/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Restriction.Enumeration
public import ClusterAlgebras.Subpattern.Freezing

/-!
# A closed reindexing is a freezing, a restriction and a relabelling

Freezing some variables and then restricting, repeated any number of times, amounts to a single
freezing followed by a single restriction. This file proves the following precise form of this
fact. Let `B̃` be an `m × n` matrix and `r` a reindexing map from `(m', n')` to `(m, n)` closed
for `B̃`. Freeze the mutable indices that `r` misses, `S = [0, n) \ r([0, n'))`, and restrict to
the preimage `I = φ_S⁻¹(r([0, m')))` of the image of `r` under the freezing map. Then `ι_I` is
closed for `Fr_S(B̃)`, and `r = φ_S ∘ ι_I ∘ π` for a bijective restriction map `π`, the
relabelling that identifies `[0, m')` with `I` in the order `r` lists it.

## Main results

* `ClusterAlgebras.ReindexingMap.exists_freeze_restrict_factorization`: every reindexing map
  closed for `B̃` factors as `φ_S ∘ ι_I ∘ π`, with `ι_I` closed for `Fr_S(B̃)` and `π` a
  bijective restriction map.

## Implementation notes

* The map `π` goes from `(m', n')` to `(|I|, n_I)`, the source of `ι_I`, where `n_I` is the
  number of elements of `I` below `n - |S|`. The statement also records `|I| = m'` and `n_I = n'`;
  stating it with the target `(|I|, n_I)` rather than `(m', n')` makes the composite `ι_I ∘ π`
  typecheck without a cast along these two equalities.

* The proof works with the inverse `ψ` of the freezing map. Its key step is that, for
  `p < m'`, the index `ψ(r(p))` is below `n - |S|` exactly when `p < n'`: on `[0, n - |S|)`
  the freezing map lists `[0, n) \ S = r([0, n'))`, and on `[n - |S|, n)` it lists `S`.

* The matrix may have entries in any type with a zero, not only in `ℤ`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 4–5*][FWZ17]
-/

@[expose] public section

namespace ClusterAlgebras

variable {m n m' n' : ℕ}

/-- If an injection `f : [0, m') → [0, m)` sends `p` below `k` exactly when `p < n'`, then its
image has `n'` elements below `k`. -/
theorem mutableCard_image_eq {k : ℕ} (h' : n' ≤ m') {f : Fin m' → Fin m}
    (hf : Function.Injective f) (hK : ∀ p, ((f p : Fin m) : ℕ) < k ↔ (p : ℕ) < n') :
    mutableCard k (Finset.univ.image f) = n' := by
  have : ((Finset.univ.image f).filter fun i : Fin m => (i : ℕ) < k)
      = Finset.univ.image fun q : Fin n' => f (Fin.castLE h' q) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨p, rfl⟩, hp⟩
      exact ⟨⟨p, (hK p).mp hp⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨⟨_, rfl⟩, (hK _).mpr q.isLt⟩
  have hinj : Function.Injective fun q : Fin n' => f (Fin.castLE h' q) :=
    hf.comp (Fin.castLE_injective h')
  rw [mutableCard, this, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin]

namespace ReindexingMap

/-- If `S` is the set of mutable indices missed by `r` and `φ_S(i) = r(p)`, then `i` is
below `n - |S|` exactly when `p` is mutable. -/
theorem val_lt_sub_card_iff_of_freezingFun_eq (h : n ≤ m) (h' : n' ≤ m')
    {r : ReindexingMap m' n' m n} {S : Finset (Fin n)}
    (hS : ∀ k, k ∉ S ↔ k ∈ Set.range (r.col h')) {p : Fin m'} {i : Fin m}
    (hi : freezingFun h S i = r p) : (i : ℕ) < n - S.card ↔ (p : ℕ) < n' := by
  constructor
  · intro hj
    obtain ⟨q, hq⟩ := (hS _).mp
      (freezingMap_col_notMem h S (sub_card_le_of_le h S) ⟨_, hj⟩)
    have hrq : r (Fin.castLE h' q) = r p := by
      have := congrArg Fin.val hq
      rw [val_col, val_col, coe_freezingMap] at this
      exact Fin.ext (this.trans (congrArg Fin.val hi))
    rw [← r.injective hrq]
    exact q.isLt
  · intro hp
    by_contra hj
    have hjn : (i : ℕ) < n := (val_freezingFun_lt_iff h S _).mp (hi.symm ▸ r.val_lt hp)
    obtain ⟨k, hkS, hk⟩ := exists_mem_freezingFun_eq_castLE h S (not_lt.mp hj) hjn
    rw [hi] at hk
    have hrk := congrArg Fin.val hk
    exact (hS k).mpr ⟨⟨p, hp⟩, Fin.ext hrk⟩ hkS

/-- If `r` is a reindexing map from `(m', n')` to `(m, n)` closed for `B`, then there are
`S ⊆ [0, n)`, `I ⊆ [0, m)` with `|I| = m'` and `|I ∩ [0, n - |S|)| = n'`, and a bijective
restriction map `π` from `(m', n')` to `(|I|, |I ∩ [0, n - |S|)|)`, such that the enumeration
`ι_I`, taken with respect to `(m, n - |S|)`, is closed for `Fr_S(B)` and `r = φ_S ∘ ι_I ∘ π`. -/
@[cluster_algebras "lem_freeze_restrict_factorization"]
theorem exists_freeze_restrict_factorization (h : n ≤ m) (h' : n' ≤ m')
    {R : Type*} [Zero R] {B : Matrix (Fin m) (Fin n) R} {r : ReindexingMap m' n' m n}
    (hr : r.IsClosedFor h' B) :
    ∃ (S : Finset (Fin n)) (I : Finset (Fin m)),
      I.card = m' ∧ mutableCard (n - S.card) I = n' ∧
      ∃ π : ReindexingMap m' n' I.card (mutableCard (n - S.card) I),
        π.IsRestriction ∧ Function.Bijective π ∧
        (enumerationMap (n - S.card) I).IsClosedFor (mutableCard_le_card _ I)
          (matrixFreeze h S B) ∧
        r = (freezingMap h S).comp ((enumerationMap (n - S.card) I).comp π) := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n), ∀ k, k ∉ S ↔ k ∈ Set.range (r.col h') :=
    ⟨(Finset.univ.image (r.col h'))ᶜ, fun k => by simp⟩
  set e := Equiv.ofBijective (freezingFun h S) (freezingFun_bijective h S)
  have hφψ : ∀ i, freezingFun h S (e.symm i) = i := e.apply_symm_apply
  have hψφ : ∀ i, e.symm (freezingFun h S i) = i := e.symm_apply_apply
  have hK : ∀ p : Fin m', ((e.symm (r p) : Fin m) : ℕ) < n - S.card ↔ (p : ℕ) < n' :=
    fun p => val_lt_sub_card_iff_of_freezingFun_eq h h' hS (hφψ (r p))
  have hψr : Function.Injective fun p => e.symm (r p) := e.symm.injective.comp r.injective
  set I : Finset (Fin m) := Finset.univ.image fun p => e.symm (r p) with hI
  have hmemI : ∀ i, i ∈ I ↔ ∃ p, e.symm (r p) = i := fun i => by simp [hI]
  have hIcard : I.card = m' := by
    rw [hI, Finset.card_image_of_injective _ hψr, Finset.card_univ, Fintype.card_fin]
  refine ⟨S, I, hIcard, mutableCard_image_eq h' hψr hK, ?_⟩
  set ι := enumerationMap (n - S.card) I
  have hrange : ∀ p, e.symm (r p) ∈ Set.range ι := fun p => by
    rw [range_enumerationMap, Finset.mem_coe, hmemI]
    exact ⟨p, rfl⟩
  let πf : Fin m' → Fin I.card := fun p =>
    (Equiv.ofInjective ι ι.injective).symm ⟨e.symm (r p), hrange p⟩
  have hιπ : ∀ p, ι (πf p) = e.symm (r p) := fun p =>
    Equiv.apply_ofInjective_symm ι.injective ⟨e.symm (r p), hrange p⟩
  have hπlt : ∀ p, (πf p : ℕ) < mutableCard (n - S.card) I ↔ (p : ℕ) < n' :=
    fun p => by rw [← val_restrictionEnumeration_lt_iff, ← coe_enumerationMap, hιπ, hK]
  have hπinj : Function.Injective πf := fun p p' hpp' =>
    hψr (show e.symm (r p) = e.symm (r p') by rw [← hιπ, ← hιπ, hpp'])
  let π : ReindexingMap m' n' I.card (mutableCard (n - S.card) I) :=
    ⟨πf, hπinj, fun p hp => (hπlt p).mpr hp⟩
  refine ⟨π, fun p hp => not_lt.mp (mt (hπlt p).mp (not_lt.mpr hp)),
    (Fintype.bijective_iff_injective_and_card π).mpr ⟨hπinj, by simp [hIcard]⟩, ?_,
    ReindexingMap.ext fun p => ((congrArg (freezingFun h S) (hιπ p)).trans (hφψ (r p))).symm⟩
  intro q i hi
  obtain ⟨p, hp⟩ : ∃ p, e.symm (r p) = ι (Fin.castLE (mutableCard_le_card _ I) q) :=
    (hmemI _).mp (restrictionEnumeration_mem (n - S.card) I _)
  have hpn : (p : ℕ) < n' := (hK p).mp (hp ▸ ι.val_lt (by simp))
  have hcol : (freezingMap h S).col (sub_card_le_of_le h S)
      (ι.col (mutableCard_le_card _ I) q) = r.col h' ⟨p, hpn⟩ := by
    refine Fin.ext ?_
    rw [val_col, val_col, coe_freezingMap, castLE_col _ _ (sub_card_le_of_le h S), ← hp, hφψ]
    rfl
  rw [matrixFreeze, hcol] at hi
  obtain ⟨p'', hp''⟩ := hr _ _ hi
  rw [← hψφ i, ← hp'']
  exact hrange p''

end ReindexingMap

end ClusterAlgebras

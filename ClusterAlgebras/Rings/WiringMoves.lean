/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.External
public import ClusterAlgebras.WiringDiagram.Commutation
public import ClusterAlgebras.WiringDiagram.BraidIso
public import ClusterAlgebras.TotalPositivity.MatsumotoTits
public import ClusterAlgebras.Subpattern.SeedReindex

/-!
# The seeds of any two wiring diagrams are mutation equivalent

Let `D` be a wiring diagram on `k ≥ 3` strands and `λ` a chamber labelling of `D`, with seed
`Σ(D, λ)`. A commutation `D ↦ D'` does not change the seed: the bijection `ψ` of chambers keeping
gaps and chamber sets is an isomorphism `Q(D) ≅ Q(D')`, so `ψ ∘ λ` is a chamber labelling of `D'`
and `Σ(D', ψ ∘ λ) = Σ(D, λ)`. A braid move mutates it, in the direction labelling the site
(`exists_labelling_seedMutation_wiringSeed`). Since any two wiring diagrams on `k` strands are
connected by commutations and braid moves (Matsumoto–Tits), the seeds of any two of them, in any
chamber labellings, are related by a mutation sequence followed by a bijective restriction map, and
every seed met along the way is again the seed of a wiring diagram.

## Main definitions

* `ClusterAlgebras.Quiver.Iso.labelling`: a labelling transported along a quiver isomorphism.

## Main results

* `ClusterAlgebras.Quiver.Iso.extExchangeMatrix_labelling`: a quiver isomorphism does not change
  the extended exchange matrix of a transported labelling.
* `ClusterAlgebras.WiringDiagram.IsCommutation.exists_labelling_wiringSeed_eq`: a commutation does
  not change the seed.
* `ClusterAlgebras.WiringDiagram.exists_seedMutationSeq_wiringSeed_eq`: the seeds of any two
  wiring diagrams are mutation equivalent, through seeds of wiring diagrams.

## Implementation notes

* For a commutation FWZ ask the bijection `ψ` to keep both the gap and the chamber set of
  every chamber. Keeping the chamber set already forces `ψ` to be the correspondence of the
  commutation (`ClusterAlgebras.WiringDiagram.eq_commEquiv_of_chamberSet`), so only that hypothesis
  is assumed; nor is `k ≥ 3` needed there.
* A wiring diagram of `WiringDiagram n'` has `n' + 2` strands, so `k ≥ 3` is `1 ≤ n'`.
* FWZ's hypothesis that "`μ_s(Σ(D, λ))` is defined" is not part of
  `ClusterAlgebras.WiringDiagram.exists_seedMutationSeq_wiringSeed_eq`; every seed met along `s` is
  a wiring seed, whose entries are nonzero flag minors.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6.
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### Transporting a labelling along a quiver isomorphism -/

namespace Quiver

variable {V V' : Type*} [Fintype V] [Fintype V'] {Q : Quiver V} {Q' : Quiver V'} {m n : ℕ}

/-- A **labelling transported along a quiver isomorphism** `φ : Q ≅ Q'`: the numbering
`φ ∘ λ` of the vertices of `Q'`. It is a labelling because `φ` matches the frozen sets. -/
def Iso.labelling (φ : Q.Iso Q') (L : Labelling Q m n) : Labelling Q' m n where
  equiv := L.equiv.trans φ.equiv
  le := L.le
  mem_frozen_iff i := (φ.mem_frozen_iff _).trans (L.mem_frozen_iff i)

/-- The numbering of a transported labelling is the composite. -/
@[simp]
theorem Iso.equiv_labelling (φ : Q.Iso Q') (L : Labelling Q m n) :
    (φ.labelling L).equiv = L.equiv.trans φ.equiv :=
  rfl

/-- **A quiver isomorphism does not change the extended exchange matrix**: the matrix of `Q'`
in the transported labelling `φ ∘ λ` is that of `Q` in `λ`, since `φ` preserves every arrow
count. -/
theorem Iso.extExchangeMatrix_labelling (φ : Q.Iso Q') (L : Labelling Q m n) :
    extExchangeMatrix Q' (φ.labelling L) = extExchangeMatrix Q L := by
  ext i j
  simp only [extExchangeMatrix, Matrix.of_apply, equiv_labelling, Equiv.trans_apply,
    signedCount, φ.arrows_eq]

end Quiver

namespace WiringDiagram

variable {n' m n : ℕ}

/-! ### A commutation does not change the seed -/

/-- **The chambers of a commutation correspond, keeping chamber sets**: this is `commEquiv`,
for the commutation move that `D'` is. -/
theorem IsCommutation.exists_equiv_chamberSet {D D' : WiringDiagram n'} {p : ℕ}
    (h : IsCommutation D D' p) :
    ∃ ψ : D.Chamber ≃ D'.Chamber, ∀ c, (ψ c).chamberSet = c.chamberSet := by
  have hp := h.1
  have hne := h.2.1
  have hD' : D' = D.commutationMove p hp hne := h.eq_commutationMove
  subst hD'
  exact ⟨D.commEquiv hp hne, D.chamberSet_commEquiv hp hne⟩

/-- **A commutation does not change the seed.** Let `D'` be obtained from the wiring diagram `D`
by a commutation, and let `ψ` be a bijection from the chambers of `D` onto those of `D'` with
`J(ψ(c)) = J(c)` for every chamber `c`. Then for every chamber labelling `λ` of `D`, `ψ ∘ λ` is a
chamber labelling of `D'` and `Σ(D', ψ ∘ λ) = Σ(D, λ)`. -/
@[cluster_algebras "lem_commutation_seed"]
theorem IsCommutation.exists_labelling_wiringSeed_eq {D D' : WiringDiagram n'} {p : ℕ}
    (h : IsCommutation D D' p) (ψ : D.Chamber ≃ D'.Chamber)
    (hJ : ∀ c, (ψ c).chamberSet = c.chamberSet) (L : Labelling D.wiringQuiver m n) :
    ∃ L' : Labelling D'.wiringQuiver m n, L'.equiv = L.equiv.trans ψ ∧
      wiringSeed D' L' = wiringSeed D L := by
  have hp := h.1
  have hne := h.2.1
  have hD' : D' = D.commutationMove p hp hne := h.eq_commutationMove
  subst hD'
  have hψ : ψ = (D.commutationIso hp hne).equiv :=
    Equiv.ext fun c => D.eq_commEquiv_of_chamberSet hp hne hJ c
  subst hψ
  refine ⟨(D.commutationIso hp hne).labelling L, rfl, SeedData.ext ?_ ?_⟩
  · funext i
    simp only [wiringSeed, Quiver.Iso.equiv_labelling, Equiv.trans_apply]
    rw [hJ]
  · exact (D.commutationIso hp hne).extExchangeMatrix_labelling L

/-! ### Any two wiring seeds are mutation equivalent -/

/-- Along a chain of commutations and braid moves from `D` to `E`, the seed of `D` in a chamber
labelling `λ` is carried by a mutation sequence `s` to the seed of `E` in some chamber labelling,
and every partial mutation along `s` is the seed of some wiring diagram. -/
theorem exists_seedMutationSeq_wiringSeed_of_reflTransGen (hk : 1 ≤ n')
    {D E : WiringDiagram n'}
    (hDE : Relation.ReflTransGen
      (fun E E' : WiringDiagram n' => (∃ p, IsCommutation E E' p) ∨ ∃ p, IsBraidMove E E' p)
      D E)
    (L : Labelling D.wiringQuiver m n) :
    ∃ (s : List (Fin n)) (LE : Labelling E.wiringQuiver m n),
      seedMutationSeq L.le (wiringSeed D L) s = wiringSeed E LE ∧
      ∀ e ≤ s.length, ∃ (E' : WiringDiagram n') (LE' : Labelling E'.wiringQuiver m n),
        seedMutationSeq L.le (wiringSeed D L) (s.take e) = wiringSeed E' LE' := by
  induction hDE with
  | refl =>
    refine ⟨[], L, rfl, fun e _ => ⟨D, L, ?_⟩⟩
    simp
  | tail _ hEF ih =>
    rename_i E F _
    obtain ⟨s, LE, hs, hpre⟩ := ih
    rcases hEF with ⟨p, hc⟩ | ⟨p, hb⟩
    · obtain ⟨ψ, hψ⟩ := hc.exists_equiv_chamberSet
      obtain ⟨LF, -, hLF⟩ := hc.exists_labelling_wiringSeed_eq ψ hψ LE
      exact ⟨s, LF, hs.trans hLF.symm, hpre⟩
    · obtain ⟨ψ, ⟨hY, hJ⟩, -⟩ := hb.existsUnique_equiv
      have hlt : ((LE.equiv.symm (E.braidSite hb.1) : Fin m) : ℕ) < n := by
        by_contra hge
        have hfr := (LE.mem_frozen_iff (LE.equiv.symm (E.braidSite hb.1))).2 (not_lt.1 hge)
        rw [Equiv.apply_symm_apply] at hfr
        exact hb.braidSite_notMem_frozen hfr
      obtain ⟨LF, -, hLF⟩ := exists_labelling_seedMutation_wiringSeed hk hb ψ hY hJ LE
        ⟨_, hlt⟩ (by simp [Fin.castLE])
      refine ⟨s ++ [⟨_, hlt⟩], LF, ?_, fun e he => ?_⟩
      · rwa [seedMutationSeq_append, hs]
      · rcases Nat.lt_or_ge e (s.length + 1) with he' | he'
        · rw [List.take_append_of_le_length (by omega)]
          exact hpre e (by omega)
        · rw [List.take_of_length_le (by simp; omega), seedMutationSeq_append, hs]
          exact ⟨F, LF, hLF⟩

/-- **The seeds of any two wiring diagrams are mutation equivalent.** Let `k = n' + 2 ≥ 3`, let
`D` and `D'` be wiring diagrams on `k` strands, and let `λ`, `λ'` be chamber labellings of `D` and
`D'`. Then there are a finite sequence `s = (q₁, …, q_d)` of elements of `[1, n]` and a bijective
restriction map `π` from `(m, n)` to `(m, n)` such that `Σ(D', λ') = (μ_s(Σ(D, λ)))^π` and, for
each `e ∈ [0, d]`, `μ_{(q₁, …, q_e)}(Σ(D, λ)) = Σ(E_e, λ_e)` for some wiring diagram `E_e` on `k`
strands and chamber labelling `λ_e` of `E_e`. -/
@[cluster_algebras "lem_wiring_seeds_equivalent"]
theorem exists_seedMutationSeq_wiringSeed_eq (hk : 1 ≤ n') (D D' : WiringDiagram n')
    (L : Labelling D.wiringQuiver m n) (L' : Labelling D'.wiringQuiver m n) :
    ∃ (s : List (Fin n)) (π : ReindexingMap m n m n), π.IsRestriction ∧ Function.Bijective π ∧
      wiringSeed D' L' = (seedMutationSeq L.le (wiringSeed D L) s).reindex L.le π ∧
      ∀ e ≤ s.length, ∃ (E : WiringDiagram n') (LE : Labelling E.wiringQuiver m n),
        seedMutationSeq L.le (wiringSeed D L) (s.take e) = wiringSeed E LE := by
  obtain ⟨s, LF, hs, hpre⟩ := exists_seedMutationSeq_wiringSeed_of_reflTransGen hk
    (reflTransGen_isCommutation_or_isBraidMove D D') L
  have hlt : ∀ i : Fin m, (i : ℕ) < n → ((LF.equiv.symm (L'.equiv i) : Fin m) : ℕ) < n := by
    intro i hi
    by_contra hge
    have h1 := (LF.mem_frozen_iff (LF.equiv.symm (L'.equiv i))).2 (not_lt.1 hge)
    rw [Equiv.apply_symm_apply, L'.mem_frozen_iff] at h1
    omega
  let π : ReindexingMap m n m n :=
    ⟨fun i => LF.equiv.symm (L'.equiv i), (L'.equiv.trans LF.equiv.symm).injective, hlt⟩
  refine ⟨s, π, fun i hi => ?_, (L'.equiv.trans LF.equiv.symm).bijective, ?_, hpre⟩
  · refine (LF.mem_frozen_iff (π i)).1 ?_
    change LF.equiv (LF.equiv.symm (L'.equiv i)) ∈ _
    rwa [Equiv.apply_symm_apply, L'.mem_frozen_iff]
  · rw [hs]
    refine SeedData.ext ?_ ?_
    · funext i
      simp [wiringSeed, π]
    · ext i j
      simp [wiringSeed, π, extExchangeMatrix, ReindexingMap.col]

end WiringDiagram

end ClusterAlgebras

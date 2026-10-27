/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Subpattern.SeedReindex

/-!
# Freezing a set of mutable indices

Freezing a set `S` of mutable indices of a seed `(x̃, B̃)` [FWZ17, Definition 4.2.1]: the
variables at `S` become frozen, the columns of `B̃` at `S` are removed, and the indices are
renumbered so that the remaining mutable ones come first. With `n_S = n - |S|`, the
renumbering is the *freezing map* `φ_S : [0, m) → [0, m)`
(`ClusterAlgebras.freezingFun`), listing first the mutable indices outside `S` in increasing
order, then the elements of `S` in increasing order, then the frozen indices `[n, m)` in
place. It is a bijective reindexing map from `(m, n_S)` to `(m, n)`
(`ClusterAlgebras.freezingMap`), closed for every matrix, so freezing a matrix
(`ClusterAlgebras.matrixFreeze`) or a seed (`ClusterAlgebras.SeedData.freeze`) is reindexing
along it. Consequently freezing commutes with mutation in any direction `k ∉ S`
(`ClusterAlgebras.SeedData.freeze_seedMutation`) [FWZ17, Lemma 4.2.2].

## Main definitions

* `ClusterAlgebras.freezingFun`: the freezing map `φ_S` of `S ⊆ [0, n)`.
* `ClusterAlgebras.freezingMap`: `φ_S` as a reindexing map from `(m, n - |S|)` to `(m, n)`.
* `ClusterAlgebras.matrixFreeze`: the freezing `Fr_S(B̃)` of an `m × n` matrix.
* `ClusterAlgebras.SeedData.freeze`: the freezing `Fr_S(x̃, B̃)` of a seed.

## Main results

* `ClusterAlgebras.freezingFun_bijective`, `ClusterAlgebras.freezingMap_isClosedFor`: the
  freezing map is a bijection, and a reindexing map closed for every matrix.
* `ClusterAlgebras.matrixFreeze_eq_matrixReindex`, `ClusterAlgebras.SeedData.freeze_eq_reindex`:
  freezing is reindexing along `φ_S`.
* `ClusterAlgebras.exists_freezingMap_col_eq`, `ClusterAlgebras.existsUnique_freezingMap_col_eq`:
  every mutable index `k ∉ S` is `φ_S(q)` for a unique `q < n - |S|`.
* `ClusterAlgebras.SeedData.freeze_seedMutation`: freezing commutes with seed mutation,
  `Fr_S(μ_k(x̃, B̃)) = μ_q(Fr_S(x̃, B̃))` where `φ_S(q) = k`.

## Implementation notes

* Indices are `Fin m`, so FWZ's `[1, m]` is `0, …, m - 1` and its `[1, n]` is the
  indices of value below `n`. The set `S` is a `Finset (Fin n)` and its complement
  `[1, n] \ S` is `Sᶜ`. The value of `φ_S` at `p < n - |S|` is the `p`-th element of `Sᶜ`,
  at `n - |S| ≤ p < n` the `(p - (n - |S|))`-th element of `S`, each read as a row index by
  `Fin.castLE`, and `p` itself at `p ≥ n`; this is [FWZ17, Definition 4.2.1] verbatim.

* The number `n_S` of mutable indices after freezing is written `n - S.card` throughout,
  so that `Fin (n - S.card)` is the type of the remaining mutable indices. In particular
  freezing at `S = ∅` produces a seed with `n - 0` mutable indices, equal to `n` only
  propositionally; `freezingFun_empty`, `freezingMap_col_empty` and `matrixFreeze_empty`
  state that it is the identity up to that cast.

* The entry `Fr_S(B̃)_{pq} = b_{φ_S(p) φ_S(q)}` reads `φ_S(q)` as a column index, which is
  `(freezingMap h S).col _ q`, so `matrixFreeze` is `matrixReindex` along `freezingMap`
  by definition.

* `matrixFreeze` is defined for matrices with entries in any type, and `SeedData.freeze`
  for seeds with entries in any type; [FWZ17] takes integer matrices and a field.

* [FWZ17, Lemma 4.2.2], that freezing commutes with mutation, assumes `x_k ≠ 0`, so that
  both seed mutations are defined. `seedMutation` is total, Lean's division being total,
  and `seedMutation_reindex` holds without that hypothesis, so it is dropped here, a
  generalisation.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 4–5*][FWZ17]
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {m n : ℕ}

/-! ### The freezing map -/

section FreezingMap

/-- The complement of a set of mutable indices has `n - |S|` elements. -/
theorem card_compl_eq_sub_card (S : Finset (Fin n)) : Sᶜ.card = n - S.card := by
  rw [Finset.card_compl, Fintype.card_fin]

/-- After freezing `S`, there are still at most `m` mutable indices. -/
theorem sub_card_le_of_le (h : n ≤ m) (S : Finset (Fin n)) : n - S.card ≤ m :=
  (Nat.sub_le n S.card).trans h

/-- The **freezing map** `φ_S` of a set `S` of mutable indices: its values at
`0, …, n_S - 1` are the elements of `[0, n) \ S` in increasing order, its values at
`n_S, …, n - 1` the elements of `S` in increasing order, and `φ_S(p) = p` for `p ≥ n`, where
`n_S = n - |S|`. -/
@[cluster_algebras "def_freezing_map"]
def freezingFun (h : n ≤ m) (S : Finset (Fin n)) (p : Fin m) : Fin m :=
  if hp : (p : ℕ) < n - S.card then
    Fin.castLE h (Sᶜ.orderEmbOfFin (card_compl_eq_sub_card S) ⟨p, hp⟩)
  else if hp' : (p : ℕ) < n then
    Fin.castLE h (S.orderEmbOfFin rfl ⟨p - (n - S.card), by
      have := card_finset_fin_le S
      omega⟩)
  else p

variable (h : n ≤ m) (S : Finset (Fin n))

/-- On `[0, n_S)` the freezing map lists `[0, n) \ S` in increasing order. -/
theorem freezingFun_of_lt {p : Fin m} (hp : (p : ℕ) < n - S.card) :
    freezingFun h S p = Fin.castLE h (Sᶜ.orderEmbOfFin (card_compl_eq_sub_card S) ⟨p, hp⟩) :=
  dif_pos hp

/-- On `[n_S, n)` the freezing map lists `S` in increasing order. -/
theorem freezingFun_of_le_of_lt {p : Fin m} (hp : n - S.card ≤ (p : ℕ)) (hp' : (p : ℕ) < n) :
    freezingFun h S p = Fin.castLE h (S.orderEmbOfFin rfl ⟨p - (n - S.card), by
      have := card_finset_fin_le S
      omega⟩) := by
  rw [freezingFun, dif_neg (not_lt.mpr hp), dif_pos hp']

/-- The freezing map fixes the frozen indices `[n, m)`. -/
theorem freezingFun_of_le {p : Fin m} (hp : n ≤ (p : ℕ)) : freezingFun h S p = p := by
  rw [freezingFun, dif_neg (by omega), dif_neg (by omega)]

/-- The freezing map takes a value below `n` exactly at the indices below `n`. -/
theorem val_freezingFun_lt_iff (p : Fin m) : (freezingFun h S p : ℕ) < n ↔ (p : ℕ) < n := by
  have hS := card_finset_fin_le S
  rcases lt_or_ge (p : ℕ) (n - S.card) with hp | hp
  · rw [freezingFun_of_lt h S hp, Fin.val_castLE]
    exact iff_of_true (Fin.is_lt _) (by omega)
  rcases lt_or_ge (p : ℕ) n with hp' | hp'
  · rw [freezingFun_of_le_of_lt h S hp hp', Fin.val_castLE]
    exact iff_of_true (Fin.is_lt _) hp'
  · rw [freezingFun_of_le h S hp']

/-- The freezing map is injective. -/
theorem freezingFun_injective : Function.Injective (freezingFun h S) := by
  have hS := card_finset_fin_le S
  have hlt := val_freezingFun_lt_iff h S
  intro p p' hpp'
  have hn : (p : ℕ) < n ↔ (p' : ℕ) < n := (hlt p).symm.trans (hpp' ▸ hlt p')
  rcases lt_or_ge (p' : ℕ) n with hp'n | hp'n
  swap
  · rwa [freezingFun_of_le h S hp'n, freezingFun_of_le h S (not_lt.mp (hn.not.mpr
      (not_lt.mpr hp'n)))] at hpp'
  have hpn := hn.mpr hp'n
  rcases lt_or_ge (p : ℕ) (n - S.card) with hp | hp <;>
    rcases lt_or_ge (p' : ℕ) (n - S.card) with hq | hq
  · rw [freezingFun_of_lt h S hp, freezingFun_of_lt h S hq] at hpp'
    have := (Sᶜ.orderEmbOfFin _).injective (Fin.castLE_injective h hpp')
    exact Fin.ext (Fin.mk.inj_iff.mp this)
  · rw [freezingFun_of_lt h S hp, freezingFun_of_le_of_lt h S hq hp'n] at hpp'
    have h₁ := Sᶜ.orderEmbOfFin_mem (card_compl_eq_sub_card S) ⟨p, hp⟩
    rw [Fin.castLE_injective h hpp', Finset.mem_compl] at h₁
    exact absurd (S.orderEmbOfFin_mem rfl _) h₁
  · rw [freezingFun_of_le_of_lt h S hp hpn, freezingFun_of_lt h S hq] at hpp'
    have h₁ := Sᶜ.orderEmbOfFin_mem (card_compl_eq_sub_card S) ⟨p', hq⟩
    rw [← Fin.castLE_injective h hpp', Finset.mem_compl] at h₁
    exact absurd (S.orderEmbOfFin_mem rfl _) h₁
  · rw [freezingFun_of_le_of_lt h S hp hpn, freezingFun_of_le_of_lt h S hq hp'n] at hpp'
    have := Fin.mk.inj_iff.mp ((S.orderEmbOfFin rfl).injective (Fin.castLE_injective h hpp'))
    exact Fin.ext (by omega)

/-- **The freezing map is a bijection** of `[0, m)`. -/
@[cluster_algebras "lem_freezing_map_reindexing"]
theorem freezingFun_bijective : Function.Bijective (freezingFun h S) :=
  (freezingFun_injective h S).bijective_of_finite

/-- The **freezing map** `φ_S`, as a reindexing map from `(m, n - |S|)` to `(m, n)`. -/
@[cluster_algebras "lem_freezing_map_reindexing"]
def freezingMap : ReindexingMap m (n - S.card) m n where
  toFun := freezingFun h S
  injective := freezingFun_injective h S
  lt_of_lt p hp := (val_freezingFun_lt_iff h S p).mpr (hp.trans_le (Nat.sub_le n S.card))

/-- The reindexing map `freezingMap h S` is the freezing map. -/
@[simp]
theorem coe_freezingMap : ⇑(freezingMap h S) = freezingFun h S :=
  rfl

/-- The freezing map, as a reindexing map, is surjective. -/
theorem freezingMap_surjective : Function.Surjective (freezingMap h S) :=
  (freezingFun_bijective h S).2

/-- **The freezing map is closed for every matrix.** -/
@[cluster_algebras "lem_freezing_map_reindexing"]
theorem freezingMap_isClosedFor {R : Type*} [Zero R] (h' : n - S.card ≤ m)
    (B : Matrix (Fin m) (Fin n) R) : (freezingMap h S).IsClosedFor h' B :=
  ReindexingMap.isClosedFor_of_surjective (freezingMap_surjective h S) h' B

variable (h' : n - S.card ≤ m)

/-- The column map of the freezing map lists `[0, n) \ S` in increasing order. -/
theorem freezingMap_col (q : Fin (n - S.card)) :
    (freezingMap h S).col h' q = Sᶜ.orderEmbOfFin (card_compl_eq_sub_card S) q := by
  apply Fin.ext
  rw [ReindexingMap.val_col, coe_freezingMap, freezingFun_of_lt h S (by simp), Fin.val_castLE]
  rfl

/-- The column map of the freezing map avoids `S`. -/
theorem freezingMap_col_notMem (q : Fin (n - S.card)) : (freezingMap h S).col h' q ∉ S := by
  rw [freezingMap_col, ← Finset.mem_compl]
  exact Sᶜ.orderEmbOfFin_mem _ q

/-- The image of the column map of the freezing map is `[0, n) \ S`. -/
theorem range_freezingMap_col : Set.range ((freezingMap h S).col h') = (↑S)ᶜ := by
  have : (freezingMap h S).col h' = Sᶜ.orderEmbOfFin (card_compl_eq_sub_card S) :=
    funext (freezingMap_col h S h')
  rw [this, Finset.range_orderEmbOfFin, Finset.coe_compl]

/-- **Every mutable index outside `S` is `φ_S(q)` for some `q < n - |S|`.** -/
@[cluster_algebras "lem_freezing_commutes"]
theorem exists_freezingMap_col_eq {k : Fin n} (hk : k ∉ S) :
    ∃ q : Fin (n - S.card), (freezingMap h S).col h' q = k := by
  rw [← Set.mem_range, range_freezingMap_col]
  exact hk

/-- Every mutable index outside `S` is `φ_S(q)` for a unique `q < n - |S|`. -/
theorem existsUnique_freezingMap_col_eq {k : Fin n} (hk : k ∉ S) :
    ∃! q : Fin (n - S.card), (freezingMap h S).col h' q = k :=
  let ⟨q, hq⟩ := exists_freezingMap_col_eq h S h' hk
  ⟨q, hq, fun _ hq' => (freezingMap h S).col_injective h' (hq'.trans hq.symm)⟩

/-- On `[n_S, n)` the freezing map takes its values in `S`. -/
theorem exists_mem_freezingFun_eq_castLE {p : Fin m} (hp : n - S.card ≤ (p : ℕ))
    (hp' : (p : ℕ) < n) : ∃ k ∈ S, freezingFun h S p = Fin.castLE h k :=
  ⟨_, S.orderEmbOfFin_mem rfl _, freezingFun_of_le_of_lt h S hp hp'⟩

/-- Every element of `S` is the value of the freezing map at an index of `[n_S, n)`. -/
theorem exists_freezingFun_eq_castLE_of_mem {k : Fin n} (hk : k ∈ S) :
    ∃ p : Fin m, n - S.card ≤ (p : ℕ) ∧ (p : ℕ) < n ∧
      freezingFun h S p = Fin.castLE h k := by
  obtain ⟨p, hp⟩ := (freezingFun_bijective h S).2 (Fin.castLE h k)
  have hpn : (p : ℕ) < n := (val_freezingFun_lt_iff h S p).mp (by simp [hp])
  refine ⟨p, not_lt.mp fun hlt => ?_, hpn, hp⟩
  have hq := freezingMap_col_notMem h S (sub_card_le_of_le h S) ⟨p, hlt⟩
  have : (freezingMap h S).col (sub_card_le_of_le h S) ⟨p, hlt⟩ = k :=
    Fin.ext (by simpa using congrArg Fin.val hp)
  exact hq (this ▸ hk)

/-- The enumeration of `[0, n) \ ∅` is the identity, up to the cast along `n - 0 = n`. -/
theorem orderEmbOfFin_compl_empty (q : Fin (n - (∅ : Finset (Fin n)).card)) :
    (∅ : Finset (Fin n))ᶜ.orderEmbOfFin (card_compl_eq_sub_card ∅) q = Fin.cast (by simp) q :=
  (congrFun (Finset.orderEmbOfFin_unique (card_compl_eq_sub_card ∅) (f := Fin.cast (by simp))
    (fun _ => by simp) fun _ _ hab => hab) q).symm

/-- The freezing map at the empty set is the identity. -/
@[simp]
theorem freezingFun_empty : freezingFun h (∅ : Finset (Fin n)) = id := by
  funext p
  rcases lt_or_ge (p : ℕ) n with hp | hp
  · have hp₀ : (p : ℕ) < n - (∅ : Finset (Fin n)).card := by simpa using hp
    rw [freezingFun_of_lt h ∅ hp₀, orderEmbOfFin_compl_empty]
    rfl
  · exact freezingFun_of_le h ∅ hp

/-- The column map of the freezing map at the empty set is the cast along `n - 0 = n`. -/
theorem freezingMap_col_empty (h' : n - (∅ : Finset (Fin n)).card ≤ m)
    (q : Fin (n - (∅ : Finset (Fin n)).card)) :
    (freezingMap h ∅).col h' q = Fin.cast (by simp) q := by
  rw [freezingMap_col, orderEmbOfFin_compl_empty]

end FreezingMap

/-! ### Freezing a matrix -/

section Matrix

variable {R : Type*} (h : n ≤ m) (S : Finset (Fin n))

/-- The **freezing** `Fr_S(B)` of an `m × n` matrix `B` at a set `S` of mutable indices: the
`m × (n - |S|)` matrix with entries `Fr_S(B)_{pq} = b_{φ_S(p) φ_S(q)}`, the index `φ_S(q)`
being read as a column index. -/
@[cluster_algebras "def_matrix_freezing"]
def matrixFreeze (B : Matrix (Fin m) (Fin n) R) : Matrix (Fin m) (Fin (n - S.card)) R :=
  fun p q => B (freezingFun h S p) ((freezingMap h S).col (sub_card_le_of_le h S) q)

/-- The entries of a frozen matrix. -/
theorem matrixFreeze_apply (B : Matrix (Fin m) (Fin n) R) (p : Fin m) (q : Fin (n - S.card)) :
    matrixFreeze h S B p q
      = B (freezingFun h S p) (Sᶜ.orderEmbOfFin (card_compl_eq_sub_card S) q) := by
  rw [matrixFreeze, freezingMap_col]

/-- **Freezing is reindexing along the freezing map**, `Fr_S(B) = B^{φ_S}`. -/
theorem matrixFreeze_eq_matrixReindex (h' : n - S.card ≤ m) (B : Matrix (Fin m) (Fin n) R) :
    matrixFreeze h S B = matrixReindex h' B (freezingMap h S) :=
  rfl

/-- Freezing at the empty set does nothing, up to the cast along `n - 0 = n` of the column
indices. -/
theorem matrixFreeze_empty (B : Matrix (Fin m) (Fin n) R) :
    matrixFreeze h ∅ B = B.submatrix id (Fin.cast (by simp)) := by
  ext p q
  rw [matrixFreeze, freezingMap_col_empty, freezingFun_empty]
  rfl

end Matrix

/-! ### Freezing a seed -/

section Seed

variable {F : Type*} (h : n ≤ m) (S : Finset (Fin n))

/-- The **freezing** `Fr_S(x̃, B̃) = ((x_{φ_S(0)}, …, x_{φ_S(m-1)}), Fr_S(B̃))` of a seed at a
set `S` of mutable indices. -/
@[cluster_algebras "def_freezing"]
def SeedData.freeze (Sd : SeedData F m n) : SeedData F m (n - S.card) where
  extCluster := Sd.extCluster ∘ freezingFun h S
  extExchangeMatrix := matrixFreeze h S Sd.extExchangeMatrix

/-- The extended cluster of a frozen seed. -/
@[simp]
theorem SeedData.freeze_extCluster (Sd : SeedData F m n) :
    (Sd.freeze h S).extCluster = Sd.extCluster ∘ freezingFun h S :=
  rfl

/-- The extended exchange matrix of a frozen seed. -/
@[simp]
theorem SeedData.freeze_extExchangeMatrix (Sd : SeedData F m n) :
    (Sd.freeze h S).extExchangeMatrix = matrixFreeze h S Sd.extExchangeMatrix :=
  rfl

/-- **Freezing a seed is reindexing it along the freezing map**,
`Fr_S(x̃, B̃) = (x̃, B̃)^{φ_S}`. -/
theorem SeedData.freeze_eq_reindex (h' : n - S.card ≤ m) (Sd : SeedData F m n) :
    Sd.freeze h S = Sd.reindex h' (freezingMap h S) :=
  rfl

/-- Freezing at the empty set keeps the extended cluster. -/
theorem SeedData.freeze_empty_extCluster (Sd : SeedData F m n) :
    (Sd.freeze h ∅).extCluster = Sd.extCluster := by
  rw [freeze_extCluster, freezingFun_empty, Function.comp_id]

variable [Field F]

/-- **Freezing commutes with seed mutation**: if `k ∉ S` and `φ_S(q) = k`, then
`Fr_S(μ_k(x̃, B̃)) = μ_q(Fr_S(x̃, B̃))` [FWZ17, Lemma 4.2.2]. The hypothesis `k ∉ S` is
implied by `φ_S(q) = k`, and the hypothesis `x_k ≠ 0` is not needed since `seedMutation` is
total. -/
@[cluster_algebras "lem_freezing_commutes"]
theorem SeedData.freeze_seedMutation (h' : n - S.card ≤ m) (Sd : SeedData F m n) {k : Fin n}
    {q : Fin (n - S.card)} (hq : (freezingMap h S).col h' q = k) :
    (seedMutation h Sd k).freeze h S = seedMutation h' (Sd.freeze h S) q := by
  rw [freeze_eq_reindex h S h', freeze_eq_reindex h S h',
    seedMutation_reindex h h' Sd (freezingMap_isClosedFor h S h' _) q, hq]

/-- **Freezing commutes with mutation along a sequence**: `Fr_S(μ_{φ_S(s)}(x̃, B̃)) =
μ_s(Fr_S(x̃, B̃))`, where `φ_S(s)` applies the column map of the freezing map to each
direction. -/
theorem SeedData.freeze_seedMutationSeq (h' : n - S.card ≤ m) (Sd : SeedData F m n)
    (s : List (Fin (n - S.card))) :
    (seedMutationSeq h Sd (s.map ((freezingMap h S).col h'))).freeze h S
      = seedMutationSeq h' (Sd.freeze h S) s := by
  rw [freeze_eq_reindex h S h', freeze_eq_reindex h S h',
    seedMutationSeq_reindex h h' Sd (freezingMap_isClosedFor h S h' _) s]

end Seed

end ClusterAlgebras

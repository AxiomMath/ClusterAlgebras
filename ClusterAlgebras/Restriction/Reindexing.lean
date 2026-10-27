/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Defs.MatrixMutationEquiv

/-!
# Reindexing maps, and pulling a matrix back along one

A *reindexing map* (`ClusterAlgebras.ReindexingMap`) from `(m', n')` to `(m, n)` is an
injection `r : Fin m' → Fin m` sending the mutable indices `[0, n')` into the mutable indices
`[0, n)`. A matrix is pulled back along it by `(Bʳ)_{pq} = b_{r(p) r(q)}`
(`ClusterAlgebras.matrixReindex`). Restricting a matrix to a subset of its indices, and
renumbering after freezing and trivialization, are all instances of this construction.

Mutation commutes with reindexing, `μ_q(Bʳ) = (μ_{r(q)} B)ʳ`; this generalises
[FWZ, Lemma 4.1.2] from restrictions to arbitrary reindexing maps.

## Main definitions

* `ClusterAlgebras.ReindexingMap`: An injection `Fin m' → Fin m` sending mutable indices to
  mutable indices.
* `ClusterAlgebras.ReindexingMap.col`: The induced map `Fin n' → Fin n` on column indices.
* `ClusterAlgebras.ReindexingMap.comp`: The composite of two reindexing maps.
* `ClusterAlgebras.ReindexingMap.IsRestriction`: A reindexing map that also sends frozen
  indices to frozen indices.
* `ClusterAlgebras.matrixReindex`: The pullback `Bʳ` of a matrix `B` along a reindexing map.

## Main results

* `ClusterAlgebras.matrixMutation_matrixReindex`: Mutation commutes with reindexing.
* `ClusterAlgebras.matrixMutationList_matrixReindex`: Mutation along a sequence commutes with
  reindexing.
* `ClusterAlgebras.ExtSkewSymmetrizable.matrixReindex`: Reindexing preserves extended
  skew-symmetrizability.

## Implementation notes

* Indices are `Fin m`, so they run over `0, …, m - 1`, and the mutable indices are those of
  value below `n`. This is the convention of `ClusterAlgebras.matrixMutation`, whose row
  carrying column `k` is `Fin.castLE hmn k`.

* A reindexing map is a bundled structure with a `FunLike` instance, so that composition
  (`ReindexingMap.comp`) and the induced map on column indices (`ReindexingMap.col`) are
  operations on the bundle. The structure carries no proof of `n ≤ m` or `n' ≤ m'`: the
  condition on mutable indices is stated on values, `p < n' → r p < n`, so it needs neither.
  The inequality `n' ≤ m'` enters only where a column index is read as a row index, in
  `ReindexingMap.col` and in `matrixReindex`.

* Being a restriction map is a predicate on a reindexing map
  (`ReindexingMap.IsRestriction`), so every result about reindexing maps applies to
  restriction maps.

* `matrixReindex` is `Matrix.submatrix` along the row map and the column map, so Mathlib's
  `submatrix` API applies to it unchanged.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

/-- A **reindexing map** from `(m', n')` to `(m, n)`: an injective map `Fin m' → Fin m`
sending every mutable index (value below `n'`) to a mutable index (value below `n`). -/
@[cluster_algebras "def_reindexing_map"]
structure ReindexingMap (m' n' m n : ℕ) where
  /-- The map on row indices. -/
  toFun : Fin m' → Fin m
  /-- Distinct indices go to distinct indices. -/
  injective : Function.Injective toFun
  /-- Mutable indices go to mutable indices. -/
  lt_of_lt : ∀ p : Fin m', (p : ℕ) < n' → (toFun p : ℕ) < n

namespace ReindexingMap

variable {m n m' n' m'' n'' : ℕ}

/-- A reindexing map coerces to its underlying function. -/
instance instFunLike : FunLike (ReindexingMap m' n' m n) (Fin m') (Fin m) where
  coe := toFun
  coe_injective r s h := by cases r; cases s; congr

/-- The underlying function of a reindexing map built from its fields. -/
@[simp]
theorem coe_mk (f : Fin m' → Fin m) (hf : Function.Injective f)
    (h : ∀ p : Fin m', (p : ℕ) < n' → (f p : ℕ) < n) : ⇑(ReindexingMap.mk f hf h) = f :=
  rfl

/-- Two reindexing maps with the same underlying function are equal. -/
@[ext]
theorem ext {r s : ReindexingMap m' n' m n} (h : ∀ p, r p = s p) : r = s :=
  DFunLike.ext r s h

/-- A reindexing map sends mutable indices to mutable indices. -/
theorem val_lt (r : ReindexingMap m' n' m n) {p : Fin m'} (hp : (p : ℕ) < n') :
    (r p : ℕ) < n :=
  r.lt_of_lt p hp

/-- The **map on column indices** induced by a reindexing map: a column index `q < n'` is
read as the row index `Fin.castLE h' q`, sent along `r`, and read back as a column index,
which it is because `r` keeps mutable indices mutable. -/
def col (r : ReindexingMap m' n' m n) (h' : n' ≤ m') (q : Fin n') : Fin n :=
  ⟨r (Fin.castLE h' q), r.val_lt (by simp)⟩

/-- The column map read back as a row index is the row map. -/
@[simp]
theorem castLE_col (r : ReindexingMap m' n' m n) (h' : n' ≤ m') (h : n ≤ m) (q : Fin n') :
    Fin.castLE h (r.col h' q) = r (Fin.castLE h' q) :=
  rfl

/-- The value of the column map. -/
@[simp]
theorem val_col (r : ReindexingMap m' n' m n) (h' : n' ≤ m') (q : Fin n') :
    (r.col h' q : ℕ) = r (Fin.castLE h' q) :=
  rfl

/-- The column map is injective. -/
theorem col_injective (r : ReindexingMap m' n' m n) (h' : n' ≤ m') :
    Function.Injective (r.col h') := by
  intro q q' hq
  have : r (Fin.castLE h' q) = r (Fin.castLE h' q') := Fin.ext (by simpa using congrArg Fin.val hq)
  exact Fin.castLE_injective h' (r.injective this)

/-- The identity reindexing map. -/
protected def id (m n : ℕ) : ReindexingMap m n m n where
  toFun := id
  injective := Function.injective_id
  lt_of_lt _ hp := hp

/-- The identity reindexing map is the identity. -/
@[simp]
theorem coe_id : ⇑(ReindexingMap.id m n) = id :=
  rfl

/-- The column map of the identity is the identity. -/
@[simp]
theorem col_id (h : n ≤ m) : (ReindexingMap.id m n).col h = id :=
  rfl

/-- **Reindexing maps compose**: if `r` is a reindexing map from `(m', n')` to `(m, n)` and
`s` one from `(m'', n'')` to `(m', n')`, then `r ∘ s` is a reindexing map from
`(m'', n'')` to `(m, n)`. -/
@[cluster_algebras "lem_reindexing_map_comp"]
def comp (r : ReindexingMap m' n' m n) (s : ReindexingMap m'' n'' m' n') :
    ReindexingMap m'' n'' m n where
  toFun := r ∘ s
  injective := r.injective.comp s.injective
  lt_of_lt _ hp := r.val_lt (s.val_lt hp)

/-- The composite reindexing map is the composite of the functions. -/
@[cluster_algebras "lem_reindexing_map_comp", simp]
theorem coe_comp (r : ReindexingMap m' n' m n) (s : ReindexingMap m'' n'' m' n') :
    ⇑(r.comp s) = r ∘ s :=
  rfl

/-- The composite applied to an index. -/
@[simp]
theorem comp_apply (r : ReindexingMap m' n' m n) (s : ReindexingMap m'' n'' m' n')
    (p : Fin m'') : r.comp s p = r (s p) :=
  rfl

/-- The column map of a composite is the composite of the column maps. -/
@[simp]
theorem col_comp (r : ReindexingMap m' n' m n) (s : ReindexingMap m'' n'' m' n')
    (h' : n' ≤ m') (h'' : n'' ≤ m'') : (r.comp s).col h'' = r.col h' ∘ s.col h'' :=
  rfl

/-- A reindexing map is a **restriction map** when it also sends every frozen index (value
at least `n'`) to a frozen index (value at least `n`). -/
@[cluster_algebras "def_restriction_map"]
def IsRestriction (r : ReindexingMap m' n' m n) : Prop :=
  ∀ p : Fin m', n' ≤ (p : ℕ) → n ≤ (r p : ℕ)

/-- A restriction map sends an index to a mutable one exactly when the index is mutable. -/
theorem IsRestriction.val_lt_iff {r : ReindexingMap m' n' m n} (hr : r.IsRestriction)
    (p : Fin m') : (r p : ℕ) < n ↔ (p : ℕ) < n' := by
  refine ⟨fun h => ?_, r.val_lt⟩
  by_contra hp
  exact absurd (hr p (not_lt.mp hp)) (not_le.mpr h)

/-- The identity is a restriction map. -/
theorem isRestriction_id : (ReindexingMap.id m n).IsRestriction :=
  fun _ h => h

/-- **Restriction maps compose.** -/
@[cluster_algebras "lem_restriction_map_comp"]
theorem IsRestriction.comp {r : ReindexingMap m' n' m n} {s : ReindexingMap m'' n'' m' n'}
    (hr : r.IsRestriction) (hs : s.IsRestriction) : (r.comp s).IsRestriction :=
  fun p hp => hr (s p) (hs p hp)

end ReindexingMap

section Reindex

variable {α : Type*} {m n m' n' m'' n'' : ℕ}

/-- The **reindexing of `B` along `r`**: the `m' × n'` matrix with entries
`(Bʳ)_{pq} = b_{r(p) r(q)}`, the column index `q` being sent along `r` by
`ReindexingMap.col`. -/
@[cluster_algebras "def_matrix_reindexing"]
def matrixReindex (h' : n' ≤ m') (B : Matrix (Fin m) (Fin n) α) (r : ReindexingMap m' n' m n) :
    Matrix (Fin m') (Fin n') α :=
  B.submatrix r (r.col h')

/-- The entries of a reindexed matrix. -/
@[simp]
theorem matrixReindex_apply (h' : n' ≤ m') (B : Matrix (Fin m) (Fin n) α)
    (r : ReindexingMap m' n' m n) (p : Fin m') (q : Fin n') :
    matrixReindex h' B r p q = B (r p) (r.col h' q) :=
  rfl

/-- Reindexing along the identity does nothing. -/
@[simp]
theorem matrixReindex_id (h : n ≤ m) (B : Matrix (Fin m) (Fin n) α) :
    matrixReindex h B (ReindexingMap.id m n) = B :=
  rfl

/-- **Reindexing twice is reindexing along the composite**: `(Bʳ)ˢ = B^{r ∘ s}`. -/
theorem matrixReindex_matrixReindex (h' : n' ≤ m') (h'' : n'' ≤ m'')
    (B : Matrix (Fin m) (Fin n) α) (r : ReindexingMap m' n' m n)
    (s : ReindexingMap m'' n'' m' n') :
    matrixReindex h'' (matrixReindex h' B r) s = matrixReindex h'' B (r.comp s) :=
  rfl

end Reindex

section Mutation

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {m n m' n' : ℕ}

omit [IsStrictOrderedRing R] in
/-- **Mutation commutes with reindexing**: `μ_q(Bʳ) = (μ_{r(q)} B)ʳ`.

This generalises [FWZ, Lemma 4.1.2] from restrictions to arbitrary reindexing maps. -/
@[cluster_algebras "lem_matmut_reindex"]
theorem matrixMutation_matrixReindex (h : n ≤ m) (h' : n' ≤ m') (B : Matrix (Fin m) (Fin n) R)
    (r : ReindexingMap m' n' m n) (q : Fin n') :
    matrixMutation h' (matrixReindex h' B r) q
      = matrixReindex h' (matrixMutation h B (r.col h' q)) r := by
  ext p j
  have hrow : ∀ p : Fin m', (p = Fin.castLE h' q ↔ r p = Fin.castLE h (r.col h' q)) := by
    intro p
    rw [ReindexingMap.castLE_col]
    exact ⟨fun hp => hp ▸ rfl, fun hp => r.injective hp⟩
  have hcol : ∀ j : Fin n', (j = q ↔ r.col h' j = r.col h' q) :=
    fun j => ⟨fun hj => hj ▸ rfl, fun hj => r.col_injective h' hj⟩
  rw [matrixReindex_apply]
  by_cases hpj : p = Fin.castLE h' q ∨ j = q
  · have hpj' : r p = Fin.castLE h (r.col h' q) ∨ r.col h' j = r.col h' q :=
      hpj.imp (hrow p).1 (hcol j).1
    rw [matrixMutation_apply_of_eq h' _ q hpj, matrixMutation_apply_of_eq h B _ hpj',
      matrixReindex_apply]
  · rw [not_or] at hpj
    obtain ⟨hp, hj⟩ := hpj
    have hp' : r p ≠ Fin.castLE h (r.col h' q) := mt (hrow p).2 hp
    have hj' : r.col h' j ≠ r.col h' q := mt (hcol j).2 hj
    rw [matrixMutation_apply_of_ne h' _ q hp hj, matrixMutation_apply_of_ne h B _ hp' hj']
    simp only [matrixReindex_apply, ReindexingMap.castLE_col]

attribute [cluster_algebras "def_matrix_mutation_sequence"] matrixMutationList

omit [IsStrictOrderedRing R] in
/-- **Mutation along a sequence commutes with reindexing**:
`μ_s(Bʳ) = (μ_{r(s)} B)ʳ`, where `r(s)` applies the column map of `r` to each direction. -/
@[cluster_algebras "lem_matmut_sequence_reindex"]
theorem matrixMutationList_matrixReindex (h : n ≤ m) (h' : n' ≤ m')
    (B : Matrix (Fin m) (Fin n) R) (r : ReindexingMap m' n' m n) (s : List (Fin n')) :
    matrixMutationList h' (matrixReindex h' B r) s
      = matrixReindex h' (matrixMutationList h B (s.map (r.col h'))) r := by
  induction s generalizing B with
  | nil => rfl
  | cons q s ih =>
    rw [matrixMutationList_cons, matrixMutation_matrixReindex h h', ih, List.map_cons,
      matrixMutationList_cons]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **Reindexing preserves extended skew-symmetrizability.** A skew-symmetrizing vector `d`
of the principal part of `B` pulls back to the skew-symmetrizing vector `d ∘ r.col` of the
principal part of `Bʳ`. In particular a restriction of an extended skew-symmetrizable matrix
is extended skew-symmetrizable [FWZ, Definition 4.1.1]. -/
@[cluster_algebras "lem_reindex_ext_skew_symmetrizable"]
theorem ExtSkewSymmetrizable.matrixReindex (h : n ≤ m) (h' : n' ≤ m')
    {B : Matrix (Fin m) (Fin n) R} (hB : ExtSkewSymmetrizable h B)
    (r : ReindexingMap m' n' m n) :
    ExtSkewSymmetrizable h' (ClusterAlgebras.matrixReindex h' B r) := by
  obtain ⟨d, hpos, hd⟩ := hB
  refine ⟨d ∘ r.col h', fun i => hpos _, fun i j => ?_⟩
  simpa only [Matrix.submatrix_apply, id, Function.comp_apply, matrixReindex_apply,
    ReindexingMap.castLE_col] using hd (r.col h' i) (r.col h' j)

end Mutation

end ClusterAlgebras

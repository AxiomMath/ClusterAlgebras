/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Folding.Defs

/-!
# Folding: the hexagon

The *hexagon matrix* `H` is the `6 × 6` skew-symmetric matrix of the oriented hexagon,
`h_{i, i+1} = 1` and `h_{i+1, i} = -1` with indices modulo `6`. It carries the *antipodal action*
of `ℤ/2ℤ`, whose generator sends `i` to `i + 3`; its orbits are the three antipodal pairs.

The matrix `H` is admissible for the antipodal action, but mutating it at any orbit `K` (that is,
along the increasing sequence `s_K`) produces a matrix `D` that is not: there are `i ∼ i'` and a
column `j` with `d_{ij} d_{i'j} < 0`, violating the sign condition `b_{ij} b_{i'j} ≥ 0` of
`ClusterAlgebras.IsGroupAdmissible`. For `K = {0, 3}`, `d_{12} = 1` and `d_{42} = -1` while
`1 ∼ 4`. So admissibility does not in general propagate under orbit mutation.

## Main definitions

* `ClusterAlgebras.hexagonMatrix`: the hexagon matrix `H`.
* `ClusterAlgebras.HexagonGroup`: the group `ℤ/2ℤ`, written multiplicatively, with its
  antipodal action on `Fin 6`.

## Main results

* `ClusterAlgebras.hexagon_mem_orbit_iff`: the orbits of the antipodal action are `{i, i + 3}`.
* `ClusterAlgebras.hexagon_isGroupAdmissible`: `H` is admissible for the antipodal action.
* `ClusterAlgebras.hexagon_not_isGroupAdmissible_matrixMutationList`: for every orbit `K`,
  `μ_{s_K}(H)` is not admissible.

## Implementation notes

* Indices are `Fin 6`, so `0, …, 5` where [FWZ] writes `1, …, 6`; the orbits `{1, 4}`,
  `{2, 5}`, `{3, 6}` of [FWZ] are `{0, 3}`, `{1, 4}`, `{2, 5}` here. Addition on `Fin 6` is
  addition modulo `6`.

* The group is a type synonym `ClusterAlgebras.HexagonGroup` of `Multiplicative (ZMod 2)`, so
  that the antipodal action is an instance on the synonym and not on `Multiplicative (ZMod 2)`
  itself, where it would be one action among many.

* Every statement is about explicit finite data, and is proved by evaluating it.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Section 4.4.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix MulAction

/-- The **hexagon matrix** `H`, the `6 × 6` integer matrix with `h_{i, i+1} = 1`,
`h_{i+1, i} = -1`, indices modulo `6`, and all other entries `0`. -/
@[cluster_algebras "def_hexagon_matrix"]
def hexagonMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun i j => if j = i + 1 then 1 else if i = j + 1 then -1 else 0

/-- The group `ℤ/2ℤ`, written multiplicatively, acting on `Fin 6` by the antipodal action
(`ClusterAlgebras.hexagonMulAction`). -/
def HexagonGroup : Type := Multiplicative (ZMod 2)

/-- `HexagonGroup` is the group `Multiplicative (ZMod 2)`. -/
instance : Group HexagonGroup := inferInstanceAs (Group (Multiplicative (ZMod 2)))

/-- `HexagonGroup` is finite, with two elements. -/
instance : Fintype HexagonGroup := inferInstanceAs (Fintype (Multiplicative (ZMod 2)))

/-- `HexagonGroup` has decidable equality. -/
instance : DecidableEq HexagonGroup := inferInstanceAs (DecidableEq (Multiplicative (ZMod 2)))

/-- The **antipodal action** of `ℤ/2ℤ` on `Fin 6`: the generator sends `i` to `i + 3`, modulo
`6`. -/
@[cluster_algebras "def_hexagon_action"]
instance hexagonMulAction : MulAction HexagonGroup (Fin 6) where
  smul g i := if Multiplicative.toAdd (g : Multiplicative (ZMod 2)) = 0 then i else i + 3
  one_smul := by decide
  mul_smul := by decide

/-- The orbits of the antipodal action are the antipodal pairs `{i, i + 3}`. -/
@[cluster_algebras "def_hexagon_action"]
theorem hexagon_mem_orbit_iff {i i' : Fin 6} :
    i' ∈ orbit HexagonGroup i ↔ i' = i ∨ i' = i + 3 := by
  rw [mem_orbit_iff]
  revert i i'
  decide

/-- Membership in an orbit of the antipodal action is decidable. -/
instance (i i' : Fin 6) : Decidable (i' ∈ orbit HexagonGroup i) :=
  decidable_of_iff _ hexagon_mem_orbit_iff.symm

/-- The hexagon matrix is admissible for the antipodal action. -/
@[cluster_algebras "lem_hexagon_admissible"]
theorem hexagon_isGroupAdmissible : IsGroupAdmissible HexagonGroup le_rfl hexagonMatrix where
  smul_eq := by decide
  eq_zero := by decide
  mul_nonneg := by decide

/-- The orbit of `i` under the antipodal action, as a finite set, is `{i, i + 3}`. -/
theorem hexagon_filter_mem_orbit (i : Fin 6) :
    Finset.univ.filter (· ∈ orbit HexagonGroup i) = {i, i + 3} := by
  ext i'
  simp [hexagon_mem_orbit_iff]

/-- The increasing sequence of a two-element set `{a, b}` with `a < b` is `[a, b]`. -/
private theorem increasingSeq_pair_of_lt {n : ℕ} {a b : Fin n} (h : a < b) :
    increasingSeq ({a, b} : Finset (Fin n)) = [a, b] := by
  rw [increasingSeq, Finset.sort_insert _ (by simpa using h.le) (by simpa using h.ne),
    Finset.sort_singleton]

/-- For every orbit `K` of the antipodal action, the mutation `μ_{s_K}(H)` of the hexagon
matrix along the increasing sequence of `K` is not admissible. -/
@[cluster_algebras "lem_hexagon_not_propagating"]
theorem hexagon_not_isGroupAdmissible_matrixMutationList (i : Fin 6) :
    ¬ IsGroupAdmissible HexagonGroup le_rfl (matrixMutationList le_rfl hexagonMatrix
      (increasingSeq (Finset.univ.filter (· ∈ orbit HexagonGroup i)))) := by
  intro h
  rw [hexagon_filter_mem_orbit] at h
  fin_cases i
  all_goals first
    | rw [increasingSeq_pair_of_lt (by decide)] at h
    | rw [Finset.pair_comm, increasingSeq_pair_of_lt (by decide)] at h
  all_goals exact absurd h.mul_nonneg (by decide)

end ClusterAlgebras

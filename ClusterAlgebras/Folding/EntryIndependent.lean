/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Folding.Defs

/-!
# Folding: entries of the folded matrix, and signs over orbits

Let `B` be a `G`-admissible `m × n` integer matrix. This file proves two facts about the
entries of `B` on pairs of orbits.

The entry `b^G_{pq} = ∑_{i ∈ θ(p)} b_{i j_q}` of the folded matrix is defined with the least
element `j_q` of the mutable orbit `θ(q)`; any `j ∈ θ(q)` gives the same sum. Indeed, if
`g(j_q) = j` then `i ↦ g(i)` permutes `θ(p)` and `b_{g(i) j} = b_{i j_q}` by condition (2).

On a pair of orbits `I` and `J`, the entries of `B` all have the same weak sign:
`b_{ij} b_{i'j'} ≥ 0` for `i, i' ∈ I` and `j, j' ∈ J`. Taking `g` with `g(j') = j`,
condition (2) gives `b_{i'j'} = b_{g(i') j}`, and `g(i') ∼ i`, so condition (4) applies.

## Main results

* `ClusterAlgebras.foldedMatrix_apply_eq_sum_of_mem_cols`: `b^G_{pq} = ∑_{i ∈ θ(p)} b_{ij}`
  for every `j ∈ θ(q)`.
* `ClusterAlgebras.IsGroupAdmissible.mul_nonneg_of_mem_orbit`: `b_{ij} b_{i'j'} ≥ 0` for
  `i ∼ i'` and `j ∼ j'`.

## Implementation notes

* In [FWZ] the sign lemma is stated for a mutable orbit `J`. A column `j : Fin n` is the
  row `Fin.castLE hmn j`, so here `j ∼ j'` is `Fin.castLE hmn j' ∈ orbit G (Fin.castLE hmn j)`,
  which says no more than that `j` and `j'` are columns in one orbit. The orbit containing
  them need not be mutable, so this is a generalisation. The same statement is also given
  for `i, i' ∈ θ(p)` and `j, j' ∈ θ(q)`
  (`ClusterAlgebras.IsGroupAdmissible.mul_nonneg_of_mem_orbit_of_mem_cols`).

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Section 4.4.
-/

@[expose] public section

namespace ClusterAlgebras

open MulAction

variable {G : Type*} [Group G] {m n mG nG : ℕ} [MulAction G (Fin m)] {hmn : n ≤ m}
  {B : Matrix (Fin m) (Fin n) ℤ}

/-- An entry of the folded matrix may be computed with any column `j` of the orbit `θ(q)`:
`b^G_{pq} = ∑_{i ∈ θ(p)} b_{ij}`. -/
@[cluster_algebras "lem_folded_entry_independent"]
theorem foldedMatrix_apply_eq_sum_of_mem_cols (hB : IsGroupAdmissible G hmn B)
    (θ : OrbitLabelling G m n mG nG) (p : Fin mG) (q : Fin nG) {j : Fin n}
    (hj : j ∈ θ.cols hmn q) : foldedMatrix θ B p q = ∑ i ∈ θ.orbit p, B i j := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.1 <|
    θ.mem_orbit_of_mem (θ.mem_cols.1 (θ.colRep_mem_cols hmn q)) (θ.mem_cols.1 hj)
  rw [foldedMatrix_apply]
  refine Finset.sum_nbij' (fun i => g • i) (fun i => g⁻¹ • i)
    (fun i hi => θ.smul_mem_orbit hi g) (fun i hi => θ.smul_mem_orbit hi g⁻¹)
    (fun i _ => inv_smul_smul g i) (fun i _ => smul_inv_smul g i)
    fun i _ => (hB.smul_eq g i _ j hg.symm).symm

/-- Over a pair of orbits, the entries of a `G`-admissible matrix have one weak sign:
`b_{ij} b_{i'j'} ≥ 0` whenever `i ∼ i'` and the columns `j, j'` satisfy `j ∼ j'`. -/
@[cluster_algebras "lem_folding_signs"]
theorem IsGroupAdmissible.mul_nonneg_of_mem_orbit (hB : IsGroupAdmissible G hmn B)
    {i i' : Fin m} (hi : i' ∈ orbit G i) {j j' : Fin n}
    (hj : Fin.castLE hmn j' ∈ orbit G (Fin.castLE hmn j)) : 0 ≤ B i j * B i' j' := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.1 hj
  rw [← hB.smul_eq g⁻¹ i' j' j (by rw [← hg, inv_smul_smul])]
  exact hB.mul_nonneg i _ (orbit_eq_iff.2 hi ▸ mem_orbit i' g⁻¹) j

/-- Over orbits `θ(p)` and `θ(q)`, the entries of a `G`-admissible matrix have one weak sign:
`b_{ij} b_{i'j'} ≥ 0` for `i, i' ∈ θ(p)` and `j, j' ∈ θ(q)`. -/
theorem IsGroupAdmissible.mul_nonneg_of_mem_orbit_of_mem_cols (hB : IsGroupAdmissible G hmn B)
    (θ : OrbitLabelling G m n mG nG) {p : Fin mG} {q : Fin nG} {i i' : Fin m}
    (hi : i ∈ θ.orbit p) (hi' : i' ∈ θ.orbit p) {j j' : Fin n} (hj : j ∈ θ.cols hmn q)
    (hj' : j' ∈ θ.cols hmn q) : 0 ≤ B i j * B i' j' :=
  hB.mul_nonneg_of_mem_orbit (θ.mem_orbit_of_mem hi hi')
    (θ.mem_orbit_of_mem (θ.mem_cols.1 hj) (θ.mem_cols.1 hj'))

end ClusterAlgebras

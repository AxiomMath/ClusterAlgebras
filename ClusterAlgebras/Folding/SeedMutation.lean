/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Folding.Exchange
public import ClusterAlgebras.Folding.MutationFolding

/-!
# Folding: orbit mutation of an admissible seed

Given folding data, let `(x̃, B̃)` be a `(G, ψ)`-admissible seed, `r` a mutable label and
`K = θ(r)`, and write `μ_{s_K}` for mutation along the increasing sequence of `K`. This file
shows that orbit mutation is compatible with folding seeds, in two ways.

First, if `μ_{s_K}(B̃)` is again `G`-admissible, then `μ_{s_K}(x̃, B̃)` is again
`(G, ψ)`-admissible. Its matrix is `μ_{s_K}(B̃)`; matrix mutation preserves skew-symmetry of
the principal part; its entries lie in `P`; and `ψ` is constant on the entries over an orbit:
over `K` every entry is sent by `ψ` to the new entry of the folded exchange relation, and over
any other orbit the entries are those of `x̃`.

Second, without any hypothesis on `μ_{s_K}(B̃)`, `(μ_{s_K}(x̃, B̃))ᴳ = μ_r((x̃, B̃)ᴳ)`: folding
commutes with orbit mutation. On matrices this is `(μ_{s_K}(B̃))ᴳ = μ_r(B̃ᴳ)`. On clusters,
the entry at a label `p ≠ r` is read at the least element `i_p` of `θ(p)`, an orbit disjoint
from `K`, where `μ_{s_K}` changes nothing; and the entry at `r` is read at `i_r ∈ K`, where the
folded exchange relation gives the new entry of `μ_r((x̃, B̃)ᴳ)`.

## Main results

* `ClusterAlgebras.matrixMutationList_castLE_apply_eq_neg`: mutation along any sequence keeps
  the principal part of a matrix skew-symmetric.
* `ClusterAlgebras.IsFoldAdmissibleSeed.seedMutationSeq_increasingSeq`: if `μ_{s_K}(B̃)` is
  `G`-admissible, then `μ_{s_K}(x̃, B̃)` is `(G, ψ)`-admissible.
* `ClusterAlgebras.foldedSeed_seedMutationSeq_increasingSeq`:
  `(μ_{s_K}(x̃, B̃))ᴳ = μ_r((x̃, B̃)ᴳ)`.

## Implementation notes

* Skew-symmetry of the principal part under mutation is proved directly, rather than as
  preservation of the skew-symmetrizing vector `(1, …, 1)`, from the closed form
  `μ_k(B)_{ij} = b_{ij} + max(0, b_{ik}) max(0, b_{kj}) - max(0, -b_{ik}) max(0, -b_{kj})`
  off row and column `k`, and holds for matrices over any ordered commutative ring.

* An index `i : Fin m` lies in `K` when `i ∈ θ.orbit (Fin.castLE θ.le r)`; such indices are
  exactly the rows `Fin.castLE hmn k` of the columns `k ∈ θ.cols hmn r`
  (`ClusterAlgebras.OrbitLabelling.map_cols_eq_orbit`).

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Lemma 4.4.7.
-/

@[expose] public section

namespace ClusterAlgebras

open MulAction

/-! ### Mutation preserves skew-symmetry of the principal part -/

section Skew

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}
  {hmn : n ≤ m} {B : Matrix (Fin m) (Fin n) R}

/-- Mutation keeps the principal part of a matrix skew-symmetric: if `b_{ij} = -b_{ji}` for
all mutable `i, j`, then the same holds for `μ_k(B)`. -/
theorem matrixMutation_castLE_apply_eq_neg
    (hB : ∀ i j : Fin n, B (Fin.castLE hmn i) j = -B (Fin.castLE hmn j) i) (k i j : Fin n) :
    matrixMutation hmn B k (Fin.castLE hmn i) j =
      -matrixMutation hmn B k (Fin.castLE hmn j) i := by
  by_cases h : i = k ∨ j = k
  · have hi : Fin.castLE hmn i = Fin.castLE hmn k ∨ j = k := h.imp_left (congrArg _)
    have hj : Fin.castLE hmn j = Fin.castLE hmn k ∨ i = k := h.symm.imp_left (congrArg _)
    rw [matrixMutation_apply_of_eq hmn B k hi, matrixMutation_apply_of_eq hmn B k hj, hB i j]
  · obtain ⟨hik, hjk⟩ := not_or.1 h
    rw [matrixMutation_apply_of_ne_eq_max hmn B k
        (fun h => hik (Fin.castLE_injective hmn h)) hjk,
      matrixMutation_apply_of_ne_eq_max hmn B k
        (fun h => hjk (Fin.castLE_injective hmn h)) hik,
      hB i j, hB i k, hB k j]
    simp only [neg_neg]
    ring

/-- Mutation along any sequence keeps the principal part of a matrix skew-symmetric. -/
theorem matrixMutationList_castLE_apply_eq_neg
    (hB : ∀ i j : Fin n, B (Fin.castLE hmn i) j = -B (Fin.castLE hmn j) i) (s : List (Fin n))
    (i j : Fin n) :
    matrixMutationList hmn B s (Fin.castLE hmn i) j =
      -matrixMutationList hmn B s (Fin.castLE hmn j) i := by
  induction s generalizing B with
  | nil => exact hB i j
  | cons k s ih => exact ih (matrixMutation_castLE_apply_eq_neg hB k)

end Skew

/-! ### Orbit mutation of an admissible seed -/

variable {G : Type*} [Group G] {m n mG nG : ℕ} [MulAction G (Fin m)] {hmn : n ≤ m}
  {F : Type*} [Field F] [CharZero F] {w : Fin m → F} [Fact (AlgebraicIndependent ℚ w)]
  {FG : Type*} [Field FG] [CharZero FG] {z : Fin mG → FG} [Fact (AlgebraicIndependent ℚ z)]
  (θ : OrbitLabelling G m n mG nG)
  {ψ : FZSemifieldHom (universalSemifield w) (universalSemifield z)} {S : SeedData F m n}

/-- An index outside the orbit `θ(r)` of a mutable label `r` is not the row of any column of
`θ(r)`. -/
theorem OrbitLabelling.ne_castLE_of_notMem_orbit {r : Fin nG} {i : Fin m}
    (hi : i ∉ θ.orbit (Fin.castLE θ.le r)) : ∀ k ∈ θ.cols hmn r, i ≠ Fin.castLE hmn k :=
  fun _ hk hik => hi (hik ▸ θ.mem_cols.1 hk)

/-- **Orbit mutation preserves admissibility** (FWZ, Lemma 4.4.7, first assertion). Let
`(x̃, B̃)` be `(G, ψ)`-admissible, `r` a mutable label and `K = θ(r)`. If `μ_{s_K}(B̃)` is
`G`-admissible, then `μ_{s_K}(x̃, B̃)` is `(G, ψ)`-admissible. -/
@[cluster_algebras "lem_mut_folded_seeds_admissible"]
theorem IsFoldAdmissibleSeed.seedMutationSeq_increasingSeq (hS : IsFoldAdmissibleSeed G hmn ψ S)
    (r : Fin nG)
    (hB : IsGroupAdmissible G hmn
      (matrixMutationList hmn S.extExchangeMatrix (increasingSeq (θ.cols hmn r)))) :
    IsFoldAdmissibleSeed G hmn ψ (seedMutationSeq hmn S (increasingSeq (θ.cols hmn r))) where
  mem := hS.seedMutationSeq_extCluster_mem_universalSemifield _
  admissible := by
    rw [seedMutationSeq_extExchangeMatrix_eq_matrixMutationList]
    exact hB
  skew i j := by
    rw [seedMutationSeq_extExchangeMatrix_eq_matrixMutationList]
    exact matrixMutationList_castLE_apply_eq_neg hS.skew _ i j
  foldValue_eq i i' hii' := by
    by_cases hi : i ∈ θ.orbit (Fin.castLE θ.le r)
    · have hi' := θ.mem_of_mem_orbit hi hii'
      rw [← θ.map_cols_eq_orbit hmn, Finset.mem_map] at hi hi'
      obtain ⟨k, hk, rfl⟩ := hi
      obtain ⟨k', hk', rfl⟩ := hi'
      exact (hS.foldValue_seedMutationSeq_increasingSeq_extCluster θ r hk).trans
        (hS.foldValue_seedMutationSeq_increasingSeq_extCluster θ r hk').symm
    · have hi' : i' ∉ θ.orbit (Fin.castLE θ.le r) := fun hi' =>
        hi (θ.mem_of_mem_orbit hi' (mem_orbit_symm.1 hii'))
      rw [seedMutationSeq_increasingSeq_extCluster_of_notMem S (θ.ne_castLE_of_notMem_orbit hi),
        seedMutationSeq_increasingSeq_extCluster_of_notMem S (θ.ne_castLE_of_notMem_orbit hi')]
      exact hS.foldValue_eq i i' hii'

/-- **Folding commutes with orbit mutation** (FWZ, Lemma 4.4.7, second assertion). Let
`(x̃, B̃)` be `(G, ψ)`-admissible, `r` a mutable label and `K = θ(r)`. Then
`(μ_{s_K}(x̃, B̃))ᴳ = μ_r((x̃, B̃)ᴳ)`. -/
@[cluster_algebras "lem_mut_folded_seeds"]
theorem foldedSeed_seedMutationSeq_increasingSeq (hS : IsFoldAdmissibleSeed G hmn ψ S)
    (r : Fin nG) :
    foldedSeed θ ψ (seedMutationSeq hmn S (increasingSeq (θ.cols hmn r))) =
      seedMutation θ.le (foldedSeed θ ψ S) r := by
  refine SeedData.ext (funext fun p => ?_) ?_
  · dsimp only [foldedSeed, seedMutation]
    by_cases hp : p = Fin.castLE θ.le r
    · subst hp
      rw [Function.update_self, ← θ.castLE_colRep hmn r]
      exact hS.foldValue_seedMutationSeq_increasingSeq_extCluster θ r (θ.colRep_mem_cols hmn r)
    · rw [Function.update_of_ne hp, seedMutationSeq_increasingSeq_extCluster_of_notMem S
        (θ.ne_castLE_of_notMem_orbit fun h =>
          Finset.disjoint_left.1 (θ.disjoint_orbit hp) (θ.rep_mem p) h)]
  · change foldedMatrix θ (seedMutationSeq hmn S (increasingSeq (θ.cols hmn r))).extExchangeMatrix
      = matrixMutation θ.le (foldedMatrix θ S.extExchangeMatrix) r
    rw [seedMutationSeq_extExchangeMatrix_eq_matrixMutationList]
    exact foldedMatrix_matrixMutationList_increasingSeq hS.admissible θ r

end ClusterAlgebras

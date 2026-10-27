/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.LaurentPhenomenon.Trivialization
public import ClusterAlgebras.YPattern.Defs
public import ClusterAlgebras.Coefficients.TripleMatrix

/-!
# The covering matrix of a semifield homomorphism into a tropical semifield

Let `x̃ = (x₁, …, xₘ)` be algebraically independent over `ℚ` in a field of characteristic zero
and let `φ : ℚ_sf(x̃) → Trop(q̄_{n+1}, …, q̄_{m̄})` be a semifield homomorphism. Its
*covering matrix* is the `m̄ × m` integer matrix `Ψ = (ψᵢⱼ)` whose first `n` rows are the
first `n` unit vectors and whose `(i, j)` entry for `i > n` is the exponent of `q̄ᵢ` in
`φ(xⱼ)`.

In the situation of the rescaling theorem, where `ψ(xᵢ) = x̄ᵢ ε̄(φ(xᵢ))` for `i ≤ n` and
`ψ(xᵢ) = ε̄(φ(xᵢ))` for `i > n`, with `ε̄` the monomial evaluation at the frozen variables
`x̄_{n+1}, …, x̄_{m̄}`, one has `ψ(xⱼ) = ∏ᵢ x̄ᵢ ^ ψᵢⱼ` for every `j`; this is the defining
property of `Ψ` in FWZ.

The main result identifies the initial extended matrix of the rescaled pattern: if
`x̃ = x̃(t₀)` is the extended cluster of a seed with extended exchange matrix `B̃₀` and
principal part `B₀`, and `ȳₖ = φ(ŷₖ)` for the `ŷ`-tuple of that seed, then
`B̃(ȳ, B₀) = Ψ B̃₀`. Indeed the first `n` rows of `Ψ` are unit vectors, and for `i > n` the
exponent of `q̄ᵢ` in `φ(ŷₖ) = ∏ⱼ φ(xⱼ) ^ bⱼₖ` is `∑ⱼ ψᵢⱼ bⱼₖ`.

## Main definitions

* `ClusterAlgebras.coveringMatrix`: the covering matrix `Ψ` of `φ`.

## Main results

* `ClusterAlgebras.coe_apply_eq_prod_zpow_coveringMatrix`: under the hypotheses of the
  rescaling theorem on `ψ`, `ψ(xⱼ) = ∏ᵢ x̄ᵢ ^ ψᵢⱼ`.
* `ClusterAlgebras.tripleExtendedMatrix_eq_coveringMatrix_mul`: `B̃(ȳ, B₀) = Ψ B̃₀`.

## Implementation notes

* Indices are `Fin m` and `Fin m̄`, so FWZ's rows `i ≤ n` are those of value below
  `n`. FWZ's standing assumptions `1 ≤ n ≤ m` and `m̄ ≥ n` are not needed to define
  `Ψ` and are dropped; `n ≤ m` enters the main result only through the principal part.
* The algebraic independence of `x̃` over `ℚ` in a field of characteristic zero is the pair of
  instance arguments `[CharZero F] [Fact (AlgebraicIndependent ℚ x)]` that make `ℚ_sf(x̃)` a
  semifield.
* FWZ state the main result "in the situation of the rescaling theorem". Its proof
  uses only that `ȳₖ = φ(ŷₖ)` at the initial vertex, for the seed whose extended cluster is
  `x̃`; the result is stated for an arbitrary seed `S` (not necessarily a vertex of a seed
  pattern) and an arbitrary tuple `ȳ` with this property, which is a generalisation. For a
  seed pattern `P` and `x̃ = x̃(t₀)`, apply it to `S = P t₀`.
* In the remark `ψ(xⱼ) = ∏ᵢ x̄ᵢ ^ ψᵢⱼ` the monomial evaluation `ε̄` appears through its value
  in the field, `tropicalEval`, which is the simp normal form of `monomialEvaluation`
  (`coe_monomialEvaluation`); no nonvanishing hypothesis on the `x̄ᵢ` is then needed.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras, Chapter 4*,
  Section 4.3, the matrix `Ψ` before Proposition 4.3.4, and Proposition 4.3.4.
-/

@[expose] public section

namespace ClusterAlgebras

open TropicalSemifield

variable {F : Type*} [Field F] [CharZero F] {m n m' : ℕ} {x : Fin m → F}
  [Fact (AlgebraicIndependent ℚ x)]

/-- The **covering matrix** `Ψ = (ψᵢⱼ)` of a semifield homomorphism
`φ : ℚ_sf(x̃) → Trop(q̄_{n+1}, …, q̄_{m'})`: the `m' × m` integer matrix with `ψᵢⱼ = 1` if
`i = j < n`, `ψᵢⱼ = 0` if `i < n` and `i ≠ j`, and, for `n ≤ i`, `ψᵢⱼ` the exponent of `q̄ᵢ`
in `φ(xⱼ)`. -/
@[cluster_algebras "def_covering_matrix"]
def coveringMatrix
    (φ : FZSemifieldHom (universalSemifield x) (TropicalSemifield (FrozenIndex m' n))) :
    Matrix (Fin m') (Fin m) ℤ :=
  Matrix.of fun i j =>
    if h : (i : ℕ) < n then (if (i : ℕ) = j then 1 else 0)
    else exponent (φ ⟨x j, mem_universalSemifield_self x j⟩) ⟨i, not_lt.1 h⟩

section CoveringMatrix

variable (φ : FZSemifieldHom (universalSemifield x) (TropicalSemifield (FrozenIndex m' n)))

/-- For `i < n`, row `i` of the covering matrix is the `i`-th unit vector. -/
theorem coveringMatrix_apply_of_lt {i : Fin m'} (hi : (i : ℕ) < n) (j : Fin m) :
    coveringMatrix φ i j = if (i : ℕ) = j then 1 else 0 := by
  simp [coveringMatrix, hi]

/-- For a frozen position `i`, the `(i, j)` entry of the covering matrix of `φ` is the exponent
of `q̄ᵢ` in `φ(xⱼ)`. -/
@[simp]
theorem coveringMatrix_apply_frozenIndex (i : FrozenIndex m' n) (j : Fin m) :
    coveringMatrix φ i.1 j = exponent (φ ⟨x j, mem_universalSemifield_self x j⟩) i := by
  simp [coveringMatrix, not_lt.2 i.2]

/-- **The covering matrix records `ψ`.** If `ψ : ℚ_sf(x̃) → ℚ_sf(x̄)` satisfies
`ψ(xᵢ) = x̄ᵢ ε̄(φ(xᵢ))` for `i < n` and `ψ(xᵢ) = ε̄(φ(xᵢ))` for `n ≤ i`, with `ε̄` the monomial
evaluation at `x̄_{n+1}, …, x̄_{m'}`, then `ψ(xⱼ) = ∏ᵢ x̄ᵢ ^ ψᵢⱼ` for every `j`. -/
theorem coe_apply_eq_prod_zpow_coveringMatrix {F' : Type*} [Field F'] [CharZero F']
    (hm' : n ≤ m') {x' : Fin m' → F'} [Fact (AlgebraicIndependent ℚ x')]
    (ψ : FZSemifieldHom (universalSemifield x) (universalSemifield x'))
    (hψ : ∀ (i : Fin m) (hi : (i : ℕ) < n),
      (ψ ⟨x i, mem_universalSemifield_self x i⟩ : F') = x' ⟨i, hi.trans_le hm'⟩ *
        tropicalEval (fun a : FrozenIndex m' n => x' a) (φ ⟨x i, mem_universalSemifield_self x i⟩))
    (hψ' : ∀ i : Fin m, n ≤ (i : ℕ) →
      (ψ ⟨x i, mem_universalSemifield_self x i⟩ : F') =
        tropicalEval (fun a : FrozenIndex m' n => x' a) (φ ⟨x i, mem_universalSemifield_self x i⟩))
    (j : Fin m) :
    (ψ ⟨x j, mem_universalSemifield_self x j⟩ : F') = ∏ i, x' i ^ coveringMatrix φ i j := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin m' => n ≤ (i : ℕ))]
  have hfrozen : ∏ i : FrozenIndex m' n, x' i ^ coveringMatrix φ i j =
      tropicalEval (fun a : FrozenIndex m' n => x' a) (φ ⟨x j, mem_universalSemifield_self x j⟩) :=
    Finset.prod_congr rfl fun i _ => by rw [coveringMatrix_apply_frozenIndex]
  have hmut : ∀ i : {i : Fin m' // ¬n ≤ (i : ℕ)},
      x' i ^ coveringMatrix φ i j = if (i : ℕ) = j then x' i else 1 := fun i => by
    rw [coveringMatrix_apply_of_lt φ (not_le.1 i.2)]
    split_ifs <;> simp
  change _ = (∏ i : FrozenIndex m' n, x' i ^ coveringMatrix φ i j) * _
  rw [hfrozen, Fintype.prod_congr _ _ hmut]
  by_cases hj : (j : ℕ) < n
  · rw [hψ j hj, mul_comm, Fintype.prod_eq_single ⟨⟨j, hj.trans_le hm'⟩, not_le.2 hj⟩
      fun i hi => if_neg fun h => hi (Subtype.ext (Fin.ext h))]
    simp
  · rw [hψ' j (not_lt.1 hj), Fintype.prod_eq_one _ fun i => if_neg (by have := i.2; omega),
      mul_one]

end CoveringMatrix

omit [CharZero F] in
/-- The `ŷ`-tuple of a seed lies in the universal semifield of its extended cluster:
`ŷⱼ = ∏ᵢ xᵢ ^ bᵢⱼ` is a product of integer powers of the generators. -/
theorem yHat_mem_universalSemifield_extCluster (S : SeedData F m n) (j : Fin n) :
    yHat S j ∈ universalSemifield S.extCluster :=
  prod_mem_universalSemifield fun i _ =>
    zpow_mem_universalSemifield (mem_universalSemifield_self _ i) _

/-- Let `S = (x̃, B̃₀)` be a seed with principal part `B₀`, let
`φ : ℚ_sf(x̃) → Trop(q̄_{n+1}, …, q̄_{m'})` be a semifield homomorphism with covering matrix
`Ψ`, and let `ȳ` be a tuple with `ȳₖ = φ(ŷₖ)` for the `ŷ`-tuple of `S`. Then
`B̃(ȳ, B₀) = Ψ B̃₀`. -/
@[cluster_algebras "prop_covering_matrix"]
theorem tripleExtendedMatrix_eq_coveringMatrix_mul (hmn : n ≤ m)
    (S : SeedData F m n) [Fact (AlgebraicIndependent ℚ S.extCluster)]
    (φ : FZSemifieldHom (universalSemifield S.extCluster) (TropicalSemifield (FrozenIndex m' n)))
    (y : Fin n → TropicalSemifield (FrozenIndex m' n))
    (hy : ∀ k, y k = φ ⟨yHat S k, yHat_mem_universalSemifield_extCluster S k⟩) :
    tripleExtendedMatrix y (principalPart hmn S.extExchangeMatrix) =
      coveringMatrix φ * S.extExchangeMatrix := by
  ext i k
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) < n
  · rw [tripleExtendedMatrix_apply_of_lt _ _ hi,
      Finset.sum_eq_single (Fin.castLE hmn ⟨i, hi⟩) (fun j _ hj => ?_) (by simp)]
    · rw [coveringMatrix_apply_of_lt φ hi, Fin.val_castLE, if_pos rfl, one_mul]
      rfl
    · rw [coveringMatrix_apply_of_lt φ hi, if_neg fun h => hj (Fin.ext h.symm), zero_mul]
  · let a : FrozenIndex m' n := ⟨i, not_lt.1 hi⟩
    change tripleExtendedMatrix y _ a.1 k = ∑ j, coveringMatrix φ a.1 j * _
    have h : (⟨yHat S k, yHat_mem_universalSemifield_extCluster S k⟩ :
        universalSemifield S.extCluster) =
        ∏ j, (⟨S.extCluster j, mem_universalSemifield_self _ j⟩ :
          universalSemifield S.extCluster) ^ S.extExchangeMatrix j k :=
      Subtype.ext (by rw [universalSemifield.coe_prod]; rfl)
    rw [tripleExtendedMatrix_apply_frozenIndex, hy, h, map_prod, exponent_prod, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zpow, exponent_zpow, coveringMatrix_apply_frozenIndex, Pi.smul_apply, smul_eq_mul,
      mul_comm]

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Tropical.Mutation

/-!
# Seed mutation and mutation of triples agree

Let `(x̃, B̃)` be a labeled seed and `k ∈ [1, n]`. Its triple `(x, y, B)` consists of the cluster
`x = (x₁, …, xₙ)`, the coefficient tuple `y` of `B̃` in `Trop(q_{n+1}, …, q_m)` and the
principal part `B` of `B̃`, with frozen variables `x_{n+1}, …, x_m`. Then the triple of
`μₖ(x̃, B̃)` is the mutation in direction `k` of the triple of `(x̃, B̃)`, with the same frozen
variables, which seed mutation does not change.

The principal part and the coefficient tuple are handled by `principalPart_matrixMutation`
and `coefficientTuple_matrixMutation`. For the cluster, the exponent of `yₖ / (yₖ ⊕ 1)` at a
frozen position `i` is `max(bᵢₖ, 0)` and that of `1 / (yₖ ⊕ 1)` is `max(-bᵢₖ, 0)`, so that
`ε(yₖ / (yₖ ⊕ 1))` and `ε(1 / (yₖ ⊕ 1))` are the frozen parts of the exchange monomials
`M⁺ₖ(x̃, B̃)` and `M⁻ₖ(x̃, B̃)`.

Conversely, a seed is determined by its triple and its frozen variables: the first `n` rows of
`B̃` form the principal part, and its frozen rows are the exponent vectors of the coefficient
tuple.

## Main results

* `ClusterAlgebras.SeedData.frozenTuple_seedMutation`: seed mutation does not change the frozen
  variables.
* `ClusterAlgebras.SeedData.toSeedTriple_seedMutation`: the triple of `μₖ(x̃, B̃)` is the
  mutation of the triple of `(x̃, B̃)`.
* `ClusterAlgebras.SeedData.eq_of_toSeedTriple_eq`: a seed is determined by its triple and its
  frozen variables.

## Implementation notes

The agreement is usually stated for a labeled seed, but the identity uses no property of the
seed: the frozen parts of the exchange monomials are products of natural powers, and both
formulas for the new cluster variable divide by the same `xₖ`. So it is stated for arbitrary
seed data, and `IsLabeledSeed.toSeedTriple_seedMutation` is the form for labeled seeds.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- A product over `Fin m` splits into the product over the first `n` positions and the product
over the frozen positions. -/
theorem prod_castLE_mul_prod_frozenIndex {M : Type*} [CommMonoid M] (hmn : n ≤ m)
    (f : Fin m → M) :
    (∏ j : Fin n, f (Fin.castLE hmn j)) * ∏ i : FrozenIndex m n, f i.1 = ∏ i, f i := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin m => (i : ℕ) < n) f]
  congr 1
  · exact Fintype.prod_equiv (Fin.castLEquiv hmn) _ _ fun _ => rfl
  · exact Fintype.prod_equiv (Equiv.subtypeEquivRight fun _ => not_lt.symm) _ _ fun _ => rfl

/-- `ε(y / (y ⊕ 1)) = ∏ᵢ xᵢ ^ max(aᵢ, 0)`, where `a` is the exponent vector of `y`. -/
theorem tropicalEval_div_add_one {ι : Type*} [Fintype ι] (x : ι → F) (y : TropicalSemifield ι) :
    tropicalEval x (y / (y + 1)) = ∏ i, x i ^ (TropicalSemifield.exponent y i).toNat := by
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast]
  congr 1
  simp only [TropicalSemifield.exponent_div, Pi.sub_apply, TropicalSemifield.exponent_add,
    TropicalSemifield.exponent_one, Pi.zero_apply]
  omega

/-- `ε(1 / (y ⊕ 1)) = ∏ᵢ xᵢ ^ max(-aᵢ, 0)`, where `a` is the exponent vector of `y`. -/
theorem tropicalEval_one_div_add_one {ι : Type*} [Fintype ι] (x : ι → F)
    (y : TropicalSemifield ι) :
    tropicalEval x (1 / (y + 1)) = ∏ i, x i ^ (-TropicalSemifield.exponent y i).toNat := by
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast]
  congr 1
  simp only [TropicalSemifield.exponent_div, Pi.sub_apply, TropicalSemifield.exponent_add,
    TropicalSemifield.exponent_one, Pi.zero_apply]
  omega

/-- The positive exchange monomial `M⁺ₖ(x̃, B̃)` is `ε(yₖ / (yₖ ⊕ 1))` times the positive exchange
monomial of the cluster and the principal part, where `y` is the coefficient tuple of `B̃` and
`ε` evaluates at the frozen variables. -/
theorem exchangeMonomialPos_eq_tropicalEval_mul (hmn : n ≤ m) (x : Fin m → F)
    (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    exchangeMonomialPos x B k =
      tropicalEval (fun i : FrozenIndex m n => x i.1)
          (coefficientTuple B k / (coefficientTuple B k + 1)) *
        exchangeMonomialPos (fun j => x (Fin.castLE hmn j)) (principalPart hmn B) k := by
  rw [tropicalEval_div_add_one, exchangeMonomialPos_eq_prod, exchangeMonomialPos_eq_prod,
    mul_comm, ← prod_castLE_mul_prod_frozenIndex hmn]
  rfl

/-- The negative exchange monomial `M⁻ₖ(x̃, B̃)` is `ε(1 / (yₖ ⊕ 1))` times the negative exchange
monomial of the cluster and the principal part, where `y` is the coefficient tuple of `B̃` and
`ε` evaluates at the frozen variables. -/
theorem exchangeMonomialNeg_eq_tropicalEval_mul (hmn : n ≤ m) (x : Fin m → F)
    (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    exchangeMonomialNeg x B k =
      tropicalEval (fun i : FrozenIndex m n => x i.1) (1 / (coefficientTuple B k + 1)) *
        exchangeMonomialNeg (fun j => x (Fin.castLE hmn j)) (principalPart hmn B) k := by
  rw [tropicalEval_one_div_add_one, exchangeMonomialNeg_eq_prod, exchangeMonomialNeg_eq_prod,
    mul_comm, ← prod_castLE_mul_prod_frozenIndex hmn]
  rfl

/-- **Seed mutation does not change the frozen variables.** -/
@[cluster_algebras "lem_triple_mutation_agrees"]
theorem SeedData.frozenTuple_seedMutation (hmn : n ≤ m) (S : SeedData F m n) (k : Fin n) :
    (seedMutation hmn S k).frozenTuple = S.frozenTuple :=
  funext fun i => Function.update_of_ne (FrozenIndex.val_ne_castLE hmn i k) _ _

/-- **Seed mutation and mutation of triples agree.** The triple of `μₖ(x̃, B̃)` is the mutation
in direction `k` of the triple of `(x̃, B̃)`, with the frozen variables of `(x̃, B̃)`. The
identity holds for all seed data. -/
@[cluster_algebras "lem_triple_mutation_agrees"]
theorem SeedData.toSeedTriple_seedMutation (hmn : n ≤ m) (S : SeedData F m n) (k : Fin n) :
    (seedMutation hmn S k).toSeedTriple hmn = (S.toSeedTriple hmn).mutation S.frozenTuple k := by
  set B := S.extExchangeMatrix
  simp only [SeedData.toSeedTriple, SeedTriple.mutation, SeedTriple.mk.injEq]
  refine ⟨funext fun j => ?_, funext fun j => ?_, principalPart_matrixMutation hmn B k⟩
  · rcases eq_or_ne j k with rfl | hj
    · rw [Function.update_self]
      change Function.update S.extCluster (Fin.castLE hmn j) _ (Fin.castLE hmn j) = _
      rw [Function.update_self, exchangeMonomialPos_eq_tropicalEval_mul hmn,
        exchangeMonomialNeg_eq_tropicalEval_mul hmn]
      rfl
    · rw [Function.update_of_ne hj]
      exact Function.update_of_ne ((Fin.castLE_injective hmn).ne hj) _ _
  · have hkj : principalPart hmn B k j = B (Fin.castLE hmn k) j := rfl
    split_ifs with hj hb
    · exact hj ▸ coefficientTuple_matrixMutation_self hmn B k
    · rw [hkj] at hb ⊢
      exact coefficientTuple_matrixMutation_of_nonpos hmn B hj hb
    · rw [hkj] at hb ⊢
      exact coefficientTuple_matrixMutation_of_nonneg hmn B hj (not_le.1 hb).le

/-- **Seed mutation and mutation of triples agree**, for a labeled seed `(x̃, B̃)`: the
triple of `μₖ(x̃, B̃)` is the mutation in direction `k` of the triple of
`(x̃, B̃)`. The hypothesis is not needed; see `SeedData.toSeedTriple_seedMutation`. -/
theorem IsLabeledSeed.toSeedTriple_seedMutation (hmn : n ≤ m) {S : SeedData F m n}
    (_hS : IsLabeledSeed K hmn S) (k : Fin n) :
    (ClusterAlgebras.seedMutation hmn S k).toSeedTriple hmn =
      (S.toSeedTriple hmn).mutation S.frozenTuple k :=
  S.toSeedTriple_seedMutation hmn k

omit [Field F] in
/-- **A seed is determined by its triple and its frozen variables.** The first `n` entries of
the extended cluster form the cluster and the others the frozen variables; the first `n` rows
of the extended exchange matrix form the principal part, and the others are the exponent
vectors of the coefficient tuple. -/
theorem SeedData.eq_of_toSeedTriple_eq (hmn : n ≤ m) {S S' : SeedData F m n}
    (hT : S.toSeedTriple hmn = S'.toSeedTriple hmn) (hf : S.frozenTuple = S'.frozenTuple) :
    S = S' := by
  simp only [SeedData.toSeedTriple, SeedTriple.mk.injEq] at hT
  obtain ⟨hx, hy, hB⟩ := hT
  refine SeedData.ext (funext fun i => ?_) (Matrix.ext fun i j => ?_)
  · by_cases hi : (i : ℕ) < n
    · exact congrFun hx ⟨i, hi⟩
    · exact congrFun hf ⟨i, not_lt.1 hi⟩
  · by_cases hi : (i : ℕ) < n
    · exact congrFun (congrFun hB ⟨i, hi⟩) j
    · exact congrFun (congrArg TropicalSemifield.exponent (congrFun hy j)) ⟨i, not_lt.1 hi⟩

end ClusterAlgebras

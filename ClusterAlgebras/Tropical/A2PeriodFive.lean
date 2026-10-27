/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.RankTwo.Matrix
public import ClusterAlgebras.Tropical.TripleMutation
public import Mathlib.Tactic.FieldSimp

/-!
# Seeds of type `A₂` are `5`-periodic up to relabelling

Let `(x̃, B̃)` be a labeled seed of rank `2` whose principal part `B₀` has rows `(0, 1)` and
`(-1, 0)`, and mutate it alternately in directions `1` and `2`, five times. The result is the
seed `(x̃^τ, B̃^τ)` obtained by interchanging the labels `1` and `2`: its extended cluster is
`(x₂, x₁, x₃, …, xₘ)` and its extended exchange matrix has entries `b_{τ(i) τ(j)}`, `τ` being the
transposition of `1` and `2`.

The computation runs through the triples `(x(t), y(t), B(t))` of the seeds, whose coefficients
live in the tropical semifield of the frozen variables. Mutating a `2 × 2` skew-symmetrizable
matrix negates it, so `B(t) = (-1)ᵗ B₀`, and each mutation is one of two explicit rules on
triples. Writing `(y₁, y₂)` for the coefficient tuple of `(x̃, B̃)`, `s = y₁y₂ ⊕ y₁ ⊕ 1`, and
identifying a tropical element with its image under the evaluation `ε` at the frozen variables,
the successive triples are

| `t` | `y₁(t)` | `y₂(t)` | `x₁(t)` | `x₂(t)` |
| --- | --- | --- | --- | --- |
| `0` | `y₁` | `y₂` | `x₁` | `x₂` |
| `1` | `y₁⁻¹` | `y₁y₂/(y₁ ⊕ 1)` | `(y₁ + x₂)/(x₁(y₁ ⊕ 1))` | `x₂` |
| `2` | `y₂/s` | `(y₁ ⊕ 1)/(y₁y₂)` | `(y₁ + x₂)/(x₁(y₁ ⊕ 1))` | `(x₁y₁y₂ + y₁ + x₂)/(s x₁x₂)` |
| `3` | `s/y₂` | `1/(y₁(y₂ ⊕ 1))` | `(x₁y₂ + 1)/(x₂(y₂ ⊕ 1))` | `(x₁y₁y₂ + y₁ + x₂)/(s x₁x₂)` |
| `4` | `y₂⁻¹` | `y₁(y₂ ⊕ 1)` | `(x₁y₂ + 1)/(x₂(y₂ ⊕ 1))` | `x₁` |
| `5` | `y₂` | `y₁` | `x₂` | `x₁` |

The coefficient identities are instances of distributivity in the tropical semifield, and are
checked on exponents, where `⊕` is the minimum. A seed is determined by its triple and its
frozen variables, which mutation does not change, and this gives the result.

## Main results

* `ClusterAlgebras.ExtSkewSymmetrizable.matrixMutation_of_fin_two`: in rank `2`, mutation
  preserves extended skew-symmetrizability, since it negates the principal part.
* `ClusterAlgebras.IsLabeledSeed.seedMutation_of_extSkewSymmetrizable`: the mutation of a labeled
  seed is a labeled seed as soon as the mutated matrix is extended skew-symmetrizable.
* `ClusterAlgebras.tropicalEval_mul`, `ClusterAlgebras.tropicalEval_div`: when every `xᵢ` is
  nonzero, `ε` is multiplicative.
* `ClusterAlgebras.SeedTriple.a2_mutation_zero`, `ClusterAlgebras.SeedTriple.a2_mutation_one`:
  the two mutation rules of type `A₂` on triples.
* `ClusterAlgebras.a2_seedMutation_period_five`: seeds of type `A₂` with arbitrary coefficients
  are `5`-periodic up to relabelling.

## Implementation notes

FWZ index the seeds by `t ∈ [0, 5]` and assume each of them a labeled seed; here they
form a family indexed by `ℕ`, constrained only by the mutations from `t` to `t + 1` for `t < 5`,
and only `Σ(0)` is assumed a labeled seed. The others are then labeled seeds: in rank `2`
mutation negates the principal part, which keeps it skew-symmetrizable with the same
skew-symmetrizing vector, so the general preservation of skew-symmetrizability under mutation
is not needed. Directions `1` and `2` of FWZ are the indices `0` and `1`
of `Fin 2`. The transposition `τ` of `[1, m]` is `Equiv.swap` of the positions
`Fin.castLE hmn 0` and `Fin.castLE hmn 1`, and on the columns `[1, 2]` it is `Equiv.swap 0 1`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ}

/-- If `d` skew-symmetrizes `B`, it skew-symmetrizes `-B`. -/
private theorem IsSkewSymmetrizingVector.neg {R : Type*} [CommRing R] {n : ℕ}
    {B : Matrix (Fin n) (Fin n) R} {d : Fin n → ℤ} (hd : IsSkewSymmetrizingVector B d) :
    IsSkewSymmetrizingVector (-B) d :=
  ⟨hd.1, fun i j => by simp only [Matrix.neg_apply, mul_neg, hd.2 i j]⟩

/-- **In rank `2`, mutation preserves extended skew-symmetrizability.** Mutation negates the
`2 × 2` principal part, and `d` skew-symmetrizes `-B` whenever it skew-symmetrizes `B`. -/
theorem ExtSkewSymmetrizable.matrixMutation_of_fin_two {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (hmn : 2 ≤ m) {B : Matrix (Fin m) (Fin 2) R}
    (hB : ExtSkewSymmetrizable hmn B) (k : Fin 2) :
    ExtSkewSymmetrizable hmn (ClusterAlgebras.matrixMutation hmn B k) := by
  have h : SkewSymmetrizable (principalPart hmn B) := hB
  change SkewSymmetrizable (principalPart hmn (ClusterAlgebras.matrixMutation hmn B k))
  rw [principalPart_matrixMutation, h.matrixMutation_eq_neg_of_fin_two]
  obtain ⟨d, hd⟩ := h
  exact ⟨d, hd.neg⟩

/-- **The mutation of a labeled seed is a labeled seed** as soon as the mutated extended exchange
matrix is extended skew-symmetrizable. The extended cluster of `μₖ(x̃, B̃)` is a free generating
tuple whenever that of `(x̃, B̃)` is; only the matrix condition is assumed. -/
theorem IsLabeledSeed.seedMutation_of_extSkewSymmetrizable [CharZero K] {n : ℕ} (hmn : n ≤ m)
    {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) (k : Fin n)
    (hB : ExtSkewSymmetrizable hmn (matrixMutation hmn S.extExchangeMatrix k)) :
    IsLabeledSeed K hmn (ClusterAlgebras.seedMutation hmn S k) := by
  have hP := hS.exchangeMonomialPos_add_exchangeMonomialNeg_ne_zero hmn k
  have hdiag := hS.extExchangeMatrix_castLE_self hmn k
  have hPmem : ∀ A : Subalgebra K F, (∀ i, i ≠ Fin.castLE hmn k → S.extCluster i ∈ A) →
      exchangeMonomialPos S.extCluster S.extExchangeMatrix k +
        exchangeMonomialNeg S.extCluster S.extExchangeMatrix k ∈ A := fun A hA =>
    exchangeMonomialPos_add_exchangeMonomialNeg_mem K A fun i hi =>
      hA i fun hic => hi (by rwa [hic])
  exact ⟨⟨algebraicIndependent_update_div hS.1.1 hP hPmem,
    adjoin_update_div_eq_top (hS.1.1.ne_zero _) hP hS.1.2 hPmem⟩, hB⟩

section TropicalEval

variable {ι : Type*} [Fintype ι] {x : ι → F}

/-- `ε(1) = 1`. -/
@[simp]
theorem tropicalEval_one (x : ι → F) : tropicalEval x 1 = 1 := by
  simp [tropicalEval]

/-- `ε(y⁻¹) = ε(y)⁻¹`. -/
theorem tropicalEval_inv (x : ι → F) (y : TropicalSemifield ι) :
    tropicalEval x y⁻¹ = (tropicalEval x y)⁻¹ := by
  simp [tropicalEval, zpow_neg, Finset.prod_inv_distrib]

/-- `ε(y y') = ε(y) ε(y')` when every `xᵢ` is nonzero. -/
theorem tropicalEval_mul (hx : ∀ i, x i ≠ 0) (y y' : TropicalSemifield ι) :
    tropicalEval x (y * y') = tropicalEval x y * tropicalEval x y' := by
  simp [tropicalEval, zpow_add₀ (hx _), Finset.prod_mul_distrib]

/-- `ε(y / y') = ε(y) / ε(y')` when every `xᵢ` is nonzero. -/
theorem tropicalEval_div (hx : ∀ i, x i ≠ 0) (y y' : TropicalSemifield ι) :
    tropicalEval x (y / y') = tropicalEval x y / tropicalEval x y' := by
  rw [div_eq_mul_inv, tropicalEval_mul hx, tropicalEval_inv, div_eq_mul_inv]

/-- `ε(y)` is nonzero when every `xᵢ` is nonzero. -/
theorem tropicalEval_ne_zero (hx : ∀ i, x i ≠ 0) (y : TropicalSemifield ι) :
    tropicalEval x y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hx i)

end TropicalEval

/-- **Mutation of a triple of type `A₂` in direction `1`.** For the exchange matrix with rows
`(0, 1)` and `(-1, 0)`, mutation in direction `1` sends `((x₁, x₂), (y₁, y₂))` to
`(((ε(y₁/(y₁ ⊕ 1)) + ε(1/(y₁ ⊕ 1)) x₂)/x₁, x₂), (y₁⁻¹, y₂ (y₁⁻¹ ⊕ 1)⁻¹))` and negates the
matrix. -/
theorem SeedTriple.a2_mutation_zero (frozen : FrozenIndex m 2 → F) (x₁ x₂ : F)
    (y₁ y₂ : TropicalSemifield (FrozenIndex m 2)) :
    (SeedTriple.mk ![x₁, x₂] ![y₁, y₂] !![0, 1; -1, 0]).mutation frozen 0 =
      ⟨![(tropicalEval frozen (y₁ / (y₁ + 1)) + tropicalEval frozen (1 / (y₁ + 1)) * x₂) / x₁,
          x₂], ![y₁⁻¹, y₂ * (y₁⁻¹ + 1)⁻¹], !![0, -1; 1, 0]⟩ := by
  simp only [SeedTriple.mutation, SeedTriple.mk.injEq]
  refine ⟨funext fun j => ?_, funext fun j => ?_, ?_⟩
  · fin_cases j <;> simp [exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod]
  · fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixMutation]

/-- **Mutation of a triple of type `A₂` in direction `2`.** For the exchange matrix with rows
`(0, -1)` and `(1, 0)`, mutation in direction `2` sends `((x₁, x₂), (y₁, y₂))` to
`((x₁, (ε(y₂/(y₂ ⊕ 1)) + ε(1/(y₂ ⊕ 1)) x₁)/x₂), (y₁ (y₂⁻¹ ⊕ 1)⁻¹, y₂⁻¹))` and negates the
matrix. -/
theorem SeedTriple.a2_mutation_one (frozen : FrozenIndex m 2 → F) (x₁ x₂ : F)
    (y₁ y₂ : TropicalSemifield (FrozenIndex m 2)) :
    (SeedTriple.mk ![x₁, x₂] ![y₁, y₂] !![0, -1; 1, 0]).mutation frozen 1 =
      ⟨![x₁, (tropicalEval frozen (y₂ / (y₂ + 1)) + tropicalEval frozen (1 / (y₂ + 1)) * x₁) /
          x₂], ![y₁ * (y₂⁻¹ + 1)⁻¹, y₂⁻¹], !![0, 1; -1, 0]⟩ := by
  simp only [SeedTriple.mutation, SeedTriple.mk.injEq]
  refine ⟨funext fun j => ?_, funext fun j => ?_, ?_⟩
  · fin_cases j <;> simp [exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod]
  · fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixMutation]

section A2Steps

variable {f : FrozenIndex m 2 → F} (hf : ∀ i, f i ≠ 0) {x₁ x₂ : F} (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
  (y₁ y₂ : TropicalSemifield (FrozenIndex m 2))

include hf

/-- The triple `Σ(1)` of the `A₂` mutation sequence. -/
theorem SeedTriple.a2_triple_one :
    (SeedTriple.mk ![x₁, x₂] ![y₁, y₂] !![0, 1; -1, 0]).mutation f 0 =
      ⟨![(tropicalEval f y₁ + x₂) / (tropicalEval f (y₁ + 1) * x₁), x₂],
        ![y₁⁻¹, y₁ * y₂ / (y₁ + 1)], !![0, -1; 1, 0]⟩ := by
  have _hp₁ := tropicalEval_ne_zero hf (y₁ + 1)
  rw [SeedTriple.a2_mutation_zero]
  have c : y₂ * (y₁⁻¹ + 1)⁻¹ = y₁ * y₂ / (y₁ + 1) := by ext i; simp; omega
  have hx : (tropicalEval f (y₁ / (y₁ + 1)) + tropicalEval f (1 / (y₁ + 1)) * x₂) / x₁ =
      (tropicalEval f y₁ + x₂) / (tropicalEval f (y₁ + 1) * x₁) := by
    simp only [tropicalEval_div hf, tropicalEval_one]
    field_simp
  rw [c, hx]

include hx₁ hx₂ in
/-- The triple `Σ(2)` of the `A₂` mutation sequence. -/
theorem SeedTriple.a2_triple_two :
    (SeedTriple.mk ![(tropicalEval f y₁ + x₂) / (tropicalEval f (y₁ + 1) * x₁), x₂]
        ![y₁⁻¹, y₁ * y₂ / (y₁ + 1)] !![0, -1; 1, 0]).mutation f 1 =
      ⟨![(tropicalEval f y₁ + x₂) / (tropicalEval f (y₁ + 1) * x₁),
          (tropicalEval f y₁ * tropicalEval f y₂ * x₁ + tropicalEval f y₁ + x₂) /
            (tropicalEval f (y₁ * y₂ + y₁ + 1) * x₁ * x₂)],
        ![y₂ / (y₁ * y₂ + y₁ + 1), (y₁ + 1) / (y₁ * y₂)], !![0, 1; -1, 0]⟩ := by
  have _he₁ := tropicalEval_ne_zero hf y₁
  have _he₂ := tropicalEval_ne_zero hf y₂
  have _hp₁ := tropicalEval_ne_zero hf (y₁ + 1)
  have _hes := tropicalEval_ne_zero hf (y₁ * y₂ + y₁ + 1)
  rw [SeedTriple.a2_mutation_one]
  have c₁ : y₁⁻¹ * ((y₁ * y₂ / (y₁ + 1))⁻¹ + 1)⁻¹ = y₂ / (y₁ * y₂ + y₁ + 1) := by
    ext i; simp; omega
  have c₂ : (y₁ * y₂ / (y₁ + 1))⁻¹ = (y₁ + 1) / (y₁ * y₂) := by ext i; simp
  have c₃ : y₁ * y₂ / (y₁ + 1) / (y₁ * y₂ / (y₁ + 1) + 1) = y₁ * y₂ / (y₁ * y₂ + y₁ + 1) := by
    ext i; simp; omega
  have c₄ : 1 / (y₁ * y₂ / (y₁ + 1) + 1) = (y₁ + 1) / (y₁ * y₂ + y₁ + 1) := by
    ext i; simp; omega
  rw [c₃, c₄, c₁, c₂]
  simp only [tropicalEval_div hf, tropicalEval_mul hf, SeedTriple.mk.injEq, and_true]
  refine funext fun j => ?_
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

include hx₁ hx₂ in
/-- The triple `Σ(3)` of the `A₂` mutation sequence. -/
theorem SeedTriple.a2_triple_three
    (hX : (tropicalEval f y₁ + x₂) / (tropicalEval f (y₁ + 1) * x₁) ≠ 0) :
    (SeedTriple.mk ![(tropicalEval f y₁ + x₂) / (tropicalEval f (y₁ + 1) * x₁),
          (tropicalEval f y₁ * tropicalEval f y₂ * x₁ + tropicalEval f y₁ + x₂) /
            (tropicalEval f (y₁ * y₂ + y₁ + 1) * x₁ * x₂)]
        ![y₂ / (y₁ * y₂ + y₁ + 1), (y₁ + 1) / (y₁ * y₂)] !![0, 1; -1, 0]).mutation f 0 =
      ⟨![(tropicalEval f y₂ * x₁ + 1) / (tropicalEval f (y₂ + 1) * x₂),
          (tropicalEval f y₁ * tropicalEval f y₂ * x₁ + tropicalEval f y₁ + x₂) /
            (tropicalEval f (y₁ * y₂ + y₁ + 1) * x₁ * x₂)],
        ![(y₁ * y₂ + y₁ + 1) / y₂, 1 / (y₁ * (y₂ + 1))], !![0, -1; 1, 0]⟩ := by
  have _he₁ := tropicalEval_ne_zero hf y₁
  have _he₂ := tropicalEval_ne_zero hf y₂
  have _hp₁ := tropicalEval_ne_zero hf (y₁ + 1)
  have _hp₂ := tropicalEval_ne_zero hf (y₂ + 1)
  have _hes := tropicalEval_ne_zero hf (y₁ * y₂ + y₁ + 1)
  rw [SeedTriple.a2_mutation_zero]
  have c₁ : (y₂ / (y₁ * y₂ + y₁ + 1))⁻¹ = (y₁ * y₂ + y₁ + 1) / y₂ := by ext i; simp
  have c₂ : (y₁ + 1) / (y₁ * y₂) * ((y₂ / (y₁ * y₂ + y₁ + 1))⁻¹ + 1)⁻¹ =
      1 / (y₁ * (y₂ + 1)) := by ext i; simp; omega
  have c₃ : y₂ / (y₁ * y₂ + y₁ + 1) / (y₂ / (y₁ * y₂ + y₁ + 1) + 1) =
      y₂ / ((y₁ + 1) * (y₂ + 1)) := by ext i; simp; omega
  have c₄ : 1 / (y₂ / (y₁ * y₂ + y₁ + 1) + 1) =
      (y₁ * y₂ + y₁ + 1) / ((y₁ + 1) * (y₂ + 1)) := by ext i; simp; omega
  rw [c₃, c₄, c₂, c₁]
  simp only [tropicalEval_div hf, tropicalEval_mul hf, SeedTriple.mk.injEq, and_true]
  refine funext fun j => ?_
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [div_eq_iff hX]
  field_simp
  ring

include hx₁ hx₂ in
/-- The triple `Σ(4)` of the `A₂` mutation sequence. -/
theorem SeedTriple.a2_triple_four
    (hX : (tropicalEval f y₁ * tropicalEval f y₂ * x₁ + tropicalEval f y₁ + x₂) /
      (tropicalEval f (y₁ * y₂ + y₁ + 1) * x₁ * x₂) ≠ 0) :
    (SeedTriple.mk ![(tropicalEval f y₂ * x₁ + 1) / (tropicalEval f (y₂ + 1) * x₂),
          (tropicalEval f y₁ * tropicalEval f y₂ * x₁ + tropicalEval f y₁ + x₂) /
            (tropicalEval f (y₁ * y₂ + y₁ + 1) * x₁ * x₂)]
        ![(y₁ * y₂ + y₁ + 1) / y₂, 1 / (y₁ * (y₂ + 1))] !![0, -1; 1, 0]).mutation f 1 =
      ⟨![(tropicalEval f y₂ * x₁ + 1) / (tropicalEval f (y₂ + 1) * x₂), x₁],
        ![y₂⁻¹, y₁ * (y₂ + 1)], !![0, 1; -1, 0]⟩ := by
  have _he₁ := tropicalEval_ne_zero hf y₁
  have _he₂ := tropicalEval_ne_zero hf y₂
  have _hp₂ := tropicalEval_ne_zero hf (y₂ + 1)
  have _hes := tropicalEval_ne_zero hf (y₁ * y₂ + y₁ + 1)
  rw [SeedTriple.a2_mutation_one]
  have c₁ : (y₁ * y₂ + y₁ + 1) / y₂ * ((1 / (y₁ * (y₂ + 1)))⁻¹ + 1)⁻¹ = y₂⁻¹ := by
    ext i; simp; omega
  have c₂ : (1 / (y₁ * (y₂ + 1)))⁻¹ = y₁ * (y₂ + 1) := by ext i; simp
  have c₃ : 1 / (y₁ * (y₂ + 1)) / (1 / (y₁ * (y₂ + 1)) + 1) = 1 / (y₁ * y₂ + y₁ + 1) := by
    ext i; simp; omega
  have c₄ : 1 / (1 / (y₁ * (y₂ + 1)) + 1) = y₁ * (y₂ + 1) / (y₁ * y₂ + y₁ + 1) := by
    ext i; simp; omega
  rw [c₃, c₄, c₁, c₂]
  simp only [tropicalEval_div hf, tropicalEval_mul hf, tropicalEval_one, SeedTriple.mk.injEq,
    and_true]
  refine funext fun j => ?_
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [div_eq_iff hX]
  field_simp
  ring

include hx₂ in
/-- The triple `Σ(5)` of the `A₂` mutation sequence: the initial triple with the labels
interchanged. -/
theorem SeedTriple.a2_triple_five
    (hX : (tropicalEval f y₂ * x₁ + 1) / (tropicalEval f (y₂ + 1) * x₂) ≠ 0) :
    (SeedTriple.mk ![(tropicalEval f y₂ * x₁ + 1) / (tropicalEval f (y₂ + 1) * x₂), x₁]
        ![y₂⁻¹, y₁ * (y₂ + 1)] !![0, 1; -1, 0]).mutation f 0 =
      ⟨![x₂, x₁], ![y₂, y₁], !![0, -1; 1, 0]⟩ := by
  have _he₂ := tropicalEval_ne_zero hf y₂
  have _hp₂ := tropicalEval_ne_zero hf (y₂ + 1)
  rw [SeedTriple.a2_mutation_zero]
  have c₂ : y₁ * (y₂ + 1) * (y₂⁻¹⁻¹ + 1)⁻¹ = y₁ := by ext i; simp
  have c₃ : y₂⁻¹ / (y₂⁻¹ + 1) = 1 / (y₂ + 1) := by ext i; simp; omega
  have c₄ : 1 / (y₂⁻¹ + 1) = y₂ / (y₂ + 1) := by ext i; simp; omega
  rw [c₃, c₄, c₂, inv_inv]
  simp only [tropicalEval_div hf, tropicalEval_one, SeedTriple.mk.injEq, and_true]
  refine funext fun j => ?_
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [div_eq_iff hX]
  field_simp
  ring

end A2Steps

/-- Along a sequence of seed mutations, the frozen variables do not change. -/
theorem SeedData.frozenTuple_eq_of_seedMutation {n N : ℕ} (hmn : n ≤ m)
    {seeds : ℕ → SeedData F m n} (d : ℕ → Fin n)
    (hstep : ∀ t < N, seeds (t + 1) = ClusterAlgebras.seedMutation hmn (seeds t) (d t)) :
    ∀ t ≤ N, (seeds t).frozenTuple = (seeds 0).frozenTuple := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih => rw [hstep t (by omega), SeedData.frozenTuple_seedMutation, ih (by omega)]

/-- In rank `2`, every seed along a sequence of mutations of a labeled seed is a labeled seed. -/
theorem IsLabeledSeed.of_seedMutation_fin_two [CharZero K] {N : ℕ} (hmn : 2 ≤ m)
    {seeds : ℕ → SeedData F m 2} (d : ℕ → Fin 2) (h0 : IsLabeledSeed K hmn (seeds 0))
    (hstep : ∀ t < N, seeds (t + 1) = ClusterAlgebras.seedMutation hmn (seeds t) (d t)) :
    ∀ t ≤ N, IsLabeledSeed K hmn (seeds t) := by
  intro t ht
  induction t with
  | zero => exact h0
  | succ t ih =>
    rw [hstep t (by omega)]
    exact (ih (by omega)).seedMutation_of_extSkewSymmetrizable hmn _
      ((ih (by omega)).2.matrixMutation_of_fin_two hmn _)

private theorem swap_castLE_frozenIndex (hmn : 2 ≤ m) (i : FrozenIndex m 2) :
    Equiv.swap (Fin.castLE hmn 0) (Fin.castLE hmn 1) i.1 = i.1 :=
  Equiv.swap_apply_of_ne_of_ne (FrozenIndex.val_ne_castLE hmn i 0)
    (FrozenIndex.val_ne_castLE hmn i 1)

omit [Field F] in
/-- The triple of the seed `(x̃^τ, B̃^τ)` obtained from a seed of type `A₂` by interchanging the
labels `1` and `2`. -/
theorem SeedData.toSeedTriple_swap_of_a2 (hmn : 2 ≤ m) {S : SeedData F m 2}
    (hB : principalPart hmn S.extExchangeMatrix = !![0, 1; -1, 0]) :
    (⟨S.extCluster ∘ Equiv.swap (Fin.castLE hmn 0) (Fin.castLE hmn 1),
      S.extExchangeMatrix.submatrix (Equiv.swap (Fin.castLE hmn 0) (Fin.castLE hmn 1))
        (Equiv.swap 0 1)⟩ : SeedData F m 2).toSeedTriple hmn =
      ⟨![S.extCluster (Fin.castLE hmn 1), S.extCluster (Fin.castLE hmn 0)],
        ![coefficientTuple S.extExchangeMatrix 1, coefficientTuple S.extExchangeMatrix 0],
        !![0, -1; 1, 0]⟩ := by
  have hb : ∀ i j, S.extExchangeMatrix (Fin.castLE hmn i) j = !![0, 1; -1, 0] i j :=
    fun i j => congrFun (congrFun hB i) j
  simp only [SeedData.toSeedTriple, SeedTriple.mk.injEq]
  refine ⟨funext fun j => ?_, funext fun j => ?_, ?_⟩
  · fin_cases j <;> simp [cluster]
  · ext i
    fin_cases j <;> simp [swap_castLE_frozenIndex]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [principalPart, hb]

/-- **Seeds of type `A₂` with arbitrary coefficients are `5`-periodic up to relabelling.** Let
`(x̃, B̃)` be a labeled seed of rank `2` whose principal part has rows `(0, 1)` and `(-1, 0)`, and
let `Σ(0) = (x̃, B̃)` and `Σ(t + 1) = μ₁(Σ(t))` for even `t`, `Σ(t + 1) = μ₂(Σ(t))` for odd `t`,
for `t < 5`. Then `Σ(5) = (x̃^τ, B̃^τ)`, where `τ` is the transposition of `1` and `2`,
`x̃^τ = (x₂, x₁, x₃, …, xₘ)` and `(B̃^τ)ᵢⱼ = b_{τ(i) τ(j)}`. -/
@[cluster_algebras "lem_a2_period_five"]
theorem a2_seedMutation_period_five [CharZero K] (hmn : 2 ≤ m) {S : SeedData F m 2}
    (hS : IsLabeledSeed K hmn S) (hB : principalPart hmn S.extExchangeMatrix = !![0, 1; -1, 0])
    (seeds : ℕ → SeedData F m 2) (h0 : seeds 0 = S)
    (hstep : ∀ t < 5, seeds (t + 1) = seedMutation hmn (seeds t) (if Even t then 0 else 1)) :
    seeds 5 = ⟨S.extCluster ∘ Equiv.swap (Fin.castLE hmn 0) (Fin.castLE hmn 1),
      S.extExchangeMatrix.submatrix (Equiv.swap (Fin.castLE hmn 0) (Fin.castLE hmn 1))
        (Equiv.swap 0 1)⟩ := by
  set f := S.frozenTuple with hfdef
  have hfroz : ∀ t ≤ 5, (seeds t).frozenTuple = f := fun t ht => by
    rw [SeedData.frozenTuple_eq_of_seedMutation hmn _ hstep t ht, h0]
  have hT : ∀ t < 5, (seeds (t + 1)).toSeedTriple hmn =
      ((seeds t).toSeedTriple hmn).mutation f (if Even t then 0 else 1) := fun t ht => by
    rw [hstep t ht, SeedData.toSeedTriple_seedMutation, hfroz t ht.le]
  have hcl : ∀ t ≤ 5, ∀ j, ((seeds t).toSeedTriple hmn).cluster j ≠ 0 := fun t ht _ =>
    (IsLabeledSeed.of_seedMutation_fin_two hmn _ (by rwa [h0]) hstep t ht).1.1.ne_zero _
  have hf : ∀ i, f i ≠ 0 := fun i => hS.1.1.ne_zero i.1
  set x₁ := S.extCluster (Fin.castLE hmn 0)
  set x₂ := S.extCluster (Fin.castLE hmn 1)
  set y₁ := coefficientTuple S.extExchangeMatrix 0
  set y₂ := coefficientTuple S.extExchangeMatrix 1
  have hx₁0 : x₁ ≠ 0 := hS.1.1.ne_zero _
  have hx₂0 : x₂ ≠ 0 := hS.1.1.ne_zero _
  have hT0 : (seeds 0).toSeedTriple hmn = ⟨![x₁, x₂], ![y₁, y₂], !![0, 1; -1, 0]⟩ := by
    simp only [h0, SeedData.toSeedTriple, SeedTriple.mk.injEq]
    refine ⟨funext fun j => ?_, funext fun j => ?_, hB⟩ <;> fin_cases j <;> rfl
  have hX₁ := hcl 1 (by norm_num) 0
  have hT1 := hT 0 (by norm_num)
  rw [hT0, if_pos (by decide), SeedTriple.a2_triple_one hf] at hT1
  rw [hT1] at hX₁
  have hX₂ := hcl 2 (by norm_num) 1
  have hT2 := hT 1 (by norm_num)
  rw [hT1, if_neg (by decide), SeedTriple.a2_triple_two hf hx₁0 hx₂0] at hT2
  rw [hT2] at hX₂
  have hX₃ := hcl 3 (by norm_num) 0
  have hT3 := hT 2 (by norm_num)
  rw [hT2, if_pos (by decide), SeedTriple.a2_triple_three hf hx₁0 hx₂0 _ _ hX₁] at hT3
  rw [hT3] at hX₃
  have hT4 := hT 3 (by norm_num)
  rw [hT3, if_neg (by decide), SeedTriple.a2_triple_four hf hx₁0 hx₂0 _ _ hX₂] at hT4
  have hT5 := hT 4 (by norm_num)
  rw [hT4, if_pos (by decide), SeedTriple.a2_triple_five hf hx₂0 _ _ hX₃] at hT5
  refine SeedData.eq_of_toSeedTriple_eq hmn
    (hT5.trans (SeedData.toSeedTriple_swap_of_a2 hmn hB).symm) ((hfroz 5 le_rfl).trans ?_)
  funext i
  simp [SeedData.frozenTuple, hfdef, swap_castLE_frozenIndex]

end ClusterAlgebras

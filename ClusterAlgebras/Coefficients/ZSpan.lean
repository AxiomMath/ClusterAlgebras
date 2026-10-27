/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Seed

/-!
# The `ℤ`-span condition

An integer matrix `C̃` satisfies the *`ℤ`-span condition* with respect to an integer matrix `B̃`
with the same columns if every row of `C̃` is an integer linear combination of the rows of `B̃`.
Under this condition, FWZ's Corollary 4.3.5 transfers coincidences of seeds from a seed pattern
with initial extended exchange matrix `B̃` to one with initial extended exchange matrix `C̃` and
the same exchange matrices. This file defines the condition, characterises it as a factorisation
`C̃ = Ψ B̃` through an integer matrix, and proves the two sufficient conditions of FWZ's
Remark 4.3.6: it holds for every `C̃` when the rows of `B̃` span `ℤⁿ`, and it holds for the
principal part of `B̃`.

## Main definitions

* `ClusterAlgebras.ZSpanCondition C B`: every row of `C` lies in the `ℤ`-span of the rows of
  `B`.

## Main results

* `ClusterAlgebras.zSpanCondition_iff_exists_mul`: `C` satisfies the `ℤ`-span condition with
  respect to `B` if and only if `C = Ψ * B` for some integer matrix `Ψ`.
* `ClusterAlgebras.zSpanCondition_of_span_eq_top`: if the rows of `B` span `ℤⁿ`, every `C`
  satisfies the `ℤ`-span condition with respect to `B`.
* `ClusterAlgebras.zSpanCondition_principalPart`: the principal part of `B` satisfies the
  `ℤ`-span condition with respect to `B`.

## Implementation notes

* FWZ take an `m̄ × n` matrix `C̃` and an `m × n` matrix `B̃`. The definition and the results
  here allow arbitrary index types for the rows of either matrix and for the common columns;
  only the factorisation `zSpanCondition_iff_exists_mul` needs the rows of `B` to be finite, so
  that `Ψ * B` is defined. The principal-part lemma is stated for `Fin m × Fin n`, the shape of
  `ClusterAlgebras.principalPart`.
* A row of an integer matrix `B : Matrix ι κ ℤ` is `B i : κ → ℤ`, so the rows of `B` are
  `Set.range B` and `ℤⁿ` is the module `κ → ℤ`; "the rows of `B̃` span `ℤⁿ`" is
  `Submodule.span ℤ (Set.range B) = ⊤`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 4–5*, Section 4.3.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {ι' ι κ : Type*}

/-- A matrix `C` satisfies the **`ℤ`-span condition** with respect to `B` (with the same
columns) if every row of `C` is an integer linear combination of the rows of `B`. -/
@[cluster_algebras "def_z_span_condition"]
def ZSpanCondition (C : Matrix ι' κ ℤ) (B : Matrix ι κ ℤ) : Prop :=
  ∀ i, C i ∈ Submodule.span ℤ (Set.range B)

/-- The `ℤ`-span condition is a factorisation: `C` satisfies it with respect to `B` if and only
if `C = Ψ * B` for some integer matrix `Ψ`, whose `i`th row holds the coefficients expressing
the `i`th row of `C` in the rows of `B`. -/
theorem zSpanCondition_iff_exists_mul [Fintype ι] {C : Matrix ι' κ ℤ} {B : Matrix ι κ ℤ} :
    ZSpanCondition C B ↔ ∃ Ψ : Matrix ι' ι ℤ, C = Ψ * B := by
  simp only [ZSpanCondition, Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun h => ?_, ?_⟩
  · choose Ψ hΨ using h
    exact ⟨Matrix.of Ψ, funext fun i => by
      simp [Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum, ← hΨ i]⟩
  · rintro ⟨Ψ, rfl⟩ i
    exact ⟨Ψ i, by rw [Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum]⟩

/-- **Full `ℤ`-rank implies the `ℤ`-span condition**: if the rows of `B` span `ℤⁿ` as an abelian
group, every matrix `C` with the same columns satisfies the `ℤ`-span condition with respect to
`B`. -/
@[cluster_algebras "lem_full_rank_span_condition"]
theorem zSpanCondition_of_span_eq_top {B : Matrix ι κ ℤ}
    (hB : Submodule.span ℤ (Set.range B) = ⊤) (C : Matrix ι' κ ℤ) : ZSpanCondition C B :=
  fun _ => hB ▸ Submodule.mem_top

/-- **Trivial coefficients satisfy the `ℤ`-span condition**: the principal part of `B`
satisfies the `ℤ`-span condition with respect to `B`, its rows being the first `n` rows
of `B`. -/
@[cluster_algebras "lem_trivial_coefficients_span_condition"]
theorem zSpanCondition_principalPart {m n : ℕ} (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ) :
    ZSpanCondition (principalPart hmn B) B :=
  fun i => Submodule.subset_span ⟨Fin.castLE hmn i, rfl⟩

end ClusterAlgebras

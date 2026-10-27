/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.Defs
public import ClusterAlgebras.Cartan.Counterpart

/-!
# Finite type of a Cartan counterpart depends only on the products `aᵢⱼ aⱼᵢ`

Positive definiteness of `DA` for a symmetrizable generalized Cartan matrix `A` depends only on
the products `aᵢⱼ aⱼᵢ`. Consequently the Cartan counterpart of an orientation of a Dynkin
diagram is of finite type.

## Main results

* `ClusterAlgebras.IsGeneralizedCartan.isCartanFiniteType_of_mul_eq`: if two symmetrizable
  generalized Cartan matrices have the same products `aᵢⱼ aⱼᵢ` and one is of finite type, so is
  the other.
* `ClusterAlgebras.cartanCounterpart_submatrix_perm`: the Cartan counterpart commutes with
  simultaneous permutation of rows and columns.
* `ClusterAlgebras.IsCartanFiniteType.submatrix_perm`: a relabelling of a Cartan matrix of finite
  type is of finite type.
* `ClusterAlgebras.IsOrientationOfWeighted.isCartanFiniteType_cartanCounterpart`: the Cartan
  counterpart of an orientation of a Dynkin diagram is of finite type.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

/-- The quadratic form `vᵀ (DA) v` written as a double sum. -/
private theorem quadForm_eq_sum (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ) (v : Fin n → ℝ) :
    v ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ v) =
      ∑ i, ∑ j, v i * ((d i : ℝ) * (A i j : ℝ)) * v j := by
  simp only [dotProduct, mulVec, diagonal_mul, map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The real symmetric matrix `M(A)` with diagonal entries `2` and off-diagonal entries
`-√(aᵢⱼ aⱼᵢ)`; it depends only on the products `aᵢⱼ aⱼᵢ`. -/
private noncomputable def productMatrix (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℝ :=
  if i = j then 2 else -Real.sqrt ((A i j * A j i : ℤ) : ℝ)

/-- `DA = E M(A) E` entrywise, with `E = diag(√dᵢ)`. -/
private theorem symmetrizer_mul_eq {A : Matrix (Fin n) (Fin n) ℤ} (hA : IsGeneralizedCartan A)
    {d : Fin n → ℤ} (hd : IsSymmetrizer A d) (i j : Fin n) :
    (d i : ℝ) * (A i j : ℝ) =
      Real.sqrt (d i) * Real.sqrt (d j) * productMatrix A i j := by
  have hdi : (0 : ℝ) ≤ d i := by exact_mod_cast (hd.1 i).le
  have hdj : (0 : ℝ) ≤ d j := by exact_mod_cast (hd.1 j).le
  by_cases hij : i = j
  · subst hij
    rw [productMatrix, if_pos rfl, Real.mul_self_sqrt hdi, hA.1 i]
    norm_num
  · rw [productMatrix, if_neg hij]
    have hle : (d i : ℝ) * (A i j : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdi (by exact_mod_cast hA.2.1 i j hij)
    have hsq : ((d i : ℝ) * (A i j : ℝ)) ^ 2 = (d i : ℝ) * d j * ((A i j * A j i : ℤ) : ℝ) := by
      have h' : (d i : ℝ) * (A i j : ℝ) = (d j : ℝ) * (A j i : ℝ) := by exact_mod_cast hd.2 i j
      push_cast
      calc ((d i : ℝ) * (A i j : ℝ)) ^ 2
          = ((d i : ℝ) * (A i j : ℝ)) * ((d j : ℝ) * (A j i : ℝ)) := by rw [sq, ← h']
        _ = _ := by ring
    have := Real.sqrt_sq_eq_abs ((d i : ℝ) * (A i j : ℝ))
    rw [hsq, abs_of_nonpos hle, Real.sqrt_mul (mul_nonneg hdi hdj), Real.sqrt_mul hdi] at this
    linarith

/-- `vᵀ (DA) v = uᵀ M(A) u` with `uᵢ = √dᵢ vᵢ`. -/
private theorem quadForm_eq_productMatrix {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : IsGeneralizedCartan A) {d : Fin n → ℤ} (hd : IsSymmetrizer A d) (v : Fin n → ℝ) :
    v ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ v) =
      ∑ i, ∑ j, (Real.sqrt (d i) * v i) * productMatrix A i j * (Real.sqrt (d j) * v j) := by
  rw [quadForm_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symmetrizer_mul_eq hA hd i j]
  ring

/-- **Finite type depends only on the products `aᵢⱼ aⱼᵢ`.** If `A` and `A'` are symmetrizable
generalized Cartan matrices with `aᵢⱼ aⱼᵢ = a'ᵢⱼ a'ⱼᵢ` for all `i, j` and `A'` is of finite
type, then `A` is of finite type, and indeed `DA` is positive definite for every symmetrizer
`D` of `A`. -/
@[cluster_algebras "lem_cartan_products"]
theorem IsGeneralizedCartan.isCartanFiniteType_of_mul_eq {A A' : Matrix (Fin n) (Fin n) ℤ}
    (hA : IsGeneralizedCartan A) (hA' : IsGeneralizedCartan A')
    (hmul : ∀ i j, A i j * A j i = A' i j * A' j i) (hfin : IsCartanFiniteType A') :
    IsCartanFiniteType A ∧ ∀ d, IsSymmetrizer A d → ∀ v : Fin n → ℝ, v ≠ 0 →
      0 < v ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ v) := by
  obtain ⟨d', hd', hpos'⟩ := hfin.2
  have hM : productMatrix A = productMatrix A' := by
    funext i j
    simp only [productMatrix, hmul]
  have key : ∀ d, IsSymmetrizer A d → ∀ v : Fin n → ℝ, v ≠ 0 →
      0 < v ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ v) := by
    intro d hd v hv
    have hd'pos : ∀ i, 0 < Real.sqrt (d' i) := fun i =>
      Real.sqrt_pos.2 (by exact_mod_cast hd'.1 i)
    have hdpos : ∀ i, 0 < Real.sqrt (d i) := fun i =>
      Real.sqrt_pos.2 (by exact_mod_cast hd.1 i)
    set w : Fin n → ℝ := fun i => Real.sqrt (d i) * v i / Real.sqrt (d' i) with hw
    have hw0 : w ≠ 0 := by
      intro h
      apply hv
      funext i
      have := congrFun h i
      simp only [hw, Pi.zero_apply, div_eq_zero_iff, mul_eq_zero, (hdpos i).ne',
        (hd'pos i).ne', false_or, or_false] at this
      simpa using this
    have hcancel : ∀ i, Real.sqrt (d' i) * w i = Real.sqrt (d i) * v i := fun i => by
      simp only [hw]
      field_simp [(hd'pos i).ne']
    have := hpos' w hw0
    rw [quadForm_eq_productMatrix hA' hd', ← hM] at this
    simp only [hcancel] at this
    rwa [quadForm_eq_productMatrix hA hd]
  obtain ⟨d, hd⟩ := hA.2.2
  exact ⟨⟨hA, d, hd, key d hd⟩, key⟩

/-- **Cartan counterparts and relabelling**: `A(B^π) = A(B)^π` for a permutation `π`. -/
@[cluster_algebras "lem_cartan_counterpart_permutation"]
theorem cartanCounterpart_submatrix_perm (B : Matrix (Fin n) (Fin n) ℤ) (π : Equiv.Perm (Fin n)) :
    cartanCounterpart (B.submatrix π π) = (cartanCounterpart B).submatrix π π := by
  ext i j
  simp [cartanCounterpart, π.injective.eq_iff]

/-- **A relabelling of a Cartan matrix of finite type is of finite type.** -/
@[cluster_algebras "lem_cartan_counterpart_permutation"]
theorem IsCartanFiniteType.submatrix_perm {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : IsCartanFiniteType A) (π : Equiv.Perm (Fin n)) :
    IsCartanFiniteType (A.submatrix π π) := by
  obtain ⟨⟨hdiag, hoff, -⟩, d, hd, hpos⟩ := hA
  have hd' : IsSymmetrizer (A.submatrix π π) (d ∘ π) :=
    ⟨fun i => hd.1 (π i), fun i j => hd.2 (π i) (π j)⟩
  refine ⟨⟨fun i => hdiag (π i), fun i j hij => hoff _ _ (π.injective.ne hij), d ∘ π, hd'⟩,
    d ∘ π, hd', fun v hv => ?_⟩
  have hu : v ∘ π.symm ≠ 0 := by
    intro h
    apply hv
    funext i
    simpa using congrFun h (π i)
  have := hpos _ hu
  rw [quadForm_eq_sum] at this ⊢
  set f : Fin n → Fin n → ℝ := fun a b =>
    (v ∘ π.symm) a * ((d a : ℝ) * (A a b : ℝ)) * (v ∘ π.symm) b with hf
  have hperm : ∑ i, ∑ j, f (π i) (π j) = ∑ a, ∑ b, f a b := by
    rw [← Equiv.sum_comp π (fun a => ∑ b, f a b)]
    exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp π (f (π i))
  rw [← hperm] at this
  simpa [hf] using this

/-- **The Cartan counterpart of an orientation of a Dynkin diagram is of finite type**: if `B`
is an orientation of `ω_X`, then `A(B)` is a Cartan matrix of finite type. -/
@[cluster_algebras "lem_dynkin_orientation_finite_type"]
theorem IsOrientationOfWeighted.isCartanFiniteType_cartanCounterpart {Xs : List DynkinSymbol}
    {B : Matrix (Fin (DynkinSymbol.listRank Xs)) (Fin (DynkinSymbol.listRank Xs)) ℤ}
    (hB : IsOrientationOfWeighted B (dynkinWeightedGraph Xs)) :
    IsCartanFiniteType (cartanCounterpart B) := by
  obtain ⟨⟨d, hd⟩, hw⟩ := hB
  obtain ⟨hA, -⟩ := hd.isGeneralizedCartan_cartanCounterpart
  have hfin := isCartanFiniteType_listCartan Xs
  refine (hA.isCartanFiniteType_of_mul_eq hfin.1 (fun i j => ?_) hfin).1
  by_cases hij : i = j
  · subst hij
    simp [cartanCounterpart, hfin.1.1 i]
  · have h := congrArg (Nat.cast : ℕ → ℤ) (hw i j)
    simp only [diagramWeight, dynkinWeightedGraph, if_neg hij, Int.natCast_natAbs] at h
    have hnn : 0 ≤ DynkinSymbol.listCartan Xs i j * DynkinSymbol.listCartan Xs j i :=
      mul_nonneg_of_nonpos_of_nonpos (hfin.1.2.1 i j hij) (hfin.1.2.1 j i (Ne.symm hij))
    rw [abs_of_nonneg hnn, abs_mul] at h
    simp [cartanCounterpart, hij, Ne.symm hij, h]

end ClusterAlgebras

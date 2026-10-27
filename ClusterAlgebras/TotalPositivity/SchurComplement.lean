/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.Minor
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The shuffle count, Schur complements, and minors through a Schur complement

For finite sets `A`, `R` in a linear order, the shuffle count `ν(A, R)` is the number of pairs
`(a, r) ∈ A × R` with `r < a`. For a matrix `x` over a field and sets `R` of rows and `C` of
columns with `|R| = |C|` and `Δ_{R,C}(x) ≠ 0`, the Schur complement `x/(R, C)` has entries
`x_{ab} - ∑_{s,t} x_{a c_t} (V⁻¹)_{t s} x_{r_s b}`, where `V` is the submatrix on `R × C`.

The main result expresses a minor on `A ∪ R`, `B ∪ C` through the Schur complement:
`Δ_{A ∪ R, B ∪ C}(x) = (-1)^{ν(A,R) + ν(B,C)} Δ_{R,C}(x) Δ_{A,B}(x/(R,C))`. The proof lists the
rows as `a₁, …, a_k, r₁, …, r_c` and the columns as `b₁, …, b_k, c₁, …, c_c`; this reorders the
increasing lists by permutations of signs `(-1)^{ν(A,R)}` and `(-1)^{ν(B,C)}`, and the reordered
matrix is a block matrix whose determinant is `det V · det (P - Q V⁻¹ U)` by Mathlib's
`Matrix.det_fromBlocks₂₂`, with `P - Q V⁻¹ U` the Schur complement restricted to `A × B`.

## Main definitions

* `ClusterAlgebras.shuffleCount`: the shuffle count `ν(A, R)`.
* `ClusterAlgebras.schurComplement`: the Schur complement `x/(R, C)`.

## Main results

* `ClusterAlgebras.minor_union_eq_schurComplement`: minors through a Schur complement.
* `ClusterAlgebras.sign_eq_neg_one_pow_card_inversions`: the sign of a permutation of `Fin n` is
  `(-1)` to the number of its inversions.
* `ClusterAlgebras.sign_eq_neg_one_pow_shuffleCount`: the permutation listing `A` before `R` has
  sign `(-1)^{ν(A, R)}`.

## Implementation notes

* Rows and columns are indexed by arbitrary linear orders rather than sets of positive integers,
  and increasing enumerations are `Finset.orderEmbOfFin`.
* The Schur complement is total: it is given by the same formula on all rows and columns, and is
  `x` itself when `|R| ≠ |C|`. Only its entries on `A × B`, off `R` and `C`, enter the main
  result.
* The main result is stated without nonemptiness hypotheses on `A`, `B`, `R`, `C`; the empty
  cases hold with the empty minor equal to `1`. Disjointness `A ∩ R = ∅`, `B ∩ C = ∅` replaces
  the conditions `A ⊆ 𝓘 ∖ R`, `B ⊆ 𝓙 ∖ C` of [FWZ].

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 1.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Matrix

variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]

/-- The **shuffle count** `ν(A, R)`: the number of pairs `(a, r) ∈ A × R` with `r < a`. -/
@[cluster_algebras "def_shuffle_count"]
def shuffleCount (A R : Finset ι) : ℕ := #{p ∈ A ×ˢ R | p.2 < p.1}

/-- The **Schur complement** `x/(R, C)` of the block `(R, C)` in a matrix `x` over a field: with
`r₁ < ⋯ < r_c` and `c₁ < ⋯ < c_c` the elements of `R` and `C` and `V = (x_{r_s c_t})_{s,t}`, its
`(a, b)` entry is `x_{ab} - ∑_{s,t} x_{a c_t} (V⁻¹)_{t s} x_{r_s b}`.

It is given by the same formula on all rows and columns, with `V⁻¹` Mathlib's inverse, and it is
`x` itself when `|R| ≠ |C|`. -/
@[cluster_algebras "def_schur_complement"]
noncomputable def schurComplement {K : Type*} [Field K] (x : Matrix ι κ K) (R : Finset ι)
    (C : Finset κ) : Matrix ι κ K :=
  if h : C.card = R.card then
    fun a b => x a b - ∑ s : Fin R.card, ∑ t : Fin R.card,
      x a (C.orderEmbOfFin h t) *
        (x.submatrix (R.orderEmbOfFin rfl) (C.orderEmbOfFin h))⁻¹ t s *
        x (R.orderEmbOfFin rfl s) b
  else x

/-! ### Signs of permutations and inversions -/

/-- On `Fin n` the sign of a permutation is Mathlib's `Equiv.Perm.signAux`, the product over the
pairs `j < i` of `-1` when `σ i ≤ σ j`. -/
theorem sign_eq_signAux {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign σ = Equiv.Perm.signAux σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp [Equiv.Perm.signAux_one]
  | swap_mul f x y hxy ih =>
    rw [Equiv.Perm.sign_mul, Equiv.Perm.signAux_mul, ih, Equiv.Perm.sign_swap hxy,
      Equiv.Perm.signAux_swap hxy]

/-- The sign of a permutation `σ` of `Fin n` is `(-1)` to the number of its **inversions**, the
pairs `i < j` with `σ j < σ i`. -/
theorem sign_eq_neg_one_pow_card_inversions {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign σ = (-1) ^ #{p : Fin n × Fin n | p.1 < p.2 ∧ σ p.2 < σ p.1} := by
  rw [sign_eq_signAux, Equiv.Perm.signAux, Finset.prod_ite, prod_const, prod_const_one, mul_one]
  congr 1
  refine Finset.card_nbij (fun p => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, Equiv.Perm.mem_finPairsLT, Set.mem_setOf_eq] at hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨hp.1, hp.2.lt_of_ne fun h => hp.1.ne' (σ.injective h)⟩
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Sigma.ext h.2 (heq_of_eq h.1)
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
    refine ⟨⟨p.2, p.1⟩, ?_, rfl⟩
    simp only [coe_filter, Equiv.Perm.mem_finPairsLT, Set.mem_setOf_eq]
    exact ⟨hp.1, hp.2.le⟩

/-! ### Listing `A` before `R` -/

/-- Listing the elements of `A` increasingly and then those of a disjoint `R` increasingly is
injective. -/
theorem injective_append_orderEmbOfFin {k c : ℕ} {A R : Finset ι} (hAR : Disjoint A R)
    (hA : #A = k) (hR : #R = c) :
    Function.Injective (Fin.append (A.orderEmbOfFin hA) (R.orderEmbOfFin hR)) := by
  intro i j hij
  induction i using Fin.addCases with
  | left s =>
    induction j using Fin.addCases with
    | left s' => simp_all
    | right t' =>
      simp only [Fin.append_left, Fin.append_right] at hij
      exact absurd (orderEmbOfFin_mem R hR t')
        (Finset.disjoint_left.1 hAR (hij ▸ orderEmbOfFin_mem A hA s))
  | right t =>
    induction j using Fin.addCases with
    | left s' =>
      simp only [Fin.append_left, Fin.append_right] at hij
      exact absurd (orderEmbOfFin_mem R hR t)
        (Finset.disjoint_left.1 hAR (hij ▸ orderEmbOfFin_mem A hA s'))
    | right t' => simp_all

/-- The inversions of the list `a₁, …, a_k, r₁, …, r_c` (elements of `A`, then of a disjoint `R`,
each increasing) correspond to the pairs `(a, r) ∈ A × R` with `r < a`: there are `ν(A, R)`. -/
theorem card_inversions_append_orderEmbOfFin {k c : ℕ} {A R : Finset ι} (hAR : Disjoint A R)
    (hA : #A = k) (hR : #R = c) :
    #{p : Fin (k + c) × Fin (k + c) | p.1 < p.2 ∧
      Fin.append (A.orderEmbOfFin hA) (R.orderEmbOfFin hR) p.2 <
        Fin.append (A.orderEmbOfFin hA) (R.orderEmbOfFin hR) p.1} =
      shuffleCount A R := by
  set g := Fin.append (A.orderEmbOfFin hA) (R.orderEmbOfFin hR) with hg
  refine Finset.card_nbij (fun p => (g p.1, g p.2)) ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
    simp only [coe_filter, mem_product, Set.mem_setOf_eq]
    obtain ⟨hij, hg'⟩ := hp
    induction i using Fin.addCases with
    | left s =>
      induction j using Fin.addCases with
      | left s' =>
        have hss : s < s' := by
          rw [Fin.lt_def] at hij ⊢
          simpa only [Fin.val_castAdd] using hij
        simp only [hg, Fin.append_left] at hg'
        exact absurd hg' (not_lt.2 ((A.orderEmbOfFin hA).monotone hss.le))
      | right t' =>
        simp only [hg, Fin.append_left, Fin.append_right] at hg' ⊢
        exact ⟨⟨orderEmbOfFin_mem A hA s, orderEmbOfFin_mem R hR t'⟩, hg'⟩
    | right t =>
      induction j using Fin.addCases with
      | left s' =>
        exact absurd hij (not_lt.2 (by simp [Fin.le_def]; omega))
      | right t' =>
        simp only [hg, Fin.append_right] at hg'
        exact absurd hg' (not_lt.2 ((R.orderEmbOfFin hR).monotone
          ((Fin.natAdd_lt_natAdd_iff k).1 hij).le))
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (injective_append_orderEmbOfFin hAR hA hR h.1)
      (injective_append_orderEmbOfFin hAR hA hR h.2)
  · rintro ⟨a, r⟩ hp
    simp only [coe_filter, mem_product, Set.mem_setOf_eq] at hp
    obtain ⟨⟨ha, hr⟩, hra⟩ := hp
    rw [← Finset.mem_coe, ← range_orderEmbOfFin A hA] at ha
    rw [← Finset.mem_coe, ← range_orderEmbOfFin R hR] at hr
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hr
    refine ⟨(Fin.castAdd c s, Fin.natAdd k t), ?_, ?_⟩
    · simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, hg, Fin.append_left,
        Fin.append_right]
      exact ⟨by simp [Fin.lt_def]; omega, hra⟩
    · simp [hg]

/-- An injective `g : Fin n → ι` with values in a set `S` of size `n` is the increasing enumeration
of `S` composed with a permutation of `Fin n`. -/
theorem exists_perm_orderEmbOfFin {n : ℕ} {S : Finset ι} (h : #S = n) {g : Fin n → ι}
    (hg : Function.Injective g) (hS : ∀ i, g i ∈ S) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, S.orderEmbOfFin h (σ i) = g i := by
  let f : Fin n → Fin n := fun i => (S.orderIsoOfFin h).symm ⟨g i, hS i⟩
  have hf : Function.Injective f := fun i j hij => hg (by simpa [f] using hij)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun i => ?_⟩
  rw [Equiv.ofBijective_apply, ← coe_orderIsoOfFin_apply]
  simp [f]

/-- **The sign of the shuffle.** If `σ` reorders the increasing list of `A ∪ R` into
`a₁, …, a_k, r₁, …, r_c` (for disjoint `A`, `R`), then `sign σ = (-1)^{ν(A, R)}`. -/
theorem sign_eq_neg_one_pow_shuffleCount {k c : ℕ} {A R : Finset ι} (hAR : Disjoint A R)
    (hA : #A = k) (hR : #R = c) (h : #(A ∪ R) = k + c) {σ : Equiv.Perm (Fin (k + c))}
    (hσ : ∀ i, (A ∪ R).orderEmbOfFin h (σ i) =
      Fin.append (A.orderEmbOfFin hA) (R.orderEmbOfFin hR) i) :
    Equiv.Perm.sign σ = (-1) ^ shuffleCount A R := by
  rw [sign_eq_neg_one_pow_card_inversions, ← card_inversions_append_orderEmbOfFin hAR hA hR]
  congr 2
  refine Finset.filter_congr fun p _ => ?_
  rw [← hσ, ← hσ, OrderEmbedding.lt_iff_lt]

/-! ### Minors through a Schur complement -/

/-- **Minors through a Schur complement.** If `|R| = |C|`, `Δ_{R,C}(x) ≠ 0`, and `A`, `B` are
disjoint from `R`, `C` with `|A| = |B|`, then
`Δ_{A ∪ R, B ∪ C}(x) = (-1)^{ν(A,R) + ν(B,C)} Δ_{R,C}(x) Δ_{A,B}(x/(R,C))`. -/
@[cluster_algebras "lem_minor_schur_complement"]
theorem minor_union_eq_schurComplement {K : Type*} [Field K] (x : Matrix ι κ K)
    {R : Finset ι} {C : Finset κ} (hRC : C.card = R.card) (hd : minor x R C ≠ 0)
    {A : Finset ι} {B : Finset κ} (hA : Disjoint A R) (hB : Disjoint B C)
    (hAB : B.card = A.card) :
    minor x (A ∪ R) (B ∪ C) =
      (-1) ^ (shuffleCount A R + shuffleCount B C) * minor x R C *
        minor (schurComplement x R C) A B := by
  classical
  have hAR : #(A ∪ R) = #A + #R := card_union_of_disjoint hA
  have hBC : #(B ∪ C) = #A + #R := by rw [card_union_of_disjoint hB, hAB, hRC]
  set eA := A.orderEmbOfFin rfl
  set eR := R.orderEmbOfFin rfl
  set eB := B.orderEmbOfFin hAB
  set eC := C.orderEmbOfFin hRC
  have hmemAR : ∀ i, Fin.append eA eR i ∈ A ∪ R := fun i => by
    induction i using Fin.addCases with
    | left s => simp [eA, orderEmbOfFin_mem]
    | right t => simp [eR, orderEmbOfFin_mem]
  have hmemBC : ∀ i, Fin.append eB eC i ∈ B ∪ C := fun i => by
    induction i using Fin.addCases with
    | left s => simp [eB, orderEmbOfFin_mem]
    | right t => simp [eC, orderEmbOfFin_mem]
  obtain ⟨σ, hσ⟩ := exists_perm_orderEmbOfFin hAR (injective_append_orderEmbOfFin hA rfl rfl)
    hmemAR
  obtain ⟨τ, hτ⟩ := exists_perm_orderEmbOfFin hBC (injective_append_orderEmbOfFin hB hAB hRC)
    hmemBC
  rw [minor_of_card_eq x rfl hRC] at hd
  rw [minor_of_card_eq x hAR hBC, minor_of_card_eq x rfl hRC,
    minor_of_card_eq (schurComplement x R C) rfl hAB]
  set X := x.submatrix (Fin.append eA eR) (Fin.append eB eC)
  have hM : x.submatrix ((A ∪ R).orderEmbOfFin hAR) ((B ∪ C).orderEmbOfFin hBC) =
      (X.submatrix σ.symm id).submatrix id τ.symm := by
    ext i j
    simp only [X, submatrix_apply, id, eA, eR, eB, eC, ← hσ, ← hτ, Equiv.apply_symm_apply]
  rw [hM, det_permute', det_permute, Equiv.Perm.sign_symm, Equiv.Perm.sign_symm,
    sign_eq_neg_one_pow_shuffleCount hA rfl rfl hAR hσ,
    sign_eq_neg_one_pow_shuffleCount hB hAB hRC hBC hτ,
    ← det_submatrix_equiv_self finSumFinEquiv X]
  set V := x.submatrix eR eC
  have hX : X.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (x.submatrix eA eB) (x.submatrix eA eC) (x.submatrix eR eB) V := by
    ext (i | i) (j | j) <;> simp [X, V]
  have : Invertible V := invertibleOfIsUnitDet V (isUnit_iff_ne_zero.2 hd)
  rw [hX, det_fromBlocks₂₂, invOf_eq_nonsing_inv]
  have hS : x.submatrix eA eB - x.submatrix eA eC * V⁻¹ * x.submatrix eR eB =
      (schurComplement x R C).submatrix eA eB := by
    ext s t
    simp only [schurComplement, dif_pos hRC, sub_apply, submatrix_apply, mul_apply, sum_mul, V,
      eC, eR]
  rw [hS]
  push_cast
  ring

end ClusterAlgebras

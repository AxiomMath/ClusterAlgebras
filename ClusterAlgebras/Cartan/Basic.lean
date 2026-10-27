/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Graph
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.Order.Star.Real

/-!
# Generalized Cartan matrices

A *symmetrizable generalized Cartan matrix* has diagonal entries `2`, nonpositive off-diagonal
entries, and a positive diagonal *symmetrizer* `D` with `DA` symmetric; it is *of finite type*
when `DA` is positive definite for some symmetrizer. This file also proves that `aᵢⱼaⱼᵢ ≤ 3`
for a matrix of finite type and that its principal submatrices are again of finite type, states
Sylvester's criterion, and defines the Coxeter graph and the relation of having the same type.

## Main definitions

* `ClusterAlgebras.IsSymmetrizer A d`: `diag(d)` is a symmetrizer of `A`.
* `ClusterAlgebras.IsGeneralizedCartan A`: `A` is a symmetrizable generalized Cartan matrix.
* `ClusterAlgebras.IsCartanFiniteType A`: `A` is a Cartan matrix of finite type.
* `ClusterAlgebras.coxeterGraph A`, `ClusterAlgebras.IsIndecomposable A`: the Coxeter graph
  of `A`, and its connectedness.
* `ClusterAlgebras.SameCartanType A A'`: `A'` is a simultaneous permutation of `A`.

## Implementation notes

* Indices are `Fin n`, so the index range `[1, n]` of [FWZ] is shifted down by one.
* A symmetrizer is recorded by its vector of diagonal entries `d`: `DA` symmetric is
  `dᵢ aᵢⱼ = dⱼ aⱼᵢ`. [FWZ] allow real diagonal entries; for an integer matrix the linear
  conditions have an integer solution whenever they have a positive real one, so the integer
  definition agrees.
* Positive definiteness is stated directly, `0 < vᵀ (DA) v` for every nonzero real `v`; the
  proofs pass through Mathlib's `Matrix.PosDef`, to which it is equivalent for a symmetric real
  matrix.
* Sylvester's criterion is proved by induction on `n` through the Schur complement of the
  leading `(n - 1) × (n - 1)` block, `Matrix.schur_complement_eq₁₁` and
  `Matrix.det_fromBlocks₁₁`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.2.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

/-- `d` is a **symmetrizer** of `A`: its entries are positive integers and `DA` is symmetric
for `D = diag(d)`, that is `dᵢ aᵢⱼ = dⱼ aⱼᵢ` for all `i, j`. -/
@[cluster_algebras "def_generalized_cartan"]
def IsSymmetrizer (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ) : Prop :=
  (∀ i, 0 < d i) ∧ ∀ i j, d i * A i j = d j * A j i

/-- A **symmetrizable generalized Cartan matrix**: an integer matrix with diagonal entries `2`,
nonpositive entries off the diagonal, and a symmetrizer. -/
@[cluster_algebras "def_generalized_cartan"]
def IsGeneralizedCartan (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i, A i i = 2) ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧ ∃ d, IsSymmetrizer A d

/-- A symmetrizable generalized Cartan matrix `A` is **of finite type**, or a *Cartan matrix of
finite type*, when for some symmetrizer `D = diag(d)` the symmetric matrix `DA` is positive
definite: `vᵀ D A v > 0` for every nonzero `v ∈ ℝⁿ`. -/
@[cluster_algebras "def_cartan_finite_type"]
def IsCartanFiniteType (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsGeneralizedCartan A ∧ ∃ d, IsSymmetrizer A d ∧
    ∀ v : Fin n → ℝ, v ≠ 0 →
      0 < v ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ v)

/-- A block matrix `[A, B; Bᴴ, D]` with `A` positive definite is positive definite when its
Schur complement `D - Bᴴ A⁻¹ B` is. -/
theorem posDef_fromBlocks₁₁_of_posDef_schur {m p R : Type*} [CommRing R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] [Fintype m] [DecidableEq m] [Finite p]
    {A : Matrix m m R} (B : Matrix m p R) (D : Matrix p p R) (hA : A.PosDef) [Invertible A]
    (hS : (D - Bᴴ * A⁻¹ * B).PosDef) : (fromBlocks A B Bᴴ D).PosDef := by
  have := Fintype.ofFinite p
  refine .of_dotProduct_mulVec_pos ((IsHermitian.fromBlocks₁₁ B D hA.1).2 hS.1) fun z hz => ?_
  rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr z, schur_complement_eq₁₁ B D _ _ hA.1,
    ← dotProduct_mulVec, ← dotProduct_mulVec]
  by_cases hy : z ∘ Sum.inr = 0
  · have hx : z ∘ Sum.inl ≠ 0 := by
      intro hx; apply hz; ext (i|i)
      exacts [congrFun hx i, congrFun hy i]
    rw [hy, mulVec_zero, add_zero]
    exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos hx)
      (hS.posSemidef.dotProduct_mulVec_nonneg _)
  · exact add_pos_of_nonneg_of_pos (hA.posSemidef.dotProduct_mulVec_nonneg _)
      (hS.dotProduct_mulVec_pos hy)

/-- A `1 × 1` matrix over a trivially starred ordered ring with positive entry is positive
definite. -/
theorem posDef_of_unique_of_pos {m R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [StarRing R] [TrivialStar R] [Unique m]
    {A : Matrix m m R} (h : 0 < A default default) : A.PosDef := by
  refine .of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp [conjTranspose_apply, Subsingleton.elim i default, Subsingleton.elim j default]
  · have hx0 : x default ≠ 0 := fun h0 => hx (funext fun i => by rwa [Subsingleton.elim i default])
    simp only [dotProduct, mulVec, Fintype.sum_unique, star_trivial]
    nlinarith [mul_self_pos.2 hx0]

/-- The inductive step of Sylvester's criterion: a real Hermitian `(n + 1) × (n + 1)` matrix of
positive determinant whose leading `n × n` block is positive definite of positive determinant
is positive definite. -/
theorem posDef_of_posDef_castSucc_of_det_pos {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hM : M.IsHermitian) (hM' : (M.submatrix Fin.castSucc Fin.castSucc).PosDef)
    (hdet' : 0 < (M.submatrix Fin.castSucc Fin.castSucc).det) (hdet : 0 < M.det) :
    M.PosDef := by
  set e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
  set N := M.submatrix e e with hN
  have hMN : M = N.submatrix e.symm e.symm := by ext i j; simp [N]
  rw [hMN]
  refine PosDef.submatrix ?_ e.symm.injective
  have hA : N.toBlocks₁₁ = M.submatrix Fin.castSucc Fin.castSucc := rfl
  have h21 : N.toBlocks₂₁ = N.toBlocks₁₂ᴴ := by
    ext i j
    simpa [N, toBlocks₂₁, toBlocks₁₂, conjTranspose_apply] using
      (hM.apply (e (Sum.inr i)) (e (Sum.inl j))).symm
  have hNb : N = fromBlocks N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₁₂ᴴ N.toBlocks₂₂ := by
    rw [← h21, fromBlocks_toBlocks]
  rw [← hA] at hM' hdet'
  letI : Invertible N.toBlocks₁₁ := invertibleOfIsUnitDet _ hdet'.ne'.isUnit
  rw [hNb]
  refine posDef_fromBlocks₁₁_of_posDef_schur _ _ hM' (posDef_of_unique_of_pos ?_)
  have hdetN : N.det = N.toBlocks₁₁.det *
      (N.toBlocks₂₂ - N.toBlocks₁₂ᴴ * N.toBlocks₁₁⁻¹ * N.toBlocks₁₂).det := by
    conv_lhs => rw [hNb]
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  rw [hN, det_submatrix_equiv_self, ← hN,
    det_unique (N.toBlocks₂₂ - N.toBlocks₁₂ᴴ * N.toBlocks₁₁⁻¹ * N.toBlocks₁₂)] at hdetN
  rw [hdetN] at hdet
  exact pos_of_mul_pos_right hdet hdet'.le

/-- **Sylvester's criterion**, for Mathlib's `Matrix.PosDef`: a real Hermitian matrix whose
leading principal minors are all positive is positive definite. -/
theorem posDef_of_isHermitian_of_leadingMinors_pos :
    ∀ {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}, M.IsHermitian →
      (∀ (k : ℕ) (hk : k ≤ n), 1 ≤ k →
        0 < (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) → M.PosDef
  | 0, M, hM, _ => .of_dotProduct_mulVec_pos hM fun x hx => (hx (Subsingleton.elim _ _)).elim
  | n + 1, M, hM, hdet => by
    have hsub : ∀ (k : ℕ) (hk : k ≤ n),
        (M.submatrix Fin.castSucc Fin.castSucc).submatrix (Fin.castLE hk) (Fin.castLE hk) =
          M.submatrix (Fin.castLE (hk.trans n.le_succ)) (Fin.castLE (hk.trans n.le_succ)) := by
      intro k hk; rfl
    have hcs : M.submatrix Fin.castSucc Fin.castSucc =
        M.submatrix (Fin.castLE n.le_succ) (Fin.castLE n.le_succ) := rfl
    refine posDef_of_posDef_castSucc_of_det_pos hM
      (posDef_of_isHermitian_of_leadingMinors_pos (hM.submatrix _) fun k hk h1 => ?_) ?_ ?_
    · rw [hsub]; exact hdet k _ h1
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [hcs]; exact hdet n _ hn
    · simpa using hdet (n + 1) le_rfl (by omega)

/-- For a symmetrizer `d` of `A`, the real matrix `DA` is positive definite in Mathlib's sense
as soon as its quadratic form is positive on nonzero vectors. -/
theorem IsSymmetrizer.posDef_diagonal_mul {A : Matrix (Fin n) (Fin n) ℤ} {d : Fin n → ℤ}
    (hd : IsSymmetrizer A d)
    (hpos : ∀ v : Fin n → ℝ, v ≠ 0 →
      0 < v ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ v)) :
    (diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)).PosDef := by
  refine .of_dotProduct_mulVec_pos ?_ fun v hv => by simpa using hpos v hv
  ext i j
  simp only [conjTranspose_apply, diagonal_mul, map_apply, star_trivial]
  exact_mod_cast hd.2 j i

/-- **A Cartan matrix of finite type has `aᵢⱼ aⱼᵢ ≤ 3`** for `i ≠ j`: the `2 × 2` principal
minor `dᵢdⱼ(4 - aᵢⱼaⱼᵢ)` of `DA` is positive. -/
@[cluster_algebras "lem_cartan_bound_three"]
theorem IsCartanFiniteType.mul_le_three {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : IsCartanFiniteType A) {i j : Fin n} (hij : i ≠ j) : A i j * A j i ≤ 3 := by
  obtain ⟨⟨hdiag, -⟩, d, hd, hpos⟩ := hA
  have hP := (hd.posDef_diagonal_mul hpos).submatrix (e := ![i, j]) (by
    intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [eq_comm])
  have hv : (![-(d i * A i j : ℝ), 2 * d i] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    simp only [Fin.isValue, cons_val_one, cons_val_fin_one, Pi.zero_apply, mul_eq_zero,
      OfNat.ofNat_ne_zero, Int.cast_eq_zero, false_or] at h1
    exact (hd.1 i).ne' (by exact_mod_cast h1)
  have key := hP.dotProduct_mulVec_pos hv
  simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two, submatrix_apply, diagonal_mul,
    map_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hdiag] at key
  have hdi := hd.1 i
  have hdj := hd.1 j
  have key' : (0 : ℤ) < 2 * d i * (d i * d j * (4 - A i j * A j i)) := by
    have : (0 : ℝ) < 2 * d i * (d i * d j * (4 - A i j * A j i)) := by
      push_cast at key
      linear_combination key
    exact_mod_cast this
  have h1 := pos_of_mul_pos_right key' (by positivity)
  have h2 := pos_of_mul_pos_right h1 (by positivity)
  omega

/-- **A principal submatrix of a Cartan matrix of finite type is of finite type**: for an
injective map `e : Fin k → Fin n`, the submatrix `(a_{e(i) e(j)})` is of finite type. -/
@[cluster_algebras "lem_cartan_principal_submatrix"]
theorem IsCartanFiniteType.submatrix {A : Matrix (Fin n) (Fin n) ℤ} (hA : IsCartanFiniteType A)
    {k : ℕ} {e : Fin k → Fin n} (he : Function.Injective e) :
    IsCartanFiniteType (A.submatrix e e) := by
  obtain ⟨⟨hdiag, hoff, -⟩, d, hd, hpos⟩ := hA
  have hd' : IsSymmetrizer (A.submatrix e e) (d ∘ e) := ⟨fun i => hd.1 _, fun i j => hd.2 _ _⟩
  refine ⟨⟨fun i => hdiag _, fun i j hij => hoff _ _ (he.ne hij), _, hd'⟩, _, hd', fun v hv => ?_⟩
  have hP := (hd.posDef_diagonal_mul hpos).submatrix he
  have hsub : ((diagonal fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)).submatrix e e =
      diagonal (fun i => ((d ∘ e) i : ℝ)) * (A.submatrix e e).map (Int.cast : ℤ → ℝ) := by
    ext i j; simp [diagonal_mul]
  rw [← hsub]
  simpa using hP.dotProduct_mulVec_pos hv

/-- **Sylvester's criterion.** A real symmetric `n × n` matrix whose leading principal minors
`det (mᵢⱼ)_{i,j ∈ [1,k]}`, `k ∈ [1, n]`, are all positive is positive definite. -/
@[cluster_algebras "lem_sylvester_criterion"]
theorem posDef_of_leadingMinors_pos {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm)
    (hdet : ∀ (k : ℕ) (hk : k ≤ n), 1 ≤ k →
      0 < (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (M *ᵥ v) := by
  have hH : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hM
  intro v hv
  simpa using (posDef_of_isHermitian_of_leadingMinors_pos hH hdet).dotProduct_mulVec_pos hv

/-- The **Coxeter graph** of an `n × n` matrix `A`: the finite simple graph on `[1, n]` in which
`i ≠ j` are adjacent when `aᵢⱼ ≠ 0 ∨ aⱼᵢ ≠ 0`. For a symmetrizable generalized Cartan matrix
this is equivalent to `aᵢⱼ ≠ 0`. -/
@[cluster_algebras "def_coxeter_graph"]
def coxeterGraph (A : Matrix (Fin n) (Fin n) ℤ) : FiniteSimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => A i j ≠ 0

/-- Adjacency in the Coxeter graph, unfolded: `i ≠ j` and `aᵢⱼ ≠ 0` or `aⱼᵢ ≠ 0`. -/
theorem coxeterGraph_adj {A : Matrix (Fin n) (Fin n) ℤ} {i j : Fin n} :
    (coxeterGraph A).Adj i j ↔ i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0) :=
  SimpleGraph.fromRel_adj _ _ _

/-- Adjacency in the Coxeter graph is decidable. -/
instance instDecidableRelCoxeterGraphAdj (A : Matrix (Fin n) (Fin n) ℤ) :
    DecidableRel (coxeterGraph A).Adj := fun _ _ =>
  decidable_of_iff _ coxeterGraph_adj.symm

/-- A matrix is **indecomposable** when its Coxeter graph is connected. Connectedness includes
nonemptiness, so the `0 × 0` matrix is not indecomposable. -/
@[cluster_algebras "def_coxeter_graph"]
def IsIndecomposable (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (coxeterGraph A).Connected

/-- Two `n × n` matrices `A` and `A'` have the **same type** when `a'ᵢⱼ = a_{σ(i)σ(j)}` for a
permutation `σ` of `[1, n]` and all `i, j`. -/
@[cluster_algebras "def_cartan_same_type"]
def SameCartanType (A A' : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i j, A' i j = A (σ i) (σ j)

end ClusterAlgebras

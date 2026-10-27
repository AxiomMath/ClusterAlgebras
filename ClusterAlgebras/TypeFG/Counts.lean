/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeFG.Finite
public import ClusterAlgebras.TypeE.Certificate
public import ClusterAlgebras.TypeFG.CertificateData.F4Cert
public import ClusterAlgebras.TypeFG.CertificateData.G2Cert
public import ClusterAlgebras.TypeFG.CertificateData.G2ECert

/-!
# Counting in types `F₄` and `G₂`

We count the cluster variables and the clusters of seed patterns of types `F₄` and `G₂`.
Mutation at a sign-coherent column only negates a row and a column; with it, every `F₄` matrix
`P_ε` mutates to `P_{(1,1,1)}`, which is therefore a reference matrix. Exchange certificates for
`P_{(1,1,1)}`, for `R_1` and for the principal-coefficient extension `R̃` of `R_1` give the counts.

## Main definitions

* `ClusterAlgebras.TypeFG.matrixG₂Ext`: the `4 × 2` matrix `R̃`.

## Main statements

* `ClusterAlgebras.TypeFG.matrixMutation_eq_of_signCoherent`: mutation at a sign-coherent index.
* `ClusterAlgebras.TypeFG.isReferenceMatrix_matrixF₄_one`: `P_{(1,1,1)}` is a reference matrix
  for `F₄`.
* `ClusterAlgebras.IsSeedPattern.encard_of_isPatternOfType_F₄`,
  `ClusterAlgebras.IsSeedPattern.encard_of_isPatternOfType_G₂`: the numbers of cluster variables
  and of clusters.

## Implementation notes

* Indices are `Fin`, so they are shifted down by one. `P_{(1,1,1)}` is `matrixF₄ 1` and `R_1` is
  `matrixG₂ 1`.
* The existence of exchange certificates is stated existentially, as for the types `E₆`, `E₇`,
  `E₈`. It is proved from certificate data in
  `ClusterAlgebras.TypeFG.CertificateData`, checked by the kernel through
  `CertificateCheck.Raw.nonempty_exchangeCertificate` (no `native_decide`).
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

namespace TypeFG

/-- **Mutation at a sign-coherent index.** If `B` is a skew-symmetrizable `n × n` integer
matrix and `k` an index with `b_{ik} ≥ 0` for all `i`, or `b_{ik} ≤ 0` for all `i`, then `μ_k(B)`
is obtained from `B` by negating row `k` and column `k`. -/
@[cluster_algebras "lem_fg_sign_coherent_mutation"]
theorem matrixMutation_eq_of_signCoherent {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {k : Fin n} (hk : (∀ i, 0 ≤ B i k) ∨ ∀ i, B i k ≤ 0) :
    matrixMutation le_rfl B k = Matrix.of fun i j => if i = k ∨ j = k then -B i j else B i j := by
  have hsign := hB.signAntisymmetric_self
  ext i j
  simp only [matrixMutation, castLE_self, Matrix.of_apply]
  split_ifs with h₁ h₂ h₃ <;> try rfl
  · rcases hk with hk | hk
    · exact absurd (hk j) (not_le.2 ((hsign.2 k j).1 h₂.2))
    · exact absurd (hk i) (not_le.2 h₂.1)
  · rcases hk with hk | hk
    · exact absurd (hk i) (not_le.2 h₃.1)
    · have := hsign.2 j k
      simp only [castLE_self] at this
      exact absurd (hk j) (not_le.2 (this.2 h₃.2))

/-- A vector which is an integer combination of the rows of `B` lies in their span. -/
private theorem mem_span_range_of_sum_eq {m n : ℕ} {B : Matrix (Fin m) (Fin n) ℤ}
    (c : Fin m → ℤ) {v : Fin n → ℤ} (h : ∑ i, c i • B i = v) :
    v ∈ Submodule.span ℤ (Set.range B) :=
  h ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The rows of `B` span `ℤⁿ` as soon as their span contains every standard basis vector. -/
private theorem span_range_eq_top_of_single_mem {m n : ℕ} {B : Matrix (Fin m) (Fin n) ℤ}
    (h : ∀ i, Pi.single i 1 ∈ Submodule.span ℤ (Set.range B)) :
    Submodule.span ℤ (Set.range B) = ⊤ :=
  eq_top_iff.2 <| (Pi.basisFun ℤ (Fin n)).span_eq.symm.le.trans <|
    Submodule.span_le.2 <| Set.range_subset_iff.2 fun i => by simpa using h i

/-- **`P_{(1,1,1)}` is a reference matrix for `F₄`**: every `P_ε` mutates to `P_{(1,1,1)}` along
a sequence of length at most `4`. -/
@[cluster_algebras "lem_fg_F4_reference"]
theorem exists_matrixMutationList_matrixF₄_eq_one (ε : Fin 3 → ℤˣ) :
    ∃ w : List (Fin 4), w.length ≤ 4 ∧ matrixMutationList le_rfl (matrixF₄ ε) w = matrixF₄ 1 := by
  have hε : ε = ![ε 0, ε 1, ε 2] := by
    ext i
    fin_cases i <;> rfl
  rw [hε]
  rcases Int.units_eq_one_or (ε 0) with h0 | h0 <;>
    rcases Int.units_eq_one_or (ε 1) with h1 | h1 <;>
    rcases Int.units_eq_one_or (ε 2) with h2 | h2 <;>
    rw [h0, h1, h2]
  · exact ⟨[], by decide, by decide⟩
  · exact ⟨[3], by decide, by decide⟩
  · exact ⟨[1, 0], by decide, by decide⟩
  · exact ⟨[1, 0, 3], by decide, by decide⟩
  · exact ⟨[0], by decide, by decide⟩
  · exact ⟨[0, 3], by decide, by decide⟩
  · exact ⟨[0, 1, 0], by decide, by decide⟩
  · exact ⟨[0, 1, 0, 3], by decide, by decide⟩

/-- **`P_{(1,1,1)}` is a reference matrix for `F₄`.** -/
@[cluster_algebras "lem_fg_F4_reference"]
theorem isReferenceMatrix_matrixF₄_one : IsReferenceMatrix .F₄ (matrixF₄ 1) := by
  intro P hP hA
  obtain ⟨ε, rfl, -⟩ := exists_eq_matrixF₄ hP hA
  obtain ⟨w, -, hw⟩ := exists_matrixMutationList_matrixF₄_eq_one ε
  exact ⟨w, 1, by rw [relabelMatrix_self]; exact hw⟩

/-- **The `F₄` computation**, first part: the rows of `P_{(1,1,1)}` span `ℤ⁴`. -/
@[cluster_algebras "prop_fg_F4_computation"]
theorem span_range_matrixF₄_one : Submodule.span ℤ (Set.range (matrixF₄ 1)) = ⊤ := by
  refine span_range_eq_top_of_single_mem fun i => ?_
  fin_cases i
  · exact mem_span_range_of_sum_eq ![0, -1, 0, -1] (by decide)
  · exact mem_span_range_of_sum_eq ![1, 0, 0, 0] (by decide)
  · exact mem_span_range_of_sum_eq ![0, 0, 0, -1] (by decide)
  · exact mem_span_range_of_sum_eq ![2, 0, 1, 0] (by decide)

/-- **The `F₄` computation**, second part: there is an exchange certificate for `P_{(1,1,1)}`
with `28` variables and `105` seeds. Checked by the kernel on the certificate data of
`ClusterAlgebras.TypeFG.CertificateData.F4`. -/
@[cluster_algebras "prop_fg_F4_computation"]
theorem nonempty_exchangeCertificate_matrixF₄_one :
    Nonempty (ExchangeCertificate le_rfl (matrixF₄ 1) 28 105) := by
  have h : matrixF₄ 1 = CertificateData.F4.initMatrix := by
    ext i j
    revert i j
    decide +kernel
  rw [h]
  exact CertificateData.F4.nonempty_exchangeCertificate le_rfl

/-- The `4 × 2` integer matrix `R̃` of the `G₂` computation, with rows `(0, 3)`, `(-1, 0)`,
`(1, 0)`, `(0, 1)`: the matrix `R_1` with principal coefficients. -/
@[cluster_algebras "prop_fg_G2_computation"]
def matrixG₂Ext : Matrix (Fin 4) (Fin 2) ℤ :=
  !![0, 3;
    -1, 0;
    1, 0;
    0, 1]

/-- **The `G₂` computation**: the principal part of `R̃` is `R_1`. -/
@[cluster_algebras "prop_fg_G2_computation"]
theorem principalPart_matrixG₂Ext : principalPart (by decide) matrixG₂Ext = matrixG₂ 1 := by
  decide

/-- **The `G₂` computation**: the rows of `R̃` span `ℤ²`. -/
@[cluster_algebras "prop_fg_G2_computation"]
theorem span_range_matrixG₂Ext : Submodule.span ℤ (Set.range matrixG₂Ext) = ⊤ := by
  refine span_range_eq_top_of_single_mem fun i => ?_
  fin_cases i
  · exact mem_span_range_of_sum_eq ![0, 0, 1, 0] (by decide)
  · exact mem_span_range_of_sum_eq ![0, 0, 0, 1] (by decide)

/-- **The `G₂` computation**: `R_1` is a reference matrix for `G₂`. -/
@[cluster_algebras "prop_fg_G2_computation"]
theorem isReferenceMatrix_matrixG₂_one : IsReferenceMatrix .G₂ (matrixG₂ 1) := by
  intro P hP hA
  obtain ⟨ε, rfl, -⟩ := exists_eq_matrixG₂ hP hA
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact ⟨[], 1, by rw [relabelMatrix_self]; rfl⟩
  · exact ⟨[(0 : Fin 2)], 1, by rw [relabelMatrix_self]; decide⟩

/-- **The `G₂` computation**: there are exchange certificates for `R_1` and for `R̃`, each with
`8` variables and `8` seeds. Checked by the kernel on the certificate data of
`ClusterAlgebras.TypeFG.CertificateData.G2` and `.G2E`. -/
@[cluster_algebras "prop_fg_G2_computation"]
theorem nonempty_exchangeCertificate_matrixG₂ :
    Nonempty (ExchangeCertificate le_rfl (matrixG₂ 1) 8 8) ∧
      Nonempty (ExchangeCertificate (by decide : 2 ≤ 4) matrixG₂Ext 8 8) := by
  have h₁ : matrixG₂ 1 = CertificateData.G2.initMatrix := by
    ext i j
    revert i j
    decide +kernel
  have h₂ : matrixG₂Ext = CertificateData.G2E.initMatrix := by
    ext i j
    revert i j
    decide +kernel
  rw [h₁, h₂]
  exact ⟨CertificateData.G2.nonempty_exchangeCertificate le_rfl,
    CertificateData.G2E.nonempty_exchangeCertificate _⟩

end TypeFG

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F] {m : ℕ}

/-- **Cluster variables and clusters in type `F₄`**: a seed pattern of type `F₄` has `28`
cluster variables and `105` clusters. -/
@[cluster_algebras "prop_type_FG_counts"]
theorem IsSeedPattern.encard_of_isPatternOfType_F₄ [CharZero K] (hmn : 4 ≤ m)
    {P : RegularTree 4 → SeedData F m 4} (hP : IsSeedPattern K hmn P)
    (hX : IsPatternOfType hmn P [.F₄]) :
    (patternClusterVariables hmn P).encard = 28 ∧ (patternClusters hmn P).encard = 105 := by
  obtain ⟨C⟩ := TypeFG.nonempty_exchangeCertificate_matrixF₄_one
  exact (ExchangeCertificate.isFiniteType_and_encard_of_isPatternOfType (X := .F₄)
    (TypeFG.skewSymmetrizable_matrixF₄ 1) TypeFG.isReferenceMatrix_matrixF₄_one le_rfl rfl
    TypeFG.span_range_matrixF₄_one C C hmn hP hX).2

/-- **Cluster variables and clusters in type `G₂`**: a seed pattern of type `G₂` has `8`
cluster variables and `8` clusters. -/
@[cluster_algebras "prop_type_FG_counts"]
theorem IsSeedPattern.encard_of_isPatternOfType_G₂ [CharZero K] (hmn : 2 ≤ m)
    {P : RegularTree 2 → SeedData F m 2} (hP : IsSeedPattern K hmn P)
    (hX : IsPatternOfType hmn P [.G₂]) :
    (patternClusterVariables hmn P).encard = 8 ∧ (patternClusters hmn P).encard = 8 := by
  obtain ⟨⟨C₀⟩, ⟨C₁⟩⟩ := TypeFG.nonempty_exchangeCertificate_matrixG₂
  exact (ExchangeCertificate.isFiniteType_and_encard_of_isPatternOfType (X := .G₂)
    (TypeFG.skewSymmetrizable_matrixG₂ 1) TypeFG.isReferenceMatrix_matrixG₂_one _
    TypeFG.principalPart_matrixG₂Ext TypeFG.span_range_matrixG₂Ext C₀ C₁ hmn hP hX).2

end ClusterAlgebras

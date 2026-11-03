/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ClusterAlgebras.QuasiCartan.SignCondition
public import ClusterAlgebras.QuasiCartan.External
public import ClusterAlgebras.TwoFinite.FiniteTypeClassification

/-!
# The Barot–Geiss–Zelevinsky criterion

A skew-symmetrizable integer matrix `B` defines seed patterns of finite type exactly when every
chordless cycle of `B` is cyclically oriented and `B` has a positive quasi-Cartan companion
(Barot–Geiss–Zelevinsky, Theorem 1.2). The condition is invariant under relabelling and
mutation equivalence, implies `2`-finiteness, and follows from `2`-finiteness through a mutation
equivalent matrix whose Cartan counterpart is of finite type.

## Main results

* `ClusterAlgebras.satisfiesBGZ_submatrix_perm_iff`: the Barot–Geiss–Zelevinsky condition is
  invariant under relabelling.
* `ClusterAlgebras.MutationEquiv.satisfiesBGZ_iff`: the condition is invariant under mutation
  equivalence of skew-symmetrizable matrices.
* `ClusterAlgebras.SatisfiesBGZ.isTwoFinite`: the condition implies `2`-finiteness.
* `ClusterAlgebras.SkewSymmetrizable.exists_isSeedPattern_principalPart_eq`: every
  skew-symmetrizable integer matrix is the exchange matrix of a seed pattern.
* `ClusterAlgebras.SkewSymmetrizable.tfae_satisfiesBGZ`: the equivalent characterizations of
  finite type.
* `ClusterAlgebras.IsSeedPattern.isFiniteType_iff_satisfiesBGZ`: a seed pattern is of finite
  type exactly when its exchange matrix satisfies the condition.

## Implementation notes

* The seed-pattern condition of the criterion quantifies over all seed patterns with exchange
  matrix `B` at some vertex, in any field `F` over any field `𝕜` of characteristic zero. In
  `SkewSymmetrizable.tfae_satisfiesBGZ` the fields are taken in `Type`;
  `IsSeedPattern.isFiniteType_iff_satisfiesBGZ` holds for fields in every universe.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.11][FWZ]
-/

@[expose] public section

universe u

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

/-! ### Relabelling and mutation -/

/-- `s(a, b)` is an edge of `B` exactly when `a ≠ b` and `B a b * B b a ≠ 0`. -/
private theorem isQCEdge_mk_iff {B : Matrix (Fin n) (Fin n) ℤ} {a b : Fin n} :
    IsQCEdge B s(a, b) ↔ a ≠ b ∧ B a b * B b a ≠ 0 := by
  refine ⟨fun ⟨i, j, he, hij, h⟩ => ?_, fun ⟨hab, h⟩ => ⟨a, b, rfl, hab, h⟩⟩
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hij, h⟩
  · exact ⟨hij.symm, by rwa [mul_comm]⟩

/-- Edges of a relabelled matrix are the relabelled edges. -/
private theorem isQCEdge_submatrix_perm_iff {B : Matrix (Fin n) (Fin n) ℤ}
    (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    IsQCEdge (B.submatrix π π) s(a, b) ↔ IsQCEdge B s(π a, π b) := by
  simp only [isQCEdge_mk_iff, submatrix_apply, π.injective.ne_iff]

/-- Cyclic enumerations of a relabelled matrix are the relabelled cyclic enumerations. -/
private theorem isQCCyclicEnumeration_submatrix_perm_iff {B : Matrix (Fin n) (Fin n) ℤ}
    (π : Equiv.Perm (Fin n)) (Z : Finset (Fin n)) {p : ℕ} (v : ZMod p → Fin n) :
    IsQCCyclicEnumeration (B.submatrix π π) Z v ↔
      IsQCCyclicEnumeration B (Z.map π.toEmbedding) (π ∘ v) := by
  unfold IsQCCyclicEnumeration
  refine and_congr Iff.rfl (and_congr (π.injective.of_comp_iff v).symm (and_congr ?_ ?_))
  · rw [Set.range_comp, Finset.coe_map, Equiv.coe_toEmbedding]
    exact (Set.image_injective.2 π.injective).eq_iff.symm
  · simp only [Function.comp_apply, isQCEdge_submatrix_perm_iff]

/-- **Relabelling a skew-symmetrizable matrix**: `B^π` is skew-symmetrizable. -/
@[cluster_algebras "lem_qc_relabel"]
theorem SkewSymmetrizable.submatrix_perm {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B)
    (π : Equiv.Perm (Fin n)) : SkewSymmetrizable (B.submatrix π π) :=
  skewSymmetrizable_submatrix hB π

/-- A relabelled companion is a companion of the relabelled matrix, positive if the
companion is. -/
@[cluster_algebras "lem_qc_relabel"]
theorem IsQuasiCartanCompanion.submatrix_perm {B A : Matrix (Fin n) (Fin n) ℤ}
    (hA : IsQuasiCartanCompanion B A) (π : Equiv.Perm (Fin n)) :
    IsQuasiCartanCompanion (B.submatrix π π) (A.submatrix π π) ∧
      (IsPositiveQuasiCartan A → IsPositiveQuasiCartan (A.submatrix π π)) := by
  have hsym : ∀ {d}, IsSymmetrizer A d → IsSymmetrizer (A.submatrix π π) (d ∘ π) :=
    fun hd => ⟨fun i => hd.1 _, fun i j => hd.2 _ _⟩
  obtain ⟨⟨hdiag, d₀, hd₀⟩, habs⟩ := hA
  have hqc : IsQuasiCartan (A.submatrix π π) := ⟨fun i => hdiag _, d₀ ∘ π, hsym hd₀⟩
  refine ⟨⟨hqc, fun i j hij => habs _ _ (π.injective.ne hij)⟩, ?_⟩
  rintro ⟨-, d, hd, hpos⟩
  refine ⟨hqc, d ∘ π, hsym hd, fun v hv => ?_⟩
  have hw : v ∘ π.symm ≠ 0 := fun h => hv (by
    funext i
    simpa using congrFun h (π i))
  convert hpos _ hw using 1
  simp only [dotProduct, mulVec, diagonal_mul, Matrix.map_apply, submatrix_apply,
    Function.comp_apply]
  conv_rhs => rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← Equiv.sum_comp π]
  simp

/-- `Z` is a chordless cycle of `B^π` exactly when `π(Z)` is one of `B`, and then the
two are cyclically oriented together. -/
@[cluster_algebras "lem_qc_relabel"]
theorem isQCChordlessCycle_submatrix_perm_iff {B : Matrix (Fin n) (Fin n) ℤ}
    (π : Equiv.Perm (Fin n)) (Z : Finset (Fin n)) :
    (IsQCChordlessCycle (B.submatrix π π) Z ↔ IsQCChordlessCycle B (Z.map π.toEmbedding)) ∧
      (IsQCChordlessCycle (B.submatrix π π) Z →
        (IsQCCyclicallyOriented (B.submatrix π π) Z ↔
          IsQCCyclicallyOriented B (Z.map π.toEmbedding))) := by
  have hcomp : ∀ {p : ℕ} (w : ZMod p → Fin n), π ∘ (π.symm ∘ w) = w := fun w => by
    funext s
    simp
  refine ⟨⟨fun ⟨p, v, hv⟩ => ⟨p, π ∘ v, (isQCCyclicEnumeration_submatrix_perm_iff π Z v).1 hv⟩,
    fun ⟨p, w, hw⟩ => ⟨p, π.symm ∘ w, (isQCCyclicEnumeration_submatrix_perm_iff π Z _).2
      (by rwa [hcomp])⟩⟩, fun _ => ⟨fun ⟨p, v, hv, hpos⟩ => ⟨p, π ∘ v,
      (isQCCyclicEnumeration_submatrix_perm_iff π Z v).1 hv, hpos⟩,
    fun ⟨p, w, hw, hpos⟩ => ⟨p, π.symm ∘ w, (isQCCyclicEnumeration_submatrix_perm_iff π Z _).2
      (by rwa [hcomp]), fun s => by simpa using hpos s⟩⟩⟩

/-- Relabelling preserves the Barot–Geiss–Zelevinsky condition. -/
private theorem SatisfiesBGZ.submatrix_perm {B : Matrix (Fin n) (Fin n) ℤ} (h : SatisfiesBGZ B)
    (π : Equiv.Perm (Fin n)) : SatisfiesBGZ (B.submatrix π π) := by
  obtain ⟨hcyc, A, hA, hpos⟩ := h
  refine ⟨fun Z hZ => ?_, A.submatrix π π, (hA.submatrix_perm π).1, (hA.submatrix_perm π).2 hpos⟩
  obtain ⟨h₁, h₂⟩ := isQCChordlessCycle_submatrix_perm_iff π Z
  exact (h₂ hZ).2 (hcyc _ (h₁.1 hZ))

/-- `B` satisfies the Barot–Geiss–Zelevinsky condition exactly when `B^π` does. -/
@[cluster_algebras "lem_qc_relabel"]
theorem satisfiesBGZ_submatrix_perm_iff {B : Matrix (Fin n) (Fin n) ℤ} (π : Equiv.Perm (Fin n)) :
    SatisfiesBGZ (B.submatrix π π) ↔ SatisfiesBGZ B := by
  refine ⟨fun h => ?_, fun h => h.submatrix_perm π⟩
  have h' := h.submatrix_perm π.symm
  rwa [submatrix_submatrix, π.self_comp_symm, submatrix_id_id] at h'

/-- Mutation equivalence preserves skew-symmetrizability. -/
private theorem MutationEquiv.skewSymmetrizable {B B' : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (h : MutationEquiv B B')
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{0}) :
    SkewSymmetrizable B' := by
  obtain ⟨ks, π, rfl⟩ := h
  exact skewSymmetrizable_submatrix (skewSymmetrizable_matrixMutationList
    (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation) hB ks) π

/-- Mutation equivalence carries the Barot–Geiss–Zelevinsky condition forward. -/
private theorem MutationEquiv.satisfiesBGZ {B B' : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (h : MutationEquiv B B') (hBGZ : SatisfiesBGZ B)
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{0})
    (hMatrixMutation : SatisfiesBGZ.MatrixMutation) :
    SatisfiesBGZ B' := by
  obtain ⟨ks, π, rfl⟩ := h
  refine SatisfiesBGZ.submatrix_perm ?_ π
  induction ks generalizing B with
  | nil => exact hBGZ
  | cons k ks ih =>
    exact ih (skewSymmetrizable_matrixMutation
      (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation) hB k) (hMatrixMutation hB hBGZ k)

/-- **Mutation equivalence preserves the condition**: for mutation equivalent
skew-symmetrizable `B`, `B'`, `B` satisfies the Barot–Geiss–Zelevinsky condition exactly when
`B'` does. -/
@[cluster_algebras "lem_qc_mutation_equivalence"]
theorem MutationEquiv.satisfiesBGZ_iff {B B' : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (h : MutationEquiv B B')
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{0})
    (hMatrixMutationMatrixMutation : MatrixMutationMatrixMutation.{0})
    (hMatrixMutation : SatisfiesBGZ.MatrixMutation) :
    SatisfiesBGZ B ↔ SatisfiesBGZ B' :=
  ⟨fun h' => h.satisfiesBGZ (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      (hMatrixMutation := hMatrixMutation) hB h',
    fun h' => (h.symm (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)).satisfiesBGZ
      (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation) (hMatrixMutation := hMatrixMutation)
      (h.skewSymmetrizable (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation) hB) h'⟩

/-- A matrix mutation equivalent to one whose Cartan counterpart is of finite type satisfies the
Barot–Geiss–Zelevinsky condition. -/
private theorem MutationEquiv.satisfiesBGZ_of_isCartanFiniteType {B B' : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (h : MutationEquiv B B')
    (hcart : IsCartanFiniteType (cartanCounterpart B'))
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{0})
    (hMatrixMutationMatrixMutation : MatrixMutationMatrixMutation.{0})
    (hMatrixMutation : SatisfiesBGZ.MatrixMutation) : SatisfiesBGZ B :=
  (h.satisfiesBGZ_iff (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
    (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)
    (hMatrixMutation := hMatrixMutation) hB).2
    ((h.skewSymmetrizable (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      hB).satisfiesBGZ_of_isCartanFiniteType hcart).2

/-- **The condition implies `2`-finiteness**: a skew-symmetrizable matrix satisfying the
Barot–Geiss–Zelevinsky condition is `2`-finite. -/
@[cluster_algebras "lem_qc_two_finite"]
theorem SatisfiesBGZ.isTwoFinite {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B)
    (h : SatisfiesBGZ B)
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{0})
    (hMatrixMutationMatrixMutation : MatrixMutationMatrixMutation.{0})
    (hMatrixMutation : SatisfiesBGZ.MatrixMutation) : IsTwoFinite B := by
  refine ⟨hB, fun B' hBB' i j => ?_⟩
  obtain ⟨-, A, hA, hpos⟩ := (hBB'.satisfiesBGZ_iff
    (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
    (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)
    (hMatrixMutation := hMatrixMutation) hB).1 h
  by_cases hij : i = j
  · obtain ⟨d, hd⟩ := hBB'.skewSymmetrizable (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      hB
    subst hij
    simp [hd.apply_self_eq_zero i]
  · obtain ⟨h₀, h₃⟩ := hpos.mul_le_three hij
    rwa [abs_mul, ← hA.2 i j hij, ← hA.2 j i (Ne.symm hij), ← abs_mul, abs_of_nonneg h₀]

/-- **Every skew-symmetrizable integer matrix is an exchange matrix**: for every vertex `t₀`
there is a seed pattern of rank `n` in `ℚ(X₁, …, Xₙ)` over `ℚ` whose exchange matrix at `t₀`
is `B`. -/
@[cluster_algebras "lem_qc_pattern_exists"]
theorem SkewSymmetrizable.exists_isSeedPattern_principalPart_eq {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (t₀ : RegularTree n)
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{0})
    (hMatrixMutationMatrixMutation : MatrixMutationMatrixMutation.{0}) :
    ∃ P : RegularTree n → SeedData (FractionRing (MvPolynomial (Fin n) ℚ)) n n,
      IsSeedPattern ℚ le_rfl P ∧ principalPart le_rfl (P t₀).extExchangeMatrix = B := by
  obtain ⟨P, hP, hP₀⟩ := exists_isSeedPattern (K := ℚ)
    (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
    (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation) le_rfl t₀
    (isLabeledSeed_genericSeed le_rfl (B := B) hB)
  exact ⟨P, hP, by rw [hP₀]; rfl⟩

/-! ### The criterion -/

/-- `2`-finiteness gives the Barot–Geiss–Zelevinsky condition, through a mutation equivalent
matrix whose Cartan counterpart is of finite type. -/
private theorem IsTwoFinite.satisfiesBGZ {B : Matrix (Fin n) (Fin n) ℤ} (h : IsTwoFinite B)
    (hExistsIsTShapeMatrixMutationListOfIsCrownShape :
      ExistsIsTShapeMatrixMutationListOfIsCrownShape)
    (hIsCyclicallyOrientedOfIsTwoFinite : IsChordlessCycle.IsCyclicallyOrientedOfIsTwoFinite)
    (hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne :
      IsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne)
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{0})
    (hMatrixMutationMatrixMutation : MatrixMutationMatrixMutation.{0})
    (hExistsMutationPathOfIsTreeOrientation : Quiver.ExistsMutationPathOfIsTreeOrientation.{0})
    (hMatrixMutation : SatisfiesBGZ.MatrixMutation)
    (hSkewSymmetrizationMatrixMutation : SkewSymmetrizable.SkewSymmetrizationMatrixMutation) :
    SatisfiesBGZ B := by
  obtain ⟨B', hBB', hcart⟩ := h.exists_mutationEquiv_isCartanFiniteType
    (hExistsIsTShapeMatrixMutationListOfIsCrownShape :=
      hExistsIsTShapeMatrixMutationListOfIsCrownShape)
    (hIsCyclicallyOrientedOfIsTwoFinite := hIsCyclicallyOrientedOfIsTwoFinite)
    (hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne :=
      hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne)
    (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
    (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)
    (hExistsMutationPathOfIsTreeOrientation := hExistsMutationPathOfIsTreeOrientation)
    (hSkewSymmetrizationMatrixMutation := hSkewSymmetrizationMatrixMutation)
  exact hBB'.satisfiesBGZ_of_isCartanFiniteType h.1 hcart
    (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
    (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)
    (hMatrixMutation := hMatrixMutation)

/-- **The Barot–Geiss–Zelevinsky criterion.** For a skew-symmetrizable integer matrix `B` the
following are equivalent: (1) some `B'` mutation equivalent to `B` has `A(B')` a Cartan matrix
of finite type; (2) every seed pattern of rank `n`, in any field `F` over any field `𝕜` of
characteristic zero (both in `Type`), with exchange matrix `B` at some vertex, is of finite
type; (3) `B` is `2`-finite; (4) every chordless cycle of `B` is cyclically oriented and `B`
has a positive quasi-Cartan companion. -/
@[cluster_algebras "thm_quasi_cartan_criterion"]
theorem SkewSymmetrizable.tfae_satisfiesBGZ {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hCartanKilling : CartanKilling)
    (hExistsIsTShapeMatrixMutationListOfIsCrownShape :
      ExistsIsTShapeMatrixMutationListOfIsCrownShape)
    (hIsCyclicallyOrientedOfIsTwoFinite : IsChordlessCycle.IsCyclicallyOrientedOfIsTwoFinite)
    (hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne :
      IsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne)
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{0})
    (hMatrixMutationMatrixMutation : MatrixMutationMatrixMutation.{0})
    (hPluckerCoordThreeTerm : PluckerCoordThreeTerm.{0})
    (hPolygonQuiverMutateIsoFlip : PolygonQuiverMutateIsoFlip)
    (hExistsMutationPathOfIsTreeOrientation : Quiver.ExistsMutationPathOfIsTreeOrientation.{0})
    (hMatrixMutation : SatisfiesBGZ.MatrixMutation)
    (hSkewSymmetrizationMatrixMutation : SkewSymmetrizable.SkewSymmetrizationMatrixMutation)
    (hLabelledMatrixDFlip : TypeD.LabelledMatrixDFlip)
    (hIsGloballyFoldableMatrixE₆Lift : TypeFG.IsGloballyFoldableMatrixE₆Lift) :
    List.TFAE
      [∃ B' : Matrix (Fin n) (Fin n) ℤ, MutationEquiv B B' ∧
          IsCartanFiniteType (cartanCounterpart B'),
        ∀ (𝕜 F : Type) [Field 𝕜] [CharZero 𝕜] [Field F] [Algebra 𝕜 F] (m : ℕ) (hmn : n ≤ m)
          (P : RegularTree n → SeedData F m n), IsSeedPattern 𝕜 hmn P →
            (∃ t, principalPart hmn (P t).extExchangeMatrix = B) → IsFiniteType P,
        IsTwoFinite B,
        SatisfiesBGZ B] := by
  tfae_have 1 → 4 := fun ⟨_, hBB', hcart⟩ => hBB'.satisfiesBGZ_of_isCartanFiniteType hB hcart
      (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)
      (hMatrixMutation := hMatrixMutation)
  tfae_have 4 → 3 := fun h => SatisfiesBGZ.isTwoFinite
      (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)
      (hMatrixMutation := hMatrixMutation) hB h
  tfae_have 3 → 1 := fun h => IsTwoFinite.exists_mutationEquiv_isCartanFiniteType
      (hExistsIsTShapeMatrixMutationListOfIsCrownShape :=
        hExistsIsTShapeMatrixMutationListOfIsCrownShape)
      (hIsCyclicallyOrientedOfIsTwoFinite := hIsCyclicallyOrientedOfIsTwoFinite)
      (hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne :=
        hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne)
      (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)
      (hExistsMutationPathOfIsTreeOrientation := hExistsMutationPathOfIsTreeOrientation)
      (hSkewSymmetrizationMatrixMutation := hSkewSymmetrizationMatrixMutation) h
  tfae_have 3 → 2 := fun h3 𝕜 F _ _ _ _ m hmn P hP ⟨t, ht⟩ =>
    ((hP.tfae_isFiniteType (hCartanKilling := hCartanKilling)
      (hExistsIsTShapeMatrixMutationListOfIsCrownShape :=
        hExistsIsTShapeMatrixMutationListOfIsCrownShape)
      (hIsCyclicallyOrientedOfIsTwoFinite := hIsCyclicallyOrientedOfIsTwoFinite)
      (hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne :=
        hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne)
      (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)
      (hPluckerCoordThreeTerm₀ := hPluckerCoordThreeTerm)
      (hPluckerCoordThreeTerm := hPluckerCoordThreeTerm)
      (hPolygonQuiverMutateIsoFlip := hPolygonQuiverMutateIsoFlip)
      (hExistsMutationPathOfIsTreeOrientation := hExistsMutationPathOfIsTreeOrientation)
      (hSkewSymmetrizationMatrixMutation := hSkewSymmetrizationMatrixMutation)
      (hLabelledMatrixDFlip := hLabelledMatrixDFlip)
      (hIsGloballyFoldableMatrixE₆Lift := hIsGloballyFoldableMatrixE₆Lift) hmn t).out 3 2).1
      (ht ▸ h3)
  tfae_have 2 → 3 := fun h2 => by
    obtain ⟨P, hP, hP₀⟩ := hB.exists_isSeedPattern_principalPart_eq
      (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation) RegularTree.root
    exact hP₀ ▸ hP.isTwoFinite_of_isFiniteType
      (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation) le_rfl
      (h2 ℚ _ n le_rfl P hP ⟨_, hP₀⟩) RegularTree.root
  tfae_finish

/-- **The criterion for a given seed pattern**: if the exchange matrix of `P t` is `B`, then
`P` is of finite type exactly when `B` satisfies the Barot–Geiss–Zelevinsky condition. -/
@[cluster_algebras "thm_quasi_cartan_criterion"]
theorem IsSeedPattern.isFiniteType_iff_satisfiesBGZ {𝕜 : Type u} {F : Type*} [Field 𝕜]
    [CharZero 𝕜] [Field F] [Algebra 𝕜 F] {m : ℕ} (hmn : n ≤ m) {P : RegularTree n → SeedData F m n}
    (hP : IsSeedPattern 𝕜 hmn P) (t : RegularTree n) (hCartanKilling : CartanKilling)
    (hExistsIsTShapeMatrixMutationListOfIsCrownShape :
      ExistsIsTShapeMatrixMutationListOfIsCrownShape)
    (hIsCyclicallyOrientedOfIsTwoFinite : IsChordlessCycle.IsCyclicallyOrientedOfIsTwoFinite)
    (hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne :
      IsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne)
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{0})
    (hMatrixMutationMatrixMutation : MatrixMutationMatrixMutation.{0})
    (hPluckerCoordThreeTerm₀ : PluckerCoordThreeTerm.{0})
    (hPluckerCoordThreeTerm : PluckerCoordThreeTerm.{u})
    (hPolygonQuiverMutateIsoFlip : PolygonQuiverMutateIsoFlip)
    (hExistsMutationPathOfIsTreeOrientation : Quiver.ExistsMutationPathOfIsTreeOrientation.{0})
    (hMatrixMutation : SatisfiesBGZ.MatrixMutation)
    (hSkewSymmetrizationMatrixMutation : SkewSymmetrizable.SkewSymmetrizationMatrixMutation)
    (hLabelledMatrixDFlip : TypeD.LabelledMatrixDFlip)
    (hIsGloballyFoldableMatrixE₆Lift : TypeFG.IsGloballyFoldableMatrixE₆Lift) :
    IsFiniteType P ↔ SatisfiesBGZ (principalPart hmn (P t).extExchangeMatrix) :=
  ⟨fun h => (hP.isTwoFinite_of_isFiniteType (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation) hmn h t).satisfiesBGZ
      (hExistsIsTShapeMatrixMutationListOfIsCrownShape :=
        hExistsIsTShapeMatrixMutationListOfIsCrownShape)
      (hIsCyclicallyOrientedOfIsTwoFinite := hIsCyclicallyOrientedOfIsTwoFinite)
      (hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne :=
        hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne)
      (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)
      (hExistsMutationPathOfIsTreeOrientation := hExistsMutationPathOfIsTreeOrientation)
      (hMatrixMutation := hMatrixMutation)
      (hSkewSymmetrizationMatrixMutation := hSkewSymmetrizationMatrixMutation),
    fun h => ((hP.tfae_isFiniteType (hCartanKilling := hCartanKilling)
      (hExistsIsTShapeMatrixMutationListOfIsCrownShape :=
        hExistsIsTShapeMatrixMutationListOfIsCrownShape)
      (hIsCyclicallyOrientedOfIsTwoFinite := hIsCyclicallyOrientedOfIsTwoFinite)
      (hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne :=
        hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne)
      (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
      (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)
      (hPluckerCoordThreeTerm₀ := hPluckerCoordThreeTerm₀)
      (hPluckerCoordThreeTerm := hPluckerCoordThreeTerm)
      (hPolygonQuiverMutateIsoFlip := hPolygonQuiverMutateIsoFlip)
      (hExistsMutationPathOfIsTreeOrientation := hExistsMutationPathOfIsTreeOrientation)
      (hSkewSymmetrizationMatrixMutation := hSkewSymmetrizationMatrixMutation)
      (hLabelledMatrixDFlip := hLabelledMatrixDFlip)
      (hIsGloballyFoldableMatrixE₆Lift := hIsGloballyFoldableMatrixE₆Lift) hmn t).out 3 2).1
      (h.isTwoFinite (hSubmatrixMatrixMutation := hSubmatrixMatrixMutation)
        (hMatrixMutationMatrixMutation := hMatrixMutationMatrixMutation)
        (hMatrixMutation := hMatrixMutation) (hP.1 t).2)⟩

end ClusterAlgebras

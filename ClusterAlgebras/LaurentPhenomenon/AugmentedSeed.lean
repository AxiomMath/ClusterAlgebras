/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.LaurentPhenomenon.Trivialization
public import ClusterAlgebras.LaurentPhenomenon.Specialization
public import ClusterAlgebras.LaurentPhenomenon.FirstPrime
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# The augmented seed

Two steps of the proof of the Laurent phenomenon along a sequence of mutations.

*The augmented seed.* Let `(x̃, B̃)` be a labeled seed in `F` over `𝕜`, of size `m × n`, and let
`R` be a `p × n` integer matrix. In the field `F(u₁, …, u_p)` of rational functions in `p`
indeterminates over `F`, the tuple `x̃⁺ = (x₁, …, xₘ, u₁, …, u_p)` together with the
`(m + p) × n` matrix `B̃⁺` whose first `m` rows are `B̃` and whose last `p` rows are `R` is a
labeled seed over `𝕜`: the indeterminates are algebraically independent over `F`, so `x̃⁺` is
algebraically independent over `𝕜`; it generates `F(u₁, …, u_p)` because `x̃` generates `F`;
and `B̃⁺` has the principal part of `B̃`. The proof of the Laurent phenomenon takes `p = 2`,
with the two new rows the unit rows in two columns `j` and `k`.

*Specialization.* Let `(x̃, B̃)` be a seed in `F` and `(x̃⁺, B̃⁺)` a seed in `F⁺`, both with
extended clusters algebraically independent over `ℚ`, and let `ι` be injective and the identity
on the first `n` positions with `B̃` the matrix of rows `B̃⁺_{ι(a) ·}`. If the entry in position
`ι(a)` of the extended cluster of `μ_s(x̃⁺, B̃⁺)` lies in `ℤ[(x̃⁺)^{±1}]`, then the entry in
position `a` of that of `μ_s(x̃, B̃)` lies in `ℤ[x̃^{±1}]`. The semifield homomorphism
`ψ : ℚ_sf(x̃⁺) → ℚ_sf(x̃)` sending `x⁺_{ι(a)}` to `x_a` and every other entry of `x̃⁺` to `1`
sends the first entry to the second, and preserves Laurentness.

## Main definitions

* `SeedData.augment`: the seed `(x̃⁺, B̃⁺)` in `F(u₁, …, u_p)`.

## Main results

* `IsLabeledSeed.augment`: the augmented seed of a labeled seed is a labeled seed.
* `seedMutationSeq_extCluster_mem_laurentSubring_of_submatrix`: Laurentness of the mutations
  of `(x̃⁺, B̃⁺)` in a position `ι(a)` gives Laurentness of those of `(x̃, B̃)` in position `a`.
* `IsLabeledSeed.exists_augmentedSeed`: the augmented seed with unit rows in columns `j` and
  `k`, packaged with the reduction of the Laurent phenomenon for `(x̃, B̃)` to that for it.

## Implementation notes

FWZ add two indeterminates with the unit rows in columns `j` and `k`; the construction
and the fact that it is a labeled seed hold for any number `p` of indeterminates and any rows
`R`, so they are stated so. The field `F(u₁, …, u_p)` is the field of fractions of
`F[u₁, …, u_p]`, which lives in the same universe as `F`; the proof of the Laurent phenomenon
inducts over all fields of a universe and needs this. The specialization step holds for any
two seeds whose matrices are related by deleting rows other than the first `n`, with no
relation between the fields or between the extended clusters beyond algebraic independence
over `ℚ`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 1–3*][FWZ16]
-/

@[expose] public section

namespace ClusterAlgebras

open Function

/-! ### Specialization -/

section Specialization

variable {F F' : Type*} [Field F] [Field F'] [CharZero F] [CharZero F'] {m m' n : ℕ}

/-- **Specialization reduces Laurentness to a larger seed.** Let `S = (x̃, B̃)` and
`T = (x̃⁺, B̃⁺)` be seeds whose extended clusters are algebraically independent over `ℚ`, and let
`ι` be injective and the identity on the first `n` positions, with `B̃` the matrix of rows
`B̃⁺_{ι(a) ·}`. If the entry in position `ι(a)` of the extended cluster of `μ_s(T)` lies in
`ℤ[(x̃⁺)^{±1}]`, then the entry in position `a` of that of `μ_s(S)` lies in `ℤ[x̃^{±1}]`. -/
theorem seedMutationSeq_extCluster_mem_laurentSubring_of_submatrix (hmn : n ≤ m)
    (hmn' : n ≤ m') {S : SeedData F m n} {T : SeedData F' m' n}
    (hS : AlgebraicIndependent ℚ S.extCluster) (hT : AlgebraicIndependent ℚ T.extCluster)
    {ι : Fin m → Fin m'} (hι : Injective ι)
    (hιn : ∀ k : Fin n, ι (Fin.castLE hmn k) = Fin.castLE hmn' k)
    (hB : S.extExchangeMatrix = T.extExchangeMatrix.submatrix ι id) (s : List (Fin n))
    (a : Fin m)
    (h : (seedMutationSeq hmn' T s).extCluster (ι a) ∈ laurentSubring T.extCluster) :
    (seedMutationSeq hmn S s).extCluster a ∈ laurentSubring S.extCluster := by
  haveI : Fact (AlgebraicIndependent ℚ S.extCluster) := ⟨hS⟩
  haveI : Fact (AlgebraicIndependent ℚ T.extCluster) := ⟨hT⟩
  let f : Fin m' → universalSemifield S.extCluster :=
    extend ι (fun a => ⟨S.extCluster a, mem_universalSemifield_self _ a⟩) 1
  let ψ := universalSemifieldLift T.extCluster f
  have hψ (a : Fin m) : (ψ ⟨T.extCluster (ι a), mem_universalSemifield_self _ (ι a)⟩ : F) =
      S.extCluster a := by
    simp [ψ, f, hι.extend_apply]
  have hψ₁ (i : Fin m') (hi : i ∉ Set.range ι) :
      ψ ⟨T.extCluster i, mem_universalSemifield_self _ i⟩ = 1 := by
    simp only [ψ, universalSemifieldLift_apply_self, f]
    exact extend_apply' _ _ _ hi
  rw [← ψ.coe_apply_seedMutationSeq_extCluster hmn' hmn (mem_universalSemifield_self _) hι hιn
    hB hψ hψ₁ s a]
  exact ψ.coe_apply_mem_laurentSubring_of_comp hψ hψ₁ _ h

end Specialization

/-! ### The augmented seed -/

section Augment

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m n p : ℕ}

/-- The **augmented seed** of `S = (x̃, B̃)` by a `p × n` integer matrix `R`: in the field
`F(u₁, …, u_p)` of rational functions in `p` indeterminates over `F`, the extended cluster
`(x₁, …, xₘ, u₁, …, u_p)` and the matrix whose first `m` rows are `B̃` and whose last `p` rows
are `R`. -/
noncomputable def SeedData.augment (S : SeedData F m n) (R : Matrix (Fin p) (Fin n) ℤ) :
    SeedData (FractionRing (MvPolynomial (Fin p) F)) (m + p) n where
  extCluster := Fin.append (fun i => algebraMap F _ (S.extCluster i))
    fun i => algebraMap (MvPolynomial (Fin p) F) _ (MvPolynomial.X i)
  extExchangeMatrix := Matrix.of (Fin.append S.extExchangeMatrix R)

namespace SeedData

variable (S : SeedData F m n) (R : Matrix (Fin p) (Fin n) ℤ)

/-- The first `m` entries of the extended cluster of the augmented seed are those of `S`. -/
@[simp]
theorem augment_extCluster_castAdd (i : Fin m) :
    (S.augment R).extCluster (Fin.castAdd p i) = algebraMap F _ (S.extCluster i) := by
  simp [augment]

/-- The last `p` entries of the extended cluster of the augmented seed are the
indeterminates. -/
@[simp]
theorem augment_extCluster_natAdd (i : Fin p) :
    (S.augment R).extCluster (Fin.natAdd m i) =
      algebraMap (MvPolynomial (Fin p) F) _ (MvPolynomial.X i) := by
  simp [augment]

/-- The first `m` rows of the matrix of the augmented seed are those of `S`. -/
@[simp]
theorem augment_extExchangeMatrix_castAdd (i : Fin m) (l : Fin n) :
    (S.augment R).extExchangeMatrix (Fin.castAdd p i) l = S.extExchangeMatrix i l := by
  simp [augment]

/-- The first `m` rows of the matrix of the augmented seed are those of `S`, indexed through
`Fin.castLE`. -/
theorem augment_extExchangeMatrix_castLE (h : m ≤ m + p) (i : Fin m) (l : Fin n) :
    (S.augment R).extExchangeMatrix (Fin.castLE h i) l = S.extExchangeMatrix i l :=
  S.augment_extExchangeMatrix_castAdd R i l

/-- The last `p` rows of the matrix of the augmented seed are those of `R`. -/
@[simp]
theorem augment_extExchangeMatrix_natAdd (i : Fin p) (l : Fin n) :
    (S.augment R).extExchangeMatrix (Fin.natAdd m i) l = R i l := by
  simp [augment]

/-- Deleting the last `p` rows of the matrix of the augmented seed gives the matrix of `S`. -/
theorem augment_extExchangeMatrix_submatrix :
    (S.augment R).extExchangeMatrix.submatrix (Fin.castAdd p) id = S.extExchangeMatrix := by
  ext i l
  simp

/-- The principal part of the matrix of the augmented seed is that of `S`. -/
theorem augment_extExchangeMatrix_castLE_castLE (hmn : n ≤ m) (hmn' : n ≤ m + p)
    (a b : Fin n) :
    (S.augment R).extExchangeMatrix (Fin.castLE hmn' a) b =
      S.extExchangeMatrix (Fin.castLE hmn a) b :=
  S.augment_extExchangeMatrix_castLE R (Nat.le_add_right m p) (Fin.castLE hmn a) b

end SeedData

/-- **The augmented seed is a labeled seed.** If `(x̃, B̃)` is a labeled seed in `F` over `𝕜`,
then so is its augmented seed `(x̃⁺, B̃⁺)` in `F(u₁, …, u_p)`, for any `p × n`
integer matrix `R`. -/
theorem IsLabeledSeed.augment (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S)
    (R : Matrix (Fin p) (Fin n) ℤ) (hmn' : n ≤ m + p) : IsLabeledSeed K hmn' (S.augment R) := by
  set P := MvPolynomial (Fin p) F
  set L := FractionRing P
  set u : Fin p → L := fun i => algebraMap P L (MvPolynomial.X i)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hu : AlgebraicIndependent F u :=
      (MvPolynomial.algebraicIndependent_X (Fin p) F).map' (f := IsScalarTower.toAlgHom F P L)
        (IsFractionRing.injective _ _)
    let e : Fin (m + p) ≃ Fin p ⊕ Fin m := finSumFinEquiv.symm.trans (Equiv.sumComm _ _)
    have he : (S.augment R).extCluster = Sum.elim u (algebraMap F L ∘ S.extCluster) ∘ e := by
      ext i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [e, u] <;> rfl
    rw [he]
    exact (hS.1.1.sumElim_comp hu).comp e e.injective
  · set E := IntermediateField.adjoin K (Set.range (S.augment R).extCluster)
    have hF (c : F) : algebraMap F L c ∈ E := by
      have hc : IsScalarTower.toAlgHom K F L c ∈
          (IntermediateField.adjoin K (Set.range S.extCluster)).map
            (IsScalarTower.toAlgHom K F L) := by
        rw [hS.1.2]
        exact ⟨c, trivial, rfl⟩
      rw [IntermediateField.adjoin_map, ← Set.range_comp] at hc
      refine IntermediateField.adjoin_le_iff.2 ?_ hc
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin _ _
        ⟨Fin.castAdd p i, S.augment_extCluster_castAdd R i⟩
    have hP (f : P) : algebraMap P L f ∈ E := by
      induction f using MvPolynomial.induction_on with
      | C a =>
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact hF a
      | add f g hf hg =>
        rw [map_add]
        exact add_mem hf hg
      | mul_X f i hf =>
        rw [map_mul]
        exact mul_mem hf (IntermediateField.subset_adjoin _ _
          ⟨Fin.natAdd m i, S.augment_extCluster_natAdd R i⟩)
    rw [eq_top_iff]
    rintro z -
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := P) z
    exact div_mem (hP a) (hP b)
  · have h : (S.augment R).extExchangeMatrix.submatrix (Fin.castLE hmn') id =
        S.extExchangeMatrix.submatrix (Fin.castLE hmn) id :=
      Matrix.ext fun a b => S.augment_extExchangeMatrix_castLE_castLE R hmn hmn' a b
    change SkewSymmetrizable _
    rw [h]
    exact hS.2

end Augment

/-! ### The augmented seed of the Laurent phenomenon -/

universe u v

/-- **The augmented seed of the Laurent phenomenon.** Let `(x̃, B̃)` be a labeled seed in `F`
over a field `𝕜` of characteristic zero, of size `m × n`, and let `j, k ∈ [1, n]`. There is a
field `F⁺ ⊇ 𝕜`, in the universe of `F`, and a labeled seed `(x̃⁺, B̃⁺)` in `F⁺` over `𝕜` of size
`(m + 2) × n` whose first `m` rows are those of `B̃`, whose row `m + 1` is the unit row in
column `j` and whose row `m + 2` is the unit row in column `k`, such that if the entry in
position `i` of the extended cluster of `μ_s(x̃⁺, B̃⁺)` lies in `ℤ[(x̃⁺)^{±1}]`, then the entry
in position `i` of that of `μ_s(x̃, B̃)` lies in `ℤ[x̃^{±1}]`. -/
theorem IsLabeledSeed.exists_augmentedSeed {K : Type v} {F : Type u} [Field K] [Field F]
    [Algebra K F] [CharZero K] {m n : ℕ} (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (hmn' : n ≤ m + 2) (j k : Fin n) :
    ∃ (F' : Type u) (_ : Field F') (_ : Algebra K F') (S' : SeedData F' (m + 2) n),
      IsLabeledSeed K hmn' S' ∧
      (∀ (i : Fin m) (l : Fin n), S'.extExchangeMatrix (Fin.castLE (Nat.le_add_right m 2) i) l =
        S.extExchangeMatrix i l) ∧
      (∀ a b : Fin n, S'.extExchangeMatrix (Fin.castLE hmn' a) b =
        S.extExchangeMatrix (Fin.castLE hmn a) b) ∧
      (∀ l : Fin n, S'.extExchangeMatrix ⟨m, by omega⟩ l = if l = j then 1 else 0) ∧
      (∀ l : Fin n, S'.extExchangeMatrix ⟨m + 1, by omega⟩ l = if l = k then 1 else 0) ∧
      ∀ (s : List (Fin n)) (i : Fin m),
        (ClusterAlgebras.seedMutationSeq hmn' S' s).extCluster
            (Fin.castLE (Nat.le_add_right m 2) i) ∈ laurentSubring S'.extCluster →
        (ClusterAlgebras.seedMutationSeq hmn S s).extCluster i ∈ laurentSubring S.extCluster := by
  let R : Matrix (Fin 2) (Fin n) ℤ := Matrix.of ![Pi.single j 1, Pi.single k 1]
  have hS' := hS.augment hmn R hmn'
  haveI : CharZero F := Algebra.charZero_of_charZero K F
  haveI : CharZero (FractionRing (MvPolynomial (Fin 2) F)) :=
    Algebra.charZero_of_charZero K _
  refine ⟨_, inferInstance, inferInstance, S.augment R, hS',
    S.augment_extExchangeMatrix_castLE R _, S.augment_extExchangeMatrix_castLE_castLE R hmn hmn',
    fun l => ?_, fun l => ?_, fun s i h => ?_⟩
  · change (S.augment R).extExchangeMatrix (Fin.natAdd m 0) l = _
    simp [R, Pi.single_apply]
  · change (S.augment R).extExchangeMatrix (Fin.natAdd m 1) l = _
    simp [R, Pi.single_apply]
  · exact seedMutationSeq_extCluster_mem_laurentSubring_of_submatrix hmn hmn'
      (hS.algebraicIndependent_rat hmn) (hS'.algebraicIndependent_rat hmn')
      (Fin.castLE_injective _) (fun _ => rfl) (S.augment_extExchangeMatrix_submatrix R).symm s i h

end ClusterAlgebras

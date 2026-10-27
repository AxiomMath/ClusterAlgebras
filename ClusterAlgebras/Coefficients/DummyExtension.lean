/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.ClusterAlgebra

/-!
# Adding dummy frozen variables

Let `Σ` be a seed pattern of rank `n` in a field `F` over `K`, with `m × n` matrices, and let
`F' = F(z₁, …, z_d)` be a purely transcendental extension of `F`, the `z_e` algebraically
independent over `F`. Appending the `z_e` to every extended cluster of `Σ` as frozen
variables, and the same number of zero rows to every extended exchange matrix, gives a seed
pattern of rank `n` in `F'`, with `(m + d) × n` matrices. Its cluster algebra is
`𝒜 ⊗_K K[Z₁, …, Z_d]`, for `𝒜` the cluster algebra of `Σ`, through `a ⊗ f ↦ a f(z)`.

## Main definitions

* `ClusterAlgebras.SeedData.extendDummy`: the extension `(x̃, B̃)^{+z}` of seed data by a
  tuple `z`.
* `ClusterAlgebras.dummyExtensionTensorHom`: the `K`-algebra map `A ⊗_K K[Z] → F'`,
  `a ⊗ f ↦ a f(z)`, for a subalgebra `A` of `F`.
* `ClusterAlgebras.dummyExtensionTensorEquiv`: the isomorphism `𝒜 ⊗_K K[Z] ≃ 𝒜⁺`.

## Main results

* `ClusterAlgebras.seedMutation_extendDummy`: mutation commutes with the extension.
* `ClusterAlgebras.IsLabeledSeed.extendDummy`: the extension of a labeled seed is one.
* `ClusterAlgebras.IsSeedPattern.extendDummy`: the extended seeds form a seed pattern.
* `ClusterAlgebras.dummyExtensionTensorHom_injective`,
  `ClusterAlgebras.dummyExtensionTensorHom_range`: the map `a ⊗ f ↦ a f(z)` is injective,
  with image the cluster algebra of the extended pattern.
* `ClusterAlgebras.dummyExtensionTensorEquiv_tmul`: the isomorphism is `a ⊗ f ↦ a f(z)`.

## Implementation notes

* The extended cluster is `Fin.append x̃ z` and the extended exchange matrix is
  `Fin.append B̃ 0` read row by row, so the old rows are those `Fin.castAdd d i` and the new
  ones those `Fin.natAdd m e`. The definition needs no structure on the type of the entries.

* The field `F'` is an `F`-algebra (`[Algebra F F']`, `[IsScalarTower K F F']`) rather than
  a field containing `F`; the seeds of `Σ` are carried into `F'` along `algebraMap F F'`,
  written inline as `⟨algebraMap F F' ∘ x̃(t), B̃(t)⟩`.

* As in the rest of the library, `K` is not assumed of characteristic zero; nothing here
  uses it.

* Indices are `Fin m`, with mutable indices those of value below `n`; the inequality
  `n ≤ m + d` of the extended pattern is any proof, and the row `Fin.castLE _ k` of the
  extended matrix is `Fin.castAdd d (Fin.castLE hmn k)`.

* The isomorphism `dummyExtensionTensorEquiv` holds without `Σ` being a seed pattern and without
  `F' = F(z)`: it uses only that the `z_e` are algebraically independent over `F`. The map
  `a ⊗ f ↦ a f(z)` is defined into `F'` for any subalgebra `A` of `F`; for `A = 𝒜` its range is
  `𝒜⁺`, and `dummyExtensionTensorEquiv` is this map with its codomain cut down to `𝒜⁺`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*]
  [FWZ], §4.3, the remark on dummy coefficient variables.
-/

@[expose] public section

namespace ClusterAlgebras

open Function TensorProduct

/-- `Fin.castLE` into `Fin (m + d)` factors through `Fin.castLE` into `Fin m` followed by
`Fin.castAdd d`. -/
theorem extendDummy_castLE_eq_castAdd {m n d : ℕ} (hmn : n ≤ m) (h : n ≤ m + d) (k : Fin n) :
    Fin.castLE h k = Fin.castAdd d (Fin.castLE hmn k) :=
  rfl

section Defs

variable {F : Type*} {m n d : ℕ}

/-- The **extension of seed data by a tuple** `z = (z₁, …, z_d)`:
`(x̃, B̃)^{+z} = ((x₁, …, xₘ, z₁, …, z_d), B̃⁺)`, where the `(m + d) × n` matrix `B̃⁺` has the
rows of `B̃` followed by `d` zero rows. -/
@[cluster_algebras "def_dummy_extension"]
def SeedData.extendDummy (S : SeedData F m n) (z : Fin d → F) : SeedData F (m + d) n where
  extCluster := Fin.append S.extCluster z
  extExchangeMatrix := Matrix.of (Fin.append S.extExchangeMatrix 0)

variable (S : SeedData F m n) (z : Fin d → F)

/-- The first `m` entries of the extended cluster of `(x̃, B̃)^{+z}` are those of `x̃`. -/
@[simp]
theorem SeedData.extendDummy_extCluster_castAdd (i : Fin m) :
    (S.extendDummy z).extCluster (Fin.castAdd d i) = S.extCluster i :=
  Fin.append_left _ _ _

/-- The last `d` entries of the extended cluster of `(x̃, B̃)^{+z}` are those of `z`. -/
@[simp]
theorem SeedData.extendDummy_extCluster_natAdd (e : Fin d) :
    (S.extendDummy z).extCluster (Fin.natAdd m e) = z e :=
  Fin.append_right _ _ _

/-- The first `m` rows of `B̃⁺` are those of `B̃`. -/
@[simp]
theorem SeedData.extendDummy_extExchangeMatrix_castAdd (i : Fin m) (j : Fin n) :
    (S.extendDummy z).extExchangeMatrix (Fin.castAdd d i) j = S.extExchangeMatrix i j := by
  simp [SeedData.extendDummy]

/-- The last `d` rows of `B̃⁺` vanish. -/
@[simp]
theorem SeedData.extendDummy_extExchangeMatrix_natAdd (e : Fin d) (j : Fin n) :
    (S.extendDummy z).extExchangeMatrix (Fin.natAdd m e) j = 0 := by
  simp [SeedData.extendDummy]

/-- The cluster of `(x̃, B̃)^{+z}` is that of `(x̃, B̃)`. -/
@[simp]
theorem cluster_extendDummy (hmn : n ≤ m) (h : n ≤ m + d) :
    cluster h (S.extendDummy z) = cluster hmn S := by
  funext k
  simp [cluster, extendDummy_castLE_eq_castAdd hmn h]

/-- The cluster variables of `(x̃, B̃)^{+z}` are those of `(x̃, B̃)`. -/
@[simp]
theorem clusterVariables_extendDummy (hmn : n ≤ m) (h : n ≤ m + d) :
    clusterVariables h (S.extendDummy z) = clusterVariables hmn S := by
  rw [clusterVariables, cluster_extendDummy S z hmn h, clusterVariables]

/-- The frozen variables of `(x̃, B̃)^{+z}` are those of `(x̃, B̃)` together with the
entries of `z`. -/
theorem frozenVariables_extendDummy (hmn : n ≤ m) :
    frozenVariables (S.extendDummy z) = frozenVariables S ∪ Set.range z := by
  ext y
  simp only [frozenVariables, Set.mem_image, Set.mem_setOf_eq, Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, by simpa using hi, by simp⟩
    | right e => exact Or.inr ⟨e, by simp⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨e, rfl⟩)
    · exact ⟨Fin.castAdd d i, by simpa using hi, by simp⟩
    · exact ⟨Fin.natAdd m e, by rw [Fin.val_natAdd]; omega, by simp⟩

/-- Applying a function `f` to the extended cluster applies it to the frozen variables. -/
theorem frozenVariables_mk_comp {F' : Type*} (f : F → F') :
    frozenVariables (⟨f ∘ S.extCluster, S.extExchangeMatrix⟩ : SeedData F' m n) =
      f '' frozenVariables S :=
  Set.image_comp f S.extCluster _

/-- Applying a function `f` to the extended cluster applies it to the cluster variables. -/
theorem clusterVariables_mk_comp {F' : Type*} (f : F → F') (hmn : n ≤ m) :
    clusterVariables hmn (⟨f ∘ S.extCluster, S.extExchangeMatrix⟩ : SeedData F' m n) =
      f '' clusterVariables hmn S :=
  Set.range_comp f (cluster hmn S)

end Defs

section Mutation

variable {F : Type*} [Field F] {m n d : ℕ}

/-- Adding dummy frozen variables does not change the positive exchange monomial. -/
theorem exchangeMonomialPos_extendDummy (S : SeedData F m n) (z : Fin d → F) (k : Fin n) :
    exchangeMonomialPos (S.extendDummy z).extCluster (S.extendDummy z).extExchangeMatrix k =
      exchangeMonomialPos S.extCluster S.extExchangeMatrix k := by
  classical
  rw [exchangeMonomialPos_eq_prod, exchangeMonomialPos_eq_prod, Fin.prod_univ_add]
  simp

/-- Adding dummy frozen variables does not change the negative exchange monomial. -/
theorem exchangeMonomialNeg_extendDummy (S : SeedData F m n) (z : Fin d → F) (k : Fin n) :
    exchangeMonomialNeg (S.extendDummy z).extCluster (S.extendDummy z).extExchangeMatrix k =
      exchangeMonomialNeg S.extCluster S.extExchangeMatrix k := by
  classical
  rw [exchangeMonomialNeg_eq_prod, exchangeMonomialNeg_eq_prod, Fin.prod_univ_add]
  simp

/-- **Mutation commutes with adding dummy frozen variables**:
`μₖ((x̃, B̃)^{+z}) = (μₖ(x̃, B̃))^{+z}`. -/
theorem seedMutation_extendDummy (hmn : n ≤ m) (h : n ≤ m + d) (S : SeedData F m n)
    (z : Fin d → F) (k : Fin n) :
    seedMutation h (S.extendDummy z) k = (seedMutation hmn S k).extendDummy z := by
  classical
  refine SeedData.ext ?_ ?_
  · funext i
    induction i using Fin.addCases with
    | left i =>
      rw [SeedData.extendDummy_extCluster_castAdd]
      simp only [seedMutation, exchangeMonomialPos_extendDummy, exchangeMonomialNeg_extendDummy,
        extendDummy_castLE_eq_castAdd hmn h]
      by_cases hi : i = Fin.castLE hmn k
      · subst hi
        simp
      · rw [update_of_ne (fun h' => hi (Fin.castAdd_injective _ _ h')), update_of_ne hi,
          SeedData.extendDummy_extCluster_castAdd]
    | right e =>
      simp only [seedMutation, exchangeMonomialPos_extendDummy, exchangeMonomialNeg_extendDummy,
        extendDummy_castLE_eq_castAdd hmn h]
      rw [update_of_ne (Fin.ne_of_val_ne (by simp; omega)),
        SeedData.extendDummy_extCluster_natAdd, SeedData.extendDummy_extCluster_natAdd]
  · ext i j
    induction i using Fin.addCases <;>
      simp [seedMutation, matrixMutation, extendDummy_castLE_eq_castAdd hmn h]

/-- **Mutation commutes with a ring homomorphism applied to the extended cluster**. -/
theorem seedMutation_mk_ringHom_comp {F' : Type*} [Field F'] (f : F →+* F') (hmn : n ≤ m)
    (S : SeedData F m n) (k : Fin n) :
    seedMutation hmn ⟨f ∘ S.extCluster, S.extExchangeMatrix⟩ k =
      ⟨f ∘ (seedMutation hmn S k).extCluster, (seedMutation hmn S k).extExchangeMatrix⟩ := by
  classical
  refine SeedData.ext ?_ rfl
  simp [seedMutation, exchangeMonomialPos, exchangeMonomialNeg, map_prod, map_zpow₀,
    Function.comp_update, map_div₀, map_add]

end Mutation

section Pattern

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] {m n d : ℕ}

/-- **Adding dummy frozen variables to a labeled seed gives a labeled seed.** If `(x̃, B̃)` is a
labeled seed in `F` over `K` and the `z_e` are algebraically independent over `F` and generate
`F'` over `F`, then `(x̃, B̃)^{+z}` is a labeled seed in `F'` over `K`. -/
theorem IsLabeledSeed.extendDummy (hmn : n ≤ m) (h : n ≤ m + d) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) {z : Fin d → F'} (hz : AlgebraicIndependent F z)
    (hzF : IntermediateField.adjoin F (Set.range z) = ⊤) :
    IsLabeledSeed K h
      (SeedData.extendDummy ⟨algebraMap F F' ∘ S.extCluster, S.extExchangeMatrix⟩ z) := by
  obtain ⟨⟨hind, htop⟩, hB⟩ := hS
  set x := S.extCluster
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hfun : Fin.append (algebraMap F F' ∘ x) z =
        Sum.elim z (algebraMap F F' ∘ x) ∘ (Equiv.sumComm _ _ ∘ finSumFinEquiv.symm) := by
      funext i
      induction i using Fin.addCases <;> simp
    change AlgebraicIndependent K (Fin.append (algebraMap F F' ∘ x) z)
    rw [hfun]
    exact (hind.sumElim_comp hz).comp _
      ((Equiv.sumComm _ _).injective.comp finSumFinEquiv.symm.injective)
  · set L := IntermediateField.adjoin K
      (Set.range (SeedData.extendDummy ⟨algebraMap F F' ∘ x, S.extExchangeMatrix⟩ z).extCluster)
    have hF : ∀ a : F, algebraMap F F' a ∈ L := by
      intro a
      have ha : IsScalarTower.toAlgHom K F F' a ∈
          (IntermediateField.adjoin K (Set.range x)).map (IsScalarTower.toAlgHom K F F') :=
        ⟨a, htop ▸ IntermediateField.mem_top, rfl⟩
      rw [IntermediateField.adjoin_map, ← Set.range_comp] at ha
      refine IntermediateField.adjoin_le_iff.2 ?_ ha
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨Fin.castAdd d i, by simp⟩
    have hzL : IntermediateField.adjoin F (Set.range z) ≤ L.toSubfield.toIntermediateField hF :=
      IntermediateField.adjoin_le_iff.2 <| Set.range_subset_iff.2 fun e =>
        show z e ∈ L from IntermediateField.subset_adjoin _ _ ⟨Fin.natAdd m e, by simp⟩
    refine eq_top_iff.2 fun y _ => show y ∈ L.toSubfield.toIntermediateField hF from hzL ?_
    rw [hzF]
    exact IntermediateField.mem_top
  · have hsub : (SeedData.extendDummy ⟨algebraMap F F' ∘ x, S.extExchangeMatrix⟩
        z).extExchangeMatrix.submatrix (Fin.castLE h) id =
          S.extExchangeMatrix.submatrix (Fin.castLE hmn) id := by
      ext i j
      simp [extendDummy_castLE_eq_castAdd hmn h]
    rwa [ExtSkewSymmetrizable, hsub]

/-- **Dummy frozen variables give a seed pattern.** If `Σ` is a seed pattern of rank `n` in `F`
over `K` and `z₁, …, z_d ∈ F'` are algebraically independent over `F` with `F' = F(z)`, then
`t ↦ Σ(t)^{+z}` is a seed pattern of rank `n` in `F'` over `K`. -/
@[cluster_algebras "lem_dummy_extension_pattern"]
theorem IsSeedPattern.extendDummy (hmn : n ≤ m) {P : RegularTree n → SeedData F m n}
    (hP : IsSeedPattern K hmn P) {z : Fin d → F'} (hz : AlgebraicIndependent F z)
    (hzF : IntermediateField.adjoin F (Set.range z) = ⊤) :
    IsSeedPattern K (hmn.trans (Nat.le_add_right m d)) fun t =>
      SeedData.extendDummy ⟨algebraMap F F' ∘ (P t).extCluster, (P t).extExchangeMatrix⟩ z := by
  refine ⟨fun t => (hP.1 t).extendDummy hmn _ hz hzF, fun k t t' htt' => ?_⟩
  simp only
  rw [hP.2 k t t' htt', seedMutation_extendDummy hmn, seedMutation_mk_ringHom_comp]

end Pattern

section Algebra

variable (K : Type*) {F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] {m n d : ℕ}

/-- The cluster algebra of a seed pattern is generated over `K` by its frozen variables and its
cluster variables. -/
theorem clusterAlgebra_eq_adjoin_frozenVariables_union (hmn : n ≤ m)
    (P : RegularTree n → SeedData F m n) :
    clusterAlgebra K hmn P = Algebra.adjoin K
      ((⋃ t, frozenVariables (P t)) ∪ ⋃ t, clusterVariables hmn (P t)) := by
  refine le_antisymm (Algebra.adjoin_le (Set.union_subset ?_ ?_))
    (Algebra.adjoin_mono (Set.union_subset_union_left _ Algebra.subset_adjoin))
  · exact Algebra.adjoin_mono Set.subset_union_left
  · exact Set.subset_union_right.trans Algebra.subset_adjoin

/-- The `K`-algebra map `A ⊗_K K[Z₁, …, Z_d] → F'`, `a ⊗ f ↦ a f(z₁, …, z_d)`, for a
subalgebra `A` of `F`. -/
noncomputable def dummyExtensionTensorHom (A : Subalgebra K F) (z : Fin d → F') :
    A ⊗[K] MvPolynomial (Fin d) K →ₐ[K] F' :=
  Algebra.TensorProduct.productMap ((IsScalarTower.toAlgHom K F F').comp A.val)
    (MvPolynomial.aeval z)

/-- The map `dummyExtensionTensorHom` sends `a ⊗ f` to `a f(z)`. -/
@[simp]
theorem dummyExtensionTensorHom_tmul (A : Subalgebra K F) (z : Fin d → F') (a : A)
    (f : MvPolynomial (Fin d) K) :
    dummyExtensionTensorHom K A z (a ⊗ₜ f) = algebraMap F F' a * MvPolynomial.aeval z f :=
  rfl

variable {K}

/-- The map `a ⊗ f ↦ a f(z)` is injective when the `z_e` are algebraically independent over
`F`. -/
theorem dummyExtensionTensorHom_injective (A : Subalgebra K F) {z : Fin d → F'}
    (hz : AlgebraicIndependent F z) : Injective (dummyExtensionTensorHom K A z) := by
  have key : ∀ w, dummyExtensionTensorHom K A z w = MvPolynomial.aeval z
      (MvPolynomial.map (A.val : A →+* F) (MvPolynomial.algebraTensorAlgEquiv K A w)) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      rw [dummyExtensionTensorHom_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul,
        MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, map_mul,
        MvPolynomial.aeval_C]
      congr 1
      exact (MvPolynomial.aeval_map_algebraMap F z f).symm
    | add w w' hw hw' => rw [map_add, hw, hw', map_add, map_add, map_add]
  intro w w' hww'
  rw [key, key] at hww'
  exact EquivLike.injective _ (MvPolynomial.map_injective _ Subtype.val_injective
    (algebraicIndependent_iff_injective_aeval.1 hz hww'))

variable (K) in
/-- The image of the map `a ⊗ f ↦ a f(z)` on `𝒜 ⊗_K K[Z]`, for `𝒜` the cluster algebra of
`P`, is the cluster algebra of `t ↦ P(t)^{+z}`. -/
theorem dummyExtensionTensorHom_range (hmn : n ≤ m) (h : n ≤ m + d)
    (P : RegularTree n → SeedData F m n) (z : Fin d → F') :
    (dummyExtensionTensorHom K (clusterAlgebra K hmn P) z).range = clusterAlgebra K h fun t =>
      SeedData.extendDummy ⟨algebraMap F F' ∘ (P t).extCluster, (P t).extExchangeMatrix⟩ z := by
  have : Nonempty (RegularTree n) := ⟨RegularTree.root⟩
  rw [dummyExtensionTensorHom, Algebra.TensorProduct.productMap_range, MvPolynomial.aeval_range,
    AlgHom.range_comp, Subalgebra.range_val, clusterAlgebra_eq_adjoin_frozenVariables_union,
    clusterAlgebra_eq_adjoin_frozenVariables_union, AlgHom.map_adjoin, ← Algebra.adjoin_union]
  congr 1
  simp only [frozenVariables_extendDummy _ z hmn, clusterVariables_extendDummy _ z hmn h,
    frozenVariables_mk_comp, clusterVariables_mk_comp]
  rw [Set.image_union, Set.image_iUnion, Set.image_iUnion, ← Set.iUnion_union,
    Set.union_right_comm]
  rfl

variable (K) in
/-- **Dummy frozen variables tensor the cluster algebra with a polynomial ring.** Let `𝒜` be
the cluster algebra of `P` and `𝒜⁺` that of `t ↦ P(t)^{+z}`, for `z₁, …, z_d` algebraically
independent over `F`. Then `a ⊗ f ↦ a f(z₁, …, z_d)` is an isomorphism of `K`-algebras
`𝒜 ⊗_K K[Z₁, …, Z_d] ≃ 𝒜⁺` (`dummyExtensionTensorEquiv_tmul`). -/
@[cluster_algebras "lem_dummy_extension_algebra"]
noncomputable def dummyExtensionTensorEquiv (hmn : n ≤ m) (h : n ≤ m + d)
    (P : RegularTree n → SeedData F m n) {z : Fin d → F'} (hz : AlgebraicIndependent F z) :
    clusterAlgebra K hmn P ⊗[K] MvPolynomial (Fin d) K ≃ₐ[K] clusterAlgebra K h fun t =>
      SeedData.extendDummy ⟨algebraMap F F' ∘ (P t).extCluster, (P t).extExchangeMatrix⟩ z :=
  (AlgEquiv.ofInjective _ (dummyExtensionTensorHom_injective _ hz)).trans
    (Subalgebra.equivOfEq _ _ (dummyExtensionTensorHom_range K hmn h P z))

/-- The isomorphism `dummyExtensionTensorEquiv` sends `a ⊗ f` to `a f(z₁, …, z_d)`. -/
@[cluster_algebras "lem_dummy_extension_algebra", simp]
theorem dummyExtensionTensorEquiv_tmul (hmn : n ≤ m) (h : n ≤ m + d)
    (P : RegularTree n → SeedData F m n) {z : Fin d → F'} (hz : AlgebraicIndependent F z)
    (a : clusterAlgebra K hmn P) (f : MvPolynomial (Fin d) K) :
    (dummyExtensionTensorEquiv K hmn h P hz (a ⊗ₜ f) : F') =
      algebraMap F F' a * MvPolynomial.aeval z f :=
  rfl

end Algebra

end ClusterAlgebras

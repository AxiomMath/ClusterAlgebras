/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Cartan.Counterpart
public import ClusterAlgebras.Coefficients.ZSpanRescaling
public import ClusterAlgebras.FiniteType.Basic

/-!
# Relabelling seeds, changing the coefficients, and reference matrices

This file develops the matrix and seed tools used for the types `E₆`, `E₇`, `E₈`. A permutation `σ`
of the mutable indices relabels an extended exchange matrix and a seed; a seed pattern through a
relabelled seed has the relabelled seeds of the original pattern, the same cluster variables and
the same clusters. Coincidences of cluster variables transfer between patterns with the same
exchange matrices under the `ℤ`-span condition, and a transfer of coincidences bounds the numbers
of cluster variables and of clusters. A *reference matrix* for a Dynkin symbol `X` is a matrix to
which every exchange matrix with Cartan counterpart `C(X)` can be mutated, up to relabelling; every
pattern of type `X` has a seed whose exchange matrix is a relabelling of it.

## Main definitions

* `ClusterAlgebras.relabelMatrix hmn B σ`: the relabelling `B̃^σ`, `(B̃^σ)ᵢⱼ = b_{σ̂(i) σ(j)}`.
* `ClusterAlgebras.SeedData.relabel hmn S σ`: the relabelling `(x̃, B̃)^σ` of a seed.
* `ClusterAlgebras.IsReferenceMatrix X B₀`: `B₀` is a reference matrix for `X`.

## Main statements

* `ClusterAlgebras.IsSeedPattern.range_eq_of_apply_eq_relabel`: relabelling a seed pattern.
* `ClusterAlgebras.IsSeedPattern.cluster_eq_of_cluster_eq_of_zSpanCondition`: coincidences of
  cluster variables transfer under the `ℤ`-span condition.
* `ClusterAlgebras.encard_patternClusterVariables_le_of_cluster_eq`: comparing the numbers of
  cluster variables and of clusters.
* `ClusterAlgebras.SkewSymmetrizable.eq_neg_of_isSymm_cartanCounterpart`: a skew-symmetrizable
  matrix with symmetric Cartan counterpart is skew-symmetric.
* `ClusterAlgebras.IsSeedPattern.exists_principalPart_eq_relabelMatrix`: a pattern of type `X`
  has a seed whose exchange matrix is a relabelled reference matrix.

## Implementation notes

* Indices are `Fin m`, so the mutable indices `1, …, n` are `0, …, n - 1`. The extension `σ̂`
  of a permutation `σ` of the mutable indices is `Equiv.Perm.extendMutable`, and the relabelling
  is reindexing along the reindexing map `ReindexingMap.ofMutablePerm hmn σ`, so the API for
  `matrixReindex` and `SeedData.reindex` applies unchanged. The composite `σ ∘ τ` is the product
  `σ * τ` of `Equiv.Perm`, and `σ(s)` for a sequence `s` is `s.map σ`.
* For `m = n` the relabelling is the simultaneous permutation `B.submatrix σ σ`
  (`relabelMatrix_self`).
* The basic properties of relabelling that do not need their hypotheses are stated without them:
  `A(B^σ) = A(B)^σ` holds for every matrix, and relabelling commutes with seed mutation (along
  sequences) for every seed data, as `seedMutation` is total and `σ̂` is closed for every matrix.
* A reference matrix for `X` is a matrix indexed by `Fin X.rank`, and the results about
  patterns of type `X` are stated for patterns of rank `X.rank`. A pattern of type `[X]` has
  rank `X.rank` anyway, and for a concrete symbol `X.rank` reduces to a numeral.
* The comparison of counts (`encard_patternClusterVariables_le_of_cluster_eq`) uses no
  property of seed patterns, so it is stated for arbitrary assignments of seed data, and its
  two inequalities are stated without the finiteness hypothesis (they hold in `ℕ∞` in general).
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {m n : ℕ}

/-! ### Relabelling -/

section Relabel

variable {α : Type*}

/-- **Relabelling by a permutation.** For a permutation `σ` of the mutable indices `Fin n`, with
extension `σ̂ = σ.extendMutable hmn` to `Fin m` (equal to `σ` on the mutable indices and to the
identity on the frozen ones), the relabelling of an `m × n` matrix `B̃` is the matrix `B̃^σ` with
`(B̃^σ)ᵢⱼ = b_{σ̂(i) σ(j)}`: the reindexing of `B̃` along the reindexing map `σ̂`. -/
@[cluster_algebras "def_exc_relabelling"]
def relabelMatrix (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) α) (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin m) (Fin n) α :=
  matrixReindex hmn B (ReindexingMap.ofMutablePerm hmn σ)

/-- The entries of a relabelled matrix: `(B̃^σ)ᵢⱼ = b_{σ̂(i) σ(j)}`. -/
@[cluster_algebras "def_exc_relabelling"]
theorem relabelMatrix_apply (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) α)
    (σ : Equiv.Perm (Fin n)) (i : Fin m) (j : Fin n) :
    relabelMatrix hmn B σ i j = B (σ.extendMutable hmn i) (σ j) := by
  simp [relabelMatrix]

/-- Relabelling by the identity permutation does nothing: `B̃^1 = B̃`. -/
theorem relabelMatrix_one (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) α) :
    relabelMatrix hmn B 1 = B := by
  ext i j
  simp only [relabelMatrix_apply, Equiv.Perm.extendMutable_one, Equiv.Perm.one_apply]

/-- **Relabelling of a seed.** The relabelling `(x̃, B̃)^σ = (x̃, B̃)^{σ̂}` of a seed by a
permutation `σ` of the mutable indices: its extended cluster is `(x_{σ̂(1)}, …, x_{σ̂(m)})` and
its extended exchange matrix is `B̃^σ`. -/
@[cluster_algebras "def_exc_relabelling"]
def SeedData.relabel {F : Type*} (hmn : n ≤ m) (S : SeedData F m n) (σ : Equiv.Perm (Fin n)) :
    SeedData F m n :=
  S.reindex hmn (ReindexingMap.ofMutablePerm hmn σ)

/-- The extended cluster of a relabelled seed: its `i`th entry is `x_{σ̂(i)}`. -/
@[cluster_algebras "def_exc_relabelling"]
theorem SeedData.relabel_extCluster {F : Type*} (hmn : n ≤ m) (S : SeedData F m n)
    (σ : Equiv.Perm (Fin n)) (i : Fin m) :
    (S.relabel hmn σ).extCluster i = S.extCluster (σ.extendMutable hmn i) :=
  rfl

/-- The extended exchange matrix of a relabelled seed is the relabelled matrix. -/
@[cluster_algebras "def_exc_relabelling"]
theorem SeedData.relabel_extExchangeMatrix {F : Type*} (hmn : n ≤ m) (S : SeedData F m n)
    (σ : Equiv.Perm (Fin n)) :
    (S.relabel hmn σ).extExchangeMatrix = relabelMatrix hmn S.extExchangeMatrix σ :=
  rfl

/-- For `m = n` the extension of `σ` is `σ` itself. -/
@[simp]
theorem _root_.Equiv.Perm.extendMutable_self (σ : Equiv.Perm (Fin n)) :
    σ.extendMutable le_rfl = σ := by
  ext i
  rw [Equiv.Perm.extendMutable_apply_of_lt le_rfl σ i.2]
  rfl

/-- For `m = n` the relabelling of a square matrix is the simultaneous permutation
`(b_{σ(i) σ(j)})` of its rows and columns. -/
theorem relabelMatrix_self (B : Matrix (Fin n) (Fin n) α) (σ : Equiv.Perm (Fin n)) :
    relabelMatrix le_rfl B σ = B.submatrix σ σ := by
  ext i j
  rw [relabelMatrix_apply, Equiv.Perm.extendMutable_self, submatrix_apply]

end Relabel

/-! ### Basic properties of relabelling -/

section Basic

variable {R : Type*} [CommRing R]

/-- **Basic properties of relabelling**, (a): the reindexing map `σ̂` is closed for every
`m × n` matrix, every index being in its image. That `σ̂` is a reindexing map from `(m, n)` to
`(m, n)` is `ReindexingMap.ofMutablePerm`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem ReindexingMap.isClosedFor_ofMutablePerm {β : Type*} [Zero β] (hmn : n ≤ m)
    (σ : Equiv.Perm (Fin n)) (B : Matrix (Fin m) (Fin n) β) :
    (ReindexingMap.ofMutablePerm hmn σ).IsClosedFor hmn B :=
  ReindexingMap.isClosedFor_of_surjective (σ.extendMutable hmn).surjective hmn B

/-- **Basic properties of relabelling**, (a): the extension of `σ ∘ τ` is `σ̂ ∘ τ̂`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem extendMutable_mul' (hmn : n ≤ m) (σ τ : Equiv.Perm (Fin n)) :
    (σ * τ).extendMutable hmn = σ.extendMutable hmn * τ.extendMutable hmn :=
  Equiv.Perm.extendMutable_mul hmn σ τ

/-- **Basic properties of relabelling**, (b): `(B̃^σ)^τ = B̃^{σ ∘ τ}`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem relabelMatrix_relabelMatrix {α : Type*} (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) α)
    (σ τ : Equiv.Perm (Fin n)) :
    relabelMatrix hmn (relabelMatrix hmn B σ) τ = relabelMatrix hmn B (σ * τ) := by
  ext i j
  simp only [relabelMatrix_apply, Equiv.Perm.extendMutable_mul, Equiv.Perm.mul_apply]

/-- **Basic properties of relabelling**, (b): `(B̃^σ)^{σ⁻¹} = B̃`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem relabelMatrix_relabelMatrix_inv {α : Type*} (hmn : n ≤ m)
    (B : Matrix (Fin m) (Fin n) α) (σ : Equiv.Perm (Fin n)) :
    relabelMatrix hmn (relabelMatrix hmn B σ) σ⁻¹ = B := by
  rw [relabelMatrix_relabelMatrix, mul_inv_cancel, relabelMatrix_one]

/-- **Basic properties of relabelling**, (b): `((x̃, B̃)^σ)^τ = (x̃, B̃)^{σ ∘ τ}`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem SeedData.relabel_relabel {F : Type*} (hmn : n ≤ m) (S : SeedData F m n)
    (σ τ : Equiv.Perm (Fin n)) : (S.relabel hmn σ).relabel hmn τ = S.relabel hmn (σ * τ) := by
  refine SeedData.ext (funext fun i => ?_) (relabelMatrix_relabelMatrix hmn _ σ τ)
  simp only [SeedData.relabel_extCluster, Equiv.Perm.extendMutable_mul, Equiv.Perm.mul_apply]

/-- **Basic properties of relabelling**, (b): `((x̃, B̃)^σ)^{σ⁻¹} = (x̃, B̃)`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem SeedData.relabel_relabel_inv {F : Type*} (hmn : n ≤ m) (S : SeedData F m n)
    (σ : Equiv.Perm (Fin n)) : (S.relabel hmn σ).relabel hmn σ⁻¹ = S := by
  refine SeedData.ext (funext fun i => ?_) (relabelMatrix_relabelMatrix_inv hmn _ σ)
  rw [SeedData.relabel_relabel, mul_inv_cancel, SeedData.relabel_extCluster,
    Equiv.Perm.extendMutable_one, Equiv.Perm.one_apply]

/-- **Basic properties of relabelling**, (c): the principal part of `B̃^σ` is `B^σ`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem principalPart_relabelMatrix {α : Type*} (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) α)
    (σ : Equiv.Perm (Fin n)) :
    principalPart hmn (relabelMatrix hmn B σ) = relabelMatrix le_rfl (principalPart hmn B) σ := by
  ext i j
  simp only [principalPart, submatrix_apply, id, relabelMatrix_apply,
    Equiv.Perm.extendMutable_castLE, Equiv.Perm.extendMutable_self]

/-- **Basic properties of relabelling**, (c): if `B̃` is extended skew-symmetrizable, so is
`B̃^σ`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem ExtSkewSymmetrizable.relabelMatrix (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) R}
    (hB : ExtSkewSymmetrizable hmn B) (σ : Equiv.Perm (Fin n)) :
    ExtSkewSymmetrizable hmn (ClusterAlgebras.relabelMatrix hmn B σ) :=
  hB.matrixReindex hmn hmn _

/-- **Basic properties of relabelling**, (c): `A(B^σ) = A(B)^σ`, for every square matrix
`B`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem cartanCounterpart_relabelMatrix (B : Matrix (Fin n) (Fin n) ℤ) (σ : Equiv.Perm (Fin n)) :
    cartanCounterpart (relabelMatrix le_rfl B σ) =
      relabelMatrix le_rfl (cartanCounterpart B) σ := by
  ext i j
  simp only [relabelMatrix_self, cartanCounterpart, submatrix_apply, of_apply,
    σ.injective.eq_iff]

/-- **Basic properties of relabelling**, (d): if the rows of `B̃` span `ℤⁿ`, so do the rows of
`B̃^σ`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem span_range_relabelMatrix (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) ℤ}
    (hB : Submodule.span ℤ (Set.range B) = ⊤) (σ : Equiv.Perm (Fin n)) :
    Submodule.span ℤ (Set.range (relabelMatrix hmn B σ)) = ⊤ := by
  have h : relabelMatrix hmn B σ =
      (LinearEquiv.funCongrLeft ℤ ℤ σ) ∘ B ∘ σ.extendMutable hmn := by
    ext i j
    simp [relabelMatrix_apply, LinearEquiv.funCongrLeft_apply]
  rw [h, Set.range_comp, (σ.extendMutable hmn).surjective.range_comp,
    ← LinearEquiv.coe_toLinearMap, Submodule.span_image, hB, Submodule.map_top,
    LinearEquiv.range]

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Basic properties of relabelling**, (e): a relabelled labeled seed is a labeled seed in the
same field. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem IsLabeledSeed.relabel (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S)
    (σ : Equiv.Perm (Fin n)) : IsLabeledSeed K hmn (S.relabel hmn σ) := by
  refine ⟨⟨hS.1.1.comp _ (σ.extendMutable hmn).injective, ?_⟩, hS.2.relabelMatrix hmn σ⟩
  rw [show (S.relabel hmn σ).extCluster = S.extCluster ∘ σ.extendMutable hmn from rfl,
    (σ.extendMutable hmn).surjective.range_comp]
  exact hS.1.2

omit [Field F] in
/-- **Basic properties of relabelling**, (e): a relabelled seed has the same frozen variables. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem SeedData.frozenVariables_relabel (hmn : n ≤ m) (S : SeedData F m n)
    (σ : Equiv.Perm (Fin n)) : frozenVariables (S.relabel hmn σ) = frozenVariables S := by
  ext x
  simp only [frozenVariables, Set.mem_image, Set.mem_setOf_eq, SeedData.relabel_extCluster]
  refine exists_congr fun i => and_congr_right fun hi => ?_
  rw [Equiv.Perm.extendMutable_apply_of_le hmn σ hi]

omit [Field F] in
/-- **Basic properties of relabelling**, (e): the cluster of `(x̃, B̃)^σ` is
`(x_{σ(1)}, …, x_{σ(n)})`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem SeedData.cluster_relabel (hmn : n ≤ m) (S : SeedData F m n) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : cluster hmn (S.relabel hmn σ) i = cluster hmn S (σ i) :=
  SeedData.cluster_reindex_ofMutablePerm hmn S σ i

omit [Field F] in
/-- **Basic properties of relabelling**, (e): a relabelled seed has the same cluster
variables. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem SeedData.clusterVariables_relabel (hmn : n ≤ m) (S : SeedData F m n)
    (σ : Equiv.Perm (Fin n)) : clusterVariables hmn (S.relabel hmn σ) = clusterVariables hmn S := by
  have h : cluster hmn (S.relabel hmn σ) = cluster hmn S ∘ σ :=
    funext (SeedData.cluster_relabel hmn S σ)
  rw [clusterVariables, clusterVariables, h, σ.surjective.range_comp]

/-- **Basic properties of relabelling**, (f): `μ_s(B̃^σ) = (μ_{σ(s)}(B̃))^σ` for every finite
sequence `s`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem matrixMutationList_relabelMatrix [LinearOrder R] (hmn : n ≤ m)
    (B : Matrix (Fin m) (Fin n) R) (σ : Equiv.Perm (Fin n)) (s : List (Fin n)) :
    matrixMutationList hmn (relabelMatrix hmn B σ) s =
      relabelMatrix hmn (matrixMutationList hmn B (s.map σ)) σ := by
  rw [relabelMatrix, matrixMutationList_matrixReindex hmn hmn,
    ReindexingMap.col_ofMutablePerm, relabelMatrix]

/-- **Basic properties of relabelling**, (f): `μ_k((x̃, B̃)^σ) = (μ_{σ(k)}(x̃, B̃))^σ`, for all
seed data, with no hypothesis `x_{σ(k)} ≠ 0`. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem seedMutation_relabel (hmn : n ≤ m) (S : SeedData F m n) (σ : Equiv.Perm (Fin n))
    (k : Fin n) :
    seedMutation hmn (S.relabel hmn σ) k = (seedMutation hmn S (σ k)).relabel hmn σ := by
  have h := seedMutation_reindex hmn hmn S
    (ReindexingMap.isClosedFor_ofMutablePerm hmn σ S.extExchangeMatrix) k
  rwa [ReindexingMap.col_ofMutablePerm] at h

/-- **Basic properties of relabelling**, (f): `μ_s((x̃, B̃)^σ) = (μ_{σ(s)}(x̃, B̃))^σ` for every
finite sequence `s`, for all seed data. -/
@[cluster_algebras "lem_exc_relabelling_basic"]
theorem seedMutationSeq_relabel (hmn : n ≤ m) (S : SeedData F m n) (σ : Equiv.Perm (Fin n))
    (s : List (Fin n)) :
    seedMutationSeq hmn (S.relabel hmn σ) s = (seedMutationSeq hmn S (s.map σ)).relabel hmn σ := by
  have h := seedMutationSeq_reindex hmn hmn S
    (ReindexingMap.isClosedFor_ofMutablePerm hmn σ S.extExchangeMatrix) s
  rwa [ReindexingMap.col_ofMutablePerm] at h

end Basic

/-! ### Relabelling a seed pattern -/

section Pattern

variable {K F F' : Type*} [Field K] [Field F] [Algebra K F] [Field F'] [Algebra K F'] {m' : ℕ}

/-- **Relabelling a seed pattern**, existence: there is a seed pattern `Π` with
`Π(t₀) = Σ(t₀)^σ`. -/
@[cluster_algebras "lem_exc_relabel_pattern"]
theorem IsSeedPattern.exists_apply_eq_relabel [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t₀ : RegularTree n)
    (σ : Equiv.Perm (Fin n)) :
    ∃ P' : RegularTree n → SeedData F m n, IsSeedPattern K hmn P' ∧ P' t₀ = (P t₀).relabel hmn σ :=
  exists_isSeedPattern hmn t₀ ((hP.1 t₀).relabel hmn σ)

omit [Field K] [Field F] [Algebra K F] in
/-- The clusters of an assignment of seed data are the images of its seeds under taking cluster
variables. -/
private theorem relabel_patternClusters_eq_image (hmn : n ≤ m)
    (P : RegularTree n → SeedData F m n) :
    patternClusters hmn P = clusterVariables hmn '' Set.range P :=
  Set.range_comp (clusterVariables hmn) P

/-- **Relabelling a seed pattern.** If `Π` is a seed pattern with `Π(t₀) = Σ(t₀)^σ`, then the
seeds of `Π` are the relabellings `Σ(u)^σ` of the seeds of `Σ`; consequently `Π` and `Σ` have
the same cluster variables and the same clusters, and `Π` is of finite type if and only if `Σ`
is. -/
@[cluster_algebras "lem_exc_relabel_pattern"]
theorem IsSeedPattern.range_eq_of_apply_eq_relabel [CharZero K] (hmn : n ≤ m)
    {P P' : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hP' : IsSeedPattern K hmn P') {t₀ : RegularTree n} {σ : Equiv.Perm (Fin n)}
    (h : P' t₀ = (P t₀).relabel hmn σ) :
    Set.range P' = Set.range (fun u => (P u).relabel hmn σ) ∧
      patternClusterVariables hmn P' = patternClusterVariables hmn P ∧
      patternClusters hmn P' = patternClusters hmn P ∧
      (IsFiniteType P' ↔ IsFiniteType P) := by
  have hrange : Set.range P' = Set.range (fun u => (P u).relabel hmn σ) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨u, rfl⟩
      obtain ⟨s, hs⟩ := hP'.exists_seedMutationSeq_eq hmn t₀ u
      obtain ⟨u', hu'⟩ := hP.seedMutationSeq_mem_range hmn t₀ (s.map σ)
      refine ⟨u', ?_⟩
      dsimp only
      rw [hs, h, seedMutationSeq_relabel, ← hu']
    · rintro _ ⟨u, rfl⟩
      obtain ⟨s, hs⟩ := hP.exists_seedMutationSeq_eq hmn t₀ u
      obtain ⟨u', hu'⟩ := hP'.seedMutationSeq_mem_range hmn t₀ (s.map ⇑(σ⁻¹ : Equiv.Perm (Fin n)))
      refine ⟨u', ?_⟩
      have hs' : (s.map ⇑(σ⁻¹ : Equiv.Perm (Fin n))).map σ = s := by simp [List.map_map]
      dsimp only
      rw [hu', h, seedMutationSeq_relabel, hs', hs]
  have hcl : patternClusters hmn P' = patternClusters hmn P := by
    rw [relabel_patternClusters_eq_image, relabel_patternClusters_eq_image, hrange,
      ← Set.range_comp, ← Set.range_comp]
    congr 1
    funext u
    exact SeedData.clusterVariables_relabel hmn (P u) σ
  refine ⟨hrange, ?_, hcl, ?_⟩
  · simp only [patternClusterVariables, ← Set.sUnion_range]
    exact congrArg Set.sUnion hcl
  · change (Set.range P').Finite ↔ (Set.range P).Finite
    rw [hrange, show (fun u => (P u).relabel hmn σ) = (fun S => S.relabel hmn σ) ∘ P from rfl,
      Set.range_comp, Set.finite_image_iff (Function.LeftInverse.injective
        (g := fun S => S.relabel hmn σ⁻¹) fun S => S.relabel_relabel_inv hmn σ).injOn]

/-- **One common exchange matrix gives all of them.** If the seeds `Σ(t₀)` and `Σ'(t₀)` of two
seed patterns of rank `n`, in fields `F` and `F'` and with matrices of sizes `m × n` and
`m' × n`, have the same exchange matrix, then `Σ(t)` and `Σ'(t)` have the same exchange matrix
for every `t`. This is `IsSeedPattern.principalPart_eq_of_principalPart_eq`. -/
@[cluster_algebras "lem_exc_same_principal_parts"]
theorem IsSeedPattern.principalPart_eq_of_principalPart_eq_at (hmn : n ≤ m) (hm' : n ≤ m')
    {P : RegularTree n → SeedData F m n} {P' : RegularTree n → SeedData F' m' n}
    (hP : IsSeedPattern K hmn P) (hP' : IsSeedPattern K hm' P') {t₀ : RegularTree n}
    (h₀ : principalPart hmn (P t₀).extExchangeMatrix = principalPart hm' (P' t₀).extExchangeMatrix)
    (t : RegularTree n) :
    principalPart hmn (P t).extExchangeMatrix = principalPart hm' (P' t).extExchangeMatrix :=
  hP.principalPart_eq_of_principalPart_eq hmn hm' hP' h₀ t

/-- **Coincidences of cluster variables transfer under the `ℤ`-span condition.** Let `Σ = P` and
`Σ̄ = P'` be seed patterns of rank `n` in `F` and `F'` over `K`, and `t₀` a vertex at which they
have the same exchange matrix and `B̃̄(t₀)` satisfies the `ℤ`-span condition with respect to
`B̃(t₀)`. If `x_{i;t} = x_{j;t'}`, then `x̄_{i;t} = x̄_{j;t'}`. -/
@[cluster_algebras "lem_exc_zspan_variables"]
theorem IsSeedPattern.cluster_eq_of_cluster_eq_of_zSpanCondition [CharZero K] (hmn : n ≤ m)
    (hm' : n ≤ m') {P : RegularTree n → SeedData F m n} {P' : RegularTree n → SeedData F' m' n}
    (hP : IsSeedPattern K hmn P) (hP' : IsSeedPattern K hm' P') {t₀ : RegularTree n}
    (hB : principalPart hmn (P t₀).extExchangeMatrix = principalPart hm' (P' t₀).extExchangeMatrix)
    (hZ : ZSpanCondition (P' t₀).extExchangeMatrix (P t₀).extExchangeMatrix)
    (t t' : RegularTree n) (i j : Fin n) (h : cluster hmn (P t) i = cluster hmn (P t') j) :
    cluster hm' (P' t) i = cluster hm' (P' t') j := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : CharZero F' := charZero_of_injective_algebraMap (algebraMap K F').injective
  exact hP.cluster_eq_of_zSpanCondition hmn hm' hP' hB hZ h

/-- If `f' : ι → β` is constant on the fibres of `f : ι → α`, the range of `f'` has at most as
many elements as the range of `f`. -/
private theorem relabel_encard_range_le {ι α β : Type*} {f : ι → α} {f' : ι → β}
    (h : ∀ a b, f a = f b → f' a = f' b) : (Set.range f').encard ≤ (Set.range f).encard := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨a₀⟩⟩
  · simp [Set.range_eq_empty]
  · let g : α → β := fun y => if hy : ∃ a, f a = y then f' hy.choose else f' a₀
    refine (Set.encard_le_encard ?_).trans (Set.encard_image_le g (Set.range f))
    rintro _ ⟨a, rfl⟩
    have hy : ∃ b, f b = f a := ⟨a, rfl⟩
    refine ⟨f a, ⟨a, rfl⟩, ?_⟩
    simp only [g, dif_pos hy]
    exact h _ _ hy.choose_spec

omit [Field K] [Field F] [Algebra K F] in
/-- The cluster variables of an assignment of seed data, as the range of `(t, i) ↦ x_{i;t}`. -/
private theorem relabel_patternClusterVariables_eq_range (hmn : n ≤ m)
    (P : RegularTree n → SeedData F m n) :
    patternClusterVariables hmn P =
      Set.range fun p : RegularTree n × Fin n => cluster hmn (P p.1) p.2 := by
  ext x
  simp [patternClusterVariables, clusterVariables]

omit [Field K] [Field F] [Algebra K F] [Field F'] [Algebra K F'] in
/-- **Comparing numbers of cluster variables and of clusters.** Let `Σ = P` and `Σ' = P'` be of
rank `n`, such that `x_{i;t} = x_{j;t'}` implies `x'_{i;t} = x'_{j;t'}` for all `t, t', i, j`.
Then `|𝒳(Σ')| ≤ |𝒳(Σ)|` and the number of clusters of `Σ'` is at most that of `Σ`; in
particular, if `𝒳(Σ)` is finite, so is `𝒳(Σ')`. No property of seed patterns is used, so the
statement is for arbitrary seed data; the two inequalities hold in `ℕ∞` without the finiteness
hypothesis. -/
@[cluster_algebras "lem_exc_transfer_counts"]
theorem encard_patternClusterVariables_le_of_cluster_eq (hmn : n ≤ m) (hm' : n ≤ m')
    {P : RegularTree n → SeedData F m n} {P' : RegularTree n → SeedData F' m' n}
    (h : ∀ (t t' : RegularTree n) (i j : Fin n), cluster hmn (P t) i = cluster hmn (P t') j →
      cluster hm' (P' t) i = cluster hm' (P' t') j) :
    (patternClusterVariables hm' P').encard ≤ (patternClusterVariables hmn P).encard ∧
      (patternClusters hm' P').encard ≤ (patternClusters hmn P).encard := by
  refine ⟨?_, relabel_encard_range_le fun t t'' ht => ?_⟩
  · rw [relabel_patternClusterVariables_eq_range, relabel_patternClusterVariables_eq_range]
    exact relabel_encard_range_le fun p q hpq => h _ _ _ _ hpq
  · have key : ∀ t t'', clusterVariables hmn (P t) = clusterVariables hmn (P t'') →
        clusterVariables hm' (P' t) ⊆ clusterVariables hm' (P' t'') := by
      rintro t t'' ht _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ : cluster hmn (P t) i ∈ clusterVariables hmn (P t'') := ht ▸ ⟨i, rfl⟩
      exact ⟨j, h _ _ _ _ hj⟩
    exact (key _ _ ht).antisymm (key _ _ ht.symm)

omit [Field K] [Field F] [Algebra K F] [Field F'] [Algebra K F'] in
/-- **Comparing numbers of cluster variables and of clusters**, finiteness: under the hypothesis
of `encard_patternClusterVariables_le_of_cluster_eq`, if `𝒳(Σ)` is finite, so is `𝒳(Σ')`. -/
@[cluster_algebras "lem_exc_transfer_counts"]
theorem finite_patternClusterVariables_of_cluster_eq (hmn : n ≤ m) (hm' : n ≤ m')
    {P : RegularTree n → SeedData F m n} {P' : RegularTree n → SeedData F' m' n}
    (h : ∀ (t t' : RegularTree n) (i j : Fin n), cluster hmn (P t) i = cluster hmn (P t') j →
      cluster hm' (P' t) i = cluster hm' (P' t') j)
    (hfin : (patternClusterVariables hmn P).Finite) : (patternClusterVariables hm' P').Finite :=
  Set.finite_of_encard_le_coe
    ((encard_patternClusterVariables_le_of_cluster_eq hmn hm' h).1.trans hfin.encard_eq_coe.le)

end Pattern

/-! ### Simply-laced Cartan counterparts -/

/-- **A skew-symmetrizable matrix with symmetric Cartan counterpart is skew-symmetric**:
`bᵢⱼ = -bⱼᵢ` for all `i, j`. -/
@[cluster_algebras "lem_exc_simply_laced_skew"]
theorem SkewSymmetrizable.eq_neg_of_isSymm_cartanCounterpart {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hA : (cartanCounterpart B).IsSymm) (i j : Fin n) :
    B i j = -B j i := by
  obtain ⟨d, hd⟩ := hB
  have habs : |B i j| = |B j i| := by
    by_cases hij : i = j
    · rw [hij]
    · have h := hA.apply i j
      simp only [cartanCounterpart, of_apply, if_neg hij, if_neg (Ne.symm hij), neg_inj] at h
      exact h.symm
  have h1 := hd.pos_iff_neg i j
  rcases abs_eq_abs.1 habs with h | h <;> omega

/-- The simply-laced Cartan matrix of a graph is symmetric. -/
theorem isSymm_cartanOfGraph (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (cartanOfGraph G).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  by_cases h : i = j
  · rw [h]
  · simp only [cartanOfGraph, of_apply, if_neg h, if_neg (Ne.symm h), G.adj_comm]

/-- The Cartan matrix `C(E_k)`, as the Cartan matrix of the one-element list `[E_k]`, is
symmetric. -/
theorem DynkinSymbol.isSymm_listCartan_E (k : ℕ) (hk : 6 ≤ k ∧ k ≤ 8) :
    (DynkinSymbol.listCartan [.E k hk]).IsSymm := by
  simp only [DynkinSymbol.listCartan, reindex_apply]
  refine Matrix.IsSymm.submatrix (Matrix.IsSymm.fromBlocks ?_ ?_ ?_) _
  · exact isSymm_cartanOfGraph _
  · simp
  · exact Matrix.IsSymm.ext fun a _ => a.elim0

/-- **A skew-symmetrizable matrix with symmetric Cartan counterpart is skew-symmetric**, for the
types `E₆`, `E₇`, `E₈`: if `A(B)` is of type `E_k`, then `bᵢⱼ = -bⱼᵢ` for all `i, j`. -/
@[cluster_algebras "lem_exc_simply_laced_skew"]
theorem SkewSymmetrizable.eq_neg_of_isOfDynkinType_E {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {k : ℕ} {hk : 6 ≤ k ∧ k ≤ 8}
    (hA : IsOfDynkinType (cartanCounterpart B) [.E k hk]) (i j : Fin n) : B i j = -B j i := by
  refine hB.eq_neg_of_isSymm_cartanCounterpart ?_ i j
  obtain ⟨σ, hσ⟩ := hA
  refine Matrix.IsSymm.ext fun a b => ?_
  rw [hσ, hσ]
  exact (DynkinSymbol.isSymm_listCartan_E k hk).apply _ _

/-! ### Reference matrices -/

section Reference

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A **reference matrix for a Dynkin symbol** `X` of rank `n`: an `n × n` integer matrix `B₀`
such that for every skew-symmetrizable `n × n` integer matrix `P` with `A(P) = C(X)` there are a
finite sequence `w` of directions and a permutation `τ` of `Fin n` with `μ_w(P) = B₀^τ`. -/
@[cluster_algebras "def_exc_reference"]
def IsReferenceMatrix (X : DynkinSymbol) (B₀ : Matrix (Fin X.rank) (Fin X.rank) ℤ) : Prop :=
  ∀ P : Matrix (Fin X.rank) (Fin X.rank) ℤ, SkewSymmetrizable P →
    cartanCounterpart P = X.cartan →
      ∃ (w : List (Fin X.rank)) (τ : Equiv.Perm (Fin X.rank)),
        matrixMutationList le_rfl P w = relabelMatrix le_rfl B₀ τ

/-- The entries of the Cartan matrix of a one-element list `[X]` are those of `C(X)`. -/
theorem DynkinSymbol.listCartan_singleton_apply (X : DynkinSymbol) (i j : Fin X.rank) :
    DynkinSymbol.listCartan [X] i j = X.cartan i j := by
  have h : ∀ a b : Fin X.rank, reindex finSumFinEquiv finSumFinEquiv
      (fromBlocks X.cartan (0 : Matrix (Fin X.rank) (Fin 0) ℤ) 0 0) (Fin.castAdd 0 a)
        (Fin.castAdd 0 b) = X.cartan a b := fun a b => by
    rw [reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁]
  exact h i j

/-- A matrix of type `[X]` is a simultaneous permutation of `C(X)`. -/
theorem IsOfDynkinType.exists_perm_of_singleton {X : DynkinSymbol}
    {A : Matrix (Fin X.rank) (Fin X.rank) ℤ} (hA : IsOfDynkinType A [X]) :
    ∃ σ : Equiv.Perm (Fin X.rank), ∀ i j, A i j = X.cartan (σ i) (σ j) := by
  obtain ⟨σ, hσ⟩ := hA
  exact ⟨σ, fun i j => (hσ i j).trans (DynkinSymbol.listCartan_singleton_apply X _ _)⟩

/-- The principal part of a matrix mutated along a sequence is its principal part mutated along
that sequence. -/
theorem relabel_principalPart_matrixMutationList {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (s : List (Fin n)) :
    principalPart hmn (matrixMutationList hmn B s) =
      matrixMutationList le_rfl (principalPart hmn B) s := by
  induction s generalizing B with
  | nil => rfl
  | cons k s ih =>
    rw [matrixMutationList_cons, ih, principalPart_matrixMutation]
    rfl

/-- **A pattern of type `X` has a relabelled reference matrix.** If `B₀` is a reference matrix
for `X` and `Σ` is a seed pattern of type `X` (of rank `X.rank`), there are a vertex `t` and a
permutation `ρ` with `B(t) = B₀^ρ`. No assumption on the characteristic of the ground field is
needed. -/
@[cluster_algebras "lem_exc_move_to_reference"]
theorem IsSeedPattern.exists_principalPart_eq_relabelMatrix {X : DynkinSymbol}
    {B₀ : Matrix (Fin X.rank) (Fin X.rank) ℤ} (href : IsReferenceMatrix X B₀)
    (hmn : X.rank ≤ m) {P : RegularTree X.rank → SeedData F m X.rank}
    (hP : IsSeedPattern K hmn P) (hX : IsPatternOfType hmn P [X]) :
    ∃ (t : RegularTree X.rank) (ρ : Equiv.Perm (Fin X.rank)),
      principalPart hmn (P t).extExchangeMatrix = relabelMatrix le_rfl B₀ ρ := by
  obtain ⟨t₁, hX⟩ := hX
  set B₁ := principalPart hmn (P t₁).extExchangeMatrix with hB₁
  obtain ⟨σ, hσ⟩ := hX.exists_perm_of_singleton
  set Q := relabelMatrix le_rfl B₁ σ⁻¹ with hQ
  have hQcart : cartanCounterpart Q = X.cartan := by
    ext a b
    rw [hQ, cartanCounterpart_relabelMatrix, relabelMatrix_self, submatrix_apply, hσ,
      Equiv.Perm.coe_inv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  obtain ⟨w, τ, hw⟩ := href Q
    (ExtSkewSymmetrizable.relabelMatrix le_rfl (B := B₁) (hP.1 t₁).2 σ⁻¹) hQcart
  set s := w.map ⇑σ⁻¹ with hs
  have hsw : s.map σ = w := by simp [hs, List.map_map]
  have hB₁Q : B₁ = relabelMatrix le_rfl Q σ := by
    rw [hQ, relabelMatrix_relabelMatrix, inv_mul_cancel, relabelMatrix_one]
  obtain ⟨t, ht⟩ := hP.seedMutationSeq_mem_range hmn t₁ s
  refine ⟨t, τ * σ, ?_⟩
  rw [ht, seedMutationSeq_extExchangeMatrix_eq_matrixMutationList,
    relabel_principalPart_matrixMutationList, ← hB₁, hB₁Q, matrixMutationList_relabelMatrix, hsw,
    hw, relabelMatrix_relabelMatrix]

end Reference

end ClusterAlgebras

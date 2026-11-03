/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ClusterAlgebras.Definitions
public import ClusterAlgebras.Defs.SkewSymmetrization
public import ClusterAlgebras.TreeOrientation
public import ClusterAlgebras.Cartan.Dynkin
public import ClusterAlgebras.FiniteType.RankTwo
public import ClusterAlgebras.Restriction.Reindexing

/-!
# Diagrams of skew-symmetrizable matrices

`2`-finite exchange matrices are classified through their diagrams [FWZ]. Here a diagram is
always handled through a skew-symmetrizable integer matrix realizing it. This file defines
weights, arrows and the graph of a matrix, mutation equivalence of diagrams, induced paths and
chordless cycles, weighted graphs and Dynkin shapes and classes, the trees `T_{a,b,c}` and the
extended Dynkin trees, and the crowns `S^s_{p,q,r}`.

## Main definitions

* `ClusterAlgebras.diagramWeight B i j`: the weight `|bᵢⱼ bⱼᵢ|`.
* `ClusterAlgebras.diagramGraph B`: the graph `G_B` of pairs of positive weight.
* `ClusterAlgebras.DiagramEquiv B B'`: `Γ((μ_s B)^π) = Γ(B')` for some `s` and `π`.
* `ClusterAlgebras.IsInducedPath`, `IsChordlessCycle`, `IsOrientedUnitCycle`: induced paths and
  chordless cycles of a matrix, given by sequences of indices.
* `ClusterAlgebras.dynkinWeightedGraph Xs`, `HasDynkinShape B Xs`, `IsOfDynkinClass B Xs`.
* `ClusterAlgebras.IsTShape`, `IsExtendedDynkinShape`, `IsCrownShape`.

## Implementation notes

* Indices are `Fin n`, so FWZ's `[1, n]` is shifted down by one.
* An arrow `i → j` of `B` is `0 < B i j`; it is not given a name.
* `B^r` for an injective `r : [1, m] → [1, n]` is `B.submatrix r r`, which is the reindexing
  `matrixReindex` along `r` read as a square reindexing map.
* A sequence `(v₁, …, v_m)` of indices is a function `v : Fin m → Fin n`; indices of a cycle are
  read modulo `m` through `finRotate m`, the successor map of `Fin m`.
* Every shape is defined through an enumeration `e : Fin M ≃ Fin N` of the indices and a model
  weight `f` on the positions `0, …, M - 1` of the enumeration, `f p q` being read for `p < q`.
  The positions of FWZ's named indices are spelled out in each docstring.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n m N : ℕ}

/-! ### Reindexing along an injective map -/

/-- An injective map `r : [1, m] → [1, n]` as a reindexing map from `(m, m)` to `(n, n)`: every
index of a square matrix is mutable, so the condition on mutable indices is automatic. -/
@[cluster_algebras "lem_cartan_counterpart_reindex"]
def squareReindexingMap (r : Fin m ↪ Fin n) : ReindexingMap m m n n where
  toFun := r
  injective := r.injective
  lt_of_lt p _ := (r p).isLt

/-- For a square matrix, the reindexing `matrixReindex` along `r` is
`B^r = B.submatrix r r`. -/
@[cluster_algebras "lem_cartan_counterpart_reindex"]
theorem matrixReindex_squareReindexingMap {α : Type*} (B : Matrix (Fin n) (Fin n) α)
    (r : Fin m ↪ Fin n) : matrixReindex le_rfl B (squareReindexingMap r) = B.submatrix r r :=
  rfl

/-- **Mutation along a sequence commutes with reindexing along an injective map**:
`μ_t(B^r) = (μ_{r(t)}(B))^r`. -/
theorem matrixMutationList_submatrix_embedding {R : Type*} [CommRing R] [LinearOrder R]
    (B : Matrix (Fin n) (Fin n) R) (r : Fin m ↪ Fin n) (t : List (Fin m)) :
    matrixMutationList le_rfl (B.submatrix r r) t =
      (matrixMutationList le_rfl B (t.map r)).submatrix r r :=
  matrixMutationList_matrixReindex le_rfl le_rfl B (squareReindexingMap r) t

/-! ### Weights, arrows and the graph of a matrix -/

attribute [cluster_algebras "def_diagram_weight"] ClusterAlgebras.diagramWeight
attribute [cluster_algebras "def_diagram_weight"] ClusterAlgebras.diagramGraph
attribute [cluster_algebras "def_diagram_shapes"] ClusterAlgebras.IsInducedPath
attribute [cluster_algebras "def_diagram_shapes"] ClusterAlgebras.IsChordlessCycle
attribute [cluster_algebras "def_diagram_shapes"] ClusterAlgebras.cycleWeights
attribute [cluster_algebras "def_diagram_shapes"] ClusterAlgebras.IsCyclicallyOriented
attribute [cluster_algebras "def_tree_shapes"] ClusterAlgebras.IsTShape
attribute [cluster_algebras "def_crown_shape"] ClusterAlgebras.IsCrownShape
attribute [cluster_algebras "lem_cycle_diagrams"] ClusterAlgebras.IsAdmissibleCycleWeights

/-- The weight is symmetric in its two indices. -/
theorem diagramWeight_comm (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    diagramWeight B i j = diagramWeight B j i := by
  rw [diagramWeight, diagramWeight, mul_comm]

/-- Adjacency in `G_B`, unfolded. -/
theorem diagramGraph_adj {B : Matrix (Fin n) (Fin n) ℤ} {i j : Fin n} :
    (diagramGraph B).Adj i j ↔ i ≠ j ∧ 0 < diagramWeight B i j :=
  Iff.rfl

/-- Adjacency in `G_B` is decidable. -/
instance instDecidableRelDiagramGraphAdj (B : Matrix (Fin n) (Fin n) ℤ) :
    DecidableRel (diagramGraph B).Adj := fun i j =>
  decidable_of_iff (i ≠ j ∧ 0 < diagramWeight B i j) diagramGraph_adj.symm

/-- An index `k` is a **source** of `B` when `b_{kj} ≥ 0` for all `j`. -/
@[cluster_algebras "def_diagram_weight"]
def IsMatrixSource (B : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) : Prop :=
  ∀ j, 0 ≤ B k j

/-- An index `k` is a **sink** of `B` when `b_{kj} ≤ 0` for all `j`. -/
@[cluster_algebras "def_diagram_weight"]
def IsMatrixSink (B : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) : Prop :=
  ∀ j, B k j ≤ 0

/-- `B` is **connected** when its diagram `Γ(B)` is connected in the sense of
`Diagram.Connected`. -/
@[cluster_algebras "def_diagram_weight"]
def IsConnectedDiagram (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (diagram (B.map (Int.cast : ℤ → ℝ))).Connected

/-- `B` is a **tree diagram** when its graph `G_B` is a finite tree. -/
@[cluster_algebras "def_diagram_weight"]
def IsTreeDiagram (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsFiniteTree (diagramGraph B)

/-! ### Mutation equivalence of diagrams -/

/-- `B` and `B'` have **mutation equivalent diagrams**, `B ∼ B'`, when
`Γ((μ_s(B))^π) = Γ(B')` for a finite sequence `s` of indices and a permutation `π`, where
`(μ_s(B))^π` has entries `(μ_s(B))_{π(i) π(j)}`. This is the mutation equivalence
`Γ(B) ∼ Γ(B')` of [FWZ], stated for matrices realizing the diagrams. -/
@[cluster_algebras "def_diagram_equivalence"]
def DiagramEquiv (B B' : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ (s : List (Fin n)) (π : Equiv.Perm (Fin n)),
    diagram (((matrixMutationList le_rfl B s).submatrix π π).map (Int.cast : ℤ → ℝ)) =
      diagram (B'.map (Int.cast : ℤ → ℝ))

/-! ### Induced paths and chordless cycles -/

/-- An induced path `(v₁, …, v_m)` is **linearly oriented** when `v_p → v_{p+1}` for all
`p ∈ [1, m - 1]`. -/
@[cluster_algebras "def_diagram_shapes"]
def IsLinearlyOrientedPath (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin m → Fin n) : Prop :=
  IsInducedPath B v ∧ ∀ p q : Fin m, (p : ℕ) + 1 = q → 0 < B (v p) (v q)

/-- A chordless cycle `(v₁, …, v_m)` is an **oriented unit cycle** when `v_p → v_{p+1}` and
`w_p = 1` for all `p`. -/
@[cluster_algebras "def_diagram_shapes"]
def IsOrientedUnitCycle (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin m → Fin n) : Prop :=
  IsChordlessCycle B v ∧ ∀ p, 0 < B (v p) (v (finRotate m p)) ∧ cycleWeights B v p = 1

/-- `B` is a **path diagram** when some enumeration of `[1, n]` is an induced path of `B`. -/
@[cluster_algebras "def_diagram_shapes"]
def IsPathDiagram (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ v : Fin n ≃ Fin n, IsInducedPath B v

/-- `B` is a **cycle diagram** when some enumeration of `[1, n]` is a chordless cycle of `B`. -/
@[cluster_algebras "def_diagram_shapes"]
def IsCycleDiagram (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ v : Fin n ≃ Fin n, IsChordlessCycle B v

/-! ### Weighted graphs, Dynkin shapes and Dynkin classes -/

/-- A **weighted graph** on `[1, m]`: a symmetric function `ω : [1, m] × [1, m] → ℕ` with
`ω(p, p) = 0`. -/
@[cluster_algebras "def_dynkin_weighted_graph"]
def IsWeightedGraph (ω : Fin m → Fin m → ℕ) : Prop :=
  (∀ p q, ω p q = ω q p) ∧ ∀ p, ω p p = 0

/-- A skew-symmetrizable `m × m` integer matrix `C` is an **orientation** of `ω` when
`w_C = ω`. -/
@[cluster_algebras "def_dynkin_weighted_graph"]
def IsOrientationOfWeighted (C : Matrix (Fin m) (Fin m) ℤ) (ω : Fin m → Fin m → ℕ) : Prop :=
  SkewSymmetrizable C ∧ ∀ i j, diagramWeight C i j = ω i j

/-- The **Dynkin weighted graph** `ω_X` of a list `X` of Dynkin symbols:
`ω_X(i, j) = C(X)ᵢⱼ C(X)ⱼᵢ` for `i ≠ j` and `ω_X(i, i) = 0`. The product is a nonnegative
integer, both factors being nonpositive. -/
@[cluster_algebras "def_dynkin_weighted_graph"]
def dynkinWeightedGraph (Xs : List DynkinSymbol) :
    Fin (DynkinSymbol.listRank Xs) → Fin (DynkinSymbol.listRank Xs) → ℕ :=
  fun i j => if i = j then 0 else
    (DynkinSymbol.listCartan Xs i j * DynkinSymbol.listCartan Xs j i).natAbs

/-- An `N × N` matrix `B` **has Dynkin shape `X`** when `B^σ` is an orientation of `ω_X` for a
bijection `σ` from the indices of `C(X)` to those of `B`, `B^σ` having entries
`b_{σ(i) σ(j)}`. The bijection also records that `X` has total rank `N`. -/
@[cluster_algebras "def_dynkin_weighted_graph"]
def HasDynkinShape (B : Matrix (Fin N) (Fin N) ℤ) (Xs : List DynkinSymbol) : Prop :=
  ∃ σ : Fin (DynkinSymbol.listRank Xs) ≃ Fin N,
    IsOrientationOfWeighted (B.submatrix σ σ) (dynkinWeightedGraph Xs)

/-- An `N × N` matrix `B` is **of Dynkin class `X`** when `B ∼ C` for a matrix `C` of Dynkin
shape `X`. FWZ ask for `C` to be an orientation of `ω_X` itself; a matrix of Dynkin
shape `X` is a relabelling `C^{σ⁻¹}` of one, and `C ∼ C^{σ⁻¹}`, so the two agree. Stating it
with Dynkin shapes keeps `C` the same size as `B` without a cast. -/
@[cluster_algebras "def_dynkin_weighted_graph"]
def IsOfDynkinClass (B : Matrix (Fin N) (Fin N) ℤ) (Xs : List DynkinSymbol) : Prop :=
  ∃ C : Matrix (Fin N) (Fin N) ℤ, HasDynkinShape C Xs ∧ DiagramEquiv B C

/-! ### The trees `T_{a,b,c}`, the extended Dynkin trees and the crowns -/

/-- The model of `B_k^{(1)}`: positions `a = 0`, `b = 1`, `x_t = t + 1` (`t ∈ [1, k - 1]`);
weight `1` on `{a, x₁}`, `{b, x₁}`, `{x_t, x_{t+1}}` (`t ∈ [1, k - 3]`), and
`ω(x_{k-2}, x_{k-1}) = 2`. -/
def bAffineModel (k : ℕ) (p q : ℕ) : ℕ :=
  if (p = 0 ∧ q = 2) ∨ (p = 1 ∧ q = 2) ∨ (2 ≤ p ∧ p + 1 = q ∧ q ≤ k - 1) then 1
  else if p = k - 1 ∧ q = k then 2 else 0

/-- `ω` is **of shape `B_k^{(1)}`** (`k ≥ 3`, `N = k + 1`): `[1, N]` has an enumeration
`a, b, x₁, …, x_{k-1}` with `ω = 1` on `{a, x₁}`, `{b, x₁}` and `{xᵢ, xᵢ₊₁}` for
`i ∈ [1, k - 3]`, `ω(x_{k-2}, x_{k-1}) = 2`, and `ω = 0` on all other pairs. -/
@[cluster_algebras "def_tree_shapes"]
def IsBAffineShape (ω : Fin N → Fin N → ℕ) (k : ℕ) : Prop :=
  3 ≤ k ∧ IsShapeOf ω (k + 1) (bAffineModel k)

/-- The model of `C_k^{(1)}`: positions `x_t = t` (`t ∈ [0, k]`); weight `2` on `{x₀, x₁}` and
`{x_{k-1}, x_k}`, and `1` on `{x_t, x_{t+1}}` for `t ∈ [1, k - 2]`. -/
def cAffineModel (k : ℕ) (p q : ℕ) : ℕ :=
  if p + 1 = q ∧ q ≤ k then (if p = 0 ∨ q = k then 2 else 1) else 0

/-- `ω` is **of shape `C_k^{(1)}`** (`k ≥ 2`, `N = k + 1`): `[1, N]` has an enumeration
`x₀, …, x_k` with `ω(x₀, x₁) = ω(x_{k-1}, x_k) = 2`, `ω(xᵢ, xᵢ₊₁) = 1` for `i ∈ [1, k - 2]`,
and `ω = 0` on all other pairs. -/
@[cluster_algebras "def_tree_shapes"]
def IsCAffineShape (ω : Fin N → Fin N → ℕ) (k : ℕ) : Prop :=
  2 ≤ k ∧ IsShapeOf ω (k + 1) (cAffineModel k)

/-- The model of `D_k^{(1)}`: positions `a = 0`, `b = 1`, `x_t = t + 1` (`t ∈ [1, k - 3]`),
`c = k - 1`, `d = k`; weight `1` on `{a, x₁}`, `{b, x₁}`, `{x_t, x_{t+1}}` (`t ∈ [1, k - 4]`),
`{x_{k-3}, c}` and `{x_{k-3}, d}`. -/
def dAffineModel (k : ℕ) (p q : ℕ) : ℕ :=
  if (p = 0 ∧ q = 2) ∨ (p = 1 ∧ q = 2) ∨ (2 ≤ p ∧ p + 1 = q ∧ q ≤ k - 2) ∨
      (p = k - 2 ∧ q = k - 1) ∨ (p = k - 2 ∧ q = k)
  then 1 else 0

/-- `ω` is **of shape `D_k^{(1)}`** (`k ≥ 4`, `N = k + 1`): `[1, N]` has an enumeration
`a, b, x₁, …, x_{k-3}, c, d` with `ω = 1` on `{a, x₁}`, `{b, x₁}`, `{xᵢ, xᵢ₊₁}`
(`i ∈ [1, k - 4]`), `{x_{k-3}, c}`, `{x_{k-3}, d}`, and `ω = 0` on all other pairs. -/
@[cluster_algebras "def_tree_shapes"]
def IsDAffineShape (ω : Fin N → Fin N → ℕ) (k : ℕ) : Prop :=
  4 ≤ k ∧ IsShapeOf ω (k + 1) (dAffineModel k)

/-- `ω` is **of shape `E₆^{(1)}`**, that is of shape `T_{2,2,2}`. -/
@[cluster_algebras "def_tree_shapes"]
def IsE6AffineShape (ω : Fin N → Fin N → ℕ) : Prop :=
  IsTShape ω 2 2 2

/-- `ω` is **of shape `E₇^{(1)}`**, that is of shape `T_{1,3,3}`. -/
@[cluster_algebras "def_tree_shapes"]
def IsE7AffineShape (ω : Fin N → Fin N → ℕ) : Prop :=
  IsTShape ω 1 3 3

/-- `ω` is **of shape `E₈^{(1)}`**, that is of shape `T_{1,2,5}`. -/
@[cluster_algebras "def_tree_shapes"]
def IsE8AffineShape (ω : Fin N → Fin N → ℕ) : Prop :=
  IsTShape ω 1 2 5

/-- The model of `F₄^{(1)}`: positions `x_t = t - 1` (`t ∈ [1, 5]`); weights
`ω(x₁, x₂) = ω(x₃, x₄) = ω(x₄, x₅) = 1` and `ω(x₂, x₃) = 2`. -/
def f4AffineModel (p q : ℕ) : ℕ :=
  if p + 1 = q ∧ q ≤ 4 then (if p = 1 then 2 else 1) else 0

/-- `ω` is **of shape `F₄^{(1)}`** (`N = 5`): `[1, 5]` has an enumeration `x₁, …, x₅` with
`ω(x₁, x₂) = ω(x₃, x₄) = ω(x₄, x₅) = 1`, `ω(x₂, x₃) = 2`, and `ω = 0` on all other pairs. -/
@[cluster_algebras "def_tree_shapes"]
def IsF4AffineShape (ω : Fin N → Fin N → ℕ) : Prop :=
  IsShapeOf ω 5 f4AffineModel

/-- The model of `G₂^{(1)}(a)`: positions `x_t = t` (`t ∈ [0, 2]`); `ω(x₀, x₁) = 3`,
`ω(x₁, x₂) = a`, `ω(x₀, x₂) = 0`. -/
def g2AffineModel (a : ℕ) (p q : ℕ) : ℕ :=
  if p = 0 ∧ q = 1 then 3 else if p = 1 ∧ q = 2 then a else 0

/-- `ω` is **of shape `G₂^{(1)}(a)`** (`N = 3`, `a ∈ {1, 2, 3}`): `[1, 3]` has an enumeration
`x₀, x₁, x₂` with `ω(x₀, x₁) = 3`, `ω(x₁, x₂) = a` and `ω(x₀, x₂) = 0`. -/
@[cluster_algebras "def_tree_shapes"]
def IsG2AffineShape (ω : Fin N → Fin N → ℕ) (a : ℕ) : Prop :=
  (a = 1 ∨ a = 2 ∨ a = 3) ∧ IsShapeOf ω 3 (g2AffineModel a)

/-- The **extended Dynkin shapes**: `B_k^{(1)}`, `C_k^{(1)}`, `D_k^{(1)}`, `E₆^{(1)}`,
`E₇^{(1)}`, `E₈^{(1)}`, `F₄^{(1)}` and `G₂^{(1)}(a)`. A matrix is of a shape when its weight
function `diagramWeight B` is. -/
@[cluster_algebras "def_tree_shapes"]
def IsExtendedDynkinShape (ω : Fin N → Fin N → ℕ) : Prop :=
  (∃ k, IsBAffineShape ω k) ∨ (∃ k, IsCAffineShape ω k) ∨ (∃ k, IsDAffineShape ω k) ∨
    IsE6AffineShape ω ∨ IsE7AffineShape ω ∨ IsE8AffineShape ω ∨ IsF4AffineShape ω ∨
    ∃ a, IsG2AffineShape ω a

/-! ### The weight sequences of `2`-finite cycles -/

end ClusterAlgebras

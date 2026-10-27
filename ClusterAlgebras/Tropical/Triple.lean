/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.SeedPattern
public import ClusterAlgebras.Tropical.Semifield

/-!
# Seeds as triples

A labeled seed `(x̃, B̃)` of rank `n` with `m` entries can be recorded by its cluster
`x = (x₁, …, xₙ)`, its principal part `B`, and its *coefficient tuple*
`y = (y₁, …, yₙ)`, where `yⱼ = ∏_{i > n} qᵢ ^ bᵢⱼ` lives in the tropical semifield
`Trop(q_{n+1}, …, q_m)` and records the frozen rows of `B̃`. The frozen variables
`x_{n+1}, …, x_m` are fixed once and for all. Seed mutation then becomes a rule on triples
`(x, y, B)`, in which the coefficients mutate tropically.

The frozen positions `i ∈ [n+1, m]` are the elements `i : Fin m` with `n ≤ i`, collected in the
index type `FrozenIndex m n`.

## Main definitions

* `ClusterAlgebras.FrozenIndex`: the frozen positions.
* `ClusterAlgebras.coefficientTuple`: the coefficient tuple of an extended exchange matrix.
* `ClusterAlgebras.tropicalEval`: the homomorphism `ε : Trop(q) → F` with `ε(qᵢ) = xᵢ`.
* `ClusterAlgebras.SeedTriple`, `ClusterAlgebras.IsSeedTriple`: labeled seed triples.
* `ClusterAlgebras.SeedTriple.mutation`: mutation of seed triples.
* `ClusterAlgebras.SeedData.toSeedTriple`: the triple of a labeled seed.
* `ClusterAlgebras.IsTriplePattern`: a labeled seed pattern of triples.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

variable (m n) in
/-- The **frozen positions** `i ∈ [n+1, m]` of an `m`-tuple, as elements `i : Fin m` with
`n ≤ i` (indices start at `0`). -/
abbrev FrozenIndex : Type :=
  {i : Fin m // n ≤ (i : ℕ)}

/-- The **coefficient tuple** of an `m × n` integer matrix `B̃ = (bᵢⱼ)`: the tuple
`(y₁, …, yₙ)` of elements of `Trop(q_{n+1}, …, q_m)` with `yⱼ = ∏_{i > n} qᵢ ^ bᵢⱼ`. -/
@[cluster_algebras "def_coefficient_tuple"]
def coefficientTuple (B : Matrix (Fin m) (Fin n) ℤ) (j : Fin n) :
    TropicalSemifield (FrozenIndex m n) :=
  TropicalSemifield.monomial fun i => B i.1 j

/-- The exponent of `qᵢ` in the coefficient tuple entry `yⱼ` of `B̃` is `bᵢⱼ`. -/
@[simp]
theorem exponent_coefficientTuple (B : Matrix (Fin m) (Fin n) ℤ) (j : Fin n)
    (i : FrozenIndex m n) : TropicalSemifield.exponent (coefficientTuple B j) i = B i.1 j :=
  rfl

/-- The map `ε : Trop(qᵢ : i ∈ ι) → F` with `ε(qᵢ) = xᵢ`, sending `∏ᵢ qᵢ ^ aᵢ` to `∏ᵢ xᵢ ^ aᵢ`.
When every `xᵢ` is nonzero it is a group homomorphism into `Fˣ`. -/
@[cluster_algebras "def_triple_mutation"]
def tropicalEval {ι : Type*} [Fintype ι] (x : ι → F) (y : TropicalSemifield ι) : F :=
  ∏ i, x i ^ TropicalSemifield.exponent y i

variable (F m n) in
/-- The data of a **labeled seed triple** of rank `n` with frozen positions `[n+1, m]`: a
cluster `x = (x₁, …, xₙ)` in `F`, a coefficient tuple `y` in `Trop(q_{n+1}, …, q_m)`, and an
`n × n` integer matrix `B`. `IsSeedTriple` says when it is a labeled seed triple. -/
@[cluster_algebras "def_seed_triple"]
structure SeedTriple where
  /-- The cluster `x = (x₁, …, xₙ)`. -/
  cluster : Fin n → F
  /-- The coefficient tuple `y = (y₁, …, yₙ)`. -/
  coeff : Fin n → TropicalSemifield (FrozenIndex m n)
  /-- The exchange matrix `B`. -/
  exchangeMatrix : Matrix (Fin n) (Fin n) ℤ

/-- The extended cluster `(x₁, …, xₙ, x_{n+1}, …, xₘ)` of a seed triple, with the frozen
variables `x_{n+1}, …, xₘ` given by `frozen`. -/
def SeedTriple.extCluster (frozen : FrozenIndex m n → F) (T : SeedTriple F m n) : Fin m → F :=
  fun i => if h : (i : ℕ) < n then T.cluster ⟨i, h⟩ else frozen ⟨i, not_lt.1 h⟩

variable (K) in
/-- `T = (x, y, B)` is a **labeled seed triple** of rank `n` over `K`, with frozen variables
`frozen = (x_{n+1}, …, xₘ)`, when `(x₁, …, xₘ)` is a free generating tuple of `F` over `K` and
`B` is skew-symmetrizable. -/
@[cluster_algebras "def_seed_triple"]
def IsSeedTriple (frozen : FrozenIndex m n → F) (T : SeedTriple F m n) : Prop :=
  IsFreeGeneratingTuple K (T.extCluster frozen) ∧ SkewSymmetrizable T.exchangeMatrix

/-- **Mutation of seed triples** in direction `k`, with frozen variables `frozen`. The
mutation of `(x, y, B)` is `(x', y', μₖ(B))`, where
* `y'ₖ = yₖ⁻¹`, and for `j ≠ k`, `y'ⱼ = yⱼ (yₖ ⊕ 1) ^ (-bₖⱼ)` if `bₖⱼ ≤ 0` and
  `y'ⱼ = yⱼ (yₖ⁻¹ ⊕ 1) ^ (-bₖⱼ)` if `bₖⱼ ≥ 0` (the two agree when `bₖⱼ = 0`; see
  `SeedTriple.mutation_coeff_of_nonneg`);
* `x'ⱼ = xⱼ` for `j ≠ k`, and
  `x'ₖ = (ε(yₖ / (yₖ ⊕ 1)) ∏_{bᵢₖ > 0} xᵢ ^ bᵢₖ + ε(1 / (yₖ ⊕ 1)) ∏_{bᵢₖ < 0} xᵢ ^ (-bᵢₖ)) / xₖ`,
  the products running over `i ∈ [1, n]` and `ε = tropicalEval frozen`. -/
@[cluster_algebras "def_triple_mutation"]
def SeedTriple.mutation (frozen : FrozenIndex m n → F) (T : SeedTriple F m n) (k : Fin n) :
    SeedTriple F m n where
  cluster := Function.update T.cluster k
    ((tropicalEval frozen (T.coeff k / (T.coeff k + 1)) *
          exchangeMonomialPos T.cluster T.exchangeMatrix k +
        tropicalEval frozen (1 / (T.coeff k + 1)) *
          exchangeMonomialNeg T.cluster T.exchangeMatrix k) / T.cluster k)
  coeff j :=
    if j = k then (T.coeff k)⁻¹
    else if T.exchangeMatrix k j ≤ 0 then T.coeff j * (T.coeff k + 1) ^ (-T.exchangeMatrix k j)
    else T.coeff j * ((T.coeff k)⁻¹ + 1) ^ (-T.exchangeMatrix k j)
  exchangeMatrix := matrixMutation le_rfl T.exchangeMatrix k

section Mutation

variable (frozen : FrozenIndex m n → F) (T : SeedTriple F m n) (k : Fin n)

/-- Mutation in direction `k` inverts the coefficient `yₖ`. -/
theorem SeedTriple.mutation_coeff_self : (T.mutation frozen k).coeff k = (T.coeff k)⁻¹ := by
  simp [SeedTriple.mutation]

/-- For `j ≠ k` with `bₖⱼ ≤ 0`, mutation in direction `k` sends `yⱼ` to
`yⱼ (yₖ ⊕ 1) ^ (-bₖⱼ)`. -/
theorem SeedTriple.mutation_coeff_of_nonpos {j : Fin n} (hj : j ≠ k)
    (hb : T.exchangeMatrix k j ≤ 0) :
    (T.mutation frozen k).coeff j = T.coeff j * (T.coeff k + 1) ^ (-T.exchangeMatrix k j) := by
  simp [SeedTriple.mutation, hj, hb]

/-- For `j ≠ k` with `bₖⱼ ≥ 0`, mutation in direction `k` sends `yⱼ` to
`yⱼ (yₖ⁻¹ ⊕ 1) ^ (-bₖⱼ)`. -/
theorem SeedTriple.mutation_coeff_of_nonneg {j : Fin n} (hj : j ≠ k)
    (hb : 0 ≤ T.exchangeMatrix k j) :
    (T.mutation frozen k).coeff j =
      T.coeff j * ((T.coeff k)⁻¹ + 1) ^ (-T.exchangeMatrix k j) := by
  rcases hb.lt_or_eq with hb | hb
  · simp [SeedTriple.mutation, hj, not_le.2 hb]
  · simp [SeedTriple.mutation, hj, ← hb]

/-- Mutation in direction `k` fixes the cluster variable `xⱼ` for `j ≠ k`. -/
theorem SeedTriple.mutation_cluster_of_ne {j : Fin n} (hj : j ≠ k) :
    (T.mutation frozen k).cluster j = T.cluster j := by
  simp [SeedTriple.mutation, hj]

/-- The exchange matrix of the mutation of `(x, y, B)` in direction `k` is `μₖ(B)`. -/
theorem SeedTriple.mutation_exchangeMatrix :
    (T.mutation frozen k).exchangeMatrix = matrixMutation le_rfl T.exchangeMatrix k :=
  rfl

end Mutation

/-- The **frozen variables** `(x_{n+1}, …, xₘ)` of a seed, as a tuple indexed by the frozen
positions. -/
def SeedData.frozenTuple (S : SeedData F m n) : FrozenIndex m n → F :=
  fun i => S.extCluster i.1

/-- The **triple of a labeled seed** `(x̃, B̃)`: its cluster `(x₁, …, xₙ)`, the coefficient tuple
of `B̃`, and the principal part `B` of `B̃`; its frozen variables are `SeedData.frozenTuple`. -/
@[cluster_algebras "def_associated_triple"]
def SeedData.toSeedTriple (hmn : n ≤ m) (S : SeedData F m n) : SeedTriple F m n where
  cluster := cluster hmn S
  coeff := coefficientTuple S.extExchangeMatrix
  exchangeMatrix := principalPart hmn S.extExchangeMatrix

variable (K) in
/-- `P` is a **labeled seed pattern of triples** of rank `n`, with frozen variables `frozen`, when
it assigns a labeled seed triple with these frozen variables to every vertex of `𝕋ₙ` and
`P t'` is the mutation of `P t` in direction `k` whenever `t —k— t'`. -/
@[cluster_algebras "def_triple_pattern"]
def IsTriplePattern (frozen : FrozenIndex m n → F) (P : RegularTree n → SeedTriple F m n) :
    Prop :=
  (∀ t, IsSeedTriple K frozen (P t)) ∧
    ∀ (k : Fin n) (t t' : RegularTree n), RegularTree.Adj k t t' → P t' = (P t).mutation frozen k

end ClusterAlgebras

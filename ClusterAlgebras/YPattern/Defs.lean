/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.SeedPattern

/-!
# `Y`-seeds and `Y`-patterns

The `ŷ`-tuple of a labeled seed `(x̃, B̃)` is `ŷⱼ = ∏ᵢ xᵢ ^ bᵢⱼ`. Under seed mutation it
transforms by a rule governed by the exchange matrix alone, and that rule, taken as a
definition, is `Y`-seed mutation: a `Y`-seed is an `n`-tuple `Y` of elements of a field
together with an `n × n` skew-symmetrizable matrix `B`, and a `Y`-pattern assigns a `Y`-seed to
every vertex of the regular tree `𝕋ₙ` so that the two ends of every edge are related by
`Y`-seed mutation.

## Main definitions

* `ClusterAlgebras.yHat`: the `ŷ`-tuple of a seed.
* `ClusterAlgebras.YSeed`: a `Y`-seed.
* `ClusterAlgebras.YSeed.IsMutation`: two `Y`-seeds are related by `Y`-seed mutation.
* `ClusterAlgebras.IsYPattern`: a `Y`-pattern.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F] {m n : ℕ}

/-- The **`ŷ`-tuple** of a seed `(x̃, B̃)` with `x̃ = (x₁, …, xₘ)`: `ŷⱼ = ∏ᵢ xᵢ ^ bᵢⱼ` for
`j ∈ [1, n]`. FWZ define it for a labeled seed; the formula makes sense for any
data, so it is defined on `SeedData`. -/
@[cluster_algebras "def_yhat"]
def yHat (S : SeedData F m n) (j : Fin n) : F :=
  ∏ i, S.extCluster i ^ S.extExchangeMatrix i j

variable (F n) in
/-- A **`Y`-seed** of rank `n` in `F`: an `n`-tuple `Y = (Y₁, …, Yₙ)` of elements of `F`
together with an `n × n` skew-symmetrizable integer matrix `B`. FWZ take `n ≥ 1`;
nothing here uses it. -/
@[cluster_algebras "def_y_seed"]
structure YSeed where
  /-- The tuple `Y = (Y₁, …, Yₙ)`. -/
  y : Fin n → F
  /-- The exchange matrix `B`. -/
  exchangeMatrix : Matrix (Fin n) (Fin n) ℤ
  /-- The exchange matrix is skew-symmetrizable. -/
  skewSymmetrizable : SkewSymmetrizable exchangeMatrix

/-- The `Y`-seeds `(Y, B)` and `(Y', B')` are **related by `Y`-seed mutation in direction
`k`**: `Yₖ ≠ 0`, `Yₖ ≠ -1`, `B' = μₖ(B)`, and for every `j`
* `Y'ⱼ = Yₖ⁻¹` if `j = k`,
* `Y'ⱼ = Yⱼ (Yₖ + 1) ^ (-bₖⱼ)` if `j ≠ k` and `bₖⱼ ≤ 0`,
* `Y'ⱼ = Yⱼ (Yₖ⁻¹ + 1) ^ (-bₖⱼ)` if `j ≠ k` and `bₖⱼ ≥ 0`. -/
@[cluster_algebras "def_y_seed_mutation"]
def YSeed.IsMutation (k : Fin n) (s s' : YSeed F n) : Prop :=
  s.y k ≠ 0 ∧ s.y k ≠ -1 ∧ s'.exchangeMatrix = matrixMutation le_rfl s.exchangeMatrix k ∧
    ∀ j, (j = k → s'.y j = (s.y k)⁻¹) ∧
      (j ≠ k → s.exchangeMatrix k j ≤ 0 →
        s'.y j = s.y j * (s.y k + 1) ^ (-s.exchangeMatrix k j)) ∧
      (j ≠ k → 0 ≤ s.exchangeMatrix k j →
        s'.y j = s.y j * ((s.y k)⁻¹ + 1) ^ (-s.exchangeMatrix k j))

/-- `P` is a **`Y`-pattern** of rank `n` in `F` when it assigns a `Y`-seed to every vertex of
`𝕋ₙ` and the `Y`-seeds at the two ends of an edge labelled `k` are related by `Y`-seed
mutation in direction `k`. -/
@[cluster_algebras "def_y_pattern"]
def IsYPattern (P : RegularTree n → YSeed F n) : Prop :=
  ∀ (k : Fin n) (t t' : RegularTree n), RegularTree.Adj k t t' → YSeed.IsMutation k (P t) (P t')

end ClusterAlgebras

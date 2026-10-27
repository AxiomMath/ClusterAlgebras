/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.FiniteType.Basic
public import ClusterAlgebras.Cartan.Counterpart

/-!
# Cluster variables and clusters of types `B_n` and `C_n`

A cluster algebra of type `B_n` or `C_n` has `n(n+1)` cluster variables and `binom(2n, n)`
clusters.

## Main results

* `IsSeedPattern.encard_of_isPatternOfType_B`: a seed pattern of type `B_n` has `n(n+1)` cluster
  variables and `binom(2n, n)` clusters.
* `IsSeedPattern.encard_of_isPatternOfType_C`: a seed pattern of type `C_n` has `n(n+1)` cluster
  variables and `binom(2n, n)` clusters.

## Implementation notes

Both statements are exercises of [FWZ, Section 5.5] and are stated as axioms.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 5][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- **Cluster variables and clusters of type `B_n`.** For `n ≥ 2`, a seed pattern of type `B_n`
has `n(n+1)` cluster variables and `binom(2n, n)` distinct clusters. -/
@[cluster_algebras "lem_type_BC_counts_exercise"]
axiom IsSeedPattern.encard_of_isPatternOfType_B [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hn : 2 ≤ n)
    (hX : IsPatternOfType hmn P [DynkinSymbol.B n hn]) :
    (patternClusterVariables hmn P).encard = (n * (n + 1) : ℕ) ∧
      (patternClusters hmn P).encard = ((2 * n).choose n : ℕ)

/-- **Cluster variables and clusters of type `C_n`.** For `n ≥ 3`, a seed pattern of type `C_n`
has `n(n+1)` cluster variables and `binom(2n, n)` distinct clusters. -/
@[cluster_algebras "lem_type_BC_counts_exercise"]
axiom IsSeedPattern.encard_of_isPatternOfType_C [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hn : 3 ≤ n)
    (hX : IsPatternOfType hmn P [DynkinSymbol.C n hn]) :
    (patternClusterVariables hmn P).encard = (n * (n + 1) : ℕ) ∧
      (patternClusters hmn P).encard = ((2 * n).choose n : ℕ)

end ClusterAlgebras

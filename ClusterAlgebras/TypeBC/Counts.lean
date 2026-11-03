/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ClusterAlgebras.TypeBC.External

/-!
# The numbers of cluster variables and clusters of types `B_n` and `C_n`

The columns `B_n` and `C_n` of FWZ's table of the numbers of cluster variables and clusters of
each finite type: `n(n+1)` cluster variables and `binom(2n, n)` clusters. FWZ obtain them from
an exercise, stated in `ClusterAlgebras.TypeBC.External` as a hypothesis; each statement here
takes it as an explicit hypothesis and applies it.

## Main statements

* `ClusterAlgebras.IsSeedPattern.encard_patternClusterVariables_of_isPatternOfType_B` and its
  companions: the counts for types `B_n` (`n ≥ 2`) and `C_n` (`n ≥ 3`).

## Implementation notes

* The number of cluster variables is `(patternClusterVariables hmn P).encard` and the number of
  clusters is `(patternClusters hmn P).encard`, so the statements also record finiteness.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- **The number of cluster variables of type `B_n`.** For `n ≥ 2`, a seed pattern of type `B_n`
has `n(n+1)` cluster variables. -/
@[cluster_algebras "prop_type_BC_counts"]
theorem IsSeedPattern.encard_patternClusterVariables_of_isPatternOfType_B [CharZero K]
    (hmn : n ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hn : 2 ≤ n)
    (hX : IsPatternOfType hmn P [DynkinSymbol.B n hn])
    (hEncardOfIsPatternOfTypeB : IsSeedPattern.EncardOfIsPatternOfTypeB.{u_1, u_2}) :
    (patternClusterVariables hmn P).encard = (n * (n + 1) : ℕ) :=
  (hEncardOfIsPatternOfTypeB hmn hP hn hX).1

/-- **The number of clusters of type `B_n`.** For `n ≥ 2`, a seed pattern of type `B_n` has
`binom(2n, n)` distinct clusters. -/
@[cluster_algebras "prop_type_BC_counts"]
theorem IsSeedPattern.encard_patternClusters_of_isPatternOfType_B [CharZero K]
    (hmn : n ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hn : 2 ≤ n)
    (hX : IsPatternOfType hmn P [DynkinSymbol.B n hn])
    (hEncardOfIsPatternOfTypeB : IsSeedPattern.EncardOfIsPatternOfTypeB.{u_1, u_2}) :
    (patternClusters hmn P).encard = ((2 * n).choose n : ℕ) :=
  (hEncardOfIsPatternOfTypeB hmn hP hn hX).2

/-- **The number of cluster variables of type `C_n`.** For `n ≥ 3`, a seed pattern of type `C_n`
has `n(n+1)` cluster variables. -/
@[cluster_algebras "prop_type_BC_counts"]
theorem IsSeedPattern.encard_patternClusterVariables_of_isPatternOfType_C [CharZero K]
    (hmn : n ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hn : 3 ≤ n)
    (hX : IsPatternOfType hmn P [DynkinSymbol.C n hn])
    (hEncardOfIsPatternOfTypeC : IsSeedPattern.EncardOfIsPatternOfTypeC.{u_1, u_2}) :
    (patternClusterVariables hmn P).encard = (n * (n + 1) : ℕ) :=
  (hEncardOfIsPatternOfTypeC hmn hP hn hX).1

/-- **The number of clusters of type `C_n`.** For `n ≥ 3`, a seed pattern of type `C_n` has
`binom(2n, n)` distinct clusters. -/
@[cluster_algebras "prop_type_BC_counts"]
theorem IsSeedPattern.encard_patternClusters_of_isPatternOfType_C [CharZero K]
    (hmn : n ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hn : 3 ≤ n)
    (hX : IsPatternOfType hmn P [DynkinSymbol.C n hn])
    (hEncardOfIsPatternOfTypeC : IsSeedPattern.EncardOfIsPatternOfTypeC.{u_1, u_2}) :
    (patternClusters hmn P).encard = ((2 * n).choose n : ℕ) :=
  (hEncardOfIsPatternOfTypeC hmn hP hn hX).2

end ClusterAlgebras

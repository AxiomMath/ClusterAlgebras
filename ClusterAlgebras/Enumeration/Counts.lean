/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Cartan.Counterpart
public import ClusterAlgebras.Decomposable.Basic
public import ClusterAlgebras.FiniteType.Basic
public import ClusterAlgebras.TypeA.Finite
public import ClusterAlgebras.TypeBC.Counts
public import ClusterAlgebras.TypeBC.TypeB
public import ClusterAlgebras.TypeBC.TypeC
public import ClusterAlgebras.TypeD.Counts
public import ClusterAlgebras.TypeE.Finite
public import ClusterAlgebras.TypeFG.Counts
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Rat.Defs

/-!
# The numbers of cluster variables and clusters

The beginning of FWZ's Section 5.9. FWZ's table gives, for each Dynkin symbol `X`, the number
`N(X)` of cluster variables and the number `K(X)` of clusters of a seed pattern of type `X`;
for a list of symbols `N` is additive and `K` multiplicative. A seed pattern of type `X` is of
finite type with these numbers, and the pair `(N, K)` separates the Dynkin symbols of each rank
except `B_n` and `C_n`.

## Main definitions

* `ClusterAlgebras.DynkinSymbol.numClusterVariables X`, `DynkinSymbol.numClusters X`: the
  numbers `N(X)` and `K(X)`, as rational numbers, as FWZ state them.
* `ClusterAlgebras.DynkinSymbol.listNumClusterVariables`, `DynkinSymbol.listNumClusters`:
  their extensions to lists of symbols.

## Main statements

* `ClusterAlgebras.IsSeedPattern.counts_of_isPatternOfType`: a seed pattern of type `X` is of
  finite type with `N(X)` cluster variables and `K(X)` clusters.
* `ClusterAlgebras.DynkinSymbol.eq_or_B_C_of_counts`: the pair `(N, K)` separates the Dynkin
  symbols of each rank, except `B_n` and `C_n`.

## Implementation notes

* `N(X)` and `K(X)` are defined in `ℚ` by FWZ's formulas, so that no integer division is
  hidden in the definition; the counts are then stated as natural numbers whose casts are
  `N(X)` and `K(X)`.
* FWZ assert that `N` alone separates the connected Dynkin types of a rank other than `B_n` and
  `C_n`; this fails in rank `6`, where `E_6`, `B_6` and `C_6` all have `42` cluster variables, so
  the pair is used.
-/

@[expose] public section

namespace ClusterAlgebras

namespace DynkinSymbol

/-- The number `N(X)` of cluster variables of a Dynkin symbol `X`: `N(A_n) = n(n+3)/2`,
`N(B_n) = N(C_n) = n(n+1)`, `N(D_n) = n²`, `N(E_6) = 42`, `N(E_7) = 70`, `N(E_8) = 128`,
`N(F_4) = 28`, `N(G_2) = 8`. -/
@[cluster_algebras "def_dynkin_counts"]
def numClusterVariables : DynkinSymbol → ℚ
  | A n _ => (n : ℚ) * (n + 3) / 2
  | B n _ => (n : ℚ) * (n + 1)
  | C n _ => (n : ℚ) * (n + 1)
  | D n _ => (n : ℚ) ^ 2
  | E n _ => if n = 6 then 42 else if n = 7 then 70 else 128
  | F₄ => 28
  | G₂ => 8

/-- The number `K(X)` of clusters of a Dynkin symbol `X`: `K(A_n) = binom(2n+2, n+1)/(n+2)`,
`K(B_n) = K(C_n) = binom(2n, n)`, `K(D_n) = (3n-2)/n · binom(2n-2, n-1)`, `K(E_6) = 833`,
`K(E_7) = 4160`, `K(E_8) = 25080`, `K(F_4) = 105`, `K(G_2) = 8`. -/
@[cluster_algebras "def_dynkin_counts"]
def numClusters : DynkinSymbol → ℚ
  | A n _ => ((2 * n + 2).choose (n + 1) : ℚ) / (n + 2)
  | B n _ => ((2 * n).choose n : ℚ)
  | C n _ => ((2 * n).choose n : ℚ)
  | D n _ => (3 * (n : ℚ) - 2) / n * ((2 * n - 2).choose (n - 1) : ℚ)
  | E n _ => if n = 6 then 833 else if n = 7 then 4160 else 25080
  | F₄ => 105
  | G₂ => 8

/-- The number `N(X) = ∑ₛ N(X^s)` of a list `X = (X¹, …, X^r)` of Dynkin symbols. -/
@[cluster_algebras "def_dynkin_counts"]
def listNumClusterVariables (Xs : List DynkinSymbol) : ℚ :=
  (Xs.map numClusterVariables).sum

/-- The number `K(X) = ∏ₛ K(X^s)` of a list `X = (X¹, …, X^r)` of Dynkin symbols. -/
@[cluster_algebras "def_dynkin_counts"]
def listNumClusters (Xs : List DynkinSymbol) : ℚ :=
  (Xs.map numClusters).prod

/-- **The two numbers separate the Dynkin symbols of each rank, except `B_n` and `C_n`.** If
`X` and `Y` have the same rank and the same numbers `N` and `K`, then `X = Y`, or the rank `n`
is at least `3` and `{X, Y} = {B_n, C_n}`. -/
@[cluster_algebras "lem_counts_distinguish_symbols"]
theorem eq_or_B_C_of_counts {X Y : DynkinSymbol} (hrank : X.rank = Y.rank)
    (hN : X.numClusterVariables = Y.numClusterVariables) (hK : X.numClusters = Y.numClusters) :
    X = Y ∨ ∃ (n : ℕ) (hn : 3 ≤ n),
      (X = B n (by omega) ∧ Y = C n hn) ∨ (X = C n hn ∧ Y = B n (by omega)) := by
  rcases X with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, ⟨hn₁, hn₂⟩⟩ | _ | _ <;>
  rcases Y with ⟨n', hn'⟩ | ⟨n', hn'⟩ | ⟨n', hn'⟩ | ⟨n', hn'⟩ | ⟨n', ⟨hn₁', hn₂'⟩⟩ | _ | _ <;>
  simp only [rank] at hrank <;> try subst hrank
  all_goals simp only [numClusterVariables, numClusters] at hN hK
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, hn', Or.inl ⟨rfl, rfl⟩⟩
    | exact Or.inr ⟨_, hn, Or.inr ⟨rfl, rfl⟩⟩
    | exfalso
  -- The remaining pairs are told apart by `N`, except `E₆` against `B₆` and `C₆`, told apart
  -- by `K`.
  all_goals first
    | (norm_num at hN; done)
    | (interval_cases n <;> first | (norm_num at hN; done) | norm_num [Nat.choose] at hK)
    | (have h4 : (4 : ℚ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
       nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℚ) ≤ n)])
    | (have h2 : (2 : ℚ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
       nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℚ) ≤ n)])

end DynkinSymbol

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- `N(A_n) = n(n+3)/2`, an integer. -/
private theorem cast_eq_numClusterVariables_A (n : ℕ) (hn : 1 ≤ n) :
    ((n * (n + 3) / 2 : ℕ) : ℚ) = (DynkinSymbol.A n hn).numClusterVariables := by
  have h2 : 2 ∣ n * (n + 3) := by
    rcases Nat.even_or_odd n with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact ⟨a * (a + a + 3), by ring⟩
    · exact ⟨(2 * a + 1) * (a + 2), by ring⟩
  rw [Nat.cast_div_charZero h2]
  push_cast
  rfl

/-- `K(A_n)` is the Catalan number `C_{n+1}`. -/
private theorem cast_catalanNumber_eq_numClusters_A (n : ℕ) (hn : 1 ≤ n) :
    (catalanNumber (n + 1) : ℚ) = (DynkinSymbol.A n hn).numClusters := by
  have h := succ_mul_catalan_eq_centralBinom (n + 1)
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (n + 1) = 2 * n + 2 by ring] at h
  simp only [DynkinSymbol.numClusters, catalanNumber]
  rw [eq_div_iff (by positivity), ← h]
  push_cast
  ring

/-- `K(D_n)` is the solution `k` of `n k = (3n - 2) binom(2n-2, n-1)`. -/
private theorem cast_eq_numClusters_D {n k : ℕ} (hn : 4 ≤ n)
    (hkn : n * k = (3 * n - 2) * (2 * n - 2).choose (n - 1)) :
    (k : ℚ) = (DynkinSymbol.D n hn).numClusters := by
  have hq : (n : ℚ) * k = (3 * n - 2) * ((2 * n - 2).choose (n - 1) : ℕ) := by
    have := congrArg (Nat.cast : ℕ → ℚ) hkn
    push_cast [Nat.cast_sub (show 2 ≤ 3 * n by omega)] at this
    exact this
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  simp only [DynkinSymbol.numClusters]
  rw [div_mul_eq_mul_div, eq_div_iff hn0, ← hq]
  ring

/-- **Numbers of cluster variables and clusters, connected case**: a seed pattern of type `[X]`
for a single Dynkin symbol `X` is of finite type, has `N(X)` cluster variables and `K(X)`
clusters. -/
theorem IsSeedPattern.counts_of_isPatternOfType_singleton [CharZero K] {X : DynkinSymbol}
    (hmn : X.rank ≤ m) {P : RegularTree X.rank → SeedData F m X.rank}
    (hP : IsSeedPattern K hmn P) (hX : IsPatternOfType hmn P [X]) :
    IsFiniteType P ∧
      (∃ N : ℕ, (patternClusterVariables hmn P).encard = N ∧
        (N : ℚ) = X.numClusterVariables) ∧
      ∃ k : ℕ, (patternClusters hmn P).encard = k ∧ (k : ℚ) = X.numClusters := by
  cases X with
  | A n hn =>
    exact ⟨hP.isFiniteType_of_typeA hn hmn hX,
      ⟨_, hP.encard_patternClusterVariables_of_typeA hn hmn hX,
        cast_eq_numClusterVariables_A n hn⟩,
      ⟨_, hP.encard_patternClusters_of_typeA hn hmn hX, cast_catalanNumber_eq_numClusters_A n hn⟩⟩
  | B n hn =>
    exact ⟨hP.isFiniteType_of_isPatternOfType_B hmn hn hX,
      ⟨_, hP.encard_patternClusterVariables_of_isPatternOfType_B hmn hn hX, by
        push_cast; rfl⟩,
      ⟨_, hP.encard_patternClusters_of_isPatternOfType_B hmn hn hX, rfl⟩⟩
  | C n hn =>
    exact ⟨hP.isFiniteType_of_isPatternOfType_C hmn hn hX,
      ⟨_, hP.encard_patternClusterVariables_of_isPatternOfType_C hmn hn hX, by
        push_cast; rfl⟩,
      ⟨_, hP.encard_patternClusters_of_isPatternOfType_C hmn hn hX, rfl⟩⟩
  | D n hn =>
    obtain ⟨hN, k, hk, hkn⟩ := hP.encard_of_isPatternOfType_D hn hmn hX
    exact ⟨hP.isFiniteType_of_isPatternOfType_D hn hmn hX, ⟨_, hN, by push_cast; rfl⟩,
      ⟨k, hk, cast_eq_numClusters_D hn hkn⟩⟩
  | E n hn =>
    refine ⟨hP.isFiniteType_of_isPatternOfType_E hn hmn hX, ?_⟩
    obtain rfl | rfl | rfl : n = 6 ∨ n = 7 ∨ n = 8 := by omega
    · obtain ⟨hN, hk⟩ := hP.encard_of_isPatternOfType_E6 hmn hX
      exact ⟨⟨42, hN, by norm_num [DynkinSymbol.numClusterVariables]⟩,
        ⟨833, hk, by norm_num [DynkinSymbol.numClusters]⟩⟩
    · obtain ⟨hN, hk⟩ := hP.encard_of_isPatternOfType_E7 hmn hX
      exact ⟨⟨70, hN, by norm_num [DynkinSymbol.numClusterVariables]⟩,
        ⟨4160, hk, by norm_num [DynkinSymbol.numClusters]⟩⟩
    · obtain ⟨hN, hk⟩ := hP.encard_of_isPatternOfType_E8 hmn hX
      exact ⟨⟨128, hN, by norm_num [DynkinSymbol.numClusterVariables]⟩,
        ⟨25080, hk, by norm_num [DynkinSymbol.numClusters]⟩⟩
  | F₄ =>
    obtain ⟨hN, hk⟩ := hP.encard_of_isPatternOfType_F₄ hmn hX
    exact ⟨hP.isFiniteType_of_isPatternOfType_F₄ hmn hX,
      ⟨28, hN, by norm_num [DynkinSymbol.numClusterVariables]⟩,
      ⟨105, hk, by norm_num [DynkinSymbol.numClusters]⟩⟩
  | G₂ =>
    obtain ⟨hN, hk⟩ := hP.encard_of_isPatternOfType_G₂ hmn hX
    exact ⟨hP.isFiniteType_of_isPatternOfType_G₂ hmn hX,
      ⟨8, hN, by norm_num [DynkinSymbol.numClusterVariables]⟩,
      ⟨8, hk, by norm_num [DynkinSymbol.numClusters]⟩⟩

/-- **Numbers of cluster variables and clusters.** FWZ's `pr:number-of-clusters`, without the
formulas in terms of exponents and the Coxeter number: a seed pattern of type
`X = (X¹, …, X^r)` is of finite type, has `N(X)` cluster variables and `K(X)` clusters.
FWZ take `r ≥ 1`; for `r = 0` the pattern has rank `0`, no cluster variables and the one
empty cluster, which are `N = 0` and `K = 1`, so that is not assumed. -/
@[cluster_algebras "prop_cluster_counts"]
theorem IsSeedPattern.counts_of_isPatternOfType [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {Xs : List DynkinSymbol}
    (hX : IsPatternOfType hmn P Xs) :
    IsFiniteType P ∧
      (∃ N : ℕ, (patternClusterVariables hmn P).encard = N ∧
        (N : ℚ) = DynkinSymbol.listNumClusterVariables Xs) ∧
      ∃ k : ℕ, (patternClusters hmn P).encard = k ∧ (k : ℚ) = DynkinSymbol.listNumClusters Xs := by
  obtain ⟨hle, Q, hQ, hfinP, hcount⟩ := hP.exists_blocks_of_isPatternOfType hmn hX
  have h s := counts_of_isPatternOfType_singleton (hle s) (hQ s).1 (hQ s).2
  choose N hN using fun s => (h s).2.1
  choose k hk using fun s => (h s).2.2
  have hfin : IsFiniteType P := hfinP.2 fun s => (h s).1
  refine ⟨hfin, ⟨∑ s, N s, ?_, ?_⟩, ∏ s, k s, ?_, ?_⟩
  · rw [(hcount hfin).1]
    simp [fun s => (hN s).1]
  · push_cast
    simp only [fun s => (hN s).2, DynkinSymbol.listNumClusterVariables, List.get_eq_getElem]
    exact Fin.sum_univ_fun_getElem Xs _
  · rw [(hcount hfin).2]
    simp [fun s => (hk s).1]
  · push_cast
    simp only [fun s => (hk s).2, DynkinSymbol.listNumClusters, List.get_eq_getElem]
    exact Fin.prod_univ_fun_getElem Xs _

end ClusterAlgebras

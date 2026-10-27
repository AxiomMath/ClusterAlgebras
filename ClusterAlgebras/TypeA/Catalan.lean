/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Catalan numbers

The Catalan numbers `c_N`, defined by `c₀ = 1` and `c_{N+1} = ∑_{i=0}^{N} cᵢ c_{N-i}`, and their
closed form `(N + 1) c_N = binom(2N, N)`. They count the triangulations of a polygon in type
`A_n` and enter the counts of type `D_n`.

## Implementation notes

* Mathlib's `catalan` is defined by exactly this recurrence, so `catalanNumber` is an
  abbreviation for it rather than a second notion, and Mathlib's lemmas apply to it directly.
-/

@[expose] public section

namespace ClusterAlgebras

/-- The **Catalan numbers** `c_N`: `c₀ = 1` and `c_{N+1} = ∑_{i=0}^{N} cᵢ c_{N-i}`. This is
Mathlib's `catalan`, which is defined by this recurrence; see `catalanNumber_zero` and
`catalanNumber_succ`. -/
@[cluster_algebras "def_catalan"]
abbrev catalanNumber (N : ℕ) : ℕ :=
  catalan N

/-- `c₀ = 1`. -/
@[cluster_algebras "def_catalan"]
theorem catalanNumber_zero : catalanNumber 0 = 1 :=
  catalan_zero

/-- `c_{N+1} = ∑_{i=0}^{N} cᵢ c_{N-i}`. -/
@[cluster_algebras "def_catalan"]
theorem catalanNumber_succ (N : ℕ) :
    catalanNumber (N + 1) =
      ∑ i ∈ Finset.range (N + 1), catalanNumber i * catalanNumber (N - i) := by
  rw [catalanNumber, catalan_succ, Finset.sum_range (fun i => catalan i * catalan (N - i))]

/-- **Closed form of the Catalan numbers**: `(N + 1) c_N = binom(2N, N)`, that is
`c_N = binom(2N, N) / (N + 1)`. -/
@[cluster_algebras "lem_catalan_closed_form"]
theorem succ_mul_catalanNumber (N : ℕ) : (N + 1) * catalanNumber N = Nat.centralBinom N :=
  succ_mul_catalan_eq_centralBinom N

end ClusterAlgebras

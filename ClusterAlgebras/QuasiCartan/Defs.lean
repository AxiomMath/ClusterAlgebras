/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Cartan.Counterpart
public import ClusterAlgebras.FiniteType.RankTwo
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Quasi-Cartan companions: the vocabulary of FWZ's Section 5.11

The criterion of Barot, Geiss and Zelevinsky characterizes the `2`-finite skew-symmetrizable
matrices `B` by a condition on `B` alone: every chordless cycle of its diagram is cyclically
oriented, and `B` has a positive quasi-Cartan companion. This file holds the definitions.

## Main definitions

* `ClusterAlgebras.IsQuasiCartan A`, `ClusterAlgebras.IsPositiveQuasiCartan A`: quasi-Cartan
  matrices, and positive ones.
* `ClusterAlgebras.IsQuasiCartanCompanion B A`: `A` is a quasi-Cartan companion of `B`.
* `ClusterAlgebras.IsQCEdge B e`, `ClusterAlgebras.qcEdgesOf B Z`: the edges of `B`, and those
  contained in `Z`.
* `ClusterAlgebras.IsQCChordlessCycle B Z`, `IsQCCyclicallyOriented B Z`: chordless cycles,
  recorded as sets, and cyclically oriented ones.
* `ClusterAlgebras.SatisfiesQCSignCondition B A Z`, `IsAdmissibleCompanion B A`: the sign
  condition, and admissible companions.
* `ClusterAlgebras.SatisfiesBGZ B`: the Barot–Geiss–Zelevinsky condition.
* `ClusterAlgebras.qcSignChange ε A`: the simultaneous sign change `ε · A`.

## Implementation notes

* Indices are `Fin n`, so FWZ's `[1, n]` is shifted down by one.
* An edge `{i, j}` is an element `s(i, j)` of `Sym2 (Fin n)` off the diagonal.
* A symmetrizer is `ClusterAlgebras.IsSymmetrizer`, a vector of positive integers `d` with
  `dᵢ aᵢⱼ = dⱼ aⱼᵢ`, as for generalized Cartan matrices.
* The sign condition is FWZ's parity condition: the number of edges `{i, j}` of `Z` with
  `aᵢⱼ > 0` is odd. It is counted with `Set.ncard`, the set being finite.
* A sign vector is a function `Fin n → ℤˣ`, the units of `ℤ` being `±1`.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

/-! ### Quasi-Cartan matrices and companions -/

/-- A **quasi-Cartan matrix**: an integer matrix `A` with `aᵢᵢ = 2` for all `i` and a
symmetrizer, a diagonal matrix `D` with positive integer entries `d₁, …, dₙ` and `DA`
symmetric. Unlike a generalized Cartan matrix, it may have positive off-diagonal entries. -/
@[cluster_algebras "def_qc_quasi_cartan"]
def IsQuasiCartan (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i, A i i = 2) ∧ ∃ d, IsSymmetrizer A d

/-- A quasi-Cartan matrix `A` is **positive** when for some symmetrizer `D = diag(d)` the
symmetric matrix `DA` is positive definite: `vᵀ D A v > 0` for every nonzero `v ∈ ℝⁿ`. -/
@[cluster_algebras "def_qc_positive"]
def IsPositiveQuasiCartan (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsQuasiCartan A ∧ ∃ d, IsSymmetrizer A d ∧
    ∀ v : Fin n → ℝ, v ≠ 0 →
      0 < v ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ v)

/-- A **quasi-Cartan companion** of the integer matrix `B`: a quasi-Cartan matrix `A` with
`|aᵢⱼ| = |bᵢⱼ|` for all `i ≠ j`. FWZ take `B` skew-symmetrizable; the definition makes
sense for every `B`. -/
@[cluster_algebras "def_qc_companion"]
def IsQuasiCartanCompanion (B A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsQuasiCartan A ∧ ∀ i j, i ≠ j → |A i j| = |B i j|

/-! ### Edges and chordless cycles -/

/-- An **edge** of `B`: a two-element set `{i, j}` with `bᵢⱼ bⱼᵢ ≠ 0`. -/
@[cluster_algebras "def_qc_edge"]
def IsQCEdge (B : Matrix (Fin n) (Fin n) ℤ) (e : Sym2 (Fin n)) : Prop :=
  ∃ i j, e = s(i, j) ∧ i ≠ j ∧ B i j * B j i ≠ 0

/-- The **edges of `Z`**: the edges of `B` contained in `Z`. -/
@[cluster_algebras "def_qc_edge"]
def qcEdgesOf (B : Matrix (Fin n) (Fin n) ℤ) (Z : Finset (Fin n)) : Set (Sym2 (Fin n)) :=
  {e | IsQCEdge B e ∧ ∀ i ∈ e, i ∈ Z}

/-- A **cyclic enumeration** of `Z ⊆ [1, n]` for `B`: a bijection `v : ℤ/p → Z`, `p ≥ 3`, such
that for all `s ≠ t` in `ℤ/p`, `{v(s), v(t)}` is an edge of `B` exactly when `t = s + 1` or
`t = s - 1`. The bijection is a map `ZMod p → Fin n`, injective with image `Z`. -/
@[cluster_algebras "def_qc_chordless_cycle"]
def IsQCCyclicEnumeration (B : Matrix (Fin n) (Fin n) ℤ) (Z : Finset (Fin n)) {p : ℕ}
    (v : ZMod p → Fin n) : Prop :=
  3 ≤ p ∧ Function.Injective v ∧ Set.range v = (Z : Set (Fin n)) ∧
    ∀ s t : ZMod p, s ≠ t → (IsQCEdge B s(v s, v t) ↔ t = s + 1 ∨ t = s - 1)

/-- A **chordless cycle** of `B`: a set `Z ⊆ [1, n]` with a cyclic enumeration. These are the
vertex sets of the induced cycles of the underlying graph of `Γ(B)`. -/
@[cluster_algebras "def_qc_chordless_cycle"]
def IsQCChordlessCycle (B : Matrix (Fin n) (Fin n) ℤ) (Z : Finset (Fin n)) : Prop :=
  ∃ (p : ℕ) (v : ZMod p → Fin n), IsQCCyclicEnumeration B Z v

/-- A chordless cycle `Z` of `B` is **cyclically oriented** when it has a cyclic enumeration
`v` with `b_{v(s) v(s+1)} > 0` for every `s ∈ ℤ/p`. -/
@[cluster_algebras "def_qc_cyclically_oriented"]
def IsQCCyclicallyOriented (B : Matrix (Fin n) (Fin n) ℤ) (Z : Finset (Fin n)) : Prop :=
  ∃ (p : ℕ) (v : ZMod p → Fin n), IsQCCyclicEnumeration B Z v ∧ ∀ s, 0 < B (v s) (v (s + 1))

/-! ### The sign condition and the criterion -/

/-- A quasi-Cartan companion `A` of `B` **satisfies the sign condition on** the chordless
cycle `Z` when the number of edges `{i, j}` of `Z` with `aᵢⱼ > 0` is odd. -/
@[cluster_algebras "def_qc_sign_condition"]
def SatisfiesQCSignCondition (B A : Matrix (Fin n) (Fin n) ℤ) (Z : Finset (Fin n)) : Prop :=
  Odd {e | e ∈ qcEdgesOf B Z ∧ ∃ i j, e = s(i, j) ∧ 0 < A i j}.ncard

/-- A quasi-Cartan companion `A` of `B` is **admissible** when it satisfies the sign condition
on every chordless cycle of `B`. -/
@[cluster_algebras "def_qc_sign_condition"]
def IsAdmissibleCompanion (B A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsQuasiCartanCompanion B A ∧
    ∀ Z, IsQCChordlessCycle B Z → SatisfiesQCSignCondition B A Z

/-- `B` satisfies the **Barot–Geiss–Zelevinsky condition** when every chordless cycle of `B` is
cyclically oriented and `B` has a positive quasi-Cartan companion. -/
@[cluster_algebras "def_qc_bgz_condition"]
def SatisfiesBGZ (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ Z, IsQCChordlessCycle B Z → IsQCCyclicallyOriented B Z) ∧
    ∃ A, IsQuasiCartanCompanion B A ∧ IsPositiveQuasiCartan A

/-! ### Simultaneous sign changes -/

/-- The **simultaneous sign change** `ε · A` of an `n × n` matrix by a sign vector
`ε = (ε₁, …, εₙ)`, `εᵢ ∈ {1, -1}`: the matrix with entries `εᵢ εⱼ aᵢⱼ`. -/
@[cluster_algebras "def_qc_sign_change"]
def qcSignChange (ε : Fin n → ℤˣ) (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => (ε i : ℤ) * ε j * A i j

end ClusterAlgebras

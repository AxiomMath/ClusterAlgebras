/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import Mathlib
public import ClusterAlgebras.Attr
public import ClusterAlgebras.Definitions

/-!
# Skew-symmetrization, and the diagram of a matrix

For a real matrix `B` indexed by a type `ι`, this file studies its **skew-symmetrization**
`skewSymmetrization B`, the matrix with entries `s i j = sgn (b i j) * √|b i j * b j i|`,
and its **diagram** `diagram B`, the directed graph on `ι` whose edges are the pairs where
`B` is positive, each weighted by `|b i j * b j i|`.

## Main definitions

* `skewSymmetrization`: the matrix with entries `sgn (b i j) * √|b i j * b j i|`.

## Main results

* `skewSymmetrization_apply_self`: skew-symmetrization fixes the diagonal entries.
* `sq_skewSymmetrization`: the square of an entry of `skewSymmetrization B` is
  `|b i j * b j i|`.
* `skewSymmetrization_pos_iff`: an entry of `skewSymmetrization B` is positive exactly when
  `b i j` is positive and `b j i` is nonzero.
* `diagram_eq_iff`: two matrices have the same diagram exactly when the same entries are
  positive and the weights `|b i j * b j i|` agree at those entries.
* `Diagram.Connected.eq_univ`: in a connected diagram, a nonempty set of vertices joined to
  its complement by no edge, in either direction, is the whole index type.

## Implementation notes

* Neither construction assumes `B` skew-symmetrizable; that hypothesis is carried by the
  lemmas that need it.
* Both are defined over an arbitrary index type rather than `Fin n`, since every formula is
  entrywise.
* A `Diagram` records its edge set as well as its weight function: for an arbitrary matrix,
  `b i j > 0 = b j i` gives an edge of weight zero. The weight vanishes off the edges.
-/

@[expose] public section

namespace ClusterAlgebras

variable {ι : Type*}

/-! ### Skew-symmetrization -/

/-- The **skew-symmetrization** `S(B)` of a real matrix `B`: the matrix with entries
`s i j = sgn (b i j) * √|b i j * b j i|`.

For a skew-symmetrizable `B` this is the skew-symmetric matrix obtained from `B` by the
diagonal conjugation `b i j ↦ √(d i / d j) * b i j` of any skew-symmetrizing vector `d`. -/
@[cluster_algebras "def_skew_symmetrization"]
noncomputable def skewSymmetrization (B : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  .of fun i j => Real.sign (B i j) * √|B i j * B j i|

/-- The entries of `S(B)`, by definition: the sign of `b i j` times the square root of the
weight `|b i j * b j i|`. -/
theorem skewSymmetrization_apply (B : Matrix ι ι ℝ) (i j : ι) :
    skewSymmetrization B i j = Real.sign (B i j) * √|B i j * B j i| :=
  rfl

/-- At a positive entry the skew-symmetrization is the positive square root of the
weight. -/
theorem skewSymmetrization_apply_of_pos {B : Matrix ι ι ℝ} {i j : ι} (h : 0 < B i j) :
    skewSymmetrization B i j = √|B i j * B j i| := by
  rw [skewSymmetrization_apply, Real.sign_of_pos h, one_mul]

/-- At a negative entry the skew-symmetrization is the negative square root of the
weight. -/
theorem skewSymmetrization_apply_of_neg {B : Matrix ι ι ℝ} {i j : ι} (h : B i j < 0) :
    skewSymmetrization B i j = -√|B i j * B j i| := by
  rw [skewSymmetrization_apply, Real.sign_of_neg h, neg_one_mul]

/-- An entry of the skew-symmetrization vanishes wherever the corresponding entry does. -/
@[simp]
theorem skewSymmetrization_apply_of_eq_zero {B : Matrix ι ι ℝ} {i j : ι} (h : B i j = 0) :
    skewSymmetrization B i j = 0 := by
  rw [skewSymmetrization_apply, h, Real.sign_zero, zero_mul]

/-- Skew-symmetrization leaves the diagonal entries unchanged. -/
@[simp]
theorem skewSymmetrization_apply_self (B : Matrix ι ι ℝ) (i : ι) :
    skewSymmetrization B i i = B i i := by
  rw [skewSymmetrization_apply, abs_mul_self, ← sq, Real.sqrt_sq_eq_abs]
  rcases lt_trichotomy (B i i) 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · simp [h]
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

/-- The square of an entry of the skew-symmetrization is `|b i j * b j i|`, with no positivity
hypothesis. On an edge of `Γ(B)` this is the edge's weight. -/
theorem sq_skewSymmetrization (B : Matrix ι ι ℝ) (i j : ι) :
    skewSymmetrization B i j ^ 2 = |B i j * B j i| := by
  rcases eq_or_ne (B i j) 0 with h | h
  · rw [skewSymmetrization_apply_of_eq_zero h, h]
    simp
  · rw [skewSymmetrization_apply, mul_pow, Real.sq_sqrt (abs_nonneg _)]
    rcases Real.sign_apply_eq_of_ne_zero _ h with h' | h' <;> rw [h'] <;> norm_num

/-- Skew-symmetrization keeps the entries that are positive positive, except that it
destroys a positive entry whose mirror vanishes. Over a skew-symmetrizable matrix the
exception is empty. -/
theorem skewSymmetrization_pos_iff {B : Matrix ι ι ℝ} {i j : ι} :
    0 < skewSymmetrization B i j ↔ 0 < B i j ∧ B j i ≠ 0 := by
  refine ⟨fun h => ?_, fun ⟨hb, hb'⟩ => ?_⟩
  · rcases lt_trichotomy (B i j) 0 with hb | hb | hb
    · rw [skewSymmetrization_apply_of_neg hb, neg_pos] at h
      exact absurd (Real.sqrt_nonneg _) h.not_ge
    · simp [skewSymmetrization_apply_of_eq_zero hb] at h
    · refine ⟨hb, fun hb' => ?_⟩
      simp [skewSymmetrization_apply, hb'] at h
  · rw [skewSymmetrization_apply_of_pos hb]
    exact Real.sqrt_pos.2 (abs_pos.2 (mul_ne_zero hb.ne' hb'))

/-! ### Diagrams -/

attribute [ext, cluster_algebras "def_diagram"] Diagram

attribute [cluster_algebras "def_diagram"] diagram

/-- The edges of `Γ(B)` are the pairs on which `B` is positive. -/
theorem edges_diagram (B : Matrix ι ι ℝ) : (diagram B).edges = {p | 0 < B p.1 p.2} :=
  rfl

/-- Membership in the edge set of `Γ(B)`, unfolded. -/
@[simp]
theorem mem_edges_diagram {B : Matrix ι ι ℝ} {p : ι × ι} :
    p ∈ (diagram B).edges ↔ 0 < B p.1 p.2 :=
  Iff.rfl

/-- The weight `Γ(B)` puts on a pair `(i, j)`: `|b i j * b j i|` if `b i j` is positive, and `0`
otherwise. -/
theorem weight_diagram (B : Matrix ι ι ℝ) (p : ι × ι) :
    (diagram B).weight p = if 0 < B p.1 p.2 then |B p.1 p.2 * B p.2 p.1| else 0 :=
  rfl

/-- The weight of an edge of `Γ(B)`. -/
@[simp]
theorem weight_diagram_of_pos {B : Matrix ι ι ℝ} {i j : ι} (h : 0 < B i j) :
    (diagram B).weight (i, j) = |B i j * B j i| :=
  if_pos h

/-- Two matrices have the same diagram exactly when the same entries are positive and the
weights `|b i j * b j i|` agree wherever they are. -/
theorem diagram_eq_iff {B B' : Matrix ι ι ℝ} :
    diagram B = diagram B' ↔
      ∀ i j, (0 < B i j ↔ 0 < B' i j) ∧
        (0 < B i j → |B i j * B j i| = |B' i j * B' j i|) := by
  refine ⟨fun h i j => ?_, fun h => ?_⟩
  · have he : 0 < B i j ↔ 0 < B' i j := by
      rw [← mem_edges_diagram (p := (i, j)), h, mem_edges_diagram]
    exact ⟨he, fun hb => by rw [← weight_diagram_of_pos hb, h, weight_diagram_of_pos (he.1 hb)]⟩
  · ext ⟨i, j⟩
    · exact (h i j).1
    · rw [weight_diagram, weight_diagram]
      by_cases hp : 0 < B i j
      · rw [if_pos hp, if_pos ((h i j).1.1 hp), (h i j).2 hp]
      · rw [if_neg hp, if_neg fun hp' => hp ((h i j).1.2 hp')]

attribute [cluster_algebras "def_diagram_connected"] Diagram.Connected

/-- In a connected diagram, a nonempty set that no edge joins to its complement, in either
direction, is the whole index type. -/
theorem Diagram.Connected.eq_univ {Γ : Diagram ι} (hΓ : Γ.Connected) {P : Set ι}
    (hP : P.Nonempty) (hsep : ∀ i ∈ P, ∀ j ∉ P, (i, j) ∉ Γ.edges ∧ (j, i) ∉ Γ.edges) :
    P = Set.univ := by
  by_contra hne
  obtain ⟨i, hi, j, hj, hij⟩ := hΓ P hP (Set.nonempty_compl.2 hne)
  exact hij.elim (hsep i hi j hj).1 (hsep i hi j hj).2

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeA.Catalan
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Prod

/-!
# Triangulations of an integer interval and the Catalan numbers

Reading a convex polygon linearly from a base point turns a triangulation of the polygon into
a triangulation of the integer interval `[0, m-1]`. This file sets up that linear model:
interleaving pairs, the sides and diagonals of `[a, b]`, its triangulations, and their number
`τ(a, b)`, which is the Catalan number `c_{b-a-1}`.

## Main definitions

* `ClusterAlgebras.TypeA.Interleave`: two pairs of integers interleave.
* `ClusterAlgebras.TypeA.intervalSides`, `ClusterAlgebras.TypeA.intervalDiagonals`: the sides
  and the set `D[a,b]` of diagonals of `[a, b]`.
* `ClusterAlgebras.TypeA.IsIntervalTriangulation`: a triangulation of `[a, b]`.
* `ClusterAlgebras.TypeA.intervalSegments`: the segments of a triangulation of `[a, b]`.
* `ClusterAlgebras.TypeA.intervalTriangulationCount`: the number `τ(a, b)` of triangulations.

## Main statements

* `ClusterAlgebras.TypeA.IsIntervalTriangulation.existsUnique_apex`: over a segment `{i, k}`
  with `k ≥ i + 2` there is exactly one apex `j`.
* `ClusterAlgebras.TypeA.exists_equiv_intervalTriangulation`: cutting at the apex of the base is
  a bijection onto triples `(k, S₁, S₂)`.
* `ClusterAlgebras.TypeA.intervalTriangulationCount_eq_catalanNumber`: `τ(a, b) = c_{b-a-1}`.

## Implementation notes

* **A two-element set `{i, j}` of integers with `i < j` is the pair `(i, j) : ℤ × ℤ`.** The
  sets are unordered; listing them increasingly makes every set a unique pair, and all the
  definitions here (interleaving, sides, diagonals) are stated for increasing pairs. Statements
  about "a two-element subset `{i, j}` of `[a, b]`" carry the hypotheses `a ≤ i < j ≤ b`.
* `intervalTriangulations a b` is the finite set of triangulations, computed as a filter of the
  powerset of `D[a, b]`, so `τ(a, b)` is a `Finset.card` and can be evaluated (`#eval` gives
  `1, 1, 2, 5, 14, 42, 132` for `b - a = 1, …, 7`).
-/

@[expose] public section

namespace ClusterAlgebras

namespace TypeA

/-! ### Interleaving, sides and diagonals -/

/-- Two two-element sets of integers `{i, j}` and `{k, l}`, given as increasing pairs `(i, j)` and
`(k, l)`, **interleave** if `i < k < j < l` or `k < i < l < j`. -/
@[cluster_algebras "def_interval_triangulation"]
def Interleave (p q : ℤ × ℤ) : Prop :=
  (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2) ∨ (q.1 < p.1 ∧ p.1 < q.2 ∧ q.2 < p.2)

/-- Interleaving is decidable: it is a condition on four integers. -/
instance instDecidableRelInterleave : DecidableRel Interleave := fun _ _ => by
  unfold Interleave
  infer_instance

/-- Interleaving is symmetric in its two arguments. -/
theorem Interleave.symm {p q : ℤ × ℤ} (h : Interleave p q) : Interleave q p :=
  Or.symm h

/-- The **sides** of `[a, b]`: the pairs `(i, i + 1)` with `a ≤ i < b`, and the pair `(a, b)`. -/
@[cluster_algebras "def_interval_triangulation"]
def intervalSides (a b : ℤ) : Finset (ℤ × ℤ) :=
  insert (a, b) ((Finset.Ico a b).image fun i => (i, i + 1))

/-- The set `D[a, b]` of **diagonals** of `[a, b]`: the increasing pairs `(i, j)` of elements of
`[a, b]` with `i + 2 ≤ j` and `(i, j) ≠ (a, b)`. -/
@[cluster_algebras "def_interval_triangulation"]
def intervalDiagonals (a b : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc a b ×ˢ Finset.Icc a b).filter fun p => p.1 + 2 ≤ p.2 ∧ p ≠ (a, b)

/-- A **triangulation of `[a, b]`**: a set `S ⊆ D[a, b]`, no two elements of which interleave,
such that every element of `D[a, b] \ S` interleaves some element of `S`. -/
@[cluster_algebras "def_interval_triangulation"]
def IsIntervalTriangulation (a b : ℤ) (S : Finset (ℤ × ℤ)) : Prop :=
  S ⊆ intervalDiagonals a b ∧ (∀ p ∈ S, ∀ q ∈ S, ¬Interleave p q) ∧
    ∀ p ∈ intervalDiagonals a b, p ∉ S → ∃ q ∈ S, Interleave p q

/-- Being a triangulation of `[a, b]` is decidable: every quantifier is bounded. -/
instance instDecidablePredIsIntervalTriangulation (a b : ℤ) :
    DecidablePred (IsIntervalTriangulation a b) := fun _ => by
  unfold IsIntervalTriangulation
  infer_instance

/-- The **segments** of a triangulation `S` of `[a, b]`: its elements and the sides of
`[a, b]`. -/
@[cluster_algebras "def_interval_triangulation"]
def intervalSegments (a b : ℤ) (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S ∪ intervalSides a b

/-- The finite set of **triangulations of `[a, b]`**, as subsets of `D[a, b]`. -/
@[cluster_algebras "def_interval_triangulation"]
def intervalTriangulations (a b : ℤ) : Finset (Finset (ℤ × ℤ)) :=
  (intervalDiagonals a b).powerset.filter (IsIntervalTriangulation a b)

/-- The **number `τ(a, b)` of triangulations of `[a, b]`**. -/
@[cluster_algebras "def_interval_triangulation"]
def intervalTriangulationCount (a b : ℤ) : ℕ :=
  (intervalTriangulations a b).card

/-- The finite set of triangulations consists of exactly the triangulations. -/
@[cluster_algebras "def_interval_triangulation"]
theorem mem_intervalTriangulations {a b : ℤ} {S : Finset (ℤ × ℤ)} :
    S ∈ intervalTriangulations a b ↔ IsIntervalTriangulation a b S := by
  rw [intervalTriangulations, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

variable {a b : ℤ} {S : Finset (ℤ × ℤ)}

/-! ### Membership in the sides and the diagonals -/

/-- An increasing pair `(i, j)` is a diagonal of `[a, b]` iff `a ≤ i`, `j ≤ b`, `i + 2 ≤ j` and
`(i, j) ≠ (a, b)`. -/
theorem mk_mem_intervalDiagonals_iff {i j : ℤ} :
    (i, j) ∈ intervalDiagonals a b ↔ a ≤ i ∧ j ≤ b ∧ i + 2 ≤ j ∧ ¬(i = a ∧ j = b) := by
  simp only [intervalDiagonals, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, ne_eq,
    Prod.mk.injEq]
  omega

/-- A pair `(i, j)` is a side of `[a, b]` iff it is `(a, b)` or `(i, i + 1)` with `a ≤ i < b`. -/
theorem mk_mem_intervalSides_iff {i j : ℤ} :
    (i, j) ∈ intervalSides a b ↔ (i = a ∧ j = b) ∨ (a ≤ i ∧ i < b ∧ j = i + 1) := by
  simp only [intervalSides, Finset.mem_insert, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro (h | ⟨x, hx, rfl, rfl⟩)
    exacts [.inl h, .inr ⟨hx.1, hx.2, rfl⟩]
  · rintro (h | ⟨h1, h2, rfl⟩)
    exacts [.inl h, .inr ⟨i, ⟨h1, h2⟩, rfl, rfl⟩]

/-- A side of `[a, b]` interleaves no pair whose entries lie in `[a, b]`. -/
theorem not_interleave_of_mem_intervalSides {i j k l : ℤ} (hp : (i, j) ∈ intervalSides a b)
    (hk : a ≤ k) (hl : l ≤ b) : ¬Interleave (i, j) (k, l) := by
  have := mk_mem_intervalSides_iff.1 hp
  simp only [Interleave]
  omega

/-- A segment `(i, j)` of a triangulation of `[a, b]` satisfies `a ≤ i < j ≤ b`. -/
theorem IsIntervalTriangulation.bounds_of_mem_intervalSegments (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {i j : ℤ} (h : (i, j) ∈ intervalSegments a b S) :
    a ≤ i ∧ i < j ∧ j ≤ b := by
  rcases Finset.mem_union.1 h with h | h
  · have := mk_mem_intervalDiagonals_iff.1 (hS.1 h)
    omega
  · have := mk_mem_intervalSides_iff.1 h
    omega

/-! ### Segments and apexes -/

/-- **No two segments of a triangulation of an interval interleave.** -/
@[cluster_algebras "lem_interval_segments"]
theorem IsIntervalTriangulation.not_interleave (hab : a < b) (hS : IsIntervalTriangulation a b S)
    {p q : ℤ × ℤ} (hp : p ∈ intervalSegments a b S) (hq : q ∈ intervalSegments a b S) :
    ¬Interleave p q := by
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  have hp' := hS.bounds_of_mem_intervalSegments hab hp
  have hq' := hS.bounds_of_mem_intervalSegments hab hq
  rcases Finset.mem_union.1 hp with hp | hp
  · rcases Finset.mem_union.1 hq with hq | hq
    · exact hS.2.1 _ hp _ hq
    · exact fun h => not_interleave_of_mem_intervalSides hq hp'.1 hp'.2.2 h.symm
  · exact not_interleave_of_mem_intervalSides hp hq'.1 hq'.2.2

/-- **A two-element subset of `[a, b]` that is not a segment of a triangulation `S` interleaves
some element of `S`.** -/
@[cluster_algebras "lem_interval_segments"]
theorem IsIntervalTriangulation.exists_interleave (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {i j : ℤ} (hai : a ≤ i) (hij : i < j) (hjb : j ≤ b)
    (h : (i, j) ∉ intervalSegments a b S) : ∃ q ∈ S, Interleave (i, j) q := by
  refine hS.2.2 _ ?_ fun h' => h (Finset.mem_union_left _ h')
  have hs : (i, j) ∉ intervalSides a b := fun h' => h (Finset.mem_union_right _ h')
  rw [mk_mem_intervalSides_iff] at hs
  rw [mk_mem_intervalDiagonals_iff]
  omega

/-- **The apex over a segment of an interval triangulation.** If `{i, k}` is a segment of a
triangulation `S` of `[a, b]` with `k ≥ i + 2`, there is exactly one `j` with `i < j < k` such
that `{i, j}` and `{j, k}` are both segments of `S`. -/
@[cluster_algebras "lem_interval_apex"]
theorem IsIntervalTriangulation.existsUnique_apex (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {i k : ℤ} (hik : i + 2 ≤ k)
    (h : (i, k) ∈ intervalSegments a b S) :
    ∃! j, i < j ∧ j < k ∧ (i, j) ∈ intervalSegments a b S ∧ (j, k) ∈ intervalSegments a b S := by
  have hb := hS.bounds_of_mem_intervalSegments hab h
  have seg_of_mem : ∀ {p}, p ∈ S → p ∈ intervalSegments a b S := fun hp =>
    Finset.mem_union_left _ hp
  have side_seg : ∀ {x : ℤ}, a ≤ x → x < b → (x, x + 1) ∈ intervalSegments a b S := fun h1 h2 =>
    Finset.mem_union_right _ (mk_mem_intervalSides_iff.2 (Or.inr ⟨h1, h2, rfl⟩))
  set J := (Finset.Ioo i k).filter (fun j => (i, j) ∈ intervalSegments a b S)
  have hJne : J.Nonempty :=
    ⟨i + 1, Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨by omega, by omega⟩, side_seg hb.1 (by omega)⟩⟩
  have hjJ := Finset.max'_mem J hJne
  set j := J.max' hJne
  obtain ⟨hjIoo, hij⟩ := Finset.mem_filter.1 hjJ
  rw [Finset.mem_Ioo] at hjIoo
  have hjk : (j, k) ∈ intervalSegments a b S := by
    by_contra hjk
    rcases eq_or_lt_of_le (show j + 1 ≤ k by omega) with he | hlt
    · exact hjk (he ▸ side_seg (by omega) (by omega))
    obtain ⟨⟨p, q⟩, hpq, hint⟩ := hS.exists_interleave hab (by omega) hjIoo.2 hb.2.2 hjk
    have hpq' := mk_mem_intervalDiagonals_iff.1 (hS.1 hpq)
    have nik := hS.not_interleave hab h (seg_of_mem hpq)
    have nij := hS.not_interleave hab hij (seg_of_mem hpq)
    simp only [Interleave] at hint nik nij
    by_cases hpi : p = i
    · have hiq : (i, q) ∈ S := hpi ▸ hpq
      have := J.le_max' q (Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 (by omega), seg_of_mem hiq⟩)
      omega
    · omega
  refine ⟨j, ⟨hjIoo.1, hjIoo.2, hij, hjk⟩, ?_⟩
  rintro j' ⟨h1, h2, h3, h4⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hS.not_interleave hab hij h4 (by simp only [Interleave]; omega)
  · exact hS.not_interleave hab h3 hjk (by simp only [Interleave]; omega)

/-! ### Cutting at the apex of the base -/

/-- Every diagonal of a triangulation of `[a, b]` lies in `[a, k]` or in `[k, b]`, where `k` is an
apex over the side `{a, b}`. -/
theorem IsIntervalTriangulation.le_or_le_of_apex (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {k : ℤ} (h1 : (a, k) ∈ intervalSegments a b S)
    (h2 : (k, b) ∈ intervalSegments a b S) {i j : ℤ} (h : (i, j) ∈ S) : j ≤ k ∨ k ≤ i := by
  have hd := mk_mem_intervalDiagonals_iff.1 (hS.1 h)
  have n1 := hS.not_interleave hab h1 (Finset.mem_union_left _ h)
  have n2 := hS.not_interleave hab h2 (Finset.mem_union_left _ h)
  simp only [Interleave] at n1 n2
  omega

/-- A triangulation `S` of `[a, b]` with apex `k` over `{a, b}` is the union of `S ∩ D[a, k]`,
`S ∩ D[k, b]` and those of `{a, k}`, `{k, b}` that are diagonals of `[a, b]`. -/
theorem IsIntervalTriangulation.eq_union_of_apex (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {k : ℤ} (hak : a < k) (hkb : k < b)
    (h1 : (a, k) ∈ intervalSegments a b S) (h2 : (k, b) ∈ intervalSegments a b S) :
    S = S ∩ intervalDiagonals a k ∪ S ∩ intervalDiagonals k b ∪
      ({(a, k), (k, b)} ∩ intervalDiagonals a b) := by
  ext ⟨i, j⟩
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, mk_mem_intervalDiagonals_iff]
  constructor
  · intro h
    have hd := mk_mem_intervalDiagonals_iff.1 (hS.1 h)
    have hc := hS.le_or_le_of_apex hab h1 h2 h
    by_cases hE : (i = a ∧ j = k) ∨ (i = k ∧ j = b)
    · exact Or.inr ⟨hE, hd⟩
    · rcases hc with hc | hc
      · exact Or.inl (Or.inl ⟨h, by omega⟩)
      · exact Or.inl (Or.inr ⟨h, by omega⟩)
  · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hd⟩)
    · exact h
    · exact h
    · exact (Finset.mem_union.1 h1).resolve_right fun h => by
        rw [mk_mem_intervalSides_iff] at h
        omega
    · exact (Finset.mem_union.1 h2).resolve_right fun h => by
        rw [mk_mem_intervalSides_iff] at h
        omega

/-- Cutting at an apex `k` over `{a, b}`: `S ∩ D[a, k]` is a triangulation of `[a, k]`. -/
theorem IsIntervalTriangulation.inter_left_of_apex (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {k : ℤ} (hkb : k < b)
    (h1 : (a, k) ∈ intervalSegments a b S) (h2 : (k, b) ∈ intervalSegments a b S) :
    IsIntervalTriangulation a k (S ∩ intervalDiagonals a k) := by
  refine ⟨Finset.inter_subset_right, fun p hp q hq =>
    hS.2.1 p (Finset.mem_inter.1 hp).1 q (Finset.mem_inter.1 hq).1, ?_⟩
  rintro ⟨i, j⟩ he hnot
  have he' := mk_mem_intervalDiagonals_iff.1 he
  have hnS : (i, j) ∉ S := fun h => hnot (Finset.mem_inter.2 ⟨h, he⟩)
  obtain ⟨⟨p, q⟩, hpq, hint⟩ := hS.2.2 _ (mk_mem_intervalDiagonals_iff.2 (by omega)) hnS
  have hd := mk_mem_intervalDiagonals_iff.1 (hS.1 hpq)
  have hc := hS.le_or_le_of_apex hab h1 h2 hpq
  simp only [Interleave] at hint
  refine ⟨(p, q), Finset.mem_inter.2 ⟨hpq, mk_mem_intervalDiagonals_iff.2 (by omega)⟩, ?_⟩
  simp only [Interleave]
  omega

/-- Cutting at an apex `k` over `{a, b}`: `S ∩ D[k, b]` is a triangulation of `[k, b]`. -/
theorem IsIntervalTriangulation.inter_right_of_apex (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {k : ℤ} (hak : a < k)
    (h1 : (a, k) ∈ intervalSegments a b S) (h2 : (k, b) ∈ intervalSegments a b S) :
    IsIntervalTriangulation k b (S ∩ intervalDiagonals k b) := by
  refine ⟨Finset.inter_subset_right, fun p hp q hq =>
    hS.2.1 p (Finset.mem_inter.1 hp).1 q (Finset.mem_inter.1 hq).1, ?_⟩
  rintro ⟨i, j⟩ he hnot
  have he' := mk_mem_intervalDiagonals_iff.1 he
  have hnS : (i, j) ∉ S := fun h => hnot (Finset.mem_inter.2 ⟨h, he⟩)
  obtain ⟨⟨p, q⟩, hpq, hint⟩ := hS.2.2 _ (mk_mem_intervalDiagonals_iff.2 (by omega)) hnS
  have hd := mk_mem_intervalDiagonals_iff.1 (hS.1 hpq)
  have hc := hS.le_or_le_of_apex hab h1 h2 hpq
  simp only [Interleave] at hint
  refine ⟨(p, q), Finset.mem_inter.2 ⟨hpq, mk_mem_intervalDiagonals_iff.2 (by omega)⟩, ?_⟩
  simp only [Interleave]
  omega

/-- Membership in the glued set `S₁ ∪ S₂ ∪ E_k` of triangulations of `[a, k]` and `[k, b]`. -/
theorem mk_mem_union_intervalDiagonals_iff {k : ℤ} {S₁ S₂ : Finset (ℤ × ℤ)} {i j : ℤ} :
    (i, j) ∈ S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b) ↔
      (i, j) ∈ S₁ ∨ (i, j) ∈ S₂ ∨
        (((i = a ∧ j = k) ∨ (i = k ∧ j = b)) ∧ (i, j) ∈ intervalDiagonals a b) := by
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, or_assoc]

/-- In the glued set `S₁ ∪ S₂ ∪ E_k`, every diagonal of `[a, b]` outside it interleaves one of
its elements. -/
private theorem IsIntervalTriangulation.exists_interleave_union {k : ℤ} (hak : a < k)
    (hkb : k < b) {S₁ S₂ : Finset (ℤ × ℤ)} (h1 : IsIntervalTriangulation a k S₁)
    (h2 : IsIntervalTriangulation k b S₂) :
    ∀ p ∈ intervalDiagonals a b, p ∉ S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b) →
      ∃ q ∈ S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b), Interleave p q := by
  rintro ⟨p, q⟩ he hnot
  have he' := mk_mem_intervalDiagonals_iff.1 he
  have memL : ∀ {x}, x ∈ S₁ → x ∈ S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b) :=
    fun hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have memR : ∀ {x}, x ∈ S₂ → x ∈ S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b) :=
    fun hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  by_cases hqk : q ≤ k
  · by_cases hE : p = a ∧ q = k
    · exact absurd (mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr ⟨Or.inl hE, he⟩))) hnot
    · obtain ⟨f, hf, hint⟩ := h1.2.2 _ (mk_mem_intervalDiagonals_iff.2 (by omega))
        fun h => hnot (memL h)
      exact ⟨f, memL hf, hint⟩
  by_cases hkp : k ≤ p
  · by_cases hE : p = k ∧ q = b
    · exact absurd (mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr ⟨Or.inr hE, he⟩))) hnot
    · obtain ⟨f, hf, hint⟩ := h2.2.2 _ (mk_mem_intervalDiagonals_iff.2 (by omega))
        fun h => hnot (memR h)
      exact ⟨f, memR hf, hint⟩
  by_cases hpa : a < p
  · refine ⟨(a, k), mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr
      ⟨Or.inl ⟨rfl, rfl⟩, mk_mem_intervalDiagonals_iff.2 (by omega)⟩)), ?_⟩
    simp only [Interleave]
    omega
  · refine ⟨(k, b), mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr
      ⟨Or.inr ⟨rfl, rfl⟩, mk_mem_intervalDiagonals_iff.2 (by omega)⟩)), ?_⟩
    simp only [Interleave]
    omega

/-- Gluing triangulations of `[a, k]` and `[k, b]`, together with those of `{a, k}`, `{k, b}`
that are diagonals of `[a, b]`, gives a triangulation of `[a, b]`. -/
theorem IsIntervalTriangulation.union {k : ℤ} (hak : a < k) (hkb : k < b)
    {S₁ S₂ : Finset (ℤ × ℤ)} (h1 : IsIntervalTriangulation a k S₁)
    (h2 : IsIntervalTriangulation k b S₂) :
    IsIntervalTriangulation a b (S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b)) := by
  have c1 : ∀ {i j}, (i, j) ∈ S₁ → a ≤ i ∧ j ≤ k ∧ i + 2 ≤ j ∧ ¬(i = a ∧ j = k) := fun h =>
    mk_mem_intervalDiagonals_iff.1 (h1.1 h)
  have c2 : ∀ {i j}, (i, j) ∈ S₂ → k ≤ i ∧ j ≤ b ∧ i + 2 ≤ j ∧ ¬(i = k ∧ j = b) := fun h =>
    mk_mem_intervalDiagonals_iff.1 (h2.1 h)
  refine ⟨?_, ?_, exists_interleave_union hak hkb h1 h2⟩
  · rintro ⟨i, j⟩ h
    rcases mk_mem_union_intervalDiagonals_iff.1 h with h | h | ⟨-, h⟩
    · have := c1 h
      exact mk_mem_intervalDiagonals_iff.2 (by omega)
    · have := c2 h
      exact mk_mem_intervalDiagonals_iff.2 (by omega)
    · exact h
  · rintro ⟨i, j⟩ hp ⟨l, m⟩ hq hint
    rcases mk_mem_union_intervalDiagonals_iff.1 hp with hp | hp | ⟨hp, -⟩ <;>
      rcases mk_mem_union_intervalDiagonals_iff.1 hq with hq | hq | ⟨hq, -⟩
    all_goals first
      | exact h1.2.1 _ hp _ hq hint
      | exact h2.2.1 _ hp _ hq hint
      | try have := c1 hp
        try have := c2 hp
        try have := c1 hq
        try have := c2 hq
        simp only [Interleave] at hint
        omega

/-- The glued triangulation meets `D[a, k]` in `S₁`. -/
theorem union_inter_intervalDiagonals_left {k : ℤ} {S₁ S₂ : Finset (ℤ × ℤ)}
    (h1 : IsIntervalTriangulation a k S₁) (h2 : IsIntervalTriangulation k b S₂) :
    (S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b)) ∩ intervalDiagonals a k = S₁ := by
  ext ⟨i, j⟩
  rw [Finset.mem_inter, mk_mem_union_intervalDiagonals_iff]
  constructor
  · rintro ⟨h | h | ⟨hE, -⟩, hd⟩
    · exact h
    · have := mk_mem_intervalDiagonals_iff.1 (h2.1 h)
      have := mk_mem_intervalDiagonals_iff.1 hd
      omega
    · have := mk_mem_intervalDiagonals_iff.1 hd
      omega
  · exact fun h => ⟨Or.inl h, h1.1 h⟩

/-- The glued triangulation meets `D[k, b]` in `S₂`. -/
theorem union_inter_intervalDiagonals_right {k : ℤ} (hak : a < k) {S₁ S₂ : Finset (ℤ × ℤ)}
    (h1 : IsIntervalTriangulation a k S₁) (h2 : IsIntervalTriangulation k b S₂) :
    (S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b)) ∩ intervalDiagonals k b = S₂ := by
  ext ⟨i, j⟩
  rw [Finset.mem_inter, mk_mem_union_intervalDiagonals_iff]
  constructor
  · rintro ⟨h | h | ⟨hE, -⟩, hd⟩
    · have := mk_mem_intervalDiagonals_iff.1 (h1.1 h)
      have := mk_mem_intervalDiagonals_iff.1 hd
      omega
    · exact h
    · have := mk_mem_intervalDiagonals_iff.1 hd
      omega
  · exact fun h => ⟨Or.inr (Or.inl h), h2.1 h⟩

/-- In the glued triangulation, `{a, k}` and `{k, b}` are segments. -/
theorem union_apex_mem_intervalSegments {k : ℤ} (hak : a < k) (hkb : k < b)
    {S₁ S₂ : Finset (ℤ × ℤ)} :
    (a, k) ∈ intervalSegments a b (S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b)) ∧
      (k, b) ∈ intervalSegments a b (S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b)) := by
  constructor
  · by_cases hk : k = a + 1
    · exact Finset.mem_union_right _ (mk_mem_intervalSides_iff.2 (Or.inr ⟨le_rfl, by omega, hk⟩))
    · exact Finset.mem_union_left _ (mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr
        ⟨Or.inl ⟨rfl, rfl⟩, mk_mem_intervalDiagonals_iff.2 (by omega)⟩)))
  · by_cases hk : b = k + 1
    · exact Finset.mem_union_right _ (mk_mem_intervalSides_iff.2 (Or.inr ⟨by omega, hkb, hk⟩))
    · exact Finset.mem_union_left _ (mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr
        ⟨Or.inr ⟨rfl, rfl⟩, mk_mem_intervalDiagonals_iff.2 (by omega)⟩)))

/-- Two triples `(k, S₁, S₂)` are equal when their apexes and their underlying sets are. -/
private theorem sigma_mk_eq_of_val_eq {k k' : Set.Ioo a b} (hk : k' = k) {U : Finset (ℤ × ℤ)}
    {t₁ : {S // IsIntervalTriangulation a k' S}} {t₂ : {S // IsIntervalTriangulation k' b S}}
    {S₁ : {S // IsIntervalTriangulation a k S}} {S₂ : {S // IsIntervalTriangulation k b S}}
    (ht₁ : t₁.1 = U ∩ intervalDiagonals a k') (ht₂ : t₂.1 = U ∩ intervalDiagonals k' b)
    (h₁ : U ∩ intervalDiagonals a k = S₁.1) (h₂ : U ∩ intervalDiagonals k b = S₂.1) :
    (⟨k', t₁, t₂⟩ : Σ k : Set.Ioo a b, {S₁ // IsIntervalTriangulation a k S₁} ×
      {S₂ // IsIntervalTriangulation k b S₂}) = ⟨k, S₁, S₂⟩ := by
  subst hk
  rw [Subtype.ext (ht₁.trans h₁), Subtype.ext (ht₂.trans h₂)]

/-- **Cutting an interval triangulation at the apex of the base.** For `b ≥ a + 2`, the map
`S ↦ (k(S), S ∩ D[a, k(S)], S ∩ D[k(S), b])`, where `k(S)` is the apex over the side `{a, b}`,
is a bijection from the triangulations of `[a, b]` onto the triples `(k, S₁, S₂)` with
`a < k < b`, `S₁` a triangulation of `[a, k]` and `S₂` one of `[k, b]`.

Stated as the existence of a bijection `e` whose first component is an apex over `{a, b}` (so
it is `k(S)`, by `IsIntervalTriangulation.existsUnique_apex`) and whose other two components
are the two intersections. -/
@[cluster_algebras "lem_interval_decomposition"]
theorem exists_equiv_intervalTriangulation (hab : a + 2 ≤ b) :
    ∃ e : {S // IsIntervalTriangulation a b S} ≃
        Σ k : Set.Ioo a b, {S₁ // IsIntervalTriangulation a k S₁} ×
          {S₂ // IsIntervalTriangulation k b S₂},
      ∀ S, (a, ((e S).1 : ℤ)) ∈ intervalSegments a b S.1 ∧
        (((e S).1 : ℤ), b) ∈ intervalSegments a b S.1 ∧
        ((e S).2.1 : Finset (ℤ × ℤ)) = S.1 ∩ intervalDiagonals a (e S).1 ∧
        ((e S).2.2 : Finset (ℤ × ℤ)) = S.1 ∩ intervalDiagonals (e S).1 b := by
  have hab' : a < b := by omega
  have hbase : ∀ S, (a, b) ∈ intervalSegments a b S := fun S =>
    Finset.mem_union_right _ (mk_mem_intervalSides_iff.2 (Or.inl ⟨rfl, rfl⟩))
  have hex : ∀ S : {S // IsIntervalTriangulation a b S}, ∃ k : Set.Ioo a b,
      (a, (k : ℤ)) ∈ intervalSegments a b S.1 ∧ ((k : ℤ), b) ∈ intervalSegments a b S.1 := by
    intro S
    obtain ⟨k, ⟨h1, h2, h3, h4⟩, -⟩ := S.2.existsUnique_apex hab' hab (hbase S.1)
    exact ⟨⟨k, h1, h2⟩, h3, h4⟩
  choose kf hkf using hex
  let F : {S // IsIntervalTriangulation a b S} →
      Σ k : Set.Ioo a b, {S₁ // IsIntervalTriangulation a k S₁} ×
        {S₂ // IsIntervalTriangulation k b S₂} := fun S =>
    ⟨kf S, ⟨S.1 ∩ intervalDiagonals a (kf S),
        S.2.inter_left_of_apex hab' (kf S).2.2 (hkf S).1 (hkf S).2⟩,
      ⟨S.1 ∩ intervalDiagonals (kf S) b,
        S.2.inter_right_of_apex hab' (kf S).2.1 (hkf S).1 (hkf S).2⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro S S' h
      have hk : kf S = kf S' := congrArg Sigma.fst h
      have h1 : S.1 ∩ intervalDiagonals a (kf S) = S'.1 ∩ intervalDiagonals a (kf S') :=
        congrArg (fun x => (x.2.1 : Finset (ℤ × ℤ))) h
      have h2 : S.1 ∩ intervalDiagonals (kf S) b = S'.1 ∩ intervalDiagonals (kf S') b :=
        congrArg (fun x => (x.2.2 : Finset (ℤ × ℤ))) h
      have e1 := S.2.eq_union_of_apex hab' (kf S).2.1 (kf S).2.2 (hkf S).1 (hkf S).2
      have e2 := S'.2.eq_union_of_apex hab' (kf S').2.1 (kf S').2.2 (hkf S').1 (hkf S').2
      apply Subtype.ext
      rw [e1, e2, h1, h2, hk]
    · rintro ⟨k, S₁, S₂⟩
      have hT := IsIntervalTriangulation.union k.2.1 k.2.2 S₁.2 S₂.2
      refine ⟨⟨_, hT⟩, ?_⟩
      have hk : kf ⟨_, hT⟩ = k := by
        obtain ⟨j, -, huniq⟩ := hT.existsUnique_apex hab' hab (hbase _)
        have h0 := hkf ⟨_, hT⟩
        have hu := union_apex_mem_intervalSegments (S₁ := S₁.1) (S₂ := S₂.1) k.2.1 k.2.2
        apply Subtype.ext
        rw [huniq _ ⟨(kf _).2.1, (kf _).2.2, h0.1, h0.2⟩, huniq _ ⟨k.2.1, k.2.2, hu.1, hu.2⟩]
      exact sigma_mk_eq_of_val_eq hk rfl rfl (union_inter_intervalDiagonals_left S₁.2 S₂.2)
        (union_inter_intervalDiagonals_right k.2.1 S₁.2 S₂.2)
  exact ⟨Equiv.ofBijective F hF, fun S => ⟨(hkf S).1, (hkf S).2, rfl, rfl⟩⟩

/-- The triangulations of `[a, b]` form a finite type, enumerated by
`intervalTriangulations a b`. -/
instance instFintypeSubtypeIsIntervalTriangulation (a b : ℤ) :
    Fintype {S // IsIntervalTriangulation a b S} :=
  Fintype.ofFinset (intervalTriangulations a b) fun _ => mem_intervalTriangulations

/-- `τ(a, b)` is the cardinality of the type of triangulations of `[a, b]`. -/
theorem card_subtype_isIntervalTriangulation (a b : ℤ) :
    Fintype.card {S // IsIntervalTriangulation a b S} = intervalTriangulationCount a b :=
  Fintype.card_ofFinset _ _

/-- **The recursion for `τ`**: for `b ≥ a + 2`,
`τ(a, b) = ∑_{k = a+1}^{b-1} τ(a, k) τ(k, b)`. -/
@[cluster_algebras "lem_interval_decomposition"]
theorem intervalTriangulationCount_eq_sum (hab : a + 2 ≤ b) :
    intervalTriangulationCount a b =
      ∑ k ∈ Finset.Ioo a b, intervalTriangulationCount a k * intervalTriangulationCount k b := by
  obtain ⟨e, -⟩ := exists_equiv_intervalTriangulation hab
  rw [← card_subtype_isIntervalTriangulation, Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [Fintype.card_prod, card_subtype_isIntervalTriangulation]
  exact (Finset.sum_subtype (p := fun x => x ∈ Set.Ioo a b) (Finset.Ioo a b)
    (fun _ => by rw [Finset.mem_Ioo, Set.mem_Ioo])
    fun k => intervalTriangulationCount a k * intervalTriangulationCount k b).symm

/-- `[a, a + 1]` has exactly one triangulation, the empty one. -/
theorem intervalTriangulationCount_self_add_one (a : ℤ) :
    intervalTriangulationCount a (a + 1) = 1 := by
  have hD : intervalDiagonals a (a + 1) = ∅ := by
    ext ⟨i, j⟩
    simp only [mk_mem_intervalDiagonals_iff, Finset.notMem_empty, iff_false]
    omega
  have h0 : IsIntervalTriangulation a (a + 1) ∅ :=
    ⟨Finset.empty_subset _, by simp, by simp [hD]⟩
  rw [intervalTriangulationCount, intervalTriangulations, hD, Finset.powerset_empty,
    Finset.filter_singleton, if_pos h0, Finset.card_singleton]

/-- **Triangulations of an interval are counted by the Catalan numbers**: for `a < b`,
`τ(a, b) = c_{b-a-1}`. -/
@[cluster_algebras "lem_interval_count"]
theorem intervalTriangulationCount_eq_catalanNumber (hab : a < b) :
    intervalTriangulationCount a b = catalanNumber (b - a - 1).toNat := by
  suffices H : ∀ n : ℕ, ∀ a b : ℤ, b - a - 1 = n →
      intervalTriangulationCount a b = catalanNumber n from H _ a b (by omega)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn
  rcases n with _ | n
  · obtain rfl : b = a + 1 := by omega
    rw [intervalTriangulationCount_self_add_one, catalanNumber_zero]
  · rw [intervalTriangulationCount_eq_sum (by omega), catalanNumber_succ]
    refine Finset.sum_nbij' (fun k => (k - a - 1).toNat) (fun i => a + 1 + i) ?_ ?_ ?_ ?_ ?_ <;>
      intro k hk <;> simp only [Finset.mem_Ioo, Finset.mem_range] at hk ⊢
    any_goals omega
    rw [ih (k - a - 1).toNat (by omega) a k (by omega),
      ih (n - (k - a - 1).toNat) (by omega) k b (by omega)]

end TypeA

end ClusterAlgebras

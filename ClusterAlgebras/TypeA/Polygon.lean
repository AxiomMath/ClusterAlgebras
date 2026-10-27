/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeA.Interval
public import ClusterAlgebras.FiniteType.External

/-!
# Reading a polygon from a base point, apexes, and flips

The vertices of the convex `m`-gon are `ZMod m`, and segments, sides, diagonals, crossing,
triangulations, triangles, clockwise listings and flips are those of
`ClusterAlgebras.PolygonTriangulation` and `ClusterAlgebras.FiniteType.External`. Reading
`ZMod m` linearly from a base point `c` turns segments into increasing pairs of `[0, m-1]`,
crossing into interleaving, and triangulations of the polygon into triangulations of
`[0, m-1]`. From this come the apex over a segment of a triangulation, the six segments of a
quadrilateral, and the existence and uniqueness of the flip at every diagonal.

## Main definitions

* `ClusterAlgebras.TypeA.basePos c v`: the position `d_c(v) ∈ [0, m-1]` of `v` read from `c`.
* `ClusterAlgebras.TypeA.basePosSeg`, `ClusterAlgebras.TypeA.basePosTri`: its action on
  segments and on sets of segments.
* `ClusterAlgebras.TypeA.IsFlipQuadrilateral T a b c d`: `b` is an apex over `{a, c}` and `d`
  one over `{c, a}`, the four rim segments being segments of `T`.

## Main statements

* `ClusterAlgebras.TypeA.cross_iff_interleave`: two segments cross exactly when their images
  interleave.
* `ClusterAlgebras.TypeA.bijOn_basePosTri`: `T ↦ d_c(T)` is a bijection from the
  triangulations of the `m`-gon onto those of `[0, m-1]`.
* `ClusterAlgebras.TypeA.IsTriangulation.existsUnique_apex`: the apex over a segment.
* `ClusterAlgebras.TypeA.IsFlipQuadrilateral.isFlipReplacement`,
  `ClusterAlgebras.TypeA.IsTriangulation.existsUnique_isFlipReplacement`: every diagonal of a
  triangulation has exactly one flip.

## Implementation notes

* **Vertex convention.** `ClusterAlgebras.vertexRep` and `ClusterAlgebras.segmentPlucker` read
  a vertex `v : ZMod m` as the column `v.val`, the representative in `[1, m]` of the
  `1`-indexed labelling shifted down by one. So the vertex `v` here is the vertex `v + 1` of
  that labelling. Every notion of this file is invariant under rotation, so no statement here
  sees the shift.
* `basePos c v` is the integer `(v - c).val`, and `basePosSeg c s(u, v)` is the increasing pair
  `(min, max)` of the two positions, the image `d_c(σ)` in the pair encoding of
  `ClusterAlgebras.TypeA.Interleave`.
* "`γ'` is the replacement of `γ` in `T`" is `IsFlipReplacement T γ γ'`: by
  `IsFlipQuadrilateral.eq_of_isFlipReplacement` the replacement is the only `γ'` with this
  property, so no separate function is defined.
* The segments of a quadrilateral are described without a hypothesis `m ≥ 4`: the two
  betweenness hypotheses already force four distinct vertices.
* `IsTriangulation` gets a `DecidablePred` instance here, so that small cases can be checked
  by `decide` and `#eval`.
-/

@[expose] public section

namespace ClusterAlgebras

namespace TypeA

variable {m : ℕ} [NeZero m]

/-- Being a triangulation is decidable: every quantifier ranges over a finite type. -/
instance instDecidablePredIsTriangulation : DecidablePred (IsTriangulation (m := m)) := fun T =>
  decidable_of_iff ((∀ e ∈ T, IsDiagonal e) ∧ (∀ e ∈ T, ∀ f ∈ T, ¬Cross e f) ∧
      ∀ e, IsDiagonal e → e ∉ T → ∃ f ∈ T, Cross e f)
    ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

/-! ### Reading the polygon from a base point -/

/-- The **position** `d_c(v) ∈ [0, m-1]` of the vertex `v` read from the base point `c`: the
representative of `v - c`. -/
@[cluster_algebras "lem_polygon_base_point"]
def basePos (c v : ZMod m) : ℤ :=
  ((v - c).val : ℤ)

/-- The image `d_c(σ)` of a segment `σ = {u, v}`: the pair of positions of its endpoints,
listed increasingly. -/
@[cluster_algebras "lem_polygon_base_point"]
def basePosSeg (c : ZMod m) (σ : Sym2 (ZMod m)) : ℤ × ℤ :=
  Sym2.lift ⟨fun u v => (min (basePos c u) (basePos c v), max (basePos c u) (basePos c v)),
    fun _ _ => Prod.ext (min_comm _ _) (max_comm _ _)⟩ σ

/-- The image `d_c(T) = {d_c(σ) : σ ∈ T}` of a set of segments. -/
@[cluster_algebras "lem_polygon_base_point"]
def basePosTri (c : ZMod m) (T : Finset (Sym2 (ZMod m))) : Finset (ℤ × ℤ) :=
  T.image (basePosSeg c)

omit [NeZero m] in
/-- The image of a segment, unfolded. -/
@[simp]
theorem basePosSeg_mk (c u v : ZMod m) :
    basePosSeg c s(u, v) = (min (basePos c u) (basePos c v), max (basePos c u) (basePos c v)) :=
  rfl

omit [NeZero m] in
/-- The position of a vertex is nonnegative. -/
theorem basePos_nonneg (c v : ZMod m) : 0 ≤ basePos c v := by
  unfold basePos; positivity

/-- The position of a vertex is less than `m`. -/
theorem basePos_lt (c v : ZMod m) : basePos c v < m := by
  unfold basePos; exact_mod_cast ZMod.val_lt _

/-- The position of `v` read from `c`, in terms of the representatives of `v` and `c`. -/
theorem basePos_eq_ite (c v : ZMod m) :
    basePos c v = if c.val ≤ v.val then (v.val : ℤ) - c.val else (v.val : ℤ) - c.val + m := by
  unfold basePos
  split_ifs with h
  · rw [ZMod.val_sub h]; push_cast [h]; ring
  · have hv : v - c + c = v := by ring
    have h1 : m ≤ (v - c).val + c.val := by
      by_contra h2
      have := ZMod.val_add_of_lt (not_le.mp h2)
      rw [hv] at this
      omega
    have := ZMod.val_add_of_le h1
    rw [hv] at this
    have := ZMod.val_lt (v - c)
    omega

/-- Reading from a base point is injective. -/
theorem basePos_injective (c : ZMod m) : Function.Injective (basePos c) := by
  intro u v h
  rw [basePos_eq_ite, basePos_eq_ite] at h
  have hu := ZMod.val_lt u
  have hv := ZMod.val_lt v
  apply ZMod.val_injective
  split_ifs at h <;> omega

omit [NeZero m] in
/-- Every integer of `[0, m-1]` is the position of some vertex. -/
theorem exists_basePos_eq (c : ZMod m) {k : ℤ} (h0 : 0 ≤ k) (hk : k < m) :
    ∃ v, basePos c v = k := by
  refine ⟨c + ((k.toNat : ℕ) : ZMod m), ?_⟩
  unfold basePos
  rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Circular betweenness in `ZMod m`, read on representatives. -/
theorem sbtw_iff_val : ∀ x y z : ZMod m, sbtw x y z ↔ (x.val < y.val ∧ y.val < z.val) ∨
    (y.val < z.val ∧ z.val < x.val) ∨ (z.val < x.val ∧ x.val < y.val) := by
  match m, ‹NeZero m› with
  | (k + 1), _ => exact fun _ _ _ => Fin.sbtw_iff

/-- Circular betweenness of vertices is circular betweenness of their positions, read from any
base point. -/
theorem sbtw_iff_sbtw_basePos (c u x v : ZMod m) :
    sbtw u x v ↔ sbtw (basePos c u) (basePos c x) (basePos c v) := by
  rw [sbtw_iff_val, Int.sbtw_iff, basePos_eq_ite, basePos_eq_ite, basePos_eq_ite]
  have hu := ZMod.val_lt u
  have hx := ZMod.val_lt x
  have hv := ZMod.val_lt v
  split_ifs <;> omega

/-- The position of the successor `u + 1` of `u`. -/
theorem basePos_add_one (c u : ZMod m) :
    basePos c (u + 1) = if basePos c u + 1 = m then 0 else basePos c u + 1 := by
  unfold basePos
  rw [show u + 1 - c = (u - c) + 1 by ring]
  have hl := ZMod.val_lt (u - c)
  rcases Nat.lt_or_ge m 2 with hm | hm
  · obtain rfl : m = 1 := by have := NeZero.ne m; omega
    have h0 : ∀ w : ZMod 1, w.val = 0 := fun w => by have := ZMod.val_lt w; omega
    simp [h0]
  · haveI : Fact (1 < m) := ⟨hm⟩
    rcases Nat.lt_or_ge ((u - c).val + 1) m with h | h
    · rw [ZMod.val_add_of_lt (by rwa [ZMod.val_one]), ZMod.val_one, if_neg (by omega)]
      push_cast; rfl
    · rw [ZMod.val_add_of_le (by rwa [ZMod.val_one]), ZMod.val_one, if_pos (by omega)]
      omega

/-- The image of a segment determines the segment. -/
theorem basePosSeg_injective (c : ZMod m) : Function.Injective (basePosSeg c) := by
  intro σ τ h
  induction σ using Sym2.ind with | _ u v => ?_
  induction τ using Sym2.ind with | _ x y => ?_
  rw [basePosSeg_mk, basePosSeg_mk, Prod.mk.injEq] at h
  have hi := basePos_injective c
  rcases le_total (basePos c u) (basePos c v) with h1 | h1 <;>
    rcases le_total (basePos c x) (basePos c y) with h2 | h2
  · rw [min_eq_left h1, max_eq_right h1, min_eq_left h2, max_eq_right h2] at h
    rw [hi h.1, hi h.2]
  · rw [min_eq_left h1, max_eq_right h1, min_eq_right h2, max_eq_left h2] at h
    rw [hi h.1, hi h.2, Sym2.eq_swap]
  · rw [min_eq_right h1, max_eq_left h1, min_eq_left h2, max_eq_right h2] at h
    rw [hi h.1, hi h.2, Sym2.eq_swap]
  · rw [min_eq_right h1, max_eq_left h1, min_eq_right h2, max_eq_left h2] at h
    rw [hi h.1, hi h.2]

/-- A segment can be named `s(u, v)` with `d_c(u) < d_c(v)`. -/
theorem IsSegment.exists_basePos_lt (c : ZMod m) {σ : Sym2 (ZMod m)} (hσ : IsSegment σ) :
    ∃ u v, σ = s(u, v) ∧ basePos c u < basePos c v := by
  induction σ using Sym2.ind with | _ u v => ?_
  have huv : u ≠ v := by simpa [IsSegment, Sym2.mk_isDiag_iff] using hσ
  rcases lt_or_gt_of_ne ((basePos_injective c).ne huv) with h | h
  exacts [⟨u, v, rfl, h⟩, ⟨v, u, Sym2.eq_swap, h⟩]

omit [NeZero m] in
/-- For `d_c(u) < d_c(v)`, the image of `s(u, v)` is `(d_c(u), d_c(v))`. -/
theorem basePosSeg_mk_of_lt {c u v : ZMod m} (h : basePos c u < basePos c v) :
    basePosSeg c s(u, v) = (basePos c u, basePos c v) := by
  rw [basePosSeg_mk, min_eq_left h.le, max_eq_right h.le]

omit [NeZero m] in
/-- `s(u, v)` is a side exactly when `v = u + 1` or `u = v + 1`. -/
theorem isSide_mk_iff {u v : ZMod m} : IsSide s(u, v) ↔ v = u + 1 ∨ u = v + 1 := by
  constructor
  · rintro ⟨i, hi⟩
    rcases Sym2.eq_iff.1 hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [Or.inl rfl, Or.inr rfl]
  · rintro (rfl | rfl)
    exacts [⟨u, rfl⟩, ⟨v, Sym2.eq_swap⟩]

omit [NeZero m] in
/-- `s(u, v)` and `s(x, y)` cross exactly when one of `x`, `y` lies strictly between `u` and
`v` and the other strictly between `v` and `u`. -/
theorem cross_mk_iff {u v x y : ZMod m} :
    Cross s(u, v) s(x, y) ↔ (sbtw u x v ∧ sbtw v y u) ∨ (sbtw u y v ∧ sbtw v x u) := by
  constructor
  · rintro ⟨a, b, c, d, h1, h2, h3, h4⟩
    rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases Sym2.eq_iff.1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    exacts [⟨u, v, x, y, rfl, rfl, h1, h2⟩, ⟨u, v, y, x, rfl, Sym2.eq_swap, h1, h2⟩]

/-- Crossing of `s(u, v)` and `s(x, y)`, read on the positions from a base point. -/
theorem cross_mk_iff_basePos (c : ZMod m) {u v x y : ZMod m} :
    Cross s(u, v) s(x, y) ↔
      (sbtw (basePos c u) (basePos c x) (basePos c v) ∧
          sbtw (basePos c v) (basePos c y) (basePos c u)) ∨
        (sbtw (basePos c u) (basePos c y) (basePos c v) ∧
          sbtw (basePos c v) (basePos c x) (basePos c u)) := by
  simp only [cross_mk_iff, ← sbtw_iff_sbtw_basePos]

omit [NeZero m] in
/-- No segment crosses itself. -/
theorem not_cross_self (σ : Sym2 (ZMod m)) : ¬Cross σ σ := by
  rintro ⟨a, b, c, d, rfl, h, h1, h2⟩
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [sbtw_irrefl_left h1, sbtw_irrefl_right h1]

/-- `d_c` is a bijection from `ZMod m` onto `[0, m-1]`. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem bijOn_basePos (c : ZMod m) :
    Set.BijOn (basePos c) Set.univ (Set.Icc 0 ((m : ℤ) - 1)) := by
  refine ⟨fun v _ => ⟨basePos_nonneg c v, by have := basePos_lt c v; omega⟩,
    (basePos_injective c).injOn, fun k hk => ?_⟩
  obtain ⟨v, hv⟩ := exists_basePos_eq c hk.1 (by have := hk.2; omega)
  exact ⟨v, trivial, hv⟩

omit [NeZero m] in
/-- `d_c(c) = 0`. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem basePos_self (c : ZMod m) : basePos c c = 0 := by
  simp [basePos]

/-- A vertex other than `u` sits at a positive position when read from `u`. -/
theorem basePos_self_lt_of_ne {u v : ZMod m} (h : u ≠ v) : basePos u u < basePos u v := by
  rw [basePos_self]
  exact lt_of_le_of_ne (basePos_nonneg u v) fun e =>
    h (basePos_injective u ((basePos_self u).trans e))

/-- For `d_c(u) < d_c(v)`, `x` lies strictly between `u` and `v` exactly when
`d_c(u) < d_c(x) < d_c(v)`. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem sbtw_iff_basePos {c u v : ZMod m} (huv : basePos c u < basePos c v) (x : ZMod m) :
    sbtw u x v ↔ basePos c u < basePos c x ∧ basePos c x < basePos c v := by
  rw [sbtw_iff_sbtw_basePos c, Int.sbtw_iff]
  omega

/-- For `d_c(u) < d_c(v)`, `x` lies strictly between `v` and `u` exactly when `d_c(x) < d_c(u)` or
`d_c(x) > d_c(v)`. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem sbtw_iff_basePos' {c u v : ZMod m} (huv : basePos c u < basePos c v) (x : ZMod m) :
    sbtw v x u ↔ basePos c x < basePos c u ∨ basePos c v < basePos c x := by
  rw [sbtw_iff_sbtw_basePos c, Int.sbtw_iff]
  have := basePos_nonneg c x
  omega

/-- For `d_c(u) < d_c(v)`, `{u, v}` is a side exactly when `d_c(v) = d_c(u) + 1` or
`(d_c(u), d_c(v)) = (0, m-1)`; this needs no bound on `m`. -/
theorem isSide_mk_iff_basePos {c u v : ZMod m} (huv : basePos c u < basePos c v) :
    IsSide s(u, v) ↔
      basePos c v = basePos c u + 1 ∨ (basePos c u = 0 ∧ basePos c v = (m : ℤ) - 1) := by
  have hi := basePos_injective c
  rw [isSide_mk_iff]
  constructor
  · rintro (rfl | rfl)
    · rw [basePos_add_one] at huv ⊢
      have := basePos_nonneg c u
      split_ifs at huv ⊢ <;> omega
    · rw [basePos_add_one] at huv ⊢
      have := basePos_lt c v
      have := basePos_nonneg c v
      split_ifs at huv ⊢ <;> omega
  · rintro (h | ⟨h1, h2⟩)
    · exact .inl (hi (by rw [basePos_add_one, if_neg (by have := basePos_lt c v; omega), h]))
    · exact .inr (hi (by rw [basePos_add_one, if_pos (by omega), h1]))

/-- For `d_c(u) < d_c(v)`, `{u, v}` is a side exactly when `d_c(v) = d_c(u) + 1` or
`(d_c(u), d_c(v)) = (0, m-1)`. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem isSide_iff_basePos (_hm : 3 ≤ m) {c u v : ZMod m} (huv : basePos c u < basePos c v) :
    IsSide s(u, v) ↔
      basePos c v = basePos c u + 1 ∨ (basePos c u = 0 ∧ basePos c v = (m : ℤ) - 1) :=
  isSide_mk_iff_basePos huv

/-- `σ ↦ d_c(σ)` maps the sides of the `m`-gon bijectively onto the sides of `[0, m-1]`. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem bijOn_basePosSeg_isSide (hm : 3 ≤ m) (c : ZMod m) :
    Set.BijOn (basePosSeg c) {σ | IsSide σ} ↑(intervalSides 0 ((m : ℤ) - 1)) := by
  refine ⟨?_, (basePosSeg_injective c).injOn, ?_⟩
  · rintro σ ⟨i, rfl⟩
    simp only [Finset.mem_coe, intervalSides, Finset.mem_insert, Finset.mem_image, Finset.mem_Ico]
    have h0 := basePos_nonneg c i
    have hl := basePos_lt c i
    rw [basePosSeg_mk, basePos_add_one]
    split_ifs with h
    · left
      rw [min_eq_right h0, max_eq_left h0]
      ext
      · rfl
      · simp only
        omega
    · right
      refine ⟨basePos c i, ⟨h0, by omega⟩, ?_⟩
      rw [min_eq_left (by omega), max_eq_right (by omega)]
  · intro q hq
    simp only [Finset.mem_coe, intervalSides, Finset.mem_insert, Finset.mem_image,
      Finset.mem_Ico] at hq
    rcases hq with rfl | ⟨i, ⟨hi0, hi⟩, rfl⟩
    · obtain ⟨u, hu⟩ := exists_basePos_eq c (k := (m : ℤ) - 1) (by omega) (by omega)
      refine ⟨s(u, u + 1), ⟨u, rfl⟩, ?_⟩
      rw [basePosSeg_mk, basePos_add_one, if_pos (by omega), hu]
      ext <;> simp <;> omega
    · obtain ⟨u, hu⟩ := exists_basePos_eq c (k := i) hi0 (by omega)
      refine ⟨s(u, u + 1), ⟨u, rfl⟩, ?_⟩
      rw [basePosSeg_mk, basePos_add_one, if_neg (by omega), hu]
      ext <;> simp

/-- `σ ↦ d_c(σ)` maps the diagonals of the `m`-gon bijectively onto `D[0, m-1]`. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem bijOn_basePosSeg_isDiagonal (c : ZMod m) :
    Set.BijOn (basePosSeg c) {σ | IsDiagonal σ} ↑(intervalDiagonals 0 ((m : ℤ) - 1)) := by
  refine ⟨?_, (basePosSeg_injective c).injOn, ?_⟩
  · intro σ hσ
    obtain ⟨u, v, rfl, huv⟩ := IsSegment.exists_basePos_lt c hσ.1
    have hs := (isSide_mk_iff_basePos huv).not.1 hσ.2
    have := basePos_nonneg c u
    have := basePos_lt c v
    simp only [Finset.mem_coe, intervalDiagonals, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, basePosSeg_mk_of_lt huv, ne_eq, Prod.mk.injEq]
    omega
  · intro q hq
    simp only [Finset.mem_coe, intervalDiagonals, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, ne_eq] at hq
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩ := hq
    obtain ⟨u, hu⟩ := exists_basePos_eq c h1 (by omega)
    obtain ⟨v, hv⟩ := exists_basePos_eq c h3 (by omega)
    have huv : basePos c u < basePos c v := by omega
    refine ⟨s(u, v), ⟨?_, ?_⟩, ?_⟩
    · rintro h
      rw [Sym2.mk_isDiag_iff] at h
      subst h
      omega
    · rw [isSide_mk_iff_basePos huv, hu, hv]
      rintro (h | ⟨h, h'⟩)
      · omega
      · exact h6 (Prod.ext h h')
    · rw [basePosSeg_mk_of_lt huv, hu, hv]

/-- Two segments cross exactly when their images interleave. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem cross_iff_interleave (c : ZMod m) {σ τ : Sym2 (ZMod m)} (hσ : IsSegment σ)
    (hτ : IsSegment τ) : Cross σ τ ↔ Interleave (basePosSeg c σ) (basePosSeg c τ) := by
  obtain ⟨u, v, rfl, huv⟩ := IsSegment.exists_basePos_lt c hσ
  obtain ⟨x, y, rfl, hxy⟩ := IsSegment.exists_basePos_lt c hτ
  rw [cross_mk_iff_basePos c, basePosSeg_mk_of_lt huv, basePosSeg_mk_of_lt hxy, Interleave,
    Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff]
  simp only
  omega

/-- Crossing is symmetric. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem cross_comm {σ τ : Sym2 (ZMod m)} : Cross σ τ ↔ Cross τ σ :=
  ⟨Cross.symm, Cross.symm⟩

/-- No segment crosses a side. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem not_cross_of_isSide {σ τ : Sym2 (ZMod m)} (hτ : IsSide τ) : ¬Cross σ τ := by
  obtain ⟨i, rfl⟩ := hτ
  induction σ using Sym2.ind with | _ u v => ?_
  rw [cross_mk_iff_basePos i, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff,
    basePos_add_one, basePos_self]
  have := basePos_nonneg i u
  have := basePos_nonneg i v
  split_ifs <;> omega

/-- No two segments of a triangulation cross. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem IsTriangulation.not_cross {T : Finset (Sym2 (ZMod m))} (hT : IsTriangulation T)
    {σ τ : Sym2 (ZMod m)} (hσ : σ ∈ segments T) (hτ : τ ∈ segments T) : ¬Cross σ τ := by
  rcases mem_segments.1 hσ with hσ | hσ
  · rcases mem_segments.1 hτ with hτ | hτ
    · exact hT.noncrossing σ hσ τ hτ
    · exact not_cross_of_isSide hτ
  · exact fun h => not_cross_of_isSide hσ h.symm

/-- `T ↦ d_c(T)` is a bijection from the triangulations of the convex `m`-gon onto the
triangulations of `[0, m-1]`. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem bijOn_basePosTri (c : ZMod m) :
    Set.BijOn (basePosTri c) {T | IsTriangulation T}
      {S | IsIntervalTriangulation 0 ((m : ℤ) - 1) S} := by
  classical
  have hD := bijOn_basePosSeg_isDiagonal c
  refine ⟨?_, (Finset.image_injective (basePosSeg_injective c)).injOn, ?_⟩
  · intro T hT
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hq
      exact hD.mapsTo (hT.isDiagonal σ hσ)
    · intro q hq r hr hqr
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hr
      exact hT.noncrossing σ hσ τ hτ
        ((cross_iff_interleave c (hT.isDiagonal σ hσ).1 (hT.isDiagonal τ hτ).1).2 hqr)
    · intro q hq hqT
      obtain ⟨σ, hσ, rfl⟩ := hD.surjOn hq
      have hσT : σ ∉ T := fun h => hqT (Finset.mem_image_of_mem _ h)
      obtain ⟨τ, hτ, hστ⟩ := hT.maximal σ hσ hσT
      exact ⟨basePosSeg c τ, Finset.mem_image_of_mem _ hτ,
        (cross_iff_interleave c hσ.1 (hT.isDiagonal τ hτ).1).1 hστ⟩
  · intro S hS
    refine ⟨Finset.univ.filter fun σ => IsDiagonal σ ∧ basePosSeg c σ ∈ S, ?_, ?_⟩
    · refine ⟨fun σ hσ => (Finset.mem_filter.1 hσ).2.1, ?_, ?_⟩
      · intro σ hσ τ hτ hστ
        have hσ' := (Finset.mem_filter.1 hσ).2
        have hτ' := (Finset.mem_filter.1 hτ).2
        exact hS.2.1 _ hσ'.2 _ hτ'.2 ((cross_iff_interleave c hσ'.1.1 hτ'.1.1).1 hστ)
      · intro σ hσ hσT
        have hσS : basePosSeg c σ ∉ S := fun h =>
          hσT (Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ, h⟩)
        obtain ⟨q, hq, hσq⟩ := hS.2.2 _ (hD.mapsTo hσ) hσS
        obtain ⟨τ, hτ, rfl⟩ := hD.surjOn (hS.1 hq)
        exact ⟨τ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hτ, hq⟩,
          (cross_iff_interleave c hσ.1 hτ.1).2 hσq⟩
    · ext q
      simp only [basePosTri, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun ⟨σ, ⟨_, hσ⟩, h⟩ => h ▸ hσ, fun hq => ?_⟩
      obtain ⟨σ, hσ, rfl⟩ := hD.surjOn (hS.1 hq)
      exact ⟨σ, ⟨hσ, hq⟩, rfl⟩

/-- A segment `σ` is a segment of `T` exactly when `d_c(σ)` is a segment of `d_c(T)`, for every set
`T` of segments. -/
@[cluster_algebras "lem_polygon_base_point"]
theorem mem_segments_iff_basePosSeg (hm : 3 ≤ m) (c : ZMod m) (T : Finset (Sym2 (ZMod m)))
    {σ : Sym2 (ZMod m)} :
    σ ∈ segments T ↔ basePosSeg c σ ∈ intervalSegments 0 ((m : ℤ) - 1) (basePosTri c T) := by
  have hS := bijOn_basePosSeg_isSide hm c
  rw [mem_segments, intervalSegments, Finset.mem_union, basePosTri,
    (basePosSeg_injective c).mem_finset_image]
  refine or_congr Iff.rfl ⟨fun h => hS.mapsTo h, fun h => ?_⟩
  obtain ⟨τ, hτ, hτσ⟩ := hS.surjOn h
  rwa [← basePosSeg_injective c hτσ]

/-! ### The apex over a segment -/

omit [NeZero m] in
/-- `s(u, v)` is a segment as soon as `u ≠ v`. -/
theorem isSegment_mk_of_ne {u v : ZMod m} (h : u ≠ v) : IsSegment s(u, v) := by
  rwa [IsSegment, Sym2.mk_isDiag_iff]

/-- For `d_c(u) < d_c(v)`, `s(u, v)` is a segment of `T` exactly when `(d_c(u), d_c(v))` is a
segment of `d_c(T)`. -/
theorem mem_segments_iff_of_basePos_lt (hm : 3 ≤ m) {c u v : ZMod m}
    (T : Finset (Sym2 (ZMod m))) (huv : basePos c u < basePos c v) :
    s(u, v) ∈ segments T ↔
      (basePos c u, basePos c v) ∈ intervalSegments 0 ((m : ℤ) - 1) (basePosTri c T) := by
  rw [mem_segments_iff_basePosSeg hm c T, basePosSeg_mk_of_lt huv]

/-- **The apex over a segment of a triangulation.** If `{a, c}` is a segment of a triangulation
`T` and some vertex lies strictly between `a` and `c`, there is exactly one `b` strictly between
`a` and `c` such that `{a, b}` and `{b, c}` are both segments of `T`. -/
@[cluster_algebras "lem_triangulation_apex"]
theorem IsTriangulation.existsUnique_apex (hm : 3 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) {a c : ZMod m} (hac : s(a, c) ∈ segments T)
    (hx : ∃ x, sbtw a x c) :
    ∃! b, sbtw a b c ∧ s(a, b) ∈ segments T ∧ s(b, c) ∈ segments T := by
  obtain ⟨x, hx⟩ := hx
  have hac' : a ≠ c := by rintro rfl; exact sbtw_irrefl_left_right hx
  have h0 := basePos_self a
  have hi := basePos_injective a
  have hpos := basePos_self_lt_of_ne hac'
  have hxK := (sbtw_iff_basePos hpos x).1 hx
  rw [h0] at hxK
  have hS : IsIntervalTriangulation 0 ((m : ℤ) - 1) (basePosTri a T) :=
    (bijOn_basePosTri a).mapsTo hT
  have hK := (mem_segments_iff_of_basePos_lt hm T hpos).1 hac
  rw [h0] at hK
  have hlt := basePos_lt a c
  obtain ⟨j, ⟨hj0, hjK, hj1, hj2⟩, hju⟩ :=
    IsIntervalTriangulation.existsUnique_apex (by omega) hS (by omega) hK
  obtain ⟨b, hb⟩ := exists_basePos_eq a (k := j) hj0.le (by omega)
  have hab : basePos a a < basePos a b := by rwa [h0, hb]
  have hbc : basePos a b < basePos a c := by rwa [hb]
  refine ⟨b, ⟨(sbtw_iff_basePos hpos b).2 ⟨hab, hbc⟩,
    (mem_segments_iff_of_basePos_lt hm T hab).2 (by rwa [h0, hb]),
    (mem_segments_iff_of_basePos_lt hm T hbc).2 (by rwa [hb])⟩, ?_⟩
  rintro y ⟨hy, hy1, hy2⟩
  obtain ⟨hay, hyc⟩ := (sbtw_iff_basePos hpos y).1 hy
  have e1 := (mem_segments_iff_of_basePos_lt hm T hay).1 hy1
  have e2 := (mem_segments_iff_of_basePos_lt hm T hyc).1 hy2
  rw [h0] at e1 hay
  exact hi ((hju _ ⟨hay, hyc, e1, e2⟩).trans hb.symm)

/-! ### Quadrilaterals -/

section Quadrilateral

variable {a b c d : ZMod m}

/-- Read from `a`, the four vertices of a quadrilateral have increasing positions
`0 < d_a(b) < d_a(c) < d_a(d)`. -/
theorem quadrilateral_basePos (hb : sbtw a b c) (hd : sbtw c d a) :
    basePos a a = 0 ∧ 0 < basePos a b ∧ basePos a b < basePos a c ∧
      basePos a c < basePos a d ∧ basePos a d < m := by
  rw [sbtw_iff_sbtw_basePos a, Int.sbtw_iff, basePos_self] at hb hd
  have := basePos_nonneg a b
  have := basePos_nonneg a c
  have := basePos_nonneg a d
  have := basePos_lt a d
  refine ⟨basePos_self a, ?_⟩
  omega

/-- If `b` lies strictly between `a` and `c` and `d` strictly between `c` and `a`, then
`a, b, c, d` are pairwise distinct, and `{a, c}` and `{b, d}` are diagonals that cross. -/
@[cluster_algebras "lem_polygon_quadrilateral"]
theorem quadrilateral_cross (hb : sbtw a b c) (hd : sbtw c d a) :
    (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∧ IsDiagonal s(a, c) ∧
      IsDiagonal s(b, d) ∧ Cross s(a, c) s(b, d) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  have ne : ∀ x y : ZMod m, basePos a x ≠ basePos a y → x ≠ y := fun x y h e => h (e ▸ rfl)
  refine ⟨⟨ne _ _ (by omega), ne _ _ (by omega), ne _ _ (by omega), ne _ _ (by omega),
    ne _ _ (by omega), ne _ _ (by omega)⟩, ⟨isSegment_mk_of_ne (ne _ _ (by omega)), ?_⟩,
    ⟨isSegment_mk_of_ne (ne _ _ (by omega)), ?_⟩, ⟨a, c, b, d, rfl, rfl, hb, hd⟩⟩ <;>
    · rw [isSide_mk_iff_basePos (c := a) (by omega)]
      omega

/-- The listings `(a, b, c)`, `(a, c, d)`, `(a, b, d)` and `(b, c, d)` are clockwise. -/
@[cluster_algebras "lem_polygon_quadrilateral"]
theorem quadrilateral_isClockwise (hb : sbtw a b c) (hd : sbtw c d a) :
    IsClockwise a b c ∧ IsClockwise a c d ∧ IsClockwise a b d ∧ IsClockwise b c d := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  simp only [IsClockwise, sbtw_iff_sbtw_basePos a, Int.sbtw_iff]
  omega

/-- Among the six segments `{a, b}`, `{b, c}`, `{c, d}`, `{d, a}`, `{a, c}`, `{b, d}`, the only
crossing pair is `{a, c}`, `{b, d}`. -/
@[cluster_algebras "lem_polygon_quadrilateral"]
theorem quadrilateral_eq_of_cross (hb : sbtw a b c) (hd : sbtw c d a) :
    ∀ σ ∈ ({s(a, b), s(b, c), s(c, d), s(d, a), s(a, c), s(b, d)} : Finset (Sym2 (ZMod m))),
      ∀ τ ∈ ({s(a, b), s(b, c), s(c, d), s(d, a), s(a, c), s(b, d)} : Finset (Sym2 (ZMod m))),
        Cross σ τ → (σ = s(a, c) ∧ τ = s(b, d)) ∨ (σ = s(b, d) ∧ τ = s(a, c)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  intro σ hσ τ hτ h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ hτ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (exfalso; rw [cross_mk_iff_basePos a, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff,
        Int.sbtw_iff] at h; omega)
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl⟩

/-- Two segments whose images interleave cross. -/
theorem cross_mk_of_interleave (c : ZMod m) {u v x y : ZMod m}
    (h : Interleave (basePosSeg c s(u, v)) (basePosSeg c s(x, y))) : Cross s(u, v) s(x, y) := by
  refine (cross_iff_interleave c (isSegment_mk_of_ne ?_) (isSegment_mk_of_ne ?_)).2 h <;>
    · rintro rfl
      simp only [basePosSeg_mk, Interleave] at h
      omega

/-- The case `0 < d_a(x) < d_a(c) < d_a(y)` of `quadrilateral_cross_left`. -/
theorem quadrilateral_cross_left_of_basePos (hb : sbtw a b c) (hd : sbtw c d a) {x y : ZMod m}
    (H : 0 < basePos a x ∧ basePos a x < basePos a c ∧ basePos a c < basePos a y) :
    s(x, y) = s(b, d) ∨ Cross s(x, y) s(a, b) ∨ Cross s(x, y) s(b, c) ∨
      Cross s(x, y) s(c, d) ∨ Cross s(x, y) s(d, a) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  have hi := basePos_injective a
  rcases lt_trichotomy (basePos a x) (basePos a b) with hxb | hxb | hxb
  · exact Or.inr <| Or.inl <|
      cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
  · rcases lt_trichotomy (basePos a y) (basePos a d) with hyd | hyd | hyd
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
        cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
    · rw [hi hxb, hi hyd]; exact Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
  · exact Or.inr <| Or.inr <| Or.inl <|
      cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)

/-- The case `d_a(b) < d_a(x) < d_a(d)`, `d_a(y) ∉ [d_a(b), d_a(d)]` of
`quadrilateral_cross_right`. -/
theorem quadrilateral_cross_right_of_basePos (hb : sbtw a b c) (hd : sbtw c d a) {x y : ZMod m}
    (H : basePos a b < basePos a x ∧ basePos a x < basePos a d ∧
      (basePos a y < basePos a b ∨ basePos a d < basePos a y)) :
    s(x, y) = s(a, c) ∨ Cross s(x, y) s(a, b) ∨ Cross s(x, y) s(b, c) ∨
      Cross s(x, y) s(c, d) ∨ Cross s(x, y) s(d, a) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  have hi := basePos_injective a
  have := basePos_nonneg a y
  rcases lt_trichotomy (basePos a x) (basePos a c) with hxc | hxc | hxc
  · exact Or.inr <| Or.inr <| Or.inl <|
      cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
  · rcases H.2.2 with hy | hy
    · rcases eq_or_lt_of_le this with hy0 | hy0
      · rw [hi hxc, hi (hy0.symm.trans h0.symm), Sym2.eq_swap]; exact Or.inl rfl
      · exact Or.inr <| Or.inl <|
          cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      cross_mk_of_interleave a (by simp only [basePosSeg_mk, Interleave]; omega)

/-- Every segment crossing `{a, c}` is `{b, d}` or crosses one of `{a, b}`, `{b, c}`, `{c, d}`,
`{d, a}`. -/
@[cluster_algebras "lem_polygon_quadrilateral"]
theorem quadrilateral_cross_left (hb : sbtw a b c) (hd : sbtw c d a) {e : Sym2 (ZMod m)}
    (he : Cross e s(a, c)) :
    e = s(b, d) ∨ Cross e s(a, b) ∨ Cross e s(b, c) ∨ Cross e s(c, d) ∨ Cross e s(d, a) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  induction e using Sym2.ind with | _ x y => ?_
  have := basePos_nonneg a x
  have := basePos_nonneg a y
  rw [cross_mk_iff_basePos a, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff] at he
  rcases (by omega : (0 < basePos a x ∧ basePos a x < basePos a c ∧ basePos a c < basePos a y) ∨
      (0 < basePos a y ∧ basePos a y < basePos a c ∧ basePos a c < basePos a x)) with H | H
  · exact quadrilateral_cross_left_of_basePos hb hd H
  · simpa only [Sym2.eq_swap (a := x)] using quadrilateral_cross_left_of_basePos hb hd H

/-- Every segment crossing `{b, d}` is `{a, c}` or crosses one of `{a, b}`, `{b, c}`, `{c, d}`,
`{d, a}`. -/
@[cluster_algebras "lem_polygon_quadrilateral"]
theorem quadrilateral_cross_right (hb : sbtw a b c) (hd : sbtw c d a) {e : Sym2 (ZMod m)}
    (he : Cross e s(b, d)) :
    e = s(a, c) ∨ Cross e s(a, b) ∨ Cross e s(b, c) ∨ Cross e s(c, d) ∨ Cross e s(d, a) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := quadrilateral_basePos hb hd
  induction e using Sym2.ind with | _ x y => ?_
  have := basePos_nonneg a x
  have := basePos_nonneg a y
  rw [cross_mk_iff_basePos a, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff] at he
  rcases (by omega : (basePos a b < basePos a x ∧ basePos a x < basePos a d ∧
        (basePos a y < basePos a b ∨ basePos a d < basePos a y)) ∨
      (basePos a b < basePos a y ∧ basePos a y < basePos a d ∧
        (basePos a x < basePos a b ∨ basePos a d < basePos a x))) with H | H
  · exact quadrilateral_cross_right_of_basePos hb hd H
  · simpa only [Sym2.eq_swap (a := x)] using quadrilateral_cross_right_of_basePos hb hd H

end Quadrilateral

/-! ### Flips -/

/-- `b` is an apex over `{a, c}` and `d` an apex over `{c, a}` in `T`: `b` lies strictly between
`a` and `c`, `d` strictly between `c` and `a`, and the four rim segments `{a, b}`, `{b, c}`,
`{c, d}`, `{d, a}` are segments of `T`. For `{a, c} ∈ T` these `b` and `d` are unique
(`IsTriangulation.existsUnique_apex_of_mem`). -/
def IsFlipQuadrilateral (T : Finset (Sym2 (ZMod m))) (a b c d : ZMod m) : Prop :=
  sbtw a b c ∧ sbtw c d a ∧ s(a, b) ∈ segments T ∧ s(b, c) ∈ segments T ∧
    s(c, d) ∈ segments T ∧ s(d, a) ∈ segments T

variable {T : Finset (Sym2 (ZMod m))} {a b c d : ZMod m}

/-- Some vertex lies strictly between the endpoints `u` and `v` of a diagonal `s(u, v)`. -/
theorem IsDiagonal.exists_sbtw {u v : ZMod m} (h : IsDiagonal s(u, v)) : ∃ x, sbtw u x v := by
  have huv : u ≠ v := fun e => h.1 (Sym2.mk_isDiag_iff.2 e)
  have h0 := basePos_self u
  have hpos := basePos_self_lt_of_ne huv
  have hs := (isSide_mk_iff_basePos hpos).not.1 h.2
  have := basePos_lt u v
  rw [h0] at hs hpos
  obtain ⟨x, hx⟩ := exists_basePos_eq u (k := 1) (by omega) (by omega)
  exact ⟨x, (sbtw_iff_basePos (by rwa [h0]) x).2 (by omega)⟩

/-- A segment of `T` other than `γ` is a segment of the flip of `T` at `γ`. -/
theorem mem_segments_flipTriangulation {γ γ' r : Sym2 (ZMod m)} (hr : r ∈ segments T)
    (hne : r ≠ γ) : r ∈ segments (flipTriangulation T γ γ') := by
  rcases mem_segments.1 hr with hr | hr
  · exact mem_segments.2 (Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hne, hr⟩)))
  · exact mem_segments.2 (Or.inr hr)

/-- The four rim segments of a flip quadrilateral differ from `{a, c}`. -/
theorem IsFlipQuadrilateral.rim_ne (hq : IsFlipQuadrilateral T a b c d) :
    s(a, b) ≠ s(a, c) ∧ s(b, c) ≠ s(a, c) ∧ s(c, d) ≠ s(a, c) ∧ s(d, a) ≠ s(a, c) := by
  obtain ⟨⟨n1, n2, n3, n4, n5, n6⟩, -⟩ := quadrilateral_cross hq.1 hq.2.1
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · intro h
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all

/-- **The two apexes over a diagonal of a triangulation.** For `{a, c} ∈ T`
there is exactly one `b` strictly between `a` and `c`, and exactly one `d` strictly between `c`
and `a`, such that `{a, b}`, `{b, c}`, respectively `{c, d}`, `{d, a}`, are segments of `T`. -/
@[cluster_algebras "lem_flip_exists"]
theorem IsTriangulation.existsUnique_apex_of_mem (hm : 4 ≤ m) (hT : IsTriangulation T)
    (hγ : s(a, c) ∈ T) :
    (∃! b, sbtw a b c ∧ s(a, b) ∈ segments T ∧ s(b, c) ∈ segments T) ∧
      ∃! d, sbtw c d a ∧ s(c, d) ∈ segments T ∧ s(d, a) ∈ segments T := by
  have hdiag := hT.isDiagonal _ hγ
  have hseg : s(a, c) ∈ segments T := mem_segments.2 (Or.inl hγ)
  refine ⟨IsTriangulation.existsUnique_apex (by omega) hT hseg (IsDiagonal.exists_sbtw hdiag),
    IsTriangulation.existsUnique_apex (by omega) hT (by rwa [Sym2.eq_swap])
      (IsDiagonal.exists_sbtw (by rwa [Sym2.eq_swap] at hdiag))⟩

/-- With `b` and `d` the apexes over `{a, c}` and `{c, a}`, `{b, d}` is a diagonal not in `T` and
`(T \ {γ}) ∪ {{b, d}}` is a triangulation: `{b, d}` replaces `γ = {a, c}` in a flip of `T`. -/
@[cluster_algebras "lem_flip_exists"]
theorem IsFlipQuadrilateral.isFlipReplacement (hT : IsTriangulation T)
    (hγ : s(a, c) ∈ T) (hq : IsFlipQuadrilateral T a b c d) :
    IsFlipReplacement T s(a, c) s(b, d) := by
  obtain ⟨r1, r2, r3, r4⟩ := hq.rim_ne
  obtain ⟨hb, hd, hab, hbc, hcd, hda⟩ := hq
  obtain ⟨-, -, hbd, hcross⟩ := quadrilateral_cross hb hd
  have hbdT : s(b, d) ∉ T := fun h => hT.noncrossing _ hγ _ h hcross
  have rim : ∀ f ∈ T, f ≠ s(a, c) → Cross f s(b, d) → False := by
    intro f hf hfγ hfc
    have hf' : f ∈ segments T := mem_segments.2 (Or.inl hf)
    rcases quadrilateral_cross_right hb hd hfc with h | h | h | h | h
    exacts [hfγ h, IsTriangulation.not_cross hT hf' hab h, IsTriangulation.not_cross hT hf' hbc h,
      IsTriangulation.not_cross hT hf' hcd h, IsTriangulation.not_cross hT hf' hda h]
  refine ⟨hT, hγ, hbd, hbdT, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    exacts [hbd, hT.isDiagonal e (Finset.mem_of_mem_erase he)]
  · intro e he f hf hef
    rcases Finset.mem_insert.1 he with rfl | he <;> rcases Finset.mem_insert.1 hf with rfl | hf
    · exact not_cross_self _ hef
    · exact rim f (Finset.mem_of_mem_erase hf) (Finset.ne_of_mem_erase hf) hef.symm
    · exact rim e (Finset.mem_of_mem_erase he) (Finset.ne_of_mem_erase he) hef
    · exact hT.noncrossing e (Finset.mem_of_mem_erase he) f (Finset.mem_of_mem_erase hf) hef
  · intro e he heT'
    by_cases heγ : e = s(a, c)
    · exact ⟨s(b, d), Finset.mem_insert_self _ _, heγ ▸ hcross⟩
    have heT : e ∉ T := fun h => heT' (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨heγ, h⟩))
    obtain ⟨f, hf, hef⟩ := hT.maximal e he heT
    by_cases hfγ : f = s(a, c)
    · subst hfγ
      have key : ∀ r ∈ segments T, r ≠ s(a, c) → Cross e r →
          ∃ f ∈ flipTriangulation T s(a, c) s(b, d), Cross e f := by
        intro r hr hrγ her
        rcases mem_segments.1 hr with hr | hr
        · exact ⟨r, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hrγ, hr⟩), her⟩
        · exact absurd her (not_cross_of_isSide hr)
      rcases quadrilateral_cross_left hb hd hef with h | h | h | h | h
      exacts [absurd (h ▸ Finset.mem_insert_self _ _) heT', key _ hab r1 h, key _ hbc r2 h,
        key _ hcd r3 h, key _ hda r4 h]
    · exact ⟨f, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hfγ, hf⟩), hef⟩

/-- `{b, d}` is the only diagonal `γ'' ∉ T` for which `(T \ {γ}) ∪ {γ''}` is a triangulation. -/
@[cluster_algebras "lem_flip_exists"]
theorem IsFlipQuadrilateral.eq_of_isFlipReplacement (hT : IsTriangulation T)
    (hq : IsFlipQuadrilateral T a b c d) {γ'' : Sym2 (ZMod m)}
    (h : IsFlipReplacement T s(a, c) γ'') : γ'' = s(b, d) := by
  obtain ⟨r1, r2, r3, r4⟩ := hq.rim_ne
  obtain ⟨hb, hd, hab, hbc, hcd, hda⟩ := hq
  obtain ⟨-, -, hγ'', hγ''T, hT''⟩ := h
  obtain ⟨f, hf, hcf⟩ := hT.maximal _ hγ'' hγ''T
  have hmem : γ'' ∈ segments (flipTriangulation T s(a, c) γ'') :=
    mem_segments.2 (Or.inl (Finset.mem_insert_self _ _))
  by_cases hfγ : f = s(a, c)
  · subst hfγ
    rcases quadrilateral_cross_left hb hd hcf with h | h | h | h | h
    exacts [h,
      absurd h (IsTriangulation.not_cross hT'' hmem (mem_segments_flipTriangulation hab r1)),
      absurd h (IsTriangulation.not_cross hT'' hmem (mem_segments_flipTriangulation hbc r2)),
      absurd h (IsTriangulation.not_cross hT'' hmem (mem_segments_flipTriangulation hcd r3)),
      absurd h (IsTriangulation.not_cross hT'' hmem (mem_segments_flipTriangulation hda r4))]
  · exact absurd hcf (hT''.noncrossing _ (Finset.mem_insert_self _ _) _
      (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hfγ, hf⟩)))

/-- A triangle of `T` containing `a` and `c` is `{a, b, c}` or `{a, c, d}`. -/
private theorem IsFlipQuadrilateral.eq_of_isTriangle (hm : 3 ≤ m) (hT : IsTriangulation T)
    (hγ : s(a, c) ∈ T) (hq : IsFlipQuadrilateral T a b c d) {t : Finset (ZMod m)}
    (ht : IsTriangle T t) (ha : a ∈ t) (hc : c ∈ t) : t = {a, b, c} ∨ t = {a, c, d} := by
  obtain ⟨hb, hd, hab, hbc, hcd, hda⟩ := hq
  obtain ⟨⟨-, n2, -, -, -, -⟩, -⟩ := quadrilateral_cross hb hd
  obtain ⟨hcard, hseg⟩ := ht
  have hac : s(a, c) ∈ segments T := mem_segments.2 (Or.inl hγ)
  have hca : s(c, a) ∈ segments T := by rwa [Sym2.eq_swap]
  obtain ⟨x, hx⟩ := Finset.card_pos.1 (show 0 < ((t.erase a).erase c).card by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨n2.symm, hc⟩), Finset.card_erase_of_mem ha,
      hcard]
    omega)
  obtain ⟨hxc, hxa, hx⟩ := by simpa only [Finset.mem_erase] using hx
  have ht := (Finset.eq_of_subset_of_card_le (s := {a, c, x}) (t := t)
    (by simp [Finset.insert_subset_iff, ha, hc, hx])
    (by rw [hcard, Finset.card_eq_three.2 ⟨a, c, x, n2, Ne.symm hxa, Ne.symm hxc, rfl⟩])).symm
  have hax := hseg a ha x hx (Ne.symm hxa)
  have hxc' := hseg x hx c hc hxc
  have h0 := basePos_self a
  have hi := basePos_injective a
  have hpos := basePos_self_lt_of_ne n2
  have := basePos_nonneg a x
  rcases lt_or_gt_of_ne (hi.ne hxc) with hlt | hgt
  · have hs : sbtw a x c := (sbtw_iff_basePos hpos x).2 ⟨by have := hi.ne hxa; omega, hlt⟩
    obtain rfl := (IsTriangulation.existsUnique_apex hm hT hac ⟨b, hb⟩).unique ⟨hs, hax, hxc'⟩
      ⟨hb, hab, hbc⟩
    exact .inl (by rw [ht, Finset.pair_comm])
  · have hs : sbtw c x a := (sbtw_iff_basePos' hpos x).2 (Or.inr hgt)
    obtain rfl := (IsTriangulation.existsUnique_apex hm hT hca ⟨d, hd⟩).unique
      ⟨hs, by rwa [Sym2.eq_swap], by rwa [Sym2.eq_swap]⟩ ⟨hd, hcd, hda⟩
    exact .inr ht

/-- The triangles of `T` having `γ = {a, c}` among their segments are exactly `{a, b, c}` and
`{a, c, d}`. -/
@[cluster_algebras "lem_flip_exists"]
theorem IsFlipQuadrilateral.isTriangle_iff (hm : 4 ≤ m) (hT : IsTriangulation T)
    (hγ : s(a, c) ∈ T) (hq : IsFlipQuadrilateral T a b c d) (t : Finset (ZMod m)) :
    (IsTriangle T t ∧ a ∈ t ∧ c ∈ t) ↔ t = {a, b, c} ∨ t = {a, c, d} := by
  refine ⟨fun ⟨ht, ha, hc⟩ => hq.eq_of_isTriangle (by omega) hT hγ ht ha hc, ?_⟩
  obtain ⟨hb, hd, hab, hbc, hcd, hda⟩ := hq
  obtain ⟨⟨n1, n2, n3, n4, -, n6⟩, -⟩ := quadrilateral_cross hb hd
  have hac : s(a, c) ∈ segments T := mem_segments.2 (Or.inl hγ)
  have hca : s(c, a) ∈ segments T := by rwa [Sym2.eq_swap]
  have had : s(a, d) ∈ segments T := by rwa [Sym2.eq_swap]
  have hba : s(b, a) ∈ segments T := by rwa [Sym2.eq_swap]
  have hcb : s(c, b) ∈ segments T := by rwa [Sym2.eq_swap]
  have hdc : s(d, c) ∈ segments T := by rwa [Sym2.eq_swap]
  rintro (rfl | rfl)
  · refine ⟨⟨Finset.card_eq_three.2 ⟨a, b, c, n1, n2, n4, rfl⟩, ?_⟩, by simp, by simp⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl) huv <;>
      first | exact absurd rfl huv | assumption
  · refine ⟨⟨Finset.card_eq_three.2 ⟨a, c, d, n2, n3, n6, rfl⟩, ?_⟩, by simp, by simp⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl) huv <;>
      first | exact absurd rfl huv | assumption

/-- **Every diagonal of a triangulation has exactly one flip.** The flip of a triangulation `T`
at any `γ ∈ T` exists, and its replacement is unique. -/
@[cluster_algebras "lem_flip_exists"]
theorem IsTriangulation.existsUnique_isFlipReplacement (hm : 4 ≤ m) (hT : IsTriangulation T)
    {γ : Sym2 (ZMod m)} (hγ : γ ∈ T) : ∃! γ', IsFlipReplacement T γ γ' := by
  induction γ using Sym2.ind with
  | _ a c =>
    obtain ⟨⟨b, hb, -⟩, ⟨d, hd, -⟩⟩ := IsTriangulation.existsUnique_apex_of_mem hm hT hγ
    have hq : IsFlipQuadrilateral T a b c d := ⟨hb.1, hd.1, hb.2.1, hb.2.2, hd.2.1, hd.2.2⟩
    exact ⟨s(b, d), hq.isFlipReplacement hT hγ,
      fun _ => hq.eq_of_isFlipReplacement hT⟩

/-! ### Vertices as natural numbers

Every vertex of `ZMod m` is the residue of a unique `k < m`, and on such residues equality,
equality of segments and circular betweenness are statements about natural numbers. -/

omit [NeZero m] in
/-- Residues of natural numbers below `m` are equal exactly when the numbers are. -/
theorem natCast_inj_of_lt {a b : ℕ} (ha : a < m) (hb : b < m) :
    (a : ZMod m) = b ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

omit [NeZero m] in
/-- Two segments with endpoints given by natural numbers below `m` are equal exactly when their
endpoints agree as natural numbers. -/
theorem sym2_natCast_eq_iff {a b c d : ℕ} (ha : a < m) (hb : b < m) (hc : c < m)
    (hd : d < m) :
    s((a : ZMod m), (b : ZMod m)) = s((c : ZMod m), (d : ZMod m)) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [Sym2.eq_iff, natCast_inj_of_lt ha hc, natCast_inj_of_lt hb hd, natCast_inj_of_lt ha hd,
    natCast_inj_of_lt hb hc]

/-- Every vertex is the residue of a natural number below `m`. -/
theorem exists_natCast_eq (v : ZMod m) : ∃ k < m, (k : ZMod m) = v :=
  ⟨v.val, ZMod.val_lt v, ZMod.natCast_zmod_val v⟩

/-- Circular betweenness of residues of natural numbers below `m`, read on the numbers. -/
theorem sbtw_natCast_iff {a b c : ℕ} (ha : a < m) (hb : b < m) (hc : c < m) :
    sbtw (a : ZMod m) (b : ZMod m) (c : ZMod m) ↔
      (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) := by
  rw [sbtw_iff_val, ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb, ZMod.val_natCast_of_lt hc]

end TypeA

end ClusterAlgebras

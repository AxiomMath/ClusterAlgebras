/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap
public import ClusterAlgebras.Plabic.TriangulationCorner

/-!
# Corner triangulations of a crossing

A *crossing* of a plabic graph is a white internal vertex with at least three darts. Let `w` be a
vertex with `m` darts, listed counterclockwise by the rotation `σ`. In the polygon of corners of
`w`, the corner following the dart `a` counterclockwise is labelled `a`, so going clockwise around
`w` the corners are `a, σ⁻¹ a, σ⁻² a, …`, and the side between the corners `a` and `σ⁻¹ a` is
crossed by the dart `a`. A *corner labelling* of `w` is a bijection `λ : ℤ/m → w` with
`λ(i + 1) = σ⁻¹(λ i)`; it identifies the polygon of corners with the convex `m`-gon. A *corner
triangulation* of `w` is a set `D` of two-element subsets of `w` which, pulled back along some
corner labelling, is a triangulation of the `m`-gon. Its segments are its elements and the sides
`{a, σ⁻¹ a}`, its triangles the three-element subsets of `w` all of whose pairs are segments, and
a listing `(x, y, z)` is clockwise when `y` occurs before `z` in `σ⁻¹ x, σ⁻² x, …`.

Every corner labelling then sees a triangulation, since two corner labellings differ by a
rotation of `ℤ/m`, and rotations preserve triangulations. A corner labelling carries segments,
triangles and clockwise listings of the pulled-back triangulation to those of `D`; from this, a
side of the polygon of corners lies in exactly one triangle of `D` and an element of `D` in
exactly two, and `D` can be flipped at any of its elements.

## Main definitions

* `ClusterAlgebras.PlabicData.IsCrossing`: a crossing of a plabic graph.
* `ClusterAlgebras.RotationSystem.IsCornerLabelling`: a corner labelling of a vertex.
* `ClusterAlgebras.RotationSystem.cornerSide`: the side `{a, σ⁻¹ a}` of a dart.
* `ClusterAlgebras.RotationSystem.cornerPullback`: the pull-back `λ^* D` of a set of pairs of
  darts along a corner labelling.
* `ClusterAlgebras.RotationSystem.IsCornerTriangulation`: a corner triangulation, with its
  segments `cornerSegments`, triangles `IsCornerTriangle`/`cornerTriangles` and clockwise listings
  `IsCornerClockwise`.

## Main results

* `ClusterAlgebras.RotationSystem.IsCornerTriangulation.isTriangulation_cornerPullback`: every
  corner labelling sees a triangulation.
* `ClusterAlgebras.RotationSystem.IsCornerTriangulation.card_filter_cornerSide`,
  `ClusterAlgebras.RotationSystem.IsCornerTriangulation.card_filter_mem`: a side lies in exactly
  one triangle and an element of `D` in exactly two.
* `ClusterAlgebras.RotationSystem.IsCornerTriangulation.exists_flip`: the flip of a corner
  triangulation.

## Implementation notes

* Pairs of darts are elements of `Sym2 H`, as segments of the `m`-gon are elements of
  `Sym2 (ZMod m)`; a corner triangulation is a `Finset (Sym2 H)` whose elements are off the
  diagonal and inside `w`. Triangles are `Finset H`s, and "`s ⊆ τ`" is `s ∈ τ.sym2`.
* The corner notions only read the rotation `σ`, so they are stated for a `RotationSystem` and
  apply to plabic graphs by dot notation. The number `m` of darts is not fixed in advance: a
  corner triangulation asks for a corner labelling `ℤ/m → H` for some `m ≠ 0`, and any corner
  labelling has `m = |w|` (`IsCornerLabelling.card_eq`).
* The lemmas on triangles and flips are stated for a set `w` of at least three darts rather than
  for a crossing: that is all their proofs use, and a crossing has at least three darts
  (`PlabicData.IsCrossing.three_le_card`).
* "`y` occurs before `z` in `σ⁻¹ x, σ⁻² x, …`" is read as: `y` occurs at some position `j ≥ 1`
  at or before which `z` does not occur.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset TypeA

/-! ### Rotations of the polygon -/

section Rotation

variable {m : ℕ} [NeZero m]

/-- Circular betweenness on `ZMod m` is invariant under translation. -/
theorem sbtw_add_right_iff (s a b c : ZMod m) : sbtw (a + s) (b + s) (c + s) ↔ sbtw a b c := by
  rw [sbtw_iff_sbtw_basePos s, sbtw_iff_sbtw_basePos 0 a]
  simp [basePos]

/-- Translating both segments preserves crossing. -/
theorem Cross.map_add {e f : Sym2 (ZMod m)} (h : Cross e f) (s : ZMod m) :
    Cross (e.map (· + s)) (f.map (· + s)) := by
  obtain ⟨a, b, c, d, rfl, rfl, h1, h2⟩ := h
  exact ⟨a + s, b + s, c + s, d + s, rfl, rfl, (sbtw_add_right_iff s _ _ _).2 h1,
    (sbtw_add_right_iff s _ _ _).2 h2⟩

omit [NeZero m] in
/-- Translating a side gives a side. -/
theorem IsSide.map_add {e : Sym2 (ZMod m)} (h : IsSide e) (s : ZMod m) :
    IsSide (e.map (· + s)) := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨i + s, by rw [Sym2.map_mk, add_right_comm]⟩

/-- Translating by `s` and then by `-s` is the identity on segments. -/
theorem map_add_neg_map_add {G : Type*} [AddGroup G] (e : Sym2 G) (s : G) :
    (e.map (· + s)).map (· + -s) = e := by
  induction e using Sym2.ind with | _ a b => simp

omit [NeZero m] in
/-- Translating a diagonal gives a diagonal. -/
theorem IsDiagonal.map_add {e : Sym2 (ZMod m)} (h : IsDiagonal e) (s : ZMod m) :
    IsDiagonal (e.map (· + s)) := by
  refine ⟨?_, fun hs => h.2 ?_⟩
  · rw [IsSegment, Sym2.isDiag_map (add_left_injective s)]
    exact h.1
  · simpa only [map_add_neg_map_add] using hs.map_add (-s)

/-- **Rotations preserve triangulations.** If `T` is a triangulation of the `m`-gon, so is the
set of segments whose translate by `s` lies in `T`. -/
theorem IsTriangulation.filter_map_add {T : Finset (Sym2 (ZMod m))} (hT : IsTriangulation T)
    (s : ZMod m) : IsTriangulation (univ.filter fun e => e.map (· + s) ∈ T) := by
  refine ⟨fun e he => ?_, fun e he f hf hef => ?_, fun e he heT => ?_⟩
  · simpa only [map_add_neg_map_add] using (hT.isDiagonal _ (mem_filter.1 he).2).map_add (-s)
  · exact hT.noncrossing _ (mem_filter.1 he).2 _ (mem_filter.1 hf).2 (hef.map_add s)
  · have heT' : e.map (· + s) ∉ T := fun h => heT (mem_filter.2 ⟨mem_univ _, h⟩)
    obtain ⟨f, hf, hef⟩ := hT.maximal _ (he.map_add s) heT'
    refine ⟨f.map (· + -s), mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
    · simpa [Sym2.map_map, Function.comp_def] using hf
    · simpa only [map_add_neg_map_add] using hef.map_add (-s)

end Rotation

/-! ### Triangles over a segment of a triangulation -/

section Count

variable {m : ℕ} [NeZero m]

/-- A vertex other than `k` and `k + 1` lies strictly between `k + 1` and `k`. -/
theorem sbtw_add_one_of_ne {k y : ZMod m} (h1 : y ≠ k) (h2 : y ≠ k + 1) : sbtw (k + 1) y k := by
  have hi := basePos_injective k
  have e1 : basePos k y ≠ basePos k k := fun h => h1 (hi h)
  have e2 : basePos k y ≠ basePos k (k + 1) := fun h => h2 (hi h)
  rw [sbtw_iff_sbtw_basePos k, Int.sbtw_iff]
  simp only [basePos_add_one, basePos_self] at e1 e2 ⊢
  have := basePos_nonneg k y
  have := basePos_lt k y
  split_ifs at e2 ⊢ <;> omega

/-- A three-element set containing `x` and `y` is `{x, y, z}` for some `z` other than `x`, `y`. -/
theorem exists_eq_insert_insert_singleton {α : Type*} [DecidableEq α] {t : Finset α}
    (ht : t.card = 3) {x y : α} (hxy : x ≠ y) (hx : x ∈ t) (hy : y ∈ t) :
    ∃ z ∈ t, z ≠ x ∧ z ≠ y ∧ t = {x, y, z} := by
  obtain ⟨z, hz⟩ := Finset.card_pos.1 (show 0 < ((t.erase x).erase y).card by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hxy.symm, hy⟩), Finset.card_erase_of_mem hx,
      ht]
    omega)
  obtain ⟨hzy, hzx, hz⟩ := by simpa only [Finset.mem_erase] using hz
  refine ⟨z, hz, hzx, hzy, (Finset.eq_of_subset_of_card_le (s := {x, y, z}) (t := t)
    (by simp [Finset.insert_subset_iff, hx, hy, hz])
    (by rw [ht, Finset.card_eq_three.2 ⟨x, y, z, hxy, hzx.symm, hzy.symm, rfl⟩])).symm⟩

/-- **A side lies in exactly one triangle.** For a triangulation `T` of the `m`-gon, `m ≥ 3`,
exactly one triangle of `T` contains the side `{k, k + 1}`. -/
theorem IsTriangulation.card_filter_side (hm : 3 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) (k : ZMod m) :
    (univ.filter fun t : Finset (ZMod m) => IsTriangle T t ∧ s(k, k + 1) ∈ t.sym2).card = 1 := by
  have hne : ∀ n : ℕ, 0 < n → n < m → (n : ZMod m) ≠ 0 := fun n h0 hn h => by
    have := (natCast_inj_of_lt (m := m) (a := n) (b := 0) hn (by omega)).1 (by simpa using h)
    omega
  have h1 : (1 : ZMod m) ≠ 0 := by simpa using hne 1 (by omega) (by omega)
  have h2 : (2 : ZMod m) ≠ 0 := by simpa using hne 2 (by omega) (by omega)
  have hk1 : k ≠ k + 1 := fun h => h1 (by linear_combination -h)
  have hk2 : k ≠ k + 1 + 1 := fun h => h2 (by linear_combination -h)
  have hseg : s(k + 1, k) ∈ segments T := mem_segments.2 (Or.inr ⟨k, Sym2.eq_swap⟩)
  obtain ⟨x, ⟨hx, hx1, hx2⟩, hxu⟩ := IsTriangulation.existsUnique_apex hm hT hseg
    ⟨_, sbtw_self_add_one hk1.symm hk2⟩
  have hxk : x ≠ k := fun h => sbtw_irrefl_right (h ▸ hx)
  have hxk1 : x ≠ k + 1 := fun h => sbtw_irrefl_left (h ▸ hx)
  rw [card_eq_one]
  refine ⟨{k, k + 1, x}, ?_⟩
  ext t
  simp only [mem_filter, mem_univ, true_and, mem_singleton, Finset.mk_mem_sym2_iff]
  constructor
  · rintro ⟨⟨hcard, hs⟩, hk, hk'⟩
    obtain ⟨y, hy, hyk, hyk1, rfl⟩ := exists_eq_insert_insert_singleton hcard hk1 hk hk'
    obtain rfl := hxu y ⟨sbtw_add_one_of_ne hyk hyk1, hs _ hk' _ hy hyk1.symm, hs _ hy _ hk hyk⟩
    rfl
  · rintro rfl
    have hside : s(k, k + 1) ∈ segments T := mem_segments.2 (Or.inr ⟨k, rfl⟩)
    have hx1' : s(x, k + 1) ∈ segments T := by rwa [Sym2.eq_swap]
    have hx2' : s(k, x) ∈ segments T := by rwa [Sym2.eq_swap]
    refine ⟨⟨Finset.card_eq_three.2 ⟨k, k + 1, x, hk1, hxk.symm, hxk1.symm, rfl⟩, ?_⟩,
      by simp, by simp⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl) huv <;>
      first | exact absurd rfl huv | assumption

/-- A triangulation of the `m`-gon, `m ≥ 3`, with an element has `m ≥ 4`. -/
theorem IsTriangulation.four_le_of_mem {T : Finset (Sym2 (ZMod m))} (hT : IsTriangulation T)
    (hm : 3 ≤ m) {e : Sym2 (ZMod m)} (he : e ∈ T) : 4 ≤ m := by
  by_contra h
  have := IsTriangulation.eq_empty_of_eq_three (by omega) hT
  simp [this] at he

/-- A segment of `insert f (T.erase e)` other than `f` is a segment of `T`. -/
theorem mem_segments_of_mem_segments_insert_erase {T : Finset (Sym2 (ZMod m))}
    {e f r : Sym2 (ZMod m)} (hr : r ∈ segments (insert f (T.erase e))) (hrf : r ≠ f) :
    r ∈ segments T := by
  rcases mem_segments.1 hr with h | h
  · exact mem_segments.2 (Or.inl (mem_of_mem_erase ((mem_insert.1 h).resolve_left hrf)))
  · exact mem_segments.2 (Or.inr h)

/-- A diagonal `e ≠ f` is not a segment of `insert f (T.erase e)`. -/
theorem notMem_segments_insert_erase {T : Finset (Sym2 (ZMod m))} {e f : Sym2 (ZMod m)}
    (he : IsDiagonal e) (hef : e ≠ f) : e ∉ segments (insert f (T.erase e)) := by
  simp [hef, he.2]

/-- **A diagonal lies in exactly two triangles.** For a triangulation `T` of the `m`-gon,
`m ≥ 3`, exactly two triangles of `T` contain a given element of `T`. -/
theorem IsTriangulation.card_filter_mem (hm : 3 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) {e : Sym2 (ZMod m)} (he : e ∈ T) :
    (univ.filter fun t : Finset (ZMod m) => IsTriangle T t ∧ e ∈ t.sym2).card = 2 := by
  have hm4 := hT.four_le_of_mem hm he
  induction e using Sym2.ind with | _ a c => ?_
  obtain ⟨⟨b, hb, -⟩, ⟨d, hd, -⟩⟩ := IsTriangulation.existsUnique_apex_of_mem hm4 hT he
  have hq : IsFlipQuadrilateral T a b c d := ⟨hb.1, hd.1, hb.2.1, hb.2.2, hd.2.1, hd.2.2⟩
  obtain ⟨⟨n1, n2, n3, n4, n5, n6⟩, -⟩ := quadrilateral_cross hb.1 hd.1
  have heq : (univ.filter fun t : Finset (ZMod m) => IsTriangle T t ∧ s(a, c) ∈ t.sym2) =
      {{a, b, c}, {a, c, d}} := by
    ext t
    simp only [mem_filter, mem_univ, true_and, Finset.mk_mem_sym2_iff, mem_insert, mem_singleton]
    exact hq.isTriangle_iff hm4 hT he t
  rw [heq, card_pair]
  intro h
  have : b ∈ ({a, c, d} : Finset (ZMod m)) := h ▸ by simp
  simp only [mem_insert, mem_singleton] at this
  rcases this with h | h | h
  exacts [n1 h.symm, n4 h, n5 h]

/-- **The quadrilateral of a flip.** Let `γ` be an element of a triangulation `T` of the `m`-gon,
`m ≥ 3`. Then `γ = {a, c}` where `{a, b, c}` and `{a, c, d}` are the triangles of `T` containing
`γ`; the listings `(a, b, c)`, `(a, c, d)`, `(a, b, d)`, `(b, c, d)` are clockwise;
`T' = (T \ {γ}) ∪ {{b, d}}` is a triangulation whose triangles containing `{b, d}` are
`{a, b, d}` and `{b, c, d}`, and whose other triangles are those of `T` other than `{a, b, c}` and
`{a, c, d}`; and `{a, b}`, `{b, c}`, `{c, d}`, `{d, a}` are segments of `T` and of `T'`. -/
theorem IsTriangulation.exists_flip_quadrilateral (hm : 3 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) {γ : Sym2 (ZMod m)} (hγ : γ ∈ T) :
    ∃ a b c d : ZMod m, γ = s(a, c) ∧
      (∀ t, (IsTriangle T t ∧ γ ∈ t.sym2) ↔ t = {a, b, c} ∨ t = {a, c, d}) ∧
      sbtw a b c ∧ sbtw a c d ∧ sbtw a b d ∧ sbtw b c d ∧
      IsTriangulation (insert s(b, d) (T.erase γ)) ∧
      (∀ t, (IsTriangle (insert s(b, d) (T.erase γ)) t ∧ s(b, d) ∈ t.sym2) ↔
        t = {a, b, d} ∨ t = {b, c, d}) ∧
      (∀ t, (IsTriangle (insert s(b, d) (T.erase γ)) t ∧ t ≠ {a, b, d} ∧ t ≠ {b, c, d}) ↔
        (IsTriangle T t ∧ t ≠ {a, b, c} ∧ t ≠ {a, c, d})) ∧
      ∀ e ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 (ZMod m))),
        e ∈ segments T ∧ e ∈ segments (insert s(b, d) (T.erase γ)) := by
  have hm4 := hT.four_le_of_mem hm hγ
  induction γ using Sym2.ind with | _ a c => ?_
  obtain ⟨⟨b, hb, -⟩, ⟨d, hd, -⟩⟩ := IsTriangulation.existsUnique_apex_of_mem hm4 hT hγ
  have hq : IsFlipQuadrilateral T a b c d := ⟨hb.1, hd.1, hb.2.1, hb.2.2, hd.2.1, hd.2.2⟩
  obtain ⟨⟨n1, n2, n3, -, n5, -⟩, hac, hbd, -⟩ := quadrilateral_cross hb.1 hd.1
  obtain ⟨c1, c2, c3, c4⟩ := quadrilateral_isClockwise hb.1 hd.1
  obtain ⟨-, -, -, hbdT, hT'⟩ := hq.isFlipReplacement hT hγ
  obtain ⟨r1, r2, r3, r4⟩ := hq.rim_ne
  set T' := insert s(b, d) (T.erase s(a, c))
  have hT'' : IsTriangulation T' := hT'
  have hab' : s(a, b) ∈ segments T' := mem_segments_flipTriangulation hq.2.2.1 r1
  have hbc' : s(b, c) ∈ segments T' := mem_segments_flipTriangulation hq.2.2.2.1 r2
  have hcd' : s(c, d) ∈ segments T' := mem_segments_flipTriangulation hq.2.2.2.2.1 r3
  have hda' : s(d, a) ∈ segments T' := mem_segments_flipTriangulation hq.2.2.2.2.2 r4
  have hq' : IsFlipQuadrilateral T' b c d a := ⟨c4, sbtw_cyclic.1 c3, hbc', hcd', hda', hab'⟩
  have hbdT' : s(b, d) ∈ T' := mem_insert_self _ _
  have hTri : ∀ t, (IsTriangle T t ∧ s(a, c) ∈ t.sym2) ↔ t = {a, b, c} ∨ t = {a, c, d} :=
    fun t => (and_congr Iff.rfl mk_mem_sym2_iff).trans (hq.isTriangle_iff hm4 hT hγ t)
  have hTri' : ∀ t, (IsTriangle T' t ∧ s(b, d) ∈ t.sym2) ↔ t = {a, b, d} ∨ t = {b, c, d} := by
    intro t
    rw [Finset.mk_mem_sym2_iff, hq'.isTriangle_iff hm4 hT'' hbdT' t,
      show ({b, d, a} : Finset (ZMod m)) = {a, b, d} by
        ext; simp only [mem_insert, mem_singleton]; tauto, or_comm]
  have hacT' : s(a, c) ∉ segments T' :=
    notMem_segments_insert_erase hac (by simp [n1, n3])
  have hbdS : s(b, d) ∉ segments T := fun h => (mem_segments.1 h).elim hbdT hbd.2
  refine ⟨a, b, c, d, rfl, hTri, c1, c2, c3, c4, hT'', hTri', fun t => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨ht, h1, h2⟩
    have hnot : s(b, d) ∉ t.sym2 := fun h => by
      rcases (hTri' t).1 ⟨ht, h⟩ with h | h
      exacts [h1 h, h2 h]
    refine ⟨⟨ht.1, fun u hu v hv huv => mem_segments_of_mem_segments_insert_erase
      (ht.2 u hu v hv huv) fun h => hnot (h ▸ mk_mem_sym2_iff.2 ⟨hu, hv⟩)⟩, ?_, ?_⟩ <;>
      rintro rfl <;> exact hacT' (ht.2 a (by simp) c (by simp) n2)
  · rintro ⟨ht, h1, h2⟩
    have hnot : s(a, c) ∉ t.sym2 := fun h => by
      rcases (hTri t).1 ⟨ht, h⟩ with h | h
      exacts [h1 h, h2 h]
    refine ⟨⟨ht.1, fun u hu v hv huv => mem_segments_flipTriangulation (ht.2 u hu v hv huv)
      fun h => hnot (h ▸ mk_mem_sym2_iff.2 ⟨hu, hv⟩)⟩, ?_, ?_⟩ <;>
      rintro rfl <;> exact hbdS (ht.2 b (by simp) d (by simp) n5)
  · intro e he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    exacts [⟨hq.2.2.1, hab'⟩, ⟨hq.2.2.2.1, hbc'⟩, ⟨hq.2.2.2.2.1, hcd'⟩, ⟨hq.2.2.2.2.2, hda'⟩]

end Count

/-! ### Corner labellings and corner triangulations -/

namespace RotationSystem

variable {H : Type*} (R : RotationSystem H)

/-- A **corner labelling** of a set `w` of darts: a bijection `λ : ℤ/m → w` with
`λ(i + 1) = σ⁻¹(λ i)` for every `i`. -/
@[cluster_algebras "def_corner_triangulation"]
def IsCornerLabelling {m : ℕ} (w : Finset H) (l : ZMod m → H) : Prop :=
  Set.BijOn l Set.univ (w : Set H) ∧ ∀ i, l (i + 1) = R.rot.symm (l i)

/-- The **side** `{a, σ⁻¹ a}` of a dart `a`: the side of the polygon of corners crossed by `a`. -/
@[cluster_algebras "def_corner_triangulation"]
def cornerSide (a : H) : Sym2 H := s(a, R.rot.symm a)

/-- The **clockwise** listings: `(x, y, z)` is clockwise when `y` occurs before `z` in the
sequence `σ⁻¹ x, σ⁻² x, …`, that is, `y` occurs at a position `j ≥ 1` at or before which `z` does
not occur. -/
@[cluster_algebras "def_corner_triangulation"]
def IsCornerClockwise (x y z : H) : Prop :=
  ∃ j : ℕ, 0 < j ∧ (R.rot.symm ^ j) x = y ∧ ∀ i : ℕ, 0 < i → i ≤ j → (R.rot.symm ^ i) x ≠ z

section Decidable

variable [DecidableEq H]

/-- The **pull-back** `λ^* D = {{i, j} : {λ i, λ j} ∈ D}` of a set `D` of pairs of darts along a
map `λ : ℤ/m → H`. -/
@[cluster_algebras "def_corner_triangulation"]
def cornerPullback {m : ℕ} [NeZero m] (l : ZMod m → H) (D : Finset (Sym2 H)) :
    Finset (Sym2 (ZMod m)) :=
  univ.filter fun e => e.map l ∈ D

/-- A **corner triangulation** of a set `w` of darts: a set `D` of two-element subsets of `w`
such that, for some corner labelling `λ`, the pull-back `λ^* D` is a triangulation of the convex
`m`-gon. -/
@[cluster_algebras "def_corner_triangulation"]
def IsCornerTriangulation (w : Finset H) (D : Finset (Sym2 H)) : Prop :=
  (∀ e ∈ D, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ w) ∧
    ∃ (m : ℕ) (_ : NeZero m) (l : ZMod m → H),
      R.IsCornerLabelling w l ∧ IsTriangulation (cornerPullback l D)

/-- The **segments** of `D`: its elements and the sides of the darts of `w`. -/
@[cluster_algebras "def_corner_triangulation"]
def cornerSegments (w : Finset H) (D : Finset (Sym2 H)) : Finset (Sym2 H) :=
  D ∪ w.image R.cornerSide

/-- A **triangle** of `D`: a three-element subset of `w` all of whose two-element subsets are
segments of `D`. -/
@[cluster_algebras "def_corner_triangulation"]
def IsCornerTriangle (w : Finset H) (D : Finset (Sym2 H)) (t : Finset H) : Prop :=
  t ⊆ w ∧ t.card = 3 ∧ ∀ u ∈ t, ∀ v ∈ t, u ≠ v → s(u, v) ∈ R.cornerSegments w D

/-- Being a triangle of `D` is decidable: a subset, a cardinality and bounded quantifiers. -/
instance (w : Finset H) (D : Finset (Sym2 H)) : DecidablePred (R.IsCornerTriangle w D) :=
  fun _ => by unfold IsCornerTriangle; infer_instance

/-- The finite set of triangles of `D`. -/
def cornerTriangles (w : Finset H) (D : Finset (Sym2 H)) : Finset (Finset H) :=
  w.powerset.filter (R.IsCornerTriangle w D)

variable {R}

/-- Membership in `cornerTriangles`, unfolded. -/
@[simp]
theorem mem_cornerTriangles {w : Finset H} {D : Finset (Sym2 H)} {t : Finset H} :
    t ∈ R.cornerTriangles w D ↔ R.IsCornerTriangle w D t := by
  simp only [cornerTriangles, mem_filter, mem_powerset, and_iff_right_iff_imp]
  exact fun h => h.1

/-- A segment of `D` is an element of `D` or the side of a dart of `w`. -/
theorem mem_cornerSegments {w : Finset H} {D : Finset (Sym2 H)} {e : Sym2 H} :
    e ∈ R.cornerSegments w D ↔ e ∈ D ∨ ∃ a ∈ w, R.cornerSide a = e := by
  simp [cornerSegments]

/-- Membership in the pull-back, unfolded. -/
theorem mem_cornerPullback {m : ℕ} [NeZero m] {l : ZMod m → H} {D : Finset (Sym2 H)}
    {e : Sym2 (ZMod m)} : e ∈ cornerPullback l D ↔ e.map l ∈ D := by
  simp [cornerPullback]

end Decidable

variable {R}

/-! ### Transport along a corner labelling -/

namespace IsCornerLabelling

variable {m : ℕ} {w : Finset H} {l : ZMod m → H}

/-- A corner labelling is injective. -/
theorem injective (hl : R.IsCornerLabelling w l) : Function.Injective l :=
  fun _ _ h => hl.1.injOn trivial trivial h

/-- A corner labelling takes values in `w`. -/
theorem mem (hl : R.IsCornerLabelling w l) (i : ZMod m) : l i ∈ w :=
  Finset.mem_coe.1 (hl.1.mapsTo trivial)

/-- Every dart of `w` is the label of some corner. -/
theorem exists_eq (hl : R.IsCornerLabelling w l) {x : H} (hx : x ∈ w) : ∃ i, l i = x := by
  obtain ⟨i, -, h⟩ := hl.1.surjOn (Finset.mem_coe.2 hx)
  exact ⟨i, h⟩

/-- Every pair of darts of `w` is the image of a pair of corners. -/
theorem exists_map_eq (hl : R.IsCornerLabelling w l) {e : Sym2 H} (he : ∀ x ∈ e, x ∈ w) :
    ∃ e' : Sym2 (ZMod m), e'.map l = e := by
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨i, rfl⟩ := hl.exists_eq (he x (Sym2.mem_mk_left x y))
    obtain ⟨j, rfl⟩ := hl.exists_eq (he _ (Sym2.mem_mk_right _ y))
    exact ⟨s(i, j), rfl⟩

/-- `λ(i + n) = σ⁻ⁿ(λ i)`. -/
theorem apply_add_nat (hl : R.IsCornerLabelling w l) (i : ZMod m) (n : ℕ) :
    l (i + n) = (R.rot.symm ^ n) (l i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, ← add_assoc, hl.2, ih, pow_succ', Equiv.Perm.mul_apply]

/-- The side of the dart `λ i` is the image of the side `{i, i + 1}` of the `m`-gon. -/
theorem cornerSide_apply (hl : R.IsCornerLabelling w l) (i : ZMod m) :
    R.cornerSide (l i) = s(i, i + 1).map l := by
  rw [cornerSide, Sym2.map_mk, hl.2]

/-- A corner labelling of `w` is indexed by `ℤ/|w|`. -/
theorem card_eq [NeZero m] (hl : R.IsCornerLabelling w l) : w.card = m := by
  classical
  have hw : w = univ.image l := by
    ext x
    simp only [mem_image, mem_univ, true_and]
    exact ⟨hl.exists_eq, fun ⟨i, hi⟩ => hi ▸ hl.mem i⟩
  rw [hw, card_image_of_injective _ hl.injective, card_univ, ZMod.card]

/-- Two corner labellings of `w` differ by a rotation of `ℤ/m`. -/
theorem exists_add [NeZero m] (hl : R.IsCornerLabelling w l) {l₀ : ZMod m → H}
    (hl₀ : R.IsCornerLabelling w l₀) : ∃ s, ∀ i, l i = l₀ (i + s) := by
  obtain ⟨s, hs⟩ := hl₀.exists_eq (hl.mem 0)
  refine ⟨s, fun i => ?_⟩
  rw [← ZMod.natCast_zmod_val i]
  have h1 := hl.apply_add_nat 0 i.val
  rw [zero_add] at h1
  rw [h1, ← hs, ← hl₀.apply_add_nat s i.val, add_comm]

/-- **Transport of clockwise listings.** If `(i, j, k)` is clockwise in the `m`-gon, then
`(λ i, λ j, λ k)` is clockwise. -/
theorem isCornerClockwise [NeZero m] (hl : R.IsCornerLabelling w l) {i j k : ZMod m}
    (h : sbtw i j k) : R.IsCornerClockwise (l i) (l j) (l k) := by
  have h' := (sbtw_iff_sbtw_basePos i i j k).1 h
  rw [Int.sbtw_iff, basePos_self] at h'
  have hk := basePos_lt i k
  unfold basePos at h' hk
  have hjk : (j - i).val < (k - i).val := by omega
  refine ⟨(j - i).val, by omega, ?_, fun n hn hnj hn' => ?_⟩
  · rw [← hl.apply_add_nat, ZMod.natCast_zmod_val, add_sub_cancel]
  · rw [← hl.apply_add_nat] at hn'
    have hkn := congrArg (fun x => (x - i).val) (hl.injective hn')
    simp only [add_sub_cancel_left, ZMod.val_natCast] at hkn
    rw [Nat.mod_eq_of_lt (by omega)] at hkn
    omega

variable [DecidableEq H]

/-- **Transport of segments.** `λ` maps the segments of `λ^* D` onto the segments of `D`. -/
theorem map_mem_cornerSegments_iff [NeZero m] (hl : R.IsCornerLabelling w l)
    {D : Finset (Sym2 H)} (e : Sym2 (ZMod m)) :
    e.map l ∈ R.cornerSegments w D ↔ e ∈ segments (cornerPullback l D) := by
  rw [mem_cornerSegments, mem_segments, mem_cornerPullback]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨a, ha, he⟩
    obtain ⟨k, rfl⟩ := hl.exists_eq ha
    exact ⟨k, Sym2.map.injective hl.injective (by rw [← he, hl.cornerSide_apply])⟩
  · rintro ⟨k, rfl⟩
    exact ⟨l k, hl.mem k, hl.cornerSide_apply k⟩

/-- `λ` preserves containment of a pair in a set. -/
theorem map_mem_sym2_image_iff (hl : R.IsCornerLabelling w l) (e : Sym2 (ZMod m))
    (t : Finset (ZMod m)) : e.map l ∈ (t.image l).sym2 ↔ e ∈ t.sym2 := by
  induction e using Sym2.ind with
  | _ i j => simp [hl.injective.eq_iff]

/-- **Transport of triangles.** `λ` maps the triangles of `λ^* D` onto those of `D`. -/
theorem isCornerTriangle_image_iff [NeZero m] (hl : R.IsCornerLabelling w l)
    {D : Finset (Sym2 H)} (t : Finset (ZMod m)) :
    R.IsCornerTriangle w D (t.image l) ↔ IsTriangle (cornerPullback l D) t := by
  have hsub : t.image l ⊆ w := fun x hx => by
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    exact hl.mem i
  unfold IsCornerTriangle IsTriangle
  rw [card_image_of_injective _ hl.injective]
  simp only [hsub, true_and]
  refine and_congr Iff.rfl ⟨fun h i hi j hj hij => ?_, fun h u hu v hv huv => ?_⟩
  · rw [← hl.map_mem_cornerSegments_iff]
    exact h (l i) (mem_image_of_mem l hi) (l j) (mem_image_of_mem l hj) (hl.injective.ne hij)
  · obtain ⟨i, hi, rfl⟩ := mem_image.1 hu
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hv
    exact (hl.map_mem_cornerSegments_iff s(i, j)).2 (h i hi j hj fun e => huv (e ▸ rfl))

/-- Every triangle of `D` is the image of a set of corners. -/
theorem exists_image_eq [NeZero m] (hl : R.IsCornerLabelling w l) {D : Finset (Sym2 H)}
    {t : Finset H} (ht : R.IsCornerTriangle w D t) : ∃ t' : Finset (ZMod m), t'.image l = t := by
  refine ⟨univ.filter fun i => l i ∈ t, ?_⟩
  ext x
  simp only [mem_image, mem_filter, mem_univ, true_and]
  refine ⟨fun ⟨i, hi, hx⟩ => hx ▸ hi, fun hx => ?_⟩
  obtain ⟨i, rfl⟩ := hl.exists_eq (ht.1 hx)
  exact ⟨i, hx, rfl⟩

/-- **Transport of triangles.** The triangles of `D` are the images of the triangles of
`λ^* D`. -/
theorem isCornerTriangle_iff [NeZero m] (hl : R.IsCornerLabelling w l) {D : Finset (Sym2 H)}
    (t : Finset H) :
    R.IsCornerTriangle w D t ↔ ∃ t', IsTriangle (cornerPullback l D) t' ∧ t'.image l = t := by
  refine ⟨fun ht => ?_, fun ⟨t', ht', h⟩ => h ▸ (hl.isCornerTriangle_image_iff t').2 ht'⟩
  obtain ⟨t', rfl⟩ := hl.exists_image_eq ht
  exact ⟨t', (hl.isCornerTriangle_image_iff t').1 ht, rfl⟩

/-- The triangles of `D` containing the image of a pair `e` are the images of the triangles of
`λ^* D` containing `e`. -/
theorem filter_cornerTriangles_eq [NeZero m] (hl : R.IsCornerLabelling w l)
    {D : Finset (Sym2 H)} (e : Sym2 (ZMod m)) :
    (R.cornerTriangles w D).filter (fun t => e.map l ∈ t.sym2) =
      (univ.filter fun t => IsTriangle (cornerPullback l D) t ∧ e ∈ t.sym2).image
        (Finset.image l) := by
  ext t
  simp only [mem_filter, mem_cornerTriangles, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨ht, he⟩
    obtain ⟨t', rfl⟩ := hl.exists_image_eq ht
    exact ⟨t', ⟨(hl.isCornerTriangle_image_iff t').1 ht, (hl.map_mem_sym2_image_iff e t').1 he⟩,
      rfl⟩
  · rintro ⟨t', ⟨ht', he'⟩, rfl⟩
    exact ⟨(hl.isCornerTriangle_image_iff t').2 ht', (hl.map_mem_sym2_image_iff e t').2 he'⟩

/-- **Transport of the triangles containing a pair.** If the triangles of `λ^* D` containing `e`
are `A` and `B`, the triangles of `D` containing the image of `e` are the images of `A` and
`B`. -/
theorem isCornerTriangle_and_mem_iff [NeZero m] (hl : R.IsCornerLabelling w l)
    {D : Finset (Sym2 H)} {e : Sym2 (ZMod m)} {A B : Finset (ZMod m)}
    (h : ∀ t, (IsTriangle (cornerPullback l D) t ∧ e ∈ t.sym2) ↔ t = A ∨ t = B) (t : Finset H) :
    (R.IsCornerTriangle w D t ∧ e.map l ∈ t.sym2) ↔ t = A.image l ∨ t = B.image l := by
  constructor
  · rintro ⟨ht, he⟩
    obtain ⟨t', rfl⟩ := hl.exists_image_eq ht
    exact ((h t').1 ⟨(hl.isCornerTriangle_image_iff t').1 ht,
      (hl.map_mem_sym2_image_iff e t').1 he⟩).imp (congrArg (image l)) (congrArg (image l))
  · rintro (rfl | rfl) <;>
      exact ⟨(hl.isCornerTriangle_image_iff _).2 ((h _).2 (by simp)).1,
        (hl.map_mem_sym2_image_iff e _).2 ((h _).2 (by simp)).2⟩

end IsCornerLabelling

variable [DecidableEq H] {w : Finset H} {D : Finset (Sym2 H)}

/-- **Every corner labelling sees a triangulation.** If `D` is a corner triangulation of `w`, then
`λ^* D` is a triangulation of the convex `m`-gon for every corner labelling `λ` of `w`. -/
@[cluster_algebras "lem_corner_triangulation_any_labelling"]
theorem IsCornerTriangulation.isTriangulation_cornerPullback (hD : R.IsCornerTriangulation w D)
    {m : ℕ} [NeZero m] {l : ZMod m → H} (hl : R.IsCornerLabelling w l) :
    IsTriangulation (cornerPullback l D) := by
  obtain ⟨-, m₀, _, l₀, hl₀, hT₀⟩ := hD
  obtain rfl : m = m₀ := hl.card_eq.symm.trans hl₀.card_eq
  obtain ⟨s, hs⟩ := hl.exists_add hl₀
  have : cornerPullback l D = univ.filter fun e => e.map (· + s) ∈ cornerPullback l₀ D := by
    ext e
    simp only [mem_cornerPullback, mem_filter, mem_univ, true_and, Sym2.map_map]
    rw [show l = l₀ ∘ (· + s) from funext hs]
  rw [this]
  exact hT₀.filter_map_add s

/-- **A side lies in exactly one triangle.** If `D` is a corner triangulation of a set `w` of at
least three darts (for instance a crossing), the side of a dart of `w` lies in exactly one
triangle of `D`. -/
@[cluster_algebras "lem_corner_triangulation_triangles"]
theorem IsCornerTriangulation.card_filter_cornerSide (hD : R.IsCornerTriangulation w D)
    (hw : 3 ≤ w.card) {a : H} (ha : a ∈ w) :
    ((R.cornerTriangles w D).filter fun t => R.cornerSide a ∈ t.sym2).card = 1 := by
  obtain ⟨-, m, _, l, hl, hT⟩ := hD
  rw [hl.card_eq] at hw
  obtain ⟨k, rfl⟩ := hl.exists_eq ha
  rw [hl.cornerSide_apply, hl.filter_cornerTriangles_eq,
    card_image_of_injective _ (Finset.image_injective hl.injective)]
  exact hT.card_filter_side hw k

/-- **An element of `D` lies in exactly two triangles.** If `D` is a corner triangulation of a set
`w` of at least three darts (for instance a crossing), each element of `D` lies in exactly two
triangles of `D`. -/
@[cluster_algebras "lem_corner_triangulation_triangles"]
theorem IsCornerTriangulation.card_filter_mem (hD : R.IsCornerTriangulation w D)
    (hw : 3 ≤ w.card) {e : Sym2 H} (he : e ∈ D) :
    ((R.cornerTriangles w D).filter fun t => e ∈ t.sym2).card = 2 := by
  obtain ⟨hDw, m, _, l, hl, hT⟩ := hD
  rw [hl.card_eq] at hw
  obtain ⟨e', rfl⟩ := hl.exists_map_eq (hDw _ he).2
  rw [hl.filter_cornerTriangles_eq,
    card_image_of_injective _ (Finset.image_injective hl.injective)]
  exact hT.card_filter_mem hw (mem_cornerPullback.2 he)

/-- **A flip of a corner triangulation.** Let `D` be a corner triangulation of a set `w` of at
least three darts (for instance a crossing) and `s ∈ D`. Then there are darts `a, b, c, d` of `w`
with `s = {a, c}`, such that the triangles of `D` containing `s` are `{a, b, c}` and `{a, c, d}`;
the listings `(a, b, c)`, `(a, c, d)`, `(a, b, d)`, `(b, c, d)` are clockwise;
`D' = (D \ {s}) ∪ {{b, d}}` is a corner triangulation of `w`; the triangles of `D'` containing
`{b, d}` are `{a, b, d}` and `{b, c, d}`; the other triangles of `D'` are the triangles of `D`
other than `{a, b, c}` and `{a, c, d}`; and `{a, b}`, `{b, c}`, `{c, d}`, `{d, a}` are segments of
both `D` and `D'`. -/
@[cluster_algebras "lem_corner_triangulation_flip"]
theorem IsCornerTriangulation.exists_flip (hD : R.IsCornerTriangulation w D) (hw : 3 ≤ w.card)
    {s : Sym2 H} (hs : s ∈ D) :
    ∃ a ∈ w, ∃ b ∈ w, ∃ c ∈ w, ∃ d ∈ w, s = s(a, c) ∧
      (∀ t, (R.IsCornerTriangle w D t ∧ s ∈ t.sym2) ↔ t = {a, b, c} ∨ t = {a, c, d}) ∧
      R.IsCornerClockwise a b c ∧ R.IsCornerClockwise a c d ∧ R.IsCornerClockwise a b d ∧
      R.IsCornerClockwise b c d ∧
      R.IsCornerTriangulation w (insert s(b, d) (D.erase s)) ∧
      (∀ t, (R.IsCornerTriangle w (insert s(b, d) (D.erase s)) t ∧ s(b, d) ∈ t.sym2) ↔
        t = {a, b, d} ∨ t = {b, c, d}) ∧
      (∀ t, (R.IsCornerTriangle w (insert s(b, d) (D.erase s)) t ∧ t ≠ {a, b, d} ∧
          t ≠ {b, c, d}) ↔
        (R.IsCornerTriangle w D t ∧ t ≠ {a, b, c} ∧ t ≠ {a, c, d})) ∧
      ∀ e ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 H)),
        e ∈ R.cornerSegments w D ∧ e ∈ R.cornerSegments w (insert s(b, d) (D.erase s)) := by
  obtain ⟨hDw, m, _, l, hl, hT⟩ := hD
  rw [hl.card_eq] at hw
  obtain ⟨γ, rfl⟩ := hl.exists_map_eq (hDw _ hs).2
  obtain ⟨a, b, c, d, rfl, hTri, c1, c2, c3, c4, hT', hTri', hOther, hRim⟩ :=
    hT.exists_flip_quadrilateral hw (mem_cornerPullback.2 hs)
  have hinj := Sym2.map.injective hl.injective
  have hpull : cornerPullback l (insert s(l b, l d) (D.erase (s(a, c).map l))) =
      insert s(b, d) ((cornerPullback l D).erase s(a, c)) := by
    ext e
    simp only [mem_cornerPullback, mem_insert, mem_erase]
    rw [show s(l b, l d) = s(b, d).map l from rfl, hinj.eq_iff, hinj.ne_iff]
  rw [← hpull] at hT' hTri' hOther hRim
  have himg : ∀ x y z : ZMod m,
      ({l x, l y, l z} : Finset H) = ({x, y, z} : Finset (ZMod m)).image l :=
    fun x y z => by simp [Finset.image_insert]
  have hbd : b ≠ d := fun h => sbtw_irrefl_right (h ▸ c3)
  have hiff : ∀ x y : Finset (ZMod m), x.image l ≠ y.image l ↔ x ≠ y :=
    fun _ _ => (Finset.image_injective hl.injective).ne_iff
  refine ⟨l a, hl.mem a, l b, hl.mem b, l c, hl.mem c, l d, hl.mem d, rfl, ?_,
    hl.isCornerClockwise c1, hl.isCornerClockwise c2, hl.isCornerClockwise c3,
    hl.isCornerClockwise c4, ⟨?_, m, inferInstance, l, hl, hT'⟩, ?_, fun t => ⟨?_, ?_⟩, ?_⟩
  · intro t
    rw [himg, himg]
    exact hl.isCornerTriangle_and_mem_iff hTri t
  · intro e he
    rcases mem_insert.1 he with rfl | he
    · refine ⟨fun h => hbd (hl.injective (Sym2.mk_isDiag_iff.1 h)), fun x hx => ?_⟩
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      exacts [hl.mem b, hl.mem d]
    · exact hDw e (mem_of_mem_erase he)
  · intro t
    rw [himg, himg]
    exact hl.isCornerTriangle_and_mem_iff (e := s(b, d)) hTri' t
  · rintro ⟨ht, h1, h2⟩
    obtain ⟨t', rfl⟩ := hl.exists_image_eq ht
    rw [himg, hiff] at h1 h2
    obtain ⟨h3, h4, h5⟩ := (hOther t').1 ⟨(hl.isCornerTriangle_image_iff t').1 ht, h1, h2⟩
    refine ⟨(hl.isCornerTriangle_image_iff t').2 h3, ?_, ?_⟩ <;> rwa [himg, hiff]
  · rintro ⟨ht, h1, h2⟩
    obtain ⟨t', rfl⟩ := hl.exists_image_eq ht
    rw [himg, hiff] at h1 h2
    obtain ⟨h3, h4, h5⟩ := (hOther t').2 ⟨(hl.isCornerTriangle_image_iff t').1 ht, h1, h2⟩
    refine ⟨(hl.isCornerTriangle_image_iff t').2 h3, ?_, ?_⟩ <;> rwa [himg, hiff]
  · simpa only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
      ← hl.map_mem_cornerSegments_iff, Sym2.map_mk] using hRim

end RotationSystem

/-! ### Crossings -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-- A **crossing** of a plabic graph: a white internal vertex with at least three darts. -/
@[cluster_algebras "def_corner_triangulation"]
def IsCrossing (w : Finset H) : Prop :=
  w ∈ G.internalVertices ∧ (∀ d ∈ w, G.colour d = .white) ∧ 3 ≤ w.card

variable {G}

/-- A crossing has at least three darts. -/
theorem IsCrossing.three_le_card {w : Finset H} (h : G.IsCrossing w) : 3 ≤ w.card := h.2.2

end PlabicData

end ClusterAlgebras

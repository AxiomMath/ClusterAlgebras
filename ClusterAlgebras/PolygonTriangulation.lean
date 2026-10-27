/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Quiver

/-!
# Triangulations of a convex polygon, and the quiver of a triangulation

The vertices of a convex `m`-gon are labelled by `ZMod m` in clockwise order. No metric or
topological property of the polygon is used, so everything here is combinatorial.

## Main definitions

* `IsSegment`, `IsSide`, `IsDiagonal`: segments, sides and diagonals of the `m`-gon.
* `Cross`: two segments cross.
* `IsClockwise`: a clockwise listing of three vertices.
* `IsTriangulation`: a maximal set of pairwise non-crossing diagonals.
* `segments`: the diagonals of a triangulation together with the sides of the `m`-gon.
* `IsTriangle`: a triangle of a triangulation.
* `polygonArrows`: the arrow multiplicities of the quiver of a triangulation.
* `polygonQuiver`: the quiver of a triangulation.

## Main results

* `IsTriangle.eq_of_mem_sym2`: two distinct segments lie in at most one common triangle.
* `twoCycleFree_polygonArrows`: the quiver of a triangulation is two-cycle-free.

## Implementation notes

* Vertices are `ZMod m` with `[NeZero m]`, which makes `ZMod m` finite; `3 ≤ m` is not
  assumed, and for `m < 3` the notions are degenerate rather than ill-formed.
* "Clockwise" is strict circular betweenness `sbtw` for the cyclic order on `ZMod m`, and
  `IsClockwise` is a reducible abbreviation for it.
* A segment is an element of `Sym2 (ZMod m)` off the diagonal.
* The two arcs into which `{a, b}` cuts `ZMod m` are `Set.cIoo a b` and `Set.cIoo b a`, so
  `Cross` is stated with `sbtw` directly.
* `Cross` has no pairwise-distinctness clause: the two `sbtw` conditions already force the
  four endpoints to be pairwise distinct, see `Cross.pairwise_ne`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {m : ℕ} [NeZero m]

/-- Circular betweenness on `ZMod m` is decidable. -/
instance instDecidableSbtwZMod (a b c : ZMod m) : Decidable (sbtw a b c) := by
  match m, ‹NeZero m›, a, b, c with
  | (n + 1), _, a, b, c => exact decidable_of_iff _ Fin.sbtw_iff.symm

/-! ### Segments, sides and diagonals -/

/-- A **segment** of the convex `m`-gon: a two-element subset of `ZMod m`, presented as an
unordered pair of distinct vertices. -/
@[cluster_algebras "def_polygon_segment"]
def IsSegment (e : Sym2 (ZMod m)) : Prop := ¬e.IsDiag

/-- A segment is a **side** of the `m`-gon when its endpoints are cyclically consecutive,
that is, when it is `s(i, i + 1)` for some vertex `i`. -/
@[cluster_algebras "def_polygon_segment"]
def IsSide (e : Sym2 (ZMod m)) : Prop := ∃ i : ZMod m, e = s(i, i + 1)

/-- A segment is a **diagonal** when it is not a side. -/
@[cluster_algebras "def_polygon_segment"]
def IsDiagonal (e : Sym2 (ZMod m)) : Prop := IsSegment e ∧ ¬IsSide e

/-- Being a segment is decidable: it is the negation of `Sym2.IsDiag`. -/
instance instDecidablePredIsSegment : DecidablePred (IsSegment (m := m)) := fun _ => by
  unfold IsSegment; infer_instance

/-- Being a side is decidable: the witness `i` ranges over the finite type `ZMod m`. -/
instance instDecidablePredIsSide : DecidablePred (IsSide (m := m)) := fun _ => by
  unfold IsSide; infer_instance

/-- Being a diagonal is decidable. -/
instance instDecidablePredIsDiagonal : DecidablePred (IsDiagonal (m := m)) := fun _ => by
  unfold IsDiagonal; infer_instance

omit [NeZero m] in
/-- A diagonal is in particular a segment. -/
theorem IsDiagonal.isSegment {e : Sym2 (ZMod m)} (h : IsDiagonal e) : IsSegment e := h.1

/-! ### Crossing -/

/-- Two segments **cross** when, naming their endpoints suitably, each of the two arcs that
`{a, b}` cuts `ZMod m` into contains one endpoint of `{c, d}`: `sbtw a c b` and `sbtw b d a`. -/
@[cluster_algebras "def_diagonals_cross"]
def Cross (e f : Sym2 (ZMod m)) : Prop :=
  ∃ a b c d : ZMod m, e = s(a, b) ∧ f = s(c, d) ∧ sbtw a c b ∧ sbtw b d a

/-- Crossing is decidable. -/
instance instDecidableCross (e f : Sym2 (ZMod m)) : Decidable (Cross e f) := by
  unfold Cross; infer_instance

/-- Four points in cyclic position `a, c, b, d` are also in cyclic position `c, b, d, a`. -/
private theorem sbtw_rotate_four {n : ℕ} {a b c d : Fin n} (h1 : sbtw a c b) (h2 : sbtw b d a) :
    sbtw c b d ∧ sbtw d a c := by
  rw [Fin.sbtw_iff] at h1 h2
  refine ⟨?_, ?_⟩ <;> rw [Fin.sbtw_iff] <;>
    simp only [Fin.lt_def] at h1 h2 ⊢ <;> omega

/-- Crossing is symmetric: if `e` crosses `f` then `f` crosses `e`. -/
theorem Cross.symm {e f : Sym2 (ZMod m)} (h : Cross e f) : Cross f e := by
  obtain ⟨a, b, c, d, rfl, rfl, h1, h2⟩ := h
  refine ⟨c, d, b, a, rfl, Sym2.eq_swap, ?_⟩
  match m, ‹NeZero m›, a, b, c, d, h1, h2 with
  | (n + 1), _, a, b, c, d, h1, h2 => exact sbtw_rotate_four h1 h2

omit [NeZero m] in
/-- The endpoints of two crossing segments are pairwise distinct. -/
theorem Cross.pairwise_ne {e f : Sym2 (ZMod m)} (h : Cross e f) :
    ∃ a b c d : ZMod m, e = s(a, b) ∧ f = s(c, d) ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨a, b, c, d, rfl, rfl, h1, h2⟩ := h
  refine ⟨a, b, c, d, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun hc => sbtw_irrefl_left_right (hc ▸ h1)
  · exact fun hc => sbtw_irrefl_left (a := a) (b := b) (hc ▸ h1)
  · exact fun hc => sbtw_irrefl_right (a := b) (hc ▸ h2)
  · exact fun hc => sbtw_irrefl_right (a := a) (hc ▸ h1)
  · exact fun hc => sbtw_irrefl_left (a := b) (b := a) (hc ▸ h2)
  · exact fun hc => sbtw_asymm h1 (hc ▸ h2)

/-! ### Clockwise listings -/

/-- A listing `(a, b, c)` of a three-element subset of `ZMod m` is **clockwise** when,
starting at `a` and increasing the index by one at each step, one meets `b` strictly before
`c`, that is, `sbtw a b c` for the cyclic order on `ZMod m`. -/
@[cluster_algebras "def_clockwise_triple"]
abbrev IsClockwise (a b c : ZMod m) : Prop := sbtw a b c

omit [NeZero m] in
/-- A clockwise listing is unchanged by cyclic rotation. -/
theorem IsClockwise.rotate {a b c : ZMod m} (h : IsClockwise a b c) : IsClockwise b c a :=
  sbtw_cyclic.2 h

/-! ### Triangulations -/

/-- A **triangulation** of the convex `m`-gon: a set of pairwise non-crossing diagonals,
maximal with that property. Maximality says every diagonal outside `T` crosses some element
of `T`. -/
@[cluster_algebras "def_triangulation"]
structure IsTriangulation (T : Finset (Sym2 (ZMod m))) : Prop where
  /-- Every element of `T` is a diagonal. -/
  isDiagonal : ∀ e ∈ T, IsDiagonal e
  /-- No two elements of `T` cross. -/
  noncrossing : ∀ e ∈ T, ∀ f ∈ T, ¬Cross e f
  /-- `T` is maximal: any diagonal outside it crosses something in it. -/
  maximal : ∀ e, IsDiagonal e → e ∉ T → ∃ f ∈ T, Cross e f

/-- The **segments of `T`**: its diagonals together with all the sides of the `m`-gon. -/
@[cluster_algebras "def_segments_of_triangulation"]
def segments (T : Finset (Sym2 (ZMod m))) : Finset (Sym2 (ZMod m)) :=
  T ∪ Finset.univ.filter IsSide

/-- A segment of `T` is either one of its diagonals or a side of the `m`-gon. -/
@[simp]
theorem mem_segments {T : Finset (Sym2 (ZMod m))} {e : Sym2 (ZMod m)} :
    e ∈ segments T ↔ e ∈ T ∨ IsSide e := by
  simp [segments]

/-- A **triangle of `T`**: a three-element subset of `ZMod m` all three of whose pairs are
segments of `T`. -/
@[cluster_algebras "def_triangle_of_triangulation"]
def IsTriangle (T : Finset (Sym2 (ZMod m))) (t : Finset (ZMod m)) : Prop :=
  t.card = 3 ∧ ∀ u ∈ t, ∀ v ∈ t, u ≠ v → s(u, v) ∈ segments T

/-- Being a triangle of `T` is decidable: a cardinality and a bounded quantification. -/
instance instDecidablePredIsTriangle (T : Finset (Sym2 (ZMod m))) :
    DecidablePred (IsTriangle T) := fun _ => by unfold IsTriangle; infer_instance

/-- **Two distinct segments lie in at most one common triangle**: the triangle is the union of
the two segments. -/
@[cluster_algebras "lem_two_segments_one_triangle"]
theorem IsTriangle.eq_of_mem_sym2 {T : Finset (Sym2 (ZMod m))} {t t' : Finset (ZMod m)}
    {σ σ' : Sym2 (ZMod m)} (hσ : ¬σ.IsDiag) (hσ' : ¬σ'.IsDiag) (hne : σ ≠ σ')
    (ht : IsTriangle T t) (ht' : IsTriangle T t') (hσt : σ ∈ t.sym2) (hσ't : σ' ∈ t.sym2)
    (hσt' : σ ∈ t'.sym2) (hσ't' : σ' ∈ t'.sym2) : t = t' := by
  classical
  induction σ using Sym2.ind with | _ a b => ?_
  induction σ' using Sym2.ind with | _ c d => ?_
  rw [Finset.mk_mem_sym2_iff] at hσt hσ't hσt' hσ't'
  have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using hσ
  have hcd : c ≠ d := by simpa [Sym2.mk_isDiag_iff] using hσ'
  have hct : t.card = 3 := ht.1
  have hct' : t'.card = 3 := ht'.1
  set u : Finset (ZMod m) := {a, b, c, d} with hu
  have hut : u ⊆ t := by
    simp only [hu, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hσt.1, hσt.2, hσ't.1, hσ't.2⟩
  have hut' : u ⊆ t' := by
    simp only [hu, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hσt'.1, hσt'.2, hσ't'.1, hσ't'.2⟩
  have hle : u.card ≤ 3 := by
    have := Finset.card_le_card hut
    omega
  have hge : 3 ≤ u.card := by
    by_contra hlt
    have hp : ({a, b} : Finset (ZMod m)) ⊆ u := by
      simp only [hu, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨by simp, by simp⟩
    have hp' : ({c, d} : Finset (ZMod m)) ⊆ u := by
      simp only [hu, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨by simp, by simp⟩
    have e1 : ({a, b} : Finset (ZMod m)) = u :=
      Finset.eq_of_subset_of_card_le hp (by rw [Finset.card_pair hab]; omega)
    have e2 : ({c, d} : Finset (ZMod m)) = u :=
      Finset.eq_of_subset_of_card_le hp' (by rw [Finset.card_pair hcd]; omega)
    have hset : ({a, b} : Finset (ZMod m)) = {c, d} := e1.trans e2.symm
    refine hne ?_
    rw [Sym2.eq_iff]
    have ha : a ∈ ({c, d} : Finset (ZMod m)) := by rw [← hset]; simp
    have hb : b ∈ ({c, d} : Finset (ZMod m)) := by rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl
    · exact Or.inl ⟨rfl, hb.resolve_left (Ne.symm hab)⟩
    · exact Or.inr ⟨rfl, hb.resolve_right (Ne.symm hab)⟩
  rw [← Finset.eq_of_subset_of_card_le hut (by omega),
    ← Finset.eq_of_subset_of_card_le hut' (by omega)]

/-! ### The quiver of a triangulation -/

/-- The triangles of `T` that contribute an arrow from `σ` to `σ'`: those admitting a
clockwise listing `(a, b, c)` with `σ = s(a,b)` and `σ' = s(b,c)`. -/
def arrowTriangles (T : Finset (Sym2 (ZMod m))) (σ σ' : Sym2 (ZMod m)) :
    Finset (Finset (ZMod m)) :=
  {t ∈ Finset.univ | IsTriangle T t ∧
    ∃ a b c : ZMod m, IsClockwise a b c ∧ σ = s(a, b) ∧ σ' = s(b, c) ∧ a ∈ t ∧ b ∈ t ∧ c ∈ t}

/-- Membership in `arrowTriangles`, unfolded. -/
theorem mem_arrowTriangles {T : Finset (Sym2 (ZMod m))} {σ σ' : Sym2 (ZMod m)}
    {t : Finset (ZMod m)} :
    t ∈ arrowTriangles T σ σ' ↔ IsTriangle T t ∧
      ∃ a b c : ZMod m, IsClockwise a b c ∧ σ = s(a, b) ∧ σ' = s(b, c) ∧
        a ∈ t ∧ b ∈ t ∧ c ∈ t := by
  simp [arrowTriangles]

/-- The **arrow multiplicities of the quiver of `T`**: `a(σ, σ')` counts the triangles of `T`
carrying a clockwise listing that runs along `σ` and then along `σ'`, except that a pair of
sides carries no arrow. -/
@[cluster_algebras "def_polygon_quiver"]
def polygonArrows (T : Finset (Sym2 (ZMod m))) (σ σ' : Sym2 (ZMod m)) : ℕ :=
  if IsSide σ ∧ IsSide σ' then 0 else (arrowTriangles T σ σ').card

/-- **The quiver of a triangulation has no loops.** -/
@[cluster_algebras "lem_polygon_quiver_is_quiver"]
theorem polygonArrows_self (T : Finset (Sym2 (ZMod m))) (σ : Sym2 (ZMod m)) :
    polygonArrows T σ σ = 0 := by
  unfold polygonArrows
  split
  · rfl
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    obtain ⟨-, a, b, c, hcw, hσ, hσ', -⟩ := mem_arrowTriangles.1 ht
    rw [hσ, Sym2.eq_iff] at hσ'
    rcases hσ' with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
    · exact sbtw_irrefl_left hcw
    · exact sbtw_irrefl_left_right hcw

/-- **The quiver of a triangulation carries no arrow between two sides.** -/
@[cluster_algebras "lem_polygon_quiver_is_quiver"]
theorem polygonArrows_eq_zero_of_isSide (T : Finset (Sym2 (ZMod m))) {σ σ' : Sym2 (ZMod m)}
    (hσ : IsSide σ) (hσ' : IsSide σ') : polygonArrows T σ σ' = 0 := by
  unfold polygonArrows; exact if_pos ⟨hσ, hσ'⟩

/-- Away from pairs of sides, the arrow multiplicity of `T` counts `arrowTriangles`. -/
theorem polygonArrows_eq_card_arrowTriangles (T : Finset (Sym2 (ZMod m))) {σ σ' : Sym2 (ZMod m)}
    (h : ¬(IsSide σ ∧ IsSide σ')) : polygonArrows T σ σ' = (arrowTriangles T σ σ').card :=
  if_neg h

/-- **The quiver of a triangulation is two-cycle-free**: for any two segments `σ` and `σ'`,
there are no arrows from `σ` to `σ'` or none from `σ'` to `σ`. -/
@[cluster_algebras "lem_polygon_quiver_is_quiver"]
theorem twoCycleFree_polygonArrows (T : Finset (Sym2 (ZMod m))) :
    TwoCycleFree (polygonArrows T) := by
  intro σ σ'
  rcases eq_or_ne σ σ' with rfl | hne
  · exact Or.inl (polygonArrows_self T σ)
  by_cases hside : IsSide σ ∧ IsSide σ'
  · exact Or.inl (polygonArrows_eq_zero_of_isSide T hside.1 hside.2)
  by_contra hc
  rw [not_or] at hc
  obtain ⟨hz1, hz2⟩ := hc
  have e1 := polygonArrows_eq_card_arrowTriangles T hside
  have e2 := polygonArrows_eq_card_arrowTriangles T (σ := σ') (σ' := σ) fun h => hside ⟨h.2, h.1⟩
  obtain ⟨t, ht⟩ := Finset.card_pos.1 (by omega : 0 < (arrowTriangles T σ σ').card)
  obtain ⟨t', ht'⟩ := Finset.card_pos.1 (by omega : 0 < (arrowTriangles T σ' σ).card)
  obtain ⟨-, a, b, c, hcw, hσ, hσ', -⟩ := mem_arrowTriangles.1 ht
  obtain ⟨-, a', b', c', hcw', hτ, hτ', -⟩ := mem_arrowTriangles.1 ht'
  have hab : a ≠ b := by rintro rfl; exact sbtw_irrefl_left hcw
  have hbc : b ≠ c := by rintro rfl; exact sbtw_irrefl_right hcw
  have hac : a ≠ c := by rintro rfl; exact sbtw_irrefl_left_right hcw
  have e3 : (s(a, b) : Sym2 (ZMod m)) = s(b', c') := hσ.symm.trans hτ'
  have e4 : (s(b, c) : Sym2 (ZMod m)) = s(a', b') := hσ'.symm.trans hτ
  rcases Sym2.eq_iff.1 e3 with ⟨hA1, hA2⟩ | ⟨hB1, hB2⟩
  · rcases Sym2.eq_iff.1 e4 with ⟨-, hC2⟩ | ⟨hD1, -⟩
    · exact hac (hC2.trans hA1.symm).symm
    · exact hab (hD1.trans hA1.symm).symm
  · rcases Sym2.eq_iff.1 e4 with ⟨-, hC2⟩ | ⟨-, hD2⟩
    · exact hbc (hC2.trans hB2.symm).symm
    · subst hD2; subst hB2; subst hB1
      exact sbtw_asymm hcw hcw'

/-- The vertices of the quiver of `T`: the segments of `T`. -/
def SegmentType (T : Finset (Sym2 (ZMod m))) : Type := {e : Sym2 (ZMod m) // e ∈ segments T}

/-- Segments of `T` have decidable equality, inherited from `Sym2 (ZMod m)`. -/
instance instDecidableEqSegmentType (T : Finset (Sym2 (ZMod m))) : DecidableEq (SegmentType T) :=
  fun _ _ => decidable_of_iff _ Subtype.ext_iff.symm

/-- There are finitely many segments of `T`. -/
instance instFintypeSegmentType (T : Finset (Sym2 (ZMod m))) : Fintype (SegmentType T) :=
  Subtype.fintype _

/-- The **quiver of the triangulation `T`**: its vertices are the segments of `T`, its frozen
vertices the sides of the `m`-gon, and its arrows are `polygonArrows`. -/
@[cluster_algebras "def_polygon_quiver"]
def polygonQuiver (T : Finset (Sym2 (ZMod m))) : Quiver (SegmentType T) where
  frozen := {σ ∈ Finset.univ | IsSide σ.1}
  arrows σ σ' := polygonArrows T σ.1 σ'.1
  isArrowSystem σ := polygonArrows_self T σ.1
  twoCycleFree σ σ' := twoCycleFree_polygonArrows T σ.1 σ'.1
  frozen_eq_zero σ hσ σ' hσ' :=
    polygonArrows_eq_zero_of_isSide T (by simpa using hσ) (by simpa using hσ')

/-- The arrows of the quiver of `T` are `polygonArrows`. -/
@[simp]
theorem polygonQuiver_arrows (T : Finset (Sym2 (ZMod m))) (σ σ' : SegmentType T) :
    (polygonQuiver T).arrows σ σ' = polygonArrows T σ.1 σ'.1 := rfl

/-- The frozen vertices of the quiver of `T` are the sides of the `m`-gon. -/
@[simp]
theorem mem_frozen_polygonQuiver {T : Finset (Sym2 (ZMod m))} {σ : SegmentType T} :
    σ ∈ (polygonQuiver T).frozen ↔ IsSide σ.1 := by
  simp [polygonQuiver]

/-! ### Examples: the square and the hexagon -/

/-- The triangulation of the square by the diagonal `{0,2}`. -/
def squareTriangulation : Finset (Sym2 (ZMod 4)) := {s(0, 2)}

/-- The single diagonal `{0,2}` is a triangulation of the square: it is a diagonal, it crosses
nothing in the set, and the only other diagonal `{1,3}` crosses it. -/
theorem isTriangulation_squareTriangulation : IsTriangulation squareTriangulation where
  isDiagonal := by decide
  noncrossing := by decide
  maximal := by decide

/-- `{0,1,2}` and `{0,2,3}` are triangles of `squareTriangulation`, while `{0,1,3}` is not. -/
theorem isTriangle_squareTriangulation :
    IsTriangle squareTriangulation {0, 1, 2} ∧ IsTriangle squareTriangulation {0, 2, 3} ∧
      ¬IsTriangle squareTriangulation {0, 1, 3} := by decide

/-- **The quiver of the square triangulated by `{0,2}`**: there are arrows from `{1,2}` and
`{3,0}` to `{0,2}` and from `{0,2}` to `{0,1}` and `{2,3}`, there is no arrow from `{0,2}` to
`{1,2}`, and there is no arrow between the sides `{0,1}` and `{1,2}`. -/
theorem polygonArrows_squareTriangulation :
    polygonArrows squareTriangulation s(1, 2) s(0, 2) = 1 ∧
      polygonArrows squareTriangulation s(3, 0) s(0, 2) = 1 ∧
      polygonArrows squareTriangulation s(0, 2) s(0, 1) = 1 ∧
      polygonArrows squareTriangulation s(0, 2) s(2, 3) = 1 ∧
      polygonArrows squareTriangulation s(0, 2) s(1, 2) = 0 ∧
      polygonArrows squareTriangulation s(0, 1) s(1, 2) = 0 := by decide

/-- The fan of the hexagon from vertex `0`. -/
def hexagonFan : Finset (Sym2 (ZMod 6)) := {s(0, 2), s(0, 3), s(0, 4)}

/-- The fan is a triangulation of the hexagon. -/
theorem isTriangulation_hexagonFan : IsTriangulation hexagonFan where
  isDiagonal := by decide
  noncrossing := by decide
  maximal := by decide

/-- Not every diagonal outside the hexagon fan crosses every element of the fan: the
diagonal `{1,3}` does not cross `{0,4}`. -/
theorem not_forall_cross_hexagonFan :
    ¬∀ e : Sym2 (ZMod 6), IsDiagonal e → e ∉ hexagonFan → ∀ f ∈ hexagonFan, Cross e f :=
  fun h => absurd (h s(1, 3) (by decide) (by decide) s(0, 4) (by decide)) (by decide)

end ClusterAlgebras

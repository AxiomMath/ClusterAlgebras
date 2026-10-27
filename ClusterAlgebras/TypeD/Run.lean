/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.PolygonTriangulation
public import ClusterAlgebras.TypeA.Catalan
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card

/-!
# Triangulations of an integer run

Triangulations of convex polygons, on integer intervals rather than on a cyclic polygon, where
"between" is the order of `ℤ`. A *run* `[u, v]` of length `L = v - u` is the convex
`(L + 1)`-gon with vertices `u, …, v`; its triangulations are those of that polygon in the sense
of `IsTriangulation`. We prove that they are the maximal non-crossing sets of chords, split them
at the apex of the outer side, count their chords and the triangulations themselves, and describe
their flips.

## Main definitions

* `ClusterAlgebras.TypeD.IsRunChord`, `RunCross`: chords of a run and their crossing.
* `ClusterAlgebras.TypeD.IsRunTriangulation`: a triangulation of a run, through
  `IsTriangulation` of the `(L + 1)`-gon.
* `ClusterAlgebras.TypeD.IsRunSegment`, `IsRunTriangle`, `runTriangles`: segments and triangles.
* `ClusterAlgebras.TypeD.runGlue`, `IsRunFlip`, `runFan`: gluing, flips and the fan.

## Main statements

* `ClusterAlgebras.TypeD.isRunTriangulation_iff`: run triangulations are the maximal
  non-crossing sets of chords.
* `ClusterAlgebras.TypeD.IsRunTriangulation.existsUnique_apex`,
  `IsRunTriangulation.existsUnique_runGlue`, `IsRunTriangulation.card`,
  `IsRunTriangulation.existsUnique_parent`, `IsRunTriangulation.isRunFlip_right`,
  `IsRunTriangulation.isRunFlip_left`, `isRunTriangulation_runGlue`,
  `IsRunTriangulation.eq_runGlue_of_isRunTriangle`, `isRunTriangulation_runFan`,
  `encard_setOf_isRunTriangulation`.

## Implementation notes

* A chord is a pair `(x, y) : ℤ × ℤ`. The image of a chord in the `(L + 1)`-gon is
  `runPolygonSegment u v c`, an element of `Sym2 (ZMod (L + 1))` with `L = (v - u).toNat`.
* A triangle `(x, y, z)` is recorded by its three vertices; its *base* is `(x, z)`, its *apex*
  `y`, its *first short side* `(x, y)` and its *second short side* `(y, z)`. Statements about
  these names are phrased with `IsRunTriangle` directly.
* The definitions are total in `u, v`; for `v ≤ u` there are no chords and the only run
  triangulation is `∅`.
-/

@[expose] public section

namespace ClusterAlgebras.TypeD

/-! ### Chords and triangulations -/

/-- A **chord** of the run `[u, v]`: a pair `(x, y)` of integers with `u ≤ x < y ≤ v`,
`y - x ≥ 2` and `(x, y) ≠ (u, v)`. -/
@[cluster_algebras "def_run_triangulation"]
def IsRunChord (u v : ℤ) (c : ℤ × ℤ) : Prop :=
  u ≤ c.1 ∧ c.1 < c.2 ∧ c.2 ≤ v ∧ 2 ≤ c.2 - c.1 ∧ c ≠ (u, v)

/-- Being a chord is decidable. -/
instance instDecidablePredIsRunChord (u v : ℤ) : DecidablePred (IsRunChord u v) := fun _ => by
  unfold IsRunChord; infer_instance

/-- Two chords `(x, y)` and `(x', y')` **cross** if `x < x' < y < y'` or `x' < x < y' < y`. -/
@[cluster_algebras "def_run_triangulation"]
def RunCross (c c' : ℤ × ℤ) : Prop :=
  (c.1 < c'.1 ∧ c'.1 < c.2 ∧ c.2 < c'.2) ∨ (c'.1 < c.1 ∧ c.1 < c'.2 ∧ c'.2 < c.2)

/-- Crossing of chords is decidable. -/
instance instDecidableRunCross (c c' : ℤ × ℤ) : Decidable (RunCross c c') := by
  unfold RunCross; infer_instance

/-- The segment `{[x - u], [y - u]}` of the convex `(L + 1)`-gon, `L = v - u`, of a pair
`(x, y)`. -/
@[cluster_algebras "def_run_triangulation"]
def runPolygonSegment (u v : ℤ) (c : ℤ × ℤ) : Sym2 (ZMod ((v - u).toNat + 1)) :=
  s(((c.1 - u : ℤ) : ZMod ((v - u).toNat + 1)), ((c.2 - u : ℤ) : ZMod ((v - u).toNat + 1)))

/-- A **triangulation of the run** `[u, v]`: a set `T` of chords whose image in the convex
`(L + 1)`-gon, `L = v - u`, is a triangulation of that polygon when `L ≥ 2`. When `L < 2` the
run has no chords, so its only triangulation is `∅`. -/
@[cluster_algebras "def_run_triangulation"]
def IsRunTriangulation (u v : ℤ) (T : Finset (ℤ × ℤ)) : Prop :=
  (∀ c ∈ T, IsRunChord u v c) ∧ (2 ≤ v - u → IsTriangulation (T.image (runPolygonSegment u v)))

/-- A **segment** of a triangulation `T` of `[u, v]`: a chord in `T`, a side `(x, x + 1)` with
`u ≤ x < v`, or the outer side `(u, v)`. -/
@[cluster_algebras "def_run_triangulation"]
def IsRunSegment (u v : ℤ) (T : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : Prop :=
  c ∈ T ∨ (u ≤ c.1 ∧ c.2 = c.1 + 1 ∧ c.2 ≤ v) ∨ c = (u, v)

/-- Being a segment is decidable. -/
instance instDecidablePredIsRunSegment (u v : ℤ) (T : Finset (ℤ × ℤ)) :
    DecidablePred (IsRunSegment u v T) := fun _ => by
  unfold IsRunSegment; infer_instance

/-- A **triangle** `(x, y, z)` of `T`: integers `x < y < z` such that `(x, y)`, `(y, z)` and
`(x, z)` are segments of `T`. Its base is `(x, z)`, its apex `y`, its first short side `(x, y)`
and its second short side `(y, z)`. -/
@[cluster_algebras "def_run_triangulation"]
def IsRunTriangle (u v : ℤ) (T : Finset (ℤ × ℤ)) (x y z : ℤ) : Prop :=
  x < y ∧ y < z ∧ IsRunSegment u v T (x, y) ∧ IsRunSegment u v T (y, z) ∧
    IsRunSegment u v T (x, z)

/-- Being a triangle is decidable. -/
instance instDecidableIsRunTriangle (u v : ℤ) (T : Finset (ℤ × ℤ)) (x y z : ℤ) :
    Decidable (IsRunTriangle u v T x y z) := by
  unfold IsRunTriangle; infer_instance

/-- The integers `u, u + 1, …, v` as a finset, the image of `Finset.range` under `t ↦ u + t`; it
equals `Finset.Icc u v` (`intRange_eq_Icc`). -/
def intRange (u v : ℤ) : Finset ℤ :=
  (Finset.range (v + 1 - u).toNat).image fun t : ℕ => u + t

/-- Membership in `intRange u v`. -/
@[simp]
theorem mem_intRange {u v x : ℤ} : x ∈ intRange u v ↔ u ≤ x ∧ x ≤ v := by
  simp only [intRange, Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨t, ht, e⟩ => by omega, fun h => ⟨(x - u).toNat, by omega, by omega⟩⟩

/-- `intRange u v` is the interval `Finset.Icc u v`. -/
theorem intRange_eq_Icc (u v : ℤ) : intRange u v = Finset.Icc u v := by
  ext; simp

/-- The finite set of triangles `(x, y, z)` of `T` with vertices in `[u, v]`. -/
@[cluster_algebras "def_run_triangulation"]
def runTriangles (u v : ℤ) (T : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ × ℤ) :=
  (intRange u v ×ˢ intRange u v ×ˢ intRange u v).filter fun t =>
    IsRunTriangle u v T t.1 t.2.1 t.2.2

/-- Membership in `runTriangles u v T`. -/
@[simp]
theorem mem_runTriangles {u v : ℤ} {T : Finset (ℤ × ℤ)} {t : ℤ × ℤ × ℤ} :
    t ∈ runTriangles u v T ↔ (u ≤ t.1 ∧ t.1 ≤ v) ∧ (u ≤ t.2.1 ∧ t.2.1 ≤ v) ∧
      (u ≤ t.2.2 ∧ t.2.2 ≤ v) ∧ IsRunTriangle u v T t.1 t.2.1 t.2.2 := by
  simp only [runTriangles, Finset.mem_filter, Finset.mem_product, mem_intRange, and_assoc]

/-- The translate `(x + t, y + t)` of a pair. -/
def shiftPair (t : ℤ) (c : ℤ × ℤ) : ℤ × ℤ :=
  (c.1 + t, c.2 + t)

/-! ### Integers in `[0, n]` as vertices of the `(n + 1)`-gon -/

private theorem zmod_val_intCast_of_le {n : ℕ} {k : ℤ} (h0 : 0 ≤ k) (h1 : k ≤ n) :
    (((k : ZMod (n + 1)).val : ℕ) : ℤ) = k := by
  rw [ZMod.val_intCast]
  exact Int.emod_eq_of_lt h0 (by omega)

private theorem zmod_intCast_inj {n : ℕ} {a b : ℤ} (ha0 : 0 ≤ a) (ha1 : a ≤ n) (hb0 : 0 ≤ b)
    (hb1 : b ≤ n) : (a : ZMod (n + 1)) = b ↔ a = b :=
  ⟨fun h => by rw [← zmod_val_intCast_of_le ha0 ha1, ← zmod_val_intCast_of_le hb0 hb1, h],
    congrArg _⟩

private theorem zmod_sbtw_intCast_iff {n : ℕ} {a b c : ℤ} (ha0 : 0 ≤ a) (ha1 : a ≤ n)
    (hb0 : 0 ≤ b) (hb1 : b ≤ n) (hc0 : 0 ≤ c) (hc1 : c ≤ n) :
    sbtw (a : ZMod (n + 1)) b c ↔ (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) := by
  have key : ∀ x y z : ZMod (n + 1), sbtw x y z ↔ (x.val < y.val ∧ y.val < z.val) ∨
      (y.val < z.val ∧ z.val < x.val) ∨ (z.val < x.val ∧ x.val < y.val) := fun _ _ _ =>
    Fin.sbtw_iff
  have := zmod_val_intCast_of_le ha0 ha1
  have := zmod_val_intCast_of_le hb0 hb1
  have := zmod_val_intCast_of_le hc0 hc1
  rw [key]
  omega

private theorem zmod_eq_intCast_val {n : ℕ} (z : ZMod (n + 1)) :
    z = ((z.val : ℤ) : ZMod (n + 1)) ∧ 0 ≤ (z.val : ℤ) ∧ (z.val : ℤ) ≤ n :=
  ⟨by simp, by omega, by have := ZMod.val_lt z; omega⟩

private theorem zmod_intCast_add_one {n : ℕ} (k : ℤ) :
    ((k + 1 : ℤ) : ZMod (n + 1)) = (k : ZMod (n + 1)) + 1 := by
  push_cast; rfl

private theorem zmod_intCast_self_add_one {n : ℕ} :
    ((n : ℤ) : ZMod (n + 1)) + 1 = ((0 : ℤ) : ZMod (n + 1)) := by
  exact_mod_cast ZMod.natCast_self (n + 1)

private theorem zmod_exists_add_one {n : ℕ} (z : ZMod (n + 1)) :
    ∃ k j : ℤ, 0 ≤ k ∧ k ≤ n ∧ 0 ≤ j ∧ j ≤ n ∧ z = (k : ZMod (n + 1)) ∧
      z + 1 = (j : ZMod (n + 1)) ∧ (j = k + 1 ∨ (k = n ∧ j = 0)) := by
  obtain ⟨hz, h0, h1⟩ := zmod_eq_intCast_val z
  rcases lt_or_eq_of_le h1 with h | h
  · exact ⟨z.val, z.val + 1, h0, h1, by omega, by omega, hz,
      by rw [zmod_intCast_add_one, ← hz], Or.inl rfl⟩
  · refine ⟨z.val, 0, h0, h1, le_rfl, by omega, hz, ?_, Or.inr ⟨h, rfl⟩⟩
    rw [hz, h, zmod_intCast_self_add_one]

private theorem cross_mk_iff {m : ℕ} [NeZero m] {a b c d : ZMod m} :
    Cross s(a, b) s(c, d) ↔ (sbtw a c b ∧ sbtw b d a) ∨ (sbtw a d b ∧ sbtw b c a) := by
  refine ⟨fun ⟨a', b', c', d', h1, h2, h3, h4⟩ => ?_, ?_⟩
  · rw [Sym2.eq_iff] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
    exacts [⟨a, b, c, d, rfl, rfl, h3, h4⟩, ⟨a, b, d, c, rfl, Sym2.eq_swap, h3, h4⟩]

private theorem prod_ne_iff {c : ℤ × ℤ} {a b : ℤ} : c ≠ (a, b) ↔ c.1 ≠ a ∨ c.2 ≠ b := by
  simp only [ne_eq, Prod.ext_iff, not_and_or]

private theorem isRunChord_iff {u v : ℤ} {c : ℤ × ℤ} :
    IsRunChord u v c ↔ u ≤ c.1 ∧ c.1 < c.2 ∧ c.2 ≤ v ∧ 2 ≤ c.2 - c.1 ∧ (c.1 ≠ u ∨ c.2 ≠ v) := by
  rw [IsRunChord, prod_ne_iff]

/-- The integer content of a chord, with `c ≠ (u, v)` unfolded. -/
private theorem IsRunChord.bounds {u v : ℤ} {c : ℤ × ℤ} (hc : IsRunChord u v c) :
    u ≤ c.1 ∧ c.1 < c.2 ∧ c.2 ≤ v ∧ 2 ≤ c.2 - c.1 ∧ (c.1 ≠ u ∨ c.2 ≠ v) :=
  isRunChord_iff.1 hc

/-- A pair `p < q` in `[0, v - u]` whose image is not a side of the polygon gives a chord. -/
private theorem isRunChord_of_not_isSide {u v p q : ℤ} (huv : 2 ≤ v - u) (hp : 0 ≤ p)
    (hpq : p < q) (hq : q ≤ (v - u).toNat)
    (h : ¬IsSide s(((p : ℤ) : ZMod ((v - u).toNat + 1)), ((q : ℤ) : ZMod ((v - u).toNat + 1)))) :
    IsRunChord u v (u + p, u + q) := by
  rw [isRunChord_iff]
  dsimp only
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · by_contra h'
    exact h ⟨(p : ZMod _), by rw [show q = p + 1 by omega, zmod_intCast_add_one]⟩
  · by_contra h'
    push Not at h'
    refine h ⟨((v - u).toNat : ℤ), ?_⟩
    rw [zmod_intCast_self_add_one, show p = 0 by omega, show q = ((v - u).toNat : ℤ) by omega]
    exact Sym2.eq_swap

/-! ### Chords of a run are the diagonals of a polygon -/

/-- **Chords of a run are the diagonals of a polygon**: for `L = v - u ≥ 2`, the map
`(x, y) ↦ {[x - u], [y - u]}` is a bijection from the chords of `[u, v]` onto the diagonals of
the convex `(L + 1)`-gon. -/
@[cluster_algebras "lem_run_chords"]
theorem bijOn_runPolygonSegment {u v : ℤ} (huv : 2 ≤ v - u) :
    Set.BijOn (runPolygonSegment u v) {c | IsRunChord u v c} {e | IsDiagonal e} := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := IsRunChord.bounds hc
    refine ⟨?_, ?_⟩
    · change ¬(s(_, _) : Sym2 _).IsDiag
      rw [Sym2.mk_isDiag_iff, zmod_intCast_inj] <;> omega
    · rintro ⟨i, hi⟩
      obtain ⟨k, j, hk0, hk1, hj0, hj1, rfl, hj, hkj⟩ := zmod_exists_add_one i
      rw [hj] at hi
      unfold runPolygonSegment at hi
      rw [Sym2.eq_iff, zmod_intCast_inj, zmod_intCast_inj, zmod_intCast_inj,
        zmod_intCast_inj] at hi <;> omega
  · intro c hc c' hc' h
    obtain ⟨h1, h2, h3, h4, h5⟩ := IsRunChord.bounds hc
    obtain ⟨h1', h2', h3', h4', h5'⟩ := IsRunChord.bounds hc'
    refine Prod.ext_iff.2 ?_
    unfold runPolygonSegment at h
    rw [Sym2.eq_iff, zmod_intCast_inj, zmod_intCast_inj, zmod_intCast_inj,
      zmod_intCast_inj] at h <;> omega
  · intro e he
    induction e using Sym2.ind with | _ a b => ?_
    obtain ⟨ha, ha0, ha1⟩ := zmod_eq_intCast_val a
    obtain ⟨hb, hb0, hb1⟩ := zmod_eq_intCast_val b
    have he' : IsDiagonal s(a, b) := he
    rw [ha, hb] at he'
    have hne : (a.val : ℤ) ≠ b.val := by
      intro h
      apply he'.1
      rw [Sym2.mk_isDiag_iff, h]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine ⟨_, isRunChord_of_not_isSide huv ha0 hlt hb1 he'.2, ?_⟩
      unfold runPolygonSegment
      simp only [add_sub_cancel_left]
      rw [← ha, ← hb]
    · rw [Sym2.eq_swap] at he'
      refine ⟨_, isRunChord_of_not_isSide huv hb0 hlt ha1 he'.2, ?_⟩
      unfold runPolygonSegment
      simp only [add_sub_cancel_left]
      rw [← ha, ← hb, Sym2.eq_swap]

/-- **Chords of a run are the diagonals of a polygon**: two chords cross if and only if their
images cross. -/
@[cluster_algebras "lem_run_chords"]
theorem cross_runPolygonSegment_iff {u v : ℤ} {c c' : ℤ × ℤ} (hc : IsRunChord u v c)
    (hc' : IsRunChord u v c') :
    Cross (runPolygonSegment u v c) (runPolygonSegment u v c') ↔ RunCross c c' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := IsRunChord.bounds hc
  obtain ⟨h1', h2', h3', h4', h5'⟩ := IsRunChord.bounds hc'
  unfold runPolygonSegment RunCross
  rw [cross_mk_iff, zmod_sbtw_intCast_iff, zmod_sbtw_intCast_iff, zmod_sbtw_intCast_iff,
    zmod_sbtw_intCast_iff] <;> omega

/-- **Chords of a run are the diagonals of a polygon**: a set of chords is a triangulation of the
run if and only if its elements pairwise do not cross and every chord not in it crosses one of
its elements. -/
@[cluster_algebras "lem_run_chords"]
theorem isRunTriangulation_iff {u v : ℤ} {T : Finset (ℤ × ℤ)} :
    IsRunTriangulation u v T ↔
      (∀ c ∈ T, IsRunChord u v c) ∧ (∀ c ∈ T, ∀ c' ∈ T, ¬RunCross c c') ∧
        ∀ c, IsRunChord u v c → c ∉ T → ∃ c' ∈ T, RunCross c c' := by
  refine ⟨fun ⟨hch, htri⟩ => ⟨hch, ?_, ?_⟩,
    fun ⟨hch, hnc, hmax⟩ => ⟨hch, fun huv => ⟨?_, ?_, ?_⟩⟩⟩
  · intro c hc c' hc' hcr
    have huv : 2 ≤ v - u := by have := (hch c hc).bounds; omega
    exact (htri huv).noncrossing _ (Finset.mem_image_of_mem _ hc) _
      (Finset.mem_image_of_mem _ hc')
      ((cross_runPolygonSegment_iff (hch c hc) (hch c' hc')).2 hcr)
  · intro c hc hcT
    have huv : 2 ≤ v - u := by have := hc.bounds; omega
    have hb := bijOn_runPolygonSegment huv
    have hnot : runPolygonSegment u v c ∉ T.image (runPolygonSegment u v) := by
      rw [Finset.mem_image]
      rintro ⟨d, hd, hdc⟩
      exact hcT (hb.injOn (hch d hd) hc hdc ▸ hd)
    obtain ⟨e, he, hce⟩ := (htri huv).maximal _ (hb.mapsTo hc) hnot
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 he
    exact ⟨d, hd, (cross_runPolygonSegment_iff hc (hch d hd)).1 hce⟩
  · intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 he
    exact (bijOn_runPolygonSegment huv).mapsTo (hch d hd)
  · intro e he f hf
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.1 hf
    exact (cross_runPolygonSegment_iff (hch d hd) (hch d' hd')).not.2 (hnc d hd d' hd')
  · intro e he heT
    obtain ⟨c, hc, rfl⟩ := (bijOn_runPolygonSegment huv).surjOn he
    have hcT : c ∉ T := fun h => heT (Finset.mem_image_of_mem _ h)
    obtain ⟨c', hc', hcr⟩ := hmax c hc hcT
    exact ⟨_, Finset.mem_image_of_mem _ hc', (cross_runPolygonSegment_iff hc (hch c' hc')).2 hcr⟩

/-- **Chords of a run are the diagonals of a polygon**: translation by `t` maps the chords of
`[u, v]` to those of `[u + t, v + t]`. -/
@[cluster_algebras "lem_run_chords"]
theorem isRunChord_shiftPair_iff {u v t : ℤ} {c : ℤ × ℤ} :
    IsRunChord (u + t) (v + t) (shiftPair t c) ↔ IsRunChord u v c := by
  simp only [isRunChord_iff, shiftPair]
  omega

/-- **Chords of a run are the diagonals of a polygon**: translation preserves crossing. -/
@[cluster_algebras "lem_run_chords"]
theorem runCross_shiftPair_iff {t : ℤ} {c c' : ℤ × ℤ} :
    RunCross (shiftPair t c) (shiftPair t c') ↔ RunCross c c' := by
  simp only [RunCross, shiftPair]
  omega

/-- Translation maps triangulations of `[u, v]` to triangulations of `[u + t, v + t]`. -/
private theorem isRunTriangulation_image_shiftPair {u v t : ℤ} {T : Finset (ℤ × ℤ)}
    (h : IsRunTriangulation u v T) :
    IsRunTriangulation (u + t) (v + t) (T.image (shiftPair t)) := by
  obtain ⟨hch, hnc, hmax⟩ := isRunTriangulation_iff.1 h
  refine isRunTriangulation_iff.2 ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
    exact isRunChord_shiftPair_iff.2 (hch d hd)
  · intro c hc c' hc'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.1 hc'
    exact runCross_shiftPair_iff.not.2 (hnc _ hd _ hd')
  · intro c hc hcT
    have hc0 : shiftPair t (shiftPair (-t) c) = c := by simp [shiftPair]
    have hd : IsRunChord u v (shiftPair (-t) c) := by
      rwa [← isRunChord_shiftPair_iff (t := t), hc0]
    have hdT : shiftPair (-t) c ∉ T := fun h' => hcT (hc0 ▸ Finset.mem_image_of_mem _ h')
    obtain ⟨d', hd', hcr⟩ := hmax _ hd hdT
    refine ⟨_, Finset.mem_image_of_mem _ hd', ?_⟩
    rwa [← hc0, runCross_shiftPair_iff]

/-- Translation of pairs is injective. -/
theorem shiftPair_injective (t : ℤ) : Function.Injective (shiftPair t) := fun a b h => by
  simp only [shiftPair, Prod.mk.injEq] at h
  exact Prod.ext (by omega) (by omega)

/-- **Chords of a run are the diagonals of a polygon**: translation maps the triangulations of
`[u, v]` to those of `[u + t, v + t]`. -/
@[cluster_algebras "lem_run_chords"]
theorem isRunTriangulation_image_shiftPair_iff {u v t : ℤ} {T : Finset (ℤ × ℤ)} :
    IsRunTriangulation (u + t) (v + t) (T.image (shiftPair t)) ↔ IsRunTriangulation u v T := by
  refine ⟨fun h => ?_, isRunTriangulation_image_shiftPair⟩
  have e : (T.image (shiftPair t)).image (shiftPair (-t)) = T := by
    rw [Finset.image_image]
    convert Finset.image_id (s := T)
    ext c <;> simp [shiftPair]
  have := isRunTriangulation_image_shiftPair (t := -t) h
  rwa [e, add_neg_cancel_right, add_neg_cancel_right] at this

/-- **Chords of a run are the diagonals of a polygon**: translation maps the segments of a set of
chords of `[u, v]` to those of its translate. -/
@[cluster_algebras "lem_run_chords"]
theorem isRunSegment_shiftPair_iff {u v t : ℤ} {T : Finset (ℤ × ℤ)} {c : ℤ × ℤ} :
    IsRunSegment (u + t) (v + t) (T.image (shiftPair t)) (shiftPair t c) ↔
      IsRunSegment u v T c := by
  unfold IsRunSegment
  rw [(shiftPair_injective t).mem_finset_image]
  refine or_congr Iff.rfl (or_congr ?_ ?_) <;> simp only [shiftPair, Prod.mk.injEq] <;>
    constructor <;> intro h
  all_goals first
    | omega
    | exact Prod.ext (by omega) (by omega)
    | (subst h; dsimp only; omega)

/-- **Chords of a run are the diagonals of a polygon**: translation maps the triangles of a set
of chords of `[u, v]` to those of its translate. -/
@[cluster_algebras "lem_run_chords"]
theorem isRunTriangle_shiftPair_iff {u v t : ℤ} {T : Finset (ℤ × ℤ)} {x y z : ℤ} :
    IsRunTriangle (u + t) (v + t) (T.image (shiftPair t)) (x + t) (y + t) (z + t) ↔
      IsRunTriangle u v T x y z := by
  unfold IsRunTriangle
  have h1 := isRunSegment_shiftPair_iff (u := u) (v := v) (t := t) (T := T) (c := (x, y))
  have h2 := isRunSegment_shiftPair_iff (u := u) (v := v) (t := t) (T := T) (c := (y, z))
  have h3 := isRunSegment_shiftPair_iff (u := u) (v := v) (t := t) (T := T) (c := (x, z))
  simp only [shiftPair] at h1 h2 h3
  rw [h1, h2, h3]
  constructor <;> rintro ⟨a, b, c, d, e⟩ <;> exact ⟨by omega, by omega, c, d, e⟩

variable {u v : ℤ} {T : Finset (ℤ × ℤ)}

/-! ### The integer model of a run triangulation -/

private theorem mem_ite_singleton {p : Prop} [Decidable p] {a c : ℤ × ℤ} :
    c ∈ (if p then ({a} : Finset (ℤ × ℤ)) else ∅) ↔ p ∧ c = a := by
  split_ifs with h <;> simp [h]

private theorem IsRunTriangulation.chord (hT : IsRunTriangulation u v T) {c : ℤ × ℤ}
    (hc : c ∈ T) : IsRunChord u v c :=
  (isRunTriangulation_iff.1 hT).1 c hc

private theorem IsRunTriangulation.not_runCross (hT : IsRunTriangulation u v T) {c c' : ℤ × ℤ}
    (hc : c ∈ T) (hc' : c' ∈ T) : ¬RunCross c c' :=
  (isRunTriangulation_iff.1 hT).2.1 c hc c' hc'

private theorem IsRunTriangulation.exists_runCross (hT : IsRunTriangulation u v T) {c : ℤ × ℤ}
    (hc : IsRunChord u v c) (hcT : c ∉ T) : ∃ c' ∈ T, RunCross c c' :=
  (isRunTriangulation_iff.1 hT).2.2 c hc hcT

private theorem IsRunTriangulation.segment_bounds (hT : IsRunTriangulation u v T) {c : ℤ × ℤ}
    (hc : IsRunSegment u v T c) : u ≤ c.1 ∧ c.2 ≤ v := by
  rcases hc with hc | ⟨h1, h2, h3⟩ | rfl
  · have := (hT.chord hc).bounds; omega
  all_goals omega

/-- Two segments of a run triangulation never cross. -/
private theorem IsRunTriangulation.not_runCross_of_isRunSegment (hT : IsRunTriangulation u v T)
    {s s' : ℤ × ℤ} (hs : IsRunSegment u v T s) (hs' : IsRunSegment u v T s') :
    ¬RunCross s s' := by
  have b := hT.segment_bounds hs
  have b' := hT.segment_bounds hs'
  rcases hs with hs | ⟨h1, h2, h3⟩ | rfl <;> rcases hs' with hs' | ⟨h1', h2', h3'⟩ | rfl <;>
    first
    | exact hT.not_runCross hs hs'
    | (unfold RunCross; omega)

/-- A segment which is a chord is in the triangulation. -/
private theorem mem_of_isRunSegment {s : ℤ × ℤ} (hs : IsRunSegment u v T s)
    (hlen : 2 ≤ s.2 - s.1) (hne : s ≠ (u, v)) : s ∈ T := by
  rcases hs with hs | ⟨h1, h2, h3⟩ | hs
  exacts [hs, by omega, absurd hs hne]

/-- A segment crossed by a pair with endpoints in `[u, v]` is in the triangulation. -/
private theorem mem_of_runCross {s f : ℤ × ℤ} (hs : IsRunSegment u v T s) (hf1 : u ≤ f.1)
    (hf2 : f.2 ≤ v) (h : RunCross f s) : s ∈ T := by
  rcases hs with hs | ⟨h1, h2, h3⟩ | rfl
  · exact hs
  all_goals (unfold RunCross at h; omega)

/-! ### Apex, splitting and size -/

private theorem IsRunTriangulation.apex_unique (hT : IsRunTriangulation u v T) {x y y' z : ℤ}
    (h : IsRunTriangle u v T x y z) (h' : IsRunTriangle u v T x y' z) : y = y' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨h1', h2', h3', h4', h5'⟩ := h'
  have a := hT.not_runCross_of_isRunSegment h3' h4
  have b := hT.not_runCross_of_isRunSegment h3 h4'
  unfold RunCross at a b
  omega

/-- Every segment of length at least two is the base of a triangle. -/
private theorem IsRunTriangulation.exists_apex (hT : IsRunTriangulation u v T) {x z : ℤ}
    (hb : IsRunSegment u v T (x, z)) (hlen : 2 ≤ z - x) : ∃ y, IsRunTriangle u v T x y z := by
  classical
  have bxz := hT.segment_bounds hb
  set S := (Finset.Ioo x z).filter (fun y => IsRunSegment u v T (x, y))
  have hS : S.Nonempty := ⟨x + 1, Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨by omega, by omega⟩,
    Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)⟩⟩
  have hyS := S.max'_mem hS
  rw [Finset.mem_filter, Finset.mem_Ioo] at hyS
  obtain ⟨⟨hxy, hyz⟩, hxyseg⟩ := hyS
  refine ⟨S.max' hS, hxy, hyz, hxyseg, ?_, hb⟩
  by_cases hz : z = S.max' hS + 1
  · exact Or.inr (Or.inl ⟨by omega, hz, by omega⟩)
  · left
    by_contra hnot
    have hch : IsRunChord u v (S.max' hS, z) :=
      isRunChord_iff.2 ⟨by omega, by omega, by omega, by omega, Or.inl (by omega)⟩
    obtain ⟨e, heT, hcr⟩ := hT.exists_runCross hch hnot
    have ns1 := hT.not_runCross_of_isRunSegment hb (Or.inl heT)
    have ns2 := hT.not_runCross_of_isRunSegment hxyseg (Or.inl heT)
    have eb := (hT.chord heT).bounds
    by_cases he1 : e.1 = x
    · have hmem : e.2 ∈ S := by
        unfold RunCross at hcr
        rw [Finset.mem_filter, Finset.mem_Ioo]
        exact ⟨⟨by omega, by omega⟩, Or.inl (by rwa [show (x, e.2) = e from Prod.ext he1.symm rfl])⟩
      have := S.le_max' _ hmem
      unfold RunCross at hcr
      omega
    · unfold RunCross at hcr ns1 ns2
      omega

/-- **Every chord and the outer side have a unique apex**: if `T` is a triangulation of `[u, v]`,
`v - u ≥ 2`, and `(x, z)` is a chord in `T` or the outer side, there is exactly one `y` such
that `(x, y, z)` is a triangle of `T`. -/
@[cluster_algebras "lem_run_apex"]
theorem IsRunTriangulation.existsUnique_apex (hT : IsRunTriangulation u v T) (huv : 2 ≤ v - u)
    {x z : ℤ} (hxz : (x, z) ∈ T ∨ (x, z) = (u, v)) : ∃! y, IsRunTriangle u v T x y z := by
  have hb : IsRunSegment u v T (x, z) := hxz.imp_right Or.inr
  have hlen : 2 ≤ z - x := by
    rcases hxz with h | h
    · have := (hT.chord h).bounds; omega
    · simp only [Prod.mk.injEq] at h; omega
  obtain ⟨y, hy⟩ := hT.exists_apex hb hlen
  exact ⟨y, hy, fun y' hy' => (hT.apex_unique hy hy').symm⟩

/-- The set `T₁ ∪ T₂ ∪ {(u, w) : w - u ≥ 2} ∪ {(w, v) : v - w ≥ 2}` obtained by gluing
triangulations of `[u, w]` and `[w, v]`. -/
@[cluster_algebras "lem_run_split"]
def runGlue (u w v : ℤ) (T₁ T₂ : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  T₁ ∪ T₂ ∪ (if 2 ≤ w - u then {(u, w)} else ∅) ∪ (if 2 ≤ v - w then {(w, v)} else ∅)

private theorem mem_runGlue {w : ℤ} {T₁ T₂ : Finset (ℤ × ℤ)} {c : ℤ × ℤ} :
    c ∈ runGlue u w v T₁ T₂ ↔
      c ∈ T₁ ∨ c ∈ T₂ ∨ (2 ≤ w - u ∧ c = (u, w)) ∨ (2 ≤ v - w ∧ c = (w, v)) := by
  simp only [runGlue, Finset.mem_union, mem_ite_singleton, or_assoc]

private theorem card_runGlue {w : ℤ} {T₁ T₂ : Finset (ℤ × ℤ)} (h₁ : IsRunTriangulation u w T₁)
    (h₂ : IsRunTriangulation w v T₂) (huw : u < w) (hwv : w < v) :
    (runGlue u w v T₁ T₂).card = T₁.card + T₂.card + (if 2 ≤ w - u then 1 else 0) +
      (if 2 ≤ v - w then 1 else 0) := by
  have b₁ : ∀ c ∈ T₁, u ≤ c.1 ∧ c.1 < c.2 ∧ c.2 ≤ w ∧ (c.1 ≠ u ∨ c.2 ≠ w) := fun c hc => by
    have := (h₁.chord hc).bounds; omega
  have b₂ : ∀ c ∈ T₂, w ≤ c.1 ∧ c.1 < c.2 ∧ c.2 ≤ v ∧ (c.1 ≠ w ∨ c.2 ≠ v) := fun c hc => by
    have := (h₂.chord hc).bounds; omega
  have d1 : Disjoint T₁ T₂ := Finset.disjoint_left.2 fun c hc hc' => by
    have := b₁ c hc; have := b₂ c hc'; omega
  have d2 : Disjoint (T₁ ∪ T₂) (if 2 ≤ w - u then {(u, w)} else ∅) :=
    Finset.disjoint_left.2 fun c hc hc' => by
      obtain ⟨-, rfl⟩ := mem_ite_singleton.1 hc'
      rcases Finset.mem_union.1 hc with hc | hc
      · have := b₁ _ hc; omega
      · have := b₂ _ hc; omega
  have d3 : Disjoint (T₁ ∪ T₂ ∪ (if 2 ≤ w - u then {(u, w)} else ∅))
      (if 2 ≤ v - w then {(w, v)} else ∅) :=
    Finset.disjoint_left.2 fun c hc hc' => by
      obtain ⟨-, rfl⟩ := mem_ite_singleton.1 hc'
      rcases Finset.mem_union.1 hc with hc | hc
      · rcases Finset.mem_union.1 hc with hc | hc
        · have := b₁ _ hc; omega
        · have := b₂ _ hc; omega
      · obtain ⟨-, hc⟩ := mem_ite_singleton.1 hc
        simp only [Prod.mk.injEq] at hc
        omega
  unfold runGlue
  rw [Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2,
    Finset.card_union_of_disjoint d1]
  split_ifs <;> simp

private theorem runGlue_filter_left {w : ℤ} {T₁ T₂ : Finset (ℤ × ℤ)}
    (h₁ : IsRunTriangulation u w T₁) (h₂ : IsRunTriangulation w v T₂) :
    (runGlue u w v T₁ T₂).filter (fun c => c.2 ≤ w ∧ c ≠ (u, w)) = T₁ := by
  ext c
  rw [Finset.mem_filter, mem_runGlue]
  constructor
  · rintro ⟨hc | hc | ⟨h, rfl⟩ | ⟨h, rfl⟩, h2, h3⟩
    · exact hc
    · have := (h₂.chord hc).bounds; omega
    · exact absurd rfl h3
    · dsimp only at h2; omega
  · intro hc
    have := (h₁.chord hc).bounds
    exact ⟨Or.inl hc, by omega, by rw [prod_ne_iff]; omega⟩

private theorem runGlue_filter_right {w : ℤ} {T₁ T₂ : Finset (ℤ × ℤ)}
    (h₁ : IsRunTriangulation u w T₁) (h₂ : IsRunTriangulation w v T₂) :
    (runGlue u w v T₁ T₂).filter (fun c => w ≤ c.1 ∧ c ≠ (w, v)) = T₂ := by
  ext c
  rw [Finset.mem_filter, mem_runGlue]
  constructor
  · rintro ⟨hc | hc | ⟨h, rfl⟩ | ⟨h, rfl⟩, h2, h3⟩
    · have := (h₁.chord hc).bounds; omega
    · exact hc
    · dsimp only at h2; omega
    · exact absurd rfl h3
  · intro hc
    have := (h₂.chord hc).bounds
    exact ⟨Or.inr (Or.inl hc), by omega, by rw [prod_ne_iff]; omega⟩

private theorem isRunChord_of_mem_runGlue {w : ℤ} {T₁ T₂ : Finset (ℤ × ℤ)} (huw : u < w)
    (hwv : w < v) (h₁ : IsRunTriangulation u w T₁) (h₂ : IsRunTriangulation w v T₂) {c : ℤ × ℤ}
    (hc : c ∈ runGlue u w v T₁ T₂) : IsRunChord u v c := by
  rw [isRunChord_iff]
  rcases mem_runGlue.1 hc with hc | hc | ⟨h, rfl⟩ | ⟨h, rfl⟩
  · have := (h₁.chord hc).bounds; omega
  · have := (h₂.chord hc).bounds; omega
  all_goals omega

private theorem not_runCross_of_mem_runGlue {w : ℤ} {T₁ T₂ : Finset (ℤ × ℤ)}
    (h₁ : IsRunTriangulation u w T₁) (h₂ : IsRunTriangulation w v T₂) {c c' : ℤ × ℤ}
    (hc : c ∈ runGlue u w v T₁ T₂) (hc' : c' ∈ runGlue u w v T₁ T₂) : ¬RunCross c c' := by
  have cls : ∀ c ∈ runGlue u w v T₁ T₂, (c ∈ T₁ ∧ u ≤ c.1 ∧ c.2 ≤ w) ∨
      (c ∈ T₂ ∧ w ≤ c.1 ∧ c.2 ≤ v) ∨ c = (u, w) ∨ c = (w, v) := fun c hc => by
    rcases mem_runGlue.1 hc with hc | hc | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · have := (h₁.chord hc).bounds; exact Or.inl ⟨hc, by omega, by omega⟩
    · have := (h₂.chord hc).bounds; exact Or.inr (Or.inl ⟨hc, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases cls c hc with ⟨hc, b⟩ | ⟨hc, b⟩ | rfl | rfl <;>
    rcases cls c' hc' with ⟨hc', b'⟩ | ⟨hc', b'⟩ | rfl | rfl
  all_goals first
    | exact h₁.not_runCross hc hc'
    | exact h₂.not_runCross hc hc'
    | (unfold RunCross; omega)

private theorem exists_runCross_of_notMem_runGlue {w : ℤ} {T₁ T₂ : Finset (ℤ × ℤ)}
    (h₁ : IsRunTriangulation u w T₁) (h₂ : IsRunTriangulation w v T₂) {f : ℤ × ℤ}
    (hf : IsRunChord u v f) (hfG : f ∉ runGlue u w v T₁ T₂) :
    ∃ c ∈ runGlue u w v T₁ T₂, RunCross f c := by
  by_contra hno
  push Not at hno
  apply hfG
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf.bounds
  by_cases hf1 : f.1 < w ∧ w < f.2
  · exfalso
    by_cases hfu : f.1 = u
    · exact hno _ (mem_runGlue.2 (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))))
        (by unfold RunCross; omega)
    · exact hno _ (mem_runGlue.2 (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))))
        (by unfold RunCross; omega)
  rcases (show f.2 ≤ w ∨ w ≤ f.1 by omega) with h | h
  · by_cases hfe : f = (u, w)
    · subst hfe; exact mem_runGlue.2 (Or.inr (Or.inr (Or.inl ⟨f4, rfl⟩)))
    by_cases hfT : f ∈ T₁
    · exact mem_runGlue.2 (Or.inl hfT)
    obtain ⟨c', hc', hcr⟩ :=
      h₁.exists_runCross (isRunChord_iff.2 ⟨f1, f2, h, f4, prod_ne_iff.1 hfe⟩) hfT
    exact absurd hcr (hno c' (mem_runGlue.2 (Or.inl hc')))
  · by_cases hfe : f = (w, v)
    · subst hfe; exact mem_runGlue.2 (Or.inr (Or.inr (Or.inr ⟨f4, rfl⟩)))
    by_cases hfT : f ∈ T₂
    · exact mem_runGlue.2 (Or.inr (Or.inl hfT))
    obtain ⟨c', hc', hcr⟩ :=
      h₂.exists_runCross (isRunChord_iff.2 ⟨h, f2, f3, f4, prod_ne_iff.1 hfe⟩) hfT
    exact absurd hcr (hno c' (mem_runGlue.2 (Or.inr (Or.inl hc'))))

/-- **Splitting a run triangulation at the apex of its outer side**: gluing triangulations of
`[u, w]` and `[w, v]`, `u < w < v`, gives a triangulation of `[u, v]` in which the outer side
has apex `w`. -/
@[cluster_algebras "lem_run_split"]
theorem isRunTriangulation_runGlue {w : ℤ} {T₁ T₂ : Finset (ℤ × ℤ)} (huw : u < w) (hwv : w < v)
    (h₁ : IsRunTriangulation u w T₁) (h₂ : IsRunTriangulation w v T₂) :
    IsRunTriangulation u v (runGlue u w v T₁ T₂) ∧
      IsRunTriangle u v (runGlue u w v T₁ T₂) u w v := by
  refine ⟨isRunTriangulation_iff.2 ⟨fun c hc => isRunChord_of_mem_runGlue huw hwv h₁ h₂ hc,
    fun c hc c' hc' => not_runCross_of_mem_runGlue h₁ h₂ hc hc',
    fun f hf hfG => exists_runCross_of_notMem_runGlue h₁ h₂ hf hfG⟩, huw, hwv, ?_, ?_,
    Or.inr (Or.inr rfl)⟩
  · by_cases h : 2 ≤ w - u
    · exact Or.inl (mem_runGlue.2 (Or.inr (Or.inr (Or.inl ⟨h, rfl⟩))))
    · exact Or.inr (Or.inl ⟨le_rfl, by omega, by omega⟩)
  · by_cases h : 2 ≤ v - w
    · exact Or.inl (mem_runGlue.2 (Or.inr (Or.inr (Or.inr ⟨h, rfl⟩))))
    · exact Or.inr (Or.inl ⟨by omega, by omega, le_rfl⟩)

private theorem IsRunTriangle.mem_left {w : ℤ} (hw : IsRunTriangle u v T u w v)
    (h : 2 ≤ w - u) : (u, w) ∈ T :=
  mem_of_isRunSegment hw.2.2.1 (by omega) (by have := hw.2.1; rw [prod_ne_iff]; omega)

private theorem IsRunTriangle.mem_right {w : ℤ} (hw : IsRunTriangle u v T u w v)
    (h : 2 ≤ v - w) : (w, v) ∈ T :=
  mem_of_isRunSegment hw.2.2.2.1 (by omega) (by have := hw.1; rw [prod_ne_iff]; omega)

/-- If `w` is the apex of the outer side, no chord crosses `w`. -/
private theorem IsRunTriangulation.le_or_le_of_isRunTriangle (hT : IsRunTriangulation u v T)
    {w : ℤ} (hw : IsRunTriangle u v T u w v) {c : ℤ × ℤ} (hc : c ∈ T) : c.2 ≤ w ∨ w ≤ c.1 := by
  by_contra h
  push Not at h
  have := (hT.chord hc).bounds
  by_cases hc1 : c.1 = u
  · exact hT.not_runCross hc (hw.mem_right (by omega)) (by unfold RunCross; omega)
  · exact hT.not_runCross hc (hw.mem_left (by omega)) (by unfold RunCross; omega)

private theorem IsRunTriangulation.isRunTriangulation_filter_left (hT : IsRunTriangulation u v T)
    {w : ℤ} (hw : IsRunTriangle u v T u w v) :
    IsRunTriangulation u w (T.filter fun c => c.2 ≤ w ∧ c ≠ (u, w)) := by
  have hwv := hw.2.1
  refine isRunTriangulation_iff.2 ⟨fun c hc => ?_, fun c hc c' hc' => ?_, fun g hg hgT => ?_⟩
  · rw [Finset.mem_filter] at hc
    have := (hT.chord hc.1).bounds
    have := prod_ne_iff.1 hc.2.2
    rw [isRunChord_iff]
    omega
  · exact hT.not_runCross (Finset.mem_filter.1 hc).1 (Finset.mem_filter.1 hc').1
  · have gb := hg.bounds
    obtain ⟨c', hc', hcr⟩ := hT.exists_runCross
      (isRunChord_iff.2 ⟨by omega, by omega, by omega, by omega, Or.inr (by omega)⟩)
      fun h => hgT (Finset.mem_filter.2 ⟨h, by omega, by rw [prod_ne_iff]; omega⟩)
    refine ⟨c', Finset.mem_filter.2 ⟨hc', ?_, ?_⟩, hcr⟩
    · rcases hT.le_or_le_of_isRunTriangle hw hc' with h | h
      · exact h
      · unfold RunCross at hcr; omega
    · rintro rfl; unfold RunCross at hcr; omega

private theorem IsRunTriangulation.isRunTriangulation_filter_right (hT : IsRunTriangulation u v T)
    {w : ℤ} (hw : IsRunTriangle u v T u w v) :
    IsRunTriangulation w v (T.filter fun c => w ≤ c.1 ∧ c ≠ (w, v)) := by
  have huw := hw.1
  refine isRunTriangulation_iff.2 ⟨fun c hc => ?_, fun c hc c' hc' => ?_, fun g hg hgT => ?_⟩
  · rw [Finset.mem_filter] at hc
    have := (hT.chord hc.1).bounds
    have := prod_ne_iff.1 hc.2.2
    rw [isRunChord_iff]
    omega
  · exact hT.not_runCross (Finset.mem_filter.1 hc).1 (Finset.mem_filter.1 hc').1
  · have gb := hg.bounds
    obtain ⟨c', hc', hcr⟩ := hT.exists_runCross
      (isRunChord_iff.2 ⟨by omega, by omega, by omega, by omega, Or.inl (by omega)⟩)
      fun h => hgT (Finset.mem_filter.2 ⟨h, by omega, by rw [prod_ne_iff]; omega⟩)
    refine ⟨c', Finset.mem_filter.2 ⟨hc', ?_, ?_⟩, hcr⟩
    · rcases hT.le_or_le_of_isRunTriangle hw hc' with h | h
      · have := (hT.chord hc').bounds
        unfold RunCross at hcr; omega
      · exact h
    · rintro rfl; unfold RunCross at hcr; omega

/-- **Splitting a run triangulation at the apex of its outer side**: if `w` is the apex of the
outer side of a triangulation `T` of `[u, v]`, every chord of `T` is contained in `[u, w]` or in
`[w, v]`, and `T` is glued from the set `T₁` of its chords contained in `[u, w]` other than
`(u, w)` and the set `T₂` of its chords contained in `[w, v]` other than `(w, v)`, which are
triangulations of `[u, w]` and `[w, v]`. -/
@[cluster_algebras "lem_run_split"]
theorem IsRunTriangulation.eq_runGlue_of_isRunTriangle (hT : IsRunTriangulation u v T) {w : ℤ}
    (hw : IsRunTriangle u v T u w v) :
    (∀ c ∈ T, c.2 ≤ w ∨ w ≤ c.1) ∧
      IsRunTriangulation u w (T.filter fun c => c.2 ≤ w ∧ c ≠ (u, w)) ∧
      IsRunTriangulation w v (T.filter fun c => w ≤ c.1 ∧ c ≠ (w, v)) ∧
      T = runGlue u w v (T.filter fun c => c.2 ≤ w ∧ c ≠ (u, w))
        (T.filter fun c => w ≤ c.1 ∧ c ≠ (w, v)) := by
  refine ⟨fun c hc => hT.le_or_le_of_isRunTriangle hw hc, hT.isRunTriangulation_filter_left hw,
    hT.isRunTriangulation_filter_right hw, ?_⟩
  ext c
  rw [mem_runGlue, Finset.mem_filter, Finset.mem_filter]
  refine ⟨fun hc => ?_, ?_⟩
  · have cb := (hT.chord hc).bounds
    rcases hT.le_or_le_of_isRunTriangle hw hc with h | h
    · by_cases hcuw : c = (u, w)
      · rw [hcuw] at cb
        exact Or.inr (Or.inr (Or.inl ⟨by omega, hcuw⟩))
      · exact Or.inl ⟨hc, h, hcuw⟩
    · by_cases hcwv : c = (w, v)
      · rw [hcwv] at cb
        exact Or.inr (Or.inr (Or.inr ⟨by omega, hcwv⟩))
      · exact Or.inr (Or.inl ⟨hc, h, hcwv⟩)
  · rintro (⟨hc, -⟩ | ⟨hc, -⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩)
    exacts [hc, hc, hw.mem_left h, hw.mem_right h]

/-- **Splitting a run triangulation at the apex of its outer side**: every triangulation of
`[u, v]`, `v - u ≥ 2`, arises by gluing from exactly one triple `(w, T₁, T₂)`. -/
@[cluster_algebras "lem_run_split"]
theorem IsRunTriangulation.existsUnique_runGlue (hT : IsRunTriangulation u v T)
    (huv : 2 ≤ v - u) :
    ∃! p : ℤ × Finset (ℤ × ℤ) × Finset (ℤ × ℤ), u < p.1 ∧ p.1 < v ∧
      IsRunTriangulation u p.1 p.2.1 ∧ IsRunTriangulation p.1 v p.2.2 ∧
        T = runGlue u p.1 v p.2.1 p.2.2 := by
  obtain ⟨w, hw, -⟩ := hT.existsUnique_apex huv (Or.inr rfl)
  obtain ⟨-, h₁, h₂, hTeq⟩ := hT.eq_runGlue_of_isRunTriangle hw
  refine ⟨(w, T.filter (fun c => c.2 ≤ w ∧ c ≠ (u, w)), T.filter (fun c => w ≤ c.1 ∧ c ≠ (w, v))),
    ⟨hw.1, hw.2.1, h₁, h₂, hTeq⟩, ?_⟩
  rintro ⟨w', T₁, T₂⟩ ⟨hw1, hw2, hT₁, hT₂, rfl⟩
  dsimp only at hw1 hw2 hT₁ hT₂ hT hw ⊢
  obtain rfl := hT.apex_unique hw (isRunTriangulation_runGlue hw1 hw2 hT₁ hT₂).2
  rw [runGlue_filter_left hT₁ hT₂, runGlue_filter_right hT₁ hT₂]

/-- A run of length at most one has no chords. -/
private theorem IsRunTriangulation.eq_empty (hT : IsRunTriangulation u v T) (h : ¬2 ≤ v - u) :
    T = ∅ :=
  Finset.eq_empty_of_forall_notMem fun c hc => by have := (hT.chord hc).bounds; omega

/-- **A triangulation of a run of length `L` has `L - 2` chords** (and none if `L = 1`):
`|T| + [L ≥ 2] = L - 1`. -/
@[cluster_algebras "lem_run_size"]
theorem IsRunTriangulation.card (hT : IsRunTriangulation u v T) (huv : u < v) :
    (T.card : ℤ) + (if 2 ≤ v - u then 1 else 0) = v - u - 1 := by
  suffices h : ∀ n : ℕ, ∀ u v : ℤ, ∀ T : Finset (ℤ × ℤ), (v - u).toNat = n →
      IsRunTriangulation u v T → u < v →
        (T.card : ℤ) + (if 2 ≤ v - u then 1 else 0) = v - u - 1 from h _ u v T rfl hT huv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u v T hn hT huv
  by_cases h2 : 2 ≤ v - u
  · obtain ⟨⟨w, T₁, T₂⟩, ⟨hw1, hw2, h₁, h₂, rfl⟩, -⟩ := hT.existsUnique_runGlue h2
    have c₁ := ih (w - u).toNat (by omega) u w T₁ rfl h₁ hw1
    have c₂ := ih (v - w).toNat (by omega) w v T₂ rfl h₂ hw2
    rw [card_runGlue h₁ h₂ hw1 hw2, if_pos h2]
    push_cast
    split_ifs at c₁ c₂ ⊢ <;> omega
  · rw [hT.eq_empty h2, if_neg h2, Finset.card_empty, Nat.cast_zero]
    omega

/-! ### Parents and flips -/

/-- A chord is a short side of at most one triangle. -/
private theorem IsRunTriangulation.parent_unique (hT : IsRunTriangulation u v T) {x z : ℤ}
    {t t' : ℤ × ℤ × ℤ}
    (ht : IsRunTriangle u v T t.1 t.2.1 t.2.2 ∧ ((t.1 = x ∧ t.2.1 = z) ∨ (t.2.1 = x ∧ t.2.2 = z)))
    (ht' : IsRunTriangle u v T t'.1 t'.2.1 t'.2.2 ∧
      ((t'.1 = x ∧ t'.2.1 = z) ∨ (t'.2.1 = x ∧ t'.2.2 = z))) : t = t' := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨a', b', c'⟩ := t'
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, hx⟩ := ht
  obtain ⟨⟨h1', h2', h3', h4', h5'⟩, hx'⟩ := ht'
  dsimp only at h1 h2 h3 h4 h5 hx h1' h2' h3' h4' h5' hx'
  have n := fun {s s' : ℤ × ℤ} (hs : IsRunSegment u v T s) (hs' : IsRunSegment u v T s') =>
    hT.not_runCross_of_isRunSegment hs hs'
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hx' with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst ha hb
  · have n1 := n h5 h4'
    have n2 := n h5' h4
    unfold RunCross at n1 n2
    obtain rfl : c = c' := by omega
    rfl
  · have n1 := n h5' h5
    unfold RunCross at n1
    omega
  · have n1 := n h5 h5'
    unfold RunCross at n1
    omega
  · have n1 := n h3 h5'
    have n2 := n h3' h5
    unfold RunCross at n1 n2
    obtain rfl : a = a' := by omega
    rfl

private theorem IsRunTriangulation.exists_parent (hT : IsRunTriangulation u v T) {x z : ℤ}
    (hxz : (x, z) ∈ T) :
    ∃ t : ℤ × ℤ × ℤ, IsRunTriangle u v T t.1 t.2.1 t.2.2 ∧
      ((t.1 = x ∧ t.2.1 = z) ∨ (t.2.1 = x ∧ t.2.2 = z)) := by
  classical
  have cb := (hT.chord hxz).bounds
  dsimp only at cb
  obtain ⟨⟨s, e⟩, hbL, hbmin⟩ :=
    ((insert (u, v) T).filter fun b => b.1 ≤ x ∧ z ≤ b.2 ∧ b ≠ (x, z)).exists_min_image
      (fun b => b.2 - b.1) ⟨(u, v), Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _,
        by omega, by omega, by rw [prod_ne_iff]; omega⟩⟩
  rw [Finset.mem_filter, Finset.mem_insert] at hbL
  obtain ⟨hbT, hb1, hb2, hbne⟩ := hbL
  have hbne' := prod_ne_iff.1 hbne
  dsimp only at hb1 hb2 hbne'
  have hbseg : IsRunSegment u v T (s, e) := hbT.symm.imp_right Or.inr
  have hbb := hT.segment_bounds hbseg
  dsimp only at hbb
  have hmemL : ∀ b ∈ T, b.1 ≤ x → z ≤ b.2 → b ≠ (x, z) → e - s ≤ b.2 - b.1 := fun b hb h1 h2 h3 =>
    hbmin b (Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem hb, h1, h2, h3⟩)
  obtain ⟨m, hsm, hme, hsms, hmes, hses⟩ := hT.exists_apex hbseg (by omega)
  have ns1 := hT.not_runCross_of_isRunSegment hsms (Or.inl hxz)
  have ns2 := hT.not_runCross_of_isRunSegment hmes (Or.inl hxz)
  have hmsb := hT.segment_bounds hsms
  have hmeb := hT.segment_bounds hmes
  dsimp only at hmsb hmeb
  unfold RunCross at ns1 ns2
  rcases (show m ≤ x ∨ z ≤ m by omega) with hm' | hm'
  · obtain ⟨rfl, rfl⟩ : m = x ∧ e = z := by
      by_contra hne
      have := hmemL _ (mem_of_isRunSegment hmes (by omega) (by rw [prod_ne_iff]; omega)) hm' hb2
        (by rw [Ne, Prod.mk.injEq]; exact hne)
      dsimp only at this
      omega
    exact ⟨(s, m, e), ⟨hsm, hme, hsms, hmes, hses⟩, Or.inr ⟨rfl, rfl⟩⟩
  · obtain ⟨rfl, rfl⟩ : s = x ∧ m = z := by
      by_contra hne
      have := hmemL _ (mem_of_isRunSegment hsms (by omega) (by rw [prod_ne_iff]; omega)) hb1 hm'
        (by rw [Ne, Prod.mk.injEq]; exact hne)
      dsimp only at this
      omega
    exact ⟨(s, m, e), ⟨hsm, hme, hsms, hmes, hses⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- **Every chord is a short side of exactly one triangle**, its *parent*: for a chord `(x, z)`
of a triangulation `T`, exactly one triangle of `T` has `(x, z)` as its first short side (it is
`(x, z, w)` with `w > z`) or as its second short side (it is `(x', x, z)` with `x' < x`). -/
@[cluster_algebras "lem_run_parent"]
theorem IsRunTriangulation.existsUnique_parent (hT : IsRunTriangulation u v T) {x z : ℤ}
    (hxz : (x, z) ∈ T) :
    ∃! t : ℤ × ℤ × ℤ, IsRunTriangle u v T t.1 t.2.1 t.2.2 ∧
      ((t.1 = x ∧ t.2.1 = z) ∨ (t.2.1 = x ∧ t.2.2 = z)) := by
  obtain ⟨t₀, ht₀⟩ := hT.exists_parent hxz
  exact ⟨t₀, ht₀, fun t ht => hT.parent_unique ht ht₀⟩

/-- **Every chord is a short side of exactly one triangle**: the outer side is a short side of no
triangle, and no side `(x, x + 1)` is a base. -/
@[cluster_algebras "lem_run_parent"]
theorem IsRunTriangulation.short_sides_ne_outer (hT : IsRunTriangulation u v T) {x y z : ℤ}
    (h : IsRunTriangle u v T x y z) : (x, y) ≠ (u, v) ∧ (y, z) ≠ (u, v) ∧ x + 1 < z := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  have b3 := hT.segment_bounds h3
  have b4 := hT.segment_bounds h4
  dsimp only at b3 b4
  refine ⟨?_, ?_, by omega⟩ <;> rw [prod_ne_iff] <;> omega

/-- `c'` is the **replacement** of the chord `c` in a flip of the run triangulation `T`: `c ∈ T`,
`c'` is a chord of `[u, v]` not in `T`, and `(T \ {c}) ∪ {c'}` is a triangulation. By
`IsRunTriangulation.isRunFlip_right` and `IsRunTriangulation.isRunFlip_left` it exists and is
unique, given the parent triangle from `IsRunTriangulation.existsUnique_parent`. -/
@[cluster_algebras "lem_run_flip"]
def IsRunFlip (u v : ℤ) (T : Finset (ℤ × ℤ)) (c c' : ℤ × ℤ) : Prop :=
  IsRunTriangulation u v T ∧ c ∈ T ∧ IsRunChord u v c' ∧ c' ∉ T ∧
    IsRunTriangulation u v (insert c' (T.erase c))

/-- Crossing of chords is symmetric. -/
theorem runCross_comm {c c' : ℤ × ℤ} : RunCross c c' ↔ RunCross c' c := by
  unfold RunCross; omega

/-- Replacing `c` by a chord `c'` crossing it gives a triangulation, provided every chord crossing
`c` other than `c'` crosses one of a family `P` of segments of `T` different from `c`, and no other
chord of `T` crosses `c'`. -/
private theorem IsRunTriangulation.isRunTriangulation_insert_erase (hT : IsRunTriangulation u v T)
    {c c' : ℤ × ℤ} (hc' : IsRunChord u v c') (hcc' : RunCross c c') (P : ℤ × ℤ → Prop)
    (hP : ∀ s, P s → IsRunSegment u v T s ∧ s ≠ c)
    (key : ∀ f : ℤ × ℤ, RunCross f c → f ≠ c' → ∃ s, P s ∧ RunCross f s)
    (nc : ∀ e ∈ T, e ≠ c → ¬RunCross e c') :
    IsRunTriangulation u v (insert c' (T.erase c)) := by
  refine isRunTriangulation_iff.2 ⟨?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hc'
    · exact hT.chord (Finset.mem_of_mem_erase he)
  · intro e he e' he'
    rcases Finset.mem_insert.1 he with rfl | he₁ <;>
      rcases Finset.mem_insert.1 he' with rfl | he₁'
    · unfold RunCross; omega
    · rw [runCross_comm]
      exact nc e' (Finset.mem_of_mem_erase he₁') (Finset.ne_of_mem_erase he₁')
    · exact nc e (Finset.mem_of_mem_erase he₁) (Finset.ne_of_mem_erase he₁)
    · exact hT.not_runCross (Finset.mem_of_mem_erase he₁) (Finset.mem_of_mem_erase he₁')
  · intro f hf hfT'
    by_cases hfc : f = c
    · exact ⟨c', Finset.mem_insert_self _ _, hfc ▸ hcc'⟩
    have hfT : f ∉ T := fun h => hfT' (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hfc, h⟩))
    obtain ⟨g, hg, hfg⟩ := hT.exists_runCross hf hfT
    by_cases hgc : g = c
    · subst hgc
      have hfc' : f ≠ c' := fun h => hfT' (h ▸ Finset.mem_insert_self _ _)
      obtain ⟨s, hs, hfs⟩ := key f hfg hfc'
      have fb := hf.bounds
      have hsT := mem_of_runCross (hP s hs).1 fb.1 fb.2.2.1 hfs
      exact ⟨s, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨(hP s hs).2, hsT⟩), hfs⟩
    · exact ⟨g, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hgc, hg⟩), hfg⟩

/-- If every chord crossing `c` other than `c'` crosses one of a family `P` of segments of `T`
different from `c`, and no other chord of `T` crosses `c'`, then `c'` is the unique replacement
of `c`. -/
private theorem IsRunTriangulation.isRunFlip_of_forall (hT : IsRunTriangulation u v T)
    {c c' : ℤ × ℤ} (hc : c ∈ T) (hc' : IsRunChord u v c') (hc'T : c' ∉ T)
    (hcc' : RunCross c c') (P : ℤ × ℤ → Prop) (hP : ∀ s, P s → IsRunSegment u v T s ∧ s ≠ c)
    (key : ∀ f : ℤ × ℤ, RunCross f c → f ≠ c' → ∃ s, P s ∧ RunCross f s)
    (nc : ∀ e ∈ T, e ≠ c → ¬RunCross e c') :
    IsRunFlip u v T c c' ∧ ∀ c'', IsRunFlip u v T c c'' → c'' = c' := by
  refine ⟨⟨hT, hc, hc', hc'T, hT.isRunTriangulation_insert_erase hc' hcc' P hP key nc⟩, ?_⟩
  rintro c'' ⟨-, -, hc'', hc''T, hT''⟩
  by_contra hne
  have hcross : RunCross c'' c := by
    by_contra hnc
    obtain ⟨g, hg, hcg⟩ := hT.exists_runCross hc'' hc''T
    by_cases hgc : g = c
    · exact hnc (hgc ▸ hcg)
    · exact hT''.not_runCross (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hgc, hg⟩)) hcg
  obtain ⟨s, hs, hfs⟩ := key c'' hcross hne
  have fb := hc''.bounds
  have hsT := mem_of_runCross (hP s hs).1 fb.1 fb.2.2.1 hfs
  exact hT''.not_runCross (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨(hP s hs).2, hsT⟩)) hfs

/-- **Flips in a run triangulation**, when the parent of `c = (x, z)` is `(x, z, w)`: with `y` the
apex of `c`, the chord `c' = (y, w)` is not in `T`, `(T \ {c}) ∪ {c'}` is a triangulation, and
`c'` is the only chord with these properties. -/
@[cluster_algebras "lem_run_flip"]
theorem IsRunTriangulation.isRunFlip_right (hT : IsRunTriangulation u v T) {x y z w : ℤ}
    (hc : (x, z) ∈ T) (hapex : IsRunTriangle u v T x y z) (hpar : IsRunTriangle u v T x z w) :
    IsRunFlip u v T (x, z) (y, w) ∧ ∀ c'', IsRunFlip u v T (x, z) c'' → c'' = (y, w) := by
  obtain ⟨h1, h2, hxy, hyz, -⟩ := hapex
  obtain ⟨-, h3, -, hzw, hxw⟩ := hpar
  have bxy := hT.segment_bounds hxy
  have bzw := hT.segment_bounds hzw
  dsimp only at bxy bzw
  have hcc' : RunCross (x, z) (y, w) := by unfold RunCross; omega
  refine hT.isRunFlip_of_forall hc ?_ ?_ hcc'
    (fun s => s = (x, y) ∨ s = (y, z) ∨ s = (z, w) ∨ s = (x, w)) ?_ ?_ ?_
  · rw [isRunChord_iff]; dsimp only; omega
  · exact fun h => hT.not_runCross hc h hcc'
  · rintro s (rfl | rfl | rfl | rfl) <;> exact ⟨by assumption, by rw [prod_ne_iff]; omega⟩
  · intro f hf hfc'
    have hfc'' := prod_ne_iff.1 hfc'
    unfold RunCross at hf
    dsimp only at hf
    rcases hf with ⟨hf1, hf2, hf3⟩ | ⟨hf1, hf2, hf3⟩
    · by_cases hfw : f.2 < w
      · by_cases hfz : z < f.2
        · exact ⟨(z, w), Or.inr (Or.inr (Or.inl rfl)), by unfold RunCross; omega⟩
        · exact ⟨(x, w), Or.inr (Or.inr (Or.inr rfl)), by unfold RunCross; omega⟩
      · exact ⟨(x, w), Or.inr (Or.inr (Or.inr rfl)), by unfold RunCross; omega⟩
    · by_cases hfw : f.2 = w
      · by_cases hfy : f.1 < y
        · exact ⟨(x, y), Or.inl rfl, by unfold RunCross; omega⟩
        · exact ⟨(y, z), Or.inr (Or.inl rfl), by unfold RunCross; omega⟩
      · by_cases hfw' : f.2 < w
        · exact ⟨(z, w), Or.inr (Or.inr (Or.inl rfl)), by unfold RunCross; omega⟩
        · exact ⟨(x, w), Or.inr (Or.inr (Or.inr rfl)), by unfold RunCross; omega⟩
  · intro e he hec
    have eb := (hT.chord he).bounds
    have hec' := prod_ne_iff.1 hec
    have n1 := hT.not_runCross_of_isRunSegment (Or.inl he) hxy
    have n2 := hT.not_runCross_of_isRunSegment (Or.inl he) hyz
    have n3 := hT.not_runCross_of_isRunSegment (Or.inl he) hzw
    have n4 := hT.not_runCross_of_isRunSegment (Or.inl he) hxw
    have n5 := hT.not_runCross he hc
    unfold RunCross at n1 n2 n3 n4 n5 ⊢
    dsimp only at n1 n2 n3 n4 n5 hec' ⊢
    omega

/-- **Flips in a run triangulation**, when the parent of `c = (x, z)` is `(x', x, z)`: with `y`
the apex of `c`, the chord `c' = (x', y)` is not in `T`, `(T \ {c}) ∪ {c'}` is a triangulation,
and `c'` is the only chord with these properties. -/
@[cluster_algebras "lem_run_flip"]
theorem IsRunTriangulation.isRunFlip_left (hT : IsRunTriangulation u v T) {x' x y z : ℤ}
    (hc : (x, z) ∈ T) (hapex : IsRunTriangle u v T x y z) (hpar : IsRunTriangle u v T x' x z) :
    IsRunFlip u v T (x, z) (x', y) ∧ ∀ c'', IsRunFlip u v T (x, z) c'' → c'' = (x', y) := by
  obtain ⟨h1, h2, hxy, hyz, -⟩ := hapex
  obtain ⟨h3, -, hx'x, -, hx'z⟩ := hpar
  have bxy := hT.segment_bounds hxy
  have bx'x := hT.segment_bounds hx'x
  have byz := hT.segment_bounds hyz
  dsimp only at bxy bx'x byz
  have hcc' : RunCross (x, z) (x', y) := by unfold RunCross; omega
  refine hT.isRunFlip_of_forall hc ?_ ?_ hcc'
    (fun s => s = (x', x) ∨ s = (x', z) ∨ s = (x, y) ∨ s = (y, z)) ?_ ?_ ?_
  · rw [isRunChord_iff]; dsimp only; omega
  · exact fun h => hT.not_runCross hc h hcc'
  · rintro s (rfl | rfl | rfl | rfl) <;> exact ⟨by assumption, by rw [prod_ne_iff]; omega⟩
  · intro f hf hfc'
    have hfc'' := prod_ne_iff.1 hfc'
    unfold RunCross at hf
    dsimp only at hf
    rcases hf with ⟨hf1, hf2, hf3⟩ | ⟨hf1, hf2, hf3⟩
    · by_cases hfx : f.1 = x'
      · by_cases hfy : f.2 < y
        · exact ⟨(x, y), Or.inr (Or.inr (Or.inl rfl)), by unfold RunCross; omega⟩
        · exact ⟨(y, z), Or.inr (Or.inr (Or.inr rfl)), by unfold RunCross; omega⟩
      · by_cases hfx' : f.1 < x'
        · exact ⟨(x', z), Or.inr (Or.inl rfl), by unfold RunCross; omega⟩
        · exact ⟨(x', x), Or.inl rfl, by unfold RunCross; omega⟩
    · exact ⟨(x', z), Or.inr (Or.inl rfl), by unfold RunCross; omega⟩
  · intro e he hec
    have eb := (hT.chord he).bounds
    have hec' := prod_ne_iff.1 hec
    have n1 := hT.not_runCross_of_isRunSegment (Or.inl he) hx'x
    have n2 := hT.not_runCross_of_isRunSegment (Or.inl he) hx'z
    have n3 := hT.not_runCross_of_isRunSegment (Or.inl he) hxy
    have n4 := hT.not_runCross_of_isRunSegment (Or.inl he) hyz
    have n5 := hT.not_runCross he hc
    unfold RunCross at n1 n2 n3 n4 n5 ⊢
    dsimp only at n1 n2 n3 n4 n5 hec' ⊢
    omega

/-! ### The fan and the Catalan count -/

/-- The **fan** `{(u, j) : u + 2 ≤ j ≤ v - 1}` of `[u, v]`. -/
@[cluster_algebras "lem_run_fan"]
def runFan (u v : ℤ) : Finset (ℤ × ℤ) :=
  (intRange (u + 2) (v - 1)).image fun j => (u, j)

/-- Membership in the fan `runFan u v`. -/
@[simp]
theorem mem_runFan {c : ℤ × ℤ} :
    c ∈ runFan u v ↔ c.1 = u ∧ u + 2 ≤ c.2 ∧ c.2 ≤ v - 1 := by
  simp only [runFan, Finset.mem_image, mem_intRange]
  refine ⟨fun ⟨j, hj, e⟩ => by subst e; exact ⟨rfl, hj⟩, fun ⟨h1, h2, h3⟩ =>
    ⟨c.2, ⟨h2, h3⟩, Prod.ext h1.symm rfl⟩⟩

/-- **The fan triangulation**: the fan is a triangulation of `[u, v]`. -/
@[cluster_algebras "lem_run_fan"]
theorem isRunTriangulation_runFan (u v : ℤ) : IsRunTriangulation u v (runFan u v) := by
  refine isRunTriangulation_iff.2 ⟨?_, ?_, ?_⟩
  · intro c hc
    rw [mem_runFan] at hc
    rw [isRunChord_iff]
    omega
  · intro c hc c' hc'
    rw [mem_runFan] at hc hc'
    unfold RunCross
    omega
  · intro f hf hfF
    have fb := hf.bounds
    have hfu : f.1 ≠ u := fun h => hfF (mem_runFan.2 ⟨h, by omega, by omega⟩)
    exact ⟨(u, f.1 + 1), mem_runFan.2 ⟨rfl, by omega, by omega⟩, by unfold RunCross; omega⟩

/-- **The fan triangulation**: the triangles of the fan are exactly the `(u, j, j + 1)` with
`u + 1 ≤ j ≤ v - 1`. -/
@[cluster_algebras "lem_run_fan"]
theorem isRunTriangle_runFan_iff {x y z : ℤ} :
    IsRunTriangle u v (runFan u v) x y z ↔ x = u ∧ u + 1 ≤ y ∧ y ≤ v - 1 ∧ z = y + 1 := by
  unfold IsRunTriangle IsRunSegment
  simp only [mem_runFan, Prod.mk.injEq]
  omega

/-- The finite set of triangulations of `[u, v]`. -/
private noncomputable def runTriangulations (u v : ℤ) : Finset (Finset (ℤ × ℤ)) := by
  classical
  exact (intRange u v ×ˢ intRange u v).powerset.filter (IsRunTriangulation u v)

private theorem mem_runTriangulations : T ∈ runTriangulations u v ↔ IsRunTriangulation u v T := by
  classical
  unfold runTriangulations
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨And.right, fun h => ⟨fun c hc => ?_, h⟩⟩
  have := (h.chord hc).bounds
  rw [Finset.mem_product, mem_intRange, mem_intRange]
  omega

/-- For `v - u ≥ 2`, gluing is a bijection onto the triangulations of `[u, v]` from the triples
`(i, T₁, T₂)` with `T₁` a triangulation of `[u, u + 1 + i]` and `T₂` one of `[u + 1 + i, v]`. -/
private theorem card_runTriangulations_eq_card_sigma (h2 : 2 ≤ v - u) :
    (runTriangulations u v).card = ((Finset.range ((v - u).toNat - 1)).sigma fun i : ℕ =>
      runTriangulations u (u + 1 + i) ×ˢ runTriangulations (u + 1 + i) v).card := by
  symm
  refine Finset.card_bij (fun a _ => runGlue u (u + 1 + a.1) v a.2.1 a.2.2) ?_ ?_ ?_
  · rintro ⟨i, T₁, T₂⟩ ha
    rw [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, mem_runTriangulations,
      mem_runTriangulations] at ha
    rw [mem_runTriangulations]
    exact (isRunTriangulation_runGlue (by omega) (by omega) ha.2.1 ha.2.2).1
  · rintro ⟨i, T₁, T₂⟩ ha ⟨i', T₁', T₂'⟩ ha' heq
    rw [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, mem_runTriangulations,
      mem_runTriangulations] at ha ha'
    dsimp only at heq ha ha'
    have hG := (isRunTriangulation_runGlue (by omega) (by omega) ha.2.1 ha.2.2).1
    have := (hG.existsUnique_runGlue h2).unique
      (y₁ := (u + 1 + i, T₁, T₂)) (y₂ := (u + 1 + i', T₁', T₂'))
      ⟨by dsimp only; omega, by dsimp only; omega, ha.2.1, ha.2.2, rfl⟩
      ⟨by dsimp only; omega, by dsimp only; omega, ha'.2.1, ha'.2.2, heq⟩
    simp only [Prod.mk.injEq] at this
    obtain ⟨h1, rfl, rfl⟩ := this
    obtain rfl : i = i' := by omega
    rfl
  · intro T hT
    rw [mem_runTriangulations] at hT
    obtain ⟨⟨w, T₁, T₂⟩, ⟨hw1, hw2, h₁, h₂, hTeq⟩, -⟩ := hT.existsUnique_runGlue h2
    dsimp only at hw1 hw2 h₁ h₂ hTeq
    have hw : u + 1 + ((w - u - 1).toNat : ℤ) = w := by omega
    refine ⟨⟨(w - u - 1).toNat, T₁, T₂⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, mem_runTriangulations,
        mem_runTriangulations]
      dsimp only
      rw [hw]
      exact ⟨by omega, h₁, h₂⟩
    · dsimp only
      rw [hw, hTeq]

private theorem card_runTriangulations (huv : u < v) :
    (runTriangulations u v).card = catalanNumber (v - u - 1).toNat := by
  suffices h : ∀ n : ℕ, ∀ u v : ℤ, (v - u).toNat = n → u < v →
      (runTriangulations u v).card = catalanNumber (v - u - 1).toNat from h _ u v rfl huv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u v hn huv
  by_cases h2 : 2 ≤ v - u
  · obtain ⟨N, hN⟩ : ∃ N, (v - u).toNat = N + 2 := ⟨(v - u).toNat - 2, by omega⟩
    rw [card_runTriangulations_eq_card_sigma h2, show (v - u).toNat - 1 = N + 1 by omega,
      show (v - u - 1).toNat = N + 1 by omega, catalanNumber_succ, Finset.card_sigma]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Finset.card_product, ih ((u + 1 + i) - u).toNat (by omega) u (u + 1 + i) rfl (by omega),
      ih (v - (u + 1 + i)).toNat (by omega) (u + 1 + i) v rfl (by omega)]
    congr 2 <;> omega
  · have hT0 : runTriangulations u v = {∅} := by
      ext T
      rw [mem_runTriangulations, Finset.mem_singleton]
      refine ⟨fun hT => hT.eq_empty h2, ?_⟩
      rintro rfl
      exact isRunTriangulation_iff.2 ⟨by simp, by simp, fun c hc _ => by have := hc.bounds; omega⟩
    rw [hT0, Finset.card_singleton, show (v - u - 1).toNat = 0 by omega, catalanNumber_zero]

/-- **Triangulations of a run are counted by Catalan numbers**: for `u < v`, the run `[u, v]` has
exactly `C_{v - u - 1}` triangulations. -/
@[cluster_algebras "lem_run_catalan"]
theorem encard_setOf_isRunTriangulation (huv : u < v) :
    {T : Finset (ℤ × ℤ) | IsRunTriangulation u v T}.encard =
      catalanNumber (v - u - 1).toNat := by
  rw [show {T | IsRunTriangulation u v T} = ↑(runTriangulations u v) from
    Set.ext fun _ => mem_runTriangulations.symm, Set.encard_coe_eq_coe_finsetCard,
    card_runTriangulations huv]

end ClusterAlgebras.TypeD

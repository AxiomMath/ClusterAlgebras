/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TypeA.Flips

/-!
# Corners of a triangulation

Let `T` be a triangulation of the convex `m`-gon, whose vertices are the elements of `ZMod m`,
labelled clockwise. A *corner* of `T` is a triple `(a, b, c)` such that `{a, b, c}` is a triangle
of `T` and the listing `(a, b, c)` is clockwise; it is the corner at `a` of the triangle
`{a, b, c}`. Each triangle has exactly three corners, its clockwise listings, which are the
cyclic rotations of one another. The corners index the white vertices' darts in the plabic graph
`G(T)` of the triangulation.

Over a segment `{a, c}` of `T` there is a corner `(a, b, c)` exactly when `c ≠ a + 1`, and then
exactly one; this is the apex of the triangle on the side of `{a, c}` running clockwise from `a`
to `c`. Counting corners by the ordered pair `(a, c)` they sit on gives `|C(T)| = 3m - 6`.

## Main definitions

* `ClusterAlgebras.triangulationCorners T`: the set `C(T)` of corners of `T`.

## Main results

* `ClusterAlgebras.mem_triangulationCorners_iff`: `(a, b, c)` is a corner if and only if `b` lies
  strictly between `a` and `c` and `{a, b}`, `{b, c}`, `{a, c}` are segments of `T`.
* `ClusterAlgebras.card_filter_mem_triangulationCorners`: over a segment `{a, c}` of `T` there are
  no corners if `c = a + 1` and exactly one otherwise.
* `ClusterAlgebras.card_triangulationCorners`: `|C(T)| = 3m - 6`.

## Implementation notes

A corner is an element of `ZMod m × ZMod m × ZMod m`, and `C(T)` is a `Finset` of such triples.
The definition does not assume that `T` is a triangulation; the two counting results do, and
they assume `3 ≤ m`.
-/

@[expose] public section

namespace ClusterAlgebras

open TypeA

variable {m : ℕ} [NeZero m]

/-! ### Two facts about the cyclic order on `ZMod m` -/

/-- Nothing lies strictly between `a` and its successor `a + 1`. -/
theorem not_sbtw_self_add_one (a b : ZMod m) : ¬sbtw a b (a + 1) := by
  rw [sbtw_iff_sbtw_basePos a, Int.sbtw_iff, basePos_self, basePos_add_one, basePos_self]
  have h1 := basePos_nonneg a b
  have h2 := basePos_lt a b
  split_ifs <;> omega

/-- If `c` is neither `a` nor `a + 1`, then `a + 1` lies strictly between `a` and `c`. -/
theorem sbtw_self_add_one {a c : ZMod m} (hac : a ≠ c) (hc : c ≠ a + 1) : sbtw a (a + 1) c := by
  have hi := basePos_injective a
  have h0 : basePos a c ≠ basePos a a := fun h => hac (hi h).symm
  have h1 : basePos a c ≠ basePos a (a + 1) := fun h => hc (hi h)
  rw [sbtw_iff_sbtw_basePos a, Int.sbtw_iff]
  rw [basePos_self] at h0 ⊢
  rw [basePos_add_one, basePos_self] at h1 ⊢
  have h2 := basePos_nonneg a c
  have h3 := basePos_lt a c
  split_ifs at h1 ⊢ <;> omega

/-! ### Corners -/

/-- The set `C(T)` of **corners** of `T`: the triples `(a, b, c)` of elements of `ZMod m` such
that `{a, b, c}` is a triangle of `T` and the listing `(a, b, c)` is clockwise. -/
@[cluster_algebras "def_triangulation_corner"]
def triangulationCorners (T : Finset (Sym2 (ZMod m))) : Finset (ZMod m × ZMod m × ZMod m) :=
  Finset.univ.filter fun x => IsTriangle T {x.1, x.2.1, x.2.2} ∧ IsClockwise x.1 x.2.1 x.2.2

/-- Membership in `C(T)`, unfolded. -/
theorem mem_triangulationCorners {T : Finset (Sym2 (ZMod m))} {a b c : ZMod m} :
    (a, b, c) ∈ triangulationCorners T ↔ IsTriangle T {a, b, c} ∧ IsClockwise a b c := by
  simp [triangulationCorners]

/-- `(a, b, c)` is a corner of `T` if and only if `b` lies strictly between `a` and `c` and
`{a, b}`, `{b, c}`, `{a, c}` are segments of `T`. -/
theorem mem_triangulationCorners_iff {T : Finset (Sym2 (ZMod m))} {a b c : ZMod m} :
    (a, b, c) ∈ triangulationCorners T ↔
      sbtw a b c ∧ s(a, b) ∈ segments T ∧ s(b, c) ∈ segments T ∧ s(a, c) ∈ segments T := by
  rw [mem_triangulationCorners, IsTriangle]
  refine and_comm.trans (and_congr_right fun hc => ?_)
  have hab : a ≠ b := fun h => sbtw_irrefl_left (h ▸ hc)
  have hbc : b ≠ c := fun h => sbtw_irrefl_right (h ▸ hc)
  have hac : a ≠ c := fun h => sbtw_irrefl_left_right (h ▸ hc)
  refine ⟨fun ⟨_, h⟩ => ⟨h a (by simp) b (by simp) hab, h b (by simp) c (by simp) hbc,
    h a (by simp) c (by simp) hac⟩, fun ⟨h1, h2, h3⟩ =>
      ⟨Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩, fun u hu v hv huv => ?_⟩⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first
      | exact absurd rfl huv
      | assumption
      | rwa [Sym2.eq_swap]

/-- The corners of `T` are closed under cyclic rotation: `(a, b, c)` is a corner exactly when
`(b, c, a)` is. -/
theorem rotate_mem_triangulationCorners_iff {T : Finset (Sym2 (ZMod m))} {a b c : ZMod m} :
    (b, c, a) ∈ triangulationCorners T ↔ (a, b, c) ∈ triangulationCorners T := by
  rw [mem_triangulationCorners_iff, mem_triangulationCorners_iff, sbtw_cyclic,
    Sym2.eq_swap (a := c), Sym2.eq_swap (a := b) (b := a)]
  tauto

/-- A corner `(a, b, c)` sits on a segment `{a, c}` with `c ≠ a + 1`. -/
theorem ne_add_one_of_mem_triangulationCorners {T : Finset (Sym2 (ZMod m))} {a b c : ZMod m}
    (h : (a, b, c) ∈ triangulationCorners T) : c ≠ a + 1 := by
  rintro rfl
  exact not_sbtw_self_add_one a b (mem_triangulationCorners_iff.1 h).1

/-- Over a segment `{a, c}` of a triangulation with `c ≠ a + 1` there is exactly one corner
`(a, b, c)`. -/
theorem existsUnique_mem_triangulationCorners (hm : 3 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) {a c : ZMod m} (hac : s(a, c) ∈ segments T) (hc : c ≠ a + 1) :
    ∃! b, (a, b, c) ∈ triangulationCorners T := by
  have hne : a ≠ c := by
    rintro rfl
    rcases mem_segments.1 hac with h | h
    · exact (hT.isDiagonal _ h).1 (Sym2.mk_isDiag_iff.2 rfl)
    · exact (isSide_mk_iff.1 h).elim hc hc
  simp only [mem_triangulationCorners_iff, hac, and_true]
  exact IsTriangulation.existsUnique_apex hm hT hac ⟨a + 1, sbtw_self_add_one hne hc⟩

/-- **The apex of a corner.** If `{a, c}` is a segment of a triangulation `T`, the number of `b`
with `(a, b, c) ∈ C(T)` is `0` if `c = a + 1` and `1` otherwise. -/
@[cluster_algebras "lem_triangulation_corner_apex"]
theorem card_filter_mem_triangulationCorners (hm : 3 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) {a c : ZMod m} (hac : s(a, c) ∈ segments T) :
    (Finset.univ.filter fun b => (a, b, c) ∈ triangulationCorners T).card =
      if c = a + 1 then 0 else 1 := by
  split_ifs with hc
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b _ hb
    exact ne_add_one_of_mem_triangulationCorners hb hc
  · obtain ⟨b, hb, hu⟩ := existsUnique_mem_triangulationCorners hm hT hac hc
    rw [Finset.card_eq_one]
    exact ⟨b, Finset.ext fun b' => by simpa using ⟨hu b', fun h => h ▸ hb⟩⟩

/-! ### Counting corners -/

/-- Each segment `e` of `T` is `s(a, c)` for exactly two ordered pairs `(a, c)`, so the ordered
pairs spanning segments of `T` are twice as many as the segments. -/
theorem card_filter_mk_mem_segments (T : Finset (Sym2 (ZMod m)))
    (hT : ∀ e ∈ segments T, ¬e.IsDiag) :
    (Finset.univ.filter fun p : ZMod m × ZMod m => s(p.1, p.2) ∈ segments T).card =
      2 * (segments T).card := by
  refine (Finset.card_eq_sum_card_fiberwise (f := fun p : ZMod m × ZMod m => s(p.1, p.2))
    (s := Finset.univ.filter fun p : ZMod m × ZMod m => s(p.1, p.2) ∈ segments T)
    (t := segments T) (fun p hp => (Finset.mem_filter.1 hp).2)).trans ?_
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with | _ u v => ?_
  have huv : u ≠ v := fun h => hT _ he (Sym2.mk_isDiag_iff.2 h)
  rw [show (Finset.univ.filter fun p : ZMod m × ZMod m => s(p.1, p.2) ∈ segments T).filter
      (fun p => s(p.1, p.2) = s(u, v)) = {(u, v), (v, u)} by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, Sym2.eq_iff]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact he
    · rwa [Sym2.eq_swap]]
  rw [Finset.card_pair (by simp [huv])]

/-- In a triangle, the only triangulation is the empty one: every segment is a side. -/
theorem IsTriangulation.eq_empty_of_eq_three (hm : m = 3) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) : T = ∅ := by
  subst hm
  refine Finset.eq_empty_of_forall_notMem fun e he => ?_
  obtain ⟨hs, hside⟩ := hT.isDiagonal e he
  induction e using Sym2.ind with | _ u v => ?_
  have huv : u ≠ v := fun h => hs (Sym2.mk_isDiag_iff.2 h)
  have key : ∀ x y : ZMod 3, x ≠ y → y = x + 1 ∨ x = y + 1 := by decide
  exact hside (isSide_mk_iff.2 (key u v huv))

/-- No segment of a triangulation is degenerate. -/
theorem IsTriangulation.not_isDiag_of_mem_segments (hm : 3 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) {e : Sym2 (ZMod m)} (he : e ∈ segments T) : ¬e.IsDiag := by
  rcases mem_segments.1 he with h | ⟨i, rfl⟩
  · exact (hT.isDiagonal e h).1
  · rw [Sym2.mk_isDiag_iff]
    intro h
    have h₁ : ((1 : ℕ) : ZMod m) = ((0 : ℕ) : ZMod m) := by
      rw [Nat.cast_one, Nat.cast_zero]
      linear_combination -h
    rw [natCast_inj_of_lt (by omega) (by omega)] at h₁
    omega

/-- A triangulation of the convex `m`-gon has `(m - 3) + m` segments: its `m - 3` diagonals and
the `m` sides. -/
theorem IsTriangulation.card_segments (hm : 3 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) : (segments T).card = (m - 3) + m := by
  have hTcard : T.card = m - 3 := by
    rcases (show m = 3 ∨ 4 ≤ m by omega) with h | h
    · rw [IsTriangulation.eq_empty_of_eq_three h hT, Finset.card_empty]
      omega
    · exact IsTriangulation.card_eq h hT
  rw [segments, Finset.card_union_of_disjoint, hTcard, card_filter_isSide hm]
  exact Finset.disjoint_left.2 fun e he hs => (hT.isDiagonal e he).2 (Finset.mem_filter.1 hs).2

/-- The corners of a triangulation `T` are in bijection with the ordered pairs `(a, c)` spanning a
segment of `T` with `c ≠ a + 1`. -/
theorem card_triangulationCorners_eq_card_filter (hm : 3 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) : (triangulationCorners T).card =
      (Finset.univ.filter fun p : ZMod m × ZMod m =>
        s(p.1, p.2) ∈ segments T ∧ p.2 ≠ p.1 + 1).card := by
  refine Finset.card_nbij (fun x => (x.1, x.2.2)) (fun x hx => ?_) (fun x hx y hy hxy => ?_)
    (fun p hp => ?_)
  · obtain ⟨a, b, c⟩ := x
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_triangulationCorners_iff.1 hx).2.2.2,
      ne_add_one_of_mem_triangulationCorners hx⟩
  · obtain ⟨a, b, c⟩ := x
    obtain ⟨a', b', c'⟩ := y
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
    obtain ⟨b₀, -, hu⟩ := existsUnique_mem_triangulationCorners hm hT
      (mem_triangulationCorners_iff.1 hx).2.2.2 (ne_add_one_of_mem_triangulationCorners hx)
    rw [hu b hx, hu b' hy]
  · obtain ⟨a, c⟩ := p
    obtain ⟨-, hac, hc⟩ := Finset.mem_filter.1 hp
    obtain ⟨b, hb, -⟩ := existsUnique_mem_triangulationCorners hm hT hac hc
    exact ⟨(a, b, c), hb, rfl⟩

/-- There are exactly `m` ordered pairs `(a, a + 1)` spanning a segment of `T`. -/
theorem card_filter_mk_mem_segments_eq_add_one (T : Finset (Sym2 (ZMod m))) :
    (Finset.univ.filter fun p : ZMod m × ZMod m =>
      s(p.1, p.2) ∈ segments T ∧ ¬p.2 ≠ p.1 + 1).card = m := by
  refine Eq.trans ?_ ((Finset.card_univ (α := ZMod m)).trans (ZMod.card m))
  refine (Finset.card_nbij' (fun p => p.1) (fun a => (a, a + 1)) (fun _ _ => by simp)
    (fun a _ => ?_) (fun p hp => ?_) (fun _ _ => rfl))
  · simpa using mem_segments.2 (.inr ⟨a, rfl⟩)
  · obtain ⟨a, c⟩ := p
    simp_all

/-- **The number of corners.** A triangulation of the convex `m`-gon, `m ≥ 3`, has
`3m - 6` corners. -/
@[cluster_algebras "lem_triangulation_corner_count"]
theorem card_triangulationCorners (hm : 3 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) : (triangulationCorners T).card = 3 * m - 6 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun p : ZMod m × ZMod m => s(p.1, p.2) ∈ segments T)
    (fun p : ZMod m × ZMod m => p.2 ≠ p.1 + 1)
  rw [Finset.filter_filter, Finset.filter_filter, card_filter_mk_mem_segments_eq_add_one,
    card_filter_mk_mem_segments T fun _ => hT.not_isDiag_of_mem_segments hm,
    hT.card_segments hm] at hsplit
  rw [card_triangulationCorners_eq_card_filter hm hT]
  omega

end ClusterAlgebras

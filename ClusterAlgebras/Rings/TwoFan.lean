/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.RectanglesQuiver
public import ClusterAlgebras.TypeA.Flips
public import ClusterAlgebras.TotalPositivity.Segment

/-!
# For `a = 2` the rectangles quiver is the quiver of a fan

Let `b ≥ 4` and let `T_b = {{j, b} : j ∈ [2, b - 2]}`, the diagonals of the convex `b`-gon at
the vertex `b`. Then `T_b` is a triangulation, and `v ↦ J(v) mod b`, the set of residues of the
elements of the label `J(v)`, is an isomorphism of quivers from the rectangles quiver `Q_{2,b}`
onto the quiver `Q(T_b)` of the triangulation.

With `c = b - 2`, the labels are `J(1, q) = {b - 1 - q, b}`, `J(2, q) = {b - 1 - q, b - q}` and
`J(∅) = {b - 1, b}`. The diagonals of `T_b` are the `J(1, q)` with `q ≤ c - 1`, and the `b` sides
of the polygon are `J(1, c) = {1, b}`, the `J(2, q)` and `J(∅)`. The triangles of `T_b` are the
`{j, j + 1, b}`, and their clockwise listings `(j, j + 1, b)` give exactly the arrows
`(2, q) → (1, q - 1)`, `(1, q) → (1, q + 1)`, `(1, q) → (2, q)` and `∅ → (1, 1)` of `Q_{2,b}`,
with `j = b - 1 - q`.

## Main definitions

* `ClusterAlgebras.lastFanTriangulation m`: the fan `T_m` of the convex `m`-gon at its last
  vertex.
* `ClusterAlgebras.twoFanSegment n v`: the segment `J(v) mod b` of the `b`-gon, `b = n + 3`.
* `ClusterAlgebras.twoFanEquiv n`: `v ↦ J(v) mod b` as a bijection from the vertices of
  `Q_{2,b}` onto the segments of `T_b`.
* `ClusterAlgebras.twoFanIso n`: the isomorphism of quivers `Q_{2,b} → Q(T_b)`.

## Main results

* `ClusterAlgebras.isTriangulation_lastFanTriangulation`: `T_b` is a triangulation.
* `ClusterAlgebras.natCast_mem_twoFanIso_equiv_iff`: the isomorphism sends `v` to `J(v) mod b`.
* `ClusterAlgebras.polygonArrows_twoFanSegment`: the arrow counts agree along `v ↦ J(v) mod b`.
* `ClusterAlgebras.twoFanSegment_mem_lastFanTriangulation_iff`,
  `ClusterAlgebras.isSide_twoFanSegment_iff`: `J(v) mod b` is a diagonal of `T_b` exactly when
  `v` is mutable, and a side exactly when `v` is frozen.
* `ClusterAlgebras.segmentPlucker_twoFanSegment`: `P_{J(v) mod b} = P_{J(v)}`.
* `ClusterAlgebras.polygonArrows_eq_ite`: the arrow count of the quiver of any set of segments
  is `1` or `0`, according to whether some triangle carries a clockwise listing along the two
  segments.

## Implementation notes

* **The size of the polygon.** The bound `b ≥ 4` is expressed by writing `b = n + 3`, so that
  the polygon is the `(n + 3)`-gon of the Plücker seeds `ClusterAlgebras.TypeA.pluckerSeed`. The
  hypothesis `n ≥ 1` is not needed: for `n = 0` the triangle has the single triangulation `∅`,
  which is `T_3`, and `Q_{2,3}` is three frozen vertices without arrows, as is `Q(∅)`.
* **Vertices.** The polygon's vertices are `ZMod b`, and the 0-based column `x : Fin b` of a
  label is the vertex `(x : ZMod b)`; this is the convention of `ClusterAlgebras.vertexRep` and
  `ClusterAlgebras.segmentPlucker`, under which the vertex `v` is the vertex `v + 1` of the
  labelling by `[1, b]`. So the vertex `b` of that labelling is `-1 : ZMod b` and
  `T_b = {s(j, -1) : j ∈ [1, b - 3]}`.
* **Rectangles.** With the 0-based rectangles `some (p, q)` of `ClusterAlgebras.RectVertex`, the
  segment `J(v) mod b` is `s(n + 1, -1)` for `v = ∅`, `s(n - q, -1)` for `p = 0` and
  `s(n - q, n + 1 - q)` for `p = 1`.
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### Arrows of the quiver of a set of segments -/

section PolygonArrows

variable {m : ℕ} [NeZero m]

omit [NeZero m] in
/-- The three vertices of a clockwise listing are pairwise distinct. -/
theorem IsClockwise.ne {a b c : ZMod m} (h : IsClockwise a b c) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c :=
  ⟨by rintro rfl; exact sbtw_irrefl_left h, by rintro rfl; exact sbtw_irrefl_left_right h,
    by rintro rfl; exact sbtw_irrefl_right h⟩

/-- Three distinct vertices form a triangle of `T` exactly when their three pairs are segments
of `T`. -/
theorem isTriangle_insert_insert_singleton_iff {T : Finset (Sym2 (ZMod m))} {a b c : ZMod m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    IsTriangle T {a, b, c} ↔
      s(a, b) ∈ segments T ∧ s(b, c) ∈ segments T ∧ s(a, c) ∈ segments T := by
  refine ⟨fun h => ⟨h.2 a (by simp) b (by simp) hab, h.2 b (by simp) c (by simp) hbc,
    h.2 a (by simp) c (by simp) hac⟩, fun ⟨h₁, h₂, h₃⟩ =>
      ⟨Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩, fun u hu v hv huv => ?_⟩⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first | exact absurd rfl huv | assumption | rwa [Sym2.eq_swap]

/-- A triangle carrying a clockwise listing `(a, b, c)` is the only triangle of `T` carrying an
arrow from `s(a, b)` to `s(b, c)`. -/
theorem arrowTriangles_eq_singleton {T : Finset (Sym2 (ZMod m))} {t₀ : Finset (ZMod m)}
    {a b c : ZMod m} (ht₀ : IsTriangle T t₀) (hcw : IsClockwise a b c) (ha : a ∈ t₀)
    (hb : b ∈ t₀) (hc : c ∈ t₀) : arrowTriangles T s(a, b) s(b, c) = {t₀} := by
  obtain ⟨hab, hac, hbc⟩ := hcw.ne
  have hne : s(a, b) ≠ s(b, c) := by
    rw [Ne, Sym2.eq_iff]
    rintro (⟨h, -⟩ | ⟨h, -⟩) <;> contradiction
  ext t
  rw [mem_arrowTriangles, Finset.mem_singleton]
  constructor
  · rintro ⟨htri, a', b', c', -, h₁, h₂, ha', hb', hc'⟩
    refine IsTriangle.eq_of_mem_sym2 (σ := s(a, b)) (σ' := s(b, c))
      (by rwa [Sym2.mk_isDiag_iff]) (by rwa [Sym2.mk_isDiag_iff]) hne htri ht₀ ?_ ?_
      (Finset.mk_mem_sym2_iff.2 ⟨ha, hb⟩) (Finset.mk_mem_sym2_iff.2 ⟨hb, hc⟩)
    · rw [h₁]
      exact Finset.mk_mem_sym2_iff.2 ⟨ha', hb'⟩
    · rw [h₂]
      exact Finset.mk_mem_sym2_iff.2 ⟨hb', hc'⟩
  · rintro rfl
    exact ⟨ht₀, a, b, c, hcw, rfl, rfl, ha, hb, hc⟩

/-- **The arrow count of the quiver of `T` is `0` or `1`**: `a(σ, σ') = 1` exactly when `σ` and
`σ'` are not both sides and some triangle `{a, b, c}` of `T` has a clockwise listing `(a, b, c)`
with `σ = s(a, b)` and `σ' = s(b, c)`. -/
theorem polygonArrows_eq_ite (T : Finset (Sym2 (ZMod m))) (σ σ' : Sym2 (ZMod m)) :
    polygonArrows T σ σ' =
      if ¬(IsSide σ ∧ IsSide σ') ∧ ∃ a b c, IsClockwise a b c ∧ σ = s(a, b) ∧ σ' = s(b, c) ∧
        IsTriangle T {a, b, c} then 1 else 0 := by
  unfold polygonArrows
  by_cases hs : IsSide σ ∧ IsSide σ'
  · simp [hs]
  rw [if_neg hs]
  by_cases h : ∃ a b c, IsClockwise a b c ∧ σ = s(a, b) ∧ σ' = s(b, c) ∧ IsTriangle T {a, b, c}
  · rw [if_pos ⟨hs, h⟩]
    obtain ⟨a, b, c, hcw, rfl, rfl, ht⟩ := h
    rw [arrowTriangles_eq_singleton ht hcw (by simp) (by simp) (by simp), Finset.card_singleton]
  · rw [if_neg fun h' => h h'.2, Finset.card_eq_zero]
    refine Finset.eq_empty_of_forall_notMem fun t ht => h ?_
    obtain ⟨htri, a, b, c, hcw, hσ, hσ', ha, hb, hc⟩ := mem_arrowTriangles.1 ht
    obtain ⟨hab, hac, hbc⟩ := hcw.ne
    have hsub : ({a, b, c} : Finset (ZMod m)) ⊆ t := by
      simp [Finset.insert_subset_iff, ha, hb, hc]
    have heq : ({a, b, c} : Finset (ZMod m)) = t := Finset.eq_of_subset_of_card_le hsub
      (by rw [htri.1, Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩])
    exact ⟨a, b, c, hcw, hσ, hσ', heq ▸ htri⟩

end PolygonArrows

/-! ### The fan at the last vertex -/

/-- The **fan `T_m` at the last vertex** of the convex `m`-gon: the diagonals `s(j, -1)`,
`j ∈ [1, m - 3]`. Labelling the vertices by `[1, m]` instead, these are the `{j, m}`,
`j ∈ [2, m - 2]`. -/
@[cluster_algebras "lem_rectangles_two_fan"]
def lastFanTriangulation (m : ℕ) : Finset (Sym2 (ZMod m)) :=
  (Finset.Icc 1 (m - 3)).image fun j : ℕ => s((j : ZMod m), -1)

section TwoFan

variable {n : ℕ}

/-! #### Vertices of the `(n + 3)`-gon read as natural numbers -/

/-- Vertices are equal exactly when their representatives are. -/
private theorem eq_iff_val {u v : ZMod (n + 3)} : u = v ↔ u.val = v.val :=
  (ZMod.val_injective _).eq_iff.symm

/-- Equality of unordered pairs of vertices, read on representatives. -/
private theorem sym2_eq_iff_val {a b c d : ZMod (n + 3)} :
    s(a, b) = s(c, d) ↔ (a.val = c.val ∧ b.val = d.val) ∨ (a.val = d.val ∧ b.val = c.val) := by
  rw [Sym2.eq_iff, eq_iff_val, eq_iff_val, eq_iff_val, eq_iff_val]

/-- Circular betweenness on `ZMod (n + 3)`, read on representatives. -/
private theorem sbtw_iff_val {a b c : ZMod (n + 3)} :
    sbtw a b c ↔ (a.val < b.val ∧ b.val < c.val) ∨ (b.val < c.val ∧ c.val < a.val) ∨
      (c.val < a.val ∧ a.val < b.val) :=
  Fin.sbtw_iff

/-- The representative of the successor of a vertex. -/
private theorem val_add_one' (u : ZMod (n + 3)) :
    (u + 1).val = if u.val = n + 2 then 0 else u.val + 1 := by
  have : Fact (1 < n + 3) := ⟨by omega⟩
  rw [ZMod.val_add, ZMod.val_one]
  have := u.val_lt
  split_ifs with h
  · simp [h]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- The last vertex `-1` has representative `n + 2`. -/
private theorem val_neg_one' : (-1 : ZMod (n + 3)).val = n + 2 :=
  ZMod.val_neg_one (n + 2)

/-- Sides of the `(n + 3)`-gon, read on representatives. -/
private theorem isSide_mk_iff_val {u v : ZMod (n + 3)} :
    IsSide s(u, v) ↔ v.val = u.val + 1 ∨ u.val = v.val + 1 ∨ (u.val = n + 2 ∧ v.val = 0) ∨
      (v.val = n + 2 ∧ u.val = 0) := by
  rw [TypeA.isSide_mk_iff, eq_iff_val, eq_iff_val, val_add_one', val_add_one']
  have := u.val_lt
  have := v.val_lt
  split_ifs <;> omega

/-- The diagonals of `T_{n+3}`, read on representatives. -/
private theorem mk_mem_lastFanTriangulation_iff_val {u v : ZMod (n + 3)} :
    s(u, v) ∈ lastFanTriangulation (n + 3) ↔
      (1 ≤ u.val ∧ u.val ≤ n ∧ v.val = n + 2) ∨ (1 ≤ v.val ∧ v.val ≤ n ∧ u.val = n + 2) := by
  simp only [lastFanTriangulation, Finset.mem_image, Finset.mem_Icc, Nat.add_sub_cancel]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, h⟩
    rw [sym2_eq_iff_val, ZMod.val_natCast_of_lt (by omega), val_neg_one'] at h
    omega
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> refine ⟨_, ⟨h1, h2⟩, ?_⟩ <;>
      rw [sym2_eq_iff_val, ZMod.val_natCast_of_lt (by omega), val_neg_one'] <;> omega

/-- The segments of `T_{n+3}`, read on representatives. -/
private theorem mk_mem_segments_lastFanTriangulation_iff_val {u v : ZMod (n + 3)} :
    s(u, v) ∈ segments (lastFanTriangulation (n + 3)) ↔
      (1 ≤ u.val ∧ u.val ≤ n ∧ v.val = n + 2) ∨ (1 ≤ v.val ∧ v.val ≤ n ∧ u.val = n + 2) ∨
        v.val = u.val + 1 ∨ u.val = v.val + 1 ∨ (u.val = n + 2 ∧ v.val = 0) ∨
          (v.val = n + 2 ∧ u.val = 0) := by
  rw [mem_segments, mk_mem_lastFanTriangulation_iff_val, isSide_mk_iff_val]
  tauto

/-- **`T_b` is a triangulation** of the convex `b`-gon, `b = n + 3`: its diagonals pairwise
share the vertex `-1` (the vertex `b` in the labelling by `[1, b]`), so none cross, and every
other diagonal `s(x, y)`, `x < y < b - 1`, crosses `s(x + 1, -1)`. -/
@[cluster_algebras "lem_rectangles_two_fan"]
theorem isTriangulation_lastFanTriangulation (n : ℕ) :
    IsTriangulation (lastFanTriangulation (n + 3)) where
  isDiagonal e he := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he
    rw [Finset.mem_Icc, Nat.add_sub_cancel] at hj
    refine ⟨fun h => ?_, ?_⟩
    · rw [Sym2.mk_isDiag_iff, eq_iff_val, ZMod.val_natCast_of_lt (by omega), val_neg_one'] at h
      omega
    · rw [isSide_mk_iff_val, ZMod.val_natCast_of_lt (by omega), val_neg_one']
      omega
  noncrossing e he f hf hc := by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨a, b, c, d, h₁, h₂, -, hac, had, hbc, hbd, -⟩ := Cross.pairwise_ne hc
    have h₁' : (-1 : ZMod (n + 3)) ∈ s(a, b) := h₁ ▸ Sym2.mem_mk_right _ _
    have h₂' : (-1 : ZMod (n + 3)) ∈ s(c, d) := h₂ ▸ Sym2.mem_mk_right _ _
    rw [Sym2.mem_iff] at h₁' h₂'
    rcases h₁' with rfl | rfl <;> rcases h₂' with h | h <;> simp_all
  maximal e he heT := by
    induction e using Sym2.ind with | _ u v => ?_
    have hu := u.val_lt
    have hv := v.val_lt
    have hseg : u.val ≠ v.val := fun h => he.1 (Sym2.mk_isDiag_iff.2 (eq_iff_val.2 h))
    have hside := mt isSide_mk_iff_val.2 he.2
    rw [mk_mem_lastFanTriangulation_iff_val] at heT
    obtain ⟨x, y, hxy, hxyuv⟩ : ∃ x y : ZMod (n + 3), x.val < y.val ∧ s(u, v) = s(x, y) := by
      rcases Nat.lt_or_gt_of_ne hseg with h | h
      · exact ⟨u, v, h, rfl⟩
      · exact ⟨v, u, h, Sym2.eq_swap⟩
    have hval := sym2_eq_iff_val.1 hxyuv
    have hx := x.val_lt
    have hy := y.val_lt
    rw [hxyuv]
    refine ⟨s(((x.val + 1 : ℕ) : ZMod (n + 3)), -1), ?_,
      x, y, ((x.val + 1 : ℕ) : ZMod (n + 3)), -1, rfl, rfl, ?_, ?_⟩
    · rw [mk_mem_lastFanTriangulation_iff_val, ZMod.val_natCast_of_lt (by omega), val_neg_one']
      omega
    · rw [sbtw_iff_val, ZMod.val_natCast_of_lt (by omega)]
      omega
    · rw [sbtw_iff_val, val_neg_one']
      omega

/-! #### The segments `J(v) mod b` -/

/-- The segment `J(v) mod b` of the `b`-gon, `b = n + 3`, for a vertex `v` of `Q_{2,b}`: it is
`s(n + 1, -1)` for `v = ∅`, `s(n - q, -1)` for the rectangle `some (0, q)` and
`s(n - q, n + 1 - q)` for `some (1, q)`. `natCast_mem_twoFanSegment_iff` says that its vertices
are the residues of the elements of `J(v)`. -/
def twoFanSegment (n : ℕ) : RectVertex 2 (n + 3) → Sym2 (ZMod (n + 3))
  | none => s(((n + 1 : ℕ) : ZMod (n + 3)), -1)
  | some (p, q) => s(((n - q : ℕ) : ZMod (n + 3)),
      if (p : ℕ) = 0 then -1 else ((n + 1 - q : ℕ) : ZMod (n + 3)))

/-- Unfold `twoFanSegment` and read every vertex as a natural number. -/
local macro "twofan_simp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := omega) only [twoFanSegment, Fin.val_zero, Fin.val_one, Fin.val_mk,
  one_ne_zero, ↓reduceIte, sym2_eq_iff_val, sbtw_iff_val,
  mk_mem_segments_lastFanTriangulation_iff_val, isSide_mk_iff_val,
  mk_mem_lastFanTriangulation_iff_val, ZMod.val_natCast_of_lt, val_neg_one', true_and, and_true,
  true_or, or_true] $[$loc]?)

/-- **The vertices of `J(v) mod b` are the residues of the elements of `J(v)`.** -/
theorem natCast_mem_twoFanSegment_iff (v : RectVertex 2 (n + 3)) (x : Fin (n + 3)) :
    ((x : ℕ) : ZMod (n + 3)) ∈ twoFanSegment n v ↔ x ∈ rectLabel 2 (n + 3) v := by
  have hx := x.isLt
  rcases v with _ | ⟨p, q⟩
  · simp (disch := omega) only [twoFanSegment, Sym2.mem_iff, eq_iff_val, ZMod.val_natCast_of_lt,
      val_neg_one', rectLabel, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · have := p.isLt
    have := q.isLt
    by_cases hp : (p : ℕ) = 0 <;>
      simp (disch := omega) only [twoFanSegment, hp, ↓reduceIte, Sym2.mem_iff, eq_iff_val,
        ZMod.val_natCast_of_lt, val_neg_one', rectLabel, Finset.mem_filter, Finset.mem_univ,
        true_and] <;> omega

/-- **The Plücker coordinate of `J(v) mod b` is that of `J(v)`**: `P_{J(v) mod b} = P_{J(v)}`
for every `2 × b` matrix. -/
theorem segmentPlucker_twoFanSegment {R : Type*} [CommRing R]
    (z : Matrix (Fin 2) (Fin (n + 3)) R) (v : RectVertex 2 (n + 3)) :
    segmentPlucker z (twoFanSegment n v) = pluckerCoord z (rectLabel 2 (n + 3) v) := by
  obtain ⟨a, b, hab⟩ : ∃ a b, twoFanSegment n v = s(a, b) := by
    rcases v with _ | ⟨p, q⟩ <;> exact ⟨_, _, rfl⟩
  rw [hab, segmentPlucker_mk]
  congr 1
  ext x
  rw [← natCast_mem_twoFanSegment_iff, hab, Sym2.mem_iff, Finset.mem_insert,
    Finset.mem_singleton, eq_iff_val, eq_iff_val, ZMod.val_natCast_of_lt x.isLt, Fin.ext_iff,
    Fin.ext_iff]
  rfl

/-- `J(v) mod b` is a segment of `T_b`. -/
theorem twoFanSegment_mem_segments (v : RectVertex 2 (n + 3)) :
    twoFanSegment n v ∈ segments (lastFanTriangulation (n + 3)) := by
  rcases v with _ | ⟨p, q⟩
  · twofan_simp
  · have := p.isLt
    have := q.isLt
    by_cases hp : (p : ℕ) = 0 <;> simp only [twoFanSegment, hp, ↓reduceIte] <;> twofan_simp <;>
      omega

/-- `J(v) mod b` is a side of the `b`-gon exactly when `v` is frozen. -/
theorem isSide_twoFanSegment_iff (v : RectVertex 2 (n + 3)) :
    IsSide (twoFanSegment n v) ↔ RectFrozen 2 (n + 3) v := by
  rcases v with _ | ⟨p, q⟩
  · simp only [RectFrozen, iff_true]
    twofan_simp
  · have := p.isLt
    have := q.isLt
    simp only [RectFrozen]
    by_cases hp : (p : ℕ) = 0 <;> simp only [twoFanSegment, hp, ↓reduceIte] <;> twofan_simp <;>
      omega

/-- `J(v) mod b` is a diagonal of `T_b` exactly when `v` is mutable. -/
theorem twoFanSegment_mem_lastFanTriangulation_iff (v : RectVertex 2 (n + 3)) :
    twoFanSegment n v ∈ lastFanTriangulation (n + 3) ↔ ¬RectFrozen 2 (n + 3) v := by
  rcases v with _ | ⟨p, q⟩
  · simp only [RectFrozen, not_true_eq_false, iff_false]
    twofan_simp
    omega
  · have := p.isLt
    have := q.isLt
    simp only [RectFrozen]
    by_cases hp : (p : ℕ) = 0 <;> simp only [twoFanSegment, hp, ↓reduceIte] <;> twofan_simp <;>
      omega

/-- `v ↦ J(v) mod b` is injective. -/
theorem twoFanSegment_injective : Function.Injective (twoFanSegment n) := by
  intro v w h
  rcases v with _ | ⟨p, q⟩ <;> rcases w with _ | ⟨p', q'⟩
  · rfl
  · have := p'.isLt
    have := q'.isLt
    simp only [twoFanSegment] at h
    split_ifs at h <;> twofan_simp at h <;> omega
  · have := p.isLt
    have := q.isLt
    simp only [twoFanSegment] at h
    split_ifs at h <;> twofan_simp at h <;> omega
  · have := p.isLt
    have := q.isLt
    have := p'.isLt
    have := q'.isLt
    simp only [twoFanSegment] at h
    simp only [Option.some.injEq, Prod.mk.injEq, Fin.ext_iff]
    split_ifs at h <;> twofan_simp at h <;> omega

/-- Every segment of `T_b` is `J(v) mod b` for some `v`. -/
theorem exists_twoFanSegment_eq {e : Sym2 (ZMod (n + 3))}
    (he : e ∈ segments (lastFanTriangulation (n + 3))) : ∃ v, twoFanSegment n v = e := by
  induction e using Sym2.ind with | _ x y => ?_
  rw [mk_mem_segments_lastFanTriangulation_iff_val] at he
  have := x.val_lt
  have := y.val_lt
  rcases he with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨some (0, ⟨n - x.val, by omega⟩), by twofan_simp; omega⟩
  · exact ⟨some (0, ⟨n - y.val, by omega⟩), by twofan_simp; omega⟩
  · rcases Nat.lt_or_ge x.val (n + 1) with hx | hx
    · exact ⟨some (1, ⟨n - x.val, by omega⟩), by twofan_simp; omega⟩
    · exact ⟨none, by twofan_simp; omega⟩
  · rcases Nat.lt_or_ge y.val (n + 1) with hy | hy
    · exact ⟨some (1, ⟨n - y.val, by omega⟩), by twofan_simp; omega⟩
    · exact ⟨none, by twofan_simp; omega⟩
  · exact ⟨some (0, ⟨n, by omega⟩), by twofan_simp; omega⟩
  · exact ⟨some (0, ⟨n, by omega⟩), by twofan_simp; omega⟩

/-- `v ↦ J(v) mod b` as a bijection from the vertices of `Q_{2,b}` onto the segments of `T_b`,
`b = n + 3`. -/
noncomputable def twoFanEquiv (n : ℕ) :
    RectVertex 2 (n + 3) ≃ SegmentType (lastFanTriangulation (n + 3)) :=
  Equiv.ofBijective (fun v => ⟨twoFanSegment n v, twoFanSegment_mem_segments v⟩)
    ⟨fun _ _ h => twoFanSegment_injective (congrArg Subtype.val h), fun e =>
      (exists_twoFanSegment_eq e.2).imp fun _ hv => Subtype.ext hv⟩

/-- The segment `twoFanEquiv n v` is `J(v) mod b`. -/
@[simp]
theorem coe_twoFanEquiv (v : RectVertex 2 (n + 3)) : (twoFanEquiv n v).1 = twoFanSegment n v :=
  rfl

/-- A step `v → w` of `Q_{2,b}`, away from pairs of frozen vertices, comes from a triangle of
`T_b` with a clockwise listing `(a, b, c)` such that `J(v) mod b = s(a, b)` and
`J(w) mod b = s(b, c)`. -/
private theorem exists_sbtw_of_rectStep {v w : RectVertex 2 (n + 3)}
    (hF : ¬(RectFrozen 2 (n + 3) v ∧ RectFrozen 2 (n + 3) w)) (h : RectStep 2 (n + 3) v w) :
    ∃ a b c : ZMod (n + 3), sbtw a b c ∧ twoFanSegment n v = s(a, b) ∧
      twoFanSegment n w = s(b, c) ∧ s(a, c) ∈ segments (lastFanTriangulation (n + 3)) := by
  rcases v with _ | ⟨p, q⟩ <;> rcases w with _ | ⟨p', q'⟩
  · exact h.elim
  · simp only [RectStep] at h
    refine ⟨((n + 1 : ℕ) : ZMod (n + 3)), -1, ((n : ℕ) : ZMod (n + 3)), ?_, ?_, ?_, ?_⟩ <;>
      (try simp only [twoFanSegment, h.1, h.2, ↓reduceIte]) <;> twofan_simp <;> omega
  · exact h.elim
  · have := p.isLt
    have := q.isLt
    have := p'.isLt
    have := q'.isLt
    simp only [RectStep] at h
    simp only [RectFrozen, not_and_or, not_or] at hF
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hp : (p : ℕ) = 0 := by omega
      have hp' : (p' : ℕ) = 0 := by omega
      refine ⟨((n - q : ℕ) : ZMod (n + 3)), -1, ((n - q - 1 : ℕ) : ZMod (n + 3)), ?_, ?_, ?_,
        ?_⟩ <;> (try simp only [twoFanSegment, hp, hp', ↓reduceIte]) <;> twofan_simp <;> omega
    · have hp : (p : ℕ) = 0 := by omega
      have hp' : (p' : ℕ) ≠ 0 := by omega
      refine ⟨-1, ((n - q : ℕ) : ZMod (n + 3)), ((n + 1 - q : ℕ) : ZMod (n + 3)), ?_, ?_, ?_,
        ?_⟩ <;> (try simp only [twoFanSegment, hp, hp', ↓reduceIte]) <;> twofan_simp <;> omega
    · have hp : (p : ℕ) ≠ 0 := by omega
      have hp' : (p' : ℕ) = 0 := by omega
      refine ⟨((n - q : ℕ) : ZMod (n + 3)), ((n + 1 - q : ℕ) : ZMod (n + 3)), -1, ?_, ?_, ?_,
        ?_⟩ <;> (try simp only [twoFanSegment, hp, hp', ↓reduceIte]) <;> twofan_simp <;> omega

/-- Conversely, away from pairs of frozen vertices, a clockwise listing `(a, b, c)` of a triangle
of `T_b` with `J(v) mod b = s(a, b)` and `J(w) mod b = s(b, c)` is a step `v → w` of
`Q_{2,b}`. -/
private theorem rectStep_of_exists_sbtw {v w : RectVertex 2 (n + 3)}
    (hF : ¬(RectFrozen 2 (n + 3) v ∧ RectFrozen 2 (n + 3) w))
    (h : ∃ a b c : ZMod (n + 3), sbtw a b c ∧ twoFanSegment n v = s(a, b) ∧
      twoFanSegment n w = s(b, c) ∧ s(a, c) ∈ segments (lastFanTriangulation (n + 3))) :
    RectStep 2 (n + 3) v w := by
  obtain ⟨a, b, c, h1, h2, h3, h4⟩ := h
  have := a.val_lt
  have := b.val_lt
  have := c.val_lt
  rw [sbtw_iff_val] at h1
  rw [mk_mem_segments_lastFanTriangulation_iff_val] at h4
  rcases v with _ | ⟨p, q⟩ <;> rcases w with _ | ⟨p', q'⟩
  · simp only [twoFanSegment] at h2 h3
    twofan_simp at h2 h3
    omega
  · have := p'.isLt
    have := q'.isLt
    simp only [twoFanSegment] at h2 h3
    simp only [RectStep]
    split_ifs at h3 <;> twofan_simp at h2 h3 <;> omega
  · have := p.isLt
    have := q.isLt
    simp only [RectFrozen, not_and_or, not_or, not_true_eq_false, or_false] at hF
    simp only [twoFanSegment] at h2 h3
    split_ifs at h2 <;> twofan_simp at h2 h3 <;> omega
  · have := p.isLt
    have := q.isLt
    have := p'.isLt
    have := q'.isLt
    simp only [twoFanSegment] at h2 h3
    simp only [RectStep]
    split_ifs at h2 h3 <;> twofan_simp at h2 h3 <;> omega

/-- The arrow counts of `Q_{2,b}` and of `Q(T_b)` agree along `v ↦ J(v) mod b`. -/
theorem polygonArrows_twoFanSegment (v w : RectVertex 2 (n + 3)) :
    polygonArrows (lastFanTriangulation (n + 3)) (twoFanSegment n v) (twoFanSegment n w) =
      rectArrows 2 (n + 3) v w := by
  rw [polygonArrows_eq_ite, rectArrows_eq_ite]
  refine if_congr ?_ rfl rfl
  rw [isSide_twoFanSegment_iff, isSide_twoFanSegment_iff]
  refine and_congr_right fun hF => ?_
  rw [show RectStep 2 (n + 3) v w ↔ _ from
    ⟨exists_sbtw_of_rectStep hF, rectStep_of_exists_sbtw hF⟩]
  refine exists₃_congr fun a b c => ⟨?_, ?_⟩
  · rintro ⟨hcw, h1, h2, ht⟩
    exact ⟨hcw, h1, h2, ht.2 a (by simp) c (by simp) hcw.ne.2.1⟩
  · rintro ⟨hcw, h1, h2, h3⟩
    obtain ⟨hab, hac, hbc⟩ := IsClockwise.ne hcw
    exact ⟨hcw, h1, h2, (isTriangle_insert_insert_singleton_iff hab hac hbc).2
      ⟨h1 ▸ twoFanSegment_mem_segments v, h2 ▸ twoFanSegment_mem_segments w, h3⟩⟩

/-- **For `a = 2` the rectangles quiver is the quiver of a fan**: `v ↦ J(v) mod b` is
an isomorphism of quivers from `Q_{2,b}` onto `Q(T_b)`, `b = n + 3`. That it is `J(v) mod b` is
`natCast_mem_twoFanIso_equiv_iff`. -/
@[cluster_algebras "lem_rectangles_two_fan"]
noncomputable def twoFanIso (n : ℕ) :
    Quiver.Iso (rectanglesQuiver 2 (n + 3)) (polygonQuiver (lastFanTriangulation (n + 3))) where
  equiv := twoFanEquiv n
  mem_frozen_iff v := by
    simpa only [polygonQuiver, Finset.mem_filter, Finset.mem_univ, true_and, coe_twoFanEquiv,
      mem_frozen_rectanglesQuiver] using isSide_twoFanSegment_iff v
  arrows_eq v w := polygonArrows_twoFanSegment v w

/-- **The isomorphism `Q_{2,b} → Q(T_b)` is `v ↦ J(v) mod b`**: the vertices of the segment it
assigns to `v` are the residues mod `b` of the elements of `J(v)`. -/
@[cluster_algebras "lem_rectangles_two_fan"]
theorem natCast_mem_twoFanIso_equiv_iff (v : RectVertex 2 (n + 3)) (x : Fin (n + 3)) :
    ((x : ℕ) : ZMod (n + 3)) ∈ ((twoFanIso n).equiv v).1 ↔ x ∈ rectLabel 2 (n + 3) v :=
  natCast_mem_twoFanSegment_iff v x

/-- The segment that the isomorphism `Q_{2,b} → Q(T_b)` assigns to `v` is `J(v) mod b`. -/
@[simp]
theorem twoFanIso_equiv_apply (v : RectVertex 2 (n + 3)) :
    ((twoFanIso n).equiv v).1 = twoFanSegment n v :=
  rfl

end TwoFan

end ClusterAlgebras

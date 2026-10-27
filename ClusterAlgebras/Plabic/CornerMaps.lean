/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BivalentRemoval
public import ClusterAlgebras.Plabic.CornerTriangulation
public import ClusterAlgebras.Plabic.EdgeContraction

/-!
# Corner maps of a contraction

Let `P` be a plabic graph and `{d, d̄}` an edge whose ends `w₁ = v(d)` and `w₂ = v(d̄)` are
distinct vertices with `p ≥ 3` and `q ≥ 3` darts, and let `Q` be the contraction of `P` along
`{d, d̄}`, whose merged vertex `v` has the `m = p + q - 2` darts `(w₁ ∪ w₂) \ {d, d̄}`. The *corner
maps* `κ₁ : w₁ → v` and `κ₂ : w₂ → v` fix every dart except `κ₁(d) = σ⁻¹(d̄)` and
`κ₂(d̄) = σ⁻¹(d)`, and `γ_e = {σ⁻¹(d), σ⁻¹(d̄)}`. In the coordinates `λ₁(i) = σ^{-(i+1)}(d)`,
`λ₂(j) = σ^{-(j+1)}(d̄)` and `λ(i) = σ^{-(i+1)}(d)` (`i < p - 1`), `λ(p - 1 + j) = σ^{-(j+1)}(d̄)`
on the polygons of corners, `κ₁` is the inclusion `ι₁(i) = i` of `[0, p - 1]` into `ℤ/m`, `κ₂` is
`ι₂(j) = p - 1 + j`, and `γ_e` is the diagonal `{0, p - 1}`. So gluing corner triangulations of
`w₁` and `w₂` along `γ_e` is the gluing of a triangulation of the `p`-gon and one of the `q`-gon
along a diagonal of the `m`-gon: it is a bijection onto the corner triangulations of `v` containing
`γ_e`, and the triangles of the glued triangulation are the images of the triangles of the two
pieces.

The file also proves that every crossing has a corner triangulation with a prescribed ear, and
that contracting an edge at a bivalent vertex is the removal of that vertex.

## Main definitions

* `ClusterAlgebras.RotationSystem.cornerMapFst`, `ClusterAlgebras.RotationSystem.cornerMapSnd`,
  `ClusterAlgebras.RotationSystem.cornerGlueDiagonal`: the corner maps `κ₁`, `κ₂` and the
  diagonal `γ_e`.
* `ClusterAlgebras.RotationSystem.cornerGlue`: the glued set `κ₁(D₁) ∪ κ₂(D₂) ∪ {γ_e}`.
* `ClusterAlgebras.polygonGlue`: the glued set `ι₁(T₁) ∪ ι₂(T₂) ∪ {{0, p - 1}}` of diagonals of
  the `m`-gon.
* `ClusterAlgebras.PlabicData.contractEdgeIsoBivalentRemoval`: the isomorphism from a contraction
  at a bivalent vertex to the removal of that vertex.

## Main results

* `ClusterAlgebras.bijOn_polygonGlue`, `ClusterAlgebras.isTriangulation_polygonGlue`,
  `ClusterAlgebras.isTriangle_polygonGlue_iff`: gluing triangulations of polygons along a
  diagonal, and the triangles of the result.
* `ClusterAlgebras.PlabicData.bijOn_cornerGlue`: gluing corner triangulations along an edge.
* `ClusterAlgebras.PlabicData.isCornerTriangle_iff_of_image_eq_cornerGlue`,
  `ClusterAlgebras.PlabicData.isCornerClockwise_cornerMapFst`,
  `ClusterAlgebras.PlabicData.isCornerClockwise_cornerMapSnd`: the triangles of a glued corner
  triangulation, and the corner maps preserve clockwise listings.
* `ClusterAlgebras.PlabicData.IsCrossing.exists_isCornerTriangulation_isCornerTriangle`: a corner
  triangulation with a prescribed ear.
* `ClusterAlgebras.PlabicData.contractEdge_isomorphic_bivalentRemoval`: a contraction at a
  bivalent vertex is a removal.

## Implementation notes

* The darts of the contraction form the subtype `H \ {d, d̄}` of `H`. The corner maps are written
  as maps `H → H`, and a set of pairs of darts of the contraction is compared with
  `κ₁(D₁) ∪ κ₂(D₂) ∪ {γ_e}` through its image under the inclusion; the merged vertex is
  `mergedVertex` read in the subtype.
* FWZ assume `P` plabic and `w₁`, `w₂` white; the statements about corners only use that
  `w₁ ≠ w₂` and that both have at least three darts, and are stated under these hypotheses.
* "`κ_k` maps clockwise listings to clockwise listings" is stated for all listings of darts of
  `w_k`, not only those of triangles.
* The polygon `[0, m - 1]` is `ℤ/m`, with `ι₂(j) = p - 1 + j` computed modulo `m`, so that
  `ι₂(q - 1) = 0`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset TypeA

/-! ### Gluing two polygons along a diagonal -/

section PolygonGlue

private theorem sbtw_iff_val {n : ℕ} [NeZero n] (x y z : ZMod n) :
    sbtw x y z ↔ (x.val < y.val ∧ y.val < z.val) ∨ (y.val < z.val ∧ z.val < x.val) ∨
      (z.val < x.val ∧ x.val < y.val) := by
  match n, ‹NeZero n› with
  | (k + 1), _ => exact Fin.sbtw_iff

private theorem eq_iff_val {n : ℕ} [NeZero n] (x y : ZMod n) : x = y ↔ x.val = y.val :=
  (ZMod.val_injective n).eq_iff.symm

private theorem eq_add_one_iff_val {n : ℕ} [NeZero n] (x y : ZMod n) :
    y = x + 1 ↔ y.val = x.val + 1 ∨ (x.val + 1 = n ∧ y.val = 0) := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have h1 : x + 1 = ((x.val + 1 : ℕ) : ZMod n) := by push_cast; rw [ZMod.natCast_zmod_val]
  rw [h1, eq_iff_val, ZMod.val_natCast]
  rcases Nat.lt_or_ge (x.val + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [show x.val + 1 = n by omega, Nat.mod_self]; omega

private theorem isSide_mk_iff_val {n : ℕ} [NeZero n] (x y : ZMod n) :
    IsSide s(x, y) ↔ (y.val = x.val + 1 ∨ (x.val + 1 = n ∧ y.val = 0)) ∨
      (x.val = y.val + 1 ∨ (y.val + 1 = n ∧ x.val = 0)) := by
  rw [isSide_mk_iff, eq_add_one_iff_val, eq_add_one_iff_val]

private theorem isDiagonal_mk_iff_val {n : ℕ} [NeZero n] (x y : ZMod n) :
    IsDiagonal s(x, y) ↔ x.val ≠ y.val ∧ ¬((y.val = x.val + 1 ∨ (x.val + 1 = n ∧ y.val = 0)) ∨
      (x.val = y.val + 1 ∨ (y.val + 1 = n ∧ x.val = 0))) := by
  rw [IsDiagonal, IsSegment, Sym2.mk_isDiag_iff, isSide_mk_iff_val, eq_iff_val]

private theorem mk_eq_mk_iff_val {n : ℕ} [NeZero n] (x y u v : ZMod n) :
    s(x, y) = s(u, v) ↔ (x.val = u.val ∧ y.val = v.val) ∨ (x.val = v.val ∧ y.val = u.val) := by
  rw [Sym2.eq_iff, eq_iff_val, eq_iff_val, eq_iff_val, eq_iff_val]

private theorem cross_mk_iff_val {n : ℕ} [NeZero n] (u v x y : ZMod n) :
    Cross s(u, v) s(x, y) ↔
      (((u.val < x.val ∧ x.val < v.val) ∨ (x.val < v.val ∧ v.val < u.val) ∨
          (v.val < u.val ∧ u.val < x.val)) ∧
        ((v.val < y.val ∧ y.val < u.val) ∨ (y.val < u.val ∧ u.val < v.val) ∨
          (u.val < v.val ∧ v.val < y.val))) ∨
      (((u.val < y.val ∧ y.val < v.val) ∨ (y.val < v.val ∧ v.val < u.val) ∨
          (v.val < u.val ∧ u.val < y.val)) ∧
        ((v.val < x.val ∧ x.val < u.val) ∨ (x.val < u.val ∧ u.val < v.val) ∨
          (u.val < v.val ∧ v.val < x.val))) := by
  rw [cross_mk_iff, sbtw_iff_val, sbtw_iff_val, sbtw_iff_val, sbtw_iff_val]

/-- The inclusion `i ↦ i` of the vertices `[0, p - 1]` of the `p`-gon into those of the `m`-gon. -/
def polygonGlueFst (m : ℕ) {p : ℕ} (i : ZMod p) : ZMod m := (i.val : ZMod m)

/-- The map `j ↦ p - 1 + j` (modulo `m`) of the vertices `[0, q - 1]` of the `q`-gon into those of
the `m`-gon. -/
def polygonGlueSnd (m p : ℕ) {q : ℕ} (j : ZMod q) : ZMod m := ((p - 1 + j.val : ℕ) : ZMod m)

/-- The diagonal `{0, p - 1}` of the `m`-gon along which a `p`-gon and a `q`-gon are glued. -/
def polygonGlueDiagonal (m p : ℕ) : Sym2 (ZMod m) := s(0, ((p - 1 : ℕ) : ZMod m))

/-- The **glued set of diagonals** `ι₁(T₁) ∪ ι₂(T₂) ∪ {{0, p - 1}}` of the `m`-gon, for sets `T₁`
and `T₂` of diagonals of the `p`-gon and of the `q`-gon. -/
def polygonGlue (m : ℕ) {p q : ℕ} (T₁ : Finset (Sym2 (ZMod p))) (T₂ : Finset (Sym2 (ZMod q))) :
    Finset (Sym2 (ZMod m)) :=
  insert (polygonGlueDiagonal m p)
    (T₁.image (Sym2.map (polygonGlueFst m)) ∪ T₂.image (Sym2.map (polygonGlueSnd m p)))

/-- A diagonal lies in `polygonGlue m T₁ T₂` iff it is `{0, p - 1}`, the image under `ι₁` of an
element of `T₁`, or the image under `ι₂` of an element of `T₂`. -/
theorem mem_polygonGlue {m p q : ℕ} {T₁ : Finset (Sym2 (ZMod p))} {T₂ : Finset (Sym2 (ZMod q))}
    {e : Sym2 (ZMod m)} : e ∈ polygonGlue m T₁ T₂ ↔ e = polygonGlueDiagonal m p ∨
      (∃ a ∈ T₁, a.map (polygonGlueFst m) = e) ∨ ∃ b ∈ T₂, b.map (polygonGlueSnd m p) = e := by
  simp [polygonGlue]

private theorem image_filter_mem_eq {α β : Type*} [Fintype α] [DecidableEq β] {f : α → β}
    {t : Finset β} (h : ∀ x ∈ t, ∃ i, f i = x) : (univ.filter fun i => f i ∈ t).image f = t := by
  ext x
  simp only [mem_image, mem_filter, mem_univ, true_and]
  refine ⟨fun ⟨i, hi, hx⟩ => hx ▸ hi, fun hx => ?_⟩
  obtain ⟨i, rfl⟩ := h x hx
  exact ⟨i, hx, rfl⟩

variable {m p q : ℕ} [NeZero m] [NeZero p] [NeZero q]

omit [NeZero m] [NeZero q] in
private theorem val_polygonGlueFst (hpq : m + 2 = p + q) (hq : 2 ≤ q) (i : ZMod p) :
    (polygonGlueFst m i).val = i.val :=
  ZMod.val_natCast_of_lt (by have := ZMod.val_lt i; omega)

omit [NeZero m] [NeZero p] in
private theorem val_polygonGlueSnd (hpq : m + 2 = p + q) (hp : 1 ≤ p) (j : ZMod q) :
    (polygonGlueSnd m p j).val = if j.val + 1 = q then 0 else p - 1 + j.val := by
  have := ZMod.val_lt j
  unfold polygonGlueSnd
  rw [ZMod.val_natCast]
  split_ifs with h
  · rw [show p - 1 + j.val = m by omega, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

omit [NeZero m] [NeZero p] in
private theorem val_polygonGlueSnd_cases (hpq : m + 2 = p + q) (hp : 1 ≤ p) (j : ZMod q) :
    (j.val + 1 = q ∧ (polygonGlueSnd m p j).val = 0) ∨
      (j.val + 1 < q ∧ (polygonGlueSnd m p j).val = p - 1 + j.val) := by
  have := ZMod.val_lt j
  rw [val_polygonGlueSnd hpq hp]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

omit [NeZero m] [NeZero q] in
private theorem val_natCast_pred (hpq : m + 2 = p + q) (hq : 2 ≤ q) :
    ((p - 1 : ℕ) : ZMod m).val = p - 1 :=
  ZMod.val_natCast_of_lt (by have := NeZero.ne p; omega)

variable (hpq : m + 2 = p + q) (hp : 3 ≤ p) (hq : 3 ≤ q)

include hpq hp hq

omit hp [NeZero q] in
private theorem sbtw_polygonGlueFst_iff (a b c : ZMod p) :
    sbtw (polygonGlueFst m a) (polygonGlueFst m b) (polygonGlueFst m c) ↔ sbtw a b c := by
  rw [sbtw_iff_val, sbtw_iff_val, val_polygonGlueFst hpq (by omega),
    val_polygonGlueFst hpq (by omega), val_polygonGlueFst hpq (by omega)]

omit hq [NeZero p] in
private theorem sbtw_polygonGlueSnd_iff (a b c : ZMod q) :
    sbtw (polygonGlueSnd m p a) (polygonGlueSnd m p b) (polygonGlueSnd m p c) ↔ sbtw a b c := by
  rw [sbtw_iff_val, sbtw_iff_val]
  have := val_polygonGlueSnd_cases hpq (by omega) a
  have := val_polygonGlueSnd_cases hpq (by omega) b
  have := val_polygonGlueSnd_cases hpq (by omega) c
  omega

omit hp [NeZero q] in
private theorem polygonGlueFst_injective :
    Function.Injective (polygonGlueFst m : ZMod p → ZMod m) :=
  fun a b h => by
    rw [eq_iff_val, val_polygonGlueFst hpq (by omega), val_polygonGlueFst hpq (by omega)] at h
    exact (eq_iff_val a b).2 h

omit hq [NeZero p] in
private theorem polygonGlueSnd_injective :
    Function.Injective (polygonGlueSnd m p : ZMod q → ZMod m) := fun a b h => by
  rw [eq_iff_val] at h
  have := val_polygonGlueSnd_cases hpq (by omega) a
  have := val_polygonGlueSnd_cases hpq (by omega) b
  refine (eq_iff_val a b).2 ?_
  omega

omit hp [NeZero q] in
private theorem cross_polygonGlueFst_iff (e f : Sym2 (ZMod p)) :
    Cross (e.map (polygonGlueFst m)) (f.map (polygonGlueFst m)) ↔ Cross e f := by
  induction e using Sym2.ind with | _ x y => ?_
  induction f using Sym2.ind with | _ u v => ?_
  simp only [Sym2.map_mk, cross_mk_iff, sbtw_polygonGlueFst_iff hpq hq]

omit hq [NeZero p] in
private theorem cross_polygonGlueSnd_iff (e f : Sym2 (ZMod q)) :
    Cross (e.map (polygonGlueSnd m p)) (f.map (polygonGlueSnd m p)) ↔ Cross e f := by
  induction e using Sym2.ind with | _ x y => ?_
  induction f using Sym2.ind with | _ u v => ?_
  simp only [Sym2.map_mk, cross_mk_iff, sbtw_polygonGlueSnd_iff hpq hp]

private theorem not_cross_polygonGlueFst_polygonGlueSnd (e : Sym2 (ZMod p)) (f : Sym2 (ZMod q)) :
    ¬Cross (e.map (polygonGlueFst m)) (f.map (polygonGlueSnd m p)) := by
  induction e using Sym2.ind with | _ x y => ?_
  induction f using Sym2.ind with | _ u v => ?_
  rw [Sym2.map_mk, Sym2.map_mk, cross_mk_iff_val, val_polygonGlueFst hpq (by omega),
    val_polygonGlueFst hpq (by omega)]
  have := ZMod.val_lt x
  have := ZMod.val_lt y
  have := val_polygonGlueSnd_cases hpq (by omega) u
  have := val_polygonGlueSnd_cases hpq (by omega) v
  omega

omit [NeZero q] in
private theorem not_cross_polygonGlueDiagonal_fst (e : Sym2 (ZMod p)) :
    ¬Cross (polygonGlueDiagonal m p) (e.map (polygonGlueFst m)) := by
  induction e using Sym2.ind with | _ x y => ?_
  rw [polygonGlueDiagonal, Sym2.map_mk, cross_mk_iff_val, val_polygonGlueFst hpq (by omega),
    val_polygonGlueFst hpq (by omega), val_natCast_pred hpq (by omega), ZMod.val_zero]
  have := ZMod.val_lt x
  have := ZMod.val_lt y
  omega

private theorem not_cross_polygonGlueDiagonal_snd (f : Sym2 (ZMod q)) :
    ¬Cross (polygonGlueDiagonal m p) (f.map (polygonGlueSnd m p)) := by
  induction f using Sym2.ind with | _ x y => ?_
  rw [polygonGlueDiagonal, Sym2.map_mk, cross_mk_iff_val, val_natCast_pred hpq (by omega),
    ZMod.val_zero]
  have := val_polygonGlueSnd_cases hpq (by omega) x
  have := val_polygonGlueSnd_cases hpq (by omega) y
  omega

omit [NeZero q] in
private theorem isDiagonal_polygonGlueDiagonal : IsDiagonal (polygonGlueDiagonal m p) := by
  rw [polygonGlueDiagonal, isDiagonal_mk_iff_val, val_natCast_pred hpq (by omega), ZMod.val_zero]
  omega

omit [NeZero q] in
private theorem isDiagonal_map_polygonGlueFst {e : Sym2 (ZMod p)} (he : IsDiagonal e) :
    IsDiagonal (e.map (polygonGlueFst m)) ∧
      e.map (polygonGlueFst m) ≠ polygonGlueDiagonal m p := by
  induction e using Sym2.ind with | _ x y => ?_
  rw [isDiagonal_mk_iff_val] at he
  rw [polygonGlueDiagonal, Sym2.map_mk, ne_eq, mk_eq_mk_iff_val, isDiagonal_mk_iff_val,
    val_polygonGlueFst hpq (by omega), val_polygonGlueFst hpq (by omega),
    val_natCast_pred hpq (by omega), ZMod.val_zero]
  have := ZMod.val_lt x
  have := ZMod.val_lt y
  omega

private theorem isDiagonal_map_polygonGlueSnd {f : Sym2 (ZMod q)} (hf : IsDiagonal f) :
    IsDiagonal (f.map (polygonGlueSnd m p)) ∧
      f.map (polygonGlueSnd m p) ≠ polygonGlueDiagonal m p := by
  induction f using Sym2.ind with | _ x y => ?_
  rw [isDiagonal_mk_iff_val] at hf
  rw [polygonGlueDiagonal, Sym2.map_mk, ne_eq, mk_eq_mk_iff_val, isDiagonal_mk_iff_val,
    val_natCast_pred hpq (by omega), ZMod.val_zero]
  have := val_polygonGlueSnd_cases hpq (by omega) x
  have := val_polygonGlueSnd_cases hpq (by omega) y
  omega

/-- A segment of the `p`-gon and one of the `q`-gon have the same image only along the glued
diagonal. -/
private theorem map_polygonGlueFst_eq_polygonGlueDiagonal {e : Sym2 (ZMod p)} {f : Sym2 (ZMod q)}
    (he : ¬e.IsDiag) (h : e.map (polygonGlueFst m) = f.map (polygonGlueSnd m p)) :
    e.map (polygonGlueFst m) = polygonGlueDiagonal m p := by
  induction e using Sym2.ind with | _ x y => ?_
  induction f using Sym2.ind with | _ u v => ?_
  rw [Sym2.mk_isDiag_iff, eq_iff_val] at he
  rw [Sym2.map_mk, Sym2.map_mk, mk_eq_mk_iff_val, val_polygonGlueFst hpq (by omega),
    val_polygonGlueFst hpq (by omega)] at h
  rw [polygonGlueDiagonal, Sym2.map_mk, mk_eq_mk_iff_val, val_polygonGlueFst hpq (by omega),
    val_polygonGlueFst hpq (by omega), val_natCast_pred hpq (by omega), ZMod.val_zero]
  have := ZMod.val_lt x
  have := ZMod.val_lt y
  have := val_polygonGlueSnd_cases hpq (by omega) u
  have := val_polygonGlueSnd_cases hpq (by omega) v
  omega

omit hp [NeZero q] in
private theorem exists_polygonGlueFst_eq {x : ZMod m} (hx : x.val ≤ p - 1) :
    ∃ i : ZMod p, polygonGlueFst m i = x := by
  have hp0 : p ≠ 0 := NeZero.ne p
  refine ⟨(x.val : ZMod p), ?_⟩
  have h1 : ((x.val : ℕ) : ZMod p).val = x.val := ZMod.val_natCast_of_lt (by omega)
  rw [eq_iff_val, val_polygonGlueFst hpq (by omega), h1]

omit [NeZero p] in
private theorem exists_polygonGlueSnd_eq {x : ZMod m} (hx : p - 1 ≤ x.val ∨ x.val = 0) :
    ∃ j : ZMod q, polygonGlueSnd m p j = x := by
  have := ZMod.val_lt x
  rcases hx with hx | hx
  · refine ⟨((x.val - (p - 1) : ℕ) : ZMod q), ?_⟩
    have h1 : ((x.val - (p - 1) : ℕ) : ZMod q).val = x.val - (p - 1) :=
      ZMod.val_natCast_of_lt (by omega)
    rw [eq_iff_val]
    have := val_polygonGlueSnd_cases hpq (by omega) (((x.val - (p - 1) : ℕ) : ZMod q))
    rw [h1] at this
    omega
  · refine ⟨((q - 1 : ℕ) : ZMod q), ?_⟩
    have h1 : ((q - 1 : ℕ) : ZMod q).val = q - 1 := ZMod.val_natCast_of_lt (by omega)
    rw [eq_iff_val]
    have := val_polygonGlueSnd_cases hpq (by omega) (((q - 1 : ℕ) : ZMod q))
    rw [h1] at this
    omega

/-- **Trichotomy**: a diagonal of the `m`-gon other than `{0, p - 1}` and not crossing it is the
image of a diagonal of the `p`-gon or of the `q`-gon. -/
private theorem polygonGlue_trichotomy {δ : Sym2 (ZMod m)} (hδ : IsDiagonal δ)
    (hγ : δ ≠ polygonGlueDiagonal m p) (hc : ¬Cross δ (polygonGlueDiagonal m p)) :
    (∃ e : Sym2 (ZMod p), IsDiagonal e ∧ e.map (polygonGlueFst m) = δ) ∨
      ∃ f : Sym2 (ZMod q), IsDiagonal f ∧ f.map (polygonGlueSnd m p) = δ := by
  induction δ using Sym2.ind with | _ x y => ?_
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  rw [isDiagonal_mk_iff_val] at hδ
  rw [polygonGlueDiagonal, ne_eq, mk_eq_mk_iff_val, val_natCast_pred hpq (by omega),
    ZMod.val_zero] at hγ
  rw [polygonGlueDiagonal, cross_mk_iff_val, val_natCast_pred hpq (by omega),
    ZMod.val_zero] at hc
  have hreg : (x.val ≤ p - 1 ∧ y.val ≤ p - 1) ∨
      ((p - 1 ≤ x.val ∨ x.val = 0) ∧ (p - 1 ≤ y.val ∨ y.val = 0)) := by omega
  clear hc
  rcases hreg with h1 | h1
  · left
    obtain ⟨i, hi⟩ := exists_polygonGlueFst_eq hpq hq h1.1
    obtain ⟨j, hj⟩ := exists_polygonGlueFst_eq hpq hq h1.2
    have hi' : i.val = x.val := by rw [← hi, val_polygonGlueFst hpq (by omega)]
    have hj' : j.val = y.val := by rw [← hj, val_polygonGlueFst hpq (by omega)]
    refine ⟨s(i, j), ?_, by rw [Sym2.map_mk, hi, hj]⟩
    rw [isDiagonal_mk_iff_val]
    omega
  · right
    obtain ⟨i, hi⟩ := exists_polygonGlueSnd_eq hpq hp hq h1.1
    obtain ⟨j, hj⟩ := exists_polygonGlueSnd_eq hpq hp hq h1.2
    have hi' := congrArg ZMod.val hi
    have hj' := congrArg ZMod.val hj
    refine ⟨s(i, j), ?_, by rw [Sym2.map_mk, hi, hj]⟩
    rw [isDiagonal_mk_iff_val]
    have := val_polygonGlueSnd_cases hpq (by omega) i
    have := val_polygonGlueSnd_cases hpq (by omega) j
    omega

/-- **Gluing triangulations.** If `T₁` and `T₂` are triangulations of the `p`-gon and of the
`q`-gon, `m + 2 = p + q`, then `ι₁(T₁) ∪ ι₂(T₂) ∪ {{0, p - 1}}` is a triangulation of the
`m`-gon. -/
theorem isTriangulation_polygonGlue {T₁ : Finset (Sym2 (ZMod p))} {T₂ : Finset (Sym2 (ZMod q))}
    (hT₁ : IsTriangulation T₁) (hT₂ : IsTriangulation T₂) :
    IsTriangulation (polygonGlue m T₁ T₂) := by
  refine ⟨fun e he => ?_, fun e he f hf => ?_, fun δ hδ hδT => ?_⟩
  · rcases mem_polygonGlue.1 he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact isDiagonal_polygonGlueDiagonal hpq hp hq
    · exact (isDiagonal_map_polygonGlueFst hpq hp hq (hT₁.isDiagonal a ha)).1
    · exact (isDiagonal_map_polygonGlueSnd hpq hp hq (hT₂.isDiagonal b hb)).1
  · rcases mem_polygonGlue.1 he with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;>
      rcases mem_polygonGlue.1 hf with rfl | ⟨a', ha', rfl⟩ | ⟨b', hb', rfl⟩
    · exact not_cross_self _
    · exact not_cross_polygonGlueDiagonal_fst hpq hp hq a'
    · exact not_cross_polygonGlueDiagonal_snd hpq hp hq b'
    · exact fun h => not_cross_polygonGlueDiagonal_fst hpq hp hq a h.symm
    · rw [cross_polygonGlueFst_iff hpq hq]
      exact hT₁.noncrossing a ha a' ha'
    · exact not_cross_polygonGlueFst_polygonGlueSnd hpq hp hq a b'
    · exact fun h => not_cross_polygonGlueDiagonal_snd hpq hp hq b h.symm
    · exact fun h => not_cross_polygonGlueFst_polygonGlueSnd hpq hp hq a' b h.symm
    · rw [cross_polygonGlueSnd_iff hpq hp]
      exact hT₂.noncrossing b hb b' hb'
  · by_cases hc : Cross δ (polygonGlueDiagonal m p)
    · exact ⟨_, mem_insert_self _ _, hc⟩
    have hne : δ ≠ polygonGlueDiagonal m p := fun h => hδT (h ▸ mem_insert_self _ _)
    rcases polygonGlue_trichotomy hpq hp hq hδ hne hc with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · have haT : a ∉ T₁ := fun h => hδT (mem_polygonGlue.2 (Or.inr (Or.inl ⟨a, h, rfl⟩)))
      obtain ⟨f, hf, haf⟩ := hT₁.maximal a ha haT
      exact ⟨f.map (polygonGlueFst m), mem_polygonGlue.2 (Or.inr (Or.inl ⟨f, hf, rfl⟩)),
        (cross_polygonGlueFst_iff hpq hq a f).2 haf⟩
    · have hbT : b ∉ T₂ := fun h => hδT (mem_polygonGlue.2 (Or.inr (Or.inr ⟨b, h, rfl⟩)))
      obtain ⟨f, hf, hbf⟩ := hT₂.maximal b hb hbT
      exact ⟨f.map (polygonGlueSnd m p), mem_polygonGlue.2 (Or.inr (Or.inr ⟨f, hf, rfl⟩)),
        (cross_polygonGlueSnd_iff hpq hp b f).2 hbf⟩

private theorem map_polygonGlueFst_mem_polygonGlue_iff {T₁ : Finset (Sym2 (ZMod p))}
    {T₂ : Finset (Sym2 (ZMod q))} {a : Sym2 (ZMod p)}
    (ha : IsDiagonal a) : a.map (polygonGlueFst m) ∈ polygonGlue m T₁ T₂ ↔ a ∈ T₁ := by
  refine ⟨fun h => ?_, fun h => mem_polygonGlue.2 (Or.inr (Or.inl ⟨a, h, rfl⟩))⟩
  have hdg := isDiagonal_map_polygonGlueFst hpq hp hq ha
  rcases mem_polygonGlue.1 h with h | ⟨a', ha', h⟩ | ⟨b, hb, h⟩
  · exact absurd h hdg.2
  · rwa [← Sym2.map.injective (polygonGlueFst_injective hpq hq) h]
  · exact absurd (map_polygonGlueFst_eq_polygonGlueDiagonal hpq hp hq ha.1 h.symm) hdg.2

private theorem map_polygonGlueSnd_mem_polygonGlue_iff {T₁ : Finset (Sym2 (ZMod p))}
    {T₂ : Finset (Sym2 (ZMod q))} (hT₁ : ∀ a ∈ T₁, IsDiagonal a) {b : Sym2 (ZMod q)}
    (hb : IsDiagonal b) : b.map (polygonGlueSnd m p) ∈ polygonGlue m T₁ T₂ ↔ b ∈ T₂ := by
  refine ⟨fun h => ?_, fun h => mem_polygonGlue.2 (Or.inr (Or.inr ⟨b, h, rfl⟩))⟩
  rcases mem_polygonGlue.1 h with h | ⟨a, ha, h⟩ | ⟨b', hb', h⟩
  · exact absurd h (isDiagonal_map_polygonGlueSnd hpq hp hq hb).2
  · exact absurd (map_polygonGlueFst_eq_polygonGlueDiagonal hpq hp hq (hT₁ a ha).1 h)
      (isDiagonal_map_polygonGlueFst hpq hp hq (hT₁ a ha)).2
  · rwa [← Sym2.map.injective (polygonGlueSnd_injective hpq hp) h]

/-- **Gluing triangulations is a bijection.** For `m + 2 = p + q` with `p, q ≥ 3`, the map
`(T₁, T₂) ↦ ι₁(T₁) ∪ ι₂(T₂) ∪ {{0, p - 1}}` is a bijection from pairs of triangulations of the
`p`-gon and of the `q`-gon onto the triangulations of the `m`-gon containing `{0, p - 1}`. -/
theorem bijOn_polygonGlue :
    Set.BijOn (fun T : Finset (Sym2 (ZMod p)) × Finset (Sym2 (ZMod q)) => polygonGlue m T.1 T.2)
      {T | IsTriangulation T.1 ∧ IsTriangulation T.2}
      {T | IsTriangulation T ∧ polygonGlueDiagonal m p ∈ T} := by
  refine ⟨fun T hT => ⟨isTriangulation_polygonGlue hpq hp hq hT.1 hT.2, mem_insert_self _ _⟩,
    fun T hT T' hT' h => ?_, fun T hT => ?_⟩
  · have h' : polygonGlue m T.1 T.2 = polygonGlue m T'.1 T'.2 := h
    refine Prod.ext (Finset.ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩)
      (Finset.ext fun b => ⟨fun hb => ?_, fun hb => ?_⟩)
    · have hd := hT.1.isDiagonal a ha
      rw [← map_polygonGlueFst_mem_polygonGlue_iff hpq hp hq (T₂ := T'.2) hd, ← h',
        map_polygonGlueFst_mem_polygonGlue_iff hpq hp hq (T₂ := T.2) hd]
      exact ha
    · have hd := hT'.1.isDiagonal a ha
      rw [← map_polygonGlueFst_mem_polygonGlue_iff hpq hp hq (T₂ := T.2) hd, h',
        map_polygonGlueFst_mem_polygonGlue_iff hpq hp hq (T₂ := T'.2) hd]
      exact ha
    · have hd := hT.2.isDiagonal b hb
      rw [← map_polygonGlueSnd_mem_polygonGlue_iff hpq hp hq hT'.1.isDiagonal hd, ← h',
        map_polygonGlueSnd_mem_polygonGlue_iff hpq hp hq hT.1.isDiagonal hd]
      exact hb
    · have hd := hT'.2.isDiagonal b hb
      rw [← map_polygonGlueSnd_mem_polygonGlue_iff hpq hp hq hT.1.isDiagonal hd, h',
        map_polygonGlueSnd_mem_polygonGlue_iff hpq hp hq hT'.1.isDiagonal hd]
      exact hb
  · obtain ⟨hT, hγ⟩ := hT
    set T₁ : Finset (Sym2 (ZMod p)) :=
      univ.filter fun a => IsDiagonal a ∧ a.map (polygonGlueFst m) ∈ T with hT₁
    set T₂ : Finset (Sym2 (ZMod q)) :=
      univ.filter fun b => IsDiagonal b ∧ b.map (polygonGlueSnd m p) ∈ T with hT₂
    have mem₁ : ∀ a, a ∈ T₁ ↔ IsDiagonal a ∧ a.map (polygonGlueFst m) ∈ T := fun a => by
      simp [hT₁]
    have mem₂ : ∀ b, b ∈ T₂ ↔ IsDiagonal b ∧ b.map (polygonGlueSnd m p) ∈ T := fun b => by
      simp [hT₂]
    have split : ∀ ε ∈ T, ε ≠ polygonGlueDiagonal m p →
        (∃ a ∈ T₁, a.map (polygonGlueFst m) = ε) ∨ ∃ b ∈ T₂, b.map (polygonGlueSnd m p) = ε := by
      intro ε hε hne
      rcases polygonGlue_trichotomy hpq hp hq (hT.isDiagonal ε hε) hne
          (hT.noncrossing ε hε _ hγ) with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact Or.inl ⟨a, (mem₁ a).2 ⟨ha, hε⟩, rfl⟩
      · exact Or.inr ⟨b, (mem₂ b).2 ⟨hb, hε⟩, rfl⟩
    have hT₁t : IsTriangulation T₁ := by
      refine ⟨fun a ha => ((mem₁ a).1 ha).1, fun a ha a' ha' h => ?_, fun a ha haT => ?_⟩
      · exact hT.noncrossing _ ((mem₁ a).1 ha).2 _ ((mem₁ a').1 ha').2
          ((cross_polygonGlueFst_iff hpq hq a a').2 h)
      · have hd := isDiagonal_map_polygonGlueFst hpq hp hq ha
        obtain ⟨ε, hε, hc⟩ := hT.maximal _ hd.1 fun h => haT ((mem₁ a).2 ⟨ha, h⟩)
        have hne : ε ≠ polygonGlueDiagonal m p := by
          rintro rfl
          exact not_cross_polygonGlueDiagonal_fst hpq hp hq a hc.symm
        rcases split ε hε hne with ⟨a', ha', rfl⟩ | ⟨b, -, rfl⟩
        · exact ⟨a', ha', (cross_polygonGlueFst_iff hpq hq a a').1 hc⟩
        · exact absurd hc (not_cross_polygonGlueFst_polygonGlueSnd hpq hp hq a b)
    have hT₂t : IsTriangulation T₂ := by
      refine ⟨fun b hb => ((mem₂ b).1 hb).1, fun b hb b' hb' h => ?_, fun b hb hbT => ?_⟩
      · exact hT.noncrossing _ ((mem₂ b).1 hb).2 _ ((mem₂ b').1 hb').2
          ((cross_polygonGlueSnd_iff hpq hp b b').2 h)
      · have hd := isDiagonal_map_polygonGlueSnd hpq hp hq hb
        obtain ⟨ε, hε, hc⟩ := hT.maximal _ hd.1 fun h => hbT ((mem₂ b).2 ⟨hb, h⟩)
        have hne : ε ≠ polygonGlueDiagonal m p := by
          rintro rfl
          exact not_cross_polygonGlueDiagonal_snd hpq hp hq b hc.symm
        rcases split ε hε hne with ⟨a, -, rfl⟩ | ⟨b', hb', rfl⟩
        · exact absurd hc.symm (not_cross_polygonGlueFst_polygonGlueSnd hpq hp hq a b)
        · exact ⟨b', hb', (cross_polygonGlueSnd_iff hpq hp b b').1 hc⟩
    refine ⟨(T₁, T₂), ⟨hT₁t, hT₂t⟩, Finset.ext fun δ => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rcases mem_polygonGlue.1 h with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      exacts [hγ, ((mem₁ a).1 ha).2, ((mem₂ b).1 hb).2]
    · by_cases hne : δ = polygonGlueDiagonal m p
      · exact hne ▸ mem_insert_self _ _
      rcases split δ h hne with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact mem_polygonGlue.2 (Or.inr (Or.inl ⟨a, ha, rfl⟩))
      · exact mem_polygonGlue.2 (Or.inr (Or.inr ⟨b, hb, rfl⟩))


/-! #### Triangles of a glued triangulation -/

omit [NeZero q] in
private theorem isSide_map_polygonGlueFst_iff (x y : ZMod p) :
    (IsSide s(polygonGlueFst m x, polygonGlueFst m y) ∨
      s(polygonGlueFst m x, polygonGlueFst m y) = polygonGlueDiagonal m p) ↔ IsSide s(x, y) := by
  rw [isSide_mk_iff_val, isSide_mk_iff_val, polygonGlueDiagonal, mk_eq_mk_iff_val,
    val_polygonGlueFst hpq (by omega), val_polygonGlueFst hpq (by omega),
    val_natCast_pred hpq (by omega), ZMod.val_zero]
  have := ZMod.val_lt x
  have := ZMod.val_lt y
  omega

private theorem isSide_map_polygonGlueSnd_iff (x y : ZMod q) :
    (IsSide s(polygonGlueSnd m p x, polygonGlueSnd m p y) ∨
      s(polygonGlueSnd m p x, polygonGlueSnd m p y) = polygonGlueDiagonal m p) ↔
      IsSide s(x, y) := by
  rw [isSide_mk_iff_val, isSide_mk_iff_val, polygonGlueDiagonal, mk_eq_mk_iff_val,
    val_natCast_pred hpq (by omega), ZMod.val_zero]
  have := val_polygonGlueSnd_cases hpq (by omega) x
  have := val_polygonGlueSnd_cases hpq (by omega) y
  omega

private theorem mk_mem_segments_polygonGlue_fst_iff {T₁ : Finset (Sym2 (ZMod p))}
    {T₂ : Finset (Sym2 (ZMod q))} {x y : ZMod p} (hxy : x ≠ y) :
    s(polygonGlueFst m x, polygonGlueFst m y) ∈ segments (polygonGlue m T₁ T₂) ↔
      s(x, y) ∈ segments T₁ := by
  have hside := isSide_map_polygonGlueFst_iff hpq hp hq x y
  rw [mem_segments, mem_segments, mem_polygonGlue]
  constructor
  · rintro ((h | ⟨a, ha, h⟩ | ⟨c, -, h⟩) | h)
    · exact Or.inr (hside.1 (Or.inr h))
    · left
      rwa [← Sym2.map.injective (polygonGlueFst_injective hpq hq)
        (show Sym2.map (polygonGlueFst m) a = Sym2.map (polygonGlueFst m) s(x, y) from h)]
    · have := map_polygonGlueFst_eq_polygonGlueDiagonal hpq hp hq (e := s(x, y))
        (fun h' => hxy (Sym2.mk_isDiag_iff.1 h')) h.symm
      exact Or.inr (hside.1 (Or.inr this))
    · exact Or.inr (hside.1 (Or.inl h))
  · rintro (h | h)
    · exact Or.inl (Or.inr (Or.inl ⟨_, h, rfl⟩))
    · rcases hside.2 h with h | h
      · exact Or.inr h
      · exact Or.inl (Or.inl h)

private theorem mk_mem_segments_polygonGlue_snd_iff {T₁ : Finset (Sym2 (ZMod p))}
    {T₂ : Finset (Sym2 (ZMod q))} (hT₁ : ∀ a ∈ T₁, IsDiagonal a) {x y : ZMod q} :
    s(polygonGlueSnd m p x, polygonGlueSnd m p y) ∈ segments (polygonGlue m T₁ T₂) ↔
      s(x, y) ∈ segments T₂ := by
  have hside := isSide_map_polygonGlueSnd_iff hpq hp hq x y
  rw [mem_segments, mem_segments, mem_polygonGlue]
  constructor
  · rintro ((h | ⟨a, ha, h⟩ | ⟨c, hc, h⟩) | h)
    · exact Or.inr (hside.1 (Or.inr h))
    · have := map_polygonGlueFst_eq_polygonGlueDiagonal hpq hp hq (hT₁ a ha).1 (e := a)
        (f := s(x, y)) h
      exact absurd this (isDiagonal_map_polygonGlueFst hpq hp hq (hT₁ a ha)).2
    · left
      rwa [← Sym2.map.injective (polygonGlueSnd_injective hpq hp)
        (show Sym2.map (polygonGlueSnd m p) c = Sym2.map (polygonGlueSnd m p) s(x, y) from h)]
    · exact Or.inr (hside.1 (Or.inl h))
  · rintro (h | h)
    · exact Or.inl (Or.inr (Or.inr ⟨_, h, rfl⟩))
    · rcases hside.2 h with h | h
      · exact Or.inr h
      · exact Or.inl (Or.inl h)

/-- A triangle of a glued triangulation lies on one side of the glued diagonal. -/
private theorem polygonGlue_triangle_side {T₁ : Finset (Sym2 (ZMod p))}
    {T₂ : Finset (Sym2 (ZMod q))} (hT₁ : IsTriangulation T₁) (hT₂ : IsTriangulation T₂)
    {t : Finset (ZMod m)} (ht : IsTriangle (polygonGlue m T₁ T₂) t) :
    (∀ x ∈ t, x.val ≤ p - 1) ∨ ∀ x ∈ t, p - 1 ≤ x.val ∨ x.val = 0 := by
  by_contra h
  push Not at h
  obtain ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy', hy0⟩⟩ := h
  have hxy : x ≠ y := by rintro rfl; omega
  have hT := isTriangulation_polygonGlue hpq hp hq hT₁ hT₂
  have hγ : polygonGlueDiagonal m p ∈ segments (polygonGlue m T₁ T₂) :=
    mem_segments.2 (Or.inl (mem_insert_self _ _))
  apply IsTriangulation.not_cross hT (ht.2 x hx y hy hxy) hγ
  rw [polygonGlueDiagonal, cross_mk_iff_val, val_natCast_pred hpq (by omega), ZMod.val_zero]
  have := ZMod.val_lt x
  omega

/-- **The triangles of a glued triangulation.** The triangles of `ι₁(T₁) ∪ ι₂(T₂) ∪ {{0, p - 1}}`
are the images of the triangles of `T₁` under `ι₁` and those of the triangles of `T₂` under
`ι₂`. -/
theorem isTriangle_polygonGlue_iff {T₁ : Finset (Sym2 (ZMod p))} {T₂ : Finset (Sym2 (ZMod q))}
    (hT₁ : IsTriangulation T₁) (hT₂ : IsTriangulation T₂) (t : Finset (ZMod m)) :
    IsTriangle (polygonGlue m T₁ T₂) t ↔
      (∃ τ, IsTriangle T₁ τ ∧ τ.image (polygonGlueFst m) = t) ∨
        ∃ τ, IsTriangle T₂ τ ∧ τ.image (polygonGlueSnd m p) = t := by
  have inj₁ := polygonGlueFst_injective hpq hq (m := m) (p := p)
  have inj₂ := polygonGlueSnd_injective hpq hp (m := m) (q := q)
  constructor
  · intro ht
    rcases polygonGlue_triangle_side hpq hp hq hT₁ hT₂ ht with h | h
    · left
      have himg := image_filter_mem_eq fun x hx => exists_polygonGlueFst_eq hpq hq (h x hx)
      refine ⟨_, ⟨?_, fun u hu v hv huv => ?_⟩, himg⟩
      · rw [← card_image_of_injective _ inj₁, himg, ht.1]
      · simp only [mem_filter, mem_univ, true_and] at hu hv
        exact (mk_mem_segments_polygonGlue_fst_iff hpq hp hq huv).1
          (ht.2 _ hu _ hv (inj₁.ne huv))
    · right
      have himg := image_filter_mem_eq fun x hx => exists_polygonGlueSnd_eq hpq hp hq (h x hx)
      refine ⟨_, ⟨?_, fun u hu v hv huv => ?_⟩, himg⟩
      · rw [← card_image_of_injective _ inj₂, himg, ht.1]
      · simp only [mem_filter, mem_univ, true_and] at hu hv
        exact (mk_mem_segments_polygonGlue_snd_iff hpq hp hq hT₁.isDiagonal).1
          (ht.2 _ hu _ hv (inj₂.ne huv))
  · rintro (⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl⟩)
    · refine ⟨by rw [card_image_of_injective _ inj₁, hτ.1], fun u hu v hv huv => ?_⟩
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hu
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hv
      have hij : i ≠ j := fun h => huv (h ▸ rfl)
      exact (mk_mem_segments_polygonGlue_fst_iff hpq hp hq hij).2 (hτ.2 i hi j hj hij)
    · refine ⟨by rw [card_image_of_injective _ inj₂, hτ.1], fun u hu v hv huv => ?_⟩
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hu
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hv
      have hij : i ≠ j := fun h => huv (h ▸ rfl)
      exact (mk_mem_segments_polygonGlue_snd_iff hpq hp hq hT₁.isDiagonal).2 (hτ.2 i hi j hj hij)

end PolygonGlue

/-! ### Orbits of a permutation -/

section Orbit

variable {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) (x : α)

private theorem pow_apply_injective_of_lt_card {i j : ℕ}
    (hi : i < (univ.filter (g.SameCycle x)).card) (hj : j < (univ.filter (g.SameCycle x)).card)
    (h : (g ^ i) x = (g ^ j) x) : i = j := by
  wlog hij : i < j generalizing i j
  · rcases Nat.lt_or_ge j i with h' | h'
    · exact (this hj hi h.symm h').symm
    · omega
  have hper : (g ^ (j - i)) ((g ^ i) x) = (g ^ i) x := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hij.le]
    exact h.symm
  have hsub : univ.filter (g.SameCycle x) ⊆
      (range (j - i)).image fun k => (g ^ k) ((g ^ i) x) := by
    intro y hy
    have hy' : g.SameCycle ((g ^ i) x) y :=
      Equiv.Perm.sameCycle_pow_left.2 (mem_filter.1 hy).2
    obtain ⟨N, hN⟩ := hy'.exists_nat_pow_eq
    have hpp : Function.IsPeriodicPt g (j - i) ((g ^ i) x) := by
      change (⇑g)^[j - i] _ = _
      rw [Equiv.Perm.iterate_eq_pow, hper]
    have hmod := hpp.iterate_mod_apply N
    rw [Equiv.Perm.iterate_eq_pow, Equiv.Perm.iterate_eq_pow] at hmod
    exact mem_image.2 ⟨N % (j - i), mem_range.2 (Nat.mod_lt _ (by omega)), hmod.trans hN⟩
  have := (card_le_card hsub).trans card_image_le
  rw [card_range] at this
  omega

private theorem exists_pow_apply_eq_of_lt_card {y : α} (hy : g.SameCycle x y) :
    ∃ k < (univ.filter (g.SameCycle x)).card, (g ^ k) x = y := by
  have hsub : (range (univ.filter (g.SameCycle x)).card).image (fun k => (g ^ k) x) ⊆
      univ.filter (g.SameCycle x) := by
    intro z hz
    obtain ⟨k, -, rfl⟩ := mem_image.1 hz
    exact mem_filter.2 ⟨mem_univ _, Equiv.Perm.sameCycle_pow_right.2 (.refl _ _)⟩
  have hcard : ((range (univ.filter (g.SameCycle x)).card).image (fun k => (g ^ k) x)).card =
      (univ.filter (g.SameCycle x)).card := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    exact pow_apply_injective_of_lt_card g x (mem_range.1 hi) (mem_range.1 hj) h
  have heq := eq_of_subset_of_card_le hsub (by rw [hcard])
  have hmem : y ∈ univ.filter (g.SameCycle x) := mem_filter.2 ⟨mem_univ _, hy⟩
  rw [← heq] at hmem
  obtain ⟨k, hk, rfl⟩ := mem_image.1 hmem
  exact ⟨k, mem_range.1 hk, rfl⟩

private theorem pow_card_filter_sameCycle_apply :
    (g ^ (univ.filter (g.SameCycle x)).card) x = x := by
  have hpos : 0 < (univ.filter (g.SameCycle x)).card :=
    card_pos.2 ⟨x, mem_filter.2 ⟨mem_univ _, .refl _ _⟩⟩
  obtain ⟨k, hk, hkx⟩ := exists_pow_apply_eq_of_lt_card g x
    (Equiv.Perm.sameCycle_pow_right.2 (.refl g x) :
      g.SameCycle x ((g ^ (univ.filter (g.SameCycle x)).card) x))
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [← hkx, pow_zero, Equiv.Perm.one_apply]
  · exfalso
    have h1 : (g ^ ((univ.filter (g.SameCycle x)).card - k)) x = (g ^ 0) x := by
      apply (g ^ k).injective
      rw [show (g ^ k) ((g ^ ((univ.filter (g.SameCycle x)).card - k)) x) =
          (g ^ (univ.filter (g.SameCycle x)).card) x by
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hk.le], pow_zero,
        Equiv.Perm.one_apply, hkx]
    have := pow_apply_injective_of_lt_card g x (by omega) hpos h1
    omega

end Orbit

/-! ### Corner labellings from the rotation -/

namespace RotationSystem

variable {H : Type*} [Fintype H] [DecidableEq H] {R : RotationSystem H}

private theorem vertexOf_eq_filter_rot_symm (x : H) :
    R.vertexOf x = univ.filter (Equiv.Perm.SameCycle R.rot.symm x) := by
  ext y
  rw [mem_vertexOf, mem_filter, ← Equiv.Perm.inv_def, Equiv.Perm.sameCycle_inv]
  simp

/-- The dart `σ^{-k}(x)` lies at the vertex of `x`. -/
theorem rot_symm_pow_apply_mem_vertexOf (x : H) (k : ℕ) : (R.rot.symm ^ k) x ∈ R.vertexOf x := by
  rw [vertexOf_eq_filter_rot_symm, mem_filter]
  exact ⟨mem_univ _, Equiv.Perm.sameCycle_pow_right.2 (.refl _ _)⟩

/-- Turning `|v(x)|` times clockwise around the vertex of `x` comes back to `x`. -/
theorem rot_symm_pow_card_vertexOf (x : H) : (R.rot.symm ^ (R.vertexOf x).card) x = x := by
  rw [vertexOf_eq_filter_rot_symm]
  exact pow_card_filter_sameCycle_apply _ _

/-- The darts `σ^{-k}(x)`, `k < |v(x)|`, are pairwise distinct. -/
theorem rot_symm_pow_injOn {x : H} {i j : ℕ} (hi : i < (R.vertexOf x).card)
    (hj : j < (R.vertexOf x).card) (h : (R.rot.symm ^ i) x = (R.rot.symm ^ j) x) : i = j := by
  rw [vertexOf_eq_filter_rot_symm] at hi hj
  exact pow_apply_injective_of_lt_card _ _ hi hj h

/-- `σ^{-k}(x) ≠ x` for `0 < k < |v(x)|`. -/
theorem rot_symm_pow_ne_self {x : H} {k : ℕ} (hk0 : 0 < k) (hk : k < (R.vertexOf x).card) :
    (R.rot.symm ^ k) x ≠ x := fun h => by
  have := rot_symm_pow_injOn (j := 0) hk (by omega) (by rwa [pow_zero])
  omega

/-- `σ(x) = σ^{-(|v(x)| - 1)}(x)`. -/
theorem rot_eq_rot_symm_pow (x : H) : R.rot x = (R.rot.symm ^ ((R.vertexOf x).card - 1)) x := by
  have hpos : 0 < (R.vertexOf x).card := card_pos.2 ⟨x, R.self_mem_vertexOf x⟩
  have h := rot_symm_pow_card_vertexOf (R := R) x
  rw [show (R.vertexOf x).card = ((R.vertexOf x).card - 1) + 1 by omega, pow_succ',
    Equiv.Perm.mul_apply] at h
  exact (Equiv.apply_eq_iff_eq_symm_apply _).2 h.symm

omit [Fintype H] [DecidableEq H] in
/-- `σ(σ^{-(k+1)}(x)) = σ^{-k}(x)`. -/
theorem rot_rot_symm_pow_succ_apply (x : H) (k : ℕ) :
    R.rot ((R.rot.symm ^ (k + 1)) x) = (R.rot.symm ^ k) x := by
  rw [pow_succ', Equiv.Perm.mul_apply, Equiv.apply_symm_apply]

/-- **A corner labelling from the rotation.** An injective map `λ : ℤ/m → H` with
`λ(i + 1) = σ⁻¹(λ i)` is a corner labelling of the vertex of `λ 0`. -/
theorem isCornerLabelling_vertexOf_of_injective {m : ℕ} [NeZero m] {l : ZMod m → H} {x : H}
    (h0 : l 0 = x) (hinj : Function.Injective l) (hl : ∀ i, l (i + 1) = R.rot.symm (l i)) :
    R.IsCornerLabelling (R.vertexOf x) l := by
  subst h0
  have hpow : ∀ n : ℕ, l n = (R.rot.symm ^ n) (l 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, hl, ih, pow_succ', Equiv.Perm.mul_apply]
  refine ⟨⟨fun i _ => ?_, hinj.injOn, fun y hy => ?_⟩, hl⟩
  · rw [Finset.mem_coe, ← ZMod.natCast_zmod_val i, hpow]
    exact rot_symm_pow_apply_mem_vertexOf _ _
  · rw [Finset.mem_coe, vertexOf_eq_filter_rot_symm, mem_filter] at hy
    obtain ⟨n, hn⟩ := hy.2.exists_nat_pow_eq
    exact ⟨n, trivial, by rw [hpow, hn]⟩

/-- **The corner labelling `i ↦ σ^{-i}(x)`** of the vertex of `x`, indexed by `ℤ/|v(x)|`. -/
theorem isCornerLabelling_rot_symm_pow {n : ℕ} (x : H) (hn : (R.vertexOf x).card = n) :
    R.IsCornerLabelling (R.vertexOf x) fun i : ZMod n => (R.rot.symm ^ i.val) x := by
  have hpos : 0 < n := hn ▸ card_pos.2 ⟨x, R.self_mem_vertexOf x⟩
  haveI : NeZero n := ⟨by omega⟩
  refine isCornerLabelling_vertexOf_of_injective (by simp) (fun i j h => ?_) fun i => ?_
  · exact ZMod.val_injective n (rot_symm_pow_injOn (by rw [hn]; exact ZMod.val_lt i)
      (by rw [hn]; exact ZMod.val_lt j) h)
  · show (R.rot.symm ^ (i + 1).val) x = R.rot.symm ((R.rot.symm ^ i.val) x)
    rcases (eq_add_one_iff_val i (i + 1)).1 rfl with h | ⟨h1, h2⟩
    · rw [h, pow_succ', Equiv.Perm.mul_apply]
    · rw [h2, pow_zero, Equiv.Perm.one_apply, ← Equiv.Perm.mul_apply, ← pow_succ', h1, ← hn,
        rot_symm_pow_card_vertexOf]

namespace IsCornerLabelling

variable {m : ℕ} [NeZero m] {w : Finset H} {l : ZMod m → H}

omit [Fintype H] in
/-- A set of pairs of darts of `w` is the image of its pull-back. -/
theorem image_cornerPullback (hl : R.IsCornerLabelling w l) {D : Finset (Sym2 H)}
    (hD : ∀ e ∈ D, ∀ x ∈ e, x ∈ w) : (cornerPullback l D).image (Sym2.map l) = D := by
  ext e
  simp only [mem_image, mem_cornerPullback]
  refine ⟨fun ⟨_, he', h⟩ => h ▸ he', fun he => ?_⟩
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨i, rfl⟩ := hl.exists_eq (hD _ he x (Sym2.mem_mk_left x y))
    obtain ⟨j, rfl⟩ := hl.exists_eq (hD _ he _ (Sym2.mem_mk_right _ y))
    exact ⟨s(i, j), he, rfl⟩

omit [Fintype H] in
/-- The pull-back of an image is the original set of segments. -/
theorem cornerPullback_image (hl : R.IsCornerLabelling w l) (T : Finset (Sym2 (ZMod m))) :
    cornerPullback l (T.image (Sym2.map l)) = T := by
  ext e
  rw [mem_cornerPullback, (Sym2.map.injective hl.injective).mem_finset_image]

omit [Fintype H] in
/-- **Transport of triangulations.** The image of a set `T` of segments of the `m`-gon along a
corner labelling is a corner triangulation exactly when `T` is a triangulation. -/
theorem isCornerTriangulation_image_iff (hl : R.IsCornerLabelling w l)
    (T : Finset (Sym2 (ZMod m))) :
    R.IsCornerTriangulation w (T.image (Sym2.map l)) ↔ IsTriangulation T := by
  refine ⟨fun h => ?_, fun hT => ⟨fun e he => ?_, m, inferInstance, l, hl, ?_⟩⟩
  · have := h.isTriangulation_cornerPullback hl
    rwa [hl.cornerPullback_image] at this
  · obtain ⟨e', he', rfl⟩ := mem_image.1 he
    refine ⟨(Sym2.isDiag_map hl.injective).not.2 (hT.isDiagonal e' he').1, fun x hx => ?_⟩
    obtain ⟨i, -, rfl⟩ := Sym2.mem_map.1 hx
    exact hl.mem i
  · rwa [hl.cornerPullback_image]

omit [Fintype H] [DecidableEq H] in
/-- **Transport of clockwise listings.** `(λ a, λ b, λ c)` is clockwise exactly when `(a, b, c)`
is clockwise in the `m`-gon, or `c = a ≠ b`. -/
theorem isCornerClockwise_iff (hl : R.IsCornerLabelling w l) (a b c : ZMod m) :
    R.IsCornerClockwise (l a) (l b) (l c) ↔ sbtw a b c ∨ (c = a ∧ b ≠ a) := by
  constructor
  · rintro ⟨j, hj, hjb, hjc⟩
    rw [← hl.apply_add_nat] at hjb
    have hb := hl.injective hjb
    have hjc' : ∀ i : ℕ, 0 < i → i ≤ j → a + (i : ZMod m) ≠ c := fun i hi hij h =>
      hjc i hi hij (by rw [← hl.apply_add_nat, h])
    by_cases hca : c = a
    · refine Or.inr ⟨hca, fun hba => ?_⟩
      have h0 : ((j : ℕ) : ZMod m) = 0 := by linear_combination hb + hba
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact hjc' m (NeZero.pos m) (Nat.le_of_dvd hj h0) (by rw [ZMod.natCast_self, add_zero, hca])
    · left
      have hk0 : 0 < (c - a).val := ZMod.val_pos.2 (sub_ne_zero.2 hca)
      have hkc : a + ((c - a).val : ZMod m) = c := by rw [ZMod.natCast_zmod_val]; ring
      have hjk : j < (c - a).val := by
        by_contra h
        exact hjc' _ hk0 (by omega) hkc
      have hkm := ZMod.val_lt (c - a)
      rw [sbtw_iff_sbtw_basePos a, Int.sbtw_iff, basePos_self]
      have hbpos : basePos a b = j := by
        unfold basePos
        rw [← hb, add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      rw [hbpos, show basePos a c = (c - a).val from rfl]
      omega
  · rintro (h | ⟨hca, hba⟩)
    · exact hl.isCornerClockwise h
    · rw [hca]
      have hpos : 0 < (b - a).val := ZMod.val_pos.2 (sub_ne_zero.2 hba)
      refine ⟨(b - a).val, hpos, ?_, fun i hi hij h => ?_⟩
      · rw [← hl.apply_add_nat, ZMod.natCast_zmod_val, add_sub_cancel]
      · rw [← hl.apply_add_nat] at h
        have h' := hl.injective h
        have h0 : ((i : ℕ) : ZMod m) = 0 := by linear_combination h'
        rw [ZMod.natCast_eq_zero_iff] at h0
        have := Nat.le_of_dvd hi h0
        have := ZMod.val_lt (b - a)
        omega

end IsCornerLabelling

end RotationSystem

/-! ### Corner maps of a white contraction -/

namespace RotationSystem

variable {H : Type*} [DecidableEq H] (R : RotationSystem H)

/-- **The corner map** `κ₁` of the contraction along `{d, d̄}`, on the darts of `w₁ = v(d)`:
`κ₁(a) = a` for `a ≠ d`, and `κ₁(d) = σ⁻¹(d̄)`. It is written as a map on all darts. -/
@[cluster_algebras "def_corner_maps"]
def cornerMapFst (d a : H) : H := if a = d then R.rot.symm (R.inv d) else a

/-- **The corner map** `κ₂` of the contraction along `{d, d̄}`, on the darts of `w₂ = v(d̄)`:
`κ₂(a) = a` for `a ≠ d̄`, and `κ₂(d̄) = σ⁻¹(d)`. It is written as a map on all darts. -/
@[cluster_algebras "def_corner_maps"]
def cornerMapSnd (d a : H) : H := if a = R.inv d then R.rot.symm d else a

/-- **The diagonal** `γ_e = {σ⁻¹(d), σ⁻¹(d̄)}` of the merged vertex along which the corners of
`v(d)` and `v(d̄)` are glued. -/
@[cluster_algebras "def_corner_maps"]
def cornerGlueDiagonal (d : H) : Sym2 H := s(R.rot.symm d, R.rot.symm (R.inv d))

/-- The **glued set of pairs** `κ₁(D₁) ∪ κ₂(D₂) ∪ {γ_e}` of two sets of pairs of darts. -/
def cornerGlue (d : H) (D₁ D₂ : Finset (Sym2 H)) : Finset (Sym2 H) :=
  insert (R.cornerGlueDiagonal d)
    (D₁.image (Sym2.map (R.cornerMapFst d)) ∪ D₂.image (Sym2.map (R.cornerMapSnd d)))

variable {R}

/-- `κ₁(d) = σ⁻¹(d̄)`. -/
@[simp]
theorem cornerMapFst_self (d : H) : R.cornerMapFst d d = R.rot.symm (R.inv d) := if_pos rfl

/-- `κ₁(a) = a` for `a ≠ d`. -/
theorem cornerMapFst_of_ne {d a : H} (h : a ≠ d) : R.cornerMapFst d a = a := if_neg h

/-- `κ₂(d̄) = σ⁻¹(d)`. -/
@[simp]
theorem cornerMapSnd_inv (d : H) : R.cornerMapSnd d (R.inv d) = R.rot.symm d := if_pos rfl

/-- `κ₂(a) = a` for `a ≠ d̄`. -/
theorem cornerMapSnd_of_ne {d a : H} (h : a ≠ R.inv d) : R.cornerMapSnd d a = a := if_neg h

/-- A pair lies in `cornerGlue d D₁ D₂` iff it is `γ_e`, the image under `κ₁` of an element of
`D₁`, or the image under `κ₂` of an element of `D₂`. -/
theorem mem_cornerGlue {d : H} {D₁ D₂ : Finset (Sym2 H)} {e : Sym2 H} :
    e ∈ R.cornerGlue d D₁ D₂ ↔ e = R.cornerGlueDiagonal d ∨
      (∃ a ∈ D₁, a.map (R.cornerMapFst d) = e) ∨ ∃ a ∈ D₂, a.map (R.cornerMapSnd d) = e := by
  simp [cornerGlue]

end RotationSystem

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b} {d : H}

/-! #### Coordinates on the corners -/

section Coordinates

/-- The corner labelling `i ↦ σ^{-(i+1)}(d)` of `v(d)`. -/
private def labelFst (G : PlabicData H b) (d : H) {p : ℕ} (i : ZMod p) : H :=
  (G.rot.symm ^ i.val) (G.rot.symm d)

/-- The corner labelling `j ↦ σ^{-(j+1)}(d̄)` of `v(d̄)`. -/
private def labelSnd (G : PlabicData H b) (d : H) {q : ℕ} (j : ZMod q) : H :=
  (G.rot.symm ^ j.val) (G.rot.symm (G.inv d))

/-- The corner labelling of the merged vertex, read in `H`: `σ^{-(i+1)}(d)` for `i < p - 1` and
`σ^{-(i+2-p)}(d̄)` for `i ≥ p - 1`. -/
private def mergedLabel (G : PlabicData H b) (d : H) (p : ℕ) {m : ℕ} (i : ZMod m) : H :=
  if i.val < p - 1 then (G.rot.symm ^ (i.val + 1)) d
  else (G.rot.symm ^ (i.val + 2 - p)) (G.inv d)

variable {p q m : ℕ}

omit [Fintype H] [DecidableEq H] in
private theorem labelFst_apply (i : ZMod p) :
    labelFst G d i = (G.rot.symm ^ (i.val + 1)) d := by
  rw [labelFst, pow_succ, Equiv.Perm.mul_apply]

omit [Fintype H] [DecidableEq H] in
private theorem labelSnd_apply (j : ZMod q) :
    labelSnd G d j = (G.rot.symm ^ (j.val + 1)) (G.inv d) := by
  rw [labelSnd, pow_succ, Equiv.Perm.mul_apply]

private theorem isCornerLabelling_labelFst (hpd : (G.vertexOf d).card = p) :
    G.IsCornerLabelling (G.vertexOf d) (labelFst G d (p := p)) := by
  have hv := G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf d)
  have h := RotationSystem.isCornerLabelling_rot_symm_pow (R := G.toRotationSystem)
    (G.rot.symm d) (n := p) (by rw [hv, hpd])
  rw [hv] at h
  exact h

private theorem isCornerLabelling_labelSnd (hqd : (G.vertexOf (G.inv d)).card = q) :
    G.IsCornerLabelling (G.vertexOf (G.inv d)) (labelSnd G d (q := q)) := by
  have hv := G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf (G.inv d))
  have h := RotationSystem.isCornerLabelling_rot_symm_pow (R := G.toRotationSystem)
    (G.rot.symm (G.inv d)) (n := q) (by rw [hv, hqd])
  rw [hv] at h
  exact h

variable (hne : G.vertexOf d ≠ G.vertexOf (G.inv d)) (hpd : (G.vertexOf d).card = p)
  (hqd : (G.vertexOf (G.inv d)).card = q) (hp : 3 ≤ p) (hq : 3 ≤ q) (hm : m + 2 = p + q)

include hne in
private theorem not_mem_both {y : H} (h1 : y ∈ G.vertexOf d) (h2 : y ∈ G.vertexOf (G.inv d)) :
    False :=
  hne ((G.vertexOf_eq_of_mem h1).symm.trans (G.vertexOf_eq_of_mem h2))

include hne hpd hqd hp hq hm

private theorem mergedLabel_spec [NeZero m] (i : ZMod m) :
    (mergedLabel G d p i ∈ G.vertexOf d ∨ mergedLabel G d p i ∈ G.vertexOf (G.inv d)) ∧
      mergedLabel G d p i ≠ d ∧ mergedLabel G d p i ≠ G.inv d := by
  have hi := ZMod.val_lt i
  unfold mergedLabel
  split_ifs with h
  · have hmem := RotationSystem.rot_symm_pow_apply_mem_vertexOf (R := G.toRotationSystem) d
      (i.val + 1)
    refine ⟨Or.inl hmem, RotationSystem.rot_symm_pow_ne_self (by omega) (by rw [hpd]; omega),
      fun h' => not_mem_both hne hmem (by rw [h']; exact G.self_mem_vertexOf _)⟩
  · have hmem := RotationSystem.rot_symm_pow_apply_mem_vertexOf (R := G.toRotationSystem) (G.inv d)
      (i.val + 2 - p)
    refine ⟨Or.inr hmem, fun h' => not_mem_both hne (by rw [h']; exact G.self_mem_vertexOf _) hmem,
      RotationSystem.rot_symm_pow_ne_self (by omega) (by rw [hqd]; omega)⟩

private theorem mergedLabel_mem [NeZero m] (i : ZMod m) :
    mergedLabel G d p i ∈ (({d, G.inv d} : Set H)ᶜ : Set H) :=
  mem_compl_pair_iff.2 (mergedLabel_spec hne hpd hqd hp hq hm i).2

private theorem mergedLabel_injective [NeZero m] :
    Function.Injective (mergedLabel G d p (m := m)) := by
  intro i j h
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  apply ZMod.val_injective
  unfold mergedLabel at h
  split_ifs at h with h1 h2 h2
  · have := RotationSystem.rot_symm_pow_injOn (R := G.toRotationSystem)
      (by rw [hpd]; omega) (by rw [hpd]; omega) h
    omega
  · have m1 := RotationSystem.rot_symm_pow_apply_mem_vertexOf (R := G.toRotationSystem) d
      (i.val + 1)
    have m2 := RotationSystem.rot_symm_pow_apply_mem_vertexOf (R := G.toRotationSystem)
      (G.inv d) (j.val + 2 - p)
    rw [← h] at m2
    exact (not_mem_both hne m1 m2).elim
  · have m1 := RotationSystem.rot_symm_pow_apply_mem_vertexOf (R := G.toRotationSystem) d
      (j.val + 1)
    have m2 := RotationSystem.rot_symm_pow_apply_mem_vertexOf (R := G.toRotationSystem)
      (G.inv d) (i.val + 2 - p)
    rw [h] at m2
    exact (not_mem_both hne m1 m2).elim
  · have := RotationSystem.rot_symm_pow_injOn (R := G.toRotationSystem)
      (by rw [hqd]; omega) (by rw [hqd]; omega) h
    omega

/-- The rotation of the contraction turns the merged labelling one step counterclockwise. -/
private theorem rot_mergedLabel_add_one [NeZero m]
    {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)} (i : ZMod m)
    {x : (({d, G.inv d} : Set H)ᶜ : Set H)} (hx : (x : H) = mergedLabel G d p (i + 1)) :
    ((G.contractEdge d hleg).rot x : H) = mergedLabel G d p i := by
  have hv := ZMod.val_lt i
  have hmemi := mergedLabel_mem hne hpd hqd hp hq hm i
  have hrot := RotationSystem.rot_rot_symm_pow_succ_apply (R := G.toRotationSystem)
  rcases (eq_add_one_iff_val i (i + 1)).1 rfl with h1 | ⟨h1, h2⟩
  · by_cases hA : i.val + 1 < p - 1
    · have e : G.rot x = mergedLabel G d p i := by
        rw [hx]
        unfold mergedLabel
        rw [h1, if_pos hA, if_pos (by omega), hrot]
      have hσ : G.rot x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by rwa [e]
      rw [coe_contractEdge_rot_of_mem hσ, e]
    · by_cases hB : i.val + 1 = p - 1
      · have e1 : (x : H) = G.rot.symm (G.inv d) := by
          rw [hx]
          unfold mergedLabel
          rw [h1, if_neg (by omega), show i.val + 1 + 2 - p = 1 by omega, pow_one]
        have e0 : mergedLabel G d p i = G.rot d := by
          unfold mergedLabel
          rw [if_pos (by omega), RotationSystem.rot_eq_rot_symm_pow (R := G.toRotationSystem) d,
            hpd, show i.val + 1 = p - 1 by omega]
        have hxd : G.rot x = G.inv d := by rw [e1, Equiv.apply_symm_apply]
        have hσ : G.rot d ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by rwa [← e0]
        rw [coe_contractEdge_rot_of_eq_inv hxd hσ, e0]
      · have e : G.rot x = mergedLabel G d p i := by
          rw [hx]
          unfold mergedLabel
          rw [h1, if_neg (by omega), if_neg (by omega),
            show i.val + 1 + 2 - p = (i.val + 2 - p) + 1 by omega, hrot]
        have hσ : G.rot x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by rwa [e]
        rw [coe_contractEdge_rot_of_mem hσ, e]
  · have e1 : (x : H) = G.rot.symm d := by
      rw [hx]
      unfold mergedLabel
      rw [h2, if_pos (by omega), zero_add, pow_one]
    have e0 : mergedLabel G d p i = G.rot (G.inv d) := by
      unfold mergedLabel
      rw [if_neg (by omega), RotationSystem.rot_eq_rot_symm_pow (R := G.toRotationSystem) (G.inv d),
        hqd, show i.val + 2 - p = q - 1 by omega]
    have hxd : G.rot x = d := by rw [e1, Equiv.apply_symm_apply]
    have hσ : G.rot (G.inv d) ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by rwa [← e0]
    rw [coe_contractEdge_rot_of_eq hxd hσ, e0]

/-- The merged labelling as a map to the darts of the contraction. -/
private def mergedLabelSub [NeZero m] (i : ZMod m) : (({d, G.inv d} : Set H)ᶜ : Set H) :=
  ⟨mergedLabel G d p i, mergedLabel_mem hne hpd hqd hp hq hm i⟩

/-- **The corner labelling of the merged vertex.** -/
private theorem isCornerLabelling_mergedLabelSub [NeZero m]
    {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)} :
    (G.contractEdge d hleg).IsCornerLabelling
      ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))
      (mergedLabelSub hne hpd hqd hp hq hm) := by
  have hsc : ¬G.rot.SameCycle d (G.inv d) := fun h => hne (G.vertexOf_eq_vertexOf_iff.2 h)
  have hV : (G.contractEdge d hleg).vertexOf (mergedLabelSub hne hpd hqd hp hq hm 0) =
      (G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) := by
    apply Finset.map_injective (Function.Embedding.subtype _)
    rw [map_vertexOf_contractEdge_of_mem (x := mergedLabelSub hne hpd hqd hp hq hm 0) hsc
      (mem_union.2 (mergedLabel_spec hne hpd hqd hp hq hm 0).1), subtype_map_of_mem]
    intro x hx
    exact mem_compl_pair_iff.2 (mem_mergedVertex.1 hx).2
  rw [← hV]
  refine RotationSystem.isCornerLabelling_vertexOf_of_injective rfl (fun i j h => ?_) fun i => ?_
  · exact mergedLabel_injective hne hpd hqd hp hq hm (congrArg Subtype.val h)
  · rw [Equiv.eq_symm_apply]
    exact Subtype.ext (rot_mergedLabel_add_one hne hpd hqd hp hq hm i
      (x := mergedLabelSub hne hpd hqd hp hq hm (i + 1)) rfl)

omit hne hqd in
private theorem cornerMapFst_labelFst [NeZero p] (i : ZMod p) :
    G.cornerMapFst d (labelFst G d i) = mergedLabel G d p (polygonGlueFst m i) := by
  have hv : (polygonGlueFst m i).val = i.val := val_polygonGlueFst hm (by omega) i
  have hi := ZMod.val_lt i
  rw [labelFst_apply]
  unfold mergedLabel
  rw [hv]
  by_cases h : i.val < p - 1
  · rw [if_pos h, RotationSystem.cornerMapFst_of_ne
      (RotationSystem.rot_symm_pow_ne_self (by omega) (by rw [hpd]; omega))]
  · have hd : (G.rot.symm ^ p) d = d := hpd ▸ RotationSystem.rot_symm_pow_card_vertexOf d
    rw [if_neg h, show i.val + 1 = p by omega, hd, show i.val + 2 - p = 1 by omega, pow_one,
      RotationSystem.cornerMapFst_self]

omit hne hpd hq in
private theorem cornerMapSnd_labelSnd [NeZero q] (j : ZMod q) :
    G.cornerMapSnd d (labelSnd G d j) = mergedLabel G d p (polygonGlueSnd m p j) := by
  have hv := val_polygonGlueSnd hm (by omega : 1 ≤ p) j
  have hj := ZMod.val_lt j
  rw [labelSnd_apply]
  unfold mergedLabel
  rw [hv]
  by_cases h : j.val + 1 = q
  · have hd : (G.rot.symm ^ q) (G.inv d) = G.inv d :=
      hqd ▸ RotationSystem.rot_symm_pow_card_vertexOf (G.inv d)
    rw [if_pos h, if_pos (by omega), zero_add, pow_one, h, hd, RotationSystem.cornerMapSnd_inv]
  · rw [if_neg h, if_neg (by omega), show p - 1 + j.val + 2 - p = j.val + 1 by omega,
      RotationSystem.cornerMapSnd_of_ne
        (RotationSystem.rot_symm_pow_ne_self (by omega) (by rw [hqd]; omega))]

omit [Fintype H] [DecidableEq H] hne hpd hqd in
private theorem cornerGlueDiagonal_eq [NeZero p] :
    G.cornerGlueDiagonal d = (polygonGlueDiagonal m p).map (mergedLabel G d p) := by
  rw [polygonGlueDiagonal, Sym2.map_mk, RotationSystem.cornerGlueDiagonal]
  unfold mergedLabel
  rw [ZMod.val_zero, val_natCast_pred hm (by omega), if_pos (by omega), if_neg (by omega),
    zero_add, pow_one, show p - 1 + 2 - p = 1 by omega, pow_one]

omit hne in
/-- In coordinates, gluing is `polygonGlue`. -/
private theorem cornerGlue_image_labels [NeZero p] [NeZero q]
    (T₁ : Finset (Sym2 (ZMod p))) (T₂ : Finset (Sym2 (ZMod q))) :
    G.cornerGlue d (T₁.image (Sym2.map (labelFst G d))) (T₂.image (Sym2.map (labelSnd G d))) =
      (polygonGlue m T₁ T₂).image (Sym2.map (mergedLabel G d p)) := by
  have h1 : Sym2.map (G.cornerMapFst d) ∘ Sym2.map (labelFst G d (p := p)) =
      Sym2.map (mergedLabel G d p (m := m)) ∘ Sym2.map (polygonGlueFst m) := by
    funext e
    simp only [Function.comp_apply, Sym2.map_map]
    congr 1
    funext i
    exact cornerMapFst_labelFst hpd hp hq hm i
  have h2 : Sym2.map (G.cornerMapSnd d) ∘ Sym2.map (labelSnd G d (q := q)) =
      Sym2.map (mergedLabel G d p (m := m)) ∘ Sym2.map (polygonGlueSnd m p) := by
    funext e
    simp only [Function.comp_apply, Sym2.map_map]
    congr 1
    funext j
    exact cornerMapSnd_labelSnd hqd hp hm j
  rw [RotationSystem.cornerGlue, polygonGlue, image_insert, image_union, image_image, image_image,
    image_image, image_image, h1, h2, cornerGlueDiagonal_eq hp hq hm]

private theorem image_val_image_mergedLabelSub [NeZero m] (X : Finset (Sym2 (ZMod m))) :
    (X.image (Sym2.map (mergedLabelSub hne hpd hqd hp hq hm))).image (Sym2.map Subtype.val) =
      X.image (Sym2.map (mergedLabel G d p)) := by
  rw [image_image]
  congr 1
  funext e
  simp only [Function.comp_apply, Sym2.map_map]
  rfl

private theorem image_cornerMapFst_image_labelFst [NeZero p] [NeZero m] (τ : Finset (ZMod p)) :
    (τ.image (labelFst G d (p := p))).image (G.cornerMapFst d) =
      ((τ.image (polygonGlueFst m)).image (mergedLabelSub hne hpd hqd hp hq hm)).image
        Subtype.val := by
  simp only [image_image]
  congr 1
  funext i
  exact cornerMapFst_labelFst hpd hp hq hm i

private theorem image_cornerMapSnd_image_labelSnd [NeZero q] [NeZero m] (τ : Finset (ZMod q)) :
    (τ.image (labelSnd G d (q := q))).image (G.cornerMapSnd d) =
      ((τ.image (polygonGlueSnd m p)).image (mergedLabelSub hne hpd hqd hp hq hm)).image
        Subtype.val := by
  simp only [image_image]
  congr 1
  funext j
  exact cornerMapSnd_labelSnd hqd hp hm j

private theorem exists_isCornerTriangulation_image_eq_cornerGlue [NeZero p] [NeZero q] [NeZero m]
    {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)} {D₁ D₂ : Finset (Sym2 H)}
    (hD₁ : G.IsCornerTriangulation (G.vertexOf d) D₁)
    (hD₂ : G.IsCornerTriangulation (G.vertexOf (G.inv d)) D₂) :
    ∃ D, (G.contractEdge d hleg).IsCornerTriangulation
        ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))) D ∧
      D.image (Sym2.map Subtype.val) = G.cornerGlue d D₁ D₂ := by
  have hl₁ := isCornerLabelling_labelFst (G := G) (d := d) hpd
  have hl₂ := isCornerLabelling_labelSnd (G := G) (d := d) hqd
  have hl := isCornerLabelling_mergedLabelSub (hleg := hleg) hne hpd hqd hp hq hm
  refine ⟨_, (hl.isCornerTriangulation_image_iff _).2
    (isTriangulation_polygonGlue hm hp hq (hD₁.isTriangulation_cornerPullback hl₁)
      (hD₂.isTriangulation_cornerPullback hl₂)), ?_⟩
  rw [image_val_image_mergedLabelSub, ← cornerGlue_image_labels hpd hqd hp hq hm,
    hl₁.image_cornerPullback fun e he => (hD₁.1 e he).2,
    hl₂.image_cornerPullback fun e he => (hD₂.1 e he).2]

private theorem injOn_cornerGlue [NeZero p] [NeZero q] [NeZero m] :
    Set.InjOn (fun D : Finset (Sym2 H) × Finset (Sym2 H) => G.cornerGlue d D.1 D.2)
      {D | G.IsCornerTriangulation (G.vertexOf d) D.1 ∧
        G.IsCornerTriangulation (G.vertexOf (G.inv d)) D.2} := by
  have hl₁ := isCornerLabelling_labelFst (G := G) (d := d) hpd
  have hl₂ := isCornerLabelling_labelSnd (G := G) (d := d) hqd
  rintro ⟨D₁, D₂⟩ ⟨hD₁, hD₂⟩ ⟨D₁', D₂'⟩ ⟨hD₁', hD₂'⟩ h
  dsimp only at hD₁ hD₂ hD₁' hD₂'
  have h' : G.cornerGlue d D₁ D₂ = G.cornerGlue d D₁' D₂' := h
  have e₁ := hl₁.image_cornerPullback fun e he => (hD₁.1 e he).2
  have e₂ := hl₂.image_cornerPullback fun e he => (hD₂.1 e he).2
  have e₁' := hl₁.image_cornerPullback fun e he => (hD₁'.1 e he).2
  have e₂' := hl₂.image_cornerPullback fun e he => (hD₂'.1 e he).2
  have t₁ := hD₁.isTriangulation_cornerPullback hl₁
  have t₂ := hD₂.isTriangulation_cornerPullback hl₂
  have t₁' := hD₁'.isTriangulation_cornerPullback hl₁
  have t₂' := hD₂'.isTriangulation_cornerPullback hl₂
  generalize RotationSystem.cornerPullback (labelFst G d (p := p)) D₁ = T₁ at e₁ t₁
  generalize RotationSystem.cornerPullback (labelSnd G d (q := q)) D₂ = T₂ at e₂ t₂
  generalize RotationSystem.cornerPullback (labelFst G d (p := p)) D₁' = T₁' at e₁' t₁'
  generalize RotationSystem.cornerPullback (labelSnd G d (q := q)) D₂' = T₂' at e₂' t₂'
  subst e₁ e₂ e₁' e₂'
  rw [cornerGlue_image_labels hpd hqd hp hq hm, cornerGlue_image_labels hpd hqd hp hq hm] at h'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj <| (bijOn_polygonGlue hm hp hq).injOn ⟨t₁, t₂⟩ ⟨t₁', t₂'⟩
    (Finset.image_injective (Sym2.map.injective (mergedLabel_injective hne hpd hqd hp hq hm)) h')
  rfl

private theorem exists_cornerGlue_eq_image [NeZero p] [NeZero q] [NeZero m]
    {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}
    {D : Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H))}
    (hD : (G.contractEdge d hleg).IsCornerTriangulation
      ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))) D)
    (hγ : G.cornerGlueDiagonal d ∈ D.image (Sym2.map Subtype.val)) :
    ∃ D₁ D₂, G.IsCornerTriangulation (G.vertexOf d) D₁ ∧
      G.IsCornerTriangulation (G.vertexOf (G.inv d)) D₂ ∧
      G.cornerGlue d D₁ D₂ = D.image (Sym2.map Subtype.val) := by
  have hl := isCornerLabelling_mergedLabelSub (hleg := hleg) hne hpd hqd hp hq hm
  obtain ⟨T, hTdef⟩ : ∃ T, RotationSystem.cornerPullback
      (mergedLabelSub hne hpd hqd hp hq hm) D = T := ⟨_, rfl⟩
  have hT : IsTriangulation T := hTdef ▸ hD.isTriangulation_cornerPullback hl
  have hDimg : T.image (Sym2.map (mergedLabelSub hne hpd hqd hp hq hm)) = D :=
    hTdef ▸ hl.image_cornerPullback fun e he => (hD.1 e he).2
  rw [← hDimg, image_val_image_mergedLabelSub] at hγ ⊢
  rw [cornerGlueDiagonal_eq hp hq hm,
    (Sym2.map.injective (mergedLabel_injective hne hpd hqd hp hq hm)).mem_finset_image] at hγ
  obtain ⟨⟨T₁, T₂⟩, ⟨hT₁, hT₂⟩, hTeq⟩ := (bijOn_polygonGlue hm hp hq).surjOn
    (show T ∈ {T | IsTriangulation T ∧ polygonGlueDiagonal m p ∈ T} from ⟨hT, hγ⟩)
  have hTeq' : polygonGlue m T₁ T₂ = T := hTeq
  have hl₁ := isCornerLabelling_labelFst (G := G) (d := d) hpd
  have hl₂ := isCornerLabelling_labelSnd (G := G) (d := d) hqd
  exact ⟨_, _, (hl₁.isCornerTriangulation_image_iff T₁).2 hT₁,
    (hl₂.isCornerTriangulation_image_iff T₂).2 hT₂,
    by rw [cornerGlue_image_labels hpd hqd hp hq hm, hTeq']⟩

end Coordinates

/-! #### Gluing corner triangulations -/

section CornerGlue

variable {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}

/-- **Gluing corner triangulations along an edge**. Let `{d, d̄}` be an edge whose ends `w₁ = v(d)`
and `w₂ = v(d̄)` are distinct vertices with at least three darts each, and let `Q` be the
contraction along `{d, d̄}`, with merged vertex `v`. Then `(D₁, D₂) ↦ κ₁(D₁) ∪ κ₂(D₂) ∪ {γ_e}` is a
bijection from the pairs of corner triangulations of `w₁` and of `w₂` onto the corner
triangulations of `v` in `Q` containing `γ_e`, the latter read in `H` through the inclusion of the
darts of `Q`. -/
@[cluster_algebras "lem_corner_triangulation_glue"]
theorem bijOn_cornerGlue (hne : G.vertexOf d ≠ G.vertexOf (G.inv d))
    (hp : 3 ≤ (G.vertexOf d).card) (hq : 3 ≤ (G.vertexOf (G.inv d)).card) :
    Set.BijOn (fun D : Finset (Sym2 H) × Finset (Sym2 H) => G.cornerGlue d D.1 D.2)
      {D | G.IsCornerTriangulation (G.vertexOf d) D.1 ∧
        G.IsCornerTriangulation (G.vertexOf (G.inv d)) D.2}
      {E | (∃ D : Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H)),
          (G.contractEdge d hleg).IsCornerTriangulation
            ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))) D ∧
          D.image (Sym2.map Subtype.val) = E) ∧ G.cornerGlueDiagonal d ∈ E} := by
  obtain ⟨p, hpd⟩ : ∃ p, (G.vertexOf d).card = p := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q, (G.vertexOf (G.inv d)).card = q := ⟨_, rfl⟩
  rw [hpd] at hp
  rw [hqd] at hq
  obtain ⟨m, hm⟩ : ∃ m, m + 2 = p + q := ⟨p + q - 2, by omega⟩
  haveI : NeZero p := ⟨by omega⟩
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero m := ⟨by omega⟩
  refine ⟨fun D hD => ⟨exists_isCornerTriangulation_image_eq_cornerGlue hne hpd hqd hp hq hm
    hD.1 hD.2, RotationSystem.mem_cornerGlue.2 (Or.inl rfl)⟩,
    injOn_cornerGlue hne hpd hqd hp hq hm, ?_⟩
  rintro E ⟨⟨D, hD, rfl⟩, hγ⟩
  obtain ⟨D₁, D₂, hD₁, hD₂, h⟩ := exists_cornerGlue_eq_image hne hpd hqd hp hq hm hD hγ
  exact ⟨(D₁, D₂), ⟨hD₁, hD₂⟩, h⟩

/-- The glued set of a pair of corner triangulations of `v(d)` and `v(d̄)`, read in the darts of
the contraction, is a corner triangulation of the merged vertex. -/
theorem isCornerTriangulation_of_image_eq_cornerGlue
    (hne : G.vertexOf d ≠ G.vertexOf (G.inv d))
    (hp : 3 ≤ (G.vertexOf d).card) (hq : 3 ≤ (G.vertexOf (G.inv d)).card)
    {D₁ D₂ : Finset (Sym2 H)} (hD₁ : G.IsCornerTriangulation (G.vertexOf d) D₁)
    (hD₂ : G.IsCornerTriangulation (G.vertexOf (G.inv d)) D₂)
    {D : Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H))}
    (hD : D.image (Sym2.map Subtype.val) = G.cornerGlue d D₁ D₂) :
    (G.contractEdge d hleg).IsCornerTriangulation
      ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))) D := by
  obtain ⟨⟨D', hD', hD'img⟩, -⟩ := (bijOn_cornerGlue (hleg := hleg) hne hp hq).mapsTo
    (show (D₁, D₂) ∈ {D : Finset (Sym2 H) × Finset (Sym2 H) |
      G.IsCornerTriangulation (G.vertexOf d) D.1 ∧
        G.IsCornerTriangulation (G.vertexOf (G.inv d)) D.2} from ⟨hD₁, hD₂⟩)
  exact Finset.image_injective (Sym2.map.injective Subtype.val_injective)
    (hD'img.trans hD.symm) ▸ hD'

/-- **The triangles of a glued corner triangulation**. In the setting of `bijOn_cornerGlue`, let
`D₁`, `D₂` be corner triangulations of `v(d)`, `v(d̄)` and `D` the set of pairs of darts of the
contraction which, read in `H`, is `κ₁(D₁) ∪ κ₂(D₂) ∪ {γ_e}`. The triangles of `D` are the sets
`κ₁(τ)` for the triangles `τ` of `D₁` and `κ₂(τ)` for the triangles `τ` of `D₂`, read in `H`. -/
@[cluster_algebras "lem_corner_triangulation_glue_triangles"]
theorem isCornerTriangle_iff_of_image_eq_cornerGlue
    (hne : G.vertexOf d ≠ G.vertexOf (G.inv d))
    (hp : 3 ≤ (G.vertexOf d).card) (hq : 3 ≤ (G.vertexOf (G.inv d)).card)
    {D₁ D₂ : Finset (Sym2 H)} (hD₁ : G.IsCornerTriangulation (G.vertexOf d) D₁)
    (hD₂ : G.IsCornerTriangulation (G.vertexOf (G.inv d)) D₂)
    {D : Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H))}
    (hD : D.image (Sym2.map Subtype.val) = G.cornerGlue d D₁ D₂)
    (t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).IsCornerTriangle
        ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))) D t ↔
      (∃ τ, G.IsCornerTriangle (G.vertexOf d) D₁ τ ∧
          τ.image (G.cornerMapFst d) = t.image Subtype.val) ∨
        ∃ τ, G.IsCornerTriangle (G.vertexOf (G.inv d)) D₂ τ ∧
          τ.image (G.cornerMapSnd d) = t.image Subtype.val := by
  obtain ⟨p, hpd⟩ : ∃ p, (G.vertexOf d).card = p := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q, (G.vertexOf (G.inv d)).card = q := ⟨_, rfl⟩
  rw [hpd] at hp
  rw [hqd] at hq
  obtain ⟨m, hm⟩ : ∃ m, m + 2 = p + q := ⟨p + q - 2, by omega⟩
  haveI : NeZero p := ⟨by omega⟩
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero m := ⟨by omega⟩
  have hl₁ := isCornerLabelling_labelFst (G := G) (d := d) hpd
  have hl₂ := isCornerLabelling_labelSnd (G := G) (d := d) hqd
  have hl := isCornerLabelling_mergedLabelSub (hleg := hleg) hne hpd hqd hp hq hm
  generalize hT₁def : RotationSystem.cornerPullback (labelFst G d (p := p)) D₁ = T₁
  generalize hT₂def : RotationSystem.cornerPullback (labelSnd G d (q := q)) D₂ = T₂
  have hT₁ : IsTriangulation T₁ := hT₁def ▸ hD₁.isTriangulation_cornerPullback hl₁
  have hT₂ : IsTriangulation T₂ := hT₂def ▸ hD₂.isTriangulation_cornerPullback hl₂
  have hD₁' : T₁.image (Sym2.map (labelFst G d (p := p))) = D₁ :=
    hT₁def ▸ hl₁.image_cornerPullback fun e he => (hD₁.1 e he).2
  have hD₂' : T₂.image (Sym2.map (labelSnd G d (q := q))) = D₂ :=
    hT₂def ▸ hl₂.image_cornerPullback fun e he => (hD₂.1 e he).2
  have hDeq : (polygonGlue m T₁ T₂).image (Sym2.map (mergedLabelSub hne hpd hqd hp hq hm)) = D := by
    apply Finset.image_injective (Sym2.map.injective Subtype.val_injective)
    rw [image_val_image_mergedLabelSub, hD, ← hD₁', ← hD₂',
      cornerGlue_image_labels hpd hqd hp hq hm]
  have hpull : RotationSystem.cornerPullback (mergedLabelSub hne hpd hqd hp hq hm) D =
      polygonGlue m T₁ T₂ := by
    rw [← hDeq, hl.cornerPullback_image]
  have himg₁ := image_cornerMapFst_image_labelFst hne hpd hqd hp hq hm
  have himg₂ := image_cornerMapSnd_image_labelSnd hne hpd hqd hp hq hm
  have hvinj : Function.Injective
      (Finset.image (Subtype.val : (({d, G.inv d} : Set H)ᶜ : Set H) → H)) :=
    Finset.image_injective Subtype.val_injective
  rw [hl.isCornerTriangle_iff, hpull]
  constructor
  · rintro ⟨t', ht', rfl⟩
    rcases (isTriangle_polygonGlue_iff hm hp hq hT₁ hT₂ t').1 ht' with
      ⟨τ', hτ', rfl⟩ | ⟨τ', hτ', rfl⟩
    · exact Or.inl ⟨τ'.image (labelFst G d (p := p)),
        (hl₁.isCornerTriangle_image_iff τ').2 (by rwa [hT₁def]), himg₁ τ'⟩
    · exact Or.inr ⟨τ'.image (labelSnd G d (q := q)),
        (hl₂.isCornerTriangle_image_iff τ').2 (by rwa [hT₂def]), himg₂ τ'⟩
  · rintro (⟨τ, hτ, himg⟩ | ⟨τ, hτ, himg⟩)
    · obtain ⟨τ', hτ', rfl⟩ := (hl₁.isCornerTriangle_iff τ).1 hτ
      rw [hT₁def] at hτ'
      exact ⟨τ'.image (polygonGlueFst m),
        (isTriangle_polygonGlue_iff hm hp hq hT₁ hT₂ _).2 (Or.inl ⟨τ', hτ', rfl⟩),
        hvinj (by rw [← himg₁, himg])⟩
    · obtain ⟨τ', hτ', rfl⟩ := (hl₂.isCornerTriangle_iff τ).1 hτ
      rw [hT₂def] at hτ'
      exact ⟨τ'.image (polygonGlueSnd m p),
        (isTriangle_polygonGlue_iff hm hp hq hT₁ hT₂ _).2 (Or.inr ⟨τ', hτ', rfl⟩),
        hvinj (by rw [← himg₂, himg])⟩

/-- **`κ₁` maps clockwise listings to clockwise listings**. -/
@[cluster_algebras "lem_corner_triangulation_glue_triangles"]
theorem isCornerClockwise_cornerMapFst (hne : G.vertexOf d ≠ G.vertexOf (G.inv d))
    (hp : 3 ≤ (G.vertexOf d).card) (hq : 3 ≤ (G.vertexOf (G.inv d)).card)
    {x y z : H} (hx : x ∈ G.vertexOf d) (hy : y ∈ G.vertexOf d) (hz : z ∈ G.vertexOf d)
    (h : G.IsCornerClockwise x y z) {x' y' z' : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hx' : (x' : H) = G.cornerMapFst d x) (hy' : (y' : H) = G.cornerMapFst d y)
    (hz' : (z' : H) = G.cornerMapFst d z) :
    (G.contractEdge d hleg).IsCornerClockwise x' y' z' := by
  obtain ⟨p, hpd⟩ : ∃ p, (G.vertexOf d).card = p := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q, (G.vertexOf (G.inv d)).card = q := ⟨_, rfl⟩
  rw [hpd] at hp
  rw [hqd] at hq
  obtain ⟨m, hm⟩ : ∃ m, m + 2 = p + q := ⟨p + q - 2, by omega⟩
  haveI : NeZero p := ⟨by omega⟩
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero m := ⟨by omega⟩
  have hl₁ := isCornerLabelling_labelFst (G := G) (d := d) hpd
  have hl := isCornerLabelling_mergedLabelSub (hleg := hleg) hne hpd hqd hp hq hm
  obtain ⟨i, rfl⟩ := hl₁.exists_eq hx
  obtain ⟨j, rfl⟩ := hl₁.exists_eq hy
  obtain ⟨k, rfl⟩ := hl₁.exists_eq hz
  have e : ∀ {u' : (({d, G.inv d} : Set H)ᶜ : Set H)} {u : ZMod p},
      (u' : H) = G.cornerMapFst d (labelFst G d u) →
        u' = mergedLabelSub hne hpd hqd hp hq hm (polygonGlueFst m u) :=
    fun hu => Subtype.ext (hu.trans (cornerMapFst_labelFst hpd hp hq hm _))
  rw [e hx', e hy', e hz', hl.isCornerClockwise_iff]
  rcases (hl₁.isCornerClockwise_iff i j k).1 h with h | ⟨hki, hji⟩
  · exact Or.inl ((sbtw_polygonGlueFst_iff hm hq i j k).2 h)
  · exact Or.inr ⟨by rw [hki], fun h' => hji (polygonGlueFst_injective hm hq h')⟩

/-- **`κ₂` maps clockwise listings to clockwise listings**. -/
@[cluster_algebras "lem_corner_triangulation_glue_triangles"]
theorem isCornerClockwise_cornerMapSnd (hne : G.vertexOf d ≠ G.vertexOf (G.inv d))
    (hp : 3 ≤ (G.vertexOf d).card) (hq : 3 ≤ (G.vertexOf (G.inv d)).card)
    {x y z : H} (hx : x ∈ G.vertexOf (G.inv d)) (hy : y ∈ G.vertexOf (G.inv d))
    (hz : z ∈ G.vertexOf (G.inv d)) (h : G.IsCornerClockwise x y z)
    {x' y' z' : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hx' : (x' : H) = G.cornerMapSnd d x) (hy' : (y' : H) = G.cornerMapSnd d y)
    (hz' : (z' : H) = G.cornerMapSnd d z) :
    (G.contractEdge d hleg).IsCornerClockwise x' y' z' := by
  obtain ⟨p, hpd⟩ : ∃ p, (G.vertexOf d).card = p := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q, (G.vertexOf (G.inv d)).card = q := ⟨_, rfl⟩
  rw [hpd] at hp
  rw [hqd] at hq
  obtain ⟨m, hm⟩ : ∃ m, m + 2 = p + q := ⟨p + q - 2, by omega⟩
  haveI : NeZero p := ⟨by omega⟩
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero m := ⟨by omega⟩
  have hl₂ := isCornerLabelling_labelSnd (G := G) (d := d) hqd
  have hl := isCornerLabelling_mergedLabelSub (hleg := hleg) hne hpd hqd hp hq hm
  obtain ⟨i, rfl⟩ := hl₂.exists_eq hx
  obtain ⟨j, rfl⟩ := hl₂.exists_eq hy
  obtain ⟨k, rfl⟩ := hl₂.exists_eq hz
  have e : ∀ {u' : (({d, G.inv d} : Set H)ᶜ : Set H)} {u : ZMod q},
      (u' : H) = G.cornerMapSnd d (labelSnd G d u) →
        u' = mergedLabelSub hne hpd hqd hp hq hm (polygonGlueSnd m p u) :=
    fun hu => Subtype.ext (hu.trans (cornerMapSnd_labelSnd hqd hp hm _))
  rw [e hx', e hy', e hz', hl.isCornerClockwise_iff]
  rcases (hl₂.isCornerClockwise_iff i j k).1 h with h | ⟨hki, hji⟩
  · exact Or.inl ((sbtw_polygonGlueSnd_iff hm hp i j k).2 h)
  · exact Or.inr ⟨by rw [hki], fun h' => hji (polygonGlueSnd_injective hm hp h')⟩

end CornerGlue

end PlabicData

/-! ### A corner triangulation with a prescribed ear -/

namespace RotationSystem

variable {H : Type*} [Fintype H] [DecidableEq H] {R : RotationSystem H}

/-- The `n`-gon, `n ≥ 3`, has a triangulation of which `{0, 1, 2}` is a triangle. -/
private theorem exists_isTriangulation_isTriangle_zero_one_two {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ T : Finset (Sym2 (ZMod n)), IsTriangulation T ∧
      IsTriangle T {((0 : ℕ) : ZMod n), ((1 : ℕ) : ZMod n), ((2 : ℕ) : ZMod n)} := by
  have v0 : ((0 : ℕ) : ZMod n).val = 0 := ZMod.val_natCast_of_lt (by omega)
  have v1 : ((1 : ℕ) : ZMod n).val = 1 := ZMod.val_natCast_of_lt (by omega)
  have v2 : ((2 : ℕ) : ZMod n).val = 2 := ZMod.val_natCast_of_lt (by omega)
  have key : ∀ T : Finset (Sym2 (ZMod n)),
      s(((0 : ℕ) : ZMod n), ((2 : ℕ) : ZMod n)) ∈ segments T →
        IsTriangle T {((0 : ℕ) : ZMod n), ((1 : ℕ) : ZMod n), ((2 : ℕ) : ZMod n)} := by
    intro T h02
    have h01 : s(((0 : ℕ) : ZMod n), ((1 : ℕ) : ZMod n)) ∈ segments T :=
      mem_segments.2 (Or.inr (by rw [isSide_mk_iff_val, v0, v1]; omega))
    have h12 : s(((1 : ℕ) : ZMod n), ((2 : ℕ) : ZMod n)) ∈ segments T :=
      mem_segments.2 (Or.inr (by rw [isSide_mk_iff_val, v1, v2]; omega))
    refine ⟨?_, ?_⟩
    · rw [card_insert_of_notMem (by
          rw [mem_insert, mem_singleton, eq_iff_val, eq_iff_val, v0, v1, v2]; omega),
        card_insert_of_notMem (by rw [mem_singleton, eq_iff_val, v1, v2]; omega),
        card_singleton]
    · simp only [mem_insert, mem_singleton]
      rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl) huv
      all_goals first
        | exact absurd rfl huv
        | assumption
        | (rw [Sym2.eq_swap]; assumption)
  rcases Nat.lt_or_ge n 4 with h | h
  · refine ⟨∅, ⟨fun e he => by simp at he, fun e he => by simp at he, fun e he _ => ?_⟩,
      key ∅ ?_⟩
    · exfalso
      induction e using Sym2.ind with | _ x y => ?_
      rw [isDiagonal_mk_iff_val] at he
      have := ZMod.val_lt x
      have := ZMod.val_lt y
      omega
    · exact mem_segments.2 (Or.inr (by rw [isSide_mk_iff_val, v0, v2]; omega))
  · have hdiag : IsDiagonal s(((0 : ℕ) : ZMod n), ((2 : ℕ) : ZMod n)) := by
      rw [isDiagonal_mk_iff_val, v0, v2]
      omega
    obtain ⟨T, hT, hsub⟩ := exists_isTriangulation_superset
      (S := {s(((0 : ℕ) : ZMod n), ((2 : ℕ) : ZMod n))})
      (by simpa only [mem_singleton, forall_eq] using hdiag)
      (by simp only [mem_singleton, forall_eq]; exact not_cross_self _)
    exact ⟨T, hT, key T (mem_segments.2 (Or.inl (hsub (mem_singleton_self _))))⟩

/-- **A corner triangulation with a prescribed ear.** If the vertex of `a` has at least three
darts, it has a corner triangulation of which `{σ(a), a, σ⁻¹(a)}` is a triangle. -/
theorem exists_isCornerTriangulation_isCornerTriangle {a : H} (ha : 3 ≤ (R.vertexOf a).card) :
    ∃ D, R.IsCornerTriangulation (R.vertexOf a) D ∧
      R.IsCornerTriangle (R.vertexOf a) D {R.rot a, a, R.rot.symm a} := by
  obtain ⟨n, hn⟩ : ∃ n, (R.vertexOf a).card = n := ⟨_, rfl⟩
  rw [hn] at ha
  haveI : NeZero n := ⟨by omega⟩
  have hl := isCornerLabelling_rot_symm_pow (R := R) (R.rot a) (n := n) (by rw [R.vertexOf_rot, hn])
  rw [R.vertexOf_rot] at hl
  obtain ⟨T, hT, htri⟩ := exists_isTriangulation_isTriangle_zero_one_two ha
  refine ⟨T.image (Sym2.map fun i : ZMod n => (R.rot.symm ^ i.val) (R.rot a)),
    (hl.isCornerTriangulation_image_iff T).2 hT, ?_⟩
  have := (hl.isCornerTriangle_image_iff
    {((0 : ℕ) : ZMod n), ((1 : ℕ) : ZMod n), ((2 : ℕ) : ZMod n)}).2
    (by rwa [hl.cornerPullback_image])
  convert this using 1
  have v0 : ((0 : ℕ) : ZMod n).val = 0 := ZMod.val_natCast_of_lt (by omega)
  have v1 : ((1 : ℕ) : ZMod n).val = 1 := ZMod.val_natCast_of_lt (by omega)
  have v2 : ((2 : ℕ) : ZMod n).val = 2 := ZMod.val_natCast_of_lt (by omega)
  simp only [image_insert, image_singleton, v0, v1, v2, pow_zero, pow_one, sq,
    Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Equiv.symm_apply_apply]

end RotationSystem

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- **A corner triangulation with a prescribed ear**. Let `w` be a crossing of `G` and `a ∈ w`.
Then `w` has a corner triangulation of which `{σ(a), a, σ⁻¹(a)}` is a triangle. -/
@[cluster_algebras "lem_ear_datum"]
theorem IsCrossing.exists_isCornerTriangulation_isCornerTriangle {w : Finset H}
    (hw : G.IsCrossing w) {a : H} (ha : a ∈ w) :
    ∃ D, G.IsCornerTriangulation w D ∧ G.IsCornerTriangle w D {G.rot a, a, G.rot.symm a} := by
  obtain ⟨x, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hw.1).1
  rw [← G.vertexOf_eq_of_mem ha] at hw ⊢
  exact RotationSystem.exists_isCornerTriangulation_isCornerTriangle hw.three_le_card

/-! ### Contracting an edge at a bivalent vertex -/

section BivalentEnd

open Equiv

variable {d : H} (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
  (hd : G.IsBivalentRemovable d)

include hG hd in
/-- `a ∉ {d, d̄}` iff the transposition of `σ d` and `d̄` sends `a` outside `{d, σ d}`. -/
theorem mem_compl_pair_iff_swap_mem_compl (a : H) :
    a ∈ (({d, G.inv d} : Set H)ᶜ : Set H) ↔
      swap (G.rot d) (G.inv d) a ∈ (({d, G.rot d} : Set H)ᶜ : Set H) := by
  have h1 : G.rot d ≠ d := hd.rot_ne
  have h2 : G.inv d ≠ d := hG.inv_ne d
  have h3 : G.rot d ≠ G.inv d := hd.inv_ne_rot.symm
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  by_cases ha1 : a = G.rot d
  · subst ha1
    rw [swap_apply_left]
    exact ⟨fun _ => ⟨h2, h3.symm⟩, fun _ => ⟨h1, h3⟩⟩
  · by_cases ha2 : a = G.inv d
    · subst ha2
      rw [swap_apply_right]
      exact ⟨fun h => (h.2 rfl).elim, fun h => (h.2 rfl).elim⟩
    · rw [swap_apply_of_ne_of_ne ha1 ha2]
      exact ⟨fun h => ⟨h.1, ha1⟩, fun h => ⟨h.1, ha2⟩⟩

/-- The bijection `H \ {d, d̄} → H \ {d, σ d}` sending `σ d` to `d̄` and fixing the other
darts. -/
def bivalentEndEquiv :
    (({d, G.inv d} : Set H)ᶜ : Set H) ≃ (({d, G.rot d} : Set H)ᶜ : Set H) :=
  (swap (G.rot d) (G.inv d)).subtypeEquiv (mem_compl_pair_iff_swap_mem_compl hG hd)

/-- `bivalentEndEquiv` is the transposition of `σ d` and `d̄` on darts. -/
@[simp]
theorem coe_bivalentEndEquiv (x : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (bivalentEndEquiv hG hd x : H) = swap (G.rot d) (G.inv d) x := rfl

/-- **A contraction at a bivalent vertex is a removal**. Let `{d, d̄}` be an edge whose ends are
distinct internal vertices of the same colour, such that `v(d)` consists of exactly two darts `d`
and `f = σ d`, with `f ≠ d̄`. The map `H \ {d, d̄} → H \ {d, f}` sending `f ↦ d̄` and fixing the
other darts is an isomorphism from the contraction along `{d, d̄}` to the removal of `v(d)` (with
`d₁ = d`, `d₂ = f`). -/
@[cluster_algebras "lem_contraction_bivalent_end"]
noncomputable def contractEdgeIsoBivalentRemoval
    {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)} :
    (G.contractEdge d hleg).Iso (G.bivalentRemoval hG hd) where
  toEquiv := bivalentEndEquiv hG hd
  map_inv x := by
    have hinv := hG.inv_involutive
    have hx := mem_compl_pair_iff.1 x.2
    have hfd : G.inv (G.rot d) ≠ G.rot d := hG.inv_ne _
    have hfd' : G.inv (G.rot d) ≠ G.inv d := fun h => hd.rot_ne (G.inv.injective h)
    apply Subtype.ext
    rw [coe_bivalentEndEquiv, coe_contractEdge_inv hinv]
    by_cases h1 : (x : H) = G.rot d
    · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd
        (by rw [coe_bivalentEndEquiv, h1, swap_apply_left]), h1,
        swap_apply_of_ne_of_ne hfd hfd']
    · by_cases h2 : (x : H) = G.inv (G.rot d)
      · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd
          (by rw [coe_bivalentEndEquiv, h2, swap_apply_of_ne_of_ne hfd hfd']), h2, hinv,
          swap_apply_left]
      · have hx1 : G.inv x ≠ G.rot d := fun h => h2 (by rw [← h, hinv])
        have hx2 : G.inv x ≠ G.inv d := fun h => hx.1 (G.inv.injective h)
        have hy : (bivalentEndEquiv hG hd x : H) = x := by
          rw [coe_bivalentEndEquiv, swap_apply_of_ne_of_ne h1 hx.2]
        rw [coe_bivalentRemoval_inv_of_ne hG hd (by rw [hy]; exact hx.2) (by rw [hy]; exact h2),
          hy, swap_apply_of_ne_of_ne hx1 hx2]
  map_rot x := by
    have hx := mem_compl_pair_iff.1 x.2
    have hsc : ¬G.rot.SameCycle d (G.inv d) := he.not_sameCycle
    have hfmem : G.rot d ∈ (({d, G.inv d} : Set H)ᶜ : Set H) :=
      mem_compl_pair_iff.2 ⟨hd.rot_ne, hd.inv_ne_rot.symm⟩
    apply Subtype.ext
    rw [coe_bivalentEndEquiv, coe_bivalentRemoval_rot, coe_bivalentEndEquiv]
    by_cases h1 : (x : H) = G.rot d
    · have hσx : G.rot x = d := by rw [h1, hd.rot_rot]
      rw [h1, swap_apply_left]
      by_cases hl : G.rot (G.inv d) = G.inv d
      · rw [coe_contractEdge_rot_of_eq_of_eq hσx hl hfmem, swap_apply_left, hl]
      · have hne1 : G.rot (G.inv d) ≠ d := fun h =>
          hsc (Equiv.Perm.SameCycle.symm ⟨1, by rwa [zpow_one]⟩)
        have hne2 : G.rot (G.inv d) ≠ G.rot d := fun h => hG.inv_ne d (G.rot.injective h)
        rw [coe_contractEdge_rot_of_eq hσx (mem_compl_pair_iff.2 ⟨hne1, hl⟩),
          swap_apply_of_ne_of_ne hne2 hl]
    · have hy : swap (G.rot d) (G.inv d) (x : H) = x := swap_apply_of_ne_of_ne h1 hx.2
      rw [hy]
      by_cases h2 : G.rot x = G.inv d
      · rw [coe_contractEdge_rot_of_eq_inv h2 hfmem, swap_apply_left, h2]
      · have h3 : G.rot x ≠ d := fun h => h1 (G.rot.injective (by rw [h, hd.rot_rot]))
        have h4 : G.rot x ≠ G.rot d := fun h => hx.1 (G.rot.injective h)
        rw [coe_contractEdge_rot_of_mem (mem_compl_pair_iff.2 ⟨h3, h2⟩),
          swap_apply_of_ne_of_ne h4 h2]
  mem_bdry_iff x := by
    have hx := mem_compl_pair_iff.1 x.2
    rw [mem_bivalentRemoval_bdry, mem_contractEdge_bdry, coe_bivalentEndEquiv]
    by_cases h1 : (x : H) = G.rot d
    · rw [h1, swap_apply_left]
      exact ⟨fun h => (hd.inv_notMem_bdry hG h).elim, fun h => (hd.rot_notMem_bdry h).elim⟩
    · rw [swap_apply_of_ne_of_ne h1 hx.2]
  map_colour x _ := by
    have hx := mem_compl_pair_iff.1 x.2
    rw [bivalentRemoval_colour, contractEdge_colour, coe_bivalentEndEquiv]
    by_cases h1 : (x : H) = G.rot d
    · rw [h1, swap_apply_left, he.colour_inv, hG.colour_rot d hd.not_isBoundaryVertex]
    · rw [swap_apply_of_ne_of_ne h1 hx.2]
  map_bvertex i := by
    rw [(IsPlabicGraph.contractEdge hG he).filter_bvertex_notMem_bdry,
      (isPlabicGraph_bivalentRemoval hG hd).filter_bvertex_notMem_bdry, map_singleton]
    congr 1
    apply Subtype.ext
    have h1 := hd.leg_mem hG i
    have h2 := mem_compl_pair_iff.1 (he.leg_mem hG i)
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h1
    rw [Equiv.toEmbedding_apply, coe_bivalentEndEquiv, coe_contractEdge_leg,
      coe_bivalentRemoval_leg,
      swap_apply_of_ne_of_ne h1.2 h2.2]

include he in
/-- **A contraction at a bivalent vertex is a removal**: the contraction along `{d, d̄}` is
isomorphic to the removal of `v(d) = {d, σ d}`. -/
@[cluster_algebras "lem_contraction_bivalent_end"]
theorem contractEdge_isomorphic_bivalentRemoval
    {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)} :
    (G.contractEdge d hleg).Isomorphic (G.bivalentRemoval hG hd) :=
  ⟨contractEdgeIsoBivalentRemoval (hG := hG) (he := he) (hd := hd)⟩

end BivalentEnd

end PlabicData

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.PolygonTriangulation

/-!
# The crossing number of a segment with respect to a triangulation

For a triangulation `T` of the convex `m`-gon and a segment `ζ`, the crossing number `κ_T(ζ)`
counts the elements of `T` that cross `ζ`. It is the induction measure of FWZ's Chapter 1: if a
diagonal `{x, y} ∈ T` crosses `{p, q}`, then replacing `{p, q}` by any of the four segments
`{r, w}` with `r ∈ {p, q}` and `w ∈ {x, y}` strictly lowers it.

The reason is a containment of arcs. With `p, x, q, y` in cyclic order, every segment crossing
`{q, x}` (say) without crossing `{x, y}` has one endpoint in the arc from `x` to `q` and the
other in the arc from `q` round to `y`, so it crosses `{p, q}`; and `{x, y}` itself crosses
`{p, q}` but not `{q, x}`, with which it shares the endpoint `x`.

## Main definitions

* `ClusterAlgebras.crossingNumber T ζ`: the number of elements of `T` crossing `ζ`.

## Main results

* `ClusterAlgebras.crossingNumber_eq_zero_iff`, `ClusterAlgebras.crossingNumber_pos_iff`: the
  crossing number vanishes exactly when nothing in `T` crosses `ζ`.
* `ClusterAlgebras.cross_mk_left_iff`: `s(a, b)` crosses `f` exactly when `f` has one endpoint
  in each of the arcs `Set.cIoo a b` and `Set.cIoo b a`.
* `ClusterAlgebras.not_cross_of_mem_of_mem`: segments sharing an endpoint do not cross.
* `ClusterAlgebras.crossingNumber_lt`: the crossing number decreases as described above.

## Implementation notes

* **The crossing number takes no hypotheses.** FWZ define `κ_T(ζ)` for a triangulation
  `T` and a segment `ζ`; the count makes sense for any finite set `T` of unordered pairs and any
  `ζ : Sym2 (ZMod m)`, so `crossingNumber` is defined in that generality.
* **The decrease uses only that `{x, y}` crosses nothing in `T`.** FWZ's proof says so;
  `crossingNumber_lt_of_forall_not_cross` is stated with that hypothesis alone, and
  `crossingNumber_lt` is FWZ's statement, derived from it. FWZ's hypothesis `p ≠ q`
  is implied by `sbtw p x q` and is not read.
* **The cyclic-order facts are proved on `Fin` and transferred.** Each is a statement about at
  most five points; on `Fin n` circular betweenness unfolds to a disjunction of `<`, and
  `ZMod (n + 1)` is `Fin (n + 1)` definitionally. They are kept to at most four betweenness
  hypotheses each, so that the arithmetic stays small.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 1.
-/

@[expose] public section

namespace ClusterAlgebras

variable {m : ℕ} [NeZero m]

/-! ### The crossing number -/

/-- The **crossing number** `κ_T(ζ)`: the number of elements of `T` that cross `ζ`.

FWZ ask `T` to be a triangulation of the convex `m`-gon and `ζ` a segment; the count
makes sense for any finite set and any element of `Sym2 (ZMod m)`, so no hypothesis is taken. -/
@[cluster_algebras "def_crossing_number"]
def crossingNumber (T : Finset (Sym2 (ZMod m))) (ζ : Sym2 (ZMod m)) : ℕ :=
  (T.filter fun δ => Cross δ ζ).card

/-- The crossing number vanishes exactly when no element of `T` crosses `ζ`. -/
theorem crossingNumber_eq_zero_iff {T : Finset (Sym2 (ZMod m))} {ζ : Sym2 (ZMod m)} :
    crossingNumber T ζ = 0 ↔ ∀ δ ∈ T, ¬Cross δ ζ := by
  simp [crossingNumber, Finset.filter_eq_empty_iff]

/-- The crossing number is positive exactly when some element of `T` crosses `ζ`. -/
theorem crossingNumber_pos_iff {T : Finset (Sym2 (ZMod m))} {ζ : Sym2 (ZMod m)} :
    0 < crossingNumber T ζ ↔ ∃ δ ∈ T, Cross δ ζ := by
  simp [crossingNumber, Finset.card_pos, Finset.filter_nonempty_iff]

/-! ### Crossing, in terms of the endpoints -/

/-- Crossing is a symmetric relation. -/
theorem cross_comm {e f : Sym2 (ZMod m)} : Cross e f ↔ Cross f e :=
  ⟨Cross.symm, Cross.symm⟩

omit [NeZero m] in
/-- `s(a, b)` crosses `f` exactly when the endpoints of `f` can be named `c, d` with `c` in the
arc from `a` to `b` and `d` in the arc from `b` to `a`: the endpoints of the first segment can
be taken as given, not merely up to a swap. -/
theorem cross_mk_left_iff {a b : ZMod m} {f : Sym2 (ZMod m)} :
    Cross s(a, b) f ↔ ∃ c d, f = s(c, d) ∧ sbtw a c b ∧ sbtw b d a := by
  refine ⟨?_, fun ⟨c, d, hf, h1, h2⟩ => ⟨a, b, c, d, rfl, hf, h1, h2⟩⟩
  rintro ⟨a', b', c, d, he, rfl, h1, h2⟩
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨c, d, rfl, h1, h2⟩
  · exact ⟨d, c, Sym2.eq_swap, h2, h1⟩

omit [NeZero m] in
/-- Two segments sharing an endpoint do not cross: the endpoints of crossing segments are
pairwise distinct. -/
theorem not_cross_of_mem_of_mem {e f : Sym2 (ZMod m)} {z : ZMod m} (he : z ∈ e) (hf : z ∈ f) :
    ¬Cross e f := by
  intro h
  obtain ⟨a, b, c, d, rfl, rfl, hab, hac, had, hbc, hbd, hcd⟩ := h.pairwise_ne
  rw [Sym2.mem_iff] at he hf
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;> contradiction

/-! ### Arcs of four points in cyclic order -/

/-- On `Fin n`: if `p, x, q, y` are in cyclic order, so are `x, q, y, p`. -/
private theorem sbtw_rotate_fin {n : ℕ} {p q x y : Fin n} (hx : sbtw p x q)
    (hy : sbtw q y p) : sbtw x q y ∧ sbtw y p x := by
  rw [Fin.sbtw_iff] at hx hy
  refine ⟨?_, ?_⟩ <;> rw [Fin.sbtw_iff] <;> simp only [Fin.lt_def] at hx hy ⊢ <;> omega

/-- On `Fin n`: if `q, y, p` are in cyclic order, a point of the arc `(q, x)` outside the arc
`(y, x)` lies in the arc `(q, p)`. -/
private theorem sbtw_of_not_sbtw_left_fin {n : ℕ} {p q x y v : Fin n}
    (hy : sbtw q y p) (hv : sbtw q v x) (hδ : ¬sbtw y v x) : sbtw q v p := by
  rw [Fin.sbtw_iff] at hy hv hδ ⊢
  simp only [Fin.lt_def] at hy hv hδ ⊢
  omega

/-- On `Fin n`: if `p, x, q, y` are in cyclic order, a point of the arc `(y, q)` outside the
arc `(y, x)` lies in the arc `(p, q)`. -/
private theorem sbtw_of_not_sbtw_right_fin {n : ℕ} {p q x y v : Fin n} (hx : sbtw p x q)
    (hy : sbtw q y p) (hv : sbtw y v q) (hδ : ¬sbtw y v x) : sbtw p v q := by
  rw [Fin.sbtw_iff] at hx hy hv hδ ⊢
  simp only [Fin.lt_def] at hx hy hv hδ ⊢
  omega

/-- If `p, x, q, y` are in cyclic order, so are `x, q, y, p`. -/
private theorem sbtw_rotate {p q x y : ZMod m} (hx : sbtw p x q) (hy : sbtw q y p) :
    sbtw x q y ∧ sbtw y p x := by
  match m, ‹NeZero m›, p, q, x, y, hx, hy with
  | (n + 1), _, p, q, x, y, hx, hy => exact sbtw_rotate_fin hx hy

/-- If `q, y, p` are in cyclic order, a point of the arc `(q, x)` outside the arc `(y, x)` lies
in the arc `(q, p)`. -/
private theorem sbtw_of_not_sbtw_left {p q x y v : ZMod m} (hy : sbtw q y p)
    (hv : sbtw q v x) (hδ : ¬sbtw y v x) : sbtw q v p := by
  match m, ‹NeZero m›, p, q, x, y, v, hy, hv, hδ with
  | (n + 1), _, p, q, x, y, v, hy, hv, hδ => exact sbtw_of_not_sbtw_left_fin hy hv hδ

/-- If `p, x, q, y` are in cyclic order, a point of the arc `(y, q)` outside the arc `(y, x)`
lies in the arc `(p, q)`. -/
private theorem sbtw_of_not_sbtw_right {p q x y v : ZMod m} (hx : sbtw p x q)
    (hy : sbtw q y p) (hv : sbtw y v q) (hδ : ¬sbtw y v x) : sbtw p v q := by
  match m, ‹NeZero m›, p, q, x, y, v, hx, hy, hv, hδ with
  | (n + 1), _, p, q, x, y, v, hx, hy, hv, hδ => exact sbtw_of_not_sbtw_right_fin hx hy hv hδ

/-! ### The decrease of the crossing number -/

/-- Let `p, x, q, y` be in cyclic order. A segment `ε` crossing `{q, x}` but not `{x, y}`
crosses `{p, q}`. -/
theorem Cross.cross_of_not_cross_left {p q x y : ZMod m} {ε : Sym2 (ZMod m)}
    (hε : Cross ε s(q, x)) (hx : sbtw p x q) (hy : sbtw q y p) (hδ : ¬Cross ε s(x, y)) :
    Cross ε s(p, q) := by
  rw [cross_comm, Sym2.eq_swap, cross_mk_left_iff] at hε
  obtain ⟨u, v, rfl, hu, hv⟩ := hε
  -- `u` lies in the arc `(x, y)`, so `v` cannot lie in the arc `(y, x)`
  have hxy : sbtw x u y := sbtw_trans_right hu (sbtw_rotate hx hy).1
  have hv' : ¬sbtw y v x := fun h =>
    hδ (cross_comm.1 (cross_mk_left_iff.2 ⟨u, v, rfl, hxy, h⟩))
  exact cross_comm.1 (cross_mk_left_iff.2
    ⟨u, v, rfl, sbtw_trans_left hx hu, sbtw_of_not_sbtw_left hy hv hv'⟩)

/-- Let `p, x, q, y` be in cyclic order. A segment `ε` crossing `{q, y}` but not `{x, y}`
crosses `{p, q}`. -/
theorem Cross.cross_of_not_cross_right {p q x y : ZMod m} {ε : Sym2 (ZMod m)}
    (hε : Cross ε s(q, y)) (hx : sbtw p x q) (hy : sbtw q y p) (hδ : ¬Cross ε s(x, y)) :
    Cross ε s(p, q) := by
  rw [cross_comm, cross_mk_left_iff] at hε
  obtain ⟨u, v, rfl, hu, hv⟩ := hε
  -- `u` lies in the arc `(x, y)`, so `v` cannot lie in the arc `(y, x)`
  have hxy : sbtw x u y := sbtw_trans_left (sbtw_rotate hx hy).1 hu
  have hv' : ¬sbtw y v x := fun h =>
    hδ (cross_comm.1 (cross_mk_left_iff.2 ⟨u, v, rfl, hxy, h⟩))
  exact cross_comm.1 (cross_mk_left_iff.2 ⟨v, u, Sym2.eq_swap,
    sbtw_of_not_sbtw_right hx hy hv hv', sbtw_trans_right hu hy⟩)

/-- **The crossing number decreases**, under the only hypothesis on `T` the argument reads:
`{x, y}` is an element of `T` crossing no element of `T`. If `x` lies in the arc from `p` to
`q` and `y` in the arc from `q` to `p`, then `κ_T({r, w}) < κ_T({p, q})` for `r ∈ {p, q}` and
`w ∈ {x, y}`. -/
theorem crossingNumber_lt_of_forall_not_cross {T : Finset (Sym2 (ZMod m))}
    {p q x y : ZMod m} (hxy : s(x, y) ∈ T) (hT : ∀ ε ∈ T, ¬Cross ε s(x, y))
    (hx : sbtw p x q) (hy : sbtw q y p) {r w : ZMod m} (hr : r = p ∨ r = q)
    (hw : w = x ∨ w = y) :
    crossingNumber T s(r, w) < crossingNumber T s(p, q) := by
  -- every element of `T` crossing `{r, w}` crosses `{p, q}`
  have hsub : T.filter (fun ε => Cross ε s(r, w)) ⊆ T.filter (fun ε => Cross ε s(p, q)) := by
    intro ε
    simp only [Finset.mem_filter]
    refine fun ⟨hεT, hε⟩ => ⟨hεT, ?_⟩
    have hδ := hT ε hεT
    rcases hr with rfl | rfl <;> rcases hw with rfl | rfl
    · -- the case `r = p` is the case `r = q` for the quadruple `(q, p, y, x)`
      rw [Sym2.eq_swap (a := r)]
      exact hε.cross_of_not_cross_right hy hx (by rwa [Sym2.eq_swap])
    · rw [Sym2.eq_swap (a := r)]
      exact hε.cross_of_not_cross_left hy hx (by rwa [Sym2.eq_swap])
    · exact hε.cross_of_not_cross_left hx hy hδ
    · exact hε.cross_of_not_cross_right hx hy hδ
  -- and `{x, y}` crosses `{p, q}` but not `{r, w}`, with which it shares `w`
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨s(x, y), ?_, ?_⟩)
  · obtain ⟨h1, h2⟩ := sbtw_rotate hx hy
    exact Finset.mem_filter.2 ⟨hxy, cross_mk_left_iff.2 ⟨q, p, Sym2.eq_swap, h1, h2⟩⟩
  · exact fun h => not_cross_of_mem_of_mem (Sym2.mem_iff.2 hw) (Sym2.mem_mk_right r w)
      (Finset.mem_filter.1 h).2

/-- **The crossing number decreases.** Let `T` be a triangulation, `p ≠ q`, and `{x, y} ∈ T`
with `x` strictly between `p` and `q` and `y` strictly between `q` and `p`. Then
`κ_T({r, w}) < κ_T({p, q})` for every `r ∈ {p, q}` and every `w ∈ {x, y}`.

Only the non-crossing property of `T` is used (see `crossingNumber_lt_of_forall_not_cross`),
and `p ≠ q` already follows from `sbtw p x q`. -/
@[cluster_algebras "lem_crossing_number_decreases"]
theorem crossingNumber_lt {T : Finset (Sym2 (ZMod m))} (hT : IsTriangulation T)
    {p q x y : ZMod m} (_hpq : p ≠ q) (hxy : s(x, y) ∈ T) (hx : sbtw p x q) (hy : sbtw q y p)
    {r w : ZMod m} (hr : r = p ∨ r = q) (hw : w = x ∨ w = y) :
    crossingNumber T s(r, w) < crossingNumber T s(p, q) :=
  crossingNumber_lt_of_forall_not_cross hxy (fun ε hε => hT.noncrossing ε hε _ hxy) hx hy hr hw

end ClusterAlgebras

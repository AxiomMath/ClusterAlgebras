/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.FiniteType.External
public import ClusterAlgebras.MatrixMutation
public import ClusterAlgebras.ExchangeMatrix

/-!
# Triangulations of a polygon: intervals, rotations, flips and exchange matrices

Facts about triangulations of a polygon with vertices `ZMod m`, used for the cluster algebras
of type `C_n`: cyclic intervals, invariance under rotations, existence and uniqueness of flips,
and the exchange matrix `B(T, λ)` of a triangulation whose diagonals are labelled by `Fin N`,
which changes by matrix mutation under a flip.

## Main definitions

* `ClusterAlgebras.TypeBC.triangulationMatrix T ℓ`: the matrix `B(T, λ)`.
* `ClusterAlgebras.TypeBC.IsTriangulationLabelling T ℓ`: `ℓ` is a bijection from `Fin N` onto
  `T`.

## Main statements

* `ClusterAlgebras.TypeBC.sbtw_iff_val_sub_of_lt` and its companions: cyclic intervals.
* `ClusterAlgebras.TypeBC.IsTriangulation.image_map_add`,
  `ClusterAlgebras.TypeBC.polygonArrows_image_map_add`: rotations preserve triangulations and
  their quivers.
* `ClusterAlgebras.TypeBC.exists_flip`: every diagonal of a triangulation can be flipped, in
  exactly one way.
* `ClusterAlgebras.TypeBC.triangulationMatrix_update_flip`: a flip mutates `B(T, λ)`.

## Implementation notes

* The set `(x, y)` of vertices strictly between `x` and `y` is Mathlib's `Set.cIoo x y`, the
  set of `z` with `sbtw x z y`, as in `ClusterAlgebras.Cross`. The representative `p_a(z)` of
  `z - a` in `[0, m - 1]` is `(z - a).val`.
* The rotation `τ : x ↦ x + t` acts on segments by `Sym2.map (· + t)` and on sets of segments by
  `Finset.image`.
* The labelling `λ` of a triangulation `T` is a function `ℓ : Fin N → Sym2 (ZMod m)` together
  with the condition `IsTriangulationLabelling T ℓ` (injective with range `T`); the matrix
  `B(T, ℓ)` is defined for every `T` and `ℓ`. Its entries are the signed counts of the arrow
  system `polygonArrows T` of the quiver `Q(T)` (`triangulationMatrix_apply` records that this is
  the arrow system of `polygonQuiver T`). The new labelling after a flip is `Function.update`.
* The statements assume only `[NeZero m]`, not `m ≥ 3`; the rotation statements about
  segments, triangles and arrows hold for every set of segments, not only triangulations; and in
  the cyclic interval statements the distinctness of `a, b, c` follows from `sbtw a b c`.
* Indices of labellings are `Fin N`, starting at `0`.
* All names carry the sub-namespace `ClusterAlgebras.TypeBC`, since the type-`A` section has
  its own versions of some of these polygon facts.
-/

@[expose] public section

namespace ClusterAlgebras

namespace TypeBC

variable {m : ℕ} [NeZero m]

/-! ### Circular betweenness through representatives

On `ZMod m` with `m ≠ 0`, `sbtw` unfolds (through `ZMod (n + 1) = Fin (n + 1)`) into a
disjunction of strict inequalities between the representatives `val`; together with the
formulas for the representatives of sums and differences, this reduces every statement about
cyclic intervals below to linear arithmetic, closed by `omega`. -/

/-- Circular betweenness on `ZMod m`, read on the representatives. -/
theorem sbtw_iff_val {x y z : ZMod m} :
    sbtw x y z ↔ (x.val < y.val ∧ y.val < z.val) ∨ (y.val < z.val ∧ z.val < x.val) ∨
      (z.val < x.val ∧ x.val < y.val) := by
  match m, ‹NeZero m›, x, y, z with
  | (n + 1), _, x, y, z => exact Fin.sbtw_iff

/-- The representative of a sum. -/
theorem val_add_ite (a b : ZMod m) :
    (a + b).val = if a.val + b.val < m then a.val + b.val else a.val + b.val - m := by
  split_ifs with h
  · exact ZMod.val_add_of_lt h
  · exact ZMod.val_add_of_le (not_lt.1 h)

/-- The representative of a difference. -/
private theorem val_sub_ite (a b : ZMod m) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else m + a.val - b.val := by
  have h := val_add_ite (a - b) b
  rw [sub_add_cancel] at h
  have := ZMod.val_lt (a - b)
  have := ZMod.val_lt a
  have := ZMod.val_lt b
  split_ifs at h ⊢ <;> omega

/-- The representative of `1`. -/
theorem val_one_ite : (1 : ZMod m).val = if m = 1 then 0 else 1 := by
  rw [ZMod.val_one_eq_one_mod]
  have := NeZero.ne m
  split_ifs with h
  · subst h; rfl
  · exact Nat.mod_eq_of_lt (by omega)

/-- Two elements of `ZMod m` are equal exactly when their representatives are. -/
theorem eq_iff_val {a b : ZMod m} : a = b ↔ a.val = b.val :=
  (ZMod.val_injective m).eq_iff.symm

omit [NeZero m] in
/-- `{x, y}` is a side exactly when `y = x + 1` or `x = y + 1`. -/
private theorem isSide_mk_iff {x y : ZMod m} : IsSide s(x, y) ↔ y = x + 1 ∨ x = y + 1 := by
  constructor
  · rintro ⟨i, hi⟩
    rcases Sym2.eq_iff.1 hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rintro (rfl | rfl)
    exacts [⟨x, rfl⟩, ⟨y, Sym2.eq_swap⟩]

omit [NeZero m] in
/-- Crossing of two segments given by their endpoints: the two ways of naming them. -/
theorem cross_mk_iff {a b c d : ZMod m} :
    Cross s(a, b) s(c, d) ↔ (sbtw a c b ∧ sbtw b d a) ∨ (sbtw a d b ∧ sbtw b c a) := by
  constructor
  · rintro ⟨a', b', c', d', he, hf, h1, h2⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases Sym2.eq_iff.1 hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    exacts [⟨a, b, c, d, rfl, rfl, h1, h2⟩, ⟨a, b, d, c, rfl, Sym2.eq_swap, h1, h2⟩]

/-- No vertex lies strictly between `i` and `i + 1`. -/
private theorem not_sbtw_add_one (i z : ZMod m) : ¬sbtw i z (i + 1) := by
  have := ZMod.val_lt i; have := ZMod.val_lt z
  rw [sbtw_iff_val, val_add_ite, val_one_ite]
  split_ifs <;> omega

/-- If no vertex lies strictly between `x ≠ y`, then `y = x + 1`. -/
private theorem eq_add_one_of_forall_not_sbtw {x y : ZMod m} (hxy : x ≠ y)
    (h : ∀ z, ¬sbtw x z y) : y = x + 1 := by
  by_contra hne
  apply h (x + 1)
  have := ZMod.val_lt x; have := ZMod.val_lt y
  rw [Ne, eq_iff_val] at hxy
  rw [eq_iff_val] at hne
  rw [sbtw_iff_val]
  simp only [val_add_ite, val_one_ite] at hne ⊢
  split_ifs at hne ⊢ <;> omega

/-! ### Cyclic intervals -/

/-- If `p_a(x) < p_a(y)`, where `p_a(z)` is the representative of `z - a` in `[0, m - 1]`, then
`(x, y) = {z : p_a(x) < p_a(z) < p_a(y)}`. -/
@[cluster_algebras "lem_bc_cyclic_intervals"]
theorem sbtw_iff_val_sub_of_lt {a x y : ZMod m} (hxy : (x - a).val < (y - a).val)
    (z : ZMod m) : sbtw x z y ↔ (x - a).val < (z - a).val ∧ (z - a).val < (y - a).val := by
  have := ZMod.val_lt a; have := ZMod.val_lt x; have := ZMod.val_lt y; have := ZMod.val_lt z
  rw [sbtw_iff_val]
  simp only [val_sub_ite] at hxy ⊢
  split_ifs at hxy ⊢ <;> omega

/-- If `p_a(x) < p_a(y)`, then `(y, x) = {z : p_a(z) > p_a(y)} ∪ {z : p_a(z) < p_a(x)}`. -/
@[cluster_algebras "lem_bc_cyclic_intervals"]
theorem sbtw_iff_val_sub_of_lt' {a x y : ZMod m} (hxy : (x - a).val < (y - a).val)
    (z : ZMod m) : sbtw y z x ↔ (y - a).val < (z - a).val ∨ (z - a).val < (x - a).val := by
  have := ZMod.val_lt a; have := ZMod.val_lt x; have := ZMod.val_lt y; have := ZMod.val_lt z
  rw [sbtw_iff_val]
  simp only [val_sub_ite] at hxy ⊢
  split_ifs at hxy ⊢ <;> omega

/-- For `x ≠ y`, the segment `{x, y}` is a side if and only if `(x, y) = ∅` or `(y, x) = ∅`. -/
@[cluster_algebras "lem_bc_cyclic_intervals"]
theorem isSide_iff_cIoo_eq_empty {x y : ZMod m} (hxy : x ≠ y) :
    IsSide s(x, y) ↔ Set.cIoo x y = ∅ ∨ Set.cIoo y x = ∅ := by
  rw [isSide_mk_iff, Set.eq_empty_iff_forall_notMem, Set.eq_empty_iff_forall_notMem]
  simp only [Set.mem_cIoo]
  exact ⟨Or.imp (by rintro rfl; exact not_sbtw_add_one x) (by rintro rfl; exact not_sbtw_add_one y),
    Or.imp (eq_add_one_of_forall_not_sbtw hxy) (eq_add_one_of_forall_not_sbtw hxy.symm)⟩

/-- If `b ∈ (a, c)`, then `c ∈ (b, a)`, `a ∈ (c, b)`, and `(a, c) = (a, b) ∪ {b} ∪ (b, c)`,
`(b, a) = (b, c) ∪ {c} ∪ (c, a)`, `(c, b) = (c, a) ∪ {a} ∪ (a, b)`. -/
@[cluster_algebras "lem_bc_cyclic_intervals"]
theorem cIoo_eq_union_of_sbtw {a b c : ZMod m} (h : sbtw a b c) :
    sbtw b c a ∧ sbtw c a b ∧
      Set.cIoo a c = Set.cIoo a b ∪ {b} ∪ Set.cIoo b c ∧
      Set.cIoo b a = Set.cIoo b c ∪ {c} ∪ Set.cIoo c a ∧
      Set.cIoo c b = Set.cIoo c a ∪ {a} ∪ Set.cIoo a b := by
  have := ZMod.val_lt a; have := ZMod.val_lt b; have := ZMod.val_lt c
  rw [sbtw_iff_val] at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sbtw_iff_val]; omega
  · rw [sbtw_iff_val]; omega
  all_goals
    ext z
    have := ZMod.val_lt z
    simp only [Set.mem_union, Set.mem_cIoo, Set.mem_singleton_iff, sbtw_iff_val, eq_iff_val]
    omega

/-- If `b ∈ (a, c)`, the three unions of `cIoo_eq_union_of_sbtw` are disjoint: the arcs `(a, b)`,
`(b, c)`, `(c, a)` are pairwise disjoint, and none contains the vertex separating it from the next
one. -/
@[cluster_algebras "lem_bc_cyclic_intervals"]
theorem disjoint_cIoo_of_sbtw {a b c : ZMod m} (h : sbtw a b c) :
    Disjoint (Set.cIoo a b) (Set.cIoo b c) ∧ Disjoint (Set.cIoo b c) (Set.cIoo c a) ∧
      Disjoint (Set.cIoo c a) (Set.cIoo a b) ∧
      b ∉ Set.cIoo a b ∪ Set.cIoo b c ∧ c ∉ Set.cIoo b c ∪ Set.cIoo c a ∧
      a ∉ Set.cIoo c a ∪ Set.cIoo a b := by
  have := ZMod.val_lt a; have := ZMod.val_lt b; have := ZMod.val_lt c
  rw [sbtw_iff_val] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [Set.disjoint_left]; intro z hz hz'
       have := ZMod.val_lt z
       simp only [Set.mem_cIoo, sbtw_iff_val] at hz hz'
       omega)
    | (simp only [Set.mem_union, Set.mem_cIoo, sbtw_iff_val]; omega)

/-! ### Rotations -/

/-- **Rotations preserve strict betweenness**: `z ∈ (x, y)` if and only if `τ(z) ∈ (τ(x), τ(y))`,
for `τ : x ↦ x + t`. -/
@[cluster_algebras "lem_bc_rotation_invariance"]
theorem sbtw_add_right_iff (t : ZMod m) {x y z : ZMod m} :
    sbtw (x + t) (z + t) (y + t) ↔ sbtw x z y := by
  have := ZMod.val_lt x; have := ZMod.val_lt y; have := ZMod.val_lt z; have := ZMod.val_lt t
  simp only [sbtw_iff_val, val_add_ite]
  split_ifs <;> omega

/-- **Rotations preserve clockwise listings.** -/
@[cluster_algebras "lem_bc_rotation_invariance"]
theorem isClockwise_add_right_iff (t : ZMod m) {a₁ a₂ a₃ : ZMod m} :
    IsClockwise (a₁ + t) (a₂ + t) (a₃ + t) ↔ IsClockwise a₁ a₂ a₃ :=
  sbtw_add_right_iff t

omit [NeZero m] in
/-- A rotation is injective on segments. -/
private theorem map_add_injective (t : ZMod m) :
    Function.Injective (Sym2.map (· + t : ZMod m → ZMod m)) :=
  Sym2.map.injective (add_left_injective t)

omit [NeZero m] in
/-- Every segment is the rotation of a segment. -/
private theorem map_sub_map_add (t : ZMod m) (e : Sym2 (ZMod m)) :
    (e.map (· - t)).map (· + t) = e := by
  induction e using Sym2.ind with
  | _ x y => simp only [Sym2.map_mk, sub_add_cancel]

omit [NeZero m] in
/-- Every finite set of vertices is the rotation of a finite set of vertices. -/
private theorem image_sub_image_add (t : ZMod m) (Δ : Finset (ZMod m)) :
    (Δ.image (· - t)).image (· + t) = Δ := by
  simp [Finset.image_image, Function.comp_def]

omit [NeZero m] in
/-- **Rotations permute the sides.** -/
@[cluster_algebras "lem_bc_rotation_invariance"]
theorem isSide_map_add_iff (t : ZMod m) (e : Sym2 (ZMod m)) :
    IsSide (e.map (· + t)) ↔ IsSide e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [Sym2.map_mk, isSide_mk_iff, isSide_mk_iff, add_right_comm x, add_right_comm y,
      add_left_inj, add_left_inj]

omit [NeZero m] in
/-- **Rotations permute the diagonals.** -/
@[cluster_algebras "lem_bc_rotation_invariance"]
theorem isDiagonal_map_add_iff (t : ZMod m) (e : Sym2 (ZMod m)) :
    IsDiagonal (e.map (· + t)) ↔ IsDiagonal e := by
  simp only [IsDiagonal, IsSegment, Sym2.isDiag_map (add_left_injective t), isSide_map_add_iff]

/-- **Rotations preserve crossing.** -/
@[cluster_algebras "lem_bc_rotation_invariance"]
theorem cross_map_add_iff (t : ZMod m) (e f : Sym2 (ZMod m)) :
    Cross (e.map (· + t)) (f.map (· + t)) ↔ Cross e f := by
  induction e using Sym2.ind with
  | _ a b =>
  induction f using Sym2.ind with
  | _ c d =>
    simp only [Sym2.map_mk, cross_mk_iff, sbtw_add_right_iff]

/-- **The rotation of a triangulation is a triangulation.** -/
@[cluster_algebras "lem_bc_rotation_invariance"]
theorem IsTriangulation.image_map_add (t : ZMod m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) : IsTriangulation (T.image (Sym2.map (· + t))) where
  isDiagonal e he := by
    obtain ⟨e, he', rfl⟩ := Finset.mem_image.1 he
    exact (isDiagonal_map_add_iff t e).2 (hT.isDiagonal e he')
  noncrossing e he f hf := by
    obtain ⟨e, he', rfl⟩ := Finset.mem_image.1 he
    obtain ⟨f, hf', rfl⟩ := Finset.mem_image.1 hf
    rw [cross_map_add_iff]
    exact hT.noncrossing e he' f hf'
  maximal e he heT := by
    rw [← map_sub_map_add t e] at he heT ⊢
    rw [isDiagonal_map_add_iff] at he
    rw [(map_add_injective t).mem_finset_image] at heT
    obtain ⟨f, hf, hcross⟩ := hT.maximal _ he heT
    exact ⟨f.map (· + t), Finset.mem_image_of_mem _ hf, (cross_map_add_iff t _ _).2 hcross⟩

/-- **The segments of a rotated triangulation are the rotated segments.** Stated for every set `T`
of segments. -/
@[cluster_algebras "lem_bc_rotation_invariance"]
theorem segments_image_map_add (t : ZMod m) (T : Finset (Sym2 (ZMod m))) :
    segments (T.image (Sym2.map (· + t))) = (segments T).image (Sym2.map (· + t)) := by
  ext e
  rw [← map_sub_map_add t e, (map_add_injective t).mem_finset_image, mem_segments,
    mem_segments, (map_add_injective t).mem_finset_image, isSide_map_add_iff]

/-- A finite set of vertices is a triangle of `T` exactly when its rotation is a triangle of the
rotation of `T`. -/
private theorem isTriangle_image_map_add_iff (t : ZMod m) (T : Finset (Sym2 (ZMod m)))
    (Δ : Finset (ZMod m)) :
    IsTriangle (T.image (Sym2.map (· + t))) (Δ.image (· + t)) ↔ IsTriangle T Δ := by
  rw [IsTriangle, IsTriangle, Finset.card_image_of_injective _ (add_left_injective t)]
  simp only [Finset.forall_mem_image, (add_left_injective t).ne_iff, segments_image_map_add]
  refine and_congr_right fun _ => ?_
  refine forall₂_congr fun u _ => forall₂_congr fun v _ => imp_congr_right fun _ => ?_
  rw [← Sym2.map_mk (· + t), (map_add_injective t).mem_finset_image]

/-- **The triangles of a rotated triangulation are the rotated triangles.** Stated for every set
`T` of segments. -/
@[cluster_algebras "lem_bc_rotation_invariance"]
theorem setOf_isTriangle_image_map_add (t : ZMod m) (T : Finset (Sym2 (ZMod m))) :
    {Δ | IsTriangle (T.image (Sym2.map (· + t))) Δ} =
      (fun Δ : Finset (ZMod m) => Δ.image (· + t)) '' {Δ | IsTriangle T Δ} := by
  ext Δ
  rw [← image_sub_image_add t Δ, Set.mem_setOf_eq, isTriangle_image_map_add_iff,
    (Finset.image_injective (add_left_injective t)).mem_set_image]
  rfl

/-- A finite set of vertices carries an arrow `s → s'` of `Q(T)` exactly when its rotation
carries the rotated arrow of `Q(τ(T))`. -/
private theorem mem_arrowTriangles_image_map_add_iff (t : ZMod m) (T : Finset (Sym2 (ZMod m)))
    (s s' : Sym2 (ZMod m)) (Δ : Finset (ZMod m)) :
    Δ.image (· + t) ∈ arrowTriangles (T.image (Sym2.map (· + t))) (s.map (· + t))
        (s'.map (· + t)) ↔ Δ ∈ arrowTriangles T s s' := by
  rw [mem_arrowTriangles, mem_arrowTriangles, isTriangle_image_map_add_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨a, b, c, hcw, hs, hs', ha, hb, hc⟩
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b, hb', rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨c, hc', rfl⟩ := Finset.mem_image.1 hc
    rw [← Sym2.map_mk (· + t)] at hs hs'
    exact ⟨a, b, c, (sbtw_add_right_iff t).1 hcw, map_add_injective t hs,
      map_add_injective t hs', ha', hb', hc'⟩
  · rintro ⟨a, b, c, hcw, rfl, rfl, ha, hb, hc⟩
    exact ⟨a + t, b + t, c + t, (sbtw_add_right_iff t).2 hcw, rfl, rfl,
      Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb, Finset.mem_image_of_mem _ hc⟩

/-- **Rotations preserve the quiver of a triangulation**: the arrow systems `a` of `Q(T)` and `a^τ`
of `Q(τ(T))` satisfy `a^τ(τ(s), τ(s')) = a(s, s')`. Stated for every set `T` and all `s, s'`, not
only for the segments of a triangulation. -/
@[cluster_algebras "lem_bc_rotation_invariance"]
theorem polygonArrows_image_map_add (t : ZMod m) (T : Finset (Sym2 (ZMod m)))
    (s s' : Sym2 (ZMod m)) :
    polygonArrows (T.image (Sym2.map (· + t))) (s.map (· + t)) (s'.map (· + t)) =
      polygonArrows T s s' := by
  simp only [polygonArrows, isSide_map_add_iff]
  split_ifs
  · rfl
  · have : arrowTriangles (T.image (Sym2.map (· + t))) (s.map (· + t)) (s'.map (· + t)) =
        (arrowTriangles T s s').image (fun Δ => Δ.image (· + t)) := by
      ext Δ
      rw [← image_sub_image_add t Δ, mem_arrowTriangles_image_map_add_iff,
        (Finset.image_injective (add_left_injective t)).mem_finset_image]
    rw [this, Finset.card_image_of_injective _ (Finset.image_injective (add_left_injective t))]

/-! ### Flips -/

section FlipHelpers

variable {T : Finset (Sym2 (ZMod m))}

/-- No segment crosses a side. -/
theorem not_cross_of_isSide {σ τ : Sym2 (ZMod m)} (hτ : IsSide τ) : ¬Cross τ σ := by
  obtain ⟨i, rfl⟩ := hτ
  induction σ using Sym2.ind with | _ u v => ?_
  rw [cross_mk_iff]
  rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact not_sbtw_add_one i _ h

/-- No two segments of a triangulation cross. -/
private theorem not_cross_of_mem_segments (hT : IsTriangulation T) {σ τ : Sym2 (ZMod m)}
    (hσ : σ ∈ segments T) (hτ : τ ∈ segments T) : ¬Cross σ τ := by
  rcases mem_segments.1 hσ with hσ | hσ
  · rcases mem_segments.1 hτ with hτ | hτ
    · exact hT.noncrossing σ hσ τ hτ
    · exact fun h => not_cross_of_isSide hτ h.symm
  · exact not_cross_of_isSide hσ

/-- A segment of `T` crossed by some segment is a diagonal in `T`, not a side. -/
theorem mem_of_cross_of_mem_segments {σ τ : Sym2 (ZMod m)} (hσ : σ ∈ segments T)
    (h : Cross σ τ) : σ ∈ T :=
  (mem_segments.1 hσ).resolve_right fun hs => not_cross_of_isSide hs h

/-- A vertex of `(a, c)` lies in `(a, b)`, is `b`, or lies in `(b, c)`. -/
private theorem sbtw_split {a c u : ZMod m} (b : ZMod m) (hu : sbtw a u c) :
    sbtw a u b ∨ u = b ∨ sbtw b u c := by
  simp only [eq_iff_val, sbtw_iff_val] at hu ⊢
  omega

/-- **The apex over a diagonal.** For `{a, c} ∈ T` there is `b ∈ (a, c)` with `{a, b}` and
`{b, c}` segments of `T`: the `b ∈ (a, c)` farthest from `a` with `{a, b}` a segment of `T`. -/
private theorem exists_apex (hT : IsTriangulation T) {a c : ZMod m} (hac : s(a, c) ∈ T) :
    ∃ b, sbtw a b c ∧ s(a, b) ∈ segments T ∧ s(b, c) ∈ segments T := by
  have hdiag := hT.isDiagonal _ hac
  have hne : a ≠ c := fun h => hdiag.1 (Sym2.mk_isDiag_iff.2 h)
  obtain ⟨x, hx⟩ : ∃ x, sbtw a x c := by
    by_contra h
    push Not at h
    exact hdiag.2 ((isSide_iff_cIoo_eq_empty hne).2 (Or.inl (Set.eq_empty_iff_forall_notMem.2 h)))
  have h1 : sbtw a (a + 1) c := by
    have := ZMod.val_lt a; have := ZMod.val_lt x; have := ZMod.val_lt c
    rw [sbtw_iff_val] at hx ⊢; rw [val_add_ite, val_one_ite]; split_ifs <;> omega
  let S : Finset (ZMod m) := Finset.univ.filter fun x => sbtw a x c ∧ s(a, x) ∈ segments T
  have hS : a + 1 ∈ S :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, mem_segments.2 (Or.inr ⟨a, rfl⟩)⟩
  obtain ⟨b, hbS, hmax⟩ := Finset.exists_max_image S (fun x => (x - a).val) ⟨_, hS⟩
  obtain ⟨-, hb, hab⟩ := Finset.mem_filter.1 hbS
  refine ⟨b, hb, hab, ?_⟩
  by_contra hbc
  have hbne : b ≠ c := by rintro rfl; exact sbtw_irrefl_right hb
  obtain ⟨f, hf, hcross⟩ := hT.maximal s(b, c) ⟨fun h => hbne (Sym2.mk_isDiag_iff.1 h),
    fun h => hbc (mem_segments.2 (Or.inr h))⟩ fun h => hbc (mem_segments.2 (Or.inl h))
  have key : ∀ u v, s(u, v) ∈ T → sbtw b u c → sbtw c v b → False := by
    intro u v hf hu hv
    have hac' : ¬Cross s(a, c) s(u, v) := hT.noncrossing _ hac _ hf
    have hab' : ¬Cross s(a, b) s(u, v) :=
      not_cross_of_mem_segments hT hab (mem_segments.2 (Or.inl hf))
    have hua : sbtw a u c := by rw [sbtw_iff_val] at hb hu ⊢; omega
    have hu2 : sbtw b u a := by rw [sbtw_iff_val] at hb hu ⊢; omega
    have hva : ¬sbtw c v a := fun h => hac' (cross_mk_iff.2 (Or.inl ⟨hua, h⟩))
    have hvb : ¬sbtw a v b := fun h => hab' (cross_mk_iff.2 (Or.inr ⟨h, hu2⟩))
    have hv : v = a := by
      rw [eq_iff_val]; rw [sbtw_iff_val] at hb hv hva hvb; omega
    subst hv
    have hle := hmax u (Finset.mem_filter.2 ⟨Finset.mem_univ _, hua,
      mem_segments.2 (Or.inl (Sym2.eq_swap ▸ hf))⟩)
    have := ZMod.val_lt v; have := ZMod.val_lt b; have := ZMod.val_lt c; have := ZMod.val_lt u
    simp only [val_sub_ite] at hle
    rw [sbtw_iff_val] at hb hu
    split_ifs at hle <;> omega
  induction f using Sym2.ind with
  | _ u v =>
    rcases cross_mk_iff.1 hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key u v hf h1 h2
    · exact key v u (Sym2.eq_swap ▸ hf) h1 h2

/-- The apex over `{a, c}` is unique: two of them would give two crossing segments. -/
private theorem apex_unique (hT : IsTriangulation T) {a b b' c : ZMod m}
    (hb : sbtw a b c) (hab : s(a, b) ∈ segments T) (hbc : s(b, c) ∈ segments T)
    (hb' : sbtw a b' c) (hab' : s(a, b') ∈ segments T) (hb'c : s(b', c) ∈ segments T) :
    b = b' := by
  by_contra hne
  have : (sbtw a b b' ∧ sbtw b' c a) ∨ (sbtw a b' b ∧ sbtw b c a) := by
    rw [eq_iff_val] at hne; rw [sbtw_iff_val] at hb hb'
    simp only [sbtw_iff_val]; omega
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact not_cross_of_mem_segments hT hab' hbc (cross_mk_iff.2 (Or.inl ⟨h1, h2⟩))
  · exact not_cross_of_mem_segments hT hab hb'c (cross_mk_iff.2 (Or.inl ⟨h1, h2⟩))

/-- Three distinct vertices pairwise joined by segments of `T` form a triangle of `T`. -/
theorem isTriangle_of_mem_segments {a b c : ZMod m} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (h1 : s(a, b) ∈ segments T) (h2 : s(b, c) ∈ segments T)
    (h3 : s(a, c) ∈ segments T) :
    IsTriangle T {a, b, c} := by
  refine ⟨Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl) huv <;>
    first | exact absurd rfl huv | assumption | (rw [Sym2.eq_swap]; assumption)

/-- A segment crossing the diagonal `{a, c}` of the quadrilateral `a, b, c, d` is the other
diagonal `{b, d}` or crosses one of the four rims. -/
theorem quad_cross_left {a b c d : ZMod m} (hb : sbtw a b c) (hd : sbtw c d a)
    {u v : ZMod m} (he : Cross s(a, c) s(u, v)) :
    s(u, v) = s(b, d) ∨ ∃ ρ ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 (ZMod m))),
      Cross ρ s(u, v) := by
  suffices key : ∀ u v, sbtw a u c → sbtw c v a → s(u, v) = s(b, d) ∨
      ∃ ρ ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 (ZMod m))), Cross ρ s(u, v) by
    rcases cross_mk_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key u v h1 h2
    · rw [Sym2.eq_swap (a := u)]; exact key v u h1 h2
  intro u v hu hv
  rcases sbtw_split b hu with hu' | rfl | hu'
  · have : sbtw b v a := by rw [sbtw_iff_val] at hb hv ⊢; omega
    exact Or.inr ⟨_, by simp, cross_mk_iff.2 (Or.inl ⟨hu', this⟩)⟩
  · rcases sbtw_split d hv with hv' | rfl | hv'
    · have : sbtw d u c := by rw [sbtw_iff_val] at hb hd ⊢; omega
      exact Or.inr ⟨_, by simp, cross_mk_iff.2 (Or.inr ⟨hv', this⟩)⟩
    · exact Or.inl rfl
    · have : sbtw a u d := by rw [sbtw_iff_val] at hb hd ⊢; omega
      exact Or.inr ⟨_, by simp, cross_mk_iff.2 (Or.inr ⟨hv', this⟩)⟩
  · have : sbtw c v b := by rw [sbtw_iff_val] at hb hv ⊢; omega
    exact Or.inr ⟨_, by simp, cross_mk_iff.2 (Or.inl ⟨hu', this⟩)⟩

/-- A segment crossing the diagonal `{b, d}` of the quadrilateral `a, b, c, d` is the other
diagonal `{a, c}` or crosses one of the four rims. -/
theorem quad_cross_right {a b c d : ZMod m} (hb : sbtw a b c) (hd : sbtw c d a)
    {u v : ZMod m} (he : Cross s(b, d) s(u, v)) :
    s(u, v) = s(a, c) ∨ ∃ ρ ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 (ZMod m))),
      Cross ρ s(u, v) := by
  have h1 : sbtw b c d := by rw [sbtw_iff_val] at hb hd ⊢; omega
  have h2 : sbtw d a b := by rw [sbtw_iff_val] at hb hd ⊢; omega
  obtain h | ⟨ρ, hρ, h⟩ := quad_cross_left h1 h2 he
  · exact Or.inl (h.trans Sym2.eq_swap)
  · refine Or.inr ⟨ρ, ?_, h⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρ ⊢
    tauto

/-- The four rims `{a, b}, {b, c}, {c, d}, {d, a}` of a quadrilateral `a, b, c, d` with
segments of `T` as rims are segments of `T` other than `{a, c}`. -/
private theorem rims_mem_segments {a b c d : ZMod m} (hb : sbtw a b c) (hd : sbtw c d a)
    (hab : s(a, b) ∈ segments T) (hbc : s(b, c) ∈ segments T) (hcd : s(c, d) ∈ segments T)
    (hda : s(d, a) ∈ segments T) :
    ∀ ρ ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 (ZMod m))),
      ρ ∈ segments T ∧ ρ ≠ s(a, c) := by
  rw [sbtw_iff_val] at hb hd
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro ρ (rfl | rfl | rfl | rfl) <;> refine ⟨by assumption, ?_⟩ <;>
    simp only [Ne, Sym2.eq_iff, eq_iff_val] <;> omega

/-- The triangles of `T` containing `a` and `c` are `{a, b, c}` and `{a, c, d}`, for apexes
`b ∈ (a, c)` and `d ∈ (c, a)` over the diagonal `{a, c}`. -/
private theorem isTriangle_eq_of_apex (hT : IsTriangulation T) {a b c d : ZMod m}
    (hb : sbtw a b c) (hab : s(a, b) ∈ segments T) (hbc : s(b, c) ∈ segments T)
    (hd : sbtw c d a) (hcd : s(c, d) ∈ segments T) (hda : s(d, a) ∈ segments T)
    {Δ : Finset (ZMod m)} (hΔ : IsTriangle T Δ) (haΔ : a ∈ Δ) (hcΔ : c ∈ Δ) :
    Δ = {a, b, c} ∨ Δ = {a, c, d} := by
  have hac : a ≠ c := by rw [Ne, eq_iff_val]; rw [sbtw_iff_val] at hb; omega
  obtain ⟨x, hxΔ, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, c} : Finset (ZMod m))) (t := Δ) (by rw [hΔ.1, Finset.card_pair hac]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  have hΔeq : Δ = {a, c, x} := (Finset.eq_of_subset_of_card_le
    (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨haΔ, hcΔ, hxΔ⟩)
    (by rw [hΔ.1, Finset.card_eq_three.2 ⟨a, c, x, hac, Ne.symm hx.1, Ne.symm hx.2, rfl⟩])).symm
  have : sbtw a x c ∨ sbtw c x a := by
    obtain ⟨h1, h2⟩ := hx
    simp only [Ne, eq_iff_val] at h1 h2 hac
    simp only [sbtw_iff_val]; omega
  rcases this with h | h
  · obtain rfl := apex_unique hT hb hab hbc h (hΔ.2 a haΔ x hxΔ (Ne.symm hx.1))
      (hΔ.2 x hxΔ c hcΔ hx.2)
    exact Or.inl (by rw [hΔeq, Finset.pair_comm])
  · obtain rfl := apex_unique hT hd hcd hda h (hΔ.2 c hcΔ x hxΔ (Ne.symm hx.2))
      (hΔ.2 x hxΔ a haΔ hx.1)
    exact Or.inr hΔeq

/-- For apexes `b ∈ (a, c)` and `d ∈ (c, a)` over the diagonal `{a, c}` of `T`, the other
diagonal `{b, d}` of the quadrilateral `a, b, c, d` is a replacement for the flip at `{a, c}`. -/
private theorem isFlipReplacement_of_apex (hT : IsTriangulation T) {a b c d : ZMod m}
    (hγ : s(a, c) ∈ T) (hb : sbtw a b c) (hd : sbtw c d a) (hab : s(a, b) ∈ segments T)
    (hbc : s(b, c) ∈ segments T) (hcd : s(c, d) ∈ segments T) (hda : s(d, a) ∈ segments T) :
    IsFlipReplacement T s(a, c) s(b, d) := by
  have hrim := rims_mem_segments hb hd hab hbc hcd hda
  have hcross : Cross s(a, c) s(b, d) := cross_mk_iff.2 (Or.inl ⟨hb, hd⟩)
  have hbd_ncross : ∀ f ∈ T, f ≠ s(a, c) → ¬Cross s(b, d) f := by
    intro f hf hfac h
    induction f using Sym2.ind with
    | _ u v =>
      obtain h' | ⟨ρ, hρ, h'⟩ := quad_cross_right hb hd h
      exacts [hfac h', not_cross_of_mem_segments hT (hrim ρ hρ).1 (mem_segments.2 (Or.inl hf)) h']
  have hbd_diag : IsDiagonal s(b, d) := by
    have hbd : b ≠ d := by rw [Ne, eq_iff_val]; rw [sbtw_iff_val] at hb hd; omega
    have hbcd : sbtw b c d := by rw [sbtw_iff_val] at hb hd ⊢; omega
    have hdab : sbtw d a b := by rw [sbtw_iff_val] at hb hd ⊢; omega
    refine ⟨fun h => hbd (Sym2.mk_isDiag_iff.1 h), fun h => ?_⟩
    rcases (isSide_iff_cIoo_eq_empty hbd).1 h with h | h
    · exact (Set.eq_empty_iff_forall_notMem.1 h) c hbcd
    · exact (Set.eq_empty_iff_forall_notMem.1 h) a hdab
  have hmem : ∀ e, e ∈ flipTriangulation T s(a, c) s(b, d) ↔
      e = s(b, d) ∨ (e ≠ s(a, c) ∧ e ∈ T) := fun e => by
    simp only [flipTriangulation, Finset.mem_insert, Finset.mem_erase]
  refine ⟨hT, hγ, hbd_diag, fun h => hT.noncrossing _ hγ _ h hcross, ?_, ?_, ?_⟩
  · intro e he
    rcases (hmem e).1 he with rfl | ⟨-, he⟩
    exacts [hbd_diag, hT.isDiagonal e he]
  · intro e he f hf
    rcases (hmem e).1 he with rfl | ⟨he1, he2⟩ <;> rcases (hmem f).1 hf with rfl | ⟨hf1, hf2⟩
    · rw [cross_mk_iff]
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      exacts [sbtw_irrefl_left h, sbtw_irrefl_right h]
    · exact hbd_ncross f hf2 hf1
    · exact fun h => hbd_ncross e he2 he1 h.symm
    · exact hT.noncrossing e he2 f hf2
  · intro e he heT
    rw [hmem, not_or, not_and_or, not_not] at heT
    obtain ⟨heb, heT⟩ := heT
    obtain rfl | hea := eq_or_ne e s(a, c)
    · exact ⟨s(b, d), (hmem _).2 (Or.inl rfl), hcross⟩
    obtain ⟨f, hf, hef⟩ := hT.maximal e he (heT.resolve_left hea)
    obtain rfl | hfac := eq_or_ne f s(a, c)
    · induction e using Sym2.ind with
      | _ u v =>
        obtain h | ⟨ρ, hρ, h⟩ := quad_cross_left hb hd hef.symm
        · exact absurd h heb
        · exact ⟨ρ, (hmem ρ).2 (Or.inr ⟨(hrim ρ hρ).2,
            mem_of_cross_of_mem_segments (hrim ρ hρ).1 h⟩), h.symm⟩
    · exact ⟨f, (hmem f).2 (Or.inr ⟨hfac, hf⟩), hef⟩

/-- For apexes `b ∈ (a, c)` and `d ∈ (c, a)` over the diagonal `{a, c}` of `T`, every replacement
for the flip at `{a, c}` is `{b, d}`. -/
private theorem eq_of_isFlipReplacement_of_apex {a b c d : ZMod m} (hb : sbtw a b c)
    (hd : sbtw c d a) (hab : s(a, b) ∈ segments T) (hbc : s(b, c) ∈ segments T)
    (hcd : s(c, d) ∈ segments T) (hda : s(d, a) ∈ segments T) {γ : Sym2 (ZMod m)}
    (h : IsFlipReplacement T s(a, c) γ) : γ = s(b, d) := by
  obtain ⟨hT, -, hdiag, hnotin, hT'⟩ := h
  have hrim := rims_mem_segments hb hd hab hbc hcd hda
  have hmem : ∀ e, e ∈ flipTriangulation T s(a, c) γ ↔ e = γ ∨ (e ≠ s(a, c) ∧ e ∈ T) :=
    fun e => by simp only [flipTriangulation, Finset.mem_insert, Finset.mem_erase]
  have hγ : γ ∈ flipTriangulation T s(a, c) γ := (hmem _).2 (Or.inl rfl)
  obtain ⟨f, hf, hc⟩ := hT.maximal γ hdiag hnotin
  obtain rfl | hfac := eq_or_ne f s(a, c)
  · induction γ using Sym2.ind with
    | _ u v =>
      obtain h | ⟨ρ, hρ, h⟩ := quad_cross_left hb hd hc.symm
      · exact h
      · exact absurd h fun h => hT'.noncrossing ρ ((hmem ρ).2 (Or.inr ⟨(hrim ρ hρ).2,
          mem_of_cross_of_mem_segments (hrim ρ hρ).1 h⟩)) _ hγ h
  · exact absurd hc (hT'.noncrossing _ hγ f ((hmem f).2 (Or.inr ⟨hfac, hf⟩)))

end FlipHelpers

/-- **Every diagonal of a triangulation can be flipped, in exactly one way.** Let `T` be a
triangulation and `γ = {a, c} ∈ T`. Then there are `b ∈ (a, c)` and `d ∈ (c, a)` such that
(a) `{a, b, c}` and `{a, c, d}` are triangles of `T`; (b) every triangle of `T` having `γ` among
its segments is one of these two; (c) `γ' = {b, d}` is a replacement for the flip of `T` at `γ`
(a diagonal not in `T` with `(T \ {γ}) ∪ {γ'}` a triangulation); (d) every replacement for this
flip is `γ'`. -/
@[cluster_algebras "lem_bc_flip_exists"]
theorem exists_flip {T : Finset (Sym2 (ZMod m))} (hT : IsTriangulation T) {a c : ZMod m}
    (hγ : s(a, c) ∈ T) :
    ∃ b d : ZMod m, sbtw a b c ∧ sbtw c d a ∧ IsTriangle T {a, b, c} ∧ IsTriangle T {a, c, d} ∧
      (∀ Δ, IsTriangle T Δ → a ∈ Δ → c ∈ Δ → Δ = {a, b, c} ∨ Δ = {a, c, d}) ∧
      IsFlipReplacement T s(a, c) s(b, d) ∧
      ∀ γ' : Sym2 (ZMod m), IsFlipReplacement T s(a, c) γ' → γ' = s(b, d) := by
  obtain ⟨b, hb, hab, hbc⟩ := exists_apex hT hγ
  obtain ⟨d, hd, hcd, hda⟩ := exists_apex hT (Sym2.eq_swap ▸ hγ : s(c, a) ∈ T)
  have hac : s(a, c) ∈ segments T := mem_segments.2 (Or.inl hγ)
  obtain ⟨hab', hac', had', hbc', hcd'⟩ : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ c ≠ d := by
    simp only [Ne, eq_iff_val]; rw [sbtw_iff_val] at hb hd; omega
  exact ⟨b, d, hb, hd, isTriangle_of_mem_segments hab' hac' hbc' hab hbc hac,
    isTriangle_of_mem_segments hac' had' hcd' hac hcd (Sym2.eq_swap ▸ hda),
    fun _ hΔ => isTriangle_eq_of_apex hT hb hab hbc hd hcd hda hΔ,
    isFlipReplacement_of_apex hT hγ hb hd hab hbc hcd hda,
    fun _ => eq_of_isFlipReplacement_of_apex hb hd hab hbc hcd hda⟩

/-! ### The exchange matrix of a labelled triangulation -/

/-- The **exchange matrix `B(T, λ)` of a labelled triangulation**: the `N × N` integer matrix
with entries `β_a(λ(p), λ(q))`, the signed counts of the arrow system `a` of the quiver `Q(T)`.
It is defined for every `T` and `ℓ`; the case of interest is a triangulation `T` with a
labelling `ℓ` satisfying `IsTriangulationLabelling T ℓ`. -/
@[cluster_algebras "def_bc_triangulation_matrix"]
def triangulationMatrix {N : ℕ} (T : Finset (Sym2 (ZMod m))) (ℓ : Fin N → Sym2 (ZMod m)) :
    Matrix (Fin N) (Fin N) ℤ :=
  Matrix.of fun p q => signedCount (polygonArrows T) (ℓ p) (ℓ q)

/-- `ℓ : Fin N → Sym2 (ZMod m)` is a **labelling of `T`**: a bijection from `Fin N` onto `T`,
that is, injective with range `T`. -/
@[cluster_algebras "def_bc_triangulation_matrix"]
def IsTriangulationLabelling {N : ℕ} (T : Finset (Sym2 (ZMod m)))
    (ℓ : Fin N → Sym2 (ZMod m)) : Prop :=
  Function.Injective ℓ ∧ Set.range ℓ = (T : Set (Sym2 (ZMod m)))

/-- The entries of `B(T, ℓ)` are the signed counts of the arrow system of the quiver
`polygonQuiver T`, read at the segments `ℓ p` and `ℓ q` of `T`. -/
@[cluster_algebras "def_bc_triangulation_matrix"]
theorem triangulationMatrix_apply {N : ℕ} (T : Finset (Sym2 (ZMod m)))
    (ℓ : Fin N → Sym2 (ZMod m)) (hℓ : ∀ p, ℓ p ∈ segments T) (p q : Fin N) :
    triangulationMatrix T ℓ p q =
      signedCount (polygonQuiver T).arrows ⟨ℓ p, hℓ p⟩ ⟨ℓ q, hℓ q⟩ :=
  rfl

/-- **`B(T, λ)` is skew-symmetric.** This holds for every `T` and `ℓ`. -/
@[cluster_algebras "lem_bc_triangulation_matrix_entries"]
theorem triangulationMatrix_apply_eq_neg {N : ℕ} (T : Finset (Sym2 (ZMod m)))
    (ℓ : Fin N → Sym2 (ZMod m)) (p q : Fin N) :
    triangulationMatrix T ℓ p q = -triangulationMatrix T ℓ q p :=
  (neg_signedCount _ _ _).symm

omit [NeZero m] in
/-- A labelling takes its values in `T`. -/
theorem IsTriangulationLabelling.mem {N : ℕ} {T : Finset (Sym2 (ZMod m))}
    {ℓ : Fin N → Sym2 (ZMod m)} (hℓ : IsTriangulationLabelling T ℓ) (p : Fin N) :
    ℓ p ∈ T :=
  Finset.mem_coe.1 (hℓ.2 ▸ Set.mem_range_self p)

omit [NeZero m] in
/-- A labelling is injective. -/
theorem IsTriangulationLabelling.injective {N : ℕ} {T : Finset (Sym2 (ZMod m))}
    {ℓ : Fin N → Sym2 (ZMod m)} (hℓ : IsTriangulationLabelling T ℓ) : Function.Injective ℓ :=
  hℓ.1

omit [NeZero m] in
/-- The range of a labelling of `T` is `T`. -/
theorem IsTriangulationLabelling.range_eq {N : ℕ} {T : Finset (Sym2 (ZMod m))}
    {ℓ : Fin N → Sym2 (ZMod m)} (hℓ : IsTriangulationLabelling T ℓ) :
    Set.range ℓ = (T : Set (Sym2 (ZMod m))) :=
  hℓ.2

/-- A triangle carrying an arrow `σ → σ'` has `σ` and `σ'` among its segments. -/
private theorem mem_sym2_of_mem_arrowTriangles {T : Finset (Sym2 (ZMod m))}
    {σ σ' : Sym2 (ZMod m)} {t : Finset (ZMod m)} (ht : t ∈ arrowTriangles T σ σ') :
    IsTriangle T t ∧ σ ∈ t.sym2 ∧ σ' ∈ t.sym2 ∧ ¬σ.IsDiag ∧ ¬σ'.IsDiag := by
  obtain ⟨htri, a, b, c, hcw, rfl, rfl, ha, hb, hc⟩ := mem_arrowTriangles.1 ht
  refine ⟨htri, Finset.mk_mem_sym2_iff.2 ⟨ha, hb⟩, Finset.mk_mem_sym2_iff.2 ⟨hb, hc⟩, ?_, ?_⟩
  · rw [Sym2.mk_isDiag_iff]
    rintro rfl
    exact sbtw_irrefl_left hcw
  · rw [Sym2.mk_isDiag_iff]
    rintro rfl
    exact sbtw_irrefl_right hcw

/-- **At most one arrow joins two segments.** -/
private theorem polygonArrows_le_one (T : Finset (Sym2 (ZMod m))) (σ σ' : Sym2 (ZMod m)) :
    polygonArrows T σ σ' ≤ 1 := by
  rcases eq_or_ne σ σ' with rfl | hne
  · simp [polygonArrows_self]
  unfold polygonArrows
  split_ifs
  · exact zero_le_one
  · refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    obtain ⟨h1, h2, h3, h4, h5⟩ := mem_sym2_of_mem_arrowTriangles ht
    obtain ⟨h1', h2', h3', -, -⟩ := mem_sym2_of_mem_arrowTriangles ht'
    exact IsTriangle.eq_of_mem_sym2 h4 h5 hne h1 h1' h2 h3 h2' h3'

/-- **The entries of `B(T, λ)` lie in `{-1, 0, 1}`.** This holds for every `T` and `ℓ`. -/
@[cluster_algebras "lem_bc_triangulation_matrix_entries"]
theorem triangulationMatrix_apply_mem {N : ℕ} (T : Finset (Sym2 (ZMod m)))
    (ℓ : Fin N → Sym2 (ZMod m)) (p q : Fin N) :
    triangulationMatrix T ℓ p q = -1 ∨ triangulationMatrix T ℓ p q = 0 ∨
      triangulationMatrix T ℓ p q = 1 := by
  have h1 := polygonArrows_le_one T (ℓ p) (ℓ q)
  have h2 := polygonArrows_le_one T (ℓ q) (ℓ p)
  have h3 := twoCycleFree_polygonArrows T (ℓ p) (ℓ q)
  simp only [triangulationMatrix, Matrix.of_apply, signedCount]
  omega

/-- Three distinct vertices of a triangle carry an arrow one way or the other between the
two segments through the middle one. -/
private theorem mem_arrowTriangles_or {T : Finset (Sym2 (ZMod m))} {Δ : Finset (ZMod m)}
    (hΔ : IsTriangle T Δ) {p w q : ZMod m} (hp : p ∈ Δ) (hw : w ∈ Δ) (hq : q ∈ Δ)
    (hpw : p ≠ w) (hwq : w ≠ q) (hpq : p ≠ q) :
    Δ ∈ arrowTriangles T s(p, w) s(w, q) ∨ Δ ∈ arrowTriangles T s(w, q) s(p, w) := by
  have : sbtw p w q ∨ sbtw q w p := by
    have := ZMod.val_lt p; have := ZMod.val_lt w; have := ZMod.val_lt q
    rw [Ne, eq_iff_val] at hpw hwq hpq
    simp only [sbtw_iff_val]
    omega
  rcases this with h | h
  · exact Or.inl (mem_arrowTriangles.2 ⟨hΔ, p, w, q, h, rfl, rfl, hp, hw, hq⟩)
  · exact Or.inr
      (mem_arrowTriangles.2 ⟨hΔ, q, w, p, h, Sym2.eq_swap, Sym2.eq_swap, hq, hw, hp⟩)

/-- Two distinct segments of a triangle carry an arrow one way or the other. -/
private theorem mem_arrowTriangles_or_of_mem_sym2 {T : Finset (Sym2 (ZMod m))}
    {Δ : Finset (ZMod m)} (hΔ : IsTriangle T Δ) {σ σ' : Sym2 (ZMod m)} (hne : σ ≠ σ')
    (hσ : σ ∈ Δ.sym2) (hσ' : σ' ∈ Δ.sym2) (hd : ¬σ.IsDiag) (hd' : ¬σ'.IsDiag) :
    Δ ∈ arrowTriangles T σ σ' ∨ Δ ∈ arrowTriangles T σ' σ := by
  induction σ using Sym2.ind with | _ x y => ?_
  induction σ' using Sym2.ind with | _ u v => ?_
  rw [Finset.mk_mem_sym2_iff] at hσ hσ'
  rw [Sym2.mk_isDiag_iff] at hd hd'
  by_cases hyu : y = u
  · subst hyu
    have hxv : x ≠ v := by rintro rfl; exact hne Sym2.eq_swap
    exact mem_arrowTriangles_or hΔ hσ.1 hσ.2 hσ'.2 hd hd' hxv
  by_cases hyv : y = v
  · subst hyv
    have hxu : x ≠ u := by rintro rfl; exact hne rfl
    rw [Sym2.eq_swap (a := u)]
    exact mem_arrowTriangles_or hΔ hσ.1 hσ.2 hσ'.1 hd (Ne.symm hd') hxu
  by_cases hxu : x = u
  · subst hxu
    rw [Sym2.eq_swap (a := x) (b := y)]
    exact mem_arrowTriangles_or hΔ hσ.2 hσ.1 hσ'.2 (Ne.symm hd) hd' hyv
  by_cases hxv : x = v
  · subst hxv
    rw [Sym2.eq_swap (a := x) (b := y), Sym2.eq_swap (a := u)]
    exact mem_arrowTriangles_or hΔ hσ.2 hσ.1 hσ'.1 (Ne.symm hd) (Ne.symm hd') hyu
  exfalso
  have hsub : ({x, y, u, v} : Finset (ZMod m)) ⊆ Δ := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hσ.1, hσ.2, hσ'.1, hσ'.2⟩
  have hcard : ({x, y, u, v} : Finset (ZMod m)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hd, hxu, hxv]),
      Finset.card_insert_of_notMem (by simp [hyu, hyv]), Finset.card_pair hd']
  have := Finset.card_le_card hsub
  rw [hcard, hΔ.1] at this
  omega

/-- **The nonzero entries of `B(T, λ)`.** For `p ≠ q`, `b_{pq} ≠ 0` if and only if some
triangle of `T` has both `λ(p)` and `λ(q)` among its segments. -/
@[cluster_algebras "lem_bc_triangulation_matrix_entries"]
theorem triangulationMatrix_apply_ne_zero_iff {N : ℕ} {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) {ℓ : Fin N → Sym2 (ZMod m)} (hℓ : IsTriangulationLabelling T ℓ)
    {p q : Fin N} (hpq : p ≠ q) :
    triangulationMatrix T ℓ p q ≠ 0 ↔ ∃ Δ, IsTriangle T Δ ∧ ℓ p ∈ Δ.sym2 ∧ ℓ q ∈ Δ.sym2 := by
  have hp := hT.isDiagonal _ (hℓ.mem p)
  have hq := hT.isDiagonal _ (hℓ.mem q)
  have hne : ℓ p ≠ ℓ q := fun h => hpq (hℓ.injective h)
  have e1 := polygonArrows_eq_card_arrowTriangles T (σ' := ℓ q) fun h => hp.2 h.1
  have e2 := polygonArrows_eq_card_arrowTriangles T (σ' := ℓ p) fun h => hq.2 h.1
  have h1 := polygonArrows_le_one T (ℓ p) (ℓ q)
  have h2 := polygonArrows_le_one T (ℓ q) (ℓ p)
  have h3 := twoCycleFree_polygonArrows T (ℓ p) (ℓ q)
  simp only [triangulationMatrix, Matrix.of_apply, signedCount]
  constructor
  · intro h
    obtain h | h : 0 < (arrowTriangles T (ℓ p) (ℓ q)).card ∨
        0 < (arrowTriangles T (ℓ q) (ℓ p)).card := by omega
    · obtain ⟨t, ht⟩ := Finset.card_pos.1 h
      obtain ⟨h1, h2, h3, -⟩ := mem_sym2_of_mem_arrowTriangles ht
      exact ⟨t, h1, h2, h3⟩
    · obtain ⟨t, ht⟩ := Finset.card_pos.1 h
      obtain ⟨h1, h2, h3, -⟩ := mem_sym2_of_mem_arrowTriangles ht
      exact ⟨t, h1, h3, h2⟩
  · rintro ⟨Δ, hΔ, hpΔ, hqΔ⟩
    rcases mem_arrowTriangles_or_of_mem_sym2 hΔ hne hpΔ hqΔ hp.1 hq.1 with h | h <;>
      have := Finset.card_pos.2 ⟨Δ, h⟩ <;> omega

/-- **The signs of `B(T, λ)`.** If `(a₁, a₂, a₃)` is a clockwise listing of a triangle of `T`
with `λ(p) = {a₁, a₂}` and `λ(q) = {a₂, a₃}`, then `b_{pq} = 1`. -/
@[cluster_algebras "lem_bc_triangulation_matrix_entries"]
theorem triangulationMatrix_apply_eq_one {N : ℕ} {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) {ℓ : Fin N → Sym2 (ZMod m)} (hℓ : IsTriangulationLabelling T ℓ)
    {p q : Fin N} {a₁ a₂ a₃ : ZMod m} (hΔ : IsTriangle T {a₁, a₂, a₃})
    (hcw : IsClockwise a₁ a₂ a₃) (hp : ℓ p = s(a₁, a₂)) (hq : ℓ q = s(a₂, a₃)) :
    triangulationMatrix T ℓ p q = 1 := by
  have e1 := polygonArrows_eq_card_arrowTriangles T (σ' := ℓ q)
    fun h => (hT.isDiagonal _ (hℓ.mem p)).2 h.1
  have h1 := polygonArrows_le_one T (ℓ p) (ℓ q)
  have h3 := twoCycleFree_polygonArrows T (ℓ p) (ℓ q)
  have := Finset.card_pos.2 ⟨({a₁, a₂, a₃} : Finset (ZMod m)),
    mem_arrowTriangles.2 ⟨hΔ, a₁, a₂, a₃, hcw, hp, hq, by simp, by simp, by simp⟩⟩
  simp only [triangulationMatrix, Matrix.of_apply, signedCount]
  omega

omit [NeZero m] in
/-- **The labelling after a flip.** If `γ'` is the replacement for the flip of `T` at `λ(k)`, the
labelling `λ'` with `λ'(k) = γ'` and `λ'(p) = λ(p)` for `p ≠ k` is a bijection onto
`T' = (T \ {λ(k)}) ∪ {γ'}`. -/
@[cluster_algebras "lem_bc_flip_matrix_mutation"]
theorem isTriangulationLabelling_update_flip {N : ℕ} {T : Finset (Sym2 (ZMod m))}
    {ℓ : Fin N → Sym2 (ZMod m)} (hℓ : IsTriangulationLabelling T ℓ) {k : Fin N}
    {γ' : Sym2 (ZMod m)} (hγ' : IsFlipReplacement T (ℓ k) γ') :
    IsTriangulationLabelling (flipTriangulation T (ℓ k) γ') (Function.update ℓ k γ') := by
  have hγ'T : γ' ∉ T := hγ'.2.2.2.1
  constructor
  · intro i j h
    by_cases hi : i = k <;> by_cases hj : j = k
    · rw [hi, hj]
    · subst hi
      rw [Function.update_self, Function.update_of_ne hj] at h
      exact absurd (h ▸ hℓ.mem j) hγ'T
    · subst hj
      rw [Function.update_self, Function.update_of_ne hi] at h
      exact absurd (h ▸ hℓ.mem i) hγ'T
    · rw [Function.update_of_ne hi, Function.update_of_ne hj] at h
      exact hℓ.injective h
  · ext x
    simp only [Set.mem_range, flipTriangulation, Finset.coe_insert, Finset.coe_erase,
      Set.mem_insert_iff, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi : i = k
      · subst hi
        exact Or.inl (Function.update_self _ _ _)
      · rw [Function.update_of_ne hi]
        exact Or.inr ⟨hℓ.mem i, fun h => hi (hℓ.injective h)⟩
    · rintro (rfl | ⟨hx, hxk⟩)
      · exact ⟨k, Function.update_self _ _ _⟩
      · obtain ⟨i, rfl⟩ : x ∈ Set.range ℓ := hℓ.range_eq ▸ Finset.mem_coe.2 hx
        exact ⟨i, Function.update_of_ne (fun h : i = k => hxk (h ▸ rfl)) _ _⟩

/-- The signed counts of the mutation of a quiver at `w`, between two vertices one of which is
mutable. -/
private theorem signedCount_mutationArrows {V : Type*} [Fintype V] [DecidableEq V] (Q : Quiver V)
    (w u v : V) (hf : u ∉ Q.frozen ∨ v ∉ Q.frozen) :
    signedCount (Q.mutationArrows w) u v =
      if u = w ∨ v = w then -signedCount Q.arrows u v
      else signedCount Q.arrows u v +
          max 0 (signedCount Q.arrows u w) * max 0 (signedCount Q.arrows w v) -
        max 0 (-signedCount Q.arrows u w) * max 0 (-signedCount Q.arrows w v) := by
  rw [Quiver.mutationArrows, signedCount_cancellation]
  split_ifs with h
  · simp only [signedCount, reversal_stepOne_of_eq Q w u v h,
      reversal_stepOne_of_eq Q w v u h.symm]
    ring
  · rw [not_or] at h
    simp only [neg_signedCount, max_zero_signedCount Q.twoCycleFree]
    simp only [signedCount, reversal_stepOne_of_ne Q w u v h.1 h.2 hf,
      reversal_stepOne_of_ne Q w v u h.2 h.1 hf.symm, Nat.cast_add, Nat.cast_mul]
    ring

/-- **A flip mutates the exchange matrix of a labelled triangulation**:
`B(T', λ') = μ_k(B(T, λ))`, where `T'` is the flip of `T` at `λ(k)` with replacement `γ'` and
`λ'` is `λ` with `λ(k)` replaced by `γ'`. The replacement is unique (`exists_flip`), so "the
replacement" is any `γ'` with `IsFlipReplacement T (ℓ k) γ'`. -/
@[cluster_algebras "lem_bc_flip_matrix_mutation"]
theorem triangulationMatrix_update_flip {N : ℕ} {T : Finset (Sym2 (ZMod m))}
    {ℓ : Fin N → Sym2 (ZMod m)} (hℓ : IsTriangulationLabelling T ℓ) {k : Fin N}
    {γ' : Sym2 (ZMod m)} (hγ' : IsFlipReplacement T (ℓ k) γ') :
    triangulationMatrix (flipTriangulation T (ℓ k) γ') (Function.update ℓ k γ') =
      matrixMutation le_rfl (triangulationMatrix T ℓ) k := by
  have hk : (⟨ℓ k, mem_segments.2 (Or.inl hγ'.2.1)⟩ : SegmentType T) ∉
      (polygonQuiver T).frozen :=
    fun h => (hγ'.1.isDiagonal _ hγ'.2.1).2 (Finset.mem_filter.1 h).2
  obtain ⟨e, he⟩ := polygonQuiver_mutate_iso_flip hγ' hk
  let σ : Fin N → SegmentType T := fun p => ⟨ℓ p, mem_segments.2 (Or.inl (hℓ.mem p))⟩
  have hfree : ∀ p, σ p ∉ (polygonQuiver T).frozen :=
    fun p h => (hγ'.1.isDiagonal _ (hℓ.mem p)).2 (Finset.mem_filter.1 h).2
  have heσ : ∀ p, (e.equiv (σ p)).1 = Function.update ℓ k γ' p := by
    intro p
    rw [he]
    by_cases hp : p = k
    · subst hp
      simp [σ]
    · rw [Function.update_of_ne hp, if_neg]
      exact fun h => hp (hℓ.injective h)
  have harr : ∀ p q, polygonArrows (flipTriangulation T (ℓ k) γ') (Function.update ℓ k γ' p)
      (Function.update ℓ k γ' q) = (polygonQuiver T).mutationArrows (σ k) (σ p) (σ q) := by
    intro p q
    rw [← heσ p, ← heσ q]
    exact e.arrows_eq (σ p) (σ q)
  have hσ : ∀ p, σ p = σ k ↔ p = k := fun p =>
    ⟨fun h => hℓ.injective (congrArg Subtype.val h), fun h => h ▸ rfl⟩
  ext p q
  have hlhs :
      triangulationMatrix (flipTriangulation T (ℓ k) γ') (Function.update ℓ k γ') p q =
        signedCount ((polygonQuiver T).mutationArrows (σ k)) (σ p) (σ q) := by
    simp only [triangulationMatrix, Matrix.of_apply, signedCount, harr]
  rw [hlhs, signedCount_mutationArrows _ _ _ _ (Or.inl (hfree p))]
  simp only [hσ]
  split_ifs with h
  · rw [matrixMutation_apply_of_eq le_rfl _ k (by simpa using h)]
    rfl
  · rw [not_or] at h
    rw [matrixMutation_apply_of_ne_eq_max le_rfl _ k (by simpa using h.1) h.2]
    rfl

end TypeBC

end ClusterAlgebras

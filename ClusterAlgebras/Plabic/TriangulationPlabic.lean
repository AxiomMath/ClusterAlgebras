/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CycleSpace
public import ClusterAlgebras.Plabic.TriangulationCorner

/-!
# The plabic graph of a triangulation

Let `T` be a triangulation of the convex `m`-gon, `m ≥ 3`, whose vertices are the elements of
`ZMod m`, labelled clockwise, and let `C(T)` be its set of corners. The plabic graph
`G(T) = (H, d ↦ d̄, σ, B, κ, β)` has the darts
`H = {ω_x, ω̄_x : x ∈ C(T)} ∪ {λ_v, λ̄_v, e_v, ē_v : v ∈ ZMod m}`, the involution exchanging
`ω_x ↔ ω̄_x`, `λ_v ↔ λ̄_v` and `e_v ↔ ē_v`, and the rotation
* `σ(ω̄_(a,b,c)) = ω̄_(c,a,b)`;
* `σ(ω_(a,b,c)) = ω_(a,b',b)` if there is exactly one `b'` with `(a, b', b) ∈ C(T)`, and `λ_a`
  otherwise;
* `σ(λ_v) = ω_(v,z,v-1)` if there is exactly one `z` with `(v, z, v - 1) ∈ C(T)`, and `λ_v`
  otherwise;
* `σ(λ̄_v) = ē_(v+1)`, `σ(ē_(v+1)) = e_v`, `σ(e_v) = λ̄_v`.

The boundary arcs are the darts `e_v`, `ē_v`; the internal vertices containing a dart `ω_x` or
`λ_v` are white and the others black; and the boundary vertex labelled `i ∈ [1, m]` is the orbit
of `λ̄_v` for `v` the class of `i`.

In FWZ's picture, `ω_(a,b,c)` is the edge from the white vertex at the polygon vertex `a` to the
black vertex inside the triangle `{a, b, c}`, `λ_v` is the edge from the white vertex at `v` to
the boundary vertex `v`, and `e_v` is the boundary arc from the boundary vertex `v` to the
boundary vertex `v - 1`. Around the white vertex at `v`, counterclockwise, come the leg `λ_v` and
then the darts `ω_(v,b,c)` of the triangles at `v`: `σ` is a cyclic permutation of
`D_v = {λ_v} ∪ {ω_x : x ∈ C(T) with first entry v}`, and the fallback values never occur.

## Main definitions

* `ClusterAlgebras.TriangulationDart T`: the darts of `G(T)`.
* `ClusterAlgebras.triangulationRot T`: the rotation `σ` of `G(T)`, as a function.
* `ClusterAlgebras.triangulationPlabicData hm hT`: the tuple `G(T)`.
* `ClusterAlgebras.triangulationWhiteDarts T v`: the set `D_v` of darts at the white vertex `v`.
* `ClusterAlgebras.triangulationFaceLabel T`: the labelling of the darts of `G(T)` by the face to
  their right, `∞` or a segment of `T`.

## Main results

* `ClusterAlgebras.triangulationRot_bijective`: `σ` is a permutation of the darts.
* `ClusterAlgebras.isCycleOn_triangulationWhiteDarts`: `σ` restricts to a cyclic permutation of
  `D_v`.
* `ClusterAlgebras.vertexOf_lam_triangulationPlabicData`: `D_v` is the vertex of `λ_v`.
* `ClusterAlgebras.vertexOf_omegaBar_triangulationPlabicData`,
  `ClusterAlgebras.vertexOf_lamBar_triangulationPlabicData`: the black vertices and the boundary
  vertices of `G(T)`.
* `ClusterAlgebras.card_vertices_triangulationPlabicData`,
  `ClusterAlgebras.card_edges_triangulationPlabicData`,
  `ClusterAlgebras.card_faceOrbits_triangulationPlabicData`: `G(T)` has `3m - 2` vertices,
  `5m - 6` edges and `2m - 2` faces.
* `ClusterAlgebras.faceOf_eq_faceOf_iff_triangulationFaceLabel`: two darts lie on the same face
  exactly when they have the same label.
* `ClusterAlgebras.isPlabicGraph_triangulationPlabicData`: `G(T)` is a plabic graph with `m`
  boundary vertices.

## Implementation notes

* The darts form an inductive type with one constructor for each of the six families of
  symbols, so that the symbols are distinct by construction; the darts `ω_x`, `ω̄_x` are indexed
  by the elements of the `Finset` `C(T)`.
* The rotation is first defined as a function `triangulationRot T`, with FWZ's fallback
  values, for every finite set `T` of segments. It is a bijection when `T` is a triangulation of
  the `m`-gon with `m ≥ 3`, and `triangulationPlabicData` takes these two hypotheses in order to
  package it as a permutation.
* Labels are `0`-indexed: `i : Fin m` is FWZ's label `i + 1`, so the boundary vertex
  `β(i)` is the vertex of `λ̄_v` with `v` the class of the natural number `i + 1`.
* The colour is a function on darts: `white` on the darts `ω_x` and `λ_v`, `black` on the
  others (its values at the boundary darts `λ̄_v`, `e_v`, `ē_v` are irrelevant).
* The labels of the faces form the type `Option (segments T)`, `none` standing for the symbol
  `∞`. The exterior face is computed from the labelling, rather than by iterating `φ`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset TypeA

variable {m : ℕ} [NeZero m]

/-! ### The darts -/

/-- The **darts** of the plabic graph `G(T)` of a triangulation `T`: for each corner `x ∈ C(T)`
the darts `ω_x` (`omega x`) and `ω̄_x` (`omegaBar x`), and for each `v ∈ ZMod m` the darts `λ_v`
(`lam v`), `λ̄_v` (`lamBar v`), `e_v` (`arc v`) and `ē_v` (`arcBar v`). -/
inductive TriangulationDart (T : Finset (Sym2 (ZMod m))) : Type
  /-- The dart `ω_x` at the white vertex of the first entry of the corner `x`. -/
  | omega (x : triangulationCorners T)
  /-- The dart `ω̄_x` at the black vertex of the triangle of the corner `x`. -/
  | omegaBar (x : triangulationCorners T)
  /-- The dart `λ_v` of the leg at the white vertex `v`. -/
  | lam (v : ZMod m)
  /-- The dart `λ̄_v` of the leg at the boundary vertex `v`. -/
  | lamBar (v : ZMod m)
  /-- The boundary arc `e_v` from the boundary vertex `v` to the boundary vertex `v - 1`. -/
  | arc (v : ZMod m)
  /-- The boundary arc `ē_v`, the reverse of `e_v`. -/
  | arcBar (v : ZMod m)
  deriving DecidableEq, Fintype

namespace TriangulationDart

variable {T : Finset (Sym2 (ZMod m))}

/-- The involution `d ↦ d̄` of `G(T)`, exchanging `ω_x ↔ ω̄_x`, `λ_v ↔ λ̄_v` and `e_v ↔ ē_v`. -/
def reverse : TriangulationDart T → TriangulationDart T
  | omega x => omegaBar x
  | omegaBar x => omega x
  | lam v => lamBar v
  | lamBar v => lam v
  | arc v => arcBar v
  | arcBar v => arc v

/-- The reverse of `ω_x` is `ω̄_x`. -/
@[simp] theorem reverse_omega (x : triangulationCorners T) : (omega x).reverse = omegaBar x := rfl
/-- The reverse of `ω̄_x` is `ω_x`. -/
@[simp] theorem reverse_omegaBar (x : triangulationCorners T) : (omegaBar x).reverse = omega x :=
  rfl
/-- The reverse of `λ_v` is `λ̄_v`. -/
@[simp] theorem reverse_lam (v : ZMod m) : (lam v : TriangulationDart T).reverse = lamBar v := rfl
/-- The reverse of `λ̄_v` is `λ_v`. -/
@[simp] theorem reverse_lamBar (v : ZMod m) : (lamBar v : TriangulationDart T).reverse = lam v :=
  rfl
/-- The reverse of `e_v` is `ē_v`. -/
@[simp] theorem reverse_arc (v : ZMod m) : (arc v : TriangulationDart T).reverse = arcBar v := rfl
/-- The reverse of `ē_v` is `e_v`. -/
@[simp] theorem reverse_arcBar (v : ZMod m) : (arcBar v : TriangulationDart T).reverse = arc v :=
  rfl

/-- The map `d ↦ d̄` is an involution. -/
theorem reverse_involutive : Function.Involutive (reverse (T := T)) := by
  intro d
  cases d <;> rfl

/-- No dart is its own reverse. -/
theorem reverse_ne (d : TriangulationDart T) : d.reverse ≠ d := by
  cases d <;> simp

/-- The colour of a dart of `G(T)`: `white` at the darts `ω_x` and `λ_v`, `black` otherwise. -/
def colour : TriangulationDart T → Shade
  | omega _ => .white
  | lam _ => .white
  | _ => .black

/-- The dart `ω_x` is white. -/
@[simp] theorem colour_omega (x : triangulationCorners T) : (omega x).colour = .white := rfl
/-- The dart `λ_v` is white. -/
@[simp] theorem colour_lam (v : ZMod m) : (lam v : TriangulationDart T).colour = .white := rfl
/-- The dart `ω̄_x` is black. -/
@[simp] theorem colour_omegaBar (x : triangulationCorners T) : (omegaBar x).colour = .black :=
  rfl

end TriangulationDart

/-! ### The rotation -/

/-- The cyclic rotation `(a, b, c) ↦ (c, a, b)` of a corner of `T`. -/
def rotateCorner {T : Finset (Sym2 (ZMod m))} (x : triangulationCorners T) :
    triangulationCorners T :=
  ⟨(x.1.2.2, x.1.1, x.1.2.1), rotate_mem_triangulationCorners_iff.1 x.2⟩

/-- Rotating a corner three times gives it back. -/
@[simp]
theorem rotateCorner_rotateCorner_rotateCorner {T : Finset (Sym2 (ZMod m))}
    (x : triangulationCorners T) : rotateCorner (rotateCorner (rotateCorner x)) = x := rfl

/-- The rotation of the corner `(a, b, c)` is `(c, a, b)`. -/
@[simp]
theorem coe_rotateCorner {T : Finset (Sym2 (ZMod m))} (x : triangulationCorners T) :
    (rotateCorner x : ZMod m × ZMod m × ZMod m) = (x.1.2.2, x.1.1, x.1.2.1) := rfl

open TriangulationDart in
open Classical in
/-- The **rotation** `σ` of `G(T)`, as a function on darts:
`σ(ω̄_(a,b,c)) = ω̄_(c,a,b)`; `σ(ω_(a,b,c)) = ω_(a,b',b)` if there is exactly one `b'` with
`(a, b', b) ∈ C(T)`, and `λ_a` otherwise; `σ(λ_v) = ω_(v,z,v-1)` if there is exactly one `z` with
`(v, z, v - 1) ∈ C(T)`, and `λ_v` otherwise; `σ(λ̄_v) = ē_(v+1)`, `σ(ē_w) = e_(w-1)` and
`σ(e_v) = λ̄_v`. -/
noncomputable def triangulationRot (T : Finset (Sym2 (ZMod m))) :
    TriangulationDart T → TriangulationDart T
  | omegaBar x => omegaBar (rotateCorner x)
  | omega x =>
    if h : ∃! b', (x.1.1, b', x.1.2.1) ∈ triangulationCorners T then
      omega ⟨(x.1.1, h.exists.choose, x.1.2.1), h.exists.choose_spec⟩
    else lam x.1.1
  | lam v =>
    if h : ∃! z, (v, z, v - 1) ∈ triangulationCorners T then
      omega ⟨(v, h.exists.choose, v - 1), h.exists.choose_spec⟩
    else lam v
  | lamBar v => arcBar (v + 1)
  | arcBar w => arc (w - 1)
  | arc v => lamBar v

section Rotation

open TriangulationDart

variable {T : Finset (Sym2 (ZMod m))}

/-- `σ(ω̄_(a,b,c)) = ω̄_(c,a,b)`. -/
@[simp]
theorem triangulationRot_omegaBar (x : triangulationCorners T) :
    triangulationRot T (omegaBar x) = omegaBar (rotateCorner x) := rfl

/-- `σ(λ̄_v) = ē_(v+1)`. -/
@[simp]
theorem triangulationRot_lamBar (v : ZMod m) :
    triangulationRot T (lamBar v) = arcBar (v + 1) := rfl

/-- `σ(ē_v) = e_(v-1)`. -/
@[simp]
theorem triangulationRot_arcBar (v : ZMod m) :
    triangulationRot T (arcBar v) = arc (v - 1) := rfl

/-- `σ(e_v) = λ̄_v`. -/
@[simp]
theorem triangulationRot_arc (v : ZMod m) :
    triangulationRot T (arc v) = lamBar v := rfl

/-- If `(a, b', b)` is the only corner with first entry `a` and last entry `b`, then
`σ(ω_(a,b,c)) = ω_(a,b',b)`. -/
theorem triangulationRot_omega_of_existsUnique {x : triangulationCorners T} {b' : ZMod m}
    (hb' : (x.1.1, b', x.1.2.1) ∈ triangulationCorners T)
    (hu : ∃! b', (x.1.1, b', x.1.2.1) ∈ triangulationCorners T) :
    triangulationRot T (omega x) = omega ⟨(x.1.1, b', x.1.2.1), hb'⟩ := by
  simp only [triangulationRot, dif_pos hu]
  congr 3
  rw [hu.unique hu.exists.choose_spec hb']

/-- If no corner has first entry `a` and last entry `b`, then `σ(ω_(a,b,c)) = λ_a`. -/
theorem triangulationRot_omega_of_not_mem {x : triangulationCorners T}
    (h : ∀ b', (x.1.1, b', x.1.2.1) ∉ triangulationCorners T) :
    triangulationRot T (omega x) = lam x.1.1 := by
  have hu : ¬∃! b', (x.1.1, b', x.1.2.1) ∈ triangulationCorners T :=
    fun hu => h _ hu.exists.choose_spec
  simp only [triangulationRot, dif_neg hu]

/-- If `(v, z, v - 1)` is the only corner with first entry `v` and last entry `v - 1`, then
`σ(λ_v) = ω_(v,z,v-1)`. -/
theorem triangulationRot_lam_of_existsUnique {v z : ZMod m}
    (hz : (v, z, v - 1) ∈ triangulationCorners T)
    (hu : ∃! z, (v, z, v - 1) ∈ triangulationCorners T) :
    triangulationRot T (lam v) = omega ⟨(v, z, v - 1), hz⟩ := by
  simp only [triangulationRot, dif_pos hu]
  congr 3
  rw [hu.unique hu.exists.choose_spec hz]

end Rotation

variable {T : Finset (Sym2 (ZMod m))}

/-! ### Facts about corners -/

/-- The middle entry of a corner `(a, b, c)` of `T` is never `a - 1`. -/
theorem snd_ne_sub_one_of_mem_triangulationCorners {a b c : ZMod m}
    (h : (a, b, c) ∈ triangulationCorners T) : b ≠ a - 1 := by
  rintro rfl
  have h' : sbtw (a - 1) c (a - 1 + 1) := by
    rw [sub_add_cancel]
    exact sbtw_cyclic.2 (mem_triangulationCorners_iff.1 h).1
  exact not_sbtw_self_add_one _ _ h'

/-- In a triangulation, a corner is determined by its first two entries. -/
theorem triangulationCorners_ext (hm : 3 ≤ m) (hT : IsTriangulation T)
    {x y : triangulationCorners T} (h₁ : x.1.1 = y.1.1) (h₂ : x.1.2.1 = y.1.2.1) : x = y := by
  obtain ⟨⟨a, b, c⟩, hx⟩ := x
  obtain ⟨⟨a', b', c'⟩, hy⟩ := y
  dsimp only at h₁ h₂
  subst h₁ h₂
  have hx' := rotate_mem_triangulationCorners_iff.2 hx
  have hy' := rotate_mem_triangulationCorners_iff.2 hy
  obtain ⟨c₀, -, hu⟩ := existsUnique_mem_triangulationCorners hm hT
    (mem_triangulationCorners_iff.1 hx').2.2.2 (ne_add_one_of_mem_triangulationCorners hx')
  obtain rfl := (hu c hx').trans (hu c' hy').symm
  rfl

omit [NeZero m] in
/-- In `ZMod m` with `3 ≤ m`, `v - 1 ≠ v + 1`. -/
theorem sub_one_ne_add_one (hm : 3 ≤ m) (v : ZMod m) : v - 1 ≠ v + 1 := by
  intro h
  have h₂ : ((2 : ℕ) : ZMod m) = 0 := by
    push_cast
    linear_combination -h
  rw [ZMod.natCast_eq_zero_iff] at h₂
  have := Nat.le_of_dvd (by norm_num) h₂
  omega

/-- If `b` lies strictly between `v` and `c`, then `b` is fewer `+1` steps from `v` than `c`. -/
theorem basePos_lt_basePos_of_sbtw {v b c : ZMod m} (h : sbtw v b c) :
    basePos v b < basePos v c := by
  rw [sbtw_iff_sbtw_basePos v, Int.sbtw_iff, basePos_self] at h
  have := basePos_nonneg v b
  have := basePos_nonneg v c
  omega

/-! ### The rotation at the white darts -/

section White

open TriangulationDart

variable (hm : 3 ≤ m) (hT : IsTriangulation T)

include hm hT

/-- The rotation at `ω_(a,b,c)`: it is `λ_a` if `b = a + 1`, and otherwise `ω_(a,b',b)` for a
corner `(a, b', b)`. -/
theorem triangulationRot_omega_cases (x : triangulationCorners T) :
    (x.1.2.1 = x.1.1 + 1 ∧ triangulationRot T (omega x) = lam x.1.1) ∨
      ∃ y : triangulationCorners T, y.1.1 = x.1.1 ∧ y.1.2.2 = x.1.2.1 ∧
        triangulationRot T (omega x) = omega y := by
  obtain ⟨⟨a, b, c⟩, hx⟩ := x
  dsimp only
  by_cases hb : b = a + 1
  · exact .inl ⟨hb, triangulationRot_omega_of_not_mem fun b' hb' =>
      ne_add_one_of_mem_triangulationCorners hb' hb⟩
  · have hu := existsUnique_mem_triangulationCorners hm hT
      (mem_triangulationCorners_iff.1 hx).2.1 hb
    obtain ⟨b', hb'⟩ := hu.exists
    exact .inr ⟨⟨(a, b', b), hb'⟩, rfl, rfl, triangulationRot_omega_of_existsUnique hb' hu⟩

/-- The rotation at `λ_v` is `ω_(v,z,v-1)` for a corner `(v, z, v - 1)`. -/
theorem exists_triangulationRot_lam (v : ZMod m) :
    ∃ y : triangulationCorners T, y.1.1 = v ∧ y.1.2.2 = v - 1 ∧
      triangulationRot T (lam v) = omega y := by
  have hseg : s(v, v - 1) ∈ segments T :=
    mem_segments.2 (.inr ⟨v - 1, by rw [Sym2.eq_swap, sub_add_cancel]⟩)
  have hu := existsUnique_mem_triangulationCorners hm hT hseg (sub_one_ne_add_one hm v)
  obtain ⟨z, hz⟩ := hu.exists
  exact ⟨⟨(v, z, v - 1), hz⟩, rfl, rfl, triangulationRot_lam_of_existsUnique hz hu⟩

/-- `σ(ω_x)` and `σ(λ_v)` differ. -/
theorem triangulationRot_omega_ne_lam (x : triangulationCorners T) (v : ZMod m) :
    triangulationRot T (omega x) ≠ triangulationRot T (lam v) := by
  intro h
  obtain ⟨z, hz₁, hz₂, hz⟩ := exists_triangulationRot_lam hm hT v
  rcases triangulationRot_omega_cases hm hT x with ⟨-, hx⟩ | ⟨y, hy₁, hy₂, hy⟩
  · rw [hx, hz] at h
    cases h
  · rw [hy, hz] at h
    cases h
    obtain ⟨⟨a, b, c⟩, hx⟩ := x
    dsimp only at hy₁ hy₂
    exact snd_ne_sub_one_of_mem_triangulationCorners hx (by rw [← hy₂, hz₂, ← hz₁, hy₁])

end White

/-- The kind of a dart, which `σ` preserves: the darts `ω_x`, `λ_v` at the white vertices, the
darts `ω̄_x` at the black vertices, and the darts `λ̄_v`, `e_v`, `ē_v` at the boundary vertices. -/
private def dartKind : TriangulationDart T → Fin 3
  | .omega _ => 0
  | .lam _ => 0
  | .omegaBar _ => 1
  | .lamBar _ => 2
  | .arcBar _ => 2
  | .arc _ => 2

/-- The rotation of corners is injective. -/
theorem rotateCorner_injective : Function.Injective (rotateCorner (T := T)) := by
  rintro ⟨⟨a, b, c⟩, hx⟩ ⟨⟨a', b', c'⟩, hx'⟩ h
  simp only [rotateCorner, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

private theorem dartKind_triangulationRot (d : TriangulationDart T) :
    dartKind (triangulationRot T d) = dartKind d := by
  cases d <;> simp only [triangulationRot] <;> (try split) <;> rfl

open TriangulationDart in
/-- For a triangulation of the `m`-gon, `m ≥ 3`, the rotation `σ` of `G(T)` is injective. -/
theorem triangulationRot_injective (hm : 3 ≤ m) (hT : IsTriangulation T) :
    Function.Injective (triangulationRot T) := by
  intro d₁ d₂ h
  have hk := congrArg dartKind h
  rw [dartKind_triangulationRot, dartKind_triangulationRot] at hk
  rcases d₁ with x | x | v | v | v | v <;> rcases d₂ with x' | x' | v' | v' | v' | v' <;>
    first
      | (simp [dartKind] at hk; done)
      | (simp at h; done)
      | (simpa using h)
      | exact congrArg omegaBar (rotateCorner_injective (by simpa using h))
      | exact absurd h (triangulationRot_omega_ne_lam hm hT _ _)
      | exact absurd h.symm (triangulationRot_omega_ne_lam hm hT _ _)
      | skip
  · rcases triangulationRot_omega_cases hm hT x with ⟨hb, hr⟩ | ⟨y, hy₁, hy₂, hr⟩ <;>
      rcases triangulationRot_omega_cases hm hT x' with ⟨hb', hr'⟩ | ⟨y', hy₁', hy₂', hr'⟩ <;>
      rw [hr, hr'] at h <;> try (simp at h; done)
    · have ha := lam.inj h
      exact congrArg omega (triangulationCorners_ext hm hT ha (by rw [hb, hb', ha]))
    · obtain rfl := omega.inj h
      exact congrArg omega (triangulationCorners_ext hm hT (by rw [← hy₁, hy₁'])
        (by rw [← hy₂, hy₂']))
  · obtain ⟨z, hz₁, -, hz⟩ := exists_triangulationRot_lam hm hT v
    obtain ⟨z', hz₁', -, hz'⟩ := exists_triangulationRot_lam hm hT v'
    rw [hz, hz'] at h
    obtain rfl := omega.inj h
    rw [← hz₁, hz₁']

/-- For a triangulation of the `m`-gon, `m ≥ 3`, the rotation `σ` of `G(T)` is a bijection. -/
theorem triangulationRot_bijective (hm : 3 ≤ m) (hT : IsTriangulation T) :
    Function.Bijective (triangulationRot T) :=
  Finite.injective_iff_bijective.1 (triangulationRot_injective hm hT)

/-! ### The plabic graph -/

open TriangulationDart in
/-- **The plabic graph `G(T)` of a triangulation** `T` of the convex `m`-gon, `m ≥ 3`. Its darts
are `TriangulationDart T`; the involution exchanges `ω_x ↔ ω̄_x`, `λ_v ↔ λ̄_v`, `e_v ↔ ē_v`; the
rotation is `triangulationRot T`; the boundary arcs are the darts `e_v`, `ē_v`; the darts `ω_x`,
`λ_v` are coloured white and the others black; and the boundary vertex labelled `i : Fin m` (FWZ's
label `i + 1`) is the vertex of `λ̄_v` for `v` the class of `i + 1`. -/
@[cluster_algebras "def_triangulation_plabic_graph"]
noncomputable def triangulationPlabicData (hm : 3 ≤ m) (hT : IsTriangulation T) :
    PlabicData (TriangulationDart T) m where
  inv := reverse_involutive.toPerm
  rot := Equiv.ofBijective _ (triangulationRot_bijective hm hT)
  bdry := univ.filter fun d => ∃ v, d = arc v ∨ d = arcBar v
  colour := TriangulationDart.colour
  leg i := lamBar ((i + 1 : ℕ) : ZMod m)

section PlabicData

open TriangulationDart

variable (hm : 3 ≤ m) (hT : IsTriangulation T)

/-- The rotation of `triangulationPlabicData hm hT` is `triangulationRot T`. -/
@[simp]
theorem triangulationPlabicData_rot_apply (d : TriangulationDart T) :
    (triangulationPlabicData hm hT).rot d = triangulationRot T d := rfl

/-- The involution of `triangulationPlabicData hm hT` is `TriangulationDart.reverse`. -/
@[simp]
theorem triangulationPlabicData_inv_apply (d : TriangulationDart T) :
    (triangulationPlabicData hm hT).inv d = d.reverse := rfl

/-- The boundary arcs of `triangulationPlabicData hm hT` are the darts `e_v` and `ē_v`. -/
theorem mem_triangulationPlabicData_bdry {d : TriangulationDart T} :
    d ∈ (triangulationPlabicData hm hT).bdry ↔ ∃ v, d = arc v ∨ d = arcBar v := by
  simp [triangulationPlabicData]

/-- The colouring of `triangulationPlabicData hm hT` is `TriangulationDart.colour`. -/
@[simp]
theorem triangulationPlabicData_colour (d : TriangulationDart T) :
    (triangulationPlabicData hm hT).colour d = d.colour := rfl

/-- The leg at the boundary vertex labelled `i : Fin m` is `λ̄_v` for `v` the class of `i + 1`. -/
@[simp]
theorem triangulationPlabicData_leg (i : Fin m) :
    (triangulationPlabicData hm hT).leg i = lamBar ((i + 1 : ℕ) : ZMod m) := rfl

/-- The vertex of a dart fixed by the cube of the rotation consists of the dart and its first two
images. -/
private theorem vertexOf_eq_of_rot_rot_rot {H : Type*} [Fintype H] [DecidableEq H]
    (R : RotationSystem H) {d : H} (h : R.rot (R.rot (R.rot d)) = d) :
    R.vertexOf d = {d, R.rot d, R.rot (R.rot d)} := by
  ext e
  rw [RotationSystem.mem_vertexOf]
  constructor
  · intro he
    obtain ⟨n, rfl⟩ := he.exists_nat_pow_eq
    clear he
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      simp only [mem_insert, mem_singleton] at ih ⊢
      rcases ih with h' | h' | h' <;> rw [h'] <;> simp [h]
  · intro he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact .refl _ _
    · exact Equiv.Perm.sameCycle_apply_right.2 (.refl _ _)
    · exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.sameCycle_apply_right.2 (.refl _ _))

/-- The black vertex of the triangle of the corner `x = (a, b, c)` is
`{ω̄_(a,b,c), ω̄_(c,a,b), ω̄_(b,c,a)}`. -/
theorem vertexOf_omegaBar_triangulationPlabicData (x : triangulationCorners T) :
    (triangulationPlabicData hm hT).vertexOf (omegaBar x) =
      {omegaBar x, omegaBar (rotateCorner x), omegaBar (rotateCorner (rotateCorner x))} :=
  vertexOf_eq_of_rot_rot_rot _ (by simp)

/-- The boundary vertex `p_v` of `G(T)` is `{λ̄_v, ē_(v+1), e_v}`. -/
theorem vertexOf_lamBar_triangulationPlabicData (v : ZMod m) :
    (triangulationPlabicData hm hT).vertexOf (lamBar v) = {lamBar v, arcBar (v + 1), arc v} := by
  rw [vertexOf_eq_of_rot_rot_rot _ (by simp)]
  simp

/-- The boundary vertex labelled `i : Fin m` is the vertex of `λ̄_v` for `v` the class of `i + 1`
in `ZMod m`. -/
@[simp]
theorem triangulationPlabicData_bvertex (i : Fin m) :
    (triangulationPlabicData hm hT).bvertex i =
      (triangulationPlabicData hm hT).vertexOf (lamBar ((i + 1 : ℕ) : ZMod m)) := rfl

end PlabicData

/-! ### The white vertices -/

/-- The set `D_v = {λ_v} ∪ {ω_x : x ∈ C(T), x has first entry v}` of darts at the white vertex
`v` of `G(T)`. -/
def triangulationWhiteDarts (T : Finset (Sym2 (ZMod m))) (v : ZMod m) :
    Finset (TriangulationDart T) :=
  insert (.lam v) ((univ.filter fun x : triangulationCorners T => x.1.1 = v).image .omega)

/-- A dart lies in `D_v` exactly when it is `λ_v` or `ω_x` for a corner `x` with first entry `v`.
-/
theorem mem_triangulationWhiteDarts {v : ZMod m} {d : TriangulationDart T} :
    d ∈ triangulationWhiteDarts T v ↔
      d = .lam v ∨ ∃ x : triangulationCorners T, x.1.1 = v ∧ d = .omega x := by
  simp only [triangulationWhiteDarts, mem_insert, mem_image, mem_filter, mem_univ, true_and]
  exact or_congr_right (exists_congr fun _ => and_congr_right fun _ => eq_comm)

section White

open TriangulationDart

variable (hm : 3 ≤ m) (hT : IsTriangulation T)

include hm hT

/-- `σ` maps `D_v` into itself. -/
theorem triangulationRot_mem_triangulationWhiteDarts {v : ZMod m} {d : TriangulationDart T}
    (hd : d ∈ triangulationWhiteDarts T v) :
    triangulationRot T d ∈ triangulationWhiteDarts T v := by
  rw [mem_triangulationWhiteDarts] at hd ⊢
  rcases hd with rfl | ⟨x, rfl, rfl⟩
  · obtain ⟨z, hz₁, -, hz⟩ := exists_triangulationRot_lam hm hT v
    exact .inr ⟨z, hz₁, hz⟩
  · rcases triangulationRot_omega_cases hm hT x with ⟨-, hr⟩ | ⟨y, hy₁, -, hr⟩
    · exact .inl hr
    · exact .inr ⟨y, hy₁, hr⟩

/-- Every dart of `D_v` lies in the orbit of `λ_v` under `σ`: iterating `σ` from `ω_(v,b,c)`
moves `b` strictly towards `v` until `σ` reaches `λ_v`. -/
theorem sameCycle_lam_of_mem_triangulationWhiteDarts {v : ZMod m} {d : TriangulationDart T}
    (hd : d ∈ triangulationWhiteDarts T v) :
    (triangulationPlabicData hm hT).rot.SameCycle d (lam v) := by
  rw [mem_triangulationWhiteDarts] at hd
  rcases hd with rfl | ⟨x, hx, rfl⟩
  · exact Equiv.Perm.SameCycle.refl _ _
  suffices ∀ n : ℕ, ∀ x : triangulationCorners T, x.1.1 = v → (basePos v x.1.2.1).toNat = n →
      (triangulationPlabicData hm hT).rot.SameCycle (omega x) (lam v) from this _ x hx rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hn
    rw [← Equiv.Perm.sameCycle_apply_left, triangulationPlabicData_rot_apply]
    rcases triangulationRot_omega_cases hm hT x with ⟨-, hr⟩ | ⟨y, hy₁, hy₂, hr⟩
    · rw [hr, hx]
    · rw [hr]
      have hlt : basePos v y.1.2.1 < basePos v x.1.2.1 := by
        have hy := (mem_triangulationCorners_iff.1 y.2).1
        rw [hy₁, hy₂, hx] at hy
        exact basePos_lt_basePos_of_sbtw hy
      have := basePos_nonneg v y.1.2.1
      exact ih _ (by omega) y (hy₁.trans hx) rfl

/-- **The rotation at a white vertex of `G(T)`**: `σ` restricts to a cyclic permutation of the set
`D_v = {λ_v} ∪ {ω_x : x ∈ C(T), x has first entry v}`. -/
@[cluster_algebras "lem_triangulation_white_rotation"]
theorem isCycleOn_triangulationWhiteDarts (v : ZMod m) :
    (triangulationPlabicData hm hT).rot.IsCycleOn (triangulationWhiteDarts T v : Set _) := by
  have hmaps : Set.MapsTo (triangulationPlabicData hm hT).rot (triangulationWhiteDarts T v)
      (triangulationWhiteDarts T v) := fun d hd =>
    triangulationRot_mem_triangulationWhiteDarts hm hT (Finset.mem_coe.1 hd)
  exact ⟨((Set.toFinite _).injOn_iff_bijOn_of_mapsTo hmaps).1 (Equiv.injective _).injOn,
    fun d hd e he => (sameCycle_lam_of_mem_triangulationWhiteDarts hm hT hd).trans
      (sameCycle_lam_of_mem_triangulationWhiteDarts hm hT he).symm⟩

/-- The white vertex `v` of `G(T)`, the vertex of `λ_v`, is `D_v`. -/
theorem vertexOf_lam_triangulationPlabicData (v : ZMod m) :
    (triangulationPlabicData hm hT).vertexOf (lam v) = triangulationWhiteDarts T v := by
  ext e
  rw [RotationSystem.mem_vertexOf]
  refine ⟨fun h => ?_, fun h => (sameCycle_lam_of_mem_triangulationWhiteDarts hm hT h).symm⟩
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simp [mem_triangulationWhiteDarts]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, triangulationPlabicData_rot_apply]
    exact triangulationRot_mem_triangulationWhiteDarts hm hT ih

end White

/-! ### Facts about the colour and the labels -/

/-- The rotation `σ` of `G(T)` preserves the colour of darts. -/
theorem colour_triangulationRot (d : TriangulationDart T) :
    (triangulationRot T d).colour = d.colour := by
  cases d <;> simp only [triangulationRot] <;> (try split) <;> rfl

omit [NeZero m] in
/-- The successor of a label: `finRotate m i` is the label `i + 1` modulo `m`. -/
theorem natCast_finRotate (i : Fin m) :
    ((finRotate m i : ℕ) : ZMod m) = ((i : ℕ) : ZMod m) + 1 := by
  rw [finRotate_apply, Fin.val_add, ZMod.natCast_mod, Nat.cast_add, Fin.val_one',
    ZMod.natCast_mod, Nat.cast_one]

/-- The number of segments of a triangulation of the `m`-gon, `m ≥ 3`: its `m - 3` diagonals and
the `m` sides. -/
theorem card_segments (hm : 3 ≤ m) (hT : IsTriangulation T) :
    (segments T).card = 2 * m - 3 := by
  have hTcard : T.card = m - 3 := by
    rcases (show m = 3 ∨ 4 ≤ m by omega) with h | h
    · rw [IsTriangulation.eq_empty_of_eq_three h hT, Finset.card_empty]
      omega
    · exact IsTriangulation.card_eq h hT
  rw [segments, Finset.card_union_of_disjoint, hTcard, card_filter_isSide hm]
  · omega
  · exact Finset.disjoint_left.2 fun e he hs => (hT.isDiagonal e he).2 (Finset.mem_filter.1 hs).2

/-- A side `{v - 1, v}` is a segment. -/
theorem sub_one_mem_segments (v : ZMod m) : s(v - 1, v) ∈ segments T :=
  mem_segments.2 (.inr ⟨v - 1, by rw [sub_add_cancel]⟩)

/-- A side `{v, v + 1}` is a segment. -/
theorem add_one_mem_segments (v : ZMod m) : s(v, v + 1) ∈ segments T :=
  mem_segments.2 (.inr ⟨v, rfl⟩)

open TriangulationDart in
/-- The **face labelling** of `G(T)`: each dart is sent to the face to its right, recorded as
`none` for the exterior and as a segment of `T` otherwise:
`e_v ↦ ∞`, `ē_v, λ̄_v ↦ {v - 1, v}`, `λ_v ↦ {v, v + 1}`, `ω_(a,b,c) ↦ {a, c}` and
`ω̄_(a,b,c) ↦ {a, b}`. -/
def triangulationFaceLabel (T : Finset (Sym2 (ZMod m))) :
    TriangulationDart T → Option (segments T)
  | arc _ => none
  | arcBar v => some ⟨s(v - 1, v), sub_one_mem_segments v⟩
  | lamBar v => some ⟨s(v - 1, v), sub_one_mem_segments v⟩
  | lam v => some ⟨s(v, v + 1), add_one_mem_segments v⟩
  | omega x => some ⟨s(x.1.1, x.1.2.2), (mem_triangulationCorners_iff.1 x.2).2.2.2⟩
  | omegaBar x => some ⟨s(x.1.1, x.1.2.1), (mem_triangulationCorners_iff.1 x.2).2.1⟩

/-! ### `G(T)` is a plabic graph -/

section IsPlabicGraph

open TriangulationDart

variable (hm : 3 ≤ m) (hT : IsTriangulation T)

/-- The vertex of `ω_x` is the white vertex of the first entry of `x`. -/
theorem vertexOf_omega_triangulationPlabicData (x : triangulationCorners T) :
    (triangulationPlabicData hm hT).vertexOf (omega x) =
      (triangulationPlabicData hm hT).vertexOf (lam x.1.1) :=
  RotationSystem.vertexOf_eq_vertexOf_iff _ |>.2 <|
    sameCycle_lam_of_mem_triangulationWhiteDarts hm hT
      (mem_triangulationWhiteDarts.2 (.inr ⟨x, rfl, rfl⟩))

/-- The vertex of `e_v` is the boundary vertex `p_v`. -/
theorem vertexOf_arc_triangulationPlabicData (v : ZMod m) :
    (triangulationPlabicData hm hT).vertexOf (arc v) =
      (triangulationPlabicData hm hT).vertexOf (lamBar v) := by
  rw [← RotationSystem.vertexOf_rot]
  rfl

/-- The vertex of `ē_v` is the boundary vertex `p_(v-1)`. -/
theorem vertexOf_arcBar_triangulationPlabicData (v : ZMod m) :
    (triangulationPlabicData hm hT).vertexOf (arcBar v) =
      (triangulationPlabicData hm hT).vertexOf (lamBar (v - 1)) := by
  rw [← RotationSystem.vertexOf_rot (d := lamBar (v - 1))]
  simp

/-- Every dart of `G(T)` is reachable from `e_0`. -/
theorem reach_arc_zero_triangulationPlabicData (d : TriangulationDart T) :
    (triangulationPlabicData hm hT).Reach (arc 0) d := by
  set G := triangulationPlabicData hm hT
  have harc : ∀ (v : ZMod m) (k : ℕ), G.Reach (arc v) (arc (v - k)) := by
    intro v k
    induction k with
    | zero => simpa using RotationSystem.Reach.refl _
    | succ k ih => simpa [G, sub_sub] using ih.inv.rot
  have harc' : ∀ w : ZMod m, G.Reach (arc 0) (arc w) := fun w => by
    simpa using harc 0 (-w).val
  have hlam : ∀ w : ZMod m, G.Reach (arc 0) (lam w) := fun w => by
    simpa [G] using (harc' w).rot.inv
  have homega : ∀ x : triangulationCorners T, G.Reach (arc 0) (omega x) := fun x => by
    obtain ⟨n, hn⟩ := (sameCycle_lam_of_mem_triangulationWhiteDarts hm hT
      (mem_triangulationWhiteDarts.2 (.inr ⟨x, rfl, rfl⟩))).symm.exists_nat_pow_eq
    have := G.reach_pow_apply (g := G.rot) (fun y => (RotationSystem.Reach.refl y).rot) n
      (lam x.1.1)
    rw [hn] at this
    exact (hlam _).trans this
  cases d with
  | arc w => exact harc' w
  | arcBar w => simpa [G] using (harc' w).inv
  | lamBar w => simpa [G] using (harc' w).rot
  | lam w => exact hlam w
  | omega x => exact homega x
  | omegaBar x => simpa [G] using (homega x).inv

/-- The rotation system of `G(T)` is connected. -/
theorem isConnected_triangulationPlabicData :
    (triangulationPlabicData hm hT).IsConnected :=
  RotationSystem.IsConnected.of_reach ⟨lam 0⟩ reverse_involutive reverse_ne fun d e =>
    (reach_arc_zero_triangulationPlabicData hm hT d).symm.trans
      (reach_arc_zero_triangulationPlabicData hm hT e)

/-! #### Counting vertices -/

/-- The rotation of a corner moves it. -/
theorem rotateCorner_ne (x : triangulationCorners T) : rotateCorner x ≠ x := by
  obtain ⟨⟨a, b, c⟩, hx⟩ := x
  intro h
  simp only [rotateCorner, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, -⟩ := h
  exact sbtw_irrefl_left_right (mem_triangulationCorners_iff.1 hx).1

/-- Rotating a corner twice moves it. -/
theorem rotateCorner_rotateCorner_ne (x : triangulationCorners T) :
    rotateCorner (rotateCorner x) ≠ x := by
  obtain ⟨⟨a, b, c⟩, hx⟩ := x
  intro h
  simp only [rotateCorner, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, -⟩ := h
  exact sbtw_irrefl_left (mem_triangulationCorners_iff.1 hx).1

/-- Two darts `ω̄_y`, `ω̄_x` lie at the same black vertex exactly when `y` is a cyclic rotation
of `x`. -/
theorem vertexOf_omegaBar_eq_iff {x y : triangulationCorners T} :
    (triangulationPlabicData hm hT).vertexOf (omegaBar y) =
        (triangulationPlabicData hm hT).vertexOf (omegaBar x) ↔
      y = x ∨ y = rotateCorner x ∨ y = rotateCorner (rotateCorner x) := by
  set G := triangulationPlabicData hm hT
  constructor
  · intro h
    have hy : omegaBar y ∈ G.vertexOf (omegaBar x) := h ▸ G.self_mem_vertexOf _
    rw [vertexOf_omegaBar_triangulationPlabicData] at hy
    simpa using hy
  · rintro (rfl | rfl | rfl)
    · rfl
    · exact G.vertexOf_rot (omegaBar x)
    · exact (G.vertexOf_rot (omegaBar (rotateCorner x))).trans (G.vertexOf_rot (omegaBar x))

/-- `G(T)` has `m - 2` black vertices, one for each triangle of `T`. -/
theorem card_image_vertexOf_omegaBar :
    (univ.image fun x : triangulationCorners T =>
      (triangulationPlabicData hm hT).vertexOf (omegaBar x)).card = m - 2 := by
  set G := triangulationPlabicData hm hT
  have h := Finset.card_eq_sum_card_image
    (fun x : triangulationCorners T => G.vertexOf (omegaBar x)) univ
  rw [Finset.sum_const_nat (m := 3) ?_] at h
  · rw [Finset.card_univ, Fintype.card_coe, card_triangulationCorners hm hT] at h
    omega
  · intro s hs
    obtain ⟨x, -, rfl⟩ := mem_image.1 hs
    rw [show (univ.filter fun y : triangulationCorners T =>
        G.vertexOf (omegaBar y) = G.vertexOf (omegaBar x)) =
          {x, rotateCorner x, rotateCorner (rotateCorner x)} by
      ext y
      simp [G, vertexOf_omegaBar_eq_iff]]
    exact card_eq_three.2 ⟨_, _, _, (rotateCorner_ne x).symm,
      (rotateCorner_rotateCorner_ne x).symm,
      fun h => rotateCorner_ne x (rotateCorner_injective h).symm, rfl⟩

/-- The vertices of `G(T)`: the white vertices `D_v`, the boundary vertices `p_v` and the black
vertices. -/
theorem vertices_triangulationPlabicData :
    (triangulationPlabicData hm hT).vertices =
      ((univ.image fun v => (triangulationPlabicData hm hT).vertexOf (lam v)) ∪
        (univ.image fun v => (triangulationPlabicData hm hT).vertexOf (lamBar v))) ∪
        univ.image fun x => (triangulationPlabicData hm hT).vertexOf (omegaBar x) := by
  ext s
  simp only [RotationSystem.mem_vertices, mem_union, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨d, rfl⟩
    cases d with
    | omega x => exact .inl (.inl ⟨x.1.1, (vertexOf_omega_triangulationPlabicData hm hT x).symm⟩)
    | omegaBar x => exact .inr ⟨x, rfl⟩
    | lam v => exact .inl (.inl ⟨v, rfl⟩)
    | lamBar v => exact .inl (.inr ⟨v, rfl⟩)
    | arc v => exact .inl (.inr ⟨v, (vertexOf_arc_triangulationPlabicData hm hT v).symm⟩)
    | arcBar v =>
      exact .inl (.inr ⟨v - 1, (vertexOf_arcBar_triangulationPlabicData hm hT v).symm⟩)
  · rintro ((⟨v, rfl⟩ | ⟨v, rfl⟩) | ⟨x, rfl⟩) <;> exact ⟨_, rfl⟩

/-- `G(T)` has `3m - 2` vertices: `m` white vertices, `m` boundary vertices and `m - 2` black
vertices. -/
theorem card_vertices_triangulationPlabicData :
    (triangulationPlabicData hm hT).vertices.card = 3 * m - 2 := by
  set G := triangulationPlabicData hm hT
  have hmem : ∀ {d e : TriangulationDart T}, G.vertexOf d = G.vertexOf e → d ∈ G.vertexOf e :=
    fun h => h ▸ G.self_mem_vertexOf _
  rw [vertices_triangulationPlabicData, card_union_of_disjoint, card_union_of_disjoint,
    card_image_of_injective, card_image_of_injective, card_image_vertexOf_omegaBar,
    card_univ, ZMod.card]
  · omega
  · intro v w h
    simpa [G, vertexOf_lamBar_triangulationPlabicData] using hmem h
  · intro v w h
    simpa [G, vertexOf_lam_triangulationPlabicData, mem_triangulationWhiteDarts] using hmem h
  · rw [disjoint_left]
    simp only [mem_image, mem_univ, true_and]
    rintro _ ⟨v, rfl⟩ ⟨w, h⟩
    simpa [G, vertexOf_lamBar_triangulationPlabicData] using hmem h.symm
  · rw [disjoint_left]
    simp only [mem_union, mem_image, mem_univ, true_and]
    rintro _ (⟨v, rfl⟩ | ⟨v, rfl⟩) ⟨x, h⟩
    · simpa [G, vertexOf_lam_triangulationPlabicData, mem_triangulationWhiteDarts] using hmem h
    · simpa [G, vertexOf_lamBar_triangulationPlabicData] using hmem h

/-! #### Counting edges -/

/-- The darts `ω_x`, `λ_v` and `e_v`: one dart of each edge of `G(T)`. -/
private def edgeDart : triangulationCorners T ⊕ ZMod m ⊕ ZMod m → TriangulationDart T :=
  Sum.elim omega (Sum.elim lam arc)

/-- `G(T)` has `|C(T)| + 2m = 5m - 6` edges. -/
theorem card_edges_triangulationPlabicData :
    (triangulationPlabicData hm hT).edges.card = 3 * m - 6 + 2 * m := by
  set G := triangulationPlabicData hm hT
  have hE : G.edges = univ.image fun p => G.edgeOf (edgeDart p) := by
    ext s
    simp only [RotationSystem.mem_edges, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨d, rfl⟩
      cases d with
      | omega x => exact ⟨.inl x, rfl⟩
      | lam v => exact ⟨.inr (.inl v), rfl⟩
      | arc v => exact ⟨.inr (.inr v), rfl⟩
      | omegaBar x => exact ⟨.inl x, pair_comm _ _⟩
      | lamBar v => exact ⟨.inr (.inl v), pair_comm _ _⟩
      | arcBar v => exact ⟨.inr (.inr v), pair_comm _ _⟩
    · rintro ⟨p, rfl⟩
      exact ⟨_, rfl⟩
  rw [hE, card_image_of_injective, card_univ, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_coe, card_triangulationCorners hm hT, ZMod.card]
  · ring
  · intro p q h
    have h' : G.edgeOf (edgeDart p) = G.edgeOf (edgeDart q) := h
    have : edgeDart p ∈ G.edgeOf (edgeDart q) := h' ▸ (G.mem_edgeOf.2 (.inl rfl))
    rw [RotationSystem.mem_edgeOf] at this
    rcases p with x | v | v <;> rcases q with y | w | w <;>
      simp only [G, edgeDart, Sum.elim_inl, Sum.elim_inr, triangulationPlabicData_inv_apply,
        reverse_omega, reverse_lam, reverse_arc, omega.injEq, lam.injEq, arc.injEq, reduceCtorEq,
        or_false] at this <;>
      rw [this]

/-! #### Counting faces -/

/-- The face labelling of `G(T)` is constant along the face permutation `φ`. -/
theorem triangulationFaceLabel_facePerm (d : TriangulationDart T) :
    triangulationFaceLabel T ((triangulationPlabicData hm hT).facePerm d) =
      triangulationFaceLabel T d := by
  rw [RotationSystem.facePerm_apply, triangulationPlabicData_inv_apply,
    triangulationPlabicData_rot_apply]
  cases d with
  | arc v => rfl
  | arcBar v => rfl
  | lamBar v =>
    obtain ⟨y, hy₁, hy₂, hr⟩ := exists_triangulationRot_lam hm hT v
    rw [reverse_lamBar, hr]
    simp only [triangulationFaceLabel, hy₁, hy₂, Option.some.injEq, Subtype.mk.injEq]
    exact Sym2.eq_swap
  | lam v => simp [triangulationFaceLabel]
  | omega x =>
    simp only [reverse_omega, triangulationRot_omegaBar, triangulationFaceLabel,
      coe_rotateCorner, Option.some.injEq, Subtype.mk.injEq]
    exact Sym2.eq_swap
  | omegaBar x =>
    rw [reverse_omegaBar]
    rcases triangulationRot_omega_cases hm hT x with ⟨hb, hr⟩ | ⟨y, hy₁, hy₂, hr⟩
    · simp only [hr, triangulationFaceLabel, hb]
    · simp only [hr, triangulationFaceLabel, hy₁, hy₂]

include hm hT in
/-- Every label is taken: `∞` by `e_0`, a side `{v, v + 1}` by `λ_v`, and a diagonal `{a, c}` of
`T` by `ω_(a,b,c)` for the apex `b` over it. -/
theorem triangulationFaceLabel_surjective :
    Function.Surjective (triangulationFaceLabel T) := by
  rintro (_ | ⟨e, he⟩)
  · exact ⟨arc 0, rfl⟩
  rcases mem_segments.1 he with h | ⟨i, rfl⟩
  · induction e using Sym2.ind with | _ a c => ?_
    have hc : c ≠ a + 1 := fun hc => (hT.isDiagonal _ h).2 ⟨a, by rw [hc]⟩
    obtain ⟨b, hb, -⟩ := existsUnique_mem_triangulationCorners hm hT he hc
    exact ⟨omega ⟨(a, b, c), hb⟩, rfl⟩
  · exact ⟨lam i, rfl⟩

include hm hT in
/-- There are `2m - 2` labels: `∞` and the `2m - 3` segments of `T`. -/
theorem card_option_segments :
    Fintype.card (Option (segments T)) = 2 * m - 2 := by
  rw [Fintype.card_option, Fintype.card_coe, card_segments hm hT]
  omega

/-- Euler's relation for the labels: `|V| - |E| + |L| = 2`. -/
theorem euler_option_segments :
    ((triangulationPlabicData hm hT).vertices.card : ℤ) -
        (triangulationPlabicData hm hT).edges.card + Fintype.card (Option (segments T)) = 2 := by
  rw [card_vertices_triangulationPlabicData, card_edges_triangulationPlabicData,
    card_option_segments hm hT]
  omega

/-- Two darts of `G(T)` lie on the same face exactly when they have the same label. -/
theorem faceOf_eq_faceOf_iff_triangulationFaceLabel (d e : TriangulationDart T) :
    (triangulationPlabicData hm hT).faceOf d = (triangulationPlabicData hm hT).faceOf e ↔
      triangulationFaceLabel T d = triangulationFaceLabel T e :=
  (isConnected_triangulationPlabicData hm hT).faceOf_eq_faceOf_iff_of_surjective
    (triangulationFaceLabel_surjective hm hT) (triangulationFaceLabel_facePerm hm hT)
    (euler_option_segments hm hT) d e

/-- `G(T)` has `2m - 2` faces (orbits of `φ`): the exterior and one for each segment of `T`. -/
theorem card_faceOrbits_triangulationPlabicData :
    (triangulationPlabicData hm hT).faceOrbits.card = 2 * m - 2 := by
  have hle := (isConnected_triangulationPlabicData hm hT).euler_le
  have hL := euler_option_segments hm hT
  have hge : Fintype.card (Option (segments T)) ≤
      (triangulationPlabicData hm hT).faceOrbits.card := by
    have hs := triangulationFaceLabel_surjective hm hT
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun l => (triangulationPlabicData hm hT).faceOf (Function.surjInv hs l))
      (fun l _ => RotationSystem.faceOf_mem_faceOrbits _ _) ?_
    intro l _ l' _ h
    have := (faceOf_eq_faceOf_iff_triangulationFaceLabel hm hT _ _).1 h
    rwa [Function.surjInv_eq hs, Function.surjInv_eq hs] at this
  rw [card_option_segments hm hT] at hL hge
  omega

/-- The exterior face of `G(T)`, the orbit of `e_0` under `φ`, consists of the darts `e_v`. -/
theorem faceOf_arc_zero_triangulationPlabicData :
    (triangulationPlabicData hm hT).faceOf (arc 0) = univ.image arc := by
  ext e
  rw [RotationSystem.mem_faceOf, ← RotationSystem.faceOf_eq_faceOf_iff,
    faceOf_eq_faceOf_iff_triangulationFaceLabel]
  cases e <;> simp [triangulationFaceLabel]

/-! #### The boundary vertices -/

/-- Every boundary vertex of `G(T)` is a vertex `p_u = {λ̄_u, ē_(u+1), e_u}`. -/
theorem exists_eq_vertexOf_lamBar_of_mem_boundaryVertices {s : Finset (TriangulationDart T)}
    (hs : s ∈ (triangulationPlabicData hm hT).boundaryVertices) :
    ∃ u, s = (triangulationPlabicData hm hT).vertexOf (lamBar u) := by
  set G := triangulationPlabicData hm hT
  obtain ⟨hs, e, he, heB⟩ := G.mem_boundaryVertices.1 hs
  obtain ⟨d, rfl⟩ := G.mem_vertices.1 hs
  rw [← G.vertexOf_eq_of_mem he]
  obtain ⟨w, rfl | rfl⟩ := (mem_triangulationPlabicData_bdry hm hT).1 heB
  · exact ⟨w, vertexOf_arc_triangulationPlabicData hm hT w⟩
  · exact ⟨w - 1, vertexOf_arcBar_triangulationPlabicData hm hT w⟩

/-- Every boundary vertex of `G(T)` has three darts, two of them boundary arcs. -/
theorem boundaryVertex_card_triangulationPlabicData :
    ∀ s ∈ (triangulationPlabicData hm hT).boundaryVertices,
      s.card = 3 ∧ (s.filter (· ∈ (triangulationPlabicData hm hT).bdry)).card = 2 := by
  intro s hs
  obtain ⟨u, rfl⟩ := exists_eq_vertexOf_lamBar_of_mem_boundaryVertices hm hT hs
  rw [vertexOf_lamBar_triangulationPlabicData]
  refine ⟨card_eq_three.2 ⟨_, _, _, by simp, by simp, by simp, rfl⟩, ?_⟩
  simp [filter_insert, filter_singleton, mem_triangulationPlabicData_bdry]

/-! #### The theorem -/

/-- **`G(T)` is a plabic graph**: for a triangulation `T` of the convex `m`-gon, `m ≥ 3`, the tuple
`G(T)` is a plabic graph with `m` boundary vertices. Its vertices are the `m` white vertices `D_v`,
the `m - 2` black vertices of the triangles and the `m` boundary vertices
`p_v = {λ̄_v, ē_(v+1), e_v}`; it has `5m - 6` edges; and its `2m - 2` faces are the exterior
`{e_v}` and one face for each segment of `T`. -/
@[cluster_algebras "lem_triangulation_plabic_graph"]
theorem isPlabicGraph_triangulationPlabicData :
    (triangulationPlabicData hm hT).IsPlabicGraph where
  toIsConnected := isConnected_triangulationPlabicData hm hT
  inv_mem_bdry d hd := by
    obtain ⟨v, rfl | rfl⟩ := (mem_triangulationPlabicData_bdry hm hT).1 hd
    · exact (mem_triangulationPlabicData_bdry hm hT).2 ⟨v, .inr rfl⟩
    · exact (mem_triangulationPlabicData_bdry hm hT).2 ⟨v, .inl rfl⟩
  euler := by
    rw [card_vertices_triangulationPlabicData, card_edges_triangulationPlabicData,
      card_faceOrbits_triangulationPlabicData]
    omega
  boundaryVertex_card := boundaryVertex_card_triangulationPlabicData hm hT
  exists_orbit := by
    have hmap : (univ.image arc).map (triangulationPlabicData hm hT).inv.toEmbedding =
        univ.image arcBar := by
      rw [map_eq_image, image_image]
      rfl
    refine ⟨univ.image arc, ?_, ?_, ?_, ?_⟩
    · rw [← faceOf_arc_zero_triangulationPlabicData hm hT]
      exact RotationSystem.faceOf_mem_faceOrbits _ _
    · intro d hd
      obtain ⟨v, -, rfl⟩ := mem_image.1 hd
      exact (mem_triangulationPlabicData_bdry hm hT).2 ⟨v, .inl rfl⟩
    · rw [hmap]
      ext d
      rw [mem_triangulationPlabicData_bdry]
      cases d <;> simp
    · rw [hmap, disjoint_left]
      simp
  one_le := by omega
  colour_rot d _ := colour_triangulationRot d
  leg_notMem_bdry i := by simp [mem_triangulationPlabicData_bdry]
  bvertex_mem i := by
    rw [triangulationPlabicData_bvertex, DiskMap.vertexOf_mem_boundaryVertices]
    refine ⟨arc ((i + 1 : ℕ) : ZMod m), ?_, ?_⟩
    · rw [vertexOf_lamBar_triangulationPlabicData]
      simp
    · exact (mem_triangulationPlabicData_bdry hm hT).2 ⟨_, .inl rfl⟩
  bvertex_injective i j h := by
    have hmem : lamBar ((i + 1 : ℕ) : ZMod m) ∈ (triangulationPlabicData hm hT).bvertex j :=
      h ▸ (triangulationPlabicData hm hT).leg_mem_bvertex i
    rw [triangulationPlabicData_bvertex, vertexOf_lamBar_triangulationPlabicData] at hmem
    simp only [mem_insert, mem_singleton, lamBar.injEq, reduceCtorEq, or_false] at hmem
    push_cast at hmem
    exact Fin.ext ((natCast_inj_of_lt i.2 j.2).1 (add_right_cancel hmem))
  exists_bvertex_eq s hs := by
    obtain ⟨u, rfl⟩ := exists_eq_vertexOf_lamBar_of_mem_boundaryVertices hm hT hs
    refine ⟨⟨(u - 1).val, ZMod.val_lt _⟩, ?_⟩
    rw [triangulationPlabicData_bvertex]
    have hu : ((((u - 1).val + 1 : ℕ)) : ZMod m) = u := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    exact congrArg (fun w => (triangulationPlabicData hm hT).vertexOf (lamBar w)) hu
  exists_exterior i := by
    refine ⟨arc (((i + 1 : ℕ) : ZMod m) + 1), ?_, ?_, ?_⟩
    · rw [DiskMap.mem_exterior]
      simp [mem_triangulationPlabicData_bdry]
    · have hi : (((finRotate m i : ℕ) + 1 : ℕ) : ZMod m) = ((i + 1 : ℕ) : ZMod m) + 1 := by
        push_cast
        rw [natCast_finRotate]
      rw [triangulationPlabicData_bvertex, hi, vertexOf_lamBar_triangulationPlabicData]
      simp
    · rw [triangulationPlabicData_bvertex, vertexOf_lamBar_triangulationPlabicData]
      simp

end IsPlabicGraph

end ClusterAlgebras

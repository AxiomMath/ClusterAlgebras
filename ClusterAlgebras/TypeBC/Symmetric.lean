/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeBC.Polygon
public import ClusterAlgebras.Folding.Defs

/-!
# Centrally symmetric triangulations

The half-turn `ω : x ↦ x + n + 1` of the convex `(2n + 2)`-gon, centrally symmetric
triangulations, and symmetric labelled triangulations `(T, λ)`, whose labels `[1, 2n - 1]` are
exchanged by the involution `ι_C : p ↦ 2n - p` exactly as `ω` exchanges the diagonals. Orbit
mutation of `B(T, λ)` is a flip of a diameter or of a pair of centrally symmetric diagonals
(FWZ's Section 5.5), and `B(T, λ)` is admissible for the action of `ι_C`.

## Main definitions

* `ClusterAlgebras.TypeBC.halfTurn n`: the half-turn `ω` of `ZMod (2n + 2)`.
* `ClusterAlgebras.TypeBC.IsDiameter n`, `ClusterAlgebras.TypeBC.IsCentrallySymmetric n`.
* `ClusterAlgebras.TypeBC.iotaC n`: the involution `ι_C` of `Fin (2n - 1)`.
* `ClusterAlgebras.TypeBC.IsSymmetricLabelledTriangulation n T ℓ`.

## Main statements

* `ClusterAlgebras.TypeBC.map_halfTurn_eq_self_iff`: the half-turn fixes exactly the diameters.
* `ClusterAlgebras.TypeBC.IsSymmetricLabelledTriangulation.exists_matrixMutationList`: orbit
  mutation of `B(T, λ)` is realised by a symmetric labelled triangulation.
* `ClusterAlgebras.TypeBC.IsSymmetricLabelledTriangulation.isGroupAdmissible`: `B(T, λ)` is
  admissible for the action of `ι_C`.

## Implementation notes

* Labels are `Fin (2n - 1)`, shifted down by one: the involution `ι_C(p) = 2n - p` on
  `[1, 2n - 1]` becomes `p ↦ 2n - 2 - p`, which is `Fin.rev`, and its fixed label `n` is `n - 1`.
  Polygon vertices are elements of `ZMod (2n + 2)`, not shifted.
* As in `ClusterAlgebras/TypeBC/TypeB.lean`, the action of `ℤ/2ℤ` by `ι_C` is the action of
  `Subgroup.zpowers (iotaC n)` on `Fin (2n - 1)`.
* Disjointness `γ ∩ ω(γ) = ∅` of two segments is stated elementwise:
  `∀ x ∈ γ, x ∉ ω(γ)`.
* The orbit `K` of `ι_C` in `IsSymmetricLabelledTriangulation.exists_matrixMutationList` is
  `{p, ι_C(p)}` for a label `p`, which covers both kinds of orbits (`p = n - 1` gives the fixed
  orbit).
* The definitions are made for every `n`; the results assume `n ≥ 2`.
-/

@[expose] public section

namespace ClusterAlgebras

namespace TypeBC

open MulAction

variable (n : ℕ)

/-- The **half-turn** `ω` of the convex `(2n + 2)`-gon: `x ↦ x + n + 1` on `ZMod (2n + 2)`. It is
applied to segments by `Sym2.map` and to sets of segments by `Finset.image`. -/
@[cluster_algebras "def_half_turn"]
def halfTurn (x : ZMod (2 * n + 2)) : ZMod (2 * n + 2) :=
  x + ((n + 1 : ℕ) : ZMod (2 * n + 2))

/-- A **diameter** of the `(2n + 2)`-gon: a segment `{x, x + n + 1}`. -/
@[cluster_algebras "def_half_turn"]
def IsDiameter (e : Sym2 (ZMod (2 * n + 2))) : Prop :=
  ∃ x, e = s(x, halfTurn n x)

/-- A set `T` of segments of the `(2n + 2)`-gon is **centrally symmetric** when `ω(T) = T`. -/
@[cluster_algebras "def_half_turn"]
def IsCentrallySymmetric (T : Finset (Sym2 (ZMod (2 * n + 2)))) : Prop :=
  T.image (Sym2.map (halfTurn n)) = T

/-- The involution **`ι_C`** of the labels `Fin (2n - 1)`: `p ↦ 2n - 2 - p`, which is `Fin.rev`;
this is `p ↦ 2n - p` on `[1, 2n - 1]` with labels shifted down by one. -/
@[cluster_algebras "def_half_turn"]
def iotaC : Equiv.Perm (Fin (2 * n - 1)) :=
  Fin.revPerm

/-- The values of `ι_C`: `ι_C(p) = 2n - 2 - p`. -/
@[cluster_algebras "def_half_turn"]
theorem iotaC_val (p : Fin (2 * n - 1)) : (iotaC n p : ℕ) = 2 * n - 2 - p := by
  simp only [iotaC, Fin.revPerm_apply, Fin.val_rev]
  omega

/-- `ι_C` is an involution. -/
theorem iotaC_mul_self : iotaC n * iotaC n = 1 := by
  ext p
  simp [iotaC]

/-- A **symmetric labelled triangulation** `(T, λ)`: `T` is a centrally symmetric triangulation
of the convex `(2n + 2)`-gon and `λ : Fin (2n - 1) → T` is a bijection with
`λ(ι_C(p)) = ω(λ(p))` for every label `p`. -/
@[cluster_algebras "def_half_turn"]
structure IsSymmetricLabelledTriangulation (T : Finset (Sym2 (ZMod (2 * n + 2))))
    (ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))) : Prop where
  /-- `T` is a triangulation. -/
  isTriangulation : IsTriangulation T
  /-- `T` is centrally symmetric. -/
  isCentrallySymmetric : IsCentrallySymmetric n T
  /-- `ℓ` is a bijection onto `T`. -/
  isTriangulationLabelling : IsTriangulationLabelling T ℓ
  /-- `λ(ι_C(p)) = ω(λ(p))`. -/
  apply_iotaC : ∀ p, ℓ (iotaC n p) = (ℓ p).map (halfTurn n)

variable {n}

/-! ### Representatives

Statements about `ZMod (2n + 2)` reduce to linear arithmetic on representatives through
`ClusterAlgebras.TypeBC.sbtw_iff_val` and its companions in
`ClusterAlgebras/TypeBC/Polygon.lean`. -/

/-- Every element of `Sym2` is a pair. -/
private theorem symExists_eq_mk {α : Type*} (e : Sym2 α) : ∃ x y, e = s(x, y) := by
  induction e using Sym2.ind with
  | _ x y => exact ⟨x, y, rfl⟩

/-- A pair containing `y` differs from a pair not containing `y`. -/
private theorem symMk_ne {α : Type*} {x y u v : α} (hu : y ≠ u) (hv : y ≠ v) :
    s(x, y) ≠ s(u, v) := fun h => by
  have : y ∈ s(u, v) := h ▸ Sym2.mem_mk_right x y
  rcases Sym2.mem_iff.1 this with h' | h'
  exacts [hu h', hv h']

/-- A pair containing `y` differs from a pair not containing `y`. -/
private theorem symMk_ne' {α : Type*} {x y u v : α} (hu : y ≠ u) (hv : y ≠ v) :
    s(y, x) ≠ s(u, v) := by
  rw [Sym2.eq_swap]
  exact symMk_ne hu hv

section Reps

variable {m : ℕ} [NeZero m]

/-- The three vertices of a strict betweenness are distinct. -/
private theorem symNe_of_sbtw {x y z : ZMod m} (h : sbtw x y z) : x ≠ y ∧ y ≠ z ∧ x ≠ z := by
  rw [sbtw_iff_val] at h
  simp only [Ne, eq_iff_val]
  omega

end Reps

/-- The representative of `n + 1` in `ZMod (2n + 2)`. -/
private theorem val_halfTurnConst : ((n + 1 : ℕ) : ZMod (2 * n + 2)).val = n + 1 :=
  ZMod.val_natCast_of_lt (by omega)

/-- The representative of `ω(x)`. -/
private theorem val_halfTurn (x : ZMod (2 * n + 2)) :
    (halfTurn n x).val = if x.val < n + 1 then x.val + (n + 1) else x.val - (n + 1) := by
  have := ZMod.val_lt x
  rw [halfTurn, val_add_ite, val_halfTurnConst]
  split_ifs <;> omega

/-- `w = ω(z)` read on the representatives. -/
private theorem eq_halfTurn_iff_val {w z : ZMod (2 * n + 2)} :
    w = halfTurn n z ↔ w.val = z.val + (n + 1) ∨ z.val = w.val + (n + 1) := by
  have := ZMod.val_lt w
  have := ZMod.val_lt z
  rw [eq_iff_val, val_halfTurn]
  split_ifs <;> omega

/-- `ι_C(p) = p` exactly for the label `n - 1`. -/
private theorem iotaC_eq_self_iff {p : Fin (2 * n - 1)} : iotaC n p = p ↔ (p : ℕ) = n - 1 := by
  rw [Fin.ext_iff, iotaC_val]
  omega

/-- `ι_C` is an involution, pointwise. -/
private theorem iotaC_iotaC (p : Fin (2 * n - 1)) : iotaC n (iotaC n p) = p := by
  simp [iotaC]

/-! ### A diagonal and its half-turn -/

/-- **The half-turn is an involution**: `ω ∘ ω = id`. -/
@[cluster_algebras "lem_half_turn_diagonals"]
theorem halfTurn_halfTurn (x : ZMod (2 * n + 2)) : halfTurn n (halfTurn n x) = x := by
  have h : ((n + 1 : ℕ) : ZMod (2 * n + 2)) + ((n + 1 : ℕ) : ZMod (2 * n + 2)) = 0 := by
    rw [← Nat.cast_add, show n + 1 + (n + 1) = 2 * n + 2 by ring, ZMod.natCast_self]
  rw [halfTurn, halfTurn, add_assoc, h, add_zero]

/-- **The half-turn permutes the diagonals.** -/
@[cluster_algebras "lem_half_turn_diagonals"]
theorem isDiagonal_map_halfTurn_iff (e : Sym2 (ZMod (2 * n + 2))) :
    IsDiagonal (e.map (halfTurn n)) ↔ IsDiagonal e :=
  isDiagonal_map_add_iff _ e

/-- **Every diameter is a diagonal** (for `n ≥ 2`). -/
@[cluster_algebras "lem_half_turn_diagonals"]
theorem IsDiameter.isDiagonal (hn : 2 ≤ n) {e : Sym2 (ZMod (2 * n + 2))} (he : IsDiameter n e) :
    IsDiagonal e := by
  obtain ⟨x, rfl⟩ := he
  have hx := ZMod.val_lt x
  have hω := val_halfTurn x
  refine ⟨fun h => ?_, ?_⟩
  · rw [Sym2.mk_isDiag_iff, eq_iff_val, hω] at h
    split_ifs at h <;> omega
  · rintro ⟨i, hi⟩
    have := ZMod.val_lt i
    have h1 := val_add_ite i 1
    have h2 : (1 : ZMod (2 * n + 2)).val = 1 := by rw [val_one_ite, if_neg (by omega)]
    rcases Sym2.eq_iff.1 hi with ⟨rfl, h⟩ | ⟨h', h⟩
    · rw [eq_iff_val, hω, h1, h2] at h
      split_ifs at h h1 <;> omega
    · rw [eq_iff_val, h1, h2] at h'
      rw [eq_iff_val, hω] at h
      split_ifs at h h1 h' <;> omega

/-- **The half-turn fixes exactly the diameters**: `ω(γ) = γ` if and only if `γ` is a diameter. -/
@[cluster_algebras "lem_half_turn_diagonals"]
theorem map_halfTurn_eq_self_iff {γ : Sym2 (ZMod (2 * n + 2))} :
    γ.map (halfTurn n) = γ ↔ IsDiameter n γ := by
  obtain ⟨x, y, rfl⟩ := symExists_eq_mk γ
  constructor
  · intro h
    rw [Sym2.map_mk] at h
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · have := ZMod.val_lt x
      rw [eq_comm, eq_halfTurn_iff_val] at h1
      omega
    · exact ⟨x, by rw [h1]⟩
  · rintro ⟨z, hz⟩
    rw [hz, Sym2.map_mk, halfTurn_halfTurn]
    exact Sym2.eq_swap

/-- **A segment not fixed by the half-turn is disjoint from its half-turn**:
`γ ∩ ω(γ) = ∅`. -/
@[cluster_algebras "lem_half_turn_diagonals"]
theorem notMem_map_halfTurn {γ : Sym2 (ZMod (2 * n + 2))} (hne : γ.map (halfTurn n) ≠ γ) :
    ∀ x ∈ γ, x ∉ γ.map (halfTurn n) := by
  obtain ⟨x, y, rfl⟩ := symExists_eq_mk γ
  have hfix : ∀ z : ZMod (2 * n + 2), z ≠ halfTurn n z := fun z h => by
    have := ZMod.val_lt z
    rw [eq_halfTurn_iff_val] at h
    omega
  intro z hz hz'
  rw [Sym2.map_mk, Sym2.mem_iff] at hz'
  rw [Sym2.mem_iff] at hz
  rw [Sym2.map_mk] at hne
  rcases hz with rfl | rfl <;> rcases hz' with h | h <;>
    first | exact hfix _ h | exact hne (by rw [h, halfTurn_halfTurn]; exact Sym2.eq_swap)

/-- **The fixed label of a symmetric labelled triangulation is a diameter**: `λ(n)` (here the
label `n - 1`) is a diameter. -/
@[cluster_algebras "lem_half_turn_diagonals"]
theorem IsSymmetricLabelledTriangulation.isDiameter (hn : 2 ≤ n)
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} {ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))}
    (h : IsSymmetricLabelledTriangulation n T ℓ) : IsDiameter n (ℓ ⟨n - 1, by omega⟩) := by
  have hfix : iotaC n ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩ := iotaC_eq_self_iff.2 rfl
  refine map_halfTurn_eq_self_iff.1 ?_
  rw [← h.apply_iotaC, hfix]

/-- **The other labels of a symmetric labelled triangulation**: for `p ≠ n` (here `p ≠ n - 1`),
`λ(ι_C(p)) = ω(λ(p)) ≠ λ(p)` and `λ(p) ∩ λ(ι_C(p)) = ∅`. -/
@[cluster_algebras "lem_half_turn_diagonals"]
theorem IsSymmetricLabelledTriangulation.apply_iotaC_ne
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} {ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))}
    (h : IsSymmetricLabelledTriangulation n T ℓ) {p : Fin (2 * n - 1)} (hp : (p : ℕ) ≠ n - 1) :
    ℓ (iotaC n p) = (ℓ p).map (halfTurn n) ∧ ℓ (iotaC n p) ≠ ℓ p ∧
      ∀ x ∈ ℓ p, x ∉ ℓ (iotaC n p) := by
  have hne : ℓ (iotaC n p) ≠ ℓ p := fun h' =>
    hp (iotaC_eq_self_iff.1 (h.isTriangulationLabelling.1 h'))
  refine ⟨h.apply_iotaC p, hne, ?_⟩
  rw [h.apply_iotaC p]
  exact notMem_map_halfTurn (h.apply_iotaC p ▸ hne)

/-! ### Orbit mutation and admissibility -/

/-- The half-turn is injective on segments. -/
private theorem map_halfTurn_injective : Function.Injective (Sym2.map (halfTurn n)) :=
  Sym2.map.injective (add_left_injective _)

/-- The half-turn is an involution on segments. -/
private theorem map_halfTurn_map_halfTurn (e : Sym2 (ZMod (2 * n + 2))) :
    (e.map (halfTurn n)).map (halfTurn n) = e := by
  obtain ⟨x, y, rfl⟩ := symExists_eq_mk e
  simp only [Sym2.map_mk, halfTurn_halfTurn]

/-- Membership in the half-turn of a set of segments. -/
private theorem mem_image_map_halfTurn {S : Finset (Sym2 (ZMod (2 * n + 2)))}
    {e : Sym2 (ZMod (2 * n + 2))} :
    e ∈ S.image (Sym2.map (halfTurn n)) ↔ e.map (halfTurn n) ∈ S := by
  refine ⟨fun h => ?_, fun h => Finset.mem_image.2 ⟨_, h, map_halfTurn_map_halfTurn e⟩⟩
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 h
  rwa [map_halfTurn_map_halfTurn]

/-- A centrally symmetric set contains `ω(e)` exactly when it contains `e`. -/
private theorem IsCentrallySymmetric.map_mem_iff {T : Finset (Sym2 (ZMod (2 * n + 2)))}
    (hT : IsCentrallySymmetric n T) {e : Sym2 (ZMod (2 * n + 2))} :
    e.map (halfTurn n) ∈ T ↔ e ∈ T := by
  conv_lhs => rw [← hT]
  exact map_halfTurn_injective.mem_finset_image

/-- The half-turn of a flip is the flip of the half-turns. -/
private theorem image_map_halfTurn_flipTriangulation (T : Finset (Sym2 (ZMod (2 * n + 2))))
    (γ γ' : Sym2 (ZMod (2 * n + 2))) :
    (flipTriangulation T γ γ').image (Sym2.map (halfTurn n)) =
      flipTriangulation (T.image (Sym2.map (halfTurn n))) (γ.map (halfTurn n))
        (γ'.map (halfTurn n)) := by
  rw [flipTriangulation, flipTriangulation, Finset.image_insert,
    Finset.image_erase map_halfTurn_injective]

/-- The half-turn of a replacement is a replacement for the half-turned flip, in a centrally
symmetric triangulation. -/
private theorem IsCentrallySymmetric.isFlipReplacement_map {T : Finset (Sym2 (ZMod (2 * n + 2)))}
    (hT : IsCentrallySymmetric n T) {γ γ' : Sym2 (ZMod (2 * n + 2))}
    (h : IsFlipReplacement T γ γ') :
    IsFlipReplacement T (γ.map (halfTurn n)) (γ'.map (halfTurn n)) := by
  obtain ⟨hT', hγ, hd, hγ', hflip⟩ := h
  refine ⟨hT', hT.map_mem_iff.2 hγ, (isDiagonal_map_halfTurn_iff _).2 hd,
    fun h' => hγ' (hT.map_mem_iff.1 h'), ?_⟩
  have : IsTriangulation ((flipTriangulation T γ γ').image (Sym2.map (halfTurn n))) :=
    TypeBC.IsTriangulation.image_map_add _ hflip
  rwa [image_map_halfTurn_flipTriangulation, hT] at this

/-- Every element of a triangulation has a unique replacement. -/
private theorem symExists_replacement {m : ℕ} [NeZero m] {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) {γ : Sym2 (ZMod m)} (hγ : γ ∈ T) :
    ∃ γ', IsFlipReplacement T γ γ' ∧ ∀ γ'', IsFlipReplacement T γ γ'' → γ'' = γ' := by
  obtain ⟨a, c, rfl⟩ := symExists_eq_mk γ
  obtain ⟨b, d, -, -, -, -, -, h1, h2⟩ := exists_flip hT hγ
  exact ⟨_, h1, h2⟩

/-- `ω(x) = e` exactly when `x = ω(e)`. -/
private theorem map_halfTurn_eq_iff {x e : Sym2 (ZMod (2 * n + 2))} :
    x.map (halfTurn n) = e ↔ x = e.map (halfTurn n) := by
  constructor <;> rintro rfl <;> rw [map_halfTurn_map_halfTurn]

/-- If `γ' = {b, d}` replaces `γ = {a, c}` in a flip of a centrally symmetric triangulation `T`
and `γ` is disjoint from `ω(γ)`, then `γ'` and `ω(γ')` do not cross. -/
private theorem not_cross_halfTurn_of_isFlipReplacement {T : Finset (Sym2 (ZMod (2 * n + 2)))}
    (hS : IsCentrallySymmetric n T) {a b c d : ZMod (2 * n + 2)} (hγT : s(a, c) ∈ T)
    (hb : sbtw a b c) (hd : sbtw c d a) (tri1 : IsTriangle T {a, b, c})
    (tri2 : IsTriangle T {a, c, d}) (hγ' : IsFlipReplacement T s(a, c) s(b, d))
    (hdisj : ∀ x ∈ s(a, c), x ∉ s(halfTurn n a, halfTurn n c)) :
    ¬Cross s(b, d) s(halfTurn n b, halfTurn n d) := by
  have hωrep : IsFlipReplacement T s(halfTurn n a, halfTurn n c)
      s(halfTurn n b, halfTurn n d) :=
    hS.isFlipReplacement_map hγ'
  obtain ⟨hab, hbc, -⟩ := symNe_of_sbtw hb
  obtain ⟨hcd, hda, -⟩ := symNe_of_sbtw hd
  have hrim : ∀ ρ ∈ segments T, (a ∈ ρ ∨ c ∈ ρ) → ¬Cross ρ s(halfTurn n b, halfTurn n d) := by
    intro ρ hρ hac hcr
    refine hωrep.2.2.2.2.noncrossing ρ (Finset.mem_insert_of_mem (Finset.mem_erase.2
      ⟨?_, mem_of_cross_of_mem_segments hρ hcr⟩)) _ (Finset.mem_insert_self _ _) hcr
    rintro rfl
    rcases hac with h | h
    exacts [hdisj a (Sym2.mem_mk_left a c) h, hdisj c (Sym2.mem_mk_right a c) h]
  intro hcr
  rcases quad_cross_right hb hd hcr with h | ⟨ρ, hρ, h⟩
  · exact hωrep.2.2.2.1 (h ▸ hγT)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · exact hrim _ (tri1.2 a (by simp) b (by simp) hab) (Or.inl (Sym2.mem_mk_left _ _)) h
  · exact hrim _ (tri1.2 b (by simp) c (by simp) hbc) (Or.inr (Sym2.mem_mk_right _ _)) h
  · exact hrim _ (tri2.2 c (by simp) d (by simp) hcd) (Or.inr (Sym2.mem_mk_left _ _)) h
  · exact hrim _ (tri2.2 d (by simp) a (by simp) hda) (Or.inl (Sym2.mem_mk_right _ _)) h

/-- If `γ' = {b, d}` replaces `γ = {a, c}` in a flip of a centrally symmetric triangulation `T`
and `γ` is disjoint from `ω(γ)`, then in the flipped triangulation the replacement for the flip at
`ω(γ)` is `ω(γ')`: it is the other diagonal `{b', d'}` of the quadrilateral over `ω(γ)`. -/
private theorem halfTurn_eq_of_isTriangle_flipTriangulation
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} (hS : IsCentrallySymmetric n T)
    {a b c d b' d' : ZMod (2 * n + 2)} (hγT : s(a, c) ∈ T) (hb : sbtw a b c) (hd : sbtw c d a)
    (tri1 : IsTriangle T {a, b, c}) (tri2 : IsTriangle T {a, c, d})
    (hγ' : IsFlipReplacement T s(a, c) s(b, d))
    (hdisj : ∀ x ∈ s(a, c), x ∉ s(halfTurn n a, halfTurn n c))
    (hb' : sbtw (halfTurn n a) b' (halfTurn n c)) (hd' : sbtw (halfTurn n c) d' (halfTurn n a))
    (tri1' : IsTriangle (flipTriangulation T s(a, c) s(b, d)) {halfTurn n a, b', halfTurn n c})
    (tri2' : IsTriangle (flipTriangulation T s(a, c) s(b, d)) {halfTurn n a, halfTurn n c, d'}) :
    s(halfTurn n b, halfTurn n d) = s(b', d') := by
  have hωrep : IsFlipReplacement T s(halfTurn n a, halfTurn n c)
      s(halfTurn n b, halfTurn n d) :=
    hS.isFlipReplacement_map hγ'
  have hL := not_cross_halfTurn_of_isFlipReplacement hS hγT hb hd tri1 tri2 hγ' hdisj
  have hrim : ∀ ρ ∈ segments (flipTriangulation T s(a, c) s(b, d)),
      ρ ≠ s(halfTurn n a, halfTurn n c) → ¬Cross ρ s(halfTurn n b, halfTurn n d) := by
    intro ρ hρ hρne hcr
    have := mem_of_cross_of_mem_segments hρ hcr
    simp only [flipTriangulation, Finset.mem_insert, Finset.mem_erase] at this
    rcases this with rfl | ⟨-, hρT⟩
    · exact hL hcr
    · exact hωrep.2.2.2.2.noncrossing ρ (Finset.mem_insert_of_mem (Finset.mem_erase.2
        ⟨hρne, hρT⟩)) _ (Finset.mem_insert_self _ _) hcr
  have hcrω : Cross s(halfTurn n a, halfTurn n c) s(halfTurn n b, halfTurn n d) :=
    (cross_map_add_iff _ s(a, c) s(b, d)).2 ⟨a, c, b, d, rfl, rfl, hb, hd⟩
  obtain ⟨h1, h2, -⟩ := symNe_of_sbtw hb'
  obtain ⟨h4, h5, -⟩ := symNe_of_sbtw hd'
  rcases quad_cross_left hb' hd' hcrω with h | ⟨ρ, hρ, h⟩
  · exact h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · exact absurd h (hrim _ (tri1'.2 _ (by simp) _ (by simp) h1) (symMk_ne (Ne.symm h1) h2))
  · exact absurd h (hrim _ (tri1'.2 _ (by simp) _ (by simp) h2) (symMk_ne' (Ne.symm h1) h2))
  · exact absurd h (hrim _ (tri2'.2 _ (by simp) _ (by simp) h4) (symMk_ne h5 (Ne.symm h4)))
  · exact absurd h (hrim _ (tri2'.2 _ (by simp) _ (by simp) h5) (symMk_ne' h5 (Ne.symm h4)))

/-- Flipping `γ ∈ T` to `γ' ∉ T` and then `ω(γ)` to `ω(γ')` keeps a set of segments centrally
symmetric. -/
private theorem IsCentrallySymmetric.flipTriangulation_flipTriangulation
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} (hS : IsCentrallySymmetric n T)
    {γ γ' : Sym2 (ZMod (2 * n + 2))} (hγ : γ ∈ T) (hγ' : γ' ∉ T) :
    IsCentrallySymmetric n (flipTriangulation (flipTriangulation T γ γ') (γ.map (halfTurn n))
      (γ'.map (halfTurn n))) := by
  have g1 : γ' ≠ γ.map (halfTurn n) := fun h => hγ' (h ▸ hS.map_mem_iff.2 hγ)
  have g2 : γ'.map (halfTurn n) ≠ γ := fun h => hγ' (hS.map_mem_iff.1 (h ▸ hγ))
  ext x
  rw [mem_image_map_halfTurn]
  simp only [flipTriangulation, Finset.mem_insert, Finset.mem_erase, ne_eq,
    map_halfTurn_eq_iff, map_halfTurn_map_halfTurn, hS.map_mem_iff]
  constructor <;> rintro (rfl | ⟨h1, rfl | ⟨h2, h3⟩⟩)
  exacts [Or.inr ⟨g1, Or.inl rfl⟩, Or.inl rfl, Or.inr ⟨h2, Or.inr ⟨h1, h3⟩⟩,
    Or.inr ⟨g2, Or.inl rfl⟩, Or.inl rfl, Or.inr ⟨h2, Or.inr ⟨h1, h3⟩⟩]

/-- Replacing `λ(k)` by `{b, d}` and `λ(ι_C(k))` by `ω({b, d})` keeps `λ(ι_C(p)) = ω(λ(p))`. -/
private theorem IsSymmetricLabelledTriangulation.apply_iotaC_update_update
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} {ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))}
    (h : IsSymmetricLabelledTriangulation n T ℓ) {k : Fin (2 * n - 1)} (hk : iotaC n k ≠ k)
    (b d : ZMod (2 * n + 2)) (q : Fin (2 * n - 1)) :
    Function.update (Function.update ℓ k s(b, d)) (iotaC n k) s(halfTurn n b, halfTurn n d)
        (iotaC n q) =
      (Function.update (Function.update ℓ k s(b, d)) (iotaC n k) s(halfTurn n b, halfTurn n d)
        q).map (halfTurn n) := by
  by_cases hq1 : q = k
  · rw [hq1, Function.update_self, Function.update_of_ne (Ne.symm hk), Function.update_self,
      Sym2.map_mk]
  by_cases hq2 : q = iotaC n k
  · rw [hq2, iotaC_iotaC, Function.update_self, Function.update_of_ne (Ne.symm hk),
      Function.update_self, Sym2.map_mk, halfTurn_halfTurn, halfTurn_halfTurn]
  have h3 : iotaC n q ≠ k := fun h' => hq2 (by rw [← h', iotaC_iotaC])
  have h4 : iotaC n q ≠ iotaC n k := fun h' => hq1 ((iotaC n).injective h')
  rw [Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne hq2,
    Function.update_of_ne hq1, h.apply_iotaC]

/-- **Flipping a two-element orbit** `{k, ι_C(k)}`: flip `λ(k)`, then `λ(ι_C(k))`. -/
private theorem IsSymmetricLabelledTriangulation.exists_flip_of_ne
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} {ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))}
    (h : IsSymmetricLabelledTriangulation n T ℓ) {k : Fin (2 * n - 1)} (hk : iotaC n k ≠ k) :
    ∃ (T' : Finset (Sym2 (ZMod (2 * n + 2)))) (ℓ' : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))),
      IsSymmetricLabelledTriangulation n T' ℓ' ∧
        triangulationMatrix T' ℓ' = matrixMutation le_rfl
          (matrixMutation le_rfl (triangulationMatrix T ℓ) k) (iotaC n k) := by
  have hℓ := h.isTriangulationLabelling
  have hS := h.isCentrallySymmetric
  obtain ⟨-, hne, hdisj⟩ := h.apply_iotaC_ne fun h' => hk (iotaC_eq_self_iff.2 h')
  obtain ⟨a, c, hac⟩ := symExists_eq_mk (ℓ k)
  have hγT : s(a, c) ∈ T := hac ▸ IsTriangulationLabelling.mem hℓ k
  obtain ⟨b, d, hb, hd, tri1, tri2, -, hγ', -⟩ := exists_flip h.isTriangulation hγT
  have hωγ : ℓ (iotaC n k) = s(halfTurn n a, halfTurn n c) := by
    rw [h.apply_iotaC, hac, Sym2.map_mk]
  have hγ'k : IsFlipReplacement T (ℓ k) s(b, d) := hac ▸ hγ'
  have hωγT1 : s(halfTurn n a, halfTurn n c) ∈ flipTriangulation T s(a, c) s(b, d) := by
    simp only [flipTriangulation, Finset.mem_insert, Finset.mem_erase]
    exact Or.inr ⟨by rw [← hωγ, ← hac]; exact hne, (hS.isFlipReplacement_map hγ').2.1⟩
  obtain ⟨b', d', hb', hd', tri1', tri2', -, hδ, -⟩ := exists_flip hγ'.2.2.2.2 hωγT1
  have hupd : Function.update ℓ k s(b, d) (iotaC n k) = s(halfTurn n a, halfTurn n c) := by
    rw [Function.update_of_ne hk, hωγ]
  have hrep2 : IsFlipReplacement (flipTriangulation T (ℓ k) s(b, d))
      (Function.update ℓ k s(b, d) (iotaC n k)) s(halfTurn n b, halfTurn n d) := by
    rw [hupd, hac, halfTurn_eq_of_isTriangle_flipTriangulation hS hγT hb hd tri1 tri2 hγ'
      (by rw [← hac, ← hωγ]; exact hdisj) hb' hd' tri1' tri2']
    exact hδ
  have hℓ1 := isTriangulationLabelling_update_flip hℓ hγ'k
  refine ⟨_, _, ⟨hrep2.2.2.2.2, ?_, isTriangulationLabelling_update_flip hℓ1 hrep2,
    h.apply_iotaC_update_update hk b d⟩, ?_⟩
  · rw [hupd, hac, show s(halfTurn n a, halfTurn n c) = s(a, c).map (halfTurn n) from rfl,
      show s(halfTurn n b, halfTurn n d) = s(b, d).map (halfTurn n) from rfl]
    exact hS.flipTriangulation_flipTriangulation hγT hγ'.2.2.2.1
  · rw [triangulationMatrix_update_flip hℓ1 hrep2, triangulationMatrix_update_flip hℓ hγ'k]

/-! #### Admissibility -/

/-- The elements of `zpowers σ`, for an involution `σ`, act as `1` or as `σ`. -/
private theorem symZpowers_smul {α : Type*} {σ : Equiv.Perm α} (hσ : σ * σ = 1)
    (g : Subgroup.zpowers σ) : (∀ x : α, g • x = x) ∨ ∀ x : α, g • x = σ x := by
  obtain ⟨g, hg⟩ := g
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have h2 : σ ^ (2 : ℤ) = 1 := by rw [zpow_two, hσ]
  rcases Int.even_or_odd' k with ⟨r, rfl | rfl⟩
  · refine Or.inl fun x => ?_
    rw [Subgroup.mk_smul, _root_.zpow_mul, h2, _root_.one_zpow, one_smul]
  · refine Or.inr fun x => ?_
    rw [Subgroup.mk_smul, _root_.zpow_add_one, _root_.zpow_mul, h2, _root_.one_zpow, one_mul,
      Equiv.Perm.smul_def]

/-- The orbits of the group generated by an involution `σ` are the sets `{a, σ a}`. -/
private theorem symMem_orbit_zpowers_iff {α : Type*} {σ : Equiv.Perm α} (hσ : σ * σ = 1)
    {a b : α} : b ∈ orbit (Subgroup.zpowers σ) a ↔ b = a ∨ b = σ a := by
  constructor
  · rintro ⟨g, rfl⟩
    exact (symZpowers_smul hσ g).imp (· a) (· a)
  · rintro (rfl | rfl)
    exacts [mem_orbit_self _, ⟨⟨σ, Subgroup.mem_zpowers σ⟩, rfl⟩]

/-- **Condition (2)**: `b_{ι(p) ι(q)} = b_{pq}`. -/
private theorem IsSymmetricLabelledTriangulation.triangulationMatrix_iotaC
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} {ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))}
    (h : IsSymmetricLabelledTriangulation n T ℓ) (p q : Fin (2 * n - 1)) :
    triangulationMatrix T ℓ (iotaC n p) (iotaC n q) = triangulationMatrix T ℓ p q := by
  have e : ∀ σ σ' : Sym2 (ZMod (2 * n + 2)),
      polygonArrows T (σ.map (halfTurn n)) (σ'.map (halfTurn n)) = polygonArrows T σ σ' := by
    intro σ σ'
    have := polygonArrows_image_map_add ((n + 1 : ℕ) : ZMod (2 * n + 2)) T σ σ'
    change polygonArrows (T.image (Sym2.map (halfTurn n))) (σ.map (halfTurn n))
      (σ'.map (halfTurn n)) = _ at this
    rwa [h.isCentrallySymmetric] at this
  simp only [triangulationMatrix, Matrix.of_apply, signedCount, h.apply_iotaC, e]

/-- Two disjoint segments are not both segments of one triangle. -/
private theorem symNot_disjoint_of_mem_sym2 {m : ℕ} [NeZero m] {T : Finset (Sym2 (ZMod m))}
    {Δ : Finset (ZMod m)} (hΔ : IsTriangle T Δ) {e f : Sym2 (ZMod m)} (he : e ∈ Δ.sym2)
    (hf : f ∈ Δ.sym2) (hed : ¬e.IsDiag) (hfd : ¬f.IsDiag) (hdisj : ∀ x ∈ e, x ∉ f) : False := by
  obtain ⟨x, y, rfl⟩ := symExists_eq_mk e
  obtain ⟨u, v, rfl⟩ := symExists_eq_mk f
  rw [Finset.mk_mem_sym2_iff] at he hf
  rw [Sym2.mk_isDiag_iff] at hed hfd
  have hxu : x ≠ u := fun h' => hdisj x (Sym2.mem_mk_left _ _) (h' ▸ Sym2.mem_mk_left _ _)
  have hxv : x ≠ v := fun h' => hdisj x (Sym2.mem_mk_left _ _) (h' ▸ Sym2.mem_mk_right _ _)
  have hyu : y ≠ u := fun h' => hdisj y (Sym2.mem_mk_right _ _) (h' ▸ Sym2.mem_mk_left _ _)
  have hyv : y ≠ v := fun h' => hdisj y (Sym2.mem_mk_right _ _) (h' ▸ Sym2.mem_mk_right _ _)
  have hsub : ({x, y, u, v} : Finset (ZMod m)) ⊆ Δ := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨he.1, he.2, hf.1, hf.2⟩
  have hcard : ({x, y, u, v} : Finset (ZMod m)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hed, hxu, hxv]),
      Finset.card_insert_of_notMem (by simp [hyu, hyv]), Finset.card_pair hfd]
  have := Finset.card_le_card hsub
  rw [hcard, hΔ.1] at this
  omega

/-- The arithmetic behind condition (4): if `a, b, c, d` are in cyclic order with
`c ≠ ω(a)`, there is no pair `x ≠ y` in `{a, b, c, d}` with `ω(x) ≠ y` and `ω(x), ω(y)` in
`{a, b, c, d}`. Read on representatives. -/
private theorem symQuad_halfTurn_absurd_nat (A B C D X Y X' Y' : ℕ) (hA : A < 2 * n + 2)
    (hB : B < 2 * n + 2) (hC : C < 2 * n + 2) (hD : D < 2 * n + 2) (hX : X < 2 * n + 2)
    (hY : Y < 2 * n + 2) (hX'' : X' < 2 * n + 2) (hY'' : Y' < 2 * n + 2)
    (hX' : X' = X + (n + 1) ∨ X = X' + (n + 1)) (hY' : Y' = Y + (n + 1) ∨ Y = Y' + (n + 1))
    (hb : (A < B ∧ B < C) ∨ (B < C ∧ C < A) ∨ (C < A ∧ A < B))
    (hd : (C < D ∧ D < A) ∨ (D < A ∧ A < C) ∨ (A < C ∧ C < D))
    (hac : ¬(C = A + (n + 1) ∨ A = C + (n + 1))) (hxy : X ≠ Y) (hωxy : X' ≠ Y)
    (hx : X = A ∨ X = B ∨ X = C ∨ X = D) (hy : Y = A ∨ Y = B ∨ Y = C ∨ Y = D)
    (hx' : X' = A ∨ X' = B ∨ X' = C ∨ X' = D) (hy' : Y' = A ∨ Y' = B ∨ Y' = C ∨ Y' = D) :
    False := by
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;> omega

/-- The arithmetic behind condition (4), on `ZMod (2n + 2)`. -/
private theorem symQuad_halfTurn_absurd {a b c d x y : ZMod (2 * n + 2)} (hb : sbtw a b c)
    (hd : sbtw c d a) (hac : c ≠ halfTurn n a) (hxy : x ≠ y) (hωxy : halfTurn n x ≠ y)
    (hx : x = a ∨ x = b ∨ x = c ∨ x = d) (hy : y = a ∨ y = b ∨ y = c ∨ y = d)
    (hx' : halfTurn n x = a ∨ halfTurn n x = b ∨ halfTurn n x = c ∨ halfTurn n x = d)
    (hy' : halfTurn n y = a ∨ halfTurn n y = b ∨ halfTurn n y = c ∨ halfTurn n y = d) :
    False := by
  rw [sbtw_iff_val] at hb hd
  rw [Ne, eq_halfTurn_iff_val] at hac
  rw [Ne, eq_iff_val] at hxy hωxy
  simp only [eq_iff_val] at hx hy hx' hy'
  exact symQuad_halfTurn_absurd_nat _ _ _ _ _ _ _ _ (ZMod.val_lt a) (ZMod.val_lt b)
    (ZMod.val_lt c) (ZMod.val_lt d) (ZMod.val_lt x) (ZMod.val_lt y) (ZMod.val_lt _)
    (ZMod.val_lt _) (eq_halfTurn_iff_val.1 rfl) (eq_halfTurn_iff_val.1 rfl) hb hd hac hxy hωxy
    hx hy hx' hy'

/-- **The geometric step of condition (4)**: for `ι(i) ≠ i` and `ι(j) ≠ j`, no two triangles
of `T` carry `λ(i), λ(j)` and `λ(i), λ(ι(j))` respectively. -/
private theorem IsSymmetricLabelledTriangulation.false_of_mem_sym2_iotaC
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} {ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))}
    (h : IsSymmetricLabelledTriangulation n T ℓ) {i j : Fin (2 * n - 1)} (hfi : iotaC n i ≠ i)
    (hfj : iotaC n j ≠ j) {Δ Δ' : Finset (ZMod (2 * n + 2))} (hΔ : IsTriangle T Δ)
    (hΔ' : IsTriangle T Δ') (hiΔ : ℓ i ∈ Δ.sym2) (hjΔ : ℓ j ∈ Δ.sym2) (hiΔ' : ℓ i ∈ Δ'.sym2)
    (hjΔ' : ℓ (iotaC n j) ∈ Δ'.sym2) : False := by
  have hℓ := h.isTriangulationLabelling
  have hT := h.isTriangulation
  obtain ⟨a, c, hac⟩ := symExists_eq_mk (ℓ i)
  have hγT : s(a, c) ∈ T := hac ▸ IsTriangulationLabelling.mem hℓ i
  obtain ⟨b, d, hb, hd, -, -, huniq, -, -⟩ := exists_flip hT hγT
  rw [hac, Finset.mk_mem_sym2_iff] at hiΔ hiΔ'
  have hS : ∀ Δ'' : Finset (ZMod (2 * n + 2)), IsTriangle T Δ'' → a ∈ Δ'' → c ∈ Δ'' →
      ∀ z ∈ Δ'', z = a ∨ z = b ∨ z = c ∨ z = d := by
    intro Δ'' hΔ'' ha hc z hz
    rcases huniq Δ'' hΔ'' ha hc with rfl | rfl <;> simp only [Finset.mem_insert,
      Finset.mem_singleton] at hz <;> tauto
  obtain ⟨x, y, hxy⟩ := symExists_eq_mk (ℓ j)
  have hωxy : ℓ (iotaC n j) = s(halfTurn n x, halfTurn n y) := by
    rw [h.apply_iotaC, hxy, Sym2.map_mk]
  rw [hxy, Finset.mk_mem_sym2_iff] at hjΔ
  rw [hωxy, Finset.mk_mem_sym2_iff] at hjΔ'
  have hxy_ne : x ≠ y := fun h' =>
    (hT.isDiagonal _ (hℓ.mem j)).1 (hxy ▸ Sym2.mk_isDiag_iff.2 h')
  have hωx : halfTurn n x ≠ y := fun h' =>
    hfj (hℓ.1 (by rw [hωxy, hxy, ← h', halfTurn_halfTurn, Sym2.eq_swap]))
  have hωa : c ≠ halfTurn n a := fun h' =>
    hfi (hℓ.1 (by rw [h.apply_iotaC, hac, Sym2.map_mk, h', halfTurn_halfTurn, Sym2.eq_swap]))
  exact symQuad_halfTurn_absurd hb hd hωa hxy_ne hωx (hS Δ hΔ hiΔ.1 hiΔ.2 x hjΔ.1)
    (hS Δ hΔ hiΔ.1 hiΔ.2 y hjΔ.2) (hS Δ' hΔ' hiΔ'.1 hiΔ'.2 _ hjΔ'.1)
    (hS Δ' hΔ' hiΔ'.1 hiΔ'.2 _ hjΔ'.2)

/-- The increasing sequence of a two-element set `{a, b}` with `a < b` is `[a, b]`. -/
private theorem symIncreasingSeq_pair_of_lt {N : ℕ} {a b : Fin N} (h : a < b) :
    increasingSeq ({a, b} : Finset (Fin N)) = [a, b] := by
  rw [increasingSeq, Finset.sort_insert _ (by simpa using h.le) (by simpa using h.ne),
    Finset.sort_singleton]

/-- **Flipping the fixed orbit**: a flip of the diameter `λ(p)`, `ι_C(p) = p`. -/
private theorem IsSymmetricLabelledTriangulation.exists_flip_of_fixed
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} {ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))}
    (h : IsSymmetricLabelledTriangulation n T ℓ) {p : Fin (2 * n - 1)} (hp : iotaC n p = p) :
    ∃ (T' : Finset (Sym2 (ZMod (2 * n + 2)))) (ℓ' : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))),
      IsSymmetricLabelledTriangulation n T' ℓ' ∧
        triangulationMatrix T' ℓ' = matrixMutation le_rfl (triangulationMatrix T ℓ) p := by
  have hℓ := h.isTriangulationLabelling
  obtain ⟨γ', hγ', huniq⟩ :=
    symExists_replacement h.isTriangulation (IsTriangulationLabelling.mem hℓ p)
  have hfixγ : (ℓ p).map (halfTurn n) = ℓ p := by rw [← h.apply_iotaC, hp]
  have hω : γ'.map (halfTurn n) = γ' := by
    have := h.isCentrallySymmetric.isFlipReplacement_map hγ'
    rw [hfixγ] at this
    exact huniq _ this
  refine ⟨_, _, ⟨hγ'.2.2.2.2, ?_, isTriangulationLabelling_update_flip hℓ hγ', ?_⟩,
    triangulationMatrix_update_flip hℓ hγ'⟩
  · rw [IsCentrallySymmetric, image_map_halfTurn_flipTriangulation, h.isCentrallySymmetric,
      hfixγ, hω]
  · intro q
    by_cases hq : q = p
    · rw [hq, hp, Function.update_self, hω]
    · have : iotaC n q ≠ p := fun h' => hq (by rw [← iotaC_iotaC q, h', hp])
      rw [Function.update_of_ne this, Function.update_of_ne hq, h.apply_iotaC]

/-- **Flipping an orbit of a symmetric labelled triangulation.** Let `(T, λ)` be a symmetric
labelled triangulation and `K = {p, ι_C(p)}` an orbit of `ι_C`. Then there is a symmetric
labelled triangulation `(T', λ')` with `B(T', λ') = μ_{s_K}(B(T, λ))`. -/
@[cluster_algebras "lem_symmetric_flip"]
theorem IsSymmetricLabelledTriangulation.exists_matrixMutationList (_hn : 2 ≤ n)
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} {ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))}
    (h : IsSymmetricLabelledTriangulation n T ℓ) (p : Fin (2 * n - 1)) :
    ∃ (T' : Finset (Sym2 (ZMod (2 * n + 2)))) (ℓ' : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))),
      IsSymmetricLabelledTriangulation n T' ℓ' ∧
        triangulationMatrix T' ℓ' =
          matrixMutationList le_rfl (triangulationMatrix T ℓ) (increasingSeq {p, iotaC n p}) := by
  by_cases hp : iotaC n p = p
  · rw [hp, Finset.pair_eq_singleton, increasingSeq, Finset.sort_singleton,
      matrixMutationList_singleton]
    exact h.exists_flip_of_fixed hp
  rcases lt_or_gt_of_ne hp with hlt | hlt
  · rw [Finset.pair_comm, symIncreasingSeq_pair_of_lt hlt]
    have := h.exists_flip_of_ne (k := iotaC n p) (by rwa [iotaC_iotaC, ne_comm])
    rwa [iotaC_iotaC] at this
  · rw [symIncreasingSeq_pair_of_lt hlt]
    exact h.exists_flip_of_ne hp

/-- **The matrix of a symmetric labelled triangulation is skew-symmetric.** -/
@[cluster_algebras "lem_symmetric_triangulation_admissible"]
theorem IsSymmetricLabelledTriangulation.triangulationMatrix_apply_eq_neg
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} {ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))}
    (_h : IsSymmetricLabelledTriangulation n T ℓ) (p q : Fin (2 * n - 1)) :
    triangulationMatrix T ℓ p q = -triangulationMatrix T ℓ q p :=
  TypeBC.triangulationMatrix_apply_eq_neg T ℓ p q

/-- The diagonal entries of `B(T, λ)` vanish. -/
private theorem triangulationMatrix_apply_self (T : Finset (Sym2 (ZMod (2 * n + 2))))
    (ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))) (i : Fin (2 * n - 1)) :
    triangulationMatrix T ℓ i i = 0 := by
  have := TypeBC.triangulationMatrix_apply_eq_neg T ℓ i i
  omega

/-- **Condition (4)**: `b_{ij} b_{ι(i) j} ≥ 0`. -/
private theorem IsSymmetricLabelledTriangulation.mul_nonneg_iotaC
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} {ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))}
    (h : IsSymmetricLabelledTriangulation n T ℓ) (i j : Fin (2 * n - 1)) :
    0 ≤ triangulationMatrix T ℓ i j * triangulationMatrix T ℓ (iotaC n i) j := by
  have hℓ := h.isTriangulationLabelling
  have hT := h.isTriangulation
  by_cases hfi : iotaC n i = i
  · rw [hfi]
    exact mul_self_nonneg _
  rw [show triangulationMatrix T ℓ (iotaC n i) j = triangulationMatrix T ℓ i (iotaC n j) by
    rw [← h.triangulationMatrix_iotaC i (iotaC n j), iotaC_iotaC]]
  by_cases hfj : iotaC n j = j
  · rw [hfj]
    exact mul_self_nonneg _
  by_cases hij : j = i
  · rw [hij, triangulationMatrix_apply_self, zero_mul]
  by_cases hij' : iotaC n j = i
  · rw [hij', triangulationMatrix_apply_self, mul_zero]
  by_cases h1 : triangulationMatrix T ℓ i j = 0
  · rw [h1, zero_mul]
  by_cases h2 : triangulationMatrix T ℓ i (iotaC n j) = 0
  · rw [h2, mul_zero]
  obtain ⟨Δ, hΔ, hiΔ, hjΔ⟩ := (triangulationMatrix_apply_ne_zero_iff hT hℓ (Ne.symm hij)).1 h1
  obtain ⟨Δ', hΔ', hiΔ', hjΔ'⟩ :=
    (triangulationMatrix_apply_ne_zero_iff hT hℓ (Ne.symm hij')).1 h2
  exact (h.false_of_mem_sym2_iotaC hfi hfj hΔ hΔ' hiΔ hjΔ hiΔ' hjΔ').elim

/-- **The matrix of a symmetric labelled triangulation is admissible**: `B(T, λ)` is
`G`-admissible for the action of `ι_C` on `Fin (2n - 1)`, all indices being mutable. -/
@[cluster_algebras "lem_symmetric_triangulation_admissible"]
theorem IsSymmetricLabelledTriangulation.isGroupAdmissible (_hn : 2 ≤ n)
    {T : Finset (Sym2 (ZMod (2 * n + 2)))} {ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))}
    (h : IsSymmetricLabelledTriangulation n T ℓ) :
    IsGroupAdmissible (Subgroup.zpowers (iotaC n)) le_rfl (triangulationMatrix T ℓ) := by
  have hℓ := h.isTriangulationLabelling
  have hT := h.isTriangulation
  have horb : ∀ i i' : Fin (2 * n - 1), i' ∈ orbit (Subgroup.zpowers (iotaC n)) i ↔
      i' = i ∨ i' = iotaC n i := fun _ _ => symMem_orbit_zpowers_iff (iotaC_mul_self n)
  refine ⟨fun g i j j' hj => ?_, fun i i' hi' => ?_, fun i i' hi' j => ?_⟩
  · simp only [Fin.castLE_refl] at hj ⊢
    rcases symZpowers_smul (iotaC_mul_self n) g with hg | hg <;> rw [hg] at hj ⊢ <;> rw [hj]
    exact h.triangulationMatrix_iotaC i j
  · simp only [Fin.castLE_refl] at hi' ⊢
    rcases (horb _ _).1 hi' with rfl | rfl
    · exact triangulationMatrix_apply_self _ _ _
    by_cases hfix : iotaC n i = i
    · rw [hfix]
      exact triangulationMatrix_apply_self _ _ _
    by_contra hne
    obtain ⟨Δ, hΔ, hi, hj⟩ := (triangulationMatrix_apply_ne_zero_iff hT hℓ (Ne.symm hfix)).1 hne
    exact symNot_disjoint_of_mem_sym2 hΔ hi hj
      (hT.isDiagonal _ (IsTriangulationLabelling.mem hℓ _)).1
      (hT.isDiagonal _ (IsTriangulationLabelling.mem hℓ _)).1
      (h.apply_iotaC_ne fun h' => hfix (iotaC_eq_self_iff.2 h')).2.2
  · rcases (horb _ _).1 hi' with rfl | rfl
    exacts [mul_self_nonneg _, h.mul_nonneg_iotaC i j]

end TypeBC

end ClusterAlgebras

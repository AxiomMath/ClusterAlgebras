/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.MutationSignedCount
public import ClusterAlgebras.Plabic.PlabicQuiver
public import ClusterAlgebras.Plabic.SquareTrips

/-!
# A square move is a mutation of the quiver

Let `G` be a plabic graph and `q = (c₁, c₂, c₃, c₄)` an internal face of `G` at which a square
move applies: `c_{k+1} = φ(c_k)` (indices modulo `4`), and the four vertices `A_k = v(c_k)` are
internal, pairwise distinct, trivalent and alternate in colour. Write `F_k = f(c̄_k)` for the face
to the left of `c_k`, and assume `F_k ≠ F_{k+1}` for every `k`. Then the quiver of the square move
`G_q` is the mutation of the quiver of `G` at the face `q`: `Q(G_q) = μ_q(Q(G))`.

The proof compares signed counts, which determine two-cycle-free arrow systems. Put `χ_k = 1` if
`A_k` is white and `χ_k = -1` if it is black. The rotation at `A_k` is the `3`-cycle
`(c̄_{k-1} c_k ℓ_k)` with `ℓ_k = σ(c_k)`, and the faces to the right and left of these darts are
`(q, F_k)`, `(F_{k-1}, q)` and `(F_k, F_{k-1})`. Hence:

* the signed count of `Q(G)` at `(q, F)` is `∑_{F_k = F} χ_k`, and it is negated in `G_q`;
* for faces `f, f' ≠ q`, the dart balance changes by `ψ_{G_q}(f, f') = ψ_G(f, f') - 2 ∑ χ_k`,
  the sum over the `k` with `(F_k, F_{k-1}) = (f, f')`.

Since consecutive `F_k` differ, the `k` with `F_k = F` all have the same `χ_k`, so the arrows
between `q` and `F` all point the same way; the products `a(i, q) a(q, j)` are then counted by the
consecutive pairs `(k - 1, k)`, and the signed counts of `Q(G_q)` and `μ_q(Q(G))` agree.

## Main definitions

* `ClusterAlgebras.PlabicData.dartWeight`: the weight `±1` of a dart at an internal vertex in the
  dart balance, `0` at a boundary vertex.

## Main results

* `ClusterAlgebras.PlabicData.dartBalance_eq_sum`: the dart balance as a sum of dart weights.
* `ClusterAlgebras.PlabicData.dartBalance_squareMove`: the change of the dart balance under a
  square move.
* `ClusterAlgebras.PlabicData.IsSquareMoveFace.quiverCount_sub_eq_sum`,
  `ClusterAlgebras.PlabicData.IsSquareMoveFace.quiverCount_squareMove_sub_eq_sum`: the signed
  counts of `Q(G)` and of `Q(G_q)` at `(q, F)`.
* `ClusterAlgebras.PlabicData.IsSquareMoveFace.quiverCount_squareMove_sub`: the signed count of
  `Q(G_q)` away from `q`.
* `ClusterAlgebras.PlabicData.IsSquareMoveFace.quiver_squareMove`: a square move is a mutation of
  the quiver.

## Implementation notes

* As in `ClusterAlgebras.Plabic.SquareMove`, the face `q` is given by its first dart `c = c₁`
  and `c_{k+1}` is `squareCorner c k` for the `0`-indexed `k : Fin 4`, so that indices are read
  modulo `4` by the arithmetic of `Fin 4`. The vertex `q` of `Q(G)` is any face `q : G.faces` whose
  underlying set of darts is the orbit `faceOf c`.
* The faces of `G` and of its square move are the same `Finset`, definitionally, so `Q(G_q)` and
  `μ_q(Q(G))` are quivers on the same vertex type and the statement is an equality of quivers.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Alternating sums around a square -/

/-- For a cyclic sequence `F₀, F₁, F₂, F₃` with consecutive terms distinct, the alternating count
`[F₀ = f] - [F₁ = f] + [F₂ = f] - [F₃ = f]` has the sign of its nonzero terms: its positive part is
`[F₀ = f] + [F₂ = f]` and its negative part `[F₁ = f] + [F₃ = f]`. -/
private theorem max_alternating {α : Type*} [DecidableEq α] {F : Fin 4 → α}
    (hF : ∀ k, F k ≠ F (k + 1)) (f : α) :
    max ((if F 0 = f then 1 else 0) - (if F 1 = f then 1 else 0) + (if F 2 = f then 1 else 0) -
      (if F 3 = f then 1 else 0) : ℤ) 0 =
        (if F 0 = f then 1 else 0) + (if F 2 = f then 1 else 0) ∧
    max (-((if F 0 = f then 1 else 0) - (if F 1 = f then 1 else 0) + (if F 2 = f then 1 else 0) -
      (if F 3 = f then 1 else 0)) : ℤ) 0 =
        (if F 1 = f then 1 else 0) + (if F 3 = f then 1 else 0) := by
  have h0 : F 0 ≠ F 1 := hF 0
  have h1 : F 1 ≠ F 2 := hF 1
  have h2 : F 2 ≠ F 3 := hF 2
  have h3 : F 3 ≠ F 0 := hF 3
  split_ifs <;> simp_all

/-- The products of arrows through a square. Let `F₀, …, F₃` be a cyclic sequence with consecutive
terms distinct and `χ` alternate between `1` and `-1`, and put `S(f) = ∑_{F_k = f} χ_k`. Then
`S(f)⁻ S(f')⁺ - S(f')⁻ S(f)⁺` is minus the antisymmetrised count of the `k` with
`(F_k, F_{k-1}) = (f, f')`, weighted by `χ_k`. -/
private theorem alternating_identity {α : Type*} [DecidableEq α] {F : Fin 4 → α}
    (hF : ∀ k, F k ≠ F (k + 1)) {χ : Fin 4 → ℤ} (hχ : ∀ k, χ (k + 1) = -χ k)
    (hχ0 : χ 0 = 1 ∨ χ 0 = -1) (i j : α) :
    max (-∑ k, if F k = i then χ k else 0) 0 * max (∑ k, if F k = j then χ k else 0) 0 -
      max (-∑ k, if F k = j then χ k else 0) 0 * max (∑ k, if F k = i then χ k else 0) 0 =
      -((∑ k, if F k = i ∧ F (k - 1) = j then χ k else 0) -
        ∑ k, if F k = j ∧ F (k - 1) = i then χ k else 0) := by
  have e1 : χ 1 = -χ 0 := hχ 0
  have e2 : χ 2 = χ 0 := by rw [show (2 : Fin 4) = 1 + 1 from rfl, hχ, e1, neg_neg]
  have e3 : χ 3 = -χ 0 := by rw [show (3 : Fin 4) = 2 + 1 from rfl, hχ, e2]
  obtain ⟨mi, mi'⟩ := max_alternating hF i
  obtain ⟨mj, mj'⟩ := max_alternating hF j
  obtain ⟨I, hI⟩ : ∃ I : Fin 4 → α → ℤ, ∀ k f, (if F k = f then 1 else 0) = I k f :=
    ⟨_, fun _ _ => rfl⟩
  have h1 : ∀ k f (x : ℤ), (if F k = f then x else 0) = I k f * x :=
    fun k f x => by rw [← hI]; split_ifs <;> simp
  have h2 : ∀ k l f f' (x : ℤ), (if F k = f ∧ F l = f' then x else 0) = I k f * I l f' * x :=
    fun k l f f' x => by rw [← hI, ← hI]; split_ifs <;> simp_all
  simp only [hI] at mi mi' mj mj'
  simp only [Fin.sum_univ_four, h1, h2]
  rw [show (0 : Fin 4) - 1 = 3 from rfl,
    show (1 : Fin 4) - 1 = 0 from rfl, show (2 : Fin 4) - 1 = 1 from rfl,
    show (3 : Fin 4) - 1 = 2 from rfl, e1, e2, e3]
  rcases hχ0 with h | h <;> rw [h]
  · have ei : ∀ f : α, I 0 f * 1 + I 1 f * -1 + I 2 f * 1 + I 3 f * -1 =
        I 0 f - I 1 f + I 2 f - I 3 f := fun f => by ring
    have ei' : ∀ f : α, -(I 0 f * 1 + I 1 f * -1 + I 2 f * 1 + I 3 f * -1) =
        -(I 0 f - I 1 f + I 2 f - I 3 f) := fun f => by ring
    rw [ei', ei', ei, ei, mi, mi', mj, mj']
    ring
  · have ei : ∀ f : α, I 0 f * -1 + I 1 f * - -1 + I 2 f * -1 + I 3 f * - -1 =
        -(I 0 f - I 1 f + I 2 f - I 3 f) := fun f => by ring
    have ei' : ∀ f : α, -(I 0 f * -1 + I 1 f * - -1 + I 2 f * -1 + I 3 f * - -1) =
        I 0 f - I 1 f + I 2 f - I 3 f := fun f => by ring
    rw [ei', ei', ei, ei, mi, mi', mj, mj']
    ring

/-- The last step of the comparison of signed counts, as an identity between integers: if the
signed count after mutation is `β + a(i, q) a(q, j) - a(j, q) a(q, i)`, the arrows at `q` are the
given positive and negative parts, and the signed count after the square move is `β - T` with
`a(i, q) a(q, j) - a(j, q) a(q, i) = -T`, then the two signed counts agree. -/
private theorem square_step {L SCm SC D T aqi aiq aqj ajq Mi Mi' Mj Mj' : ℤ}
    (hm : SCm = SC + aiq * aqj - ajq * aqi) (hs : SC = D) (h1 : aqi = Mi) (h2 : aiq = Mi')
    (h3 : aqj = Mj) (h4 : ajq = Mj') (hT : L = D - T) (key : Mi' * Mj - Mj' * Mi = -T) :
    L = SCm := by
  subst h1 h2 h3 h4
  linarith

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-! ### Dart weights -/

/-- The **weight** of a dart `x` in the dart balance: `1` if `v(x)` is an internal white vertex,
`-1` if it is an internal black vertex, and `0` if it is a boundary vertex. -/
def dartWeight (x : H) : ℤ :=
  if G.IsBoundaryVertex (G.vertexOf x) then 0 else if G.colour x = .white then 1 else -1

/-- The dart balance `ψ_G(f, f')` is the total weight of the darts with `f` to their right and `f'`
to their left. -/
theorem dartBalance_eq_sum (f f' : G.faces) :
    G.dartBalance f f' =
      ∑ x, if G.rightFace x = f ∧ G.leftFace x = f' then G.dartWeight x else 0 := by
  rw [dartBalance, natCast_card_filter, natCast_card_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  by_cases hv : G.IsBoundaryVertex (G.vertexOf x)
  · simp [dartWeight, IsInternalOfColour, hv]
  · have hx : x ∉ G.bdry := fun h => hv (G.isBoundaryVertex_vertexOf_of_mem h)
    by_cases hf : G.rightFace x = f ∧ G.leftFace x = f'
    · rcases (show G.colour x = .white ∨ G.colour x = .black by cases G.colour x <;> simp)
        with hc | hc <;> simp [dartWeight, IsInternalOfColour, hv, hx, hc, hf]
    · simp [hf]

/-- In a plabic graph, the weight of a dart depends only on its vertex. -/
theorem IsPlabicGraph.dartWeight_rot {G : PlabicData H b} (hG : G.IsPlabicGraph) (x : H) :
    G.dartWeight (G.rot x) = G.dartWeight x := by
  by_cases h : G.IsBoundaryVertex (G.vertexOf x)
  · simp [dartWeight, G.vertexOf_rot, h]
  · simp [dartWeight, G.vertexOf_rot, h, hG.colour_rot x h]

/-- A square move negates the weights of the darts at the four vertices of the face. -/
theorem dartWeight_squareMove (c x : H) : (G.squareMove c).dartWeight x =
    if G.vertexOf x ∈ G.squareVertices c then -G.dartWeight x else G.dartWeight x := by
  by_cases hv : G.IsBoundaryVertex (G.vertexOf x)
  · simp [dartWeight, hv]
  · by_cases hs : G.vertexOf x ∈ G.squareVertices c
    · cases hc : G.colour x <;> simp [dartWeight, hv, hs, hc, colour_squareMove]
    · simp [dartWeight, hv, hs, colour_squareMove]

/-- **The change of the dart balance under a square move**: the darts at the four vertices of the
face change sign. -/
theorem dartBalance_squareMove (c : H) (f f' : G.faces) :
    (G.squareMove c).dartBalance f f' = G.dartBalance f f' -
      2 * ∑ x, if G.vertexOf x ∈ G.squareVertices c ∧ G.rightFace x = f ∧ G.leftFace x = f' then
        G.dartWeight x else 0 := by
  rw [dartBalance_eq_sum, dartBalance_eq_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [dartWeight_squareMove]
  simp only [toDiskMap_squareMove]
  by_cases h1 : G.vertexOf x ∈ G.squareVertices c
  · by_cases h2 : G.rightFace x = f ∧ G.leftFace x = f'
    · simp only [h1, h2, and_self, if_true]
      ring
    · simp [h1, h2]
  · simp [h1]

/-! ### Darts around a square face -/

/-- The orbit of `φ` through `d` is the orbit through `c` exactly when `d` lies in it. -/
theorem faceOf_eq_faceOf_iff_mem {c d : H} : G.faceOf d = G.faceOf c ↔ d ∈ G.faceOf c := by
  rw [RotationSystem.faceOf_eq_faceOf_iff, RotationSystem.mem_faceOf,
    Equiv.Perm.sameCycle_comm]

/-- The corners `c_k` lie on the face through `c`. -/
theorem faceOf_squareCorner (c : H) (k : Fin 4) : G.faceOf (G.squareCorner c k) = G.faceOf c :=
  G.faceOf_eq_of_mem (G.mem_faceOf.2
    (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)))

/-- In a plabic graph, the face to the right of `σ(x)` is the face to the left of `x`: both are the
orbit of `φ` through `x̄`, as `φ(x̄) = σ(x)`. -/
theorem IsPlabicGraph.rightFace_rot {G : PlabicData H b} (hG : G.IsPlabicGraph) (x : H) :
    G.rightFace (G.rot x) = G.leftFace x := by
  change G.faceOf _ = G.faceOf _
  rw [← G.faceOf_facePerm (G.inv x), G.facePerm_apply, hG.inv_involutive]

/-- The darts at the four vertices `v(c_k)` are the darts of these vertices. -/
theorem filter_mem_squareVertices (c : H) :
    ({x | G.vertexOf x ∈ G.squareVertices c} : Finset H) =
      univ.biUnion fun k => G.vertexOf (G.squareCorner c k) := by
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_squareVertices]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk ▸ G.self_mem_vertexOf x⟩,
    fun ⟨k, hk⟩ => ⟨k, (G.vertexOf_eq_of_mem hk).symm⟩⟩

/-- The signed count of `Q(G)` is that of the counting function. -/
theorem signedCount_quiver (i j : G.faces) :
    signedCount G.quiver.arrows i j = (G.quiverCount i j : ℤ) - G.quiverCount j i := by
  rw [arrows_quiver, signedCount_cancellation, signedCount]

namespace IsSquareMoveFace

variable {G} {c : H} (hq : G.IsSquareMoveFace c)

include hq

/-- The corners `c₁, …, c₄` are distinct darts. -/
theorem squareCorner_injective : Function.Injective (G.squareCorner c) :=
  fun _ _ h => hq.injective (congrArg G.vertexOf h)

/-- The face `q` through `c` consists of the four corners `c_k`. -/
theorem faceOf_eq_image : G.faceOf c = univ.image (G.squareCorner c) := by
  ext e
  simp only [RotationSystem.mem_faceOf, mem_image, mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    refine ⟨⟨n % 4, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    simp only [squareCorner]
    conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, Equiv.Perm.mul_apply,
      Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hq.facePerm_pow_four]
  · rintro ⟨k, rfl⟩
    exact Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)

/-- A sum over the darts of the face `q` is a sum over its four corners. -/
theorem sum_faceOf {M : Type*} [AddCommMonoid M] (g : H → M) :
    ∑ x ∈ G.faceOf c, g x = ∑ k, g (G.squareCorner c k) := by
  rw [hq.faceOf_eq_image, sum_image fun _ _ _ _ h => hq.squareCorner_injective h]

/-- A sum over the darts at the four vertices `v(c_k) = {c_k, σ(c_k), σ²(c_k)}` of `q`. -/
theorem sum_squareVertices {M : Type*} [AddCommMonoid M] (g : H → M) :
    ∑ x with G.vertexOf x ∈ G.squareVertices c, g x =
      ∑ k, (g (G.squareCorner c k) + g (G.rot (G.squareCorner c k)) +
        g (G.rot (G.rot (G.squareCorner c k)))) := by
  rw [filter_mem_squareVertices, sum_biUnion]
  · refine sum_congr rfl fun k _ => ?_
    obtain ⟨h1, h2⟩ := rot_ne_of_card_vertexOf_eq_three (hq.card_vertexOf k)
    have h12 : G.rot (G.squareCorner c k) ≠ G.rot (G.rot (G.squareCorner c k)) :=
      fun h => h1 (G.rot.injective h).symm
    rw [vertexOf_eq_of_card_vertexOf_eq_three (hq.card_vertexOf k), sum_insert, sum_insert,
      sum_singleton, add_assoc]
    · simpa using h12
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨h1.symm, h2.symm⟩
  · intro j _ k _ hjk
    rw [Function.onFun, disjoint_left]
    intro x hj hk
    exact hjk (hq.injective ((G.vertexOf_eq_of_mem hj).symm.trans (G.vertexOf_eq_of_mem hk)))

/-- `σ²(c_k) = c̄_{k-1}`: the third dart at `v(c_k)`. -/
theorem rot_rot_squareCorner' (k : Fin 4) :
    G.rot (G.rot (G.squareCorner c k)) = G.inv (G.squareCorner c (k - 1)) := by
  simpa only [sub_add_cancel] using hq.rot_rot_squareCorner (k - 1)

/-- The face `q` is not a boundary face. -/
theorem faceOf_notMem_boundaryFaces : G.faceOf c ∉ G.boundaryFaces := fun h =>
  (G.mem_boundaryFaces.1 h).2 (G.mem_internalFaces.1 hq.faceOf_mem_internalFaces).2

/-- The face `q` is a mutable vertex of `Q(G)`. -/
theorem notMem_frozen_quiver {q : G.faces} (hqc : (q : Finset H) = G.faceOf c) :
    q ∉ G.quiver.frozen := by
  rw [mem_frozen_quiver, hqc]
  exact hq.faceOf_notMem_boundaryFaces

/-- Consecutive corners carry opposite weights. -/
theorem dartWeight_squareCorner_add_one (k : Fin 4) :
    G.dartWeight (G.squareCorner c (k + 1)) = -G.dartWeight (G.squareCorner c k) := by
  unfold dartWeight
  rw [if_neg (hq.not_isBoundaryVertex _), if_neg (hq.not_isBoundaryVertex _),
    hq.colour_squareCorner_add_one]
  cases G.colour (G.squareCorner c k) <;> simp

/-- The weight of a corner is `±1`. -/
theorem dartWeight_squareCorner (k : Fin 4) :
    G.dartWeight (G.squareCorner c k) = 1 ∨ G.dartWeight (G.squareCorner c k) = -1 := by
  unfold dartWeight
  rw [if_neg (hq.not_isBoundaryVertex _)]
  split_ifs <;> simp

/-- The dart balance `ψ_G(q, F) = ∑_{F_k = F} χ_k`, where `F_k` is the face to the left of
`c_k` and `χ_k` the weight of `c_k`. -/
theorem dartBalance_left {q : G.faces} (hqc : (q : Finset H) = G.faceOf c) (F : G.faces) :
    G.dartBalance q F = ∑ k, if G.leftFace (G.squareCorner c k) = F then
      G.dartWeight (G.squareCorner c k) else 0 := by
  rw [dartBalance_eq_sum, hqc]
  have h : ∀ x, (if G.rightFace x = G.faceOf c ∧ G.leftFace x = F then G.dartWeight x else 0) =
      if x ∈ G.faceOf c then (if G.leftFace x = F then G.dartWeight x else 0) else 0 :=
    fun x => by
      have e : G.rightFace x = G.faceOf c ↔ x ∈ G.faceOf c := G.faceOf_eq_faceOf_iff_mem
      by_cases h1 : x ∈ G.faceOf c <;> simp [e, h1]
  rw [sum_congr rfl fun x _ => h x, sum_ite_mem, univ_inter, hq.sum_faceOf]

variable (hG : G.IsPlabicGraph)

include hG

/-- The weight of `c̄_k` is that of `c_{k+1}`. -/
theorem dartWeight_inv_squareCorner (k : Fin 4) :
    G.dartWeight (G.inv (G.squareCorner c k)) = G.dartWeight (G.squareCorner c (k + 1)) := by
  rw [← hq.rot_rot_squareCorner k, hG.dartWeight_rot, hG.dartWeight_rot]

/-- The face to the left of `ℓ_k = σ(c_k)` is the face `F_{k-1}` to the left of `c_{k-1}`. -/
theorem leftFace_rot_squareCorner (k : Fin 4) :
    G.leftFace (G.rot (G.squareCorner c k)) = G.leftFace (G.squareCorner c (k - 1)) := by
  change G.faceOf _ = G.faceOf _
  rw [← G.faceOf_facePerm (G.inv (G.rot (G.squareCorner c k))), G.facePerm_apply,
    hG.inv_involutive, hq.rot_rot_squareCorner']

/-- The face to the left of `σ²(c_k) = c̄_{k-1}` is `q`. -/
theorem leftFace_rot_rot_squareCorner (k : Fin 4) :
    G.leftFace (G.rot (G.rot (G.squareCorner c k))) = G.faceOf c := by
  rw [hq.rot_rot_squareCorner', DiskMap.leftFace, hG.inv_involutive, G.faceOf_squareCorner]

/-- The dart balance `ψ_G(F, q) = -∑_{F_k = F} χ_k`: the darts with `q` to their left are the
`c̄_k`, at the vertex `v(c_{k+1})` of the opposite colour. -/
theorem dartBalance_right {q : G.faces} (hqc : (q : Finset H) = G.faceOf c) (F : G.faces) :
    G.dartBalance F q = -∑ k, if G.leftFace (G.squareCorner c k) = F then
      G.dartWeight (G.squareCorner c k) else 0 := by
  rw [dartBalance_eq_sum, hqc, ← Equiv.sum_comp G.inv]
  have h : ∀ x, (if G.rightFace (G.inv x) = F ∧ G.leftFace (G.inv x) = G.faceOf c then
      G.dartWeight (G.inv x) else 0) =
      if x ∈ G.faceOf c then (if G.leftFace x = F then G.dartWeight (G.inv x) else 0) else 0 := by
    intro x
    have e : G.leftFace (G.inv x) = G.faceOf c ↔ x ∈ G.faceOf c := by
      rw [DiskMap.leftFace, hG.inv_involutive]
      exact G.faceOf_eq_faceOf_iff_mem
    have e' : G.rightFace (G.inv x) = G.leftFace x := rfl
    by_cases h1 : x ∈ G.faceOf c <;> simp [e, e', h1]
  rw [sum_congr rfl fun x _ => h x, sum_ite_mem, univ_inter, hq.sum_faceOf, ← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [hq.dartWeight_inv_squareCorner hG, hq.dartWeight_squareCorner_add_one]
  split_ifs <;> simp

/-- **The signed count of `Q(G)` at `(q, F)`**: `c(q, F) - c(F, q) = ∑_{F_k = F} χ_k` for every
face `F ≠ q`. -/
theorem quiverCount_sub_eq_sum {q : G.faces} (hqc : (q : Finset H) = G.faceOf c) {F : G.faces}
    (hF : F ≠ q) :
    (G.quiverCount q F : ℤ) - G.quiverCount F q = ∑ k, if G.leftFace (G.squareCorner c k) = F
      then G.dartWeight (G.squareCorner c k) else 0 := by
  have hbd : ¬((q : Finset H) ∈ G.boundaryFaces ∧ (F : Finset H) ∈ G.boundaryFaces) :=
    fun h => hq.faceOf_notMem_boundaryFaces (hqc ▸ h.1)
  have := G.two_mul_quiverCount_sub hG.toIsDiskMap (Ne.symm hF) hbd
  rw [hq.dartBalance_left hqc, hq.dartBalance_right hG hqc] at this
  linarith

/-- The weights of the darts at the vertices of `q` with neither side equal to `q`: these are the
darts `ℓ_k = σ(c_k)`, from `F_k` to `F_{k-1}`, of weight `χ_k`. -/
theorem sum_squareVertices_dartWeight {f f' : G.faces} (hf : (f : Finset H) ≠ G.faceOf c)
    (hf' : (f' : Finset H) ≠ G.faceOf c) :
    (∑ x, if G.vertexOf x ∈ G.squareVertices c ∧ G.rightFace x = f ∧ G.leftFace x = f' then
      G.dartWeight x else 0) =
      ∑ k, if G.leftFace (G.squareCorner c k) = f ∧ G.leftFace (G.squareCorner c (k - 1)) = f'
        then G.dartWeight (G.squareCorner c k) else 0 := by
  simp only [ite_and (G.vertexOf _ ∈ _)]
  rw [← sum_filter, hq.sum_squareVertices]
  refine sum_congr rfl fun k _ => ?_
  have ha : ¬(G.rightFace (G.squareCorner c k) = f ∧ G.leftFace (G.squareCorner c k) = f') :=
    fun h => hf (h.1 ▸ G.faceOf_squareCorner c k)
  have hc : ¬(G.rightFace (G.rot (G.rot (G.squareCorner c k))) = f ∧
      G.leftFace (G.rot (G.rot (G.squareCorner c k))) = f') :=
    fun h => hf' (h.2 ▸ hq.leftFace_rot_rot_squareCorner hG k)
  rw [if_neg ha, if_neg hc, hG.rightFace_rot, hq.leftFace_rot_squareCorner hG,
    hG.dartWeight_rot, zero_add, add_zero]

/-- **The signed count of `Q(G_q)` at `(q, F)`**: `c_q(q, F) - c_q(F, q) = -∑_{F_k = F} χ_k` for
every face `F ≠ q`, where `c_q` is the counting function of the square move `G_q`. -/
theorem quiverCount_squareMove_sub_eq_sum {q : G.faces} (hqc : (q : Finset H) = G.faceOf c)
    {F : G.faces} (hF : F ≠ q) :
    ((G.squareMove c).quiverCount q F : ℤ) - (G.squareMove c).quiverCount F q =
      -∑ k, if G.leftFace (G.squareCorner c k) = F then G.dartWeight (G.squareCorner c k)
        else 0 := by
  rw [hq.squareMove.quiverCount_sub_eq_sum (hG.squareMove c) hqc hF, ← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  change (if G.leftFace (G.squareCorner c k) = F then
    (G.squareMove c).dartWeight (G.squareCorner c k) else 0) = _
  rw [dartWeight_squareMove, if_pos (vertexOf_squareCorner_mem_squareVertices c k)]
  split_ifs <;> simp

/-- **The arrows between `q` and a face `F ≠ q`** in `Q(G)`: `a(q, F)` and `a(F, q)` are the
positive and negative parts of `∑_{F_k = F} χ_k`. -/
theorem arrows_quiver_eq_max {q : G.faces} (hqc : (q : Finset H) = G.faceOf c) {F : G.faces}
    (hF : F ≠ q) :
    (G.quiver.arrows q F : ℤ) = max (∑ k, if G.leftFace (G.squareCorner c k) = F then
        G.dartWeight (G.squareCorner c k) else 0) 0 ∧
      (G.quiver.arrows F q : ℤ) = max (-∑ k, if G.leftFace (G.squareCorner c k) = F then
        G.dartWeight (G.squareCorner c k) else 0) 0 := by
  have := hq.quiverCount_sub_eq_sum hG hqc hF
  rw [arrows_quiver_apply, arrows_quiver_apply]
  constructor <;> omega

/-- **The signed count of `Q(G_q)` away from `q`**: for faces `i ≠ j`, both different from `q` and
not both boundary faces, `c_q(i, j) - c_q(j, i)` is `c(i, j) - c(j, i)` minus the antisymmetrised
weight of the darts `ℓ_k` from `F_k = i` to `F_{k-1} = j`. -/
theorem quiverCount_squareMove_sub {q : G.faces} (hqc : (q : Finset H) = G.faceOf c)
    {i j : G.faces} (hi : i ≠ q) (hj : j ≠ q) (hij : i ≠ j)
    (hbd : ¬((i : Finset H) ∈ G.boundaryFaces ∧ (j : Finset H) ∈ G.boundaryFaces)) :
    ((G.squareMove c).quiverCount i j : ℤ) - (G.squareMove c).quiverCount j i =
      (G.quiverCount i j : ℤ) - G.quiverCount j i -
        ((∑ k, if G.leftFace (G.squareCorner c k) = i ∧
            G.leftFace (G.squareCorner c (k - 1)) = j then G.dartWeight (G.squareCorner c k)
            else 0) -
          ∑ k, if G.leftFace (G.squareCorner c k) = j ∧
            G.leftFace (G.squareCorner c (k - 1)) = i then G.dartWeight (G.squareCorner c k)
            else 0) := by
  have hne : ∀ F : G.faces, F ≠ q → (F : Finset H) ≠ G.faceOf c :=
    fun F hF h => hF (Subtype.ext (h.trans hqc.symm))
  have hb : ¬((i : Finset H) ∈ (G.squareMove c).boundaryFaces ∧
      (j : Finset H) ∈ (G.squareMove c).boundaryFaces) := by
    rwa [boundaryFaces_squareMove]
  have e1 := (G.squareMove c).two_mul_quiverCount_sub (hG.squareMove c).toIsDiskMap hij hb
  have e2 := G.two_mul_quiverCount_sub hG.toIsDiskMap hij hbd
  rw [dartBalance_squareMove, dartBalance_squareMove,
    hq.sum_squareVertices_dartWeight hG (hne i hi) (hne j hj),
    hq.sum_squareVertices_dartWeight hG (hne j hj) (hne i hi)] at e1
  linarith

/-- The signed count of `Q(G_q)` is that of the mutation `μ_q(Q(G))`. -/
theorem quiverCount_squareMove_sub_eq_signedCount_mutate
    (hF : ∀ k, G.leftFace (G.squareCorner c k) ≠ G.leftFace (G.squareCorner c (k + 1)))
    {q : G.faces} (hqc : (q : Finset H) = G.faceOf c) (i j : G.faces) :
    ((G.squareMove c).quiverCount i j : ℤ) - (G.squareMove c).quiverCount j i =
      signedCount (G.quiver.mutate (hq.notMem_frozen_quiver hqc)).arrows i j := by
  have hk := hq.notMem_frozen_quiver hqc
  rcases eq_or_ne i j with rfl | hij
  · simp only [sub_self, signedCount]
  by_cases hi : i = q
  · subst hi
    linarith [G.quiver.signedCount_mutate_of_left_eq hk j, G.signedCount_quiver i j,
      hq.quiverCount_squareMove_sub_eq_sum hG hqc hij.symm,
      hq.quiverCount_sub_eq_sum hG hqc hij.symm]
  by_cases hj : j = q
  · subst hj
    linarith [G.quiver.signedCount_mutate_of_right_eq hk i, G.signedCount_quiver i j,
      hq.quiverCount_squareMove_sub_eq_sum hG hqc hi, hq.quiverCount_sub_eq_sum hG hqc hi]
  by_cases hbd : (i : Finset H) ∈ G.boundaryFaces ∧ (j : Finset H) ∈ G.boundaryFaces
  · have hb : (i : Finset H) ∈ (G.squareMove c).boundaryFaces ∧
        (j : Finset H) ∈ (G.squareMove c).boundaryFaces := by
      rwa [boundaryFaces_squareMove]
    have hm := G.quiver.signedCount_mutate_of_frozen hk (G.mem_frozen_quiver.2 hbd.1)
      (G.mem_frozen_quiver.2 hbd.2)
    have hs := G.signedCount_quiver i j
    simp only [G.quiverCount_eq_zero hbd.1 hbd.2, G.quiverCount_eq_zero hbd.2 hbd.1,
      (G.squareMove c).quiverCount_eq_zero hb.1 hb.2,
      (G.squareMove c).quiverCount_eq_zero hb.2 hb.1, Nat.cast_zero, sub_self] at hs ⊢
    linarith
  have key := alternating_identity (F := fun k => G.leftFace (G.squareCorner c k))
    (χ := fun k => G.dartWeight (G.squareCorner c k)) hF hq.dartWeight_squareCorner_add_one
    (hq.dartWeight_squareCorner 0) (i : Finset H) (j : Finset H)
  beta_reduce at key
  exact square_step (G.quiver.signedCount_mutate_of_not_frozen hk hi hj
    fun h => hbd ⟨G.mem_frozen_quiver.1 h.1, G.mem_frozen_quiver.1 h.2⟩)
    (G.signedCount_quiver i j) (hq.arrows_quiver_eq_max hG hqc hi).1
    (hq.arrows_quiver_eq_max hG hqc hi).2 (hq.arrows_quiver_eq_max hG hqc hj).1
    (hq.arrows_quiver_eq_max hG hqc hj).2 (hq.quiverCount_squareMove_sub hG hqc hi hj hij hbd)
    key

/-- Let `G` be a plabic graph and `q = (c₁, c₂, c₃, c₄)` a face at which a square move applies,
with `c₁ = c` and `c_{k+1} = squareCorner c k`, and assume that for each `k` (modulo `4`) the faces
to the left of `c_k` and of `c_{k+1}` are distinct. Then the quiver of the square move of `G` at
`q` is the mutation of the quiver of `G` at the face `q`: `Q(G_q) = μ_q(Q(G))`. -/
@[cluster_algebras "lem_square_move_quiver"]
theorem quiver_squareMove
    (hF : ∀ k, G.leftFace (G.squareCorner c k) ≠ G.leftFace (G.squareCorner c (k + 1)))
    {q : G.faces} (hqc : (q : Finset H) = G.faceOf c) :
    (G.squareMove c).quiver = G.quiver.mutate (hq.notMem_frozen_quiver hqc) :=
  Quiver.ext' rfl ((G.squareMove c).quiver.twoCycleFree.eq_of_signedCount_eq
    (G.quiver.mutate _).twoCycleFree (funext₂ fun i j =>
      ((G.squareMove c).signedCount_quiver i j).trans
        (hq.quiverCount_squareMove_sub_eq_signedCount_mutate hG hF hqc i j)))

end IsSquareMoveFace

end PlabicData

end ClusterAlgebras

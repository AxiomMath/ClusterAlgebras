/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.EdgeContraction
public import ClusterAlgebras.Plabic.PlabicQuiver
public import ClusterAlgebras.Plabic.SquareTrips

/-!
# Contracting an edge: the quiver and the roundtrips

Let `G = (H, d ↦ d̄, σ, B, κ, β)` be a plabic graph and `{d, d̄}` an edge whose endpoints
`u = v(d)` and `w = v(d̄)` are distinct internal vertices of a common colour `c`, and let `G_e` be
the contraction of `G` along `{d, d̄}`, with darts `H' = H \ {d, d̄}`.

*The quiver.* The bijection `Ψ(f) = f ∩ H'` from the faces of `G` to the faces of `G_e` matches
the boundary faces. A dart `x ∈ H' \ B` has the same partner in `G` and `G_e`, its two faces in
`G_e` are the images under `Ψ` of its faces in `G`, and its vertex in `G_e` is internal of a given
colour exactly when its vertex in `G` is. The two deleted darts `d` and `d̄` lie at internal
vertices of the same colour, so they contribute equally to `ψ_G(f, f')` and `ψ_G(f', f)`, which
cancels in the difference. By the criterion for an isomorphism of quivers of plabic graphs, `Ψ` is
an isomorphism `Q(G) → Q(G_e)`.

*Roundtrips.* With `ρ = (d d̄)` and `τ = σ ∘ ρ`, the rotation of `G_e` is the first return
`τ_{H'}`. For `y ∈ H' \ B` with `ȳ` at the merged vertex, the trip of `G` leaving along `y` crosses
the edge `{d, d̄}` some number of times and then follows `τ` (black) or `ρ ∘ σ⁻¹` (white); so the
trip map of `G_e` is the first return to `H'` of the trip map of `G`. Since no orbit of the trip
map of `G` lies in `{d, d̄}`, the trip map of `G` has an orbit avoiding the legs if and only if
that of `G_e` does.

## Main results

* `ClusterAlgebras.PlabicData.exists_quiverIso_contractEdge`: `f ↦ f ∩ H'` is an isomorphism
  `Q(G) → Q(G_e)`.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.hasRoundtrip_contractEdge_iff`: `G` has a roundtrip
  if and only if `G_e` has one.
* `ClusterAlgebras.PlabicData.coe_contractEdge_tripMap`: the trip map of `G_e` is the first return
  to `H'` of the trip map of `G`.
* `ClusterAlgebras.PlabicData.bijOn_faces_contractEdge`: `f ↦ f ∩ H'` matches the faces.

## Implementation notes

* As in `ClusterAlgebras.Plabic.EdgeContraction`, the darts of `G_e` form the subtype
  `({d, d̄} : Set H)ᶜ` of `H` and `f ∩ H'` is `Finset.subtype`.
* The trip maps are the permutations `IsPlabicGraph.tripEquiv` of all darts, which preserve `B`;
  a roundtrip is an orbit avoiding the darts that are in `B` or are legs, and these lie in `H'`.
* In the white case FWZ compare `T^s(y)` with `τ^{-s}(ȳ)` through `ρ`. Here this is the
  statement that the first return of `τ⁻¹` is the first return of its conjugate `σ⁻¹ ∘ ρ` by `ρ`,
  which fixes `H'` pointwise, together with `(τ⁻¹)_{H'} = (τ_{H'})⁻¹`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm Function

/-! ### First returns -/

section FirstReturn

variable {X : Type*} [Finite X] {Y : Set X}

/-- If `P` and `Q` agree off `Y` and `P y = Q y'`, then the first return of `y` under `P` is the
first return of `y'` under `Q`. -/
theorem coe_firstReturn_eq_of_eqOn_compl {P Q : Perm X} {y y' : Y} (h₁ : P y = Q y')
    (h : ∀ z, z ∉ Y → P z = Q z) :
    (firstReturn P Y y : X) = firstReturn Q Y y' := by
  have key : ∀ s, 0 < s → (∀ r, 0 < r → r < s → (Q ^ r) (y' : X) ∉ Y) →
      (P ^ s) (y : X) = (Q ^ s) y' := by
    intro s
    induction s with
    | zero => exact fun h => absurd h (lt_irrefl 0)
    | succ s ih =>
      intro _ hmin
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · simpa using h₁
      · rw [pow_succ', Perm.mul_apply, ih hs fun r hr hrs => hmin r hr (by omega),
          h _ (hmin s hs (by omega)), ← Perm.mul_apply, ← pow_succ']
  set m := firstReturnTime Q Y y' with hm
  have hmpos : 0 < m := firstReturnTime_pos _
  have hmin : ∀ r, 0 < r → r < m → (Q ^ r) (y' : X) ∉ Y := fun r hr hrm =>
    pow_apply_notMem_of_lt_firstReturnTime hr hrm
  rw [coe_firstReturn Q Y y', ← hm, ← key m hmpos hmin]
  refine coe_firstReturn_of_pow hmpos ?_ fun j hj hjm => ?_
  · rw [key m hmpos hmin]
    exact pow_firstReturnTime_apply_mem _
  · rw [key j hj fun r hr hrj => hmin r hr (by omega)]
    exact hmin j hj hjm

/-- The first return of `π⁻¹` to `Y` is the inverse of the first return of `π`. -/
theorem firstReturnPerm_inv (π : Perm X) (Y : Set X) :
    firstReturnPerm π⁻¹ Y = (firstReturnPerm π Y)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right (Perm.ext fun x => Subtype.ext ?_)
  rw [Perm.mul_apply, Perm.one_apply, coe_firstReturnPerm, coe_firstReturnPerm]
  set m := firstReturnTime π⁻¹ Y x with hm
  have hmpos : 0 < m := firstReturnTime_pos _
  have hback : ∀ j, j ≤ m → (π ^ j) ((π⁻¹ ^ m) (x : X)) = (π⁻¹ ^ (m - j)) x := by
    intro j hj
    rw [show m = j + (m - j) by omega, pow_add, Perm.mul_apply, Nat.add_sub_cancel_left,
      ← Perm.mul_apply, inv_pow, inv_pow, mul_inv_cancel, Perm.one_apply]
  have h0 : (π ^ m) ((π⁻¹ ^ m) (x : X)) = x := by
    rw [hback m le_rfl, Nat.sub_self, pow_zero, Perm.one_apply]
  have hx' : (firstReturn π⁻¹ Y x : X) = (π⁻¹ ^ m) x := by rw [coe_firstReturn, ← hm]
  rw [coe_firstReturn_of_pow (y := firstReturn π⁻¹ Y x) hmpos, hx', h0]
  · rw [hx', h0]
    exact x.2
  · intro j hj hjm
    rw [hx', hback j hjm.le]
    exact pow_apply_notMem_of_lt_firstReturnTime (by omega) (by omega)

/-- Conjugating by a permutation `ρ` that preserves `Y` and fixes it pointwise does not change the
first return to `Y`. -/
theorem coe_firstReturn_conj {π ρ : Perm X} (hρY : ∀ x, ρ x ∈ Y ↔ x ∈ Y)
    (hρ : ∀ y ∈ Y, ρ y = y) (y : Y) :
    (firstReturn (ρ * π * ρ⁻¹) Y y : X) = firstReturn π Y y := by
  have hpow : ∀ n : ℕ, ((ρ * π * ρ⁻¹) ^ n) (y : X) = ρ ((π ^ n) y) := fun n => by
    rw [conj_pow, Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq.2 (hρ y y.2).symm]
  have hm := pow_firstReturnTime_apply_mem (π := π) y
  rw [coe_firstReturn π Y y, ← hρ _ hm, ← hpow]
  refine coe_firstReturn_of_pow (firstReturnTime_pos _) ?_ fun j hj hjm => ?_
  · rwa [hpow, hρY]
  · rw [hpow, hρY]
    exact pow_apply_notMem_of_lt_firstReturnTime hj hjm

end FirstReturn

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b} {d : H}
  {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}

/-! ### Darts at the endpoints of the edge -/

section Endpoints

/-- A dart lies at the vertex `v(a)` iff its vertex is `v(a)`. -/
theorem mem_vertexOf_iff_vertexOf_eq {x a : H} : x ∈ G.vertexOf a ↔ G.vertexOf x = G.vertexOf a :=
  ⟨G.vertexOf_eq_of_mem, fun h => h ▸ G.self_mem_vertexOf x⟩

/-- Darts at one vertex lie together at an endpoint of the edge, or not. -/
theorem mem_union_vertexOf_iff_of_vertexOf_eq {x x' : H} (h : G.vertexOf x = G.vertexOf x') :
    x ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) ↔ x' ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  simp only [mem_union, mem_vertexOf_iff_vertexOf_eq, h]

omit [Fintype H] [DecidableEq H] in
/-- A dart outside `H \ {d, d̄}` is `d` or `d̄`. -/
theorem eq_or_eq_of_notMem_compl_pair {x : H} (hx : x ∉ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    x = d ∨ x = G.inv d := by
  rwa [mem_compl_pair_iff, not_and_or, not_not, not_not] at hx

/-- The darts `d`, `d̄` lie at the endpoints of the edge. -/
theorem mem_union_of_notMem_compl_pair {x : H} (hx : x ∉ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    x ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  rcases eq_or_eq_of_notMem_compl_pair hx with rfl | rfl
  · exact mem_union_left _ (G.self_mem_vertexOf _)
  · exact mem_union_right _ (G.self_mem_vertexOf _)

/-- The reverses of the darts `d`, `d̄` lie at the endpoints of the edge. -/
theorem inv_mem_union_of_notMem_compl_pair (hinv : Involutive G.inv) {x : H}
    (hx : x ∉ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    G.inv x ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  rcases eq_or_eq_of_notMem_compl_pair hx with rfl | rfl
  · exact mem_union_right _ (G.self_mem_vertexOf _)
  · rw [hinv]
    exact mem_union_left _ (G.self_mem_vertexOf _)

omit [Fintype H] in
/-- The transposition of `d` and `d̄` reverses the darts `d`, `d̄`. -/
theorem swap_apply_eq_inv_of_notMem_compl_pair (hinv : Involutive G.inv) {x : H}
    (hx : x ∉ (({d, G.inv d} : Set H)ᶜ : Set H)) : swap d (G.inv d) x = G.inv x := by
  rcases eq_or_eq_of_notMem_compl_pair hx with rfl | rfl
  · rw [swap_apply_left]
  · rw [swap_apply_right, hinv]

omit [Fintype H] in
/-- The transposition of `d` and `d̄` fixes every dart of `H \ {d, d̄}`. -/
theorem swap_apply_of_mem_compl_pair {x : H} (hx : x ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    swap d (G.inv d) x = x :=
  swap_apply_of_ne_of_ne (mem_compl_pair_iff.1 hx).1 (mem_compl_pair_iff.1 hx).2

/-- A dart at an endpoint of the edge is at an internal vertex of colour `s` iff `κ(d) = s`. -/
theorem isInternalOfColour_iff_of_mem_union (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
    {x : H} (hx : x ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) (s : Shade) :
    G.IsInternalOfColour x s ↔ G.colour d = s := by
  rw [IsInternalOfColour, colour_eq_of_mem_union hG he hx]
  exact ⟨fun h => h.2, fun h => ⟨fun hb => he.notMem_of_isBoundaryVertex hb hx, h⟩⟩

end Endpoints

/-! ### The quiver -/

section Quiver

/-- **Faces under the contraction of an edge**: `f ↦ f ∩ H'` is a bijection from the faces of `G`
onto the faces of the contraction. -/
theorem bijOn_faces_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    Set.BijOn (fun f : Finset H => f.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))
      G.faces (G.contractEdge d hleg).faces := by
  have hb := bijOn_faceOrbits_contractEdge (hleg := hleg) hG he
  have hext := subtype_exterior (hleg := hleg) he
  refine ⟨fun f hf => ?_, fun f hf f' hf' h => ?_, fun g hg => ?_⟩
  · obtain ⟨hfe, hfΦ⟩ := (DiskMap.mem_faces _).1 (mem_coe.1 hf)
    refine mem_coe.2 ((DiskMap.mem_faces _).2 ⟨fun h => hfe ?_, mem_coe.1 (hb.mapsTo
      (mem_coe.2 hfΦ))⟩)
    rw [← hext] at h
    exact hb.injOn (mem_coe.2 hfΦ) (mem_coe.2 hG.exterior_mem_faceOrbits) h
  · exact hb.injOn (mem_coe.2 ((DiskMap.mem_faces _).1 (mem_coe.1 hf)).2)
      (mem_coe.2 ((DiskMap.mem_faces _).1 (mem_coe.1 hf')).2) h
  · obtain ⟨hge, hgΦ⟩ := (DiskMap.mem_faces _).1 (mem_coe.1 hg)
    obtain ⟨f, hf, rfl⟩ := hb.surjOn (mem_coe.2 hgΦ)
    refine ⟨f, mem_coe.2 ((DiskMap.mem_faces _).2 ⟨fun h => hge ?_, mem_coe.1 hf⟩), rfl⟩
    simp only [h, hext]

/-- The face to the right of a dart of the contraction is the trace of its face in `G`. -/
theorem rightFace_contractEdge (hinv : Involutive G.inv) (x : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).rightFace x =
      (G.rightFace x).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :=
  (subtype_faceOf_eq_faceOf hinv x.2 (SameCycle.refl _ _)).symm

/-- The face to the left of a dart of the contraction is the trace of its face in `G`. -/
theorem leftFace_contractEdge (hinv : Involutive G.inv) (x : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).leftFace x =
      (G.leftFace x).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) := by
  have hzy : G.facePerm.SameCycle (G.inv x) ((G.contractEdge d hleg).inv x : H) := by
    rw [coe_contractEdge_inv hinv]
  exact (subtype_faceOf_eq_faceOf hinv ((G.contractEdge d hleg).inv x).2 hzy).symm

/-- A dart of the contraction is at an internal vertex of colour `s` iff it is so in `G`. -/
theorem isInternalOfColour_contractEdge_iff (he : G.IsContractibleEdge d)
    (x : (({d, G.inv d} : Set H)ᶜ : Set H)) (s : Shade) :
    (G.contractEdge d hleg).IsInternalOfColour x s ↔ G.IsInternalOfColour x s := by
  rw [IsInternalOfColour, IsInternalOfColour, isBoundaryVertex_vertexOf_contractEdge_iff he,
    contractEdge_colour]

/-- The darts of the contraction counted by its dart balance at `(f ∩ H', f' ∩ H')` are the darts
of `H'` counted by the dart balance of `G` at `(f, f')`. -/
theorem card_filter_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) (s : Shade)
    {f f' : Finset H} (hf : f ∈ G.faceOrbits) (hf' : f' ∈ G.faceOrbits) :
    #{x | x ∉ (G.contractEdge d hleg).bdry ∧ (G.contractEdge d hleg).IsInternalOfColour x s ∧
      (G.contractEdge d hleg).rightFace x = f.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) ∧
      (G.contractEdge d hleg).leftFace x = f'.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))} =
    #{x | (x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f ∧ G.leftFace x = f') ∧
      x ∈ (({d, G.inv d} : Set H)ᶜ : Set H)} := by
  have hinv := hG.inv_involutive
  have hb := bijOn_faceOrbits_contractEdge (hleg := hleg) hG he
  have hinj : ∀ {g g' : Finset H}, g ∈ G.faceOrbits → g' ∈ G.faceOrbits →
      (g.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) =
        g'.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) ↔ g = g') :=
    fun hg hg' => ⟨fun h => hb.injOn (mem_coe.2 hg) (mem_coe.2 hg') h, fun h => h ▸ rfl⟩
  have key : ∀ a : (({d, G.inv d} : Set H)ᶜ : Set H),
      (a ∉ (G.contractEdge d hleg).bdry ∧ (G.contractEdge d hleg).IsInternalOfColour a s ∧
        (G.contractEdge d hleg).rightFace a = f.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) ∧
        (G.contractEdge d hleg).leftFace a =
          f'.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))) ↔
      ((a : H) ∉ G.bdry ∧ G.IsInternalOfColour a s ∧ G.rightFace a = f ∧ G.leftFace a = f') := by
    intro a
    rw [mem_contractEdge_bdry, isInternalOfColour_contractEdge_iff he, rightFace_contractEdge hinv,
      leftFace_contractEdge hinv, hinj (RotationSystem.faceOf_mem_faceOrbits _ _) hf,
      hinj (RotationSystem.faceOf_mem_faceOrbits _ _) hf']
  refine card_bij (fun a _ => (a : H)) (fun a ha => ?_) (fun a _ a' _ h => Subtype.ext h)
    (fun x hx => ?_)
  · rw [mem_filter] at ha ⊢
    exact ⟨mem_univ _, (key a).1 ha.2, a.2⟩
  · rw [mem_filter] at hx
    exact ⟨⟨x, hx.2.2⟩, mem_filter.2 ⟨mem_univ _, (key _).2 hx.2.1⟩, rfl⟩

/-- The darts counted by the dart balance of `G` split into those of `H'` and those of the edge. -/
theorem card_filter_eq_add_card_filter (s : Shade) (f f' : Finset H) :
    #{x | x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f ∧ G.leftFace x = f'} =
      #{x | (x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f ∧ G.leftFace x = f') ∧
        x ∈ (({d, G.inv d} : Set H)ᶜ : Set H)} +
      #{x | (x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f ∧ G.leftFace x = f') ∧
        x ∉ (({d, G.inv d} : Set H)ᶜ : Set H)} := by
  rw [← card_filter_add_card_filter_not (s := filter _ univ)
    (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)), filter_filter, filter_filter]

/-- The darts `d`, `d̄` contribute equally to the dart balances at `(f, f')` and at `(f', f)`. -/
theorem card_filter_notMem_comm (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) (s : Shade)
    (f f' : Finset H) :
    #{x | (x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f ∧ G.leftFace x = f') ∧
        x ∉ (({d, G.inv d} : Set H)ᶜ : Set H)} =
      #{x | (x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f' ∧ G.leftFace x = f) ∧
        x ∉ (({d, G.inv d} : Set H)ᶜ : Set H)} := by
  have hinv := hG.inv_involutive
  have hint : ∀ x, x ∉ (({d, G.inv d} : Set H)ᶜ : Set H) →
      (G.IsInternalOfColour (G.inv x) s ↔ G.IsInternalOfColour x s) := fun x hx => by
    rw [isInternalOfColour_iff_of_mem_union hG he (inv_mem_union_of_notMem_compl_pair hinv hx),
      isInternalOfColour_iff_of_mem_union hG he (mem_union_of_notMem_compl_pair hx)]
  refine card_equiv G.inv fun x => ?_
  simp only [mem_filter, mem_univ, true_and, DiskMap.rightFace, DiskMap.leftFace,
    hG.inv_mem_bdry_iff, hinv x, apply_mem_compl_pair_iff hinv]
  exact ⟨fun ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩ => ⟨⟨h₁, (hint x h₅).2 h₂, h₄, h₃⟩, h₅⟩,
    fun ⟨⟨h₁, h₂, h₃, h₄⟩, h₅⟩ => ⟨⟨h₁, (hint x h₅).1 h₂, h₄, h₃⟩, h₅⟩⟩

/-- If `{d, d̄}` is an edge of the plabic graph `G` whose endpoints are distinct internal vertices
of the same colour, then `f ↦ f ∩ H'`, where `H' = H \ {d, d̄}`, is an isomorphism from `Q(G)` to
the quiver of the contraction of `G` along `{d, d̄}`. -/
@[cluster_algebras "lem_edge_contraction_quiver"]
theorem exists_quiverIso_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    ∃ e : G.quiver.Iso (G.contractEdge d hleg).quiver, ∀ f,
      ((e.equiv f : (G.contractEdge d hleg).faces) : Finset (({d, G.inv d} : Set H)ᶜ : Set H)) =
        (f : Finset H).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) := by
  have hb := bijOn_faces_contractEdge (hleg := hleg) hG he
  let Ψ : G.faces ≃ (G.contractEdge d hleg).faces := hb.equiv _
  have hΨ : ∀ f, ((Ψ f : (G.contractEdge d hleg).faces) :
      Finset (({d, G.inv d} : Set H)ᶜ : Set H)) =
        (f : Finset H).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) := fun _ => rfl
  have hfo : ∀ f : G.faces, (f : Finset H) ∈ G.faceOrbits := fun f =>
    ((DiskMap.mem_faces _).1 f.2).2
  have hbd : ∀ f, ((Ψ f : (G.contractEdge d hleg).faces) :
      Finset (({d, G.inv d} : Set H)ᶜ : Set H)) ∈ (G.contractEdge d hleg).boundaryFaces ↔
        (f : Finset H) ∈ G.boundaryFaces := by
    intro f
    rw [hΨ, DiskMap.mem_boundaryFaces, DiskMap.mem_boundaryFaces,
      iff_true_intro (show _ ∈ (G.contractEdge d hleg).faces from hb.mapsTo f.2),
      iff_true_intro f.2, true_and, true_and, not_iff_not, disjoint_left, disjoint_left]
    exact ⟨fun h a ha haB => h (show (⟨a, he.mem_of_mem_bdry haB⟩ :
        (({d, G.inv d} : Set H)ᶜ : Set H)) ∈ _ from mem_subtype.2 ha) (mem_contractEdge_bdry.2 haB),
      fun h a ha haB => h (mem_subtype.1 ha) (mem_contractEdge_bdry.1 haB)⟩
  have hψ : ∀ f f' : G.faces, f ≠ f' →
      ¬((f : Finset H) ∈ G.boundaryFaces ∧ (f' : Finset H) ∈ G.boundaryFaces) →
      G.dartBalance f f' - G.dartBalance f' f = (G.contractEdge d hleg).dartBalance (Ψ f) (Ψ f') -
        (G.contractEdge d hleg).dartBalance (Ψ f') (Ψ f) := by
    intro f f' _ _
    rw [dartBalance, dartBalance, dartBalance, dartBalance, hΨ, hΨ,
      card_filter_contractEdge hG he _ (hfo f) (hfo f'),
      card_filter_contractEdge hG he _ (hfo f) (hfo f'),
      card_filter_contractEdge hG he _ (hfo f') (hfo f),
      card_filter_contractEdge hG he _ (hfo f') (hfo f),
      card_filter_eq_add_card_filter (d := d) .white (f : Finset H) f',
      card_filter_eq_add_card_filter (d := d) .black (f : Finset H) f',
      card_filter_eq_add_card_filter (d := d) .white (f' : Finset H) f,
      card_filter_eq_add_card_filter (d := d) .black (f' : Finset H) f,
      card_filter_notMem_comm hG he .white (f : Finset H) f',
      card_filter_notMem_comm hG he .black (f : Finset H) f']
    push_cast
    ring
  obtain ⟨e, he'⟩ := exists_quiverIso_of_dartBalance hG.toIsDiskMap
    (hG.contractEdge (hleg := hleg) he).toIsDiskMap Ψ hbd hψ
  exact ⟨e, fun f => by rw [he', hΨ]⟩

end Quiver

/-! ### Roundtrips -/

section Roundtrip

/-- At a dart outside `v(d) ∪ v(d̄)`, the turn of the contraction is the turn of `G`. -/
theorem coe_contractEdge_turn_of_notMem (he : G.IsContractibleEdge d)
    {z : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hz : (z : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    ((G.contractEdge d hleg).turn z : H) = G.turn z := by
  have hb := isBoundaryVertex_vertexOf_contractEdge_iff (hleg := hleg) he (x := z)
  by_cases hzb : G.IsBoundaryVertex (G.vertexOf z)
  · rw [turn_of_isBoundaryVertex (hb.2 hzb), turn_of_isBoundaryVertex hzb]
  have hzb' : ¬(G.contractEdge d hleg).IsBoundaryVertex ((G.contractEdge d hleg).vertexOf z) :=
    fun h => hzb (hb.1 h)
  cases hc : G.colour z
  · rw [turn_of_white hzb' (by rw [contractEdge_colour, hc]), turn_of_white hzb hc]
    have hv := G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf z)
    have hm : G.rot.symm z ∈ (({d, G.inv d} : Set H)ᶜ : Set H) :=
      mem_compl_pair_of_notMem (by rwa [mem_union_vertexOf_iff_of_vertexOf_eq hv])
    have hr : (G.contractEdge d hleg).rot ⟨G.rot.symm z, hm⟩ = z := Subtype.ext (by
      rw [coe_contractEdge_rot_of_mem (by simp)]
      simp)
    rw [(Equiv.symm_apply_eq _).2 hr.symm]
  · rw [turn_of_black hzb' (by rw [contractEdge_colour, hc]), turn_of_black hzb hc,
      coe_contractEdge_rot_of_mem (mem_compl_pair_of_notMem (rot_notMem_of_notMem hz))]

/-- **The trip map of the contraction is a first return.** The trip map of the contraction along
`{d, d̄}` is the first-return map to `H' = H \ {d, d̄}` of the trip map of `G`. -/
theorem coe_contractEdge_tripMap (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
    (y : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    ((G.contractEdge d hleg).tripMap y : H) =
      firstReturn hG.tripEquiv (({d, G.inv d} : Set H)ᶜ : Set H) y := by
  have hinv := hG.inv_involutive
  have hz : ((G.contractEdge d hleg).inv y : H) = G.inv y := coe_contractEdge_inv hinv y
  set z := (G.contractEdge d hleg).inv y
  have hTy : hG.tripEquiv y = G.turn z := by
    rw [IsPlabicGraph.tripEquiv_apply, tripMap_apply, hz]
  rw [tripMap_apply]
  by_cases hzU : (z : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
  swap
  · rw [coe_contractEdge_turn_of_notMem he hzU, coe_firstReturn_of_apply_mem, hTy]
    rw [hTy]
    exact mem_compl_pair_of_notMem <| by
      rwa [mem_union_vertexOf_iff_of_vertexOf_eq (vertexOf_turn _)]
  have hzb : ¬G.IsBoundaryVertex (G.vertexOf z) := fun h => he.notMem_of_isBoundaryVertex h hzU
  have hzb' : ¬(G.contractEdge d hleg).IsBoundaryVertex ((G.contractEdge d hleg).vertexOf z) :=
    fun h => hzb ((isBoundaryVertex_vertexOf_contractEdge_iff he).1 h)
  have hzs : swap d (G.inv d) z = z := swap_apply_of_mem_compl_pair z.2
  have hxb : ∀ x, x ∉ (({d, G.inv d} : Set H)ᶜ : Set H) →
      ¬G.IsBoundaryVertex (G.vertexOf (G.inv x)) := fun x hx h =>
    he.notMem_of_isBoundaryVertex h (inv_mem_union_of_notMem_compl_pair hinv hx)
  have hxc : ∀ x, x ∉ (({d, G.inv d} : Set H)ᶜ : Set H) → G.colour (G.inv x) = G.colour d :=
    fun x hx => colour_eq_of_mem_union hG he (inv_mem_union_of_notMem_compl_pair hinv hx)
  have hzc := colour_eq_of_mem_union hG he hzU
  cases hc : G.colour d
  · -- white: `T_e(y) = σ'⁻¹(ȳ)` and `σ'⁻¹ = (τ⁻¹)_{H'}`
    rw [turn_of_white hzb' (by rw [contractEdge_colour, hzc, hc]), contractEdge_rot,
      inducedRotationPerm, ← Perm.inv_def, ← firstReturnPerm_inv, coe_firstReturnPerm]
    have hconj : swap d (G.inv d) * (G.rot * swap d (G.inv d))⁻¹ * (swap d (G.inv d))⁻¹ =
        G.rot⁻¹ * swap d (G.inv d) := by
      rw [mul_inv_rev, swap_inv, ← mul_assoc, swap_mul_self, one_mul]
    rw [← coe_firstReturn_conj (ρ := swap d (G.inv d)) (fun x => ?_) (fun x hx => ?_), hconj]
    · refine (coe_firstReturn_eq_of_eqOn_compl ?_ fun x hx => ?_).symm
      · rw [hTy, turn_of_white hzb (hzc.trans hc), Perm.mul_apply, hzs, Perm.inv_def]
      · rw [IsPlabicGraph.tripEquiv_apply, tripMap_apply,
          turn_of_white (hxb x hx) ((hxc x hx).trans hc), Perm.mul_apply,
          swap_apply_eq_inv_of_notMem_compl_pair hinv hx, Perm.inv_def]
    · rw [mem_compl_pair_iff, mem_compl_pair_iff, Ne, Ne, Ne, Ne, swap_apply_eq_iff,
        swap_apply_eq_iff, swap_apply_left, swap_apply_right]
      tauto
    · exact swap_apply_of_mem_compl_pair hx
  · -- black: `T_e(y) = σ'(ȳ) = τ_{H'}(ȳ)`
    rw [turn_of_black hzb' (by rw [contractEdge_colour, hzc, hc]), contractEdge_rot,
      coe_inducedRotationPerm, inducedRotation]
    refine (coe_firstReturn_eq_of_eqOn_compl ?_ fun x hx => ?_).symm
    · rw [hTy, turn_of_black hzb (hzc.trans hc), Perm.mul_apply, hzs]
    · rw [IsPlabicGraph.tripEquiv_apply, tripMap_apply,
        turn_of_black (hxb x hx) ((hxc x hx).trans hc), Perm.mul_apply,
        swap_apply_eq_inv_of_notMem_compl_pair hinv hx]

/-- At an internal vertex, a dart fixed by the turn is fixed by the rotation. -/
theorem rot_eq_self_of_turn_eq_self {e : H} (hb : ¬G.IsBoundaryVertex (G.vertexOf e))
    (h : G.turn e = e) : G.rot e = e := by
  cases hc : G.colour e
  · rw [turn_of_white hb hc, Equiv.symm_apply_eq] at h
    exact h.symm
  · rwa [turn_of_black hb hc] at h

/-- Every orbit of the trip map of `G` meets `H' = H \ {d, d̄}`. -/
theorem exists_sameCycle_tripEquiv_mem (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
    (x : H) : ∃ y ∈ (({d, G.inv d} : Set H)ᶜ : Set H), hG.tripEquiv.SameCycle x y := by
  have hinv := hG.inv_involutive
  by_cases hx : x ∈ (({d, G.inv d} : Set H)ᶜ : Set H)
  · exact ⟨x, hx, SameCycle.refl _ _⟩
  have hT : ∀ x, hG.tripEquiv.SameCycle x (G.tripMap x) := fun x =>
    sameCycle_apply_right.2 (SameCycle.refl _ _)
  have hstep : ∀ e, e ∉ (({d, G.inv d} : Set H)ᶜ : Set H) →
      G.tripMap e ∈ (({d, G.inv d} : Set H)ᶜ : Set H) ∨ G.tripMap e = G.inv e := by
    intro e he'
    refine or_iff_not_imp_left.2 fun h => ?_
    have hmem : G.tripMap e ∈ G.vertexOf (G.inv e) := turn_mem_vertexOf _
    rcases eq_or_eq_of_notMem_compl_pair he' with rfl | rfl <;>
      rcases eq_or_eq_of_notMem_compl_pair h with h1 | h1
    · rw [h1] at hmem
      exact absurd (G.vertexOf_eq_of_mem hmem) he.vertexOf_ne
    · exact h1
    · rw [hinv]
      exact h1
    · rw [h1, hinv] at hmem
      exact absurd (G.vertexOf_eq_of_mem hmem).symm he.vertexOf_ne
  have hfix : ∀ e, e ∉ (({d, G.inv d} : Set H)ᶜ : Set H) → G.turn e = e → G.rot e = e :=
    fun e he' => rot_eq_self_of_turn_eq_self fun hb =>
      he.notMem_of_isBoundaryVertex hb (mem_union_of_notMem_compl_pair he')
  have hinv' : ∀ e, e ∉ (({d, G.inv d} : Set H)ᶜ : Set H) →
      G.inv e ∉ (({d, G.inv d} : Set H)ᶜ : Set H) := fun e he' h =>
    he' ((apply_mem_compl_pair_iff hinv d e).1 h)
  rcases hstep x hx with h | h
  · exact ⟨_, h, hT x⟩
  rcases hstep (G.inv x) (hinv' x hx) with h' | h'
  · exact ⟨_, h', (h ▸ hT x : hG.tripEquiv.SameCycle x (G.inv x)).trans (hT _)⟩
  -- both `T x = x̄` and `T x̄ = x`: then `σ` fixes `d` and `d̄`
  rw [hinv] at h'
  have r1 := hfix (G.inv x) (hinv' x hx) (by rwa [tripMap_apply] at h)
  have r2 := hfix x hx (by rwa [tripMap_apply, hinv] at h')
  have hboth : G.rot d = d ∧ G.rot (G.inv d) = G.inv d := by
    rcases eq_or_eq_of_notMem_compl_pair hx with rfl | rfl
    · exact ⟨r2, r1⟩
    · rw [hinv] at r1
      exact ⟨r1, r2⟩
  exact (rot_ne_or_rot_inv_ne hG he).elim (absurd hboth.1) (absurd hboth.2)

/-- If `{d, d̄}` is an edge of the plabic graph `G` whose endpoints are distinct internal vertices
of the same colour, then the contraction of `G` along `{d, d̄}` has a roundtrip if and only if `G`
has one. -/
@[cluster_algebras "lem_edge_contraction_roundtrip"]
theorem IsPlabicGraph.hasRoundtrip_contractEdge_iff (hG : G.IsPlabicGraph)
    (he : G.IsContractibleEdge d) : (G.contractEdge d hleg).HasRoundtrip ↔ G.HasRoundtrip := by
  have hGe := hG.contractEdge (hleg := hleg) he
  have hL : {z | z ∈ G.bdry ∨ G.IsLeg z} ⊆ (({d, G.inv d} : Set H)ᶜ : Set H) := by
    rintro z (hz | ⟨j, rfl⟩)
    exacts [he.mem_of_mem_bdry hz, hleg j]
  have hT : firstReturnPerm hG.tripEquiv (({d, G.inv d} : Set H)ᶜ : Set H) = hGe.tripEquiv := by
    ext y
    rw [coe_firstReturnPerm, IsPlabicGraph.tripEquiv_apply, coe_contractEdge_tripMap hG he]
  have hmem : ∀ z : (({d, G.inv d} : Set H)ᶜ : Set H),
      z ∈ {z | z ∈ (G.contractEdge d hleg).bdry ∨ (G.contractEdge d hleg).IsLeg z} ↔
        (z : H) ∈ {z | z ∈ G.bdry ∨ G.IsLeg z} := by
    intro z
    simp only [Set.mem_setOf_eq, mem_contractEdge_bdry, IsLeg, Subtype.ext_iff,
      coe_contractEdge_leg]
  rw [hGe.hasRoundtrip_iff_exists_forall_sameCycle, hG.hasRoundtrip_iff_exists_forall_sameCycle,
    exists_forall_sameCycle_notMem_iff hG.tripEquiv hL (exists_sameCycle_tripEquiv_mem hG he),
    hT]
  simp_rw [hmem]

end Roundtrip

end PlabicData

end ClusterAlgebras

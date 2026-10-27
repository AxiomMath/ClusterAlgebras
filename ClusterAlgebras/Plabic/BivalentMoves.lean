/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BivalentRemoval
public import ClusterAlgebras.Plabic.PlabicQuiver
public import ClusterAlgebras.Plabic.SquareTrips

/-!
# Removing a bivalent vertex: the quiver and the roundtrips

Let `G = (H, d ↦ d̄, σ, B, κ, β)` be a plabic graph and `v = {d₁, d₂}` an internal vertex with
`d₂ = σ d₁` and `d̄₁ ≠ d₂`, and let `G_v` be the removal of `v`, with darts `H' = H \ {d₁, d₂}`.
Write `x_i = d̄_i`.

*The quiver.* The bijection `Ψ(f) = f ∩ H'` from the faces of `G` to the faces of `G_v` matches the
boundary faces. Every dart `x ∈ H'` has the same vertex and colour in `G` and `G_v`, and its two
faces in `G_v` are the images under `Ψ` of its two faces in `G`: for `x ∉ {x₁, x₂}` its partner is
unchanged, and the new partner `x₂` of `x₁` lies on the face `φ(x₂) = d₁ = x̄₁` of `G`, and
symmetrically. The two deleted darts `d₁`, `d₂` lie at the internal vertex `v`, with faces
`(f(d₁), f(x₁))` and `(f(d₂), f(x₂)) = (f(x₁), f(d₁))`, so they contribute equally to
`ψ_G(f, f')` and `ψ_G(f', f)`, which cancels in the difference. By the criterion for an isomorphism
of quivers of plabic graphs, `Ψ` is an isomorphism `Q(G) → Q(G_v)`.

*Roundtrips.* The trip map `T` of `G` sends `x₁` to `d₂` and `d₂` to a dart of `H'`, and
symmetrically for `x₂`; away from `x₁, x₂` the trip maps of `G` and `G_v` agree. So the trip map of
`G_v` is the first-return map of `T` to `H'`. Since `T` maps `d₁`, `d₂` into `H'`, every orbit of
`T` meets `H'`, and `T` has an orbit avoiding the legs if and only if the trip map of `G_v` does.

## Main results

* `ClusterAlgebras.PlabicData.exists_quiverIso_bivalentRemoval`: `f ↦ f ∩ H'` is an isomorphism
  `Q(G) → Q(G_v)`.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.hasRoundtrip_bivalentRemoval_iff`: `G` has a
  roundtrip if and only if `G_v` has one.
* `ClusterAlgebras.PlabicData.coe_bivalentRemoval_tripMap`: the trip map of `G_v` is the first
  return to `H'` of the trip map of `G`.
* `ClusterAlgebras.PlabicData.bijOn_faces_bivalentRemoval`: `f ↦ f ∩ H'` matches the faces.

## Implementation notes

* As in `ClusterAlgebras.Plabic.BivalentRemoval`, the darts of `G_v` form the subtype
  `({d₁, σ d₁} : Set H)ᶜ` of `H`, and `f ∩ H'` is `Finset.subtype`.
* The trip maps are the permutations `IsPlabicGraph.tripEquiv` of all darts, which preserve `B`;
  a roundtrip is an orbit avoiding the darts that are in `B` or are legs, and these lie in `H'`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm Function

/-- An element lies outside the complement of `{a, c}` iff it is `a` or `c`. -/
theorem notMem_compl_pair_iff {α : Type*} {a c x : α} :
    x ∉ ({a, c}ᶜ : Set α) ↔ x = a ∨ x = c := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_not]

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b} {d : H}

/-! ### The darts of the removed vertex -/

namespace IsBivalentRemovable

variable (hd : G.IsBivalentRemovable d)

include hd

/-- At `v`, the turn sends `d₁` to `d₂`, whatever the colour of `v`. -/
theorem turn_eq_rot : G.turn d = G.rot d := by
  cases hc : G.colour d
  · rw [turn_of_white hd.not_isBoundaryVertex hc, Equiv.symm_apply_eq, hd.rot_rot]
  · rw [turn_of_black hd.not_isBoundaryVertex hc]

/-- At `v`, the turn sends `d₂` to `d₁`, whatever the colour of `v`. -/
theorem turn_rot : G.turn (G.rot d) = d := by
  have hb : ¬G.IsBoundaryVertex (G.vertexOf (G.rot d)) := by
    rw [G.vertexOf_rot]
    exact hd.not_isBoundaryVertex
  cases hc : G.colour (G.rot d)
  · rw [turn_of_white hb hc, Equiv.symm_apply_apply]
  · rw [turn_of_black hb hc, hd.rot_rot]

/-- The turn of a dart of `H'` lies in `H'`. -/
theorem turn_mem {z : H} (hz : z ∈ ({d, G.rot d}ᶜ : Set H)) :
    G.turn z ∈ ({d, G.rot d}ᶜ : Set H) :=
  mem_of_sameCycle_rot_bivalentRemoval hd hz ((RotationSystem.mem_vertexOf _).1
    (turn_mem_vertexOf z))

end IsBivalentRemovable

/-! ### The quiver -/

section Quiver

variable (hG : G.IsPlabicGraph) (hd : G.IsBivalentRemovable d)

include hG in
/-- The partner of `d` lies on the face of `G` of `σ d`. -/
theorem sameCycle_facePerm_inv_rot_self : G.facePerm.SameCycle (G.inv d) (G.rot d) := by
  have := sameCycle_apply_right.2 (SameCycle.refl G.facePerm (G.inv d))
  rwa [RotationSystem.facePerm_apply, hG.inv_involutive] at this

include hG hd in
/-- The partner of `σ d` lies on the face of `G` of `d`. -/
theorem sameCycle_facePerm_inv_rot_rot : G.facePerm.SameCycle (G.inv (G.rot d)) d := by
  have := sameCycle_apply_right.2 (SameCycle.refl G.facePerm (G.inv (G.rot d)))
  rwa [RotationSystem.facePerm_apply, hG.inv_involutive, hd.rot_rot] at this

include hG hd in
/-- The partner of a dart `y ∈ H'` in the removal lies on the face of `G` of its partner in `G`. -/
theorem sameCycle_facePerm_inv_bivalentRemoval_inv (y : ({d, G.rot d}ᶜ : Set H)) :
    G.facePerm.SameCycle (G.inv y) ((G.bivalentRemoval hG hd).inv y : H) := by
  by_cases h₁ : (y : H) = G.inv d
  · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd h₁, h₁, hG.inv_involutive]
    exact (sameCycle_facePerm_inv_rot_rot hG hd).symm
  by_cases h₂ : (y : H) = G.inv (G.rot d)
  · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂, h₂, hG.inv_involutive]
    exact (sameCycle_facePerm_inv_rot_self hG).symm
  rw [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂]

/-- The face to the right of a dart of the removal is the trace of its face in `G`. -/
theorem bivalentRemoval_rightFace (y : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).rightFace y =
      (G.rightFace y).subtype (· ∈ ({d, G.rot d}ᶜ : Set H)) :=
  bivalentRemoval_faceOf hG hd y

/-- The face to the left of a dart of the removal is the trace of its face in `G`. -/
theorem bivalentRemoval_leftFace (y : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).leftFace y =
      (G.leftFace y).subtype (· ∈ ({d, G.rot d}ᶜ : Set H)) := by
  rw [DiskMap.leftFace, DiskMap.leftFace, bivalentRemoval_faceOf,
    G.faceOf_eq_faceOf_iff.2 (sameCycle_facePerm_inv_bivalentRemoval_inv hG hd y)]

/-- A dart of the removal is at an internal vertex of colour `s` iff it is so in `G`. -/
theorem isInternalOfColour_bivalentRemoval_iff (y : ({d, G.rot d}ᶜ : Set H)) (s : Shade) :
    (G.bivalentRemoval hG hd).IsInternalOfColour y s ↔ G.IsInternalOfColour y s := by
  rw [IsInternalOfColour, IsInternalOfColour, isBoundaryVertex_bivalentRemoval_vertexOf_iff,
    bivalentRemoval_colour]

/-- **Faces under the removal of a bivalent vertex**: `f ↦ f ∩ H'` is a bijection from the faces
of `G` onto the faces of the removal. -/
theorem bijOn_faces_bivalentRemoval :
    Set.BijOn (fun f : Finset H => f.subtype (· ∈ ({d, G.rot d}ᶜ : Set H)))
      G.faces (G.bivalentRemoval hG hd).faces := by
  have hb := bijOn_faceOrbits_bivalentRemoval hG hd
  have hext := bivalentRemoval_exterior hG hd
  refine ⟨fun f hf => ?_, fun f hf f' hf' h => ?_, fun g hg => ?_⟩
  · obtain ⟨hfe, hfΦ⟩ := (DiskMap.mem_faces _).1 (mem_coe.1 hf)
    refine mem_coe.2 ((DiskMap.mem_faces _).2 ⟨fun h => hfe ?_, mem_coe.1 (hb.mapsTo
      (mem_coe.2 hfΦ))⟩)
    rw [hext] at h
    exact hb.injOn (mem_coe.2 hfΦ) (mem_coe.2 hG.exterior_mem_faceOrbits) h
  · exact hb.injOn (mem_coe.2 ((DiskMap.mem_faces _).1 (mem_coe.1 hf)).2)
      (mem_coe.2 ((DiskMap.mem_faces _).1 (mem_coe.1 hf')).2) h
  · obtain ⟨hge, hgΦ⟩ := (DiskMap.mem_faces _).1 (mem_coe.1 hg)
    obtain ⟨f, hf, rfl⟩ := hb.surjOn (mem_coe.2 hgΦ)
    refine ⟨f, mem_coe.2 ((DiskMap.mem_faces _).2 ⟨fun h => hge ?_, mem_coe.1 hf⟩), rfl⟩
    simp only [h, hext]

/-- The darts of the removal counted by its dart balance at `(f ∩ H', f' ∩ H')` are the darts of
`H'` counted by the dart balance of `G` at `(f, f')`. -/
theorem card_filter_bivalentRemoval (s : Shade) {f f' : Finset H} (hf : f ∈ G.faceOrbits)
    (hf' : f' ∈ G.faceOrbits) :
    #{x | x ∉ (G.bivalentRemoval hG hd).bdry ∧ (G.bivalentRemoval hG hd).IsInternalOfColour x s ∧
      (G.bivalentRemoval hG hd).rightFace x = f.subtype (· ∈ ({d, G.rot d}ᶜ : Set H)) ∧
      (G.bivalentRemoval hG hd).leftFace x = f'.subtype (· ∈ ({d, G.rot d}ᶜ : Set H))} =
    #{x | (x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f ∧ G.leftFace x = f') ∧
      x ∈ ({d, G.rot d}ᶜ : Set H)} := by
  have hb := bijOn_faceOrbits_bivalentRemoval hG hd
  have hinj : ∀ {g g' : Finset H}, g ∈ G.faceOrbits → g' ∈ G.faceOrbits →
      (g.subtype (· ∈ ({d, G.rot d}ᶜ : Set H)) =
        g'.subtype (· ∈ ({d, G.rot d}ᶜ : Set H)) ↔ g = g') :=
    fun hg hg' => ⟨fun h => hb.injOn (mem_coe.2 hg) (mem_coe.2 hg') h, fun h => h ▸ rfl⟩
  have key : ∀ a : ({d, G.rot d}ᶜ : Set H),
      (a ∉ (G.bivalentRemoval hG hd).bdry ∧ (G.bivalentRemoval hG hd).IsInternalOfColour a s ∧
        (G.bivalentRemoval hG hd).rightFace a = f.subtype (· ∈ ({d, G.rot d}ᶜ : Set H)) ∧
        (G.bivalentRemoval hG hd).leftFace a = f'.subtype (· ∈ ({d, G.rot d}ᶜ : Set H))) ↔
      ((a : H) ∉ G.bdry ∧ G.IsInternalOfColour a s ∧ G.rightFace a = f ∧ G.leftFace a = f') := by
    intro a
    rw [mem_bivalentRemoval_bdry, isInternalOfColour_bivalentRemoval_iff,
      bivalentRemoval_rightFace, bivalentRemoval_leftFace,
      hinj (RotationSystem.faceOf_mem_faceOrbits _ _) hf,
      hinj (RotationSystem.faceOf_mem_faceOrbits _ _) hf']
  refine card_bij (fun a _ => (a : H)) (fun a ha => ?_) (fun a _ a' _ h => Subtype.ext h)
    (fun x hx => ?_)
  · rw [mem_filter] at ha ⊢
    exact ⟨mem_univ _, (key a).1 ha.2, a.2⟩
  · rw [mem_filter] at hx
    exact ⟨⟨x, hx.2.2⟩, mem_filter.2 ⟨mem_univ _, (key _).2 hx.2.1⟩, rfl⟩

omit [Fintype H] in
/-- The darts counted by the dart balance of `G` split into those of `H'` and those of `v`. -/
theorem card_filter_eq_add_card_filter_bivalent [Fintype H] (s : Shade) (f f' : Finset H) :
    #{x | x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f ∧ G.leftFace x = f'} =
      #{x | (x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f ∧ G.leftFace x = f') ∧
        x ∈ ({d, G.rot d}ᶜ : Set H)} +
      #{x | (x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f ∧ G.leftFace x = f') ∧
        x ∉ ({d, G.rot d}ᶜ : Set H)} := by
  rw [← card_filter_add_card_filter_not (s := filter _ univ)
    (· ∈ ({d, G.rot d}ᶜ : Set H)), filter_filter, filter_filter]

include hG hd in
/-- The darts `d₁`, `d₂` of `v` contribute equally to the dart balances at `(f, f')` and at
`(f', f)`: exchanging them exchanges the faces on their two sides. -/
theorem card_filter_notMem_comm_bivalent (s : Shade) (f f' : Finset H) :
    #{x | (x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f ∧ G.leftFace x = f') ∧
        x ∉ ({d, G.rot d}ᶜ : Set H)} =
      #{x | (x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f' ∧ G.leftFace x = f) ∧
        x ∉ ({d, G.rot d}ᶜ : Set H)} := by
  have hr : G.rightFace (G.rot d) = G.leftFace d := by
    rw [DiskMap.rightFace, DiskMap.leftFace, G.faceOf_eq_faceOf_iff]
    exact (sameCycle_facePerm_inv_rot_self hG).symm
  have hl : G.leftFace (G.rot d) = G.rightFace d := by
    rw [DiskMap.rightFace, DiskMap.leftFace, G.faceOf_eq_faceOf_iff]
    exact sameCycle_facePerm_inv_rot_rot hG hd
  have hcol : G.colour (G.rot d) = G.colour d := hG.colour_rot d hd.not_isBoundaryVertex
  have hint : G.IsInternalOfColour (G.rot d) s ↔ G.IsInternalOfColour d s := by
    rw [IsInternalOfColour, IsInternalOfColour, G.vertexOf_rot, hcol]
  have hsw : ∀ x, swap d (G.rot d) x ∉ ({d, G.rot d}ᶜ : Set H) ↔
      x ∉ ({d, G.rot d}ᶜ : Set H) := by
    intro x
    rw [notMem_compl_pair_iff, notMem_compl_pair_iff, swap_apply_eq_iff, swap_apply_eq_iff,
      swap_apply_left, swap_apply_right]
    tauto
  refine card_equiv (swap d (G.rot d)) fun x => ?_
  simp only [mem_filter, mem_univ, true_and]
  by_cases hx : x ∈ ({d, G.rot d}ᶜ : Set H)
  · have hx' : swap d (G.rot d) x ∈ ({d, G.rot d}ᶜ : Set H) :=
      of_not_not fun h => (hsw x).1 h hx
    simp only [hx, hx', not_true_eq_false, and_false]
  rcases notMem_compl_pair_iff.1 hx with rfl | rfl
  · rw [swap_apply_left, hr, hl, hint]
    simp only [hd.notMem_bdry, hd.rot_notMem_bdry, not_false_eq_true, true_and]
    exact ⟨fun ⟨⟨h1, h2, h3⟩, _⟩ => ⟨⟨h1, h3, h2⟩, notMem_compl_pair_iff.2 (Or.inr rfl)⟩,
      fun ⟨⟨h1, h2, h3⟩, _⟩ => ⟨⟨h1, h3, h2⟩, hx⟩⟩
  · rw [swap_apply_right, ← hr, ← hl, ← hint]
    simp only [hd.notMem_bdry, hd.rot_notMem_bdry, not_false_eq_true, true_and]
    exact ⟨fun ⟨⟨h1, h2, h3⟩, _⟩ => ⟨⟨h1, h3, h2⟩, notMem_compl_pair_iff.2 (Or.inl rfl)⟩,
      fun ⟨⟨h1, h2, h3⟩, _⟩ => ⟨⟨h1, h3, h2⟩, hx⟩⟩

/-- **Removing a bivalent vertex does not change the quiver**: if `v = {d₁, d₂}` is an internal
vertex of the plabic graph `G` with `d₂ = σ d₁` and `d̄₁ ≠ d₂`, then `f ↦ f ∩ H'`, where
`H' = H \ {d₁, d₂}`, is an isomorphism from `Q(G)` to the quiver of the removal of `v`. -/
@[cluster_algebras "lem_bivalent_removal_quiver"]
theorem exists_quiverIso_bivalentRemoval :
    ∃ e : G.quiver.Iso (G.bivalentRemoval hG hd).quiver, ∀ f,
      ((e.equiv f : (G.bivalentRemoval hG hd).faces) : Finset ({d, G.rot d}ᶜ : Set H)) =
        (f : Finset H).subtype (· ∈ ({d, G.rot d}ᶜ : Set H)) := by
  have hb := bijOn_faces_bivalentRemoval hG hd
  let Ψ : G.faces ≃ (G.bivalentRemoval hG hd).faces := hb.equiv _
  have hΨ : ∀ f, ((Ψ f : (G.bivalentRemoval hG hd).faces) : Finset ({d, G.rot d}ᶜ : Set H)) =
      (f : Finset H).subtype (· ∈ ({d, G.rot d}ᶜ : Set H)) := fun _ => rfl
  have hfo : ∀ f : G.faces, (f : Finset H) ∈ G.faceOrbits := fun f =>
    ((DiskMap.mem_faces _).1 f.2).2
  have hbd : ∀ f, ((Ψ f : (G.bivalentRemoval hG hd).faces) : Finset ({d, G.rot d}ᶜ : Set H)) ∈
      (G.bivalentRemoval hG hd).boundaryFaces ↔ (f : Finset H) ∈ G.boundaryFaces := by
    intro f
    rw [hΨ, DiskMap.mem_boundaryFaces, DiskMap.mem_boundaryFaces,
      iff_true_intro (show _ ∈ (G.bivalentRemoval hG hd).faces from hb.mapsTo f.2),
      iff_true_intro f.2, true_and, true_and, not_iff_not, disjoint_left, disjoint_left]
    exact ⟨fun h a ha haB => h (show (⟨a, hd.mem_of_mem_bdry haB⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ _
      from mem_subtype.2 ha) ((mem_bivalentRemoval_bdry hG hd).2 haB),
      fun h a ha haB => h (mem_subtype.1 ha) ((mem_bivalentRemoval_bdry hG hd).1 haB)⟩
  have hψ : ∀ f f' : G.faces, f ≠ f' →
      ¬((f : Finset H) ∈ G.boundaryFaces ∧ (f' : Finset H) ∈ G.boundaryFaces) →
      G.dartBalance f f' - G.dartBalance f' f =
        (G.bivalentRemoval hG hd).dartBalance (Ψ f) (Ψ f') -
          (G.bivalentRemoval hG hd).dartBalance (Ψ f') (Ψ f) := by
    intro f f' _ _
    rw [dartBalance, dartBalance, dartBalance, dartBalance, hΨ, hΨ,
      card_filter_bivalentRemoval hG hd _ (hfo f) (hfo f'),
      card_filter_bivalentRemoval hG hd _ (hfo f) (hfo f'),
      card_filter_bivalentRemoval hG hd _ (hfo f') (hfo f),
      card_filter_bivalentRemoval hG hd _ (hfo f') (hfo f),
      card_filter_eq_add_card_filter_bivalent (d := d) .white (f : Finset H) f',
      card_filter_eq_add_card_filter_bivalent (d := d) .black (f : Finset H) f',
      card_filter_eq_add_card_filter_bivalent (d := d) .white (f' : Finset H) f,
      card_filter_eq_add_card_filter_bivalent (d := d) .black (f' : Finset H) f,
      card_filter_notMem_comm_bivalent hG hd .white (f : Finset H) f',
      card_filter_notMem_comm_bivalent hG hd .black (f : Finset H) f']
    push_cast
    ring
  obtain ⟨e, he'⟩ := exists_quiverIso_of_dartBalance hG.toIsDiskMap
    (isPlabicGraph_bivalentRemoval hG hd).toIsDiskMap Ψ hbd hψ
  exact ⟨e, fun f => by rw [he', hΨ]⟩

end Quiver

/-! ### Roundtrips -/

section Roundtrip

variable (hG : G.IsPlabicGraph) (hd : G.IsBivalentRemovable d)

/-- The inverse rotation of the removal is the restriction of `σ⁻¹`. -/
theorem coe_bivalentRemoval_rot_symm (y : ({d, G.rot d}ᶜ : Set H)) :
    ((G.bivalentRemoval hG hd).rot.symm y : H) = G.rot.symm y :=
  rfl

/-- At a dart of `H'`, the turn of the removal is the turn of `G`. -/
theorem coe_bivalentRemoval_turn (z : ({d, G.rot d}ᶜ : Set H)) :
    ((G.bivalentRemoval hG hd).turn z : H) = G.turn z := by
  have hb := isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd z
  by_cases hzb : G.IsBoundaryVertex (G.vertexOf z)
  · rw [turn_of_isBoundaryVertex (hb.2 hzb), turn_of_isBoundaryVertex hzb]
  have hzb' : ¬(G.bivalentRemoval hG hd).IsBoundaryVertex
      ((G.bivalentRemoval hG hd).vertexOf z) := fun h => hzb (hb.1 h)
  cases hc : G.colour z
  · rw [turn_of_white hzb' (by rw [bivalentRemoval_colour, hc]), turn_of_white hzb hc,
      coe_bivalentRemoval_rot_symm]
  · rw [turn_of_black hzb' (by rw [bivalentRemoval_colour, hc]), turn_of_black hzb hc,
      coe_bivalentRemoval_rot]

/-- **The trip map of the removal is a first return.** The trip map of the removal of a bivalent
vertex `v = {d₁, d₂}` is the first-return map to `H' = H \ {d₁, d₂}` of the trip map of `G`. -/
theorem coe_bivalentRemoval_tripMap (y : ({d, G.rot d}ᶜ : Set H)) :
    ((G.bivalentRemoval hG hd).tripMap y : H) =
      firstReturn hG.tripEquiv ({d, G.rot d}ᶜ : Set H) y := by
  have hinv := hG.inv_involutive
  have hT : ∀ x, hG.tripEquiv x = G.turn (G.inv x) := fun _ => rfl
  rw [tripMap_apply, coe_bivalentRemoval_turn]
  by_cases h₁ : (y : H) = G.inv d
  · -- `T(x₁) = d₂ ∉ H'` and `T(d₂) = R(x₂)`
    have e1 : hG.tripEquiv y = G.rot d := by rw [hT, h₁, hinv, hd.turn_eq_rot]
    have e2 : (hG.tripEquiv ^ 2) (y : H) = G.turn (G.inv (G.rot d)) := by
      rw [pow_two, Perm.mul_apply, e1, hT]
    rw [coe_firstReturn_of_pow two_pos ?_ ?_, e2, coe_bivalentRemoval_inv_of_eq_inv hG hd h₁]
    · rw [e2]
      exact hd.turn_mem (hd.inv_rot_mem hG)
    · intro j hj hj2
      obtain rfl : j = 1 := by omega
      rw [pow_one, e1]
      exact notMem_compl_pair_iff.2 (Or.inr rfl)
  by_cases h₂ : (y : H) = G.inv (G.rot d)
  · -- `T(x₂) = d₁ ∉ H'` and `T(d₁) = R(x₁)`
    have e1 : hG.tripEquiv y = d := by rw [hT, h₂, hinv, hd.turn_rot]
    have e2 : (hG.tripEquiv ^ 2) (y : H) = G.turn (G.inv d) := by
      rw [pow_two, Perm.mul_apply, e1, hT]
    rw [coe_firstReturn_of_pow two_pos ?_ ?_, e2, coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂]
    · rw [e2]
      exact hd.turn_mem (hd.inv_mem hG)
    · intro j hj hj2
      obtain rfl : j = 1 := by omega
      rw [pow_one, e1]
      exact notMem_compl_pair_iff.2 (Or.inl rfl)
  rw [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂, coe_firstReturn_of_apply_mem, hT]
  rw [hT]
  exact hd.turn_mem (((coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂) ▸
    ((G.bivalentRemoval hG hd).inv y).2 : G.inv y ∈ ({d, G.rot d}ᶜ : Set H)))

include hd in
/-- Every orbit of the trip map of `G` meets `H' = H \ {d₁, d₂}`. -/
theorem exists_sameCycle_tripEquiv_mem_bivalentRemoval (x : H) :
    ∃ y ∈ ({d, G.rot d}ᶜ : Set H), hG.tripEquiv.SameCycle x y := by
  by_cases hx : x ∈ ({d, G.rot d}ᶜ : Set H)
  · exact ⟨x, hx, SameCycle.refl _ _⟩
  refine ⟨G.turn (G.inv x), hd.turn_mem ?_, sameCycle_apply_right.2 (SameCycle.refl _ _)⟩
  rcases notMem_compl_pair_iff.1 hx with rfl | rfl
  · exact hd.inv_mem hG
  · exact hd.inv_rot_mem hG

/-- **Removing a bivalent vertex keeps roundtrips**: if `v = {d₁, d₂}` is an internal vertex of the
plabic graph `G` with `d₂ = σ d₁` and `d̄₁ ≠ d₂`, then `G` has a roundtrip if and only if the
removal of `v` has one. -/
@[cluster_algebras "lem_bivalent_removal_roundtrip"]
theorem IsPlabicGraph.hasRoundtrip_bivalentRemoval_iff :
    G.HasRoundtrip ↔ (G.bivalentRemoval hG hd).HasRoundtrip := by
  symm
  have hGv := isPlabicGraph_bivalentRemoval hG hd
  have hL : {z | z ∈ G.bdry ∨ G.IsLeg z} ⊆ ({d, G.rot d}ᶜ : Set H) := by
    rintro z (hz | ⟨j, rfl⟩)
    · exact hd.mem_of_mem_bdry hz
    · exact hd.leg_mem hG j
  have h1 := exists_forall_sameCycle_notMem_iff hG.tripEquiv hL
    (exists_sameCycle_tripEquiv_mem_bivalentRemoval hG hd)
  have hT : firstReturnPerm hG.tripEquiv ({d, G.rot d}ᶜ : Set H) = hGv.tripEquiv := by
    ext y
    rw [coe_firstReturnPerm, IsPlabicGraph.tripEquiv_apply, coe_bivalentRemoval_tripMap hG hd]
  have hmem : ∀ z : ({d, G.rot d}ᶜ : Set H),
      z ∈ {z | z ∈ (G.bivalentRemoval hG hd).bdry ∨ (G.bivalentRemoval hG hd).IsLeg z} ↔
        (z : H) ∈ {z | z ∈ G.bdry ∨ G.IsLeg z} := by
    intro z
    simp only [Set.mem_setOf_eq, mem_bivalentRemoval_bdry, IsLeg, Subtype.ext_iff,
      coe_bivalentRemoval_leg]
  rw [hGv.hasRoundtrip_iff_exists_forall_sameCycle, hG.hasRoundtrip_iff_exists_forall_sameCycle,
    h1, hT]
  simp_rw [hmem]

end Roundtrip

end PlabicData

end ClusterAlgebras

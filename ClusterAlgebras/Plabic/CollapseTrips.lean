/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.TreeCollapse

/-!
# Trips after collapsing a tree

Let `G` be a plabic graph without roundtrip and `T = (v, W)` a rooted tree of `G` with interval
`(a₁, …, a_k)`, and let `G' = G/{(v, W, c)}` be the collapse of `T` (`PlabicData.collapse`). The
darts of `G'` are darts of `G`, and away from the tree nothing changes: a vertex of `G` which is
neither the root nor in `W` is a vertex of `G'` with the same darts, kind and colour.

If the root `v` is internal, the trip map `T'` of `G'` is the first-return map of the trip map `T`
of `G` to the darts `H' \ B` of `G'`: a trip of `G` that enters the tree at `v` runs through all of
its darts and comes back to `v` (`RootedTree.exists_tripChain`), while in `G'` it turns at `v°`
directly. Hence the one-way trips of `G'` are those of `G` with the darts of the tree deleted. If
the root is a boundary vertex `β(y₀)`, the darts of the tree form the trip of the leg `g_{y₀}`, and
every other one-way trip of `G'` is the corresponding one-way trip of `G`.

In both cases a set of darts of `G'` pendant at a vertex, on which the trip from `i` is symmetric,
lifts to such a set of darts of `G`.

## Main results

* `ClusterAlgebras.PlabicData.RootedTree.coe_tripMap_collapse`: for an internal root, the trip
  map of `G'` is the first return of the trip map of `G` to `H' \ B`.
* `ClusterAlgebras.PlabicData.RootedTree.IsCollapsibleOfColour.mem_oneWayTrip_collapse_iff`: for
  an internal root, a dart of `G'` off `B` lies on the one-way trip from `i` in `G'` if and only if
  it does in `G`.
* `ClusterAlgebras.PlabicData.RootedTree.coe_iterate_tripMap_collapse_leg`: for a boundary root
  `β(y₀)` and `i ≠ y₀`, `T'ⁿ(g_i) = Tⁿ(g_i)` for all `n`.
* `ClusterAlgebras.PlabicData.RootedTree.IsCollapsibleOfColour.exists_isPendantAt_of_collapse`:
  lifting a pendant set over a collapsed tree with internal root.
* `ClusterAlgebras.PlabicData.RootedTree.exists_isPendantAt_of_collapse_of_eq_bvertex`: lifting a
  pendant set over a collapsed tree with boundary root.

## Implementation notes

* The darts of `G'` form the subtype `G.collapseDarts {(T, c)}` of the darts of `G`, so
  FWZ's identification of a dart of `G'` with a dart of `G` is the coercion. The set `H' \ B`,
  as a set of darts of `G`, is `{x | x ∈ G.collapseDarts {(T, c)} ∧ x ∉ G.bdry}`.
* FWZ's `darts(i)` is the one-way trip `G.oneWayTrip i`; the label `i : Fin b` is
  FWZ's label `i + 1`.
* Superfluous hypotheses are not assumed. `RootedTree.coe_tripMap_collapse` holds for every
  rooted tree with internal root and every colour `c`, collapsible or not.
  `RootedTree.coe_iterate_tripMap_collapse_leg` and
  `RootedTree.exists_isPendantAt_of_collapse_of_eq_bvertex` hold for every rooted tree with root
  `β(y₀)`, and without the hypothesis that `G` has no roundtrip: the darts of the tree are mapped
  into themselves by the trip map, since `T(ḡ_{y₀}) = g_{y₀}`, so a trip which meets them contains
  the leg `g_{y₀}`. A lifted pendant set contains the image of the given one as a set of darts of
  `G`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-! ### Darts of a collapse kept from `G` -/

section Core

variable {𝒯 : Finset (G.RootedTree × Shade)}

/-- At a kept dart, the colour of the collapse is that of `G`. -/
private theorem collapse_colour_of_mem (hG : G.IsPlabicGraph) {x : G.collapseDarts 𝒯}
    (hx : (x : H) ∈ G.collapseCore 𝒯) : (G.collapse 𝒯).colour x = G.colour x := by
  change G.collapseColour 𝒯 x = G.colour x
  rw [collapseColour, dif_neg]
  rintro ⟨p, hp, i, hi, hxi⟩
  exact inv_leg_notMem_collapseCore hG (mem_familyDarts.2 ⟨p, hp, hi⟩) (hxi ▸ hx)

/-- A kept dart lies at a boundary vertex of the collapse if and only if it does in `G`. -/
private theorem collapse_isBoundaryVertex_iff {x : G.collapseDarts 𝒯}
    (hx : (x : H) ∈ G.collapseCore 𝒯) :
    (G.collapse 𝒯).IsBoundaryVertex ((G.collapse 𝒯).vertexOf x) ↔
      G.IsBoundaryVertex (G.vertexOf x) := by
  have hmap := map_collapse_vertexOf_of_mem hx
  constructor
  · rintro ⟨d, hd, hdB⟩
    refine (exists_mem_bdry_filter_vertexOf_iff (𝒯 := 𝒯) (d := (x : H))).1
      ⟨d, ?_, mem_collapse_bdry.1 hdB⟩
    rw [← hmap]
    exact mem_map_of_mem _ hd
  · intro h
    obtain ⟨y, hy, hyB⟩ := (exists_mem_bdry_filter_vertexOf_iff (𝒯 := 𝒯) (d := (x : H))).2 h
    rw [← hmap, mem_map] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨d, hd, mem_collapse_bdry.2 hyB⟩

/-- A kept dart lies at an internal vertex of the collapse if and only if it does in `G`. -/
private theorem collapse_vertexOf_mem_internalVertices_iff {x : G.collapseDarts 𝒯}
    (hx : (x : H) ∈ G.collapseCore 𝒯) :
    (G.collapse 𝒯).vertexOf x ∈ (G.collapse 𝒯).internalVertices ↔
      G.vertexOf x ∈ G.internalVertices := by
  rw [DiskMap.vertexOf_mem_internalVertices, DiskMap.vertexOf_mem_internalVertices,
    collapse_isBoundaryVertex_iff hx]

/-- If `σ x` is kept, the rotation of the collapse sends `x` to `σ x`. -/
private theorem coe_collapse_rot_of_rot_mem {x : G.collapseDarts 𝒯}
    (hx : (x : H) ∈ G.collapseCore 𝒯) (h : G.rot x ∈ G.collapseCore 𝒯) :
    ((G.collapse 𝒯).rot x : H) = G.rot x := by
  rw [coe_collapse_rot_of_mem hx]
  exact coe_firstReturn_of_apply_mem (π := G.rot) (Y := G.collapseCore 𝒯) (y := ⟨x, hx⟩) h

/-- Two kept darts lie at the same vertex of the collapse if and only if they do in `G`. -/
private theorem collapse_vertexOf_eq_iff {x y : G.collapseDarts 𝒯}
    (hx : (x : H) ∈ G.collapseCore 𝒯) (hy : (y : H) ∈ G.collapseCore 𝒯) :
    (G.collapse 𝒯).vertexOf y = (G.collapse 𝒯).vertexOf x ↔
      G.vertexOf (y : H) = G.vertexOf (x : H) := by
  constructor
  · intro h
    have hmem : (y : H) ∈ (G.vertexOf x).filter (· ∈ G.collapseCore 𝒯) := by
      rw [← map_collapse_vertexOf_of_mem hx, ← h]
      exact mem_map_of_mem _ ((G.collapse 𝒯).self_mem_vertexOf y)
    exact G.vertexOf_eq_of_mem (mem_filter.1 hmem).1
  · intro h
    have hmem : (y : H) ∈ ((G.collapse 𝒯).vertexOf x).map (Embedding.subtype _) := by
      rw [map_collapse_vertexOf_of_mem hx, mem_filter, ← h]
      exact ⟨G.self_mem_vertexOf _, hy⟩
    obtain ⟨y', hy', hyy⟩ := mem_map.1 hmem
    rw [Subtype.ext hyy] at hy'
    exact (G.collapse 𝒯).vertexOf_eq_of_mem hy'

/-- A kept dart `e` at the vertex of a kept dart `x` of `G` lies at the vertex of `x` in the
collapse. -/
private theorem mem_collapse_vertexOf {x : G.collapseDarts 𝒯} (hx : (x : H) ∈ G.collapseCore 𝒯)
    {e : H} (he : e ∈ G.vertexOf x) (heK : e ∈ G.collapseCore 𝒯) :
    (⟨e, G.collapseCore_subset 𝒯 heK⟩ : G.collapseDarts 𝒯) ∈ (G.collapse 𝒯).vertexOf x := by
  have h := (collapse_vertexOf_eq_iff (y := ⟨e, G.collapseCore_subset 𝒯 heK⟩) hx heK).2
    (G.vertexOf_eq_of_mem he)
  rw [← h]
  exact (G.collapse 𝒯).self_mem_vertexOf _

end Core

/-! ### Collapsing one tree -/

section OneTree

private theorem mem_familyDarts_singleton {T : G.RootedTree} {c : Shade} {x : H} :
    x ∈ G.familyDarts {(T, c)} ↔ x ∈ T.darts := by
  simp [familyDarts]

private theorem mem_collapseCore_of_notMem {T : G.RootedTree} {c : Shade} {x : H}
    (hx : x ∉ T.darts) : x ∈ G.collapseCore {(T, c)} :=
  Or.inl fun h => hx (mem_familyDarts_singleton.1 h)

/-- If the vertex of `z` carries no dart of `T`, the turn of the collapse at `z` is that of
`G`. -/
private theorem coe_turn_collapse (hG : G.IsPlabicGraph) {T : G.RootedTree} {c : Shade}
    {z : G.collapseDarts {(T, c)}} (hz : ∀ e ∈ G.vertexOf (z : H), e ∉ T.darts) :
    ((G.collapse {(T, c)}).turn z : H) = G.turn z := by
  have hzK : (z : H) ∈ G.collapseCore {(T, c)} :=
    mem_collapseCore_of_notMem (hz _ (G.self_mem_vertexOf _))
  by_cases hb : G.IsBoundaryVertex (G.vertexOf (z : H))
  · rw [turn_of_isBoundaryVertex ((collapse_isBoundaryVertex_iff hzK).2 hb),
      turn_of_isBoundaryVertex hb]
  have hb' : ¬(G.collapse {(T, c)}).IsBoundaryVertex ((G.collapse {(T, c)}).vertexOf z) :=
    fun h => hb ((collapse_isBoundaryVertex_iff hzK).1 h)
  have hcol := collapse_colour_of_mem hG hzK
  cases hc : G.colour (z : H) with
  | black =>
    rw [turn_of_black hb' (hcol.trans hc), turn_of_black hb hc]
    exact coe_collapse_rot_of_rot_mem hzK
      (mem_collapseCore_of_notMem (hz _ (G.rot_mem_vertexOf _)))
  | white =>
    rw [turn_of_white hb' (hcol.trans hc), turn_of_white hb hc]
    have hwK : G.rot.symm (z : H) ∈ G.collapseCore {(T, c)} :=
      mem_collapseCore_of_notMem (hz _ (G.rot_symm_mem_vertexOf _))
    have hw : (G.collapse {(T, c)}).rot ⟨G.rot.symm z, G.collapseCore_subset _ hwK⟩ = z :=
      Subtype.ext (by
        rw [coe_collapse_rot_of_rot_mem hwK (by simpa using hzK)]
        simp)
    rw [(Equiv.symm_apply_eq _).2 hw.symm]

/-- The darts off the tree are closed under the involution. -/
private theorem inv_notMem_darts (hG : G.IsPlabicGraph) {T : G.RootedTree} {x : H}
    (hx : x ∉ T.darts) : G.inv x ∉ T.darts :=
  fun h => hx (by simpa [hG.inv_involutive _] using T.inv_mem_darts hG h)

/-- A dart off the tree, away from the root, lies at a vertex carrying no dart of the tree. -/
private theorem forall_mem_vertexOf_notMem_darts (hG : G.IsPlabicGraph) {T : G.RootedTree}
    {x : H} (hx : x ∉ T.darts) (hr : G.vertexOf x ≠ T.root) :
    ∀ e ∈ G.vertexOf x, e ∉ T.darts := by
  intro e he heD
  have hve := G.vertexOf_eq_of_mem he
  rcases T.vertexOf_mem_or_eq_root hG heD with h | h
  · exact hx (T.mem_darts_of_vertexOf_mem (hve ▸ h))
  · exact hr (hve ▸ h)

/-- If `T(y)` is off the tree, the first return of `y` to `H' \ B` is `T(y)`. -/
private theorem coe_firstReturn_of_tripMap_notMem (hG : G.IsPlabicGraph) {T : G.RootedTree}
    {c : Shade} {y : G.collapseDarts {(T, c)}} (hy : (y : H) ∉ G.bdry)
    (h : G.tripMap y ∉ T.darts) :
    (firstReturn hG.tripEquiv {x | x ∈ G.collapseDarts {(T, c)} ∧ x ∉ G.bdry}
      ⟨y, y.2, hy⟩ : H) = G.tripMap y :=
  coe_firstReturn_of_apply_mem (π := hG.tripEquiv)
    ⟨G.collapseCore_subset _ (mem_collapseCore_of_notMem h),
      fun hB => hy ((tripMap_mem_bdry_iff hG _).1 hB)⟩

section Internal

variable (hG : G.IsPlabicGraph) {T : G.RootedTree} {c : Shade}
  (hroot : ¬G.IsBoundaryVertex T.root)

include hG hroot

/-- For an internal root, no dart of the collapse is a dart of the tree. -/
private theorem notMem_darts_of_mem_collapseDarts {x : H} (hx : x ∈ G.collapseDarts {(T, c)}) :
    x ∉ T.darts := by
  rcases hx with (hx | ⟨i, rfl⟩) | ⟨i, hi, rfl⟩
  · exact fun h => hx (mem_familyDarts_singleton.2 h)
  · exact fun h => T.not_isLeg_of_mem_darts hG hroot h ⟨i, rfl⟩
  · exact absurd (mem_familyDarts_singleton.1 hi)
      fun h => T.not_isLeg_of_mem_darts hG hroot h ⟨i, rfl⟩

/-- For an internal root, every dart of the collapse is kept. -/
private theorem mem_collapseCore_of_internal (x : G.collapseDarts {(T, c)}) :
    (x : H) ∈ G.collapseCore {(T, c)} :=
  mem_collapseCore_of_notMem (notMem_darts_of_mem_collapseDarts hG hroot x.2)

omit hroot in
/-- At an internal root, every dart has the colour of `a₁`. -/
private theorem colour_eq_of_mem_root' (hroot : ¬G.IsBoundaryVertex T.root) {d : H}
    (hd : d ∈ T.root) : G.colour d = G.colour T.intervalStart :=
  hG.colour_eq_of_mem_vertexOf (by rwa [← T.root_eq_vertexOf_intervalStart])
    (by rwa [← T.root_eq_vertexOf_intervalStart])

/-- If `σ x = a₁`, the rotation of the collapse sends `x` to `σ a_k`. -/
private theorem coe_collapse_rot_of_rot_eq_intervalStart {x : G.collapseDarts {(T, c)}}
    (hx : G.rot x = T.intervalStart) :
    ((G.collapse {(T, c)}).rot x : H) = G.rot T.intervalEnd := by
  have hxK := mem_collapseCore_of_internal hG hroot x
  rw [coe_collapse_rot_of_mem hxK]
  have hk := T.one_le_intervalLength
  have hpow : ∀ j, (G.rot ^ (j + 1)) (x : H) = (G.rot ^ j) T.intervalStart := by
    intro j
    rw [pow_succ, Equiv.Perm.mul_apply, hx]
  have hend : (G.rot ^ (T.intervalLength + 1)) (x : H) = G.rot T.intervalEnd := by
    rw [hpow, RootedTree.intervalEnd, ← Equiv.Perm.mul_apply, ← pow_succ',
      Nat.sub_add_cancel hk]
  rw [← hend]
  refine coe_firstReturn_of_pow (by omega)
    (by rw [hend]; exact mem_collapseCore_of_notMem (T.rot_intervalEnd_notMem hG))
    fun j hj hjk hK => ?_
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [hpow] at hK
  exact notMem_darts_of_mem_collapseDarts hG hroot (G.collapseCore_subset _ hK)
    (T.pow_intervalStart_mem_darts (by omega))

/-- If `T(y)` is the entry `s` of the tree, the first return of `y` to `H' \ B` is `T(z)`. -/
private theorem coe_firstReturn_of_tripMap_eq_tripEntry (hR : ¬G.HasRoundtrip) {y : H}
    (hy : y ∈ {x | x ∈ G.collapseDarts {(T, c)} ∧ x ∉ G.bdry})
    (hs : G.tripMap y = T.tripEntry) (hw : G.tripMap T.tripExit ∉ T.darts) :
    (firstReturn hG.tripEquiv {x | x ∈ G.collapseDarts {(T, c)} ∧ x ∉ G.bdry} ⟨y, hy⟩ : H) =
      G.tripMap T.tripExit := by
  obtain ⟨N, -, hX, hN⟩ := T.exists_tripChain hG hR
  have hmemX : ∀ n ≤ N, G.tripMap^[n] T.tripEntry ∈ T.darts := by
    intro n hn
    rw [hX]
    exact mem_image.2 ⟨n, mem_range.2 (by omega), rfl⟩
  have hiter : ∀ n, G.tripMap^[n + 1] y = G.tripMap^[n] T.tripEntry := fun n => by
    rw [iterate_succ_apply, hs]
  have hz : G.tripMap^[N + 2] y = G.tripMap T.tripExit := by
    rw [hiter, iterate_succ_apply', hN]
  have hzD : T.tripExit ∈ T.darts := hN ▸ hmemX N le_rfl
  rw [← hz, ← hG.tripEquiv_pow_apply]
  refine coe_firstReturn_of_pow (by omega) ?_ fun j hj hjN => ?_
  · rw [hG.tripEquiv_pow_apply, hz]
    exact ⟨G.collapseCore_subset _ (mem_collapseCore_of_notMem hw),
      fun h => T.notMem_bdry_of_mem_darts hzD ((tripMap_mem_bdry_iff hG _).1 h)⟩
  · rw [hG.tripEquiv_pow_apply]
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hiter]
    rintro ⟨h1, -⟩
    exact notMem_darts_of_mem_collapseDarts hG hroot h1 (hmemX j (by omega))

/-- If `ȳ` lies at the internal root, so does its image in the collapse, with the colour of
`a₁`. -/
private theorem collapse_inv_of_vertexOf_inv_eq_root {y : G.collapseDarts {(T, c)}}
    (hr : G.vertexOf (G.inv y) = T.root) :
    ¬(G.collapse {(T, c)}).IsBoundaryVertex
        ((G.collapse {(T, c)}).vertexOf ((G.collapse {(T, c)}).inv y)) ∧
      (G.collapse {(T, c)}).colour ((G.collapse {(T, c)}).inv y) = G.colour T.intervalStart := by
  have hz : ((G.collapse {(T, c)}).inv y : H) = G.inv y := coe_collapse_inv hG y
  have hzK := mem_collapseCore_of_internal hG hroot ((G.collapse {(T, c)}).inv y)
  refine ⟨?_, ?_⟩
  · rwa [collapse_isBoundaryVertex_iff hzK, hz, hr]
  · rw [collapse_colour_of_mem hG hzK, hz, colour_eq_of_mem_root' hG hroot (T.mem_root_iff.2 hr)]

/-- The turn of `ȳ` in `G'` is the first return of `y` to `H' \ B` under the trip map of `G`,
when `ȳ` lies at a black internal root. -/
private theorem coe_turn_collapse_inv_of_black (hR : ¬G.HasRoundtrip)
    {y : G.collapseDarts {(T, c)}} (hy : (y : H) ∉ G.bdry) (hr : G.vertexOf (G.inv y) = T.root)
    (hc : G.colour T.intervalStart = .black) :
    ((G.collapse {(T, c)}).turn ((G.collapse {(T, c)}).inv y) : H) =
      firstReturn hG.tripEquiv {x | x ∈ G.collapseDarts {(T, c)} ∧ x ∉ G.bdry} ⟨y, y.2, hy⟩ := by
  obtain ⟨hb', hcol⟩ := collapse_inv_of_vertexOf_inv_eq_root hG hroot hr
  have hz : ((G.collapse {(T, c)}).inv y : H) = G.inv y := coe_collapse_inv hG y
  have hbv : ¬G.IsBoundaryVertex (G.vertexOf (G.inv y)) := by rwa [hr]
  have hTy : G.tripMap y = G.rot (G.inv y) := by
    rw [tripMap_apply, turn_of_black hbv
      ((colour_eq_of_mem_root' hG hroot (T.mem_root_iff.2 hr)).trans hc)]
  rw [turn_of_black hb' (hcol.trans hc)]
  by_cases hσ : G.rot (G.inv y) ∈ T.darts
  · have ha1 : G.rot (G.inv y) = T.intervalStart := T.rot_eq_intervalStart hG
      (inv_notMem_darts hG (notMem_darts_of_mem_collapseDarts hG hroot y.2)) hσ
    rw [coe_collapse_rot_of_rot_eq_intervalStart hG hroot (by rwa [hz])]
    have hs : G.tripMap y = T.tripEntry := by rw [hTy, ha1, T.tripEntry_of_black hc]
    have hkb : ¬G.IsBoundaryVertex (G.vertexOf T.intervalEnd) := by
      rwa [T.mem_root_iff.1 T.intervalEnd_mem_root]
    have hTz : G.tripMap T.tripExit = G.rot T.intervalEnd := by
      rw [T.tripExit_of_black hroot hc, tripMap_apply, hG.inv_involutive,
        turn_of_black hkb ((colour_eq_of_mem_root' hG hroot T.intervalEnd_mem_root).trans hc)]
    rw [coe_firstReturn_of_tripMap_eq_tripEntry hG hroot hR ⟨y.2, hy⟩ hs
      (hTz ▸ T.rot_intervalEnd_notMem hG), hTz]
  · rw [coe_collapse_rot_of_rot_mem (mem_collapseCore_of_internal hG hroot _)
      (by rw [hz]; exact mem_collapseCore_of_notMem hσ),
      hz, coe_firstReturn_of_tripMap_notMem hG hy (hTy ▸ hσ), hTy]

/-- The turn of `ȳ` in `G'` is the first return of `y` to `H' \ B` under the trip map of `G`,
when `ȳ` lies at a white internal root. -/
private theorem coe_turn_collapse_inv_of_white (hR : ¬G.HasRoundtrip)
    {y : G.collapseDarts {(T, c)}} (hy : (y : H) ∉ G.bdry) (hr : G.vertexOf (G.inv y) = T.root)
    (hc : G.colour T.intervalStart = .white) :
    ((G.collapse {(T, c)}).turn ((G.collapse {(T, c)}).inv y) : H) =
      firstReturn hG.tripEquiv {x | x ∈ G.collapseDarts {(T, c)} ∧ x ∉ G.bdry} ⟨y, y.2, hy⟩ := by
  obtain ⟨hb', hcol⟩ := collapse_inv_of_vertexOf_inv_eq_root hG hroot hr
  have hyiD := inv_notMem_darts hG (notMem_darts_of_mem_collapseDarts hG hroot y.2)
  have hz : ((G.collapse {(T, c)}).inv y : H) = G.inv y := coe_collapse_inv hG y
  have hzK := mem_collapseCore_of_internal hG hroot ((G.collapse {(T, c)}).inv y)
  have hbv : ¬G.IsBoundaryVertex (G.vertexOf (G.inv y)) := by rwa [hr]
  have hTy : G.tripMap y = G.rot.symm (G.inv y) := by
    rw [tripMap_apply, turn_of_white hbv
      ((colour_eq_of_mem_root' hG hroot (T.mem_root_iff.2 hr)).trans hc)]
  rw [turn_of_white hb' (hcol.trans hc)]
  by_cases hσ : G.rot.symm (G.inv y) ∈ T.darts
  · have hak : G.rot.symm (G.inv y) = T.intervalEnd :=
      T.eq_intervalEnd hG hσ (by rwa [Equiv.apply_symm_apply])
    have hwK : G.rot.symm T.intervalStart ∈ G.collapseCore {(T, c)} :=
      mem_collapseCore_of_notMem T.rot_symm_intervalStart_notMem
    have hw : (G.collapse {(T, c)}).rot ⟨G.rot.symm T.intervalStart,
        G.collapseCore_subset _ hwK⟩ = (G.collapse {(T, c)}).inv y := by
      apply Subtype.ext
      rw [coe_collapse_rot_of_rot_eq_intervalStart hG hroot (by simp), hz, ← hak,
        Equiv.apply_symm_apply]
    rw [(Equiv.symm_apply_eq _).2 hw.symm]
    have hs : G.tripMap y = T.tripEntry := by
      rw [hTy, hak, T.tripEntry_of_white hroot hc]
    have hab : ¬G.IsBoundaryVertex (G.vertexOf T.intervalStart) := by
      rwa [T.mem_root_iff.1 T.intervalStart_mem_root]
    have hTz : G.tripMap T.tripExit = G.rot.symm T.intervalStart := by
      rw [T.tripExit_of_white hc, tripMap_apply, hG.inv_involutive, turn_of_white hab hc]
    rw [coe_firstReturn_of_tripMap_eq_tripEntry hG hroot hR ⟨y.2, hy⟩ hs
      (hTz ▸ T.rot_symm_intervalStart_notMem), hTz]
  · have hwK : G.rot.symm (G.inv y) ∈ G.collapseCore {(T, c)} :=
      mem_collapseCore_of_notMem hσ
    have hw : (G.collapse {(T, c)}).rot ⟨G.rot.symm (G.inv y),
        G.collapseCore_subset _ hwK⟩ = (G.collapse {(T, c)}).inv y := by
      apply Subtype.ext
      rw [coe_collapse_rot_of_rot_mem hwK (by simpa [Equiv.apply_symm_apply, hz] using hzK),
        Equiv.apply_symm_apply, hz]
    rw [(Equiv.symm_apply_eq _).2 hw.symm, coe_firstReturn_of_tripMap_notMem hG hy (hTy ▸ hσ),
      hTy]

/-- A dart of the lift of a pendant set over a collapsed tree with internal root, away from the
lifted vertex, lies at an internal vertex all of whose darts are in the lift. -/
private theorem vertexOf_mem_internalVertices_and_mem_of_mem_lift
    {x : G.collapseDarts {(T, c)}} {D' : Set (G.collapseDarts {(T, c)})}
    (hD' : (G.collapse {(T, c)}).IsPendantAt ((G.collapse {(T, c)}).vertexOf x) D')
    {D : Set H} (hD : ∀ d, d ∈ D ↔ d ∈ Subtype.val '' D' ∨
      (((∃ y ∈ D', G.vertexOf (y : H) = T.root) ∧ G.vertexOf (x : H) ≠ T.root) ∧
        d ∈ T.darts))
    {d : H} (hd : d ∈ D) (hne : G.vertexOf d ≠ G.vertexOf (x : H)) :
    G.vertexOf d ∈ G.internalVertices ∧ ∀ e ∈ G.vertexOf d, e ∈ D := by
  have hK := mem_collapseCore_of_internal (c := c) hG hroot
  rcases (hD d).1 hd with ⟨d', hd', rfl⟩ | ⟨hP, hdT⟩
  · have hne' : (G.collapse {(T, c)}).vertexOf d' ≠ (G.collapse {(T, c)}).vertexOf x :=
      fun h => hne ((collapse_vertexOf_eq_iff (hK x) (hK d')).1 h)
    refine ⟨(collapse_vertexOf_mem_internalVertices_iff (hK d')).1
      (hD'.vertexOf_mem_internalVertices d' hd' hne'), fun e he => ?_⟩
    by_cases heD : e ∈ T.darts
    · have hd'r : G.vertexOf (d' : H) = T.root := by
        rcases T.vertexOf_mem_or_eq_root hG heD with h | h
        · exact absurd (T.mem_darts_of_vertexOf_mem (G.vertexOf_eq_of_mem he ▸ h))
            (notMem_darts_of_mem_collapseDarts hG hroot d'.2)
        · exact (G.vertexOf_eq_of_mem he).symm.trans h
      exact (hD e).2 (Or.inr ⟨⟨⟨d', hd', hd'r⟩, fun h => hne (hd'r.trans h.symm)⟩, heD⟩)
    · exact (hD e).2 (Or.inl ⟨_, hD'.mem_of_mem_vertexOf d' hd' hne' _
        (mem_collapse_vertexOf (hK d') he (mem_collapseCore_of_notMem heD)), rfl⟩)
  · rcases T.vertexOf_mem_or_eq_root hG hdT with hW | hr
    · refine ⟨T.nonRoot_subset hW, fun e he => (hD e).2 (Or.inr ⟨hP, ?_⟩)⟩
      exact T.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_eq_of_mem he])
    · refine ⟨by rw [hr]; exact G.mem_internalVertices.2 ⟨T.root_mem_vertices, hroot⟩,
        fun e he => ?_⟩
      by_cases heD : e ∈ T.darts
      · exact (hD e).2 (Or.inr ⟨hP, heD⟩)
      obtain ⟨⟨y', hy', hy'r⟩, hxr⟩ := hP
      have hne' : (G.collapse {(T, c)}).vertexOf y' ≠ (G.collapse {(T, c)}).vertexOf x :=
        fun h => hxr (((collapse_vertexOf_eq_iff (hK x) (hK y')).1 h).symm.trans hy'r)
      have he' : e ∈ G.vertexOf (y' : H) := by rwa [hy'r, ← hr]
      exact (hD e).2 (Or.inl ⟨_, hD'.mem_of_mem_vertexOf y' hy' hne' _
        (mem_collapse_vertexOf (hK y') he' (mem_collapseCore_of_notMem heD)), rfl⟩)

end Internal

/-- **Collapsing a tree with internal root takes first returns of the trip map**. Let `G` be a
plabic graph without roundtrip, `T = (v, W)` a rooted tree of `G` whose root `v` is internal, and
`G' = G/{(v, W, c)}`, with darts `H'`. Then the trip map `T'` of `G'` is the first-return map of
the trip map `T` of `G` to `H' \ B`: for `y ∈ H' \ B`, `T'(y) = T_{H' \ B}(y)`. The tree need not
be collapsible. -/
@[cluster_algebras "lem_collapse_trip_map"]
theorem RootedTree.coe_tripMap_collapse (hG : G.IsPlabicGraph) (hR : ¬G.HasRoundtrip)
    (T : G.RootedTree) (c : Shade) (hroot : ¬G.IsBoundaryVertex T.root)
    (y : G.collapseDarts {(T, c)}) (hy : (y : H) ∉ G.bdry) :
    ((G.collapse {(T, c)}).tripMap y : H) =
      firstReturn hG.tripEquiv {x | x ∈ G.collapseDarts {(T, c)} ∧ x ∉ G.bdry} ⟨y, y.2, hy⟩ := by
  have hz : ((G.collapse {(T, c)}).inv y : H) = G.inv y := coe_collapse_inv hG y
  rw [tripMap_apply]
  by_cases hr : G.vertexOf (G.inv y) = T.root
  · cases hc : G.colour T.intervalStart with
    | black => exact coe_turn_collapse_inv_of_black hG hroot hR hy hr hc
    | white => exact coe_turn_collapse_inv_of_white hG hroot hR hy hr hc
  · have hall := forall_mem_vertexOf_notMem_darts hG
      (inv_notMem_darts hG (notMem_darts_of_mem_collapseDarts hG hroot y.2)) hr
    rw [coe_turn_collapse hG (by rwa [hz]), hz, ← tripMap_apply,
      coe_firstReturn_of_tripMap_notMem hG hy (hall _ (turn_mem_vertexOf _))]

/-- **Trips after collapsing a tree with internal root**. Let `G` be a plabic graph without
roundtrip, `T = (v, W)` a collapsible tree of colour `c` of `G` whose root `v` is internal, and
`G' = G/{(v, W, c)}`, with darts `H'`. Then for every dart `y ∈ H' \ B`, `y ∈ darts_{G'}(i)` if
and only if `y ∈ darts_G(i)`. -/
@[cluster_algebras "lem_collapse_internal_trips"]
theorem RootedTree.IsCollapsibleOfColour.mem_oneWayTrip_collapse_iff (hG : G.IsPlabicGraph)
    (hR : ¬G.HasRoundtrip) {T : G.RootedTree} {c : Shade} (hT : T.IsCollapsibleOfColour c)
    (hroot : ¬G.IsBoundaryVertex T.root) (i : Fin b) (y : G.collapseDarts {(T, c)})
    (hy : (y : H) ∉ G.bdry) :
    y ∈ (G.collapse {(T, c)}).oneWayTrip i ↔ (y : H) ∈ G.oneWayTrip i := by
  obtain ⟨hG', -⟩ := hT.moveEquivalent_collapse hG
  let e : {x | x ∈ G.collapseDarts {(T, c)} ∧ x ∉ G.bdry} ≃
      {x : G.collapseDarts {(T, c)} | x ∉ (G.collapse {(T, c)}).bdry} :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h => x.2.2 (mem_collapse_bdry.1 h)⟩
      invFun := fun x => ⟨x.1.1, x.1.2, fun h => x.2 (mem_collapse_bdry.2 h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfr : ∀ x, e (firstReturn hG.tripEquiv
      {x | x ∈ G.collapseDarts {(T, c)} ∧ x ∉ G.bdry} x) =
      firstReturn hG'.tripEquiv {x : G.collapseDarts {(T, c)} | x ∉ (G.collapse {(T, c)}).bdry}
        (e x) := by
    intro x
    apply Subtype.ext
    have hmem : hG'.tripEquiv (e x : G.collapseDarts {(T, c)}) ∈
        {x : G.collapseDarts {(T, c)} | x ∉ (G.collapse {(T, c)}).bdry} :=
      fun h => (e x).2 ((tripMap_mem_bdry_iff hG' _).1 h)
    rw [coe_firstReturn_of_apply_mem (π := hG'.tripEquiv) hmem]
    exact Subtype.ext (T.coe_tripMap_collapse hG hR c hroot ⟨x.1, x.2.1⟩ x.2.2).symm
  have key := hG.tripSet_eq_of_firstReturn hG' e
    (fun j => ⟨⟨G.collapseCore_subset _ (G.leg_mem_collapseCore _ j), hG.leg_notMem_bdry j⟩, rfl⟩)
    hfr ⟨y, y.2, hy⟩
  have := Finset.ext_iff.1 key i
  rw [mem_tripSet, mem_tripSet] at this
  exact this.symm

/-- For a boundary root `β(y₀)` and `i ≠ y₀`, the one-way trip from `i` avoids the darts of the
tree: these are mapped into themselves by the trip map, and contain no leg but `g_{y₀}`. -/
private theorem RootedTree.iterate_tripMap_leg_notMem_darts (hG : G.IsPlabicGraph)
    (T : G.RootedTree) {y₀ i : Fin b} (hT0 : T.root = G.bvertex y₀) (hi : i ≠ y₀) (n : ℕ) :
    G.tripMap^[n] (G.leg i) ∉ T.darts := by
  have hb : G.IsBoundaryVertex T.root :=
    hT0 ▸ G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem y₀)
  have hmaps : ∀ x ∈ T.darts, G.tripMap x ∈ T.darts := by
    intro x hx
    by_cases hz : x = T.tripExit
    · rw [hz, T.tripExit_of_isBoundaryVertex hb, tripMap_apply, hG.inv_involutive,
        turn_of_isBoundaryVertex (by rw [T.mem_root_iff.1 T.intervalStart_mem_root]; exact hb)]
      exact T.intervalStart_mem_darts
    · exact T.tripMap_mem_darts hG hx hz
  have hiter : ∀ k, ∀ x ∈ T.darts, G.tripMap^[k] x ∈ T.darts := by
    intro k
    induction k with
    | zero => exact fun x hx => hx
    | succ k ih =>
      intro x hx
      rw [iterate_succ_apply']
      exact hmaps _ (ih x hx)
  intro hn
  have hp : 0 < orderOf hG.tripEquiv := (isOfFinOrder_of_finite _).orderOf_pos
  have hback : G.tripMap^[orderOf hG.tripEquiv * n - n] (G.tripMap^[n] (G.leg i)) =
      G.leg i := by
    rw [← iterate_add_apply, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n hp),
      ← hG.tripEquiv_pow_apply, pow_mul, pow_orderOf_eq_one, one_pow, Equiv.Perm.one_apply]
  have hgi := hiter (orderOf hG.tripEquiv * n - n) _ hn
  rw [hback] at hgi
  have := T.leg_eq_intervalStart hG hgi
  rw [T.intervalStart_eq_leg hG hT0] at this
  exact hi (hG.leg_injective this)

/-- The iterates of the trip map at a leg are not in `B`. -/
private theorem iterate_tripMap_leg_notMem_bdry (hG : G.IsPlabicGraph) (i : Fin b) (n : ℕ) :
    G.tripMap^[n] (G.leg i) ∉ G.bdry := by
  induction n with
  | zero => exact hG.leg_notMem_bdry i
  | succ n ih =>
    rw [iterate_succ_apply']
    exact fun h => ih ((tripMap_mem_bdry_iff hG _).1 h)

/-- **Trips after collapsing a tree with boundary root**. Let `G` be a plabic graph,
`T = (β(y₀), W)` a rooted tree of `G`, `G' = G/{(β(y₀), W, c)}` with trip map `T'`, and `i ≠ y₀`.
Then `T'ⁿ(g_i) = Tⁿ(g_i)` for every `n ≥ 0`. The tree need not be collapsible, and `G` may have
roundtrips. -/
@[cluster_algebras "lem_collapse_boundary_trips"]
theorem RootedTree.coe_iterate_tripMap_collapse_leg (hG : G.IsPlabicGraph) (T : G.RootedTree)
    (c : Shade) {y₀ i : Fin b} (hT0 : T.root = G.bvertex y₀) (hi : i ≠ y₀) (n : ℕ) :
    (((G.collapse {(T, c)}).tripMap^[n] ((G.collapse {(T, c)}).leg i) : _) : H) =
      G.tripMap^[n] (G.leg i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', tripMap_apply]
    set y := G.tripMap^[n] (G.leg i)
    have hyD : y ∉ T.darts := T.iterate_tripMap_leg_notMem_darts hG hT0 hi n
    have hyB : y ∉ G.bdry := iterate_tripMap_leg_notMem_bdry hG i n
    have hyiD : G.inv y ∉ T.darts := inv_notMem_darts hG hyD
    have hr : G.vertexOf (G.inv y) ≠ T.root := by
      intro h
      have hbv : G.IsBoundaryVertex (G.vertexOf (G.inv y)) := by
        rw [h, hT0]
        exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem y₀)
      obtain ⟨j, hj⟩ := hG.exists_eq_leg_of_isBoundaryVertex hbv
        (fun hB => hyB (hG.inv_mem_bdry_iff.1 hB))
      have hroot : T.root = G.bvertex j := by
        rw [← h, hj]
        rfl
      apply hyiD
      rw [hj, ← T.intervalStart_eq_leg hG hroot]
      exact T.intervalStart_mem_darts
    have hall := forall_mem_vertexOf_notMem_darts hG hyiD hr
    have hX : (((G.collapse {(T, c)}).inv
        ((G.collapse {(T, c)}).tripMap^[n] ((G.collapse {(T, c)}).leg i)) : _) : H) =
        G.inv y := by
      rw [coe_collapse_inv hG, ih]
    rw [coe_turn_collapse hG (by rwa [hX]), hX, tripMap_apply]

/-- **Lifting a pendant set over a collapsed tree with internal root**. Let `G` be a plabic graph
without roundtrip, `T = (v, W)` a collapsible tree of colour `c` of `G` whose root `v` is internal,
and `G' = G/{(v, W, c)}`. Let `w'` be a vertex of `G'` and `D'` a set of darts of `G'` pendant at
`w'` such that `y ∈ darts_{G'}(i) ↔ ȳ ∈ darts_{G'}(i)` for every `y ∈ D'`. Then there are a vertex
`w` of `G` and a set `D ⊇ D'` of darts of `G` pendant at `w` such that
`y ∈ darts_G(i) ↔ ȳ ∈ darts_G(i)` for every `y ∈ D`. -/
@[cluster_algebras "lem_pendant_lift_internal"]
theorem RootedTree.IsCollapsibleOfColour.exists_isPendantAt_of_collapse (hG : G.IsPlabicGraph)
    (hR : ¬G.HasRoundtrip) {T : G.RootedTree} {c : Shade} (hT : T.IsCollapsibleOfColour c)
    (hroot : ¬G.IsBoundaryVertex T.root) (i : Fin b)
    {w' : Finset (G.collapseDarts {(T, c)})} (hw' : w' ∈ (G.collapse {(T, c)}).vertices)
    {D' : Set (G.collapseDarts {(T, c)})} (hD' : (G.collapse {(T, c)}).IsPendantAt w' D')
    (hsym : ∀ y ∈ D', (y ∈ (G.collapse {(T, c)}).oneWayTrip i ↔
      (G.collapse {(T, c)}).inv y ∈ (G.collapse {(T, c)}).oneWayTrip i)) :
    ∃ w ∈ G.vertices, ∃ D : Set H, G.IsPendantAt w D ∧ Subtype.val '' D' ⊆ D ∧
      ∀ y ∈ D, (y ∈ G.oneWayTrip i ↔ G.inv y ∈ G.oneWayTrip i) := by
  obtain ⟨x, rfl⟩ := (G.collapse {(T, c)}).mem_vertices.1 hw'
  -- `D = D' ∪ D_T` if `D'` has a dart at `v°` and `w' ≠ v°`, and `D = D'` otherwise.
  obtain ⟨D, hD⟩ : ∃ D : Set H, ∀ d, d ∈ D ↔ d ∈ Subtype.val '' D' ∨
      (((∃ y ∈ D', G.vertexOf (y : H) = T.root) ∧ G.vertexOf (x : H) ≠ T.root) ∧
        d ∈ T.darts) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hnb : ∀ z ∈ D', (z : H) ∉ G.bdry := fun z hz h =>
    hD'.notMem_bdry z hz (mem_collapse_bdry.2 h)
  have hint := fun d (hd : d ∈ D) hne =>
    vertexOf_mem_internalVertices_and_mem_of_mem_lift hG hroot hD' hD hd hne
  refine ⟨G.vertexOf x, G.vertexOf_mem_vertices _, D, ⟨?_, ?_, fun d hd hne => (hint d hd hne).1,
    fun d hd hne => (hint d hd hne).2⟩, fun d hd => (hD d).2 (Or.inl hd), ?_⟩
  · intro d hd
    rcases (hD d).1 hd with ⟨d', hd', rfl⟩ | ⟨-, hdT⟩
    · exact hnb d' hd'
    · exact T.notMem_bdry_of_mem_darts hdT
  · intro d hd
    rcases (hD d).1 hd with ⟨d', hd', rfl⟩ | ⟨hP, hdT⟩
    · exact (hD _).2 (Or.inl ⟨_, hD'.inv_mem d' hd', coe_collapse_inv hG d'⟩)
    · exact (hD _).2 (Or.inr ⟨hP, T.inv_mem_darts hG hdT⟩)
  · intro d hd
    rcases (hD d).1 hd with ⟨d', hd', rfl⟩ | ⟨-, hdT⟩
    · have h1 := hT.mem_oneWayTrip_collapse_iff hG hR hroot i d' (hnb d' hd')
      have h2 := hT.mem_oneWayTrip_collapse_iff hG hR hroot i _ (hnb _ (hD'.inv_mem d' hd'))
      rw [coe_collapse_inv hG] at h2
      rw [← h1, ← h2]
      exact hsym d' hd'
    · exact T.mem_oneWayTrip_iff_inv_mem hG hR hroot i hdT

/-- For a boundary root `β(y₀)` and `i ≠ y₀`, a dart of the collapse lies on the one-way trip from
`i` in the collapse if and only if it does in `G`. -/
theorem RootedTree.mem_oneWayTrip_collapse_iff_of_eq_bvertex (hG : G.IsPlabicGraph)
    (T : G.RootedTree) (c : Shade) {y₀ i : Fin b} (hT0 : T.root = G.bvertex y₀) (hi : i ≠ y₀)
    (y : G.collapseDarts {(T, c)}) :
    y ∈ (G.collapse {(T, c)}).oneWayTrip i ↔ (y : H) ∈ G.oneWayTrip i := by
  have hcoe := T.coe_iterate_tripMap_collapse_leg hG c hT0 hi
  have hlen : (G.collapse {(T, c)}).tripLength i = G.tripLength i := by
    unfold tripLength
    congr 1
    ext m
    simp only [Set.mem_setOf_eq]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, by rw [← hcoe m, ← hj]; rfl⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, Subtype.ext (by rw [hcoe m, ← hj]; rfl)⟩
  rw [mem_oneWayTrip, mem_oneWayTrip, hlen]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  rw [← hcoe k]
  exact Subtype.coe_inj.symm

/-- For a boundary root `β(y₀)` and `i ≠ y₀`, the one-way trip from `i` avoids the darts of the
tree. -/
private theorem RootedTree.notMem_oneWayTrip_of_mem_darts (hG : G.IsPlabicGraph)
    (T : G.RootedTree) {y₀ i : Fin b} (hT0 : T.root = G.bvertex y₀) (hi : i ≠ y₀) {d : H}
    (hd : d ∈ T.darts) : d ∉ G.oneWayTrip i := by
  intro h
  obtain ⟨k, -, rfl⟩ := mem_oneWayTrip.1 h
  exact T.iterate_tripMap_leg_notMem_darts hG hT0 hi k hd

/-- For a boundary root, a vertex of `G` carrying a kept dart is kept whole. -/
private theorem mem_collapseCore_of_mem_vertexOf (hG : G.IsPlabicGraph) {T : G.RootedTree}
    {c : Shade} (hb : G.IsBoundaryVertex T.root) {x : G.collapseDarts {(T, c)}}
    (hx : (x : H) ∈ G.collapseCore {(T, c)}) {e : H} (he : e ∈ G.vertexOf (x : H)) :
    e ∈ G.collapseCore {(T, c)} := by
  have hU := vertexOf_notMem_nonRoot_of_mem_collapseCore hG hx
  have hfil := filter_vertexOf_mem_collapseCore_of_not hG hU (by
    by_cases h : G.vertexOf (x : H) = T.root
    · exact Or.inl (by rwa [h])
    · exact Or.inr fun p hp => by
        rw [Finset.mem_singleton.1 hp]
        exact fun h' => h h'.symm)
  rw [← hfil] at he
  exact (mem_filter.1 he).2

/-- For a boundary root `β(y₀)`, the only dart of the collapse which is not kept is `ḡ_{y₀}`. -/
private theorem coe_eq_inv_leg_of_notMem_collapseCore (hG : G.IsPlabicGraph) {T : G.RootedTree}
    {c : Shade} {y₀ : Fin b} (hT0 : T.root = G.bvertex y₀) {x : G.collapseDarts {(T, c)}}
    (hx : (x : H) ∉ G.collapseCore {(T, c)}) : (x : H) = G.inv (G.leg y₀) := by
  rcases x.2 with hx' | ⟨j, hj, hxj⟩
  · exact absurd hx' hx
  · rw [hxj, T.leg_eq_intervalStart hG (mem_familyDarts_singleton.1 hj),
      T.intervalStart_eq_leg hG hT0]

/-- For a boundary root, a dart at the vertex of the collapse of a kept dart is kept. -/
private theorem mem_collapseCore_of_collapse_vertexOf_eq (hG : G.IsPlabicGraph)
    {T : G.RootedTree} {c : Shade} {y₀ : Fin b} (hT0 : T.root = G.bvertex y₀)
    {x y : G.collapseDarts {(T, c)}} (hy : (y : H) ∈ G.collapseCore {(T, c)})
    (h : (G.collapse {(T, c)}).vertexOf y = (G.collapse {(T, c)}).vertexOf x) :
    (x : H) ∈ G.collapseCore {(T, c)} := by
  by_contra hx
  have hg : G.leg y₀ ∈ T.darts := T.intervalStart_eq_leg hG hT0 ▸ T.intervalStart_mem_darts
  have hsing := collapse_vertexOf_inv_leg hG (mem_familyDarts_singleton.2 hg)
    (coe_eq_inv_leg_of_notMem_collapseCore hG hT0 hx)
  have hyx : y ∈ (G.collapse {(T, c)}).vertexOf x :=
    h ▸ (G.collapse {(T, c)}).self_mem_vertexOf y
  rw [hsing, mem_singleton] at hyx
  exact hx (hyx ▸ hy)

/-- A dart of the lift of a pendant set over a collapsed tree with boundary root, away from the
lifted vertex `w`, lies at an internal vertex all of whose darts are in the lift. -/
private theorem vertexOf_mem_internalVertices_and_mem_of_mem_lift_of_eq_bvertex
    (hG : G.IsPlabicGraph) {T : G.RootedTree} {c : Shade} {y₀ : Fin b}
    (hT0 : T.root = G.bvertex y₀) {x : G.collapseDarts {(T, c)}}
    {D' : Set (G.collapseDarts {(T, c)})}
    (hD' : (G.collapse {(T, c)}).IsPendantAt ((G.collapse {(T, c)}).vertexOf x) D')
    {w : Finset H} (hW1 : ∀ y : G.collapseDarts {(T, c)}, (y : H) ∈ G.collapseCore {(T, c)} →
      (G.collapse {(T, c)}).vertexOf y = (G.collapse {(T, c)}).vertexOf x →
        G.vertexOf (y : H) = w)
    (hW2 : G.leg y₀ ∈ Subtype.val '' D' → T.root = w)
    {D : Set H} (hD : ∀ d, d ∈ D ↔ d ∈ Subtype.val '' D' ∨
      (G.leg y₀ ∈ Subtype.val '' D' ∧ d ∈ T.darts))
    {d : H} (hd : d ∈ D) (hne : G.vertexOf d ≠ w) :
    G.vertexOf d ∈ G.internalVertices ∧ ∀ e ∈ G.vertexOf d, e ∈ D := by
  have hb : G.IsBoundaryVertex T.root :=
    hT0 ▸ G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem y₀)
  have hg : G.leg y₀ ∈ T.darts := T.intervalStart_eq_leg hG hT0 ▸ T.intervalStart_mem_darts
  rcases (hD d).1 hd with ⟨d', hd', rfl⟩ | ⟨hQ, hdT⟩
  · by_cases hdK : (d' : H) ∈ G.collapseCore {(T, c)}
    · have hne' : (G.collapse {(T, c)}).vertexOf d' ≠ (G.collapse {(T, c)}).vertexOf x :=
        fun h => hne (hW1 d' hdK h)
      exact ⟨(collapse_vertexOf_mem_internalVertices_iff hdK).1
        (hD'.vertexOf_mem_internalVertices d' hd' hne'), fun e he => (hD e).2 (Or.inl ⟨_,
          hD'.mem_of_mem_vertexOf d' hd' hne' _ (mem_collapse_vertexOf hdK he
            (mem_collapseCore_of_mem_vertexOf hG hb hdK he)), rfl⟩)⟩
    · have hdg := coe_eq_inv_leg_of_notMem_collapseCore hG hT0 hdK
      have hQ : G.leg y₀ ∈ Subtype.val '' D' :=
        ⟨_, hD'.inv_mem d' hd', by rw [coe_collapse_inv hG, hdg, hG.inv_involutive]⟩
      have hW := T.vertexOf_inv_leg_mem hG hg
      rw [← hdg] at hW
      exact ⟨T.nonRoot_subset hW, fun e he => (hD e).2 (Or.inr ⟨hQ,
        T.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_eq_of_mem he])⟩)⟩
  · rcases T.vertexOf_mem_or_eq_root hG hdT with hW | hr
    · exact ⟨T.nonRoot_subset hW, fun e he => (hD e).2 (Or.inr ⟨hQ,
        T.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_eq_of_mem he])⟩)⟩
    · exact absurd (hr.trans (hW2 hQ)) hne

/-- **Lifting a pendant set over a collapsed tree with boundary root**. Let `G` be a plabic graph,
`T = (β(y₀), W)` a rooted tree of `G`, `G' = G/{(β(y₀), W, c)}`, and `i ≠ y₀`. Let `w'` be a vertex
of `G'` and `D'` a set of darts of `G'` pendant at `w'` such that
`y ∈ darts_{G'}(i) ↔ ȳ ∈ darts_{G'}(i)` for every `y ∈ D'`. Then there are a vertex `w` of `G` and
a set `D ⊇ D'` of darts of `G` pendant at `w` such that `y ∈ darts_G(i) ↔ ȳ ∈ darts_G(i)` for every
`y ∈ D`. The tree need not be collapsible, and `G` may have roundtrips. -/
@[cluster_algebras "lem_pendant_lift_boundary"]
theorem RootedTree.exists_isPendantAt_of_collapse_of_eq_bvertex (hG : G.IsPlabicGraph)
    (T : G.RootedTree) (c : Shade) {y₀ i : Fin b} (hT0 : T.root = G.bvertex y₀) (hi : i ≠ y₀)
    {w' : Finset (G.collapseDarts {(T, c)})} (hw' : w' ∈ (G.collapse {(T, c)}).vertices)
    {D' : Set (G.collapseDarts {(T, c)})} (hD' : (G.collapse {(T, c)}).IsPendantAt w' D')
    (hsym : ∀ y ∈ D', (y ∈ (G.collapse {(T, c)}).oneWayTrip i ↔
      (G.collapse {(T, c)}).inv y ∈ (G.collapse {(T, c)}).oneWayTrip i)) :
    ∃ w ∈ G.vertices, ∃ D : Set H, G.IsPendantAt w D ∧ Subtype.val '' D' ⊆ D ∧
      ∀ y ∈ D, (y ∈ G.oneWayTrip i ↔ G.inv y ∈ G.oneWayTrip i) := by
  have hb : G.IsBoundaryVertex T.root :=
    hT0 ▸ G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem y₀)
  have hgr : G.vertexOf (G.leg y₀) = T.root := hT0.symm
  obtain ⟨x, rfl⟩ := (G.collapse {(T, c)}).mem_vertices.1 hw'
  -- The vertex `w` of `G` containing `w'`; it is `β(y₀)` if `w'` is the new lollipop.
  obtain ⟨w, hw⟩ : ∃ w : Finset H,
      w = if (x : H) ∈ G.collapseCore {(T, c)} then G.vertexOf (x : H) else T.root :=
    ⟨_, rfl⟩
  have hwv : w ∈ G.vertices := by
    rw [hw]
    split_ifs
    exacts [G.vertexOf_mem_vertices _, T.root_mem_vertices]
  have hW1 : ∀ y : G.collapseDarts {(T, c)}, (y : H) ∈ G.collapseCore {(T, c)} →
      (G.collapse {(T, c)}).vertexOf y = (G.collapse {(T, c)}).vertexOf x →
        G.vertexOf (y : H) = w := by
    intro y hy h
    have hx := mem_collapseCore_of_collapse_vertexOf_eq hG hT0 hy h
    rw [hw, if_pos hx]
    exact (collapse_vertexOf_eq_iff hx hy).1 h
  have hW2 : G.leg y₀ ∈ Subtype.val '' D' → T.root = w := by
    rintro ⟨g', hg', hgg⟩
    have hgK : (g' : H) ∈ G.collapseCore {(T, c)} := hgg ▸ G.leg_mem_collapseCore _ y₀
    have hbg : G.IsBoundaryVertex (G.vertexOf (g' : H)) := by rwa [hgg, hgr]
    have hv : (G.collapse {(T, c)}).vertexOf g' = (G.collapse {(T, c)}).vertexOf x := by
      by_contra h
      exact (G.vertexOf_mem_internalVertices.1 ((collapse_vertexOf_mem_internalVertices_iff
        hgK).1 (hD'.vertexOf_mem_internalVertices g' hg' h))) hbg
    rw [← hgr, ← hgg]
    exact hW1 g' hgK hv
  -- `D = D' ∪ D_T` if `g_{y₀} ∈ D'`, and `D = D'` otherwise.
  obtain ⟨D, hD⟩ : ∃ D : Set H, ∀ d, d ∈ D ↔ d ∈ Subtype.val '' D' ∨
      (G.leg y₀ ∈ Subtype.val '' D' ∧ d ∈ T.darts) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hint := fun d (hd : d ∈ D) hne =>
    vertexOf_mem_internalVertices_and_mem_of_mem_lift_of_eq_bvertex hG hT0 hD' hW1 hW2 hD hd hne
  refine ⟨w, hwv, D, ⟨?_, ?_, fun d hd hne => (hint d hd hne).1,
    fun d hd hne => (hint d hd hne).2⟩, fun d hd => (hD d).2 (Or.inl hd), ?_⟩
  · intro d hd
    rcases (hD d).1 hd with ⟨d', hd', rfl⟩ | ⟨-, hdT⟩
    · exact fun h => hD'.notMem_bdry d' hd' (mem_collapse_bdry.2 h)
    · exact T.notMem_bdry_of_mem_darts hdT
  · intro d hd
    rcases (hD d).1 hd with ⟨d', hd', rfl⟩ | ⟨hQ, hdT⟩
    · exact (hD _).2 (Or.inl ⟨_, hD'.inv_mem d' hd', coe_collapse_inv hG d'⟩)
    · exact (hD _).2 (Or.inr ⟨hQ, T.inv_mem_darts hG hdT⟩)
  · intro d hd
    rcases (hD d).1 hd with ⟨d', hd', rfl⟩ | ⟨-, hdT⟩
    · have hmem := T.mem_oneWayTrip_collapse_iff_of_eq_bvertex hG c hT0 hi
      rw [← hmem d', ← coe_collapse_inv hG d', ← hmem]
      exact hsym d' hd'
    · exact iff_of_false (T.notMem_oneWayTrip_of_mem_darts hG hT0 hi hdT)
        (T.notMem_oneWayTrip_of_mem_darts hG hT0 hi (T.inv_mem_darts hG hdT))

end OneTree

end PlabicData

end ClusterAlgebras

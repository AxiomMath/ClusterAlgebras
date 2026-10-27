/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CycleSpace
public import ClusterAlgebras.Plabic.FirstReturn
public import ClusterAlgebras.Plabic.Trips

/-!
# Hollow digons, excision of edges, and loops

This file collects three tools used to simplify plabic graphs.

*Hollow digons.* If `{d₁, d₂}` is a hollow digon of a disk map, then `φ` swaps `d₁` and `d₂`, so
`σ(d̄₁) = d₂` and `σ(d̄₂) = d₁`: each vertex of the digon carries one dart of the digon and the
reverse of the other, and both vertices are internal.

*Excision.* Given a set `𝓔` of edges of the graph of a plabic graph `K`, with set of darts `X`,
the excision `K ⊖ 𝓔` keeps the darts of `H \ X` connected to the boundary, with the rotation
`σ_X` given by the first return of `σ` to `H \ X`.

*Loops.* Let `{d, d̄}` be a loop at a vertex `u` of a disk map, with rotation
`(d, a₁, …, a_k, d̄, b₁, …, b_l)` at `u`, `k, l ≥ 1`. Cutting the loop off and splitting `u`
into the two vertices `(a₁, …, a_k)` and `(b₁, …, b_l)` yields a rotation system with one vertex
more, one edge fewer and as many faces; Euler's bound shows that it is disconnected, so the darts
`a_i` cannot be joined to the darts `b_j` without passing through `u` or the loop. In a plabic
graph, one side of the loop is therefore cut off from the boundary, and the trip leaving `u`
into that side never reaches a leg: a loop gives a roundtrip.

## Main definitions

* `ClusterAlgebras.PlabicData.excisionRot`: the first-return map `σ_X` of the rotation to the
  complement of the darts of a set of edges, extended by the identity.
* `ClusterAlgebras.PlabicData.excisionDarts`: the darts `H°` of the excision.
* `ClusterAlgebras.PlabicData.edgeExcision`: the excision `K ⊖ 𝓔` of a set of edges.
* `ClusterAlgebras.RotationSystem.ArcLoopStep`: the steps of the separation lemma for a loop.

## Main results

* `ClusterAlgebras.DiskMap.IsDiskMap.hollowDigon_shape`: the shape of a hollow digon.
* `ClusterAlgebras.DiskMap.IsDiskMap.loop_separates`: a loop separates a disk map;
  `RotationSystem.IsConnected.loop_separates` is the same for a
  connected rotation system satisfying Euler's relation.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.hasRoundtrip_of_loop`: a loop gives a roundtrip.

## Implementation notes

* **Excised darts.** The first-return map `σ_X` is a permutation of the subtype `H \ X`; it is
  extended by the identity on `X` to a permutation `excisionRot` of `H`, so that the darts of the
  excision form a `Finset H` and the rotation and the involution of the excision are restrictions
  of permutations of `H`. The excision is defined for any set of edges; that the edges are edges of
  the graph is used, with the plabic graph conditions, to give each labelled boundary vertex a
  dart in `H°`. Nonemptiness of `𝓔` is not needed for the construction.
* **Labels.** The boundary labelling of the excision is that of `K`. It is recorded, as throughout
  the chapter, by a dart `leg i` at the vertex labelled `i`: the leg `g_i` of `K` if it survives,
  and otherwise the dart `σ(g_i) ∈ B` of the same vertex.
* **Rotations as lists.** The rotation `(d, a₁, …, a_k, d̄, b₁, …, b_l)` at a vertex is the list
  `Equiv.Perm.toList σ d` of Mathlib, the cycle of `σ` through `d` read from `d`; the hypothesis
  is `σ.toList d = d :: as ++ d̄ :: bs`, with `A` and `B_u` the darts of the lists `as` and `bs`.
* **Sequences of steps.** A finite sequence of steps `z₀, …, z_n` is the reflexive transitive
  closure `Relation.ReflTransGen` of the step relation.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Hollow digons -/

namespace DiskMap

variable {H : Type*} [Fintype H] [DecidableEq H] {M : DiskMap H}

namespace IsDiskMap

variable (hM : M.IsDiskMap)

include hM

/-- In a disk map, the boundary `M.bdry` is nonempty. -/
theorem bdry_nonempty : M.bdry.Nonempty := by
  obtain ⟨f, hf, hfB, -, -⟩ := hM.exists_orbit
  obtain ⟨x, rfl⟩ := M.mem_faceOrbits.1 hf
  exact ⟨x, hfB (M.self_mem_faceOf x)⟩

/-- In a disk map, `σ` cannot fix both a dart `x ∉ B` and its reverse `x̄`. -/
theorem not_rot_eq_self_and_rot_inv_eq {x : H} (hx : x ∉ M.bdry) (h₁ : M.rot x = x)
    (h₂ : M.rot (M.inv x) = M.inv x) : False := by
  obtain ⟨y, hy⟩ := hM.bdry_nonempty
  have key : ∀ e, M.Reach x e → e = x ∨ e = M.inv x := by
    intro e he
    induction he with
    | refl => exact Or.inl rfl
    | rot _ ih =>
      rcases ih with rfl | rfl
      · exact Or.inl h₁
      · exact Or.inr h₂
    | inv _ ih =>
      rcases ih with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (hM.inv_involutive _)
  rcases key y (hM.reach x y) with rfl | rfl
  · exact hx hy
  · exact hx (hM.inv_mem_bdry_iff.1 hy)

/-- **The shape of a hollow digon**: if `{d₁, d₂}` is a hollow digon of
a disk map, then `v(d₁)` and `v(d₂)` are internal vertices, `v(d₁)` contains the two distinct
darts `d₁` and `d̄₂ = σ⁻¹(d₁)`, and `v(d₂)` contains the two distinct darts `d₂` and
`d̄₁ = σ⁻¹(d₂)`. -/
@[cluster_algebras "lem_hollow_digon_shape"]
theorem hollowDigon_shape {d₁ d₂ : H} (h : M.IsHollowDigon {d₁, d₂}) :
    ¬M.IsBoundaryVertex (M.vertexOf d₁) ∧ ¬M.IsBoundaryVertex (M.vertexOf d₂) ∧
      (d₁ ∈ M.vertexOf d₁ ∧ M.inv d₂ ∈ M.vertexOf d₁ ∧ d₁ ≠ M.inv d₂ ∧
        M.rot.symm d₁ = M.inv d₂) ∧
      (d₂ ∈ M.vertexOf d₂ ∧ M.inv d₁ ∈ M.vertexOf d₂ ∧ d₂ ≠ M.inv d₁ ∧
        M.rot.symm d₂ = M.inv d₁) := by
  obtain ⟨hint, e₁, e₂, hf, hne⟩ := h
  obtain ⟨hfaces, hdisj⟩ := M.mem_internalFaces.1 hint
  obtain ⟨x, hx⟩ := M.mem_faceOrbits.1 (M.mem_faces.1 hfaces).2
  have hd₁B : d₁ ∉ M.bdry := disjoint_left.1 hdisj (by simp)
  have hd₂B : d₂ ∉ M.bdry := disjoint_left.1 hdisj (by simp)
  have hd₁₂ : d₁ ≠ d₂ := by
    rintro rfl
    have h₁ : e₁ ∈ ({d₁, d₁} : Finset H) := hf ▸ by simp
    have h₂ : e₂ ∈ ({d₁, d₁} : Finset H) := hf ▸ by simp
    simp only [mem_insert, mem_singleton, or_self] at h₁ h₂
    exact hne (by rw [h₁, h₂])
  have hface : ∀ y ∈ ({d₁, d₂} : Finset H), M.faceOf y = {d₁, d₂} := fun y hy =>
    (M.faceOf_eq_of_mem (hx ▸ hy)).trans hx
  -- `φ` swaps `d₁` and `d₂`
  have hswap : ∀ y z, M.faceOf y = {y, z} → y ≠ z → M.facePerm y = z := by
    intro y z hyz hne
    have hmem : M.facePerm y ∈ ({y, z} : Finset H) := hyz ▸ M.facePerm_mem_faceOf y
    rcases mem_insert.1 hmem with h | h
    · exfalso
      have hz : z ∈ M.faceOf y := hyz ▸ by simp
      exact hne ((M.mem_faceOf.1 hz).eq_of_left h)
    · exact mem_singleton.1 h
  have hφ₁ : M.facePerm d₁ = d₂ := hswap d₁ d₂ (hface d₁ (by simp)) hd₁₂
  have hφ₂ : M.facePerm d₂ = d₁ :=
    hswap d₂ d₁ ((hface d₂ (by simp)).trans (pair_comm _ _)) hd₁₂.symm
  rw [RotationSystem.facePerm_apply] at hφ₁ hφ₂
  have hs₁ : M.rot.symm d₁ = M.inv d₂ := by rw [← hφ₂, Equiv.symm_apply_apply]
  have hs₂ : M.rot.symm d₂ = M.inv d₁ := by rw [← hφ₁, Equiv.symm_apply_apply]
  have hm₁ : M.inv d₂ ∈ M.vertexOf d₁ := hs₁ ▸ M.rot_symm_mem_vertexOf d₁
  have hm₂ : M.inv d₁ ∈ M.vertexOf d₂ := hs₂ ▸ M.rot_symm_mem_vertexOf d₂
  have hne₁ : d₁ ≠ M.inv d₂ := by
    intro h
    have h' : M.inv d₁ = d₂ := by rw [h, hM.inv_involutive]
    refine hM.not_rot_eq_self_and_rot_inv_eq hd₁B ?_ ?_
    · conv_lhs => rw [h]
      rw [hφ₂]
    · rw [hφ₁, h']
  have hne₂ : d₂ ≠ M.inv d₁ := by
    intro h
    apply hne₁
    rw [h, hM.inv_involutive]
  refine ⟨fun hv => hne₁ ?_, fun hv => hne₂ ?_, ⟨M.self_mem_vertexOf d₁, hm₁, hne₁, hs₁⟩,
    ⟨M.self_mem_vertexOf d₂, hm₂, hne₂, hs₂⟩⟩
  · exact eq_of_notMem_bdry hM.boundaryVertex_card hv (M.self_mem_vertexOf d₁) hm₁ hd₁B
      (mt hM.inv_mem_bdry_iff.1 hd₂B)
  · exact eq_of_notMem_bdry hM.boundaryVertex_card hv (M.self_mem_vertexOf d₂) hm₂ hd₂B
      (mt hM.inv_mem_bdry_iff.1 hd₁B)

end IsDiskMap

end DiskMap

/-! ### Excision of edges -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-- The first-return map `σ_X` of the rotation to `H \ X`, where `X` is the set of darts of a set
`𝓔` of edges, extended by the identity on `X`. -/
noncomputable def excisionRot (𝓔 : Finset (Finset H)) : Equiv.Perm H :=
  Equiv.Perm.ofSubtype (firstReturnPerm G.rot ((↑(𝓔.biUnion id) : Set H)ᶜ))

/-- A **step of the excision** of `𝓔`: between two darts of `H \ X`, a step `z ↦ σ_X^{±1}(z)` or
`z ↦ z̄`, where `X` is the set of darts of `𝓔`. -/
def ExcisionStep (𝓔 : Finset (Finset H)) (z z' : H) : Prop :=
  z ∉ 𝓔.biUnion id ∧ z' ∉ 𝓔.biUnion id ∧
    (z' = G.excisionRot 𝓔 z ∨ z = G.excisionRot 𝓔 z' ∨ z' = G.inv z)

open scoped Classical in
/-- The darts `H°` of the excision of `𝓔`: the darts of `H \ X` joined to a dart of `B` by a finite
sequence of steps `z ↦ σ_X^{±1}(z)` and `z ↦ z̄` inside `H \ X`, where `X` is the set of darts
of `𝓔`. -/
noncomputable def excisionDarts (𝓔 : Finset (Finset H)) : Finset H :=
  {z | z ∉ 𝓔.biUnion id ∧ ∃ x ∈ G.bdry, x ∉ 𝓔.biUnion id ∧
    Relation.ReflTransGen (G.ExcisionStep 𝓔) x z}

variable {G}

/-- On a dart `z ∉ X`, `σ_X(z)` is the first return of `σ` to `H \ X` from `z`. -/
theorem excisionRot_apply_of_notMem {𝓔 : Finset (Finset H)} {z : H} (hz : z ∉ 𝓔.biUnion id) :
    G.excisionRot 𝓔 z =
      (firstReturn G.rot ((↑(𝓔.biUnion id) : Set H)ᶜ) ⟨z, by simpa using hz⟩ : H) := by
  rw [excisionRot, Equiv.Perm.ofSubtype_apply_of_mem _ (by simpa using hz)]
  rfl

/-- `σ_X` fixes every dart of `X`. -/
theorem excisionRot_apply_of_mem {𝓔 : Finset (Finset H)} {z : H} (hz : z ∈ 𝓔.biUnion id) :
    G.excisionRot 𝓔 z = z :=
  Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simpa using hz)

/-- `σ_X(z)` lies in `X` if and only if `z` does. -/
theorem excisionRot_mem_iff {𝓔 : Finset (Finset H)} {z : H} :
    G.excisionRot 𝓔 z ∈ 𝓔.biUnion id ↔ z ∈ 𝓔.biUnion id := by
  by_cases hz : z ∈ 𝓔.biUnion id
  · rw [excisionRot_apply_of_mem hz]
  · rw [excisionRot_apply_of_notMem hz]
    refine iff_of_false ?_ hz
    simpa using (firstReturn G.rot ((↑(𝓔.biUnion id) : Set H)ᶜ) ⟨z, by simpa using hz⟩).2

/-- If `σ(z) ∉ X`, then `σ_X(z) = σ(z)`. -/
theorem excisionRot_apply_of_rot_notMem {𝓔 : Finset (Finset H)} {z : H} (hz : z ∉ 𝓔.biUnion id)
    (hσ : G.rot z ∉ 𝓔.biUnion id) : G.excisionRot 𝓔 z = G.rot z := by
  rw [excisionRot_apply_of_notMem hz]
  exact coe_firstReturn_of_apply_mem (by simpa using hσ)

/-- A dart lies in `H°` if and only if it lies outside `X` and is joined to a dart of `B` outside
`X` by a finite sequence of excision steps. -/
theorem mem_excisionDarts {𝓔 : Finset (Finset H)} {z : H} :
    z ∈ G.excisionDarts 𝓔 ↔ z ∉ 𝓔.biUnion id ∧ ∃ x ∈ G.bdry, x ∉ 𝓔.biUnion id ∧
      Relation.ReflTransGen (G.ExcisionStep 𝓔) x z := by
  classical
  simp [excisionDarts]

/-- A dart of `H°` lies outside `X`. -/
theorem notMem_of_mem_excisionDarts {𝓔 : Finset (Finset H)} {z : H}
    (hz : z ∈ G.excisionDarts 𝓔) : z ∉ 𝓔.biUnion id :=
  (mem_excisionDarts.1 hz).1

/-- The darts of `H°` are closed under steps. -/
theorem mem_excisionDarts_of_step {𝓔 : Finset (Finset H)} {z z' : H}
    (hz : z ∈ G.excisionDarts 𝓔) (h : G.ExcisionStep 𝓔 z z') : z' ∈ G.excisionDarts 𝓔 := by
  obtain ⟨-, x, hx, hxX, hxz⟩ := mem_excisionDarts.1 hz
  exact mem_excisionDarts.2 ⟨h.2.1, x, hx, hxX, hxz.tail h⟩

/-- A dart of `B` outside `X` lies in `H°`. -/
theorem mem_excisionDarts_of_mem_bdry {𝓔 : Finset (Finset H)} {z : H} (hz : z ∈ G.bdry)
    (hzX : z ∉ 𝓔.biUnion id) : z ∈ G.excisionDarts 𝓔 :=
  mem_excisionDarts.2 ⟨hzX, z, hz, hzX, Relation.ReflTransGen.refl⟩

/-- `σ_X(z)` lies in `H°` if and only if `z` does. -/
theorem excisionRot_mem_excisionDarts_iff {𝓔 : Finset (Finset H)} {z : H} :
    G.excisionRot 𝓔 z ∈ G.excisionDarts 𝓔 ↔ z ∈ G.excisionDarts 𝓔 := by
  constructor
  · intro h
    have hX := notMem_of_mem_excisionDarts h
    exact mem_excisionDarts_of_step h ⟨hX, excisionRot_mem_iff.not.1 hX, Or.inr (Or.inl rfl)⟩
  · intro h
    have hX := notMem_of_mem_excisionDarts h
    exact mem_excisionDarts_of_step h ⟨hX, excisionRot_mem_iff.not.2 hX, Or.inl rfl⟩

/-- If `X` is closed under the involution, then so is `H°`. -/
theorem inv_mem_excisionDarts_iff {𝓔 : Finset (Finset H)} (hinv : Function.Involutive G.inv)
    (hX : ∀ x ∈ 𝓔.biUnion id, G.inv x ∈ 𝓔.biUnion id) {z : H} :
    G.inv z ∈ G.excisionDarts 𝓔 ↔ z ∈ G.excisionDarts 𝓔 := by
  have key : ∀ z, z ∈ G.excisionDarts 𝓔 → G.inv z ∈ G.excisionDarts 𝓔 := by
    intro z h
    have hzX := notMem_of_mem_excisionDarts h
    refine mem_excisionDarts_of_step h ⟨hzX, fun h' => hzX ?_, Or.inr (Or.inr rfl)⟩
    simpa [hinv z] using hX _ h'
  exact ⟨fun h => hinv z ▸ key _ h, key z⟩

/-- The set of darts of a set of edges of a plabic graph is closed under the involution. -/
theorem inv_mem_biUnion_of_subset_edges (hG : G.IsPlabicGraph) {𝓔 : Finset (Finset H)}
    (h𝓔 : 𝓔 ⊆ G.edges) {x : H} (hx : x ∈ 𝓔.biUnion id) : G.inv x ∈ 𝓔.biUnion id := by
  obtain ⟨e, he, hxe⟩ := mem_biUnion.1 hx
  obtain ⟨y, rfl⟩ := G.mem_edges.1 (h𝓔 he)
  refine mem_biUnion.2 ⟨_, he, ?_⟩
  simp only [id, RotationSystem.mem_edgeOf] at hxe ⊢
  rcases hxe with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (hG.inv_involutive y)

/-- If no edge of `𝓔` meets `B`, then every dart of `B` lies in `H°`. -/
theorem bdry_subset_excisionDarts {𝓔 : Finset (Finset H)} (h𝓔B : ∀ e ∈ 𝓔, Disjoint e G.bdry) :
    G.bdry ⊆ G.excisionDarts 𝓔 := fun z hz =>
  mem_excisionDarts_of_mem_bdry hz fun h => by
    obtain ⟨e, he, hze⟩ := mem_biUnion.1 h
    exact disjoint_left.1 (h𝓔B e he) hze hz

/-- In a plabic graph, `σ(g_i)` lies in `B`. -/
theorem IsPlabicGraph.rot_leg_mem_bdry (hG : G.IsPlabicGraph) (i : Fin b) :
    G.rot (G.leg i) ∈ G.bdry := by
  have hv : G.IsBoundaryVertex (G.vertexOf (G.leg i)) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  by_contra h
  exact DiskMap.rot_ne_of_isBoundaryVertex hG.boundaryVertex_card hv
    (DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card hv (G.rot_mem_vertexOf _)
      (G.self_mem_vertexOf _) h (hG.leg_notMem_bdry i))

/-- In a plabic graph, if no edge of `𝓔` meets `B`, then `σ(g_i)` lies in `H°`. -/
theorem IsPlabicGraph.rot_leg_mem_excisionDarts (hG : G.IsPlabicGraph) {𝓔 : Finset (Finset H)}
    (h𝓔B : ∀ e ∈ 𝓔, Disjoint e G.bdry) (i : Fin b) :
    G.rot (G.leg i) ∈ G.excisionDarts 𝓔 :=
  bdry_subset_excisionDarts h𝓔B (hG.rot_leg_mem_bdry i)

variable (G)

/-- The **excision** `K ⊖ 𝓔` of a set `𝓔` of edges of the graph of a plabic graph `K`.
With `X` the set of darts of `𝓔` and `σ_X` the first-return map of `σ` to
`H \ X`, it is the tuple `(H°, d ↦ d̄, σ_X, B, κ°, β)` on the set `H°` of darts of `H \ X` joined
to `B` by steps `z ↦ σ_X^{±1}(z)` and `z ↦ z̄` inside `H \ X` (`excisionDarts`), with the
involution and `σ_X` restricted to `H°`, the colour of each dart that of its vertex in `K`, and
the boundary vertices labelled as in `K`: the vertex labelled `i` is recorded by the leg `g_i` if
`g_i ∈ H°`, and otherwise by the dart `σ(g_i) ∈ B` of the same vertex. -/
@[cluster_algebras "def_edge_excision"]
noncomputable def edgeExcision (hG : G.IsPlabicGraph) (𝓔 : Finset (Finset H)) (h𝓔 : 𝓔 ⊆ G.edges)
    (h𝓔B : ∀ e ∈ 𝓔, Disjoint e G.bdry) : PlabicData (G.excisionDarts 𝓔) b where
  inv := G.inv.subtypePerm fun _ =>
    inv_mem_excisionDarts_iff hG.inv_involutive fun _ hx => inv_mem_biUnion_of_subset_edges hG h𝓔 hx
  rot := (G.excisionRot 𝓔).subtypePerm fun _ => excisionRot_mem_excisionDarts_iff
  bdry := G.bdry.subtype (· ∈ G.excisionDarts 𝓔)
  colour z := G.colour z
  leg i :=
    if h : G.leg i ∈ G.excisionDarts 𝓔 then ⟨G.leg i, h⟩
    else ⟨G.rot (G.leg i), hG.rot_leg_mem_excisionDarts h𝓔B i⟩

variable {G}

section edgeExcision

variable {hG : G.IsPlabicGraph} {𝓔 : Finset (Finset H)} {h𝓔 : 𝓔 ⊆ G.edges}
  {h𝓔B : ∀ e ∈ 𝓔, Disjoint e G.bdry}

/-- The involution of `K ⊖ 𝓔` is the restriction of that of `K`. -/
@[simp]
theorem coe_edgeExcision_inv (z : G.excisionDarts 𝓔) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).inv z : H) = G.inv z := rfl

/-- The rotation of `K ⊖ 𝓔` is the restriction of `σ_X`. -/
@[simp]
theorem coe_edgeExcision_rot (z : G.excisionDarts 𝓔) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).rot z : H) = G.excisionRot 𝓔 z := rfl

/-- A dart of `H°` lies in the boundary of `K ⊖ 𝓔` if and only if it lies in `B`. -/
@[simp]
theorem mem_edgeExcision_bdry {z : G.excisionDarts 𝓔} :
    z ∈ (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).bdry ↔ (z : H) ∈ G.bdry := by
  simp [edgeExcision]

/-- The colour of a dart of `K ⊖ 𝓔` is its colour in `K`. -/
@[simp]
theorem edgeExcision_colour (z : G.excisionDarts 𝓔) :
    (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).colour z = G.colour z := rfl

/-- If `g_i ∈ H°`, then the `i`-th leg of `K ⊖ 𝓔` is `g_i`. -/
theorem coe_edgeExcision_leg_of_mem {i : Fin b} (h : G.leg i ∈ G.excisionDarts 𝓔) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).leg i : H) = G.leg i := by
  simp [edgeExcision, h]

/-- If `g_i ∉ H°`, then the `i`-th leg of `K ⊖ 𝓔` is `σ(g_i)`. -/
theorem coe_edgeExcision_leg_of_notMem {i : Fin b} (h : G.leg i ∉ G.excisionDarts 𝓔) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).leg i : H) = G.rot (G.leg i) := by
  simp [edgeExcision, h]

end edgeExcision

end PlabicData

/-! ### Cycles of a permutation read as lists -/

section CyclicList

variable {α : Type*} [Fintype α] [DecidableEq α] {p : Equiv.Perm α} {x y : α} {as bs : List α}

/-- `p` maps the `i`-th entry of its cycle through `x` to the next entry, cyclically. -/
theorem apply_getElem_toList (p : Equiv.Perm α) (x : α) (i : ℕ) (hi : i < (p.toList x).length) :
    p (p.toList x)[i] = (p.toList x)[(i + 1) % (p.toList x).length]'(Nat.mod_lt _ (by omega)) := by
  rw [← Equiv.Perm.next_toList_eq_apply p x _ (List.getElem_mem hi)]
  exact List.next_getElem _ (Equiv.Perm.nodup_toList p x) i hi

/-- If the cycle of `p` through `x` is the list `l`, then `p` maps the `i`-th entry of `l` to the
next entry, cyclically. -/
theorem apply_getElem_of_toList_eq {l : List α} (hl : p.toList x = l) (i : ℕ)
    (hi : i < l.length) : p l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
  subst hl
  exact apply_getElem_toList p x i hi

/-- If the cycle of `p` through `x` is `(x, a₁, …, a_k, y, …)`, then `p` maps `x` and each `a_i` to
some `a_j` or to `y`. -/
theorem apply_mem_or_eq_of_toList (hL : p.toList x = x :: as ++ y :: bs) {z : α}
    (hz : z ∈ x :: as) : p z ∈ as ∨ p z = y := by
  have key := apply_getElem_of_toList_eq hL
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  simp only [List.length_cons] at hi
  have hl : i < (x :: as ++ y :: bs).length := by simp; omega
  have h1 : (x :: as)[i] = (x :: as ++ y :: bs)[i] := (List.getElem_append_left _).symm
  rw [h1, key i hl]
  have hmod : (i + 1) % (x :: as ++ y :: bs).length = i + 1 := Nat.mod_eq_of_lt (by simp; omega)
  simp only [hmod]
  rcases Nat.lt_or_ge i as.length with h | h
  · left
    have e : (x :: as ++ y :: bs)[i + 1]'(by simp; omega) = as[i] := by
      simp [List.getElem_append_left h]
    rw [e]
    exact List.getElem_mem h
  · right
    have : i = as.length := by omega
    subst this
    simp

/-- The cycle `(x, a₁, …, a_k, y, b₁, …, b_l)` read from `y`. -/
theorem toList_eq_of_toList (hL : p.toList x = x :: as ++ y :: bs) :
    p.toList y = y :: bs ++ x :: as := by
  have hy : y = (p ^ (as.length + 1)) x := by
    have hlen : as.length + 1 < (p.toList x).length := by rw [hL]; simp
    rw [← Equiv.Perm.getElem_toList (p := p) (x := x) (n := as.length + 1) hlen,
      List.getElem_of_eq hL]
    simp [List.getElem_append_right]
  rw [hy, Equiv.Perm.toList_pow_apply_eq_rotate, hL, ← hy]
  exact List.rotate_append_length_eq (x :: as) (y :: bs)

/-- If the cycle of `p` through `x` is `(x, a₁, …, a_k, y, b₁, …, b_l)`, then `z` is an entry of it
if and only if `z` is in the same cycle of `p` as `x`. -/
theorem mem_toList_of_toList (hL : p.toList x = x :: as ++ y :: bs) {z : α} :
    z ∈ p.toList x ↔ p.SameCycle x z := by
  rw [Equiv.Perm.mem_toList_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  by_contra hx
  have := Equiv.Perm.toList_eq_nil_iff.2 hx
  rw [hL] at this
  simp at this

/-- If the cycle of `p` through `x` is `(x, a₁, …, a_k, y, b₁, …, b_l)`, then its entries are
distinct. -/
theorem nodup_of_toList (hL : p.toList x = x :: as ++ y :: bs) :
    (x :: as ++ y :: bs).Nodup := hL ▸ Equiv.Perm.nodup_toList p x

/-- If the cycle of `p` through `x` is `(x, a₁, …, a_k, y, …)`, then no `a_i` is `x` or `y`. -/
theorem ne_and_ne_of_mem_of_toList (hL : p.toList x = x :: as ++ y :: bs) {a : α} (ha : a ∈ as) :
    a ≠ x ∧ a ≠ y := by
  have hnd := nodup_of_toList hL
  simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons, not_or,
    List.nodup_append] at hnd
  exact ⟨fun h => hnd.1.1 (h ▸ ha), fun h => hnd.2.2.2 y (h ▸ ha) y (by simp) rfl⟩

/-- If the cycle of `p` through `x` is `(x, a₁, …, a_k, y, …)`, then `p` maps only `x` and the
`a_i` into `{a₁, …, a_k, y}`. -/
theorem eq_or_mem_of_apply_mem_or_eq (hL : p.toList x = x :: as ++ y :: bs) {z : α}
    (hz : p z ∈ as ∨ p z = y) : z = x ∨ z ∈ as := by
  have hnd := nodup_of_toList hL
  have hpz : p z ∈ p.toList x := by rw [hL]; rcases hz with h | h <;> simp [h]
  have hzL : z ∈ p.toList x :=
    (mem_toList_of_toList hL).2
      (Equiv.Perm.sameCycle_apply_right.1 ((mem_toList_of_toList hL).1 hpz))
  rw [hL] at hzL
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hzL
  rcases hzL with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    subst h
    have := apply_mem_or_eq_of_toList (toList_eq_of_toList hL) (z := z) (by simp)
    simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons, not_or,
      List.nodup_append] at hnd
    grind
  · exfalso
    have := apply_mem_or_eq_of_toList (toList_eq_of_toList hL) (z := z) (by simp [h])
    simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons, not_or,
      List.nodup_append] at hnd
    grind

/-- If the cycle of `p` through `x` is `(x, a₁, …, a_k, y, …)` with `1 ≤ k`, then `p x = a₁` is
one of the `a_i`. -/
theorem apply_mem_of_toList (hL : p.toList x = x :: as ++ y :: bs) (h : as ≠ []) : p x ∈ as := by
  have key := apply_getElem_of_toList_eq hL 0 (by simp)
  have hmod : (0 + 1) % (x :: as ++ y :: bs).length = 1 :=
    Nat.mod_eq_of_lt (by simp)
  simp only [hmod] at key
  have e1 : (x :: as ++ y :: bs)[0] = x := by simp
  have e2 : (x :: as ++ y :: bs)[1]'(by simp) = as[0]'(List.length_pos_iff.2 h) := by
    simp [List.getElem_append_left (List.length_pos_iff.2 h)]
  rw [e1, e2] at key
  rw [key]
  exact List.getElem_mem _

/-- Along the cycle `(x, a₁, …, a_k, y, …)` of `p`, the permutation `p ∘ (x y)` carries each `a_i`
to `y`. -/
theorem sameCycle_mul_swap_of_mem (hL : p.toList x = x :: as ++ y :: bs) {a : α} (ha : a ∈ as) :
    (p * Equiv.swap x y).SameCycle a y := by
  have hnd := nodup_of_toList hL
  simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons, not_or,
    List.nodup_append] at hnd
  have hxas : x ∉ as := hnd.1.1
  have hyas : y ∉ as := fun h => (hnd.2.2.2 y h y (by simp)) rfl
  have hxy : x ≠ y := hnd.1.2.1
  by_contra hne
  have key : ∀ n : ℕ, ((p * Equiv.swap x y) ^ n) a ∈ as ∧
      ((p * Equiv.swap x y) ^ n) a = (p ^ n) a := by
    intro n
    induction n with
    | zero => exact ⟨ha, rfl⟩
    | succ n ih =>
      obtain ⟨hw, hwe⟩ := ih
      have hwx : ((p * Equiv.swap x y) ^ n) a ≠ x := fun h => hxas (h ▸ hw)
      have hwy : ((p * Equiv.swap x y) ^ n) a ≠ y := fun h => hyas (h ▸ hw)
      have hτ : ((p * Equiv.swap x y) ^ (n + 1)) a = p (((p * Equiv.swap x y) ^ n) a) := by
        rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hwx hwy]
      rcases apply_mem_or_eq_of_toList hL (List.mem_cons_of_mem _ hw) with h | h
      · refine ⟨hτ ▸ h, ?_⟩
        rw [hτ, hwe, pow_succ', Equiv.Perm.mul_apply]
      · exact absurd ⟨((n + 1 : ℕ) : ℤ), by rw [zpow_natCast, hτ, h]⟩ hne
  have hxa : p.SameCycle x a := by
    have : a ∈ p.toList x := by rw [hL]; simp [ha]
    exact ((mem_toList_of_toList hL).1 this)
  obtain ⟨n, hn⟩ := hxa.symm.exists_nat_pow_eq
  obtain ⟨h1, h2⟩ := key n
  exact hxas (by rw [← hn, ← h2]; exact h1)

end CyclicList

namespace RotationSystem

variable {H : Type*} [Fintype H] [DecidableEq H] (R : RotationSystem H)

/-- A **step around a loop** `{d, d̄}` with sides `A` and `B`: from
a dart `z` to a dart `z'`, both outside `{d, d̄}`, one of `z' = z̄`; `z' = σ^{±1}(z)` with `z` not
at the vertex `v(d)`; `z, z' ∈ A`; `z, z' ∈ B`. -/
def ArcLoopStep (d : H) (A B : List H) (z z' : H) : Prop :=
  z ≠ d ∧ z ≠ R.inv d ∧ z' ≠ d ∧ z' ≠ R.inv d ∧
    (z' = R.inv z ∨ ((z' = R.rot z ∨ z' = R.rot.symm z) ∧ z ∉ R.vertexOf d) ∨
      (z ∈ A ∧ z' ∈ A) ∨ (z ∈ B ∧ z' ∈ B))

/-- A rotation system whose involution is fixed-point-free has half as many edges as darts. -/
private theorem two_mul_card_edges (hinv : Function.Involutive R.inv) (hfix : ∀ d, R.inv d ≠ d) :
    2 * R.edges.card = Fintype.card H := by
  have hfib : ∀ s ∈ univ.image R.edgeOf,
      ({a ∈ univ | R.edgeOf a = s} : Finset H).card = 2 := by
    intro s hs
    obtain ⟨d, -, rfl⟩ := mem_image.1 hs
    have : ({a ∈ univ | R.edgeOf a = R.edgeOf d} : Finset H) = R.edgeOf d := by
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_edgeOf]
      constructor
      · exact fun h => R.mem_edgeOf.1 (h ▸ R.mem_edgeOf.2 (Or.inl rfl))
      · rintro (rfl | rfl)
        · rfl
        · ext x
          simp only [mem_edgeOf, hinv d]
          tauto
    rw [this, edgeOf, card_pair (hfix d).symm]
  rw [← card_univ, card_eq_sum_card_image R.edgeOf univ, sum_const_nat hfib, edges, mul_comm]

private theorem card_vertices_eq_numOrbits : R.vertices.card = numOrbits R.rot :=
  (numOrbits_eq_card_image R.rot).symm

private theorem card_faceOrbits_eq_numOrbits : R.faceOrbits.card = numOrbits R.facePerm :=
  (numOrbits_eq_card_image R.facePerm).symm

omit [Fintype H] in
private theorem card_compl_pair [Fintype H] {x y : H} (hxy : x ≠ y) :
    Fintype.card (({x, y} : Set H)ᶜ : Set H) + 2 = Fintype.card H := by
  rw [Fintype.card_subtype]
  have : ({z | z ∈ (({x, y} : Set H)ᶜ : Set H)} : Finset H) = (univ.erase x).erase y := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, mem_filter,
      mem_univ, true_and, mem_erase, ne_eq]
    tauto
  rw [this, card_erase_of_mem (by simp [Ne.symm hxy]), card_erase_of_mem (mem_univ _), card_univ]
  have : 1 < Fintype.card H := Fintype.one_lt_card_iff.2 ⟨x, y, hxy⟩
  omega

omit [Fintype H] [DecidableEq H] in
private theorem mem_compl_pair {x y z : H} :
    z ∈ (({x, y} : Set H)ᶜ : Set H) ↔ z ≠ x ∧ z ≠ y := by
  simp

omit [Fintype H] [DecidableEq H] in
private theorem exists_sameCycle_mem_compl_pair (f : Equiv.Perm H) {x y : H}
    (hx : f x ∈ (({x, y} : Set H)ᶜ : Set H)) (hy : f y ∈ (({x, y} : Set H)ᶜ : Set H)) (z : H) :
    ∃ w ∈ (({x, y} : Set H)ᶜ : Set H), f.SameCycle z w := by
  by_cases hz : z ∈ (({x, y} : Set H)ᶜ : Set H)
  · exact ⟨z, hz, Equiv.Perm.SameCycle.refl _ _⟩
  · obtain rfl | rfl : z = x ∨ z = y := by
      simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_not] using hz
    · exact ⟨_, hx, Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)⟩
    · exact ⟨_, hy, Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)⟩

private theorem notMem_vertexOf_of_mem {d z e : H} (hz : z ∉ R.vertexOf d)
    (he : e ∈ R.vertexOf z) : e ∉ R.vertexOf d := fun he' =>
  hz (R.mem_vertexOf.2 ((R.mem_vertexOf.1 he').trans (R.mem_vertexOf.1 he).symm))

/-- If the rotation at `v(d)` is `(d, a₁, …, a_k, d̄, b₁, …, b_l)`, then the darts at `v(d)` are
`d`, the `a_i`, `d̄` and the `b_j`. -/
theorem mem_vertexOf_iff_of_toList {d : H} {as bs : List H}
    (hL : R.rot.toList d = d :: as ++ R.inv d :: bs) {z : H} :
    z ∈ R.vertexOf d ↔ z = d ∨ z ∈ as ∨ z = R.inv d ∨ z ∈ bs := by
  rw [R.mem_vertexOf, ← mem_toList_of_toList hL, hL]
  simp

/-- If the rotation at `v(d)` is `(d, a₁, …, a_k, d̄, b₁, …, b_l)`, then `d̄` lies at `v(d)`. -/
theorem inv_mem_vertexOf_of_toList {d : H} {as bs : List H}
    (hL : R.rot.toList d = d :: as ++ R.inv d :: bs) : R.inv d ∈ R.vertexOf d :=
  (R.mem_vertexOf_iff_of_toList hL).2 (Or.inr (Or.inr (Or.inl rfl)))

/-- If `d̄ ≠ d` lies at `v(d)`, then the rotation at `v(d)` reads
`(d, a₁, …, a_k, d̄, b₁, …, b_l)`. -/
theorem exists_toList_eq_of_inv_mem_vertexOf {d : H} (hdι : R.inv d ≠ d)
    (hιu : R.inv d ∈ R.vertexOf d) :
    ∃ as bs : List H, R.rot.toList d = d :: as ++ R.inv d :: bs := by
  have hsupp : d ∈ R.rot.support :=
    Equiv.Perm.mem_support.2 fun h => hdι ((R.mem_vertexOf.1 hιu).eq_of_left h).symm
  obtain ⟨s, bs, hst⟩ :=
    List.append_of_mem (Equiv.Perm.mem_toList_iff.2 ⟨R.mem_vertexOf.1 hιu, hsupp⟩)
  have h0 := Equiv.Perm.toList_getElem_zero R.rot d hsupp
  rw [List.getElem_of_eq hst] at h0
  cases s with
  | nil =>
    simp only [List.nil_append, List.getElem_cons_zero] at h0
    exact absurd h0 hdι
  | cons a as =>
    simp only [List.cons_append, List.getElem_cons_zero] at h0
    subst h0
    exact ⟨as, bs, hst⟩

private noncomputable def loopCut (hι : Function.Involutive R.inv) (d : H) :
    RotationSystem (({d, R.inv d} : Set H)ᶜ : Set H) :=
  ⟨R.inv.subtypePerm (apply_mem_compl_pair_iff hι d), inducedRotationPerm R.inv R.rot d⟩

private theorem loopCut_rot (hι : Function.Involutive R.inv) (d : H) :
    (R.loopCut hι d).rot = firstReturnPerm (R.rot * Equiv.swap d (R.inv d)) ({d, R.inv d}ᶜ) :=
  rfl

private theorem loopCut_inv_involutive (hι : Function.Involutive R.inv) (d : H) :
    Function.Involutive (R.loopCut hι d).inv := fun z => Subtype.ext (hι z)

private theorem loopCut_inv_ne (hι : Function.Involutive R.inv) (hfix : ∀ z, R.inv z ≠ z) (d : H)
    (z : (({d, R.inv d} : Set H)ᶜ : Set H)) : (R.loopCut hι d).inv z ≠ z := fun h =>
  hfix z (congrArg Subtype.val h)

private theorem loopCut_rot_of_notMem (hι : Function.Involutive R.inv) {d : H}
    (hιu : R.inv d ∈ R.vertexOf d) (z : (({d, R.inv d} : Set H)ᶜ : Set H))
    (hz : (z : H) ∉ R.vertexOf d) : ((R.loopCut hι d).rot z : H) = R.rot z := by
  have hz' := mem_compl_pair.1 z.2
  have hσz : R.rot z ∉ R.vertexOf d := R.notMem_vertexOf_of_mem hz (R.rot_mem_vertexOf _)
  have hτz : (R.rot * Equiv.swap d (R.inv d)) z = R.rot z := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hz'.1 hz'.2]
  rw [loopCut_rot, coe_firstReturnPerm, coe_firstReturn_of_apply_mem, hτz]
  rw [hτz, mem_compl_pair]
  refine ⟨fun h => hσz ?_, fun h => hσz ?_⟩
  · rw [h]
    exact R.self_mem_vertexOf d
  · rw [h]
    exact hιu

private theorem loopCut_reach_of_sameCycle (hι : Function.Involutive R.inv) {d : H}
    {y y' : (({d, R.inv d} : Set H)ᶜ : Set H)}
    (h : (R.rot * Equiv.swap d (R.inv d)).SameCycle y y') : (R.loopCut hι d).Reach y y' := by
  have h' : (R.loopCut hι d).rot.SameCycle y y' := by
    rw [loopCut_rot]
    exact (sameCycle_firstReturnPerm_iff _ _).2 h
  obtain ⟨n, rfl⟩ := h'.exists_nat_pow_eq
  exact (R.loopCut hι d).reach_pow_apply (fun x => (Reach.refl x).rot) n y

private theorem loopCut_reach_of_mem_left (hι : Function.Involutive R.inv) {d : H}
    {as bs : List H} (hL : R.rot.toList d = d :: as ++ R.inv d :: bs)
    {y y' : (({d, R.inv d} : Set H)ᶜ : Set H)} (hy : (y : H) ∈ as) (hy' : (y' : H) ∈ as) :
    (R.loopCut hι d).Reach y y' :=
  R.loopCut_reach_of_sameCycle hι
    ((sameCycle_mul_swap_of_mem hL hy).trans (sameCycle_mul_swap_of_mem hL hy').symm)

private theorem loopCut_reach_of_mem_right (hι : Function.Involutive R.inv) {d : H}
    {as bs : List H} (hL : R.rot.toList d = d :: as ++ R.inv d :: bs)
    {y y' : (({d, R.inv d} : Set H)ᶜ : Set H)} (hy : (y : H) ∈ bs) (hy' : (y' : H) ∈ bs) :
    (R.loopCut hι d).Reach y y' := by
  have h := (sameCycle_mul_swap_of_mem (toList_eq_of_toList hL) hy).trans
    (sameCycle_mul_swap_of_mem (toList_eq_of_toList hL) hy').symm
  rw [Equiv.swap_comm] at h
  exact R.loopCut_reach_of_sameCycle hι h

private theorem loopCut_reach_of_arcLoopStep (hι : Function.Involutive R.inv) {d : H}
    {as bs : List H} (hL : R.rot.toList d = d :: as ++ R.inv d :: bs) {z z' : H}
    (hz : z ∈ (({d, R.inv d} : Set H)ᶜ : Set H)) (hz' : z' ∈ (({d, R.inv d} : Set H)ᶜ : Set H))
    (h : R.ArcLoopStep d as bs z z') : (R.loopCut hι d).Reach ⟨z, hz⟩ ⟨z', hz'⟩ := by
  have hιu := R.inv_mem_vertexOf_of_toList hL
  obtain ⟨-, -, -, -, h | ⟨h | h, hzu⟩ | ⟨ha, ha'⟩ | ⟨hb, hb'⟩⟩ := h
  · subst h
    exact (Reach.refl _).inv
  · subst h
    convert (Reach.refl (R := R.loopCut hι d) ⟨z, hz⟩).rot using 1
    exact Subtype.ext (R.loopCut_rot_of_notMem hι hιu ⟨z, hz⟩ hzu).symm
  · have hz'u : z' ∉ R.vertexOf d := R.notMem_vertexOf_of_mem hzu (h ▸ R.rot_symm_mem_vertexOf z)
    refine Reach.symm ?_
    convert (Reach.refl (R := R.loopCut hι d) ⟨z', hz'⟩).rot using 1
    apply Subtype.ext
    rw [R.loopCut_rot_of_notMem hι hιu ⟨z', hz'⟩ hz'u]
    change z = R.rot z'
    rw [h, Equiv.apply_symm_apply]
  · exact R.loopCut_reach_of_mem_left hι hL (y := ⟨z, hz⟩) (y' := ⟨z', hz'⟩) ha ha'
  · exact R.loopCut_reach_of_mem_right hι hL (y := ⟨z, hz⟩) (y' := ⟨z', hz'⟩) hb hb'

private theorem exists_loopCut_reach_side (hR : R.IsConnected) (hι : Function.Involutive R.inv)
    {d : H} {as bs : List H} (hL : R.rot.toList d = d :: as ++ R.inv d :: bs)
    (w : (({d, R.inv d} : Set H)ᶜ : Set H)) :
    ∃ y : (({d, R.inv d} : Set H)ᶜ : Set H), ((y : H) ∈ as ∨ (y : H) ∈ bs) ∧
      (R.loopCut hι d).Reach w y := by
  have hmemu := fun z => R.mem_vertexOf_iff_of_toList hL (z := z)
  have hdu := R.self_mem_vertexOf d
  have hιu := R.inv_mem_vertexOf_of_toList hL
  have main : ∀ e, R.Reach (w : H) e →
      (∃ y : (({d, R.inv d} : Set H)ᶜ : Set H), ((y : H) ∈ as ∨ (y : H) ∈ bs) ∧
        (R.loopCut hι d).Reach w y) ∨
      (e ∉ R.vertexOf d ∧ ∃ he : e ∈ (({d, R.inv d} : Set H)ᶜ : Set H),
        (R.loopCut hι d).Reach w ⟨e, he⟩) := by
    intro e he
    induction he with
    | refl =>
      by_cases hw : (w : H) ∈ R.vertexOf d
      · left
        have hw' := mem_compl_pair.1 w.2
        rcases (hmemu w).1 hw with h | h | h | h
        · exact absurd h hw'.1
        · exact ⟨w, Or.inl h, Reach.refl _⟩
        · exact absurd h hw'.2
        · exact ⟨w, Or.inr h, Reach.refl _⟩
      · exact Or.inr ⟨hw, w.2, Reach.refl _⟩
    | @rot e _ ih =>
      rcases ih with h | ⟨heu, heY, hr⟩
      · exact Or.inl h
      · have hσe : R.rot e ∉ R.vertexOf d := R.notMem_vertexOf_of_mem heu (R.rot_mem_vertexOf _)
        have hσeY : R.rot e ∈ (({d, R.inv d} : Set H)ᶜ : Set H) :=
          mem_compl_pair.2 ⟨fun h => hσe (h ▸ hdu), fun h => hσe (h ▸ hιu)⟩
        refine Or.inr ⟨hσe, hσeY, ?_⟩
        convert hr.rot using 1
        exact Subtype.ext (R.loopCut_rot_of_notMem hι hιu ⟨e, heY⟩ heu).symm
    | @inv e _ ih =>
      rcases ih with h | ⟨heu, heY, hr⟩
      · exact Or.inl h
      · have hιeY := (apply_mem_compl_pair_iff hι d e).2 heY
        have hr' : (R.loopCut hι d).Reach w ⟨R.inv e, hιeY⟩ := hr.inv
        by_cases hιe : R.inv e ∈ R.vertexOf d
        · left
          have h' := mem_compl_pair.1 hιeY
          rcases (hmemu _).1 hιe with h | h | h | h
          · exact absurd h h'.1
          · exact ⟨_, Or.inl h, hr'⟩
          · exact absurd h h'.2
          · exact ⟨_, Or.inr h, hr'⟩
        · exact Or.inr ⟨hιe, hιeY, hr'⟩
  rcases main d (hR.reach w d) with h | ⟨h, -⟩
  · exact h
  · exact absurd hdu h

private theorem card_vertices_loopCut (hι : Function.Involutive R.inv) {d : H} {as bs : List H}
    (hL : R.rot.toList d = d :: as ++ R.inv d :: bs) (hk : as ≠ []) (hl : bs ≠ [])
    (hdι : d ≠ R.inv d) : (R.loopCut hι d).vertices.card = R.vertices.card + 1 := by
  have hL' := toList_eq_of_toList hL
  have hY := exists_sameCycle_mem_compl_pair (R.rot * Equiv.swap d (R.inv d)) (x := d)
    (y := R.inv d)
    (by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      exact mem_compl_pair.2 (ne_and_ne_of_mem_of_toList hL' (apply_mem_of_toList hL' hl)).symm)
    (by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      exact mem_compl_pair.2 (ne_and_ne_of_mem_of_toList hL (apply_mem_of_toList hL hk)))
  rw [card_vertices_eq_numOrbits, card_vertices_eq_numOrbits, loopCut_rot,
    numOrbits_firstReturnPerm _ _ hY]
  exact numOrbits_mul_swap_of_sameCycle R.rot hdι
    (R.mem_vertexOf.1 (R.inv_mem_vertexOf_of_toList hL))

private theorem card_faceOrbits_loopCut (hι : Function.Involutive R.inv) {d : H}
    {as bs : List H} (hL : R.rot.toList d = d :: as ++ R.inv d :: bs) (hk : as ≠ [])
    (hl : bs ≠ []) : (R.loopCut hι d).faceOrbits.card = R.faceOrbits.card := by
  have hL' := toList_eq_of_toList hL
  rw [card_faceOrbits_eq_numOrbits, card_faceOrbits_eq_numOrbits]
  refine numOrbits_inducedRotationPerm_mul hι R.rot d (exists_sameCycle_mem_compl_pair _ ?_ ?_)
  · exact mem_compl_pair.2 (ne_and_ne_of_mem_of_toList hL' (apply_mem_of_toList hL' hl)).symm
  · rw [Equiv.Perm.mul_apply, hι d]
    exact mem_compl_pair.2 (ne_and_ne_of_mem_of_toList hL (apply_mem_of_toList hL hk))

private theorem card_edges_loopCut (hι : Function.Involutive R.inv) (hfix : ∀ z, R.inv z ≠ z)
    (d : H) : (R.loopCut hι d).edges.card + 1 = R.edges.card := by
  have h1 := (R.loopCut hι d).two_mul_card_edges (R.loopCut_inv_involutive hι d)
    (R.loopCut_inv_ne hι hfix d)
  have h2 := R.two_mul_card_edges hι hfix
  have h3 : Fintype.card (({d, R.inv d} : Set H)ᶜ : Set H) + 2 = Fintype.card H := by
    convert card_compl_pair (hfix d).symm
  omega

variable {R}

/-- **A loop separates a connected rotation system satisfying Euler's relation**: the form of
`DiskMap.IsDiskMap.loop_separates` for a connected rotation system with
`|V| - |E| + |Φ| = 2`. -/
theorem IsConnected.loop_separates (hR : R.IsConnected)
    (heuler : (R.vertices.card : ℤ) - R.edges.card + R.faceOrbits.card = 2) {d : H}
    {as bs : List H} (hL : R.rot.toList d = d :: as ++ R.inv d :: bs) (hk : as ≠ [])
    (hl : bs ≠ []) : ¬∃ z₀ ∈ as, ∃ z ∈ bs, Relation.ReflTransGen (R.ArcLoopStep d as bs) z₀ z := by
  rintro ⟨z₀, hz₀, z₁, hz₁, hchain⟩
  have hι := hR.inv_involutive
  have hz₀Y := mem_compl_pair.2 (ne_and_ne_of_mem_of_toList hL hz₀)
  have hz₁Y := mem_compl_pair.2 (ne_and_ne_of_mem_of_toList (toList_eq_of_toList hL) hz₁).symm
  have hchain' : ∀ z, Relation.ReflTransGen (R.ArcLoopStep d as bs) z₀ z →
      ∀ hz : z ∈ (({d, R.inv d} : Set H)ᶜ : Set H),
        (R.loopCut hι d).Reach ⟨z₀, hz₀Y⟩ ⟨z, hz⟩ := by
    intro z hz
    induction hz with
    | refl => exact fun _ => Reach.refl _
    | tail _ hbc ih =>
      exact fun _ => (ih (mem_compl_pair.2 ⟨hbc.1, hbc.2.1⟩)).trans
        (R.loopCut_reach_of_arcLoopStep hι hL _ _ hbc)
  have hto : ∀ y : (({d, R.inv d} : Set H)ᶜ : Set H), (R.loopCut hι d).Reach y ⟨z₀, hz₀Y⟩ := by
    intro y
    obtain ⟨t, ht | ht, hyt⟩ := R.exists_loopCut_reach_side hR hι hL y
    · exact hyt.trans (R.loopCut_reach_of_mem_left hι hL (y' := ⟨z₀, hz₀Y⟩) ht hz₀)
    · exact (hyt.trans (R.loopCut_reach_of_mem_right hι hL (y' := ⟨z₁, hz₁Y⟩) ht hz₁)).trans
        (hchain' z₁ hchain hz₁Y).symm
  have hconn : (R.loopCut hι d).IsConnected :=
    IsConnected.of_reach ⟨⟨z₀, hz₀Y⟩⟩ (R.loopCut_inv_involutive hι d)
      (R.loopCut_inv_ne hι hR.inv_ne d) fun y y' => (hto y).trans (hto y').symm
  have hV := R.card_vertices_loopCut hι hL hk hl (hR.inv_ne d).symm
  have hΦ := R.card_faceOrbits_loopCut hι hL hk hl
  have hE := R.card_edges_loopCut hι hR.inv_ne d
  have heul : ((R.loopCut hι d).vertices.card : ℤ) - (R.loopCut hι d).edges.card +
      (R.loopCut hι d).faceOrbits.card ≤ 2 := hconn.euler_le
  omega

/-- The steps around the loop `{d, d̄}` with sides `A`, `B` are those around `{d̄, d}` with sides
`B`, `A`. -/
theorem arcLoopStep_inv (hinv : Function.Involutive R.inv) {d : H}
    (hu : R.vertexOf (R.inv d) = R.vertexOf d) (A B : List H) :
    R.ArcLoopStep (R.inv d) B A = R.ArcLoopStep d A B := by
  funext z z'
  simp only [ArcLoopStep, hinv d, hu, eq_iff_iff]
  tauto

/-- Steps around a loop can be reversed. -/
theorem ArcLoopStep.symm (hinv : Function.Involutive R.inv) {d : H} {A B : List H} {z z' : H}
    (h : R.ArcLoopStep d A B z z') : R.ArcLoopStep d A B z' z := by
  obtain ⟨h1, h2, h3, h4, h | ⟨h | h, hzu⟩ | ⟨ha, ha'⟩ | ⟨hb, hb'⟩⟩ := h
  · exact ⟨h3, h4, h1, h2, Or.inl (by rw [h, hinv z])⟩
  · have hz'u : z' ∉ R.vertexOf d := fun h' =>
      hzu (R.mem_vertexOf.2 ((R.mem_vertexOf.1 h').trans
        (h ▸ Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)).symm))
    exact ⟨h3, h4, h1, h2, Or.inr (Or.inl ⟨Or.inr (by rw [h, Equiv.symm_apply_apply]), hz'u⟩)⟩
  · have hz'u : z' ∉ R.vertexOf d := fun h' =>
      hzu (R.mem_vertexOf.2 ((R.mem_vertexOf.1 h').trans
        (h ▸ Equiv.Perm.sameCycle_symm_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)).symm))
    exact ⟨h3, h4, h1, h2, Or.inr (Or.inl ⟨Or.inl (by rw [h, Equiv.apply_symm_apply]), hz'u⟩)⟩
  · exact ⟨h3, h4, h1, h2, Or.inr (Or.inr (Or.inl ⟨ha', ha⟩))⟩
  · exact ⟨h3, h4, h1, h2, Or.inr (Or.inr (Or.inr ⟨hb', hb⟩))⟩

/-- Sequences of steps around a loop can be reversed. -/
theorem ArcLoopStep.reflTransGen_symm (hinv : Function.Involutive R.inv) {d : H} {A B : List H}
    {x y : H} (h : Relation.ReflTransGen (R.ArcLoopStep d A B) x y) :
    Relation.ReflTransGen (R.ArcLoopStep d A B) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hbc.symm hinv) ih

end RotationSystem

namespace DiskMap.IsDiskMap

variable {H : Type*} [Fintype H] [DecidableEq H] {M : DiskMap H}

/-- **A loop separates a disk map**: let `u = v(d)` be a vertex of a disk map whose rotation is
`(d, a₁, …, a_k, d̄, b₁, …, b_l)` with `k, l ≥ 1`, that is, `σ.toList d = d :: as ++ d̄ :: bs`
with `A = as = [a₁, …, a_k]` and `B_u = bs = [b₁, …, b_l]` nonempty. Then there is no finite
sequence of steps (`RotationSystem.ArcLoopStep`) from a dart of `A` to a dart of `B_u`: no
sequence `z₀, …, z_n` of darts outside `{d, d̄}` with `z₀ ∈ A`, `z_n ∈ B_u`, each step being
`z_{j+1} = z̄_j`, or `z_{j+1} = σ^{±1}(z_j)` with `z_j ∉ u`, or `z_j, z_{j+1} ∈ A`, or
`z_j, z_{j+1} ∈ B_u`. -/
@[cluster_algebras "lem_disk_map_loop_separates"]
theorem loop_separates (hM : M.IsDiskMap) {d : H} {as bs : List H}
    (hL : M.rot.toList d = d :: as ++ M.inv d :: bs) (hk : as ≠ []) (hl : bs ≠ []) :
    ¬∃ z₀ ∈ as, ∃ z ∈ bs, Relation.ReflTransGen (M.ArcLoopStep d as bs) z₀ z :=
  hM.toIsConnected.loop_separates hM.euler hL hk hl

end DiskMap.IsDiskMap

/-! ### Loops give roundtrips -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- At an internal vertex of a plabic graph every dart has the colour of the vertex. -/
private theorem IsPlabicGraph.colour_eq_of_mem_vertexOf (hG : G.IsPlabicGraph) {p z : H}
    (hu : ¬G.IsBoundaryVertex (G.vertexOf p)) (hz : z ∈ G.vertexOf p) :
    G.colour z = G.colour p := by
  obtain ⟨n, rfl⟩ := (G.mem_vertexOf.1 hz).exists_nat_pow_eq
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : (G.rot ^ n) p ∈ G.vertexOf p := by
      rw [G.mem_vertexOf]; exact ⟨n, by simp⟩
    have hv : G.vertexOf ((G.rot ^ n) p) = G.vertexOf p := G.vertexOf_eq_of_mem hn
    rw [pow_succ', Equiv.Perm.mul_apply, hG.colour_rot _ (by rwa [hv]), ih hn]

private theorem IsPlabicGraph.exists_tripMap_side (hG : G.IsPlabicGraph) {p : H}
    {S S' : List H} (hu : ¬G.IsBoundaryVertex (G.vertexOf p))
    (hL : G.rot.toList p = p :: S ++ G.inv p :: S') :
    ∃ e ∈ G.vertexOf p, (G.tripMap e ∈ S ∨ G.tripMap e = e) ∧
      ∀ z, G.inv z ∈ S → G.tripMap z ∈ S ∨ G.tripMap z = e := by
  have hιu := G.inv_mem_vertexOf_of_toList hL
  have hzu : ∀ z, G.inv z ∈ S → G.inv z ∈ G.vertexOf p := fun z hz =>
    (G.mem_vertexOf_iff_of_toList hL).2 (Or.inr (Or.inl hz))
  cases hc : G.colour p
  · -- white: `T(z) = σ⁻¹(z̄)` at `v(p)`, and `e = p`
    have hturn : ∀ z ∈ G.vertexOf p, G.turn z = G.rot.symm z := fun z hz =>
      turn_of_white (by rwa [G.vertexOf_eq_of_mem hz])
        (by rw [hG.colour_eq_of_mem_vertexOf hu hz, hc])
    have hback : ∀ z, z ∈ S ∨ z = G.inv p → G.rot.symm z ∈ S ∨ G.rot.symm z = p := by
      intro z hz
      have := eq_or_mem_of_apply_mem_or_eq hL (z := G.rot.symm z)
        (by rwa [Equiv.apply_symm_apply])
      tauto
    refine ⟨p, G.self_mem_vertexOf p, ?_, fun z hz => ?_⟩
    · rw [tripMap_apply, hturn _ hιu]
      exact hback _ (Or.inr rfl)
    · rw [tripMap_apply, hturn _ (hzu z hz)]
      exact hback _ (Or.inl hz)
  · -- black: `T(z) = σ(z̄)` at `v(p)`, and `e = p̄`
    have hturn : ∀ z ∈ G.vertexOf p, G.turn z = G.rot z := fun z hz =>
      turn_of_black (by rwa [G.vertexOf_eq_of_mem hz])
        (by rw [hG.colour_eq_of_mem_vertexOf hu hz, hc])
    refine ⟨G.inv p, hιu, ?_, fun z hz => ?_⟩
    · rw [tripMap_apply, hG.inv_involutive p, hturn _ (G.self_mem_vertexOf p)]
      exact apply_mem_or_eq_of_toList hL (List.mem_cons_self ..)
    · rw [tripMap_apply, hturn _ (hzu z hz)]
      exact apply_mem_or_eq_of_toList hL (List.mem_cons_of_mem _ hz)

private theorem IsPlabicGraph.side_tripMap (hG : G.IsPlabicGraph) {p e : H} {S S' : List H}
    (hL : G.rot.toList p = p :: S ++ G.inv p :: S')
    (hsep : ∀ s ∈ S, ∀ z, Relation.ReflTransGen (G.ArcLoopStep p S S') s z → z ∉ S')
    (hC : ∀ s ∈ S, ∀ z, Relation.ReflTransGen (G.ArcLoopStep p S S') s z →
      ¬G.IsBoundaryVertex (G.vertexOf z))
    (K2 : ∀ z, G.inv z ∈ S → G.tripMap z ∈ S ∨ G.tripMap z = e) {s w : H} (hs : s ∈ S)
    (hsw : Relation.ReflTransGen (G.ArcLoopStep p S S') s w) :
    (∃ s ∈ S, Relation.ReflTransGen (G.ArcLoopStep p S S') s (G.tripMap w)) ∨
      G.tripMap w = e := by
  have hι := hG.inv_involutive
  have hιu := G.inv_mem_vertexOf_of_toList hL
  obtain ⟨hwp, hwι⟩ : w ≠ p ∧ w ≠ G.inv p := by
    rcases hsw.cases_tail with rfl | ⟨w', -, hw'⟩
    · exact ne_and_ne_of_mem_of_toList hL hs
    · exact ⟨hw'.2.2.1, hw'.2.2.2.1⟩
  have hιwp : G.inv w ≠ p := fun h => hwι (by rw [← h, hι w])
  have hιwι : G.inv w ≠ G.inv p := fun h => hwp (hι.injective h)
  have hsι : Relation.ReflTransGen (G.ArcLoopStep p S S') s (G.inv w) :=
    hsw.tail ⟨hwp, hwι, hιwp, hιwι, Or.inl rfl⟩
  have hint : ¬G.IsBoundaryVertex (G.vertexOf (G.inv w)) := hC s hs _ hsι
  by_cases hιwu : G.inv w ∈ G.vertexOf p
  · rcases (G.mem_vertexOf_iff_of_toList hL).1 hιwu with h | h | h | h
    · exact absurd h hιwp
    · exact (K2 w h).imp (fun h' => ⟨_, h', Relation.ReflTransGen.refl⟩) id
    · exact absurd h hιwι
    · exact absurd h (hsep s hs _ hsι)
  · left
    have hTv : G.tripMap w ∈ G.vertexOf (G.inv w) := turn_mem_vertexOf _
    have hTu : G.tripMap w ∉ G.vertexOf p := fun h =>
      hιwu (G.mem_vertexOf.2 ((G.mem_vertexOf.1 h).trans (G.mem_vertexOf.1 hTv).symm))
    refine ⟨s, hs, hsι.tail ⟨hιwp, hιwι, fun h => hTu (h ▸ G.self_mem_vertexOf p),
      fun h => hTu (h ▸ hιu), Or.inr (Or.inl ⟨?_, hιwu⟩)⟩⟩
    rw [tripMap_apply]
    cases hc : G.colour (G.inv w)
    · exact Or.inr (turn_of_white hint hc)
    · exact Or.inl (turn_of_black hint hc)

/-- One side of a loop: if no dart reachable by steps from the side `S` of the loop at the
internal vertex `v(p)` lies at a boundary vertex, and none lies in the other side `S'`, then the
trip leaving `v(p)` into `S` is a roundtrip. -/
private theorem hasRoundtrip_of_side (hG : G.IsPlabicGraph) {p : H} {S S' : List H}
    (hu : ¬G.IsBoundaryVertex (G.vertexOf p))
    (hL : G.rot.toList p = p :: S ++ G.inv p :: S')
    (hsep : ∀ s ∈ S, ∀ z, Relation.ReflTransGen (G.ArcLoopStep p S S') s z → z ∉ S')
    (hC : ∀ s ∈ S, ∀ z, Relation.ReflTransGen (G.ArcLoopStep p S S') s z →
      ¬G.IsBoundaryVertex (G.vertexOf z)) :
    G.HasRoundtrip := by
  obtain ⟨e, heu, K1, K2⟩ := hG.exists_tripMap_side hu hL
  -- the orbit of `e` stays in the darts reachable from `S`, together with `e`
  have horbit : ∀ n, (∃ s ∈ S, Relation.ReflTransGen (G.ArcLoopStep p S S') s
      (G.tripMap^[n] e)) ∨ G.tripMap^[n] e = e := by
    intro n
    induction n with
    | zero => exact Or.inr rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with ⟨s, hs, hsw⟩ | h
      · exact hG.side_tripMap hL hsep hC K2 hs hsw
      · rw [h]
        exact K1.imp (fun h' => ⟨_, h', Relation.ReflTransGen.refl⟩) id
  have heint : ¬G.IsBoundaryVertex (G.vertexOf e) := by rwa [G.vertexOf_eq_of_mem heu]
  refine hasRoundtrip_iff.2 ⟨e, notMem_bdry_of_mem_vertexOf heint (G.self_mem_vertexOf e),
    fun n ⟨j, hj⟩ => ?_⟩
  have hlegv : G.IsBoundaryVertex (G.vertexOf (G.leg j)) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j)
  rcases horbit n with ⟨s, hs, hsz⟩ | h
  · exact hC s hs _ hsz (hj ▸ hlegv)
  · rw [h] at hj
    exact heint (hj ▸ hlegv)

private theorem IsPlabicGraph.exists_reflTransGen_arcLoopStep (hG : G.IsPlabicGraph) {d : H}
    (as bs : List H) (hu : ¬G.IsBoundaryVertex (G.vertexOf d)) (hιu : G.inv d ∈ G.vertexOf d) :
    ∃ x₀, ∀ c, G.IsBoundaryVertex (G.vertexOf c) →
      Relation.ReflTransGen (G.ArcLoopStep d as bs) c x₀ := by
  have hbv : ∀ x, G.IsBoundaryVertex (G.vertexOf x) →
      x ∉ G.vertexOf d ∧ x ≠ d ∧ x ≠ G.inv d := fun x hx =>
    have hxu : x ∉ G.vertexOf d := fun h => hu (G.vertexOf_eq_of_mem h ▸ hx)
    ⟨hxu, fun h => hxu (h ▸ G.self_mem_vertexOf d), fun h => hxu (h ▸ hιu)⟩
  have hrotstep : ∀ x, G.IsBoundaryVertex (G.vertexOf x) →
      G.ArcLoopStep d as bs x (G.rot x) := by
    intro x hx
    have hx' : G.IsBoundaryVertex (G.vertexOf (G.rot x)) := by rwa [G.vertexOf_rot]
    exact ⟨(hbv x hx).2.1, (hbv x hx).2.2, (hbv _ hx').2.1, (hbv _ hx').2.2,
      Or.inr (Or.inl ⟨Or.inl rfl, (hbv x hx).1⟩)⟩
  have hrotpow : ∀ x, G.IsBoundaryVertex (G.vertexOf x) → ∀ n : ℕ,
      Relation.ReflTransGen (G.ArcLoopStep d as bs) x ((G.rot ^ n) x) := by
    intro x hx n
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
      have hv : G.vertexOf ((G.rot ^ n) x) = G.vertexOf x :=
        G.vertexOf_eq_of_mem (G.mem_vertexOf.2 ⟨n, by simp⟩)
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.tail (hrotstep _ (hv ▸ hx))
  obtain ⟨x₀, hx₀⟩ := G.mem_faceOrbits.1 hG.exterior_mem_faceOrbits
  have hφstep : ∀ e ∈ G.exterior,
      Relation.ReflTransGen (G.ArcLoopStep d as bs) e (G.facePerm e) := by
    intro e he
    have heB := G.exterior_subset_bdry he
    have hv : G.IsBoundaryVertex (G.vertexOf e) := G.isBoundaryVertex_vertexOf_of_mem heB
    have hv' : G.IsBoundaryVertex (G.vertexOf (G.inv e)) :=
      G.isBoundaryVertex_vertexOf_of_mem (hG.inv_mem_bdry e heB)
    rw [RotationSystem.facePerm_apply]
    exact (Relation.ReflTransGen.single ⟨(hbv e hv).2.1, (hbv e hv).2.2, (hbv _ hv').2.1,
      (hbv _ hv').2.2, Or.inl rfl⟩).tail (hrotstep _ hv')
  have hext : ∀ n : ℕ, (G.facePerm ^ n) x₀ ∈ G.exterior ∧
      Relation.ReflTransGen (G.ArcLoopStep d as bs) x₀ ((G.facePerm ^ n) x₀) := by
    intro n
    induction n with
    | zero => exact ⟨hx₀ ▸ G.self_mem_faceOf x₀, Relation.ReflTransGen.refl⟩
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      refine ⟨?_, ih.2.trans (hφstep _ ih.1)⟩
      rw [← hx₀, G.mem_faceOf]
      exact ⟨((n + 1 : ℕ) : ℤ), by rw [zpow_natCast, pow_succ', Equiv.Perm.mul_apply]⟩
  refine ⟨x₀, fun c hc => ?_⟩
  obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hc)
  obtain ⟨i', rfl⟩ := (finRotate b).surjective i
  obtain ⟨e, he, hei, -⟩ := hG.exists_exterior i'
  rw [hi] at hei
  obtain ⟨n, hn⟩ := (G.mem_vertexOf.1 hei).exists_nat_pow_eq
  obtain ⟨m, hm⟩ := (G.mem_faceOf.1 (hx₀ ▸ he : e ∈ G.faceOf x₀)).exists_nat_pow_eq
  have he₀ := (hext m).2
  rw [hm] at he₀
  have hce : Relation.ReflTransGen (G.ArcLoopStep d as bs) c e := hn ▸ hrotpow c hc n
  exact hce.trans (RotationSystem.ArcLoopStep.reflTransGen_symm hG.inv_involutive he₀)

/-- **A loop gives a roundtrip**: if a plabic graph has an edge of the graph
`{d, d̄}` (so `d ∉ B`) with `v(d) = v(d̄)`, then it has a roundtrip. -/
@[cluster_algebras "lem_loop_roundtrip"]
theorem IsPlabicGraph.hasRoundtrip_of_loop (hG : G.IsPlabicGraph) {d : H} (hd : d ∉ G.bdry)
    (hloop : G.vertexOf (G.inv d) = G.vertexOf d) : G.HasRoundtrip := by
  have hι := hG.inv_involutive
  have hdι : G.inv d ≠ d := hG.inv_ne d
  have hιu : G.inv d ∈ G.vertexOf d := hloop ▸ G.self_mem_vertexOf _
  have hu : ¬G.IsBoundaryVertex (G.vertexOf d) := fun hv =>
    hdι (DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card hv hιu (G.self_mem_vertexOf d)
      (mt hG.inv_mem_bdry_iff.1 hd) hd)
  have hu' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv d)) := by rwa [hloop]
  -- the rotation at `u = v(d)` is `(d, a₁, …, a_k, d̄, b₁, …, b_l)`
  obtain ⟨as, bs, hL⟩ := G.exists_toList_eq_of_inv_mem_vertexOf hdι hιu
  have hL' : G.rot.toList (G.inv d) = G.inv d :: bs ++ G.inv (G.inv d) :: as := by
    rw [hι d]
    exact toList_eq_of_toList hL
  have hstep_eq := G.arcLoopStep_inv hι hloop as bs
  -- if one side is empty, it gives the roundtrip
  by_cases hk : as = []
  · subst hk
    exact hasRoundtrip_of_side hG hu hL (by simp) (by simp)
  by_cases hl : bs = []
  · subst hl
    exact hasRoundtrip_of_side hG hu' hL' (by simp) (by simp)
  have hsepAB := hG.toIsDiskMap.loop_separates hL hk hl
  -- darts at boundary vertices are joined to a dart `e₀` of the exterior by steps
  obtain ⟨x₀, hbd⟩ := hG.exists_reflTransGen_arcLoopStep as bs hu hιu
  have hsymm : ∀ {x y : H}, Relation.ReflTransGen (G.ArcLoopStep d as bs) x y →
      Relation.ReflTransGen (G.ArcLoopStep d as bs) y x := fun h =>
    RotationSystem.ArcLoopStep.reflTransGen_symm hι h
  by_cases hA : ∀ s ∈ as, ∀ z, Relation.ReflTransGen (G.ArcLoopStep d as bs) s z →
      ¬G.IsBoundaryVertex (G.vertexOf z)
  · exact hasRoundtrip_of_side hG hu hL
      (fun s hs z hsz hz => hsepAB ⟨s, hs, z, hz, hsz⟩) hA
  · push Not at hA
    obtain ⟨s, hs, z, hsz, hz⟩ := hA
    refine hasRoundtrip_of_side hG hu' hL' ?_ ?_ <;> rw [hstep_eq] <;> intro t ht z' htz hz'
    · exact hsepAB ⟨z', hz', t, ht, hsymm htz⟩
    · exact hsepAB
        ⟨s, hs, t, ht, (hsz.trans (hbd z hz)).trans (hsymm (htz.trans (hbd z' hz')))⟩

end PlabicData

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap
public import ClusterAlgebras.QuiverOps

/-!
# The quiver of a plabic graph

Let `G` be a plabic graph with set of faces `F` and set of boundary faces `F_∂`. For faces
`f, f'` let `c(f, f')` count the darts `d ∉ B` running from an internal white vertex `v(d)` to an
internal black vertex `v(d̄)`, with `f` to the right of `d` and `f'` to its left, provided `f ≠ f'`
and `f, f'` are not both boundary faces. The quiver `Q(G)` has vertices `F`, frozen vertices `F_∂`
and arrows the two-cycle cancellation `ρ(c)`.

The *dart balance* `ψ_G(f, f')` counts the darts from `f` to `f'` (to the right of the dart and
to its left) at internal white vertices, minus those at internal black vertices. Every dart from
`f` to `f'` joins two internal vertices once `f, f'` are not both boundary faces, and sorting
these darts by the colours of their two ends gives
`2 (c(f, f') - c(f', f)) = ψ_G(f, f') - ψ_G(f', f)`. Hence a bijection of faces matching the
boundary faces and the antisymmetrised dart balances is an isomorphism of quivers. An isomorphism
of plabic graphs maps faces to faces and boundary faces to boundary faces, and the induced
bijection of faces is an isomorphism of quivers.

## Main definitions

* `ClusterAlgebras.PlabicData.quiverCount`, `ClusterAlgebras.PlabicData.quiver`: the counting
  function `c` and the quiver `Q(G)`.
* `ClusterAlgebras.PlabicData.dartBalance`: the dart balance `ψ_G`.
* `ClusterAlgebras.PlabicData.quiverIsoOfDartBalance`: the isomorphism of quivers given by a
  bijection of faces matching the dart balances.
* `ClusterAlgebras.PlabicData.Iso.faceEquiv`, `ClusterAlgebras.PlabicData.Iso.quiverIso`: the
  bijection of faces and the isomorphism of quivers induced by an isomorphism of plabic graphs.

## Main results

* `ClusterAlgebras.PlabicData.isArrowSystem_cancellation_quiverCount`,
  `ClusterAlgebras.PlabicData.twoCycleFree_cancellation_quiverCount`,
  `ClusterAlgebras.PlabicData.cancellation_quiverCount_eq_zero`: `Q(G)` is a quiver.
* `ClusterAlgebras.PlabicData.two_mul_quiverCount_sub`: the signed counts of `Q(G)` from the dart
  balance.
* `ClusterAlgebras.PlabicData.exists_quiverIso_of_dartBalance`: a criterion for an isomorphism of
  quivers of plabic graphs.
* `ClusterAlgebras.PlabicData.Iso.bijOn_faces`: an isomorphism of plabic graphs matches the faces.
* `ClusterAlgebras.PlabicData.Iso.exists_quiverIso`: isomorphic plabic graphs have isomorphic
  quivers.

## Implementation notes

* The vertex set of `Q(G)` is the type `↥G.faces` of faces, each face being the `Finset` of its
  darts; its frozen vertices are the faces lying in `G.boundaryFaces`.
* The conditions `f ≠ f'` and "not both boundary faces" are part of the predicate counted by
  `quiverCount`, as in FWZ. With them, `quiverCount` is an arrow system with no arrow
  between boundary faces for any tuple of the shape of a plabic graph, so `quiver` is defined on
  `PlabicData` without hypotheses.
* FWZ prove that an isomorphism of plabic graphs induces an isomorphism of quivers through
  the dart balance. The proof here compares the counting functions `c` directly, which needs no
  hypothesis on the two tuples.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-- The dart `d` lies at an **internal vertex of colour `s`**: `v(d)` contains no dart of `B` and
`κ(v(d)) = s`. -/
abbrev IsInternalOfColour (d : H) (s : Shade) : Prop :=
  ¬G.IsBoundaryVertex (G.vertexOf d) ∧ G.colour d = s

/-! ### The quiver -/

/-- The **counting function** `c(f, f')` of the quiver of a plabic graph: the number of darts
`d ∉ B` such that `v(d)` is an internal white vertex, `v(d̄)` is an internal black vertex, `f` is
the face to the right of `d` and `f'` the face to its left, `f ≠ f'`, and not both of `f, f'` are
boundary faces. -/
@[cluster_algebras "def_plabic_graph_quiver"]
def quiverCount (f f' : G.faces) : ℕ :=
  #{d | d ∉ G.bdry ∧ G.IsInternalOfColour d .white ∧ G.IsInternalOfColour (G.inv d) .black ∧
    G.rightFace d = f ∧ G.leftFace d = f' ∧ f ≠ f' ∧
    ¬((f : Finset H) ∈ G.boundaryFaces ∧ (f' : Finset H) ∈ G.boundaryFaces)}

/-- No dart is counted from a face to itself. -/
@[simp]
theorem quiverCount_self (f : G.faces) : G.quiverCount f f = 0 := by
  simp [quiverCount]

/-- No dart is counted between two boundary faces. -/
theorem quiverCount_eq_zero {f f' : G.faces} (hf : (f : Finset H) ∈ G.boundaryFaces)
    (hf' : (f' : Finset H) ∈ G.boundaryFaces) : G.quiverCount f f' = 0 := by
  simp [quiverCount, hf, hf']

/-- The counting function is an arrow system. -/
theorem isArrowSystem_quiverCount : IsArrowSystem G.quiverCount := G.quiverCount_self

/-- **The quiver of a plabic graph is a quiver**: `ρ(c)` is an arrow system. -/
@[cluster_algebras "lem_plabic_graph_quiver_is_quiver"]
theorem isArrowSystem_cancellation_quiverCount : IsArrowSystem (cancellation G.quiverCount) :=
  G.isArrowSystem_quiverCount.cancellation

/-- **The quiver of a plabic graph is a quiver**: `ρ(c)` is two-cycle-free. -/
@[cluster_algebras "lem_plabic_graph_quiver_is_quiver"]
theorem twoCycleFree_cancellation_quiverCount : TwoCycleFree (cancellation G.quiverCount) :=
  cancellation_twoCycleFree _

/-- **The quiver of a plabic graph is a quiver**: `ρ(c)` has no arrow between two boundary
faces. -/
@[cluster_algebras "lem_plabic_graph_quiver_is_quiver"]
theorem cancellation_quiverCount_eq_zero {f f' : G.faces}
    (hf : (f : Finset H) ∈ G.boundaryFaces) (hf' : (f' : Finset H) ∈ G.boundaryFaces) :
    cancellation G.quiverCount f f' = 0 := by
  simp [cancellation, G.quiverCount_eq_zero hf hf']

/-- The **quiver of a plabic graph** `Q(G) = (F, F_∂, ρ(c))`: its vertices are the faces, its
frozen vertices the boundary faces, and its arrows the two-cycle cancellation of the counting
function `quiverCount`. -/
@[cluster_algebras "def_plabic_graph_quiver"]
def quiver : Quiver G.faces where
  frozen := {f | (f : Finset H) ∈ G.boundaryFaces}
  arrows := cancellation G.quiverCount
  isArrowSystem := G.isArrowSystem_cancellation_quiverCount
  twoCycleFree := G.twoCycleFree_cancellation_quiverCount
  frozen_eq_zero _ hf _ hf' :=
    G.cancellation_quiverCount_eq_zero (by simpa using hf) (by simpa using hf')

/-- The frozen vertices of `Q(G)` are the boundary faces. -/
@[simp]
theorem mem_frozen_quiver {f : G.faces} :
    f ∈ G.quiver.frozen ↔ (f : Finset H) ∈ G.boundaryFaces := by
  simp [quiver]

/-- The arrows of `Q(G)` are the two-cycle cancellation of the counting function. -/
theorem arrows_quiver : G.quiver.arrows = cancellation G.quiverCount := rfl

/-- The arrows of `Q(G)` are the truncated differences of the counting function. -/
theorem arrows_quiver_apply (f f' : G.faces) :
    G.quiver.arrows f f' = G.quiverCount f f' - G.quiverCount f' f := by
  rw [arrows_quiver, cancellation_eq_sub]

/-! ### The dart balance -/

/-- The **dart balance** `ψ_G(f, f')`: the number of darts `x ∉ B` at an internal white vertex
with `f` to the right of `x` and `f'` to its left, minus the number of such darts at an internal
black vertex. -/
@[cluster_algebras "def_plabic_dart_balance"]
def dartBalance (f f' : G.faces) : ℤ :=
  (#{x | x ∉ G.bdry ∧ G.IsInternalOfColour x .white ∧ G.rightFace x = f ∧
      G.leftFace x = f'} : ℤ) -
    #{x | x ∉ G.bdry ∧ G.IsInternalOfColour x .black ∧ G.rightFace x = f ∧ G.leftFace x = f'}

/-! ### Signed counts from the dart balance -/

section IsDiskMap

variable {G}

/-- In a disk map, a dart `x ∉ B` whose two sides are not both boundary faces joins two internal
vertices: `v(x)` and `v(x̄)` are internal. -/
theorem not_isBoundaryVertex_of_notMem_boundaryFaces (hG : G.toDiskMap.IsDiskMap) {x : H}
    (hx : x ∉ G.bdry)
    (hbd : ¬(G.rightFace x ∈ G.boundaryFaces ∧ G.leftFace x ∈ G.boundaryFaces)) :
    ¬G.IsBoundaryVertex (G.vertexOf x) ∧ ¬G.IsBoundaryVertex (G.vertexOf (G.inv x)) := by
  refine ⟨fun hv => hbd ⟨hG.rightFace_mem_boundaryFaces hx hv,
    hG.leftFace_mem_boundaryFaces hx hv⟩, fun hv => ?_⟩
  have hx' : G.inv x ∉ G.bdry := fun h => hx (hG.inv_mem_bdry_iff.1 h)
  have h1 := hG.rightFace_mem_boundaryFaces hx' hv
  have h2 := hG.leftFace_mem_boundaryFaces hx' hv
  simp only [DiskMap.rightFace, DiskMap.leftFace, hG.inv_involutive x] at h1 h2
  exact hbd ⟨h2, h1⟩

/-- The counting function at `(f', f)`, read through the reversed darts: `c(f', f)` counts the
darts `x ∉ B` from `f` to `f'` with `v(x̄)` internal white and `v(x)` internal black. -/
theorem quiverCount_swap (hG : G.toDiskMap.IsDiskMap) (f f' : G.faces) :
    G.quiverCount f' f = #{x | x ∉ G.bdry ∧ G.IsInternalOfColour (G.inv x) .white ∧
      G.IsInternalOfColour x .black ∧ G.rightFace x = f ∧ G.leftFace x = f' ∧ f' ≠ f ∧
      ¬((f' : Finset H) ∈ G.boundaryFaces ∧ (f : Finset H) ∈ G.boundaryFaces)} := by
  rw [quiverCount]
  refine card_equiv G.inv fun d => ?_
  simp only [mem_filter, mem_univ, true_and, DiskMap.rightFace, DiskMap.leftFace,
    hG.inv_mem_bdry_iff, hG.inv_involutive d]
  tauto

/-- The dart balance at `(f', f)`, read through the reversed darts. -/
theorem dartBalance_swap (hG : G.toDiskMap.IsDiskMap) (f f' : G.faces) :
    G.dartBalance f' f =
      (#{x | x ∉ G.bdry ∧ G.IsInternalOfColour (G.inv x) .white ∧ G.rightFace x = f ∧
        G.leftFace x = f'} : ℤ) -
      #{x | x ∉ G.bdry ∧ G.IsInternalOfColour (G.inv x) .black ∧ G.rightFace x = f ∧
        G.leftFace x = f'} := by
  have key : ∀ s : Shade,
      #{x | x ∉ G.bdry ∧ G.IsInternalOfColour x s ∧ G.rightFace x = f' ∧ G.leftFace x = f} =
      #{x | x ∉ G.bdry ∧ G.IsInternalOfColour (G.inv x) s ∧ G.rightFace x = f ∧
        G.leftFace x = f'} := by
    intro s
    refine card_equiv G.inv fun d => ?_
    simp only [mem_filter, mem_univ, true_and, DiskMap.rightFace, DiskMap.leftFace,
      hG.inv_mem_bdry_iff, hG.inv_involutive d]
    tauto
  rw [dartBalance, key, key]

/-- **Signed counts of `Q(G)` from the dart balance**: for faces `f ≠ f'` not both boundary faces,
`2 (c(f, f') - c(f', f)) = ψ_G(f, f') - ψ_G(f', f)`. -/
@[cluster_algebras "lem_plabic_signed_count_balance"]
theorem two_mul_quiverCount_sub (hG : G.toDiskMap.IsDiskMap) {f f' : G.faces} (hne : f ≠ f')
    (hbd : ¬((f : Finset H) ∈ G.boundaryFaces ∧ (f' : Finset H) ∈ G.boundaryFaces)) :
    2 * ((G.quiverCount f f' : ℤ) - G.quiverCount f' f) =
      G.dartBalance f f' - G.dartBalance f' f := by
  rw [G.quiverCount_swap hG f f', G.dartBalance_swap hG f f', dartBalance, quiverCount]
  simp only [natCast_card_filter, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases h1 : x ∈ G.bdry
  · simp [h1]
  by_cases h2 : G.rightFace x = f
  swap
  · simp [h2]
  by_cases h3 : G.leftFace x = f'
  swap
  · simp [h3]
  obtain ⟨hv1, hv2⟩ :=
    G.not_isBoundaryVertex_of_notMem_boundaryFaces hG h1 (by rwa [h2, h3])
  have hne' : f' ≠ f := Ne.symm hne
  have hbd' : ¬((f' : Finset H) ∈ G.boundaryFaces ∧ (f : Finset H) ∈ G.boundaryFaces) :=
    fun h => hbd ⟨h.2, h.1⟩
  have hcol : ∀ s : Shade, s = .white ∨ s = .black := fun s => by cases s <;> simp
  rcases hcol (G.colour x) with hc1 | hc1 <;> rcases hcol (G.colour (G.inv x)) with hc2 | hc2 <;>
    simp [IsInternalOfColour, h1, h2, h3, hv1, hv2, hc1, hc2, hne, hne', hbd, hbd']

end IsDiskMap

/-! ### A criterion for an isomorphism of quivers -/

section Criterion

variable {G} {H' : Type*} [Fintype H'] [DecidableEq H'] {b' : ℕ} {G' : PlabicData H' b'}

/-- The **isomorphism of quivers** `Q(G) → Q(G')` given by a bijection `Ψ` of faces matching the
boundary faces and the antisymmetrised dart balances. -/
def quiverIsoOfDartBalance (hG : G.toDiskMap.IsDiskMap) (hG' : G'.toDiskMap.IsDiskMap)
    (Ψ : G.faces ≃ G'.faces)
    (hΨ : ∀ f, ((Ψ f : G'.faces) : Finset H') ∈ G'.boundaryFaces ↔
      (f : Finset H) ∈ G.boundaryFaces)
    (hψ : ∀ f f' : G.faces, f ≠ f' →
      ¬((f : Finset H) ∈ G.boundaryFaces ∧ (f' : Finset H) ∈ G.boundaryFaces) →
      G.dartBalance f f' - G.dartBalance f' f =
        G'.dartBalance (Ψ f) (Ψ f') - G'.dartBalance (Ψ f') (Ψ f)) :
    G.quiver.Iso G'.quiver where
  equiv := Ψ
  mem_frozen_iff f := by rw [mem_frozen_quiver, mem_frozen_quiver, hΨ]
  arrows_eq u v := by
    have key : (G'.quiverCount (Ψ u) (Ψ v) : ℤ) - G'.quiverCount (Ψ v) (Ψ u) =
        (G.quiverCount u v : ℤ) - G.quiverCount v u := by
      by_cases huv : u = v
      · subst huv
        simp
      by_cases hbd : (u : Finset H) ∈ G.boundaryFaces ∧ (v : Finset H) ∈ G.boundaryFaces
      · have h1 := (hΨ u).2 hbd.1
        have h2 := (hΨ v).2 hbd.2
        rw [G.quiverCount_eq_zero hbd.1 hbd.2, G.quiverCount_eq_zero hbd.2 hbd.1,
          G'.quiverCount_eq_zero h1 h2, G'.quiverCount_eq_zero h2 h1]
      · have hne' : Ψ u ≠ Ψ v := Ψ.injective.ne huv
        have hbd' : ¬(((Ψ u : G'.faces) : Finset H') ∈ G'.boundaryFaces ∧
            ((Ψ v : G'.faces) : Finset H') ∈ G'.boundaryFaces) := by
          rwa [hΨ, hΨ]
        have e1 := G.two_mul_quiverCount_sub hG huv hbd
        have e2 := G'.two_mul_quiverCount_sub hG' hne' hbd'
        have e3 := hψ u v huv hbd
        omega
    rw [arrows_quiver_apply, arrows_quiver_apply]
    omega

/-- The bijection underlying `quiverIsoOfDartBalance` is `Ψ`. -/
@[simp]
theorem quiverIsoOfDartBalance_equiv (hG : G.toDiskMap.IsDiskMap)
    (hG' : G'.toDiskMap.IsDiskMap) (Ψ : G.faces ≃ G'.faces)
    (hΨ : ∀ f, ((Ψ f : G'.faces) : Finset H') ∈ G'.boundaryFaces ↔
      (f : Finset H) ∈ G.boundaryFaces)
    (hψ : ∀ f f' : G.faces, f ≠ f' →
      ¬((f : Finset H) ∈ G.boundaryFaces ∧ (f' : Finset H) ∈ G.boundaryFaces) →
      G.dartBalance f f' - G.dartBalance f' f =
        G'.dartBalance (Ψ f) (Ψ f') - G'.dartBalance (Ψ f') (Ψ f)) :
    (quiverIsoOfDartBalance hG hG' Ψ hΨ hψ).equiv = Ψ :=
  rfl

/-- **A criterion for an isomorphism of quivers of plabic graphs**: a bijection `Ψ : F → F'` of
faces with `Ψ(F_∂) = F'_∂` and `ψ_G(f, f') - ψ_G(f', f) = ψ_{G'}(Ψ f, Ψ f') - ψ_{G'}(Ψ f', Ψ f)`
for all faces `f ≠ f'` not both boundary faces is an isomorphism `Q(G) → Q(G')`. -/
@[cluster_algebras "lem_plabic_quiver_iso_criterion"]
theorem exists_quiverIso_of_dartBalance (hG : G.toDiskMap.IsDiskMap)
    (hG' : G'.toDiskMap.IsDiskMap) (Ψ : G.faces ≃ G'.faces)
    (hΨ : ∀ f, ((Ψ f : G'.faces) : Finset H') ∈ G'.boundaryFaces ↔
      (f : Finset H) ∈ G.boundaryFaces)
    (hψ : ∀ f f' : G.faces, f ≠ f' →
      ¬((f : Finset H) ∈ G.boundaryFaces ∧ (f' : Finset H) ∈ G.boundaryFaces) →
      G.dartBalance f f' - G.dartBalance f' f =
        G'.dartBalance (Ψ f) (Ψ f') - G'.dartBalance (Ψ f') (Ψ f)) :
    ∃ e : G.quiver.Iso G'.quiver, e.equiv = Ψ :=
  ⟨quiverIsoOfDartBalance hG hG' Ψ hΨ hψ, rfl⟩

end Criterion

/-! ### Isomorphisms of plabic graphs -/

/-- Iterates of intertwined permutations are intertwined. -/
private theorem pow_apply_of_semiconj {α β : Type*} {f : Equiv.Perm α} {g : Equiv.Perm β}
    (θ : α ≃ β) (h : ∀ x, θ (f x) = g (θ x)) (n : ℕ) (x : α) :
    θ ((f ^ n) x) = (g ^ n) (θ x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, ih]

/-- A bijection intertwining two permutations of finite sets maps their cycles to cycles. -/
private theorem sameCycle_map_of_semiconj {α β : Type*} [Finite α] {f : Equiv.Perm α}
    {g : Equiv.Perm β} (θ : α ≃ β) (h : ∀ x, θ (f x) = g (θ x)) {x y : α}
    (hxy : f.SameCycle x y) : g.SameCycle (θ x) (θ y) := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  exact ⟨n, by rw [zpow_natCast, pow_apply_of_semiconj θ h]⟩

namespace Iso

variable {G} {H' : Type*} [Fintype H'] [DecidableEq H'] {G' : PlabicData H' b}

/-- An isomorphism intertwines the face permutations: `θ φ = φ' θ`. -/
theorem map_facePerm (θ : G.Iso G') (d : H) :
    θ.toEquiv (G.facePerm d) = G'.facePerm (θ.toEquiv d) := by
  simp [θ.map_rot, θ.map_inv]

/-- The inverse of an isomorphism intertwines the face permutations. -/
theorem symm_map_facePerm (θ : G.Iso G') (d : H') :
    θ.toEquiv.symm (G'.facePerm d) = G.facePerm (θ.toEquiv.symm d) := by
  apply θ.toEquiv.injective
  rw [Equiv.apply_symm_apply, θ.map_facePerm, Equiv.apply_symm_apply]

/-- An isomorphism maps each orbit `f(d)` of `φ` onto the orbit `f(θ d)` of `φ'`. -/
theorem map_faceOf (θ : G.Iso G') (d : H) :
    (G.faceOf d).map θ.toEquiv.toEmbedding = G'.faceOf (θ.toEquiv d) := by
  ext y
  rw [mem_map_equiv, RotationSystem.mem_faceOf, RotationSystem.mem_faceOf]
  constructor
  · intro h
    simpa using sameCycle_map_of_semiconj θ.toEquiv θ.map_facePerm h
  · intro h
    simpa using sameCycle_map_of_semiconj θ.toEquiv.symm θ.symm_map_facePerm h

/-- The face to the right of `θ d` is the image of the face to the right of `d`. -/
theorem rightFace_apply (θ : G.Iso G') (d : H) :
    G'.rightFace (θ.toEquiv d) = (G.rightFace d).map θ.toEquiv.toEmbedding :=
  (θ.map_faceOf d).symm

/-- The face to the left of `θ d` is the image of the face to the left of `d`. -/
theorem leftFace_apply (θ : G.Iso G') (d : H) :
    G'.leftFace (θ.toEquiv d) = (G.leftFace d).map θ.toEquiv.toEmbedding := by
  rw [DiskMap.leftFace, DiskMap.leftFace, ← θ.map_inv, θ.map_faceOf]

/-- An isomorphism maps `B` onto `B'`. -/
theorem map_bdry (θ : G.Iso G') : G.bdry.map θ.toEquiv.toEmbedding = G'.bdry := by
  ext y
  rw [mem_map_equiv, ← θ.mem_bdry_iff, Equiv.apply_symm_apply]

/-- An isomorphism maps orbits of `φ` to orbits of `φ'`, and only those. -/
theorem map_mem_faceOrbits_iff (θ : G.Iso G') {f : Finset H} :
    f.map θ.toEquiv.toEmbedding ∈ G'.faceOrbits ↔ f ∈ G.faceOrbits := by
  simp only [RotationSystem.mem_faceOrbits]
  constructor
  · rintro ⟨d', hd'⟩
    refine ⟨θ.toEquiv.symm d', map_injective θ.toEquiv.toEmbedding ?_⟩
    rw [θ.map_faceOf, Equiv.apply_symm_apply, hd']
  · rintro ⟨d, rfl⟩
    exact ⟨θ.toEquiv d, (θ.map_faceOf d).symm⟩

/-- An isomorphism maps faces to faces, and only those. -/
theorem map_mem_faces_iff (θ : G.Iso G') {f : Finset H} :
    f.map θ.toEquiv.toEmbedding ∈ G'.faces ↔ f ∈ G.faces := by
  rw [DiskMap.mem_faces, DiskMap.mem_faces, θ.map_mem_faceOrbits_iff, ← θ.map_exterior, Ne, Ne,
    map_inj]

/-- An isomorphism maps boundary faces to boundary faces, and only those. -/
theorem map_mem_boundaryFaces_iff (θ : G.Iso G') {f : Finset H} :
    f.map θ.toEquiv.toEmbedding ∈ G'.boundaryFaces ↔ f ∈ G.boundaryFaces := by
  rw [DiskMap.mem_boundaryFaces, DiskMap.mem_boundaryFaces, θ.map_mem_faces_iff, ← θ.map_bdry,
    disjoint_map]

/-- **An isomorphism of plabic graphs matches the faces**: `f ↦ θ(f)` is a bijection from the
faces of `G` onto the faces of `G'`, and from the boundary faces of `G` onto the boundary faces of
`G'`. -/
@[cluster_algebras "lem_plabic_isomorphism_faces"]
theorem bijOn_faces (θ : G.Iso G') :
    Set.BijOn (fun f : Finset H => f.map θ.toEquiv.toEmbedding) G.faces G'.faces ∧
      Set.BijOn (fun f : Finset H => f.map θ.toEquiv.toEmbedding) G.boundaryFaces
        G'.boundaryFaces := by
  have hinj : ∀ s : Set (Finset H), Set.InjOn (fun f : Finset H => f.map θ.toEquiv.toEmbedding) s :=
    fun _ => (map_injective _).injOn
  have hback : ∀ f' : Finset H',
      (f'.map θ.toEquiv.symm.toEmbedding).map θ.toEquiv.toEmbedding = f' := by
    intro f'
    ext y
    simp
  refine ⟨⟨fun f hf => θ.map_mem_faces_iff.2 hf, hinj _, fun f' hf' => ?_⟩,
    ⟨fun f hf => θ.map_mem_boundaryFaces_iff.2 hf, hinj _, fun f' hf' => ?_⟩⟩
  · refine ⟨f'.map θ.toEquiv.symm.toEmbedding, θ.map_mem_faces_iff.1 ?_, hback f'⟩
    rw [hback]
    exact hf'
  · refine ⟨f'.map θ.toEquiv.symm.toEmbedding, θ.map_mem_boundaryFaces_iff.1 ?_, hback f'⟩
    rw [hback]
    exact hf'

/-- The **bijection of faces** `f ↦ θ(f)` induced by an isomorphism of plabic graphs. -/
def faceEquiv (θ : G.Iso G') : G.faces ≃ G'.faces :=
  θ.toEquiv.finsetCongr.subtypeEquiv fun _ => θ.map_mem_faces_iff.symm

/-- The face `θ(f)` is the image of the darts of `f` under `θ`. -/
@[simp]
theorem coe_faceEquiv (θ : G.Iso G') (f : G.faces) :
    ((θ.faceEquiv f : G'.faces) : Finset H') = (f : Finset H).map θ.toEquiv.toEmbedding :=
  rfl

/-- An isomorphism preserves being at an internal vertex of a given colour. -/
theorem isInternalOfColour_iff (θ : G.Iso G') (d : H) (s : Shade) :
    G'.IsInternalOfColour (θ.toEquiv d) s ↔ G.IsInternalOfColour d s := by
  simp only [IsInternalOfColour, θ.isBoundaryVertex_vertexOf_iff]
  exact and_congr_right fun h => by rw [θ.map_colour d h]

/-- An isomorphism preserves the counting function of the quiver. -/
@[simp]
theorem quiverCount_faceEquiv (θ : G.Iso G') (f f' : G.faces) :
    G'.quiverCount (θ.faceEquiv f) (θ.faceEquiv f') = G.quiverCount f f' := by
  rw [quiverCount, quiverCount]
  refine (card_equiv θ.toEquiv fun x => ?_).symm
  simp only [mem_filter, mem_univ, true_and, θ.mem_bdry_iff, ← θ.map_inv,
    θ.isInternalOfColour_iff, θ.rightFace_apply, θ.leftFace_apply, coe_faceEquiv, map_inj,
    θ.faceEquiv.injective.ne_iff, θ.map_mem_boundaryFaces_iff]

/-- The **isomorphism of quivers** `Q(G) → Q(G')` induced by an isomorphism of plabic graphs:
`f ↦ θ(f)`. -/
def quiverIso (θ : G.Iso G') : G.quiver.Iso G'.quiver where
  equiv := θ.faceEquiv
  mem_frozen_iff f := by
    rw [mem_frozen_quiver, mem_frozen_quiver, coe_faceEquiv, θ.map_mem_boundaryFaces_iff]
  arrows_eq u v := by
    rw [arrows_quiver_apply, arrows_quiver_apply, θ.quiverCount_faceEquiv,
      θ.quiverCount_faceEquiv]

/-- The underlying bijection of faces of `θ.quiverIso` is `θ.faceEquiv`. -/
@[simp]
theorem quiverIso_equiv (θ : G.Iso G') : θ.quiverIso.equiv = θ.faceEquiv := rfl

/-- **Isomorphic plabic graphs have isomorphic quivers**: for an isomorphism `θ : G → G'`, the map
`f ↦ θ(f)` of faces is an isomorphism `Q(G) → Q(G')`. -/
@[cluster_algebras "lem_plabic_isomorphism_quiver"]
theorem exists_quiverIso (θ : G.Iso G') :
    ∃ e : G.quiver.Iso G'.quiver,
      ∀ f, ((e.equiv f : G'.faces) : Finset H') = (f : Finset H).map θ.toEquiv.toEmbedding :=
  ⟨θ.quiverIso, fun _ => rfl⟩

end Iso

end PlabicData

end ClusterAlgebras

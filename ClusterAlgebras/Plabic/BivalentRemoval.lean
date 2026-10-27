/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap
public import ClusterAlgebras.Plabic.FirstReturn

/-!
# Removing and inserting bivalent vertices

Let `G = (H, d ↦ d̄, σ, B, κ, β)` be a plabic graph and let `v` be an internal vertex consisting of
exactly two darts `d₁` and `d₂ = σ d₁`, with `d̄₁ ≠ d₂`. The local move (M2) removes `v`: the two
edges `{d₁, d̄₁}` and `{d₂, d̄₂}` at `v` are merged into the single edge `{d̄₁, d̄₂}`. In terms of
darts, the darts of the removal are `H' = H \ {d₁, d₂}`, the new involution exchanges `d̄₁` and
`d̄₂` and agrees with `d ↦ d̄` elsewhere, and the rotation, the boundary, the colours and the
labelling are restricted to `H'`.

The face permutation `φ' = σ' ∘ ι'` of the removal is the first-return map of `φ = σ ∘ (d ↦ d̄)`
to `H'`, and every orbit of `φ` meets `H'`; so `f ↦ f ∩ H'` is a bijection from the orbits of `φ`
onto those of `φ'`. From this, the removal is again a plabic graph, with the same boundary
vertices, legs and numbers of faces and of internal faces.

Conversely, a bivalent vertex `{f, f*}` of any colour may be inserted on an edge `{d, d̄}` with
`d ∉ B`: the darts become `H ⊔ {f, f*}`, the involution pairs `d` with `f` and `f*` with `d̄`, and
`(f, f*)` is a new cycle of the rotation. The insertion is a plabic graph with the boundary
vertices and legs of `G`, and removing the inserted vertex gives back `G`.

## Main definitions

* `ClusterAlgebras.PlabicData.IsBivalentRemovable G d`: the vertex of `d = d₁` is internal and
  consists of exactly the two darts `d₁` and `d₂ = σ d₁`, with `d̄₁ ≠ d₂`.
* `ClusterAlgebras.PlabicData.bivalentRemoval`: the removal of a bivalent vertex.
* `ClusterAlgebras.PlabicData.bivalentInsertion`: the insertion of a bivalent vertex on an edge.
* `ClusterAlgebras.PlabicData.bivalentInsertionRemovalIso`: the isomorphism from `G` to the removal
  of the vertex inserted into `G`.

## Main results

* `ClusterAlgebras.PlabicData.bijOn_faceOrbits_bivalentRemoval`: `f ↦ f ∩ H'` is a bijection
  between the orbits of the face permutations.
* `ClusterAlgebras.PlabicData.isPlabicGraph_bivalentRemoval` and its companions: the removal is a
  plabic graph with the same boundary vertices, legs, and numbers of faces and of internal faces.
* `ClusterAlgebras.PlabicData.isPlabicGraph_bivalentInsertion` and its companions: an insertion is
  a plabic graph with the boundary vertices and legs of `G`.
* `ClusterAlgebras.PlabicData.bivalentRemoval_bivalentInsertion_isomorphic`: removing the inserted
  vertex gives back `G`.

## Implementation notes

* The darts of the removal at `d₁ = d` form the subtype of the set `({d, σ d}ᶜ : Set H)`. Its
  involution is the restriction of the involution of `H` that exchanges `d̄₁` with `d̄₂` and `d₁`
  with `d₂` and agrees with `d ↦ d̄` elsewhere; the rotation is the restriction of `σ`. The removal
  is defined for a plabic graph `G`, since its legs must avoid `{d₁, d₂}`.
* The darts of the insertion are `H ⊕ Fin 2`, with `f = Sum.inr 0` and `f* = Sum.inr 1`. Its
  involution is written as a product of transpositions with the extension of `d ↦ d̄` by the
  identity, so that it is a permutation without hypotheses; its values are those given by FWZ
  when `d ↦ d̄` is a fixed-point-free involution.
* "The removal is `G`" is stated as an isomorphism of plabic graphs whose bijection of darts is
  the canonical identification `e ↦ Sum.inl e` of `H` with `(H ⊕ Fin 2) \ {f, f*}`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function Equiv Equiv.Perm

/-! ### Preliminaries -/

/-- A bijection intertwining two permutations of finite sets matches their orbits. -/
private theorem sameCycle_iff_of_semiconj {α β : Type*} [Finite α] [Finite β] {f : Perm α}
    {g : Perm β} (θ : α ≃ β) (h : ∀ x, θ (f x) = g (θ x)) {x y : α} :
    g.SameCycle (θ x) (θ y) ↔ f.SameCycle x y := by
  have hpow : ∀ (n : ℕ) (x : α), θ ((f ^ n) x) = (g ^ n) (θ x) := by
    intro n
    induction n with
    | zero => exact fun _ => rfl
    | succ n ih =>
      exact fun x => by rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, h, ih]
  constructor
  · intro hxy
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast]; exact θ.injective ((hpow n x).trans hn)⟩
  · intro hxy
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← hpow, hn]⟩

/-- A bijection intertwining two permutations of finite sets preserves the number of orbits. -/
private theorem numOrbits_eq_of_semiconj {α β : Type*} [Finite α] [Finite β] {f : Perm α}
    {g : Perm β} (θ : α ≃ β) (h : ∀ x, θ (f x) = g (θ x)) : numOrbits f = numOrbits g :=
  Nat.card_congr (Quotient.congr θ fun _ _ => (sameCycle_iff_of_semiconj θ h).symm)

private theorem sameCycle_of_eq_apply {α : Type*} {f : Perm α} {x y : α} (h : f x = y) :
    f.SameCycle y x := by
  subst h
  exact sameCycle_apply_left.2 (SameCycle.refl f x)

/-- If `π y ∉ Y` and `π (π y) ∈ Y`, the first return of `y` to `Y` is `π (π y)`. -/
theorem coe_firstReturn_of_apply_apply_mem {X : Type*} [Finite X] {π : Perm X} {Y : Set X}
    {y : Y} (h₁ : π y ∉ Y) (h₂ : π (π y) ∈ Y) : (firstReturn π Y y : X) = π (π y) := by
  have hmin : ∀ j, 0 < j → j < 2 → (π ^ j) y ∉ Y := fun j hj hj2 => by
    obtain rfl : j = 1 := by omega
    rwa [pow_one]
  rw [coe_firstReturn_of_pow two_pos (by rwa [pow_two, Perm.mul_apply]) hmin, pow_two,
    Perm.mul_apply]

namespace RotationSystem

variable {H : Type*} [Fintype H] [DecidableEq H] (R : RotationSystem H)

/-- A rotation system whose involution is fixed-point-free has half as many edges as darts. -/
private theorem two_mul_card_edges (hinv : Involutive R.inv) (hfix : ∀ d, R.inv d ≠ d) :
    2 * R.edges.card = Fintype.card H := by
  have hfib : ∀ s ∈ univ.image R.edgeOf,
      ({a ∈ univ | R.edgeOf a = s} : Finset H).card = 2 := by
    intro s hs
    obtain ⟨d, -, rfl⟩ := mem_image.1 hs
    have : ({a ∈ univ | R.edgeOf a = R.edgeOf d} : Finset H) = R.edgeOf d := by
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_edgeOf]
      constructor
      · exact fun h => R.mem_edgeOf.1 (h ▸ R.mem_edgeOf.2 (Or.inl rfl) : a ∈ R.edgeOf d)
      · rintro (rfl | rfl)
        · rfl
        · ext x
          simp only [mem_edgeOf, hinv d]
          tauto
    rw [this, edgeOf, card_pair (hfix d).symm]
  rw [← card_univ, card_eq_sum_card_image R.edgeOf univ, sum_const_nat hfib, edges, mul_comm]

/-- The orbits of the face permutation are counted by `numOrbits`. -/
private theorem card_faceOrbits_eq_numOrbits : R.faceOrbits.card = numOrbits R.facePerm :=
  (numOrbits_eq_card_image R.facePerm).symm

end RotationSystem

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-! ### The removal of a bivalent vertex -/

/-- The hypotheses of the removal of a bivalent vertex on the dart `d = d₁`: its vertex `v` is
internal and consists of exactly two darts, `d₁` and `d₂ = σ d₁`, and `d̄₁ ≠ d₂`. -/
structure IsBivalentRemovable (d : H) : Prop where
  /-- The vertex `v(d)` is internal. -/
  not_isBoundaryVertex : ¬G.IsBoundaryVertex (G.vertexOf d)
  /-- The vertex `v(d)` consists of exactly two darts. -/
  card_vertexOf : (G.vertexOf d).card = 2
  /-- `d̄₁ ≠ d₂ = σ d₁`. -/
  inv_ne_rot : G.inv d ≠ G.rot d

namespace IsBivalentRemovable

variable {G} {d : H} (hd : G.IsBivalentRemovable d)

include hd

/-- The two darts of `v` are distinct: `d₂ ≠ d₁`. -/
theorem rot_ne : G.rot d ≠ d := by
  intro h
  have hsub : G.vertexOf d ⊆ {d} := by
    intro e he
    rw [RotationSystem.mem_vertexOf] at he
    rw [mem_singleton, ← (he.eq_of_left h)]
  have := (card_le_card hsub).trans (card_singleton d).le
  rw [hd.card_vertexOf] at this
  omega

/-- The rotation exchanges the two darts of `v`: `σ d₂ = d₁`. -/
theorem rot_rot : G.rot (G.rot d) = d := by
  by_contra h
  have h1 : G.rot (G.rot d) ≠ G.rot d := fun h' => hd.rot_ne (G.rot.injective h')
  have hmem : G.rot (G.rot d) ∈ G.vertexOf d := by
    rw [RotationSystem.mem_vertexOf]
    exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))
  have : 2 < (G.vertexOf d).card :=
    two_lt_card.2 ⟨d, G.self_mem_vertexOf d, G.rot d, G.rot_mem_vertexOf d, _, hmem,
      hd.rot_ne.symm, Ne.symm h, h1.symm⟩
  rw [hd.card_vertexOf] at this
  omega

/-- The darts of `v` are `d₁` and `d₂`. -/
theorem mem_vertexOf_iff {e : H} : e ∈ G.vertexOf d ↔ e = d ∨ e = G.rot d := by
  have hsub : ({d, G.rot d} : Finset H) ⊆ G.vertexOf d := by
    intro e he
    rcases mem_insert.1 he with rfl | he
    · exact G.self_mem_vertexOf _
    · rw [mem_singleton.1 he]
      exact G.rot_mem_vertexOf d
  have heq : ({d, G.rot d} : Finset H) = G.vertexOf d :=
    eq_of_subset_of_card_le hsub (by rw [hd.card_vertexOf, card_pair hd.rot_ne.symm])
  rw [← heq, mem_insert, mem_singleton]

/-- The dart `d₁` is not in the boundary `B`. -/
theorem notMem_bdry : d ∉ G.bdry := fun h =>
  hd.not_isBoundaryVertex ⟨d, G.self_mem_vertexOf d, h⟩

/-- The dart `d₂ = σ d₁` is not in the boundary `B`. -/
theorem rot_notMem_bdry : G.rot d ∉ G.bdry := fun h =>
  hd.not_isBoundaryVertex ⟨G.rot d, G.rot_mem_vertexOf d, h⟩

/-- A dart lies in `H' = H \ {d₁, d₂}` iff its image under `σ` does. -/
theorem rot_mem_iff (y : H) :
    G.rot y ∈ ({d, G.rot d}ᶜ : Set H) ↔ y ∈ ({d, G.rot d}ᶜ : Set H) := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  rw [G.rot.injective.eq_iff' hd.rot_rot, G.rot.injective.eq_iff]
  tauto

/-- `d̄₁ ≠ d̄₂`. -/
theorem inv_ne_inv_rot : G.inv d ≠ G.inv (G.rot d) := fun h =>
  hd.rot_ne (G.inv.injective h).symm

/-- A dart of `B` lies in `H'`. -/
theorem mem_of_mem_bdry {y : H} (hy : y ∈ G.bdry) : y ∈ ({d, G.rot d}ᶜ : Set H) := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨fun h => hd.notMem_bdry (h ▸ hy), fun h => hd.rot_notMem_bdry (h ▸ hy)⟩

variable (hG : G.IsPlabicGraph)

include hG

/-- `d̄₂ ≠ d₁`. -/
theorem inv_rot_ne : G.inv (G.rot d) ≠ d := fun h =>
  hd.inv_ne_rot (hG.inv_involutive.eq_iff.1 h).symm

/-- The dart `d̄₁` is not in the boundary `B`. -/
theorem inv_notMem_bdry : G.inv d ∉ G.bdry := fun h =>
  hd.notMem_bdry (hG.inv_mem_bdry_iff.1 h)

/-- The dart `d̄₂` is not in the boundary `B`. -/
theorem inv_rot_notMem_bdry : G.inv (G.rot d) ∉ G.bdry := fun h =>
  hd.rot_notMem_bdry (hG.inv_mem_bdry_iff.1 h)

/-- The dart `d̄₁` lies in `H' = H \ {d₁, d₂}`. -/
theorem inv_mem : G.inv d ∈ ({d, G.rot d}ᶜ : Set H) := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨hG.inv_ne d, hd.inv_ne_rot⟩

/-- The dart `d̄₂` lies in `H' = H \ {d₁, d₂}`. -/
theorem inv_rot_mem : G.inv (G.rot d) ∈ ({d, G.rot d}ᶜ : Set H) := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨hd.inv_rot_ne hG, hG.inv_ne (G.rot d)⟩

/-- The legs avoid the removed vertex. -/
theorem leg_mem (i : Fin b) : G.leg i ∈ ({d, G.rot d}ᶜ : Set H) := by
  have hv : G.IsBoundaryVertex (G.vertexOf (G.leg i)) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨fun h => hd.not_isBoundaryVertex (h ▸ hv), fun h => hd.not_isBoundaryVertex ?_⟩
  rw [← G.vertexOf_rot, ← h]
  exact hv

/-- The involution of `H` exchanging `d̄₁` with `d̄₂` and `d₁` with `d₂`, agreeing with `d ↦ d̄`
elsewhere, preserves `H'`. -/
theorem removalInv_mem_iff (y : H) :
    (swap d (G.inv (G.rot d)) * swap (G.rot d) (G.inv d) * G.inv) y ∈
      ({d, G.rot d}ᶜ : Set H) ↔ y ∈ ({d, G.rot d}ᶜ : Set H) := by
  set ι := swap d (G.inv (G.rot d)) * swap (G.rot d) (G.inv d) * G.inv
  have h1 : ι d = G.rot d := by
    simp only [ι, Perm.mul_apply, swap_apply_right]
    exact swap_apply_of_ne_of_ne hd.rot_ne (hG.inv_ne (G.rot d)).symm
  have h2 : ι (G.rot d) = d := by
    simp only [ι, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne (hG.inv_ne (G.rot d)) hd.inv_ne_inv_rot.symm,
      swap_apply_right]
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  rw [ι.injective.eq_iff' h2, ι.injective.eq_iff' h1]
  tauto

end IsBivalentRemovable

/-- **The removal of a bivalent vertex.** Let `G` be a plabic graph and `v` an internal vertex
consisting of exactly two darts `d₁ = d` and `d₂ = σ d₁`, with `d̄₁ ≠ d₂`. The removal of `v` has
darts `H' = H \ {d₁, d₂}`, the involution `ι'` agreeing with `d ↦ d̄` except that `ι'(d̄₁) = d̄₂`
and `ι'(d̄₂) = d̄₁`, the restriction `σ'` of `σ`, the boundary `B`, the colours of `G` (which
matter only at the internal vertices other than `v`), and the labelling of `G`. -/
@[cluster_algebras "def_bivalent_removal"]
def bivalentRemoval {d : H} (hG : G.IsPlabicGraph) (hd : G.IsBivalentRemovable d) :
    PlabicData (({d, G.rot d}ᶜ : Set H)) b where
  inv := (swap d (G.inv (G.rot d)) * swap (G.rot d) (G.inv d) * G.inv).subtypePerm
    (hd.removalInv_mem_iff hG)
  rot := G.rot.subtypePerm hd.rot_mem_iff
  bdry := G.bdry.subtype (· ∈ ({d, G.rot d}ᶜ : Set H))
  colour y := G.colour y
  leg i := ⟨G.leg i, hd.leg_mem hG i⟩

section Removal

variable {G} {d : H} (hG : G.IsPlabicGraph) (hd : G.IsBivalentRemovable d)

/-- The rotation `σ'` of the removal is the restriction of `σ`. -/
@[simp]
theorem coe_bivalentRemoval_rot (y : ({d, G.rot d}ᶜ : Set H)) :
    ((G.bivalentRemoval hG hd).rot y : H) = G.rot y :=
  rfl

/-- The removal of a bivalent vertex has the legs of `G`. -/
@[cluster_algebras "lem_bivalent_removal_plabic", simp]
theorem coe_bivalentRemoval_leg (i : Fin b) :
    ((G.bivalentRemoval hG hd).leg i : H) = G.leg i :=
  rfl

/-- The removal has the colours of `G`. -/
@[simp]
theorem bivalentRemoval_colour (y : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).colour y = G.colour y :=
  rfl

/-- A dart of `H'` is in the boundary of the removal iff it is in `B`. -/
@[simp]
theorem mem_bivalentRemoval_bdry {y : ({d, G.rot d}ᶜ : Set H)} :
    y ∈ (G.bivalentRemoval hG hd).bdry ↔ (y : H) ∈ G.bdry :=
  mem_subtype

/-- `ι'(d̄₁) = d̄₂`. -/
theorem coe_bivalentRemoval_inv_of_eq_inv {y : ({d, G.rot d}ᶜ : Set H)} (hy : (y : H) = G.inv d) :
    ((G.bivalentRemoval hG hd).inv y : H) = G.inv (G.rot d) := by
  change (swap d (G.inv (G.rot d)) * swap (G.rot d) (G.inv d) * G.inv) y = _
  rw [hy, Perm.mul_apply, Perm.mul_apply, hG.inv_involutive,
    swap_apply_of_ne_of_ne hd.rot_ne.symm (hG.inv_ne d).symm, swap_apply_left]

/-- `ι'(d̄₂) = d̄₁`. -/
theorem coe_bivalentRemoval_inv_of_eq_inv_rot {y : ({d, G.rot d}ᶜ : Set H)}
    (hy : (y : H) = G.inv (G.rot d)) :
    ((G.bivalentRemoval hG hd).inv y : H) = G.inv d := by
  change (swap d (G.inv (G.rot d)) * swap (G.rot d) (G.inv d) * G.inv) y = _
  rw [hy, Perm.mul_apply, Perm.mul_apply, hG.inv_involutive, swap_apply_left,
    swap_apply_of_ne_of_ne (hG.inv_ne d) hd.inv_ne_inv_rot]

/-- Away from `d̄₁` and `d̄₂`, `ι'` agrees with `d ↦ d̄`. -/
theorem coe_bivalentRemoval_inv_of_ne {y : ({d, G.rot d}ᶜ : Set H)} (h₁ : (y : H) ≠ G.inv d)
    (h₂ : (y : H) ≠ G.inv (G.rot d)) :
    ((G.bivalentRemoval hG hd).inv y : H) = G.inv y := by
  change (swap d (G.inv (G.rot d)) * swap (G.rot d) (G.inv d) * G.inv) y = _
  have hy := y.2
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
  have e1 : G.inv y ≠ G.rot d := fun h => h₂ (hG.inv_involutive.eq_iff.1 h)
  have e2 : G.inv y ≠ G.inv d := fun h => hy.1 (G.inv.injective h)
  have e3 : G.inv y ≠ d := fun h => h₁ (hG.inv_involutive.eq_iff.1 h)
  have e4 : G.inv y ≠ G.inv (G.rot d) := fun h => hy.2 (G.inv.injective h)
  rw [Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne e1 e2,
    swap_apply_of_ne_of_ne e3 e4]

/-- On `B`, `ι'` agrees with `d ↦ d̄`. -/
theorem coe_bivalentRemoval_inv_of_mem_bdry {y : ({d, G.rot d}ᶜ : Set H)} (hy : (y : H) ∈ G.bdry) :
    ((G.bivalentRemoval hG hd).inv y : H) = G.inv y :=
  coe_bivalentRemoval_inv_of_ne hG hd (fun h => hd.inv_notMem_bdry hG (h ▸ hy))
    fun h => hd.inv_rot_notMem_bdry hG (h ▸ hy)

/-! #### Faces of the removal -/

/-- The face permutation of the removal is the first-return map of `φ` to `H'`. -/
theorem coe_bivalentRemoval_facePerm (y : ({d, G.rot d}ᶜ : Set H)) :
    ((G.bivalentRemoval hG hd).facePerm y : H) =
      (firstReturn G.facePerm ({d, G.rot d}ᶜ : Set H) y : H) := by
  have hφ : ∀ x, G.facePerm x = G.rot (G.inv x) := fun _ => rfl
  have hinv := hG.inv_involutive
  have hnot : ∀ x : H, x = d ∨ x = G.rot d → x ∉ ({d, G.rot d}ᶜ : Set H) := by
    rintro x (rfl | rfl) <;> simp
  rw [RotationSystem.facePerm_apply, coe_bivalentRemoval_rot]
  by_cases h₁ : (y : H) = G.inv d
  · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd h₁, coe_firstReturn_of_apply_apply_mem ?_ ?_,
      hφ, hφ, h₁, hinv]
    · rw [hφ, h₁, hinv]
      exact hnot _ (Or.inr rfl)
    · rw [hφ, hφ, h₁, hinv]
      exact (hd.rot_mem_iff _).2 (hd.inv_rot_mem hG)
  by_cases h₂ : (y : H) = G.inv (G.rot d)
  · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂, coe_firstReturn_of_apply_apply_mem ?_ ?_,
      hφ, hφ, h₂, hinv, hd.rot_rot]
    · rw [hφ, h₂, hinv, hd.rot_rot]
      exact hnot _ (Or.inl rfl)
    · rw [hφ, hφ, h₂, hinv, hd.rot_rot]
      exact (hd.rot_mem_iff _).2 (hd.inv_mem hG)
  rw [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂]
  symm
  refine coe_firstReturn_of_apply_mem ((hd.rot_mem_iff _).2 ?_)
  have hy := y.2
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy ⊢
  exact ⟨fun h => h₁ (hinv.eq_iff.1 h), fun h => h₂ (hinv.eq_iff.1 h)⟩

/-- The face permutation of the removal, as a permutation, is the first-return map of `φ`. -/
theorem bivalentRemoval_facePerm :
    (G.bivalentRemoval hG hd).facePerm = firstReturnPerm G.facePerm ({d, G.rot d}ᶜ : Set H) :=
  Equiv.ext fun y => Subtype.ext (coe_bivalentRemoval_facePerm hG hd y)

/-- Two darts of `H'` lie in one orbit of `φ'` iff they lie in one orbit of `φ`. -/
theorem sameCycle_bivalentRemoval_facePerm_iff {y z : ({d, G.rot d}ᶜ : Set H)} :
    (G.bivalentRemoval hG hd).facePerm.SameCycle y z ↔ G.facePerm.SameCycle y z := by
  rw [bivalentRemoval_facePerm, sameCycle_firstReturnPerm_iff]

include hG hd in
/-- Every orbit of `φ` meets `H'`. -/
theorem exists_mem_sameCycle_bivalentRemoval (x : H) :
    ∃ y ∈ ({d, G.rot d}ᶜ : Set H), G.facePerm.SameCycle x y := by
  have hinv := hG.inv_involutive
  by_cases hx : x ∈ ({d, G.rot d}ᶜ : Set H)
  · exact ⟨x, hx, SameCycle.refl _ _⟩
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
    not_and_or, not_not] at hx
  rcases hx with rfl | rfl
  · exact ⟨G.inv (G.rot x), hd.inv_rot_mem hG,
      sameCycle_of_eq_apply (by rw [RotationSystem.facePerm_apply, hinv, hd.rot_rot])⟩
  · exact ⟨G.inv d, hd.inv_mem hG,
      sameCycle_of_eq_apply (by rw [RotationSystem.facePerm_apply, hinv])⟩

/-- The orbit of `φ'` through a dart of `H'` is the trace on `H'` of its orbit under `φ`. -/
theorem bivalentRemoval_faceOf (y : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).faceOf y =
      (G.faceOf y).subtype (· ∈ ({d, G.rot d}ᶜ : Set H)) := by
  ext z
  rw [RotationSystem.mem_faceOf, mem_subtype, RotationSystem.mem_faceOf,
    sameCycle_bivalentRemoval_facePerm_iff]

/-- **Faces under the removal of a bivalent vertex**: `f ↦ f ∩ H'` is a bijection from the set of
orbits of `φ = σ ∘ (d ↦ d̄)` onto the set of orbits of `σ' ∘ ι'`. -/
@[cluster_algebras "lem_bivalent_removal_faces"]
theorem bijOn_faceOrbits_bivalentRemoval :
    Set.BijOn (fun f : Finset H => f.subtype (· ∈ ({d, G.rot d}ᶜ : Set H)))
      G.faceOrbits (G.bivalentRemoval hG hd).faceOrbits := by
  have hrep : ∀ f ∈ G.faceOrbits, ∃ y : ({d, G.rot d}ᶜ : Set H), G.faceOf y = f := by
    intro f hf
    obtain ⟨x, rfl⟩ := G.mem_faceOrbits.1 hf
    obtain ⟨y, hy, hxy⟩ := exists_mem_sameCycle_bivalentRemoval hG hd x
    exact ⟨⟨y, hy⟩, (G.faceOf_eq_faceOf_iff.2 hxy).symm⟩
  refine ⟨fun f hf => ?_, fun f hf f' hf' hff' => ?_, fun f' hf' => ?_⟩
  · obtain ⟨y, rfl⟩ := hrep f hf
    dsimp only
    rw [Finset.mem_coe, ← bivalentRemoval_faceOf hG hd y]
    exact RotationSystem.faceOf_mem_faceOrbits _ _
  · obtain ⟨y, rfl⟩ := hrep f hf
    obtain ⟨x', rfl⟩ := G.mem_faceOrbits.1 hf'
    have hy : y ∈ (G.faceOf y).subtype (· ∈ ({d, G.rot d}ᶜ : Set H)) :=
      mem_subtype.2 (G.self_mem_faceOf _)
    simp only at hff'
    rw [hff', mem_subtype] at hy
    exact G.faceOf_eq_of_mem hy
  · obtain ⟨y, rfl⟩ := (G.bivalentRemoval hG hd).mem_faceOrbits.1 (Finset.mem_coe.1 hf')
    exact ⟨G.faceOf y, Finset.mem_coe.2 (G.faceOf_mem_faceOrbits _),
      (bivalentRemoval_faceOf hG hd y).symm⟩

/-! #### Vertices, boundary and exterior of the removal -/

/-- Two darts of `H'` lie in one cycle of `σ'` iff they lie in one cycle of `σ`. -/
theorem sameCycle_bivalentRemoval_rot_iff {y z : ({d, G.rot d}ᶜ : Set H)} :
    (G.bivalentRemoval hG hd).rot.SameCycle y z ↔ G.rot.SameCycle y z :=
  sameCycle_subtypePerm (h := hd.rot_mem_iff)

include hd in
/-- A dart in the vertex of a dart of `H'` lies in `H'`. -/
theorem mem_of_sameCycle_rot_bivalentRemoval {y z : H} (hy : y ∈ ({d, G.rot d}ᶜ : Set H))
    (hyz : G.rot.SameCycle y z) : z ∈ ({d, G.rot d}ᶜ : Set H) := by
  have hy' := hy
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy' ⊢
  have key : G.rot.SameCycle y d → False := fun h => by
    have : y ∈ G.vertexOf d := (RotationSystem.mem_vertexOf _).2 h.symm
    rcases hd.mem_vertexOf_iff.1 this with h' | h'
    · exact hy'.1 h'
    · exact hy'.2 h'
  refine ⟨fun h => key (h ▸ hyz), fun h => key ?_⟩
  rw [h] at hyz
  exact (sameCycle_apply_right.1 hyz)

/-- For darts `y` and `z` of `H'`, `z` lies in the vertex of `y` in the removal iff it does so in
`G`. -/
theorem mem_bivalentRemoval_vertexOf {y z : ({d, G.rot d}ᶜ : Set H)} :
    z ∈ (G.bivalentRemoval hG hd).vertexOf y ↔ (z : H) ∈ G.vertexOf y := by
  rw [RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf,
    sameCycle_bivalentRemoval_rot_iff]

/-- The vertices of the removal are those of `G` other than `v`, with the same darts. -/
theorem map_bivalentRemoval_vertexOf (y : ({d, G.rot d}ᶜ : Set H)) :
    ((G.bivalentRemoval hG hd).vertexOf y).map (Embedding.subtype _) = G.vertexOf y := by
  ext z
  simp only [mem_map, Embedding.coe_subtype]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_bivalentRemoval_vertexOf hG hd).1 hw
  · intro hz
    have hzS := mem_of_sameCycle_rot_bivalentRemoval hd y.2 ((RotationSystem.mem_vertexOf _).1 hz)
    exact ⟨⟨z, hzS⟩, (mem_bivalentRemoval_vertexOf hG hd).2 hz, rfl⟩

/-- The vertex of a dart of `H'` is a boundary vertex of the removal iff its vertex in `G` is a
boundary vertex of `G`. -/
theorem isBoundaryVertex_bivalentRemoval_vertexOf_iff (y : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).IsBoundaryVertex ((G.bivalentRemoval hG hd).vertexOf y) ↔
      G.IsBoundaryVertex (G.vertexOf y) := by
  constructor
  · rintro ⟨z, hz, hzB⟩
    exact ⟨z, (mem_bivalentRemoval_vertexOf hG hd).1 hz, (mem_bivalentRemoval_bdry hG hd).1 hzB⟩
  · rintro ⟨z, hz, hzB⟩
    exact ⟨⟨z, hd.mem_of_mem_bdry hzB⟩, (mem_bivalentRemoval_vertexOf hG hd).2 hz,
      (mem_bivalentRemoval_bdry hG hd).2 hzB⟩

/-- The `i`-th boundary vertex of the removal has the darts of that of `G`. -/
theorem map_bivalentRemoval_bvertex (i : Fin b) :
    ((G.bivalentRemoval hG hd).bvertex i).map (Embedding.subtype _) = G.bvertex i :=
  map_bivalentRemoval_vertexOf hG hd _

/-- The removal has the boundary `B` of `G`. -/
theorem map_bivalentRemoval_bdry :
    (G.bivalentRemoval hG hd).bdry.map (Embedding.subtype _) = G.bdry :=
  subtype_map_of_mem fun _ hy => hd.mem_of_mem_bdry hy

/-- The exterior of the removal is the exterior of `G`, viewed in `H'`. -/
theorem bivalentRemoval_exterior :
    (G.bivalentRemoval hG hd).exterior = G.exterior.subtype (· ∈ ({d, G.rot d}ᶜ : Set H)) := by
  ext y
  rw [DiskMap.mem_exterior, mem_subtype, DiskMap.mem_exterior, mem_bivalentRemoval_bdry,
    mem_bivalentRemoval_bdry, coe_bivalentRemoval_rot]

/-- A dart of `H'` is in the exterior of the removal iff it is in the exterior of `G`. -/
theorem mem_bivalentRemoval_exterior {y : ({d, G.rot d}ᶜ : Set H)} :
    y ∈ (G.bivalentRemoval hG hd).exterior ↔ (y : H) ∈ G.exterior := by
  rw [bivalentRemoval_exterior, mem_subtype]

/-- A dart of `H'` is the image under `ι'` of a dart of the exterior of the removal iff it is the
image under `d ↦ d̄` of a dart of the exterior of `G`. -/
theorem mem_map_inv_bivalentRemoval_exterior {y : ({d, G.rot d}ᶜ : Set H)} :
    y ∈ (G.bivalentRemoval hG hd).exterior.map (G.bivalentRemoval hG hd).inv.toEmbedding ↔
      (y : H) ∈ G.exterior.map G.inv.toEmbedding := by
  simp only [mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' := (mem_bivalentRemoval_exterior hG hd).1 ha
    exact ⟨a, ha', (coe_bivalentRemoval_inv_of_mem_bdry hG hd (G.exterior_subset_bdry ha')).symm⟩
  · rintro ⟨a, ha, hay⟩
    refine ⟨⟨a, hd.mem_of_mem_bdry (G.exterior_subset_bdry ha)⟩,
      (mem_bivalentRemoval_exterior hG hd).2 ha,
      Subtype.ext
        ((coe_bivalentRemoval_inv_of_mem_bdry hG hd (G.exterior_subset_bdry ha)).trans hay)⟩

/-! #### The removal is a plabic graph -/

/-- If `F` is a bijection from `s` onto `t` and `P a ↔ Q (F a)` for every `a ∈ s`, then `s` and
`t` have the same number of elements satisfying `P` and `Q` respectively. -/
private theorem card_filter_eq_of_bijOn {α β : Type*} {F : α → β} {s : Finset α} {t : Finset β}
    (h : Set.BijOn F s t) {P : α → Prop} {Q : β → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ a ∈ s, P a ↔ Q (F a)) : (s.filter P).card = (t.filter Q).card := by
  refine card_nbij F (fun a ha => ?_) (fun a ha a' ha' e => ?_) (fun c hc => ?_)
  · rw [mem_coe, mem_filter] at ha ⊢
    exact ⟨h.mapsTo ha.1, (hPQ a ha.1).1 ha.2⟩
  · rw [mem_coe, mem_filter] at ha ha'
    exact h.injOn ha.1 ha'.1 e
  · rw [mem_coe, mem_filter] at hc
    obtain ⟨a, ha, rfl⟩ := h.surjOn hc.1
    exact ⟨a, by rw [mem_coe, mem_filter]; exact ⟨ha, (hPQ a ha).2 hc.2⟩, rfl⟩

/-- The involution `ι'` of the removal is an involution. -/
theorem bivalentRemoval_inv_involutive : Involutive (G.bivalentRemoval hG hd).inv := by
  intro y
  apply Subtype.ext
  by_cases h₁ : (y : H) = G.inv d
  · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd (coe_bivalentRemoval_inv_of_eq_inv hG hd h₁),
      h₁]
  by_cases h₂ : (y : H) = G.inv (G.rot d)
  · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd (coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂),
      h₂]
  have hy := y.2
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
  have e := coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂
  rw [coe_bivalentRemoval_inv_of_ne hG hd (by rw [e]; exact fun h => hy.1 (G.inv.injective h))
    (by rw [e]; exact fun h => hy.2 (G.inv.injective h)), e, hG.inv_involutive]

/-- The involution `ι'` of the removal has no fixed points. -/
theorem bivalentRemoval_inv_ne (y : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).inv y ≠ y := by
  intro h
  have h' := congrArg Subtype.val h
  by_cases h₁ : (y : H) = G.inv d
  · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd h₁, h₁] at h'
    exact hd.inv_ne_inv_rot h'.symm
  by_cases h₂ : (y : H) = G.inv (G.rot d)
  · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂, h₂] at h'
    exact hd.inv_ne_inv_rot h'
  rw [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂] at h'
  exact hG.inv_ne _ h'

open Classical in
/-- The projection of `H` onto `H'` sending `d₁ ↦ d̄₁`, `d₂ ↦ d̄₂` and fixing `H'`. -/
private def reachProj (e : H) : ({d, G.rot d}ᶜ : Set H) :=
  if h : e ∈ ({d, G.rot d}ᶜ : Set H) then ⟨e, h⟩ else if e = d then ⟨G.inv d, hd.inv_mem hG⟩
    else ⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩

private theorem reachProj_of_mem {e : H} (he : e ∈ ({d, G.rot d}ᶜ : Set H)) :
    reachProj hG hd e = ⟨e, he⟩ :=
  dif_pos he

private theorem reachProj_self : reachProj hG hd d = ⟨G.inv d, hd.inv_mem hG⟩ := by
  simp [reachProj]

private theorem reachProj_rot :
    reachProj hG hd (G.rot d) = ⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩ := by
  simp [reachProj, hd.rot_ne]

private theorem reach_reachProj_rot (e : H) :
    (G.bivalentRemoval hG hd).Reach (reachProj hG hd e) (reachProj hG hd (G.rot e)) := by
  by_cases he : e ∈ ({d, G.rot d}ᶜ : Set H)
  · have : reachProj hG hd (G.rot e) = (G.bivalentRemoval hG hd).rot (reachProj hG hd e) := by
      rw [reachProj_of_mem hG hd he, reachProj_of_mem hG hd ((hd.rot_mem_iff e).2 he)]
      rfl
    rw [this]
    exact (RotationSystem.Reach.refl _).rot
  have h₁₂ : (G.bivalentRemoval hG hd).inv ⟨G.inv d, hd.inv_mem hG⟩ =
      ⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩ :=
    Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv hG hd rfl)
  have h₂₁ : (G.bivalentRemoval hG hd).inv ⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩ =
      ⟨G.inv d, hd.inv_mem hG⟩ :=
    Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv_rot hG hd rfl)
  obtain rfl | rfl : e = d ∨ e = G.rot d := by
    simpa [or_iff_not_imp_left] using he
  · rw [reachProj_self, reachProj_rot, ← h₁₂]
    exact (RotationSystem.Reach.refl _).inv
  · rw [hd.rot_rot, reachProj_self, reachProj_rot, ← h₂₁]
    exact (RotationSystem.Reach.refl _).inv

private theorem reach_reachProj_inv (e : H) :
    (G.bivalentRemoval hG hd).Reach (reachProj hG hd e) (reachProj hG hd (G.inv e)) := by
  have hinv := hG.inv_involutive
  by_cases he : e ∈ ({d, G.rot d}ᶜ : Set H)
  · by_cases h₁ : e = G.inv d
    · subst h₁
      rw [hinv, reachProj_self, reachProj_of_mem hG hd he]
      exact RotationSystem.Reach.refl _
    by_cases h₂ : e = G.inv (G.rot d)
    · subst h₂
      rw [hinv, reachProj_rot, reachProj_of_mem hG hd he]
      exact RotationSystem.Reach.refl _
    have hie : G.inv e ∈ ({d, G.rot d}ᶜ : Set H) := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => h₁ (hinv.eq_iff.1 h), fun h => h₂ (hinv.eq_iff.1 h)⟩
    have : reachProj hG hd (G.inv e) = (G.bivalentRemoval hG hd).inv (reachProj hG hd e) := by
      rw [reachProj_of_mem hG hd he, reachProj_of_mem hG hd hie]
      exact Subtype.ext (coe_bivalentRemoval_inv_of_ne hG hd (y := ⟨e, he⟩) h₁ h₂).symm
    rw [this]
    exact (RotationSystem.Reach.refl _).inv
  obtain rfl | rfl : e = d ∨ e = G.rot d := by
    simpa [or_iff_not_imp_left] using he
  · rw [reachProj_self, reachProj_of_mem hG hd (hd.inv_mem hG)]
    exact RotationSystem.Reach.refl _
  · rw [reachProj_rot, reachProj_of_mem hG hd (hd.inv_rot_mem hG)]
    exact RotationSystem.Reach.refl _

/-- Any two darts of the removal of a bivalent vertex are connected. -/
theorem bivalentRemoval_reach (y z : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).Reach y z := by
  have main : ∀ a e, G.Reach a e →
      (G.bivalentRemoval hG hd).Reach (reachProj hG hd a) (reachProj hG hd e) := by
    intro a e h
    induction h with
    | refl => exact RotationSystem.Reach.refl _
    | rot _ ih => exact ih.trans (reach_reachProj_rot hG hd _)
    | inv _ ih => exact ih.trans (reach_reachProj_inv hG hd _)
  have := main y z (hG.toIsConnected.reach y z)
  rwa [reachProj_of_mem hG hd y.2, reachProj_of_mem hG hd z.2] at this

/-- The removal has as many orbits of its face permutation as `G`. -/
theorem card_bivalentRemoval_faceOrbits :
    (G.bivalentRemoval hG hd).faceOrbits.card = G.faceOrbits.card :=
  (card_nbij _ (bijOn_faceOrbits_bivalentRemoval hG hd).mapsTo
    (bijOn_faceOrbits_bivalentRemoval hG hd).injOn
    (bijOn_faceOrbits_bivalentRemoval hG hd).surjOn).symm

/-- The removal has one vertex fewer than `G`. -/
theorem card_bivalentRemoval_vertices_add_one :
    (G.bivalentRemoval hG hd).vertices.card + 1 = G.vertices.card := by
  have himage : (G.bivalentRemoval hG hd).vertices.image (Finset.map (Embedding.subtype _)) =
      G.vertices.erase (G.vertexOf d) := by
    ext w
    simp only [mem_image, mem_erase, RotationSystem.mem_vertices]
    constructor
    · rintro ⟨w', ⟨y, rfl⟩, rfl⟩
      rw [map_bivalentRemoval_vertexOf hG hd y]
      refine ⟨fun h => ?_, y, rfl⟩
      have hy : (y : H) ∈ G.vertexOf d := h ▸ G.self_mem_vertexOf _
      exact y.2 (by rcases hd.mem_vertexOf_iff.1 hy with h' | h' <;> simp [h'])
    · rintro ⟨hne, x, rfl⟩
      have hx : x ∈ ({d, G.rot d}ᶜ : Set H) := by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨fun h => hne (h ▸ rfl), fun h => hne ?_⟩
        rw [h, RotationSystem.vertexOf_rot]
      exact ⟨_, ⟨⟨x, hx⟩, rfl⟩, map_bivalentRemoval_vertexOf hG hd ⟨x, hx⟩⟩
  have hcard := card_image_of_injective (G.bivalentRemoval hG hd).vertices
    (Finset.map_injective (Embedding.subtype (· ∈ ({d, G.rot d}ᶜ : Set H))))
  rw [himage, card_erase_of_mem (G.vertexOf_mem_vertices d)] at hcard
  have hpos : 0 < G.vertices.card := card_pos.2 ⟨_, G.vertexOf_mem_vertices d⟩
  omega

/-- The removal has one edge fewer than `G`. -/
theorem card_bivalentRemoval_edges_add_one :
    (G.bivalentRemoval hG hd).edges.card + 1 = G.edges.card := by
  have h1 := RotationSystem.two_mul_card_edges (G.bivalentRemoval hG hd).toRotationSystem
    (bivalentRemoval_inv_involutive hG hd) (bivalentRemoval_inv_ne hG hd)
  have h2 := RotationSystem.two_mul_card_edges G.toRotationSystem hG.inv_involutive hG.inv_ne
  have h3 : Fintype.card (({d, G.rot d}ᶜ : Set H)) = Fintype.card H - 2 := by
    rw [Fintype.card_compl_set]
    simp [hd.rot_ne.symm]
  have h4 : 2 ≤ Fintype.card H := by
    rw [← card_univ]
    exact (card_pair hd.rot_ne.symm).symm.le.trans (card_le_univ _)
  change 2 * (G.bivalentRemoval hG hd).edges.card = _ at h1
  change 2 * G.edges.card = _ at h2
  omega

/-- The removal of a bivalent vertex is a disk map. -/
theorem bivalentRemoval_isDiskMap : (G.bivalentRemoval hG hd).IsDiskMap where
  nonempty := ⟨⟨G.inv d, hd.inv_mem hG⟩⟩
  inv_involutive := bivalentRemoval_inv_involutive hG hd
  inv_ne := bivalentRemoval_inv_ne hG hd
  transitive y z := RotationSystem.reach_iff_exists_mem_closure _ |>.1
    (bivalentRemoval_reach hG hd y z)
  inv_mem_bdry y hy := by
    rw [mem_bivalentRemoval_bdry] at hy ⊢
    rw [coe_bivalentRemoval_inv_of_mem_bdry hG hd hy]
    exact hG.inv_mem_bdry _ hy
  euler := by
    have hV := card_bivalentRemoval_vertices_add_one hG hd
    have hE := card_bivalentRemoval_edges_add_one hG hd
    have := hG.euler
    change ((G.bivalentRemoval hG hd).vertices.card : ℤ) - (G.bivalentRemoval hG hd).edges.card +
      (G.bivalentRemoval hG hd).faceOrbits.card = 2
    rw [card_bivalentRemoval_faceOrbits hG hd]
    omega
  boundaryVertex_card w hw := by
    obtain ⟨hwV, hwB⟩ := (DiskMap.mem_boundaryVertices _).1 hw
    obtain ⟨y, rfl⟩ := RotationSystem.mem_vertices _ |>.1 hwV
    have hb : G.vertexOf y ∈ G.boundaryVertices := G.vertexOf_mem_boundaryVertices.2
      ((isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd y).1 hwB)
    obtain ⟨h3, h2⟩ := hG.boundaryVertex_card _ hb
    refine ⟨?_, ?_⟩
    · rw [← card_map (Embedding.subtype _), map_bivalentRemoval_vertexOf hG hd y, h3]
    · rw [← h2, ← map_bivalentRemoval_vertexOf hG hd y, filter_map, card_map]
      congr 1
      exact filter_congr fun z _ => mem_bivalentRemoval_bdry hG hd
  exists_orbit := by
    refine ⟨(G.bivalentRemoval hG hd).exterior, ?_, fun y hy => ?_, ?_, ?_⟩
    · rw [bivalentRemoval_exterior]
      exact (bijOn_faceOrbits_bivalentRemoval hG hd).mapsTo hG.exterior_mem_faceOrbits
    · rw [mem_bivalentRemoval_exterior] at hy
      exact (mem_bivalentRemoval_bdry hG hd).2 (G.exterior_subset_bdry hy)
    · ext y
      rw [mem_union, mem_bivalentRemoval_exterior, mem_map_inv_bivalentRemoval_exterior,
        mem_bivalentRemoval_bdry, ← mem_union, hG.exterior_union_map_inv]
    · exact disjoint_left.2 fun y hy hy' => disjoint_left.1 hG.disjoint_exterior_map_inv
        ((mem_bivalentRemoval_exterior hG hd).1 hy)
        ((mem_map_inv_bivalentRemoval_exterior hG hd).1 hy')

/-- **Removing a bivalent vertex gives a plabic graph.** -/
@[cluster_algebras "lem_bivalent_removal_plabic"]
theorem isPlabicGraph_bivalentRemoval : (G.bivalentRemoval hG hd).IsPlabicGraph where
  toIsDiskMap := bivalentRemoval_isDiskMap hG hd
  one_le := hG.one_le
  colour_rot y hy := by
    rw [isBoundaryVertex_bivalentRemoval_vertexOf_iff] at hy
    exact hG.colour_rot y hy
  leg_notMem_bdry i := by
    rw [mem_bivalentRemoval_bdry, coe_bivalentRemoval_leg]
    exact hG.leg_notMem_bdry i
  bvertex_mem i := by
    refine (G.bivalentRemoval hG hd).vertexOf_mem_boundaryVertices.2 ?_
    rw [isBoundaryVertex_bivalentRemoval_vertexOf_iff, coe_bivalentRemoval_leg]
    exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  bvertex_injective i j hij := by
    apply hG.bvertex_injective
    rw [← map_bivalentRemoval_bvertex hG hd, ← map_bivalentRemoval_bvertex hG hd, hij]
  exists_bvertex_eq w hw := by
    obtain ⟨hwV, hwB⟩ := (DiskMap.mem_boundaryVertices _).1 hw
    obtain ⟨y, rfl⟩ := RotationSystem.mem_vertices _ |>.1 hwV
    have hb : G.vertexOf y ∈ G.boundaryVertices := G.vertexOf_mem_boundaryVertices.2
      ((isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd y).1 hwB)
    obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ hb
    refine ⟨i, Finset.map_injective (Embedding.subtype _) ?_⟩
    rw [map_bivalentRemoval_bvertex, map_bivalentRemoval_vertexOf, hi]
  exists_exterior i := by
    obtain ⟨e, he, he1, he2⟩ := hG.exists_exterior i
    refine ⟨⟨e, hd.mem_of_mem_bdry (G.exterior_subset_bdry he)⟩,
      (mem_bivalentRemoval_exterior hG hd).2 he, ?_, ?_⟩
    · rw [← mem_map' (Embedding.subtype _), map_bivalentRemoval_bvertex]
      exact he1
    · rw [← mem_map' (Embedding.subtype _), map_bivalentRemoval_bvertex, Embedding.coe_subtype,
        coe_bivalentRemoval_inv_of_mem_bdry hG hd (G.exterior_subset_bdry he)]
      exact he2

/-- The removal of a bivalent vertex has the boundary vertices of `G`, with the same darts. -/
@[cluster_algebras "lem_bivalent_removal_plabic"]
theorem image_bivalentRemoval_boundaryVertices :
    (G.bivalentRemoval hG hd).boundaryVertices.image (Finset.map (Embedding.subtype _)) =
      G.boundaryVertices := by
  ext w
  simp only [mem_image]
  constructor
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨hwV, hwB⟩ := (DiskMap.mem_boundaryVertices _).1 hw'
    obtain ⟨y, rfl⟩ := RotationSystem.mem_vertices _ |>.1 hwV
    rw [map_bivalentRemoval_vertexOf]
    exact G.vertexOf_mem_boundaryVertices.2
      ((isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd y).1 hwB)
  · intro hw
    obtain ⟨hwV, hwB⟩ := (DiskMap.mem_boundaryVertices _).1 hw
    obtain ⟨x, rfl⟩ := RotationSystem.mem_vertices _ |>.1 hwV
    obtain ⟨e, he, heB⟩ := hwB
    refine ⟨(G.bivalentRemoval hG hd).vertexOf ⟨e, hd.mem_of_mem_bdry heB⟩, ?_, ?_⟩
    · exact (G.bivalentRemoval hG hd).vertexOf_mem_boundaryVertices.2
        ((isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd _).2 ⟨e, G.self_mem_vertexOf e, heB⟩)
    · rw [map_bivalentRemoval_vertexOf, G.vertexOf_eq_of_mem he]

/-- The removal of a bivalent vertex has as many faces as `G`. -/
@[cluster_algebras "lem_bivalent_removal_plabic"]
theorem card_bivalentRemoval_faces :
    (G.bivalentRemoval hG hd).faces.card = G.faces.card := by
  have hb := bijOn_faceOrbits_bivalentRemoval hG hd
  rw [DiskMap.faces, DiskMap.faces, ← filter_ne', ← filter_ne']
  refine (card_filter_eq_of_bijOn hb fun f hf => ?_).symm
  rw [bivalentRemoval_exterior]
  exact (hb.injOn.ne_iff hf hG.exterior_mem_faceOrbits).symm

/-- The removal of a bivalent vertex has as many internal faces as `G`. -/
@[cluster_algebras "lem_bivalent_removal_plabic"]
theorem card_bivalentRemoval_internalFaces :
    (G.bivalentRemoval hG hd).internalFaces.card = G.internalFaces.card := by
  have hb := bijOn_faceOrbits_bivalentRemoval hG hd
  rw [DiskMap.internalFaces, DiskMap.internalFaces, DiskMap.faces, DiskMap.faces, ← filter_ne',
    ← filter_ne', filter_filter, filter_filter]
  refine (card_filter_eq_of_bijOn hb fun f hf => ?_).symm
  rw [bivalentRemoval_exterior, ← (hb.injOn.ne_iff hf hG.exterior_mem_faceOrbits)]
  refine and_congr_right fun _ => ?_
  refine ⟨fun h => disjoint_left.2 fun z hz hzB => ?_, fun h => disjoint_left.2 fun z hz hzB => ?_⟩
  · rw [mem_subtype] at hz
    exact disjoint_left.1 h hz ((mem_bivalentRemoval_bdry hG hd).1 hzB)
  · exact disjoint_left.1 h
      (show (⟨z, hd.mem_of_mem_bdry hzB⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ _ from mem_subtype.2 hz)
      ((mem_bivalentRemoval_bdry hG hd).2 hzB)

end Removal

/-! ### Inserting a bivalent vertex -/

/-- **Inserting a bivalent vertex**: the insertion of a vertex of colour `c` on the edge
`{d, d̄}`. The darts are `H ⊕ Fin 2`, the two new darts being `f = Sum.inr 0` and
`f* = Sum.inr 1`; the involution pairs `d` with `f` and `f*` with `d̄` and agrees with `d ↦ d̄`
elsewhere (when `d ↦ d̄` is a fixed-point-free involution, see `bivalentInsertion_inv_inl_self`
and its companions); the rotation extends `σ` by the cycle `(f, f*)`; the colouring extends that
of `G` by giving the vertex `{f, f*}` the colour `c`; and `B` and the labelling are those of
`G`. -/
@[cluster_algebras "def_bivalent_insertion"]
def bivalentInsertion (d : H) (c : Shade) : PlabicData (H ⊕ Fin 2) b where
  inv := Equiv.swap (Sum.inl d) (Sum.inr 0) * Equiv.swap (Sum.inl (G.inv d)) (Sum.inr 1) *
    Equiv.swap (Sum.inl d) (Sum.inl (G.inv d)) * Perm.sumCongr G.inv 1
  rot := Perm.sumCongr G.rot (Equiv.swap 0 1)
  bdry := G.bdry.map Embedding.inl
  colour := Sum.elim G.colour fun _ => c
  leg i := Sum.inl (G.leg i)

private theorem sumCongr_pow {α β : Type*} (f : Perm α) (g : Perm β) (n : ℕ) :
    Perm.sumCongr f g ^ n = Perm.sumCongr (f ^ n) (g ^ n) := by
  simpa using (map_pow (sumCongrHom α β) (f, g) n).symm

private theorem fin_two_eq (k : Fin 2) : k = 0 ∨ k = 1 := by
  rcases k with ⟨_ | _ | k, hk⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

section Insertion

variable {G} (d : H) (c : Shade)

section Raw

omit [Fintype H]

/-- On the darts of `H`, the rotation of the insertion is `σ`. -/
@[simp]
theorem bivalentInsertion_rot_inl (e : H) :
    (G.bivalentInsertion d c).rot (Sum.inl e) = Sum.inl (G.rot e) :=
  rfl

/-- The rotation of the insertion sends `f = Sum.inr 0` to `f* = Sum.inr 1`. -/
@[simp]
theorem bivalentInsertion_rot_inr_zero : (G.bivalentInsertion d c).rot (Sum.inr 0) = Sum.inr 1 := by
  simp [bivalentInsertion]

/-- The rotation of the insertion sends `f* = Sum.inr 1` to `f = Sum.inr 0`. -/
@[simp]
theorem bivalentInsertion_rot_inr_one : (G.bivalentInsertion d c).rot (Sum.inr 1) = Sum.inr 0 := by
  simp [bivalentInsertion]

/-- The insertion of a bivalent vertex has the legs of `G`. -/
@[cluster_algebras "lem_bivalent_insertion_plabic", simp]
theorem bivalentInsertion_leg (i : Fin b) :
    (G.bivalentInsertion d c).leg i = Sum.inl (G.leg i) :=
  rfl

/-- On the darts of `H`, the insertion has the colours of `G`. -/
@[simp]
theorem bivalentInsertion_colour_inl (e : H) :
    (G.bivalentInsertion d c).colour (Sum.inl e) = G.colour e :=
  rfl

/-- The new darts `f` and `f*` have the colour `c`. -/
@[simp]
theorem bivalentInsertion_colour_inr (j : Fin 2) :
    (G.bivalentInsertion d c).colour (Sum.inr j) = c :=
  rfl

/-- A dart of `H` is in the boundary of the insertion iff it is in `B`. -/
@[simp]
theorem inl_mem_bivalentInsertion_bdry {e : H} :
    Sum.inl e ∈ (G.bivalentInsertion d c).bdry ↔ e ∈ G.bdry := by
  simp [bivalentInsertion]

/-- The new darts `f` and `f*` are not in the boundary of the insertion. -/
@[simp]
theorem inr_notMem_bivalentInsertion_bdry (j : Fin 2) :
    Sum.inr j ∉ (G.bivalentInsertion d c).bdry := by
  simp [bivalentInsertion]

/-- `f = Sum.inr 0` is paired with `d`. -/
@[simp]
theorem bivalentInsertion_inv_inr_zero :
    (G.bivalentInsertion d c).inv (Sum.inr 0) = Sum.inl d := by
  simp [bivalentInsertion, Perm.mul_apply, swap_apply_of_ne_of_ne]

variable {d}

/-- `d` is paired with `f = Sum.inr 0`. -/
theorem bivalentInsertion_inv_inl_self (hfix : G.inv d ≠ d) :
    (G.bivalentInsertion d c).inv (Sum.inl d) = Sum.inr 0 := by
  simp [bivalentInsertion, Perm.mul_apply, swap_apply_of_ne_of_ne, hfix.symm]

/-- `f* = Sum.inr 1` is paired with `d̄`. -/
theorem bivalentInsertion_inv_inr_one (hfix : G.inv d ≠ d) :
    (G.bivalentInsertion d c).inv (Sum.inr 1) = Sum.inl (G.inv d) := by
  simp [bivalentInsertion, Perm.mul_apply, swap_apply_of_ne_of_ne, hfix]

/-- `d̄` is paired with `f* = Sum.inr 1`. -/
theorem bivalentInsertion_inv_inl_inv (hinv : Involutive G.inv) :
    (G.bivalentInsertion d c).inv (Sum.inl (G.inv d)) = Sum.inr 1 := by
  simp [bivalentInsertion, Perm.mul_apply, swap_apply_of_ne_of_ne, hinv d]

/-- Away from `d` and `d̄` the involution of the insertion is `d ↦ d̄`. -/
theorem bivalentInsertion_inv_inl_of_ne (hinv : Involutive G.inv) {e : H} (h₁ : e ≠ d)
    (h₂ : e ≠ G.inv d) :
    (G.bivalentInsertion d c).inv (Sum.inl e) = Sum.inl (G.inv e) := by
  have h₃ : G.inv e ≠ d := fun h => h₂ (hinv.eq_iff.1 h)
  have h₄ : G.inv e ≠ G.inv d := fun h => h₁ (G.inv.injective h)
  simp [bivalentInsertion, Perm.mul_apply, swap_apply_of_ne_of_ne, h₃, h₄]

/-- If `d ↦ d̄` is an involution without a fixed point at `d`, then so is the involution of the
insertion. -/
theorem bivalentInsertion_inv_involutive (hinv : Involutive G.inv) (hfix : G.inv d ≠ d) :
    Involutive (G.bivalentInsertion d c).inv := by
  rintro (e | j)
  · by_cases h₁ : e = d
    · rw [h₁, bivalentInsertion_inv_inl_self c hfix, bivalentInsertion_inv_inr_zero]
    by_cases h₂ : e = G.inv d
    · rw [h₂, bivalentInsertion_inv_inl_inv c hinv, bivalentInsertion_inv_inr_one c hfix]
    rw [bivalentInsertion_inv_inl_of_ne c hinv h₁ h₂,
      bivalentInsertion_inv_inl_of_ne c hinv (fun h => h₂ (hinv.eq_iff.1 h))
        (fun h => h₁ (G.inv.injective h)), hinv]
  · rcases fin_two_eq j with rfl | rfl
    · rw [bivalentInsertion_inv_inr_zero, bivalentInsertion_inv_inl_self c hfix]
    · rw [bivalentInsertion_inv_inr_one c hfix, bivalentInsertion_inv_inl_inv c hinv]

/-- If `d ↦ d̄` is a fixed-point-free involution, then so is the involution of the insertion. -/
theorem bivalentInsertion_inv_ne (hinv : Involutive G.inv) (hfix : ∀ e, G.inv e ≠ e)
    (y : H ⊕ Fin 2) : (G.bivalentInsertion d c).inv y ≠ y := by
  rcases y with e | j
  · by_cases h₁ : e = d
    · rw [h₁, bivalentInsertion_inv_inl_self c (hfix d)]
      exact Sum.inr_ne_inl
    by_cases h₂ : e = G.inv d
    · rw [h₂, bivalentInsertion_inv_inl_inv c hinv]
      exact Sum.inr_ne_inl
    rw [bivalentInsertion_inv_inl_of_ne c hinv h₁ h₂]
    exact fun h => hfix e (Sum.inl_injective h)
  · rcases fin_two_eq j with rfl | rfl
    · rw [bivalentInsertion_inv_inr_zero]
      exact Sum.inl_ne_inr
    · rw [bivalentInsertion_inv_inr_one c (hfix d)]
      exact Sum.inl_ne_inr

end Raw

/-! #### Vertices, boundary and exterior of the insertion -/

/-- In the insertion, the vertex of a dart of `H` consists of the darts of its vertex in `G`. -/
theorem bivalentInsertion_vertexOf_inl (e : H) :
    (G.bivalentInsertion d c).vertexOf (Sum.inl e) = (G.vertexOf e).map Embedding.inl := by
  ext z
  rw [RotationSystem.mem_vertexOf, mem_map]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    refine ⟨(G.rot ^ n) e, (RotationSystem.mem_vertexOf _).2 (sameCycle_pow_apply_self _ _ _), ?_⟩
    change _ = (Perm.sumCongr G.rot (Equiv.swap 0 1) ^ n) (Sum.inl e)
    rw [sumCongr_pow, Perm.sumCongr_apply, Sum.map_inl]
    rfl
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨n, hn⟩ := ((RotationSystem.mem_vertexOf _).1 ha).exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    change (Perm.sumCongr G.rot (Equiv.swap 0 1) ^ n) (Sum.inl e) = _
    rw [sumCongr_pow, Perm.sumCongr_apply, Sum.map_inl, hn]
    rfl

/-- In the insertion, the vertex of each new dart is `{f, f*}`. -/
theorem bivalentInsertion_vertexOf_inr (j : Fin 2) :
    (G.bivalentInsertion d c).vertexOf (Sum.inr j) = {Sum.inr 0, Sum.inr 1} := by
  have h01 : (G.bivalentInsertion d c).rot.SameCycle (Sum.inr 0) (Sum.inr 1) :=
    (sameCycle_of_eq_apply (bivalentInsertion_rot_inr_zero d c)).symm
  ext z
  rw [RotationSystem.mem_vertexOf, mem_insert, mem_singleton]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    change (Perm.sumCongr G.rot (Equiv.swap 0 1) ^ n) (Sum.inr j) = _ ∨
      (Perm.sumCongr G.rot (Equiv.swap 0 1) ^ n) (Sum.inr j) = _
    rw [sumCongr_pow, Perm.sumCongr_apply, Sum.map_inr]
    rcases fin_two_eq ((Equiv.swap (0 : Fin 2) 1 ^ n) j) with h | h <;> rw [h] <;> simp
  · rintro (rfl | rfl) <;> rcases fin_two_eq j with rfl | rfl
    · exact SameCycle.refl _ _
    · exact h01.symm
    · exact h01
    · exact SameCycle.refl _ _

/-- The vertex of a dart of `H` is a boundary vertex of the insertion iff its vertex in `G` is a
boundary vertex of `G`. -/
theorem isBoundaryVertex_bivalentInsertion_vertexOf_inl (e : H) :
    (G.bivalentInsertion d c).IsBoundaryVertex ((G.bivalentInsertion d c).vertexOf (Sum.inl e)) ↔
      G.IsBoundaryVertex (G.vertexOf e) := by
  rw [bivalentInsertion_vertexOf_inl]
  constructor
  · rintro ⟨z, hz, hzB⟩
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hz
    exact ⟨a, ha, (inl_mem_bivalentInsertion_bdry d c).1 hzB⟩
  · rintro ⟨a, ha, haB⟩
    exact ⟨Sum.inl a, mem_map_of_mem _ ha, (inl_mem_bivalentInsertion_bdry d c).2 haB⟩

/-- The new vertex `{f, f*}` is not a boundary vertex of the insertion. -/
theorem not_isBoundaryVertex_bivalentInsertion_vertexOf_inr (j : Fin 2) :
    ¬(G.bivalentInsertion d c).IsBoundaryVertex
      ((G.bivalentInsertion d c).vertexOf (Sum.inr j)) := by
  rw [bivalentInsertion_vertexOf_inr]
  rintro ⟨z, hz, hzB⟩
  rcases mem_insert.1 hz with rfl | hz
  · exact inr_notMem_bivalentInsertion_bdry d c 0 hzB
  · rw [mem_singleton.1 hz] at hzB
    exact inr_notMem_bivalentInsertion_bdry d c 1 hzB

omit [Fintype H] in
/-- The insertion has the exterior of `G`. -/
theorem bivalentInsertion_exterior :
    (G.bivalentInsertion d c).exterior = G.exterior.map Embedding.inl := by
  ext z
  rcases z with e | j
  · rw [DiskMap.mem_exterior, bivalentInsertion_rot_inl, inl_mem_bivalentInsertion_bdry,
      inl_mem_bivalentInsertion_bdry]
    simp [DiskMap.mem_exterior]
  · rw [DiskMap.mem_exterior]
    simp

/-- The vertices of the insertion are those of `G`, with the same darts, together with the new
vertex `{f, f*}`. -/
theorem bivalentInsertion_vertices :
    (G.bivalentInsertion d c).vertices =
      insert {Sum.inr 0, Sum.inr 1} (G.vertices.image (Finset.map Embedding.inl)) := by
  ext w
  simp only [RotationSystem.mem_vertices, mem_insert, mem_image]
  constructor
  · rintro ⟨y, rfl⟩
    rcases y with e | j
    · exact Or.inr ⟨G.vertexOf e, ⟨e, rfl⟩, (bivalentInsertion_vertexOf_inl d c e).symm⟩
    · exact Or.inl (bivalentInsertion_vertexOf_inr d c j)
  · rintro (rfl | ⟨v, ⟨e, rfl⟩, rfl⟩)
    · exact ⟨Sum.inr 0, bivalentInsertion_vertexOf_inr d c 0⟩
    · exact ⟨Sum.inl e, bivalentInsertion_vertexOf_inl d c e⟩

/-- The insertion has one vertex more than `G`. -/
theorem card_bivalentInsertion_vertices :
    (G.bivalentInsertion d c).vertices.card = G.vertices.card + 1 := by
  rw [bivalentInsertion_vertices, card_insert_of_notMem, card_image_of_injective _
    (Finset.map_injective _)]
  rw [mem_image]
  rintro ⟨v, -, hv⟩
  have : (Sum.inr 0 : H ⊕ Fin 2) ∈ v.map Embedding.inl := by
    rw [hv]
    exact mem_insert_self _ _
  obtain ⟨a, -, ha⟩ := mem_map.1 this
  exact Sum.inl_ne_inr ha

/-- The insertion of a bivalent vertex has the boundary vertices of `G`, with the same darts. -/
@[cluster_algebras "lem_bivalent_insertion_plabic"]
theorem bivalentInsertion_boundaryVertices :
    (G.bivalentInsertion d c).boundaryVertices =
      G.boundaryVertices.image (Finset.map Embedding.inl) := by
  ext w
  rw [DiskMap.mem_boundaryVertices, mem_image]
  constructor
  · rintro ⟨hwV, hwB⟩
    obtain ⟨y, rfl⟩ := RotationSystem.mem_vertices _ |>.1 hwV
    rcases y with e | j
    · exact ⟨G.vertexOf e, G.vertexOf_mem_boundaryVertices.2
        ((isBoundaryVertex_bivalentInsertion_vertexOf_inl d c e).1 hwB),
        (bivalentInsertion_vertexOf_inl d c e).symm⟩
    · exact absurd hwB (not_isBoundaryVertex_bivalentInsertion_vertexOf_inr d c j)
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hvV, hvB⟩ := (DiskMap.mem_boundaryVertices _).1 hv
    obtain ⟨e, rfl⟩ := RotationSystem.mem_vertices _ |>.1 hvV
    rw [← bivalentInsertion_vertexOf_inl d c e]
    exact ⟨RotationSystem.vertexOf_mem_vertices _ _,
      (isBoundaryVertex_bivalentInsertion_vertexOf_inl d c e).2 hvB⟩

/-- The new vertex `{f, f*}` of the insertion satisfies `IsBivalentRemovable`, with `d₁ = f` and
`d₂ = f*`. -/
theorem isBivalentRemovable_bivalentInsertion :
    (G.bivalentInsertion d c).IsBivalentRemovable (Sum.inr 0) where
  not_isBoundaryVertex := not_isBoundaryVertex_bivalentInsertion_vertexOf_inr d c 0
  card_vertexOf := by
    rw [bivalentInsertion_vertexOf_inr]
    exact card_pair (by simp)
  inv_ne_rot := by
    rw [bivalentInsertion_inv_inr_zero, bivalentInsertion_rot_inr_zero]
    exact Sum.inl_ne_inr

/-! #### Faces of the insertion -/

variable {d}

section Faces

variable (hinv : Involutive G.inv) (hfix : G.inv d ≠ d)

include hinv

omit [Fintype H] in
/-- Away from `d` and `d̄`, the face permutation of the insertion is `φ`. -/
theorem bivalentInsertion_facePerm_inl_of_ne {e : H} (h₁ : e ≠ d) (h₂ : e ≠ G.inv d) :
    (G.bivalentInsertion d c).facePerm (Sum.inl e) = Sum.inl (G.facePerm e) := by
  rw [RotationSystem.facePerm_apply, bivalentInsertion_inv_inl_of_ne c hinv h₁ h₂]
  rfl

omit [Fintype H] in
/-- The face permutation of the insertion sends `f` to `φ d̄`. -/
theorem bivalentInsertion_facePerm_inr_zero :
    (G.bivalentInsertion d c).facePerm (Sum.inr 0) = Sum.inl (G.facePerm (G.inv d)) := by
  rw [RotationSystem.facePerm_apply, bivalentInsertion_inv_inr_zero, RotationSystem.facePerm_apply,
    hinv]
  rfl

include hfix

omit [Fintype H] hinv in
/-- The face permutation of the insertion sends `d` to `f*`. -/
theorem bivalentInsertion_facePerm_inl_self :
    (G.bivalentInsertion d c).facePerm (Sum.inl d) = Sum.inr 1 := by
  rw [RotationSystem.facePerm_apply, bivalentInsertion_inv_inl_self c hfix,
    bivalentInsertion_rot_inr_zero]

omit [Fintype H] hfix in
/-- The face permutation of the insertion sends `d̄` to `f`. -/
theorem bivalentInsertion_facePerm_inl_inv :
    (G.bivalentInsertion d c).facePerm (Sum.inl (G.inv d)) = Sum.inr 0 := by
  rw [RotationSystem.facePerm_apply, bivalentInsertion_inv_inl_inv c hinv,
    bivalentInsertion_rot_inr_one]

omit [Fintype H] hinv in
/-- The face permutation of the insertion sends `f*` to `φ d`. -/
theorem bivalentInsertion_facePerm_inr_one :
    (G.bivalentInsertion d c).facePerm (Sum.inr 1) = Sum.inl (G.facePerm d) := by
  rw [RotationSystem.facePerm_apply, bivalentInsertion_inv_inr_one c hfix]
  rfl

omit [Fintype H] in
/-- `φ` is the first-return map of the face permutation of the insertion to `H`. -/
private theorem coe_firstReturn_bivalentInsertion [Finite H] (e : H) :
    (firstReturn (G.bivalentInsertion d c).facePerm (Set.range Sum.inl)
      (Equiv.ofInjective Sum.inl Sum.inl_injective e) : H ⊕ Fin 2) =
        Sum.inl (G.facePerm e) := by
  have hnot : ∀ j : Fin 2, (Sum.inr j : H ⊕ Fin 2) ∉ Set.range Sum.inl := by simp
  have hmem : ∀ a : H, (Sum.inl a : H ⊕ Fin 2) ∈ Set.range Sum.inl := fun a => ⟨a, rfl⟩
  by_cases h₁ : e = d
  · subst h₁
    rw [coe_firstReturn_of_apply_apply_mem ?_ ?_, Equiv.ofInjective_apply,
      bivalentInsertion_facePerm_inl_self c hfix, bivalentInsertion_facePerm_inr_one c hfix]
    · rw [Equiv.ofInjective_apply, bivalentInsertion_facePerm_inl_self c hfix]
      exact hnot 1
    · rw [Equiv.ofInjective_apply, bivalentInsertion_facePerm_inl_self c hfix,
        bivalentInsertion_facePerm_inr_one c hfix]
      exact hmem _
  by_cases h₂ : e = G.inv d
  · subst h₂
    rw [coe_firstReturn_of_apply_apply_mem ?_ ?_, Equiv.ofInjective_apply,
      bivalentInsertion_facePerm_inl_inv c hinv, bivalentInsertion_facePerm_inr_zero c hinv]
    · rw [Equiv.ofInjective_apply, bivalentInsertion_facePerm_inl_inv c hinv]
      exact hnot 0
    · rw [Equiv.ofInjective_apply, bivalentInsertion_facePerm_inl_inv c hinv,
        bivalentInsertion_facePerm_inr_zero c hinv]
      exact hmem _
  have h1 := bivalentInsertion_facePerm_inl_of_ne c hinv h₁ h₂
  rw [coe_firstReturn_of_apply_mem (by rw [Equiv.ofInjective_apply, h1]; exact hmem _)]
  exact h1

omit [Fintype H] in
private theorem bivalentInsertion_semiconj [Finite H] (e : H) :
    Equiv.ofInjective Sum.inl Sum.inl_injective (G.facePerm e) =
      firstReturnPerm (G.bivalentInsertion d c).facePerm (Set.range Sum.inl)
        (Equiv.ofInjective Sum.inl Sum.inl_injective e) :=
  Subtype.ext (coe_firstReturn_bivalentInsertion c hinv hfix e).symm

omit [Fintype H] in
/-- Two darts of `H` lie in one orbit of the face permutation of the insertion iff they lie in
one orbit of `φ`. -/
theorem sameCycle_bivalentInsertion_facePerm_inl_iff [Finite H] {a e : H} :
    (G.bivalentInsertion d c).facePerm.SameCycle (Sum.inl a) (Sum.inl e) ↔
      G.facePerm.SameCycle a e := by
  rw [← sameCycle_iff_of_semiconj _ (bivalentInsertion_semiconj c hinv hfix),
    sameCycle_firstReturnPerm_iff]
  rfl

/-- The insertion has as many orbits of its face permutation as `G`. -/
theorem card_bivalentInsertion_faceOrbits :
    (G.bivalentInsertion d c).faceOrbits.card = G.faceOrbits.card := by
  rw [RotationSystem.card_faceOrbits_eq_numOrbits, RotationSystem.card_faceOrbits_eq_numOrbits,
    numOrbits_eq_of_semiconj _ (bivalentInsertion_semiconj c hinv hfix),
    numOrbits_firstReturnPerm]
  rintro (e | j)
  · exact ⟨Sum.inl e, ⟨e, rfl⟩, SameCycle.refl _ _⟩
  · rcases fin_two_eq j with rfl | rfl
    · exact ⟨Sum.inl (G.inv d), ⟨_, rfl⟩,
        sameCycle_of_eq_apply (bivalentInsertion_facePerm_inl_inv c hinv)⟩
    · exact ⟨Sum.inl d, ⟨_, rfl⟩,
        sameCycle_of_eq_apply (bivalentInsertion_facePerm_inl_self c hfix)⟩

end Faces

/-! #### The insertion is a plabic graph -/

variable (hG : G.IsPlabicGraph) (hd : d ∉ G.bdry)

include hG

/-- Any two darts of the insertion into a plabic graph are connected. -/
theorem bivalentInsertion_reach (y z : H ⊕ Fin 2) : (G.bivalentInsertion d c).Reach y z := by
  have hinv := hG.inv_involutive
  have hfix := hG.inv_ne d
  have hstep : ∀ e, (G.bivalentInsertion d c).Reach (Sum.inl e) (Sum.inl (G.inv e)) := by
    intro e
    by_cases h₁ : e = d
    · subst h₁
      have := (RotationSystem.Reach.refl (R := (G.bivalentInsertion e c).toRotationSystem)
        (Sum.inl e)).inv.rot.inv
      rwa [bivalentInsertion_inv_inl_self c hfix, bivalentInsertion_rot_inr_zero,
        bivalentInsertion_inv_inr_one c hfix] at this
    by_cases h₂ : e = G.inv d
    · subst h₂
      have := (RotationSystem.Reach.refl (R := (G.bivalentInsertion d c).toRotationSystem)
        (Sum.inl (G.inv d))).inv.rot.inv
      rw [bivalentInsertion_inv_inl_inv c hinv, bivalentInsertion_rot_inr_one,
        bivalentInsertion_inv_inr_zero] at this
      rw [hinv d]
      exact this
    have := (RotationSystem.Reach.refl (R := (G.bivalentInsertion d c).toRotationSystem)
      (Sum.inl e)).inv
    rwa [bivalentInsertion_inv_inl_of_ne c hinv h₁ h₂] at this
  have hlift : ∀ a e, G.Reach a e → (G.bivalentInsertion d c).Reach (Sum.inl a) (Sum.inl e) := by
    intro a e h
    induction h with
    | refl => exact RotationSystem.Reach.refl _
    | rot _ ih => exact ih.rot
    | inv _ ih => exact ih.trans (hstep _)
  have hall : ∀ y, (G.bivalentInsertion d c).Reach (Sum.inl d) y := by
    rintro (e | j)
    · exact hlift d e (hG.toIsConnected.reach d e)
    · rcases fin_two_eq j with rfl | rfl
      · have := (RotationSystem.Reach.refl (R := (G.bivalentInsertion d c).toRotationSystem)
          (Sum.inl d)).inv
        rwa [bivalentInsertion_inv_inl_self c hfix] at this
      · have := (RotationSystem.Reach.refl (R := (G.bivalentInsertion d c).toRotationSystem)
          (Sum.inl d)).inv.rot
        rwa [bivalentInsertion_inv_inl_self c hfix, bivalentInsertion_rot_inr_zero] at this
  exact (hall y).symm.trans (hall z)

/-- The insertion into a plabic graph has one edge more than `G`. -/
theorem card_bivalentInsertion_edges :
    (G.bivalentInsertion d c).edges.card = G.edges.card + 1 := by
  have h1 := RotationSystem.two_mul_card_edges (G.bivalentInsertion d c).toRotationSystem
    (bivalentInsertion_inv_involutive c hG.inv_involutive (hG.inv_ne d))
    (bivalentInsertion_inv_ne c hG.inv_involutive hG.inv_ne)
  have h2 := RotationSystem.two_mul_card_edges G.toRotationSystem hG.inv_involutive hG.inv_ne
  rw [Fintype.card_sum, Fintype.card_fin] at h1
  change 2 * (G.bivalentInsertion d c).edges.card = _ at h1
  change 2 * G.edges.card = _ at h2
  omega

include hd

/-- The exterior of the insertion is a face of the insertion. -/
theorem bivalentInsertion_exterior_mem_faceOrbits :
    (G.bivalentInsertion d c).exterior ∈ (G.bivalentInsertion d c).faceOrbits := by
  have hinv := hG.inv_involutive
  have hfix := hG.inv_ne d
  obtain ⟨x, hx⟩ := G.mem_faceOrbits.1 hG.exterior_mem_faceOrbits
  have hnot : ∀ e, G.facePerm.SameCycle x e → e ∈ G.bdry := fun e he =>
    G.exterior_subset_bdry (hx ▸ (RotationSystem.mem_faceOf _).2 he)
  refine (G.bivalentInsertion d c).mem_faceOrbits.2 ⟨Sum.inl x, ?_⟩
  rw [bivalentInsertion_exterior]
  ext z
  rw [RotationSystem.mem_faceOf]
  rcases z with e | j
  · rw [sameCycle_bivalentInsertion_facePerm_inl_iff c hinv hfix, mem_map]
    constructor
    · intro h
      exact ⟨e, hx ▸ (RotationSystem.mem_faceOf _).2 h, rfl⟩
    · rintro ⟨a, ha, hae⟩
      cases hae
      rw [← hx] at ha
      exact (RotationSystem.mem_faceOf _).1 ha
  · simp only [mem_map, Embedding.inl_apply, reduceCtorEq, and_false, exists_false, iff_false]
    intro h
    rcases fin_two_eq j with rfl | rfl
    · exact hd (hG.inv_mem_bdry_iff.1 (hnot _ ((sameCycle_bivalentInsertion_facePerm_inl_iff c
        hinv hfix).1
          (h.trans (sameCycle_of_eq_apply (bivalentInsertion_facePerm_inl_inv c hinv))))))
    · exact hd (hnot _ ((sameCycle_bivalentInsertion_facePerm_inl_iff c hinv hfix).1
        (h.trans (sameCycle_of_eq_apply (bivalentInsertion_facePerm_inl_self c hfix)))))

/-- On `B`, the involution of the insertion is `d ↦ d̄`. -/
theorem bivalentInsertion_inv_inl_of_mem_bdry {e : H} (he : e ∈ G.bdry) :
    (G.bivalentInsertion d c).inv (Sum.inl e) = Sum.inl (G.inv e) :=
  bivalentInsertion_inv_inl_of_ne c hG.inv_involutive (fun h => hd (h ▸ he))
    fun h => hd (hG.inv_mem_bdry_iff.1 (h ▸ he))

/-- The image of the exterior of the insertion under its involution is the image under `d ↦ d̄` of
the exterior of `G`. -/
theorem bivalentInsertion_map_inv_exterior :
    (G.bivalentInsertion d c).exterior.map (G.bivalentInsertion d c).inv.toEmbedding =
      (G.exterior.map G.inv.toEmbedding).map Embedding.inl := by
  rw [bivalentInsertion_exterior]
  ext z
  simp only [mem_map, Equiv.coe_toEmbedding, Embedding.inl_apply]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨G.inv a, ⟨a, ha, rfl⟩,
      (bivalentInsertion_inv_inl_of_mem_bdry c hG hd (G.exterior_subset_bdry ha)).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨Sum.inl a, ⟨a, ha, rfl⟩,
      bivalentInsertion_inv_inl_of_mem_bdry c hG hd (G.exterior_subset_bdry ha)⟩

/-- The insertion of a bivalent vertex into a plabic graph is a disk map. -/
theorem bivalentInsertion_isDiskMap : (G.bivalentInsertion d c).IsDiskMap where
  nonempty := ⟨Sum.inr 0⟩
  inv_involutive := bivalentInsertion_inv_involutive c hG.inv_involutive (hG.inv_ne d)
  inv_ne := bivalentInsertion_inv_ne c hG.inv_involutive hG.inv_ne
  transitive y z := RotationSystem.reach_iff_exists_mem_closure _ |>.1
    (bivalentInsertion_reach c hG y z)
  inv_mem_bdry y hy := by
    rcases y with e | j
    · rw [inl_mem_bivalentInsertion_bdry] at hy
      rw [bivalentInsertion_inv_inl_of_mem_bdry c hG hd hy, inl_mem_bivalentInsertion_bdry]
      exact hG.inv_mem_bdry _ hy
    · exact absurd hy (inr_notMem_bivalentInsertion_bdry d c j)
  euler := by
    have hV := card_bivalentInsertion_vertices d c (G := G)
    have hE := card_bivalentInsertion_edges (d := d) c hG
    have hF := card_bivalentInsertion_faceOrbits c hG.inv_involutive (hG.inv_ne d)
    have := hG.euler
    change ((G.bivalentInsertion d c).vertices.card : ℤ) - (G.bivalentInsertion d c).edges.card +
      (G.bivalentInsertion d c).faceOrbits.card = 2
    rw [hV, hE, hF]
    push_cast
    linarith
  boundaryVertex_card w hw := by
    obtain ⟨hwV, hwB⟩ := (DiskMap.mem_boundaryVertices _).1 hw
    obtain ⟨y, rfl⟩ := RotationSystem.mem_vertices _ |>.1 hwV
    rcases y with e | j
    · have hb : G.vertexOf e ∈ G.boundaryVertices := G.vertexOf_mem_boundaryVertices.2
        ((isBoundaryVertex_bivalentInsertion_vertexOf_inl d c e).1 hwB)
      obtain ⟨h3, h2⟩ := hG.boundaryVertex_card _ hb
      rw [bivalentInsertion_vertexOf_inl, card_map, filter_map, card_map]
      refine ⟨h3, Eq.trans ?_ h2⟩
      congr 1
      exact filter_congr fun z _ => inl_mem_bivalentInsertion_bdry d c
    · exact absurd hwB (not_isBoundaryVertex_bivalentInsertion_vertexOf_inr d c j)
  exists_orbit := by
    refine ⟨(G.bivalentInsertion d c).exterior,
      bivalentInsertion_exterior_mem_faceOrbits c hG hd, fun y hy => ?_, ?_, ?_⟩
    · exact DiskMap.exterior_subset_bdry _ hy
    · rw [bivalentInsertion_map_inv_exterior c hG hd, bivalentInsertion_exterior, ← map_union,
        hG.exterior_union_map_inv]
      rfl
    · rw [bivalentInsertion_map_inv_exterior c hG hd, bivalentInsertion_exterior, disjoint_map]
      exact hG.disjoint_exterior_map_inv

/-- **An insertion of a bivalent vertex is a plabic graph.** -/
@[cluster_algebras "lem_bivalent_insertion_plabic"]
theorem isPlabicGraph_bivalentInsertion : (G.bivalentInsertion d c).IsPlabicGraph where
  toIsDiskMap := bivalentInsertion_isDiskMap c hG hd
  one_le := hG.one_le
  colour_rot y hy := by
    rcases y with e | j
    · rw [isBoundaryVertex_bivalentInsertion_vertexOf_inl] at hy
      exact hG.colour_rot e hy
    · rcases fin_two_eq j with rfl | rfl
      · rw [bivalentInsertion_rot_inr_zero]
        rfl
      · rw [bivalentInsertion_rot_inr_one]
        rfl
  leg_notMem_bdry i := by
    rw [bivalentInsertion_leg, inl_mem_bivalentInsertion_bdry]
    exact hG.leg_notMem_bdry i
  bvertex_mem i := by
    refine (G.bivalentInsertion d c).vertexOf_mem_boundaryVertices.2 ?_
    rw [bivalentInsertion_leg, isBoundaryVertex_bivalentInsertion_vertexOf_inl]
    exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  bvertex_injective i j hij := by
    apply hG.bvertex_injective
    apply Finset.map_injective (Embedding.inl (α := H) (β := Fin 2))
    simpa only [bvertex, bivalentInsertion_leg, bivalentInsertion_vertexOf_inl] using hij
  exists_bvertex_eq w hw := by
    rw [bivalentInsertion_boundaryVertices, mem_image] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    obtain ⟨i, rfl⟩ := hG.exists_bvertex_eq v hv
    exact ⟨i, by simp only [bvertex, bivalentInsertion_leg, bivalentInsertion_vertexOf_inl]⟩
  exists_exterior i := by
    obtain ⟨e, he, he1, he2⟩ := hG.exists_exterior i
    refine ⟨Sum.inl e, ?_, ?_, ?_⟩
    · rw [bivalentInsertion_exterior]
      exact mem_map_of_mem _ he
    · simp only [bvertex, bivalentInsertion_leg, bivalentInsertion_vertexOf_inl]
      exact mem_map_of_mem _ he1
    · simp only [bvertex, bivalentInsertion_leg, bivalentInsertion_vertexOf_inl]
      rw [bivalentInsertion_inv_inl_of_mem_bdry c hG hd (G.exterior_subset_bdry he)]
      exact mem_map_of_mem _ he2

/-! #### Removing the inserted vertex -/

omit [Fintype H] hG hd in
/-- Every dart of `H` lies outside the new vertex `{f, f*}` of the insertion. -/
theorem inl_mem_compl_bivalentInsertion (e : H) :
    (Sum.inl e : H ⊕ Fin 2) ∈
      ({Sum.inr 0, (G.bivalentInsertion d c).rot (Sum.inr 0)}ᶜ : Set (H ⊕ Fin 2)) := by
  simp

/-- **Removing an inserted vertex**: the removal of the vertex `{f, f*}` of the insertion, with
`d₁ = f` and `d₂ = f*`, is `G`. Precisely, the identification `e ↦ Sum.inl e` of the darts of `G`
with those of the removal is an isomorphism of plabic graphs: it intertwines the involutions and
the rotations and preserves `B`, the colours and the legs. -/
@[cluster_algebras "lem_bivalent_insertion_removal"]
noncomputable def bivalentInsertionRemovalIso :
    G.Iso ((G.bivalentInsertion d c).bivalentRemoval (isPlabicGraph_bivalentInsertion c hG hd)
      (isBivalentRemovable_bivalentInsertion d c)) where
  toEquiv := Equiv.ofBijective (fun e => ⟨Sum.inl e, inl_mem_compl_bivalentInsertion c e⟩)
    ⟨fun _ _ h => Sum.inl_injective (congrArg Subtype.val h), by
      rintro ⟨y | j, hy⟩
      · exact ⟨y, rfl⟩
      · rcases fin_two_eq j with rfl | rfl <;> simp at hy⟩
  map_inv e := by
    have hinv := hG.inv_involutive
    have hfix := hG.inv_ne d
    apply Subtype.ext
    change Sum.inl (G.inv e) = _
    by_cases h₁ : e = d
    · rw [coe_bivalentRemoval_inv_of_eq_inv _ _ (by simp [h₁]), bivalentInsertion_rot_inr_zero,
        bivalentInsertion_inv_inr_one c hfix, h₁]
    by_cases h₂ : e = G.inv d
    · rw [coe_bivalentRemoval_inv_of_eq_inv_rot _ _
        (by simp [h₂, bivalentInsertion_inv_inr_one c hfix]), bivalentInsertion_inv_inr_zero, h₂,
        hinv]
    rw [coe_bivalentRemoval_inv_of_ne _ _ (by simp [h₁])
      (by simp [h₂, bivalentInsertion_inv_inr_one c hfix])]
    exact (bivalentInsertion_inv_inl_of_ne c hinv h₁ h₂).symm
  map_rot _ := Subtype.ext rfl
  mem_bdry_iff e := by
    rw [mem_bivalentRemoval_bdry]
    exact inl_mem_bivalentInsertion_bdry d c
  map_colour _ _ := rfl
  map_bvertex i := by
    rw [hG.filter_bvertex_notMem_bdry,
      (isPlabicGraph_bivalentRemoval _ _).filter_bvertex_notMem_bdry, map_singleton]
    rfl

/-- The isomorphism `bivalentInsertionRemovalIso` is the identification `e ↦ Sum.inl e`. -/
@[simp]
theorem coe_bivalentInsertionRemovalIso_apply (e : H) :
    ((bivalentInsertionRemovalIso c hG hd).toEquiv e : H ⊕ Fin 2) = Sum.inl e :=
  rfl

/-- **Removing an inserted vertex**: the removal of the vertex `{f, f*}` of the insertion, with
`d₁ = f` and `d₂ = f*`, is isomorphic to `G`. -/
@[cluster_algebras "lem_bivalent_insertion_removal"]
theorem bivalentRemoval_bivalentInsertion_isomorphic :
    ((G.bivalentInsertion d c).bivalentRemoval (isPlabicGraph_bivalentInsertion c hG hd)
      (isBivalentRemovable_bivalentInsertion d c)).Isomorphic G :=
  ⟨(bivalentInsertionRemovalIso c hG hd).symm⟩

end Insertion

end PlabicData

end ClusterAlgebras

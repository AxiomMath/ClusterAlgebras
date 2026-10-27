/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap

/-!
# The cycle space of a rotation system

Let `R = (H, d ↦ d̄, σ)` be a connected rotation system, with vertices `V`, edges `E` and orbits
`Φ` of the face permutation `φ = σ ∘ (d ↦ d̄)`. Its rational cycle space `Z(R)` consists of the
functions `c : H → ℚ` with `c(d̄) = -c(d)` and `∑_{d ∈ v} c(d) = 0` at every vertex `v`. This file
computes `dim Z(R) = |E| - |V| + 1`, shows that the differences `d ↦ h(f(d̄)) - h(f(d))` of a
function `h` on `Φ` are cycles, and deduces the Euler bound `|V| - |E| + |Φ| ≤ 2`. When equality
holds, as it does for a disk map, the *coboundary* `h ↦ (d ↦ h(f(d̄)) - h(f(d)))` maps onto
`Z(R)`. In particular every integer cycle of a disk map is the coboundary of a unique integer
function on the faces vanishing on the exterior.

## Main definitions

* `ClusterAlgebras.RotationSystem.antisymmetricFunctions`: the space `W` of functions with
  `c(d̄) = -c(d)`.
* `ClusterAlgebras.RotationSystem.vertexBoundary`: the map `∂c(v) = ∑_{d ∈ v} c(d)`.
* `ClusterAlgebras.RotationSystem.coboundary`: the map `δh(d) = h(f(d̄)) - h(f(d))` from `ℚ^Φ`
  to `ℚ^H`.

## Main results

* `ClusterAlgebras.RotationSystem.IsConnected.finrank_cycleSpace`: `dim Z(R) = |E| - |V| + 1`.
* `ClusterAlgebras.RotationSystem.sub_faceOf_mem_cycleSpace`: differences of face values are
  cycles.
* `ClusterAlgebras.RotationSystem.IsConnected.euler_le`: `|V| - |E| + |Φ| ≤ 2`.
* `ClusterAlgebras.RotationSystem.IsConnected.faceOf_eq_faceOf_iff_of_surjective`: recognising
  the faces from an invariant labelling.
* `ClusterAlgebras.RotationSystem.IsConnected.range_coboundary_eq`: under Euler's relation the
  coboundary maps onto the cycle space.
* `ClusterAlgebras.DiskMap.IsDiskMap.existsUnique_faceFunction`: integer cycles of a disk map
  bound.

## Implementation notes

* A function on `Φ` is a function on the subtype `R.faceOrbits` of `Finset H`; the orbit of `d`
  as an element of it is `R.toFaceOrbit d`, and likewise `R.toVertex d` for the vertex. The
  lemma on differences of face values is stated for any function `Finset H → ℚ`, which covers the
  functions on `Φ`, and needs only that `d ↦ d̄` be an involution.
* Dimensions are `Module.finrank ℚ`, and the identities between them are stated in `ℤ`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Module

namespace RotationSystem

section Antisymmetric

variable {H : Type*} (R : RotationSystem H)

/-- The space `W` of **antisymmetric** functions: the `c : H → ℚ` with `c(d̄) = -c(d)`. -/
def antisymmetricFunctions : Submodule ℚ (H → ℚ) where
  carrier := {c | ∀ d, c (R.inv d) = -c d}
  add_mem' := by
    intro c c' hc hc' d
    simp only [Set.mem_setOf_eq, Pi.add_apply] at hc hc' ⊢
    rw [hc, hc']
    ring
  zero_mem' := by simp
  smul_mem' := by
    intro a c hc d
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hc ⊢
    rw [hc]
    ring

/-- A function lies in `W` exactly when `c(d̄) = -c(d)` for every dart `d`. -/
theorem mem_antisymmetricFunctions {c : H → ℚ} :
    c ∈ R.antisymmetricFunctions ↔ ∀ d, c (R.inv d) = -c d :=
  Iff.rfl

/-- An antisymmetric function sums to zero. -/
theorem sum_eq_zero_of_mem_antisymmetricFunctions [Fintype H] {c : H → ℚ}
    (hc : c ∈ R.antisymmetricFunctions) : ∑ d, c d = 0 := by
  have h := Equiv.sum_comp R.inv c
  simp only [(R.mem_antisymmetricFunctions).1 hc, sum_neg_distrib] at h
  linarith

end Antisymmetric

variable {H : Type*} [Fintype H] [DecidableEq H] (R : RotationSystem H)

/-! ### Vertices and orbits as elements of `V` and `Φ` -/

/-- The vertex `v(d)` of a dart, as an element of the set `V` of vertices. -/
def toVertex (d : H) : R.vertices := ⟨R.vertexOf d, R.vertexOf_mem_vertices d⟩

/-- The orbit `f(d)` of a dart under `φ`, as an element of the set `Φ` of orbits. -/
def toFaceOrbit (d : H) : R.faceOrbits := ⟨R.faceOf d, R.faceOf_mem_faceOrbits d⟩

/-- The vertex `R.toVertex d` is the set of darts `R.vertexOf d`. -/
@[simp]
theorem coe_toVertex (d : H) : (R.toVertex d : Finset H) = R.vertexOf d := rfl

/-- The orbit `R.toFaceOrbit d` is the set of darts `R.faceOf d`. -/
@[simp]
theorem coe_toFaceOrbit (d : H) : (R.toFaceOrbit d : Finset H) = R.faceOf d := rfl

/-- A dart and its rotation `σ(d)` have the same vertex. -/
@[simp]
theorem toVertex_rot (d : H) : R.toVertex (R.rot d) = R.toVertex d :=
  Subtype.ext (R.vertexOf_rot d)

/-- A dart and its image `φ(d)` lie in the same orbit of `φ`. -/
@[simp]
theorem toFaceOrbit_facePerm (d : H) : R.toFaceOrbit (R.facePerm d) = R.toFaceOrbit d :=
  Subtype.ext (R.faceOf_facePerm d)

/-- Every vertex is the vertex of some dart. -/
theorem toVertex_surjective : Function.Surjective R.toVertex := by
  rintro ⟨v, hv⟩
  obtain ⟨d, rfl⟩ := R.mem_vertices.1 hv
  exact ⟨d, rfl⟩

/-- Every orbit of `φ` is the orbit of some dart. -/
theorem toFaceOrbit_surjective : Function.Surjective R.toFaceOrbit := by
  rintro ⟨f, hf⟩
  obtain ⟨d, rfl⟩ := R.mem_faceOrbits.1 hf
  exact ⟨d, rfl⟩

/-- A dart lies in a vertex exactly when that vertex is its own. -/
theorem mem_vertex_iff (v : R.vertices) (d : H) : d ∈ (v : Finset H) ↔ v = R.toVertex d := by
  obtain ⟨e, rfl⟩ := R.toVertex_surjective v
  rw [coe_toVertex, mem_vertexOf, ← R.vertexOf_eq_vertexOf_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- The vertices partition the darts. -/
theorem sum_vertices_sum {M : Type*} [AddCommMonoid M] (c : H → M) :
    ∑ v ∈ R.vertices, ∑ d ∈ v, c d = ∑ d, c d := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := R.vertices) (g := R.vertexOf)
    (fun d _ => R.vertexOf_mem_vertices d)]
  refine sum_congr rfl fun v hv => ?_
  obtain ⟨e, rfl⟩ := R.mem_vertices.1 hv
  congr 1
  ext d
  simp only [mem_filter, mem_univ, true_and, mem_vertexOf, vertexOf_eq_vertexOf_iff]
  exact Equiv.Perm.sameCycle_comm

/-- The rotation permutes the darts of each vertex. -/
theorem sum_vertex_rot {M : Type*} [AddCommMonoid M] (g : H → M) {v : Finset H}
    (hv : v ∈ R.vertices) : ∑ d ∈ v, g (R.rot d) = ∑ d ∈ v, g d := by
  obtain ⟨e, rfl⟩ := R.mem_vertices.1 hv
  refine sum_nbij' R.rot R.rot.symm (fun a ha => ?_) (fun a ha => ?_) (fun a _ => by simp)
    (fun a _ => by simp) (fun a _ => rfl)
  · rw [mem_vertexOf] at ha ⊢
    exact Equiv.Perm.sameCycle_apply_right.2 ha
  · rw [mem_vertexOf] at ha ⊢
    exact Equiv.Perm.sameCycle_symm_apply_right.2 ha

/-! ### Antisymmetric functions and the vertex boundary -/

/-- Every cycle is an antisymmetric function: `Z(R) ⊆ W`. -/
theorem cycleSpace_le_antisymmetricFunctions : R.cycleSpace ≤ R.antisymmetricFunctions :=
  fun _ hc => hc.1

/-- The **vertex boundary** `∂ : ℚ^H → ℚ^V`, `∂c(v) = ∑_{d ∈ v} c(d)`. -/
def vertexBoundary : (H → ℚ) →ₗ[ℚ] (R.vertices → ℚ) where
  toFun c v := ∑ d ∈ (v : Finset H), c d
  map_add' c c' := by ext v; simp [sum_add_distrib]
  map_smul' a c := by ext v; simp [mul_sum]

/-- The value of `∂c` at a vertex `v` is `∑_{d ∈ v} c(d)`. -/
@[simp]
theorem vertexBoundary_apply (c : H → ℚ) (v : R.vertices) :
    R.vertexBoundary c v = ∑ d ∈ (v : Finset H), c d :=
  rfl

/-- The cycle space is the kernel of the vertex boundary on antisymmetric functions. -/
theorem cycleSpace_eq_inf_ker :
    R.cycleSpace = R.antisymmetricFunctions ⊓ LinearMap.ker R.vertexBoundary := by
  ext c
  simp only [Submodule.mem_inf, LinearMap.mem_ker, mem_cycleSpace, mem_antisymmetricFunctions]
  refine ⟨fun ⟨h1, h2⟩ => ⟨h1, funext fun v => h2 v v.2⟩,
    fun ⟨h1, h2⟩ => ⟨h1, fun v hv => congr_fun h2 ⟨v, hv⟩⟩⟩

/-! ### The dimension of the space of antisymmetric functions -/

/-- The edge `{d, d̄}` of a dart, as an element of the set `E` of edges. -/
private def toEdge (d : H) : R.edges := ⟨R.edgeOf d, R.mem_edges.2 ⟨d, rfl⟩⟩

/-- A chosen dart of each edge. -/
private noncomputable def edgeRep (e : R.edges) : H := (R.mem_edges.1 e.2).choose

private theorem edgeOf_edgeRep (e : R.edges) : R.edgeOf (R.edgeRep e) = e :=
  (R.mem_edges.1 e.2).choose_spec

private theorem toEdge_edgeRep (e : R.edges) : R.toEdge (R.edgeRep e) = e :=
  Subtype.ext (R.edgeOf_edgeRep e)

private theorem toEdge_inv (hinv : Function.Involutive R.inv) (d : H) :
    R.toEdge (R.inv d) = R.toEdge d := by
  apply Subtype.ext
  simp only [toEdge, edgeOf, hinv d]
  exact pair_comm _ _

private theorem edgeRep_toEdge (d : H) :
    R.edgeRep (R.toEdge d) = d ∨ R.edgeRep (R.toEdge d) = R.inv d := by
  have h : R.edgeRep (R.toEdge d) ∈ R.edgeOf (R.edgeRep (R.toEdge d)) := by simp
  rw [R.edgeOf_edgeRep] at h
  exact (R.mem_edgeOf).1 h

/-- Restriction of an antisymmetric function to the chosen darts of the edges. -/
private noncomputable def restrictEdges : R.antisymmetricFunctions →ₗ[ℚ] (R.edges → ℚ) where
  toFun c e := (c : H → ℚ) (R.edgeRep e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem restrictEdges_injective : Function.Injective R.restrictEdges := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  apply Subtype.ext
  funext d
  have h := congr_fun hc (R.toEdge d)
  change (c : H → ℚ) (R.edgeRep (R.toEdge d)) = 0 at h
  rcases R.edgeRep_toEdge d with h' | h' <;> rw [h'] at h
  · exact h
  · simp only [Submodule.coe_zero, Pi.zero_apply]
    linarith [c.2 d]

private theorem restrictEdges_surjective (hinv : Function.Involutive R.inv)
    (hne : ∀ d, R.inv d ≠ d) : Function.Surjective R.restrictEdges := by
  intro x
  refine ⟨⟨fun d => if R.edgeRep (R.toEdge d) = d then x (R.toEdge d)
    else -x (R.toEdge d), fun d => ?_⟩, ?_⟩
  · simp only [R.toEdge_inv hinv]
    rcases R.edgeRep_toEdge d with h | h
    · rw [if_pos h, if_neg (by rw [h]; exact (hne d).symm)]
    · rw [if_pos h, if_neg (by rw [h]; exact hne d), neg_neg]
  · funext e
    change (if R.edgeRep (R.toEdge (R.edgeRep e)) = R.edgeRep e then
      x (R.toEdge (R.edgeRep e)) else -x (R.toEdge (R.edgeRep e))) = x e
    rw [R.toEdge_edgeRep, if_pos rfl]

/-- The space `W` of antisymmetric functions has dimension `|E|`, the involution being
fixed-point-free. -/
theorem finrank_antisymmetricFunctions (hinv : Function.Involutive R.inv)
    (hne : ∀ d, R.inv d ≠ d) : finrank ℚ R.antisymmetricFunctions = R.edges.card := by
  rw [(LinearEquiv.ofBijective _ ⟨R.restrictEdges_injective,
    R.restrictEdges_surjective hinv hne⟩).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe]

/-! ### The image of the vertex boundary -/

/-- The sum of the values of a function on the vertices. -/
private def sumVertices : (R.vertices → ℚ) →ₗ[ℚ] ℚ where
  toFun x := ∑ v, x v
  map_add' x y := by simp [sum_add_distrib]
  map_smul' a x := by simp [mul_sum]

omit [Fintype H] in
/-- For a dart `e`, the function `𝟙_e - 𝟙_{ē}` is antisymmetric. -/
private theorem single_sub_single_mem (hinv : Function.Involutive R.inv) (hne : ∀ d, R.inv d ≠ d)
    (e : H) :
    (Pi.single e 1 - Pi.single (R.inv e) 1 : H → ℚ) ∈ R.antisymmetricFunctions := by
  intro x
  have hinj := hinv.injective
  by_cases h1 : x = e
  · subst h1
    simp [hne x, (hne x).symm]
  by_cases h2 : x = R.inv e
  · subst h2
    simp [hinv e, hne e, (hne e).symm]
  have h3 : R.inv x ≠ e := fun h => h2 (by rw [← h, hinv x])
  simp [h1, h2, h3, hinj.eq_iff]

private theorem vertexBoundary_single_sub_single (e : H) :
    R.vertexBoundary (Pi.single e 1 - Pi.single (R.inv e) 1 : H → ℚ) =
      Pi.single (R.toVertex e) 1 - Pi.single (R.toVertex (R.inv e)) 1 := by
  ext v
  simp only [vertexBoundary_apply, Pi.sub_apply, sum_sub_distrib]
  rw [sum_pi_single', sum_pi_single']
  simp only [mem_vertex_iff, Pi.single_apply]

/-- The vertex boundary maps the antisymmetric functions onto the functions on `V` summing to
zero. -/
private theorem map_vertexBoundary (hR : R.IsConnected) :
    R.antisymmetricFunctions.map R.vertexBoundary = LinearMap.ker R.sumVertices := by
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    rw [LinearMap.mem_ker]
    change ∑ v : R.vertices, ∑ d ∈ (v : Finset H), c d = 0
    rw [sum_coe_sort R.vertices (fun v => ∑ d ∈ v, c d), R.sum_vertices_sum,
      R.sum_eq_zero_of_mem_antisymmetricFunctions hc]
  · obtain ⟨d₀⟩ := hR.nonempty
    have key : ∀ e, (Pi.single (R.toVertex e) 1 - Pi.single (R.toVertex d₀) 1 :
        R.vertices → ℚ) ∈ R.antisymmetricFunctions.map R.vertexBoundary := by
      intro e
      induction hR.reach d₀ e with
      | refl => simp
      | rot _ ih => rwa [toVertex_rot]
      | @inv y _ ih =>
        have hy : (Pi.single (R.toVertex y) 1 - Pi.single (R.toVertex (R.inv y)) 1 :
            R.vertices → ℚ) ∈ R.antisymmetricFunctions.map R.vertexBoundary := by
          rw [← R.vertexBoundary_single_sub_single]
          exact Submodule.mem_map_of_mem
            (R.single_sub_single_mem hR.inv_involutive hR.inv_ne y)
        have := Submodule.sub_mem _ ih hy
        rwa [sub_sub_sub_cancel_left] at this
    intro x hx
    rw [LinearMap.mem_ker] at hx
    change ∑ v, x v = 0 at hx
    have hsum : x = ∑ v, x v • (Pi.single v 1 - Pi.single (R.toVertex d₀) 1 :
        R.vertices → ℚ) := by
      funext w
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, sum_sub_distrib, ← sum_mul,
        hx, zero_mul, sub_zero]
      rw [Finset.sum_eq_single w (fun b _ hb => by simp [hb.symm])
        (fun h => absurd (mem_univ w) h)]
      simp
    rw [hsum]
    refine Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ ?_
    obtain ⟨e, rfl⟩ := R.toVertex_surjective v
    exact key e

/-! ### The dimension of the cycle space -/

variable {R}

/-- **Dimension of the cycle space**: for a connected rotation system,
`dim_ℚ Z(R) = |E| - |V| + 1`. -/
@[cluster_algebras "lem_rotation_system_cycle_space_dim"]
theorem IsConnected.finrank_cycleSpace (hR : R.IsConnected) :
    (finrank ℚ R.cycleSpace : ℤ) = R.edges.card - R.vertices.card + 1 := by
  set g := R.vertexBoundary ∘ₗ R.antisymmetricFunctions.subtype
  have hker : finrank ℚ (LinearMap.ker g) = finrank ℚ R.cycleSpace := by
    have hk : LinearMap.ker g = R.cycleSpace.comap R.antisymmetricFunctions.subtype := by
      ext x
      simp only [g, LinearMap.ker_comp, Submodule.mem_comap, R.cycleSpace_eq_inf_ker,
        Submodule.mem_inf, Submodule.coe_subtype, SetLike.coe_mem, true_and]
    rw [hk]
    exact (Submodule.comapSubtypeEquivOfLe R.cycleSpace_le_antisymmetricFunctions).finrank_eq
  have hrange : LinearMap.range g = LinearMap.ker R.sumVertices := by
    rw [LinearMap.range_comp, Submodule.range_subtype, R.map_vertexBoundary hR]
  have hS : finrank ℚ (LinearMap.ker R.sumVertices) + 1 = R.vertices.card := by
    have h := LinearMap.finrank_range_add_finrank_ker R.sumVertices
    have hsurj : LinearMap.range R.sumVertices = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro q
      obtain ⟨d⟩ := hR.nonempty
      refine ⟨Pi.single (R.toVertex d) q, ?_⟩
      change ∑ v, Pi.single (R.toVertex d) q v = q
      simp
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe] at h
    omega
  have h := LinearMap.finrank_range_add_finrank_ker g
  rw [hker, hrange, R.finrank_antisymmetricFunctions hR.inv_involutive hR.inv_ne] at h
  omega

/-! ### Differences of face values -/

variable (R) in
/-- **Differences of face values are cycles**: if `d ↦ d̄` is an involution, then for every
function `h` on sets of darts, `d ↦ h(f(d̄)) - h(f(d))` lies in the cycle space. -/
@[cluster_algebras "lem_rotation_system_coboundary_cycle"]
theorem sub_faceOf_mem_cycleSpace (hinv : Function.Involutive R.inv) (h : Finset H → ℚ) :
    (fun d => h (R.faceOf (R.inv d)) - h (R.faceOf d)) ∈ R.cycleSpace := by
  have hf : ∀ d, R.faceOf (R.inv d) = R.faceOf (R.rot d) := fun d => by
    rw [← R.faceOf_facePerm (R.inv d), facePerm_apply, hinv d]
  refine ⟨fun d => by simp only [hinv d]; ring, fun v hv => ?_⟩
  simp only [hf, sum_sub_distrib]
  rw [R.sum_vertex_rot (fun d => h (R.faceOf d)) hv, sub_self]

variable (R) in
/-- The **coboundary** `δ : ℚ^Φ → ℚ^H`, `δh(d) = h(f(d̄)) - h(f(d))`. -/
def coboundary : (R.faceOrbits → ℚ) →ₗ[ℚ] (H → ℚ) where
  toFun h d := h (R.toFaceOrbit (R.inv d)) - h (R.toFaceOrbit d)
  map_add' h h' := by ext d; simp only [Pi.add_apply]; ring
  map_smul' a h := by ext d; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The value of `δh` at a dart `d` is `h(f(d̄)) - h(f(d))`. -/
@[simp]
theorem coboundary_apply (h : R.faceOrbits → ℚ) (d : H) :
    R.coboundary h d = h (R.toFaceOrbit (R.inv d)) - h (R.toFaceOrbit d) :=
  rfl

/-- The coboundary takes values in the cycle space. -/
theorem range_coboundary_le_cycleSpace (hinv : Function.Involutive R.inv) :
    LinearMap.range R.coboundary ≤ R.cycleSpace := by
  rintro _ ⟨h, rfl⟩
  convert R.sub_faceOf_mem_cycleSpace hinv
    (fun f => if hf : f ∈ R.faceOrbits then h ⟨f, hf⟩ else 0) using 1
  funext d
  simp [toFaceOrbit, R.faceOf_mem_faceOrbits]

/-- In a connected rotation system, a function on `Φ` taking the same value on both sides of
every dart is constant. -/
theorem IsConnected.eq_of_forall_inv {α : Type*} (hR : R.IsConnected) {h : R.faceOrbits → α}
    (hh : ∀ d, h (R.toFaceOrbit (R.inv d)) = h (R.toFaceOrbit d)) (f f' : R.faceOrbits) :
    h f = h f' := by
  have key : ∀ d : H, ∀ g, Relation.ReflTransGen R.FaceAdj (R.faceOf d) g →
      ∀ hg : g ∈ R.faceOrbits, h ⟨g, hg⟩ = h (R.toFaceOrbit d) := by
    intro d g hrel
    induction hrel with
    | refl => intro _; rfl
    | tail _ hstep ih =>
      obtain ⟨x, rfl, rfl⟩ := hstep
      intro _
      exact (hh x).trans (ih (R.faceOf_mem_faceOrbits x))
  obtain ⟨d, rfl⟩ := R.toFaceOrbit_surjective f
  obtain ⟨e, rfl⟩ := R.toFaceOrbit_surjective f'
  exact (key d _ (hR.reflTransGen_faceAdj d e) _).symm

/-- In a connected rotation system the kernel of the coboundary is the line of constants. -/
theorem IsConnected.ker_coboundary (hR : R.IsConnected) :
    LinearMap.ker R.coboundary = ℚ ∙ (1 : R.faceOrbits → ℚ) := by
  apply le_antisymm
  · intro h hh
    rw [LinearMap.mem_ker] at hh
    have hc : ∀ d, h (R.toFaceOrbit (R.inv d)) = h (R.toFaceOrbit d) := fun d =>
      sub_eq_zero.1 (congr_fun hh d)
    obtain ⟨d⟩ := hR.nonempty
    refine Submodule.mem_span_singleton.2 ⟨h (R.toFaceOrbit d), funext fun f => ?_⟩
    simp [hR.eq_of_forall_inv hc f (R.toFaceOrbit d)]
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    funext d
    simp

/-- In a connected rotation system the image of the coboundary has dimension `|Φ| - 1`. -/
theorem IsConnected.finrank_range_coboundary (hR : R.IsConnected) :
    finrank ℚ (LinearMap.range R.coboundary) + 1 = R.faceOrbits.card := by
  obtain ⟨d⟩ := hR.nonempty
  have : Nonempty R.faceOrbits := ⟨R.toFaceOrbit d⟩
  have h := LinearMap.finrank_range_add_finrank_ker R.coboundary
  rwa [hR.ker_coboundary, finrank_span_singleton one_ne_zero,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h

/-! ### The Euler bound -/

/-- **Euler bound for a connected rotation system**: `|V| - |E| + |Φ| ≤ 2`. -/
@[cluster_algebras "lem_rotation_system_euler_bound"]
theorem IsConnected.euler_le (hR : R.IsConnected) :
    (R.vertices.card : ℤ) - R.edges.card + R.faceOrbits.card ≤ 2 := by
  have h1 := hR.finrank_range_coboundary
  have h2 := Submodule.finrank_mono (R.range_coboundary_le_cycleSpace hR.inv_involutive)
  have h3 := hR.finrank_cycleSpace
  omega

/-- When Euler's relation `|V| - |E| + |Φ| = 2` holds, the coboundary maps onto the cycle
space. -/
theorem IsConnected.range_coboundary_eq (hR : R.IsConnected)
    (heuler : (R.vertices.card : ℤ) - R.edges.card + R.faceOrbits.card = 2) :
    LinearMap.range R.coboundary = R.cycleSpace := by
  apply Submodule.eq_of_le_of_finrank_le (R.range_coboundary_le_cycleSpace hR.inv_involutive)
  have h1 := hR.finrank_range_coboundary
  have h3 := hR.finrank_cycleSpace
  omega

/-! ### Recognising the faces -/

/-- **Recognising the faces from an invariant labelling**: if `λ : H → L` is a surjection onto a
finite set, constant along `φ`, with `|V| - |E| + |L| = 2`, then two darts lie in the same orbit
of `φ` exactly when they have the same label. -/
@[cluster_algebras "lem_face_labelling_criterion"]
theorem IsConnected.faceOf_eq_faceOf_iff_of_surjective {L : Type*} [Fintype L]
    (hR : R.IsConnected) {lab : H → L} (hsurj : Function.Surjective lab)
    (hlab : ∀ d, lab (R.facePerm d) = lab d)
    (heuler : (R.vertices.card : ℤ) - R.edges.card + Fintype.card L = 2) (d d' : H) :
    R.faceOf d = R.faceOf d' ↔ lab d = lab d' := by
  have easy : ∀ e e', R.faceOf e = R.faceOf e' → lab e = lab e' := by
    intro e e' h
    obtain ⟨n, rfl⟩ := ((R.faceOf_eq_faceOf_iff).1 h).exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hlab, ih]
  refine ⟨easy d d', fun h => ?_⟩
  let F : R.faceOrbits → L := fun f => lab (R.toFaceOrbit_surjective f).choose
  have hF : ∀ e, F (R.toFaceOrbit e) = lab e := fun e =>
    easy _ _ (congrArg Subtype.val (R.toFaceOrbit_surjective (R.toFaceOrbit e)).choose_spec)
  have hFs : Function.Surjective F := fun l => by
    obtain ⟨e, rfl⟩ := hsurj l
    exact ⟨_, hF e⟩
  have hcard : Fintype.card R.faceOrbits ≤ Fintype.card L := by
    rw [Fintype.card_coe]
    have := hR.euler_le
    omega
  exact congrArg Subtype.val (((Fintype.bijective_iff_surjective_and_card F).2
    ⟨hFs, le_antisymm hcard (Fintype.card_le_of_surjective F hFs)⟩).1
    (show F (R.toFaceOrbit d) = F (R.toFaceOrbit d') by rw [hF, hF, h]))

end RotationSystem

/-! ### Integer cycles of a disk map -/

namespace DiskMap

variable {H : Type*} [Fintype H] [DecidableEq H] {M : DiskMap H}

/-- A rational face function of a disk map that vanishes on the exterior face and whose
differences across every dart are integers takes integer values. -/
theorem IsDiskMap.exists_int_eq_of_sub_eq (hM : M.IsDiskMap) {h : M.faceOrbits → ℚ}
    {c : H → ℤ} (h0 : h ⟨M.exterior, hM.exterior_mem_faceOrbits⟩ = 0)
    (hc : ∀ d, h (M.toFaceOrbit (M.inv d)) - h (M.toFaceOrbit d) = c d) (f : M.faceOrbits) :
    ∃ n : ℤ, h f = n := by
  obtain ⟨d₀, hd₀⟩ := M.mem_faceOrbits.1 hM.exterior_mem_faceOrbits
  have key : ∀ g, Relation.ReflTransGen M.FaceAdj (M.faceOf d₀) g →
      ∀ hg : g ∈ M.faceOrbits, ∃ n : ℤ, h ⟨g, hg⟩ = n := by
    intro g hrel
    induction hrel with
    | refl =>
      intro hg
      have : (⟨M.faceOf d₀, hg⟩ : M.faceOrbits) =
          ⟨M.exterior, hM.exterior_mem_faceOrbits⟩ := Subtype.ext hd₀
      rw [this, h0]
      exact ⟨0, by simp⟩
    | tail _ hstep ih =>
      obtain ⟨x, rfl, rfl⟩ := hstep
      intro _
      obtain ⟨n, hn⟩ := ih (M.faceOf_mem_faceOrbits x)
      refine ⟨n + c x, ?_⟩
      change h (M.toFaceOrbit x) = n at hn
      change h (M.toFaceOrbit (M.inv x)) = _
      push_cast
      linarith [hc x]
  obtain ⟨e, rfl⟩ := M.toFaceOrbit_surjective f
  exact key _ (hM.toIsConnected.reflTransGen_faceAdj d₀ e) _

/-- **Integer cycles of a disk map bound**: if `c : H → ℤ` satisfies `c(d̄) = -c(d)` for every
dart and `∑_{d ∈ v} c(d) = 0` for every vertex, there is exactly one `h : Φ → ℤ` with
`h(f_∞) = 0` and `h(f_ℓ(d)) - h(f_r(d)) = c(d)` for every dart `d`, where `f_r(d) = f(d)` and
`f_ℓ(d) = f(d̄)` are the orbits of `φ` containing `d` and `d̄`. -/
@[cluster_algebras "lem_disk_map_cycles"]
theorem IsDiskMap.existsUnique_faceFunction (hM : M.IsDiskMap) (c : H → ℤ)
    (hc : ∀ d, c (M.inv d) = -c d) (hcv : ∀ v ∈ M.vertices, ∑ d ∈ v, c d = 0) :
    ∃! h : M.faceOrbits → ℤ, h ⟨M.exterior, hM.exterior_mem_faceOrbits⟩ = 0 ∧
      ∀ d, h (M.toFaceOrbit (M.inv d)) - h (M.toFaceOrbit d) = c d := by
  have hR : M.IsConnected := hM.toIsConnected
  set ext : M.faceOrbits := ⟨M.exterior, hM.exterior_mem_faceOrbits⟩
  have hcZ : (fun d => (c d : ℚ)) ∈ M.cycleSpace := by
    refine ⟨fun d => by simp [hc], fun v hv => ?_⟩
    simp only
    exact_mod_cast hcv v hv
  rw [← hR.range_coboundary_eq hM.euler] at hcZ
  obtain ⟨h₀, hh₀⟩ := hcZ
  obtain ⟨h₁, hext₁, hh₁⟩ : ∃ h₁ : M.faceOrbits → ℚ, h₁ ext = 0 ∧
      ∀ d, h₁ (M.toFaceOrbit (M.inv d)) - h₁ (M.toFaceOrbit d) = c d := by
    refine ⟨fun f => h₀ f - h₀ ext, by simp, fun d => ?_⟩
    have := congr_fun hh₀ d
    simp only [RotationSystem.coboundary_apply] at this
    linarith
  choose n hn using hM.exists_int_eq_of_sub_eq hext₁ hh₁
  have hn0 : n ext = 0 := by exact_mod_cast (hext₁ ▸ hn ext).symm
  have hnc : ∀ d, n (M.toFaceOrbit (M.inv d)) - n (M.toFaceOrbit d) = c d := fun d => by
    have := hh₁ d
    rw [hn, hn] at this
    exact_mod_cast this
  refine ⟨n, ⟨hn0, hnc⟩, fun h₂ ⟨h2e, h2c⟩ => funext fun f => ?_⟩
  have := hR.eq_of_forall_inv (h := fun f => h₂ f - n f) (fun d => by
    linarith [h2c d, hnc d]) f ext
  simp only [h2e, hn0] at this
  linarith

end DiskMap

end ClusterAlgebras

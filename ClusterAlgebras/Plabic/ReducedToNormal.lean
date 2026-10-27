/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.LoopDecomposition
public import ClusterAlgebras.Plabic.LoopDecomposition2
public import ClusterAlgebras.Plabic.NearlyLeaflessSequences
public import ClusterAlgebras.Plabic.ReducedIffMinimal
public import ClusterAlgebras.Plabic.ExcisionLemmas

/-!
# Reduced graphs are move-equivalent to normal graphs

Let `G` be a reduced nearly leafless plabic graph without white lollipops. By strong induction on
the number of faces, `G` is move-equivalent to a normal plabic graph. First `G ∼ K` for a nearly
leafless graph `K` that is normal or has a loop `{d, d̄}` at a black internal vertex `u`. In the
second case `K` is reduced with the faces of `G`, so the rotation at `u` is
`(d, a₁, …, a_k, d̄, b₁, …, b_l)` with `k, l ≥ 1` (an empty side would be an internal face with one
dart), and, the loop separating the two sides, one side of the loop contains no dart of `B`.
Cutting `K` along the loop gives `K ∼ Y⟨f ← R⟩`, where `R` has one boundary vertex, no internal
leaf and fewer faces, and `Y` is move-equivalent to a graph with an internal face of one dart.
A hollow digon of a graph nearly leafless equivalent to `R` would be a hollow digon of the
corresponding gluing, so `R` is reduced; by induction `R ∼ N` with `N` normal and reduced. The
triple diagram `X(N)` is minimal, with the (trivial) strand permutation of `X(L_black)`, which has
no triple point; a white vertex of `N` would give a triple point of `X(N)`, so `N ≅ L_black`.
Then `K ∼ Y⟨f ← L_black⟩ ≅ Y`, and `Y` is not reduced: a contradiction.

## Main results

* `ClusterAlgebras.PlabicGraph.IsReduced.exists_moveEquivalent_isNormalPlabicGraph`: a reduced
  nearly leafless plabic graph without white lollipops is move-equivalent to a normal plabic
  graph.

## Implementation notes

* FWZ's hypothesis "no white lollipop, nor a tree that collapses to a white lollipop" is used in
  the form "nearly leafless, no white lollipop"; no property of decorated trip permutations is
  used.
* The gluing `Y⟨f ← R⟩` lives on a subset of `H_Y ⊕ H_R`, so the darts of `Y` and of the inserted
  graph are disjoint by construction and no isomorphic copies are needed.
* The induction is over all numbers of boundary vertices at once, since the inside `R` has one
  boundary vertex.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

open Finset Function Equiv Equiv.Perm

namespace ClusterAlgebras

namespace RotationSystem

variable {H₀ : Type*} [Fintype H₀] [DecidableEq H₀] {R : RotationSystem H₀}

/-- If the rotation at `v(x)` is the cycle `(x, a₁, …, a_k, y, b₁, …, b_l)`, the open arc from `x`
to `y` is `{a₁, …, a_k}`. -/
private theorem rotArc_eq_of_toList {x y : H₀} {as bs : List H₀}
    (hL : R.rot.toList x = x :: as ++ y :: bs) : R.rotArc x y = {z | z ∈ as} := by
  have hnd := nodup_of_toList hL
  have hget : ∀ n (hn : n < (x :: as ++ y :: bs).length),
      (R.rot ^ n) x = (x :: as ++ y :: bs)[n] := fun n hn => by
    rw [← Equiv.Perm.getElem_toList R.rot x n (by rwa [hL])]
    exact List.getElem_of_eq hL _
  have hlen : (x :: as ++ y :: bs).length = as.length + bs.length + 2 := by
    simp only [List.cons_append, List.length_cons, List.length_append]
    omega
  have hy : (R.rot ^ (as.length + 1)) x = y := by
    rw [hget _ (by omega)]
    simp [List.getElem_append_right]
  have has : ∀ k (hk : k < as.length), (x :: as ++ y :: bs)[k + 1]'(by omega) = as[k] := by
    intro k hk
    simp [List.getElem_append_left hk]
  have hdist : R.rotDist x y = as.length + 1 := by
    apply le_antisymm
      (Nat.sInf_le (show as.length + 1 ∈ {m | 0 < m ∧ (R.rot ^ m) x = y} from ⟨by omega, hy⟩))
    obtain ⟨hpos, heq⟩ := Nat.sInf_mem (s := {m | 0 < m ∧ (R.rot ^ m) x = y}) ⟨_, by omega, hy⟩
    by_contra hlt
    push Not at hlt
    change sInf {m | 0 < m ∧ (R.rot ^ m) x = y} < as.length + 1 at hlt
    have h1 := hget _ (by omega : sInf {m | 0 < m ∧ (R.rot ^ m) x = y} < _)
    have h2 := hget (as.length + 1) (by omega)
    rw [heq] at h1
    rw [hy] at h2
    have := (hnd.getElem_inj_iff).1 (h1.symm.trans h2)
    omega
  ext a
  rw [mem_rotArc, hdist, Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, hm0, hm, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [hget _ (by omega), has k (by omega)]
    exact List.getElem_mem _
  · intro ha
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    exact ⟨k + 1, by omega, by omega, by rw [hget _ (by omega), has k hk]⟩

/-- If the rotation at `v(d)` is the cycle `(d, a₁, …, a_k, d̄, b₁, …, b_l)`, then `LoopStep d`
equals `ArcLoopStep d [a₁, …, a_k] [b₁, …, b_l]`. -/
private theorem loopStep_eq_arcLoopStep {d : H₀} {as bs : List H₀}
    (hL : R.rot.toList d = d :: as ++ R.inv d :: bs) :
    R.LoopStep d = R.ArcLoopStep d as bs := by
  have hA := rotArc_eq_of_toList hL
  have hB := rotArc_eq_of_toList (toList_eq_of_toList hL)
  funext z z'
  simp only [LoopStep, ArcLoopStep, hA, hB, Set.mem_setOf_eq, eq_iff_iff]
  tauto

end RotationSystem

/-! ### Choosing the inside of a loop -/

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- A dart at a boundary vertex is not at the internal vertex `v(d)` of a loop. -/
private theorem notMem_vertexOf_of_isBoundaryVertex {d x : H}
    (hu : ¬G.IsBoundaryVertex (G.vertexOf d)) (hloop : G.inv d ∈ G.vertexOf d)
    (hx : G.IsBoundaryVertex (G.vertexOf x)) : x ∉ G.vertexOf d ∧ x ≠ d ∧ x ≠ G.inv d := by
  have hxu : x ∉ G.vertexOf d := fun h => hu (G.vertexOf_eq_of_mem h ▸ hx)
  exact ⟨hxu, fun h => hxu (h ▸ G.self_mem_vertexOf d), fun h => hxu (h ▸ hloop)⟩

/-- Around a loop at an internal vertex, a dart at a boundary vertex is related to its rotation
by `ArcLoopStep`. -/
private theorem arcLoopStep_rot_of_isBoundaryVertex {d : H}
    (hu : ¬G.IsBoundaryVertex (G.vertexOf d)) (hloop : G.inv d ∈ G.vertexOf d) (as bs : List H)
    {x : H} (hx : G.IsBoundaryVertex (G.vertexOf x)) : G.ArcLoopStep d as bs x (G.rot x) := by
  have hx' : G.IsBoundaryVertex (G.vertexOf (G.rot x)) := by rwa [G.vertexOf_rot]
  obtain ⟨hxu, hx₁, hx₂⟩ := notMem_vertexOf_of_isBoundaryVertex hu hloop hx
  obtain ⟨-, hx₁', hx₂'⟩ := notMem_vertexOf_of_isBoundaryVertex hu hloop hx'
  exact ⟨hx₁, hx₂, hx₁', hx₂', Or.inr (Or.inl ⟨Or.inl rfl, hxu⟩)⟩

/-- Around a loop at an internal vertex, a dart at a boundary vertex is joined to its images
under the rotation by steps of `ArcLoopStep`. -/
private theorem reflTransGen_arcLoopStep_rot_pow {d : H}
    (hu : ¬G.IsBoundaryVertex (G.vertexOf d)) (hloop : G.inv d ∈ G.vertexOf d) (as bs : List H)
    {x : H} (hx : G.IsBoundaryVertex (G.vertexOf x)) (n : ℕ) :
    Relation.ReflTransGen (G.ArcLoopStep d as bs) x ((G.rot ^ n) x) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    have hv : G.vertexOf ((G.rot ^ n) x) = G.vertexOf x :=
      G.vertexOf_eq_of_mem (G.mem_vertexOf.2 ⟨n, by simp⟩)
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.tail (arcLoopStep_rot_of_isBoundaryVertex hu hloop as bs (hv ▸ hx))

/-- Around a loop at an internal vertex `v(d)` of a plabic graph, any two darts at boundary
vertices are joined by steps of `ArcLoopStep`. -/
private theorem reflTransGen_arcLoopStep_of_isBoundaryVertex (hG : G.IsPlabicGraph) {d : H}
    (hu : ¬G.IsBoundaryVertex (G.vertexOf d)) (hloop : G.inv d ∈ G.vertexOf d) (as bs : List H)
    {c c' : H} (hc : G.IsBoundaryVertex (G.vertexOf c))
    (hc' : G.IsBoundaryVertex (G.vertexOf c')) :
    Relation.ReflTransGen (G.ArcLoopStep d as bs) c c' := by
  obtain ⟨x₀, hx₀⟩ := G.mem_faceOrbits.1 hG.exterior_mem_faceOrbits
  have hφstep : ∀ e ∈ G.exterior,
      Relation.ReflTransGen (G.ArcLoopStep d as bs) e (G.facePerm e) := by
    intro e he
    have heB := G.exterior_subset_bdry he
    have hv : G.IsBoundaryVertex (G.vertexOf e) := G.isBoundaryVertex_vertexOf_of_mem heB
    have hv' : G.IsBoundaryVertex (G.vertexOf (G.inv e)) :=
      G.isBoundaryVertex_vertexOf_of_mem (hG.inv_mem_bdry e heB)
    obtain ⟨-, he₁, he₂⟩ := notMem_vertexOf_of_isBoundaryVertex hu hloop hv
    obtain ⟨-, he₁', he₂'⟩ := notMem_vertexOf_of_isBoundaryVertex hu hloop hv'
    rw [RotationSystem.facePerm_apply]
    exact (Relation.ReflTransGen.single ⟨he₁, he₂, he₁', he₂', Or.inl rfl⟩).tail
      (arcLoopStep_rot_of_isBoundaryVertex hu hloop as bs hv')
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
  have hbd : ∀ x, G.IsBoundaryVertex (G.vertexOf x) →
      Relation.ReflTransGen (G.ArcLoopStep d as bs) x x₀ := by
    intro x hx
    obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hx)
    obtain ⟨i', rfl⟩ := (finRotate b).surjective i
    obtain ⟨e, he, hei, -⟩ := hG.exists_exterior i'
    rw [hi] at hei
    obtain ⟨n, hn⟩ := (G.mem_vertexOf.1 hei).exists_nat_pow_eq
    have hxe : Relation.ReflTransGen (G.ArcLoopStep d as bs) x e :=
      hn ▸ reflTransGen_arcLoopStep_rot_pow hu hloop as bs hx n
    have hex : e ∈ G.faceOf x₀ := hx₀ ▸ he
    obtain ⟨m, hm⟩ := (G.mem_faceOf.1 hex).exists_nat_pow_eq
    have he₀ := (hext m).2
    rw [hm] at he₀
    exact hxe.trans (RotationSystem.ArcLoopStep.reflTransGen_symm hG.inv_involutive he₀)
  exact (hbd c hc).trans
    (RotationSystem.ArcLoopStep.reflTransGen_symm hG.inv_involutive (hbd c' hc'))

/-- If `d̄` lies at the vertex of `d`, the cycle of the rotation through `d` is
`(d, a₁, …, a_k, d̄, b₁, …, b_l)`. -/
private theorem exists_rot_toList_eq_of_inv_mem_vertexOf (hG : G.IsPlabicGraph) {d : H}
    (hloop : G.inv d ∈ G.vertexOf d) :
    ∃ as bs, G.rot.toList d = d :: as ++ G.inv d :: bs := by
  have hdι : G.inv d ≠ d := hG.inv_ne d
  have hsupp : d ∈ G.rot.support := by
    rw [Equiv.Perm.mem_support]
    intro h
    exact hdι ((G.mem_vertexOf.1 hloop).eq_of_left h).symm
  have hmem : G.inv d ∈ G.rot.toList d :=
    Equiv.Perm.mem_toList_iff.2 ⟨G.mem_vertexOf.1 hloop, hsupp⟩
  obtain ⟨s0, bs, hst⟩ := List.append_of_mem hmem
  obtain ⟨as, rfl⟩ : ∃ as, s0 = d :: as := by
    have h0 := Equiv.Perm.toList_getElem_zero G.rot d hsupp
    rw [List.getElem_of_eq hst] at h0
    cases s0 with
    | nil =>
      simp only [List.nil_append, List.getElem_cons_zero] at h0
      exact absurd h0 hdι
    | cons a as =>
      simp only [List.cons_append, List.getElem_cons_zero] at h0
      exact ⟨as, by rw [h0]⟩
  exact ⟨as, bs, hst⟩

/-- **Choosing the inside of a loop.** If the rotation at the internal vertex `u = v(d)` of a
plabic graph is the cycle `(d, a₁, …, a_k, d̄, b₁, …, b_l)` with `k, l ≥ 1`, then for `d' = d` or
`d' = d̄` the side of `(u, d')` contains no dart of `B`. -/
private theorem exists_loopSide_notMem_bdry (hG : G.IsPlabicGraph) {d : H}
    (hu : ¬G.IsBoundaryVertex (G.vertexOf d)) (hloop : G.inv d ∈ G.vertexOf d)
    (hk : G.rot d ≠ G.inv d) (hl : G.rot (G.inv d) ≠ d) :
    ∃ d', d' ∈ G.vertexOf d ∧ G.inv d' ∈ G.vertexOf d' ∧ G.rot d' ≠ G.inv d' ∧
      G.rot (G.inv d') ≠ d' ∧ ∀ z ∈ G.loopSide d', z ∉ G.bdry := by
  have hι := hG.inv_involutive
  obtain ⟨as, bs, hL⟩ := exists_rot_toList_eq_of_inv_mem_vertexOf hG hloop
  have has : as ≠ [] := by
    rintro rfl
    exact hk (by simpa only [List.not_mem_nil, false_or] using
      apply_mem_or_eq_of_toList hL List.mem_cons_self)
  have hbs : bs ≠ [] := by
    rintro rfl
    exact hl (by simpa only [List.not_mem_nil, false_or] using
      apply_mem_or_eq_of_toList (toList_eq_of_toList hL) List.mem_cons_self)
  have hvu : G.vertexOf (G.inv d) = G.vertexOf d := G.vertexOf_eq_of_mem hloop
  have hL' : G.rot.toList (G.inv d) = G.inv d :: bs ++ G.inv (G.inv d) :: as := by
    rw [hι d]
    exact toList_eq_of_toList hL
  have hsepAB := hG.toIsDiskMap.loop_separates hL has hbs
  by_cases hA : ∀ s ∈ as, ∀ z, Relation.ReflTransGen (G.ArcLoopStep d as bs) s z →
      ¬G.IsBoundaryVertex (G.vertexOf z)
  · refine ⟨d, G.self_mem_vertexOf d, hloop, hk, hl, fun z hz hzB => ?_⟩
    rw [RotationSystem.loopSide, Set.mem_setOf_eq, RotationSystem.loopStep_eq_arcLoopStep hL]
      at hz
    exact hA _ (apply_mem_of_toList hL has) z hz.2.2 (G.isBoundaryVertex_vertexOf_of_mem hzB)
  · push Not at hA
    obtain ⟨s, hs, z, hsz, hz⟩ := hA
    refine ⟨G.inv d, hloop, ?_, ?_, ?_, fun z' hz' hz'B => ?_⟩
    · rw [hι d, hvu]
      exact G.self_mem_vertexOf d
    · rwa [hι d]
    · rwa [hι d]
    · rw [RotationSystem.loopSide, Set.mem_setOf_eq, RotationSystem.loopStep_eq_arcLoopStep hL',
        G.arcLoopStep_inv hι hvu as bs] at hz'
      exact hsepAB ⟨s, hs, _, apply_mem_of_toList hL' hbs,
        (hsz.trans (reflTransGen_arcLoopStep_of_isBoundaryVertex hG hu hloop as bs hz
          (G.isBoundaryVertex_vertexOf_of_mem hz'B))).trans
          (RotationSystem.ArcLoopStep.reflTransGen_symm hι hz'.2.2)⟩

end PlabicData

/-! ### Hollow digons of a glued graph -/

/-- The orbit of a point exchanged with another one by the face permutation is the pair of
them. -/
private theorem RotationSystem.faceOf_eq_pair' {X : Type*} [Fintype X] [DecidableEq X]
    (R : RotationSystem X) {x y : X} (hxy : R.facePerm x = y) (hyx : R.facePerm y = x) :
    R.faceOf x = {x, y} := by
  ext z
  rw [RotationSystem.mem_faceOf]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have := ih ⟨(n : ℤ), by rw [zpow_natCast]⟩
      simp only [mem_insert, mem_singleton] at this ⊢
      rcases this with h | h <;> rw [h] <;> simp [hxy, hyx]
  · simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · rw [← hxy]
      exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)

/-- If the orbit of `x` under the face permutation is a pair `{x, y}` with `x ≠ y`, the face
permutation maps `x` to `y`. -/
private theorem RotationSystem.facePerm_eq_of_faceOf_eq_pair {X : Type*} [Fintype X]
    [DecidableEq X] (R : RotationSystem X) {x y : X} (h : R.faceOf x = {x, y}) (hxy : x ≠ y) :
    R.facePerm x = y := by
  have h₁ : R.facePerm x ∈ ({x, y} : Finset X) := by
    rw [← h]
    exact R.facePerm_mem_faceOf x
  have h₂ : y ∈ R.faceOf x := by simp [h]
  rcases mem_insert.1 h₁ with h₁ | h₁
  · exact absurd ((R.mem_faceOf.1 h₂).eq_of_left h₁) hxy
  · exact mem_singleton.1 h₁

namespace PlabicData

variable {HY HR : Type*} [Fintype HY] [Fintype HR] [DecidableEq HY] [DecidableEq HR] {b : ℕ}
  {Y : PlabicData HY b} {f : HY} {R : PlabicData HR 1} {p g : HR}

omit [Fintype HY] [DecidableEq HY] in
/-- A dart of `R` whose face avoids `p̄` is neither the leg `g` nor its partner `ḡ`. -/
private theorem IsLeafGluingSite.ne_of_inv_notMem_faceOf (h : Y.IsLeafGluingSite f R p g)
    {r : HR} (hp : R.inv p ∉ R.faceOf r) : r ≠ g ∧ r ≠ R.inv g := by
  constructor
  · rintro rfl
    have hφp : R.facePerm (R.inv p) = r := by
      rw [RotationSystem.facePerm_apply, h.inv_inv_right, h.rot_right]
    have := Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl R.facePerm (R.inv p))
    rw [hφp] at this
    exact hp (R.mem_faceOf.2 this)
  · rintro rfl
    have hφ : R.facePerm (R.inv g) = R.inv p := by
      rw [RotationSystem.facePerm_apply, h.inv_inv_right, h.rot_rot_right]
    exact hp (hφ ▸ R.facePerm_mem_faceOf _)

omit [Fintype HY] [Fintype HR] in
/-- A dart of the gluing `Y⟨f ← R⟩` coming from `R` is not in its boundary. -/
private theorem IsLeafGluingSite.notMem_leafGluing_bdry_of_coe_eq_inr
    (h : Y.IsLeafGluingSite f R p g) {x : leafGluingDarts f R p g} {r : HR}
    (hx : (x : HY ⊕ HR) = Sum.inr r) : x ∉ (Y.leafGluing h).bdry := by
  intro hxB
  rw [mem_leafGluing_bdry h, hx] at hxB
  simp at hxB

/-- A hollow digon of `R` gives a hollow digon of the gluing `Y⟨f ← R⟩`: its darts avoid the
leg `g` and its partner `ḡ`, so the gluing does not change the face permutation on them. -/
private theorem IsLeafGluingSite.exists_isHollowDigon_leafGluing
    (h : Y.IsLeafGluingSite f R p g) {s : Finset HR} (hs : R.IsHollowDigon s) :
    ∃ s', (Y.leafGluing h).IsHollowDigon s' := by
  obtain ⟨hsI, c₁, c₂, rfl, hv⟩ := hs
  obtain ⟨hsF, hdisj⟩ := R.mem_internalFaces.1 hsI
  obtain ⟨e, he⟩ := R.mem_faceOrbits.1 (R.mem_faces.1 hsF).2
  have hc₁₂ : c₁ ≠ c₂ := fun h' => hv (h' ▸ rfl)
  have hface : ∀ r ∈ ({c₁, c₂} : Finset HR), R.faceOf r = {c₁, c₂} := fun r hr => by
    rw [← he, R.faceOf_eq_of_mem (by rwa [he])]
  have hnotB : ∀ r ∈ ({c₁, c₂} : Finset HR), r ∉ R.bdry := fun r hr hrB =>
    disjoint_left.1 hdisj hr hrB
  have hpB : ∀ r ∈ ({c₁, c₂} : Finset HR), R.inv p ∉ R.faceOf r := fun r hr hp =>
    hnotB _ (by rwa [← hface r hr]) h.mem_bdry_inv_p
  have hng : ∀ r ∈ ({c₁, c₂} : Finset HR), r ≠ g ∧ r ≠ R.inv g := fun r hr =>
    h.ne_of_inv_notMem_faceOf (hpB r hr)
  have hmem : ∀ r ∈ ({c₁, c₂} : Finset HR), Sum.inr r ∈ leafGluingDarts f R p g := by
    intro r hr
    simp only [leafGluingDarts, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      reduceCtorEq, Sum.inr.injEq, false_or, not_or]
    exact ⟨fun e => hnotB r hr (e ▸ h.mem_bdry_inv_p), fun e => hnotB r hr (e ▸ h.mem_bdry_p),
      (hng r hr).1⟩
  have hφx : ∀ r (hr : r ∈ ({c₁, c₂} : Finset HR)),
      ((Y.leafGluing h).facePerm ⟨_, hmem r hr⟩ : HY ⊕ HR) = Sum.inr (R.facePerm r) := by
    intro r hr
    rw [h.coe_leafGluing_facePerm_of_ne (by simp) (by simpa using (hng r hr).2)]
    rfl
  have m₁ : c₁ ∈ ({c₁, c₂} : Finset HR) := by simp
  have m₂ : c₂ ∈ ({c₁, c₂} : Finset HR) := by simp
  set x₁ : leafGluingDarts f R p g := ⟨_, hmem c₁ m₁⟩
  set x₂ : leafGluingDarts f R p g := ⟨_, hmem c₂ m₂⟩
  have hx12 : (Y.leafGluing h).facePerm x₁ = x₂ := Subtype.ext (by
    rw [hφx c₁ m₁, RotationSystem.facePerm_eq_of_faceOf_eq_pair _ (hface c₁ m₁) hc₁₂])
  have hx21 : (Y.leafGluing h).facePerm x₂ = x₁ := Subtype.ext (by
    rw [hφx c₂ m₂, RotationSystem.facePerm_eq_of_faceOf_eq_pair _
      ((hface c₂ m₂).trans (pair_comm c₁ c₂)) hc₁₂.symm])
  have hpair := RotationSystem.faceOf_eq_pair' _ hx12 hx21
  refine ⟨{x₁, x₂}, ?_, x₁, x₂, rfl, ?_⟩
  · rw [DiskMap.mem_internalFaces, DiskMap.mem_faces]
    refine ⟨⟨fun he' => h.notMem_leafGluing_bdry_of_coe_eq_inr (r := c₁) rfl
      ((Y.leafGluing h).exterior_subset_bdry (by rw [← he']; exact mem_insert_self _ _)), ?_⟩, ?_⟩
    · rw [← hpair]
      exact (Y.leafGluing h).mem_faceOrbits.2 ⟨x₁, rfl⟩
    · rw [disjoint_left]
      intro x hx
      rw [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [h.notMem_leafGluing_bdry_of_coe_eq_inr (r := c₁) rfl,
        h.notMem_leafGluing_bdry_of_coe_eq_inr (r := c₂) rfl]
  · intro heq
    have := congrArg (Finset.map (Function.Embedding.subtype _)) heq
    rw [h.map_leafGluing_vertexOf_inr (x := x₁) (r := c₁) rfl,
      h.map_leafGluing_vertexOf_inr (x := x₂) (r := c₂) rfl] at this
    exact hv (Finset.map_injective _ this)

end PlabicData

/-! ### Triple points of the triple diagram of a normal graph -/

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- In the triple diagram `X(G)`, the vertex of `x⁺_k` for a dart `k` at a black vertex that is
not the reverse `ḡ_i` of a leg contains no dart of the boundary circle: it is a triple point. -/
private theorem IsNormalPlabicPregraph.vertexOf_plus_mem_internalVertices
    (hG : G.IsNormalPlabicPregraph) {k : G.BlackDart} (hk : G.legIndex k = none) :
    (G.tripleOfNormal hG).vertexOf (.plus k) ∈ (G.tripleOfNormal hG).internalVertices := by
  rw [DiskMap.vertexOf_mem_internalVertices]
  rintro ⟨z, hz, hzB⟩
  rw [hG.mem_tripleOfNormal_bdry] at hzB
  have hv := (G.tripleOfNormal hG).vertexOf_eq_of_mem hz
  have key : ∀ r, (G.tripleOfNormal hG).vertexOf (.del r) =
      (G.tripleOfNormal hG).vertexOf (.plus k) → False := by
    intro r hr
    have hmem : (TripleOfNormalDart.plus k : G.TripleDart) ∈
        (G.tripleOfNormal hG).vertexOf (.del r) := by
      rw [hr]
      exact (G.tripleOfNormal hG).self_mem_vertexOf _
    rw [hG.vertexOf_tripleOfNormal_del r, mem_insert, mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h
    · cases h
    · unfold IsNormalPlabicPregraph.endDart at h
      split_ifs at h
      cases h
      rw [hG.legIndex_invLeg] at hk
      cases hk
    · cases h
  cases z with
  | plus _ => simp at hzB
  | minus _ => simp at hzB
  | del r => exact key r hv
  | del' r => exact key _ ((hG.vertexOf_tripleOfNormal_del' r).symm.trans hv)

/-- If every dart at a black vertex is the reverse `ḡ_i` of a leg, the triple diagram `X(G)` has
no triple point. -/
private theorem IsNormalPlabicPregraph.internalVertices_tripleOfNormal_eq_empty
    (hG : G.IsNormalPlabicPregraph) (h : ∀ k : G.BlackDart, G.legIndex k ≠ none) :
    (G.tripleOfNormal hG).internalVertices = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  obtain ⟨hvV, hvB⟩ := (DiskMap.mem_internalVertices _).1 hv
  obtain ⟨z, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
  apply hvB
  cases z with
  | plus k =>
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (h k)
    refine ⟨_, (G.tripleOfNormal hG).rot_mem_vertexOf _, ?_⟩
    rw [tripleOfNormal_rot, hG.tripleRot_plus_of_some hi, mem_tripleOfNormal_bdry]
    rfl
  | minus k =>
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (h k)
    refine ⟨_, (G.tripleOfNormal hG).rot_mem_vertexOf _, ?_⟩
    rw [tripleOfNormal_rot, hG.tripleRot_minus_of_some hi, mem_tripleOfNormal_bdry]
    rfl
  | del r =>
    exact (G.tripleOfNormal hG).isBoundaryVertex_vertexOf_of_mem
      ((mem_tripleOfNormal_bdry hG).2 rfl)
  | del' r =>
    exact (G.tripleOfNormal hG).isBoundaryVertex_vertexOf_of_mem
      ((mem_tripleOfNormal_bdry hG).2 rfl)

/-- The black lollipop graph `L_black` is a normal plabic graph. -/
private theorem isNormalPlabicGraph_lollipopGraph_black :
    (lollipopGraph .black).IsNormalPlabicGraph :=
  ⟨isPlabicGraph_lollipopGraph .black, by constructor <;> decide⟩

/-- The triple diagram of the black lollipop graph `L_black` has no triple point. -/
private theorem internalVertices_toTripleDiagram_lollipopGraph_black :
    isNormalPlabicGraph_lollipopGraph_black.toTripleDiagram.data.internalVertices = ∅ := by
  refine isNormalPlabicGraph_lollipopGraph_black.isNormalPlabicPregraph
    |>.internalVertices_tripleOfNormal_eq_empty fun k => ?_
  obtain ⟨k, hk⟩ := k
  obtain rfl : k = .gBar := by
    revert hk
    cases k <;> decide
  change (lollipopGraph .black).legIndex
    ((lollipopGraph .black).inv ((lollipopGraph .black).leg 0)) ≠ none
  rw [isNormalPlabicGraph_lollipopGraph_black.isNormalPlabicPregraph.legIndex_inv_leg]
  simp

/-- A normal plabic graph whose triple diagram has no triple point has no internal white
vertex. -/
private theorem IsNormalPlabicGraph.colour_ne_white_of_internalVertices_eq_empty
    (hN : G.IsNormalPlabicGraph)
    (h : (G.tripleOfNormal hN.isNormalPlabicPregraph).internalVertices = ∅) {a : H}
    (ha : ¬G.IsBoundaryVertex (G.vertexOf a)) : G.colour a ≠ .white := by
  intro hc
  obtain ⟨h1, h2⟩ := hN.inv_internal_black_of_white ha hc
  have hnone : G.legIndex (G.inv a) = none :=
    hN.isNormalPlabicPregraph.legIndex_eq_none_of_internal
      (by rwa [hN.toIsPlabicGraph.inv_involutive a])
  have hv := hN.isNormalPlabicPregraph.vertexOf_plus_mem_internalVertices
    (k := ⟨_, mem_blackDarts.2 ⟨h1, h2⟩⟩) hnone
  rw [h] at hv
  exact notMem_empty _ hv

/-- **A reduced normal graph with one boundary vertex is a black lollipop.** Its triple diagram is
minimal and has the strand permutation of the triple diagram of `L_black`, which has no triple
point; so it has no triple point, the graph has no white vertex, and the vertex at the end of the
leg consists of `ḡ₁` alone. -/
private theorem IsNormalPlabicGraph.isomorphic_lollipopGraph_of_isMinimal {N : PlabicData H 1}
    (hN : N.IsNormalPlabicGraph) (hmin : hN.toTripleDiagram.IsMinimal) :
    N.Isomorphic (lollipopGraph .black) := by
  have hG := hN.toIsPlabicGraph
  have hcard :=
    hmin isNormalPlabicGraph_lollipopGraph_black.toTripleDiagram (Subsingleton.elim _ _)
  rw [internalVertices_toTripleDiagram_lollipopGraph_black, card_empty, Nat.le_zero,
    card_eq_zero] at hcard
  have hint := hN.not_isBoundaryVertex_inv_leg 0
  have hcol := hN.colour_inv_leg 0
  have hone : N.vertexOf (N.inv (N.leg 0)) = {N.inv (N.leg 0)} := by
    ext x
    rw [mem_singleton]
    refine ⟨fun hx => ?_, fun hx => hx ▸ N.self_mem_vertexOf _⟩
    have hxv : N.vertexOf x = N.vertexOf (N.inv (N.leg 0)) := N.vertexOf_eq_of_mem hx
    have hxc : N.colour x = .black := (hG.colour_eq_of_mem_vertexOf hint hx).trans hcol
    have hxi : ¬N.IsBoundaryVertex (N.vertexOf x) := hxv ▸ hint
    by_cases hb : N.IsBoundaryVertex (N.vertexOf (N.inv x))
    · have hxB : x ∉ N.bdry := notMem_bdry_of_mem_vertexOf hxi (N.self_mem_vertexOf x)
      obtain ⟨i, hi⟩ := hN.isNormalPlabicPregraph.exists_leg_eq hb
        fun h => hxB (hG.inv_mem_bdry_iff.1 h)
      rw [Subsingleton.elim i 0] at hi
      rw [hi, hG.inv_involutive]
    · exfalso
      refine hN.colour_ne_white_of_internalVertices_eq_empty hcard hb ?_
      cases hcx : N.colour (N.inv x) with
      | white => rfl
      | black => exact absurd (hcx.trans hxc.symm) (hN.colour_inv_ne x hxi hb)
  refine hG.isomorphic_lollipopGraph (u := {N.inv (N.leg 0)})
    ⟨⟨⟨?_, card_singleton _⟩, N.inv (N.leg 0), mem_singleton_self _, ?_⟩, fun d hd => ?_⟩
  · rw [← hone]
    exact N.vertexOf_mem_internalVertices.2 hint
  · rw [hG.inv_involutive]
    exact N.leg_mem_bvertex 0
  · rw [mem_singleton.1 hd]
    exact hcol

end PlabicData

/-! ### Gluing a black lollipop into a black leaf -/

namespace PlabicData

variable {HY : Type} [Fintype HY] [DecidableEq HY] {b : ℕ} {Y : PlabicData HY b} {f : HY}

omit [Fintype HY] [DecidableEq HY] in
/-- The only dart of `L_black` kept in the gluing `Y⟨f ← L_black⟩` is `ḡ`. -/
private theorem inr_mem_leafGluingDarts_lollipopGraph_iff (r : LollipopDart) :
    Sum.inr r ∈ leafGluingDarts f (lollipopGraph .black)
      ((lollipopGraph .black).rot.symm ((lollipopGraph .black).leg 0))
      ((lollipopGraph .black).leg 0) ↔ r = .gBar := by
  have hp : (lollipopGraph .black).rot.symm ((lollipopGraph .black).leg 0) = .e := by decide
  simp only [leafGluingDarts, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    reduceCtorEq, Sum.inr.injEq, false_or, not_or, hp]
  cases r <;> decide

omit [Fintype HY] [DecidableEq HY] in
/-- The darts of `Y` kept in the gluing `Y⟨f ← L_black⟩` are those other than `f`. -/
private theorem inl_mem_leafGluingDarts_lollipopGraph_iff (y : HY) :
    Sum.inl y ∈ leafGluingDarts f (lollipopGraph .black)
      ((lollipopGraph .black).rot.symm ((lollipopGraph .black).leg 0))
      ((lollipopGraph .black).leg 0) ↔ y ≠ f := by
  simp [leafGluingDarts]

/-- The darts of the gluing `Y⟨f ← L_black⟩` are those of `Y`, with `f` replaced by the dart `ḡ`
of `L_black`. -/
private def leafGluingLollipopEquiv (f : HY) : HY ≃ leafGluingDarts f (lollipopGraph .black)
    ((lollipopGraph .black).rot.symm ((lollipopGraph .black).leg 0))
    ((lollipopGraph .black).leg 0) where
  toFun y :=
    if hy : y = f then ⟨Sum.inr .gBar, (inr_mem_leafGluingDarts_lollipopGraph_iff _).2 rfl⟩
    else ⟨Sum.inl y, (inl_mem_leafGluingDarts_lollipopGraph_iff y).2 hy⟩
  invFun x := Sum.elim id (fun _ => f) x.1
  left_inv y := by
    by_cases hy : y = f
    · subst hy
      simp
    · simp [hy]
  right_inv := by
    rintro ⟨y | r, hx⟩
    · have hy : y ≠ f := (inl_mem_leafGluingDarts_lollipopGraph_iff y).1 hx
      simp [hy]
    · obtain rfl := (inr_mem_leafGluingDarts_lollipopGraph_iff r).1 hx
      simp

omit [Fintype HY] in
private theorem coe_leafGluingLollipopEquiv_self :
    (leafGluingLollipopEquiv f f : HY ⊕ LollipopDart) = Sum.inr .gBar := by
  simp [leafGluingLollipopEquiv]

omit [Fintype HY] in
private theorem coe_leafGluingLollipopEquiv_of_ne {y : HY} (hy : y ≠ f) :
    (leafGluingLollipopEquiv f y : HY ⊕ LollipopDart) = Sum.inl y := by
  simp [leafGluingLollipopEquiv, hy]

/-- Gluing the black lollipop graph `L_black` into a black leaf `{f}` of `Y` gives back `Y`: the
darts of the gluing are those of `Y`, with `f` replaced by the dart `ḡ` of `L_black`. -/
private theorem isomorphic_leafGluing_lollipopGraph (hY : Y.IsPlabicGraph) (hf : f ∉ Y.bdry)
    (hff : Y.rot f = f) (hc : Y.colour f = .black) :
    Y.Isomorphic (Y.leafGluing
      (isLeafGluingSite_of_isPlabicGraph hY (isPlabicGraph_lollipopGraph .black) hf hff)) := by
  have h := isLeafGluingSite_of_isPlabicGraph hY (isPlabicGraph_lollipopGraph .black) hf hff
  have hig : (lollipopGraph .black).inv ((lollipopGraph .black).leg 0) = .gBar := rfl
  have hrg : (lollipopGraph .black).rot .gBar = .gBar := by decide
  have hθf := coe_leafGluingLollipopEquiv_self (f := f)
  refine ⟨⟨leafGluingLollipopEquiv f, fun d => ?_, fun d => ?_, fun d => ?_, fun d _ => ?_,
    fun i => ?_⟩⟩
  · apply Subtype.ext
    rw [coe_leafGluing_inv]
    by_cases hd : d = f
    · subst hd
      rw [coe_leafGluingLollipopEquiv_of_ne h.inv_ne_self_left, hθf, ← hig,
        h.leafGluingInv_inr_inv_g]
    by_cases hd' : d = Y.inv f
    · subst hd'
      rw [h.inv_inv_left, hθf, coe_leafGluingLollipopEquiv_of_ne h.inv_ne_self_left,
        h.leafGluingInv_inl_inv_f, hig]
    have hid : Y.inv d ≠ f := fun e => hd' (h.inv_eq_f_iff.1 e)
    rw [coe_leafGluingLollipopEquiv_of_ne hid, coe_leafGluingLollipopEquiv_of_ne hd,
      h.leafGluingInv_of_ne (by simpa using hd) (by simpa using hd') (by simp) (by simp)]
    rfl
  · apply Subtype.ext
    rw [coe_leafGluing_rot]
    by_cases hd : d = f
    · subst hd
      rw [hff, hθf]
      simp [hrg]
    · rw [coe_leafGluingLollipopEquiv_of_ne (fun e => hd (h.rot_eq_f_iff.1 e)),
        coe_leafGluingLollipopEquiv_of_ne hd]
      rfl
  · rw [mem_leafGluing_bdry h]
    by_cases hd : d = f
    · subst hd
      rw [hθf]
      simp [hf]
    · rw [coe_leafGluingLollipopEquiv_of_ne hd]
      simp
  · rw [leafGluing_colour]
    by_cases hd : d = f
    · subst hd
      rw [hθf, hc]
      rfl
    · rw [coe_leafGluingLollipopEquiv_of_ne hd]
      rfl
  · have hG' := h.isPlabicGraph_leafGluing hY (isPlabicGraph_lollipopGraph .black)
    rw [hY.filter_bvertex_notMem_bdry i, hG'.filter_bvertex_notMem_bdry i, map_singleton]
    congr 1
    apply Subtype.ext
    rw [coe_leafGluing_leg]
    exact coe_leafGluingLollipopEquiv_of_ne (h.leg_ne i)

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- A plabic graph in which the face permutation fixes a dart outside `B` is not reduced. -/
private theorem not_isReduced_of_facePerm_eq (K : PlabicGraph b) {z : K.Dart}
    (hz : z ∉ K.data.bdry) (hφ : K.data.facePerm z = z) : ¬K.IsReduced := by
  have hface : K.data.faceOf z = {z} := by
    ext y
    rw [RotationSystem.mem_faceOf, mem_singleton]
    exact ⟨fun h => (h.eq_of_left hφ).symm, fun h => h ▸ Equiv.Perm.SameCycle.refl _ _⟩
  refine not_isReduced_of_card_eq_one K (f := K.data.faceOf z) ?_ (by rw [hface, card_singleton])
  rw [DiskMap.mem_internalFaces, DiskMap.mem_faces]
  refine ⟨⟨fun h => hz (K.data.exterior_subset_bdry ?_), K.data.mem_faceOrbits.2 ⟨z, rfl⟩⟩, ?_⟩
  · rw [← h, hface]
    exact mem_singleton_self z
  · rw [hface]
    exact disjoint_singleton_left.2 hz

/-- A hollow digon of `R` gives a hollow digon of the gluing `Y⟨f ← R⟩`. -/
private theorem exists_isHollowDigon_leafGluing (Y : PlabicGraph b) {f : Y.Dart}
    (hf : f ∉ Y.data.bdry) (hff : Y.data.rot f = f) (R : PlabicGraph 1) {s : Finset R.Dart}
    (hs : R.data.IsHollowDigon s) : ∃ s', (Y.leafGluing hf hff R).data.IsHollowDigon s' :=
  (isLeafGluingSite_of_isPlabicGraph Y.isPlabicGraph R.isPlabicGraph hf
    hff).exists_isHollowDigon_leafGluing hs

/-- Gluing `L_black` into a black leaf `{f}` of `Y` gives a graph isomorphic to `Y`. -/
private theorem leafGluing_lollipop_isomorphic (Y : PlabicGraph b) {f : Y.Dart}
    (hf : f ∉ Y.data.bdry) (hff : Y.data.rot f = f) (hc : Y.data.colour f = .black) :
    Y.Isomorphic (Y.leafGluing hf hff (lollipopPlabicGraph .black)) :=
  isomorphic_leafGluing_lollipopGraph Y.isPlabicGraph hf hff hc

/-- If a reduced graph is move-equivalent to a gluing `Y⟨f ← R⟩` with `R` nearly leafless,
then `R` is reduced. -/
private theorem isReduced_of_moveEquivalent_leafGluing {K : PlabicGraph b} (hKred : K.IsReduced)
    {Y : PlabicGraph b} {f : Y.Dart} {hf : f ∉ Y.data.bdry} {hff : Y.data.rot f = f}
    {R : PlabicGraph 1} (hKYR : MoveEquivalent Set.univ K (Y.leafGluing hf hff R))
    (hRnl : R.data.IsNearlyLeafless) : R.IsReduced := by
  by_contra hRred
  obtain ⟨X, hRX, s, hs⟩ := (not_isReduced_iff hRnl).1 hRred
  obtain ⟨s', hs'⟩ := exists_isHollowDigon_leafGluing Y hf hff X hs
  have hKX : MoveEquivalent Set.univ K (Y.leafGluing hf hff X) :=
    hKYR.trans (MoveEquivalent.leafGluing Y hf hff hRX.moveEquivalent)
  exact (hKred _ hKX.symm).1 s' hs'

/-- The statement of `IsReduced.exists_moveEquivalent_isNormalPlabicGraph` for graphs with `n`
faces, by strong induction on `n`. -/
private theorem exists_moveEquivalent_isNormalPlabicGraph_aux (n : ℕ) :
    ∀ (b : ℕ) (G : PlabicGraph b), G.data.faces.card = n → G.IsReduced →
      G.data.IsNearlyLeafless → (∀ i v, ¬G.data.IsLollipopOfColour i .white v) →
      ∃ N : PlabicGraph b, MoveEquivalent Set.univ G N ∧ N.data.IsNormalPlabicGraph := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b G hn hred hnl hw
  obtain ⟨K, hGK, hK, hnorm | ⟨d, hdB, hdv, hdu, hdc⟩⟩ :=
    exists_moveEquivalent_isNormal_or_loop hnl hw
  · exact ⟨K, hGK, ⟨K.isPlabicGraph, hnorm⟩⟩
  exfalso
  have hG := K.isPlabicGraph
  have hKred := hred.of_moveEquivalent hGK
  have hKn : K.data.faces.card = n := by rw [← hn, (hGK.card_eq).2.1]
  have hloop : K.data.inv d ∈ K.data.vertexOf d := hdv ▸ K.data.self_mem_vertexOf _
  have hk : K.data.rot d ≠ K.data.inv d := by
    intro h
    refine not_isReduced_of_facePerm_eq K (z := K.data.inv d)
      (fun h' => hdB (hG.inv_mem_bdry_iff.1 h')) ?_ hKred
    rw [RotationSystem.facePerm_apply, hG.inv_involutive, h]
  have hl : K.data.rot (K.data.inv d) ≠ d := fun h =>
    not_isReduced_of_facePerm_eq K hdB h hKred
  obtain ⟨d', hd'u, hloop', hk', hl', hS⟩ := exists_loopSide_notMem_bdry hG hdu hloop hk hl
  have hu' : ¬K.data.IsBoundaryVertex (K.data.vertexOf d') := by
    rwa [K.data.vertexOf_eq_of_mem hd'u]
  have hc' : K.data.colour d' = .black := by
    rw [hG.colour_eq_of_mem_vertexOf hdu hd'u, hdc]
  obtain ⟨Y, f, hf, hff, R, hcol, hRleaf, hRfaces, hKYR, Y', hYY', φ, hφ, hφcard⟩ :=
    exists_leafGluing_of_loop K hK hu' hloop' hk' hl' hS
  have hRnl : R.data.IsNearlyLeafless := fun v hv => absurd hv (hRleaf v)
  have hRred : R.IsReduced := isReduced_of_moveEquivalent_leafGluing hKred hKYR hRnl
  obtain ⟨N, hRN, hN⟩ := ih _ (hKn ▸ hRfaces) 1 R rfl hRred hRnl
    (fun i v hv => hRleaf v hv.1.1)
  have hNL : N.data.Isomorphic (lollipopGraph .black) :=
    hN.isomorphic_lollipopGraph_of_isMinimal
      ((isReduced_iff_isMinimal hN).1 (hRred.of_moveEquivalent hRN))
  have hRL : MoveEquivalent Set.univ R (lollipopPlabicGraph .black) :=
    hRN.trans (MoveEquivalent.of_isomorphic hNL.symm)
  have hKY' : MoveEquivalent Set.univ K Y' :=
    (hKYR.trans (MoveEquivalent.leafGluing Y hf hff hRL)).trans
      ((MoveEquivalent.of_isomorphic
        (leafGluing_lollipop_isomorphic Y hf hff (hcol.trans hc'))).trans hYY')
  exact not_isReduced_of_card_eq_one Y' hφ hφcard (hKred.of_moveEquivalent hKY')

/-- **Reduced nearly leafless graphs without white lollipops are move-equivalent to normal ones**:
a reduced nearly leafless plabic graph `G` that has no white lollipop is move-equivalent to a
normal plabic graph. -/
@[cluster_algebras "lem_reduced_to_normal"]
theorem IsReduced.exists_moveEquivalent_isNormalPlabicGraph {G : PlabicGraph b}
    (hred : G.IsReduced) (hnl : G.data.IsNearlyLeafless)
    (hw : ∀ i v, ¬G.data.IsLollipopOfColour i .white v) :
    ∃ N : PlabicGraph b, MoveEquivalent Set.univ G N ∧ N.data.IsNormalPlabicGraph :=
  exists_moveEquivalent_isNormalPlabicGraph_aux _ b G rfl hred hnl hw

end PlabicGraph

end ClusterAlgebras

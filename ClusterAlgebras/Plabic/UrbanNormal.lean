/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.UrbanRenewal
public import ClusterAlgebras.Plabic.NormalTriple
public import ClusterAlgebras.Plabic.Swivel

/-!
# Urban renewal and the normal flip are swivel moves

Let `G` be a normal plabic graph and `X(G)` its triple diagram, on the darts `x⁺_k`, `x⁻_k`
(`k ∈ K`, the darts at black vertices) and `∂_r`, `∂'_r`. The digons of `X(G)` come in two kinds:
`{x⁺_{c̄₄}, x⁺_{c̄₂}}` for an internal square face `(c₁, c₂, c₃, c₄)` with black corners `v(c₁)`,
`v(c₃)` and distinct white corners `v(c₂) ≠ v(c₄)`, the faces at which urban renewal applies; and
`{x⁻_k, x⁻_{σk}}` for a black vertex `{k, σk}` with two distinct white neighbours, the vertices at
which the normal flip applies.

Urban renewal and the normal flip replace the rotation `σ` of `G` by `σ ∘ π`. In both cases `π`
fixes the darts at boundary vertices and preserves the colours of the darts at internal vertices,
and the two white vertices it touches keep three darts each; so the result `G'` is a normal plabic
pregraph with the boundary vertices, legs and colours of `G`. Its triple diagram `X(G')` is
isomorphic to the swivel move of `X(G)` at the corresponding digon: for urban renewal by
`x⁻_k ↦ x⁻_k`, `x⁺_k ↦ x⁺_{π(k)}`, and for the normal flip by the identity of the symbols. Since a
swivel move of a triple diagram is a triple diagram, `X(G')` is a triple diagram, and so `G'` is a
normal plabic graph.

## Main results

* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.isDigon_tripleOfNormal_iff`: the digons of
  `X(G)`.
* `ClusterAlgebras.PlabicData.IsUrbanRenewalFace.isNormalPlabicPregraph_urbanRenewal`,
  `IsUrbanRenewalFace.boundaryVertices_urbanRenewal`, `IsUrbanRenewalFace.colour_urbanRenewal`:
  urban renewal gives a normal plabic pregraph with the boundary vertices, legs and colours of `G`.
* `ClusterAlgebras.PlabicData.IsUrbanRenewalFace.exists_iso_swivelMove`: urban renewal is a swivel
  move.
* `ClusterAlgebras.PlabicData.IsUrbanRenewalFace.isNormalPlabicGraph_urbanRenewal`: urban renewal
  gives a normal plabic graph.
* `ClusterAlgebras.PlabicData.IsNormalFlipVertex.isNormalPlabicPregraph_normalFlip`,
  `IsNormalFlipVertex.boundaryVertices_normalFlip`, `IsNormalFlipVertex.colour_normalFlip`,
  `IsNormalFlipVertex.vertexOf_normalFlip`, `IsNormalFlipVertex.rot_normalFlip`: the normal flip
  gives a normal plabic pregraph with the darts, black vertices, boundary vertices and legs of `G`,
  whose white vertices are those of `G` other than `v(k̄)`, `v(\overline{σk})`, together with
  `(k̄, a₂, b₁)` and `(\overline{σk}, b₂, a₁)`.
* `ClusterAlgebras.PlabicData.IsNormalFlipVertex.exists_iso_swivelMove`: the normal flip is a
  swivel move.
* `ClusterAlgebras.PlabicData.IsNormalFlipVertex.isNormalPlabicGraph_normalFlip`: the normal flip
  gives a normal plabic graph.

## Implementation notes

* **Darts of `K`.** A dart of `X(G)` such as `x⁺_k` carries the proof that `k ∈ K`. The digons in
  `IsNormalPlabicGraph.isDigon_tripleOfNormal_iff` are therefore written `{x⁺_{k₁}, x⁺_{k₂}}` for
  darts `k₁, k₂ ∈ K` with `k₁ = c̄₄` and `k₂ = c̄₂` (and likewise for the normal flip). A digon has
  two elements, so the set `δ` need not be assumed to have two elements.
* **The triple diagram of `G'`.** `G'` has the same set `K` of darts at black vertices as `G`, but
  `X(G')` is built on the type of darts `x^±_k` with `k ∈ K(G')`, which is not the type of the
  darts of `X(G)`. The statement that `X(G')` *is* the swivel move of `X(G)` after a normal flip is
  therefore the statement that the map `x^±_k ↦ x^±_k`, `∂_r ↦ ∂_r`, `∂'_r ↦ ∂'_r` is an
  isomorphism of pre-triple diagrams, together with `K(G') = K(G)`. The values of the isomorphisms
  are stated for every proof that the target lies in `K`.
* **The two white vertices.** Both moves are handled in the variables `x`, `y` of the two white
  vertices: `x = c̄₁`, `y = c̄₃` for urban renewal and `x = k̄`, `y = \overline{σk}` for the normal
  flip. In both cases `π` acts on the six darts of these vertices as `(x σx σ²y)(σ²x y σy)`; urban
  renewal moreover acts on their reverses as `(\overline{σy} x̄ \overline{σ²y})
  (\overline{σx} ȳ \overline{σ²x})`.
* **The faces of the digons.** The swivel move at a digon `{d₁, φ(d₁)}` is taken at `d₁ = x⁺_{c̄₄}`
  for urban renewal and `d₁ = x⁻_k` for the normal flip; the digon is the orbit of `φ` through
  `d₁`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Orbits of permutations -/

/-- If `f^m(x) = x` with `m > 0`, every point of the orbit of `x` is `f^j(x)` for some `j < m`. -/
private theorem exists_lt_pow_eq_of_sameCycle {α : Type*} [Finite α] {f : Equiv.Perm α}
    {x y : α} {m : ℕ} (hm : 0 < m) (hx : (f ^ m) x = x) (h : f.SameCycle x y) :
    ∃ j < m, (f ^ j) x = y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  refine ⟨n % m, Nat.mod_lt _ hm, ?_⟩
  have hpow : ∀ q, (f ^ (m * q)) x = x := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hx, ih]
  conv_rhs => rw [← Nat.mod_add_div n m, pow_add, Equiv.Perm.mul_apply, hpow]

/-- A property preserved by `f` holds along the orbit of `f`. -/
private theorem of_sameCycle_of_forall {α : Type*} [Finite α] {f : Equiv.Perm α} {P : α → Prop}
    (hP : ∀ y, P y → P (f y)) {x y : α} (hx : P x) (h : f.SameCycle x y) : P y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hP _ ih

/-- Two permutations agreeing on a set `S` closed under one of them have the same orbits through
the points of `S`. -/
private theorem sameCycle_iff_of_eqOn' {α : Type*} [Finite α] {f g : Equiv.Perm α} {S : α → Prop}
    (hS : ∀ y, S y → S (f y)) (hfg : ∀ y, S y → g y = f y) {x : α} (hx : S x) (y : α) :
    g.SameCycle x y ↔ f.SameCycle x y := by
  have key : ∀ n : ℕ, (g ^ n) x = (f ^ n) x ∧ S ((f ^ n) x) := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, ih.1]
      exact ⟨hfg _ ih.2, hS _ ih.2⟩
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [(key n).1]
    exact ⟨n, by rw [zpow_natCast]⟩
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [← (key n).1]
    exact ⟨n, by rw [zpow_natCast]⟩

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-! ### Rewiring a normal plabic graph -/

section Rewire

variable {π : Equiv.Perm H}

/-- If `π` fixes every dart of `v(d)`, then the vertex of `d` after rewiring is `v(d)`. -/
private theorem vertexOf_rewire_of_forall {d : H} (h : ∀ e ∈ G.vertexOf d, π e = e) :
    (G.rewire π).vertexOf d = G.vertexOf d := by
  ext e
  simp only [RotationSystem.mem_vertexOf, rot_rewire]
  exact sameCycle_iff_of_eqOn' (S := fun y => y ∈ G.vertexOf d)
    (fun y hy => by rw [← G.vertexOf_eq_of_mem hy]; exact G.rot_mem_vertexOf y)
    (fun y hy => by rw [Equiv.Perm.mul_apply, h y hy]) (G.self_mem_vertexOf d) e

variable (hG : G.IsNormalPlabicGraph)
  (hbd : ∀ d, G.IsBoundaryVertex (G.vertexOf d) → π d = d)
  (hcol : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) → G.colour (π d) = G.colour d)

include hbd

/-- `π` maps darts at internal vertices to darts at internal vertices. -/
private theorem not_isBoundaryVertex_perm {d : H} (hd : ¬G.IsBoundaryVertex (G.vertexOf d)) :
    ¬G.IsBoundaryVertex (G.vertexOf (π d)) := fun h =>
  hd (by have := hbd _ h; rwa [π.injective this] at h)

/-- At a boundary vertex the rewired graph has the vertex of `G`. -/
private theorem vertexOf_rewire_of_isBoundaryVertex {d : H}
    (hd : G.IsBoundaryVertex (G.vertexOf d)) : (G.rewire π).vertexOf d = G.vertexOf d :=
  vertexOf_rewire_of_forall fun e he => hbd e (by rwa [G.vertexOf_eq_of_mem he])

include hG hcol

/-- The darts of the new vertex of a dart `d` at an internal vertex of `G` lie at internal
vertices of `G`, of the colour of `d`. -/
private theorem forall_mem_vertexOf_rewire {d : H} (hd : ¬G.IsBoundaryVertex (G.vertexOf d)) :
    ∀ e ∈ (G.rewire π).vertexOf d,
      ¬G.IsBoundaryVertex (G.vertexOf e) ∧ G.colour e = G.colour d := by
  intro e he
  rw [RotationSystem.mem_vertexOf] at he
  refine of_sameCycle_of_forall (P := fun y => ¬G.IsBoundaryVertex (G.vertexOf y) ∧
    G.colour y = G.colour d) (fun y hy => ?_) ⟨hd, rfl⟩ he
  have hπ := not_isBoundaryVertex_perm hbd hy.1
  refine ⟨by rw [rot_rewire_apply, G.vertexOf_rot]; exact hπ, ?_⟩
  rw [rot_rewire_apply, hG.colour_rot _ hπ, hcol _ hy.1, hy.2]

/-- A vertex of the rewired graph is a boundary vertex exactly when the vertex of `G` through the
same dart is. -/
private theorem isBoundaryVertex_rewire_iff (d : H) :
    (G.rewire π).IsBoundaryVertex ((G.rewire π).vertexOf d) ↔
      G.IsBoundaryVertex (G.vertexOf d) := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨e, he, heB⟩ := h
    exact (forall_mem_vertexOf_rewire hG hbd hcol hd e he).1
      (G.isBoundaryVertex_vertexOf_of_mem heB)
  · intro h
    rw [vertexOf_rewire_of_isBoundaryVertex hbd h]
    exact h

/-- At an internal vertex the rewired graph keeps the colours of `G`. -/
private theorem colour_rewire_of_not_isBoundaryVertex {d : H}
    (hd : ¬G.IsBoundaryVertex (G.vertexOf d)) : (G.rewire π).colour d = G.colour d :=
  colour_rewire_of_forall (forall_mem_vertexOf_rewire hG hbd hcol hd)

private theorem boundaryVertices_rewire :
    (G.rewire π).boundaryVertices = G.boundaryVertices := by
  ext v
  simp only [DiskMap.mem_boundaryVertices, RotationSystem.mem_vertices]
  constructor
  · rintro ⟨⟨d, rfl⟩, hb⟩
    have hb' := (isBoundaryVertex_rewire_iff hG hbd hcol d).1 hb
    rw [vertexOf_rewire_of_isBoundaryVertex hbd hb']
    exact ⟨⟨d, rfl⟩, hb'⟩
  · rintro ⟨⟨d, rfl⟩, hb⟩
    rw [← vertexOf_rewire_of_isBoundaryVertex hbd hb]
    exact ⟨⟨d, rfl⟩, (isBoundaryVertex_rewire_iff hG hbd hcol d).2 hb⟩

omit hG hcol in
private theorem exterior_rewire : (G.rewire π).exterior = G.exterior := by
  ext d
  simp only [DiskMap.mem_exterior, bdry_rewire, rot_rewire_apply]
  refine and_congr_right fun hd => ?_
  rw [hbd d (G.isBoundaryVertex_vertexOf_of_mem hd)]

omit hcol in
private theorem faceOrbits_rewire {f : Finset H} (hf : f ∈ G.faceOrbits) (hfB : f ⊆ G.bdry) :
    f ∈ (G.rewire π).faceOrbits := by
  obtain ⟨d, rfl⟩ := G.mem_faceOrbits.1 hf
  refine (G.rewire π).mem_faceOrbits.2 ⟨d, ?_⟩
  ext e
  simp only [RotationSystem.mem_faceOf]
  refine sameCycle_iff_of_eqOn' (S := fun y => y ∈ G.faceOf d)
    (fun y hy => by rw [← G.faceOf_eq_of_mem hy]; exact G.facePerm_mem_faceOf y)
    (fun y hy => ?_) (G.self_mem_faceOf d) e
  have hy' : G.inv y ∈ G.bdry := hG.inv_mem_bdry _ (hfB hy)
  simp only [RotationSystem.facePerm_apply]
  change G.rot (π (G.inv y)) = G.rot (G.inv y)
  rw [hbd _ (G.isBoundaryVertex_vertexOf_of_mem hy')]

/-- A rewiring `σ ∘ π` of a normal plabic graph, with `π` fixing the darts at boundary vertices,
preserving the colours of the darts at internal vertices, and producing white vertices of three
darts, is a normal plabic pregraph. -/
private theorem isNormalPlabicPregraph_rewire
    (hwhite : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) → G.colour d = .white →
      ((G.rewire π).vertexOf d).card = 3) :
    (G.rewire π).IsNormalPlabicPregraph := by
  have hB := isBoundaryVertex_rewire_iff hG hbd hcol
  have hC := fun d => colour_rewire_of_not_isBoundaryVertex (d := d) hG hbd hcol
  have hBV := boundaryVertices_rewire hG hbd hcol
  have hbv : ∀ i, (G.rewire π).bvertex i = G.bvertex i := fun i =>
    vertexOf_rewire_of_isBoundaryVertex hbd
      (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))
  exact
  { colour_inv_ne := fun d hd hd' => by
      rw [hB] at hd
      have hd'' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv d)) := (hB (G.inv d)).not.1 hd'
      change (G.rewire π).colour (G.inv d) ≠ (G.rewire π).colour d
      rw [hC _ hd, hC _ hd'']
      exact hG.colour_inv_ne d hd hd''
    card_vertexOf_of_white := fun d hd hw => by
      rw [hB] at hd
      exact hwhite d hd (by rwa [hC _ hd] at hw)
    not_isBoundaryVertex_inv_leg := fun i => (hB _).not.2 (hG.not_isBoundaryVertex_inv_leg i)
    colour_inv_leg := fun i => by
      change (G.rewire π).colour (G.inv (G.leg i)) = _
      rw [hC _ (hG.not_isBoundaryVertex_inv_leg i)]
      exact hG.colour_inv_leg i
    one_le := hG.one_le
    nonempty := hG.nonempty
    inv_involutive := hG.inv_involutive
    inv_ne := hG.inv_ne
    inv_mem_bdry := hG.inv_mem_bdry
    boundaryVertex_card := by rw [hBV]; exact hG.boundaryVertex_card
    exists_orbit := by
      obtain ⟨f, hf, hfB, hu, hd⟩ := hG.exists_orbit
      exact ⟨f, faceOrbits_rewire hG hbd hf hfB, hfB, hu, hd⟩
    colour_rot := fun d hd => by
      rw [hB] at hd
      have hd' : ¬G.IsBoundaryVertex (G.vertexOf ((G.rewire π).rot d)) := by
        rw [rot_rewire_apply, G.vertexOf_rot]; exact not_isBoundaryVertex_perm hbd hd
      rw [hC _ hd, hC _ hd', rot_rewire_apply, hG.colour_rot _ (not_isBoundaryVertex_perm hbd hd),
        hcol _ hd]
    leg_notMem_bdry := hG.leg_notMem_bdry
    bvertex_mem := fun i => by rw [hbv, hBV]; exact hG.bvertex_mem i
    bvertex_injective := fun i j h => hG.bvertex_injective (by rwa [hbv, hbv] at h)
    exists_bvertex_eq := fun v hv => by
      rw [hBV] at hv
      obtain ⟨i, hi⟩ := hG.exists_bvertex_eq v hv
      exact ⟨i, by rw [hbv, hi]⟩
    exists_exterior := fun i => by
      rw [exterior_rewire hbd, hbv, hbv]
      exact hG.exists_exterior i }

end Rewire

/-! ### Two white vertices -/

/-- A vertex whose rotation is the `3`-cycle `(a, b, c)` is `{a, b, c}`. -/
private theorem vertexOf_eq_of_rot_three (R : RotationSystem H) {a b c : H} (h₁ : R.rot a = b)
    (h₂ : R.rot b = c) (h₃ : R.rot c = a) : R.vertexOf a = {a, b, c} := by
  have h3 : (R.rot ^ 3) a = a := by simp [pow_succ, h₁, h₂, h₃]
  ext e
  rw [RotationSystem.mem_vertexOf]
  simp only [mem_insert, mem_singleton]
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := exists_lt_pow_eq_of_sameCycle (by norm_num) h3 h
    interval_cases j <;> simp [pow_succ, h₁, h₂]
  · rintro (rfl | rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact ⟨1, by simp [h₁]⟩
    · exact ⟨((2 : ℕ) : ℤ), by rw [zpow_natCast]; simp [pow_succ, h₁, h₂]⟩

/-- Every dart of a white vertex of a normal plabic graph lies at an internal vertex and is
white. -/
private theorem forall_mem_vertexOf_of_white (hG : G.IsNormalPlabicGraph) {x : H}
    (hi : ¬G.IsBoundaryVertex (G.vertexOf x)) (hw : G.colour x = .white) :
    ∀ d ∈ G.vertexOf x, ¬G.IsBoundaryVertex (G.vertexOf d) ∧ G.colour d = .white := by
  intro d hd
  rw [RotationSystem.mem_vertexOf] at hd
  refine of_sameCycle_of_forall (P := fun y => ¬G.IsBoundaryVertex (G.vertexOf y) ∧
    G.colour y = .white) (fun y hy => ?_) ⟨hi, hw⟩ hd
  exact ⟨by rw [G.vertexOf_rot]; exact hy.1, by rw [hG.colour_rot _ hy.1, hy.2]⟩

/-- Two darts `x`, `y` at distinct white vertices of `G`. -/
private structure WhitePair (G : PlabicData H b) (x y : H) : Prop where
  int_x : ¬G.IsBoundaryVertex (G.vertexOf x)
  white_x : G.colour x = .white
  int_y : ¬G.IsBoundaryVertex (G.vertexOf y)
  white_y : G.colour y = .white
  ne : G.vertexOf x ≠ G.vertexOf y

namespace WhitePair

variable {x y : H} (hG : G.IsNormalPlabicGraph)

include hG

omit hG in
private theorem symm (w : WhitePair G x y) : WhitePair G y x :=
  ⟨w.int_y, w.white_y, w.int_x, w.white_x, w.ne.symm⟩

private theorem vertexOf_x (w : WhitePair G x y) : G.vertexOf x = {x, G.rot x, G.rot (G.rot x)} :=
  vertexOf_eq_of_card_vertexOf_eq_three (hG.card_vertexOf_of_white x w.int_x w.white_x)

private theorem rot3_x (w : WhitePair G x y) : G.rot (G.rot (G.rot x)) = x :=
  rot_rot_rot_of_card_vertexOf_eq_three (hG.card_vertexOf_of_white x w.int_x w.white_x)

private theorem rot_ne_x (w : WhitePair G x y) : G.rot x ≠ x ∧ G.rot (G.rot x) ≠ x :=
  rot_ne_of_card_vertexOf_eq_three (hG.card_vertexOf_of_white x w.int_x w.white_x)

/-- The six darts of the two white vertices. -/
private theorem mem_iff (w : WhitePair G x y) {d : H} :
    d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)] ↔
      d ∈ G.vertexOf x ∨ d ∈ G.vertexOf y := by
  rw [w.vertexOf_x hG, w.symm.vertexOf_x hG]
  simp only [List.mem_cons, List.not_mem_nil, or_false, mem_insert, mem_singleton]
  tauto

private theorem forall_mem_white (w : WhitePair G x y) {d : H}
    (hd : d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)]) :
    ¬G.IsBoundaryVertex (G.vertexOf d) ∧ G.colour d = .white := by
  rcases (w.mem_iff hG).1 hd with h | h
  · exact forall_mem_vertexOf_of_white hG w.int_x w.white_x d h
  · exact forall_mem_vertexOf_of_white hG w.int_y w.white_y d h

private theorem forall_mem_black (w : WhitePair G x y) {d : H}
    (hd : d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)]) :
    ¬G.IsBoundaryVertex (G.vertexOf (G.inv d)) ∧ G.colour (G.inv d) = .black :=
  hG.inv_internal_black_of_white (w.forall_mem_white hG hd).1 (w.forall_mem_white hG hd).2

private theorem nodup (w : WhitePair G x y) :
    [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)].Nodup := by
  obtain ⟨hx1, hx2⟩ := w.rot_ne_x hG
  obtain ⟨hy1, hy2⟩ := w.symm.rot_ne_x hG
  have hx3 : G.rot (G.rot x) ≠ G.rot x := fun h => hx1 (G.rot.injective h)
  have hy3 : G.rot (G.rot y) ≠ G.rot y := fun h => hy1 (G.rot.injective h)
  have cross : ∀ a ∈ G.vertexOf x, ∀ a' ∈ G.vertexOf y, a ≠ a' := by
    rintro a ha a' ha' rfl
    exact w.ne ((G.vertexOf_eq_of_mem ha).symm.trans (G.vertexOf_eq_of_mem ha'))
  rw [w.vertexOf_x hG] at cross
  rw [w.symm.vertexOf_x hG] at cross
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at cross
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true]
  refine ⟨⟨hx1.symm, hx2.symm, cross.1.1, cross.1.2.1, cross.1.2.2⟩,
    ⟨hx3.symm, cross.2.1.1, cross.2.1.2.1, cross.2.1.2.2⟩,
    ⟨cross.2.2.1, cross.2.2.2.1, cross.2.2.2.2⟩, ⟨hy1.symm, hy2.symm⟩, ⟨hy3.symm, not_false⟩⟩

/-- The twelve darts of the two white vertices and their reverses are pairwise distinct. -/
private theorem nodup_twelve (w : WhitePair G x y) :
    ([x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)] ++
      [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)), G.inv y, G.inv (G.rot y),
        G.inv (G.rot (G.rot y))]).Nodup := by
  have h := w.nodup hG
  refine List.nodup_append.2 ⟨h, ?_, ?_⟩
  · have := h.map G.inv.injective
    simpa using this
  · intro a ha a' ha' he
    subst he
    have h1 := (w.forall_mem_white hG ha).2
    have hb : ∃ d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)], G.inv d = a := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' ⊢
      rcases ha' with h | h | h | h | h | h <;> exact ⟨_, by simp, h.symm⟩
    obtain ⟨d, hd, rfl⟩ := hb
    rw [(w.forall_mem_black hG hd).2] at h1
    exact Shade.noConfusion h1

/-- The reverse of one of the six darts is a black dart whose reverse is at an interior vertex. -/
private theorem exists_blackDart (w : WhitePair G x y) {d : H}
    (hd : d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)]) :
    ∃ k : G.BlackDart, (k : H) = G.inv d ∧ ¬G.IsBoundaryVertex (G.vertexOf (G.inv k)) := by
  refine ⟨⟨_, mem_blackDarts.2 (w.forall_mem_black hG hd)⟩, rfl, ?_⟩
  change ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.inv d)))
  rw [hG.isNormalPlabicPregraph.inv_inv]
  exact (w.forall_mem_white hG hd).1

/-- The reverse of a leg is not the reverse of one of the six darts. -/
private theorem inv_leg_notMem (w : WhitePair G x y) (i : Fin b) :
    G.inv (G.leg i) ∉ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)), G.inv y,
      G.inv (G.rot y), G.inv (G.rot (G.rot y))] := fun h => by
  have h' : G.leg i ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)] := by
    simpa using h
  exact (w.forall_mem_white hG h').1 (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))

/-- Rewiring by a permutation acting on the six darts as `(x σx σ²y)(σ²x y σy)` and fixing the
other darts of white vertices gives white vertices of three darts. -/
private theorem card_vertexOf_rewire (w : WhitePair G x y) {π : Equiv.Perm H} (p1 : π x = G.rot x)
    (p2 : π (G.rot x) = G.rot (G.rot y)) (p3 : π (G.rot (G.rot y)) = x)
    (p4 : π (G.rot (G.rot x)) = y) (p5 : π y = G.rot y) (p6 : π (G.rot y) = G.rot (G.rot x))
    (hfix : ∀ z, ¬G.IsBoundaryVertex (G.vertexOf z) → G.colour z = .white →
      z ∉ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)] → π z = z)
    (d : H) (hd : ¬G.IsBoundaryVertex (G.vertexOf d)) (hw : G.colour d = .white) :
    ((G.rewire π).vertexOf d).card = 3 := by
  have hx3 := w.rot3_x hG
  have hy3 := w.symm.rot3_x hG
  have hn := w.nodup hG
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hn
  obtain ⟨⟨n12, n13, n14, n15, n16⟩, ⟨n23, n24, n25, n26⟩, ⟨n34, n35, n36⟩, ⟨n45, n46⟩, n56, -⟩ :=
    hn
  have V1 : (G.rewire π).vertexOf x = {x, G.rot (G.rot x), G.rot y} :=
    vertexOf_eq_of_rot_three _ (by rw [rot_rewire_apply, p1]) (by rw [rot_rewire_apply, p4])
      (by rw [rot_rewire_apply, p6, hx3])
  have V2 : (G.rewire π).vertexOf (G.rot x) = {G.rot x, y, G.rot (G.rot y)} :=
    vertexOf_eq_of_rot_three _ (by rw [rot_rewire_apply, p2, hy3]) (by rw [rot_rewire_apply, p5])
      (by rw [rot_rewire_apply, p3])
  have C1 : ((G.rewire π).vertexOf x).card = 3 := by
    rw [V1, card_insert_of_notMem (by simp [n13, n15]), card_pair n35]
  have C2 : ((G.rewire π).vertexOf (G.rot x)).card = 3 := by
    rw [V2, card_insert_of_notMem (by simp [n24, n26]), card_pair n46]
  by_cases hd6 : d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)]
  · have m1 : ∀ e ∈ ({x, G.rot (G.rot x), G.rot y} : Finset H),
        ((G.rewire π).vertexOf e).card = 3 := fun e he => by
      rw [← V1] at he; rwa [RotationSystem.vertexOf_eq_of_mem _ he]
    have m2 : ∀ e ∈ ({G.rot x, y, G.rot (G.rot y)} : Finset H),
        ((G.rewire π).vertexOf e).card = 3 := fun e he => by
      rw [← V2] at he; rwa [RotationSystem.vertexOf_eq_of_mem _ he]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd6
    rcases hd6 with rfl | rfl | rfl | rfl | rfl | rfl
    · exact m1 _ (by simp)
    · exact m2 _ (by simp)
    · exact m1 _ (by simp)
    · exact m2 _ (by simp)
    · exact m1 _ (by simp)
    · exact m2 _ (by simp)
  · have hfix' : ∀ e ∈ G.vertexOf d, π e = e := by
      intro e he
      obtain ⟨he1, he2⟩ := forall_mem_vertexOf_of_white hG hd hw e he
      refine hfix e he1 he2 fun he6 => hd6 ((w.mem_iff hG).2 ?_)
      rcases (w.mem_iff hG).1 he6 with h | h
      · left; rw [← G.vertexOf_eq_of_mem h, G.vertexOf_eq_of_mem he]; exact G.self_mem_vertexOf d
      · right; rw [← G.vertexOf_eq_of_mem h, G.vertexOf_eq_of_mem he]; exact G.self_mem_vertexOf d
    rw [vertexOf_rewire_of_forall hfix']
    exact hG.card_vertexOf_of_white d hd hw

end WhitePair

/-! ### Permutations of white and black darts -/

section Lists

variable {π : Equiv.Perm H} {LW LB : List H}
  (hW : ∀ d ∈ LW, ¬G.IsBoundaryVertex (G.vertexOf d) ∧ G.colour d = .white)
  (hB : ∀ d ∈ LB, ¬G.IsBoundaryVertex (G.vertexOf d) ∧ G.colour d = .black)
  (hπW : ∀ d ∈ LW, π d ∈ LW) (hπB : ∀ d ∈ LB, π d ∈ LB)
  (hfix : ∀ d, d ∉ LW → d ∉ LB → π d = d)

include hW hB hπW hπB hfix

omit hπW hπB in
/-- A permutation preserving a list of white darts and a list of black darts at internal vertices,
and fixing every other dart, fixes the darts at boundary vertices. -/
private theorem perm_eq_of_isBoundaryVertex_of_lists {d : H}
    (hd : G.IsBoundaryVertex (G.vertexOf d)) : π d = d :=
  hfix d (fun h => (hW d h).1 hd) (fun h => (hB d h).1 hd)

/-- A permutation preserving a list of white darts and a list of black darts at internal vertices,
and fixing every other dart, preserves the colours of the darts at internal vertices. -/
private theorem colour_perm_of_lists {d : H} : G.colour (π d) = G.colour d := by
  by_cases h1 : d ∈ LW
  · rw [(hW _ (hπW d h1)).2, (hW d h1).2]
  by_cases h2 : d ∈ LB
  · rw [(hB _ (hπB d h2)).2, (hB d h2).2]
  rw [hfix d h1 h2]

end Lists

/-! ### The setting of urban renewal -/

/-- The setting of urban renewal, written with the darts `x = c̄₁` and `y = c̄₃` of the white
vertices `w = v(c₂)` and `w' = v(c₄)`: then `c₂ = σx`, `e₂ = σ²x`, `c₄ = σy`, `e₄ = σ²y`, and
`π` is `(x σx σ²y)(σ²x y σy)(\overline{σy} x̄ \overline{σ²y})(\overline{σx} ȳ \overline{σ²x})`. -/
private structure UrbanFacts (G : PlabicData H b) (π : Equiv.Perm H) (x y : H) : Prop
    extends WhitePair G x y where
  face_x : G.rot (G.inv (G.rot x)) = G.inv y
  face_y : G.rot (G.inv (G.rot y)) = G.inv x
  p1 : π x = G.rot x
  p2 : π (G.rot x) = G.rot (G.rot y)
  p3 : π (G.rot (G.rot y)) = x
  p4 : π (G.rot (G.rot x)) = y
  p5 : π y = G.rot y
  p6 : π (G.rot y) = G.rot (G.rot x)
  q1 : π (G.inv (G.rot y)) = G.inv x
  q2 : π (G.inv x) = G.inv (G.rot (G.rot y))
  q3 : π (G.inv (G.rot (G.rot y))) = G.inv (G.rot y)
  q4 : π (G.inv (G.rot x)) = G.inv y
  q5 : π (G.inv y) = G.inv (G.rot (G.rot x))
  q6 : π (G.inv (G.rot (G.rot x))) = G.inv (G.rot x)
  fix : ∀ z, z ∉ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)] →
    z ∉ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)), G.inv y, G.inv (G.rot y),
      G.inv (G.rot (G.rot y))] → π z = z

/-- The setting of the normal flip, written with the darts `x = k̄` and `y = \overline{σk}` of the
white vertices `w₁ = v(k̄)` and `w₂ = v(\overline{σk})`: then `a₁ = σx`, `a₂ = σ²x`, `b₁ = σy`,
`b₂ = σ²y`, and `π` is `(x σx σ²y)(σ²x y σy)`. -/
private structure FlipFacts (G : PlabicData H b) (π : Equiv.Perm H) (x y : H) : Prop
    extends WhitePair G x y where
  face_x : G.rot (G.inv x) = G.inv y
  face_y : G.rot (G.inv y) = G.inv x
  p1 : π x = G.rot x
  p2 : π (G.rot x) = G.rot (G.rot y)
  p3 : π (G.rot (G.rot y)) = x
  p4 : π (G.rot (G.rot x)) = y
  p5 : π y = G.rot y
  p6 : π (G.rot y) = G.rot (G.rot x)
  fix : ∀ z, z ∉ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)] → π z = z

/-- A black vertex with two darts is a `2`-cycle of the rotation. -/
private theorem rot_rot_of_card_vertexOf_eq_two {k : H} (h : (G.vertexOf k).card = 2) :
    G.rot (G.rot k) = k ∧ G.rot k ≠ k := by
  have h1 : G.rot k ≠ k := by
    intro h1
    have : G.vertexOf k = {k} := by
      ext e
      rw [RotationSystem.mem_vertexOf, mem_singleton]
      exact ⟨fun he => (he.eq_of_left h1).symm, by rintro rfl; exact Equiv.Perm.SameCycle.refl _ _⟩
    rw [this, card_singleton] at h
    omega
  refine ⟨?_, h1⟩
  by_contra h2
  have h3 : G.rot (G.rot k) ≠ G.rot k := fun h3 => h1 (G.rot.injective h3)
  have hsub : ({k, G.rot k, G.rot (G.rot k)} : Finset H) ⊆ G.vertexOf k := by
    intro e he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact G.self_mem_vertexOf _
    · exact G.rot_mem_vertexOf _
    · have := G.rot_mem_vertexOf (G.rot k)
      rwa [G.vertexOf_rot] at this
  have := card_le_card hsub
  rw [card_insert_of_notMem (by simp [h1.symm, Ne.symm h2]), card_pair h3.symm, h] at this
  omega

namespace UrbanFacts

variable {π : Equiv.Perm H} {x y : H} (hG : G.IsNormalPlabicGraph)

include hG

omit hG in
private theorem perm_mem_white (u : UrbanFacts G π x y) :
    ∀ d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)],
      π d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)] := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [u.p1, u.p2, u.p3, u.p4, u.p5, u.p6]

omit hG in
private theorem perm_mem_inv_black (u : UrbanFacts G π x y) :
    ∀ d ∈ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)), G.inv y, G.inv (G.rot y),
        G.inv (G.rot (G.rot y))],
      π d ∈ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)), G.inv y, G.inv (G.rot y),
        G.inv (G.rot (G.rot y))] := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [u.q1, u.q2, u.q3, u.q4, u.q5, u.q6]

private theorem forall_mem_inv_black (u : UrbanFacts G π x y) :
    ∀ d ∈ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)), G.inv y, G.inv (G.rot y),
        G.inv (G.rot (G.rot y))],
      ¬G.IsBoundaryVertex (G.vertexOf d) ∧ G.colour d = .black := by
  intro d hd
  have : ∃ e ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)], G.inv e = d := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with h | h | h | h | h | h <;> exact ⟨_, by simp, h.symm⟩
  obtain ⟨e, he, rfl⟩ := this
  exact u.toWhitePair.forall_mem_black hG he

private theorem perm_eq (u : UrbanFacts G π x y) {d : H}
    (hd : G.IsBoundaryVertex (G.vertexOf d)) : π d = d :=
  perm_eq_of_isBoundaryVertex_of_lists (fun _ h => u.toWhitePair.forall_mem_white hG h)
    (u.forall_mem_inv_black hG) u.fix hd

private theorem colour_perm (u : UrbanFacts G π x y) {d : H} : G.colour (π d) = G.colour d :=
  colour_perm_of_lists (fun _ h => u.toWhitePair.forall_mem_white hG h)
    (u.forall_mem_inv_black hG) u.perm_mem_white u.perm_mem_inv_black u.fix

private theorem isNormalPlabicPregraph (u : UrbanFacts G π x y) :
    (G.rewire π).IsNormalPlabicPregraph :=
  isNormalPlabicPregraph_rewire hG (fun _ h => u.perm_eq hG h) (fun _ _ => u.colour_perm hG)
    (u.toWhitePair.card_vertexOf_rewire hG u.p1 u.p2 u.p3 u.p4 u.p5 u.p6
      fun z _ hw hz => u.fix z hz fun hz' => by
        have := (u.forall_mem_inv_black hG z hz').2
        rw [hw] at this
        exact Shade.noConfusion this)

end UrbanFacts

namespace FlipFacts

variable {π : Equiv.Perm H} {x y : H} (hG : G.IsNormalPlabicGraph)

include hG

omit hG in
private theorem perm_mem_white (u : FlipFacts G π x y) :
    ∀ d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)],
      π d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)] := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [u.p1, u.p2, u.p3, u.p4, u.p5, u.p6]

private theorem perm_eq (u : FlipFacts G π x y) {d : H}
    (hd : G.IsBoundaryVertex (G.vertexOf d)) : π d = d :=
  perm_eq_of_isBoundaryVertex_of_lists (LB := []) (fun _ h => u.toWhitePair.forall_mem_white hG h)
    (by simp) (fun d h _ => u.fix d h) hd

private theorem colour_perm (u : FlipFacts G π x y) {d : H} : G.colour (π d) = G.colour d :=
  colour_perm_of_lists (LB := []) (fun _ h => u.toWhitePair.forall_mem_white hG h)
    (by simp) u.perm_mem_white (by simp) (fun d h _ => u.fix d h)

private theorem isNormalPlabicPregraph (u : FlipFacts G π x y) :
    (G.rewire π).IsNormalPlabicPregraph :=
  isNormalPlabicPregraph_rewire hG (fun _ h => u.perm_eq hG h) (fun _ _ => u.colour_perm hG)
    (u.toWhitePair.card_vertexOf_rewire hG u.p1 u.p2 u.p3 u.p4 u.p5 u.p6
      fun z _ _ hz => u.fix z hz)

end FlipFacts

omit [Fintype H] [DecidableEq H] in
private theorem squareCorner_one_eq (c : H) : G.squareCorner c 1 = G.rot (G.inv c) := by
  simp [squareCorner, G.facePerm_apply]

omit [Fintype H] [DecidableEq H] in
private theorem squareCorner_three_eq (c : H) :
    G.squareCorner c 3 = G.rot (G.inv (G.squareCorner c 2)) := by
  change (G.facePerm ^ 3) c = G.rot (G.inv ((G.facePerm ^ 2) c))
  rw [pow_succ', Equiv.Perm.mul_apply, G.facePerm_apply]

/-- The setting of urban renewal at the face through `c`, written with `x = c̄₁` and `y = c̄₃`. -/
private theorem IsUrbanRenewalFace.urbanFacts (hG : G.IsNormalPlabicGraph) {c : H}
    (hc : G.IsUrbanRenewalFace c) :
    UrbanFacts G (G.urbanRenewalPerm c) (G.inv c) (G.inv (G.squareCorner c 2)) := by
  have hinv := hG.inv_involutive
  have e1 := squareCorner_one_eq (G := G) c
  have e2 : G.squareCorner c 2 = G.rot (G.inv (G.squareCorner c 1)) := by
    change (G.facePerm ^ 2) c = G.rot (G.inv ((G.facePerm ^ 1) c))
    rw [pow_succ', Equiv.Perm.mul_apply, G.facePerm_apply]
  have e3 := squareCorner_three_eq (G := G) c
  have e4 : G.rot (G.inv (G.squareCorner c 3)) = c := by
    have := hc.facePerm_pow_four
    rwa [pow_succ', Equiv.Perm.mul_apply, G.facePerm_apply] at this
  have h := hc.urbanRenewalPerm_apply hG
  dsimp only at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have int_x : ¬G.IsBoundaryVertex (G.vertexOf (G.inv c)) := by
    rw [← G.vertexOf_rot, ← e1]; exact hc.not_isBoundaryVertex 1
  have int_y : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.squareCorner c 2))) := by
    rw [← G.vertexOf_rot, ← e3]; exact hc.not_isBoundaryVertex 3
  exact
  { int_x := int_x
    white_x := by rw [← hG.colour_rot _ int_x, ← e1]; exact hc.colour_squareCorner_one
    int_y := int_y
    white_y := by rw [← hG.colour_rot _ int_y, ← e3]; exact hc.colour_squareCorner_three
    ne := by
      rw [← G.vertexOf_rot (G.inv c), ← G.vertexOf_rot (G.inv (G.squareCorner c 2)), ← e1, ← e3]
      exact hc.vertexOf_ne
    face_x := by rw [← e1, hinv (G.squareCorner c 2)]; exact e2.symm
    face_y := by rwa [← e3, hinv c]
    p1 := by rwa [← e1]
    p2 := by rwa [← e1, ← e3]
    p3 := by rwa [← e3]
    p4 := by rwa [← e1]
    p5 := by rwa [← e3]
    p6 := by rwa [← e3, ← e1]
    q1 := by rwa [← e3, hinv c]
    q2 := by rwa [hinv c, ← e3]
    q3 := by rwa [← e3]
    q4 := by rwa [← e1, hinv (G.squareCorner c 2)]
    q5 := by rwa [hinv (G.squareCorner c 2), ← e1]
    q6 := by rwa [← e1]
    fix := by
      intro z hz1 hz2
      apply urbanRenewalPerm_apply_of_notMem
      rw [e1, e3]
      rw [hinv c, hinv (G.squareCorner c 2)] at hz2
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz1 hz2 ⊢
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hz1
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hz2
      exact ⟨a1, a2, a6, a3, a4, a5, b5, b1, b6, b2, b4, b3⟩ }

/-- The setting of the normal flip at `u = {k, σk}`, written with `x = k̄` and
`y = \overline{σk}`. -/
private theorem IsNormalFlipVertex.flipFacts (hG : G.IsNormalPlabicGraph) {k : H}
    (hk : G.IsNormalFlipVertex k) :
    FlipFacts G (G.normalFlipPerm k) (G.inv k) (G.inv (G.rot k)) := by
  have hinv := hG.inv_involutive
  have h := hk.normalFlipPerm_apply hG
  dsimp only at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact
  { int_x := hk.not_isBoundaryVertex_inv
    white_x := hk.colour_inv
    int_y := hk.not_isBoundaryVertex_inv_rot
    white_y := hk.colour_inv_rot
    ne := hk.vertexOf_inv_ne
    face_x := by rw [hinv k, hinv (G.rot k)]
    face_y := by
      rw [hinv (G.rot k), hinv k]; exact (rot_rot_of_card_vertexOf_eq_two hk.card_vertexOf).1
    p1 := h1
    p2 := h2
    p3 := h3
    p4 := h4
    p5 := h5
    p6 := h6
    fix := by
      intro z hz
      apply normalFlipPerm_apply_of_notMem
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz ⊢
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hz
      exact ⟨a1, a2, a6, a3, a4, a5⟩ }

/-! ### Urban renewal and the normal flip give normal plabic pregraphs -/

/-- **Urban renewal gives a normal plabic pregraph**: for a face `c` with `G.IsUrbanRenewalFace c`,
the urban renewal of a normal plabic graph `G` is a normal plabic pregraph. -/
@[cluster_algebras "lem_urban_renewal_pregraph"]
theorem IsUrbanRenewalFace.isNormalPlabicPregraph_urbanRenewal (hG : G.IsNormalPlabicGraph)
    {c : H} (hc : G.IsUrbanRenewalFace c) : (G.urbanRenewal c).IsNormalPlabicPregraph :=
  (hc.urbanFacts hG).isNormalPlabicPregraph hG

/-- The urban renewal has the boundary vertices, the legs and the labelling of `G`. -/
@[cluster_algebras "lem_urban_renewal_pregraph"]
theorem IsUrbanRenewalFace.boundaryVertices_urbanRenewal (hG : G.IsNormalPlabicGraph) {c : H}
    (hc : G.IsUrbanRenewalFace c) :
    (G.urbanRenewal c).boundaryVertices = G.boundaryVertices ∧
      ∀ i, (G.urbanRenewal c).leg i = G.leg i ∧ (G.urbanRenewal c).bvertex i = G.bvertex i := by
  have u := hc.urbanFacts hG
  refine ⟨boundaryVertices_rewire hG (fun _ h => u.perm_eq hG h) (fun _ _ => u.colour_perm hG),
    fun i => ⟨rfl, vertexOf_rewire_of_isBoundaryVertex (fun _ h => u.perm_eq hG h)
      (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))⟩⟩

/-- In the urban renewal, a dart lies at an internal vertex exactly when it does in `G`, and then
its vertex has the colour it has in `G`. -/
@[cluster_algebras "lem_urban_renewal_pregraph"]
theorem IsUrbanRenewalFace.colour_urbanRenewal (hG : G.IsNormalPlabicGraph) {c : H}
    (hc : G.IsUrbanRenewalFace c) (d : H) :
    ((G.urbanRenewal c).IsBoundaryVertex ((G.urbanRenewal c).vertexOf d) ↔
        G.IsBoundaryVertex (G.vertexOf d)) ∧
      (¬G.IsBoundaryVertex (G.vertexOf d) → (G.urbanRenewal c).colour d = G.colour d) := by
  have u := hc.urbanFacts hG
  exact ⟨isBoundaryVertex_rewire_iff hG (fun _ h => u.perm_eq hG h)
    (fun _ _ => u.colour_perm hG) d, fun hd => colour_rewire_of_not_isBoundaryVertex hG
      (fun _ h => u.perm_eq hG h) (fun _ _ => u.colour_perm hG) hd⟩

/-- **A normal flip gives a normal plabic pregraph**: for a dart `k` with `G.IsNormalFlipVertex k`,
the normal flip of a normal plabic graph `G` at `u = {k, σk}` is a normal plabic pregraph. -/
@[cluster_algebras "lem_normal_flip_pregraph"]
theorem IsNormalFlipVertex.isNormalPlabicPregraph_normalFlip (hG : G.IsNormalPlabicGraph)
    {k : H} (hk : G.IsNormalFlipVertex k) : (G.normalFlip k).IsNormalPlabicPregraph :=
  (hk.flipFacts hG).isNormalPlabicPregraph hG

/-- The normal flip has the boundary vertices, the legs and the labelling of `G`. -/
@[cluster_algebras "lem_normal_flip_pregraph"]
theorem IsNormalFlipVertex.boundaryVertices_normalFlip (hG : G.IsNormalPlabicGraph) {k : H}
    (hk : G.IsNormalFlipVertex k) :
    (G.normalFlip k).boundaryVertices = G.boundaryVertices ∧
      ∀ i, (G.normalFlip k).leg i = G.leg i ∧ (G.normalFlip k).bvertex i = G.bvertex i := by
  have u := hk.flipFacts hG
  refine ⟨boundaryVertices_rewire hG (fun _ h => u.perm_eq hG h) (fun _ _ => u.colour_perm hG),
    fun i => ⟨rfl, vertexOf_rewire_of_isBoundaryVertex (fun _ h => u.perm_eq hG h)
      (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))⟩⟩

/-- In the normal flip, a dart lies at an internal vertex exactly when it does in `G`, and then its
vertex has the colour it has in `G`. -/
@[cluster_algebras "lem_normal_flip_pregraph"]
theorem IsNormalFlipVertex.colour_normalFlip (hG : G.IsNormalPlabicGraph) {k : H}
    (hk : G.IsNormalFlipVertex k) (d : H) :
    ((G.normalFlip k).IsBoundaryVertex ((G.normalFlip k).vertexOf d) ↔
        G.IsBoundaryVertex (G.vertexOf d)) ∧
      (¬G.IsBoundaryVertex (G.vertexOf d) → (G.normalFlip k).colour d = G.colour d) := by
  have u := hk.flipFacts hG
  exact ⟨isBoundaryVertex_rewire_iff hG (fun _ h => u.perm_eq hG h)
    (fun _ _ => u.colour_perm hG) d, fun hd => colour_rewire_of_not_isBoundaryVertex hG
      (fun _ h => u.perm_eq hG h) (fun _ _ => u.colour_perm hG) hd⟩

/-- The vertices of the normal flip other than the two new white vertices are those of `G`: every
vertex of `G` other than `w₁ = v(k̄)` and `w₂ = v(\overline{σk})`, in particular every black and
every boundary vertex, is a vertex of the normal flip, with the same rotation. -/
@[cluster_algebras "lem_normal_flip_pregraph"]
theorem IsNormalFlipVertex.vertexOf_normalFlip (hG : G.IsNormalPlabicGraph) {k : H}
    (hk : G.IsNormalFlipVertex k) {d : H} (h₁ : G.vertexOf d ≠ G.vertexOf (G.inv k))
    (h₂ : G.vertexOf d ≠ G.vertexOf (G.inv (G.rot k))) :
    (G.normalFlip k).vertexOf d = G.vertexOf d ∧
      ∀ e ∈ G.vertexOf d, (G.normalFlip k).rot e = G.rot e := by
  have u := hk.flipFacts hG
  have hfix : ∀ e ∈ G.vertexOf d, G.normalFlipPerm k e = e := by
    intro e he
    refine u.fix e fun he' => ?_
    rcases (u.toWhitePair.mem_iff hG).1 he' with h | h
    · exact h₁ ((G.vertexOf_eq_of_mem he).symm.trans (G.vertexOf_eq_of_mem h))
    · exact h₂ ((G.vertexOf_eq_of_mem he).symm.trans (G.vertexOf_eq_of_mem h))
  exact ⟨vertexOf_rewire_of_forall hfix, fun e he => by
    change G.rot (G.normalFlipPerm k e) = G.rot e
    rw [hfix e he]⟩

/-- The two new white vertices of the normal flip: with `a₁ = σ(k̄)`, `a₂ = σ(a₁)`,
`b₁ = σ(\overline{σk})` and `b₂ = σ(b₁)`, the rotation of the normal flip has the cycles
`(k̄, a₂, b₁)` and `(\overline{σk}, b₂, a₁)`. -/
@[cluster_algebras "lem_normal_flip_pregraph"]
theorem IsNormalFlipVertex.rot_normalFlip (hG : G.IsNormalPlabicGraph) {k : H}
    (hk : G.IsNormalFlipVertex k) :
    (G.normalFlip k).rot (G.inv k) = G.rot (G.rot (G.inv k)) ∧
      (G.normalFlip k).rot (G.rot (G.rot (G.inv k))) = G.rot (G.inv (G.rot k)) ∧
      (G.normalFlip k).rot (G.rot (G.inv (G.rot k))) = G.inv k ∧
      (G.normalFlip k).rot (G.inv (G.rot k)) = G.rot (G.rot (G.inv (G.rot k))) ∧
      (G.normalFlip k).rot (G.rot (G.rot (G.inv (G.rot k)))) = G.rot (G.inv k) ∧
      (G.normalFlip k).rot (G.rot (G.inv k)) = G.inv (G.rot k) := by
  have u := hk.flipFacts hG
  have hx3 := u.toWhitePair.rot3_x hG
  have hy3 := u.toWhitePair.symm.rot3_x hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> change G.rot (G.normalFlipPerm k _) = _
  · rw [u.p1]
  · rw [u.p4]
  · rw [u.p6, hx3]
  · rw [u.p5]
  · rw [u.p3]
  · rw [u.p2, hy3]

/-! ### Computations in the triple diagram of a normal plabic pregraph -/

namespace IsNormalPlabicPregraph

variable (hP : G.IsNormalPlabicPregraph)

include hP

private theorem tripleRot_plus_eq' {k : G.BlackDart}
    (h : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k))) : hP.tripleRot (.plus k) = .minus k :=
  hP.tripleRot_plus_of_none (hP.legIndex_eq_none_of_internal h)

private theorem tripleRot_minus_eq' {k k' : G.BlackDart}
    (h : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k))) (hk' : (k' : H) = G.inv (G.rot (G.inv k))) :
    hP.tripleRot (.minus k) = .plus k' := by
  rw [hP.tripleRot_minus_of_none (hP.legIndex_eq_none_of_internal h)]
  congr 1
  exact Subtype.ext hk'.symm

private theorem tripleInv_plus_eq' {k k' : G.BlackDart} (hk' : (k' : H) = G.rot k) :
    hP.tripleInv (.plus k) = .minus k' := by
  rw [tripleInv_plus]
  congr 1
  exact Subtype.ext hk'.symm

private theorem tripleInv_minus_eq' {k k' : G.BlackDart} (hk' : (k' : H) = G.rot.symm k) :
    hP.tripleInv (.minus k) = .plus k' := by
  rw [tripleInv_minus]
  congr 1
  exact Subtype.ext hk'.symm

private theorem facePerm_plus_eq' {k k' : G.BlackDart}
    (h : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.rot k))))
    (hk' : (k' : H) = G.inv (G.rot (G.inv (G.rot k)))) :
    (G.tripleOfNormal hP).facePerm (.plus k) = .plus k' := by
  rw [facePerm_tripleOfNormal_plus]
  exact hP.tripleRot_minus_eq' (k := ⟨G.rot k, hP.rot_mem_blackDarts k.2⟩) h hk'

private theorem facePerm_minus_eq' {k k' : G.BlackDart}
    (h : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k'))) (hk' : (k' : H) = G.rot.symm k) :
    (G.tripleOfNormal hP).facePerm (.minus k) = .minus k' := by
  rw [facePerm_tripleOfNormal_minus,
    show (⟨G.rot.symm k, hP.rot_symm_mem_blackDarts k.2⟩ : G.BlackDart) = k' from
      Subtype.ext hk'.symm]
  exact hP.tripleRot_plus_eq' h

/-- The vertex of `X(G)` through `x⁻_k` is that through `x⁺_k`, when `v(k̄)` is internal. -/
private theorem vertexOf_minus_eq' {k : G.BlackDart}
    (h : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k))) :
    (G.tripleOfNormal hP).vertexOf (.minus k) = (G.tripleOfNormal hP).vertexOf (.plus k) := by
  rw [← hP.tripleRot_plus_eq' h]
  exact RotationSystem.vertexOf_rot _ _

/-- The dart `x⁺_{k'}` lies at the triple point of `x⁺_k` exactly when `k̄'` and `k̄` lie at the
same (white) vertex of `G`. -/
private theorem plus_mem_vertexOf_plus_iff {k k' : G.BlackDart}
    (h : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k))) :
    (.plus k' : G.TripleDart) ∈ (G.tripleOfNormal hP).vertexOf (.plus k) ↔
      G.vertexOf (G.inv k') = G.vertexOf (G.inv k) := by
  have hl := hP.legIndex_eq_none_of_internal h
  have hw := hP.colour_inv k.2 hl
  have hcard := hP.card_vertexOf_of_white _ h hw
  have hV := vertexOf_eq_of_card_vertexOf_eq_three hcard
  rw [hP.vertexOf_tripleOfNormal_plus_of_none hl]
  simp only [mem_insert, mem_singleton, TripleOfNormalDart.plus.injEq, reduceCtorEq, or_false,
    false_or]
  constructor
  · rintro (rfl | rfl | rfl)
    · rfl
    · rw [coe_psi, hP.inv_inv, G.vertexOf_rot]
    · rw [coe_psi, coe_psi, hP.inv_inv, hP.inv_inv, G.vertexOf_rot, G.vertexOf_rot]
  · intro he
    have hm : G.inv k' ∈ G.vertexOf (G.inv k) := he ▸ G.self_mem_vertexOf _
    rw [hV] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact Or.inl (Subtype.ext (G.inv.injective hm))
    · refine Or.inr (Or.inl (Subtype.ext ?_))
      rw [coe_psi, ← hm, hP.inv_inv]
    · refine Or.inr (Or.inr (Subtype.ext ?_))
      rw [coe_psi, coe_psi, hP.inv_inv, ← hm, hP.inv_inv]

end IsNormalPlabicPregraph

/-! ### The digons of `X(G)` -/

namespace TripleData

variable {K : Type} [Fintype K] [DecidableEq K] {X : TripleData K b}

/-- Two darts outside `B`, at distinct vertices, exchanged by `φ`, form a digon. -/
private theorem isDigon_of_facePerm {d₁ d₂ : K} (h₁ : X.facePerm d₁ = d₂)
    (h₂ : X.facePerm d₂ = d₁) (hb₁ : d₁ ∉ X.bdry) (hb₂ : d₂ ∉ X.bdry)
    (hv : X.vertexOf d₁ ≠ X.vertexOf d₂) :
    X.faceOf d₁ = {d₁, d₂} ∧ X.IsDigon (X.faceOf d₁) := by
  have hf : X.faceOf d₁ = {d₁, d₂} := by
    have h2 : (X.facePerm ^ 2) d₁ = d₁ := by simp [pow_succ, h₁, h₂]
    ext e
    rw [RotationSystem.mem_faceOf]
    simp only [mem_insert, mem_singleton]
    constructor
    · intro h
      obtain ⟨j, hj, rfl⟩ := exists_lt_pow_eq_of_sameCycle (by norm_num) h2 h
      interval_cases j <;> simp [h₁]
    · rintro (rfl | rfl)
      · exact Equiv.Perm.SameCycle.refl _ _
      · exact ⟨1, by simp [h₁]⟩
  refine ⟨hf, X.mem_internalFaces.2 ⟨X.mem_faces.2 ⟨fun he => hb₁ ?_,
    X.faceOf_mem_faceOrbits d₁⟩, ?_⟩, d₁, by rw [hf, h₁], by rw [h₁]; exact hv⟩
  · exact X.exterior_subset_bdry (he ▸ X.self_mem_faceOf d₁)
  · rw [hf]
    refine disjoint_left.2 fun e he => ?_
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl <;> assumption

/-- A digon is the orbit `f(d₁)` of each of its darts `d₁`. -/
private theorem IsDigon.exists_eq_faceOf {δ : Finset K} (hδ : X.IsDigon δ) :
    ∃ d₁, δ = X.faceOf d₁ ∧ δ = {d₁, X.facePerm d₁} := by
  obtain ⟨hint, d₁, rfl, -⟩ := hδ
  obtain ⟨e, he⟩ := X.mem_faceOrbits.1 (X.mem_faces.1 (X.mem_internalFaces.1 hint).1).2
  refine ⟨d₁, ?_, rfl⟩
  rw [X.faceOf_eq_of_mem (d := e) (e := d₁) (by rw [he]; exact mem_insert_self _ _), he]

end TripleData

/-- The corners of the face through `σk`, when `x⁺_k` and `x⁺_{k'}` are exchanged by `φ`. -/
private theorem squareCorner_rot_of_inv_rot_inv_rot (hG : G.IsNormalPlabicGraph) {k k' : H}
    (hkk : G.inv (G.rot (G.inv (G.rot k'))) = k) (hkk' : G.inv (G.rot (G.inv (G.rot k))) = k') :
    G.squareCorner (G.rot k) 1 = G.inv k' ∧ G.squareCorner (G.rot k) 2 = G.rot k' ∧
      G.squareCorner (G.rot k) 3 = G.inv k ∧ (G.facePerm ^ 4) (G.rot k) = G.rot k := by
  have hinv := hG.inv_involutive
  set c := G.rot k
  have sq1 : G.squareCorner c 1 = G.inv k' := by
    rw [squareCorner_one_eq, ← hkk', hinv]
  have sq2 : G.squareCorner c 2 = G.rot k' := by
    change (G.facePerm ^ 2) c = _
    rw [pow_succ', Equiv.Perm.mul_apply, pow_one]
    change G.facePerm (G.squareCorner c 1) = _
    rw [sq1, G.facePerm_apply, hinv]
  have sq3 : G.squareCorner c 3 = G.inv k := by
    rw [squareCorner_three_eq, sq2, ← hkk, hinv]
  refine ⟨sq1, sq2, sq3, ?_⟩
  rw [pow_succ', Equiv.Perm.mul_apply]
  change G.facePerm (G.squareCorner c 3) = c
  rw [sq3, G.facePerm_apply, hinv]

/-- The face through `σk` is an urban renewal face, when `x⁺_k` and `x⁺_{k'}` are exchanged by `φ`
and lie at distinct vertices of `X(G)`. -/
private theorem isUrbanRenewalFace_rot (hG : G.IsNormalPlabicGraph) {k k' : G.BlackDart}
    (hlk : G.legIndex k = none) (hlk' : G.legIndex k' = none)
    (hkk : G.inv (G.rot (G.inv (G.rot k'))) = k) (hkk' : G.inv (G.rot (G.inv (G.rot k))) = k')
    (hv : (G.tripleOfNormal hG.isNormalPlabicPregraph).vertexOf (.plus k) ≠
      (G.tripleOfNormal hG.isNormalPlabicPregraph).vertexOf (.plus k')) :
    G.IsUrbanRenewalFace (G.rot k) := by
  set P := hG.isNormalPlabicPregraph
  obtain ⟨sq1, sq2, sq3, sq4⟩ := squareCorner_rot_of_inv_rot_inv_rot hG hkk hkk'
  set c := G.rot k
  have I0 : ¬G.IsBoundaryVertex (G.vertexOf c) :=
    (mem_blackDarts.1 (P.rot_mem_blackDarts k.2)).1
  have I1 : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k')) := P.not_isBoundaryVertex_inv k'.2 hlk'
  have I2 : ¬G.IsBoundaryVertex (G.vertexOf (G.rot k')) :=
    (mem_blackDarts.1 (P.rot_mem_blackDarts k'.2)).1
  have I3 : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k)) := P.not_isBoundaryVertex_inv k.2 hlk
  have Iall : ∀ j : Fin 4, ¬G.IsBoundaryVertex (G.vertexOf (G.squareCorner c j)) := by
    intro j
    fin_cases j
    · simpa [squareCorner_zero] using I0
    · simpa [sq1] using I1
    · simpa [sq2] using I2
    · simpa [sq3] using I3
  have hcB : c ∉ G.bdry := notMem_bdry_of_mem_vertexOf I0 (G.self_mem_vertexOf c)
  have hface : G.faceOf c ∈ G.internalFaces := by
    refine G.mem_internalFaces.2 ⟨G.mem_faces.2 ⟨fun he => hcB ?_,
      G.faceOf_mem_faceOrbits c⟩, disjoint_left.2 fun e he heB => ?_⟩
    · exact G.exterior_subset_bdry (he ▸ G.self_mem_faceOf c)
    · rw [RotationSystem.mem_faceOf] at he
      obtain ⟨j, hj, rfl⟩ := exists_lt_pow_eq_of_sameCycle (by norm_num) sq4 he
      exact notMem_bdry_of_mem_vertexOf (Iall ⟨j, hj⟩) (G.self_mem_vertexOf _) heB
  exact
    { faceOf_mem_internalFaces := hface
      facePerm_pow_four := sq4
      not_isBoundaryVertex := Iall
      colour_squareCorner_zero := by
        rw [squareCorner_zero]
        exact (mem_blackDarts.1 (P.rot_mem_blackDarts k.2)).2
      colour_squareCorner_one := by rw [sq1]; exact P.colour_inv k'.2 hlk'
      colour_squareCorner_two := by
        rw [sq2]
        exact (mem_blackDarts.1 (P.rot_mem_blackDarts k'.2)).2
      colour_squareCorner_three := by rw [sq3]; exact P.colour_inv k.2 hlk
      vertexOf_ne := by
        rw [sq1, sq3]
        intro heq
        have hm := (P.plus_mem_vertexOf_plus_iff (k := k) (k' := k') I3).2 heq
        exact hv (RotationSystem.vertexOf_eq_of_mem _ hm).symm }

/-- A digon of `X(G)` through a dart `x⁺_k` comes from an urban renewal face of `G`. -/
private theorem exists_isUrbanRenewalFace_of_isDigon_plus (hG : G.IsNormalPlabicGraph)
    (k : G.BlackDart)
    (hb₂ : (G.tripleOfNormal hG.isNormalPlabicPregraph).facePerm (.plus k) ∉
      (G.tripleOfNormal hG.isNormalPlabicPregraph).bdry)
    (hφφ : (G.tripleOfNormal hG.isNormalPlabicPregraph).facePerm
      ((G.tripleOfNormal hG.isNormalPlabicPregraph).facePerm (.plus k)) = .plus k)
    (hv : (G.tripleOfNormal hG.isNormalPlabicPregraph).vertexOf (.plus k) ≠
      (G.tripleOfNormal hG.isNormalPlabicPregraph).vertexOf
        ((G.tripleOfNormal hG.isNormalPlabicPregraph).facePerm (.plus k))) :
    ∃ c, G.IsUrbanRenewalFace c ∧ ∃ k₁ k₂ : G.BlackDart,
      (k₁ : H) = G.inv (G.squareCorner c 3) ∧ (k₂ : H) = G.inv (G.squareCorner c 1) ∧
        ({.plus k, (G.tripleOfNormal hG.isNormalPlabicPregraph).facePerm (.plus k)} :
          Finset G.TripleDart) = {.plus k₁, .plus k₂} := by
  set P := hG.isNormalPlabicPregraph
  set X := G.tripleOfNormal P
  have hinv := hG.inv_involutive
  have e1 : X.facePerm (.plus k) = P.tripleRot (.minus ⟨G.rot k, P.rot_mem_blackDarts k.2⟩) :=
    rfl
  rcases hl : G.legIndex (G.rot k) with _ | i
  swap
  · rw [e1, P.tripleRot_minus_of_some (k := ⟨G.rot k, _⟩) hl] at hb₂
    exact absurd ((P.mem_tripleOfNormal_bdry).2 rfl) hb₂
  set k' := P.psi ⟨G.rot k, P.rot_mem_blackDarts k.2⟩ hl
  have hφ : X.facePerm (.plus k) = .plus k' := by
    rw [e1, P.tripleRot_minus_of_none (k := ⟨G.rot k, _⟩) hl]
  rw [hφ] at hφφ hv ⊢
  have e2 : X.facePerm (.plus k') =
      P.tripleRot (.minus ⟨G.rot k', P.rot_mem_blackDarts k'.2⟩) := rfl
  rcases hl' : G.legIndex (G.rot k') with _ | i
  swap
  · rw [e2, P.tripleRot_minus_of_some (k := ⟨G.rot k', _⟩) hl'] at hφφ
    exact absurd hφφ (by simp)
  rw [e2, P.tripleRot_minus_of_none (k := ⟨G.rot k', _⟩) hl',
    TripleOfNormalDart.plus.injEq] at hφφ
  have hkk : G.inv (G.rot (G.inv (G.rot k'))) = k := congrArg Subtype.val hφφ
  have hkk' : G.inv (G.rot (G.inv (G.rot k))) = k' := rfl
  obtain ⟨sq1, -, sq3, -⟩ := squareCorner_rot_of_inv_rot_inv_rot hG hkk hkk'
  exact ⟨G.rot k, isUrbanRenewalFace_rot hG (hφφ ▸ P.legIndex_psi _ hl') (P.legIndex_psi _ hl)
    hkk hkk' hv, k, k', by rw [sq3, hinv], by rw [sq1, hinv], rfl⟩

/-- A black vertex `{k, m}` of `G` with `m = σ⁻¹k = σk`, whose darts `x⁻_k`, `x⁻_m` lie at
distinct vertices of `X(G)`, is a normal flip vertex. -/
private theorem isNormalFlipVertex_of_rot_symm (hG : G.IsNormalPlabicGraph) {k m : G.BlackDart}
    (hm : (m : H) = G.rot.symm k) (hkk : G.rot.symm (G.rot.symm k) = k)
    (hl : G.legIndex (G.rot.symm k) = none) (hlk : G.legIndex k = none)
    (hv : (G.tripleOfNormal hG.isNormalPlabicPregraph).vertexOf (.minus k) ≠
      (G.tripleOfNormal hG.isNormalPlabicPregraph).vertexOf (.minus m)) :
    G.IsNormalFlipVertex k ∧ (m : H) = G.rot k := by
  set P := hG.isNormalPlabicPregraph
  have hrr : G.rot (G.rot k) = k := by
    conv_lhs => rw [← hkk]
    simp
  have hsym : G.rot.symm k = G.rot k := by
    rw [Equiv.symm_apply_eq, hrr]
  have hm' : (m : H) = G.rot k := hm.trans hsym
  have hlk' : G.legIndex (G.rot k) = none := by rwa [← hsym]
  have hne : G.rot k ≠ k := by
    intro h
    apply hv
    rw [show m = k from Subtype.ext (by rw [hm', h])]
  have hk2 : G.vertexOf (k : H) = {(k : H), G.rot k} := by
    ext e
    rw [RotationSystem.mem_vertexOf]
    simp only [mem_insert, mem_singleton]
    constructor
    · intro h
      obtain ⟨j, hj, rfl⟩ := exists_lt_pow_eq_of_sameCycle (m := 2) (by norm_num)
        (by simp [pow_succ, hrr]) h
      interval_cases j <;> simp
    · rintro (rfl | rfl)
      · exact Equiv.Perm.SameCycle.refl _ _
      · exact ⟨1, by simp⟩
  refine ⟨{ not_isBoundaryVertex := (mem_blackDarts.1 k.2).1
            colour_eq := (mem_blackDarts.1 k.2).2
            card_vertexOf := by rw [hk2, card_pair hne.symm]
            not_isBoundaryVertex_inv := P.not_isBoundaryVertex_inv k.2 hlk
            colour_inv := P.colour_inv k.2 hlk
            not_isBoundaryVertex_inv_rot :=
              P.not_isBoundaryVertex_inv (P.rot_mem_blackDarts k.2) hlk'
            colour_inv_rot := P.colour_inv (P.rot_mem_blackDarts k.2) hlk'
            vertexOf_inv_ne := ?_ }, hm'⟩
  intro heq
  have I : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k)) := P.not_isBoundaryVertex_inv k.2 hlk
  have Im : ¬G.IsBoundaryVertex (G.vertexOf (G.inv m)) := by
    rw [hm']
    exact P.not_isBoundaryVertex_inv (P.rot_mem_blackDarts k.2) hlk'
  have hm := (P.plus_mem_vertexOf_plus_iff (k := k) (k' := m) I).2 (by rw [hm']; exact heq.symm)
  apply hv
  rw [P.vertexOf_minus_eq' I, P.vertexOf_minus_eq' Im, RotationSystem.vertexOf_eq_of_mem _ hm]

/-- A digon of `X(G)` through a dart `x⁻_k` comes from a normal flip vertex of `G`. -/
private theorem exists_isNormalFlipVertex_of_isDigon_minus (hG : G.IsNormalPlabicGraph)
    (k : G.BlackDart)
    (hb₂ : (G.tripleOfNormal hG.isNormalPlabicPregraph).facePerm (.minus k) ∉
      (G.tripleOfNormal hG.isNormalPlabicPregraph).bdry)
    (hφφ : (G.tripleOfNormal hG.isNormalPlabicPregraph).facePerm
      ((G.tripleOfNormal hG.isNormalPlabicPregraph).facePerm (.minus k)) = .minus k)
    (hv : (G.tripleOfNormal hG.isNormalPlabicPregraph).vertexOf (.minus k) ≠
      (G.tripleOfNormal hG.isNormalPlabicPregraph).vertexOf
        ((G.tripleOfNormal hG.isNormalPlabicPregraph).facePerm (.minus k))) :
    ∃ k', G.IsNormalFlipVertex k' ∧ ∃ k₁ k₂ : G.BlackDart, (k₁ : H) = k' ∧
      (k₂ : H) = G.rot k' ∧
        ({.minus k, (G.tripleOfNormal hG.isNormalPlabicPregraph).facePerm (.minus k)} :
          Finset G.TripleDart) = {.minus k₁, .minus k₂} := by
  set P := hG.isNormalPlabicPregraph
  set X := G.tripleOfNormal P
  have e1 : X.facePerm (.minus k) =
      P.tripleRot (.plus ⟨G.rot.symm k, P.rot_symm_mem_blackDarts k.2⟩) := rfl
  rcases hl : G.legIndex (G.rot.symm k) with _ | i
  swap
  · rw [e1, P.tripleRot_plus_of_some (k := ⟨G.rot.symm k, _⟩) hl] at hb₂
    exact absurd ((P.mem_tripleOfNormal_bdry).2 rfl) hb₂
  set m : G.BlackDart := ⟨G.rot.symm k, P.rot_symm_mem_blackDarts k.2⟩
  have hφ : X.facePerm (.minus k) = .minus m := by
    rw [e1, P.tripleRot_plus_of_none (k := ⟨G.rot.symm k, _⟩) hl]
  rw [hφ] at hφφ hv ⊢
  have e2 : X.facePerm (.minus m) =
      P.tripleRot (.plus ⟨G.rot.symm m, P.rot_symm_mem_blackDarts m.2⟩) := rfl
  rcases hl' : G.legIndex (G.rot.symm m) with _ | i
  swap
  · rw [e2, P.tripleRot_plus_of_some (k := ⟨G.rot.symm m, _⟩) hl'] at hφφ
    exact absurd hφφ (by simp)
  rw [e2, P.tripleRot_plus_of_none (k := ⟨G.rot.symm m, _⟩) hl',
    TripleOfNormalDart.minus.injEq] at hφφ
  have hkk : G.rot.symm (G.rot.symm k) = k := congrArg Subtype.val hφφ
  have hlk : G.legIndex k = none := by
    have : G.legIndex (G.rot.symm (G.rot.symm k)) = none := hl'
    rwa [hkk] at this
  obtain ⟨hfv, hm⟩ := isNormalFlipVertex_of_rot_symm hG rfl hkk hl hlk hv
  exact ⟨(k : H), hfv, k, m, rfl, hm, rfl⟩

/-- The two darts `x⁺_{c̄₄}`, `x⁺_{c̄₂}` of an urban renewal face form a digon of `X(G)`. -/
private theorem isDigon_plus_of_isUrbanRenewalFace (hG : G.IsNormalPlabicGraph) {c : H}
    (hc : G.IsUrbanRenewalFace c) {k₁ k₂ : G.BlackDart}
    (hk₁ : (k₁ : H) = G.inv (G.squareCorner c 3)) (hk₂ : (k₂ : H) = G.inv (G.squareCorner c 1)) :
    (G.tripleOfNormal hG.isNormalPlabicPregraph).IsDigon {.plus k₁, .plus k₂} := by
  set P := hG.isNormalPlabicPregraph
  set X := G.tripleOfNormal P
  have hinv := hG.inv_involutive
  have u := hc.urbanFacts hG
  rw [squareCorner_three_eq] at hk₁
  rw [squareCorner_one_eq] at hk₂
  have hφ₁ : X.facePerm (.plus k₁) = .plus k₂ :=
    P.facePerm_plus_eq' (by rw [hk₁, u.face_y, hinv]; exact u.int_x)
      (by rw [hk₁, u.face_y, hinv, hk₂])
  have hφ₂ : X.facePerm (.plus k₂) = .plus k₁ :=
    P.facePerm_plus_eq' (by rw [hk₂, u.face_x, hinv]; exact u.int_y)
      (by rw [hk₂, u.face_x, hinv, hk₁])
  have hI : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k₁)) := by
    rw [hk₁, hinv, G.vertexOf_rot]
    exact u.int_y
  have hv : X.vertexOf (.plus k₁) ≠ X.vertexOf (.plus k₂) := by
    intro heq
    have hm : (.plus k₂ : G.TripleDart) ∈ X.vertexOf (.plus k₁) :=
      heq ▸ RotationSystem.self_mem_vertexOf _ _
    have := (P.plus_mem_vertexOf_plus_iff hI).1 hm
    rw [hk₁, hk₂, hinv, hinv, G.vertexOf_rot, G.vertexOf_rot] at this
    exact u.ne this
  obtain ⟨hf, hd⟩ := TripleData.isDigon_of_facePerm hφ₁ hφ₂
    (fun h => by simpa using (P.mem_tripleOfNormal_bdry).1 h)
    (fun h => by simpa using (P.mem_tripleOfNormal_bdry).1 h) hv
  rwa [hf] at hd

/-- The two darts `x⁻_k`, `x⁻_{σk}` of a normal flip vertex form a digon of `X(G)`. -/
private theorem isDigon_minus_of_isNormalFlipVertex (hG : G.IsNormalPlabicGraph) {k : H}
    (hk : G.IsNormalFlipVertex k) {k₁ k₂ : G.BlackDart} (hk₁ : (k₁ : H) = k)
    (hk₂ : (k₂ : H) = G.rot k) :
    (G.tripleOfNormal hG.isNormalPlabicPregraph).IsDigon {.minus k₁, .minus k₂} := by
  set P := hG.isNormalPlabicPregraph
  set X := G.tripleOfNormal P
  have u := hk.flipFacts hG
  have hrr := (rot_rot_of_card_vertexOf_eq_two hk.card_vertexOf).1
  have hI₁ : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k₁)) := by rw [hk₁]; exact u.int_x
  have hI₂ : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k₂)) := by rw [hk₂]; exact u.int_y
  have hφ₁ : X.facePerm (.minus k₁) = .minus k₂ :=
    P.facePerm_minus_eq' hI₂ (by rw [hk₁, hk₂, Equiv.eq_symm_apply, hrr])
  have hφ₂ : X.facePerm (.minus k₂) = .minus k₁ :=
    P.facePerm_minus_eq' hI₁ (by rw [hk₁, hk₂, Equiv.symm_apply_apply])
  have hv : X.vertexOf (.minus k₁) ≠ X.vertexOf (.minus k₂) := by
    rw [P.vertexOf_minus_eq' hI₁, P.vertexOf_minus_eq' hI₂]
    intro heq
    have hm : (.plus k₂ : G.TripleDart) ∈ X.vertexOf (.plus k₁) :=
      heq ▸ RotationSystem.self_mem_vertexOf _ _
    have := (P.plus_mem_vertexOf_plus_iff hI₁).1 hm
    rw [hk₁, hk₂] at this
    exact u.ne this.symm
  obtain ⟨hf, hd⟩ := TripleData.isDigon_of_facePerm hφ₁ hφ₂
    (fun h => by simpa using (P.mem_tripleOfNormal_bdry).1 h)
    (fun h => by simpa using (P.mem_tripleOfNormal_bdry).1 h) hv
  rwa [hf] at hd

/-- **The digons of `X(G)`**: let `G` be a normal plabic graph and `δ` a set of darts of `X(G)`.
Then `δ` is a digon of `X(G)` if and only if either `δ = {x⁺_{c̄₄}, x⁺_{c̄₂}}` for a face
`(c₁, c₂, c₃, c₄)` with `G.IsUrbanRenewalFace c` (with `c₁ = c` and `c_{k+1} = squareCorner c k`),
or `δ = {x⁻_k, x⁻_{σk}}` for a black vertex `{k, σk}` with `G.IsNormalFlipVertex k`. A digon has
two elements, so `δ` need not be assumed to have two elements. -/
@[cluster_algebras "lem_triple_of_normal_digons"]
theorem IsNormalPlabicGraph.isDigon_tripleOfNormal_iff (hG : G.IsNormalPlabicGraph)
    (δ : Finset G.TripleDart) :
    (G.tripleOfNormal hG.isNormalPlabicPregraph).IsDigon δ ↔
      (∃ c, G.IsUrbanRenewalFace c ∧ ∃ k₁ k₂ : G.BlackDart,
        (k₁ : H) = G.inv (G.squareCorner c 3) ∧ (k₂ : H) = G.inv (G.squareCorner c 1) ∧
          δ = {.plus k₁, .plus k₂}) ∨
      (∃ k, G.IsNormalFlipVertex k ∧ ∃ k₁ k₂ : G.BlackDart, (k₁ : H) = k ∧
        (k₂ : H) = G.rot k ∧ δ = {.minus k₁, .minus k₂}) := by
  set P := hG.isNormalPlabicPregraph
  set X := G.tripleOfNormal P
  constructor
  · intro hδ
    obtain ⟨d₁, hδ₁, hδ₂⟩ := TripleData.IsDigon.exists_eq_faceOf hδ
    have hd : X.IsDigon (X.faceOf d₁) := hδ₁ ▸ hδ
    obtain ⟨hb₁, hb₂⟩ := hd.notMem_bdry
    rw [hδ₂]
    rcases d₁ with k | k | r | r
    · exact Or.inl (exists_isUrbanRenewalFace_of_isDigon_plus hG k hb₂ hd.facePerm_facePerm
        hd.vertexOf_ne)
    · exact Or.inr (exists_isNormalFlipVertex_of_isDigon_minus hG k hb₂ hd.facePerm_facePerm
        hd.vertexOf_ne)
    · exact absurd ((P.mem_tripleOfNormal_bdry).2 rfl) hb₁
    · exact absurd ((P.mem_tripleOfNormal_bdry).2 rfl) hb₁
  · rintro (⟨c, hc, k₁, k₂, hk₁, hk₂, rfl⟩ | ⟨k, hk, k₁, k₂, hk₁, hk₂, rfl⟩)
    · exact isDigon_plus_of_isUrbanRenewalFace hG hc hk₁ hk₂
    · exact isDigon_minus_of_isNormalFlipVertex hG hk hk₁ hk₂

/-! ### Isomorphisms of triple diagrams induced by a rewiring -/

section RewireIso

variable {π : Equiv.Perm H}

/-- A pair of bijections `e, f : K ≃ K'` induces a bijection of the darts of triple diagrams of
normal plabic graphs, `x⁺_k ↦ x⁺_{e k}`, `x⁻_k ↦ x⁻_{f k}`, `∂_r ↦ ∂_r`, `∂'_r ↦ ∂'_r`. -/
private def mapEquiv₂ {K K' : Type*} {n : ℕ} (e f : K ≃ K') :
    TripleOfNormalDart K n ≃ TripleOfNormalDart K' n where
  toFun
    | .plus k => .plus (e k)
    | .minus k => .minus (f k)
    | .del r => .del r
    | .del' r => .del' r
  invFun
    | .plus k => .plus (e.symm k)
    | .minus k => .minus (f.symm k)
    | .del r => .del r
    | .del' r => .del' r
  left_inv := by rintro (_ | _ | _ | _) <;> simp
  right_inv := by rintro (_ | _ | _ | _) <;> simp

variable (hK : ∀ d, d ∈ (G.rewire π).blackDarts ↔ d ∈ G.blackDarts)
  (hπK : ∀ d, π d ∈ G.blackDarts ↔ d ∈ G.blackDarts)

/-- The bijection `x⁺_k ↦ x⁺_{π k}`, `x⁻_k ↦ x⁻_k`, `∂_r ↦ ∂_r`, `∂'_r ↦ ∂'_r` from the darts of
`X(G.rewire π)` to those of `X(G)`, when the two graphs have the same darts at black vertices and
`π` preserves them. -/
private def rewireDartEquiv : (G.rewire π).TripleDart ≃ G.TripleDart :=
  mapEquiv₂ (π.subtypeEquiv fun a => (hK a).trans (hπK a).symm) (Equiv.subtypeEquivRight hK)

private theorem rewireDartEquiv_plus {k : (G.rewire π).BlackDart} {k' : G.BlackDart}
    (h : π k = (k' : H)) : rewireDartEquiv hK hπK (.plus k) = .plus k' := by
  change TripleOfNormalDart.plus _ = _
  congr 1
  exact Subtype.ext h

private theorem rewireDartEquiv_minus {k : (G.rewire π).BlackDart} {k' : G.BlackDart}
    (h : (k : H) = k') : rewireDartEquiv hK hπK (.minus k) = .minus k' := by
  simp [rewireDartEquiv, mapEquiv₂, Subtype.ext_iff, h]

private theorem rewireDartEquiv_del (r : Fin (2 * b)) :
    rewireDartEquiv hK hπK (.del r) = .del r := rfl

private theorem rewireDartEquiv_del' (r : Fin (2 * b)) :
    rewireDartEquiv hK hπK (.del' r) = .del' r := rfl

variable (hP : G.IsNormalPlabicPregraph) (hP' : (G.rewire π).IsNormalPlabicPregraph)

private theorem rewireDartEquiv_endDart (hleg : ∀ i, π (G.inv (G.leg i)) = G.inv (G.leg i))
    (r : Fin (2 * b)) : rewireDartEquiv hK hπK (hP'.endDart r) = hP.endDart r := by
  rcases exists_sourceIndex_or_targetIndex r with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [hP'.endDart_sourceIndex, hP.endDart_sourceIndex]
    exact rewireDartEquiv_plus hK hπK (hleg i)
  · rw [hP'.endDart_targetIndex, hP.endDart_targetIndex]
    exact rewireDartEquiv_minus hK hπK rfl

/-- The bijection `rewireDartEquiv` is an isomorphism of pre-triple diagrams from `X(G.rewire π)`
to any `Y` with the involution, `B`, orientation and endpoints of `X(G)`, as soon as it
intertwines the rotations. -/
private def rewireTripleIso (hleg : ∀ i, π (G.inv (G.leg i)) = G.inv (G.leg i))
    (Y : TripleData G.TripleDart b) (hYinv : Y.inv = hP.tripleInv)
    (hYbdry : Y.bdry = (G.tripleOfNormal hP).bdry) (hYout : Y.isOut = TripleOfNormalDart.isPlus)
    (hYend : ∀ r, Y.endpoint r = (G.tripleOfNormal hP).endpoint r)
    (hrot : ∀ z, rewireDartEquiv hK hπK (hP'.tripleRot z) = Y.rot (rewireDartEquiv hK hπK z)) :
    ((G.rewire π).tripleOfNormal hP').Iso Y where
  toEquiv := rewireDartEquiv hK hπK
  map_inv := by
    rw [hYinv]
    rintro (k | k | r | r)
    · simp [rewireDartEquiv, mapEquiv₂, Subtype.ext_iff]
    · simp [rewireDartEquiv, mapEquiv₂, Equiv.Perm.mul_def]
    · simp [rewireDartEquiv, mapEquiv₂]
    · simp [rewireDartEquiv, mapEquiv₂]
  map_rot := hrot
  mem_bdry_iff z := by
    rw [hYbdry, hP.mem_tripleOfNormal_bdry, hP'.mem_tripleOfNormal_bdry]
    rcases z with _ | _ | _ | _ <;> simp [rewireDartEquiv, mapEquiv₂]
  map_isOut z _ := by
    rw [hYout]
    rcases z with _ | _ | _ | _ <;> simp [rewireDartEquiv, mapEquiv₂]
  map_endpoint r := by
    rw [hYend]
    simp only [TripleData.endpoint, IsNormalPlabicPregraph.tripleOfNormal_endDart,
      IsNormalPlabicPregraph.vertexOf_tripleOfNormal_endDart,
      IsNormalPlabicPregraph.vertexOf_tripleOfNormal_del, map_insert, map_singleton,
      Equiv.coe_toEmbedding]
    rw [rewireDartEquiv_endDart hK hπK hP hP' hleg]
    rfl

end RewireIso

/-! ### Triple diagrams isomorphic to a triple diagram -/

private theorem card_image_univ_eq_of_map {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (θ : α ≃ β) (F : α → Finset α) (F' : β → Finset β)
    (h : ∀ a, (F a).map θ.toEmbedding = F' (θ a)) :
    (univ.image F').card = (univ.image F).card := by
  have : univ.image F' = (univ.image F).map ⟨fun s => s.map θ.toEmbedding, map_injective _⟩ := by
    ext s
    simp only [mem_image, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨F (θ.symm y), ⟨_, rfl⟩, by rw [h, Equiv.apply_symm_apply]⟩
    · rintro ⟨s, ⟨a, rfl⟩, rfl⟩
      exact ⟨θ a, (h a).symm⟩
  rw [this, card_map]

/-- A pre-triple diagram isomorphic to a triple diagram is a triple diagram. -/
private theorem isTripleDiagram_of_iso {K K' : Type} [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] {Y : TripleData K b} {X' : TripleData K' b} (θ : Y.Iso X')
    (hY : Y.IsPreTripleDiagram) (hX' : X'.IsTripleDiagram) : Y.IsTripleDiagram := by
  have he : ∀ d, (Y.edgeOf d).map θ.toEquiv.toEmbedding = X'.edgeOf (θ.toEquiv d) := by
    intro d
    simp [RotationSystem.edgeOf, θ.map_inv]
  refine hY.isTripleDiagram (fun d e => ?_) ?_
  · refine (RotationSystem.reach_iff_exists_mem_closure _).1 ?_
    have key : ∀ a c, X'.Reach a c → Y.Reach (θ.toEquiv.symm a) (θ.toEquiv.symm c) := by
      intro a c h
      induction h with
      | refl => exact .refl _
      | rot _ ih => rw [θ.symm_map_rot]; exact ih.rot
      | inv _ ih => rw [θ.symm_map_inv]; exact ih.inv
    simpa using key _ _ (hX'.toIsDiskMap.toIsConnected.reach (θ.toEquiv d) (θ.toEquiv e))
  · have h1 : Y.vertices.card = X'.vertices.card :=
      (card_image_univ_eq_of_map θ.toEquiv _ _ θ.map_vertexOf).symm
    have h2 : Y.edges.card = X'.edges.card := (card_image_univ_eq_of_map θ.toEquiv _ _ he).symm
    have h3 : Y.faceOrbits.card = X'.faceOrbits.card :=
      (card_image_univ_eq_of_map θ.toEquiv _ _ θ.map_faceOf).symm
    rw [h1, h2, h3]
    exact hX'.euler

/-! ### Urban renewal is a swivel move -/

section Darts

variable {π : Equiv.Perm H}
  (hbd : ∀ d, G.IsBoundaryVertex (G.vertexOf d) → π d = d)
  (hcol : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) → G.colour (π d) = G.colour d)

include hbd hcol

/-- The rewired graph has the darts at black vertices of `G`. -/
private theorem mem_blackDarts_rewire_iff (hG : G.IsNormalPlabicGraph) (d : H) :
    d ∈ (G.rewire π).blackDarts ↔ d ∈ G.blackDarts := by
  rw [mem_blackDarts, mem_blackDarts, isBoundaryVertex_rewire_iff hG hbd hcol]
  refine and_congr_right fun hd => ?_
  rw [colour_rewire_of_not_isBoundaryVertex hG hbd hcol hd]

/-- `π` preserves the darts at black vertices. -/
private theorem perm_mem_blackDarts_iff (d : H) : π d ∈ G.blackDarts ↔ d ∈ G.blackDarts := by
  rw [mem_blackDarts, mem_blackDarts]
  by_cases hd : G.IsBoundaryVertex (G.vertexOf d)
  · rw [hbd d hd]
  · rw [hcol d hd]
    exact and_congr_left fun _ => iff_of_true (not_isBoundaryVertex_perm hbd hd) hd

end Darts

/-- A digon is the orbit `f(d)` of each of its darts `d`. -/
private theorem TripleData.IsDigon.eq_faceOf {K : Type} [Fintype K] [DecidableEq K]
    {X : TripleData K b} {δ : Finset K} (hδ : X.IsDigon δ) {d : K} (hd : d ∈ δ) :
    δ = X.faceOf d := by
  obtain ⟨d₁, h₁, -⟩ := TripleData.IsDigon.exists_eq_faceOf hδ
  rw [h₁] at hd ⊢
  exact (X.faceOf_eq_of_mem hd).symm

/-- The dart `c̄₄` of the face of urban renewal lies at a black vertex. -/
theorem IsUrbanRenewalFace.inv_squareCorner_three_mem_blackDarts (hG : G.IsNormalPlabicGraph)
    {c : H} (hc : G.IsUrbanRenewalFace c) : G.inv (G.squareCorner c 3) ∈ G.blackDarts :=
  mem_blackDarts.2 (hG.inv_internal_black_of_white (hc.not_isBoundaryVertex 3)
    hc.colour_squareCorner_three)

/-- The dart `c̄₂` of the face of urban renewal lies at a black vertex. -/
theorem IsUrbanRenewalFace.inv_squareCorner_one_mem_blackDarts (hG : G.IsNormalPlabicGraph)
    {c : H} (hc : G.IsUrbanRenewalFace c) : G.inv (G.squareCorner c 1) ∈ G.blackDarts :=
  mem_blackDarts.2 (hG.inv_internal_black_of_white (hc.not_isBoundaryVertex 1)
    hc.colour_squareCorner_one)

/-- The dart `k` of the vertex of the normal flip lies at a black vertex. -/
theorem IsNormalFlipVertex.mem_blackDarts {k : H} (hk : G.IsNormalFlipVertex k) :
    k ∈ G.blackDarts :=
  PlabicData.mem_blackDarts.2 ⟨hk.not_isBoundaryVertex, hk.colour_eq⟩

namespace UrbanFacts

variable {π : Equiv.Perm H} {x y : H} (hG : G.IsNormalPlabicGraph)

include hG

/-- `π` fixes the reverses `ḡ_i` of the legs. -/
private theorem perm_inv_leg (u : UrbanFacts G π x y) (i : Fin b) :
    π (G.inv (G.leg i)) = G.inv (G.leg i) := by
  refine u.fix _ (fun h => ?_) (fun h => ?_)
  · have := (u.toWhitePair.forall_mem_white hG h).2
    rw [hG.colour_inv_leg i] at this
    exact Shade.noConfusion this
  · exact u.toWhitePair.inv_leg_notMem hG i h

/-- The identity `π(\overline{σ(π w)}) = \overline{σ w}` at the darts `w` of white vertices. -/
private theorem perm_inv_rot_perm (u : UrbanFacts G π x y) {w : H}
    (hw : ¬G.IsBoundaryVertex (G.vertexOf w)) (hc : G.colour w = .white) :
    π (G.inv (G.rot (π w))) = G.inv (G.rot w) := by
  have hx3 := u.toWhitePair.rot3_x hG
  have hy3 := u.toWhitePair.symm.rot3_x hG
  by_cases h6 : w ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h6
    rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u.p1, u.q6]
    · rw [u.p2, hy3, u.q5]
    · rw [u.p4, u.q1, hx3]
    · rw [u.p5, u.q3]
    · rw [u.p6, hx3, u.q2]
    · rw [u.p3, u.q4, hy3]
  · have hwB : w ∉ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)), G.inv y, G.inv (G.rot y),
        G.inv (G.rot (G.rot y))] := fun h => by
      have := (u.forall_mem_inv_black hG w h).2
      rw [hc] at this
      exact Shade.noConfusion this
    rw [u.fix w h6 hwB]
    have hrw : ¬G.IsBoundaryVertex (G.vertexOf (G.rot w)) := by rwa [G.vertexOf_rot]
    have hrc : G.colour (G.rot w) = .white := by rw [hG.colour_rot _ hw, hc]
    refine u.fix _ (fun h => ?_) (fun h => ?_)
    · have := (u.toWhitePair.forall_mem_white hG h).2
      rw [(hG.inv_internal_black_of_white hrw hrc).2] at this
      exact Shade.noConfusion this
    · have h' : G.rot w ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)] := by
        simpa using h
      apply h6
      rw [u.toWhitePair.mem_iff hG] at h' ⊢
      rcases h' with h' | h'
      · left; rw [← G.vertexOf_eq_of_mem h', G.vertexOf_rot]; exact G.self_mem_vertexOf w
      · right; rw [← G.vertexOf_eq_of_mem h', G.vertexOf_rot]; exact G.self_mem_vertexOf w

/-- Urban renewal is a swivel move, in the variables `x = c̄₁` and `y = c̄₃`. -/
private theorem exists_iso (u : UrbanFacts G π x y) (hP' : (G.rewire π).IsNormalPlabicPregraph)
    {k₁ : G.BlackDart} (hk₁ : (k₁ : H) = G.inv (G.rot y))
    (hd : (G.tripleOfNormal hG.isNormalPlabicPregraph).IsDigon
      ((G.tripleOfNormal hG.isNormalPlabicPregraph).faceOf (.plus k₁))) :
    ∃ θ : ((G.rewire π).tripleOfNormal hP').Iso
        ((G.tripleOfNormal hG.isNormalPlabicPregraph).swivelMove (.plus k₁)),
      (∀ (k : (G.rewire π).BlackDart) (hk : (k : H) ∈ G.blackDarts),
        θ.toEquiv (.minus k) = .minus ⟨k, hk⟩) ∧
      (∀ (k : (G.rewire π).BlackDart) (hk : π k ∈ G.blackDarts),
        θ.toEquiv (.plus k) = .plus ⟨π k, hk⟩) ∧
      (∀ r, θ.toEquiv (.del r) = .del r) ∧ (∀ r, θ.toEquiv (.del' r) = .del' r) := by
  set P := hG.isNormalPlabicPregraph
  set X := G.tripleOfNormal P
  have hbd : ∀ d, G.IsBoundaryVertex (G.vertexOf d) → π d = d := fun _ h => u.perm_eq hG h
  have hcol : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) → G.colour (π d) = G.colour d :=
    fun _ _ => u.colour_perm hG
  have hK := mem_blackDarts_rewire_iff hbd hcol hG
  have hπK := perm_mem_blackDarts_iff hbd hcol
  have hinv := P.inv_inv
  have hx3 := u.toWhitePair.rot3_x hG
  have hy3 := u.toWhitePair.symm.rot3_x hG
  have W : ∀ d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)],
      ¬G.IsBoundaryVertex (G.vertexOf d) := fun d h => (u.toWhitePair.forall_mem_white hG h).1
  obtain ⟨bx, hbx, Ix⟩ := u.toWhitePair.exists_blackDart hG (d := x) (by simp)
  obtain ⟨brx, hbrx, Irx⟩ := u.toWhitePair.exists_blackDart hG (d := G.rot x) (by simp)
  obtain ⟨brrx, hbrrx, Irrx⟩ := u.toWhitePair.exists_blackDart hG (d := G.rot (G.rot x)) (by simp)
  obtain ⟨by', hby, Iy⟩ := u.toWhitePair.exists_blackDart hG (d := y) (by simp)
  obtain ⟨bry, hbry, Iry⟩ := u.toWhitePair.exists_blackDart hG (d := G.rot y) (by simp)
  obtain ⟨brry, hbrry, Irry⟩ := u.toWhitePair.exists_blackDart hG (d := G.rot (G.rot y)) (by simp)
  obtain rfl : k₁ = bry := Subtype.ext (hk₁.trans hbry.symm)
  have h1 : X.rot (.plus k₁) = .minus k₁ := P.tripleRot_plus_eq' Iry
  have h2 : X.rot (.minus k₁) = .plus brry := P.tripleRot_minus_eq' Iry (by rw [hbrry, hbry, hinv])
  have h3 : X.rot (.plus brry) = .minus brry := P.tripleRot_plus_eq' Irry
  have h4 : X.rot (.minus brry) = .plus by' :=
    P.tripleRot_minus_eq' Irry (by rw [hby, hbrry, hinv, hy3])
  have hφ : X.facePerm (.plus k₁) = .plus brx :=
    P.facePerm_plus_eq' (by rw [hbry, u.face_y, hinv]; exact W _ (by simp))
      (by rw [hbrx, hbry, u.face_y, hinv])
  have hi1 : X.inv (.plus brx) = .minus by' := P.tripleInv_plus_eq' (by rw [hby, hbrx, u.face_x])
  have hi2 : X.inv (.plus k₁) = .minus bx := P.tripleInv_plus_eq' (by rw [hbx, hbry, u.face_y])
  have h5 : X.rot (.plus by') = X.inv (X.facePerm (.plus k₁)) := by
    rw [hφ, hi1]; exact P.tripleRot_plus_eq' Iy
  have g1 : X.rot (X.facePerm (.plus k₁)) = .minus brx := by
    rw [hφ]; exact P.tripleRot_plus_eq' Irx
  have g2 : X.rot (.minus brx) = .plus brrx := P.tripleRot_minus_eq' Irx (by rw [hbrrx, hbrx, hinv])
  have g3 : X.rot (.plus brrx) = .minus brrx := P.tripleRot_plus_eq' Irrx
  have g4 : X.rot (.minus brrx) = .plus bx :=
    P.tripleRot_minus_eq' Irrx (by rw [hbx, hbrrx, hinv, hx3])
  have g5 : X.rot (.plus bx) = X.inv (.plus k₁) := by rw [hi2]; exact P.tripleRot_plus_eq' Ix
  have hn := u.toWhitePair.nodup hG
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hn
  obtain ⟨⟨n12, n13, n14, n15, n16⟩, ⟨n23, n24, n25, n26⟩, ⟨n34, n35, n36⟩, ⟨n45, n46⟩, n56, -⟩ :=
    hn
  have hnd : [.plus k₁, .plus brry, .plus by', X.facePerm (.plus k₁), .plus brrx,
      .plus bx].Nodup := by
    rw [hφ]
    simp [Subtype.ext_iff, hbx, hbrx, hbrrx, hby, hbry, hbrry, n23, n56, Ne.symm n12, Ne.symm n13,
      Ne.symm n14, Ne.symm n15, Ne.symm n16, Ne.symm n24, Ne.symm n25, Ne.symm n26, Ne.symm n34,
      Ne.symm n35, Ne.symm n36, Ne.symm n45, Ne.symm n46]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ :=
    TripleData.swivelRot_of_darts h1 h2 h3 h4 h5 g1 g2 g3 g4 g5 hnd
  rw [hi2] at s2
  rw [hφ] at s5 s6 s7
  rw [hi1] at s6
  have eplus : ∀ {k k' : G.BlackDart},
      (TripleOfNormalDart.plus k : G.TripleDart) = .plus k' → (k : H) = k' :=
    fun h => congrArg Subtype.val (TripleOfNormalDart.plus.inj h)
  have hplus : ∀ k : G.BlackDart, (k : H) ∉ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)),
      G.inv y, G.inv (G.rot y), G.inv (G.rot (G.rot y))] →
      X.swivelRot (.plus k₁) (.plus k) = X.rot (.plus k) := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hk
    exact s7 _ (fun h => n5 ((eplus h).trans hbry)) (fun h => n6 ((eplus h).trans hbrry))
      (fun h => n4 ((eplus h).trans hby)) (fun h => n2 ((eplus h).trans hbrx))
      (fun h => n3 ((eplus h).trans hbrrx)) (fun h => n1 ((eplus h).trans hbx))
  have hother : ∀ z : G.TripleDart, z.isPlus = false →
      X.swivelRot (.plus k₁) z = X.rot z := by
    intro z hz
    refine s7 _ ?_ ?_ ?_ ?_ ?_ ?_ <;> rintro rfl <;> simp at hz
  have hleg := u.perm_inv_leg hG
  have hrot : ∀ z, rewireDartEquiv hK hπK (hP'.tripleRot z) =
      (X.swivelMove (.plus k₁)).rot (rewireDartEquiv hK hπK z) := by
    rintro (k | k | r | r)
    · have hkK : (k : H) ∈ G.blackDarts := (hK k).1 k.2
      rcases hl : G.legIndex k with _ | i
      · rw [hP'.tripleRot_plus_of_none (k := k) hl,
          rewireDartEquiv_minus hK hπK (k' := ⟨k, hkK⟩) rfl, TripleData.swivelMove_rot]
        by_cases hk6 : (k : H) ∈ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)), G.inv y,
            G.inv (G.rot y), G.inv (G.rot (G.rot y))]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk6
          rcases hk6 with h | h | h | h | h | h
          · rw [rewireDartEquiv_plus hK hπK (k' := brry) (by rw [h, u.q2, hbrry]), s2]
            exact congrArg _ (Subtype.ext (h.trans hbx.symm))
          · rw [rewireDartEquiv_plus hK hπK (k' := by') (by rw [h, u.q4, hby]), s4]
            exact congrArg _ (Subtype.ext (h.trans hbrx.symm))
          · rw [rewireDartEquiv_plus hK hπK (k' := brx) (by rw [h, u.q6, hbrx]), s5]
            exact congrArg _ (Subtype.ext (h.trans hbrrx.symm))
          · rw [rewireDartEquiv_plus hK hπK (k' := brrx) (by rw [h, u.q5, hbrrx]), s6]
            exact congrArg _ (Subtype.ext (h.trans hby.symm))
          · rw [rewireDartEquiv_plus hK hπK (k' := bx) (by rw [h, u.q1, hbx]), s3]
            exact congrArg _ (Subtype.ext (h.trans hbry.symm))
          · rw [rewireDartEquiv_plus hK hπK (k' := k₁) (by rw [h, u.q3, hbry]), s1]
            exact congrArg _ (Subtype.ext (h.trans hbrry.symm))
        · have hkW : (k : H) ∉ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)] :=
            fun h => by
              have := (u.toWhitePair.forall_mem_white hG h).2
              rw [(mem_blackDarts.1 hkK).2] at this
              exact Shade.noConfusion this
          rw [rewireDartEquiv_plus hK hπK (k' := ⟨k, hkK⟩) (u.fix _ hkW hk6), hplus _ hk6]
          exact (P.tripleRot_plus_of_none (k := ⟨k, hkK⟩) hl).symm
      · have hk : (k : H) = G.inv (G.leg i) := (inv_leg_of_legIndex_eq_some hl).symm
        have hk6 : (k : H) ∉ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)), G.inv y,
            G.inv (G.rot y), G.inv (G.rot (G.rot y))] := hk ▸ u.toWhitePair.inv_leg_notMem hG i
        rw [hP'.tripleRot_plus_of_some (k := k) hl, rewireDartEquiv_del',
          rewireDartEquiv_plus hK hπK (k' := ⟨k, hkK⟩) (by rw [hk]; exact hleg i),
          TripleData.swivelMove_rot, hplus _ hk6]
        exact (P.tripleRot_plus_of_some (k := ⟨k, hkK⟩) hl).symm
    · have hkK : (k : H) ∈ G.blackDarts := (hK k).1 k.2
      rw [rewireDartEquiv_minus hK hπK (k' := ⟨k, hkK⟩) rfl, TripleData.swivelMove_rot,
        hother _ rfl]
      change _ = P.tripleRot _
      rcases hl : G.legIndex k with _ | i
      · have hl' : (G.rewire π).legIndex k = none := hl
        rw [hP'.tripleRot_minus_of_none (k := k) hl', P.tripleRot_minus_of_none (k := ⟨k, hkK⟩) hl]
        exact rewireDartEquiv_plus hK hπK (u.perm_inv_rot_perm hG
          (P.not_isBoundaryVertex_inv hkK hl) (P.colour_inv hkK hl))
      · have hl' : (G.rewire π).legIndex k = some i := hl
        rw [hP'.tripleRot_minus_of_some (k := k) hl', P.tripleRot_minus_of_some (k := ⟨k, hkK⟩) hl]
        rfl
    · rw [hP'.tripleRot_del, rewireDartEquiv_endDart hK hπK P hP' hleg, rewireDartEquiv_del,
        TripleData.swivelMove_rot, hother _ rfl]
      rfl
    · rw [hP'.tripleRot_del', rewireDartEquiv_del, rewireDartEquiv_del',
        TripleData.swivelMove_rot, hother _ rfl]
      rfl
  exact ⟨rewireTripleIso hK hπK P hP' hleg (X.swivelMove (.plus k₁)) rfl rfl rfl
    (fun r => TripleData.IsDigon.endpoint_swivelMove P.isPreTripleDiagram_tripleOfNormal hd r) hrot,
    fun k _ => rewireDartEquiv_minus hK hπK rfl, fun k _ => rewireDartEquiv_plus hK hπK rfl,
    fun _ => rfl, fun _ => rfl⟩

end UrbanFacts

namespace FlipFacts

variable {π : Equiv.Perm H} {x y : H} (hG : G.IsNormalPlabicGraph)

include hG

/-- `π` fixes the darts at black vertices. -/
private theorem perm_of_black (u : FlipFacts G π x y) {k : H} (hk : G.colour k = .black) :
    π k = k :=
  u.fix k fun h => by
    have := (u.toWhitePair.forall_mem_white hG h).2
    rw [hk] at this
    exact Shade.noConfusion this

/-- The normal flip is a swivel move, in the variables `x = k̄` and `y = \overline{σk}`. -/
private theorem exists_iso (u : FlipFacts G π x y) (hP' : (G.rewire π).IsNormalPlabicPregraph)
    {k₁ : G.BlackDart} (hk₁ : (k₁ : H) = G.inv x)
    (hd : (G.tripleOfNormal hG.isNormalPlabicPregraph).IsDigon
      ((G.tripleOfNormal hG.isNormalPlabicPregraph).faceOf (.minus k₁))) :
    ∃ θ : ((G.rewire π).tripleOfNormal hP').Iso
        ((G.tripleOfNormal hG.isNormalPlabicPregraph).swivelMove (.minus k₁)),
      (∀ (k : (G.rewire π).BlackDart) (hk : (k : H) ∈ G.blackDarts),
        θ.toEquiv (.plus k) = .plus ⟨k, hk⟩ ∧ θ.toEquiv (.minus k) = .minus ⟨k, hk⟩) ∧
      (∀ r, θ.toEquiv (.del r) = .del r) ∧ (∀ r, θ.toEquiv (.del' r) = .del' r) := by
  set P := hG.isNormalPlabicPregraph
  set X := G.tripleOfNormal P
  have hbd : ∀ d, G.IsBoundaryVertex (G.vertexOf d) → π d = d := fun _ h => u.perm_eq hG h
  have hcol : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) → G.colour (π d) = G.colour d :=
    fun _ _ => u.colour_perm hG
  have hK := mem_blackDarts_rewire_iff hbd hcol hG
  have hπK := perm_mem_blackDarts_iff hbd hcol
  have hinv := P.inv_inv
  have hx3 := u.toWhitePair.rot3_x hG
  have hy3 := u.toWhitePair.symm.rot3_x hG
  have mB : ∀ d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)],
      G.inv d ∈ G.blackDarts := fun d h => mem_blackDarts.2 (u.toWhitePair.forall_mem_black hG h)
  have πB : ∀ d ∈ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)],
      π (G.inv d) = G.inv d := fun d h => u.perm_of_black hG (mem_blackDarts.1 (mB d h)).2
  obtain ⟨bx, hbx, Ix⟩ := u.toWhitePair.exists_blackDart hG (d := x) (by simp)
  obtain ⟨brx, hbrx, Irx⟩ := u.toWhitePair.exists_blackDart hG (d := G.rot x) (by simp)
  obtain ⟨brrx, hbrrx, Irrx⟩ := u.toWhitePair.exists_blackDart hG (d := G.rot (G.rot x)) (by simp)
  obtain ⟨by', hby, Iy⟩ := u.toWhitePair.exists_blackDart hG (d := y) (by simp)
  obtain ⟨bry, hbry, Iry⟩ := u.toWhitePair.exists_blackDart hG (d := G.rot y) (by simp)
  obtain ⟨brry, hbrry, Irry⟩ := u.toWhitePair.exists_blackDart hG (d := G.rot (G.rot y)) (by simp)
  obtain rfl : k₁ = bx := Subtype.ext (hk₁.trans hbx.symm)
  have h1 : X.rot (.minus k₁) = .plus brx := P.tripleRot_minus_eq' Ix (by rw [hbrx, hbx, hinv])
  have h2 : X.rot (.plus brx) = .minus brx := P.tripleRot_plus_eq' Irx
  have h3 : X.rot (.minus brx) = .plus brrx := P.tripleRot_minus_eq' Irx (by rw [hbrrx, hbrx, hinv])
  have h4 : X.rot (.plus brrx) = .minus brrx := P.tripleRot_plus_eq' Irrx
  have hφ : X.facePerm (.minus k₁) = .minus by' :=
    P.facePerm_minus_eq' Iy (by rw [hby, hbx, Equiv.eq_symm_apply, u.face_y])
  have hi1 : X.inv (.minus by') = .plus k₁ :=
    P.tripleInv_minus_eq' (by rw [hby, hbx, Equiv.eq_symm_apply, u.face_x])
  have hi2 : X.inv (.minus k₁) = .plus by' :=
    P.tripleInv_minus_eq' (by rw [hby, hbx, Equiv.eq_symm_apply, u.face_y])
  have h5 : X.rot (.minus brrx) = X.inv (X.facePerm (.minus k₁)) := by
    rw [hφ, hi1]; exact P.tripleRot_minus_eq' Irrx (by rw [hbx, hbrrx, hinv, hx3])
  have g1 : X.rot (X.facePerm (.minus k₁)) = .plus bry := by
    rw [hφ]; exact P.tripleRot_minus_eq' Iy (by rw [hbry, hby, hinv])
  have g2 : X.rot (.plus bry) = .minus bry := P.tripleRot_plus_eq' Iry
  have g3 : X.rot (.minus bry) = .plus brry := P.tripleRot_minus_eq' Iry (by rw [hbrry, hbry, hinv])
  have g4 : X.rot (.plus brry) = .minus brry := P.tripleRot_plus_eq' Irry
  have g5 : X.rot (.minus brry) = X.inv (.minus k₁) := by
    rw [hi2]; exact P.tripleRot_minus_eq' Irry (by rw [hby, hbrry, hinv, hy3])
  have hn := u.toWhitePair.nodup hG
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hn
  obtain ⟨⟨n12, n13, n14, n15, n16⟩, ⟨n23, n24, n25, n26⟩, ⟨n34, n35, n36⟩, ⟨n45, n46⟩, n56, -⟩ :=
    hn
  have hnd : [.minus k₁, .minus brx, .minus brrx, X.facePerm (.minus k₁), .minus bry,
      .minus brry].Nodup := by
    rw [hφ]
    simp [Subtype.ext_iff, hbx, hbrx, hbrrx, hby, hbry, hbrry, n12, n13, n14, n15, n16, n23, n24,
      n25, n26, n34, n35, n36, n45, n46, n56]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ :=
    TripleData.swivelRot_of_darts h1 h2 h3 h4 h5 g1 g2 g3 g4 g5 hnd
  rw [hi2] at s2
  rw [hφ] at s5 s6 s7
  rw [hi1] at s6
  have eminus : ∀ {k k' : G.BlackDart},
      (TripleOfNormalDart.minus k : G.TripleDart) = .minus k' → (k : H) = k' :=
    fun h => congrArg Subtype.val (TripleOfNormalDart.minus.inj h)
  have hminus : ∀ k : G.BlackDart, (k : H) ∉ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)),
      G.inv y, G.inv (G.rot y), G.inv (G.rot (G.rot y))] →
      X.swivelRot (.minus k₁) (.minus k) = X.rot (.minus k) := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hk
    exact s7 _ (fun h => n1 ((eminus h).trans hbx)) (fun h => n2 ((eminus h).trans hbrx))
      (fun h => n3 ((eminus h).trans hbrrx)) (fun h => n4 ((eminus h).trans hby))
      (fun h => n5 ((eminus h).trans hbry)) (fun h => n6 ((eminus h).trans hbrry))
  have hother : ∀ z : G.TripleDart, z.isDel = true ∨ z.isPlus = true →
      X.swivelRot (.minus k₁) z = X.rot z := by
    intro z hz
    refine s7 _ ?_ ?_ ?_ ?_ ?_ ?_ <;> rintro rfl <;> simp at hz
  have hleg : ∀ i, π (G.inv (G.leg i)) = G.inv (G.leg i) :=
    fun i => u.perm_of_black hG (hG.colour_inv_leg i)
  have hrot : ∀ z, rewireDartEquiv hK hπK (hP'.tripleRot z) =
      (X.swivelMove (.minus k₁)).rot (rewireDartEquiv hK hπK z) := by
    rintro (k | k | r | r)
    · have hkK : (k : H) ∈ G.blackDarts := (hK k).1 k.2
      rw [rewireDartEquiv_plus hK hπK (k' := ⟨k, hkK⟩)
          (u.perm_of_black hG (mem_blackDarts.1 hkK).2), TripleData.swivelMove_rot,
        hother _ (Or.inr rfl)]
      change _ = P.tripleRot _
      rcases hl : G.legIndex k with _ | i
      · have hl' : (G.rewire π).legIndex k = none := hl
        rw [hP'.tripleRot_plus_of_none (k := k) hl', P.tripleRot_plus_of_none (k := ⟨k, hkK⟩) hl]
        exact rewireDartEquiv_minus hK hπK rfl
      · have hl' : (G.rewire π).legIndex k = some i := hl
        rw [hP'.tripleRot_plus_of_some (k := k) hl', P.tripleRot_plus_of_some (k := ⟨k, hkK⟩) hl]
        rfl
    · have hkK : (k : H) ∈ G.blackDarts := (hK k).1 k.2
      rw [rewireDartEquiv_minus hK hπK (k' := ⟨k, hkK⟩) rfl, TripleData.swivelMove_rot]
      rcases hl : G.legIndex k with _ | i
      · have hl' : (G.rewire π).legIndex k = none := hl
        rw [hP'.tripleRot_minus_of_none (k := k) hl']
        by_cases hk6 : (k : H) ∈ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)), G.inv y,
            G.inv (G.rot y), G.inv (G.rot (G.rot y))]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk6
          have hkv : ∀ {b' : G.BlackDart}, (k : H) = b' → (⟨k, hkK⟩ : G.BlackDart) = b' :=
            fun h => Subtype.ext h
          rcases hk6 with h | h | h | h | h | h
          · rw [hkv (h.trans hbx.symm), s1]
            refine rewireDartEquiv_plus hK hπK ?_
            change π (G.inv (G.rot (π (G.inv k)))) = _
            rw [h, hinv, u.p1, πB _ (by simp), hbrrx]
          · rw [hkv (h.trans hbrx.symm), s2]
            refine rewireDartEquiv_plus hK hπK ?_
            change π (G.inv (G.rot (π (G.inv k)))) = _
            rw [h, hinv, u.p2, hy3, πB _ (by simp), hby]
          · rw [hkv (h.trans hbrrx.symm), s4]
            refine rewireDartEquiv_plus hK hπK ?_
            change π (G.inv (G.rot (π (G.inv k)))) = _
            rw [h, hinv, u.p4, πB _ (by simp), hbry]
          · rw [hkv (h.trans hby.symm), s5]
            refine rewireDartEquiv_plus hK hπK ?_
            change π (G.inv (G.rot (π (G.inv k)))) = _
            rw [h, hinv, u.p5, πB _ (by simp), hbrry]
          · rw [hkv (h.trans hbry.symm), s6]
            refine rewireDartEquiv_plus hK hπK ?_
            change π (G.inv (G.rot (π (G.inv k)))) = _
            rw [h, hinv, u.p6, hx3, πB _ (by simp), hbx]
          · rw [hkv (h.trans hbrry.symm), s3]
            refine rewireDartEquiv_plus hK hπK ?_
            change π (G.inv (G.rot (π (G.inv k)))) = _
            rw [h, hinv, u.p3, πB _ (by simp), hbrx]
        · rw [hminus _ hk6]
          change _ = P.tripleRot _
          rw [P.tripleRot_minus_of_none (k := ⟨k, hkK⟩) hl]
          refine rewireDartEquiv_plus hK hπK ?_
          change π (G.inv (G.rot (π (G.inv k)))) = G.inv (G.rot (G.inv k))
          have hk6' : G.inv k ∉ [x, G.rot x, G.rot (G.rot x), y, G.rot y, G.rot (G.rot y)] := by
            intro h
            apply hk6
            have := List.mem_map_of_mem (f := G.inv) h
            simpa [hinv] using this
          rw [u.fix _ hk6']
          exact u.perm_of_black hG (P.inv_black_of_white
            (by rw [G.vertexOf_rot]; exact P.not_isBoundaryVertex_inv hkK hl)
            (by rw [hG.colour_rot _ (P.not_isBoundaryVertex_inv hkK hl)]
                exact P.colour_inv hkK hl)).2
      · have hl' : (G.rewire π).legIndex k = some i := hl
        have hk : (k : H) = G.inv (G.leg i) := (inv_leg_of_legIndex_eq_some hl).symm
        have hk6 : (k : H) ∉ [G.inv x, G.inv (G.rot x), G.inv (G.rot (G.rot x)), G.inv y,
            G.inv (G.rot y), G.inv (G.rot (G.rot y))] := hk ▸ u.toWhitePair.inv_leg_notMem hG i
        rw [hminus _ hk6, hP'.tripleRot_minus_of_some (k := k) hl']
        change _ = P.tripleRot _
        rw [P.tripleRot_minus_of_some (k := ⟨k, hkK⟩) hl]
        rfl
    · rw [hP'.tripleRot_del, rewireDartEquiv_endDart hK hπK P hP' hleg, rewireDartEquiv_del,
        TripleData.swivelMove_rot, hother _ (Or.inl rfl)]
      rfl
    · rw [hP'.tripleRot_del', rewireDartEquiv_del, rewireDartEquiv_del',
        TripleData.swivelMove_rot, hother _ (Or.inl rfl)]
      rfl
  exact ⟨rewireTripleIso hK hπK P hP' hleg (X.swivelMove (.minus k₁)) rfl rfl rfl
    (fun r => TripleData.IsDigon.endpoint_swivelMove P.isPreTripleDiagram_tripleOfNormal hd r) hrot,
    fun k hk => ⟨rewireDartEquiv_plus hK hπK (u.perm_of_black hG (mem_blackDarts.1 hk).2),
      rewireDartEquiv_minus hK hπK rfl⟩, fun _ => rfl, fun _ => rfl⟩

end FlipFacts

/-- **Urban renewal is a swivel move**: for a face `c` with `G.IsUrbanRenewalFace c`, let `G'` be
the urban renewal of the normal plabic graph `G` at the face `(c₁, c₂, c₃, c₄)` with `c₁ = c`, and
`π` its permutation. Then `G'` has the darts at black vertices of `G`, the set
`{x⁺_{c̄₄}, x⁺_{c̄₂}}` is a digon of `X(G)` (the orbit of `φ` through `x⁺_{c̄₄}`), and the map `θ`
with `θ(x⁻_k) = x⁻_k`, `θ(x⁺_k) = x⁺_{π(k)}`, `θ(∂_r) = ∂_r` and `θ(∂'_r) = ∂'_r` is an isomorphism
of pre-triple diagrams from `X(G')` to the swivel move of `X(G)` at this digon. -/
@[cluster_algebras "lem_urban_renewal_swivel"]
theorem IsUrbanRenewalFace.exists_iso_swivelMove (hG : G.IsNormalPlabicGraph) {c : H}
    (hc : G.IsUrbanRenewalFace c) :
    (G.urbanRenewal c).blackDarts = G.blackDarts ∧
    (G.tripleOfNormal hG.isNormalPlabicPregraph).faceOf
        (.plus ⟨G.inv (G.squareCorner c 3), hc.inv_squareCorner_three_mem_blackDarts hG⟩) =
      {.plus ⟨G.inv (G.squareCorner c 3), hc.inv_squareCorner_three_mem_blackDarts hG⟩,
        .plus ⟨G.inv (G.squareCorner c 1), hc.inv_squareCorner_one_mem_blackDarts hG⟩} ∧
    (G.tripleOfNormal hG.isNormalPlabicPregraph).IsDigon
      ((G.tripleOfNormal hG.isNormalPlabicPregraph).faceOf
        (.plus ⟨G.inv (G.squareCorner c 3), hc.inv_squareCorner_three_mem_blackDarts hG⟩)) ∧
    ∃ θ : ((G.urbanRenewal c).tripleOfNormal (hc.isNormalPlabicPregraph_urbanRenewal hG)).Iso
        ((G.tripleOfNormal hG.isNormalPlabicPregraph).swivelMove
          (.plus ⟨G.inv (G.squareCorner c 3), hc.inv_squareCorner_three_mem_blackDarts hG⟩)),
      (∀ (k : (G.urbanRenewal c).BlackDart) (hk : (k : H) ∈ G.blackDarts),
        θ.toEquiv (.minus k) = .minus ⟨k, hk⟩) ∧
      (∀ (k : (G.urbanRenewal c).BlackDart) (hk : G.urbanRenewalPerm c k ∈ G.blackDarts),
        θ.toEquiv (.plus k) = .plus ⟨G.urbanRenewalPerm c k, hk⟩) ∧
      (∀ r, θ.toEquiv (.del r) = .del r) ∧ (∀ r, θ.toEquiv (.del' r) = .del' r) := by
  have u := hc.urbanFacts hG
  have hbd : ∀ d, G.IsBoundaryVertex (G.vertexOf d) → G.urbanRenewalPerm c d = d :=
    fun _ h => u.perm_eq hG h
  have hcol : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) →
      G.colour (G.urbanRenewalPerm c d) = G.colour d := fun _ _ => u.colour_perm hG
  have hδ := (hG.isDigon_tripleOfNormal_iff
    {.plus ⟨G.inv (G.squareCorner c 3), hc.inv_squareCorner_three_mem_blackDarts hG⟩,
      .plus ⟨G.inv (G.squareCorner c 1), hc.inv_squareCorner_one_mem_blackDarts hG⟩}).2
    (Or.inl ⟨c, hc, _, _, rfl, rfl, rfl⟩)
  have hf := TripleData.IsDigon.eq_faceOf hδ (mem_insert_self _ _)
  have hd := hf ▸ hδ
  refine ⟨Finset.ext (mem_blackDarts_rewire_iff hbd hcol hG), hf.symm, hd, ?_⟩
  exact u.exists_iso hG (hc.isNormalPlabicPregraph_urbanRenewal hG)
    (by change G.inv (G.squareCorner c 3) = _; rw [squareCorner_three_eq]) hd

/-- **Urban renewal gives a normal plabic graph**: for a face `c` with `G.IsUrbanRenewalFace c`,
the urban renewal of a normal plabic graph is a normal plabic graph. -/
@[cluster_algebras "lem_urban_renewal_normal"]
theorem IsUrbanRenewalFace.isNormalPlabicGraph_urbanRenewal (hG : G.IsNormalPlabicGraph) {c : H}
    (hc : G.IsUrbanRenewalFace c) : (G.urbanRenewal c).IsNormalPlabicGraph := by
  obtain ⟨-, -, hd, θ, -⟩ := hc.exists_iso_swivelMove hG
  have hP' := hc.isNormalPlabicPregraph_urbanRenewal hG
  exact hP'.isNormalPlabicGraph_of_isTripleDiagram (isTripleDiagram_of_iso θ
    hP'.isPreTripleDiagram_tripleOfNormal
    (TripleData.IsDigon.isTripleDiagram_swivelMove hG.isTripleDiagram_tripleOfNormal hd))

/-- **A normal flip is a swivel move**: for a dart `k` with `G.IsNormalFlipVertex k`, let `G'` be
the normal flip of the normal plabic graph `G` at `u = {k, σk}`. Then `G'` has the darts at black
vertices of `G`, the set `{x⁻_k, x⁻_{σk}}` is a digon of `X(G)` (the orbit of `φ` through `x⁻_k`),
and `X(G')` is the swivel move of `X(G)` at this digon: the identification `x^±_{k'} ↦ x^±_{k'}`,
`∂_r ↦ ∂_r`, `∂'_r ↦ ∂'_r` of their darts is an isomorphism of pre-triple diagrams. -/
@[cluster_algebras "lem_normal_flip_swivel"]
theorem IsNormalFlipVertex.exists_iso_swivelMove (hG : G.IsNormalPlabicGraph) {k : H}
    (hk : G.IsNormalFlipVertex k) :
    (G.normalFlip k).blackDarts = G.blackDarts ∧
    (G.tripleOfNormal hG.isNormalPlabicPregraph).faceOf (.minus ⟨k, hk.mem_blackDarts⟩) =
      {.minus ⟨k, hk.mem_blackDarts⟩,
        .minus ⟨G.rot k, hG.isNormalPlabicPregraph.rot_mem_blackDarts hk.mem_blackDarts⟩} ∧
    (G.tripleOfNormal hG.isNormalPlabicPregraph).IsDigon
      ((G.tripleOfNormal hG.isNormalPlabicPregraph).faceOf (.minus ⟨k, hk.mem_blackDarts⟩)) ∧
    ∃ θ : ((G.normalFlip k).tripleOfNormal (hk.isNormalPlabicPregraph_normalFlip hG)).Iso
        ((G.tripleOfNormal hG.isNormalPlabicPregraph).swivelMove (.minus ⟨k, hk.mem_blackDarts⟩)),
      (∀ (k' : (G.normalFlip k).BlackDart) (hk' : (k' : H) ∈ G.blackDarts),
        θ.toEquiv (.plus k') = .plus ⟨k', hk'⟩ ∧ θ.toEquiv (.minus k') = .minus ⟨k', hk'⟩) ∧
      (∀ r, θ.toEquiv (.del r) = .del r) ∧ (∀ r, θ.toEquiv (.del' r) = .del' r) := by
  have u := hk.flipFacts hG
  have hbd : ∀ d, G.IsBoundaryVertex (G.vertexOf d) → G.normalFlipPerm k d = d :=
    fun _ h => u.perm_eq hG h
  have hcol : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) →
      G.colour (G.normalFlipPerm k d) = G.colour d := fun _ _ => u.colour_perm hG
  have hδ := (hG.isDigon_tripleOfNormal_iff
    {.minus ⟨k, hk.mem_blackDarts⟩,
      .minus ⟨G.rot k, hG.isNormalPlabicPregraph.rot_mem_blackDarts hk.mem_blackDarts⟩}).2
    (Or.inr ⟨k, hk, _, _, rfl, rfl, rfl⟩)
  have hf := TripleData.IsDigon.eq_faceOf hδ (mem_insert_self _ _)
  have hd := hf ▸ hδ
  refine ⟨Finset.ext (mem_blackDarts_rewire_iff hbd hcol hG), hf.symm, hd, ?_⟩
  exact u.exists_iso hG (hk.isNormalPlabicPregraph_normalFlip hG)
    (k₁ := ⟨k, hk.mem_blackDarts⟩) (by change k = _; rw [hG.inv_involutive]) hd

/-- **A normal flip gives a normal plabic graph**: for a dart `k` with `G.IsNormalFlipVertex k`,
the normal flip of a normal plabic graph is a normal plabic graph. -/
@[cluster_algebras "lem_normal_flip_normal"]
theorem IsNormalFlipVertex.isNormalPlabicGraph_normalFlip (hG : G.IsNormalPlabicGraph) {k : H}
    (hk : G.IsNormalFlipVertex k) : (G.normalFlip k).IsNormalPlabicGraph := by
  obtain ⟨-, -, hd, θ, -⟩ := hk.exists_iso_swivelMove hG
  have hP' := hk.isNormalPlabicPregraph_normalFlip hG
  exact hP'.isNormalPlabicGraph_of_isTripleDiagram (isTripleDiagram_of_iso θ
    hP'.isPreTripleDiagram_tripleOfNormal
    (TripleData.IsDigon.isTripleDiagram_swivelMove hG.isTripleDiagram_tripleOfNormal hd))

end PlabicData

end ClusterAlgebras

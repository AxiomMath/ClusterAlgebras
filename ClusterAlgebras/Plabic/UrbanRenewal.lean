/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.NormalPlabic
public import ClusterAlgebras.Plabic.SquareTrips

/-!
# Urban renewal and the normal flip

Two local moves act on normal plabic graphs by changing the rotation `σ` and nothing else (the
colours being recomputed from the new vertices). Both have the form `σ' = σ ∘ π` for a product `π`
of disjoint `3`-cycles of darts.

* **Urban renewal.** Let `(c₁, c₂, c₃, c₄)` be an internal face of a normal plabic graph `G`, with
  `c_{k+1} = φ(c_k)` (indices modulo `4`), black corners `v(c₁)`, `v(c₃)` and distinct white
  corners `v(c₂) ≠ v(c₄)`. With `e₂ = σ(c₂)` and `e₄ = σ(c₄)`, the urban renewal of `G` at the face
  has rotation `σ ∘ π`, where `π` is the composite of the cycles
  `(c̄₁ c₂ e₄)`, `(e₂ c̄₃ c₄)`, `(c̄₄ c₁ ē₄)` and `(c̄₂ c₃ ē₂)`. The white vertices exchange the
  edges `c₂` and `c₄`, and the black ends of `c₁`, `c₃` move to the former outer neighbours
  `v(ē₄)`, `v(ē₂)`. The twelve darts moved by `π` are pairwise distinct, so the four cycles are
  disjoint.
* **Normal flip.** Let `u = {k, σ(k)}` be a black vertex with two darts whose neighbours `v(k̄)`,
  `v(\overline{σ k})` are distinct white vertices. With `a₁ = σ(k̄)`, `a₂ = σ(a₁)`,
  `b₁ = σ(\overline{σ k})`, `b₂ = σ(b₁)`, the normal flip of `G` at `u` has rotation `σ ∘ π`, where
  `π` is the composite of the cycles `(k̄ a₁ b₂)` and `(a₂ \overline{σ k} b₁)`.

Two normal plabic graphs are *normal-move-equivalent* if they are joined by a finite sequence of
normal plabic graphs in which each graph is isomorphic to the previous one, or to an urban renewal
or a normal flip of it, or the previous one is isomorphic to an urban renewal or a normal flip of
it.

## Main definitions

* `ClusterAlgebras.PlabicData.rewire`: the tuple `(H, d ↦ d̄, σ ∘ π, B, κ', β)`, where `κ'` colours
  a vertex black when its darts lie at black vertices of `G` and white otherwise.
* `ClusterAlgebras.PlabicData.IsUrbanRenewalFace`, `ClusterAlgebras.PlabicData.urbanRenewalPerm`,
  `ClusterAlgebras.PlabicData.urbanRenewal`: the conditions on the face, the permutation `π` and
  the urban renewal.
* `ClusterAlgebras.PlabicData.IsNormalFlipVertex`, `ClusterAlgebras.PlabicData.normalFlipPerm`,
  `ClusterAlgebras.PlabicData.normalFlip`: the conditions on the vertex, the permutation `π` and
  the normal flip.
* `ClusterAlgebras.PlabicGraph.IsUrbanRenewal`, `ClusterAlgebras.PlabicGraph.IsNormalFlip`,
  `ClusterAlgebras.PlabicGraph.NormalMoveStep`, `ClusterAlgebras.PlabicGraph.NormalMoveEquivalent`:
  normal move equivalence.

## Main results

* `ClusterAlgebras.PlabicData.IsUrbanRenewalFace.nodup`: the twelve darts moved by urban renewal
  are pairwise distinct.
* `ClusterAlgebras.PlabicData.IsUrbanRenewalFace.urbanRenewalPerm_apply`,
  `ClusterAlgebras.PlabicData.IsNormalFlipVertex.normalFlipPerm_apply`: the values of `π` on the
  darts it moves; `urbanRenewalPerm_apply_of_notMem` and `normalFlipPerm_apply_of_notMem`: `π`
  fixes every other dart. `ClusterAlgebras.PlabicData.IsNormalFlipVertex.nodup`: the six darts
  moved by the normal flip are pairwise distinct.
* `ClusterAlgebras.PlabicGraph.NormalMoveEquivalent.symm`,
  `ClusterAlgebras.PlabicGraph.NormalMoveEquivalent.trans`: normal move equivalence is an
  equivalence relation on normal plabic graphs.

## Implementation notes

* **Faces.** The face `(c₁, c₂, c₃, c₄)` is given by its first dart `c = c₁`, and
  `c_{k+1} = squareCorner c k = φ^k(c)` for `k : Fin 4`. The condition `φ^4(c) = c` reads the
  indices modulo `4`. Since `v(c₁)` is black and `v(c₂)` white, and `v(c₂) ≠ v(c₄)`, the orbit of
  `c` under `φ` has exactly four darts, so the face consists of the four darts `c_k`. A black
  (white) vertex is an internal vertex whose darts are black (white).
* **Cycles.** The cyclic permutation `(x y z)` is `List.formPerm [x, y, z]`, and the composite of
  cycles is their product in `Equiv.Perm H`, the rightmost acting first; under the hypotheses the
  cycles are disjoint, so the order is immaterial.
* **Colours.** The constructions are defined for every dart of any tuple of the shape of a plabic
  graph. The colouring `κ'` of `rewire` gives a dart `d` the colour black exactly when every dart
  of the new vertex of `d` lies at a black internal vertex of `G`; at a vertex meeting `B` the
  colour is irrelevant.
* **Normal move equivalence.** Graphs on different dart types are compared as elements of
  `PlabicGraph b`. A finite sequence `G = G₀, …, G_r = G'` of normal plabic graphs whose steps
  satisfy a relation is `G` being normal together with the `Relation.ReflTransGen` of the step
  relation `NormalMoveStep`, each step of which requires both of its ends to be normal.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-! ### Rewiring the rotation -/

/-- The tuple `(H, d ↦ d̄, σ ∘ π, B, κ', β)` obtained from `G` by replacing the rotation `σ` with
`σ ∘ π`. The colouring `κ'` gives a dart the colour black when every dart of its vertex for
`σ ∘ π` lies at a black internal vertex of `G`, and white otherwise. The involution, `B` and the
labelling are those of `G`. -/
@[cluster_algebras "def_urban_renewal"]
def rewire (π : Equiv.Perm H) : PlabicData H b where
  toDiskMap := { G.toDiskMap with rot := G.rot * π }
  colour d :=
    if ∀ e ∈ ({ G.toRotationSystem with rot := G.rot * π } : RotationSystem H).vertexOf d,
        ¬G.IsBoundaryVertex (G.vertexOf e) ∧ G.colour e = .black then .black else .white
  leg := G.leg

variable {G}

/-- Rewiring does not change the involution. -/
@[simp]
theorem inv_rewire (π : Equiv.Perm H) : (G.rewire π).inv = G.inv := rfl

/-- The rotation of `G.rewire π` is `G.rot * π`. -/
@[simp]
theorem rot_rewire (π : Equiv.Perm H) : (G.rewire π).rot = G.rot * π := rfl

/-- The rotation of `G.rewire π` sends `d` to `G.rot (π d)`. -/
theorem rot_rewire_apply (π : Equiv.Perm H) (d : H) : (G.rewire π).rot d = G.rot (π d) := rfl

/-- Rewiring does not change the boundary darts. -/
@[simp]
theorem bdry_rewire (π : Equiv.Perm H) : (G.rewire π).bdry = G.bdry := rfl

/-- Rewiring does not change `leg`. -/
@[simp]
theorem leg_rewire (π : Equiv.Perm H) : (G.rewire π).leg = G.leg := rfl

/-- The colour of a dart of the rewired graph is black exactly when every dart of its new vertex
lies at a black internal vertex of `G`. -/
theorem colour_rewire_eq_black_iff {π : Equiv.Perm H} {d : H} :
    (G.rewire π).colour d = .black ↔
      ∀ e ∈ (G.rewire π).vertexOf d, ¬G.IsBoundaryVertex (G.vertexOf e) ∧ G.colour e = .black := by
  change (if _ then _ else _) = _ ↔ _
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by simp) h

/-- If every dart of the new vertex of `d` lies at an internal vertex of `G` of the colour of `d`,
the rewired graph gives `d` its colour in `G`. -/
theorem colour_rewire_of_forall {π : Equiv.Perm H} {d : H}
    (h : ∀ e ∈ (G.rewire π).vertexOf d,
      ¬G.IsBoundaryVertex (G.vertexOf e) ∧ G.colour e = G.colour d) :
    (G.rewire π).colour d = G.colour d := by
  cases hd : G.colour d
  · cases hd' : (G.rewire π).colour d
    · rfl
    · simpa [hd] using
        (colour_rewire_eq_black_iff.1 hd' d (RotationSystem.self_mem_vertexOf _ d)).2.symm
  · exact colour_rewire_eq_black_iff.2 fun e he => hd ▸ h e he

/-! ### Products of disjoint `3`-cycles -/

omit [Fintype H] in
/-- A product of two disjoint `3`-cycles `(a₁ a₂ a₃)(a₄ a₅ a₆)` maps each `a_i` to the next dart
of its cycle. -/
private theorem formPerm_mul_formPerm_apply {a₁ a₂ a₃ a₄ a₅ a₆ : H}
    (h : [a₁, a₂, a₃, a₄, a₅, a₆].Nodup) :
    let π := [a₁, a₂, a₃].formPerm * [a₄, a₅, a₆].formPerm
    π a₁ = a₂ ∧ π a₂ = a₃ ∧ π a₃ = a₁ ∧ π a₄ = a₅ ∧ π a₅ = a₆ ∧ π a₆ = a₄ := by
  intro π
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨h12, h13, h14, h15, h16⟩, ⟨h23, h24, h25, h26⟩, ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56⟩ := h
  simp only [π, Equiv.Perm.mul_apply, List.formPerm_cons_cons, List.formPerm_singleton,
    Equiv.Perm.one_apply, Equiv.swap_apply_def]
  simp_all [eq_comm]

omit [Fintype H] in
/-- A product of four disjoint `3`-cycles maps each of their twelve darts to the next dart of its
cycle. -/
private theorem formPerm_mul_four_apply {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ : H}
    (h : [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂].Nodup) :
    let π := [a₁, a₂, a₃].formPerm * [a₄, a₅, a₆].formPerm * [a₇, a₈, a₉].formPerm *
      [a₁₀, a₁₁, a₁₂].formPerm
    π a₁ = a₂ ∧ π a₂ = a₃ ∧ π a₃ = a₁ ∧ π a₄ = a₅ ∧ π a₅ = a₆ ∧ π a₆ = a₄ ∧
      π a₇ = a₈ ∧ π a₈ = a₉ ∧ π a₉ = a₇ ∧ π a₁₀ = a₁₁ ∧ π a₁₁ = a₁₂ ∧ π a₁₂ = a₁₀ := by
  intro π
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨h12, h13, h14, h15, h16, h17, h18, h19, h110, h111, h112⟩,
    ⟨h23, h24, h25, h26, h27, h28, h29, h210, h211, h212⟩,
    ⟨h34, h35, h36, h37, h38, h39, h310, h311, h312⟩,
    ⟨h45, h46, h47, h48, h49, h410, h411, h412⟩,
    ⟨h56, h57, h58, h59, h510, h511, h512⟩,
    ⟨h67, h68, h69, h610, h611, h612⟩,
    ⟨h78, h79, h710, h711, h712⟩, ⟨h89, h810, h811, h812⟩, ⟨h910, h911, h912⟩,
    ⟨h1011, h1012⟩, h1112⟩ := h
  simp only [π, Equiv.Perm.mul_apply, List.formPerm_cons_cons, List.formPerm_singleton,
    Equiv.Perm.one_apply, Equiv.swap_apply_def]
  simp_all [eq_comm]

/-! ### Urban renewal -/

variable (G)

/-- The conditions of **urban renewal** at the face `(c₁, c₂, c₃, c₄)` with `c₁ = c` and
`c_{k+1} = φ(c_k)`, that is `c_{k+1} = squareCorner c k`: the face through `c` is an internal face,
`φ^4(c) = c` (indices are read modulo `4`), the vertices `v(c₁)`, `v(c₃)` are black and `v(c₂)`,
`v(c₄)` are white (all four are internal), and `v(c₂) ≠ v(c₄)`. -/
@[cluster_algebras "def_urban_renewal"]
structure IsUrbanRenewalFace (c : H) : Prop where
  /-- The face through `c` is an internal face. -/
  faceOf_mem_internalFaces : G.faceOf c ∈ G.internalFaces
  /-- `c₅ = φ^4(c) = c₁`. -/
  facePerm_pow_four : (G.facePerm ^ 4) c = c
  /-- Each `v(c_k)` is an internal vertex. -/
  not_isBoundaryVertex : ∀ k, ¬G.IsBoundaryVertex (G.vertexOf (G.squareCorner c k))
  /-- `v(c₁)` is black. -/
  colour_squareCorner_zero : G.colour (G.squareCorner c 0) = .black
  /-- `v(c₂)` is white. -/
  colour_squareCorner_one : G.colour (G.squareCorner c 1) = .white
  /-- `v(c₃)` is black. -/
  colour_squareCorner_two : G.colour (G.squareCorner c 2) = .black
  /-- `v(c₄)` is white. -/
  colour_squareCorner_three : G.colour (G.squareCorner c 3) = .white
  /-- `v(c₂) ≠ v(c₄)`. -/
  vertexOf_ne : G.vertexOf (G.squareCorner c 1) ≠ G.vertexOf (G.squareCorner c 3)

/-- The permutation `π` of **urban renewal** at the face `(c₁, c₂, c₃, c₄)` with `c₁ = c`: with
`e₂ = σ(c₂)` and `e₄ = σ(c₄)`, the composite of the cycles `(c̄₁ c₂ e₄)`, `(e₂ c̄₃ c₄)`,
`(c̄₄ c₁ ē₄)` and `(c̄₂ c₃ ē₂)`. -/
@[cluster_algebras "def_urban_renewal"]
def urbanRenewalPerm (c : H) : Equiv.Perm H :=
  [G.inv c, G.squareCorner c 1, G.rot (G.squareCorner c 3)].formPerm *
    [G.rot (G.squareCorner c 1), G.inv (G.squareCorner c 2), G.squareCorner c 3].formPerm *
    [G.inv (G.squareCorner c 3), c, G.inv (G.rot (G.squareCorner c 3))].formPerm *
    [G.inv (G.squareCorner c 1), G.squareCorner c 2, G.inv (G.rot (G.squareCorner c 1))].formPerm

/-- The **urban renewal** of `G` at the face `(c₁, c₂, c₃, c₄)` with `c₁ = c`: the tuple
`(H, d ↦ d̄, σ ∘ π, B, κ', β)` with `π = urbanRenewalPerm c`, where `κ'` colours a vertex black if
its darts lie at black vertices of `G` and white otherwise. It is meaningful for a normal plabic
graph `G` and a face satisfying `G.IsUrbanRenewalFace c`. -/
@[cluster_algebras "def_urban_renewal"]
def urbanRenewal (c : H) : PlabicData H b := G.rewire (G.urbanRenewalPerm c)

variable {G}

/-- The rotation of the urban renewal is `σ ∘ π`. -/
theorem rot_urbanRenewal (c : H) : (G.urbanRenewal c).rot = G.rot * G.urbanRenewalPerm c := rfl

omit [Fintype H] in
/-- `π` fixes every dart other than the twelve darts it moves. -/
theorem urbanRenewalPerm_apply_of_notMem {c x : H}
    (h : x ∉ [G.inv c, G.squareCorner c 1, G.rot (G.squareCorner c 3),
      G.rot (G.squareCorner c 1), G.inv (G.squareCorner c 2), G.squareCorner c 3,
      G.inv (G.squareCorner c 3), c, G.inv (G.rot (G.squareCorner c 3)),
      G.inv (G.squareCorner c 1), G.squareCorner c 2, G.inv (G.rot (G.squareCorner c 1))]) :
    G.urbanRenewalPerm c x = x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  simp only [urbanRenewalPerm, Equiv.Perm.mul_apply]
  rw [List.formPerm_apply_of_notMem (x := x) (by simp [h10, h11, h12]),
    List.formPerm_apply_of_notMem (x := x) (by simp [h7, h8, h9]),
    List.formPerm_apply_of_notMem (x := x) (by simp [h4, h5, h6]),
    List.formPerm_apply_of_notMem (x := x) (by simp [h1, h2, h3])]

/-- At a white vertex, the darts `x`, `σ(x)`, `σ²(x)` (with `σ(x)` at the vertex) are pairwise
distinct. -/
private theorem rot_ne_of_white (hG : G.IsNormalPlabicGraph) {x : H}
    (hint : ¬G.IsBoundaryVertex (G.vertexOf (G.rot x))) (hcol : G.colour (G.rot x) = .white) :
    G.rot x ≠ x ∧ G.rot (G.rot x) ≠ x ∧ G.rot (G.rot x) ≠ G.rot x := by
  have hcard := hG.card_vertexOf_of_white _ hint hcol
  rw [G.vertexOf_rot] at hcard
  obtain ⟨h1, h2⟩ := rot_ne_of_card_vertexOf_eq_three hcard
  exact ⟨h1, h2, fun h => h1 (G.rot.injective h)⟩

/-- Every dart of a white vertex is white, and its reverse lies at a black vertex. -/
private theorem colour_of_mem_white (hG : G.IsNormalPlabicGraph) {y z : H}
    (hint : ¬G.IsBoundaryVertex (G.vertexOf y)) (hcol : G.colour y = .white)
    (hz : z ∈ G.vertexOf y) : G.colour z = .white ∧ G.colour (G.inv z) = .black := by
  have hzint : ¬G.IsBoundaryVertex (G.vertexOf z) := by rwa [G.vertexOf_eq_of_mem hz]
  have hzw : G.colour z = .white := by
    obtain ⟨n, rfl⟩ := (G.mem_vertexOf.1 hz).exists_nat_pow_eq
    clear hz hzint
    induction n with
    | zero => simpa using hcol
    | succ n ih =>
      have hn : ¬G.IsBoundaryVertex (G.vertexOf ((G.rot ^ n) y)) := by
        rwa [G.vertexOf_eq_of_mem (G.mem_vertexOf.2
          (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)))]
      rw [pow_succ', Equiv.Perm.mul_apply, hG.colour_rot _ hn, ih]
  exact ⟨hzw, (hG.inv_internal_black_of_white hzint hzw).2⟩

/-- The twelve darts of `IsUrbanRenewalFace.nodup`, written with `x = c̄₁` and `y = c̄₃`, are
pairwise distinct when `v(σ x)` and `v(σ y)` are distinct white vertices. -/
private theorem nodup_twelve (hG : G.IsNormalPlabicGraph) {x y : H}
    (hxi : ¬G.IsBoundaryVertex (G.vertexOf (G.rot x))) (hxc : G.colour (G.rot x) = .white)
    (hyi : ¬G.IsBoundaryVertex (G.vertexOf (G.rot y))) (hyc : G.colour (G.rot y) = .white)
    (hxy : G.vertexOf (G.rot x) ≠ G.vertexOf (G.rot y)) :
    [x, G.rot x, G.rot (G.rot y), G.rot (G.rot x), y, G.rot y,
      G.inv (G.rot y), G.inv x, G.inv (G.rot (G.rot y)), G.inv (G.rot x), G.inv y,
      G.inv (G.rot (G.rot x))].Nodup := by
  obtain ⟨hx1, hx2, hx3⟩ := rot_ne_of_white hG hxi hxc
  obtain ⟨hy1, hy2, hy3⟩ := rot_ne_of_white hG hyi hyc
  have mx₁ : x ∈ G.vertexOf (G.rot x) := G.vertexOf_rot x ▸ G.self_mem_vertexOf x
  have mx₂ := G.self_mem_vertexOf (G.rot x)
  have mx₃ := G.rot_mem_vertexOf (G.rot x)
  have my₁ : y ∈ G.vertexOf (G.rot y) := G.vertexOf_rot y ▸ G.self_mem_vertexOf y
  have my₂ := G.self_mem_vertexOf (G.rot y)
  have my₃ := G.rot_mem_vertexOf (G.rot y)
  have cross : ∀ a ∈ G.vertexOf (G.rot x), ∀ a' ∈ G.vertexOf (G.rot y), a ≠ a' := by
    rintro a ha a' ha' rfl
    exact hxy ((G.vertexOf_eq_of_mem ha).symm.trans (G.vertexOf_eq_of_mem ha'))
  have c11 := cross _ mx₁ _ my₁
  have c12 := cross _ mx₁ _ my₂
  have c13 := cross _ mx₁ _ my₃
  have c21 := cross _ mx₂ _ my₁
  have c22 := cross _ mx₂ _ my₂
  have c23 := cross _ mx₂ _ my₃
  have c31 := cross _ mx₃ _ my₁
  have c32 := cross _ mx₃ _ my₂
  have c33 := cross _ mx₃ _ my₃
  have hM : [G.rot y, x, G.rot (G.rot y), G.rot x, y, G.rot (G.rot x)].Nodup := by
    simp [hx1.symm, hx2.symm, hx3.symm, hy1, hy2, hy3.symm, c11, c12.symm, c13, c21, c22.symm,
      c23.symm, c31.symm, c32.symm, c33.symm]
  have hL : [x, G.rot x, G.rot (G.rot y), G.rot (G.rot x), y, G.rot y].Nodup := by
    simp [hx1.symm, hx2.symm, hx3.symm, hy1.symm, hy2, hy3, c11, c12, c13, c21, c22, c23, c31,
      c32, c33.symm]
  have hcol : ∀ z ∈ [x, G.rot x, G.rot (G.rot x)] ++ [y, G.rot y, G.rot (G.rot y)],
      G.colour z = .white ∧ G.colour (G.inv z) = .black := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro z ((rfl | rfl | rfl) | (rfl | rfl | rfl))
    exacts [colour_of_mem_white hG hxi hxc mx₁, colour_of_mem_white hG hxi hxc mx₂,
      colour_of_mem_white hG hxi hxc mx₃, colour_of_mem_white hG hyi hyc my₁,
      colour_of_mem_white hG hyi hyc my₂, colour_of_mem_white hG hyi hyc my₃]
  change ([x, G.rot x, G.rot (G.rot y), G.rot (G.rot x), y, G.rot y] ++
    [G.rot y, x, G.rot (G.rot y), G.rot x, y, G.rot (G.rot x)].map G.inv).Nodup
  refine List.nodup_append.2 ⟨hL, hM.map G.inv.injective, ?_⟩
  intro a ha a' ha' h
  have hw : G.colour a = .white := (hcol a (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at ha ⊢
    tauto)).1
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha'
  have hb : G.colour (G.inv z) = .black := (hcol z (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hz ⊢
    tauto)).2
  simp [h, hb] at hw

/-- **The darts moved by urban renewal**: in a normal plabic graph, at a face `(c₁, c₂, c₃, c₄)`
satisfying `IsUrbanRenewalFace` (with `c₁ = c`, `e₂ = σ(c₂)`, `e₄ = σ(c₄)`), the twelve darts
`c̄₁, c₂, e₄, e₂, c̄₃, c₄, c̄₄, c₁, ē₄, c̄₂, c₃, ē₂` are pairwise distinct. -/
@[cluster_algebras "lem_urban_renewal_darts"]
theorem IsUrbanRenewalFace.nodup (hG : G.IsNormalPlabicGraph) {c : H}
    (hc : G.IsUrbanRenewalFace c) :
    [G.inv c, G.squareCorner c 1, G.rot (G.squareCorner c 3),
      G.rot (G.squareCorner c 1), G.inv (G.squareCorner c 2), G.squareCorner c 3,
      G.inv (G.squareCorner c 3), c, G.inv (G.rot (G.squareCorner c 3)),
      G.inv (G.squareCorner c 1), G.squareCorner c 2,
      G.inv (G.rot (G.squareCorner c 1))].Nodup := by
  have h₂ : G.squareCorner c 1 = G.rot (G.inv c) := by
    simp [squareCorner, G.facePerm_apply]
  have h₄ : G.squareCorner c 3 = G.rot (G.inv (G.squareCorner c 2)) := by
    simp [squareCorner, pow_succ', G.facePerm_apply]
  have key := nodup_twelve hG (x := G.inv c) (y := G.inv (G.squareCorner c 2))
    (h₂ ▸ hc.not_isBoundaryVertex 1) (h₂ ▸ hc.colour_squareCorner_one)
    (h₄ ▸ hc.not_isBoundaryVertex 3) (h₄ ▸ hc.colour_squareCorner_three)
    (h₂ ▸ h₄ ▸ hc.vertexOf_ne)
  rwa [← h₂, ← h₄, hG.inv_involutive c, hG.inv_involutive] at key

/-- The values of the permutation `π` of urban renewal on the darts it moves: it is the product of
the four disjoint cycles `(c̄₁ c₂ e₄)`, `(e₂ c̄₃ c₄)`, `(c̄₄ c₁ ē₄)` and `(c̄₂ c₃ ē₂)`, with
`e₂ = σ(c₂)` and `e₄ = σ(c₄)`. -/
theorem IsUrbanRenewalFace.urbanRenewalPerm_apply (hG : G.IsNormalPlabicGraph) {c : H}
    (hc : G.IsUrbanRenewalFace c) :
    let π := G.urbanRenewalPerm c
    π (G.inv c) = G.squareCorner c 1 ∧
      π (G.squareCorner c 1) = G.rot (G.squareCorner c 3) ∧
      π (G.rot (G.squareCorner c 3)) = G.inv c ∧
      π (G.rot (G.squareCorner c 1)) = G.inv (G.squareCorner c 2) ∧
      π (G.inv (G.squareCorner c 2)) = G.squareCorner c 3 ∧
      π (G.squareCorner c 3) = G.rot (G.squareCorner c 1) ∧
      π (G.inv (G.squareCorner c 3)) = c ∧
      π c = G.inv (G.rot (G.squareCorner c 3)) ∧
      π (G.inv (G.rot (G.squareCorner c 3))) = G.inv (G.squareCorner c 3) ∧
      π (G.inv (G.squareCorner c 1)) = G.squareCorner c 2 ∧
      π (G.squareCorner c 2) = G.inv (G.rot (G.squareCorner c 1)) ∧
      π (G.inv (G.rot (G.squareCorner c 1))) = G.inv (G.squareCorner c 1) :=
  formPerm_mul_four_apply (hc.nodup hG)

/-! ### The normal flip -/

variable (G)

/-- The conditions of the **normal flip** at the vertex `u = v(k)`: `u` is a black (internal)
vertex consisting of exactly two darts `k` and `σ(k)`, and `v(k̄)` and `v(\overline{σ k})` are
distinct white (internal) vertices. -/
@[cluster_algebras "def_normal_flip"]
structure IsNormalFlipVertex (k : H) : Prop where
  /-- `u = v(k)` is an internal vertex. -/
  not_isBoundaryVertex : ¬G.IsBoundaryVertex (G.vertexOf k)
  /-- `u` is black. -/
  colour_eq : G.colour k = .black
  /-- `u` consists of exactly two darts, `k` and `σ(k)`. -/
  card_vertexOf : (G.vertexOf k).card = 2
  /-- `v(k̄)` is an internal vertex. -/
  not_isBoundaryVertex_inv : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k))
  /-- `v(k̄)` is white. -/
  colour_inv : G.colour (G.inv k) = .white
  /-- `v(\overline{σ k})` is an internal vertex. -/
  not_isBoundaryVertex_inv_rot : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.rot k)))
  /-- `v(\overline{σ k})` is white. -/
  colour_inv_rot : G.colour (G.inv (G.rot k)) = .white
  /-- `v(k̄) ≠ v(\overline{σ k})`. -/
  vertexOf_inv_ne : G.vertexOf (G.inv k) ≠ G.vertexOf (G.inv (G.rot k))

/-- The permutation `π` of the **normal flip** at `u = {k, σ(k)}`: with `a₁ = σ(k̄)`,
`a₂ = σ(a₁)`, `b₁ = σ(\overline{σ k})` and `b₂ = σ(b₁)`, the composite of the cycles `(k̄ a₁ b₂)`
and `(a₂ \overline{σ k} b₁)`. -/
@[cluster_algebras "def_normal_flip"]
def normalFlipPerm (k : H) : Equiv.Perm H :=
  [G.inv k, G.rot (G.inv k), G.rot (G.rot (G.inv (G.rot k)))].formPerm *
    [G.rot (G.rot (G.inv k)), G.inv (G.rot k), G.rot (G.inv (G.rot k))].formPerm

/-- The **normal flip** of `G` at `u = {k, σ(k)}`: the tuple `(H, d ↦ d̄, σ ∘ π, B, κ', β)` with
`π = normalFlipPerm k` and `κ'` as for urban renewal. It is meaningful for a normal plabic graph
`G` and a vertex satisfying `G.IsNormalFlipVertex k`. -/
@[cluster_algebras "def_normal_flip"]
def normalFlip (k : H) : PlabicData H b := G.rewire (G.normalFlipPerm k)

variable {G}

/-- The rotation of the normal flip is `σ ∘ π`. -/
theorem rot_normalFlip (k : H) : (G.normalFlip k).rot = G.rot * G.normalFlipPerm k := rfl

omit [Fintype H] in
/-- `π` fixes every dart other than the six darts it moves. -/
theorem normalFlipPerm_apply_of_notMem {k x : H}
    (h : x ∉ [G.inv k, G.rot (G.inv k), G.rot (G.rot (G.inv (G.rot k))),
      G.rot (G.rot (G.inv k)), G.inv (G.rot k), G.rot (G.inv (G.rot k))]) :
    G.normalFlipPerm k x = x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [normalFlipPerm, Equiv.Perm.mul_apply]
  rw [List.formPerm_apply_of_notMem (x := x) (by simp [h4, h5, h6]),
    List.formPerm_apply_of_notMem (x := x) (by simp [h1, h2, h3])]

/-- The six darts moved by the normal flip at `u = {k, σ(k)}`, namely
`k̄, a₁, b₂, a₂, \overline{σ k}, b₁`, are pairwise distinct: they are the darts of the two distinct
white vertices `v(k̄)` and `v(\overline{σ k})`, each with three darts. -/
theorem IsNormalFlipVertex.nodup (hG : G.IsNormalPlabicGraph) {k : H}
    (hk : G.IsNormalFlipVertex k) :
    [G.inv k, G.rot (G.inv k), G.rot (G.rot (G.inv (G.rot k))), G.rot (G.rot (G.inv k)),
      G.inv (G.rot k), G.rot (G.inv (G.rot k))].Nodup :=
  (nodup_twelve hG (x := G.inv k) (y := G.inv (G.rot k))
    (G.vertexOf_rot (G.inv k) ▸ hk.not_isBoundaryVertex_inv)
    ((hG.colour_rot _ hk.not_isBoundaryVertex_inv).trans hk.colour_inv)
    (G.vertexOf_rot (G.inv (G.rot k)) ▸ hk.not_isBoundaryVertex_inv_rot)
    ((hG.colour_rot _ hk.not_isBoundaryVertex_inv_rot).trans hk.colour_inv_rot)
    (G.vertexOf_rot (G.inv k) ▸ G.vertexOf_rot (G.inv (G.rot k)) ▸ hk.vertexOf_inv_ne)).sublist
    (List.sublist_append_left _ _)

/-- The values of the permutation `π` of the normal flip on the darts it moves: it is the product
of the two disjoint cycles `(k̄ a₁ b₂)` and `(a₂ \overline{σ k} b₁)`, with `a₁ = σ(k̄)`,
`a₂ = σ(a₁)`, `b₁ = σ(\overline{σ k})` and `b₂ = σ(b₁)`. -/
theorem IsNormalFlipVertex.normalFlipPerm_apply (hG : G.IsNormalPlabicGraph) {k : H}
    (hk : G.IsNormalFlipVertex k) :
    let π := G.normalFlipPerm k
    π (G.inv k) = G.rot (G.inv k) ∧
      π (G.rot (G.inv k)) = G.rot (G.rot (G.inv (G.rot k))) ∧
      π (G.rot (G.rot (G.inv (G.rot k)))) = G.inv k ∧
      π (G.rot (G.rot (G.inv k))) = G.inv (G.rot k) ∧
      π (G.inv (G.rot k)) = G.rot (G.inv (G.rot k)) ∧
      π (G.rot (G.inv (G.rot k))) = G.rot (G.rot (G.inv k)) :=
  formPerm_mul_formPerm_apply (hk.nodup hG)

end PlabicData

/-! ### Normal move equivalence -/

namespace PlabicGraph

variable {b : ℕ}

/-- `G'` is isomorphic to an **urban renewal** of `G`: to the urban renewal of `G` at a face
satisfying `PlabicData.IsUrbanRenewalFace`. -/
@[cluster_algebras "def_normal_move_equivalent"]
def IsUrbanRenewal (G G' : PlabicGraph b) : Prop :=
  ∃ c, G.data.IsUrbanRenewalFace c ∧ G'.data.Isomorphic (G.data.urbanRenewal c)

/-- `G'` is isomorphic to a **normal flip** of `G`: to the normal flip of `G` at a vertex
satisfying `PlabicData.IsNormalFlipVertex`. -/
@[cluster_algebras "def_normal_move_equivalent"]
def IsNormalFlip (G G' : PlabicGraph b) : Prop :=
  ∃ k, G.data.IsNormalFlipVertex k ∧ G'.data.Isomorphic (G.data.normalFlip k)

/-- A **step** of normal move equivalence: `G` and `G'` are normal plabic graphs, and `G'` is
isomorphic to `G`, or `G'` is isomorphic to an urban renewal or a normal flip of `G`, or `G` is
isomorphic to an urban renewal or a normal flip of `G'`. -/
@[cluster_algebras "def_normal_move_equivalent"]
def NormalMoveStep (G G' : PlabicGraph b) : Prop :=
  G.data.IsNormalPlabicGraph ∧ G'.data.IsNormalPlabicGraph ∧
    (G'.Isomorphic G ∨ (G.IsUrbanRenewal G' ∨ G.IsNormalFlip G') ∨
      (G'.IsUrbanRenewal G ∨ G'.IsNormalFlip G))

/-- **Normal move equivalence**: two normal plabic graphs `G` and `G'` are normal-move-equivalent
if there is a finite sequence `G = G₀, G₁, …, G_r = G'` of normal plabic graphs such that for each
`t ∈ [1, r]`, `G_t` is isomorphic to `G_{t-1}`, or `G_t` is isomorphic to an urban renewal or a
normal flip of `G_{t-1}`, or `G_{t-1}` is isomorphic to an urban renewal or a normal flip of
`G_t`. -/
@[cluster_algebras "def_normal_move_equivalent"]
def NormalMoveEquivalent (G G' : PlabicGraph b) : Prop :=
  G.data.IsNormalPlabicGraph ∧ Relation.ReflTransGen NormalMoveStep G G'

/-- Each step of normal move equivalence can be reversed. -/
theorem NormalMoveStep.symm {G G' : PlabicGraph b} (h : NormalMoveStep G G') :
    NormalMoveStep G' G := by
  obtain ⟨hG, hG', h⟩ := h
  refine ⟨hG', hG, ?_⟩
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

namespace NormalMoveEquivalent

variable {G G' G'' : PlabicGraph b}

/-- A normal plabic graph is normal-move-equivalent to itself. -/
theorem refl (hG : G.data.IsNormalPlabicGraph) : NormalMoveEquivalent G G :=
  ⟨hG, Relation.ReflTransGen.refl⟩

/-- The first graph of a normal move equivalence is a normal plabic graph. -/
theorem isNormalPlabicGraph_left (h : NormalMoveEquivalent G G') : G.data.IsNormalPlabicGraph :=
  h.1

/-- The last graph of a normal move equivalence is a normal plabic graph. -/
theorem isNormalPlabicGraph_right (h : NormalMoveEquivalent G G') :
    G'.data.IsNormalPlabicGraph := by
  obtain ⟨hG, h⟩ := h
  induction h with
  | refl => exact hG
  | tail _ hs _ => exact hs.2.1

/-- Normal move equivalence is transitive. -/
theorem trans (h : NormalMoveEquivalent G G') (h' : NormalMoveEquivalent G' G'') :
    NormalMoveEquivalent G G'' :=
  ⟨h.1, h.2.trans h'.2⟩

/-- A single normal move step is a normal move equivalence. -/
theorem of_normalMoveStep (h : NormalMoveStep G G') : NormalMoveEquivalent G G' :=
  ⟨h.1, Relation.ReflTransGen.single h⟩

/-- Normal move equivalence is symmetric. -/
theorem symm (h : NormalMoveEquivalent G G') : NormalMoveEquivalent G' G := by
  refine ⟨h.isNormalPlabicGraph_right, ?_⟩
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.head hs.symm ih

/-- Isomorphic normal plabic graphs are normal-move-equivalent. -/
theorem of_isomorphic (hG : G.data.IsNormalPlabicGraph) (hG' : G'.data.IsNormalPlabicGraph)
    (h : G'.Isomorphic G) : NormalMoveEquivalent G G' :=
  of_normalMoveStep ⟨hG, hG', Or.inl h⟩

/-- A normal plabic graph isomorphic to an urban renewal of a normal plabic graph `G` is
normal-move-equivalent to `G`. -/
theorem of_isUrbanRenewal (hG : G.data.IsNormalPlabicGraph) (hG' : G'.data.IsNormalPlabicGraph)
    (h : G.IsUrbanRenewal G') : NormalMoveEquivalent G G' :=
  of_normalMoveStep ⟨hG, hG', Or.inr (Or.inl (Or.inl h))⟩

/-- A normal plabic graph isomorphic to a normal flip of a normal plabic graph `G` is
normal-move-equivalent to `G`. -/
theorem of_isNormalFlip (hG : G.data.IsNormalPlabicGraph) (hG' : G'.data.IsNormalPlabicGraph)
    (h : G.IsNormalFlip G') : NormalMoveEquivalent G G' :=
  of_normalMoveStep ⟨hG, hG', Or.inr (Or.inl (Or.inr h))⟩

end NormalMoveEquivalent

end PlabicGraph

end ClusterAlgebras

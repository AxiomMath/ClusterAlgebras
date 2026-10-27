/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.StrandDiagram
public import ClusterAlgebras.Plabic.NormalTriple
public import ClusterAlgebras.Plabic.CornerMaps
public import ClusterAlgebras.Plabic.SquareTrips
public import ClusterAlgebras.Plabic.Swivel
public import ClusterAlgebras.Plabic.BivalentMoves
public import ClusterAlgebras.Plabic.EdgeContractionMoves

/-!
# Generalized triple diagrams and local moves

A generalized triple diagram of a plabic graph `G` is a pre-triple diagram isomorphic to a strand
diagram `X°(G, D)` of a white datum `D`, provided every trip of `G` contains an initial dart. This
file relates generalized triple diagrams to normal plabic graphs, to flips of the white datum and
to the local moves of plabic graphs.

For a normal plabic graph the crossings are the white vertices, with three darts each, so the only
white datum is empty, and its strand diagram is the triple diagram `X(G)`. Flipping one diagonal of
the corner triangulation at one crossing changes the strand diagram by a swivel move, and since any
two triangulations of a polygon are joined by flips, the generalized triple diagrams of `G` are
unique up to swivel moves and isomorphisms. Removing a bivalent vertex and contracting an edge
between two black vertices do not change the generalized triple diagrams, and a square move at a
face whose first corner is white changes them by a swivel move.

## Main results

* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.isGeneralizedTripleDiagram_tripleOfNormal`: the
  triple diagram of a normal plabic graph is a generalized triple diagram.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset TypeA

/-! ### Isomorphisms out of a strand diagram -/

/-- A bijection intertwining two rotations maps each vertex onto a vertex. -/
private theorem map_vertexOf_of_semiconj' {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {R : RotationSystem α} {R' : RotationSystem β} (θ : α ≃ β)
    (h : ∀ x, θ (R.rot x) = R'.rot (θ x)) (d : α) :
    (R.vertexOf d).map θ.toEmbedding = R'.vertexOf (θ d) := by
  have hp : ∀ (n : ℕ) (x : α), θ ((R.rot ^ n) x) = (R'.rot ^ n) (θ x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      simp only [pow_succ', Equiv.Perm.mul_apply]
      rw [h, ih]
  ext y
  rw [mem_map_equiv, RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf]
  constructor
  · intro hs
    obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← hp, hn, Equiv.apply_symm_apply]⟩
  · intro hs
    obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    apply θ.injective
    rw [hp, hn, Equiv.apply_symm_apply]

/-- A pre-triple diagram isomorphic to a triple diagram is a triple diagram. -/
private theorem isTripleDiagram_of_iso' {b : ℕ} {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {Y : TripleData α b} {X' : TripleData β b} (θ : Y.Iso X')
    (hY : Y.IsPreTripleDiagram) (hX' : X'.IsTripleDiagram) : Y.IsTripleDiagram := by
  have hcard : ∀ (F : α → Finset α) (F' : β → Finset β),
      (∀ d, (F d).map θ.toEquiv.toEmbedding = F' (θ.toEquiv d)) →
        (univ.image F).card = (univ.image F').card := by
    intro F F' h
    have : (univ.image F').image (Finset.map θ.toEquiv.symm.toEmbedding) = univ.image F := by
      ext s
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        refine ⟨θ.toEquiv.symm y, ?_⟩
        rw [← Finset.map_injective θ.toEquiv.toEmbedding |>.eq_iff, h, Finset.map_map]
        simp
      · rintro ⟨x, rfl⟩
        refine ⟨F' (θ.toEquiv x), ⟨_, rfl⟩, ?_⟩
        rw [← h, Finset.map_map]
        simp
    rw [← this, card_image_of_injective _ (Finset.map_injective _)]
  have hv : ∀ d, (Y.vertexOf d).map θ.toEquiv.toEmbedding = X'.vertexOf (θ.toEquiv d) :=
    map_vertexOf_of_semiconj' θ.toEquiv θ.map_rot
  have hf : ∀ d, (Y.faceOf d).map θ.toEquiv.toEmbedding = X'.faceOf (θ.toEquiv d) :=
    fun d => map_vertexOf_of_semiconj' (R := ⟨Y.inv, Y.facePerm⟩) (R' := ⟨X'.inv, X'.facePerm⟩)
      θ.toEquiv θ.map_facePerm d
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
  · have h1 : Y.vertices.card = X'.vertices.card := hcard _ _ hv
    have h2 : Y.edges.card = X'.edges.card := hcard _ _ he
    have h3 : Y.faceOrbits.card = X'.faceOrbits.card := hcard _ _ hf
    rw [h1, h2, h3]
    exact hX'.euler

/-! ### Flips of corner triangulations -/

namespace RotationSystem

variable {H : Type*} {R : RotationSystem H}

/-- Of the listings `(x, y, z)` and `(x, z, y)`, at most one is clockwise. -/
private theorem IsCornerClockwise.not_swap {x y z : H} (h : R.IsCornerClockwise x y z) :
    ¬R.IsCornerClockwise x z y := by
  rintro ⟨j', hj', hj'z, hj'y⟩
  obtain ⟨j, hj, hjy, hjz⟩ := h
  rcases le_or_gt j j' with hle | hlt
  · exact hj'y j hj hle hjy
  · exact hjz j' hj' hlt.le hj'z

variable [DecidableEq H]

/-- **Uniqueness of the flip of a corner triangulation.** If `E` is a corner triangulation of a
set `w` of at least three darts, `s ∈ E`, and both `(E \ {s}) ∪ {t}` and `(E \ {s}) ∪ {t'}` are
corner triangulations with `t, t' ≠ s`, then `t = t'`. -/
private theorem IsCornerTriangulation.eq_of_insert_erase {w : Finset H} {E : Finset (Sym2 H)}
    (hE : R.IsCornerTriangulation w E) (hw : 3 ≤ w.card) {s t t' : Sym2 H} (hs : s ∈ E)
    (ht : t ≠ s) (ht' : t' ≠ s) (h₁ : R.IsCornerTriangulation w (insert t (E.erase s)))
    (h₂ : R.IsCornerTriangulation w (insert t' (E.erase s))) : t = t' := by
  obtain ⟨hEw, m, _, l, hl, hT⟩ := hE
  have hm3 : 3 ≤ m := hl.card_eq ▸ hw
  have lift : ∀ u : Sym2 H, (∀ x ∈ u, x ∈ w) → ∃ u' : Sym2 (ZMod m), u'.map l = u := by
    intro u hu
    induction u using Sym2.ind with
    | _ x y =>
      obtain ⟨i, rfl⟩ := hl.exists_eq (hu x (Sym2.mem_mk_left x y))
      obtain ⟨j, rfl⟩ := hl.exists_eq (hu _ (Sym2.mem_mk_right _ y))
      exact ⟨s(i, j), rfl⟩
  obtain ⟨γ, rfl⟩ := lift s (hEw s hs).2
  obtain ⟨δ, rfl⟩ := lift t (h₁.1 t (mem_insert_self _ _)).2
  obtain ⟨δ', rfl⟩ := lift t' (h₂.1 t' (mem_insert_self _ _)).2
  have hinj := Sym2.map.injective hl.injective
  set T := cornerPullback l E with hTdef
  have hpull : ∀ δ : Sym2 (ZMod m),
      cornerPullback l (insert (δ.map l) (E.erase (γ.map l))) = insert δ (T.erase γ) := by
    intro δ
    ext e
    simp only [hTdef, mem_cornerPullback, mem_insert, mem_erase]
    rw [hinj.eq_iff, hinj.ne_iff]
  have hγ : γ ∈ T := mem_cornerPullback.2 hs
  have hm : 4 ≤ m := by
    by_contra hm
    simp [IsTriangulation.eq_empty_of_eq_three (by omega) hT] at hγ
  have rep : ∀ δ : Sym2 (ZMod m), δ.map l ≠ γ.map l →
      R.IsCornerTriangulation w (insert (δ.map l) (E.erase (γ.map l))) →
      IsFlipReplacement T γ δ := by
    intro δ hne h
    have hT' := h.isTriangulation_cornerPullback hl
    rw [hpull] at hT'
    have hδγ : δ ≠ γ := fun e => hne (by rw [e])
    have hδT : δ ∉ T := by
      intro hδ
      have he : insert δ (T.erase γ) = T.erase γ := insert_eq_of_mem (mem_erase.2 ⟨hδγ, hδ⟩)
      rw [he] at hT'
      obtain ⟨f, hf, hcf⟩ := hT'.maximal γ (hT.isDiagonal γ hγ) (notMem_erase γ T)
      exact hT.noncrossing γ hγ f (mem_of_mem_erase hf) hcf
    exact ⟨hT, hγ, hT'.isDiagonal δ (mem_insert_self _ _), hδT, hT'⟩
  have e := (IsTriangulation.existsUnique_isFlipReplacement hm hT hγ).unique
    (rep δ ht h₁) (rep δ' ht' h₂)
  rw [e]

end RotationSystem

/-- A pair of darts of a three-element set, off the diagonal, is one of its three pairs. -/
private theorem eq_or_of_mem_sym2_three {H : Type*} [DecidableEq H] {x y z : H} {e : Sym2 H}
    (he : e ∈ ({x, y, z} : Finset H).sym2) (hd : ¬e.IsDiag) :
    e = s(x, y) ∨ e = s(x, z) ∨ e = s(y, z) := by
  induction e using Sym2.ind with | _ u v => ?_
  rw [mk_mem_sym2_iff] at he
  obtain ⟨hu, hv⟩ := he
  have huv : u ≠ v := fun h => hd (Sym2.mk_isDiag_iff.2 h)
  simp only [mem_insert, mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first | exact absurd rfl huv | simp [Sym2.eq_swap]

namespace PlabicData

open StrandSymbol

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

section StrandIso

variable (hG : G.IsPlabicGraph) {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D)
  {H' : Type*} [Fintype H'] [DecidableEq H']

/-- An isomorphism out of a strand diagram: a bijection of darts commuting with the involutions
and the rotations, matching the boundaries, the orientations and the darts of the endpoints. -/
private theorem strandDiagram_isomorphic_of (Y : TripleData H' b) (θ : G.StrandDart D ≃ H')
    (hinv : ∀ a, θ ((G.strandDiagram hG hD).inv a) = Y.inv (θ a))
    (hrot : ∀ a, θ ((G.strandDiagram hG hD).rot a) = Y.rot (θ a))
    (hbdry : ∀ a, θ a ∈ Y.bdry ↔ a.1.IsBoundary)
    (hout : ∀ a, ¬a.1.IsBoundary → Y.isOut (θ a) = a.1.isOut)
    (hend : ∀ r, θ ((G.strandDiagram hG hD).endDart r) = Y.endDart r) :
    (G.strandDiagram hG hD).Isomorphic Y :=
  ⟨{ toEquiv := θ
     map_inv := hinv
     map_rot := hrot
     mem_bdry_iff := fun a => by rw [hbdry, mem_strandDiagram_bdry]
     map_isOut := fun a ha => by
       rw [hout a ((mem_strandDiagram_bdry hG hD).not.1 ha), strandDiagram_isOut]
     map_endpoint := fun r => by
       rw [TripleData.endpoint, TripleData.endpoint, map_vertexOf_of_semiconj' θ hrot, hend] }⟩

omit [Fintype H'] [DecidableEq H'] in
/-- To check that a map out of a strand diagram commutes with the involutions, it suffices to
check it on the symbols `x⁺_d`, `y⁺_{s,τ}` and `∂_r`. -/
private theorem strandDiagram_map_inv_of {Y : TripleData H' b} (hY : Function.Involutive Y.inv)
    (θ : G.StrandDart D → H')
    (h : ∀ a : G.StrandDart D, ((∃ d, a.1 = xPlus d) ∨ (∃ s τ, a.1 = yPlus s τ) ∨
      ∃ r, a.1 = bd r) → θ ((G.strandDiagram hG hD).inv a) = Y.inv (θ a))
    (a : G.StrandDart D) : θ ((G.strandDiagram hG hD).inv a) = Y.inv (θ a) := by
  set X := G.strandDiagram hG hD
  have hX : Function.Involutive X.inv := (isPreTripleDiagram_strandDiagram hG hD).inv_involutive
  have hrev : ∀ c : G.StrandDart D, ((∃ d, c.1 = xPlus d) ∨ (∃ s τ, c.1 = yPlus s τ) ∨
      ∃ r, c.1 = bd r) → θ (X.inv (X.inv c)) = Y.inv (θ (X.inv c)) := by
    intro c hc
    rw [hX c, h c hc, hY]
  obtain ⟨a, ha⟩ := a
  cases a with
  | xPlus d => exact h _ (Or.inl ⟨d, rfl⟩)
  | yPlus s τ => exact h _ (Or.inr (Or.inl ⟨s, τ, rfl⟩))
  | bd r => exact h _ (Or.inr (Or.inr ⟨r, rfl⟩))
  | xMinus t =>
    have e : X.inv (X.inv ⟨xMinus t, ha⟩) = ⟨xMinus t, ha⟩ := hX _
    rw [← e]
    exact hrev _ (Or.inl ⟨_, rfl⟩)
  | yMinus s τ =>
    have e : X.inv (X.inv ⟨yMinus s τ, ha⟩) = ⟨yMinus s τ, ha⟩ := hX _
    rw [← e]
    exact hrev _ (Or.inr (Or.inl ⟨_, _, rfl⟩))
  | bd' r =>
    have e : X.inv (X.inv ⟨bd' r, ha⟩) = ⟨bd' r, ha⟩ := hX _
    rw [← e]
    exact hrev _ (Or.inr (Or.inr ⟨_, rfl⟩))

end StrandIso

/-! ### Chains of length one -/

/-- If `d` is not terminal and `T(d)` is, the chain from `d` ends at `T(d)`. -/
theorem chainEnd_eq_tripMap {d : H} (hd : ¬G.IsTerminal d) (hT : G.IsTerminal (G.tripMap d)) :
    G.chainEnd d = G.tripMap d := by
  have hT' : G.IsTerminal (G.tripMap^[1] d) := hT
  have h1 : G.chainLength d ≤ 1 := chainLength_le hT'
  have h0 : G.chainLength d ≠ 0 := by
    intro h
    have := chainLength_spec (G := G) ⟨1, hT'⟩
    rw [h] at this
    exact hd this
  rw [chainEnd_def, show G.chainLength d = 1 by omega]
  rfl

/-! ### The triple diagram of a normal plabic graph -/

/-- In a triangle, the empty set is a triangulation. -/
private theorem isTriangulation_empty_three : IsTriangulation (∅ : Finset (Sym2 (ZMod 3))) where
  isDiagonal := by simp
  noncrossing := by simp
  maximal e he _ := by
    exfalso
    obtain ⟨hs, hside⟩ := he
    induction e using Sym2.ind with | _ u v => ?_
    have huv : u ≠ v := fun h => hs (Sym2.mk_isDiag_iff.2 h)
    have key : ∀ x y : ZMod 3, x ≠ y → y = x + 1 ∨ x = y + 1 := by decide
    exact hside (isSide_mk_iff.2 (key u v huv))

/-- The empty datum has no pair `(s, τ)`. -/
private theorem not_isDatumSegment_empty {s : Sym2 H} {τ : Finset H} :
    ¬G.IsDatumSegment (fun _ => ∅) s τ := by
  rintro ⟨w, -, hs, -⟩
  simp at hs

namespace IsNormalPlabicGraph

variable (hG : G.IsNormalPlabicGraph)

include hG

/-- In a normal plabic graph, a white internal vertex is a crossing. -/
theorem isCrossing_vertexOf {a : H} (ha : ¬G.IsBoundaryVertex (G.vertexOf a))
    (hc : G.colour a = .white) : G.IsCrossing (G.vertexOf a) := by
  refine ⟨G.vertexOf_mem_internalVertices.2 ha, fun d hd => ?_, ?_⟩
  · rw [colour_eq_of_sameCycle hG.toIsPlabicGraph ha ((RotationSystem.mem_vertexOf _).1 hd), hc]
  · rw [hG.card_vertexOf_of_white a ha hc]

/-- In a normal plabic graph, the reverse of a dart at a black vertex lies at a boundary vertex
or at a crossing. -/
theorem isCrossing_or_isBoundaryVertex_inv {k : H} (hk : k ∈ G.blackDarts) :
    G.IsCrossing (G.vertexOf (G.inv k)) ∨ G.IsBoundaryVertex (G.vertexOf (G.inv k)) := by
  by_cases hb : G.IsBoundaryVertex (G.vertexOf (G.inv k))
  · exact Or.inr hb
  · obtain ⟨hki, hkc⟩ := mem_blackDarts.1 hk
    exact Or.inl (hG.isCrossing_vertexOf hb
      (hG.isNormalPlabicPregraph.inv_white_of_black hki hkc hb))

/-- A dart at a black vertex is terminal. -/
theorem isTerminal_of_mem_blackDarts {k : H} (hk : k ∈ G.blackDarts) : G.IsTerminal k :=
  ⟨notMem_bdry_of_mem_blackDarts hk, hG.isCrossing_or_isBoundaryVertex_inv hk⟩

/-- The reverse of a dart at a black vertex is initial. -/
theorem isInitial_inv_of_mem_blackDarts {k : H} (hk : k ∈ G.blackDarts) :
    G.IsInitial (G.inv k) := by
  have hP := hG.toIsPlabicGraph
  have hkB := notMem_bdry_of_mem_blackDarts hk
  have hiB : G.inv k ∉ G.bdry := fun h => hkB (hP.inv_mem_bdry_iff.1 h)
  exact ⟨hiB, (hG.isCrossing_or_isBoundaryVertex_inv hk).imp id (hP.isLeg_of_isBoundaryVertex hiB)⟩

/-- The reverse of an initial dart lies at a black vertex. -/
theorem inv_mem_blackDarts_of_isInitial {d : H} (hd : G.IsInitial d) :
    G.inv d ∈ G.blackDarts := by
  rcases hd.2 with hc | ⟨i, rfl⟩
  · exact mem_blackDarts.2 (hG.inv_internal_black_of_white hc.not_isBoundaryVertex
      (hc.2.1 d (G.self_mem_vertexOf d)))
  · exact hG.isNormalPlabicPregraph.inv_leg_mem_blackDarts i

/-- A terminal dart lies at a black vertex. -/
theorem mem_blackDarts_of_isTerminal {t : H} (ht : G.IsTerminal t) : t ∈ G.blackDarts := by
  have hP := hG.toIsPlabicGraph
  by_cases hb : G.IsBoundaryVertex (G.vertexOf t)
  · exfalso
    obtain ⟨i, rfl⟩ := hP.isLeg_of_isBoundaryVertex ht.1 hb
    rcases ht.2 with hc | hc
    · have := hc.2.1 _ (G.self_mem_vertexOf _)
      rw [hG.colour_inv_leg i] at this
      exact Shade.noConfusion this
    · exact hG.not_isBoundaryVertex_inv_leg i hc
  · refine mem_blackDarts.2 ⟨hb, ?_⟩
    cases hcol : G.colour t with
    | white =>
      exfalso
      obtain ⟨h1, h2⟩ := hG.inv_internal_black_of_white hb hcol
      rcases ht.2 with hc | hc
      · have := hc.2.1 _ (G.self_mem_vertexOf _)
        rw [h2] at this
        exact Shade.noConfusion this
      · exact h1 hc
    | black => rfl

/-- Every trip of a normal plabic graph contains an initial dart. -/
theorem exists_isInitial_mem_trip {d : H} (hd : d ∉ G.bdry) : ∃ e ∈ G.trip d, G.IsInitial e := by
  have hP := hG.toIsPlabicGraph
  by_cases hi : G.IsInitial d
  · exact ⟨d, G.mem_trip_self d, hi⟩
  · have hb : ¬G.IsBoundaryVertex (G.vertexOf d) := fun hb =>
      hi ⟨hd, Or.inr (hP.isLeg_of_isBoundaryVertex hd hb)⟩
    have hk : d ∈ G.blackDarts := by
      refine mem_blackDarts.2 ⟨hb, ?_⟩
      cases hcol : G.colour d with
      | white => exact (hi ⟨hd, Or.inl (hG.isCrossing_vertexOf hb hcol)⟩).elim
      | black => rfl
    exact ⟨G.tripMap d, ⟨1, rfl⟩, (hG.isTerminal_of_mem_blackDarts hk).isInitial_tripMap hP⟩

/-- In a normal plabic graph the empty family is a white datum: every crossing has three darts. -/
theorem isWhiteDatum_empty : G.IsWhiteDatum fun _ => ∅ := by
  intro w hw
  obtain ⟨x, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hw.1).1
  have hx : ¬G.IsBoundaryVertex (G.vertexOf x) := hw.not_isBoundaryVertex
  have h3 : (G.vertexOf x).card = 3 :=
    hG.card_vertexOf_of_white x hx (hw.2.1 x (G.self_mem_vertexOf x))
  refine ⟨by simp, 3, inferInstance, _, RotationSystem.isCornerLabelling_rot_symm_pow x h3, ?_⟩
  have : RotationSystem.cornerPullback (fun i : ZMod 3 => (G.rot.symm ^ i.val) x)
      (∅ : Finset (Sym2 H)) = ∅ := by
    ext e
    simp [RotationSystem.mem_cornerPullback]
  rw [this]
  exact isTriangulation_empty_three

/-- A triangle of the empty white datum is a whole crossing, on which the clockwise successor is
`σ⁻¹`. -/
theorem cornerNext_of_isDatumTriangle_empty {τ : Finset H}
    (hτ : G.IsDatumTriangle (fun _ => ∅) τ) {p : H} (hp : p ∈ τ) :
    τ = G.vertexOf p ∧ ∀ q ∈ τ, G.cornerNext τ q = G.rot.symm q := by
  obtain ⟨w, hw, ht⟩ := hτ
  have hwp := hw.eq_vertexOf (ht.1 hp)
  have hx : ¬G.IsBoundaryVertex (G.vertexOf p) := hwp ▸ hw.not_isBoundaryVertex
  have h3 : (G.vertexOf p).card = 3 :=
    hG.card_vertexOf_of_white p hx (hw.2.1 p (ht.1 hp))
  have hτw : τ = w := eq_of_subset_of_card_le ht.1 (by rw [hwp, h3, ht.2.1])
  refine ⟨hτw.trans hwp, fun q hq => ?_⟩
  refine (hG.isWhiteDatum_empty).cornerNext_eq_rot_symm ⟨w, hw, ht⟩ hq ?_
  rw [hτw, hw.eq_vertexOf (hτw ▸ hq)]
  exact G.rot_symm_mem_vertexOf q

/-- The dart of `X(G)` of a dart of the strand diagram `X°(G, ∅)`: `x⁺_d ↦ x⁺_{d̄}`,
`x⁻_t ↦ x⁻_t`, `∂_r ↦ ∂_r`, `∂'_r ↦ ∂'_r`. -/
private def normalStrandFun : G.StrandDart (fun _ => ∅) → G.TripleDart
  | ⟨xPlus d, h⟩ => .plus ⟨G.inv d, hG.inv_mem_blackDarts_of_isInitial h⟩
  | ⟨xMinus t, h⟩ => .minus ⟨t, hG.mem_blackDarts_of_isTerminal h⟩
  | ⟨yPlus _ _, h⟩ => (not_isDatumSegment_empty h).elim
  | ⟨yMinus _ _, h⟩ => (not_isDatumSegment_empty h).elim
  | ⟨bd r, _⟩ => .del r
  | ⟨bd' r, _⟩ => .del' r

/-- The inverse of `normalStrandFun`. -/
private def normalStrandInvFun : G.TripleDart → G.StrandDart (fun _ => ∅)
  | .plus k => ⟨xPlus (G.inv k), hG.isInitial_inv_of_mem_blackDarts k.2⟩
  | .minus k => ⟨xMinus k, hG.isTerminal_of_mem_blackDarts k.2⟩
  | .del r => ⟨bd r, trivial⟩
  | .del' r => ⟨bd' r, trivial⟩

/-- The bijection between the darts of `X°(G, ∅)` and of `X(G)`. -/
private def normalStrandEquiv : G.StrandDart (fun _ => ∅) ≃ G.TripleDart where
  toFun := normalStrandFun hG
  invFun := normalStrandInvFun hG
  left_inv := by
    rintro ⟨a, ha⟩
    cases a with
    | xPlus d => exact Subtype.ext (congrArg xPlus (hG.inv_involutive d))
    | xMinus t => rfl
    | yPlus s τ => exact (not_isDatumSegment_empty ha).elim
    | yMinus s τ => exact (not_isDatumSegment_empty ha).elim
    | bd r => rfl
    | bd' r => rfl
  right_inv := by
    rintro (k | k | r | r)
    · exact congrArg TripleOfNormalDart.plus (Subtype.ext (hG.inv_involutive k))
    · rfl
    · rfl
    · rfl

private theorem normalStrandEquiv_apply (a : G.StrandDart (fun _ => ∅)) :
    normalStrandEquiv hG a = normalStrandFun hG a := rfl

private theorem normalStrandFun_of_eq_xPlus {a : G.StrandDart (fun _ => ∅)} {d : H}
    (h : a.1 = xPlus d) (hk : G.inv d ∈ G.blackDarts) :
    normalStrandFun hG a = .plus ⟨G.inv d, hk⟩ := by
  obtain ⟨a, ha⟩ := a
  subst h
  rfl

private theorem normalStrandFun_of_eq_xMinus {a : G.StrandDart (fun _ => ∅)} {t : H}
    (h : a.1 = xMinus t) (hk : t ∈ G.blackDarts) :
    normalStrandFun hG a = .minus ⟨t, hk⟩ := by
  obtain ⟨a, ha⟩ := a
  subst h
  rfl

private theorem normalStrandFun_endSymbol (r : Fin (2 * b))
    (h : G.IsStrandSymbol (fun _ => ∅) (G.endSymbol r)) :
    normalStrandFun hG ⟨G.endSymbol r, h⟩ = hG.isNormalPlabicPregraph.endDart r := by
  have hN := hG.isNormalPlabicPregraph
  rcases exists_sourceIndex_or_targetIndex r with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [normalStrandFun_of_eq_xPlus hG (endSymbol_sourceIndex i) (hN.inv_leg_mem_blackDarts i),
      IsNormalPlabicPregraph.endDart_sourceIndex]
    rfl
  · rw [normalStrandFun_of_eq_xMinus hG (endSymbol_targetIndex i) (hN.inv_leg_mem_blackDarts i),
      IsNormalPlabicPregraph.endDart_targetIndex]
    rfl

/-- **The triple diagram of a normal graph is a generalized one**: if `G` is a normal plabic graph,
then `X(G)` is a generalized triple diagram of `G`. -/
@[cluster_algebras "lem_generalized_of_normal"]
theorem isGeneralizedTripleDiagram_tripleOfNormal :
    G.IsGeneralizedTripleDiagram hG.toIsPlabicGraph
      (G.tripleOfNormal hG.isNormalPlabicPregraph) := by
  have hP := hG.toIsPlabicGraph
  have hN := hG.isNormalPlabicPregraph
  have hD := hG.isWhiteDatum_empty
  refine ⟨hN.isPreTripleDiagram_tripleOfNormal, fun d hd => hG.exists_isInitial_mem_trip hd,
    fun _ => ∅, hD, TripleData.Isomorphic.symm _ ?_⟩
  set Y := G.tripleOfNormal hN
  set X := G.strandDiagram hP hD
  refine strandDiagram_isomorphic_of hP hD Y (normalStrandEquiv hG) ?_ ?_ ?_ ?_ ?_
  · refine strandDiagram_map_inv_of hP hD hN.isPreTripleDiagram_tripleOfNormal.inv_involutive
      _ ?_
    rintro ⟨a, ha⟩ (⟨d, rfl⟩ | ⟨s, τ, rfl⟩ | ⟨r, rfl⟩)
    · have hd : G.IsInitial d := ha
      have hk := hG.inv_mem_blackDarts_of_isInitial hd
      obtain ⟨hki, hkc⟩ := mem_blackDarts.1 hk
      have hT : G.tripMap d = G.rot (G.inv d) := turn_of_black hki hkc
      have hnt : ¬G.IsTerminal d := by
        rintro ⟨-, hc | hc⟩
        · have := hc.2.1 _ (G.self_mem_vertexOf _)
          rw [hkc] at this
          exact Shade.noConfusion this
        · exact hki hc
      have hk' : G.rot (G.inv d) ∈ G.blackDarts := hN.rot_mem_blackDarts hk
      have hend : G.chainEnd d = G.rot (G.inv d) := by
        rw [chainEnd_eq_tripMap hnt (hT ▸ hG.isTerminal_of_mem_blackDarts hk'), hT]
      simp only [normalStrandEquiv_apply, IsNormalPlabicPregraph.tripleOfNormal_inv]
      rw [normalStrandFun_of_eq_xMinus hG (t := G.rot (G.inv d)) (by
        rw [strandDiagram_inv_apply]; exact congrArg xMinus hend) hk']
      rfl
    · exact (not_isDatumSegment_empty ha).elim
    · rfl
  · intro a
    simp only [normalStrandEquiv_apply, Y, IsNormalPlabicPregraph.tripleOfNormal_rot]
    rcases strandDart_cases hP hD a with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ |
      ⟨τ, p, hτ, hp, rfl⟩ | ⟨τ, p, hτ, hp, rfl⟩
    · rw [strandDiagram_rot_bd, normalStrandFun_endSymbol]
      rfl
    · rw [strandDiagram_rot_bd']
      rfl
    · rw [strandDiagram_rot_endSymbol, normalStrandFun_endSymbol,
        IsNormalPlabicPregraph.tripleRot_endDart]
      rfl
    · obtain ⟨-, hcn⟩ := hG.cornerNext_of_isDatumTriangle_empty hτ hp
      have hk : G.inv p ∈ G.blackDarts :=
        hG.inv_mem_blackDarts_of_isInitial ⟨hτ.notMem_bdry hp, Or.inl (hτ.vertexOf hp).1⟩
      have h1 : G.pairOut τ p = xPlus p := by rw [pairOut, if_pos (hcn p hp)]
      have h2 : G.pairIn τ p = xMinus (G.inv p) := by rw [pairIn, if_pos (hcn p hp)]
      rw [strandDiagram_rot_pairOut hP hD hτ hp, normalStrandFun_of_eq_xMinus hG h2 hk,
        normalStrandFun_of_eq_xPlus hG h1 hk, IsNormalPlabicPregraph.tripleRot_plus_of_none]
      exact hN.legIndex_eq_none_of_internal (by
        rw [hG.inv_involutive]; exact (hτ.vertexOf hp).1.not_isBoundaryVertex)
    · obtain ⟨hτp, hcn⟩ := hG.cornerNext_of_isDatumTriangle_empty hτ hp
      have hx : ¬G.IsBoundaryVertex (G.vertexOf p) := (hτ.vertexOf hp).1.not_isBoundaryVertex
      have hk : G.inv p ∈ G.blackDarts :=
        hG.inv_mem_blackDarts_of_isInitial ⟨hτ.notMem_bdry hp, Or.inl (hτ.vertexOf hp).1⟩
      have h3 : (G.vertexOf p).card = 3 :=
        hG.card_vertexOf_of_white p hx ((hτ.vertexOf hp).1.2.1 p (G.self_mem_vertexOf p))
      have hq : G.rot.symm p ∈ τ := by rw [hτp]; exact G.rot_symm_mem_vertexOf p
      have hσ : G.rot.symm (G.rot.symm p) = G.rot p := by
        apply G.rot.injective
        apply G.rot.injective
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
          rot_rot_rot_of_card_vertexOf_eq_three h3]
      have hcc : G.cornerNext τ (G.cornerNext τ p) = G.rot p := by
        rw [hcn p hp, hcn _ hq, hσ]
      have hrp : G.rot p ∈ τ := by rw [hτp]; exact G.rot_mem_vertexOf p
      have hk' : G.inv (G.rot p) ∈ G.blackDarts :=
        hG.inv_mem_blackDarts_of_isInitial ⟨hτ.notMem_bdry hrp, Or.inl (hτ.vertexOf hrp).1⟩
      have h1 : G.pairOut τ (G.cornerNext τ (G.cornerNext τ p)) = xPlus (G.rot p) := by
        rw [hcc, pairOut, if_pos (hcn _ hrp)]
      have h2 : G.pairIn τ p = xMinus (G.inv p) := by rw [pairIn, if_pos (hcn p hp)]
      have hnone : G.legIndex (⟨G.inv p, hk⟩ : G.BlackDart) = none := by
        refine hN.legIndex_eq_none_of_internal ?_
        rwa [hG.inv_involutive]
      rw [strandDiagram_rot_pairIn hP hD hτ hp, normalStrandFun_of_eq_xPlus hG h1 hk',
        normalStrandFun_of_eq_xMinus hG h2 hk,
        IsNormalPlabicPregraph.tripleRot_minus_of_none hN hnone]
      congr 1
      exact Subtype.ext (by rw [IsNormalPlabicPregraph.coe_psi, hG.inv_involutive])
  · rintro ⟨a, ha⟩
    cases a with
    | yPlus s τ => exact (not_isDatumSegment_empty ha).elim
    | yMinus s τ => exact (not_isDatumSegment_empty ha).elim
    | _ =>
      simp only [Y, IsNormalPlabicPregraph.mem_tripleOfNormal_bdry]
      simp [normalStrandEquiv, normalStrandFun, StrandSymbol.IsBoundary]
  · rintro ⟨a, ha⟩ -
    cases a with
    | yPlus s τ => exact (not_isDatumSegment_empty ha).elim
    | yMinus s τ => exact (not_isDatumSegment_empty ha).elim
    | _ => rfl
  · intro r
    exact normalStrandFun_endSymbol hG r _

end IsNormalPlabicGraph

/-! ### Flips of a white datum -/

section Flip

open RotationSystem

variable {D D' : Finset H → Finset (Sym2 H)}

/-- The combinatorial data of a flip of a white datum at the crossing `w`: `D'` agrees with `D`
at the other crossings, and `D'_w` is obtained from `D_w` by replacing the diagonal `s = {q₁, q₃}`
of the quadrilateral `(q₁, q₂, q₃, q₄)` by `s' = {q₂, q₄}`; the triangles of `D_w` containing `s`
are `τ₁ = {q₁, q₂, q₃}` and `τ₂ = {q₁, q₃, q₄}`, those of `D'_w` containing `s'` are
`τ₁' = {q₁, q₂, q₄}` and `τ₂' = {q₂, q₃, q₄}`, and the other triangles agree. -/
private structure FlipData (G : PlabicData H b) (D D' : Finset H → Finset (Sym2 H))
    (w : Finset H) (s s' : Sym2 H) (q₁ q₂ q₃ q₄ : H) (τ₁ τ₂ τ₁' τ₂' : Finset H) : Prop where
  isCrossing : G.IsCrossing w
  isWhiteDatum : G.IsWhiteDatum D
  isWhiteDatum' : G.IsWhiteDatum D'
  agree : ∀ x, G.IsCrossing x → x ≠ w → D' x = D x
  mem : s ∈ D w
  mem' : s' ∈ D' w
  mem_iff : ∀ e, e ∈ D' w ↔ e = s' ∨ (e ∈ D w ∧ e ≠ s)
  mem_iff' : ∀ e, e ∈ D w ↔ e = s ∨ (e ∈ D' w ∧ e ≠ s')
  mem₁ : q₁ ∈ w
  mem₂ : q₂ ∈ w
  mem₃ : q₃ ∈ w
  mem₄ : q₄ ∈ w
  ne₁₂ : q₁ ≠ q₂
  ne₁₃ : q₁ ≠ q₃
  ne₁₄ : q₁ ≠ q₄
  ne₂₃ : q₂ ≠ q₃
  ne₂₄ : q₂ ≠ q₄
  ne₃₄ : q₃ ≠ q₄
  eq_s : s = s(q₁, q₃)
  eq_s' : s' = s(q₂, q₄)
  eq₁ : τ₁ = {q₁, q₂, q₃}
  eq₂ : τ₂ = {q₁, q₃, q₄}
  eq₁' : τ₁' = {q₁, q₂, q₄}
  eq₂' : τ₂' = {q₂, q₃, q₄}
  tri₁ : G.IsCornerTriangle w (D w) τ₁
  tri₂ : G.IsCornerTriangle w (D w) τ₂
  tri₁' : G.IsCornerTriangle w (D' w) τ₁'
  tri₂' : G.IsCornerTriangle w (D' w) τ₂'
  eq_or : ∀ t, G.IsCornerTriangle w (D w) t → s ∈ t.sym2 → t = τ₁ ∨ t = τ₂
  eq_or' : ∀ t, G.IsCornerTriangle w (D' w) t → s' ∈ t.sym2 → t = τ₁' ∨ t = τ₂'
  other : ∀ t, G.IsCornerTriangle w (D' w) t → t ≠ τ₁' → t ≠ τ₂' → G.IsCornerTriangle w (D w) t
  other' : ∀ t, G.IsCornerTriangle w (D w) t → t ≠ τ₁ → t ≠ τ₂ → G.IsCornerTriangle w (D' w) t

variable {w : Finset H} {s s' : Sym2 H} {q₁ q₂ q₃ q₄ : H} {τ₁ τ₂ τ₁' τ₂' : Finset H}

/-- The flip read backwards: from `D'` to `D`, with the quadrilateral `(q₂, q₁, q₄, q₃)`. -/
private theorem FlipData.symm (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂') :
    FlipData G D' D w s' s q₂ q₁ q₄ q₃ τ₁' τ₂' τ₁ τ₂ where
  isCrossing := h.isCrossing
  isWhiteDatum := h.isWhiteDatum'
  isWhiteDatum' := h.isWhiteDatum
  agree x hx hxw := (h.agree x hx hxw).symm
  mem := h.mem'
  mem' := h.mem
  mem_iff := h.mem_iff'
  mem_iff' := h.mem_iff
  mem₁ := h.mem₂
  mem₂ := h.mem₁
  mem₃ := h.mem₄
  mem₄ := h.mem₃
  ne₁₂ := h.ne₁₂.symm
  ne₁₃ := h.ne₂₄
  ne₁₄ := h.ne₂₃
  ne₂₃ := h.ne₁₄
  ne₂₄ := h.ne₁₃
  ne₃₄ := h.ne₃₄.symm
  eq_s := h.eq_s'
  eq_s' := h.eq_s
  eq₁ := by rw [h.eq₁']; ext; simp only [mem_insert, mem_singleton]; tauto
  eq₂ := by rw [h.eq₂']; ext; simp only [mem_insert, mem_singleton]; tauto
  eq₁' := by rw [h.eq₁]; ext; simp only [mem_insert, mem_singleton]; tauto
  eq₂' := by rw [h.eq₂]; ext; simp only [mem_insert, mem_singleton]; tauto
  tri₁ := h.tri₁'
  tri₂ := h.tri₂'
  tri₁' := h.tri₁
  tri₂' := h.tri₂
  eq_or := h.eq_or'
  eq_or' := h.eq_or
  other := h.other'
  other' := h.other

/-- The flip with the quadrilateral read from `q₃`: `(q₃, q₄, q₁, q₂)`, exchanging `τ₁` with `τ₂`
and `τ₁'` with `τ₂'`. -/
private theorem FlipData.rotate (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂') :
    FlipData G D D' w s s' q₃ q₄ q₁ q₂ τ₂ τ₁ τ₂' τ₁' where
  isCrossing := h.isCrossing
  isWhiteDatum := h.isWhiteDatum
  isWhiteDatum' := h.isWhiteDatum'
  agree := h.agree
  mem := h.mem
  mem' := h.mem'
  mem_iff := h.mem_iff
  mem_iff' := h.mem_iff'
  mem₁ := h.mem₃
  mem₂ := h.mem₄
  mem₃ := h.mem₁
  mem₄ := h.mem₂
  ne₁₂ := h.ne₃₄
  ne₁₃ := h.ne₁₃.symm
  ne₁₄ := h.ne₂₃.symm
  ne₂₃ := h.ne₁₄.symm
  ne₂₄ := h.ne₂₄.symm
  ne₃₄ := h.ne₁₂
  eq_s := by rw [h.eq_s, Sym2.eq_swap]
  eq_s' := by rw [h.eq_s', Sym2.eq_swap]
  eq₁ := by rw [h.eq₂]; ext; simp only [mem_insert, mem_singleton]; tauto
  eq₂ := by rw [h.eq₁]; ext; simp only [mem_insert, mem_singleton]; tauto
  eq₁' := by rw [h.eq₂']; ext; simp only [mem_insert, mem_singleton]; tauto
  eq₂' := by rw [h.eq₁']; ext; simp only [mem_insert, mem_singleton]; tauto
  tri₁ := h.tri₂
  tri₂ := h.tri₁
  tri₁' := h.tri₂'
  tri₂' := h.tri₁'
  eq_or t ht hs := (h.eq_or t ht hs).symm
  eq_or' t ht hs := (h.eq_or' t ht hs).symm
  other t ht h₁ h₂ := h.other t ht h₂ h₁
  other' t ht h₁ h₂ := h.other' t ht h₂ h₁

/-- The diagonal `s` is not a segment of `D'_w`. -/
private theorem FlipData.notMem_cornerSegments
    (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂') : s ∉ G.cornerSegments w (D' w) := by
  rw [mem_cornerSegments]
  rintro (hs | ⟨x, hx, hxs⟩)
  · rcases (h.mem_iff s).1 hs with h1 | ⟨-, h2⟩
    · rw [h.eq_s, h.eq_s'] at h1
      rcases Sym2.eq_iff.1 h1 with ⟨h3, -⟩ | ⟨h3, -⟩
      exacts [h.ne₁₂ h3, h.ne₁₄ h3]
    · exact h2 rfl
  · exact cornerSide_notMem_of_isCornerTriangulation (h.isWhiteDatum w h.isCrossing) hx
      (hxs ▸ h.mem)

/-- `τ₁` is not a triangle of `D'_w`. -/
private theorem FlipData.not_isCornerTriangle₁
    (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂') :
    ¬G.IsCornerTriangle w (D' w) τ₁ := fun ht => h.notMem_cornerSegments (by
  rw [h.eq_s]
  exact ht.2.2 q₁ (by rw [h.eq₁]; simp) q₃ (by rw [h.eq₁]; simp) h.ne₁₃)

/-- `τ₂` is not a triangle of `D'_w`. -/
private theorem FlipData.not_isCornerTriangle₂
    (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂') :
    ¬G.IsCornerTriangle w (D' w) τ₂ := fun ht => h.notMem_cornerSegments (by
  rw [h.eq_s]
  exact ht.2.2 q₁ (by rw [h.eq₂]; simp) q₃ (by rw [h.eq₂]; simp) h.ne₁₃)

/-- A crossing containing one of the darts `q_k` is `w`. -/
private theorem FlipData.eq_of_mem (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂')
    {x : Finset H} (hx : G.IsCrossing x) {q : H} (hq : q ∈ w) (hqx : q ∈ x) : x = w :=
  (hx.eq_vertexOf hqx).trans (h.isCrossing.eq_vertexOf hq).symm

/-- The pair `(e, τ)` of a symbol `y^±_{e,τ}` of `X°(G, D')`, sent to the pair of the corresponding
symbol of `X°(G, D)`: `y^±_{s',τ₁'} ↦ y^±_{s,τ₁}`, `y^±_{s',τ₂'} ↦ y^±_{s,τ₂}`, and
`y^±_{e,τ'} ↦ y^±_{e,τ}` for the other sides `e` of `τ' ∈ {τ₁', τ₂'}`, with `τ ∈ {τ₁, τ₂}` the
triangle containing `e`; every other pair is fixed. -/
private def flipPair (s s' : Sym2 H) (τ₁ τ₂ τ₁' τ₂' : Finset H) (e : Sym2 H) (τ : Finset H) :
    Sym2 H × Finset H :=
  if τ = τ₁' then (if e = s' then (s, τ₁) else if e ∈ τ₁.sym2 then (e, τ₁) else (e, τ₂))
  else if τ = τ₂' then (if e = s' then (s, τ₂) else if e ∈ τ₁.sym2 then (e, τ₁) else (e, τ₂))
  else (e, τ)

/-- The values of `flipPair` at the six pairs of `τ₁'` and `τ₂'`. -/
private theorem FlipData.flipPair_values
    (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂') :
    flipPair s s' τ₁ τ₂ τ₁' τ₂' s(q₁, q₂) τ₁' = (s(q₁, q₂), τ₁) ∧
    flipPair s s' τ₁ τ₂ τ₁' τ₂' s(q₁, q₄) τ₁' = (s(q₁, q₄), τ₂) ∧
    flipPair s s' τ₁ τ₂ τ₁' τ₂' s(q₂, q₄) τ₁' = (s, τ₁) ∧
    flipPair s s' τ₁ τ₂ τ₁' τ₂' s(q₂, q₃) τ₂' = (s(q₂, q₃), τ₁) ∧
    flipPair s s' τ₁ τ₂ τ₁' τ₂' s(q₃, q₄) τ₂' = (s(q₃, q₄), τ₂) ∧
    flipPair s s' τ₁ τ₂ τ₁' τ₂' s(q₂, q₄) τ₂' = (s, τ₂) := by
  have n12 := h.ne₁₂
  have n13 := h.ne₁₃
  have n14 := h.ne₁₄
  have n23 := h.ne₂₃
  have n24 := h.ne₂₄
  have n34 := h.ne₃₄
  have h12' : τ₂' ≠ τ₁' := by
    rw [h.eq₁', h.eq₂']
    intro e
    have : q₃ ∈ ({q₁, q₂, q₄} : Finset H) := by rw [← e]; simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h' | h'
    exacts [n13 h'.symm, n23 h'.symm, n34 h']
  rw [h.eq_s']
  simp only [flipPair, if_neg h12', h.eq₁, mk_mem_sym2_iff, mem_insert,
    mem_singleton, Sym2.eq_iff]
  simp [n12, n13, n14, n23, n24, n34, n12.symm, n13.symm, n14.symm, n23.symm, n24.symm,
    n34.symm]

/-- **The pairs of a flip.** `flipPair` sends the pairs `(e, τ)` indexing the symbols `y^±` of
`X°(G, D')` to pairs indexing those of `X°(G, D)`, the reverse flip undoes it, and it changes `e`
only for `e = s'`. -/
private theorem FlipData.flipPair_spec (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂')
    {e : Sym2 H} {τ : Finset H} (he : G.IsDatumSegment D' e τ) :
    G.IsDatumSegment D (flipPair s s' τ₁ τ₂ τ₁' τ₂' e τ).1
        (flipPair s s' τ₁ τ₂ τ₁' τ₂' e τ).2 ∧
      flipPair s' s τ₁' τ₂' τ₁ τ₂ (flipPair s s' τ₁ τ₂ τ₁' τ₂' e τ).1
        (flipPair s s' τ₁ τ₂ τ₁' τ₂' e τ).2 = (e, τ) ∧
      (flipPair s s' τ₁ τ₂ τ₁' τ₂' e τ).1 = if e = s' then s else e := by
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := h.flipPair_values
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := h.symm.flipPair_values
  rw [@Sym2.eq_swap _ q₂ q₁] at u1
  rw [@Sym2.eq_swap _ q₄ q₃] at u5
  rw [← h.eq_s] at u3 u6
  have hD1 : ∀ e, e ∈ D' w → e ≠ s' → e ∈ D w := fun e he hne =>
    (((h.mem_iff e).1 he).resolve_left hne).1
  have hs1 : s ∈ τ₁.sym2 := by rw [h.eq_s, h.eq₁, mk_mem_sym2_iff]; simp
  have hs2 : s ∈ τ₂.sym2 := by rw [h.eq_s, h.eq₂, mk_mem_sym2_iff]; simp
  obtain ⟨x, hx, heD, htri, heτ⟩ := he
  by_cases hxw : x = w
  · subst hxw
    have hdiag : ¬e.IsDiag := ((h.isWhiteDatum' x hx).1 e heD).1
    by_cases h1 : τ = τ₁'
    · subst h1
      rcases eq_or_of_mem_sym2_three (h.eq₁' ▸ heτ) hdiag with rfl | rfl | rfl
      · have hne : s(q₁, q₂) ≠ s' := by
          rw [h.eq_s']; intro e
          rcases Sym2.eq_iff.1 e with ⟨h3, -⟩ | ⟨h3, -⟩
          exacts [h.ne₁₂ h3, h.ne₁₄ h3]
        rw [v1, if_neg hne]
        refine ⟨⟨x, hx, hD1 _ heD hne, h.tri₁, by rw [h.eq₁, mk_mem_sym2_iff]; simp⟩, ?_, rfl⟩
        dsimp only
        rw [u1]
      · have hne : s(q₁, q₄) ≠ s' := by
          rw [h.eq_s']; intro e
          rcases Sym2.eq_iff.1 e with ⟨h3, -⟩ | ⟨h3, -⟩
          exacts [h.ne₁₂ h3, h.ne₁₄ h3]
        rw [v2, if_neg hne]
        refine ⟨⟨x, hx, hD1 _ heD hne, h.tri₂, by rw [h.eq₂, mk_mem_sym2_iff]; simp⟩, ?_, rfl⟩
        dsimp only
        rw [u4]
      · rw [v3, ← h.eq_s', if_pos rfl]
        refine ⟨⟨x, hx, h.mem, h.tri₁, hs1⟩, ?_, rfl⟩
        dsimp only
        rw [u3]
    by_cases h2 : τ = τ₂'
    · subst h2
      rcases eq_or_of_mem_sym2_three (h.eq₂' ▸ heτ) hdiag with rfl | rfl | rfl
      · have hne : s(q₂, q₃) ≠ s' := by
          rw [h.eq_s']; intro e
          rcases Sym2.eq_iff.1 e with ⟨-, h3⟩ | ⟨h3, -⟩
          exacts [h.ne₃₄ h3, h.ne₂₄ h3]
        rw [v4, if_neg hne]
        refine ⟨⟨x, hx, hD1 _ heD hne, h.tri₁, by rw [h.eq₁, mk_mem_sym2_iff]; simp⟩, ?_, rfl⟩
        dsimp only
        rw [u2]
      · rw [v6, ← h.eq_s', if_pos rfl]
        refine ⟨⟨x, hx, h.mem, h.tri₂, hs2⟩, ?_, rfl⟩
        dsimp only
        rw [u6]
      · have hne : s(q₃, q₄) ≠ s' := by
          rw [h.eq_s']; intro e
          rcases Sym2.eq_iff.1 e with ⟨h3, -⟩ | ⟨h3, -⟩
          exacts [h.ne₂₃ h3.symm, h.ne₃₄ h3]
        rw [v5, if_neg hne]
        refine ⟨⟨x, hx, hD1 _ heD hne, h.tri₂, by rw [h.eq₂, mk_mem_sym2_iff]; simp⟩, ?_, rfl⟩
        dsimp only
        rw [u5]
    -- another triangle of `D'_w`
    have hτD := h.other τ htri h1 h2
    have hτ1 : τ ≠ τ₁ := fun e => h.not_isCornerTriangle₁ (e ▸ htri)
    have hτ2 : τ ≠ τ₂ := fun e => h.not_isCornerTriangle₂ (e ▸ htri)
    have hes' : e ≠ s' := by
      rintro rfl
      rcases h.eq_or' τ htri heτ with h' | h'
      exacts [h1 h', h2 h']
    simp only [flipPair, if_neg h1, if_neg h2, if_neg hτ1, if_neg hτ2, if_neg hes']
    exact ⟨⟨x, hx, hD1 e heD hes', hτD, heτ⟩, trivial, trivial⟩
  · -- a triangle at another crossing
    have hDx : D' x = D x := h.agree x hx hxw
    have hq : ∀ q ∈ w, q ∉ τ := fun q hq hqτ => hxw (h.eq_of_mem hx hq (htri.1 hqτ))
    have hn : ∀ t : Finset H, q₁ ∈ t → τ ≠ t := fun t ht e => hq q₁ h.mem₁ (e ▸ ht)
    have hn' : ∀ t : Finset H, q₂ ∈ t → τ ≠ t := fun t ht e => hq q₂ h.mem₂ (e ▸ ht)
    have h1 := hn τ₁' (by rw [h.eq₁']; simp)
    have h2 := hn' τ₂' (by rw [h.eq₂']; simp)
    have h3 := hn τ₁ (by rw [h.eq₁]; simp)
    have h4 := hn τ₂ (by rw [h.eq₂]; simp)
    have hes' : e ≠ s' := by
      rintro rfl
      have : q₂ ∈ τ := mem_sym2_iff.1 heτ q₂ (by rw [h.eq_s']; exact Sym2.mem_mk_left _ _)
      exact hq q₂ h.mem₂ this
    simp only [flipPair, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg hes']
    exact ⟨⟨x, hx, hDx ▸ heD, hDx ▸ htri, heτ⟩, trivial, trivial⟩

/-- The symbols of `X°(G, D')` sent to those of `X°(G, D)` by a flip: `flipPair` on the symbols
`y^±`, the identity on the others. -/
private def flipSym (s s' : Sym2 H) (τ₁ τ₂ τ₁' τ₂' : Finset H) :
    StrandSymbol H b → StrandSymbol H b
  | yPlus e τ => yPlus (flipPair s s' τ₁ τ₂ τ₁' τ₂' e τ).1 (flipPair s s' τ₁ τ₂ τ₁' τ₂' e τ).2
  | yMinus e τ => yMinus (flipPair s s' τ₁ τ₂ τ₁' τ₂' e τ).1 (flipPair s s' τ₁ τ₂ τ₁' τ₂' e τ).2
  | xPlus d => xPlus d
  | xMinus t => xMinus t
  | bd r => bd r
  | bd' r => bd' r

private theorem FlipData.isStrandSymbol_flipSym
    (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂') {a : StrandSymbol H b}
    (ha : G.IsStrandSymbol D' a) :
    G.IsStrandSymbol D (flipSym s s' τ₁ τ₂ τ₁' τ₂' a) ∧
      flipSym s' s τ₁' τ₂' τ₁ τ₂ (flipSym s s' τ₁ τ₂ τ₁' τ₂' a) = a := by
  cases a with
  | xPlus d => exact ⟨ha, rfl⟩
  | xMinus t => exact ⟨ha, rfl⟩
  | yPlus e τ =>
    obtain ⟨h1, h2, -⟩ := h.flipPair_spec ha
    exact ⟨h1, by simp only [flipSym, h2]⟩
  | yMinus e τ =>
    obtain ⟨h1, h2, -⟩ := h.flipPair_spec ha
    exact ⟨h1, by simp only [flipSym, h2]⟩
  | bd r => exact ⟨trivial, rfl⟩
  | bd' r => exact ⟨trivial, rfl⟩

/-- The bijection of darts of a flip, `X°(G, D') → X°(G, D)`. -/
private def FlipData.strandEquiv (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂') :
    G.StrandDart D' ≃ G.StrandDart D where
  toFun a := ⟨flipSym s s' τ₁ τ₂ τ₁' τ₂' a.1, (h.isStrandSymbol_flipSym a.2).1⟩
  invFun a := ⟨flipSym s' s τ₁' τ₂' τ₁ τ₂ a.1, (h.symm.isStrandSymbol_flipSym a.2).1⟩
  left_inv a := Subtype.ext (h.isStrandSymbol_flipSym a.2).2
  right_inv a := Subtype.ext (h.symm.isStrandSymbol_flipSym a.2).2

omit [Fintype H] in
private theorem flipSym_endSymbol (r : Fin (2 * b)) :
    flipSym s s' τ₁ τ₂ τ₁' τ₂' (G.endSymbol r) = G.endSymbol r := by
  unfold endSymbol
  split_ifs <;> rfl

omit [Fintype H] in
/-- `flipSym` fixes the pair symbols of a triangle other than `τ₁'` and `τ₂'`. -/
private theorem flipSym_pair_of_ne {τ : Finset H} (h1 : τ ≠ τ₁') (h2 : τ ≠ τ₂') (p : H) :
    flipSym (b := b) s s' τ₁ τ₂ τ₁' τ₂' (G.pairOut τ p) = G.pairOut τ p ∧
      flipSym (b := b) s s' τ₁ τ₂ τ₁' τ₂' (G.pairIn τ p) = G.pairIn τ p := by
  unfold pairOut pairIn
  split_ifs <;> simp [flipSym, flipPair, h1, h2]

omit [Fintype H] in
/-- `flipSym` on the pair symbols at `p` of a triangle `τ'`, when `p` has the same clockwise
successor `q` in `τ'` and in `τ`. -/
private theorem flipSym_pair_of_eq {τ' τ : Finset H} {p q : H} (h' : G.cornerNext τ' p = q)
    (hτ : G.cornerNext τ p = q) (hF : flipPair s s' τ₁ τ₂ τ₁' τ₂' s(p, q) τ' = (s(p, q), τ)) :
    flipSym (b := b) s s' τ₁ τ₂ τ₁' τ₂' (G.pairOut τ' p) = G.pairOut τ p ∧
      flipSym (b := b) s s' τ₁ τ₂ τ₁' τ₂' (G.pairIn τ' p) = G.pairIn τ p := by
  unfold pairOut pairIn
  rw [h', hτ]
  split_ifs <;> simp [flipSym, hF]

omit [Fintype H] in
/-- `flipSym` on the pair symbols of a diagonal. -/
private theorem flipSym_pair_of_diag {τ' τ : Finset H} {p q p₀ q₀ : H}
    (h' : G.cornerNext τ' p = q) (hτ : G.cornerNext τ p₀ = q₀) (hq : q ≠ G.rot.symm p)
    (hq₀ : q₀ ≠ G.rot.symm p₀)
    (hF : flipPair s s' τ₁ τ₂ τ₁' τ₂' s(p, q) τ' = (s(p₀, q₀), τ)) :
    flipSym (b := b) s s' τ₁ τ₂ τ₁' τ₂' (G.pairOut τ' p) = G.pairOut τ p₀ ∧
      flipSym (b := b) s s' τ₁ τ₂ τ₁' τ₂' (G.pairIn τ' p) = G.pairIn τ p₀ := by
  unfold pairOut pairIn
  rw [h', hτ, if_neg hq, if_neg hq, if_neg hq₀, if_neg hq₀]
  simp [flipSym, hF]

/-- A triangle of `D'` other than `τ₁'` and `τ₂'` is a triangle of `D` other than `τ₁` and
`τ₂`. -/
private theorem FlipData.isDatumTriangle_of_ne
    (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂') {τ : Finset H}
    (hτ : G.IsDatumTriangle D' τ) (h1 : τ ≠ τ₁') (h2 : τ ≠ τ₂') :
    G.IsDatumTriangle D τ ∧ τ ≠ τ₁ ∧ τ ≠ τ₂ := by
  obtain ⟨x, hx, ht⟩ := hτ
  by_cases hxw : x = w
  · subst hxw
    exact ⟨⟨x, hx, h.other τ ht h1 h2⟩, fun e => h.not_isCornerTriangle₁ (e ▸ ht),
      fun e => h.not_isCornerTriangle₂ (e ▸ ht)⟩
  · have hq : q₁ ∉ τ := fun hq => hxw (h.eq_of_mem hx h.mem₁ (ht.1 hq))
    refine ⟨⟨x, hx, h.agree x hx hxw ▸ ht⟩, ?_, ?_⟩ <;> rintro rfl
    · exact hq (by rw [h.eq₁]; simp)
    · exact hq (by rw [h.eq₂]; simp)

end Flip

/-! ### The digon of a diagonal -/

private theorem vertexOf_strandDiagram_of_pairOut (hG : G.IsPlabicGraph) {D}
    (hD : G.IsWhiteDatum D) {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H} (hp : p ∈ τ)
    {z : G.StrandDart D} (hz : z.1 = G.pairOut τ p) :
    (G.strandDiagram hG hD).vertexOf z = G.strandTriplePoint D τ := by
  have : z = ⟨G.pairOut τ p, isStrandSymbol_pairOut hD hτ hp⟩ := Subtype.ext hz
  rw [this, strandDiagram_vertexOf_pairOut hG hD hτ hp]

private theorem vertexOf_strandDiagram_of_pairIn (hG : G.IsPlabicGraph) {D}
    (hD : G.IsWhiteDatum D) {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H} (hp : p ∈ τ)
    {z : G.StrandDart D} (hz : z.1 = G.pairIn τ p) :
    (G.strandDiagram hG hD).vertexOf z = G.strandTriplePoint D τ := by
  have : z = (G.strandDiagram hG hD).rot ⟨G.pairOut τ p, isStrandSymbol_pairOut hD hτ hp⟩ := by
    rw [strandDiagram_rot_pairOut hG hD hτ hp]
    exact Subtype.ext hz
  rw [this, (G.strandDiagram hG hD).vertexOf_rot, strandDiagram_vertexOf_pairOut hG hD hτ hp]

/-- **The digon of a diagonal.** For `s ∈ D_w` and the two triangles `τ₁ ≠ τ₂` of `D_w`
containing `s`, the darts `y⁻_{s,τ₁}` and `y⁻_{s,τ₂}` form a digon of `X°(G, D)`: the face
permutation exchanges them, and they lie at the distinct triple points of `τ₁` and `τ₂`. -/
theorem isDigon_strandDiagram_yMinus (hG : G.IsPlabicGraph) {D : Finset H → Finset (Sym2 H)}
    (hD : G.IsWhiteDatum D) {w : Finset H} (hw : G.IsCrossing w) {s : Sym2 H} (hs : s ∈ D w)
    {τ₁ τ₂ : Finset H} (h₁ : G.IsCornerTriangle w (D w) τ₁) (h₂ : G.IsCornerTriangle w (D w) τ₂)
    (hs₁ : s ∈ τ₁.sym2) (hs₂ : s ∈ τ₂.sym2) (hne : τ₁ ≠ τ₂) {d₁ d₂ : G.StrandDart D}
    (hd₁ : d₁.1 = yMinus s τ₁) (hd₂ : d₂.1 = yMinus s τ₂) :
    (G.strandDiagram hG hD).facePerm d₁ = d₂ ∧ (G.strandDiagram hG hD).facePerm d₂ = d₁ ∧
      (G.strandDiagram hG hD).faceOf d₁ = {d₁, d₂} ∧
      (G.strandDiagram hG hD).IsDigon {d₁, d₂} := by
  set X := G.strandDiagram hG hD
  have g₁ : G.IsDatumSegment D s τ₁ := ⟨w, hw, hs, h₁, hs₁⟩
  have g₂ : G.IsDatumSegment D s τ₂ := ⟨w, hw, hs, h₂, hs₂⟩
  have o₁ : G.otherTriangle D s τ₁ = τ₂ :=
    (hD.eq_otherTriangle g₁ (.of_isDatumSegment g₂) hs₂ hne.symm).symm
  have o₂ : G.otherTriangle D s τ₂ = τ₁ :=
    (hD.eq_otherTriangle g₂ (.of_isDatumSegment g₁) hs₁ hne).symm
  have f₁ : X.facePerm d₁ = d₂ := by
    apply Subtype.ext
    rw [RotationSystem.facePerm_apply, strandDiagram_rot_apply, strandDiagram_inv_apply, hd₁,
      hd₂]
    change yMinus s (G.otherTriangle D s τ₁) = _
    rw [o₁]
  have f₂ : X.facePerm d₂ = d₁ := by
    apply Subtype.ext
    rw [RotationSystem.facePerm_apply, strandDiagram_rot_apply, strandDiagram_inv_apply, hd₁,
      hd₂]
    change yMinus s (G.otherTriangle D s τ₂) = _
    rw [o₂]
  have hface : X.faceOf d₁ = {d₁, d₂} := by
    refine filter_sameCycle_eq (by simp) ?_ ?_
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy ⊢
      rcases hy with rfl | rfl
      · exact Or.inr f₁
      · exact Or.inl f₂
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Equiv.Perm.SameCycle.refl _ _
      · exact sameCycle_of_apply_eq f₁
  have vt : ∀ (τ : Finset H) (hτ : G.IsDatumSegment D s τ) (z : G.StrandDart D),
      z.1 = yMinus s τ → X.vertexOf z = G.strandTriplePoint D τ := by
    intro τ hτ z hz
    obtain ⟨p, hp, hsp, hn⟩ := hD.exists_eq_mk_cornerNext hτ
    refine vertexOf_strandDiagram_of_pairIn hG hD (.of_isDatumSegment hτ) hp ?_
    rw [hz, pairIn, if_neg hn, ← hsp]
  have hnB : ∀ z : G.StrandDart D, z = d₁ ∨ z = d₂ → z ∉ X.bdry := by
    rintro z (rfl | rfl) <;> rw [mem_strandDiagram_bdry]
    · rw [hd₁]; exact id
    · rw [hd₂]; exact id
  refine ⟨f₁, f₂, hface, ?_, d₁, by rw [f₁], ?_⟩
  · rw [DiskMap.mem_internalFaces, DiskMap.mem_faces]
    refine ⟨⟨fun he => ?_, hface ▸ X.faceOf_mem_faceOrbits d₁⟩, ?_⟩
    · have : d₁ ∈ X.exterior := he ▸ (by simp)
      exact hnB d₁ (Or.inl rfl) (X.exterior_subset_bdry this)
    · rw [disjoint_left]
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      exact hnB z hz
  · rw [f₁, vt τ₁ g₁ d₁ hd₁, vt τ₂ g₂ d₂ hd₂]
    intro e
    exact hne ((bijOn_strandTriplePoint hG hD).injOn (.of_isDatumSegment g₁)
      (.of_isDatumSegment g₂) e)

/-! ### A flip is a swivel move -/

section FlipIso

variable {D D' : Finset H → Finset (Sym2 H)} {w : Finset H} {s s' : Sym2 H} {q₁ q₂ q₃ q₄ : H}
  {τ₁ τ₂ τ₁' τ₂' : Finset H}

/-- **The isomorphism of a flip.** Given the data of a flip together with the clockwise successors
in the four triangles `τ₁, τ₂, τ₁', τ₂'`, the strand diagram `X°(G, D')` is isomorphic to the
swivel move of `X°(G, D)` at `y⁻_{s,τ₁}`. -/
private theorem FlipData.strandDiagram_isomorphic
    (h : FlipData G D D' w s s' q₁ q₂ q₃ q₄ τ₁ τ₂ τ₁' τ₂') (hG : G.IsPlabicGraph)
    (c₁ : G.cornerNext τ₁ q₁ = q₂) (c₂ : G.cornerNext τ₁ q₂ = q₃) (c₃ : G.cornerNext τ₁ q₃ = q₁)
    (c₄ : G.cornerNext τ₂ q₁ = q₃) (c₅ : G.cornerNext τ₂ q₃ = q₄) (c₆ : G.cornerNext τ₂ q₄ = q₁)
    (c₇ : G.cornerNext τ₁' q₁ = q₂) (c₈ : G.cornerNext τ₁' q₂ = q₄)
    (c₉ : G.cornerNext τ₁' q₄ = q₁) (c₁₀ : G.cornerNext τ₂' q₂ = q₃)
    (c₁₁ : G.cornerNext τ₂' q₃ = q₄) (c₁₂ : G.cornerNext τ₂' q₄ = q₂) {d₁ : G.StrandDart D}
    (hd₁ : d₁.1 = yMinus s τ₁) :
    (G.strandDiagram hG h.isWhiteDatum').Isomorphic
      ((G.strandDiagram hG h.isWhiteDatum).swivelMove d₁) := by
  have hD := h.isWhiteDatum
  have hD' := h.isWhiteDatum'
  have hw := h.isCrossing
  set X := G.strandDiagram hG hD
  set X' := G.strandDiagram hG hD'
  set θ := h.strandEquiv
  have θval : ∀ a, (θ a).1 = flipSym s s' τ₁ τ₂ τ₁' τ₂' a.1 := fun _ => rfl
  have T₁ : G.IsDatumTriangle D τ₁ := ⟨w, hw, h.tri₁⟩
  have T₂ : G.IsDatumTriangle D τ₂ := ⟨w, hw, h.tri₂⟩
  have T₁' : G.IsDatumTriangle D' τ₁' := ⟨w, hw, h.tri₁'⟩
  have T₂' : G.IsDatumTriangle D' τ₂' := ⟨w, hw, h.tri₂'⟩
  have m₁₁ : q₁ ∈ τ₁ := by simp [h.eq₁]
  have m₁₂ : q₂ ∈ τ₁ := by simp [h.eq₁]
  have m₁₃ : q₃ ∈ τ₁ := by simp [h.eq₁]
  have m₂₁ : q₁ ∈ τ₂ := by simp [h.eq₂]
  have m₂₃ : q₃ ∈ τ₂ := by simp [h.eq₂]
  have m₂₄ : q₄ ∈ τ₂ := by simp [h.eq₂]
  have n₁₁ : q₁ ∈ τ₁' := by simp [h.eq₁']
  have n₁₂ : q₂ ∈ τ₁' := by simp [h.eq₁']
  have n₁₄ : q₄ ∈ τ₁' := by simp [h.eq₁']
  have n₂₂ : q₂ ∈ τ₂' := by simp [h.eq₂']
  have n₂₃ : q₃ ∈ τ₂' := by simp [h.eq₂']
  have n₂₄ : q₄ ∈ τ₂' := by simp [h.eq₂']
  have hs1 : s ∈ τ₁.sym2 := by rw [h.eq_s, h.eq₁, mk_mem_sym2_iff]; simp
  have hs2 : s ∈ τ₂.sym2 := by rw [h.eq_s, h.eq₂, mk_mem_sym2_iff]; simp
  have hne12 : τ₁ ≠ τ₂ := by
    rw [h.eq₁, h.eq₂]
    intro e
    have : q₂ ∈ ({q₁, q₃, q₄} : Finset H) := by rw [← e]; simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h' | h'
    exacts [h.ne₁₂ h'.symm, h.ne₂₃ h', h.ne₂₄ h']
  -- the diagonals `s` and `s'` are not sides
  have nside : ∀ {E : Finset (Sym2 H)}, G.IsCornerTriangulation w E → ∀ {p q : H}, p ∈ w →
      s(p, q) ∈ E → q ≠ G.rot.symm p := by
    intro E hE p q hp he hq
    subst hq
    exact cornerSide_notMem_of_isCornerTriangulation hE hp he
  have ns₃ : q₁ ≠ G.rot.symm q₃ :=
    nside (hD w hw) h.mem₃ (by rw [Sym2.eq_swap, ← h.eq_s]; exact h.mem)
  have ns₁ : q₃ ≠ G.rot.symm q₁ := nside (hD w hw) h.mem₁ (by rw [← h.eq_s]; exact h.mem)
  have ns'₂ : q₄ ≠ G.rot.symm q₂ := nside (hD' w hw) h.mem₂ (by rw [← h.eq_s']; exact h.mem')
  have ns'₄ : q₂ ≠ G.rot.symm q₄ :=
    nside (hD' w hw) h.mem₄ (by rw [Sym2.eq_swap, ← h.eq_s']; exact h.mem')
  -- the twelve pair symbols of `τ₁'` and `τ₂'`
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := h.flipPair_values
  obtain ⟨P1, Q1⟩ := flipSym_pair_of_eq (b := b) c₇ c₁ v1
  obtain ⟨P2, Q2⟩ := flipSym_pair_of_diag (b := b) c₈ c₃ ns'₂ ns₃
    (by rw [v3, h.eq_s, @Sym2.eq_swap _ q₁ q₃])
  obtain ⟨P3, Q3⟩ := flipSym_pair_of_eq (b := b) c₉ c₆
    (by rw [@Sym2.eq_swap _ q₄ q₁, v2])
  obtain ⟨P4, Q4⟩ := flipSym_pair_of_eq (b := b) c₁₀ c₂ v4
  obtain ⟨P5, Q5⟩ := flipSym_pair_of_eq (b := b) c₁₁ c₅ v5
  obtain ⟨P6, Q6⟩ := flipSym_pair_of_diag (b := b) c₁₂ c₄ ns'₄ ns₁
    (by rw [@Sym2.eq_swap _ q₄ q₂, v6, h.eq_s])
  -- the digon and the swivel move
  set d₂ : G.StrandDart D := ⟨yMinus s τ₂, ⟨w, hw, h.mem, h.tri₂, hs2⟩⟩
  obtain ⟨f₁, f₂, hface, hdig⟩ := isDigon_strandDiagram_yMinus hG hD hw h.mem h.tri₁ h.tri₂
    hs1 hs2 hne12 hd₁ (rfl : d₂.1 = yMinus s τ₂)
  have hd : X.IsDigon (X.faceOf d₁) := hface ▸ hdig
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, -, g1, g2, g3, g4, -, -, -, -, hi₁,
    hi₂, s1, t3, s4, tb1, s6, td2, hφ, s5, tb3, s3, ta1, s2, -, -⟩ :=
    hd.exists_swivel (isPreTripleDiagram_strandDiagram hG hD)
  rw [f₁] at g1 hi₂ s6 td2 hφ s5
  -- the symbols of the darts at the digon
  have e_d₁ : d₁.1 = G.pairIn τ₁ q₃ := by
    rw [hd₁, pairIn, c₃, if_neg ns₃, Sym2.eq_swap, ← h.eq_s]
  have e_d₂ : d₂.1 = G.pairIn τ₂ q₁ := by
    rw [pairIn, c₄, if_neg ns₁, ← h.eq_s]
  have o₁ : G.otherTriangle D s τ₁ = τ₂ :=
    (hD.eq_otherTriangle ⟨w, hw, h.mem, h.tri₁, hs1⟩ T₂ hs2 hne12.symm).symm
  have o₂ : G.otherTriangle D s τ₂ = τ₁ :=
    (hD.eq_otherTriangle ⟨w, hw, h.mem, h.tri₂, hs2⟩ T₁ hs1 hne12).symm
  have e_id₁ : (X.inv d₁).1 = G.pairOut τ₂ q₁ := by
    rw [strandDiagram_inv_apply, hd₁, pairOut, c₄, if_neg ns₁, ← h.eq_s]
    change yPlus s (G.otherTriangle D s τ₁) = _
    rw [o₁]
  have e_id₂ : (X.inv d₂).1 = G.pairOut τ₁ q₃ := by
    rw [strandDiagram_inv_apply, pairOut, c₃, if_neg ns₃, Sym2.eq_swap, ← h.eq_s]
    change yPlus s (G.otherTriangle D s τ₂) = _
    rw [o₂]
  have e_a₁ : a₁.1 = G.pairOut τ₁ q₂ := by
    rw [← h1, strandDiagram_rot_apply, e_d₁, strandRotSym_pairIn hG hD T₁ m₁₃, c₃, c₁]
  have e_a₂ : a₂.1 = G.pairIn τ₁ q₂ := by
    rw [← h2, strandDiagram_rot_apply, e_a₁, strandRotSym_pairOut hG T₁ m₁₂]
  have e_a₃ : a₃.1 = G.pairOut τ₁ q₁ := by
    rw [← h3, strandDiagram_rot_apply, e_a₂, strandRotSym_pairIn hG hD T₁ m₁₂, c₂, c₃]
  have e_a₄ : a₄.1 = G.pairIn τ₁ q₁ := by
    rw [← h4, strandDiagram_rot_apply, e_a₃, strandRotSym_pairOut hG T₁ m₁₁]
  have e_b₁ : b₁.1 = G.pairOut τ₂ q₄ := by
    rw [← g1, strandDiagram_rot_apply, e_d₂, strandRotSym_pairIn hG hD T₂ m₂₁, c₄, c₅]
  have e_b₂ : b₂.1 = G.pairIn τ₂ q₄ := by
    rw [← g2, strandDiagram_rot_apply, e_b₁, strandRotSym_pairOut hG T₂ m₂₄]
  have e_b₃ : b₃.1 = G.pairOut τ₂ q₃ := by
    rw [← g3, strandDiagram_rot_apply, e_b₂, strandRotSym_pairIn hG hD T₂ m₂₄, c₆, c₄]
  have e_b₄ : b₄.1 = G.pairIn τ₂ q₃ := by
    rw [← g4, strandDiagram_rot_apply, e_b₃, strandRotSym_pairOut hG T₂ m₂₃]
  -- darts at the two triple points of the digon are not at boundary vertices
  have hnot : ∀ z : G.StrandDart D, z ∈ X.vertexOf d₁ ∪ X.vertexOf d₂ →
      ¬X.IsBoundaryVertex (X.vertexOf z) := by
    intro z hz
    rcases mem_union.1 hz with hz | hz
    · rw [X.vertexOf_eq_of_mem hz]; exact hi₁
    · rw [X.vertexOf_eq_of_mem hz]; exact hi₂
  have vd₁ : X.vertexOf d₁ = G.strandTriplePoint D τ₁ :=
    vertexOf_strandDiagram_of_pairIn hG hD T₁ m₁₃ e_d₁
  have vd₂ : X.vertexOf d₂ = G.strandTriplePoint D τ₂ :=
    vertexOf_strandDiagram_of_pairIn hG hD T₂ m₂₁ e_d₂
  have hnotT : ∀ (τ : Finset H), G.IsDatumTriangle D τ → τ ≠ τ₁ → τ ≠ τ₂ →
      ∀ z : G.StrandDart D, X.vertexOf z = G.strandTriplePoint D τ →
        z ∉ X.vertexOf d₁ ∪ X.vertexOf d₂ := by
    intro τ hτ hτ1 hτ2 z hz hmem
    have inj := (bijOn_strandTriplePoint hG hD).injOn
    rcases mem_union.1 hmem with hm | hm
    · rw [X.vertexOf_eq_of_mem hm, vd₁] at hz
      exact hτ1 (inj hτ T₁ hz.symm)
    · rw [X.vertexOf_eq_of_mem hm, vd₂] at hz
      exact hτ2 (inj hτ T₂ hz.symm)
  have fixed : ∀ a : G.StrandDart D',
      flipSym s s' τ₁ τ₂ τ₁' τ₂' (G.strandRotSym D' a.1) =
        G.strandRotSym D (flipSym s s' τ₁ τ₂ τ₁' τ₂' a.1) →
      θ a ∉ X.vertexOf d₁ ∪ X.vertexOf d₂ → θ (X'.rot a) = X.swivelRot d₁ (θ a) := by
    intro a e1 e2
    rw [← f₁] at e2
    rw [TripleData.swivelRot_apply_of_notMem e2]
    exact Subtype.ext e1
  refine strandDiagram_isomorphic_of hG hD' _ θ ?_ ?_ ?_ ?_ ?_
  · -- the involutions
    refine strandDiagram_map_inv_of hG hD'
      (isPreTripleDiagram_strandDiagram hG hD).inv_involutive _ ?_
    rintro ⟨a, ha⟩ (⟨d, rfl⟩ | ⟨e, τ, rfl⟩ | ⟨r, rfl⟩)
    · rfl
    · apply Subtype.ext
      obtain ⟨o1, o2, -⟩ := hD'.otherTriangle_spec (ha : G.IsDatumSegment D' e τ)
      obtain ⟨S1, S2, S3⟩ := h.flipPair_spec (ha : G.IsDatumSegment D' e τ)
      obtain ⟨S1', S2', S3'⟩ := h.flipPair_spec o1
      set F := flipPair s s' τ₁ τ₂ τ₁' τ₂' e τ
      set F' := flipPair s s' τ₁ τ₂ τ₁' τ₂' e (G.otherTriangle D' e τ)
      have e1 : F'.1 = F.1 := S3'.trans S3.symm
      have e2 : F'.2 = G.otherTriangle D F.1 F.2 := by
        refine hD.eq_otherTriangle S1 (.of_isDatumSegment S1') (e1 ▸ ?_) ?_
        · obtain ⟨_, _, _, _, hm⟩ := S1'
          exact hm
        · intro he
          have : F' = F := Prod.ext e1 he
          rw [this, S2] at S2'
          exact o2 (congrArg Prod.snd S2').symm
      change yMinus F'.1 F'.2 = G.strandInvSym D (yPlus F.1 F.2)
      rw [e1, e2]
      rfl
    · rfl
  · -- the rotations
    intro a
    change θ (X'.rot a) = X.swivelRot d₁ (θ a)
    rcases strandDart_cases hG hD' a with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ |
      ⟨τ, p, hτ, hp, rfl⟩ | ⟨τ, p, hτ, hp, rfl⟩
    · refine fixed _ (by simp only [strandRotSym_bd]; exact flipSym_endSymbol r) ?_
      intro hm
      exact hnot _ hm ⟨_, X.self_mem_vertexOf _, (mem_strandDiagram_bdry hG hD).2 trivial⟩
    · refine fixed _ rfl ?_
      intro hm
      exact hnot _ hm ⟨_, X.self_mem_vertexOf _, (mem_strandDiagram_bdry hG hD).2 trivial⟩
    · refine fixed _ ?_ ?_
      · rw [strandRotSym_endSymbol hG, flipSym_endSymbol, strandRotSym_endSymbol hG]
        rfl
      · intro hm
        refine hnot _ hm ⟨X.rot (θ _), X.rot_mem_vertexOf _, ?_⟩
        rw [mem_strandDiagram_bdry, strandDiagram_rot_apply, θval, flipSym_endSymbol,
          strandRotSym_endSymbol hG]
        trivial
    · by_cases ht1 : τ = τ₁'
      · subst ht1
        have hp' : p = q₁ ∨ p = q₂ ∨ p = q₄ := by
          rw [h.eq₁'] at hp; simpa using hp
        rcases hp' with rfl | rfl | rfl
        · have eθ : θ ⟨G.pairOut τ p, isStrandSymbol_pairOut hD' hτ hp⟩ = a₃ :=
            Subtype.ext (by rw [θval, P1, e_a₃])
          rw [eθ, t3]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairOut hG T₁' n₁₁, Q1, e_a₄]
        · have eθ : θ ⟨G.pairOut τ p, isStrandSymbol_pairOut hD' hτ hp⟩ = X.inv d₂ :=
            Subtype.ext (by rw [θval, P2, e_id₂])
          rw [eθ, td2]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairOut hG T₁' n₁₂, Q2, e_d₁]
        · have eθ : θ ⟨G.pairOut τ p, isStrandSymbol_pairOut hD' hτ hp⟩ = b₁ :=
            Subtype.ext (by rw [θval, P3, e_b₁])
          rw [eθ, tb1]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairOut hG T₁' n₁₄, Q3, e_b₂]
      by_cases ht2 : τ = τ₂'
      · subst ht2
        have hp' : p = q₂ ∨ p = q₃ ∨ p = q₄ := by
          rw [h.eq₂'] at hp; simpa using hp
        rcases hp' with rfl | rfl | rfl
        · have eθ : θ ⟨G.pairOut τ p, isStrandSymbol_pairOut hD' hτ hp⟩ = a₁ :=
            Subtype.ext (by rw [θval, P4, e_a₁])
          rw [eθ, ta1]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairOut hG T₂' n₂₂, Q4, e_a₂]
        · have eθ : θ ⟨G.pairOut τ p, isStrandSymbol_pairOut hD' hτ hp⟩ = b₃ :=
            Subtype.ext (by rw [θval, P5, e_b₃])
          rw [eθ, tb3]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairOut hG T₂' n₂₃, Q5, e_b₄]
        · have eθ : θ ⟨G.pairOut τ p, isStrandSymbol_pairOut hD' hτ hp⟩ = X.inv d₁ :=
            Subtype.ext (by rw [θval, P6, e_id₁])
          rw [eθ, hφ]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairOut hG T₂' n₂₄, Q6, e_d₂]
      obtain ⟨hτD, hτ1, hτ2⟩ := h.isDatumTriangle_of_ne hτ ht1 ht2
      obtain ⟨F1, F2⟩ := flipSym_pair_of_ne (b := b) (s := s) (s' := s') (τ₁ := τ₁) (τ₂ := τ₂)
        (G := G) ht1 ht2 p
      refine fixed _ ?_ ?_
      · rw [strandRotSym_pairOut hG hτ hp, F2, F1, strandRotSym_pairOut hG hτD hp]
      · refine hnotT τ hτD hτ1 hτ2 _ ?_
        exact vertexOf_strandDiagram_of_pairOut hG hD hτD hp (by rw [θval, F1])
    · by_cases ht1 : τ = τ₁'
      · subst ht1
        have hp' : p = q₁ ∨ p = q₂ ∨ p = q₄ := by
          rw [h.eq₁'] at hp; simpa using hp
        rcases hp' with rfl | rfl | rfl
        · have eθ : θ ⟨G.pairIn τ p, isStrandSymbol_pairIn hG hD' hτ hp⟩ = a₄ :=
            Subtype.ext (by rw [θval, Q1, e_a₄])
          rw [eθ, s4]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairIn hG hD' T₁' n₁₁, c₇, c₈, P3,
            e_b₁]
        · have eθ : θ ⟨G.pairIn τ p, isStrandSymbol_pairIn hG hD' hτ hp⟩ = d₁ :=
            Subtype.ext (by rw [θval, Q2, e_d₁])
          rw [eθ, s1]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairIn hG hD' T₁' n₁₂, c₈, c₉, P1,
            e_a₃]
        · have eθ : θ ⟨G.pairIn τ p, isStrandSymbol_pairIn hG hD' hτ hp⟩ = b₂ :=
            Subtype.ext (by rw [θval, Q3, e_b₂])
          rw [eθ, s6]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairIn hG hD' T₁' n₁₄, c₉, c₇, P2,
            e_id₂]
      by_cases ht2 : τ = τ₂'
      · subst ht2
        have hp' : p = q₂ ∨ p = q₃ ∨ p = q₄ := by
          rw [h.eq₂'] at hp; simpa using hp
        rcases hp' with rfl | rfl | rfl
        · have eθ : θ ⟨G.pairIn τ p, isStrandSymbol_pairIn hG hD' hτ hp⟩ = a₂ :=
            Subtype.ext (by rw [θval, Q4, e_a₂])
          rw [eθ, s2]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairIn hG hD' T₂' n₂₂, c₁₀, c₁₁, P6,
            e_id₁]
        · have eθ : θ ⟨G.pairIn τ p, isStrandSymbol_pairIn hG hD' hτ hp⟩ = b₄ :=
            Subtype.ext (by rw [θval, Q5, e_b₄])
          rw [eθ, s3]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairIn hG hD' T₂' n₂₃, c₁₁, c₁₂, P4,
            e_a₁]
        · have eθ : θ ⟨G.pairIn τ p, isStrandSymbol_pairIn hG hD' hτ hp⟩ = d₂ :=
            Subtype.ext (by rw [θval, Q6, e_d₂])
          rw [eθ, s5]
          apply Subtype.ext
          rw [θval, strandDiagram_rot_apply, strandRotSym_pairIn hG hD' T₂' n₂₄, c₁₂, c₁₀, P5,
            e_b₃]
      obtain ⟨hτD, hτ1, hτ2⟩ := h.isDatumTriangle_of_ne hτ ht1 ht2
      have hq := hD'.cornerNext_mem hτ (hD'.cornerNext_mem hτ hp)
      obtain ⟨F1, F2⟩ := flipSym_pair_of_ne (b := b) (s := s) (s' := s') (τ₁ := τ₁) (τ₂ := τ₂)
        (G := G) ht1 ht2 p
      obtain ⟨F3, -⟩ := flipSym_pair_of_ne (b := b) (s := s) (s' := s') (τ₁ := τ₁) (τ₂ := τ₂)
        (G := G) ht1 ht2 (G.cornerNext τ (G.cornerNext τ p))
      refine fixed _ ?_ ?_
      · rw [strandRotSym_pairIn hG hD' hτ hp, F3, F2, strandRotSym_pairIn hG hD hτD hp]
      · refine hnotT τ hτD hτ1 hτ2 _ ?_
        exact vertexOf_strandDiagram_of_pairIn hG hD hτD hp (by rw [θval, F2])
  · -- the boundaries
    rintro ⟨a, ha⟩
    rw [TripleData.swivelMove_bdry, mem_strandDiagram_bdry, θval]
    cases a <;> exact Iff.rfl
  · -- the orientations
    rintro ⟨a, ha⟩ -
    rw [TripleData.swivelMove_isOut, strandDiagram_isOut, θval]
    cases a <;> rfl
  · -- the endpoints
    intro r
    rw [TripleData.swivelMove_endDart]
    exact Subtype.ext (flipSym_endSymbol r)

omit [Fintype H] in
/-- The three elements of a three-element set `{x, y, z}` are pairwise distinct. -/
private theorem ne_of_card_eq_three {x y z : H} (h : ({x, y, z} : Finset H).card = 3) :
    x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> subst e
  · rw [insert_eq_of_mem (mem_insert_self _ _)] at h
    have := card_insert_le x ({z} : Finset H)
    rw [card_singleton] at this
    omega
  · rw [insert_eq_of_mem (mem_insert_of_mem (mem_singleton_self _))] at h
    have := card_insert_le y ({x} : Finset H)
    rw [card_singleton] at this
    omega
  · rw [show (insert y {y} : Finset H) = {y} from insert_eq_of_mem (mem_singleton_self y)] at h
    have := card_insert_le x ({y} : Finset H)
    rw [card_singleton] at this
    omega

/-- The clockwise successors in a triangle `{x, y, z}` of a white datum with `(x, y, z)`
clockwise. -/
private theorem IsWhiteDatum.cornerNext_eq_of_isCornerClockwise
    {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D) {τ : Finset H}
    (hτ : G.IsDatumTriangle D τ) {x y z : H} (he : τ = {x, y, z})
    (hc : G.IsCornerClockwise x y z) :
    G.cornerNext τ x = y ∧ G.cornerNext τ y = z ∧ G.cornerNext τ z = x := by
  have hx : x ∈ τ := by rw [he]; simp
  obtain ⟨q, r, hτ', hxq, hxr, hqr, h1, h2, h3, -, -, -, hcl⟩ := hD.cornerNext_spec hτ hx
  have hq : q ∈ ({x, y, z} : Finset H) := by rw [← he, hτ']; simp
  have hr : r ∈ ({x, y, z} : Finset H) := by rw [← he, hτ']; simp
  simp only [mem_insert, mem_singleton] at hq hr
  rcases hq with rfl | rfl | rfl
  · exact absurd rfl hxq
  · rcases hr with rfl | rfl | rfl
    · exact absurd rfl hxr
    · exact absurd rfl hqr
    · exact ⟨h1, h2, h3⟩
  · rcases hr with rfl | rfl | rfl
    · exact absurd rfl hxr
    · exact absurd hcl hc.not_swap
    · exact absurd rfl hqr

/-- **A flip of a corner triangulation is a swivel move**. Let `G` be a plabic graph and `D, D'`
white data of `G` that agree except at one crossing `w`, where `D'_w = (D_w \ {s}) ∪ {s'}` for some
`s ∈ D_w` and some `s' ∉ D_w`. Let `τ₁ ≠ τ₂` be the two triangles of `D_w` containing `s`, and
`d₁, d₂` the darts `y⁻_{s,τ₁}`, `y⁻_{s,τ₂}` of `X°(G, D)`. Then `{d₁, d₂}` is a digon of
`X°(G, D)` (the face of `d₁`), and `X°(G, D')` is isomorphic to the swivel move of `X°(G, D)` at
it. -/
@[cluster_algebras "lem_strand_diagram_flip"]
theorem isDigon_and_isomorphic_swivelMove_of_flip (hG : G.IsPlabicGraph)
    {D D' : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D) (hD' : G.IsWhiteDatum D')
    {w : Finset H} (hw : G.IsCrossing w) (hagree : ∀ x, G.IsCrossing x → x ≠ w → D' x = D x)
    {s s' : Sym2 H} (hs : s ∈ D w) (hs' : s' ∉ D w) (hD'w : D' w = insert s' ((D w).erase s))
    {τ₁ τ₂ : Finset H} (hτ₁ : G.IsCornerTriangle w (D w) τ₁)
    (hτ₂ : G.IsCornerTriangle w (D w) τ₂) (hsτ₁ : s ∈ τ₁.sym2) (hsτ₂ : s ∈ τ₂.sym2)
    (hne : τ₁ ≠ τ₂) {d₁ d₂ : G.StrandDart D} (hd₁ : d₁.1 = yMinus s τ₁)
    (hd₂ : d₂.1 = yMinus s τ₂) :
    (G.strandDiagram hG hD).faceOf d₁ = {d₁, d₂} ∧ (G.strandDiagram hG hD).IsDigon {d₁, d₂} ∧
      (G.strandDiagram hG hD').Isomorphic ((G.strandDiagram hG hD).swivelMove d₁) := by
  obtain ⟨-, -, hface, hdig⟩ :=
    isDigon_strandDiagram_yMinus hG hD hw hs hτ₁ hτ₂ hsτ₁ hsτ₂ hne hd₁ hd₂
  refine ⟨hface, hdig, ?_⟩
  obtain ⟨q₁, m₁, q₂, m₂, q₃, m₃, q₄, m₄, hsq, htri, c1, c2, c3, c4, hT'', htri'', hother, -⟩ :=
    (hD w hw).exists_flip hw.three_le_card hs
  have tri : ∀ {t : Finset H}, t = {q₁, q₂, q₃} ∨ t = {q₁, q₃, q₄} →
      G.IsCornerTriangle w (D w) t := fun ht => ((htri _).2 ht).1
  have k₁ := ne_of_card_eq_three (tri (Or.inl rfl)).2.1
  have k₂ := ne_of_card_eq_three (tri (Or.inr rfl)).2.1
  have hss : s(q₂, q₄) ≠ s := by
    rw [hsq]
    intro e
    rcases Sym2.eq_iff.1 e with ⟨h1, -⟩ | ⟨h1, -⟩
    exacts [k₁.1 h1.symm, k₁.2.2 h1]
  have hs's : s' ≠ s := fun e => hs' (e ▸ hs)
  have hss' : s' = s(q₂, q₄) :=
    RotationSystem.IsCornerTriangulation.eq_of_insert_erase (hD w hw) hw.three_le_card hs hs's
      hss (hD'w ▸ hD' w hw) hT''
  subst hss'
  rw [← hD'w] at htri'' hother
  have tri' : ∀ {t : Finset H}, t = {q₁, q₂, q₄} ∨ t = {q₂, q₃, q₄} →
      G.IsCornerTriangle w (D' w) t := fun ht => ((htri'' _).2 ht).1
  have k₃ := ne_of_card_eq_three (tri' (Or.inl rfl)).2.1
  have h₀ : FlipData G D D' w s s(q₂, q₄) q₁ q₂ q₃ q₄ {q₁, q₂, q₃} {q₁, q₃, q₄} {q₁, q₂, q₄}
      {q₂, q₃, q₄} :=
    { isCrossing := hw
      isWhiteDatum := hD
      isWhiteDatum' := hD'
      agree := hagree
      mem := hs
      mem' := by rw [hD'w]; exact mem_insert_self _ _
      mem_iff := fun e => by rw [hD'w, mem_insert, mem_erase]; tauto
      mem_iff' := fun e => by
        rw [hD'w, mem_insert, mem_erase]
        constructor
        · intro he
          by_cases h1 : e = s
          · exact Or.inl h1
          · exact Or.inr ⟨Or.inr ⟨h1, he⟩, fun h2 => hs' (h2 ▸ he)⟩
        · rintro (rfl | ⟨h1 | ⟨-, h1⟩, h2⟩)
          · exact hs
          · exact absurd h1 h2
          · exact h1
      mem₁ := m₁
      mem₂ := m₂
      mem₃ := m₃
      mem₄ := m₄
      ne₁₂ := k₁.1
      ne₁₃ := k₁.2.1
      ne₁₄ := k₂.2.1
      ne₂₃ := k₁.2.2
      ne₂₄ := k₃.2.2
      ne₃₄ := k₂.2.2
      eq_s := hsq
      eq_s' := rfl
      eq₁ := rfl
      eq₂ := rfl
      eq₁' := rfl
      eq₂' := rfl
      tri₁ := tri (Or.inl rfl)
      tri₂ := tri (Or.inr rfl)
      tri₁' := tri' (Or.inl rfl)
      tri₂' := tri' (Or.inr rfl)
      eq_or := fun t ht hst => (htri t).1 ⟨ht, hst⟩
      eq_or' := fun t ht hst => (htri'' t).1 ⟨ht, hst⟩
      other := fun t ht h1 h2 => ((hother t).1 ⟨ht, h1, h2⟩).1
      other' := fun t ht h1 h2 => ((hother t).2 ⟨ht, h1, h2⟩).1 }
  obtain ⟨e1, e2, e3⟩ := hD.cornerNext_eq_of_isCornerClockwise ⟨w, hw, h₀.tri₁⟩ rfl c1
  obtain ⟨e4, e5, e6⟩ := hD.cornerNext_eq_of_isCornerClockwise ⟨w, hw, h₀.tri₂⟩ rfl c2
  obtain ⟨e7, e8, e9⟩ := hD'.cornerNext_eq_of_isCornerClockwise ⟨w, hw, h₀.tri₁'⟩ rfl c3
  obtain ⟨e10, e11, e12⟩ := hD'.cornerNext_eq_of_isCornerClockwise ⟨w, hw, h₀.tri₂'⟩ rfl c4
  rcases (htri τ₁).1 ⟨hτ₁, hsτ₁⟩ with rfl | rfl
  · exact h₀.strandDiagram_isomorphic hG e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 hd₁
  · exact h₀.rotate.strandDiagram_isomorphic hG e5 e6 e4 e3 e1 e2 e11 e12 e10 e9 e7 e8 hd₁

end FlipIso

/-! ### Uniqueness of generalized triple diagrams -/

section Unique

open RotationSystem

/-- White data agreeing at every crossing have isomorphic strand diagrams. -/
private theorem strandDiagram_isomorphic_of_agree (hG : G.IsPlabicGraph)
    {D D' : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D) (hD' : G.IsWhiteDatum D')
    (h : ∀ x, G.IsCrossing x → D' x = D x) :
    (G.strandDiagram hG hD').Isomorphic (G.strandDiagram hG hD) := by
  have hT : ∀ τ, G.IsDatumTriangle D' τ ↔ G.IsDatumTriangle D τ := fun τ =>
    ⟨fun ⟨w, hw, ht⟩ => ⟨w, hw, h w hw ▸ ht⟩, fun ⟨w, hw, ht⟩ => ⟨w, hw, (h w hw).symm ▸ ht⟩⟩
  have hS : ∀ e τ, G.IsDatumSegment D' e τ ↔ G.IsDatumSegment D e τ := fun e τ =>
    ⟨fun ⟨w, hw, he, ht, hm⟩ => ⟨w, hw, h w hw ▸ he, h w hw ▸ ht, hm⟩,
      fun ⟨w, hw, he, ht, hm⟩ => ⟨w, hw, (h w hw).symm ▸ he, (h w hw).symm ▸ ht, hm⟩⟩
  have hI : ∀ a, G.IsStrandSymbol D' a ↔ G.IsStrandSymbol D a := by
    intro a
    cases a with
    | yPlus e τ => exact hS e τ
    | yMinus e τ => exact hS e τ
    | _ => exact Iff.rfl
  set θ : G.StrandDart D' ≃ G.StrandDart D := Equiv.subtypeEquivRight hI
  have θval : ∀ a, (θ a).1 = a.1 := fun _ => rfl
  refine strandDiagram_isomorphic_of hG hD' _ θ ?_ ?_ ?_ ?_ ?_
  · refine strandDiagram_map_inv_of hG hD'
      (isPreTripleDiagram_strandDiagram hG hD).inv_involutive _ ?_
    rintro ⟨a, ha⟩ (⟨d, rfl⟩ | ⟨e, τ, rfl⟩ | ⟨r, rfl⟩)
    · rfl
    · apply Subtype.ext
      have ha' : G.IsDatumSegment D e τ := (hS e τ).1 ha
      obtain ⟨o1, o2, -⟩ := hD'.otherTriangle_spec (ha : G.IsDatumSegment D' e τ)
      have ho : G.otherTriangle D' e τ = G.otherTriangle D e τ := by
        obtain ⟨-, -, -, -, hm⟩ := id o1
        exact hD.eq_otherTriangle ha' ((hT _).1 (.of_isDatumSegment o1)) hm o2
      change yMinus e (G.otherTriangle D' e τ) = yMinus e (G.otherTriangle D e τ)
      rw [ho]
    · rfl
  · intro a
    apply Subtype.ext
    rw [θval, strandDiagram_rot_apply, strandDiagram_rot_apply, θval]
    rcases IsStrandSymbol.cases hG hD' a.2 with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩ |
      ⟨τ, p, hτ, hp, hr⟩ | ⟨τ, p, hτ, hp, hr⟩ <;> rw [hr]
    · rfl
    · rfl
    · rw [strandRotSym_endSymbol hG, strandRotSym_endSymbol hG]
    · rw [strandRotSym_pairOut hG hτ hp, strandRotSym_pairOut hG ((hT τ).1 hτ) hp]
    · rw [strandRotSym_pairIn hG hD' hτ hp, strandRotSym_pairIn hG hD ((hT τ).1 hτ) hp]
  · intro a
    rw [mem_strandDiagram_bdry, θval]
  · intro a _
    rw [strandDiagram_isOut, θval]
  · intro r
    rfl

/-- `D'` is obtained from the white datum `D` by one flip at one crossing. -/
private structure IsFlipStep (G : PlabicData H b) (D D' : Finset H → Finset (Sym2 H)) :
    Prop where
  isWhiteDatum : G.IsWhiteDatum D
  isWhiteDatum' : G.IsWhiteDatum D'
  exists_flip : ∃ w, G.IsCrossing w ∧ (∀ x, G.IsCrossing x → x ≠ w → D' x = D x) ∧
    ∃ s s', s ∈ D w ∧ s' ∉ D w ∧ D' w = insert s' ((D w).erase s)

/-- Replacing the corner triangulation at one crossing is a sequence of flips. -/
private theorem reflTransGen_isFlipStep_update {E : Finset H → Finset (Sym2 H)}
    (hE : G.IsWhiteDatum E) {w : Finset H} (hw : G.IsCrossing w) {F : Finset (Sym2 H)}
    (hF : G.IsCornerTriangulation w F) :
    Relation.ReflTransGen (IsFlipStep G) E (Function.update E w F) := by
  obtain ⟨hEw, m, _, l, hl, hT₁⟩ := hE w hw
  have hT₂ := hF.isTriangulation_cornerPullback hl
  have hinj := Sym2.map.injective hl.injective
  have hupd : ∀ U, IsTriangulation U →
      G.IsWhiteDatum (Function.update E w (U.image (Sym2.map l))) := by
    intro U hU x hx
    by_cases hxw : x = w
    · subst hxw
      rw [Function.update_self]
      exact (hl.isCornerTriangulation_image_iff U).2 hU
    · rw [Function.update_of_ne hxw]
      exact hE x hx
  have e₂ : Function.update E w ((cornerPullback l F).image (Sym2.map l)) =
      Function.update E w F := by
    rw [hl.image_cornerPullback fun e he => (hF.1 e he).2]
  have e₁ : Function.update E w ((cornerPullback l (E w)).image (Sym2.map l)) = E := by
    rw [hl.image_cornerPullback fun e he => (hEw e he).2, Function.update_eq_self]
  rw [← e₂]
  by_cases hm : 4 ≤ m
  · have key : ∀ U, Relation.ReflTransGen IsFlip (cornerPullback l (E w)) U →
        Relation.ReflTransGen (IsFlipStep G) E
          (Function.update E w (U.image (Sym2.map l))) := by
      intro U hU
      induction hU with
      | refl => rw [e₁]
      | tail _ hstep ih =>
        obtain ⟨γ, γ', hrep, rfl⟩ := hstep
        refine ih.tail ⟨hupd _ hrep.1, hupd _ hrep.2.2.2.2, w, hw, fun x _ hxw => ?_,
          γ.map l, γ'.map l, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne hxw, Function.update_of_ne hxw]
        · rw [Function.update_self]
          exact mem_image_of_mem _ hrep.2.1
        · rw [Function.update_self]
          intro hm'
          exact hrep.2.2.2.1 (hinj.mem_finset_image.1 hm')
        · rw [Function.update_self, Function.update_self, flipTriangulation, image_insert,
            image_erase hinj]
    exact key _ (IsTriangulation.reflTransGen_isFlip hm hT₁ hT₂)
  · have hm3 : m = 3 := by
      have := hl.card_eq
      have := hw.three_le_card
      omega
    rw [IsTriangulation.eq_empty_of_eq_three hm3 hT₂,
      ← IsTriangulation.eq_empty_of_eq_three hm3 hT₁, e₁]

/-- Any two white data are joined by flips, up to their values away from the crossings. -/
private theorem exists_reflTransGen_isFlipStep {D₁ D₂ : Finset H → Finset (Sym2 H)}
    (hD₁ : G.IsWhiteDatum D₁) (hD₂ : G.IsWhiteDatum D₂) :
    ∃ D₃, Relation.ReflTransGen (IsFlipStep G) D₁ D₃ ∧ G.IsWhiteDatum D₃ ∧
      ∀ x, G.IsCrossing x → D₃ x = D₂ x := by
  have key : ∀ S : Finset (Finset H), (∀ x ∈ S, G.IsCrossing x) →
      Relation.ReflTransGen (IsFlipStep G) D₁ (fun x => if x ∈ S then D₂ x else D₁ x) ∧
        G.IsWhiteDatum (fun x => if x ∈ S then D₂ x else D₁ x) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      simp only [notMem_empty, if_false]
      exact ⟨.refl, hD₁⟩
    | insert w S hwS ih =>
      intro hS
      have hw := hS w (mem_insert_self _ _)
      obtain ⟨h1, hE⟩ := ih fun x hx => hS x (mem_insert_of_mem hx)
      have h2 := reflTransGen_isFlipStep_update hE hw (hD₂ w hw)
      have e : Function.update (fun x => if x ∈ S then D₂ x else D₁ x) w (D₂ w) =
          fun x => if x ∈ insert w S then D₂ x else D₁ x := by
        funext x
        by_cases hx : x = w
        · subst hx
          simp
        · rw [Function.update_of_ne hx]
          simp [hx]
      rw [e] at h2
      refine ⟨h1.trans h2, fun x hx => ?_⟩
      dsimp only
      split_ifs
      · exact hD₂ x hx
      · exact hD₁ x hx
  obtain ⟨h1, h2⟩ := key (G.vertices.filter G.IsCrossing) fun x hx => (mem_filter.1 hx).2
  refine ⟨_, h1, h2, fun x hx => ?_⟩
  rw [if_pos (mem_filter.2 ⟨(G.mem_internalVertices.1 hx.1).1, hx⟩)]

/-- One flip of the white datum preserves being a triple diagram and is a swivel move. -/
private theorem IsFlipStep.exists_moveEquivalent (hG : G.IsPlabicGraph)
    {D D' : Finset H → Finset (Sym2 H)} (h : IsFlipStep G D D')
    (hX : (G.strandDiagram hG h.isWhiteDatum).IsTripleDiagram) :
    ∃ hX' : (G.strandDiagram hG h.isWhiteDatum').IsTripleDiagram,
      TripleDiagram.MoveEquivalent
        { Dart := G.StrandDart D, data := G.strandDiagram hG h.isWhiteDatum,
          isTripleDiagram := hX }
        { Dart := G.StrandDart D', data := G.strandDiagram hG h.isWhiteDatum',
          isTripleDiagram := hX' } := by
  obtain ⟨w, hw, hag, s, s', hs, hs', hD'w⟩ := h.exists_flip
  have h2 := (h.isWhiteDatum w hw).card_filter_mem hw.three_le_card hs
  obtain ⟨τ₁, τ₂, hne, hF⟩ := card_eq_two.1 h2
  have m₁ : τ₁ ∈ (G.cornerTriangles w (D w)).filter fun t => s ∈ t.sym2 := by rw [hF]; simp
  have m₂ : τ₂ ∈ (G.cornerTriangles w (D w)).filter fun t => s ∈ t.sym2 := by rw [hF]; simp
  rw [mem_filter, mem_cornerTriangles] at m₁ m₂
  set X := G.strandDiagram hG h.isWhiteDatum
  set d₁ : G.StrandDart D := ⟨yMinus s τ₁, ⟨w, hw, hs, m₁.1, m₁.2⟩⟩
  set d₂ : G.StrandDart D := ⟨yMinus s τ₂, ⟨w, hw, hs, m₂.1, m₂.2⟩⟩
  obtain ⟨hface, hdig, hiso⟩ := isDigon_and_isomorphic_swivelMove_of_flip hG h.isWhiteDatum
    h.isWhiteDatum' hw hag hs hs' hD'w m₁.1 m₂.1 m₁.2 m₂.2 hne (d₁ := d₁) (d₂ := d₂) rfl rfl
  have hd : X.IsDigon (X.faceOf d₁) := hface ▸ hdig
  have hsw := hd.isTripleDiagram_swivelMove hX
  obtain ⟨θ⟩ := hiso
  have hX' := isTripleDiagram_of_iso' θ (isPreTripleDiagram_strandDiagram hG _) hsw
  exact ⟨hX', TripleDiagram.MoveEquivalent.of_isSwivelMove ⟨d₁, hd, ⟨θ.symm⟩⟩⟩

/-- **Generalized triple diagrams are unique up to swivel moves**. Let `G` be a plabic graph and
`X₁, X₂` generalized triple diagrams of `G` such that `X₁` is a triple diagram. Then `X₂` is a
triple diagram and `X₁ ∼ X₂`. -/
@[cluster_algebras "lem_generalized_triple_diagram_unique"]
theorem IsGeneralizedTripleDiagram.exists_moveEquivalent (hG : G.IsPlabicGraph)
    {H₁ H₂ : Type} [Fintype H₁] [DecidableEq H₁] [Fintype H₂] [DecidableEq H₂]
    {X₁ : TripleData H₁ b} {X₂ : TripleData H₂ b} (h₁ : G.IsGeneralizedTripleDiagram hG X₁)
    (h₂ : G.IsGeneralizedTripleDiagram hG X₂) (hX₁ : X₁.IsTripleDiagram) :
    ∃ hX₂ : X₂.IsTripleDiagram,
      TripleDiagram.MoveEquivalent { Dart := H₁, data := X₁, isTripleDiagram := hX₁ }
        { Dart := H₂, data := X₂, isTripleDiagram := hX₂ } := by
  obtain ⟨-, -, D₁, hD₁, ⟨θ₁⟩⟩ := h₁
  obtain ⟨hP₂, -, D₂, hD₂, ⟨θ₂⟩⟩ := h₂
  have hY₁ : (G.strandDiagram hG hD₁).IsTripleDiagram :=
    isTripleDiagram_of_iso' θ₁.symm (isPreTripleDiagram_strandDiagram hG hD₁) hX₁
  obtain ⟨D₃, hchain, hD₃, hagree⟩ := exists_reflTransGen_isFlipStep hD₁ hD₂
  have key : ∀ E, Relation.ReflTransGen (IsFlipStep G) D₁ E → ∀ hE : G.IsWhiteDatum E,
      ∃ hXE : (G.strandDiagram hG hE).IsTripleDiagram,
        TripleDiagram.MoveEquivalent
          { Dart := G.StrandDart D₁, data := G.strandDiagram hG hD₁, isTripleDiagram := hY₁ }
          { Dart := G.StrandDart E, data := G.strandDiagram hG hE, isTripleDiagram := hXE } := by
    intro E hE
    induction hE with
    | refl => exact fun _ => ⟨hY₁, TripleDiagram.MoveEquivalent.refl _⟩
    | tail _ hstep ih =>
      intro _
      obtain ⟨hXE, hm⟩ := ih hstep.isWhiteDatum
      obtain ⟨hXE', hm'⟩ := hstep.exists_moveEquivalent hG hXE
      exact ⟨hXE', hm.trans hm'⟩
  obtain ⟨hY₃, hm₃⟩ := key D₃ hchain hD₃
  obtain ⟨θ₃⟩ := strandDiagram_isomorphic_of_agree hG hD₂ hD₃ hagree
  have hY₂ : (G.strandDiagram hG hD₂).IsTripleDiagram :=
    isTripleDiagram_of_iso' θ₃.symm (isPreTripleDiagram_strandDiagram hG hD₂) hY₃
  have hX₂ : X₂.IsTripleDiagram := isTripleDiagram_of_iso' θ₂ hP₂ hY₂
  refine ⟨hX₂, ?_⟩
  refine (TripleDiagram.MoveEquivalent.of_isomorphic ⟨θ₁⟩).trans (hm₃.trans ?_)
  let Y₂ : TripleDiagram b :=
    { Dart := G.StrandDart D₂, data := G.strandDiagram hG hD₂, isTripleDiagram := hY₂ }
  refine (TripleDiagram.MoveEquivalent.of_isomorphic (X' := Y₂) ⟨θ₃⟩).trans ?_
  exact TripleDiagram.MoveEquivalent.of_isomorphic ⟨θ₂.symm⟩

end Unique

/-! ### Restricting to a set of darts -/

section Restrict

open Function

variable {Y : Set H} [Fintype Y] {G' : PlabicData Y b}

/-- A plabic graph `G'` on a set `Y` of darts of `G` is a **restriction** of `G` when every dart at
a crossing of `G` lies in `Y`, the crossings of `G'` are those of `G` through darts of `Y`, with
the same rotations, and `G'` has the legs and the boundary of `G`. -/
private structure IsRestriction (G : PlabicData H b) (G' : PlabicData Y b) : Prop where
  mem_of_isCrossing : ∀ p : H, G.IsCrossing (G.vertexOf p) → p ∈ Y
  isCrossing_iff : ∀ y : Y, G'.IsCrossing (G'.vertexOf y) ↔ G.IsCrossing (G.vertexOf y)
  rot_eq : ∀ y : Y, G.IsCrossing (G.vertexOf y) → (G'.rot y : H) = G.rot y
  leg_eq : ∀ i, (G'.leg i : H) = G.leg i
  mem_bdry_iff : ∀ y : Y, y ∈ G'.bdry ↔ (y : H) ∈ G.bdry


private theorem IsRestriction.rot_pow (R : IsRestriction G G') {y : Y}
    (hy : G.IsCrossing (G.vertexOf y)) (n : ℕ) :
    ((G'.rot ^ n) y : H) = (G.rot ^ n) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hc : G.IsCrossing (G.vertexOf ((G'.rot ^ n) y)) := by
      rw [ih, G.vertexOf_eq_of_mem ((RotationSystem.mem_vertexOf _).2
        (Equiv.Perm.sameCycle_pow_right.2 (.refl _ _)))]
      exact hy
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [R.rot_eq _ hc, ih]

private theorem IsRestriction.map_vertexOf (R : IsRestriction G G') {y : Y}
    (hy : G.IsCrossing (G.vertexOf y)) :
    (G'.vertexOf y).map (Embedding.subtype _) = G.vertexOf y := by
  ext p
  simp only [mem_map, Embedding.coe_subtype, RotationSystem.mem_vertexOf]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨n, rfl⟩ := hz.exists_nat_pow_eq
    rw [R.rot_pow hy n]
    exact Equiv.Perm.sameCycle_pow_right.2 (.refl _ _)
  · intro hp
    obtain ⟨n, rfl⟩ := hp.exists_nat_pow_eq
    exact ⟨(G'.rot ^ n) y, Equiv.Perm.sameCycle_pow_right.2 (.refl _ _), R.rot_pow hy n⟩

private theorem IsRestriction.isCrossing_of_mem (R : IsRestriction G G') {y z : Y}
    (hy : G.IsCrossing (G.vertexOf y))
    (hz : z ∈ G'.vertexOf y) : G.IsCrossing (G.vertexOf z) := by
  have : (z : H) ∈ G.vertexOf y := by
    rw [← R.map_vertexOf hy]
    exact mem_map_of_mem _ hz
  rwa [G.vertexOf_eq_of_mem this]

private theorem IsRestriction.rot_symm_eq (R : IsRestriction G G') {y : Y}
    (hy : G.IsCrossing (G.vertexOf y)) :
    (G'.rot.symm y : H) = G.rot.symm y := by
  have := R.rot_eq _ (R.isCrossing_of_mem hy (G'.rot_symm_mem_vertexOf y))
  rw [Equiv.apply_symm_apply] at this
  rw [this, Equiv.symm_apply_apply]

private theorem IsRestriction.rot_symm_pow (R : IsRestriction G G') {y : Y}
    (hy : G.IsCrossing (G.vertexOf y)) (n : ℕ) :
    ((G'.rot.symm ^ n) y : H) = (G.rot.symm ^ n) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm : (G'.rot.symm ^ n) y ∈ G'.vertexOf y :=
      RotationSystem.rot_symm_pow_apply_mem_vertexOf y n
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [R.rot_symm_eq (R.isCrossing_of_mem hy hm), ih]

/-- The side of a dart at a crossing. -/
private theorem IsRestriction.cornerSide_eq (R : IsRestriction G G') {y : Y}
    (hy : G.IsCrossing (G.vertexOf y)) :
    G.cornerSide (y : H) = (G'.cornerSide y).map Subtype.val := by
  rw [RotationSystem.cornerSide, RotationSystem.cornerSide, Sym2.map_mk, R.rot_symm_eq hy]

/-- A corner labelling of a crossing of `G'` is one of `G`. -/
private theorem IsRestriction.isCornerLabelling (R : IsRestriction G G') {y : Y}
    (hy : G.IsCrossing (G.vertexOf y)) {m : ℕ}
    {l : ZMod m → Y} (hl : G'.IsCornerLabelling (G'.vertexOf y) l) :
    G.IsCornerLabelling (G.vertexOf y) (fun i => (l i : H)) := by
  refine ⟨⟨fun i _ => ?_, fun i _ j _ h => hl.injective (Subtype.ext h), fun p hp => ?_⟩,
    fun i => ?_⟩
  · rw [Finset.mem_coe, ← R.map_vertexOf hy]
    exact mem_map_of_mem _ (hl.mem i)
  · rw [Finset.mem_coe, ← R.map_vertexOf hy, mem_map] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    obtain ⟨i, rfl⟩ := hl.exists_eq hz
    exact ⟨i, trivial, rfl⟩
  · simp only
    rw [hl.2, R.rot_symm_eq (R.isCrossing_of_mem hy (hl.mem i))]

omit [Fintype H] [Fintype Y] in
private theorem cornerPullback_map {m : ℕ} [NeZero m] (l : ZMod m → Y) (E : Finset (Sym2 Y)) :
    RotationSystem.cornerPullback (fun i => (l i : H)) (E.map (Embedding.subtype _).sym2Map) =
      RotationSystem.cornerPullback l E := by
  ext e
  rw [RotationSystem.mem_cornerPullback, RotationSystem.mem_cornerPullback]
  have : e.map (fun i => (l i : H)) = (Embedding.subtype _).sym2Map (e.map l) := by
    rw [Embedding.sym2Map_apply, Sym2.map_map]
    rfl
  rw [this, mem_map' (Embedding.subtype _).sym2Map]

/-- **Corner triangulations of a crossing of a restriction.** -/
private theorem IsRestriction.isCornerTriangulation_iff (R : IsRestriction G G') {y : Y}
    (hy : G.IsCrossing (G.vertexOf y))
    {E : Finset (Sym2 Y)} :
    G'.IsCornerTriangulation (G'.vertexOf y) E ↔
      G.IsCornerTriangulation (G.vertexOf y) (E.map (Embedding.subtype _).sym2Map) := by
  constructor
  · rintro ⟨hE, m, _, l, hl, hT⟩
    refine ⟨fun e he => ?_, m, inferInstance, fun i => (l i : H), R.isCornerLabelling hy hl, ?_⟩
    · obtain ⟨e', he', rfl⟩ := mem_map.1 he
      refine ⟨?_, fun x hx => ?_⟩
      · rw [Embedding.sym2Map_apply, Sym2.isDiag_map (Embedding.injective _)]
        exact (hE e' he').1
      · rw [Embedding.sym2Map_apply, Sym2.mem_map] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [← R.map_vertexOf hy]
        exact mem_map_of_mem _ ((hE e' he').2 z hz)
    · rwa [cornerPullback_map]
  · rintro ⟨hE, m, _, l, hl, hT⟩
    refine ⟨fun e he => ?_, ?_⟩
    · have h := hE _ (mem_map_of_mem (Embedding.subtype _).sym2Map he)
      refine ⟨?_, fun x hx => ?_⟩
      · have h1 := h.1
        rwa [Embedding.sym2Map_apply, Sym2.isDiag_map (Embedding.injective _)] at h1
      · have h2 := h.2 x (by rw [Embedding.sym2Map_apply]; exact Sym2.mem_map.2 ⟨x, hx, rfl⟩)
        rw [← R.map_vertexOf hy, mem_map] at h2
        obtain ⟨z, hz, hzx⟩ := h2
        rwa [← Subtype.ext hzx]
    · set n := (G'.vertexOf y).card
      have hn : 0 < n := card_pos.2 ⟨y, G'.self_mem_vertexOf y⟩
      haveI : NeZero n := ⟨by omega⟩
      have hl' := RotationSystem.isCornerLabelling_rot_symm_pow (R := G'.toRotationSystem) y rfl
      refine ⟨n, inferInstance, _, hl', ?_⟩
      have := (show G.IsCornerTriangulation (G.vertexOf y) (E.map (Embedding.subtype _).sym2Map)
        from ⟨hE, m, inferInstance, l, hl, hT⟩).isTriangulation_cornerPullback
        (R.isCornerLabelling hy hl')
      rwa [cornerPullback_map] at this

/-- **Corner triangles of a crossing of a restriction.** -/
private theorem IsRestriction.isCornerTriangle_iff (R : IsRestriction G G') {y : Y}
    (hy : G.IsCrossing (G.vertexOf y))
    {E : Finset (Sym2 Y)} {τ : Finset Y} :
    G'.IsCornerTriangle (G'.vertexOf y) E τ ↔
      G.IsCornerTriangle (G.vertexOf y) (E.map (Embedding.subtype _).sym2Map)
        (τ.map (Embedding.subtype _)) := by
  have hseg : ∀ u v : Y, s((u : H), (v : H)) ∈ G.cornerSegments (G.vertexOf y)
      (E.map (Embedding.subtype _).sym2Map) ↔ s(u, v) ∈ G'.cornerSegments (G'.vertexOf y) E := by
    intro u v
    rw [RotationSystem.mem_cornerSegments, RotationSystem.mem_cornerSegments]
    have e1 : s((u : H), (v : H)) = (Embedding.subtype _).sym2Map s(u, v) := rfl
    rw [e1, mem_map' (Embedding.subtype _).sym2Map]
    refine or_congr Iff.rfl ⟨fun ⟨a, ha, hae⟩ => ?_, fun ⟨a, ha, hae⟩ => ?_⟩
    · rw [← R.map_vertexOf hy, mem_map] at ha
      obtain ⟨a', ha', rfl⟩ := ha
      refine ⟨a', ha', ?_⟩
      rw [Embedding.coe_subtype, R.cornerSide_eq (R.isCrossing_of_mem hy ha')] at hae
      exact Sym2.map.injective Subtype.val_injective hae
    · refine ⟨a, ?_, ?_⟩
      · rw [← R.map_vertexOf hy]
        exact mem_map_of_mem _ ha
      · rw [R.cornerSide_eq (R.isCrossing_of_mem hy ha), hae]
        rfl
  constructor
  · rintro ⟨hsub, hcard, hs⟩
    refine ⟨?_, by rw [card_map]; exact hcard, fun u hu v hv huv => ?_⟩
    · rw [← R.map_vertexOf hy]
      exact map_subset_map.2 hsub
    · obtain ⟨u', hu', rfl⟩ := mem_map.1 hu
      obtain ⟨v', hv', rfl⟩ := mem_map.1 hv
      exact (hseg u' v').2 (hs u' hu' v' hv' fun h => huv (by rw [h]))
  · rintro ⟨hsub, hcard, hs⟩
    refine ⟨?_, by rw [card_map] at hcard; exact hcard, fun u hu v hv huv => ?_⟩
    · rw [← R.map_vertexOf hy] at hsub
      exact map_subset_map.1 hsub
    · exact (hseg u v).1 (hs _ (mem_map_of_mem _ hu) _ (mem_map_of_mem _ hv)
        fun h => huv (Subtype.ext h))

/-- **Clockwise successors at a crossing of a restriction.** -/
private theorem IsRestriction.cornerNext_eq (R : IsRestriction G G') {y : Y}
    (hy : G.IsCrossing (G.vertexOf y)) (τ : Finset Y) :
    G.cornerNext (τ.map (Embedding.subtype _)) (y : H) = G'.cornerNext τ y := by
  have hP : ∀ k : ℕ, (0 < k ∧ (G.rot.symm ^ k) (y : H) ∈ τ.map (Embedding.subtype _) ∧
      (G.rot.symm ^ k) (y : H) ≠ y) ↔
      (0 < k ∧ (G'.rot.symm ^ k) y ∈ τ ∧ (G'.rot.symm ^ k) y ≠ y) := by
    intro k
    have hm : ∀ z : Y, (z : H) ∈ τ.map (Embedding.subtype _) ↔ z ∈ τ := fun z => mem_map' _
    rw [← R.rot_symm_pow hy k, hm]
    exact and_congr Iff.rfl (and_congr Iff.rfl (by rw [Ne, Ne, Subtype.ext_iff]))
  classical
  unfold RotationSystem.cornerNext
  by_cases h' : ∃ k : ℕ, 0 < k ∧ (G'.rot.symm ^ k) y ∈ τ ∧ (G'.rot.symm ^ k) y ≠ y
  · have h : ∃ k : ℕ, 0 < k ∧ (G.rot.symm ^ k) (y : H) ∈ τ.map (Embedding.subtype _) ∧
        (G.rot.symm ^ k) (y : H) ≠ y := let ⟨k, hk⟩ := h'; ⟨k, (hP k).2 hk⟩
    rw [dif_pos h, dif_pos h']
    have e : Nat.find h = Nat.find h' := le_antisymm (Nat.find_min' h ((hP _).2 (Nat.find_spec h')))
      (Nat.find_min' h' ((hP _).1 (Nat.find_spec h)))
    rw [e, R.rot_symm_pow hy]
  · have h : ¬∃ k : ℕ, 0 < k ∧ (G.rot.symm ^ k) (y : H) ∈ τ.map (Embedding.subtype _) ∧
        (G.rot.symm ^ k) (y : H) ≠ y := fun ⟨k, hk⟩ => h' ⟨k, (hP k).1 hk⟩
    rw [dif_neg h, dif_neg h']

/-- A crossing of `G'` is the vertex of one of its darts, at a crossing of `G`. -/
private theorem IsRestriction.exists_of_isCrossing (R : IsRestriction G G') {x : Finset Y}
    (hx : G'.IsCrossing x) : ∃ y : Y, x = G'.vertexOf y ∧ G.IsCrossing (G.vertexOf y) := by
  obtain ⟨y, rfl⟩ := G'.mem_vertices.1 (G'.mem_internalVertices.1 hx.1).1
  exact ⟨y, rfl, (R.isCrossing_iff y).1 hx⟩

omit [Fintype H] [DecidableEq H] [Fintype Y] in
private theorem map_mem_sym2_map_iff {e : Sym2 Y} {τ : Finset Y} :
    e.map Subtype.val ∈ (τ.map (Embedding.subtype _)).sym2 ↔ e ∈ τ.sym2 := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [Sym2.map_mk, mk_mem_sym2_iff, mk_mem_sym2_iff]
    exact and_congr (mem_map' (Embedding.subtype _)) (mem_map' (Embedding.subtype _))

/-- White data of `G` and of a restriction `G'` that agree at every crossing. -/
private def RestrictRel (G : PlabicData H b) (G' : PlabicData Y b)
    (D' : Finset Y → Finset (Sym2 Y)) (D : Finset H → Finset (Sym2 H)) : Prop :=
  ∀ y : Y, G.IsCrossing (G.vertexOf y) →
    D (G.vertexOf y) = (D' (G'.vertexOf y)).map (Embedding.subtype _).sym2Map

section RestrictData

variable {D' : Finset Y → Finset (Sym2 Y)} {D : Finset H → Finset (Sym2 H)}

private theorem IsRestriction.isDatumSegment_iff (R : IsRestriction G G')
    (hrel : RestrictRel G G' D' D) {e : Sym2 Y} {τ : Finset Y} :
    G'.IsDatumSegment D' e τ ↔
      G.IsDatumSegment D (e.map Subtype.val) (τ.map (Embedding.subtype _)) := by
  constructor
  · rintro ⟨x, hx, he, ht, hm⟩
    obtain ⟨y, rfl, hy⟩ := R.exists_of_isCrossing hx
    refine ⟨G.vertexOf y, hy, ?_, ?_, map_mem_sym2_map_iff.2 hm⟩
    · rw [hrel y hy]
      exact mem_map_of_mem (Embedding.subtype _).sym2Map he
    · rw [hrel y hy]
      exact (R.isCornerTriangle_iff hy).1 ht
  · rintro ⟨x, hx, he, ht, hm⟩
    obtain ⟨u, hu⟩ : τ.Nonempty := by
      rw [← card_pos]
      have := ht.2.1
      rw [card_map] at this
      omega
    have hxu : x = G.vertexOf u := hx.eq_vertexOf (ht.1 (mem_map_of_mem _ hu))
    subst hxu
    refine ⟨G'.vertexOf u, (R.isCrossing_iff u).2 hx, ?_, ?_, map_mem_sym2_map_iff.1 hm⟩
    · rw [hrel u hx] at he
      exact (mem_map' (Embedding.subtype _).sym2Map).1 he
    · rw [hrel u hx] at ht
      exact (R.isCornerTriangle_iff hx).2 ht

private theorem IsRestriction.isDatumTriangle_iff (R : IsRestriction G G')
    (hrel : RestrictRel G G' D' D) {τ : Finset Y} :
    G'.IsDatumTriangle D' τ ↔ G.IsDatumTriangle D (τ.map (Embedding.subtype _)) := by
  constructor
  · rintro ⟨x, hx, ht⟩
    obtain ⟨y, rfl, hy⟩ := R.exists_of_isCrossing hx
    exact ⟨G.vertexOf y, hy, by rw [hrel y hy]; exact (R.isCornerTriangle_iff hy).1 ht⟩
  · rintro ⟨x, hx, ht⟩
    obtain ⟨u, hu⟩ : τ.Nonempty := by
      rw [← card_pos]
      have := ht.2.1
      rw [card_map] at this
      omega
    have hxu : x = G.vertexOf u := hx.eq_vertexOf (ht.1 (mem_map_of_mem _ hu))
    subst hxu
    refine ⟨G'.vertexOf u, (R.isCrossing_iff u).2 hx, ?_⟩
    rw [hrel u hx] at ht
    exact (R.isCornerTriangle_iff hx).2 ht

omit [Fintype H] [DecidableEq H] [Fintype Y] in
/-- A set of darts inside `Y` is the image of a set of darts of `G'`. -/
private theorem exists_map_eq_of_subset {τ₀ : Finset H} (h : ∀ x ∈ τ₀, x ∈ Y) :
    ∃ τ : Finset Y, τ.map (Embedding.subtype _) = τ₀ := by
  classical
  exact ⟨τ₀.subtype (· ∈ Y), subtype_map_of_mem h⟩

omit [Fintype H] [DecidableEq H] [Fintype Y] in
private theorem exists_sym2_map_eq {e₀ : Sym2 H} (h : ∀ x ∈ e₀, x ∈ Y) :
    ∃ e : Sym2 Y, e.map Subtype.val = e₀ := by
  induction e₀ using Sym2.ind with
  | _ u v => exact ⟨s(⟨u, h u (Sym2.mem_mk_left _ _)⟩, ⟨v, h v (Sym2.mem_mk_right _ _)⟩), rfl⟩

/-- Every dart of a triangle of a white datum of `G` lies in `Y`. -/
private theorem IsRestriction.mem_of_isDatumTriangle (R : IsRestriction G G') {τ : Finset H}
    (hτ : G.IsDatumTriangle D τ) {p : H} (hp : p ∈ τ) : p ∈ Y :=
  R.mem_of_isCrossing p (hτ.vertexOf hp).1

end RestrictData

/-- The symbols of `X°(G', D')` sent to those of `X°(G, D)`: `x⁺_c ↦ x⁺_c`, `x⁻_t ↦ x⁻_{t₀}` for
the dart `t₀` of `G` with `t̄₀ = t̄` (the reverse in `G'`), and `y^±_{e,τ} ↦ y^±_{e,τ}`. -/
private def restrictSym (G : PlabicData H b) (G' : PlabicData Y b) :
    StrandSymbol Y b → StrandSymbol H b
  | xPlus c => xPlus c
  | xMinus t => xMinus (G.inv (G'.inv t))
  | yPlus e τ => yPlus (e.map Subtype.val) (τ.map (Embedding.subtype _))
  | yMinus e τ => yMinus (e.map Subtype.val) (τ.map (Embedding.subtype _))
  | bd r => bd r
  | bd' r => bd' r

omit [Fintype H] [DecidableEq H] [Fintype Y] in
private theorem restrictSym_injective : Injective (restrictSym (b := b) G G') := by
  intro a a' h
  cases a <;> cases a' <;> simp only [restrictSym, reduceCtorEq] at h
  · rw [Subtype.ext (xPlus.inj h)]
  · rw [G'.inv.injective (Subtype.ext (G.inv.injective (xMinus.inj h)))]
  · obtain ⟨h1, h2⟩ := yPlus.inj h
    rw [Sym2.map.injective Subtype.val_injective h1, map_injective _ h2]
  · obtain ⟨h1, h2⟩ := yMinus.inj h
    rw [Sym2.map.injective Subtype.val_injective h1, map_injective _ h2]
  · rw [bd.inj h]
  · rw [bd'.inj h]

section RestrictPlabic

variable (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)

include hG hG'

omit hG hG' in
private theorem IsRestriction.isLeg_iff (R : IsRestriction G G') (y : Y) :
    G'.IsLeg y ↔ G.IsLeg y :=
  ⟨fun ⟨i, hi⟩ => ⟨i, by rw [← R.leg_eq, hi]⟩,
    fun ⟨i, hi⟩ => ⟨i, Subtype.ext (by rw [R.leg_eq, hi])⟩⟩

omit hG hG' in
private theorem IsRestriction.isInitial_iff (R : IsRestriction G G') (y : Y) :
    G'.IsInitial y ↔ G.IsInitial y := by
  unfold IsInitial
  rw [R.mem_bdry_iff, R.isCrossing_iff, R.isLeg_iff]

private theorem IsRestriction.isBoundaryVertex_iff (R : IsRestriction G G') {y : Y}
    (hy : y ∉ G'.bdry) :
    G'.IsBoundaryVertex (G'.vertexOf y) ↔ G.IsBoundaryVertex (G.vertexOf y) := by
  have hy' : (y : H) ∉ G.bdry := (R.mem_bdry_iff y).not.1 hy
  constructor
  · intro h
    exact hG.isBoundaryVertex_of_isLeg ((R.isLeg_iff y).1 (hG'.isLeg_of_isBoundaryVertex hy h))
  · intro h
    exact hG'.isBoundaryVertex_of_isLeg ((R.isLeg_iff y).2 (hG.isLeg_of_isBoundaryVertex hy' h))

private theorem IsRestriction.isTerminal_iff (R : IsRestriction G G') (t : Y) :
    G'.IsTerminal t ↔ G.IsTerminal (G.inv (G'.inv t)) := by
  unfold IsTerminal
  rw [hG.inv_involutive]
  have e1 : t ∉ G'.bdry ↔ G.inv (G'.inv t) ∉ G.bdry := by
    rw [hG.inv_mem_bdry_iff, ← R.mem_bdry_iff, hG'.inv_mem_bdry_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hq : G'.inv t ∉ G'.bdry := fun h => h1 (hG'.inv_mem_bdry_iff.1 h)
    exact ⟨e1.1 h1, h2.imp (R.isCrossing_iff _).1 (R.isBoundaryVertex_iff hG hG' hq).1⟩
  · rintro ⟨h1, h2⟩
    have h1' := e1.2 h1
    have hq : G'.inv t ∉ G'.bdry := fun h => h1' (hG'.inv_mem_bdry_iff.1 h)
    exact ⟨h1', h2.imp (R.isCrossing_iff _).2 (R.isBoundaryVertex_iff hG hG' hq).2⟩

omit hG hG' in
/-- A dart of `G` that is initial, or the reverse of a terminal dart, lies in `Y`. -/
private theorem IsRestriction.mem_of_isInitial (R : IsRestriction G G') {p : H}
    (hp : G.IsInitial p) : p ∈ Y := by
  rcases hp.2 with h | ⟨i, rfl⟩
  · exact R.mem_of_isCrossing p h
  · rw [← R.leg_eq]
    exact (G'.leg i).2

omit hG' in
private theorem IsRestriction.inv_mem_of_isTerminal (R : IsRestriction G G') {t : H}
    (ht : G.IsTerminal t) : G.inv t ∈ Y := by
  rcases ht.2 with h | h
  · exact R.mem_of_isCrossing _ h
  · have hq : G.inv t ∉ G.bdry := fun h' => ht.1 (hG.inv_mem_bdry_iff.1 h')
    obtain ⟨i, hi⟩ := hG.isLeg_of_isBoundaryVertex hq h
    rw [← hi, ← R.leg_eq]
    exact (G'.leg i).2

omit hG in
private theorem IsRestriction.restrictSym_endSymbol (R : IsRestriction G G') (r : Fin (2 * b)) :
    restrictSym G G' (G'.endSymbol r) = G.endSymbol r := by
  rcases exists_sourceIndex_or_targetIndex r with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [endSymbol_sourceIndex, endSymbol_sourceIndex]
    exact congrArg xPlus (R.leg_eq i)
  · rw [endSymbol_targetIndex, endSymbol_targetIndex]
    change xMinus (G.inv (G'.inv (G'.inv (G'.leg i)) : H)) = _
    rw [hG'.inv_involutive, R.leg_eq]

variable {D' : Finset Y → Finset (Sym2 Y)} {D : Finset H → Finset (Sym2 H)}
  (hD' : G'.IsWhiteDatum D') (hD : G.IsWhiteDatum D)

private theorem IsRestriction.isStrandSymbol_restrictSym (R : IsRestriction G G')
    (hrel : RestrictRel G G' D' D) {a : StrandSymbol Y b} (ha : G'.IsStrandSymbol D' a) :
    G.IsStrandSymbol D (restrictSym G G' a) := by
  cases a with
  | xPlus c => exact (R.isInitial_iff c).1 ha
  | xMinus t => exact (R.isTerminal_iff hG hG' t).1 ha
  | yPlus e τ => exact (R.isDatumSegment_iff hrel).1 ha
  | yMinus e τ => exact (R.isDatumSegment_iff hrel).1 ha
  | bd r => trivial
  | bd' r => trivial

private theorem IsRestriction.exists_restrictSym_eq (R : IsRestriction G G')
    (hrel : RestrictRel G G' D' D) {a : StrandSymbol H b} (ha : G.IsStrandSymbol D a) :
    ∃ a', G'.IsStrandSymbol D' a' ∧ restrictSym G G' a' = a := by
  cases a with
  | xPlus d =>
    have hd : G.IsInitial d := ha
    refine ⟨xPlus ⟨d, R.mem_of_isInitial hd⟩, ?_, rfl⟩
    exact (R.isInitial_iff _).2 hd
  | xMinus t =>
    have ht : G.IsTerminal t := ha
    set q : Y := ⟨G.inv t, R.inv_mem_of_isTerminal hG ht⟩
    have e : restrictSym (b := b) G G' (xMinus (G'.inv q)) = xMinus t := by
      change xMinus (G.inv (G'.inv (G'.inv q) : H)) = _
      rw [hG'.inv_involutive, hG.inv_involutive]
    refine ⟨xMinus (G'.inv q), ?_, e⟩
    exact (R.isTerminal_iff hG hG' _).2 (by rw [hG'.inv_involutive, hG.inv_involutive]; exact ht)
  | yPlus e τ =>
    have h : G.IsDatumSegment D e τ := ha
    have hτY : ∀ x ∈ τ, x ∈ Y := fun x hx => R.mem_of_isDatumTriangle (.of_isDatumSegment h) hx
    obtain ⟨τ', rfl⟩ := exists_map_eq_of_subset hτY
    obtain ⟨e', rfl⟩ := exists_sym2_map_eq (fun x hx => hτY x
      (mem_sym2_iff.1 (let ⟨_, _, _, _, hm⟩ := h; hm) x hx))
    exact ⟨yPlus e' τ', (R.isDatumSegment_iff hrel).2 h, rfl⟩
  | yMinus e τ =>
    have h : G.IsDatumSegment D e τ := ha
    have hτY : ∀ x ∈ τ, x ∈ Y := fun x hx => R.mem_of_isDatumTriangle (.of_isDatumSegment h) hx
    obtain ⟨τ', rfl⟩ := exists_map_eq_of_subset hτY
    obtain ⟨e', rfl⟩ := exists_sym2_map_eq (fun x hx => hτY x
      (mem_sym2_iff.1 (let ⟨_, _, _, _, hm⟩ := h; hm) x hx))
    exact ⟨yMinus e' τ', (R.isDatumSegment_iff hrel).2 h, rfl⟩
  | bd r => exact ⟨bd r, trivial, rfl⟩
  | bd' r => exact ⟨bd' r, trivial, rfl⟩

include hD' hD in
/-- **The strand diagrams of a restriction.** If the chains of `G` and `G'` from each initial dart
arrive at the same dart, then the strand diagrams of white data of `G` and `G'` agreeing at every
crossing are isomorphic. -/
private theorem IsRestriction.strandDiagram_isomorphic (R : IsRestriction G G')
    (hend : ∀ c : Y, G'.IsInitial c → G.inv (G.chainEnd c) = G'.inv (G'.chainEnd c))
    (hrel : RestrictRel G G' D' D) :
    (G'.strandDiagram hG' hD').Isomorphic (G.strandDiagram hG hD) := by
  set X := G.strandDiagram hG hD
  set X' := G'.strandDiagram hG' hD'
  set f : G'.StrandDart D' → G.StrandDart D := fun a =>
    ⟨restrictSym G G' a.1, R.isStrandSymbol_restrictSym hG hG' hrel a.2⟩ with hf
  have hfval : ∀ a, (f a).1 = restrictSym G G' a.1 := fun _ => rfl
  have hbij : Bijective f := by
    refine ⟨fun a a' h => Subtype.ext (restrictSym_injective (congrArg Subtype.val h)),
      fun a => ?_⟩
    obtain ⟨a', ha', e⟩ := R.exists_restrictSym_eq hG hG' hrel a.2
    exact ⟨⟨a', ha'⟩, Subtype.ext e⟩
  set θ := Equiv.ofBijective f hbij
  have θval : ∀ a, (θ a).1 = restrictSym G G' a.1 := fun _ => rfl
  -- pair symbols
  have hpair : ∀ {τ : Finset Y} (hτ : G'.IsDatumTriangle D' τ) {p : Y} (hp : p ∈ τ),
      restrictSym G G' (G'.pairOut τ p) = G.pairOut (τ.map (Embedding.subtype _)) p ∧
      restrictSym G G' (G'.pairIn τ p) = G.pairIn (τ.map (Embedding.subtype _)) p := by
    intro τ hτ p hp
    have hc : G.IsCrossing (G.vertexOf p) := (R.isCrossing_iff p).1 (hτ.vertexOf hp).1
    have hcn := R.cornerNext_eq hc τ
    have hiff : G.cornerNext (τ.map (Embedding.subtype _)) p = G.rot.symm p ↔
        G'.cornerNext τ p = G'.rot.symm p := by
      rw [hcn, ← R.rot_symm_eq hc, Subtype.val_inj]
    unfold pairOut pairIn
    by_cases h : G'.cornerNext τ p = G'.rot.symm p
    · rw [if_pos h, if_pos h, if_pos (hiff.2 h), if_pos (hiff.2 h)]
      refine ⟨rfl, ?_⟩
      change xMinus (G.inv (G'.inv (G'.inv p) : H)) = _
      rw [hG'.inv_involutive]
    · rw [if_neg h, if_neg h, if_neg (mt hiff.1 h), if_neg (mt hiff.1 h), hcn]
      exact ⟨rfl, rfl⟩
  refine strandDiagram_isomorphic_of hG' hD' X θ ?_ ?_ ?_ ?_ ?_
  · refine strandDiagram_map_inv_of hG' hD' (isPreTripleDiagram_strandDiagram hG hD).inv_involutive
      _ ?_
    rintro ⟨a, ha⟩ (⟨c, rfl⟩ | ⟨e, τ, rfl⟩ | ⟨r, rfl⟩)
    · apply Subtype.ext
      rw [θval, strandDiagram_inv_apply, strandDiagram_inv_apply, θval]
      change xMinus (G.inv (G'.inv (G'.chainEnd c) : H)) = xMinus (G.chainEnd c)
      rw [← hend c ha, hG.inv_involutive]
    · apply Subtype.ext
      rw [θval, strandDiagram_inv_apply, strandDiagram_inv_apply, θval]
      have hseg : G'.IsDatumSegment D' e τ := ha
      obtain ⟨o1, o2, -⟩ := hD'.otherTriangle_spec hseg
      have ho : (G'.otherTriangle D' e τ).map (Embedding.subtype _) =
          G.otherTriangle D (e.map Subtype.val) (τ.map (Embedding.subtype _)) := by
        refine hD.eq_otherTriangle ((R.isDatumSegment_iff hrel).1 hseg)
          ((R.isDatumTriangle_iff hrel).1 (.of_isDatumSegment o1)) ?_
          (fun h => o2 (map_injective _ h))
        obtain ⟨-, -, -, -, hm⟩ := (R.isDatumSegment_iff hrel).1 o1
        exact hm
      change yMinus (e.map Subtype.val) ((G'.otherTriangle D' e τ).map (Embedding.subtype _)) =
        yMinus (e.map Subtype.val) (G.otherTriangle D (e.map Subtype.val)
          (τ.map (Embedding.subtype _)))
      rw [ho]
    · rfl
  · intro a
    apply Subtype.ext
    rw [θval, strandDiagram_rot_apply, strandDiagram_rot_apply, θval]
    rcases IsStrandSymbol.cases hG' hD' a.2 with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩ |
      ⟨τ, p, hτ, hp, hr⟩ | ⟨τ, p, hτ, hp, hr⟩ <;> rw [hr]
    · rw [strandRotSym_bd, R.restrictSym_endSymbol hG']
      rfl
    · rfl
    · rw [strandRotSym_endSymbol hG', R.restrictSym_endSymbol hG', strandRotSym_endSymbol hG]
      rfl
    · have hτ' := (R.isDatumTriangle_iff hrel).1 hτ
      have hp' : (p : H) ∈ τ.map (Embedding.subtype _) := mem_map_of_mem _ hp
      rw [strandRotSym_pairOut hG' hτ hp, (hpair hτ hp).1, (hpair hτ hp).2,
        strandRotSym_pairOut hG hτ' hp']
    · have hτ' := (R.isDatumTriangle_iff hrel).1 hτ
      have hp' : (p : H) ∈ τ.map (Embedding.subtype _) := mem_map_of_mem _ hp
      have hq := hD'.cornerNext_mem hτ hp
      have hq' := hD'.cornerNext_mem hτ hq
      have hc : ∀ z ∈ τ, G.IsCrossing (G.vertexOf z) := fun z hz =>
        (R.isCrossing_iff z).1 (hτ.vertexOf hz).1
      rw [strandRotSym_pairIn hG' hD' hτ hp, (hpair hτ hq').1, (hpair hτ hp).2,
        strandRotSym_pairIn hG hD hτ' hp', R.cornerNext_eq (hc p hp),
        R.cornerNext_eq (hc _ hq)]
  · intro a
    rw [mem_strandDiagram_bdry, θval]
    obtain ⟨a, ha⟩ := a
    cases a <;> exact Iff.rfl
  · rintro ⟨a, ha⟩ -
    rw [strandDiagram_isOut, θval]
    cases a <;> rfl
  · intro r
    exact Subtype.ext (R.restrictSym_endSymbol hG' r)

end RestrictPlabic

private theorem IsRestriction.exists_restrictRel_of_isWhiteDatum (R : IsRestriction G G')
    {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D) :
    ∃ D' : Finset Y → Finset (Sym2 Y), G'.IsWhiteDatum D' ∧ RestrictRel G G' D' D := by
  set D' : Finset Y → Finset (Sym2 Y) := fun x' =>
    (D (x'.map (Embedding.subtype _))).preimage (Sym2.map Subtype.val)
      (Sym2.map.injective Subtype.val_injective).injOn with hD'def
  have hrel : RestrictRel G G' D' D := by
    intro y hy
    simp only [hD'def]
    rw [R.map_vertexOf hy]
    ext e
    constructor
    · intro he
      obtain ⟨e', rfl⟩ := exists_sym2_map_eq (Y := Y) fun x hx => R.mem_of_isCrossing x (by
        rw [hy.eq_vertexOf ((hD _ hy).1 e he |>.2 x hx)] at hy; exact hy)
      exact mem_map_of_mem (Embedding.subtype _).sym2Map (mem_preimage.2 he)
    · intro he
      obtain ⟨e', he', rfl⟩ := mem_map.1 he
      exact mem_preimage.1 he'
  refine ⟨D', fun x' hx' => ?_, hrel⟩
  obtain ⟨y, rfl, hy⟩ := R.exists_of_isCrossing hx'
  rw [R.isCornerTriangulation_iff hy, ← hrel y hy]
  exact hD _ hy

private theorem IsRestriction.exists_restrictRel_of_isWhiteDatum' (R : IsRestriction G G')
    {D' : Finset Y → Finset (Sym2 Y)} (hD' : G'.IsWhiteDatum D') :
    ∃ D : Finset H → Finset (Sym2 H), G.IsWhiteDatum D ∧ RestrictRel G G' D' D := by
  classical
  set D : Finset H → Finset (Sym2 H) := fun x =>
    (D' (x.subtype (· ∈ Y))).map (Embedding.subtype _).sym2Map with hDdef
  have hsub : ∀ s : Finset Y, (s.map (Embedding.subtype _)).subtype (· ∈ Y) = s := by
    intro s
    ext z
    simp [mem_subtype, mem_map]
  have hrel : RestrictRel G G' D' D := by
    intro y hy
    simp only [hDdef]
    rw [← R.map_vertexOf hy, hsub]
  refine ⟨D, fun x hx => ?_, hrel⟩
  obtain ⟨p, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hx.1).1
  have hp : p ∈ Y := R.mem_of_isCrossing p hx
  have hy : G.IsCrossing (G.vertexOf ((⟨p, hp⟩ : Y) : H)) := hx
  rw [hrel ⟨p, hp⟩ hy]
  exact (R.isCornerTriangulation_iff hy).1 (hD' _ ((R.isCrossing_iff _).2 hy))

/-- **Generalized triple diagrams of a restriction.** If `G'` is a restriction of `G` whose chains
from initial darts arrive where those of `G` do, and every trip of `G` meets an initial dart
exactly when every trip of `G'` does, then `G` and `G'` have the same generalized triple
diagrams. -/
private theorem IsRestriction.isGeneralizedTripleDiagram_iff (R : IsRestriction G G')
    (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (hend : ∀ c : Y, G'.IsInitial c → G.inv (G.chainEnd c) = G'.inv (G'.chainEnd c))
    (horb : (∀ d ∉ G.bdry, ∃ e ∈ G.trip d, G.IsInitial e) ↔
      ∀ d ∉ G'.bdry, ∃ e ∈ G'.trip d, G'.IsInitial e)
    {H'' : Type*} [Fintype H''] [DecidableEq H''] (X : TripleData H'' b) :
    G.IsGeneralizedTripleDiagram hG X ↔ G'.IsGeneralizedTripleDiagram hG' X := by
  constructor
  · rintro ⟨hX, ho, D, hD, ⟨θ⟩⟩
    obtain ⟨D', hD', hrel⟩ := R.exists_restrictRel_of_isWhiteDatum hD
    obtain ⟨θ'⟩ := R.strandDiagram_isomorphic hG hG' hD' hD hend hrel
    exact ⟨hX, horb.1 ho, D', hD', ⟨θ.trans θ'.symm⟩⟩
  · rintro ⟨hX, ho, D', hD', ⟨θ⟩⟩
    obtain ⟨D, hD, hrel⟩ := R.exists_restrictRel_of_isWhiteDatum' hD'
    obtain ⟨θ'⟩ := R.strandDiagram_isomorphic hG hG' hD' hD hend hrel
    exact ⟨hX, horb.2 ho, D, hD, ⟨θ.trans θ'⟩⟩

/-- A crossing of `G'` at `y` is one of `G` when the vertex of `y` in `G'` is that of `G` read in
`H`, with the same colours and the same boundary status. -/
private theorem isCrossing_iff_of_map_vertexOf {y : Y}
    (hmap : (G'.vertexOf y).map (Embedding.subtype _) = G.vertexOf y)
    (hbv : G'.IsBoundaryVertex (G'.vertexOf y) ↔ G.IsBoundaryVertex (G.vertexOf y))
    (hcol : ∀ z : Y, G'.colour z = G.colour z) :
    G'.IsCrossing (G'.vertexOf y) ↔ G.IsCrossing (G.vertexOf y) := by
  unfold IsCrossing
  rw [G'.vertexOf_mem_internalVertices, G.vertexOf_mem_internalVertices, hbv, ← hmap, card_map]
  refine and_congr Iff.rfl (and_congr ⟨fun h p hp => ?_, fun h z hz => ?_⟩ Iff.rfl)
  · obtain ⟨z, hz, rfl⟩ := mem_map.1 hp
    rw [Embedding.coe_subtype, ← hcol]
    exact h z hz
  · rw [hcol]
    exact h _ (mem_map_of_mem _ hz)

/-! ### Chains under a first return -/

/-- **Chains under a first return.** Suppose that the trip map of `G'` is the first return to `Y`
of the trip map `T` of `G`, that initial darts of `G'` are initial in `G`, that a dart `y` of `Y`
is terminal in `G'` exactly when one of `y, T y, …` before its first return is terminal in `G`, and
that the first such dart then has the reverse of `y` in `G'` as its reverse. Then the chains of `G`
and `G'` from an initial dart of `G'` end at darts with the same reverse. -/
private theorem inv_chainEnd_eq_of_firstReturn (hG : G.IsPlabicGraph)
    (hG' : G'.IsPlabicGraph)
    (htrip : ∀ y : Y, (G'.tripMap y : H) = firstReturn hG.tripEquiv Y y)
    (hterm : ∀ y : Y, G'.IsTerminal y ↔
      ∃ j < firstReturnTime hG.tripEquiv Y y, G.IsTerminal ((hG.tripEquiv ^ j) y))
    (harr : ∀ y : Y, ∀ j < firstReturnTime hG.tripEquiv Y y,
      G.IsTerminal ((hG.tripEquiv ^ j) y) → (∀ i < j, ¬G.IsTerminal ((hG.tripEquiv ^ i) y)) →
        G.inv ((hG.tripEquiv ^ j) y) = G'.inv y)
    {c : Y} (hc : G'.IsInitial c) : G.inv (G.chainEnd c) = G'.inv (G'.chainEnd c) := by
  set T := hG.tripEquiv
  have hpow : ∀ (a b : ℕ) (x : H), (T ^ a) ((T ^ b) x) = (T ^ (b + a)) x := by
    intro a b x
    rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
  set m := G'.chainLength c
  have claim : ∀ i ≤ m, ∃ N, ((G'.tripMap^[i] c : Y) : H) = (T ^ N) c ∧
      ∀ n < N, ¬G.IsTerminal ((T ^ n) c) := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨0, rfl, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
    | succ i ih =>
      intro hi
      obtain ⟨N, hN, hnt⟩ := ih (by omega)
      have hy : ¬G'.IsTerminal (G'.tripMap^[i] c) := not_isTerminal_of_lt_chainLength (by omega)
      have hy' : ∀ j < firstReturnTime T Y (G'.tripMap^[i] c),
          ¬G.IsTerminal ((T ^ j) (G'.tripMap^[i] c : H)) :=
        fun j hj ht => hy ((hterm _).2 ⟨j, hj, ht⟩)
      refine ⟨N + firstReturnTime T Y (G'.tripMap^[i] c), ?_, fun n hn => ?_⟩
      · rw [Function.iterate_succ_apply', htrip, coe_firstReturn, hN, hpow]
      · by_cases hnN : n < N
        · exact hnt n hnN
        · obtain ⟨j, rfl⟩ : ∃ j, n = N + j := ⟨n - N, by omega⟩
          have := hy' j (by omega)
          rwa [hN, hpow] at this
  obtain ⟨N, hN, hnt⟩ := claim m le_rfl
  have hyN : (G'.chainEnd c : H) = (T ^ N) c := hN
  have hyt : G'.IsTerminal (G'.chainEnd c) := hc.isTerminal_chainEnd hG'
  classical
  have hex : ∃ j, j < firstReturnTime T Y (G'.chainEnd c) ∧
      G.IsTerminal ((T ^ j) (G'.chainEnd c : H)) := by
    obtain ⟨j, hj, ht⟩ := (hterm _).1 hyt
    exact ⟨j, hj, ht⟩
  obtain ⟨hj, ht⟩ := Nat.find_spec hex
  have hmin : ∀ i < Nat.find hex, ¬G.IsTerminal ((T ^ i) (G'.chainEnd c : H)) :=
    fun i hi hti => Nat.find_min hex hi ⟨by omega, hti⟩
  have hTj : (T ^ Nat.find hex) (G'.chainEnd c : H) = (T ^ (N + Nat.find hex)) c := by
    have := hpow (Nat.find hex) N c
    rwa [← hyN] at this
  have h1 : G.IsTerminal (G.tripMap^[N + Nat.find hex] c) := by
    rw [tripMap_iterate_eq hG, ← hTj]
    exact ht
  have hlen : G.chainLength c = N + Nat.find hex := by
    refine le_antisymm (chainLength_le h1) (not_lt.1 fun hlt => ?_)
    have h2 := chainLength_spec (G := G) ⟨_, h1⟩
    rw [tripMap_iterate_eq hG] at h2
    by_cases hL : G.chainLength c < N
    · exact hnt _ hL h2
    · obtain ⟨i, hi⟩ : ∃ i, G.chainLength c = N + i := ⟨_, (Nat.add_sub_cancel' (not_lt.1 hL)).symm⟩
      rw [hi] at h2 hlt
      apply hmin i (by omega)
      rwa [hyN, hpow]
  rw [chainEnd_def, hlen, tripMap_iterate_eq hG, ← hTj]
  exact harr _ _ hj ht hmin

/-- **Trips under a first return.** If the trip map of `G'` is the first return to `Y` of that of
`G`, every trip of `G` meets `Y`, and `G` and `G'` have the same boundary and the same initial
darts, all in `Y`, then every trip of `G` contains an initial dart exactly when every trip of `G'`
does. -/
private theorem exists_isInitial_mem_trip_iff_of_firstReturn (hG : G.IsPlabicGraph)
    (htrip : ∀ y : Y, (G'.tripMap y : H) = firstReturn hG.tripEquiv Y y)
    (hmeet : ∀ x : H, ∃ y ∈ Y, hG.tripEquiv.SameCycle x y)
    (hbdry : ∀ y : Y, y ∈ G'.bdry ↔ (y : H) ∈ G.bdry)
    (hinit : ∀ y : Y, G'.IsInitial y ↔ G.IsInitial y)
    (hinitY : ∀ p : H, G.IsInitial p → p ∈ Y) :
    (∀ d ∉ G.bdry, ∃ e ∈ G.trip d, G.IsInitial e) ↔
      ∀ d ∉ G'.bdry, ∃ e ∈ G'.trip d, G'.IsInitial e := by
  set T := hG.tripEquiv
  have hT' : ∀ y : Y, G'.tripMap y = firstReturnPerm T Y y := fun y =>
    Subtype.ext (by rw [htrip, coe_firstReturnPerm])
  have hiter : ∀ (n : ℕ) (y : Y), G'.tripMap^[n] y = (firstReturnPerm T Y ^ n) y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', ih, hT', pow_succ', Equiv.Perm.mul_apply]
  have hB : ∀ x y : H, T.SameCycle x y → (x ∈ G.bdry ↔ y ∈ G.bdry) := by
    intro x y h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, IsPlabicGraph.tripEquiv_apply,
        tripMap_mem_bdry_iff hG]
      exact ih (Equiv.Perm.sameCycle_pow_right.2 (.refl _ _))
  constructor
  · intro h d hd
    have hd' : (d : H) ∉ G.bdry := (hbdry d).not.1 hd
    obtain ⟨e, he, hei⟩ := h d hd'
    obtain ⟨n, hn⟩ := he
    simp only at hn
    have heY := hinitY _ hei
    have hs : (firstReturnPerm T Y).SameCycle d ⟨e, heY⟩ :=
      (sameCycle_firstReturnPerm_iff (π := T) (Y := Y)).2
        ⟨n, by rw [zpow_natCast, ← tripMap_iterate_eq hG, hn]⟩
    obtain ⟨k, hk⟩ := hs.exists_nat_pow_eq
    refine ⟨⟨e, heY⟩, ⟨k, ?_⟩, (hinit _).2 hei⟩
    change G'.tripMap^[k] d = _
    rw [hiter]
    exact hk
  · intro h d hd
    obtain ⟨y, hyY, hdy⟩ := hmeet d
    have hy : (⟨y, hyY⟩ : Y) ∉ G'.bdry := by
      rw [hbdry]
      exact fun h' => hd ((hB _ _ hdy).2 h')
    obtain ⟨e, he, hei⟩ := h _ hy
    obtain ⟨n, hn⟩ := he
    simp only at hn
    have hs : T.SameCycle y e := by
      rw [← hn, hiter]
      exact (sameCycle_firstReturnPerm_iff (π := T) (Y := Y) (y := ⟨y, hyY⟩)).1
        ⟨n, by rw [zpow_natCast]⟩
    obtain ⟨k, hk⟩ := (hdy.trans hs).exists_nat_pow_eq
    refine ⟨e, ⟨k, ?_⟩, (hinit _).1 hei⟩
    change G.tripMap^[k] d = _
    rw [tripMap_iterate_eq hG]
    exact hk

end Restrict

/-! ### Removing a bivalent vertex and contracting a black edge -/

section LocalMoves

/-- **Removing a bivalent vertex**. Let `G` be a plabic graph, `v` an internal vertex consisting of
exactly two darts `d₁ = d` and `d₂ = σ d₁` with `d̄₁ ≠ d₂`, and `G'` the removal of `v`. Then a
pre-triple diagram is a generalized triple diagram of `G` if and only if it is one of `G'`. (Being
a pre-triple diagram is part of both sides.) -/
@[cluster_algebras "lem_generalized_removal"]
theorem isGeneralizedTripleDiagram_bivalentRemoval_iff (hG : G.IsPlabicGraph) {d : H}
    (hd : G.IsBivalentRemovable d) {H'' : Type*} [Fintype H''] [DecidableEq H'']
    (X : TripleData H'' b) :
    G.IsGeneralizedTripleDiagram hG X ↔
      (G.bivalentRemoval hG hd).IsGeneralizedTripleDiagram (isPlabicGraph_bivalentRemoval hG hd)
        X := by
  set G' := G.bivalentRemoval hG hd
  have hG' : G'.IsPlabicGraph := isPlabicGraph_bivalentRemoval hG hd
  have hinv := hG.inv_involutive
  have hv2 : ¬G.IsCrossing (G.vertexOf d) := fun h => by
    have := h.three_le_card
    rw [hd.card_vertexOf] at this
    omega
  have R : IsRestriction G G' :=
    { mem_of_isCrossing := fun p hp => by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨fun h => hv2 (h ▸ hp), fun h => hv2 ?_⟩
        rw [← G.vertexOf_rot, ← h]
        exact hp
      isCrossing_iff := fun y => isCrossing_iff_of_map_vertexOf
        (map_bivalentRemoval_vertexOf hG hd y)
        (isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd y)
        fun z => bivalentRemoval_colour hG hd z
      rot_eq := fun y _ => coe_bivalentRemoval_rot hG hd y
      leg_eq := coe_bivalentRemoval_leg hG hd
      mem_bdry_iff := fun y => mem_bivalentRemoval_bdry hG hd }
  set T := hG.tripEquiv
  have hT : ∀ x : H, T x = G.turn (G.inv x) := fun _ => rfl
  have hnt1 : ¬G.IsTerminal (G.inv d) := by
    rintro ⟨-, h⟩
    rw [hinv] at h
    rcases h with h | h
    exacts [hv2 h, hd.not_isBoundaryVertex h]
  have hnt2 : ¬G.IsTerminal (G.inv (G.rot d)) := by
    rintro ⟨-, h⟩
    rw [hinv, G.vertexOf_rot] at h
    rcases h with h | h
    exacts [hv2 h, hd.not_isBoundaryVertex h]
  have hfrt2 : ∀ y : ({d, G.rot d}ᶜ : Set H), T y ∉ ({d, G.rot d}ᶜ : Set H) →
      (T ^ 2) (y : H) ∈ ({d, G.rot d}ᶜ : Set H) → firstReturnTime T _ y = 2 := by
    intro y h1 h2
    refine firstReturnTime_eq_iff.2 ⟨two_pos, h2, fun j hj hj2 => ?_⟩
    obtain rfl : j = 1 := by omega
    rwa [pow_one]
  have key : ∀ y : ({d, G.rot d}ᶜ : Set H),
      (firstReturnTime T _ y = 1 ∧ (G'.inv y : H) = G.inv y) ∨
      (firstReturnTime T _ y = 2 ∧ ¬G.IsTerminal y ∧ (G'.inv y : H) = G.inv (T y)) := by
    intro y
    by_cases h₁ : (y : H) = G.inv d
    · right
      have e1 : T y = G.rot d := by rw [hT, h₁, hinv, hd.turn_eq_rot]
      refine ⟨hfrt2 y (by rw [e1]; exact notMem_compl_pair_iff.2 (Or.inr rfl)) ?_, h₁ ▸ hnt1, ?_⟩
      · rw [pow_two, Equiv.Perm.mul_apply, e1, hT]
        exact hd.turn_mem (hd.inv_rot_mem hG)
      · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd h₁, e1]
    by_cases h₂ : (y : H) = G.inv (G.rot d)
    · right
      have e1 : T y = d := by rw [hT, h₂, hinv, hd.turn_rot]
      refine ⟨hfrt2 y (by rw [e1]; exact notMem_compl_pair_iff.2 (Or.inl rfl)) ?_, h₂ ▸ hnt2, ?_⟩
      · rw [pow_two, Equiv.Perm.mul_apply, e1, hT]
        exact hd.turn_mem (hd.inv_mem hG)
      · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂, e1]
    · left
      have hm : G.inv y ∈ ({d, G.rot d}ᶜ : Set H) := by
        have := (G'.inv y).2
        rwa [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂] at this
      refine ⟨firstReturnTime_eq_iff.2 ⟨one_pos, ?_, fun j hj hj1 => by omega⟩,
        coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂⟩
      rw [pow_one, hT]
      exact hd.turn_mem hm
  have hterm : ∀ y : ({d, G.rot d}ᶜ : Set H), G'.IsTerminal y ↔
      ∃ j < firstReturnTime T _ y, G.IsTerminal ((T ^ j) y) := by
    intro y
    rw [R.isTerminal_iff hG hG']
    rcases key y with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [h2, hinv, h1]
      exact ⟨fun h => ⟨0, one_pos, h⟩, fun ⟨j, hj, h⟩ => by
        obtain rfl : j = 0 := by omega
        exact h⟩
    · rw [h3, hinv, h1]
      refine ⟨fun h => ⟨1, by omega, by rwa [pow_one]⟩, fun ⟨j, hj, h⟩ => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain rfl : j = 0 := by omega
        exact absurd h h2
      · rwa [pow_one] at h
  have harr : ∀ y : ({d, G.rot d}ᶜ : Set H), ∀ j < firstReturnTime T _ y,
      G.IsTerminal ((T ^ j) y) → (∀ i < j, ¬G.IsTerminal ((T ^ i) y)) →
        G.inv ((T ^ j) y) = G'.inv y := by
    intro y j hj ht _
    rcases key y with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · obtain rfl : j = 0 := by omega
      rw [pow_zero, Equiv.Perm.one_apply, h2]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 (h1 ▸ hj) with hj' | rfl
      · obtain rfl : j = 0 := by omega
        exact absurd ht h2
      · rw [pow_one, h3]
  refine R.isGeneralizedTripleDiagram_iff hG hG'
    (fun c hc => inv_chainEnd_eq_of_firstReturn hG hG' (coe_bivalentRemoval_tripMap hG hd)
      hterm harr hc)
    (exists_isInitial_mem_trip_iff_of_firstReturn hG (coe_bivalentRemoval_tripMap hG hd)
      (exists_sameCycle_tripEquiv_mem_bivalentRemoval hG hd) R.mem_bdry_iff
      R.isInitial_iff fun p hp => R.mem_of_isInitial hp) X

/-- **Contracting a black edge**. Let `G` be a plabic graph, `{d, d̄}` an edge whose ends
`v(d) ≠ v(d̄)` are both black internal vertices, and `G'` the contraction along it. Then a
pre-triple diagram is a generalized triple diagram of `G` if and only if it is one of `G'`. (Being
a pre-triple diagram is part of both sides.) -/
@[cluster_algebras "lem_generalized_black_contraction"]
theorem isGeneralizedTripleDiagram_contractEdge_iff (hG : G.IsPlabicGraph) {d : H}
    (he : G.IsContractibleEdge d) (hb : G.colour d = .black) {H'' : Type*} [Fintype H'']
    [DecidableEq H''] (X : TripleData H'' b) :
    G.IsGeneralizedTripleDiagram hG X ↔
      (G.contractEdge d (he.leg_mem hG)).IsGeneralizedTripleDiagram (hG.contractEdge he) X := by
  set G' := G.contractEdge d (he.leg_mem hG)
  have hG' : G'.IsPlabicGraph := hG.contractEdge he
  have hinv := hG.inv_involutive
  have hblack : ∀ x : H, x ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) → G.colour x = .black :=
    fun x hx => (colour_eq_of_mem_union hG he hx).trans hb
  have hnc : ∀ x : H, x ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) → ¬G.IsCrossing (G.vertexOf x) := by
    intro x hx hc
    have := hc.2.1 x (G.self_mem_vertexOf x)
    rw [hblack x hx] at this
    exact Shade.noConfusion this
  have hd1 : d ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) := mem_union_left _ (G.self_mem_vertexOf d)
  have hd2 : G.inv d ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
    mem_union_right _ (G.self_mem_vertexOf _)
  have R : IsRestriction G G' :=
    { mem_of_isCrossing := fun p hp => by
        rw [mem_compl_pair_iff]
        exact ⟨fun h => hnc d hd1 (h ▸ hp), fun h => hnc _ hd2 (h ▸ hp)⟩
      isCrossing_iff := fun y => by
        by_cases hy : (y : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
        · refine iff_of_false (fun hc => ?_) (hnc y hy)
          have := hc.2.1 y (G'.self_mem_vertexOf y)
          rw [contractEdge_colour, hblack y hy] at this
          exact Shade.noConfusion this
        · exact isCrossing_iff_of_map_vertexOf
            (map_vertexOf_contractEdge_of_notMem he.not_sameCycle hy)
            (isBoundaryVertex_vertexOf_contractEdge_iff he) contractEdge_colour
      rot_eq := fun y hy => by
        have hy' : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := fun h => hnc y h hy
        exact coe_contractEdge_rot_of_mem (mem_compl_pair_of_notMem (rot_notMem_of_notMem hy'))
      leg_eq := coe_contractEdge_leg
      mem_bdry_iff := fun y => mem_contractEdge_bdry }
  set T := hG.tripEquiv
  have hnt : ∀ x : H, x ∉ (({d, G.inv d} : Set H)ᶜ : Set H) → ¬G.IsTerminal x := by
    rintro x hx ⟨-, h⟩
    have hx' : G.inv x ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
      rcases eq_or_eq_of_notMem_compl_pair hx with rfl | rfl
      · exact hd2
      · rw [hinv]; exact hd1
    rcases h with h | h
    · exact hnc _ hx' h
    · exact he.notMem_of_isBoundaryVertex h hx'
  have hinv' : ∀ y : (({d, G.inv d} : Set H)ᶜ : Set H), (G'.inv y : H) = G.inv y :=
    coe_contractEdge_inv hinv
  have hterm : ∀ y : (({d, G.inv d} : Set H)ᶜ : Set H), G'.IsTerminal y ↔
      ∃ j < firstReturnTime T _ y, G.IsTerminal ((T ^ j) y) := by
    intro y
    rw [R.isTerminal_iff hG hG', hinv', hinv]
    refine ⟨fun h => ⟨0, firstReturnTime_pos y, h⟩, fun ⟨j, hj, h⟩ => ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact h
    · exact absurd h (hnt _ (pow_apply_notMem_of_lt_firstReturnTime hj0 hj))
  have harr : ∀ y : (({d, G.inv d} : Set H)ᶜ : Set H), ∀ j < firstReturnTime T _ y,
      G.IsTerminal ((T ^ j) y) → (∀ i < j, ¬G.IsTerminal ((T ^ i) y)) →
        G.inv ((T ^ j) y) = G'.inv y := by
    intro y j hj ht _
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero, Equiv.Perm.one_apply, hinv']
    · exact absurd ht (hnt _ (pow_apply_notMem_of_lt_firstReturnTime hj0 hj))
  refine R.isGeneralizedTripleDiagram_iff hG hG'
    (fun c hc => inv_chainEnd_eq_of_firstReturn hG hG' (coe_contractEdge_tripMap hG he)
      hterm harr hc)
    (exists_isInitial_mem_trip_iff_of_firstReturn hG (coe_contractEdge_tripMap hG he)
      (exists_sameCycle_tripEquiv_mem hG he) R.mem_bdry_iff
      R.isInitial_iff fun p hp => R.mem_of_isInitial hp) X

end LocalMoves

/-! ### Chains and trivalent crossings -/

section Trivalent

/-- If `Tⁿ(d)` is terminal and no earlier `Tʲ(d)` is, the chain from `d` ends at `Tⁿ(d)`. -/
theorem chainEnd_eq_iterate {d : H} {n : ℕ} (hn : G.IsTerminal (G.tripMap^[n] d))
    (hmin : ∀ j < n, ¬G.IsTerminal (G.tripMap^[j] d)) : G.chainEnd d = G.tripMap^[n] d := by
  have : G.chainLength d = n :=
    le_antisymm (chainLength_le hn) (not_lt.1 fun h => hmin _ h (chainLength_spec ⟨n, hn⟩))
  rw [chainEnd_def, this]

/-- The chain from a dart `d` that is not terminal, with a terminal dart ahead of it, is the chain
from `T(d)`. -/
theorem chainEnd_tripMap {d : H} (hd : ¬G.IsTerminal d)
    (hex : ∃ m, G.IsTerminal (G.tripMap^[m] d)) :
    G.chainEnd (G.tripMap d) = G.chainEnd d := by
  have hspec := chainLength_spec hex
  have hL : G.chainLength d ≠ 0 := fun h => hd (by rw [h] at hspec; exact hspec)
  obtain ⟨L', hL'⟩ : ∃ L', G.chainLength d = L' + 1 := ⟨G.chainLength d - 1, by omega⟩
  have h1 : G.IsTerminal (G.tripMap^[L'] (G.tripMap d)) := by
    rw [← Function.iterate_succ_apply]
    rw [hL'] at hspec
    exact hspec
  rw [chainEnd_eq_iterate h1 fun j hj ht => not_isTerminal_of_lt_chainLength
    (show j + 1 < G.chainLength d by omega) (by rwa [Function.iterate_succ_apply]),
    chainEnd_def, hL', Function.iterate_succ_apply]

omit [Fintype H] in
/-- A corner triangulation of a set of three darts is empty. -/
private theorem isCornerTriangulation_eq_empty {w : Finset H} {E : Finset (Sym2 H)}
    (hE : G.IsCornerTriangulation w E) (h3 : w.card = 3) : E = ∅ := by
  obtain ⟨hEw, m, _, l, hl, hT⟩ := hE
  have hm : m = 3 := hl.card_eq.symm.trans h3
  rw [← hl.image_cornerPullback fun e he => (hEw e he).2,
    IsTriangulation.eq_empty_of_eq_three hm hT, image_empty]

/-- At a crossing with three darts, the only triangle of a white datum is the crossing itself, on
which the clockwise successor is `σ⁻¹`. -/
private theorem IsWhiteDatum.trivalent {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D)
    {p : H} (hc : G.IsCrossing (G.vertexOf p)) (h3 : (G.vertexOf p).card = 3) :
    G.IsDatumTriangle D (G.vertexOf p) ∧
      ∀ q ∈ G.vertexOf p, G.cornerNext (G.vertexOf p) q = G.rot.symm q := by
  obtain ⟨hτ, hs⟩ := hD.sideTriangle_spec hc
  have hp : p ∈ G.sideTriangle D p := mem_sym2_iff.1 hs p (Sym2.mem_mk_left _ _)
  obtain ⟨-, ht⟩ := hτ.vertexOf hp
  have he : G.sideTriangle D p = G.vertexOf p :=
    eq_of_subset_of_card_le ht.1 (by rw [h3, ht.2.1])
  rw [he] at hτ
  refine ⟨hτ, fun q hq => hD.cornerNext_eq_rot_symm hτ hq ?_⟩
  rw [← G.vertexOf_eq_of_mem hq]
  exact G.rot_symm_mem_vertexOf q

/-- The rotation of the strand diagram at a crossing with three darts:
`x⁺_q ↦ x⁻_{q̄} ↦ x⁺_{σ q}`. -/
private theorem strandRotSym_trivalent (hG : G.IsPlabicGraph) {D : Finset H → Finset (Sym2 H)}
    (hD : G.IsWhiteDatum D) {p : H} (hc : G.IsCrossing (G.vertexOf p))
    (h3 : (G.vertexOf p).card = 3) {q : H} (hq : q ∈ G.vertexOf p) :
    G.strandRotSym D (xPlus q) = xMinus (G.inv q) ∧
      G.strandRotSym D (xMinus (G.inv q)) = xPlus (G.rot q) := by
  obtain ⟨hτ, hcn⟩ := hD.trivalent hc h3
  have hvq : G.vertexOf q = G.vertexOf p := G.vertexOf_eq_of_mem hq
  have h3' : (G.vertexOf q).card = 3 := hvq ▸ h3
  have hq1 : G.rot.symm q ∈ G.vertexOf p := hvq ▸ G.rot_symm_mem_vertexOf q
  have hrq : G.rot q ∈ G.vertexOf p := hvq ▸ G.rot_mem_vertexOf q
  have hσ : G.rot.symm (G.rot.symm q) = G.rot q := by
    apply G.rot.injective
    apply G.rot.injective
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      rot_rot_rot_of_card_vertexOf_eq_three h3']
  have h1 : G.pairOut (G.vertexOf p) q = xPlus q := by rw [pairOut, if_pos (hcn q hq)]
  have h2 : G.pairIn (G.vertexOf p) q = xMinus (G.inv q) := by rw [pairIn, if_pos (hcn q hq)]
  have h4 : G.pairOut (G.vertexOf p) (G.rot q) = xPlus (G.rot q) := by
    rw [pairOut, if_pos (hcn _ hrq)]
  refine ⟨?_, ?_⟩
  · rw [← h1, ← h2, strandRotSym_pairOut hG hτ hq]
  · rw [← h2, strandRotSym_pairIn hG hD hτ hq, hcn q hq, hcn _ hq1, hσ, h4]

end Trivalent

/-! ### The corners of a square face -/

/-- Away from the corners, the square move does not change the crossings. -/
private theorem isCrossing_squareMove_iff {c x : H} (hx : G.vertexOf x ∉ G.squareVertices c) :
    (G.squareMove c).IsCrossing (G.vertexOf x) ↔ G.IsCrossing (G.vertexOf x) := by
  unfold IsCrossing
  rw [internalVertices_squareMove]
  refine and_congr Iff.rfl (and_congr ⟨fun h d hd => ?_, fun h d hd => ?_⟩ Iff.rfl)
  · have hd' : G.vertexOf d ∉ G.squareVertices c := by rwa [G.vertexOf_eq_of_mem hd]
    rw [← colour_squareMove_of_notMem G hd']
    exact h d hd
  · have hd' : G.vertexOf d ∉ G.squareVertices c := by rwa [G.vertexOf_eq_of_mem hd]
    rw [colour_squareMove_of_notMem G hd']
    exact h d hd

/-- Away from the corners, the square move does not change the initial darts. -/
private theorem isInitial_squareMove_iff {c x : H} (hx : G.vertexOf x ∉ G.squareVertices c) :
    (G.squareMove c).IsInitial x ↔ G.IsInitial x := by
  unfold IsInitial
  rw [vertexOf_squareMove, isCrossing_squareMove_iff hx]
  rfl

/-- Away from the corners, the square move does not change the terminal darts. -/
private theorem isTerminal_squareMove_iff {c t : H}
    (ht : G.vertexOf (G.inv t) ∉ G.squareVertices c) :
    (G.squareMove c).IsTerminal t ↔ G.IsTerminal t := by
  unfold IsTerminal
  rw [inv_squareMove, vertexOf_squareMove, isCrossing_squareMove_iff ht]
  rfl

namespace IsSquareMoveFace

variable {c : H} (hq : G.IsSquareMoveFace c) (hG : G.IsPlabicGraph)

include hq hG

omit hG in
/-- The darts of the corner `v(c_{k+1})`: `c̄_k`, `c_{k+1}` and `e_{k+1}`. -/
private theorem vertexOf_squareCorner_succ (k : Fin 4) :
    G.vertexOf (G.squareCorner c (k + 1)) =
      {G.inv (G.squareCorner c k), G.squareCorner c (k + 1), G.rot (G.squareCorner c (k + 1))} := by
  rw [vertexOf_eq_of_card_vertexOf_eq_three (hq.card_vertexOf _), hq.rot_rot_squareCorner]
  ext x
  simp only [mem_insert, mem_singleton]
  tauto

omit hG in
private theorem colour_of_mem_vertexOf_squareCorner (hG : G.IsPlabicGraph) (k : Fin 4) {x : H}
    (hx : x ∈ G.vertexOf (G.squareCorner c k)) : G.colour x = G.colour (G.squareCorner c k) :=
  colour_eq_of_sameCycle hG (hq.not_isBoundaryVertex k) ((RotationSystem.mem_vertexOf _).1 hx)

/-- A corner of the face is a crossing exactly when it is white. -/
private theorem isCrossing_vertexOf_squareCorner_iff (k : Fin 4) :
    G.IsCrossing (G.vertexOf (G.squareCorner c k)) ↔ G.colour (G.squareCorner c k) = .white := by
  refine ⟨fun h => h.2.1 _ (G.self_mem_vertexOf _), fun h => ⟨hq.vertexOf_mem_internalVertices k,
    fun x hx => (hq.colour_of_mem_vertexOf_squareCorner hG k hx).trans h, ?_⟩⟩
  rw [hq.card_vertexOf k]

/-- A dart at a corner is initial exactly when the corner is white. -/
private theorem isInitial_iff_of_mem (k : Fin 4) {x : H}
    (hx : x ∈ G.vertexOf (G.squareCorner c k)) :
    G.IsInitial x ↔ G.colour (G.squareCorner c k) = .white := by
  have hv : G.vertexOf x = G.vertexOf (G.squareCorner c k) := G.vertexOf_eq_of_mem hx
  have hb : ¬G.IsBoundaryVertex (G.vertexOf x) := hv ▸ hq.not_isBoundaryVertex k
  rw [← hq.isCrossing_vertexOf_squareCorner_iff hG k, ← hv]
  refine ⟨fun h => h.2.resolve_right fun hl => hb (hG.isBoundaryVertex_of_isLeg hl),
    fun h => ⟨notMem_bdry_of_mem_vertexOf hb (G.self_mem_vertexOf x), Or.inl h⟩⟩

/-- A dart running to a corner is terminal exactly when the corner is white. -/
private theorem isTerminal_iff_of_inv_mem (k : Fin 4) {t : H}
    (ht : G.inv t ∈ G.vertexOf (G.squareCorner c k)) :
    G.IsTerminal t ↔ G.colour (G.squareCorner c k) = .white := by
  have hv : G.vertexOf (G.inv t) = G.vertexOf (G.squareCorner c k) := G.vertexOf_eq_of_mem ht
  have hb : ¬G.IsBoundaryVertex (G.vertexOf (G.inv t)) := hv ▸ hq.not_isBoundaryVertex k
  rw [← hq.isCrossing_vertexOf_squareCorner_iff hG k, ← hv]
  refine ⟨fun h => h.2.resolve_right hb, fun h => ⟨fun htB => ?_, Or.inl h⟩⟩
  exact notMem_bdry_of_mem_vertexOf hb (G.self_mem_vertexOf _) (hG.inv_mem_bdry_iff.2 htB)

end IsSquareMoveFace

namespace IsSquareMoveFace

variable {c : H} (hq : G.IsSquareMoveFace c) (hG : G.IsPlabicGraph)

include hq hG

omit hG in
/-- The colours of the corners when `v(c₁)` is white. -/
private theorem colours_of_white (hc : G.colour c = .white) :
    G.colour (G.squareCorner c 0) = .white ∧ G.colour (G.squareCorner c 1) = .black ∧
      G.colour (G.squareCorner c 2) = .white ∧ G.colour (G.squareCorner c 3) = .black ∧
      (G.squareMove c).colour (G.squareCorner c 0) = .black ∧
      (G.squareMove c).colour (G.squareCorner c 1) = .white ∧
      (G.squareMove c).colour (G.squareCorner c 2) = .black ∧
      (G.squareMove c).colour (G.squareCorner c 3) = .white := by
  have h0 : G.colour (G.squareCorner c 0) = .white := by rwa [squareCorner_zero]
  have h1 : G.colour (G.squareCorner c 1) = .black := by
    have := hq.colour_squareCorner_add_one 0
    rwa [h0, zero_add] at this
  have h2 : G.colour (G.squareCorner c 2) = .white := by
    have := hq.colour_squareCorner_add_one 1
    rwa [h1] at this
  have h3 : G.colour (G.squareCorner c 3) = .black := by
    have := hq.colour_squareCorner_add_one 2
    rwa [h2] at this
  have hs : ∀ k, (G.squareMove c).colour (G.squareCorner c k) =
      (G.colour (G.squareCorner c k)).swap := fun k =>
    colour_squareMove_of_mem G (vertexOf_squareCorner_mem_squareVertices c k)
  refine ⟨h0, h1, h2, h3, ?_, ?_, ?_, ?_⟩
  · rw [hs, h0]; rfl
  · rw [hs, h1]; rfl
  · rw [hs, h2]; rfl
  · rw [hs, h3]; rfl

/-- **Chains through a square.** Let `v(c₁)` be white. For a dart `a` other than the darts `c_k`,
`c̄_k` of the edges of the face, the chains from `a` in `G` and in the square move `G₁` end at the
same dart, except when the path from `a` enters the square along some `ē_k`: then one of them ends
at `ē_k` and the other at `σ(e_k) = c̄_{k-1}`, the terminal dart of the corner where the trip of
the other graph turns. -/
private theorem rho_chainEnd_squareMove (hc : G.colour c = .white) {ρ : H → H}
    (hρ : ∀ x, G.vertexOf (G.inv x) ∉ G.squareVertices c → ρ x = x)
    (hρ0 : ρ (G.inv (G.squareCorner c 3)) = G.inv (G.rot (G.squareCorner c 0)))
    (hρ1 : ρ (G.inv (G.rot (G.squareCorner c 1))) = G.inv (G.squareCorner c 0))
    (hρ2 : ρ (G.inv (G.squareCorner c 1)) = G.inv (G.rot (G.squareCorner c 2)))
    (hρ3 : ρ (G.inv (G.rot (G.squareCorner c 3))) = G.inv (G.squareCorner c 2))
    {a : H} (ha : a ∉ G.squareEdgeDarts c) :
    ρ ((G.squareMove c).chainEnd a) = G.chainEnd a := by
  have hG₁ := hG.squareMove c
  have hq₁ := hq.squareMove
  have hinv := hG.inv_involutive
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := hq.colours_of_white hc
  set Z : Set H := {t | G.vertexOf (G.inv t) ∈ G.squareVertices c} with hZ
  have hT : ∀ x, x ∉ Z → (G.squareMove c).tripMap x = G.tripMap x :=
    fun x hx => turn_squareMove_of_notMem hx
  have hterm : ∀ t, t ∉ Z → ((G.squareMove c).IsTerminal t ↔ G.IsTerminal t) :=
    fun t ht => isTerminal_squareMove_iff ht
  have hTE : ∀ x, x ∉ Z → G.tripMap x ∉ G.squareEdgeDarts c := by
    intro x hx
    refine hq.notMem_squareEdgeDarts fun k hk => hx ?_
    rw [hZ, Set.mem_setOf_eq, ← vertexOf_turn, ← tripMap_apply, hk]
    exact vertexOf_squareCorner_mem_squareVertices c k
  have hZE : ∀ t, t ∈ Z → t ∉ G.squareEdgeDarts c →
      ∃ k, t = G.inv (G.rot (G.squareCorner c k)) := by
    intro t ht hE
    obtain ⟨k, hk⟩ := mem_squareVertices.1 ht
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp⟩
    have hm : G.inv t ∈ G.vertexOf (G.squareCorner c (j + 1)) := by
      rw [hk]
      exact G.self_mem_vertexOf _
    rw [hq.vertexOf_squareCorner_succ] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with h | h | h
    · exact absurd ⟨j, Or.inl (G.inv.injective h).symm⟩ hE
    · exact absurd ⟨j + 1, Or.inr (by rw [← h, hinv])⟩ hE
    · exact ⟨j + 1, by rw [← h, hinv]⟩
  have hnone : ∀ (G' : PlabicData H b) (d : H), (¬∃ m, G'.IsTerminal (G'.tripMap^[m] d)) →
      G'.chainEnd d = d := by
    intro G' d h
    rw [chainEnd_def, chainLength, dif_neg h]
    rfl
  by_cases hex : ∃ i, G.tripMap^[i] a ∈ Z ∨ G.IsTerminal (G.tripMap^[i] a)
  · classical
    have hmin : ∀ j < Nat.find hex, G.tripMap^[j] a ∉ Z ∧ ¬G.IsTerminal (G.tripMap^[j] a) :=
      fun j hj => not_or.1 (Nat.find_min hex hj)
    have hP₁ : ∀ j ≤ Nat.find hex, (G.squareMove c).tripMap^[j] a = G.tripMap^[j] a := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega),
          hT _ (hmin j (by omega)).1]
    have hmin₁ : ∀ j < Nat.find hex,
        ¬(G.squareMove c).IsTerminal ((G.squareMove c).tripMap^[j] a) := by
      intro j hj
      rw [hP₁ j hj.le, hterm _ (hmin j hj).1]
      exact (hmin j hj).2
    by_cases hz : G.tripMap^[Nat.find hex] a ∈ Z
    · have hE : G.tripMap^[Nat.find hex] a ∉ G.squareEdgeDarts c := by
        rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
        · rw [h0]
          exact ha
        · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
          rw [hj, Function.iterate_succ_apply']
          exact hTE _ (hmin j (by omega)).1
      obtain ⟨k, hk⟩ := hZE _ hz hE
      -- the darts of the four corners
      have hinvm : ∀ j, G.inv (G.inv (G.rot (G.squareCorner c j))) ∈
          G.vertexOf (G.squareCorner c j) := fun j => by
        rw [hinv]; exact G.rot_mem_vertexOf _
      have hinvc : ∀ j, G.inv (G.inv (G.squareCorner c j)) ∈
          G.vertexOf (G.squareCorner c j) := fun j => by
        rw [hinv]; exact G.self_mem_vertexOf _
      set n := Nat.find hex
      have hstepG : ∀ y, G.tripMap^[n] a = y → ¬G.IsTerminal y → G.IsTerminal (G.tripMap y) →
          G.chainEnd a = G.tripMap y := by
        intro y hy h1 h2
        rw [chainEnd_eq_iterate (n := n + 1) (by rwa [Function.iterate_succ_apply', hy])
          fun j hj => ?_, Function.iterate_succ_apply', hy]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact (hmin j hj).2
        · rwa [hy]
      have hstepG₁ : ∀ y, G.tripMap^[n] a = y → ¬(G.squareMove c).IsTerminal y →
          (G.squareMove c).IsTerminal ((G.squareMove c).tripMap y) →
          (G.squareMove c).chainEnd a = (G.squareMove c).tripMap y := by
        intro y hy h1 h2
        have hy₁ : (G.squareMove c).tripMap^[n] a = y := (hP₁ n le_rfl).trans hy
        rw [chainEnd_eq_iterate (n := n + 1) (by rwa [Function.iterate_succ_apply', hy₁])
          fun j hj => ?_, Function.iterate_succ_apply', hy₁]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact hmin₁ j hj
        · rwa [hy₁]
      have hendG : ∀ y, G.tripMap^[n] a = y → G.IsTerminal y → G.chainEnd a = y := by
        intro y hy h
        rw [chainEnd_eq_iterate (by rwa [hy]) fun j hj => (hmin j hj).2, hy]
      have hendG₁ : ∀ y, G.tripMap^[n] a = y → (G.squareMove c).IsTerminal y →
          (G.squareMove c).chainEnd a = y := by
        intro y hy h
        rw [chainEnd_eq_iterate (by rwa [hP₁ n le_rfl, hy]) hmin₁, hP₁ n le_rfl, hy]
      have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> simp
      rcases hk4 with rfl | rfl | rfl | rfl
      · -- `ē₁`, at the white corner `v(c₁)`
        have t1 : G.IsTerminal (G.inv (G.rot (G.squareCorner c 0))) :=
          (hq.isTerminal_iff_of_inv_mem hG 0 (hinvm 0)).2 c0
        have t2 : ¬(G.squareMove c).IsTerminal (G.inv (G.rot (G.squareCorner c 0))) := by
          intro h
          have := (hq₁.isTerminal_iff_of_inv_mem hG₁ 0 (hinvm 0)).1 h
          change (G.squareMove c).colour (G.squareCorner c 0) = .white at this
          rw [d0] at this
          exact Shade.noConfusion this
        have e3 : (G.squareMove c).tripMap (G.inv (G.rot (G.squareCorner c 0))) =
            G.inv (G.squareCorner c 3) := hq₁.tripMap_inv_rot_squareCorner_of_black hG₁ 3 d0
        have t3 : (G.squareMove c).IsTerminal (G.inv (G.squareCorner c 3)) :=
          (hq₁.isTerminal_iff_of_inv_mem hG₁ 3 (hinvc 3)).2 d3
        rw [hstepG₁ _ hk t2 (by rw [e3]; exact t3), e3, hρ0, hendG _ hk t1]
      · -- `ē₂`, at the black corner `v(c₂)`
        have t1 : ¬G.IsTerminal (G.inv (G.rot (G.squareCorner c 1))) := by
          intro h
          have := (hq.isTerminal_iff_of_inv_mem hG 1 (hinvm 1)).1 h
          rw [c1] at this
          exact Shade.noConfusion this
        have t2 : (G.squareMove c).IsTerminal (G.inv (G.rot (G.squareCorner c 1))) :=
          (hq₁.isTerminal_iff_of_inv_mem hG₁ 1 (hinvm 1)).2 d1
        have e3 : G.tripMap (G.inv (G.rot (G.squareCorner c 1))) = G.inv (G.squareCorner c 0) :=
          hq.tripMap_inv_rot_squareCorner_of_black hG 0 c1
        have t3 : G.IsTerminal (G.inv (G.squareCorner c 0)) :=
          (hq.isTerminal_iff_of_inv_mem hG 0 (hinvc 0)).2 c0
        rw [hendG₁ _ hk t2, hρ1, hstepG _ hk t1 (by rw [e3]; exact t3), e3]
      · -- `ē₃`, at the white corner `v(c₃)`
        have t1 : G.IsTerminal (G.inv (G.rot (G.squareCorner c 2))) :=
          (hq.isTerminal_iff_of_inv_mem hG 2 (hinvm 2)).2 c2
        have t2 : ¬(G.squareMove c).IsTerminal (G.inv (G.rot (G.squareCorner c 2))) := by
          intro h
          have := (hq₁.isTerminal_iff_of_inv_mem hG₁ 2 (hinvm 2)).1 h
          change (G.squareMove c).colour (G.squareCorner c 2) = .white at this
          rw [d2] at this
          exact Shade.noConfusion this
        have e3 : (G.squareMove c).tripMap (G.inv (G.rot (G.squareCorner c 2))) =
            G.inv (G.squareCorner c 1) := hq₁.tripMap_inv_rot_squareCorner_of_black hG₁ 1 d2
        have t3 : (G.squareMove c).IsTerminal (G.inv (G.squareCorner c 1)) :=
          (hq₁.isTerminal_iff_of_inv_mem hG₁ 1 (hinvc 1)).2 d1
        rw [hstepG₁ _ hk t2 (by rw [e3]; exact t3), e3, hρ2, hendG _ hk t1]
      · -- `ē₄`, at the black corner `v(c₄)`
        have t1 : ¬G.IsTerminal (G.inv (G.rot (G.squareCorner c 3))) := by
          intro h
          have := (hq.isTerminal_iff_of_inv_mem hG 3 (hinvm 3)).1 h
          rw [c3] at this
          exact Shade.noConfusion this
        have t2 : (G.squareMove c).IsTerminal (G.inv (G.rot (G.squareCorner c 3))) :=
          (hq₁.isTerminal_iff_of_inv_mem hG₁ 3 (hinvm 3)).2 d3
        have e3 : G.tripMap (G.inv (G.rot (G.squareCorner c 3))) = G.inv (G.squareCorner c 2) :=
          hq.tripMap_inv_rot_squareCorner_of_black hG 2 c3
        have t3 : G.IsTerminal (G.inv (G.squareCorner c 2)) :=
          (hq.isTerminal_iff_of_inv_mem hG 2 (hinvc 2)).2 c2
        rw [hendG₁ _ hk t2, hρ3, hstepG _ hk t1 (by rw [e3]; exact t3), e3]
    · have ht : G.IsTerminal (G.tripMap^[Nat.find hex] a) :=
        (Nat.find_spec hex).resolve_left hz
      rw [chainEnd_eq_iterate ht fun j hj => (hmin j hj).2,
        chainEnd_eq_iterate (by rwa [hP₁ _ le_rfl, hterm _ hz]) hmin₁, hP₁ _ le_rfl, hρ _ hz]
  · push Not at hex
    have hP₁ : ∀ j, (G.squareMove c).tripMap^[j] a = G.tripMap^[j] a := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hT _ (hex j).1]
    rw [hnone (G.squareMove c) a fun ⟨m, hm⟩ => (hex m).2 (by
        rwa [hP₁, hterm _ (hex m).1] at hm),
      hnone G a fun ⟨m, hm⟩ => (hex m).2 hm, hρ a (hex 0).1]

end IsSquareMoveFace

/-! ### The darts at the corners of a square face -/

/-- The dart `σ^i(c_{k+1})` at the corner `v(c_{k+1})` (`k : Fin 4`, `i : Fin 3`): `c_{k+1}`,
`e_{k+1}` and `c̄_k`. -/
private def squareDart (G : PlabicData H b) (c : H) (p : Fin 4 × Fin 3) : H :=
  (G.rot ^ (p.2 : ℕ)) (G.squareCorner c p.1)

/-- The exchange of the initial darts at the corners in a square move, on the indices of
`squareDart`: `c̄₁ ↔ e₁`, `c̄₃ ↔ e₃`, `e₂ ↔ c̄₂`, `e₄ ↔ c̄₄`, `c₂ ↔ c₃`, `c₄ ↔ c₁`. -/
private def squareIdxInit : Equiv.Perm (Fin 4 × Fin 3) :=
  Equiv.swap (1, 2) (0, 1) * Equiv.swap (3, 2) (2, 1) * Equiv.swap (1, 1) (2, 2) *
    Equiv.swap (3, 1) (0, 2) * Equiv.swap (1, 0) (2, 0) * Equiv.swap (3, 0) (0, 0)

/-- The exchange of the terminal darts at the corners in a square move, on the indices of the
reverses of `squareDart`: `c₁ ↔ c₂`, `c₃ ↔ c₄`, `c̄₂ ↔ ē₃`, `c̄₄ ↔ ē₁`, `ē₂ ↔ c̄₁`, `ē₄ ↔ c̄₃`. -/
private def squareIdxTerm : Equiv.Perm (Fin 4 × Fin 3) :=
  Equiv.swap (1, 2) (2, 2) * Equiv.swap (3, 2) (0, 2) * Equiv.swap (1, 0) (2, 1) *
    Equiv.swap (3, 0) (0, 1) * Equiv.swap (1, 1) (0, 0) * Equiv.swap (3, 1) (2, 0)

private theorem squareIdxInit_parity :
    ∀ p : Fin 4 × Fin 3, ((squareIdxInit p).1 : ℕ) % 2 ≠ (p.1 : ℕ) % 2 := by decide

private theorem squareIdxTerm_parity :
    ∀ p : Fin 4 × Fin 3, ((squareIdxTerm p).1 : ℕ) % 2 ≠ (p.1 : ℕ) % 2 := by decide

private theorem squareDart_mem (G : PlabicData H b) (c : H) (p : Fin 4 × Fin 3) :
    G.squareDart c p ∈ G.vertexOf (G.squareCorner c p.1) :=
  (RotationSystem.mem_vertexOf _).2 (Equiv.Perm.sameCycle_pow_right.2 (.refl _ _))

private theorem vertexOf_squareDart_mem (G : PlabicData H b) (c : H) (p : Fin 4 × Fin 3) :
    G.vertexOf (G.squareDart c p) ∈ G.squareVertices c := by
  rw [G.vertexOf_eq_of_mem (G.squareDart_mem c p)]
  exact vertexOf_squareCorner_mem_squareVertices c p.1

omit [Fintype H] [DecidableEq H] in
@[simp] private theorem squareDart_zero {c : H} (k : Fin 4) :
    G.squareDart c (k, 0) = G.squareCorner c k := by simp [squareDart]

omit [Fintype H] [DecidableEq H] in
@[simp] private theorem squareDart_one {c : H} (k : Fin 4) :
    G.squareDart c (k, 1) = G.rot (G.squareCorner c k) := by simp [squareDart]

namespace IsSquareMoveFace

variable {c : H} (hq : G.IsSquareMoveFace c)

include hq

private theorem rot_squareDart (p : Fin 4 × Fin 3) :
    G.rot (G.squareDart c p) = G.squareDart c (p.1, p.2 + 1) := by
  obtain ⟨k, i⟩ := p
  have h3 := rot_rot_rot_of_card_vertexOf_eq_three (hq.card_vertexOf k)
  simp only [squareDart]
  obtain ⟨i, hi⟩ := i
  interval_cases i
  · change G.rot ((G.rot ^ 0) _) = (G.rot ^ 1) _
    simp
  · change G.rot ((G.rot ^ 1) _) = (G.rot ^ 2) _
    simp [pow_two]
  · change G.rot ((G.rot ^ 2) _) = (G.rot ^ 0) _
    simp [pow_two, h3]

private theorem squareDart_injective : Function.Injective (G.squareDart c) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  have hv : G.vertexOf (G.squareCorner c k) = G.vertexOf (G.squareCorner c k') := by
    rw [← G.vertexOf_eq_of_mem (G.squareDart_mem c (k, i)), h,
      G.vertexOf_eq_of_mem (G.squareDart_mem c (k', i'))]
  obtain rfl := hq.injective hv
  obtain ⟨h1, h2⟩ := rot_ne_of_card_vertexOf_eq_three (hq.card_vertexOf k)
  have h3 := rot_rot_rot_of_card_vertexOf_eq_three (hq.card_vertexOf k)
  have h1' : G.rot (G.rot (G.squareCorner c k)) ≠ G.rot (G.squareCorner c k) :=
    fun e => h1 (G.rot.injective e)
  simp only [squareDart] at h
  obtain ⟨i, hi⟩ := i
  obtain ⟨i', hi'⟩ := i'
  interval_cases i <;> interval_cases i' <;>
    simp only [pow_zero, pow_one, pow_two, Equiv.Perm.one_apply,
      Equiv.Perm.mul_apply] at h <;>
    first
    | rfl
    | (exfalso
       first
       | exact h1 h | exact h1 h.symm | exact h2 h | exact h2 h.symm | exact h1' h
       | exact h1' h.symm)

/-- Every dart at a corner of the face is a `squareDart`. -/
private theorem exists_squareDart_eq {x : H} (hx : G.vertexOf x ∈ G.squareVertices c) :
    ∃ p, G.squareDart c p = x := by
  obtain ⟨k, hk⟩ := mem_squareVertices.1 hx
  have hm : x ∈ G.vertexOf (G.squareCorner c k) := by rw [hk]; exact G.self_mem_vertexOf x
  rw [vertexOf_eq_of_card_vertexOf_eq_three (hq.card_vertexOf k)] at hm
  simp only [mem_insert, mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · exact ⟨(k, 0), by simp [squareDart]⟩
  · exact ⟨(k, 1), by simp [squareDart]⟩
  · exact ⟨(k, 2), by simp [squareDart, pow_succ', Equiv.Perm.mul_apply]⟩

private theorem squareDart_two (k : Fin 4) :
    G.squareDart c (k + 1, 2) = G.inv (G.squareCorner c k) := by
  simp only [squareDart, Fin.isValue, Fin.val_two, pow_two, Equiv.Perm.mul_apply]
  exact hq.rot_rot_squareCorner k

end IsSquareMoveFace

namespace IsSquareMoveFace

variable {c : H} (hq : G.IsSquareMoveFace c)

include hq

private theorem squareDart_two' {j k : Fin 4} (h : j = k + 1) :
    G.squareDart c (j, 2) = G.inv (G.squareCorner c k) := by
  subst h
  exact hq.squareDart_two k

/-- The exchange of initial darts at the corners in a square move, as a permutation of the darts.
-/
private noncomputable def squareInit : Equiv.Perm H :=
  squareIdxInit.extendDomain (Equiv.ofInjective _ hq.squareDart_injective)

/-- The exchange of terminal darts at the corners in a square move, as a permutation of the
darts. -/
private noncomputable def squareTerm : Equiv.Perm H :=
  squareIdxTerm.extendDomain (Equiv.ofInjective (fun p => G.inv (G.squareDart c p))
    (G.inv.injective.comp hq.squareDart_injective))

private theorem squareInit_squareDart (p : Fin 4 × Fin 3) :
    hq.squareInit (G.squareDart c p) = G.squareDart c (squareIdxInit p) := by
  unfold squareInit
  simpa using Equiv.Perm.extendDomain_apply_image squareIdxInit
    (Equiv.ofInjective _ hq.squareDart_injective) p

private theorem squareTerm_inv_squareDart (p : Fin 4 × Fin 3) :
    hq.squareTerm (G.inv (G.squareDart c p)) = G.inv (G.squareDart c (squareIdxTerm p)) := by
  unfold squareTerm
  simpa using Equiv.Perm.extendDomain_apply_image squareIdxTerm
    (Equiv.ofInjective (fun p => G.inv (G.squareDart c p))
      (G.inv.injective.comp hq.squareDart_injective)) p

private theorem squareInit_of_notMem {x : H} (hx : G.vertexOf x ∉ G.squareVertices c) :
    hq.squareInit x = x := by
  apply Equiv.Perm.extendDomain_apply_not_subtype
  rintro ⟨p, rfl⟩
  exact hx (G.vertexOf_squareDart_mem c p)

private theorem squareTerm_of_notMem (hG : G.IsPlabicGraph) {t : H}
    (ht : G.vertexOf (G.inv t) ∉ G.squareVertices c) : hq.squareTerm t = t := by
  apply Equiv.Perm.extendDomain_apply_not_subtype
  rintro ⟨p, rfl⟩
  apply ht
  rw [hG.inv_involutive]
  exact G.vertexOf_squareDart_mem c p

variable (hG : G.IsPlabicGraph)

include hG

omit hG in
private theorem colour_squareCorner_of_white (hc : G.colour c = .white) (k : Fin 4) :
    G.colour (G.squareCorner c k) = (if (k : ℕ) % 2 = 0 then .white else .black) ∧
      (G.squareMove c).colour (G.squareCorner c k) =
        (if (k : ℕ) % 2 = 0 then .black else .white) := by
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := hq.colours_of_white hc
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by revert k; decide
  rcases hk with rfl | rfl | rfl | rfl <;> simp [-squareCorner_zero, c0, c1, c2, c3, d0, d1, d2, d3]

private theorem isInitial_squareDart_iff (hc : G.colour c = .white) (p : Fin 4 × Fin 3) :
    G.IsInitial (G.squareDart c p) ↔ (p.1 : ℕ) % 2 = 0 := by
  rw [hq.isInitial_iff_of_mem hG p.1 (G.squareDart_mem c p),
    (hq.colour_squareCorner_of_white hc p.1).1]
  split_ifs with h <;> simp [h]

private theorem isInitial_squareMove_squareDart_iff (hc : G.colour c = .white)
    (p : Fin 4 × Fin 3) :
    (G.squareMove c).IsInitial (G.squareDart c p) ↔ (p.1 : ℕ) % 2 ≠ 0 := by
  rw [hq.squareMove.isInitial_iff_of_mem (hG.squareMove c) p.1 (G.squareDart_mem c p)]
  change (G.squareMove c).colour (G.squareCorner c p.1) = .white ↔ _
  rw [(hq.colour_squareCorner_of_white hc p.1).2]
  split_ifs with h <;> simp [h]

private theorem isTerminal_inv_squareDart_iff (hc : G.colour c = .white) (p : Fin 4 × Fin 3) :
    G.IsTerminal (G.inv (G.squareDart c p)) ↔ (p.1 : ℕ) % 2 = 0 := by
  rw [hq.isTerminal_iff_of_inv_mem hG p.1 (by rw [hG.inv_involutive]; exact G.squareDart_mem c p),
    (hq.colour_squareCorner_of_white hc p.1).1]
  split_ifs with h <;> simp [h]

private theorem isTerminal_squareMove_inv_squareDart_iff (hc : G.colour c = .white)
    (p : Fin 4 × Fin 3) :
    (G.squareMove c).IsTerminal (G.inv (G.squareDart c p)) ↔ (p.1 : ℕ) % 2 ≠ 0 := by
  rw [hq.squareMove.isTerminal_iff_of_inv_mem (hG.squareMove c) p.1
    (by change G.inv (G.inv _) ∈ _; rw [hG.inv_involutive]; exact G.squareDart_mem c p)]
  change (G.squareMove c).colour (G.squareCorner c p.1) = .white ↔ _
  rw [(hq.colour_squareCorner_of_white hc p.1).2]
  split_ifs with h <;> simp [h]

/-- The initial darts of the square move correspond to those of `G` under `squareInit`. -/
private theorem isInitial_squareMove_iff_squareInit (hc : G.colour c = .white) (d : H) :
    (G.squareMove c).IsInitial d ↔ G.IsInitial (hq.squareInit d) := by
  by_cases hd : G.vertexOf d ∈ G.squareVertices c
  · obtain ⟨p, rfl⟩ := hq.exists_squareDart_eq hd
    rw [hq.squareInit_squareDart, hq.isInitial_squareMove_squareDart_iff hG hc,
      hq.isInitial_squareDart_iff hG hc]
    have := squareIdxInit_parity p
    constructor <;> intro <;> omega
  · rw [hq.squareInit_of_notMem hd, isInitial_squareMove_iff hd]

/-- The terminal darts of the square move correspond to those of `G` under `squareTerm`. -/
private theorem isTerminal_squareMove_iff_squareTerm (hc : G.colour c = .white) (t : H) :
    (G.squareMove c).IsTerminal t ↔ G.IsTerminal (hq.squareTerm t) := by
  by_cases ht : G.vertexOf (G.inv t) ∈ G.squareVertices c
  · obtain ⟨p, hp⟩ := hq.exists_squareDart_eq ht
    have e : t = G.inv (G.squareDart c p) := by rw [hp, hG.inv_involutive]
    rw [e, hq.squareTerm_inv_squareDart, hq.isTerminal_squareMove_inv_squareDart_iff hG hc,
      hq.isTerminal_inv_squareDart_iff hG hc]
    have := squareIdxTerm_parity p
    constructor <;> intro <;> omega
  · rw [hq.squareTerm_of_notMem hG ht, isTerminal_squareMove_iff ht]

end IsSquareMoveFace

/-- A crossing with three darts has the empty corner triangulation. -/
private theorem isCornerTriangulation_empty_of_card {R : RotationSystem H} {x : H}
    (h3 : (R.vertexOf x).card = 3) : R.IsCornerTriangulation (R.vertexOf x) ∅ := by
  refine ⟨by simp, 3, inferInstance, _, RotationSystem.isCornerLabelling_rot_symm_pow x h3, ?_⟩
  have : RotationSystem.cornerPullback (fun i : ZMod 3 => (R.rot.symm ^ i.val) x)
      (∅ : Finset (Sym2 H)) = ∅ := by
    ext e
    simp [RotationSystem.mem_cornerPullback]
  rw [this]
  exact isTriangulation_empty_three

/-- The white datum of a square move: empty at the corners, `D` elsewhere. -/
private def squareDatum (G : PlabicData H b) (c : H) (D : Finset H → Finset (Sym2 H)) :
    Finset H → Finset (Sym2 H) :=
  fun x => if x ∈ G.squareVertices c then ∅ else D x

namespace IsSquareMoveFace

variable {c : H} (hq : G.IsSquareMoveFace c) (hG : G.IsPlabicGraph)
  {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D)

include hq hG hD

omit hG in
private theorem isWhiteDatum_squareDatum : (G.squareMove c).IsWhiteDatum (G.squareDatum c D) := by
  intro x hx
  obtain ⟨y, rfl⟩ := (G.squareMove c).mem_vertices.1
    ((G.squareMove c).mem_internalVertices.1 hx.1).1
  change G.IsCornerTriangulation (G.vertexOf y) (G.squareDatum c D (G.vertexOf y))
  by_cases h : G.vertexOf y ∈ G.squareVertices c
  · rw [squareDatum, if_pos h]
    obtain ⟨k, hk⟩ := mem_squareVertices.1 h
    exact isCornerTriangulation_empty_of_card (by rw [← hk]; exact hq.card_vertexOf k)
  · rw [squareDatum, if_neg h]
    exact hD _ ((isCrossing_squareMove_iff h).1 hx)

omit hG in
/-- The pairs `(e, τ)` of the symbols `y^±` are the same for `G` and its square move. -/
private theorem isDatumSegment_squareDatum_iff {e : Sym2 H} {τ : Finset H} :
    (G.squareMove c).IsDatumSegment (G.squareDatum c D) e τ ↔ G.IsDatumSegment D e τ := by
  constructor
  · rintro ⟨x, hx, he, ht, hm⟩
    obtain ⟨y, rfl⟩ := (G.squareMove c).mem_vertices.1
      ((G.squareMove c).mem_internalVertices.1 hx.1).1
    by_cases h : G.vertexOf y ∈ G.squareVertices c
    · change e ∈ G.squareDatum c D (G.vertexOf y) at he
      rw [squareDatum, if_pos h] at he
      simp at he
    · change e ∈ G.squareDatum c D (G.vertexOf y) at he
      change G.IsCornerTriangle (G.vertexOf y) (G.squareDatum c D (G.vertexOf y)) τ at ht
      rw [squareDatum, if_neg h] at he ht
      exact ⟨G.vertexOf y, (isCrossing_squareMove_iff h).1 hx, he, ht, hm⟩
  · rintro ⟨x, hx, he, ht, hm⟩
    obtain ⟨y, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hx.1).1
    by_cases h : G.vertexOf y ∈ G.squareVertices c
    · exfalso
      obtain ⟨k, hk⟩ := mem_squareVertices.1 h
      have h3 : (G.vertexOf y).card = 3 := by rw [← hk]; exact hq.card_vertexOf k
      rw [isCornerTriangulation_eq_empty (hD _ hx) h3] at he
      simp at he
    · refine ⟨G.vertexOf y, (isCrossing_squareMove_iff h).2 hx, ?_, ?_, hm⟩
      · rw [squareDatum, if_neg h]
        exact he
      · change G.IsCornerTriangle (G.vertexOf y) (G.squareDatum c D (G.vertexOf y)) τ
        rw [squareDatum, if_neg h]
        exact ht

omit hG hD in
/-- A triangle of the white datum of the square move is a whole black corner of `G` or a triangle
of `D` away from the corners. -/
private theorem isDatumTriangle_squareDatum {τ : Finset H}
    (hτ : (G.squareMove c).IsDatumTriangle (G.squareDatum c D) τ) :
    (∃ k : Fin 4, τ = G.vertexOf (G.squareCorner c k) ∧
        (G.squareMove c).colour (G.squareCorner c k) = .white) ∨
      (G.IsDatumTriangle D τ ∧ ∀ q ∈ τ, G.vertexOf q ∉ G.squareVertices c) := by
  obtain ⟨x, hx, ht⟩ := hτ
  obtain ⟨y, rfl⟩ := (G.squareMove c).mem_vertices.1
    ((G.squareMove c).mem_internalVertices.1 hx.1).1
  change G.IsCornerTriangle (G.vertexOf y) (G.squareDatum c D (G.vertexOf y)) τ at ht
  by_cases h : G.vertexOf y ∈ G.squareVertices c
  · obtain ⟨k, hk⟩ := mem_squareVertices.1 h
    left
    refine ⟨k, ?_, ?_⟩
    · rw [hk]
      exact eq_of_subset_of_card_le ht.1 (by rw [← hk, hq.card_vertexOf k, ht.2.1])
    · exact hx.2.1 (G.squareCorner c k) (by
        change G.squareCorner c k ∈ G.vertexOf y
        rw [← hk]; exact G.self_mem_vertexOf _)
  · right
    rw [squareDatum, if_neg h] at ht
    refine ⟨⟨G.vertexOf y, (isCrossing_squareMove_iff h).1 hx, ht⟩, fun q hq' => ?_⟩
    rwa [G.vertexOf_eq_of_mem (ht.1 hq')]

end IsSquareMoveFace

/-- An internal face of two darts at distinct vertices exchanged by the face permutation is a
digon. -/
private theorem isDigon_of_facePerm {α : Type*} [Fintype α] [DecidableEq α] {X : TripleData α b}
    {d₁ d₂ : α} (h₁ : X.facePerm d₁ = d₂) (h₂ : X.facePerm d₂ = d₁) (hB₁ : d₁ ∉ X.bdry)
    (hB₂ : d₂ ∉ X.bdry) (hv : X.vertexOf d₁ ≠ X.vertexOf d₂) :
    X.faceOf d₁ = {d₁, d₂} ∧ X.IsDigon {d₁, d₂} := by
  have hface : X.faceOf d₁ = {d₁, d₂} := by
    refine filter_sameCycle_eq (by simp) ?_ ?_
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy ⊢
      rcases hy with rfl | rfl
      · exact Or.inr h₁
      · exact Or.inl h₂
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Equiv.Perm.SameCycle.refl _ _
      · exact sameCycle_of_apply_eq h₁
  refine ⟨hface, ?_, d₁, by rw [h₁], by rwa [h₁]⟩
  rw [DiskMap.mem_internalFaces, DiskMap.mem_faces]
  refine ⟨⟨fun he => ?_, hface ▸ X.faceOf_mem_faceOrbits d₁⟩, ?_⟩
  · have : d₁ ∈ X.exterior := he ▸ (by simp)
    exact hB₁ (X.exterior_subset_bdry this)
  · rw [disjoint_left]
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    exacts [hB₁, hB₂]

namespace IsSquareMoveFace

variable {c : H} (hq : G.IsSquareMoveFace c) (hG : G.IsPlabicGraph)

include hq hG

omit hG in
private theorem inv_squareCorner_mem (k : Fin 4) :
    G.inv (G.squareCorner c k) ∈ G.vertexOf (G.squareCorner c (k + 1)) := by
  rw [← hq.vertexOf_inv_squareCorner]
  exact G.self_mem_vertexOf _

/-- **Every trip of the square move meets an initial dart**, when every trip of `G` does. -/
private theorem exists_isInitial_mem_trip_squareMove (hc : G.colour c = .white)
    (horb : ∀ d ∉ G.bdry, ∃ e ∈ G.trip d, G.IsInitial e) :
    ∀ d ∉ (G.squareMove c).bdry, ∃ e ∈ (G.squareMove c).trip d, (G.squareMove c).IsInitial e := by
  have hG₁ := hG.squareMove c
  have hq₁ := hq.squareMove
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := hq.colours_of_white hc
  set T := hG.tripEquiv
  set T₁ := hG₁.tripEquiv
  have hfr := hq.firstReturnPerm_tripEquiv_squareMove hG
  have hsame : ∀ y z : H, y ∈ (G.squareEdgeDarts c)ᶜ → z ∈ (G.squareEdgeDarts c)ᶜ →
      T.SameCycle y z → T₁.SameCycle y z := by
    intro y z hy hz h
    have h' : (firstReturnPerm T (G.squareEdgeDarts c)ᶜ).SameCycle ⟨y, hy⟩ ⟨z, hz⟩ :=
      (sameCycle_firstReturnPerm_iff (π := T) (Y := (G.squareEdgeDarts c)ᶜ)).2 h
    rw [← hfr] at h'
    exact (sameCycle_firstReturnPerm_iff (π := T₁) (Y := (G.squareEdgeDarts c)ᶜ)).1 h'
  have hfwd : ∀ x z : H, T₁.SameCycle x z → z ∈ (G.squareMove c).trip x := by
    intro x z h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    change (G.squareMove c).tripMap^[n] x = z
    rw [← hG₁.tripEquiv_pow_apply]
    exact hn
  have hback : ∀ x e : H, e ∈ G.trip x → T.SameCycle x e := by
    rintro x e ⟨n, rfl⟩
    exact ⟨n, by rw [zpow_natCast, hG.tripEquiv_pow_apply]⟩
  have hB : ∀ x y : H, T₁.SameCycle x y →
      (x ∈ (G.squareMove c).bdry ↔ y ∈ (G.squareMove c).bdry) := by
    intro x y h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, IsPlabicGraph.tripEquiv_apply,
        tripMap_mem_bdry_iff hG₁]
      exact ih (Equiv.Perm.sameCycle_pow_right.2 (.refl _ _))
  have hstep : ∀ x y : H, G.tripMap x = y → T.SameCycle x y := fun x y h =>
    sameCycle_of_apply_eq h
  have hE : ∀ k, G.rot (G.squareCorner c k) ∈ (G.squareEdgeDarts c)ᶜ :=
    hq.rot_squareCorner_notMem
  have hI0 : T₁.SameCycle (G.rot (G.squareCorner c 0)) (G.inv (G.squareCorner c 0)) :=
    (sameCycle_of_apply_eq (hq₁.tripMap_inv_squareCorner_of_black hG₁ 0 d0)).symm
  have hI2 : T₁.SameCycle (G.rot (G.squareCorner c 2)) (G.inv (G.squareCorner c 2)) :=
    (sameCycle_of_apply_eq (hq₁.tripMap_inv_squareCorner_of_black hG₁ 2 d2)).symm
  have iI0 : (G.squareMove c).IsInitial (G.inv (G.squareCorner c 0)) :=
    (hq₁.isInitial_iff_of_mem hG₁ 1 (hq.inv_squareCorner_mem 0)).2 d1
  have iI2 : (G.squareMove c).IsInitial (G.inv (G.squareCorner c 2)) :=
    (hq₁.isInitial_iff_of_mem hG₁ 3 (hq.inv_squareCorner_mem 2)).2 d3
  have iE1 : (G.squareMove c).IsInitial (G.rot (G.squareCorner c 1)) :=
    (hq₁.isInitial_iff_of_mem hG₁ 1 (G.rot_mem_vertexOf _)).2 d1
  have iE3 : (G.squareMove c).IsInitial (G.rot (G.squareCorner c 3)) :=
    (hq₁.isInitial_iff_of_mem hG₁ 3 (G.rot_mem_vertexOf _)).2 d3
  intro d hd
  obtain ⟨y, hyY, hdy⟩ := hq₁.exists_sameCycle_notMem_squareEdgeDarts hG₁ d
  have hyB : y ∉ G.bdry := fun h => hd ((hB d y hdy).2 h)
  obtain ⟨e, he, hei⟩ := horb y hyB
  have hye := hback y e he
  suffices h : ∃ z ∈ (G.squareEdgeDarts c)ᶜ, T.SameCycle y z ∧
      ∃ w, (G.squareMove c).IsInitial w ∧ T₁.SameCycle z w by
    obtain ⟨z, hzY, hyz, w, hw, hzw⟩ := h
    exact ⟨w, hfwd d w (hdy.trans ((hsame y z hyY hzY hyz).trans hzw)), hw⟩
  by_cases hev : G.vertexOf e ∈ G.squareVertices c
  · obtain ⟨⟨k, i⟩, rfl⟩ := hq.exists_squareDart_eq hev
    have hk := (hq.isInitial_squareDart_iff hG hc (k, i)).1 hei
    have hk' : k = 0 ∨ k = 2 :=
      (by decide : ∀ k : Fin 4, (k : ℕ) % 2 = 0 → k = 0 ∨ k = 2) k hk
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i
    rcases hk' with rfl | rfl <;> rcases hi with rfl | rfl | rfl
    · rw [squareDart_zero] at hye
      refine ⟨_, hE 2, hye.trans ((hstep _ _ (hq.tripMap_squareCorner_of_black hG 0 c1)).trans
        (hstep _ _ (hq.tripMap_squareCorner_of_white hG 1 c2))), _, iI2, hI2⟩
    · rw [squareDart_one] at hye
      exact ⟨_, hE 0, hye, _, iI0, hI0⟩
    · rw [hq.squareDart_two' (j := 0) (k := 3) rfl] at hye
      exact ⟨_, hE 3, hye.trans (hstep _ _ (hq.tripMap_inv_squareCorner_of_black hG 3 c3)), _,
        iE3, .refl _ _⟩
    · rw [squareDart_zero] at hye
      have e2 : G.tripMap (G.squareCorner c 3) = G.rot (G.squareCorner c 0) :=
        hq.tripMap_squareCorner_of_white hG 3 c0
      refine ⟨_, hE 0, hye.trans ((hstep _ _ (hq.tripMap_squareCorner_of_black hG 2 c3)).trans
        (hstep _ _ e2)), _, iI0, hI0⟩
    · rw [squareDart_one] at hye
      exact ⟨_, hE 2, hye, _, iI2, hI2⟩
    · rw [hq.squareDart_two' (j := 2) (k := 1) rfl] at hye
      exact ⟨_, hE 1, hye.trans (hstep _ _ (hq.tripMap_inv_squareCorner_of_black hG 1 c1)), _,
        iE1, .refl _ _⟩
  · refine ⟨e, ?_, hye, e, (isInitial_squareMove_iff hev).2 hei, .refl _ _⟩
    exact hq.notMem_squareEdgeDarts fun k hk =>
      hev (hk ▸ vertexOf_squareCorner_mem_squareVertices c k)

/-- **Chains under a square move**: `squareTerm` sends the end of the chain of the square move from
an initial dart `d` to the end of the chain of `G` from `squareInit d`. -/
private theorem squareTerm_chainEnd (hc : G.colour c = .white) {d : H}
    (hd : (G.squareMove c).IsInitial d) :
    hq.squareTerm ((G.squareMove c).chainEnd d) = G.chainEnd (hq.squareInit d) := by
  have hG₁ := hG.squareMove c
  have hq₁ := hq.squareMove
  have hinv := hG.inv_involutive
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := hq.colours_of_white hc
  have tv := hq.squareTerm_inv_squareDart
  have hρ0 : hq.squareTerm (G.inv (G.squareCorner c 3)) = G.inv (G.rot (G.squareCorner c 0)) := by
    have := tv (3, 0)
    rwa [squareDart_zero, show squareIdxTerm (3, 0) = (0, 1) by decide,
      squareDart_one] at this
  have hρ1 : hq.squareTerm (G.inv (G.rot (G.squareCorner c 1))) = G.inv (G.squareCorner c 0) := by
    have := tv (1, 1)
    rwa [squareDart_one, show squareIdxTerm (1, 1) = (0, 0) by decide,
      squareDart_zero] at this
  have hρ2 : hq.squareTerm (G.inv (G.squareCorner c 1)) = G.inv (G.rot (G.squareCorner c 2)) := by
    have := tv (1, 0)
    rwa [squareDart_zero, show squareIdxTerm (1, 0) = (2, 1) by decide,
      squareDart_one] at this
  have hρ3 : hq.squareTerm (G.inv (G.rot (G.squareCorner c 3))) = G.inv (G.squareCorner c 2) := by
    have := tv (3, 1)
    rwa [squareDart_one, show squareIdxTerm (3, 1) = (2, 0) by decide,
      squareDart_zero] at this
  have chain : ∀ {a : H}, a ∉ G.squareEdgeDarts c →
      hq.squareTerm ((G.squareMove c).chainEnd a) = G.chainEnd a := fun ha =>
    hq.rho_chainEnd_squareMove hG hc (fun x hx => hq.squareTerm_of_notMem hG hx) hρ0 hρ1 hρ2 hρ3
      ha
  -- the trip maps and the statuses at the corners
  have nb : ¬(Shade.black = Shade.white) := nofun
  have TC0 : G.tripMap (G.squareCorner c 0) = G.squareCorner c 1 :=
    hq.tripMap_squareCorner_of_black hG 0 c1
  have TC2 : G.tripMap (G.squareCorner c 2) = G.squareCorner c 3 :=
    hq.tripMap_squareCorner_of_black hG 2 c3
  have TI1 : G.tripMap (G.inv (G.squareCorner c 1)) = G.rot (G.squareCorner c 1) :=
    hq.tripMap_inv_squareCorner_of_black hG 1 c1
  have TI3 : G.tripMap (G.inv (G.squareCorner c 3)) = G.rot (G.squareCorner c 3) :=
    hq.tripMap_inv_squareCorner_of_black hG 3 c3
  have T₁C1 : (G.squareMove c).tripMap (G.squareCorner c 1) = G.squareCorner c 2 :=
    hq₁.tripMap_squareCorner_of_black hG₁ 1 d2
  have T₁C3 : (G.squareMove c).tripMap (G.squareCorner c 3) = G.squareCorner c 0 :=
    hq₁.tripMap_squareCorner_of_black hG₁ 3 d0
  have T₁I0 : (G.squareMove c).tripMap (G.inv (G.squareCorner c 0)) = G.rot (G.squareCorner c 0) :=
    hq₁.tripMap_inv_squareCorner_of_black hG₁ 0 d0
  have T₁I2 : (G.squareMove c).tripMap (G.inv (G.squareCorner c 2)) = G.rot (G.squareCorner c 2) :=
    hq₁.tripMap_inv_squareCorner_of_black hG₁ 2 d2
  have tC : ∀ k j : Fin 4, j = k + 1 → (G.IsTerminal (G.squareCorner c k) ↔
      G.colour (G.squareCorner c j) = .white) := by
    intro k j h
    subst h
    exact hq.isTerminal_iff_of_inv_mem hG (k + 1) (hq.inv_squareCorner_mem k)
  have tC₁ : ∀ k j : Fin 4, j = k + 1 → ((G.squareMove c).IsTerminal (G.squareCorner c k) ↔
      (G.squareMove c).colour (G.squareCorner c j) = .white) := by
    intro k j h
    subst h
    exact hq₁.isTerminal_iff_of_inv_mem hG₁ (k + 1) (hq.inv_squareCorner_mem k)
  have tI : ∀ k : Fin 4, G.IsTerminal (G.inv (G.squareCorner c k)) ↔
      G.colour (G.squareCorner c k) = .white := fun k =>
    hq.isTerminal_iff_of_inv_mem hG k (by rw [hinv]; exact G.self_mem_vertexOf _)
  have tI₁ : ∀ k : Fin 4, (G.squareMove c).IsTerminal (G.inv (G.squareCorner c k)) ↔
      (G.squareMove c).colour (G.squareCorner c k) = .white := fun k =>
    hq₁.isTerminal_iff_of_inv_mem hG₁ k (by
      change G.inv (G.inv _) ∈ _; rw [hinv]; exact G.self_mem_vertexOf _)
  have nC0 : ¬G.IsTerminal (G.squareCorner c 0) := by rw [tC 0 1 rfl, c1]; exact nb
  have tC1 : G.IsTerminal (G.squareCorner c 1) := (tC 1 2 rfl).2 c2
  have nC2 : ¬G.IsTerminal (G.squareCorner c 2) := by rw [tC 2 3 rfl, c3]; exact nb
  have tC3 : G.IsTerminal (G.squareCorner c 3) := (tC 3 0 rfl).2 c0
  have tC₁0 : (G.squareMove c).IsTerminal (G.squareCorner c 0) := (tC₁ 0 1 rfl).2 d1
  have nC₁1 : ¬(G.squareMove c).IsTerminal (G.squareCorner c 1) := by
    rw [tC₁ 1 2 rfl, d2]; exact nb
  have tC₁2 : (G.squareMove c).IsTerminal (G.squareCorner c 2) := (tC₁ 2 3 rfl).2 d3
  have nC₁3 : ¬(G.squareMove c).IsTerminal (G.squareCorner c 3) := by
    rw [tC₁ 3 0 rfl, d0]; exact nb
  have nI1 : ¬G.IsTerminal (G.inv (G.squareCorner c 1)) := by rw [tI 1, c1]; exact nb
  have nI3 : ¬G.IsTerminal (G.inv (G.squareCorner c 3)) := by rw [tI 3, c3]; exact nb
  have nI₁0 : ¬(G.squareMove c).IsTerminal (G.inv (G.squareCorner c 0)) := by
    rw [tI₁ 0, d0]; exact nb
  have nI₁2 : ¬(G.squareMove c).IsTerminal (G.inv (G.squareCorner c 2)) := by
    rw [tI₁ 2, d2]; exact nb
  have iI1 : G.IsInitial (G.inv (G.squareCorner c 1)) :=
    (hq.isInitial_iff_of_mem hG 2 (hq.inv_squareCorner_mem 1)).2 c2
  have iI3 : G.IsInitial (G.inv (G.squareCorner c 3)) :=
    (hq.isInitial_iff_of_mem hG 0 (hq.inv_squareCorner_mem 3)).2 c0
  by_cases hdv : G.vertexOf d ∈ G.squareVertices c
  · obtain ⟨⟨k, i⟩, rfl⟩ := hq.exists_squareDart_eq hdv
    have hk := (hq.isInitial_squareMove_squareDart_iff hG hc (k, i)).1 hd
    have hk' : k = 1 ∨ k = 3 :=
      (by decide : ∀ k : Fin 4, (k : ℕ) % 2 ≠ 0 → k = 1 ∨ k = 3) k hk
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i
    have hex := hd.exists_isTerminal hG₁
    rw [hq.squareInit_squareDart]
    rcases hk' with rfl | rfl <;> rcases hi with rfl | rfl | rfl
    · -- `c₂ ↦ c₃`
      rw [show squareIdxInit (1, 0) = (2, 0) by decide, squareDart_zero, squareDart_zero,
        chainEnd_eq_tripMap (G := G.squareMove c) nC₁1 (by rw [T₁C1]; exact tC₁2), T₁C1,
        chainEnd_eq_tripMap (G := G) nC2 (by rw [TC2]; exact tC3), TC2]
      have := tv (3, 2)
      rwa [hq.squareDart_two' (j := 3) (k := 2) rfl, hinv,
        show squareIdxTerm (3, 2) = (0, 2) by decide, hq.squareDart_two' (j := 0) (k := 3) rfl,
        hinv] at this
    · -- `e₂ ↦ c̄₂`
      rw [squareDart_one, show squareIdxInit (1, 1) = (2, 2) by decide,
        hq.squareDart_two' (j := 2) (k := 1) rfl,
        ← chainEnd_tripMap (G := G) nI1 (iI1.exists_isTerminal hG), TI1]
      exact chain (hq.rot_squareCorner_notMem 1)
    · -- `c̄₁ ↦ e₁`
      rw [hq.squareDart_two' (j := 1) (k := 0) rfl] at hex ⊢
      rw [show squareIdxInit (1, 2) = (0, 1) by decide, squareDart_one,
        ← chainEnd_tripMap (G := G.squareMove c) nI₁0 hex, T₁I0]
      exact chain (hq.rot_squareCorner_notMem 0)
    · -- `c₄ ↦ c₁`
      rw [show squareIdxInit (3, 0) = (0, 0) by decide, squareDart_zero, squareDart_zero,
        chainEnd_eq_tripMap (G := G.squareMove c) nC₁3 (by rw [T₁C3]; exact tC₁0), T₁C3,
        chainEnd_eq_tripMap (G := G) nC0 (by rw [TC0]; exact tC1), TC0]
      have := tv (1, 2)
      rwa [hq.squareDart_two' (j := 1) (k := 0) rfl, hinv,
        show squareIdxTerm (1, 2) = (2, 2) by decide, hq.squareDart_two' (j := 2) (k := 1) rfl,
        hinv] at this
    · -- `e₄ ↦ c̄₄`
      rw [squareDart_one, show squareIdxInit (3, 1) = (0, 2) by decide,
        hq.squareDart_two' (j := 0) (k := 3) rfl,
        ← chainEnd_tripMap (G := G) nI3 (iI3.exists_isTerminal hG), TI3]
      exact chain (hq.rot_squareCorner_notMem 3)
    · -- `c̄₃ ↦ e₃`
      rw [hq.squareDart_two' (j := 3) (k := 2) rfl] at hex ⊢
      rw [show squareIdxInit (3, 2) = (2, 1) by decide, squareDart_one,
        ← chainEnd_tripMap (G := G.squareMove c) nI₁2 hex, T₁I2]
      exact chain (hq.rot_squareCorner_notMem 2)
  · rw [hq.squareInit_of_notMem hdv]
    refine chain fun ⟨k, hk⟩ => hdv ?_
    rcases hk with rfl | rfl
    · exact vertexOf_squareCorner_mem_squareVertices c k
    · rw [hq.vertexOf_inv_squareCorner]
      exact vertexOf_squareCorner_mem_squareVertices c (k + 1)

end IsSquareMoveFace

/-- The symbols of `X°(G₁, D₁)` sent to those of `X°(G, D)` along a square move:
`x⁺_d ↦ x⁺_{ρ' d}`, `x⁻_t ↦ x⁻_{ρ t}`, and every other symbol fixed. -/
private def squareSym (ρ' ρ : Equiv.Perm H) : StrandSymbol H b → StrandSymbol H b
  | xPlus d => xPlus (ρ' d)
  | xMinus t => xMinus (ρ t)
  | yPlus e τ => yPlus e τ
  | yMinus e τ => yMinus e τ
  | bd r => bd r
  | bd' r => bd' r

/-- `squareSym` as a bijection of symbols. -/
private def squareSymEquiv (ρ' ρ : Equiv.Perm H) : StrandSymbol H b ≃ StrandSymbol H b where
  toFun := squareSym ρ' ρ
  invFun := squareSym ρ'.symm ρ.symm
  left_inv a := by cases a <;> simp [squareSym]
  right_inv a := by cases a <;> simp [squareSym]

/-- **A square move is a swivel move**. Let `G` be a plabic graph, `(c₁, c₂, c₃, c₄)` an internal
face at which a square move applies, with `v(c₁)` white, and `G₁` the square move of `G` at it. Let
`X` be a generalized triple diagram of `G` that is a triple diagram. Then `G₁` has a generalized
triple diagram `X₁` that is a triple diagram with `X ∼ X₁`; namely `X₁ = X°(G₁, D₁)` for a white
datum `D₁` of `G₁`. -/
@[cluster_algebras "lem_generalized_square"]
theorem IsGeneralizedTripleDiagram.exists_squareMove (hG : G.IsPlabicGraph) {c : H}
    (hq : G.IsSquareMoveFace c) (hc : G.colour c = .white) {H₀ : Type} [Fintype H₀]
    [DecidableEq H₀] {X : TripleData H₀ b} (hgen : G.IsGeneralizedTripleDiagram hG X)
    (hX : X.IsTripleDiagram) :
    ∃ (D₁ : Finset H → Finset (Sym2 H)) (hD₁ : (G.squareMove c).IsWhiteDatum D₁)
      (hX₁ : ((G.squareMove c).strandDiagram (hG.squareMove c) hD₁).IsTripleDiagram),
      (G.squareMove c).IsGeneralizedTripleDiagram (hG.squareMove c)
          ((G.squareMove c).strandDiagram (hG.squareMove c) hD₁) ∧
        TripleDiagram.MoveEquivalent { Dart := H₀, data := X, isTripleDiagram := hX }
          { Dart := (G.squareMove c).StrandDart D₁,
            data := (G.squareMove c).strandDiagram (hG.squareMove c) hD₁,
            isTripleDiagram := hX₁ } := by
  obtain ⟨-, horb, D, hD, ⟨θ₀⟩⟩ := hgen
  have hG₁ := hG.squareMove c
  have hq₁ := hq.squareMove
  have hinv := hG.inv_involutive
  obtain ⟨c0, c1, c2, c3, d0, d1, d2, d3⟩ := hq.colours_of_white hc
  have hD₁ := hq.isWhiteDatum_squareDatum hD
  set D₁ := G.squareDatum c D
  set X₀ := G.strandDiagram hG hD
  set X₁ := (G.squareMove c).strandDiagram hG₁ hD₁
  have hP₀ := isPreTripleDiagram_strandDiagram hG hD
  have hP₁ := isPreTripleDiagram_strandDiagram hG₁ hD₁
  have hX₀ : X₀.IsTripleDiagram := isTripleDiagram_of_iso' θ₀.symm hP₀ hX
  have nb : ¬(Shade.black = Shade.white) := nofun
  -- the corners that are crossings
  have hcr : ∀ k : Fin 4, (k : ℕ) % 2 = 0 →
      G.IsCrossing (G.vertexOf (G.squareCorner c k)) := by
    intro k hk
    rw [hq.isCrossing_vertexOf_squareCorner_iff hG k,
      (hq.colour_squareCorner_of_white hc k).1, if_pos hk]
  have hcr₁ : ∀ k : Fin 4, (k : ℕ) % 2 ≠ 0 →
      (G.squareMove c).IsCrossing (G.vertexOf (G.squareCorner c k)) := by
    intro k hk
    have := hq₁.isCrossing_vertexOf_squareCorner_iff hG₁ k
    change (G.squareMove c).IsCrossing (G.vertexOf (G.squareCorner c k)) ↔
      (G.squareMove c).colour (G.squareCorner c k) = _ at this
    rw [this, (hq.colour_squareCorner_of_white hc k).2, if_neg hk]
  -- the rotations of the strand diagrams at these crossings
  have rotX : ∀ k : Fin 4, (k : ℕ) % 2 = 0 → ∀ i j : Fin 3, j = i + 1 →
      G.strandRotSym D (xPlus (G.squareDart c (k, i))) = xMinus (G.inv (G.squareDart c (k, i))) ∧
        G.strandRotSym D (xMinus (G.inv (G.squareDart c (k, i)))) =
          xPlus (G.squareDart c (k, j)) := by
    intro k hk i j hj
    obtain ⟨h1, h2⟩ := strandRotSym_trivalent hG hD (hcr k hk) (hq.card_vertexOf k)
      (G.squareDart_mem c (k, i))
    refine ⟨h1, h2.trans ?_⟩
    rw [hq.rot_squareDart, hj]
  have rotX₁ : ∀ k : Fin 4, (k : ℕ) % 2 ≠ 0 → ∀ i j : Fin 3, j = i + 1 →
      (G.squareMove c).strandRotSym D₁ (xPlus (G.squareDart c (k, i))) =
          xMinus (G.inv (G.squareDart c (k, i))) ∧
        (G.squareMove c).strandRotSym D₁ (xMinus (G.inv (G.squareDart c (k, i)))) =
          xPlus (G.squareDart c (k, j)) := by
    intro k hk i j hj
    obtain ⟨h1, h2⟩ := strandRotSym_trivalent hG₁ hD₁ (hcr₁ k hk) (hq.card_vertexOf k)
      (G.squareDart_mem c (k, i))
    refine ⟨h1, h2.trans ?_⟩
    change xPlus (G.rot (G.squareDart c (k, i))) = _
    rw [hq.rot_squareDart, hj]
  -- the chains from `c₁` and `c₃`
  have tC : ∀ k j : Fin 4, j = k + 1 → (G.IsTerminal (G.squareCorner c k) ↔
      G.colour (G.squareCorner c j) = .white) := by
    intro k j h
    subst h
    exact hq.isTerminal_iff_of_inv_mem hG (k + 1) (hq.inv_squareCorner_mem k)
  have iC0 : G.IsInitial (G.squareDart c (0, 0)) := by
    rw [hq.isInitial_squareDart_iff hG hc]; rfl
  have iC2 : G.IsInitial (G.squareDart c (2, 0)) := by
    rw [hq.isInitial_squareDart_iff hG hc]; rfl
  have TC0 : G.tripMap (G.squareCorner c 0) = G.squareCorner c 1 :=
    hq.tripMap_squareCorner_of_black hG 0 c1
  have TC2 : G.tripMap (G.squareCorner c 2) = G.squareCorner c 3 :=
    hq.tripMap_squareCorner_of_black hG 2 c3
  have eC0 : G.chainEnd (G.squareDart c (0, 0)) = G.inv (G.squareDart c (2, 2)) := by
    rw [squareDart_zero, hq.squareDart_two' (j := 2) (k := 1) rfl, hinv,
      chainEnd_eq_tripMap (by rw [tC 0 1 rfl, c1]; exact nb)
        (by rw [TC0, tC 1 2 rfl]; exact c2), TC0]
  have eC2 : G.chainEnd (G.squareDart c (2, 0)) = G.inv (G.squareDart c (0, 2)) := by
    rw [squareDart_zero, hq.squareDart_two' (j := 0) (k := 3) rfl, hinv,
      chainEnd_eq_tripMap (by rw [tC 2 3 rfl, c3]; exact nb)
        (by rw [TC2, tC 3 0 rfl]; exact c0), TC2]
  -- the digon `{x⁺_{c₁}, x⁺_{c₃}}`
  set d₁ : G.StrandDart D := ⟨xPlus (G.squareDart c (0, 0)), iC0⟩
  set d₂ : G.StrandDart D := ⟨xPlus (G.squareDart c (2, 0)), iC2⟩
  have hinv₁ : (X₀.inv d₁).1 = xMinus (G.inv (G.squareDart c (2, 2))) := by
    rw [strandDiagram_inv_apply]
    change xMinus (G.chainEnd (G.squareDart c (0, 0))) = _
    rw [eC0]
  have hinv₂ : (X₀.inv d₂).1 = xMinus (G.inv (G.squareDart c (0, 2))) := by
    rw [strandDiagram_inv_apply]
    change xMinus (G.chainEnd (G.squareDart c (2, 0))) = _
    rw [eC2]
  have f₁ : X₀.facePerm d₁ = d₂ := by
    apply Subtype.ext
    rw [RotationSystem.facePerm_apply, strandDiagram_rot_apply, hinv₁]
    exact (rotX 2 rfl 2 0 rfl).2
  have f₂ : X₀.facePerm d₂ = d₁ := by
    apply Subtype.ext
    rw [RotationSystem.facePerm_apply, strandDiagram_rot_apply, hinv₂]
    exact (rotX 0 rfl 2 0 rfl).2
  have htri : ∀ k : Fin 4, (k : ℕ) % 2 = 0 →
      G.IsDatumTriangle D (G.vertexOf (G.squareCorner c k)) ∧
        G.pairOut (G.vertexOf (G.squareCorner c k)) (G.squareDart c (k, 0)) =
          xPlus (G.squareDart c (k, 0)) := by
    intro k hk
    obtain ⟨hτ, hcn⟩ := hD.trivalent (hcr k hk) (hq.card_vertexOf k)
    exact ⟨hτ, by rw [pairOut, if_pos (hcn _ (G.squareDart_mem c (k, 0)))]⟩
  have vd₁ : X₀.vertexOf d₁ = G.strandTriplePoint D (G.vertexOf (G.squareCorner c 0)) :=
    vertexOf_strandDiagram_of_pairOut hG hD (htri 0 rfl).1 (G.squareDart_mem c (0, 0))
      (htri 0 rfl).2.symm
  have vd₂ : X₀.vertexOf d₂ = G.strandTriplePoint D (G.vertexOf (G.squareCorner c 2)) :=
    vertexOf_strandDiagram_of_pairOut hG hD (htri 2 rfl).1 (G.squareDart_mem c (2, 0))
      (htri 2 rfl).2.symm
  have hv : X₀.vertexOf d₁ ≠ X₀.vertexOf d₂ := by
    rw [vd₁, vd₂]
    intro e
    have := hq.injective ((bijOn_strandTriplePoint hG hD).injOn (htri 0 rfl).1 (htri 2 rfl).1 e)
    exact absurd this (by decide)
  obtain ⟨hface, hdig⟩ := isDigon_of_facePerm f₁ f₂
    (by rw [mem_strandDiagram_bdry]; exact id) (by rw [mem_strandDiagram_bdry]; exact id) hv
  have hd : X₀.IsDigon (X₀.faceOf d₁) := hface ▸ hdig
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, -, g1, g2, g3, g4, -, -, -, -, hi₁,
    hi₂, s1, t3, s4, tb1, s6, td2, hφ, s5, tb3, s3, ta1, s2, -, -⟩ :=
    hd.exists_swivel hP₀
  rw [f₁] at g1 hi₂ s6 td2 hφ s5
  have e_a₁ : a₁.1 = xMinus (G.inv (G.squareDart c (0, 0))) := by
    rw [← h1, strandDiagram_rot_apply]; exact (rotX 0 rfl 0 1 rfl).1
  have e_a₂ : a₂.1 = xPlus (G.squareDart c (0, 1)) := by
    rw [← h2, strandDiagram_rot_apply, e_a₁]; exact (rotX 0 rfl 0 1 rfl).2
  have e_a₃ : a₃.1 = xMinus (G.inv (G.squareDart c (0, 1))) := by
    rw [← h3, strandDiagram_rot_apply, e_a₂]; exact (rotX 0 rfl 1 2 rfl).1
  have e_a₄ : a₄.1 = xPlus (G.squareDart c (0, 2)) := by
    rw [← h4, strandDiagram_rot_apply, e_a₃]; exact (rotX 0 rfl 1 2 rfl).2
  have e_b₁ : b₁.1 = xMinus (G.inv (G.squareDart c (2, 0))) := by
    rw [← g1, strandDiagram_rot_apply]; exact (rotX 2 rfl 0 1 rfl).1
  have e_b₂ : b₂.1 = xPlus (G.squareDart c (2, 1)) := by
    rw [← g2, strandDiagram_rot_apply, e_b₁]; exact (rotX 2 rfl 0 1 rfl).2
  have e_b₃ : b₃.1 = xMinus (G.inv (G.squareDart c (2, 1))) := by
    rw [← g3, strandDiagram_rot_apply, e_b₂]; exact (rotX 2 rfl 1 2 rfl).1
  have e_b₄ : b₄.1 = xPlus (G.squareDart c (2, 2)) := by
    rw [← g4, strandDiagram_rot_apply, e_b₃]; exact (rotX 2 rfl 1 2 rfl).2
  -- the bijection of darts
  set ρ' := hq.squareInit
  set ρ := hq.squareTerm with hρ
  have hiff : ∀ a, (G.squareMove c).IsStrandSymbol D₁ a ↔
      G.IsStrandSymbol D (squareSym ρ' ρ a) := by
    intro a
    cases a with
    | xPlus d => exact hq.isInitial_squareMove_iff_squareInit hG hc d
    | xMinus t => exact hq.isTerminal_squareMove_iff_squareTerm hG hc t
    | yPlus e τ => exact hq.isDatumSegment_squareDatum_iff hD
    | yMinus e τ => exact hq.isDatumSegment_squareDatum_iff hD
    | bd r => exact Iff.rfl
    | bd' r => exact Iff.rfl
  set θ : (G.squareMove c).StrandDart D₁ ≃ G.StrandDart D :=
    (squareSymEquiv ρ' ρ).subtypeEquiv hiff
  have θval : ∀ a, (θ a).1 = squareSym ρ' ρ a.1 := fun _ => rfl
  -- away from the corners `squareSym` is the identity
  have hlegc : ∀ i : Fin b, G.vertexOf (G.leg i) ∉ G.squareVertices c := by
    intro i h
    obtain ⟨k, hk⟩ := mem_squareVertices.1 h
    exact hq.not_isBoundaryVertex k (hk ▸ hG.isBoundaryVertex_of_isLeg ⟨i, rfl⟩)
  have sEnd : ∀ r, squareSym ρ' ρ (G.endSymbol r) = G.endSymbol r := by
    intro r
    rcases exists_sourceIndex_or_targetIndex r with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [endSymbol_sourceIndex]
      exact congrArg xPlus (hq.squareInit_of_notMem (hlegc i))
    · rw [endSymbol_targetIndex]
      exact congrArg xMinus (hq.squareTerm_of_notMem hG (by rw [hinv]; exact hlegc i))
  have hpairfix : ∀ (τ : Finset H) (p : H), (∀ q ∈ τ, G.vertexOf q ∉ G.squareVertices c) →
      p ∈ τ → squareSym ρ' ρ (G.pairOut τ p) = G.pairOut τ p ∧
        squareSym ρ' ρ (G.pairIn τ p) = G.pairIn τ p := by
    intro τ p hτc hp
    unfold pairOut pairIn
    split_ifs
    · exact ⟨congrArg xPlus (hq.squareInit_of_notMem (hτc p hp)),
        congrArg xMinus (hq.squareTerm_of_notMem hG (by rw [hinv]; exact hτc p hp))⟩
    · exact ⟨rfl, rfl⟩
  -- darts of the two triple points of the digon
  have hnot : ∀ z : G.StrandDart D, z ∈ X₀.vertexOf d₁ ∪ X₀.vertexOf d₂ →
      ¬X₀.IsBoundaryVertex (X₀.vertexOf z) := by
    intro z hz
    rcases mem_union.1 hz with hz | hz
    · rw [X₀.vertexOf_eq_of_mem hz]; exact hi₁
    · rw [X₀.vertexOf_eq_of_mem hz]; exact hi₂
  have hnotT : ∀ τ : Finset H, G.IsDatumTriangle D τ →
      τ ≠ G.vertexOf (G.squareCorner c 0) → τ ≠ G.vertexOf (G.squareCorner c 2) →
      ∀ z : G.StrandDart D, X₀.vertexOf z = G.strandTriplePoint D τ →
        z ∉ X₀.vertexOf d₁ ∪ X₀.vertexOf d₂ := by
    intro τ hτ hτ1 hτ2 z hz hmem
    have inj := (bijOn_strandTriplePoint hG hD).injOn
    rcases mem_union.1 hmem with hm | hm
    · rw [X₀.vertexOf_eq_of_mem hm, vd₁] at hz
      exact hτ1 (inj hτ (htri 0 rfl).1 hz.symm)
    · rw [X₀.vertexOf_eq_of_mem hm, vd₂] at hz
      exact hτ2 (inj hτ (htri 2 rfl).1 hz.symm)
  have fixed : ∀ a : (G.squareMove c).StrandDart D₁,
      squareSym ρ' ρ ((G.squareMove c).strandRotSym D₁ a.1) =
        G.strandRotSym D (squareSym ρ' ρ a.1) →
      θ a ∉ X₀.vertexOf d₁ ∪ X₀.vertexOf d₂ → θ (X₁.rot a) = X₀.swivelRot d₁ (θ a) := by
    intro a e1 e2
    rw [← f₁] at e2
    rw [TripleData.swivelRot_apply_of_notMem e2]
    exact Subtype.ext e1
  -- the twelve darts at the black corners of `G`
  have outCase : ∀ (k : Fin 4), (k : ℕ) % 2 ≠ 0 → ∀ (i j : Fin 3), j = i + 1 →
      ∀ (a : (G.squareMove c).StrandDart D₁), a.1 = xPlus (G.squareDart c (k, i)) →
      ∀ N M : G.StrandDart D, N.1 = xPlus (G.squareDart c (squareIdxInit (k, i))) →
        M.1 = xMinus (G.inv (G.squareDart c (squareIdxTerm (k, i)))) → X₀.swivelRot d₁ N = M →
        θ (X₁.rot a) = X₀.swivelRot d₁ (θ a) := by
    intro k hk i j hj a ha N M hN hM hs
    have eθ : θ a = N := Subtype.ext (by
      rw [θval, ha, hN]
      exact congrArg xPlus (hq.squareInit_squareDart _))
    rw [eθ, hs]
    apply Subtype.ext
    rw [θval, strandDiagram_rot_apply, ha, (rotX₁ k hk i j hj).1, hM]
    exact congrArg xMinus (hq.squareTerm_inv_squareDart _)
  have inCase : ∀ (k : Fin 4), (k : ℕ) % 2 ≠ 0 → ∀ (i j : Fin 3), j = i + 1 →
      ∀ (a : (G.squareMove c).StrandDart D₁), a.1 = xMinus (G.inv (G.squareDart c (k, i))) →
      ∀ N M : G.StrandDart D, N.1 = xMinus (G.inv (G.squareDart c (squareIdxTerm (k, i)))) →
        M.1 = xPlus (G.squareDart c (squareIdxInit (k, j))) → X₀.swivelRot d₁ N = M →
        θ (X₁.rot a) = X₀.swivelRot d₁ (θ a) := by
    intro k hk i j hj a ha N M hN hM hs
    have eθ : θ a = N := Subtype.ext (by
      rw [θval, ha, hN]
      exact congrArg xMinus (hq.squareTerm_inv_squareDart _))
    rw [eθ, hs]
    apply Subtype.ext
    rw [θval, strandDiagram_rot_apply, ha, (rotX₁ k hk i j hj).2, hM]
    exact congrArg xPlus (hq.squareInit_squareDart _)
  have hisos : (G.squareMove c).strandDiagram hG₁ hD₁ |>.Isomorphic (X₀.swivelMove d₁) := by
    refine strandDiagram_isomorphic_of hG₁ hD₁ _ θ ?_ ?_ ?_ ?_ ?_
    · refine strandDiagram_map_inv_of hG₁ hD₁ hP₀.inv_involutive _ ?_
      rintro ⟨a, ha⟩ (⟨d, rfl⟩ | ⟨e, τ, rfl⟩ | ⟨r, rfl⟩)
      · apply Subtype.ext
        change (θ _).1 = (X₀.inv (θ _)).1
        rw [θval, strandDiagram_inv_apply, strandDiagram_inv_apply, θval]
        change xMinus (ρ ((G.squareMove c).chainEnd d)) = xMinus (G.chainEnd (ρ' d))
        rw [hq.squareTerm_chainEnd hG hc ha]
      · apply Subtype.ext
        change (θ _).1 = (X₀.inv (θ _)).1
        rw [θval, strandDiagram_inv_apply, strandDiagram_inv_apply, θval]
        have hseg₁ : (G.squareMove c).IsDatumSegment D₁ e τ := ha
        have hseg : G.IsDatumSegment D e τ := (hq.isDatumSegment_squareDatum_iff hD).1 hseg₁
        obtain ⟨o1, o2, -⟩ := hD₁.otherTriangle_spec hseg₁
        have o1' := (hq.isDatumSegment_squareDatum_iff hD).1 o1
        have ho : (G.squareMove c).otherTriangle D₁ e τ = G.otherTriangle D e τ := by
          obtain ⟨-, -, -, -, hm⟩ := id o1'
          exact hD.eq_otherTriangle hseg (.of_isDatumSegment o1') hm o2
        change yMinus e ((G.squareMove c).otherTriangle D₁ e τ) =
          yMinus e (G.otherTriangle D e τ)
        rw [ho]
      · rfl
    · intro a
      change θ (X₁.rot a) = X₀.swivelRot d₁ (θ a)
      rcases strandDart_cases hG₁ hD₁ a with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ |
        ⟨τ, p, hτ, hp, rfl⟩ | ⟨τ, p, hτ, hp, rfl⟩
      · refine fixed _ ?_ ?_
        · change squareSym ρ' ρ (G.endSymbol r) = G.endSymbol r
          exact sEnd r
        · intro hm
          exact hnot _ hm ⟨_, X₀.self_mem_vertexOf _, (mem_strandDiagram_bdry hG hD).2 trivial⟩
      · refine fixed _ rfl ?_
        intro hm
        exact hnot _ hm ⟨_, X₀.self_mem_vertexOf _, (mem_strandDiagram_bdry hG hD).2 trivial⟩
      · refine fixed _ ?_ ?_
        · change squareSym ρ' ρ ((G.squareMove c).strandRotSym D₁
              ((G.squareMove c).endSymbol r)) = G.strandRotSym D (squareSym ρ' ρ (G.endSymbol r))
          rw [strandRotSym_endSymbol hG₁, sEnd, strandRotSym_endSymbol hG]
          rfl
        · intro hm
          refine hnot _ hm ⟨X₀.rot (θ _), X₀.rot_mem_vertexOf _, ?_⟩
          rw [mem_strandDiagram_bdry, strandDiagram_rot_apply, θval]
          change (G.strandRotSym D (squareSym ρ' ρ (G.endSymbol r))).IsBoundary
          rw [sEnd, strandRotSym_endSymbol hG]
          trivial
      · rcases hq.isDatumTriangle_squareDatum hτ with ⟨k, rfl, hk⟩ | ⟨hτD, hτc⟩
        · have hk' : (k : ℕ) % 2 ≠ 0 := by
            intro h
            rw [(hq.colour_squareCorner_of_white hc k).2, if_pos h] at hk
            exact nb hk
          obtain ⟨⟨k', i⟩, rfl⟩ := hq.exists_squareDart_eq
            (by rw [G.vertexOf_eq_of_mem hp]; exact vertexOf_squareCorner_mem_squareVertices c k)
          obtain rfl : k = k' := hq.injective (by
            change G.vertexOf (G.squareCorner c k) = G.vertexOf (G.squareCorner c k')
            rw [← G.vertexOf_eq_of_mem (G.squareDart_mem c (k', i)), G.vertexOf_eq_of_mem hp])
          obtain ⟨-, hcn⟩ := hD₁.trivalent (hcr₁ k hk') (hq.card_vertexOf k)
          have ha : (G.squareMove c).pairOut (G.vertexOf (G.squareCorner c k))
              (G.squareDart c (k, i)) =
              xPlus (G.squareDart c (k, i)) := by rw [pairOut, if_pos]; exact hcn _ hp
          have hk4 : k = 1 ∨ k = 3 :=
            (by decide : ∀ k : Fin 4, (k : ℕ) % 2 ≠ 0 → k = 1 ∨ k = 3) k hk'
          have hi : i = 0 ∨ i = 1 ∨ i = 2 :=
            (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i
          rcases hk4 with rfl | rfl <;> rcases hi with rfl | rfl | rfl
          · exact outCase 1 hk' 0 1 rfl _ ha d₂ b₃ rfl (by rw [e_b₃]; rfl) s5
          · exact outCase 1 hk' 1 2 rfl _ ha b₄ a₁ (by rw [e_b₄]; rfl) (by rw [e_a₁]; rfl) s3
          · exact outCase 1 hk' 2 0 rfl _ ha a₂ (X₀.inv d₁) (by rw [e_a₂]; rfl)
              (by rw [hinv₁]; rfl) s2
          · exact outCase 3 hk' 0 1 rfl _ ha d₁ a₃ rfl (by rw [e_a₃]; rfl) s1
          · exact outCase 3 hk' 1 2 rfl _ ha a₄ b₁ (by rw [e_a₄]; rfl) (by rw [e_b₁]; rfl) s4
          · exact outCase 3 hk' 2 0 rfl _ ha b₂ (X₀.inv d₂) (by rw [e_b₂]; rfl)
              (by rw [hinv₂]; rfl) s6
        · have hne : ∀ k, τ ≠ G.vertexOf (G.squareCorner c k) := fun k e => hτc _
            (by rw [e]; exact G.self_mem_vertexOf _) (vertexOf_squareCorner_mem_squareVertices c k)
          refine fixed _ ?_ (hnotT τ hτD (hne 0) (hne 2) _
            (vertexOf_strandDiagram_of_pairOut hG hD hτD hp (by
              rw [θval]; exact (hpairfix τ p hτc hp).1)))
          change squareSym ρ' ρ ((G.squareMove c).strandRotSym D₁
              ((G.squareMove c).pairOut τ p)) = G.strandRotSym D (squareSym ρ' ρ (G.pairOut τ p))
          rw [strandRotSym_pairOut hG₁ hτ hp]
          change squareSym ρ' ρ (G.pairIn τ p) = _
          rw [(hpairfix τ p hτc hp).1, (hpairfix τ p hτc hp).2, strandRotSym_pairOut hG hτD hp]
      · rcases hq.isDatumTriangle_squareDatum hτ with ⟨k, rfl, hk⟩ | ⟨hτD, hτc⟩
        · have hk' : (k : ℕ) % 2 ≠ 0 := by
            intro h
            rw [(hq.colour_squareCorner_of_white hc k).2, if_pos h] at hk
            exact nb hk
          obtain ⟨⟨k', i⟩, rfl⟩ := hq.exists_squareDart_eq
            (by rw [G.vertexOf_eq_of_mem hp]; exact vertexOf_squareCorner_mem_squareVertices c k)
          obtain rfl : k = k' := hq.injective (by
            change G.vertexOf (G.squareCorner c k) = G.vertexOf (G.squareCorner c k')
            rw [← G.vertexOf_eq_of_mem (G.squareDart_mem c (k', i)), G.vertexOf_eq_of_mem hp])
          obtain ⟨-, hcn⟩ := hD₁.trivalent (hcr₁ k hk') (hq.card_vertexOf k)
          have ha : (G.squareMove c).pairIn (G.vertexOf (G.squareCorner c k))
              (G.squareDart c (k, i)) =
              xMinus (G.inv (G.squareDart c (k, i))) := by
            rw [pairIn, if_pos]
            · rfl
            · exact hcn _ hp
          have hk4 : k = 1 ∨ k = 3 :=
            (by decide : ∀ k : Fin 4, (k : ℕ) % 2 ≠ 0 → k = 1 ∨ k = 3) k hk'
          have hi : i = 0 ∨ i = 1 ∨ i = 2 :=
            (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i
          rcases hk4 with rfl | rfl <;> rcases hi with rfl | rfl | rfl
          · exact inCase 1 hk' 0 1 rfl _ ha b₃ b₄ (by rw [e_b₃]; rfl) (by rw [e_b₄]; rfl) tb3
          · exact inCase 1 hk' 1 2 rfl _ ha a₁ a₂ (by rw [e_a₁]; rfl) (by rw [e_a₂]; rfl) ta1
          · exact inCase 1 hk' 2 0 rfl _ ha (X₀.inv d₁) d₂ (by rw [hinv₁]; rfl) rfl hφ
          · exact inCase 3 hk' 0 1 rfl _ ha a₃ a₄ (by rw [e_a₃]; rfl) (by rw [e_a₄]; rfl) t3
          · exact inCase 3 hk' 1 2 rfl _ ha b₁ b₂ (by rw [e_b₁]; rfl) (by rw [e_b₂]; rfl) tb1
          · exact inCase 3 hk' 2 0 rfl _ ha (X₀.inv d₂) d₁ (by rw [hinv₂]; rfl) rfl td2
        · have hne : ∀ k, τ ≠ G.vertexOf (G.squareCorner c k) := fun k e => hτc _
            (by rw [e]; exact G.self_mem_vertexOf _) (vertexOf_squareCorner_mem_squareVertices c k)
          have hq2 := hD.cornerNext_mem hτD (hD.cornerNext_mem hτD hp)
          refine fixed _ ?_ (hnotT τ hτD (hne 0) (hne 2) _
            (vertexOf_strandDiagram_of_pairIn hG hD hτD hp (by
              rw [θval]; exact (hpairfix τ p hτc hp).2)))
          change squareSym ρ' ρ ((G.squareMove c).strandRotSym D₁
              ((G.squareMove c).pairIn τ p)) = G.strandRotSym D (squareSym ρ' ρ (G.pairIn τ p))
          rw [strandRotSym_pairIn hG₁ hD₁ hτ hp]
          change squareSym ρ' ρ (G.pairOut τ (G.cornerNext τ (G.cornerNext τ p))) = _
          rw [(hpairfix τ _ hτc hq2).1, (hpairfix τ p hτc hp).2, strandRotSym_pairIn hG hD hτD hp]
    · rintro ⟨a, ha⟩
      rw [TripleData.swivelMove_bdry, mem_strandDiagram_bdry, θval]
      cases a <;> exact Iff.rfl
    · rintro ⟨a, ha⟩ -
      rw [TripleData.swivelMove_isOut, strandDiagram_isOut, θval]
      cases a <;> rfl
    · intro r
      rw [TripleData.swivelMove_endDart]
      exact Subtype.ext (sEnd r)
  obtain ⟨θ'⟩ := hisos
  have hX₁ : X₁.IsTripleDiagram :=
    isTripleDiagram_of_iso' θ' hP₁ (hd.isTripleDiagram_swivelMove hX₀)
  refine ⟨D₁, hD₁, hX₁, ⟨hP₁, hq.exists_isInitial_mem_trip_squareMove hG hc horb, D₁, hD₁,
    TripleData.Isomorphic.refl _⟩, ?_⟩
  let Y₀ : TripleDiagram b :=
    { Dart := G.StrandDart D, data := X₀, isTripleDiagram := hX₀ }
  exact (TripleDiagram.MoveEquivalent.of_isomorphic (X' := Y₀) ⟨θ₀⟩).trans
    (TripleDiagram.MoveEquivalent.of_isSwivelMove ⟨d₁, hd, ⟨θ'.symm⟩⟩)

end PlabicData

end ClusterAlgebras

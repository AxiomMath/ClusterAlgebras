/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.GeneralizedMoves
public import ClusterAlgebras.Plabic.LocalMoves
public import ClusterAlgebras.Plabic.Excision
public import ClusterAlgebras.Plabic.TrivalentMoves

/-!
# Strand diagrams of a white contraction, local moves and connectedness

Let `P` be a plabic graph and `{d, d̄}` an edge whose ends `w₁ = v(d)` and `w₂ = v(d̄)` are
distinct white vertices with `p ≥ 3` and `q ≥ 3` darts, and let `Q` be the contraction of `P` along
`{d, d̄}`, with merged vertex `v`. Gluing corner triangulations `D₁`, `D₂` of `w₁`, `w₂` along the
diagonal `γ_e` gives a corner triangulation `κ₁(D₁) ∪ κ₂(D₂) ∪ {γ_e}` of `v`. If the white data
`D^P` of `P` and `D^Q` of `Q` agree at the other crossings and are glued in this way at `v`, the
strand diagrams `X°(P, D^P)` and `X°(Q, D^Q)` are isomorphic: the chains of `P` and `Q` from an
initial dart other than `d`, `d̄` coincide, the two darts `d`, `d̄`, which are both initial and
terminal in `P`, become the strands crossing `γ_e`, and the triangles of `D^Q_v` are the images of
those of `D^P_{w₁}` and `D^P_{w₂}`. Consequently every generalized triple diagram of `P` is one of
`Q`, and conversely a strand diagram of `Q` whose white datum contains `γ_e` at `v` is a
generalized triple diagram of `P`.

Together with the square moves, removals and black contractions, this shows that the relation `∘∼`
acts on generalized triple diagrams that are triple diagrams by swivel moves. Finally, a
generalized triple diagram on which `⟨σ, d ↦ d̄⟩` acts transitively is a triple diagram: the graph
is transformed, keeping the diagram generalized, by splitting the crossings with at least four
darts along diagonals of the white datum, recolouring black the white vertices with at most two
darts, inserting black vertices on the edges without a black end and contracting the edges joining
two black vertices; the result is normal, where `X(G)` is a triple diagram, unless it has a loop at
a black vertex, which is excluded by the transitivity since a loop separates the graph
(`DiskMap.IsDiskMap.loop_separates`).

## Main results

* `ClusterAlgebras.PlabicData.strandDiagram_isomorphic_contractEdge`: the strand diagrams of a
  white contraction are isomorphic.
* `ClusterAlgebras.PlabicData.IsGeneralizedTripleDiagram.contractEdge_white`: contracting an edge
  between two crossings preserves generalized triple diagrams.
* `ClusterAlgebras.PlabicData.isGeneralizedTripleDiagram_of_contractEdge_white`: splitting a
  crossing along a diagonal gives a generalized triple diagram.
* `ClusterAlgebras.PlabicGraph.CircMoveEquivalent.exists_moveEquivalent`: `∘∼`-moves are swivel
  moves.
* `ClusterAlgebras.PlabicData.IsGeneralizedTripleDiagram.isTripleDiagram`: connected generalized
  triple diagrams are triple diagrams.

## Implementation notes

* The darts of the contraction form the subtype `H \ {d, d̄}` of `H`, and the merged vertex is
  `mergedVertex` read in the subtype, as in `bijOn_cornerGlue`. The isomorphism of strand diagrams
  is built in the direction `X°(Q, D^Q) → X°(P, D^P)`, where it is a map of symbols defined without
  choices: a symbol of `Q` is read in `H`, the strands `y^±_{γ_e, τ}` become `x⁺_d`, `x⁻_{d̄}` (for
  the triangle `τ` on the side of `w₁`) or `x⁺_{d̄}`, `x⁻_d` (on the side of `w₂`), and the other
  strands of `v` are pulled back along `κ₁` or `κ₂`.
* A triple diagram `X` together with the proof that it is one is a `TripleDiagram`; the move
  equivalence `X ∼ X'` is `TripleDiagram.MoveEquivalent`.
* In the proof of `IsGeneralizedTripleDiagram.isTripleDiagram` the four stages are inductions over
  plabic graphs bundled with their darts (`PlabicGraph`). The splitting stage decreases the sum of
  `2^{|w|}` over the darts of the crossings `w` with at least four darts; the insertion stage
  decreases the number of darts of edges without a black internal end; the contraction stage
  decreases the number of darts.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function

namespace PlabicData

open StrandSymbol

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}

/-! ### Generic helpers -/

/-- A bijection intertwining two rotations maps each vertex onto a vertex. -/
private theorem map_vertexOf_of_semiconj {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
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

section StrandIso

variable {G : PlabicData H b} (hG : G.IsPlabicGraph) {D : Finset H → Finset (Sym2 H)}
  (hD : G.IsWhiteDatum D) {H' : Type*} [Fintype H'] [DecidableEq H']

/-- An isomorphism out of a strand diagram: a bijection of darts commuting with the involutions
and the rotations, matching the boundaries, the orientations and the darts of the endpoints. -/
private theorem strandDiagram_isomorphic_of' (Y : TripleData H' b) (θ : G.StrandDart D ≃ H')
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
       rw [TripleData.endpoint, TripleData.endpoint, map_vertexOf_of_semiconj θ hrot, hend] }⟩

omit [Fintype H'] [DecidableEq H'] in
/-- To check that a map out of a strand diagram commutes with the involutions, it suffices to
check it on the symbols `x⁺_d`, `y⁺_{s,τ}` and `∂_r`. -/
private theorem strandDiagram_map_inv_of' {Y : TripleData H' b} (hY : Function.Involutive Y.inv)
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

/-- Of the listings `(x, y, z)` and `(x, z, y)`, at most one is clockwise. -/
private theorem isCornerClockwise_not_swap {α : Type*} {R : RotationSystem α} {x y z : α}
    (h : R.IsCornerClockwise x y z) : ¬R.IsCornerClockwise x z y := by
  rintro ⟨j', hj', hj'z, hj'y⟩
  obtain ⟨j, hj, hjy, hjz⟩ := h
  rcases le_or_gt j j' with hle | hlt
  · exact hj'y j hj hle hjy
  · exact hjz j' hj' hlt.le hj'z

/-- The clockwise successors in a triangle `{x, y, z}` of a white datum with `(x, y, z)`
clockwise. -/
private theorem cornerNext_eq_of_isCornerClockwise {H₀ : Type*} [Fintype H₀] [DecidableEq H₀]
    {G : PlabicData H₀ b} {D : Finset H₀ → Finset (Sym2 H₀)} (hD : G.IsWhiteDatum D)
    {τ : Finset H₀} (hτ : G.IsDatumTriangle D τ) {x y z : H₀} (he : τ = {x, y, z})
    (hc : G.IsCornerClockwise x y z) :
    G.cornerNext τ x = y ∧ G.cornerNext τ y = z ∧ G.cornerNext τ z = x := by
  have hx : x ∈ τ := by rw [he]; simp
  obtain ⟨q, r, hτ', hxq, hxr, hqr, h1, h2, h3, -, -, -, hcl⟩ := hD.cornerNext_spec hτ hx
  have hq : q ∈ ({x, y, z} : Finset H₀) := by rw [← he, hτ']; simp
  have hr : r ∈ ({x, y, z} : Finset H₀) := by rw [← he, hτ']; simp
  simp only [mem_insert, mem_singleton] at hq hr
  rcases hq with rfl | rfl | rfl
  · exact absurd rfl hxq
  · rcases hr with rfl | rfl | rfl
    · exact absurd rfl hxr
    · exact absurd rfl hqr
    · exact ⟨h1, h2, h3⟩
  · rcases hr with rfl | rfl | rfl
    · exact absurd rfl hxr
    · exact absurd hcl (isCornerClockwise_not_swap hc)
    · exact absurd rfl hqr

/-- In a triangle of a white datum, the clockwise successor of `x` is `σ⁻¹ x` exactly when the
pair `{x, cornerNext τ x}` is not an element of `D_{v(x)}`. -/
private theorem cornerNext_eq_rot_symm_iff {H₀ : Type*} [Fintype H₀] [DecidableEq H₀]
    {G : PlabicData H₀ b} {D : Finset H₀ → Finset (Sym2 H₀)} (hD : G.IsWhiteDatum D)
    {τ : Finset H₀} (hτ : G.IsDatumTriangle D τ) {x : H₀} (hx : x ∈ τ) :
    G.cornerNext τ x = G.rot.symm x ↔ s(x, G.cornerNext τ x) ∉ D (G.vertexOf x) := by
  constructor
  · intro h hm
    obtain ⟨hw, -⟩ := hτ.vertexOf hx
    refine cornerSide_notMem_of_isCornerTriangulation (hD _ hw) (G.self_mem_vertexOf x) ?_
    rwa [RotationSystem.cornerSide, ← h]
  · intro h
    by_contra h'
    exact h (hD.mk_cornerNext_mem hτ hx h')

/-- **Chains under a first return.** Suppose that the trip map of `G'` is the first return to `Y`
of the trip map `T` of `G`, that a dart `y` of `Y` is terminal in `G'` exactly when one of
`y, T y, …` before its first return is terminal in `G`, and that the first such dart then has the
reverse of `y` in `G'` as its reverse. Then the chains of `G` and `G'` from an initial dart of `G'`
end at darts with the same reverse. -/
private theorem inv_chainEnd_eq_of_firstReturn' {G : PlabicData H b} {Y : Set H} [Fintype Y]
    {G' : PlabicData Y b} (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
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
    rw [← hyN] at this
    exact this
  have h1 : G.IsTerminal (G.tripMap^[N + Nat.find hex] c) := by
    rw [tripMap_iterate_eq hG, ← hTj]
    exact ht
  have hlen : G.chainLength c = N + Nat.find hex := by
    refine le_antisymm (chainLength_le h1) (not_lt.1 fun hlt => ?_)
    have h2 := chainLength_spec (G := G) ⟨_, h1⟩
    rw [tripMap_iterate_eq hG] at h2
    by_cases hL : G.chainLength c < N
    · exact hnt _ hL h2
    · obtain ⟨i, hi⟩ : ∃ i, G.chainLength c = N + i :=
        ⟨_, (Nat.add_sub_cancel' (not_lt.1 hL)).symm⟩
      rw [hi] at h2 hlt
      apply hmin i (by omega)
      rwa [hyN, hpow]
  rw [chainEnd_def, hlen, tripMap_iterate_eq hG, ← hTj]
  exact harr _ _ hj ht hmin

/-- A terminal dart is the end of its own chain. -/
private theorem chainEnd_eq_self_of_isTerminal {G : PlabicData H b} {t : H}
    (ht : G.IsTerminal t) : G.chainEnd t = t := by
  have h0 : G.chainLength t = 0 := Nat.le_zero.1 (chainLength_le (j := 0) ht)
  rw [chainEnd_def, h0]
  rfl

/-! ### The corner map at one end of an edge -/

section Ends

variable (G : PlabicData H b)

/-- The darts of the merged vertex on the side of `v(a)`, together with `σ⁻¹(ā)`: the set
`κ_a(v(a))` (with `a` itself). -/
private def glueSide (a : H) : Finset H := insert (G.rot.symm (G.inv a)) (G.vertexOf a)

/-- The inverse of the corner map at the end `a`: `σ⁻¹(ā) ↦ a`, fixing the other darts. -/
private def glueBack (a x : H) : H := if x = G.rot.symm (G.inv a) then a else x


/-- The symbol `y⁺_{e,t}` of the contraction, read at the end `a`: `x⁺_a` if `e = γ_e`, and
`y⁺_{κ_a⁻¹ e, κ_a⁻¹ t}` otherwise. -/
private def glueEndPlus (a : H) (e : Sym2 H) (t : Finset H) : StrandSymbol H b :=
  if e = G.cornerGlueDiagonal a then xPlus a
  else yPlus (e.map (glueBack G a)) (t.image (glueBack G a))

/-- The symbol `y⁻_{e,t}` of the contraction, read at the end `a`: `x⁻_ā` if `e = γ_e`, and
`y⁻_{κ_a⁻¹ e, κ_a⁻¹ t}` otherwise. -/
private def glueEndMinus (a : H) (e : Sym2 H) (t : Finset H) : StrandSymbol H b :=
  if e = G.cornerGlueDiagonal a then xMinus (G.inv a)
  else yMinus (e.map (glueBack G a)) (t.image (glueBack G a))

/-- The symbol `y⁺_{e,t}` of the contraction along `{d, d̄}`, read in `G`. -/
private def glueYPlus (d : H) (e : Sym2 H) (t : Finset H) : StrandSymbol H b :=
  if t ⊆ glueSide G d then glueEndPlus G d e t
  else if t ⊆ glueSide G (G.inv d) then glueEndPlus G (G.inv d) e t else yPlus e t

/-- The symbol `y⁻_{e,t}` of the contraction along `{d, d̄}`, read in `G`. -/
private def glueYMinus (d : H) (e : Sym2 H) (t : Finset H) : StrandSymbol H b :=
  if t ⊆ glueSide G d then glueEndMinus G d e t
  else if t ⊆ glueSide G (G.inv d) then glueEndMinus G (G.inv d) e t else yMinus e t

/-- **The symbols of the contraction read in `G`.** A symbol of the strand diagram of the
contraction along `{d, d̄}` is sent to a symbol of `G`: `x^±` and `∂`, `∂'` are kept, and
`y^±_{e,t}` is read by `glueYPlus`, `glueYMinus`. -/
private def glueSym (d : H) : StrandSymbol (({d, G.inv d} : Set H)ᶜ : Set H) b → StrandSymbol H b
  | xPlus c => xPlus c
  | xMinus t => xMinus t
  | yPlus e t => glueYPlus G d (e.map Subtype.val) (t.map (Embedding.subtype _))
  | yMinus e t => glueYMinus G d (e.map Subtype.val) (t.map (Embedding.subtype _))
  | bd r => bd r
  | bd' r => bd' r

/-- A left inverse of `glueSym`: `x⁺_d`, `x⁻_{d̄}` (resp. `x⁺_{d̄}`, `x⁻_d`) become the strands
`y^±_{γ_e, κ_a τ}` across `γ_e` in the triangle `κ_a τ` of the side triangle `τ` of the end `a = d`
(resp. `a = d̄`), and the strands at `v(d)`, `v(d̄)` are pushed forward along `κ₁`, `κ₂`. -/
private noncomputable def glueInvSym (d : H) (D : Finset H → Finset (Sym2 H)) :
    StrandSymbol H b → StrandSymbol H b
  | xPlus c =>
    if c = d then yPlus (G.cornerGlueDiagonal d) ((G.sideTriangle D d).image (G.cornerMapFst d))
    else if c = G.inv d then
      yPlus (G.cornerGlueDiagonal d) ((G.sideTriangle D (G.inv d)).image (G.cornerMapFst (G.inv d)))
    else xPlus c
  | xMinus t =>
    if t = G.inv d then
      yMinus (G.cornerGlueDiagonal d) ((G.sideTriangle D d).image (G.cornerMapFst d))
    else if t = d then
      yMinus (G.cornerGlueDiagonal d)
        ((G.sideTriangle D (G.inv d)).image (G.cornerMapFst (G.inv d)))
    else xMinus t
  | yPlus s τ =>
    if τ ⊆ G.vertexOf d then yPlus (s.map (G.cornerMapFst d)) (τ.image (G.cornerMapFst d))
    else if τ ⊆ G.vertexOf (G.inv d) then
      yPlus (s.map (G.cornerMapFst (G.inv d))) (τ.image (G.cornerMapFst (G.inv d)))
    else yPlus s τ
  | yMinus s τ =>
    if τ ⊆ G.vertexOf d then yMinus (s.map (G.cornerMapFst d)) (τ.image (G.cornerMapFst d))
    else if τ ⊆ G.vertexOf (G.inv d) then
      yMinus (s.map (G.cornerMapFst (G.inv d))) (τ.image (G.cornerMapFst (G.inv d)))
    else yMinus s τ
  | bd r => bd r
  | bd' r => bd' r

variable {G} {a : H} (hinv : Involutive G.inv) (hne : G.vertexOf a ≠ G.vertexOf (G.inv a))

include hne in
private theorem notMem_inv_of_mem_end {x : H} (hx : x ∈ G.vertexOf a) :
    x ∉ G.vertexOf (G.inv a) := fun h =>
  hne ((G.vertexOf_eq_of_mem hx).symm.trans (G.vertexOf_eq_of_mem h))

include hne in
private theorem rot_symm_inv_notMem : G.rot.symm (G.inv a) ∉ G.vertexOf a := fun h =>
  notMem_inv_of_mem_end hne h (G.rot_symm_mem_vertexOf (G.inv a))

private theorem cornerMapFst_mem_glueSide {x : H} (hx : x ∈ G.vertexOf a) :
    G.cornerMapFst a x ∈ glueSide G a := by
  unfold RotationSystem.cornerMapFst glueSide
  split_ifs
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem hx

include hne in
private theorem cornerMapFst_ne_self (x : H) : G.cornerMapFst a x ≠ a := by
  unfold RotationSystem.cornerMapFst
  split_ifs with h
  · intro h'
    have : G.rot.symm (G.inv a) ∈ G.vertexOf a := by rw [h']; exact G.self_mem_vertexOf a
    exact rot_symm_inv_notMem hne this
  · exact h

include hne in
private theorem glueBack_cornerMapFst {x : H} (hx : x ∈ G.vertexOf a) :
    glueBack G a (G.cornerMapFst a x) = x := by
  by_cases hxa : x = a
  · subst hxa
    simp [RotationSystem.cornerMapFst, glueBack]
  · rw [RotationSystem.cornerMapFst_of_ne hxa, glueBack, if_neg]
    intro h
    exact rot_symm_inv_notMem hne (h ▸ hx)

include hne in
private theorem cornerMapFst_injOn : Set.InjOn (G.cornerMapFst a) (G.vertexOf a) :=
  fun x hx y hy h => by
    rw [← glueBack_cornerMapFst hne hx, ← glueBack_cornerMapFst hne hy, h]

include hne in
private theorem map_cornerMapFst_inj {x y x' y' : H} (hx : x ∈ G.vertexOf a)
    (hy : y ∈ G.vertexOf a) (hx' : x' ∈ G.vertexOf a) (hy' : y' ∈ G.vertexOf a)
    (h : s(G.cornerMapFst a x, G.cornerMapFst a y) = s(G.cornerMapFst a x', G.cornerMapFst a y')) :
    s(x, y) = s(x', y') := by
  have hi := cornerMapFst_injOn hne
  rw [Sym2.eq_iff] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hi hx hx' h1, hi hy hy' h2⟩
  · exact Or.inr ⟨hi hx hy' h1, hi hy hx' h2⟩

/-- `κ_a` maps the side `{a, σ⁻¹ a}` of `a` to the diagonal `γ_e`. -/
private theorem map_cornerSide_eq (h2 : 2 ≤ (G.vertexOf a).card) :
    s(G.cornerMapFst a a, G.cornerMapFst a (G.rot.symm a)) = G.cornerGlueDiagonal a := by
  have hne' : G.rot.symm a ≠ a := by
    have := RotationSystem.rot_symm_pow_ne_self (R := G.toRotationSystem) (x := a) (k := 1)
      one_pos (by omega)
    rwa [pow_one] at this
  rw [RotationSystem.cornerMapFst_self, RotationSystem.cornerMapFst_of_ne hne',
    RotationSystem.cornerGlueDiagonal, Sym2.eq_swap]

include hne in
private theorem map_eq_cornerGlueDiagonal_iff (h2 : 2 ≤ (G.vertexOf a).card) {x y : H}
    (hx : x ∈ G.vertexOf a) (hy : y ∈ G.vertexOf a) :
    s(G.cornerMapFst a x, G.cornerMapFst a y) = G.cornerGlueDiagonal a ↔
      s(x, y) = G.cornerSide a := by
  rw [← map_cornerSide_eq h2, RotationSystem.cornerSide]
  refine ⟨map_cornerMapFst_inj hne hx hy (G.self_mem_vertexOf a) (G.rot_symm_mem_vertexOf a),
    fun h => ?_⟩
  rw [Sym2.eq_iff] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Sym2.eq_swap

include hinv hne in
/-- A dart of `v(a)` whose image under `κ_a` lies on the side of `v(ā)` is sent to an end of
`γ_e`. -/
private theorem cornerMapFst_mem_glueSide_inv {x : H} (hx : x ∈ G.vertexOf a)
    (h : G.cornerMapFst a x ∈ glueSide G (G.inv a)) :
    G.cornerMapFst a x = G.rot.symm a ∨ G.cornerMapFst a x = G.rot.symm (G.inv a) := by
  unfold glueSide at h
  rw [hinv a] at h
  unfold RotationSystem.cornerMapFst at h ⊢
  split_ifs at h ⊢ with hxa
  · exact Or.inr rfl
  · rcases mem_insert.1 h with h | h
    · exact Or.inl h
    · exact absurd h (notMem_inv_of_mem_end hne hx)

omit [Fintype H] [DecidableEq H] in
private theorem eq_of_mem_pair {p q x y : H} (hpq : p ≠ q) (hxy : x ≠ y) (hx : x = p ∨ x = q)
    (hy : y = p ∨ y = q) : s(x, y) = s(p, q) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl hxy

omit [Fintype H] in
include hinv in
private theorem cornerMapSnd_eq_cornerMapFst_inv :
    G.cornerMapSnd a = G.cornerMapFst (G.inv a) := by
  funext x
  unfold RotationSystem.cornerMapSnd RotationSystem.cornerMapFst
  rw [hinv a]

include hinv hne in
/-- **Membership in a glued triangulation.** For darts `x ≠ y` of `v(a)`, the pair
`{κ_a x, κ_a y}` lies in `κ_a(D₁) ∪ κ_ā(D₂) ∪ {γ_e}` exactly when `{x, y} ∈ D₁` or `{x, y}` is the
side of `a`. -/
private theorem mk_mem_cornerGlue_iff (h2 : 2 ≤ (G.vertexOf a).card)
    {D₁ D₂ : Finset (Sym2 H)} (hD₁ : G.IsCornerTriangulation (G.vertexOf a) D₁)
    (hD₂ : G.IsCornerTriangulation (G.vertexOf (G.inv a)) D₂) {x y : H}
    (hx : x ∈ G.vertexOf a) (hy : y ∈ G.vertexOf a) (hxy : x ≠ y) :
    s(G.cornerMapFst a x, G.cornerMapFst a y) ∈ G.cornerGlue a D₁ D₂ ↔
      s(x, y) ∈ D₁ ∨ s(x, y) = G.cornerSide a := by
  have hne' : G.vertexOf (G.inv a) ≠ G.vertexOf (G.inv (G.inv a)) := by
    rw [hinv a]
    exact hne.symm
  have hpq : G.rot.symm a ≠ G.rot.symm (G.inv a) := fun h =>
    rot_symm_inv_notMem hne (h ▸ G.rot_symm_mem_vertexOf a)
  have hκ := cornerMapFst_injOn hne
  rw [RotationSystem.mem_cornerGlue, map_eq_cornerGlueDiagonal_iff hne h2 hx hy]
  constructor
  · rintro (h | ⟨f, hf, hfe⟩ | ⟨f, hf, hfe⟩)
    · exact Or.inr h
    · left
      induction f using Sym2.ind with | _ u v => ?_
      obtain ⟨hu, hv⟩ : u ∈ G.vertexOf a ∧ v ∈ G.vertexOf a :=
        ⟨(hD₁.1 _ hf).2 u (Sym2.mem_mk_left _ _), (hD₁.1 _ hf).2 v (Sym2.mem_mk_right _ _)⟩
      rw [Sym2.map_mk] at hfe
      rw [← map_cornerMapFst_inj hne hu hv hx hy hfe]
      exact hf
    · right
      induction f using Sym2.ind with | _ u v => ?_
      obtain ⟨hu, hv⟩ : u ∈ G.vertexOf (G.inv a) ∧ v ∈ G.vertexOf (G.inv a) :=
        ⟨(hD₂.1 _ hf).2 u (Sym2.mem_mk_left _ _), (hD₂.1 _ hf).2 v (Sym2.mem_mk_right _ _)⟩
      rw [Sym2.map_mk, cornerMapSnd_eq_cornerMapFst_inv hinv] at hfe
      have hmem : ∀ z ∈ s(G.cornerMapFst a x, G.cornerMapFst a y),
          z ∈ glueSide G (G.inv a) := by
        rw [← hfe]
        intro z hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · exact cornerMapFst_mem_glueSide hu
        · exact cornerMapFst_mem_glueSide hv
      rw [← map_eq_cornerGlueDiagonal_iff hne h2 hx hy, RotationSystem.cornerGlueDiagonal]
      exact eq_of_mem_pair hpq (fun h => hxy (hκ hx hy h))
        (cornerMapFst_mem_glueSide_inv hinv hne hx (hmem _ (Sym2.mem_mk_left _ _)))
        (cornerMapFst_mem_glueSide_inv hinv hne hy (hmem _ (Sym2.mem_mk_right _ _)))
  · rintro (h | h)
    · exact Or.inr (Or.inl ⟨_, h, Sym2.map_mk _ _ _⟩)
    · exact Or.inl h

/-- A triangle at `v(a)` is sent by `κ_a` into the side of `a`, and not into the side of `ā`. -/
private theorem image_cornerMapFst_subset {τ : Finset H} (hτ : τ ⊆ G.vertexOf a) :
    τ.image (G.cornerMapFst a) ⊆ glueSide G a := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
  exact cornerMapFst_mem_glueSide (hτ hx)

include hinv hne in
private theorem not_image_cornerMapFst_subset_inv {τ : Finset H} (hτ : τ ⊆ G.vertexOf a)
    (h3 : τ.card = 3) : ¬τ.image (G.cornerMapFst a) ⊆ glueSide G (G.inv a) := by
  intro h
  have key : ∀ x ∈ τ, x ≠ a → x = G.rot.symm a := by
    intro x hx hxa
    have hm := h (mem_image_of_mem _ hx)
    rcases cornerMapFst_mem_glueSide_inv hinv hne (hτ hx) hm with h1 | h1
    · rwa [RotationSystem.cornerMapFst_of_ne hxa] at h1
    · rw [RotationSystem.cornerMapFst_of_ne hxa] at h1
      exact absurd (h1 ▸ hτ hx) (rot_symm_inv_notMem hne)
  have hsub : τ ⊆ {a, G.rot.symm a} := by
    intro x hx
    by_cases hxa : x = a
    · rw [hxa]
      exact mem_insert_self _ _
    · rw [key x hx hxa]
      exact mem_insert_of_mem (mem_singleton_self _)
  have := card_le_card hsub
  have := card_le_two (a := a) (b := G.rot.symm a)
  omega

include hne in
/-- If `γ_e` is a pair of darts of `κ_a(τ)`, then the side of `a` is a pair of darts of `τ`. -/
private theorem cornerSide_mem_sym2_of_cornerGlueDiagonal_mem {τ : Finset H}
    (hτ : τ ⊆ G.vertexOf a) (h : G.cornerGlueDiagonal a ∈ (τ.image (G.cornerMapFst a)).sym2) :
    G.cornerSide a ∈ τ.sym2 := by
  rw [RotationSystem.cornerGlueDiagonal, mk_mem_sym2_iff] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨x, hx, hxe⟩ := mem_image.1 h1
  obtain ⟨y, hy, hye⟩ := mem_image.1 h2
  rw [RotationSystem.cornerSide, mk_mem_sym2_iff]
  have hya : y = a := by
    by_contra hya
    rw [RotationSystem.cornerMapFst_of_ne hya] at hye
    exact rot_symm_inv_notMem hne (hye ▸ hτ hy)
  have hxa : x ≠ a := by
    intro hxa'
    rw [hxa', RotationSystem.cornerMapFst_self] at hxe
    exact rot_symm_inv_notMem hne (hxe ▸ G.rot_symm_mem_vertexOf a)
  rw [RotationSystem.cornerMapFst_of_ne hxa] at hxe
  exact ⟨hya ▸ hy, hxe ▸ hx⟩

include hinv hne in
/-- A pair of distinct darts lying on both sides is `γ_e`. -/
private theorem eq_cornerGlueDiagonal_of_subset {e : Sym2 H} (he : ¬e.IsDiag)
    (h1 : ∀ z ∈ e, z ∈ glueSide G a) (h2 : ∀ z ∈ e, z ∈ glueSide G (G.inv a)) :
    e = G.cornerGlueDiagonal a := by
  have hpq : G.rot.symm a ≠ G.rot.symm (G.inv a) := fun h =>
    rot_symm_inv_notMem hne (h ▸ G.rot_symm_mem_vertexOf a)
  have hz : ∀ z ∈ e, z = G.rot.symm a ∨ z = G.rot.symm (G.inv a) := by
    intro z hz
    have hz1 := h1 z hz
    have hz2 := h2 z hz
    unfold glueSide at hz1 hz2
    rw [hinv a] at hz2
    rcases mem_insert.1 hz1 with h | h
    · exact Or.inr h
    · rcases mem_insert.1 hz2 with h' | h'
      · exact Or.inl h'
      · exact absurd h' (notMem_inv_of_mem_end hne h)
  induction e using Sym2.ind with | _ u v => ?_
  have huv : u ≠ v := fun h => he (Sym2.mk_isDiag_iff.2 h)
  rw [RotationSystem.cornerGlueDiagonal]
  exact eq_of_mem_pair hpq huv (hz u (Sym2.mem_mk_left _ _)) (hz v (Sym2.mem_mk_right _ _))

end Ends

/-! ### The contraction away from the merged vertex -/

section Contraction

variable {G : PlabicData H b} {d : H} {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}

omit [Fintype H] in
/-- A set of darts of the contraction is recovered from its image in `H`. -/
private theorem subtype_map_subtype {s : Finset (({d, G.inv d} : Set H)ᶜ : Set H)} :
    (s.map (Embedding.subtype _)).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) = s := by
  ext z
  rw [mem_subtype]
  exact mem_map' (Embedding.subtype _)

section Away

variable (he : G.IsContractibleEdge d)

include he

omit he in
private theorem coe_rot_of_notMem {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    ((G.contractEdge d hleg).rot y : H) = G.rot y :=
  coe_contractEdge_rot_of_mem (mem_compl_pair_of_notMem (rot_notMem_of_notMem hy))

private theorem map_vertexOf_of_notMem {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    ((G.contractEdge d hleg).vertexOf y).map (Embedding.subtype _) = G.vertexOf y :=
  map_vertexOf_contractEdge_of_notMem he.not_sameCycle hy

private theorem notMem_of_mem_vertexOf {y z : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d))
    (hz : z ∈ (G.contractEdge d hleg).vertexOf y) :
    (z : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  have h : (z : H) ∈ G.vertexOf y := by
    rw [← map_vertexOf_of_notMem (hleg := hleg) he hy]
    exact mem_map_of_mem _ hz
  rwa [mem_union_vertexOf_iff_of_vertexOf_eq (G.vertexOf_eq_of_mem h)]

private theorem coe_rot_symm_of_notMem {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    ((G.contractEdge d hleg).rot.symm y : H) = G.rot.symm y := by
  have h := coe_rot_of_notMem (hleg := hleg)
    (notMem_of_mem_vertexOf (hleg := hleg) he hy ((G.contractEdge d hleg).rot_symm_mem_vertexOf y))
  rw [Equiv.apply_symm_apply] at h
  rw [h, Equiv.symm_apply_apply]

private theorem coe_rot_symm_pow_of_notMem {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) (n : ℕ) :
    (((G.contractEdge d hleg).rot.symm ^ n) y : H) = (G.rot.symm ^ n) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm : ((G.contractEdge d hleg).rot.symm ^ n) y ∈ (G.contractEdge d hleg).vertexOf y :=
      RotationSystem.rot_symm_pow_apply_mem_vertexOf y n
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [coe_rot_symm_of_notMem (hleg := hleg) he (notMem_of_mem_vertexOf (hleg := hleg) he hy hm),
      ih]

private theorem cornerSide_eq_of_notMem {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    G.cornerSide (y : H) = ((G.contractEdge d hleg).cornerSide y).map Subtype.val := by
  rw [RotationSystem.cornerSide, RotationSystem.cornerSide, Sym2.map_mk,
    coe_rot_symm_of_notMem (hleg := hleg) he hy]

private theorem isCornerLabelling_of_notMem {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) {m : ℕ}
    {l : ZMod m → (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hl : (G.contractEdge d hleg).IsCornerLabelling ((G.contractEdge d hleg).vertexOf y) l) :
    G.IsCornerLabelling (G.vertexOf y) (fun i => (l i : H)) := by
  refine ⟨⟨fun i _ => ?_, fun i _ j _ h => hl.injective (Subtype.ext h), fun p hp => ?_⟩,
    fun i => ?_⟩
  · rw [Finset.mem_coe, ← map_vertexOf_of_notMem (hleg := hleg) he hy]
    exact mem_map_of_mem _ (hl.mem i)
  · rw [Finset.mem_coe, ← map_vertexOf_of_notMem (hleg := hleg) he hy, mem_map] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    obtain ⟨i, rfl⟩ := hl.exists_eq hz
    exact ⟨i, trivial, rfl⟩
  · simp only
    rw [hl.2, coe_rot_symm_of_notMem (hleg := hleg) he
      (notMem_of_mem_vertexOf (hleg := hleg) he hy (hl.mem i))]

omit he [Fintype H] in
private theorem cornerPullback_map' {m : ℕ} [NeZero m]
    (l : ZMod m → (({d, G.inv d} : Set H)ᶜ : Set H))
    (E : Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H))) :
    RotationSystem.cornerPullback (fun i => (l i : H)) (E.map (Embedding.subtype _).sym2Map) =
      RotationSystem.cornerPullback l E := by
  ext e
  rw [RotationSystem.mem_cornerPullback, RotationSystem.mem_cornerPullback]
  have : e.map (fun i => (l i : H)) = (Embedding.subtype _).sym2Map (e.map l) := by
    rw [Embedding.sym2Map_apply, Sym2.map_map]
    rfl
  rw [this, mem_map' (Embedding.subtype _).sym2Map]

/-- Corner triangulations of a crossing of the contraction away from the merged vertex. -/
private theorem isCornerTriangulation_iff_of_notMem {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d))
    {E : Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H))} :
    (G.contractEdge d hleg).IsCornerTriangulation ((G.contractEdge d hleg).vertexOf y) E ↔
      G.IsCornerTriangulation (G.vertexOf y) (E.map (Embedding.subtype _).sym2Map) := by
  constructor
  · rintro ⟨hE, m, _, l, hl, hT⟩
    refine ⟨fun e he' => ?_, m, inferInstance, fun i => (l i : H),
      isCornerLabelling_of_notMem (hleg := hleg) he hy hl, ?_⟩
    · obtain ⟨e', he'', rfl⟩ := mem_map.1 he'
      refine ⟨?_, fun x hx => ?_⟩
      · rw [Embedding.sym2Map_apply, Sym2.isDiag_map (Embedding.injective _)]
        exact (hE e' he'').1
      · rw [Embedding.sym2Map_apply, Sym2.mem_map] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [← map_vertexOf_of_notMem (hleg := hleg) he hy]
        exact mem_map_of_mem _ ((hE e' he'').2 z hz)
    · rwa [cornerPullback_map']
  · rintro ⟨hE, m, _, l, hl, hT⟩
    refine ⟨fun e he' => ?_, ?_⟩
    · have h := hE _ (mem_map_of_mem (Embedding.subtype _).sym2Map he')
      refine ⟨?_, fun x hx => ?_⟩
      · have h1 := h.1
        rwa [Embedding.sym2Map_apply, Sym2.isDiag_map (Embedding.injective _)] at h1
      · have h2 := h.2 x (by rw [Embedding.sym2Map_apply]; exact Sym2.mem_map.2 ⟨x, hx, rfl⟩)
        rw [← map_vertexOf_of_notMem (hleg := hleg) he hy, mem_map] at h2
        obtain ⟨z, hz, hzx⟩ := h2
        rwa [← Subtype.ext hzx]
    · set n := ((G.contractEdge d hleg).vertexOf y).card
      have hn : 0 < n := card_pos.2 ⟨y, (G.contractEdge d hleg).self_mem_vertexOf y⟩
      haveI : NeZero n := ⟨by omega⟩
      have hl' := RotationSystem.isCornerLabelling_rot_symm_pow
        (R := (G.contractEdge d hleg).toRotationSystem) y rfl
      refine ⟨n, inferInstance, _, hl', ?_⟩
      have := (show G.IsCornerTriangulation (G.vertexOf y) (E.map (Embedding.subtype _).sym2Map)
        from ⟨hE, m, inferInstance, l, hl, hT⟩).isTriangulation_cornerPullback
        (isCornerLabelling_of_notMem (hleg := hleg) he hy hl')
      rwa [cornerPullback_map'] at this

/-- Corner triangles of a crossing of the contraction away from the merged vertex. -/
private theorem isCornerTriangle_iff_of_notMem {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d))
    {E : Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H))}
    {τ : Finset (({d, G.inv d} : Set H)ᶜ : Set H)} :
    (G.contractEdge d hleg).IsCornerTriangle ((G.contractEdge d hleg).vertexOf y) E τ ↔
      G.IsCornerTriangle (G.vertexOf y) (E.map (Embedding.subtype _).sym2Map)
        (τ.map (Embedding.subtype _)) := by
  have hseg : ∀ u v : (({d, G.inv d} : Set H)ᶜ : Set H),
      s((u : H), (v : H)) ∈ G.cornerSegments (G.vertexOf y)
        (E.map (Embedding.subtype _).sym2Map) ↔
      s(u, v) ∈ (G.contractEdge d hleg).cornerSegments ((G.contractEdge d hleg).vertexOf y) E := by
    intro u v
    rw [RotationSystem.mem_cornerSegments, RotationSystem.mem_cornerSegments]
    have e1 : s((u : H), (v : H)) = (Embedding.subtype _).sym2Map s(u, v) := rfl
    rw [e1, mem_map' (Embedding.subtype _).sym2Map]
    refine or_congr Iff.rfl ⟨fun ⟨a, ha, hae⟩ => ?_, fun ⟨a, ha, hae⟩ => ?_⟩
    · rw [← map_vertexOf_of_notMem (hleg := hleg) he hy, mem_map] at ha
      obtain ⟨a', ha', rfl⟩ := ha
      refine ⟨a', ha', ?_⟩
      rw [Embedding.coe_subtype, cornerSide_eq_of_notMem (hleg := hleg) he
        (notMem_of_mem_vertexOf (hleg := hleg) he hy ha')]
        at hae
      exact Sym2.map.injective Subtype.val_injective hae
    · refine ⟨a, ?_, ?_⟩
      · rw [← map_vertexOf_of_notMem (hleg := hleg) he hy]
        exact mem_map_of_mem _ ha
      · rw [cornerSide_eq_of_notMem (hleg := hleg) he
          (notMem_of_mem_vertexOf (hleg := hleg) he hy ha), hae]
        rfl
  constructor
  · rintro ⟨hsub, hcard, hs⟩
    refine ⟨?_, (card_map _).trans hcard, fun u hu v hv huv => ?_⟩
    · rw [← map_vertexOf_of_notMem (hleg := hleg) he hy]
      exact map_subset_map.2 hsub
    · obtain ⟨u', hu', rfl⟩ := mem_map.1 hu
      obtain ⟨v', hv', rfl⟩ := mem_map.1 hv
      exact (hseg u' v').2 (hs u' hu' v' hv' fun h => huv (by rw [h]))
  · rintro ⟨hsub, hcard, hs⟩
    refine ⟨?_, (card_map _).symm.trans hcard, fun u hu v hv huv => ?_⟩
    · rw [← map_vertexOf_of_notMem (hleg := hleg) he hy] at hsub
      exact map_subset_map.1 hsub
    · exact (hseg u v).1 (hs _ (mem_map_of_mem _ hu) _ (mem_map_of_mem _ hv)
        fun h => huv (Subtype.ext h))

/-- Clockwise successors at a crossing of the contraction away from the merged vertex. -/
private theorem cornerNext_eq_of_notMem {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d))
    (τ : Finset (({d, G.inv d} : Set H)ᶜ : Set H)) :
    G.cornerNext (τ.map (Embedding.subtype _)) (y : H) =
      (G.contractEdge d hleg).cornerNext τ y := by
  have hP : ∀ k : ℕ, (0 < k ∧ (G.rot.symm ^ k) (y : H) ∈ τ.map (Embedding.subtype _) ∧
      (G.rot.symm ^ k) (y : H) ≠ y) ↔ (0 < k ∧ ((G.contractEdge d hleg).rot.symm ^ k) y ∈ τ ∧
        ((G.contractEdge d hleg).rot.symm ^ k) y ≠ y) := by
    intro k
    have hm : ∀ z : (({d, G.inv d} : Set H)ᶜ : Set H),
        (z : H) ∈ τ.map (Embedding.subtype _) ↔ z ∈ τ := fun z => mem_map' _
    rw [← coe_rot_symm_pow_of_notMem (hleg := hleg) he hy k, hm]
    exact and_congr Iff.rfl (and_congr Iff.rfl (by rw [Ne, Ne, Subtype.ext_iff]))
  classical
  unfold RotationSystem.cornerNext
  by_cases h' : ∃ k : ℕ, 0 < k ∧ ((G.contractEdge d hleg).rot.symm ^ k) y ∈ τ ∧
      ((G.contractEdge d hleg).rot.symm ^ k) y ≠ y
  · have h : ∃ k : ℕ, 0 < k ∧ (G.rot.symm ^ k) (y : H) ∈ τ.map (Embedding.subtype _) ∧
        (G.rot.symm ^ k) (y : H) ≠ y := let ⟨k, hk⟩ := h'; ⟨k, (hP k).2 hk⟩
    rw [dif_pos h, dif_pos h']
    have e : Nat.find h = Nat.find h' :=
      le_antisymm (Nat.find_min' h ((hP _).2 (Nat.find_spec h')))
        (Nat.find_min' h' ((hP _).1 (Nat.find_spec h)))
    rw [e, coe_rot_symm_pow_of_notMem (hleg := hleg) he hy]
  · have h : ¬∃ k : ℕ, 0 < k ∧ (G.rot.symm ^ k) (y : H) ∈ τ.map (Embedding.subtype _) ∧
        (G.rot.symm ^ k) (y : H) ≠ y := fun ⟨k, hk⟩ => h' ⟨k, (hP k).1 hk⟩
    rw [dif_neg h, dif_neg h']

/-- Crossings of the contraction away from the merged vertex are those of `G`. -/
private theorem isCrossing_iff_of_notMem {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    (G.contractEdge d hleg).IsCrossing ((G.contractEdge d hleg).vertexOf y) ↔
      G.IsCrossing (G.vertexOf y) := by
  unfold IsCrossing
  rw [(G.contractEdge d hleg).vertexOf_mem_internalVertices, G.vertexOf_mem_internalVertices,
    isBoundaryVertex_vertexOf_contractEdge_iff he, ← map_vertexOf_of_notMem (hleg := hleg) he hy,
    card_map]
  refine and_congr Iff.rfl (and_congr ⟨fun h p hp => ?_, fun h z hz => ?_⟩ Iff.rfl)
  · obtain ⟨z, hz, rfl⟩ := mem_map.1 hp
    rw [Embedding.coe_subtype, ← contractEdge_colour (hleg := hleg)]
    exact h z hz
  · rw [contractEdge_colour]
    exact h _ (mem_map_of_mem _ hz)

end Away

/-! ### A contraction between two crossings -/

section White

variable (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) (hw : G.colour d = .white)
  (hp : 3 ≤ (G.vertexOf d).card) (hq : 3 ≤ (G.vertexOf (G.inv d)).card)

include he in
private theorem notMem_inv_vertexOf_of_mem {x : H} (hx : x ∈ G.vertexOf d) :
    x ∉ G.vertexOf (G.inv d) := fun h =>
  he.vertexOf_ne ((G.vertexOf_eq_of_mem hx).symm.trans (G.vertexOf_eq_of_mem h))

include he in
private theorem not_isBoundaryVertex_of_mem {x : H}
    (hx : x ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) : ¬G.IsBoundaryVertex (G.vertexOf x) := by
  rcases mem_union.1 hx with h | h
  · rw [G.vertexOf_eq_of_mem h]; exact he.not_isBoundaryVertex
  · rw [G.vertexOf_eq_of_mem h]; exact he.not_isBoundaryVertex_inv

include hG he hw hp hq in
/-- Both ends of the edge are crossings. -/
private theorem isCrossing_vertexOf_of_mem {x : H}
    (hx : x ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) : G.IsCrossing (G.vertexOf x) := by
  have hwh : ∀ z ∈ G.vertexOf d ∪ G.vertexOf (G.inv d), G.colour z = .white :=
    fun z hz => (colour_eq_of_mem_union hG he hz).trans hw
  rcases mem_union.1 hx with h | h
  · rw [G.vertexOf_eq_of_mem h]
    exact ⟨he.mem_internalVertices, fun z hz => hwh z (mem_union_left _ hz), hp⟩
  · rw [G.vertexOf_eq_of_mem h]
    exact ⟨he.inv_mem_internalVertices, fun z hz => hwh z (mem_union_right _ hz), hq⟩

include he hp hq in
private theorem three_le_card_mergedVertex : 3 ≤ (G.mergedVertex d).card := by
  have hdisj : Disjoint (G.vertexOf d) (G.vertexOf (G.inv d)) :=
    disjoint_left.2 fun x hx => notMem_inv_vertexOf_of_mem he hx
  have h1 := card_union_of_disjoint hdisj
  have h2 := le_card_sdiff ({d, G.inv d} : Finset H) (G.vertexOf d ∪ G.vertexOf (G.inv d))
  have h3 := card_le_two (a := d) (b := G.inv d)
  unfold mergedVertex
  omega

include he in
/-- The vertex of the contraction at a dart of `v(d) ∪ v(d̄)` is the merged vertex. -/
private theorem vertexOf_eq_merged {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    (G.contractEdge d hleg).vertexOf y =
      (G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) := by
  rw [← map_vertexOf_contractEdge_of_mem he.not_sameCycle hy, subtype_map_subtype]

include hG he hw hp hq in
/-- The merged vertex is a crossing of the contraction. -/
private theorem isCrossing_vertexOf_merged {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (y : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    (G.contractEdge d hleg).IsCrossing ((G.contractEdge d hleg).vertexOf y) := by
  have hmap := map_vertexOf_contractEdge_of_mem (hleg := hleg) he.not_sameCycle hy
  refine ⟨(G.contractEdge d hleg).vertexOf_mem_internalVertices.2 ?_, fun z hz => ?_, ?_⟩
  · rw [isBoundaryVertex_vertexOf_contractEdge_iff he]
    exact not_isBoundaryVertex_of_mem he hy
  · have hz' : (z : H) ∈ G.mergedVertex d := by
      rw [← hmap]
      exact mem_map_of_mem _ hz
    rw [contractEdge_colour]
    exact (colour_eq_of_mem_union hG he (mem_union.2 (mem_mergedVertex.1 hz').1)).trans hw
  · rw [← card_map (Embedding.subtype _), hmap]
    exact three_le_card_mergedVertex he hp hq

include hG he hw hp hq in
private theorem isCrossing_vertexOf_iff (y : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).IsCrossing ((G.contractEdge d hleg).vertexOf y) ↔
      G.IsCrossing (G.vertexOf y) := by
  by_cases hy : (y : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
  · exact iff_of_true (isCrossing_vertexOf_merged hG he hw hp hq hy)
      (isCrossing_vertexOf_of_mem hG he hw hp hq hy)
  · exact isCrossing_iff_of_notMem he hy

private theorem isLeg_contractEdge_iff (y : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).IsLeg y ↔ G.IsLeg y :=
  ⟨fun ⟨i, hi⟩ => ⟨i, by rw [← hi]; rfl⟩,
    fun ⟨i, hi⟩ => ⟨i, Subtype.ext (by rw [coe_contractEdge_leg, hi])⟩⟩

include hG he hw hp hq in
/-- Initial darts of the contraction are the initial darts of `G` other than `d`, `d̄`. -/
private theorem isInitial_contractEdge_iff (y : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).IsInitial y ↔ G.IsInitial y := by
  unfold IsInitial
  rw [mem_contractEdge_bdry, isCrossing_vertexOf_iff hG he hw hp hq, isLeg_contractEdge_iff]

include hG he hw hp hq in
/-- Terminal darts of the contraction are the terminal darts of `G` other than `d`, `d̄`. -/
private theorem isTerminal_contractEdge_iff (t : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).IsTerminal t ↔ G.IsTerminal t := by
  unfold IsTerminal
  have hi : ((G.contractEdge d hleg).inv t : H) = G.inv t :=
    coe_contractEdge_inv hG.inv_involutive t
  rw [mem_contractEdge_bdry, isCrossing_vertexOf_iff hG he hw hp hq,
    isBoundaryVertex_vertexOf_contractEdge_iff he, hi]

include hG he hw hp hq in
/-- The trip map sends `d` and `d̄` back into `H \ {d, d̄}`. -/
private theorem tripMap_mem_of_notMem {z : H} (hz : z ∉ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    G.tripMap z ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
  have hinv := hG.inv_involutive
  have hiz : G.inv z ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
    inv_mem_union_of_notMem_compl_pair hinv hz
  have hc := isCrossing_vertexOf_of_mem hG he hw hp hq hiz
  have hT : G.tripMap z = G.rot.symm (G.inv z) := by
    rw [tripMap_apply, turn_of_white (not_isBoundaryVertex_of_mem he hiz)
      ((colour_eq_of_mem_union hG he hiz).trans hw)]
  have hne : G.rot.symm (G.inv z) ≠ G.inv z := by
    have := RotationSystem.rot_symm_pow_ne_self (R := G.toRotationSystem) (x := G.inv z)
      (k := 1) one_pos (by have := hc.three_le_card; omega)
    rwa [pow_one] at this
  rw [hT, mem_compl_pair_iff]
  rcases eq_or_eq_of_notMem_compl_pair hz with h | h
  · rw [h] at hne ⊢
    refine ⟨fun h' => ?_, hne⟩
    have hm : G.rot.symm (G.inv d) ∈ G.vertexOf (G.inv d) := G.rot_symm_mem_vertexOf _
    rw [h'] at hm
    exact notMem_inv_vertexOf_of_mem he (G.self_mem_vertexOf d) hm
  · rw [h, hinv] at hne ⊢
    refine ⟨hne, fun h' => ?_⟩
    have hm : G.rot.symm d ∈ G.vertexOf d := G.rot_symm_mem_vertexOf _
    rw [h'] at hm
    exact notMem_inv_vertexOf_of_mem he hm (G.self_mem_vertexOf _)

include hG he hw hp hq in
/-- A dart of `H \ {d, d̄}` sent to `d` or `d̄` by the trip map is terminal. -/
private theorem isTerminal_of_tripMap_notMem {z : H}
    (hT : G.tripMap z ∉ (({d, G.inv d} : Set H)ᶜ : Set H)) : G.IsTerminal z := by
  have hm : G.tripMap z ∈ G.vertexOf (G.inv z) := turn_mem_vertexOf _
  have hu := mem_union_of_notMem_compl_pair hT
  rw [mem_union_vertexOf_iff_of_vertexOf_eq (G.vertexOf_eq_of_mem hm)] at hu
  refine ⟨fun hB => not_isBoundaryVertex_of_mem he hu
    (G.isBoundaryVertex_vertexOf_of_mem (hG.inv_mem_bdry _ hB)), ?_⟩
  exact Or.inl (isCrossing_vertexOf_of_mem hG he hw hp hq hu)

include hG he hw hp hq in
/-- **Chains of a white contraction.** The chain of the contraction from an initial dart ends where
the chain of `G` does. -/
private theorem coe_chainEnd_contractEdge {c : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hc : (G.contractEdge d (he.leg_mem hG)).IsInitial c) :
    ((G.contractEdge d (he.leg_mem hG)).chainEnd c : H) = G.chainEnd c := by
  have hQ := hG.contractEdge (hleg := he.leg_mem hG) he
  have hinv := hG.inv_involutive
  set T := hG.tripEquiv
  have hT1 : ∀ y : (({d, G.inv d} : Set H)ᶜ : Set H), T y ∈ (({d, G.inv d} : Set H)ᶜ : Set H) →
      ∀ j, j < firstReturnTime T _ y → j = 0 := by
    intro y hy j hj
    by_contra h0
    have := pow_apply_notMem_of_lt_firstReturnTime (π := T) (y := y) (j := 1) one_pos
      (by omega)
    rw [pow_one] at this
    exact this hy
  have hterm : ∀ y : (({d, G.inv d} : Set H)ᶜ : Set H),
      (G.contractEdge d (he.leg_mem hG)).IsTerminal y ↔
        ∃ j < firstReturnTime T _ y, G.IsTerminal ((T ^ j) y) := by
    intro y
    rw [isTerminal_contractEdge_iff hG he hw hp hq]
    refine ⟨fun h => ⟨0, firstReturnTime_pos y, h⟩, fun ⟨j, hj, h⟩ => ?_⟩
    by_cases hTy : T y ∈ (({d, G.inv d} : Set H)ᶜ : Set H)
    · obtain rfl := hT1 y hTy j hj
      exact h
    · exact isTerminal_of_tripMap_notMem hG he hw hp hq hTy
  have harr : ∀ y : (({d, G.inv d} : Set H)ᶜ : Set H), ∀ j < firstReturnTime T _ y,
      G.IsTerminal ((T ^ j) y) → (∀ i < j, ¬G.IsTerminal ((T ^ i) y)) →
        G.inv ((T ^ j) y) = (G.contractEdge d (he.leg_mem hG)).inv y := by
    intro y j hj ht hmin
    rw [coe_contractEdge_inv hinv]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    exfalso
    by_cases hTy : T y ∈ (({d, G.inv d} : Set H)ᶜ : Set H)
    · exact absurd (hT1 y hTy j hj) (by omega)
    · by_cases hj1 : j = 1
      · subst hj1
        exact hmin 0 one_pos (isTerminal_of_tripMap_notMem hG he hw hp hq hTy)
      · have h1 := pow_apply_notMem_of_lt_firstReturnTime (π := T) (y := y) (j := j - 1)
          (by omega) (by omega)
        have h2 := tripMap_mem_of_notMem hG he hw hp hq h1
        have h3 := pow_apply_notMem_of_lt_firstReturnTime (π := T) (y := y) hj0 hj
        rw [← IsPlabicGraph.tripEquiv_apply hG, ← Equiv.Perm.mul_apply, ← pow_succ',
          Nat.sub_add_cancel hj0] at h2
        exact h3 h2
  have key := inv_chainEnd_eq_of_firstReturn' hG hQ
    (coe_contractEdge_tripMap (hleg := he.leg_mem hG) hG he) hterm harr hc
  rw [coe_contractEdge_inv hinv] at key
  exact (G.inv.injective key).symm

include hG he hw hp hq in
/-- An initial dart of `G` is followed, within at most one step of the trip map, by an initial dart
of `G` other than `d`, `d̄`. -/
private theorem exists_isInitial_mem {e : H} (he' : G.IsInitial e) :
    ∃ e' ∈ (({d, G.inv d} : Set H)ᶜ : Set H), G.IsInitial e' ∧ ∃ k : ℕ, G.tripMap^[k] e = e' := by
  by_cases hm : e ∈ (({d, G.inv d} : Set H)ᶜ : Set H)
  · exact ⟨e, hm, he', 0, rfl⟩
  refine ⟨G.tripMap e, tripMap_mem_of_notMem hG he hw hp hq hm, ?_, 1, rfl⟩
  have hiz : G.inv e ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
    inv_mem_union_of_notMem_compl_pair hG.inv_involutive hm
  have hv : G.vertexOf (G.tripMap e) = G.vertexOf (G.inv e) := vertexOf_turn _
  refine ⟨fun hB => not_isBoundaryVertex_of_mem he hiz ?_, Or.inl ?_⟩
  · rw [← hv]
    exact G.isBoundaryVertex_vertexOf_of_mem hB
  · rw [hv]
    exact isCrossing_vertexOf_of_mem hG he hw hp hq hiz

include hG he hw hp hq in
/-- **Trips of a white contraction.** Every trip of `G` contains an initial dart exactly when every
trip of the contraction does. -/
private theorem exists_isInitial_mem_trip_contractEdge_iff :
    (∀ x ∉ G.bdry, ∃ e ∈ G.trip x, G.IsInitial e) ↔
      ∀ y ∉ (G.contractEdge d (he.leg_mem hG)).bdry,
        ∃ e ∈ (G.contractEdge d (he.leg_mem hG)).trip y,
          (G.contractEdge d (he.leg_mem hG)).IsInitial e := by
  set Q := G.contractEdge d (he.leg_mem hG)
  set T := hG.tripEquiv
  have htrip := coe_contractEdge_tripMap (hleg := he.leg_mem hG) hG he
  have hT' : ∀ y, Q.tripMap y = firstReturnPerm T _ y := fun y =>
    Subtype.ext (by rw [htrip, coe_firstReturnPerm])
  have hiter : ∀ (n : ℕ) (y : (({d, G.inv d} : Set H)ᶜ : Set H)),
      Q.tripMap^[n] y = (firstReturnPerm T _ ^ n) y := by
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
  · intro h y hy
    have hy' : (y : H) ∉ G.bdry := mem_contractEdge_bdry.not.1 hy
    obtain ⟨e, ⟨n, hn⟩, hei⟩ := h y hy'
    simp only at hn
    obtain ⟨e', he'Y, he'i, k, hk⟩ := exists_isInitial_mem hG he hw hp hq hei
    have hs : (firstReturnPerm T _).SameCycle y ⟨e', he'Y⟩ :=
      (sameCycle_firstReturnPerm_iff (π := T) (Y := (({d, G.inv d} : Set H)ᶜ : Set H))).2
        ⟨((n + k : ℕ) : ℤ), by
          rw [zpow_natCast, ← tripMap_iterate_eq hG]
          change _ = e'
          rw [← hk, ← hn, ← Function.iterate_add_apply, add_comm]⟩
    obtain ⟨m, hm⟩ := hs.exists_nat_pow_eq
    refine ⟨⟨e', he'Y⟩, ⟨m, ?_⟩, (isInitial_contractEdge_iff hG he hw hp hq _).2 he'i⟩
    change Q.tripMap^[m] y = _
    rw [hiter]
    exact hm
  · intro h x hx
    obtain ⟨y, hyY, hxy⟩ := exists_sameCycle_tripEquiv_mem hG he x
    have hy : (⟨y, hyY⟩ : (({d, G.inv d} : Set H)ᶜ : Set H)) ∉ Q.bdry := by
      rw [mem_contractEdge_bdry]
      exact fun h' => hx ((hB _ _ hxy).2 h')
    obtain ⟨e, ⟨n, hn⟩, hei⟩ := h _ hy
    simp only at hn
    have hs : T.SameCycle y e := by
      rw [← hn, hiter]
      exact (sameCycle_firstReturnPerm_iff (π := T) (Y := (({d, G.inv d} : Set H)ᶜ : Set H))
        (y := ⟨y, hyY⟩)).1 ⟨n, by rw [zpow_natCast]⟩
    obtain ⟨k, hk⟩ := (hxy.trans hs).exists_nat_pow_eq
    refine ⟨e, ⟨k, ?_⟩, (isInitial_contractEdge_iff hG he hw hp hq _).1 hei⟩
    change G.tripMap^[k] x = _
    rw [tripMap_iterate_eq hG]
    exact hk

/-! #### The two ends of the edge -/

include hG he in
private theorem vertexOf_ne_of_end {a : H} (ha : a = d ∨ a = G.inv d) :
    G.vertexOf a ≠ G.vertexOf (G.inv a) := by
  rcases ha with rfl | rfl
  · exact he.vertexOf_ne
  · rw [hG.inv_involutive]; exact he.vertexOf_ne.symm

include hG in
private theorem inv_end {a : H} (ha : a = d ∨ a = G.inv d) : G.inv a = d ∨ G.inv a = G.inv d := by
  rcases ha with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (hG.inv_involutive _)

include hG in
private theorem cornerGlueDiagonal_end {a : H} (ha : a = d ∨ a = G.inv d) :
    G.cornerGlueDiagonal a = G.cornerGlueDiagonal d := by
  rcases ha with rfl | rfl
  · rfl
  · rw [RotationSystem.cornerGlueDiagonal, RotationSystem.cornerGlueDiagonal, hG.inv_involutive,
      Sym2.eq_swap]

include hG in
private theorem cornerGlue_end {a : H} (ha : a = d ∨ a = G.inv d)
    (DP : Finset H → Finset (Sym2 H)) :
    G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))) =
      G.cornerGlue a (DP (G.vertexOf a)) (DP (G.vertexOf (G.inv a))) := by
  have hinv := hG.inv_involutive
  rcases ha with rfl | rfl
  · rfl
  · unfold RotationSystem.cornerGlue
    rw [cornerGlueDiagonal_end hG (Or.inr rfl), cornerMapSnd_eq_cornerMapFst_inv hinv,
      cornerMapSnd_eq_cornerMapFst_inv hinv, hinv, union_comm]

include he in
private theorem vertexOf_end_subset {a : H} (ha : a = d ∨ a = G.inv d) :
    G.vertexOf a ⊆ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  rcases ha with rfl | rfl
  · exact subset_union_left
  · exact subset_union_right

include hG he in
private theorem glueSide_end_subset {a : H} (ha : a = d ∨ a = G.inv d) :
    glueSide G a ⊆ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  intro x hx
  rcases mem_insert.1 hx with rfl | hx
  · exact vertexOf_end_subset he (inv_end hG ha) (G.rot_symm_mem_vertexOf _)
  · exact vertexOf_end_subset he ha hx

include hG he hw hp hq in
private theorem isCrossing_vertexOf_end {a : H} (ha : a = d ∨ a = G.inv d) :
    G.IsCrossing (G.vertexOf a) :=
  isCrossing_vertexOf_of_mem hG he hw hp hq (vertexOf_end_subset he ha (G.self_mem_vertexOf a))

include hG he in
/-- The symbol `y⁺` at a triangle on the side of the end `a` is read at `a`. -/
private theorem glueYPlus_end {a : H} (ha : a = d ∨ a = G.inv d) {τ : Finset H}
    (hτ : τ ⊆ G.vertexOf a) (h3 : τ.card = 3) (e : Sym2 H) :
    glueYPlus G d e (τ.image (G.cornerMapFst a)) =
      glueEndPlus G a e (τ.image (G.cornerMapFst a)) := by
  have hinv := hG.inv_involutive
  have hne := vertexOf_ne_of_end hG he ha
  unfold glueYPlus
  rcases ha with rfl | rfl
  · rw [if_pos (image_cornerMapFst_subset hτ)]
  · rw [if_neg (by have := not_image_cornerMapFst_subset_inv hinv hne hτ h3; rwa [hinv] at this),
      if_pos (image_cornerMapFst_subset hτ)]

include hG he in
/-- The symbol `y⁻` at a triangle on the side of the end `a` is read at `a`. -/
private theorem glueYMinus_end {a : H} (ha : a = d ∨ a = G.inv d) {τ : Finset H}
    (hτ : τ ⊆ G.vertexOf a) (h3 : τ.card = 3) (e : Sym2 H) :
    glueYMinus G d e (τ.image (G.cornerMapFst a)) =
      glueEndMinus G a e (τ.image (G.cornerMapFst a)) := by
  have hinv := hG.inv_involutive
  have hne := vertexOf_ne_of_end hG he ha
  unfold glueYMinus
  rcases ha with rfl | rfl
  · rw [if_pos (image_cornerMapFst_subset hτ)]
  · rw [if_neg (by have := not_image_cornerMapFst_subset_inv hinv hne hτ h3; rwa [hinv] at this),
      if_pos (image_cornerMapFst_subset hτ)]

include hG he in
private theorem not_subset_glueSide_of_notMem {t : Finset H} {z : H} (hz : z ∈ t)
    (hzW : z ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) {a : H} (ha : a = d ∨ a = G.inv d) :
    ¬t ⊆ glueSide G a := fun h => hzW (glueSide_end_subset hG he ha (h hz))

include hG he in
/-- The symbols `y^±` at a triangle away from the merged vertex are kept. -/
private theorem glueY_of_notMem {t : Finset H} {z : H} (hz : z ∈ t)
    (hzW : z ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) (e : Sym2 H) :
    glueYPlus G d e t = yPlus e t ∧ glueYMinus G d e t = yMinus e t := by
  have h1 := not_subset_glueSide_of_notMem hG he hz hzW (Or.inl rfl)
  have h2 := not_subset_glueSide_of_notMem hG he hz hzW (Or.inr rfl)
  unfold glueYPlus glueYMinus
  rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
  exact ⟨rfl, rfl⟩

/-! #### Triangles at the merged vertex -/

section Merged

variable {DP : Finset H → Finset (Sym2 H)}
  {DQ : Finset (({d, G.inv d} : Set H)ᶜ : Set H) → Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H))}

include hG he hw hp hq in
/-- **Triangles at the merged vertex.** The triangles of `D^Q_v` are the images under `κ_a` of
the triangles of `D^P_{v(a)}`, for the two ends `a` of the edge. -/
private theorem isCornerTriangle_merged_iff (hDP : G.IsWhiteDatum DP)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    (t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).IsCornerTriangle
        ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))
        (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))) t ↔
      ∃ a, (a = d ∨ a = G.inv d) ∧ ∃ τ, G.IsCornerTriangle (G.vertexOf a) (DP (G.vertexOf a)) τ ∧
        τ.image (G.cornerMapFst a) = t.map (Embedding.subtype _) := by
  have hinv := hG.inv_involutive
  have hc1 := isCrossing_vertexOf_end hG he hw hp hq (Or.inl rfl)
  have hc2 := isCrossing_vertexOf_end hG he hw hp hq (Or.inr rfl)
  rw [isCornerTriangle_iff_of_image_eq_cornerGlue he.vertexOf_ne hp hq (hDP _ hc1) (hDP _ hc2)
    hglue t, map_eq_image, cornerMapSnd_eq_cornerMapFst_inv hinv]
  constructor
  · rintro (⟨τ, h1, h2⟩ | ⟨τ, h1, h2⟩)
    · exact ⟨d, Or.inl rfl, τ, h1, h2⟩
    · exact ⟨G.inv d, Or.inr rfl, τ, h1, h2⟩
  · rintro ⟨a, ha | ha, τ, h1, h2⟩ <;> subst ha
    · exact Or.inl ⟨τ, h1, h2⟩
    · exact Or.inr ⟨τ, h1, h2⟩

include hG he hp hq in
/-- `κ_a` maps clockwise listings at `v(a)` to clockwise listings of the contraction. -/
private theorem isCornerClockwise_end {a : H} (ha : a = d ∨ a = G.inv d) {x y z : H}
    (hx : x ∈ G.vertexOf a) (hy : y ∈ G.vertexOf a) (hz : z ∈ G.vertexOf a)
    (h : G.IsCornerClockwise x y z) {x' y' z' : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hx' : (x' : H) = G.cornerMapFst a x) (hy' : (y' : H) = G.cornerMapFst a y)
    (hz' : (z' : H) = G.cornerMapFst a z) :
    (G.contractEdge d hleg).IsCornerClockwise x' y' z' := by
  have hinv := hG.inv_involutive
  rcases ha with rfl | rfl
  · exact isCornerClockwise_cornerMapFst he.vertexOf_ne hp hq hx hy hz h hx' hy' hz'
  · rw [← cornerMapSnd_eq_cornerMapFst_inv hinv] at hx' hy' hz'
    exact isCornerClockwise_cornerMapSnd he.vertexOf_ne hp hq hx hy hz h hx' hy' hz'

omit [Fintype H] in
private theorem map_sym2Map_subtype_eq_image
    (E : Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H))) :
    E.map (Embedding.subtype _).sym2Map = E.image (Sym2.map Subtype.val) := by
  rw [map_eq_image]
  rfl

include he in
/-- The white data agree at a crossing away from the merged vertex. -/
private theorem datum_eq_of_notMem
    (hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) = DP x)
    {y : (({d, G.inv d} : Set H)ᶜ : Set H)} (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d))
    (hc : G.IsCrossing (G.vertexOf y)) :
    DP (G.vertexOf y) =
      (DQ ((G.contractEdge d hleg).vertexOf y)).map (Embedding.subtype _).sym2Map := by
  have h1 : G.vertexOf y ≠ G.vertexOf d := fun h =>
    hy (mem_union_left _ (h ▸ G.self_mem_vertexOf _))
  have h2 : G.vertexOf y ≠ G.vertexOf (G.inv d) := fun h =>
    hy (mem_union_right _ (h ▸ G.self_mem_vertexOf _))
  rw [← hrel _ hc h1 h2, map_sym2Map_subtype_eq_image,
    ← map_vertexOf_of_notMem (hleg := hleg) he hy,
    subtype_map_subtype]

include he in
/-- The crossings of the contraction are the merged vertex and the crossings of `G` away from
`v(d) ∪ v(d̄)`. -/
private theorem isCrossing_contractEdge_cases {x : Finset (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hx : (G.contractEdge d hleg).IsCrossing x) :
    x = (G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) ∨
      ∃ y : (({d, G.inv d} : Set H)ᶜ : Set H), x = (G.contractEdge d hleg).vertexOf y ∧
        (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) ∧ G.IsCrossing (G.vertexOf y) := by
  obtain ⟨y, rfl⟩ := (G.contractEdge d hleg).mem_vertices.1
    ((G.contractEdge d hleg).mem_internalVertices.1 hx.1).1
  by_cases hy : (y : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
  · exact Or.inl (vertexOf_eq_merged he hy)
  · exact Or.inr ⟨y, rfl, hy, (isCrossing_iff_of_notMem he hy).1 hx⟩

include hG he hw hp hq in
/-- **Triangles of the white datum of the contraction.** A triangle of `D^Q` lies at the merged
vertex, where it is the image under `κ_a` of a triangle of `D^P_{v(a)}` for an end `a` of the
edge, or at a crossing away from `v(d) ∪ v(d̄)`, where it is a triangle of `D^P`. -/
private theorem isDatumTriangle_contractEdge_cases (hDP : G.IsWhiteDatum DP)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    (hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) = DP x)
    {t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)}
    (ht : (G.contractEdge d hleg).IsDatumTriangle DQ t) :
    (∃ a, (a = d ∨ a = G.inv d) ∧ ∃ τ, G.IsCornerTriangle (G.vertexOf a) (DP (G.vertexOf a)) τ ∧
        τ.image (G.cornerMapFst a) = t.map (Embedding.subtype _)) ∨
      (∃ y : (({d, G.inv d} : Set H)ᶜ : Set H), (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) ∧
        G.IsCrossing (G.vertexOf y) ∧ t ⊆ (G.contractEdge d hleg).vertexOf y ∧
        G.IsCornerTriangle (G.vertexOf y) (DP (G.vertexOf y)) (t.map (Embedding.subtype _))) := by
  obtain ⟨x, hx, htx⟩ := ht
  rcases isCrossing_contractEdge_cases he hx with rfl | ⟨y, rfl, hy, hc⟩
  · exact Or.inl ((isCornerTriangle_merged_iff hG he hw hp hq hDP hglue t).1 htx)
  · refine Or.inr ⟨y, hy, hc, htx.1, ?_⟩
    rw [datum_eq_of_notMem (hleg := hleg) he hrel hy hc]
    exact (isCornerTriangle_iff_of_notMem he hy).1 htx

include hG he hw hp hq in
/-- **The pairs of a triangle at the merged vertex.** For a triangle `κ_a(τ)` of `D^Q_v` and
`x ∈ τ`, the clockwise successor of `κ_a x` is `κ_a` of that of `x`, and the pair of `κ_a x` in
`κ_a(τ)` is read in `G` as the pair of `x` in `τ`. -/
private theorem pair_glueSym_end (hDP : G.IsWhiteDatum DP)
    (hDQ : (G.contractEdge d hleg).IsWhiteDatum DQ)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    {a : H} (ha : a = d ∨ a = G.inv d) {τ : Finset H}
    (hτ : G.IsCornerTriangle (G.vertexOf a) (DP (G.vertexOf a)) τ)
    {t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hτt : τ.image (G.cornerMapFst a) = t.map (Embedding.subtype _))
    (ht : (G.contractEdge d hleg).IsDatumTriangle DQ t) {x : H} (hx : x ∈ τ)
    {p : (({d, G.inv d} : Set H)ᶜ : Set H)} (hpx : (p : H) = G.cornerMapFst a x) :
    ((G.contractEdge d hleg).cornerNext t p : H) = G.cornerMapFst a (G.cornerNext τ x) ∧
      glueSym G d ((G.contractEdge d hleg).pairOut t p) = G.pairOut τ x ∧
      glueSym G d ((G.contractEdge d hleg).pairIn t p) = G.pairIn τ x := by
  set Q := G.contractEdge d hleg
  set κ := G.cornerMapFst a
  have hinv := hG.inv_involutive
  have hne := vertexOf_ne_of_end hG he ha
  have hca := isCrossing_vertexOf_end hG he hw hp hq ha
  have hcia := isCrossing_vertexOf_end hG he hw hp hq (inv_end hG ha)
  have h2 : 2 ≤ (G.vertexOf a).card := Nat.le_of_succ_le hca.three_le_card
  have hτD : G.IsDatumTriangle DP τ := ⟨_, hca, hτ⟩
  have hτv : τ ⊆ G.vertexOf a := hτ.1
  have hmemt : ∀ {z : (({d, G.inv d} : Set H)ᶜ : Set H)} {u : H}, u ∈ τ →
      (z : H) = κ u → z ∈ t := by
    intro z u hu hz
    have : (z : H) ∈ t.map (Embedding.subtype _) := by
      rw [← hτt, hz]
      exact mem_image_of_mem _ hu
    exact (mem_map' (Embedding.subtype _)).1 this
  have hlift : ∀ {u : H}, u ∈ τ →
      ∃ z : (({d, G.inv d} : Set H)ᶜ : Set H), z ∈ t ∧ (z : H) = κ u := by
    intro u hu
    have : κ u ∈ t.map (Embedding.subtype _) := by rw [← hτt]; exact mem_image_of_mem _ hu
    exact mem_map.1 this
  have hpt : p ∈ t := hmemt hx hpx
  obtain ⟨q, r, hτe, hxq, hxr, hqr, h1, h2', h3, -, -, -, hcl⟩ := hDP.cornerNext_spec hτD hx
  have hqτ : q ∈ τ := by rw [hτe]; simp
  have hrτ : r ∈ τ := by rw [hτe]; simp
  obtain ⟨pq, -, hpq⟩ := hlift hqτ
  obtain ⟨pr, -, hpr⟩ := hlift hrτ
  have hteq : t = {p, pq, pr} := by
    apply map_injective (Embedding.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))
    rw [← hτt, hτe]
    simp only [image_insert, image_singleton, map_insert, map_singleton, Embedding.coe_subtype,
      hpx, hpq, hpr]
  have hclQ := isCornerClockwise_end (hleg := hleg) hG he hp hq ha (hτv hx) (hτv hqτ) (hτv hrτ) hcl
    hpx hpq hpr
  have hcnQ : Q.cornerNext t p = pq := (cornerNext_eq_of_isCornerClockwise hDQ ht hteq hclQ).1
  have hcn : (Q.cornerNext t p : H) = κ (G.cornerNext τ x) := by rw [hcnQ, hpq, h1]
  refine ⟨hcn, ?_⟩
  -- the pairs
  set n := G.cornerNext τ x with hn
  have hnτ : n ∈ τ := hDP.cornerNext_mem hτD hx
  have hxn : x ≠ n := (hDP.cornerNext_ne hτD hx).symm
  have hvx : G.vertexOf x = G.vertexOf a := G.vertexOf_eq_of_mem (hτv hx)
  have hPiff := cornerNext_eq_rot_symm_iff hDP hτD hx
  rw [hvx] at hPiff
  have hQiff := cornerNext_eq_rot_symm_iff hDQ ht hpt
  have hpW : (p : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
    rw [hpx]; exact glueSide_end_subset hG he ha (cornerMapFst_mem_glueSide (hτv hx))
  rw [vertexOf_eq_merged he hpW] at hQiff
  have hmap : s(p, Q.cornerNext t p).map Subtype.val = s(κ x, κ n) := by
    rw [Sym2.map_mk, hpx, hcn]
  have hQmem : s(p, Q.cornerNext t p) ∈
      DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))) ↔
      s(x, n) ∈ DP (G.vertexOf a) ∨ s(x, n) = G.cornerSide a := by
    rw [← (Sym2.map.injective Subtype.val_injective).mem_finset_image, hglue, hmap,
      cornerGlue_end hG ha DP]
    exact mk_mem_cornerGlue_iff hinv hne h2 (hDP _ hca) (hDP _ hcia) (hτv hx) (hτv hnτ) hxn
  have hside_notMem : G.cornerSide a ∉ DP (G.vertexOf a) :=
    cornerSide_notMem_of_isCornerTriangulation (hDP _ hca) (G.self_mem_vertexOf a)
  have hglueY : ∀ e : Sym2 (({d, G.inv d} : Set H)ᶜ : Set H), e.map Subtype.val = s(κ x, κ n) →
      glueSym G d (yPlus e t) = glueEndPlus G a (s(κ x, κ n)) (τ.image κ) ∧
      glueSym G d (yMinus e t) = glueEndMinus G a (s(κ x, κ n)) (τ.image κ) := by
    intro e he'
    refine ⟨?_, ?_⟩
    · change glueYPlus G d (e.map Subtype.val) (t.map (Embedding.subtype _)) = _
      rw [he', ← hτt, glueYPlus_end hG he ha hτv hτ.2.1]
    · change glueYMinus G d (e.map Subtype.val) (t.map (Embedding.subtype _)) = _
      rw [he', ← hτt, glueYMinus_end hG he ha hτv hτ.2.1]
  have hback : (s(κ x, κ n)).map (glueBack G a) = s(x, n) := by
    rw [Sym2.map_mk, glueBack_cornerMapFst hne (hτv hx), glueBack_cornerMapFst hne (hτv hnτ)]
  have hbackτ : (τ.image κ).image (glueBack G a) = τ := by
    rw [image_image]
    conv_rhs => rw [← image_id (s := τ)]
    exact image_congr fun z hz => glueBack_cornerMapFst hne (hτv hz)
  by_cases hD : s(x, n) ∈ DP (G.vertexOf a)
  · -- a diagonal: both pairs are `y`-symbols
    have hns : s(x, n) ≠ G.cornerSide a := fun h => hside_notMem (h ▸ hD)
    have hP : ¬(n = G.rot.symm x) := fun h => (hPiff.1 h) hD
    have hQ : ¬(Q.cornerNext t p = Q.rot.symm p) := fun h => (hQiff.1 h) (hQmem.2 (Or.inl hD))
    have hγ : s(κ x, κ n) ≠ G.cornerGlueDiagonal a := fun h =>
      hns ((map_eq_cornerGlueDiagonal_iff hne h2 (hτv hx) (hτv hnτ)).1 h)
    obtain ⟨hy1, hy2⟩ := hglueY _ hmap
    refine ⟨?_, ?_⟩
    · rw [pairOut, if_neg hQ, hy1, glueEndPlus, if_neg hγ, hback, hbackτ, pairOut, ← hn, if_neg hP]
    · rw [pairIn, if_neg hQ, hy2, glueEndMinus, if_neg hγ, hback, hbackτ, pairIn, ← hn, if_neg hP]
  · have hP : n = G.rot.symm x := hPiff.2 hD
    by_cases hS : s(x, n) = G.cornerSide a
    · -- the side of `a`: the pair of `κ_a a` crosses `γ_e`
      have hxa : x = a := by
        rw [RotationSystem.cornerSide, Sym2.eq_iff] at hS
        rcases hS with ⟨h, -⟩ | ⟨hx', hn'⟩
        · exact h
        · exfalso
          have h22 := RotationSystem.rot_symm_pow_ne_self (R := G.toRotationSystem) (x := a)
            (k := 2) two_pos (by have := hca.three_le_card; omega)
          apply h22
          rw [pow_two, Equiv.Perm.mul_apply, ← hx', ← hP, hn']
      have hQ : ¬(Q.cornerNext t p = Q.rot.symm p) := fun h => (hQiff.1 h) (hQmem.2 (Or.inr hS))
      have hγ : s(κ x, κ n) = G.cornerGlueDiagonal a :=
        (map_eq_cornerGlueDiagonal_iff hne h2 (hτv hx) (hτv hnτ)).2 hS
      obtain ⟨hy1, hy2⟩ := hglueY _ hmap
      refine ⟨?_, ?_⟩
      · rw [pairOut, if_neg hQ, hy1, glueEndPlus, if_pos hγ, pairOut, ← hn, if_pos hP, hxa]
      · rw [pairIn, if_neg hQ, hy2, glueEndMinus, if_pos hγ, pairIn, ← hn, if_pos hP, hxa]
    · -- a side other than that of `a`: both pairs are `x`-symbols
      have hQ : Q.cornerNext t p = Q.rot.symm p :=
        hQiff.2 fun h => (hQmem.1 h).elim hD hS
      have hxa : x ≠ a := by
        intro hxa
        apply hS
        rw [hP, hxa]
        rfl
      have hκx : κ x = x := RotationSystem.cornerMapFst_of_ne hxa
      refine ⟨?_, ?_⟩
      · rw [pairOut, if_pos hQ, pairOut, ← hn, if_pos hP]
        change xPlus (p : H) = _
        rw [hpx, hκx]
      · rw [pairIn, if_pos hQ, pairIn, ← hn, if_pos hP]
        change xMinus ((Q.inv p : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = _
        rw [coe_contractEdge_inv hinv, hpx, hκx]

omit [Fintype H] [DecidableEq H] in
private theorem map_mem_sym2_map_iff' {e : Sym2 (({d, G.inv d} : Set H)ᶜ : Set H)}
    {τ : Finset (({d, G.inv d} : Set H)ᶜ : Set H)} :
    e.map Subtype.val ∈ (τ.map (Embedding.subtype _)).sym2 ↔ e ∈ τ.sym2 := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [Sym2.map_mk, mk_mem_sym2_iff, mk_mem_sym2_iff]
    exact and_congr (mem_map' (Embedding.subtype _)) (mem_map' (Embedding.subtype _))

include hG he hp hq in
/-- The darts of the side of an end `a`, other than `a`, are darts of the contraction. -/
private theorem mem_compl_of_mem_glueSide {a : H} (ha : a = d ∨ a = G.inv d) {z : H}
    (hz : z ∈ glueSide G a) (hza : z ≠ a) : z ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
  have hinv := hG.inv_involutive
  have hne := vertexOf_ne_of_end hG he ha
  have hia : G.inv a ≠ a := hG.inv_ne a
  have hzia : z ≠ G.inv a := by
    rcases mem_insert.1 hz with rfl | hz'
    · intro h
      have h2 : 2 ≤ (G.vertexOf (G.inv a)).card := by
        rcases inv_end hG ha with h' | h' <;> rw [h'] <;> omega
      have := RotationSystem.rot_symm_pow_ne_self (R := G.toRotationSystem) (x := G.inv a)
        (k := 1) one_pos (by omega)
      rw [pow_one] at this
      exact this h
    · intro h
      exact notMem_inv_of_mem_end hne hz' (h ▸ G.self_mem_vertexOf _)
  rw [mem_compl_pair_iff]
  rcases ha with rfl | rfl
  · exact ⟨hza, hzia⟩
  · rw [hinv] at hzia
    exact ⟨hzia, hza⟩

include hG he in
/-- The two ends of the edge are each other's reverse. -/
private theorem eq_inv_of_end {a a' : H} (ha : a = d ∨ a = G.inv d) (ha' : a' = d ∨ a' = G.inv d)
    (hne : a' ≠ a) : a' = G.inv a := by
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
  · exact absurd rfl hne
  · rfl
  · exact (hG.inv_involutive _).symm
  · exact absurd rfl hne

include hG he hw hp hq in
/-- **Segments of the white datum of the contraction.** -/
private theorem isDatumSegment_contractEdge_cases (hDP : G.IsWhiteDatum DP)
    (hDQ : (G.contractEdge d hleg).IsWhiteDatum DQ)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    (hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) = DP x)
    {e : Sym2 (({d, G.inv d} : Set H)ᶜ : Set H)} {t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)}
    (h : (G.contractEdge d hleg).IsDatumSegment DQ e t) :
    (∃ a, (a = d ∨ a = G.inv d) ∧ ∃ τ, G.IsCornerTriangle (G.vertexOf a) (DP (G.vertexOf a)) τ ∧
        τ.image (G.cornerMapFst a) = t.map (Embedding.subtype _) ∧
        (e.map Subtype.val = G.cornerGlueDiagonal a ∨ ∃ u ∈ τ, ∃ w ∈ τ, u ≠ w ∧
          s(u, w) ∈ DP (G.vertexOf a) ∧
          e.map Subtype.val = s(G.cornerMapFst a u, G.cornerMapFst a w))) ∨
      (∃ y : (({d, G.inv d} : Set H)ᶜ : Set H), (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) ∧
        G.IsCrossing (G.vertexOf y) ∧ t ⊆ (G.contractEdge d hleg).vertexOf y ∧
        G.IsDatumSegment DP (e.map Subtype.val) (t.map (Embedding.subtype _))) := by
  have hinv := hG.inv_involutive
  obtain ⟨x, hx, hex, htx, het⟩ := h
  rcases isCrossing_contractEdge_cases he hx with rfl | ⟨y, rfl, hy, hc⟩
  · obtain ⟨a, ha, τ, hτ, hτt⟩ := (isCornerTriangle_merged_iff hG he hw hp hq hDP hglue t).1 htx
    refine Or.inl ⟨a, ha, τ, hτ, hτt, ?_⟩
    have hne := vertexOf_ne_of_end hG he ha
    have hca := isCrossing_vertexOf_end hG he hw hp hq ha
    have hcia := isCrossing_vertexOf_end hG he hw hp hq (inv_end hG ha)
    have h2 : 2 ≤ (G.vertexOf a).card := Nat.le_of_succ_le hca.three_le_card
    have hdiag := ((hDQ _ hx).1 e hex).1
    induction e using Sym2.ind with | _ z₁ z₂ => ?_
    have hz : ∀ z ∈ t, ∃ u ∈ τ, G.cornerMapFst a u = z := by
      intro z hz
      have : (z : H) ∈ t.map (Embedding.subtype _) := mem_map_of_mem _ hz
      rw [← hτt] at this
      exact mem_image.1 this
    obtain ⟨u, hu, hu'⟩ := hz z₁ (mk_mem_sym2_iff.1 het).1
    obtain ⟨w, hw', hw''⟩ := hz z₂ (mk_mem_sym2_iff.1 het).2
    have huw : u ≠ w := by
      rintro rfl
      exact hdiag (Sym2.mk_isDiag_iff.2 (Subtype.ext (hu'.symm.trans hw'')))
    have hmap : s(z₁, z₂).map Subtype.val = s(G.cornerMapFst a u, G.cornerMapFst a w) := by
      rw [Sym2.map_mk, hu', hw'']
    have hmem : s(G.cornerMapFst a u, G.cornerMapFst a w) ∈
        G.cornerGlue a (DP (G.vertexOf a)) (DP (G.vertexOf (G.inv a))) := by
      rw [← cornerGlue_end hG ha, ← hglue, ← hmap]
      exact mem_image_of_mem _ hex
    rcases (mk_mem_cornerGlue_iff hinv hne h2 (hDP _ hca) (hDP _ hcia) (hτ.1 hu) (hτ.1 hw') huw).1
      hmem with h' | h'
    · exact Or.inr ⟨u, hu, w, hw', huw, h', hmap⟩
    · left
      rw [hmap]
      exact (map_eq_cornerGlueDiagonal_iff hne h2 (hτ.1 hu) (hτ.1 hw')).2 h'
  · refine Or.inr ⟨y, hy, hc, htx.1, G.vertexOf y, hc, ?_, ?_, map_mem_sym2_map_iff'.2 het⟩
    · rw [datum_eq_of_notMem (hleg := hleg) he hrel hy hc]
      exact mem_map_of_mem _ hex
    · rw [datum_eq_of_notMem (hleg := hleg) he hrel hy hc]
      exact (isCornerTriangle_iff_of_notMem he hy).1 htx

include hG he hw hp hq in
/-- **The pairs of a triangle of the contraction**, read in `G`: for every triangle `t` of `D^Q`
there are a triangle `τ` of `D^P` and a bijection `μ : t → τ` commuting with the clockwise
successors, such that the pair of `p` in `t` is read as the pair of `μ p` in `τ`. -/
private theorem exists_pair_glueSym (hDP : G.IsWhiteDatum DP)
    (hDQ : (G.contractEdge d hleg).IsWhiteDatum DQ)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    (hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) = DP x)
    {t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)}
    (ht : (G.contractEdge d hleg).IsDatumTriangle DQ t) :
    ∃ (τ : Finset H) (μ : (({d, G.inv d} : Set H)ᶜ : Set H) → H), G.IsDatumTriangle DP τ ∧
      ∀ p ∈ t, μ p ∈ τ ∧ glueSym G d ((G.contractEdge d hleg).pairOut t p) = G.pairOut τ (μ p) ∧
        glueSym G d ((G.contractEdge d hleg).pairIn t p) = G.pairIn τ (μ p) ∧
        μ ((G.contractEdge d hleg).cornerNext t p) = G.cornerNext τ (μ p) := by
  have hinv := hG.inv_involutive
  rcases isDatumTriangle_contractEdge_cases hG he hw hp hq hDP hglue hrel ht with
    ⟨a, ha, τ, hτ, hτt⟩ | ⟨y, hy, hc, hty, hτ⟩
  · have hne := vertexOf_ne_of_end hG he ha
    have hca := isCrossing_vertexOf_end hG he hw hp hq ha
    have hτD : G.IsDatumTriangle DP τ := ⟨_, hca, hτ⟩
    refine ⟨τ, fun z => glueBack G a z, hτD, fun p hpt => ?_⟩
    have : (p : H) ∈ τ.image (G.cornerMapFst a) := by rw [hτt]; exact mem_map_of_mem _ hpt
    obtain ⟨x, hx, hxp⟩ := mem_image.1 this
    obtain ⟨hcn, h1, h2⟩ := pair_glueSym_end hG he hw hp hq hDP hDQ hglue ha hτ hτt ht hx hxp.symm
    have hμ : glueBack G a p = x := by rw [← hxp, glueBack_cornerMapFst hne (hτ.1 hx)]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> beta_reduce
    · rw [hμ]; exact hx
    · rw [hμ]; exact h1
    · rw [hμ]; exact h2
    · rw [hcn, hμ, glueBack_cornerMapFst hne (hτ.1 (hDP.cornerNext_mem hτD hx))]
  · have hτD : G.IsDatumTriangle DP (t.map (Embedding.subtype _)) := ⟨_, hc, hτ⟩
    refine ⟨t.map (Embedding.subtype _), Subtype.val, hτD, fun p hpt => ?_⟩
    have hpW := notMem_of_mem_vertexOf (hleg := hleg) he hy (hty hpt)
    have hcn := cornerNext_eq_of_notMem (hleg := hleg) he hpW t
    have hiff : G.cornerNext (t.map (Embedding.subtype _)) p = G.rot.symm p ↔
        (G.contractEdge d hleg).cornerNext t p = (G.contractEdge d hleg).rot.symm p := by
      rw [hcn, ← coe_rot_symm_of_notMem (hleg := hleg) he hpW, Subtype.val_inj]
    have hmem : (p : H) ∈ t.map (Embedding.subtype _) := mem_map_of_mem _ hpt
    refine ⟨hmem, ?_, ?_, hcn.symm⟩
    · unfold pairOut
      by_cases h : (G.contractEdge d hleg).cornerNext t p = (G.contractEdge d hleg).rot.symm p
      · rw [if_pos h, if_pos (hiff.2 h)]
        rfl
      · rw [if_neg h, if_neg (mt hiff.1 h), hcn]
        exact (glueY_of_notMem hG he hmem hpW _).1
    · unfold pairIn
      by_cases h : (G.contractEdge d hleg).cornerNext t p = (G.contractEdge d hleg).rot.symm p
      · rw [if_pos h, if_pos (hiff.2 h)]
        change xMinus (((G.contractEdge d hleg).inv p : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = _
        rw [coe_contractEdge_inv hinv]
      · rw [if_neg h, if_neg (mt hiff.1 h), hcn]
        exact (glueY_of_notMem hG he hmem hpW _).2

include hG in
private theorem glueSym_endSymbol (r : Fin (2 * b)) :
    glueSym G d ((G.contractEdge d hleg).endSymbol r) = G.endSymbol r := by
  rcases exists_sourceIndex_or_targetIndex r with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [endSymbol_sourceIndex, endSymbol_sourceIndex]
    rfl
  · rw [endSymbol_targetIndex, endSymbol_targetIndex]
    change xMinus (((G.contractEdge d hleg).inv ((G.contractEdge d hleg).leg i) :
      (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = _
    rw [coe_contractEdge_inv hG.inv_involutive]
    rfl

include hG he in
/-- The strands `y^±_{γ_e, t}` at a triangle `t` on the side of the end `a` are read as `x⁺_a`,
`x⁻_ā`. -/
private theorem glueSym_y_end_diag {a : H} (ha : a = d ∨ a = G.inv d) {τ : Finset H}
    (hτv : τ ⊆ G.vertexOf a) (h3 : τ.card = 3) {t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hτt : τ.image (G.cornerMapFst a) = t.map (Embedding.subtype _))
    {e : Sym2 (({d, G.inv d} : Set H)ᶜ : Set H)}
    (he₀ : e.map Subtype.val = G.cornerGlueDiagonal a) :
    glueSym G d (yPlus e t) = xPlus a ∧ glueSym G d (yMinus e t) = xMinus (G.inv a) := by
  refine ⟨?_, ?_⟩
  · change glueYPlus G d (e.map Subtype.val) (t.map (Embedding.subtype _)) = _
    rw [← hτt, glueYPlus_end hG he ha hτv h3, glueEndPlus, if_pos he₀]
  · change glueYMinus G d (e.map Subtype.val) (t.map (Embedding.subtype _)) = _
    rw [← hτt, glueYMinus_end hG he ha hτv h3, glueEndMinus, if_pos he₀]

include hG he in
/-- The strands `y^±_{e, t}` at a triangle `t = κ_a τ` on the side of the end `a`, for a diagonal
`e = κ_a s` with `s ∈ D^P_{v(a)}`, are read as `y^±_{s, τ}`. -/
private theorem glueSym_y_end {a : H} (ha : a = d ∨ a = G.inv d) {DP : Finset H → Finset (Sym2 H)}
    (hDP : G.IsWhiteDatum DP) (hca : G.IsCrossing (G.vertexOf a)) {τ : Finset H}
    (hτv : τ ⊆ G.vertexOf a) (h3 : τ.card = 3) {t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hτt : τ.image (G.cornerMapFst a) = t.map (Embedding.subtype _)) {u w : H} (hu : u ∈ τ)
    (hw' : w ∈ τ) (hs : s(u, w) ∈ DP (G.vertexOf a))
    {e : Sym2 (({d, G.inv d} : Set H)ᶜ : Set H)}
    (he₀ : e.map Subtype.val = s(G.cornerMapFst a u, G.cornerMapFst a w)) :
    glueSym G d (yPlus e t) = yPlus s(u, w) τ ∧ glueSym G d (yMinus e t) = yMinus s(u, w) τ := by
  have hne := vertexOf_ne_of_end hG he ha
  have h2 : 2 ≤ (G.vertexOf a).card := Nat.le_of_succ_le hca.three_le_card
  have hγ : e.map Subtype.val ≠ G.cornerGlueDiagonal a := by
    rw [he₀, Ne, map_eq_cornerGlueDiagonal_iff hne h2 (hτv hu) (hτv hw')]
    intro h
    rw [h] at hs
    exact cornerSide_notMem_of_isCornerTriangulation (hDP _ hca) (G.self_mem_vertexOf a) hs
  have hback : (e.map Subtype.val).map (glueBack G a) = s(u, w) := by
    rw [he₀, Sym2.map_mk, glueBack_cornerMapFst hne (hτv hu),
      glueBack_cornerMapFst hne (hτv hw')]
  have hbackτ : (τ.image (G.cornerMapFst a)).image (glueBack G a) = τ := by
    rw [image_image]
    conv_rhs => rw [← image_id (s := τ)]
    exact image_congr fun z hz => glueBack_cornerMapFst hne (hτv hz)
  refine ⟨?_, ?_⟩
  · change glueYPlus G d (e.map Subtype.val) (t.map (Embedding.subtype _)) = _
    rw [← hτt, glueYPlus_end hG he ha hτv h3, glueEndPlus, if_neg hγ, hback, hbackτ]
  · change glueYMinus G d (e.map Subtype.val) (t.map (Embedding.subtype _)) = _
    rw [← hτt, glueYMinus_end hG he ha hτv h3, glueEndMinus, if_neg hγ, hback, hbackτ]

include hG he in
/-- The strands `y^±_{e, t}` at a triangle away from the merged vertex are kept. -/
private theorem glueSym_y_other {t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)}
    {z : (({d, G.inv d} : Set H)ᶜ : Set H)} (hz : z ∈ t)
    (hzW : (z : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d))
    (e : Sym2 (({d, G.inv d} : Set H)ᶜ : Set H)) :
    glueSym G d (yPlus e t) = yPlus (e.map Subtype.val) (t.map (Embedding.subtype _)) ∧
      glueSym G d (yMinus e t) = yMinus (e.map Subtype.val) (t.map (Embedding.subtype _)) :=
  glueY_of_notMem hG he (mem_map_of_mem _ hz) hzW _

include hG he in
private theorem glueInvSym_xPlus_end (DP : Finset H → Finset (Sym2 H)) {a : H}
    (ha : a = d ∨ a = G.inv d) :
    glueInvSym G d DP (xPlus a) =
      yPlus (G.cornerGlueDiagonal d) ((G.sideTriangle DP a).image (G.cornerMapFst a)) := by
  have hdi : G.inv d ≠ d := hG.inv_ne d
  rcases ha with rfl | rfl
  · simp [glueInvSym]
  · simp [glueInvSym, hdi]

include hG he in
private theorem glueInvSym_xMinus_end (DP : Finset H → Finset (Sym2 H)) {a : H}
    (ha : a = d ∨ a = G.inv d) :
    glueInvSym G d DP (xMinus (G.inv a)) =
      yMinus (G.cornerGlueDiagonal d) ((G.sideTriangle DP a).image (G.cornerMapFst a)) := by
  have hdi : G.inv d ≠ d := hG.inv_ne d
  rcases ha with rfl | rfl
  · simp [glueInvSym]
  · simp [glueInvSym, hdi.symm, hG.inv_involutive d]

include he in
private theorem glueInvSym_y_end (DP : Finset H → Finset (Sym2 H)) {a : H}
    (ha : a = d ∨ a = G.inv d) {τ : Finset H} (hτv : τ ⊆ G.vertexOf a) (hτn : τ.Nonempty)
    (s : Sym2 H) :
    glueInvSym G d DP (yPlus s τ) =
        yPlus (s.map (G.cornerMapFst a)) (τ.image (G.cornerMapFst a)) ∧
      glueInvSym G d DP (yMinus s τ) =
        yMinus (s.map (G.cornerMapFst a)) (τ.image (G.cornerMapFst a)) := by
  rcases ha with rfl | rfl
  · simp [glueInvSym, hτv]
  · have hn : ¬τ ⊆ G.vertexOf d := by
      intro h
      obtain ⟨z, hz⟩ := hτn
      exact notMem_inv_vertexOf_of_mem he (h hz) (hτv hz)
    simp [glueInvSym, hτv, hn]

private theorem glueInvSym_y_other (DP : Finset H → Finset (Sym2 H)) {τ : Finset H} {z : H}
    (hz : z ∈ τ) (hzW : z ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) (s : Sym2 H) :
    glueInvSym G d DP (yPlus s τ) = yPlus s τ ∧ glueInvSym G d DP (yMinus s τ) = yMinus s τ := by
  have h1 : ¬τ ⊆ G.vertexOf d := fun h => hzW (mem_union_left _ (h hz))
  have h2 : ¬τ ⊆ G.vertexOf (G.inv d) := fun h => hzW (mem_union_right _ (h hz))
  simp [glueInvSym, h1, h2]

private theorem glueInvSym_of_mem (DP : Finset H → Finset (Sym2 H)) {c : H}
    (hc : c ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    glueInvSym G d DP (xPlus c) = xPlus c ∧ glueInvSym G d DP (xMinus c) = xMinus c := by
  rw [mem_compl_pair_iff] at hc
  simp [glueInvSym, hc.1, hc.2]

include hG he hw hp hq in
private theorem isInitial_end {a : H} (ha : a = d ∨ a = G.inv d) : G.IsInitial a := by
  have haW := vertexOf_end_subset he ha (G.self_mem_vertexOf a)
  exact ⟨notMem_bdry_of_mem_vertexOf (not_isBoundaryVertex_of_mem he haW) (G.self_mem_vertexOf a),
    Or.inl (isCrossing_vertexOf_end hG he hw hp hq ha)⟩

include hG he hw hp hq in
private theorem isTerminal_end {a : H} (ha : a = d ∨ a = G.inv d) : G.IsTerminal a := by
  have hia := inv_end hG ha
  have haW := vertexOf_end_subset he ha (G.self_mem_vertexOf a)
  refine ⟨notMem_bdry_of_mem_vertexOf (not_isBoundaryVertex_of_mem he haW) (G.self_mem_vertexOf a),
    Or.inl (isCrossing_vertexOf_end hG he hw hp hq hia)⟩

include hG he hw hp hq in
private theorem isTerminal_inv_end {a : H} (ha : a = d ∨ a = G.inv d) : G.IsTerminal (G.inv a) :=
  isTerminal_end hG he hw hp hq (inv_end hG ha)

include hG he hw hp hq in
/-- The merged vertex is a crossing of the contraction. -/
private theorem isCrossing_merged :
    (G.contractEdge d hleg).IsCrossing
      ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))) := by
  have hm : G.rot.symm (G.inv d) ∈ (({d, G.inv d} : Set H)ᶜ : Set H) :=
    mem_compl_of_mem_glueSide hG he hp hq (Or.inl rfl) (mem_insert_self _ _)
      (fun h => rot_symm_inv_notMem he.vertexOf_ne (by rw [h]; exact G.self_mem_vertexOf d))
  have hW : G.rot.symm (G.inv d) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
    mem_union_right _ (G.rot_symm_mem_vertexOf _)
  have := isCrossing_vertexOf_merged (hleg := hleg) (y := ⟨_, hm⟩) hG he hw hp hq hW
  rwa [vertexOf_eq_merged he hW] at this

include hG he in
private theorem mem_union_of_end_triangle {a : H} (ha : a = d ∨ a = G.inv d) {τ : Finset H}
    (hτv : τ ⊆ G.vertexOf a) {t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hτt : τ.image (G.cornerMapFst a) = t.map (Embedding.subtype _))
    {z : (({d, G.inv d} : Set H)ᶜ : Set H)} (hz : z ∈ t) :
    (z : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  have : (z : H) ∈ τ.image (G.cornerMapFst a) := by rw [hτt]; exact mem_map_of_mem _ hz
  obtain ⟨x, hx, hxz⟩ := mem_image.1 this
  rw [← hxz]
  exact glueSide_end_subset hG he ha
    (cornerMapFst_mem_glueSide (hτv hx))

include hG he hw hp hq in
/-- The strand diagram of the contraction is read in that of `G`. -/
private theorem isStrandSymbol_glueSym (hDP : G.IsWhiteDatum DP)
    (hDQ : (G.contractEdge d hleg).IsWhiteDatum DQ)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    (hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) = DP x)
    {a : StrandSymbol (({d, G.inv d} : Set H)ᶜ : Set H) b}
    (ha : (G.contractEdge d hleg).IsStrandSymbol DQ a) :
    G.IsStrandSymbol DP (glueSym G d a) := by
  have key : ∀ {e t}, (G.contractEdge d hleg).IsDatumSegment DQ e t →
      G.IsStrandSymbol DP (glueSym G d (yPlus e t)) ∧
        G.IsStrandSymbol DP (glueSym G d (yMinus e t)) := by
    intro e t h
    rcases isDatumSegment_contractEdge_cases hG he hw hp hq hDP hDQ hglue hrel h with
      ⟨a, ha', τ, hτ, hτt, he₀ | ⟨u, hu, w, hw', -, hs, he₀⟩⟩ | ⟨y, hy, hc, hty, hseg⟩
    · obtain ⟨h1, h2⟩ := glueSym_y_end_diag hG he ha' hτ.1 hτ.2.1 hτt he₀
      rw [h1, h2]
      exact ⟨isInitial_end hG he hw hp hq ha', isTerminal_inv_end hG he hw hp hq ha'⟩
    · have hca := isCrossing_vertexOf_end hG he hw hp hq ha'
      obtain ⟨h1, h2⟩ := glueSym_y_end hG he ha' hDP hca hτ.1 hτ.2.1 hτt hu hw' hs he₀
      rw [h1, h2]
      exact ⟨⟨_, hca, hs, hτ, mk_mem_sym2_iff.2 ⟨hu, hw'⟩⟩,
        ⟨_, hca, hs, hτ, mk_mem_sym2_iff.2 ⟨hu, hw'⟩⟩⟩
    · obtain ⟨z, hz⟩ : t.Nonempty := by
        have := (IsDatumTriangle.of_isDatumSegment hseg).card_eq
        rw [card_map] at this
        exact card_pos.1 (by omega)
      obtain ⟨h1, h2⟩ := glueSym_y_other hG he hz (notMem_of_mem_vertexOf he hy (hty hz)) e
      rw [h1, h2]
      exact ⟨hseg, hseg⟩
  cases a with
  | xPlus c => exact (isInitial_contractEdge_iff hG he hw hp hq c).1 ha
  | xMinus t => exact (isTerminal_contractEdge_iff hG he hw hp hq t).1 ha
  | yPlus e t => exact (key ha).1
  | yMinus e t => exact (key ha).2
  | bd r => trivial
  | bd' r => trivial

include hG he hw hp hq in
/-- `glueInvSym` is a left inverse of `glueSym` on the strand diagram of the contraction. -/
private theorem glueInvSym_glueSym (hDP : G.IsWhiteDatum DP)
    (hDQ : (G.contractEdge d hleg).IsWhiteDatum DQ)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    (hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) = DP x)
    {a : StrandSymbol (({d, G.inv d} : Set H)ᶜ : Set H) b}
    (ha : (G.contractEdge d hleg).IsStrandSymbol DQ a) :
    glueInvSym G d DP (glueSym G d a) = a.map (Embedding.subtype _) := by
  have key : ∀ {e t}, (G.contractEdge d hleg).IsDatumSegment DQ e t →
      glueInvSym G d DP (glueSym G d (yPlus e t)) =
          yPlus (e.map Subtype.val) (t.map (Embedding.subtype _)) ∧
        glueInvSym G d DP (glueSym G d (yMinus e t)) =
          yMinus (e.map Subtype.val) (t.map (Embedding.subtype _)) := by
    intro e t h
    have het : e ∈ t.sym2 := let ⟨_, _, _, _, h'⟩ := h; h'
    rcases isDatumSegment_contractEdge_cases hG he hw hp hq hDP hDQ hglue hrel h with
      ⟨a, ha', τ, hτ, hτt, he₀ | ⟨u, hu, w, hw', -, hs, he₀⟩⟩ | ⟨y, hy, hc, hty, hseg⟩
    · obtain ⟨h1, h2⟩ := glueSym_y_end_diag hG he ha' hτ.1 hτ.2.1 hτt he₀
      have hne := vertexOf_ne_of_end hG he ha'
      have hca := isCrossing_vertexOf_end hG he hw hp hq ha'
      have hτD : G.IsDatumTriangle DP τ := ⟨_, hca, hτ⟩
      have hside : G.cornerSide a ∈ τ.sym2 := by
        refine cornerSide_mem_sym2_of_cornerGlueDiagonal_mem hne hτ.1 ?_
        rw [hτt, ← he₀]
        exact map_mem_sym2_map_iff'.2 het
      have hτs := hDP.eq_sideTriangle hτD hside
      rw [h1, h2, glueInvSym_xPlus_end hG he DP ha', glueInvSym_xMinus_end hG he DP ha', ← hτs, hτt,
        ← cornerGlueDiagonal_end hG ha', ← he₀]
      exact ⟨rfl, rfl⟩
    · have hca := isCrossing_vertexOf_end hG he hw hp hq ha'
      obtain ⟨h1, h2⟩ := glueSym_y_end hG he ha' hDP hca hτ.1 hτ.2.1 hτt hu hw' hs he₀
      have hτn : τ.Nonempty := ⟨u, hu⟩
      obtain ⟨h3, h4⟩ := glueInvSym_y_end he DP ha' hτ.1 hτn s(u, w)
      rw [h1, h2, h3, h4, hτt, Sym2.map_mk, ← he₀]
      exact ⟨rfl, rfl⟩
    · obtain ⟨z, hz⟩ : t.Nonempty := by
        have := (IsDatumTriangle.of_isDatumSegment hseg).card_eq
        rw [card_map] at this
        exact card_pos.1 (by omega)
      have hzW := notMem_of_mem_vertexOf he hy (hty hz)
      obtain ⟨h1, h2⟩ := glueSym_y_other hG he hz hzW e
      obtain ⟨h3, h4⟩ := glueInvSym_y_other DP (mem_map_of_mem (Embedding.subtype _) hz) hzW
        (e.map Subtype.val)
      rw [h1, h2, h3, h4]
      exact ⟨rfl, rfl⟩
  cases a with
  | xPlus c => exact (glueInvSym_of_mem DP c.2).1
  | xMinus t => exact (glueInvSym_of_mem DP t.2).2
  | yPlus e t => exact (key ha).1
  | yMinus e t => exact (key ha).2
  | bd r => rfl
  | bd' r => rfl

omit [Fintype H] [DecidableEq H] in
private theorem exists_subtype_map_eq {τ₀ : Finset H}
    (h : ∀ x ∈ τ₀, x ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    ∃ τ : Finset (({d, G.inv d} : Set H)ᶜ : Set H), τ.map (Embedding.subtype _) = τ₀ := by
  classical
  exact ⟨τ₀.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)), subtype_map_of_mem h⟩

include hG he hp hq in
/-- The image under `κ_a` of a set of darts of `v(a)` consists of darts of the contraction. -/
private theorem exists_map_eq_image_end {a : H} (ha : a = d ∨ a = G.inv d) {τ : Finset H}
    (hτv : τ ⊆ G.vertexOf a) :
    ∃ t : Finset (({d, G.inv d} : Set H)ᶜ : Set H),
      τ.image (G.cornerMapFst a) = t.map (Embedding.subtype _) := by
  have hne := vertexOf_ne_of_end hG he ha
  obtain ⟨t, ht⟩ := exists_subtype_map_eq (G := G) (d := d) (τ₀ := τ.image (G.cornerMapFst a))
    (by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
      exact mem_compl_of_mem_glueSide hG he hp hq ha (cornerMapFst_mem_glueSide (hτv hx))
        (cornerMapFst_ne_self hne _))
  exact ⟨t, ht.symm⟩

include hG he hw hp hq in
/-- The strands across `γ_e` in the triangle of the side of the end `a`. -/
private theorem exists_isDatumSegment_diag (hDP : G.IsWhiteDatum DP)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    {a : H} (ha : a = d ∨ a = G.inv d) :
    ∃ (e : Sym2 (({d, G.inv d} : Set H)ᶜ : Set H)) (t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)),
      (G.contractEdge d hleg).IsDatumSegment DQ e t ∧ e.map Subtype.val = G.cornerGlueDiagonal a ∧
      ∃ τ, G.IsCornerTriangle (G.vertexOf a) (DP (G.vertexOf a)) τ ∧
        τ.image (G.cornerMapFst a) = t.map (Embedding.subtype _) := by
  have hne := vertexOf_ne_of_end hG he ha
  have hca := isCrossing_vertexOf_end hG he hw hp hq ha
  have h2 : 2 ≤ (G.vertexOf a).card := Nat.le_of_succ_le hca.three_le_card
  obtain ⟨hτD, hside⟩ := hDP.sideTriangle_spec (D := DP) (p := a) hca
  set τ := G.sideTriangle DP a
  have haτ : a ∈ τ := mem_sym2_iff.1 hside a (Sym2.mem_mk_left _ _)
  have hτ : G.IsCornerTriangle (G.vertexOf a) (DP (G.vertexOf a)) τ := (hτD.vertexOf haτ).2
  obtain ⟨t, hτt⟩ := exists_map_eq_image_end hG he hp hq ha hτ.1
  have hγ : G.cornerGlueDiagonal d ∈
      G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))) :=
    RotationSystem.mem_cornerGlue.2 (Or.inl rfl)
  rw [← hglue] at hγ
  obtain ⟨e, he', hee⟩ := mem_image.1 hγ
  rw [← cornerGlueDiagonal_end hG ha] at hee
  refine ⟨e, t, ⟨_, isCrossing_merged hG he hw hp hq, he',
    (isCornerTriangle_merged_iff hG he hw hp hq hDP hglue t).2 ⟨a, ha, τ, hτ, hτt⟩, ?_⟩,
    hee, τ, hτ, hτt⟩
  rw [← map_mem_sym2_map_iff', hee, ← hτt, ← map_cornerSide_eq h2]
  have hσ : G.rot.symm a ∈ τ := mem_sym2_iff.1 hside _ (Sym2.mem_mk_right _ _)
  exact mk_mem_sym2_iff.2 ⟨mem_image_of_mem _ haτ, mem_image_of_mem _ hσ⟩

include hG he hw hp hq in
/-- Every strand `y^±_{s, τ}` of `G` is read from a strand of the contraction. -/
private theorem exists_isDatumSegment_lift (hDP : G.IsWhiteDatum DP)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    (hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) = DP x)
    {s : Sym2 H} {τ : Finset H} (hs : G.IsDatumSegment DP s τ) :
    ∃ (e : Sym2 (({d, G.inv d} : Set H)ᶜ : Set H)) (t : Finset (({d, G.inv d} : Set H)ᶜ : Set H)),
      (G.contractEdge d hleg).IsDatumSegment DQ e t ∧ glueSym G d (yPlus e t) = yPlus s τ ∧
        glueSym G d (yMinus e t) = yMinus s τ := by
  have hinv := hG.inv_involutive
  obtain ⟨x, hx, hsx, hτx, hsτ⟩ := hs
  obtain ⟨z, hz⟩ : τ.Nonempty := card_pos.1 (by have := hτx.2.1; omega)
  have hxz : x = G.vertexOf z := hx.eq_vertexOf (hτx.1 hz)
  subst hxz
  by_cases hzW : z ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
  · obtain ⟨a, ha, hza⟩ : ∃ a, (a = d ∨ a = G.inv d) ∧ G.vertexOf z = G.vertexOf a := by
      rcases mem_union.1 hzW with h | h
      · exact ⟨d, Or.inl rfl, G.vertexOf_eq_of_mem h⟩
      · exact ⟨G.inv d, Or.inr rfl, G.vertexOf_eq_of_mem h⟩
    rw [hza] at hx hsx hτx
    have hne := vertexOf_ne_of_end hG he ha
    have hca := isCrossing_vertexOf_end hG he hw hp hq ha
    have hcia := isCrossing_vertexOf_end hG he hw hp hq (inv_end hG ha)
    have h2 : 2 ≤ (G.vertexOf a).card := Nat.le_of_succ_le hca.three_le_card
    obtain ⟨t, hτt⟩ := exists_map_eq_image_end hG he hp hq ha hτx.1
    induction s using Sym2.ind with | _ u w => ?_
    obtain ⟨hu, hw'⟩ := mk_mem_sym2_iff.1 hsτ
    have huw : u ≠ w := fun h => ((hDP _ hca).1 _ hsx).1 (Sym2.mk_isDiag_iff.2 h)
    have hmem : s(G.cornerMapFst a u, G.cornerMapFst a w) ∈
        G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))) := by
      rw [cornerGlue_end hG ha]
      exact (mk_mem_cornerGlue_iff hinv hne h2 (hDP _ hca) (hDP _ hcia) (hτx.1 hu) (hτx.1 hw')
        huw).2 (Or.inl hsx)
    rw [← hglue] at hmem
    obtain ⟨e, he', hee⟩ := mem_image.1 hmem
    have hseg : (G.contractEdge d hleg).IsDatumSegment DQ e t := by
      refine ⟨_, isCrossing_merged hG he hw hp hq, he',
        (isCornerTriangle_merged_iff hG he hw hp hq hDP hglue t).2 ⟨a, ha, τ, hτx, hτt⟩, ?_⟩
      rw [← map_mem_sym2_map_iff', hee, ← hτt]
      exact mk_mem_sym2_iff.2 ⟨mem_image_of_mem _ hu, mem_image_of_mem _ hw'⟩
    obtain ⟨h1, h2'⟩ := glueSym_y_end hG he ha hDP hca hτx.1 hτx.2.1 hτt hu hw' hsx hee
    exact ⟨e, t, hseg, h1, h2'⟩
  · have hzY := mem_compl_pair_of_notMem hzW
    set y : (({d, G.inv d} : Set H)ᶜ : Set H) := ⟨z, hzY⟩
    have hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := hzW
    have hdat := datum_eq_of_notMem (hleg := hleg) he hrel hy hx
    have hτY : ∀ x ∈ τ, x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
      intro x hxτ
      apply mem_compl_pair_of_notMem
      rwa [mem_union_vertexOf_iff_of_vertexOf_eq (G.vertexOf_eq_of_mem (hτx.1 hxτ))]
    obtain ⟨t, rfl⟩ := exists_subtype_map_eq hτY
    rw [hdat] at hsx hτx
    obtain ⟨e, he', rfl⟩ := mem_map.1 hsx
    have hseg : (G.contractEdge d hleg).IsDatumSegment DQ e t :=
      ⟨_, (isCrossing_iff_of_notMem he hy).2 hx, he', (isCornerTriangle_iff_of_notMem he hy).2 hτx,
        map_mem_sym2_map_iff'.1 hsτ⟩
    obtain ⟨z', hz'⟩ : t.Nonempty := by
      have := hτx.2.1
      rw [card_map] at this
      exact card_pos.1 (by omega)
    have hz'W : (z' : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
      notMem_of_mem_vertexOf (hleg := hleg) he hy
        (((isCornerTriangle_iff_of_notMem (hleg := hleg) he hy).2 hτx).1 hz')
    obtain ⟨h1, h2⟩ := glueSym_y_other hG he hz' hz'W e
    exact ⟨e, t, hseg, h1.trans (by rw [Embedding.sym2Map_apply]; rfl),
      h2.trans (by rw [Embedding.sym2Map_apply]; rfl)⟩

include hG he hw hp hq in
/-- **`glueSym` is onto the strand diagram of `G`.** -/
private theorem exists_glueSym_eq (hDP : G.IsWhiteDatum DP)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    (hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) = DP x)
    {a : StrandSymbol H b} (ha : G.IsStrandSymbol DP a) :
    ∃ a', (G.contractEdge d hleg).IsStrandSymbol DQ a' ∧ glueSym G d a' = a := by
  have hinv := hG.inv_involutive
  cases a with
  | xPlus c =>
    by_cases hc : c ∈ (({d, G.inv d} : Set H)ᶜ : Set H)
    · exact ⟨xPlus ⟨c, hc⟩, (isInitial_contractEdge_iff hG he hw hp hq _).2 ha, rfl⟩
    · have hc' := eq_or_eq_of_notMem_compl_pair hc
      obtain ⟨e, t, hseg, hee, τ, hτ, hτt⟩ := exists_isDatumSegment_diag (hleg := hleg) (DQ := DQ)
        hG he hw hp hq hDP hglue hc'
      exact ⟨yPlus e t, hseg, (glueSym_y_end_diag hG he hc' hτ.1 hτ.2.1 hτt hee).1⟩
  | xMinus t =>
    by_cases ht : t ∈ (({d, G.inv d} : Set H)ᶜ : Set H)
    · exact ⟨xMinus ⟨t, ht⟩, (isTerminal_contractEdge_iff hG he hw hp hq _).2 ha, rfl⟩
    · have ha' : G.inv t = d ∨ G.inv t = G.inv d := inv_end hG (eq_or_eq_of_notMem_compl_pair ht)
      obtain ⟨e, t', hseg, hee, τ, hτ, hτt⟩ := exists_isDatumSegment_diag (hleg := hleg) (DQ := DQ)
        hG he hw hp hq hDP hglue ha'
      refine ⟨yMinus e t', hseg, ?_⟩
      rw [(glueSym_y_end_diag hG he ha' hτ.1 hτ.2.1 hτt hee).2, hinv]
  | yPlus s τ =>
    obtain ⟨e, t, hseg, h1, -⟩ := exists_isDatumSegment_lift (hleg := hleg) hG he hw hp hq hDP hglue
      hrel ha
    exact ⟨yPlus e t, hseg, h1⟩
  | yMinus s τ =>
    obtain ⟨e, t, hseg, -, h2⟩ := exists_isDatumSegment_lift (hleg := hleg) hG he hw hp hq hDP hglue
      hrel ha
    exact ⟨yMinus e t, hseg, h2⟩
  | bd r => exact ⟨bd r, trivial, rfl⟩
  | bd' r => exact ⟨bd' r, trivial, rfl⟩

include hG he hw hp hq in
/-- **`glueSym` commutes with the involutions**, on the symbols `x⁺`, `y⁺` and `∂`. -/
private theorem glueSym_strandInvSym (hDP : G.IsWhiteDatum DP)
    (hDQ : (G.contractEdge d hleg).IsWhiteDatum DQ)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    (hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) = DP x)
    {a : StrandSymbol (({d, G.inv d} : Set H)ᶜ : Set H) b}
    (ha : (G.contractEdge d hleg).IsStrandSymbol DQ a)
    (hform : (∃ c, a = xPlus c) ∨ (∃ e t, a = yPlus e t) ∨ ∃ r, a = bd r) :
    glueSym G d ((G.contractEdge d hleg).strandInvSym DQ a) =
      G.strandInvSym DP (glueSym G d a) := by
  have hinv := hG.inv_involutive
  rcases hform with ⟨c, rfl⟩ | ⟨e, t, rfl⟩ | ⟨r, rfl⟩
  · change xMinus (((G.contractEdge d hleg).chainEnd c : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
      xMinus (G.chainEnd c)
    rw [coe_chainEnd_contractEdge hG he hw hp hq ha]
  · have h : (G.contractEdge d hleg).IsDatumSegment DQ e t := ha
    obtain ⟨ho, hoτ, -⟩ := hDQ.otherTriangle_spec h
    set t'' := (G.contractEdge d hleg).otherTriangle DQ e t with ht''
    change glueSym G d (yMinus e t'') = G.strandInvSym DP (glueSym G d (yPlus e t))
    have het : e ∈ t.sym2 := let ⟨_, _, _, _, h'⟩ := h; h'
    have het'' : e ∈ t''.sym2 := let ⟨_, _, _, _, h'⟩ := ho; h'
    have hzt : (Quot.out e).1 ∈ t := mem_sym2_iff.1 het _ (Sym2.out_fst_mem e)
    have hzt'' : (Quot.out e).1 ∈ t'' := mem_sym2_iff.1 het'' _ (Sym2.out_fst_mem e)
    have hdiag : ¬e.IsDiag := by
      obtain ⟨x, hx, hex, -, -⟩ := h
      exact ((hDQ _ hx).1 e hex).1
    have hmapinj : ∀ {t₁ t₂ : Finset (({d, G.inv d} : Set H)ᶜ : Set H)},
        t₁.map (Embedding.subtype _) = t₂.map (Embedding.subtype _) → t₁ = t₂ :=
      fun h' => map_injective _ h'
    rcases isDatumSegment_contractEdge_cases hG he hw hp hq hDP hDQ hglue hrel h with
      ⟨a, ha', τ, hτ, hτt, he₀ | ⟨u, hu, w, hw', huw, hs, he₀⟩⟩ | ⟨y, hy, hc, hty, hseg⟩
    · -- `e = γ_e`, at the side of `a`
      have hne := vertexOf_ne_of_end hG he ha'
      have hca := isCrossing_vertexOf_end hG he hw hp hq ha'
      have hτD : G.IsDatumTriangle DP τ := ⟨_, hca, hτ⟩
      rw [(glueSym_y_end_diag hG he ha' hτ.1 hτ.2.1 hτt he₀).1]
      change _ = xMinus (G.chainEnd a)
      rw [chainEnd_eq_self_of_isTerminal (isTerminal_end hG he hw hp hq ha')]
      have hside : G.cornerSide a ∈ τ.sym2 := by
        refine cornerSide_mem_sym2_of_cornerGlueDiagonal_mem hne hτ.1 ?_
        rw [hτt, ← he₀]
        exact map_mem_sym2_map_iff'.2 het
      rcases isDatumSegment_contractEdge_cases hG he hw hp hq hDP hDQ hglue hrel ho with
        ⟨a'', ha'', τ'', hτ'', hτt'', he₀'' | ⟨u, hu, w, hw', huw, hs, he₀''⟩⟩ |
          ⟨y, hy, hc, hty, hseg⟩
      · by_cases haa : a'' = a
        · subst haa
          exfalso
          have hτD'' : G.IsDatumTriangle DP τ'' := ⟨_, hca, hτ''⟩
          have hside'' : G.cornerSide a'' ∈ τ''.sym2 := by
            refine cornerSide_mem_sym2_of_cornerGlueDiagonal_mem hne hτ''.1 ?_
            rw [hτt'', ← he₀'']
            exact map_mem_sym2_map_iff'.2 het''
          have h1 := hDP.eq_sideTriangle hτD hside
          have h2 := hDP.eq_sideTriangle hτD'' hside''
          exact hoτ (hmapinj (by rw [← hτt'', ← hτt, h1, h2]))
        · have hia := eq_inv_of_end hG he ha' ha'' haa
          rw [(glueSym_y_end_diag hG he ha'' hτ''.1 hτ''.2.1 hτt'' he₀'').2, hia, hinv]
      · exfalso
        have hca'' := isCrossing_vertexOf_end hG he hw hp hq ha''
        have hne'' := vertexOf_ne_of_end hG he ha''
        have h2 : 2 ≤ (G.vertexOf a'').card := by have := hca''.three_le_card; omega
        have : s(G.cornerMapFst a'' u, G.cornerMapFst a'' w) = G.cornerGlueDiagonal a'' := by
          rw [← he₀'', he₀, cornerGlueDiagonal_end hG ha', cornerGlueDiagonal_end hG ha'']
        rw [map_eq_cornerGlueDiagonal_iff hne'' h2 (hτ''.1 hu) (hτ''.1 hw')] at this
        rw [this] at hs
        exact cornerSide_notMem_of_isCornerTriangulation (hDP _ hca'') (G.self_mem_vertexOf _) hs
      · exact absurd (mem_union_of_end_triangle hG he ha' hτ.1 hτt hzt)
          (notMem_of_mem_vertexOf he hy (hty hzt''))
    · -- a diagonal `κ_a {u, w}` at the side of `a`
      have hne := vertexOf_ne_of_end hG he ha'
      have hca := isCrossing_vertexOf_end hG he hw hp hq ha'
      have h2 : 2 ≤ (G.vertexOf a).card := Nat.le_of_succ_le hca.three_le_card
      have hτD : G.IsDatumTriangle DP τ := ⟨_, hca, hτ⟩
      have hγ : e.map Subtype.val ≠ G.cornerGlueDiagonal a := by
        rw [he₀, Ne, map_eq_cornerGlueDiagonal_iff hne h2 (hτ.1 hu) (hτ.1 hw')]
        intro h'
        rw [h'] at hs
        exact cornerSide_notMem_of_isCornerTriangulation (hDP _ hca) (G.self_mem_vertexOf a) hs
      rw [(glueSym_y_end hG he ha' hDP hca hτ.1 hτ.2.1 hτt hu hw' hs he₀).1]
      change _ = yMinus s(u, w) (G.otherTriangle DP s(u, w) τ)
      rcases isDatumSegment_contractEdge_cases hG he hw hp hq hDP hDQ hglue hrel ho with
        ⟨a'', ha'', τ'', hτ'', hτt'', he₀'' | ⟨u'', hu'', w'', hw'', huw'', hs'', he₀''⟩⟩ |
          ⟨y, hy, hc, hty, hseg⟩
      · exfalso
        exact hγ (by rw [he₀'', cornerGlueDiagonal_end hG ha', cornerGlueDiagonal_end hG ha''])
      · by_cases haa : a'' = a
        · subst haa
          have hss : s(u'', w'') = s(u, w) :=
            map_cornerMapFst_inj hne (hτ''.1 hu'') (hτ''.1 hw'') (hτ.1 hu) (hτ.1 hw')
              (he₀''.symm.trans he₀)
          rw [(glueSym_y_end hG he ha'' hDP hca hτ''.1 hτ''.2.1 hτt'' hu'' hw'' hs'' he₀'').2, hss]
          congr 1
          refine hDP.eq_otherTriangle ⟨_, hca, hs, hτ, mk_mem_sym2_iff.2 ⟨hu, hw'⟩⟩
            ⟨_, hca, hτ''⟩ ?_ ?_
          · rw [← hss]; exact mk_mem_sym2_iff.2 ⟨hu'', hw''⟩
          · intro hττ
            exact hoτ (hmapinj (by rw [← hτt'', ← hτt, hττ]))
        · exfalso
          have hia := eq_inv_of_end hG he ha' ha'' haa
          have hne'' := vertexOf_ne_of_end hG he ha''
          apply hγ
          refine eq_cornerGlueDiagonal_of_subset hinv hne ?_ ?_ ?_
          · rw [Sym2.isDiag_map Subtype.val_injective]
            exact hdiag
          · intro z hz
            rw [he₀] at hz
            rcases Sym2.mem_iff.1 hz with rfl | rfl
            · exact cornerMapFst_mem_glueSide (hτ.1 hu)
            · exact cornerMapFst_mem_glueSide (hτ.1 hw')
          · intro z hz
            rw [he₀''] at hz
            rw [← hia]
            rcases Sym2.mem_iff.1 hz with rfl | rfl
            · exact cornerMapFst_mem_glueSide (hτ''.1 hu'')
            · exact cornerMapFst_mem_glueSide (hτ''.1 hw'')
      · exact absurd (mem_union_of_end_triangle hG he ha' hτ.1 hτt hzt)
          (notMem_of_mem_vertexOf he hy (hty hzt''))
    · -- a strand away from the merged vertex
      have hzW := notMem_of_mem_vertexOf he hy (hty hzt)
      rw [(glueSym_y_other hG he hzt hzW e).1]
      change _ = yMinus (e.map Subtype.val) (G.otherTriangle DP (e.map Subtype.val)
        (t.map (Embedding.subtype _)))
      rcases isDatumSegment_contractEdge_cases hG he hw hp hq hDP hDQ hglue hrel ho with
        ⟨a'', ha'', τ'', hτ'', hτt'', -⟩ | ⟨y'', hy'', hc'', hty'', hseg''⟩
      · exact absurd (mem_union_of_end_triangle hG he ha'' hτ''.1 hτt'' hzt'') hzW
      · rw [(glueSym_y_other hG he hzt'' hzW e).2]
        congr 1
        refine hDP.eq_otherTriangle hseg (IsDatumTriangle.of_isDatumSegment hseg'')
          (let ⟨_, _, _, _, h'⟩ := hseg''; h') ?_
        intro htt
        exact hoτ (hmapinj htt)
  · rfl

include hG he hw hp hq in
/-- **`glueSym` commutes with the rotations.** -/
private theorem glueSym_strandRotSym (hDP : G.IsWhiteDatum DP)
    (hDQ : (G.contractEdge d (he.leg_mem hG)).IsWhiteDatum DQ)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))))
    (hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) = DP x)
    {a : StrandSymbol (({d, G.inv d} : Set H)ᶜ : Set H) b}
    (ha : (G.contractEdge d (he.leg_mem hG)).IsStrandSymbol DQ a) :
    glueSym G d ((G.contractEdge d (he.leg_mem hG)).strandRotSym DQ a) =
      G.strandRotSym DP (glueSym G d a) := by
  have hQ := hG.contractEdge (hleg := he.leg_mem hG) he
  rcases IsStrandSymbol.cases hQ hDQ ha with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ |
    ⟨t, p, ht, hpt, rfl⟩ | ⟨t, p, ht, hpt, rfl⟩
  · rw [strandRotSym_bd, glueSym_endSymbol hG]
    rfl
  · rfl
  · rw [strandRotSym_endSymbol hQ, glueSym_endSymbol hG, strandRotSym_endSymbol hG]
    rfl
  · obtain ⟨τ, μ, hτ, hμ⟩ := exists_pair_glueSym hG he hw hp hq hDP hDQ hglue hrel ht
    obtain ⟨hμp, h1, h2, -⟩ := hμ p hpt
    rw [strandRotSym_pairOut hQ ht hpt, h2, h1, strandRotSym_pairOut hG hτ hμp]
  · obtain ⟨τ, μ, hτ, hμ⟩ := exists_pair_glueSym hG he hw hp hq hDP hDQ hglue hrel ht
    obtain ⟨hμp, -, h2, h3⟩ := hμ p hpt
    have hq₁ := hDQ.cornerNext_mem ht hpt
    have hq₂ := hDQ.cornerNext_mem ht hq₁
    obtain ⟨-, h1', -, h3'⟩ := hμ _ hq₁
    obtain ⟨-, h1'', -, -⟩ := hμ _ hq₂
    rw [strandRotSym_pairIn hQ hDQ ht hpt, h2, strandRotSym_pairIn hG hDP hτ hμp, h1'', h3', h3]

omit [Fintype H] in
private theorem strandSymbol_map_injective {α β : Type*} (f : α ↪ β) :
    Injective (StrandSymbol.map (b := b) f) := by
  intro x y h
  cases x <;> cases y <;> simp only [StrandSymbol.map, reduceCtorEq] at h
  · rw [f.injective (xPlus.inj h)]
  · rw [f.injective (xMinus.inj h)]
  · obtain ⟨h1, h2⟩ := yPlus.inj h
    rw [Sym2.map.injective f.injective h1, map_injective f h2]
  · obtain ⟨h1, h2⟩ := yMinus.inj h
    rw [Sym2.map.injective f.injective h1, map_injective f h2]
  · rw [bd.inj h]
  · rw [bd'.inj h]

private theorem glueSym_isBoundary_and_isOut
    (a : StrandSymbol (({d, G.inv d} : Set H)ᶜ : Set H) b) :
    ((glueSym G d a).IsBoundary ↔ a.IsBoundary) ∧ (glueSym G d a).isOut = a.isOut := by
  cases a with
  | xPlus c => exact ⟨Iff.rfl, rfl⟩
  | xMinus t => exact ⟨Iff.rfl, rfl⟩
  | yPlus e t =>
    simp only [glueSym, glueYPlus, glueEndPlus]
    split_ifs <;> exact ⟨Iff.rfl, rfl⟩
  | yMinus e t =>
    simp only [glueSym, glueYMinus, glueEndMinus]
    split_ifs <;> exact ⟨Iff.rfl, rfl⟩
  | bd r => exact ⟨Iff.rfl, rfl⟩
  | bd' r => exact ⟨Iff.rfl, rfl⟩

end Merged

end White

end Contraction

/-! ### Strand diagrams of a white contraction -/

section Glue

variable {G : PlabicData H b} {d : H}

/-- **Strand diagrams of a white contraction**. Let `P` be a plabic graph and `{d, d̄}` an edge
whose ends `w₁ = v(d)` and `w₂ = v(d̄)` are distinct white internal vertices with at least three
darts each, and let `Q` be the contraction along `{d, d̄}`, with merged vertex `v`. Let `D^P` be a
white datum of `P` and `D^Q` one of `Q` with `D^Q_x = D^P_x` at every crossing `x ∉ {w₁, w₂}` of
`P` and `D^Q_v = κ₁(D^P_{w₁}) ∪ κ₂(D^P_{w₂}) ∪ {γ_e}`, sets of pairs of darts of `Q` being read in
`P`. Then `X°(P, D^P)` is isomorphic to `X°(Q, D^Q)`. -/
@[cluster_algebras "lem_strand_diagram_glue"]
theorem strandDiagram_isomorphic_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
    (hw : G.colour d = .white) (hp : 3 ≤ (G.vertexOf d).card)
    (hq : 3 ≤ (G.vertexOf (G.inv d)).card) {DP : Finset H → Finset (Sym2 H)}
    {DQ : Finset (({d, G.inv d} : Set H)ᶜ : Set H) →
      Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H))}
    (hDP : G.IsWhiteDatum DP) (hDQ : (G.contractEdge d (he.leg_mem hG)).IsWhiteDatum DQ)
    (hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) = DP x)
    (hglue : (DQ ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
      (Sym2.map Subtype.val) = G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d)))) :
    (G.strandDiagram hG hDP).Isomorphic
      ((G.contractEdge d (he.leg_mem hG)).strandDiagram (hG.contractEdge he) hDQ) := by
  set Q := G.contractEdge d (he.leg_mem hG)
  have hQ : Q.IsPlabicGraph := hG.contractEdge he
  set f : Q.StrandDart DQ → G.StrandDart DP := fun a =>
    ⟨glueSym G d a.1, isStrandSymbol_glueSym hG he hw hp hq hDP hDQ hglue hrel a.2⟩ with hf
  have hbij : Bijective f := by
    refine ⟨fun a a' h => Subtype.ext ?_, fun a => ?_⟩
    · have h' : glueSym G d a.1 = glueSym G d a'.1 := congrArg Subtype.val h
      have := congrArg (glueInvSym G d DP) h'
      rw [glueInvSym_glueSym hG he hw hp hq hDP hDQ hglue hrel a.2,
        glueInvSym_glueSym hG he hw hp hq hDP hDQ hglue hrel a'.2] at this
      exact strandSymbol_map_injective _ this
    · obtain ⟨a', ha', e⟩ := exists_glueSym_eq (hleg := he.leg_mem hG) hG he hw hp hq hDP hglue hrel
        a.2
      exact ⟨⟨a', ha'⟩, Subtype.ext e⟩
  set θ := Equiv.ofBijective f hbij
  have θval : ∀ a, (θ a).1 = glueSym G d a.1 := fun _ => rfl
  refine TripleData.Isomorphic.symm _
    (strandDiagram_isomorphic_of' hQ hDQ (G.strandDiagram hG hDP) θ ?_ ?_ ?_ ?_ ?_)
  · refine strandDiagram_map_inv_of' hQ hDQ
      (isPreTripleDiagram_strandDiagram hG hDP).inv_involutive _ fun a hform => ?_
    apply Subtype.ext
    rw [θval, strandDiagram_inv_apply, strandDiagram_inv_apply, θval]
    exact glueSym_strandInvSym hG he hw hp hq hDP hDQ hglue hrel a.2 hform
  · intro a
    apply Subtype.ext
    rw [θval, strandDiagram_rot_apply, strandDiagram_rot_apply, θval]
    exact glueSym_strandRotSym hG he hw hp hq hDP hDQ hglue hrel a.2
  · intro a
    rw [mem_strandDiagram_bdry, θval]
    exact (glueSym_isBoundary_and_isOut a.1).1
  · intro a _
    rw [strandDiagram_isOut, θval]
    exact (glueSym_isBoundary_and_isOut a.1).2
  · exact fun r => Subtype.ext (glueSym_endSymbol hG r)

omit [Fintype H] in
private theorem image_preimage_sym2 {E : Finset (Sym2 H)}
    (h : ∀ e ∈ E, ∀ x ∈ e, x ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (E.preimage (Sym2.map (Subtype.val : (({d, G.inv d} : Set H)ᶜ : Set H) → H))
      (Sym2.map.injective Subtype.val_injective).injOn).image (Sym2.map Subtype.val) = E := by
  ext e
  constructor
  · intro he
    obtain ⟨e', he', rfl⟩ := mem_image.1 he
    exact mem_preimage.1 he'
  · intro he
    have hY := h e he
    induction e using Sym2.ind with
    | _ u v =>
      exact mem_image.2 ⟨s(⟨u, hY u (Sym2.mem_mk_left _ _)⟩, ⟨v, hY v (Sym2.mem_mk_right _ _)⟩),
        mem_preimage.2 he, rfl⟩

/-- A crossing of `G` other than `v(d)`, `v(d̄)` is the vertex of a dart away from them. -/
private theorem exists_notMem_of_isCrossing {x : Finset H} (hx : G.IsCrossing x)
    (h1 : x ≠ G.vertexOf d) (h2 : x ≠ G.vertexOf (G.inv d)) :
    ∃ z, x = G.vertexOf z ∧ z ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  obtain ⟨z, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hx.1).1
  refine ⟨z, rfl, fun hz => ?_⟩
  rcases mem_union.1 hz with h | h
  · exact h1 (G.vertexOf_eq_of_mem h)
  · exact h2 (G.vertexOf_eq_of_mem h)

/-- **Contracting an edge between two crossings**. Let `P` be a plabic graph, `{d, d̄}` an edge
whose ends `v(d) ≠ v(d̄)` are white internal vertices with at least three darts each, and `Q` the
contraction along it. Then every generalized triple diagram of `P` is a generalized triple diagram
of `Q`. -/
@[cluster_algebras "lem_generalized_white_contraction"]
theorem IsGeneralizedTripleDiagram.contractEdge_white (hG : G.IsPlabicGraph)
    (he : G.IsContractibleEdge d) (hw : G.colour d = .white) (hp : 3 ≤ (G.vertexOf d).card)
    (hq : 3 ≤ (G.vertexOf (G.inv d)).card) {H'' : Type*} [Fintype H'']
    [DecidableEq H''] {X : TripleData H'' b} (hX : G.IsGeneralizedTripleDiagram hG X) :
    (G.contractEdge d (he.leg_mem hG)).IsGeneralizedTripleDiagram (hG.contractEdge he) X := by
  obtain ⟨hpre, horb, DP, hDP, ⟨φ⟩⟩ := hX
  set Q := G.contractEdge d (he.leg_mem hG)
  set v' := (G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))
  have hc1 := isCrossing_vertexOf_end hG he hw hp hq (Or.inl rfl)
  have hc2 := isCrossing_vertexOf_end hG he hw hp hq (Or.inr rfl)
  obtain ⟨⟨D, hD, hDimg⟩, -⟩ :=
    (bijOn_cornerGlue (hleg := he.leg_mem hG) he.vertexOf_ne hp hq).mapsTo
    (show (DP (G.vertexOf d), DP (G.vertexOf (G.inv d))) ∈ {D : Finset (Sym2 H) × Finset (Sym2 H) |
      G.IsCornerTriangulation (G.vertexOf d) D.1 ∧
        G.IsCornerTriangulation (G.vertexOf (G.inv d)) D.2} from ⟨hDP _ hc1, hDP _ hc2⟩)
  set DQ : Finset (({d, G.inv d} : Set H)ᶜ : Set H) →
      Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H)) := fun x' =>
    if x' = v' then D else
      (DP (x'.map (Embedding.subtype _))).preimage (Sym2.map Subtype.val)
        (Sym2.map.injective Subtype.val_injective).injOn with hDQdef
  have hY : ∀ {x : Finset H}, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      ∀ e ∈ DP x, ∀ z ∈ e, z ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
    intro x hx h1 h2 e he' z hz
    obtain ⟨z₀, rfl, hz₀⟩ := exists_notMem_of_isCrossing hx h1 h2
    have hzx := ((hDP _ hx).1 e he').2 z hz
    apply mem_compl_pair_of_notMem
    rwa [mem_union_vertexOf_iff_of_vertexOf_eq (G.vertexOf_eq_of_mem hzx)]
  have hsub_ne : ∀ {x : Finset H}, G.IsCrossing x → x ≠ G.vertexOf d →
      x ≠ G.vertexOf (G.inv d) → x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) ≠ v' := by
    intro x hx h1 h2 h
    obtain ⟨z₀, rfl, hz₀⟩ := exists_notMem_of_isCrossing hx h1 h2
    have hz₀Y := mem_compl_pair_of_notMem hz₀
    have : (⟨z₀, hz₀Y⟩ : (({d, G.inv d} : Set H)ᶜ : Set H)) ∈ v' := by
      rw [← h, mem_subtype]; exact G.self_mem_vertexOf z₀
    rw [mem_subtype, mem_mergedVertex] at this
    exact hz₀ (mem_union.2 this.1)
  have hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (DQ (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) =
        DP x := by
    intro x hx h1 h2
    have hxY : ∀ z ∈ x, z ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
      obtain ⟨z₀, rfl, hz₀⟩ := exists_notMem_of_isCrossing hx h1 h2
      intro z hz
      apply mem_compl_pair_of_notMem
      rwa [mem_union_vertexOf_iff_of_vertexOf_eq (G.vertexOf_eq_of_mem hz)]
    rw [hDQdef]
    simp only
    rw [if_neg (hsub_ne hx h1 h2), subtype_map_of_mem hxY]
    exact image_preimage_sym2 (hY hx h1 h2)
  have hglue : (DQ v').image (Sym2.map Subtype.val) =
      G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))) := by
    rw [hDQdef]
    simp only
    exact hDimg
  have hDQ : Q.IsWhiteDatum DQ := by
    intro x' hx'
    rcases isCrossing_contractEdge_cases he hx' with rfl | ⟨y, rfl, hy, hc⟩
    · have hDQv : DQ v' = D := if_pos rfl
      rw [hDQv]
      exact hD
    · have hx1 : G.vertexOf y ≠ G.vertexOf d := fun h =>
        hy (mem_union_left _ (h ▸ G.self_mem_vertexOf _))
      have hx2 : G.vertexOf y ≠ G.vertexOf (G.inv d) := fun h =>
        hy (mem_union_right _ (h ▸ G.self_mem_vertexOf _))
      have hsub : (G.vertexOf (y : H)).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) =
          Q.vertexOf y := by
        rw [← map_vertexOf_of_notMem (hleg := he.leg_mem hG) he hy, subtype_map_subtype]
      rw [isCornerTriangulation_iff_of_notMem he hy, map_sym2Map_subtype_eq_image, ← hsub,
        hrel _ hc hx1 hx2]
      exact hDP _ hc
  refine ⟨hpre, (exists_isInitial_mem_trip_contractEdge_iff hG he hw hp hq).1 horb, DQ, hDQ, ?_⟩
  obtain ⟨ψ⟩ := strandDiagram_isomorphic_contractEdge hG he hw hp hq hDP hDQ hrel hglue
  exact ⟨φ.trans ψ⟩

/-- **Splitting a crossing along a diagonal**. Let `P` be a plabic graph, `{d, d̄}` an edge whose
ends `v(d) ≠ v(d̄)` are white internal vertices with at least three darts each, and `Q` the
contraction along it, with merged vertex `v`. Let `D` be a white datum of `Q` with `γ_e ∈ D_v`
(read in `P`), and suppose that every trip of `Q` contains an initial dart. Then `X°(Q, D)` is a
generalized triple diagram of `P`. -/
@[cluster_algebras "lem_generalized_white_split"]
theorem isGeneralizedTripleDiagram_of_contractEdge_white (hG : G.IsPlabicGraph)
    (he : G.IsContractibleEdge d) (hw : G.colour d = .white) (hp : 3 ≤ (G.vertexOf d).card)
    (hq : 3 ≤ (G.vertexOf (G.inv d)).card)
    {D : Finset (({d, G.inv d} : Set H)ᶜ : Set H) → Finset (Sym2 (({d, G.inv d} : Set H)ᶜ : Set H))}
    (hD : (G.contractEdge d (he.leg_mem hG)).IsWhiteDatum D)
    (hγ : G.cornerGlueDiagonal d ∈
      (D ((G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image
        (Sym2.map Subtype.val))
    (horb : ∀ y ∉ (G.contractEdge d (he.leg_mem hG)).bdry,
      ∃ e ∈ (G.contractEdge d (he.leg_mem hG)).trip y,
        (G.contractEdge d (he.leg_mem hG)).IsInitial e) :
    G.IsGeneralizedTripleDiagram hG
      ((G.contractEdge d (he.leg_mem hG)).strandDiagram (hG.contractEdge he) hD) := by
  set Q := G.contractEdge d (he.leg_mem hG)
  have hQ : Q.IsPlabicGraph := hG.contractEdge he
  set v' := (G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))
  obtain ⟨⟨D₁, D₂⟩, ⟨hD₁, hD₂⟩, hglue₀⟩ :=
    (bijOn_cornerGlue (hleg := he.leg_mem hG) he.vertexOf_ne hp hq).surjOn
      (show (D v').image (Sym2.map Subtype.val) ∈ {E | (∃ D' : Finset (Sym2 (({d, G.inv d} :
        Set H)ᶜ : Set H)), Q.IsCornerTriangulation v' D' ∧ D'.image (Sym2.map Subtype.val) = E) ∧
          G.cornerGlueDiagonal d ∈ E} from
        ⟨⟨D v', hD _ (isCrossing_merged hG he hw hp hq), rfl⟩, hγ⟩)
  have hglue₀' : G.cornerGlue d D₁ D₂ = (D v').image (Sym2.map Subtype.val) := hglue₀
  set DP : Finset H → Finset (Sym2 H) := fun x =>
    if x = G.vertexOf d then D₁ else if x = G.vertexOf (G.inv d) then D₂ else
      (D (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val)
    with hDPdef
  have hDP1 : DP (G.vertexOf d) = D₁ := by simp only [hDPdef, ↓reduceIte]
  have hDP2 : DP (G.vertexOf (G.inv d)) = D₂ := by
    simp only [hDPdef, if_neg he.vertexOf_ne.symm, ↓reduceIte]
  have hrel : ∀ x, G.IsCrossing x → x ≠ G.vertexOf d → x ≠ G.vertexOf (G.inv d) →
      (D (x.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))).image (Sym2.map Subtype.val) =
        DP x := by
    intro x _ h1 h2
    simp only [hDPdef, if_neg h1, if_neg h2]
  have hglue : (D v').image (Sym2.map Subtype.val) =
      G.cornerGlue d (DP (G.vertexOf d)) (DP (G.vertexOf (G.inv d))) := by
    rw [hDP1, hDP2, hglue₀']
  have hDP : G.IsWhiteDatum DP := by
    intro x hx
    by_cases h1 : x = G.vertexOf d
    · rw [h1, hDP1]; exact hD₁
    by_cases h2 : x = G.vertexOf (G.inv d)
    · rw [h2, hDP2]; exact hD₂
    obtain ⟨z, rfl, hz⟩ := exists_notMem_of_isCrossing hx h1 h2
    set y : (({d, G.inv d} : Set H)ᶜ : Set H) := ⟨z, mem_compl_pair_of_notMem hz⟩
    have hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := hz
    have hsub : (G.vertexOf (y : H)).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) =
        Q.vertexOf y := by
      rw [← map_vertexOf_of_notMem (hleg := he.leg_mem hG) he hy, subtype_map_subtype]
    have hcQ : Q.IsCrossing (Q.vertexOf y) := (isCrossing_iff_of_notMem he hy).2 hx
    have := (isCornerTriangulation_iff_of_notMem he hy).1 (hD _ hcQ)
    rwa [map_sym2Map_subtype_eq_image, ← hsub, hrel _ hx h1 h2] at this
  refine ⟨isPreTripleDiagram_strandDiagram hQ hD,
    (exists_isInitial_mem_trip_contractEdge_iff hG he hw hp hq).2 horb, DP, hDP, ?_⟩
  exact TripleData.Isomorphic.symm _
    (strandDiagram_isomorphic_contractEdge hG he hw hp hq hDP hD hrel hglue)

end Glue

/-! ### Local moves and generalized triple diagrams -/

section CircMoves

omit [DecidableEq H] in
private theorem coe_firstReturn_congr {X : Type*} [Finite X] {π π' : Equiv.Perm X} {Y Y' : Set X}
    (hπ : π = π') (hY : Y = Y') (y : Y) (y' : Y') (h : (y : X) = y') :
    (firstReturn π Y y : X) = firstReturn π' Y' y' := by
  subst hπ hY
  rw [Subtype.ext h]

/-- An isomorphism from a bijection of darts commuting with the involutions and the rotations,
matching `B` with `B'` and the colours of internal vertices, and mapping `leg i` to `leg' i`. -/
private def isoOfMapLeg' {H' : Type*} [Fintype H'] [DecidableEq H'] {G : PlabicData H b}
    {G' : PlabicData H' b} (e : H ≃ H')
    (map_inv : ∀ d, e (G.inv d) = G'.inv (e d)) (map_rot : ∀ d, e (G.rot d) = G'.rot (e d))
    (mem_bdry_iff : ∀ d, e d ∈ G'.bdry ↔ d ∈ G.bdry)
    (map_colour : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) → G'.colour (e d) = G.colour d)
    (map_leg : ∀ i, e (G.leg i) = G'.leg i) : G.Iso G' where
  toEquiv := e
  map_inv := map_inv
  map_rot := map_rot
  mem_bdry_iff := mem_bdry_iff
  map_colour := map_colour
  map_bvertex i := by
    rw [bvertex, bvertex, ← map_leg, ← map_vertexOf_of_semiconj e map_rot]
    ext y
    simp only [mem_map_equiv, mem_filter]
    rw [← mem_bdry_iff (e.symm y), Equiv.apply_symm_apply]

variable {G : PlabicData H b} {d : H}

private theorem IsContractibleEdge.inv_of_involutive (hinv : Involutive G.inv)
    (he : G.IsContractibleEdge d) : G.IsContractibleEdge (G.inv d) where
  vertexOf_ne := by rw [hinv]; exact he.vertexOf_ne.symm
  mem_internalVertices := he.inv_mem_internalVertices
  inv_mem_internalVertices := by rw [hinv]; exact he.mem_internalVertices
  colour_inv := by rw [hinv]; exact he.colour_inv.symm

/-- The contractions along `d` and along `d̄` are the same tuple. -/
private noncomputable def contractEdgeInvIso' (hinv : Involutive G.inv)
    {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}
    {hleg' : ∀ i, G.leg i ∈ (({G.inv d, G.inv (G.inv d)} : Set H)ᶜ : Set H)} :
    (G.contractEdge d hleg).Iso (G.contractEdge (G.inv d) hleg') :=
  have hY : (({d, G.inv d} : Set H)ᶜ : Set H) =
      (({G.inv d, G.inv (G.inv d)} : Set H)ᶜ : Set H) := by
    rw [hinv, Set.pair_comm]
  have hmem : ∀ x : H, x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) ↔
      x ∈ (({G.inv d, G.inv (G.inv d)} : Set H)ᶜ : Set H) := fun x => by rw [hY]
  isoOfMapLeg' (Equiv.subtypeEquivRight hmem)
    (fun x => Subtype.ext (by
      change ((G.contractEdge d hleg).inv x : H) = ((G.contractEdge (G.inv d) hleg').inv _ : H)
      rw [coe_contractEdge_inv hinv, coe_contractEdge_inv hinv]
      rfl))
    (fun x => Subtype.ext (by
      change (firstReturn (G.rot * Equiv.swap d (G.inv d)) _ x : H) =
        (firstReturn (G.rot * Equiv.swap (G.inv d) (G.inv (G.inv d))) _ _ : H)
      exact coe_firstReturn_congr (by rw [hinv, Equiv.swap_comm]) hY _ _ rfl))
    (fun x => by
      rw [mem_contractEdge_bdry, mem_contractEdge_bdry]
      rfl)
    (fun _ _ => rfl)
    (fun _ => rfl)

/-- If one end of the edge is bivalent, contracting it does not change the generalized triple
diagrams. -/
private theorem isGeneralizedTripleDiagram_contractEdge_iff_of_two (hG : G.IsPlabicGraph)
    (he : G.IsContractibleEdge d)
    (h2 : (G.vertexOf d).card = 2 ∨ (G.vertexOf (G.inv d)).card = 2) {H'' : Type*} [Fintype H'']
    [DecidableEq H''] (X : TripleData H'' b) :
    G.IsGeneralizedTripleDiagram hG X ↔
      (G.contractEdge d (he.leg_mem hG)).IsGeneralizedTripleDiagram (hG.contractEdge he) X := by
  have hinv := hG.inv_involutive
  have hrem : ∀ {a : H} (ha : G.IsContractibleEdge a), (G.vertexOf a).card = 2 →
      (G.IsGeneralizedTripleDiagram hG X ↔
        (G.contractEdge a (ha.leg_mem hG)).IsGeneralizedTripleDiagram (hG.contractEdge ha) X) := by
    intro a ha h2a
    have hd : G.IsBivalentRemovable a :=
      ⟨ha.not_isBoundaryVertex, h2a, fun h => ha.vertexOf_ne
        (by rw [h, G.vertexOf_rot])⟩
    obtain ⟨θ⟩ := contractEdge_isomorphic_bivalentRemoval (hleg := ha.leg_mem hG) hG ha hd
    rw [isGeneralizedTripleDiagram_bivalentRemoval_iff hG hd X]
    exact (θ.isGeneralizedTripleDiagram_iff (hG.contractEdge ha)
      (isPlabicGraph_bivalentRemoval hG hd) X).symm
  rcases h2 with h2 | h2
  · exact hrem he h2
  · have he' := IsContractibleEdge.inv_of_involutive hinv he
    rw [hrem he' h2]
    exact ((contractEdgeInvIso' hinv (hleg := he.leg_mem hG)
      (hleg' := he'.leg_mem hG)).isGeneralizedTripleDiagram_iff
        (hG.contractEdge he) (hG.contractEdge he') X).symm

/-- The two ends of an edge of a plabic graph are not both leaves. -/
private theorem not_card_eq_one_and_card_eq_one (hG : G.IsPlabicGraph)
    (he : G.IsContractibleEdge d) :
    ¬((G.vertexOf d).card = 1 ∧ (G.vertexOf (G.inv d)).card = 1) := by
  rintro ⟨h1, h2⟩
  have hinv := hG.inv_involutive
  have hfix : ∀ x : H, (G.vertexOf x).card = 1 → G.rot x = x := by
    intro x hx
    obtain ⟨y, hy⟩ := card_eq_one.1 hx
    have h1 := G.rot_mem_vertexOf x
    have h2 := G.self_mem_vertexOf x
    rw [hy, mem_singleton] at h1 h2
    rw [h1, h2]
  have hS : ∀ e : H, G.Reach d e → e = d ∨ e = G.inv d := by
    intro e h
    induction h with
    | refl => exact Or.inl rfl
    | rot _ ih =>
      rcases ih with rfl | rfl
      · exact Or.inl (hfix _ h1)
      · exact Or.inr (hfix _ h2)
    | inv _ ih =>
      rcases ih with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (hinv _)
  have hb : 0 < b := hG.one_le
  obtain ⟨hl1, hl2⟩ := mem_compl_pair_iff.1 (he.leg_mem hG ⟨0, hb⟩)
  rcases hS _ (hG.toIsDiskMap.toIsConnected.reach d (G.leg ⟨0, hb⟩)) with h | h
  · exact hl1 h
  · exact hl2 h

/-- **Contractions and splittings of an edge** in the relation `∘∼`: if the edge does not join a
white internal leaf to a white vertex with at least three darts, every generalized triple diagram
of `G` (resp. of the contraction) that is a triple diagram is move-equivalent to one of the
contraction (resp. of `G`). -/
private theorem exists_moveEquivalent_contractEdge (hG : G.IsPlabicGraph)
    (he : G.IsContractibleEdge d) (hnl : ¬G.IsWhiteLeafEdge d) (X : TripleDiagram b) :
    (G.IsGeneralizedTripleDiagram hG X.data → ∃ X' : TripleDiagram b,
      (G.contractEdge d (he.leg_mem hG)).IsGeneralizedTripleDiagram (hG.contractEdge he) X'.data ∧
        X.MoveEquivalent X') ∧
    ((G.contractEdge d (he.leg_mem hG)).IsGeneralizedTripleDiagram (hG.contractEdge he) X.data →
      ∃ X' : TripleDiagram b, G.IsGeneralizedTripleDiagram hG X'.data ∧ X.MoveEquivalent X') := by
  have hinv := hG.inv_involutive
  set Q := G.contractEdge d (he.leg_mem hG)
  have hQ : Q.IsPlabicGraph := hG.contractEdge he
  -- the same diagram works when the generalized triple diagrams of `G` and `Q` agree
  have hsame : (G.IsGeneralizedTripleDiagram hG X.data ↔ Q.IsGeneralizedTripleDiagram hQ X.data) →
      ((G.IsGeneralizedTripleDiagram hG X.data → ∃ X' : TripleDiagram b,
        Q.IsGeneralizedTripleDiagram hQ X'.data ∧ X.MoveEquivalent X') ∧
      (Q.IsGeneralizedTripleDiagram hQ X.data →
        ∃ X' : TripleDiagram b, G.IsGeneralizedTripleDiagram hG X'.data ∧
          X.MoveEquivalent X')) := fun h =>
    ⟨fun h' => ⟨X, h.1 h', TripleDiagram.MoveEquivalent.refl X⟩,
      fun h' => ⟨X, h.2 h', TripleDiagram.MoveEquivalent.refl X⟩⟩
  cases hc : G.colour d with
  | black => exact hsame (isGeneralizedTripleDiagram_contractEdge_iff hG he hc X.data)
  | white =>
    have hci : G.colour (G.inv d) = .white := he.colour_inv.trans hc
    have hp1 : 1 ≤ (G.vertexOf d).card := card_pos.2 ⟨d, G.self_mem_vertexOf d⟩
    have hq1 : 1 ≤ (G.vertexOf (G.inv d)).card := card_pos.2 ⟨_, G.self_mem_vertexOf _⟩
    by_cases h2 : (G.vertexOf d).card = 2 ∨ (G.vertexOf (G.inv d)).card = 2
    · exact hsame (isGeneralizedTripleDiagram_contractEdge_iff_of_two hG he h2 X.data)
    by_cases h3 : 3 ≤ (G.vertexOf d).card ∧ 3 ≤ (G.vertexOf (G.inv d)).card
    · obtain ⟨hp, hq⟩ := h3
      refine ⟨fun h => ⟨X, h.contractEdge_white hG he hc hp hq,
        TripleDiagram.MoveEquivalent.refl X⟩, fun h => ?_⟩
      -- the splitting: choose a corner triangulation of the merged vertex containing `γ_e`
      obtain ⟨-, horbQ, D₀, hD₀, ⟨φ⟩⟩ := h
      set v' := (G.mergedVertex d).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))
      have hc1 := isCrossing_vertexOf_end hG he hc hp hq (Or.inl rfl)
      have hc2 := isCrossing_vertexOf_end hG he hc hp hq (Or.inr rfl)
      obtain ⟨D₁, hD₁, -⟩ := hc1.exists_isCornerTriangulation_isCornerTriangle
        (G.self_mem_vertexOf d)
      obtain ⟨D₂, hD₂, -⟩ := hc2.exists_isCornerTriangulation_isCornerTriangle
        (G.self_mem_vertexOf (G.inv d))
      obtain ⟨⟨Dv, hDv, hDvimg⟩, hγ⟩ :=
        (bijOn_cornerGlue (hleg := he.leg_mem hG) he.vertexOf_ne hp hq).mapsTo
          (show (D₁, D₂) ∈ {D : Finset (Sym2 H) × Finset (Sym2 H) |
            G.IsCornerTriangulation (G.vertexOf d) D.1 ∧
              G.IsCornerTriangulation (G.vertexOf (G.inv d)) D.2} from ⟨hD₁, hD₂⟩)
      set D := Function.update D₀ v' Dv with hDdef
      have hDv' : D v' = Dv := Function.update_self _ _ _
      have hD : Q.IsWhiteDatum D := by
        intro x hx
        by_cases hxv : x = v'
        · rw [hxv, hDv']; exact hDv
        · rw [hDdef, Function.update_of_ne hxv]; exact hD₀ x hx
      have hgenD : Q.IsGeneralizedTripleDiagram hQ (Q.strandDiagram hQ hD) :=
        ⟨isPreTripleDiagram_strandDiagram hQ hD, horbQ, D, hD, TripleData.Isomorphic.refl _⟩
      obtain ⟨hXD, hmove⟩ := IsGeneralizedTripleDiagram.exists_moveEquivalent hQ
        ⟨X.isTripleDiagram.toIsPreTripleDiagram, horbQ, D₀, hD₀, ⟨φ⟩⟩ hgenD X.isTripleDiagram
      refine ⟨⟨_, Q.strandDiagram hQ hD, hXD⟩,
        isGeneralizedTripleDiagram_of_contractEdge_white hG he hc hp hq hD ?_ horbQ, hmove⟩
      rw [hDv']
      exact hDvimg ▸ hγ
    · exfalso
      have hcases : ((G.vertexOf d).card = 1 ∧ 3 ≤ (G.vertexOf (G.inv d)).card) ∨
          ((G.vertexOf (G.inv d)).card = 1 ∧ 3 ≤ (G.vertexOf d).card) ∨
          ((G.vertexOf d).card = 1 ∧ (G.vertexOf (G.inv d)).card = 1) := by omega
      rcases hcases with ⟨h1, h3'⟩ | ⟨h1, h3'⟩ | h11
      · exact hnl (Or.inl ⟨⟨he.mem_internalVertices, h1⟩, hc, hci, h3'⟩)
      · exact hnl (Or.inr ⟨⟨he.inv_mem_internalVertices, h1⟩, hci, hc, h3'⟩)
      · exact not_card_eq_one_and_card_eq_one hG he h11

/-! #### Square moves at a white corner -/

omit [Fintype H] [DecidableEq H] in
private theorem squareCorner_facePerm {c : H} (hc4 : (G.facePerm ^ 4) c = c) (k : Fin 4) :
    G.squareCorner (G.facePerm c) k = G.squareCorner c (k + 1) := by
  have hs : ∀ n : ℕ, (G.facePerm ^ n) (G.facePerm c) = (G.facePerm ^ (n + 1)) c := fun n => by
    rw [pow_succ, Equiv.Perm.mul_apply]
  unfold squareCorner
  rw [hs]
  fin_cases k
  · rfl
  · rfl
  · rfl
  · change (G.facePerm ^ 4) c = (G.facePerm ^ 0) c
    rw [hc4]
    rfl

private theorem squareVertices_facePerm {c : H} (hc4 : (G.facePerm ^ 4) c = c) :
    G.squareVertices (G.facePerm c) = G.squareVertices c := by
  ext v
  simp only [mem_squareVertices, squareCorner_facePerm hc4]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k - 1, by rw [sub_add_cancel]⟩

private theorem squareMove_facePerm {c : H} (hc4 : (G.facePerm ^ 4) c = c) :
    G.squareMove (G.facePerm c) = G.squareMove c := by
  unfold squareMove
  rw [squareVertices_facePerm hc4]

private theorem IsSquareMoveFace.facePerm {c : H} (hq : G.IsSquareMoveFace c) :
    G.IsSquareMoveFace (G.facePerm c) where
  faceOf_mem_internalFaces := by
    rw [RotationSystem.faceOf_facePerm]; exact hq.faceOf_mem_internalFaces
  facePerm_pow_four := by
    rw [← Equiv.Perm.mul_apply, ← pow_succ, pow_succ', Equiv.Perm.mul_apply,
      hq.facePerm_pow_four]
  vertexOf_mem_internalVertices k := by
    rw [squareCorner_facePerm hq.facePerm_pow_four]
    exact hq.vertexOf_mem_internalVertices (k + 1)
  injective k l h := by
    simp only [squareCorner_facePerm hq.facePerm_pow_four] at h
    exact add_right_cancel (hq.injective h)
  card_vertexOf k := by
    rw [squareCorner_facePerm hq.facePerm_pow_four]
    exact hq.card_vertexOf (k + 1)
  colour_ne k := by
    rw [squareCorner_facePerm hq.facePerm_pow_four, squareCorner_facePerm hq.facePerm_pow_four]
    exact hq.colour_ne (k + 1)

/-- A square move is a square move at a face whose first corner is white. -/
private theorem IsSquareMoveFace.exists_white {c : H} (hq : G.IsSquareMoveFace c) :
    ∃ c', G.IsSquareMoveFace c' ∧ G.colour c' = .white ∧ G.squareMove c' = G.squareMove c := by
  cases hc : G.colour c with
  | white => exact ⟨c, hq, hc, rfl⟩
  | black =>
    refine ⟨G.facePerm c, hq.facePerm, ?_, squareMove_facePerm hq.facePerm_pow_four⟩
    have h := hq.colour_ne 0
    change G.colour c ≠ G.colour (G.facePerm c) at h
    rw [hc] at h
    cases h' : G.colour (G.facePerm c) with
    | white => rfl
    | black => exact absurd h'.symm h

private theorem isGeneralizedTripleDiagram_of_eq {G' : PlabicData H b} (h : G = G')
    (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) {H'' : Type*} [Fintype H''] [DecidableEq H'']
    {X : TripleData H'' b} (hX : G.IsGeneralizedTripleDiagram hG X) :
    G'.IsGeneralizedTripleDiagram hG' X := by
  subst h
  exact hX

end CircMoves

/-! ### Loops at black vertices -/

section Loop

variable {G : PlabicData H b}

omit [Fintype H] in
/-- A corner triangulation of a set of three darts is empty. -/
private theorem isCornerTriangulation_eq_empty' {w : Finset H} {E : Finset (Sym2 H)}
    (hE : G.IsCornerTriangulation w E) (h3 : w.card = 3) : E = ∅ := by
  obtain ⟨hEw, m, _, l, hl, hT⟩ := hE
  have hm : m = 3 := hl.card_eq.symm.trans h3
  rw [← hl.image_cornerPullback fun e he => (hEw e he).2,
    IsTriangulation.eq_empty_of_eq_three hm hT, image_empty]

/-- When every crossing has three darts, a white datum has no segments. -/
private theorem not_isDatumSegment_of_three {D : Finset H → Finset (Sym2 H)}
    (hD : G.IsWhiteDatum D) (h3 : ∀ w, G.IsCrossing w → w.card = 3) {s : Sym2 H}
    {τ : Finset H} : ¬G.IsDatumSegment D s τ := by
  rintro ⟨w, hw, hs, -, -⟩
  rw [isCornerTriangulation_eq_empty' (hD w hw) (h3 w hw)] at hs
  exact notMem_empty _ hs

/-- When every crossing has three darts, the pairs of a triangle of a white datum are `x`-symbols,
and the triangle is the crossing. -/
private theorem pair_of_three {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D)
    (h3 : ∀ w, G.IsCrossing w → w.card = 3) {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H}
    (hp : p ∈ τ) :
    G.pairOut τ p = xPlus p ∧ G.pairIn τ p = xMinus (G.inv p) ∧
      G.cornerNext τ (G.cornerNext τ p) ∈ G.vertexOf p ∧ G.IsCrossing (G.vertexOf p) := by
  obtain ⟨hw, ht⟩ := hτ.vertexOf hp
  have hτw : τ = G.vertexOf p := eq_of_subset_of_card_le ht.1 (by rw [h3 _ hw, ht.2.1])
  have hσ : G.rot.symm p ∈ τ := by rw [hτw]; exact G.rot_symm_mem_vertexOf p
  have hcn := hD.cornerNext_eq_rot_symm hτ hp hσ
  refine ⟨by rw [pairOut, if_pos hcn], by rw [pairIn, if_pos hcn], ?_, hw⟩
  rw [← hτw]
  exact hD.cornerNext_mem hτ (hD.cornerNext_mem hτ hp)

/-- The turn at a dart is the dart itself, its successor or its predecessor in the rotation. -/
private theorem turn_cases (z : H) :
    G.turn z = z ∨ G.turn z = G.rot z ∨ G.turn z = G.rot.symm z := by
  unfold turn
  split_ifs
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- The side of a symbol of the strand diagram with respect to a set `C` of darts: `x^±_c` lies on
the side of `c`, and the boundary symbols on the side `P₀`. -/
private def loopSide (C : H → Prop) (P₀ : Prop) : StrandSymbol H b → Prop
  | xPlus c => C c
  | xMinus t => C t
  | yPlus _ _ => False
  | yMinus _ _ => False
  | bd _ => P₀
  | bd' _ => P₀

/-- **No loop at a black vertex.** Let `G` be a plabic graph all of whose crossings have three
darts, `D` a white datum, and suppose that every trip of `G` contains an initial dart and that
`⟨σ°, d ↦ d̄⟩` acts transitively on `X°(G, D)`. Then `G` has no loop at a black internal vertex: a
loop separates the darts of `G` into two sides (`DiskMap.IsDiskMap.loop_separates`), each trip
lies on one side, and the side of the strands is invariant under `σ°` and `d ↦ d̄`. -/
private theorem false_of_black_loop (hG : G.IsPlabicGraph)
    (h3 : ∀ w, G.IsCrossing w → w.card = 3) {D : Finset H → Finset (Sym2 H)}
    (hD : G.IsWhiteDatum D) (horb : ∀ x ∉ G.bdry, ∃ e ∈ G.trip x, G.IsInitial e)
    (htrans : ∀ a a' : G.StrandDart D, (G.strandDiagram hG hD).Reach a a') {d : H}
    (hu : ¬G.IsBoundaryVertex (G.vertexOf d)) (hblack : G.colour d = .black)
    (hloop : G.vertexOf (G.inv d) = G.vertexOf d) : False := by
  have hι := hG.inv_involutive
  have hdι : G.inv d ≠ d := hG.inv_ne d
  have hιu : G.inv d ∈ G.vertexOf d := hloop ▸ G.self_mem_vertexOf _
  have hbl : ∀ z ∈ G.vertexOf d, G.colour z = .black := fun z hz =>
    (colour_eq_of_sameCycle hG hu (G.mem_vertexOf.1 hz)).trans hblack
  have hturn : ∀ z ∈ G.vertexOf d, G.turn z = G.rot z := fun z hz =>
    turn_of_black (by rwa [G.vertexOf_eq_of_mem hz]) (hbl z hz)
  have hnc : ∀ z ∈ G.vertexOf d, ¬G.IsCrossing (G.vertexOf z) := by
    intro z hz hc
    have := hc.2.1 z (G.self_mem_vertexOf z)
    rw [hbl z hz] at this
    exact Shade.noConfusion this
  have huB : ∀ z ∈ G.vertexOf d, z ∉ G.bdry := fun z hz =>
    notMem_bdry_of_mem_vertexOf hu hz
  have hnleg : ∀ z ∈ G.vertexOf d, ¬G.IsLeg z := by
    intro z hz hl
    exact hu (G.vertexOf_eq_of_mem hz ▸ hG.isBoundaryVertex_of_isLeg hl)
  have hnotinit : ∀ z ∈ G.vertexOf d, ¬G.IsInitial z := fun z hz h =>
    h.2.elim (hnc z hz) (hnleg z hz)
  have hnotterm : ∀ z, G.inv z ∈ G.vertexOf d → ¬G.IsTerminal z := by
    intro z hz h
    rcases h.2 with h' | h'
    · exact hnc _ hz h'
    · exact hu (G.vertexOf_eq_of_mem hz ▸ h')
  -- the rotation at `u = v(d)` is `(d, a₁, …, a_k, d̄, b₁, …, b_l)`
  have hsupp : d ∈ G.rot.support := by
    rw [Equiv.Perm.mem_support]
    intro h
    exact hdι ((G.mem_vertexOf.1 hιu).eq_of_left h).symm
  have hmem : G.inv d ∈ G.rot.toList d :=
    Equiv.Perm.mem_toList_iff.2 ⟨G.mem_vertexOf.1 hιu, hsupp⟩
  obtain ⟨s, bs, hst⟩ := List.append_of_mem hmem
  obtain ⟨as, hs⟩ : ∃ as, s = d :: as := by
    have h0 := Equiv.Perm.toList_getElem_zero G.rot d hsupp
    rw [List.getElem_of_eq hst] at h0
    cases s with
    | nil =>
      simp only [List.nil_append, List.getElem_cons_zero] at h0
      exact absurd h0 hdι
    | cons a as =>
      simp only [List.cons_append, List.getElem_cons_zero] at h0
      exact ⟨as, by rw [h0]⟩
  subst hs
  have hL : G.rot.toList d = d :: as ++ G.inv d :: bs := hst
  have hL' : G.rot.toList (G.inv d) = G.inv d :: bs ++ G.inv (G.inv d) :: as := by
    rw [hι d]; exact toList_eq_of_toList hL
  have hL'' : G.rot.toList (G.inv d) = G.inv d :: bs ++ d :: as := by
    rw [hL', hι d]
  have hnd := nodup_of_toList hL
  simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons, not_or,
    List.nodup_append] at hnd
  have hdas : d ∉ as := hnd.1.1
  have hdbs : d ∉ bs := hnd.1.2.2
  have hιas : G.inv d ∉ as := fun h => hnd.2.2.2 _ h _ (Or.inl rfl) rfl
  have hιbs : G.inv d ∉ bs := hnd.2.2.1.1
  have hmemu : ∀ z, z ∈ G.vertexOf d ↔ z = d ∨ z ∈ as ∨ z = G.inv d ∨ z ∈ bs := by
    intro z
    rw [G.mem_vertexOf, ← mem_toList_of_toList hL, hL]
    simp
  have hTd : G.tripMap d = G.rot (G.inv d) := by rw [tripMap_apply, hturn _ hιu]
  have hTι : G.tripMap (G.inv d) = G.rot d := by
    rw [tripMap_apply, hι, hturn _ (G.self_mem_vertexOf d)]
  -- neither side of the loop is empty
  have hk : as ≠ [] := by
    intro hk
    subst hk
    have hσ : G.rot d = G.inv d := by
      have := apply_mem_or_eq_of_toList hL (z := d) (by simp)
      simpa using this
    have hfix : ∀ n, G.tripMap^[n] (G.inv d) = G.inv d := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, hTι, hσ]
    obtain ⟨e, ⟨n, hn⟩, he⟩ := horb (G.inv d) (huB _ hιu)
    simp only at hn
    rw [hfix] at hn
    rw [← hn] at he
    exact hnotinit _ hιu he
  have hl : bs ≠ [] := by
    intro hl
    subst hl
    have hσ : G.rot (G.inv d) = d := by
      have := apply_mem_or_eq_of_toList hL'' (z := G.inv d) (by simp)
      simpa using this
    have hfix : ∀ n, G.tripMap^[n] d = d := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, hTd, hσ]
    obtain ⟨e, ⟨n, hn⟩, he⟩ := horb d (huB _ (G.self_mem_vertexOf d))
    simp only at hn
    rw [hfix] at hn
    rw [← hn] at he
    exact hnotinit _ (G.self_mem_vertexOf d) he
  have hsep := hG.toIsDiskMap.loop_separates hL hk hl
  have ha₁ : G.rot d ∈ as := apply_mem_of_toList hL hk
  have hb₁ : G.rot (G.inv d) ∈ bs := apply_mem_of_toList hL'' hl
  have hAσ : ∀ z ∈ as, G.rot z ∈ as ∨ G.rot z = G.inv d := fun z hz =>
    apply_mem_or_eq_of_toList hL (List.mem_cons_of_mem _ hz)
  have hBσ : ∀ z ∈ bs, G.rot z ∈ bs ∨ G.rot z = d := fun z hz =>
    apply_mem_or_eq_of_toList hL'' (List.mem_cons_of_mem _ hz)
  have hne_as : ∀ z ∈ as, z ≠ d ∧ z ≠ G.inv d := fun z hz =>
    ⟨fun h => hdas (h ▸ hz), fun h => hιas (h ▸ hz)⟩
  have hne_bs : ∀ z ∈ bs, z ≠ d ∧ z ≠ G.inv d := fun z hz =>
    ⟨fun h => hdbs (h ▸ hz), fun h => hιbs (h ▸ hz)⟩
  have hinvne : ∀ z, z ≠ d → z ≠ G.inv d → G.inv z ≠ d ∧ G.inv z ≠ G.inv d := by
    intro z h1 h2
    refine ⟨fun h => h2 ?_, fun h => h1 (hι.injective h)⟩
    rw [← h, hι]
  -- the joining relation
  set J : H → H → Prop := Relation.ReflTransGen (G.ArcLoopStep d as bs) with hJ
  have hsymm : ∀ {x y : H}, J x y → J y x := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hbc.symm hι) ih
  -- a dart is joined to the next dart of its trip other than `d`, `d̄`
  have hstep : ∀ z, z ≠ d → z ≠ G.inv d →
      ((G.tripMap z ≠ d ∧ G.tripMap z ≠ G.inv d) → J z (G.tripMap z)) ∧
      ((G.tripMap z = d ∨ G.tripMap z = G.inv d) →
        G.tripMap (G.tripMap z) ≠ d ∧ G.tripMap (G.tripMap z) ≠ G.inv d ∧
          J z (G.tripMap (G.tripMap z))) := by
    intro z hz1 hz2
    obtain ⟨hzi1, hzi2⟩ := hinvne z hz1 hz2
    have hinvstep : G.ArcLoopStep d as bs z (G.inv z) := ⟨hz1, hz2, hzi1, hzi2, Or.inl rfl⟩
    have hT : G.tripMap z = G.turn (G.inv z) := tripMap_apply z
    refine ⟨fun ⟨hT1, hT2⟩ => ?_, fun hTd' => ?_⟩
    · have h2 : J (G.inv z) (G.tripMap z) := by
        by_cases hziu : G.inv z ∈ G.vertexOf d
        · rw [hT, hturn _ hziu] at hT1 hT2 ⊢
          rcases (hmemu _).1 hziu with h | h | h | h
          · exact absurd h hzi1
          · rcases hAσ _ h with h' | h'
            · exact Relation.ReflTransGen.single
                ⟨hzi1, hzi2, hT1, hT2, Or.inr (Or.inr (Or.inl ⟨h, h'⟩))⟩
            · exact absurd h' hT2
          · exact absurd h hzi2
          · rcases hBσ _ h with h' | h'
            · exact Relation.ReflTransGen.single
                ⟨hzi1, hzi2, hT1, hT2, Or.inr (Or.inr (Or.inr ⟨h, h'⟩))⟩
            · exact absurd h' hT1
        · rw [hT] at hT1 hT2 ⊢
          rcases turn_cases (G.inv z) with h | h | h
          · rw [h]
          · rw [h] at hT1 hT2 ⊢
            exact Relation.ReflTransGen.single
              ⟨hzi1, hzi2, hT1, hT2, Or.inr (Or.inl ⟨Or.inl rfl, hziu⟩)⟩
          · rw [h] at hT1 hT2 ⊢
            exact Relation.ReflTransGen.single
              ⟨hzi1, hzi2, hT1, hT2, Or.inr (Or.inl ⟨Or.inr rfl, hziu⟩)⟩
      exact (Relation.ReflTransGen.single hinvstep).trans h2
    · have hTu : G.tripMap z ∈ G.vertexOf d :=
        hTd'.elim (fun h => h ▸ G.self_mem_vertexOf d) (fun h => h ▸ hιu)
      have hziu : G.inv z ∈ G.vertexOf d := by
        have h1 : G.tripMap z ∈ G.vertexOf (G.inv z) := turn_mem_vertexOf _
        have h2 : G.vertexOf (G.inv z) = G.vertexOf d :=
          (G.vertexOf_eq_of_mem h1).symm.trans (G.vertexOf_eq_of_mem hTu)
        rw [← h2]
        exact G.self_mem_vertexOf _
      rw [hT, hturn _ hziu] at hTd' ⊢
      rcases (hmemu _).1 hziu with h | h | h | h
      · exact absurd h hzi1
      · have hw' : G.rot (G.inv z) = G.inv d := by
          rcases hAσ _ h with h' | h'
          · rcases hTd' with h'' | h''
            · exact absurd (h'' ▸ h') hdas
            · exact absurd (h'' ▸ h') hιas
          · exact h'
        rw [hw', hTι]
        refine ⟨(hne_as _ ha₁).1, (hne_as _ ha₁).2, ?_⟩
        exact (Relation.ReflTransGen.single hinvstep).tail
          ⟨hzi1, hzi2, (hne_as _ ha₁).1, (hne_as _ ha₁).2, Or.inr (Or.inr (Or.inl ⟨h, ha₁⟩))⟩
      · exact absurd h hzi2
      · have hw' : G.rot (G.inv z) = d := by
          rcases hBσ _ h with h' | h'
          · rcases hTd' with h'' | h''
            · exact absurd (h'' ▸ h') hdbs
            · exact absurd (h'' ▸ h') hιbs
          · exact h'
        rw [hw', hTd]
        refine ⟨(hne_bs _ hb₁).1, (hne_bs _ hb₁).2, ?_⟩
        exact (Relation.ReflTransGen.single hinvstep).tail
          ⟨hzi1, hzi2, (hne_bs _ hb₁).1, (hne_bs _ hb₁).2, Or.inr (Or.inr (Or.inr ⟨h, hb₁⟩))⟩
  -- the darts of a trip other than `d`, `d̄` are joined
  have htrip : ∀ z₀, z₀ ≠ d → z₀ ≠ G.inv d → ∀ n : ℕ,
      ((G.tripMap^[n] z₀ ≠ d ∧ G.tripMap^[n] z₀ ≠ G.inv d) → J z₀ (G.tripMap^[n] z₀)) ∧
      ((G.tripMap^[n] z₀ = d ∨ G.tripMap^[n] z₀ = G.inv d) →
        J z₀ (G.tripMap^[n + 1] z₀)) := by
    intro z₀ h1 h2 n
    induction n with
    | zero =>
      refine ⟨fun _ => Relation.ReflTransGen.refl, fun h => ?_⟩
      rcases h with h | h
      · exact absurd h h1
      · exact absurd h h2
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      set y := G.tripMap^[n] z₀
      by_cases hy : y ≠ d ∧ y ≠ G.inv d
      · have hJy := ih.1 hy
        obtain ⟨hs1, hs2⟩ := hstep y hy.1 hy.2
        refine ⟨fun h => hJy.trans (hs1 h), fun h => ?_⟩
        rw [Function.iterate_succ_apply']
        exact hJy.trans (hs2 h).2.2
      · have hy' : y = d ∨ y = G.inv d := by tauto
        have hJ := ih.2 hy'
        rw [Function.iterate_succ_apply'] at hJ
        have hTy : G.tripMap y ≠ d ∧ G.tripMap y ≠ G.inv d := by
          rcases hy' with h | h
          · rw [h, hTd]; exact hne_bs _ hb₁
          · rw [h, hTι]; exact hne_as _ ha₁
        refine ⟨fun _ => hJ, fun h => ?_⟩
        rcases h with h | h
        · exact absurd h hTy.1
        · exact absurd h hTy.2
  -- the chain from an initial dart stays on one side
  have hchain : ∀ c, G.IsInitial c → J c (G.chainEnd c) := by
    intro c hc
    have hc1 : c ≠ d := fun h => hnotinit d (G.self_mem_vertexOf d) (h ▸ hc)
    have hc2 : c ≠ G.inv d := fun h => hnotinit _ hιu (h ▸ hc)
    have ht := hc.isTerminal_chainEnd hG
    have ht1 : G.chainEnd c ≠ d := fun h => hnotterm d hιu (h ▸ ht)
    have ht2 : G.chainEnd c ≠ G.inv d := fun h =>
      hnotterm (G.inv d) (by rw [hι]; exact G.self_mem_vertexOf d) (h ▸ ht)
    rw [chainEnd_def] at ht1 ht2 ⊢
    exact (htrip c hc1 hc2 _).1 ⟨ht1, ht2⟩
  -- darts at boundary vertices are joined to a dart `x₀` of the exterior
  have hbv : ∀ x, G.IsBoundaryVertex (G.vertexOf x) →
      x ∉ G.vertexOf d ∧ x ≠ d ∧ x ≠ G.inv d := by
    intro x hx
    have hxu : x ∉ G.vertexOf d := fun h => hu (G.vertexOf_eq_of_mem h ▸ hx)
    exact ⟨hxu, fun h => hxu (h ▸ G.self_mem_vertexOf d), fun h => hxu (h ▸ hιu)⟩
  have hrotstep : ∀ x, G.IsBoundaryVertex (G.vertexOf x) →
      G.ArcLoopStep d as bs x (G.rot x) := by
    intro x hx
    have hx' : G.IsBoundaryVertex (G.vertexOf (G.rot x)) := by rwa [G.vertexOf_rot]
    exact ⟨(hbv x hx).2.1, (hbv x hx).2.2, (hbv _ hx').2.1, (hbv _ hx').2.2,
      Or.inr (Or.inl ⟨Or.inl rfl, (hbv x hx).1⟩)⟩
  have hrotpow : ∀ x, G.IsBoundaryVertex (G.vertexOf x) → ∀ n : ℕ, J x ((G.rot ^ n) x) := by
    intro x hx n
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
      have hv : G.vertexOf ((G.rot ^ n) x) = G.vertexOf x :=
        G.vertexOf_eq_of_mem (G.mem_vertexOf.2 ⟨n, by simp⟩)
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.tail (hrotstep _ (hv ▸ hx))
  obtain ⟨x₀, hx₀⟩ := G.mem_faceOrbits.1 hG.exterior_mem_faceOrbits
  have hextB : ∀ e ∈ G.exterior, e ∈ G.bdry := fun e he => G.exterior_subset_bdry he
  have hφstep : ∀ e ∈ G.exterior, J e (G.facePerm e) := by
    intro e he
    have heB := hextB e he
    have hv : G.IsBoundaryVertex (G.vertexOf e) := G.isBoundaryVertex_vertexOf_of_mem heB
    have hv' : G.IsBoundaryVertex (G.vertexOf (G.inv e)) :=
      G.isBoundaryVertex_vertexOf_of_mem (hG.inv_mem_bdry e heB)
    rw [RotationSystem.facePerm_apply]
    exact (Relation.ReflTransGen.single ⟨(hbv e hv).2.1, (hbv e hv).2.2, (hbv _ hv').2.1,
      (hbv _ hv').2.2, Or.inl rfl⟩).tail (hrotstep _ hv')
  have hext : ∀ n : ℕ, (G.facePerm ^ n) x₀ ∈ G.exterior ∧ J x₀ ((G.facePerm ^ n) x₀) := by
    intro n
    induction n with
    | zero => exact ⟨hx₀ ▸ G.self_mem_faceOf x₀, Relation.ReflTransGen.refl⟩
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      refine ⟨?_, ih.2.trans (hφstep _ ih.1)⟩
      rw [← hx₀, G.mem_faceOf]
      exact ⟨((n + 1 : ℕ) : ℤ), by rw [zpow_natCast, pow_succ', Equiv.Perm.mul_apply]⟩
  have hbd : ∀ c, G.IsBoundaryVertex (G.vertexOf c) → J c x₀ := by
    intro c hc
    obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hc)
    obtain ⟨i', rfl⟩ := (finRotate b).surjective i
    obtain ⟨e, he, hei, -⟩ := hG.exists_exterior i'
    rw [hi] at hei
    obtain ⟨n, hn⟩ := (G.mem_vertexOf.1 hei).exists_nat_pow_eq
    have hce : J c e := hn ▸ hrotpow c hc n
    have hex : e ∈ G.faceOf x₀ := hx₀ ▸ he
    obtain ⟨m, hm⟩ := (G.mem_faceOf.1 hex).exists_nat_pow_eq
    have he₀ := (hext m).2
    rw [hm] at he₀
    exact hce.trans (hsymm he₀)
  -- the side of a dart
  set C : H → Prop := fun z => ∃ a ∈ as, J a z with hCdef
  have hCJ : ∀ {x y : H}, J x y → (C x ↔ C y) := fun hxy =>
    ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h.trans hxy⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h.trans (hsymm hxy)⟩⟩
  have hlegC : ∀ i, (C (G.leg i) ↔ C x₀) ∧ (C (G.inv (G.leg i)) ↔ C x₀) := by
    intro i
    have hlv : G.IsBoundaryVertex (G.vertexOf (G.leg i)) :=
      G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
    have h1 := hbd _ hlv
    obtain ⟨-, hl1, hl2⟩ := hbv _ hlv
    obtain ⟨hi1, hi2⟩ := hinvne _ hl1 hl2
    have h2 : J (G.inv (G.leg i)) (G.leg i) :=
      Relation.ReflTransGen.single ⟨hi1, hi2, hl1, hl2, Or.inl (hι _).symm⟩
    exact ⟨hCJ h1, hCJ (h2.trans h1)⟩
  have hendC : ∀ r, loopSide C (C x₀) (G.endSymbol r) ↔ C x₀ := by
    intro r
    rcases exists_sourceIndex_or_targetIndex r with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [endSymbol_sourceIndex]; exact (hlegC i).1
    · rw [endSymbol_targetIndex]; exact (hlegC i).2
  have hpair : ∀ {τ : Finset H}, G.IsDatumTriangle D τ → ∀ {p : H}, p ∈ τ →
      (C p ↔ C (G.inv p)) ∧ (C (G.inv p) ↔ C (G.cornerNext τ (G.cornerNext τ p))) := by
    intro τ hτ p hp
    obtain ⟨-, -, hq, hc⟩ := pair_of_three hD h3 hτ hp
    have hpu : ∀ x ∈ G.vertexOf p, x ∉ G.vertexOf d := by
      intro x hx hxu
      apply hnc x hxu
      rwa [G.vertexOf_eq_of_mem hx]
    have hne : ∀ x ∈ G.vertexOf p, x ≠ d ∧ x ≠ G.inv d := fun x hx =>
      ⟨fun h => hpu x hx (h ▸ G.self_mem_vertexOf d), fun h => hpu x hx (h ▸ hιu)⟩
    obtain ⟨hp1, hp2⟩ := hne p (G.self_mem_vertexOf p)
    obtain ⟨hi1, hi2⟩ := hinvne p hp1 hp2
    have hJi : J p (G.inv p) := Relation.ReflTransGen.single ⟨hp1, hp2, hi1, hi2, Or.inl rfl⟩
    have hJv : ∀ n : ℕ, J p ((G.rot ^ n) p) := by
      intro n
      induction n with
      | zero => exact Relation.ReflTransGen.refl
      | succ n ih =>
        have hm : (G.rot ^ n) p ∈ G.vertexOf p :=
          G.mem_vertexOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))
        have hm' : (G.rot ^ (n + 1)) p ∈ G.vertexOf p :=
          G.mem_vertexOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))
        rw [pow_succ', Equiv.Perm.mul_apply] at hm' ⊢
        exact ih.tail ⟨(hne _ hm).1, (hne _ hm).2, (hne _ hm').1, (hne _ hm').2,
          Or.inr (Or.inl ⟨Or.inl rfl, hpu _ hm⟩)⟩
    obtain ⟨n, hn⟩ := (G.mem_vertexOf.1 hq).exists_nat_pow_eq
    refine ⟨hCJ hJi, ?_⟩
    rw [← hn]
    exact hCJ ((hsymm hJi).trans (hJv n))
  have hrotS : ∀ a : G.StrandDart D,
      loopSide C (C x₀) (G.strandRotSym D a.1) ↔ loopSide C (C x₀) a.1 := by
    intro a
    rcases IsStrandSymbol.cases hG hD a.2 with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩ |
      ⟨τ, p, hτ, hp, hr⟩ | ⟨τ, p, hτ, hp, hr⟩ <;> rw [hr]
    · rw [strandRotSym_bd]; exact hendC r
    · rw [strandRotSym_bd']; exact Iff.rfl
    · rw [strandRotSym_endSymbol hG]; exact (hendC r).symm
    · obtain ⟨h1, h2, -, -⟩ := pair_of_three hD h3 hτ hp
      rw [strandRotSym_pairOut hG hτ hp, h1, h2]
      exact (hpair hτ hp).1.symm
    · obtain ⟨-, h2, -, -⟩ := pair_of_three hD h3 hτ hp
      obtain ⟨h1', -, -, -⟩ := pair_of_three hD h3 hτ
        (hD.cornerNext_mem hτ (hD.cornerNext_mem hτ hp))
      rw [strandRotSym_pairIn hG hD hτ hp, h1', h2]
      exact (hpair hτ hp).2.symm
  have hinvS : ∀ a : G.StrandDart D,
      loopSide C (C x₀) (G.strandInvSym D a.1) ↔ loopSide C (C x₀) a.1 := by
    rintro ⟨a, ha⟩
    cases a with
    | xPlus c => exact (hCJ (hchain c ha)).symm
    | xMinus t =>
      obtain ⟨h1, h2⟩ := (show G.IsTerminal t from ha).chainStart_spec hG
      have := hchain _ h1
      rw [h2] at this
      exact hCJ this
    | yPlus s τ => exact absurd ha (not_isDatumSegment_of_three hD h3)
    | yMinus s τ => exact absurd ha (not_isDatumSegment_of_three hD h3)
    | bd r => exact Iff.rfl
    | bd' r => exact Iff.rfl
  have hreach : ∀ a a' : G.StrandDart D, (G.strandDiagram hG hD).Reach a a' →
      (loopSide C (C x₀) a.1 ↔ loopSide C (C x₀) a'.1) := by
    intro a a' h
    induction h with
    | refl => exact Iff.rfl
    | rot _ ih =>
      rw [strandDiagram_rot_apply]
      exact ih.trans (hrotS _).symm
    | inv _ ih =>
      rw [strandDiagram_inv_apply]
      exact ih.trans (hinvS _).symm
  -- both sides contain an initial dart
  obtain ⟨e, ⟨n, hn⟩, he⟩ := horb _ (huB _ (G.rot_mem_vertexOf d))
  simp only at hn
  obtain ⟨e', ⟨n', hn'⟩, he'⟩ := horb _ (huB _ (hloop ▸ G.rot_mem_vertexOf (G.inv d)))
  simp only at hn'
  have hen : e ≠ d ∧ e ≠ G.inv d :=
    ⟨fun h => hnotinit d (G.self_mem_vertexOf d) (h ▸ he), fun h => hnotinit _ hιu (h ▸ he)⟩
  have hen' : e' ≠ d ∧ e' ≠ G.inv d :=
    ⟨fun h => hnotinit d (G.self_mem_vertexOf d) (h ▸ he'), fun h => hnotinit _ hιu (h ▸ he')⟩
  have hJe : J (G.rot d) e := by
    have := (htrip _ (hne_as _ ha₁).1 (hne_as _ ha₁).2 n).1 (by rw [hn]; exact hen)
    rwa [hn] at this
  have hJe' : J (G.rot (G.inv d)) e' := by
    have := (htrip _ (hne_bs _ hb₁).1 (hne_bs _ hb₁).2 n').1 (by rw [hn']; exact hen')
    rwa [hn'] at this
  have hCe : C e := ⟨_, ha₁, hJe⟩
  have hCe' : ¬C e' := fun ⟨a, ha, hae'⟩ => hsep ⟨a, ha, _, hb₁, hae'.trans (hsymm hJe')⟩
  exact hCe' ((hreach ⟨xPlus e, he⟩ ⟨xPlus e', he'⟩ (htrans _ _)).1 hCe)

/-- A pre-triple diagram transitive under `⟨σ, d ↦ d̄⟩` makes an isomorphic one transitive. -/
private theorem reach_of_iso {H₁ H₂ : Type*} [Fintype H₁] [DecidableEq H₁] [Fintype H₂]
    [DecidableEq H₂] {X : TripleData H₁ b} {Y : TripleData H₂ b} (φ : X.Iso Y)
    (htrans : ∀ x y : H₁, X.Reach x y) (a a' : H₂) : Y.Reach a a' := by
  have key : ∀ x y : H₁, X.Reach x y → Y.Reach (φ.toEquiv x) (φ.toEquiv y) := by
    intro x y h
    induction h with
    | refl => exact .refl _
    | rot _ ih => rw [φ.map_rot]; exact ih.rot
    | inv _ ih => rw [φ.map_inv]; exact ih.inv
  simpa using key _ _ (htrans (φ.toEquiv.symm a) (φ.toEquiv.symm a'))

/-- **The last stage.** Let `G` be a plabic graph whose white internal vertices have three darts,
each edge `{x, x̄}` (`x ∉ B`) of which has a black internal end, and whose edges joining two black
internal vertices are loops. Then a transitive generalized triple diagram of `G` is a triple
diagram: if `G` has no loop at a black vertex it is normal, and `X(G)` is a triple diagram; a loop
at a black vertex is impossible (`false_of_black_loop`). -/
private theorem isTripleDiagram_of_normalForm (hG : G.IsPlabicGraph)
    (h3w : ∀ x, ¬G.IsBoundaryVertex (G.vertexOf x) → G.colour x = .white →
      (G.vertexOf x).card = 3)
    (hblk : ∀ x, x ∉ G.bdry →
      (¬G.IsBoundaryVertex (G.vertexOf x) ∧ G.colour x = .black) ∨
        (¬G.IsBoundaryVertex (G.vertexOf (G.inv x)) ∧ G.colour (G.inv x) = .black))
    (hbb : ∀ x, ¬G.IsBoundaryVertex (G.vertexOf x) → G.colour x = .black →
      ¬G.IsBoundaryVertex (G.vertexOf (G.inv x)) → G.colour (G.inv x) = .black →
        G.vertexOf (G.inv x) = G.vertexOf x)
    {H'' : Type} [Fintype H''] [DecidableEq H''] {X : TripleData H'' b}
    (hgen : G.IsGeneralizedTripleDiagram hG X) (htrans : ∀ x y : H'', X.Reach x y) :
    X.IsTripleDiagram := by
  obtain ⟨hpre, horb, D, hD, ⟨φ⟩⟩ := hgen
  have h3 : ∀ w, G.IsCrossing w → w.card = 3 := by
    intro w hw
    obtain ⟨x, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hw.1).1
    exact h3w x (G.vertexOf_mem_internalVertices.1 hw.1) (hw.2.1 x (G.self_mem_vertexOf x))
  by_cases hloop : ∃ x, ¬G.IsBoundaryVertex (G.vertexOf x) ∧ G.colour x = .black ∧
      G.vertexOf (G.inv x) = G.vertexOf x
  · obtain ⟨x, hxu, hxb, hxl⟩ := hloop
    exact (false_of_black_loop hG h3 hD horb (reach_of_iso φ htrans) hxu hxb hxl).elim
  push Not at hloop
  have hnorm : G.IsNormal :=
    { colour_inv_ne := by
        intro x hx hx'
        have hxB : x ∉ G.bdry := notMem_bdry_of_mem_vertexOf hx (G.self_mem_vertexOf x)
        rcases hblk x hxB with ⟨-, hxb⟩ | ⟨-, hxb⟩
        · intro h
          rw [hxb] at h
          exact hloop x hx hxb (hbb x hx hxb hx' h)
        · intro h
          rw [hxb] at h
          exact hloop x hx h.symm (hbb x hx h.symm hx' hxb)
      card_vertexOf_of_white := h3w
      not_isBoundaryVertex_inv_leg := by
        intro i
        rcases hblk _ (hG.leg_notMem_bdry i) with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)) h
        · exact h
      colour_inv_leg := by
        intro i
        rcases hblk _ (hG.leg_notMem_bdry i) with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)) h
        · exact h }
  have hN : G.IsNormalPlabicGraph := ⟨hG, hnorm⟩
  obtain ⟨hX, -⟩ := IsGeneralizedTripleDiagram.exists_moveEquivalent hG
    hN.isGeneralizedTripleDiagram_tripleOfNormal ⟨hpre, horb, D, hD, ⟨φ⟩⟩
    hN.isTripleDiagram_tripleOfNormal
  exact hX

end Loop

/-! #### Stage 2: recolouring small white vertices -/

section Recolour

variable {G : PlabicData H b}

/-- The recolouring of `G` in which every white internal vertex with at most two darts becomes
black. -/
private def recolour (G : PlabicData H b) : PlabicData H b :=
  { G with
    colour := fun z => if ¬G.IsBoundaryVertex (G.vertexOf z) ∧ G.colour z = .white ∧
      (G.vertexOf z).card ≤ 2 then .black else G.colour z }

private theorem recolour_colour (z : H) : (recolour G).colour z =
    if ¬G.IsBoundaryVertex (G.vertexOf z) ∧ G.colour z = .white ∧ (G.vertexOf z).card ≤ 2 then
      .black else G.colour z := rfl

private theorem isPlabicGraph_recolour (hG : G.IsPlabicGraph) : (recolour G).IsPlabicGraph where
  toIsDiskMap := hG.toIsDiskMap
  one_le := hG.one_le
  colour_rot d hd := by
    have hv : G.vertexOf (G.rot d) = G.vertexOf d := G.vertexOf_rot d
    change (recolour G).colour (G.rot d) = (recolour G).colour d
    rw [recolour_colour, recolour_colour, hv, hG.colour_rot d hd]
  leg_notMem_bdry := hG.leg_notMem_bdry
  bvertex_mem := hG.bvertex_mem
  bvertex_injective := hG.bvertex_injective
  exists_bvertex_eq := hG.exists_bvertex_eq
  exists_exterior := hG.exists_exterior

/-- At a vertex with at most two darts, `σ` and `σ⁻¹` agree. -/
private theorem rot_eq_rot_symm_of_card_le_two {z : H} (h : (G.vertexOf z).card ≤ 2) :
    G.rot z = G.rot.symm z := by
  have h1 : 1 ≤ (G.vertexOf z).card := card_pos.2 ⟨z, G.self_mem_vertexOf z⟩
  have hr := RotationSystem.rot_eq_rot_symm_pow (R := G.toRotationSystem) z
  rcases (show (G.vertexOf z).card = 1 ∨ (G.vertexOf z).card = 2 by omega) with h' | h'
  · rw [h', show 1 - 1 = 0 from rfl, pow_zero, Equiv.Perm.one_apply] at hr
    change G.rot z = z at hr
    rw [hr]
    conv_lhs => rw [← Equiv.symm_apply_apply G.rot z, hr]
  · rw [h', show 2 - 1 = 1 from rfl, pow_one] at hr
    exact hr

private theorem recolour_isCrossing_iff (w : Finset H) :
    (recolour G).IsCrossing w ↔ G.IsCrossing w := by
  have key : w ∈ G.internalVertices → 3 ≤ w.card → ∀ d ∈ w,
      (recolour G).colour d = G.colour d := by
    intro hw h3 d hd
    obtain ⟨x, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hw).1
    have hv : G.vertexOf d = G.vertexOf x := G.vertexOf_eq_of_mem hd
    rw [recolour_colour, if_neg]
    rintro ⟨-, -, h⟩
    rw [hv] at h
    omega
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun d hd => (key h1 h3 d hd) ▸ h2 d hd, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun d hd => (key h1 h3 d hd).symm ▸ h2 d hd, h3⟩

private theorem recolour_turn (z : H) : (recolour G).turn z = G.turn z := by
  by_cases hb : G.IsBoundaryVertex (G.vertexOf z)
  · rw [turn_of_isBoundaryVertex hb,
      turn_of_isBoundaryVertex (G := recolour G) (show (recolour G).IsBoundaryVertex
        ((recolour G).vertexOf z) from hb)]
  · have hb' : ¬(recolour G).IsBoundaryVertex ((recolour G).vertexOf z) := hb
    cases hc : G.colour z with
    | white =>
      by_cases hsm : (G.vertexOf z).card ≤ 2
      · rw [turn_of_black hb' (by rw [recolour_colour, if_pos ⟨hb, hc, hsm⟩]),
          turn_of_white hb hc]
        exact rot_eq_rot_symm_of_card_le_two hsm
      · rw [turn_of_white hb' (by rw [recolour_colour, if_neg (fun h => hsm h.2.2), hc]),
          turn_of_white hb hc]
        rfl
    | black =>
      have hnw : ¬(¬G.IsBoundaryVertex (G.vertexOf z) ∧ G.colour z = .white ∧
          (G.vertexOf z).card ≤ 2) := by
        rintro ⟨-, h, -⟩
        rw [hc] at h
        exact Shade.noConfusion h
      rw [turn_of_black hb' (by rw [recolour_colour, if_neg hnw, hc]), turn_of_black hb hc]
      rfl

private theorem recolour_tripMap_eq : (recolour G).tripMap = G.tripMap :=
  funext fun z => recolour_turn (G.inv z)

private theorem recolour_isInitial_iff (z : H) : (recolour G).IsInitial z ↔ G.IsInitial z := by
  unfold IsInitial
  rw [recolour_isCrossing_iff]
  rfl

private theorem recolour_isTerminal_iff (z : H) : (recolour G).IsTerminal z ↔ G.IsTerminal z := by
  unfold IsTerminal
  rw [recolour_isCrossing_iff]
  rfl

private theorem recolour_chainLength (z : H) : (recolour G).chainLength z = G.chainLength z := by
  have hiff : ∀ m, (recolour G).IsTerminal ((recolour G).tripMap^[m] z) ↔
      G.IsTerminal (G.tripMap^[m] z) := fun m => by
    rw [recolour_tripMap_eq, recolour_isTerminal_iff]
  by_cases h : ∃ m, G.IsTerminal (G.tripMap^[m] z)
  · have h' : ∃ m, (recolour G).IsTerminal ((recolour G).tripMap^[m] z) :=
      let ⟨m, hm⟩ := h; ⟨m, (hiff m).2 hm⟩
    refine le_antisymm (chainLength_le ((hiff _).2 (chainLength_spec h)))
      (chainLength_le ((hiff _).1 (chainLength_spec h')))
  · have h' : ¬∃ m, (recolour G).IsTerminal ((recolour G).tripMap^[m] z) :=
      fun ⟨m, hm⟩ => h ⟨m, (hiff m).1 hm⟩
    rw [chainLength, dif_neg h', chainLength, dif_neg h]

private theorem recolour_chainEnd (z : H) : (recolour G).chainEnd z = G.chainEnd z := by
  rw [chainEnd_def, chainEnd_def, recolour_chainLength, recolour_tripMap_eq]

variable {D : Finset H → Finset (Sym2 H)}

private theorem recolour_isDatumTriangle_iff (τ : Finset H) :
    (recolour G).IsDatumTriangle D τ ↔ G.IsDatumTriangle D τ := by
  unfold IsDatumTriangle
  simp only [recolour_isCrossing_iff]
  rfl

private theorem recolour_isDatumSegment_iff (s : Sym2 H) (τ : Finset H) :
    (recolour G).IsDatumSegment D s τ ↔ G.IsDatumSegment D s τ := by
  unfold IsDatumSegment
  simp only [recolour_isCrossing_iff]
  rfl

private theorem recolour_isStrandSymbol_iff (a : StrandSymbol H b) :
    (recolour G).IsStrandSymbol D a ↔ G.IsStrandSymbol D a := by
  cases a with
  | xPlus c => exact recolour_isInitial_iff c
  | xMinus t => exact recolour_isTerminal_iff t
  | yPlus s τ => exact recolour_isDatumSegment_iff s τ
  | yMinus s τ => exact recolour_isDatumSegment_iff s τ
  | bd r => exact Iff.rfl
  | bd' r => exact Iff.rfl

/-- Recolouring the small white vertices does not change the generalized triple diagrams. -/
private theorem isGeneralizedTripleDiagram_recolour (hG : G.IsPlabicGraph) {H₀ : Type*}
    [Fintype H₀] [DecidableEq H₀] {X₀ : TripleData H₀ b}
    (hgen : G.IsGeneralizedTripleDiagram hG X₀) :
    (recolour G).IsGeneralizedTripleDiagram (isPlabicGraph_recolour hG) X₀ := by
  obtain ⟨hpre, horb, D, hD, ⟨φ⟩⟩ := hgen
  have hG' := isPlabicGraph_recolour hG
  have hD' : (recolour G).IsWhiteDatum D := fun w hw => hD w ((recolour_isCrossing_iff w).1 hw)
  refine ⟨hpre, ?_, D, hD', ?_⟩
  · intro x hx
    obtain ⟨e, he, hei⟩ := horb x hx
    refine ⟨e, ?_, (recolour_isInitial_iff e).2 hei⟩
    change e ∈ Set.range fun n : ℕ => (recolour G).tripMap^[n] x
    rw [recolour_tripMap_eq]
    exact he
  set θ : G.StrandDart D ≃ (recolour G).StrandDart D :=
    Equiv.subtypeEquivRight fun a => (recolour_isStrandSymbol_iff a).symm
  have θval : ∀ a, (θ a).1 = a.1 := fun _ => rfl
  refine ⟨φ.trans (Classical.choice (strandDiagram_isomorphic_of' hG hD _ θ ?_ ?_ ?_ ?_ ?_))⟩
  · refine strandDiagram_map_inv_of' hG hD
      (isPreTripleDiagram_strandDiagram hG' hD').inv_involutive _ ?_
    rintro ⟨a, ha⟩ (⟨c, rfl⟩ | ⟨s, τ, rfl⟩ | ⟨r, rfl⟩)
    · apply Subtype.ext
      rw [θval, strandDiagram_inv_apply, strandDiagram_inv_apply, θval]
      change xMinus (G.chainEnd c) = xMinus ((recolour G).chainEnd c)
      rw [recolour_chainEnd]
    · apply Subtype.ext
      rw [θval, strandDiagram_inv_apply, strandDiagram_inv_apply, θval]
      change yMinus s (G.otherTriangle D s τ) = yMinus s ((recolour G).otherTriangle D s τ)
      have hseg : G.IsDatumSegment D s τ := ha
      have hseg' : (recolour G).IsDatumSegment D s τ := (recolour_isDatumSegment_iff s τ).2 hseg
      obtain ⟨o1, o2, -⟩ := hD.otherTriangle_spec hseg
      have := hD'.eq_otherTriangle hseg'
        ((recolour_isDatumTriangle_iff _).2 (IsDatumTriangle.of_isDatumSegment o1))
        (let ⟨_, _, _, _, h⟩ := o1; h) o2
      rw [← this]
    · rfl
  · intro a
    apply Subtype.ext
    rw [θval, strandDiagram_rot_apply, strandDiagram_rot_apply, θval]
    rcases IsStrandSymbol.cases hG hD a.2 with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩ |
      ⟨τ, p, hτ, hp, hr⟩ | ⟨τ, p, hτ, hp, hr⟩ <;> rw [hr]
    · rfl
    · rfl
    · rw [strandRotSym_endSymbol hG, show G.endSymbol r = (recolour G).endSymbol r from rfl,
        strandRotSym_endSymbol hG']
    · have hτ' : (recolour G).IsDatumTriangle D τ := (recolour_isDatumTriangle_iff τ).2 hτ
      rw [strandRotSym_pairOut hG hτ hp, show G.pairOut τ p = (recolour G).pairOut τ p from rfl,
        strandRotSym_pairOut hG' hτ' hp]
      rfl
    · have hτ' : (recolour G).IsDatumTriangle D τ := (recolour_isDatumTriangle_iff τ).2 hτ
      rw [strandRotSym_pairIn hG hD hτ hp, show G.pairIn τ p = (recolour G).pairIn τ p from rfl,
        strandRotSym_pairIn hG' hD' hτ' hp]
      rfl
  · intro a
    rw [mem_strandDiagram_bdry, θval]
  · intro a _
    rw [strandDiagram_isOut, θval]
  · intro r
    exact Subtype.ext rfl

end Recolour

/-! #### Stage 1: splitting crossings -/

section Split

open Function in
private theorem card_orbit_eq_minimalPeriod' (σ : Equiv.Perm H) (x : H) :
    ({y | σ.SameCycle x y} : Finset H).card = minimalPeriod σ x := by
  have h : ({y | σ.SameCycle x y} : Finset H) =
      (range (minimalPeriod σ x)).image fun i => (σ ^ i) x := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
    constructor
    · intro hy
      obtain ⟨n, rfl⟩ := hy.exists_nat_pow_eq
      refine ⟨n % minimalPeriod σ x,
        Nat.mod_lt _ (minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x)), ?_⟩
      rw [← Equiv.Perm.iterate_eq_pow, ← Equiv.Perm.iterate_eq_pow, iterate_mod_minimalPeriod_eq]
    · rintro ⟨i, -, rfl⟩
      exact Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)
  rw [h, card_image_of_injOn, card_range]
  intro i hi j hj hij
  exact iterate_injOn_Iio_minimalPeriod (f := σ) (x := x) (by simpa using hi) (by simpa using hj)
    (by simpa [Equiv.Perm.iterate_eq_pow] using hij)

open Function in
private theorem pow_card_orbit_apply' (σ : Equiv.Perm H) (x : H) :
    (σ ^ ({y | σ.SameCycle x y} : Finset H).card) x = x := by
  rw [card_orbit_eq_minimalPeriod', ← Equiv.Perm.iterate_eq_pow, iterate_minimalPeriod]

open Function in
private theorem eq_of_pow_apply_eq_of_lt' (σ : Equiv.Perm H) (x : H) {i j : ℕ}
    (hi : i < ({y | σ.SameCycle x y} : Finset H).card)
    (hj : j < ({y | σ.SameCycle x y} : Finset H).card) (h : (σ ^ i) x = (σ ^ j) x) : i = j := by
  rw [card_orbit_eq_minimalPeriod'] at hi hj
  exact iterate_injOn_Iio_minimalPeriod (f := σ) (x := x) hi hj
    (by simpa [Equiv.Perm.iterate_eq_pow] using h)

open Function in
private theorem exists_pow_lt_card_of_sameCycle' (σ : Equiv.Perm H) {x y : H}
    (h : σ.SameCycle x y) :
    ∃ i < ({y | σ.SameCycle x y} : Finset H).card, (σ ^ i) x = y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  refine ⟨n % minimalPeriod σ x, ?_, ?_⟩
  · rw [card_orbit_eq_minimalPeriod']
    exact Nat.mod_lt _ (minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x))
  · rw [← Equiv.Perm.iterate_eq_pow, ← Equiv.Perm.iterate_eq_pow, iterate_mod_minimalPeriod_eq]

/-- If `x ≠ y` are in the cycle of `s = σ y` and neither is the `σ`-predecessor of the other,
then `x = σ ^ j s` with `1 ≤ j` and `j + 3` at most the length of the cycle. -/
private theorem exists_pow_eq_of_ne_rot (σ : Equiv.Perm H) {s x y : H} (hs : s = σ y)
    (hsx : σ.SameCycle s x) (hxy : x ≠ y) (h₁ : y ≠ σ.symm x) (h₂ : x ≠ σ.symm y) :
    ∃ j, 1 ≤ j ∧ j + 3 ≤ ({z | σ.SameCycle s z} : Finset H).card ∧ (σ ^ j) s = x := by
  obtain ⟨j, hj, hjx⟩ := exists_pow_lt_card_of_sameCycle' σ hsx
  have hpowk := pow_card_orbit_apply' σ s
  generalize ({z | σ.SameCycle s z} : Finset H).card = k at hj hpowk ⊢
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply h₁
    rw [← hjx, pow_zero, Equiv.Perm.one_apply, hs, Equiv.symm_apply_apply]
  have hj1 : j ≠ k - 1 := by
    intro h
    apply hxy
    apply σ.injective
    rw [← hjx, ← Equiv.Perm.mul_apply, ← pow_succ', h, show k - 1 + 1 = k by omega, hpowk, hs]
  have hj2 : j ≠ k - 2 := by
    intro h
    apply h₂
    rw [Equiv.eq_symm_apply]
    apply σ.injective
    have h2 : (σ ^ (j + 2)) s = σ (σ ((σ ^ j) s)) := by
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [← hs, ← hjx, ← h2, h, show k - 2 + 2 = k by omega, hpowk]
  exact ⟨j, by omega, by omega, hjx⟩

private theorem mem_of_sameCycle_of_mapsTo' {X₀ : Type*} [Finite X₀] {σ : Equiv.Perm X₀}
    {A : Set X₀} (hA : ∀ a ∈ A, σ a ∈ A) {x y : X₀} (hx : x ∈ A) (h : σ.SameCycle x y) : y ∈ A := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hA _ ih

variable {K : PlabicData H b} {s : H} {p : ℕ}

/-- **The two new vertices of a splitting.** In the splitting at `z = v(s)` of size `p`, with
`2 ≤ p ≤ k - 2` for the number `k` of darts of `z`, the vertex of `n` has at most `p + 1` and at
least three darts, that of `n̄` at most `k - p + 1` and at least three darts, every dart of `z`
lies at one of them, and `σ⁻¹(n) = σ^{p-1}(s)`, `σ⁻¹(n̄) = σ^{k-1}(s) = σ⁻¹(s)`. -/
private theorem vertexSplit_facts (hp2 : 2 ≤ p) (hpk : p + 2 ≤ (K.vertexOf s).card) :
    (∀ e : H ⊕ Fin 2, (∀ x, e = Sum.inl x → K.rot.SameCycle s x) →
      ((K.vertexSplit s p).vertexOf e).card ≤ (K.vertexOf s).card - 1) ∧
    3 ≤ ((K.vertexSplit s p).vertexOf (Sum.inr 0)).card ∧
    3 ≤ ((K.vertexSplit s p).vertexOf (Sum.inr 1)).card ∧
    (K.vertexSplit s p).rot.symm (Sum.inr 0) = Sum.inl ((K.rot ^ (p - 1)) s) ∧
    (K.vertexSplit s p).rot.symm (Sum.inr 1) = Sum.inl (K.rot.symm s) := by
  set P := K.vertexSplit s p
  set k := (K.vertexOf s).card with hkdef
  have hkf : ({y | K.rot.SameCycle s y} : Finset H).card = k := rfl
  have hpk' : p ≤ ({y | K.rot.SameCycle s y} : Finset H).card := by omega
  have hrot : ∀ e, P.rot e = splitRot K.rot s p e := fun _ => rfl
  have hstep : ∀ j, j < k → P.rot (Sum.inl ((K.rot ^ j) s)) =
      if j + 1 = p then Sum.inr 0 else if j + 1 = k then Sum.inr 1
        else Sum.inl ((K.rot ^ (j + 1)) s) := fun j hj => by
    rw [hrot, splitRot_inl_pow K.rot s p hpk' (by rw [hkf]; exact hj), hkf]
  have h0 : P.rot (Sum.inr 0) = Sum.inl s := by
    rw [hrot, splitRot_inr_zero, if_neg (by omega)]
  have h1 : P.rot (Sum.inr 1) = Sum.inl ((K.rot ^ p) s) := by
    rw [hrot, splitRot_inr_one_of_le K.rot s p hpk', if_neg (by rw [hkf]; omega)]
  -- the two closed sets
  let A₀ : Set (H ⊕ Fin 2) := {e | e = Sum.inr 0 ∨ ∃ j < p, e = Sum.inl ((K.rot ^ j) s)}
  let A₁ : Set (H ⊕ Fin 2) :=
    {e | e = Sum.inr 1 ∨ ∃ j, p ≤ j ∧ j < k ∧ e = Sum.inl ((K.rot ^ j) s)}
  have hA₀ : ∀ e ∈ A₀, P.rot e ∈ A₀ := by
    rintro e (rfl | ⟨j, hj, rfl⟩)
    · rw [h0]; exact Or.inr ⟨0, by omega, by simp⟩
    · rw [hstep j (by omega)]
      split_ifs with h1' h2'
      · exact Or.inl rfl
      · omega
      · exact Or.inr ⟨j + 1, by omega, rfl⟩
  have hA₁ : ∀ e ∈ A₁, P.rot e ∈ A₁ := by
    rintro e (rfl | ⟨j, hj1, hj2, rfl⟩)
    · rw [h1]; exact Or.inr ⟨p, le_rfl, by omega, rfl⟩
    · rw [hstep j hj2]
      split_ifs with h1' h2'
      · omega
      · exact Or.inl rfl
      · exact Or.inr ⟨j + 1, by omega, by omega, rfl⟩
  have hsub₀ : ∀ e ∈ A₀, P.vertexOf e ⊆
      insert (Sum.inr 0) ((range p).image fun j => Sum.inl ((K.rot ^ j) s)) := by
    intro e he y hy
    have := mem_of_sameCycle_of_mapsTo' hA₀ he (P.mem_vertexOf.1 hy)
    rcases this with rfl | ⟨j, hj, rfl⟩
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_image.2 ⟨j, mem_range.2 hj, rfl⟩)
  have hsub₁ : ∀ e ∈ A₁, P.vertexOf e ⊆
      insert (Sum.inr 1) ((Ico p k).image fun j => Sum.inl ((K.rot ^ j) s)) := by
    intro e he y hy
    have := mem_of_sameCycle_of_mapsTo' hA₁ he (P.mem_vertexOf.1 hy)
    rcases this with rfl | ⟨j, hj1, hj2, rfl⟩
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_image.2 ⟨j, mem_Ico.2 ⟨hj1, hj2⟩, rfl⟩)
  have hcard₀ : ∀ e ∈ A₀, (P.vertexOf e).card ≤ k - 1 := by
    intro e he
    have := card_le_card (hsub₀ e he)
    have h2 := card_insert_le (Sum.inr 0 : H ⊕ Fin 2)
      ((range p).image fun j => Sum.inl ((K.rot ^ j) s))
    have h3 := card_image_le (s := range p) (f := fun j => (Sum.inl ((K.rot ^ j) s) : H ⊕ Fin 2))
    rw [card_range] at h3
    omega
  have hcard₁ : ∀ e ∈ A₁, (P.vertexOf e).card ≤ k - 1 := by
    intro e he
    have := card_le_card (hsub₁ e he)
    have h2 := card_insert_le (Sum.inr 1 : H ⊕ Fin 2)
      ((Ico p k).image fun j => Sum.inl ((K.rot ^ j) s))
    have h3 := card_image_le (s := Ico p k) (f := fun j => (Sum.inl ((K.rot ^ j) s) : H ⊕ Fin 2))
    rw [Nat.card_Ico] at h3
    omega
  have hσs : K.rot s ≠ s := by
    intro h
    have := eq_of_pow_apply_eq_of_lt' K.rot s (i := 1) (j := 0) (by rw [hkf]; omega)
      (by rw [hkf]; omega) (by rw [pow_one, pow_zero, Equiv.Perm.one_apply, h])
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases e with x | j
    · obtain ⟨i, hi, rfl⟩ := exists_pow_lt_card_of_sameCycle' K.rot (he x rfl)
      rw [hkf] at hi
      by_cases hip : i < p
      · exact hcard₀ _ (Or.inr ⟨i, hip, rfl⟩)
      · exact hcard₁ _ (Or.inr ⟨i, by omega, hi, rfl⟩)
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      · exact hcard₀ _ (Or.inl rfl)
      · exact hcard₁ _ (Or.inl rfl)
  · have hsub : ({Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} : Finset (H ⊕ Fin 2)) ⊆
        P.vertexOf (Sum.inr 0) := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rw [P.mem_vertexOf]
      rcases hy with rfl | rfl | rfl
      · exact Equiv.Perm.SameCycle.refl _ _
      · rw [← h0]; exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
      · have e1 : P.rot (Sum.inl s) = Sum.inl (K.rot s) := by
          have := hstep 0 (by omega)
          rw [if_neg (by omega), if_neg (by omega), pow_zero, Equiv.Perm.one_apply,
            pow_one] at this
          exact this
        rw [← e1, ← h0]
        exact Equiv.Perm.sameCycle_apply_right.2
          (Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _))
    have h3 : ({Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} : Finset (H ⊕ Fin 2)).card = 3 := by
      refine card_eq_three.2 ⟨_, _, _, by simp, by simp, ?_, rfl⟩
      simpa using hσs.symm
    exact h3 ▸ card_le_card hsub
  · have hsub : ({Sum.inr 1, Sum.inl ((K.rot ^ p) s), Sum.inl ((K.rot ^ (p + 1)) s)} :
        Finset (H ⊕ Fin 2)) ⊆ P.vertexOf (Sum.inr 1) := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rw [P.mem_vertexOf]
      rcases hy with rfl | rfl | rfl
      · exact Equiv.Perm.SameCycle.refl _ _
      · rw [← h1]; exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
      · have e1 : P.rot (Sum.inl ((K.rot ^ p) s)) = Sum.inl ((K.rot ^ (p + 1)) s) := by
          rw [hstep p (by omega), if_neg (by omega), if_neg (by omega)]
        rw [← e1, ← h1]
        exact Equiv.Perm.sameCycle_apply_right.2
          (Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _))
    have h3 : ({Sum.inr 1, Sum.inl ((K.rot ^ p) s), Sum.inl ((K.rot ^ (p + 1)) s)} :
        Finset (H ⊕ Fin 2)).card = 3 := by
      refine card_eq_three.2 ⟨_, _, _, by simp, by simp, ?_, rfl⟩
      intro h
      apply hσs
      have h' : (K.rot ^ p) s = (K.rot ^ p) (K.rot s) := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ]
        exact Sum.inl_injective h
      exact ((K.rot ^ p).injective h').symm
    exact h3 ▸ card_le_card hsub
  · rw [Equiv.symm_apply_eq]
    rw [hstep (p - 1) (by omega), if_pos (by omega)]
  · rw [Equiv.symm_apply_eq]
    have hk1 : (K.rot ^ (k - 1)) s = K.rot.symm s := by
      rw [Equiv.eq_symm_apply, ← Equiv.Perm.mul_apply, ← pow_succ',
        show k - 1 + 1 = k by omega]
      exact pow_card_orbit_apply' K.rot s
    rw [← hk1, hstep (k - 1) (by omega), if_neg (by omega), if_pos (by omega)]

/-- The weight of a dart at a crossing with at least four darts. -/
private noncomputable def bigWeight (G : PlabicData H b) (x : H) : ℕ :=
  open Classical in
  if G.IsCrossing (G.vertexOf x) ∧ 4 ≤ (G.vertexOf x).card then 2 ^ (G.vertexOf x).card else 0

/-- The sum of the weights `2^{|w|}` of the darts at crossings `w` with at least four darts. -/
private noncomputable def bigExcess (G : PlabicData H b) : ℕ := ∑ x, bigWeight G x

private theorem bigWeight_le {G : PlabicData H b} {x : H} {n : ℕ}
    (h : (G.vertexOf x).card ≤ n) : bigWeight G x ≤ 2 ^ n := by
  unfold bigWeight
  split_ifs
  · exact Nat.pow_le_pow_right (by norm_num) h
  · exact Nat.zero_le _

/-- **Splitting a crossing along a diagonal of the white datum** lowers `bigExcess`. -/
private theorem bigExcess_vertexSplit_lt {K : PlabicData H b} {s : H}
    {p : ℕ} (hc : K.IsCrossing (K.vertexOf s))
    (hk : 4 ≤ (K.vertexOf s).card) (hp2 : 2 ≤ p) (hpk : p + 2 ≤ (K.vertexOf s).card) :
    bigExcess (K.vertexSplit s p) < bigExcess K := by
  set P := K.vertexSplit s p
  set k := (K.vertexOf s).card with hkdef
  obtain ⟨hle, -, -, -, -⟩ := vertexSplit_facts (K := K) (s := s) hp2 hpk
  have hwP : ∀ e : H ⊕ Fin 2, (∀ x, e = Sum.inl x → K.rot.SameCycle s x) →
      bigWeight P e ≤ 2 ^ (k - 1) := fun e he => bigWeight_le (hle e he)
  have hout : ∀ x, ¬K.rot.SameCycle s x → bigWeight P (Sum.inl x) = bigWeight K x := by
    intro x hx
    have hv : P.vertexOf (Sum.inl x) = (K.vertexOf x).map Embedding.inl :=
      K.vertexOf_vertexSplit_inl s p hx
    have hcr : P.IsCrossing (P.vertexOf (Sum.inl x)) ↔ K.IsCrossing (K.vertexOf x) := by
      unfold IsCrossing
      rw [P.vertexOf_mem_internalVertices, K.vertexOf_mem_internalVertices, hv,
        isBoundaryVertex_map_inl_iff, card_map]
      refine and_congr Iff.rfl (and_congr ⟨fun h d hd => ?_, fun h d hd => ?_⟩ Iff.rfl)
      · exact h _ (mem_map_of_mem _ hd)
      · obtain ⟨d', hd', rfl⟩ := mem_map.1 hd
        exact h d' hd'
    unfold bigWeight
    by_cases h : K.IsCrossing (K.vertexOf x) ∧ 4 ≤ (K.vertexOf x).card
    · rw [if_pos h, if_pos ⟨hcr.2 h.1, by rw [hv, card_map]; exact h.2⟩, hv, card_map]
    · rw [if_neg h, if_neg fun h' => h ⟨hcr.1 h'.1, by rw [hv, card_map] at h'; exact h'.2⟩]
  have hin : ∀ x, K.rot.SameCycle s x → bigWeight K x = 2 ^ k := by
    intro x hx
    have hv : K.vertexOf x = K.vertexOf s := (K.vertexOf_eq_vertexOf_iff.2 hx).symm
    unfold bigWeight
    rw [hv, if_pos ⟨hc, hk⟩]
  set f : H → ℕ := fun x => if K.rot.SameCycle s x then 2 ^ (k - 1) else bigWeight K x with hf
  have hPsum : bigExcess P ≤ ∑ x, f x + 2 * 2 ^ (k - 1) := by
    unfold bigExcess
    rw [Fintype.sum_sum_type, Fin.sum_univ_two]
    have h1 : ∑ x, bigWeight P (Sum.inl x) ≤ ∑ x, f x := by
      refine sum_le_sum fun x _ => ?_
      simp only [hf]
      split_ifs with hx
      · exact hwP _ fun y hy => (Sum.inl.inj hy) ▸ hx
      · exact (hout x hx).le
    have h2 := hwP (Sum.inr 0) (fun y hy => (Sum.inr_ne_inl hy).elim)
    have h3 := hwP (Sum.inr 1) (fun y hy => (Sum.inr_ne_inl hy).elim)
    omega
  have hKsum : bigExcess K = ∑ x, f x + k * 2 ^ (k - 1) := by
    have hsplit : ∀ x, bigWeight K x =
        f x + (if K.rot.SameCycle s x then 2 ^ (k - 1) else 0) := by
      intro x
      simp only [hf]
      split_ifs with hx
      · rw [hin x hx, ← two_mul, ← pow_succ']
        congr 1
        omega
      · rfl
    unfold bigExcess
    rw [sum_congr rfl fun x _ => hsplit x, sum_add_distrib, ← sum_filter, sum_const,
      smul_eq_mul]
    rfl
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  rw [hKsum]
  have : 2 * 2 ^ (k - 1) < k * 2 ^ (k - 1) := Nat.mul_lt_mul_of_pos_right (by omega) hpos
  omega

end Split

/-! ### Reductions of a plabic graph carrying a transitive generalized triple diagram -/

section Reduction

variable {H'' : Type} [Fintype H''] [DecidableEq H''] {X : TripleData H'' b}

/-- An internal vertex of colour `c` at the dart `x`. -/
private def IsIntOf (G : PlabicData H b) (x : H) (c : Shade) : Prop :=
  ¬G.IsBoundaryVertex (G.vertexOf x) ∧ G.colour x = c

/-- **Stage 4: contracting black edges.** If the white internal vertices have three darts and every
edge has a black internal end, contracting the edges joining two distinct black vertices one at a
time reaches the last stage. -/
private theorem isTripleDiagram_of_blackEnds (htrans : ∀ x y : H'', X.Reach x y) :
    ∀ n, ∀ N : PlabicGraph b, Fintype.card N.Dart = n →
      (∀ x, IsIntOf N.data x .white → (N.data.vertexOf x).card = 3) →
      (∀ x, x ∉ N.data.bdry → IsIntOf N.data x .black ∨ IsIntOf N.data (N.data.inv x) .black) →
      N.data.IsGeneralizedTripleDiagram N.isPlabicGraph X → X.IsTripleDiagram := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn h3w hblk hgen
  set G := N.data
  have hG : G.IsPlabicGraph := N.isPlabicGraph
  by_cases hex : ∃ x, IsIntOf G x .black ∧ IsIntOf G (G.inv x) .black ∧
      G.vertexOf (G.inv x) ≠ G.vertexOf x
  · obtain ⟨x, ⟨hxu, hxb⟩, ⟨hxu', hxb'⟩, hne⟩ := hex
    have he : G.IsContractibleEdge x :=
      ⟨hne.symm, G.vertexOf_mem_internalVertices.2 hxu, G.vertexOf_mem_internalVertices.2 hxu',
        hxb'.trans hxb.symm⟩
    set Q := G.contractEdge x (he.leg_mem hG)
    have hQ : Q.IsPlabicGraph := hG.contractEdge he
    have hinv := hG.inv_involutive
    have hbv : ∀ y : (({x, G.inv x} : Set N.Dart)ᶜ : Set N.Dart),
        Q.IsBoundaryVertex (Q.vertexOf y) ↔ G.IsBoundaryVertex (G.vertexOf y) :=
      fun y => isBoundaryVertex_vertexOf_contractEdge_iff he
    have hint : ∀ y : (({x, G.inv x} : Set N.Dart)ᶜ : Set N.Dart) , ∀ c,
        IsIntOf Q y c ↔ IsIntOf G y c := fun y c => by
      unfold IsIntOf
      rw [hbv, contractEdge_colour]
    have hint' : ∀ y : (({x, G.inv x} : Set N.Dart)ᶜ : Set N.Dart), ∀ c,
        IsIntOf Q (Q.inv y) c ↔ IsIntOf G (G.inv y) c := fun y c => by
      rw [hint, coe_contractEdge_inv hinv]
    let N' : PlabicGraph b := ⟨_, Q, hQ⟩
    refine ih (Fintype.card N'.Dart) (hn ▸ Fintype.card_subtype_lt (x := x) (by simp)) N' rfl
      ?_ ?_ ((isGeneralizedTripleDiagram_contractEdge_iff hG he hxb X).1 hgen)
    · intro y hy
      have hyG := (hint y .white).1 hy
      have hyW : (y : N.Dart) ∉ G.vertexOf x ∪ G.vertexOf (G.inv x) := by
        intro h
        have := (colour_eq_of_mem_union hG he h).trans hxb
        rw [hyG.2] at this
        exact Shade.noConfusion this
      change (Q.vertexOf y).card = 3
      rw [← card_map (Embedding.subtype _),
        map_vertexOf_contractEdge_of_notMem he.not_sameCycle hyW]
      exact h3w _ hyG
    · intro y hy
      rw [hint, hint']
      exact hblk _ (mem_contractEdge_bdry.not.1 hy)
  · push Not at hex
    refine isTripleDiagram_of_normalForm hG (fun x hx hc => h3w x ⟨hx, hc⟩)
      (fun x hx => hblk x hx) (fun x hx hb hx' hb' => hex x ⟨hx, hb⟩ ⟨hx', hb'⟩) hgen htrans

/-- The darts of the edges without a black internal end. -/
private noncomputable def badDarts (G : PlabicData H b) : Finset H :=
  open Classical in
  univ.filter fun x => x ∉ G.bdry ∧ ¬IsIntOf G x .black ∧ ¬IsIntOf G (G.inv x) .black

/-- **Stage 3: inserting black vertices.** If the white internal vertices have three darts,
inserting a black vertex on each edge without a black internal end, one at a time, reaches
stage 4. -/
private theorem isTripleDiagram_of_whiteThree (htrans : ∀ x y : H'', X.Reach x y) :
    ∀ n, ∀ N : PlabicGraph b, (badDarts N.data).card = n →
      (∀ x, IsIntOf N.data x .white → (N.data.vertexOf x).card = 3) →
      N.data.IsGeneralizedTripleDiagram N.isPlabicGraph X → X.IsTripleDiagram := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn h3w hgen
  set G := N.data
  have hG : G.IsPlabicGraph := N.isPlabicGraph
  by_cases hex : ∃ x, x ∉ G.bdry ∧ ¬IsIntOf G x .black ∧ ¬IsIntOf G (G.inv x) .black
  · obtain ⟨x, hxB, hx1, hx2⟩ := hex
    have hinv := hG.inv_involutive
    have hfix : G.inv x ≠ x := hG.inv_ne x
    set G₁ := G.bivalentInsertion x .black
    have hG₁ : G₁.IsPlabicGraph := isPlabicGraph_bivalentInsertion .black hG hxB
    have hd₁ := isBivalentRemovable_bivalentInsertion (G := G) x Shade.black
    obtain ⟨θ⟩ := bivalentRemoval_bivalentInsertion_isomorphic Shade.black hG hxB
    have hgen₁ : G₁.IsGeneralizedTripleDiagram hG₁ X :=
      (isGeneralizedTripleDiagram_bivalentRemoval_iff hG₁ hd₁ X).2
        ((θ.isGeneralizedTripleDiagram_iff (isPlabicGraph_bivalentRemoval hG₁ hd₁) hG X).2 hgen)
    have hintl : ∀ e c, IsIntOf G₁ (Sum.inl e) c ↔ IsIntOf G e c := fun e c => by
      unfold IsIntOf
      rw [isBoundaryVertex_bivalentInsertion_vertexOf_inl, bivalentInsertion_colour_inl]
    have hintr : ∀ j, IsIntOf G₁ (Sum.inr j) .black := fun j =>
      ⟨not_isBoundaryVertex_bivalentInsertion_vertexOf_inr x _ j, rfl⟩
    let N₁ : PlabicGraph b := ⟨_, G₁, hG₁⟩
    have hsub : badDarts G₁ ⊆ ((badDarts G).erase x).map Embedding.inl := by
      intro y hy
      simp only [badDarts, mem_filter, mem_univ, true_and] at hy
      obtain ⟨hyB, hy1, hy2⟩ := hy
      rcases y with e | j
      · rw [inl_mem_bivalentInsertion_bdry] at hyB
        rw [hintl] at hy1
        have hex : e ≠ x := by
          rintro rfl
          rw [bivalentInsertion_inv_inl_self _ hfix] at hy2
          exact hy2 (hintr 0)
        have hei : e ≠ G.inv x := by
          rintro rfl
          rw [bivalentInsertion_inv_inl_inv _ hinv] at hy2
          exact hy2 (hintr 1)
        rw [bivalentInsertion_inv_inl_of_ne _ hinv hex hei, hintl] at hy2
        refine mem_map_of_mem _ (mem_erase.2 ⟨hex, ?_⟩)
        simp only [badDarts, mem_filter, mem_univ, true_and]
        exact ⟨hyB, hy1, hy2⟩
      · exact absurd (hintr j) hy1
    have hxbad : x ∈ badDarts G := by
      simp only [badDarts, mem_filter, mem_univ, true_and]
      exact ⟨hxB, hx1, hx2⟩
    have hlt : (badDarts G₁).card < n := by
      have := card_le_card hsub
      rw [card_map, card_erase_of_mem hxbad] at this
      have hpos : 0 < (badDarts G).card := card_pos.2 ⟨x, hxbad⟩
      omega
    refine ih _ hlt N₁ rfl ?_ hgen₁
    rintro (e | j) hy
    · change ((G.bivalentInsertion x Shade.black).vertexOf (Sum.inl e)).card = 3
      rw [bivalentInsertion_vertexOf_inl, card_map]
      exact h3w e ((hintl e _).1 hy)
    · exact Shade.noConfusion (hy.2.symm.trans (hintr j).2)
  · push Not at hex
    refine isTripleDiagram_of_blackEnds htrans _ N rfl h3w (fun x hx => ?_) hgen
    by_contra h
    push Not at h
    exact h.2 (hex x hx h.1)

/-- **Stage 2: recolouring.** If the white internal vertices have at most three darts, recolouring
black those with at most two darts reaches stage 3. -/
private theorem isTripleDiagram_of_whiteLeThree (htrans : ∀ x y : H'', X.Reach x y)
    (N : PlabicGraph b) (h3 : ∀ x, IsIntOf N.data x .white → (N.data.vertexOf x).card ≤ 3)
    (hgen : N.data.IsGeneralizedTripleDiagram N.isPlabicGraph X) : X.IsTripleDiagram := by
  refine isTripleDiagram_of_whiteThree htrans _
    ⟨N.Dart, recolour N.data, isPlabicGraph_recolour N.isPlabicGraph⟩ rfl ?_
    (isGeneralizedTripleDiagram_recolour _ hgen)
  rintro x ⟨hx, hc⟩
  change ¬N.data.IsBoundaryVertex (N.data.vertexOf x) at hx
  change (recolour N.data).colour x = .white at hc
  rw [recolour_colour] at hc
  by_cases hcond : ¬N.data.IsBoundaryVertex (N.data.vertexOf x) ∧ N.data.colour x = .white ∧
      (N.data.vertexOf x).card ≤ 2
  · rw [if_pos hcond] at hc
    exact Shade.noConfusion hc
  · rw [if_neg hcond] at hc
    change (N.data.vertexOf x).card = 3
    have h1 := h3 x ⟨hx, hc⟩
    have h2 : ¬(N.data.vertexOf x).card ≤ 2 := fun h => hcond ⟨hx, hc, h⟩
    omega

/-- **Stage 1: splitting crossings.** Splitting a crossing with at least four darts along a
diagonal of the white datum keeps `X` a generalized triple diagram
(`isGeneralizedTripleDiagram_of_contractEdge_white`) and lowers `bigExcess`; when no crossing has
four darts, stage 2 applies. -/
private theorem isTripleDiagram_of_bigExcess (htrans : ∀ x y : H'', X.Reach x y) :
    ∀ n, ∀ N : PlabicGraph b, bigExcess N.data = n →
      N.data.IsGeneralizedTripleDiagram N.isPlabicGraph X → X.IsTripleDiagram := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn hgen
  set G := N.data
  have hG : G.IsPlabicGraph := N.isPlabicGraph
  have hinv := hG.inv_involutive
  by_cases hex : ∃ x, IsIntOf G x .white ∧ 4 ≤ (G.vertexOf x).card
  · obtain ⟨x, ⟨hxu, hxw⟩, hx4⟩ := hex
    have hcw : G.IsCrossing (G.vertexOf x) :=
      ⟨G.vertexOf_mem_internalVertices.2 hxu, fun z hz =>
        (colour_eq_of_sameCycle hG hxu (G.mem_vertexOf.1 hz)).trans hxw, by omega⟩
    obtain ⟨hpre, horb, D, hD, ⟨φ⟩⟩ := hgen
    obtain ⟨e, he⟩ : ∃ e, e ∈ D (G.vertexOf x) := by
      obtain ⟨hDw, m, _, l, hl, hT⟩ := hD _ hcw
      have hm : m = (G.vertexOf x).card := (hl.card_eq).symm
      have hcard := TypeA.IsTriangulation.card_eq (by omega) hT
      obtain ⟨e', he'⟩ := card_pos.1 (show 0 < (RotationSystem.cornerPullback l
        (D (G.vertexOf x))).card by omega)
      exact ⟨_, RotationSystem.mem_cornerPullback.1 he'⟩
    have hDw := (hD _ hcw).1 e he
    induction e using Sym2.ind with | _ x₁ y₁ => ?_
    have hx₁ : x₁ ∈ G.vertexOf x := hDw.2 x₁ (Sym2.mem_mk_left _ _)
    have hy₁ : y₁ ∈ G.vertexOf x := hDw.2 y₁ (Sym2.mem_mk_right _ _)
    have hxy : x₁ ≠ y₁ := fun h => hDw.1 (Sym2.mk_isDiag_iff.2 h)
    have hns1 : y₁ ≠ G.rot.symm x₁ := fun h =>
      cornerSide_notMem_of_isCornerTriangulation (hD _ hcw) hx₁
        (by rwa [RotationSystem.cornerSide, ← h])
    have hns2 : x₁ ≠ G.rot.symm y₁ := fun h =>
      cornerSide_notMem_of_isCornerTriangulation (hD _ hcw) hy₁
        (by rwa [RotationSystem.cornerSide, ← h, Sym2.eq_swap])
    set s₀ := G.rot y₁ with hs₀
    have hvs : G.vertexOf s₀ = G.vertexOf x := by
      rw [hs₀, G.vertexOf_rot]
      exact G.vertexOf_eq_of_mem hy₁
    set k := (G.vertexOf x).card with hkdef
    have hkf : ({y | G.rot.SameCycle s₀ y} : Finset N.Dart).card = k := by
      change (G.vertexOf s₀).card = k
      rw [hvs]
    obtain ⟨j, hj1, hj3, hjx⟩ := exists_pow_eq_of_ne_rot G.rot hs₀
      (G.mem_vertexOf.1 (hvs ▸ hx₁)) hxy hns1 hns2
    rw [hkf] at hj3
    set p := j + 1 with hpdef
    have hp2 : 2 ≤ p := by omega
    have hpk : p + 2 ≤ (G.vertexOf s₀).card := by rw [hvs]; omega
    have hz : ¬G.IsBoundaryVertex (G.vertexOf s₀) := by rw [hvs]; exact hxu
    set P := G.vertexSplit s₀ p
    have hP : P.IsPlabicGraph := hG.vertexSplit hz p
    have he' : P.IsContractibleEdge (Sum.inr 0) :=
      G.isContractibleEdge_vertexSplit s₀ p hz (by omega)
    obtain ⟨-, h3a, h3b, hσ0, hσ1⟩ := vertexSplit_facts (K := G) (s := s₀) hp2 hpk
    have hwP : P.colour (Sum.inr 0) = .white := by
      change G.colour s₀ = .white
      exact (colour_eq_of_sameCycle hG hxu (G.mem_vertexOf.1 (hvs ▸ G.self_mem_vertexOf s₀))).trans
        hxw
    have hinvP : P.inv (Sum.inr 0) = Sum.inr 1 := rfl
    have hqP : 3 ≤ (P.vertexOf (P.inv (Sum.inr 0))).card := by rw [hinvP]; exact h3b
    set θ := G.contractEdgeVertexSplitIso s₀ p hinv
    have hQ : (P.contractEdge (Sum.inr 0) (he'.leg_mem hP)).IsPlabicGraph := hP.contractEdge he'
    have hgenQ := (show G.IsGeneralizedTripleDiagram hG X from
      ⟨hpre, horb, D, hD, ⟨φ⟩⟩).of_iso θ hG hQ
    have hD' := θ.isWhiteDatum_mapDatum hD
    obtain ⟨ψ⟩ : (G.strandDiagram hG hD).Isomorphic
        ((P.contractEdge (Sum.inr 0) (he'.leg_mem hP)).strandDiagram hQ hD') :=
      ⟨θ.strandDiagramIso hG hQ hD⟩
    -- `γ_e = {x₁, y₁}`
    have hθx : ∀ z, ((θ.toEquiv z : (({Sum.inr 0, P.inv (Sum.inr 0)} : Set (N.Dart ⊕ Fin 2))ᶜ :
        Set (N.Dart ⊕ Fin 2))) : N.Dart ⊕ Fin 2) = Sum.inl z := fun _ => rfl
    have hx₁W : Sum.inl x₁ ∈ P.vertexOf (Sum.inr 0) ∪ P.vertexOf (P.inv (Sum.inr 0)) := by
      refine mem_union_left _ ?_
      have : P.rot.symm (Sum.inr 0) = Sum.inl x₁ := by
        rw [hσ0, show p - 1 = j by omega, hjx]
      rw [← this]
      exact P.rot_symm_mem_vertexOf _
    have hv' := vertexOf_eq_merged (hleg := he'.leg_mem hP) he' (y := θ.toEquiv x₁) hx₁W
    have hγ : P.cornerGlueDiagonal (Sum.inr 0) ∈
        ((mapDatum θ.toEquiv D) ((P.mergedVertex (Sum.inr 0)).subtype
          (· ∈ (({Sum.inr 0, P.inv (Sum.inr 0)} : Set (N.Dart ⊕ Fin 2))ᶜ :
            Set (N.Dart ⊕ Fin 2))))).image (Sym2.map Subtype.val) := by
      rw [← hv', ← θ.map_vertexOf, mapDatum_map, ← map_sym2Map_subtype_eq_image, map_map]
      have hσ1' : P.rot.symm (P.inv (Sum.inr 0)) = Sum.inl (G.rot.symm s₀) := by
        rw [hinvP]; exact hσ1
      have hval : RotationSystem.cornerGlueDiagonal P.toRotationSystem (Sum.inr 0) =
          (θ.toEquiv.toEmbedding.sym2Map.trans (Embedding.subtype _).sym2Map) s(x₁, y₁) := by
        have hsy : G.rot.symm s₀ = y₁ := by rw [hs₀, Equiv.symm_apply_apply]
        rw [RotationSystem.cornerGlueDiagonal, hσ1', hσ0, show p - 1 = j by omega, hjx, hsy]
        rfl
      rw [hval, G.vertexOf_eq_of_mem hx₁]
      exact mem_map_of_mem _ he
    obtain ⟨-, horbP, D'', hD'', ⟨χ⟩⟩ := isGeneralizedTripleDiagram_of_contractEdge_white hP he'
      hwP h3a hqP hD' hγ hgenQ.2.1
    let N₁ : PlabicGraph b := ⟨_, P, hP⟩
    exact ih _ (hn ▸ bigExcess_vertexSplit_lt (hvs ▸ hcw) (by rw [hvs]; exact hx4) hp2 hpk)
      N₁ rfl ⟨hpre, horbP, D'', hD'', ⟨φ.trans (ψ.trans χ)⟩⟩
  · push Not at hex
    exact isTripleDiagram_of_whiteLeThree htrans N
      (fun x hx => Nat.lt_succ_iff.1 (hex x hx)) hgen

end Reduction

/-- **Connected generalized triple diagrams are triple diagrams**. Let `G` be a plabic graph and
`X` a generalized triple diagram of `G` on which the group generated by `σ` and `d ↦ d̄` acts
transitively. Then `X` is a triple diagram. -/
@[cluster_algebras "lem_generalized_triple_diagram_connected"]
theorem IsGeneralizedTripleDiagram.isTripleDiagram {G : PlabicData H b} (hG : G.IsPlabicGraph)
    {H'' : Type} [Fintype H''] [DecidableEq H''] {X : TripleData H'' b}
    (hgen : G.IsGeneralizedTripleDiagram hG X)
    (htrans : ∀ x y : H'', ∃ g ∈ Subgroup.closure ({X.inv, X.rot} : Set (Equiv.Perm H'')),
      g x = y) :
    X.IsTripleDiagram :=
  isTripleDiagram_of_bigExcess
    (fun x y => (RotationSystem.reach_iff_exists_mem_closure (R := X.toRotationSystem)).2
      (htrans x y)) _ ⟨H, G, hG⟩ rfl hgen

end PlabicData

namespace PlabicGraph

open PlabicData

variable {b : ℕ}

/-- One step of `∘∼` carries a generalized triple diagram that is a triple diagram to a
move-equivalent one. -/
private theorem CircStep.exists_moveEquivalent {G₀ G₁ : PlabicGraph b} (h : G₀.CircStep G₁)
    (X : TripleDiagram b) (hX : G₀.data.IsGeneralizedTripleDiagram G₀.isPlabicGraph X.data) :
    ∃ X' : TripleDiagram b, G₁.data.IsGeneralizedTripleDiagram G₁.isPlabicGraph X'.data ∧
      X.MoveEquivalent X' := by
  have hG₀ := G₀.isPlabicGraph
  have hG₁ := G₁.isPlabicGraph
  rcases h with hiso | ⟨c, hq, ⟨θ⟩⟩ | (⟨d, hd, ⟨θ⟩⟩ | ⟨d, hd, ⟨θ⟩⟩) |
    (⟨d, hnl, he, ⟨θ⟩⟩ | ⟨d, hnl, he, ⟨θ⟩⟩)
  · obtain ⟨θ⟩ : Nonempty (G₁.data.Iso G₀.data) := hiso
    exact ⟨X, (θ.isGeneralizedTripleDiagram_iff hG₁ hG₀ X.data).2 hX,
      TripleDiagram.MoveEquivalent.refl X⟩
  · obtain ⟨c', hq', hw', heq⟩ := hq.exists_white
    obtain ⟨D₁, hD₁, hX₁, hgen, hmove⟩ :=
      IsGeneralizedTripleDiagram.exists_squareMove hG₀ hq' hw' hX X.isTripleDiagram
    refine ⟨⟨_, _, hX₁⟩, (θ.isGeneralizedTripleDiagram_iff hG₁ (hG₀.squareMove c) _).2
      (isGeneralizedTripleDiagram_of_eq heq _ _ hgen), hmove⟩
  · exact ⟨X, (θ.isGeneralizedTripleDiagram_iff hG₁ (isPlabicGraph_bivalentRemoval hG₀ hd) X.data).2
      ((isGeneralizedTripleDiagram_bivalentRemoval_iff hG₀ hd X.data).1 hX),
      TripleDiagram.MoveEquivalent.refl X⟩
  · exact ⟨X, (isGeneralizedTripleDiagram_bivalentRemoval_iff hG₁ hd X.data).2
      ((θ.isGeneralizedTripleDiagram_iff hG₀ (isPlabicGraph_bivalentRemoval hG₁ hd) X.data).1 hX),
      TripleDiagram.MoveEquivalent.refl X⟩
  · obtain ⟨X', hgen, hm⟩ := (exists_moveEquivalent_contractEdge hG₀ he hnl X).1 hX
    exact ⟨X', (θ.isGeneralizedTripleDiagram_iff hG₁ (hG₀.contractEdge he) X'.data).2 hgen, hm⟩
  · exact (exists_moveEquivalent_contractEdge hG₁ he hnl X).2
      ((θ.isGeneralizedTripleDiagram_iff hG₀ (hG₁.contractEdge he) X.data).1 hX)

/-- **`∘∼`-moves are swivel moves**. Let `G` and `G'` be plabic graphs with `G ∘∼ G'`, and let `X`
be a generalized triple diagram of `G` that is a triple diagram. Then `G'` has a generalized triple
diagram `X'` that is a triple diagram with `X ∼ X'`. -/
@[cluster_algebras "lem_circ_moves_swivel"]
theorem CircMoveEquivalent.exists_moveEquivalent {G G' : PlabicGraph b}
    (h : G.CircMoveEquivalent G') (X : TripleDiagram b)
    (hX : G.data.IsGeneralizedTripleDiagram G.isPlabicGraph X.data) :
    ∃ X' : TripleDiagram b, G'.data.IsGeneralizedTripleDiagram G'.isPlabicGraph X'.data ∧
      X.MoveEquivalent X' := by
  induction h with
  | refl => exact ⟨X, hX, TripleDiagram.MoveEquivalent.refl X⟩
  | tail _ hst ih =>
    obtain ⟨X₁, h₁, hm₁⟩ := ih
    obtain ⟨X₂, h₂, hm₂⟩ := CircStep.exists_moveEquivalent hst X₁ h₁
    exact ⟨X₂, h₂, hm₁.trans hm₂⟩

end PlabicGraph


end ClusterAlgebras

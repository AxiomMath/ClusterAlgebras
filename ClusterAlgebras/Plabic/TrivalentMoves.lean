/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.EdgeContraction
public import ClusterAlgebras.Plabic.LocalMoves
public import ClusterAlgebras.Plabic.Trivalent

/-!
# Splitting, contracting and flipping

Splitting a vertex and contracting an edge are inverse operations. Let `K` be a plabic graph and
`S` the splitting of `K` at an internal vertex `z = v(s)` from `s` of size `p ∈ [0, k]`, with new
darts `n`, `n̄`. The new edge `{n, n̄}` joins the two distinct internal vertices `(n x_1 … x_p)`
and `(n̄ x_{p+1} … x_k)`, both coloured `κ(z)`, and contracting it gives back `K`: the rotation
induced on the old darts is `σ`. Conversely, if `{d, d̄}` is an edge of a plabic graph `G` joining
distinct internal vertices of the same colour, with rotations `(d a_1 … a_p)` and `(d̄ b_1 … b_q)`,
the merged vertex of the contraction `K` of `G` along `{d, d̄}` is `(a_1 … a_p b_1 … b_q)`, and `G`
is the splitting of `K` at it from `a_1 = σ(d)` of size `p`, with new darts `d`, `d̄`.

A flip of `G` at an edge `{d, d̄}` joining the trivalent vertices `(d a_1 a_2)` and
`(d̄ b_1 b_2)` is the splitting of the contraction along `{d, d̄}` at the merged vertex
`(a_1 a_2 b_1 b_2)`, read from `a_2`, of size `2`; since contractions and splittings of plabic
graphs are plabic graphs, so is the flip.

A *trivalent resolution* of a plabic graph `X` whose internal vertices have at least three darts
is a trivalent plabic graph reached from `X` by repeatedly undoing contractions without creating
internal vertices with fewer than three darts. Splitting a vertex with `k ≥ 4` darts from any of
its darts with size `2` produces vertices with `3` and `k - 1` darts, and lowers the excess
`∑_v (|v| - 3)`; by induction on the excess, resolutions exist.

## Main definitions

* `ClusterAlgebras.PlabicGraph.IsResolution`: trivalent resolutions, with their steps
  `ClusterAlgebras.PlabicGraph.ResolutionStep`.
* `ClusterAlgebras.complPairSumEquiv`: the identification of a set of darts with the darts off an
  edge `{d, e}` together with two new darts.

## Main results

* `ClusterAlgebras.PlabicData.isContractibleEdge_vertexSplit`,
  `ClusterAlgebras.PlabicData.isomorphic_contractEdge_vertexSplit`: the new edge of a splitting
  can be contracted, and contracting it gives back the graph.
* `ClusterAlgebras.PlabicData.isomorphic_vertexSplit_contractEdge`: an edge is the splitting of
  its contraction.
* `ClusterAlgebras.PlabicData.isomorphic_flipMove_vertexSplit`: a flip is a rotated splitting of
  a contraction.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.flipMove`: a flip is a plabic graph.
* `ClusterAlgebras.PlabicGraph.exists_isResolution`: resolutions exist.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.of_iso`: a tuple isomorphic to a plabic graph, with
  its chosen darts `leg i` outside `B`, is a plabic graph.

## Implementation notes

* **Equality as isomorphism.** FWZ's equalities between a graph and a splitting or a
  contraction compare tuples on different sets of darts: the splitting of `K` lives on
  `H ⊕ Fin 2`, the contraction of `G` along `{d, d̄}` on the subtype `({d, d̄})ᶜ`. They are stated
  as isomorphisms of plabic graphs, given by the evident identifications of darts:
  `ClusterAlgebras.splitComplEquiv` for the contraction of a splitting, and
  `ClusterAlgebras.complPairSumEquiv`, which sends `d` and `d̄` to the new darts `n = Sum.inr 0`
  and `n̄ = Sum.inr 1` and fixes every other dart, for the splitting of a contraction. These
  isomorphisms are the definitions `contractEdgeVertexSplitIso`, `contractEdgeSplitIso` and
  `flipMoveSplitIso`.
* **The vertex `z`.** A splitting is determined by the dart `s` it starts from, `z` being the
  vertex `v(s)`; FWZ's "vertex `z` of the contraction containing `a_1`", from which the
  splitting reads from `a_2`, is the vertex of `a_2`. The starting dart is a dart of the
  contraction, so its membership in `({d, d̄})ᶜ` is a hypothesis of the statements.
* **Resolutions.** The sequence `X = X₀, …, X_m` of a resolution is the reflexive-transitive
  closure of `PlabicGraph.ResolutionStep`, a step `X_{j-1} → X_j` asking that `X_j` have all
  internal vertices with at least three darts and that `X_{j-1}` be isomorphic to the contraction
  of `X_j` along an edge (`PlabicGraph.IsEdgeContraction`). The quantity `ex(X)` of FWZ is
  used only in the proof of `exists_isResolution`, through the dart-weighted variant
  `∑_x (|v(x)| - 3)` over the darts at internal vertices.
* **Labels.** The labels `[1, b]` are `Fin b`, `0`-indexed, as in the rest of the chapter.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm Function

/-! ### Orbits of permutations -/

section Orbits

variable {X : Type*}

/-- A set mapped into itself by a permutation of a finite set contains the cycles of its
elements. -/
private theorem mem_of_sameCycle_of_mapsTo [Finite X] {σ : Perm X} {A : Set X}
    (hA : ∀ a ∈ A, σ a ∈ A) {x y : X} (hx : x ∈ A) (h : σ.SameCycle x y) : y ∈ A := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact hA _ ih

private theorem sameCycle_map_iff {α β : Type*} {f : Perm α} {g : Perm β} (e : α ≃ β)
    (h : ∀ x, e (f x) = g (e x)) {x y : α} : g.SameCycle (e x) (e y) ↔ f.SameCycle x y := by
  have hc : e.permCongr f = g := by
    ext x
    simpa [Equiv.permCongr_apply] using h (e.symm x)
  have hpow : ∀ n : ℤ, ∀ x, e ((f ^ n) x) = (g ^ n) (e x) := by
    intro n x
    rw [← hc]
    have : (e.permCongr f) ^ n = e.permCongr (f ^ n) := by
      simpa using (map_zpow (Equiv.permCongrHom e).toMonoidHom f n).symm
    rw [this, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, e.injective (by rw [hpow, hn])⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hpow, hn]⟩

section Period

variable [Fintype X] [DecidableEq X]

private theorem card_orbit_eq_minimalPeriod (σ : Perm X) (x : X) :
    ({y | σ.SameCycle x y} : Finset X).card = minimalPeriod σ x := by
  have h : ({y | σ.SameCycle x y} : Finset X) =
      (range (minimalPeriod σ x)).image fun i => (σ ^ i) x := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
    constructor
    · intro hy
      obtain ⟨n, rfl⟩ := hy.exists_nat_pow_eq
      refine ⟨n % minimalPeriod σ x,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (MulAction.minimalPeriod_pos σ x).out), ?_⟩
      rw [← Perm.iterate_eq_pow, ← Perm.iterate_eq_pow, iterate_mod_minimalPeriod_eq]
    · rintro ⟨i, -, rfl⟩
      exact sameCycle_pow_right.2 (SameCycle.refl _ _)
  rw [h, card_image_of_injOn, card_range]
  intro i hi j hj hij
  exact iterate_injOn_Iio_minimalPeriod (f := σ) (x := x) (by simpa using hi) (by simpa using hj)
    (by simpa [Perm.iterate_eq_pow] using hij)

/-- `σ^k(x) = x` for `k` the number of elements of the orbit of `x`. -/
private theorem pow_card_orbit_apply (σ : Perm X) (x : X) :
    (σ ^ ({y | σ.SameCycle x y} : Finset X).card) x = x := by
  rw [card_orbit_eq_minimalPeriod, ← Perm.iterate_eq_pow, iterate_minimalPeriod]

/-- The elements `σ^i(x)`, `i < k`, of the orbit of `x` are distinct. -/
private theorem eq_of_pow_apply_eq_of_lt (σ : Perm X) (x : X) {i j : ℕ}
    (hi : i < ({y | σ.SameCycle x y} : Finset X).card)
    (hj : j < ({y | σ.SameCycle x y} : Finset X).card) (h : (σ ^ i) x = (σ ^ j) x) : i = j := by
  rw [card_orbit_eq_minimalPeriod] at hi hj
  exact iterate_injOn_Iio_minimalPeriod (f := σ) (x := x) hi hj
    (by simpa [Perm.iterate_eq_pow] using h)

/-- Every element of the orbit of `x` is `σ^i(x)` for some `i` less than the size of the orbit. -/
private theorem exists_pow_lt_card_of_sameCycle (σ : Perm X) {x y : X} (h : σ.SameCycle x y) :
    ∃ i < ({y | σ.SameCycle x y} : Finset X).card, (σ ^ i) x = y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  refine ⟨n % minimalPeriod σ x, ?_, ?_⟩
  · rw [card_orbit_eq_minimalPeriod]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero (MulAction.minimalPeriod_pos σ x).out)
  · rw [← Perm.iterate_eq_pow, ← Perm.iterate_eq_pow, iterate_mod_minimalPeriod_eq]

/-- An orbit with three elements is the `3`-cycle `(x σx σ²x)`. -/
private theorem three_cycle_of_card {σ : Perm X} {x : X}
    (h : ({y | σ.SameCycle x y} : Finset X).card = 3) :
    σ (σ (σ x)) = x ∧ x ≠ σ x ∧ x ≠ σ (σ x) ∧ σ x ≠ σ (σ x) ∧
      ∀ y, σ.SameCycle x y → y = x ∨ y = σ x ∨ y = σ (σ x) := by
  have hp : ∀ i : ℕ, (σ ^ i) x = σ^[i] x := fun i => (congrFun (Perm.iterate_eq_pow σ i) x).symm
  have h3 := pow_card_orbit_apply σ x
  rw [h, hp] at h3
  have hne : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → σ^[i] x ≠ σ^[j] x := fun i j hi hj hij e =>
    hij (eq_of_pow_apply_eq_of_lt σ x (by omega) (by omega) (by rwa [hp, hp]))
  refine ⟨h3, hne 0 1 (by norm_num) (by norm_num) (by norm_num),
    hne 0 2 (by norm_num) (by norm_num) (by norm_num),
    hne 1 2 (by norm_num) (by norm_num) (by norm_num), fun y hy => ?_⟩
  obtain ⟨i, hi, rfl⟩ := exists_pow_lt_card_of_sameCycle σ hy
  rw [h] at hi
  rw [hp]
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end Period

end Orbits

namespace PlabicData

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}

/-! ### Isomorphisms -/

/-- A bijection intertwining the rotations maps each vertex onto the vertex of the image. -/
theorem map_vertexOf_of_map_rot {G : PlabicData H b} {G' : PlabicData H' b} (e : H ≃ H')
    (h : ∀ x, e (G.rot x) = G'.rot (e x)) (d : H) :
    (G.vertexOf d).map e.toEmbedding = G'.vertexOf (e d) := by
  ext y
  rw [mem_map_equiv, RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf,
    ← sameCycle_map_iff e h, Equiv.apply_symm_apply]

/-- An isomorphism `G → G'` from a bijection of darts commuting with the involutions and the
rotations, matching `B` with `B'` and the colours of internal vertices, and mapping each chosen
dart `leg i` to `leg' i`. -/
def Iso.ofEquivOfMapLeg {G : PlabicData H b} {G' : PlabicData H' b} (e : H ≃ H')
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
    rw [bvertex, bvertex, ← map_leg, ← map_vertexOf_of_map_rot e map_rot]
    ext y
    simp only [mem_map_equiv, mem_filter]
    rw [← mem_bdry_iff (e.symm y), Equiv.apply_symm_apply]

namespace Iso

variable {G : PlabicData H b} {G' : PlabicData H' b}

private theorem card_image_univ_eq (e : H ≃ H') {f : H → Finset H} {f' : H' → Finset H'}
    (h : ∀ d, (f d).map e.toEmbedding = f' (e d)) :
    (univ.image f).card = (univ.image f').card := by
  have key : (univ.image f).image (fun v => v.map e.toEmbedding) = univ.image f' := by
    ext v'
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨v, ⟨d, rfl⟩, rfl⟩
      exact ⟨e d, (h d).symm⟩
    · rintro ⟨d', rfl⟩
      exact ⟨_, ⟨e.symm d', rfl⟩, by rw [h, Equiv.apply_symm_apply]⟩
  rw [← key, card_image_of_injective _ (map_injective _)]

/-- Isomorphic tuples have the same number of vertices. -/
private theorem card_vertices (θ : G.Iso G') : G.vertices.card = G'.vertices.card :=
  card_image_univ_eq θ.toEquiv θ.map_vertexOf

/-- An isomorphism maps each edge `{d, d̄}` onto the edge `{θ d, θ d̄}`. -/
private theorem map_edgeOf (θ : G.Iso G') (d : H) :
    (G.edgeOf d).map θ.toEquiv.toEmbedding = G'.edgeOf (θ.toEquiv d) := by
  simp [RotationSystem.edgeOf, θ.map_inv]

/-- Isomorphic tuples have the same number of edges. -/
private theorem card_edges (θ : G.Iso G') : G.edges.card = G'.edges.card :=
  card_image_univ_eq θ.toEquiv θ.map_edgeOf

/-- Isomorphic tuples have the same number of orbits of the face permutation. -/
private theorem card_faceOrbits (θ : G.Iso G') : G.faceOrbits.card = G'.faceOrbits.card :=
  card_image_univ_eq θ.toEquiv θ.map_faceOf

/-- An isomorphism maps boundary vertices to boundary vertices, and only those. -/
private theorem map_mem_boundaryVertices_iff (θ : G.Iso G') {v : Finset H} :
    v.map θ.toEquiv.toEmbedding ∈ G'.boundaryVertices ↔ v ∈ G.boundaryVertices := by
  rw [DiskMap.mem_boundaryVertices, DiskMap.mem_boundaryVertices, RotationSystem.mem_vertices,
    RotationSystem.mem_vertices]
  have hb : G'.IsBoundaryVertex (v.map θ.toEquiv.toEmbedding) ↔ G.IsBoundaryVertex v := by
    simp only [DiskMap.IsBoundaryVertex, mem_map_equiv]
    constructor
    · rintro ⟨d, hd, hdB⟩
      exact ⟨_, hd, by rwa [← θ.mem_bdry_iff, Equiv.apply_symm_apply]⟩
    · rintro ⟨d, hd, hdB⟩
      exact ⟨θ.toEquiv d, by simpa using hd, (θ.mem_bdry_iff d).2 hdB⟩
  rw [hb]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨d', hd'⟩
    refine ⟨θ.toEquiv.symm d', map_injective θ.toEquiv.toEmbedding ?_⟩
    rw [θ.map_vertexOf, Equiv.apply_symm_apply, hd']
  · rintro ⟨d, rfl⟩
    exact ⟨θ.toEquiv d, (θ.map_vertexOf d).symm⟩

private theorem map_map_inv (θ : G.Iso G') (t : Finset H) :
    (t.map G.inv.toEmbedding).map θ.toEquiv.toEmbedding =
      (t.map θ.toEquiv.toEmbedding).map G'.inv.toEmbedding := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [θ.map_inv]

end Iso

/-- **Plabic graphs are transported along isomorphisms**: if `G` is isomorphic to a plabic graph
and its chosen darts `leg i` lie outside `B`, then `G` is a plabic graph. -/
theorem IsPlabicGraph.of_iso {G : PlabicData H b} {G' : PlabicData H' b} (θ : G.Iso G')
    (hG' : G'.IsPlabicGraph) (hleg : ∀ i, G.leg i ∉ G.bdry) : G.IsPlabicGraph := by
  have hθleg : ∀ i, θ.toEquiv (G.leg i) = G'.leg i := by
    intro i
    have h := θ.map_bvertex i
    rw [hG'.filter_bvertex_notMem_bdry] at h
    have hm : θ.toEquiv (G.leg i) ∈
        ((G.bvertex i).filter (· ∉ G.bdry)).map θ.toEquiv.toEmbedding :=
      mem_map_of_mem _ (mem_filter.2 ⟨G.leg_mem_bvertex i, hleg i⟩)
    rw [h] at hm
    exact mem_singleton.1 hm
  have hbv : ∀ i, (G.bvertex i).map θ.toEquiv.toEmbedding = G'.bvertex i := fun i => by
    rw [bvertex, θ.map_vertexOf, hθleg]
    rfl
  have hinv : Involutive G.inv := fun d =>
    θ.toEquiv.injective (by rw [θ.map_inv, θ.map_inv, hG'.inv_involutive])
  have hreach : ∀ {x' y' : H'}, G'.Reach x' y' →
      G.Reach (θ.toEquiv.symm x') (θ.toEquiv.symm y') := by
    intro x' y' h
    induction h with
    | refl => exact RotationSystem.Reach.refl _
    | rot _ ih =>
      rw [θ.symm_map_rot]
      exact ih.rot
    | inv _ ih =>
      rw [θ.symm_map_inv]
      exact ih.inv
  refine
    { toIsDiskMap :=
        { toIsConnected := RotationSystem.IsConnected.of_reach
            (hG'.nonempty.map θ.toEquiv.symm) hinv
            (fun d h => hG'.inv_ne (θ.toEquiv d) (by rw [← θ.map_inv, h]))
            (fun d e => by
              simpa using hreach (hG'.toIsConnected.reach (θ.toEquiv d) (θ.toEquiv e)))
          inv_mem_bdry := fun d hd => by
            rw [← θ.mem_bdry_iff, θ.map_inv]
            exact hG'.inv_mem_bdry _ ((θ.mem_bdry_iff d).2 hd)
          euler := by
            have h := hG'.euler
            rwa [← θ.card_vertices, ← θ.card_edges, ← θ.card_faceOrbits] at h
          boundaryVertex_card := ?_
          exists_orbit := ?_ }
      one_le := hG'.one_le
      colour_rot := ?_
      leg_notMem_bdry := hleg
      bvertex_mem := fun i => θ.map_mem_boundaryVertices_iff.1 (by
        rw [hbv]
        exact hG'.bvertex_mem i)
      bvertex_injective := fun i j h => hG'.bvertex_injective (by rw [← hbv, ← hbv, h])
      exists_bvertex_eq := ?_
      exists_exterior := ?_ }
  · intro v hv
    obtain ⟨h1, h2⟩ := hG'.boundaryVertex_card _ (θ.map_mem_boundaryVertices_iff.2 hv)
    rw [card_map] at h1
    refine ⟨h1, ?_⟩
    rw [filter_map, card_map] at h2
    rw [← h2]
    congr 1
    exact filter_congr fun x _ => by simp [θ.mem_bdry_iff]
  · obtain ⟨f', hf', hsub, hunion, hdisj⟩ := hG'.exists_orbit
    have hf : (f'.map θ.toEquiv.symm.toEmbedding).map θ.toEquiv.toEmbedding = f' := by
      ext y
      simp
    refine ⟨f'.map θ.toEquiv.symm.toEmbedding, ?_, ?_, ?_, ?_⟩
    · rw [← θ.map_mem_faceOrbits_iff, hf]
      exact hf'
    · intro x hx
      have : θ.toEquiv x ∈ f' := by
        rw [← hf]
        exact mem_map_of_mem _ hx
      exact (θ.mem_bdry_iff x).1 (hsub this)
    · apply map_injective θ.toEquiv.toEmbedding
      rw [map_union, Iso.map_map_inv, hf, hunion, θ.map_bdry]
    · rw [← disjoint_map θ.toEquiv.toEmbedding, Iso.map_map_inv, hf]
      exact hdisj
  · intro d hd
    have hd' : ¬G'.IsBoundaryVertex (G'.vertexOf (θ.toEquiv d)) := by
      rwa [θ.isBoundaryVertex_vertexOf_iff]
    have hrd : ¬G.IsBoundaryVertex (G.vertexOf (G.rot d)) := by
      rwa [G.vertexOf_rot]
    rw [← θ.map_colour _ hrd, θ.map_rot, hG'.colour_rot _ hd', θ.map_colour _ hd]
  · intro v hv
    obtain ⟨i, hi⟩ := hG'.exists_bvertex_eq _ (θ.map_mem_boundaryVertices_iff.2 hv)
    exact ⟨i, map_injective θ.toEquiv.toEmbedding (by rw [hbv, hi])⟩
  · intro i
    obtain ⟨d', hd', h1, h2⟩ := hG'.exists_exterior i
    refine ⟨θ.toEquiv.symm d', ?_, ?_, ?_⟩
    · rw [← θ.map_exterior, mem_map_equiv] at hd'
      exact hd'
    · rw [← hbv, mem_map_equiv] at h1
      exact h1
    · rw [← hbv, mem_map_equiv, θ.symm_map_inv] at h2
      exact h2

/-! ### Contracting the new edge of a splitting -/

section VertexSplit

omit [Fintype H] in
/-- The legs of a splitting avoid its new darts. -/
theorem vertexSplit_leg_mem {K : PlabicData H b} {s : H} {p : ℕ} (i : Fin b) :
    (K.vertexSplit s p).leg i ∈
      (({Sum.inr 0, (K.vertexSplit s p).inv (Sum.inr 0)} : Set (H ⊕ Fin 2))ᶜ :
        Set (H ⊕ Fin 2)) := by
  simp

variable (K : PlabicData H b) (s : H) (p : ℕ)

/-- The identification of the darts `H` of `K` with the darts of the contraction of a splitting of
`K` along its new edge is an isomorphism. -/
noncomputable def contractEdgeVertexSplitIso (hinv : Involutive K.inv) :
    K.Iso ((K.vertexSplit s p).contractEdge (Sum.inr 0) vertexSplit_leg_mem) :=
  Iso.ofEquivOfMapLeg (splitComplEquiv K.inv)
    (fun x => Subtype.ext (by
      rw [coe_contractEdge_inv (splitInv_involutive hinv)]
      rfl))
    (fun x => by
      change splitComplEquiv K.inv (K.rot x) =
        inducedRotationPerm (splitInv K.inv) (splitRot K.rot s p) (Sum.inr 0)
          (splitComplEquiv K.inv x)
      rw [inducedRotationPerm_splitRot, Equiv.permCongr_apply, Equiv.symm_apply_apply])
    (fun x => by
      rw [mem_contractEdge_bdry]
      change Sum.inl x ∈ K.bdry.map Embedding.inl ↔ x ∈ K.bdry
      simp)
    (fun _ _ => rfl)
    (fun _ => rfl)

/-- The darts of the vertex `z = v(s)` and the two new darts of a splitting at `z`. -/
private def splitSet (K : PlabicData H b) (s : H) : Set (H ⊕ Fin 2) :=
  {e | Sum.elim (fun x => K.rot.SameCycle s x) (fun _ => True) e}

omit [Fintype H] [DecidableEq H] in
@[simp]
private theorem inl_mem_splitSet {x : H} : Sum.inl x ∈ splitSet K s ↔ K.rot.SameCycle s x :=
  Iff.rfl

omit [Fintype H] [DecidableEq H] in
@[simp]
private theorem inr_mem_splitSet {i : Fin 2} : Sum.inr i ∈ splitSet K s := trivial

omit [Fintype H] in
/-- The rotation of a splitting maps the darts of `z` and the new darts among themselves. -/
private theorem rot_vertexSplit_mem_splitSet {e : H ⊕ Fin 2} (he : e ∈ splitSet K s) :
    (K.vertexSplit s p).rot e ∈ splitSet K s := by
  rcases e with x | i
  · rw [inl_mem_splitSet] at he
    rw [rot_vertexSplit, splitRot_inl]
    split_ifs <;> simp [he]
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · rw [rot_vertexSplit, splitRot_inr_zero]
      split_ifs <;> simp [SameCycle.refl]
    · rw [rot_vertexSplit, splitRot_inr_one]
      split_ifs <;> simp [sameCycle_pow_right, SameCycle.refl]

/-- The vertices of the darts of `z` and of the new darts in a splitting at an internal vertex `z`
are internal. -/
private theorem not_isBoundaryVertex_vertexSplit (hz : ¬K.IsBoundaryVertex (K.vertexOf s))
    {e : H ⊕ Fin 2} (he : e ∈ splitSet K s) :
    ¬(K.vertexSplit s p).IsBoundaryVertex ((K.vertexSplit s p).vertexOf e) := by
  rintro ⟨y, hy, hyB⟩
  have hyZ := mem_of_sameCycle_of_mapsTo (fun _ h => K.rot_vertexSplit_mem_splitSet s p h) he
    ((RotationSystem.mem_vertexOf _).1 hy)
  rw [bdry_vertexSplit, mem_map] at hyB
  obtain ⟨x, hx, rfl⟩ := hyB
  rw [Embedding.inl_apply, inl_mem_splitSet] at hyZ
  exact hz ⟨x, (RotationSystem.mem_vertexOf _).2 hyZ, hx⟩

/-- In the splitting of `K` at an internal vertex `z = v(s)` from `s` of size `p ∈ [0, k]`, the
new edge `{n, n̄}` joins two distinct internal vertices of the same colour. -/
@[cluster_algebras "lem_vertex_split_contraction"]
theorem isContractibleEdge_vertexSplit (hz : ¬K.IsBoundaryVertex (K.vertexOf s))
    (hp : p ≤ (K.vertexOf s).card) : (K.vertexSplit s p).IsContractibleEdge (Sum.inr 0) := by
  have hp' : p ≤ ({y | K.rot.SameCycle s y} : Finset H).card := hp
  have hint := fun e (he : e ∈ splitSet K s) => K.not_isBoundaryVertex_vertexSplit s p hz he
  -- the vertex of `n` is `{n, x_1, …, x_p}`
  let A : Set (H ⊕ Fin 2) := {e | e = Sum.inr 0 ∨ ∃ j < p, e = Sum.inl ((K.rot ^ j) s)}
  have hA : ∀ e ∈ A, (K.vertexSplit s p).rot e ∈ A := by
    rintro e (rfl | ⟨j, hj, rfl⟩)
    · rw [rot_vertexSplit, splitRot_inr_zero]
      split_ifs with h0
      · exact Or.inl rfl
      · exact Or.inr ⟨0, by omega, by simp⟩
    · rw [rot_vertexSplit, splitRot_inl_pow K.rot s p hp' (by omega)]
      split_ifs with h1 h2
      · exact Or.inl rfl
      · omega
      · exact Or.inr ⟨j + 1, by omega, rfl⟩
  have hd : (K.vertexSplit s p).inv (Sum.inr 0) = Sum.inr 1 := rfl
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [hd]
    intro h
    have h1 := mem_of_sameCycle_of_mapsTo hA (Or.inl rfl)
      ((K.vertexSplit s p).vertexOf_eq_vertexOf_iff.1 h)
    rcases h1 with h1 | ⟨j, -, h1⟩ <;> simp at h1
  · exact (K.vertexSplit s p).vertexOf_mem_internalVertices.2 (hint _ (by simp))
  · rw [hd]
    exact (K.vertexSplit s p).vertexOf_mem_internalVertices.2 (hint _ (by simp))

/-- **Contracting the new edge of a splitting gives back the graph**: the contraction of a
splitting of `K` along its new edge `{n, n̄}` is isomorphic to `K`, by the identification of its
darts `(H ⊔ {n, n̄}) \ {n, n̄}` with `H`. -/
@[cluster_algebras "lem_vertex_split_contraction"]
theorem isomorphic_contractEdge_vertexSplit (hinv : Involutive K.inv) :
    K.Isomorphic ((K.vertexSplit s p).contractEdge (Sum.inr 0) vertexSplit_leg_mem) :=
  ⟨K.contractEdgeVertexSplitIso s p hinv⟩

end VertexSplit

end PlabicData

/-! ### The darts of a graph as the darts of a contraction and two new darts -/

section ComplPair

variable {α : Type*} [DecidableEq α] (d e : α) (h : d ≠ e)

/-- The identification of `α` with `(α \ {d, e}) ⊕ Fin 2` sending `d` to `Sum.inr 0`, `e` to
`Sum.inr 1`, and every other element `x` to `Sum.inl x`. -/
def complPairSumEquiv : α ≃ (({d, e} : Set α)ᶜ : Set α) ⊕ Fin 2 where
  toFun x := if hd : x = d then Sum.inr 0 else if he : x = e then Sum.inr 1 else
    Sum.inl ⟨x, by simp [hd, he]⟩
  invFun := Sum.elim Subtype.val ![d, e]
  left_inv x := by
    dsimp only
    split_ifs with hd he
    · simp [hd]
    · simp [he]
    · rfl
  right_inv y := by
    rcases y with ⟨x, hx⟩ | i
    · have hx' : x ≠ d ∧ x ≠ e := by simpa [not_or] using hx
      simp [hx'.1, hx'.2]
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · simp
      · simp [h.symm]

/-- `complPairSumEquiv d e h` sends `d` to `Sum.inr 0`. -/
@[simp]
theorem complPairSumEquiv_left : complPairSumEquiv d e h d = Sum.inr 0 := by
  simp [complPairSumEquiv]

/-- `complPairSumEquiv d e h` sends `e` to `Sum.inr 1`. -/
@[simp]
theorem complPairSumEquiv_right : complPairSumEquiv d e h e = Sum.inr 1 := by
  simp [complPairSumEquiv, h.symm]

/-- `complPairSumEquiv d e h` sends an element `x` distinct from `d` and `e` to `Sum.inl x`. -/
theorem complPairSumEquiv_of_ne {x : α} (hd : x ≠ d) (he : x ≠ e) :
    complPairSumEquiv d e h x = Sum.inl ⟨x, by simp [hd, he]⟩ := by
  simp [complPairSumEquiv, hd, he]

/-- `complPairSumEquiv d e h` sends an element of `({d, e})ᶜ` to its image under `Sum.inl`. -/
@[simp]
theorem complPairSumEquiv_coe (x : (({d, e} : Set α)ᶜ : Set α)) :
    complPairSumEquiv d e h x = Sum.inl x := by
  have hx : (x : α) ≠ d ∧ (x : α) ≠ e := by
    have := x.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
    exact this
  rw [complPairSumEquiv_of_ne d e h hx.1 hx.2]

/-- The inverse of `complPairSumEquiv d e h` sends `Sum.inl x` to `x`. -/
@[simp]
theorem complPairSumEquiv_symm_inl (x : (({d, e} : Set α)ᶜ : Set α)) :
    (complPairSumEquiv d e h).symm (Sum.inl x) = x := rfl

/-- The inverse of `complPairSumEquiv d e h` sends `Sum.inr 0` to `d`. -/
@[simp]
theorem complPairSumEquiv_symm_inr_zero : (complPairSumEquiv d e h).symm (Sum.inr 0) = d := rfl

/-- The inverse of `complPairSumEquiv d e h` sends `Sum.inr 1` to `e`. -/
@[simp]
theorem complPairSumEquiv_symm_inr_one : (complPairSumEquiv d e h).symm (Sum.inr 1) = e := rfl

end ComplPair

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

/-! ### An edge is the splitting of its contraction -/

section ContractSplit

variable {G : PlabicData H b} {d : H} {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}

/-- The darts `σ^i(d)` and `σ^j(d̄)` lie at the two distinct endpoints. -/
private theorem pow_ne_pow_inv (he : G.IsContractibleEdge d) (i j : ℕ) :
    (G.rot ^ i) d ≠ (G.rot ^ j) (G.inv d) := by
  intro h
  apply he.not_sameCycle
  have h2 : G.rot.SameCycle ((G.rot ^ i) d) (G.inv d) := by
    rw [h]
    exact (sameCycle_pow_right.2 (SameCycle.refl _ _)).symm
  exact (sameCycle_pow_right.2 (SameCycle.refl _ _)).trans h2

/-- Along the merged vertex, the rotation of the contraction runs through `a₁, …, a_p`, where
`a_{j+1} = σ^{j+1}(d)`. -/
private theorem coe_contractEdge_rot_pow_of_lt (he : G.IsContractibleEdge d) {p : ℕ}
    (hcard : (G.vertexOf d).card = p + 1) (ha : G.rot d ∈ (({d, G.inv d} : Set H)ᶜ : Set H))
    {j : ℕ} (hj : j < p) :
    ((((G.contractEdge d hleg).rot ^ j) ⟨G.rot d, ha⟩ : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
      (G.rot ^ (j + 1)) d := by
  have hk : ({y | G.rot.SameCycle d y} : Finset H).card = p + 1 := hcard
  induction j with
  | zero => simp
  | succ j ih =>
    have hx := ih (by omega)
    have e1 : G.rot ((G.rot ^ (j + 1)) d) = (G.rot ^ (j + 1 + 1)) d := by
      rw [pow_succ' G.rot (j + 1), Perm.mul_apply]
    have hmem : G.rot (((G.contractEdge d hleg).rot ^ j) ⟨G.rot d, ha⟩ : H) ∈
        (({d, G.inv d} : Set H)ᶜ : Set H) := by
      rw [hx, e1, mem_compl_pair_iff]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := eq_of_pow_apply_eq_of_lt G.rot d (i := j + 1 + 1) (j := 0) (by omega) (by omega)
          (by rwa [pow_zero, Perm.one_apply])
        omega
      · have := pow_ne_pow_inv he (j + 1 + 1) 0
        rw [pow_zero, Perm.one_apply] at this
        exact this h
    rw [pow_succ', Perm.mul_apply, coe_contractEdge_rot_of_mem hmem, hx, e1]

/-- Along the merged vertex, after `a₁, …, a_p`, the rotation of the contraction runs through
`b₁, …, b_q`, where `b_{i+1} = σ^{i+1}(d̄)`. -/
private theorem coe_contractEdge_rot_pow_add_of_lt (he : G.IsContractibleEdge d) {p q : ℕ}
    (hcard : (G.vertexOf d).card = p + 1) (hcard' : (G.vertexOf (G.inv d)).card = q + 1)
    (ha : G.rot d ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) (hp : 1 ≤ p) {i : ℕ} (hi : i < q) :
    ((((G.contractEdge d hleg).rot ^ (p + i)) ⟨G.rot d, ha⟩ :
      (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = (G.rot ^ (i + 1)) (G.inv d) := by
  have hk : ({y | G.rot.SameCycle d y} : Finset H).card = p + 1 := hcard
  have hk' : ({y | G.rot.SameCycle (G.inv d) y} : Finset H).card = q + 1 := hcard'
  induction i with
  | zero =>
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    have hx := coe_contractEdge_rot_pow_of_lt (hleg := hleg) he hcard ha (j := p') (by omega)
    have e1 : G.rot (((G.contractEdge d hleg).rot ^ p') ⟨G.rot d, ha⟩ : H) = d := by
      rw [hx, ← Perm.mul_apply, ← pow_succ', ← hk]
      exact pow_card_orbit_apply G.rot d
    have hmem : G.rot (G.inv d) ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
      rw [mem_compl_pair_iff]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := pow_ne_pow_inv he 0 1
        rw [pow_zero, Perm.one_apply, pow_one] at this
        exact this h.symm
      · have := eq_of_pow_apply_eq_of_lt G.rot (G.inv d) (i := 1) (j := 0) (by omega) (by omega)
          (by rwa [pow_zero, Perm.one_apply, pow_one])
        omega
    rw [add_zero, pow_succ', Perm.mul_apply, coe_contractEdge_rot_of_eq e1 hmem, zero_add, pow_one]
  | succ i ih =>
    have hx := ih (by omega)
    have e1 : G.rot ((G.rot ^ (i + 1)) (G.inv d)) = (G.rot ^ (i + 1 + 1)) (G.inv d) := by
      rw [pow_succ' G.rot (i + 1), Perm.mul_apply]
    have hmem : G.rot (((G.contractEdge d hleg).rot ^ (p + i)) ⟨G.rot d, ha⟩ : H) ∈
        (({d, G.inv d} : Set H)ᶜ : Set H) := by
      rw [hx, e1, mem_compl_pair_iff]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := pow_ne_pow_inv he 0 (i + 1 + 1)
        rw [pow_zero, Perm.one_apply] at this
        exact this h.symm
      · have := eq_of_pow_apply_eq_of_lt G.rot (G.inv d) (i := i + 1 + 1) (j := 0) (by omega)
          (by omega) (by rwa [pow_zero, Perm.one_apply])
        omega
    rw [← add_assoc, pow_succ', Perm.mul_apply, coe_contractEdge_rot_of_mem hmem, hx, e1]

/-- The merged vertex has `|v(d)| + |v(d̄)| - 2` darts. -/
private theorem card_vertexOf_contractEdge_of_mem (he : G.IsContractibleEdge d)
    {x : (({d, G.inv d} : Set H)ᶜ : Set H)} (hx : (x : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    ((G.contractEdge d hleg).vertexOf x).card + 2 =
      (G.vertexOf d).card + (G.vertexOf (G.inv d)).card := by
  have h1 := map_vertexOf_contractEdge_of_mem (hleg := hleg) he.not_sameCycle hx
  have h2 : ((G.contractEdge d hleg).vertexOf x).card = (G.mergedVertex d).card := by
    rw [← h1, card_map]
  have hdisj : Disjoint (G.vertexOf d) (G.vertexOf (G.inv d)) :=
    disjoint_left.2 fun y h1 h2 =>
      he.vertexOf_ne ((G.vertexOf_eq_of_mem h1).symm.trans (G.vertexOf_eq_of_mem h2))
  have hsub : ({d, G.inv d} : Finset H) ⊆ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
    intro y hy
    rcases mem_insert.1 hy with rfl | hy
    · exact mem_union_left _ (G.self_mem_vertexOf _)
    · rw [mem_singleton.1 hy]
      exact mem_union_right _ (G.self_mem_vertexOf _)
  have hne : d ≠ G.inv d := fun h => he.vertexOf_ne (by rw [← h])
  have h3 := card_sdiff_add_card_eq_card hsub
  rw [card_union_of_disjoint hdisj, card_pair hne] at h3
  rw [h2, mergedVertex]
  omega

/-- The rotation of `G` agrees with the rotation of the splitting of its contraction along
`{d, d̄}` from `σ(d)` of size `|v(d)| - 1`, under the identification `complPairSumEquiv` of
darts. -/
theorem contractEdgeSplit_map_rot (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
    {p : ℕ} (hcard : (G.vertexOf d).card = p + 1)
    (ha : G.rot d ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) (x : H) :
    complPairSumEquiv d (G.inv d) (hG.inv_ne d).symm (G.rot x) =
      splitRot (G.contractEdge d hleg).rot ⟨G.rot d, ha⟩ p
        (complPairSumEquiv d (G.inv d) (hG.inv_ne d).symm x) := by
  set θ := complPairSumEquiv d (G.inv d) (hG.inv_ne d).symm
  set K := G.contractEdge d hleg
  set a : (({d, G.inv d} : Set H)ᶜ : Set H) := ⟨G.rot d, ha⟩
  obtain ⟨q, hq⟩ : ∃ q, (G.vertexOf (G.inv d)).card = q + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (card_pos.2 ⟨_, G.self_mem_vertexOf _⟩)).symm⟩
  have hk : ({y | G.rot.SameCycle d y} : Finset H).card = p + 1 := hcard
  have hk' : ({y | G.rot.SameCycle (G.inv d) y} : Finset H).card = q + 1 := hq
  have had := mem_compl_pair_iff.1 ha
  have hp1 : 1 ≤ p := by
    by_contra h0
    have := pow_card_orbit_apply G.rot d
    rw [hk, show p = 0 by omega, zero_add, pow_one] at this
    exact had.1 this
  have hA : ∀ j < p, ((K.rot ^ j) a : H) = (G.rot ^ (j + 1)) d := fun j hj =>
    coe_contractEdge_rot_pow_of_lt (hleg := hleg) he hcard ha hj
  have hB : ∀ i < q, ((K.rot ^ (p + i)) a : H) = (G.rot ^ (i + 1)) (G.inv d) := fun i hi =>
    coe_contractEdge_rot_pow_add_of_lt (hleg := hleg) he hcard hq ha hp1 hi
  have haU : (a : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
    mem_union_left _ (G.rot_mem_vertexOf d)
  have hkK : ({y | K.rot.SameCycle a y} : Finset _).card = p + q := by
    have := card_vertexOf_contractEdge_of_mem (hleg := hleg) he haU
    rw [hcard, hq] at this
    change ((G.contractEdge d hleg).vertexOf a).card = p + q
    omega
  have hpk : p ≤ ({y | K.rot.SameCycle a y} : Finset _).card := by omega
  obtain ⟨t, rfl⟩ := θ.symm.surjective x
  rw [Equiv.apply_symm_apply]
  rcases t with y | i
  · rw [complPairSumEquiv_symm_inl]
    have hy2 := mem_compl_pair_iff.1 y.2
    by_cases hyd : (y : H) ∈ G.vertexOf d
    · obtain ⟨i, hi, hiy⟩ :=
        exists_pow_lt_card_of_sameCycle G.rot ((RotationSystem.mem_vertexOf _).1 hyd)
      rw [hk] at hi
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := by
        rcases i with _ | j
        · rw [pow_zero, Perm.one_apply] at hiy
          exact absurd hiy.symm hy2.1
        · exact ⟨j, rfl⟩
      have hy : y = (K.rot ^ j) a := Subtype.ext (by rw [hA j (by omega), hiy])
      have e1 : G.rot ((G.rot ^ (j + 1)) d) = (G.rot ^ (j + 1 + 1)) d := by
        rw [pow_succ' G.rot (j + 1), Perm.mul_apply]
      rw [hy, splitRot_inl_pow K.rot a p hpk (by omega), hA j (by omega), e1, hkK]
      split_ifs with h1 h2
      · have : (G.rot ^ (j + 1 + 1)) d = d := by
          rw [show j + 1 + 1 = ({y | G.rot.SameCycle d y} : Finset H).card by omega]
          exact pow_card_orbit_apply G.rot d
        rw [this, complPairSumEquiv_left]
      · omega
      · rw [← hA (j + 1) (by omega), complPairSumEquiv_coe]
    by_cases hyd' : (y : H) ∈ G.vertexOf (G.inv d)
    · obtain ⟨i, hi, hiy⟩ :=
        exists_pow_lt_card_of_sameCycle G.rot ((RotationSystem.mem_vertexOf _).1 hyd')
      rw [hk'] at hi
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := by
        rcases i with _ | m
        · rw [pow_zero, Perm.one_apply] at hiy
          exact absurd hiy.symm hy2.2
        · exact ⟨m, rfl⟩
      have hy : y = (K.rot ^ (p + m)) a := Subtype.ext (by rw [hB m (by omega), hiy])
      have e1 : G.rot ((G.rot ^ (m + 1)) (G.inv d)) = (G.rot ^ (m + 1 + 1)) (G.inv d) := by
        rw [pow_succ' G.rot (m + 1), Perm.mul_apply]
      rw [hy, splitRot_inl_pow K.rot a p hpk (by omega), hB m (by omega), e1, hkK]
      split_ifs with h1 h2
      · omega
      · have : (G.rot ^ (m + 1 + 1)) (G.inv d) = G.inv d := by
          rw [show m + 1 + 1 = ({y | G.rot.SameCycle (G.inv d) y} : Finset H).card by omega]
          exact pow_card_orbit_apply G.rot (G.inv d)
        rw [this, complPairSumEquiv_right]
      · rw [show p + m + 1 = p + (m + 1) by omega, ← hB (m + 1) (by omega),
          complPairSumEquiv_coe]
    · have hyU : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
        rw [mem_union, not_or]
        exact ⟨hyd, hyd'⟩
      have hrm := mem_compl_pair_of_notMem (rot_notMem_of_notMem hyU)
      have hσ : ((K.rot y : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = G.rot y :=
        coe_contractEdge_rot_of_mem hrm
      have hns : ¬K.rot.SameCycle a y := by
        intro h
        have hm : (y : H) ∈ G.mergedVertex d := by
          rw [← map_vertexOf_contractEdge_of_mem (hleg := hleg) he.not_sameCycle haU]
          exact mem_map_of_mem _ ((RotationSystem.mem_vertexOf _).2 h)
        exact hyU (mem_union.2 (mem_mergedVertex.1 hm).1)
      rw [splitRot_inl_of_not_sameCycle _ _ _ hns, ← hσ, complPairSumEquiv_coe]
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · rw [complPairSumEquiv_symm_inr_zero, splitRot_inr_zero, if_neg (by omega)]
      exact complPairSumEquiv_coe _ _ _ a
    · rw [complPairSumEquiv_symm_inr_one, splitRot_inr_one_of_le K.rot a p hpk, hkK]
      split_ifs with h
      · have : (G.rot ^ 1) (G.inv d) = G.inv d := by
          rw [show 1 = ({y | G.rot.SameCycle (G.inv d) y} : Finset H).card by omega]
          exact pow_card_orbit_apply G.rot (G.inv d)
        rw [pow_one] at this
        rw [this, complPairSumEquiv_right]
      · have : ((K.rot ^ p) a : H) = G.rot (G.inv d) := by
          simpa using hB 0 (by omega)
        rw [← this, complPairSumEquiv_coe]

/-- The identification `complPairSumEquiv` of the darts of `G` with those of a splitting of its
contraction along `{d, d̄}` with new darts `d`, `d̄` intertwines the involutions. -/
theorem complPairSumEquiv_inv_vertexSplit (hinv : Involutive G.inv) (hne : d ≠ G.inv d)
    (s : (({d, G.inv d} : Set H)ᶜ : Set H)) (p : ℕ) (x : H) :
    complPairSumEquiv d (G.inv d) hne (G.inv x) =
      ((G.contractEdge d hleg).vertexSplit s p).inv (complPairSumEquiv d (G.inv d) hne x) := by
  by_cases hx : x = d
  · subst hx
    simp
  by_cases hx' : x = G.inv d
  · subst hx'
    rw [hinv]
    simp
  · have hm' : G.inv x ≠ d ∧ G.inv x ≠ G.inv d := by
      refine ⟨fun h => hx' ?_, fun h => hx (hinv.injective h)⟩
      rw [← h, hinv]
    rw [complPairSumEquiv_of_ne _ _ _ hx hx', complPairSumEquiv_of_ne _ _ _ hm'.1 hm'.2,
      inv_vertexSplit, splitInv_inl]
    congr 1
    apply Subtype.ext
    rw [coe_contractEdge_inv hinv]

/-- The identification `complPairSumEquiv` matches `B` with the boundary arcs of a splitting of the
contraction. -/
theorem complPairSumEquiv_mem_bdry_vertexSplit_iff (he : G.IsContractibleEdge d)
    (hne : d ≠ G.inv d) (s : (({d, G.inv d} : Set H)ᶜ : Set H)) (p : ℕ) (x : H) :
    complPairSumEquiv d (G.inv d) hne x ∈ ((G.contractEdge d hleg).vertexSplit s p).bdry ↔
      x ∈ G.bdry := by
  have hdB : d ∉ G.bdry := fun h => (mem_compl_pair_iff.1 (he.mem_of_mem_bdry h)).1 rfl
  have hdB' : G.inv d ∉ G.bdry := fun h => (mem_compl_pair_iff.1 (he.mem_of_mem_bdry h)).2 rfl
  by_cases hx : x = d
  · subst hx
    simp [hdB]
  by_cases hx' : x = G.inv d
  · subst hx'
    simp [hdB']
  · rw [complPairSumEquiv_of_ne _ _ _ hx hx']
    simp

/-- The identification `complPairSumEquiv` maps the legs of `G` to the legs of a splitting of the
contraction. -/
theorem complPairSumEquiv_leg_vertexSplit (hne : d ≠ G.inv d)
    (s : (({d, G.inv d} : Set H)ᶜ : Set H)) (p : ℕ) (i : Fin b) :
    complPairSumEquiv d (G.inv d) hne (G.leg i) =
      ((G.contractEdge d hleg).vertexSplit s p).leg i := by
  have hl := mem_compl_pair_iff.1 (hleg i)
  rw [complPairSumEquiv_of_ne _ _ _ hl.1 hl.2]
  rfl

/-- The isomorphism of `G` with the splitting of its contraction along `{d, d̄}` at the merged
vertex from `σ(d)` of size `p = |v(d)| - 1`, with new darts `d` and `d̄`. -/
noncomputable def contractEdgeSplitIso (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
    {p : ℕ} (hcard : (G.vertexOf d).card = p + 1)
    (ha : G.rot d ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    G.Iso ((G.contractEdge d hleg).vertexSplit ⟨G.rot d, ha⟩ p) :=
  Iso.ofEquivOfMapLeg (complPairSumEquiv d (G.inv d) (hG.inv_ne d).symm)
    (complPairSumEquiv_inv_vertexSplit hG.inv_involutive _ _ _)
    (contractEdgeSplit_map_rot hG he hcard ha)
    (complPairSumEquiv_mem_bdry_vertexSplit_iff he _ _ _)
    (fun x _ => by
      have hcol : G.colour (G.rot d) = G.colour d := hG.colour_rot d he.not_isBoundaryVertex
      by_cases hx : x = d
      · subst hx
        simp [hcol]
      by_cases hx' : x = G.inv d
      · subst hx'
        simp [hcol, he.colour_inv]
      · rw [complPairSumEquiv_of_ne _ _ _ hx hx']
        rfl)
    (complPairSumEquiv_leg_vertexSplit _ _ _)

/-- **An edge is the splitting of its contraction**. Let `{d, d̄}` be an edge of the plabic graph
`G` whose endpoints are distinct internal vertices of the same colour, with `v(d)` consisting of
`p + 1` darts and `σ(d) ∉ {d, d̄}` (so `p ≥ 1`). Then `G` is isomorphic to the splitting of the
contraction `K` of `G` along `{d, d̄}` at the vertex of `K` containing `σ(d)`, from `σ(d)`, of size
`p`; the isomorphism `complPairSumEquiv` sends `d` and `d̄` to the new darts `n` and `n̄` and fixes
every other dart. -/
@[cluster_algebras "lem_contraction_split_inverse"]
theorem isomorphic_vertexSplit_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
    {p : ℕ} (hcard : (G.vertexOf d).card = p + 1)
    (ha : G.rot d ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    G.Isomorphic ((G.contractEdge d hleg).vertexSplit ⟨G.rot d, ha⟩ p) :=
  ⟨contractEdgeSplitIso hG he hcard ha⟩

end ContractSplit

/-! ### A flip is a rotated splitting of a contraction -/

section Flip

variable {G : PlabicData H b} {d : H}

/-- The endpoints of an edge satisfying the conditions of the flip move satisfy the conditions of
the contraction. -/
theorem IsFlipEdge.isContractibleEdge (hf : G.IsFlipEdge d) : G.IsContractibleEdge d :=
  ⟨hf.vertexOf_ne, G.vertexOf_mem_internalVertices.2 hf.not_isBoundaryVertex,
    G.vertexOf_mem_internalVertices.2 hf.not_isBoundaryVertex_inv, hf.colour_inv⟩

/-- At an edge satisfying the conditions of the flip move, `a₂ = σ²(d)` is neither `d` nor `d̄`. -/
theorem IsFlipEdge.rot_rot_mem (hf : G.IsFlipEdge d) :
    G.rot (G.rot d) ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
  obtain ⟨-, -, n2, -, -⟩ := three_cycle_of_card hf.card_vertexOf
  have := pow_ne_pow_inv hf.isContractibleEdge 2 0
  rw [pow_zero, Perm.one_apply, pow_two, Perm.mul_apply] at this
  exact mem_compl_pair_iff.2 ⟨n2.symm, this⟩

variable {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}

/-- A dart outside the trivalent vertex `{d, σ(d), σ²(d)}` does not lie at the vertex of `d`. -/
theorem notMem_vertexOf_of_ne {y : H}
    (h : ∀ z, G.rot.SameCycle d z → z = d ∨ z = G.rot d ∨ z = G.rot (G.rot d)) (h₀ : y ≠ d)
    (h₁ : y ≠ G.rot d) (h₂ : y ≠ G.rot (G.rot d)) : y ∉ G.vertexOf d := fun hy => by
  rcases h y ((RotationSystem.mem_vertexOf _).1 hy) with h | h | h <;> contradiction

/-- The rotation of the flip agrees with the rotation of the splitting of the contraction along
`{d, d̄}` from `a₂` of size `2`, under the identification `complPairSumEquiv` of darts. -/
theorem flipMove_map_rot (hG : G.IsPlabicGraph) (hf : G.IsFlipEdge d)
    (ha : G.rot (G.rot d) ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) (x : H) :
    complPairSumEquiv d (G.inv d) (hG.inv_ne d).symm (flipRot G.rot G.inv d x) =
      splitRot (G.contractEdge d hleg).rot ⟨G.rot (G.rot d), ha⟩ 2
        (complPairSumEquiv d (G.inv d) (hG.inv_ne d).symm x) := by
  have he := hf.isContractibleEdge
  set θ := complPairSumEquiv d (G.inv d) (hG.inv_ne d).symm
  set K := G.contractEdge d hleg
  obtain ⟨h3, n1, n2, n3, hx3⟩ := three_cycle_of_card hf.card_vertexOf
  obtain ⟨h3', m1, m2, m3, hy3⟩ := three_cycle_of_card hf.card_vertexOf_inv
  have hc : ∀ i j : ℕ, G.rot^[i] d ≠ G.rot^[j] (G.inv d) := fun i j => by
    have := pow_ne_pow_inv he i j
    rwa [← Perm.iterate_eq_pow, ← Perm.iterate_eq_pow] at this
  have c01 : d ≠ G.rot (G.inv d) := hc 0 1
  have c02 : d ≠ G.rot (G.rot (G.inv d)) := hc 0 2
  have c10 : G.rot d ≠ G.inv d := hc 1 0
  have c11 : G.rot d ≠ G.rot (G.inv d) := hc 1 1
  have c21 : G.rot (G.rot d) ≠ G.rot (G.inv d) := hc 2 1
  have c22 : G.rot (G.rot d) ≠ G.rot (G.rot (G.inv d)) := hc 2 2
  have ma1 : G.rot d ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2 ⟨n1.symm, c10⟩
  have mb1 : G.rot (G.inv d) ∈ (({d, G.inv d} : Set H)ᶜ : Set H) :=
    mem_compl_pair_iff.2 ⟨c01.symm, m1.symm⟩
  have mb2 : G.rot (G.rot (G.inv d)) ∈ (({d, G.inv d} : Set H)ᶜ : Set H) :=
    mem_compl_pair_iff.2 ⟨c02.symm, m2.symm⟩
  set a1 : (({d, G.inv d} : Set H)ᶜ : Set H) := ⟨_, ma1⟩
  set a2 : (({d, G.inv d} : Set H)ᶜ : Set H) := ⟨_, ha⟩
  set b1 : (({d, G.inv d} : Set H)ᶜ : Set H) := ⟨_, mb1⟩
  set b2 : (({d, G.inv d} : Set H)ᶜ : Set H) := ⟨_, mb2⟩
  have r1 : K.rot a1 = a2 := Subtype.ext (coe_contractEdge_rot_of_mem ha)
  have r2 : K.rot a2 = b1 := Subtype.ext (coe_contractEdge_rot_of_eq h3 mb1)
  have r3 : K.rot b1 = b2 := Subtype.ext (coe_contractEdge_rot_of_mem mb2)
  have r4 : K.rot b2 = a1 := Subtype.ext (coe_contractEdge_rot_of_eq_inv h3' ma1)
  have hpow1 : (K.rot ^ (2 - 1)) a2 = b1 := by rw [show 2 - 1 = 1 from rfl, pow_one, r2]
  have hne : ∀ {u v : (({d, G.inv d} : Set H)ᶜ : Set H)}, (u : H) ≠ v → u ≠ v :=
    fun h e => h (congrArg Subtype.val e)
  obtain ⟨t, rfl⟩ := θ.symm.surjective x
  rw [Equiv.apply_symm_apply]
  rcases t with y | i
  · rw [complPairSumEquiv_symm_inl, splitRot_inl, hpow1]
    by_cases y1 : y = a1
    · subst y1
      rw [hf.flipRot_apply_rot, if_neg (fun h => hne c11 h.2), if_pos r1, complPairSumEquiv_right]
    by_cases y2 : y = a2
    · subst y2
      rw [hf.flipRot_apply_rot_rot, if_neg (fun h => hne c21 h.2),
        if_neg (by rw [r2]; exact hne c21.symm), r2]
      exact complPairSumEquiv_coe _ _ _ b1
    by_cases y3 : y = b1
    · subst y3
      rw [hf.flipRot_apply_rot_inv, if_pos ⟨by norm_num, rfl⟩, complPairSumEquiv_left]
    by_cases y4 : y = b2
    · subst y4
      rw [hf.flipRot_apply_rot_rot_inv, if_neg (fun h => hne m3.symm h.2),
        if_neg (by rw [r4]; exact hne n3), r4]
      exact complPairSumEquiv_coe _ _ _ a1
    · have hy := mem_compl_pair_iff.1 y.2
      have hyx := notMem_vertexOf_of_ne hx3 hy.1 (fun h => y1 (Subtype.ext h))
        (fun h => y2 (Subtype.ext h))
      have hyy := notMem_vertexOf_of_ne hy3 hy.2 (fun h => y3 (Subtype.ext h))
        (fun h => y4 (Subtype.ext h))
      have hrm := mem_compl_pair_of_notMem
        (rot_notMem_of_notMem fun h => (mem_union.1 h).elim hyx hyy)
      have hσ : K.rot y = ⟨G.rot y, hrm⟩ := Subtype.ext (coe_contractEdge_rot_of_mem hrm)
      have hσa : K.rot y ≠ a2 := by
        rw [hσ]
        exact fun h => y1 (Subtype.ext (G.rot.injective (congrArg Subtype.val h)))
      rw [hf.flipRot_apply_of_notMem hyx hyy, if_neg (fun h => y3 h.2), if_neg hσa, hσ]
      exact complPairSumEquiv_coe _ _ _ ⟨G.rot y, hrm⟩
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · rw [complPairSumEquiv_symm_inr_zero, hf.flipRot_apply_self, splitRot_inr_zero,
        if_neg (by norm_num)]
      exact complPairSumEquiv_coe _ _ _ a2
    · have hsq : (K.rot ^ 2) a2 = b2 := by rw [pow_two, Perm.mul_apply, r2, r3]
      rw [complPairSumEquiv_symm_inr_one, hf.flipRot_apply_inv, splitRot_inr_one, hsq,
        if_neg (fun h => hne c22.symm h.2)]
      exact complPairSumEquiv_coe _ _ _ b2

/-- The isomorphism of the flip of `G` at `{d, d̄}` with the splitting of the contraction of `G`
along `{d, d̄}` at its merged vertex, from `a₂ = σ²(d)`, of size `2`, with new darts `d` and
`d̄`. -/
noncomputable def flipMoveSplitIso (hG : G.IsPlabicGraph) (hf : G.IsFlipEdge d)
    (ha : G.rot (G.rot d) ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.flipMove d).Iso ((G.contractEdge d hleg).vertexSplit ⟨G.rot (G.rot d), ha⟩ 2) :=
  Iso.ofEquivOfMapLeg (complPairSumEquiv d (G.inv d) (hG.inv_ne d).symm)
    (complPairSumEquiv_inv_vertexSplit hG.inv_involutive _ _ _)
    (flipMove_map_rot hG hf ha)
    (complPairSumEquiv_mem_bdry_vertexSplit_iff hf.isContractibleEdge _ _ _)
    (fun x _ => by
      have he := hf.isContractibleEdge
      have hmem : G.rot (G.rot d) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
        refine mem_union_left _ ?_
        rw [← G.vertexOf_rot d]
        exact G.rot_mem_vertexOf _
      have hcol : G.colour (G.rot (G.rot d)) = G.colour d := colour_eq_of_mem_union hG he hmem
      rw [colour_flipMove]
      by_cases hx : x = d
      · subst hx
        simp [hcol, G.self_mem_vertexOf]
      by_cases hx' : x = G.inv d
      · subst hx'
        simp [hcol, G.self_mem_vertexOf]
      · rw [complPairSumEquiv_of_ne _ _ _ hx hx']
        split_ifs with h
        · exact colour_eq_of_mem_union hG he h
        · rfl)
    (complPairSumEquiv_leg_vertexSplit _ _ _)

/-- **A flip is a rotated splitting of a contraction**. Let `{d, d̄}` be an edge of the plabic
graph `G` satisfying the conditions of the flip move, with `a₂ = σ²(d)`. Then the flip of `G` at
`{d, d̄}` is isomorphic to the splitting of the contraction `K` of `G` along `{d, d̄}` at the
vertex of `K` containing `a₁ = σ(d)` (which contains `a₂`), from `a₂`, of size `2`; the isomorphism
`complPairSumEquiv` sends `d` and `d̄` to the new darts `n` and `n̄` and fixes every other dart. -/
@[cluster_algebras "lem_flip_is_split"]
theorem isomorphic_flipMove_vertexSplit (hG : G.IsPlabicGraph) (hf : G.IsFlipEdge d)
    (ha : G.rot (G.rot d) ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.flipMove d).Isomorphic ((G.contractEdge d hleg).vertexSplit ⟨G.rot (G.rot d), ha⟩ 2) :=
  ⟨flipMoveSplitIso hG hf ha⟩

/-- The flip of a plabic graph at a flip edge is a plabic graph. -/
@[cluster_algebras "lem_flip_plabic"]
theorem IsPlabicGraph.flipMove (hG : G.IsPlabicGraph) (hf : G.IsFlipEdge d) :
    (G.flipMove d).IsPlabicGraph := by
  have he := hf.isContractibleEdge
  have hleg := he.leg_mem hG
  have ha := hf.rot_rot_mem
  have hz : ¬(G.contractEdge d hleg).IsBoundaryVertex
      ((G.contractEdge d hleg).vertexOf ⟨G.rot (G.rot d), ha⟩) := by
    rw [isBoundaryVertex_vertexOf_contractEdge_iff he, G.vertexOf_rot, G.vertexOf_rot]
    exact hf.not_isBoundaryVertex
  exact IsPlabicGraph.of_iso (flipMoveSplitIso (hleg := hleg) hG hf ha)
    ((hG.contractEdge he).vertexSplit hz 2) hG.leg_notMem_bdry

end Flip

/-! ### Splitting a vertex with at least four darts -/

section Resolution

/-- The excess `∑ (|v(x)| - 3)` over the darts `x` at internal vertices; it vanishes on a graph
whose internal vertices have exactly three darts, and decreases under the splittings used to
build resolutions. -/
private def excess (G : PlabicData H b) : ℕ :=
  ∑ x, if G.IsBoundaryVertex (G.vertexOf x) then 0 else (G.vertexOf x).card - 3

private theorem rot_ne_self_of_two_le (K : PlabicData H b) (s : H)
    (hk : 2 ≤ ({y | K.rot.SameCycle s y} : Finset H).card) : K.rot s ≠ s := by
  intro h
  have := eq_of_pow_apply_eq_of_lt K.rot s (i := 1) (j := 0) (by omega) (by omega)
    (by rwa [pow_one, pow_zero, Perm.one_apply])
  omega

omit [Fintype H] in
private theorem card_vertexSplit_two_triple (K : PlabicData H b) (s : H) (hs1 : K.rot s ≠ s) :
    ({Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} : Finset (H ⊕ Fin 2)).card = 3 := by
  refine card_eq_three.2 ⟨_, _, _, by simp, by simp, ?_, rfl⟩
  simpa using hs1.symm

/-- After splitting `s` with size `2`, the new dart `n` lies at the vertex `{n, s, σ s}`. -/
private theorem vertexOf_vertexSplit_two_inr_zero (K : PlabicData H b) (s : H)
    (hs1 : K.rot s ≠ s) :
    (K.vertexSplit s 2).vertexOf (Sum.inr 0) = {Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} := by
  set S := K.vertexSplit s 2
  have hsr : ∀ e, S.rot e = splitRot K.rot s 2 e := fun _ => rfl
  have e0 : S.rot (Sum.inr 0) = Sum.inl s := by rw [hsr, splitRot_inr_zero, if_neg (by norm_num)]
  have e1 : S.rot (Sum.inl s) = Sum.inl (K.rot s) := by
    rw [hsr, splitRot_inl, if_neg, if_neg hs1]
    rintro ⟨-, h⟩
    rw [show 2 - 1 = 1 from rfl, pow_one] at h
    exact hs1 h.symm
  have e2 : S.rot (Sum.inl (K.rot s)) = Sum.inr 0 := by
    rw [hsr, splitRot_inl, if_pos]
    exact ⟨by norm_num, by rw [show 2 - 1 = 1 from rfl, pow_one]⟩
  ext e
  rw [RotationSystem.mem_vertexOf]
  constructor
  · intro h
    refine mem_of_sameCycle_of_mapsTo
      (A := (({Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} : Finset (H ⊕ Fin 2)) : Set (H ⊕ Fin 2)))
      ?_ (by simp) h
    intro a ha
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl <;> simp [e0, e1, e2]
  · intro h
    simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact SameCycle.refl _ _
    · rw [← e0]
      exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    · rw [← e1, ← e0]
      exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))

private theorem vertexOf_vertexSplit_two_of_mem (K : PlabicData H b) (s : H) (hs1 : K.rot s ≠ s)
    {e : H ⊕ Fin 2} (he : e ∈ ({Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} : Finset (H ⊕ Fin 2))) :
    (K.vertexSplit s 2).vertexOf e = {Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} := by
  rw [← vertexOf_vertexSplit_two_inr_zero K s hs1] at he ⊢
  exact (K.vertexSplit s 2).vertexOf_eq_of_mem he

/-- After splitting `s` with size `2`, the other new dart `n̄` lies at the vertex of `σ ^ j s`
for `2 ≤ j < k`. -/
private theorem sameCycle_vertexSplit_two_inr_one (K : PlabicData H b) (s : H) {j : ℕ}
    (hj2 : 2 ≤ j) (hjk : j < ({y | K.rot.SameCycle s y} : Finset H).card) :
    (K.vertexSplit s 2).rot.SameCycle (Sum.inr 1) (Sum.inl ((K.rot ^ j) s)) := by
  set S := K.vertexSplit s 2
  set k := ({y | K.rot.SameCycle s y} : Finset H).card
  have hsr : ∀ e, S.rot e = splitRot K.rot s 2 e := fun _ => rfl
  induction j, hj2 using Nat.le_induction with
  | base =>
    have : S.rot (Sum.inr 1) = Sum.inl ((K.rot ^ 2) s) := by
      rw [hsr, splitRot_inr_one_of_le K.rot s 2 (by omega), if_neg (by omega)]
    rw [← this]
    exact sameCycle_apply_right.2 (SameCycle.refl _ _)
  | succ j hj ih =>
    have : S.rot (Sum.inl ((K.rot ^ j) s)) = Sum.inl ((K.rot ^ (j + 1)) s) := by
      rw [hsr, splitRot_inl_pow K.rot s 2 (by omega) (by omega), if_neg (by omega),
        if_neg (by omega)]
    rw [← this]
    exact sameCycle_apply_right.2 (ih (by omega))

/-- Splitting a vertex with `k ≥ 4` darts with size `2` produces vertices with at most `k - 1`
darts. -/
private theorem card_vertexOf_vertexSplit_two_le (K : PlabicData H b) (s : H)
    (hk : 4 ≤ ({y | K.rot.SameCycle s y} : Finset H).card) (e : H ⊕ Fin 2)
    (he : e ∈ splitSet K s) :
    ((K.vertexSplit s 2).vertexOf e).card ≤ ({y | K.rot.SameCycle s y} : Finset H).card - 1 := by
  set S := K.vertexSplit s 2
  set k := ({y | K.rot.SameCycle s y} : Finset H).card
  have hs1 := rot_ne_self_of_two_le K s (by omega)
  set A0 : Finset (H ⊕ Fin 2) := {Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)}
  have hA0 : S.vertexOf (Sum.inr 0) = A0 := vertexOf_vertexSplit_two_inr_zero K s hs1
  have hA0card : A0.card = 3 := card_vertexSplit_two_triple K s hs1
  let Zf : Finset (H ⊕ Fin 2) := (K.vertexOf s).map Embedding.inl ∪ {Sum.inr 0, Sum.inr 1}
  have hZf : ∀ e, e ∈ splitSet K s → e ∈ Zf := by
    rintro (x | i) he
    · rw [inl_mem_splitSet] at he
      exact mem_union_left _ (mem_map_of_mem _ ((RotationSystem.mem_vertexOf _).2 he))
    · fin_cases i <;> simp [Zf]
  have hZfcard : Zf.card = k + 2 := by
    rw [card_union_of_disjoint, card_map, card_pair (by simp)]
    · rfl
    · rw [disjoint_left]
      intro e he he'
      simp only [mem_map, Embedding.inl_apply] at he
      obtain ⟨x, -, rfl⟩ := he
      simp at he'
  have hsub : ∀ e ∈ splitSet K s, S.vertexOf e ⊆ Zf := fun e he y hy =>
    hZf _ (mem_of_sameCycle_of_mapsTo (fun _ h => K.rot_vertexSplit_mem_splitSet s 2 h) he
      ((RotationSystem.mem_vertexOf _).1 hy))
  have hA0Zf : A0 ⊆ Zf := by
    rw [← hA0]
    exact hsub _ (by simp)
  by_cases h : S.vertexOf e = A0
  · rw [h, hA0card]
    omega
  · have hdisj : Disjoint (S.vertexOf e) A0 := by
      rw [disjoint_left]
      intro y hy hy'
      rw [← hA0] at hy'
      exact h ((S.vertexOf_eq_of_mem hy).symm.trans ((S.vertexOf_eq_of_mem hy').trans hA0))
    have h1 : S.vertexOf e ⊆ Zf \ A0 := fun y hy =>
      mem_sdiff.2 ⟨hsub e he hy, disjoint_left.1 hdisj hy⟩
    have h2 := card_le_card h1
    have h3' := card_sdiff_add_card_eq_card hA0Zf
    omega

/-- Splitting a vertex with `k ≥ 4` darts with size `2` produces vertices with at least `3`
darts. -/
private theorem three_le_card_vertexOf_vertexSplit_two (K : PlabicData H b) (s : H)
    (hk : 4 ≤ ({y | K.rot.SameCycle s y} : Finset H).card) (e : H ⊕ Fin 2)
    (he : e ∈ splitSet K s) : 3 ≤ ((K.vertexSplit s 2).vertexOf e).card := by
  set S := K.vertexSplit s 2
  set k := ({y | K.rot.SameCycle s y} : Finset H).card
  have hs1 := rot_ne_self_of_two_le K s (by omega)
  have hcases : S.vertexOf e = {Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} ∨
      S.rot.SameCycle (Sum.inr 1) e := by
    rcases e with x | i
    · rw [inl_mem_splitSet] at he
      obtain ⟨j, hj, rfl⟩ := exists_pow_lt_card_of_sameCycle K.rot he
      rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | h2
      · exact Or.inl (vertexOf_vertexSplit_two_of_mem K s hs1 (by simp))
      · exact Or.inl (vertexOf_vertexSplit_two_of_mem K s hs1 (by simp))
      · exact Or.inr (sameCycle_vertexSplit_two_inr_one K s h2 hj)
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · exact Or.inl (vertexOf_vertexSplit_two_inr_zero K s hs1)
      · exact Or.inr (SameCycle.refl _ _)
  rcases hcases with h | h
  · rw [h, card_vertexSplit_two_triple K s hs1]
  · rw [← S.vertexOf_eq_vertexOf_iff.2 h]
    have hsub3 : ({Sum.inr 1, Sum.inl ((K.rot ^ 2) s), Sum.inl ((K.rot ^ 3) s)} :
        Finset (H ⊕ Fin 2)) ⊆ S.vertexOf (Sum.inr 1) := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rw [RotationSystem.mem_vertexOf]
      rcases hy with rfl | rfl | rfl
      · exact SameCycle.refl _ _
      · exact sameCycle_vertexSplit_two_inr_one K s le_rfl (by omega)
      · exact sameCycle_vertexSplit_two_inr_one K s (by omega) (by omega)
    have h3card : ({Sum.inr 1, Sum.inl ((K.rot ^ 2) s), Sum.inl ((K.rot ^ 3) s)} :
        Finset (H ⊕ Fin 2)).card = 3 := by
      refine card_eq_three.2 ⟨_, _, _, by simp, by simp, ?_, rfl⟩
      have hne : (K.rot ^ 2) s ≠ (K.rot ^ 3) s := fun h =>
        absurd (eq_of_pow_apply_eq_of_lt K.rot s (by omega) (by omega) h) (by omega)
      simpa using hne
    rw [← h3card]
    exact card_le_card hsub3

/-- Splitting a vertex `z` with `k ≥ 4` darts from `s` with size `2` keeps all internal vertices
of size at least three. -/
private theorem three_le_card_of_mem_internalVertices_vertexSplit_two (K : PlabicData H b)
    (s : H) (hk : 4 ≤ (K.vertexOf s).card) (h3 : ∀ v ∈ K.internalVertices, 3 ≤ v.card) :
    ∀ v ∈ (K.vertexSplit s 2).internalVertices, 3 ≤ v.card := by
  intro v hv
  obtain ⟨hvV, hvB⟩ := (DiskMap.mem_internalVertices _).1 hv
  obtain ⟨e, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
  by_cases he : e ∈ splitSet K s
  · exact three_le_card_vertexOf_vertexSplit_two K s hk e he
  · rcases e with x | i
    · rw [inl_mem_splitSet] at he
      have hvx : (K.vertexSplit s 2).vertexOf (Sum.inl x) = (K.vertexOf x).map Embedding.inl :=
        K.vertexOf_vertexSplit_inl s 2 he
      have hb : (K.vertexSplit s 2).IsBoundaryVertex ((K.vertexOf x).map Embedding.inl) ↔
          K.IsBoundaryVertex (K.vertexOf x) := K.isBoundaryVertex_map_inl_iff s 2 _
      rw [hvx, card_map]
      rw [hvx, hb] at hvB
      exact h3 _ (K.vertexOf_mem_internalVertices.2 hvB)
    · exact absurd (inr_mem_splitSet K s) he

/-- Splitting a vertex `z` with `k ≥ 4` darts from `s` with size `2` lowers the excess. -/
private theorem excess_vertexSplit_two_lt (K : PlabicData H b) (s : H)
    (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) (hk : 4 ≤ (K.vertexOf s).card) :
    excess (K.vertexSplit s 2) < excess K := by
  set S := K.vertexSplit s 2
  set k := ({y | K.rot.SameCycle s y} : Finset H).card
  have hk' : 4 ≤ k := hk
  have hs1 := rot_ne_self_of_two_le K s (by omega)
  set wK : H → ℕ := fun x =>
    if K.IsBoundaryVertex (K.vertexOf x) then 0 else (K.vertexOf x).card - 3
  set wS : H ⊕ Fin 2 → ℕ := fun e =>
    if S.IsBoundaryVertex (S.vertexOf e) then 0 else (S.vertexOf e).card - 3
  have hw_le : ∀ x, wS (Sum.inl x) ≤ wK x := by
    intro x
    by_cases hx : K.rot.SameCycle s x
    · have hv : K.vertexOf x = K.vertexOf s := (K.vertexOf_eq_vertexOf_iff.2 hx).symm
      have : (S.vertexOf (Sum.inl x)).card ≤ k - 1 :=
        card_vertexOf_vertexSplit_two_le K s hk _ ((inl_mem_splitSet K s).2 hx)
      simp only [wS, wK, hv, if_neg hz]
      split_ifs
      · exact Nat.zero_le _
      · change _ ≤ k - 3
        omega
    · have hv : S.vertexOf (Sum.inl x) = (K.vertexOf x).map Embedding.inl :=
        K.vertexOf_vertexSplit_inl s 2 hx
      have hb : S.IsBoundaryVertex ((K.vertexOf x).map Embedding.inl) ↔
          K.IsBoundaryVertex (K.vertexOf x) := K.isBoundaryVertex_map_inl_iff s 2 _
      simp only [wS, wK, hv, hb, card_map]
      exact le_rfl
  have hw_s : wS (Sum.inl s) = 0 := by
    have hv : S.vertexOf (Sum.inl s) = _ := vertexOf_vertexSplit_two_of_mem K s hs1 (by simp)
    simp only [wS, hv, card_vertexSplit_two_triple K s hs1]
    split_ifs <;> rfl
  have hw_0 : wS (Sum.inr 0) = 0 := by
    have hv : S.vertexOf (Sum.inr 0) = _ := vertexOf_vertexSplit_two_inr_zero K s hs1
    simp only [wS, hv, card_vertexSplit_two_triple K s hs1]
    split_ifs <;> rfl
  have hw_1 : wS (Sum.inr 1) ≤ k - 4 := by
    have : (S.vertexOf (Sum.inr 1)).card ≤ k - 1 :=
      card_vertexOf_vertexSplit_two_le K s hk _ (by simp)
    simp only [wS]
    split_ifs <;> omega
  have hwK_s : wK s = k - 3 := by
    simp only [wK, if_neg hz]
    rfl
  have hSsum : excess S = ∑ x, wS (Sum.inl x) + (wS (Sum.inr 0) + wS (Sum.inr 1)) := by
    rw [excess, Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [hSsum, show excess K = ∑ x, wK x from rfl, ← add_sum_erase _ _ (mem_univ s),
    ← add_sum_erase _ _ (mem_univ s), hw_s, hw_0, hwK_s]
  have : ∑ x ∈ univ.erase s, wS (Sum.inl x) ≤ ∑ x ∈ univ.erase s, wK x :=
    sum_le_sum fun x _ => hw_le x
  omega

end Resolution

end PlabicData

/-! ### Trivalent resolutions -/

namespace PlabicGraph

variable {b : ℕ}

/-- A step of a resolution: every internal vertex of `Y` has at least three darts, and `X` is
isomorphic to the contraction of `Y` along an edge. -/
def ResolutionStep (X Y : PlabicGraph b) : Prop :=
  (∀ v ∈ Y.data.internalVertices, 3 ≤ v.card) ∧ ∃ d, Y.IsEdgeContraction X d

/-- A **trivalent resolution** of a plabic graph `X` whose internal vertices all have at least
three darts: a trivalent plabic graph `T` such that there is a sequence `X = X₀, X₁, …, X_m` of
plabic graphs, all of whose internal vertices have at least three darts, with `T` isomorphic to
`X_m` and each `X_{j-1}` isomorphic to the contraction of `X_j` along an edge. -/
@[cluster_algebras "def_resolution"]
def IsResolution (X T : PlabicGraph b) : Prop :=
  (∀ v ∈ X.data.internalVertices, 3 ≤ v.card) ∧ T.IsTrivalent ∧
    ∃ Y, Relation.ReflTransGen ResolutionStep X Y ∧ T.Isomorphic Y

/-- A plabic graph whose internal vertices all have at least three darts has a trivalent
resolution. -/
@[cluster_algebras "lem_resolution_exists"]
theorem exists_isResolution (X : PlabicGraph b)
    (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card) : ∃ T, X.IsResolution T := by
  suffices h : ∀ n, ∀ X : PlabicGraph b, PlabicData.excess X.data = n →
      (∀ v ∈ X.data.internalVertices, 3 ≤ v.card) →
        ∃ Y, Relation.ReflTransGen ResolutionStep X Y ∧ Y.IsTrivalent by
    obtain ⟨Y, hXY, hY⟩ := h _ X rfl hX
    exact ⟨Y, hX, hY, Y, hXY, ⟨PlabicData.Iso.refl _⟩⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hX
  by_cases htri : X.IsTrivalent
  · exact ⟨X, Relation.ReflTransGen.refl, htri⟩
  · have : ∃ v ∈ X.data.internalVertices, v.card ≠ 3 := by
      by_contra hc
      push Not at hc
      exact htri hc
    obtain ⟨v, hv, hv3⟩ := this
    obtain ⟨hvV, hvB⟩ := (DiskMap.mem_internalVertices _).1 hv
    obtain ⟨s, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
    have hk : 4 ≤ (X.data.vertexOf s).card := by
      have := hX _ hv
      omega
    have hthick :=
      PlabicData.three_le_card_of_mem_internalVertices_vertexSplit_two X.data s hk hX
    have hlt := PlabicData.excess_vertexSplit_two_lt X.data s hvB hk
    let X₁ : PlabicGraph b :=
      { Dart := X.Dart ⊕ Fin 2
        data := X.data.vertexSplit s 2
        isPlabicGraph := X.isPlabicGraph.vertexSplit hvB 2 }
    obtain ⟨Y, hY, hYt⟩ := ih _ (hn ▸ hlt) X₁ rfl hthick
    refine ⟨Y, Relation.ReflTransGen.head ⟨hthick, Sum.inr 0, ?_⟩ hY, hYt⟩
    exact ⟨X.data.isContractibleEdge_vertexSplit s 2 hvB (by omega),
      X.data.isomorphic_contractEdge_vertexSplit s 2 X.isPlabicGraph.inv_involutive⟩

end PlabicGraph

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap

/-!
# Triple diagrams and swivel moves

D. Thurston's *triple diagrams* are encoded, like plabic graphs, as disk maps: a triple diagram
with `b` arcs is a disk map `(H, d ↦ d̄, σ, B)` whose boundary vertices, the *endpoints*, are
labelled `ε(1), …, ε(2b)` clockwise, whose internal vertices, the *triple points*, have six darts
each, together with an *orientation* `o` of the darts outside `B` that alternates around each
triple point and is reversed by `d ↦ d̄`. The endpoint `s_i = ε(2i - 1)` is a source and
`t_i = ε(2i)` a target.

Following a strand straight through a triple point means leaving it by the opposite dart, three
steps along the rotation. This gives the *strand map* `S(d) = σ³(d̄)` (or `S(d) = d̄` when `d̄`
lies at an endpoint), its *arcs* from the sources to the targets, its *closed strands*, and the
*strand permutation* `π_X` sending `i` to the `j` at whose target `t_j` the arc from `s_i` ends.

A *swivel move* at a digon `{d₁, d₂}` (an internal face of two darts at distinct triple points)
rewrites the rotations at the two triple points; two triple diagrams are *move-equivalent* when
they are joined by swivel moves and isomorphisms. A *pre-triple diagram* satisfies every condition
of a triple diagram except transitivity and Euler's relation.

Finally, for a disk map whose boundary vertices are labelled clockwise, the rotation at a boundary
vertex is determined by the labelling: it is the cycle `q̄ ↦ p ↦ g ↦ q̄`, where `p` is the dart of
the exterior at the vertex, `q` the dart of the exterior running to it and `g` its dart outside
`B`.

## Main definitions

* `ClusterAlgebras.TripleData`, `ClusterAlgebras.TripleData.IsTripleDiagram`: triple diagrams
  with the endpoints `TripleData.endpoint`, sources `TripleData.source`, targets
  `TripleData.target` and boundary vertices `TripleData.boundaryArc`;
  `ClusterAlgebras.TripleDiagram` bundles the dart type.
* `ClusterAlgebras.TripleData.strandMap`, `TripleData.arcLength`, `TripleData.arc`,
  `TripleData.IsClosedStrand`, `TripleData.IsStrand`, `TripleData.PassesThrough`,
  `TripleData.strandPerm`: strands and the strand permutation.
* `ClusterAlgebras.TripleDiagram.Iso`, `ClusterAlgebras.TripleDiagram.Isomorphic`: isomorphisms of
  triple diagrams.
* `ClusterAlgebras.TripleData.swivelMove`, `ClusterAlgebras.TripleDiagram.MoveEquivalent`: the
  swivel move and move equivalence.
* `ClusterAlgebras.TripleData.IsPreTripleDiagram`: pre-triple diagrams.
* `ClusterAlgebras.TripleData.Iso`, `ClusterAlgebras.TripleData.Isomorphic`: isomorphisms of
  pre-triple diagrams.
* `ClusterAlgebras.TripleData.IsDigon`: digons, the hollow digons of the underlying disk map
  (`TripleData.isDigon_iff_isHollowDigon`).

## Main results

* `ClusterAlgebras.DiskMap.rot_cycle_of_mem_boundaryVertices`: the rotation at a labelled
  boundary vertex.
* `ClusterAlgebras.TripleData.isTripleDiagram_iff`: a triple diagram is a pre-triple diagram that
  is a disk map.

## Implementation notes

* **Raw data and predicates.** As for plabic graphs, `TripleData H b` extends `DiskMap H` by the
  labelling and the orientation, and the conditions are the predicates `IsPreTripleDiagram` and
  `IsTripleDiagram`. Moves and isomorphisms are defined on the raw data.
* **Labels.** The label set `[1, 2b]` of the endpoints is `Fin (2 * b)`, `0`-indexed: `r` stands
  for the label `r + 1` of [FWZ], and `r + 1` modulo `2b` is `finRotate (2 * b) r`. As with the
  legs of a plabic graph, `ε` is recorded by one dart `endDart r` at each endpoint, with
  `ε(r) = endpoint r`, the vertex of `endDart r`; the conditions require `endDart r ∉ B`, so it is
  the dart `n_r` of [FWZ]. The arc label `i : Fin b` stands for `i + 1`; its source
  `s_{i+1} = ε(2i + 1)` and target `t_{i+1} = ε(2i + 2)` are the endpoints of `Fin (2 * b)`-index
  `2i` and `2i + 1` (`sourceIndex`, `targetIndex`).
* **Orientation.** The orientation is a function `isOut : H → Bool`, `true` for `out` and `false`
  for `in`; its values on `B` are irrelevant.
* **Strands.** The strand map is a function on all darts, given by the formula of [FWZ]. The arc
  from `s_i` is computed by searching the first `|H|` iterates of `S`, which is no restriction
  (`TripleData.arcLength_eq_zero_iff`, `TripleData.arcLength_eq_succ_iff`); closed strands are
  forward orbits of `S`, and a strand is recorded by its set of darts.
* **Swivel moves.** The swivel move at `{d₁, d₂}` is determined by `d₁`: `d₂ = φ(d₁)`,
  `a_k = σ^k(d₁)` and `b_k = σ^k(d₂)`. Its rotation is `σ ∘ τ` for the product `τ` of the two
  `3`-cycles `(d₁ a₂ b₄)` and `(a₄ d₂ b₂)`, written with transpositions, so that it is computable
  and defined for every `d₁`; at a digon it is the rotation of [FWZ]
  (`TripleData.swivelRot_apply_of_ne`, `TripleData.swivelRot_apply_six`). Move equivalence is the
  equivalence relation generated by isomorphism and by `X' ≅ swivel move of X` at a digon, which
  reads every step in either direction.
* **Isomorphisms.** One structure `TripleData.Iso` serves pre-triple diagrams, and an isomorphism
  of (bundled) triple diagrams is an isomorphism of their data.
* The rotation lemma `DiskMap.rot_cycle_of_mem_boundaryVertices` is proved for one boundary
  vertex `v` with a dart `p` of the exterior, a dart `q` of the exterior with `q̄ ∈ v` and a dart
  `g ∈ v` outside `B`; the labelling `ν` of [FWZ] only serves to name these darts, and the
  involution need not be fixed-point-free.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Iterates on a finite set -/

/-- On a finite type, every iterate `f^[n] a` is one of the first `|α|` iterates. -/
theorem exists_lt_card_iterate_eq {α : Type*} [Fintype α] (f : α → α) (a : α) (n : ℕ) :
    ∃ k < Fintype.card α, f^[n] a = f^[k] a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < Fintype.card α
    · exact ⟨n, hn, rfl⟩
    obtain ⟨i, j, hij, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun j : Fin (Fintype.card α + 1) => f^[j] a) (by simp)
    wlog hlt : i < j generalizing i j
    · exact this j i hij.symm h.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
    have hj : (j : ℕ) ≤ n := by omega
    have hij' : (i : ℕ) < j := hlt
    obtain ⟨k, hk, hk'⟩ := ih (n - (j - i)) (by omega)
    refine ⟨k, hk, ?_⟩
    rw [← hk', show n - (j - i) = (n - j) + i by omega, show n = (n - j) + j by omega,
      Function.iterate_add_apply, Nat.add_sub_cancel, Function.iterate_add_apply, h]

/-! ### The rotation at a labelled boundary vertex -/

namespace DiskMap

variable {H : Type*} [Fintype H] [DecidableEq H] {M : DiskMap H}

/-- **The rotation at a labelled boundary vertex.** Let `d ↦ d̄` be an involution, `B` closed under
it, every boundary vertex of three darts, two of them in `B`, and some orbit `f` of `φ` with
`f ⊆ B`, `f ∪ f̄ = B` and `f ∩ f̄ = ∅` (the third and fourth conditions of a disk map). Let `v` be
a boundary vertex, `p` a dart of the exterior `f_∞` at `v`, `q` a dart of `f_∞` running to `v` and
`g` a dart of `v` not in `B`. Then `v = {q̄, p, g}` and `σ` permutes it as the cycle
`q̄ ↦ p ↦ g ↦ q̄`. -/
@[cluster_algebras "lem_disk_map_boundary_rotation"]
theorem rot_cycle_of_mem_boundaryVertices (hinv : Function.Involutive M.inv)
    (hbdry : ∀ d ∈ M.bdry, M.inv d ∈ M.bdry)
    (hdeg : ∀ v ∈ M.boundaryVertices, v.card = 3 ∧ (v.filter (· ∈ M.bdry)).card = 2)
    (horb : ∃ f ∈ M.faceOrbits, f ⊆ M.bdry ∧ f ∪ f.map M.inv.toEmbedding = M.bdry ∧
      Disjoint f (f.map M.inv.toEmbedding))
    {v : Finset H} (hv : v ∈ M.boundaryVertices) {p q g : H} (hp : p ∈ M.exterior) (hpv : p ∈ v)
    (hq : q ∈ M.exterior) (hqv : M.inv q ∈ v) (hgv : g ∈ v) (hg : g ∉ M.bdry) :
    v = {M.inv q, p, g} ∧ M.rot (M.inv q) = p ∧ M.rot p = g ∧ M.rot g = M.inv q := by
  obtain ⟨f, hf, hfB, hu, hd⟩ := horb
  have hfe := M.eq_exterior_of_mem_faceOrbits hinv hbdry hdeg hf hfB hu hd
  subst hfe
  obtain ⟨hvV, hbv⟩ := M.mem_boundaryVertices.1 hv
  obtain rfl : v = M.vertexOf p := by
    obtain ⟨x, rfl⟩ := M.mem_vertices.1 hvV
    exact (M.vertexOf_eq_of_mem hpv).symm
  have hpB := M.exterior_subset_bdry hp
  have hqbB := hbdry _ (M.exterior_subset_bdry hq)
  have hqext : M.inv q ∉ M.exterior := fun h =>
    disjoint_left.1 hd h (mem_map_equiv.2 (by simpa using hq))
  have hpq : p ≠ M.inv q := fun h => hqext (h ▸ hp)
  have hφq : M.rot (M.inv q) ∈ M.exterior := by
    obtain ⟨d₀, hd₀⟩ := M.mem_faceOrbits.1 hf
    have h := M.facePerm_mem_faceOf q
    rw [← hd₀] at hq
    rwa [M.faceOf_eq_of_mem hq, hd₀] at h
  have hvq : M.vertexOf (M.inv q) = M.vertexOf p := M.vertexOf_eq_of_mem hqv
  have hrq : M.rot (M.inv q) = p := by
    by_contra hne
    have hmem : M.rot (M.inv q) ∈ M.vertexOf p := hvq ▸ M.rot_mem_vertexOf (M.inv q)
    exact not_three_mem_bdry hdeg hbv hmem hqv hpv (M.exterior_subset_bdry hφq) hqbB hpB
      (rot_ne_of_isBoundaryVertex hdeg (hvq ▸ hbv)) hne hpq.symm
  have hrp : M.rot p = g :=
    eq_of_notMem_bdry hdeg hbv (M.rot_mem_vertexOf p) hgv (M.mem_exterior.1 hp).2 hg
  have hgq : g ≠ M.inv q := fun h => hg (h ▸ hqbB)
  have hgp : g ≠ p := fun h => hg (h ▸ hpB)
  have hset : M.vertexOf p = {M.inv q, p, g} := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · rw [(hdeg _ hv).1, card_insert_of_notMem (by simp [hpq.symm, hgq.symm]),
        card_pair hgp.symm]
  have hvg : M.vertexOf g = M.vertexOf p := M.vertexOf_eq_of_mem hgv
  have hrg : M.rot g = M.inv q := by
    have hm : M.rot g ∈ M.vertexOf p := hvg ▸ M.rot_mem_vertexOf g
    rw [hset] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with h | h | h
    · exact h
    · rw [← hrq] at h
      exact absurd (M.rot.injective h) hgq
    · exact absurd h (rot_ne_of_isBoundaryVertex hdeg (hvg ▸ hbv))
  exact ⟨hset, hrq, hrp, hrg⟩

end DiskMap

/-! ### Triple diagrams -/

/-- The data `(H, d ↦ d̄, σ, B, ε, o)` of a **triple diagram** with `b` arcs: a disk map's data
together with a dart `endDart r` at each endpoint `ε(r) = v(endDart r)` (labels `0`-indexed:
`r : Fin (2 * b)` stands for the label `r + 1`) and an orientation `isOut` (`true` for `out`,
`false` for `in`). The conditions are `TripleData.IsTripleDiagram`. -/
@[cluster_algebras "def_triple_diagram"]
structure TripleData (H : Type*) (b : ℕ) extends DiskMap H where
  /-- A dart at the endpoint `ε(r)`; for a (pre-)triple diagram, the dart `n_r` not in `B`. -/
  endDart : Fin (2 * b) → H
  /-- The orientation: `isOut d` is `true` when `o(d) = out` and `false` when `o(d) = in`. -/
  isOut : H → Bool

/-- The index `2i` in `Fin (2 * b)` of the source `s_{i+1} = ε(2i + 1)` next to the arc label
`i : Fin b`, which stands for the label `i + 1`. -/
def sourceIndex {b : ℕ} (i : Fin b) : Fin (2 * b) := ⟨2 * i, by omega⟩

/-- The index `2i + 1` in `Fin (2 * b)` of the target `t_{i+1} = ε(2i + 2)` next to the arc label
`i : Fin b`, which stands for the label `i + 1`. -/
def targetIndex {b : ℕ} (i : Fin b) : Fin (2 * b) := ⟨2 * i + 1, by omega⟩

/-- The value of `sourceIndex i` is `2i`. -/
@[simp]
theorem sourceIndex_val {b : ℕ} (i : Fin b) : (sourceIndex i : ℕ) = 2 * i := rfl

/-- The value of `targetIndex i` is `2i + 1`. -/
@[simp]
theorem targetIndex_val {b : ℕ} (i : Fin b) : (targetIndex i : ℕ) = 2 * i + 1 := rfl

/-- `sourceIndex` is injective. -/
theorem sourceIndex_injective {b : ℕ} : Function.Injective (sourceIndex (b := b)) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [sourceIndex_val] at this
  exact Fin.ext (by omega)

/-- `targetIndex` is injective. -/
theorem targetIndex_injective {b : ℕ} : Function.Injective (targetIndex (b := b)) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [targetIndex_val] at this
  exact Fin.ext (by omega)

/-- No source index is a target index. -/
theorem sourceIndex_ne_targetIndex {b : ℕ} (i j : Fin b) : sourceIndex i ≠ targetIndex j := by
  intro h
  have := congrArg Fin.val h
  simp only [sourceIndex_val, targetIndex_val] at this
  omega

/-- Every endpoint label is a source index or a target index. -/
theorem exists_sourceIndex_or_targetIndex {b : ℕ} (r : Fin (2 * b)) :
    (∃ i, sourceIndex i = r) ∨ ∃ i, targetIndex i = r := by
  rcases Nat.even_or_odd' r with ⟨k, hk | hk⟩
  · exact Or.inl ⟨⟨k, by omega⟩, Fin.ext (by simp [hk])⟩
  · exact Or.inr ⟨⟨k, by omega⟩, Fin.ext (by simp [hk])⟩

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)

/-- The endpoint `ε(r)` of `0`-indexed label `r`: the vertex of `endDart r`. -/
def endpoint (r : Fin (2 * b)) : Finset H := X.vertexOf (X.endDart r)

/-- The source `s_{i+1} = ε(2i + 1)` next to the arc label `i`: the endpoint of index
`sourceIndex i`. -/
def source (i : Fin b) : Finset H := X.endpoint (sourceIndex i)

/-- The target `t_{i+1} = ε(2i + 2)` next to the arc label `i`: the endpoint of index
`targetIndex i`. -/
def target (i : Fin b) : Finset H := X.endpoint (targetIndex i)

/-- The **boundary vertex** `i` of a triple diagram: the boundary arc from `s_i` to `t_i`, the edge
`{p, p̄}` of the darts `p` of the exterior at `t_i` (they run to `s_i`). -/
@[cluster_algebras "def_triple_diagram"]
def boundaryArc (i : Fin b) : Finset H :=
  ({d ∈ X.exterior | d ∈ X.target i}).biUnion X.edgeOf

/-- A **pre-triple diagram** with `b` arcs: every condition of a triple diagram except
transitivity and Euler's relation. That is, `H` is nonempty, `d ↦ d̄` is a fixed-point-free
involution, `B` is closed under it, every boundary vertex (endpoint) consists of three darts, two
of them in `B`, some orbit `f` of `φ` satisfies `f ⊆ B`, `f ∪ f̄ = B` and `f ∩ f̄ = ∅`; every
internal vertex (triple point) has six darts; `ε` is a bijection from the labels onto the
endpoints, `endDart r` is the dart of `ε(r)` not in `B`, and for every `r` some dart of the
exterior at `ε(r + 1)` runs to `ε(r)`; the orientation is reversed by `d ↦ d̄` off `B`, alternates
around each triple point, and is `out` at each source and `in` at each target. -/
@[cluster_algebras "def_pre_triple_diagram"]
structure IsPreTripleDiagram : Prop where
  /-- There is at least one arc. -/
  one_le : 1 ≤ b
  /-- There is a dart. -/
  nonempty : Nonempty H
  /-- `d ↦ d̄` is an involution. -/
  inv_involutive : Function.Involutive X.inv
  /-- `d ↦ d̄` has no fixed point. -/
  inv_ne : ∀ d, X.inv d ≠ d
  /-- `B` is closed under `d ↦ d̄`. -/
  inv_mem_bdry : ∀ d ∈ X.bdry, X.inv d ∈ X.bdry
  /-- Every boundary vertex has three darts, two of them in `B`. -/
  boundaryVertex_card : ∀ v ∈ X.boundaryVertices,
    v.card = 3 ∧ (v.filter (· ∈ X.bdry)).card = 2
  /-- Some orbit of `φ` is half of the boundary. -/
  exists_orbit : ∃ f ∈ X.faceOrbits, f ⊆ X.bdry ∧
    f ∪ f.map X.inv.toEmbedding = X.bdry ∧ Disjoint f (f.map X.inv.toEmbedding)
  /-- Every triple point consists of six darts. -/
  internalVertex_card : ∀ v ∈ X.internalVertices, v.card = 6
  /-- The chosen dart at `ε(r)` is the one not in `B`. -/
  endDart_notMem_bdry : ∀ r, X.endDart r ∉ X.bdry
  /-- Each `ε(r)` is an endpoint. -/
  endpoint_mem : ∀ r, X.endpoint r ∈ X.boundaryVertices
  /-- `ε` is injective. -/
  endpoint_injective : Function.Injective X.endpoint
  /-- `ε` is onto the endpoints. -/
  exists_endpoint_eq : ∀ v ∈ X.boundaryVertices, ∃ r, X.endpoint r = v
  /-- Some dart of the exterior at `ε(r + 1)` runs to `ε(r)`. -/
  exists_exterior : ∀ r, ∃ d ∈ X.exterior,
    d ∈ X.endpoint (finRotate (2 * b) r) ∧ X.inv d ∈ X.endpoint r
  /-- `o(d̄) ≠ o(d)` for `d ∉ B`. -/
  isOut_inv : ∀ d, d ∉ X.bdry → X.isOut (X.inv d) ≠ X.isOut d
  /-- `o(σ d) ≠ o(d)` for `d` at a triple point. -/
  isOut_rot : ∀ d, ¬X.IsBoundaryVertex (X.vertexOf d) → X.isOut (X.rot d) ≠ X.isOut d
  /-- The dart of `s_i` not in `B` is `out`. -/
  isOut_source : ∀ i, X.isOut (X.endDart (sourceIndex i)) = true
  /-- The dart of `t_i` not in `B` is `in`. -/
  isOut_target : ∀ i, X.isOut (X.endDart (targetIndex i)) = false

/-- A **triple diagram** with `b ≥ 1` arcs: `(H, d ↦ d̄, σ, B)` is a disk map (its boundary
vertices are the *endpoints*, its internal vertices the *triple points*), every triple point
consists of six darts, `ε` is a bijection from `[1, 2b]` onto the endpoints such that some dart of
the exterior at `ε(r + 1)` runs to `ε(r)` (labels modulo `2b`), `endDart r` is the dart of `ε(r)`
not in `B`, and the orientation `o` satisfies `o(d̄) ≠ o(d)` for `d ∉ B`, `o(σ d) ≠ o(d)` at
triple points, `o = out` at each source `s_i = ε(2i - 1)` and `o = in` at each target
`t_i = ε(2i)`. The conditions other than the disk map's are those of `IsPreTripleDiagram`.
-/
@[cluster_algebras "def_triple_diagram"]
structure IsTripleDiagram : Prop extends X.toDiskMap.IsDiskMap, X.IsPreTripleDiagram

/-- A triple diagram is exactly a pre-triple diagram whose underlying data is a disk map. -/
theorem isTripleDiagram_iff :
    X.IsTripleDiagram ↔ X.toDiskMap.IsDiskMap ∧ X.IsPreTripleDiagram :=
  ⟨fun h => ⟨h.toIsDiskMap, h.toIsPreTripleDiagram⟩, fun ⟨h₁, h₂⟩ => { h₁, h₂ with }⟩

/-- A pre-triple diagram whose rotation system is transitive and satisfies Euler's relation is a
triple diagram. -/
theorem IsPreTripleDiagram.isTripleDiagram {X : TripleData H b} (hX : X.IsPreTripleDiagram)
    (htrans : ∀ d e : H,
      ∃ g ∈ Subgroup.closure ({X.inv, X.rot} : Set (Equiv.Perm H)), g d = e)
    (heuler : (X.vertices.card : ℤ) - X.edges.card + X.faceOrbits.card = 2) :
    X.IsTripleDiagram :=
  { hX with
    transitive := htrans
    euler := heuler }

/-! ### Strands -/

/-- The dart `d` **runs to an endpoint**: `v(d̄)` is a boundary vertex. -/
def RunsToEndpoint (d : H) : Prop := X.IsBoundaryVertex (X.vertexOf (X.inv d))

/-- Running to an endpoint is decidable. -/
instance : DecidablePred X.RunsToEndpoint := fun _ => by unfold RunsToEndpoint; infer_instance

/-- The **strand map** `S`: `S(d) = σ³(d̄)` if `v(d̄)` is a triple point and `S(d) = d̄` if
`v(d̄)` is an endpoint. It is meant for darts not in `B`. -/
@[cluster_algebras "def_strand"]
def strandMap (d : H) : H :=
  if X.RunsToEndpoint d then X.inv d else (X.rot ^ 3) (X.inv d)

/-- If `d` runs to an endpoint, then `S(d) = d̄`. -/
theorem strandMap_of_runsToEndpoint {d : H} (h : X.RunsToEndpoint d) :
    X.strandMap d = X.inv d := if_pos h

/-- If `d` does not run to an endpoint, then `S(d) = σ(σ(σ(d̄)))`. -/
theorem strandMap_of_not_runsToEndpoint {d : H} (h : ¬X.RunsToEndpoint d) :
    X.strandMap d = X.rot (X.rot (X.rot (X.inv d))) := by
  rw [strandMap, if_neg h, pow_succ, pow_succ, pow_one]
  rfl

/-- The `k`-th dart `S^k(a_i)` along the arc from the source `s_i`, where `a_i` is the dart of
`s_i` not in `B`. -/
def arcDart (i : Fin b) (k : ℕ) : H := X.strandMap^[k] (X.endDart (sourceIndex i))

/-- The `0`-th dart of the arc from `s_i` is the dart `a_i` of `s_i` not in `B`. -/
@[simp]
theorem arcDart_zero (i : Fin b) : X.arcDart i 0 = X.endDart (sourceIndex i) := rfl

/-- The `(k + 1)`-th dart of the arc from `s_i` is `S` of its `k`-th dart. -/
theorem arcDart_succ (i : Fin b) (k : ℕ) :
    X.arcDart i (k + 1) = X.strandMap (X.arcDart i k) :=
  Function.iterate_succ_apply' _ _ _

/-- The index `m - 1` of the last dart of the arc from `s_i`, if the arc reaches an endpoint: the
least `k` such that `S^k(a_i)` runs to an endpoint, searched among `k < |H|`
(`arcLastIndex_eq_some_iff`, `arcLastIndex_eq_none_iff`). -/
def arcLastIndex (i : Fin b) : Option ℕ :=
  (List.range (Fintype.card H)).find? fun k => decide (X.RunsToEndpoint (X.arcDart i k))

/-- The **length** `m` of the arc from `s_i`: the least `m ≥ 1` such that `S^{m-1}(a_i)` runs to
an endpoint, and `0` if there is none. -/
@[cluster_algebras "def_strand"]
def arcLength (i : Fin b) : ℕ := (X.arcLastIndex i).elim 0 (· + 1)

/-- The **arc** from `s_i`: the sequence `(a_i, S(a_i), …, S^{m-1}(a_i))`. -/
@[cluster_algebras "def_strand"]
def arc (i : Fin b) : List H := (List.range (X.arcLength i)).map (X.arcDart i)

/-- The first label `j` (if any) whose target `t_j` is the vertex `v`. -/
def findTarget (v : Finset H) : Option (Fin b) :=
  (List.finRange b).find? fun j => decide (X.target j = v)

/-- If `findTarget v = some j`, then `t_j = v`. -/
theorem target_eq_of_findTarget_eq_some {v : Finset H} {j : Fin b} (h : X.findTarget v = some j) :
    X.target j = v := by
  simpa using List.find?_some h

/-- If `v` is the target `t_j` of some label `j`, then `findTarget v` is defined. -/
theorem isSome_findTarget {v : Finset H} (h : ∃ j, X.target j = v) : (X.findTarget v).isSome := by
  obtain ⟨j, hj⟩ := h
  exact List.find?_isSome.2 ⟨j, List.mem_finRange j, by simpa using hj⟩

/-- The **strand permutation** `π_X`: it sends `i` to the `j` such that the last dart
`S^{m-1}(a_i)` of the arc from `s_i` runs to `t_j`, and sends `i` to `i` if `m = 0` (or if there
is no such `j`). -/
@[cluster_algebras "def_strand"]
def strandPerm (i : Fin b) : Fin b :=
  match X.arcLastIndex i with
  | none => i
  | some k => (X.findTarget (X.vertexOf (X.inv (X.arcDart i k)))).getD i

/-- The **forward orbit** `{S^k(d) : k ≥ 0}` of a dart under the strand map, computed from its
first `|H|` iterates (`mem_strandOrbit`). -/
def strandOrbit (d : H) : Finset H :=
  (range (Fintype.card H)).image fun k => X.strandMap^[k] d

/-- A **closed strand**: an orbit of `S` on the darts not in `B` containing no dart at an
endpoint. -/
@[cluster_algebras "def_strand"]
def IsClosedStrand (C : Finset H) : Prop :=
  ∃ d ∉ X.bdry, C = X.strandOrbit d ∧ ∀ e ∈ C, ¬X.IsBoundaryVertex (X.vertexOf e)

/-- A **strand**, recorded by its set of darts: the darts of an arc, or a closed strand. -/
@[cluster_algebras "def_strand"]
def IsStrand (s : Finset H) : Prop := (∃ i, s = (X.arc i).toFinset) ∨ X.IsClosedStrand s

/-- A strand with set of darts `s` **passes through** the triple point `v`: `v` is the vertex of
one of its darts and is a triple point. -/
@[cluster_algebras "def_strand"]
def PassesThrough (s : Finset H) (v : Finset H) : Prop :=
  v ∈ X.internalVertices ∧ ∃ d ∈ s, X.vertexOf d = v

/-- `arcLastIndex i = some m` exactly when `S^m(a_i)` is the first dart of the sequence
`S^k(a_i)` running to an endpoint. -/
theorem arcLastIndex_eq_some_iff {i : Fin b} {m : ℕ} :
    X.arcLastIndex i = some m ↔
      X.RunsToEndpoint (X.arcDart i m) ∧ ∀ k < m, ¬X.RunsToEndpoint (X.arcDart i k) := by
  rw [arcLastIndex, List.find?_range_eq_some]
  constructor
  · rintro ⟨h, -, hk⟩
    exact ⟨of_decide_eq_true h, fun k hk' => by simpa using hk k hk'⟩
  · rintro ⟨h, hk⟩
    refine ⟨decide_eq_true h, List.mem_range.2 ?_, fun k hk' => by simpa using hk k hk'⟩
    by_contra hm
    obtain ⟨k, hk', hkm⟩ := exists_lt_card_iterate_eq X.strandMap (X.endDart (sourceIndex i)) m
    exact hk k (by omega) (by rwa [arcDart, ← hkm])

/-- `arcLastIndex i = none` exactly when no dart `S^k(a_i)` runs to an endpoint. -/
theorem arcLastIndex_eq_none_iff {i : Fin b} :
    X.arcLastIndex i = none ↔ ∀ k, ¬X.RunsToEndpoint (X.arcDart i k) := by
  rw [arcLastIndex, List.find?_eq_none]
  constructor
  · intro h k hk
    obtain ⟨k', hk', hkk⟩ := exists_lt_card_iterate_eq X.strandMap (X.endDart (sourceIndex i)) k
    exact h k' (List.mem_range.2 hk') (decide_eq_true (by rwa [arcDart, ← hkk]))
  · intro h k _
    simpa using h k

/-- The arc from `s_i` has length `0` exactly when no dart `S^k(a_i)` runs to an endpoint. -/
theorem arcLength_eq_zero_iff {i : Fin b} :
    X.arcLength i = 0 ↔ ∀ k, ¬X.RunsToEndpoint (X.arcDart i k) := by
  rw [← arcLastIndex_eq_none_iff, arcLength]
  cases X.arcLastIndex i <;> simp

/-- The arc from `s_i` has length `m + 1` exactly when `S^m(a_i)` is the first dart of the
sequence `S^k(a_i)` running to an endpoint. -/
theorem arcLength_eq_succ_iff {i : Fin b} {m : ℕ} :
    X.arcLength i = m + 1 ↔
      X.RunsToEndpoint (X.arcDart i m) ∧ ∀ k < m, ¬X.RunsToEndpoint (X.arcDart i k) := by
  rw [← arcLastIndex_eq_some_iff, arcLength]
  cases X.arcLastIndex i <;> simp

/-- The arc from `s_i` has `arcLength i` darts. -/
theorem length_arc (i : Fin b) : (X.arc i).length = X.arcLength i := by simp [arc]

/-- The `k`-th entry of the arc from `s_i` is `S^k(a_i)`. -/
theorem getElem_arc (i : Fin b) (k : ℕ) (hk : k < (X.arc i).length) :
    (X.arc i)[k] = X.arcDart i k := by simp [arc]

/-- If the arc from `s_i` has length `0`, then `π_X(i) = i`. -/
theorem strandPerm_of_arcLength_eq_zero {i : Fin b} (h : X.arcLength i = 0) :
    X.strandPerm i = i := by
  rw [arcLength_eq_zero_iff, ← arcLastIndex_eq_none_iff] at h
  rw [strandPerm, h]

/-- If the arc from `s_i` has length `m + 1` and its last dart `S^m(a_i)` runs to a target, it runs
to the target `t_{π_X(i)}`. -/
theorem target_strandPerm {i : Fin b} {m : ℕ} (h : X.arcLength i = m + 1)
    (hj : ∃ j, X.target j = X.vertexOf (X.inv (X.arcDart i m))) :
    X.target (X.strandPerm i) = X.vertexOf (X.inv (X.arcDart i m)) := by
  rw [arcLength_eq_succ_iff, ← arcLastIndex_eq_some_iff] at h
  rw [strandPerm, h]
  dsimp only
  obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.1 (X.isSome_findTarget hj)
  rw [hj', Option.getD_some]
  exact X.target_eq_of_findTarget_eq_some hj'

/-- `e` lies in the forward orbit of `d` exactly when `e = S^k(d)` for some `k`. -/
theorem mem_strandOrbit {d e : H} : e ∈ X.strandOrbit d ↔ ∃ k, X.strandMap^[k] d = e := by
  simp only [strandOrbit, mem_image, mem_range]
  constructor
  · exact fun ⟨k, _, hk⟩ => ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨k', hk', hkk⟩ := exists_lt_card_iterate_eq X.strandMap d k
    exact ⟨k', hk', hkk.symm⟩

/-! ### Isomorphisms -/

/-- An **isomorphism** `X → X'` of pre-triple diagrams with the same number of arcs: a bijection
`θ : H ≃ H'` with `θ(d̄) = θ(d)̄` and `θ(σ d) = σ'(θ d)`, mapping `B` onto `B'`, with
`o'(θ d) = o(d)` for `d ∉ B`, and mapping `ε(r)` onto `ε'(r)` for every `r`. For triple diagrams
these are the isomorphisms of triple diagrams (`TripleDiagram.Iso`). -/
@[cluster_algebras "def_pre_triple_isomorphism"]
structure Iso {H' : Type*} [Fintype H'] [DecidableEq H'] (X' : TripleData H' b) where
  /-- The bijection of darts. -/
  toEquiv : H ≃ H'
  /-- `θ(d̄) = θ(d)̄`. -/
  map_inv : ∀ d, toEquiv (X.inv d) = X'.inv (toEquiv d)
  /-- `θ(σ d) = σ'(θ d)`. -/
  map_rot : ∀ d, toEquiv (X.rot d) = X'.rot (toEquiv d)
  /-- `θ(B) = B'`. -/
  mem_bdry_iff : ∀ d, toEquiv d ∈ X'.bdry ↔ d ∈ X.bdry
  /-- `o'(θ d) = o(d)` for `d ∉ B`. -/
  map_isOut : ∀ d, d ∉ X.bdry → X'.isOut (toEquiv d) = X.isOut d
  /-- `θ(ε(r)) = ε'(r)`. -/
  map_endpoint : ∀ r, (X.endpoint r).map toEquiv.toEmbedding = X'.endpoint r

/-- Two pre-triple diagrams are **isomorphic** if an isomorphism exists. -/
@[cluster_algebras "def_pre_triple_isomorphism"]
def Isomorphic {H' : Type*} [Fintype H'] [DecidableEq H'] (X' : TripleData H' b) : Prop :=
  Nonempty (X.Iso X')

namespace Iso

variable {X} {H' H'' : Type*} [Fintype H'] [DecidableEq H'] [Fintype H''] [DecidableEq H'']
  {X' : TripleData H' b} {X'' : TripleData H'' b}

/-- The inverse bijection intertwines the rotations. -/
theorem symm_map_rot (θ : X.Iso X') (d : H') :
    θ.toEquiv.symm (X'.rot d) = X.rot (θ.toEquiv.symm d) := by
  apply θ.toEquiv.injective
  simp [θ.map_rot]

/-- The inverse bijection intertwines the involutions. -/
theorem symm_map_inv (θ : X.Iso X') (d : H') :
    θ.toEquiv.symm (X'.inv d) = X.inv (θ.toEquiv.symm d) := by
  apply θ.toEquiv.injective
  simp [θ.map_inv]

/-- An isomorphism intertwines the face permutations. -/
theorem map_facePerm (θ : X.Iso X') (d : H) :
    θ.toEquiv (X.facePerm d) = X'.facePerm (θ.toEquiv d) := by
  simp [θ.map_rot, θ.map_inv]

/-- The identity isomorphism. -/
def refl (X : TripleData H b) : X.Iso X where
  toEquiv := Equiv.refl H
  map_inv _ := rfl
  map_rot _ := rfl
  mem_bdry_iff _ := Iff.rfl
  map_isOut _ _ := rfl
  map_endpoint _ := by simp

/-- The inverse of an isomorphism. -/
def symm (θ : X.Iso X') : X'.Iso X where
  toEquiv := θ.toEquiv.symm
  map_inv := θ.symm_map_inv
  map_rot := θ.symm_map_rot
  mem_bdry_iff d := by rw [← θ.mem_bdry_iff, Equiv.apply_symm_apply]
  map_isOut d hd := by
    have hd' : θ.toEquiv.symm d ∉ X.bdry := by rwa [← θ.mem_bdry_iff, Equiv.apply_symm_apply]
    simpa using (θ.map_isOut _ hd').symm
  map_endpoint r := by
    rw [← θ.map_endpoint r, map_map]
    ext y
    simp

/-- The composite of two isomorphisms. -/
def trans (θ : X.Iso X') (θ' : X'.Iso X'') : X.Iso X'' where
  toEquiv := θ.toEquiv.trans θ'.toEquiv
  map_inv d := by simp [θ.map_inv, θ'.map_inv]
  map_rot d := by simp [θ.map_rot, θ'.map_rot]
  mem_bdry_iff d := by simp [θ.mem_bdry_iff, θ'.mem_bdry_iff]
  map_isOut d hd := by
    simp only [Equiv.trans_apply]
    rw [θ'.map_isOut _ (by rwa [θ.mem_bdry_iff]), θ.map_isOut _ hd]
  map_endpoint r := by
    rw [← θ'.map_endpoint r, ← θ.map_endpoint r, map_map]
    rfl

end Iso

/-- Every pre-triple diagram is isomorphic to itself. -/
theorem Isomorphic.refl : X.Isomorphic X := ⟨Iso.refl X⟩

/-- Isomorphism of pre-triple diagrams is symmetric. -/
theorem Isomorphic.symm {H' : Type*} [Fintype H'] [DecidableEq H'] {X' : TripleData H' b}
    (h : X.Isomorphic X') : X'.Isomorphic X :=
  h.elim fun θ => ⟨θ.symm⟩

/-- Isomorphism of pre-triple diagrams is transitive. -/
theorem Isomorphic.trans {H' H'' : Type*} [Fintype H'] [DecidableEq H'] [Fintype H'']
    [DecidableEq H''] {X' : TripleData H' b} {X'' : TripleData H'' b}
    (h : X.Isomorphic X') (h' : X'.Isomorphic X'') : X.Isomorphic X'' :=
  h.elim fun θ => h'.elim fun θ' => ⟨θ.trans θ'⟩

/-! ### Digons and swivel moves -/

/-- A **digon**: an internal face consisting of exactly two darts `d₁` and `d₂ = φ(d₁)` whose
vertices `v(d₁)` and `v(d₂)` are distinct. -/
@[cluster_algebras "def_triple_digon"]
def IsDigon (f : Finset H) : Prop :=
  f ∈ X.internalFaces ∧
    ∃ d₁, f = {d₁, X.facePerm d₁} ∧ X.vertexOf d₁ ≠ X.vertexOf (X.facePerm d₁)

/-- Being a digon is decidable. -/
instance : DecidablePred X.IsDigon := fun _ => by unfold IsDigon; infer_instance

/-- A digon is the same as a hollow digon of the underlying disk map: an internal face of two
darts at distinct vertices. -/
theorem isDigon_iff_isHollowDigon {f : Finset H} : X.IsDigon f ↔ X.IsHollowDigon f := by
  constructor
  · rintro ⟨hf, d₁, rfl, hv⟩
    exact ⟨hf, d₁, X.facePerm d₁, rfl, hv⟩
  · rintro ⟨hf, d₁, d₂, rfl, hv⟩
    obtain ⟨d, hd⟩ := X.mem_faceOrbits.1 (X.mem_faces.1 (X.mem_internalFaces.1 hf).1).2
    have h₁ : X.faceOf d₁ = {d₁, d₂} := by
      rw [← hd]
      exact X.faceOf_eq_of_mem (hd ▸ mem_insert_self _ _)
    have hφ : X.facePerm d₁ = d₂ := by
      rcases mem_insert.1 (h₁ ▸ X.facePerm_mem_faceOf d₁) with h | h
      · have h₂ : d₂ ∈ X.faceOf d₁ := h₁ ▸ mem_insert_of_mem (mem_singleton_self _)
        exact absurd (congrArg X.vertexOf ((X.mem_faceOf.1 h₂).eq_of_left h)) hv
      · exact mem_singleton.1 h
    exact ⟨hf, d₁, by rw [hφ], by rwa [hφ]⟩

/-- The rotation of the **swivel move** at the digon `{d₁, d₂}`, `d₂ = φ(d₁)`: with the rotations
at `x = v(d₁)` and `y = v(d₂)` written `(d̄₂, d₁, a₁, a₂, a₃, a₄)` and `(d̄₁, d₂, b₁, b₂, b₃, b₄)`,
so that `a_k = σ^k(d₁)` and `b_k = σ^k(d₂)`, it is `σ ∘ τ` for the product `τ` of the `3`-cycles
`(d₁ a₂ b₄)` and `(a₄ d₂ b₂)`. At a digon its cycles at `x` and `y` are
`(d̄₂, d₁, a₃, a₄, b₁, b₂)` and `(d̄₁, d₂, b₃, b₄, a₁, a₂)` (`swivelRot_apply_six`), and it agrees
with `σ` elsewhere (`swivelRot_apply_of_ne`). -/
def swivelRot (d₁ : H) : Equiv.Perm H :=
  X.rot * (Equiv.swap d₁ ((X.rot ^ 4) (X.facePerm d₁)) * Equiv.swap d₁ ((X.rot ^ 2) d₁)) *
    (Equiv.swap ((X.rot ^ 4) d₁) ((X.rot ^ 2) (X.facePerm d₁)) *
      Equiv.swap ((X.rot ^ 4) d₁) (X.facePerm d₁))

/-- The **swivel move** of `X` at the digon `{d₁, φ(d₁)}`: the rotations at `x = v(d₁)` and
`y = v(d₂)`, `d₂ = φ(d₁)`, written `(d̄₂, d₁, a₁, a₂, a₃, a₄)` and `(d̄₁, d₂, b₁, b₂, b₃, b₄)`,
are replaced by `(d̄₂, d₁, a₃, a₄, b₁, b₂)` and `(d̄₁, d₂, b₃, b₄, a₁, a₂)`, and everything else is
kept. It is defined for every dart `d₁`, and is the swivel move when `{d₁, φ(d₁)}` is a digon
(`IsDigon`). -/
@[cluster_algebras "def_swivel_move"]
def swivelMove (d₁ : H) : TripleData H b :=
  { X with rot := X.swivelRot d₁ }

omit [Fintype H] in
/-- The rotation of the swivel move at `d₁` is `swivelRot d₁`. -/
@[simp]
theorem swivelMove_rot (d₁ : H) : (X.swivelMove d₁).rot = X.swivelRot d₁ := rfl

omit [Fintype H] in
/-- The swivel move keeps the involution `d ↦ d̄`. -/
@[simp]
theorem swivelMove_inv (d₁ : H) : (X.swivelMove d₁).inv = X.inv := rfl

omit [Fintype H] in
/-- The swivel move keeps `B`. -/
@[simp]
theorem swivelMove_bdry (d₁ : H) : (X.swivelMove d₁).bdry = X.bdry := rfl

omit [Fintype H] in
/-- The swivel move keeps the darts `endDart r` at the endpoints. -/
@[simp]
theorem swivelMove_endDart (d₁ : H) : (X.swivelMove d₁).endDart = X.endDart := rfl

omit [Fintype H] in
/-- The swivel move keeps the orientation. -/
@[simp]
theorem swivelMove_isOut (d₁ : H) : (X.swivelMove d₁).isOut = X.isOut := rfl

section SwivelRot

variable {X} {d₁ : H}

omit [Fintype H] in
/-- Away from `d₁, a₂, a₄, d₂, b₂, b₄` the swivel rotation is `σ`. -/
theorem swivelRot_apply_of_ne {z : H} (h₁ : z ≠ d₁) (h₂ : z ≠ (X.rot ^ 2) d₁)
    (h₃ : z ≠ (X.rot ^ 4) d₁) (h₄ : z ≠ X.facePerm d₁) (h₅ : z ≠ (X.rot ^ 2) (X.facePerm d₁))
    (h₆ : z ≠ (X.rot ^ 4) (X.facePerm d₁)) : X.swivelRot d₁ z = X.rot z := by
  simp only [swivelRot, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_of_ne_of_ne h₃ h₄, Equiv.swap_apply_of_ne_of_ne h₃ h₅,
    Equiv.swap_apply_of_ne_of_ne h₁ h₂, Equiv.swap_apply_of_ne_of_ne h₁ h₆]

omit [Fintype H] in
/-- At the six darts `d₁, a₂, a₄, d₂, b₂, b₄`, assumed distinct, the swivel rotation is `σ ∘ τ`
with `τ = (d₁ a₂ b₄)(a₄ d₂ b₂)`. When `{d₁, φ(d₁)}` is a digon of a pre-triple diagram, these
describe the new cycles `(d̄₂, d₁, a₃, a₄, b₁, b₂)` and `(d̄₁, d₂, b₃, b₄, a₁, a₂)`. -/
theorem swivelRot_apply_six
    (hnd : [d₁, (X.rot ^ 2) d₁, (X.rot ^ 4) d₁, X.facePerm d₁, (X.rot ^ 2) (X.facePerm d₁),
      (X.rot ^ 4) (X.facePerm d₁)].Nodup) :
    X.swivelRot d₁ d₁ = X.rot ((X.rot ^ 2) d₁) ∧
    X.swivelRot d₁ ((X.rot ^ 2) d₁) = X.rot ((X.rot ^ 4) (X.facePerm d₁)) ∧
    X.swivelRot d₁ ((X.rot ^ 4) (X.facePerm d₁)) = X.rot d₁ ∧
    X.swivelRot d₁ ((X.rot ^ 4) d₁) = X.rot (X.facePerm d₁) ∧
    X.swivelRot d₁ (X.facePerm d₁) = X.rot ((X.rot ^ 2) (X.facePerm d₁)) ∧
    X.swivelRot d₁ ((X.rot ^ 2) (X.facePerm d₁)) = X.rot ((X.rot ^ 4) d₁) := by
  simp only [swivelRot, Equiv.Perm.mul_apply]
  generalize (X.rot ^ 2) d₁ = a₂ at hnd ⊢
  generalize (X.rot ^ 4) d₁ = a₄ at hnd ⊢
  generalize (X.rot ^ 2) (X.facePerm d₁) = b₂ at hnd ⊢
  generalize (X.rot ^ 4) (X.facePerm d₁) = b₄ at hnd ⊢
  generalize X.facePerm d₁ = d₂ at hnd ⊢
  have hnd' := List.nodup_reverse.2 hnd
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hnd'
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd hnd'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Equiv.swap_apply_def, hnd, hnd']

end SwivelRot

end TripleData

/-! ### Bundled triple diagrams and move equivalence -/

/-- A **triple diagram** with `b` arcs, bundled with its dart type, so that triple diagrams on
different dart types can be collected in one type. -/
structure TripleDiagram (b : ℕ) where
  /-- The darts. -/
  Dart : Type
  [instFintype : Fintype Dart]
  [instDecidableEq : DecidableEq Dart]
  /-- The data of the triple diagram. -/
  data : TripleData Dart b
  /-- The conditions of a triple diagram hold. -/
  isTripleDiagram : data.IsTripleDiagram

attribute [instance] TripleDiagram.instFintype TripleDiagram.instDecidableEq

namespace TripleDiagram

variable {b : ℕ}

/-- An **isomorphism** of triple diagrams `X → X'`: a bijection of darts commuting with `d ↦ d̄`
and with `σ`, carrying `B` to `B'`, preserving the orientation and carrying `ε(r)` to `ε'(r)` for
every `r`. -/
@[cluster_algebras "def_triple_isomorphism"]
abbrev Iso (X X' : TripleDiagram b) : Type := X.data.Iso X'.data

/-- Two triple diagrams are **isomorphic** if an isomorphism exists. -/
@[cluster_algebras "def_triple_isomorphism"]
abbrev Isomorphic (X X' : TripleDiagram b) : Prop := X.data.Isomorphic X'.data

/-- `X'` is **a swivel move of** `X` (up to isomorphism): it is isomorphic to the swivel move of
`X` at some digon `{d₁, φ(d₁)}`. -/
def IsSwivelMove (X X' : TripleDiagram b) : Prop :=
  ∃ d₁, X.data.IsDigon (X.data.faceOf d₁) ∧ (X.data.swivelMove d₁).Isomorphic X'.data

/-- **Move equivalence** `X ∼ X'` of triple diagrams: the equivalence relation generated by
isomorphism and swivel moves, i.e. `X` and `X'` are related by a finite sequence of swivel moves
and isomorphisms, each step taken in either direction. -/
@[cluster_algebras "def_swivel_move"]
def MoveEquivalent (X X' : TripleDiagram b) : Prop :=
  Relation.EqvGen (fun Y Y' => Y.Isomorphic Y' ∨ Y.IsSwivelMove Y') X X'

/-- Every triple diagram is move-equivalent to itself. -/
@[refl]
theorem MoveEquivalent.refl (X : TripleDiagram b) : X.MoveEquivalent X := Relation.EqvGen.refl X

/-- Move equivalence is symmetric. -/
@[symm]
theorem MoveEquivalent.symm {X X' : TripleDiagram b} (h : X.MoveEquivalent X') :
    X'.MoveEquivalent X :=
  Relation.EqvGen.symm _ _ h

/-- Move equivalence is transitive. -/
@[trans]
theorem MoveEquivalent.trans {X X' X'' : TripleDiagram b} (h : X.MoveEquivalent X')
    (h' : X'.MoveEquivalent X'') : X.MoveEquivalent X'' :=
  Relation.EqvGen.trans _ _ _ h h'

/-- Isomorphic triple diagrams are move-equivalent. -/
theorem MoveEquivalent.of_isomorphic {X X' : TripleDiagram b} (h : X.Isomorphic X') :
    X.MoveEquivalent X' :=
  Relation.EqvGen.rel _ _ (Or.inl h)

/-- A triple diagram is move-equivalent to each of its swivel moves. -/
theorem MoveEquivalent.of_isSwivelMove {X X' : TripleDiagram b} (h : X.IsSwivelMove X') :
    X.MoveEquivalent X' :=
  Relation.EqvGen.rel _ _ (Or.inr h)

/-- Move equivalence is an equivalence relation. -/
theorem MoveEquivalent.equivalence : Equivalence (MoveEquivalent (b := b)) :=
  ⟨MoveEquivalent.refl, MoveEquivalent.symm, MoveEquivalent.trans⟩

end TripleDiagram

end ClusterAlgebras

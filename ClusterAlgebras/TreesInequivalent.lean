/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.External
public import ClusterAlgebras.TreeOrientation

/-!
# An acyclic quiver mutation equivalent to a tree orientation orients a tree

Assuming the Caldero–Keller theorem, an acyclic quiver with no frozen vertices which is
mutation equivalent to an orientation of a finite tree is itself an orientation of a finite
tree, isomorphic to the first. Hence orientations of non-isomorphic trees are never mutation
equivalent.

Mutation at a source or a sink is a reversal (`ClusterAlgebras.Quiver.mutate_arrows_of_isSource`),
and a reversal exchanges the two directions across a pair, so it preserves the total arrow
count `a u v + a v u` (`ClusterAlgebras.reversal_add_reversal`). That total is therefore
constant along a mutation path whose steps are all at a source or a sink, and being an
orientation of `G` is a condition on the total alone
(`ClusterAlgebras.Quiver.IsOrientation.of_arrows_add_arrows`): one across an edge of `G`, zero
off it.

## Main results

* `ClusterAlgebras.exists_isTreeOrientation_of_mutationEquivalent`: an acyclic quiver with no
  frozen vertices mutation equivalent to an orientation of a finite tree `T` orients a finite
  tree isomorphic to `T`.
* `ClusterAlgebras.nonempty_iso_of_mutationEquivalent`: mutation equivalent orientations of
  finite trees orient isomorphic trees.
* `ClusterAlgebras.not_mutationEquivalent_of_isEmpty_iso`: orientations of non-isomorphic
  finite trees are not mutation equivalent.
* `ClusterAlgebras.not_forall_isTreeOrientation`: the oriented tree is determined only up to
  isomorphism.

## Implementation notes

The conclusion is stated up to isomorphism of trees. An orientation of `T` itself cannot be
asserted, because mutation equivalence is insensitive to relabelling the vertices: an
isomorphism of quivers witnesses `Q.MutationEquivalent Q'`
(`ClusterAlgebras.Quiver.MutationEquivalent.of_iso`), and a relabelling moves the edges.
`ClusterAlgebras.not_forall_isTreeOrientation` gives a three-vertex counterexample.
-/

@[expose] public section

namespace ClusterAlgebras

universe u

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- **A reversal preserves the total arrow count across each pair.** On a pair meeting `k`
it exchanges the two directions and on any other pair it changes nothing, so the sum of
the two is untouched either way. -/
theorem reversal_add_reversal [DecidableEq V] (c : V → V → ℕ) (k i j : V) :
    reversal c k i j + reversal c k j i = c i j + c j i := by
  simp only [reversal]
  by_cases hij : i = k ∨ j = k
  · rw [if_pos hij, if_pos hij.symm]
    exact add_comm _ _
  · rw [if_neg hij, if_neg (mt Or.symm hij)]

namespace Quiver

/-- **A quiver orients at most one graph.** Off the diagonal, `u` and `v` are adjacent in
an oriented graph exactly when some arrow joins them, so the arrows determine the edges. -/
theorem IsOrientation.unique {Q : Quiver V} {G G' : FiniteSimpleGraph V}
    (h : Q.IsOrientation G) (h' : Q.IsOrientation G') : G = G' := by
  ext u v
  rcases eq_or_ne u v with rfl | hne
  · simp
  · constructor
    · intro hadj
      by_contra hna
      obtain ⟨z, z'⟩ := (h'.2 u v hne).2 hna
      have := (h.2 u v hne).1 hadj
      omega
    · intro hadj
      by_contra hna
      obtain ⟨z, z'⟩ := (h.2 u v hne).2 hna
      have := (h'.2 u v hne).1 hadj
      omega

/-- **Being an orientation of `G` is a condition on the total arrow counts alone.** A
quiver with no frozen vertices whose totals match those of an orientation of `G` is itself
one: across an edge the total is one, and off the edges it is zero, which forces both
directions to vanish. -/
theorem IsOrientation.of_arrows_add_arrows {Q R : Quiver V} {G : FiniteSimpleGraph V}
    (hQ : Q.IsOrientation G) (hf : R.frozen = ∅)
    (h : ∀ u v, R.arrows u v + R.arrows v u = Q.arrows u v + Q.arrows v u) :
    R.IsOrientation G := by
  refine ⟨hf, fun u v huv => ⟨fun hadj => ?_, fun hna => ?_⟩⟩
  · rw [h u v]
    exact (hQ.2 u v huv).1 hadj
  · obtain ⟨z, z'⟩ := (hQ.2 u v huv).2 hna
    have := h u v
    omega

/-- **An isomorphism of quivers carries an orientation along.** The image quiver orients
the image of the graph under the same bijection of vertices. -/
theorem IsOrientation.map {V' : Type*} [Fintype V'] {Q : Quiver V} {Q' : Quiver V'}
    {G : FiniteSimpleGraph V} (hQ : Q.IsOrientation G) (e : Q.Iso Q') :
    Q'.IsOrientation (G.map e.equiv.toEmbedding) := by
  refine ⟨Finset.eq_empty_iff_forall_notMem.2 fun x hx => ?_, fun u' v' huv => ?_⟩
  · have hmem := (e.mem_frozen_iff (e.equiv.symm x)).1 (by simpa using hx)
    rw [hQ.1] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · obtain ⟨u, rfl⟩ := e.equiv.surjective u'
    obtain ⟨v, rfl⟩ := e.equiv.surjective v'
    have hne : u ≠ v := fun hc => huv (by rw [hc])
    have hadj : (G.map e.equiv.toEmbedding).Adj (e.equiv u) (e.equiv v) ↔ G.Adj u v :=
      (SimpleGraph.Iso.map e.equiv G).map_adj_iff
    rw [e.arrows_eq, e.arrows_eq, hadj]
    exact hQ.2 u v hne

variable [DecidableEq V]

/-- **Along a mutation path at sources and sinks the total arrow count across each pair is
unchanged.** -/
theorem MutationPath.arrows_add_arrows_of_atSourceOrSink :
    ∀ {Q : Quiver V} (p : Q.MutationPath), p.AtSourceOrSink →
      ∀ u v, p.result.arrows u v + p.result.arrows v u = Q.arrows u v + Q.arrows v u
  | _, .nil _, _, _, _ => rfl
  | Q, .cons hk p, hp, u, v => by
      rw [result_cons, arrows_add_arrows_of_atSourceOrSink p hp.2 u v]
      rcases hp.1 with hs | hs
      · rw [Q.mutate_arrows_of_isSource hk hs]
        exact reversal_add_reversal _ _ _ _
      · rw [Q.mutate_arrows_of_isSink hk hs]
        exact reversal_add_reversal _ _ _ _

end Quiver

/-- **An acyclic quiver with no frozen vertices mutation equivalent to an orientation of a
finite tree is an orientation of a finite tree isomorphic to it**, given the Caldero–Keller
theorem as the hypothesis `hCK`. -/
theorem exists_isTreeOrientation_of_calderoKeller (hCK : CalderoKeller.{u}) {V V' : Type u}
    [Fintype V] [Fintype V'] [DecidableEq V] {T : FiniteSimpleGraph V} {Q : Quiver V}
    {Q' : Quiver V'} (hT : IsFiniteTree T) (hQ : Q.IsTreeOrientation T) (hQ' : Acyclic Q')
    (hfQ' : Q'.frozen = ∅) (h : Q.MutationEquivalent Q') :
    ∃ T' : FiniteSimpleGraph V',
      IsFiniteTree T' ∧ Q'.IsTreeOrientation T' ∧ Nonempty (T ≃g T') := by
  obtain ⟨p, hsos, ⟨e⟩⟩ := hCK (acyclic_of_isTreeOrientation hT hQ) hQ' hQ.1 hfQ' h
  have hres : p.result.IsOrientation T :=
    hQ.of_arrows_add_arrows (by rw [p.frozen_result, hQ.1])
      (p.arrows_add_arrows_of_atSourceOrSink hsos)
  refine ⟨T.map e.equiv.toEmbedding, ?_, hres.map e, ⟨SimpleGraph.Iso.map e.equiv T⟩⟩
  exact (SimpleGraph.Iso.map e.equiv T).isTree_iff.1 hT

/-- **An acyclic quiver with no frozen vertices mutation equivalent to an orientation of a
finite tree is an orientation of a finite tree isomorphic to it**, granted Caldero–Keller. -/
@[cluster_algebras "prop_trees_inequivalent"]
theorem exists_isTreeOrientation_of_mutationEquivalent {V V' : Type u} [Fintype V]
    [Fintype V'] [DecidableEq V] {T : FiniteSimpleGraph V} {Q : Quiver V} {Q' : Quiver V'}
    (hT : IsFiniteTree T) (hQ : Q.IsTreeOrientation T) (hQ' : Acyclic Q')
    (hfQ' : Q'.frozen = ∅) (h : Q.MutationEquivalent Q') :
    ∃ T' : FiniteSimpleGraph V',
      IsFiniteTree T' ∧ Q'.IsTreeOrientation T' ∧ Nonempty (T ≃g T') :=
  exists_isTreeOrientation_of_calderoKeller calderoKeller hT hQ hQ' hfQ' h

/-- **Mutation equivalent orientations of finite trees orient isomorphic trees.** -/
@[cluster_algebras "prop_trees_inequivalent"]
theorem nonempty_iso_of_mutationEquivalent {V V' : Type u} [Fintype V] [Fintype V']
    [DecidableEq V] {T : FiniteSimpleGraph V} {T' : FiniteSimpleGraph V'} {Q : Quiver V}
    {Q' : Quiver V'} (hT : IsFiniteTree T) (hT' : IsFiniteTree T')
    (hQ : Q.IsTreeOrientation T) (hQ' : Q'.IsTreeOrientation T')
    (h : Q.MutationEquivalent Q') : Nonempty (T ≃g T') := by
  obtain ⟨T'', -, hQ'T'', ⟨f⟩⟩ := exists_isTreeOrientation_of_mutationEquivalent hT hQ
    (acyclic_of_isTreeOrientation hT' hQ') hQ'.1 h
  obtain rfl := hQ'T''.unique hQ'
  exact ⟨f⟩

/-- **Orientations of non-isomorphic finite trees are not mutation equivalent.** -/
@[cluster_algebras "prop_trees_inequivalent"]
theorem not_mutationEquivalent_of_isEmpty_iso {V V' : Type u} [Fintype V] [Fintype V']
    [DecidableEq V] {T : FiniteSimpleGraph V} {T' : FiniteSimpleGraph V'} {Q : Quiver V}
    {Q' : Quiver V'} (hT : IsFiniteTree T) (hT' : IsFiniteTree T')
    (hQ : Q.IsTreeOrientation T) (hQ' : Q'.IsTreeOrientation T')
    (hiso : IsEmpty (T ≃g T')) : ¬Q.MutationEquivalent Q' := fun h =>
  (nonempty_iso_of_mutationEquivalent hT hT' hQ hQ' h).elim hiso.false

/-! ## The tree is determined only up to isomorphism

A three-vertex witness that the conclusion above cannot name `T` itself. The path
`0 - 1 - 2`, oriented as `0 → 1 → 2`, is relabelled by the transposition of `0` and `1`;
the relabelled quiver is mutation equivalent to the original by the empty path, is acyclic
because it orients a tree, and carries an arrow on the pair `{0, 2}`, which is not an edge
of the path. -/

/-- The path `0 - 1 - 2` on three vertices. -/
def pathThree : FiniteSimpleGraph (Fin 3) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val

/-- Adjacency in `pathThree` is decidable. -/
instance instDecidableRelPathThreeAdj : DecidableRel pathThree.Adj :=
  fun u v => by unfold pathThree; infer_instance

omit [Fintype V] in
/-- A vertex with no neighbours reaches nothing but itself. -/
theorem _root_.SimpleGraph.not_reachable_of_forall_not_adj {G : SimpleGraph V} {v w : V}
    (hv : ∀ x, ¬G.Adj v x) (h : v ≠ w) : ¬G.Reachable v w := by
  rintro ⟨p⟩
  cases p with
  | nil => exact h rfl
  | cons hadj _ => exact hv _ hadj

/-- The path is connected: every vertex is reachable from `0`. -/
theorem pathThree_connected : pathThree.Connected := by
  have h0 : ∀ v, pathThree.Reachable 0 v := by
    intro v
    fin_cases v
    · exact .refl _
    · exact (show pathThree.Adj 0 1 by decide).reachable
    · exact ((show pathThree.Adj 0 1 by decide).reachable).trans
        (show pathThree.Adj 1 2 by decide).reachable
  exact { preconnected := fun u v => (h0 u).symm.trans (h0 v) }

/-- The path is acyclic: each of its two edges is a bridge, since deleting it isolates an
endpoint. -/
theorem pathThree_isAcyclic : pathThree.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  rw [SimpleGraph.isBridge_iff]
  revert hvw
  fin_cases v <;> fin_cases w <;> intro hvw
  · exact absurd hvw (by decide)
  · exact SimpleGraph.not_reachable_of_forall_not_adj (by decide +revert) (by decide)
  · exact absurd hvw (by decide)
  · exact fun hr => SimpleGraph.not_reachable_of_forall_not_adj (v := (0 : Fin 3))
      (by decide +revert) (by decide) hr.symm
  · exact absurd hvw (by decide)
  · exact fun hr => SimpleGraph.not_reachable_of_forall_not_adj (v := (2 : Fin 3))
      (by decide +revert) (by decide) hr.symm
  · exact absurd hvw (by decide)
  · exact SimpleGraph.not_reachable_of_forall_not_adj (by decide +revert) (by decide)
  · exact absurd hvw (by decide)

/-- The path `0 - 1 - 2` is a finite tree. -/
theorem isFiniteTree_pathThree : IsFiniteTree pathThree :=
  ⟨pathThree_connected, pathThree_isAcyclic⟩

/-- The path `0 - 1 - 2` oriented as `0 → 1 → 2`. -/
def pathThreeQuiver : Quiver (Fin 3) where
  frozen := ∅
  arrows u v := if u = 0 ∧ v = 1 then 1 else if u = 1 ∧ v = 2 then 1 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; fin_cases i <;> fin_cases j <;> decide
  frozen_eq_zero := by decide

/-- The same quiver with `0` and `1` interchanged: arrows `1 → 0` and `0 → 2`. -/
def pathThreeQuiverSwap : Quiver (Fin 3) where
  frozen := ∅
  arrows u v := if u = 1 ∧ v = 0 then 1 else if u = 0 ∧ v = 2 then 1 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; fin_cases i <;> fin_cases j <;> decide
  frozen_eq_zero := by decide

/-- `pathThreeQuiver` orients the path: one arrow across each of its two edges, none
across the pair `{0, 2}`. -/
theorem pathThreeQuiver_isOrientation : pathThreeQuiver.IsOrientation pathThree := by
  refine ⟨rfl, ?_⟩
  decide

/-- Transposing `0` and `1` is an isomorphism from `pathThreeQuiver` to
`pathThreeQuiverSwap`. -/
def pathThreeQuiverIso : pathThreeQuiver.Iso pathThreeQuiverSwap where
  equiv := Equiv.swap 0 1
  mem_frozen_iff := by decide
  arrows_eq := by decide

/-- **The tree in `exists_isTreeOrientation_of_mutationEquivalent` cannot be `T` itself:** on
three vertices, a quiver mutation equivalent to an orientation of a tree `T` need not orient
`T`. -/
theorem not_forall_isTreeOrientation :
    ¬∀ (T : FiniteSimpleGraph (Fin 3)) (Q Q' : Quiver (Fin 3)), IsFiniteTree T →
        Q.IsTreeOrientation T → Acyclic Q' → Q'.frozen = ∅ → Q.MutationEquivalent Q' →
        Q'.IsTreeOrientation T := by
  intro hall
  have hmap : pathThreeQuiverSwap.IsOrientation
      (pathThree.map (Equiv.swap (0 : Fin 3) 1).toEmbedding) :=
    pathThreeQuiver_isOrientation.map pathThreeQuiverIso
  have hacyclic : Acyclic pathThreeQuiverSwap :=
    acyclic_of_isTreeOrientation
      ((SimpleGraph.Iso.map (Equiv.swap (0 : Fin 3) 1) pathThree).isTree_iff.1
        isFiniteTree_pathThree) hmap
  have hbad := hall pathThree pathThreeQuiver pathThreeQuiverSwap isFiniteTree_pathThree
    pathThreeQuiver_isOrientation hacyclic rfl
    (Quiver.MutationEquivalent.of_iso pathThreeQuiverIso)
  have h02 := (hbad.2 0 2 (by decide)).2 (by decide)
  exact absurd h02.1 (by decide)

end ClusterAlgebras

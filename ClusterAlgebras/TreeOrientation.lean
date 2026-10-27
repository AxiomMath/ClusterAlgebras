/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Acyclic

/-!
# Finite trees, and orienting one into a quiver

A finite tree is a `SimpleGraph.IsTree` on a finite vertex type, written `IsFiniteTree`, and an
orientation of a tree is an orientation of it as a finite simple graph, written
`Quiver.IsTreeOrientation`. Arrow counts that split each edge one way orient the graph, and
every orientation of a finite tree is acyclic.

## Main results

* `orientation_of_arrow_counts`: arrow counts that split each edge one way and vanish off the
  edges are the arrow counts of an orientation of the graph with no frozen vertices.
* `reachable_of_steps`: a run of consecutive adjacencies joins its endpoints by a walk.
* `acyclic_of_isTreeOrientation`: an orientation of a finite tree is acyclic.

## Implementation notes

`IsFiniteTree` and `Quiver.IsTreeOrientation` are reducible abbreviations for
`SimpleGraph.IsTree` and `Quiver.IsOrientation`. A tree is characterised by there being exactly
one path between any two vertices, which is `SimpleGraph.isTree_iff_existsUnique_path`. Mathlib's
`IsTree` also asks the vertex type to be nonempty, whereas the unique-path condition holds
vacuously on the empty graph.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*.
-/

@[expose] public section

namespace ClusterAlgebras

variable {V : Type*} [Fintype V]

attribute [cluster_algebras "def_finite_tree"] IsFiniteTree

attribute [cluster_algebras "def_tree_orientation"] Quiver.IsTreeOrientation

/-- Arrow counts that split each edge one way and vanish off the edges are the arrow counts of
an orientation of the graph with no frozen vertices. -/
@[cluster_algebras "lem_orientation_from_arrow_counts"]
theorem orientation_of_arrow_counts (T : FiniteSimpleGraph V) (a : V → V → ℕ)
    (hself : ∀ v, a v v = 0) (hadj : ∀ u v, T.Adj u v → a u v + a v u = 1)
    (hne : ∀ u v, u ≠ v → ¬T.Adj u v → a u v = 0) :
    ∃ Q : Quiver V, Q.arrows = a ∧ Q.frozen = ∅ ∧ Q.IsOrientation T := by
  have htcf : TwoCycleFree a := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · exact Or.inl (hself i)
    · by_cases h : T.Adj i j
      · have := hadj i j h
        omega
      · exact Or.inl (hne i j hij h)
  refine ⟨⟨∅, a, hself, htcf, by simp⟩, rfl, rfl, rfl, fun u v huv => ⟨?_, ?_⟩⟩
  · exact fun h => hadj u v h
  · exact fun h => ⟨hne u v huv h, hne v u huv.symm (fun hc => h hc.symm)⟩

omit [Fintype V] in
/-- A run of consecutive adjacencies along `v` makes `v a` and `v (a + k)` reachable. -/
theorem reachable_of_steps {H : SimpleGraph V} (v : ℕ → V) :
    ∀ (k a : ℕ), (∀ t, a ≤ t → t < a + k → H.Adj (v t) (v (t + 1))) →
      H.Reachable (v a) (v (a + k)) := by
  intro k
  induction k with
  | zero => intro a _; exact SimpleGraph.Reachable.refl (v a)
  | succ k ih =>
    intro a h
    have h1 : H.Adj (v a) (v (a + 1)) := h a le_rfl (by omega)
    have h2 := ih (a + 1) fun t ht ht' => h t (by omega) (by omega)
    have h3 := h1.reachable.trans h2
    rwa [show a + 1 + k = a + (k + 1) from by omega] at h3

/-- An orientation of a finite tree is acyclic. -/
@[cluster_algebras "lem_tree_orientation_acyclic"]
theorem acyclic_of_isTreeOrientation {T : FiniteSimpleGraph V} {Q : Quiver V}
    (hT : IsFiniteTree T) (hQ : Q.IsTreeOrientation T) : Acyclic Q := by
  intro r v hc
  have hadj : ∀ t, t < r → T.Adj (v t) (v (t + 1)) := by
    intro t ht
    by_contra hna
    exact absurd ((hQ.2 _ _ (hc.apply_ne_apply_succ ht)).2 hna).1 (hc.arrows_pos ht).ne'
  have hsum : ∀ t, t < r → Q.arrows (v t) (v (t + 1)) + Q.arrows (v (t + 1)) (v t) = 1 :=
    fun t ht => (hQ.2 _ _ (hc.apply_ne_apply_succ ht)).1 (hadj t ht)
  rcases eq_or_lt_of_le hc.two_le with h2 | h3
  · have hr : r = 2 := h2.symm
    subst hr
    have hlen : v 2 = v 0 := hc.apply_length
    have hf : 0 < Q.arrows (v 0) (v 1) := hc.arrows_pos (t := 0) (by omega)
    have hb : 0 < Q.arrows (v 1) (v 2) := hc.arrows_pos (t := 1) (by omega)
    rw [hlen] at hb
    have hs : Q.arrows (v 0) (v 1) + Q.arrows (v 1) (v 0) = 1 := hsum 0 (by omega)
    omega
  · have hbridge : T.IsBridge s(v 0, v 1) :=
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hT.isAcyclic) (hadj 0 (by omega))
    rw [SimpleGraph.isBridge_iff] at hbridge
    refine hbridge ?_
    have hstep : ∀ t, 1 ≤ t → t < 1 + (r - 1) →
        (T.deleteEdges {s(v 0, v 1)}).Adj (v t) (v (t + 1)) := by
      intro t ht ht'
      have htr : t < r := by omega
      refine ⟨hadj t htr, ?_⟩
      rw [SimpleGraph.fromEdgeSet_adj]
      rintro ⟨hmem, -⟩
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
      rcases hmem with ⟨h0, -⟩ | ⟨h0, h1⟩
      · exact absurd (hc.2.2.1 (Set.mem_Iio.2 htr) (Set.mem_Iio.2 (by omega)) h0) (by omega)
      · have ht1 : t = 1 := hc.2.2.1 (Set.mem_Iio.2 htr) (Set.mem_Iio.2 (by omega)) h0
        rw [ht1] at h1
        have h20 : v 2 = v 0 := h1
        exact absurd (hc.2.2.1 (Set.mem_Iio.2 (show 2 < r from by omega))
          (Set.mem_Iio.2 (show 0 < r from by omega)) h20) (by omega)
    have hreach := reachable_of_steps (H := T.deleteEdges {s(v 0, v 1)}) v (r - 1) 1 hstep
    rw [show 1 + (r - 1) = r from by omega, hc.apply_length] at hreach
    exact hreach.symm

end ClusterAlgebras

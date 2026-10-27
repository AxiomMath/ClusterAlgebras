/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.NearlyLeaflessSequences

/-!
# Reducedness under recolouring, normalization and nearly leafless moves

Let `G` be a nearly leafless plabic graph. The recolouring `R_i` of the lollipop at a label `i`
keeps `G` nearly leafless and commutes with local moves between nearly leafless graphs; it does
not change the disk map, so it carries hollow digons to hollow digons. Since a nearly leafless
graph is not reduced exactly when it is nearly leafless equivalent to a graph with a hollow digon,
and `R_i` is an involution, `G` is reduced if and only if `R_i(G)` is. Consequently a plabic graph
is reduced exactly when any of its normalizations is.

Finally, if two nearly leafless plabic graphs `G ∼ G'` are move-equivalent and `G` is reduced, the
moves can be chosen through nearly leafless graphs: following a sequence of moves from `G` to `G'`,
each graph has a collapsing family whose collapse is nearly leafless and nearly leafless equivalent
to `G`; at `G'` the family is empty, as a nearly leafless graph has no collapsible tree.

## Main results

* `ClusterAlgebras.PlabicGraph.isReduced_iff_isReduced_recolourLollipop`: recolouring a lollipop
  keeps reducedness.
* `ClusterAlgebras.PlabicGraph.IsNormalization.isReduced_iff`: a normalization is reduced exactly
  when the graph is.
* `ClusterAlgebras.PlabicGraph.IsReduced.nearlyLeaflessEquivalent`: moves between reduced nearly
  leafless graphs avoid stray leaves.

## Implementation notes

* Labels are `0`-indexed: `i : Fin b` is FWZ's label `i + 1`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

namespace PlabicData

/-- Recolouring keeps a plabic graph nearly leafless: it changes neither the disk map nor the
labelling. -/
theorem IsNearlyLeafless.recolourLollipop {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}
    {G : PlabicData H b} (hG : G.IsNearlyLeafless) (i : Fin b) :
    (G.recolourLollipop i).IsNearlyLeafless :=
  hG

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-! ### Recolouring and reducedness -/

/-- Recolouring twice at the same label gives back the bundled plabic graph. -/
@[simp]
theorem recolourLollipop_recolourLollipop (G : PlabicGraph b) (i : Fin b) :
    (G.recolourLollipop i).recolourLollipop i = G := by
  obtain ⟨D, d, h⟩ := G
  simp only [recolourLollipop]
  congr 1
  exact PlabicData.recolourLollipop_recolourLollipop i

/-- Recolouring keeps hollow digons: they are a property of the disk map. -/
theorem isHollowDigon_recolourLollipop {G : PlabicGraph b} (i : Fin b) {f : Finset G.Dart} :
    (G.recolourLollipop i).data.IsHollowDigon f ↔ G.data.IsHollowDigon f :=
  Iff.rfl

/-- Recolouring carries a nearly leafless equivalence `G ≈ G'` to a nearly leafless equivalence
`R_i(G) ≈ R_i(G')`. -/
theorem NearlyLeaflessEquivalent.recolourLollipop {G G' : PlabicGraph b}
    (h : NearlyLeaflessEquivalent G G') (i : Fin b) :
    NearlyLeaflessEquivalent (G.recolourLollipop i) (G'.recolourLollipop i) := by
  obtain ⟨hG, h⟩ := h
  refine ⟨hG.recolourLollipop i, ?_⟩
  induction h with
  | refl => exact .refl
  | @tail B C hBC hst ih =>
    exact ih.tail ⟨hst.1.recolourLollipop i,
      hst.2.recolourLollipop (NearlyLeaflessEquivalent.isNearlyLeafless_right ⟨hG, hBC⟩) hst.1 i⟩

/-- If a nearly leafless plabic graph `G` is not reduced, neither is `R_i(G)`. -/
private theorem not_isReduced_recolourLollipop {G : PlabicGraph b}
    (hG : G.data.IsNearlyLeafless) (i : Fin b) (h : ¬G.IsReduced) :
    ¬(G.recolourLollipop i).IsReduced := by
  obtain ⟨X, hX, f, hf⟩ := (not_isReduced_iff hG).1 h
  exact (not_isReduced_iff (G := G.recolourLollipop i) (hG.recolourLollipop i)).2
    ⟨X.recolourLollipop i, hX.recolourLollipop i, f, hf⟩

/-- Recolouring a lollipop keeps reducedness: if `G` is a nearly leafless plabic graph and `i` a
label, then `G` is reduced if and only if `R_i(G)` is reduced. -/
@[cluster_algebras "lem_recolouring_reduced"]
theorem isReduced_iff_isReduced_recolourLollipop {G : PlabicGraph b}
    (hG : G.data.IsNearlyLeafless) (i : Fin b) :
    G.IsReduced ↔ (G.recolourLollipop i).IsReduced := by
  refine ⟨fun h => ?_, not_imp_not.1 (not_isReduced_recolourLollipop hG i)⟩
  have := not_imp_not.1
    (not_isReduced_recolourLollipop (G := G.recolourLollipop i) (hG.recolourLollipop i) i)
  rw [PlabicGraph.recolourLollipop_recolourLollipop] at this
  exact this h

/-! ### Normalizations -/

/-- A step of a normalization keeps and reflects reducedness. -/
theorem NormalizationStep.isReduced_iff {G G' : PlabicGraph b} (h : NormalizationStep G G') :
    G.IsReduced ↔ G'.IsReduced := by
  rcases h with h | ⟨hG, i, rfl⟩
  · have h' : MoveEquivalent Set.univ G G' := Relation.ReflTransGen.single h
    exact ⟨fun hr => hr.of_moveEquivalent h', fun hr => hr.of_moveEquivalent h'.symm⟩
  · exact isReduced_iff_isReduced_recolourLollipop hG i

/-- If `N` is a normalization of a plabic graph `G`, then `G` is reduced if and only if `N` is
reduced. -/
@[cluster_algebras "lem_normalization_reduced"]
theorem IsNormalization.isReduced_iff {G N : PlabicGraph b} (h : IsNormalization G N) :
    G.IsReduced ↔ N.IsReduced := by
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact Iff.rfl
  | tail _ hst ih => exact ih.trans hst.isReduced_iff

/-! ### Moves between reduced nearly leafless graphs -/

/-- Moves between reduced nearly leafless graphs avoid stray leaves: if `G` and `G'` are nearly
leafless plabic graphs, `G` is reduced and `G ∼ G'`, then `G` and `G'` are nearly leafless
equivalent. -/
@[cluster_algebras "lem_reduced_nearly_leafless_moves"]
theorem IsReduced.nearlyLeaflessEquivalent {G G' : PlabicGraph b} (hred : G.IsReduced)
    (hG : G.data.IsNearlyLeafless) (hG' : G'.data.IsNearlyLeafless)
    (h : MoveEquivalent Set.univ G G') : NearlyLeaflessEquivalent G G' := by
  have key : ∀ K, MoveEquivalent Set.univ G K →
      ∃ (𝒯 : Finset (K.data.RootedTree × Shade)) (h𝒯 : K.data.IsCollapsingFamily 𝒯),
        (K.data.collapse 𝒯).IsNearlyLeafless ∧ NearlyLeaflessEquivalent G (K.collapse h𝒯) := by
    intro K hK
    induction hK with
    | refl =>
      have hθ := collapse_empty_isomorphic G
      have hnl : (G.data.collapse ∅).IsNearlyLeafless :=
        hθ.symm.elim fun θ => θ.isNearlyLeafless G.isPlabicGraph
          (G.collapse (isCollapsingFamily_empty (G := G.data))).isPlabicGraph hG
      exact ⟨∅, isCollapsingFamily_empty, hnl,
        ⟨hG, Relation.ReflTransGen.single ⟨hnl, Or.inl hθ⟩⟩⟩
    | @tail A B _ hAB ih =>
      obtain ⟨𝒯, h𝒯, hnl, hGA⟩ := ih
      rcases hasCollapseSteps A B 𝒯 h𝒯 hnl hAB with ⟨𝒯', h𝒯', hnl', hst⟩ | ⟨X, hX, hXd⟩
      · exact ⟨𝒯', h𝒯', hnl', hGA.trans ⟨hGA.isNearlyLeafless_right, .single ⟨hnl', hst⟩⟩⟩
      · exact absurd hred ((not_isReduced_iff hG).2 ⟨X, hGA.trans hX, hXd⟩)
  obtain ⟨𝒯, h𝒯, -, hseq⟩ := key G' h
  obtain rfl : 𝒯 = ∅ := by
    by_contra hne
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.2 hne
    exact hG'.not_isCollapsible G'.isPlabicGraph p.1 (h𝒯.isCollapsibleOfColour p hp).isCollapsible
  exact hseq.trans ⟨hseq.isNearlyLeafless_right,
    .single ⟨hG', Or.inl (collapse_empty_isomorphic G').symm⟩⟩

end PlabicGraph

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.FaceLabels
public import ClusterAlgebras.Plabic.GrassmannNecklace

/-!
# Strong equivalence of reduced plabic graphs

FWZ's Section 7.13 calls two reduced plabic graphs with the same number of boundary vertices
*strongly equivalent* when they have the same face labels. The labels compared here are the
target face labels `𝓕_tgt(G)` (`PlabicData.targetLabels`).

## Main definitions

* `ClusterAlgebras.PlabicGraph.StronglyEquivalent`: `𝓕_tgt(G) = 𝓕_tgt(G')`.
* `ClusterAlgebras.DecoratedPerm.IsNecklaceWeaklySeparatedCollection`: the weakly separated
  collections between the Grassmann necklace of `π̃` and its positroid, the range of
  Oh–Postnikov–Speyer's bijection.

## Main results

* `ClusterAlgebras.PlabicGraph.StronglyEquivalent.equivalence`: strong equivalence is an
  equivalence relation.

## Implementation notes

FWZ define strong equivalence for reduced plabic graphs. Here reducedness of `G` and `G'` is not
part of the relation; statements using the relation assume it as a hypothesis.
-/

@[expose] public section

namespace ClusterAlgebras

namespace PlabicGraph

variable {b : ℕ}

/-- Two plabic graphs `G, G'` with `b` boundary vertices are **strongly equivalent** if they have
the same collection of target face labels, `𝓕_tgt(G) = 𝓕_tgt(G')`. -/
@[cluster_algebras "def_strongly_equivalent"]
def StronglyEquivalent (G G' : PlabicGraph b) : Prop :=
  G.data.targetLabels = G'.data.targetLabels

/-- Every plabic graph is strongly equivalent to itself. -/
@[refl]
theorem StronglyEquivalent.refl (G : PlabicGraph b) : StronglyEquivalent G G := rfl

/-- If `G` is strongly equivalent to `G'`, then `G'` is strongly equivalent to `G`. -/
@[symm]
theorem StronglyEquivalent.symm {G G' : PlabicGraph b} (h : StronglyEquivalent G G') :
    StronglyEquivalent G' G :=
  Eq.symm h

/-- If `G` is strongly equivalent to `G'` and `G'` to `G''`, then `G` is strongly equivalent
to `G''`. -/
@[trans]
theorem StronglyEquivalent.trans {G G' G'' : PlabicGraph b} (h : StronglyEquivalent G G')
    (h' : StronglyEquivalent G' G'') : StronglyEquivalent G G'' :=
  Eq.trans h h'

/-- Strong equivalence is an equivalence relation. -/
theorem StronglyEquivalent.equivalence : Equivalence (StronglyEquivalent (b := b)) :=
  ⟨StronglyEquivalent.refl, StronglyEquivalent.symm, StronglyEquivalent.trans⟩

end PlabicGraph

/-- The collections of Oh–Postnikov–Speyer's theorem: weakly separated collections
`𝒞 ⊆ ([b] choose a)` with `{I_1, …, I_b} ⊆ 𝒞 ⊆ 𝓜_𝓘`, for the Grassmann necklace `𝓘 = 𝓘(π̃)` of
the decorated permutation `π̃` and its positroid `𝓜_𝓘`. -/
def DecoratedPerm.IsNecklaceWeaklySeparatedCollection {b : ℕ} (π : DecoratedPerm b) (a : ℕ)
    (C : Finset (Finset (Fin b))) : Prop :=
  IsWeaklySeparatedCollection a C ∧ Finset.univ.image π.necklace ⊆ C ∧
    C ⊆ positroid a π.necklace

end ClusterAlgebras

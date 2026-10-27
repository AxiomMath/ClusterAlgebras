/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.Reduced
public import ClusterAlgebras.Plabic.TripSides

/-!
# Face labels of a plabic graph

Let `G` be a plabic graph with `b` boundary vertices and let `f` be a face of `G`. The face `f`
*lies to the left of the one-way trip from `i`* if either `π_G(i) ≠ i` and `h(f) = 1` for every
winding function `h` of that trip, or `π_G(i) = i` and the decoration `ε_G(i)` is white. The
*source label* of `f` is the set `I_src(f)` of labels `i` such that `f` lies to the left of the
one-way trip from `i`, its *target label* is `I_tgt(f) = π_G(I_src(f))`, and the *collection of
target face labels* of `G` is `𝓕_tgt(G) = {I_tgt(f) : f a face of G}`.

Since a one-way trip from `i` with `π_G(i) ≠ i` has exactly one winding function `h_i`
(`ClusterAlgebras.PlabicData.IsPlabicGraph.existsUnique_isTripWinding`), for such `i` the face `f`
lies to the left of the trip exactly when `h_i(f) = 1`.

## Main definitions

* `ClusterAlgebras.PlabicData.IsLeftOfTrip`: faces to the left of a one-way trip.
* `ClusterAlgebras.PlabicData.sourceLabel`: the source label `I_src(f)` of a face.
* `ClusterAlgebras.PlabicData.targetLabel`: the target label `I_tgt(f)` of a face.
* `ClusterAlgebras.PlabicData.targetLabels`: the collection `𝓕_tgt(G)` of target face labels.

## Main results

* `ClusterAlgebras.PlabicData.IsPlabicGraph.isLeftOfTrip_iff`: for `π_G(i) ≠ i`, a face lies to
  the left of the trip from `i` if and only if a (the) winding function of the trip takes the
  value `1` on it.

## Implementation notes

* **Labels.** As throughout the chapter, the label set `[1, b]` is `Fin b`, `0`-indexed: the
  element `i : Fin b` is FWZ's label `i + 1`.
* **Faces.** A face is a `Finset H` (an element of `G.faces`), and the labels are defined for
  every `f : Finset H`. A winding function is a function on the subtype `G.faceOrbits`, so the
  first clause of `IsLeftOfTrip` includes the membership `f ∈ G.faceOrbits`, which holds for
  every face.
* **The decoration** `ε_G(i)` of a fixed point `i` of `π_G` is `G.tripDecoration ⟨i, hi⟩`, which
  is defined for every `G`; FWZ's definitions do not need `π_G` to be a bijection.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-! ### Faces to the left of a trip -/

/-- The face `f` **lies to the left of the one-way trip from `i`** (the label `i : Fin b` is
FWZ's `i + 1`): either `π_G(i) ≠ i` and `h(f) = 1` for every winding function `h` of the
one-way trip from `i`, or `π_G(i) = i` and `ε_G(i)` is white. Otherwise `f` lies to the right of
it. -/
@[cluster_algebras "def_trip_side"]
def IsLeftOfTrip (i : Fin b) (f : Finset H) : Prop :=
  (G.tripPerm i ≠ i ∧ ∃ hf : f ∈ G.faceOrbits, ∀ h : G.faceOrbits → ℤ, G.IsTripWinding i h →
      h ⟨f, hf⟩ = 1) ∨
    ∃ hi : G.tripPerm i = i, G.tripDecoration ⟨i, hi⟩ = .white

variable {G}

/-- At a label `i` with `π_G(i) ≠ i`, the face `f` lies to the left of the trip from `i` exactly
when `h(f) = 1` for every winding function `h` of the trip. -/
theorem isLeftOfTrip_iff_of_ne {i : Fin b} (hi : G.tripPerm i ≠ i) {f : Finset H}
    (hf : f ∈ G.faceOrbits) :
    G.IsLeftOfTrip i f ↔ ∀ h : G.faceOrbits → ℤ, G.IsTripWinding i h → h ⟨f, hf⟩ = 1 := by
  refine ⟨fun hl => ?_, fun hl => .inl ⟨hi, hf, hl⟩⟩
  rcases hl with ⟨_, _, hl⟩ | ⟨hi', _⟩
  · exact hl
  · exact absurd hi' hi

/-- At a fixed point `i` of `π_G`, the face `f` lies to the left of the trip from `i` exactly when
`ε_G(i)` is white. -/
theorem isLeftOfTrip_iff_of_eq {i : Fin b} (hi : G.tripPerm i = i) (f : Finset H) :
    G.IsLeftOfTrip i f ↔ G.tripDecoration ⟨i, hi⟩ = .white := by
  refine ⟨fun hl => ?_, fun hl => .inr ⟨hi, hl⟩⟩
  rcases hl with ⟨hi', _⟩ | ⟨_, hl⟩
  · exact absurd hi hi'
  · exact hl

/-- At a fixed point `i` of `π_G`, the face `f` lies to the left of the trip from `i` exactly when
`i` is white for the decoration of `G`. -/
theorem isLeftOfTrip_iff_isWhiteDecorated {i : Fin b} (hi : G.tripPerm i = i) (f : Finset H) :
    G.IsLeftOfTrip i f ↔ G.IsWhiteDecorated i := by
  rw [isLeftOfTrip_iff_of_eq hi, tripDecoration_eq_white_iff]

/-- For a plabic graph and a label `i` with `π_G(i) ≠ i`, the face `f` lies to the left of the
trip from `i` exactly when a winding function `h` of the trip (which is unique) takes the value
`1` at `f`. -/
theorem IsPlabicGraph.isLeftOfTrip_iff (hG : G.IsPlabicGraph) {i : Fin b} (hi : G.tripPerm i ≠ i)
    {h : G.faceOrbits → ℤ} (hW : G.IsTripWinding i h) {f : Finset H} (hf : f ∈ G.faceOrbits) :
    G.IsLeftOfTrip i f ↔ h ⟨f, hf⟩ = 1 := by
  rw [isLeftOfTrip_iff_of_ne hi hf]
  refine ⟨fun hl => hl h hW, fun hl h' hW' => ?_⟩
  obtain ⟨_, _, huniq⟩ := hG.existsUnique_isTripWinding hi
  rwa [huniq h' hW', ← huniq h hW]

/-! ### Source and target labels -/

variable (G)

open scoped Classical in
/-- The **source label** `I_src(f)` of a face `f`: the set of labels `i` such that `f` lies to the
left of the one-way trip from `i`. Labels are indexed from `0`, so `i : Fin b` stands for the label
`i + 1` of the usual `1`-indexed convention. -/
@[cluster_algebras "def_face_labels"]
noncomputable def sourceLabel (f : Finset H) : Finset (Fin b) :=
  {i | G.IsLeftOfTrip i f}

/-- The **target label** `I_tgt(f) = {π_G(i) : i ∈ I_src(f)}` of a face `f`. Labels are indexed
from `0`, so `i : Fin b` stands for the label `i + 1` of the usual `1`-indexed convention. -/
@[cluster_algebras "def_target_label"]
noncomputable def targetLabel (f : Finset H) : Finset (Fin b) :=
  (G.sourceLabel f).image G.tripPerm

/-- The **collection of target face labels** `𝓕_tgt(G) = {I_tgt(f) : f a face of G}`. -/
@[cluster_algebras "def_target_label_collection"]
noncomputable def targetLabels : Finset (Finset (Fin b)) :=
  G.faces.image G.targetLabel

variable {G}

/-- A label `i` lies in `I_src(f)` if and only if `f` lies to the left of the trip from `i`. -/
@[simp]
theorem mem_sourceLabel {f : Finset H} {i : Fin b} : i ∈ G.sourceLabel f ↔ G.IsLeftOfTrip i f := by
  classical
  simp [sourceLabel]

/-- A label `j` lies in `I_tgt(f)` if and only if `j = π_G(i)` for some `i` such that `f` lies to
the left of the trip from `i`. -/
@[simp]
theorem mem_targetLabel {f : Finset H} {j : Fin b} :
    j ∈ G.targetLabel f ↔ ∃ i, G.IsLeftOfTrip i f ∧ G.tripPerm i = j := by
  simp [targetLabel]

/-- If `f` lies to the left of the trip from `i`, then `π_G(i) ∈ I_tgt(f)`. -/
theorem tripPerm_mem_targetLabel {f : Finset H} {i : Fin b} (hi : G.IsLeftOfTrip i f) :
    G.tripPerm i ∈ G.targetLabel f :=
  mem_targetLabel.2 ⟨i, hi, rfl⟩

/-- When `π_G` is injective, `π_G(i) ∈ I_tgt(f)` if and only if `i ∈ I_src(f)`. -/
theorem tripPerm_mem_targetLabel_iff (hπ : Function.Injective G.tripPerm) {f : Finset H}
    {i : Fin b} : G.tripPerm i ∈ G.targetLabel f ↔ G.IsLeftOfTrip i f := by
  rw [targetLabel, hπ.mem_finset_image, mem_sourceLabel]

/-- When `π_G` is injective, `|I_tgt(f)| = |I_src(f)|`. -/
theorem card_targetLabel (hπ : Function.Injective G.tripPerm) (f : Finset H) :
    #(G.targetLabel f) = #(G.sourceLabel f) :=
  card_image_of_injective _ hπ

/-- A set `I` lies in `𝓕_tgt(G)` if and only if `I = I_tgt(f)` for some face `f` of `G`. -/
@[simp]
theorem mem_targetLabels {I : Finset (Fin b)} :
    I ∈ G.targetLabels ↔ ∃ f ∈ G.faces, G.targetLabel f = I := by
  simp [targetLabels]

/-- The target label of a face of `G` lies in `𝓕_tgt(G)`. -/
theorem targetLabel_mem_targetLabels {f : Finset H} (hf : f ∈ G.faces) :
    G.targetLabel f ∈ G.targetLabels :=
  mem_targetLabels.2 ⟨f, hf, rfl⟩

end PlabicData

end ClusterAlgebras

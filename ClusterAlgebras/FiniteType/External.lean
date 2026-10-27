/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.External
public import ClusterAlgebras.PolygonTriangulation
public import ClusterAlgebras.QuiverOps
public import ClusterAlgebras.TreeOrientation

/-!
# Flips, tree orientations and mutations

Two exercises of Fomin–Williams–Zelevinsky, assumed as axioms: a flip of a triangulation of a
polygon is a mutation of its quiver, and any two orientations of a finite tree are joined by
mutations at sources and sinks.

## Main definitions

* `flipTriangulation`: The set of diagonals `(T \ {γ}) ∪ {γ'}` obtained from `T` by replacing
  `γ` with `γ'`.
* `IsFlipReplacement`: `γ'` replaces `γ` in a flip of the triangulation `T`.

## Main results

* `polygonQuiver_mutate_iso_flip`: The quiver of a flipped triangulation is isomorphic to the
  mutation of the original quiver at the flipped diagonal.
* `Quiver.exists_mutationPath_of_isTreeOrientation`: Any two orientations of a finite tree are
  joined by a mutation path at sources and sinks.

## Implementation notes

Both results are exercises in FWZ and are stated as `axiom`s, so `#print axioms` on a
downstream result reports which of them it rests on.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### Flips are mutations -/

section Flip

variable {m : ℕ} [NeZero m]

/-- The result `(T \ {γ}) ∪ {γ'}` of the flip of `T` at `γ` with replacement `γ'`. -/
@[cluster_algebras "def_flip"]
def flipTriangulation (T : Finset (Sym2 (ZMod m))) (γ γ' : Sym2 (ZMod m)) :
    Finset (Sym2 (ZMod m)) :=
  insert γ' (T.erase γ)

/-- `γ'` is the **replacement** of `γ` in a flip of the triangulation `T`: `γ ∈ T`, `γ'` is a
diagonal not in `T`, and `(T \ {γ}) ∪ {γ'}` is a triangulation. The passage from `T` to
`flipTriangulation T γ γ'` is then the *flip of `T` at `γ`*. -/
@[cluster_algebras "def_flip"]
def IsFlipReplacement (T : Finset (Sym2 (ZMod m))) (γ γ' : Sym2 (ZMod m)) : Prop :=
  IsTriangulation T ∧ γ ∈ T ∧ IsDiagonal γ' ∧ γ' ∉ T ∧
    IsTriangulation (flipTriangulation T γ γ')

/-- **A flip is a mutation.** If `γ'` replaces `γ` in a flip of the triangulation `T`, the
bijection from the segments of `T` to those of `(T \ {γ}) ∪ {γ'}` sending `γ` to `γ'` and fixing
every other segment is an isomorphism from `μ_γ(Q(T))` to `Q((T \ {γ}) ∪ {γ'})`. The
mutability of the vertex `γ` of `Q(T)` is the hypothesis `hk`. -/
@[cluster_algebras "lem_flip_is_mutation"]
axiom polygonQuiver_mutate_iso_flip {T : Finset (Sym2 (ZMod m))} {γ γ' : Sym2 (ZMod m)}
    (h : IsFlipReplacement T γ γ')
    (hk : (⟨γ, mem_segments.2 (Or.inl h.2.1)⟩ : SegmentType T) ∉ (polygonQuiver T).frozen) :
    ∃ e : ((polygonQuiver T).mutate hk).Iso (polygonQuiver (flipTriangulation T γ γ')),
      ∀ σ : SegmentType T, (e.equiv σ).1 = if σ.1 = γ then γ' else σ.1

end Flip

/-! ### Orientations of a tree -/

universe u

/-- **Orientations of a tree are mutation equivalent.** Any two orientations `Q`, `Q'` of a
finite tree on the same vertex set are joined by a mutation path each of whose mutations is
performed at a source or a sink of the quiver it is applied to. -/
@[cluster_algebras "lem_tree_orientations_equivalent"]
axiom Quiver.exists_mutationPath_of_isTreeOrientation {V : Type u} [Fintype V] [DecidableEq V]
    {T : FiniteSimpleGraph V} (hT : IsFiniteTree T) {Q Q' : Quiver V}
    (hQ : Q.IsTreeOrientation T) (hQ' : Q'.IsTreeOrientation T) :
    ∃ p : Q.MutationPath, p.AtSourceOrSink ∧ p.result = Q'

end ClusterAlgebras

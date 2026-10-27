/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.PolygonTriangulation
public import ClusterAlgebras.TotalPositivity.Minor

/-!
# Plücker coordinates of segments, and the extended cluster of a triangulation

The vertices of the convex `m`-gon are `ZMod m`, as in `ClusterAlgebras.PolygonTriangulation`,
and the columns of a `2 × m` matrix are `Fin m`. A vertex `v` has exactly one representative
`v̄ ∈ Fin m`, its value `ZMod.val v` in `[0, m)`. The Plücker coordinate of a segment `{u, v}` is
`P_{{ū, v̄}}`.

## Implementation notes

* **`segmentPlucker` is defined on all of `Sym2 (ZMod m)`**, through `Sym2.lift`, since
  `P_{{ū, v̄}}` does not depend on the order of `u` and `v`. On a diagonal element `s(v, v)` it is
  `pluckerCoord z {v̄}`, the junk value of a minor of unequal sizes; only segments are used.

* **The extended cluster is indexed by `SegmentType T`**, the subtype of segments of `T` that the
  quiver of a triangulation is already indexed by.
-/

@[expose] public section

namespace ClusterAlgebras

variable {R : Type*} [CommRing R] {m : ℕ} [NeZero m]

/-- The representative `v̄ ∈ Fin m` of a vertex `v ∈ ZMod m`, namely its value `ZMod.val v`. -/
def vertexRep (v : ZMod m) : Fin m := ⟨v.val, v.val_lt⟩

/-- Taking representatives is injective: distinct vertices have distinct representatives. -/
theorem vertexRep_injective : Function.Injective (vertexRep (m := m)) := fun _ _ h =>
  ZMod.val_injective m (Fin.mk.inj_iff.1 h)

/-- The **Plücker coordinate of a segment** `σ = {u, v}` of the convex `m`-gon:
`P_σ(z) = P_{{ū, v̄}}(z)` for a `2 × m` matrix `z`. -/
@[cluster_algebras "def_segment_plucker"]
def segmentPlucker (z : Matrix (Fin 2) (Fin m) R) (σ : Sym2 (ZMod m)) : R :=
  Sym2.lift ⟨fun u v => pluckerCoord z {vertexRep u, vertexRep v}, fun _ _ =>
    congrArg (pluckerCoord z) (Finset.pair_comm _ _)⟩ σ

/-- The Plücker coordinate of the segment `{u, v}`, unfolded. -/
@[simp]
theorem segmentPlucker_mk (z : Matrix (Fin 2) (Fin m) R) (u v : ZMod m) :
    segmentPlucker z s(u, v) = pluckerCoord z {vertexRep u, vertexRep v} := rfl

/-- A ring homomorphism carries the Plücker coordinate of a segment of `z` to that of its
image. -/
theorem RingHom.map_segmentPlucker {S : Type*} [CommRing S] (f : R →+* S)
    (z : Matrix (Fin 2) (Fin m) R) (σ : Sym2 (ZMod m)) :
    f (segmentPlucker z σ) = segmentPlucker (z.map f) σ := by
  induction σ using Sym2.ind with
  | _ u v => exact RingHom.map_pluckerCoord f z _

/-- The **extended cluster** of a triangulation `T` of the convex `m`-gon: the Plücker coordinates
`P_σ(z)` of the generic `2 × m` matrix `z`, indexed by the segments `σ` of `T`. -/
@[cluster_algebras "def_grassmann_extended_cluster"]
noncomputable def grassmannExtendedCluster (T : Finset (Sym2 (ZMod m))) :
    SegmentType T → MvPolynomial (Fin 2 × Fin m) ℤ :=
  fun σ => segmentPlucker (genericMatrix (Fin 2) (Fin m)) σ.1

end ClusterAlgebras

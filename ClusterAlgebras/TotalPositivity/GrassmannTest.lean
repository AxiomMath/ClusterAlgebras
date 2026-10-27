/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.SubtractionFree
public import ClusterAlgebras.TotalPositivity.CrossingNumber
public import ClusterAlgebras.TotalPositivity.Ptolemy

/-!
# Total positivity tests for `2 × m` matrices from triangulations

Let `T` be a triangulation of the convex `m`-gon and `z` the generic `2 × m` matrix. The
extended cluster `x̃(T)` consists of the Plücker coordinates `P_σ(z)` of the segments `σ` of `T`.
Every Plücker coordinate `P_ζ(z)` of a segment `ζ` is subtraction-free in `x̃(T)`. The proof is by
strong induction on the crossing number `κ_T(ζ)`: a segment crossing nothing in `T` is a segment
of `T`, and if a diagonal `δ = {x, y} ∈ T` crosses `ζ = {p, q}`, the Ptolemy relation
`P_ζ P_δ = P_{px} P_{qy} + P_{py} P_{qx}` expresses `P_ζ` through four segments of smaller crossing
number, divided by the nonzero entry `P_δ` of `x̃(T)`.

Evaluating at a real matrix `x` turns this into a **total positivity test**: if `P_σ(x) > 0` for
the `2m - 3` segments `σ` of `T`, then all the Plücker coordinates `P_{ij}(x)`, `i < j`, are
positive, since a subtraction-free expression in positive reals is positive.

## Main results

* `ClusterAlgebras.isSubtractionFree_segmentPlucker`: the Plücker coordinate of every segment is
  subtraction-free in the extended cluster of a triangulation.
* `ClusterAlgebras.pluckerCoord_pos_of_isTriangulation`: a real `2 × m` matrix whose Plücker
  coordinates are positive on the segments of a triangulation has all its Plücker coordinates
  positive.
* `ClusterAlgebras.segmentPlucker_genericMatrix_ne_zero`: the Plücker coordinate of a segment of
  the generic matrix is nonzero.

## Implementation notes

* **FWZ's hypothesis `m ≥ 3` is dropped; only `m ≠ 0` is assumed**, a generalization. For
  `m = 1` there is no segment and no pair `i < j`; for `m = 2` the only segment `s(0, 1)` is a
  side, hence a segment of every `T`, and both statements hold trivially. The case `m ≥ 4`
  needed by the Ptolemy relation is recovered in the inductive step from the four distinct
  endpoints of two crossing segments.

* **The vertices of the polygon are `ZMod m` and the columns are `Fin m`.** The pair `i < j` of
  columns is the segment between the vertices `i, j` read in `ZMod m`, whose representatives are
  `i, j` again.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapter 1*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial

/-- The Plücker coordinate `P_{ab}(z) = z_{1a} z_{2b} - z_{1b} z_{2a}` of the generic `2 × κ`
matrix on two distinct columns `a ≠ b` is nonzero. -/
theorem pluckerCoord_genericMatrix_pair_ne_zero {κ : Type*} [LinearOrder κ] {a b : κ}
    (hab : a ≠ b) : pluckerCoord (genericMatrix (Fin 2) κ) {a, b} ≠ 0 := by
  wlog h : a < b generalizing a b
  · rw [Finset.pair_comm]
    exact this hab.symm (lt_of_le_of_ne (not_lt.1 h) hab.symm)
  rw [pluckerCoord_pair _ h]
  intro h0
  -- evaluate at the matrix with `1` in positions `(0, a)` and `(1, b)` and `0` elsewhere
  have := congrArg (eval fun p : Fin 2 × κ => if p = (0, a) ∨ p = (1, b) then (1 : ℤ) else 0) h0
  simp [Matrix.mvPolynomialX_apply, hab, hab.symm] at this

variable {m : ℕ} [NeZero m]

/-- The Plücker coordinate `P_σ(z)` of a segment `σ` of the generic `2 × m` matrix is nonzero. -/
theorem segmentPlucker_genericMatrix_ne_zero {σ : Sym2 (ZMod m)} (hσ : IsSegment σ) :
    segmentPlucker (genericMatrix (Fin 2) (Fin m)) σ ≠ 0 := by
  induction σ using Sym2.ind with
  | _ u v =>
    rw [segmentPlucker_mk]
    exact pluckerCoord_genericMatrix_pair_ne_zero
      (vertexRep_injective.ne fun h => hσ (Sym2.mk_isDiag_iff.2 h))

/-- **Plücker coordinates of segments are subtraction-free in the extended cluster.** For a
triangulation `T` of the convex `m`-gon and the generic `2 × m` matrix `z`, the Plücker coordinate
`P_ζ(z)` of every segment `ζ` is subtraction-free in the extended cluster `x̃(T)`.

FWZ assume `m ≥ 3`; the statement holds for every `m ≠ 0`, trivially for `m ≤ 2`. -/
@[cluster_algebras "thm_grassmann_subtraction_free"]
theorem isSubtractionFree_segmentPlucker {T : Finset (Sym2 (ZMod m))} (hT : IsTriangulation T)
    {ζ : Sym2 (ZMod m)} (hζ : IsSegment ζ) :
    IsSubtractionFree (grassmannExtendedCluster T)
      (segmentPlucker (genericMatrix (Fin 2) (Fin m)) ζ) := by
  induction hn : crossingNumber T ζ using Nat.strong_induction_on generalizing ζ with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · -- a segment crossing nothing in `T` is a segment of `T`
      have hmem : ζ ∈ segments T := by
        rw [mem_segments]
        by_cases hside : IsSide ζ
        · exact Or.inr hside
        by_contra hT'
        obtain ⟨δ, hδ, hcross⟩ := hT.maximal ζ ⟨hζ, hside⟩ fun h => hT' (Or.inl h)
        exact crossingNumber_eq_zero_iff.1 hn δ hδ hcross.symm
      exact IsSubtractionFree.self (grassmannExtendedCluster T) ⟨ζ, hmem⟩
    · obtain ⟨δ, hδT, hδ⟩ := crossingNumber_pos_iff.1 (hn ▸ hpos)
      obtain ⟨p, q, x, y, rfl, rfl, hx, hy⟩ := hδ.symm
      have hpq : p ≠ q := fun h => sbtw_irrefl_left_right (h ▸ hx)
      have hpx : p ≠ x := fun h => sbtw_irrefl_left (h ▸ hx)
      have hqx : q ≠ x := fun h => sbtw_irrefl_right (h ▸ hx)
      have hqy : q ≠ y := fun h => sbtw_irrefl_left (h ▸ hy)
      have hpy : p ≠ y := fun h => sbtw_irrefl_right (h ▸ hy)
      have hxy : x ≠ y := fun h => sbtw_asymm hx (h ▸ hy)
      -- the four endpoints are distinct, so `m ≥ 4`
      have hm : 4 ≤ m := by
        have h := Finset.card_le_univ ({p, q, x, y} : Finset (ZMod m))
        rwa [ZMod.card, Finset.card_insert_of_notMem (by simp [hpq, hpx, hpy]),
          Finset.card_insert_of_notMem (by simp [hqx, hqy]), Finset.card_pair hxy] at h
      have seg {a b : ZMod m} (hab : a ≠ b) : IsSegment s(a, b) := fun h =>
        hab (Sym2.mk_isDiag_iff.1 h)
      exact IsSubtractionFree.of_mul_eq_add
        (ih _ (hn ▸ crossingNumber_lt hT hpq hδT hx hy (Or.inl rfl) (Or.inl rfl)) (seg hpx) rfl)
        (ih _ (hn ▸ crossingNumber_lt hT hpq hδT hx hy (Or.inr rfl) (Or.inr rfl)) (seg hqy) rfl)
        (ih _ (hn ▸ crossingNumber_lt hT hpq hδT hx hy (Or.inl rfl) (Or.inr rfl)) (seg hpy) rfl)
        (ih _ (hn ▸ crossingNumber_lt hT hpq hδT hx hy (Or.inr rfl) (Or.inl rfl)) (seg hqx) rfl)
        (IsSubtractionFree.self (grassmannExtendedCluster T)
          ⟨s(x, y), mem_segments.2 (Or.inl hδT)⟩)
        (segmentPlucker_genericMatrix_ne_zero (seg hxy))
        (segmentPlucker_ptolemy hm _ hpq hx hy)

/-- The representative of the vertex `i ∈ ZMod m` of a column `i ∈ Fin m` is `i`. -/
theorem vertexRep_natCast_val (i : Fin m) : vertexRep ((i : ℕ) : ZMod m) = i :=
  Fin.ext (by simp [vertexRep, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt])

/-- **A total positivity test for `2 × m` matrices.** Let `T` be a triangulation of the convex
`m`-gon and `x` a real `2 × m` matrix with `P_σ(x) > 0` for every segment `σ` of `T`. Then
`P_{ij}(x) > 0` for all columns `i < j`.

FWZ assume `m ≥ 3`; the statement holds for every `m ≠ 0`, trivially for `m ≤ 2`. -/
@[cluster_algebras "thm_grassmann_tp_test"]
theorem pluckerCoord_pos_of_isTriangulation {T : Finset (Sym2 (ZMod m))} (hT : IsTriangulation T)
    (x : Matrix (Fin 2) (Fin m) ℝ) (hx : ∀ σ ∈ segments T, 0 < segmentPlucker x σ)
    {i j : Fin m} (hij : i < j) : 0 < pluckerCoord x {i, j} := by
  set φ : MvPolynomial (Fin 2 × Fin m) ℤ →+* ℝ :=
    eval₂Hom (Int.castRingHom ℝ) fun p => x p.1 p.2 with hφ
  have hφσ (σ : Sym2 (ZMod m)) :
      φ (segmentPlucker (genericMatrix (Fin 2) (Fin m)) σ) = segmentPlucker x σ := by
    rw [RingHom.map_segmentPlucker, hφ, genericMatrix_map_eval₂Hom]
  have hζ : IsSegment s(((i : ℕ) : ZMod m), ((j : ℕ) : ZMod m)) := fun h => by
    have := congrArg vertexRep (Sym2.mk_isDiag_iff.1 h)
    rw [vertexRep_natCast_val, vertexRep_natCast_val] at this
    exact hij.ne this
  have := (isSubtractionFree_segmentPlucker hT hζ).pos φ fun σ => (hφσ σ.1).symm ▸ hx σ.1 σ.2
  rwa [hφσ, segmentPlucker_mk, vertexRep_natCast_val, vertexRep_natCast_val] at this

end ClusterAlgebras

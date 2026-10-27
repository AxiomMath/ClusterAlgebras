/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.MatsumotoTits
public import ClusterAlgebras.TotalPositivity.ChamberCluster
public import ClusterAlgebras.TotalPositivity.SubtractionFree
public import ClusterAlgebras.TotalPositivity.Permutation
public import ClusterAlgebras.External

/-!
# The total positivity criterion for flag minors

Let `D` be a wiring diagram and `z` the generic square matrix. The chamber minors `P_{J(c)}(z)`,
over the chambers `c` of `D`, form the extended cluster `x̃(D)`. This file proves the criterion
for flag total positivity of Berenstein, Fomin and Zelevinsky [FWZ]: every flag minor `P_J(z)`,
`∅ ≠ J ⊊ [1, n]`, is subtraction-free in `x̃(D)`; consequently a complex matrix whose chamber
minors for the single diagram `D` are positive real numbers is flag totally positive.

The proof runs along a chain of commutations and braid moves from `D` to an arbitrary wiring
diagram `E` (the Matsumoto–Tits theorem), showing that every chamber minor of `E` is
subtraction-free in `x̃(D)`. A commutation creates no new chamber set, and a braid move creates
exactly one, which satisfies a three-term exchange relation with chamber minors of the previous
diagram; subtraction-free elements are stable under such relations. Every flag set is the chamber
set of a chamber of some wiring diagram, which concludes.

## Main results

* `ClusterAlgebras.WiringDiagram.isSubtractionFree_flagMinor`: every flag minor of the generic
  matrix is subtraction-free in the extended cluster of a wiring diagram.
* `ClusterAlgebras.WiringDiagram.isFlagTotallyPositive_of_chamber`: the flag total positivity
  test by the chamber minors of one wiring diagram.

## Implementation notes

* **Strands.** Wiring diagrams have `n + 2` strands, so the matrices are `(n + 2) × (n + 2)`;
  this encodes the hypothesis that there are at least two strands. The three-term relation for
  flag minors needs at least three strands; it is used only at a braid move, whose three distinct
  wires `α < β < γ` supply it.

* **The intermediate statement.** `isSubtractionFree_flagMinor_chamberSet` records the inductive
  claim of the proof: the chamber minors of every wiring diagram `E` on the same strands are
  subtraction-free in `x̃(D)`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapter 1*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

/-- Every flag minor of the generic square matrix is nonzero. -/
theorem flagMinor_genericMatrix_ne_zero {m : ℕ} (J : Finset (Fin m)) :
    flagMinor (genericMatrix (Fin m) (Fin m)) J ≠ 0 :=
  minor_genericMatrix_ne_zero (card_initialRows (by simpa using J.card_le_univ))

namespace WiringDiagram

variable {n : ℕ}

/-- **Chamber minors are subtraction-free in chamber minors.** For wiring diagrams `D` and `E` on
the same strands, every chamber minor `P_{J(c)}(z)` of `E` is subtraction-free in the extended
cluster `x̃(D)`. -/
theorem isSubtractionFree_flagMinor_chamberSet (D : WiringDiagram n) {E : WiringDiagram n}
    (c : E.Chamber) :
    IsSubtractionFree (wiringExtendedCluster D)
      (flagMinor (genericMatrix (Fin (n + 2)) (Fin (n + 2))) c.chamberSet) := by
  induction reflTransGen_isCommutation_or_isBraidMove D E with
  | refl => exact IsSubtractionFree.self _ c
  | @tail E₁ E₂ _ hmove ih =>
    rcases hmove with ⟨p, h⟩ | ⟨p, h⟩
    · obtain ⟨c₁, hc₁⟩ := h.exists_chamberSet_eq c
      exact hc₁ ▸ ih c₁
    · by_cases hc : c = E₂.braidSite h.length_le
      · obtain ⟨S, α, β, γ, hαβ, hβγ, hα, hβ, hγ, hYZ, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩,
          ⟨c₃, h₃⟩, ⟨c₄, h₄⟩⟩ := h.exists_exchange_sets
        have hn : 3 ≤ n + 2 := by
          have := γ.isLt
          have : (α : ℕ) < β := hαβ
          have : (β : ℕ) < γ := hβγ
          omega
        have key := flagMinor_three_term hn (genericMatrix (Fin (n + 2)) (Fin (n + 2))) S
          hα hβ hγ hαβ hβγ
        subst hc
        have hY := ih (E₁.braidSite h.1)
        rcases hYZ with ⟨hY', hZ'⟩ | ⟨hY', hZ'⟩
        · rw [hZ']
          rw [hY'] at hY
          refine (ih c₁).of_mul_eq_add (ih c₄) (ih c₂) (ih c₃) hY
            (flagMinor_genericMatrix_ne_zero _) ?_
          rw [h₁, h₂, h₃, h₄, mul_comm, key]
        · rw [hZ']
          rw [hY'] at hY
          refine (ih c₁).of_mul_eq_add (ih c₄) (ih c₂) (ih c₃) hY
            (flagMinor_genericMatrix_ne_zero _) ?_
          rw [h₁, h₂, h₃, h₄, key]
      · obtain ⟨c₁, hc₁⟩ := h.exists_chamberSet_eq c hc
        exact hc₁ ▸ ih c₁

/-- **Flag minors are subtraction-free in chamber minors.** For a wiring diagram `D` on `n + 2`
strands and the generic `(n + 2) × (n + 2)` matrix `z`, every flag minor `P_J(z)` with
`∅ ≠ J ⊊ [1, n + 2]` is subtraction-free in the extended cluster `x̃(D)`. -/
@[cluster_algebras "thm_flag_subtraction_free"]
theorem isSubtractionFree_flagMinor (D : WiringDiagram n) {J : Finset (Fin (n + 2))}
    (hJ : J.Nonempty) (hJ' : J ≠ Finset.univ) :
    IsSubtractionFree (wiringExtendedCluster D)
      (flagMinor (genericMatrix (Fin (n + 2)) (Fin (n + 2))) J) := by
  obtain ⟨E, c, rfl⟩ := exists_chamberSet_eq hJ hJ'
  exact isSubtractionFree_flagMinor_chamberSet D c

/-- **The flag total positivity test.** A complex `(n + 2) × (n + 2)` matrix whose chamber minors
`P_{J(c)}(x)`, over the chambers `c` of one wiring diagram, are positive real numbers is flag
totally positive. -/
@[cluster_algebras "thm_flag_tp_test"]
theorem isFlagTotallyPositive_of_chamber (D : WiringDiagram n)
    (x : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hx : ∀ c : D.Chamber, ∃ r : ℝ, 0 < r ∧ flagMinor x c.chamberSet = r) :
    IsFlagTotallyPositive x := by
  intro J hJ hJ'
  have hφ (K : Finset (Fin (n + 2))) :
      MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun p => x p.1 p.2)
        (flagMinor (genericMatrix (Fin (n + 2)) (Fin (n + 2))) K) = flagMinor x K := by
    rw [RingHom.map_flagMinor, genericMatrix_map_eval₂Hom]
  obtain ⟨r, hr, e⟩ := (isSubtractionFree_flagMinor D hJ hJ').exists_pos_real
    (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) fun p => x p.1 p.2)
    fun c => by simpa only [wiringExtendedCluster, hφ] using hx c
  exact ⟨r, hr, (hφ J).symm.trans e⟩

end WiringDiagram

end ClusterAlgebras

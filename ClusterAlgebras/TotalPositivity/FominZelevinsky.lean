/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.DoubleExchange
public import ClusterAlgebras.TotalPositivity.SubtractionFree

/-!
# The theorem of Fomin and Zelevinsky: total positivity tests for square matrices

Let `D` be a double wiring diagram on `n + 2` strands and `z` the generic `(n + 2) × (n + 2)`
matrix. The chamber minors `Δ_{I(c),J(c)}(z)`, one for each chamber `c` of `D`, form the extended
cluster `x̃(D)`. Fomin and Zelevinsky showed that every minor `Δ_{I,J}(z)` with `I`, `J` nonempty
of the same size is subtraction-free in `x̃(D)`: a ratio of two polynomials with nonnegative
integer coefficients in the chamber minors of `D`. Evaluating at a real matrix `x` then shows that
`x` is totally positive as soon as the `(n + 2) ^ 2` chamber minors of `D` are positive at `x`.

The proof follows the three-step sketch of [FWZ]. Any double wiring diagram `E` is reached from
`D` by a chain of swaps and braids, and by induction along the chain every chamber minor of `E` is
subtraction-free in `x̃(D)`. At a swap or a braid every chamber of the new diagram but one keeps
the label of a chamber of the old one; the remaining chamber `Z` satisfies an exchange relation
`Δ(Z) Δ(Y) = a₁ a₂ + b₁ b₂` with `Y` a chamber of the old diagram, the right-hand side built from
old chamber minors and `1`, and `Δ(Y) ≠ 0`, so `Δ(Z)` is subtraction-free. Finally every minor is
the chamber minor of some chamber of some double wiring diagram.

## Main results

* `ClusterAlgebras.DoubleWiringDiagram.isSubtractionFree_doubleExtendedCluster`: every chamber
  minor of every double wiring diagram `E` is subtraction-free in `x̃(D)`.
* `ClusterAlgebras.DoubleWiringDiagram.isSubtractionFree_minor`: the theorem of Fomin and
  Zelevinsky, every minor of the generic matrix is subtraction-free in `x̃(D)`.
* `ClusterAlgebras.DoubleWiringDiagram.isTotallyPositive_of_chamber`: the total positivity test,
  a real matrix whose chamber minors for `D` are positive is totally positive.

Along the way:

* `ClusterAlgebras.DoubleWiringDiagram.doubleExtendedCluster_ne_zero`: chamber minors of the
  generic matrix are nonzero.

## Implementation notes

* **Indices.** Strands are `Fin (n + 2)`, so FWZ's `n ≥ 2` is automatic. Positions in the
  word are `0`-based, and a chamber's span `(L, R)` is recorded so that the crossing at its left
  end is at position `L - 1` and that at its right end at position `R - 1`; a swap or braid at the
  `0`-based position `p` is FWZ's move at position `p + 1`, and its site chamber has span
  `(p + 1, p + 2)`, resp. `(p + 1, p + 3)`.
* **Swaps of two equal crossings.** A swap at `p` of two crossings of the same level and colour
  leaves the word, hence the diagram, unchanged; this is the case the exchange relation does not
  cover, and the proof disposes of it by identifying the two diagrams.
* **The chamber `Y`** of the old diagram at the site of the move is not given in advance; it is
  built from its gap and its count of crossings to the left,
  `ClusterAlgebras.DoubleWiringDiagram.exists_chamber_of_levelAt_eq`.
* **The induction is stated for an arbitrary family `y`**: the step lemmas show that if every
  chamber minor of `E` is subtraction-free in `y` then so is every chamber minor of `E'`, and the
  theorem takes `y = x̃(D)`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapter 1*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

namespace DoubleWiringDiagram

variable {n : ℕ}

/-- **Chamber minors of the generic matrix are nonzero**, the two halves of a chamber's label
having the same size. -/
theorem doubleExtendedCluster_ne_zero (D : DoubleWiringDiagram n) (c : D.Chamber) :
    doubleExtendedCluster D c ≠ 0 :=
  minor_genericMatrix_ne_zero (by rw [card_label, card_label])

/-- **The swap step.** If `E'` is obtained from `E` by a swap and every chamber minor of `E` is
subtraction-free in `y`, then so is every chamber minor of `E'`. -/
private theorem swap_step {S : Type*} {y : S → MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℤ}
    {E E' : DoubleWiringDiagram n} {p : ℕ} (h : E.IsSwap E' p)
    (ih : ∀ c : E.Chamber, IsSubtractionFree y (doubleExtendedCluster E c)) (c' : E'.Chamber) :
    IsSubtractionFree y (doubleExtendedCluster E' c') := by
  by_cases hc' : c'.left = p + 1 ∧ c'.right = p + 2
  swap
  · obtain ⟨c, hc⟩ := h.exists_label_eq c' hc'
    simpa only [doubleExtendedCluster, hc] using ih c
  obtain ⟨l, r, a, b, hl, hE, hE'⟩ := id h
  subst hl
  have hlen' : l.length + 1 < E'.word.length := by rw [hE']; simp
  have h1 := c'.levelAt_of_left_eq_succ hc'.1
  have h2 := c'.levelAt_of_right_eq_succ hc'.2 hlen'
  have eE : E.word.getD l.length (0, default) = a ∧
      E.word.getD (l.length + 1) (0, default) = b := by
    simp [hE, List.getD_eq_getElem?_getD]
  have eE' : E'.word.getD l.length (0, default) = b ∧
      E'.word.getD (l.length + 1) (0, default) = a := by
    simp [hE', List.getD_eq_getElem?_getD]
  simp only [levelAt, eE'] at h1 h2
  have hab1 : a.1 = b.1 := Fin.castSucc_injective _ (h2.trans h1.symm)
  by_cases hab2 : a.2 = b.2
  · have hab : a = b := Prod.ext hab1 hab2
    subst hab
    obtain ⟨w, _, _⟩ := E
    obtain ⟨w', _, _⟩ := E'
    obtain rfl : w = w' := hE.trans hE'.symm
    exact ih c'
  have hlev : E.levelAt l.length = E.levelAt (l.length + 1) := by
    simp only [levelAt, eE, hab1]
  have hcol : E.colourAt l.length ≠ E.colourAt (l.length + 1) := by
    simpa only [colourAt, eE] using hab2
  have hlen : l.length + 1 < E.word.length := by rw [hE]; simp
  obtain ⟨Y, hY⟩ := E.exists_chamber_of_levelAt_eq (Nat.lt_succ_self _) hlen rfl hlev.symm
    (fun u hu hu' => absurd hu' (by omega))
  have hZ : c'.gap = E.levelAt l.length ∧ c'.left = l.length + 1 ∧ c'.right = l.length + 2 :=
    ⟨by rw [← h1]; simp only [levelAt, eE, hab1], hc'⟩
  obtain ⟨a₁, a₂, b₁, b₂, hw, hex⟩ := h.exists_exchange hlev hcol Y hY c' hZ
  have hw' : ∀ w ∈ [a₁, a₂, b₁, b₂], IsSubtractionFree y w := by
    intro w hwm
    rcases hw w hwm with rfl | ⟨c, -, rfl⟩
    · exact IsSubtractionFree.one y
    · exact ih c
  refine IsSubtractionFree.of_mul_eq_add (hw' a₁ (by simp)) (hw' a₂ (by simp)) (hw' b₁ (by simp))
    (hw' b₂ (by simp)) (ih Y) (doubleExtendedCluster_ne_zero E Y) ?_
  rw [mul_comm, hex]

/-- **The braid step.** If `E'` is obtained from `E` by a braid and every chamber minor of `E` is
subtraction-free in `y`, then so is every chamber minor of `E'`. -/
private theorem braid_step {S : Type*} {y : S → MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℤ}
    {E E' : DoubleWiringDiagram n} {p : ℕ} (h : E.IsBraid E' p)
    (ih : ∀ c : E.Chamber, IsSubtractionFree y (doubleExtendedCluster E c)) (c' : E'.Chamber) :
    IsSubtractionFree y (doubleExtendedCluster E' c') := by
  by_cases hc' : c'.left = p + 1 ∧ c'.right = p + 3
  swap
  · obtain ⟨c, hc⟩ := h.exists_label_eq c' hc'
    simpa only [doubleExtendedCluster, hc] using ih c
  obtain ⟨l, r, e, g, k, hgk, hl, hE, -⟩ := id h
  subst hl
  have hlen : l.length + 2 < E.word.length := by rw [hE]; simp
  have eE : E.word.getD l.length (0, default) = (g, e) ∧
      E.word.getD (l.length + 1) (0, default) = (k, e) ∧
      E.word.getD (l.length + 2) (0, default) = (g, e) := by
    simp [hE, List.getD_eq_getElem?_getD]
  obtain ⟨Y, hY⟩ := E.exists_chamber_of_levelAt_eq (G := E.levelAt l.length)
    (by omega : l.length < l.length + 2) hlen rfl (by simp only [levelAt, eE])
    (fun u hu hu' => by
      obtain rfl : u = l.length + 1 := by omega
      simp only [levelAt, eE, ne_eq, Fin.castSucc_inj]
      intro hkg
      rw [hkg] at hgk
      omega)
  have hZ : c'.gap = E'.levelAt l.length ∧ c'.left = l.length + 1 ∧ c'.right = l.length + 3 :=
    ⟨(c'.levelAt_of_left_eq_succ hc'.1).symm, hc'⟩
  obtain ⟨c₁, c₂, c₃, c₄, -, hex⟩ := h.exists_exchange Y hY c' hZ
  refine IsSubtractionFree.of_mul_eq_add (ih c₁) (ih c₂) (ih c₃) (ih c₄) (ih Y)
    (doubleExtendedCluster_ne_zero E Y) ?_
  rw [mul_comm, hex]

/-- **Every chamber minor of every double wiring diagram is subtraction-free in `x̃(D)`.** This is
the induction along a chain of swaps and braids from `D` to `E` at the heart of the
Fomin–Zelevinsky theorem. -/
theorem isSubtractionFree_doubleExtendedCluster (D E : DoubleWiringDiagram n) (c : E.Chamber) :
    IsSubtractionFree (doubleExtendedCluster D) (doubleExtendedCluster E c) := by
  induction reflTransGen_isSwap_or_isBraid D E with
  | refl => exact IsSubtractionFree.self _ c
  | tail _ hstep ih =>
    rcases hstep with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact swap_step hp ih c
    · exact braid_step hp ih c

/-- **Fomin–Zelevinsky.** For a double wiring diagram `D` on `n + 2` strands and the generic
`(n + 2) × (n + 2)` matrix `z`, every minor `Δ_{I,J}(z)` with `I`, `J` nonempty of the same size is
subtraction-free in the extended cluster `x̃(D)`. -/
@[cluster_algebras "thm_fz_double_subtraction_free"]
theorem isSubtractionFree_minor (D : DoubleWiringDiagram n) {I J : Finset (Fin (n + 2))}
    (hI : I.Nonempty) (hIJ : I.card = J.card) :
    IsSubtractionFree (doubleExtendedCluster D)
      (minor (genericMatrix (Fin (n + 2)) (Fin (n + 2))) I J) := by
  obtain ⟨E, c, hcI, hcJ⟩ := exists_label_eq hI hIJ
  simpa only [doubleExtendedCluster, hcI, hcJ] using isSubtractionFree_doubleExtendedCluster D E c

/-- **The total positivity test for square matrices.** A real `(n + 2) × (n + 2)` matrix whose
chamber minors `Δ_{I(c),J(c)}(x)`, over the chambers `c` of one double wiring diagram, are all
positive is totally positive. -/
@[cluster_algebras "thm_double_tp_test"]
theorem isTotallyPositive_of_chamber (D : DoubleWiringDiagram n)
    (x : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (hx : ∀ c : D.Chamber, 0 < minor x (D.label c .thin) (D.label c .thick)) :
    IsTotallyPositive x := by
  set φ := MvPolynomial.eval₂Hom (Int.castRingHom ℝ) fun p : Fin (n + 2) × Fin (n + 2) =>
    x p.1 p.2
  have hφ (I J : Finset (Fin (n + 2))) :
      φ (minor (genericMatrix (Fin (n + 2)) (Fin (n + 2))) I J) = minor x I J := by
    rw [RingHom.map_minor, genericMatrix_map_eval₂Hom]
  intro I J hI hIJ
  rw [← hφ]
  exact (isSubtractionFree_minor D hI hIJ).pos φ fun c => by
    rw [doubleExtendedCluster, hφ]; exact hx c

end DoubleWiringDiagram

end ClusterAlgebras

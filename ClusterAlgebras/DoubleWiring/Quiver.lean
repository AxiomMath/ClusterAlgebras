/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.DoubleWiring.Label

/-!
# The quiver of a double wiring diagram

The quiver `Q(D)` of a double wiring diagram `D` has the chambers of `D` as vertices and the
unbounded chambers as frozen vertices. An arrow joins two chambers, at least one of them bounded,
when one of five conditions holds, each phrased in terms of the gaps of the two chambers, the
positions of their ends and the colours (thick or thin) of the crossings at those ends.

## Main definitions

* `DoubleWiringDiagram.Arrow`: the relation "there is an arrow `c → c'` in `Q(D)`".
* `DoubleWiringDiagram.wiringArrows`: the arrow multiplicities of `Q(D)`, each `0` or `1`.
* `DoubleWiringDiagram.wiringQuiver`: the quiver `Q(D)`.

## Main results

* `DoubleWiringDiagram.isArrowSystem_wiringArrows`: `Q(D)` has no loops.
* `DoubleWiringDiagram.wiringArrows_eq_zero_of_not_bounded`: `Q(D)` has no arrow between two
  unbounded chambers.
* `DoubleWiringDiagram.twoCycleFree_wiringArrows`: `Q(D)` has no two-cycles.

## Implementation notes

The colour conditions are what make `Q(D)` two-cycle-free. Conditions (ii)–(v) each impose one of
four patterns on the two spans — containment either way, or one of the two strict interleavings —
and exchanging `c` and `c'` exchanges (ii) with (iii) and (iv) with (v). The four patterns are
pairwise incompatible for distinct chambers, so both arrows of a two-cycle come from the same
pattern, and each of the four resulting pairs of conditions requires a single end to be both thick
and thin. Without the colour conditions all four pairs are satisfiable. When both arrows come from
(ii) the two spans coincide, which `Chamber.not_span_eq_of_gap_adjacent` excludes.
-/

@[expose] public section

namespace ClusterAlgebras

namespace DoubleWiringDiagram

variable {n : ℕ} (D : DoubleWiringDiagram n)

open Chamber

/-- `Arrow c c'` holds when `Q(D)` has an arrow `c → c'`: at least one of `c` and `c'` is
bounded, and either

* (i) `c` and `c'` lie in the same gap, and either `c'` begins where `c` ends, at a thick
  crossing, or `c'` ends where `c` begins, at a thin crossing; or

the gaps of `c` and `c'` are adjacent and one of the following holds:

* (ii) the span of `c` contains that of `c'`, and `c'` is bounded with thin left end and thick
  right end;
* (iii) the span of `c'` contains that of `c`, and `c` is bounded with thick left end and thin
  right end;
* (iv) `L(c) < L(c') < R(c) < R(c')`, and the ends `L(c')` and `R(c)` are thin;
* (v) `L(c') < L(c) < R(c') < R(c)`, and the ends `L(c)` and `R(c')` are thick.

Finiteness of an end is required explicitly only where it is not implied: in (iv) the inequality
`L(c) < L(c')` forces `L(c')` finite and `R(c) < R(c')` forces `R(c)` finite, and likewise in (v),
whereas in (i) the end whose colour is read is required to exist. -/
@[cluster_algebras "def_double_wiring_quiver"]
def Arrow (c c' : D.Chamber) : Prop :=
  (c.Bounded ∨ c'.Bounded) ∧
    ((c.gap = c'.gap ∧
        ((c.right = c'.left ∧ c.HasRightEnd ∧ c.rightEndColour = .thick) ∨
          (c.left = c'.right ∧ c.HasLeftEnd ∧ c.leftEndColour = .thin))) ∨
      (((c'.gap : ℕ) + 1 = (c.gap : ℕ) ∨ (c.gap : ℕ) + 1 = (c'.gap : ℕ)) ∧
        ((c.left ≤ c'.left ∧ c'.right ≤ c.right ∧ c'.Bounded ∧
            c'.leftEndColour = .thin ∧ c'.rightEndColour = .thick) ∨
          (c'.left ≤ c.left ∧ c.right ≤ c'.right ∧ c.Bounded ∧
            c.leftEndColour = .thick ∧ c.rightEndColour = .thin) ∨
          (c.left < c'.left ∧ c'.left < c.right ∧ c.right < c'.right ∧
            c'.leftEndColour = .thin ∧ c.rightEndColour = .thin) ∨
          (c'.left < c.left ∧ c.left < c'.right ∧ c'.right < c.right ∧
            c.leftEndColour = .thick ∧ c'.rightEndColour = .thick))))

/-- Whether there is an arrow is decidable. -/
instance instDecidableArrow (c c' : D.Chamber) : Decidable (D.Arrow c c') := by
  unfold Arrow; infer_instance

/-- The arrow multiplicities of `Q(D)`: at most one arrow per ordered pair. -/
@[cluster_algebras "def_double_wiring_quiver"]
def wiringArrows (c c' : D.Chamber) : ℕ := if D.Arrow c c' then 1 else 0

/-- **`Q(D)` has no loops.** -/
@[cluster_algebras "lem_double_wiring_quiver_is_quiver"]
theorem isArrowSystem_wiringArrows (c : D.Chamber) : D.wiringArrows c c = 0 := by
  rw [wiringArrows, if_neg]
  have hlr := c.left_lt_right
  rintro ⟨-, (⟨-, (⟨hr, -, -⟩ | ⟨hl, -, -⟩)⟩ | ⟨hg, -⟩)⟩
  · omega
  · omega
  · omega

/-- **`Q(D)` has no arrow between two unbounded chambers.** -/
@[cluster_algebras "lem_double_wiring_quiver_is_quiver"]
theorem wiringArrows_eq_zero_of_not_bounded {c c' : D.Chamber} (hc : ¬c.Bounded)
    (hc' : ¬c'.Bounded) : D.wiringArrows c c' = 0 := by
  rw [wiringArrows, if_neg]
  rintro ⟨(h | h), -⟩
  · exact hc h
  · exact hc' h

/-- **`Q(D)` is two-cycle-free.** -/
@[cluster_algebras "lem_double_wiring_quiver_is_quiver"]
theorem twoCycleFree_wiringArrows : TwoCycleFree (D.wiringArrows) := by
  intro c c'
  by_cases h : D.Arrow c c'
  · right
    rw [wiringArrows, if_neg]
    rintro ⟨-, hc'⟩
    obtain ⟨-, hc⟩ := h
    have hlr := c.left_lt_right
    have hlr' := c'.left_lt_right
    rcases hc with ⟨hg, hi⟩ | ⟨hadj, hrest⟩
    · rcases hc' with ⟨-, hi'⟩ | ⟨hadj', -⟩
      · rcases hi with ⟨hr, -, hcol⟩ | ⟨hl, -, hcol⟩ <;>
          rcases hi' with ⟨hr', -, hcol'⟩ | ⟨hl', -, hcol'⟩
        · omega
        · refine absurd (hcol.symm.trans (?_ : c.rightEndColour = c'.leftEndColour)
            |>.trans hcol') (by decide)
          rw [rightEndColour, leftEndColour, hl']
        · refine absurd (hcol.symm.trans (?_ : c.leftEndColour = c'.rightEndColour)
            |>.trans hcol') (by decide)
          rw [leftEndColour, rightEndColour, hl]
        · omega
      · rw [hg] at hadj'; omega
    · rcases hc' with ⟨hg', -⟩ | ⟨-, hrest'⟩
      · rw [hg'] at hadj; omega
      · rcases hrest with ⟨h1, h2, -, hcol, -⟩ | ⟨h1, h2, -, hcol, -⟩ |
            ⟨h1, h2, h3, -, hcol⟩ | ⟨h1, h2, h3, hcol, -⟩ <;>
          rcases hrest' with ⟨k1, k2, -, kcol, -⟩ | ⟨k1, k2, -, kcol, -⟩ |
            ⟨k1, k2, k3, kcol, -⟩ | ⟨k1, k2, k3, -, kcol⟩
        · exact not_span_eq_of_gap_adjacent hadj (by omega) (by omega)
        · exact absurd (hcol.symm.trans kcol) (by decide)
        · omega
        · omega
        · exact absurd (hcol.symm.trans kcol) (by decide)
        · exact not_span_eq_of_gap_adjacent hadj (by omega) (by omega)
        · omega
        · omega
        · omega
        · omega
        · omega
        · exact absurd (hcol.symm.trans kcol) (by decide)
        · omega
        · omega
        · exact absurd (hcol.symm.trans kcol) (by decide)
        · omega
  · left
    rw [wiringArrows, if_neg h]

/-- The **quiver of the double wiring diagram `D`**: its vertices are the chambers, its frozen
vertices the unbounded ones, and its arrows those of `Arrow`. -/
@[cluster_algebras "def_double_wiring_quiver"]
def wiringQuiver : Quiver D.Chamber where
  frozen := {c ∈ Finset.univ | ¬c.Bounded}
  arrows := D.wiringArrows
  isArrowSystem := D.isArrowSystem_wiringArrows
  twoCycleFree := D.twoCycleFree_wiringArrows
  frozen_eq_zero c hc c' hc' :=
    D.wiringArrows_eq_zero_of_not_bounded (by simpa using hc) (by simpa using hc')

/-- The arrows of `Q(D)` are the arrow counts, by definition. -/
@[simp]
theorem arrows_wiringQuiver : D.wiringQuiver.arrows = D.wiringArrows := rfl

/-- The frozen vertices of `Q(D)` are the unbounded chambers, by definition. -/
@[simp]
theorem mem_frozen_wiringQuiver (c : D.Chamber) :
    c ∈ D.wiringQuiver.frozen ↔ ¬c.Bounded := by
  rw [wiringQuiver]; simp

/-- **No ordered pair of chambers carries more than one arrow.** -/
@[cluster_algebras "lem_double_wiring_quiver_is_quiver"]
theorem wiringArrows_le_one (c c' : D.Chamber) : D.wiringArrows c c' ≤ 1 := by
  rw [wiringArrows]; split_ifs <;> omega

end DoubleWiringDiagram

end ClusterAlgebras

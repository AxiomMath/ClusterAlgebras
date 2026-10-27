/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.WiringDiagram.Basic

/-!
# Double wiring diagrams

A double wiring diagram on `n + 2` strands is a superposition of two ordinary wiring diagrams,
one thick and one thin. It is modelled combinatorially as a word in letters `(level, colour)`,
each colour's subword being a wiring diagram in the sense of `ClusterAlgebras.WiringDiagram`.

Gaps between strands are indexed by `Fin (n + 2)`: a crossing of level `g : Fin (n + 1)` cuts
the gap `g.castSucc`, so the top gap `Fin.last` is cut by no crossing and holds exactly one
chamber, the region above every curve.

## Main definitions

* `ClusterAlgebras.DoubleWiringDiagram.toWiringDiagram`: the wiring diagram formed by the
  crossings of one colour.
* `ClusterAlgebras.DoubleWiringDiagram.levelAt`: the gap cut by the crossing at a position.
* `ClusterAlgebras.DoubleWiringDiagram.colourAt`: the colour of the crossing at a position.

## Main results

* `ClusterAlgebras.DoubleWiringDiagram.multiplicity_last`: no crossing cuts the top gap.
* `ClusterAlgebras.DoubleWiringDiagram.sum_multiplicity`: the multiplicities of the gaps sum to
  the number of crossings.
* `ClusterAlgebras.DoubleWiringDiagram.length_word`: the word has length `(n + 2) * (n + 1)`.

## Implementation notes

A double wiring diagram is usually drawn as a picture, with chambers the connected components of
the complement of the curves. Read literally, that complement has more components than there are
chambers: for `n + 2 = 3` it has twenty-five components, of which only nine are chambers, the
others being slivers and lens regions between the thick and thin curves of a level. The word
model avoids this, and its chambers are defined combinatorially from the gaps.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

deriving instance Repr for Colour

namespace Colour

/-- The default colour is `thick`. -/
instance instInhabitedColour : Inhabited Colour := ⟨.thick⟩

/-- The other colour. -/
def swap : Colour → Colour
  | .thick => .thin
  | .thin => .thick

/-- Swapping the thick colour gives the thin one. -/
@[simp] theorem swap_thick : Colour.thick.swap = .thin := rfl

/-- Swapping the thin colour gives the thick one. -/
@[simp] theorem swap_thin : Colour.thin.swap = .thick := rfl

/-- Swapping a colour twice returns it. -/
@[simp] theorem swap_swap (e : Colour) : e.swap.swap = e := by cases e <;> rfl

/-- The two colours are distinct, so swapping never fixes one. -/
theorem swap_ne (e : Colour) : e.swap ≠ e := by cases e <;> simp

end Colour

variable {n : ℕ}

attribute [cluster_algebras "def_double_wiring_diagram"] DoubleWiringDiagram

namespace DoubleWiringDiagram

variable (D : DoubleWiringDiagram n)

/-- The wiring diagram formed by the crossings of colour `e`: its word is the subword of
colour `e`. -/
def toWiringDiagram (e : Colour) : WiringDiagram n where
  word := subword D.word e
  length_eq := D.length_subword e
  prod_eq := D.prod_subword e

/-- A colour's wiring diagram is its subword, by definition. -/
@[simp]
theorem word_toWiringDiagram (e : Colour) :
    (D.toWiringDiagram e).word = subword D.word e := rfl

/-! ### Reading the word -/

/-- The **level of the crossing at position `t`**, as a gap: a crossing of level `g` cuts the
gap `g.castSucc`, and no other. Past the end of the word this is `Fin.last`. -/
def levelAt (t : ℕ) : Fin (n + 2) := (D.word.getD t (0, default)).1.castSucc

/-- The **colour of the crossing at position `t`**, and `thick` past the end of the word. -/
def colourAt (t : ℕ) : Colour := (D.word.getD t (0, default)).2

/-- Recording levels as gaps loses no letters. -/
@[simp]
theorem length_levels : D.levels.length = D.word.length := by simp [levels]

/-- The gap list agrees with `levelAt` at every genuine position. -/
theorem levels_getElem {t : ℕ} (ht : t < D.word.length) :
    D.levels[t]'(by simpa using ht) = D.levelAt t := by
  simp only [levels, List.getElem_map, levelAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem ht, Option.getD_some]

/-- No crossing cuts the top gap: every level is a `Fin.castSucc`. -/
theorem levels_ne_last {g : Fin (n + 2)} (hg : g ∈ D.levels) : g ≠ Fin.last _ := by
  rw [levels, List.mem_map] at hg
  obtain ⟨x, -, rfl⟩ := hg
  exact Fin.castSucc_ne_last x.1

/-- The top gap `Fin.last` is cut by no crossing. -/
@[simp]
theorem multiplicity_last : D.multiplicity (Fin.last _) = 0 := by
  rw [multiplicity, List.count_eq_zero]
  exact fun hg => D.levels_ne_last hg rfl

/-- **The multiplicities of the gaps sum to the number of crossings**, since each crossing cuts
exactly one gap. -/
theorem sum_multiplicity : ∑ g : Fin (n + 2), D.multiplicity g = D.word.length := by
  classical
  simp only [multiplicity]
  rw [← D.length_levels, ← List.sum_toFinset_count_eq_length D.levels]
  exact (Finset.sum_subset (Finset.subset_univ _) fun g _ hg =>
    List.count_eq_zero.2 fun hm => hg (List.mem_toFinset.2 hm)).symm

/-- `2 * (m + 2).choose 2 = (m + 2) * (m + 1)`. -/
private theorem two_mul_choose_two (m : ℕ) : 2 * (m + 2).choose 2 = (m + 2) * (m + 1) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have h : (k + 1 + 2).choose 2 = (k + 2) + (k + 2).choose 2 := by
      rw [show k + 1 + 2 = (k + 2) + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]
    rw [h, Nat.mul_add, ih]
    ring

/-- The two subwords partition the word, since every letter has exactly one colour. -/
theorem length_subword_add_length_subword :
    (subword D.word .thick).length + (subword D.word .thin).length = D.word.length := by
  classical
  rw [subword, subword, List.length_map, List.length_map,
    ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  induction D.word with
  | nil => rfl
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.length_cons]
    cases a.2 <;> simp <;> omega

/-- **The word has one letter per colour per pair of strands**, so its length is
`(n + 2) * (n + 1)`. -/
theorem length_word : D.word.length = (n + 2) * (n + 1) := by
  rw [← D.length_subword_add_length_subword, D.length_subword, D.length_subword,
    ← two_mul_choose_two n]
  ring

end DoubleWiringDiagram

end ClusterAlgebras

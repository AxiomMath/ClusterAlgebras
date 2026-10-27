/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.DoubleWiring.Chamber

/-!
# Chamber labels

Each chamber of a double wiring diagram is assigned a pair of subsets of `[1,n]`, one per colour,
recording which curves of that colour pass below it. The pair is the chamber's label, and it names
the chamber minor `Δ_{I,J}`.

## Main definitions

* `ClusterAlgebras.Colour.numbering`: the numbering of the curves of each colour.
* `ClusterAlgebras.DoubleWiringDiagram.belowSet`: the curves of one colour lying at or below a gap.
* `ClusterAlgebras.DoubleWiringDiagram.label`: the label of a chamber.

## Implementation notes

Reading the left edge from the bottom, the thick curves are numbered `1, 2, …, n` and the thin
curves `n, …, 2, 1`, so a thin curve's number is the reverse of the level it starts at; this is
`ClusterAlgebras.Colour.numbering`.

A label may be read at any position of the chamber's span, with the same result by
`WiringDiagram.lem_chamber_set_well_defined` for the colour's own wiring diagram, since no crossing
of the chamber's gap of either colour occurs within the span. Here the label is read at the span's
left end.
-/

@[expose] public section

namespace ClusterAlgebras

namespace Colour

variable {n : ℕ}

/-- The numbering of the curves of each colour: a thick curve is numbered by the level it starts
at, and a thin curve by the reverse of that level. -/
def numbering : Colour → Equiv.Perm (Fin (n + 2))
  | .thick => Equiv.refl _
  | .thin => Fin.revPerm

/-- A thick curve is numbered by the level it starts at. -/
@[simp]
theorem numbering_thick (v : Fin (n + 2)) : (numbering .thick) v = v := rfl

/-- A thin curve is numbered by the reverse of the level it starts at. -/
@[simp]
theorem numbering_thin (v : Fin (n + 2)) : (numbering .thin) v = Fin.rev v := rfl

end Colour

namespace DoubleWiringDiagram

variable {n : ℕ} (D : DoubleWiringDiagram n)

/-- The number of crossings of one colour at positions before `t` — the position in that colour's
own subword corresponding to the position `t` of the interleaved word. -/
def colourCountUpTo (e : Colour) (t : ℕ) : ℕ :=
  ((D.word.take t).filter fun x => x.2 = e).length

/-- No crossing of either colour precedes the first position. -/
@[simp]
theorem colourCountUpTo_zero (e : Colour) : D.colourCountUpTo e 0 = 0 := by
  simp [colourCountUpTo]

/-- The curves of one colour lying at or below a gap after `t` of that colour's crossings, numbered
by `Colour.numbering` for that colour. -/
def belowSet (e : Colour) (t : ℕ) (G : Fin (n + 2)) : Finset (Fin (n + 2)) :=
  {v ∈ Finset.univ | (D.toWiringDiagram e).levelOf t ((Colour.numbering e).symm v) ≤ G}

/-- Membership in `belowSet`, unfolded. -/
@[simp]
theorem mem_belowSet {e : Colour} {t : ℕ} {G v : Fin (n + 2)} :
    v ∈ D.belowSet e t G ↔
      (D.toWiringDiagram e).levelOf t ((Colour.numbering e).symm v) ≤ G := by
  simp [belowSet]

/-- The label of a chamber, one subset per colour: the curves of that colour passing below it.
The pair `(I, J)`, with `I` the thin curves and `J` the thick ones, indexes the chamber minor
`Δ_{I,J}`. -/
@[cluster_algebras "def_double_chamber_label"]
def label (c : D.Chamber) (e : Colour) : Finset (Fin (n + 2)) :=
  D.belowSet e (D.colourCountUpTo e c.left) c.gap

/-- Membership in a chamber's label, unfolded. -/
@[simp]
theorem mem_label {c : D.Chamber} {e : Colour} {v : Fin (n + 2)} :
    v ∈ D.label c e ↔
      (D.toWiringDiagram e).levelOf (D.colourCountUpTo e c.left)
        ((Colour.numbering e).symm v) ≤ c.gap := by
  rw [label, mem_belowSet]

/-- The chamber above every curve is labelled by every curve of each colour: its label is the pair
`([1,n], [1,n])`. -/
@[simp]
theorem label_top (e : Colour) :
    D.label ⟨Fin.last _, 0, by simp⟩ e = Finset.univ := by
  ext v
  simp only [mem_label, Finset.mem_univ, iff_true]
  exact Fin.le_last _

end DoubleWiringDiagram

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.DoubleWiring.Quiver

/-!
# Local moves on a double wiring diagram

There are three kinds of local move on a double wiring diagram: a braid move inside the thick
family, a braid move inside the thin family, and a two-crossing move exchanging a thick and a thin
crossing of the same level. The third is not a braid move, its block has length two, and it
changes the quiver: the chamber between the two crossings acquires ends of the other two colours.

## Main definitions

* `DoubleWiringDiagram.chamberAt`: the chamber of a given gap spanning a given position.
* `DoubleWiringDiagram.LocalMove`: the relation between two double wiring diagrams whose words
  agree outside a short block and differ inside it by one of the three local moves.
* `DoubleWiringDiagram.siteBraid`, `DoubleWiringDiagram.siteColour`: the chamber at which a local
  move takes place.

## Main results

* `DoubleWiringDiagram.subword_swap_of_colour_ne`: exchanging two adjacent letters of different
  colours leaves each colour's subword unchanged.

## Implementation notes

A local move is a relation between `D` and `D'` rather than a function building `D'` from `D`.
Whether a given `D'` is a double wiring diagram is then a property of `D'`, carried by its own
fields, and the move need not re-establish the structure conditions of `DoubleWiringDiagram`.

The colour-exchange move leaves both subwords unchanged as lists: the thick letter and the thin
letter exchange places in the interleaved word, but each keeps its index within its own colour's
subword.
-/

@[expose] public section

namespace ClusterAlgebras

namespace DoubleWiringDiagram

variable {n : ℕ} (D : DoubleWiringDiagram n)

/-- The chamber of a given gap spanning a given position. -/
def chamberAt (g : Fin (n + 2)) (t : ℕ) (ht : t ≤ D.word.length) : D.Chamber where
  gap := g
  idx := D.countUpTo g t
  idx_le := by
    have h := D.countUpTo_le_of_le (g := g) ht
    rwa [D.countUpTo_length] at h

/-- `D.chamberAt g t ht` lies in gap `g`. -/
@[simp]
theorem gap_chamberAt (g : Fin (n + 2)) (t : ℕ) (ht : t ≤ D.word.length) :
    (D.chamberAt g t ht).gap = g := rfl

/-- The index of `D.chamberAt g t ht` is the number of crossings in gap `g` before position `t`.
-/
@[simp]
theorem idx_chamberAt (g : Fin (n + 2)) (t : ℕ) (ht : t ≤ D.word.length) :
    (D.chamberAt g t ht).idx = D.countUpTo g t := rfl

/-- Position `t` lies in the span of `D.chamberAt g t ht`. -/
@[simp]
theorem inSpan_chamberAt (g : Fin (n + 2)) (t : ℕ) (ht : t ≤ D.word.length) :
    (D.chamberAt g t ht).InSpan t := rfl

/-- **A local move**: `D` and `D'` agree outside a block starting at position `p`, and inside it
they differ by one of:

* a braid move inside one colour, exchanging levels `g, h, g` for `h, g, h` with `h` one above
  `g`;
* an exchange of a thick and a thin crossing of the same level, in a block of length two. -/
@[cluster_algebras "def_double_local_move"]
def LocalMove (D D' : DoubleWiringDiagram n) (p : ℕ) : Prop :=
  (∃ (e : Colour) (g h : Fin (n + 1)), (g : ℕ) + 1 = (h : ℕ) ∧
      D.word.take p = D'.word.take p ∧
      D.word.drop (p + 3) = D'.word.drop (p + 3) ∧
      (D.word.drop p).take 3 = [(g, e), (h, e), (g, e)] ∧
      (D'.word.drop p).take 3 = [(h, e), (g, e), (h, e)]) ∨
    (∃ g : Fin (n + 1),
      D.word.take p = D'.word.take p ∧
      D.word.drop (p + 2) = D'.word.drop (p + 2) ∧
      (D.word.drop p).take 2 = [(g, .thick), (g, .thin)] ∧
      (D'.word.drop p).take 2 = [(g, .thin), (g, .thick)])

/-- **The site of a braid move**: the chamber of the moved gap spanning the middle of the
three crossings. -/
def siteBraid (g : Fin (n + 1)) (p : ℕ) (hp : p + 3 ≤ D.word.length) : D.Chamber :=
  D.chamberAt g.castSucc (p + 1) (by omega)

/-- **The site of a colour exchange**: the chamber of the level's gap between the two
crossings. -/
def siteColour (g : Fin (n + 1)) (p : ℕ) (hp : p + 2 ≤ D.word.length) : D.Chamber :=
  D.chamberAt g.castSucc (p + 1) (by omega)

/-- The braid-move site lies in the moved level's gap. -/
@[simp]
theorem gap_siteBraid (g : Fin (n + 1)) (p : ℕ) (hp : p + 3 ≤ D.word.length) :
    (D.siteBraid g p hp).gap = g.castSucc := rfl

/-- The colour-exchange site lies in the exchanged level's gap. -/
@[simp]
theorem gap_siteColour (g : Fin (n + 1)) (p : ℕ) (hp : p + 2 ≤ D.word.length) :
    (D.siteColour g p hp).gap = g.castSucc := rfl

/-- The index of the braid-move site counts the moved gap's crossings before position `p + 1`. -/
@[simp]
theorem idx_siteBraid (g : Fin (n + 1)) (p : ℕ) (hp : p + 3 ≤ D.word.length) :
    (D.siteBraid g p hp).idx = D.countUpTo g.castSucc (p + 1) := rfl

/-- The index of the colour-exchange site counts the level's gap crossings before `p + 1`. -/
@[simp]
theorem idx_siteColour (g : Fin (n + 1)) (p : ℕ) (hp : p + 2 ≤ D.word.length) :
    (D.siteColour g p hp).idx = D.countUpTo g.castSucc (p + 1) := rfl

/-! ### The colour exchange leaves both subwords unchanged -/

/-- Exchanging two adjacent letters of different colours leaves each colour's subword unchanged.
-/
theorem subword_swap_of_colour_ne {a b : Fin (n + 1) × Colour} (hab : a.2 ≠ b.2)
    (l r : List (Fin (n + 1) × Colour)) (e : Colour) :
    subword (l ++ b :: a :: r) e = subword (l ++ a :: b :: r) e := by
  rcases eq_or_ne a.2 e with ha | ha
  · have hb : b.2 ≠ e := fun h => hab (ha.trans h.symm)
    simp [subword, List.filter_append, ha, hb]
  · rcases eq_or_ne b.2 e with hb | hb <;> simp [subword, List.filter_append, ha, hb]

end DoubleWiringDiagram

end ClusterAlgebras

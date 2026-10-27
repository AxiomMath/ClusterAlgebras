/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CycleSpace
public import ClusterAlgebras.DoubleWiring.Basic

/-!
# The plabic graph of a coloured word

Let `E = ((i_1, ε_1), …, (i_p, ε_p))` be a word on `N` levels: each letter is a crossing level
`i_t ∈ [1, N - 1]` together with a colour `ε_t`, thick or thin. Write
`P_ℓ = {t : i_t = ℓ or i_t = ℓ - 1}` for the crossings touching the level `ℓ ∈ [1, N]`, and
`nx_ℓ(s)` for the least element of `P_ℓ` after a position `s ∈ P_ℓ ∪ {-∞}` (or `+∞`). The plabic
graph `G(E) = (H, d ↦ d̄, σ, B, κ, β)` has the darts
`r_(ℓ,s)` (`s ∈ P_ℓ ∪ {-∞}`), `l_(ℓ,s)` (`s ∈ P_ℓ ∪ {+∞}`), `u_t`, `ū_t` and `e_j`, `ē_j`
(`j ∈ [1, 2N]`), the involution `r_(ℓ,s) ↔ l_(ℓ,nx_ℓ(s))`, `u_t ↔ ū_t`, `e_j ↔ ē_j`, and the
rotation
* `r_(ℓ,t) ↦ u_t ↦ l_(ℓ,t) ↦ r_(ℓ,t)` for `ℓ = i_t`;
* `r_(ℓ,t) ↦ l_(ℓ,t) ↦ ū_t ↦ r_(ℓ,t)` for `ℓ = i_t + 1`;
* `g_j ↦ ē_(j+1) ↦ e_j ↦ g_j`, where `g_ℓ = r_(ℓ,-∞)` and `g_(2N+1-ℓ) = l_(ℓ,+∞)`.

The boundary arcs are the darts `e_j`, `ē_j`; the vertex of `u_t` is white and that of `ū_t` black
when `ε_t` is thick, and the reverse when it is thin; and `β(j)` is the vertex of `g_j`.

In FWZ's picture, level `ℓ` is the `ℓ`-th horizontal line from the bottom, running from the
boundary vertex `ℓ` on the left to the boundary vertex `2N + 1 - ℓ` on the right; the crossing
`t` is a vertical edge `u_t` from a vertex on level `i_t` to a vertex on level `i_t + 1`; and
`r_(ℓ,s)`, `l_(ℓ,s)` are the pieces of level `ℓ` leaving the vertex at position `s` to the right
and to the left. A wiring diagram is such a word with every letter thick, and a double wiring
diagram is such a word as it stands.

The proof that `G(E)` is a plabic graph labels every dart by the face to its right: `∞` for the
exterior, and otherwise a pair `(g, j)`, the chamber of the gap `g ∈ [0, N]` (between the levels
`g` and `g + 1`) lying between the `j`-th and the `(j + 1)`-st crossings of that gap. This
labelling is constant along `φ`, and Euler's relation for the labels identifies the faces with
the labels.

## Main definitions

* `ClusterAlgebras.WordDart E`: the darts of `G(E)`.
* `ClusterAlgebras.wordPlabicData E`: the tuple `G(E)`.
* `ClusterAlgebras.WordDart.faceLabel E`: the labelling of the darts of `G(E)` by chambers.

## Main results

* `ClusterAlgebras.faceOf_eq_faceOf_iff_faceLabel_eq`: two darts of `G(E)` lie on the same face
  exactly when they have the same chamber label.
* `ClusterAlgebras.isPlabicGraph_wordPlabicData`: `G(E)` is a plabic graph with `2N` boundary
  vertices.

## Implementation notes

* The number of levels is `N = n + 1`, so that a word is a function `E : Fin p → Fin n × Colour`
  and no hypothesis `N ≥ 2` is needed: FWZ ask for `N ≥ 2`, but the construction and the
  theorem hold for every `N ≥ 1`. Everything is `0`-indexed: the level `ℓ : Fin (n + 1)` is FWZ's
  level `ℓ + 1`, the crossing level `c : Fin n` of a letter joins the levels
  `c.castSucc` and `c.succ` (FWZ's `i_t = c + 1`), the position `t : Fin p` is FWZ's
  `t + 1`, and the boundary label `j : Fin (2 * (n + 1))` is FWZ's `j + 1`. With
  `n + 1` levels a double wiring diagram on `n + 2` strands is exactly a word here.
* A dart `r_(ℓ,t)` with `t ∈ P_ℓ` is `rLow t` when `ℓ = i_t` and `rUp t` when `ℓ = i_t + 1`, and
  likewise for `l_(ℓ,t)`: the darts are indexed by the vertices they leave, so that the three
  darts of each internal vertex are three constructors of the same index. The darts
  `r_(ℓ,-∞)`, `l_(ℓ,+∞)` are `rStart ℓ` and `lEnd ℓ`.
* The positions `-∞ < t < +∞` are the elements of `WithBot (Fin p)` (for the darts `r`) and of
  `WithTop (Fin p)` (for the darts `l`), and `nx_ℓ` is `nextAbove (levelCrossings E ℓ)`, a minimum
  over a `Finset`; its inverse is `prevBelow`.
* The colour is a function on darts; its value at the boundary darts is irrelevant and is
  `black`.
* The labels of the faces form the `Finset` `faceLabels E` of values `none` (for `∞`) and
  `some (g, j)` with `j ≤ c_g`, the number of crossings in the gap `g`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Neighbours in a finite set of positions -/

section Neighbours

variable {α : Type*} [LinearOrder α]

/-- The least element of `P` above a position `s ∈ α ∪ {-∞}`, or `+∞` if there is none. -/
def nextAbove (P : Finset α) (s : WithBot α) : WithTop α :=
  (P.filter fun t : α => s < (↑t : WithBot α)).min

/-- The greatest element of `P` below a position `s ∈ α ∪ {+∞}`, or `-∞` if there is none. -/
def prevBelow (P : Finset α) (s : WithTop α) : WithBot α :=
  (P.filter fun t : α => (↑t : WithTop α) < s).max

variable {P : Finset α}

/-- If `nextAbove P s = b`, then `b` is the least element of `P` above `s`. -/
theorem nextAbove_eq_coe {s : WithBot α} {b : α} (h : nextAbove P s = b) :
    b ∈ P ∧ s < b ∧ ∀ t ∈ P, s < t → b ≤ t := by
  have hm := Finset.mem_of_min h
  rw [mem_filter] at hm
  refine ⟨hm.1, hm.2, fun t ht hst => ?_⟩
  have := Finset.min_le (s := P.filter fun t : α => s < (↑t : WithBot α))
    (mem_filter.2 ⟨ht, hst⟩)
  rw [nextAbove] at h
  rw [h] at this
  exact WithTop.coe_le_coe.1 this

/-- If `nextAbove P s = ⊤`, then every element of `P` is at most `s`. -/
theorem nextAbove_eq_top {s : WithBot α} (h : nextAbove P s = ⊤) :
    ∀ t ∈ P, (t : WithBot α) ≤ s := by
  intro t ht
  by_contra hlt
  rw [nextAbove, Finset.min_eq_top] at h
  have : t ∈ P.filter fun t : α => s < (↑t : WithBot α) := mem_filter.2 ⟨ht, not_le.1 hlt⟩
  simp [h] at this

/-- If `prevBelow P s = b`, then `b` is the greatest element of `P` below `s`. -/
theorem prevBelow_eq_coe {s : WithTop α} {b : α} (h : prevBelow P s = b) :
    b ∈ P ∧ (b : WithTop α) < s ∧ ∀ t ∈ P, (t : WithTop α) < s → t ≤ b := by
  have hm := Finset.mem_of_max h
  rw [mem_filter] at hm
  refine ⟨hm.1, hm.2, fun t ht hst => ?_⟩
  have := Finset.le_max (s := P.filter fun t : α => (↑t : WithTop α) < s)
    (mem_filter.2 ⟨ht, hst⟩)
  rw [prevBelow] at h
  rw [h] at this
  exact WithBot.coe_le_coe.1 this

/-- If `prevBelow P s = ⊥`, then every element of `P` is at least `s`. -/
theorem prevBelow_eq_bot {s : WithTop α} (h : prevBelow P s = ⊥) :
    ∀ t ∈ P, s ≤ (t : WithTop α) := by
  intro t ht
  by_contra hlt
  rw [prevBelow, Finset.max_eq_bot] at h
  have : t ∈ P.filter fun t : α => (↑t : WithTop α) < s := mem_filter.2 ⟨ht, not_le.1 hlt⟩
  simp [h] at this

/-- `nextAbove P s` is either `⊤` or an element of `α`. -/
theorem nextAbove_cases (s : WithBot α) :
    nextAbove P s = ⊤ ∨ ∃ b : α, nextAbove P s = ↑b := by
  cases h : nextAbove P s with
  | top => exact .inl rfl
  | coe b => exact .inr ⟨b, rfl⟩

/-- `prevBelow P s` is either `⊥` or an element of `α`. -/
theorem prevBelow_cases (s : WithTop α) :
    prevBelow P s = ⊥ ∨ ∃ b : α, prevBelow P s = ↑b := by
  cases h : prevBelow P s with
  | bot => exact .inl rfl
  | coe b => exact .inr ⟨b, rfl⟩

/-- `prevBelow P` undoes `nextAbove P` on `P ∪ {-∞}`. -/
theorem prevBelow_nextAbove {s : WithBot α} (hs : ∀ a : α, s = a → a ∈ P) :
    prevBelow P (nextAbove P s) = s := by
  rcases nextAbove_cases (P := P) s with h | ⟨b, h⟩
  · have hle := nextAbove_eq_top h
    rw [h]
    rcases prevBelow_cases (P := P) ⊤ with h' | ⟨c, h'⟩
    · rw [h']
      cases s with
      | bot => rfl
      | coe a =>
        have := prevBelow_eq_bot h' a (hs a rfl)
        exact absurd this (by simp)
    · obtain ⟨hc, -, hcmax⟩ := prevBelow_eq_coe h'
      rw [h']
      cases s with
      | bot => exact absurd (hle c hc) (by simp)
      | coe a =>
        have h1 := WithBot.coe_le_coe.1 (hle c hc)
        have h2 := hcmax a (hs a rfl) (by simp)
        rw [le_antisymm h1 h2]
  · obtain ⟨hb, hsb, hbmin⟩ := nextAbove_eq_coe h
    rw [h]
    rcases prevBelow_cases (P := P) (b : WithTop α) with h' | ⟨c, h'⟩
    · rw [h']
      cases s with
      | bot => rfl
      | coe a =>
        have := prevBelow_eq_bot h' a (hs a rfl)
        exact absurd (WithTop.coe_le_coe.1 this) (not_le.2 (WithBot.coe_lt_coe.1 hsb))
    · obtain ⟨hc, hcb, hcmax⟩ := prevBelow_eq_coe h'
      rw [h']
      have hcb' := WithTop.coe_lt_coe.1 hcb
      cases s with
      | bot =>
        have := hbmin c hc (WithBot.bot_lt_coe c)
        exact absurd this (not_le.2 hcb')
      | coe a =>
        have h1 : c ≤ a := by
          by_contra hca
          exact absurd (hbmin c hc (WithBot.coe_lt_coe.2 (not_le.1 hca))) (not_le.2 hcb')
        have h2 := hcmax a (hs a rfl) (WithTop.coe_lt_coe.2 (WithBot.coe_lt_coe.1 hsb))
        rw [le_antisymm h1 h2]

/-- `nextAbove P` undoes `prevBelow P` on `P ∪ {+∞}`. -/
theorem nextAbove_prevBelow {s : WithTop α} (hs : ∀ a : α, s = a → a ∈ P) :
    nextAbove P (prevBelow P s) = s := by
  rcases prevBelow_cases (P := P) s with h | ⟨b, h⟩
  · have hle := prevBelow_eq_bot h
    rw [h]
    rcases nextAbove_cases (P := P) ⊥ with h' | ⟨c, h'⟩
    · rw [h']
      cases s with
      | top => rfl
      | coe a =>
        have := nextAbove_eq_top h' a (hs a rfl)
        exact absurd this (by simp)
    · obtain ⟨hc, -, hcmin⟩ := nextAbove_eq_coe h'
      rw [h']
      cases s with
      | top => exact absurd (hle c hc) (by simp)
      | coe a =>
        have h1 := WithTop.coe_le_coe.1 (hle c hc)
        have h2 := hcmin a (hs a rfl) (by simp)
        rw [le_antisymm h2 h1]
  · obtain ⟨hb, hsb, hbmax⟩ := prevBelow_eq_coe h
    rw [h]
    rcases nextAbove_cases (P := P) (b : WithBot α) with h' | ⟨c, h'⟩
    · rw [h']
      cases s with
      | top => rfl
      | coe a =>
        have := nextAbove_eq_top h' a (hs a rfl)
        exact absurd (WithBot.coe_le_coe.1 this) (not_le.2 (WithTop.coe_lt_coe.1 hsb))
    · obtain ⟨hc, hcb, hcmin⟩ := nextAbove_eq_coe h'
      rw [h']
      have hcb' := WithBot.coe_lt_coe.1 hcb
      cases s with
      | top =>
        have := hbmax c hc (WithTop.coe_lt_top c)
        exact absurd this (not_le.2 hcb')
      | coe a =>
        have h1 : a ≤ c := by
          by_contra hca
          exact absurd (hbmax c hc (WithTop.coe_lt_coe.2 (not_le.1 hca))) (not_le.2 hcb')
        have h2 := hcmin a (hs a rfl) (WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.1 hsb))
        rw [le_antisymm h2 h1]

end Neighbours

/-! ### The darts -/

variable {n p : ℕ}

/-- The two levels `c.castSucc` and `c.succ` joined by a crossing of level `c` differ. -/
private theorem castSucc_ne_succ (c : Fin n) : c.castSucc ≠ c.succ := Fin.castSucc_lt_succ.ne

/-- The set `P_ℓ` of the crossings of the word `E` touching the level `ℓ`: those of crossing level
`ℓ` (joining `ℓ` to the level above) or `ℓ - 1` (joining the level below to `ℓ`). -/
def levelCrossings (E : Fin p → Fin n × Colour) (ℓ : Fin (n + 1)) : Finset (Fin p) :=
  univ.filter fun t => (E t).1.castSucc = ℓ ∨ (E t).1.succ = ℓ

/-- The **darts** of the plabic graph `G(E)` of a word `E` on `n + 1` levels. For a level `ℓ`, the
darts `r_(ℓ,-∞)` (`rStart ℓ`) and `l_(ℓ,+∞)` (`lEnd ℓ`) are the legs at the two ends of the level;
for a position `t`, with `E t = (c, ε)`, the darts `r_(c,t)`, `l_(c,t)` (`rLow t`, `lLow t`) and
`u_t` (`cross t`) leave the lower vertex of the crossing, on the level `c.castSucc`, and the darts
`r_(c+1,t)`, `l_(c+1,t)` (`rUp t`, `lUp t`) and `ū_t` (`crossBar t`) leave the upper one, on the
level `c.succ`; and `e_j` (`arc j`), `ē_j` (`arcBar j`) are the boundary arcs. -/
inductive WordDart (E : Fin p → Fin n × Colour) : Type
  /-- The dart `r_(ℓ,-∞)` leaving the left end of the level `ℓ` to the right. -/
  | rStart (ℓ : Fin (n + 1))
  /-- The dart `l_(ℓ,+∞)` leaving the right end of the level `ℓ` to the left. -/
  | lEnd (ℓ : Fin (n + 1))
  /-- The dart `r_(i_t,t)` leaving the lower vertex of the crossing `t` to the right. -/
  | rLow (t : Fin p)
  /-- The dart `l_(i_t,t)` leaving the lower vertex of the crossing `t` to the left. -/
  | lLow (t : Fin p)
  /-- The dart `r_(i_t+1,t)` leaving the upper vertex of the crossing `t` to the right. -/
  | rUp (t : Fin p)
  /-- The dart `l_(i_t+1,t)` leaving the upper vertex of the crossing `t` to the left. -/
  | lUp (t : Fin p)
  /-- The dart `u_t` of the crossing `t`, leaving its lower vertex upwards. -/
  | cross (t : Fin p)
  /-- The dart `ū_t` of the crossing `t`, leaving its upper vertex downwards. -/
  | crossBar (t : Fin p)
  /-- The boundary arc `e_j` from the boundary vertex `j` to the boundary vertex `j - 1`. -/
  | arc (j : Fin (2 * (n + 1)))
  /-- The boundary arc `ē_j`, the reverse of `e_j`. -/
  | arcBar (j : Fin (2 * (n + 1)))
  deriving DecidableEq, Fintype

namespace WordDart

variable {E : Fin p → Fin n × Colour}

/-- The dart `r_(ℓ,s)` of the level `ℓ` at the position `s ∈ P_ℓ ∪ {-∞}`. -/
def rDart (E : Fin p → Fin n × Colour) (ℓ : Fin (n + 1)) (s : WithBot (Fin p)) : WordDart E :=
  WithBot.recBotCoe (rStart ℓ) (fun t => if (E t).1.castSucc = ℓ then rLow t else rUp t) s

/-- The dart `l_(ℓ,s)` of the level `ℓ` at the position `s ∈ P_ℓ ∪ {+∞}`. -/
def lDart (E : Fin p → Fin n × Colour) (ℓ : Fin (n + 1)) (s : WithTop (Fin p)) : WordDart E :=
  WithTop.recTopCoe (lEnd ℓ) (fun t => if (E t).1.castSucc = ℓ then lLow t else lUp t) s

/-- `r_(ℓ,-∞)` is `rStart ℓ`. -/
@[simp] theorem rDart_bot (ℓ : Fin (n + 1)) : rDart E ℓ ⊥ = rStart ℓ := rfl

/-- `l_(ℓ,+∞)` is `lEnd ℓ`. -/
@[simp] theorem lDart_top (ℓ : Fin (n + 1)) : lDart E ℓ ⊤ = lEnd ℓ := rfl

/-- `r_(ℓ,t)` is `rLow t` on the lower level of the crossing `t` and `rUp t` otherwise. -/
theorem rDart_coe (ℓ : Fin (n + 1)) (t : Fin p) :
    rDart E ℓ t = if (E t).1.castSucc = ℓ then rLow t else rUp t := rfl

/-- `l_(ℓ,t)` is `lLow t` on the lower level of the crossing `t` and `lUp t` otherwise. -/
theorem lDart_coe (ℓ : Fin (n + 1)) (t : Fin p) :
    lDart E ℓ t = if (E t).1.castSucc = ℓ then lLow t else lUp t := rfl

/-- On the lower level of the crossing `t`, `r_(ℓ,t)` is `rLow t`. -/
@[simp] theorem rDart_castSucc (t : Fin p) : rDart E (E t).1.castSucc t = rLow t := by
  simp [rDart_coe]

/-- On the lower level of the crossing `t`, `l_(ℓ,t)` is `lLow t`. -/
@[simp] theorem lDart_castSucc (t : Fin p) : lDart E (E t).1.castSucc t = lLow t := by
  simp [lDart_coe]

/-- On the upper level of the crossing `t`, `r_(ℓ,t)` is `rUp t`. -/
@[simp] theorem rDart_succ (t : Fin p) : rDart E (E t).1.succ t = rUp t := by
  simp [rDart_coe, castSucc_ne_succ]

/-- On the upper level of the crossing `t`, `l_(ℓ,t)` is `lUp t`. -/
@[simp] theorem lDart_succ (t : Fin p) : lDart E (E t).1.succ t = lUp t := by
  simp [lDart_coe, castSucc_ne_succ]

/-- The next position `nx_ℓ(s)` of the level `ℓ` after `s`. -/
abbrev nx (E : Fin p → Fin n × Colour) (ℓ : Fin (n + 1)) (s : WithBot (Fin p)) :
    WithTop (Fin p) :=
  nextAbove (levelCrossings E ℓ) s

/-- The previous position of the level `ℓ` before `s`, the inverse of `nx_ℓ`. -/
abbrev pv (E : Fin p → Fin n × Colour) (ℓ : Fin (n + 1)) (s : WithTop (Fin p)) :
    WithBot (Fin p) :=
  prevBelow (levelCrossings E ℓ) s

/-- The involution `d ↦ d̄` of `G(E)`: `r_(ℓ,s) ↔ l_(ℓ,nx_ℓ(s))`, `u_t ↔ ū_t`, `e_j ↔ ē_j`. -/
def reverse : WordDart E → WordDart E
  | rStart ℓ => lDart E ℓ (nx E ℓ ⊥)
  | rLow t => lDart E (E t).1.castSucc (nx E (E t).1.castSucc t)
  | rUp t => lDart E (E t).1.succ (nx E (E t).1.succ t)
  | lEnd ℓ => rDart E ℓ (pv E ℓ ⊤)
  | lLow t => rDart E (E t).1.castSucc (pv E (E t).1.castSucc t)
  | lUp t => rDart E (E t).1.succ (pv E (E t).1.succ t)
  | cross t => crossBar t
  | crossBar t => cross t
  | arc j => arcBar j
  | arcBar j => arc j

/-- The reverse of `u_t` is `ū_t`. -/
@[simp] theorem reverse_cross (t : Fin p) : (cross t : WordDart E).reverse = crossBar t := rfl

/-- The reverse of `ū_t` is `u_t`. -/
@[simp] theorem reverse_crossBar (t : Fin p) : (crossBar t : WordDart E).reverse = cross t := rfl

/-- The reverse of `e_j` is `ē_j`. -/
@[simp] theorem reverse_arc (j : Fin (2 * (n + 1))) : (arc j : WordDart E).reverse = arcBar j :=
  rfl

/-- The reverse of `ē_j` is `e_j`. -/
@[simp] theorem reverse_arcBar (j : Fin (2 * (n + 1))) :
    (arcBar j : WordDart E).reverse = arc j := rfl

/-- The crossing `t` touches its lower level. -/
theorem mem_levelCrossings_castSucc (t : Fin p) : t ∈ levelCrossings E (E t).1.castSucc := by
  simp [levelCrossings]

/-- The crossing `t` touches its upper level. -/
theorem mem_levelCrossings_succ (t : Fin p) : t ∈ levelCrossings E (E t).1.succ := by
  simp [levelCrossings]

/-- The crossing `t` touches the level `ℓ` exactly when `ℓ` is its lower or its upper level. -/
theorem mem_levelCrossings {ℓ : Fin (n + 1)} {t : Fin p} :
    t ∈ levelCrossings E ℓ ↔ (E t).1.castSucc = ℓ ∨ (E t).1.succ = ℓ := by
  simp [levelCrossings]

/-- `r_(ℓ,s)` is reversed to `l_(ℓ,nx_ℓ(s))`. -/
theorem reverse_rDart {ℓ : Fin (n + 1)} {s : WithBot (Fin p)}
    (hs : ∀ t : Fin p, s = t → t ∈ levelCrossings E ℓ) :
    (rDart E ℓ s).reverse = lDart E ℓ (nx E ℓ s) := by
  cases s with
  | bot => rfl
  | coe t =>
    rcases mem_levelCrossings.1 (hs t rfl) with h | h
    · subst h; simp [reverse]
    · subst h; simp [reverse]

/-- `l_(ℓ,s)` is reversed to `r_(ℓ,pv_ℓ(s))`. -/
theorem reverse_lDart {ℓ : Fin (n + 1)} {s : WithTop (Fin p)}
    (hs : ∀ t : Fin p, s = t → t ∈ levelCrossings E ℓ) :
    (lDart E ℓ s).reverse = rDart E ℓ (pv E ℓ s) := by
  cases s with
  | top => rfl
  | coe t =>
    rcases mem_levelCrossings.1 (hs t rfl) with h | h
    · subst h; simp [reverse]
    · subst h; simp [reverse]

/-- A finite position `nx_ℓ(s)` lies in `P_ℓ`. -/
theorem nx_mem {ℓ : Fin (n + 1)} (s : WithBot (Fin p)) :
    ∀ t : Fin p, nx E ℓ s = t → t ∈ levelCrossings E ℓ :=
  fun _ h => (nextAbove_eq_coe h).1

/-- A finite position `pv_ℓ(s)` lies in `P_ℓ`. -/
theorem pv_mem {ℓ : Fin (n + 1)} (s : WithTop (Fin p)) :
    ∀ t : Fin p, pv E ℓ s = t → t ∈ levelCrossings E ℓ :=
  fun _ h => (prevBelow_eq_coe h).1

/-- `pv_ℓ` undoes `nx_ℓ` on `P_ℓ ∪ {-∞}`. -/
theorem pv_nx {ℓ : Fin (n + 1)} {s : WithBot (Fin p)}
    (hs : ∀ t : Fin p, s = t → t ∈ levelCrossings E ℓ) : pv E ℓ (nx E ℓ s) = s :=
  prevBelow_nextAbove hs

/-- `nx_ℓ` undoes `pv_ℓ` on `P_ℓ ∪ {+∞}`. -/
theorem nx_pv {ℓ : Fin (n + 1)} {s : WithTop (Fin p)}
    (hs : ∀ t : Fin p, s = t → t ∈ levelCrossings E ℓ) : nx E ℓ (pv E ℓ s) = s :=
  nextAbove_prevBelow hs

/-- Reversing `r_(ℓ,s)` twice gives `r_(ℓ,s)`. -/
theorem reverse_reverse_rDart {ℓ : Fin (n + 1)} {s : WithBot (Fin p)}
    (hs : ∀ t : Fin p, s = t → t ∈ levelCrossings E ℓ) :
    (rDart E ℓ s).reverse.reverse = rDart E ℓ s := by
  rw [reverse_rDart hs, reverse_lDart (nx_mem s), pv_nx hs]

/-- Reversing `l_(ℓ,s)` twice gives `l_(ℓ,s)`. -/
theorem reverse_reverse_lDart {ℓ : Fin (n + 1)} {s : WithTop (Fin p)}
    (hs : ∀ t : Fin p, s = t → t ∈ levelCrossings E ℓ) :
    (lDart E ℓ s).reverse.reverse = lDart E ℓ s := by
  rw [reverse_lDart hs, reverse_rDart (pv_mem s), nx_pv hs]

/-- The position `t`, in `WithBot (Fin p)`, lies in `P_ℓ` for the lower level `ℓ` of the crossing
`t`. -/
theorem coe_mem_castSucc (t : Fin p) :
    ∀ t' : Fin p, ((t : WithBot (Fin p)) = t') → t' ∈ levelCrossings E (E t).1.castSucc := by
  intro t' h
  obtain rfl := WithBot.coe_injective h
  exact mem_levelCrossings_castSucc t

/-- The position `t`, in `WithBot (Fin p)`, lies in `P_ℓ` for the upper level `ℓ` of the crossing
`t`. -/
theorem coe_mem_succ (t : Fin p) :
    ∀ t' : Fin p, ((t : WithBot (Fin p)) = t') → t' ∈ levelCrossings E (E t).1.succ := by
  intro t' h
  obtain rfl := WithBot.coe_injective h
  exact mem_levelCrossings_succ t

/-- The position `t`, in `WithTop (Fin p)`, lies in `P_ℓ` for the lower level `ℓ` of the crossing
`t`. -/
theorem coe_mem_castSucc' (t : Fin p) :
    ∀ t' : Fin p, ((t : WithTop (Fin p)) = t') → t' ∈ levelCrossings E (E t).1.castSucc := by
  intro t' h
  obtain rfl := WithTop.coe_injective h
  exact mem_levelCrossings_castSucc t

/-- The position `t`, in `WithTop (Fin p)`, lies in `P_ℓ` for the upper level `ℓ` of the crossing
`t`. -/
theorem coe_mem_succ' (t : Fin p) :
    ∀ t' : Fin p, ((t : WithTop (Fin p)) = t') → t' ∈ levelCrossings E (E t).1.succ := by
  intro t' h
  obtain rfl := WithTop.coe_injective h
  exact mem_levelCrossings_succ t

/-- The map `d ↦ d̄` is an involution. -/
theorem reverse_involutive : Function.Involutive (reverse (E := E)) := by
  intro d
  cases d with
  | rStart ℓ => exact reverse_reverse_rDart (s := ⊥) (by simp)
  | lEnd ℓ => exact reverse_reverse_lDart (s := ⊤) (by simp)
  | rLow t =>
    have := reverse_reverse_rDart (coe_mem_castSucc (E := E) t)
    rwa [rDart_castSucc] at this
  | rUp t =>
    have := reverse_reverse_rDart (coe_mem_succ (E := E) t)
    rwa [rDart_succ] at this
  | lLow t =>
    have := reverse_reverse_lDart (coe_mem_castSucc' (E := E) t)
    rwa [lDart_castSucc] at this
  | lUp t =>
    have := reverse_reverse_lDart (coe_mem_succ' (E := E) t)
    rwa [lDart_succ] at this
  | cross t => rfl
  | crossBar t => rfl
  | arc j => rfl
  | arcBar j => rfl

/-- The kind of a dart: `0` for the darts `r`, `1` for the darts `l`, `2` for `u_t`, `3` for
`ū_t`, `4` for `e_j` and `5` for `ē_j`. -/
private def kind : WordDart E → Fin 6
  | rStart _ | rLow _ | rUp _ => 0
  | lEnd _ | lLow _ | lUp _ => 1
  | cross _ => 2
  | crossBar _ => 3
  | arc _ => 4
  | arcBar _ => 5

private theorem kind_rDart (ℓ : Fin (n + 1)) (s : WithBot (Fin p)) : kind (rDart E ℓ s) = 0 := by
  cases s with
  | bot => rfl
  | coe t => simp only [rDart_coe]; split <;> rfl

private theorem kind_lDart (ℓ : Fin (n + 1)) (s : WithTop (Fin p)) : kind (lDart E ℓ s) = 1 := by
  cases s with
  | top => rfl
  | coe t => simp only [lDart_coe]; split <;> rfl

/-- The involution `d ↦ d̄` has no fixed points. -/
theorem reverse_ne (d : WordDart E) : d.reverse ≠ d := by
  intro h
  have := congrArg kind h
  cases d <;> simp only [reverse, kind_rDart, kind_lDart] at this <;> simp [kind] at this

/-! ### The rotation -/

/-- The boundary label of the left end of the level `ℓ`: `ℓ`, so that `g_ℓ = r_(ℓ,-∞)`. -/
def legIndexR (ℓ : Fin (n + 1)) : Fin (2 * (n + 1)) := ⟨ℓ, by omega⟩

/-- The boundary label of the right end of the level `ℓ`: `2(n + 1) - 1 - ℓ`, so that
`g_(2(n + 1) - 1 - ℓ) = l_(ℓ,+∞)`, with labels and levels indexed from `0`. -/
def legIndexL (ℓ : Fin (n + 1)) : Fin (2 * (n + 1)) := ⟨2 * (n + 1) - 1 - ℓ, by omega⟩

/-- The leg `g_j` at the boundary vertex labelled `j`: `r_(ℓ,-∞)` for `j = ℓ ≤ n` and `l_(ℓ,+∞)`
for `j = 2(n + 1) - 1 - ℓ`. -/
def boundaryLeg (E : Fin p → Fin n × Colour) (j : Fin (2 * (n + 1))) : WordDart E :=
  if h : (j : ℕ) < n + 1 then rStart ⟨j, h⟩ else lEnd ⟨2 * (n + 1) - 1 - j, by omega⟩

/-- The leg at the left end of the level `ℓ` is `r_(ℓ,-∞)`. -/
@[simp]
theorem boundaryLeg_legIndexR (ℓ : Fin (n + 1)) : boundaryLeg E (legIndexR ℓ) = rStart ℓ := by
  rw [boundaryLeg, dif_pos (show ((legIndexR ℓ : Fin _) : ℕ) < n + 1 from ℓ.isLt)]
  rfl

/-- The leg at the right end of the level `ℓ` is `l_(ℓ,+∞)`. -/
@[simp]
theorem boundaryLeg_legIndexL (ℓ : Fin (n + 1)) : boundaryLeg E (legIndexL ℓ) = lEnd ℓ := by
  have := ℓ.isLt
  rw [boundaryLeg, dif_neg (by simp [legIndexL]; omega)]
  congr 1
  ext
  simp [legIndexL]
  omega

/-- The **rotation** `σ` of `G(E)`, as a function on darts: the `3`-cycles
`r_(c,t) ↦ u_t ↦ l_(c,t) ↦ r_(c,t)` and `r_(c+1,t) ↦ l_(c+1,t) ↦ ū_t ↦ r_(c+1,t)` at the two
vertices of each crossing, and `g_j ↦ ē_(j+1) ↦ e_j ↦ g_j` at each boundary vertex. -/
def rot : WordDart E → WordDart E
  | rLow t => cross t
  | cross t => lLow t
  | lLow t => rLow t
  | rUp t => lUp t
  | lUp t => crossBar t
  | crossBar t => rUp t
  | rStart ℓ => arcBar (finRotate _ (legIndexR ℓ))
  | lEnd ℓ => arcBar (finRotate _ (legIndexL ℓ))
  | arcBar j => arc ((finRotate _).symm j)
  | arc j => boundaryLeg E j

/-- The rotation sends `e_j` to `g_j`. -/
@[simp] theorem rot_arc (j : Fin (2 * (n + 1))) : rot (arc j : WordDart E) = boundaryLeg E j :=
  rfl

/-- The rotation sends `ē_j` to `e_(j-1)`. -/
@[simp] theorem rot_arcBar (j : Fin (2 * (n + 1))) :
    rot (arcBar j : WordDart E) = arc ((finRotate _).symm j) := rfl

/-- The rotation sends `g_j` to `ē_(j+1)`. -/
theorem rot_boundaryLeg (j : Fin (2 * (n + 1))) :
    rot (boundaryLeg E j) = arcBar (finRotate _ j) := by
  unfold boundaryLeg
  split_ifs with h
  · simp only [rot]
    congr 2
  · simp only [rot]
    congr 2
    ext
    simp [legIndexL]
    omega

/-- The cube of the rotation is the identity. -/
theorem rot_rot_rot (d : WordDart E) : rot (rot (rot d)) = d := by
  cases d with
  | rStart ℓ => simp [rot]
  | lEnd ℓ => simp [rot]
  | arc j => simp [rot_boundaryLeg]
  | arcBar j => simp [rot_boundaryLeg]
  | _ => rfl

/-- The **colour of the lower vertex** of a crossing: white if it is thick, black if it is thin.
The upper vertex has the other colour. -/
def lowerShade : Colour → Shade
  | .thick => .white
  | .thin => .black

/-- The colour of a dart of `G(E)`: at the crossing `t`, `lowerShade ε_t` on the lower vertex
`{r_(c,t), u_t, l_(c,t)}` and the other colour on the upper vertex `{r_(c+1,t), l_(c+1,t), ū_t}`;
`black` (an irrelevant value) at the boundary vertices. -/
def colour : WordDart E → Shade
  | rLow t | cross t | lLow t => lowerShade (E t).2
  | rUp t | lUp t | crossBar t => (lowerShade (E t).2).swap
  | _ => .black

/-- The colour is constant along the rotation. -/
theorem colour_rot (d : WordDart E) : (rot d).colour = d.colour := by
  cases d with
  | arc j =>
    simp only [rot_arc, boundaryLeg]
    split_ifs <;> rfl
  | _ => rfl

end WordDart

/-! ### The plabic graph -/

open WordDart in
/-- **The plabic graph `G(E)` of a coloured word** `E : Fin p → Fin n × Colour` on `n + 1` levels.
Its darts are `WordDart E`; the involution exchanges `r_(ℓ,s) ↔ l_(ℓ,nx_ℓ(s))`, `u_t ↔ ū_t`,
`e_j ↔ ē_j`; the rotation is `WordDart.rot`; the boundary arcs are the darts `e_j`, `ē_j`; the
vertex of `u_t` is white and that of `ū_t` black if `ε_t` is thick, and the reverse if it is thin;
and the boundary vertex `β(j)` labelled `j : Fin (2(n + 1))` is the vertex of the leg `g_j`. -/
@[cluster_algebras "def_word_plabic_graph"]
def wordPlabicData (E : Fin p → Fin n × Colour) : PlabicData (WordDart E) (2 * (n + 1)) where
  inv := reverse_involutive.toPerm
  rot := ⟨rot, fun d => rot (rot d), rot_rot_rot, rot_rot_rot⟩
  bdry := univ.filter fun d => ∃ j, d = arc j ∨ d = arcBar j
  colour := WordDart.colour
  leg := boundaryLeg E

section PlabicData

open WordDart

variable (E : Fin p → Fin n × Colour)

/-- The rotation of `G(E)` is `WordDart.rot`. -/
@[simp]
theorem wordPlabicData_rot_apply (d : WordDart E) : (wordPlabicData E).rot d = d.rot := rfl

/-- The involution of `G(E)` is `WordDart.reverse`. -/
@[simp]
theorem wordPlabicData_inv_apply (d : WordDart E) : (wordPlabicData E).inv d = d.reverse := rfl

/-- The boundary arcs of `G(E)` are the darts `e_j` and `ē_j`. -/
theorem mem_wordPlabicData_bdry {d : WordDart E} :
    d ∈ (wordPlabicData E).bdry ↔ ∃ j, d = arc j ∨ d = arcBar j := by
  simp [wordPlabicData]

/-- The colour of `G(E)` is `WordDart.colour`. -/
@[simp]
theorem wordPlabicData_colour (d : WordDart E) : (wordPlabicData E).colour d = d.colour := rfl

/-- The leg of `G(E)` at the boundary vertex `j` is `g_j`. -/
@[simp]
theorem wordPlabicData_leg (j : Fin (2 * (n + 1))) :
    (wordPlabicData E).leg j = boundaryLeg E j := rfl

/-- The vertex of a dart fixed by the cube of the rotation consists of the dart and its first two
images. -/
private theorem vertexOf_eq_of_rot_rot_rot {H : Type*} [Fintype H] [DecidableEq H]
    (R : RotationSystem H) {d : H} (h : R.rot (R.rot (R.rot d)) = d) :
    R.vertexOf d = {d, R.rot d, R.rot (R.rot d)} := by
  ext e
  rw [RotationSystem.mem_vertexOf]
  constructor
  · intro he
    obtain ⟨n, rfl⟩ := he.exists_nat_pow_eq
    clear he
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      simp only [mem_insert, mem_singleton] at ih ⊢
      rcases ih with h' | h' | h' <;> rw [h'] <;> simp [h]
  · intro he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact .refl _ _
    · exact Equiv.Perm.sameCycle_apply_right.2 (.refl _ _)
    · exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.sameCycle_apply_right.2 (.refl _ _))

/-- The lower vertex `W_t = {u_t, l_(c,t), r_(c,t)}` of the crossing `t`. -/
theorem vertexOf_cross_wordPlabicData (t : Fin p) :
    (wordPlabicData E).vertexOf (cross t) = {cross t, lLow t, rLow t} :=
  vertexOf_eq_of_rot_rot_rot _ (rot_rot_rot (cross t))

/-- The upper vertex `K_t = {ū_t, r_(c+1,t), l_(c+1,t)}` of the crossing `t`. -/
theorem vertexOf_crossBar_wordPlabicData (t : Fin p) :
    (wordPlabicData E).vertexOf (crossBar t) = {crossBar t, rUp t, lUp t} :=
  vertexOf_eq_of_rot_rot_rot _ (rot_rot_rot (crossBar t))

/-- The boundary vertex `β(j) = {e_j, g_j, ē_(j+1)}`. -/
theorem vertexOf_arc_wordPlabicData (j : Fin (2 * (n + 1))) :
    (wordPlabicData E).vertexOf (arc j) = {arc j, boundaryLeg E j, arcBar (finRotate _ j)} := by
  rw [vertexOf_eq_of_rot_rot_rot _ (rot_rot_rot (arc j))]
  simp [rot_boundaryLeg]

/-- The vertex of `r_(c,t)` is the lower vertex of the crossing `t`. -/
theorem vertexOf_rLow_wordPlabicData (t : Fin p) :
    (wordPlabicData E).vertexOf (rLow t) = (wordPlabicData E).vertexOf (cross t) :=
  ((wordPlabicData E).vertexOf_rot (lLow t)).trans ((wordPlabicData E).vertexOf_rot (cross t))

/-- The vertex of `l_(c,t)` is the lower vertex of the crossing `t`. -/
theorem vertexOf_lLow_wordPlabicData (t : Fin p) :
    (wordPlabicData E).vertexOf (lLow t) = (wordPlabicData E).vertexOf (cross t) :=
  (wordPlabicData E).vertexOf_rot (cross t)

/-- The vertex of `r_(c+1,t)` is the upper vertex of the crossing `t`. -/
theorem vertexOf_rUp_wordPlabicData (t : Fin p) :
    (wordPlabicData E).vertexOf (rUp t) = (wordPlabicData E).vertexOf (crossBar t) :=
  (wordPlabicData E).vertexOf_rot (crossBar t)

/-- The vertex of `l_(c+1,t)` is the upper vertex of the crossing `t`. -/
theorem vertexOf_lUp_wordPlabicData (t : Fin p) :
    (wordPlabicData E).vertexOf (lUp t) = (wordPlabicData E).vertexOf (crossBar t) :=
  ((wordPlabicData E).vertexOf_rot (rUp t)).trans ((wordPlabicData E).vertexOf_rot (crossBar t))

/-- The vertex of the leg `g_j` is the vertex of `e_j`. -/
theorem vertexOf_boundaryLeg_wordPlabicData (j : Fin (2 * (n + 1))) :
    (wordPlabicData E).vertexOf (boundaryLeg E j) = (wordPlabicData E).vertexOf (arc j) :=
  (wordPlabicData E).vertexOf_rot (arc j)

/-- The boundary vertex `β(j)` is the vertex of `e_j`. -/
theorem bvertex_wordPlabicData (j : Fin (2 * (n + 1))) :
    (wordPlabicData E).bvertex j = (wordPlabicData E).vertexOf (arc j) :=
  vertexOf_boundaryLeg_wordPlabicData E j

/-- The vertex of `ē_j` is the vertex of `e_(j-1)`. -/
theorem vertexOf_arcBar_wordPlabicData (j : Fin (2 * (n + 1))) :
    (wordPlabicData E).vertexOf (arcBar j) =
      (wordPlabicData E).vertexOf (arc ((finRotate _).symm j)) := by
  have h := (wordPlabicData E).vertexOf_rot (boundaryLeg E ((finRotate _).symm j))
  rw [wordPlabicData_rot_apply, rot_boundaryLeg, Equiv.apply_symm_apply] at h
  rw [h, vertexOf_boundaryLeg_wordPlabicData]

/-! #### Connectivity -/

namespace WordDart

/-- The leg `g_j` is `r_(ℓ,-∞)` or `l_(ℓ,+∞)` for some level `ℓ`. -/
theorem boundaryLeg_cases (j : Fin (2 * (n + 1))) :
    (∃ ℓ, boundaryLeg E j = rStart ℓ) ∨ ∃ ℓ, boundaryLeg E j = lEnd ℓ := by
  unfold boundaryLeg
  split_ifs
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

/-- A boundary arc `e_i` is not a leg. -/
@[simp] theorem arc_ne_boundaryLeg (i j : Fin (2 * (n + 1))) : arc i ≠ boundaryLeg E j := by
  rcases boundaryLeg_cases (E := E) j with ⟨ℓ, h⟩ | ⟨ℓ, h⟩ <;> simp [h]

/-- A boundary arc `ē_i` is not a leg. -/
@[simp] theorem arcBar_ne_boundaryLeg (i j : Fin (2 * (n + 1))) :
    arcBar i ≠ boundaryLeg E j := by
  rcases boundaryLeg_cases (E := E) j with ⟨ℓ, h⟩ | ⟨ℓ, h⟩ <;> simp [h]

/-- The dart `u_t` is not a leg. -/
@[simp] theorem cross_ne_boundaryLeg (t : Fin p) (j : Fin (2 * (n + 1))) :
    cross t ≠ boundaryLeg E j := by
  rcases boundaryLeg_cases (E := E) j with ⟨ℓ, h⟩ | ⟨ℓ, h⟩ <;> simp [h]

/-- The dart `ū_t` is not a leg. -/
@[simp] theorem crossBar_ne_boundaryLeg (t : Fin p) (j : Fin (2 * (n + 1))) :
    crossBar t ≠ boundaryLeg E j := by
  rcases boundaryLeg_cases (E := E) j with ⟨ℓ, h⟩ | ⟨ℓ, h⟩ <;> simp [h]

/-- A leg is not a boundary arc `e_i`. -/
@[simp] theorem boundaryLeg_ne_arc (i j : Fin (2 * (n + 1))) : boundaryLeg E j ≠ arc i :=
  (arc_ne_boundaryLeg (E := E) i j).symm

/-- A leg is not a boundary arc `ē_i`. -/
@[simp] theorem boundaryLeg_ne_arcBar (i j : Fin (2 * (n + 1))) : boundaryLeg E j ≠ arcBar i :=
  (arcBar_ne_boundaryLeg (E := E) i j).symm

end WordDart

/-- From `l_(ℓ,t)` the rotation reaches `r_(ℓ,t)`, in one step at the lower vertex of the crossing
`t` and in two at the upper one. -/
theorem reach_lDart_rDart_wordPlabicData {ℓ : Fin (n + 1)} {t : Fin p}
    (ht : t ∈ levelCrossings E ℓ) :
    (wordPlabicData E).Reach (lDart E ℓ t) (rDart E ℓ t) := by
  rcases mem_levelCrossings.1 ht with rfl | rfl
  · rw [lDart_castSucc, rDart_castSucc]
    exact (RotationSystem.Reach.refl _).rot
  · rw [lDart_succ, rDart_succ]
    exact (RotationSystem.Reach.refl _).rot.rot

/-- Walking along the level `ℓ` from its left end reaches every dart `r_(ℓ,t)`. -/
theorem reach_rStart_rDart_wordPlabicData (ℓ : Fin (n + 1)) :
    ∀ (k : ℕ) (t : Fin p), (t : ℕ) = k → t ∈ levelCrossings E ℓ →
      (wordPlabicData E).Reach (rStart ℓ) (rDart E ℓ t) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t htk ht
    have hpv := pv_mem (E := E) (ℓ := ℓ) (t : WithTop (Fin p))
    have hstep : (wordPlabicData E).Reach (rDart E ℓ (pv E ℓ t)) (rDart E ℓ t) := by
      have h := (RotationSystem.Reach.refl (R := (wordPlabicData E).toRotationSystem)
        (rDart E ℓ (pv E ℓ t))).inv
      have ht' : ∀ t' : Fin p, (t : WithTop (Fin p)) = t' → t' ∈ levelCrossings E ℓ :=
        fun t' h => WithTop.coe_injective h ▸ ht
      rw [wordPlabicData_inv_apply, reverse_rDart hpv, nx_pv ht'] at h
      exact h.trans (reach_lDart_rDart_wordPlabicData E ht)
    refine RotationSystem.Reach.trans ?_ hstep
    rcases prevBelow_cases (P := levelCrossings E ℓ) (t : WithTop (Fin p)) with h | ⟨t', h⟩
    · rw [show pv E ℓ t = ⊥ from h]
      exact RotationSystem.Reach.refl _
    · obtain ⟨ht', hlt, -⟩ := prevBelow_eq_coe h
      rw [show pv E ℓ t = t' from h]
      exact ih t' (by have := WithTop.coe_lt_coe.1 hlt; rw [← htk]; exact this) t' rfl ht'

/-- The boundary arcs `e_(k+1)`, `e_k` are linked through `ē_(k+1)`. -/
theorem reach_arc_arc_zero_wordPlabicData (k : ℕ) (hk : k < 2 * (n + 1)) :
    (wordPlabicData E).Reach (arc ⟨k, hk⟩) (arc ⟨0, by omega⟩) := by
  induction k with
  | zero => exact RotationSystem.Reach.refl _
  | succ k ih =>
    refine RotationSystem.Reach.trans ?_ (ih (by omega))
    have h := (RotationSystem.Reach.refl (R := (wordPlabicData E).toRotationSystem)
      (arc ⟨k + 1, hk⟩)).inv.rot
    convert h using 1
    simp only [wordPlabicData_rot_apply, wordPlabicData_inv_apply, reverse, rot_arcBar]
    congr 1
    ext
    have : NeZero (2 * (n + 1)) := ⟨by omega⟩
    rw [coe_finRotate_symm_of_ne_zero (by simp [Fin.ext_iff])]
    simp

/-- Every dart of `G(E)` is reachable from `e_1`. -/
theorem reach_arc_zero_wordPlabicData (d : WordDart E) :
    (wordPlabicData E).Reach (arc ⟨0, by omega⟩) d := by
  set G := wordPlabicData E
  have harc : ∀ j, G.Reach (arc ⟨0, by omega⟩) (arc j) := fun j =>
    (reach_arc_arc_zero_wordPlabicData E j.1 j.2).symm
  have hrStart : ∀ ℓ, G.Reach (arc ⟨0, by omega⟩) (rStart ℓ) := fun ℓ => by
    simpa [G] using (harc (legIndexR ℓ)).rot
  have hrLow : ∀ t, G.Reach (arc ⟨0, by omega⟩) (rLow t) := fun t => by
    have := (hrStart _).trans (reach_rStart_rDart_wordPlabicData E (E t).1.castSucc _ t rfl
      (mem_levelCrossings_castSucc t))
    rwa [rDart_castSucc] at this
  have hrUp : ∀ t, G.Reach (arc ⟨0, by omega⟩) (rUp t) := fun t => by
    have := (hrStart _).trans (reach_rStart_rDart_wordPlabicData E (E t).1.succ _ t rfl
      (mem_levelCrossings_succ t))
    rwa [rDart_succ] at this
  cases d with
  | arc j => exact harc j
  | arcBar j => simpa [G] using (harc j).inv
  | rStart ℓ => exact hrStart ℓ
  | lEnd ℓ => simpa [G] using (harc (legIndexL ℓ)).rot
  | rLow t => exact hrLow t
  | cross t => exact (hrLow t).rot
  | lLow t => exact (hrLow t).rot.rot
  | rUp t => exact hrUp t
  | lUp t => exact (hrUp t).rot
  | crossBar t => exact (hrUp t).rot.rot

/-- The rotation system of `G(E)` is connected. -/
theorem isConnected_wordPlabicData : (wordPlabicData E).IsConnected :=
  RotationSystem.IsConnected.of_reach ⟨arc ⟨0, by omega⟩⟩ reverse_involutive reverse_ne
    fun d e => (reach_arc_zero_wordPlabicData E d).symm.trans (reach_arc_zero_wordPlabicData E e)

/-! #### Counting vertices and edges -/

/-- The vertices of `G(E)`: the lower and upper vertices of the crossings, and the boundary
vertices. -/
theorem vertices_wordPlabicData :
    (wordPlabicData E).vertices =
      ((univ.image fun t => (wordPlabicData E).vertexOf (cross t)) ∪
        (univ.image fun t => (wordPlabicData E).vertexOf (crossBar t))) ∪
        univ.image fun j => (wordPlabicData E).vertexOf (arc j) := by
  ext v
  simp only [RotationSystem.mem_vertices, mem_union, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨d, rfl⟩
    cases d with
    | cross t => exact .inl (.inl ⟨t, rfl⟩)
    | lLow t => exact .inl (.inl ⟨t, (vertexOf_lLow_wordPlabicData E t).symm⟩)
    | rLow t => exact .inl (.inl ⟨t, (vertexOf_rLow_wordPlabicData E t).symm⟩)
    | crossBar t => exact .inl (.inr ⟨t, rfl⟩)
    | rUp t => exact .inl (.inr ⟨t, (vertexOf_rUp_wordPlabicData E t).symm⟩)
    | lUp t => exact .inl (.inr ⟨t, (vertexOf_lUp_wordPlabicData E t).symm⟩)
    | arc j => exact .inr ⟨j, rfl⟩
    | arcBar j => exact .inr ⟨_, (vertexOf_arcBar_wordPlabicData E j).symm⟩
    | rStart ℓ =>
      refine .inr ⟨legIndexR ℓ, ?_⟩
      rw [← vertexOf_boundaryLeg_wordPlabicData, boundaryLeg_legIndexR]
    | lEnd ℓ =>
      refine .inr ⟨legIndexL ℓ, ?_⟩
      rw [← vertexOf_boundaryLeg_wordPlabicData, boundaryLeg_legIndexL]
  · rintro ((⟨t, rfl⟩ | ⟨t, rfl⟩) | ⟨j, rfl⟩) <;> exact ⟨_, rfl⟩

/-- `G(E)` has `2p + 2(n + 1)` vertices. -/
theorem card_vertices_wordPlabicData :
    (wordPlabicData E).vertices.card = 2 * p + 2 * (n + 1) := by
  set G := wordPlabicData E
  have hmem : ∀ {d e : WordDart E}, G.vertexOf d = G.vertexOf e → d ∈ G.vertexOf e :=
    fun h => h ▸ G.self_mem_vertexOf _
  rw [vertices_wordPlabicData, card_union_of_disjoint, card_union_of_disjoint,
    card_image_of_injective, card_image_of_injective, card_image_of_injective]
  · simp only [card_univ, Fintype.card_fin]
    ring
  · intro i j h
    have := hmem h
    rw [vertexOf_arc_wordPlabicData] at this
    simpa using this
  · intro t t' h
    have := hmem h
    rw [vertexOf_crossBar_wordPlabicData] at this
    simpa using this
  · intro t t' h
    have := hmem h
    rw [vertexOf_cross_wordPlabicData] at this
    simpa using this
  · rw [disjoint_left]
    simp only [mem_image, mem_univ, true_and]
    rintro _ ⟨t, rfl⟩ ⟨t', h⟩
    have := hmem h.symm
    rw [vertexOf_crossBar_wordPlabicData] at this
    simp at this
  · rw [disjoint_left]
    simp only [mem_union, mem_image, mem_univ, true_and]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) ⟨j, h⟩ <;>
    · have := hmem h.symm
      rw [vertexOf_arc_wordPlabicData] at this
      simp at this

/-- The darts `r_(ℓ,-∞)`, `r_(c,t)`, `r_(c+1,t)`, `u_t` and `e_j`: one dart of each edge. -/
private def edgeRep : Fin (n + 1) ⊕ Fin p ⊕ Fin p ⊕ Fin p ⊕ Fin (2 * (n + 1)) → WordDart E :=
  Sum.elim rStart (Sum.elim rLow (Sum.elim rUp (Sum.elim cross arc)))

private theorem exists_edgeRep_eq_rDart (ℓ : Fin (n + 1)) (s : WithBot (Fin p)) :
    ∃ x, edgeRep E x = rDart E ℓ s := by
  cases s with
  | bot => exact ⟨.inl ℓ, rfl⟩
  | coe t =>
    rw [rDart_coe]
    split_ifs
    · exact ⟨.inr (.inl t), rfl⟩
    · exact ⟨.inr (.inr (.inl t)), rfl⟩

private theorem edgeRep_ne_reverse
    (x y : Fin (n + 1) ⊕ Fin p ⊕ Fin p ⊕ Fin p ⊕ Fin (2 * (n + 1))) :
    edgeRep E x ≠ (edgeRep E y).reverse := by
  intro h
  have := congrArg kind h
  rcases x with ℓ | t | t | t | j <;> rcases y with ℓ' | t' | t' | t' | j' <;>
    simp only [edgeRep, Sum.elim_inl, Sum.elim_inr, reverse, kind_lDart] at this <;>
    simp [kind] at this

/-- Reversing a dart of `G(E)` does not change its edge. -/
theorem edgeOf_reverse_wordPlabicData (d : WordDart E) :
    (wordPlabicData E).edgeOf d.reverse = (wordPlabicData E).edgeOf d := by
  change ({d.reverse, (wordPlabicData E).inv d.reverse} : Finset _) =
    {d, (wordPlabicData E).inv d}
  rw [wordPlabicData_inv_apply, wordPlabicData_inv_apply, reverse_involutive d]
  exact pair_comm _ _

private theorem edges_wordPlabicData :
    (wordPlabicData E).edges = univ.image fun x => (wordPlabicData E).edgeOf (edgeRep E x) := by
  ext e
  simp only [RotationSystem.mem_edges, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨d, rfl⟩
    have hrev := edgeOf_reverse_wordPlabicData E
    cases d with
    | rStart ℓ => exact ⟨.inl ℓ, rfl⟩
    | rLow t => exact ⟨.inr (.inl t), rfl⟩
    | rUp t => exact ⟨.inr (.inr (.inl t)), rfl⟩
    | cross t => exact ⟨.inr (.inr (.inr (.inl t))), rfl⟩
    | arc j => exact ⟨.inr (.inr (.inr (.inr j))), rfl⟩
    | crossBar t => exact ⟨.inr (.inr (.inr (.inl t))), (hrev (cross t)).symm⟩
    | arcBar j => exact ⟨.inr (.inr (.inr (.inr j))), (hrev (arc j)).symm⟩
    | lEnd ℓ =>
      obtain ⟨x, hx⟩ := exists_edgeRep_eq_rDart E ℓ (pv E ℓ ⊤)
      exact ⟨x, hx ▸ hrev (lEnd ℓ)⟩
    | lLow t =>
      obtain ⟨x, hx⟩ := exists_edgeRep_eq_rDart E (E t).1.castSucc (pv E (E t).1.castSucc t)
      exact ⟨x, hx ▸ hrev (lLow t)⟩
    | lUp t =>
      obtain ⟨x, hx⟩ := exists_edgeRep_eq_rDart E (E t).1.succ (pv E (E t).1.succ t)
      exact ⟨x, hx ▸ hrev (lUp t)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩

/-- `G(E)` has `3p + 3(n + 1)` edges. -/
theorem card_edges_wordPlabicData :
    (wordPlabicData E).edges.card = 3 * p + 3 * (n + 1) := by
  set G := wordPlabicData E
  rw [edges_wordPlabicData, card_image_of_injective, card_univ]
  · simp only [Fintype.card_sum, Fintype.card_fin]
    ring
  · intro x y h
    have h' : G.edgeOf (edgeRep E x) = G.edgeOf (edgeRep E y) := h
    have hx : edgeRep E x ∈ G.edgeOf (edgeRep E y) := h' ▸ G.mem_edgeOf.2 (.inl rfl)
    rcases G.mem_edgeOf.1 hx with hxy | hxy
    · rcases x with ℓ | t | t | t | j <;> rcases y with ℓ' | t' | t' | t' | j' <;>
        simp_all [edgeRep]
    · exact absurd hxy (edgeRep_ne_reverse E x y)


/-! #### The face labelling -/

namespace WordDart

variable {E}

/-- The **gap** `c + 1 : Fin (n + 2)` of the crossing `t` of level `c`: the gaps `g ∈ [0, n + 1]`
lie between the levels `g - 1` and `g` (the gap `0` below every level, the gap `n + 1` above), and
the crossing `t` lies in the gap between the levels `c.castSucc` and `c.succ`. -/
def gapOf (E : Fin p → Fin n × Colour) (t : Fin p) : Fin (n + 2) := (E t).1.succ.castSucc

/-- The number `c_g` of crossings in the gap `g`. -/
def gapCount (E : Fin p → Fin n × Colour) (g : Fin (n + 2)) : ℕ :=
  (univ.filter fun t => gapOf E t = g).card

/-- The number `N_g(s)` of crossings in the gap `g` at positions `≤ s`. -/
def countLE (E : Fin p → Fin n × Colour) (g : Fin (n + 2)) (s : WithBot (Fin p)) : ℕ :=
  (univ.filter fun t => gapOf E t = g ∧ (t : WithBot (Fin p)) ≤ s).card

/-- The number `N^<_g(s)` of crossings in the gap `g` at positions `< s`. -/
def countLT (E : Fin p → Fin n × Colour) (g : Fin (n + 2)) (s : WithTop (Fin p)) : ℕ :=
  (univ.filter fun t => gapOf E t = g ∧ (t : WithTop (Fin p)) < s).card

/-- The label `(ℓ - 1, N_(ℓ-1)(s))` of `r_(ℓ,s)`, in `0`-indexed levels: the chamber below the
level `ℓ` after the position `s`. -/
def labelR (E : Fin p → Fin n × Colour) (ℓ : Fin (n + 1)) (s : WithBot (Fin p)) :
    Option (Fin (n + 2) × ℕ) :=
  some (ℓ.castSucc, countLE E ℓ.castSucc s)

/-- The label `(ℓ, N^<_ℓ(s))` of `l_(ℓ,s)`, in `0`-indexed levels: the chamber above the level `ℓ`
before the position `s`. -/
def labelL (E : Fin p → Fin n × Colour) (ℓ : Fin (n + 1)) (s : WithTop (Fin p)) :
    Option (Fin (n + 2) × ℕ) :=
  some (ℓ.succ, countLT E ℓ.succ s)

/-- The **face labelling** of `G(E)`: each dart is sent to the face to its right, `none` for the
exterior and `some (g, j)` for the chamber of the gap `g` between the `j`-th and the `(j + 1)`-st
crossings of that gap: `e_j ↦ ∞`, `r_(ℓ,s) ↦ (ℓ - 1, N_(ℓ-1)(s))`, `l_(ℓ,s) ↦ (ℓ, N^<_ℓ(s))`,
`u_t ↦ (i_t, N_(i_t)(t))`, `ū_t ↦ (i_t, N^<_(i_t)(t))` and `ē_j ↦ Λ(g_j)`. -/
def faceLabel (E : Fin p → Fin n × Colour) : WordDart E → Option (Fin (n + 2) × ℕ)
  | rStart ℓ => labelR E ℓ ⊥
  | rLow t => labelR E (E t).1.castSucc t
  | rUp t => labelR E (E t).1.succ t
  | lEnd ℓ => labelL E ℓ ⊤
  | lLow t => labelL E (E t).1.castSucc t
  | lUp t => labelL E (E t).1.succ t
  | cross t => some (gapOf E t, countLE E (gapOf E t) t)
  | crossBar t => some (gapOf E t, countLT E (gapOf E t) t)
  | arc _ => none
  | arcBar j =>
    if h : (j : ℕ) < n + 1 then labelR E ⟨j, h⟩ ⊥
    else labelL E ⟨2 * (n + 1) - 1 - j, by omega⟩ ⊤

/-- The label of `r_(ℓ,s)` is `labelR E ℓ s`. -/
theorem faceLabel_rDart {ℓ : Fin (n + 1)} {s : WithBot (Fin p)}
    (hs : ∀ t : Fin p, s = t → t ∈ levelCrossings E ℓ) :
    faceLabel E (rDart E ℓ s) = labelR E ℓ s := by
  cases s with
  | bot => rfl
  | coe t =>
    rcases mem_levelCrossings.1 (hs t rfl) with rfl | rfl
    · rw [rDart_castSucc]; rfl
    · rw [rDart_succ]; rfl

/-- The label of `l_(ℓ,s)` is `labelL E ℓ s`. -/
theorem faceLabel_lDart {ℓ : Fin (n + 1)} {s : WithTop (Fin p)}
    (hs : ∀ t : Fin p, s = t → t ∈ levelCrossings E ℓ) :
    faceLabel E (lDart E ℓ s) = labelL E ℓ s := by
  cases s with
  | top => rfl
  | coe t =>
    rcases mem_levelCrossings.1 (hs t rfl) with rfl | rfl
    · rw [lDart_castSucc]; rfl
    · rw [lDart_succ]; rfl

/-- The label of `ē_j` is the label of the leg `g_j`. -/
theorem faceLabel_arcBar (j : Fin (2 * (n + 1))) :
    faceLabel E (arcBar j) = faceLabel E (boundaryLeg E j) := by
  simp only [faceLabel, boundaryLeg]
  split_ifs <;> rfl

/-- A crossing in the gap below the level `ℓ` joins `ℓ` to the level below. -/
theorem succ_eq_of_gapOf_eq_castSucc {t : Fin p} {ℓ : Fin (n + 1)}
    (h : gapOf E t = ℓ.castSucc) : (E t).1.succ = ℓ := by
  ext
  simpa [gapOf] using congrArg Fin.val h

/-- A crossing in the gap above the level `ℓ` joins `ℓ` to the level above. -/
theorem castSucc_eq_of_gapOf_eq_succ {t : Fin p} {ℓ : Fin (n + 1)}
    (h : gapOf E t = ℓ.succ) : (E t).1.castSucc = ℓ := by
  ext
  have := congrArg Fin.val h
  simp [gapOf] at this
  simp
  omega

/-- No crossing lies in the bottom gap `0`. -/
theorem gapOf_ne_zero (t : Fin p) : (gapOf E t : ℕ) ≠ 0 := by simp [gapOf]

/-- No crossing lies in the top gap `n + 1`. -/
theorem gapOf_ne_last (t : Fin p) : (gapOf E t : ℕ) ≠ n + 1 := by
  simp [gapOf]
  omega

/-- `N_g(s) ≤ c_g`. -/
theorem countLE_le (g : Fin (n + 2)) (s : WithBot (Fin p)) : countLE E g s ≤ gapCount E g :=
  card_le_card fun t ht => by simp only [mem_filter, mem_univ, true_and] at ht ⊢; exact ht.1

/-- `N^<_g(s) ≤ c_g`. -/
theorem countLT_le (g : Fin (n + 2)) (s : WithTop (Fin p)) : countLT E g s ≤ gapCount E g :=
  card_le_card fun t ht => by simp only [mem_filter, mem_univ, true_and] at ht ⊢; exact ht.1

/-- `N_g(s) = 0` when no crossing of the gap `g` is at a position `≤ s`. -/
theorem countLE_eq_zero {g : Fin (n + 2)} {s : WithBot (Fin p)}
    (h : ∀ t, gapOf E t = g → ¬(t : WithBot (Fin p)) ≤ s) : countLE E g s = 0 := by
  rw [countLE, card_eq_zero, filter_eq_empty_iff]
  exact fun t _ ht => h t ht.1 ht.2

/-- `N^<_g(s) = 0` when no crossing of the gap `g` is at a position `< s`. -/
theorem countLT_eq_zero {g : Fin (n + 2)} {s : WithTop (Fin p)}
    (h : ∀ t, gapOf E t = g → ¬(t : WithTop (Fin p)) < s) : countLT E g s = 0 := by
  rw [countLT, card_eq_zero, filter_eq_empty_iff]
  exact fun t _ ht => h t ht.1 ht.2

/-- `c_g = 0` when no crossing lies in the gap `g`. -/
theorem gapCount_eq_zero {g : Fin (n + 2)} (h : ∀ t, gapOf E t ≠ g) : gapCount E g = 0 := by
  rw [gapCount, card_eq_zero, filter_eq_empty_iff]
  exact fun t _ ht => h t ht

/-- `N_g(s) = c_g` when every crossing of the gap `g` is at a position `≤ s`. -/
theorem countLE_eq_gapCount {g : Fin (n + 2)} {s : WithBot (Fin p)}
    (h : ∀ t, gapOf E t = g → (t : WithBot (Fin p)) ≤ s) : countLE E g s = gapCount E g := by
  rw [countLE, gapCount]
  congr 1
  ext t
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', h t h'⟩⟩

/-- `N_g(-∞) = 0`. -/
@[simp] theorem countLE_bot (g : Fin (n + 2)) : countLE E g ⊥ = 0 :=
  countLE_eq_zero fun t _ => by simp

/-- `N^<_g(+∞) = c_g`. -/
@[simp] theorem countLT_top (g : Fin (n + 2)) : countLT E g ⊤ = gapCount E g := by
  rw [countLT, gapCount]
  congr 1
  ext t
  simp

/-- `N_g(s) = N_g(s')` when the crossings of the gap `g` at positions `≤ s` and `≤ s'` agree. -/
theorem countLE_congr {g : Fin (n + 2)} {s s' : WithBot (Fin p)}
    (h : ∀ t, gapOf E t = g → ((t : WithBot (Fin p)) ≤ s ↔ (t : WithBot (Fin p)) ≤ s')) :
    countLE E g s = countLE E g s' := by
  rw [countLE, countLE]
  congr 1
  ext t
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h' => ⟨h'.1, (h t h'.1).1 h'.2⟩, fun h' => ⟨h'.1, (h t h'.1).2 h'.2⟩⟩

/-- `N^<_g(s) = N^<_g(s')` when the crossings of the gap `g` at positions `< s` and `< s'` agree.
-/
theorem countLT_congr {g : Fin (n + 2)} {s s' : WithTop (Fin p)}
    (h : ∀ t, gapOf E t = g → ((t : WithTop (Fin p)) < s ↔ (t : WithTop (Fin p)) < s')) :
    countLT E g s = countLT E g s' := by
  rw [countLT, countLT]
  congr 1
  ext t
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h' => ⟨h'.1, (h t h'.1).1 h'.2⟩, fun h' => ⟨h'.1, (h t h'.1).2 h'.2⟩⟩

/-- `N_g(s) = N^<_g(s')` when the crossings of the gap `g` at positions `≤ s` are those at
positions `< s'`. -/
theorem countLE_eq_countLT {g : Fin (n + 2)} {s : WithBot (Fin p)} {s' : WithTop (Fin p)}
    (h : ∀ t, gapOf E t = g → ((t : WithBot (Fin p)) ≤ s ↔ (t : WithTop (Fin p)) < s')) :
    countLE E g s = countLT E g s' := by
  rw [countLE, countLT]
  congr 1
  ext t
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h' => ⟨h'.1, (h t h'.1).1 h'.2⟩, fun h' => ⟨h'.1, (h t h'.1).2 h'.2⟩⟩

/-- The label of the leg `g_j` at a left end `j ≤ n`: the bottom chamber `(j, 0)` of the gap
`j`. -/
theorem faceLabel_boundaryLeg_of_lt {j : Fin (2 * (n + 1))} (h : (j : ℕ) < n + 1) :
    faceLabel E (boundaryLeg E j) = some (⟨j, by omega⟩, 0) := by
  rw [boundaryLeg, dif_pos h]
  simp only [faceLabel, labelR, countLE_bot]
  rfl

/-- The label of the leg `g_j` at a right end `j ≥ n + 1`: the last chamber of the gap
`2(n + 1) - j`. -/
theorem faceLabel_boundaryLeg_of_le {j : Fin (2 * (n + 1))} (h : n + 1 ≤ (j : ℕ)) :
    faceLabel E (boundaryLeg E j) =
      some (⟨2 * (n + 1) - j, by omega⟩, gapCount E ⟨2 * (n + 1) - j, by omega⟩) := by
  rw [boundaryLeg, dif_neg (by omega)]
  simp only [faceLabel, labelL, countLT_top]
  have : (Fin.succ ⟨2 * (n + 1) - 1 - j, by omega⟩ : Fin (n + 2)) = ⟨2 * (n + 1) - j, by omega⟩ :=
    Fin.ext (by simp; omega)
  rw [this]

private theorem val_finRotate (j : Fin (2 * (n + 1))) :
    (finRotate _ j : ℕ) = ((j : ℕ) + 1) % (2 * (n + 1)) := by
  haveI : NeZero (2 * (n + 1)) := ⟨by omega⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one']
  simp [Nat.add_mod]

end WordDart

/-- If no crossing of the level `ℓ` lies above `s`, the boundary arc after the leg
`g_(legIndexL ℓ)` carries the label of `r_(ℓ,s)`. -/
theorem faceLabel_arcBar_finRotate_legIndexL {ℓ : Fin (n + 1)} {s : WithBot (Fin p)}
    (hle : ∀ t ∈ levelCrossings E ℓ, (t : WithBot (Fin p)) ≤ s) :
    faceLabel E (arcBar (finRotate _ (legIndexL ℓ))) = labelR E ℓ s := by
  have hv : ((finRotate _ (legIndexL ℓ) : Fin (2 * (n + 1))) : ℕ) =
      (2 * (n + 1) - 1 - ℓ + 1) % (2 * (n + 1)) :=
    val_finRotate _
  rw [faceLabel_arcBar]
  by_cases hℓ : (ℓ : ℕ) = 0
  · have hj : ((finRotate _ (legIndexL ℓ) : Fin (2 * (n + 1))) : ℕ) = 0 := by
      rw [hv, hℓ, show 2 * (n + 1) - 1 - 0 + 1 = 2 * (n + 1) by omega, Nat.mod_self]
    rw [faceLabel_boundaryLeg_of_lt (E := E) (by rw [hj]; omega), labelR,
      countLE_eq_zero (g := ℓ.castSucc) fun t ht => absurd (congrArg Fin.val ht)
        (by rw [Fin.val_castSucc, hℓ]; exact gapOf_ne_zero t)]
    exact congrArg some (Prod.ext (Fin.ext (by rw [Fin.val_castSucc, hℓ]; exact hj)) rfl)
  · have hj : ((finRotate _ (legIndexL ℓ) : Fin (2 * (n + 1))) : ℕ) = 2 * (n + 1) - ℓ := by
      rw [hv, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [faceLabel_boundaryLeg_of_le (E := E) (by rw [hj]; omega), labelR]
    have hg : (⟨2 * (n + 1) - ((finRotate _ (legIndexL ℓ) : Fin (2 * (n + 1))) : ℕ),
        by omega⟩ : Fin (n + 2)) = ℓ.castSucc := Fin.ext (by simp only [Fin.val_castSucc]; omega)
    rw [hg, countLE_eq_gapCount fun t ht => hle t
      (mem_levelCrossings.2 (.inr (succ_eq_of_gapOf_eq_castSucc ht)))]

/-- If no crossing of the level `ℓ` lies below `s`, the boundary arc after the leg
`g_(legIndexR ℓ)` carries the label of `l_(ℓ,s)`. -/
theorem faceLabel_arcBar_finRotate_legIndexR {ℓ : Fin (n + 1)} {s : WithTop (Fin p)}
    (hge : ∀ t ∈ levelCrossings E ℓ, s ≤ (t : WithTop (Fin p))) :
    faceLabel E (arcBar (finRotate _ (legIndexR ℓ))) = labelL E ℓ s := by
  have hv : ((finRotate _ (legIndexR ℓ) : Fin (2 * (n + 1))) : ℕ) = ℓ + 1 := by
    rw [val_finRotate]
    exact Nat.mod_eq_of_lt (by simp only [legIndexR]; omega)
  have hzero : countLT E ℓ.succ s = 0 := countLT_eq_zero fun t ht => not_lt.2
    (hge t (mem_levelCrossings.2 (.inl (castSucc_eq_of_gapOf_eq_succ ht))))
  rw [faceLabel_arcBar, labelL, hzero]
  by_cases hℓ : (ℓ : ℕ) < n
  · rw [faceLabel_boundaryLeg_of_lt (E := E) (by rw [hv]; omega)]
    exact congrArg some (Prod.ext (Fin.ext (by rw [Fin.val_succ]; exact hv)) rfl)
  · rw [faceLabel_boundaryLeg_of_le (E := E) (by rw [hv]; omega)]
    have hg : (⟨2 * (n + 1) - ((finRotate _ (legIndexR ℓ) : Fin (2 * (n + 1))) : ℕ),
        by omega⟩ : Fin (n + 2)) = ℓ.succ := Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [hg, gapCount_eq_zero fun t ht => gapOf_ne_last t (by rw [ht, Fin.val_succ]; omega)]

/-- `φ` keeps the label of `r_(ℓ,s)`. -/
theorem faceLabel_facePerm_rDart_wordPlabicData {ℓ : Fin (n + 1)} {s : WithBot (Fin p)}
    (hs : ∀ t : Fin p, s = t → t ∈ levelCrossings E ℓ) :
    faceLabel E ((wordPlabicData E).facePerm (rDart E ℓ s)) = labelR E ℓ s := by
  rw [RotationSystem.facePerm_apply, wordPlabicData_inv_apply, reverse_rDart hs,
    wordPlabicData_rot_apply]
  rcases nextAbove_cases (P := levelCrossings E ℓ) s with h | ⟨t, h⟩
  · rw [show nx E ℓ s = ⊤ from h, lDart_top]
    exact faceLabel_arcBar_finRotate_legIndexL E (nextAbove_eq_top h)
  · obtain ⟨htP, hst, hmin⟩ := nextAbove_eq_coe h
    rw [show nx E ℓ s = t from h]
    have key : ∀ t', gapOf E t' = ℓ.castSucc → ((t' : WithBot (Fin p)) ≤ s ↔ t' < t) :=
      fun t' ht' => ⟨fun hle => WithBot.coe_lt_coe.1 (hle.trans_lt hst), fun hlt => not_lt.1
        fun hgt => not_le.2 hlt
          (hmin t' (mem_levelCrossings.2 (.inr (succ_eq_of_gapOf_eq_castSucc ht'))) hgt)⟩
    rcases mem_levelCrossings.1 htP with hc | hc
    · subst hc
      rw [lDart_castSucc]
      change labelR E (E t).1.castSucc t = _
      rw [labelR, labelR, countLE_congr (s' := s) fun t' ht' => ?_]
      rw [key t' ht', WithBot.coe_le_coe]
      have hne : t' ≠ t := by
        rintro rfl
        have := congrArg Fin.val ht'
        simp [gapOf] at this
      exact ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩
    · subst hc
      rw [lDart_succ]
      change some (gapOf E t, countLT E (gapOf E t) t) = labelR E (E t).1.succ s
      rw [labelR, countLE_eq_countLT (s' := (t : WithTop (Fin p))) fun t' ht' => ?_]
      · rfl
      rw [key t' ht', WithTop.coe_lt_coe]

/-- `φ` keeps the label of `l_(ℓ,s)`. -/
theorem faceLabel_facePerm_lDart_wordPlabicData {ℓ : Fin (n + 1)} {s : WithTop (Fin p)}
    (hs : ∀ t : Fin p, s = t → t ∈ levelCrossings E ℓ) :
    faceLabel E ((wordPlabicData E).facePerm (lDart E ℓ s)) = labelL E ℓ s := by
  rw [RotationSystem.facePerm_apply, wordPlabicData_inv_apply, reverse_lDart hs,
    wordPlabicData_rot_apply]
  rcases prevBelow_cases (P := levelCrossings E ℓ) s with h | ⟨t, h⟩
  · rw [show pv E ℓ s = ⊥ from h, rDart_bot]
    exact faceLabel_arcBar_finRotate_legIndexR E (prevBelow_eq_bot h)
  · obtain ⟨htP, hts, hmax⟩ := prevBelow_eq_coe h
    rw [show pv E ℓ s = t from h]
    have key : ∀ t', gapOf E t' = ℓ.succ → ((t' : WithTop (Fin p)) < s ↔ t' ≤ t) :=
      fun t' ht' => ⟨hmax t' (mem_levelCrossings.2 (.inl (castSucc_eq_of_gapOf_eq_succ ht'))),
        fun hle => (WithTop.coe_le_coe.2 hle).trans_lt hts⟩
    rcases mem_levelCrossings.1 htP with hc | hc
    · subst hc
      rw [rDart_castSucc]
      change some (gapOf E t, countLE E (gapOf E t) t) = labelL E (E t).1.castSucc s
      rw [labelL, countLE_eq_countLT (s' := s) fun t' ht' => ?_]
      · rfl
      rw [key t' ht', WithBot.coe_le_coe]
    · subst hc
      rw [rDart_succ]
      change labelL E (E t).1.succ t = _
      rw [labelL, labelL, countLT_congr (s' := s) fun t' ht' => ?_]
      rw [key t' ht', WithTop.coe_lt_coe]
      have hne : t' ≠ t := by
        rintro rfl
        have := congrArg Fin.val ht'
        simp [gapOf] at this
      exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hne⟩

/-- The face labelling of `G(E)` is constant along the face permutation `φ`. -/
theorem faceLabel_facePerm_wordPlabicData (d : WordDart E) :
    faceLabel E ((wordPlabicData E).facePerm d) = faceLabel E d := by
  cases d with
  | rStart ℓ => exact faceLabel_facePerm_rDart_wordPlabicData E (s := ⊥) (by simp)
  | lEnd ℓ => exact faceLabel_facePerm_lDart_wordPlabicData E (s := ⊤) (by simp)
  | rLow t =>
    have := faceLabel_facePerm_rDart_wordPlabicData E (coe_mem_castSucc (E := E) t)
    rwa [rDart_castSucc] at this
  | rUp t =>
    have := faceLabel_facePerm_rDart_wordPlabicData E (coe_mem_succ (E := E) t)
    rwa [rDart_succ] at this
  | lLow t =>
    have := faceLabel_facePerm_lDart_wordPlabicData E (coe_mem_castSucc' (E := E) t)
    rwa [lDart_castSucc] at this
  | lUp t =>
    have := faceLabel_facePerm_lDart_wordPlabicData E (coe_mem_succ' (E := E) t)
    rwa [lDart_succ] at this
  | cross t => rfl
  | crossBar t => rfl
  | arc j => rfl
  | arcBar j => exact (faceLabel_arcBar j).symm


/-! #### Counting faces -/

namespace WordDart

variable {E}

/-- The set `L` of face labels of `G(E)`: `∞` (as `none`) and the chambers `(g, j)` with
`j ≤ c_g` of each gap `g`. -/
def faceLabels (E : Fin p → Fin n × Colour) : Finset (Option (Fin (n + 2) × ℕ)) :=
  insert none ((univ.sigma fun g => range (gapCount E g + 1)).image fun x => some (x.1, x.2))

/-- The labels are `∞` and the chambers `(g, k)` with `k ≤ c_g`. -/
theorem mem_faceLabels {x : Option (Fin (n + 2) × ℕ)} :
    x ∈ faceLabels E ↔ x = none ∨ ∃ g k, k ≤ gapCount E g ∧ x = some (g, k) := by
  simp only [faceLabels, mem_insert, mem_image, mem_sigma, mem_univ, true_and, mem_range,
    Sigma.exists]
  constructor <;> rintro (h | ⟨g, k, hk, rfl⟩)
  all_goals first | exact .inl h | exact .inr ⟨g, k, by omega, rfl⟩

/-- The crossings fill the gaps: `∑_g c_g = p`. -/
theorem sum_gapCount : ∑ g, gapCount E g = p := by
  have := card_eq_sum_card_fiberwise (f := gapOf E) (s := (univ : Finset (Fin p)))
    (t := univ) (fun _ _ => mem_univ _)
  rw [card_univ, Fintype.card_fin] at this
  exact this.symm

/-- There are `p + n + 3` labels. -/
theorem card_faceLabels : (faceLabels E).card = p + n + 3 := by
  rw [faceLabels, card_insert_of_notMem (by simp), card_image_of_injective, card_sigma]
  · simp only [card_range, sum_add_distrib, sum_gapCount, sum_const, card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
    ring
  · rintro ⟨g, k⟩ ⟨g', k'⟩ h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- Every dart is labelled by an element of `faceLabels E`. -/
theorem faceLabel_mem_faceLabels (d : WordDart E) : faceLabel E d ∈ faceLabels E := by
  have hR : ∀ ℓ s, labelR E ℓ s ∈ faceLabels E := fun ℓ s =>
    mem_faceLabels.2 (.inr ⟨_, _, countLE_le _ _, rfl⟩)
  have hL : ∀ ℓ s, labelL E ℓ s ∈ faceLabels E := fun ℓ s =>
    mem_faceLabels.2 (.inr ⟨_, _, countLT_le _ _, rfl⟩)
  cases d with
  | rStart ℓ => exact hR _ _
  | rLow t => exact hR _ _
  | rUp t => exact hR _ _
  | lEnd ℓ => exact hL _ _
  | lLow t => exact hL _ _
  | lUp t => exact hL _ _
  | cross t => exact mem_faceLabels.2 (.inr ⟨_, _, countLE_le _ _, rfl⟩)
  | crossBar t => exact mem_faceLabels.2 (.inr ⟨_, _, countLT_le _ _, rfl⟩)
  | arc j => exact mem_faceLabels.2 (.inl rfl)
  | arcBar j =>
    simp only [faceLabel]
    split_ifs
    · exact hR _ _
    · exact hL _ _

/-- For `1 ≤ k ≤ c_g`, the `k`-th crossing of the gap `g` has exactly `k` crossings of the gap at
or before it. -/
theorem exists_countLE_eq {g : Fin (n + 2)} {k : ℕ} (hk : 1 ≤ k) (hkc : k ≤ gapCount E g) :
    ∃ t, gapOf E t = g ∧ countLE E g t = k := by
  have hinj : ∀ t₁ t₂ (h₁ : t₁ ∈ univ.filter fun t => gapOf E t = g)
      (h₂ : t₂ ∈ univ.filter fun t => gapOf E t = g),
      countLE E g t₁ = countLE E g t₂ → t₁ = t₂ := by
    have hlt : ∀ t₁ t₂, gapOf E t₂ = g → t₁ < t₂ → countLE E g t₁ < countLE E g t₂ := by
      intro t₁ t₂ h₂ hlt
      apply card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨t₂, by simp [h₂], ?_⟩
        simp only [mem_filter, mem_univ, true_and, WithBot.coe_le_coe, not_and, not_le]
        exact fun _ => hlt
      · intro t ht
        simp only [mem_filter, mem_univ, true_and, WithBot.coe_le_coe] at ht ⊢
        exact ⟨ht.1, ht.2.trans hlt.le⟩
    intro t₁ t₂ h₁ h₂ h
    simp only [mem_filter, mem_univ, true_and] at h₁ h₂
    rcases lt_trichotomy t₁ t₂ with hl | rfl | hl
    · exact absurd h (hlt _ _ h₂ hl).ne
    · rfl
    · exact absurd h (hlt _ _ h₁ hl).ne'
  obtain ⟨t, ht, hkt⟩ := surj_on_of_inj_on_of_card_le (s := univ.filter fun t => gapOf E t = g)
    (t := Icc 1 (gapCount E g)) (fun t _ => countLE E g t)
    (fun t ht => by
      simp only [mem_filter, mem_univ, true_and] at ht
      refine mem_Icc.2 ⟨card_pos.2 ⟨t, by simp [ht]⟩, countLE_le _ _⟩)
    hinj (by rw [Nat.card_Icc]; exact (Nat.add_sub_cancel _ _).le) k (mem_Icc.2 ⟨hk, hkc⟩)
  exact ⟨t, (mem_filter.1 ht).2, hkt.symm⟩

/-- Every label is taken: `∞` by `e_1`, the bottom chamber `(g, 0)` of the gap `g ≤ n` by
`r_(g+1,-∞)`, the top gap's chamber by `l_(n+1,+∞)`, and the chamber `(g, k)` with `k ≥ 1` by
`u_t` for the `k`-th crossing `t` of the gap `g`. -/
theorem exists_faceLabel_eq {x : Option (Fin (n + 2) × ℕ)} (hx : x ∈ faceLabels E) :
    ∃ d, faceLabel E d = x := by
  rcases mem_faceLabels.1 hx with rfl | ⟨g, k, hk, rfl⟩
  · exact ⟨arc ⟨0, by omega⟩, rfl⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · by_cases hg : (g : ℕ) < n + 1
    · refine ⟨rStart ⟨g, hg⟩, ?_⟩
      simp only [faceLabel, labelR, countLE_bot]
      rfl
    · refine ⟨lEnd (Fin.last n), ?_⟩
      have hg' : (Fin.last n).succ = g := Fin.ext (by simp; omega)
      simp only [faceLabel, labelL, countLT_top, hg']
      rw [gapCount_eq_zero fun t ht => gapOf_ne_last t (by rw [ht]; omega)]
  · obtain ⟨t, ht, hkt⟩ := exists_countLE_eq (E := E) hk1 hk
    refine ⟨cross t, ?_⟩
    simp only [faceLabel, ht, hkt]

end WordDart

/-- Euler's relation for the labels: `|V| - |E| + |L| = 2`. -/
theorem euler_faceLabels :
    ((wordPlabicData E).vertices.card : ℤ) - (wordPlabicData E).edges.card +
      Fintype.card (faceLabels E) = 2 := by
  rw [card_vertices_wordPlabicData, card_edges_wordPlabicData, Fintype.card_coe, card_faceLabels]
  push_cast
  ring

/-- Two darts of `G(E)` lie on the same face exactly when they have the same chamber label. -/
theorem faceOf_eq_faceOf_iff_faceLabel_eq (d e : WordDart E) :
    (wordPlabicData E).faceOf d = (wordPlabicData E).faceOf e ↔
      faceLabel E d = faceLabel E e := by
  have := (isConnected_wordPlabicData E).faceOf_eq_faceOf_iff_of_surjective
    (lab := fun d => (⟨faceLabel E d, faceLabel_mem_faceLabels d⟩ : faceLabels E))
    (fun x => by
      obtain ⟨d, hd⟩ := exists_faceLabel_eq x.2
      exact ⟨d, Subtype.ext hd⟩)
    (fun d => Subtype.ext (faceLabel_facePerm_wordPlabicData E d)) (euler_faceLabels E) d e
  rw [this, Subtype.mk.injEq]

/-- `G(E)` has `p + n + 3` faces (orbits of `φ`): the exterior and one for each chamber. -/
theorem card_faceOrbits_wordPlabicData :
    (wordPlabicData E).faceOrbits.card = p + n + 3 := by
  have hle := (isConnected_wordPlabicData E).euler_le
  have hL := euler_faceLabels E
  have hge : Fintype.card (faceLabels E) ≤ (wordPlabicData E).faceOrbits.card := by
    have hs : Function.Surjective fun d => (⟨faceLabel E d, faceLabel_mem_faceLabels d⟩ :
        faceLabels E) := fun x => by
      obtain ⟨d, hd⟩ := exists_faceLabel_eq x.2
      exact ⟨d, Subtype.ext hd⟩
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun l => (wordPlabicData E).faceOf (Function.surjInv hs l))
      (fun l _ => RotationSystem.faceOf_mem_faceOrbits _ _) ?_
    intro l _ l' _ h
    have := (faceOf_eq_faceOf_iff_faceLabel_eq E _ _).1 h
    exact (Function.surjInv_eq hs l).symm.trans ((Subtype.ext this).trans
      (Function.surjInv_eq hs l'))
  rw [Fintype.card_coe, card_faceLabels] at hL hge
  omega

/-- The exterior face of `G(E)`, the orbit of `e_1` under `φ`, consists of the darts `e_j`. -/
theorem faceOf_arc_zero_wordPlabicData :
    (wordPlabicData E).faceOf (arc ⟨0, by omega⟩) = univ.image arc := by
  ext e
  rw [RotationSystem.mem_faceOf, ← RotationSystem.faceOf_eq_faceOf_iff,
    faceOf_eq_faceOf_iff_faceLabel_eq]
  cases e with
  | arc j => simp [faceLabel]
  | arcBar j =>
    simp only [faceLabel, mem_image, mem_univ, true_and, reduceCtorEq, exists_false, iff_false]
    split_ifs <;> simp [labelR, labelL]
  | _ => simp [faceLabel, labelR, labelL]

/-! #### The boundary vertices -/

/-- Every boundary vertex of `G(E)` is a vertex `β(j) = {e_j, g_j, ē_(j+1)}`. -/
theorem exists_eq_vertexOf_arc_of_mem_boundaryVertices_wordPlabicData {v : Finset (WordDart E)}
    (hv : v ∈ (wordPlabicData E).boundaryVertices) :
    ∃ j, v = (wordPlabicData E).vertexOf (arc j) := by
  set G := wordPlabicData E
  obtain ⟨hv, e, he, heB⟩ := G.mem_boundaryVertices.1 hv
  obtain ⟨d, rfl⟩ := G.mem_vertices.1 hv
  rw [← G.vertexOf_eq_of_mem he]
  obtain ⟨j, rfl | rfl⟩ := (mem_wordPlabicData_bdry E).1 heB
  · exact ⟨j, rfl⟩
  · exact ⟨_, vertexOf_arcBar_wordPlabicData E j⟩

/-- A leg `g_j` is not a boundary arc of `G(E)`. -/
theorem boundaryLeg_notMem_wordPlabicData_bdry (j : Fin (2 * (n + 1))) :
    boundaryLeg E j ∉ (wordPlabicData E).bdry := by
  rw [mem_wordPlabicData_bdry]
  rintro ⟨i, h | h⟩ <;> simp at h

/-- Every boundary vertex of `G(E)` has three darts, two of them boundary arcs. -/
theorem boundaryVertex_card_wordPlabicData :
    ∀ v ∈ (wordPlabicData E).boundaryVertices,
      v.card = 3 ∧ (v.filter (· ∈ (wordPlabicData E).bdry)).card = 2 := by
  intro v hv
  obtain ⟨j, rfl⟩ := exists_eq_vertexOf_arc_of_mem_boundaryVertices_wordPlabicData E hv
  rw [vertexOf_arc_wordPlabicData]
  refine ⟨card_eq_three.2 ⟨_, _, _, by simp, by simp, by simp, rfl⟩, ?_⟩
  rw [filter_insert, filter_insert, filter_singleton,
    if_pos ((mem_wordPlabicData_bdry E).2 ⟨j, .inl rfl⟩),
    if_neg (boundaryLeg_notMem_wordPlabicData_bdry E j),
    if_pos ((mem_wordPlabicData_bdry E).2 ⟨_, .inr rfl⟩)]
  exact card_pair (by simp)

/-! #### The theorem -/

/-- **`G(E)` is a plabic graph**: for a coloured word `E` on `n + 1` levels, the tuple `G(E)` is a
plabic graph with `2(n + 1)` boundary vertices. Its vertices are the lower and upper vertices of
the `p` crossings and the `2(n + 1)` boundary vertices `β(j) = {e_j, g_j, ē_(j+1)}`; it has
`3p + 3(n + 1)` edges; and its `p + n + 3` faces are the exterior `{e_j}` and the chambers. -/
@[cluster_algebras "lem_word_plabic_graph"]
theorem isPlabicGraph_wordPlabicData : (wordPlabicData E).IsPlabicGraph where
  toIsConnected := isConnected_wordPlabicData E
  inv_mem_bdry d hd := by
    obtain ⟨j, rfl | rfl⟩ := (mem_wordPlabicData_bdry E).1 hd
    · exact (mem_wordPlabicData_bdry E).2 ⟨j, .inr rfl⟩
    · exact (mem_wordPlabicData_bdry E).2 ⟨j, .inl rfl⟩
  euler := by
    rw [card_vertices_wordPlabicData, card_edges_wordPlabicData,
      card_faceOrbits_wordPlabicData]
    push_cast
    ring
  boundaryVertex_card := boundaryVertex_card_wordPlabicData E
  exists_orbit := by
    have hmap : (univ.image arc).map (wordPlabicData E).inv.toEmbedding =
        univ.image (arcBar : Fin (2 * (n + 1)) → WordDart E) := by
      rw [map_eq_image, image_image]
      rfl
    refine ⟨univ.image arc, ?_, ?_, ?_, ?_⟩
    · rw [← faceOf_arc_zero_wordPlabicData E]
      exact RotationSystem.faceOf_mem_faceOrbits _ _
    · intro d hd
      obtain ⟨j, -, rfl⟩ := mem_image.1 hd
      exact (mem_wordPlabicData_bdry E).2 ⟨j, .inl rfl⟩
    · rw [hmap]
      ext d
      rw [mem_wordPlabicData_bdry]
      cases d <;> simp
    · rw [hmap, disjoint_left]
      simp
  one_le := by omega
  colour_rot d _ := colour_rot d
  leg_notMem_bdry j := boundaryLeg_notMem_wordPlabicData_bdry E j
  bvertex_mem j := by
    rw [bvertex_wordPlabicData, DiskMap.vertexOf_mem_boundaryVertices]
    exact ⟨arc j, (wordPlabicData E).self_mem_vertexOf _,
      (mem_wordPlabicData_bdry E).2 ⟨j, .inl rfl⟩⟩
  bvertex_injective i j h := by
    rw [bvertex_wordPlabicData, bvertex_wordPlabicData] at h
    have hmem : arc i ∈ (wordPlabicData E).vertexOf (arc j) :=
      h ▸ (wordPlabicData E).self_mem_vertexOf _
    rw [vertexOf_arc_wordPlabicData] at hmem
    simpa using hmem
  exists_bvertex_eq v hv := by
    obtain ⟨j, rfl⟩ := exists_eq_vertexOf_arc_of_mem_boundaryVertices_wordPlabicData E hv
    exact ⟨j, bvertex_wordPlabicData E j⟩
  exists_exterior i := by
    refine ⟨arc (finRotate _ i), ?_, ?_, ?_⟩
    · rw [DiskMap.mem_exterior]
      exact ⟨(mem_wordPlabicData_bdry E).2 ⟨_, .inl rfl⟩,
        boundaryLeg_notMem_wordPlabicData_bdry E _⟩
    · rw [bvertex_wordPlabicData]
      exact (wordPlabicData E).self_mem_vertexOf _
    · rw [bvertex_wordPlabicData, vertexOf_arc_wordPlabicData]
      simp


end PlabicData

end ClusterAlgebras

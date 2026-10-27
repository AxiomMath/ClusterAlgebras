/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.RectanglesQuiver

/-!
# The quivers along the cyclic shift mutation sequence

The quivers met along the cyclic shift mutation sequence of the rectangles seed.

## Implementation notes

* Rows and columns are `0`-based, `c = b - a`.
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### The states of the sequence -/

/-- `(p, q)` is a mutable rectangle of `Q_{a,b}`: `p + 2 ≤ a` and `q + 2 ≤ b - a`. -/
def CsMut (a b p q : ℕ) : Prop := p + 2 ≤ a ∧ q + 2 ≤ b - a

/-- The mutable rectangles already mutated when the next vertex of the sequence is `(R, Q₀)`:
the rows below `R`, and the first `Q₀` rectangles of row `R`. -/
def CsDone (a b R Q₀ p q : ℕ) : Prop :=
  p + 2 ≤ a ∧ q + 2 ≤ b - a ∧ (R < p ∨ (p = R ∧ q < Q₀))

/-- The arrows between two mutable rectangles, given the set `M` of mutated rectangles. -/
def csArrowMM (M : ℕ → ℕ → Prop) (p q p' q' : ℕ) : Prop :=
  (p' = p ∧ q' = q + 1 ∧ (M p q ∧ M p' q' ∨ ¬M p q ∧ ¬M p' q')) ∨
  (p' = p ∧ q' + 1 = q ∧ ¬M p q ∧ M p' q') ∨
  (p' = p + 1 ∧ q' = q ∧ (M p q ∧ M p' q' ∨ ¬M p q ∧ ¬M p' q')) ∨
  (p' = p + 1 ∧ q' + 1 = q ∧ ¬M p q ∧ M p' q' ∧ ¬M p q' ∧ M p' q) ∨
  (p' + 1 = p ∧ q' + 1 = q ∧
    (¬M p q ∧ ¬M p' q' ∧ ¬M p q' ∨ M p q ∧ M p' q' ∧ M p' q)) ∨
  (p' + 1 = p ∧ q' = q ∧ M p q ∧ ¬M p' q')

/-- The arrows from a mutable rectangle `(p, q)` to a frozen rectangle `(f, g)`. -/
def csArrowMF (a c : ℕ) (M : ℕ → ℕ → Prop) (p q f g : ℕ) : Prop :=
  (f + 2 ≤ a ∧ g + 1 = c ∧
    (p = f ∧ q + 2 = c ∧ ¬M p q ∨ p = f + 1 ∧ q + 2 = c ∧ M f q)) ∨
  (f + 1 = a ∧
    (p + 2 = a ∧ q + 1 = g ∧ M p q ∨
     p + 2 = a ∧ q = g ∧ 1 ≤ q ∧ ¬M p q ∧ ¬M p (q - 1) ∨
     q = 0 ∧ g = 0 ∧ ¬M p 0 ∧ (p + 2 = a ∨ M (p + 1) 0)))

/-- The arrows from a frozen rectangle `(f, g)` to a mutable rectangle `(p, q)`. -/
def csArrowFM (a c : ℕ) (M : ℕ → ℕ → Prop) (f g p q : ℕ) : Prop :=
  (f + 2 ≤ a ∧ g + 1 = c ∧
    (f = p + 1 ∧ q + 2 = c ∧ ¬M f q ∨ f = p ∧ q + 2 = c ∧ M p q)) ∨
  (f + 1 = a ∧
    (p + 2 = a ∧ g = q + 1 ∧ ¬M p q ∨
     p + 2 = a ∧ g = q + 2 ∧ M p (q + 1) ∨
     q = 0 ∧ g = 0 ∧ M p 0 ∧ (p = 0 ∨ ¬M (p - 1) 0)))

/-- The arrows of the quiver reached along the cyclic shift sequence once the rectangles of `M`
are mutated. -/
def csArrow (a b : ℕ) (M : ℕ → ℕ → Prop) : RectVertex a b → RectVertex a b → Prop
  | none, none => False
  | none, some (p, q) => CsMut a b p q ∧ (p : ℕ) = 0 ∧ ¬M 0 q ∧ ((q : ℕ) = 0 ∨ M 0 (q - 1))
  | some (p, q), none =>
      CsMut a b p q ∧ (p : ℕ) = 0 ∧ M 0 q ∧ ((q : ℕ) + 2 = b - a ∨ ¬M 0 (q + 1))
  | some (p, q), some (p', q') =>
      CsMut a b p q ∧ CsMut a b p' q' ∧ csArrowMM M p q p' q' ∨
      CsMut a b p q ∧ ¬CsMut a b p' q' ∧ csArrowMF a (b - a) M p q p' q' ∨
      ¬CsMut a b p q ∧ CsMut a b p' q' ∧ csArrowFM a (b - a) M p q p' q'

/-- A vertex of `Q_{a,b}` is mutable. -/
def CsMutV (a b : ℕ) : RectVertex a b → Prop
  | none => False
  | some (p, q) => CsMut a b p q

/-- The in-neighbours of `(R, Q₀)` when it is mutated. -/
def CsInNbr (a b R Q₀ : ℕ) : RectVertex a b → Prop
  | none => R = 0
  | some (p, q) => ((p : ℕ) + 1 = R ∧ (q : ℕ) = Q₀) ∨
      ((p : ℕ) = R + 1 ∧ (R + 2 < a ∧ (q : ℕ) = Q₀ ∨ R + 2 = a ∧ (q : ℕ) = Q₀ + 1))

/-- The out-neighbours of `(R, Q₀)` when it is mutated. -/
def CsOutNbr (a b R Q₀ : ℕ) : RectVertex a b → Prop
  | none => False
  | some (p, q) => ((p : ℕ) = R ∧ (q : ℕ) = Q₀ + 1) ∨
      (Q₀ = 0 ∧ (p : ℕ) + 1 = a ∧ (q : ℕ) = 0) ∨ (0 < Q₀ ∧ (p : ℕ) = R ∧ (q : ℕ) + 1 = Q₀)

section Step

variable {a b : ℕ}

/-- A rectangle is mutable, on the right edge, or on the bottom edge. -/
theorem csMut_or {p q : ℕ} (hp : p < a) (hq : q < b - a) :
    CsMut a b p q ∨ (p + 2 ≤ a ∧ q + 1 = b - a) ∨ p + 1 = a := by
  unfold CsMut
  omega

/-- Closes a goal about the arrows between two vertices `u`, `v` of `Q_{a,b}`: splits each into
the empty rectangle, the mutable rectangles, the right edge and the bottom edge, splits a pair of
mutable rectangles according to their relative position, and calls `grind`. -/
local macro "cs_pair_crunch" u:ident v:ident : tactic =>
  `(tactic| (
    rcases $u:ident with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ <;> rcases $v:ident with _ | ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩
    · simp_all [csArrow, CsMutV, CsInNbr, CsOutNbr]
    · (try simp only [csArrow, CsDone, CsMut, CsInNbr, CsOutNbr, CsMutV, Option.some.injEq,
        Prod.mk.injEq, Fin.mk.injEq, ne_eq, reduceCtorEq, not_false_eq_true] at *) <;>
      grind (splits := 40)
    · (try simp only [csArrow, CsDone, CsMut, CsInNbr, CsOutNbr, CsMutV, Option.some.injEq,
        Prod.mk.injEq, Fin.mk.injEq, ne_eq, reduceCtorEq, not_false_eq_true] at *) <;>
      grind (splits := 40)
    · try simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq, ne_eq] at *
      try simp only [csArrow, CsInNbr, CsOutNbr, CsMutV] at *
      rcases csMut_or hp hq with hmu | ⟨hf1, hf2⟩ | hf <;>
      rcases csMut_or hp' hq' with hmv | ⟨hg1, hg2⟩ | hg
      · have hmu' := hmu
        have hmv' := hmv
        unfold CsMut at hmu' hmv'
        simp only [hmu, hmv, true_and, not_true_eq_false, false_and, or_false]
        rcases (show p' = p ∨ p' = p + 1 ∨ p' + 1 = p ∨ (p' ≠ p ∧ p' ≠ p + 1 ∧ p' + 1 ≠ p) by
            omega) with rfl | rfl | rfl | ⟨h1, h2, h3⟩ <;>
        rcases (show q' = q ∨ q' = q + 1 ∨ q' + 1 = q ∨
            (q' ≠ q ∧ q' ≠ q + 1 ∧ q' + 1 ≠ q) by omega)
          with rfl | rfl | rfl | ⟨g1, g2, g3⟩ <;>
        simp_all only [csArrowMM, csArrowMF, csArrowFM, CsMut, CsDone, ne_eq, add_eq_left,
          left_eq_add, one_ne_zero, false_and, and_false, false_or, or_false, true_and, and_true,
          add_left_inj, Nat.add_right_cancel_iff, not_false_eq_true, Nat.succ_ne_self,
          OfNat.ofNat_ne_zero] <;>
        grind (splits := 40)
      all_goals
        first
        | (have hnu : ¬CsMut a b p q := by unfold CsMut; omega
           have hnv : ¬CsMut a b p' q' := by unfold CsMut; omega
           simp_all [CsMutV])
        | (have hmu' : p + 2 ≤ a ∧ q + 2 ≤ b - a := hmu
           have hnv : ¬CsMut a b p' q' := by unfold CsMut; omega
           simp only [hmu, hnv, true_and, not_true_eq_false, false_and, or_false, false_or,
             not_false_eq_true, and_true] at *
           simp only [csArrowMF, csArrowFM, CsDone] at *
           grind (splits := 40))
        | (have hmv' : p' + 2 ≤ a ∧ q' + 2 ≤ b - a := hmv
           have hnu : ¬CsMut a b p q := by unfold CsMut; omega
           simp only [hmv, hnu, true_and, not_true_eq_false, false_and, or_false, false_or,
             not_false_eq_true, and_true] at *
           simp only [csArrowMF, csArrowFM, CsDone] at *
           grind (splits := 40))))

/-- Closes a goal about the arrows between a vertex `u` and a fixed mutable rectangle. -/
local macro "cs_vertex_crunch" u:ident : tactic =>
  `(tactic| (
    rcases $u:ident with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    · simp only [csArrow, CsDone, CsMut, CsInNbr, CsOutNbr] at *
      grind (splits := 40)
    · rcases csMut_or hp hq with hmu | ⟨hf1, hf2⟩ | hf
      · have hmu' := hmu
        unfold CsMut at hmu'
        simp only [csArrow, csArrowMM, csArrowMF, csArrowFM, CsDone, CsMut, CsInNbr, CsOutNbr,
          Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq] at *
        grind (splits := 40)
      all_goals
        simp only [csArrow, csArrowMM, csArrowMF, csArrowFM, CsDone, CsMut, CsInNbr, CsOutNbr,
          Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq] at *
        grind (splits := 40)))

set_option maxHeartbeats 4000000 in
-- a case analysis on the positions of the vertices
/-- **The quiver mutation at `(r, s)`**, away from `(r, s)`: the arrows from the in-neighbours to
the out-neighbours are added, those from the out-neighbours to the in-neighbours removed. -/
theorem csArrow_step (r : Fin a) (s : Fin (b - a)) (hr : (r : ℕ) + 2 ≤ a)
    (hs : (s : ℕ) + 2 ≤ b - a) (u v : RectVertex a b) (hu : u ≠ some (r, s))
    (hv : v ≠ some (r, s)) (huv : CsMutV a b u ∨ CsMutV a b v) :
    csArrow a b (CsDone a b r (s + 1)) u v ↔
      (csArrow a b (CsDone a b r s) u v ∧ ¬(CsOutNbr a b r s u ∧ CsInNbr a b r s v)) ∨
        (CsInNbr a b r s u ∧ CsOutNbr a b r s v ∧ ¬csArrow a b (CsDone a b r s) v u) := by
  obtain ⟨R, hR⟩ := r
  obtain ⟨Q₀, hQ⟩ := s
  simp only at hr hs ⊢
  cs_pair_crunch u v

set_option maxHeartbeats 4000000 in
-- a case analysis on the positions of the vertices
/-- The quiver of every state of the sequence has no two-cycle. -/
theorem not_csArrow_and_csArrow (R Q₀ : ℕ) (hR : R + 2 ≤ a) (hQ : Q₀ + 2 ≤ b - a)
    (u v : RectVertex a b) :
    ¬(csArrow a b (CsDone a b R Q₀) u v ∧ csArrow a b (CsDone a b R Q₀) v u) := by
  cs_pair_crunch u v

set_option maxHeartbeats 4000000 in
-- a case analysis on the positions of the vertices
/-- There is no arrow from an in-neighbour of `(R, Q₀)` to an out-neighbour. -/
theorem not_csArrow_of_csInNbr_of_csOutNbr (R Q₀ : ℕ) (hR : R + 2 ≤ a)
    (hQ : Q₀ + 2 ≤ b - a) (u v : RectVertex a b) (hu : CsInNbr a b R Q₀ u)
    (hv : CsOutNbr a b R Q₀ v) : ¬csArrow a b (CsDone a b R Q₀) u v := by
  cs_pair_crunch u v

set_option maxHeartbeats 2000000 in
-- a case analysis on the positions of the vertices
/-- Before the mutation at `(r, s)`, there is an arrow `u → (r, s)` iff `u` is in `CsInNbr`. -/
theorem csArrow_to_center (r : Fin a) (s : Fin (b - a)) (hr : (r : ℕ) + 2 ≤ a)
    (hs : (s : ℕ) + 2 ≤ b - a) (u : RectVertex a b) :
    csArrow a b (CsDone a b r s) u (some (r, s)) ↔ CsInNbr a b r s u := by
  obtain ⟨R, hR⟩ := r
  obtain ⟨Q₀, hQ⟩ := s
  simp only at hr hs ⊢
  cs_vertex_crunch u

set_option maxHeartbeats 2000000 in
-- a case analysis on the positions of the vertices
/-- Before the mutation at `(r, s)`, there is an arrow `(r, s) → v` iff `v` is in `CsOutNbr`. -/
theorem csArrow_from_center (r : Fin a) (s : Fin (b - a)) (hr : (r : ℕ) + 2 ≤ a)
    (hs : (s : ℕ) + 2 ≤ b - a) (v : RectVertex a b) :
    csArrow a b (CsDone a b r s) (some (r, s)) v ↔ CsOutNbr a b r s v := by
  obtain ⟨R, hR⟩ := r
  obtain ⟨Q₀, hQ⟩ := s
  simp only at hr hs ⊢
  cs_vertex_crunch v

set_option maxHeartbeats 2000000 in
-- a case analysis on the positions of the vertices
/-- After the mutation at `(r, s)`, its in-neighbours are its former out-neighbours. -/
theorem csArrow_succ_to_center (r : Fin a) (s : Fin (b - a)) (hr : (r : ℕ) + 2 ≤ a)
    (hs : (s : ℕ) + 2 ≤ b - a) (u : RectVertex a b) :
    csArrow a b (CsDone a b r (s + 1)) u (some (r, s)) ↔ CsOutNbr a b r s u := by
  obtain ⟨R, hR⟩ := r
  obtain ⟨Q₀, hQ⟩ := s
  simp only at hr hs ⊢
  cs_vertex_crunch u

set_option maxHeartbeats 2000000 in
-- a case analysis on the positions of the vertices
/-- After the mutation at `(r, s)`, its out-neighbours are its former in-neighbours. -/
theorem csArrow_succ_from_center (r : Fin a) (s : Fin (b - a)) (hr : (r : ℕ) + 2 ≤ a)
    (hs : (s : ℕ) + 2 ≤ b - a) (v : RectVertex a b) :
    csArrow a b (CsDone a b r (s + 1)) (some (r, s)) v ↔ CsInNbr a b r s v := by
  obtain ⟨R, hR⟩ := r
  obtain ⟨Q₀, hQ⟩ := s
  simp only at hr hs ⊢
  cs_vertex_crunch v

/-- No vertex is both an in- and an out-neighbour of `(R, Q₀)`. -/
theorem not_csInNbr_and_csOutNbr (R Q₀ : ℕ) (hR : R + 2 ≤ a) (u : RectVertex a b) :
    ¬(CsInNbr a b R Q₀ u ∧ CsOutNbr a b R Q₀ u) := by
  rcases u with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ <;> simp only [CsInNbr, CsOutNbr] <;> grind

/-- The states at the end of a row and at the start of the next one coincide. -/
theorem csDone_end_row (R : ℕ) (hR : 1 ≤ R) :
    CsDone a b R (b - a - 1) = CsDone a b (R - 1) 0 := by
  funext p q
  simp only [CsDone, eq_iff_iff]
  omega

/-- In the first state nothing is mutated. -/
theorem not_csDone_start (p q : ℕ) : ¬CsDone a b (a - 2) 0 p q := by
  simp only [CsDone]
  omega

/-! ### The first and the last state -/

/-- The **boundary rotation** `σ` of `V_{a,b}`: it fixes the mutable rectangles and moves the
frozen ones one step along the boundary, `∅ ↦ (0, c - 1)`, `(p, c - 1) ↦ (p + 1, c - 1)`,
`(a - 1, q) ↦ (a - 1, q - 1)` for `q > 0`, and `(a - 1, 0) ↦ ∅`. -/
def csRot (a b : ℕ) : RectVertex a b → RectVertex a b
  | none => if h : 0 < a ∧ 0 < b - a then some (⟨0, h.1⟩, ⟨b - a - 1, by omega⟩) else none
  | some (p, q) =>
      if h : (q : ℕ) + 1 = b - a ∧ (p : ℕ) + 1 < a then some (⟨p + 1, h.2⟩, q)
      else if h' : (p : ℕ) + 1 = a ∧ 0 < (q : ℕ) then some (p, ⟨q - 1, by omega⟩)
      else if (p : ℕ) + 1 = a ∧ (q : ℕ) = 0 then none
      else some (p, q)

/-- `σ(∅) = (0, c - 1)`. -/
theorem csRot_none (ha : 0 < a) (hc : 0 < b - a) :
    csRot a b none = some (⟨0, ha⟩, ⟨b - a - 1, by omega⟩) := by
  simp [csRot, ha, hc]

/-- The value of `σ` on a rectangle, according to its position. -/
theorem csRot_some_cases (p : Fin a) (q : Fin (b - a)) :
    (CsMut a b p q ∧ csRot a b (some (p, q)) = some (p, q)) ∨
    (∃ h : (p : ℕ) + 1 < a, (p : ℕ) + 2 ≤ a ∧ (q : ℕ) + 1 = b - a ∧
      csRot a b (some (p, q)) = some (⟨p + 1, h⟩, q)) ∨
    (∃ h : 0 < (q : ℕ), (p : ℕ) + 1 = a ∧
      csRot a b (some (p, q)) = some (p, ⟨q - 1, by omega⟩)) ∨
    ((p : ℕ) + 1 = a ∧ (q : ℕ) = 0 ∧ csRot a b (some (p, q)) = none) := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp only [csRot, CsMut]
  by_cases h1 : q + 1 = b - a ∧ p + 1 < a
  · exact Or.inr (Or.inl ⟨h1.2, by omega, h1.1, by simp [h1]⟩)
  by_cases h2 : p + 1 = a ∧ 0 < q
  · exact Or.inr (Or.inr (Or.inl ⟨h2.2, h2.1, by simp [h2]⟩))
  by_cases h3 : p + 1 = a ∧ q = 0
  · exact Or.inr (Or.inr (Or.inr ⟨h3.1, h3.2, by simp [h3]⟩))
  · exact Or.inl ⟨by omega, by simp [h1, h2, h3]⟩

/-- `σ` fixes the mutable rectangles. -/
theorem csRot_of_csMutV {v : RectVertex a b} (hv : CsMutV a b v) : csRot a b v = v := by
  rcases v with _ | ⟨p, q⟩
  · exact hv.elim
  · rcases csRot_some_cases p q with ⟨hm, h⟩ | ⟨hw, h1, h2, h⟩ | ⟨hw, h1, h⟩ | ⟨h1, h2, h⟩
    · exact h
    all_goals simp only [CsMutV, CsMut] at *; omega

/-- `σ` preserves the frozen vertices. -/
theorem rectFrozen_csRot_iff (ha : 2 ≤ a) (hc : 2 ≤ b - a) (v : RectVertex a b) :
    RectFrozen a b (csRot a b v) ↔ RectFrozen a b v := by
  rcases v with _ | ⟨p, q⟩
  · rw [csRot_none (by omega) (by omega)]
    simp only [RectFrozen]
    grind
  · rcases csRot_some_cases p q with ⟨hm, h⟩ | ⟨hw, h1, h2, h⟩ | ⟨hw, h1, h⟩ | ⟨h1, h2, h⟩ <;>
      rw [h] <;> simp only [RectFrozen] at * <;> grind

/-- `σ` is injective. -/
theorem csRot_injective (ha : 2 ≤ a) (hc : 2 ≤ b - a) : Function.Injective (csRot a b) := by
  intro v w hvw
  rcases v with _ | ⟨p, q⟩ <;> rcases w with _ | ⟨p', q'⟩
  · rfl
  · rw [csRot_none (by omega) (by omega)] at hvw
    rcases csRot_some_cases p' q' with ⟨hm, h⟩ | ⟨hw, h1, h2, h⟩ | ⟨hw, h1, h⟩ | ⟨h1, h2, h⟩ <;>
      rw [h] at hvw <;> simp only [Option.some.injEq, Prod.mk.injEq, Fin.ext_iff,
        reduceCtorEq, CsMut] at * <;> grind
  · rw [csRot_none (by omega) (by omega)] at hvw
    rcases csRot_some_cases p q with ⟨hm, h⟩ | ⟨hw, h1, h2, h⟩ | ⟨hw, h1, h⟩ | ⟨h1, h2, h⟩ <;>
      rw [h] at hvw <;> simp only [Option.some.injEq, Prod.mk.injEq, Fin.ext_iff,
        reduceCtorEq, CsMut] at * <;> grind
  · rcases csRot_some_cases p q with ⟨hm, h⟩ | ⟨hw, h1, h2, h⟩ | ⟨hw, h1, h⟩ | ⟨h1, h1', h⟩ <;>
    rcases csRot_some_cases p' q' with ⟨hm', h'⟩ | ⟨hw', h4, h2', h'⟩ | ⟨hw', h4, h'⟩ |
      ⟨h3, h3', h'⟩ <;>
    rw [h, h'] at hvw <;>
    simp only [Option.some.injEq, Prod.mk.injEq, Fin.ext_iff, reduceCtorEq, CsMut] at * <;>
    omega

set_option maxHeartbeats 4000000 in
-- a case analysis on the positions of the vertices
/-- **The first state is the rectangles quiver**: before any mutation, the arrows are those of
`Q_{a,b}`. -/
theorem csArrow_start_iff (u v : RectVertex a b) :
    csArrow a b (CsDone a b (a - 2) 0) u v ↔
      ¬(RectFrozen a b u ∧ RectFrozen a b v) ∧ RectStep a b u v := by
  have h0 : CsDone a b (a - 2) 0 = fun _ _ => False := by
    funext p q; simp only [eq_iff_iff, iff_false]; exact not_csDone_start p q
  rw [h0]
  rcases u with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ <;> rcases v with _ | ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩
  · simp [csArrow, RectStep]
  · simp only [csArrow, CsMut, RectFrozen, RectStep]
    grind
  · simp only [csArrow, CsMut, RectFrozen, RectStep]
    grind
  · simp only [csArrow, CsMut, RectFrozen, RectStep, csArrowMM, csArrowMF, csArrowFM,
      not_false_eq_true, and_true, true_and, and_false, false_and, or_false, false_or]
    grind (splits := 40)

set_option maxHeartbeats 8000000 in
-- a case analysis on the positions of the vertices
/-- **The last state is the rectangles quiver rotated**: once every mutable rectangle is mutated,
the arrows are those of `Q_{a,b}` read through the boundary rotation `σ`. -/
theorem csArrow_end_iff (ha : 2 ≤ a) (hc : 2 ≤ b - a) (u v : RectVertex a b) :
    csArrow a b (CsDone a b 0 (b - a - 1)) u v ↔
      ¬(RectFrozen a b (csRot a b u) ∧ RectFrozen a b (csRot a b v)) ∧
        RectStep a b (csRot a b u) (csRot a b v) := by
  have h0 : CsDone a b 0 (b - a - 1) = fun p q => p + 2 ≤ a ∧ q + 2 ≤ b - a := by
    funext p q; simp only [CsDone, eq_iff_iff]; omega
  rw [h0]
  rcases u with _ | ⟨p, q⟩ <;> rcases v with _ | ⟨p', q'⟩
  · simp [csArrow, csRot_none (by omega : 0 < a) (by omega : 0 < b - a), RectStep]
  · rw [csRot_none (by omega) (by omega)]
    rcases csRot_some_cases p' q' with ⟨hm, h⟩ | ⟨h0, hm1, hm2, h⟩ | ⟨h0, hm, h⟩ |
      ⟨hm1, hm2, h⟩ <;> rw [h] <;>
    simp only [csArrow, CsMut, RectFrozen, RectStep] at * <;> grind
  · rw [csRot_none (by omega) (by omega)]
    rcases csRot_some_cases p q with ⟨hm, h⟩ | ⟨h0, hm1, hm2, h⟩ | ⟨h0, hm, h⟩ |
      ⟨hm1, hm2, h⟩ <;> rw [h] <;>
    simp only [csArrow, CsMut, RectFrozen, RectStep] at * <;> grind
  · obtain ⟨p, hp⟩ := p
    obtain ⟨q, hq⟩ := q
    obtain ⟨p', hp'⟩ := p'
    obtain ⟨q', hq'⟩ := q'
    rcases csRot_some_cases ⟨p, hp⟩ ⟨q, hq⟩ with ⟨hm, h⟩ | ⟨h0, hm1, hm2, h⟩ | ⟨h0, hm, h⟩ |
      ⟨hm1, hm2, h⟩ <;>
    rcases csRot_some_cases ⟨p', hp'⟩ ⟨q', hq'⟩ with ⟨hm', h'⟩ | ⟨h0', hm1', hm2', h'⟩ |
      ⟨h0', hm', h'⟩ | ⟨hm1', hm2', h'⟩ <;>
    rw [h, h'] <;>
    simp only [csArrow, CsMut, RectFrozen, RectStep, csArrowMM, csArrowMF, csArrowFM] at * <;>
    grind (splits := 40)

end Step

end ClusterAlgebras

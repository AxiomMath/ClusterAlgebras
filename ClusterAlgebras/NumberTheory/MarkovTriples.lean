/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

/-!
# Markov triples and Markov moves

A *Markov triple* is a triple `(a₁, a₂, a₃)` of positive integers with
`a₁² + a₂² + a₃² = 3 a₁ a₂ a₃`. For `k ∈ {1, 2, 3}` the *Markov move* `ν_k` replaces `a_k` by
`(a_i² + a_j²) / a_k`, where `{i, j} = {1, 2, 3} ∖ {k}`; for a finite sequence
`s = (k₁, …, k_d)` the move along `s` is `ν_s(a) = ν_{k_d}(⋯ ν_{k₁}(a) ⋯)`.

On a Markov triple, `ν_k` is Vieta jumping: the new entry is the other root `3 a_i a_j - a_k`
of the quadratic `X² - 3 a_i a_j X + a_i² + a_j²`, so `ν_k` sends Markov triples to Markov
triples, and every triple reached from `(1, 1, 1)` is a Markov triple. Conversely, moving at a
largest entry of a Markov triple other than `(1, 1, 1)` strictly decreases that entry, and
since `ν_k` is an involution, descent on the entry sum shows that every Markov triple is
reached from `(1, 1, 1)`.

FWZ index triples by `{1, 2, 3}`; here they are functions on `Fin 3`, so FWZ's index
`i` is Lean index `i - 1`, and the complement `{i, j}` of `k` is `{k + 1, k + 2}`, computed in
`Fin 3`.

## Main definitions

* `ClusterAlgebras.IsMarkovTriple`: the predicate of being a Markov triple.
* `ClusterAlgebras.markovMove`: the Markov move `ν_k`.
* `ClusterAlgebras.markovMoveSeq`: the Markov move `ν_s` along a finite sequence `s`.

## Main results

* `ClusterAlgebras.IsMarkovTriple.markovMove`: Vieta jumping, `ν_k` preserves Markov triples.
* `ClusterAlgebras.isMarkovTriple_markovMoveSeq_one`: every `ν_s(1, 1, 1)` is a Markov triple.
* `ClusterAlgebras.IsMarkovTriple.markovMove_lt`: descent at a largest entry.
* `ClusterAlgebras.IsMarkovTriple.exists_markovMoveSeq_eq`: every Markov triple is
  `ν_s(1, 1, 1)` for some `s`.

## Implementation notes

FWZ define `ν_k` on triples of positive rationals. Here `markovMove` is the total
function on all of `ℚ³` given by the same formula, with Lean's convention `x / 0 = 0`; on
positive triples it is FWZ's move. A sequence `s = (k₁, …, k_d)` is the list
`[k₁, …, k_d]`, and `ν_s` is the left fold, which applies `ν_{k₁}` first.

Statements about the moves of an integer triple `a : Fin 3 → ℕ` are made through its cast
`fun i => (a i : ℚ)`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*,
  Chapter 3.
-/

@[expose] public section

namespace ClusterAlgebras

/-- In `Fin 3`, `k + 1 ≠ k`. -/
private lemma fin_three_add_one_ne (k : Fin 3) : k + 1 ≠ k := by
  fin_cases k <;> decide

/-- In `Fin 3`, `k + 2 ≠ k`. -/
private lemma fin_three_add_two_ne (k : Fin 3) : k + 2 ≠ k := by
  fin_cases k <;> decide

/-! ### Markov triples -/

/-- A **Markov triple** is a triple `(a₁, a₂, a₃)` of positive integers with
`a₁² + a₂² + a₃² = 3 a₁ a₂ a₃`. -/
@[cluster_algebras "def_markov_triple"]
structure IsMarkovTriple (a : Fin 3 → ℕ) : Prop where
  /-- The entries of a Markov triple are positive. -/
  pos : ∀ i, 0 < a i
  /-- The Markov equation. -/
  eq : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 3 * a 0 * a 1 * a 2

/-- `(1, 1, 1)` is a Markov triple. -/
theorem isMarkovTriple_one : IsMarkovTriple 1 :=
  ⟨fun _ => Nat.one_pos, by simp⟩

namespace IsMarkovTriple

variable {a : Fin 3 → ℕ}

/-- The Markov equation, read starting from any index `k`. -/
theorem eq_rotate (h : IsMarkovTriple a) (k : Fin 3) :
    a k ^ 2 + a (k + 1) ^ 2 + a (k + 2) ^ 2 = 3 * a k * a (k + 1) * a (k + 2) := by
  fin_cases k <;> simp <;> linear_combination h.eq

/-- A triple of positive integers satisfying the Markov equation read starting from some index
`k` is a Markov triple. -/
theorem of_eq_rotate (hpos : ∀ i, 0 < a i) (k : Fin 3)
    (h : a k ^ 2 + a (k + 1) ^ 2 + a (k + 2) ^ 2 = 3 * a k * a (k + 1) * a (k + 2)) :
    IsMarkovTriple a := by
  refine ⟨hpos, ?_⟩
  fin_cases k <;> simp at h <;> linear_combination h

end IsMarkovTriple

/-! ### Markov moves -/

/-- The **Markov move** `ν_k`: replace the `k`-th entry `a_k` of the triple `a` by
`(a_i² + a_j²) / a_k`, where `{i, j} = {k + 1, k + 2}` is the complement of `k` in `Fin 3`.

FWZ define it on triples of positive rationals; this is the same formula on all of
`ℚ³`, with `x / 0 = 0`. -/
@[cluster_algebras "def_markov_move"]
def markovMove (a : Fin 3 → ℚ) (k : Fin 3) : Fin 3 → ℚ :=
  Function.update a k ((a (k + 1) ^ 2 + a (k + 2) ^ 2) / a k)

/-- The **Markov move along a sequence** `s = [k₁, …, k_d]`:
`ν_s(a) = ν_{k_d}(⋯ ν_{k₁}(a) ⋯)`, and `ν_s(a) = a` for the empty sequence. -/
@[cluster_algebras "def_markov_move"]
def markovMoveSeq (a : Fin 3 → ℚ) (s : List (Fin 3)) : Fin 3 → ℚ :=
  s.foldl markovMove a

/-- The new `k`-th entry of `ν_k(a)`. -/
@[simp]
theorem markovMove_apply_self (a : Fin 3 → ℚ) (k : Fin 3) :
    markovMove a k k = (a (k + 1) ^ 2 + a (k + 2) ^ 2) / a k :=
  Function.update_self ..

/-- The move `ν_k` leaves the entries other than the `k`-th one unchanged. -/
@[simp]
theorem markovMove_apply_of_ne (a : Fin 3 → ℚ) {k i : Fin 3} (h : i ≠ k) :
    markovMove a k i = a i :=
  Function.update_of_ne h ..

/-- The Markov move `ν_k` is an involution on triples whose two entries other than the `k`-th
are not both zero. -/
theorem markovMove_markovMove (a : Fin 3 → ℚ) (k : Fin 3)
    (h : a (k + 1) ^ 2 + a (k + 2) ^ 2 ≠ 0) : markovMove (markovMove a k) k = a := by
  funext i
  by_cases hi : i = k
  · subst hi
    rw [markovMove_apply_self, markovMove_apply_of_ne _ (fin_three_add_one_ne i),
      markovMove_apply_of_ne _ (fin_three_add_two_ne i), markovMove_apply_self,
      div_div_cancel₀ h]
  · simp [hi]

/-- The move along the empty sequence is the identity. -/
@[simp]
theorem markovMoveSeq_nil (a : Fin 3 → ℚ) : markovMoveSeq a [] = a :=
  rfl

/-- The move along `k :: s` is `ν_k` followed by the move along `s`. -/
@[simp]
theorem markovMoveSeq_cons (a : Fin 3 → ℚ) (k : Fin 3) (s : List (Fin 3)) :
    markovMoveSeq a (k :: s) = markovMoveSeq (markovMove a k) s :=
  rfl

/-- The move along `s ++ t` is the move along `s` followed by the move along `t`. -/
@[simp]
theorem markovMoveSeq_append (a : Fin 3 → ℚ) (s t : List (Fin 3)) :
    markovMoveSeq a (s ++ t) = markovMoveSeq (markovMoveSeq a s) t :=
  List.foldl_append ..

/-- The move along `s` followed by `k` is `ν_k` applied after the move along `s`. -/
theorem markovMoveSeq_concat (a : Fin 3 → ℚ) (s : List (Fin 3)) (k : Fin 3) :
    markovMoveSeq a (s ++ [k]) = markovMove (markovMoveSeq a s) k := by
  simp

/-! ### Vieta jumping -/

namespace IsMarkovTriple

variable {a : Fin 3 → ℕ}

/-- **Vieta jumping**: the Markov move `ν_k` sends a Markov triple to a Markov triple. -/
@[cluster_algebras "lem_markov_vieta"]
theorem markovMove (h : IsMarkovTriple a) (k : Fin 3) :
    ∃ b, IsMarkovTriple b ∧ markovMove (fun i => (a i : ℚ)) k = fun i => (b i : ℚ) := by
  have e := h.eq_rotate k
  have hk := h.pos k
  have hi := h.pos (k + 1)
  have hj := h.pos (k + 2)
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (show a k ≤ 3 * a (k + 1) * a (k + 2) by nlinarith)
  have hcz : c * a k = a (k + 1) ^ 2 + a (k + 2) ^ 2 := by
    zify at e hc ⊢
    linear_combination -e - (a k : ℤ) * hc
  have hc0 : 0 < c := by nlinarith
  refine ⟨Function.update a k c, ?_, ?_⟩
  · refine of_eq_rotate (fun i => ?_) k ?_
    · by_cases hik : i = k
      · simpa [hik] using hc0
      · simpa [hik] using h.pos i
    · simp only [Function.update_self, Function.update_of_ne (fin_three_add_one_ne k),
        Function.update_of_ne (fin_three_add_two_ne k)]
      zify at hcz hc ⊢
      linear_combination -hcz - (c : ℤ) * hc
  · funext i
    by_cases hik : i = k
    · subst hik
      rw [markovMove_apply_self, Function.update_self,
        div_eq_iff (by exact_mod_cast hk.ne')]
      exact_mod_cast hcz.symm
    · simp [hik]

/-- Every triple reached from a Markov triple by Markov moves is a Markov triple. -/
theorem markovMoveSeq (h : IsMarkovTriple a) (s : List (Fin 3)) :
    ∃ b, IsMarkovTriple b ∧ markovMoveSeq (fun i => (a i : ℚ)) s = fun i => (b i : ℚ) := by
  induction s generalizing a with
  | nil => exact ⟨a, h, rfl⟩
  | cons k s ih =>
    obtain ⟨b, hb, e⟩ := h.markovMove k
    obtain ⟨c, hc, e'⟩ := ih hb
    exact ⟨c, hc, by rw [markovMoveSeq_cons, e, e']⟩

end IsMarkovTriple

/-- **The triples in the Markov tree are Markov triples**: `ν_s(1, 1, 1)` is a Markov triple
for every finite sequence `s`. -/
@[cluster_algebras "lem_markov_reachable_markov"]
theorem isMarkovTriple_markovMoveSeq_one (s : List (Fin 3)) :
    ∃ b, IsMarkovTriple b ∧ markovMoveSeq 1 s = fun i => (b i : ℚ) := by
  rw [show (1 : Fin 3 → ℚ) = fun i => ((1 : Fin 3 → ℕ) i : ℚ) from funext fun _ => by simp]
  exact isMarkovTriple_one.markovMoveSeq s

/-! ### Descent -/

/-- The arithmetic core of descent: if `x² + y² + z² = 3xyz` with `x, y` positive and at most
`z`, and `z ≠ 1`, then `x² + y² < z²`. -/
private lemma markov_sq_add_sq_lt_sq {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hxz : x ≤ z)
    (hyz : y ≤ z) (h : x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z) (hz : z ≠ 1) :
    x ^ 2 + y ^ 2 < z ^ 2 := by
  wlog hxy : x ≤ y generalizing x y
  · have := this hy hx hyz hxz (by linear_combination h) (le_of_not_ge hxy)
    linarith
  -- First, `y < z`.
  have hyz' : y < z := by
    rcases hyz.lt_or_eq with h1 | rfl
    · exact h1
    exfalso
    have h2 : y ^ 2 ≤ x ^ 2 := by nlinarith
    obtain rfl : x = y := by nlinarith
    have : 3 * x ^ 2 * (x - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h4 | h4
    · nlinarith
    · exact hz (by linarith)
  -- The other root `3xy - z` of `X² - 3xy X + x² + y²` satisfies `(y - z)(y - c) ≤ 0`.
  have hcz : (3 * x * y - z) * z = x ^ 2 + y ^ 2 := by linear_combination -h
  have hf : (y - z) * (y - (3 * x * y - z)) = x ^ 2 + 2 * y ^ 2 - 3 * x * y ^ 2 := by
    linear_combination hcz
  have hf' : (y - z) * (y - (3 * x * y - z)) ≤ 0 := by nlinarith
  have hcy : 3 * x * y - z ≤ y := by nlinarith
  nlinarith

namespace IsMarkovTriple

variable {a : Fin 3 → ℕ}

/-- **Descent for Markov triples**: if `a` is a Markov triple other than `(1, 1, 1)` and `a_k`
is a largest entry, then the `k`-th entry of `ν_k(a)` is smaller than `a_k`. -/
@[cluster_algebras "lem_markov_descent"]
theorem markovMove_lt (h : IsMarkovTriple a) (ha : a ≠ 1) {k : Fin 3}
    (hk : ∀ i, a i ≤ a k) : ClusterAlgebras.markovMove (fun i => (a i : ℚ)) k k < a k := by
  have hk0 : (0 : ℚ) < a k := by exact_mod_cast h.pos k
  rw [markovMove_apply_self, div_lt_iff₀ hk0]
  have hz : a k ≠ 1 := fun h1 => ha <| funext fun i =>
    le_antisymm (by simpa [h1] using hk i) (by simpa using Nat.one_le_iff_ne_zero.2 (h.pos i).ne')
  have e : (a k : ℤ) ^ 2 + (a (k + 1) : ℤ) ^ 2 + (a (k + 2) : ℤ) ^ 2 =
      3 * a k * a (k + 1) * a (k + 2) := by exact_mod_cast h.eq_rotate k
  have key := markov_sq_add_sq_lt_sq (x := a (k + 1)) (y := a (k + 2)) (z := a k)
    (by exact_mod_cast h.pos _) (by exact_mod_cast h.pos _) (by exact_mod_cast hk _)
    (by exact_mod_cast hk _) (by linear_combination e)
    (by exact_mod_cast hz)
  have : (a (k + 1) : ℚ) ^ 2 + (a (k + 2) : ℚ) ^ 2 < (a k : ℚ) ^ 2 := by exact_mod_cast key
  linarith

/-- **Every Markov triple lies in the Markov tree**: every Markov triple is `ν_s(1, 1, 1)` for
some finite sequence `s`. -/
@[cluster_algebras "thm_markov_all_triples"]
theorem exists_markovMoveSeq_eq (h : IsMarkovTriple a) :
    ∃ s, ClusterAlgebras.markovMoveSeq 1 s = fun i => (a i : ℚ) := by
  obtain ⟨n, hn⟩ : ∃ n, ∑ i, a i = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
  by_cases ha : a = 1
  · subst ha
    exact ⟨[], by funext; simp⟩
  obtain ⟨k, hk⟩ := Finite.exists_max a
  obtain ⟨b, hb, e⟩ := h.markovMove k
  have hlt := h.markovMove_lt ha hk
  rw [e] at hlt
  have hbk : b k < a k := by exact_mod_cast (show ((b k : ℕ) : ℚ) < a k from hlt)
  have hbi : ∀ i, i ≠ k → b i = a i := fun i hi => by
    simpa [markovMove_apply_of_ne _ hi] using (congrFun e i).symm
  have hsum : ∑ i, b i < n := hn ▸ Finset.sum_lt_sum
    (fun i _ => if hi : i = k then hi ▸ hbk.le else (hbi i hi).le) ⟨k, Finset.mem_univ _, hbk⟩
  obtain ⟨s, hs⟩ := ih _ hsum hb rfl
  refine ⟨s ++ [k], ?_⟩
  have hS : ((a (k + 1) : ℚ)) ^ 2 + (a (k + 2) : ℚ) ^ 2 ≠ 0 := by
    have := h.pos (k + 1)
    positivity
  rw [markovMoveSeq_concat, hs, ← e, markovMove_markovMove _ _ hS]

end IsMarkovTriple

end ClusterAlgebras

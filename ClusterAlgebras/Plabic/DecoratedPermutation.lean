/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.Basic

/-!
# Decorated permutations

A *decorated permutation* on `b` letters is a permutation `π` of `[1,b]` together with a colour,
white or black, on each of its fixed points. FWZ write it as the sequence `π̃ = (π̃(1), …, π̃(b))`
with `π̃(i) = π(i)` off the fixed points, and `π̃(i)` the letter `i` over- or underlined at a white
or black fixed point. Decorated permutations index the trip permutations of plabic graphs.

An *anti-excedance* of `π̃` is a letter `i` with `π⁻¹(i) > i`, or a white fixed point; their number
`a(π̃)` can equally be counted on values, as the letters `i` with `π(i) < i` or white fixed.

For `i ≠ j` in `[1,b]` the *cyclic interval* `[i,j)_b` consists of `i, i+1, …, j-1` read modulo
`b`. Its two ends are detected by comparing a letter with its cyclic predecessor, and summing this
over the arcs `[i, π(i))_b` of a decorated permutation shows that each letter `x` lies in exactly
`a(π̃) - w` of them, `w` the number of white fixed points.

Finally `π̃_{a,b}` is the rotation `i ↦ i + a` modulo `b`, with its fixed points (present only
when `a = 0` or `a = b`) black if `a = 0` and white otherwise.

## Main definitions

* `ClusterAlgebras.DecoratedPerm b`: decorated permutations on `b` letters.
* `ClusterAlgebras.DecoratedPerm.IsAntiExcedance`,
  `ClusterAlgebras.DecoratedPerm.numAntiExcedances`: anti-excedances and their number `a(π̃)`.
* `ClusterAlgebras.cyclicIco i j`: the cyclic interval `[i,j)_b`.
* `ClusterAlgebras.DecoratedPerm.topCell a b`: the decorated permutation `π̃_{a,b}`.

## Main results

* `ClusterAlgebras.DecoratedPerm.numAntiExcedances_eq_card`: anti-excedances counted by values.
* `ClusterAlgebras.cyclicIco_ends`: the ends of a cyclic interval.
* `ClusterAlgebras.DecoratedPerm.card_cyclicIco_add_card_isWhiteFixed`: every letter lies in
  `a(π̃) - w` of the arcs `[i, π(i))_b`.
* `ClusterAlgebras.DecoratedPerm.numAntiExcedances_topCell`: `π̃_{a,b}` has `a` anti-excedances.

## Implementation notes

* The letters `[1,b]` are `Fin b`, indexed from `0`: the element `i : Fin b` is the letter
  `i.val + 1`. Comparisons such as `π⁻¹(i) > i` are unaffected by the shift.
* The decoration is a function on the subtype of fixed points, so two decorated permutations are
  equal exactly when they are equal as pairs; `DecoratedPerm.ext` compares the colours pointwise.
* The cyclic predecessor `x⁻` (`x - 1`, and `b` for `x = 1`) is `(finRotate b).symm x`, which is
  `x - 1` in `Fin b` by `finRotate_symm_apply`.
* `cyclicIco i j` is defined for all `i, j`; for `i = j` it is all of `Fin b`. The results about
  it assume `i ≠ j`, which already forces `b ≥ 2`, so that hypothesis of FWZ is dropped;
  likewise `DecoratedPerm.card_cyclicIco_add_card_isWhiteFixed` holds for every `b`.
* `topCell a b` is defined for all `a, b`; it is FWZ's `π̃_{a,b}` when `a ≤ b`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7.
-/

@[expose] public section

open Finset

namespace ClusterAlgebras

/-- A **decorated permutation** on `b` letters: a permutation `perm` of `[1,b]` and a colour
`colour` on each of its fixed points. FWZ's letter `i.val + 1` is `i : Fin b`. In
FWZ's notation `π̃(i)` is `perm i` off the fixed points, `i` overlined at a white fixed point and
underlined at a black one. -/
@[cluster_algebras "def_decorated_permutation"]
structure DecoratedPerm (b : ℕ) where
  /-- The underlying permutation. -/
  perm : Equiv.Perm (Fin b)
  /-- The colour of each fixed point. -/
  colour : {i : Fin b // perm i = i} → Shade
  deriving DecidableEq

namespace DecoratedPerm

variable {b : ℕ} (π : DecoratedPerm b)

/-- Two decorated permutations are equal when their permutations are, with the same colour at
each fixed point. -/
@[ext]
theorem ext {π σ : DecoratedPerm b} (hperm : π.perm = σ.perm)
    (hcolour : ∀ i (hπ : π.perm i = i) (hσ : σ.perm i = i),
      π.colour ⟨i, hπ⟩ = σ.colour ⟨i, hσ⟩) : π = σ := by
  obtain ⟨p, c⟩ := π
  obtain ⟨q, d⟩ := σ
  obtain rfl : p = q := hperm
  congr
  funext ⟨i, h⟩
  exact hcolour i h h

/-- The decorated permutation with permutation `p` whose fixed points `i` are coloured `c i`. -/
def ofColouring (p : Equiv.Perm (Fin b)) (c : Fin b → Shade) : DecoratedPerm b where
  perm := p
  colour i := c i

/-- The permutation of `ofColouring p c` is `p`. -/
@[simp]
theorem ofColouring_perm (p : Equiv.Perm (Fin b)) (c : Fin b → Shade) :
    (ofColouring p c).perm = p := rfl

/-- The colour of a fixed point `i` of `ofColouring p c` is `c i`. -/
@[simp]
theorem ofColouring_colour (p : Equiv.Perm (Fin b)) (c : Fin b → Shade) (i) :
    (ofColouring p c).colour i = c i := rfl

/-- `i` is a fixed point of `π` coloured white: FWZ's `π̃(i) = i̅`. -/
def IsWhiteFixed (i : Fin b) : Prop :=
  ∃ h : π.perm i = i, π.colour ⟨i, h⟩ = .white

/-- `i` is a fixed point of `π` coloured black: FWZ's `π̃(i) = i̲`. -/
def IsBlackFixed (i : Fin b) : Prop :=
  ∃ h : π.perm i = i, π.colour ⟨i, h⟩ = .black

/-- Being a white fixed point is decidable. -/
instance : DecidablePred π.IsWhiteFixed := fun _ => inferInstanceAs (Decidable (∃ _ : _, _))

/-- Being a black fixed point is decidable. -/
instance : DecidablePred π.IsBlackFixed := fun _ => inferInstanceAs (Decidable (∃ _ : _, _))

/-- A white fixed point is a fixed point. -/
theorem IsWhiteFixed.perm_apply_eq {π : DecoratedPerm b} {i : Fin b} (h : π.IsWhiteFixed i) :
    π.perm i = i :=
  h.1

/-- A black fixed point is a fixed point. -/
theorem IsBlackFixed.perm_apply_eq {π : DecoratedPerm b} {i : Fin b} (h : π.IsBlackFixed i) :
    π.perm i = i :=
  h.1

/-- A fixed point `i` is a white fixed point exactly when its colour is white. -/
theorem isWhiteFixed_iff_of_perm_apply_eq {i : Fin b} (h : π.perm i = i) :
    π.IsWhiteFixed i ↔ π.colour ⟨i, h⟩ = .white :=
  ⟨fun ⟨_, hc⟩ => hc, fun hc => ⟨h, hc⟩⟩

/-- A fixed point `i` is a black fixed point exactly when its colour is black. -/
theorem isBlackFixed_iff_of_perm_apply_eq {i : Fin b} (h : π.perm i = i) :
    π.IsBlackFixed i ↔ π.colour ⟨i, h⟩ = .black :=
  ⟨fun ⟨_, hc⟩ => hc, fun hc => ⟨h, hc⟩⟩

/-- A fixed point is white or black. -/
theorem isWhiteFixed_or_isBlackFixed {i : Fin b} (h : π.perm i = i) :
    π.IsWhiteFixed i ∨ π.IsBlackFixed i := by
  rw [π.isWhiteFixed_iff_of_perm_apply_eq h, π.isBlackFixed_iff_of_perm_apply_eq h]
  cases π.colour ⟨i, h⟩ <;> simp

/-- A white fixed point is not a black fixed point. -/
theorem not_isBlackFixed_of_isWhiteFixed {i : Fin b} (h : π.IsWhiteFixed i) :
    ¬π.IsBlackFixed i := by
  rintro ⟨h', hc⟩
  rw [(π.isWhiteFixed_iff_of_perm_apply_eq h').1 h] at hc
  exact Shade.noConfusion hc

/-- Being a white fixed point is invariant under `π`. -/
theorem isWhiteFixed_perm_apply_iff {i : Fin b} :
    π.IsWhiteFixed (π.perm i) ↔ π.IsWhiteFixed i := by
  by_cases h : π.perm i = i
  · rw [h]
  · exact iff_of_false (fun hw => h (π.perm.injective hw.1)) fun hw => h hw.1

/-- `i` is an **anti-excedance** of `π̃ = (π, ε)`: `π⁻¹(i) > i`, or `i` is a white fixed point. -/
@[cluster_algebras "def_anti_excedance"]
def IsAntiExcedance (i : Fin b) : Prop :=
  i < π.perm⁻¹ i ∨ π.IsWhiteFixed i

/-- Being an anti-excedance is decidable. -/
instance : DecidablePred π.IsAntiExcedance := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The number `a(π̃)` of anti-excedances of `π̃`. -/
@[cluster_algebras "def_anti_excedance"]
def numAntiExcedances : ℕ :=
  #{i | π.IsAntiExcedance i}

/-- **Counting anti-excedances by values.** `a(π̃)` is the number of `i` with `π(i) < i`, or
`i` a white fixed point. -/
@[cluster_algebras "lem_anti_excedance_count"]
theorem numAntiExcedances_eq_card :
    π.numAntiExcedances = #{i | π.perm i < i ∨ π.IsWhiteFixed i} := by
  refine Finset.card_equiv π.perm⁻¹ fun i => ?_
  have := π.isWhiteFixed_perm_apply_iff (i := π.perm⁻¹ i)
  simp at this
  simp [IsAntiExcedance, this]

end DecoratedPerm

/-! ### Cyclic intervals -/

/-- The **cyclic interval** `[i,j)_b`: the letters `i, i+1, …, j-1` read modulo `b`, that is
`{x | i ≤ x < j}` if `i < j` and `{x | i ≤ x or x < j}` otherwise. FWZ take `i ≠ j`; for
`i = j` this is all of `Fin b`. -/
@[cluster_algebras "def_cyclic_interval"]
def cyclicIco {b : ℕ} (i j : Fin b) : Finset (Fin b) :=
  if i < j then univ.filter (fun x => i ≤ x ∧ x < j) else univ.filter (fun x => i ≤ x ∨ x < j)

/-- `x ∈ [i,j)_b` exactly when `i ≤ x < j` if `i < j`, and `i ≤ x` or `x < j` if `j ≤ i`. -/
theorem mem_cyclicIco {b : ℕ} {i j x : Fin b} :
    x ∈ cyclicIco i j ↔ (i < j ∧ i ≤ x ∧ x < j) ∨ (j ≤ i ∧ (i ≤ x ∨ x < j)) := by
  unfold cyclicIco
  split_ifs with h
  · simp [h]
  · simp [h, not_lt.mp h]

/-- For `i < j`, `x ∈ [i,j)_b` exactly when `i ≤ x < j`. -/
theorem mem_cyclicIco_of_lt {b : ℕ} {i j x : Fin b} (h : i < j) :
    x ∈ cyclicIco i j ↔ i ≤ x ∧ x < j := by
  simp [cyclicIco, h]

/-- For `j ≤ i`, `x ∈ [i,j)_b` exactly when `i ≤ x` or `x < j`. -/
theorem mem_cyclicIco_of_le {b : ℕ} {i j x : Fin b} (h : j ≤ i) :
    x ∈ cyclicIco i j ↔ i ≤ x ∨ x < j := by
  simp [cyclicIco, not_lt.mpr h]

/-- **The ends of a cyclic interval.** For `i ≠ j` and a letter `x` with cyclic predecessor
`x⁻ = (finRotate b).symm x`, `[x⁻ ∈ [i,j)_b] - [x ∈ [i,j)_b] = [x = j] - [x = i]`. -/
@[cluster_algebras "lem_cyclic_interval_ends"]
theorem cyclicIco_ends {b : ℕ} {i j : Fin b} (hij : i ≠ j) (x : Fin b) :
    ((if (finRotate b).symm x ∈ cyclicIco i j then 1 else 0 : ℤ) -
        if x ∈ cyclicIco i j then 1 else 0) =
      (if x = j then 1 else 0) - if x = i then 1 else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by have := x.pos; omega⟩
  have key : ((finRotate (n + 1)).symm x).val = if x.val = 0 then n else x.val - 1 := by
    split_ifs with hx
    · obtain rfl : x = 0 := Fin.ext hx
      rw [show (finRotate (n + 1)).symm 0 = Fin.last n from
        (Equiv.symm_apply_eq _).2 (finRotate_last').symm]
      rfl
    · exact coe_finRotate_symm_of_ne_zero (fun h => hx (by simp [h]))
  have hi := i.isLt
  have hj := j.isLt
  have hx := x.isLt
  rw [Fin.ne_iff_vne] at hij
  simp only [mem_cyclicIco, Fin.lt_def, Fin.le_def, Fin.ext_iff, key]
  split_ifs <;> omega

/-! ### The arcs of a decorated permutation -/

namespace DecoratedPerm

variable {b : ℕ} (π : DecoratedPerm b)

/-- The number of non-fixed `i` with `x ∈ [i, π(i))_b` is unchanged by passing from `x` to its
cyclic predecessor. -/
theorem card_cyclicIco_finRotate_symm (x : Fin b) :
    #{i | π.perm i ≠ i ∧ (finRotate b).symm x ∈ cyclicIco i (π.perm i)} =
      #{i | π.perm i ≠ i ∧ x ∈ cyclicIco i (π.perm i)} := by
  have h : (#{i | π.perm i ≠ i ∧ (finRotate b).symm x ∈ cyclicIco i (π.perm i)} : ℤ) -
      #{i | π.perm i ≠ i ∧ x ∈ cyclicIco i (π.perm i)} = 0 := by
    simp only [Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
    calc _ = ∑ i, ((if x = π.perm i then (1 : ℤ) else 0) - if x = i then 1 else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : π.perm i = i
          · simp [hi]
          · simpa [hi] using cyclicIco_ends (Ne.symm hi) x
      _ = 0 := by
          rw [Finset.sum_sub_distrib,
            Equiv.sum_comp π.perm (fun j => if x = j then (1 : ℤ) else 0)]
          simp
  omega

/-- **Counting the cyclic intervals of a decorated permutation.** For every letter `x`, the number
of non-fixed `i` with `x ∈ [i, π(i))_b`, plus the number of white fixed points, is `a(π̃)`. -/
@[cluster_algebras "lem_cyclic_interval_count"]
theorem card_cyclicIco_add_card_isWhiteFixed (x : Fin b) :
    #{i | π.perm i ≠ i ∧ x ∈ cyclicIco i (π.perm i)} + #{i | π.IsWhiteFixed i} =
      π.numAntiExcedances := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by have := x.pos; omega⟩
  set N : Fin (n + 1) → ℕ := fun x => #{i | π.perm i ≠ i ∧ x ∈ cyclicIco i (π.perm i)} with hN
  have step : ∀ y, N ((finRotate (n + 1)).symm y) = N y := π.card_cyclicIco_finRotate_symm
  have hconst : ∀ k (hk : k < n + 1), N ⟨k, hk⟩ = N (Fin.last n) := by
    intro k hk
    induction k with
    | zero =>
      rw [← step]
      congr 1
    | succ k ih =>
      rw [← step, ← ih (by omega)]
      congr 1
      ext
      rw [coe_finRotate_symm_of_ne_zero (by simp [Fin.ext_iff])]
      simp
  have hlast : N (Fin.last n) = #{i | π.perm i < i} := by
    simp only [hN]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_cyclicIco, Fin.lt_def, Fin.le_def,
      Fin.val_last, ne_eq, Fin.ext_iff]
    have := (π.perm i).isLt
    have := i.isLt
    omega
  change N x + _ = _
  rw [hconst x.val x.isLt, hlast, numAntiExcedances_eq_card, filter_or, card_union_of_disjoint]
  exact Finset.disjoint_filter.2 fun i _ h hw => (ne_of_lt h) hw.1

/-! ### The top cell -/

/-- The **decorated permutation `π̃_{a,b}`**: `π_{a,b}` is the rotation `i ↦ i + a` modulo `b`
(`finRotate b ^ a`), and its fixed points are black if `a = 0` and white if `a ≥ 1`. This is
FWZ's `π̃_{a,b}` for `a ≤ b`; see `topCell_perm_apply_val_of_lt` and
`topCell_perm_apply_val_of_le` for its values. -/
@[cluster_algebras "def_top_cell_permutation"]
def topCell (a b : ℕ) : DecoratedPerm b :=
  ofColouring (finRotate b ^ a) fun _ => if a = 0 then .black else .white

/-- The values of a power of `finRotate`. -/
theorem _root_.finRotate_pow_apply_val (a : ℕ) {b : ℕ} (i : Fin b) :
    ((finRotate b ^ a) i).val = (i.val + a) % b := by
  induction a with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by have := i.pos; omega⟩
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
      ← Nat.add_mod, Nat.add_assoc]

/-- The permutation of `π̃_{a,b}` is `finRotate b ^ a`. -/
theorem topCell_perm (a b : ℕ) : (topCell a b).perm = finRotate b ^ a := rfl

/-- `π_{a,b}(i) = (i + a) mod b`. -/
theorem topCell_perm_apply_val (a b : ℕ) (i : Fin b) :
    ((topCell a b).perm i).val = (i.val + a) % b :=
  finRotate_pow_apply_val a i

/-- `π_{a,b}(i) = i + a` for the letters `i ∈ [1, b - a]`. -/
theorem topCell_perm_apply_val_of_lt {a b : ℕ} {i : Fin b} (h : i.val + a < b) :
    ((topCell a b).perm i).val = i.val + a := by
  rw [topCell_perm_apply_val, Nat.mod_eq_of_lt h]

/-- `π_{a,b}(i) = i + a - b` for the letters `i ∈ [b - a + 1, b]`, when `a ≤ b`. -/
theorem topCell_perm_apply_val_of_le {a b : ℕ} (hab : a ≤ b) {i : Fin b} (h : b ≤ i.val + a) :
    ((topCell a b).perm i).val = i.val + a - b := by
  rw [topCell_perm_apply_val, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by have := i.isLt; omega)]

/-- The fixed points of `π̃_{a,b}` are black if `a = 0` and white otherwise. -/
@[simp]
theorem topCell_colour (a b : ℕ) (i) :
    (topCell a b).colour i = if a = 0 then .black else .white := rfl

/-- The letters of `[1,b]` among the last `a` are `a` in number. -/
private theorem card_filter_sub_le_val {a b : ℕ} (hab : a ≤ b) :
    #{i : Fin b | b - a ≤ i.val} = a := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin b)))
    (fun i : Fin b => (i : ℕ) < b - a)
  have h2 : #{i : Fin b | (i : ℕ) < b - a} = min b (b - a) := Fin.card_filter_val_lt
  simp only [not_lt, card_univ, Fintype.card_fin] at h1
  omega

/-- `π̃_{a,b}` has `a` anti-excedances, for `a ≤ b`: they are the last `a` letters. -/
theorem numAntiExcedances_topCell {a b : ℕ} (hab : a ≤ b) :
    (topCell a b).numAntiExcedances = a := by
  rw [numAntiExcedances_eq_card]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [IsWhiteFixed, topCell_perm]
  · have key : ∀ i : Fin b,
        ((topCell a b).perm i < i ∨ (topCell a b).IsWhiteFixed i) ↔ b - a ≤ i.val := by
      intro i
      have hv := topCell_perm_apply_val a b i
      have hi := i.isLt
      simp only [IsWhiteFixed, topCell_colour, ha.ne', if_false, exists_prop, and_true,
        Fin.lt_def, Fin.ext_iff, hv]
      rcases lt_or_ge (i.val + a) b with h | h
      · rw [Nat.mod_eq_of_lt h]
        omega
      · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
        omega
    rw [filter_congr fun i _ => key i]
    exact card_filter_sub_le_val hab

end DecoratedPerm

end ClusterAlgebras

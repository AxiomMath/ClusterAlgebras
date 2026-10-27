/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Data.Int.ModEq
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Affine transpositions, partial products and position maps

Fix `b ≥ 1`. For `1 ≤ i < j ≤ b` the *affine transposition* `s_{i,j} : ℤ → ℤ` exchanges
`i + m b` and `j + m b` for every `m ∈ ℤ` and fixes every other integer. For `f : ℤ → ℤ`, the
composite `f ∘ s_{i,j}` is `f` with its values at the positions `i + m b` and `j + m b` swapped,
the *swap* of [FWZ]. A finite sequence of pairs `((i₁, j₁), …, (i_r, j_r))` gives the
*partial products* `f₀ = f`, `f_t = f_{t-1} ∘ s_{i_t,j_t}`, and the *position maps*
`ρ_t = τ_t ∘ ⋯ ∘ τ₁`, where `τ_t` is the transposition of `[1, b]` exchanging `i_t` and `j_t`.
The value of `f` at `x` is carried along by the position maps: `f_t (ρ_t x) = f x`.

A sequence of pairs is *nested* if no later pair has an entry strictly between the two entries
of an earlier pair; this is the condition under which the bridge graph of the sequence is drawn.

## Main definitions

* `ClusterAlgebras.affineTransposition`: the affine transposition `s_{i,j}`.
* `ClusterAlgebras.swapProduct`: the partial products `f_t`.
* `ClusterAlgebras.positionMap`: the position maps `ρ_t`.
* `ClusterAlgebras.IsNestedPairSequence`: nested sequences of pairs.

## Main results

* `ClusterAlgebras.affineTransposition_lt_iff`: the pairs `p < q` reversed by `s_{i,j}`.
* `ClusterAlgebras.swapProduct_positionMap`: `f_t (ρ_t x) = f x`.

## Implementation notes

* Pairs are pairs of integers, sequences of pairs are lists `List (ℤ × ℤ)`, and the partial
  products and position maps are indexed by `t : ℕ`; for `t` beyond the length `r` of the
  sequence they are constant, equal to their values at `r`.
* The affine transposition is defined for all integers `i, j` (the case `n ≡ i` taking
  precedence); the hypothesis `1 ≤ i < j ≤ b` is carried by the lemmas.
* The position map `ρ_t` is a permutation of `ℤ`, the product of the transpositions
  `Equiv.swap i_u j_u`, rather than of `[1, b]`: when all entries lie in `[1, b]` it maps `[1, b]`
  onto itself and fixes every other integer, and its restriction to `[1, b]` is FWZ's
  `ρ_t`. This keeps the labels as the integers of FWZ, so that they can be compared with
  the values of the partial products without a change of indexing.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7.
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### Affine transpositions -/

/-- The *affine transposition* `s_{i,j}` for `b`: `n ↦ n + (j - i)` if `n ≡ i (mod b)`,
`n ↦ n - (j - i)` if `n ≡ j (mod b)`, and `n ↦ n` otherwise. When `1 ≤ i < j ≤ b` the first two
cases are exclusive; for general `i j` the first case takes precedence. -/
@[cluster_algebras "def_affine_transposition"]
def affineTransposition (b : ℕ) (i j : ℤ) (n : ℤ) : ℤ :=
  if n ≡ i [ZMOD b] then n + (j - i) else if n ≡ j [ZMOD b] then n - (j - i) else n

section affineTransposition

variable {b : ℕ} {i j : ℤ}

/-- If `n ≡ i (mod b)`, then `s_{i,j} n = n + (j - i)`. -/
theorem affineTransposition_of_modEq_left {n : ℤ} (h : n ≡ i [ZMOD b]) :
    affineTransposition b i j n = n + (j - i) := by
  simp [affineTransposition, h]

/-- If `n ≢ i (mod b)` and `n ≡ j (mod b)`, then `s_{i,j} n = n - (j - i)`. -/
theorem affineTransposition_of_modEq_right {n : ℤ} (hi : ¬ n ≡ i [ZMOD b])
    (h : n ≡ j [ZMOD b]) : affineTransposition b i j n = n - (j - i) := by
  simp [affineTransposition, h, hi]

/-- If `n` is congruent to neither `i` nor `j` modulo `b`, then `s_{i,j} n = n`. -/
theorem affineTransposition_of_not_modEq {n : ℤ} (hi : ¬ n ≡ i [ZMOD b])
    (hj : ¬ n ≡ j [ZMOD b]) : affineTransposition b i j n = n := by
  simp [affineTransposition, hi, hj]

/-- An affine transposition commutes with the shifts by multiples of `b`. -/
theorem affineTransposition_add_mul (n m : ℤ) :
    affineTransposition b i j (n + m * b) = affineTransposition b i j n + m * b := by
  have key : ∀ k : ℤ, (n + m * b ≡ k [ZMOD b]) ↔ (n ≡ k [ZMOD b]) := fun k => by
    simp [Int.ModEq, Int.add_mul_emod_self_right]
  unfold affineTransposition
  simp only [key]
  split_ifs <;> ring

/-- An affine transposition commutes with the shift by `b`. -/
theorem affineTransposition_add (n : ℤ) :
    affineTransposition b i j (n + b) = affineTransposition b i j n + b := by
  simpa using affineTransposition_add_mul (b := b) (i := i) (j := j) n 1

/-- Two integers less than `b` apart are congruent modulo `b` only if they are equal. -/
theorem modEq_iff_eq_of_lt {x y : ℤ} (h₁ : y < x + b) (h₂ : x < y + b) :
    x ≡ y [ZMOD b] ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ Int.ModEq.refl _⟩
  have := Int.eq_zero_of_abs_lt_dvd (m := b) (x := x - y) (Int.modEq_iff_dvd.mp h.symm)
    (by rw [abs_lt]; omega)
  omega

/-- For `i < j < i + b` and `i ≤ x < i + b`, the affine transposition `s_{i,j}` exchanges `i`
and `j` and fixes the other integers in `[i, i + b)`. -/
theorem affineTransposition_of_le_of_lt (hij : i < j) (hjb : j < i + b) {x : ℤ} (hx : i ≤ x)
    (hx' : x < i + b) :
    affineTransposition b i j x = if x = i then j else if x = j then i else x := by
  unfold affineTransposition
  simp only [modEq_iff_eq_of_lt (b := b) (x := x) (y := i) (by omega) hx',
    modEq_iff_eq_of_lt (b := b) (x := x) (y := j) (by omega) (by omega)]
  split_ifs <;> omega

/-- For `i < j < i + b`, `s_{i,j}` maps `i + m b` to `j + m b`. -/
theorem affineTransposition_left_add_mul (hij : i < j) (hjb : j < i + b) (m : ℤ) :
    affineTransposition b i j (i + m * b) = j + m * b := by
  rw [affineTransposition_add_mul, affineTransposition_of_le_of_lt hij hjb le_rfl (by omega),
    if_pos rfl]

/-- For `i < j < i + b`, `s_{i,j}` maps `j + m b` to `i + m b`. -/
theorem affineTransposition_right_add_mul (hij : i < j) (hjb : j < i + b) (m : ℤ) :
    affineTransposition b i j (j + m * b) = i + m * b := by
  rw [affineTransposition_add_mul, affineTransposition_of_le_of_lt hij hjb hij.le hjb,
    if_neg hij.ne', if_pos rfl]

/-- On `[1, b]`, the affine transposition `s_{i,j}` agrees with the transposition of `i` and
`j`, for `i, j ∈ [1, b]`. -/
theorem affineTransposition_eq_swap (hi : 1 ≤ i ∧ i ≤ b) (hj : 1 ≤ j ∧ j ≤ b) {p : ℤ}
    (hp : 1 ≤ p ∧ p ≤ b) : affineTransposition b i j p = Equiv.swap i j p := by
  unfold affineTransposition
  simp only [modEq_iff_eq_of_lt (b := b) (x := p) (y := i) (by omega) (by omega),
    modEq_iff_eq_of_lt (b := b) (x := p) (y := j) (by omega) (by omega)]
  split_ifs with h1 h2
  · simp [h1]
  · simp [h2]
  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- Every integer is `x + m b` for some `m` and some `x ∈ [i, i + b)`. -/
theorem exists_eq_add_mul_of_pos {b : ℤ} (hb : 0 < b) (i n : ℤ) :
    ∃ x m : ℤ, i ≤ x ∧ x < i + b ∧ n = x + m * b :=
  ⟨i + (n - i) % b, (n - i) / b, by have := Int.emod_nonneg (n - i) hb.ne'; omega,
    by have := Int.emod_lt_of_pos (n - i) hb; omega,
    by have := Int.emod_add_mul_ediv (n - i) b; linarith⟩

/-- For `i < j < i + b`, the affine transposition `s_{i,j}` is an involution. -/
theorem affineTransposition_involutive (hij : i < j) (hjb : j < i + b) :
    Function.Involutive (affineTransposition b i j) := by
  intro n
  obtain ⟨x, m, hx, hx', rfl⟩ := exists_eq_add_mul_of_pos (b := b) (by omega) i n
  rw [affineTransposition_add_mul, affineTransposition_of_le_of_lt hij hjb hx hx']
  split_ifs with ha hb'
  · rw [affineTransposition_add_mul, affineTransposition_of_le_of_lt hij hjb (by omega)
      (by omega), if_neg (by omega), if_pos rfl, ha]
  · rw [affineTransposition_add_mul, affineTransposition_of_le_of_lt hij hjb le_rfl
      (by omega), if_pos rfl, hb']
  · rw [affineTransposition_add_mul, affineTransposition_of_le_of_lt hij hjb hx hx', if_neg ha,
      if_neg hb']

/-- **Pairs reversed by an affine transposition**. Let `1 ≤ i < j ≤ b` and `p < q`. Then
`s_{i,j}(p) > s_{i,j}(q)` if and only if `(p, q) = (x + m b, y + m b)` for some `m` and some
`i ≤ x < y ≤ j` with `x = i` or `y = j`. -/
@[cluster_algebras "lem_swap_reversed_pairs"]
theorem affineTransposition_lt_iff (hi : 1 ≤ i) (hij : i < j) (hjb : j ≤ b) {p q : ℤ}
    (hpq : p < q) :
    affineTransposition b i j q < affineTransposition b i j p ↔
      ∃ m x y : ℤ, i ≤ x ∧ x < y ∧ y ≤ j ∧ (x = i ∨ y = j) ∧ p = x + m * b ∧ q = y + m * b := by
  have hjb' : j < i + b := by omega
  have hb : (0 : ℤ) < b := by omega
  constructor
  · intro h
    obtain ⟨x, m, hx1, hx2, rfl⟩ := exists_eq_add_mul_of_pos hb i p
    obtain ⟨y, m', hy1, hy2, rfl⟩ := exists_eq_add_mul_of_pos hb i q
    rw [affineTransposition_add_mul, affineTransposition_add_mul,
      affineTransposition_of_le_of_lt hij hjb' hx1 hx2,
      affineTransposition_of_le_of_lt hij hjb' hy1 hy2] at h
    rcases lt_trichotomy m m' with hm | rfl | hm
    · have : m * b + b ≤ m' * b := by nlinarith
      split_ifs at h <;> omega
    · refine ⟨m, x, y, hx1, ?_, ?_, ?_, rfl, rfl⟩ <;> split_ifs at h <;> omega
    · have : m' * b + b ≤ m * b := by nlinarith
      split_ifs at h <;> omega
  · rintro ⟨m, x, y, hix, hxy, hyj, hxy', rfl, rfl⟩
    rw [affineTransposition_add_mul, affineTransposition_add_mul,
      affineTransposition_of_le_of_lt hij hjb' hix (by omega),
      affineTransposition_of_le_of_lt hij hjb' (by omega) (by omega)]
    split_ifs <;> omega

end affineTransposition

/-! ### Partial products -/

/-- The *partial products* of a sequence of pairs `s = ((i₁, j₁), …, (i_r, j_r))` for a map
`f : ℤ → ℤ`: `swapProduct b f s t` is `f_t = f ∘ s_{i₁,j₁} ∘ ⋯ ∘ s_{i_t,j_t}`, so `f₀ = f` and
`f_t = f_{t-1} ∘ s_{i_t,j_t}` for `t ∈ [1, r]`. For `t ≥ r` it is `f_r`. -/
@[cluster_algebras "def_swap_products"]
def swapProduct (b : ℕ) (f : ℤ → ℤ) (s : List (ℤ × ℤ)) (t : ℕ) : ℤ → ℤ :=
  (s.take t).foldl (fun g p => g ∘ affineTransposition b p.1 p.2) f

section swapProduct

variable {b : ℕ} {f : ℤ → ℤ} {s : List (ℤ × ℤ)}

/-- The zeroth partial product is `f`. -/
@[simp]
theorem swapProduct_zero : swapProduct b f s 0 = f := rfl

/-- For `t < r`, `f_{t+1} = f_t ∘ s_{i_{t+1},j_{t+1}}`. -/
theorem swapProduct_succ {t : ℕ} (ht : t < s.length) :
    swapProduct b f s (t + 1) =
      swapProduct b f s t ∘ affineTransposition b s[t].1 s[t].2 := by
  rw [swapProduct, swapProduct, List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some,
    List.foldl_append]
  rfl

/-- The partial products of the empty sequence are all equal to `f`. -/
@[simp]
theorem swapProduct_nil (t : ℕ) : swapProduct b f [] t = f := by
  simp [swapProduct]

/-- The `(t + 1)`-st partial product of `p :: s` for `f` is the `t`-th partial product of `s`
for `f ∘ s_{p.1,p.2}`. -/
@[simp]
theorem swapProduct_cons_succ (p : ℤ × ℤ) (t : ℕ) :
    swapProduct b f (p :: s) (t + 1) =
      swapProduct b (f ∘ affineTransposition b p.1 p.2) s t := by
  simp [swapProduct]

/-- For `t ≥ r`, the partial product `f_t` equals `f_r`. -/
theorem swapProduct_of_length_le {t : ℕ} (ht : s.length ≤ t) :
    swapProduct b f s t = swapProduct b f s s.length := by
  simp [swapProduct, List.take_of_length_le ht]

end swapProduct

/-! ### Position maps -/

/-- The *position maps* of a sequence of pairs `s = ((i₁, j₁), …, (i_r, j_r))`: `positionMap s t`
is `ρ_t = τ_t ∘ τ_{t-1} ∘ ⋯ ∘ τ₁`, where `τ_u` is the transposition exchanging `i_u` and `j_u`;
`ρ₀` is the identity, and `ρ_t = ρ_r` for `t ≥ r`.

It is a permutation of `ℤ`. When `1 ≤ i_u, j_u ≤ b` for all `u`, it fixes every integer outside
`[1, b]` and maps `[1, b]` onto itself (`positionMap_mem_Icc`). -/
@[cluster_algebras "def_bridge_position_map"]
def positionMap (s : List (ℤ × ℤ)) (t : ℕ) : Equiv.Perm ℤ :=
  (s.take t).foldl (fun ρ p => Equiv.swap p.1 p.2 * ρ) 1

section positionMap

variable {s : List (ℤ × ℤ)}

/-- The zeroth position map is the identity. -/
@[simp]
theorem positionMap_zero : positionMap s 0 = 1 := rfl

/-- For `t < r`, `ρ_{t+1} = τ_{t+1} * ρ_t`, where `τ_{t+1}` exchanges `i_{t+1}` and `j_{t+1}`. -/
theorem positionMap_succ {t : ℕ} (ht : t < s.length) :
    positionMap s (t + 1) = Equiv.swap s[t].1 s[t].2 * positionMap s t := by
  rw [positionMap, positionMap, List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some,
    List.foldl_append]
  rfl

/-- The position maps of the empty sequence are all the identity. -/
@[simp]
theorem positionMap_nil (t : ℕ) : positionMap [] t = 1 := by
  simp [positionMap]

/-- For `t ≥ r`, the position map `ρ_t` equals `ρ_r`. -/
theorem positionMap_of_length_le {t : ℕ} (ht : s.length ≤ t) :
    positionMap s t = positionMap s s.length := by
  simp [positionMap, List.take_of_length_le ht]

/-- If all pairs of `s` lie in `[1, b]`, the position maps send `[1, b]` to itself. -/
theorem positionMap_mem_Icc {b : ℤ} (hs : ∀ p ∈ s, (1 ≤ p.1 ∧ p.1 ≤ b) ∧ (1 ≤ p.2 ∧ p.2 ≤ b))
    (t : ℕ) {x : ℤ} (hx : 1 ≤ x ∧ x ≤ b) : 1 ≤ positionMap s t x ∧ positionMap s t x ≤ b := by
  induction t with
  | zero => simpa using hx
  | succ t ih =>
    rcases lt_or_ge t s.length with ht | ht
    · rw [positionMap_succ ht, Equiv.Perm.mul_apply]
      have hp := hs _ (List.getElem_mem ht)
      rcases eq_or_ne (positionMap s t x) s[t].1 with h1 | h1
      · rw [h1, Equiv.swap_apply_left]
        exact hp.2
      rcases eq_or_ne (positionMap s t x) s[t].2 with h2 | h2
      · rw [h2, Equiv.swap_apply_right]
        exact hp.1
      rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rwa [positionMap_of_length_le (by omega), ← positionMap_of_length_le ht]

end positionMap

/-- **A wire keeps its value**. Let `s` be a sequence of pairs with entries in `[1, b]`, with
partial products `f_t` for `f`. Then `f_t (ρ_t x) = f x` for every `x ∈ [1, b]` and every `t`. -/
@[cluster_algebras "lem_bridge_wire_value"]
theorem swapProduct_positionMap {b : ℕ} (f : ℤ → ℤ) {s : List (ℤ × ℤ)}
    (hs : ∀ p ∈ s, (1 ≤ p.1 ∧ p.1 ≤ b) ∧ (1 ≤ p.2 ∧ p.2 ≤ b)) (t : ℕ) {x : ℤ}
    (hx : 1 ≤ x ∧ x ≤ b) : swapProduct b f s t (positionMap s t x) = f x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rcases lt_or_ge t s.length with ht | ht
    · have hp := hs _ (List.getElem_mem ht)
      have hm := positionMap_mem_Icc (b := (b : ℤ)) hs (t + 1) hx
      rw [swapProduct_succ ht, Function.comp_apply, affineTransposition_eq_swap hp.1 hp.2 hm,
        positionMap_succ ht, Equiv.Perm.mul_apply, Equiv.swap_apply_self, ih]
    · rwa [swapProduct_of_length_le (by omega), positionMap_of_length_le (by omega),
        ← swapProduct_of_length_le ht, ← positionMap_of_length_le ht]

/-! ### Nested sequences -/

/-- A sequence of pairs `s = ((i₁, j₁), …, (i_r, j_r))` is *nested* if for all
`t < t'` and every integer `h` with `i_t < h < j_t`, `h ∉ {i_{t'}, j_{t'}}`: no later pair has an
entry strictly between the entries of an earlier pair. See `isNestedPairSequence_iff` for the
statement with indices. -/
@[cluster_algebras "def_nested_pair_sequence"]
def IsNestedPairSequence (s : List (ℤ × ℤ)) : Prop :=
  s.Pairwise fun p q => q.1 ∉ Set.Ioo p.1 p.2 ∧ q.2 ∉ Set.Ioo p.1 p.2

/-- A sequence `s` is nested if and only if for all indices `t < t'` and every integer `h` with
`i_t < h < j_t`, `h` differs from both `i_{t'}` and `j_{t'}`. -/
theorem isNestedPairSequence_iff {s : List (ℤ × ℤ)} :
    IsNestedPairSequence s ↔ ∀ (t t' : ℕ) (ht : t < s.length) (ht' : t' < s.length), t < t' →
      ∀ h : ℤ, s[t].1 < h → h < s[t].2 → h ≠ s[t'].1 ∧ h ≠ s[t'].2 := by
  rw [IsNestedPairSequence, List.pairwise_iff_getElem]
  refine forall_congr' fun t => forall_congr' fun t' => forall_congr' fun ht =>
    forall_congr' fun ht' => forall_congr' fun _ => ?_
  exact ⟨fun ⟨h1, h2⟩ h hl hr => ⟨fun e => h1 (e ▸ ⟨hl, hr⟩), fun e => h2 (e ▸ ⟨hl, hr⟩)⟩,
    fun H => ⟨fun ⟨hl, hr⟩ => (H _ hl hr).1 rfl, fun ⟨hl, hr⟩ => (H _ hl hr).2 rfl⟩⟩

/-- The empty sequence is nested. -/
@[simp]
theorem isNestedPairSequence_nil : IsNestedPairSequence [] := List.Pairwise.nil

/-- The sequence `p :: s` is nested if and only if no entry of a pair of `s` lies strictly
between `p.1` and `p.2`, and `s` is nested. -/
@[simp]
theorem isNestedPairSequence_cons {p : ℤ × ℤ} {s : List (ℤ × ℤ)} :
    IsNestedPairSequence (p :: s) ↔
      (∀ q ∈ s, q.1 ∉ Set.Ioo p.1 p.2 ∧ q.2 ∉ Set.Ioo p.1 p.2) ∧ IsNestedPairSequence s :=
  List.pairwise_cons

end ClusterAlgebras

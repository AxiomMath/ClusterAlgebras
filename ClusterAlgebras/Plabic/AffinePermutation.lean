/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Bounded affine permutations, bridge pairs and length

Fix an integer `b ≥ 1`. A map `f : ℤ → ℤ` with `f (n + b) = f n + b` for all `n` induces a map
`n + bℤ ↦ f n + bℤ` of `ℤ/bℤ`, and `f` is a bijection if and only if this residue map is one.
An `(a, b)`-bounded affine permutation is such a bijection with `n ≤ f n ≤ n + b` for every `n` and
`∑_{i=1}^b (f i - i) = a b`; these are the affinizations of decorated permutations on `b` letters
with `a` anti-excedances.

An integer `n` is a fixed point of `f` modulo `b` when `f n ≡ n [ZMOD b]`. A bridge pair of `f` is
a pair `1 ≤ i < j ≤ b` with `f i < f j`, all of whose intermediate integers are fixed points modulo
`b` while `i` and `j` are not; a bounded affine permutation that is not equivalent to the identity
modulo `b` has one, and its values there satisfy `j ≤ f i < f j ≤ i + b`. The length of `f` counts
its inversions `(p, q)`, `p < q`, `f p > f q`, with `1 ≤ p ≤ b`; for a bounded affine permutation
all of whose integers are fixed points modulo `b` it is `a (b - a)`.

## Main definitions

* `ClusterAlgebras.affineResidueMap b f`: the map `n + bℤ ↦ f n + bℤ` of `ZMod b`.
* `ClusterAlgebras.IsBoundedAffinePerm a b f`: `f` is an `(a, b)`-bounded affine permutation.
* `ClusterAlgebras.IsFixedPointMod b f n`: `n` is a fixed point of `f` modulo `b`.
* `ClusterAlgebras.IsBridgePair b f i j`: `(i, j)` is a bridge pair of `f`.
* `ClusterAlgebras.IsInversion f p q` and `ClusterAlgebras.affineLength b f`: inversions and the
  length `ℓ(f) ∈ ℕ∞`.

## Main results

* `ClusterAlgebras.bijective_iff_bijective_affineResidueMap`: a map with `f (n + b) = f n + b` is
  bijective iff its residue map is.
* `ClusterAlgebras.IsBoundedAffinePerm.exists_isBridgePair`: a bounded affine permutation with a
  non-fixed point has a bridge pair.
* `ClusterAlgebras.IsInversion.lt_add`: inversions of a map with `n ≤ f n ≤ n + b` are short.
* `ClusterAlgebras.IsBoundedAffinePerm.affineLength_eq_of_forall_isFixedPointMod`: the length of
  an `(a, b)`-bounded affine permutation equivalent to the identity modulo `b` is `a (b - a)`.
* `ClusterAlgebras.IsBoundedAffinePerm.isBridgePair_values`: `j ≤ f i < f j ≤ i + b` at a bridge
  pair `(i, j)`.

## Implementation notes

* The integers `a` and `b` are natural numbers, cast to `ℤ`. FWZ's hypothesis `b ≥ 1`
  is dropped wherever the statement remains true without it: for `b = 0` a bounded map is the
  identity, every integer is a fixed point and the length is `0`.
* The residue map is computed on the representative `ZMod.cast x : ℤ` of a class `x`; it is
  independent of the representative when `f (n + b) = f n + b` (`affineResidueMap_intCast`).
* The length is the cardinality `Set.encard` in `ℕ∞` of the set of inversions with `1 ≤ p ≤ b`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras*, Chapter 7.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function

/-! ### Periodic maps and their residue maps -/

section Periodic

variable {b : ℕ} {f : ℤ → ℤ}

/-- If `f (n + b) = f n + b` for all `n`, then `f (n + m b) = f n + m b` for all `n, m`. -/
theorem apply_add_mul_of_apply_add (hf : ∀ n, f (n + b) = f n + b) (n m : ℤ) :
    f (n + m * b) = f n + m * b := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show n + ((k : ℤ) + 1) * b = n + k * b + b by ring, hf, ih]
    ring
  | pred k ih =>
    have := hf (n + (-(k : ℤ) - 1) * b)
    rw [show n + (-(k : ℤ) - 1) * b + b = n + -(k : ℤ) * b by ring, ih] at this
    linarith

/-- Two integers with the same class in `ZMod b` differ by a multiple of `b`. -/
theorem exists_eq_add_mul_of_intCast_eq {n n' : ℤ} (h : (n : ZMod b) = n') :
    ∃ m : ℤ, n' = n + m * b := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub n n' b).1 h
  exact ⟨m, by linear_combination hm⟩

/-- The map `ℤ/bℤ → ℤ/bℤ`, `n + bℤ ↦ f n + bℤ`, induced by `f : ℤ → ℤ`. It is computed on the
representative `ZMod.cast x` of the class `x`; when `f (n + b) = f n + b` for all `n` it does not
depend on that choice (`affineResidueMap_intCast`). -/
def affineResidueMap (b : ℕ) (f : ℤ → ℤ) (x : ZMod b) : ZMod b :=
  (f (x.cast : ℤ) : ZMod b)

/-- The residue map sends the class of `n` to the class of `f n`. -/
theorem affineResidueMap_intCast (hf : ∀ n, f (n + b) = f n + b) (n : ℤ) :
    affineResidueMap b f n = f n := by
  obtain ⟨m, hm⟩ := exists_eq_add_mul_of_intCast_eq (ZMod.intCast_zmod_cast (n : ZMod b)).symm
  rw [affineResidueMap, hm, apply_add_mul_of_apply_add hf]
  simp

/-- **A periodic map is bijective iff it is bijective on residues.** If `f (n + b) = f n + b` for
every `n`, then `f` is a bijection if and only if the map `n + bℤ ↦ f n + bℤ` of `ℤ/bℤ` is. -/
@[cluster_algebras "lem_periodic_bijection_residues"]
theorem bijective_iff_bijective_affineResidueMap (hf : ∀ n, f (n + b) = f n + b) :
    Bijective f ↔ Bijective (affineResidueMap b f) := by
  refine ⟨fun hbij => ⟨fun x y hxy => ?_, fun y => ?_⟩, fun hbij => ⟨fun n n' h => ?_, fun k => ?_⟩⟩
  · obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨n', rfl⟩ := ZMod.intCast_surjective y
    rw [affineResidueMap_intCast hf, affineResidueMap_intCast hf] at hxy
    obtain ⟨m, hm⟩ := exists_eq_add_mul_of_intCast_eq hxy
    rw [← apply_add_mul_of_apply_add hf] at hm
    rw [hbij.1 hm]
    simp
  · obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
    obtain ⟨n, hn⟩ := hbij.2 k
    exact ⟨n, by rw [affineResidueMap_intCast hf, hn]⟩
  · have h' : (n : ZMod b) = n' := hbij.1 (by
      rw [affineResidueMap_intCast hf, affineResidueMap_intCast hf, h])
    obtain ⟨m, hm⟩ := exists_eq_add_mul_of_intCast_eq h'
    have := apply_add_mul_of_apply_add hf n m
    rw [← hm, ← h] at this
    linarith
  · obtain ⟨x, hx⟩ := hbij.2 (k : ZMod b)
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    rw [affineResidueMap_intCast hf] at hx
    obtain ⟨m, hm⟩ := exists_eq_add_mul_of_intCast_eq hx
    exact ⟨n + m * b, by rw [apply_add_mul_of_apply_add hf, hm]⟩

end Periodic

/-! ### Bounded affine permutations -/

/-- An **`(a, b)`-bounded affine permutation** is a bijection `f : ℤ → ℤ` with
`f (n + b) = f n + b` and `n ≤ f n ≤ n + b` for every `n`, and `∑_{i=1}^b (f i - i) = a b`. -/
@[cluster_algebras "def_bounded_affine_permutation"]
structure IsBoundedAffinePerm (a b : ℕ) (f : ℤ → ℤ) : Prop where
  /-- `f` is a bijection of `ℤ`. -/
  bijective : Bijective f
  /-- `f (n + b) = f n + b`. -/
  apply_add : ∀ n, f (n + b) = f n + b
  /-- `n ≤ f n`. -/
  le_apply : ∀ n, n ≤ f n
  /-- `f n ≤ n + b`. -/
  apply_le : ∀ n, f n ≤ n + b
  /-- `∑_{i=1}^b (f i - i) = a b`. -/
  sum_sub_eq : ∑ i ∈ Icc (1 : ℤ) b, (f i - i) = a * b

/-! ### Fixed points modulo `b` -/

/-- An integer `n` is a **fixed point of `f` modulo `b`** if `f n ≡ n [ZMOD b]`. A map is
*equivalent to the identity modulo `b`* when every integer is a fixed point modulo `b`. -/
@[cluster_algebras "def_affine_fixed_point"]
def IsFixedPointMod (b : ℕ) (f : ℤ → ℤ) (n : ℤ) : Prop :=
  f n ≡ n [ZMOD b]

section FixedPoint

variable {b : ℕ} {f : ℤ → ℤ} {n : ℤ}

/-- Being a fixed point modulo `b` is decidable. -/
instance : Decidable (IsFixedPointMod b f n) :=
  inferInstanceAs (Decidable (_ ≡ _ [ZMOD _]))

/-- For a map with `f (n + b) = f n + b`, being a fixed point modulo `b` depends only on the
residue class. -/
theorem isFixedPointMod_add_mul_iff (hf : ∀ n, f (n + b) = f n + b) (n m : ℤ) :
    IsFixedPointMod b f (n + m * b) ↔ IsFixedPointMod b f n := by
  simp [IsFixedPointMod, Int.ModEq, apply_add_mul_of_apply_add hf]

/-- If `f n = n + b`, then `n` is a fixed point of `f` modulo `b`. -/
theorem isFixedPointMod_of_eq_add (h : f n = n + b) : IsFixedPointMod b f n := by
  simp [IsFixedPointMod, Int.ModEq, h]

/-- If `f n = n`, then `n` is a fixed point of `f` modulo `b`. -/
theorem isFixedPointMod_of_eq (h : f n = n) : IsFixedPointMod b f n := by
  simp [IsFixedPointMod, h, Int.ModEq.refl]

/-- A fixed point `n` modulo `b` with `n ≤ f n ≤ n + b` has `f n = n` or `f n = n + b`. -/
theorem IsFixedPointMod.eq_or_eq_add (h : IsFixedPointMod b f n) (h₁ : n ≤ f n)
    (h₂ : f n ≤ n + b) : f n = n ∨ f n = n + b := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.1 h.symm
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · left
    simpa using ht
  · have hb' : (0 : ℤ) < b := by exact_mod_cast hb
    have ht0 : 0 ≤ t := by nlinarith
    have ht1 : t ≤ 1 := by nlinarith
    interval_cases t <;> simp_all

end FixedPoint

/-! ### Bridge pairs -/

/-- A **bridge pair** of `f : ℤ → ℤ` (for `b`) is a pair of integers `(i, j)` with
`1 ≤ i < j ≤ b`, `f i < f j`, every `h` with `i < h < j` a fixed point of `f` modulo `b`, and
neither `i` nor `j` a fixed point modulo `b`. -/
@[cluster_algebras "def_bridge_pair"]
structure IsBridgePair (b : ℕ) (f : ℤ → ℤ) (i j : ℤ) : Prop where
  /-- `1 ≤ i`. -/
  one_le : 1 ≤ i
  /-- `i < j`. -/
  lt : i < j
  /-- `j ≤ b`. -/
  le : j ≤ b
  /-- `f i < f j`. -/
  apply_lt_apply : f i < f j
  /-- Every integer strictly between `i` and `j` is a fixed point modulo `b`. -/
  isFixedPointMod_of_lt_of_lt : ∀ h, i < h → h < j → IsFixedPointMod b f h
  /-- `i` is not a fixed point modulo `b`. -/
  not_isFixedPointMod_left : ¬ IsFixedPointMod b f i
  /-- `j` is not a fixed point modulo `b`. -/
  not_isFixedPointMod_right : ¬ IsFixedPointMod b f j

section BridgePair

variable {a b : ℕ} {f : ℤ → ℤ}

/-- If `1 ≤ x < y ≤ b` are not fixed points modulo `b` and `f x < f y`, then `f` has a bridge
pair: take such a pair with `y - x` minimal. -/
theorem exists_isBridgePair_of_lt {x y : ℤ} (hx : 1 ≤ x) (hxy : x < y) (hy : y ≤ b)
    (hfxy : f x < f y) (hnx : ¬ IsFixedPointMod b f x) (hny : ¬ IsFixedPointMod b f y) :
    ∃ i j, IsBridgePair b f i j := by
  induction hd : (y - x).toNat using Nat.strong_induction_on generalizing x y with
  | _ d ih =>
    by_cases hall : ∀ h, x < h → h < y → IsFixedPointMod b f h
    · exact ⟨x, y, hx, hxy, hy, hfxy, hall, hnx, hny⟩
    · push Not at hall
      obtain ⟨h, hxh, hhy, hnh⟩ := hall
      by_cases hfh : f x < f h
      · exact ih (h - x).toNat (by omega) hx hxh (by omega) hfh hnx hnh rfl
      · exact ih (y - h).toNat (by omega) (by omega) hhy hy (by omega) hnh hny rfl

/-- Every integer `k` is `r + q b` for a representative `r = (k - 1) % b + 1 ∈ [1, b]`. -/
theorem sub_one_emod_add_one_spec {b : ℤ} (hb : 0 < b) (k : ℤ) :
    1 ≤ (k - 1) % b + 1 ∧ (k - 1) % b + 1 ≤ b ∧ k = (k - 1) % b + 1 + (k - 1) / b * b := by
  have h1 := Int.emod_nonneg (k - 1) hb.ne'
  have h2 := Int.emod_lt_of_pos (k - 1) hb
  have h3 := Int.emod_add_mul_ediv (k - 1) b
  exact ⟨by omega, by omega, by linear_combination -h3⟩

/-- If `f` is injective with `f (n + b) = f n + b`, `x` is not a fixed point modulo `b` and
`f x = y + q b`, then `y` is not a fixed point modulo `b`. -/
theorem not_isFixedPointMod_of_apply_eq_add_mul (hinj : Injective f)
    (hper : ∀ n, f (n + b) = f n + b) {x y q : ℤ} (hx : ¬ IsFixedPointMod b f x)
    (hxy : f x = y + q * b) : ¬ IsFixedPointMod b f y := by
  intro hfix
  obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.1 hfix
  have : f y = f (x + (-q - t) * b) := by
    rw [apply_add_mul_of_apply_add hper]
    linear_combination -ht - hxy
  exact hx (by rwa [← isFixedPointMod_add_mul_iff hper x (-q - t), ← hinj this])

/-- If `f` has no bridge pair, then `f` is antitone on the integers of `[1, b]` that are not
fixed points modulo `b`. -/
theorem apply_le_apply_of_not_exists_isBridgePair (hno : ¬ ∃ i j, IsBridgePair b f i j)
    {x y : ℤ} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ b) (hnx : ¬ IsFixedPointMod b f x)
    (hny : ¬ IsFixedPointMod b f y) : f y ≤ f x := by
  rcases hxy.lt_or_eq with hxy | rfl
  · exact not_lt.1 fun hlt => hno (exists_isBridgePair_of_lt hx hxy hy hlt hnx hny)
  · exact le_rfl

/-- **A bridge pair exists.** An `(a, b)`-bounded affine permutation with an integer that is not
a fixed point modulo `b` has a bridge pair. -/
@[cluster_algebras "lem_affine_adjacent_pair"]
theorem IsBoundedAffinePerm.exists_isBridgePair (hf : IsBoundedAffinePerm a b f)
    (h : ∃ n, ¬ IsFixedPointMod b f n) : ∃ i j, IsBridgePair b f i j := by
  obtain ⟨n, hn⟩ := h
  have hper := hf.apply_add
  have hb : (0 : ℤ) < b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exfalso
      have := hf.le_apply n
      have := hf.apply_le n
      exact hn (isFixedPointMod_of_eq (by omega))
    · exact_mod_cast hb
  by_contra hno
  set N := (Icc (1 : ℤ) b).filter (fun x => ¬ IsFixedPointMod b f x) with hN
  have hmemN : ∀ x, x ∈ N ↔ 1 ≤ x ∧ x ≤ b ∧ ¬ IsFixedPointMod b f x := by
    simp [hN, and_assoc]
  have hne : N.Nonempty := by
    obtain ⟨h1, h2, h3⟩ := sub_one_emod_add_one_spec hb n
    refine ⟨(n - 1) % b + 1, (hmemN _).2 ⟨h1, h2, fun hfix => hn ?_⟩⟩
    rwa [h3, isFixedPointMod_add_mul_iff hper]
  set x₁ := N.min' hne
  set xₘ := N.max' hne
  obtain ⟨h1a, h1b, h1c⟩ := (hmemN x₁).1 (N.min'_mem hne)
  obtain ⟨hma, hmb, hmc⟩ := (hmemN xₘ).1 (N.max'_mem hne)
  have h1m : f xₘ ≤ f x₁ := apply_le_apply_of_not_exists_isBridgePair hno h1a
    (N.min'_le _ (N.max'_mem hne)) hmb h1c hmc
  have hm : xₘ < f xₘ :=
    lt_of_le_of_ne (hf.le_apply _) (fun e => hmc (isFixedPointMod_of_eq e.symm))
  obtain ⟨hya, hyb, hyc⟩ := sub_one_emod_add_one_spec hb (f x₁)
  set y := (f x₁ - 1) % b + 1
  set q := (f x₁ - 1) / b
  have hyN := (hmemN y).2 ⟨hya, hyb,
    not_isFixedPointMod_of_apply_eq_add_mul hf.bijective.1 hper h1c hyc⟩
  have hy1 : x₁ ≤ y := N.min'_le _ hyN
  have hym : y ≤ xₘ := N.le_max' _ hyN
  have hq1 : 1 ≤ q := by
    by_contra hq
    have : q * b ≤ 0 := by nlinarith
    linarith
  have hq2 : q ≤ 1 := by
    by_contra hq
    have := hf.apply_le x₁
    nlinarith
  have hfx : f x₁ = x₁ + b := by
    have := hf.apply_le x₁
    rw [le_antisymm hq2 hq1] at hyc
    omega
  exact h1c (isFixedPointMod_of_eq_add hfx)

/-- **Values at a bridge pair.** If `(i, j)` is a bridge pair of an `(a, b)`-bounded affine
permutation `f`, then `j ≤ f i < f j ≤ i + b`. -/
@[cluster_algebras "lem_bridge_pair_values"]
theorem IsBoundedAffinePerm.isBridgePair_values (hf : IsBoundedAffinePerm a b f) {i j : ℤ}
    (h : IsBridgePair b f i j) : j ≤ f i ∧ f i < f j ∧ f j ≤ i + b := by
  have hinj := hf.bijective.1
  have hper := hf.apply_add
  have := h.lt
  have := h.one_le
  have := h.le
  refine ⟨?_, h.apply_lt_apply, ?_⟩
  · have hi : f i ≠ i := fun e => h.not_isFixedPointMod_left (isFixedPointMod_of_eq e)
    have hi' := hf.le_apply i
    by_contra! hlt
    have hfix := h.isFixedPointMod_of_lt_of_lt (f i) (by omega) hlt
    rcases hfix.eq_or_eq_add (hf.le_apply _) (hf.apply_le _) with e | e
    · have := hinj e
      omega
    · have e' := hper (f i - b)
      rw [sub_add_cancel, e] at e'
      have := hinj (show f (f i - b) = f i by linarith)
      omega
  · have hj : f j ≠ j + b := fun e =>
      h.not_isFixedPointMod_right (isFixedPointMod_of_eq_add e)
    have hj' := hf.apply_le j
    by_contra! hlt
    have hfix := h.isFixedPointMod_of_lt_of_lt (f j - b) (by omega) (by omega)
    rcases hfix.eq_or_eq_add (hf.le_apply _) (hf.apply_le _) with e | e
    · have e' := hper (f j - b)
      rw [e, sub_add_cancel] at e'
      have := hinj e'
      omega
    · rw [sub_add_cancel] at e
      have := hinj e
      omega

end BridgePair

/-! ### Inversions and length -/

/-- An **inversion** of `f : ℤ → ℤ` is a pair `(p, q)` of integers with `p < q` and
`f p > f q`. -/
@[cluster_algebras "def_affine_length"]
def IsInversion (f : ℤ → ℤ) (p q : ℤ) : Prop :=
  p < q ∧ f q < f p

/-- The **length** `ℓ(f) ∈ ℕ∞` of `f : ℤ → ℤ` (for `b`): the number of inversions `(p, q)` of `f`
with `1 ≤ p ≤ b`. -/
@[cluster_algebras "def_affine_length"]
noncomputable def affineLength (b : ℕ) (f : ℤ → ℤ) : ℕ∞ :=
  {pq : ℤ × ℤ | 1 ≤ pq.1 ∧ pq.1 ≤ b ∧ IsInversion f pq.1 pq.2}.encard

section Length

variable {a b : ℕ} {f : ℤ → ℤ}

/-- **Inversions are short.** If `n ≤ f n ≤ n + b` for every `n` and `(p, q)` is an inversion of
`f`, then `q < p + b`. -/
@[cluster_algebras "lem_affine_inversion_short"]
theorem IsInversion.lt_add (h₁ : ∀ n, n ≤ f n) (h₂ : ∀ n, f n ≤ n + b) {p q : ℤ}
    (h : IsInversion f p q) : q < p + b := by
  by_contra hq
  have := h₁ q
  have := h₂ p
  have := h.2
  omega

/-- The length of a map with `n ≤ f n ≤ n + b` for every `n` is finite. -/
theorem affineLength_ne_top (h₁ : ∀ n, n ≤ f n) (h₂ : ∀ n, f n ≤ n + b) :
    affineLength b f ≠ ⊤ := by
  refine (Set.encard_lt_top_iff.2 ?_).ne
  refine ((Icc (1 : ℤ) b ×ˢ Icc (1 : ℤ) (2 * b)).finite_toSet).subset ?_
  rintro ⟨p, q⟩ ⟨hp1, hpb, hinv⟩
  have := hinv.lt_add h₁ h₂
  have := hinv.1
  simp only [coe_product, Set.mem_prod, mem_coe, mem_Icc]
  omega

/-- If every value of `f` is `n` or `n + b`, then an inversion `(p, q)` of `f` has `f p = p + b`
and `f q = q`. -/
theorem IsInversion.apply_eq_of_forall_eq_or_eq_add (hval : ∀ n, f n = n ∨ f n = n + b)
    {p q : ℤ} (h : IsInversion f p q) : f p = p + b ∧ f q = q := by
  obtain ⟨hpq, hfqp⟩ := h
  refine ⟨?_, ?_⟩ <;> rcases hval p with hp | hp <;> rcases hval q with hq | hq <;> omega

/-- An `(a, b)`-bounded affine permutation equivalent to the identity modulo `b`, with `0 < b`,
has exactly `a` integers `i ∈ [1, b]` with `f i = i + b`. -/
theorem IsBoundedAffinePerm.card_filter_apply_eq_add (hf : IsBoundedAffinePerm a b f)
    (hfix : ∀ n, IsFixedPointMod b f n) (hb : 0 < b) :
    ((Icc (1 : ℤ) b).filter (fun i => f i = i + b)).card = a := by
  have hsum := hf.sum_sub_eq
  rw [sum_congr rfl (g := fun i => if f i = i + b then (b : ℤ) else 0) (fun i _ => by
    rcases (hfix i).eq_or_eq_add (hf.le_apply i) (hf.apply_le i) with h | h <;>
      simp [h, hb.ne']), ← sum_filter, sum_const, nsmul_eq_mul] at hsum
  exact_mod_cast mul_right_cancel₀ (by exact_mod_cast hb.ne' : (b : ℤ) ≠ 0) hsum

/-- An `(a, b)`-bounded affine permutation equivalent to the identity modulo `b`, with `0 < b`,
has exactly `b - a` integers `i ∈ [1, b]` with `f i = i`. -/
theorem IsBoundedAffinePerm.card_filter_apply_eq (hf : IsBoundedAffinePerm a b f)
    (hfix : ∀ n, IsFixedPointMod b f n) (hb : 0 < b) :
    ((Icc (1 : ℤ) b).filter (fun i => f i = i)).card = b - a := by
  have h := card_filter_add_card_filter_not (s := Icc (1 : ℤ) b) (fun i => f i = i + b)
  have hfilt : (Icc (1 : ℤ) b).filter (fun i => ¬ f i = i + b) =
      (Icc (1 : ℤ) b).filter (fun i => f i = i) :=
    filter_congr fun i _ => ⟨((hfix i).eq_or_eq_add (hf.le_apply i) (hf.apply_le i)).resolve_right,
      fun h => by omega⟩
  rw [hfilt, hf.card_filter_apply_eq_add hfix hb, Int.card_Icc] at h
  omega

/-- **Length of a map equivalent to the identity.** An `(a, b)`-bounded affine permutation all of
whose integers are fixed points modulo `b` has length `a (b - a)`. -/
@[cluster_algebras "lem_affine_identity_length"]
theorem IsBoundedAffinePerm.affineLength_eq_of_forall_isFixedPointMod
    (hf : IsBoundedAffinePerm a b f) (hfix : ∀ n, IsFixedPointMod b f n) :
    affineLength b f = (a * (b - a) : ℕ) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp only [Nat.zero_sub, mul_zero, Nat.cast_zero, affineLength, Set.encard_eq_zero]
    ext ⟨p, q⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    omega
  have hval : ∀ n, f n = n ∨ f n = n + b := fun n =>
    (hfix n).eq_or_eq_add (hf.le_apply n) (hf.apply_le n)
  set I := (Icc (1 : ℤ) b).filter (fun i => f i = i + b) with hI
  set I' := (Icc (1 : ℤ) b).filter (fun i => f i = i) with hI'
  let φ : ℤ × ℤ → ℤ × ℤ := fun pr => (pr.1, if pr.1 < pr.2 then pr.2 else pr.2 + b)
  have hset : {pq : ℤ × ℤ | 1 ≤ pq.1 ∧ pq.1 ≤ b ∧ IsInversion f pq.1 pq.2} =
      ↑((I ×ˢ I').image φ) := by
    ext ⟨p, q⟩
    simp only [Set.mem_setOf_eq, coe_image, coe_product, Set.mem_image, Set.mem_prod,
      mem_coe, hI, hI', mem_filter, mem_Icc, Prod.exists, Prod.mk.injEq, φ]
    constructor
    · rintro ⟨hp1, hpb, hinv⟩
      have hq := hinv.lt_add hf.le_apply hf.apply_le
      obtain ⟨hfp, hfq⟩ := hinv.apply_eq_of_forall_eq_or_eq_add hval
      obtain ⟨hpq, -⟩ := hinv
      by_cases hqb : q ≤ b
      · exact ⟨p, q, ⟨⟨⟨hp1, hpb⟩, hfp⟩, ⟨by omega, hqb⟩, hfq⟩, rfl, by simp [hpq]⟩
      · have e := hf.apply_add (q - b)
        rw [sub_add_cancel, hfq] at e
        refine ⟨p, q - b, ⟨⟨⟨hp1, hpb⟩, hfp⟩, ⟨by omega, by omega⟩, by omega⟩, rfl, ?_⟩
        rw [if_neg (by omega)]
        ring
    · rintro ⟨x, r, ⟨⟨⟨hp1, hpb⟩, hfp⟩, ⟨hr1, hrb⟩, hfr⟩, rfl, rfl⟩
      refine ⟨hp1, hpb, ?_⟩
      split_ifs with hpr
      · exact ⟨hpr, by omega⟩
      · have hrp : r ≠ x := by
          rintro rfl
          omega
        have e := hf.apply_add r
        exact ⟨by omega, by omega⟩
  have hinj : Set.InjOn φ ↑(I ×ˢ I') := by
    rintro ⟨p, r⟩ hpr ⟨p', r'⟩ hpr' e
    simp only [coe_product, Set.mem_prod, mem_coe, hI, hI', mem_filter, mem_Icc] at hpr hpr'
    simp only [φ, Prod.mk.injEq] at e
    obtain ⟨rfl, e⟩ := e
    simp only [Prod.mk.injEq, true_and]
    split_ifs at e <;> omega
  rw [affineLength, hset, Set.encard_coe_eq_coe_finsetCard, card_image_of_injOn hinj,
    card_product, hf.card_filter_apply_eq_add hfix hb, hf.card_filter_apply_eq hfix hb]

end Length

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.AffinePermutation
public import ClusterAlgebras.Plabic.DecoratedPermutation

/-!
# The affinization of a decorated permutation

Let `π̃ = (π, ε)` be a decorated permutation on `b` letters. Its *affinization* is the map
`f_π̃ : ℤ → ℤ` with, for a letter `i ∈ [1, b]`, `f_π̃(i) = π(i)` if `π(i) > i` or `i` is a black
fixed point, and `f_π̃(i) = π(i) + b` if `π(i) < i` or `i` is a white fixed point; it is extended
to all of `ℤ` by `f_π̃(i + m b) = f_π̃(i) + m b`. It satisfies `f_π̃(n + b) = f_π̃(n) + b` and
`n ≤ f_π̃(n) ≤ n + b`, and its displacements over `[1, b]` add up to `a(π̃) b`; it is therefore an
`(a(π̃), b)`-bounded affine permutation.

Conversely a map `f` with `n ≤ f(n) ≤ n + b` determines `π_f(i) = f(i) mod b` and, at a fixed point
`i` of `π_f`, the colour black if `f(i) = i` and white otherwise. For an `(a, b)`-bounded affine
permutation `f`, `π_f` is a permutation, `π̃_f = (π_f, ε_f)` has `a` anti-excedances, and the two
constructions are mutually inverse: `π̃ ↦ f_π̃` is a bijection from the decorated permutations on
`b` letters with `a` anti-excedances onto the `(a, b)`-bounded affine permutations. The
affinization of `π̃_{a,b}` is `n ↦ n + a`.

## Main definitions

* `ClusterAlgebras.letterMod b hb n`: the letter `n mod b` of `[1, b]`.
* `ClusterAlgebras.DecoratedPerm.affinization π`: the affinization `f_π̃`.
* `ClusterAlgebras.affineResidue b f`, `ClusterAlgebras.affineColour b f`, and
  `ClusterAlgebras.IsBoundedAffinePerm.decoratedPerm`: the decorated permutation `π̃_f`.

## Main results

* `ClusterAlgebras.DecoratedPerm.affinization_add`: `f_π̃(n + b) = f_π̃(n) + b`.
* `ClusterAlgebras.DecoratedPerm.le_affinization`, `ClusterAlgebras.DecoratedPerm.affinization_le`:
  `n ≤ f_π̃(n) ≤ n + b`.
* `ClusterAlgebras.DecoratedPerm.sum_affinization_sub`: `∑_{i=1}^b (f_π̃(i) - i) = a(π̃) b`.
* `ClusterAlgebras.DecoratedPerm.isBoundedAffinePerm_affinization`: `f_π̃` is an
  `(a(π̃), b)`-bounded affine permutation.
* `ClusterAlgebras.bijective_affineResidue`: `π_f` is a permutation.
* `ClusterAlgebras.IsBoundedAffinePerm.numAntiExcedances_decoratedPerm`: `a(π̃_f) = a`.
* `ClusterAlgebras.DecoratedPerm.decoratedPerm_affinization`: `π̃_{f_π̃} = π̃`.
* `ClusterAlgebras.IsBoundedAffinePerm.affinization_decoratedPerm`: `f_{π̃_f} = f`.
* `ClusterAlgebras.DecoratedPerm.bijOn_affinization`: `π̃ ↦ f_π̃` is a bijection onto the
  `(a, b)`-bounded affine permutations.
* `ClusterAlgebras.DecoratedPerm.affinization_topCell`: `f_{π̃_{a,b}}(n) = n + a`.

## Implementation notes

* The letters `[1, b]` are `Fin b`, indexed from `0`: the element `i : Fin b` is the letter
  `i.val + 1`, which is the integer `(i : ℤ) + 1`. Thus `letterMod b hb n` is the element of
  `Fin b` with value `(n - 1) % b`, and `f_π̃((i : ℤ) + 1)` is computed from `π.perm i`.
* The affinization is defined for every `b`; for `b = 0` (no letters) it is the identity, the only
  map with `n ≤ f(n) ≤ n + 0`. With this convention every statement about the affinization alone
  holds for all `b`, and the hypothesis `b ≥ 1` is only needed in
  `IsBoundedAffinePerm.numAntiExcedances_decoratedPerm` and `DecoratedPerm.bijOn_affinization`.
* `affineResidue b f` and `affineColour b f` are defined for every `f`, the colour at every letter;
  only its values at the fixed points of `π_f` enter `π̃_f`. The decorated permutation `π̃_f`
  itself is `IsBoundedAffinePerm.decoratedPerm`, which needs `π_f` to be a permutation.
* The bijection `DecoratedPerm.bijOn_affinization` is `Set.BijOn` between the set of decorated
  permutations with `a` anti-excedances and the set of `(a, b)`-bounded affine permutations.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7.
-/

@[expose] public section

open Finset Function

namespace ClusterAlgebras

/-! ### Letters modulo `b` -/

section LetterMod

variable {b : ℕ}

/-- The letter `n mod b` of `[1, b]` congruent to the integer `n` modulo `b`, for `b ≥ 1`. As the
letter `ℓ` is `ℓ - 1 : Fin b`, this is the element of `Fin b` with value `(n - 1) % b`. -/
def letterMod (b : ℕ) (hb : 0 < b) (n : ℤ) : Fin b :=
  ⟨((n - 1) % b).toNat, by
    have h1 := Int.emod_nonneg (n - 1) (b := b) (by omega)
    have h2 := Int.emod_lt_of_pos (n - 1) (b := b) (by omega)
    omega⟩

/-- The value of `letterMod b hb n`, as an integer, is `(n - 1) % b`. -/
theorem letterMod_val (hb : 0 < b) (n : ℤ) : ((letterMod b hb n : ℕ) : ℤ) = (n - 1) % b := by
  have h1 := Int.emod_nonneg (n - 1) (b := b) (by omega)
  simp only [letterMod]
  omega

/-- `n` is the integer of its letter `letterMod b hb n` plus `⌊(n - 1) / b⌋ b`. -/
theorem letterMod_add_ediv_mul (hb : 0 < b) (n : ℤ) :
    ((letterMod b hb n : ℕ) : ℤ) + 1 + (n - 1) / b * b = n := by
  rw [letterMod_val]
  linarith [Int.emod_add_mul_ediv (n - 1) b]

/-- The letter of `i + m b` is `i`. -/
theorem letterMod_add_mul (hb : 0 < b) (i : Fin b) (m : ℤ) :
    letterMod b hb ((i : ℕ) + 1 + m * b) = i := by
  ext
  have h := letterMod_val hb ((i : ℕ) + 1 + m * b)
  rw [show ((i : ℕ) : ℤ) + 1 + m * b - 1 = (i : ℕ) + m * b by ring, Int.add_mul_emod_self_right,
    Int.emod_eq_of_lt (by omega) (by have := i.isLt; omega)] at h
  exact_mod_cast h

/-- The letter of the integer `i` is `i`. -/
theorem letterMod_natCast_add_one (hb : 0 < b) (i : Fin b) :
    letterMod b hb ((i : ℕ) + 1) = i := by
  simpa using letterMod_add_mul hb i 0

/-- The letter of `n` is `i` exactly when `n = i + m b` for some `m`. -/
theorem letterMod_eq_iff (hb : 0 < b) (n : ℤ) (i : Fin b) :
    letterMod b hb n = i ↔ ∃ m : ℤ, n = (i : ℕ) + 1 + m * b := by
  constructor
  · rintro rfl
    exact ⟨_, (letterMod_add_ediv_mul hb n).symm⟩
  · rintro ⟨m, rfl⟩
    exact letterMod_add_mul hb i m

/-- The class modulo `b` of an integer is the class of its letter. -/
theorem intCast_eq_letterMod (hb : 0 < b) (n : ℤ) :
    (n : ZMod b) = ((((letterMod b hb n : ℕ) : ℤ) + 1 : ℤ) : ZMod b) := by
  conv_lhs => rw [← letterMod_add_ediv_mul hb n]
  push_cast
  simp

/-- A sum over `[1, b] ⊆ ℤ` is a sum over the letters `Fin b`. -/
theorem sum_Icc_one_eq_sum_fin {M : Type*} [AddCommMonoid M] (b : ℕ) (g : ℤ → M) :
    ∑ n ∈ Icc (1 : ℤ) b, g n = ∑ i : Fin b, g ((i : ℕ) + 1) := by
  symm
  refine Finset.sum_bij (fun i _ => ((i : ℕ) : ℤ) + 1) (fun i _ => ?_) (fun i _ j _ h => ?_)
    (fun n hn => ?_) (fun _ _ => rfl)
  · have := i.isLt
    simp only [mem_Icc]
    omega
  · exact Fin.ext (by omega)
  · simp only [mem_Icc] at hn
    exact ⟨⟨(n - 1).toNat, by omega⟩, mem_univ _, by dsimp only; omega⟩

end LetterMod

/-! ### The affinization -/

namespace DecoratedPerm

variable {b : ℕ} (π : DecoratedPerm b)

/-- The **affinization** `f_π̃ : ℤ → ℤ` of a decorated permutation `π̃ = (π, ε)` on `b` letters.
For a letter `i ∈ [1, b]`,
`f_π̃(i) = π(i)` if `π(i) > i`, `π(i) + b` if `π(i) < i`, `i + b` if `i` is a white fixed point,
and `i` if `i` is a black fixed point; and `f_π̃(i + m b) = f_π̃(i) + m b` for `m ∈ ℤ`. The letter
`i : Fin b` is the integer `(i : ℤ) + 1`. For `b = 0` this is the identity. -/
@[cluster_algebras "def_affinization"]
def affinization (n : ℤ) : ℤ :=
  if hb : 0 < b then
    (if letterMod b hb n < π.perm (letterMod b hb n) then
        ((π.perm (letterMod b hb n) : ℕ) : ℤ) + 1
      else if π.perm (letterMod b hb n) < letterMod b hb n then
        ((π.perm (letterMod b hb n) : ℕ) : ℤ) + 1 + b
      else if π.IsWhiteFixed (letterMod b hb n) then ((letterMod b hb n : ℕ) : ℤ) + 1 + b
      else ((letterMod b hb n : ℕ) : ℤ) + 1) + (n - 1) / b * b
  else n

/-- For `b = 0` the affinization is the identity. -/
theorem affinization_of_eq_zero (π : DecoratedPerm 0) (n : ℤ) : π.affinization n = n := by
  simp [affinization]

/-- The value of the affinization at a letter: `f_π̃(i) = π(i) + b` if `π(i) < i` or `i` is a white
fixed point, and `f_π̃(i) = π(i)` otherwise. -/
theorem affinization_natCast_add_one (i : Fin b) :
    π.affinization ((i : ℕ) + 1) =
      ((π.perm i : ℕ) : ℤ) + 1 + if π.perm i < i ∨ π.IsWhiteFixed i then (b : ℤ) else 0 := by
  have hb : 0 < b := i.pos
  have hq : (((i : ℕ) : ℤ) + 1 - 1) / b = 0 :=
    Int.ediv_eq_zero_of_lt (by omega) (by have := i.isLt; omega)
  simp only [affinization, dif_pos hb, letterMod_natCast_add_one, hq, zero_mul, add_zero]
  by_cases hfix : π.perm i = i
  · simp only [hfix, lt_irrefl, if_false, false_or]
    split_ifs <;> ring
  · have hw : ¬ π.IsWhiteFixed i := fun h => hfix h.1
    rcases lt_or_gt_of_ne hfix with h | h <;> simp [h, not_lt.2 h.le, hw]

/-- `f_π̃(i) = π(i)` when `π(i) > i`. -/
theorem affinization_of_lt {i : Fin b} (h : i < π.perm i) :
    π.affinization ((i : ℕ) + 1) = ((π.perm i : ℕ) : ℤ) + 1 := by
  rw [affinization_natCast_add_one, if_neg]
  · simp
  · rintro (h' | h')
    · exact lt_asymm h h'
    · exact h.ne' h'.1

/-- `f_π̃(i) = π(i) + b` when `π(i) < i`. -/
theorem affinization_of_gt {i : Fin b} (h : π.perm i < i) :
    π.affinization ((i : ℕ) + 1) = ((π.perm i : ℕ) : ℤ) + 1 + b := by
  rw [affinization_natCast_add_one, if_pos (Or.inl h)]

/-- `f_π̃(i) = i + b` at a white fixed point `i`. -/
theorem affinization_of_isWhiteFixed {i : Fin b} (h : π.IsWhiteFixed i) :
    π.affinization ((i : ℕ) + 1) = ((i : ℕ) : ℤ) + 1 + b := by
  rw [affinization_natCast_add_one, if_pos (Or.inr h), h.perm_apply_eq]

/-- `f_π̃(i) = i` at a black fixed point `i`. -/
theorem affinization_of_isBlackFixed {i : Fin b} (h : π.IsBlackFixed i) :
    π.affinization ((i : ℕ) + 1) = ((i : ℕ) : ℤ) + 1 := by
  rw [affinization_natCast_add_one, if_neg, h.perm_apply_eq]
  · simp
  · rintro (h' | h')
    · rw [h.perm_apply_eq] at h'
      exact lt_irrefl _ h'
    · exact π.not_isBlackFixed_of_isWhiteFixed h' h

/-- The affinization at `n`, written as `i + m b` with `i` a letter. -/
theorem affinization_eq (hb : 0 < b) (n : ℤ) :
    π.affinization n = π.affinization ((letterMod b hb n : ℕ) + 1) + (n - 1) / b * b := by
  have hq : (((letterMod b hb n : ℕ) : ℤ) + 1 - 1) / b = 0 :=
    Int.ediv_eq_zero_of_lt (by omega) (by have := (letterMod b hb n).isLt; omega)
  conv_rhs => simp only [affinization, dif_pos hb, letterMod_natCast_add_one, hq, zero_mul,
    add_zero]
  simp only [affinization, dif_pos hb]

/-- `f_π̃(i + m b) = f_π̃(i) + m b` for a letter `i`. -/
theorem affinization_natCast_add_one_add_mul (i : Fin b) (m : ℤ) :
    π.affinization ((i : ℕ) + 1 + m * b) = π.affinization ((i : ℕ) + 1) + m * b := by
  have hb : 0 < b := i.pos
  rw [π.affinization_eq hb, letterMod_add_mul]
  congr 2
  rw [show ((i : ℕ) : ℤ) + 1 + m * b - 1 = (i : ℕ) + m * b by ring,
    Int.add_mul_ediv_right _ _ (by omega), Int.ediv_eq_zero_of_lt (by omega)
      (by have := i.isLt; omega), zero_add]

/-- **The affinization is periodic**: `f_π̃(n + b) = f_π̃(n) + b`. -/
@[cluster_algebras "lem_affinization_periodic"]
theorem affinization_add (n : ℤ) : π.affinization (n + b) = π.affinization n + b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [affinization]
  · have hn := letterMod_add_ediv_mul hb n
    set i := letterMod b hb n
    set q := (n - 1) / b
    rw [← hn, show ((i : ℕ) : ℤ) + 1 + q * b + b = (i : ℕ) + 1 + (q + 1) * b by ring,
      affinization_natCast_add_one_add_mul, affinization_natCast_add_one_add_mul]
    ring

/-- The displacement `f_π̃(i) - i` at a letter lies in `[0, b]`. -/
private theorem affinization_natCast_add_one_bounds (i : Fin b) :
    ((i : ℕ) : ℤ) + 1 ≤ π.affinization ((i : ℕ) + 1) ∧
      π.affinization ((i : ℕ) + 1) ≤ (i : ℕ) + 1 + b := by
  rw [affinization_natCast_add_one]
  have := (π.perm i).isLt
  split_ifs with h
  · rcases h with h | h
    · rw [Fin.lt_def] at h
      omega
    · rw [h.perm_apply_eq]
      omega
  · have h' : i ≤ π.perm i := not_lt.1 fun h' => h (Or.inl h')
    rw [Fin.le_def] at h'
    omega

/-- **Bounds on the affinization**, lower bound: `n ≤ f_π̃(n)`. -/
@[cluster_algebras "lem_affinization_bounds"]
theorem le_affinization (n : ℤ) : n ≤ π.affinization n := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [affinization]
  · have hn := letterMod_add_ediv_mul hb n
    rw [π.affinization_eq hb]
    have := (π.affinization_natCast_add_one_bounds (letterMod b hb n)).1
    omega

/-- **Bounds on the affinization**, upper bound: `f_π̃(n) ≤ n + b`. -/
@[cluster_algebras "lem_affinization_bounds"]
theorem affinization_le (n : ℤ) : π.affinization n ≤ n + b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [affinization]
  · have hn := letterMod_add_ediv_mul hb n
    rw [π.affinization_eq hb]
    have := (π.affinization_natCast_add_one_bounds (letterMod b hb n)).2
    omega

/-- **The displacement sum of the affinization**: `∑_{i=1}^b (f_π̃(i) - i) = a(π̃) b`. -/
@[cluster_algebras "lem_affinization_sum"]
theorem sum_affinization_sub :
    ∑ n ∈ Icc (1 : ℤ) b, (π.affinization n - n) = π.numAntiExcedances * b := by
  rw [sum_Icc_one_eq_sum_fin]
  simp only [affinization_natCast_add_one]
  have hperm := Equiv.sum_comp π.perm (fun j : Fin b => ((j : ℕ) : ℤ))
  have hsplit : ∀ i : Fin b,
      ((π.perm i : ℕ) : ℤ) + 1 + (if π.perm i < i ∨ π.IsWhiteFixed i then (b : ℤ) else 0) -
        (((i : ℕ) : ℤ) + 1) =
      (((π.perm i : ℕ) : ℤ) - ((i : ℕ) : ℤ)) +
        if π.perm i < i ∨ π.IsWhiteFixed i then (b : ℤ) else 0 := fun i => by ring
  simp only [hsplit, sum_add_distrib, sum_sub_distrib, hperm, sub_self, zero_add]
  rw [← sum_filter, sum_const, nsmul_eq_mul, numAntiExcedances_eq_card]

/-- **The affinization is bounded**: `f_π̃` is an `(a(π̃), b)`-bounded affine permutation. -/
@[cluster_algebras "lem_affinization_bounded"]
theorem isBoundedAffinePerm_affinization :
    IsBoundedAffinePerm π.numAntiExcedances b π.affinization where
  bijective := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact (funext π.affinization_of_eq_zero : π.affinization = id) ▸ bijective_id
    · haveI : NeZero b := ⟨hb.ne'⟩
      rw [bijective_iff_bijective_affineResidueMap π.affinization_add]
      refine Finite.surjective_iff_bijective.1 fun x => ?_
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
      refine ⟨(((π.perm.symm (letterMod b hb n) : ℕ) : ℤ) + 1 : ℤ), ?_⟩
      rw [affineResidueMap_intCast π.affinization_add, affinization_natCast_add_one,
        Equiv.apply_symm_apply, intCast_eq_letterMod hb n]
      split_ifs <;> push_cast <;> simp
  apply_add := π.affinization_add
  le_apply := π.le_affinization
  apply_le := π.affinization_le
  sum_sub_eq := π.sum_affinization_sub

end DecoratedPerm

/-! ### The decorated permutation of a bounded map -/

section Residue

variable {a b : ℕ} {f : ℤ → ℤ}

/-- The map `π_f : [1, b] → [1, b]`, `π_f(i) = f(i) mod b`, of the decorated permutation `π̃_f` of
`f : ℤ → ℤ`; the letter `i : Fin b` is the integer `(i : ℤ) + 1`. It is a permutation when `f` is
an `(a, b)`-bounded affine permutation (`bijective_affineResidue`). -/
@[cluster_algebras "def_affine_decorated_permutation"]
def affineResidue (b : ℕ) (f : ℤ → ℤ) (i : Fin b) : Fin b :=
  letterMod b i.pos (f ((i : ℕ) + 1))

/-- The colouring `ε_f` of the decorated permutation `π̃_f` of `f : ℤ → ℤ`: black at a letter `i`
with `f(i) = i`, white otherwise. Only its values at the fixed points of `π_f` enter `π̃_f`. -/
@[cluster_algebras "def_affine_decorated_permutation"]
def affineColour (b : ℕ) (f : ℤ → ℤ) (i : Fin b) : Shade :=
  if f ((i : ℕ) + 1) = (i : ℕ) + 1 then .black else .white

/-- For `n ≤ f(n) ≤ n + b`, `f(i) = π_f(i) + b` if `f(i) > b`, and `f(i) = π_f(i)` otherwise. -/
theorem apply_natCast_add_one_eq_affineResidue (h₁ : ∀ n, n ≤ f n) (h₂ : ∀ n, f n ≤ n + b)
    (i : Fin b) :
    f ((i : ℕ) + 1) = ((affineResidue b f i : ℕ) : ℤ) + 1 +
      if (b : ℤ) < f ((i : ℕ) + 1) then (b : ℤ) else 0 := by
  have hs := letterMod_add_ediv_mul i.pos (f ((i : ℕ) + 1))
  have hj : ((letterMod b i.pos (f ((i : ℕ) + 1)) : ℕ) : ℤ) < b := by
    exact_mod_cast (letterMod b i.pos (f ((i : ℕ) + 1))).isLt
  have hi : ((i : ℕ) : ℤ) < b := by exact_mod_cast i.isLt
  have l := h₁ ((i : ℕ) + 1)
  have u := h₂ ((i : ℕ) + 1)
  have hb' : (0 : ℤ) < b := by exact_mod_cast i.pos
  simp only [affineResidue]
  set j := letterMod b i.pos (f ((i : ℕ) + 1))
  set q := (f ((i : ℕ) + 1) - 1) / b
  have hq0 : 0 ≤ q := by
    by_contra hq
    push Not at hq
    nlinarith
  have hq1 : q ≤ 1 := by
    by_contra hq
    push Not at hq
    nlinarith
  interval_cases q <;> split_ifs <;> omega

/-- **The residue map of a bounded affine permutation is a permutation**: `π_f` is a bijection of
`[1, b]`. -/
@[cluster_algebras "lem_affine_residue_permutation"]
theorem bijective_affineResidue (hf : IsBoundedAffinePerm a b f) :
    Bijective (affineResidue b f) := by
  refine Finite.injective_iff_bijective.1 fun i j hij => ?_
  have hb := i.pos
  have hR := (bijective_iff_bijective_affineResidueMap hf.apply_add).1 hf.bijective
  have e : ((((i : ℕ) : ℤ) + 1 : ℤ) : ZMod b) = ((((j : ℕ) : ℤ) + 1 : ℤ) : ZMod b) := by
    apply hR.1
    rw [affineResidueMap_intCast hf.apply_add, affineResidueMap_intCast hf.apply_add,
      intCast_eq_letterMod hb (f _), intCast_eq_letterMod hb (f _)]
    simp only [affineResidue] at hij
    rw [hij]
  obtain ⟨m, hm⟩ := exists_eq_add_mul_of_intCast_eq e
  calc i = letterMod b hb ((i : ℕ) + 1 + m * b) := (letterMod_add_mul hb i m).symm
    _ = letterMod b hb ((j : ℕ) + 1) := by rw [hm]
    _ = j := letterMod_natCast_add_one hb j

/-- The **decorated permutation `π̃_f = (π_f, ε_f)`** of an `(a, b)`-bounded affine permutation
`f`: `π_f(i) = f(i) mod b`, and a fixed point `i` of `π_f` is black if `f(i) = i` and white
otherwise. -/
@[cluster_algebras "def_affine_decorated_permutation"]
noncomputable def IsBoundedAffinePerm.decoratedPerm (hf : IsBoundedAffinePerm a b f) :
    DecoratedPerm b :=
  DecoratedPerm.ofColouring (Equiv.ofBijective _ (bijective_affineResidue hf)) (affineColour b f)

namespace IsBoundedAffinePerm

/-- The permutation of `π̃_f` sends `i` to the residue `f(i) mod b`. -/
@[simp]
theorem decoratedPerm_perm_apply (hf : IsBoundedAffinePerm a b f) (i : Fin b) :
    hf.decoratedPerm.perm i = affineResidue b f i :=
  rfl

/-- The colouring of `π̃_f` is `affineColour b f`. -/
theorem decoratedPerm_colour (hf : IsBoundedAffinePerm a b f) (i) :
    hf.decoratedPerm.colour i = affineColour b f i :=
  rfl

/-- `π̃_f` depends only on `f`. -/
theorem decoratedPerm_congr {g : ℤ → ℤ} (hf : IsBoundedAffinePerm a b f)
    (hg : IsBoundedAffinePerm a b g) (h : f = g) : hf.decoratedPerm = hg.decoratedPerm := by
  subst h
  rfl

/-- `i` is a white fixed point of `π̃_f` if and only if `π_f(i) = i` and `f(i) ≠ i`. -/
theorem isWhiteFixed_decoratedPerm_iff (hf : IsBoundedAffinePerm a b f) (i : Fin b) :
    hf.decoratedPerm.IsWhiteFixed i ↔
      affineResidue b f i = i ∧ f ((i : ℕ) + 1) ≠ (i : ℕ) + 1 := by
  simp [DecoratedPerm.IsWhiteFixed, decoratedPerm_colour, affineColour]

/-- The letters `i` with `π_f(i) < i` or `i` a white fixed point of `π̃_f` are those with
`f(i) > b`. -/
theorem lt_or_isWhiteFixed_decoratedPerm_iff (hf : IsBoundedAffinePerm a b f) (i : Fin b) :
    hf.decoratedPerm.perm i < i ∨ hf.decoratedPerm.IsWhiteFixed i ↔ (b : ℤ) < f ((i : ℕ) + 1) := by
  have hv := apply_natCast_add_one_eq_affineResidue hf.le_apply hf.apply_le i
  have l := hf.le_apply ((i : ℕ) + 1)
  have u := hf.apply_le ((i : ℕ) + 1)
  have hj := (affineResidue b f i).isLt
  have hi := i.isLt
  rw [decoratedPerm_perm_apply, isWhiteFixed_decoratedPerm_iff, Fin.lt_def, Fin.ext_iff]
  split_ifs at hv <;> omega

/-- **Anti-excedances of `π̃_f`**: for `b ≥ 1` and an `(a, b)`-bounded affine permutation `f`,
`a(π̃_f) = a`. -/
@[cluster_algebras "lem_affine_decorated_anti_excedances"]
theorem numAntiExcedances_decoratedPerm (hb : 0 < b) (hf : IsBoundedAffinePerm a b f) :
    hf.decoratedPerm.numAntiExcedances = a := by
  have hsum := hf.sum_sub_eq
  simp only [sum_Icc_one_eq_sum_fin] at hsum
  have hsplit : ∀ i : Fin b, f ((i : ℕ) + 1) - (((i : ℕ) : ℤ) + 1) =
      ((affineResidue b f i : ℕ) : ℤ) - (i : ℕ) +
        if (b : ℤ) < f ((i : ℕ) + 1) then (b : ℤ) else 0 := fun i => by
    have := apply_natCast_add_one_eq_affineResidue hf.le_apply hf.apply_le i
    split_ifs at this ⊢ <;> omega
  simp only [hsplit, sum_add_distrib, sum_sub_distrib] at hsum
  have hperm := Equiv.sum_comp hf.decoratedPerm.perm (fun j : Fin b => ((j : ℕ) : ℤ))
  simp only [decoratedPerm_perm_apply] at hperm
  rw [hperm, sub_self, zero_add, ← sum_filter, sum_const, nsmul_eq_mul] at hsum
  rw [DecoratedPerm.numAntiExcedances_eq_card,
    filter_congr (fun i _ => hf.lt_or_isWhiteFixed_decoratedPerm_iff i)]
  have hb' : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  exact_mod_cast mul_right_cancel₀ hb' hsum

/-- **`π̃ ↦ f_π̃` has a right inverse**: the affinization of `π̃_f` is `f`. -/
@[cluster_algebras "lem_affinization_right_inverse"]
theorem affinization_decoratedPerm (hf : IsBoundedAffinePerm a b f) :
    hf.decoratedPerm.affinization = f := by
  funext n
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [DecoratedPerm.affinization_of_eq_zero]
    exact le_antisymm (hf.le_apply n) (by simpa using hf.apply_le n)
  · rw [← letterMod_add_ediv_mul hb n, DecoratedPerm.affinization_natCast_add_one_add_mul,
      apply_add_mul_of_apply_add hf.apply_add, DecoratedPerm.affinization_natCast_add_one,
      if_congr (hf.lt_or_isWhiteFixed_decoratedPerm_iff _) rfl rfl, decoratedPerm_perm_apply,
      ← apply_natCast_add_one_eq_affineResidue hf.le_apply hf.apply_le]

end IsBoundedAffinePerm

end Residue

/-! ### The bijection -/

namespace DecoratedPerm

variable {b : ℕ} (π : DecoratedPerm b)

/-- **`π̃ ↦ f_π̃` has a left inverse**: `π̃_{f_π̃} = π̃`. -/
@[cluster_algebras "lem_affinization_left_inverse"]
theorem decoratedPerm_affinization {a : ℕ} (h : IsBoundedAffinePerm a b π.affinization) :
    h.decoratedPerm = π := by
  have hres : ∀ i, affineResidue b π.affinization i = π.perm i := by
    intro i
    simp only [affineResidue, affinization_natCast_add_one]
    split_ifs
    · simpa using letterMod_add_mul i.pos (π.perm i) 1
    · simpa using letterMod_add_mul i.pos (π.perm i) 0
  refine DecoratedPerm.ext (Equiv.ext hres) fun i h₁ h₂ => ?_
  have hb : (0 : ℤ) < b := by exact_mod_cast i.pos
  rw [IsBoundedAffinePerm.decoratedPerm_colour, affineColour]
  rcases π.isWhiteFixed_or_isBlackFixed h₂ with hw | hk
  · rw [affinization_of_isWhiteFixed _ hw, if_neg (by omega),
      (π.isWhiteFixed_iff_of_perm_apply_eq h₂).1 hw]
  · rw [affinization_of_isBlackFixed _ hk, if_pos rfl,
      (π.isBlackFixed_iff_of_perm_apply_eq h₂).1 hk]

/-- **Decorated permutations and bounded affine permutations.** For `b ≥ 1`, `π̃ ↦ f_π̃` is a
bijection from the decorated permutations on `b` letters with `a` anti-excedances onto the
`(a, b)`-bounded affine permutations. -/
@[cluster_algebras "lem_affinization_bijection"]
theorem bijOn_affinization (hb : 0 < b) (a : ℕ) :
    Set.BijOn (affinization (b := b)) {π | π.numAntiExcedances = a}
      {f | IsBoundedAffinePerm a b f} := by
  refine ⟨fun π hπ => ?_, fun π hπ σ _ h => ?_, fun f hf => ?_⟩
  · simp only [Set.mem_setOf_eq] at hπ ⊢
    rw [← hπ]
    exact π.isBoundedAffinePerm_affinization
  · simp only [Set.mem_setOf_eq] at hπ
    have hπ' : IsBoundedAffinePerm a b π.affinization := hπ ▸ π.isBoundedAffinePerm_affinization
    have hσ' : IsBoundedAffinePerm a b σ.affinization := h ▸ hπ'
    calc π = hπ'.decoratedPerm := (π.decoratedPerm_affinization hπ').symm
      _ = hσ'.decoratedPerm := IsBoundedAffinePerm.decoratedPerm_congr hπ' hσ' h
      _ = σ := σ.decoratedPerm_affinization hσ'
  · exact ⟨hf.decoratedPerm, hf.numAntiExcedances_decoratedPerm hb,
      hf.affinization_decoratedPerm⟩

/-- **The affinization of `π̃_{a,b}`** is `n ↦ n + a`, for `a ≤ b`. -/
@[cluster_algebras "lem_top_cell_affinization"]
theorem affinization_topCell {a : ℕ} (hab : a ≤ b) :
    (topCell a b).affinization = fun n : ℤ => n + a := by
  funext n
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain rfl : a = 0 := by omega
    simp [affinization_of_eq_zero]
  · rw [← letterMod_add_ediv_mul hb n, affinization_natCast_add_one_add_mul,
      affinization_natCast_add_one]
    set i := letterMod b hb n
    have hw : (topCell a b).IsWhiteFixed i ↔ (topCell a b).perm i = i ∧ a ≠ 0 := by
      simp [IsWhiteFixed]
    have hv := topCell_perm_apply_val a b i
    have hi := i.isLt
    simp only [hw, Fin.lt_def, Fin.ext_iff, hv]
    rcases lt_or_ge (i.val + a) b with h | h
    · rw [Nat.mod_eq_of_lt h]
      split_ifs <;> omega
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      split_ifs <;> omega

end DecoratedPerm

end ClusterAlgebras

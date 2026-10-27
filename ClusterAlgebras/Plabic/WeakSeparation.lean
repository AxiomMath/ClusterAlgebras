/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.List.Forall2
public import Mathlib.Order.Preorder.Finite

/-!
# Weak separation, Grassmann necklaces and positroids

The combinatorial vocabulary of FWZ's Section 7.13. Two `a`-element subsets `I, J` of `[1, b]` are
*weakly separated* (Leclerc–Zelevinsky) when no four elements, two of `I \ J` and two of `J \ I`,
alternate around the circle `1, …, b`; a collection of `a`-element subsets is weakly separated when
its members are pairwise weakly separated. A *Grassmann necklace* of type `(a, b)` is a sequence
`(I₁, …, I_b)` of `a`-element subsets with `I_{ℓ+1} ⊇ I_ℓ \ {ℓ}`, cyclically. The cyclic order
`<_ℓ` reads `[1, b]` starting at `ℓ`, through the rank `r_ℓ(x) ∈ [0, b - 1]`; it induces the
shifted Gale order `≤_ℓ` on `a`-element subsets, comparing their elements in increasing `<_ℓ`
order; and the *positroid* of a necklace `ℐ` is the set of `a`-element subsets `J` with
`I_ℓ ≤_ℓ J` for every `ℓ`.

## Main definitions

* `ClusterAlgebras.WeaklySeparated I J`: `I` and `J` are weakly separated.
* `ClusterAlgebras.IsWeaklySeparatedCollection a C`,
  `ClusterAlgebras.IsMaximalWeaklySeparatedCollection a C`: `C ⊆ ([b] choose a)` is a (maximal)
  weakly separated collection.
* `ClusterAlgebras.IsGrassmannNecklace a I`: `I` is a Grassmann necklace of type `(a, b)`.
* `ClusterAlgebras.cyclicRank ℓ x`, `ClusterAlgebras.cyclicLT ℓ x y`: the rank `r_ℓ(x)` and the
  cyclic order `x <_ℓ y`.
* `ClusterAlgebras.galeLE ℓ I J`: the order `I ≤_ℓ J` on `a`-element subsets.
* `ClusterAlgebras.positroid a I`: the positroid `ℳ_ℐ` of a Grassmann necklace.

## Main results

* `ClusterAlgebras.weaklySeparated_iff`: weak separation in terms of four alternating elements
  `p < q < r < s`, and `ClusterAlgebras.WeaklySeparated.symm`.
* `ClusterAlgebras.IsWeaklySeparatedCollection.exists_maximal`: every weakly separated collection
  lies in a maximal one.
* `ClusterAlgebras.cyclicRank_injective`, `ClusterAlgebras.cyclicRank_lt`,
  `ClusterAlgebras.exists_cyclicRank_eq`, `ClusterAlgebras.cyclicRank_add_one`,
  `ClusterAlgebras.cyclicLT_add_one_iff`: `r_ℓ` is a bijection onto `[0, b - 1]` with
  `r_ℓ(ℓ) = 0`, and `r_{ℓ+1}(x) = r_ℓ(x) - 1` for `x ≠ ℓ`.
* `ClusterAlgebras.galeLE_refl`, `ClusterAlgebras.galeLE.trans`,
  `ClusterAlgebras.galeLE.antisymm`: `≤_ℓ` is a partial order.

## Implementation notes

* The label set `[1, b]` is `Fin b`, read with a shift: the element `i : Fin b` is the label
  `i + 1`. The relations `i < j` of weak separation are invariant under this shift, and so is the
  rank: for `ℓ, x : Fin b`, `cyclicRank ℓ x` is `r_{ℓ+1}(x + 1)` in the labels of the text. A
  Grassmann necklace `(I₁, …, I_b)` is a function `I : Fin b → Finset (Fin b)` with `I ℓ` the set
  `I_{ℓ+1}`; the convention `I_{b+1} = I₁` is the addition of `Fin b`, which needs `b ≥ 1`
  (`NeZero b`), as in the text.
* Subsets of `[1, b]` are `Finset (Fin b)` and collections of them are
  `Finset (Finset (Fin b))`; the size `a` is a parameter of the predicates on collections.
  `WeaklySeparated` and `galeLE` are defined for all pairs of subsets, the text defining them for
  pairs of `a`-element subsets: for subsets of different sizes `WeaklySeparated` is not
  Leclerc–Zelevinsky's notion, and `galeLE` is false.
* The ordered lists `i₁ <_ℓ ⋯ <_ℓ iₐ` of the text enter `galeLE` only through their ranks: the
  list `cyclicRanks ℓ I` is the increasing list of the ranks `r_ℓ(i)`, `i ∈ I`, which is
  `(r_ℓ(i₁), …, r_ℓ(iₐ))`.
* A maximal weakly separated collection is Mathlib's `Maximal` for the inclusion order of
  `Finset (Finset (Fin b))`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras, Chapter 7*,
  Section 7.13.
-/

@[expose] public section

namespace ClusterAlgebras

variable {b : ℕ}

/-! ### Weak separation -/

section WeakSeparation

/-- Two subsets `I, J` of `[1, b]` are *weakly separated* if there are no `i, i' ∈ I \ J` and
`j, j' ∈ J \ I` with `i < j < i' < j'`, `j < i' < j' < i`, `i' < j' < i < j` or `j' < i < j < i'`.
FWZ use the notion for two `a`-element subsets. The element `i : Fin b` is the label `i + 1`; the
conditions are invariant under this shift. -/
@[cluster_algebras "def_weakly_separated"]
def WeaklySeparated (I J : Finset (Fin b)) : Prop :=
  ¬ ∃ i ∈ I \ J, ∃ j ∈ J \ I, ∃ i' ∈ I \ J, ∃ j' ∈ J \ I,
    (i < j ∧ j < i' ∧ i' < j') ∨ (j < i' ∧ i' < j' ∧ j' < i) ∨
      (i' < j' ∧ j' < i ∧ i < j) ∨ (j' < i ∧ i < j ∧ j < i')

/-- Weak separation is decidable. -/
instance : DecidableRel (WeaklySeparated (b := b)) := fun I J => by
  unfold WeaklySeparated; infer_instance

/-- `I` and `J` are weakly separated if and only if there are no `p < q < r < s` alternating
between `I \ J` and `J \ I`. -/
theorem weaklySeparated_iff {I J : Finset (Fin b)} :
    WeaklySeparated I J ↔ ¬ ∃ p q r s : Fin b, p < q ∧ q < r ∧ r < s ∧
      ((p ∈ I \ J ∧ q ∈ J \ I ∧ r ∈ I \ J ∧ s ∈ J \ I) ∨
        (p ∈ J \ I ∧ q ∈ I \ J ∧ r ∈ J \ I ∧ s ∈ I \ J)) := by
  unfold WeaklySeparated
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨i, hi, j, hj, i', hi', j', hj', ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩⟩
    · exact ⟨i, j, i', j', h1, h2, h3, .inl ⟨hi, hj, hi', hj'⟩⟩
    · exact ⟨j, i', j', i, h1, h2, h3, .inr ⟨hj, hi', hj', hi⟩⟩
    · exact ⟨i', j', i, j, h1, h2, h3, .inl ⟨hi', hj', hi, hj⟩⟩
    · exact ⟨j', i, j, i', h1, h2, h3, .inr ⟨hj', hi, hj, hi'⟩⟩
  · rintro ⟨p, q, r, s, h1, h2, h3, ⟨hp, hq, hr, hs⟩ | ⟨hp, hq, hr, hs⟩⟩
    · exact ⟨p, hp, q, hq, r, hr, s, hs, .inl ⟨h1, h2, h3⟩⟩
    · exact ⟨s, hs, p, hp, q, hq, r, hr, .inr (.inl ⟨h1, h2, h3⟩)⟩

/-- Weak separation is symmetric. -/
theorem WeaklySeparated.symm {I J : Finset (Fin b)} (h : WeaklySeparated I J) :
    WeaklySeparated J I := by
  rw [weaklySeparated_iff] at h ⊢
  rintro ⟨p, q, r, s, h1, h2, h3, h' | h'⟩
  exacts [h ⟨p, q, r, s, h1, h2, h3, .inr h'⟩, h ⟨p, q, r, s, h1, h2, h3, .inl h'⟩]

/-- `I` and `J` are weakly separated if and only if `J` and `I` are. -/
theorem weaklySeparated_comm {I J : Finset (Fin b)} : WeaklySeparated I J ↔ WeaklySeparated J I :=
  ⟨.symm, .symm⟩

/-- A set is weakly separated from itself. -/
@[simp]
theorem weaklySeparated_self (I : Finset (Fin b)) : WeaklySeparated I I := by
  simp [WeaklySeparated]

/-- A set is weakly separated from any set containing it. -/
theorem weaklySeparated_of_subset {I J : Finset (Fin b)} (h : I ⊆ J) : WeaklySeparated I J := by
  rintro ⟨i, hi, -⟩
  exact (Finset.mem_sdiff.1 hi).2 (h (Finset.mem_sdiff.1 hi).1)

end WeakSeparation

/-! ### Weakly separated collections -/

section Collection

/-- A collection `C` of subsets of `[1, b]` is a *weakly separated collection* (of `a`-element
subsets) if every member of `C` has `a` elements and any two members of `C` are weakly
separated. -/
@[cluster_algebras "def_weakly_separated_collection"]
def IsWeaklySeparatedCollection (a : ℕ) (C : Finset (Finset (Fin b))) : Prop :=
  C ⊆ Finset.powersetCard a Finset.univ ∧ ∀ I ∈ C, ∀ J ∈ C, WeaklySeparated I J

/-- A *maximal weakly separated collection* of `a`-element subsets of `[1, b]`: a weakly separated
collection contained in no strictly larger weakly separated collection. -/
@[cluster_algebras "def_weakly_separated_collection"]
abbrev IsMaximalWeaklySeparatedCollection (a : ℕ) (C : Finset (Finset (Fin b))) : Prop :=
  Maximal (IsWeaklySeparatedCollection a) C

/-- Being a weakly separated collection is decidable. -/
instance (a : ℕ) : DecidablePred (IsWeaklySeparatedCollection (b := b) a) := fun C => by
  unfold IsWeaklySeparatedCollection; infer_instance

variable {a : ℕ} {C C' : Finset (Finset (Fin b))}

/-- Every member of a weakly separated collection of `a`-element subsets has `a` elements. -/
theorem IsWeaklySeparatedCollection.card_eq (h : IsWeaklySeparatedCollection a C) {I}
    (hI : I ∈ C) : I.card = a :=
  (Finset.mem_powersetCard.1 (h.1 hI)).2

/-- Any two members of a weakly separated collection are weakly separated. -/
theorem IsWeaklySeparatedCollection.weaklySeparated (h : IsWeaklySeparatedCollection a C) {I J}
    (hI : I ∈ C) (hJ : J ∈ C) : WeaklySeparated I J :=
  h.2 I hI J hJ

/-- A subcollection of a weakly separated collection is weakly separated. -/
theorem IsWeaklySeparatedCollection.mono (h : IsWeaklySeparatedCollection a C) (hC : C' ⊆ C) :
    IsWeaklySeparatedCollection a C' :=
  ⟨hC.trans h.1, fun I hI J hJ => h.2 I (hC hI) J (hC hJ)⟩

/-- `C` is a maximal weakly separated collection if and only if it is a weakly separated
collection and every weakly separated collection containing `C` equals `C`. -/
theorem isMaximalWeaklySeparatedCollection_iff :
    IsMaximalWeaklySeparatedCollection a C ↔ IsWeaklySeparatedCollection a C ∧
      ∀ C', IsWeaklySeparatedCollection a C' → C ⊆ C' → C' = C :=
  ⟨fun h => ⟨h.1, fun _ hC' hle => (h.2 hC' hle).antisymm hle⟩,
    fun h => ⟨h.1, fun C' hC' hle => (h.2 C' hC' hle).le⟩⟩

/-- Every weakly separated collection is contained in a maximal one. -/
theorem IsWeaklySeparatedCollection.exists_maximal (h : IsWeaklySeparatedCollection a C) :
    ∃ C', C ⊆ C' ∧ IsMaximalWeaklySeparatedCollection a C' :=
  (Set.toFinite {C | IsWeaklySeparatedCollection a C}).exists_le_maximal (a := C) h

end Collection

/-! ### The cyclic orders `<_ℓ` -/

section CyclicOrder

/-- The rank `r_ℓ(x)` of `x` for the cyclic order starting at `ℓ`: `x - ℓ` if `x ≥ ℓ` and
`x - ℓ + b` if `x < ℓ`. The elements `ℓ, x : Fin b` are the labels `ℓ + 1, x + 1`; the rank is
invariant under this shift. -/
@[cluster_algebras "def_cyclic_order"]
def cyclicRank (ℓ x : Fin b) : ℕ :=
  if ℓ ≤ x then (x : ℕ) - ℓ else (x : ℕ) + b - ℓ

/-- The linear order `<_ℓ` on `[1, b]`: `x <_ℓ y` if and only if `r_ℓ(x) < r_ℓ(y)`. -/
@[cluster_algebras "def_cyclic_order"]
def cyclicLT (ℓ x y : Fin b) : Prop :=
  cyclicRank ℓ x < cyclicRank ℓ y

/-- The cyclic order `<_ℓ` is decidable. -/
instance (ℓ : Fin b) : DecidableRel (cyclicLT ℓ) := fun x y => by
  unfold cyclicLT; infer_instance

/-- `x <_ℓ y` if and only if `r_ℓ(x) < r_ℓ(y)`. -/
theorem cyclicLT_iff {ℓ x y : Fin b} : cyclicLT ℓ x y ↔ cyclicRank ℓ x < cyclicRank ℓ y :=
  Iff.rfl

/-- For `ℓ ≤ x`, `r_ℓ(x) = x - ℓ`. -/
theorem cyclicRank_of_le {ℓ x : Fin b} (h : ℓ ≤ x) : cyclicRank ℓ x = (x : ℕ) - ℓ :=
  if_pos h

/-- For `x < ℓ`, `r_ℓ(x) = x + b - ℓ`. -/
theorem cyclicRank_of_lt {ℓ x : Fin b} (h : x < ℓ) : cyclicRank ℓ x = (x : ℕ) + b - ℓ :=
  if_neg (not_le.2 h)

/-- The rank `r_ℓ(x)` is the value of `x - ℓ` in `Fin b`. -/
theorem cyclicRank_eq_val_sub (ℓ x : Fin b) : cyclicRank ℓ x = ((x - ℓ : Fin b) : ℕ) := by
  rcases le_or_gt ℓ x with h | h
  · rw [cyclicRank_of_le h, Fin.coe_sub_iff_le.2 h]
  · rw [cyclicRank_of_lt h, Fin.coe_sub_iff_lt.2 h]; omega

/-- The rank `r_ℓ(x)` is less than `b`. -/
theorem cyclicRank_lt (ℓ x : Fin b) : cyclicRank ℓ x < b := by
  rw [cyclicRank_eq_val_sub]; exact Fin.is_lt _

/-- The rank `r_ℓ` is injective. -/
theorem cyclicRank_injective (ℓ : Fin b) : Function.Injective (cyclicRank ℓ) := by
  intro x y h
  have := x.isLt; have := y.isLt; have := ℓ.isLt
  simp only [cyclicRank, Fin.le_def] at h
  exact Fin.ext (by split_ifs at h <;> omega)

/-- `r_ℓ(x) = r_ℓ(y)` if and only if `x = y`. -/
@[simp]
theorem cyclicRank_inj {ℓ x y : Fin b} : cyclicRank ℓ x = cyclicRank ℓ y ↔ x = y :=
  (cyclicRank_injective ℓ).eq_iff

/-- Every `n < b` is the rank `r_ℓ(x)` of some `x`. -/
theorem exists_cyclicRank_eq (ℓ : Fin b) {n : ℕ} (hn : n < b) : ∃ x, cyclicRank ℓ x = n := by
  have := ℓ.isLt
  by_cases h : n + ℓ < b
  · exact ⟨⟨n + ℓ, h⟩, by simp only [cyclicRank, Fin.le_def]; split_ifs <;> omega⟩
  · exact ⟨⟨n + ℓ - b, by omega⟩, by simp only [cyclicRank, Fin.le_def]; split_ifs <;> omega⟩

/-- `r_ℓ(ℓ) = 0`. -/
@[simp]
theorem cyclicRank_self (ℓ : Fin b) : cyclicRank ℓ ℓ = 0 := by
  simp [cyclicRank]

/-- `r_ℓ(x) = 0` if and only if `x = ℓ`. -/
@[simp]
theorem cyclicRank_eq_zero_iff {ℓ x : Fin b} : cyclicRank ℓ x = 0 ↔ x = ℓ := by
  rw [← cyclicRank_self ℓ, cyclicRank_inj]

/-- `<_1` is the usual order (`0 : Fin b` is the label `1`). -/
@[simp]
theorem cyclicRank_zero [NeZero b] (x : Fin b) : cyclicRank 0 x = x := by
  simp [cyclicRank]

/-- `x <_1 y` if and only if `x < y`. -/
@[simp]
theorem cyclicLT_zero_iff [NeZero b] {x y : Fin b} : cyclicLT 0 x y ↔ x < y := by
  rw [cyclicLT, cyclicRank_zero, cyclicRank_zero, Fin.lt_def]

private theorem val_add_one_eq [NeZero b] (ℓ : Fin b) :
    ((ℓ + 1 : Fin b) : ℕ) = if (ℓ : ℕ) + 1 = b then 0 else (ℓ : ℕ) + 1 := by
  have h := ℓ.isLt
  rw [Fin.val_add, Fin.val_one']
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rw [Nat.mod_eq_of_lt hb]
    split_ifs with h'
    · rw [h', Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  · obtain rfl : b = 1 := by omega
    simp

/-- For `x ≠ ℓ`, `r_{ℓ+1}(x) + 1 = r_ℓ(x)`. -/
theorem cyclicRank_add_one [NeZero b] {ℓ x : Fin b} (hx : x ≠ ℓ) :
    cyclicRank (ℓ + 1) x + 1 = cyclicRank ℓ x := by
  have hx' : (x : ℕ) ≠ ℓ := Fin.val_ne_iff.2 hx
  have h1 := x.isLt; have h2 := ℓ.isLt
  have h3 := val_add_one_eq ℓ
  simp only [cyclicRank, Fin.le_def]
  split_ifs at h3 ⊢ <;> omega

/-- `r_{ℓ+1}(ℓ) = b - 1`: `ℓ` is the largest element for `<_{ℓ+1}`. -/
@[simp]
theorem cyclicRank_add_one_self [NeZero b] (ℓ : Fin b) : cyclicRank (ℓ + 1) ℓ = b - 1 := by
  have h2 := ℓ.isLt
  have h3 := val_add_one_eq ℓ
  simp only [cyclicRank, Fin.le_def]
  split_ifs at h3 ⊢ <;> omega

/-- For `x, y ≠ ℓ`, `x <_{ℓ+1} y` if and only if `x <_ℓ y`. -/
theorem cyclicLT_add_one_iff [NeZero b] {ℓ x y : Fin b} (hx : x ≠ ℓ) (hy : y ≠ ℓ) :
    cyclicLT (ℓ + 1) x y ↔ cyclicLT ℓ x y := by
  have := cyclicRank_add_one hx
  have := cyclicRank_add_one hy
  simp only [cyclicLT]
  omega

/-- `<_ℓ` is irreflexive. -/
theorem cyclicLT_irrefl (ℓ x : Fin b) : ¬ cyclicLT ℓ x x :=
  lt_irrefl _

/-- `<_ℓ` is transitive. -/
theorem cyclicLT.trans {ℓ x y z : Fin b} (h₁ : cyclicLT ℓ x y) (h₂ : cyclicLT ℓ y z) :
    cyclicLT ℓ x z :=
  lt_trans h₁ h₂

/-- Any two elements are comparable for `<_ℓ`: `x <_ℓ y`, `x = y` or `y <_ℓ x`. -/
theorem cyclicLT_trichotomy (ℓ x y : Fin b) : cyclicLT ℓ x y ∨ x = y ∨ cyclicLT ℓ y x := by
  rcases lt_trichotomy (cyclicRank ℓ x) (cyclicRank ℓ y) with h | h | h
  exacts [.inl h, .inr (.inl (cyclicRank_injective ℓ h)), .inr (.inr h)]

/-- `ℓ` is the least element for `<_ℓ`. -/
theorem cyclicLT_self_left {ℓ x : Fin b} (hx : x ≠ ℓ) : cyclicLT ℓ ℓ x := by
  rw [cyclicLT, cyclicRank_self]
  exact Nat.pos_of_ne_zero (cyclicRank_eq_zero_iff.not.2 hx)

end CyclicOrder

/-! ### The order `≤_ℓ` on `a`-element subsets -/

section GaleOrder

/-- The ranks `r_ℓ(i₁) < ⋯ < r_ℓ(iₐ)` of the elements `i₁ <_ℓ ⋯ <_ℓ iₐ` of `I`, as an increasing
list. -/
def cyclicRanks (ℓ : Fin b) (I : Finset (Fin b)) : List ℕ :=
  (I.image (cyclicRank ℓ)).sort (· ≤ ·)

/-- The list `cyclicRanks ℓ I` has one entry for each element of `I`. -/
@[simp]
theorem length_cyclicRanks (ℓ : Fin b) (I : Finset (Fin b)) :
    (cyclicRanks ℓ I).length = I.card := by
  rw [cyclicRanks, Finset.length_sort, Finset.card_image_of_injective _ (cyclicRank_injective ℓ)]

/-- The entries of `cyclicRanks ℓ I` are the ranks `r_ℓ(i)` of the elements `i ∈ I`. -/
@[simp]
theorem mem_cyclicRanks {ℓ : Fin b} {I : Finset (Fin b)} {n : ℕ} :
    n ∈ cyclicRanks ℓ I ↔ ∃ i ∈ I, cyclicRank ℓ i = n := by
  simp [cyclicRanks]

/-- A subset `I` is determined by the list `cyclicRanks ℓ I`. -/
theorem cyclicRanks_injective (ℓ : Fin b) : Function.Injective (cyclicRanks ℓ) := by
  intro I J h
  have h' := congrArg List.toFinset h
  simp only [cyclicRanks, Finset.sort_toFinset] at h'
  exact Finset.image_injective (cyclicRank_injective ℓ) h'

/-- The order `I ≤_ℓ J` on `a`-element subsets of `[1, b]`: listing `I = {i₁, …, iₐ}` with
`i₁ <_ℓ ⋯ <_ℓ iₐ` and `J = {j₁, …, jₐ}` with `j₁ <_ℓ ⋯ <_ℓ jₐ`, `r_ℓ(i_t) ≤ r_ℓ(j_t)` for every
`t`. For subsets of different sizes it is false. -/
@[cluster_algebras "def_l_order_on_subsets"]
def galeLE (ℓ : Fin b) (I J : Finset (Fin b)) : Prop :=
  List.Forall₂ (· ≤ ·) (cyclicRanks ℓ I) (cyclicRanks ℓ J)

/-- The order `≤_ℓ` is decidable. -/
instance (ℓ : Fin b) : DecidableRel (galeLE ℓ) := fun I J => by
  unfold galeLE; infer_instance

/-- If `I ≤_ℓ J`, then `I` and `J` have the same number of elements. -/
theorem galeLE.card_eq {ℓ : Fin b} {I J : Finset (Fin b)} (h : galeLE ℓ I J) :
    I.card = J.card := by
  rw [← length_cyclicRanks ℓ, ← length_cyclicRanks ℓ]
  exact h.length_eq

/-- `≤_ℓ` is reflexive. -/
@[simp]
theorem galeLE_refl (ℓ : Fin b) (I : Finset (Fin b)) : galeLE ℓ I I :=
  List.forall₂_refl _

private theorem forall₂_le_trans {l₁ l₂ l₃ : List ℕ} (h₁ : List.Forall₂ (· ≤ ·) l₁ l₂)
    (h₂ : List.Forall₂ (· ≤ ·) l₂ l₃) : List.Forall₂ (· ≤ ·) l₁ l₃ := by
  induction h₁ generalizing l₃ with
  | nil => exact h₂
  | cons hab _ ih =>
    cases h₂ with
    | cons hbc h => exact .cons (le_trans hab hbc) (ih h)

private theorem forall₂_le_antisymm {l₁ l₂ : List ℕ} (h₁ : List.Forall₂ (· ≤ ·) l₁ l₂)
    (h₂ : List.Forall₂ (· ≤ ·) l₂ l₁) : l₁ = l₂ := by
  induction h₁ with
  | nil => rfl
  | cons hab _ ih =>
    cases h₂ with
    | cons hba h => rw [le_antisymm hab hba, ih h]

/-- `≤_ℓ` is transitive. -/
theorem galeLE.trans {ℓ : Fin b} {I J K : Finset (Fin b)} (h₁ : galeLE ℓ I J)
    (h₂ : galeLE ℓ J K) : galeLE ℓ I K :=
  forall₂_le_trans h₁ h₂

/-- `≤_ℓ` is antisymmetric. -/
theorem galeLE.antisymm {ℓ : Fin b} {I J : Finset (Fin b)} (h₁ : galeLE ℓ I J)
    (h₂ : galeLE ℓ J I) : I = J :=
  cyclicRanks_injective ℓ (forall₂_le_antisymm h₁ h₂)

end GaleOrder

/-! ### Grassmann necklaces and positroids -/

section Necklace

/-- A *Grassmann necklace of type `(a, b)`*: a sequence `(I₁, …, I_b)` of `a`-element subsets of
`[1, b]` with `I_{ℓ+1} ⊇ I_ℓ \ {ℓ}` for every `ℓ`, where `I_{b+1} = I₁`. The set `I ℓ` is `I_{ℓ+1}`
of the text, and `ℓ : Fin b` is the label `ℓ + 1`; `ℓ + 1` is computed in `Fin b`, so that the
step from `I_b` returns to `I₁`. -/
@[cluster_algebras "def_grassmann_necklace"]
structure IsGrassmannNecklace [NeZero b] (a : ℕ) (I : Fin b → Finset (Fin b)) : Prop where
  /-- Each `I_ℓ` has `a` elements. -/
  card_eq : ∀ ℓ, (I ℓ).card = a
  /-- `I_ℓ \ {ℓ} ⊆ I_{ℓ+1}`. -/
  sdiff_subset : ∀ ℓ, I ℓ \ {ℓ} ⊆ I (ℓ + 1)

/-- The *positroid* `ℳ_ℐ` of a Grassmann necklace `ℐ = (I₁, …, I_b)` of type `(a, b)`: the
`a`-element subsets `J` of `[1, b]` with `I_ℓ ≤_ℓ J` for every `ℓ`. It is defined for every
sequence `I`. -/
@[cluster_algebras "def_positroid"]
def positroid (a : ℕ) (I : Fin b → Finset (Fin b)) : Finset (Finset (Fin b)) :=
  (Finset.powersetCard a Finset.univ).filter fun J => ∀ ℓ, galeLE ℓ (I ℓ) J

/-- `J` lies in the positroid of `I` if and only if `J` has `a` elements and `I_ℓ ≤_ℓ J` for
every `ℓ`. -/
@[simp]
theorem mem_positroid {a : ℕ} {I : Fin b → Finset (Fin b)} {J : Finset (Fin b)} :
    J ∈ positroid a I ↔ J.card = a ∧ ∀ ℓ, galeLE ℓ (I ℓ) J := by
  simp [positroid]

/-- The positroid of `I` consists of `a`-element subsets of `[1, b]`. -/
theorem positroid_subset_powersetCard (a : ℕ) (I : Fin b → Finset (Fin b)) :
    positroid a I ⊆ Finset.powersetCard a Finset.univ :=
  Finset.filter_subset _ _

end Necklace

end ClusterAlgebras

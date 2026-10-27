/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DecoratedPermutation
public import ClusterAlgebras.Plabic.WeakSeparation

/-!
# Grassmann necklaces and decorated permutations

Let `π̃ = (π, ε)` be a decorated permutation on `b` letters and `ℓ ∈ [1,b]`. A letter `i` is an
*`ℓ`-anti-excedance* of `π̃` if `π⁻¹(i) >_ℓ i` for the cyclic order `<_ℓ` starting at `ℓ`, or `i`
is a white fixed point. The set `I_ℓ(π̃)` of `ℓ`-anti-excedances changes in a controlled way from
`ℓ` to `ℓ + 1`: the letter `ℓ` is replaced by `π(ℓ)`, unless `ℓ` is a black fixed point, in which
case nothing changes. Hence all the `I_ℓ(π̃)` have `a(π̃)` elements, and
`ℐ(π̃) = (I_1(π̃), …, I_b(π̃))` is a Grassmann necklace of type `(a(π̃), b)`.

Conversely, a Grassmann necklace `ℐ = (I_1, …, I_b)` determines a decorated permutation `π̃(ℐ)`:
`μ_ℐ(i)` is the letter that enters `I_{i+1}` when `i` leaves `I_i`, and `i` itself if `i ∉ I_i`;
a fixed point `i` is white if `i ∈ I_i` and black otherwise. The two constructions are mutually
inverse, so that `π̃ ↦ ℐ(π̃)` is a bijection from the decorated permutations on `b` letters with
`a` anti-excedances onto the Grassmann necklaces of type `(a, b)`.

## Main definitions

* `ClusterAlgebras.DecoratedPerm.IsAntiExcedanceAt`,
  `ClusterAlgebras.DecoratedPerm.antiExcedancesAt`: `ℓ`-anti-excedances and the set `I_ℓ(π̃)`.
* `ClusterAlgebras.DecoratedPerm.necklace`: the Grassmann necklace `ℐ(π̃)`.
* `ClusterAlgebras.necklacePerm`, `ClusterAlgebras.necklaceColour`,
  `ClusterAlgebras.IsGrassmannNecklace.decoratedPerm`: the decorated permutation `π̃(ℐ)` of a
  Grassmann necklace.
* `ClusterAlgebras.necklaceEquiv`: the bijection between decorated permutations with `a`
  anti-excedances and Grassmann necklaces of type `(a, b)`.

## Main results

* `ClusterAlgebras.DecoratedPerm.antiExcedancesAt_add_one_of_not_isBlackFixed`,
  `ClusterAlgebras.DecoratedPerm.antiExcedancesAt_add_one_of_isBlackFixed`: the step from `ℓ` to
  `ℓ + 1`.
* `ClusterAlgebras.DecoratedPerm.card_antiExcedancesAt`: `|I_ℓ(π̃)| = a(π̃)`.
* `ClusterAlgebras.DecoratedPerm.isGrassmannNecklace_necklace`: `ℐ(π̃)` is a Grassmann necklace.
* `ClusterAlgebras.IsGrassmannNecklace.add_one_eq_insert`,
  `ClusterAlgebras.IsGrassmannNecklace.add_one_eq_of_notMem`: the step of a Grassmann necklace.
* `ClusterAlgebras.IsGrassmannNecklace.bijective_necklacePerm`: `μ_ℐ` is a permutation.
* `ClusterAlgebras.DecoratedPerm.decoratedPerm_necklace`: `π̃(ℐ(π̃)) = π̃`.
* `ClusterAlgebras.IsGrassmannNecklace.necklace_decoratedPerm`: `ℐ(π̃(ℐ)) = ℐ`.

## Implementation notes

* The letters `[1,b]` are `Fin b`, indexed from `0`: `i : Fin b` is the letter `i.val + 1`. The
  set `antiExcedancesAt ℓ` is `I_{ℓ+1}(π̃)` of the text and, as for `IsGrassmannNecklace`, the
  necklace `I : Fin b → Finset (Fin b)` has `I ℓ = I_{ℓ+1}`. The step `ℓ ↦ ℓ + 1` is computed in
  `Fin b`, so `I_{b+1} = I_1` is the wrap-around of `Fin b`; this needs `b ≥ 1` (`NeZero b`).
* The least element of `I_{i+1} \ (I_i \ {i})` in the definition of `μ_ℐ` is taken for the usual
  order of `Fin b`; for a Grassmann necklace this set has at most one element, so the choice of
  order is immaterial.
* The decoration `ε_ℐ` is a colouring `necklaceColour I` of all letters, which
  `DecoratedPerm.ofColouring` restricts to the fixed points of `μ_ℐ`. That `μ_ℐ` is a permutation
  is part of the construction of `π̃(ℐ)`, which is therefore `IsGrassmannNecklace.decoratedPerm`,
  a function of the proof that `ℐ` is a necklace.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  Section 7.13.
-/

@[expose] public section

open Finset

namespace ClusterAlgebras

namespace DecoratedPerm

variable {b : ℕ} (π : DecoratedPerm b)

/-! ### `ℓ`-anti-excedances -/

/-- `i` is an **`ℓ`-anti-excedance** of `π̃ = (π, ε)`: `π⁻¹(i) >_ℓ i`, or `i` is a white fixed
point. The letters `ℓ, i : Fin b` are the labels `ℓ + 1, i + 1`. -/
@[cluster_algebras "def_l_anti_excedance"]
def IsAntiExcedanceAt (ℓ i : Fin b) : Prop :=
  cyclicLT ℓ i (π.perm⁻¹ i) ∨ π.IsWhiteFixed i

/-- Being an `ℓ`-anti-excedance is decidable. -/
instance (ℓ : Fin b) : DecidablePred (π.IsAntiExcedanceAt ℓ) := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- The set `I_{ℓ+1}(π̃)` of `ℓ`-anti-excedances of `π̃` (with `ℓ : Fin b` the label `ℓ + 1`). -/
@[cluster_algebras "def_l_anti_excedance"]
def antiExcedancesAt (ℓ : Fin b) : Finset (Fin b) :=
  {i | π.IsAntiExcedanceAt ℓ i}

/-- `i ∈ I_{ℓ+1}(π̃)` if and only if `π⁻¹(i) >_ℓ i` or `i` is a white fixed point. -/
theorem mem_antiExcedancesAt {ℓ i : Fin b} :
    i ∈ π.antiExcedancesAt ℓ ↔ cyclicLT ℓ i (π.perm⁻¹ i) ∨ π.IsWhiteFixed i := by
  simp [antiExcedancesAt, IsAntiExcedanceAt]

/-- `I_1(π̃)` is the set of anti-excedances. -/
theorem antiExcedancesAt_zero [NeZero b] :
    π.antiExcedancesAt 0 = ({i | π.IsAntiExcedance i} : Finset (Fin b)) := by
  ext i
  simp [mem_antiExcedancesAt, IsAntiExcedance, cyclicLT_zero_iff]

/-- `|I_1(π̃)| = a(π̃)`. -/
theorem card_antiExcedancesAt_zero [NeZero b] :
    #(π.antiExcedancesAt 0) = π.numAntiExcedances := by
  rw [antiExcedancesAt_zero, numAntiExcedances]

/-- A black fixed point is in no `I_ℓ(π̃)`. -/
theorem notMem_antiExcedancesAt_of_isBlackFixed {ℓ i : Fin b} (h : π.IsBlackFixed i) :
    i ∉ π.antiExcedancesAt ℓ := by
  rw [mem_antiExcedancesAt]
  rintro (h' | h')
  · rw [show π.perm⁻¹ i = i by rw [Equiv.Perm.inv_eq_iff_eq, h.perm_apply_eq]] at h'
    exact cyclicLT_irrefl _ _ h'
  · exact π.not_isBlackFixed_of_isWhiteFixed h' h

/-- `i ∈ I_i(π̃)` if and only if `i` is not a black fixed point. -/
theorem self_mem_antiExcedancesAt_iff {i : Fin b} :
    i ∈ π.antiExcedancesAt i ↔ ¬π.IsBlackFixed i := by
  refine ⟨fun h h' => π.notMem_antiExcedancesAt_of_isBlackFixed h' h, fun h => ?_⟩
  rw [mem_antiExcedancesAt]
  by_cases hi : π.perm i = i
  · exact .inr ((π.isWhiteFixed_or_isBlackFixed hi).resolve_right h)
  · exact .inl (cyclicLT_self_left fun h' => hi (Equiv.Perm.inv_eq_iff_eq.1 h').symm)

/-- For `π(i) ≠ i`, the letter `π(i)` is not an `i`-anti-excedance. -/
theorem perm_apply_notMem_antiExcedancesAt {i : Fin b} (h : π.perm i ≠ i) :
    π.perm i ∉ π.antiExcedancesAt i := by
  rw [mem_antiExcedancesAt, Equiv.Perm.inv_eq_iff_eq.2 rfl, isWhiteFixed_perm_apply_iff]
  rintro (h' | h')
  · simp [cyclicLT] at h'
  · exact h h'.perm_apply_eq

/-- `π(i) ∉ I_i(π̃) \ {i}`. -/
theorem perm_apply_notMem_antiExcedancesAt_sdiff (i : Fin b) :
    π.perm i ∉ π.antiExcedancesAt i \ {i} := by
  by_cases h : π.perm i = i
  · simp [h]
  · exact fun h' => π.perm_apply_notMem_antiExcedancesAt h (mem_sdiff.1 h').1

section Step

variable [NeZero b]

/-- `i ∈ I_{i+1}(π̃)` if and only if `i` is a white fixed point, as `i` is the largest element for
`<_{i+1}`. -/
theorem self_mem_antiExcedancesAt_add_one_iff {i : Fin b} :
    i ∈ π.antiExcedancesAt (i + 1) ↔ π.IsWhiteFixed i := by
  rw [mem_antiExcedancesAt, or_iff_right]
  rw [cyclicLT, cyclicRank_add_one_self]
  have := cyclicRank_lt (i + 1) (π.perm⁻¹ i)
  omega

/-- For `x ≠ i` and `π⁻¹(x) ≠ i`, `x ∈ I_{i+1}(π̃)` if and only if `x ∈ I_i(π̃)`. -/
theorem mem_antiExcedancesAt_add_one_iff_of_ne {i x : Fin b} (hx : x ≠ i)
    (hx' : π.perm⁻¹ x ≠ i) :
    x ∈ π.antiExcedancesAt (i + 1) ↔ x ∈ π.antiExcedancesAt i := by
  rw [mem_antiExcedancesAt, mem_antiExcedancesAt, cyclicLT_add_one_iff hx hx']

/-- For `π(i) ≠ i`, the letter `π(i)` is an `(i+1)`-anti-excedance. -/
theorem perm_apply_mem_antiExcedancesAt_add_one {i : Fin b} (h : π.perm i ≠ i) :
    π.perm i ∈ π.antiExcedancesAt (i + 1) := by
  rw [mem_antiExcedancesAt, Equiv.Perm.inv_eq_iff_eq.2 rfl, cyclicLT, cyclicRank_add_one_self]
  left
  have h1 := cyclicRank_lt (i + 1) (π.perm i)
  have h2 : cyclicRank (i + 1) (π.perm i) ≠ cyclicRank (i + 1) i := by
    rwa [Ne, cyclicRank_inj]
  rw [cyclicRank_add_one_self] at h2
  omega

/-- **The step from `ℓ` to `ℓ + 1`**, for `i` not a black fixed point:
`I_{i+1}(π̃) = (I_i(π̃) \ {i}) ∪ {π(i)}`. -/
@[cluster_algebras "lem_l_anti_excedance_step"]
theorem antiExcedancesAt_add_one_of_not_isBlackFixed {i : Fin b} (h : ¬π.IsBlackFixed i) :
    π.antiExcedancesAt (i + 1) = insert (π.perm i) (π.antiExcedancesAt i \ {i}) := by
  ext x
  rw [mem_insert, mem_sdiff, mem_singleton]
  by_cases hxi : x = i
  · subst hxi
    rw [self_mem_antiExcedancesAt_add_one_iff]
    refine ⟨fun hw => .inl hw.perm_apply_eq.symm, ?_⟩
    rintro (hx | ⟨_, hx⟩)
    · exact (π.isWhiteFixed_or_isBlackFixed hx.symm).resolve_right h
    · exact absurd rfl hx
  · by_cases hxp : x = π.perm i
    · subst hxp
      simpa using π.perm_apply_mem_antiExcedancesAt_add_one hxi
    · rw [π.mem_antiExcedancesAt_add_one_iff_of_ne hxi (by rwa [Ne, Equiv.Perm.inv_eq_iff_eq])]
      simp [hxp, hxi]

/-- **The step from `ℓ` to `ℓ + 1`**, for `i` a black fixed point: `I_{i+1}(π̃) = I_i(π̃)`. -/
@[cluster_algebras "lem_l_anti_excedance_step"]
theorem antiExcedancesAt_add_one_of_isBlackFixed {i : Fin b} (h : π.IsBlackFixed i) :
    π.antiExcedancesAt (i + 1) = π.antiExcedancesAt i := by
  ext x
  by_cases hxi : x = i
  · subst hxi
    simp only [π.notMem_antiExcedancesAt_of_isBlackFixed h]
  · exact π.mem_antiExcedancesAt_add_one_iff_of_ne hxi
      (by rwa [Ne, Equiv.Perm.inv_eq_iff_eq, h.perm_apply_eq])

/-- For `x ≠ i`, `x ∈ I_{i+1}(π̃)` if and only if `x ∈ I_i(π̃)` or `π(i) = x`. -/
theorem mem_antiExcedancesAt_add_one_iff {i x : Fin b} (hx : x ≠ i) :
    x ∈ π.antiExcedancesAt (i + 1) ↔ x ∈ π.antiExcedancesAt i ∨ π.perm i = x := by
  by_cases h : π.IsBlackFixed i
  · rw [π.antiExcedancesAt_add_one_of_isBlackFixed h, h.perm_apply_eq]
    simp [Ne.symm hx]
  · rw [π.antiExcedancesAt_add_one_of_not_isBlackFixed h]
    simp only [mem_insert, mem_sdiff, mem_singleton, hx, not_false_eq_true, and_true]
    tauto

/-- `|I_{i+1}(π̃)| = |I_i(π̃)|`. -/
theorem card_antiExcedancesAt_add_one (i : Fin b) :
    #(π.antiExcedancesAt (i + 1)) = #(π.antiExcedancesAt i) := by
  by_cases h : π.IsBlackFixed i
  · rw [π.antiExcedancesAt_add_one_of_isBlackFixed h]
  · rw [π.antiExcedancesAt_add_one_of_not_isBlackFixed h,
      card_insert_of_notMem (π.perm_apply_notMem_antiExcedancesAt_sdiff i),
      card_sdiff_of_subset (singleton_subset_iff.2 ((π.self_mem_antiExcedancesAt_iff).2 h)),
      card_singleton]
    have : 0 < #(π.antiExcedancesAt i) :=
      card_pos.2 ⟨i, (π.self_mem_antiExcedancesAt_iff).2 h⟩
    omega

end Step

open Fin.NatCast in
/-- **The number of `ℓ`-anti-excedances does not depend on `ℓ`**: `|I_ℓ(π̃)| = a(π̃)`. -/
@[cluster_algebras "lem_l_anti_excedance_count"]
theorem card_antiExcedancesAt (ℓ : Fin b) : #(π.antiExcedancesAt ℓ) = π.numAntiExcedances := by
  have : NeZero b := ⟨ℓ.pos.ne'⟩
  have key (n : ℕ) : #(π.antiExcedancesAt (n : Fin b)) = π.numAntiExcedances := by
    induction n with
    | zero => simpa using π.card_antiExcedancesAt_zero
    | succ n ih => rw [Nat.cast_succ, card_antiExcedancesAt_add_one, ih]
  simpa using key ℓ.val

/-! ### The Grassmann necklace of a decorated permutation -/

/-- The **Grassmann necklace** `ℐ(π̃) = (I_1(π̃), …, I_b(π̃))` of `π̃`. As for
`IsGrassmannNecklace`, its term `π.necklace ℓ = π.antiExcedancesAt ℓ` is `I_{ℓ+1}(π̃)` of the
text. -/
@[cluster_algebras "def_necklace_of_permutation"]
def necklace : Fin b → Finset (Fin b) :=
  π.antiExcedancesAt

/-- The term `π.necklace ℓ` of `ℐ(π̃)` is `π.antiExcedancesAt ℓ`. -/
@[simp]
theorem necklace_apply (ℓ : Fin b) : π.necklace ℓ = π.antiExcedancesAt ℓ :=
  rfl

/-- **The necklace of a decorated permutation is a Grassmann necklace**, of type `(a(π̃), b)`. -/
@[cluster_algebras "lem_necklace_of_permutation"]
theorem isGrassmannNecklace_necklace [NeZero b] :
    IsGrassmannNecklace π.numAntiExcedances π.necklace where
  card_eq ℓ := π.card_antiExcedancesAt ℓ
  sdiff_subset ℓ := by
    simp only [necklace_apply]
    by_cases h : π.IsBlackFixed ℓ
    · rw [π.antiExcedancesAt_add_one_of_isBlackFixed h]
      exact sdiff_subset
    · rw [π.antiExcedancesAt_add_one_of_not_isBlackFixed h]
      exact subset_insert _ _

end DecoratedPerm

/-! ### The decorated permutation of a Grassmann necklace -/

section Necklace

variable {b : ℕ} [NeZero b]

/-- The permutation `μ_ℐ` of a Grassmann necklace `ℐ`: `μ_ℐ(i)` is the least element of
`I_{i+1} \ (I_i \ {i})` if `i ∈ I_i` and this set is nonempty, and `i` otherwise. Here `I ℓ` is
`I_{ℓ+1}` and `i : Fin b` is the label `i + 1`. It is defined for every sequence `I`; it is a
permutation when `I` is a Grassmann necklace (`IsGrassmannNecklace.bijective_necklacePerm`). -/
@[cluster_algebras "def_permutation_of_necklace"]
def necklacePerm (I : Fin b → Finset (Fin b)) (i : Fin b) : Fin b :=
  if h : i ∈ I i ∧ (I (i + 1) \ (I i \ {i})).Nonempty then (I (i + 1) \ (I i \ {i})).min' h.2
  else i

/-- The decoration `ε_ℐ` of a Grassmann necklace `ℐ`: white at `i` if `i ∈ I_i` and black
otherwise. It is used at the fixed points of `μ_ℐ`. -/
@[cluster_algebras "def_permutation_of_necklace"]
def necklaceColour (I : Fin b → Finset (Fin b)) (i : Fin b) : Shade :=
  if i ∈ I i then .white else .black

/-- If `i ∉ I_i`, then `μ_ℐ(i) = i`. -/
theorem necklacePerm_of_notMem {I : Fin b → Finset (Fin b)} {i : Fin b} (h : i ∉ I i) :
    necklacePerm I i = i := by
  rw [necklacePerm, dif_neg (fun h' => h h'.1)]

omit [NeZero b] in
/-- If `i ∈ I_i`, then `ε_ℐ(i)` is white. -/
@[simp]
theorem necklaceColour_of_mem {I : Fin b → Finset (Fin b)} {i : Fin b} (h : i ∈ I i) :
    necklaceColour I i = .white :=
  if_pos h

omit [NeZero b] in
/-- If `i ∉ I_i`, then `ε_ℐ(i)` is black. -/
@[simp]
theorem necklaceColour_of_notMem {I : Fin b → Finset (Fin b)} {i : Fin b} (h : i ∉ I i) :
    necklaceColour I i = .black :=
  if_neg h

namespace IsGrassmannNecklace

variable {a : ℕ} {I : Fin b → Finset (Fin b)} (hI : IsGrassmannNecklace a I)

include hI

/-- **The step of a Grassmann necklace**, for `i ∈ I_i`: `I_{i+1} = (I_i \ {i}) ∪ {μ_ℐ(i)}` with
`μ_ℐ(i) ∉ I_i \ {i}`. -/
@[cluster_algebras "lem_necklace_step"]
theorem add_one_eq_insert {i : Fin b} (h : i ∈ I i) :
    I (i + 1) = insert (necklacePerm I i) (I i \ {i}) ∧ necklacePerm I i ∉ I i \ {i} := by
  have hsub := hI.sdiff_subset i
  have hcard : #(I (i + 1) \ (I i \ {i})) = 1 := by
    rw [card_sdiff_of_subset hsub, hI.card_eq, card_sdiff_of_subset (singleton_subset_iff.2 h),
      hI.card_eq, card_singleton]
    have : 0 < a := hI.card_eq i ▸ card_pos.2 ⟨i, h⟩
    omega
  obtain ⟨j, hj⟩ := card_eq_one.1 hcard
  have hμ : necklacePerm I i = j := by
    rw [necklacePerm, dif_pos ⟨h, hj ▸ singleton_nonempty j⟩]
    simp only [hj, min'_singleton]
  refine ⟨?_, hμ ▸ (mem_sdiff.1 (hj ▸ mem_singleton_self j)).2⟩
  rw [hμ, insert_eq, ← hj]
  exact (sdiff_union_of_subset hsub).symm

/-- **The step of a Grassmann necklace**, for `i ∉ I_i`: `I_{i+1} = I_i`. -/
@[cluster_algebras "lem_necklace_step"]
theorem add_one_eq_of_notMem {i : Fin b} (h : i ∉ I i) : I (i + 1) = I i := by
  have hsub : I i ⊆ I (i + 1) := by
    simpa [sdiff_singleton_eq_erase, erase_eq_of_notMem h] using hI.sdiff_subset i
  exact (eq_of_subset_of_card_le hsub (by rw [hI.card_eq, hI.card_eq])).symm

/-- For `x ≠ t`, `x ∈ I_{t+1}` if and only if `x ∈ I_t` or `μ_ℐ(t) = x`. -/
theorem mem_add_one_iff {t x : Fin b} (hx : x ≠ t) :
    x ∈ I (t + 1) ↔ x ∈ I t ∨ necklacePerm I t = x := by
  by_cases h : t ∈ I t
  · rw [(hI.add_one_eq_insert h).1]
    simp only [mem_insert, mem_sdiff, mem_singleton, hx, not_false_eq_true, and_true]
    tauto
  · rw [hI.add_one_eq_of_notMem h, necklacePerm_of_notMem h]
    simp [Ne.symm hx]

/-- `x ∈ I_{x+1}` if and only if `x ∈ I_x` and `μ_ℐ(x) = x`. -/
theorem self_mem_add_one_iff {x : Fin b} :
    x ∈ I (x + 1) ↔ x ∈ I x ∧ necklacePerm I x = x := by
  by_cases h : x ∈ I x
  · rw [(hI.add_one_eq_insert h).1]
    simp [h, eq_comm]
  · rw [hI.add_one_eq_of_notMem h]
    simp [h]

/-- If `μ_ℐ(t) = j` with `t ≠ j`, then `j ∉ I_t`. -/
theorem notMem_of_necklacePerm_eq {t j : Fin b} (ht : t ≠ j) (hμ : necklacePerm I t = j) :
    j ∉ I t := by
  intro hjt
  have htI : t ∈ I t := by_contra fun h => ht ((necklacePerm_of_notMem h).symm.trans hμ)
  exact (hI.add_one_eq_insert htI).2 (hμ ▸ mem_sdiff.2 ⟨hjt, notMem_singleton.2 (Ne.symm ht)⟩)

/-- For a letter `j`, the number of `t ≠ j` with `μ_ℐ(t) = j` is `[j ∈ I_j] - [j ∈ I_{j+1}]`. -/
theorem card_necklacePerm_eq (j : Fin b) :
    (#{t ∈ univ.erase j | necklacePerm I t = j} : ℤ) =
      (if j ∈ I j then 1 else 0) - if j ∈ I (j + 1) then 1 else 0 := by
  set m : Fin b → ℤ := fun t => if j ∈ I t then 1 else 0 with hm
  have hstep : ∀ t ∈ univ.erase j, m (t + 1) - m t = if necklacePerm I t = j then 1 else 0 := by
    intro t ht
    have ht : t ≠ j := ne_of_mem_erase ht
    have hiff := hI.mem_add_one_iff (Ne.symm ht)
    by_cases hμ : necklacePerm I t = j
    · have hjt := hI.notMem_of_necklacePerm_eq ht hμ
      simp [hm, hμ, hjt, hiff.2 (.inr hμ)]
    · simp only [hμ, or_false] at hiff
      simp [hm, hμ, hiff]
  have hsum : ∑ t, (m (t + 1) - m t) = 0 := by
    rw [sum_sub_distrib, sub_eq_zero]
    exact Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ => rfl
  rw [← add_sum_erase _ _ (mem_univ j), sum_congr rfl hstep, ← natCast_card_filter] at hsum
  change _ = m j - m (j + 1)
  linarith

/-- **The decorated permutation of a necklace is a decorated permutation**: `μ_ℐ` is a
permutation of `[1,b]`. -/
@[cluster_algebras "lem_permutation_of_necklace"]
theorem bijective_necklacePerm : Function.Bijective (necklacePerm I) := by
  refine Finite.injective_iff_bijective.1 fun s t hst => ?_
  by_contra hne
  obtain ⟨j, hs⟩ : ∃ j, necklacePerm I s = j := ⟨_, rfl⟩
  have ht : necklacePerm I t = j := hst ▸ hs
  have hc := hI.card_necklacePerm_eq j
  by_cases hj : necklacePerm I j = j
  · have h0 : #{t ∈ univ.erase j | necklacePerm I t = j} = 0 := by
      have := hI.self_mem_add_one_iff (x := j)
      simp only [hj, and_true] at this
      simp only [this, sub_self] at hc
      exact_mod_cast hc
    rw [card_eq_zero, filter_eq_empty_iff] at h0
    by_cases hsj : s = j
    · exact h0 (mem_erase.2 ⟨fun h => hne (hsj.trans h.symm), mem_univ t⟩) ht
    · exact h0 (mem_erase.2 ⟨hsj, mem_univ s⟩) hs
  · have hsj : s ≠ j := fun h => hj (h ▸ hs)
    have htj : t ≠ j := fun h => hj (h ▸ ht)
    have h2 : 1 < #{t ∈ univ.erase j | necklacePerm I t = j} :=
      one_lt_card.2 ⟨s, by simp [hsj, hs], t, by simp [htj, ht], hne⟩
    have h2' : (1 : ℤ) < #{t ∈ univ.erase j | necklacePerm I t = j} := by exact_mod_cast h2
    rw [hc] at h2'
    split_ifs at h2' <;> norm_num at h2'

/-- The **decorated permutation `π̃(ℐ) = (μ_ℐ, ε_ℐ)` of a Grassmann necklace** `ℐ`. -/
@[cluster_algebras "def_permutation_of_necklace"]
noncomputable def decoratedPerm : DecoratedPerm b :=
  .ofColouring (Equiv.ofBijective _ hI.bijective_necklacePerm) (necklaceColour I)

/-- The permutation of `π̃(ℐ)` is `μ_ℐ`. -/
@[simp]
theorem decoratedPerm_perm_apply (i : Fin b) : hI.decoratedPerm.perm i = necklacePerm I i :=
  rfl

/-- The white fixed points of `π̃(ℐ)` are the fixed points `i` of `μ_ℐ` with `i ∈ I_i`. -/
theorem isWhiteFixed_decoratedPerm_iff {i : Fin b} :
    hI.decoratedPerm.IsWhiteFixed i ↔ necklacePerm I i = i ∧ i ∈ I i := by
  refine ⟨fun ⟨h, hc⟩ => ⟨h, ?_⟩, fun ⟨h, h'⟩ => ⟨h, ?_⟩⟩
  · change necklaceColour I i = .white at hc
    by_contra h'
    simp [necklaceColour_of_notMem h'] at hc
  · exact necklaceColour_of_mem h'

open Fin.NatCast in
/-- **From a necklace to its decorated permutation and back**: `ℐ(π̃(ℐ)) = ℐ`. -/
@[cluster_algebras "lem_necklace_right_inverse"]
theorem necklace_decoratedPerm : hI.decoratedPerm.necklace = I := by
  funext ℓ
  ext x
  rw [DecoratedPerm.necklace_apply]
  have key : ∀ n : ℕ, n < b →
      (x ∈ hI.decoratedPerm.antiExcedancesAt (x + 1 + n) ↔ x ∈ I (x + 1 + n)) := by
    intro n hn
    induction n with
    | zero =>
      simp only [Nat.cast_zero, add_zero]
      rw [DecoratedPerm.self_mem_antiExcedancesAt_add_one_iff, isWhiteFixed_decoratedPerm_iff,
        hI.self_mem_add_one_iff, and_comm]
    | succ n ih =>
      have hne : x ≠ x + 1 + n := by
        intro h
        have h0 : ((n + 1 : ℕ) : Fin b) = 0 := by
          have : x + ((n + 1 : ℕ) : Fin b) = x + 0 := by
            rw [add_zero, Nat.cast_succ, add_comm (n : Fin b) 1, ← add_assoc]
            exact h.symm
          exact add_left_cancel this
        have := congrArg Fin.val h0
        rw [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt hn] at this
        omega
      rw [Nat.cast_succ, ← add_assoc, DecoratedPerm.mem_antiExcedancesAt_add_one_iff _ hne,
        hI.mem_add_one_iff hne, ih (by omega), decoratedPerm_perm_apply]
  have := key (ℓ - x - 1).val (ℓ - x - 1).isLt
  rwa [Fin.cast_val_eq_self, show x + 1 + (ℓ - x - 1) = ℓ by abel] at this

/-- `π̃(ℐ)` has `a` anti-excedances. -/
theorem numAntiExcedances_decoratedPerm : hI.decoratedPerm.numAntiExcedances = a := by
  rw [← hI.decoratedPerm.card_antiExcedancesAt_zero, ← DecoratedPerm.necklace_apply,
    hI.necklace_decoratedPerm, hI.card_eq]

end IsGrassmannNecklace

namespace DecoratedPerm

variable (π : DecoratedPerm b)

/-- **From a decorated permutation to its necklace and back**: `π̃(ℐ(π̃)) = π̃`. -/
@[cluster_algebras "lem_necklace_left_inverse"]
theorem decoratedPerm_necklace : π.isGrassmannNecklace_necklace.decoratedPerm = π := by
  have hperm : ∀ i, necklacePerm π.necklace i = π.perm i := by
    intro i
    by_cases h : π.IsBlackFixed i
    · rw [necklacePerm_of_notMem (by simpa [π.self_mem_antiExcedancesAt_iff] using h),
        h.perm_apply_eq]
    · have hi : i ∈ π.necklace i := π.self_mem_antiExcedancesAt_iff.2 h
      obtain ⟨h1, h2⟩ := π.isGrassmannNecklace_necklace.add_one_eq_insert hi
      have hmem : necklacePerm π.necklace i ∈ π.necklace (i + 1) := by
        rw [h1]
        exact mem_insert_self _ _
      rw [necklace_apply, π.antiExcedancesAt_add_one_of_not_isBlackFixed h, mem_insert] at hmem
      exact hmem.resolve_right h2
  refine DecoratedPerm.ext (Equiv.ext hperm) fun i h1 h2 => ?_
  change necklaceColour π.necklace i = _
  rcases π.isWhiteFixed_or_isBlackFixed h2 with hw | hb
  · have : i ∈ π.necklace i :=
      π.self_mem_antiExcedancesAt_iff.2 (π.not_isBlackFixed_of_isWhiteFixed hw)
    rw [necklaceColour_of_mem this, (π.isWhiteFixed_iff_of_perm_apply_eq h2).1 hw]
  · have : i ∉ π.necklace i := π.notMem_antiExcedancesAt_of_isBlackFixed hb
    rw [necklaceColour_of_notMem this, (π.isBlackFixed_iff_of_perm_apply_eq h2).1 hb]

end DecoratedPerm

end Necklace

/-- **Decorated permutations and Grassmann necklaces**: `π̃ ↦ ℐ(π̃)` is a bijection from the
decorated permutations on `b` letters with `a` anti-excedances onto the Grassmann necklaces of
type `(a, b)`, with inverse `ℐ ↦ π̃(ℐ)`. -/
@[cluster_algebras "lem_necklace_bijection"]
noncomputable def necklaceEquiv (a b : ℕ) [NeZero b] :
    {π : DecoratedPerm b // π.numAntiExcedances = a} ≃
      {I : Fin b → Finset (Fin b) // IsGrassmannNecklace a I} where
  toFun π := ⟨π.1.necklace, by
    obtain ⟨π, rfl⟩ := π
    exact π.isGrassmannNecklace_necklace⟩
  invFun I := ⟨I.2.decoratedPerm, I.2.numAntiExcedances_decoratedPerm⟩
  left_inv π := Subtype.ext π.1.decoratedPerm_necklace
  right_inv I := Subtype.ext I.2.necklace_decoratedPerm

/-- The bijection `necklaceEquiv` is `π̃ ↦ ℐ(π̃)`. -/
@[simp, cluster_algebras "lem_necklace_bijection"]
theorem necklaceEquiv_apply {a b : ℕ} [NeZero b]
    (π : {π : DecoratedPerm b // π.numAntiExcedances = a}) :
    (necklaceEquiv a b π : Fin b → Finset (Fin b)) = π.1.necklace :=
  rfl

/-- The inverse of `necklaceEquiv` is `ℐ ↦ π̃(ℐ)`. -/
@[simp, cluster_algebras "lem_necklace_bijection"]
theorem necklaceEquiv_symm_apply {a b : ℕ} [NeZero b]
    (I : {I : Fin b → Finset (Fin b) // IsGrassmannNecklace a I}) :
    ((necklaceEquiv a b).symm I : DecoratedPerm b) = I.2.decoratedPerm :=
  rfl

end ClusterAlgebras

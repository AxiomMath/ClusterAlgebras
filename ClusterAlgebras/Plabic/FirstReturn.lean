/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# First-return maps and orbit counts of permutations

Let `π` be a permutation of a finite set `X` and `Y ⊆ X`. The *first-return map* `π_Y : Y → Y`
sends `y` to `π^m(y)`, where `m ≥ 1` is least with `π^m(y) ∈ Y`. It is a permutation of `Y`,
and two elements of `Y` lie in one orbit of `π_Y` exactly when they lie in one orbit of `π`.
So when every orbit of `π` meets `Y`, the permutations `π` and `π_Y` have the same number of
orbits.

We also count how the number of orbits changes under right multiplication by a transposition
`(p q)`: it goes up by one when `p` and `q` lie in one orbit, and down by one otherwise. Finally,
for a fixed-point-free involution `ι`, a permutation `σ` and an element `d`, the *rotation
induced off* the pair `{d, ι d}` is the first return of `σ ∘ (d ι(d))` to `H \ {d, ι d}`; the
face permutation `σ' ∘ ι` it defines has as many orbits as `σ ∘ ι`, when every orbit of `σ ∘ ι`
meets `H \ {d, ι d}`. This is the count of faces under contraction of an edge of a plabic graph.

## Main definitions

* `ClusterAlgebras.firstReturn π Y`: the first-return map `π_Y : Y → Y`.
* `ClusterAlgebras.firstReturnTime π Y y`: the least `m ≥ 1` with `π^m(y) ∈ Y`.
* `ClusterAlgebras.firstReturnPerm π Y`: the first-return map as a permutation of `Y`.
* `ClusterAlgebras.numOrbits σ`: the number of orbits of a permutation, fixed points included.
* `ClusterAlgebras.inducedRotation ι σ d`: the rotation induced on `H \ {d, ι d}`.

## Main results

* `ClusterAlgebras.firstReturn_bijective`: the first-return map is a bijection of `Y`.
* `ClusterAlgebras.exists_iterate_firstReturn_eq_iff`: two elements of `Y` lie in one orbit of
  `π_Y` exactly when they lie in one orbit of `π`.
* `ClusterAlgebras.numOrbits_mul_swap_of_sameCycle`,
  `ClusterAlgebras.numOrbits_mul_swap_of_not_sameCycle`: right multiplication by `(p q)` raises
  the number of orbits by one when `p` and `q` lie in one orbit, and lowers it by one otherwise.
* `ClusterAlgebras.inducedRotation_bijective`: the induced rotation is a bijection.
* `ClusterAlgebras.numOrbits_inducedRotationPerm_mul`: the face permutation `σ' ∘ ι` has as
  many orbits as `σ ∘ ι`.
* `ClusterAlgebras.exists_forall_sameCycle_notMem_iff`: for `L ⊆ Y`, when every orbit of `π`
  meets `Y`, `π` has an orbit disjoint from `L` exactly when `π_Y` does.

## Implementation notes

* A subset `Y` of `X` is a `Set X`, and the first-return map acts on the subtype `↥Y`; the
  complement `H \ {d, ι d}` is `({d, ι d}ᶜ : Set H)`.
* The orbit of `x` under a permutation `σ` is the class of `x` for `Equiv.Perm.SameCycle σ`, and
  `numOrbits σ` is the cardinality of the quotient by that relation. Unlike
  `Equiv.Perm.cycleType`, this counts the fixed points of `σ` as orbits.
* Composition `ρ ∘ (p q)` is the product `ρ * Equiv.swap p q` of `Equiv.Perm`.
* The lemma on contracting an edge needs only that `ι` is an involution: that `ι` has no fixed
  point is not used, and is not assumed.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras*, Chapter 7.
-/

@[expose] public section

open Equiv Equiv.Perm Function

namespace ClusterAlgebras

variable {X : Type*}

/-! ### First-return maps -/

section FirstReturn

variable [Finite X] (π : Perm X) (Y : Set X)

/-- Every element of `Y` returns to `Y` after a positive number of steps of `π`. -/
theorem exists_pow_succ_apply_mem (y : Y) : ∃ m : ℕ, (π ^ (m + 1)) y ∈ Y := by
  refine ⟨orderOf π - 1, ?_⟩
  rw [Nat.sub_add_cancel (isOfFinOrder_of_finite π).orderOf_pos, pow_orderOf_eq_one]
  exact y.2

open scoped Classical in
/-- The *first-return time* of `y ∈ Y` under `π`: the least `m ≥ 1` with `π^m(y) ∈ Y`. -/
noncomputable def firstReturnTime (y : Y) : ℕ :=
  Nat.find (exists_pow_succ_apply_mem π Y y) + 1

variable {π Y}

/-- The first-return time is positive. -/
theorem firstReturnTime_pos (y : Y) : 0 < firstReturnTime π Y y :=
  Nat.succ_pos _

/-- After its first-return time, `y` lies in `Y` again. -/
theorem pow_firstReturnTime_apply_mem (y : Y) : (π ^ firstReturnTime π Y y) y ∈ Y := by
  classical
  unfold firstReturnTime
  exact Nat.find_spec (exists_pow_succ_apply_mem π Y y)

/-- At a positive time smaller than the first-return time, `π^j(y)` is not in `Y`. -/
theorem pow_apply_notMem_of_lt_firstReturnTime {y : Y} {j : ℕ} (hj : 0 < j)
    (hjt : j < firstReturnTime π Y y) : (π ^ j) y ∉ Y := by
  classical
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  unfold firstReturnTime at hjt
  exact Nat.find_min (exists_pow_succ_apply_mem π Y y) (by omega)

/-- The first-return time is at most every positive `m` with `π^m(y) ∈ Y`. -/
theorem firstReturnTime_le {y : Y} {m : ℕ} (hm : 0 < m) (hmY : (π ^ m) y ∈ Y) :
    firstReturnTime π Y y ≤ m := by
  classical
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  unfold firstReturnTime
  have := Nat.find_min' (exists_pow_succ_apply_mem π Y y) hmY
  omega

/-- The first-return time is characterised by being positive, landing in `Y`, and missing `Y`
at every smaller positive time. -/
theorem firstReturnTime_eq_iff {y : Y} {m : ℕ} :
    firstReturnTime π Y y = m ↔
      0 < m ∧ (π ^ m) y ∈ Y ∧ ∀ j, 0 < j → j < m → (π ^ j) y ∉ Y := by
  constructor
  · rintro rfl
    exact ⟨firstReturnTime_pos y, pow_firstReturnTime_apply_mem y,
      fun j hj hjm => pow_apply_notMem_of_lt_firstReturnTime hj hjm⟩
  · rintro ⟨hm, hmY, hmin⟩
    refine le_antisymm (firstReturnTime_le hm hmY) (not_lt.1 fun hlt => ?_)
    exact hmin _ (firstReturnTime_pos y) hlt (pow_firstReturnTime_apply_mem y)

variable (π Y)

/-- The **first-return map** `π_Y : Y → Y` of a permutation `π` of a finite set `X` to a subset
`Y`: it sends `y` to `π^m(y)` for the least `m ≥ 1` with `π^m(y) ∈ Y`. -/
@[cluster_algebras "def_first_return"]
noncomputable def firstReturn (y : Y) : Y :=
  ⟨(π ^ firstReturnTime π Y y) y, pow_firstReturnTime_apply_mem y⟩

/-- The first return of `y` is `π^m(y)`, for `m` the first-return time of `y`. -/
@[simp]
theorem coe_firstReturn (y : Y) : (firstReturn π Y y : X) = (π ^ firstReturnTime π Y y) y :=
  rfl

variable {π Y}

/-- If `m ≥ 1` is least with `π^m(y) ∈ Y`, the first return of `y` is `π^m(y)`. -/
theorem coe_firstReturn_of_pow {y : Y} {m : ℕ} (hm : 0 < m) (hmY : (π ^ m) y ∈ Y)
    (hmin : ∀ j, 0 < j → j < m → (π ^ j) y ∉ Y) : (firstReturn π Y y : X) = (π ^ m) y := by
  rw [coe_firstReturn, firstReturnTime_eq_iff.2 ⟨hm, hmY, hmin⟩]

/-- If `π(y) ∈ Y`, the first return of `y` is `π(y)`. -/
theorem coe_firstReturn_of_apply_mem {y : Y} (h : π y ∈ Y) : (firstReturn π Y y : X) = π y := by
  simpa only [pow_one] using coe_firstReturn_of_pow (π := π) (y := y) (m := 1) one_pos
    (by rwa [pow_one]) fun j hj hj1 => by omega

variable (π Y)

/-- The first-return map `π_Y` is injective. -/
theorem firstReturn_injective : Injective (firstReturn π Y) := by
  have key : ∀ y y' : Y, firstReturnTime π Y y ≤ firstReturnTime π Y y' →
      firstReturn π Y y = firstReturn π Y y' → y = y' := by
    intro y y' hle h
    have h' := congrArg Subtype.val h
    simp only [coe_firstReturn] at h'
    have hpos := firstReturnTime_pos (π := π) y
    have hy : (y : X) = (π ^ (firstReturnTime π Y y' - firstReturnTime π Y y)) y' := by
      have : π ^ firstReturnTime π Y y' = π ^ firstReturnTime π Y y *
          π ^ (firstReturnTime π Y y' - firstReturnTime π Y y) := by
        rw [← pow_add]
        congr 1
        omega
      rw [this, Perm.mul_apply] at h'
      exact (π ^ firstReturnTime π Y y).injective h'
    rcases Nat.eq_zero_or_pos (firstReturnTime π Y y' - firstReturnTime π Y y) with h0 | hp
    · rw [h0, pow_zero, Perm.one_apply] at hy
      exact Subtype.ext hy
    · exact absurd (hy ▸ y.2) (pow_apply_notMem_of_lt_firstReturnTime hp (by omega))
  intro y y' h
  rcases le_total (firstReturnTime π Y y) (firstReturnTime π Y y') with hle | hle
  · exact key y y' hle h
  · exact (key y' y hle h.symm).symm

/-- **A first-return map is a permutation**: `π_Y` is a bijection of `Y`. -/
@[cluster_algebras "lem_first_return_bijective"]
theorem firstReturn_bijective : Bijective (firstReturn π Y) :=
  Finite.injective_iff_bijective.1 (firstReturn_injective π Y)

/-- The first-return map `π_Y`, as a permutation of `Y`. -/
noncomputable def firstReturnPerm : Perm Y :=
  Equiv.ofBijective _ (firstReturn_bijective π Y)

/-- The permutation `firstReturnPerm π Y` acts as the first-return map. -/
@[simp]
theorem coe_firstReturnPerm : ⇑(firstReturnPerm π Y) = firstReturn π Y :=
  rfl

/-- Every iterate of the first-return map sends `y` to `π^n(y)` for some `n`. -/
theorem exists_coe_iterate_firstReturn (y : Y) (k : ℕ) :
    ∃ n : ℕ, ((firstReturn π Y)^[k] y : X) = (π ^ n) y := by
  induction k generalizing y with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨n, hn⟩ := ih (firstReturn π Y y)
    refine ⟨n + firstReturnTime π Y y, ?_⟩
    rw [iterate_succ_apply, hn, coe_firstReturn, pow_add, Perm.mul_apply]

/-- If `π^n(y) ∈ Y`, then `π^n(y)` is an iterate of the first-return map applied to `y`. -/
theorem exists_iterate_firstReturn_of_pow (n : ℕ) (y : Y) (hy : (π ^ n) y ∈ Y) :
    ∃ k : ℕ, ((firstReturn π Y)^[k] y : X) = (π ^ n) y := by
  induction n using Nat.strong_induction_on generalizing y with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, rfl⟩
  · have hle := firstReturnTime_le hn hy
    have hpos := firstReturnTime_pos (π := π) y
    have hsplit : (π ^ (n - firstReturnTime π Y y)) (firstReturn π Y y : X) = (π ^ n) y := by
      rw [coe_firstReturn, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hle]
    obtain ⟨k, hk⟩ := ih (n - firstReturnTime π Y y) (by omega) (firstReturn π Y y)
      (hsplit ▸ hy)
    exact ⟨k + 1, by rw [iterate_succ_apply, hk, hsplit]⟩

/-- **Orbits of a first-return map.** For `y, y' ∈ Y`, `y' = π_Y^k(y)` for some `k ≥ 0` if and
only if `y' = π^n(y)` for some `n ≥ 0`. -/
@[cluster_algebras "lem_first_return_orbits"]
theorem exists_iterate_firstReturn_eq_iff {y y' : Y} :
    (∃ k : ℕ, y' = (firstReturn π Y)^[k] y) ↔ ∃ n : ℕ, (y' : X) = (π ^ n) y := by
  constructor
  · rintro ⟨k, rfl⟩
    exact exists_coe_iterate_firstReturn π Y y k
  · rintro ⟨n, hn⟩
    obtain ⟨k, hk⟩ := exists_iterate_firstReturn_of_pow π Y n y (hn ▸ y'.2)
    exact ⟨k, Subtype.ext (hn.trans hk.symm)⟩

omit [Finite X] in
/-- Every `f^n(x)` lies in the orbit of `x` under `f`. -/
theorem sameCycle_pow_apply_self (f : Perm X) (x : X) (n : ℕ) : f.SameCycle x ((f ^ n) x) :=
  sameCycle_pow_right.2 (SameCycle.refl _ _)

/-- Two elements of `Y` lie in one orbit of `π_Y` if and only if they lie in one orbit of `π`. -/
theorem sameCycle_firstReturnPerm_iff {y y' : Y} :
    (firstReturnPerm π Y).SameCycle y y' ↔ π.SameCycle y y' := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [coe_pow, coe_firstReturnPerm] at hk
    obtain ⟨n, hn⟩ := (exists_iterate_firstReturn_eq_iff π Y).1 ⟨k, hk.symm⟩
    exact hn ▸ sameCycle_pow_apply_self π _ n
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    obtain ⟨k, hk⟩ := (exists_iterate_firstReturn_eq_iff π Y).2 ⟨n, hn.symm⟩
    rw [hk, ← coe_firstReturnPerm, ← coe_pow]
    exact sameCycle_pow_apply_self _ _ k

end FirstReturn

/-! ### Counting orbits -/

section NumOrbits

/-- The number of orbits of a permutation `σ` of `X`, that is, of classes of
`Equiv.Perm.SameCycle σ`. Fixed points of `σ` count as orbits. -/
noncomputable def numOrbits (σ : Perm X) : ℕ :=
  Nat.card (Quotient (SameCycle.setoid σ))

/-- `numOrbits σ` is the number of distinct orbits of `σ`, each read as a finite set. -/
theorem numOrbits_eq_card_image [Fintype X] [DecidableEq X] (σ : Perm X) :
    numOrbits σ = (Finset.univ.image fun x => ({y | σ.SameCycle x y} : Finset X)).card := by
  classical
  let g : Quotient (SameCycle.setoid σ) → Finset X :=
    Quotient.lift (fun x => ({y | σ.SameCycle x y} : Finset X)) fun a b hab => by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(hab : σ.SameCycle a b).symm.trans, (hab : σ.SameCycle a b).trans⟩
  have hg : Injective g := by
    intro u v huv
    induction u using Quotient.inductionOn with | h a => ?_
    induction v using Quotient.inductionOn with | h b => ?_
    have hb : b ∈ g ⟦a⟧ := by
      rw [huv]
      simp [g, SameCycle.refl]
    simp only [g, Quotient.lift_mk, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact Quotient.sound hb
  rw [numOrbits, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.card_image_of_injective _ hg]
  congr 1
  ext s
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, rfl⟩
    induction u using Quotient.inductionOn with | h a => exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟦a⟧, rfl⟩

variable [Finite X]

/-- If every orbit of `π` meets `Y`, the first-return map `π_Y` has as many orbits as `π`. -/
theorem numOrbits_firstReturnPerm (π : Perm X) (Y : Set X)
    (h : ∀ x, ∃ y ∈ Y, π.SameCycle x y) : numOrbits (firstReturnPerm π Y) = numOrbits π := by
  let f : Quotient (SameCycle.setoid (firstReturnPerm π Y)) → Quotient (SameCycle.setoid π) :=
    Quotient.map (fun y : Y => (y : X)) fun _ _ => (sameCycle_firstReturnPerm_iff π Y).1
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun u v huv => ?_, fun c => ?_⟩)
  · induction u using Quotient.inductionOn with | h a => ?_
    induction v using Quotient.inductionOn with | h b => ?_
    exact Quotient.sound ((sameCycle_firstReturnPerm_iff π Y).2 (Quotient.exact huv))
  · induction c using Quotient.inductionOn with | h x => ?_
    obtain ⟨y, hy, hxy⟩ := h x
    exact ⟨⟦⟨y, hy⟩⟧, Quotient.sound hxy.symm⟩

/-- If the orbits of `σ'` are those of `σ` with the two distinct orbits of `a` and `b` merged,
then `σ` has one orbit more than `σ'`. -/
theorem numOrbits_eq_add_one_of_merge {σ σ' : Perm X} {a b : X} (hab : ¬σ.SameCycle a b)
    (h : ∀ x y, σ'.SameCycle x y ↔ σ.SameCycle x y ∨ (σ.SameCycle x a ∧ σ.SameCycle y b) ∨
      (σ.SameCycle x b ∧ σ.SameCycle y a)) :
    numOrbits σ = numOrbits σ' + 1 := by
  classical
  cases nonempty_fintype X
  let f : Quotient (SameCycle.setoid σ) → Quotient (SameCycle.setoid σ') :=
    Quotient.map id fun x y hxy => (h x y).2 (Or.inl hxy)
  have hne : ∀ x, ¬σ.SameCycle x a → (⟦x⟧ : Quotient (SameCycle.setoid σ)) ≠ ⟦a⟧ :=
    fun x hx hxa => hx (Quotient.exact hxa)
  have himage : (Finset.univ.erase (⟦a⟧ : Quotient (SameCycle.setoid σ))).image f =
      Finset.univ := by
    refine Finset.eq_univ_iff_forall.2 fun c => ?_
    induction c using Quotient.inductionOn with | h x => ?_
    rw [Finset.mem_image]
    by_cases hx : σ.SameCycle x a
    · refine ⟨⟦b⟧, Finset.mem_erase.2 ⟨hne b fun hba => hab hba.symm, Finset.mem_univ _⟩, ?_⟩
      exact Quotient.sound ((h b x).2 (Or.inr (Or.inr ⟨SameCycle.refl _ _, hx⟩)))
    · exact ⟨⟦x⟧, Finset.mem_erase.2 ⟨hne x hx, Finset.mem_univ _⟩, rfl⟩
  have hinj : Set.InjOn f (Finset.univ.erase (⟦a⟧ : Quotient (SameCycle.setoid σ))) := by
    intro u hu v hv huv
    induction u using Quotient.inductionOn with | h x => ?_
    induction v using Quotient.inductionOn with | h y => ?_
    rcases (h x y).1 (Quotient.exact huv) with hxy | ⟨hxa, -⟩ | ⟨-, hya⟩
    · exact Quotient.sound hxy
    · exact ((Finset.mem_erase.1 hu).1 (Quotient.sound hxa)).elim
    · exact ((Finset.mem_erase.1 hv).1 (Quotient.sound hya)).elim
  have hcard := Finset.card_image_of_injOn hinj
  rw [himage, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Finset.card_univ] at hcard
  have hpos : 0 < Fintype.card (Quotient (SameCycle.setoid σ)) :=
    Fintype.card_pos_iff.2 ⟨⟦a⟧⟩
  rw [numOrbits, numOrbits, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard]
  omega

end NumOrbits

/-! ### Composing with a transposition -/

section Transposition

variable [DecidableEq X] (ρ : Perm X) {p q : X}

/-- Along an initial stretch of the `ρ`-orbit of `x` avoiding `p` and `q`, the permutations
`ρ` and `ρ * swap p q` agree. -/
theorem mul_swap_pow_apply_eq {x : X} {n : ℕ} (h : ∀ j < n, (ρ ^ j) x ≠ p ∧ (ρ ^ j) x ≠ q) :
    ((ρ * swap p q) ^ n) x = (ρ ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih (fun j hj => h j (by omega)), pow_succ' ρ,
      Perm.mul_apply, Perm.mul_apply,
      swap_apply_of_ne_of_ne (h n (by omega)).1 (h n (by omega)).2]

variable [Finite X]

/-- If the `ρ`-orbit of `x` contains `p` or `q`, then `ρ` and `ρ * swap p q` agree on its
initial stretch up to the first visit of `p` or `q`. -/
theorem exists_mul_swap_pow_apply {x : X} (hx : ρ.SameCycle x p ∨ ρ.SameCycle x q) :
    ∃ n : ℕ, ((ρ * swap p q) ^ n) x = (ρ ^ n) x ∧ ((ρ ^ n) x = p ∨ (ρ ^ n) x = q) := by
  classical
  have hex : ∃ n : ℕ, (ρ ^ n) x = p ∨ (ρ ^ n) x = q :=
    hx.elim (·.exists_nat_pow_eq.imp fun _ => Or.inl) (·.exists_nat_pow_eq.imp fun _ => Or.inr)
  exact ⟨Nat.find hex,
    mul_swap_pow_apply_eq ρ fun j hj => not_or.1 (Nat.find_min hex hj), Nat.find_spec hex⟩

/-- On an orbit of `ρ` containing neither `p` nor `q`, the permutation `ρ * swap p q` acts as
`ρ`. -/
theorem sameCycle_mul_swap_iff_of_not {x : X} (hp : ¬ρ.SameCycle x p) (hq : ¬ρ.SameCycle x q)
    (y : X) : (ρ * swap p q).SameCycle x y ↔ ρ.SameCycle x y := by
  have hpow : ∀ n, ((ρ * swap p q) ^ n) x = (ρ ^ n) x := fun n =>
    mul_swap_pow_apply_eq ρ fun j _ =>
      ⟨fun h => hp (h ▸ sameCycle_pow_apply_self ρ x j),
        fun h => hq (h ▸ sameCycle_pow_apply_self ρ x j)⟩
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [hpow]
    exact sameCycle_pow_apply_self ρ x n
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [← hpow]
    exact sameCycle_pow_apply_self _ x n

/-- If `p` and `q` lie in different orbits of `ρ`, they lie in one orbit of `ρ * swap p q`. -/
theorem sameCycle_mul_swap_of_not_sameCycle (hpq : ¬ρ.SameCycle p q) :
    (ρ * swap p q).SameCycle p q := by
  obtain ⟨n, hn, hpq''⟩ := exists_mul_swap_pow_apply ρ (p := p) (q := q) (x := ρ q)
    (Or.inr (sameCycle_apply_left.2 (SameCycle.refl _ _)))
  have hρq : (ρ * swap p q) p = ρ q := by rw [Perm.mul_apply, swap_apply_left]
  rcases hpq'' with h | h
  · have h1 : ρ.SameCycle (ρ q) p := by
      rw [← h]
      exact sameCycle_pow_apply_self ρ (ρ q) n
    exact absurd (sameCycle_apply_left.1 h1) fun h' => hpq h'.symm
  · have h2 : ((ρ * swap p q) ^ n) ((ρ * swap p q) p) = q := by rw [hρq, hn, h]
    have h3 : (ρ * swap p q).SameCycle p (((ρ * swap p q) ^ n) ((ρ * swap p q) p)) :=
      sameCycle_pow_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))
    rwa [h2] at h3

/-- If `p` and `q` lie in different orbits of `ρ`, everything in the `ρ`-orbits of `p` and `q`
lies in the `(ρ * swap p q)`-orbit of `p`. -/
theorem sameCycle_mul_swap_of_sameCycle_or (hpq : ¬ρ.SameCycle p q) {x : X}
    (hx : ρ.SameCycle x p ∨ ρ.SameCycle x q) : (ρ * swap p q).SameCycle x p := by
  obtain ⟨n, hn, h⟩ := exists_mul_swap_pow_apply ρ hx
  have hx' := sameCycle_pow_apply_self (ρ * swap p q) x n
  rw [hn] at hx'
  rcases h with h | h
  · exact h ▸ hx'
  · exact (h ▸ hx').trans (sameCycle_mul_swap_of_not_sameCycle ρ hpq).symm

/-- If `p` and `q` lie in different orbits of `ρ`, then the orbits of `ρ * swap p q` are those
of `ρ`, with the orbits of `p` and `q` merged into one. -/
theorem sameCycle_mul_swap_iff (hpq : ¬ρ.SameCycle p q) {x y : X} :
    (ρ * swap p q).SameCycle x y ↔ ρ.SameCycle x y ∨ (ρ.SameCycle x p ∧ ρ.SameCycle y q) ∨
      (ρ.SameCycle x q ∧ ρ.SameCycle y p) := by
  have hA : ∀ x, ρ.SameCycle x p ∨ ρ.SameCycle x q → (ρ * swap p q).SameCycle x p :=
    fun _ => sameCycle_mul_swap_of_sameCycle_or ρ hpq
  constructor
  · intro h
    by_cases hx : ρ.SameCycle x p ∨ ρ.SameCycle x q
    · have hy : ρ.SameCycle y p ∨ ρ.SameCycle y q := by
        by_contra hy
        rw [not_or] at hy
        have hyx := (sameCycle_mul_swap_iff_of_not ρ hy.1 hy.2 x).1 h.symm
        exact not_or.2 hy (hx.imp hyx.trans hyx.trans)
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (hx.trans hy.symm)
      · exact Or.inr (Or.inl ⟨hx, hy⟩)
      · exact Or.inr (Or.inr ⟨hx, hy⟩)
      · exact Or.inl (hx.trans hy.symm)
    · rw [not_or] at hx
      exact Or.inl ((sameCycle_mul_swap_iff_of_not ρ hx.1 hx.2 y).1 h)
  · rintro (h | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · by_cases hx : ρ.SameCycle x p ∨ ρ.SameCycle x q
      · have hy : ρ.SameCycle y p ∨ ρ.SameCycle y q := hx.imp h.symm.trans h.symm.trans
        exact (hA x hx).trans (hA y hy).symm
      · rw [not_or] at hx
        exact (sameCycle_mul_swap_iff_of_not ρ hx.1 hx.2 y).2 h
    · exact (hA x (Or.inl hx)).trans (hA y (Or.inr hy)).symm
    · exact (hA x (Or.inr hx)).trans (hA y (Or.inl hy)).symm

/-- If `p ≠ q` lie in one orbit of `ρ`, they lie in different orbits of `ρ * swap p q`. -/
theorem not_sameCycle_mul_swap (hne : p ≠ q) (h : ρ.SameCycle p q) :
    ¬(ρ * swap p q).SameCycle p q := by
  classical
  have hex : ∃ k : ℕ, (ρ ^ (k + 1)) p = q := by
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rcases n with _ | k
    · exact absurd hn hne
    · exact ⟨k, hn⟩
  obtain ⟨k, hq, hmin⟩ : ∃ k, (ρ ^ (k + 1)) p = q ∧ ∀ j < k, (ρ ^ (j + 1)) p ≠ q :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hnp : ∀ j ≤ k, (ρ ^ (j + 1)) p ≠ p := by
    intro j hj hjp
    rcases hj.lt_or_eq with hj | rfl
    · have h1 : (ρ ^ (k + 1)) p = (ρ ^ (k - j - 1 + 1)) ((ρ ^ (j + 1)) p) := by
        rw [← Perm.mul_apply, ← pow_add]
        congr 2
        omega
      rw [hjp] at h1
      exact hmin (k - j - 1) (by omega) (h1.symm.trans hq)
    · exact hne (hjp.symm.trans hq)
  have hS : ∀ j ≤ k, ∃ i ≤ k, (ρ ^ (i + 1)) p = (ρ * swap p q) ((ρ ^ (j + 1)) p) := by
    intro j hj
    rcases hj.lt_or_eq with hj | rfl
    · refine ⟨j + 1, hj, ?_⟩
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hnp j hj.le) (hmin j hj), pow_succ' ρ (j + 1),
        Perm.mul_apply]
    · refine ⟨0, Nat.zero_le _, ?_⟩
      rw [hq, Perm.mul_apply, swap_apply_right, zero_add, pow_one]
  have hpow : ∀ n : ℕ, ∃ i ≤ k, (ρ ^ (i + 1)) p = ((ρ * swap p q) ^ n) q := by
    intro n
    induction n with
    | zero => exact ⟨k, le_rfl, hq⟩
    | succ n ih =>
      obtain ⟨i, hi, hin⟩ := ih
      rw [pow_succ', Perm.mul_apply, ← hin]
      exact hS i hi
  intro hpq
  obtain ⟨n, hn⟩ := hpq.symm.exists_nat_pow_eq
  obtain ⟨i, hi, hin⟩ := hpow n
  exact hnp i hi (hin.trans hn)

/-- **Composing with a transposition splits one orbit**: if `p ≠ q` lie in one orbit of `ρ`, then
`ρ ∘ (p q)` has one orbit more than `ρ`. -/
@[cluster_algebras "lem_transposition_orbit_count"]
theorem numOrbits_mul_swap_of_sameCycle (hne : p ≠ q) (h : ρ.SameCycle p q) :
    numOrbits (ρ * swap p q) = numOrbits ρ + 1 := by
  have h' := not_sameCycle_mul_swap ρ hne h
  refine numOrbits_eq_add_one_of_merge h' fun x y => ?_
  simpa only [mul_swap_mul_self] using sameCycle_mul_swap_iff (ρ * swap p q) h' (x := x) (y := y)

/-- **Composing with a transposition merges two orbits**: if `p` and `q` lie in different orbits
of `ρ`, then `ρ ∘ (p q)` has one orbit fewer than `ρ`. -/
@[cluster_algebras "lem_transposition_orbit_count"]
theorem numOrbits_mul_swap_of_not_sameCycle (h : ¬ρ.SameCycle p q) :
    numOrbits (ρ * swap p q) = numOrbits ρ - 1 := by
  have := numOrbits_eq_add_one_of_merge h fun _ _ => sameCycle_mul_swap_iff ρ h
  omega

end Transposition

/-! ### The rotation induced off an edge -/

section InducedRotation

variable {H : Type*} [Finite H]

/-- The **rotation induced off an edge**: for permutations `ι`, `σ` of `H` and `d ∈ H`, the
first-return map of `τ = σ ∘ (d ι(d))` to `H' = H \ {d, ι d}`. In FWZ `ι` is a
fixed-point-free involution; the definition does not need it. -/
@[cluster_algebras "def_induced_rotation"]
noncomputable def inducedRotation [DecidableEq H] (ι σ : Perm H) (d : H) :
    ({d, ι d}ᶜ : Set H) → ({d, ι d}ᶜ : Set H) :=
  firstReturn (σ * swap d (ι d)) ({d, ι d}ᶜ)

/-- The rotation induced off an edge, as a permutation of `H \ {d, ι d}`. -/
noncomputable def inducedRotationPerm [DecidableEq H] (ι σ : Perm H) (d : H) :
    Perm ({d, ι d}ᶜ : Set H) :=
  firstReturnPerm (σ * swap d (ι d)) ({d, ι d}ᶜ)

/-- The permutation `inducedRotationPerm ι σ d` acts as the induced rotation. -/
@[simp]
theorem coe_inducedRotationPerm [DecidableEq H] (ι σ : Perm H) (d : H) :
    ⇑(inducedRotationPerm ι σ d) = inducedRotation ι σ d :=
  rfl

/-- The induced rotation `inducedRotation ι σ d` is the first-return map of `σ ∘ (d ι(d))` to
`H \ {d, ι d}`. -/
theorem inducedRotation_eq_firstReturn [DecidableEq H] (ι σ : Perm H) (d : H) :
    inducedRotation ι σ d = firstReturn (σ * swap d (ι d)) ({d, ι d}ᶜ) :=
  rfl

omit [Finite H] in
/-- An involution `ι` preserves `H \ {d, ι d}`. -/
theorem apply_mem_compl_pair_iff {ι : Perm H} (hι : Involutive ι) (d x : H) :
    ι x ∈ ({d, ι d}ᶜ : Set H) ↔ x ∈ ({d, ι d}ᶜ : Set H) := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, hι.eq_iff, hι d]
  tauto

/-- The rotation induced off an edge is a permutation of `H \ {d, ι d}`. -/
@[cluster_algebras "lem_contraction_face_orbit_count"]
theorem inducedRotation_bijective [DecidableEq H] (ι σ : Perm H) (d : H) :
    Bijective (inducedRotation ι σ d) :=
  firstReturn_bijective _ _

/-- The face permutation after contracting: `σ' ∘ ι|_{H'}` is the first-return map of
`φ = σ ∘ ι` to `H' = H \ {d, ι d}`. -/
theorem inducedRotationPerm_mul_subtypePerm [DecidableEq H] {ι : Perm H} (hι : Involutive ι)
    (σ : Perm H) (d : H) :
    inducedRotationPerm ι σ d * ι.subtypePerm (apply_mem_compl_pair_iff hι d) =
      firstReturnPerm (σ * ι) ({d, ι d}ᶜ) := by
  set Y : Set H := ({d, ι d}ᶜ : Set H)
  have hY : ∀ x, x ∉ Y ↔ x = d ∨ x = ι d := by
    intro x
    simp only [Y, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_not]
  have hτ : ∀ y, y ∉ Y → (σ * swap d (ι d)) y = (σ * ι) y := by
    intro y hy
    rcases (hY y).1 hy with rfl | rfl
    · rw [Perm.mul_apply, Perm.mul_apply, swap_apply_left]
    · rw [Perm.mul_apply, Perm.mul_apply, swap_apply_right, hι]
  ext ⟨x, hx⟩
  simp only [Perm.mul_apply, coe_inducedRotationPerm, Perm.subtypePerm_apply,
    coe_firstReturnPerm, inducedRotation_eq_firstReturn]
  have hιx : ι x ∈ Y := (apply_mem_compl_pair_iff hι d x).2 hx
  have key : ∀ j, 0 < j → (∀ i, 0 < i → i < j → ((σ * ι) ^ i) x ∉ Y) →
      ((σ * swap d (ι d)) ^ j) (ι x) = ((σ * ι) ^ j) x := by
    intro j
    induction j with
    | zero => exact fun h => absurd h (lt_irrefl 0)
    | succ j ih =>
      intro _ hmin
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · have hd : ι x ≠ d ∧ ι x ≠ ι d := by
          simpa [Y, not_or] using hιx
        rw [pow_one, pow_one, Perm.mul_apply, Perm.mul_apply,
          swap_apply_of_ne_of_ne hd.1 hd.2]
      · rw [pow_succ', Perm.mul_apply, ih hj fun i hi hij => hmin i hi (by omega),
          hτ _ (hmin j hj (by omega)), ← Perm.mul_apply, ← pow_succ']
  set m := firstReturnTime (σ * ι) Y ⟨x, hx⟩ with hm
  have hmpos : 0 < m := firstReturnTime_pos _
  have hmin : ∀ i, 0 < i → i < m → ((σ * ι) ^ i) x ∉ Y := fun i hi him =>
    pow_apply_notMem_of_lt_firstReturnTime (y := ⟨x, hx⟩) hi him
  have hmem : ((σ * ι) ^ m) x ∈ Y := pow_firstReturnTime_apply_mem (y := ⟨x, hx⟩)
  rw [coe_firstReturn (σ * ι) Y ⟨x, hx⟩, ← hm]
  refine (coe_firstReturn_of_pow (y := ⟨ι x, hιx⟩) hmpos ?_ ?_).trans (key m hmpos hmin)
  · rwa [key m hmpos hmin]
  · intro j hj hjm
    rw [key j hj fun i hi hij => hmin i hi (by omega)]
    exact hmin j hj hjm

/-- **Contracting an edge keeps the number of face orbits.** Let `ι` be an involution of the
finite set `H`, `σ` a permutation of `H` and `d ∈ H`, and let `σ'` be the rotation induced on
`H' = H \ {d, ι d}`. If every orbit of `φ = σ ∘ ι` meets `H'`, then the permutation
`σ' ∘ ι|_{H'}` of `H'` has exactly as many orbits as `φ`. -/
@[cluster_algebras "lem_contraction_face_orbit_count"]
theorem numOrbits_inducedRotationPerm_mul [DecidableEq H] {ι : Perm H} (hι : Involutive ι)
    (σ : Perm H) (d : H) (h : ∀ x, ∃ y ∈ ({d, ι d}ᶜ : Set H), (σ * ι).SameCycle x y) :
    numOrbits (inducedRotationPerm ι σ d * ι.subtypePerm (apply_mem_compl_pair_iff hι d)) =
      numOrbits (σ * ι) := by
  rw [inducedRotationPerm_mul_subtypePerm hι, numOrbits_firstReturnPerm _ _ h]

end InducedRotation

/-! ### Orbits avoiding a subset -/

/-- **Orbits avoiding a subset under a first return.** Let `π` be a permutation of a finite set
`X` and `L ⊆ Y ⊆ X`, with every orbit of `π` meeting `Y`. Then `π` has an orbit disjoint from `L`
if and only if the first-return map `π_Y` has an orbit disjoint from `L`. -/
@[cluster_algebras "lem_first_return_free_orbit"]
theorem exists_forall_sameCycle_notMem_iff [Finite X] (π : Perm X) {Y L : Set X} (hLY : L ⊆ Y)
    (h : ∀ x, ∃ y ∈ Y, π.SameCycle x y) :
    (∃ x, ∀ z, π.SameCycle x z → z ∉ L) ↔
      ∃ y : Y, ∀ z : Y, (firstReturnPerm π Y).SameCycle y z → (z : X) ∉ L := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hxy⟩ := h x
    exact ⟨⟨y, hy⟩, fun z hz => hx z (hxy.trans ((sameCycle_firstReturnPerm_iff π Y).1 hz))⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, fun z hz hzL => hy ⟨z, hLY hzL⟩ ((sameCycle_firstReturnPerm_iff π Y).2 hz) hzL⟩

end ClusterAlgebras

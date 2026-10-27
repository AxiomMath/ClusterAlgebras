/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.Affinization
public import ClusterAlgebras.Plabic.BridgeSequence

/-!
# Wires of a bridge sequence

Let `f` be a map `ℤ → ℤ` and `s = ((i₁, j₁), …, (i_r, j_r))` a bridge sequence for `f`, with
partial products `f₀ = f, …, f_r` and position maps `ρ_t = τ_t ∘ ⋯ ∘ τ₁`, where `τ_t` is the
transposition of `[1, b]` exchanging `i_t` and `j_t`. The *wire* of a letter `x ∈ [1, b]` is the
sequence of its positions `ρ₀(x), …, ρ_r(x)`; it carries the value `f(x)`, in that
`f_t(ρ_t(x)) = f(x)`.

Every integer is a fixed point of `f_r` modulo `b`, so `f(x) ≡ ρ_r(x) (mod b)`. For the
affinization of a decorated permutation `π̃ = (π, ε)` this says that the bridge sequence factors
the permutation: `π = τ_r ∘ ⋯ ∘ τ₁`.

For an `(a, b)`-bounded affine permutation `f`, wires behave like the strands of a reduced wiring
diagram. Two wires `x, y` whose values are in the wrong order, `f(x) > f(y)`, cannot cross after
they are in the right order: if `ρ_{t₀}(x) < ρ_{t₀}(y)`, then `ρ_{t₁}(x) < ρ_{t₁}(y)` for every
`t₁ ≥ t₀` at which neither wire has come to rest at a fixed point of `f_{t₁}`. A wire of value
`f(x) = z + b` stays weakly right of the line `z`, and a wire of value `f(x) = z` stays weakly
left of it.

## Main results

* `ClusterAlgebras.IsBridgeSequence.positionMap_modEq`: `ρ_r(x) ≡ f(x) (mod b)`.
* `ClusterAlgebras.DecoratedPerm.perm_eq_positionMap`: a bridge sequence for the affinization of
  `π̃ = (π, ε)` factors `π = τ_r ∘ ⋯ ∘ τ₁`.
* `ClusterAlgebras.IsBridgeSequence.positionMap_lt_positionMap`: two wires cross at most once.
* `ClusterAlgebras.IsBridgeSequence.le_positionMap_of_apply_eq_add`: a wire of value `z + b`
  stays weakly right of the line `z`.
* `ClusterAlgebras.IsBridgeSequence.positionMap_le_of_apply_eq`: a wire of value `z` stays weakly
  left of the line `z`.

## Implementation notes

* As in `ClusterAlgebras.Plabic.SwapProducts`, the letters of the wires are the integers of
  `[1, b]` and the position map `ρ_t` is a permutation of `ℤ` fixing every integer outside
  `[1, b]`; its restriction to `[1, b]` is FWZ's `ρ_t = τ_t ∘ ⋯ ∘ τ₁`. In the
  factorization of `π`, whose letters are `Fin b`, the letter `x : Fin b` is the integer
  `(x : ℤ) + 1`.
* The sequence is indexed from `0`, the position maps and partial products by `t : ℕ`; for
  `t ≥ r` they are constant, equal to their values at `r`. So the statements on wires hold for
  every `t`, not only for `t ∈ [0, r]`, and FWZ's hypothesis `t₁ ≤ r` is not needed.
* The crossing lemma does not use boundedness; it holds for every map with a bridge sequence.
* Two letters `x, y ∈ [1, b]` with `f(x) ≡ f(y) (mod b)` are equal
  (`IsBoundedAffinePerm.eq_of_apply_modEq`); this is the injectivity of `π_f`
  (`bijective_affineResidue`), proved directly from the injectivity and periodicity of `f`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7.
-/

@[expose] public section

namespace ClusterAlgebras

/-- Two integers of `[1, b]` congruent modulo `b` are equal. -/
theorem eq_of_modEq_of_mem_Icc {b : ℕ} {x y : ℤ} (hx : 1 ≤ x ∧ x ≤ b) (hy : 1 ≤ y ∧ y ≤ b)
    (h : x ≡ y [ZMOD b]) : x = y := by
  have := Int.eq_zero_of_abs_lt_dvd (m := b) (x := y - x) (Int.modEq_iff_dvd.mp h)
    (by rw [abs_lt]; omega)
  omega

/-- Two letters `x, y ∈ [1, b]` whose values under an `(a, b)`-bounded affine permutation are
congruent modulo `b` are equal. -/
theorem IsBoundedAffinePerm.eq_of_apply_modEq {a b : ℕ} {f : ℤ → ℤ}
    (hf : IsBoundedAffinePerm a b f) {x y : ℤ} (hx : 1 ≤ x ∧ x ≤ b) (hy : 1 ≤ y ∧ y ≤ b)
    (h : f x ≡ f y [ZMOD b]) : x = y := by
  obtain ⟨m, hm⟩ := Int.modEq_iff_add_fac.1 h
  have e : f y = f (x + m * b) := by
    rw [apply_add_mul_of_apply_add hf.apply_add, hm]
    ring
  refine eq_of_modEq_of_mem_Icc hx hy ?_
  rw [hf.bijective.1 e]
  simp [Int.ModEq]

section PositionMap

variable {s : List (ℤ × ℤ)}

/-- If all pairs of `s` lie in `[1, b]`, the position maps fix every integer outside `[1, b]`. -/
theorem positionMap_apply_of_not_mem_Icc {b : ℤ}
    (hs : ∀ p ∈ s, (1 ≤ p.1 ∧ p.1 ≤ b) ∧ (1 ≤ p.2 ∧ p.2 ≤ b)) (t : ℕ) {x : ℤ}
    (hx : ¬ (1 ≤ x ∧ x ≤ b)) : positionMap s t x = x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rcases lt_or_ge t s.length with ht | ht
    · have hp := hs _ (List.getElem_mem ht)
      rw [positionMap_succ ht, Equiv.Perm.mul_apply, ih,
        Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hx hp.1)
          (by rintro rfl; exact hx hp.2)]
    · rwa [positionMap_of_length_le (by omega), ← positionMap_of_length_le ht]

/-- If all pairs of `s` lie in `[1, b]`, the inverses of the position maps send `[1, b]` to
itself. -/
theorem positionMap_symm_mem_Icc {b : ℤ}
    (hs : ∀ p ∈ s, (1 ≤ p.1 ∧ p.1 ≤ b) ∧ (1 ≤ p.2 ∧ p.2 ≤ b)) (t : ℕ) {z : ℤ}
    (hz : 1 ≤ z ∧ z ≤ b) : 1 ≤ (positionMap s t).symm z ∧ (positionMap s t).symm z ≤ b := by
  by_contra h
  have e := positionMap_apply_of_not_mem_Icc hs t h
  rw [Equiv.apply_symm_apply] at e
  exact h (e ▸ hz)

end PositionMap

section Wires

variable {a b : ℕ} {f : ℤ → ℤ} {s : List (ℤ × ℤ)}

/-- Every letter `x ∈ [1, b]` satisfies `ρ_r(x) ≡ f(x) (mod b)`, where `ρ_r` is the last position
map of a bridge sequence for `f`. -/
theorem IsBridgeSequence.positionMap_modEq (hs : IsBridgeSequence b f s) {x : ℤ}
    (hx : 1 ≤ x ∧ x ≤ b) : positionMap s s.length x ≡ f x [ZMOD b] := by
  have h := hs.isFixedPointMod (positionMap s s.length x)
  rw [IsFixedPointMod, swapProduct_positionMap f hs.mem_Icc _ hx] at h
  exact h.symm

/-- Once a wire is at a fixed point `p ∈ [1, b]` of the partial product `f_t`, it stays at `p`. -/
theorem IsBridgeSequence.positionMap_eq_of_isFixedPointMod (hs : IsBridgeSequence b f s)
    {x : ℤ} {t : ℕ} (hfix : IsFixedPointMod b (swapProduct b f s t) (positionMap s t x))
    (hx : 1 ≤ positionMap s t x ∧ positionMap s t x ≤ b) {u : ℕ} (hu : t ≤ u) :
    positionMap s u x = positionMap s t x := by
  induction u, hu using Nat.le_induction with
  | base => rfl
  | succ u htu ih =>
    rcases lt_or_ge u s.length with hul | hul
    · obtain ⟨h1, h2⟩ := hs.ne_of_isFixedPointMod hx hfix hul htu
      rw [positionMap_succ hul, Equiv.Perm.mul_apply, ih, Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rwa [positionMap_of_length_le (by omega), ← positionMap_of_length_le hul]

/-- If the wire of `x ∈ [1, b]` is not at a fixed point of `f_u`, it was not at a fixed point of
`f_t` for any `t ≤ u`. -/
theorem IsBridgeSequence.not_isFixedPointMod_positionMap_of_le (hs : IsBridgeSequence b f s)
    {x : ℤ} (hx : 1 ≤ x ∧ x ≤ b) {t u : ℕ} (htu : t ≤ u)
    (h : ¬ IsFixedPointMod b (swapProduct b f s u) (positionMap s u x)) :
    ¬ IsFixedPointMod b (swapProduct b f s t) (positionMap s t x) := by
  intro hfix
  have hm := positionMap_mem_Icc (b := (b : ℤ)) hs.mem_Icc t hx
  rw [hs.positionMap_eq_of_isFixedPointMod hfix hm htu] at h
  exact h (hs.isFixedPointMod_swapProduct hm hfix htu)

end Wires

/-- **A bridge sequence factors the permutation.** Let `π̃ = (π, ε)` be a decorated permutation on
`b` letters and `s` a bridge sequence of length `r` for its affinization `f_π̃`. Then
`π = τ_r ∘ ⋯ ∘ τ₁`, where `τ_t` is the transposition of `[1, b]` exchanging `i_t` and `j_t`: the
last position map `ρ_r = τ_r ∘ ⋯ ∘ τ₁` sends the letter `x` to `π(x)`. The letter `x : Fin b` is
the integer `(x : ℤ) + 1`. -/
@[cluster_algebras "lem_bridge_sequence_factorization"]
theorem DecoratedPerm.perm_eq_positionMap {b : ℕ} (π : DecoratedPerm b) {s : List (ℤ × ℤ)}
    (hs : IsBridgeSequence b π.affinization s) (x : Fin b) :
    ((π.perm x : ℕ) : ℤ) + 1 = positionMap s s.length ((x : ℕ) + 1) := by
  have hx : 1 ≤ ((x : ℕ) : ℤ) + 1 ∧ ((x : ℕ) : ℤ) + 1 ≤ b := by omega
  have hπ : 1 ≤ ((π.perm x : ℕ) : ℤ) + 1 ∧ ((π.perm x : ℕ) : ℤ) + 1 ≤ b := by omega
  refine eq_of_modEq_of_mem_Icc hπ (positionMap_mem_Icc (b := (b : ℤ)) hs.mem_Icc _ hx) ?_
  refine Int.ModEq.trans ?_ (hs.positionMap_modEq hx).symm
  rw [π.affinization_natCast_add_one]
  split_ifs <;> simp [Int.ModEq]

section Wires

variable {a b : ℕ} {f : ℤ → ℤ} {s : List (ℤ × ℤ)}

/-- **Two wires cross at most once.** Let `s` be a bridge sequence for `f` with partial products
`f_t` and position maps `ρ_t`. Let `x, y ∈ [1, b]` and `t₀ ≤ t₁` be such that
`ρ_{t₀}(x) < ρ_{t₀}(y)`, `f(x) > f(y)`, and neither `ρ_{t₁}(x)` nor `ρ_{t₁}(y)` is a fixed point of
`f_{t₁}` modulo `b`. Then `ρ_{t₁}(x) < ρ_{t₁}(y)`. (FWZ assume `f` is an `(a, b)`-bounded
affine permutation and `t₁ ≤ r`; neither is needed.) -/
@[cluster_algebras "lem_bridge_wire_order"]
theorem IsBridgeSequence.positionMap_lt_positionMap (hs : IsBridgeSequence b f s) {x y : ℤ}
    (hx : 1 ≤ x ∧ x ≤ b) (hy : 1 ≤ y ∧ y ≤ b) {t₀ t₁ : ℕ} (ht : t₀ ≤ t₁)
    (hlt : positionMap s t₀ x < positionMap s t₀ y) (hf : f y < f x)
    (hx₁ : ¬ IsFixedPointMod b (swapProduct b f s t₁) (positionMap s t₁ x))
    (hy₁ : ¬ IsFixedPointMod b (swapProduct b f s t₁) (positionMap s t₁ y)) :
    positionMap s t₁ x < positionMap s t₁ y := by
  suffices H : ∀ t, t₀ ≤ t → t ≤ t₁ → positionMap s t x < positionMap s t y from
    H t₁ ht le_rfl
  intro t h0
  induction t, h0 using Nat.le_induction with
  | base => exact fun _ => hlt
  | succ t h0 ih =>
    intro h1
    have ih := ih (by omega)
    rcases lt_or_ge t s.length with hl | hl
    · have hp := hs.isBridgePair t hl
      have hnx := hs.not_isFixedPointMod_positionMap_of_le hx (by omega : t ≤ t₁) hx₁
      have hny := hs.not_isFixedPointMod_positionMap_of_le hy (by omega : t ≤ t₁) hy₁
      have hxi : ¬ (s[t].1 < positionMap s t x ∧ positionMap s t x < s[t].2) := fun h =>
        hnx (hp.isFixedPointMod_of_lt_of_lt _ h.1 h.2)
      have hyi : ¬ (s[t].1 < positionMap s t y ∧ positionMap s t y < s[t].2) := fun h =>
        hny (hp.isFixedPointMod_of_lt_of_lt _ h.1 h.2)
      have hij : ¬ (positionMap s t x = s[t].1 ∧ positionMap s t y = s[t].2) := by
        rintro ⟨e1, e2⟩
        have := hp.apply_lt_apply
        rw [← e1, ← e2, swapProduct_positionMap f hs.mem_Icc t hx,
          swapProduct_positionMap f hs.mem_Icc t hy] at this
        omega
      have := hp.lt
      rw [positionMap_succ hl, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        Equiv.swap_apply_def]
      split_ifs <;> omega
    · rwa [positionMap_of_length_le (by omega), ← positionMap_of_length_le hl]

/-- Along a bridge sequence for `f`, there is a least `t₁ ≥ t` at which a given integer `z` is a
fixed point of `f_{t₁}`. -/
private theorem IsBridgeSequence.exists_isFixedPointMod_add (hs : IsBridgeSequence b f s)
    (t : ℕ) (z : ℤ) : ∃ k, IsFixedPointMod b (swapProduct b f s (t + k)) z :=
  ⟨s.length, by
    rw [swapProduct_of_length_le (by omega)]
    exact hs.isFixedPointMod z⟩

/-- The wire arriving at the line `z` when `z` becomes a fixed point is the wire whose value is
congruent to `z`: if `z ∈ [1, b]` is a fixed point of `f_t` and `f(x) ≡ z (mod b)` for a letter
`x ∈ [1, b]`, then `ρ_t(x) = z`. -/
theorem IsBridgeSequence.positionMap_eq_of_isFixedPointMod_of_modEq (hs : IsBridgeSequence b f s)
    (hf : IsBoundedAffinePerm a b f) {x z : ℤ} (hx : 1 ≤ x ∧ x ≤ b) (hz : 1 ≤ z ∧ z ≤ b) {t : ℕ}
    (hfix : IsFixedPointMod b (swapProduct b f s t) z) (hxz : f x ≡ z [ZMOD b]) :
    positionMap s t x = z := by
  have hy := positionMap_symm_mem_Icc (b := (b : ℤ)) hs.mem_Icc t hz
  have hvy := swapProduct_positionMap f hs.mem_Icc t hy
  rw [Equiv.apply_symm_apply] at hvy
  have hxy : x = (positionMap s t).symm z := by
    refine hf.eq_of_apply_modEq hx hy (hxz.trans ?_)
    rw [← hvy]
    exact hfix.symm
  rw [hxy, Equiv.apply_symm_apply]

/-- **A wire of value `z + b` stays weakly right of the line `z`.** Let `f` be an `(a, b)`-bounded
affine permutation and `s` a bridge sequence for `f`. If `x, z ∈ [1, b]` and `f(x) = z + b`, then
`ρ_t(x) ≥ z` for every `t`. -/
@[cluster_algebras "lem_bridge_wire_white_line"]
theorem IsBridgeSequence.le_positionMap_of_apply_eq_add (hs : IsBridgeSequence b f s)
    (hf : IsBoundedAffinePerm a b f) {x z : ℤ} (hx : 1 ≤ x ∧ x ≤ b) (hz : 1 ≤ z ∧ z ≤ b)
    (hfx : f x = z + b) (t : ℕ) : z ≤ positionMap s t x := by
  classical
  by_contra! h0
  have hex := hs.exists_isFixedPointMod_add t z
  have key : ∀ k ≤ Nat.find hex, positionMap s (t + k) x < z := by
    intro k
    induction k with
    | zero => exact fun _ => by simpa using h0
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      have hnz := Nat.find_min hex (show k < Nat.find hex by omega)
      rw [← add_assoc]
      rcases lt_or_ge (t + k) s.length with hl | hl
      · have hp := hs.isBridgePair (t + k) hl
        have hv := (hs.isBoundedAffinePerm_swapProduct hf (t + k)).isBridgePair_values hp
        have hvx := swapProduct_positionMap f hs.mem_Icc (t + k) hx
        have hzi : ¬ (s[t + k].1 < z ∧ z < s[t + k].2) := fun h =>
          hnz (hp.isFixedPointMod_of_lt_of_lt _ h.1 h.2)
        have hzj : ¬ (positionMap s (t + k) x = s[t + k].1 ∧ s[t + k].2 = z) := by
          rintro ⟨e1, e2⟩
          rw [e1] at hvx
          omega
        have := hp.lt
        rw [positionMap_succ hl, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
        split_ifs <;> omega
      · rwa [positionMap_of_length_le (by omega), ← positionMap_of_length_le hl]
  have h1 := key _ le_rfl
  rw [hs.positionMap_eq_of_isFixedPointMod_of_modEq hf hx hz (Nat.find_spec hex)
    (by simp [hfx, Int.ModEq])] at h1
  exact lt_irrefl _ h1

/-- **A wire of value `z` stays weakly left of the line `z`.** Let `f` be an `(a, b)`-bounded
affine permutation and `s` a bridge sequence for `f`. If `x, z ∈ [1, b]` and `f(x) = z`, then
`ρ_t(x) ≤ z` for every `t`. -/
@[cluster_algebras "lem_bridge_wire_black_line"]
theorem IsBridgeSequence.positionMap_le_of_apply_eq (hs : IsBridgeSequence b f s)
    (hf : IsBoundedAffinePerm a b f) {x z : ℤ} (hx : 1 ≤ x ∧ x ≤ b) (hz : 1 ≤ z ∧ z ≤ b)
    (hfx : f x = z) (t : ℕ) : positionMap s t x ≤ z := by
  classical
  by_contra! h0
  have hex := hs.exists_isFixedPointMod_add t z
  have key : ∀ k ≤ Nat.find hex, z < positionMap s (t + k) x := by
    intro k
    induction k with
    | zero => exact fun _ => by simpa using h0
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      have hnz := Nat.find_min hex (show k < Nat.find hex by omega)
      rw [← add_assoc]
      rcases lt_or_ge (t + k) s.length with hl | hl
      · have hp := hs.isBridgePair (t + k) hl
        have hft := hs.isBoundedAffinePerm_swapProduct hf (t + k)
        have hle := hft.le_apply s[t + k].1
        have hvx := swapProduct_positionMap f hs.mem_Icc (t + k) hx
        have hzi : ¬ (s[t + k].1 < z ∧ z < s[t + k].2) := fun h =>
          hnz (hp.isFixedPointMod_of_lt_of_lt _ h.1 h.2)
        have hzj : ¬ (positionMap s (t + k) x = s[t + k].2 ∧ s[t + k].1 = z) := by
          rintro ⟨e1, e2⟩
          rw [e1] at hvx
          have := hp.apply_lt_apply
          omega
        have := hp.lt
        rw [positionMap_succ hl, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
        split_ifs <;> omega
      · rwa [positionMap_of_length_le (by omega), ← positionMap_of_length_le hl]
  have h1 := key _ le_rfl
  rw [hs.positionMap_eq_of_isFixedPointMod_of_modEq hf hx hz (Nat.find_spec hex)
    (by rw [hfx])] at h1
  exact lt_irrefl _ h1

end Wires

end ClusterAlgebras

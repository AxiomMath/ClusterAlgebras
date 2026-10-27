/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.TripleDiagram
public import ClusterAlgebras.Plabic.FirstReturn

/-!
# Swivel moves

Let `X` be a triple diagram and `{d₁, d₂}` a digon of `X`, with `d₂ = φ(d₁)`, at the triple points
`x = v(d₁)` and `y = v(d₂)`, whose rotations are `(d̄₂, d₁, a₁, a₂, a₃, a₄)` and
`(d̄₁, d₂, b₁, b₂, b₃, b₄)`. The swivel move `X'` replaces them by `(d̄₂, d₁, a₃, a₄, b₁, b₂)` and
`(d̄₁, d₂, b₃, b₄, a₁, a₂)`. This file proves the basic facts about swivel moves.

## Main results

* `ClusterAlgebras.TripleData.IsDigon.exists_swivel`: the darts at a digon and the cycles of the
  swivel rotation.
* `ClusterAlgebras.TripleData.IsDigon.isPreTripleDiagram_swivelMove`,
  `ClusterAlgebras.TripleData.IsDigon.isTripleDiagram_swivelMove`: a swivel move of a (pre-)triple
  diagram is a (pre-)triple diagram.
* `ClusterAlgebras.TripleData.Iso.swivelMove`, `ClusterAlgebras.TripleData.Iso.isDigon_faceOf_map`:
  swivel moves commute with isomorphisms.
* `ClusterAlgebras.TripleData.IsDigon.swivelMove_swivelMove`: a swivel move is an involution up to
  isomorphism.
* `ClusterAlgebras.TripleData.IsDigon.strandPerm_swivelMove`: a swivel move preserves the strand
  permutation.

## Implementation notes

* A digon is given, as in `TripleDiagram.IsSwivelMove`, by one of its darts `d₁`: the hypothesis
  is that the face `f(d₁)` is a digon, and then `d₂ = φ(d₁)` and `φ(d₂) = d₁`
  (`TripleData.IsDigon.facePerm_facePerm`).
* Transitivity and Euler's relation are used only to show that the swivel move of a triple
  diagram is again one. The other three results hold for pre-triple diagrams and are stated for
  them; an isomorphism of triple diagrams is an isomorphism of their data.
* Off `x ∪ y` the swivel rotation is `σ`, so the vertices of the swivel move are those of `X` with
  `x, y` replaced by the two new cycles. The faces are counted, as in FWZ, through the
  first-return maps of `φ` and `φ'` to `H ∖ {d̄₁, d̄₂}`, which coincide; the arcs are compared
  through the maps skipping the darts `d₁, d̄₁, d₂, d̄₂`, which coincide for `S` and `S'`.
* The isomorphism `X'' → X` of `TripleData.IsDigon.swivelMove_swivelMove` exchanges `d₁` with `d₂`
  and `d̄₁` with `d̄₂`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm

/-! ### Orbits of permutations -/

section Orbits

/-- If a finite set `C` containing `x` is closed under `f` and all its points lie on the orbit of
`x`, then `C` is that orbit. -/
private theorem sameCycle_iff_mem_of_mapsTo {α : Type*} [Finite α] {f : Perm α} {C : Finset α}
    {x : α} (hC : ∀ y ∈ C, f y ∈ C) (hreach : ∀ y ∈ C, f.SameCycle x y) (hx : x ∈ C) {y : α} :
    f.SameCycle x y ↔ y ∈ C := by
  refine ⟨fun h => ?_, hreach y⟩
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact hC _ ih

/-- Two permutations agreeing on a set closed under the first have the same orbits through its
points. -/
private theorem sameCycle_iff_of_eqOn {α : Type*} [Finite α] {f g : Perm α} {S : Set α}
    (hS : ∀ z ∈ S, f z ∈ S) (hfg : ∀ z ∈ S, f z = g z) {x : α} (hx : x ∈ S) {y : α} :
    f.SameCycle x y ↔ g.SameCycle x y := by
  have key : ∀ n : ℕ, (f ^ n) x = (g ^ n) x ∧ (f ^ n) x ∈ S := by
    intro n
    induction n with
    | zero => exact ⟨rfl, hx⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply]
      exact ⟨by rw [hfg _ h2, h1], hS _ h2⟩
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  · exact ⟨n, by rw [zpow_natCast, ← (key n).1, hn]⟩
  · exact ⟨n, by rw [zpow_natCast, (key n).1, hn]⟩

/-- An orbit of six points: if the orbit of `x` under `f` has six points, then `f⁶ x = x` and
`x, f x, …, f⁵ x` are distinct. -/
private theorem pow_six_apply_of_card_eq_six {α : Type*} [Fintype α] [DecidableEq α] {f : Perm α}
    {x : α} (h : ({y | f.SameCycle x y} : Finset α).card = 6) :
    (f ^ 6) x = x ∧ ∀ i j : ℕ, i < 6 → j < 6 → (f ^ i) x = (f ^ j) x → i = j := by
  have hx : f x ≠ x := by
    intro hfx
    have : ({y | f.SameCycle x y} : Finset α) = {x} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun h => (h.eq_of_left hfx).symm, fun h => h ▸ SameCycle.refl _ _⟩
    rw [this] at h
    simp at h
  have hsupp : (f.cycleOf x).support = ({y | f.SameCycle x y} : Finset α) := by
    ext y
    rw [mem_support_cycleOf_iff]
    simp [hx]
  have hc : (f.cycleOf x).support.card = 6 := hsupp ▸ h
  refine ⟨?_, fun i j hi hj hij => ?_⟩
  · have := f.pow_mod_card_support_cycleOf_self_apply 6 x
    rw [hc] at this
    simpa using this.symm
  · have hl : (f.toList x).length = 6 := by rw [Perm.length_toList, hc]
    exact ((nodup_toList f x).getElem_inj_iff (hi := by omega) (hj := by omega)).1
      (by rw [getElem_toList f x i (by omega), getElem_toList f x j (by omega), hij])

/-- A bijection intertwining two permutations intertwines their powers. -/
private theorem pow_apply_of_semiconj {α β : Type*} {f : Perm α} {g : Perm β} (θ : α ≃ β)
    (h : ∀ x, θ (f x) = g (θ x)) (n : ℕ) (x : α) : θ ((f ^ n) x) = (g ^ n) (θ x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, h, ih]

/-- A bijection intertwining two permutations maps the orbit of `x` onto the orbit of `θ x`. -/
private theorem map_sameCycle_of_semiconj {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {f : Perm α} {g : Perm β} (θ : α ≃ β)
    (h : ∀ x, θ (f x) = g (θ x)) (x : α) :
    ({y | f.SameCycle x y} : Finset α).map θ.toEmbedding =
      ({y | g.SameCycle (θ x) y} : Finset β) := by
  have h' : ∀ y, θ.symm (g y) = f (θ.symm y) := fun y => by
    apply θ.injective
    rw [h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext y
  simp only [mem_map_equiv, mem_filter, mem_univ, true_and]
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rw [zpow_natCast, ← pow_apply_of_semiconj θ h, hn, Equiv.apply_symm_apply]
  · intro hy
    obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rw [zpow_natCast, ← hn, pow_apply_of_semiconj θ.symm h', Equiv.symm_apply_apply]


/-- The product of two disjoint transpositions `(a b)(c d)` exchanges `a, b` and `c, d`. -/
private theorem swap_mul_swap_apply_of_ne {α : Type*} [DecidableEq α] {a b c d : α}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (swap a b * swap c d) a = b ∧ (swap a b * swap c d) b = a ∧
      (swap a b * swap c d) c = d ∧ (swap a b * swap c d) d = c := by
  simp only [Perm.mul_apply]
  exact ⟨by rw [swap_apply_of_ne_of_ne hac had, swap_apply_left],
    by rw [swap_apply_of_ne_of_ne hbc hbd, swap_apply_right],
    by rw [swap_apply_left, swap_apply_of_ne_of_ne had.symm hbd.symm],
    by rw [swap_apply_right, swap_apply_of_ne_of_ne hac.symm hbc.symm]⟩

/-- The product `(a b)(ι a ι b)` of two disjoint transpositions commutes with the involution
`ι`. -/
theorem swap_mul_swap_apply_comm_of_involutive {α : Type*} [DecidableEq α] {ι : α → α}
    (hι : Function.Involutive ι) {a b : α} (ha : a ≠ ι a) (hab : a ≠ ι b) (hba : b ≠ ι a)
    (hb : b ≠ ι b) (z : α) :
    (swap a b * swap (ι a) (ι b)) (ι z) = ι ((swap a b * swap (ι a) (ι b)) z) := by
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> grind [Function.Involutive]

/-- Two maps `α → Finset α`, each sending `z` to a set containing it and the points of `U` to
subsets of `U`, which agree off `U`, take as many values as they take on `U`. -/
private theorem card_image_univ_eq_of_eqOn_compl {α : Type*} [Fintype α] [DecidableEq α]
    {f g : α → Finset α} (U : Finset α) (hfg : ∀ z ∉ U, f z = g z) (hf : ∀ u ∈ U, f u ⊆ U)
    (hg : ∀ u ∈ U, g u ⊆ U) (hfs : ∀ z, z ∈ f z) (hgs : ∀ z, z ∈ g z)
    (hU : (U.image f).card = (U.image g).card) :
    (univ.image f).card = (univ.image g).card := by
  have split : ∀ k : α → Finset α, (∀ u ∈ U, k u ⊆ U) → (∀ z, z ∈ k z) →
      (univ.image k).card = (Uᶜ.image k).card + (U.image k).card := by
    intro k h1 h2
    rw [← card_union_of_disjoint, ← image_union, union_comm, union_compl]
    rw [disjoint_left]
    intro v hv hv'
    simp only [mem_image] at hv hv'
    obtain ⟨z, hz, rfl⟩ := hv
    obtain ⟨u, hu, he⟩ := hv'
    exact (mem_compl.1 hz) (h1 u hu (he ▸ h2 z))
  have hc : Uᶜ.image f = Uᶜ.image g := image_congr fun z hz => hfg z (by simpa using hz)
  rw [split f hf hfs, split g hg hgs, hc, hU]

/-- Six distinct points form a set of six elements. -/
private theorem card_eq_six_of_nodup {α : Type*} [DecidableEq α] {a b c d e f : α}
    (h : [a, b, c, d, e, f].Nodup) : ({a, b, c, d, e, f} : Finset α).card = 6 := by
  simpa using List.toFinset_card_of_nodup h

/-- The image of a set on which a map takes exactly the two values `A` and `B`. -/
private theorem image_eq_pair {α β : Type*} [DecidableEq β] {U : Finset α} {f : α → β} {A B : β}
    (h : ∀ u ∈ U, f u = A ∨ f u = B) {a b : α} (ha : a ∈ U) (hb : b ∈ U) (hfa : f a = A)
    (hfb : f b = B) : U.image f = {A, B} := by
  ext v
  simp only [mem_image, mem_insert, mem_singleton]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact h u hu
  · rintro (rfl | rfl)
    exacts [⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩]

/-- A first return after one step. -/
private theorem coe_firstReturn_mk_of_apply_mem {α : Type*} [Finite α] {π : Perm α} {Y : Set α}
    {z : α} (hz : z ∈ Y) (h : π z ∈ Y) : (firstReturn π Y ⟨z, hz⟩ : α) = π z :=
  coe_firstReturn_of_apply_mem h

/-- A first return after two steps. -/
private theorem coe_firstReturn_mk_of_apply_apply_mem {α : Type*} [Finite α] {π : Perm α}
    {Y : Set α} {z : α} (hz : z ∈ Y) (h₁ : π z ∉ Y) (h₂ : π (π z) ∈ Y) :
    (firstReturn π Y ⟨z, hz⟩ : α) = π (π z) := by
  have := coe_firstReturn_of_pow (π := π) (y := ⟨z, hz⟩) (m := 2) two_pos
    (by rwa [pow_two, Perm.mul_apply]) (fun j hj hj2 => by
      obtain rfl : j = 1 := by omega
      rwa [pow_one])
  rwa [pow_two, Perm.mul_apply] at this

private theorem exists_iterate_jump_of_exists_iterate {α : Type*} {S g : α → α} {L : Finset α}
    {E : α → Prop} (hL : ∀ l ∈ L, ¬E l)
    (hS : ∀ z, z ∉ L → ¬E z →
      (S z ∉ L ∧ g z = S z) ∨ (S z ∈ L ∧ S (S z) ∉ L ∧ g z = S (S z)))
    {a : α} (ha : a ∉ L) {w : α} :
    (∃ k, S^[k] a = w ∧ E w ∧ ∀ j < k, ¬E (S^[j] a)) →
      (∃ n, g^[n] a = w ∧ E w ∧ ∀ j < n, ¬E (g^[j] a)) := by
  rintro ⟨k, hk, hE, hj⟩
  induction k using Nat.strong_induction_on generalizing a with
  | _ k ih =>
  rcases k with _ | k
  · exact ⟨0, hk, hE, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  have hEa : ¬E a := hj 0 (Nat.succ_pos _)
  rcases hS a ha hEa with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨n, hn, -, hjn⟩ := ih k (Nat.lt_succ_self _) h1
      (by rwa [Function.iterate_succ_apply] at hk) (fun j hj' => by
        have := hj (j + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this)
    refine ⟨n + 1, by rwa [Function.iterate_succ_apply, h2], hE, fun j hj' => ?_⟩
    rcases j with _ | j
    · exact hEa
    · rw [Function.iterate_succ_apply, h2]; exact hjn j (by omega)
  · rcases k with _ | k
    · rw [Function.iterate_one] at hk
      exact absurd (hk ▸ hE) (hL _ h1)
    · obtain ⟨n, hn, -, hjn⟩ := ih k (by omega) h2
        (by rwa [Function.iterate_succ_apply, Function.iterate_succ_apply] at hk)
        (fun j hj' => by
          have := hj (j + 2) (by omega)
          rwa [Function.iterate_succ_apply, Function.iterate_succ_apply] at this)
      refine ⟨n + 1, by rwa [Function.iterate_succ_apply, h3], hE, fun j hj' => ?_⟩
      rcases j with _ | j
      · exact hEa
      · rw [Function.iterate_succ_apply, h3]; exact hjn j (by omega)

private theorem exists_iterate_of_exists_iterate_jump {α : Type*} {S g : α → α} {L : Finset α}
    {E : α → Prop} (hL : ∀ l ∈ L, ¬E l)
    (hS : ∀ z, z ∉ L → ¬E z →
      (S z ∉ L ∧ g z = S z) ∨ (S z ∈ L ∧ S (S z) ∉ L ∧ g z = S (S z)))
    {a : α} (ha : a ∉ L) {w : α} :
    (∃ n, g^[n] a = w ∧ E w ∧ ∀ j < n, ¬E (g^[j] a)) →
      (∃ k, S^[k] a = w ∧ E w ∧ ∀ j < k, ¬E (S^[j] a)) := by
  rintro ⟨n, hn, hE, hj⟩
  induction n generalizing a with
  | zero => exact ⟨0, hn, hE, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
  have hEa : ¬E a := hj 0 (Nat.succ_pos _)
  rcases hS a ha hEa with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨k, hk, -, hjk⟩ := ih h1 (by rwa [Function.iterate_succ_apply, h2] at hn)
      (fun j hj' => by
        have := hj (j + 1) (by omega)
        rwa [Function.iterate_succ_apply, h2] at this)
    refine ⟨k + 1, by rwa [Function.iterate_succ_apply], hE, fun j hj' => ?_⟩
    rcases j with _ | j
    · exact hEa
    · rw [Function.iterate_succ_apply]; exact hjk j (by omega)
  · obtain ⟨k, hk, -, hjk⟩ := ih h2 (by rwa [Function.iterate_succ_apply, h3] at hn)
      (fun j hj' => by
        have := hj (j + 1) (by omega)
        rwa [Function.iterate_succ_apply, h3] at this)
    refine ⟨k + 2, by rwa [Function.iterate_succ_apply, Function.iterate_succ_apply],
      hE, fun j hj' => ?_⟩
    rcases j with _ | _ | j
    · exact hEa
    · rw [Function.iterate_one]; exact hL _ h1
    · rw [Function.iterate_succ_apply, Function.iterate_succ_apply]; exact hjk j (by omega)

/-- Following `S` from `a ∉ L` until the first point satisfying `E`, while skipping the points of
`L` (none of which satisfies `E`, and which `S` never visits twice in a row), is the same as
following the map `g` that jumps over them. -/
private theorem exists_iterate_hit_iff {α : Type*} {S g : α → α} {L : Finset α} {E : α → Prop}
    (hL : ∀ l ∈ L, ¬E l)
    (hS : ∀ z, z ∉ L → ¬E z →
      (S z ∉ L ∧ g z = S z) ∨ (S z ∈ L ∧ S (S z) ∉ L ∧ g z = S (S z)))
    {a : α} (ha : a ∉ L) {w : α} :
    (∃ k, S^[k] a = w ∧ E w ∧ ∀ j < k, ¬E (S^[j] a)) ↔
      (∃ n, g^[n] a = w ∧ E w ∧ ∀ j < n, ¬E (g^[j] a)) :=
  ⟨exists_iterate_jump_of_exists_iterate hL hS ha, exists_iterate_of_exists_iterate_jump hL hS ha⟩

/-- The cycle of `f` through a point of a `6`-cycle `c₀ → c₁ → ⋯ → c₅ → c₀` is that cycle. -/
private theorem sameCycle_iff_mem_of_six {α : Type*} [Finite α] [DecidableEq α] {f : Perm α}
    {c₀ c₁ c₂ c₃ c₄ c₅ : α} (h₀ : f c₀ = c₁) (h₁ : f c₁ = c₂) (h₂ : f c₂ = c₃)
    (h₃ : f c₃ = c₄) (h₄ : f c₄ = c₅) (h₅ : f c₅ = c₀) {x : α}
    (hx : x ∈ ({c₀, c₁, c₂, c₃, c₄, c₅} : Finset α)) {w : α} :
    f.SameCycle x w ↔ w ∈ ({c₀, c₁, c₂, c₃, c₄, c₅} : Finset α) := by
  have step : ∀ {x y z : α}, f.SameCycle x y → f y = z → f.SameCycle x z :=
    fun h e => e ▸ sameCycle_apply_right.2 h
  have e₁ := step (SameCycle.refl _ c₀) h₀
  have e₂ := step e₁ h₁
  have e₃ := step e₂ h₂
  have e₄ := step e₃ h₃
  have e₅ := step e₄ h₄
  have hc : ∀ y ∈ ({c₀, c₁, c₂, c₃, c₄, c₅} : Finset α), f.SameCycle c₀ y := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with h | h | h | h | h | h <;> rw [h]
    all_goals first | exact SameCycle.refl _ _ | assumption
  refine sameCycle_iff_mem_of_mapsTo (fun y hy => ?_)
    (fun y hy => (hc x hx).symm.trans (hc y hy)) hx
  simp only [mem_insert, mem_singleton] at hy ⊢
  rcases hy with h | h | h | h | h | h <;> rw [h] <;> simp [h₀, h₁, h₂, h₃, h₄, h₅]

/-- A swap of two points with the same value under `p` preserves `p`. -/
theorem apply_swap_eq_of_eq {α β : Type*} [DecidableEq α] (p : α → β) {a b : α}
    (h : p a = p b) (z : α) : p (swap a b z) = p z := by
  rw [swap_apply_def]
  split_ifs <;> simp_all

/-- A product of two swaps, each of two points with the same value under `p`, preserves `p`. -/
theorem apply_swap_mul_swap_eq_of_eq {α β : Type*} [DecidableEq α] (p : α → β) {a b c d : α}
    (hab : p a = p b) (hcd : p c = p d) (z : α) : p ((swap a b * swap c d) z) = p z := by
  rw [Perm.mul_apply, apply_swap_eq_of_eq p hab, apply_swap_eq_of_eq p hcd]

end Orbits

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {d₁ : H}

/-! ### Digons -/

/-- At a digon `f(d₁)`, the face permutation exchanges `d₁` and `d₂ = φ(d₁)`. -/
theorem IsDigon.facePerm_facePerm (hd : X.IsDigon (X.faceOf d₁)) :
    X.facePerm (X.facePerm d₁) = d₁ := by
  obtain ⟨-, d, hf, hv⟩ := hd
  have hd₁ : d₁ ∈ ({d, X.facePerm d} : Finset H) := hf ▸ X.self_mem_faceOf d₁
  have hne : X.facePerm d ≠ d := fun h => hv (by rw [h])
  have hφd : X.facePerm (X.facePerm d) = d := by
    have h1 : X.facePerm d ∈ X.faceOf d₁ := by simp [hf]
    have h2 : X.facePerm (X.facePerm d) ∈ X.faceOf d₁ := by
      rw [← X.faceOf_eq_of_mem h1]; exact X.facePerm_mem_faceOf _
    rw [hf] at h2
    rcases mem_insert.1 h2 with h | h
    · exact h
    · exact absurd (X.facePerm.injective (mem_singleton.1 h)) hne
  rcases mem_insert.1 hd₁ with h | h
  · rw [h, hφd]
  · rw [mem_singleton.1 h, hφd]

/-- At a digon `f(d₁)`, the darts `d₁` and `d₂ = φ(d₁)` lie at distinct vertices. -/
theorem IsDigon.vertexOf_ne (hd : X.IsDigon (X.faceOf d₁)) :
    X.vertexOf d₁ ≠ X.vertexOf (X.facePerm d₁) := by
  have hφφ := hd.facePerm_facePerm
  obtain ⟨-, d, hf, hv⟩ := hd
  have hd₁ : d₁ ∈ ({d, X.facePerm d} : Finset H) := hf ▸ X.self_mem_faceOf d₁
  rcases mem_insert.1 hd₁ with h | h
  · rwa [h]
  · have h' : d₁ = X.facePerm d := mem_singleton.1 h
    have hd' : X.facePerm d₁ = d := by
      rw [h'] at hφφ ⊢
      exact X.facePerm.injective hφφ
    rw [hd', h']
    exact Ne.symm hv

/-- The darts `d₁` and `d₂ = φ(d₁)` of a digon `f(d₁)` lie outside `B`. -/
theorem IsDigon.notMem_bdry (hd : X.IsDigon (X.faceOf d₁)) :
    d₁ ∉ X.bdry ∧ X.facePerm d₁ ∉ X.bdry := by
  have hdisj := (X.mem_internalFaces.1 hd.1).2
  exact ⟨disjoint_left.1 hdisj (X.self_mem_faceOf d₁),
    disjoint_left.1 hdisj (X.facePerm_mem_faceOf d₁)⟩

/-- A dart `e` off the boundary with `σ(ē') = e` for a dart `e'` off the boundary lies at an
internal vertex. -/
private theorem not_isBoundaryVertex_of_rot_inv_eq (hX : X.IsPreTripleDiagram) {e e' : H}
    (h : X.rot (X.inv e') = e) (he : e ∉ X.bdry) (he' : e' ∉ X.bdry) :
    ¬X.IsBoundaryVertex (X.vertexOf e) := by
  intro hbv
  have hinvB : X.inv e' ∉ X.bdry := fun hb =>
    he' (by simpa [hX.inv_involutive e'] using hX.inv_mem_bdry _ hb)
  have hmem : X.inv e' ∈ X.vertexOf e := by
    rw [← h, X.vertexOf_rot]
    exact X.self_mem_vertexOf _
  have heq := DiskMap.eq_of_notMem_bdry hX.boundaryVertex_card hbv hmem
    (X.self_mem_vertexOf e) hinvB he
  rw [heq] at h
  exact DiskMap.rot_ne_of_isBoundaryVertex hX.boundaryVertex_card hbv h

/-- **The darts at a digon.** Let `f(d₁)` be a digon of a pre-triple diagram, `d₂ = φ(d₁)`. Then
`x = v(d₁)` and `y = v(d₂)` are distinct triple points whose rotations are
`(d̄₂, d₁, a₁, a₂, a₃, a₄)` and `(d̄₁, d₂, b₁, b₂, b₃, b₄)`, for twelve distinct darts. -/
theorem IsDigon.exists_darts (hX : X.IsPreTripleDiagram) (hd : X.IsDigon (X.faceOf d₁)) :
    ∃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : H,
      X.rot d₁ = a₁ ∧ X.rot a₁ = a₂ ∧ X.rot a₂ = a₃ ∧ X.rot a₃ = a₄ ∧
      X.rot a₄ = X.inv (X.facePerm d₁) ∧
      X.rot (X.facePerm d₁) = b₁ ∧ X.rot b₁ = b₂ ∧ X.rot b₂ = b₃ ∧ X.rot b₃ = b₄ ∧
      X.rot b₄ = X.inv d₁ ∧
      [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄,
        X.inv d₁].Nodup ∧
      X.vertexOf d₁ = {d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁)} ∧
      X.vertexOf (X.facePerm d₁) = {X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁} ∧
      ¬X.IsBoundaryVertex (X.vertexOf d₁) ∧ ¬X.IsBoundaryVertex (X.vertexOf (X.facePerm d₁)) := by
  have hφφ : X.rot (X.inv (X.facePerm d₁)) = d₁ := hd.facePerm_facePerm
  have hφ : X.rot (X.inv d₁) = X.facePerm d₁ := rfl
  have hv := hd.vertexOf_ne
  obtain ⟨hd₁B, hd₂B⟩ := hd.notMem_bdry
  generalize X.facePerm d₁ = d₂ at hφφ hφ hv hd₂B ⊢
  have hint₁ := not_isBoundaryVertex_of_rot_inv_eq hX hφφ hd₁B hd₂B
  have hint₂ := not_isBoundaryVertex_of_rot_inv_eq hX hφ hd₂B hd₁B
  have hc₁ : (X.vertexOf d₁).card = 6 :=
    hX.internalVertex_card _ (X.vertexOf_mem_internalVertices.2 hint₁)
  have hc₂ : (X.vertexOf d₂).card = 6 :=
    hX.internalVertex_card _ (X.vertexOf_mem_internalVertices.2 hint₂)
  obtain ⟨h6₁, hinj₁⟩ := pow_six_apply_of_card_eq_six (f := X.rot) hc₁
  obtain ⟨h6₂, hinj₂⟩ := pow_six_apply_of_card_eq_six (f := X.rot) hc₂
  have hs : ∀ (e : H) (k : ℕ), X.rot ((X.rot ^ k) e) = (X.rot ^ (k + 1)) e := fun e k => by
    rw [pow_succ', Perm.mul_apply]
  have h5₁ : (X.rot ^ 5) d₁ = X.inv d₂ := X.rot.injective (by rwa [hφφ, hs])
  have h5₂ : (X.rot ^ 5) d₂ = X.inv d₁ := X.rot.injective (by rwa [hφ, hs])
  have hreach : ∀ (e : H) (k : ℕ), X.rot.SameCycle e ((X.rot ^ k) e) := fun e k =>
    sameCycle_pow_right.2 (SameCycle.refl _ _)
  have hcross : ∀ i j : ℕ, (X.rot ^ i) d₁ ≠ (X.rot ^ j) d₂ := by
    intro i j h
    exact hv (X.vertexOf_eq_vertexOf_iff.2 ((hreach d₁ i).trans (h ▸ (hreach d₂ j).symm)))
  have hV : ∀ e : H, (X.rot ^ 6) e = e →
      X.vertexOf e = {e, (X.rot ^ 1) e, (X.rot ^ 2) e, (X.rot ^ 3) e, (X.rot ^ 4) e,
        (X.rot ^ 5) e} := fun e h6 => by
    ext z
    rw [RotationSystem.mem_vertexOf]
    exact sameCycle_iff_mem_of_six (by rw [pow_one]) (hs e 1) (hs e 2) (hs e 3) (hs e 4)
      ((hs e 5).trans h6) (by simp)
  refine ⟨(X.rot ^ 1) d₁, (X.rot ^ 2) d₁, (X.rot ^ 3) d₁, (X.rot ^ 4) d₁,
    (X.rot ^ 1) d₂, (X.rot ^ 2) d₂, (X.rot ^ 3) d₂, (X.rot ^ 4) d₂,
    pow_one X.rot ▸ rfl, hs d₁ 1, hs d₁ 2, hs d₁ 3, (hs d₁ 4).trans h5₁,
    pow_one X.rot ▸ rfl, hs d₂ 1, hs d₂ 2, hs d₂ 3, (hs d₂ 4).trans h5₂, ?_,
    h5₁ ▸ hV d₁ h6₁, h5₂ ▸ hV d₂ h6₂, hint₁, hint₂⟩
  have hl : ((List.range 6).map (fun k => (X.rot ^ k) d₁) ++
      (List.range 6).map (fun k => (X.rot ^ k) d₂)).Nodup := by
    rw [List.nodup_append]
    refine ⟨List.nodup_range.map_on fun i hi j hj h =>
        hinj₁ i j (List.mem_range.1 hi) (List.mem_range.1 hj) h,
      List.nodup_range.map_on fun i hi j hj h =>
        hinj₂ i j (List.mem_range.1 hi) (List.mem_range.1 hj) h, ?_⟩
    simp only [List.mem_map, List.mem_range]
    rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩
    exact hcross i j
  rwa [← h5₁, ← h5₂]

/-! ### The darts away from the digon -/

/-- Off `x ∪ y`, the swivel rotation at `d₁` is `σ`. -/
theorem swivelRot_apply_of_notMem {z : H}
    (hz : z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) : X.swivelRot d₁ z = X.rot z := by
  simp only [mem_union, RotationSystem.mem_vertexOf, not_or] at hz
  have hp : ∀ (e : H) (k : ℕ), X.rot.SameCycle e ((X.rot ^ k) e) := fun e k =>
    sameCycle_pow_right.2 (SameCycle.refl _ _)
  refine swivelRot_apply_of_ne ?_ ?_ ?_ ?_ ?_ ?_ <;> rintro rfl
  · exact hz.1 (SameCycle.refl _ _)
  · exact hz.1 (hp _ _)
  · exact hz.1 (hp _ _)
  · exact hz.2 (SameCycle.refl _ _)
  · exact hz.2 (hp _ _)
  · exact hz.2 (hp _ _)

/-- The rotation preserves `x ∪ y` and its complement. -/
theorem rot_mem_union_vertexOf_iff {z : H} :
    X.rot z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) ↔
      z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := by
  simp only [mem_union, RotationSystem.mem_vertexOf, sameCycle_apply_right]

/-- Off `x ∪ y`, the vertices of the swivel move are those of `X`. -/
theorem vertexOf_swivelMove_of_notMem {z : H}
    (hz : z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) :
    (X.swivelMove d₁).vertexOf z = X.vertexOf z := by
  ext w
  simp only [RotationSystem.mem_vertexOf]
  refine (sameCycle_iff_of_eqOn (S := {z | z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)})
    (fun y hy => ?_) (fun y hy => ?_) hz).symm
  · exact fun h => hy (rot_mem_union_vertexOf_iff.1 h)
  · exact (swivelRot_apply_of_notMem hy).symm

/-- The six darts `d₁, a₂, a₄, d₂, b₂, b₄` form a sublist of the twelve darts of a digon. -/
private theorem sublist_six_twelve {α : Type*} {d₁ a₁ a₂ a₃ a₄ e₂ d₂ b₁ b₂ b₃ b₄ e₁ : α} :
    [d₁, a₂, a₄, d₂, b₂, b₄].Sublist [d₁, a₁, a₂, a₃, a₄, e₂, d₂, b₁, b₂, b₃, b₄, e₁] := by
  repeat first | exact List.nil_sublist _ | apply List.Sublist.cons_cons | apply List.Sublist.cons

/-- A vertex through a dart outside `x ∪ y` avoids `x ∪ y`. -/
theorem notMem_of_mem_vertexOf {z w : H} (hz : z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (hw : w ∈ X.vertexOf z) : w ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := by
  rw [RotationSystem.mem_vertexOf] at hw
  simp only [mem_union, RotationSystem.mem_vertexOf, not_or] at hz ⊢
  exact ⟨fun h => hz.1 (h.trans hw.symm), fun h => hz.2 (h.trans hw.symm)⟩

omit [Fintype H] in
/-- The swivel rotation at the twelve darts of a digon, given their names. -/
theorem swivelRot_of_darts {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : H} (h1 : X.rot d₁ = a₁)
    (h2 : X.rot a₁ = a₂) (h3 : X.rot a₂ = a₃) (h4 : X.rot a₃ = a₄)
    (h5 : X.rot a₄ = X.inv (X.facePerm d₁))
    (g1 : X.rot (X.facePerm d₁) = b₁) (g2 : X.rot b₁ = b₂) (g3 : X.rot b₂ = b₃)
    (g4 : X.rot b₃ = b₄) (g5 : X.rot b₄ = X.inv d₁)
    (hnd : [d₁, a₂, a₄, X.facePerm d₁, b₂, b₄].Nodup) :
    X.swivelRot d₁ d₁ = a₃ ∧ X.swivelRot d₁ a₂ = X.inv d₁ ∧ X.swivelRot d₁ b₄ = a₁ ∧
      X.swivelRot d₁ a₄ = b₁ ∧ X.swivelRot d₁ (X.facePerm d₁) = b₃ ∧
      X.swivelRot d₁ b₂ = X.inv (X.facePerm d₁) ∧
      ∀ z, z ≠ d₁ → z ≠ a₂ → z ≠ a₄ → z ≠ X.facePerm d₁ → z ≠ b₂ → z ≠ b₄ →
        X.swivelRot d₁ z = X.rot z := by
  have p2 : (X.rot ^ 2) d₁ = a₂ := by simp only [pow_succ', Perm.mul_apply, pow_zero,
    Perm.one_apply, h1, h2]
  have p4 : (X.rot ^ 4) d₁ = a₄ := by simp only [pow_succ', Perm.mul_apply, pow_zero,
    Perm.one_apply, h1, h2, h3, h4]
  have q2 : (X.rot ^ 2) (X.facePerm d₁) = b₂ := by simp only [pow_succ', Perm.mul_apply,
    pow_zero, Perm.one_apply, g1, g2]
  have q4 : (X.rot ^ 4) (X.facePerm d₁) = b₄ := by simp only [pow_succ', Perm.mul_apply,
    pow_zero, Perm.one_apply, g1, g2, g3, g4]
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := X.swivelRot_apply_six (d₁ := d₁) (by rwa [p2, p4, q2, q4])
  rw [p2, h3] at s1
  rw [p2, q4, g5] at s2
  rw [q4, h1] at s3
  rw [p4, g1] at s4
  rw [q2, g3] at s5
  rw [q2, p4, h5] at s6
  exact ⟨s1, s2, s3, s4, s5, s6, fun z n1 n2 n3 n4 n5 n6 =>
    swivelRot_apply_of_ne n1 (p2 ▸ n2) (p4 ▸ n3) n4 (q2 ▸ n5) (q4 ▸ n6)⟩

/-- **The swivel move at a digon, dart by dart.** Let `f(d₁)` be a digon of a pre-triple diagram,
`d₂ = φ(d₁)`, with rotations `(d̄₂, d₁, a₁, a₂, a₃, a₄)` at `x = v(d₁)` and
`(d̄₁, d₂, b₁, b₂, b₃, b₄)` at `y = v(d₂)`. Then the swivel rotation has the cycles
`(d̄₂, d₁, a₃, a₄, b₁, b₂)` and `(d̄₁, d₂, b₃, b₄, a₁, a₂)`, which are the vertices of the swivel
move at `d₁` and `d₂`. -/
theorem IsDigon.exists_swivel (hX : X.IsPreTripleDiagram) (hd : X.IsDigon (X.faceOf d₁)) :
    ∃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : H,
      X.rot d₁ = a₁ ∧ X.rot a₁ = a₂ ∧ X.rot a₂ = a₃ ∧ X.rot a₃ = a₄ ∧
      X.rot a₄ = X.inv (X.facePerm d₁) ∧
      X.rot (X.facePerm d₁) = b₁ ∧ X.rot b₁ = b₂ ∧ X.rot b₂ = b₃ ∧ X.rot b₃ = b₄ ∧
      X.rot b₄ = X.inv d₁ ∧
      [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄,
        X.inv d₁].Nodup ∧
      X.vertexOf d₁ = {d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁)} ∧
      X.vertexOf (X.facePerm d₁) = {X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁} ∧
      ¬X.IsBoundaryVertex (X.vertexOf d₁) ∧ ¬X.IsBoundaryVertex (X.vertexOf (X.facePerm d₁)) ∧
      X.swivelRot d₁ d₁ = a₃ ∧ X.swivelRot d₁ a₃ = a₄ ∧ X.swivelRot d₁ a₄ = b₁ ∧
      X.swivelRot d₁ b₁ = b₂ ∧ X.swivelRot d₁ b₂ = X.inv (X.facePerm d₁) ∧
      X.swivelRot d₁ (X.inv (X.facePerm d₁)) = d₁ ∧
      X.swivelRot d₁ (X.inv d₁) = X.facePerm d₁ ∧ X.swivelRot d₁ (X.facePerm d₁) = b₃ ∧
      X.swivelRot d₁ b₃ = b₄ ∧ X.swivelRot d₁ b₄ = a₁ ∧ X.swivelRot d₁ a₁ = a₂ ∧
      X.swivelRot d₁ a₂ = X.inv d₁ ∧
      (X.swivelMove d₁).vertexOf d₁ = {X.inv (X.facePerm d₁), d₁, a₃, a₄, b₁, b₂} ∧
      (X.swivelMove d₁).vertexOf (X.facePerm d₁) =
        {X.inv d₁, X.facePerm d₁, b₃, b₄, a₁, a₂} := by
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂⟩ := hd.exists_darts hX
  have hφφ : X.rot (X.inv (X.facePerm d₁)) = d₁ := hd.facePerm_facePerm
  obtain ⟨s1, s2, s3, s4, s5, s6, off⟩ := swivelRot_of_darts h1 h2 h3 h4 h5 g1 g2 g3 g4 g5
    (hnd.sublist sublist_six_twelve)
  have hφr : X.rot (X.inv d₁) = X.facePerm d₁ := rfl
  generalize X.facePerm d₁ = d₂ at *
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hnd'
  have hφ : X.swivelRot d₁ (X.inv d₁) = d₂ := by
    rw [off _ ?_ ?_ ?_ ?_ ?_ ?_, hφr] <;> intro h <;> simp [h] at hnd'
  have t3 : X.swivelRot d₁ a₃ = a₄ := by
    rw [off _ ?_ ?_ ?_ ?_ ?_ ?_, h4] <;> intro h <;> simp [h] at hnd'
  have tb1 : X.swivelRot d₁ b₁ = b₂ := by
    rw [off _ ?_ ?_ ?_ ?_ ?_ ?_, g2] <;> intro h <;> simp [h] at hnd'
  have td2 : X.swivelRot d₁ (X.inv d₂) = d₁ := by
    rw [off _ ?_ ?_ ?_ ?_ ?_ ?_, hφφ] <;> intro h <;> simp [h] at hnd'
  have tb3 : X.swivelRot d₁ b₃ = b₄ := by
    rw [off _ ?_ ?_ ?_ ?_ ?_ ?_, g4] <;> intro h <;> simp [h] at hnd'
  have ta1 : X.swivelRot d₁ a₁ = a₂ := by
    rw [off _ ?_ ?_ ?_ ?_ ?_ ?_, h2] <;> intro h <;> simp [h] at hnd'
  refine ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂, s1, t3, s4, tb1, s6, td2, hφ, s5, tb3, s3, ta1, s2, ?_, ?_⟩
  · ext w
    rw [RotationSystem.mem_vertexOf]
    exact sameCycle_iff_mem_of_six (f := X.swivelRot d₁) td2 s1 t3 s4 tb1 s6 (by simp)
  · ext w
    rw [RotationSystem.mem_vertexOf]
    exact sameCycle_iff_mem_of_six (f := X.swivelRot d₁) hφ s5 tb3 s3 ta1 s2 (by simp)

/-! ### The vertices of a swivel move -/

/-- The triple points `x` and `y` of a digon of a pre-triple diagram are internal vertices. -/
theorem IsDigon.not_isBoundaryVertex (hX : X.IsPreTripleDiagram) (hd : X.IsDigon (X.faceOf d₁)) :
    ¬X.IsBoundaryVertex (X.vertexOf d₁) ∧ ¬X.IsBoundaryVertex (X.vertexOf (X.facePerm d₁)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hi₁, hi₂⟩ :=
    hd.exists_darts hX
  exact ⟨hi₁, hi₂⟩

/-- No dart of `B` lies in `x ∪ y`. -/
theorem IsDigon.notMem_of_mem_bdry (hX : X.IsPreTripleDiagram) (hd : X.IsDigon (X.faceOf d₁))
    {z : H} (hz : z ∈ X.bdry) : z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := by
  obtain ⟨hi₁, hi₂⟩ := hd.not_isBoundaryVertex hX
  rw [mem_union, not_or]
  exact ⟨fun h => hi₁ ⟨z, h, hz⟩, fun h => hi₂ ⟨z, h, hz⟩⟩

/-- No dart at a boundary vertex lies in `x ∪ y`. -/
theorem IsDigon.notMem_of_isBoundaryVertex (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) {z : H} (hz : X.IsBoundaryVertex (X.vertexOf z)) :
    z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := by
  obtain ⟨hi₁, hi₂⟩ := hd.not_isBoundaryVertex hX
  rw [mem_union, not_or]
  exact ⟨fun h => hi₁ (X.vertexOf_eq_of_mem h ▸ hz), fun h => hi₂ (X.vertexOf_eq_of_mem h ▸ hz)⟩

/-- In the swivel move, the vertex of a dart of `x ∪ y` is the new vertex at `d₁` or at `d₂`. -/
theorem IsDigon.vertexOf_swivelMove_eq_or (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) {z : H} (hz : z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) :
    (X.swivelMove d₁).vertexOf z = (X.swivelMove d₁).vertexOf d₁ ∨
      (X.swivelMove d₁).vertexOf z = (X.swivelMove d₁).vertexOf (X.facePerm d₁) := by
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, -, -, hV₁, hV₂, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, hW₁, hW₂⟩ := hd.exists_swivel hX
  generalize X.facePerm d₁ = d₂ at *
  rw [hV₁, hV₂] at hz
  simp only [mem_union, mem_insert, mem_singleton] at hz
  have hx' : ∀ w ∈ ({X.inv d₂, d₁, a₃, a₄, b₁, b₂} : Finset H),
      (X.swivelMove d₁).vertexOf w = (X.swivelMove d₁).vertexOf d₁ := fun w hw => by
    rw [← hW₁] at hw; exact (X.swivelMove d₁).vertexOf_eq_of_mem hw
  have hy' : ∀ w ∈ ({X.inv d₁, d₂, b₃, b₄, a₁, a₂} : Finset H),
      (X.swivelMove d₁).vertexOf w = (X.swivelMove d₁).vertexOf d₂ := fun w hw => by
    rw [← hW₂] at hw; exact (X.swivelMove d₁).vertexOf_eq_of_mem hw
  rcases hz with (h | h | h | h | h | h) | (h | h | h | h | h | h) <;> rw [h]
  exacts [Or.inl (hx' _ (by simp)), Or.inr (hy' _ (by simp)), Or.inr (hy' _ (by simp)),
    Or.inl (hx' _ (by simp)), Or.inl (hx' _ (by simp)), Or.inl (hx' _ (by simp)),
    Or.inr (hy' _ (by simp)), Or.inl (hx' _ (by simp)), Or.inl (hx' _ (by simp)),
    Or.inr (hy' _ (by simp)), Or.inr (hy' _ (by simp)), Or.inr (hy' _ (by simp))]

/-- In the swivel move, the vertex of a dart of `x ∪ y` is one of the two new triple points: it
lies in `x ∪ y`, contains no dart of `B`, and has six darts. -/
theorem IsDigon.vertexOf_swivelMove_of_mem (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) {z : H} (hz : z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) :
    (X.swivelMove d₁).vertexOf z ⊆ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) ∧
      ¬(X.swivelMove d₁).IsBoundaryVertex ((X.swivelMove d₁).vertexOf z) ∧
      ((X.swivelMove d₁).vertexOf z).card = 6 := by
  have hnB := fun w (hw : w ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) (hwB : w ∈ X.bdry) =>
    hd.notMem_of_mem_bdry hX hwB hw
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, -, hnd, hV₁, hV₂, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, hW₁, hW₂⟩ := hd.exists_swivel hX
  have key := hd.vertexOf_swivelMove_eq_or hX hz
  generalize X.facePerm d₁ = d₂ at *
  rw [hV₁, hV₂] at hnB ⊢
  rw [hW₁, hW₂] at key
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hnd'
  have hsub : ∀ w, (w = X.inv d₂ ∨ w = d₁ ∨ w = a₃ ∨ w = a₄ ∨ w = b₁ ∨ w = b₂) ∨
      (w = X.inv d₁ ∨ w = d₂ ∨ w = b₃ ∨ w = b₄ ∨ w = a₁ ∨ w = a₂) →
      w ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H) ∪ {d₂, b₁, b₂, b₃, b₄, X.inv d₁} := by
    intro w hw
    simp only [mem_union, mem_insert, mem_singleton]
    rcases hw with (h | h | h | h | h | h) | (h | h | h | h | h | h) <;> simp [h]
  rcases key with h | h <;> rw [h] <;> refine ⟨fun w hw => hsub w ?_, ?_, ?_⟩
  · simp only [mem_insert, mem_singleton] at hw; exact Or.inl hw
  · rintro ⟨w, hw, hwB⟩
    simp only [mem_insert, mem_singleton] at hw
    exact hnB w (hsub w (Or.inl hw)) hwB
  · apply card_eq_six_of_nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    and_intros <;> exact fun h => by simp [h] at hnd'
  · simp only [mem_insert, mem_singleton] at hw; exact Or.inr hw
  · rintro ⟨w, hw, hwB⟩
    simp only [mem_insert, mem_singleton] at hw
    exact hnB w (hsub w (Or.inr hw)) hwB
  · apply card_eq_six_of_nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    and_intros <;> exact fun h => by simp [h] at hnd'

/-- A vertex of the swivel move is a boundary vertex exactly when the vertex of `X` through the
same dart is. -/
theorem IsDigon.isBoundaryVertex_swivelMove_iff (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) (z : H) :
    (X.swivelMove d₁).IsBoundaryVertex ((X.swivelMove d₁).vertexOf z) ↔
      X.IsBoundaryVertex (X.vertexOf z) := by
  by_cases hz : z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)
  · exact iff_of_false (hd.vertexOf_swivelMove_of_mem hX hz).2.1
      fun h => hd.notMem_of_isBoundaryVertex hX h hz
  · rw [vertexOf_swivelMove_of_notMem hz]
    rfl

/-- The swivel move has the boundary vertices of `X`. -/
theorem IsDigon.boundaryVertices_swivelMove (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) :
    (X.swivelMove d₁).boundaryVertices = X.boundaryVertices := by
  ext v
  simp only [DiskMap.mem_boundaryVertices, RotationSystem.mem_vertices]
  constructor
  · rintro ⟨⟨z, rfl⟩, hb⟩
    have hb' := (hd.isBoundaryVertex_swivelMove_iff hX z).1 hb
    rw [vertexOf_swivelMove_of_notMem (hd.notMem_of_isBoundaryVertex hX hb')]
    exact ⟨⟨z, rfl⟩, hb'⟩
  · rintro ⟨⟨z, rfl⟩, hb⟩
    have hz := hd.notMem_of_isBoundaryVertex hX hb
    refine ⟨⟨z, vertexOf_swivelMove_of_notMem hz⟩, ?_⟩
    rw [← vertexOf_swivelMove_of_notMem hz]
    exact (hd.isBoundaryVertex_swivelMove_iff hX z).2 hb

/-- The swivel move has the endpoints of `X`. -/
theorem IsDigon.endpoint_swivelMove (hX : X.IsPreTripleDiagram) (hd : X.IsDigon (X.faceOf d₁))
    (r : Fin (2 * b)) : (X.swivelMove d₁).endpoint r = X.endpoint r :=
  vertexOf_swivelMove_of_notMem (hd.notMem_of_isBoundaryVertex hX
    (X.vertexOf_mem_boundaryVertices.1 (hX.endpoint_mem r)))

/-- The swivel move has the exterior of `X`. -/
theorem IsDigon.exterior_swivelMove (hX : X.IsPreTripleDiagram) (hd : X.IsDigon (X.faceOf d₁)) :
    (X.swivelMove d₁).exterior = X.exterior := by
  ext z
  simp only [DiskMap.mem_exterior, swivelMove_bdry, swivelMove_rot]
  refine and_congr_right fun hz => ?_
  rw [swivelRot_apply_of_notMem (hd.notMem_of_mem_bdry hX hz)]

/-- The face permutation of the swivel move agrees with that of `X` on `B`. -/
theorem IsDigon.facePerm_swivelMove_of_mem_bdry (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) {z : H} (hz : z ∈ X.bdry) :
    (X.swivelMove d₁).facePerm z = X.facePerm z := by
  simp only [RotationSystem.facePerm_apply]
  exact swivelRot_apply_of_notMem (hd.notMem_of_mem_bdry hX (hX.inv_mem_bdry z hz))

/-- The orientation alternates around the triple points of the swivel move. -/
theorem IsDigon.isOut_swivelRot (hX : X.IsPreTripleDiagram) (hd : X.IsDigon (X.faceOf d₁))
    (z : H) (hz : ¬X.IsBoundaryVertex (X.vertexOf z)) :
    X.isOut (X.swivelRot d₁ z) ≠ X.isOut z := by
  by_cases hU : z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)
  · obtain ⟨hi₁, hi₂⟩ := hd.not_isBoundaryVertex hX
    have hr : ∀ w ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁),
        X.isOut (X.rot w) = !X.isOut w := by
      intro w hw
      refine Bool.eq_not_iff.2 (hX.isOut_rot w ?_)
      rcases mem_union.1 hw with h | h
      · rwa [X.vertexOf_eq_of_mem h]
      · rwa [X.vertexOf_eq_of_mem h]
    have oe₁ : X.isOut (X.inv d₁) = !X.isOut d₁ :=
      Bool.eq_not_iff.2 (hX.isOut_inv d₁ hd.notMem_bdry.1)
    have hφr : X.rot (X.inv d₁) = X.facePerm d₁ := rfl
    obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, -, hV₁, hV₂,
      -, -, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -, -⟩ := hd.exists_swivel hX
    generalize X.facePerm d₁ = d₂ at *
    rw [hV₁, hV₂] at hU hr
    have oa₁ : X.isOut a₁ = !X.isOut d₁ := by rw [← h1, hr d₁ (by simp)]
    have oa₂ : X.isOut a₂ = X.isOut d₁ := by rw [← h2, hr a₁ (by simp), oa₁, Bool.not_not]
    have oa₃ : X.isOut a₃ = !X.isOut d₁ := by rw [← h3, hr a₂ (by simp), oa₂]
    have oa₄ : X.isOut a₄ = X.isOut d₁ := by rw [← h4, hr a₃ (by simp), oa₃, Bool.not_not]
    have oe₂ : X.isOut (X.inv d₂) = !X.isOut d₁ := by rw [← h5, hr a₄ (by simp), oa₄]
    have od₂ : X.isOut d₂ = X.isOut d₁ := by
      rw [← hφr, hr (X.inv d₁) (by simp), oe₁, Bool.not_not]
    have ob₁ : X.isOut b₁ = !X.isOut d₁ := by rw [← g1, hr d₂ (by simp), od₂]
    have ob₂ : X.isOut b₂ = X.isOut d₁ := by rw [← g2, hr b₁ (by simp), ob₁, Bool.not_not]
    have ob₃ : X.isOut b₃ = !X.isOut d₁ := by rw [← g3, hr b₂ (by simp), ob₂]
    have ob₄ : X.isOut b₄ = X.isOut d₁ := by rw [← g4, hr b₃ (by simp), ob₃, Bool.not_not]
    simp only [mem_union, mem_insert, mem_singleton] at hU
    rcases hU with (h | h | h | h | h | h) | (h | h | h | h | h | h) <;> rw [h] <;>
      simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, oa₁, oa₂, oa₃, oa₄, oe₁,
        oe₂, od₂, ob₁, ob₂, ob₃, ob₄] <;> cases X.isOut d₁ <;> simp
  · rw [swivelRot_apply_of_notMem hU]
    exact hX.isOut_rot z hz

/-- **A swivel move of a pre-triple diagram is a pre-triple diagram.** -/
theorem IsDigon.isPreTripleDiagram_swivelMove (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) : (X.swivelMove d₁).IsPreTripleDiagram where
  one_le := hX.one_le
  nonempty := hX.nonempty
  inv_involutive := hX.inv_involutive
  inv_ne := hX.inv_ne
  inv_mem_bdry := hX.inv_mem_bdry
  boundaryVertex_card := by
    rw [hd.boundaryVertices_swivelMove hX]
    exact hX.boundaryVertex_card
  exists_orbit := by
    obtain ⟨f, hf, hfB, hu, hdj⟩ := hX.exists_orbit
    refine ⟨f, ?_, hfB, hu, hdj⟩
    obtain ⟨e, rfl⟩ := X.mem_faceOrbits.1 hf
    refine (X.swivelMove d₁).mem_faceOrbits.2 ⟨e, ?_⟩
    ext w
    simp only [RotationSystem.mem_faceOf]
    refine (sameCycle_iff_of_eqOn (S := (X.faceOf e : Set H)) (fun y hy => ?_)
      (fun y hy => ?_) (X.self_mem_faceOf e)).symm
    · simp only [mem_coe] at hy ⊢
      rw [← X.faceOf_eq_of_mem hy]
      exact X.facePerm_mem_faceOf y
    · exact (hd.facePerm_swivelMove_of_mem_bdry hX (hfB hy)).symm
  internalVertex_card := by
    intro v hv
    obtain ⟨hvV, hvb⟩ := (X.swivelMove d₁).mem_internalVertices.1 hv
    obtain ⟨z, rfl⟩ := (X.swivelMove d₁).mem_vertices.1 hvV
    by_cases hz : z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)
    · exact (hd.vertexOf_swivelMove_of_mem hX hz).2.2
    · rw [vertexOf_swivelMove_of_notMem hz] at hvb ⊢
      exact hX.internalVertex_card _ (X.vertexOf_mem_internalVertices.2 hvb)
  endDart_notMem_bdry := hX.endDart_notMem_bdry
  endpoint_mem r := by
    rw [hd.endpoint_swivelMove hX, hd.boundaryVertices_swivelMove hX]
    exact hX.endpoint_mem r
  endpoint_injective := by
    have : (X.swivelMove d₁).endpoint = X.endpoint := funext (hd.endpoint_swivelMove hX)
    rw [this]
    exact hX.endpoint_injective
  exists_endpoint_eq v hv := by
    rw [hd.boundaryVertices_swivelMove hX] at hv
    obtain ⟨r, hr⟩ := hX.exists_endpoint_eq v hv
    exact ⟨r, (hd.endpoint_swivelMove hX r).trans hr⟩
  exists_exterior r := by
    simp only [hd.exterior_swivelMove hX, hd.endpoint_swivelMove hX, swivelMove_inv]
    exact hX.exists_exterior r
  isOut_inv := hX.isOut_inv
  isOut_rot z hz := hd.isOut_swivelRot hX z ((hd.isBoundaryVertex_swivelMove_iff hX z).not.1 hz)
  isOut_source := hX.isOut_source
  isOut_target := hX.isOut_target

/-! ### Counting vertices and faces -/

/-- In the swivel move, `d₁` and `d₂` still lie at distinct vertices. -/
theorem IsDigon.vertexOf_swivelMove_ne (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) :
    (X.swivelMove d₁).vertexOf d₁ ≠ (X.swivelMove d₁).vertexOf (X.facePerm d₁) := by
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, -, hnd, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, hW₁, hW₂⟩ := hd.exists_swivel hX
  generalize X.facePerm d₁ = d₂ at *
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hnd'
  rw [hW₁, hW₂]
  intro h
  have : d₂ ∈ ({X.inv d₂, d₁, a₃, a₄, b₁, b₂} : Finset H) := by rw [h]; simp
  simp only [mem_insert, mem_singleton] at this
  rcases this with h | h | h | h | h | h <;> simp [h.symm] at hnd'

/-- **A swivel move preserves the number of vertices.** -/
theorem IsDigon.card_vertices_swivelMove (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) : (X.swivelMove d₁).vertices.card = X.vertices.card := by
  have hU : ∀ u ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁),
      X.vertexOf u ⊆ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun u hu => by
    rcases mem_union.1 hu with h | h
    · rw [X.vertexOf_eq_of_mem h]; exact subset_union_left
    · rw [X.vertexOf_eq_of_mem h]; exact subset_union_right
  have hd₁ : d₁ ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) :=
    mem_union_left _ (X.self_mem_vertexOf d₁)
  have hd₂ : X.facePerm d₁ ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) :=
    mem_union_right _ (X.self_mem_vertexOf _)
  refine card_image_univ_eq_of_eqOn_compl _ (fun z hz => vertexOf_swivelMove_of_notMem hz)
    (fun u hu => (hd.vertexOf_swivelMove_of_mem hX hu).1) hU
    (X.swivelMove d₁).self_mem_vertexOf X.self_mem_vertexOf ?_
  rw [image_eq_pair (fun u hu => hd.vertexOf_swivelMove_eq_or hX hu) hd₁ hd₂ rfl rfl,
    image_eq_pair (A := X.vertexOf d₁) (B := X.vertexOf (X.facePerm d₁)) (fun u hu => ?_)
      hd₁ hd₂ rfl rfl, card_pair (hd.vertexOf_swivelMove_ne hX), card_pair hd.vertexOf_ne]
  rcases mem_union.1 hu with h | h
  · exact Or.inl (X.vertexOf_eq_of_mem h)
  · exact Or.inr (X.vertexOf_eq_of_mem h)

/-- The number of face orbits is the number of orbits of the face permutation. -/
private theorem card_faceOrbits_eq_numOrbits' {H : Type*} [Fintype H] [DecidableEq H]
    (R : RotationSystem H) : R.faceOrbits.card = numOrbits R.facePerm := by
  rw [numOrbits_eq_card_image]
  rfl

/-- If every point off `Y` is `p` or `q`, and `π` maps both into `Y`, then every cycle of `π`
meets `Y`. -/
private theorem exists_mem_sameCycle_of_apply_mem {α : Type*} {π : Perm α} {Y : Set α} {p q : α}
    (hY : ∀ z, z ∉ Y → z = p ∨ z = q) (hp : π p ∈ Y) (hq : π q ∈ Y) (x : α) :
    ∃ y ∈ Y, π.SameCycle x y := by
  by_cases hx : x ∈ Y
  · exact ⟨x, hx, SameCycle.refl _ _⟩
  · rcases hY x hx with rfl | rfl
    · exact ⟨_, hp, sameCycle_apply_right.2 (SameCycle.refl _ _)⟩
    · exact ⟨_, hq, sameCycle_apply_right.2 (SameCycle.refl _ _)⟩

/-- **A swivel move preserves the number of faces**: the first-return maps of `φ` and of the face
permutation `φ'` of the swivel move to `H ∖ {d̄₁, d̄₂}` coincide. -/
theorem IsDigon.numOrbits_facePerm_swivelMove (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) :
    numOrbits (X.swivelMove d₁).facePerm = numOrbits X.facePerm := by
  have hinv := hX.inv_involutive
  have hφφ : X.rot (X.inv (X.facePerm d₁)) = d₁ := hd.facePerm_facePerm
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, -, -, -, -,
    s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -, -⟩ := hd.exists_swivel hX
  obtain ⟨-, -, -, -, -, -, off⟩ := swivelRot_of_darts h1 h2 h3 h4 h5 g1 g2 g3 g4 g5
    (hnd.sublist sublist_six_twelve)
  have hφ' : ∀ z, (X.swivelMove d₁).facePerm z = X.swivelRot d₁ (X.inv z) := fun _ => rfl
  have hφ : ∀ z, X.facePerm z = X.rot (X.inv z) := fun _ => rfl
  generalize X.facePerm d₁ = d₂ at *
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hnd'
  set Y : Set H := ({X.inv d₁, X.inv d₂} : Set H)ᶜ with hY
  have hmemY : ∀ z, z ∈ Y ↔ z ≠ X.inv d₁ ∧ z ≠ X.inv d₂ := fun z => by
    simp [hY, not_or]
  have hYc : ∀ z, z ∉ Y → z = X.inv d₁ ∨ z = X.inv d₂ := fun z hz => by
    rwa [hmemY, not_and_or, not_ne_iff, not_ne_iff] at hz
  have hY₁ : X.facePerm (X.inv d₁) ∈ Y := by
    rw [hφ, hinv, h1, hmemY]
    exact ⟨fun h => by simp [h] at hnd', fun h => by simp [h] at hnd'⟩
  have hY₂ : X.facePerm (X.inv d₂) ∈ Y := by
    rw [hφ, hinv, g1, hmemY]
    exact ⟨fun h => by simp [h] at hnd', fun h => by simp [h] at hnd'⟩
  have hY₁' : (X.swivelMove d₁).facePerm (X.inv d₁) ∈ Y := by
    rw [hφ', hinv, s1, hmemY]
    exact ⟨fun h => by simp [h] at hnd', fun h => by simp [h] at hnd'⟩
  have hY₂' : (X.swivelMove d₁).facePerm (X.inv d₂) ∈ Y := by
    rw [hφ', hinv, s8, hmemY]
    exact ⟨fun h => by simp [h] at hnd', fun h => by simp [h] at hnd'⟩
  have hn₁ : X.inv d₁ ∉ Y := fun h => ((hmemY _).1 h).1 rfl
  have hn₂ : X.inv d₂ ∉ Y := fun h => ((hmemY _).1 h).2 rfl
  have key : ∀ z (hz : z ∈ Y), (firstReturn X.facePerm Y ⟨z, hz⟩ : H) =
      firstReturn (X.swivelMove d₁).facePerm Y ⟨z, hz⟩ := by
    intro z hz
    obtain ⟨hz₁, hz₂⟩ := (hmemY z).1 hz
    have hz₁' : X.inv z ≠ d₁ := fun h => hz₁ (by rw [← h, hinv])
    have hz₂' : X.inv z ≠ d₂ := fun h => hz₂ (by rw [← h, hinv])
    by_cases ha₂ : X.inv z = a₂
    · have e1 : X.facePerm z = a₃ := by rw [hφ, ha₂, h3]
      have e2 : (X.swivelMove d₁).facePerm z = X.inv d₁ := by rw [hφ', ha₂, s12]
      have e3 : (X.swivelMove d₁).facePerm (X.inv d₁) = a₃ := by rw [hφ', hinv, s1]
      have hm : a₃ ∈ Y := (hmemY _).2 ⟨fun h => by simp [h] at hnd', fun h => by simp [h] at hnd'⟩
      rw [coe_firstReturn_mk_of_apply_mem hz (e1 ▸ hm),
        coe_firstReturn_mk_of_apply_apply_mem hz (e2 ▸ hn₁) (by rwa [e2, e3]), e2, e3,
        e1]
    by_cases ha₄ : X.inv z = a₄
    · have e1 : X.facePerm z = X.inv d₂ := by rw [hφ, ha₄, h5]
      have e2 : X.facePerm (X.inv d₂) = b₁ := by rw [hφ, hinv, g1]
      have e3 : (X.swivelMove d₁).facePerm z = b₁ := by rw [hφ', ha₄, s3]
      have hm : b₁ ∈ Y := (hmemY _).2 ⟨fun h => by simp [h] at hnd', fun h => by simp [h] at hnd'⟩
      rw [coe_firstReturn_mk_of_apply_apply_mem hz (e1 ▸ hn₂) (by rwa [e1, e2]),
        coe_firstReturn_mk_of_apply_mem hz (e3 ▸ hm), e1, e2, e3]
    by_cases hb₂ : X.inv z = b₂
    · have e1 : X.facePerm z = b₃ := by rw [hφ, hb₂, g3]
      have e2 : (X.swivelMove d₁).facePerm z = X.inv d₂ := by rw [hφ', hb₂, s5]
      have e3 : (X.swivelMove d₁).facePerm (X.inv d₂) = b₃ := by rw [hφ', hinv, s8]
      have hm : b₃ ∈ Y := (hmemY _).2 ⟨fun h => by simp [h] at hnd', fun h => by simp [h] at hnd'⟩
      rw [coe_firstReturn_mk_of_apply_mem hz (e1 ▸ hm),
        coe_firstReturn_mk_of_apply_apply_mem hz (e2 ▸ hn₂) (by rwa [e2, e3]), e2, e3,
        e1]
    by_cases hb₄ : X.inv z = b₄
    · have e1 : X.facePerm z = X.inv d₁ := by rw [hφ, hb₄, g5]
      have e2 : X.facePerm (X.inv d₁) = a₁ := by rw [hφ, hinv, h1]
      have e3 : (X.swivelMove d₁).facePerm z = a₁ := by rw [hφ', hb₄, s10]
      have hm : a₁ ∈ Y := (hmemY _).2 ⟨fun h => by simp [h] at hnd', fun h => by simp [h] at hnd'⟩
      rw [coe_firstReturn_mk_of_apply_apply_mem hz (e1 ▸ hn₁) (by rwa [e1, e2]),
        coe_firstReturn_mk_of_apply_mem hz (e3 ▸ hm), e1, e2, e3]
    have e : (X.swivelMove d₁).facePerm z = X.facePerm z := by
      rw [hφ', hφ, off _ hz₁' ha₂ ha₄ hz₂' hb₂ hb₄]
    have hm : X.facePerm z ∈ Y := by
      rw [hmemY, hφ]
      refine ⟨fun h => hb₄ (X.rot.injective (by rw [h, g5])), fun h => ha₄ (X.rot.injective
        (by rw [h, h5]))⟩
    rw [coe_firstReturn_mk_of_apply_mem hz hm, coe_firstReturn_mk_of_apply_mem hz (e ▸ hm), e]
  have hperm : firstReturnPerm X.facePerm Y = firstReturnPerm (X.swivelMove d₁).facePerm Y := by
    refine Equiv.ext fun y => Subtype.ext ?_
    rw [coe_firstReturnPerm, coe_firstReturnPerm]
    obtain ⟨z, hz⟩ := y
    exact key z hz
  rw [← numOrbits_firstReturnPerm _ Y (exists_mem_sameCycle_of_apply_mem hYc hY₁' hY₂'), ← hperm,
    numOrbits_firstReturnPerm _ Y (exists_mem_sameCycle_of_apply_mem hYc hY₁ hY₂)]

/-! ### A swivel move gives a triple diagram -/

/-- In the swivel move of a triple diagram, every dart reaches every other. -/
theorem IsDigon.reach_swivelMove (hX : X.IsTripleDiagram) (hd : X.IsDigon (X.faceOf d₁))
    (d e : H) : (X.swivelMove d₁).Reach d e := by
  have hP := hX.toIsPreTripleDiagram
  have hU : ∀ u ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁), (X.swivelMove d₁).Reach d₁ u := by
    obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, -, -, hV₁, hV₂, -, -,
      s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -, -⟩ := hd.exists_swivel hP
    have step : ∀ {u v : H}, (X.swivelMove d₁).Reach d₁ u → X.swivelRot d₁ u = v →
        (X.swivelMove d₁).Reach d₁ v := fun {u v} h e => by
      have h' := h.rot
      rwa [swivelMove_rot, e] at h'
    generalize X.facePerm d₁ = d₂ at *
    have c0 := RotationSystem.Reach.refl (R := (X.swivelMove d₁).toRotationSystem) d₁
    have c1 := step c0 s1
    have c2 := step c1 s2
    have c3 := step c2 s3
    have c4 := step c3 s4
    have c5 := step c4 s5
    have c6 : (X.swivelMove d₁).Reach d₁ (X.inv d₁) := c0.inv
    have c7 := step c6 s7
    have c8 := step c7 s8
    have c9 := step c8 s9
    have c10 := step c9 s10
    have c11 := step c10 s11
    intro u hu
    rw [hV₁, hV₂] at hu
    simp only [mem_union, mem_insert, mem_singleton] at hu
    rcases hu with (h | h | h | h | h | h) | (h | h | h | h | h | h) <;> rw [h] <;> assumption
  have hstep : ∀ z, (X.swivelMove d₁).Reach z (X.rot z) := by
    intro z
    by_cases hz : z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)
    · exact (hU z hz).symm.trans (hU _ (rot_mem_union_vertexOf_iff.2 hz))
    · have h := (RotationSystem.Reach.refl (R := (X.swivelMove d₁).toRotationSystem) z).rot
      rwa [swivelMove_rot, swivelRot_apply_of_notMem hz] at h
  induction hX.toIsConnected.reach d e with
  | refl => exact RotationSystem.Reach.refl _
  | rot _ ih => exact ih.trans (hstep _)
  | inv _ ih => exact ih.inv

/-- **A swivel move gives a triple diagram**: the swivel move of a triple diagram at a digon
`f(d₁)` is a triple diagram. -/
@[cluster_algebras "lem_swivel_move_triple"]
theorem IsDigon.isTripleDiagram_swivelMove (hX : X.IsTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) : (X.swivelMove d₁).IsTripleDiagram := by
  have hP := hX.toIsPreTripleDiagram
  refine (hd.isPreTripleDiagram_swivelMove hP).isTripleDiagram (fun d e =>
    (X.swivelMove d₁).toRotationSystem.reach_iff_exists_mem_closure.1
      (hd.reach_swivelMove hX d e)) ?_
  have hF : (X.swivelMove d₁).faceOrbits.card = X.faceOrbits.card := by
    rw [card_faceOrbits_eq_numOrbits', card_faceOrbits_eq_numOrbits',
      hd.numOrbits_facePerm_swivelMove hP]
  rw [hd.card_vertices_swivelMove hP, show (X.swivelMove d₁).edges = X.edges from rfl, hF]
  exact hX.euler

/-! ### Swivel moves commute with isomorphisms -/

namespace Iso

variable {H'' : Type*} [Fintype H''] [DecidableEq H''] {X'' : TripleData H'' b}

/-- An isomorphism maps each vertex `v(d)` onto the vertex `v(θ d)`. -/
theorem map_vertexOf (θ : X.Iso X'') (d : H) :
    (X.vertexOf d).map θ.toEquiv.toEmbedding = X''.vertexOf (θ.toEquiv d) :=
  map_sameCycle_of_semiconj θ.toEquiv θ.map_rot d

/-- An isomorphism maps each orbit `f(d)` of `φ` onto the orbit `f(θ d)`. -/
theorem map_faceOf (θ : X.Iso X'') (d : H) :
    (X.faceOf d).map θ.toEquiv.toEmbedding = X''.faceOf (θ.toEquiv d) :=
  map_sameCycle_of_semiconj θ.toEquiv θ.map_facePerm d

/-- An isomorphism maps the exterior onto the exterior. -/
theorem map_exterior (θ : X.Iso X'') :
    X.exterior.map θ.toEquiv.toEmbedding = X''.exterior := by
  ext y
  rw [mem_map_equiv, DiskMap.mem_exterior, DiskMap.mem_exterior, ← θ.mem_bdry_iff,
    ← θ.mem_bdry_iff (X.rot _), θ.map_rot, Equiv.apply_symm_apply]

/-- An isomorphism intertwines the swivel rotations at `d₁` and at `θ d₁`. -/
theorem map_swivelRot (θ : X.Iso X'') (d₁ z : H) :
    θ.toEquiv (X.swivelRot d₁ z) = X''.swivelRot (θ.toEquiv d₁) (θ.toEquiv z) := by
  have hp := pow_apply_of_semiconj θ.toEquiv θ.map_rot
  simp only [swivelRot, Perm.mul_apply, θ.map_rot, ← θ.toEquiv.injective.swap_apply, hp,
    θ.map_facePerm]

/-- **Swivel moves commute with isomorphisms**: an isomorphism `θ : X → X''` of pre-triple
diagrams is an isomorphism from the swivel move of `X` at `d₁` to the swivel move of `X''` at
`θ d₁`. -/
@[cluster_algebras "lem_swivel_isomorphism"]
def swivelMove (θ : X.Iso X'') (hX : X.IsPreTripleDiagram) (hX'' : X''.IsPreTripleDiagram)
    (d₁ : H) : (X.swivelMove d₁).Iso (X''.swivelMove (θ.toEquiv d₁)) where
  toEquiv := θ.toEquiv
  map_inv := θ.map_inv
  map_rot d := θ.map_swivelRot d₁ d
  mem_bdry_iff := θ.mem_bdry_iff
  map_isOut := θ.map_isOut
  map_endpoint r := by
    have he : θ.toEquiv (X.endDart r) = X''.endDart r := by
      have hmem : θ.toEquiv (X.endDart r) ∈ X''.vertexOf (X''.endDart r) := by
        have := θ.map_endpoint r
        rw [endpoint, endpoint] at this
        rw [← this]
        exact mem_map_of_mem _ (X.self_mem_vertexOf _)
      exact DiskMap.eq_of_notMem_bdry hX''.boundaryVertex_card
        (X''.vertexOf_mem_boundaryVertices.1 (hX''.endpoint_mem r)) hmem
        (X''.self_mem_vertexOf _) (by rw [θ.mem_bdry_iff]; exact hX.endDart_notMem_bdry r)
        (hX''.endDart_notMem_bdry r)
    have := map_sameCycle_of_semiconj (f := X.swivelRot d₁)
      (g := X''.swivelRot (θ.toEquiv d₁)) θ.toEquiv (θ.map_swivelRot d₁) (X.endDart r)
    rwa [he] at this

/-- The isomorphism of swivel moves has the bijection of darts of `θ`. -/
@[simp]
theorem swivelMove_toEquiv (θ : X.Iso X'') (hX : X.IsPreTripleDiagram)
    (hX'' : X''.IsPreTripleDiagram) (d₁ : H) : (θ.swivelMove hX hX'' d₁).toEquiv = θ.toEquiv :=
  rfl

/-- **Isomorphisms preserve digons**: if `θ : X → X''` is an isomorphism and `f(d₁)` is a digon
of `X`, then `f(θ d₁)` is a digon of `X''` and `φ''(θ d₁) = θ(φ d₁)`. -/
@[cluster_algebras "lem_swivel_isomorphism"]
theorem isDigon_faceOf_map (θ : X.Iso X'') (hd : X.IsDigon (X.faceOf d₁)) :
    X''.IsDigon (X''.faceOf (θ.toEquiv d₁)) ∧
      X''.facePerm (θ.toEquiv d₁) = θ.toEquiv (X.facePerm d₁) := by
  refine ⟨?_, (θ.map_facePerm d₁).symm⟩
  obtain ⟨hint, d, hf, hv⟩ := hd
  obtain ⟨hne, hdisj⟩ := X.mem_internalFaces.1 hint
  rw [DiskMap.mem_faces] at hne
  rw [← θ.map_faceOf]
  refine ⟨X''.mem_internalFaces.2 ⟨X''.mem_faces.2 ⟨?_, ?_⟩, ?_⟩, θ.toEquiv d, ?_, ?_⟩
  · rw [← θ.map_exterior]
    exact fun h => hne.1 (map_injective _ h)
  · rw [θ.map_faceOf]
    exact X''.faceOf_mem_faceOrbits _
  · rw [disjoint_left]
    intro w hw hwB
    rw [mem_map_equiv] at hw
    exact disjoint_left.1 hdisj hw ((θ.mem_bdry_iff _).1 (by rwa [Equiv.apply_symm_apply]))
  · rw [hf, map_insert, map_singleton]
    simp only [Equiv.coe_toEmbedding, θ.map_facePerm]
  · rw [← θ.map_vertexOf, ← θ.map_facePerm, ← θ.map_vertexOf]
    exact fun h => hv (map_injective _ h)

end Iso

/-! ### A swivel move is an involution up to isomorphism -/

/-- The face permutation of the swivel move at a digon sends `d₁` to `d₂ = φ(d₁)`. -/
theorem IsDigon.facePerm_swivelMove (hX : X.IsPreTripleDiagram) (hd : X.IsDigon (X.faceOf d₁)) :
    (X.swivelMove d₁).facePerm d₁ = X.facePerm d₁ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    s7, -⟩ := hd.exists_swivel hX
  exact s7

/-- The face `f'(d₁)` of the swivel move at a digon `f(d₁)` is again a digon. -/
theorem IsDigon.isDigon_swivelMove (hX : X.IsPreTripleDiagram) (hd : X.IsDigon (X.faceOf d₁)) :
    (X.swivelMove d₁).IsDigon ((X.swivelMove d₁).faceOf d₁) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    s6, -, -⟩ := hd.exists_swivel hX
  have hφ₁ := hd.facePerm_swivelMove hX
  have hφ₂ : (X.swivelMove d₁).facePerm (X.facePerm d₁) = d₁ := s6
  obtain ⟨hd₁B, hd₂B⟩ := hd.notMem_bdry
  have hfaceOf : (X.swivelMove d₁).faceOf d₁ = {d₁, X.facePerm d₁} := by
    ext w
    rw [RotationSystem.mem_faceOf]
    refine sameCycle_iff_mem_of_mapsTo ?_ ?_ (by simp)
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy ⊢
      rcases hy with rfl | rfl
      · exact Or.inr hφ₁
      · exact Or.inl hφ₂
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact SameCycle.refl _ _
      · rw [← hφ₁]
        exact sameCycle_apply_right.2 (SameCycle.refl _ _)
  refine ⟨?_, d₁, by rw [hfaceOf, hφ₁], by rw [hφ₁]; exact hd.vertexOf_swivelMove_ne hX⟩
  refine (X.swivelMove d₁).mem_internalFaces.2 ⟨(X.swivelMove d₁).mem_faces.2
    ⟨fun h => ?_, (X.swivelMove d₁).faceOf_mem_faceOrbits d₁⟩, ?_⟩
  · have : d₁ ∈ (X.swivelMove d₁).exterior := h ▸ (X.swivelMove d₁).self_mem_faceOf d₁
    exact hd₁B (DiskMap.exterior_subset_bdry _ (hd.exterior_swivelMove hX ▸ this))
  · rw [hfaceOf, disjoint_left]
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hd₁B
    · exact hd₂B

/-- **A swivel move is an involution up to isomorphism**. Let `f(d₁)` be a digon of a pre-triple
diagram `X` and `X'` the swivel move of `X` at `d₁`. Then `f'(d₁)` is a digon of `X'` with
`φ'(d₁) = φ(d₁)`, and the swivel move of `X'` at `d₁` is isomorphic to `X`. -/
@[cluster_algebras "lem_swivel_move_inverse"]
theorem IsDigon.swivelMove_swivelMove (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) :
    (X.swivelMove d₁).IsDigon ((X.swivelMove d₁).faceOf d₁) ∧
      (X.swivelMove d₁).facePerm d₁ = X.facePerm d₁ ∧
      ((X.swivelMove d₁).swivelMove d₁).Isomorphic X := by
  have hinv := hX.inv_involutive
  obtain ⟨hd₁B, hd₂B⟩ := hd.notMem_bdry
  have hinvB : ∀ z, z ∉ X.bdry → X.inv z ∉ X.bdry := fun z hz h =>
    hz (by simpa [hinv z] using hX.inv_mem_bdry _ h)
  have hoU : ∀ z, ¬X.IsBoundaryVertex (X.vertexOf z) →
      X.isOut (X.rot z) = !X.isOut z := fun z hz => Bool.eq_not_iff.2 (hX.isOut_rot z hz)
  have hW : ∀ z, z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) →
      ¬X.IsBoundaryVertex (X.vertexOf z) := fun z hz h => hd.notMem_of_isBoundaryVertex hX h hz
  have hendU : ∀ r, X.endDart r ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun r =>
    hd.notMem_of_isBoundaryVertex hX (X.vertexOf_mem_boundaryVertices.1 (hX.endpoint_mem r))
  have hendU' : ∀ r, X.endDart r ∉ (X.swivelMove d₁).vertexOf d₁ ∪
      (X.swivelMove d₁).vertexOf (X.facePerm d₁) := fun r h => by
    rcases mem_union.1 h with h | h
    · exact hendU r ((hd.vertexOf_swivelMove_of_mem hX
        (mem_union_left _ (X.self_mem_vertexOf d₁))).1 h)
    · exact hendU r ((hd.vertexOf_swivelMove_of_mem hX
        (mem_union_right _ (X.self_mem_vertexOf _))).1 h)
  have hfixU : ∀ r, ∀ w ∈ X.vertexOf (X.endDart r),
      w ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun r w hw =>
    notMem_of_mem_vertexOf (hendU r) hw
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    -, -, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, hW₁, hW₂⟩ := hd.exists_swivel hX
  have hφ₁ : (X.swivelMove d₁).facePerm d₁ = X.facePerm d₁ := s7
  have hend : ∀ r, ((X.swivelMove d₁).swivelMove d₁).endpoint r = X.endpoint r := fun r => by
    change ((X.swivelMove d₁).swivelMove d₁).vertexOf (X.endDart r) = X.vertexOf (X.endDart r)
    rw [vertexOf_swivelMove_of_notMem (by rw [hφ₁]; exact hendU' r),
      vertexOf_swivelMove_of_notMem (hendU r)]
  obtain ⟨-, -, -, -, -, -, off⟩ := swivelRot_of_darts h1 h2 h3 h4 h5 g1 g2 g3 g4 g5
    (hnd.sublist sublist_six_twelve)
  have hφ : X.rot (X.inv d₁) = X.facePerm d₁ := rfl
  have hφφ : X.rot (X.inv (X.facePerm d₁)) = d₁ := hd.facePerm_facePerm
  have hrotU : ∀ z, X.rot z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) ↔
      z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun z => rot_mem_union_vertexOf_iff
  refine ⟨hd.isDigon_swivelMove hX, hφ₁, ?_⟩
  have hd₂U : X.facePerm d₁ ∈ X.vertexOf (X.facePerm d₁) := X.self_mem_vertexOf _
  have od₂ : X.isOut (X.facePerm d₁) = X.isOut d₁ := by
    rw [← hφ, hoU _ (hW _ (mem_union_right _ (by rw [hV₂]; simp))),
      Bool.eq_not_iff.2 (hX.isOut_inv d₁ hd₁B), Bool.not_not]
  have oe₂ : X.isOut (X.inv (X.facePerm d₁)) = X.isOut (X.inv d₁) := by
    rw [Bool.eq_not_iff.2 (hX.isOut_inv _ hd₂B), Bool.eq_not_iff.2 (hX.isOut_inv _ hd₁B), od₂]
  generalize X.facePerm d₁ = d₂ at *
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hnd'
  have hnd6 : [d₁, a₄, b₂, (X.swivelMove d₁).facePerm d₁, b₄, a₂].Nodup := by
    rw [hφ₁]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    and_intros <;> exact fun h => by simp [h] at hnd'
  obtain ⟨u1, u2, u3, u4, u5, u6, off''⟩ := swivelRot_of_darts (X := X.swivelMove d₁)
    (a₁ := a₃) (a₂ := a₄) (a₃ := b₁) (a₄ := b₂) (b₁ := b₃) (b₂ := b₄) (b₃ := a₁) (b₄ := a₂)
    s1 s2 s3 s4 (by rwa [hφ₁]) (by rwa [hφ₁]) s9 s10 s11 s12 hnd6
  simp only [hφ₁, swivelMove_inv] at u1 u2 u3 u4 u5 u6 off''
  set θ : Perm H := swap d₁ d₂ * swap (X.inv d₁) (X.inv d₂) with hθ
  obtain ⟨θd₁, θd₂, θe₁, θe₂⟩ :
      θ d₁ = d₂ ∧ θ d₂ = d₁ ∧ θ (X.inv d₁) = X.inv d₂ ∧ θ (X.inv d₂) = X.inv d₁ :=
    swap_mul_swap_apply_of_ne (fun h => by simp [h.symm] at hnd')
      (fun h => by simp [h.symm] at hnd') (fun h => by simp [h.symm] at hnd')
      (fun h => by simp [h.symm] at hnd')
  have θfix : ∀ z, z ≠ d₁ → z ≠ d₂ → z ≠ X.inv d₁ → z ≠ X.inv d₂ → θ z = z := by
    intro z n1 n2 n3 n4
    rw [hθ, Perm.mul_apply, swap_apply_of_ne_of_ne n3 n4, swap_apply_of_ne_of_ne n1 n2]
  have θU : ∀ z, z ∉ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H) ∪
      {d₂, b₁, b₂, b₃, b₄, X.inv d₁} → θ z = z := by
    intro z hz
    exact θfix z (fun h => hz (by rw [h]; simp)) (fun h => hz (by rw [h]; simp))
      (fun h => hz (by rw [h]; simp)) (fun h => hz (by rw [h]; simp))
  rw [hV₁, hV₂] at hfixU hrotU
  obtain ⟨θa₁, θa₂, θa₃, θa₄, θb₁, θb₂, θb₃, θb₄⟩ : θ a₁ = a₁ ∧ θ a₂ = a₂ ∧ θ a₃ = a₃ ∧
      θ a₄ = a₄ ∧ θ b₁ = b₁ ∧ θ b₂ = b₂ ∧ θ b₃ = b₃ ∧ θ b₄ = b₄ := by
    and_intros <;> refine θfix _ ?_ ?_ ?_ ?_ <;> intro h <;> simp [h] at hnd'
  have ta₁ : (X.swivelMove d₁).swivelRot d₁ a₁ = a₂ := by
    rw [off'' _ ?_ ?_ ?_ ?_ ?_ ?_, swivelMove_rot, s11] <;> intro h <;> simp [h] at hnd'
  have ta₃ : (X.swivelMove d₁).swivelRot d₁ a₃ = a₄ := by
    rw [off'' _ ?_ ?_ ?_ ?_ ?_ ?_, swivelMove_rot, s2] <;> intro h <;> simp [h] at hnd'
  have tb₁ : (X.swivelMove d₁).swivelRot d₁ b₁ = b₂ := by
    rw [off'' _ ?_ ?_ ?_ ?_ ?_ ?_, swivelMove_rot, s4] <;> intro h <;> simp [h] at hnd'
  have tb₃ : (X.swivelMove d₁).swivelRot d₁ b₃ = b₄ := by
    rw [off'' _ ?_ ?_ ?_ ?_ ?_ ?_, swivelMove_rot, s9] <;> intro h <;> simp [h] at hnd'
  have te₁ : (X.swivelMove d₁).swivelRot d₁ (X.inv d₁) = d₂ := by
    rw [off'' _ ?_ ?_ ?_ ?_ ?_ ?_, swivelMove_rot, s7] <;> intro h <;> simp [h] at hnd'
  have te₂ : (X.swivelMove d₁).swivelRot d₁ (X.inv d₂) = d₁ := by
    rw [off'' _ ?_ ?_ ?_ ?_ ?_ ?_, swivelMove_rot, s6] <;> intro h <;> simp [h] at hnd'
  refine ⟨⟨θ, fun z => ?_, fun z => ?_, fun z => ?_, fun z _ => ?_, fun r => ?_⟩⟩
  · exact swap_mul_swap_apply_comm_of_involutive hinv (fun h => by simp [h.symm] at hnd')
      (fun h => by simp [h.symm] at hnd') (fun h => by simp [h.symm] at hnd')
      (fun h => by simp [h.symm] at hnd') z
  · change θ ((X.swivelMove d₁).swivelRot d₁ z) = X.rot (θ z)
    by_cases hz : z ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H) ∪ {d₂, b₁, b₂, b₃, b₄, X.inv d₁}
    · simp only [mem_union, mem_insert, mem_singleton] at hz
      rcases hz with (h | h | h | h | h | h) | (h | h | h | h | h | h) <;> rw [h] <;>
        simp only [u1, u2, u3, u4, u5, u6, ta₁, ta₃, tb₁, tb₃, te₁, te₂, θd₁, θd₂, θe₁, θe₂,
          θa₁, θa₂, θa₃, θa₄, θb₁, θb₂, θb₃, θb₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hφ,
          hφφ]
    · have n : ∀ v ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H) ∪
          {d₂, b₁, b₂, b₃, b₄, X.inv d₁}, z ≠ v := fun v hv h => hz (h ▸ hv)
      rw [off'' z (n _ (by simp)) (n _ (by simp)) (n _ (by simp)) (n _ (by simp))
          (n _ (by simp)) (n _ (by simp)), swivelMove_rot,
        off z (n _ (by simp)) (n _ (by simp)) (n _ (by simp)) (n _ (by simp))
          (n _ (by simp)) (n _ (by simp)), θU z hz,
        θU _ (fun h => hz ((hrotU z).1 h))]
  · exact Iff.of_eq (apply_swap_mul_swap_eq_of_eq (· ∈ X.bdry)
      (propext (iff_of_false hd₁B hd₂B))
      (propext (iff_of_false (hinvB _ hd₁B) (hinvB _ hd₂B))) z)
  · exact apply_swap_mul_swap_eq_of_eq X.isOut od₂.symm oe₂.symm z
  · rw [hend r]
    ext w
    simp only [mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [θU v (hfixU r v hv)]
      exact hv
    · intro hw
      exact ⟨w, hw, θU w (hfixU r w hw)⟩

/-! ### A swivel move preserves the strand permutation -/

/-- The strand permutation read off the last dart of the arc. -/
private theorem strandPerm_eq_elim (Y : TripleData H b) (i : Fin b) :
    Y.strandPerm i = ((Y.arcLastIndex i).map (Y.arcDart i)).elim i
      (fun w => (Y.findTarget (Y.vertexOf (Y.inv w))).getD i) := by
  unfold strandPerm
  cases Y.arcLastIndex i <;> rfl

/-- The last dart of the arc from `s_i` is the first iterate of the strand map running to an
endpoint. -/
private theorem map_arcLastIndex_eq_some_iff (Y : TripleData H b) {i : Fin b} {w : H} :
    (Y.arcLastIndex i).map (Y.arcDart i) = some w ↔
      ∃ k, Y.strandMap^[k] (Y.endDart (sourceIndex i)) = w ∧ Y.RunsToEndpoint w ∧
        ∀ j < k, ¬Y.RunsToEndpoint (Y.strandMap^[j] (Y.endDart (sourceIndex i))) := by
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨h1, h2⟩ := Y.arcLastIndex_eq_some_iff.1 hm
    exact ⟨m, rfl, h1, h2⟩
  · rintro ⟨k, rfl, h1, h2⟩
    exact ⟨k, Y.arcLastIndex_eq_some_iff.2 ⟨h1, h2⟩, rfl⟩

/-- **A swivel move preserves the strand permutation**: if `f(d₁)` is a digon of a pre-triple
diagram `X`, then `π_{X'} = π_X` for the swivel move `X'` of `X` at `d₁`. -/
@[cluster_algebras "lem_swivel_strand_permutation"]
theorem IsDigon.strandPerm_swivelMove (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) : (X.swivelMove d₁).strandPerm = X.strandPerm := by
  have hinv := hX.inv_involutive
  have hE : (X.swivelMove d₁).RunsToEndpoint = X.RunsToEndpoint :=
    funext fun z => propext (hd.isBoundaryVertex_swivelMove_iff hX (X.inv z))
  have hT : (X.swivelMove d₁).findTarget = X.findTarget := by
    funext v
    unfold findTarget target
    simp only [hd.endpoint_swivelMove hX]
  have hEU : ∀ z, X.RunsToEndpoint z → X.inv z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) :=
    fun z hz => hd.notMem_of_isBoundaryVertex hX hz
  have hlast : ∀ w, X.RunsToEndpoint w →
      (X.swivelMove d₁).vertexOf (X.inv w) = X.vertexOf (X.inv w) := fun w hw =>
    vertexOf_swivelMove_of_notMem (hEU w hw)
  have haU : ∀ i : Fin b, X.endDart (sourceIndex i) ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) :=
    fun i => hd.notMem_of_isBoundaryVertex hX
      (X.vertexOf_mem_boundaryVertices.1 (hX.endpoint_mem _))
  have hoff : ∀ z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁), X.swivelRot d₁ z = X.rot z :=
    fun z hz => swivelRot_apply_of_notMem hz
  have hrotU : ∀ z, X.rot z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) ↔
      z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun z => rot_mem_union_vertexOf_iff
  have hint : ∀ z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁),
      ¬X.IsBoundaryVertex (X.vertexOf z) := fun z hz h => hd.notMem_of_isBoundaryVertex hX h hz
  have hS3 : ∀ z, ¬X.RunsToEndpoint z → X.strandMap z = X.rot (X.rot (X.rot (X.inv z))) :=
    fun z hz => X.strandMap_of_not_runsToEndpoint hz
  have hS3' : ∀ z, ¬X.RunsToEndpoint z → (X.swivelMove d₁).strandMap z =
      X.swivelRot d₁ (X.swivelRot d₁ (X.swivelRot d₁ (X.inv z))) := fun z hz =>
    (X.swivelMove d₁).strandMap_of_not_runsToEndpoint (by rwa [hE])
  have hφφ : X.rot (X.inv (X.facePerm d₁)) = d₁ := hd.facePerm_facePerm
  have hφ : X.rot (X.inv d₁) = X.facePerm d₁ := rfl
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    -, -, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -, -⟩ := hd.exists_swivel hX
  generalize X.facePerm d₁ = d₂ at *
  rw [hV₁, hV₂] at hEU haU hoff hrotU hint
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hnd'
  set L : Finset H := {d₁, X.inv d₁, d₂, X.inv d₂} with hLdef
  have hLU : ∀ v ∈ L, v ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H) ∪
      {d₂, b₁, b₂, b₃, b₄, X.inv d₁} := by
    intro v hv
    simp only [hLdef, mem_insert, mem_singleton] at hv
    rcases hv with h | h | h | h <;> rw [h] <;> simp
  have hL : ∀ l ∈ L, ¬X.RunsToEndpoint l := by
    intro l hl
    simp only [hLdef, mem_insert, mem_singleton] at hl
    rcases hl with h | h | h | h <;> rw [h] <;> refine hint _ ?_ <;>
      (try simp only [hinv d₁, hinv d₂]) <;> simp
  have Ld₁ : d₁ ∈ L := by simp [hLdef]
  have Le₁ : X.inv d₁ ∈ L := by simp [hLdef]
  have Ld₂ : d₂ ∈ L := by simp [hLdef]
  have Le₂ : X.inv d₂ ∈ L := by simp [hLdef]
  have nL : ∀ v, v ∈ ({a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄} : Finset H) → v ∉ L := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    simp only [hLdef, mem_insert, mem_singleton, not_or]
    rcases hv with h | h | h | h | h | h | h | h <;> rw [h] <;> and_intros <;>
      exact fun h => by simp [h] at hnd'
  have La₁ : a₁ ∉ L := nL _ (by simp)
  have La₂ : a₂ ∉ L := nL _ (by simp)
  have La₃ : a₃ ∉ L := nL _ (by simp)
  have La₄ : a₄ ∉ L := nL _ (by simp)
  have Lb₁ : b₁ ∉ L := nL _ (by simp)
  have Lb₂ : b₂ ∉ L := nL _ (by simp)
  have Lb₃ : b₃ ∉ L := nL _ (by simp)
  have Lb₄ : b₄ ∉ L := nL _ (by simp)
  have Sd₁ : X.strandMap d₁ = b₂ := by rw [hS3 _ (hL _ Ld₁), hφ, g1, g2]
  have Se₁ : X.strandMap (X.inv d₁) = a₃ := by rw [hS3 _ (hL _ Le₁), hinv, h1, h2, h3]
  have Sd₂ : X.strandMap d₂ = a₂ := by rw [hS3 _ (hL _ Ld₂), hφφ, h1, h2]
  have Se₂ : X.strandMap (X.inv d₂) = b₃ := by rw [hS3 _ (hL _ Le₂), hinv, g1, g2, g3]
  have S'd₁ : (X.swivelMove d₁).strandMap d₁ = b₄ := by rw [hS3' _ (hL _ Ld₁), s7, s8, s9]
  have S'e₁ : (X.swivelMove d₁).strandMap (X.inv d₁) = b₁ := by
    rw [hS3' _ (hL _ Le₁), hinv, s1, s2, s3]
  have S'd₂ : (X.swivelMove d₁).strandMap d₂ = a₄ := by rw [hS3' _ (hL _ Ld₂), s6, s1, s2]
  have S'e₂ : (X.swivelMove d₁).strandMap (X.inv d₂) = a₁ := by
    rw [hS3' _ (hL _ Le₂), hinv, s8, s9, s10]
  set g : H → H := fun z => if X.strandMap z ∈ L then X.strandMap (X.strandMap z) else
    X.strandMap z
  have hS : ∀ z, z ∉ L → ¬X.RunsToEndpoint z →
      (X.strandMap z ∉ L ∧ g z = X.strandMap z) ∨
        (X.strandMap z ∈ L ∧ X.strandMap (X.strandMap z) ∉ L ∧
          g z = X.strandMap (X.strandMap z)) := by
    intro z _ _
    by_cases h : X.strandMap z ∈ L
    · refine Or.inr ⟨h, ?_, if_pos h⟩
      have h' := h
      simp only [hLdef, mem_insert, mem_singleton] at h'
      rcases h' with h' | h' | h' | h' <;> rw [h']
      · rwa [Sd₁]
      · rwa [Se₁]
      · rwa [Sd₂]
      · rwa [Se₂]
    · exact Or.inl ⟨h, if_neg h⟩
  have hS' : ∀ z, z ∉ L → ¬X.RunsToEndpoint z →
      ((X.swivelMove d₁).strandMap z ∉ L ∧ g z = (X.swivelMove d₁).strandMap z) ∨
        ((X.swivelMove d₁).strandMap z ∈ L ∧
          (X.swivelMove d₁).strandMap ((X.swivelMove d₁).strandMap z) ∉ L ∧
          g z = (X.swivelMove d₁).strandMap ((X.swivelMove d₁).strandMap z)) := by
    intro z hzL hEz
    have hgz : g z = if X.strandMap z ∈ L then X.strandMap (X.strandMap z) else
      X.strandMap z := rfl
    have hz3 := hS3 z hEz
    have hz3' := hS3' z hEz
    by_cases hw : X.inv z ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H) ∪
        {d₂, b₁, b₂, b₃, b₄, X.inv d₁}
    · simp only [mem_union, mem_insert, mem_singleton] at hw
      have nd₁ : X.inv z ≠ d₁ := fun h => hzL (by rwa [← hinv z, h])
      have nd₂ : X.inv z ≠ d₂ := fun h => hzL (by rwa [← hinv z, h])
      have ne₁ : X.inv z ≠ X.inv d₁ := fun h => hzL (by rwa [X.inv.injective h])
      have ne₂ : X.inv z ≠ X.inv d₂ := fun h => hzL (by rwa [X.inv.injective h])
      rcases hw with (h | h | h | h | h | h) | (h | h | h | h | h | h)
      all_goals first
        | exact absurd h nd₁ | exact absurd h nd₂ | exact absurd h ne₁ | exact absurd h ne₂
        | skip
      all_goals
        rw [h] at hz3 hz3'
        simp only [h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hφ, hφφ] at hz3
        simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12] at hz3'
        rw [hgz, hz3, hz3']
        simp [Sd₁, Se₁, Sd₂, Se₂, S'd₁, S'e₁, S'd₂, S'e₂, Ld₁, Le₁, Ld₂, Le₂, La₁, La₂, La₃,
          La₄, Lb₁, Lb₂, Lb₃, Lb₄]
    · have hw₁ : X.rot (X.inv z) ∉ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H) ∪
          {d₂, b₁, b₂, b₃, b₄, X.inv d₁} := fun h => hw ((hrotU _).1 h)
      have hw₂ : X.rot (X.rot (X.inv z)) ∉ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H) ∪
          {d₂, b₁, b₂, b₃, b₄, X.inv d₁} := fun h => hw₁ ((hrotU _).1 h)
      have hw₃ : X.rot (X.rot (X.rot (X.inv z))) ∉ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H) ∪
          {d₂, b₁, b₂, b₃, b₄, X.inv d₁} := fun h => hw₂ ((hrotU _).1 h)
      have e : (X.swivelMove d₁).strandMap z = X.strandMap z := by
        rw [hz3', hz3, hoff _ hw, hoff _ hw₁, hoff _ hw₂]
      have hSL : X.strandMap z ∉ L := fun h => hw₃ (hz3 ▸ hLU _ h)
      exact Or.inl ⟨e ▸ hSL, by rw [hgz, if_neg hSL, e]⟩
  have key : ∀ i, ((X.swivelMove d₁).arcLastIndex i).map ((X.swivelMove d₁).arcDart i) =
      (X.arcLastIndex i).map (X.arcDart i) := by
    intro i
    have ha : X.endDart (sourceIndex i) ∉ L := fun h => haU i (hLU _ h)
    apply Option.ext
    intro w
    rw [map_arcLastIndex_eq_some_iff, map_arcLastIndex_eq_some_iff, hE, swivelMove_endDart,
      exists_iterate_hit_iff hL hS' ha, exists_iterate_hit_iff hL hS ha]
  funext i
  rw [strandPerm_eq_elim, strandPerm_eq_elim, key, hT]
  cases h : (X.arcLastIndex i).map (X.arcDart i) with
  | none => rfl
  | some w =>
    simp only [Option.elim]
    rw [swivelMove_inv, hlast w ((map_arcLastIndex_eq_some_iff X).1 h).choose_spec.2.1]

end TripleData

end ClusterAlgebras

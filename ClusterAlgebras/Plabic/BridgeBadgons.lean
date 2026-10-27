/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BridgeNormalization
public import ClusterAlgebras.Plabic.BridgeWires

/-!
# Bridge decompositions have no monogon and no parallel digon

Let `f` be an `(a, b)`-bounded affine permutation, `s = ((i₁, j₁), …, (i_r, j_r))` a bridge
sequence for `f` with partial products `f₀ = f, …, f_r` and position maps `ρ_t`, and
`γ : [1, b] → {white, black}`. The strand diagram `X° = X°(G(s, γ), ∅)` of the bridge graph is a
triple diagram; this file shows that it has no monogon and no parallel digon.

The triple points of `X°` are the crossings `W_t = {up_{i_t,t}, dn_{i_t,t}, c_t}` with
`t ≠ m_{i_t}`, and the darts arriving at `W_t` are `δ¹_t = dn_{i_t,u_t}`,
`δ²_t = up_{i_t, nx_{i_t}(t)}` and `δ³_t = c̄_t`. As `G(s, γ)` has no roundtrip, every dart off
the boundary lies on the one-way trip from exactly one label, its *start*: `δ¹_t` starts at
`ρ_{t-1}⁻¹(i_t)`, `δ³_t` at `ρ_{t-1}⁻¹(j_t)`, and `δ²_t` at the label `x` with
`ρ_r(x) = π_G(x) = i_t`. A monogon at `W_t` is a trip carrying two of these darts; two of these
starts agree only if `i_t` is a fixed point of `f_{t-1}`, or of `f_t`, which the bridge sequence
excludes.

A parallel digon with corners `W_t` and `W_u` is a pair of stretches of trips, leaving `W_t`
along two of the `δ^t_k` and arriving at `W_u` along two of the `δ^u_k`. The keys of the darts
increase along trips, which forces `t < u` when both stretches avoid `δ²`. Otherwise the two
wires carrying the stretches either arrive in the order forbidden by the bridge pair condition at
`u` (`IsBridgeSequence.positionMap_lt_positionMap`), or one of them would cross the line of `i_u`
on the wrong side (`IsBridgeSequence.le_positionMap_of_apply_eq_add`,
`IsBridgeSequence.positionMap_le_of_apply_eq`).

## Main results

* `ClusterAlgebras.IsBridgeSequence.not_hasMonogon_strandDiagram_bridgeGraph`: a bridge
  decomposition has no monogon.
* `ClusterAlgebras.IsBridgeSequence.not_hasParallelDigon_strandDiagram_bridgeGraph`: a bridge
  decomposition has no parallel digon.

## Implementation notes

* Labels are `0`-indexed as in `ClusterAlgebras.Plabic.BridgeGraph`: `x : Fin b` is
  FWZ's label `x + 1`, so the start `ρ_{t-1}⁻¹(i_t)` is the label `x'` with
  `x' + 1 = ρ_{t-1}⁻¹(i_t)`. Bridges are `1`-indexed, the `t`-th pair being `s[t - 1]`, which is a
  bridge pair of `f_{t-1} = swapProduct b f s (t - 1)`.
* The strand diagram `X°(G(s, γ), ∅)` is only defined for `b ≥ 1`, which is assumed. The proof
  that it has no monogon does not use that `f` is bounded, which is then not assumed.
* In the second case of the parallel digon, FWZ bound `t` and `u` by `min(t, u)` and
  `max(t, u)`; the key argument already gives `t < u`, which is used instead.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160, Section 7.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset BridgeGraph BridgeSymbol PlabicData

variable {a b : ℕ} {f : ℤ → ℤ} {s : List (ℤ × ℤ)}

/-- The pairs of a bridge sequence satisfy `1 ≤ i_t < j_t ≤ b`. -/
theorem IsBridgeSequence.forall_mem_bounds (hS : IsBridgeSequence b f s) :
    ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b := fun p hp => by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hp
  have h := hS.isBridgePair t ht
  exact ⟨h.one_le, h.lt, h.le⟩

/-- The `t`-th pair (`1`-indexed) of a bridge sequence is a bridge pair of `f_{t-1}`. -/
private theorem isBridgePair_pair (hS : IsBridgeSequence b f s) {t : ℕ}
    (ht : 1 ≤ t ∧ t ≤ s.length) :
    IsBridgePair b (swapProduct b f s (t - 1)) (pair s t).1 (pair s t).2 := by
  rw [pair_eq_getElem ht.1 ht.2]
  exact hS.isBridgePair (t - 1) (by omega)

/-- Every dart of the bridge graph off the boundary lies on a one-way trip. -/
private theorem exists_mem_oneWayTrip (hb : 1 ≤ b) (hS : IsBridgeSequence b f s)
    (γ : Fin b → Shade) {d : BridgeDart b s} (hd : d ∉ (bridgeGraph b s γ).bdry) :
    ∃ i, d ∈ (bridgeGraph b s γ).oneWayTrip i := by
  have hG := isPlabicGraph_bridgeGraph hb hS.forall_mem_bounds hS.isNestedPairSequence γ
  have h := not_hasRoundtrip_bridgeGraph hS.forall_mem_bounds γ
  rw [PlabicData.hasRoundtrip_iff] at h
  push Not at h
  obtain ⟨n, j, hj⟩ := h d hd
  obtain ⟨i, hi, -⟩ := hG.existsUnique_mem_oneWayTrip ⟨j, n, hj.symm⟩
  exact ⟨i, hi⟩

/-- The start of `δ¹_t = dn_{x, pv_x(t)}` for `t ∈ P_x` is `ρ_{t-1}⁻¹(x)`. -/
private theorem start_dn (hb : 1 ≤ b) (hS : IsBridgeSequence b f s) (γ : Fin b → Shade)
    {x : Fin b} {t : ℕ} (ht : t ∈ heights s x) {d : BridgeDart b s}
    (hd : d.1 = .dn x (prev s x t)) {x' : Fin b}
    (hx' : d ∈ (bridgeGraph b s γ).oneWayTrip x') :
    (x' : ℤ) + 1 = (positionMap s (t - 1)).symm ((x : ℤ) + 1) := by
  have hbd := hS.forall_mem_bounds
  have hG := isPlabicGraph_bridgeGraph hb hbd hS.isNestedPairSequence γ
  obtain ⟨x1, hx1⟩ := exists_label_eq (b := b)
    (positionMap_symm_mem_Icc (b := (b : ℤ)) hS.mem_Icc (t - 1) (z := (x : ℤ) + 1)
      ⟨by omega, by have := x.isLt; omega⟩)
  have h0 := pos_of_mem_heights ht
  have htop := le_top ht
  have hpl := prev_lt (s := s) (x := x) h0
  obtain ⟨hdd, hmem⟩ := dn_mem_oneWayTrip_bridgeGraph hb hbd hS.isNestedPairSequence γ
    (y := x) (τ := t - 1) (u := prev s x t) (by omega) (prev_eq_zero_or_mem x t) (by omega)
    (fun v hv hvI => by
      rw [mem_Icc] at hvI
      have := le_prev hv (show v < t by omega)
      omega) hx1
  obtain rfl : d = ⟨.dn x (prev s x t), hdd⟩ := Subtype.ext hd
  rw [hG.eq_of_mem_oneWayTrip hx' hmem]
  exact hx1

/-- The start of `δ³_t = c̄_t` is `ρ_{t-1}⁻¹(j_t)`. -/
private theorem start_bridgeRev (hb : 1 ≤ b) (hS : IsBridgeSequence b f s) (γ : Fin b → Shade)
    {t : ℕ} (ht : 1 ≤ t ∧ t ≤ s.length) {d : BridgeDart b s} (hd : d.1 = .bridgeRev t)
    {x' : Fin b} (hx' : d ∈ (bridgeGraph b s γ).oneWayTrip x') :
    (x' : ℤ) + 1 = (positionMap s (t - 1)).symm (pair s t).2 := by
  have hbd := hS.forall_mem_bounds
  have hG := isPlabicGraph_bridgeGraph hb hbd hS.isNestedPairSequence γ
  have hpb := pair_bounds hbd ht.1 ht.2
  obtain ⟨y, hy⟩ := exists_label_eq (b := b) (i := (pair s t).2) ⟨by omega, hpb.2.2⟩
  obtain ⟨x3, hx3⟩ := exists_label_eq (b := b)
    (positionMap_symm_mem_Icc (b := (b : ℤ)) hS.mem_Icc (t - 1) (z := (y : ℤ) + 1)
      ⟨by omega, by have := y.isLt; omega⟩)
  have hmem := bridgeRev_mem_oneWayTrip_bridgeGraph hb hbd hS.isNestedPairSequence γ ht hy hx3
  obtain rfl : d = ⟨.bridgeRev t, ht⟩ := Subtype.ext hd
  rw [hG.eq_of_mem_oneWayTrip hx' hmem, hx3, hy]

/-- The start `x'` of `up_{z,u}` has `ρ_r(x') = π_G(x') = z`. -/
private theorem start_up (hb : 1 ≤ b) (hS : IsBridgeSequence b f s) (γ : Fin b → Shade)
    {z : Fin b} {u : ℕ} (hu : u ∈ heights s z) {d : BridgeDart b s} (hd : d.1 = .up z u)
    {x' : Fin b} (hx' : d ∈ (bridgeGraph b s γ).oneWayTrip x') :
    positionMap s s.length ((x' : ℤ) + 1) = (z : ℤ) + 1 := by
  have hbd := hS.forall_mem_bounds
  have hG := isPlabicGraph_bridgeGraph hb hbd hS.isNestedPairSequence γ
  obtain ⟨x2, hx2⟩ := exists_label_eq (b := b)
    (positionMap_symm_mem_Icc (b := (b : ℤ)) hS.mem_Icc s.length (z := (z : ℤ) + 1)
      ⟨by omega, by have := z.isLt; omega⟩)
  have hperm : (bridgeGraph b s γ).tripPerm x2 = z := by
    have h1 := tripPerm_bridgeGraph hbd γ x2
    rw [hx2, Equiv.apply_symm_apply] at h1
    exact Fin.ext (by omega)
  have hmem := up_mem_oneWayTrip_bridgeGraph hb hbd hS.isNestedPairSequence γ hu hperm
  obtain rfl : d = ⟨.up z u, hu⟩ := Subtype.ext hd
  rw [hG.eq_of_mem_oneWayTrip hx' hmem, hx2, Equiv.apply_symm_apply]

/-- The crossings of the bridge graph, the darts arriving at them, and their starts: every
crossing is `W_t` for some `t ∈ [1, r]` with `t ≠ m_{i_t}`, the darts `d` with `d̄ ∈ W_t` are
`δ¹_t = dn_{i_t,u_t}`, `δ²_t = up_{i_t, nx(t)}` and `δ³_t = c̄_t`, and they start at
`ρ_{t-1}⁻¹(i_t)`, at the label `x'` with `ρ_r(x') = i_t`, and at `ρ_{t-1}⁻¹(j_t)`. -/
private theorem crossing_data (hb : 1 ≤ b) (hS : IsBridgeSequence b f s) (γ : Fin b → Shade)
    {w : Finset (BridgeDart b s)} (hw : (bridgeGraph b s γ).IsCrossing w) :
    ∃ (t : ℕ) (x : Fin b), (1 ≤ t ∧ t ≤ s.length) ∧ (x : ℤ) + 1 = (pair s t).1 ∧ t < top s x ∧
      (∀ d : BridgeDart b s, (bridgeGraph b s γ).inv d ∈ w ↔
        (d.1 = .dn x (prev s x t) ∨ d.1 = .up x (next s x t) ∨ d.1 = .bridgeRev t)) ∧
      ∀ d : BridgeDart b s, ∀ x' : Fin b, d ∈ (bridgeGraph b s γ).oneWayTrip x' →
        (d.1 = .dn x (prev s x t) → (x' : ℤ) + 1 = (positionMap s (t - 1)).symm (pair s t).1) ∧
        (d.1 = .up x (next s x t) → positionMap s s.length ((x' : ℤ) + 1) = (pair s t).1) ∧
        (d.1 = .bridgeRev t → (x' : ℤ) + 1 = (positionMap s (t - 1)).symm (pair s t).2) := by
  obtain ⟨t, x, ht, hx, htm, himg, -⟩ := exists_eq_of_isCrossing_bridgeGraph γ hw
  have htP : t ∈ heights s x := mem_heights.2 ⟨ht.1, ht.2, Or.inl hx⟩
  have htT : t < top s x := lt_of_le_of_ne (le_top htP) htm
  have hpl := prev_lt (s := s) (x := x) (by omega : 0 < t)
  obtain ⟨-, -, -, hiff⟩ := bridgeGraph_inv_mem_crossing_iff γ ht hx htm
    (prev_eq_zero_or_mem x t) hpl (fun v hv hvI => by
      rw [mem_Icc] at hvI
      have := le_prev hv (show v < t by omega)
      omega)
  refine ⟨t, x, ht, hx, htT, fun d => ?_, fun d x' hx' => ⟨fun hd => ?_, fun hd => ?_,
    fun hd => start_bridgeRev hb hS γ ht hd hx'⟩⟩
  · have e : (bridgeGraph b s γ).inv d ∈ w ↔
        ((bridgeGraph b s γ).inv d).1 ∈ w.image Subtype.val := by
      rw [mem_image]
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨e, he, hee⟩ => Subtype.ext hee ▸ he⟩
    rw [e, himg, hiff]
    simp only [mem_insert, mem_singleton]
  · rw [start_dn hb hS γ htP hd hx', hx]
  · rw [start_up hb hS γ (next_mem htT) hd hx', hx]

/-- The start of `δ³_t` is not the start of `δ²_t`: otherwise `i_t` would be a fixed point of
`f_t`, which the bridge sequence excludes. -/
private theorem false_of_start_bridgeRev_of_start_up (hS : IsBridgeSequence b f s) {t : ℕ}
    (ht : 1 ≤ t ∧ t ≤ s.length) {x : Fin b} (hx : (x : ℤ) + 1 = (pair s t).1)
    (htT : t < top s x) {i : Fin b} (h1 : (i : ℤ) + 1 = (positionMap s (t - 1)).symm (pair s t).2)
    (h2 : positionMap s s.length ((i : ℤ) + 1) = (pair s t).1) : False := by
  have hI : 1 ≤ (i : ℤ) + 1 ∧ (i : ℤ) + 1 ≤ b := ⟨by omega, by have := i.isLt; omega⟩
  have hmod := hS.positionMap_modEq hI
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have ht' : t' < s.length := by omega
  have hpos : positionMap s (t' + 1) ((i : ℤ) + 1) = (pair s (t' + 1)).1 := by
    rw [positionMap_succ ht', Equiv.Perm.mul_apply, h1, Nat.add_sub_cancel,
      Equiv.apply_symm_apply, pair_succ ht', Equiv.swap_apply_right]
  have hfix : IsFixedPointMod b (swapProduct b f s (t' + 1)) (pair s (t' + 1)).1 := by
    have e := swapProduct_positionMap f hS.mem_Icc (t' + 1) hI
    rw [hpos] at e
    rw [IsFixedPointMod, e]
    rw [h2] at hmod
    exact hmod.symm
  have hpb := pair_bounds hS.forall_mem_bounds ht.1 ht.2
  have htop := top_mem ⟨_, mem_heights.2 ⟨ht.1, ht.2, Or.inl hx⟩⟩
  have hT1 := pos_of_mem_heights htop
  have hT2 := le_length_of_mem_heights htop
  obtain ⟨n1, n2⟩ := hS.ne_of_isFixedPointMod (u := top s x - 1) ⟨by omega, by omega⟩ hfix
    (by omega) (by omega)
  rw [← pair_eq_getElem (by omega) hT2] at n1 n2
  rcases (mem_heights.1 htop).2.2 with e | e
  · exact n1 (hx.symm.trans e)
  · exact n2 (hx.symm.trans e)

/-- **No trip passes a crossing twice**: two darts of one one-way trip of `G(s, γ)` whose reverses
lie at the same crossing are equal. -/
private theorem eq_of_inv_mem_of_mem_oneWayTrip (hb : 1 ≤ b) (hS : IsBridgeSequence b f s)
    (γ : Fin b → Shade) {w : Finset (BridgeDart b s)} (hw : (bridgeGraph b s γ).IsCrossing w)
    {d d' : BridgeDart b s} (hd : (bridgeGraph b s γ).inv d ∈ w)
    (hd' : (bridgeGraph b s γ).inv d' ∈ w) {i : Fin b}
    (hi : d ∈ (bridgeGraph b s γ).oneWayTrip i) (hi' : d' ∈ (bridgeGraph b s γ).oneWayTrip i) :
    d = d' := by
  obtain ⟨t, x, ht, hx, htT, hiff, hstart⟩ := crossing_data hb hS γ hw
  have hp := isBridgePair_pair hS ht
  have hI : 1 ≤ (i : ℤ) + 1 ∧ (i : ℤ) + 1 ≤ b := ⟨by omega, by have := i.isLt; omega⟩
  -- the value of the wire of `i`
  have hval : ∀ τ, swapProduct b f s τ (positionMap s τ ((i : ℤ) + 1)) = f ((i : ℤ) + 1) :=
    fun τ => swapProduct_positionMap f hS.mem_Icc τ hI
  have hmod := hS.positionMap_modEq hI
  -- `δ¹_t` and `δ²_t` do not start at the same label
  have h12 : (i : ℤ) + 1 = (positionMap s (t - 1)).symm (pair s t).1 →
      positionMap s s.length ((i : ℤ) + 1) = (pair s t).1 → False := by
    intro h1 h2
    apply hp.not_isFixedPointMod_left
    have e := hval (t - 1)
    rw [h1, Equiv.apply_symm_apply] at e
    rw [IsFixedPointMod, e, ← h1]
    rw [h2] at hmod
    exact hmod.symm
  have hii : ∀ e : BridgeDart b s, e ∈ (bridgeGraph b s γ).oneWayTrip i →
      (bridgeGraph b s γ).inv e ∈ w → ∀ e' : BridgeDart b s,
      e' ∈ (bridgeGraph b s γ).oneWayTrip i → (bridgeGraph b s γ).inv e' ∈ w →
      e.1 ≠ e'.1 → e.1 ≠ .bridgeRev t → False := by
    intro e he hew e' he' hew' hne hne3
    obtain ⟨s1, s2, s3⟩ := hstart e i he
    obtain ⟨s1', s2', s3'⟩ := hstart e' i he'
    rcases (hiff e).1 hew with h | h | h
    · rcases (hiff e').1 hew' with h' | h' | h'
      · exact hne (h.trans h'.symm)
      · exact h12 (s1 h) (s2' h')
      · exact hp.lt.ne ((positionMap s (t - 1)).symm.injective ((s1 h).symm.trans (s3' h')))
    · rcases (hiff e').1 hew' with h' | h' | h'
      · exact h12 (s1' h') (s2 h)
      · exact hne (h.trans h'.symm)
      · exact false_of_start_bridgeRev_of_start_up hS ht hx htT (s3' h')
          (s2 h)
    · exact hne3 h
  by_contra hne
  have hne' : d.1 ≠ d'.1 := fun h => hne (Subtype.ext h)
  by_cases h3 : d.1 = .bridgeRev t
  · exact hii d' hi' hd' d hi hd hne'.symm (fun h => hne' (h3.trans h.symm))
  · exact hii d hi hd d' hi' hd' hne' h3

/-- In `G(s, γ)` for a bridge sequence `s`, every crossing consists of three darts. -/
private theorem card_eq_three (γ : Fin b → Shade) :
    ∀ w, (bridgeGraph b s γ).IsCrossing w → w.card = 3 := fun _ hw => by
  obtain ⟨-, -, -, -, -, -, h⟩ := exists_eq_of_isCrossing_bridgeGraph γ hw
  exact h

/-! ### Keys along a stretch of a trip -/

private theorem key_of_eq_dn {d : BridgeDart b s} {x : Fin b} {u : ℕ} (h : d.1 = .dn x u) :
    d.key = 2 * (u : ℤ) + 1 := by
  simp only [BridgeDart.key, h, BridgeSymbol.key]

private theorem key_of_eq_up {d : BridgeDart b s} {x : Fin b} {u : ℕ} (h : d.1 = .up x u) :
    d.key = 4 * (s.length : ℤ) + 4 - 2 * u := by
  simp only [BridgeDart.key, h, BridgeSymbol.key]

private theorem key_of_eq_bridge {d : BridgeDart b s} {t : ℕ} (h : d.1 = .bridge t) :
    d.key = 2 * (t : ℤ) := by
  simp only [BridgeDart.key, h, BridgeSymbol.key]

private theorem key_of_eq_bridgeRev {d : BridgeDart b s} {t : ℕ} (h : d.1 = .bridgeRev t) :
    d.key = 2 * (t : ℤ) := by
  simp only [BridgeDart.key, h, BridgeSymbol.key]

/-- Along a stretch `d, T(d), …, Tⁿ(d)` of a trip of `G(s, γ)` with `d ∉ B` and no leg among
`T(d), …, Tⁿ(d)`, the keys increase by at least one at each step. -/
private theorem key_growth (hb : 1 ≤ b) (hS : IsBridgeSequence b f s) (γ : Fin b → Shade)
    {d : BridgeDart b s} (hd : d ∉ (bridgeGraph b s γ).bdry) {n : ℕ}
    (hleg : ∀ k, 1 ≤ k → k ≤ n →
      ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[k] d)) :
    ∀ k ≤ n, (bridgeGraph b s γ).tripMap^[k] d ∉ (bridgeGraph b s γ).bdry ∧
      d.key + k ≤ ((bridgeGraph b s γ).tripMap^[k] d).key := by
  have hbd := hS.forall_mem_bounds
  have hG := isPlabicGraph_bridgeGraph hb hbd hS.isNestedPairSequence γ
  intro k
  induction k with
  | zero => exact fun _ => by simpa using hd
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hl := hleg (k + 1) (by omega) hk
    rw [Function.iterate_succ_apply'] at hl ⊢
    refine ⟨fun h => h1 ((tripMap_mem_bdry_iff hG _).1 h), ?_⟩
    have := BridgeDart.key_lt_key_tripMap hbd γ h1 hl
    push_cast
    omega

/-- **(N)** If a one-way trip carries `δ¹_t` or `δ³_t` and, later, `δ¹_u` or `δ³_u`, then
`t < u`. -/
private theorem lt_of_iterate (hb : 1 ≤ b) (hS : IsBridgeSequence b f s) (γ : Fin b → Shade)
    {t : ℕ} (ht : 1 ≤ t ∧ t ≤ s.length) {x : Fin b} (hx : (x : ℤ) + 1 = (pair s t).1)
    (htT : t < top s x) {u : ℕ} (hu0 : 1 ≤ u) {x' : Fin b} {d : BridgeDart b s}
    (hd : d.1 = .dn x (prev s x t) ∨ d.1 = .bridgeRev t) {n : ℕ} (hn : 1 ≤ n)
    (hleg : ∀ k, 1 ≤ k → k ≤ n →
      ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[k] d))
    (he : ((bridgeGraph b s γ).tripMap^[n] d).1 = .dn x' (prev s x' u) ∨
      ((bridgeGraph b s γ).tripMap^[n] d).1 = .bridgeRev u) : t < u := by
  set G := bridgeGraph b s γ
  have hbd := hS.forall_mem_bounds
  have hG := isPlabicGraph_bridgeGraph hb hbd hS.isNestedPairSequence γ
  have htP : t ∈ heights s x := mem_heights.2 ⟨ht.1, ht.2, Or.inl hx⟩
  -- the first step: `T(δ¹_t) = c_t` and `T(δ³_t) = dn_{i_t,t}`, of keys `2t` and `2t + 1`
  have hT : 2 * (t : ℤ) ≤ (G.tripMap d).key ∧ ∀ v, (G.tripMap d).1 ≠ .bridgeRev v := by
    rcases hd with hd | hd
    · have hdd : IsDart s (.dn x (prev s x t)) := hd ▸ d.2
      have e : (G.tripMap d).1 = .bridge t := by
        rw [show d = ⟨_, hdd⟩ from Subtype.ext hd]
        exact (tripMap_bridgeGraph_dn hbd γ (prev_lt_top htP) (next_prev htP) hdd).1 hx
      rw [key_of_eq_bridge e, e]
      exact ⟨le_rfl, fun v h => by cases h⟩
    · have hdd : IsDart (b := b) s (.bridgeRev t) := ht
      have e : (G.tripMap d).1 = .dn x t := by
        rw [show d = ⟨_, hdd⟩ from Subtype.ext hd]
        exact (tripMap_bridgeGraph_bridgeRev γ hdd hx).1 htT.ne
      rw [key_of_eq_dn e, e]
      exact ⟨by omega, fun v h => by cases h⟩
  have hd0 : d ∉ G.bdry := by
    rw [bridgeGraph.mem_bdry]
    rcases hd with hd | hd <;> rw [hd] <;> simp
  have hTd : G.tripMap d ∉ G.bdry := fun h => hd0 ((tripMap_mem_bdry_iff hG d).1 h)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨-, hkey⟩ := key_growth hb hS γ hTd (n := m) (fun k hk1 hk2 => by
    rw [← Function.iterate_succ_apply]
    exact hleg (k + 1) (by omega) (by omega)) m le_rfl
  rw [Function.iterate_succ_apply] at he
  rcases he with he | he
  · rw [key_of_eq_dn he] at hkey
    have := prev_lt (s := s) (x := x') (by omega : 0 < u)
    have := hT.1
    omega
  · rw [key_of_eq_bridgeRev he] at hkey
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact absurd he (hT.2 u)
    · have := hT.1
      omega

/-! ### Strand paths between crossings -/

/-- A strand path of `X°(G, ∅)` from the triple point `x_w` to the triple point `x_{w'}` follows a
stretch `y, T(y), …, Tⁿ(y)` of a trip with `ȳ ∈ w` and `\overline{Tⁿ(y)} ∈ w'`, and its first and
last darts are determined by `y` and `Tⁿ(y)`. -/
private theorem exists_of_isStrandPath {H : Type*} [Fintype H] [DecidableEq H]
    {G : PlabicData H b} (hG : G.IsPlabicGraph) (htri : ∀ w, G.IsCrossing w → w.card = 3)
    {P : List (G.StrandDart fun _ => ∅)}
    (hP : (G.strandDiagram hG (isWhiteDatum_empty htri)).IsStrandPath P)
    {w w' : Finset H} (hw : G.IsCrossing w) (hw' : G.IsCrossing w')
    (hs : (G.strandDiagram hG (isWhiteDatum_empty htri)).pathStart P =
      G.crossingTriplePoint (fun _ => ∅) w)
    (he : (G.strandDiagram hG (isWhiteDatum_empty htri)).pathEnd P =
      G.crossingTriplePoint (fun _ => ∅) w') :
    ∃ y ∉ G.bdry, ∃ n, 1 ≤ n ∧ (∀ k, 1 ≤ k → k ≤ n → ¬G.IsLeg (G.tripMap^[k] y)) ∧
      G.inv y ∈ w ∧ G.inv (G.tripMap^[n] y) ∈ w' ∧
      P.head?.map Subtype.val = some (StrandSymbol.xPlus (G.tripMap y)) ∧
      P.getLast?.map (fun e => ((G.strandDiagram hG (isWhiteDatum_empty htri)).inv e).1) =
        some (StrandSymbol.xMinus (G.tripMap^[n] y)) := by
  set X := G.strandDiagram hG (isWhiteDatum_empty htri)
  obtain ⟨y, hyB, n, hn, -, -, hleg, hhead, hlast⟩ := exists_tripMap_of_isStrandPath hG htri hP
    (hs ▸ crossingTriplePoint_mem_internalVertices htri hG hw)
    (he ▸ crossingTriplePoint_mem_internalVertices htri hG hw')
  obtain ⟨e₁, P', rfl⟩ := List.exists_cons_of_ne_nil hP.ne_nil
  have hm := List.getLast?_eq_some_getLast (l := e₁ :: P') (List.cons_ne_nil _ _)
  set eₘ := (e₁ :: P').getLast (List.cons_ne_nil _ _)
  have h1 : e₁.1 = StrandSymbol.xPlus (G.tripMap y) := hhead e₁ rfl
  have hlastv := hlast eₘ hm
  have hTyw : G.tripMap y ∈ w := by
    have : e₁ ∈ X.pathStart (e₁ :: P') := X.self_mem_vertexOf e₁
    rw [hs] at this
    exact (mem_crossingTriplePoint_of_eq_xPlus h1).1 this
  have hyw : G.vertexOf (G.inv y) = w :=
    (vertexOf_turn (G.inv y)).symm.trans (hw.eq_vertexOf hTyw).symm
  have hy'w : G.inv (G.tripMap^[n] y) ∈ w' := by
    have : X.inv eₘ ∈ X.pathEnd (e₁ :: P') := by
      rw [X.pathEnd_of_getLast? hm]
      exact X.self_mem_vertexOf _
    rw [he] at this
    exact (mem_crossingTriplePoint_of_eq_xMinus hG hlastv).1 this
  refine ⟨y, hyB, n, hn, hleg, hyw ▸ G.self_mem_vertexOf _, hy'w, by simp [h1], ?_⟩
  rw [hm]
  exact congrArg some hlastv

/-! ### The cases of a parallel digon -/

/-- The position map `ρ_t = τ_t ∘ ρ_{t-1}`. -/
private theorem positionMap_eq_swap {t : ℕ} (ht : 1 ≤ t ∧ t ≤ s.length) (v : ℤ) :
    positionMap s t v = Equiv.swap (pair s t).1 (pair s t).2 (positionMap s (t - 1) v) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [positionMap_succ (by omega), pair_succ (by omega), Equiv.Perm.mul_apply, Nat.add_sub_cancel]

/-- **Case 1** of the parallel digon: the strand path leaving `x_{W_t}` along `δ²_t` cannot run
to the same triple point as one leaving along `δ¹_t` or `δ³_t`. -/
private theorem false_of_up (hb : 1 ≤ b) (hS : IsBridgeSequence b f s) (γ : Fin b → Shade)
    {t : ℕ} (ht : 1 ≤ t ∧ t ≤ s.length) {xt : Fin b} (hxt : (xt : ℤ) + 1 = (pair s t).1)
    (htT : t < top s xt) {u : ℕ} (hu : 1 ≤ u ∧ u ≤ s.length) {xu : Fin b}
    (hxu : (xu : ℤ) + 1 = (pair s u).1) (huT : u < top s xu)
    {y y' : BridgeDart b s} {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (hleg : ∀ k, 1 ≤ k → k ≤ n →
      ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[k] y))
    (hleg' : ∀ k, 1 ≤ k → k ≤ n' →
      ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[k] y'))
    (hy : y.1 = .up xt (next s xt t)) (hy' : y'.1 = .dn xt (prev s xt t) ∨ y'.1 = .bridgeRev t)
    (hz : ((bridgeGraph b s γ).tripMap^[n] y).1 = .dn xu (prev s xu u) ∨
      ((bridgeGraph b s γ).tripMap^[n] y).1 = .up xu (next s xu u) ∨
      ((bridgeGraph b s γ).tripMap^[n] y).1 = .bridgeRev u)
    (hz' : ((bridgeGraph b s γ).tripMap^[n'] y').1 = .dn xu (prev s xu u) ∨
      ((bridgeGraph b s γ).tripMap^[n'] y').1 = .up xu (next s xu u) ∨
      ((bridgeGraph b s γ).tripMap^[n'] y').1 = .bridgeRev u)
    (hzz : (bridgeGraph b s γ).tripMap^[n] y ≠ (bridgeGraph b s γ).tripMap^[n'] y')
    {sy : Fin b} (hsy : y ∈ (bridgeGraph b s γ).oneWayTrip sy)
    (hsz : (bridgeGraph b s γ).tripMap^[n] y ∈ (bridgeGraph b s γ).oneWayTrip sy) : False := by
  set G := bridgeGraph b s γ
  have hyB : y ∉ G.bdry := by
    rw [bridgeGraph.mem_bdry, hy]
    simp
  obtain ⟨-, hkey⟩ := key_growth hb hS γ hyB hleg n le_rfl
  rw [key_of_eq_up hy] at hkey
  have hnt := le_length_of_mem_heights (next_mem htT)
  have hp0 := prev_lt (s := s) (x := xu) (by omega : 0 < u)
  rcases hz with hz | hz | hz
  · rw [key_of_eq_dn hz] at hkey
    omega
  · -- `Tⁿ(y) = δ²_u`: both lie on the trip ending at `i_t = i_u`
    have e1 := start_up hb hS γ (next_mem htT) hy hsy
    have e2 := start_up hb hS γ (next_mem huT) hz hsz
    obtain rfl : xt = xu := Fin.ext (by omega)
    rw [key_of_eq_up hz] at hkey
    have hut : u < t := by
      by_contra h
      rcases eq_or_lt_of_le (not_lt.1 h) with h | h
      · subst h
        omega
      · have huP : u ∈ heights s xt := mem_heights.2 ⟨hu.1, hu.2, Or.inl hxu⟩
        have := next_le huP h
        have := lt_next huT
        omega
    have hz'' : ((bridgeGraph b s γ).tripMap^[n'] y').1 = .dn xt (prev s xt u) ∨
        ((bridgeGraph b s γ).tripMap^[n'] y').1 = .bridgeRev u := by
      rcases hz' with h | h | h
      · exact Or.inl h
      · exact absurd (Subtype.ext (hz.trans h.symm)) hzz
      · exact Or.inr h
    have := lt_of_iterate hb hS γ ht hxt htT hu.1 hy' hn' hleg' hz''
    omega
  · rw [key_of_eq_bridgeRev hz] at hkey
    omega

/-- The start `x'` of a dart `z` with `z̄` at `W_u` has `ρ_{u-1}(x') ∉ {i_u, j_u}` if `z = δ²_u`:
otherwise the trip from `x'` would also carry `δ¹_u` or `δ³_u`, and pass `W_u` twice. -/
private theorem positionMap_ne_of_up (hb : 1 ≤ b) (hS : IsBridgeSequence b f s)
    (γ : Fin b → Shade) {w : Finset (BridgeDart b s)} (hw : (bridgeGraph b s γ).IsCrossing w)
    {u : ℕ} (hu : 1 ≤ u ∧ u ≤ s.length) {xu : Fin b} (hxu : (xu : ℤ) + 1 = (pair s u).1)
    (huT : u < top s xu)
    (hiff : ∀ d : BridgeDart b s, (bridgeGraph b s γ).inv d ∈ w ↔
      (d.1 = .dn xu (prev s xu u) ∨ d.1 = .up xu (next s xu u) ∨ d.1 = .bridgeRev u))
    {z : BridgeDart b s} (hz : z.1 = .up xu (next s xu u)) {sx : Fin b}
    (hzs : z ∈ (bridgeGraph b s γ).oneWayTrip sx) :
    positionMap s (u - 1) ((sx : ℤ) + 1) ≠ (pair s u).1 ∧
      positionMap s (u - 1) ((sx : ℤ) + 1) ≠ (pair s u).2 := by
  have hbd := hS.forall_mem_bounds
  have hzw := (hiff z).2 (Or.inr (Or.inl hz))
  have hpl := prev_lt (s := s) (x := xu) (by omega : 0 < u)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hsx : (sx : ℤ) + 1 = (positionMap s (u - 1)).symm ((xu : ℤ) + 1) := by
      rw [Equiv.eq_symm_apply, h, hxu]
    obtain ⟨hdd, hmem⟩ := dn_mem_oneWayTrip_bridgeGraph hb hbd hS.isNestedPairSequence γ
      (y := xu) (τ := u - 1) (u := prev s xu u) (by omega) (prev_eq_zero_or_mem xu u)
      (by omega) (fun v hv hvI => by
        rw [mem_Icc] at hvI
        have := le_prev hv (show v < u by omega)
        omega) hsx
    have := congrArg Subtype.val
      (eq_of_inv_mem_of_mem_oneWayTrip hb hS γ hw hzw ((hiff _).2 (Or.inl rfl)) hzs hmem)
    rw [hz] at this
    cases this
  · have hpb := pair_bounds hbd hu.1 hu.2
    obtain ⟨y, hy⟩ := exists_label_eq (b := b) (i := (pair s u).2) ⟨by omega, hpb.2.2⟩
    have hsx : (sx : ℤ) + 1 = (positionMap s (u - 1)).symm ((y : ℤ) + 1) := by
      rw [Equiv.eq_symm_apply, h, hy]
    have hmem := bridgeRev_mem_oneWayTrip_bridgeGraph hb hbd hS.isNestedPairSequence γ hu hy hsx
    have := congrArg Subtype.val (eq_of_inv_mem_of_mem_oneWayTrip hb hS γ hw hzw
      ((hiff ⟨.bridgeRev u, hu⟩).2 (Or.inr (Or.inr rfl))) hzs hmem)
    rw [hz] at this
    cases this

/-- The start `U` of `δ²_u` has `ρ_{u-1}(U) ∉ {i_u, j_u}` and `f(U) ∈ {i_u, i_u + b}`, and
`ρ_{u-1}(U)` is not a fixed point of `f_{u-1}`. -/
private theorem up_props (hb : 1 ≤ b) (hf : IsBoundedAffinePerm a b f)
    (hS : IsBridgeSequence b f s) (γ : Fin b → Shade) {w : Finset (BridgeDart b s)}
    (hw : (bridgeGraph b s γ).IsCrossing w)
    {u : ℕ} (hu : 1 ≤ u ∧ u ≤ s.length) {xu : Fin b} (hxu : (xu : ℤ) + 1 = (pair s u).1)
    (huT : u < top s xu)
    (hiff : ∀ d : BridgeDart b s, (bridgeGraph b s γ).inv d ∈ w ↔
      (d.1 = .dn xu (prev s xu u) ∨ d.1 = .up xu (next s xu u) ∨ d.1 = .bridgeRev u))
    {z : BridgeDart b s} (hz : z.1 = .up xu (next s xu u)) {sx : Fin b}
    (hzs : z ∈ (bridgeGraph b s γ).oneWayTrip sx) :
    (positionMap s (u - 1) ((sx : ℤ) + 1) ≠ (pair s u).1 ∧
      positionMap s (u - 1) ((sx : ℤ) + 1) ≠ (pair s u).2) ∧
    (f ((sx : ℤ) + 1) = (xu : ℤ) + 1 ∨ f ((sx : ℤ) + 1) = (xu : ℤ) + 1 + b) ∧
    ¬IsFixedPointMod b (swapProduct b f s (u - 1)) (positionMap s (u - 1) ((sx : ℤ) + 1)) := by
  have hzI : 1 ≤ (xu : ℤ) + 1 ∧ (xu : ℤ) + 1 ≤ b := ⟨by omega, by have := xu.isLt; omega⟩
  have hsI : 1 ≤ (sx : ℤ) + 1 ∧ (sx : ℤ) + 1 ≤ b := ⟨by omega, by have := sx.isLt; omega⟩
  have hne := positionMap_ne_of_up hb hS γ hw hu hxu huT hiff hz hzs
  have hmod := hS.positionMap_modEq hsI
  rw [start_up hb hS γ (next_mem huT) hz hzs] at hmod
  have hle := hf.le_apply ((sx : ℤ) + 1)
  have hge := hf.apply_le ((sx : ℤ) + 1)
  refine ⟨hne, ?_, fun hfix => ?_⟩
  · by_cases hc : f ((sx : ℤ) + 1) ≤ b
    · exact Or.inl (eq_of_modEq_of_mem_Icc ⟨by omega, hc⟩ hzI hmod.symm)
    · right
      have e : f ((sx : ℤ) + 1) - b ≡ f ((sx : ℤ) + 1) [ZMOD b] :=
        Int.modEq_iff_dvd.2 ⟨1, by ring⟩
      have := eq_of_modEq_of_mem_Icc ⟨by omega, by omega⟩ hzI (e.trans hmod.symm)
      omega
  · rw [IsFixedPointMod, swapProduct_positionMap f hS.mem_Icc (u - 1) hsI] at hfix
    have hpI := positionMap_mem_Icc (b := (b : ℤ)) hS.mem_Icc (u - 1) hsI
    exact hne.1 ((eq_of_modEq_of_mem_Icc hpI hzI (hfix.symm.trans hmod.symm)).trans hxu)

/-- The starts of `δ¹_t` and `δ³_t` have values `α < β`, and their wires keep their order after
time `t` as long as neither is at a fixed point. -/
private theorem positionMap_lt_of_dn_bridgeRev (hb : 1 ≤ b) (hS : IsBridgeSequence b f s)
    (γ : Fin b → Shade) {t : ℕ} (ht : 1 ≤ t ∧ t ≤ s.length) {xt : Fin b}
    (hxt : (xt : ℤ) + 1 = (pair s t).1) {y1 y3 : BridgeDart b s}
    (hy1 : y1.1 = .dn xt (prev s xt t)) (hy3 : y3.1 = .bridgeRev t) {s1 s3 : Fin b}
    (hs1 : y1 ∈ (bridgeGraph b s γ).oneWayTrip s1) (hs3 : y3 ∈ (bridgeGraph b s γ).oneWayTrip s3) :
    f ((s1 : ℤ) + 1) < f ((s3 : ℤ) + 1) ∧ ∀ τ, t ≤ τ →
      ¬IsFixedPointMod b (swapProduct b f s τ) (positionMap s τ ((s3 : ℤ) + 1)) →
      ¬IsFixedPointMod b (swapProduct b f s τ) (positionMap s τ ((s1 : ℤ) + 1)) →
      positionMap s τ ((s3 : ℤ) + 1) < positionMap s τ ((s1 : ℤ) + 1) := by
  have hI : ∀ x : Fin b, 1 ≤ (x : ℤ) + 1 ∧ (x : ℤ) + 1 ≤ b :=
    fun x => ⟨by omega, by have := x.isLt; omega⟩
  have hpt := isBridgePair_pair hS ht
  have hρ1 : positionMap s (t - 1) ((s1 : ℤ) + 1) = (pair s t).1 := by
    rw [start_dn hb hS γ (mem_heights.2 ⟨ht.1, ht.2, Or.inl hxt⟩) hy1 hs1,
      Equiv.apply_symm_apply, hxt]
  have hρ3 : positionMap s (t - 1) ((s3 : ℤ) + 1) = (pair s t).2 := by
    rw [start_bridgeRev hb hS γ ht hy3 hs3, Equiv.apply_symm_apply]
  have hαβ : f ((s1 : ℤ) + 1) < f ((s3 : ℤ) + 1) := by
    rw [← swapProduct_positionMap f hS.mem_Icc (t - 1) (hI s1),
      ← swapProduct_positionMap f hS.mem_Icc (t - 1) (hI s3), hρ1, hρ3]
    exact hpt.apply_lt_apply
  refine ⟨hαβ, fun τ hτ h3 h1 =>
    hS.positionMap_lt_positionMap (hI s3) (hI s1) hτ ?_ hαβ h3 h1⟩
  rw [positionMap_eq_swap ht, positionMap_eq_swap ht, hρ1, hρ3, Equiv.swap_apply_right,
    Equiv.swap_apply_left]
  exact hpt.lt

/-- In case 2 of the parallel digon, the end of the strand path along `δ³_t` cannot be the start
of `δ²_u` while the end of the one along `δ¹_t` is the start of `δ¹_u` or `δ³_u`. -/
private theorem false_of_dn_bridgeRev_of_up_right (hb : 1 ≤ b) (hf : IsBoundedAffinePerm a b f)
    (hS : IsBridgeSequence b f s) (γ : Fin b → Shade) {w : Finset (BridgeDart b s)}
    (hw : (bridgeGraph b s γ).IsCrossing w)
    {t : ℕ} (ht : 1 ≤ t ∧ t ≤ s.length) {xt : Fin b} (hxt : (xt : ℤ) + 1 = (pair s t).1)
    (htT : t < top s xt) {u : ℕ} (hu : 1 ≤ u ∧ u ≤ s.length) {xu : Fin b}
    (hxu : (xu : ℤ) + 1 = (pair s u).1) (huT : u < top s xu)
    (hiff : ∀ d : BridgeDart b s, (bridgeGraph b s γ).inv d ∈ w ↔
      (d.1 = .dn xu (prev s xu u) ∨ d.1 = .up xu (next s xu u) ∨ d.1 = .bridgeRev u))
    {y1 z3 : BridgeDart b s} {n1 : ℕ} (hn1 : 1 ≤ n1)
    (hleg1 : ∀ k, 1 ≤ k → k ≤ n1 →
      ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[k] y1))
    (hd1 : y1.1 = .dn xt (prev s xt t) ∨ y1.1 = .bridgeRev t)
    (h1 : ((bridgeGraph b s γ).tripMap^[n1] y1).1 = .dn xu (prev s xu u) ∨
      ((bridgeGraph b s γ).tripMap^[n1] y1).1 = .bridgeRev u)
    (h3 : z3.1 = .up xu (next s xu u)) {s1 s3 : Fin b}
    (hz1 : (bridgeGraph b s γ).tripMap^[n1] y1 ∈ (bridgeGraph b s γ).oneWayTrip s1)
    (hz3 : z3 ∈ (bridgeGraph b s γ).oneWayTrip s3) (hαβ : f ((s1 : ℤ) + 1) < f ((s3 : ℤ) + 1))
    (worder : t ≤ u - 1 →
      ¬IsFixedPointMod b (swapProduct b f s (u - 1)) (positionMap s (u - 1) ((s3 : ℤ) + 1)) →
      ¬IsFixedPointMod b (swapProduct b f s (u - 1)) (positionMap s (u - 1) ((s1 : ℤ) + 1)) →
      positionMap s (u - 1) ((s3 : ℤ) + 1) < positionMap s (u - 1) ((s1 : ℤ) + 1)) : False := by
  have hI : ∀ x : Fin b, 1 ≤ (x : ℤ) + 1 ∧ (x : ℤ) + 1 ≤ b :=
    fun x => ⟨by omega, by have := x.isLt; omega⟩
  have hpu := isBridgePair_pair hS hu
  obtain ⟨hv1, hv2, hv3⟩ := (hS.isBoundedAffinePerm_swapProduct hf (u - 1)).isBridgePair_values hpu
  have hfi := hpu.not_isFixedPointMod_left
  have hfj := hpu.not_isFixedPointMod_right
  have hij := hpu.lt
  obtain ⟨hne, hfU, hnf⟩ := up_props hb hf hS γ hw hu hxu huT hiff h3 hz3
  have htu := lt_of_iterate hb hS γ ht hxt htT hu.1 (x' := xu) hd1 hn1 hleg1 h1
  rcases h1 with h1 | h1
  · have hρD : positionMap s (u - 1) ((s1 : ℤ) + 1) = (pair s u).1 := by
      rw [start_dn hb hS γ (mem_heights.2 ⟨hu.1, hu.2, Or.inl hxu⟩) h1 hz1,
        Equiv.apply_symm_apply, hxu]
    have hwo := worder (by omega) hnf (by rwa [hρD])
    have hfD : f ((s1 : ℤ) + 1) = swapProduct b f s (u - 1) (pair s u).1 := by
      rw [← swapProduct_positionMap f hS.mem_Icc (u - 1) (hI s1), hρD]
    rcases hfU with hfU | hfU
    · omega
    · have := hS.le_positionMap_of_apply_eq_add hf (hI s3) (hI xu) hfU (u - 1)
      omega
  · have hρD : positionMap s (u - 1) ((s1 : ℤ) + 1) = (pair s u).2 := by
      rw [start_bridgeRev hb hS γ hu h1 hz1, Equiv.apply_symm_apply]
    have hwo := worder (by omega) hnf (by rwa [hρD])
    have hfD : f ((s1 : ℤ) + 1) = swapProduct b f s (u - 1) (pair s u).2 := by
      rw [← swapProduct_positionMap f hS.mem_Icc (u - 1) (hI s1), hρD]
    rcases hfU with hfU | hfU
    · omega
    · have := hS.le_positionMap_of_apply_eq_add hf (hI s3) (hI xu) hfU (u - 1)
      refine hnf (hpu.isFixedPointMod_of_lt_of_lt _ ?_ ?_)
      · have := hne.1
        omega
      · omega

/-- In case 2 of the parallel digon, the end of the strand path along `δ¹_t` cannot be the start
of `δ²_u` while the end of the one along `δ³_t` is the start of `δ¹_u` or `δ³_u`. -/
private theorem false_of_dn_bridgeRev_of_up_left (hb : 1 ≤ b) (hf : IsBoundedAffinePerm a b f)
    (hS : IsBridgeSequence b f s) (γ : Fin b → Shade) {w : Finset (BridgeDart b s)}
    (hw : (bridgeGraph b s γ).IsCrossing w)
    {t : ℕ} (ht : 1 ≤ t ∧ t ≤ s.length) {xt : Fin b} (hxt : (xt : ℤ) + 1 = (pair s t).1)
    (htT : t < top s xt) {u : ℕ} (hu : 1 ≤ u ∧ u ≤ s.length) {xu : Fin b}
    (hxu : (xu : ℤ) + 1 = (pair s u).1) (huT : u < top s xu)
    (hiff : ∀ d : BridgeDart b s, (bridgeGraph b s γ).inv d ∈ w ↔
      (d.1 = .dn xu (prev s xu u) ∨ d.1 = .up xu (next s xu u) ∨ d.1 = .bridgeRev u))
    {y3 z1 : BridgeDart b s} {n3 : ℕ} (hn3 : 1 ≤ n3)
    (hleg3 : ∀ k, 1 ≤ k → k ≤ n3 →
      ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[k] y3))
    (hd3 : y3.1 = .dn xt (prev s xt t) ∨ y3.1 = .bridgeRev t)
    (h3 : ((bridgeGraph b s γ).tripMap^[n3] y3).1 = .dn xu (prev s xu u) ∨
      ((bridgeGraph b s γ).tripMap^[n3] y3).1 = .bridgeRev u)
    (h1 : z1.1 = .up xu (next s xu u)) {s1 s3 : Fin b}
    (hz1 : z1 ∈ (bridgeGraph b s γ).oneWayTrip s1)
    (hz3 : (bridgeGraph b s γ).tripMap^[n3] y3 ∈ (bridgeGraph b s γ).oneWayTrip s3)
    (hαβ : f ((s1 : ℤ) + 1) < f ((s3 : ℤ) + 1))
    (worder : t ≤ u - 1 →
      ¬IsFixedPointMod b (swapProduct b f s (u - 1)) (positionMap s (u - 1) ((s3 : ℤ) + 1)) →
      ¬IsFixedPointMod b (swapProduct b f s (u - 1)) (positionMap s (u - 1) ((s1 : ℤ) + 1)) →
      positionMap s (u - 1) ((s3 : ℤ) + 1) < positionMap s (u - 1) ((s1 : ℤ) + 1)) : False := by
  have hI : ∀ x : Fin b, 1 ≤ (x : ℤ) + 1 ∧ (x : ℤ) + 1 ≤ b :=
    fun x => ⟨by omega, by have := x.isLt; omega⟩
  have hpu := isBridgePair_pair hS hu
  obtain ⟨hv1, hv2, hv3⟩ := (hS.isBoundedAffinePerm_swapProduct hf (u - 1)).isBridgePair_values hpu
  have hfi := hpu.not_isFixedPointMod_left
  have hfj := hpu.not_isFixedPointMod_right
  have hij := hpu.lt
  obtain ⟨-, hfU, hnf⟩ := up_props hb hf hS γ hw hu hxu huT hiff h1 hz1
  have htu := lt_of_iterate hb hS γ ht hxt htT hu.1 (x' := xu) hd3 hn3 hleg3 h3
  rcases h3 with h3 | h3
  · have hρD : positionMap s (u - 1) ((s3 : ℤ) + 1) = (pair s u).1 := by
      rw [start_dn hb hS γ (mem_heights.2 ⟨hu.1, hu.2, Or.inl hxu⟩) h3 hz3,
        Equiv.apply_symm_apply, hxu]
    have hwo := worder (by omega) (by rwa [hρD]) hnf
    have hfD : f ((s3 : ℤ) + 1) = swapProduct b f s (u - 1) (pair s u).1 := by
      rw [← swapProduct_positionMap f hS.mem_Icc (u - 1) (hI s3), hρD]
    rcases hfU with hfU | hfU
    · have := hS.positionMap_le_of_apply_eq hf (hI s1) (hI xu) hfU (u - 1)
      omega
    · omega
  · have hρD : positionMap s (u - 1) ((s3 : ℤ) + 1) = (pair s u).2 := by
      rw [start_bridgeRev hb hS γ hu h3 hz3, Equiv.apply_symm_apply]
    have hwo := worder (by omega) (by rwa [hρD]) hnf
    have hfD : f ((s3 : ℤ) + 1) = swapProduct b f s (u - 1) (pair s u).2 := by
      rw [← swapProduct_positionMap f hS.mem_Icc (u - 1) (hI s3), hρD]
    rcases hfU with hfU | hfU
    · have := hS.positionMap_le_of_apply_eq hf (hI s1) (hI xu) hfU (u - 1)
      omega
    · omega

/-- **Case 2** of the parallel digon: strand paths leaving `x_{W_t}` along `δ¹_t` and along `δ³_t`
cannot run to the same triple point `x_{W_u}` along different darts. -/
private theorem false_of_dn_bridgeRev (hb : 1 ≤ b) (hf : IsBoundedAffinePerm a b f)
    (hS : IsBridgeSequence b f s) (γ : Fin b → Shade) {w : Finset (BridgeDart b s)}
    (hw : (bridgeGraph b s γ).IsCrossing w)
    {t : ℕ} (ht : 1 ≤ t ∧ t ≤ s.length) {xt : Fin b} (hxt : (xt : ℤ) + 1 = (pair s t).1)
    (htT : t < top s xt) {u : ℕ} (hu : 1 ≤ u ∧ u ≤ s.length) {xu : Fin b}
    (hxu : (xu : ℤ) + 1 = (pair s u).1) (huT : u < top s xu)
    (hiff : ∀ d : BridgeDart b s, (bridgeGraph b s γ).inv d ∈ w ↔
      (d.1 = .dn xu (prev s xu u) ∨ d.1 = .up xu (next s xu u) ∨ d.1 = .bridgeRev u))
    {y1 y3 : BridgeDart b s} {n1 n3 : ℕ} (hn1 : 1 ≤ n1) (hn3 : 1 ≤ n3)
    (hleg1 : ∀ k, 1 ≤ k → k ≤ n1 →
      ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[k] y1))
    (hleg3 : ∀ k, 1 ≤ k → k ≤ n3 →
      ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[k] y3))
    (hy1 : y1.1 = .dn xt (prev s xt t)) (hy3 : y3.1 = .bridgeRev t)
    (hz1w : (bridgeGraph b s γ).inv ((bridgeGraph b s γ).tripMap^[n1] y1) ∈ w)
    (hz3w : (bridgeGraph b s γ).inv ((bridgeGraph b s γ).tripMap^[n3] y3) ∈ w)
    (hzz : (bridgeGraph b s γ).tripMap^[n1] y1 ≠ (bridgeGraph b s γ).tripMap^[n3] y3)
    {s1 s3 : Fin b} (hs1 : y1 ∈ (bridgeGraph b s γ).oneWayTrip s1)
    (hz1 : (bridgeGraph b s γ).tripMap^[n1] y1 ∈ (bridgeGraph b s γ).oneWayTrip s1)
    (hs3 : y3 ∈ (bridgeGraph b s γ).oneWayTrip s3)
    (hz3 : (bridgeGraph b s γ).tripMap^[n3] y3 ∈ (bridgeGraph b s γ).oneWayTrip s3) : False := by
  set G := bridgeGraph b s γ
  have hI : ∀ x : Fin b, 1 ≤ (x : ℤ) + 1 ∧ (x : ℤ) + 1 ≤ b :=
    fun x => ⟨by omega, by have := x.isLt; omega⟩
  have huP : u ∈ heights s xu := mem_heights.2 ⟨hu.1, hu.2, Or.inl hxu⟩
  have hpu := isBridgePair_pair hS hu
  -- the positions at `u - 1` of the starts of `δ¹_u` and `δ³_u`
  have hpos : ∀ (sx : Fin b) (z : BridgeDart b s), z ∈ G.oneWayTrip sx →
      (z.1 = .dn xu (prev s xu u) → positionMap s (u - 1) ((sx : ℤ) + 1) = (pair s u).1) ∧
      (z.1 = .bridgeRev u → positionMap s (u - 1) ((sx : ℤ) + 1) = (pair s u).2) := by
    intro sx z hz
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [start_dn hb hS γ huP h hz, Equiv.apply_symm_apply, hxu]
    · rw [start_bridgeRev hb hS γ hu h hz, Equiv.apply_symm_apply]
  obtain ⟨hαβ, hwo⟩ := positionMap_lt_of_dn_bridgeRev hb hS γ ht hxt hy1 hy3 hs1 hs3
  have worder := hwo (u - 1)
  obtain ⟨hv1, hv2, hv3⟩ := (hS.isBoundedAffinePerm_swapProduct hf (u - 1)).isBridgePair_values hpu
  have hfi := hpu.not_isFixedPointMod_left
  have hfj := hpu.not_isFixedPointMod_right
  have hij := hpu.lt
  rcases (hiff _).1 hz1w with h1 | h1 | h1 <;> rcases (hiff _).1 hz3w with h3 | h3 | h3
  · exact hzz (Subtype.ext (h1.trans h3.symm))
  · exact false_of_dn_bridgeRev_of_up_right hb hf hS γ hw ht hxt htT hu hxu huT hiff hn1 hleg1
      (Or.inl hy1) (Or.inl h1) h3 hz1 hz3 hαβ worder
  · -- `{z₁, z₃} = {δ¹_u, δ³_u}`, with `x₁` at `i_u`
    have hρ1' := (hpos s1 _ hz1).1 h1
    have hρ3' := (hpos s3 _ hz3).2 h3
    have htu := lt_of_iterate hb hS γ ht hxt htT hu.1 (x' := xu) (Or.inl hy1) hn1 hleg1
      (Or.inl h1)
    have := worder (by omega) (by rwa [hρ3']) (by rwa [hρ1'])
    omega
  · exact false_of_dn_bridgeRev_of_up_left hb hf hS γ hw ht hxt htT hu hxu huT hiff hn3 hleg3
      (Or.inr hy3) (Or.inl h3) h1 hz1 hz3 hαβ worder
  · exact hzz (Subtype.ext (h1.trans h3.symm))
  · exact false_of_dn_bridgeRev_of_up_left hb hf hS γ hw ht hxt htT hu hxu huT hiff hn3 hleg3
      (Or.inr hy3) (Or.inr h3) h1 hz1 hz3 hαβ worder
  · -- `{z₁, z₃} = {δ³_u, δ¹_u}`, with `x₃` at `i_u`: the values are in the wrong order
    have hρ1' := (hpos s1 _ hz1).2 h1
    have hρ3' := (hpos s3 _ hz3).1 h3
    have e1 := swapProduct_positionMap f hS.mem_Icc (u - 1) (hI s1)
    have e3 := swapProduct_positionMap f hS.mem_Icc (u - 1) (hI s3)
    rw [hρ1'] at e1
    rw [hρ3'] at e3
    have := hpu.apply_lt_apply
    omega
  · exact false_of_dn_bridgeRev_of_up_right hb hf hS γ hw ht hxt htT hu hxu huT hiff hn1 hleg1
      (Or.inl hy1) (Or.inr h1) h3 hz1 hz3 hαβ worder
  · exact hzz (Subtype.ext (h1.trans h3.symm))

/-- A stretch of a one-way trip of `G(s, γ)` passing no leg stays on that trip. -/
private theorem iterate_mem_oneWayTrip (hb : 1 ≤ b) (hS : IsBridgeSequence b f s)
    (γ : Fin b → Shade) {y : BridgeDart b s} {n : ℕ} {sy : Fin b}
    (hleg : ∀ k, 1 ≤ k → k ≤ n →
      ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[k] y))
    (hy : y ∈ (bridgeGraph b s γ).oneWayTrip sy) :
    (bridgeGraph b s γ).tripMap^[n] y ∈ (bridgeGraph b s γ).oneWayTrip sy := by
  obtain ⟨p, hp, hpn⟩ := (isPlabicGraph_bridgeGraph hb hS.forall_mem_bounds
    hS.isNestedPairSequence γ).exists_iterate_leg_eq_of_iterate_mem_oneWayTrip (x := y) (n := n)
      (j := 0) hleg (Nat.zero_le _) (by simpa using hy)
  exact mem_oneWayTrip.2 ⟨p + n, hpn, by rw [add_comm, Function.iterate_add_apply, hp]⟩

/-- **A bridge decomposition has no monogon.** Let `s` be a bridge sequence for `f : ℤ → ℤ` (with
`b ≥ 1`) and `γ : [1, b] → Shade`. Then the strand diagram `X°(G(s, γ), ∅)` of the bridge graph
has no monogon. -/
@[cluster_algebras "lem_bridge_no_monogon"]
theorem IsBridgeSequence.not_hasMonogon_strandDiagram_bridgeGraph (hb : 1 ≤ b)
    (hS : IsBridgeSequence b f s) (γ : Fin b → Shade) :
    ¬((bridgeGraph b s γ).strandDiagram
      (isPlabicGraph_bridgeGraph hb hS.forall_mem_bounds hS.isNestedPairSequence γ)
      (isWhiteDatum_empty_bridgeGraph γ)).HasMonogon := by
  set G := bridgeGraph b s γ
  have hG := isPlabicGraph_bridgeGraph hb hS.forall_mem_bounds hS.isNestedPairSequence γ
  have htri := card_eq_three (s := s) γ
  rintro ⟨P, hP⟩
  obtain ⟨w, hw, hwP⟩ := (bijOn_crossingTriplePoint htri hG).surjOn hP.pathStart_mem
  obtain ⟨y, y', hne, hy, hy', τ, hyτ, hy'τ⟩ :=
    (exists_isMonogon_iff hG htri hw).1 ⟨P, hP, hwP.symm⟩
  cases τ with
  | oneWay i =>
    refine hne (eq_of_inv_mem_of_mem_oneWayTrip hb hS γ hw ?_ ?_ hyτ hy'τ)
    · rw [← hy]
      exact G.self_mem_vertexOf _
    · rw [← hy']
      exact G.self_mem_vertexOf _
  | round O hO =>
    exact not_hasRoundtrip_bridgeGraph hS.forall_mem_bounds γ ⟨O, hO⟩

/-- **A bridge decomposition has no parallel digon.** Let `f` be an `(a, b)`-bounded affine
permutation (with `b ≥ 1`), `s` a bridge sequence for `f` and `γ : [1, b] → Shade`. Then the
strand diagram `X°(G(s, γ), ∅)` of the bridge graph has no parallel digon. -/
@[cluster_algebras "lem_bridge_no_parallel_digon"]
theorem IsBridgeSequence.not_hasParallelDigon_strandDiagram_bridgeGraph (hb : 1 ≤ b)
    (hf : IsBoundedAffinePerm a b f) (hS : IsBridgeSequence b f s) (γ : Fin b → Shade) :
    ¬((bridgeGraph b s γ).strandDiagram
      (isPlabicGraph_bridgeGraph hb hS.forall_mem_bounds hS.isNestedPairSequence γ)
      (isWhiteDatum_empty_bridgeGraph γ)).HasParallelDigon := by
  set G := bridgeGraph b s γ
  have hG := isPlabicGraph_bridgeGraph hb hS.forall_mem_bounds hS.isNestedPairSequence γ
  have htri := card_eq_three (s := s) γ
  rintro ⟨P, Q, xc, yc, hD⟩
  obtain ⟨wt, hwt, rfl⟩ := (bijOn_crossingTriplePoint htri hG).surjOn hD.mem_left
  obtain ⟨wu, hwu, rfl⟩ := (bijOn_crossingTriplePoint htri hG).surjOn hD.mem_right
  -- the stretches of trips followed by `P` and `Q`
  obtain ⟨yP, hyPB, nP, hnP, hlegP, hyPw, hzPw, hheadP, hlastP⟩ :=
    exists_of_isStrandPath hG htri hD.isStrandPath_fst hwt hwu hD.pathStart_fst hD.pathEnd_fst
  obtain ⟨yQ, hyQB, nQ, hnQ, hlegQ, hyQw, hzQw, hheadQ, hlastQ⟩ :=
    exists_of_isStrandPath hG htri hD.isStrandPath_snd hwt hwu hD.pathStart_snd hD.pathEnd_snd
  have hyy : yP ≠ yQ := fun h => hD.head?_ne
    (Option.map_injective Subtype.val_injective (by rw [hheadP, hheadQ, h]))
  have hinj : Function.Injective fun e : G.StrandDart (fun _ => ∅) =>
      ((G.strandDiagram hG (isWhiteDatum_empty htri)).inv e).1 :=
    fun e₁ e₂ he => (G.strandDiagram hG (isWhiteDatum_empty htri)).inv.injective (Subtype.ext he)
  have hzz : G.tripMap^[nP] yP ≠ G.tripMap^[nQ] yQ := fun h => hD.getLast?_ne
    (Option.map_injective hinj (by rw [hlastP, hlastQ, h]))
  -- their starts
  obtain ⟨sP, hsP⟩ := exists_mem_oneWayTrip hb hS γ hyPB
  obtain ⟨sQ, hsQ⟩ := exists_mem_oneWayTrip hb hS γ hyQB
  have hzP := iterate_mem_oneWayTrip hb hS γ hlegP hsP
  have hzQ := iterate_mem_oneWayTrip hb hS γ hlegQ hsQ
  -- the corners
  obtain ⟨t, xt, ht, hxt, htT, hifft, -⟩ := crossing_data hb hS γ hwt
  obtain ⟨u, xu, hu, hxu, huT, hiffu, -⟩ := crossing_data hb hS γ hwu
  have czP := (hiffu _).1 hzPw
  have czQ := (hiffu _).1 hzQw
  rcases (hifft yP).1 hyPw with hP | hP | hP <;> rcases (hifft yQ).1 hyQw with hQ | hQ | hQ
  · exact hyy (Subtype.ext (hP.trans hQ.symm))
  · exact false_of_up hb hS γ ht hxt htT hu hxu huT hnQ hnP hlegQ hlegP hQ (Or.inl hP) czQ czP
      hzz.symm hsQ hzQ
  · exact false_of_dn_bridgeRev hb hf hS γ hwu ht hxt htT hu hxu huT hiffu hnP hnQ hlegP hlegQ
      hP hQ hzPw hzQw hzz hsP hzP hsQ hzQ
  · exact false_of_up hb hS γ ht hxt htT hu hxu huT hnP hnQ hlegP hlegQ hP (Or.inl hQ) czP czQ
      hzz hsP hzP
  · exact hyy (Subtype.ext (hP.trans hQ.symm))
  · exact false_of_up hb hS γ ht hxt htT hu hxu huT hnP hnQ hlegP hlegQ hP (Or.inr hQ) czP czQ
      hzz hsP hzP
  · exact false_of_dn_bridgeRev hb hf hS γ hwu ht hxt htT hu hxu huT hiffu hnQ hnP hlegQ hlegP
      hQ hP hzQw hzPw hzz.symm hsQ hzQ hsP hzP
  · exact false_of_up hb hS γ ht hxt htT hu hxu huT hnQ hnP hlegQ hlegP hQ (Or.inr hP) czQ czP
      hzz.symm hsQ hzQ
  · exact hyy (Subtype.ext (hP.trans hQ.symm))

end ClusterAlgebras

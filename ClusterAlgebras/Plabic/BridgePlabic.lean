/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BridgeGraph
public import ClusterAlgebras.Plabic.CycleSpace
public import ClusterAlgebras.Plabic.Trips
public import ClusterAlgebras.Plabic.BridgeSequence
public import ClusterAlgebras.Plabic.Affinization

/-!
# The bridge graph is a plabic graph

Let `s = ((i₁, j₁), …, (i_r, j_r))` be a nested sequence of pairs with `1 ≤ i_t < j_t ≤ b` and
`γ : [1, b] → {white, black}`. The bridge graph `G(s, γ)` is a plabic graph with `b` boundary
vertices and `r + 1` faces: the face labelled `t ∈ [1, r]` lies just above the `t`-th bridge, and
the face labelled `0` is the bottom face. The faces are recognised by an invariant labelling
`Λ` of the darts, built from the label `Φ(y, τ)` of the region just below height `τ` between the
lines of `y` and `y + 1`: the least `t > τ` with `i_t ≤ y < j_t`, or `0` if there is none.

A trip running down a line crosses every bridge it meets and turns up at the foot of a line, so
the trip permutation of `G(s, γ)` is the product `τ_r ∘ ⋯ ∘ τ₁` of the transpositions
`τ_t = (i_t j_t)`, the first pair being applied first.

For a decorated permutation `π̃ = (π, ε)` and a bridge sequence `s` for its affinization, the
bridge decomposition `G(π̃, s)` is the bridge graph of `s` with the lollipop at a fixed point `x`
coloured `ε(x)`; it is a plabic graph, as bridge sequences are nested.

## Main definitions

* `ClusterAlgebras.BridgeGraph.regionLabel`: the region labels `Φ(y, τ)`.
* `ClusterAlgebras.BridgeSymbol.faceLabel`: the face labelling `Λ` of the darts.
* `ClusterAlgebras.DecoratedPerm.bridgeDecomposition`: the bridge decomposition `G(π̃, s)`.

## Main results

* `ClusterAlgebras.isPlabicGraph_bridgeGraph`: the bridge graph is a plabic graph.
* `ClusterAlgebras.card_faces_bridgeGraph`: it has `r + 1` faces.
* `ClusterAlgebras.tripMap_bridgeGraph_dn`, `tripMap_bridgeGraph_bridge`,
  `tripMap_bridgeGraph_bridgeRev`, `tripMap_bridgeGraph_up`, `tripMap_bridgeGraph_lollipop`: the
  trip map of the bridge graph.
* `ClusterAlgebras.tripPerm_bridgeGraph`: its trip permutation is `τ_r ∘ ⋯ ∘ τ₁`.
* `ClusterAlgebras.DecoratedPerm.isPlabicGraph_bridgeDecomposition`: a bridge decomposition is a
  plabic graph.

## Implementation notes

* **Labels.** As in the construction of the bridge graph, `x : Fin b` stands for the `1`-indexed
  label `x + 1`, while the entries of the pairs and the first argument `y` of `Φ(y, τ)` are
  `1`-indexed integers. So `Φ(x - 1, u)` for a line position `x` (in `1`-indexed labels) is
  `regionLabel s x u` for the Lean label `x`, and `Φ(x, u - 1)` is
  `regionLabel s (x + 1) (u - 1)`. The face label `∞` is `none`.
* **Counting.** Euler's relation is obtained from three invariant keys: a key of the vertices,
  onto a set of `b + ℓ₀ + 2r` values, a key of the edges, into a set of `b + ℓ₀ + 3r` values,
  and the face labelling, onto `r + 2` values (`ℓ₀` being the number of lollipop positions).
  They give `|V| ≥ b + ℓ₀ + 2r`, `|E| ≤ b + ℓ₀ + 3r` and `|Φ| ≥ r + 2`; with the bound
  `|V| - |E| + |Φ| ≤ 2` for connected rotation systems all three are equalities. This replaces
  the direct count of the darts in [FWZ].
* **Hypotheses.** [FWZ] assumes `b ≥ 1`, `1 ≤ i_t < j_t ≤ b` and that `s` is nested
  throughout. Nestedness is used only for the faces; the trip map and the trip permutation are
  computed without it. Being a plabic graph needs `b ≥ 1`, which is part of the definition of
  the bridge graph and of a plabic graph in [FWZ].
* **The trip permutation.** The composite `τ_r ∘ ⋯ ∘ τ₁` is the position map `positionMap s r`,
  a permutation of `ℤ` preserving `[1, b]`; the statement compares it with the trip permutation
  through the label shift `x ↦ x + 1`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160, Section 7.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Generalities on orbits -/

section Orbits

variable {α : Type*}

/-- A function invariant under a permutation is constant on its cycles. -/
private theorem eq_of_sameCycle_of_apply_eq {β : Type*} [Finite α] {g : Equiv.Perm α}
    {f : α → β} (hf : ∀ a, f (g a) = f a) {a a' : α} (h : g.SameCycle a a') : f a = f a' := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hf, ih]

/-- If `g a = g a'` implies `f a = f a'`, the image of `f` is no larger than that of `g`. -/
private theorem card_image_le_card_image_of_factor {β γ : Type*} [Fintype α] [DecidableEq β]
    [DecidableEq γ] {f : α → β} {g : α → γ} (h : ∀ a a', g a = g a' → f a = f a') :
    (univ.image f).card ≤ (univ.image g).card := by
  classical
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
  · simp [univ_eq_empty]
  · let k : γ → β := fun c => if hc : ∃ a, g a = c then f hc.choose else f a₀
    calc (univ.image f).card ≤ ((univ.image g).image k).card := by
          apply card_le_card
          intro y hy
          obtain ⟨a, -, rfl⟩ := mem_image.1 hy
          have hc : ∃ a', g a' = g a := ⟨a, rfl⟩
          refine mem_image.2 ⟨g a, mem_image_of_mem _ (mem_univ _), ?_⟩
          simp only [k, dif_pos hc]
          exact h _ _ hc.choose_spec
      _ ≤ _ := card_image_le

/-- The vertex of a dart fixed by the cube of the rotation consists of the dart and its first two
images. -/
private theorem vertexOf_eq_of_rot_rot_rot [Fintype α] [DecidableEq α]
    (R : RotationSystem α) {d : α} (h : R.rot (R.rot (R.rot d)) = d) :
    R.vertexOf d = {d, R.rot d, R.rot (R.rot d)} := by
  ext e
  rw [RotationSystem.mem_vertexOf]
  constructor
  · intro he
    obtain ⟨n, rfl⟩ := he.exists_nat_pow_eq
    clear he
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      simp only [mem_insert, mem_singleton] at ih ⊢
      rcases ih with h' | h' | h' <;> rw [h'] <;> simp [h]
  · intro he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact .refl _ _
    · exact Equiv.Perm.sameCycle_apply_right.2 (.refl _ _)
    · exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.sameCycle_apply_right.2 (.refl _ _))

end Orbits

/-- The value of `finRotate b x` is `x + 1` modulo `b`. -/
private theorem val_finRotate {b : ℕ} (x : Fin b) :
    ((finRotate b x : Fin b) : ℕ) = if (x : ℕ) + 1 = b then 0 else (x : ℕ) + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by have := x.isLt; omega⟩
  rw [finRotate_apply, Fin.val_add_one]
  grind [Fin.ext_iff]

/-! ### Region labels -/

namespace BridgeGraph

variable {b : ℕ} {s : List (ℤ × ℤ)}

/-- For `1 ≤ t ≤ r`, the `t`-th pair of `s` is a member of `s`. -/
theorem pair_mem {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ s.length) : pair s t ∈ s := by
  rw [pair_eq_getElem h1 h2]
  exact List.getElem_mem _

/-- If every pair `(i, j)` of `s` satisfies `1 ≤ i < j ≤ b`, then `1 ≤ i_t < j_t ≤ b` for every
`t ∈ [1, r]`. -/
theorem pair_bounds (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) {t : ℕ} (h1 : 1 ≤ t)
    (h2 : t ≤ s.length) : 1 ≤ (pair s t).1 ∧ (pair s t).1 < (pair s t).2 ∧ (pair s t).2 ≤ b :=
  hs _ (pair_mem h1 h2)

/-- Nestedness, with `1`-indexed pairs: no later pair has an entry strictly between the entries of
an earlier one. -/
theorem ne_pair_of_isNestedPairSequence (hn : IsNestedPairSequence s) {t t' : ℕ} (h1 : 1 ≤ t)
    (htt' : t < t') (ht' : t' ≤ s.length) {h : ℤ} (hl : (pair s t).1 < h)
    (hr : h < (pair s t).2) : h ≠ (pair s t').1 ∧ h ≠ (pair s t').2 := by
  have := (isNestedPairSequence_iff.1 hn) (t - 1) (t' - 1) (by omega) (by omega) (by omega) h
  rw [pair_eq_getElem h1 (by omega)] at hl hr
  rw [pair_eq_getElem (by omega) ht']
  exact this hl hr

/-- A height that is not in `P_x` is not the height of a bridge ending on the line of `x`. -/
theorem ne_of_notMem_heights {x : Fin b} {t : ℕ} (h : t ∉ heights s x) (h1 : 1 ≤ t)
    (h2 : t ≤ s.length) : (x : ℤ) + 1 ≠ (pair s t).1 ∧ (x : ℤ) + 1 ≠ (pair s t).2 := by
  rw [mem_heights] at h
  exact ⟨fun e => h ⟨h1, h2, Or.inl e⟩, fun e => h ⟨h1, h2, Or.inr e⟩⟩

/-- A height above `m_x` is not in `P_x`. -/
theorem notMem_heights_of_top_lt {x : Fin b} {t : ℕ} (h : top s x < t) : t ∉ heights s x :=
  fun ht => absurd (le_top ht) (by omega)

/-- The end of the `t`-th pair on the line of `x` is the right one when it is not the left one. -/
theorem eq_snd_of_mem_heights {x : Fin b} {t : ℕ} (ht : t ∈ heights s x)
    (hx : (x : ℤ) + 1 ≠ (pair s t).1) : (x : ℤ) + 1 = (pair s t).2 :=
  (mem_heights.1 ht).2.2.resolve_left hx

/-- Two labels on whose lines the `t`-th bridge has an end on the same side are equal. -/
theorem eq_of_mem_heights_of_iff {x x' : Fin b} {t : ℕ} (hx : t ∈ heights s x)
    (hx' : t ∈ heights s x')
    (h : (x : ℤ) + 1 = (pair s t).1 ↔ (x' : ℤ) + 1 = (pair s t).1) : x = x' := by
  grind [mem_heights]

/-- The greatest element of `{0} ∪ P_x` at most `τ + 1` is `τ + 1` when `τ + 1 ∈ P_x`. -/
theorem prev_succ_of_mem {x : Fin b} {τ : ℕ} (h : τ + 1 ∈ heights s x) :
    prev s x (τ + 1 + 1) = τ + 1 :=
  le_antisymm (by have := prev_lt (s := s) (x := x) (u := τ + 1 + 1) (by omega); omega)
    (le_prev h (by omega))

/-- The greatest element of `{0} ∪ P_x` at most `τ` does not change at a height `τ + 1 ∉ P_x`. -/
theorem prev_succ_of_notMem {x : Fin b} {τ : ℕ} (h : τ + 1 ∉ heights s x) :
    prev s x (τ + 1 + 1) = prev s x (τ + 1) := by
  unfold prev
  congr 1
  ext t
  simp only [mem_filter]
  refine ⟨fun ⟨ht, hlt⟩ => ⟨ht, lt_of_le_of_ne (by omega) fun e => h (e ▸ ht)⟩,
    fun ⟨ht, hlt⟩ => ⟨ht, by omega⟩⟩

/-- The label `Φ(y, τ)` of the region just below height `τ` between the lines of the `1`-indexed
labels `y` and `y + 1`: the least `t ∈ [1, r]` with `t > τ` and `i_t ≤ y < j_t` (the bridge
closing the region from below), or `0` if there is none (the bottom region). -/
def regionLabel (s : List (ℤ × ℤ)) (y : ℤ) (τ : ℕ) : ℕ :=
  if h : ∃ t < s.length + 1, τ < t ∧ (pair s t).1 ≤ y ∧ y < (pair s t).2 then Nat.find h else 0

/-- Two region labels agree when the same bridges count for them. -/
theorem regionLabel_congr {y y' : ℤ} {τ τ' : ℕ}
    (h : ∀ t, (τ < t ∧ t ≤ s.length ∧ (pair s t).1 ≤ y ∧ y < (pair s t).2) ↔
      (τ' < t ∧ t ≤ s.length ∧ (pair s t).1 ≤ y' ∧ y' < (pair s t).2)) :
    regionLabel s y τ = regionLabel s y' τ' := by
  have h' : ∀ t, (t < s.length + 1 ∧ τ < t ∧ (pair s t).1 ≤ y ∧ y < (pair s t).2) ↔
      (t < s.length + 1 ∧ τ' < t ∧ (pair s t).1 ≤ y' ∧ y' < (pair s t).2) := fun t => by
    grind
  unfold regionLabel
  by_cases hP : ∃ t < s.length + 1, τ < t ∧ (pair s t).1 ≤ y ∧ y < (pair s t).2
  · have hQ : ∃ t < s.length + 1, τ' < t ∧ (pair s t).1 ≤ y' ∧ y' < (pair s t).2 :=
      (exists_congr h').1 hP
    rw [dif_pos hP, dif_pos hQ]
    exact le_antisymm (Nat.find_min' hP ((h' _).2 (Nat.find_spec hQ)))
      (Nat.find_min' hQ ((h' _).1 (Nat.find_spec hP)))
  · rw [dif_neg hP, dif_neg (fun hQ => hP ((exists_congr h').2 hQ))]

/-- `Φ(y, t - 1) = t` when `i_t ≤ y < j_t`. -/
theorem regionLabel_pred_of_spans {y : ℤ} {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ s.length)
    (hc : (pair s t).1 ≤ y ∧ y < (pair s t).2) : regionLabel s y (t - 1) = t := by
  have hP : ∃ t' < s.length + 1, t - 1 < t' ∧ (pair s t').1 ≤ y ∧ y < (pair s t').2 :=
    ⟨t, by omega, by omega, hc⟩
  rw [regionLabel, dif_pos hP]
  apply le_antisymm (Nat.find_min' hP ⟨by omega, by omega, hc⟩)
  have := (Nat.find_spec hP).2.1
  omega

/-- `Φ(y, t - 1) = Φ(y, t)` unless `i_t ≤ y < j_t`. -/
theorem regionLabel_pred_of_not_spans {y : ℤ} {t : ℕ} (h1 : 1 ≤ t)
    (hc : ¬((pair s t).1 ≤ y ∧ y < (pair s t).2)) :
    regionLabel s y (t - 1) = regionLabel s y t := by
  apply regionLabel_congr
  grind

/-- `Φ(y - 1, τ) = Φ(y, τ)` when `y` lies in no pair after the `τ`-th. -/
theorem regionLabel_sub_one {y : ℤ} {τ : ℕ}
    (h : ∀ t, τ < t → t ≤ s.length → y ≠ (pair s t).1 ∧ y ≠ (pair s t).2) :
    regionLabel s (y - 1) τ = regionLabel s y τ := by
  apply regionLabel_congr
  grind

/-- `Φ(y + 1, τ) = Φ(y, τ)` when `y + 1` lies in no pair after the `τ`-th. -/
theorem regionLabel_add_one {y : ℤ} {τ : ℕ}
    (h : ∀ t, τ < t → t ≤ s.length → y + 1 ≠ (pair s t).1 ∧ y + 1 ≠ (pair s t).2) :
    regionLabel s (y + 1) τ = regionLabel s y τ := by
  simpa using (regionLabel_sub_one h).symm

/-- `Φ(y, τ) = Φ(y, τ')` when no bridge of height in `(τ, τ']` spans `y`. -/
theorem regionLabel_eq_of_gap {y : ℤ} {τ τ' : ℕ} (hle : τ ≤ τ')
    (h : ∀ t, τ < t → t ≤ τ' → t ≤ s.length → ¬((pair s t).1 ≤ y ∧ y < (pair s t).2)) :
    regionLabel s y τ = regionLabel s y τ' := by
  apply regionLabel_congr
  grind

/-- `Φ(0, τ) = 0`. -/
theorem regionLabel_zero (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (τ : ℕ) :
    regionLabel s 0 τ = 0 := by
  rw [regionLabel, dif_neg]
  rintro ⟨t, h2, h1, h3, h4⟩
  have := pair_bounds hs (t := t) (by omega) (by omega)
  omega

/-- `Φ(b, τ) = 0`. -/
theorem regionLabel_card (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (τ : ℕ) :
    regionLabel s b τ = 0 := by
  rw [regionLabel, dif_neg]
  rintro ⟨t, h2, h1, h3, h4⟩
  have := pair_bounds hs (t := t) (by omega) (by omega)
  omega

/-- The region to the right of the line of the label `x + 1` modulo `b`: `Φ(x + 1, τ)`, read
modulo `b` (for `x + 1 = b` both sides are `0`). -/
theorem regionLabel_finRotate (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (x : Fin b)
    (τ : ℕ) : regionLabel s (finRotate b x : ℤ) τ = regionLabel s ((x : ℤ) + 1) τ := by
  have hv := val_finRotate x
  split_ifs at hv with h
  · have e1 : ((finRotate b x : ℕ) : ℤ) = 0 := by exact_mod_cast hv
    have e2 : (x : ℤ) + 1 = b := by exact_mod_cast h
    rw [e1, e2, regionLabel_zero hs, regionLabel_card hs]
  · have e1 : ((finRotate b x : ℕ) : ℤ) = (x : ℤ) + 1 := by exact_mod_cast hv
    rw [e1]

/-- For a nested sequence `s` and a segment of the line of `x` from the height `u` to
`u' = nx_x(u)`, `Φ(y, u) = Φ(y, u' - 1)` for `y = x` and `y = x + 1`: no bridge of height in
`(u, u')` spans these `y`. -/
theorem regionLabel_next (hn : IsNestedPairSequence s) {x : Fin b} {u : ℕ}
    (hut : u < top s x) {y : ℤ} (hy : y = x ∨ y = (x : ℤ) + 1) :
    regionLabel s y u = regionLabel s y (next s x u - 1) := by
  have hlt := lt_next hut
  have hm := next_mem hut
  have hmr := le_length_of_mem_heights hm
  apply regionLabel_eq_of_gap (by omega)
  intro t ht1 ht2 htr hc
  have htP : t ∉ heights s x := fun h => by have := next_le h ht1; omega
  obtain ⟨e1, e2⟩ := ne_of_notMem_heights htP (by omega) htr
  have hin : (pair s t).1 < (x : ℤ) + 1 ∧ (x : ℤ) + 1 < (pair s t).2 := by
    rcases hy with rfl | rfl <;> omega
  have := ne_pair_of_isNestedPairSequence hn (by omega) (show t < next s x u by omega) hmr
    hin.1 hin.2
  exact (mem_heights.1 hm).2.2.elim this.1 this.2

/-- For a nested sequence `s`, `Φ(i_t, t) = Φ(j_t - 1, t)`. -/
theorem regionLabel_fst_eq (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (hn : IsNestedPairSequence s) {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ s.length) :
    regionLabel s (pair s t).1 t = regionLabel s ((pair s t).2 - 1) t := by
  have hb := pair_bounds hs h1 h2
  have key : ∀ t', t < t' → t' ≤ s.length →
      ¬((pair s t).1 < (pair s t').1 ∧ (pair s t').1 < (pair s t).2) ∧
        ¬((pair s t).1 < (pair s t').2 ∧ (pair s t').2 < (pair s t).2) := fun t' h h' =>
    ⟨fun ⟨a, c⟩ => (ne_pair_of_isNestedPairSequence hn h1 h h' a c).1 rfl,
      fun ⟨a, c⟩ => (ne_pair_of_isNestedPairSequence hn h1 h h' a c).2 rfl⟩
  apply regionLabel_congr
  intro t'
  constructor <;> rintro ⟨ha, hb', hc1, hc2⟩ <;> obtain ⟨k1, k2⟩ := key t' ha hb' <;>
    exact ⟨ha, hb', by omega, by omega⟩

end BridgeGraph

/-! ### Keys of darts -/

namespace BridgeSymbol

open BridgeGraph

variable {b : ℕ} {s : List (ℤ × ℤ)}

/-- The **face labelling** `Λ` of the darts of the bridge graph, with values in
`{∞} ∪ [0, r]` (`∞` being `none`): `Λ(e_x) = ∞`, `Λ(ē_x) = Λ(λ_x) = Φ(x - 1, 0)`,
`Λ(dn_{x,u}) = Φ(x - 1, u)`, `Λ(up_{x,u}) = Φ(x, u - 1)`, `Λ(c_t) = Φ(j_t - 1, t)` and
`Λ(c̄_t) = t`, in `1`-indexed labels. -/
def faceLabel (s : List (ℤ × ℤ)) : BridgeSymbol b → Option ℕ
  | .bdry _ => none
  | .bdryRev x => some (regionLabel s (x : ℤ) 0)
  | .lam x => some (regionLabel s (x : ℤ) 0)
  | .dn x u => some (regionLabel s (x : ℤ) u)
  | .up x u => some (regionLabel s ((x : ℤ) + 1) (u - 1))
  | .bridge t => some (regionLabel s ((pair s t).2 - 1) t)
  | .bridgeRev t => some t

/-- The key of the end of the `u`-th bridge on the line of `x`: its white end if `x + 1 = i_u`,
its black end otherwise. -/
def endKey (s : List (ℤ × ℤ)) (x : Fin b) (u : ℕ) : Fin b ⊕ Fin b ⊕ ℕ ⊕ ℕ :=
  if (x : ℤ) + 1 = (pair s u).1 then .inr (.inr (.inl u)) else .inr (.inr (.inr u))

/-- The key of the vertex of a dart of the bridge graph: `inl x` for the boundary vertex `x`,
`inr (inl x)` for the lollipop at `x`, and the white or black end of the `t`-th bridge. -/
def vertexKey (s : List (ℤ × ℤ)) : BridgeSymbol b → Fin b ⊕ Fin b ⊕ ℕ ⊕ ℕ
  | .bdry x => .inl x
  | .bdryRev y => .inl ((finRotate b).symm y)
  | .lam x => .inr (.inl x)
  | .dn x u => if u = 0 then .inl x else endKey s x u
  | .up x u => endKey s x u
  | .bridge t => .inr (.inr (.inl t))
  | .bridgeRev t => .inr (.inr (.inr t))

/-- The key of the edge of a dart of the bridge graph: the boundary edge `x`, the lollipop edge
at `x`, the `t`-th bridge, or the segment of a line just above the end of the `u`-th bridge on
it, recorded by `u` and the side of that end. -/
def edgeKey (s : List (ℤ × ℤ)) : BridgeSymbol b → Fin b ⊕ Fin b ⊕ ℕ ⊕ (ℕ × Bool)
  | .bdry x => .inl x
  | .bdryRev x => .inl x
  | .lam x => .inr (.inl x)
  | .dn x u =>
    if u < top s x then
      .inr (.inr (.inr (next s x u, decide ((x : ℤ) + 1 = (pair s (next s x u)).1))))
    else .inr (.inl x)
  | .up x u => .inr (.inr (.inr (u, decide ((x : ℤ) + 1 = (pair s u).1))))
  | .bridge t => .inr (.inr (.inl t))
  | .bridgeRev t => .inr (.inr (.inl t))

/-- The vertex key is invariant under the rotation. -/
theorem vertexKey_rotate {d : BridgeSymbol b} (hd : IsDart s d) :
    vertexKey s (d.rotate s) = vertexKey s d := by
  cases d with
  | bdry x => simp [vertexKey]
  | bdryRev y => rfl
  | lam x => rfl
  | dn x u =>
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · simp only [rotate_dn_zero, vertexKey, Equiv.symm_apply_apply, ↓reduceIte]
    · rw [rotate_dn_of_ne_zero hu.ne']
      by_cases h : (x : ℤ) + 1 = (pair s u).1 <;> simp [h, vertexKey, endKey, hu.ne']
  | up x u =>
    have hu := pos_of_mem_heights hd
    rw [rotate_up]
    by_cases h : (x : ℤ) + 1 = (pair s u).1
    · by_cases h' : u < top s x <;> simp [h, h', vertexKey, endKey, hu.ne']
    · simp [h, vertexKey, endKey]
  | bridge t =>
    simp only [rotate]
    split
    · next x hx => simp [vertexKey, endKey, leftEnd_eq_some.1 hx]
    · rfl
  | bridgeRev t =>
    simp only [rotate]
    split
    · next y hy =>
      obtain ⟨h1, h2⟩ := rightEnd_eq_some.1 hy
      have ht : t ≠ 0 := by have := hd.1; omega
      split_ifs <;> simp [vertexKey, endKey, h2, ht]
    · rfl

/-- The colour is invariant under the rotation, at every dart. -/
theorem colour_rotate (γ : Fin b → Shade) {d : BridgeSymbol b} (hd : IsDart s d) :
    colour s γ (d.rotate s) = colour s γ d := by
  cases d with
  | bdry x => simp [colour]
  | bdryRev y => rfl
  | lam x => rfl
  | dn x u =>
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · simp [colour]
    · rw [rotate_dn_of_ne_zero hu.ne', colour_dn_of_ne_zero γ hu.ne']
      by_cases h : (x : ℤ) + 1 = (pair s u).1 <;> simp [h, colour_up]
  | up x u =>
    have hu := pos_of_mem_heights hd
    rw [rotate_up, colour_up]
    by_cases h : (x : ℤ) + 1 = (pair s u).1
    · by_cases h' : u < top s x <;> simp [h, h', colour_dn_of_ne_zero γ hu.ne']
    · simp [h]
  | bridge t =>
    simp only [rotate]
    split
    · next x hx => simp [colour_up, leftEnd_eq_some.1 hx]
    · rfl
  | bridgeRev t =>
    simp only [rotate]
    split
    · next y hy =>
      obtain ⟨h1, h2⟩ := rightEnd_eq_some.1 hy
      have ht : t ≠ 0 := by have := hd.1; omega
      split_ifs <;> simp [colour_up, colour_dn_of_ne_zero γ ht, h2]
    · rfl

/-- For a nested sequence `s`, the face labelling is invariant under the face permutation
`φ(d) = σ(d̄)`. -/
theorem faceLabel_rotate_reverse (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (hn : IsNestedPairSequence s) {d : BridgeSymbol b} (hd : IsDart s d) :
    faceLabel s ((d.reverse s).rotate s) = faceLabel s d := by
  cases d with
  | bdry x => rfl
  | bdryRev x => rfl
  | lam x =>
    simp only [reverse_lam, rotate_dn_zero, faceLabel, Option.some.injEq]
    rw [regionLabel_finRotate hs]
    exact regionLabel_add_one fun t ht htr =>
      ne_of_notMem_heights (by rw [isDart_lam.1 hd]; exact notMem_empty t) (by omega) htr
  | dn x u =>
    by_cases hut : u < top s x
    · rw [reverse_dn_of_lt_top hut, rotate_up]
      have hm := next_mem hut
      have hlt := lt_next hut
      have h1 := pos_of_mem_heights hm
      have h2 := le_length_of_mem_heights hm
      have hb := pair_bounds hs h1 h2
      have hF2 := regionLabel_next hn hut (Or.inl rfl)
      split_ifs with hleft htop
      · simp only [faceLabel, Option.some.injEq]
        rw [hF2, regionLabel_pred_of_not_spans h1 (by omega)]
      · simp only [faceLabel, Option.some.injEq]
        have htop' : next s x u = top s x := le_antisymm (le_top hm) (not_lt.1 htop)
        rw [hF2, regionLabel_pred_of_not_spans h1 (by omega), ← regionLabel_fst_eq hs hn h1 h2,
          ← hleft]
        exact regionLabel_add_one
          fun t ht htr => ne_of_notMem_heights (notMem_heights_of_top_lt (by omega)) (by omega) htr
      · have hright := eq_snd_of_mem_heights hm hleft
        simp only [faceLabel, Option.some.injEq]
        rw [hF2, regionLabel_pred_of_spans h1 h2 (by omega)]
    · obtain rfl : u = 0 := hd.resolve_right fun h => hut h.2
      simp [reverse_dn, hut, faceLabel]
  | up x u' =>
    have hut := prev_lt_top hd
    have hu := prev_eq_zero_or_mem x u' (s := s)
    have hnx : next s x (prev s x u') = u' := next_prev hd
    have hF2 := regionLabel_next hn hut (Or.inr rfl)
    rw [hnx] at hF2
    rw [reverse_up]
    simp only [faceLabel]
    rcases eq_or_ne (prev s x u') 0 with h0 | h0
    · rw [h0, rotate_dn_zero]
      simp only [Option.some.injEq]
      rw [regionLabel_finRotate hs, ← hF2, h0]
    · have hmem := hu.resolve_left h0
      have h1 := pos_of_mem_heights hmem
      have h2 := le_length_of_mem_heights hmem
      have hb := pair_bounds hs h1 h2
      rw [rotate_dn_of_ne_zero h0]
      split_ifs with hleft
      · simp only [Option.some.injEq]
        rw [← hF2, ← regionLabel_fst_eq hs hn h1 h2, hleft]
      · have hright := eq_snd_of_mem_heights hmem hleft
        simp only [Option.some.injEq]
        rw [← hF2, regionLabel_pred_of_not_spans h1 (by omega)]
  | bridge t =>
    obtain ⟨x, y, hx, hy, hxy, htx, hty⟩ := exists_ends hs hd.1 hd.2
    have hb := pair_bounds hs hd.1 hd.2
    rw [reverse_bridge, rotate_bridgeRev_of_eq hy (by omega)]
    have hy' : (pair s t).2 - 1 = (y : ℤ) := by omega
    split_ifs with htop
    · simp only [faceLabel, hy']
    · simp only [faceLabel, Option.some.injEq, hy']
      rw [regionLabel_pred_of_not_spans hd.1 (by omega)]
      have htop' : t = top s y := le_antisymm (le_top hty) (not_lt.1 htop)
      exact regionLabel_add_one
        fun t' ht htr => ne_of_notMem_heights (notMem_heights_of_top_lt (by omega)) (by omega) htr
  | bridgeRev t =>
    obtain ⟨x, y, hx, hy, hxy, htx, hty⟩ := exists_ends hs hd.1 hd.2
    have hb := pair_bounds hs hd.1 hd.2
    rw [reverse_bridgeRev, rotate_bridge_of_eq hx]
    simp only [faceLabel, Option.some.injEq]
    exact regionLabel_pred_of_spans hd.1 hd.2 (by omega)

/-- A dart is *primary* if it is a boundary arc `e_x`, a lollipop dart, a dart `up_{x,u}` or a
bridge `c_t`: every edge has exactly one primary dart. -/
private def IsPrimary : BridgeSymbol b → Prop
  | .bdry _ => True
  | .lam _ => True
  | .up _ _ => True
  | .bridge _ => True
  | _ => False

/-- Every dart is a primary dart or the reverse of one. -/
private theorem exists_isPrimary {d : BridgeSymbol b} (hd : IsDart s d) :
    ∃ e, IsDart s e ∧ IsPrimary e ∧ (d = e ∨ d = reverse s e) := by
  cases d with
  | bdry x => exact ⟨_, hd, trivial, Or.inl rfl⟩
  | bdryRev x => exact ⟨.bdry x, trivial, trivial, Or.inr rfl⟩
  | lam x => exact ⟨_, hd, trivial, Or.inl rfl⟩
  | dn x u =>
    by_cases hut : u < top s x
    · have hu : u = 0 ∨ u ∈ heights s x := hd.imp_right And.left
      refine ⟨.up x (next s x u), next_mem hut, trivial, Or.inr ?_⟩
      rw [reverse_up, prev_next hu hut]
    · obtain rfl : u = 0 := hd.resolve_right fun h => hut h.2
      exact ⟨.lam x, top_eq_zero_iff.1 (by omega), trivial, Or.inr rfl⟩
  | up x u => exact ⟨_, hd, trivial, Or.inl rfl⟩
  | bridge t => exact ⟨_, hd, trivial, Or.inl rfl⟩
  | bridgeRev t => exact ⟨.bridge t, hd, trivial, Or.inr rfl⟩

/-- The edge key is invariant under the involution. -/
private theorem edgeKey_reverse {d : BridgeSymbol b} (hd : IsDart s d) :
    edgeKey s (d.reverse s) = edgeKey s d := by
  cases d with
  | bdry x => rfl
  | bdryRev x => rfl
  | lam x =>
    have h0 : top s x = 0 := top_eq_zero_iff.2 hd
    simp [edgeKey, h0]
  | dn x u =>
    rw [reverse_dn]
    split_ifs with hut <;> simp [edgeKey, hut]
  | up x u =>
    rw [reverse_up]
    simp [edgeKey, prev_lt_top hd, next_prev hd]
  | bridge t => rfl
  | bridgeRev t => rfl

/-- Primary darts with the same edge key are equal. -/
private theorem eq_of_isPrimary {d e : BridgeSymbol b} (hd : IsDart s d) (he : IsDart s e)
    (hpd : IsPrimary d) (hpe : IsPrimary e) (h : edgeKey s d = edgeKey s e) : d = e := by
  cases d with
  | up x u =>
    cases e with
    | up x' u' =>
      simp only [edgeKey, Sum.inr.injEq, Prod.mk.injEq, decide_eq_decide] at h
      obtain ⟨rfl, h⟩ := h
      rw [eq_of_mem_heights_of_iff hd he h]
    | _ => simp_all [IsPrimary, edgeKey]
  | _ => cases e <;> simp_all [IsPrimary, edgeKey]

/-- Two darts with the same edge key are equal or reverse to each other. -/
theorem eq_or_eq_reverse_of_edgeKey_eq {d e : BridgeSymbol b} (hd : IsDart s d)
    (he : IsDart s e) (h : edgeKey s d = edgeKey s e) : e = d ∨ e = reverse s d := by
  obtain ⟨d₀, hd₀, hpd, hdd⟩ := exists_isPrimary hd
  obtain ⟨e₀, he₀, hpe, hee⟩ := exists_isPrimary he
  have kd : edgeKey s d = edgeKey s d₀ := by
    rcases hdd with rfl | rfl
    · rfl
    · exact edgeKey_reverse hd₀
  have ke : edgeKey s e = edgeKey s e₀ := by
    rcases hee with rfl | rfl
    · rfl
    · exact edgeKey_reverse he₀
  obtain rfl := eq_of_isPrimary hd₀ he₀ hpd hpe (kd.symm.trans (h.trans ke))
  rcases hdd with rfl | rfl
  · exact hee
  · rw [reverse_reverse hd₀]
    exact hee.symm

end BridgeSymbol

/-! ### The bridge graph is a plabic graph -/

open BridgeGraph BridgeSymbol

section Plabic

variable {b : ℕ} {s : List (ℤ × ℤ)}

/-- The boundary arcs of the bridge graph are reached from `e_1`, for any rotation system acting on
the darts by the bridge graph's rotation and involution. -/
private theorem reach_bdry_bridgeGraph (hb : 1 ≤ b) (R : RotationSystem (BridgeDart b s))
    (hrot : ∀ (d : BridgeSymbol b) (hd : IsDart s d), (R.rot ⟨d, hd⟩).1 = d.rotate s)
    (hinv : ∀ (d : BridgeSymbol b) (hd : IsDart s d), (R.inv ⟨d, hd⟩).1 = d.reverse s)
    (x : Fin b) : R.Reach ⟨.bdry ⟨0, hb⟩, trivial⟩ ⟨.bdry x, trivial⟩ := by
  have step : ∀ x : Fin b, R.Reach ⟨.bdry ⟨0, hb⟩, trivial⟩ ⟨.bdry x, trivial⟩ →
      R.Reach ⟨.bdry ⟨0, hb⟩, trivial⟩ ⟨.bdry (finRotate b x), trivial⟩ := by
    intro x h
    have e1 : R.rot ⟨.bdry x, trivial⟩ = ⟨.dn x 0, Or.inl rfl⟩ := Subtype.ext (hrot _ _)
    have e2 : R.rot ⟨.dn x 0, Or.inl rfl⟩ = ⟨.bdryRev (finRotate b x), trivial⟩ :=
      Subtype.ext (hrot _ _)
    have e3 : R.inv ⟨.bdryRev (finRotate b x), trivial⟩ = ⟨.bdry (finRotate b x), trivial⟩ :=
      Subtype.ext (hinv _ _)
    have := h.rot.rot.inv
    rwa [e1, e2, e3] at this
  have all : ∀ k (hk : k < b), R.Reach ⟨.bdry ⟨0, hb⟩, trivial⟩ ⟨.bdry ⟨k, hk⟩, trivial⟩ := by
    intro k
    induction k with
    | zero => exact fun _ => .refl _
    | succ k ih =>
      intro hk
      have := step _ (ih (by omega))
      have e : finRotate b ⟨k, by omega⟩ = ⟨k + 1, hk⟩ := by
        apply Fin.ext
        rw [val_finRotate]
        split_ifs with h
        · simp at h
          omega
        · rfl
      rwa [e] at this
  exact all x.1 x.2

/-- The legs of the bridge graph are reached from `e_1`. -/
private theorem reach_dn_zero_bridgeGraph (hb : 1 ≤ b) (R : RotationSystem (BridgeDart b s))
    (hrot : ∀ (d : BridgeSymbol b) (hd : IsDart s d), (R.rot ⟨d, hd⟩).1 = d.rotate s)
    (hinv : ∀ (d : BridgeSymbol b) (hd : IsDart s d), (R.inv ⟨d, hd⟩).1 = d.reverse s)
    (x : Fin b) : R.Reach ⟨.bdry ⟨0, hb⟩, trivial⟩ ⟨.dn x 0, Or.inl rfl⟩ := by
  have e : R.rot ⟨.bdry x, trivial⟩ = ⟨.dn x 0, Or.inl rfl⟩ := Subtype.ext (hrot _ _)
  rw [← e]
  exact (reach_bdry_bridgeGraph hb R hrot hinv x).rot

/-- A `dn` dart at a height of `P_x` below `m_x` is reached whenever the `up` dart at that height
is. -/
private theorem reach_dn_of_reach_up (R : RotationSystem (BridgeDart b s))
    (hrot : ∀ (d : BridgeSymbol b) (hd : IsDart s d), (R.rot ⟨d, hd⟩).1 = d.rotate s)
    {d₀ : BridgeDart b s} (x : Fin b) (v : ℕ) (hv : v ∈ heights s x) (hvt : v < top s x)
    (h : R.Reach d₀ ⟨.up x v, hv⟩) : R.Reach d₀ ⟨.dn x v, Or.inr ⟨hv, hvt⟩⟩ := by
  by_cases hl : (x : ℤ) + 1 = (pair s v).1
  · have e : R.rot ⟨.up x v, hv⟩ = ⟨.dn x v, Or.inr ⟨hv, hvt⟩⟩ :=
      Subtype.ext ((hrot _ _).trans (by rw [rotate_up, if_pos hl, if_pos hvt]))
    rw [← e]
    exact h.rot
  · have e : R.rot ⟨.dn x v, Or.inr ⟨hv, hvt⟩⟩ = ⟨.up x v, hv⟩ :=
      Subtype.ext ((hrot _ _).trans
        (by rw [rotate_dn_of_ne_zero (pos_of_mem_heights hv).ne', if_neg hl]))
    rw [← e] at h
    exact h.trans (RotationSystem.Reach.rot (.refl _)).symm

/-- The `up` darts of the bridge graph are reached from `e_1`. -/
private theorem reach_up_bridgeGraph (hb : 1 ≤ b) (R : RotationSystem (BridgeDart b s))
    (hrot : ∀ (d : BridgeSymbol b) (hd : IsDart s d), (R.rot ⟨d, hd⟩).1 = d.rotate s)
    (hinv : ∀ (d : BridgeSymbol b) (hd : IsDart s d), (R.inv ⟨d, hd⟩).1 = d.reverse s)
    (u : ℕ) (x : Fin b) (hu : u ∈ heights s x) :
    R.Reach ⟨.bdry ⟨0, hb⟩, trivial⟩ ⟨.up x u, hu⟩ := by
  induction u using Nat.strong_induction_on generalizing x with
  | _ u ih =>
    have hv : IsDart s (.dn x (prev s x u)) :=
      (prev_eq_zero_or_mem x u).imp_right fun h => ⟨h, prev_lt_top hu⟩
    have e : R.inv ⟨.dn x (prev s x u), hv⟩ = ⟨.up x u, hu⟩ :=
      Subtype.ext ((hinv _ _).trans
        (by rw [reverse_dn_of_lt_top (prev_lt_top hu), next_prev hu]))
    rw [← e]
    apply RotationSystem.Reach.inv
    rcases prev_eq_zero_or_mem x u (s := s) with h0 | hmem
    · have e' : (⟨.dn x (prev s x u), hv⟩ : BridgeDart b s) = ⟨.dn x 0, Or.inl rfl⟩ :=
        Subtype.ext (congrArg (BridgeSymbol.dn x) h0)
      rw [e']
      exact reach_dn_zero_bridgeGraph hb R hrot hinv x
    · exact reach_dn_of_reach_up R hrot x _ hmem (prev_lt_top hu)
        (ih _ (prev_lt (pos_of_mem_heights hu)) x hmem)

/-- Every dart of the bridge graph is reached from the boundary arc `e_1` by the rotation and the
involution, for any rotation system acting on the darts by the bridge graph's rotation and
involution. -/
private theorem reach_bridgeGraph (hb : 1 ≤ b) (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (R : RotationSystem (BridgeDart b s))
    (hrot : ∀ (d : BridgeSymbol b) (hd : IsDart s d), (R.rot ⟨d, hd⟩).1 = d.rotate s)
    (hinv : ∀ (d : BridgeSymbol b) (hd : IsDart s d), (R.inv ⟨d, hd⟩).1 = d.reverse s)
    (d : BridgeDart b s) :
    R.Reach ⟨.bdry ⟨0, hb⟩, trivial⟩ d := by
  set d₀ : BridgeDart b s := ⟨.bdry ⟨0, hb⟩, trivial⟩
  have hbdry := reach_bdry_bridgeGraph hb R hrot hinv
  have hdn0 := reach_dn_zero_bridgeGraph hb R hrot hinv
  have hup := reach_up_bridgeGraph hb R hrot hinv
  have hbridge : ∀ (t : ℕ) (ht : 1 ≤ t ∧ t ≤ s.length), R.Reach d₀ ⟨.bridge t, ht⟩ := by
    intro t ht
    obtain ⟨x, y, hx, hy, hxy, htx, hty⟩ := exists_ends hs ht.1 ht.2
    have e : R.rot ⟨.bridge t, ht⟩ = ⟨.up x t, htx⟩ :=
      Subtype.ext ((hrot _ _).trans (rotate_bridge_of_eq hx))
    have := hup t x htx
    rw [← e] at this
    exact this.trans (RotationSystem.Reach.rot (.refl _)).symm
  obtain ⟨d, hd⟩ := d
  cases d with
  | bdry x => exact hbdry x
  | bdryRev x =>
    have e : R.inv ⟨.bdry x, trivial⟩ = ⟨.bdryRev x, trivial⟩ := Subtype.ext (hinv _ _)
    rw [← e]
    exact (hbdry x).inv
  | lam x =>
    have h0 : top s x = 0 := top_eq_zero_iff.2 hd
    have e : R.inv ⟨.dn x 0, Or.inl rfl⟩ = ⟨.lam x, hd⟩ :=
      Subtype.ext ((hinv _ _).trans (by simp [reverse_dn, h0]))
    rw [← e]
    exact (hdn0 x).inv
  | dn x u =>
    cases hd with
    | inl h0 =>
      subst h0
      exact hdn0 x
    | inr h => exact reach_dn_of_reach_up R hrot x u h.1 h.2 (hup u x h.1)
  | up x u => exact hup u x hd
  | bridge t => exact hbridge t hd
  | bridgeRev t =>
    have e : R.inv ⟨.bridge t, hd⟩ = ⟨.bridgeRev t, hd⟩ := Subtype.ext (hinv _ _)
    rw [← e]
    exact (hbridge t hd).inv

/-- The rotation system of the bridge graph is connected. -/
theorem isConnected_bridgeGraph (hb : 1 ≤ b) (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) : (bridgeGraph b s γ).IsConnected := by
  refine RotationSystem.IsConnected.of_reach ⟨⟨.bdry ⟨0, hb⟩, trivial⟩⟩
    bridgeGraph.inv_involutive ?_ fun d e => ?_
  · rintro ⟨d, hd⟩ h
    have h' : d.reverse s = d := congrArg Subtype.val h
    cases d with
    | dn x u =>
      rw [reverse_dn] at h'
      split_ifs at h'
    | _ => simp at h'
  · have hr := reach_bridgeGraph hb hs (bridgeGraph b s γ).toRotationSystem
      (fun _ _ => rfl) (fun _ _ => rfl)
    exact (hr d).symm.trans (hr e)

namespace bridgeGraph

variable {γ : Fin b → Shade}

/-- The vertex key is constant on each vertex of the bridge graph. -/
theorem vertexKey_eq_of_mem_vertexOf {d e : BridgeDart b s}
    (h : e ∈ (bridgeGraph b s γ).vertexOf d) : vertexKey s e.1 = vertexKey s d.1 :=
  (eq_of_sameCycle_of_apply_eq (f := fun d : BridgeDart b s => vertexKey s d.1)
    (g := (bridgeGraph b s γ).rot) (fun d => vertexKey_rotate d.2)
    ((bridgeGraph b s γ).mem_vertexOf.1 h)).symm

/-- A dart whose vertex key is not that of a boundary vertex lies at an internal vertex. -/
theorem not_isBoundaryVertex_of_vertexKey {d : BridgeDart b s}
    (h : ∀ x, vertexKey s d.1 ≠ .inl x) :
    ¬(bridgeGraph b s γ).IsBoundaryVertex ((bridgeGraph b s γ).vertexOf d) := by
  rintro ⟨⟨e, he'⟩, he, heB⟩
  rw [mem_bdry] at heB
  have := vertexKey_eq_of_mem_vertexOf he
  cases e with
  | bdry x => exact h x this.symm
  | bdryRev y => exact h _ this.symm
  | _ => simp at heB

/-- The boundary arc `e_x` lies at the boundary vertex of the leg `g_x`. -/
theorem bdry_mem_vertexOf_leg (x : Fin b) :
    (⟨.bdry x, trivial⟩ : BridgeDart b s) ∈ (bridgeGraph b s γ).vertexOf ⟨.dn x 0, Or.inl rfl⟩ := by
  rw [RotationSystem.mem_vertexOf]
  have e : (bridgeGraph b s γ).rot ⟨.bdry x, trivial⟩ = ⟨.dn x 0, Or.inl rfl⟩ := rfl
  rw [← e]
  exact Equiv.Perm.sameCycle_apply_left.2 (.refl _ _)

/-- The leg `g_x` lies at a boundary vertex. -/
theorem isBoundaryVertex_leg (x : Fin b) :
    (bridgeGraph b s γ).IsBoundaryVertex
      ((bridgeGraph b s γ).vertexOf ⟨.dn x 0, Or.inl rfl⟩) :=
  ⟨_, bdry_mem_vertexOf_leg x, by simp⟩

/-- The boundary vertex at `e_x` is `{e_x, g_x, ē_{x+1}}`. -/
theorem vertexOf_bdry (x : Fin b) :
    (bridgeGraph b s γ).vertexOf ⟨.bdry x, trivial⟩ =
      {⟨.bdry x, trivial⟩, ⟨.dn x 0, Or.inl rfl⟩, ⟨.bdryRev (finRotate b x), trivial⟩} :=
  vertexOf_eq_of_rot_rot_rot (bridgeGraph b s γ).toRotationSystem (Subtype.ext (by
    change (((BridgeSymbol.bdry x).rotate s).rotate s).rotate s = _
    simp only [rotate_bdry, rotate_dn_zero, rotate_bdryRev, Equiv.symm_apply_apply]))

/-- Every boundary vertex of the bridge graph is the vertex of some `e_x`. -/
theorem exists_eq_vertexOf_bdry {v : Finset (BridgeDart b s)}
    (hv : v ∈ (bridgeGraph b s γ).boundaryVertices) :
    ∃ x, v = (bridgeGraph b s γ).vertexOf ⟨.bdry x, trivial⟩ := by
  rw [DiskMap.mem_boundaryVertices] at hv
  obtain ⟨hv, e, he, heB⟩ := hv
  obtain ⟨d, rfl⟩ := (bridgeGraph b s γ).mem_vertices.1 hv
  rw [← (bridgeGraph b s γ).vertexOf_eq_of_mem he]
  rw [mem_bdry] at heB
  obtain ⟨e, he'⟩ := e
  cases e with
  | bdry x => exact ⟨x, rfl⟩
  | bdryRev y =>
    refine ⟨(finRotate b).symm y, ?_⟩
    rw [← (bridgeGraph b s γ).vertexOf_rot ⟨.bdryRev y, he'⟩]
    rfl
  | _ => simp at heB

end bridgeGraph

/-- The bridge graph has at least `b + |L| + 2r` vertices, `L` the lollipop positions. -/
private theorem card_vertices_bridgeGraph_ge (γ : Fin b → Shade) :
    ((univ : Finset (Fin b)).disjSum ((univ.filter fun x : Fin b => heights s x = ∅).disjSum
      ((Icc 1 s.length).disjSum (Icc 1 s.length)))).card ≤
      (bridgeGraph b s γ).vertices.card := by
  refine (card_le_card ?_).trans (card_image_le_card_image_of_factor
    (f := fun d : BridgeDart b s => vertexKey s d.1) (g := (bridgeGraph b s γ).vertexOf) ?_)
  · intro k hk
    rw [mem_image]
    rcases k with x | x | t | t
    · exact ⟨⟨.bdry x, trivial⟩, mem_univ _, rfl⟩
    · simp only [inr_mem_disjSum, inl_mem_disjSum, mem_filter, mem_univ,
        true_and] at hk
      exact ⟨⟨.lam x, hk⟩, mem_univ _, rfl⟩
    · simp only [inr_mem_disjSum, inl_mem_disjSum, mem_Icc] at hk
      exact ⟨⟨.bridge t, hk⟩, mem_univ _, rfl⟩
    · simp only [inr_mem_disjSum, mem_Icc] at hk
      exact ⟨⟨.bridgeRev t, hk⟩, mem_univ _, rfl⟩
  · intro d d' h
    have : d' ∈ (bridgeGraph b s γ).vertexOf d := by
      rw [h]
      exact (bridgeGraph b s γ).self_mem_vertexOf d'
    exact (bridgeGraph.vertexKey_eq_of_mem_vertexOf this).symm

/-- The bridge graph has at most `b + |L| + 3r` edges, `L` the lollipop positions. -/
private theorem card_edges_bridgeGraph_le (γ : Fin b → Shade) :
    (bridgeGraph b s γ).edges.card ≤ ((univ : Finset (Fin b)).disjSum
      ((univ.filter fun x : Fin b => heights s x = ∅).disjSum ((Icc 1 s.length).disjSum
        ((Icc 1 s.length) ×ˢ (univ : Finset Bool))))).card := by
  refine (card_image_le_card_image_of_factor (f := (bridgeGraph b s γ).edgeOf)
    (g := fun d : BridgeDart b s => edgeKey s d.1) ?_).trans (card_le_card ?_)
  · intro d d' h
    rcases eq_or_eq_reverse_of_edgeKey_eq d.2 d'.2 h with h' | h'
    · rw [Subtype.ext h']
    · have : d' = (bridgeGraph b s γ).inv d := Subtype.ext h'
      rw [this]
      change ({d, (bridgeGraph b s γ).inv d} : Finset _) =
        {(bridgeGraph b s γ).inv d, (bridgeGraph b s γ).inv ((bridgeGraph b s γ).inv d)}
      rw [bridgeGraph.inv_involutive d, pair_comm]
  · intro k hk
    obtain ⟨⟨d, hd⟩, -, rfl⟩ := mem_image.1 hk
    cases d with
    | bdry x => simp [edgeKey]
    | bdryRev x => simp [edgeKey]
    | lam x => simpa [edgeKey] using hd
    | dn x u =>
      simp only [edgeKey]
      split_ifs with hut
      · have hm := next_mem hut
        simp only [inr_mem_disjSum, mem_product, mem_Icc, mem_univ, and_true]
        exact ⟨pos_of_mem_heights hm, le_length_of_mem_heights hm⟩
      · obtain rfl : u = 0 := hd.resolve_right fun h => hut h.2
        simpa [← top_eq_zero_iff] using hut
    | up x u =>
      simp only [edgeKey, inr_mem_disjSum, mem_product, mem_Icc, mem_univ, and_true]
      exact ⟨pos_of_mem_heights hd, le_length_of_mem_heights hd⟩
    | bridge t => simpa [edgeKey] using hd
    | bridgeRev t => simpa [edgeKey] using hd

/-- The counts behind Euler's relation for the bridge graph: `|V| - |E| + |Φ| = 2`, the face
labelling takes `r + 2` values, and there are `r + 2` orbits of `φ`. -/
private theorem bridgeGraph_count (hb : 1 ≤ b) (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (hn : IsNestedPairSequence s) (γ : Fin b → Shade) :
    ((bridgeGraph b s γ).vertices.card : ℤ) - (bridgeGraph b s γ).edges.card +
        (bridgeGraph b s γ).faceOrbits.card = 2 ∧
      (univ.image fun d : BridgeDart b s => faceLabel s d.1).card = s.length + 2 ∧
      (bridgeGraph b s γ).faceOrbits.card = s.length + 2 := by
  have hR := isConnected_bridgeGraph hb hs γ
  have heu := hR.euler_le
  have hV := card_vertices_bridgeGraph_ge (s := s) γ
  have hE := card_edges_bridgeGraph_le (s := s) γ
  set lol : Finset (Fin b) := univ.filter fun x => heights s x = ∅ with hlol
  set Λ : BridgeDart b s → Option ℕ := fun d => faceLabel s d.1 with hΛdef
  have hΛ : ∀ d, Λ ((bridgeGraph b s γ).facePerm d) = Λ d := fun d =>
    faceLabel_rotate_reverse hs hn d.2
  have hF1 : (insert none ((range (s.length + 1)).image some) : Finset (Option ℕ)).card ≤
      (univ.image Λ).card := by
    refine card_le_card fun k hk => ?_
    rw [mem_insert, mem_image] at hk
    rw [mem_image]
    rcases hk with rfl | ⟨t, ht, rfl⟩
    · exact ⟨⟨.bdry ⟨0, hb⟩, trivial⟩, mem_univ _, rfl⟩
    · rcases Nat.eq_zero_or_pos t with rfl | ht0
      · refine ⟨⟨.bdryRev ⟨0, hb⟩, trivial⟩, mem_univ _, ?_⟩
        simp [Λ, faceLabel, regionLabel_zero hs]
      · exact ⟨⟨.bridgeRev t, ht0, by simp at ht; omega⟩, mem_univ _, rfl⟩
  have hF2 : (univ.image Λ).card ≤ (bridgeGraph b s γ).faceOrbits.card :=
    card_image_le_card_image_of_factor fun d d' h => by
      rw [RotationSystem.faceOf_eq_faceOf_iff] at h
      exact eq_of_sameCycle_of_apply_eq hΛ h
  have hL : (insert none ((range (s.length + 1)).image some) : Finset (Option ℕ)).card =
      s.length + 2 := by
    rw [card_insert_of_notMem (by simp), card_image_of_injective _ (Option.some_injective _),
      card_range]
  have hW : ((univ : Finset (Fin b)).disjSum
      (lol.disjSum ((Icc 1 s.length).disjSum (Icc 1 s.length)))).card =
      b + lol.card + (s.length + s.length) := by
    simp only [card_disjSum, card_univ, Fintype.card_fin, Nat.card_Icc]
    omega
  have hE' : ((univ : Finset (Fin b)).disjSum (lol.disjSum ((Icc 1 s.length).disjSum
      ((Icc 1 s.length) ×ˢ (univ : Finset Bool))))).card =
      b + lol.card + (s.length + s.length * 2) := by
    simp only [card_disjSum, card_univ, Fintype.card_fin, Nat.card_Icc, card_product,
      Fintype.card_bool]
    omega
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- In the bridge graph of a nested sequence, two darts lie on the same orbit of `φ` exactly
when they have the same face label. -/
theorem faceOf_eq_faceOf_iff_bridgeGraph (hb : 1 ≤ b)
    (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (hn : IsNestedPairSequence s)
    (γ : Fin b → Shade) (d d' : BridgeDart b s) :
    (bridgeGraph b s γ).faceOf d = (bridgeGraph b s γ).faceOf d' ↔
      faceLabel s d.1 = faceLabel s d'.1 := by
  obtain ⟨heu, hΛ, hΦ⟩ := bridgeGraph_count hb hs hn γ
  have hR := isConnected_bridgeGraph hb hs γ
  set S := univ.image fun d : BridgeDart b s => faceLabel s d.1
  have key := hR.faceOf_eq_faceOf_iff_of_surjective (L := ↥S)
    (lab := fun d => ⟨faceLabel s d.1, mem_image_of_mem _ (mem_univ _)⟩)
    (fun ⟨k, hk⟩ => by
      obtain ⟨d, -, rfl⟩ := mem_image.1 hk
      exact ⟨d, rfl⟩)
    (fun d => Subtype.ext (faceLabel_rotate_reverse hs hn d.2))
    (by rw [Fintype.card_coe, hΛ]; omega) d d'
  rw [key, Subtype.mk.injEq]

/-- A symbol has no face label exactly when it is a boundary symbol. -/
theorem faceLabel_eq_none_iff {d : BridgeSymbol b} : faceLabel s d = none ↔ ∃ x, d = .bdry x := by
  cases d <;> simp [faceLabel]

/-- The darts on the orbit of `φ` through `e_1` are exactly the boundary arcs `e_x`. -/
private theorem mem_faceOf_bdry_iff (hb : 1 ≤ b) (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (hn : IsNestedPairSequence s) (γ : Fin b → Shade) (e : BridgeDart b s) :
    e ∈ (bridgeGraph b s γ).faceOf ⟨.bdry ⟨0, hb⟩, trivial⟩ ↔ ∃ x, e.1 = .bdry x := by
  rw [← faceLabel_eq_none_iff, RotationSystem.mem_faceOf,
    ← RotationSystem.faceOf_eq_faceOf_iff, faceOf_eq_faceOf_iff_bridgeGraph hb hs hn]
  exact eq_comm

/-- The orbit of `φ` through `e_1` is half of the boundary of the bridge graph. -/
private theorem exists_orbit_bridgeGraph (hb : 1 ≤ b)
    (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (hn : IsNestedPairSequence s)
    (γ : Fin b → Shade) :
    ∃ f ∈ (bridgeGraph b s γ).faceOrbits, f ⊆ (bridgeGraph b s γ).bdry ∧
      f ∪ f.map (bridgeGraph b s γ).inv.toEmbedding = (bridgeGraph b s γ).bdry ∧
      Disjoint f (f.map (bridgeGraph b s γ).inv.toEmbedding) := by
  set d₀ : BridgeDart b s := ⟨.bdry ⟨0, hb⟩, trivial⟩
  have hext := mem_faceOf_bdry_iff hb hs hn γ
  refine ⟨(bridgeGraph b s γ).faceOf d₀, (bridgeGraph b s γ).faceOf_mem_faceOrbits d₀, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, hx⟩ := (hext e).1 he
    rw [bridgeGraph.mem_bdry, hx]
    trivial
  · ext ⟨e, he⟩
    rw [mem_union, mem_map_equiv, hext, hext, bridgeGraph.mem_bdry]
    change (∃ x, e = .bdry x) ∨ (∃ x, e.reverse s = .bdry x) ↔ e.IsBoundaryArc
    cases e with
    | dn x u =>
      simp only [reverse_dn]
      split_ifs <;> simp
    | _ => simp
  · rw [disjoint_left]
    rintro ⟨e, he⟩ h1 h2
    rw [mem_map_equiv, hext] at h2
    obtain ⟨x, hx⟩ := (hext _).1 h1
    obtain ⟨y, hy⟩ := h2
    change e = .bdry x at hx
    change e.reverse s = .bdry y at hy
    subst hx
    simp at hy

/-- **The bridge graph is a plabic graph.** Let `b ≥ 1`, let `s` be a nested sequence of `r ≥ 0`
pairs of integers with `1 ≤ i_t < j_t ≤ b`, and let `γ : [1, b] → Shade`. Then `G(s, γ)` is a
plabic graph with `b` boundary vertices. -/
@[cluster_algebras "lem_bridge_graph_plabic"]
theorem isPlabicGraph_bridgeGraph (hb : 1 ≤ b) (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (hn : IsNestedPairSequence s) (γ : Fin b → Shade) : (bridgeGraph b s γ).IsPlabicGraph := by
  have hR := isConnected_bridgeGraph hb hs γ
  obtain ⟨heu, -, -⟩ := bridgeGraph_count hb hs hn γ
  refine
    { toIsDiskMap :=
        { toIsConnected := hR
          inv_mem_bdry := ?_
          euler := heu
          boundaryVertex_card := ?_
          exists_orbit := ?_ }
      one_le := hb
      colour_rot := fun d _ => colour_rotate γ d.2
      leg_notMem_bdry := fun i => by
        rw [bridgeGraph.mem_bdry]
        exact not_isBoundaryArc_dn i 0
      bvertex_mem := fun i => (bridgeGraph b s γ).vertexOf_mem_boundaryVertices.2
        (bridgeGraph.isBoundaryVertex_leg i)
      bvertex_injective := ?_
      exists_bvertex_eq := ?_
      exists_exterior := ?_ }
  · rintro ⟨d, hd⟩ h
    rw [bridgeGraph.mem_bdry] at h ⊢
    change (d.reverse s).IsBoundaryArc
    cases d <;> simp_all
  · intro v hv
    obtain ⟨x, rfl⟩ := bridgeGraph.exists_eq_vertexOf_bdry hv
    rw [bridgeGraph.vertexOf_bdry]
    refine ⟨?_, ?_⟩
    · rw [card_eq_three]
      exact ⟨_, _, _, by simp, by simp, by simp, rfl⟩
    · simp [filter_insert, filter_singleton]
  · exact exists_orbit_bridgeGraph hb hs hn γ
  · intro i j h
    have hj : (bridgeGraph b s γ).leg j ∈ (bridgeGraph b s γ).bvertex i := by
      rw [h]
      exact (bridgeGraph b s γ).self_mem_vertexOf _
    simpa [vertexKey] using (bridgeGraph.vertexKey_eq_of_mem_vertexOf hj).symm
  · intro v hv
    obtain ⟨x, rfl⟩ := bridgeGraph.exists_eq_vertexOf_bdry hv
    refine ⟨x, ?_⟩
    rw [← (bridgeGraph b s γ).vertexOf_rot ⟨.bdry x, trivial⟩]
    rfl
  · intro i
    refine ⟨⟨.bdry (finRotate b i), trivial⟩, ?_, bridgeGraph.bdry_mem_vertexOf_leg _, ?_⟩
    · rw [DiskMap.mem_exterior, bridgeGraph.mem_bdry, bridgeGraph.mem_bdry]
      exact ⟨trivial, not_isBoundaryArc_dn _ 0⟩
    · rw [PlabicData.bvertex, RotationSystem.mem_vertexOf]
      have e : (bridgeGraph b s γ).inv ⟨.bdry (finRotate b i), trivial⟩ =
          (bridgeGraph b s γ).rot ⟨.dn i 0, Or.inl rfl⟩ := rfl
      rw [e]
      exact Equiv.Perm.sameCycle_apply_right.2 (.refl _ _)

/-- **Faces of the bridge graph.** Let `b ≥ 1`, let `s` be a nested sequence of `r ≥ 0` pairs of
integers with `1 ≤ i_t < j_t ≤ b`, and let `γ : [1, b] → Shade`. Then `G(s, γ)` has exactly
`r + 1` faces. -/
@[cluster_algebras "lem_bridge_graph_faces"]
theorem card_faces_bridgeGraph (hb : 1 ≤ b) (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (hn : IsNestedPairSequence s) (γ : Fin b → Shade) :
    (bridgeGraph b s γ).faces.card = s.length + 1 := by
  obtain ⟨-, -, hΦ⟩ := bridgeGraph_count hb hs hn γ
  have hG := isPlabicGraph_bridgeGraph hb hs hn γ
  rw [DiskMap.faces, card_erase_of_mem hG.exterior_mem_faceOrbits, hΦ]
  rfl

end Plabic

/-! ### Trips in the bridge graph -/

section Trips

variable {b : ℕ} {s : List (ℤ × ℤ)}

namespace BridgeGraph

/-- The `t`-th pair is `s[t - 1]`; for `t = τ + 1` this is `s[τ]`. -/
theorem pair_succ {τ : ℕ} (h : τ < s.length) : pair s (τ + 1) = s[τ] :=
  List.getD_eq_getElem _ _ h

/-- The top height `m_x` on the line of `x` is at most the number of pairs. -/
theorem top_le_length (x : Fin b) : top s x ≤ s.length :=
  Finset.sup_le fun _ ht => le_length_of_mem_heights ht

end BridgeGraph

private theorem endKey_ne_inl (x : Fin b) (u : ℕ) (y : Fin b) : endKey s x u ≠ .inl y := by
  unfold endKey
  split_ifs <;> simp

namespace bridgeGraph

variable (γ : Fin b → Shade)

/-- The vertex of an `up` dart is not a boundary vertex. -/
theorem not_isBoundaryVertex_up {x : Fin b} {u : ℕ} (h : IsDart s (.up x u)) :
    ¬(bridgeGraph b s γ).IsBoundaryVertex ((bridgeGraph b s γ).vertexOf ⟨.up x u, h⟩) :=
  not_isBoundaryVertex_of_vertexKey fun y => endKey_ne_inl x u y

/-- The vertex of a `dn` dart at a nonzero height is not a boundary vertex. -/
theorem not_isBoundaryVertex_dn {x : Fin b} {u : ℕ} (hu : u ≠ 0) (h : IsDart s (.dn x u)) :
    ¬(bridgeGraph b s γ).IsBoundaryVertex ((bridgeGraph b s γ).vertexOf ⟨.dn x u, h⟩) :=
  not_isBoundaryVertex_of_vertexKey fun y => by
    change (if u = 0 then _ else _) ≠ _
    rw [if_neg hu]
    exact endKey_ne_inl x u y

/-- The vertex of a `bridge` dart is not a boundary vertex. -/
theorem not_isBoundaryVertex_bridge {t : ℕ} (h : IsDart (b := b) s (.bridge t)) :
    ¬(bridgeGraph b s γ).IsBoundaryVertex ((bridgeGraph b s γ).vertexOf ⟨.bridge t, h⟩) :=
  not_isBoundaryVertex_of_vertexKey fun y => by simp [vertexKey]

/-- The vertex of a `bridgeRev` dart is not a boundary vertex. -/
theorem not_isBoundaryVertex_bridgeRev {t : ℕ} (h : IsDart (b := b) s (.bridgeRev t)) :
    ¬(bridgeGraph b s γ).IsBoundaryVertex ((bridgeGraph b s γ).vertexOf ⟨.bridgeRev t, h⟩) :=
  not_isBoundaryVertex_of_vertexKey fun y => by simp [vertexKey]

/-- The vertex of a `lam` dart is not a boundary vertex. -/
theorem not_isBoundaryVertex_lam {x : Fin b} (h : IsDart s (.lam x)) :
    ¬(bridgeGraph b s γ).IsBoundaryVertex ((bridgeGraph b s γ).vertexOf ⟨.lam x, h⟩) :=
  not_isBoundaryVertex_of_vertexKey fun y => by simp [vertexKey]

end bridgeGraph

/-- **The trip map of the bridge graph**, going down a line: for a line position `x`,
`u ∈ ({0} ∪ P_x) \ {m_x}` and `u' = nx_x(u)`, `T(dn_{x,u}) = c_{u'}` if `x + 1 = i_{u'}` and
`T(dn_{x,u}) = c̄_{u'}` if `x + 1 = j_{u'}`. -/
@[cluster_algebras "lem_bridge_graph_trip_map"]
theorem tripMap_bridgeGraph_dn (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (γ : Fin b → Shade)
    {x : Fin b} {u u' : ℕ} (hut : u < top s x) (hnext : next s x u = u')
    (h : IsDart s (.dn x u)) :
    ((x : ℤ) + 1 = (pair s u').1 →
      ((bridgeGraph b s γ).tripMap ⟨.dn x u, h⟩).1 = .bridge u') ∧
    ((x : ℤ) + 1 = (pair s u').2 →
      ((bridgeGraph b s γ).tripMap ⟨.dn x u, h⟩).1 = .bridgeRev u') := by
  subst hnext
  have hm := next_mem hut
  have hz : (bridgeGraph b s γ).inv ⟨.dn x u, h⟩ = ⟨.up x (next s x u), hm⟩ :=
    Subtype.ext (reverse_dn_of_lt_top hut)
  have hint := bridgeGraph.not_isBoundaryVertex_up γ hm
  have hb := pair_bounds hs (pos_of_mem_heights hm) (le_length_of_mem_heights hm)
  rw [PlabicData.tripMap_apply, hz]
  refine ⟨fun hl => ?_, fun hr => ?_⟩
  · rw [PlabicData.turn_of_white hint (by simp [colour_up, hl])]
    simp only [bridgeGraph.rot_symm_val]
    rw [rotateInv_up, if_pos hl]
  · have hl : ¬(x : ℤ) + 1 = (pair s (next s x u)).1 := by omega
    rw [PlabicData.turn_of_black hint (by simp [colour_up, hl])]
    simp only [bridgeGraph.rot_val]
    rw [rotate_up, if_neg hl]

/-- **The trip map of the bridge graph**, along a bridge: `T(c_t) = dn_{j_t,t}` if `t ≠ m_{j_t}`
and `T(c_t) = up_{j_t,t}` if `t = m_{j_t}`, where the label `y` with `y + 1 = j_t` is the right
end of the `t`-th pair. -/
@[cluster_algebras "lem_bridge_graph_trip_map"]
theorem tripMap_bridgeGraph_bridge (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) {t : ℕ} (ht : IsDart (b := b) s (.bridge t)) {y : Fin b}
    (hy : (y : ℤ) + 1 = (pair s t).2) :
    (t ≠ top s y → ((bridgeGraph b s γ).tripMap ⟨.bridge t, ht⟩).1 = .dn y t) ∧
    (t = top s y → ((bridgeGraph b s γ).tripMap ⟨.bridge t, ht⟩).1 = .up y t) := by
  have hb := pair_bounds hs ht.1 ht.2
  have hty : t ∈ heights s y := mem_heights.2 ⟨ht.1, ht.2, Or.inr hy⟩
  have hz : (bridgeGraph b s γ).inv ⟨.bridge t, ht⟩ = ⟨.bridgeRev t, ht⟩ := rfl
  rw [PlabicData.tripMap_apply, hz,
    PlabicData.turn_of_black (bridgeGraph.not_isBoundaryVertex_bridgeRev γ ht) rfl]
  simp only [bridgeGraph.rot_val]
  rw [rotate_bridgeRev_of_eq hy (by omega)]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [if_pos (lt_of_le_of_ne (le_top hty) h)]
  · rw [if_neg (by omega)]

/-- **The trip map of the bridge graph**, along a reversed bridge: `T(c̄_t) = dn_{i_t,t}` if
`t ≠ m_{i_t}` and `T(c̄_t) = up_{i_t,t}` if `t = m_{i_t}`, where the label `x` with
`x + 1 = i_t` is the left end of the `t`-th pair. -/
@[cluster_algebras "lem_bridge_graph_trip_map"]
theorem tripMap_bridgeGraph_bridgeRev (γ : Fin b → Shade) {t : ℕ}
    (ht : IsDart (b := b) s (.bridgeRev t)) {x : Fin b} (hx : (x : ℤ) + 1 = (pair s t).1) :
    (t ≠ top s x → ((bridgeGraph b s γ).tripMap ⟨.bridgeRev t, ht⟩).1 = .dn x t) ∧
    (t = top s x → ((bridgeGraph b s γ).tripMap ⟨.bridgeRev t, ht⟩).1 = .up x t) := by
  have htx : t ∈ heights s x := mem_heights.2 ⟨ht.1, ht.2, Or.inl hx⟩
  have hz : (bridgeGraph b s γ).inv ⟨.bridgeRev t, ht⟩ = ⟨.bridge t, ht⟩ := rfl
  rw [PlabicData.tripMap_apply, hz,
    PlabicData.turn_of_white (bridgeGraph.not_isBoundaryVertex_bridge γ ht) rfl]
  simp only [bridgeGraph.rot_symm_val]
  rw [rotateInv_bridge_of_eq hx]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [if_pos (lt_of_le_of_ne (le_top htx) h)]
  · rw [if_neg (by omega)]

/-- **The trip map of the bridge graph**, going up a line: for a line position `x`,
`u ∈ ({0} ∪ P_x) \ {m_x}` and `u' = nx_x(u)`, `T(up_{x,u'}) = up_{x,u}` if `u ≠ 0` and
`T(up_{x,u'}) = g_x` if `u = 0`. -/
@[cluster_algebras "lem_bridge_graph_trip_map"]
theorem tripMap_bridgeGraph_up (γ : Fin b → Shade) {x : Fin b} {u u' : ℕ}
    (hu : u = 0 ∨ u ∈ heights s x) (hut : u < top s x) (hnext : next s x u = u')
    (h : IsDart s (.up x u')) :
    (u ≠ 0 → ((bridgeGraph b s γ).tripMap ⟨.up x u', h⟩).1 = .up x u) ∧
    (u = 0 → ((bridgeGraph b s γ).tripMap ⟨.up x u', h⟩).1 = .dn x 0) := by
  subst hnext
  have hd : IsDart s (.dn x u) := hu.imp_right fun h => ⟨h, hut⟩
  have hz : (bridgeGraph b s γ).inv ⟨.up x (next s x u), h⟩ = ⟨.dn x u, hd⟩ :=
    Subtype.ext (by rw [bridgeGraph.inv_val, reverse_up, prev_next hu hut])
  rw [PlabicData.tripMap_apply, hz]
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have hint := bridgeGraph.not_isBoundaryVertex_dn γ h0 hd
    by_cases hl : (x : ℤ) + 1 = (pair s u).1
    · rw [PlabicData.turn_of_white hint (by simp [colour_dn_of_ne_zero γ h0, hl])]
      simp only [bridgeGraph.rot_symm_val]
      rw [rotateInv_dn_of_ne_zero h0, if_pos hl]
    · rw [PlabicData.turn_of_black hint (by simp [colour_dn_of_ne_zero γ h0, hl])]
      simp only [bridgeGraph.rot_val]
      rw [rotate_dn_of_ne_zero h0, if_neg hl]
  · subst h0
    rw [PlabicData.turn_of_isBoundaryVertex (bridgeGraph.isBoundaryVertex_leg x)]

/-- **The trip map of the bridge graph** at a lollipop position `z`: `T(g_z) = λ_z` and
`T(λ_z) = g_z`. -/
@[cluster_algebras "lem_bridge_graph_trip_map"]
theorem tripMap_bridgeGraph_lollipop (γ : Fin b → Shade) {z : Fin b} (hz : heights s z = ∅) :
    ((bridgeGraph b s γ).tripMap ⟨.dn z 0, Or.inl rfl⟩).1 = .lam z ∧
      ((bridgeGraph b s γ).tripMap ⟨.lam z, hz⟩).1 = .dn z 0 := by
  have h0 : top s z = 0 := top_eq_zero_iff.2 hz
  have e1 : (bridgeGraph b s γ).inv ⟨.dn z 0, Or.inl rfl⟩ = ⟨.lam z, hz⟩ :=
    Subtype.ext (by simp [reverse_dn, h0])
  have e2 : (bridgeGraph b s γ).inv ⟨.lam z, hz⟩ = ⟨.dn z 0, Or.inl rfl⟩ := rfl
  have hint := bridgeGraph.not_isBoundaryVertex_lam γ hz
  refine ⟨?_, ?_⟩
  · rw [PlabicData.tripMap_apply, e1]
    cases hc : γ z
    · rw [PlabicData.turn_of_white hint hc]
      rfl
    · rw [PlabicData.turn_of_black hint hc]
      rfl
  · rw [PlabicData.tripMap_apply, e2,
      PlabicData.turn_of_isBoundaryVertex (bridgeGraph.isBoundaryVertex_leg z)]

/-! #### The trip permutation -/

/-- The trip from `d` reaches `e` without meeting a leg after `d` (`e` included). -/
private def TripAvoids {H : Type*} [Fintype H] [DecidableEq H] (G : PlabicData H b)
    (d e : H) : Prop :=
  ∃ k, G.tripMap^[k] d = e ∧ ∀ k', 0 < k' → k' ≤ k → ¬G.IsLeg (G.tripMap^[k'] d)

private theorem TripAvoids.refl {H : Type*} [Fintype H] [DecidableEq H] {G : PlabicData H b}
    (d : H) : TripAvoids G d d :=
  ⟨0, rfl, fun _ h1 h2 => by omega⟩

private theorem TripAvoids.step {H : Type*} [Fintype H] [DecidableEq H] {G : PlabicData H b}
    {d e : H} (h : TripAvoids G d e) (he : ¬G.IsLeg (G.tripMap e)) :
    TripAvoids G d (G.tripMap e) := by
  obtain ⟨k, rfl, hk⟩ := h
  refine ⟨k + 1, by rw [Function.iterate_succ_apply'], fun k' h1 h2 => ?_⟩
  rcases Nat.lt_or_ge k' (k + 1) with h | h
  · exact hk k' h1 (by omega)
  · obtain rfl : k' = k + 1 := by omega
    rw [Function.iterate_succ_apply']
    exact he

/-- If the trip from `g_i` reaches `e` without meeting a leg, and `T(e) = g_j`, then the trip
permutation sends `i` to `j`. -/
private theorem tripPerm_eq_of_tripAvoids {H : Type*} [Fintype H] [DecidableEq H]
    {G : PlabicData H b} {i j : Fin b} {e : H} (h : TripAvoids G (G.leg i) e)
    (hj : G.tripMap e = G.leg j) (hinj : Function.Injective G.leg) : G.tripPerm i = j := by
  obtain ⟨k, rfl, hk⟩ := h
  have hleg : G.IsLeg (G.tripMap^[k + 1] (G.leg i)) :=
    ⟨j, by rw [Function.iterate_succ_apply', hj]⟩
  have hex : ∃ m, 0 < m ∧ G.IsLeg (G.tripMap^[m] (G.leg i)) := ⟨k + 1, by omega, hleg⟩
  have hlen : G.tripLength i = k + 1 := by
    apply le_antisymm (PlabicData.tripLength_le (by omega) hleg)
    by_contra hlt
    obtain ⟨h0, hl⟩ := PlabicData.tripLength_spec hex
    exact hk _ h0 (by omega) hl
  apply hinj
  rw [PlabicData.leg_tripPerm hex, hlen, Function.iterate_succ_apply', hj]

/-- A dart that is not some `dn_{y,0}` is not a leg of the bridge graph. -/
private theorem bridgeGraph_not_isLeg (γ : Fin b → Shade) {d : BridgeDart b s}
    (h : ∀ y, d.1 ≠ .dn y 0) : ¬(bridgeGraph b s γ).IsLeg d := by
  rintro ⟨y, rfl⟩
  exact h y rfl

/-- Two steps of a trip running down the line of `y` from the vertex at height `u`: it crosses
the bridge of height `t = nx_y(u)` to the other end `z` of the `t`-th pair, and then continues
downwards from height `t` on the line of `z`, or turns up if `t = m_z`. -/
private theorem tripMap_tripMap_dn (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) {y : Fin b} {u : ℕ} (hut : u < top s y) (hd : IsDart s (.dn y u)) :
    ∃ z : Fin b, (z : ℤ) + 1 = Equiv.swap (pair s (next s y u)).1 (pair s (next s y u)).2
        ((y : ℤ) + 1) ∧ next s y u ∈ heights s z ∧
      (∀ w, ((bridgeGraph b s γ).tripMap ⟨.dn y u, hd⟩).1 ≠ .dn w 0) ∧
      ((bridgeGraph b s γ).tripMap ((bridgeGraph b s γ).tripMap ⟨.dn y u, hd⟩)).1 =
        if next s y u < top s z then .dn z (next s y u) else .up z (next s y u) := by
  have hm := next_mem hut
  have h1 := pos_of_mem_heights hm
  have h2 := le_length_of_mem_heights hm
  have hb := pair_bounds hs h1 h2
  obtain ⟨xl, xr, hxl, hxr, -, hml, hmr⟩ := exists_ends hs h1 h2
  obtain ⟨ha1, ha2⟩ := tripMap_bridgeGraph_dn hs γ hut rfl hd
  rcases (mem_heights.1 hm).2.2 with hl | hr
  · have e1 : (bridgeGraph b s γ).tripMap ⟨.dn y u, hd⟩ = ⟨.bridge (next s y u), h1, h2⟩ :=
      Subtype.ext (ha1 hl)
    refine ⟨xr, by rw [← hl, Equiv.swap_apply_left, hxr], hmr, by rw [e1]; simp, ?_⟩
    rw [e1]
    obtain ⟨hb1, hb2⟩ := tripMap_bridgeGraph_bridge hs γ ⟨h1, h2⟩ hxr
    split_ifs with htop
    · exact hb1 htop.ne
    · exact hb2 (le_antisymm (le_top hmr) (not_lt.1 htop))
  · have e1 : (bridgeGraph b s γ).tripMap ⟨.dn y u, hd⟩ = ⟨.bridgeRev (next s y u), h1, h2⟩ :=
      Subtype.ext (ha2 hr)
    refine ⟨xl, by rw [← hr, Equiv.swap_apply_right, hxl], hml, by rw [e1]; simp, ?_⟩
    rw [e1]
    obtain ⟨hb1, hb2⟩ := tripMap_bridgeGraph_bridgeRev γ ⟨h1, h2⟩ hxl
    split_ifs with htop
    · exact hb1 htop.ne
    · exact hb2 (le_antisymm (le_top hml) (not_lt.1 htop))

/-- The position maps fix every integer lying in no pair. -/
private theorem positionMap_apply_of_forall_ne {v : ℤ}
    (h : ∀ (u : ℕ) (hu : u < s.length), v ≠ s[u].1 ∧ v ≠ s[u].2) (τ : ℕ) :
    positionMap s τ v = v := by
  induction τ with
  | zero => simp
  | succ τ ih =>
    rcases lt_or_ge τ s.length with hτ | hτ
    · rw [positionMap_succ hτ, Equiv.Perm.mul_apply, ih,
        Equiv.swap_apply_of_ne_of_ne (h τ hτ).1 (h τ hτ).2]
    · rw [positionMap_of_length_le (by omega), ← positionMap_of_length_le hτ, ih]

/-- One step of the trip from `g_x` across a height `τ + 1 ∈ P_y`: it continues on the line of
`z`, with `z + 1 = τ_{τ+1}(y + 1)`. -/
private theorem exists_tripAvoids_succ_of_mem (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) {x y : Fin b} {τ : ℕ} (hmem : τ + 1 ∈ heights s y)
    (hD : IsDart s (.dn y (prev s y (τ + 1))))
    (hav : TripAvoids (bridgeGraph b s γ) ((bridgeGraph b s γ).leg x)
      ⟨.dn y (prev s y (τ + 1)), hD⟩) :
    ∃ z : Fin b, (z : ℤ) + 1 = Equiv.swap (pair s (τ + 1)).1 (pair s (τ + 1)).2 ((y : ℤ) + 1) ∧
      ((τ + 1 < top s z ∧ ∃ h, TripAvoids (bridgeGraph b s γ) ((bridgeGraph b s γ).leg x)
          ⟨.dn z (prev s z (τ + 1 + 1)), h⟩) ∨
        (top s z ≤ τ + 1 ∧ ∃ h, TripAvoids (bridgeGraph b s γ) ((bridgeGraph b s γ).leg x)
          ⟨.up z (top s z), h⟩)) := by
  have hut : prev s y (τ + 1) < top s y := prev_lt_top hmem
  have hnx : next s y (prev s y (τ + 1)) = τ + 1 := next_prev hmem
  obtain ⟨z, hz, hzm, hnl, hT2⟩ := tripMap_tripMap_dn hs γ hut hD
  rw [hnx] at hz hzm hT2
  have hl2 : ∀ w, ((bridgeGraph b s γ).tripMap ((bridgeGraph b s γ).tripMap
      ⟨.dn y (prev s y (τ + 1)), hD⟩)).1 ≠ .dn w 0 := by
    intro w
    rw [hT2]
    split_ifs <;> simp
  have av := (hav.step (bridgeGraph_not_isLeg γ hnl)).step (bridgeGraph_not_isLeg γ hl2)
  refine ⟨z, hz, ?_⟩
  by_cases htz : τ + 1 < top s z
  · have hdart : IsDart s (.dn z (prev s z (τ + 1 + 1))) := by
      rw [prev_succ_of_mem hzm]
      exact Or.inr ⟨hzm, htz⟩
    refine Or.inl ⟨htz, hdart, ?_⟩
    have e : (bridgeGraph b s γ).tripMap ((bridgeGraph b s γ).tripMap
        ⟨.dn y (prev s y (τ + 1)), hD⟩) = ⟨.dn z (prev s z (τ + 1 + 1)), hdart⟩ :=
      Subtype.ext ((hT2.trans (if_pos htz)).trans
        (congrArg (BridgeSymbol.dn z) (prev_succ_of_mem hzm).symm))
    rw [← e]
    exact av
  · have htop : top s z = τ + 1 := le_antisymm (not_lt.1 htz) (le_top hzm)
    have hdart : IsDart s (.up z (top s z)) := by
      rw [htop]
      exact hzm
    refine Or.inr ⟨by omega, hdart, ?_⟩
    have e : (bridgeGraph b s γ).tripMap ((bridgeGraph b s γ).tripMap
        ⟨.dn y (prev s y (τ + 1)), hD⟩) = ⟨.up z (top s z), hdart⟩ :=
      Subtype.ext ((hT2.trans (if_neg htz)).trans
        (congrArg (BridgeSymbol.up z) htop.symm))
    rw [← e]
    exact av

/-- The trip from the leg `g_x` at a line position, followed up to height `τ`: it is on the line of
`y`, with `y + 1 = (τ_τ ∘ ⋯ ∘ τ₁)(x + 1)`, at a `dn` dart below `m_y` or at the top `up` dart. -/
private theorem exists_tripAvoids_of_le_length (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) {x : Fin b} (hne : (heights s x).Nonempty) :
    ∀ τ ≤ s.length, ∃ y : Fin b, (y : ℤ) + 1 = positionMap s τ ((x : ℤ) + 1) ∧
      ((τ < top s y ∧ ∃ h, TripAvoids (bridgeGraph b s γ) ((bridgeGraph b s γ).leg x)
          ⟨.dn y (prev s y (τ + 1)), h⟩) ∨
        (top s y ≤ τ ∧ ∃ h, TripAvoids (bridgeGraph b s γ) ((bridgeGraph b s γ).leg x)
          ⟨.up y (top s y), h⟩)) := by
  intro τ
  induction τ with
  | zero =>
    intro _
    have hp : prev s x (0 + 1) = 0 := Nat.lt_one_iff.1 (prev_lt (by norm_num))
    refine ⟨x, by simp, Or.inl ⟨top_pos_iff.2 hne, Or.inl hp, ?_⟩⟩
    have e : (⟨.dn x (prev s x (0 + 1)), Or.inl hp⟩ : BridgeDart b s) =
        (bridgeGraph b s γ).leg x := Subtype.ext (congrArg (BridgeSymbol.dn x) hp)
    rw [e]
    exact TripAvoids.refl _
  | succ τ ih =>
    intro hτ
    have hlt : τ < s.length := by omega
    obtain ⟨y, hy, hA | hB⟩ := ih (by omega)
    · obtain ⟨hlt', hD, hav⟩ := hA
      have hpm : positionMap s (τ + 1) ((x : ℤ) + 1) =
          Equiv.swap (pair s (τ + 1)).1 (pair s (τ + 1)).2 ((y : ℤ) + 1) := by
        rw [positionMap_succ hlt, Equiv.Perm.mul_apply, ← hy, pair_succ hlt]
      by_cases hmem : τ + 1 ∈ heights s y
      · obtain ⟨z, hz, h⟩ := exists_tripAvoids_succ_of_mem hs γ hmem hD hav
        exact ⟨z, hz.trans hpm.symm, h⟩
      · obtain ⟨e1, e2⟩ := ne_of_notMem_heights hmem (by omega) hτ
        have hney : (heights s y).Nonempty := top_pos_iff.1 (by omega)
        have htop : τ + 1 < top s y := lt_of_le_of_ne hlt' fun h => hmem (by
          rw [h]
          exact top_mem hney)
        refine ⟨y, by rw [hpm, Equiv.swap_apply_of_ne_of_ne e1 e2], Or.inl ⟨htop, ?_⟩⟩
        have hp : prev s y (τ + 1 + 1) = prev s y (τ + 1) := prev_succ_of_notMem hmem
        have hdart : IsDart s (.dn y (prev s y (τ + 1 + 1))) := by
          rw [hp]
          exact hD
        refine ⟨hdart, ?_⟩
        have e : (⟨.dn y (prev s y (τ + 1 + 1)), hdart⟩ : BridgeDart b s) =
            ⟨.dn y (prev s y (τ + 1)), hD⟩ := Subtype.ext (congrArg (BridgeSymbol.dn y) hp)
        rw [e]
        exact hav
    · obtain ⟨htop, hB⟩ := hB
      have hnot : τ + 1 ∉ heights s y := notMem_heights_of_top_lt (by omega)
      obtain ⟨e1, e2⟩ := ne_of_notMem_heights hnot (by omega) hτ
      refine ⟨y, ?_, Or.inr ⟨by omega, hB⟩⟩
      rw [positionMap_succ hlt, Equiv.Perm.mul_apply, ← hy, ← pair_succ hlt,
        Equiv.swap_apply_of_ne_of_ne e1 e2]

/-- A trip from the leg `g_x` reaching an `up` dart on the line of `y` without meeting a leg ends
at the boundary vertex `y`. -/
private theorem tripPerm_eq_of_tripAvoids_up (γ : Fin b → Shade)
    (hinj : Function.Injective (bridgeGraph b s γ).leg) {x y : Fin b} (u : ℕ)
    (hu : u ∈ heights s y) (hav : TripAvoids (bridgeGraph b s γ) ((bridgeGraph b s γ).leg x)
      ⟨.up y u, hu⟩) :
    (bridgeGraph b s γ).tripPerm x = y := by
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    have hv : prev s y u = 0 ∨ prev s y u ∈ heights s y := prev_eq_zero_or_mem y u
    obtain ⟨d1, d2⟩ := tripMap_bridgeGraph_up γ hv (prev_lt_top hu) (next_prev hu) hu
    rcases eq_or_ne (prev s y u) 0 with h0 | h0
    · exact tripPerm_eq_of_tripAvoids hav (Subtype.ext (d2 h0)) hinj
    · have hmem := hv.resolve_left h0
      have e : (bridgeGraph b s γ).tripMap ⟨.up y u, hu⟩ = ⟨.up y (prev s y u), hmem⟩ :=
        Subtype.ext (d1 h0)
      have av := hav.step (by rw [e]; exact bridgeGraph_not_isLeg γ (by simp))
      rw [e] at av
      exact ih _ (prev_lt (pos_of_mem_heights hu)) hmem av

/-- **The trip permutation of the bridge graph.** Let `s` be a sequence of pairs of integers
with `1 ≤ i_t < j_t ≤ b`, let `γ : [1, b] → Shade`, and let `τ_t` be the transposition exchanging
`i_t` and `j_t`. Then the trip permutation of `G(s, γ)` is `τ_r ∘ τ_{r-1} ∘ ⋯ ∘ τ₁`: in
`0`-indexed labels, `π_G(x) + 1 = (τ_r ∘ ⋯ ∘ τ₁)(x + 1)`, the composite being the position map
`positionMap s r`. -/
@[cluster_algebras "lem_bridge_graph_trip_permutation"]
theorem tripPerm_bridgeGraph (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (γ : Fin b → Shade)
    (x : Fin b) :
    (((bridgeGraph b s γ).tripPerm x : ℕ) : ℤ) + 1 = positionMap s s.length ((x : ℤ) + 1) := by
  have hinj : Function.Injective (bridgeGraph b s γ).leg := fun i j h => by
    simpa using congrArg Subtype.val h
  by_cases hx : heights s x = ∅
  · obtain ⟨h1, h2⟩ := tripMap_bridgeGraph_lollipop γ hx
    have e1 : (bridgeGraph b s γ).tripMap ((bridgeGraph b s γ).leg x) = ⟨.lam x, hx⟩ :=
      Subtype.ext h1
    have hT : TripAvoids (bridgeGraph b s γ) ((bridgeGraph b s γ).leg x)
        ((bridgeGraph b s γ).tripMap ((bridgeGraph b s γ).leg x)) :=
      (TripAvoids.refl _).step (by rw [e1]; exact bridgeGraph_not_isLeg γ (by simp))
    have := tripPerm_eq_of_tripAvoids hT (by rw [e1]; exact Subtype.ext h2) hinj
    rw [this, positionMap_apply_of_forall_ne]
    intro u hu
    have := ne_of_notMem_heights (by rw [hx]; exact notMem_empty (u + 1)) (by omega)
      (show u + 1 ≤ s.length by omega)
    rwa [pair_succ hu] at this
  · obtain ⟨y, hy, hA | ⟨-, hup, hav⟩⟩ :=
      exists_tripAvoids_of_le_length hs γ (nonempty_iff_ne_empty.2 hx) s.length le_rfl
    · exact absurd (top_le_length (s := s) y) (by omega)
    · rw [tripPerm_eq_of_tripAvoids_up γ hinj _ hup hav]
      exact hy

end Trips

/-! ### Bridge decompositions -/

namespace DecoratedPerm

variable {b : ℕ}

/-- The **bridge decomposition** `G(π̃, s)` of a decorated permutation `π̃ = (π, ε)` along a
sequence of pairs `s`: the bridge graph `G(s, γ)` for the colouring `γ(x) = ε(x)` if `π(x) = x`
and `γ(x) = black` otherwise. -/
@[cluster_algebras "def_bridge_decomposition"]
def bridgeDecomposition (π : DecoratedPerm b) (s : List (ℤ × ℤ)) :
    PlabicData (BridgeDart b s) b :=
  bridgeGraph b s fun x => if h : π.perm x = x then π.colour ⟨x, h⟩ else .black

/-- The bridge decomposition `G(π̃, s)` is the bridge graph for the colouring `γ(x) = ε(x)` if
`π(x) = x` and `γ(x) = black` otherwise. -/
theorem bridgeDecomposition_eq (π : DecoratedPerm b) (s : List (ℤ × ℤ)) :
    π.bridgeDecomposition s =
      bridgeGraph b s fun x => if h : π.perm x = x then π.colour ⟨x, h⟩ else .black :=
  rfl

/-- **A bridge decomposition is a plabic graph**: if `b ≥ 1` and `s` is a bridge sequence for the
affinization of `π̃`, then `G(π̃, s)` is a plabic graph with `b` boundary vertices. -/
@[cluster_algebras "lem_bridge_decomposition_plabic"]
theorem isPlabicGraph_bridgeDecomposition (hb : 1 ≤ b) (π : DecoratedPerm b)
    {s : List (ℤ × ℤ)} (hs : IsBridgeSequence b π.affinization s) :
    (π.bridgeDecomposition s).IsPlabicGraph :=
  isPlabicGraph_bridgeGraph hb (fun p hp => by
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hp
      have h := hs.isBridgePair t ht
      exact ⟨h.one_le, h.lt, h.le⟩)
    hs.isNestedPairSequence _

end DecoratedPerm

end ClusterAlgebras

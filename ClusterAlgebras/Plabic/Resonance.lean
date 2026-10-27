/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CyclicallyIncreasing
public import ClusterAlgebras.Plabic.Excision
public import ClusterAlgebras.Plabic.SquareTrips
public import ClusterAlgebras.Plabic.TripRuns

/-!
# The resonance property

A plabic graph `G` has the *resonance property* if at every internal vertex `v` that is not a
lollipop, with darts `d₁, σ(d₁), …, σ^{m-1}(d₁)`, we have `m ≥ 2` and there are labels
`i₁ < i₂ < ⋯ < i_m` such that, listing the darts of `v` clockwise from a suitable one, their edges
carry the labels `{i₁, i₂}, {i₂, i₃}, …, {i_{m-1}, i_m}, {i₁, i_m}` in this order. Here the label
`λ(d)` of the edge of a dart `d` is the set of one-way trips traversing it.

At a vertex satisfying the resonance condition every label has two elements, and for `m ≥ 3` the
labels of distinct darts are distinct. Through the corner trip sets `cr(e)` (the one-way trip
turning in the corner clockwise after `e`), the condition says that every corner is turned by
exactly one one-way trip and that these trips, read clockwise, form a cyclically increasing
sequence.

The resonance property is preserved by isomorphisms and by square moves, and it fails in the
presence of a hollow digon.

## Main definitions

* `ClusterAlgebras.PlabicData.ResonanceCondition`: the resonance condition at a vertex.
* `ClusterAlgebras.PlabicData.HasResonanceProperty`: the resonance property.

## Main results

* `ClusterAlgebras.PlabicData.ResonanceCondition.card_edgeLabel`,
  `ClusterAlgebras.PlabicData.ResonanceCondition.injOn_edgeLabel`: at a vertex satisfying the
  resonance condition every label has two elements, and distinct darts have distinct labels if the
  vertex has at least three darts.
* `ClusterAlgebras.PlabicData.ResonanceCondition.of_edgeLabel_eq`: the resonance condition depends
  only on the number of darts and on the sequence of labels read around the vertex.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.resonanceCondition_iff_cornerTripSet`: the resonance
  condition through corners.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.hasResonanceProperty_iff_of_isomorphic`: isomorphisms
  preserve resonance.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.hasResonanceProperty_iff_squareMove`: square moves
  preserve resonance.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.not_hasResonanceProperty_of_isHollowDigon`: a hollow
  digon violates resonance.

## Implementation notes

* **Labels.** The label set `[1, b]` of [FWZ] is `Fin b`, `0`-indexed: the element `i : Fin b`
  is the label `i + 1` of [FWZ]. The order of `Fin b` is that of the labels, so increasing
  integers `i₁ < ⋯ < i_m` are a strictly monotone map `i : Fin m → Fin b`, and the label
  `{i_k, i_{k+1}}` of the `k`-th dart (with `i_{m+1} = i_1`) is `{i k, i (finRotate m k)}`.
* **The starting dart.** [FWZ] lists the darts clockwise from `σ^r(d₁)` for an index `r`;
  since the darts `σ^r(d₁)` are exactly the darts of the vertex, the condition is stated with an
  arbitrary dart `d` of the vertex as the first one, the `k`-th dart being `σ^{-k}(d)`.
* **Vertices.** `ResonanceCondition` is defined for any finite set of darts; it is meant for the
  vertices of the graph, which are the sets `vertexOf d`.
* **Superfluous hypotheses.** The resonance condition at a vertex does not depend on whether the
  vertex is a lollipop, so `IsPlabicGraph.resonanceCondition_iff_cornerTripSet` is stated for
  every internal vertex.
* **Corner sequences.** In `IsPlabicGraph.resonanceCondition_iff_cornerTripSet` the sequence
  `(c₁, …, c_m)` with `cr(σ^{-(k-1)}(e₁)) = {c_k}` is a map `c : Fin m → Fin b`, read as the list
  `List.ofFn c`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Function

/-! ### Orbits of a permutation of known size -/

section Orbit

variable {H : Type*} [Fintype H] [DecidableEq H] {f : Perm H} {d : H} {n : ℕ}

private theorem pow_apply_inj_of_card (hcard : (univ.filter (f.SameCycle d)).card = n)
    {i j : ℕ} (hi : i < n) (hj : j < n) (h : (f ^ i) d = (f ^ j) d) : i = j := by
  wlog hij : i < j generalizing i j
  · rcases Nat.lt_or_ge j i with h' | h'
    · exact (this hj hi h.symm h').symm
    · omega
  have hper : (f ^ (j - i)) ((f ^ i) d) = (f ^ i) d := by
    rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hij.le]
    exact h.symm
  have hve : univ.filter (f.SameCycle ((f ^ i) d)) = univ.filter (f.SameCycle d) := by
    ext x
    simp [Perm.sameCycle_pow_left]
  generalize (f ^ i) d = e at hper hve
  have hsub : univ.filter (f.SameCycle e) ⊆ (range (j - i)).image fun k => (f ^ k) e := by
    intro x hx
    obtain ⟨N, hN⟩ := (mem_filter.1 hx).2.exists_nat_pow_eq
    have hpp : IsPeriodicPt f (j - i) e := by
      change (⇑f)^[j - i] e = e
      rw [Perm.iterate_eq_pow, hper]
    have hmod := hpp.iterate_mod_apply N
    rw [Perm.iterate_eq_pow, Perm.iterate_eq_pow] at hmod
    exact mem_image.2 ⟨N % (j - i), mem_range.2 (Nat.mod_lt _ (by omega)), hmod.trans hN⟩
  have := (card_le_card hsub).trans card_image_le
  rw [hve, hcard, card_range] at this
  omega

private theorem exists_pow_apply_eq_of_card (hcard : (univ.filter (f.SameCycle d)).card = n)
    {e : H} (he : f.SameCycle d e) : ∃ k < n, (f ^ k) d = e := by
  have hsub : (range n).image (fun k => (f ^ k) d) ⊆ univ.filter (f.SameCycle d) := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := mem_image.1 hx
    exact mem_filter.2 ⟨mem_univ _, Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)⟩
  have hcardim : ((range n).image (fun k => (f ^ k) d)).card = n := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    exact pow_apply_inj_of_card hcard (mem_range.1 hi) (mem_range.1 hj) h
  have heq := eq_of_subset_of_card_le hsub (by rw [hcard, hcardim])
  have he' : e ∈ univ.filter (f.SameCycle d) := mem_filter.2 ⟨mem_univ _, he⟩
  rw [← heq] at he'
  obtain ⟨k, hk, rfl⟩ := mem_image.1 he'
  exact ⟨k, mem_range.1 hk, rfl⟩

private theorem pow_card_apply_of_card (hcard : (univ.filter (f.SameCycle d)).card = n) :
    (f ^ n) d = d := by
  have hpos : 0 < n := by
    rw [← hcard]
    exact card_pos.2 ⟨d, mem_filter.2 ⟨mem_univ _, Perm.SameCycle.refl _ _⟩⟩
  obtain ⟨k, hk, hkd⟩ := exists_pow_apply_eq_of_card hcard
    (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl f d) : f.SameCycle d ((f ^ n) d))
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa using hkd.symm
  · exfalso
    have h1 : (f ^ k) ((f ^ (n - k)) d) = (f ^ k) d := by
      rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hk.le, hkd]
    have h2 : (f ^ (n - k)) d = (f ^ 0) d := by
      rw [pow_zero, Perm.one_apply]
      exact (f ^ k).injective h1
    have := pow_apply_inj_of_card hcard (by omega) hpos h2
    omega

end Orbit

namespace RotationSystem

variable {H : Type*} [Fintype H] [DecidableEq H] {R : RotationSystem H}

private theorem filter_sameCycle_rot_symm (d : H) :
    univ.filter (Perm.SameCycle R.rot.symm d) = R.vertexOf d := by
  ext e
  rw [mem_filter, RotationSystem.mem_vertexOf]
  exact ⟨fun h => Perm.sameCycle_inv.1 h.2, fun h => ⟨mem_univ _, Perm.sameCycle_inv.2 h⟩⟩

private theorem rot_symm_pow_mem_vertexOf (d : H) (n : ℕ) : (R.rot.symm ^ n) d ∈ R.vertexOf d := by
  rw [← filter_sameCycle_rot_symm]
  exact mem_filter.2 ⟨mem_univ _, Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)⟩

private theorem vertexOf_rot_symm_pow (d : H) (n : ℕ) :
    R.vertexOf ((R.rot.symm ^ n) d) = R.vertexOf d :=
  R.vertexOf_eq_of_mem (rot_symm_pow_mem_vertexOf d n)

/-- Every dart of the vertex of `d` is `σ^{-k}(d)` for some `k` less than the number of darts. -/
private theorem exists_rot_symm_pow_eq {d e : H} (he : e ∈ R.vertexOf d) :
    ∃ k < (R.vertexOf d).card, (R.rot.symm ^ k) d = e := by
  rw [← filter_sameCycle_rot_symm] at he ⊢
  exact exists_pow_apply_eq_of_card rfl (mem_filter.1 he).2

private theorem rot_symm_pow_card (d : H) : (R.rot.symm ^ (R.vertexOf d).card) d = d := by
  rw [← filter_sameCycle_rot_symm]
  exact pow_card_apply_of_card rfl

private theorem rot_symm_pow_mod (d : H) (n : ℕ) :
    (R.rot.symm ^ (n % (R.vertexOf d).card)) d = (R.rot.symm ^ n) d := by
  have hpp : IsPeriodicPt R.rot.symm (R.vertexOf d).card d := by
    change (⇑R.rot.symm)^[_] d = d
    rw [Perm.iterate_eq_pow, rot_symm_pow_card]
  have := hpp.iterate_mod_apply n
  rwa [Perm.iterate_eq_pow, Perm.iterate_eq_pow] at this

omit [Fintype H] [DecidableEq H] in
private theorem rot_rot_symm_pow_succ (d : H) (n : ℕ) :
    R.rot ((R.rot.symm ^ (n + 1)) d) = (R.rot.symm ^ n) d := by
  rw [pow_succ', Perm.mul_apply, Equiv.apply_symm_apply]

end RotationSystem

/-! ### Arithmetic modulo the number of darts -/

private theorem mod_ne_add_mod {m n j : ℕ} (hj : 0 < j) (hjm : j < m) : n % m ≠ (n + j) % m := by
  rw [← Nat.mod_add_mod n m j]
  have hr : n % m < m := Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_ge (n % m + j) m with h | h
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show n % m + j - m < m by omega)]
    omega

private theorem val_finRotate {m : ℕ} (k : Fin m) : (finRotate m k : ℕ) = (k + 1) % m := by
  cases m with
  | zero => exact k.elim0
  | succ n =>
    rw [coe_finRotate]
    split_ifs with h
    · subst h
      simp
    · have := Fin.val_lt_last h
      rw [Nat.mod_eq_of_lt (by omega)]

/-- The class of `n` modulo `m`, as an element of `Fin m`. -/
private def finMod {m : ℕ} (hm : 0 < m) (n : ℕ) : Fin m := ⟨n % m, Nat.mod_lt _ hm⟩

private theorem finMod_add_self {m : ℕ} (hm : 0 < m) (n : ℕ) :
    finMod hm (n + m) = finMod hm n :=
  Fin.ext (Nat.add_mod_right n m)

private theorem finMod_ne {m : ℕ} (hm : 0 < m) (n : ℕ) {j : ℕ} (hj : 0 < j) (hjm : j < m) :
    finMod hm n ≠ finMod hm (n + j) :=
  fun h => mod_ne_add_mod hj hjm (congrArg Fin.val h)

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-! ### The resonance condition -/

/-- The **resonance condition** at a vertex `v`: `v` has `m ≥ 2` darts, and for some dart `d` of
`v` and labels `i₁ < ⋯ < i_m` (a strictly monotone `i : Fin m → Fin b`), the darts
`d, σ^{-1}(d), …, σ^{-(m-1)}(d)` of `v`, listed clockwise, have the labels
`{i₁, i₂}, {i₂, i₃}, …, {i_{m-1}, i_m}, {i₁, i_m}` in this order. Labels are `0`-indexed:
`i : Fin b` stands for the boundary label `i + 1` in `{1, …, b}`. -/
@[cluster_algebras "def_resonance"]
def ResonanceCondition (v : Finset H) : Prop :=
  2 ≤ v.card ∧ ∃ d ∈ v, ∃ i : Fin v.card → Fin b, StrictMono i ∧
    ∀ k : Fin v.card,
      G.edgeLabel (G.edgeOf ((G.rot.symm ^ (k : ℕ)) d)) = {i k, i (finRotate _ k)}

/-- The **resonance property**: the resonance condition holds at every internal vertex that is not
a lollipop. -/
@[cluster_algebras "def_resonance"]
def HasResonanceProperty : Prop :=
  ∀ v ∈ G.internalVertices, (∀ i, ¬G.IsLollipop i v) → G.ResonanceCondition v

variable {G}

/-- The resonance condition read along the rotation: the label of `σ^{-n}(d)` is
`{i_{n mod m}, i_{(n+1) mod m}}` for every `n`. -/
private theorem ResonanceCondition.exists_nat {a : H} (h : G.ResonanceCondition (G.vertexOf a))
    (hpos : 0 < (G.vertexOf a).card) :
    ∃ d ∈ G.vertexOf a, ∃ i : Fin (G.vertexOf a).card → Fin b, StrictMono i ∧
      ∀ n : ℕ, G.edgeLabel (G.edgeOf ((G.rot.symm ^ n) d)) =
        {i (finMod hpos n), i (finMod hpos (n + 1))} := by
  obtain ⟨-, d, hd, i, hi, hl⟩ := h
  refine ⟨d, hd, i, hi, fun n => ?_⟩
  have hvd : G.vertexOf d = G.vertexOf a := G.vertexOf_eq_of_mem hd
  have h1 := hl (finMod hpos n)
  have h2 : (G.rot.symm ^ ((finMod hpos n : Fin _) : ℕ)) d = (G.rot.symm ^ n) d := by
    have := RotationSystem.rot_symm_pow_mod (R := G.toRotationSystem) d n
    rwa [hvd] at this
  rw [h2] at h1
  rw [h1, show finRotate _ (finMod hpos n) = finMod hpos (n + 1) from
    Fin.ext (by simp only [finMod, val_finRotate, Nat.mod_add_mod])]

/-- At a vertex satisfying the resonance condition, every dart has a label with exactly two
elements. -/
theorem ResonanceCondition.card_edgeLabel {a : H} (h : G.ResonanceCondition (G.vertexOf a))
    {e : H} (he : e ∈ G.vertexOf a) : (G.edgeLabel (G.edgeOf e)).card = 2 := by
  have hm := h.1
  obtain ⟨d, hd, i, hi, hl⟩ := h.exists_nat (by omega)
  have hvd : G.vertexOf d = G.vertexOf a := G.vertexOf_eq_of_mem hd
  rw [← hvd] at he
  obtain ⟨k, -, rfl⟩ := RotationSystem.exists_rot_symm_pow_eq he
  rw [hl, card_pair (hi.injective.ne (finMod_ne _ k one_pos (by omega)))]

/-- At a vertex with at least three darts satisfying the resonance condition, distinct darts have
distinct labels. -/
theorem ResonanceCondition.injOn_edgeLabel {a : H} (h : G.ResonanceCondition (G.vertexOf a))
    (h3 : 3 ≤ (G.vertexOf a).card) :
    Set.InjOn (fun e => G.edgeLabel (G.edgeOf e)) (G.vertexOf a : Set H) := by
  have hpos : 0 < (G.vertexOf a).card := by omega
  obtain ⟨d, hd, i, hi, hl⟩ := h.exists_nat hpos
  have hvd : G.vertexOf d = G.vertexOf a := G.vertexOf_eq_of_mem hd
  intro e he e' he' hee'
  simp only [mem_coe, ← hvd] at he he'
  obtain ⟨k, hk, rfl⟩ := RotationSystem.exists_rot_symm_pow_eq he
  obtain ⟨k', hk', rfl⟩ := RotationSystem.exists_rot_symm_pow_eq he'
  rw [hvd] at hk hk'
  simp only [hl] at hee'
  have hmem1 : i (finMod hpos k) ∈ ({i (finMod hpos k'), i (finMod hpos (k' + 1))} : Finset _) :=
    hee' ▸ mem_insert_self _ _
  have hmem2 : i (finMod hpos (k + 1)) ∈
      ({i (finMod hpos k'), i (finMod hpos (k' + 1))} : Finset _) :=
    hee' ▸ mem_insert_of_mem (mem_singleton_self _)
  simp only [mem_insert, mem_singleton, hi.injective.eq_iff, finMod, Fin.mk.injEq] at hmem1 hmem2
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at hmem1
  rcases hmem1 with h1 | h1
  · rw [h1]
  · exfalso
    rcases hmem2 with h2 | h2
    · -- `k' ≡ k + 1 ≡ k' + 2`
      have h3' : k' % (G.vertexOf a).card = (k' + 2) % (G.vertexOf a).card := by
        rw [← h2, h1, Nat.mod_add_mod]
      exact mod_ne_add_mod (m := (G.vertexOf a).card) (n := k') (j := 2) two_pos (by omega) h3'
    · have := (Nat.ModEq.add_right_cancel' 1 h2 : k ≡ k' [MOD _])
      unfold Nat.ModEq at this
      rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at this
      subst this
      exact mod_ne_add_mod (m := (G.vertexOf a).card) (n := k) (j := 1) one_pos (by omega)
        (by rwa [Nat.mod_eq_of_lt hk])

/-- **Transfer of the resonance condition.** If two vertices `v(a)` and `v(a')`, possibly of
different graphs, have the same number of darts, and the labels of `σ^{-n}(a)` and `σ'^{-n}(a')`
agree for every `n`, then the resonance condition at `v(a)` implies that at `v(a')`. -/
theorem ResonanceCondition.of_edgeLabel_eq {H' : Type*} [Fintype H'] [DecidableEq H']
    {G' : PlabicData H' b} {a : H} {a' : H'}
    (hcard : (G'.vertexOf a').card = (G.vertexOf a).card)
    (hlab : ∀ n : ℕ, G'.edgeLabel (G'.edgeOf ((G'.rot.symm ^ n) a')) =
      G.edgeLabel (G.edgeOf ((G.rot.symm ^ n) a)))
    (h : G.ResonanceCondition (G.vertexOf a)) : G'.ResonanceCondition (G'.vertexOf a') := by
  obtain ⟨h2, d, hd, i, hi, hl⟩ := h
  obtain ⟨j, -, rfl⟩ := RotationSystem.exists_rot_symm_pow_eq hd
  refine ⟨hcard ▸ h2, (G'.rot.symm ^ j) a', RotationSystem.rot_symm_pow_mem_vertexOf _ _,
    fun k => i (Fin.cast hcard k), fun x y hxy => hi (show Fin.cast hcard x < Fin.cast hcard y
      from hxy), fun k => ?_⟩
  rw [← Perm.mul_apply, ← pow_add, hlab, pow_add, Perm.mul_apply]
  have := hl (Fin.cast hcard k)
  rw [Fin.val_cast] at this
  rw [this, show finRotate _ (Fin.cast hcard k) = Fin.cast hcard (finRotate _ k) from
    Fin.ext (by simp only [Fin.val_cast, val_finRotate, hcard])]

/-! ### Corners -/

/-- A corner trip set has at most one element. -/
private theorem IsPlabicGraph.card_cornerTripSet_le_one (hG : G.IsPlabicGraph) (e : H) :
    (G.cornerTripSet e).card ≤ 1 := by
  cases hc : G.colour e
  · rw [cornerTripSet_of_white hc]
    exact hG.card_tripSet_le_one _
  · rw [cornerTripSet_of_black hc]
    exact hG.card_tripSet_le_one _

/-- The darts of a vertex are stable under `σ^{-n}`. -/
private theorem rot_symm_pow_mem_of_mem {a e : H} (he : e ∈ G.vertexOf a) (n : ℕ) :
    (G.rot.symm ^ n) e ∈ G.vertexOf a := by
  have := RotationSystem.rot_symm_pow_mem_vertexOf (R := G.toRotationSystem) e n
  rwa [G.vertexOf_eq_of_mem he] at this

/-- At an internal vertex, the label of `σ^{-(n+1)}(e)` is the union of the corner trip sets of
`σ^{-(n+1)}(e)` and `σ^{-n}(e)`. -/
private theorem IsPlabicGraph.edgeLabel_rot_symm_pow_succ (hG : G.IsPlabicGraph) {a : H}
    (hx : G.vertexOf a ∈ G.internalVertices) {e : H} (he : e ∈ G.vertexOf a) (n : ℕ) :
    G.edgeLabel (G.edgeOf ((G.rot.symm ^ (n + 1)) e)) =
      G.cornerTripSet ((G.rot.symm ^ (n + 1)) e) ∪ G.cornerTripSet ((G.rot.symm ^ n) e) := by
  rw [hG.edgeLabel_edgeOf_eq_cornerTripSet_union, RotationSystem.rot_rot_symm_pow_succ]
  rw [RotationSystem.vertexOf_rot_symm_pow, G.vertexOf_eq_of_mem he]
  exact (G.mem_internalVertices.1 hx).2

/-- At an internal vertex satisfying the resonance condition, every corner trip set is a
singleton. -/
private theorem ResonanceCondition.card_cornerTripSet (hG : G.IsPlabicGraph) {a : H}
    (hx : G.vertexOf a ∈ G.internalVertices) (h : G.ResonanceCondition (G.vertexOf a)) {e : H}
    (he : e ∈ G.vertexOf a) : (G.cornerTripSet e).card = 1 := by
  have hm := h.1
  have hpos : 0 < (G.vertexOf a).card := by omega
  obtain ⟨d, hd, i, hi, hl⟩ := h.exists_nat hpos
  rw [← G.vertexOf_eq_of_mem hd] at he
  obtain ⟨n, -, rfl⟩ := RotationSystem.exists_rot_symm_pow_eq he
  have h2 : (G.edgeLabel (G.edgeOf ((G.rot.symm ^ (n + 1)) d))).card = 2 := by
    rw [hl, card_pair (hi.injective.ne (finMod_ne hpos _ one_pos (by omega)))]
  rw [hG.edgeLabel_rot_symm_pow_succ hx hd n] at h2
  have := card_union_le (G.cornerTripSet ((G.rot.symm ^ (n + 1)) d))
    (G.cornerTripSet ((G.rot.symm ^ n) d))
  have h1 := hG.card_cornerTripSet_le_one ((G.rot.symm ^ (n + 1)) d)
  have h1' := hG.card_cornerTripSet_le_one ((G.rot.symm ^ n) d)
  omega

/-- At an internal vertex with at least three darts satisfying the resonance condition, the corner
trip sets read clockwise form a cyclically increasing sequence. -/
private theorem ResonanceCondition.cyclicallyIncreasing_of_two_lt (hG : G.IsPlabicGraph) {a : H}
    (hx : G.vertexOf a ∈ G.internalVertices) (h : G.ResonanceCondition (G.vertexOf a))
    (hm3 : 2 < (G.vertexOf a).card) {e₁ : H} (he₁ : e₁ ∈ G.vertexOf a)
    {c : Fin (G.vertexOf a).card → Fin b}
    (hc : ∀ k : Fin (G.vertexOf a).card, G.cornerTripSet ((G.rot.symm ^ (k : ℕ)) e₁) = {c k}) :
    CyclicallyIncreasing (List.ofFn c) := by
  have hpos : 0 < (G.vertexOf a).card := by omega
  obtain ⟨d, hd, i, hi, hl⟩ := h.exists_nat hpos
  have hvd : G.vertexOf d = G.vertexOf a := G.vertexOf_eq_of_mem hd
  have hmod : ∀ n, (G.rot.symm ^ (n % (G.vertexOf a).card)) d = (G.rot.symm ^ n) d :=
    fun n => hvd ▸ RotationSystem.rot_symm_pow_mod (R := G.toRotationSystem) d n
  have hcrF : ∀ n : ℕ, G.cornerTripSet ((G.rot.symm ^ (n + 1)) d) =
      {i (finMod hpos (n + 1 + 1))} := by
    intro n
    obtain ⟨u, hu⟩ :=
      card_eq_one.1 (h.card_cornerTripSet hG hx (G.rot_symm_pow_mem_of_mem hd (n + 1)))
    have hu1 : u ∈ G.edgeLabel (G.edgeOf ((G.rot.symm ^ (n + 1)) d)) := by
      rw [hG.edgeLabel_rot_symm_pow_succ hx hd n, hu]
      exact mem_union_left _ (mem_singleton_self _)
    have hu2 : u ∈ G.edgeLabel (G.edgeOf ((G.rot.symm ^ (n + 1 + 1)) d)) := by
      rw [hG.edgeLabel_rot_symm_pow_succ hx hd (n + 1), hu]
      exact mem_union_right _ (mem_singleton_self _)
    rw [hl] at hu1 hu2
    rw [hu]
    simp only [mem_insert, mem_singleton] at hu1 hu2
    rcases hu1 with rfl | rfl
    · exfalso
      rcases hu2 with h' | h'
      · exact finMod_ne hpos (n + 1) one_pos (by omega) (hi.injective h')
      · exact finMod_ne hpos (n + 1) (j := 2) two_pos (by omega) (hi.injective h')
    · rfl
  have hcr : ∀ n : ℕ, G.cornerTripSet ((G.rot.symm ^ n) d) = {i (finMod hpos (n + 1))} := by
    intro n
    have e1 : (G.rot.symm ^ n) d = (G.rot.symm ^ (n + (G.vertexOf a).card - 1 + 1)) d := by
      rw [← hmod (n + (G.vertexOf a).card - 1 + 1), Nat.sub_add_cancel (by omega),
        Nat.add_mod_right, hmod]
    rw [e1, hcrF]
    congr 2
    rw [show n + (G.vertexOf a).card - 1 + 1 + 1 = n + 1 + (G.vertexOf a).card by omega,
      finMod_add_self]
  rw [← hvd] at he₁
  obtain ⟨t, -, rfl⟩ := RotationSystem.exists_rot_symm_pow_eq he₁
  have hck : ∀ k : Fin (G.vertexOf a).card, c k = i (finMod hpos (k + t + 1)) := fun k =>
    singleton_inj.1 <| by rw [← hc k, ← Perm.mul_apply, ← pow_add, hcr]
  have hcycI : CyclicallyIncreasing (List.ofFn i) :=
    ⟨0, by rw [List.length_ofFn]; omega, by rwa [List.rotate_zero, List.sortedLT_ofFn_iff]⟩
  have heq : List.ofFn c = (List.ofFn i).rotate (t + 1) := by
    refine List.ext_getElem (by simp) fun n h1 h2 => ?_
    simp only [List.getElem_ofFn, List.getElem_rotate, List.length_ofFn]
    rw [hck]
    congr 1
  exact heq ▸ hcycI.rotate _

/-- At an internal vertex with two darts satisfying the resonance condition, the two corner trip
sets read clockwise form a cyclically increasing sequence. -/
private theorem ResonanceCondition.cyclicallyIncreasing_of_card_eq_two (hG : G.IsPlabicGraph)
    {a : H} (hx : G.vertexOf a ∈ G.internalVertices) (h : G.ResonanceCondition (G.vertexOf a))
    (hm2 : (G.vertexOf a).card = 2) {e₁ : H} (he₁ : e₁ ∈ G.vertexOf a)
    {c : Fin (G.vertexOf a).card → Fin b}
    (hc : ∀ k : Fin (G.vertexOf a).card, G.cornerTripSet ((G.rot.symm ^ (k : ℕ)) e₁) = {c k}) :
    CyclicallyIncreasing (List.ofFn c) := by
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 (by rwa [List.length_ofFn] :
    (List.ofFn c).length = 2)
  have hp : c ⟨0, by omega⟩ = p := by
    have : (List.ofFn c)[0]'(by rw [List.length_ofFn]; omega) = p := by simp [hpq]
    rwa [List.getElem_ofFn] at this
  have hq : c ⟨1, by omega⟩ = q := by
    have : (List.ofFn c)[1]'(by rw [List.length_ofFn]; omega) = q := by simp [hpq]
    rwa [List.getElem_ofFn] at this
  have hlab := h.card_edgeLabel (G.rot_symm_pow_mem_of_mem he₁ (0 + 1))
  rw [hG.edgeLabel_rot_symm_pow_succ hx he₁ 0] at hlab
  have h1 := hc ⟨1, by omega⟩
  have h0 := hc ⟨0, by omega⟩
  simp only at h1 h0
  rw [h1, h0, hp, hq] at hlab
  rw [hpq]
  refine cyclicallyIncreasing_pair fun hpq' => ?_
  rw [hpq', union_self, card_singleton] at hlab
  omega

/-- At an internal vertex with at least two darts, singleton corner trip sets forming a cyclically
increasing sequence give the resonance condition. -/
private theorem IsPlabicGraph.resonanceCondition_of_cornerTripSet (hG : G.IsPlabicGraph) {a : H}
    (hx : G.vertexOf a ∈ G.internalVertices) (hm : 2 ≤ (G.vertexOf a).card)
    {c : Fin (G.vertexOf a).card → Fin b}
    (hc : ∀ k : Fin (G.vertexOf a).card, G.cornerTripSet ((G.rot.symm ^ (k : ℕ)) a) = {c k})
    (hcyc : CyclicallyIncreasing (List.ofFn c)) : G.ResonanceCondition (G.vertexOf a) := by
  have hpos : 0 < (G.vertexOf a).card := by omega
  obtain ⟨s, hs, hsorted⟩ := hcyc
  have hcE : ∀ n : ℕ, G.cornerTripSet ((G.rot.symm ^ n) a) = {c (finMod hpos n)} := by
    intro n
    rw [← RotationSystem.rot_symm_pow_mod]
    exact hc (finMod hpos n)
  refine ⟨hm, (G.rot.symm ^ (s + 1)) a, RotationSystem.rot_symm_pow_mem_vertexOf _ _,
    fun k => c (finMod hpos (k + s)), fun k k' hkk' => ?_, fun k => ?_⟩
  · have := hsorted.strictMono_get
      (show (⟨(k : ℕ), by simp⟩ : Fin ((List.ofFn c).rotate s).length) < ⟨(k' : ℕ), by simp⟩
        from hkk')
    simpa [List.getElem_rotate, finMod] using this
  · beta_reduce
    rw [← Perm.mul_apply, ← pow_add, show (k : ℕ) + (s + 1) = k + s + 1 by omega,
      hG.edgeLabel_rot_symm_pow_succ hx (G.self_mem_vertexOf a), hcE, hcE,
      show finMod hpos ((finRotate _ k : ℕ) + s) = finMod hpos (k + s + 1) from
        Fin.ext (by simp only [finMod, val_finRotate, Nat.mod_add_mod]; congr 1; omega),
      union_comm, ← insert_eq]

/-- **The resonance condition through corners.** Let `x` be an internal vertex of a plabic graph
`G`, consisting of `m` darts. Then the resonance condition holds at `x` if and only if `m ≥ 2`, the
corner trip set `cr(e)` has exactly one element for every dart `e` of `x`, and for every dart `e₁`
of `x` the sequence `(c₁, …, c_m)` with `cr(σ^{-(k-1)}(e₁)) = {c_k}` is cyclically increasing. Here
the sequence is `c : Fin m → Fin b`, `0`-indexed, and labels are `0`-indexed: `i : Fin b` stands
for the boundary label `i + 1` in `{1, …, b}`. -/
@[cluster_algebras "lem_resonance_corners"]
theorem IsPlabicGraph.resonanceCondition_iff_cornerTripSet (hG : G.IsPlabicGraph)
    {x : Finset H} (hx : x ∈ G.internalVertices) :
    G.ResonanceCondition x ↔ 2 ≤ x.card ∧ (∀ e ∈ x, (G.cornerTripSet e).card = 1) ∧
      ∀ e₁ ∈ x, ∃ c : Fin x.card → Fin b,
        (∀ k : Fin x.card, G.cornerTripSet ((G.rot.symm ^ (k : ℕ)) e₁) = {c k}) ∧
          CyclicallyIncreasing (List.ofFn c) := by
  obtain ⟨a, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hx).1
  refine ⟨fun h => ⟨h.1, fun e he => h.card_cornerTripSet hG hx he, fun e₁ he₁ => ?_⟩,
    fun ⟨hm, _, hcyc⟩ => ?_⟩
  · have hE : ∀ k : Fin (G.vertexOf a).card,
        ∃ u, G.cornerTripSet ((G.rot.symm ^ (k : ℕ)) e₁) = {u} := fun k =>
      card_eq_one.1 (h.card_cornerTripSet hG hx (G.rot_symm_pow_mem_of_mem he₁ k))
    choose c hc using hE
    refine ⟨c, hc, ?_⟩
    rcases Nat.lt_or_ge 2 (G.vertexOf a).card with hm3 | hm2
    · exact h.cyclicallyIncreasing_of_two_lt hG hx hm3 he₁ hc
    · exact h.cyclicallyIncreasing_of_card_eq_two hG hx (by have := h.1; omega) he₁ hc
  · obtain ⟨c, hc, hcyc⟩ := hcyc a (G.self_mem_vertexOf a)
    exact hG.resonanceCondition_of_cornerTripSet hx hm hc hcyc

/-! ### Isomorphisms -/

section Iso

variable {H' : Type*} [Fintype H'] [DecidableEq H'] {G' : PlabicData H' b}

private theorem iso_map_rot_symm_pow (θ : G.Iso G') (n : ℕ) (d : H) :
    θ.toEquiv ((G.rot.symm ^ n) d) = (G'.rot.symm ^ n) (θ.toEquiv d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, pow_succ', Perm.mul_apply, ← ih]
    apply G'.rot.injective
    rw [← θ.map_rot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem iso_tripSet (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (θ : G.Iso G')
    (d : H) : G'.tripSet (θ.toEquiv d) = G.tripSet d := by
  let e : (Set.univ : Set H) ≃ (Set.univ : Set H') :=
    (Equiv.Set.univ H).trans (θ.toEquiv.trans (Equiv.Set.univ H').symm)
  have he : ∀ y, (e y : H') = θ.toEquiv y := fun y => rfl
  refine (hG.tripSet_eq_of_firstReturn hG' e
    (fun i => ⟨Set.mem_univ _, by rw [he]; exact Iso.map_leg hG hG' θ i⟩)
    (fun y => Subtype.ext ?_) ⟨d, Set.mem_univ _⟩).symm
  rw [he, coe_firstReturn_of_apply_mem (π := hG.tripEquiv) (Set.mem_univ _),
    coe_firstReturn_of_apply_mem (π := hG'.tripEquiv) (Set.mem_univ _), he]
  simpa only [IsPlabicGraph.tripEquiv_apply] using θ.map_tripMap _

private theorem iso_edgeLabel (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (θ : G.Iso G')
    (d : H) : G'.edgeLabel (G'.edgeOf (θ.toEquiv d)) = G.edgeLabel (G.edgeOf d) := by
  rw [edgeLabel_edgeOf, edgeLabel_edgeOf, ← θ.map_inv, iso_tripSet hG hG', iso_tripSet hG hG']

private theorem iso_mem_internalVertices (θ : G.Iso G') {v : Finset H}
    (hv : v ∈ G.internalVertices) : v.map θ.toEquiv.toEmbedding ∈ G'.internalVertices := by
  obtain ⟨hvV, hvB⟩ := G.mem_internalVertices.1 hv
  obtain ⟨d, rfl⟩ := G.mem_vertices.1 hvV
  rwa [θ.map_vertexOf, DiskMap.vertexOf_mem_internalVertices, θ.isBoundaryVertex_vertexOf_iff]

private theorem iso_isLollipop (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (θ : G.Iso G')
    {i : Fin b} {v : Finset H} (h : G.IsLollipop i v) :
    G'.IsLollipop i (v.map θ.toEquiv.toEmbedding) := by
  obtain ⟨⟨hv, hcard⟩, d, hd, hdi⟩ := h
  refine ⟨⟨iso_mem_internalVertices θ hv, by rw [card_map, hcard]⟩, θ.toEquiv d,
    mem_map_equiv.2 (by simpa using hd), ?_⟩
  rw [← θ.map_inv]
  have : (G.bvertex i).map θ.toEquiv.toEmbedding = G'.bvertex i := by
    rw [bvertex, bvertex, θ.map_vertexOf, Iso.map_leg hG hG' θ]
  rw [← this]
  exact mem_map_of_mem _ hdi

private theorem hasResonanceProperty_of_iso (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (θ : G.Iso G') (h : G.HasResonanceProperty) : G'.HasResonanceProperty := by
  intro w hw hlol
  obtain ⟨hwV, hwB⟩ := G'.mem_internalVertices.1 hw
  obtain ⟨a', rfl⟩ := G'.mem_vertices.1 hwV
  have ha : θ.toEquiv (θ.toEquiv.symm a') = a' := θ.toEquiv.apply_symm_apply a'
  have hmap : (G.vertexOf (θ.toEquiv.symm a')).map θ.toEquiv.toEmbedding = G'.vertexOf a' := by
    rw [θ.map_vertexOf, ha]
  have hint : G.vertexOf (θ.toEquiv.symm a') ∈ G.internalVertices := by
    rw [DiskMap.vertexOf_mem_internalVertices, ← θ.isBoundaryVertex_vertexOf_iff, ha]
    exact hwB
  have hres := h _ hint fun i hl => hlol i (by rw [← hmap]; exact iso_isLollipop hG hG' θ hl)
  refine hres.of_edgeLabel_eq (by rw [← hmap, card_map]) fun n => ?_
  conv_lhs => rw [← ha, ← iso_map_rot_symm_pow]
  rw [iso_edgeLabel hG hG']

/-- **Isomorphisms preserve resonance**: if the plabic graphs `G` and `G'` are isomorphic, then `G`
has the resonance property if and only if `G'` has. -/
@[cluster_algebras "lem_resonance_isomorphism"]
theorem IsPlabicGraph.hasResonanceProperty_iff_of_isomorphic (hG : G.IsPlabicGraph)
    (hG' : G'.IsPlabicGraph) (h : G.Isomorphic G') :
    G.HasResonanceProperty ↔ G'.HasResonanceProperty := by
  obtain ⟨θ⟩ := h
  exact ⟨hasResonanceProperty_of_iso hG hG' θ, hasResonanceProperty_of_iso hG' hG θ.symm⟩

end Iso

/-! ### Square moves -/

private theorem fin4_add (j : Fin 4) :
    j + 3 + 1 = j ∧ j + 1 + 1 = j + 2 ∧ j + 3 + 3 = j + 2 ∧ j + 2 + 1 = j + 3 ∧
      j + 2 + 2 = j ∧ j + 2 + 3 = j + 1 ∧ j + 3 + 2 = j + 1 := by
  revert j
  decide

namespace IsSquareMoveFace

variable {c : H}

/-- If `T(d) = d'` and `d'` lies at an internal vertex, then `tr(d') = tr(d)`. -/
private theorem tripSet_eq_of_tripMap_eq (hG : G.IsPlabicGraph) {d d' : H}
    (h : G.tripMap d = d') (hb : ¬G.IsBoundaryVertex (G.vertexOf d')) :
    G.tripSet d' = G.tripSet d := by
  subst h
  exact hG.tripSet_tripMap (hG.not_isLeg_of_not_isBoundaryVertex hb)

/-- The trip set of `c_j`, in terms of the trip sets `t_k = tr(ē_k)` of the darts entering the
square: `t_j` if `v(c_j)` is white and `t_{j-1}` if it is black. -/
private theorem tripSet_squareCorner (hq : G.IsSquareMoveFace c) (hG : G.IsPlabicGraph)
    (j : Fin 4) :
    G.tripSet (G.squareCorner c j) =
      if G.colour (G.squareCorner c j) = .white then
        G.tripSet (G.inv (G.rot (G.squareCorner c j)))
      else G.tripSet (G.inv (G.rot (G.squareCorner c (j + 3)))) := by
  obtain ⟨h31, -⟩ := fin4_add j
  cases hcol : G.colour (G.squareCorner c j)
  · rw [if_pos rfl]
    exact tripSet_eq_of_tripMap_eq hG (hq.tripMap_inv_rot_squareCorner_of_white hG j hcol)
      (hq.not_isBoundaryVertex j)
  · rw [if_neg (by simp)]
    have hb : G.colour (G.squareCorner c (j + 3 + 1)) = .black := by rwa [h31]
    have e1 := hq.tripMap_squareCorner_of_black hG (j + 3) hb
    rw [h31] at e1
    have hw : G.colour (G.squareCorner c (j + 3)) = .white := by
      rw [hq.colour_squareCorner_eq_swap, hb]
      rfl
    rw [tripSet_eq_of_tripMap_eq hG e1 (hq.not_isBoundaryVertex j)]
    exact tripSet_eq_of_tripMap_eq hG (hq.tripMap_inv_rot_squareCorner_of_white hG (j + 3) hw)
      (hq.not_isBoundaryVertex _)

/-- The trip set of `c̄_j`: `t_{j+1}` if `v(c_{j+1})` is black and `t_{j+2}` if it is white. -/
private theorem tripSet_inv_squareCorner (hq : G.IsSquareMoveFace c) (hG : G.IsPlabicGraph)
    (j : Fin 4) :
    G.tripSet (G.inv (G.squareCorner c j)) =
      if G.colour (G.squareCorner c (j + 1)) = .black then
        G.tripSet (G.inv (G.rot (G.squareCorner c (j + 1))))
      else G.tripSet (G.inv (G.rot (G.squareCorner c (j + 2)))) := by
  obtain ⟨-, h11, -⟩ := fin4_add j
  cases hcol : G.colour (G.squareCorner c (j + 1))
  · rw [if_neg (by simp)]
    rw [tripSet_eq_of_tripMap_eq hG (hq.tripMap_inv_squareCorner_of_white hG j hcol)
      (hq.not_isBoundaryVertex_inv j)]
    have hb : G.colour (G.squareCorner c (j + 1 + 1)) = .black := by
      rw [hq.colour_squareCorner_add_one, hcol]
      rfl
    have e1 := hq.tripMap_inv_rot_squareCorner_of_black hG (j + 1) hb
    rw [h11] at e1
    exact tripSet_eq_of_tripMap_eq hG e1 (hq.not_isBoundaryVertex_inv _)
  · rw [if_pos rfl]
    exact tripSet_eq_of_tripMap_eq hG (hq.tripMap_inv_rot_squareCorner_of_black hG j hcol)
      (hq.not_isBoundaryVertex_inv j)

/-- The trip set of `e_j = σ(c_j)` is `t_{j+2}`: the trip entering the square along `ē_{j+2}`
leaves it along `e_j`. -/
private theorem tripSet_rot_squareCorner (hq : G.IsSquareMoveFace c) (hG : G.IsPlabicGraph)
    (j : Fin 4) :
    G.tripSet (G.rot (G.squareCorner c j)) =
      G.tripSet (G.inv (G.rot (G.squareCorner c (j + 2)))) := by
  obtain ⟨h31, -, h33, -⟩ := fin4_add j
  cases hcol : G.colour (G.squareCorner c j)
  · have hw : G.colour (G.squareCorner c (j + 3 + 1)) = .white := by rwa [h31]
    have e1 := hq.tripMap_squareCorner_of_white hG (j + 3) hw
    rw [h31] at e1
    rw [tripSet_eq_of_tripMap_eq hG e1 (hq.not_isBoundaryVertex_rot j),
      hq.tripSet_squareCorner hG (j + 3), if_neg, h33]
    rw [hq.colour_squareCorner_eq_swap, h31, hcol]
    simp
  · rw [tripSet_eq_of_tripMap_eq hG (hq.tripMap_inv_squareCorner_of_black hG j hcol)
      (hq.not_isBoundaryVertex_rot j), hq.tripSet_inv_squareCorner hG j, if_neg]
    rw [hq.colour_squareCorner_add_one, hcol]
    simp

/-- Trip sets of `G^q` agree with those of `G` off the edges of the square. -/
private theorem tripSet_squareMove_of_notMem (hq : G.IsSquareMoveFace c) (hG : G.IsPlabicGraph)
    {y : H} (hy : y ∈ (G.squareEdgeDarts c)ᶜ) : (G.squareMove c).tripSet y = G.tripSet y := by
  refine IsPlabicGraph.tripSet_eq_of_firstReturn_eq (hG.squareMove c) hG
    (fun i => hq.setOf_mem_bdry_or_isLeg_subset hG (Or.inr ⟨i, rfl⟩)) rfl ?_ hy
  have := congrArg DFunLike.coe (hq.firstReturnPerm_tripEquiv_squareMove hG)
  simpa [coe_firstReturnPerm] using this

private theorem tripSet_squareMove_inv_rot_squareCorner (hq : G.IsSquareMoveFace c)
    (hG : G.IsPlabicGraph) (j : Fin 4) :
    (G.squareMove c).tripSet (G.inv (G.rot (G.squareCorner c j))) =
      G.tripSet (G.inv (G.rot (G.squareCorner c j))) :=
  hq.tripSet_squareMove_of_notMem hG (hq.inv_rot_squareCorner_notMem hG j)

/-- The labels of the edges of the square are rotated by two steps. -/
private theorem edgeLabel_squareMove_squareCorner (hq : G.IsSquareMoveFace c)
    (hG : G.IsPlabicGraph) (k : Fin 4) :
    (G.squareMove c).edgeLabel ((G.squareMove c).edgeOf (G.squareCorner c k)) =
      G.edgeLabel (G.edgeOf (G.squareCorner c (k + 2))) := by
  obtain ⟨-, h11, -, h21, h22, h23, -⟩ := fin4_add k
  rw [edgeLabel_edgeOf, edgeLabel_edgeOf]
  have a1 := hq.squareMove.tripSet_squareCorner (hG.squareMove c) k
  have a2 := hq.squareMove.tripSet_inv_squareCorner (hG.squareMove c) k
  have b1 := hq.tripSet_squareCorner hG (k + 2)
  have b2 := hq.tripSet_inv_squareCorner hG (k + 2)
  simp only [squareCorner_squareMove, inv_squareMove, rot_squareMove,
    colour_squareMove_of_mem G (vertexOf_squareCorner_mem_squareVertices c _),
    hq.tripSet_squareMove_inv_rot_squareCorner hG] at a1 a2
  simp only [h21, h22, h23] at b1 b2
  simp only [inv_squareMove]
  rw [a1, a2, b1, b2]
  have col1 : G.colour (G.squareCorner c (k + 1)) = (G.colour (G.squareCorner c k)).swap :=
    hq.colour_squareCorner_add_one k
  have col2 : G.colour (G.squareCorner c (k + 2)) = G.colour (G.squareCorner c k) := by
    rw [← h11, hq.colour_squareCorner_add_one, col1]
    cases G.colour (G.squareCorner c k) <;> rfl
  have col3 : G.colour (G.squareCorner c (k + 3)) = (G.colour (G.squareCorner c k)).swap := by
    rw [← h21, hq.colour_squareCorner_add_one, col2]
  rw [col1, col2, col3]
  cases G.colour (G.squareCorner c k) <;> simp [union_comm]

/-- The labels of the other edges at the corners are rotated by two steps. -/
private theorem edgeLabel_squareMove_rot_squareCorner (hq : G.IsSquareMoveFace c)
    (hG : G.IsPlabicGraph) (k : Fin 4) :
    (G.squareMove c).edgeLabel ((G.squareMove c).edgeOf (G.rot (G.squareCorner c k))) =
      G.edgeLabel (G.edgeOf (G.rot (G.squareCorner c (k + 2)))) := by
  obtain ⟨-, -, -, -, h22, -⟩ := fin4_add k
  rw [edgeLabel_edgeOf, edgeLabel_edgeOf]
  simp only [inv_squareMove]
  rw [hq.tripSet_squareMove_of_notMem hG (hq.rot_squareCorner_notMem k),
    hq.tripSet_squareMove_inv_rot_squareCorner hG, hq.tripSet_rot_squareCorner hG k,
    hq.tripSet_rot_squareCorner hG (k + 2), h22]
  exact union_comm _ _

private theorem rot_symm_squareCorner (hq : G.IsSquareMoveFace c) (j : Fin 4) :
    G.rot.symm (G.squareCorner c j) = G.inv (G.squareCorner c (j + 3)) := by
  rw [Equiv.symm_apply_eq, hq.rot_inv_squareCorner (j + 3), (fin4_add j).1]

private theorem rot_symm_inv_squareCorner (hq : G.IsSquareMoveFace c) (j : Fin 4) :
    G.rot.symm (G.inv (G.squareCorner c (j + 3))) = G.rot (G.squareCorner c j) := by
  rw [Equiv.symm_apply_eq]
  have := hq.rot_rot_squareCorner (j + 3)
  rw [(fin4_add j).1] at this
  exact this.symm

/-- Rotating `c_k` and `c_{k+2}` in step runs through the three darts at each corner. -/
private theorem rot_symm_pow_squareCorner (hq : G.IsSquareMoveFace c) (k : Fin 4) (n : ℕ) :
    ((G.rot.symm ^ n) (G.squareCorner c k) = G.squareCorner c k ∧
      (G.rot.symm ^ n) (G.squareCorner c (k + 2)) = G.squareCorner c (k + 2)) ∨
    ((G.rot.symm ^ n) (G.squareCorner c k) = G.inv (G.squareCorner c (k + 3)) ∧
      (G.rot.symm ^ n) (G.squareCorner c (k + 2)) = G.inv (G.squareCorner c (k + 1))) ∨
    ((G.rot.symm ^ n) (G.squareCorner c k) = G.rot (G.squareCorner c k) ∧
      (G.rot.symm ^ n) (G.squareCorner c (k + 2)) = G.rot (G.squareCorner c (k + 2))) := by
  obtain ⟨-, -, -, -, -, h23, -⟩ := fin4_add k
  induction n with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, Perm.mul_apply]
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inr (Or.inl ⟨by rw [h1, hq.rot_symm_squareCorner], ?_⟩)
      rw [h2, hq.rot_symm_squareCorner, h23]
    · refine Or.inr (Or.inr ⟨by rw [h1, hq.rot_symm_inv_squareCorner], ?_⟩)
      have := hq.rot_symm_inv_squareCorner (k + 2)
      rw [h23] at this
      rw [h2, this]
    · exact Or.inl ⟨by rw [h1, Equiv.symm_apply_apply], by rw [h2, Equiv.symm_apply_apply]⟩

private theorem edgeLabel_squareMove_rot_symm_pow (hq : G.IsSquareMoveFace c)
    (hG : G.IsPlabicGraph) (k : Fin 4) (n : ℕ) :
    (G.squareMove c).edgeLabel ((G.squareMove c).edgeOf ((G.rot.symm ^ n) (G.squareCorner c k))) =
      G.edgeLabel (G.edgeOf ((G.rot.symm ^ n) (G.squareCorner c (k + 2)))) := by
  obtain ⟨-, -, -, -, -, -, h32⟩ := fin4_add k
  rcases hq.rot_symm_pow_squareCorner k n with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact hq.edgeLabel_squareMove_squareCorner hG k
  · rw [h1, h2]
    refine ((hG.squareMove c).edgeLabel_edgeOf_inv (G.squareCorner c (k + 3))).trans
      ((hq.edgeLabel_squareMove_squareCorner hG (k + 3)).trans ?_)
    rw [h32]
    exact (hG.edgeLabel_edgeOf_inv _).symm
  · rw [h1, h2]
    exact hq.edgeLabel_squareMove_rot_squareCorner hG k

/-- Edge labels at a vertex off the square are unchanged by the square move. -/
private theorem edgeLabel_squareMove_rot_symm_pow_of_notMem (hq : G.IsSquareMoveFace c)
    (hG : G.IsPlabicGraph) {a : H} (hsq : G.vertexOf a ∉ G.squareVertices c) (n : ℕ) :
    (G.squareMove c).edgeLabel ((G.squareMove c).edgeOf ((G.rot.symm ^ n) a)) =
      G.edgeLabel (G.edgeOf ((G.rot.symm ^ n) a)) := by
  have hnot : ∀ k, G.vertexOf ((G.rot.symm ^ n) a) ≠ G.vertexOf (G.squareCorner c k) := by
    intro k h'
    rw [RotationSystem.vertexOf_rot_symm_pow] at h'
    exact hsq (h' ▸ vertexOf_squareCorner_mem_squareVertices c k)
  have hiy : G.inv ((G.rot.symm ^ n) a) ∈ (G.squareEdgeDarts c)ᶜ := by
    rintro ⟨k, h' | h'⟩
    · apply hnot (k + 1)
      rw [← hq.vertexOf_inv_squareCorner, h', hG.inv_involutive]
    · apply hnot k
      rw [G.inv.injective h']
  rw [edgeLabel_edgeOf, edgeLabel_edgeOf]
  simp only [inv_squareMove]
  rw [hq.tripSet_squareMove_of_notMem hG (hq.notMem_squareEdgeDarts hnot),
    hq.tripSet_squareMove_of_notMem hG hiy]

end IsSquareMoveFace

private theorem hasResonanceProperty_squareMove (hG : G.IsPlabicGraph) {c : H}
    (hq : G.IsSquareMoveFace c) (h : G.HasResonanceProperty) :
    (G.squareMove c).HasResonanceProperty := by
  intro v hv hlol
  have hv' : v ∈ G.internalVertices := hv
  obtain ⟨hvV, -⟩ := G.mem_internalVertices.1 hv'
  obtain ⟨a, rfl⟩ := G.mem_vertices.1 hvV
  by_cases hsq : G.vertexOf a ∈ G.squareVertices c
  · obtain ⟨k, hk⟩ := mem_squareVertices.1 hsq
    rw [← hk]
    have hres := h _ (hq.vertexOf_mem_internalVertices (k + 2)) fun i hl => by
      have := hl.1.2
      rw [hq.card_vertexOf] at this
      omega
    exact hres.of_edgeLabel_eq (G' := G.squareMove c) (a' := G.squareCorner c k)
      (by rw [vertexOf_squareMove, hq.card_vertexOf, hq.card_vertexOf])
      (hq.edgeLabel_squareMove_rot_symm_pow hG k)
  · exact (h _ hv' hlol).of_edgeLabel_eq (G := G) (a := a) (G' := G.squareMove c) (a' := a) rfl
      (hq.edgeLabel_squareMove_rot_symm_pow_of_notMem hG hsq)

/-- **Square moves preserve resonance**: if `q` is a face of the plabic graph `G` at which a square
move applies, then `G` has the resonance property if and only if its square move `G^q` has. The
face `q = (c₁, c₂, c₃, c₄)` is given by its dart `c = c₁`. -/
@[cluster_algebras "lem_resonance_square_move"]
theorem IsPlabicGraph.hasResonanceProperty_iff_squareMove (hG : G.IsPlabicGraph) {c : H}
    (hq : G.IsSquareMoveFace c) :
    G.HasResonanceProperty ↔ (G.squareMove c).HasResonanceProperty := by
  refine ⟨hasResonanceProperty_squareMove hG hq, fun h => ?_⟩
  have := hasResonanceProperty_squareMove (hG.squareMove c) hq.squareMove h
  rwa [squareMove_squareMove] at this

/-! ### Hollow digons -/

/-- At an internal vertex with at least two darts, the resonance property gives the resonance
condition. -/
private theorem HasResonanceProperty.resonanceCondition (h : G.HasResonanceProperty) {a : H}
    (ha : ¬G.IsBoundaryVertex (G.vertexOf a)) (h2 : 2 ≤ (G.vertexOf a).card) :
    G.ResonanceCondition (G.vertexOf a) :=
  h _ ((DiskMap.vertexOf_mem_internalVertices _).2 ha) fun _ hl => by
    have := hl.1.2
    omega

private theorem colour_rot_symm (hG : G.IsPlabicGraph) {d : H}
    (hd : ¬G.IsBoundaryVertex (G.vertexOf d)) : G.colour (G.rot.symm d) = G.colour d := by
  have hv : G.vertexOf (G.rot.symm d) = G.vertexOf d :=
    G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf d)
  have := hG.colour_rot (G.rot.symm d) (by rwa [hv])
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

/-- At a black internal vertex, a trip arriving along `d₂` with `σ⁻¹(d₁) = d̄₂` leaves along
`d₁`. -/
private theorem tripMap_eq_of_rot_symm_eq_inv_of_black (hG : G.IsPlabicGraph) {d₁ d₂ : H}
    (hx : ¬G.IsBoundaryVertex (G.vertexOf d₁)) (hm : G.inv d₂ ∈ G.vertexOf d₁)
    (hs : G.rot.symm d₁ = G.inv d₂) (hc : G.colour d₁ = .black) : G.tripMap d₂ = d₁ := by
  rw [tripMap_apply, turn_of_black (by rwa [G.vertexOf_eq_of_mem hm])
    (by rw [← hs, colour_rot_symm hG hx, hc]), ← hs, Equiv.apply_symm_apply]

private theorem vertexOf_eq_pair {d e : H} (hm : e ∈ G.vertexOf d) (hne : d ≠ e)
    (h : (G.vertexOf d).card ≤ 2) : G.vertexOf d = {d, e} := by
  refine (eq_of_subset_of_card_le (fun z hz => ?_) (by rw [card_pair hne]; omega)).symm
  rw [mem_insert, mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact G.self_mem_vertexOf _
  · exact hm

/-- If two vertices with two darts each are joined by both of their edges, every dart reachable
from the first lies at one of them. -/
private theorem mem_union_of_reach (hG : G.IsPlabicGraph) {d₁ d₂ e : H}
    (hxe : G.vertexOf d₁ = {d₁, G.inv d₂}) (hye : G.vertexOf d₂ = {d₂, G.inv d₁})
    (he : G.Reach d₁ e) : e ∈ G.vertexOf d₁ ∪ G.vertexOf d₂ := by
  induction he with
  | refl => exact mem_union_left _ (G.self_mem_vertexOf _)
  | rot _ ih =>
    rcases mem_union.1 ih with h' | h'
    · exact mem_union_left _ (by rw [← G.vertexOf_eq_of_mem h']; exact G.rot_mem_vertexOf _)
    · exact mem_union_right _ (by rw [← G.vertexOf_eq_of_mem h']; exact G.rot_mem_vertexOf _)
  | inv _ ih =>
    rw [hxe, hye] at ih ⊢
    simp only [mem_union, mem_insert, mem_singleton] at ih ⊢
    rcases ih with (rfl | rfl) | (rfl | rfl)
    · simp
    · simp [hG.inv_involutive _]
    · simp
    · simp [hG.inv_involutive _]

/-- The case of a hollow digon `{d₁, d₂}` with `v(d₁)` black and `v(d₂)` white. -/
private theorem false_of_hollowDigon_black_white (hG : G.IsPlabicGraph)
    (h : G.HasResonanceProperty) {d₁ d₂ : H}
    (hx : ¬G.IsBoundaryVertex (G.vertexOf d₁)) (hy : ¬G.IsBoundaryVertex (G.vertexOf d₂))
    (hm₁ : G.inv d₂ ∈ G.vertexOf d₁) (hne₁ : d₁ ≠ G.inv d₂) (hs₁ : G.rot.symm d₁ = G.inv d₂)
    (hm₂ : G.inv d₁ ∈ G.vertexOf d₂) (hne₂ : d₂ ≠ G.inv d₁) (hs₂ : G.rot.symm d₂ = G.inv d₁)
    (hc₁ : G.colour d₁ = .black) (hc₂ : G.colour d₂ = .white) : False := by
  have hvy : G.vertexOf (G.inv d₁) = G.vertexOf d₂ := G.vertexOf_eq_of_mem hm₂
  have hT1 := tripMap_eq_of_rot_symm_eq_inv_of_black hG hx hm₁ hs₁ hc₁
  have hT2 : G.tripMap (G.inv d₂) = G.inv d₁ := by
    rw [tripMap_apply, hG.inv_involutive, turn_of_white hy hc₂, hs₂]
  have htr1 := IsSquareMoveFace.tripSet_eq_of_tripMap_eq hG hT1 hx
  have htr2 := IsSquareMoveFace.tripSet_eq_of_tripMap_eq hG hT2 (by rwa [hvy])
  have hlab : G.edgeLabel (G.edgeOf d₁) = G.edgeLabel (G.edgeOf d₂) := by
    rw [edgeLabel_edgeOf, edgeLabel_edgeOf, htr1, htr2]
  have hlx : G.edgeLabel (G.edgeOf (G.inv d₂)) = G.edgeLabel (G.edgeOf d₁) := by
    rw [hG.edgeLabel_edgeOf_inv, hlab]
  have hly : G.edgeLabel (G.edgeOf (G.inv d₁)) = G.edgeLabel (G.edgeOf d₂) := by
    rw [hG.edgeLabel_edgeOf_inv, hlab]
  have hx2 : 2 ≤ (G.vertexOf d₁).card :=
    one_lt_card.2 ⟨d₁, G.self_mem_vertexOf d₁, G.inv d₂, hm₁, hne₁⟩
  have hy2 : 2 ≤ (G.vertexOf d₂).card :=
    one_lt_card.2 ⟨d₂, G.self_mem_vertexOf d₂, G.inv d₁, hm₂, hne₂⟩
  rcases Nat.lt_or_ge 2 (G.vertexOf d₁).card with hx3 | hx3
  · exact hne₁ ((h.resonanceCondition hx hx2).injOn_edgeLabel hx3 (G.self_mem_vertexOf d₁)
      hm₁ hlx.symm)
  rcases Nat.lt_or_ge 2 (G.vertexOf d₂).card with hy3 | hy3
  · exact hne₂ ((h.resonanceCondition hy hy2).injOn_edgeLabel hy3 (G.self_mem_vertexOf d₂)
      hm₂ hly.symm)
  obtain ⟨z, hz⟩ := hG.bdry_nonempty
  rcases mem_union.1 (mem_union_of_reach hG (vertexOf_eq_pair hm₁ hne₁ hx3)
    (vertexOf_eq_pair hm₂ hne₂ hy3) (hG.reach d₁ z)) with h' | h'
  · exact hx ⟨z, h', hz⟩
  · exact hy ⟨z, h', hz⟩

/-- **A hollow digon violates resonance**: a plabic graph containing a hollow digon does not have
the resonance property. -/
@[cluster_algebras "lem_hollow_digon_not_resonant"]
theorem IsPlabicGraph.not_hasResonanceProperty_of_isHollowDigon (hG : G.IsPlabicGraph)
    {f : Finset H} (hf : G.IsHollowDigon f) : ¬G.HasResonanceProperty := by
  intro h
  obtain ⟨-, d₁, d₂, rfl, -⟩ := id hf
  obtain ⟨hx, hy, ⟨-, hm₁, hne₁, hs₁⟩, ⟨-, hm₂, hne₂, hs₂⟩⟩ := hG.hollowDigon_shape hf
  have hvx : G.vertexOf (G.inv d₂) = G.vertexOf d₁ := G.vertexOf_eq_of_mem hm₁
  have hvy : G.vertexOf (G.inv d₁) = G.vertexOf d₂ := G.vertexOf_eq_of_mem hm₂
  have hx2 : 2 ≤ (G.vertexOf d₁).card :=
    one_lt_card.2 ⟨d₁, G.self_mem_vertexOf d₁, G.inv d₂, hm₁, hne₁⟩
  -- if a two-dart orbit of the trip map avoids the legs, its darts have empty trip sets
  have hempty : ∀ {u w : H}, G.tripMap u = w → G.tripMap w = u →
      ¬G.IsBoundaryVertex (G.vertexOf u) → ¬G.IsBoundaryVertex (G.vertexOf w) →
      G.tripSet u = ∅ := by
    intro u w huw hwu hu hw
    have horbit : ∀ n, G.tripMap^[n] u = u ∨ G.tripMap^[n] u = w := by
      intro n
      induction n with
      | zero => exact Or.inl rfl
      | succ n ih =>
        rw [iterate_succ_apply']
        rcases ih with h' | h' <;> rw [h']
        · exact Or.inr huw
        · exact Or.inl hwu
    refine hG.tripSet_eq_empty_of_forall_not_isLeg fun n => ?_
    rcases horbit n with h' | h' <;> rw [h']
    · exact hG.not_isLeg_of_not_isBoundaryVertex hu
    · exact hG.not_isLeg_of_not_isBoundaryVertex hw
  have hcard := (h.resonanceCondition hx hx2).card_edgeLabel (G.self_mem_vertexOf d₁)
  rw [edgeLabel_edgeOf] at hcard
  cases hc₁ : G.colour d₁ <;> cases hc₂ : G.colour d₂
  · -- both white: the trip map swaps `d̄₁` and `d̄₂`
    have hT1 : G.tripMap (G.inv d₁) = G.inv d₂ := by
      rw [tripMap_apply, hG.inv_involutive, turn_of_white hx hc₁, hs₁]
    have hT2 : G.tripMap (G.inv d₂) = G.inv d₁ := by
      rw [tripMap_apply, hG.inv_involutive, turn_of_white hy hc₂, hs₂]
    rw [hempty hT1 hT2 (by rwa [hvy]) (by rwa [hvx]), union_empty] at hcard
    have := hG.card_tripSet_le_one d₁
    omega
  · exact false_of_hollowDigon_black_white hG h hy hx hm₂ hne₂ hs₂ hm₁ hne₁ hs₁ hc₂ hc₁
  · exact false_of_hollowDigon_black_white hG h hx hy hm₁ hne₁ hs₁ hm₂ hne₂ hs₂ hc₁ hc₂
  · -- both black: the trip map swaps `d₁` and `d₂`
    rw [hempty (tripMap_eq_of_rot_symm_eq_inv_of_black hG hy hm₂ hs₂ hc₂)
      (tripMap_eq_of_rot_symm_eq_inv_of_black hG hx hm₁ hs₁ hc₁) hx hy, empty_union] at hcard
    have := hG.card_tripSet_le_one (G.inv d₁)
    omega

end PlabicData

end ClusterAlgebras

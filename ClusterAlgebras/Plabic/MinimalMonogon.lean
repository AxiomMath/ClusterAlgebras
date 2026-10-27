/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BoundaryParallelCuts
public import ClusterAlgebras.Plabic.ClosedStrands
public import ClusterAlgebras.Plabic.External
public import ClusterAlgebras.Plabic.HugMonogon
public import ClusterAlgebras.Plabic.MonogonCut
public import ClusterAlgebras.Plabic.Straighten

/-!
# Minimal triple diagrams have no badgons

A monogon of a triple diagram can be turned, by swivel moves, into a hollow monogon. The proof is
by strong induction on the number of triple points. Among the diagrams move-equivalent to `X` and
their convex monogons, choose a convex monogon `M` with the fewest darts `m`. If `m = 1`, `M` is a
hollow monogon. Otherwise consider the inside `X|_M`, a triple diagram with fewer triple points:

* if `X|_M` is not monogon-stable, the induction hypothesis gives a hollow monogon in a diagram
  move-equivalent to it, and the moves lift to `X`;
* if `X|_M` is monogon-stable, it has the straightening property; an arc `Q` of `X|_M` with a run
  of least size has a minimal interval, along which it can be made boundary-parallel; lifting
  these moves, `Q` becomes a returning path of `M` that hugs `M`. A hugging returning path from a
  point to itself has one dart and is a hollow monogon; a parallel one gives a hollow monogon by
  an exercise in FWZ; an anti-parallel one gives a closed aligned rail, whose push-off has
  a convex monogon with `m - 1` darts, contradicting the choice of `M`.

As a hollow monogon is not minimal, minimal triple diagrams are monogon-stable; hence, by
Thurston's straightening, they have no badgons, and so no closed strands.

## Main results

* `ClusterAlgebras.TripleDiagram.exists_moveEquivalent_isHollowMonogon`: a monogon can be made
  hollow.
* `ClusterAlgebras.TripleDiagram.IsMinimal.isMonogonStable`: minimal diagrams are monogon-stable.
* `ClusterAlgebras.TripleDiagram.IsMinimal.not_hasBadgon`: a minimal triple diagram has no
  badgons.
* `ClusterAlgebras.TripleDiagram.IsMinimal.not_isClosedStrand`: a minimal triple diagram has no
  closed strands.

## Implementation notes

* Labels are `0`-indexed: a returning path from `z_{a+1}` to `z_{c+1}` is
  `X.IsReturningPath P ζ Q a c`, and the entries of side lists and cut lists are numbered
  from `0`.
* The *run* of an arc of the inside `X|_M` is measured on the inside list: it is the difference of
  the indices of the list entries at the positions of its two ends. The interval of the arc whose
  interior positions carry the entries strictly between these is the interval `I_Q` of FWZ.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace TripleData

section MinimalMonogon

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}

/-- The value of a difference in `Fin n`. -/
private theorem val_sub_ite' {n : ℕ} (p a : Fin n) :
    ((p - a : Fin n) : ℕ) = if (a : ℕ) ≤ p then (p : ℕ) - a else n - a + p := by
  rw [Fin.val_sub]
  have := a.isLt
  have := p.isLt
  split_ifs with h
  · rw [show n - (a : ℕ) + p = (p - a) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

private theorem add_mod_ite {x s n : ℕ} (hx : x < n) (hs : s ≤ n) :
    (x + s) % n = if x + s < n then x + s else x + s - n := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- After a shift by `s ≤ 1` of the circle `ℤ/n`, the positions strictly inside the cyclic
interval from `a` to `c` are those whose shifts lie strictly between the shifts of `a` and `c`,
when the shift of `a` is the smaller one. -/
private theorem mem_cyclicIcc_sdiff_iff_shift {n s : ℕ} (hs : s ≤ 1) (a c r : Fin n)
    (hac : ((a : ℕ) + s) % n < ((c : ℕ) + s) % n) :
    r ∈ cyclicIcc a c \ {a, c} ↔
      ((a : ℕ) + s) % n < ((r : ℕ) + s) % n ∧ ((r : ℕ) + s) % n < ((c : ℕ) + s) % n := by
  have ha := a.isLt
  have hc := c.isLt
  have hr := r.isLt
  rw [mem_sdiff, mem_cyclicIcc, Fin.le_def, val_sub_ite', val_sub_ite', mem_insert, mem_singleton,
    Fin.ext_iff, Fin.ext_iff]
  rw [add_mod_ite ha (by omega), add_mod_ite hc (by omega)] at hac ⊢
  rw [add_mod_ite hr (by omega)]
  split_ifs at hac ⊢ <;> omega

omit [Fintype H] [DecidableEq H] in
/-- An interval of `j` for a map `π` of the arcs of a cut along a list `L` with shift `s ≤ 1`,
described on the cut list: its interior positions are those whose cut list index lies strictly
between the indices of the two ends `s_j` and `t_{π(j)}`. -/
private theorem exists_isIntervalOf_cut {L : List H} {s : ℕ} (hs : s ≤ 1) (hev : Even L.length)
    (π : Fin (L.length / 2) → Fin (L.length / 2)) (j : Fin (L.length / 2)) :
    ∃ I, IsIntervalOf π j I ∧ ∀ r, r ∈ intervalInterior π j I ↔
      min (cutEndIndex L s (sourceIndex j) : ℕ) (cutEndIndex L s (targetIndex (π j))) <
          cutEndIndex L s r ∧
        (cutEndIndex L s r : ℕ) <
          max (cutEndIndex L s (sourceIndex j) : ℕ) (cutEndIndex L s (targetIndex (π j))) := by
  have hne : (cutEndIndex L s (sourceIndex j) : ℕ) ≠ cutEndIndex L s (targetIndex (π j)) :=
    fun h => sourceIndex_ne_targetIndex j (π j) (cutEndIndex_injective (Fin.ext h))
  have h2 : 2 * (L.length / 2) = L.length := by obtain ⟨t, ht⟩ := hev; omega
  have hval : ∀ r : Fin (2 * (L.length / 2)),
      (cutEndIndex L s r : ℕ) = ((r : ℕ) + s) % (2 * (L.length / 2)) := by
    intro r
    simp only [cutEndIndex]
    exact congrArg (((r : ℕ) + s) % ·) h2.symm
  simp only [hval] at hne ⊢
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨cyclicIcc (sourceIndex j) (targetIndex (π j)), Or.inl rfl, fun r => ?_⟩
    rw [intervalInterior, mem_cyclicIcc_sdiff_iff_shift hs _ _ r h, min_eq_left h.le,
      max_eq_right h.le]
  · refine ⟨cyclicIcc (targetIndex (π j)) (sourceIndex j), Or.inr rfl, fun r => ?_⟩
    rw [intervalInterior, pair_comm, mem_cyclicIcc_sdiff_iff_shift hs _ _ r h, min_eq_right h.le,
      max_eq_left h.le]

/-! ### Arcs of a cut -/

/-- The strand map of a pre-triple diagram is injective. -/
private theorem strandMap_injective' {X : TripleData H b} : Function.Injective X.strandMap := by
  have hv : ∀ d d', X.RunsToEndpoint d → ¬X.RunsToEndpoint d' →
      X.inv d ≠ X.rot (X.rot (X.rot (X.inv d'))) := by
    intro d d' hd hd' h
    apply hd'
    change X.IsBoundaryVertex (X.vertexOf (X.inv d'))
    have := congrArg X.vertexOf h
    rw [X.vertexOf_rot, X.vertexOf_rot, X.vertexOf_rot] at this
    rwa [← this]
  intro d d' h
  by_cases hd : X.RunsToEndpoint d <;> by_cases hd' : X.RunsToEndpoint d'
  · rw [X.strandMap_of_runsToEndpoint hd, X.strandMap_of_runsToEndpoint hd'] at h
    exact X.inv.injective h
  · rw [X.strandMap_of_runsToEndpoint hd, X.strandMap_of_not_runsToEndpoint hd'] at h
    exact absurd h (hv d d' hd hd')
  · rw [X.strandMap_of_not_runsToEndpoint hd, X.strandMap_of_runsToEndpoint hd'] at h
    exact absurd h.symm (hv d' d hd' hd)
  · rw [X.strandMap_of_not_runsToEndpoint hd, X.strandMap_of_not_runsToEndpoint hd'] at h
    exact X.inv.injective (X.rot.injective (X.rot.injective (X.rot.injective h)))

/-- Two arcs, the second at least as long as the first, with the same last dart are equal. -/
private theorem eq_of_arcDart_last_eq_aux' {X : TripleData H b} (hX : X.IsPreTripleDiagram)
    {j j' : Fin b} (hle : X.arcLength j ≤ X.arcLength j')
    (h : X.arcDart j (X.arcLength j - 1) = X.arcDart j' (X.arcLength j' - 1)) : j = j' := by
  have hm := hX.arcLength_ne_zero j
  have hm' := hX.arcLength_ne_zero j'
  have h' : X.strandMap^[X.arcLength j - 1] (X.endDart (sourceIndex j)) =
      X.strandMap^[X.arcLength j - 1]
        (X.arcDart j' (X.arcLength j' - X.arcLength j)) := by
    change X.arcDart j _ = _
    rw [h, arcDart, arcDart, ← Function.iterate_add_apply]
    congr 1
    omega
  have h0 := strandMap_injective'.iterate _ h'
  rcases Nat.eq_zero_or_pos (X.arcLength j' - X.arcLength j) with h1 | h1
  · rw [h1, arcDart_zero] at h0
    exact sourceIndex_injective (hX.endpoint_injective (by rw [endpoint, endpoint, h0]))
  · exfalso
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero h1.ne'
    rw [ht] at h0
    obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hm'
    have hs := X.strandStep_arcDart hM (k := t) (by omega)
    have hb := (X.mem_boundaryVertices.1 (hX.endpoint_mem (sourceIndex j))).2
    change X.IsBoundaryVertex (X.vertexOf (X.endDart (sourceIndex j))) at hb
    rw [h0, hs.vertexOf_eq] at hb
    exact hs.1 hb

/-- The strand permutation of a triple diagram is injective. -/
private theorem strandPerm_injective'' {X : TripleData H b} (hX : X.IsTripleDiagram) :
    Function.Injective X.strandPerm := by
  intro j j' h
  have h1 := endDart_arcEndIndex hX j
  have h2 := endDart_arcEndIndex hX j'
  rw [show X.arcEndIndex j = X.arcEndIndex j' by simp only [arcEndIndex, h], h2] at h1
  have h3 := (X.inv.injective h1).symm
  rcases le_total (X.arcLength j) (X.arcLength j') with hle | hle
  · exact eq_of_arcDart_last_eq_aux' hX.toIsPreTripleDiagram hle h3
  · exact (eq_of_arcDart_last_eq_aux' hX.toIsPreTripleDiagram hle h3.symm).symm

/-- The arc from `s_j` of a cut along `(K, L)` with shift `s` consists of darts over `K` forming a
strand path of `X`; its first dart is the entry of `L` at the position of `s_j`, and the reverse of
its last dart the entry of `L` at the position of `t_{π(j)}`. -/
private theorem arc_cut_ends {X : TripleData H b} {K : Finset H} {L : List H} {s : ℕ}
    (hX : X.IsTripleDiagram) (hc : X.IsCutData K L) (hY : (X.cut K L s).IsTripleDiagram)
    (j : Fin (L.length / 2)) :
    ∃ Q : List {d // d ∈ K}, Q.map Sum.inl = (X.cut K L s).arc j ∧
      X.IsStrandPath (Q.map Subtype.val) ∧
      (Q.map Subtype.val).head? = some L[(cutEndIndex L s (sourceIndex j) : ℕ)] ∧
      (Q.map Subtype.val).getLast?.map X.inv =
        some L[(cutEndIndex L s (targetIndex ((X.cut K L s).strandPerm j)) : ℕ)] := by
  have hYp := hY.toIsPreTripleDiagram
  have hm := hYp.arcLength_ne_zero j
  have hYP : (X.cut K L s).IsStrandPath ((X.cut K L s).arc j) :=
    (X.cut K L s).isStrandPath_arc hYp hm
  obtain ⟨Q, hQ, hP⟩ := hc.exists_isStrandPath_of_isStrandPath_cut hX.toIsPreTripleDiagram hYP
  refine ⟨Q, hQ.symm, hP, ?_, ?_⟩
  · have h0 : ((X.cut K L s).arc j).head? = some ((X.cut K L s).endDart (sourceIndex j)) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [length_arc]; omega),
        getElem_arc, arcDart_zero]
    rw [hQ, List.head?_map, cut_endDart, hc.cutListDart_eq] at h0
    rw [List.head?_map]
    obtain ⟨q, hq, hq'⟩ := Option.map_eq_some_iff.1 h0
    rw [hq, Option.map_some, congrArg Subtype.val (Sum.inl_injective hq')]
  · have h0 : ((X.cut K L s).arc j).getLast? =
        some ((X.cut K L s).arcDart j ((X.cut K L s).arcLength j - 1)) := by
      rw [List.getLast?_eq_getElem?, length_arc,
        List.getElem?_eq_getElem (by rw [length_arc]; omega), getElem_arc]
    have h1 := endDart_arcEndIndex hY j
    rw [hQ, List.getLast?_map] at h0
    obtain ⟨q, hq, hq'⟩ := Option.map_eq_some_iff.1 h0
    rw [← hq', hc.cut_inv_inl hX.inv_involutive] at h1
    rw [List.getLast?_map, hq, Option.map_some, Option.map_some]
    change (X.cut K L s).endDart (targetIndex ((X.cut K L s).strandPerm j)) = _ at h1
    rw [cut_endDart, hc.cutListDart_eq] at h1
    exact congrArg some (congrArg Subtype.val (Sum.inl_injective h1)).symm

/-! ### Isomorphisms preserve boundary-parallel arcs -/

/-- If `θ : X → X'` is an isomorphism of triple diagrams and the arc from `s'_j` of `X'` is
boundary-parallel along `I`, so is the arc from `s_j` of `X`. -/
private theorem isBoundaryParallel_of_iso {H' : Type*} [Fintype H'] [DecidableEq H']
    {X : TripleData H b} {X' : TripleData H' b} (θ : X.Iso X') (hX : X.IsTripleDiagram)
    (hX' : X'.IsTripleDiagram) {j : Fin b} {I : Finset (Fin (2 * b))}
    (h : X'.IsBoundaryParallel j I) : X.IsBoundaryParallel j I := by
  have hp := hX.toIsPreTripleDiagram
  have hp' := hX'.toIsPreTripleDiagram
  have hπ : X'.strandPerm = X.strandPerm := θ.strandPerm_eq hp hp'
  have hlen : X'.arcLength j = X.arcLength j := by
    simp only [arcLength, θ.arcLastIndex_eq hp hp']
  obtain ⟨hI, hS', hcard, hpass⟩ := h
  rw [hπ] at hI hcard hpass
  have hS : X.IsSimpleArc j := by
    intro k l hk hl hv
    apply hS' k l (by rw [hlen]; exact hk) (by rw [hlen]; exact hl)
    rw [← θ.map_arcDart hp hp', ← θ.map_arcDart hp hp', ← θ.map_inv, ← θ.map_inv,
      ← θ.map_vertexOf, ← θ.map_vertexOf, hv]
  refine ⟨hI, hS, ?_, fun r hr => ?_⟩
  · rw [← hcard, hS.ncard_passesThrough hX, hS'.ncard_passesThrough hX', hlen]
  · obtain ⟨hint, d, hd, hdv⟩ := hpass r hr
    rw [← θ.map_endDart hp hp', ← θ.map_inv] at hint hdv
    refine ⟨X.vertexOf_mem_internalVertices.2
      ((θ.isBoundaryVertex_vertexOf_iff _).not.1 (X'.vertexOf_mem_internalVertices.1 hint)), ?_⟩
    obtain ⟨t, ht, rfl⟩ := mem_arc_toFinset.1 hd
    refine ⟨X.arcDart j t, mem_arc_toFinset.2 ⟨t, by rw [← hlen]; exact ht, rfl⟩, ?_⟩
    rw [← θ.map_arcDart hp hp', ← θ.map_vertexOf, ← θ.map_vertexOf] at hdv
    exact map_injective _ hdv

/-! ### Diagrams agreeing at the points of an arc -/

/-- If `σ'` agrees with `σ` on the vertex of `d`, then `σ'^k(d) = σ^k(d)`. -/
private theorem rot_pow_eq_of_forall_mem_vertexOf {X X' : TripleData H b} {d : H}
    (h : ∀ e ∈ X.vertexOf d, X'.rot e = X.rot e) (k : ℕ) : (X'.rot ^ k) d = (X.rot ^ k) d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
    apply h
    rw [← X.vertexOf_rot_pow_apply k d]
    exact X.self_mem_vertexOf _

/-- Diagrams with the same involution whose rotations agree at the vertex of `ē` have the same
`ζ` darts at `e`. -/
private theorem sideDarts_eq_of_forall_mem_vertexOf {X X' : TripleData H b} (hinv : X'.inv = X.inv)
    {e : H} (h : ∀ d ∈ X.vertexOf (X.inv e), X'.rot d = X.rot d) (ζ : StrandSide) :
    X'.sideDarts ζ e = X.sideDarts ζ e := by
  have hp := rot_pow_eq_of_forall_mem_vertexOf h
  have h1 := h _ (X.self_mem_vertexOf (X.inv e))
  cases ζ <;> simp only [sideDarts, hinv, hp, h1]

/-! ### Darts strictly between two darts of a list -/

omit [Fintype H] in
/-- The darts `X.hugDarts P ζ Q` are the entries of the `ζ` list strictly between the first dart
of `Q` and the reverse of its last dart. -/
private theorem mem_hugDarts_iff {X : TripleData H b} {P Q : List H} {ζ : StrandSide} {f g : H}
    (hf : Q.head? = some f) (hg : Q.getLast? = some g) {d : H} :
    d ∈ X.hugDarts P ζ Q ↔ ∃ t, ∃ ht : t < (X.sideList ζ P).length,
      min ((X.sideList ζ P).idxOf f) ((X.sideList ζ P).idxOf (X.inv g)) < t ∧
      t < max ((X.sideList ζ P).idxOf f) ((X.sideList ζ P).idxOf (X.inv g)) ∧
      (X.sideList ζ P)[t] = d := by
  simp only [hugDarts, hf, hg]
  generalize X.sideList ζ P = Λ
  generalize Λ.idxOf f = x
  generalize Λ.idxOf (X.inv g) = y
  split_ifs with h
  · rw [List.mem_iff_getElem]
    constructor
    · rintro ⟨n, hn, rfl⟩
      simp only [List.length_take, List.length_drop] at hn
      exact ⟨x + 1 + n, by omega, by omega, by omega, by simp [List.getElem_take,
        List.getElem_drop]⟩
    · rintro ⟨t, ht, h1, h2, rfl⟩
      refine ⟨t - (x + 1), by simp only [List.length_take, List.length_drop]; omega, ?_⟩
      simp only [List.getElem_take, List.getElem_drop]
      congr 1
      omega
  · rw [List.mem_reverse, List.mem_iff_getElem]
    constructor
    · rintro ⟨n, hn, rfl⟩
      simp only [List.length_take, List.length_drop] at hn
      exact ⟨y + 1 + n, by omega, by omega, by omega, by simp [List.getElem_take,
        List.getElem_drop]⟩
    · rintro ⟨t, ht, h1, h2, rfl⟩
      refine ⟨t - (y + 1), by simp only [List.length_take, List.length_drop]; omega, ?_⟩
      simp only [List.getElem_take, List.getElem_drop]
      congr 1
      omega

section Helpers

variable {X : TripleData H b}

private theorem rot_pow_rot_pow' (hX : X.IsPreTripleDiagram) {d : H}
    (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) (m n : ℕ) :
    (X.rot ^ m) ((X.rot ^ n) d) = (X.rot ^ ((m + n) % 6)) d := by
  rw [← Equiv.Perm.mul_apply, ← pow_add, hX.rot_pow_mod_six hd]

/-- At an internal vertex, the antipodal pairs through `σ^i(c)` and `σ^j(c)` differ when
`i ∉ {j, j + 3}` modulo `6`. -/
private theorem pair_ne_of_rot_pow (hX : X.IsPreTripleDiagram) {c : H}
    (hz : ¬X.IsBoundaryVertex (X.vertexOf c)) {i j : ℕ} (hi : i < 6) (hj : j < 6)
    (h₁ : i ≠ j) (h₂ : i ≠ (3 + j) % 6) :
    ({(X.rot ^ i) c, (X.rot ^ 3) ((X.rot ^ i) c)} : Finset H) ≠
      {(X.rot ^ j) c, (X.rot ^ 3) ((X.rot ^ j) c)} := by
  intro h
  have hi' : (X.rot ^ i) c ∈ ({(X.rot ^ j) c, (X.rot ^ 3) ((X.rot ^ j) c)} : Finset H) := by
    rw [← h]
    exact mem_insert_self _ _
  rw [rot_pow_rot_pow' hX hz] at hi'
  simp only [mem_insert, mem_singleton] at hi'
  rcases hi' with h' | h'
  · exact h₁ ((hX.rot_pow_six hz).2 i j hi hj h')
  · exact h₂ ((hX.rot_pow_six hz).2 i _ hi (Nat.mod_lt _ (by norm_num)) h')

/-- A strand path leaving an internal vertex at `σ^3(σ^i(c))` and returning at `σ^j(c)`, with
`i ∉ {j, j + 3}` modulo `6`, is a monogon. -/
private theorem isMonogon_of_rot_pow (hX : X.IsPreTripleDiagram) {c : H}
    (hz : ¬X.IsBoundaryVertex (X.vertexOf c)) {Q : List H} (hQ : X.IsStrandPath Q) {i j : ℕ}
    (hi : i < 6) (hj : j < 6) (h₁ : i ≠ j) (h₂ : i ≠ (3 + j) % 6)
    (hf : Q.head? = some ((X.rot ^ 3) ((X.rot ^ i) c)))
    (hg : ∀ u ∈ Q.getLast?, X.inv u = (X.rot ^ j) c) : X.IsMonogon Q := by
  have hmem : ∀ n, (X.rot ^ n) c ∈ X.vertexOf c := fun n => by
    rw [← X.vertexOf_rot_pow_apply n c]; exact X.self_mem_vertexOf _
  exact (X.isMonogon_of_two_passes hX (X.vertexOf_mem_internalVertices.2 hz) (hmem i) (hmem j)
    (pair_ne_of_rot_pow hX hz hi hj h₁ h₂) hQ hf hg).1

/-- A returning path from a point `z_{a+1}` to itself is a monogon. -/
private theorem isMonogon_of_isReturningPath_self (hX : X.IsPreTripleDiagram) {P Q : List H}
    {ζ : StrandSide} {a : ℕ} (hQ : X.IsReturningPath P ζ Q a a) : X.IsMonogon Q := by
  obtain ⟨e, he, f, hf, hfe⟩ := hQ.head?_mem
  obtain ⟨e', he', g, hg, hge⟩ := hQ.getLast?_mem
  obtain rfl : e' = e := Option.mem_unique he' he
  have hPs := hQ.isSimpleStrandPath.isStrandPath
  have ha := hQ.lt_left
  rw [List.getElem?_eq_getElem (by omega), Option.mem_def, Option.some_inj] at he
  subst he
  have hz : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[a])) :=
    ((X.isStrandPath_iff_getElem.1 hPs).2.2 a ha).1
  have hPa := (X.isStrandPath_iff_getElem.1 hPs).2.1 a (by omega)
  have hc₀out : X.isOut (X.inv P[a]) = false := by
    rw [hX.isOut_inv_apply hPa.1, hPa.2]; rfl
  set c₀ := X.inv P[a]
  have hfQ : f ∈ Q := List.mem_of_mem_head? hf
  have hgQ : g ∈ Q := List.mem_of_mem_getLast? hg
  have hfout : X.isOut f = true := hQ.isStrandPath.isOut_eq_true f hfQ
  have hgout : X.isOut (X.inv g) = false := by
    rw [hX.isOut_inv_apply (hQ.isStrandPath.notMem_bdry g hgQ),
      hQ.isStrandPath.isOut_eq_true g hgQ]; rfl
  have hout : ∀ n, X.isOut ((X.rot ^ n) c₀) = decide ¬Even n := by
    intro n
    rw [hX.isOut_rot_pow_apply hz, hc₀out]
    by_cases h : Even n <;> simp [h]
  have hrr := rot_pow_rot_pow' hX hz
  have hrot1 : X.rot c₀ = (X.rot ^ 1) c₀ := by rw [pow_one]
  cases ζ
  · simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hfe hge
    have hf1 : f = (X.rot ^ 1) c₀ := by
      rcases hfe with h | h
      · rw [h, hrot1]
      · rw [h, hout 2] at hfout
        exact absurd hfout (by decide)
    have hg2 : X.inv g = (X.rot ^ 2) c₀ := by
      rcases hge with h | h
      · rw [h, hrot1, hout 1] at hgout
        exact absurd hgout (by decide)
      · exact h
    exact isMonogon_of_rot_pow hX hz hQ.isStrandPath (i := 4) (j := 2) (by omega) (by omega)
      (by omega) (by omega) (by rw [Option.mem_def.1 hf, hrr, hf1])
      fun u hu => by rw [Option.mem_unique hu hg, hg2]
  · simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hfe hge
    have hf5 : f = (X.rot ^ 5) c₀ := by
      rcases hfe with h | h
      · rw [h, hout 4] at hfout
        exact absurd hfout (by decide)
      · exact h
    have hg4 : X.inv g = (X.rot ^ 4) c₀ := by
      rcases hge with h | h
      · exact h
      · rw [h, hout 5] at hgout
        exact absurd hgout (by decide)
    exact isMonogon_of_rot_pow hX hz hQ.isStrandPath (i := 2) (j := 4) (by omega) (by omega)
      (by omega) (by omega) (by rw [Option.mem_def.1 hf, hrr, hf5])
      fun u hu => by rw [Option.mem_unique hu hg, hg4]

omit [Fintype H] in
/-- The entries of an infix `F` of a list `L` without repeated entries sit at consecutive
positions of `L`. -/
private theorem exists_idxOf_of_isInfix {L F : List H} (hnd : L.Nodup) (hF : F <:+: L) :
    ∃ p, ∀ k (hk : k < F.length), L.idxOf F[k] = p + k := by
  obtain ⟨s, t, rfl⟩ := hF
  refine ⟨s.length, fun k hk => ?_⟩
  have hlt : s.length + k < (s ++ F ++ t).length := by simp; omega
  have h : (s ++ F ++ t)[s.length + k]'hlt = F[k] := by
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
    simp
  rw [← h, hnd.idxOf_getElem]

end Helpers

/-! ### Hollow monogons across isomorphisms -/

/-- A diagram isomorphic to one with a hollow monogon has a hollow monogon. -/
private theorem HIsomorphic.exists_isHollowMonogon' {H' : Type} [Fintype H'] [DecidableEq H']
    {b' : ℕ} {X : TripleData H b} {X' : TripleData H' b'}
    (h : X.HIsomorphic X') {c : H'} (hc : X'.IsHollowMonogon {c}) :
    ∃ d, X.IsHollowMonogon {d} := by
  obtain ⟨rfl, ⟨θ⟩⟩ := h
  obtain ⟨hcB, hφ⟩ := hc.facePerm_eq
  refine ⟨θ.toEquiv.symm c, X.isHollowMonogon_singleton ?_ ?_⟩
  · rwa [← θ.mem_bdry_iff, Equiv.apply_symm_apply]
  · apply θ.toEquiv.injective
    rwa [θ.map_facePerm, Equiv.apply_symm_apply]

/-! ### A hugging returning path from a point to itself -/

/-- A returning path of `P` from a point `z_{a+1}` to itself that hugs `P` has one dart, and gives
a hollow monogon. -/
private theorem exists_isHollowMonogon_of_hugs_self {X : TripleData H b}
    (hX : X.IsPreTripleDiagram) {P Q : List H} {ζ : StrandSide} {a : ℕ}
    (hnd : (X.sideList ζ P).Nodup) (hQ : X.Hugs P ζ Q a a) :
    ∃ c, X.IsHollowMonogon {c} := by
  have hR := hQ.isReturningPath
  have hmono := isMonogon_of_isReturningPath_self hX hR
  obtain ⟨e, he, f, hf, hfe⟩ := hR.head?_mem
  obtain ⟨e', he', g, hg, hge⟩ := hR.getLast?_mem
  obtain rfl : e = e' := Option.mem_unique he he'
  have ha := hR.lt_left
  have heP : e ∈ P.dropLast := by
    have h : P.dropLast[a]? = some e := by
      rw [List.getElem?_dropLast, if_pos (by omega)]
      exact he
    exact List.mem_of_getElem? h
  have hinf : X.sideDarts ζ e <:+: X.sideList ζ P := by
    cases ζ
    · exact List.infix_flatMap_of_mem heP _
    · exact List.infix_flatMap_of_mem (List.mem_reverse.2 heP) _
  obtain ⟨p, hp⟩ := exists_idxOf_of_isInfix hnd hinf
  have hlen2 : (X.sideDarts ζ e).length = 2 := by cases ζ <;> rfl
  have hsd : ∀ x ∈ X.sideDarts ζ e,
      (X.sideList ζ P).idxOf x = p ∨ (X.sideList ζ P).idxOf x = p + 1 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := hp k hk
    omega
  have hfQ : f ∈ Q := List.mem_of_mem_head? hf
  have hgQ : g ∈ Q := List.mem_of_mem_getLast? hg
  have hfg : f ≠ X.inv g := by
    intro h
    have h1 := hR.isStrandPath.isOut_eq_true f hfQ
    rw [h, hX.isOut_inv_apply (hR.isStrandPath.notMem_bdry g hgQ),
      hR.isStrandPath.isOut_eq_true g hgQ] at h1
    exact Bool.false_ne_true h1
  have hidx : (X.sideList ζ P).idxOf f ≠ (X.sideList ζ P).idxOf (X.inv g) := fun h =>
    hfg ((List.idxOf_inj (hinf.subset hfe)).1 h)
  have hJ : X.hugDarts P ζ Q = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro d hd
    obtain ⟨t, -, h1, h2, -⟩ := (mem_hugDarts_iff (Option.mem_def.1 hf) (Option.mem_def.1 hg)).1 hd
    have := hsd f hfe
    have := hsd _ hge
    omega
  have hlen := hQ.length_hugDarts
  rw [hJ, List.length_nil] at hlen
  have hQ1 : Q.length = 1 := by
    have := List.length_pos_iff.2 hR.isStrandPath.ne_nil
    omega
  obtain ⟨q, rfl⟩ := List.length_eq_one_iff.1 hQ1
  rcases X.isHollowMonogon_of_isMonogon_singleton hX hmono with h | h <;> exact ⟨_, h⟩

/-! ### Diagrams agreeing at the points of a strand path -/

/-- A diagram with the same involution as `X`, whose rotation agrees with that of `X` at every
dart not lying at a triple point avoided by the strand path `P`, has the same side lists along
`P`. -/
private theorem sideList_eq_of_rot_eq {X X' : TripleData H b} {P : List H}
    (hP : X.IsStrandPath P) (hinv : X'.inv = X.inv)
    (hrot : ∀ d, ¬(X.vertexOf d ∈ X.internalVertices ∧ ∀ e ∈ P, X.vertexOf d ≠ X.vertexOf e) →
      X'.rot d = X.rot d) (ζ : StrandSide) :
    X'.sideList ζ P = X.sideList ζ P := by
  have h : ∀ ζ', ∀ e ∈ P.dropLast, X'.sideDarts ζ' e = X.sideDarts ζ' e := by
    intro ζ' e he
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem he
    rw [List.length_dropLast] at hl
    rw [List.getElem_dropLast]
    refine sideDarts_eq_of_forall_mem_vertexOf hinv (fun d hd => hrot d ?_) ζ'
    rintro ⟨-, hav⟩
    refine hav P[l + 1] (List.getElem_mem _) ?_
    have hstep := ((X.isStrandPath_iff_getElem.1 hP).2.2 l (by omega)).2
    rw [hstep, X.vertexOf_rot_pow_apply, X.vertexOf_eq_of_mem hd]
  cases ζ
  · exact List.flatMap_congr (h _)
  · exact List.flatMap_congr fun e he => h _ e (List.mem_reverse.1 he)

/-! ### Making an arc of the inside hug the monogon -/

/-- The second half of Case B: given the lift `X'` of a straightening `Y'` of the inside `X|_M`,
with the arc of `Y'` from `s_j` boundary-parallel along the interval `I` of the arc `j` of `X|_M`
whose interior positions carry the inside list entries strictly between its ends, the arc `j` of
`X'|_M` hugs `M`. The inside of `X'` is taken along a set `K'` and a list `L'` equal to those of
`X`. -/
private theorem exists_hugs_aux {X X' : TripleData H b} {P : List H} {ζ : StrandSide}
    {h : X.faceOrbits → ℤ} (hX' : X'.IsTripleDiagram) {K' : Finset H} {L' : List H}
    (hK : K' = X.insideDarts P ζ h) (hL : L' = X.insideList ζ P)
    (hside : X'.sideList ζ P = L') (hc' : X'.IsCutData K' L')
    (hY' : (X'.cut K' L' ζ.cutShift).IsTripleDiagram)
    (hhug' : ∀ (Q' : List {d // d ∈ K'}) (j' : Fin (L'.length / 2)),
      Q'.map Sum.inl = (X'.cut K' L' ζ.cutShift).arc j' →
      ∀ I, (X'.cut K' L' ζ.cutShift).IsBoundaryParallel j' I →
      (∀ r, r ∈ intervalInterior (X'.cut K' L' ζ.cutShift).strandPerm j' I ↔
        ∃ d ∈ X'.hugDarts P ζ (Q'.map Subtype.val), ∃ hd : d ∈ K',
          (X'.cut K' L' ζ.cutShift).endDart r = .inl ⟨d, hd⟩) →
      ∃ a c, X'.Hugs P ζ (Q'.map Subtype.val) a c)
    {Y' : TripleDiagram ((X.insideList ζ P).length / 2)}
    (hiso : (X'.cut K' L' ζ.cutShift).HIsomorphic Y'.data)
    (hπY' : Y'.data.strandPerm = (X.monogonCut P ζ h).strandPerm)
    {j : Fin ((X.insideList ζ P).length / 2)}
    {I : Finset (Fin (2 * ((X.insideList ζ P).length / 2)))}
    (hbp : Y'.data.IsBoundaryParallel j I)
    (hImem : ∀ r, r ∈ intervalInterior (X.monogonCut P ζ h).strandPerm j I ↔
      min (cutEndIndex (X.insideList ζ P) ζ.cutShift (sourceIndex j) : ℕ)
          (cutEndIndex (X.insideList ζ P) ζ.cutShift
            (targetIndex ((X.monogonCut P ζ h).strandPerm j))) <
          cutEndIndex (X.insideList ζ P) ζ.cutShift r ∧
        (cutEndIndex (X.insideList ζ P) ζ.cutShift r : ℕ) <
          max (cutEndIndex (X.insideList ζ P) ζ.cutShift (sourceIndex j) : ℕ)
            (cutEndIndex (X.insideList ζ P) ζ.cutShift
              (targetIndex ((X.monogonCut P ζ h).strandPerm j)))) :
    ∃ Q a c, X'.Hugs P ζ Q a c := by
  subst hK hL
  have hLnd := hc'.nodup
  obtain ⟨θ⟩ := hIsomorphic_iff_isomorphic.1 hiso
  have hπZ : (X'.cut (X.insideDarts P ζ h) (X.insideList ζ P) ζ.cutShift).strandPerm =
      (X.monogonCut P ζ h).strandPerm :=
    (θ.strandPerm_eq hY'.toIsPreTripleDiagram Y'.isTripleDiagram.toIsPreTripleDiagram).symm.trans
      hπY'
  have hbpZ := isBoundaryParallel_of_iso θ hY' Y'.isTripleDiagram hbp
  obtain ⟨Q₂, hQ₂, -, hf, hl⟩ := arc_cut_ends hX' hc' hY' j
  obtain ⟨g, hg, hgx⟩ := Option.map_eq_some_iff.1 hl
  set π' := (X'.cut (X.insideDarts P ζ h) (X.insideList ζ P) ζ.cutShift).strandPerm
  have hImem' : ∀ r, r ∈ intervalInterior π' j I ↔
      min (cutEndIndex (X.insideList ζ P) ζ.cutShift (sourceIndex j) : ℕ)
          (cutEndIndex (X.insideList ζ P) ζ.cutShift (targetIndex (π' j))) <
          cutEndIndex (X.insideList ζ P) ζ.cutShift r ∧
        (cutEndIndex (X.insideList ζ P) ζ.cutShift r : ℕ) <
          max (cutEndIndex (X.insideList ζ P) ζ.cutShift (sourceIndex j) : ℕ)
            (cutEndIndex (X.insideList ζ P) ζ.cutShift (targetIndex (π' j))) := by
    rwa [hπZ]
  have hmemJ : ∀ d, d ∈ X'.hugDarts P ζ (Q₂.map Subtype.val) ↔
      ∃ t, ∃ ht : t < (X.insideList ζ P).length,
        min (cutEndIndex (X.insideList ζ P) ζ.cutShift (sourceIndex j) : ℕ)
            (cutEndIndex (X.insideList ζ P) ζ.cutShift (targetIndex (π' j))) < t ∧
          t < max (cutEndIndex (X.insideList ζ P) ζ.cutShift (sourceIndex j) : ℕ)
            (cutEndIndex (X.insideList ζ P) ζ.cutShift (targetIndex (π' j))) ∧
          (X.insideList ζ P)[t] = d := by
    intro d
    rw [mem_hugDarts_iff hf hg]
    simp only [hside, hgx, hLnd.idxOf_getElem]
    exact Iff.rfl
  obtain ⟨a, c, hH⟩ := hhug' Q₂ j hQ₂ I hbpZ fun r => by
    rw [hImem' r, cut_endDart, hc'.cutListDart_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, (hmemJ _).2 ⟨_, Fin.isLt _, h1, h2, rfl⟩, hc'.getElem_mem _, rfl⟩
    · rintro ⟨d, hd, hdK, he⟩
      have hde := congrArg Subtype.val (Sum.inl_injective he)
      simp only at hde
      subst hde
      obtain ⟨t, ht, h1, h2, h3⟩ := (hmemJ _).1 hd
      rw [← hLnd.getElem_inj_iff.1 h3]
      exact ⟨h1, h2⟩
  exact ⟨_, a, c, hH⟩

/-- Let `M` be a convex monogon with inside `ζ` and `m ≥ 2` darts of a triple diagram `X`, whose
inside `X|_M` has the straightening property. Then some triple diagram `X' ∼ X`, with the same
darts, has `M` as a convex monogon with inside `ζ` and a returning path of `M` on side `ζ` that
hugs `M`. -/
private theorem IsConvexMonogon.exists_hugs_of_hasStraighteningProperty {X : TripleData H b}
    {P : List H} {ζ : StrandSide} {h : X.faceOrbits → ℤ} (hM : X.IsConvexMonogon P ζ)
    (hX : X.IsTripleDiagram) (hh : X.IsMonogonWindingFunction P h) (hm : 2 ≤ P.length)
    (hst : TripleDiagram.HasStraighteningProperty
      ⟨_, X.monogonCut P ζ h, hM.isTripleDiagram_monogonCut hX hh hm⟩) :
    ∃ (X' : TripleData H b) (hX' : X'.IsTripleDiagram),
      TripleDiagram.MoveEquivalent ⟨H, X, hX⟩ ⟨H, X', hX'⟩ ∧ X'.IsConvexMonogon P ζ ∧
      ∃ Q a c, X'.Hugs P ζ Q a c := by
  have hY := hM.isTripleDiagram_monogonCut hX hh hm
  have hs : ζ.cutShift ≤ 1 := by cases ζ <;> simp [StrandSide.cutShift]
  have hev : Even (X.insideList ζ P).length := by
    rw [length_insideList]
    exact even_two_mul _
  have hlen := length_insideList (X := X) ζ P
  -- an arc of the inside with a run of least size
  let run : Fin ((X.insideList ζ P).length / 2) → ℕ := fun j =>
    max (cutEndIndex (X.insideList ζ P) ζ.cutShift (sourceIndex j) : ℕ)
        (cutEndIndex (X.insideList ζ P) ζ.cutShift
          (targetIndex ((X.monogonCut P ζ h).strandPerm j))) -
      min (cutEndIndex (X.insideList ζ P) ζ.cutShift (sourceIndex j) : ℕ)
        (cutEndIndex (X.insideList ζ P) ζ.cutShift
          (targetIndex ((X.monogonCut P ζ h).strandPerm j)))
  obtain ⟨j, -, hj⟩ := exists_min_image univ run ⟨⟨0, by omega⟩, mem_univ _⟩
  -- its interval `I_Q` is minimal
  obtain ⟨I, hIint, hImem⟩ := exists_isIntervalOf_cut hs hev (X.monogonCut P ζ h).strandPerm j
  have hImin : IsMinimalInterval (X.monogonCut P ζ h).strandPerm j I := by
    refine ⟨hIint, fun j' hj' ⟨h1, h2⟩ => ?_⟩
    have hr1 : sourceIndex j' ∈ intervalInterior (X.monogonCut P ζ h).strandPerm j I := by
      rw [intervalInterior, mem_sdiff, mem_insert, mem_singleton]
      exact ⟨h1, fun h => h.elim (fun h => hj' (sourceIndex_injective h))
        (sourceIndex_ne_targetIndex _ _)⟩
    have hr2 : targetIndex ((X.monogonCut P ζ h).strandPerm j') ∈
        intervalInterior (X.monogonCut P ζ h).strandPerm j I := by
      rw [intervalInterior, mem_sdiff, mem_insert, mem_singleton]
      exact ⟨h2, fun h => h.elim (fun h => sourceIndex_ne_targetIndex _ _ h.symm)
        (fun h => hj' (strandPerm_injective'' hY (targetIndex_injective h)))⟩
    obtain ⟨hm1, hm2⟩ := (hImem _).1 hr1
    obtain ⟨hm3, hm4⟩ := (hImem _).1 hr2
    have := hj j' (mem_univ _)
    simp only [run] at this
    omega
  -- straightening the inside and lifting the moves
  obtain ⟨Y', hYY', hbp⟩ := hst.2 j I hImin
  obtain ⟨X', hX', hXX', hinv, -, -, -, hrot, hM', h', hh', hK', hN, hiso⟩ :=
    hM.exists_moveEquivalent_monogonCut hX hh hm hYY'
  exact ⟨X', hX', hXX', hM', exists_hugs_aux (h := h) hX' hK'
    (sideList_eq_of_rot_eq hM.isMonogon.isStrandPath hinv hrot ζ) rfl
    (hM'.isCutData_insideDarts hX' hh')
    (hM'.isTripleDiagram_monogonCut hX' hh' hm)
    (fun Q' j' hQ' I hB hI => hM'.hugs_of_isBoundaryParallel_monogonCut hX' hh' hm hQ' hB hI)
    ⟨hN, hiso⟩ hYY'.strandPerm_eq hbp hImem⟩

end MinimalMonogon

end TripleData

namespace TripleDiagram

variable {b : ℕ}

open TripleData in
/-- If a convex monogon `M` of `Y` has the fewest darts among the convex monogons of diagrams
move-equivalent to `Y`, and its inside is monogon-stable, then some diagram move-equivalent to `Y`
has a hollow monogon. -/
theorem exists_isHollowMonogon_of_isMonogonStable {Y : TripleDiagram b} {P : List Y.Dart}
    {ζ : StrandSide} {h : Y.data.faceOrbits → ℤ} (hM : Y.data.IsConvexMonogon P ζ)
    (hh : Y.data.IsMonogonWindingFunction P h) (hm : 2 ≤ P.length)
    (hst : TripleDiagram.IsMonogonStable
      ⟨_, Y.data.monogonCut P ζ h, hM.isTripleDiagram_monogonCut Y.isTripleDiagram hh hm⟩)
    (hmin : ∀ Z : TripleDiagram b, Y.MoveEquivalent Z → ∀ P' ζ',
      Z.data.IsConvexMonogon P' ζ' → P.length ≤ P'.length) :
    ∃ X' : TripleDiagram b, Y.MoveEquivalent X' ∧ ∃ c, X'.data.IsHollowMonogon {c} := by
  obtain ⟨Z, hZ, hYZ, hMZ, Q, a, c, hQ⟩ := hM.exists_hugs_of_hasStraighteningProperty
    Y.isTripleDiagram hh hm hst.hasStraighteningProperty
  rcases lt_trichotomy a c with hac | rfl | hca
  · obtain ⟨σ', -, hσ', hmv, e, he⟩ := exists_hollowMonogon_of_hugs ⟨Y.Dart, Z, hZ⟩ hac hQ
    exact ⟨_, hYZ.trans hmv, e, he⟩
  · obtain ⟨e, he⟩ := exists_isHollowMonogon_of_hugs_self hZ.toIsPreTripleDiagram
      (hMZ.isCutData_insideDarts hZ (existsUnique_isMonogonWindingFunction hZ hMZ.isMonogon
        hMZ.isSimpleStrandPath).exists.choose_spec).nodup hQ
    exact ⟨_, hYZ, e, he⟩
  · exfalso
    obtain ⟨R, hR, -, -⟩ := hQ.exists_closedAlignedRail hZ.toIsPreTripleDiagram hca
    obtain ⟨hW, hmvW⟩ := exists_moveEquivalent_pushOff ⟨Y.Dart, Z, hZ⟩ R
    obtain ⟨P', hP', hlen, hhead, -⟩ :=
      ClosedAlignedRail.exists_isSimpleStrandPath_pushOff hZ.toIsPreTripleDiagram R
        hMZ.isSimpleStrandPath hR
    have := hmin ⟨Y.Dart, R.pushOff, hW⟩ (hYZ.trans hmvW) P' ζ
      (ClosedAlignedRail.isConvexMonogon_pushOff hZ hMZ R hR hP'.isStrandPath hlen hhead)
    omega

open TripleData in
/-- A hollow monogon in a diagram move-equivalent to the inside of a convex monogon of `Y` lifts to
a hollow monogon of a diagram move-equivalent to `Y`. -/
theorem exists_isHollowMonogon_of_moveEquivalent_monogonCut {Y : TripleDiagram b}
    {P : List Y.Dart} {ζ : StrandSide} {h : Y.data.faceOrbits → ℤ}
    (hM : Y.data.IsConvexMonogon P ζ) (hh : Y.data.IsMonogonWindingFunction P h)
    (hm : 2 ≤ P.length) {D : TripleDiagram ((Y.data.insideList ζ P).length / 2)}
    (hD : TripleDiagram.MoveEquivalent
      ⟨_, Y.data.monogonCut P ζ h, hM.isTripleDiagram_monogonCut Y.isTripleDiagram hh hm⟩ D)
    {c : D.Dart} (hc : D.data.IsHollowMonogon {c}) :
    ∃ X' : TripleDiagram b, Y.MoveEquivalent X' ∧ ∃ c, X'.data.IsHollowMonogon {c} := by
  obtain ⟨Z, hZ, hYZ, -, -, -, -, -, hMZ, h', hh', -, hN, hiso⟩ :=
    hM.exists_moveEquivalent_monogonCut Y.isTripleDiagram hh hm hD
  obtain ⟨d, hd⟩ := HIsomorphic.exists_isHollowMonogon' ⟨hN, hiso⟩ hc
  obtain ⟨d', -, hd'⟩ := hMZ.exists_isHollowMonogon_of_isHollowMonogon_monogonCut hZ hh' hd
  exact ⟨⟨Y.Dart, Z, hZ⟩, hYZ, _, hd'⟩

open TripleData in
/-- **A monogon can be made hollow**: if a triple diagram `X` has a monogon, then some triple
diagram move-equivalent to `X` has a hollow monogon. -/
@[cluster_algebras "lem_monogon_to_hollow"]
theorem exists_moveEquivalent_isHollowMonogon (X : TripleDiagram b) (hX : X.data.HasMonogon) :
    ∃ X' : TripleDiagram b, X.MoveEquivalent X' ∧ ∃ c, X'.data.IsHollowMonogon {c} := by
  classical
  suffices key : ∀ n (b : ℕ) (X : TripleDiagram b), X.data.internalVertices.card = n →
      X.data.HasMonogon →
        ∃ X' : TripleDiagram b, X.MoveEquivalent X' ∧ ∃ c, X'.data.IsHollowMonogon {c} from
    key _ b X rfl hX
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro b X hn hmono
  -- a convex monogon with the fewest darts among the diagrams move-equivalent to `X`
  have hex : ∃ m, ∃ Y : TripleDiagram b, X.MoveEquivalent Y ∧
      ∃ P ζ, Y.data.IsConvexMonogon P ζ ∧ P.length = m := by
    obtain ⟨P, ζ, hP⟩ := exists_isConvexMonogon X.isTripleDiagram hmono
    exact ⟨_, X, MoveEquivalent.refl X, P, ζ, hP, rfl⟩
  obtain ⟨Y, hXY, P, ζ, hM, hPm⟩ := Nat.find_spec hex
  have hminm : ∀ Z : TripleDiagram b, X.MoveEquivalent Z → ∀ P' ζ',
      Z.data.IsConvexMonogon P' ζ' → P.length ≤ P'.length := fun Z hZ P' ζ' hP' =>
    hPm ▸ Nat.find_min' hex ⟨Z, hZ, P', ζ', hP', rfl⟩
  have hYX := Y.isTripleDiagram
  -- a convex monogon of one dart is hollow
  rcases Nat.lt_or_ge P.length 2 with hm | hm
  · have h1 : P.length = 1 := by
      have := hM.length_pos
      omega
    obtain ⟨e, rfl⟩ := List.length_eq_one_iff.1 h1
    rcases Y.data.isHollowMonogon_of_isMonogon_singleton hYX.toIsPreTripleDiagram hM.isMonogon
      with h | h <;> exact ⟨Y, hXY, _, h⟩
  obtain ⟨h, hh, -⟩ := hM.exists_windingFunction
  -- the inside has fewer triple points
  have hDcard : (Y.data.monogonCut P ζ h).internalVertices.card < n := by
    have h1 := hM.card_internalVertices_monogonCut_le hYX hh
    have h2 := hXY.card_internalVertices_eq
    have h3 : 0 < Y.data.internalVertices.card := card_pos.2 ⟨_, hM.isMonogon.pathStart_mem⟩
    have h4 := hM.length_pos
    omega
  by_cases hst : TripleDiagram.IsMonogonStable
      ⟨_, Y.data.monogonCut P ζ h, hM.isTripleDiagram_monogonCut hYX hh hm⟩
  · obtain ⟨X', hYX', hX'⟩ := exists_isHollowMonogon_of_isMonogonStable hM hh hm hst
      fun Z hZ => hminm Z (hXY.trans hZ)
    exact ⟨X', hXY.trans hYX', hX'⟩
  · simp only [IsMonogonStable, not_forall, not_not] at hst
    obtain ⟨D', hDD', hD'm⟩ := hst
    obtain ⟨D'', hD'D'', c, hc⟩ := ihn _ (by rwa [hDD'.card_internalVertices_eq])
      _ D' rfl hD'm
    obtain ⟨X', hYX', hX'⟩ :=
      exists_isHollowMonogon_of_moveEquivalent_monogonCut hM hh hm (hDD'.trans hD'D'') hc
    exact ⟨X', hXY.trans hYX', hX'⟩

/-- **Minimal diagrams are monogon-stable**: a minimal triple diagram is monogon-stable. -/
@[cluster_algebras "lem_minimal_monogon_stable"]
theorem IsMinimal.isMonogonStable {X : TripleDiagram b} (hX : X.IsMinimal) :
    X.IsMonogonStable := by
  intro X' hXX' hmono
  obtain ⟨X'', hX'X'', c, hc⟩ := X'.exists_moveEquivalent_isHollowMonogon hmono
  exact X''.not_isMinimal_of_isHollowMonogon hc (hX.of_moveEquivalent (hXX'.trans hX'X''))

/-- **A minimal triple diagram has no badgons**: a minimal triple diagram has no monogon and no
parallel digon. -/
@[cluster_algebras "lem_minimal_no_badgon"]
theorem IsMinimal.not_hasBadgon {X : TripleDiagram b} (hX : X.IsMinimal) :
    ¬X.data.HasBadgon := by
  have hs := hX.isMonogonStable
  rintro (h | h)
  · exact hs X (MoveEquivalent.refl X) h
  · exact hs.hasStraighteningProperty.1 X (MoveEquivalent.refl X) h

/-- **A minimal triple diagram has no closed strands**: no strand of a minimal triple diagram is
closed. -/
@[cluster_algebras "lem_minimal_no_closed_strand"]
theorem IsMinimal.not_isClosedStrand {X : TripleDiagram b} (hX : X.IsMinimal)
    (C : Finset X.Dart) : ¬X.data.IsClosedStrand C :=
  TripleData.not_isClosedStrand_of_not_hasBadgon X.isTripleDiagram hX.not_hasBadgon C

end TripleDiagram

end ClusterAlgebras

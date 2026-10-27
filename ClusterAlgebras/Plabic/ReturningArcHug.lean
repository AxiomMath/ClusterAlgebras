/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BoundaryParallelCuts

/-!
# Making a minimal returning arc hug

This file proves a step of D. Thurston's straightening argument for triple diagrams. Let `S` be a
simple arc of a triple diagram `X`, from `s_i`, and `ζ` a side with `N_ζ ≥ 2`. The returning paths
of `S` on side `ζ` are the arcs of the cut `X|_{S,ζ}` both of whose end legs lie in the `ζ` list of
`S`. If `Q` is a returning path such that no returning path has both ends strictly between those of
`Q` in the `ζ` list, then the interval `I_Q` of the pair of `Q` whose interior positions carry the
darts of the `ζ` list strictly between the ends of `Q` is a minimal interval of the cut. If the cut
has the straightening property, moves of the cut make its arc from the first end of `Q`
boundary-parallel along `I_Q`; lifting these moves to `X` gives `X' ∼ X` in which `S` and its `ζ`
list are unchanged, every returning path of `S` keeps its two ends, and the returning path with the
ends of `Q` hugs `S`.

## Main results

* `ClusterAlgebras.TripleData.IsSimpleArc.exists_moveEquivalent_hugs`: making a minimal returning
  arc hug.

## Implementation notes

* Labels are `0`-indexed: a returning path from `z_{a+1}` to `z_{c+1}` is
  `X.IsReturningPath (X.arc i) ζ Q a c`, and the arc label `i : Fin b` is FWZ's `i + 1`.
* The minimality of `Q` is stated in the form produced by
  `ClusterAlgebras.TripleData.exists_isReturningPath_minimal`: a dart lies strictly between `f` and
  `g` in the `ζ` list `L` when `L.idxOf` of it lies strictly between `L.idxOf f` and `L.idxOf g`.
  The condition is required of all returning paths, which is equivalent, since the ends of `Q`
  itself are not strictly between them.
* The returning paths of `S` in `X'` are given with the same points `z_{a'+1}`, `z_{c'+1}` as in
  `X`, as the rotation of `X'` agrees with that of `X` at the points of `S`. The returning path of
  `X'` with the ends of `Q` is the one that hugs `S`.
* FWZ assume that `X` is monogon-stable; the argument does not use it, and the hypothesis
  is omitted.
* The interval `I_Q` is the cyclic interval between the positions of the two ends of `Q` that
  contains the positions of the cut list entries between them; the cut list starts with the legs
  of `X` on side `ζ` and ends with the `ζ` list of `S`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace TripleData

section ReturningArcHug

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

/-! ### Intervals of a cut read on its cut list -/

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
  have hval : ∀ r : Fin (2 * (L.length / 2)),
      (cutEndIndex L s r : ℕ) = ((r : ℕ) + s) % (2 * (L.length / 2)) := by
    intro r
    simp only [cutEndIndex]
    exact congrArg (((r : ℕ) + s) % ·) (Nat.two_mul_div_two_of_even hev).symm
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
    rw [← this]
    exact hd
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
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_one_of_ne_zero h1.ne'
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
  have : X.arcEndIndex j = X.arcEndIndex j' := by
    simp only [arcEndIndex, h]
  rw [this, h2] at h1
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
    apply hS' k l (by rwa [hlen]) (by rwa [hlen])
    rw [← θ.map_arcDart hp hp', ← θ.map_arcDart hp hp', ← θ.map_inv, ← θ.map_inv,
      ← θ.map_vertexOf, ← θ.map_vertexOf, hv]
  refine ⟨hI, hS, ?_, fun r hr => ?_⟩
  · rw [← hcard, hS.ncard_passesThrough hX, hS'.ncard_passesThrough hX', hlen]
  · obtain ⟨hint, d, hd, hdv⟩ := hpass r hr
    rw [← θ.map_endDart hp hp', ← θ.map_inv] at hint hdv
    refine ⟨X.vertexOf_mem_internalVertices.2
      ((θ.isBoundaryVertex_vertexOf_iff _).not.1 (X'.vertexOf_mem_internalVertices.1 hint)), ?_⟩
    obtain ⟨t, ht, rfl⟩ := mem_arc_toFinset.1 hd
    refine ⟨X.arcDart j t, mem_arc_toFinset.2 ⟨t, by rwa [← hlen], rfl⟩, ?_⟩
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

/-- The darts of the arc from `s_i` other than the last. -/
private theorem mem_dropLast_arc' {X : TripleData H b} {i : Fin b} {e : H} :
    e ∈ (X.arc i).dropLast ↔ ∃ k, k + 1 < X.arcLength i ∧ e = X.arcDart i k := by
  rw [List.mem_iff_getElem]
  simp only [List.length_dropLast, length_arc, List.getElem_dropLast, getElem_arc]
  constructor <;> rintro ⟨k, hk, rfl⟩ <;> exact ⟨k, by omega, rfl⟩

/-- If `σ'` agrees with `σ` at every dart not lying at a triple point avoided by the arc `S` from
`s_i`, then `σ'` agrees with `σ` at the points `z_l` of `S`. -/
private theorem rot_eq_of_mem_dropLast_arc {X X' : TripleData H b} {i : Fin b}
    (hX : X.IsTripleDiagram)
    (hrot : ∀ d, ¬(X.vertexOf d ∈ X.internalVertices ∧
      ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) → X'.rot d = X.rot d)
    {e : H} (he : e ∈ (X.arc i).dropLast) : ∀ d ∈ X.vertexOf (X.inv e), X'.rot d = X.rot d := by
  obtain ⟨k, hk, rfl⟩ := mem_dropLast_arc'.1 he
  intro d hd
  apply hrot
  rintro ⟨hint, hpass⟩
  apply hpass
  refine ⟨hint, X.arcDart i (k + 1), mem_arc_toFinset.2 ⟨k + 1, hk, rfl⟩, ?_⟩
  rw [arcDart_succ_eq hX hk, X.vertexOf_rot_pow_apply, X.vertexOf_eq_of_mem hd]

/-- A diagram with the same involution as `X` and the same rotation at the points of the arc `S`
from `s_i` has the same `ζ` list along `S`. -/
private theorem sideList_arc_eq {X X' : TripleData H b} {i : Fin b} (hX : X.IsTripleDiagram)
    (hinv : X'.inv = X.inv)
    (hrot : ∀ d, ¬(X.vertexOf d ∈ X.internalVertices ∧
      ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) → X'.rot d = X.rot d)
    (ζ : StrandSide) : X'.sideList ζ (X.arc i) = X.sideList ζ (X.arc i) := by
  have h : ∀ ζ', ∀ e ∈ (X.arc i).dropLast, X'.sideDarts ζ' e = X.sideDarts ζ' e := fun ζ' e he =>
    sideDarts_eq_of_forall_mem_vertexOf hinv (rot_eq_of_mem_dropLast_arc hX hrot he) ζ'
  cases ζ
  · exact List.flatMap_congr (h _)
  · exact List.flatMap_congr fun e he => h _ e (List.mem_reverse.1 he)

/-- A returning path of `P` in `X'` with the ends of a returning path of `P` in `X` from `z_{a+1}`
to `z_{c+1}` runs from `z_{a+1}` to `z_{c+1}`, if `X'` and `X` have the same involution and the
same `ζ` darts at the darts of `P`. -/
private theorem isReturningPath_of_ends {X X' : TripleData H b} {P : List H} {ζ : StrandSide}
    {U U' : List H} {a c a' c' : ℕ} (hinv : X'.inv = X.inv)
    (hside : ∀ e ∈ P.dropLast, X'.sideDarts ζ e = X.sideDarts ζ e)
    (hU : X.IsReturningPath P ζ U a c) (hU' : X'.IsReturningPath P ζ U' a' c')
    (hhead : U'.head? = U.head?) (hlast : U'.getLast?.map X.inv = U.getLast?.map X.inv) :
    X'.IsReturningPath P ζ U' a c := by
  have hmem : ∀ x (hx : x + 1 < P.length), ∀ e ∈ P[x]?, e ∈ P.dropLast := by
    intro x hx e he
    have h : P.dropLast[x]? = some e := by
      rw [List.getElem?_dropLast, if_pos (by omega)]
      exact he
    exact List.mem_of_getElem? h
  refine ⟨hU'.isSimpleStrandPath, hU'.isStrandPath, hU.lt_left, hU.lt_right, ?_, ?_,
    hU'.interiorPoints_ne⟩
  · obtain ⟨e, he, f, hf, hfe⟩ := hU.head?_mem
    refine ⟨e, he, f, hhead ▸ hf, ?_⟩
    rwa [hside e (hmem a hU.lt_left e he)]
  · obtain ⟨e, he, f, hf, hfe⟩ := hU.getLast?_mem
    have h1 : U'.getLast?.map X.inv = some (X.inv f) := by
      rw [hlast, Option.mem_def.1 hf, Option.map_some]
    obtain ⟨f', hf', hff⟩ := Option.map_eq_some_iff.1 h1
    refine ⟨e, he, f', hf', ?_⟩
    rwa [hside e (hmem c hU.lt_right e he), hinv, hff]

/-! ### Darts strictly between two darts of a list -/

omit [Fintype H] in
/-- A dart lies in `X.hugDarts P ζ Q` exactly when it is an entry of `X.sideList ζ P` strictly
between the first dart `f` of `Q` and the reverse `X.inv g` of its last dart `g`. -/
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
      exact ⟨x + 1 + n, by omega, by omega, by omega,
        by simp [List.getElem_take, List.getElem_drop]⟩
    · rintro ⟨t, ht, h1, h2, rfl⟩
      refine ⟨t - (x + 1), by simp only [List.length_take, List.length_drop]; omega, ?_⟩
      simp only [List.getElem_take, List.getElem_drop]
      congr 1
      omega
  · rw [List.mem_reverse, List.mem_iff_getElem]
    constructor
    · rintro ⟨n, hn, rfl⟩
      simp only [List.length_take, List.length_drop] at hn
      exact ⟨y + 1 + n, by omega, by omega, by omega,
        by simp [List.getElem_take, List.getElem_drop]⟩
    · rintro ⟨t, ht, h1, h2, rfl⟩
      refine ⟨t - (y + 1), by simp only [List.length_take, List.length_drop]; omega, ?_⟩
      simp only [List.getElem_take, List.getElem_drop]
      congr 1
      omega

omit [Fintype H] [DecidableEq H] in
/-- In a list `pre ++ Λ` without repetition, the entry of index `x` lies in `Λ` exactly when
`x ≥ |pre|`. -/
private theorem getElem_mem_iff_of_eq_append {L pre Λ : List H} (hnd : L.Nodup)
    (hL : L = pre ++ Λ) {x : ℕ} (hx : x < L.length) : L[x] ∈ Λ ↔ pre.length ≤ x := by
  subst hL
  constructor
  · intro h
    by_contra hlt
    rw [List.getElem_append_left (by omega)] at h
    exact List.disjoint_of_nodup_append hnd (List.getElem_mem _) h
  · intro h
    rw [List.getElem_append_right h]
    exact List.getElem_mem _

omit [Fintype H] [DecidableEq H] in
/-- In a list `pre ++ Λ` without repetition, the entry of index `|pre| + t` is the entry `t` of
`Λ`, and no other entry. -/
private theorem getElem_eq_iff_of_eq_append {L pre Λ : List H} (hnd : L.Nodup)
    (hL : L = pre ++ Λ) {x : ℕ} (hx : x < L.length) {t : ℕ} (ht : t < Λ.length) :
    Λ[t] = L[x] ↔ x = pre.length + t := by
  subst hL
  have h : (pre ++ Λ)[pre.length + t]'(by simp; omega) = Λ[t] := by
    rw [List.getElem_append_right (by omega)]
    simp
  exact ⟨fun h' => (hnd.getElem_inj_iff.1 (h.trans h')).symm, by rintro rfl; exact h.symm⟩

omit [Fintype H] in
/-- In a list `pre ++ Λ` without repetition, the entry of index `x ≥ |pre|` has index `x - |pre|`
in `Λ`. -/
private theorem idxOf_getElem_of_eq_append {L pre Λ : List H} (hnd : L.Nodup)
    (hL : L = pre ++ Λ) {x : ℕ} (hx : x < L.length) (hp : pre.length ≤ x) :
    Λ.idxOf L[x] = x - pre.length := by
  have hlen : L.length = pre.length + Λ.length := by rw [hL, List.length_append]
  rw [← (getElem_eq_iff_of_eq_append hnd hL hx (t := x - pre.length) (by omega)).2 (by omega)]
  exact (List.nodup_append.1 (hL ▸ hnd)).2.1.idxOf_getElem _ _

omit [Fintype H] in
/-- In a list `L = pre ++ Λ` without repetition, `Λ` the `ζ` list of `P`, the entry of `L` of index
`z` is a hug dart of `Q` exactly when `z` lies strictly between the indices in `L` of the first
dart of `Q` and of the reverse of its last dart. -/
private theorem getElem_mem_hugDarts_iff {X : TripleData H b} {P Q L pre : List H}
    {ζ : StrandSide} (hnd : L.Nodup) (hL : L = pre ++ X.sideList ζ P) {x y : ℕ}
    (hx : x < L.length) (hy : y < L.length) (hpx : pre.length ≤ x) (hpy : pre.length ≤ y) {g : H}
    (hf : Q.head? = some L[x]) (hg : Q.getLast? = some g) (hgy : X.inv g = L[y]) {z : ℕ}
    (hz : z < L.length) : L[z] ∈ X.hugDarts P ζ Q ↔ min x y < z ∧ z < max x y := by
  have hlen : L.length = pre.length + (X.sideList ζ P).length := by rw [hL, List.length_append]
  rw [mem_hugDarts_iff hf hg, hgy, idxOf_getElem_of_eq_append hnd hL hx hpx,
    idxOf_getElem_of_eq_append hnd hL hy hpy]
  constructor
  · rintro ⟨t, ht, h1, h2, h3⟩
    have := (getElem_eq_iff_of_eq_append hnd hL hz ht).1 h3
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨z - pre.length, by omega, by omega, by omega,
      (getElem_eq_iff_of_eq_append hnd hL hz (by omega)).2 (by omega)⟩

/-! ### Arcs of the cut along a simple arc -/

/-- The first dart of the arc from `s_j` of the cut along `S` on side `ζ` is the entry of the cut
list at the position of `s_j`, and the reverse of its last dart the entry at the position of
`t_{π(j)}`. -/
private theorem arcCut_arc_ends {H : Type} [Fintype H] [DecidableEq H] {X : TripleData H b}
    {i : Fin b} {ζ : StrandSide} (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (hN : 2 ≤ (X.arcCutList i ζ).length) (j : Fin ((X.arcCutList i ζ).length / 2)) :
    ∃ Q : List {d // d ∈ X.arcSideDarts i ζ}, Q.map Sum.inl = (X.arcCut i ζ).arc j ∧
      (Q.map Subtype.val).head? = some (X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ)
        ζ.cutShift (sourceIndex j) : ℕ)] ∧
      (Q.map Subtype.val).getLast?.map X.inv = some (X.arcCutList i ζ)[(cutEndIndex
        (X.arcCutList i ζ) ζ.cutShift (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ)] := by
  obtain ⟨Q, h1, -, h2, h3⟩ := arc_cut_ends (s := ζ.cutShift) hX (hS.isCutData_arcCutList hX ζ)
    (hS.isTripleDiagram_arcCut hX ζ hN) j
  exact ⟨Q, h1, h2, h3⟩

/-- If `X'` has the involution of `X`, agrees with `X` at the points of `S`, and the arcs of its
cut along `S` with both ends in the `ζ` list are returning paths, then an arc of the cut of `X`
that is a returning path of `S` gives the arc of the cut of `X'` with the same index, a returning
path of `S` in `X'` with the same ends. -/
private theorem exists_isReturningPath_cut_of_arcCut {H : Type} [Fintype H] [DecidableEq H]
    {X X' : TripleData H b} {i : Fin b} {ζ : StrandSide} (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) (hN : 2 ≤ (X.arcCutList i ζ).length) (hX' : X'.IsTripleDiagram)
    (hinv : X'.inv = X.inv)
    (hrot : ∀ d, ¬(X.vertexOf d ∈ X.internalVertices ∧
      ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) → X'.rot d = X.rot d)
    (hc' : X'.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ))
    (hY' : (X'.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift).IsTripleDiagram)
    (hπZ : (X'.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift).strandPerm =
      (X.arcCut i ζ).strandPerm)
    (hret' : ∀ U : List H, (∃ (U₀ : List {d // d ∈ X.arcSideDarts i ζ})
        (j' : Fin ((X.arcCutList i ζ).length / 2)), U = U₀.map Subtype.val ∧
          U₀.map Sum.inl = (X'.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift).arc j') →
      (∀ f ∈ U.head?, f ∈ X.sideList ζ (X.arc i)) →
      (∀ f ∈ U.getLast?, X.inv f ∈ X.sideList ζ (X.arc i)) →
      ∃ a c, X'.IsReturningPath (X.arc i) ζ U a c)
    {U₀ : List {d // d ∈ X.arcSideDarts i ζ}} {jU : Fin ((X.arcCutList i ζ).length / 2)}
    (hU₀ : U₀.map Sum.inl = (X.arcCut i ζ).arc jU) {a' c' : ℕ}
    (hU : X.IsReturningPath (X.arc i) ζ (U₀.map Subtype.val) a' c') :
    ∃ U₂ : List {d // d ∈ X.arcSideDarts i ζ}, U₂.map Sum.inl =
        (X'.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift).arc jU ∧
      X'.IsReturningPath (X.arc i) ζ (U₂.map Subtype.val) a' c' ∧
      (U₂.map Subtype.val).head? = (U₀.map Subtype.val).head? ∧
      (U₂.map Subtype.val).getLast?.map X.inv = (U₀.map Subtype.val).getLast?.map X.inv := by
  obtain ⟨U₁, hU₁, hU₁h, hU₁l⟩ := arcCut_arc_ends hX hS hN jU
  obtain rfl : U₁ = U₀ := List.map_injective_iff.2 Sum.inl_injective (hU₁.trans hU₀.symm)
  obtain ⟨U₂, hU₂, -, hU₂h, hU₂l⟩ := arc_cut_ends hX' hc' hY' jU
  simp only [hinv, hπZ] at hU₂l
  have hh := hU₂h.trans hU₁h.symm
  have hl := hU₂l.trans hU₁l.symm
  obtain ⟨-, hUh, hUl⟩ := (hS.exists_isReturningPath_iff hX ζ hN _).1 ⟨a', c', hU⟩
  obtain ⟨a'', c'', hR⟩ := hret' _ ⟨U₂, jU, rfl, hU₂⟩ (fun f hf => hUh f (by rwa [hh] at hf))
    (fun f hf => by
      have h1 : (U₂.map Subtype.val).getLast?.map X.inv = some (X.inv f) := by
        rw [Option.mem_def.1 hf]
        rfl
      rw [hl] at h1
      obtain ⟨g, hg, hgf⟩ := Option.map_eq_some_iff.1 h1
      rw [← hgf]
      exact hUl g hg)
  have hsideD : ∀ e ∈ (X.arc i).dropLast, X'.sideDarts ζ e = X.sideDarts ζ e := fun e he =>
    sideDarts_eq_of_forall_mem_vertexOf hinv (rot_eq_of_mem_dropLast_arc hX hrot he) ζ
  exact ⟨U₂, hU₂, isReturningPath_of_ends hinv hsideD hU hR hh hl, hh, hl⟩

/-- Given the lift `X'` of a straightening `Y'` of the cut along `S`, with the arc of `Y'` from
`s_j` boundary-parallel along the interval `I` of `Q`, the returning paths of `S` in `X` give
returning paths of `S` in `X'` with the same ends, and the one of `Q` hugs `S`. The cut of `X'` is
taken along a set `K'` and a list `L'` equal to those of `X`. -/
private theorem exists_hugs_aux {H : Type} [Fintype H] [DecidableEq H] {X X' : TripleData H b}
    {i : Fin b} {ζ : StrandSide} (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (hN : 2 ≤ (X.arcCutList i ζ).length) (hX' : X'.IsTripleDiagram) (hinv : X'.inv = X.inv)
    (hrot : ∀ d, ¬(X.vertexOf d ∈ X.internalVertices ∧
      ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) → X'.rot d = X.rot d)
    (harc : X'.arc i = X.arc i) {K' : Finset H} {L' : List H}
    (hK : K' = X.arcSideDarts i ζ) (hL : L' = X.arcCutList i ζ) (hc' : X'.IsCutData K' L')
    (hY' : (X'.cut K' L' ζ.cutShift).IsTripleDiagram)
    (hret' : ∀ U : List H, (∃ (U₀ : List {d // d ∈ K'}) (j' : Fin (L'.length / 2)),
        U = U₀.map Subtype.val ∧ U₀.map Sum.inl = (X'.cut K' L' ζ.cutShift).arc j') →
      (∀ f ∈ U.head?, f ∈ X'.sideList ζ (X'.arc i)) →
      (∀ f ∈ U.getLast?, X'.inv f ∈ X'.sideList ζ (X'.arc i)) →
      ∃ a c, X'.IsReturningPath (X'.arc i) ζ U a c)
    (hhug' : ∀ (Q' : List {d // d ∈ K'}) (j' : Fin (L'.length / 2)),
      Q'.map Sum.inl = (X'.cut K' L' ζ.cutShift).arc j' →
      ∀ a c, X'.IsReturningPath (X'.arc i) ζ (Q'.map Subtype.val) a c →
      ∀ I, (X'.cut K' L' ζ.cutShift).IsBoundaryParallel j' I →
      (∀ r, r ∈ intervalInterior (X'.cut K' L' ζ.cutShift).strandPerm j' I ↔
        ∃ d ∈ X'.hugDarts (X'.arc i) ζ (Q'.map Subtype.val), ∃ hd : d ∈ K',
          (X'.cut K' L' ζ.cutShift).endDart r = .inl ⟨d, hd⟩) →
      X'.Hugs (X'.arc i) ζ (Q'.map Subtype.val) a c)
    {Y' : TripleDiagram ((X.arcCutList i ζ).length / 2)}
    (hiso : (X'.cut K' L' ζ.cutShift).HIsomorphic Y'.data)
    (hπY' : Y'.data.strandPerm = (X.arcCut i ζ).strandPerm)
    {j : Fin ((X.arcCutList i ζ).length / 2)}
    {I : Finset (Fin (2 * ((X.arcCutList i ζ).length / 2)))}
    (hbp : Y'.data.IsBoundaryParallel j I)
    (hImem : ∀ r, r ∈ intervalInterior (X.arcCut i ζ).strandPerm j I ↔
      min (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ)
          (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (targetIndex ((X.arcCut i ζ).strandPerm j))) <
          cutEndIndex (X.arcCutList i ζ) ζ.cutShift r ∧
        (cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ) <
          max (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ)
            (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
              (targetIndex ((X.arcCut i ζ).strandPerm j))))
    {Q₀ : List {d // d ∈ X.arcSideDarts i ζ}} (hQ₀ : Q₀.map Sum.inl = (X.arcCut i ζ).arc j)
    {a c : ℕ} (hQ : X.IsReturningPath (X.arc i) ζ (Q₀.map Subtype.val) a c) :
    (∀ U a' c', X.IsReturningPath (X.arc i) ζ U a' c' →
      ∃ U', X'.IsReturningPath (X.arc i) ζ U' a' c' ∧ U'.head? = U.head? ∧
        U'.getLast?.map X.inv = U.getLast?.map X.inv) ∧
    ∃ Q', X'.Hugs (X.arc i) ζ Q' a c ∧ Q'.head? = (Q₀.map Subtype.val).head? ∧
      Q'.getLast?.map X.inv = (Q₀.map Subtype.val).getLast?.map X.inv := by
  subst hK hL
  have hLnd : (X.arcCutList i ζ).Nodup := (hS.isCutData_arcCutList hX ζ).nodup
  obtain ⟨pre, hLpre⟩ : ∃ pre, X.arcCutList i ζ = pre ++ X.sideList ζ (X.arc i) :=
    ⟨_, arcCutList_eq_append ζ⟩
  obtain ⟨θ⟩ := hIsomorphic_iff_isomorphic.1 hiso
  have hπZ : (X'.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift).strandPerm =
      (X.arcCut i ζ).strandPerm :=
    (θ.strandPerm_eq hY'.toIsPreTripleDiagram Y'.isTripleDiagram.toIsPreTripleDiagram).symm.trans
      hπY'
  have hside := sideList_arc_eq hX hinv hrot ζ
  rw [harc, hside, hinv] at hret'
  rw [harc] at hhug'
  refine ⟨fun U a' c' hU => ?_, ?_⟩
  · obtain ⟨⟨U₀, jU, rfl, hU₀⟩, -, -⟩ := (hS.exists_isReturningPath_iff hX ζ hN U).1 ⟨a', c', hU⟩
    obtain ⟨U₂, -, hR, hh, hl⟩ :=
      exists_isReturningPath_cut_of_arcCut hX hS hN hX' hinv hrot hc' hY' hπZ hret' hU₀ hU
    exact ⟨_, hR, hh, hl⟩
  obtain ⟨-, hQh, hQl⟩ := (hS.exists_isReturningPath_iff hX ζ hN _).1 ⟨a, c, hQ⟩
  obtain ⟨Q₁, hQ₁, hQ₁h, hQ₁l⟩ := arcCut_arc_ends hX hS hN j
  obtain rfl : Q₀ = Q₁ :=
    (List.map_injective_iff.2 Sum.inl_injective (hQ₁.trans hQ₀.symm)).symm
  obtain ⟨g₀, hg₀, hg₀x⟩ := Option.map_eq_some_iff.1 hQ₁l
  have hx₁ : pre.length ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ) :=
    (getElem_mem_iff_of_eq_append hLnd hLpre (Fin.isLt _)).1 (hQh _ (Option.mem_def.2 hQ₁h))
  have hx₂ : pre.length ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
      (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ) := by
    refine (getElem_mem_iff_of_eq_append hLnd hLpre (Fin.isLt _)).1 ?_
    rw [← hg₀x]
    exact hQl _ (Option.mem_def.2 hg₀)
  obtain ⟨Q₂, hQ₂, hR, hh, hl⟩ :=
    exists_isReturningPath_cut_of_arcCut hX hS hN hX' hinv hrot hc' hY' hπZ hret' hQ₀ hQ
  obtain ⟨g, hg, hgx⟩ := Option.map_eq_some_iff.1 (hl.trans hQ₁l)
  have hLpre' : X.arcCutList i ζ = pre ++ X'.sideList ζ (X.arc i) := by rwa [hside]
  have hgx' : X'.inv g = (X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ) ζ.cutShift
      (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ)] := by rwa [hinv]
  refine ⟨_, hhug' Q₂ j hQ₂ a c hR I
    (isBoundaryParallel_of_iso θ hY' Y'.isTripleDiagram hbp) fun r => ?_, hh, hl⟩
  rw [hπZ, hImem r, cut_endDart, hc'.cutListDart_eq, ← getElem_mem_hugDarts_iff hLnd hLpre'
    (Fin.isLt _) (Fin.isLt _) hx₁ hx₂ (hh.trans hQ₁h) hg hgx' (Fin.isLt _)]
  refine ⟨fun h => ⟨_, h, hc'.getElem_mem _, rfl⟩, ?_⟩
  rintro ⟨d, hd, hdK, he⟩
  have hde := congrArg Subtype.val (Sum.inl_injective he)
  simp only at hde
  subst hde
  exact hd

/-! ### Making a minimal returning arc hug -/

/-- If no returning path of `S` has both ends strictly between those of `Q` in the `ζ` list, the
interval of the pair of `Q` read on the cut list is a minimal interval of the cut. -/
private theorem isMinimalInterval_of_cut {H : Type} [Fintype H] [DecidableEq H]
    {X : TripleData H b} {i : Fin b} {ζ : StrandSide} (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) (hN : 2 ≤ (X.arcCutList i ζ).length) {pre : List H}
    (hLpre : X.arcCutList i ζ = pre ++ X.sideList ζ (X.arc i))
    {j : Fin ((X.arcCutList i ζ).length / 2)}
    {I : Finset (Fin (2 * ((X.arcCutList i ζ).length / 2)))}
    (hIint : IsIntervalOf (X.arcCut i ζ).strandPerm j I)
    (hImem : ∀ r, r ∈ intervalInterior (X.arcCut i ζ).strandPerm j I ↔
      min (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ)
          (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (targetIndex ((X.arcCut i ζ).strandPerm j))) <
          cutEndIndex (X.arcCutList i ζ) ζ.cutShift r ∧
        (cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ) <
          max (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ)
            (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
              (targetIndex ((X.arcCut i ζ).strandPerm j))))
    {Q : List H} {g : H}
    (hQh : Q.head? = some (X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ) ζ.cutShift
      (sourceIndex j) : ℕ)])
    (hg : Q.getLast? = some g)
    (hgx : X.inv g = (X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ) ζ.cutShift
      (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ)])
    (hx₁ : pre.length ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ))
    (hx₂ : pre.length ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
      (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ))
    (hmin : ∀ Q' a' c', X.IsReturningPath (X.arc i) ζ Q' a' c' →
      ∀ f ∈ Q.head?, ∀ g ∈ Q.getLast?, ∀ f' ∈ Q'.head?, ∀ g' ∈ Q'.getLast?,
        let L := X.sideList ζ (X.arc i)
        let k := L.idxOf f
        let l := L.idxOf (X.inv g)
        ¬((min k l < L.idxOf f' ∧ L.idxOf f' < max k l) ∧
          (min k l < L.idxOf (X.inv g') ∧ L.idxOf (X.inv g') < max k l))) :
    IsMinimalInterval (X.arcCut i ζ).strandPerm j I := by
  have hLnd : (X.arcCutList i ζ).Nodup := (hS.isCutData_arcCutList hX ζ).nodup
  refine ⟨hIint, fun j' hj' ⟨h1, h2⟩ => ?_⟩
  have hr1 : sourceIndex j' ∈ intervalInterior (X.arcCut i ζ).strandPerm j I := by
    rw [intervalInterior, mem_sdiff, mem_insert, mem_singleton]
    exact ⟨h1, fun h => h.elim (fun h => hj' (sourceIndex_injective h))
      (sourceIndex_ne_targetIndex _ _)⟩
  have hr2 : targetIndex ((X.arcCut i ζ).strandPerm j') ∈
      intervalInterior (X.arcCut i ζ).strandPerm j I := by
    rw [intervalInterior, mem_sdiff, mem_insert, mem_singleton]
    exact ⟨h2, fun h => h.elim (fun h => sourceIndex_ne_targetIndex _ _ h.symm)
      (fun h => hj' (strandPerm_injective'' (hS.isTripleDiagram_arcCut hX ζ hN)
        (targetIndex_injective h)))⟩
  obtain ⟨hm1, hm2⟩ := (hImem _).1 hr1
  obtain ⟨hm3, hm4⟩ := (hImem _).1 hr2
  obtain ⟨Q', hQ', hQ'h, hQ'l⟩ := arcCut_arc_ends hX hS hN j'
  obtain ⟨g', hg', hg'x⟩ := Option.map_eq_some_iff.1 hQ'l
  have hp1 : pre.length ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j') : ℕ) := by
    omega
  have hp2 : pre.length ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
      (targetIndex ((X.arcCut i ζ).strandPerm j')) : ℕ) := by
    omega
  obtain ⟨a', c', hR'⟩ := (hS.exists_isReturningPath_iff hX ζ hN (Q'.map Subtype.val)).2
    ⟨⟨Q', j', rfl, hQ'⟩, fun f hf => by
      rw [hQ'h, Option.mem_def, Option.some_inj] at hf
      rw [← hf]
      exact (getElem_mem_iff_of_eq_append hLnd hLpre (Fin.isLt _)).2 hp1,
     fun f hf => by
      rw [Option.mem_def.1 hf] at hg'
      rw [Option.some_inj.1 hg', hg'x]
      exact (getElem_mem_iff_of_eq_append hLnd hLpre (Fin.isLt _)).2 hp2⟩
  have := hmin _ a' c' hR' _ (Option.mem_def.2 hQh) g hg _ (Option.mem_def.2 hQ'h) g' hg'
  simp only at this
  rw [hgx, hg'x, idxOf_getElem_of_eq_append hLnd hLpre (Fin.isLt _) hx₁,
    idxOf_getElem_of_eq_append hLnd hLpre (Fin.isLt _) hx₂,
    idxOf_getElem_of_eq_append hLnd hLpre (Fin.isLt _) hp1,
    idxOf_getElem_of_eq_append hLnd hLpre (Fin.isLt _) hp2] at this
  omega

/-- **Making a minimal returning arc hug**. Let `S` be the simple arc from `s_i` of a triple
diagram `X`, `ζ` a side with `N_ζ ≥ 2` such that the cut `X|_{S,ζ}` has the straightening property,
and `Q` a returning path of `S` on side `ζ`, from `z_{a+1}` to `z_{c+1}`, such that no returning
path of `S` on side `ζ` has both its first dart and the reverse of its last dart strictly between
those of `Q` in the `ζ` list. Then there is a triple diagram `X' ∼ X` with the darts, involution,
`B`, `ε` and `o` of `X`, whose rotation agrees with that of `X` at every dart not lying at a triple
point of `X` avoided by `S`, whose arc from `s_i` is `S`, such that for every returning path `U` of
`S` on side `ζ` in `X`, from `z_{a'+1}` to `z_{c'+1}`, `S` has in `X'` a returning path on side `ζ`
from `z_{a'+1}` to `z_{c'+1}` with the first dart of `U` and the reverse of the last dart of `U`;
and the one with the ends of `Q` hugs `S`. -/
@[cluster_algebras "lem_returning_arc_hug"]
theorem IsSimpleArc.exists_moveEquivalent_hugs {H : Type} [Fintype H] [DecidableEq H]
    {X : TripleData H b} {i : Fin b} (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) (hN : 2 ≤ (X.arcCutList i ζ).length)
    (hst : TripleDiagram.HasStraighteningProperty
      ⟨_, X.arcCut i ζ, hS.isTripleDiagram_arcCut hX ζ hN⟩)
    {Q : List H} {a c : ℕ} (hQ : X.IsReturningPath (X.arc i) ζ Q a c)
    (hmin : ∀ Q' a' c', X.IsReturningPath (X.arc i) ζ Q' a' c' →
      ∀ f ∈ Q.head?, ∀ g ∈ Q.getLast?, ∀ f' ∈ Q'.head?, ∀ g' ∈ Q'.getLast?,
        let L := X.sideList ζ (X.arc i)
        let k := L.idxOf f
        let l := L.idxOf (X.inv g)
        ¬((min k l < L.idxOf f' ∧ L.idxOf f' < max k l) ∧
          (min k l < L.idxOf (X.inv g') ∧ L.idxOf (X.inv g') < max k l))) :
    ∃ (X' : TripleData H b) (hX' : X'.IsTripleDiagram),
      TripleDiagram.MoveEquivalent ⟨H, X, hX⟩ ⟨H, X', hX'⟩ ∧
      X'.inv = X.inv ∧ X'.bdry = X.bdry ∧ X'.endDart = X.endDart ∧ X'.isOut = X.isOut ∧
      (∀ d, ¬(X.vertexOf d ∈ X.internalVertices ∧
          ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) → X'.rot d = X.rot d) ∧
      X'.IsSimpleArc i ∧ X'.arc i = X.arc i ∧
      (∀ U a' c', X.IsReturningPath (X.arc i) ζ U a' c' →
        ∃ U', X'.IsReturningPath (X.arc i) ζ U' a' c' ∧ U'.head? = U.head? ∧
          U'.getLast?.map X.inv = U.getLast?.map X.inv) ∧
      ∃ Q', X'.Hugs (X.arc i) ζ Q' a c ∧ Q'.head? = Q.head? ∧
        Q'.getLast?.map X.inv = Q.getLast?.map X.inv := by
  have hs : ζ.cutShift ≤ 1 := by cases ζ <;> simp [StrandSide.cutShift]
  have hLnd : (X.arcCutList i ζ).Nodup := (hS.isCutData_arcCutList hX ζ).nodup
  obtain ⟨pre, hLpre⟩ : ∃ pre, X.arcCutList i ζ = pre ++ X.sideList ζ (X.arc i) :=
    ⟨_, arcCutList_eq_append ζ⟩
  obtain ⟨⟨Q₀, j, rfl, hQ₀⟩, hQh, hQl⟩ := (hS.exists_isReturningPath_iff hX ζ hN Q).1 ⟨a, c, hQ⟩
  obtain ⟨Q₁, hQ₁, hQ₁h, hQ₁l⟩ := arcCut_arc_ends hX hS hN j
  obtain rfl : Q₁ = Q₀ := List.map_injective_iff.2 Sum.inl_injective (hQ₁.trans hQ₀.symm)
  obtain ⟨g, hg, hgx⟩ := Option.map_eq_some_iff.1 hQ₁l
  have hx₁ : pre.length ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ) :=
    (getElem_mem_iff_of_eq_append hLnd hLpre (Fin.isLt _)).1 (hQh _ (Option.mem_def.2 hQ₁h))
  have hx₂ : pre.length ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
      (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ) := by
    refine (getElem_mem_iff_of_eq_append hLnd hLpre (Fin.isLt _)).1 ?_
    rw [← hgx]
    exact hQl _ (Option.mem_def.2 hg)
  obtain ⟨I, hIint, hImem⟩ :=
    exists_isIntervalOf_cut hs (even_length_arcCutList ζ) (X.arcCut i ζ).strandPerm j
  obtain ⟨Y', hYY', hbp⟩ :=
    hst.2 j I (isMinimalInterval_of_cut hX hS hN hLpre hIint hImem hQ₁h hg hgx hx₁ hx₂ hmin)
  obtain ⟨X', hX', hXX', hinv, hbdry, hend, hout, hrot, hS', harc, hK, hL, hiso⟩ :=
    hS.exists_moveEquivalent_hIsomorphic_arcCut hX ζ hN hYY'
  have hN' : 2 ≤ (X'.arcCutList i ζ).length := hL ▸ hN
  obtain ⟨h1, h2⟩ := exists_hugs_aux hX hS hN hX' hinv hrot harc hK hL
    (hS'.isCutData_arcCutList hX' ζ) (hS'.isTripleDiagram_arcCut hX' ζ hN')
    (fun U h1 h2 h3 => (hS'.exists_isReturningPath_iff hX' ζ hN' U).2 ⟨h1, h2, h3⟩)
    (fun Q' j' hQ' a c hr I hB hI => hS'.hugs_of_isBoundaryParallel_arcCut hX' hN' hQ' hr hB hI)
    hiso hYY'.strandPerm_eq hbp hImem hQ₀ hQ
  exact ⟨X', hX', hXX', hinv, hbdry, hend, hout, hrot, hS', harc, h1, h2⟩

end ReturningArcHug

end TripleData

end ClusterAlgebras

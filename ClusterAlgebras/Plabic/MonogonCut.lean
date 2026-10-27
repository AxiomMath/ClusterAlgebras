/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.ArcCut
public import ClusterAlgebras.Plabic.Monogon

/-!
# The inside of a convex monogon

Let `M = (e₁, …, e_m)`, `m ≥ 2`, be a convex monogon of a triple diagram `X` with inside `ζ`,
inside darts `H_in(M)` and inside list `(g₀, …, g_{N-1})`, `N = 2(m - 1)`. Its *inside* `X|_M` is
the cut of `X` along `H_in(M)` and the inside list: the darts are `H_in(M)` together with `2N` new
darts `α_k, ᾱ_k`, the rotation is `σ` on the inside darts off the list and closes each `g_k` into
the `3`-cycle `(g_k ᾱ_k α_{k-1})` of a new endpoint. It is a triple diagram with `m - 1` arcs whose
triple points are the triple points of `X` avoided by `M`; swivel moves of the inside lift to
swivel moves of `X` that keep `M` convex with the same inside; and monogons, hollow monogons and
arcs of the inside are monogons, hollow monogons and returning paths of `M` in `X`.

## Main definitions

* `TripleData.monogonCut`: the inside `X|_M` of a convex monogon.

## Main results

* `TripleData.IsConvexMonogon.isTripleDiagram_monogonCut`,
  `TripleData.IsConvexMonogon.internalVertices_monogonCut`,
  `TripleData.IsConvexMonogon.card_internalVertices_monogonCut_le`: the inside is a triple diagram
  whose triple points are triple points of `X` avoided by `M`, at most `T - m` of them.
* `TripleData.IsConvexMonogon.exists_moveEquivalent_monogonCut`: moves of the inside lift.
* `TripleData.IsConvexMonogon.exists_isMonogon_of_isMonogon_monogonCut`,
  `TripleData.IsConvexMonogon.exists_isHollowMonogon_of_isHollowMonogon_monogonCut`,
  `TripleData.IsConvexMonogon.exists_isReturningPath_arc_monogonCut`: monogons, hollow monogons and
  arcs of the inside.

## Implementation notes

* The inside darts `H_in(M)` are defined relative to a winding function `h` of `M`, which is
  unique (`existsUnique_isMonogonWindingFunction`); so is the inside `X.monogonCut P ζ h`.
* The inside is the cut `X.cut (X.insideDarts P ζ h) (X.insideList ζ P) ζ.cutShift` of
  `ClusterAlgebras.TripleData.cut`, exactly as the cut along a simple arc: the endpoint `ε'(r)`
  (labels `0`-indexed, `r : Fin (2 * (N / 2))`) is the cycle of `g_r` (inside right) or of
  `g_{r+1}` (inside left).
* Euler's relation for the inside is proved, as in FWZ, together with the *outside system*
  `O`: the cut of the rotation system of `X` along the darts that are neither inside nor darts of
  `M` or their reverses, and the outside list. Only the rotation system of `O` matters; it is
  obtained as a cut of `X` with its set `B` emptied.
* Moves of the inside are lifted along sequences of swivel moves
  (`TripleDiagram.MoveEquivalent.exists_swivelSteps`); the two insides then have the same number
  of arcs only propositionally, and their isomorphism is stated after transport along that
  equality.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

/-! ### Lists of pairs -/

section ListPairs

omit [Fintype H] [DecidableEq H]

private theorem length_flatMap_pair {α β : Type*} (A : List α) (f g : α → β) :
    (A.flatMap fun a => [f a, g a]).length = 2 * A.length := by
  induction A with
  | nil => simp
  | cons a A ih => simp [List.flatMap_cons, ih]; ring

private theorem getElem_flatMap_pair {α β : Type*} (A : List α) (f g : α → β) (k : ℕ)
    (hk : k < (A.flatMap fun a => [f a, g a]).length) (hk' : k / 2 < A.length) :
    (A.flatMap fun a => [f a, g a])[k] = if k % 2 = 0 then f A[k / 2] else g A[k / 2] := by
  induction A generalizing k with
  | nil => simp at hk'
  | cons a A ih =>
    match k with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem_cons_succ]
      rw [ih k (by simp at hk ⊢; omega) (by simp at hk' ⊢; omega)]
      have h1 : (k + 2) % 2 = k % 2 := by omega
      have h2 : (k + 2) / 2 = k / 2 + 1 := by omega
      simp only [h1, h2, List.getElem_cons_succ]

end ListPairs

/-! ### Local facts on simple monogons -/

section Local

variable {X : TripleData H b}

private theorem val_finRotate' {n : ℕ} (j : Fin n) :
    (finRotate n j : ℕ) = if (j : ℕ) + 1 < n then (j : ℕ) + 1 else 0 := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : j = Fin.last n
    · subst h
      simp
    · have : (j : ℕ) < n := Fin.val_lt_last h
      simp only [h, if_false, show (j : ℕ) + 1 < n + 1 by omega, if_true]

private theorem finRotate_eq_succ' {L : ℕ} (i : Fin L) (hi : (i : ℕ) + 1 < L) :
    finRotate L i = ⟨i + 1, hi⟩ :=
  Fin.ext (by rw [val_finRotate', if_pos hi])

private theorem finRotate_eq_zero' {L : ℕ} (i : Fin L) (hi : ¬(i : ℕ) + 1 < L) :
    finRotate L i = ⟨0, i.pos⟩ :=
  Fin.ext (by rw [val_finRotate', if_neg hi])

private theorem rotPow_inj (hX : X.IsPreTripleDiagram) {d : H}
    (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) {i j : ℕ} (hi : i < 6) (hj : j < 6)
    (h : (X.rot ^ i) d = (X.rot ^ j) d) : i = j :=
  (hX.rot_pow_six hd).2 i j hi hj h

private theorem exists_eq_rotPow (hX : X.IsPreTripleDiagram) {d e : H}
    (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) (he : e ∈ X.vertexOf d) :
    ∃ k < 6, e = (X.rot ^ k) d := by
  obtain ⟨n, hn⟩ := (X.mem_vertexOf.1 he).exists_nat_pow_eq
  exact ⟨n % 6, Nat.mod_lt _ (by norm_num), by rw [← hn, hX.rot_pow_mod_six hd]⟩

private theorem strandStep_getElem' {P : List H} (hP : X.IsStrandPath P) {l : ℕ}
    (hl : l + 1 < P.length) : X.StrandStep P[l] P[l + 1] :=
  List.isChain_iff_getElem.1 hP.isChain l hl

/-- The vertex of a monogon: its last dart returns to `v(e₁)`, a triple point. -/
private theorem vertexOf_inv_last' {P : List H} (hP : X.IsMonogon P) (h0 : 0 < P.length) :
    X.vertexOf (X.inv P[P.length - 1]) = X.vertexOf P[0] ∧
      ¬X.IsBoundaryVertex (X.vertexOf P[0]) := by
  have hne := hP.isStrandPath.ne_nil
  have h1 := hP.pathEnd_eq
  rw [X.pathEnd_of_getLast? (List.getLast?_eq_some_getLast hne),
    X.pathStart_of_head? (List.head?_eq_some_head hne), List.getLast_eq_getElem,
    List.head_eq_getElem] at h1
  have h2 := hP.pathStart_mem
  rw [X.pathStart_of_head? (List.head?_eq_some_head hne), List.head_eq_getElem] at h2
  exact ⟨h1, X.vertexOf_mem_internalVertices.1 h2⟩

private theorem vertexOf_getElem_inj' {P : List H} (hw : X.IsSimpleClosedWalk P.get) {i j : ℕ}
    (hi : i < P.length) (hj : j < P.length) (h : X.vertexOf P[i] = X.vertexOf P[j]) : i = j :=
  congrArg Fin.val (hw.injective_vertexOf (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h)

private theorem eq_of_vertexOf_eq_finRotate' {L : ℕ} {w : Fin L → H}
    (hw : X.IsSimpleClosedWalk w) (i : Fin L) {d : H}
    (hd : X.vertexOf d = X.vertexOf (w (finRotate L i))) :
    (∀ j, d = w j → d = w (finRotate L i)) ∧ ∀ j, d = X.inv (w j) → d = X.inv (w i) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [hj, hw.eq_of_vertexOf_eq (i := i) (j := j) (by rw [← hj, hd])]
  · rw [hj, hw.eq_of_vertexOf_inv_eq (i := i) (j := j) (by rw [← hj, hd])]

/-- The exponent `t` with `e₁ = σ^t(ē_m)` at the corner of a monogon with inside `ζ`. -/
private def cornerExp' : StrandSide → ℕ
  | .right => 1
  | .left => 5

private theorem getElem_zero_eq_rotPow (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (h0 : 0 < P.length) {ζ : StrandSide}
    (hc : X.IsInsideCorner ζ P[0] P[P.length - 1]) :
    P[0] = (X.rot ^ cornerExp' ζ) (X.inv P[P.length - 1]) := by
  cases ζ with
  | right =>
    simp only [cornerExp', pow_one]
    exact hc.symm
  | left =>
    simp only [cornerExp']
    have hx := (vertexOf_inv_last' hP h0).2
    change X.rot P[0] = X.inv P[P.length - 1] at hc
    rw [← hc, ← Equiv.Perm.mul_apply, ← pow_succ]
    exact (hX.rot_pow_six_apply hx).symm

/-- The darts at an interior point `z_l = v(ē_l)` of a simple monogon: `σ^k ē_l` is a dart of
the monogon only for `k = 3` and the reverse of one only for `k = 0`. -/
private theorem rotPow_inv_getElem_mem (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {l : ℕ} (hl : l + 1 < P.length) {k : ℕ}
    (hk : k < 6) :
    ((X.rot ^ k) (X.inv P[l]) ∈ P ↔ k = 3) ∧ (X.inv ((X.rot ^ k) (X.inv P[l])) ∈ P ↔ k = 0) := by
  have hw := hP.isSimpleClosedWalk hX hs
  have hstep := strandStep_getElem' hP.isStrandPath hl
  have htrip : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[l])) := hstep.1
  have hv : X.vertexOf ((X.rot ^ k) (X.inv P[l])) =
      X.vertexOf (P.get (finRotate P.length ⟨l, by omega⟩)) := by
    rw [X.vertexOf_rot_pow_apply, finRotate_eq_succ' _ hl]
    exact hstep.vertexOf_eq.symm
  obtain ⟨hA, hB⟩ := eq_of_vertexOf_eq_finRotate' hw ⟨l, by omega⟩ hv
  rw [finRotate_eq_succ' _ hl] at hA
  refine ⟨⟨fun hd => ?_, fun hk3 => ?_⟩, ⟨fun hd => ?_, fun hk0 => ?_⟩⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_get.1 hd
    exact rotPow_inj hX htrip hk (by norm_num) ((hA j hj.symm).trans hstep.2)
  · rw [hk3, ← hstep.2]
    exact List.getElem_mem _
  · obtain ⟨j, hj⟩ := List.mem_iff_get.1 hd
    have := hB j (by rw [hj, hX.inv_inv_apply])
    exact rotPow_inj hX htrip hk (by norm_num) (by rw [this, pow_zero, Equiv.Perm.one_apply]; rfl)
  · rw [hk0, pow_zero, Equiv.Perm.one_apply, hX.inv_inv_apply]
    exact List.getElem_mem _

/-- The darts at the vertex `x` of a simple monogon with corner condition `ζ`: `σ^k ē_m` is a
dart of the monogon only for `k = t` (`e₁ = σ^t ē_m`) and the reverse of one only for `k = 0`. -/
private theorem rotPow_inv_last_mem (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) (h0 : 0 < P.length) {ζ : StrandSide}
    (hc : X.IsInsideCorner ζ P[0] P[P.length - 1]) {k : ℕ} (hk : k < 6) :
    ((X.rot ^ k) (X.inv P[P.length - 1]) ∈ P ↔ k = cornerExp' ζ) ∧
      (X.inv ((X.rot ^ k) (X.inv P[P.length - 1])) ∈ P ↔ k = 0) := by
  have hw := hP.isSimpleClosedWalk hX hs
  have hx := vertexOf_inv_last' hP h0
  have htrip : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[P.length - 1])) := by
    rw [hx.1]
    exact hx.2
  have hlast : ¬(P.length - 1 + 1 < P.length) := by omega
  have hv : X.vertexOf ((X.rot ^ k) (X.inv P[P.length - 1])) =
      X.vertexOf (P.get (finRotate P.length ⟨P.length - 1, by omega⟩)) := by
    rw [X.vertexOf_rot_pow_apply, finRotate_eq_zero' _ hlast]
    exact hx.1
  have he1 := getElem_zero_eq_rotPow hX hP h0 hc
  obtain ⟨hA, hB⟩ := eq_of_vertexOf_eq_finRotate' hw ⟨P.length - 1, by omega⟩ hv
  rw [finRotate_eq_zero' _ hlast] at hA
  have hct : cornerExp' ζ < 6 := by cases ζ <;> decide
  refine ⟨⟨fun hd => ?_, fun hkt => ?_⟩, ⟨fun hd => ?_, fun hk0 => ?_⟩⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_get.1 hd
    exact rotPow_inj hX htrip hk hct ((hA j hj.symm).trans he1)
  · rw [hkt, ← he1]
    exact List.getElem_mem _
  · obtain ⟨j, hj⟩ := List.mem_iff_get.1 hd
    have := hB j (by rw [hj, hX.inv_inv_apply])
    exact rotPow_inj hX htrip hk (by norm_num) (by rw [this, pow_zero, Equiv.Perm.one_apply]; rfl)
  · rw [hk0, pow_zero, Equiv.Perm.one_apply, hX.inv_inv_apply]
    exact List.getElem_mem _

/-- Every dart at a vertex of a monogon is `σ^k ē_l` for an interior point `z_l` or `σ^k ē_m`. -/
private theorem exists_of_vertexOf_eq (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) {d e : H} (he : e ∈ P) (hd : X.vertexOf d = X.vertexOf e) :
    (∃ l, ∃ hl : l + 1 < P.length, ∃ k < 6, d = (X.rot ^ k) (X.inv P[l])) ∨
      ∃ h0 : 0 < P.length, ∃ k < 6, d = (X.rot ^ k) (X.inv (P[P.length - 1]'(by omega))) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  rcases j with _ | j
  · have hx := vertexOf_inv_last' hP hj
    have htrip : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[P.length - 1])) := by
      rw [hx.1]
      exact hx.2
    obtain ⟨k, hk, rfl⟩ := exists_eq_rotPow hX htrip
      (by rw [hx.1, ← hd]; exact X.self_mem_vertexOf d)
    exact Or.inr ⟨hj, k, hk, rfl⟩
  · have hstep := strandStep_getElem' hP.isStrandPath hj
    obtain ⟨k, hk, rfl⟩ := exists_eq_rotPow hX hstep.1
      (by rw [← hstep.vertexOf_eq, ← hd]; exact X.self_mem_vertexOf d)
    exact Or.inl ⟨j, hj, k, hk, rfl⟩

end Local

/-! ### Side lists of a monogon -/

section SideLists

variable {X : TripleData H b}

omit [Fintype H] [DecidableEq H] in
private theorem length_sideList (ζ : StrandSide) (P : List H) :
    (X.sideList ζ P).length = 2 * (P.length - 1) := by
  cases ζ
  · change (P.dropLast.flatMap fun e => [X.rot (X.inv e), (X.rot ^ 2) (X.inv e)]).length = _
    rw [length_flatMap_pair, List.length_dropLast]
  · change (P.dropLast.reverse.flatMap
      fun e => [(X.rot ^ 4) (X.inv e), (X.rot ^ 5) (X.inv e)]).length = _
    rw [length_flatMap_pair, List.length_reverse, List.length_dropLast]

omit [Fintype H] [DecidableEq H] in
private theorem getElem_sideList_right {P : List H} {k : ℕ}
    (hk : k < (X.sideList .right P).length) :
    (X.sideList .right P)[k] =
      (X.rot ^ (k % 2 + 1)) (X.inv (P[k / 2]'(by rw [length_sideList] at hk; omega))) := by
  have hk' := hk
  rw [length_sideList] at hk'
  change (P.dropLast.flatMap fun e => [X.rot (X.inv e), (X.rot ^ 2) (X.inv e)])[k] = _
  rw [getElem_flatMap_pair _ _ _ _ _ (by rw [List.length_dropLast]; omega), List.getElem_dropLast]
  split_ifs with h
  · rw [h, zero_add, pow_one]
  · rw [show k % 2 + 1 = 2 by omega]

omit [Fintype H] [DecidableEq H] in
private theorem getElem_sideList_left {P : List H} {k : ℕ}
    (hk : k < (X.sideList .left P).length) :
    (X.sideList .left P)[k] =
      (X.rot ^ (k % 2 + 4)) (X.inv (P[P.length - 2 - k / 2]'(by
        rw [length_sideList] at hk; omega))) := by
  have hk' := hk
  rw [length_sideList] at hk'
  change (P.dropLast.reverse.flatMap
    fun e => [(X.rot ^ 4) (X.inv e), (X.rot ^ 5) (X.inv e)])[k] = _
  rw [getElem_flatMap_pair _ _ _ _ _ (by rw [List.length_reverse, List.length_dropLast]; omega),
    List.getElem_reverse, List.getElem_dropLast]
  have e : P.dropLast.length - 1 - k / 2 = P.length - 2 - k / 2 := by
    rw [List.length_dropLast]; omega
  simp only [e]
  split_ifs with h
  · rw [h]
  · rw [show k % 2 + 4 = 5 by omega]

omit [Fintype H] [DecidableEq H] in
/-- The `ζ` list of a strand path: its darts are the `ζ` darts at the interior points. -/
private theorem getElem_sideList (ζ : StrandSide) {P : List H} {k : ℕ}
    (hk : k < (X.sideList ζ P).length) :
    ∃ l, ∃ hl : l + 1 < P.length, (X.sideList ζ P)[k] ∈ X.sideDarts ζ P[l] := by
  have hk' := hk
  rw [length_sideList] at hk'
  cases ζ
  · refine ⟨k / 2, by omega, ?_⟩
    rw [getElem_sideList_right]
    simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h]
    · exact Or.inl (by rw [zero_add, pow_one])
    · exact Or.inr rfl
  · refine ⟨P.length - 2 - k / 2, by omega, ?_⟩
    rw [getElem_sideList_left]
    simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The darts of the `ζ` list of a strand path lie at its interior points. -/
private theorem vertexOf_of_mem_sideList {P : List H} (hP : X.IsStrandPath P) {ζ : StrandSide}
    {d : H} (hd : d ∈ X.sideList ζ P) :
    ∃ l, ∃ hl : l + 1 < P.length, X.vertexOf d = X.vertexOf (X.inv P[l]) ∧
      X.vertexOf d = X.vertexOf P[l + 1] := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨l, hl, hm⟩ := getElem_sideList ζ hk
  have hv : X.vertexOf (X.sideList ζ P)[k] = X.vertexOf (X.inv P[l]) := by
    cases ζ <;>
    · simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h <;> rw [h]
      · first
        | exact X.vertexOf_rot _
        | exact X.vertexOf_rot_pow_apply _ _
      · exact X.vertexOf_rot_pow_apply _ _
  exact ⟨l, hl, hv, hv.trans (strandStep_getElem' hP hl).vertexOf_eq.symm⟩

/-- The `ζ` list of a simple monogon has no repetition. -/
private theorem nodup_sideList (hX : X.IsPreTripleDiagram) {P : List H} (hP : X.IsMonogon P)
    (hs : X.IsSimpleStrandPath P) (ζ : StrandSide) : (X.sideList ζ P).Nodup := by
  have hw := hP.isSimpleClosedWalk hX hs
  rw [List.nodup_iff_injective_get]
  intro i j hij
  simp only [List.get_eq_getElem] at hij
  have hlen := length_sideList (X := X) ζ P
  have hi : (i : ℕ) < 2 * (P.length - 1) := by have := i.isLt; omega
  have hj : (j : ℕ) < 2 * (P.length - 1) := by have := j.isLt; omega
  apply Fin.ext
  cases ζ
  · rw [getElem_sideList_right, getElem_sideList_right] at hij
    have hli : (i : ℕ) / 2 + 1 < P.length := by omega
    have hlj : (j : ℕ) / 2 + 1 < P.length := by omega
    have hv := congrArg X.vertexOf hij
    rw [X.vertexOf_rot_pow_apply, X.vertexOf_rot_pow_apply,
      ← (strandStep_getElem' hP.isStrandPath hli).vertexOf_eq,
      ← (strandStep_getElem' hP.isStrandPath hlj).vertexOf_eq] at hv
    have hl := vertexOf_getElem_inj' hw (by omega) (by omega) hv
    have hl' : (i : ℕ) / 2 = (j : ℕ) / 2 := by omega
    simp only [hl'] at hij
    have := rotPow_inj hX (strandStep_getElem' hP.isStrandPath hlj).1 (by omega) (by omega) hij
    omega
  · rw [getElem_sideList_left, getElem_sideList_left] at hij
    have hli : P.length - 2 - (i : ℕ) / 2 + 1 < P.length := by omega
    have hlj : P.length - 2 - (j : ℕ) / 2 + 1 < P.length := by omega
    have hv := congrArg X.vertexOf hij
    rw [X.vertexOf_rot_pow_apply, X.vertexOf_rot_pow_apply,
      ← (strandStep_getElem' hP.isStrandPath hli).vertexOf_eq,
      ← (strandStep_getElem' hP.isStrandPath hlj).vertexOf_eq] at hv
    have hl := vertexOf_getElem_inj' hw (by omega) (by omega) hv
    have hl' : (i : ℕ) / 2 = (j : ℕ) / 2 := by omega
    simp only [hl'] at hij
    have := rotPow_inj hX (strandStep_getElem' hP.isStrandPath hlj).1 (by omega) (by omega) hij
    omega

end SideLists

/-! ### The inside of a convex monogon -/

/-- **The inside of a convex monogon**. Let `M` be a convex monogon of `X` with inside `ζ`,
inside darts `H_in(M)` (relative to the winding function `h`) and inside list `(g₀, …, g_{N-1})`.
Its inside `X|_M` has the darts `H_in(M) ⊔ {α_k, ᾱ_k : k ∈ ℤ/N}`; its involution is that of `X`
on the inside darts and exchanges `α_k` and `ᾱ_k`; its rotation is `σ` on the inside darts
outside the list and consists of the `3`-cycles `(g_k ᾱ_k α_{k-1})` on the remaining darts;
`B' = {α_k, ᾱ_k}`; `o' = o`; and, for `r : Fin (2 * (N / 2))`, `ε'(r)` is the cycle of `g_r`
(inside right) or of `g_{r+1}` (inside left). It has `N / 2` arcs. -/
@[cluster_algebras "def_monogon_cut"]
noncomputable def monogonCut (X : TripleData H b) (P : List H) (ζ : StrandSide)
    (h : X.faceOrbits → ℤ) :
    TripleData (CutDart (X.insideDarts P ζ h) (X.insideList ζ P).length)
      ((X.insideList ζ P).length / 2) :=
  X.cut (X.insideDarts P ζ h) (X.insideList ζ P) ζ.cutShift

section Inside

variable {X : TripleData H b} {P : List H} {ζ : StrandSide} {h : X.faceOrbits → ℤ}

omit [Fintype H] [DecidableEq H] in
/-- The inside list of a monogon `(e₁, …, e_m)` has `N = 2(m - 1)` darts. -/
theorem length_insideList (ζ : StrandSide) (P : List H) :
    (X.insideList ζ P).length = 2 * (P.length - 1) :=
  length_sideList ζ P

/-- The darts of the inside list are inside. -/
theorem IsConvexMonogon.mem_insideDarts_of_mem_insideList (hX : X.IsTripleDiagram)
    (hM : X.IsConvexMonogon P ζ) (hh : X.IsMonogonWindingFunction P h) {d : H}
    (hd : d ∈ X.insideList ζ P) : d ∈ X.insideDarts P ζ h := by
  have := X.subset_avoidingClosure P {d | d ∈ X.insideList ζ P} hd
  rw [← hM.insideDarts_eq_avoidingClosure hX hh] at this
  exact_mod_cast this

/-- An inside dart outside the inside list lies at a triple point avoided by `M`. -/
theorem IsConvexMonogon.avoids_of_mem_insideDarts (hX : X.IsTripleDiagram)
    (hM : X.IsConvexMonogon P ζ) (hh : X.IsMonogonWindingFunction P h) {d : H}
    (hd : d ∈ X.insideDarts P ζ h) (hL : d ∉ X.insideList ζ P) :
    ¬X.IsBoundaryVertex (X.vertexOf d) ∧ ∀ e ∈ P, X.vertexOf d ≠ X.vertexOf e :=
  ⟨fun hb => hM.notMem_insideDarts_of_isBoundaryVertex hX hh hb hd,
    fun e he hv => hL ((hM.mem_insideDarts_iff_mem_insideList hX hh ⟨e, he, hv⟩).1 hd)⟩

/-- The darts of the inside list lie at the vertices of `M`. -/
theorem exists_vertexOf_eq_of_mem_insideList (hP : X.IsStrandPath P) {d : H}
    (hd : d ∈ X.insideList ζ P) : ∃ e ∈ P, X.vertexOf d = X.vertexOf e := by
  obtain ⟨l, hl, -, hv⟩ := vertexOf_of_mem_sideList hP hd
  exact ⟨_, List.getElem_mem hl, hv⟩

/-- The inside darts and the inside list of a convex monogon satisfy the hypotheses of the cut. -/
theorem IsConvexMonogon.isCutData_insideDarts (hX : X.IsTripleDiagram) (hM : X.IsConvexMonogon P ζ)
    (hh : X.IsMonogonWindingFunction P h) :
    X.IsCutData (X.insideDarts P ζ h) (X.insideList ζ P) where
  nodup := nodup_sideList hX.toIsPreTripleDiagram hM.isMonogon hM.isSimpleStrandPath ζ
  mem_of_mem_list _ hd := hM.mem_insideDarts_of_mem_insideList hX hh hd
  inv_mem d hd := (inv_mem_insideDarts_iff hX.toIsPreTripleDiagram hh hM.length_pos d).2 hd
  notMem_bdry d hd := ((mem_insideDarts hM.length_pos).1 hd).1
  not_isBoundaryVertex d hd hL := (hM.avoids_of_mem_insideDarts hX hh hd hL).1
  mem_of_mem_vertexOf d hd hL e he := by
    obtain ⟨hb, havoid⟩ := hM.avoids_of_mem_insideDarts hX hh hd hL
    refine ⟨(mem_insideDarts_iff_of_forall_ne hX hM.isMonogon hh hb havoid he).2 hd,
      fun heL => ?_⟩
    obtain ⟨e', he', hv⟩ := exists_vertexOf_eq_of_mem_insideList hM.isMonogon.isStrandPath heL
    exact havoid e' he' ((X.vertexOf_eq_of_mem he).symm.trans hv)

end Inside

/-! ### Darts at the vertices of a convex monogon -/

section Classify

variable {X : TripleData H b} {P : List H} {ζ : StrandSide} {h : X.faceOrbits → ℤ}

omit [Fintype H] [DecidableEq H] in
private theorem getElem_sideList_right_two_mul {l : ℕ} (hl : l + 1 < P.length) :
    (X.sideList .right P)[2 * l]'(by rw [length_sideList]; omega) = X.rot (X.inv P[l]) := by
  rw [getElem_sideList_right]
  simp only [show 2 * l % 2 = 0 by omega, show 2 * l / 2 = l by omega, zero_add, pow_one]

omit [Fintype H] [DecidableEq H] in
private theorem getElem_sideList_right_two_mul_add_one {l : ℕ} (hl : l + 1 < P.length) :
    (X.sideList .right P)[2 * l + 1]'(by rw [length_sideList]; omega) =
      (X.rot ^ 2) (X.inv P[l]) := by
  rw [getElem_sideList_right]
  simp only [show (2 * l + 1) % 2 = 1 by omega, show (2 * l + 1) / 2 = l by omega,
    Nat.reduceAdd]

omit [Fintype H] [DecidableEq H] in
private theorem getElem_sideList_left_two_mul {l : ℕ} (hl : l + 1 < P.length) :
    (X.sideList .left P)[2 * (P.length - 2 - l)]'(by rw [length_sideList]; omega) =
      (X.rot ^ 4) (X.inv P[l]) := by
  rw [getElem_sideList_left]
  simp only [show 2 * (P.length - 2 - l) % 2 = 0 by omega,
    show P.length - 2 - 2 * (P.length - 2 - l) / 2 = l by omega, zero_add]

omit [Fintype H] [DecidableEq H] in
private theorem getElem_sideList_left_two_mul_add_one {l : ℕ} (hl : l + 1 < P.length) :
    (X.sideList .left P)[2 * (P.length - 2 - l) + 1]'(by rw [length_sideList]; omega) =
      (X.rot ^ 5) (X.inv P[l]) := by
  rw [getElem_sideList_left]
  simp only [show (2 * (P.length - 2 - l) + 1) % 2 = 1 by omega,
    show P.length - 2 - (2 * (P.length - 2 - l) + 1) / 2 = l by omega, Nat.reduceAdd]

/-- The corner darts `σ^{o+1} c, …, σ^{o+4} c`. -/
private def cornerList (X : TripleData H b) (o : ℕ) (c : H) : List H :=
  (List.range 4).map fun q => (X.rot ^ (q + o + 1)) c

/-- The outside list of a monogon with inside `ζ` and `c = ē_m`: the list of the other side
followed by the four darts of the vertex `x` other than `e₁` and `ē_m`. -/
private def outsideList (X : TripleData H b) (ζ : StrandSide) (P : List H) (c : H) : List H :=
  match ζ with
  | .right => X.sideList .left P ++ cornerList X 1 c
  | .left => X.sideList .right P ++ cornerList X 0 c

/-- The darts of the outside system: neither inside nor darts of `M` or their reverses. -/
private def outsideDarts (X : TripleData H b) (K : Finset H) (P : List H) : Finset H :=
  univ.filter fun d => d ∉ K ∧ d ∉ P ∧ X.inv d ∉ P

private theorem mem_outsideDarts {K : Finset H} {d : H} :
    d ∈ outsideDarts X K P ↔ d ∉ K ∧ d ∉ P ∧ X.inv d ∉ P := by
  simp [outsideDarts]

omit [Fintype H] [DecidableEq H] in
private theorem mem_cornerList {o : ℕ} {c d : H} :
    d ∈ cornerList X o c ↔ ∃ q < 4, d = (X.rot ^ (q + o + 1)) c := by
  simp only [cornerList, List.mem_map, List.mem_range]
  exact ⟨fun ⟨q, hq, e⟩ => ⟨q, hq, e.symm⟩, fun ⟨q, hq, e⟩ => ⟨q, hq, e.symm⟩⟩

omit [Fintype H] [DecidableEq H] in
private theorem length_cornerList (o : ℕ) (c : H) : (cornerList X o c).length = 4 := by
  simp [cornerList]

omit [Fintype H] [DecidableEq H] in
private theorem getElem_cornerList {o : ℕ} {c : H} {q : ℕ} (hq : q < (cornerList X o c).length) :
    (cornerList X o c)[q] = (X.rot ^ (q + o + 1)) c := by
  simp [cornerList]

omit [Fintype H] [DecidableEq H] in
private theorem length_outsideList (ζ : StrandSide) (P : List H) (c : H) :
    (outsideList X ζ P c).length = 2 * (P.length - 1) + 4 := by
  cases ζ <;> simp [outsideList, length_sideList, length_cornerList]

private theorem rotPow_eq_rotPow_iff (hX : X.IsPreTripleDiagram) {d : H}
    (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    (X.rot ^ i) d = (X.rot ^ j) d ↔ i = j :=
  ⟨rotPow_inj hX hd hi hj, fun e => e ▸ rfl⟩

omit [Fintype H] [DecidableEq H] in
/-- At an interior point `z_l`, a dart `σ^k ē_l` other than `ē_l` and `e_{l+1}` is in the right
list (`k ∈ {1, 2}`) or in the left list (`k ∈ {4, 5}`). -/
private theorem rotPow_mem_sideList {l : ℕ} (hl : l + 1 < P.length) {k : ℕ} (hk : k < 6)
    (h0 : k ≠ 0) (h3 : k ≠ 3) :
    (X.rot ^ k) (X.inv P[l]) ∈ X.sideList .right P ∧ (k = 1 ∨ k = 2) ∨
      (X.rot ^ k) (X.inv P[l]) ∈ X.sideList .left P ∧ (k = 4 ∨ k = 5) := by
  interval_cases k
  · exact absurd rfl h0
  · refine Or.inl ⟨?_, Or.inl rfl⟩
    rw [pow_one, ← getElem_sideList_right_two_mul hl]
    exact List.getElem_mem _
  · refine Or.inl ⟨?_, Or.inr rfl⟩
    rw [← getElem_sideList_right_two_mul_add_one hl]
    exact List.getElem_mem _
  · exact absurd rfl h3
  · refine Or.inr ⟨?_, Or.inl rfl⟩
    rw [← getElem_sideList_left_two_mul hl]
    exact List.getElem_mem _
  · refine Or.inr ⟨?_, Or.inr rfl⟩
    rw [← getElem_sideList_left_two_mul_add_one hl]
    exact List.getElem_mem _

omit [Fintype H] [DecidableEq H] in
/-- The darts of the side lists are `σ^k ē_l` with `k ∈ {1, 2}` (right) or `k ∈ {4, 5}` (left). -/
private theorem exists_of_mem_sideList {ζ' : StrandSide} {d : H} (hd : d ∈ X.sideList ζ' P) :
    ∃ l, ∃ hl : l + 1 < P.length, ∃ k, d = (X.rot ^ k) (X.inv P[l]) ∧
      ((ζ' = .right ∧ (k = 1 ∨ k = 2)) ∨ (ζ' = .left ∧ (k = 4 ∨ k = 5))) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  have hlen := length_sideList (X := X) ζ' P
  cases ζ'
  · refine ⟨i / 2, by omega, i % 2 + 1, getElem_sideList_right hi, Or.inl ⟨rfl, by omega⟩⟩
  · refine ⟨P.length - 2 - i / 2, by omega, i % 2 + 4, getElem_sideList_left hi,
      Or.inr ⟨rfl, by omega⟩⟩

omit [Fintype H] [DecidableEq H] in
private theorem mem_insideList_or_outsideList {ζ' : StrandSide} {c d : H}
    (hd : d ∈ X.sideList ζ' P) : d ∈ X.insideList ζ P ∨ d ∈ outsideList X ζ P c := by
  cases ζ <;> cases ζ' <;> simp only [insideList, outsideList, List.mem_append] <;> tauto

variable (hX : X.IsTripleDiagram) (hM : X.IsConvexMonogon P ζ)

include hX hM

/-- A dart `σ^k ē_l` at an interior point is inside exactly when it is a `ζ` dart. -/
private theorem rotPow_mem_insideDarts_iff {l : ℕ} (hl : l + 1 < P.length) {k : ℕ} (hk : k < 6)
    (hh : X.IsMonogonWindingFunction P h) :
    (X.rot ^ k) (X.inv P[l]) ∈ X.insideDarts P ζ h ↔
      (ζ = .right ∧ (k = 1 ∨ k = 2)) ∨ (ζ = .left ∧ (k = 4 ∨ k = 5)) := by
  have hpre := hX.toIsPreTripleDiagram
  have htrip : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[l])) :=
    (strandStep_getElem' hM.isMonogon.isStrandPath hl).1
  rw [hM.mem_insideDarts_iff_mem_sideDarts hX hh hl
    (RotationSystem.rot_pow_apply_mem_vertexOf _ k _)]
  cases ζ
  · simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false]
    rw [show X.rot (X.inv P[l]) = (X.rot ^ 1) (X.inv P[l]) by rw [pow_one],
      rotPow_eq_rotPow_iff hpre htrip hk (by norm_num),
      rotPow_eq_rotPow_iff hpre htrip hk (by norm_num)]
    simp
  · simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false]
    rw [rotPow_eq_rotPow_iff hpre htrip hk (by norm_num),
      rotPow_eq_rotPow_iff hpre htrip hk (by norm_num)]
    simp

/-- No dart of the vertex `x` of `M` is inside. -/
private theorem rotPow_inv_last_notMem_insideDarts (hh : X.IsMonogonWindingFunction P h) (k : ℕ) :
    (X.rot ^ k) (X.inv (P[P.length - 1]'(by have := hM.length_pos; omega))) ∉
      X.insideDarts P ζ h := by
  apply hM.notMem_insideDarts_of_mem_pathStart hX hh
  rw [X.pathStart_of_head? (List.head?_eq_some_head hM.isMonogon.isStrandPath.ne_nil),
    List.head_eq_getElem, ← (vertexOf_inv_last' hM.isMonogon hM.length_pos).1]
  exact RotationSystem.rot_pow_apply_mem_vertexOf _ k _

/-- Every dart at a vertex of `M` is a dart of `M`, the reverse of one, a dart of the inside list
or a dart of the outside list. -/
private theorem mem_or_of_vertexOf_eq {d e : H} (he : e ∈ P)
    (hd : X.vertexOf d = X.vertexOf e) :
    d ∈ P ∨ X.inv d ∈ P ∨ d ∈ X.insideList ζ P ∨
      d ∈ outsideList X ζ P (X.inv (P[P.length - 1]'(by have := hM.length_pos; omega))) := by
  have hpre := hX.toIsPreTripleDiagram
  rcases exists_of_vertexOf_eq hpre hM.isMonogon he hd with ⟨l, hl, k, hk, rfl⟩ |
    ⟨h0, k, hk, rfl⟩
  · obtain ⟨h1, h2⟩ := rotPow_inv_getElem_mem hpre hM.isMonogon hM.isSimpleStrandPath hl hk
    by_cases hk0 : k = 0
    · exact Or.inr (Or.inl (h2.2 hk0))
    by_cases hk3 : k = 3
    · exact Or.inl (h1.2 hk3)
    refine Or.inr (Or.inr ?_)
    rcases rotPow_mem_sideList hl hk hk0 hk3 with ⟨hm, -⟩ | ⟨hm, -⟩ <;>
      exact mem_insideList_or_outsideList hm
  · have hc := hM.isInsideCorner_getElem
    obtain ⟨h1, h2⟩ := rotPow_inv_last_mem hpre hM.isMonogon hM.isSimpleStrandPath h0 hc hk
    by_cases hk0 : k = 0
    · exact Or.inr (Or.inl (h2.2 hk0))
    by_cases hkt : k = cornerExp' ζ
    · exact Or.inl (h1.2 hkt)
    refine Or.inr (Or.inr (Or.inr ?_))
    cases ζ
    · simp only [cornerExp'] at hkt
      simp only [outsideList, List.mem_append, mem_cornerList]
      exact Or.inr ⟨k - 2, by omega, by rw [show k - 2 + 1 + 1 = k by omega]⟩
    · simp only [cornerExp'] at hkt
      simp only [outsideList, List.mem_append, mem_cornerList]
      exact Or.inr ⟨k - 1, by omega, by rw [show k - 1 + 0 + 1 = k by omega]⟩

/-- The darts of the outside list are neither inside nor darts of `M` or their reverses. -/
private theorem notMem_of_mem_outsideList (hh : X.IsMonogonWindingFunction P h) {d : H}
    (hd : d ∈ outsideList X ζ P (X.inv (P[P.length - 1]'(by have := hM.length_pos; omega)))) :
    d ∉ X.insideDarts P ζ h ∧ d ∉ P ∧ X.inv d ∉ P := by
  have hpre := hX.toIsPreTripleDiagram
  have h0 := hM.length_pos
  have hside : ∀ ζ', ζ' ≠ ζ → d ∈ X.sideList ζ' P →
      d ∉ X.insideDarts P ζ h ∧ d ∉ P ∧ X.inv d ∉ P := by
    intro ζ' hζ' hd'
    obtain ⟨l, hl, k, rfl, hk⟩ := exists_of_mem_sideList hd'
    have hk6 : k < 6 := by omega
    obtain ⟨h1, h2⟩ := rotPow_inv_getElem_mem hpre hM.isMonogon hM.isSimpleStrandPath hl hk6
    refine ⟨fun hK => ?_, fun hP => by have := h1.1 hP; omega,
      fun hP => by have := h2.1 hP; omega⟩
    rw [rotPow_mem_insideDarts_iff hX hM hl hk6 hh] at hK
    rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ <;> rcases hK with ⟨rfl, hK⟩ | ⟨rfl, hK⟩ <;>
      first | exact hζ' rfl | omega
  have hcorner : ∀ q < 4, ∀ o, (o = 1 ∧ ζ = .right ∨ o = 0 ∧ ζ = .left) →
      d = (X.rot ^ (q + o + 1)) (X.inv (P[P.length - 1]'(by omega))) →
      d ∉ X.insideDarts P ζ h ∧ d ∉ P ∧ X.inv d ∉ P := by
    intro q hq o ho hd'
    have hc := hM.isInsideCorner_getElem
    obtain ⟨h1, h2⟩ := rotPow_inv_last_mem hpre hM.isMonogon hM.isSimpleStrandPath h0 hc
      (k := q + o + 1) (by omega)
    subst hd'
    refine ⟨rotPow_inv_last_notMem_insideDarts hX hM hh _, fun hP => ?_,
      fun hP => by have := h2.1 hP; omega⟩
    have := h1.1 hP
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [cornerExp'] at this <;> omega
  cases ζ
  · simp only [outsideList, List.mem_append, mem_cornerList] at hd
    rcases hd with hd | ⟨q, hq, hd⟩
    · exact hside .left (by decide) hd
    · exact hcorner q hq 1 (Or.inl ⟨rfl, rfl⟩) hd
  · simp only [outsideList, List.mem_append, mem_cornerList] at hd
    rcases hd with hd | ⟨q, hq, hd⟩
    · exact hside .right (by decide) hd
    · exact hcorner q hq 0 (Or.inr ⟨rfl, rfl⟩) hd

omit hX in
/-- The darts of the outside list lie at the vertices of `M`. -/
private theorem exists_vertexOf_eq_of_mem_outsideList {d : H}
    (hd : d ∈ outsideList X ζ P (X.inv (P[P.length - 1]'(by have := hM.length_pos; omega)))) :
    ∃ e ∈ P, X.vertexOf d = X.vertexOf e := by
  have h0 := hM.length_pos
  have hcorner : ∀ k, X.vertexOf ((X.rot ^ k) (X.inv (P[P.length - 1]'(by omega)))) =
      X.vertexOf P[0] := fun k => by
    rw [X.vertexOf_rot_pow_apply, (vertexOf_inv_last' hM.isMonogon h0).1]
  cases ζ <;>
  · simp only [outsideList, List.mem_append, mem_cornerList] at hd
    rcases hd with hd | ⟨q, hq, rfl⟩
    · obtain ⟨l, hl, -, hv⟩ := vertexOf_of_mem_sideList hM.isMonogon.isStrandPath hd
      exact ⟨_, List.getElem_mem hl, hv⟩
    · exact ⟨_, List.getElem_mem h0, hcorner _⟩

/-- The outside list has no repetition. -/
private theorem nodup_outsideList :
    (outsideList X ζ P (X.inv (P[P.length - 1]'(by have := hM.length_pos; omega)))).Nodup := by
  have hpre := hX.toIsPreTripleDiagram
  have h0 := hM.length_pos
  have hw := hM.isMonogon.isSimpleClosedWalk hpre hM.isSimpleStrandPath
  have hx := vertexOf_inv_last' hM.isMonogon h0
  have htrip : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (P[P.length - 1]'(by omega)))) :=
    hx.1 ▸ hx.2
  have hcn : ∀ o, o ≤ 1 → (cornerList X o (X.inv (P[P.length - 1]'(by omega)))).Nodup := by
    intro o ho
    rw [List.nodup_iff_injective_get]
    intro i j hij
    simp only [List.get_eq_getElem, getElem_cornerList] at hij
    have hlen := length_cornerList (X := X) o (X.inv (P[P.length - 1]'(by omega)))
    have hi := i.isLt
    have hj := j.isLt
    exact Fin.ext (by have := rotPow_inj hpre htrip (by omega) (by omega) hij; omega)
  have hdisj : ∀ ζ' o, ∀ a ∈ X.sideList ζ' P,
      ∀ c ∈ cornerList X o (X.inv (P[P.length - 1]'(by omega))), a ≠ c := by
    intro ζ' o a ha c hc hac
    obtain ⟨l, hl, -, hv⟩ := vertexOf_of_mem_sideList hM.isMonogon.isStrandPath ha
    obtain ⟨q, -, rfl⟩ := mem_cornerList.1 hc
    rw [hac, X.vertexOf_rot_pow_apply, hx.1] at hv
    have := vertexOf_getElem_inj' hw h0 hl hv
    omega
  cases ζ
  · exact List.nodup_append.2 ⟨nodup_sideList hpre hM.isMonogon hM.isSimpleStrandPath _,
      hcn 1 le_rfl, hdisj _ _⟩
  · exact List.nodup_append.2 ⟨nodup_sideList hpre hM.isMonogon hM.isSimpleStrandPath _,
      hcn 0 (by norm_num), hdisj _ _⟩

end Classify

/-! ### Chains of the face permutation along the lists -/

section Chains

variable {X : TripleData H b}

omit [Fintype H] [DecidableEq H] in
private theorem facePerm_apply' (d : H) : X.facePerm d = X.rot (X.inv d) := rfl

omit [Fintype H] [DecidableEq H] in
private theorem facePerm_pow_succ_apply' (n : ℕ) (d : H) :
    (X.facePerm ^ (n + 1)) d = X.facePerm ((X.facePerm ^ n) d) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

/-- From `σ(a)` the orbit of `φ` runs outside `K` to `c`: `φ^{t+1}(ā) = c`, and the darts
`φ^j(ā)` with `0 < j ≤ t` are not in `K`. -/
private def ChainTo (X : TripleData H b) (K : Finset H) (a c : H) : Prop :=
  ∃ t, (X.facePerm ^ (t + 1)) (X.inv a) = c ∧
    ∀ j, 0 < j → j ≤ t → (X.facePerm ^ j) (X.inv a) ∉ K

omit [Fintype H] [DecidableEq H] in
private theorem chainTo_zero (hinv : Function.Involutive X.inv) {K : Finset H} {a c : H}
    (h : X.rot a = c) : ChainTo X K a c :=
  ⟨0, by rw [zero_add, pow_one, facePerm_apply', hinv, h], fun j hj hj' => absurd hj' (by omega)⟩

omit [Fintype H] [DecidableEq H] in
private theorem chainTo_one (hinv : Function.Involutive X.inv) {K : Finset H} {a c₁ c : H}
    (h₁ : X.rot a = c₁) (hc₁ : c₁ ∉ K) (h₂ : X.facePerm c₁ = c) : ChainTo X K a c := by
  refine ⟨1, ?_, fun j hj hj' => ?_⟩
  · rw [facePerm_pow_succ_apply', pow_one, facePerm_apply' (X.inv a), hinv, h₁, h₂]
  · obtain rfl : j = 1 := by omega
    rwa [pow_one, facePerm_apply', hinv, h₁]

omit [Fintype H] [DecidableEq H] in
private theorem chainTo_two (hinv : Function.Involutive X.inv) {K : Finset H} {a c₁ c₂ c : H}
    (h₁ : X.rot a = c₁) (hc₁ : c₁ ∉ K) (h₂ : X.facePerm c₁ = c₂) (hc₂ : c₂ ∉ K)
    (h₃ : X.facePerm c₂ = c) : ChainTo X K a c := by
  have e : X.facePerm (X.inv a) = c₁ := by rw [facePerm_apply', hinv, h₁]
  refine ⟨2, ?_, fun j hj hj' => ?_⟩
  · rw [facePerm_pow_succ_apply', facePerm_pow_succ_apply', pow_one, e, h₂, h₃]
  · rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
    · rwa [pow_one, e]
    · rwa [facePerm_pow_succ_apply', pow_one, e, h₂]

omit [Fintype H] [DecidableEq H] in
/-- The chains between consecutive darts of a list give the hypothesis of the face count of a
cut. -/
private theorem chain_of_chainTo {K : Finset H} {L : List H} (hN : 0 < L.length)
    (hstep : ∀ k (hk : k + 1 < L.length), ChainTo X K L[k] L[k + 1])
    (hlast : ChainTo X K (L[L.length - 1]'(by omega)) (L[0]'hN)) :
    ∀ k : Fin L.length, ∃ t, (X.facePerm ^ (t + 1)) (X.inv L[(k : ℕ)]) =
      L[((finRotate _ k : Fin L.length) : ℕ)] ∧
      ∀ j, 0 < j → j ≤ t → (X.facePerm ^ j) (X.inv L[(k : ℕ)]) ∉ K := by
  rintro ⟨k, hk⟩
  by_cases hk' : k + 1 < L.length
  · have e : ((finRotate _ ⟨k, hk⟩ : Fin L.length) : ℕ) = k + 1 := by
      rw [val_finRotate', if_pos hk']
    simp only [e]
    exact hstep k hk'
  · have e : ((finRotate _ ⟨k, hk⟩ : Fin L.length) : ℕ) = 0 := by
      rw [val_finRotate', if_neg hk']
    simp only [e]
    obtain rfl : k = L.length - 1 := by omega
    exact hlast

variable {P : List H}

private theorem rot_rot_pow_two_inv_getElem (hP : X.IsStrandPath P) {l : ℕ}
    (hl : l + 1 < P.length) :
    X.rot ((X.rot ^ 2) (X.inv P[l])) = P[l + 1] := by
  rw [(strandStep_getElem' hP hl).2]
  rfl

private theorem rot_rot_pow_five (hX : X.IsPreTripleDiagram) {d : H}
    (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) : X.rot ((X.rot ^ 5) d) = d := by
  change (X.rot ^ 6) d = d
  exact hX.rot_pow_six_apply hd

/-- Consecutive darts of the right list. -/
private theorem chainTo_sideList_right (hX : X.IsPreTripleDiagram) (hP : X.IsStrandPath P)
    {K : Finset H} (hK : ∀ e ∈ P, e ∉ K) {k : ℕ}
    (hk : k + 1 < (X.sideList .right P).length) :
    ChainTo X K (X.sideList .right P)[k] (X.sideList .right P)[k + 1] := by
  have hlen := length_sideList (X := X) .right P
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [getElem_sideList_right_two_mul (by omega), getElem_sideList_right_two_mul_add_one
      (by omega)]
    exact chainTo_zero hX.inv_involutive rfl
  · simp only [show 2 * l + 1 + 1 = 2 * (l + 1) by ring]
    rw [getElem_sideList_right_two_mul_add_one (by omega), getElem_sideList_right_two_mul
      (by omega)]
    exact chainTo_one hX.inv_involutive (rot_rot_pow_two_inv_getElem hP (by omega))
      (hK _ (List.getElem_mem _)) rfl

/-- Consecutive darts of the left list. -/
private theorem chainTo_sideList_left (hX : X.IsPreTripleDiagram) (hP : X.IsStrandPath P)
    {K : Finset H} (hK : ∀ e ∈ P, X.inv e ∉ K) {k : ℕ}
    (hk : k + 1 < (X.sideList .left P).length) :
    ChainTo X K (X.sideList .left P)[k] (X.sideList .left P)[k + 1] := by
  have hlen := length_sideList (X := X) .left P
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have e1 := getElem_sideList_left_two_mul (X := X) (P := P) (l := P.length - 2 - j)
      (by omega)
    have e2 := getElem_sideList_left_two_mul_add_one (X := X) (P := P) (l := P.length - 2 - j)
      (by omega)
    simp only [show P.length - 2 - (P.length - 2 - j) = j by omega] at e1 e2
    rw [e1, e2]
    exact chainTo_zero hX.inv_involutive rfl
  · set l := P.length - 2 - j with hl
    have e1 := getElem_sideList_left_two_mul_add_one (X := X) (P := P) (l := l) (by omega)
    have e2 := getElem_sideList_left_two_mul (X := X) (P := P) (l := l - 1) (by omega)
    simp only [show P.length - 2 - l = j by omega,
      show P.length - 2 - (l - 1) = j + 1 by omega] at e1 e2
    simp only [show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    rw [e1, e2]
    have hstep := strandStep_getElem' hP (l := l - 1) (by omega)
    simp only [show l - 1 + 1 = l by omega] at hstep
    refine chainTo_one hX.inv_involutive (c₁ := X.inv P[l])
      (rot_rot_pow_five hX (strandStep_getElem' hP (l := l) (by omega)).1)
      (hK _ (List.getElem_mem _)) ?_
    rw [facePerm_apply', hX.inv_inv_apply, hstep.2]
    rfl

omit [Fintype H] [DecidableEq H] in
/-- Chains along a concatenation of two lists. -/
private theorem chainTo_append {K : Finset H} {A B : List H} (hA : 0 < A.length)
    (hB : 0 < B.length) (hsA : ∀ k (hk : k + 1 < A.length), ChainTo X K A[k] A[k + 1])
    (hmid : ChainTo X K (A[A.length - 1]'(by omega)) (B[0]'hB))
    (hsB : ∀ k (hk : k + 1 < B.length), ChainTo X K B[k] B[k + 1])
    (hlast : ChainTo X K (B[B.length - 1]'(by omega)) (A[0]'hA)) :
    (∀ k (hk : k + 1 < (A ++ B).length), ChainTo X K (A ++ B)[k] (A ++ B)[k + 1]) ∧
      ChainTo X K ((A ++ B)[(A ++ B).length - 1]'(by simp; omega))
        ((A ++ B)[0]'(by simp; omega)) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [List.length_append] at hk
    by_cases h1 : k + 1 < A.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left h1]
      exact hsA k h1
    by_cases h2 : k + 1 = A.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
      obtain rfl : k = A.length - 1 := by omega
      simp only [show A.length - 1 + 1 - A.length = 0 by omega]
      exact hmid
    · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      simp only [show k + 1 - A.length = k - A.length + 1 by omega]
      exact hsB _ (by omega)
  · rw [List.getElem_append_right (by simp; omega), List.getElem_append_left hA]
    simp only [List.length_append, show A.length + B.length - 1 - A.length = B.length - 1 by omega]
    exact hlast

omit [Fintype H] [DecidableEq H] in
private theorem chainTo_cornerList (hinv : Function.Involutive X.inv) {K : Finset H} {o : ℕ}
    {c : H} {k : ℕ} (hk : k + 1 < (cornerList X o c).length) :
    ChainTo X K (cornerList X o c)[k] (cornerList X o c)[k + 1] := by
  rw [getElem_cornerList, getElem_cornerList]
  refine chainTo_zero hinv ?_
  rw [show k + 1 + o + 1 = (k + o + 1) + 1 by ring, pow_succ' X.rot (k + o + 1),
    Equiv.Perm.mul_apply]

variable {ζ : StrandSide} {h : X.faceOrbits → ℤ}

/-- The chains of `φ` along the inside list: from `σ(g_k)` the orbit of `φ` runs outside the
inside darts to `g_{k+1}`. -/
private theorem chain_insideList (hX : X.IsTripleDiagram) (hM : X.IsConvexMonogon P ζ)
    (hm : 2 ≤ P.length) :
    ∀ k : Fin (X.insideList ζ P).length, ∃ t,
      (X.facePerm ^ (t + 1)) (X.inv (X.insideList ζ P)[(k : ℕ)]) =
        (X.insideList ζ P)[((finRotate _ k : Fin (X.insideList ζ P).length) : ℕ)] ∧
      ∀ j, 0 < j → j ≤ t → (X.facePerm ^ j) (X.inv (X.insideList ζ P)[(k : ℕ)]) ∉
        X.insideDarts P ζ h := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  have h0 := hM.length_pos
  have hP := hM.isMonogon.isStrandPath
  have hlen := length_sideList (X := X) ζ P
  have hK1 : ∀ e ∈ P, e ∉ X.insideDarts P ζ h := fun e he hK =>
    ((mem_insideDarts h0).1 hK).2.1 he
  have hK2 : ∀ e ∈ P, X.inv e ∉ X.insideDarts P ζ h := fun e he hK =>
    ((mem_insideDarts h0).1 hK).2.2.1 (by rwa [hpre.inv_inv_apply])
  have hc := hM.isInsideCorner_getElem
  refine chain_of_chainTo (by simp only [insideList]; omega) (fun k hk => ?_) ?_
  · cases ζ
    · exact chainTo_sideList_right hpre hP hK1 hk
    · exact chainTo_sideList_left hpre hP hK2 hk
  · cases ζ
    · have e1 : (X.insideList .right P)[(X.insideList .right P).length - 1]'(by
          simp only [insideList]; omega) = (X.rot ^ 2) (X.inv (P[P.length - 2]'(by omega))) := by
        simp only [insideList, hlen, show 2 * (P.length - 1) - 1 = 2 * (P.length - 2) + 1 by omega]
        exact getElem_sideList_right_two_mul_add_one (by omega)
      have e0 : (X.insideList .right P)[0]'(by simp only [insideList]; omega) =
          X.rot (X.inv (P[0]'h0)) := getElem_sideList_right_two_mul (l := 0) (by omega)
      rw [e1, e0]
      have hs := rot_rot_pow_two_inv_getElem (X := X) hP (l := P.length - 2) (by omega)
      simp only [show P.length - 2 + 1 = P.length - 1 by omega] at hs
      exact chainTo_two hinv hs (hK1 _ (List.getElem_mem _)) hc (hK1 _ (List.getElem_mem _)) rfl
    · have e1 : (X.insideList .left P)[(X.insideList .left P).length - 1]'(by
          simp only [insideList]; omega) = (X.rot ^ 5) (X.inv (P[0]'h0)) := by
        have := getElem_sideList_left_two_mul_add_one (X := X) (P := P) (l := 0) (by omega)
        simp only [insideList, hlen, show 2 * (P.length - 1) - 1 = 2 * (P.length - 2 - 0) + 1 by
          omega]
        exact this
      have e0 : (X.insideList .left P)[0]'(by simp only [insideList]; omega) =
          (X.rot ^ 4) (X.inv (P[P.length - 2]'(by omega))) := by
        simpa only [show P.length - 2 - (P.length - 2) = 0 by omega, mul_zero] using
          getElem_sideList_left_two_mul (X := X) (P := P) (l := P.length - 2) (by omega)
      rw [e1, e0]
      have hstep := strandStep_getElem' hP (l := P.length - 2) (by omega)
      simp only [show P.length - 2 + 1 = P.length - 1 by omega] at hstep
      refine chainTo_two hinv (c₂ := X.inv (P[P.length - 1]'(by omega)))
        (rot_rot_pow_five hpre (strandStep_getElem' hP (l := 0)
        (by omega)).1) (hK2 _ (List.getElem_mem _)) ?_ (hK2 _ (List.getElem_mem _)) ?_
      · rw [facePerm_apply', hinv]
        exact hc
      · rw [facePerm_apply', hinv, hstep.2]
        rfl

/-- The chains of `φ` along the outside list. -/
private theorem chain_outsideList (hX : X.IsTripleDiagram) (hM : X.IsConvexMonogon P ζ)
    (hm : 2 ≤ P.length) :
    let Lo := outsideList X ζ P (X.inv (P[P.length - 1]'(by omega)))
    ∀ k : Fin Lo.length, ∃ t, (X.facePerm ^ (t + 1)) (X.inv Lo[(k : ℕ)]) =
        Lo[((finRotate _ k : Fin Lo.length) : ℕ)] ∧
      ∀ j, 0 < j → j ≤ t → (X.facePerm ^ j) (X.inv Lo[(k : ℕ)]) ∉
        outsideDarts X (X.insideDarts P ζ h) P := by
  intro Lo
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  have h0 := hM.length_pos
  have hP := hM.isMonogon.isStrandPath
  have hO1 : ∀ e ∈ P, e ∉ outsideDarts X (X.insideDarts P ζ h) P := fun e he hO =>
    (mem_outsideDarts.1 hO).2.1 he
  have hO2 : ∀ e ∈ P, X.inv e ∉ outsideDarts X (X.insideDarts P ζ h) P := fun e he hO =>
    (mem_outsideDarts.1 hO).2.2 (by rwa [hpre.inv_inv_apply])
  have hc := hM.isInsideCorner_getElem
  have hx := vertexOf_inv_last' hM.isMonogon h0
  have htx : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (P[P.length - 1]'(by omega)))) :=
    hx.1 ▸ hx.2
  have hstep := strandStep_getElem' hP (l := P.length - 2) (by omega)
  simp only [show P.length - 2 + 1 = P.length - 1 by omega] at hstep
  have hlenR := length_sideList (X := X) .right P
  have hlenL := length_sideList (X := X) .left P
  have hcl := fun o => length_cornerList (X := X) o (X.inv (P[P.length - 1]'(by omega)))
  have hNo : 0 < Lo.length := by
    simp only [Lo, length_outsideList]; omega
  cases ζ
  · have key := chainTo_append (X := X) (K := outsideDarts X (X.insideDarts P .right h) P)
      (A := X.sideList .left P) (B := cornerList X 1 (X.inv (P[P.length - 1]'(by omega))))
      (by omega) (by rw [hcl]; omega) (fun k hk => chainTo_sideList_left hpre hP hO2 hk) ?_
      (fun k hk => chainTo_cornerList hinv hk) ?_
    · exact chain_of_chainTo hNo key.1 key.2
    · have e1 : (X.sideList .left P)[(X.sideList .left P).length - 1]'(by omega) =
          (X.rot ^ 5) (X.inv (P[0]'h0)) := by
        have := getElem_sideList_left_two_mul_add_one (X := X) (P := P) (l := 0) (by omega)
        simp only [hlenL, show 2 * (P.length - 1) - 1 = 2 * (P.length - 2 - 0) + 1 by omega]
        exact this
      rw [e1, getElem_cornerList]
      refine chainTo_one hinv (rot_rot_pow_five hpre (strandStep_getElem' hP (l := 0)
        (by omega)).1) (hO2 _ (List.getElem_mem _)) ?_
      change X.rot (X.inv (X.inv P[0])) = _
      rw [hinv, ← hc]
      rfl
    · rw [getElem_cornerList]
      have e0 : (X.sideList .left P)[0]'(by omega) =
          (X.rot ^ 4) (X.inv (P[P.length - 2]'(by omega))) := by
        simpa only [show P.length - 2 - (P.length - 2) = 0 by omega, mul_zero] using
          getElem_sideList_left_two_mul (X := X) (P := P) (l := P.length - 2) (by omega)
      rw [e0]
      simp only [hcl]
      refine chainTo_one hinv (rot_rot_pow_five hpre htx) (hO2 _ (List.getElem_mem _)) ?_
      rw [facePerm_apply', hinv, hstep.2]
      rfl
  · have key := chainTo_append (X := X) (K := outsideDarts X (X.insideDarts P .left h) P)
      (A := X.sideList .right P) (B := cornerList X 0 (X.inv (P[P.length - 1]'(by omega))))
      (by omega) (by rw [hcl]; omega) (fun k hk => chainTo_sideList_right hpre hP hO1 hk) ?_
      (fun k hk => chainTo_cornerList hinv hk) ?_
    · exact chain_of_chainTo hNo key.1 key.2
    · have e1 : (X.sideList .right P)[(X.sideList .right P).length - 1]'(by omega) =
          (X.rot ^ 2) (X.inv (P[P.length - 2]'(by omega))) := by
        simp only [hlenR, show 2 * (P.length - 1) - 1 = 2 * (P.length - 2) + 1 by omega]
        exact getElem_sideList_right_two_mul_add_one (by omega)
      rw [e1, getElem_cornerList]
      have hs := rot_rot_pow_two_inv_getElem (X := X) hP (l := P.length - 2) (by omega)
      simp only [show P.length - 2 + 1 = P.length - 1 by omega] at hs
      exact chainTo_one hinv hs (hO1 _ (List.getElem_mem _)) rfl
    · rw [getElem_cornerList, getElem_sideList_right_two_mul (l := 0) (by omega)]
      simp only [hcl]
      have he1 := getElem_zero_eq_rotPow hpre hM.isMonogon h0 hc
      simp only [cornerExp'] at he1
      refine chainTo_one hinv (c₁ := P[0]) ?_ (hO1 _ (List.getElem_mem _)) rfl
      rw [he1]
      rfl

end Chains

/-! ### Counting the vertices and edges of a cut -/

section CutCount

variable {X : TripleData H b} {K : Finset H} {L : List H} {s : ℕ}

/-- A rotation system whose involution is fixed-point-free has half as many edges as darts. -/
private theorem two_mul_card_edges_eq (R : RotationSystem H)
    (hinv : Function.Involutive R.inv) (hfix : ∀ d, R.inv d ≠ d) :
    2 * R.edges.card = Fintype.card H := by
  have hfib : ∀ s ∈ univ.image R.edgeOf,
      ({a ∈ univ | R.edgeOf a = s} : Finset H).card = 2 := by
    intro s hs
    obtain ⟨d, -, rfl⟩ := mem_image.1 hs
    have : ({a ∈ univ | R.edgeOf a = R.edgeOf d} : Finset H) = R.edgeOf d := by
      ext a
      simp only [mem_filter, mem_univ, true_and, RotationSystem.mem_edgeOf]
      refine ⟨fun h => R.mem_edgeOf.1 (h ▸ R.mem_edgeOf.2 (Or.inl rfl)), ?_⟩
      rintro (rfl | rfl)
      · rfl
      · ext x
        simp only [RotationSystem.mem_edgeOf, hinv d]
        tauto
    rw [this, RotationSystem.edgeOf, card_pair (hfix d).symm]
  rw [← card_univ, card_eq_sum_card_image R.edgeOf univ, sum_const_nat hfib,
    RotationSystem.edges, mul_comm]

/-- A cut has at least as many vertices as the triple points of `X` it keeps plus the new
endpoints. -/
private theorem card_vertices_cut_ge (hc : X.IsCutData K L) :
    ((K.filter (· ∉ L)).image X.vertexOf).card + L.length ≤ (X.cut K L s).vertices.card := by
  have hV : (X.cut K L s).vertices.card =
      (X.cut K L s).boundaryVertices.card + (X.cut K L s).internalVertices.card := by
    rw [DiskMap.boundaryVertices, DiskMap.internalVertices, card_filter_add_card_filter_not]
  have hI : (X.cut K L s).internalVertices.card =
      ((K.filter (· ∉ L)).image X.vertexOf).card := by
    rw [hc.internalVertices_cut, card_image_of_injOn]
    intro v hv w hw hvw
    simp only [coe_image, coe_filter, Set.mem_image, Set.mem_setOf_eq] at hv hw
    obtain ⟨d, ⟨hdK, hdL⟩, rfl⟩ := hv
    obtain ⟨d', ⟨hdK', hdL'⟩, rfl⟩ := hw
    have key : ∀ {d d' : H} (hdK : d ∈ K) (hdL : d ∉ L),
        liftVertex K L.length (X.vertexOf d) = liftVertex K L.length (X.vertexOf d') →
        X.vertexOf d ⊆ X.vertexOf d' := by
      intro d d' hdK hdL h x hx
      have hxK := (hc.mem_of_mem_vertexOf d hdK hdL x hx).1
      have : (Sum.inl ⟨x, hxK⟩ : CutDart K L.length) ∈ liftVertex K L.length (X.vertexOf d) :=
        mem_liftVertex.2 ⟨⟨x, hxK⟩, hx, rfl⟩
      rw [h, mem_liftVertex] at this
      obtain ⟨y, hy, hxy⟩ := this
      rw [← Sum.inl_injective hxy] at hy
      exact hy
    exact Subset.antisymm (key hdK hdL hvw) (key hdK' hdL' hvw.symm)
  have hB : L.length ≤ (X.cut K L s).boundaryVertices.card := by
    have hsub : univ.image (cutTriple K L) ⊆ (X.cut K L s).boundaryVertices := by
      intro v hv
      obtain ⟨k, -, rfl⟩ := mem_image.1 hv
      refine (X.cut K L s).mem_boundaryVertices.2 ⟨(X.cut K L s).mem_vertices.2
        ⟨cutListDart K L k, hc.cut_vertexOf_cutListDart k⟩, ?_⟩
      rw [← hc.cut_vertexOf_cutListDart (s := s) k]
      exact hc.cut_isBoundaryVertex_vertexOf_of_mem_cutTriple (k := k) (by simp [cutTriple])
    calc L.length = (univ.image (cutTriple K L)).card := by
          rw [card_image_of_injective _ hc.cutTriple_injective, card_univ, Fintype.card_fin]
      _ ≤ _ := card_le_card hsub
  omega

/-- The edges of a cut. -/
private theorem two_mul_card_edges_cut (hc : X.IsCutData K L) (hinv : Function.Involutive X.inv)
    (hfix : ∀ d, X.inv d ≠ d) :
    2 * (X.cut K L s).edges.card = K.card + 2 * L.length := by
  rw [two_mul_card_edges_eq (X.cut K L s).toRotationSystem (hc.cut_inv_involutive hinv) ?_,
    IsCutData.card_cutDart]
  rintro (d | ⟨k, β⟩)
  · rw [hc.cut_inv_inl hinv]
    intro h
    exact hfix d.1 (congrArg Subtype.val (Sum.inl_injective h))
  · rw [hc.cut_inv_inr hinv]
    cases β <;> simp

end CutCount

/-! ### Euler's relation for the inside -/

section Euler

variable {X : TripleData H b} {P : List H} {ζ : StrandSide} {h : X.faceOrbits → ℤ}

/-- The data of `X` with the set `B` emptied: the same rotation system, without endpoints. -/
private def emptyBdry (X : TripleData H b) : TripleData H b := { X with bdry := ∅ }

omit [Fintype H] [DecidableEq H] in
private theorem not_isBoundaryVertex_emptyBdry (v : Finset H) :
    ¬(emptyBdry X).IsBoundaryVertex v := by
  rintro ⟨d, -, hd⟩
  simp [emptyBdry] at hd

omit [Fintype H] [DecidableEq H] in
private theorem mem_of_reach' {T : Set H} (hrot : ∀ x ∈ T, X.rot x ∈ T)
    (hinv : ∀ x ∈ T, X.inv x ∈ T) {d e : H} (h : X.Reach d e) : d ∈ T → e ∈ T := by
  induction h with
  | refl => exact id
  | rot _ ih => exact fun hd => hrot _ (ih hd)
  | inv _ ih => exact fun hd => hinv _ (ih hd)

/-- The reverse of a dart of a monogon lies at the vertex of a dart of the monogon. -/
private theorem exists_vertexOf_inv_eq' (hP : X.IsMonogon P) {e : H} (he : e ∈ P) :
    ∃ e' ∈ P, X.vertexOf (X.inv e) = X.vertexOf e' := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  by_cases hj' : j + 1 < P.length
  · exact ⟨_, List.getElem_mem hj', (strandStep_getElem' hP.isStrandPath hj').vertexOf_eq.symm⟩
  · obtain rfl : j = P.length - 1 := by omega
    exact ⟨_, List.getElem_mem (by omega), (vertexOf_inv_last' hP (by omega)).1⟩

/-- A dart at a vertex avoided by a monogon is neither a dart of it nor the reverse of one. -/
private theorem notMem_of_avoids (hX : X.IsPreTripleDiagram) (hP : X.IsMonogon P) {d : H}
    (hd : ∀ e ∈ P, X.vertexOf d ≠ X.vertexOf e) : d ∉ P ∧ X.inv d ∉ P := by
  refine ⟨fun h => hd d h rfl, fun h => ?_⟩
  obtain ⟨e', he', hv⟩ := exists_vertexOf_inv_eq' hP h
  rw [hX.inv_inv_apply] at hv
  exact hd e' he' hv

variable (hX : X.IsTripleDiagram) (hM : X.IsConvexMonogon P ζ)
  (hh : X.IsMonogonWindingFunction P h)

include hX hM hh

/-- The inside darts are generated from the inside list by the involution and by `σ` off the
list. -/
private theorem forall_mem_insideDarts_of_closed (C : Set H)
    (hL : ∀ d ∈ X.insideList ζ P, d ∈ C)
    (hinv : ∀ d ∈ C, d ∈ X.insideDarts P ζ h → X.inv d ∈ C)
    (hrot : ∀ d ∈ C, d ∈ X.insideDarts P ζ h → d ∉ X.insideList ζ P → X.rot d ∈ C) :
    ∀ d ∈ X.insideDarts P ζ h, d ∈ C := by
  have hc := hM.isCutData_insideDarts hX hh
  have hpow : ∀ d ∈ C, d ∈ X.insideDarts P ζ h → d ∉ X.insideList ζ P → ∀ n,
      (X.rot ^ n) d ∈ C ∧ (X.rot ^ n) d ∈ X.insideDarts P ζ h ∧
        (X.rot ^ n) d ∉ X.insideList ζ P := by
    intro d hdC hdK hdL n
    induction n with
    | zero => exact ⟨hdC, hdK, hdL⟩
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨hrot _ ih.1 ih.2.1 ih.2.2, hc.rot_mem ih.2.1 ih.2.2, hc.rot_notMem ih.2.1 ih.2.2⟩
  have hT : X.IsClosedOff P {d | d ∈ C ∧ d ∈ X.insideDarts P ζ h} := by
    refine ⟨fun d hd => ⟨hinv d hd.1 hd.2, hc.inv_mem d hd.2⟩, fun d hd hb hav => ?_⟩
    have hdL : d ∉ X.insideList ζ P := fun hL => by
      obtain ⟨e, he, hv⟩ := exists_vertexOf_eq_of_mem_insideList hM.isMonogon.isStrandPath hL
      exact hav e he hv
    have h1 := hpow d hd.1 hd.2 hdL 1
    have h5 := hpow d hd.1 hd.2 hdL 5
    rw [pow_one] at h1
    have e5 : X.rot.symm d = (X.rot ^ 5) d := by
      rw [Equiv.symm_apply_eq]
      exact (rot_rot_pow_five hX.toIsPreTripleDiagram hb).symm
    exact ⟨⟨h1.1, h1.2.1⟩, by rw [e5]; exact ⟨h5.1, h5.2.1⟩⟩
  have hsub : {d | d ∈ X.insideList ζ P} ⊆ {d | d ∈ C ∧ d ∈ X.insideDarts P ζ h} :=
    fun d hd => ⟨hL d hd, hc.mem_of_mem_list d hd⟩
  intro d hd
  have := X.avoidingClosure_subset hsub hT
  rw [← hM.insideDarts_eq_avoidingClosure hX hh] at this
  exact (this hd).1

/-- The outside darts and the outside list satisfy the hypotheses of the cut, for `X` with `B`
emptied. -/
private theorem isCutData_outside :
    (emptyBdry X).IsCutData (outsideDarts X (X.insideDarts P ζ h) P)
      (outsideList X ζ P (X.inv (P[P.length - 1]'(by have := hM.length_pos; omega)))) where
  nodup := nodup_outsideList hX hM
  mem_of_mem_list _ hd := mem_outsideDarts.2 (notMem_of_mem_outsideList hX hM hh hd)
  inv_mem d hd := by
    obtain ⟨h1, h2, h3⟩ := mem_outsideDarts.1 hd
    refine mem_outsideDarts.2 ⟨fun hK => h1 ?_, h3, ?_⟩
    · exact (inv_mem_insideDarts_iff hX.toIsPreTripleDiagram hh hM.length_pos d).1 hK
    · change X.inv (X.inv d) ∉ P
      rwa [hX.toIsPreTripleDiagram.inv_inv_apply]
  notMem_bdry d _ := by simp [emptyBdry]
  not_isBoundaryVertex _ _ _ := not_isBoundaryVertex_emptyBdry _
  mem_of_mem_vertexOf d hd hL e he := by
    have hpre := hX.toIsPreTripleDiagram
    obtain ⟨h1, h2, h3⟩ := mem_outsideDarts.1 hd
    change e ∈ X.vertexOf d at he
    have hav : ∀ e' ∈ P, X.vertexOf d ≠ X.vertexOf e' := by
      intro e' he' hv
      rcases mem_or_of_vertexOf_eq hX hM he' hv with h | h | h | h
      · exact h2 h
      · exact h3 h
      · exact h1 (hM.mem_insideDarts_of_mem_insideList hX hh h)
      · exact hL h
    have hve : X.vertexOf e = X.vertexOf d := X.vertexOf_eq_of_mem he
    have hav' : ∀ e' ∈ P, X.vertexOf e ≠ X.vertexOf e' := fun e' he' => hve ▸ hav e' he'
    obtain ⟨he2, he3⟩ := notMem_of_avoids hpre hM.isMonogon hav'
    refine ⟨mem_outsideDarts.2 ⟨fun heK => ?_, he2, he3⟩, fun heL => ?_⟩
    · by_cases hb : X.IsBoundaryVertex (X.vertexOf d)
      · exact hM.notMem_insideDarts_of_isBoundaryVertex hX hh (hve ▸ hb) heK
      · exact h1 ((mem_insideDarts_iff_of_forall_ne hX hM.isMonogon hh hb hav he).1 heK)
    · obtain ⟨e', he', hv⟩ := exists_vertexOf_eq_of_mem_outsideList hM heL
      exact hav' e' he' hv

/-- The outside darts are reached from the outside list by the steps of the outside system. -/
private theorem forall_mem_outsideDarts_of_closed (C : Set H)
    (hL : ∀ d ∈ outsideList X ζ P (X.inv (P[P.length - 1]'(by have := hM.length_pos; omega))),
      d ∈ C)
    (hinv : ∀ d ∈ C, d ∈ outsideDarts X (X.insideDarts P ζ h) P → X.inv d ∈ C)
    (hrot : ∀ d ∈ C, d ∈ outsideDarts X (X.insideDarts P ζ h) P →
      d ∉ outsideList X ζ P (X.inv (P[P.length - 1]'(by have := hM.length_pos; omega))) →
      X.rot d ∈ C) :
    ∀ d ∈ outsideDarts X (X.insideDarts P ζ h) P, d ∈ C := by
  have hpre := hX.toIsPreTripleDiagram
  have hc := hM.isCutData_insideDarts hX hh
  have hco := isCutData_outside hX hM hh
  have h0 := hM.length_pos
  set T : Set H := {d | (d ∈ C ∧ d ∈ outsideDarts X (X.insideDarts P ζ h) P) ∨
    d ∈ X.insideDarts P ζ h ∨ d ∈ P ∨ X.inv d ∈ P} with hTdef
  have hTinv : ∀ x ∈ T, X.inv x ∈ T := by
    rintro x (⟨hxC, hxO⟩ | hxK | hxP | hxP)
    · exact Or.inl ⟨hinv x hxC hxO, hco.inv_mem x hxO⟩
    · exact Or.inr (Or.inl (hc.inv_mem x hxK))
    · exact Or.inr (Or.inr (Or.inr (by rwa [hpre.inv_inv_apply])))
    · exact Or.inr (Or.inr (Or.inl hxP))
  have hTrot : ∀ x ∈ T, X.rot x ∈ T := by
    intro x hx
    by_cases hm : ∃ e ∈ P, X.vertexOf x = X.vertexOf e
    · obtain ⟨e, he, hv⟩ := hm
      rcases mem_or_of_vertexOf_eq hX hM (d := X.rot x) he (by rw [X.vertexOf_rot]; exact hv) with
        h | h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inl (hM.mem_insideDarts_of_mem_insideList hX hh h))
      · exact Or.inl ⟨hL _ h, hco.mem_of_mem_list _ h⟩
    · have hav : ∀ e ∈ P, X.vertexOf x ≠ X.vertexOf e := fun e he hv => hm ⟨e, he, hv⟩
      obtain ⟨hx2, hx3⟩ := notMem_of_avoids hpre hM.isMonogon hav
      rcases hx with ⟨hxC, hxO⟩ | hxK | hxP | hxP
      · have hxL : x ∉ outsideList X ζ P (X.inv (P[P.length - 1]'(by omega))) := fun hxL => by
          obtain ⟨e, he, hv⟩ := exists_vertexOf_eq_of_mem_outsideList hM hxL
          exact hav e he hv
        exact Or.inl ⟨hrot x hxC hxO hxL, hco.rot_mem hxO hxL⟩
      · have hxL : x ∉ X.insideList ζ P := fun hxL => by
          obtain ⟨e, he, hv⟩ := exists_vertexOf_eq_of_mem_insideList hM.isMonogon.isStrandPath hxL
          exact hav e he hv
        exact Or.inr (Or.inl (hc.rot_mem hxK hxL))
      · exact absurd hxP hx2
      · exact absurd hxP hx3
  intro d hd
  have hT := mem_of_reach' hTrot hTinv (hX.toIsDiskMap.toIsConnected.reach (P[0]'h0) d)
    (Or.inr (Or.inr (Or.inl (List.getElem_mem h0))))
  obtain ⟨h1, h2, h3⟩ := mem_outsideDarts.1 hd
  rcases hT with ⟨hC, -⟩ | hK | hP | hP
  · exact hC
  · exact absurd hK h1
  · exact absurd hP h2
  · exact absurd hP h3

omit hh in
/-- Every orbit of `φ` contains a dart that is neither a dart of `M` nor the reverse of one. -/
private theorem exists_faceOf_eq (hm : 2 ≤ P.length) (d : H) :
    ∃ d', X.faceOf d' = X.faceOf d ∧ d' ∉ P ∧ X.inv d' ∉ P := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  have h0 := hM.length_pos
  have hc := hM.isInsideCorner_getElem
  have hs := hM.isSimpleStrandPath
  have hP := hM.isMonogon
  have hz : ∀ l (hl : l + 1 < P.length) k, k < 6 → k ≠ 0 → k ≠ 3 →
      (X.rot ^ k) (X.inv P[l]) ∉ P ∧ X.inv ((X.rot ^ k) (X.inv P[l])) ∉ P := by
    intro l hl k hk h0' h3
    obtain ⟨h1, h2⟩ := rotPow_inv_getElem_mem hpre hP hs hl hk
    exact ⟨fun h => h3 (h1.1 h), fun h => h0' (h2.1 h)⟩
  have hx : ∀ k, k < 6 → k ≠ 0 → k ≠ cornerExp' ζ →
      (X.rot ^ k) (X.inv (P[P.length - 1]'(by omega))) ∉ P ∧
        X.inv ((X.rot ^ k) (X.inv (P[P.length - 1]'(by omega)))) ∉ P := by
    intro k hk h0' ht
    obtain ⟨h1, h2⟩ := rotPow_inv_last_mem hpre hP hs h0 hc hk
    exact ⟨fun h => ht (h1.1 h), fun h => h0' (h2.1 h)⟩
  have hφ : ∀ x, X.faceOf (X.facePerm x) = X.faceOf x := X.faceOf_facePerm
  have hlast := strandStep_getElem' hP.isStrandPath (l := P.length - 2) (by omega)
  simp only [show P.length - 2 + 1 = P.length - 1 by omega] at hlast
  by_cases hd1 : d ∈ P
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd1
    by_cases hj' : j + 1 < P.length
    · refine ⟨X.facePerm P[j], hφ _, ?_⟩
      have := hz j hj' 1 (by norm_num) (by norm_num) (by norm_num)
      rwa [pow_one] at this
    · obtain rfl : j = P.length - 1 := by omega
      cases ζ
      · have hc' : X.rot (X.inv P[P.length - 1]) = P[0] := hc
        refine ⟨X.facePerm (X.facePerm P[P.length - 1]), by rw [hφ, hφ], ?_⟩
        rw [facePerm_apply' P[P.length - 1], hc', facePerm_apply']
        have := hz 0 (by omega) 1 (by norm_num) (by norm_num) (by norm_num)
        rwa [pow_one] at this
      · refine ⟨X.facePerm P[P.length - 1], hφ _, ?_⟩
        have := hx 1 (by norm_num) (by norm_num) (by simp [cornerExp'])
        rwa [pow_one] at this
  · by_cases hd2 : X.inv d ∈ P
    · obtain ⟨j, hj, hjd⟩ := List.getElem_of_mem hd2
      have hd' : d = X.inv P[j] := by rw [hjd, hinv]
      subst hd'
      by_cases j0 : j = 0
      · subst j0
        cases ζ
        · have hc' : X.rot (X.inv P[P.length - 1]) = P[0] := hc
          refine ⟨X.facePerm (X.inv P[0]), hφ _, ?_⟩
          rw [facePerm_apply', hinv, ← hc']
          exact hx 2 (by norm_num) (by norm_num) (by simp [cornerExp'])
        · have hc' : X.rot P[0] = X.inv P[P.length - 1] := hc
          refine ⟨X.facePerm (X.facePerm (X.inv P[0])), by rw [hφ, hφ], ?_⟩
          rw [facePerm_apply' (X.inv P[0]), hinv, hc', facePerm_apply', hinv, hlast.2]
          exact hz (P.length - 2) (by omega) 4 (by norm_num) (by norm_num) (by norm_num)
      · have hstep := strandStep_getElem' hP.isStrandPath (l := j - 1) (by omega)
        simp only [show j - 1 + 1 = j by omega] at hstep
        refine ⟨X.facePerm (X.inv P[j]), hφ _, ?_⟩
        rw [facePerm_apply', hinv, hstep.2]
        exact hz (j - 1) (by omega) 4 (by norm_num) (by norm_num) (by norm_num)
    · exact ⟨d, rfl, hd1, hd2⟩

omit hh in
/-- The vertices of `X`: those of `M`, and those of the inside and of the outside darts. -/
private theorem card_vertices_le :
    X.vertices.card ≤ P.length +
      (((X.insideDarts P ζ h).filter (· ∉ X.insideList ζ P)).image X.vertexOf).card +
      (((outsideDarts X (X.insideDarts P ζ h) P).filter
        (· ∉ outsideList X ζ P (X.inv (P[P.length - 1]'(by have := hM.length_pos; omega))))).image
        X.vertexOf).card := by
  have hpre := hX.toIsPreTripleDiagram
  set A := ((X.insideDarts P ζ h).filter (· ∉ X.insideList ζ P)).image X.vertexOf with hA
  set B := ((outsideDarts X (X.insideDarts P ζ h) P).filter
    (· ∉ outsideList X ζ P (X.inv (P[P.length - 1]'(by have := hM.length_pos; omega))))).image
    X.vertexOf with hB
  have hsub : X.vertices ⊆ P.toFinset.image X.vertexOf ∪ A ∪ B := by
    intro v hv
    obtain ⟨d, rfl⟩ := X.mem_vertices.1 hv
    by_cases hm' : ∃ e ∈ P, X.vertexOf d = X.vertexOf e
    · obtain ⟨e, he, hve⟩ := hm'
      exact mem_union_left _ (mem_union_left _
        (mem_image.2 ⟨e, List.mem_toFinset.2 he, hve.symm⟩))
    · have hav : ∀ e ∈ P, X.vertexOf d ≠ X.vertexOf e := fun e he hve => hm' ⟨e, he, hve⟩
      obtain ⟨h2, h3⟩ := notMem_of_avoids hpre hM.isMonogon hav
      by_cases hK : d ∈ X.insideDarts P ζ h
      · refine mem_union_left _ (mem_union_right _ (mem_image.2 ⟨d, mem_filter.2 ⟨hK, ?_⟩, rfl⟩))
        intro hL
        obtain ⟨e, he, hve⟩ := exists_vertexOf_eq_of_mem_insideList hM.isMonogon.isStrandPath hL
        exact hav e he hve
      · refine mem_union_right _ (mem_image.2 ⟨d, mem_filter.2
          ⟨mem_outsideDarts.2 ⟨hK, h2, h3⟩, ?_⟩, rfl⟩)
        intro hL
        obtain ⟨e, he, hve⟩ := exists_vertexOf_eq_of_mem_outsideList hM hL
        exact hav e he hve
  have c1 := card_le_card hsub
  have c2 := card_union_le (P.toFinset.image X.vertexOf ∪ A) B
  have c3 := card_union_le (P.toFinset.image X.vertexOf) A
  have c4 : (P.toFinset.image X.vertexOf).card ≤ P.length :=
    card_image_le.trans (List.toFinset_card_le P)
  omega

omit hh in
/-- The darts of `X`: the inside darts, the outside darts and the `2m` darts `e_l, ē_l`. -/
private theorem card_add_card_le :
    (X.insideDarts P ζ h).card + (outsideDarts X (X.insideDarts P ζ h) P).card + 2 * P.length ≤
      Fintype.card H := by
  have hpre := hX.toIsPreTripleDiagram
  have h0 := hM.length_pos
  have hP := hM.isMonogon.isStrandPath
  have hnd : P.Nodup := List.nodup_iff_injective_get.2
    (hM.isMonogon.isSimpleClosedWalk hpre hM.isSimpleStrandPath).injective
  have hMd : Disjoint P.toFinset (P.toFinset.image X.inv) := by
    rw [disjoint_left]
    intro d hd hd'
    obtain ⟨e, he, rfl⟩ := mem_image.1 hd'
    have h1 := hP.isOut_eq_true _ (List.mem_toFinset.1 hd)
    rw [hpre.isOut_inv_apply (hP.notMem_bdry _ (List.mem_toFinset.1 he)),
      hP.isOut_eq_true _ (List.mem_toFinset.1 he)] at h1
    simp at h1
  have hMcard : (P.toFinset ∪ P.toFinset.image X.inv).card = 2 * P.length := by
    rw [card_union_of_disjoint hMd, card_image_of_injective _ X.inv.injective,
      List.toFinset_card_of_nodup hnd]
    ring
  have hd1 : Disjoint (X.insideDarts P ζ h) (outsideDarts X (X.insideDarts P ζ h) P) :=
    disjoint_left.2 fun d hK hO => (mem_outsideDarts.1 hO).1 hK
  have hd2 : Disjoint (X.insideDarts P ζ h ∪ outsideDarts X (X.insideDarts P ζ h) P)
      (P.toFinset ∪ P.toFinset.image X.inv) := by
    rw [disjoint_left]
    intro d hd hdM
    have hgood : d ∉ P ∧ X.inv d ∉ P := by
      rcases mem_union.1 hd with hK | hO
      · exact ⟨((mem_insideDarts h0).1 hK).2.1, ((mem_insideDarts h0).1 hK).2.2.1⟩
      · exact ⟨(mem_outsideDarts.1 hO).2.1, (mem_outsideDarts.1 hO).2.2⟩
    rcases mem_union.1 hdM with hdP | hdI
    · exact hgood.1 (List.mem_toFinset.1 hdP)
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hdI
      exact hgood.2 (by rw [hpre.inv_inv_apply]; exact List.mem_toFinset.1 he)
  have := card_le_univ (X.insideDarts P ζ h ∪ outsideDarts X (X.insideDarts P ζ h) P ∪
    (P.toFinset ∪ P.toFinset.image X.inv))
  rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1, hMcard] at this
  exact this

omit hh in
/-- The orbits of `φ` meet the inside or the outside darts. -/
private theorem card_faceOrbits_le (hm : 2 ≤ P.length) :
    X.faceOrbits.card ≤ ((X.insideDarts P ζ h).image X.faceOf).card +
      ((outsideDarts X (X.insideDarts P ζ h) P).image X.faceOf).card := by
  have hsub : X.faceOrbits ⊆ (X.insideDarts P ζ h).image X.faceOf ∪
      (outsideDarts X (X.insideDarts P ζ h) P).image X.faceOf := by
    intro f hf
    obtain ⟨d, rfl⟩ := X.mem_faceOrbits.1 hf
    obtain ⟨d', hd', h2, h3⟩ := exists_faceOf_eq hX hM hm d
    by_cases hK : d' ∈ X.insideDarts P ζ h
    · exact mem_union_left _ (mem_image.2 ⟨d', hK, hd'⟩)
    · exact mem_union_right _ (mem_image.2 ⟨d', mem_outsideDarts.2 ⟨hK, h2, h3⟩, hd'⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

omit hX hM hh in
private theorem emptyBdry_vertexOf : (emptyBdry X).vertexOf = X.vertexOf := rfl

omit hX hM hh in
private theorem emptyBdry_faceOf : (emptyBdry X).faceOf = X.faceOf := rfl

/-- **Euler's relation for the inside**: both the inside and the outside system are connected
rotation systems, whose Euler characteristics add up to `4`. -/
private theorem euler_monogonCut (hm : 2 ≤ P.length) :
    ((X.monogonCut P ζ h).vertices.card : ℤ) - (X.monogonCut P ζ h).edges.card +
      (X.monogonCut P ζ h).faceOrbits.card = 2 := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  have hc := hM.isCutData_insideDarts hX hh
  have hco := isCutData_outside hX hM hh
  have hlenL := length_insideList (X := X) ζ P
  have hlenO := length_outsideList (X := X) ζ P (X.inv (P[P.length - 1]'(by omega)))
  have conn' := hc.isConnected_cut (s := ζ.cutShift) hpre (by omega)
    (forall_mem_insideDarts_of_closed hX hM hh)
  have connO : ((emptyBdry X).cut (outsideDarts X (X.insideDarts P ζ h) P)
      (outsideList X ζ P (X.inv (P[P.length - 1]'(by omega)))) 0).IsConnected := by
    refine RotationSystem.IsConnected.of_reach ⟨.inr (⟨0, by omega⟩, true)⟩
      (hco.cut_inv_involutive hinv) ?_
      (hco.reach_cut hinv (by omega) (forall_mem_outsideDarts_of_closed hX hM hh))
    rintro (d | ⟨k, β⟩)
    · rw [hco.cut_inv_inl hinv]
      intro h'
      exact hX.inv_ne d.1 (congrArg Subtype.val (Sum.inl_injective h'))
    · rw [hco.cut_inv_inr hinv]
      cases β <;> simp
  have e1 := conn'.euler_le
  have e2 := connO.euler_le
  have f1 := hc.card_faceOrbits_cut (s := ζ.cutShift) hinv (by omega) (chain_insideList hX hM hm)
  have f2 := hco.card_faceOrbits_cut (s := 0) hinv (by omega) (chain_outsideList hX hM hm)
  have v1 := card_vertices_cut_ge (s := ζ.cutShift) hc
  have v2 := card_vertices_cut_ge (s := 0) hco
  have g1 := two_mul_card_edges_cut (s := ζ.cutShift) hc hinv hX.inv_ne
  have g2 := two_mul_card_edges_cut (s := 0) hco hinv hX.inv_ne
  rw [emptyBdry_vertexOf] at v2
  rw [emptyBdry_faceOf] at f2
  have hV := card_vertices_le (h := h) hX hM
  have hH := card_add_card_le (h := h) hX hM
  have hF := card_faceOrbits_le (h := h) hX hM hm
  have hE := two_mul_card_edges_eq X.toRotationSystem hinv hX.inv_ne
  have he := hX.euler
  change ((X.cut (X.insideDarts P ζ h) (X.insideList ζ P) ζ.cutShift).vertices.card : ℤ) -
    (X.cut (X.insideDarts P ζ h) (X.insideList ζ P) ζ.cutShift).edges.card +
    (X.cut (X.insideDarts P ζ h) (X.insideList ζ P) ζ.cutShift).faceOrbits.card = 2
  omega

omit hh in
/-- The orientation along the inside list alternates, starting with `out` (inside right) or
`in` (inside left). -/
private theorem isOut_insideList (k : Fin (X.insideList ζ P).length) :
    X.isOut (X.insideList ζ P)[(k : ℕ)] = decide (Even ((k : ℕ) + ζ.cutShift)) := by
  have hpre := hX.toIsPreTripleDiagram
  have hP := hM.isMonogon.isStrandPath
  obtain ⟨k, hk⟩ := k
  have hlen := length_sideList (X := X) ζ P
  cases ζ
  · change X.isOut (X.sideList .right P)[k] = decide (Even (k + 0))
    have hstep := strandStep_getElem' hP (l := k / 2) (by simp only [insideList] at hk; omega)
    rw [getElem_sideList_right, hpre.isOut_rot_pow_apply hstep.1,
      hpre.isOut_inv_apply (hP.notMem_bdry _ (List.getElem_mem _)),
      hP.isOut_eq_true _ (List.getElem_mem _)]
    rcases Nat.mod_two_eq_zero_or_one k with h' | h' <;> simp [h', Nat.even_iff]
  · change X.isOut (X.sideList .left P)[k] = decide (Even (k + 1))
    have hstep := strandStep_getElem' hP (l := P.length - 2 - k / 2)
      (by simp only [insideList] at hk; omega)
    rw [getElem_sideList_left, hpre.isOut_rot_pow_apply hstep.1,
      hpre.isOut_inv_apply (hP.notMem_bdry _ (List.getElem_mem _)),
      hP.isOut_eq_true _ (List.getElem_mem _)]
    rcases Nat.mod_two_eq_zero_or_one k with h' | h' <;> simp [h', Nat.even_iff] <;> omega

/-- **The inside of a convex monogon is a triple diagram**: for a convex monogon `M` of a triple
diagram `X` with `m ≥ 2`, `X|_M` is a triple diagram (with `m - 1` arcs, see
`length_insideList`). -/
@[cluster_algebras "lem_monogon_cut_triple"]
theorem IsConvexMonogon.isTripleDiagram_monogonCut (hm : 2 ≤ P.length) :
    (X.monogonCut P ζ h).IsTripleDiagram := by
  have hpre := hX.toIsPreTripleDiagram
  have hc := hM.isCutData_insideDarts hX hh
  have hlenL := length_insideList (X := X) ζ P
  refine IsPreTripleDiagram.isTripleDiagram ?_ ?_ (euler_monogonCut hX hM hh hm)
  · exact hc.isPreTripleDiagram_cut hpre (by omega) ⟨P.length - 1, by omega⟩
      (isOut_insideList hX hM)
  · exact (hc.isConnected_cut hpre (by omega)
      (forall_mem_insideDarts_of_closed hX hM hh)).transitive

end Euler

/-! ### Triple points, monogons, hollow monogons and arcs of the inside -/

section Features

variable {X : TripleData H b} {P : List H} {ζ : StrandSide} {h : X.faceOrbits → ℤ}
  (hX : X.IsTripleDiagram) (hM : X.IsConvexMonogon P ζ) (hh : X.IsMonogonWindingFunction P h)

include hX hM hh

open scoped Classical in
/-- **Triple points of the inside**: the triple points of `X|_M` are exactly the triple points of
`X` avoided by `M` (that is, different from the vertices of the darts of `M`, which are also the
vertices of their reverses) whose darts are inside, each carried by the darts over it. -/
@[cluster_algebras "lem_monogon_cut_triple"]
theorem IsConvexMonogon.internalVertices_monogonCut :
    (X.monogonCut P ζ h).internalVertices =
      (X.internalVertices.filter fun v =>
        (∀ e ∈ P, v ≠ X.vertexOf e) ∧ v ⊆ X.insideDarts P ζ h).image
        (liftVertex (X.insideDarts P ζ h) (X.insideList ζ P).length) := by
  have hc := hM.isCutData_insideDarts hX hh
  rw [monogonCut, hc.internalVertices_cut]
  congr 1
  ext v
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨d, ⟨hdK, hdL⟩, rfl⟩
    obtain ⟨hb, hav⟩ := hM.avoids_of_mem_insideDarts hX hh hdK hdL
    exact ⟨X.vertexOf_mem_internalVertices.2 hb, hav,
      fun e he => (hc.mem_of_mem_vertexOf d hdK hdL e he).1⟩
  · rintro ⟨hint, hav, hsub⟩
    obtain ⟨x, rfl⟩ := X.mem_vertices.1 (X.mem_internalVertices.1 hint).1
    refine ⟨x, ⟨hsub (X.self_mem_vertexOf x), fun hL => ?_⟩, rfl⟩
    obtain ⟨e, he, hv⟩ := exists_vertexOf_eq_of_mem_insideList hM.isMonogon.isStrandPath hL
    exact hav e he hv

open scoped Classical in
/-- **Number of triple points of the inside**: if `X` has `T` triple points, `X|_M` has at most
`T - m` of them. -/
@[cluster_algebras "lem_monogon_cut_triple"]
theorem IsConvexMonogon.card_internalVertices_monogonCut_le :
    (X.monogonCut P ζ h).internalVertices.card ≤ X.internalVertices.card - P.length := by
  have hpre := hX.toIsPreTripleDiagram
  set Z : Finset (Finset H) := P.toFinset.image X.vertexOf with hZ
  have hZcard : Z.card = P.length := by
    have e : Z = (P.map X.vertexOf).toFinset := by
      ext v
      simp [hZ]
    rw [e, List.toFinset_card_of_nodup hM.isSimpleStrandPath.nodup_map_vertexOf, List.length_map]
  have hZsub : Z ⊆ X.internalVertices := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := mem_image.1 hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.1 he)
    refine X.vertexOf_mem_internalVertices.2 ?_
    rcases j with _ | j
    · exact (vertexOf_inv_last' hM.isMonogon hj).2
    · exact (strandStep_getElem' hM.isMonogon.isStrandPath hj).not_isBoundaryVertex
  have hsub : (X.internalVertices.filter fun v =>
      (∀ e ∈ P, v ≠ X.vertexOf e) ∧ v ⊆ X.insideDarts P ζ h) ⊆ X.internalVertices \ Z := by
    intro v hv
    obtain ⟨hint, hav, -⟩ := mem_filter.1 hv
    refine mem_sdiff.2 ⟨hint, fun hvZ => ?_⟩
    obtain ⟨e, he, rfl⟩ := mem_image.1 hvZ
    exact hav e (List.mem_toFinset.1 he) rfl
  rw [hM.internalVertices_monogonCut hX hh]
  calc _ ≤ _ := card_image_le
    _ ≤ (X.internalVertices \ Z).card := card_le_card hsub
    _ = _ := by rw [card_sdiff_of_subset hZsub, hZcard]

/-- **Monogons of the inside**: a monogon of `X|_M` consists of inside darts, and these form a
monogon of `X`. -/
@[cluster_algebras "lem_monogon_cut_features"]
theorem IsConvexMonogon.exists_isMonogon_of_isMonogon_monogonCut
    {Q : List (CutDart (X.insideDarts P ζ h) (X.insideList ζ P).length)}
    (hQ : (X.monogonCut P ζ h).IsMonogon Q) :
    ∃ Q' : List {d // d ∈ X.insideDarts P ζ h}, Q = Q'.map Sum.inl ∧
      X.IsMonogon (Q'.map Subtype.val) := by
  have hc := hM.isCutData_insideDarts hX hh
  obtain ⟨Q', rfl, -⟩ := hc.exists_isStrandPath_of_isStrandPath_cut hX.toIsPreTripleDiagram
    hQ.isStrandPath
  exact ⟨Q', rfl, hc.isMonogon_of_isMonogon_cut hX.toIsPreTripleDiagram hQ⟩

/-- **Hollow monogons of the inside**: a hollow monogon of `X|_M` is `{d}` for an inside dart `d`,
and `{d}` is a hollow monogon of `X`. -/
@[cluster_algebras "lem_monogon_cut_features"]
theorem IsConvexMonogon.exists_isHollowMonogon_of_isHollowMonogon_monogonCut
    {f : Finset (CutDart (X.insideDarts P ζ h) (X.insideList ζ P).length)}
    (hf : (X.monogonCut P ζ h).IsHollowMonogon f) :
    ∃ d : {d // d ∈ X.insideDarts P ζ h}, f = {Sum.inl d} ∧ X.IsHollowMonogon {d.1} := by
  have hc := hM.isCutData_insideDarts hX hh
  have hinv := hX.inv_involutive
  obtain ⟨hfI, hcard⟩ := hf
  obtain ⟨hfF, hdisj⟩ := (X.monogonCut P ζ h).mem_internalFaces.1 hfI
  obtain ⟨x, rfl⟩ := card_eq_one.1 hcard
  obtain ⟨y, hy⟩ := (X.monogonCut P ζ h).mem_faceOrbits.1 ((X.monogonCut P ζ h).mem_faces.1 hfF).2
  have hxf : (X.monogonCut P ζ h).faceOf x = {x} := by
    rw [← hy]
    exact (X.monogonCut P ζ h).faceOf_eq_of_mem (by rw [hy]; exact mem_singleton_self x)
  have hφ : (X.monogonCut P ζ h).facePerm x = x := by
    have := (X.monogonCut P ζ h).facePerm_mem_faceOf x
    rwa [hxf, mem_singleton] at this
  rcases x with d | p
  · refine ⟨d, rfl, ?_⟩
    by_cases hL : X.inv d.1 ∈ X.insideList ζ P
    · obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hL
      have := hc.cut_facePerm_inl_of_eq (s := ζ.cutShift) hinv d ⟨k, hk⟩ hkd.symm
      change (X.cut _ _ ζ.cutShift).facePerm (.inl d) = .inl d at hφ
      rw [this] at hφ
      exact absurd hφ (by simp)
    · have := hc.cut_facePerm_inl_of_notMem (s := ζ.cutShift) hinv d hL
      change (X.cut _ _ ζ.cutShift).facePerm (.inl d) = .inl d at hφ
      rw [this] at hφ
      exact X.isHollowMonogon_singleton (hc.notMem_bdry _ d.2)
        (congrArg Subtype.val (Sum.inl_injective hφ))
  · exfalso
    exact disjoint_left.1 hdisj (mem_singleton_self _) (IsCutData.mem_cut_bdry.2 rfl)

/-- **Arcs of the inside**: every arc of `X|_M` (for `m ≥ 2`) consists of inside darts, and these
form a returning path of `M` on its inside `ζ`. -/
@[cluster_algebras "lem_monogon_cut_features"]
theorem IsConvexMonogon.exists_isReturningPath_arc_monogonCut (hm : 2 ≤ P.length)
    (j : Fin ((X.insideList ζ P).length / 2)) :
    ∃ Q : List {d // d ∈ X.insideDarts P ζ h}, Q.map Sum.inl = (X.monogonCut P ζ h).arc j ∧
      ∃ a c, X.IsReturningPath P ζ (Q.map Subtype.val) a c := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  have hc := hM.isCutData_insideDarts hX hh
  have hY := hM.isTripleDiagram_monogonCut hX hh hm
  have hA := (X.monogonCut P ζ h).isStrandPath_arc hY.toIsPreTripleDiagram
    (hY.toIsPreTripleDiagram.arcLength_ne_zero j)
  obtain ⟨Q, hQ, hQX⟩ := hc.exists_isStrandPath_of_isStrandPath_cut (s := ζ.cutShift) hpre hA
  have hne : Q ≠ [] := fun h' => hQX.ne_nil (by rw [h']; rfl)
  obtain ⟨hhead, hlast⟩ := hc.mem_list_of_eq_arc_cut (s := ζ.cutShift) hpre hne hQ.symm
  refine ⟨Q, hQ.symm, ?_⟩
  have hne' : Q.map Subtype.val ≠ [] := hQX.ne_nil
  obtain ⟨f, hf⟩ : ∃ f, (Q.map Subtype.val).head? = some f := ⟨_, List.head?_eq_some_head hne'⟩
  obtain ⟨g, hg⟩ : ∃ g, (Q.map Subtype.val).getLast? = some g :=
    ⟨_, List.getLast?_eq_some_getLast hne'⟩
  have hfL := hhead f (by rw [hf]; rfl)
  have hgL := hlast g (by rw [hg]; rfl)
  obtain ⟨k₁, hk₁, rfl⟩ := List.getElem_of_mem hfL
  obtain ⟨k₂, hk₂, hk₂g⟩ := List.getElem_of_mem hgL
  obtain ⟨a, ha, haf⟩ := getElem_sideList ζ hk₁
  obtain ⟨c, hc', hcg⟩ := getElem_sideList ζ hk₂
  refine ⟨a, c, hM.isSimpleStrandPath, hQX, ha, hc', ⟨P[a], by simp, _, by rw [hf]; rfl, haf⟩,
    ⟨P[c], by simp, g, by rw [hg]; rfl, by rw [← hk₂g]; exact hcg⟩, ?_⟩
  -- the interior points of the arc are avoided by `M`
  intro z hz e he
  simp only [interiorPoints, List.mem_map] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  simp only [List.length_dropLast, List.length_map] at hi
  simp only [List.getElem_dropLast, List.getElem_map]
  have hA' : (X.monogonCut P ζ h).IsStrandPath (Q.map Sum.inl) := hQ ▸ hA
  have hstep := List.isChain_iff_getElem.1 hA'.isChain i (by rw [List.length_map]; omega)
  have hrun := hstep.1
  simp only [List.getElem_map] at hrun
  unfold RunsToEndpoint monogonCut at hrun
  rw [hc.cut_inv_inl hinv] at hrun
  obtain ⟨d', hd'L, hd'⟩ := hc.cut_not_isBoundaryVertex_iff.1 hrun
  have hqK : X.inv Q[i].1 ∈ X.insideDarts P ζ h := hc.inv_mem _ Q[i].2
  have hqL : X.inv Q[i].1 ∉ X.insideList ζ P := by
    have : d' = ⟨X.inv Q[i].1, hqK⟩ := (Sum.inl_injective hd').symm
    rwa [this] at hd'L
  obtain ⟨-, hav⟩ := hM.avoids_of_mem_insideDarts hX hh hqK hqL
  refine ⟨hav e he, fun hv => ?_⟩
  obtain ⟨e', he', hv'⟩ := exists_vertexOf_inv_eq' hM.isMonogon he
  exact hav e' he' (hv.trans hv')

end Features

/-! ### Swivel moves inside a convex monogon -/

section SwivelInside

variable {X : TripleData H b} {P : List H} {ζ : StrandSide} {d₁ : H}

/-- Off `x ∪ y`, the powers of the swivel rotation are those of `σ`. -/
private theorem swivelRot_pow_apply_of_notMem' {z : H}
    (hz : z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) (n : ℕ) :
    ((X.swivelMove d₁).rot ^ n) z = (X.rot ^ n) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ' X.rot, Equiv.Perm.mul_apply, swivelMove_rot]
    exact swivelRot_apply_of_notMem
      (notMem_of_mem_vertexOf hz (RotationSystem.rot_pow_apply_mem_vertexOf _ n z))

/-- **A swivel move inside a convex monogon**: at a digon of `X` whose two triple points consist
of inside darts off the inside list, the swivel move keeps `M` a convex monogon with inside `ζ`,
with the same inside list and the same inside darts. -/
private theorem swivelMove_insideDarts (hX : X.IsTripleDiagram) (hM : X.IsConvexMonogon P ζ)
    {h : X.faceOrbits → ℤ} (hh : X.IsMonogonWindingFunction P h) (hD : X.IsDigon (X.faceOf d₁))
    (hU : ∀ z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁),
      z ∈ X.insideDarts P ζ h ∧ z ∉ X.insideList ζ P) :
    (X.swivelMove d₁).IsConvexMonogon P ζ ∧
      (X.swivelMove d₁).insideList ζ P = X.insideList ζ P ∧
      ∀ h₂, (X.swivelMove d₁).IsMonogonWindingFunction P h₂ →
        (X.swivelMove d₁).insideDarts P ζ h₂ = X.insideDarts P ζ h := by
  have hpre := hX.toIsPreTripleDiagram
  have hc := hM.isCutData_insideDarts hX hh
  have hY : (X.swivelMove d₁).IsTripleDiagram := hD.isTripleDiagram_swivelMove hX
  have hYpre := hY.toIsPreTripleDiagram
  have hne := hM.isMonogon.isStrandPath.ne_nil
  set U := X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) with hUdef
  set Y := X.swivelMove d₁ with hYdef
  have hMv : ∀ z, (∃ e ∈ P, X.vertexOf z = X.vertexOf e) → z ∉ U := fun z ⟨e, he, hv⟩ hzU =>
    (hM.avoids_of_mem_insideDarts hX hh (hU z hzU).1 (hU z hzU).2).2 e he hv
  have hPU : ∀ e ∈ P, e ∉ U := fun e he => hMv e ⟨e, he, rfl⟩
  have hPU' : ∀ e ∈ P, X.inv e ∉ U := fun e he => hMv _ (exists_vertexOf_inv_eq' hM.isMonogon he)
  have hv : ∀ z ∉ U, Y.vertexOf z = X.vertexOf z := fun z hz => vertexOf_swivelMove_of_notMem hz
  have hrot : ∀ z ∉ U, Y.rot z = X.rot z := fun z hz => swivelRot_apply_of_notMem hz
  -- the monogon and its side lists
  have hstep : ∀ a ∈ P, ∀ a', Y.StrandStep a a' ↔ X.StrandStep a a' := by
    intro a ha a'
    unfold StrandStep RunsToEndpoint
    rw [swivelMove_inv, hv _ (hPU' a ha), swivelRot_pow_apply_of_notMem' (hPU' a ha)]
    exact Iff.rfl
  have hSP : Y.IsStrandPath P := by
    obtain ⟨hne', hpt, hst⟩ := X.isStrandPath_iff_getElem.1 hM.isMonogon.isStrandPath
    exact Y.isStrandPath_iff_getElem.2 ⟨hne', hpt,
      fun t ht => (hstep _ (List.getElem_mem _) _).2 (hst t ht)⟩
  have hhead : Y.vertexOf (P.head hne) = X.vertexOf (P.head hne) := hv _ (hPU _ (List.head_mem hne))
  have hstart : Y.pathStart P = X.pathStart P := by
    rw [Y.pathStart_of_head? (List.head?_eq_some_head hne),
      X.pathStart_of_head? (List.head?_eq_some_head hne), hhead]
  have hend : Y.pathEnd P = X.pathEnd P := by
    rw [Y.pathEnd_of_getLast? (List.getLast?_eq_some_getLast hne),
      X.pathEnd_of_getLast? (List.getLast?_eq_some_getLast hne), swivelMove_inv,
      hv _ (hPU' _ (List.getLast_mem hne))]
  have hint : Y.interiorPoints P = X.interiorPoints P := by
    unfold interiorPoints
    rw [swivelMove_inv]
    exact List.map_congr_left fun e he => hv _ (hPU' e (List.dropLast_subset _ he))
  have hMono : Y.IsMonogon P := by
    refine ⟨hSP, ?_, by rw [hend, hstart]; exact hM.isMonogon.pathEnd_eq, ?_⟩
    · have h1 := hM.isMonogon.pathStart_mem
      rw [X.pathStart_of_head? (List.head?_eq_some_head hne),
        X.vertexOf_mem_internalVertices] at h1
      rw [Y.pathStart_of_head? (List.head?_eq_some_head hne), Y.vertexOf_mem_internalVertices,
        hhead]
      exact h1
    · intro e₁ he₁ eₘ heₘ
      rw [swivelMove_inv, swivelRot_pow_apply_of_notMem' (hPU e₁ (List.mem_of_mem_head? he₁))]
      exact hM.isMonogon.inv_ne e₁ he₁ eₘ heₘ
  have hSimple : Y.IsSimpleStrandPath P := by
    obtain ⟨-, h2, h3, h4⟩ := X.isSimpleStrandPath_iff.1 hM.isSimpleStrandPath
    exact Y.isSimpleStrandPath_iff.2 ⟨hSP, by rwa [hint], by rwa [hint, hstart],
      by rwa [hint, hend]⟩
  have hcorner : ∀ e₁ ∈ P.head?, ∀ eₘ ∈ P.getLast?, Y.IsInsideCorner ζ e₁ eₘ := by
    intro e₁ he₁ eₘ heₘ
    have := hM.isInsideCorner e₁ he₁ eₘ heₘ
    have he₁P := List.mem_of_mem_head? he₁
    have heₘP := List.mem_of_mem_getLast? heₘ
    cases ζ
    · change Y.rot (Y.inv eₘ) = e₁
      rw [swivelMove_inv, hrot _ (hPU' eₘ heₘP)]
      exact this
    · change Y.rot e₁ = Y.inv eₘ
      rw [swivelMove_inv, hrot _ (hPU e₁ he₁P)]
      exact this
  have hside : Y.sideList ζ P = X.sideList ζ P := by
    have hsd : ∀ ζ', ∀ e ∈ P, Y.sideDarts ζ' e = X.sideDarts ζ' e := by
      intro ζ' e he
      have hYinv : Y.inv = X.inv := rfl
      have hYpow : ∀ n, (Y.rot ^ n) (X.inv e) = (X.rot ^ n) (X.inv e) :=
        swivelRot_pow_apply_of_notMem' (hPU' e he)
      cases ζ'
      · simp only [sideDarts, hYinv]
        rw [hYpow, hrot _ (hPU' e he)]
      · simp only [sideDarts, hYinv]
        rw [hYpow, hYpow]
    cases ζ
    · exact List.flatMap_congr fun e he => hsd _ e (List.dropLast_subset _ he)
    · exact List.flatMap_congr fun e he =>
        hsd _ e (List.dropLast_subset _ (List.mem_reverse.1 he))
  -- the new triple points
  have hYvU : ∀ z ∈ U, Y.vertexOf z ⊆ U ∧ ¬Y.IsBoundaryVertex (Y.vertexOf z) := fun z hz =>
    ⟨(hD.vertexOf_swivelMove_of_mem hpre hz).1, (hD.vertexOf_swivelMove_of_mem hpre hz).2.1⟩
  have hoff : ∀ z ∈ U, ∀ e ∈ P, Y.vertexOf z ≠ Y.vertexOf e := fun z hz e he hve =>
    hPU e he ((hYvU z hz).1 (hve ▸ Y.self_mem_vertexOf e))
  have hpowC : ∀ C : Set H, Y.IsClosedOff P C → ∀ z ∈ C, ¬Y.IsBoundaryVertex (Y.vertexOf z) →
      (∀ e ∈ P, Y.vertexOf z ≠ Y.vertexOf e) → ∀ n, (Y.rot ^ n) z ∈ C := by
    intro C hC z hz hb hoffz n
    induction n with
    | zero => exact hz
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (hC.2 _ ih (by rwa [Y.vertexOf_rot_pow_apply]) (by rwa [Y.vertexOf_rot_pow_apply])).1
  have hvsub : ∀ C : Set H, Y.IsClosedOff P C → ∀ z ∈ C, z ∈ U → ∀ w ∈ Y.vertexOf z, w ∈ C := by
    intro C hC z hz hzU w hw
    obtain ⟨n, rfl⟩ := (Y.mem_vertexOf.1 hw).exists_nat_pow_eq
    exact hpowC C hC z hz (hYvU z hzU).2 (hoff z hzU) n
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, -, -, hV₁, hV₂, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, hW₁, hW₂⟩ := hD.exists_swivel hpre
  have hfill : ∀ C : Set H, Y.IsClosedOff P C → ∀ u ∈ C, u ∈ U → ∀ z ∈ U, z ∈ C := by
    intro C hC u hu huU
    have hd₁U : d₁ ∈ U := mem_union_left _ (X.self_mem_vertexOf d₁)
    have hd₂U : X.facePerm d₁ ∈ U := mem_union_right _ (X.self_mem_vertexOf _)
    have hi₁U : X.inv d₁ ∈ U := mem_union_right _ (by rw [hV₂]; simp)
    have hi₂U : X.inv (X.facePerm d₁) ∈ U := mem_union_left _ (by rw [hV₁]; simp)
    have hx'y' : (∀ w ∈ Y.vertexOf d₁, w ∈ C) ∧ ∀ w ∈ Y.vertexOf (X.facePerm d₁), w ∈ C := by
      rcases hD.vertexOf_swivelMove_eq_or hpre huU with h' | h'
      · have hx' : ∀ w ∈ Y.vertexOf d₁, w ∈ C := fun w hw => hvsub C hC u hu huU w (h' ▸ hw)
        have hi₁ : X.inv d₁ ∈ C := hC.1 _ (hx' d₁ (Y.self_mem_vertexOf d₁))
        have e : Y.vertexOf (X.inv d₁) = Y.vertexOf (X.facePerm d₁) :=
          Y.vertexOf_eq_of_mem (by rw [hW₂]; simp)
        exact ⟨hx', fun w hw => hvsub C hC _ hi₁ hi₁U w (e ▸ hw)⟩
      · have hy' : ∀ w ∈ Y.vertexOf (X.facePerm d₁), w ∈ C := fun w hw =>
          hvsub C hC u hu huU w (h' ▸ hw)
        have hi₂ : X.inv (X.facePerm d₁) ∈ C := hC.1 _ (hy' _ (Y.self_mem_vertexOf _))
        have e : Y.vertexOf (X.inv (X.facePerm d₁)) = Y.vertexOf d₁ :=
          Y.vertexOf_eq_of_mem (by rw [hW₁]; simp)
        exact ⟨fun w hw => hvsub C hC _ hi₂ hi₂U w (e ▸ hw), hy'⟩
    intro z hz
    rcases hD.vertexOf_swivelMove_eq_or hpre hz with h' | h'
    · exact hx'y'.1 z (h' ▸ Y.self_mem_vertexOf z)
    · exact hx'y'.2 z (h' ▸ Y.self_mem_vertexOf z)
  -- the inside darts are closed off `M` in the swivel move
  have hKrot : ∀ d ∈ X.insideDarts P ζ h, (∀ e ∈ P, Y.vertexOf d ≠ Y.vertexOf e) →
      Y.rot d ∈ X.insideDarts P ζ h := by
    intro d hd hoffd
    by_cases hdU : d ∈ U
    · exact (hU _ ((hYvU d hdU).1 (Y.rot_mem_vertexOf d))).1
    · rw [hrot d hdU]
      refine hc.rot_mem hd fun hL => ?_
      obtain ⟨e, he, hve⟩ := exists_vertexOf_eq_of_mem_insideList hM.isMonogon.isStrandPath hL
      exact hoffd e he (by rw [hv d hdU, hv e (hPU e he)]; exact hve)
  have hKY : Y.IsClosedOff P (X.insideDarts P ζ h : Set H) := by
    refine ⟨fun d hd => hc.inv_mem d hd, fun d hd hb hoffd => ⟨hKrot d hd hoffd, ?_⟩⟩
    have hpowK : ∀ n, (Y.rot ^ n) d ∈ X.insideDarts P ζ h := by
      intro n
      induction n with
      | zero => exact hd
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hKrot _ ih (by rwa [Y.vertexOf_rot_pow_apply])
    have e5 : Y.rot.symm d = (Y.rot ^ 5) d := by
      rw [Equiv.symm_apply_eq]
      exact (rot_rot_pow_five hYpre hb).symm
    rw [e5]
    exact hpowK 5
  have hLK : {d | d ∈ X.insideList ζ P} ⊆ (X.insideDarts P ζ h : Set H) := fun d hd =>
    hc.mem_of_mem_list d hd
  have hsubK := Y.avoidingClosure_subset hLK hKY
  have hKb : ∀ d ∈ X.insideDarts P ζ h, ¬Y.IsBoundaryVertex (Y.vertexOf d) := fun d hd hb =>
    hM.notMem_insideDarts_of_isBoundaryVertex hX hh
      ((hD.isBoundaryVertex_swivelMove_iff hpre d).1 hb) hd
  have hMY : Y.IsConvexMonogon P ζ :=
    isConvexMonogon_of_avoidingClosure hY hMono hSimple hcorner fun d hd =>
      hKb d (hsubK (by rwa [hside] at hd))
  refine ⟨hMY, hside, fun h₂ hh₂ => ?_⟩
  have e2 := hMY.insideDarts_eq_avoidingClosure hY hh₂
  simp only [insideList, hside] at e2
  -- the closure in the swivel move is closed off `M` in `X`
  set C₂ := Y.avoidingClosure P {d | d ∈ X.sideList ζ P} with hC₂def
  have hC₂ := Y.isClosedOff_avoidingClosure P {d | d ∈ X.sideList ζ P}
  have hC₂X : X.IsClosedOff P C₂ := by
    refine ⟨fun d hd => hC₂.1 d hd, fun d hd hb hoffd => ?_⟩
    by_cases hdU : d ∈ U
    · have hall := hfill C₂ hC₂ d hd hdU
      exact ⟨hall _ (rot_mem_union_vertexOf_iff.2 hdU),
        hall _ (rot_mem_union_vertexOf_iff.1 (by rwa [Equiv.apply_symm_apply]))⟩
    · have hb' : ¬Y.IsBoundaryVertex (Y.vertexOf d) := by rw [hv d hdU]; exact hb
      have hoff' : ∀ e ∈ P, Y.vertexOf d ≠ Y.vertexOf e := fun e he => by
        rw [hv d hdU, hv e (hPU e he)]; exact hoffd e he
      obtain ⟨h1, h2⟩ := hC₂.2 d hd hb' hoff'
      refine ⟨by rwa [hrot d hdU] at h1, ?_⟩
      have hsU : X.rot.symm d ∉ U := fun hs => hdU (by
        have := rot_mem_union_vertexOf_iff.2 hs
        rwa [Equiv.apply_symm_apply] at this)
      have e : Y.rot.symm d = X.rot.symm d := by
        rw [Equiv.symm_apply_eq, hrot _ hsU, Equiv.apply_symm_apply]
      rwa [e] at h2
  have hKC₂ : (X.insideDarts P ζ h : Set H) ⊆ C₂ := by
    rw [hM.insideDarts_eq_avoidingClosure hX hh]
    exact X.avoidingClosure_subset (Y.subset_avoidingClosure P _) hC₂X
  apply Finset.coe_injective
  rw [e2]
  exact Set.Subset.antisymm hsubK hKC₂

end SwivelInside

end TripleData

/-! ### Moves of the inside lift -/

namespace TripleData

section Lift

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {P : List H}
  {ζ : StrandSide} {h : X.faceOrbits → ℤ}

omit [Fintype H] in
/-- The cut along `(K', L')`, for `K' = K` and `L' = L`, transported to `L.length / 2` arcs, is
isomorphic to whatever the cut along `(K, L)` is isomorphic to. -/
private theorem isomorphic_cut_congr {Y : TripleData H b} {K K' : Finset H} {L L' : List H}
    {s : ℕ} (hK : K' = K) (hL : L' = L) {H'' : Type} [Fintype H''] [DecidableEq H'']
    {Z : TripleData H'' (L.length / 2)} (h : (Y.cut K L s).Isomorphic Z) :
    ∃ hN : L'.length / 2 = L.length / 2,
      (hN ▸ Y.cut K' L' s : TripleData (CutDart K' L'.length) (L.length / 2)).Isomorphic Z := by
  subst hK hL
  exact ⟨rfl, h⟩

/-- The invariant of the lifting induction: `X'` is reached from `X` by swivel moves, has the data
of `X` except for the rotation, which agrees with `σ` off the inside darts outside the inside
list, `M` is a convex monogon of `X'` with inside `ζ`, the same inside darts and the same inside
list, and the cut of `X'` along them is `W`. -/
private def MonogonLiftInvariant (X : TripleData H b) (P : List H) (ζ : StrandSide)
    (h : X.faceOrbits → ℤ)
    (W : TripleData (CutDart (X.insideDarts P ζ h) (X.insideList ζ P).length)
      ((X.insideList ζ P).length / 2)) (X' : TripleData H b) : Prop :=
  Relation.ReflTransGen SwivelStep X X' ∧ X'.inv = X.inv ∧ X'.bdry = X.bdry ∧
    X'.endDart = X.endDart ∧ X'.isOut = X.isOut ∧
    (∀ d, (d ∉ X.insideDarts P ζ h ∨ d ∈ X.insideList ζ P) → X'.rot d = X.rot d) ∧
    X'.IsConvexMonogon P ζ ∧
    (∀ h', X'.IsMonogonWindingFunction P h' → X'.insideDarts P ζ h' = X.insideDarts P ζ h) ∧
    X'.insideList ζ P = X.insideList ζ P ∧
    W = X'.cut (X.insideDarts P ζ h) (X.insideList ζ P) ζ.cutShift

/-- One swivel move of the inside lifts to a swivel move of the diagram. -/
private theorem MonogonLiftInvariant.step (hX : X.IsTripleDiagram)
    {W W' : TripleData (CutDart (X.insideDarts P ζ h) (X.insideList ζ P).length)
      ((X.insideList ζ P).length / 2)} {X₁ : TripleData H b}
    (hI : MonogonLiftInvariant X P ζ h W X₁) (hst : W.SwivelStep W') :
    ∃ X₂, MonogonLiftInvariant X P ζ h W' X₂ := by
  obtain ⟨hch, hinv, hbdry, hend, hout, hrot, hM₁, hK₁, hL₁, rfl⟩ := hI
  have hX₁ : X₁.IsTripleDiagram := isTripleDiagram_of_reflTransGen_swivelStep hch hX
  obtain ⟨h₁, hh₁, -⟩ :=
    existsUnique_isMonogonWindingFunction hX₁ hM₁.isMonogon hM₁.isSimpleStrandPath
  have hc₁ : X₁.IsCutData (X.insideDarts P ζ h) (X.insideList ζ P) := by
    have := hM₁.isCutData_insideDarts hX₁ hh₁
    rwa [hK₁ h₁ hh₁, hL₁] at this
  obtain ⟨e, hD, rfl⟩ := hst
  rcases e with e | p
  swap
  · exfalso
    have hdisj := ((X₁.cut _ _ ζ.cutShift).mem_internalFaces.1 hD.1).2
    exact disjoint_left.1 hdisj ((X₁.cut _ _ ζ.cutShift).self_mem_faceOf _)
      (IsCutData.mem_cut_bdry.2 rfl)
  obtain ⟨h₂, -, he1, he2, -, hDX⟩ := hc₁.isDigon_of_isDigon_cut hX₁.toIsPreTripleDiagram hD
  have hcut := hc₁.swivelMove_cut hX₁.toIsPreTripleDiagram hD
  have hUK : ∀ z ∈ X₁.vertexOf e.1 ∪ X₁.vertexOf (X₁.facePerm e.1),
      z ∈ X.insideDarts P ζ h ∧ z ∉ X.insideList ζ P := by
    intro z hz
    rcases mem_union.1 hz with hz | hz
    · exact hc₁.mem_of_mem_vertexOf _ e.2 he1 z hz
    · exact hc₁.mem_of_mem_vertexOf _ h₂ he2 z hz
  have hUK₁ : ∀ z ∈ X₁.vertexOf e.1 ∪ X₁.vertexOf (X₁.facePerm e.1),
      z ∈ X₁.insideDarts P ζ h₁ ∧ z ∉ X₁.insideList ζ P := fun z hz => by
    rw [hK₁ h₁ hh₁, hL₁]
    exact hUK z hz
  obtain ⟨hM₂, hL₂, hK₂⟩ := swivelMove_insideDarts hX₁ hM₁ hh₁ hDX hUK₁
  refine ⟨X₁.swivelMove e.1, hch.tail ⟨e.1, hDX, rfl⟩, hinv, hbdry, hend, hout, fun d hd => ?_,
    hM₂, fun h' hh' => (hK₂ h' hh').trans (hK₁ h₁ hh₁), hL₂.trans hL₁, hcut.symm⟩
  have hdU : d ∉ X₁.vertexOf e.1 ∪ X₁.vertexOf (X₁.facePerm e.1) := fun hdU => by
    obtain ⟨h1, h2⟩ := hUK d hdU
    rcases hd with hd | hd
    · exact hd h1
    · exact h2 hd
  rw [swivelMove_rot, swivelRot_apply_of_notMem hdU]
  exact hrot d hd

/-- **Moves of the inside lift**. Let `M` be a convex monogon with inside `ζ` and `m ≥ 2` of a
triple diagram `X = (H, d ↦ d̄, σ, B, ε, o)`, `h` its winding function, and `Y ∼ X|_M`. Then there
is a triple diagram `X' = (H, d ↦ d̄, σ', B, ε, o) ∼ X` such that `σ'(d) = σ(d)` for every dart
`d` that does not lie at a triple point of `X` avoided by `M`, `M` is a convex monogon of `X'`
with inside `ζ`, the inside darts `H_in(M)` of `X'` (for its winding function `h'`) are those of
`X`, and `X'|_M` is isomorphic to `Y` (after identifying their numbers of arcs, which are
equal). -/
@[cluster_algebras "lem_monogon_cut_lift"]
theorem IsConvexMonogon.exists_moveEquivalent_monogonCut (hX : X.IsTripleDiagram)
    (hM : X.IsConvexMonogon P ζ) (hh : X.IsMonogonWindingFunction P h) (hm : 2 ≤ P.length)
    {Y : TripleDiagram ((X.insideList ζ P).length / 2)}
    (hY : TripleDiagram.MoveEquivalent
      ⟨_, X.monogonCut P ζ h, hM.isTripleDiagram_monogonCut hX hh hm⟩ Y) :
    ∃ (X' : TripleData H b) (hX' : X'.IsTripleDiagram),
      TripleDiagram.MoveEquivalent ⟨H, X, hX⟩ ⟨H, X', hX'⟩ ∧
      X'.inv = X.inv ∧ X'.bdry = X.bdry ∧ X'.endDart = X.endDart ∧ X'.isOut = X.isOut ∧
      (∀ d, ¬(X.vertexOf d ∈ X.internalVertices ∧ ∀ e ∈ P, X.vertexOf d ≠ X.vertexOf e) →
        X'.rot d = X.rot d) ∧
      X'.IsConvexMonogon P ζ ∧
      ∃ h' : X'.faceOrbits → ℤ, X'.IsMonogonWindingFunction P h' ∧
        X'.insideDarts P ζ h' = X.insideDarts P ζ h ∧
        ∃ hN : (X'.insideList ζ P).length / 2 = (X.insideList ζ P).length / 2,
          (hN ▸ X'.monogonCut P ζ h' : TripleData
            (CutDart (X'.insideDarts P ζ h') (X'.insideList ζ P).length)
            ((X.insideList ζ P).length / 2)).Isomorphic Y.data := by
  obtain ⟨W, hW, hWY⟩ := hY.exists_swivelSteps
  have key : ∀ W', Relation.ReflTransGen SwivelStep (X.monogonCut P ζ h) W' →
      ∃ X₁, MonogonLiftInvariant X P ζ h W' X₁ := by
    intro W' hW'
    induction hW' with
    | refl =>
      refine ⟨X, Relation.ReflTransGen.refl, rfl, rfl, rfl, rfl, fun _ _ => rfl, hM,
        fun h' hh' => ?_, rfl, rfl⟩
      rw [DiskMap.IsWindingFunction.unique hX.toIsDiskMap hh' hh]
    | tail _ hst ih =>
      obtain ⟨X₁, h₁⟩ := ih
      exact h₁.step hX hst
  obtain ⟨X', hch, hinv, hbdry, hend, hout, hrot, hM', hK', hL', rfl⟩ := key W hW
  have hX' : X'.IsTripleDiagram := isTripleDiagram_of_reflTransGen_swivelStep hch hX
  obtain ⟨h', hh', -⟩ :=
    existsUnique_isMonogonWindingFunction hX' hM'.isMonogon hM'.isSimpleStrandPath
  refine ⟨X', hX', TripleDiagram.MoveEquivalent.of_reflTransGen_swivelStep (X := ⟨H, X, hX⟩)
    (X' := ⟨H, X', hX'⟩) hch (Isomorphic.refl _), hinv, hbdry, hend, hout, fun d hd => ?_, hM',
    h', hh', hK' h' hh', isomorphic_cut_congr (hK' h' hh') hL' hWY⟩
  apply hrot
  by_contra hcon
  rw [not_or, not_not] at hcon
  obtain ⟨hb, hav⟩ := hM.avoids_of_mem_insideDarts hX hh hcon.1 hcon.2
  exact hd ⟨X.vertexOf_mem_internalVertices.2 hb, hav⟩

end Lift

end TripleData

end ClusterAlgebras

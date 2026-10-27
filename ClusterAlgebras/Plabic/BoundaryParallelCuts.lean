/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BoundaryParallel
public import ClusterAlgebras.Plabic.MonogonCut
public import ClusterAlgebras.Plabic.ClosedStrands

/-!
# Cuts along boundary-parallel arcs

Let `X` be a triple diagram and `S` the arc from `s_i`, boundary-parallel along an interval `I` of
`i`: `S` is simple, passes through `k` triple points, and the `2k` legs at the interior positions
of `I` run straight to the points of `S`. This file collects the facts on cuts used in Thurston's
straightening argument.

* The cut `X|_{S,η}` on the side `η` opposite to `I` determines `X`: a diagram `X'` with the same
  `π(i)` whose arc from `s_i` is boundary-parallel along `I` and whose cut is isomorphic to that of
  `X` is isomorphic to `X`. The isomorphism is the given one on the darts of `H_η(S)` and is forced
  on the darts at the points of `S` and at the endpoints, which are named by the same coordinates
  in `X` and `X'`.
* The strand permutation of the cut is determined by `π_X`, `i` and `I`: every leg of the cut sits
  at a position of `X` (a leg `n_r` at a position on side `η`, or the dart `σ³ n̄_r` at a point of
  `S`, for `r` interior to `I`), and an arc of the cut from the leg of `s_j` ends at the leg of
  `t_{π(j)}`.
* An arc of a cut along a simple arc, or of the inside of a convex monogon, that is a returning
  path and is boundary-parallel along the interval spanned by the darts of the side list between
  its ends hugs the arc, respectively the monogon.
* In the combing step, a strand boundary-parallel in the (possibly nested) cut produces an aligned
  or a staggered rail along `S`.

## Main results

* `ClusterAlgebras.TripleData.IsBoundaryParallel.isomorphic_of_hIsomorphic_arcCut`: gluing along a
  boundary-parallel arc.
* `ClusterAlgebras.TripleData.IsSimpleArc.hugs_of_isBoundaryParallel_arcCut`: a boundary-parallel
  returning arc hugs.
* `ClusterAlgebras.TripleData.IsBoundaryParallel.arcCut_strandPerm_eq`: the cut along a
  boundary-parallel arc has a determined strand permutation.
* `ClusterAlgebras.TripleData.IsSimpleArc.exists_rail_of_isBoundaryParallel_arcCut`,
  `ClusterAlgebras.TripleData.IsSimpleArc.exists_rail_of_isBoundaryParallel_arcCut_arcCut`: a
  boundary-parallel strand in the nested cut gives a rail, for `t = 0` and for `t ≥ 1`.
* `ClusterAlgebras.TripleData.IsConvexMonogon.hugs_of_isBoundaryParallel_monogonCut`: a
  boundary-parallel arc of the inside hugs.

## Implementation notes

* Labels are `0`-indexed, as everywhere in the formalization: the arc label `i : Fin b` is
  FWZ's `i + 1`, a position `r : Fin (2 * b)` is FWZ's `r + 1`, and the darts of an arc,
  the entries of a cut list and the entries of a side list are numbered from `0`.
* The darts of a cut are the `Sum.inl d` over the darts `d` of the diagram, and its endpoint
  `ε'(r)` carries the entry `(r + s) mod N` of the cut list (`TripleData.cut`); an arc of a cut is
  given as a list `Q` of darts of the side with `Q.map Sum.inl` the arc. The interval of an arc of
  a cut is described through the legs at its interior positions.
* Cuts with numbers of arcs that are equal only as numbers are compared by `HIsomorphic`.
* In the rail lemma, `Y₂` is `X|_{S,ζ}` when `t = 0` and a cut of `X|_{S,ζ}` when `t ≥ 1`; these
  cuts have different types of darts, so the lemma is stated by two theorems. The side `θ` of the
  single dart `A` containing the position of `g_t` is given as the side containing the leg `g_t`
  (a leg lies on the side of its position).
* Some of FWZ's hypotheses are not needed and are omitted: `N_η ≥ 2` in
  `IsBoundaryParallel.isomorphic_of_hIsomorphic_arcCut`; `b ≥ 2` and the minimality of `I` in
  `IsBoundaryParallel.arcCut_strandPerm_eq`; the minimality of `I` and the absence of returning
  paths in `IsSimpleArc.exists_rail_of_isBoundaryParallel_arcCut` and
  `IsSimpleArc.exists_rail_of_isBoundaryParallel_arcCut_arcCut`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Clockwise rotations of positions -/

section Rotations

private theorem val_finRotate_pow' {n : ℕ} (a : Fin n) (k : ℕ) :
    ((finRotate n ^ k) a : ℕ) = ((a : ℕ) + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt a.isLt]
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    have hn : 0 < n := Fin.pos a
    haveI : NeZero n := ⟨by omega⟩
    rw [finRotate_apply, Fin.val_add, ih, Fin.val_one', Nat.add_mod_mod, Nat.mod_add_mod,
      add_assoc]

private theorem finRotate_pow_val_sub' {n : ℕ} (a c : Fin n) :
    (finRotate n ^ ((c - a : Fin n) : ℕ)) a = c := by
  apply Fin.ext
  rw [val_finRotate_pow', Fin.sub_def]
  simp only
  have ha := a.isLt
  have hc := c.isLt
  rw [Nat.add_mod_mod, show (a : ℕ) + (n - a + c) = n + c by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt hc]

end Rotations

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

/-- If `Q.map f` is the arc from `s_j`, then its `l`-th dart is `f Q[l]`. -/
theorem arcDart_eq_of_map_eq_arc {α : Type*} {Y : TripleData H b} {f : α → H} {Q : List α}
    {j : Fin b} (hQ : Q.map f = Y.arc j) {l : ℕ} (hl : l < Q.length) :
    Y.arcDart j l = f Q[l] := by
  have h1 : (Y.arc j)[l]? = some (Y.arcDart j l) := by
    rw [List.getElem?_eq_getElem (by rw [← hQ, List.length_map]; exact hl), getElem_arc]
  rw [← hQ, List.getElem?_map, List.getElem?_eq_getElem hl] at h1
  exact (Option.some_injective _ h1).symm

/-! ### Side lists of strand paths -/

section SideLists

variable {X : TripleData H b}

omit [Fintype H] [DecidableEq H] in
private theorem length_flatMap_pair' {α β : Type*} (A : List α) (f g : α → β) :
    (A.flatMap fun a => [f a, g a]).length = 2 * A.length := by
  induction A with
  | nil => simp
  | cons a A ih => simp [List.flatMap_cons, ih]; ring

omit [Fintype H] [DecidableEq H] in
private theorem getElem_flatMap_pair' {α β : Type*} (A : List α) (f g : α → β) (k : ℕ)
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

omit [Fintype H] [DecidableEq H] in
private theorem length_sideList' (ζ : StrandSide) (P : List H) :
    (X.sideList ζ P).length = 2 * (P.length - 1) := by
  cases ζ
  · change (P.dropLast.flatMap fun e => [X.rot (X.inv e), (X.rot ^ 2) (X.inv e)]).length = _
    rw [length_flatMap_pair', List.length_dropLast]
  · change (P.dropLast.reverse.flatMap
      fun e => [(X.rot ^ 4) (X.inv e), (X.rot ^ 5) (X.inv e)]).length = _
    rw [length_flatMap_pair', List.length_reverse, List.length_dropLast]

omit [Fintype H] [DecidableEq H] in
private theorem getElem_sideList_right' {P : List H} {k : ℕ}
    (hk : k < (X.sideList .right P).length) :
    (X.sideList .right P)[k] =
      (X.rot ^ (k % 2 + 1)) (X.inv (P[k / 2]'(by rw [length_sideList'] at hk; omega))) := by
  have hk' := hk
  rw [length_sideList'] at hk'
  change (P.dropLast.flatMap fun e => [X.rot (X.inv e), (X.rot ^ 2) (X.inv e)])[k] = _
  rw [getElem_flatMap_pair' _ _ _ _ _ (by rw [List.length_dropLast]; omega),
    List.getElem_dropLast]
  split_ifs with h
  · rw [h, zero_add, pow_one]
  · rw [show k % 2 + 1 = 2 by omega]

omit [Fintype H] [DecidableEq H] in
private theorem getElem_sideList_left' {P : List H} {k : ℕ}
    (hk : k < (X.sideList .left P).length) :
    (X.sideList .left P)[k] =
      (X.rot ^ (k % 2 + 4)) (X.inv (P[P.length - 2 - k / 2]'(by
        rw [length_sideList'] at hk; omega))) := by
  have hk' := hk
  rw [length_sideList'] at hk'
  change (P.dropLast.reverse.flatMap
    fun e => [(X.rot ^ 4) (X.inv e), (X.rot ^ 5) (X.inv e)])[k] = _
  rw [getElem_flatMap_pair' _ _ _ _ _ (by rw [List.length_reverse, List.length_dropLast]; omega),
    List.getElem_reverse, List.getElem_dropLast]
  have e : P.dropLast.length - 1 - k / 2 = P.length - 2 - k / 2 := by
    rw [List.length_dropLast]; omega
  simp only [e]
  split_ifs with h
  · rw [h]
  · rw [show k % 2 + 4 = 5 by omega]

/-- The index `l` of the interior point `z_{l+1}` of a strand path with `m` darts at which the
entry `k` of its `ζ` list lies: `⌊k/2⌋` on the right and `m - 2 - ⌊k/2⌋` on the left. -/
private def sidePoint : StrandSide → ℕ → ℕ → ℕ
  | .right, _, k => k / 2
  | .left, m, k => m - 2 - k / 2

/-- The exponent `e` with entry `k` of the `ζ` list equal to `σ^e(ē_{l+1})`: `k mod 2 + 1` on the
right and `k mod 2 + 4` on the left. -/
private def sideExp : StrandSide → ℕ → ℕ
  | .right, k => k % 2 + 1
  | .left, k => k % 2 + 4

omit [Fintype H] [DecidableEq H] in
private theorem sidePoint_lt {ζ : StrandSide} {P : List H} {k : ℕ}
    (hk : k < (X.sideList ζ P).length) : sidePoint ζ P.length k + 1 < P.length := by
  rw [length_sideList'] at hk
  cases ζ <;> simp only [sidePoint] <;> omega

omit [Fintype H] [DecidableEq H] in
private theorem getElem_sideList' {ζ : StrandSide} {P : List H} {k : ℕ}
    (hk : k < (X.sideList ζ P).length) :
    (X.sideList ζ P)[k] = (X.rot ^ sideExp ζ k)
      (X.inv (P[sidePoint ζ P.length k]'(by have := sidePoint_lt hk; omega))) := by
  cases ζ
  · exact getElem_sideList_right' hk
  · exact getElem_sideList_left' hk

omit [Fintype H] [DecidableEq H] in
/-- A `ζ` dart of a strand path at its interior point `z_{a+1}` is an entry of its `ζ` list lying
at that point. -/
private theorem exists_getElem_sideList_of_mem_sideDarts {P : List H} {ζ : StrandSide} {a : ℕ}
    (ha : a + 1 < P.length) {f : H} (hf : f ∈ X.sideDarts ζ P[a]) :
    ∃ k, ∃ hk : k < (X.sideList ζ P).length, (X.sideList ζ P)[k] = f ∧
      sidePoint ζ P.length k = a := by
  have hl := length_sideList' (X := X) ζ P
  cases ζ
  · simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · refine ⟨2 * a, by omega, ?_, by simp only [sidePoint]; omega⟩
      rw [getElem_sideList_right']
      simp only [show 2 * a % 2 + 1 = 1 by omega, show 2 * a / 2 = a by omega, pow_one]
    · refine ⟨2 * a + 1, by omega, ?_, by simp only [sidePoint]; omega⟩
      rw [getElem_sideList_right']
      simp only [show (2 * a + 1) % 2 + 1 = 2 by omega, show (2 * a + 1) / 2 = a by omega]
  · simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · refine ⟨2 * (P.length - 2 - a), by omega, ?_, by simp only [sidePoint]; omega⟩
      rw [getElem_sideList_left']
      simp only [show 2 * (P.length - 2 - a) % 2 + 4 = 4 by omega,
        show P.length - 2 - 2 * (P.length - 2 - a) / 2 = a by omega]
    · refine ⟨2 * (P.length - 2 - a) + 1, by omega, ?_, by simp only [sidePoint]; omega⟩
      rw [getElem_sideList_left']
      simp only [show (2 * (P.length - 2 - a) + 1) % 2 + 4 = 5 by omega,
        show P.length - 2 - (2 * (P.length - 2 - a) + 1) / 2 = a by omega]

omit [Fintype H] [DecidableEq H] in
private theorem take_drop_getElem?' {α : Type*} (Λ : List α) {i j : ℕ} (hj : j < Λ.length) :
    ((Λ.drop (i + 1)).take (j - i - 1)).length = j - i - 1 ∧
      ∀ t < j - i - 1, ((Λ.drop (i + 1)).take (j - i - 1))[t]? = Λ[i + 1 + t]? := by
  refine ⟨by simp; omega, fun t ht => ?_⟩
  rw [List.getElem?_take_of_lt ht, List.getElem?_drop]

omit [Fintype H] [DecidableEq H] in
private theorem drop_take_reverse_getElem?' {α : Type*} (Λ : List α) {i j : ℕ} (hji : j < i)
    (hi : i < Λ.length) :
    (((Λ.take i).drop (j + 1)).reverse).length = i - j - 1 ∧
      ∀ t < i - j - 1, (((Λ.take i).drop (j + 1)).reverse)[t]? = Λ[i - 1 - t]? := by
  have hl : (((Λ.take i).drop (j + 1)).reverse).length = i - j - 1 := by simp; omega
  refine ⟨hl, fun t ht => ?_⟩
  rw [List.getElem?_reverse (by simp at hl ⊢; omega), List.getElem?_drop,
    List.getElem?_take_of_lt (by simp; omega)]
  congr 1
  simp
  omega

omit [Fintype H] in
/-- The darts `hugDarts` for a path with first dart `f` and last dart `f'`. -/
private theorem hugDarts_eq' {P Q : List H} {ζ : StrandSide} {f f' : H} (hf : Q.head? = some f)
    (hf' : Q.getLast? = some f') :
    X.hugDarts P ζ Q =
      if (X.sideList ζ P).idxOf f < (X.sideList ζ P).idxOf (X.inv f') then
        ((X.sideList ζ P).drop ((X.sideList ζ P).idxOf f + 1)).take
          ((X.sideList ζ P).idxOf (X.inv f') - (X.sideList ζ P).idxOf f - 1)
      else (((X.sideList ζ P).take ((X.sideList ζ P).idxOf f)).drop
        ((X.sideList ζ P).idxOf (X.inv f') + 1)).reverse := by
  simp only [hugDarts, hf, hf']

/-- The first dart `f` of a returning path `Q` of `P` on side `ζ` from `z_{a+1}` to `z_{c+1}` and
the reverse `f̄'` of its last dart are entries `k₁ ≠ k₂` of the `ζ` list, and `f` comes first
exactly when `νs = -1`: the right list follows the points of `P` in increasing order with the
`out` dart first at each point, the left list in decreasing order with the `out` dart second. -/
private theorem exists_indices_of_isReturningPath (hX : X.IsPreTripleDiagram) {P Q : List H}
    {ζ : StrandSide} {a c : ℕ} (hret : X.IsReturningPath P ζ Q a c) {f f' : H}
    (hf : Q.head? = some f) (hf' : Q.getLast? = some f') :
    ∃ k₁ k₂, ∃ (h₁ : k₁ < (X.sideList ζ P).length) (h₂ : k₂ < (X.sideList ζ P).length),
      (X.sideList ζ P)[k₁] = f ∧ (X.sideList ζ P)[k₂] = X.inv f' ∧ k₁ ≠ k₂ ∧
        (k₁ < k₂ ↔ hugExponent ζ a c = -1) := by
  obtain ⟨e, he, g, hg, hge⟩ := hret.head?_mem
  obtain ⟨e', he', g', hg', hge'⟩ := hret.getLast?_mem
  rw [hf, Option.mem_def, Option.some.injEq] at hg
  rw [hf', Option.mem_def, Option.some.injEq] at hg'
  subst hg hg'
  have ha := hret.lt_left
  have hc := hret.lt_right
  rw [Option.mem_def, List.getElem?_eq_getElem (by omega), Option.some.injEq] at he he'
  subst he he'
  obtain ⟨k₁, hk₁, hk₁f, hk₁a⟩ := exists_getElem_sideList_of_mem_sideDarts ha hge
  obtain ⟨k₂, hk₂, hk₂f, hk₂c⟩ := exists_getElem_sideList_of_mem_sideDarts hc hge'
  have hP := hret.isSimpleStrandPath.isStrandPath
  have hPg := (X.isStrandPath_iff_getElem.1 hP).2
  -- the orientations of `f` (out) and `f̄'` (in)
  have hfo : X.isOut f = true :=
    hret.isStrandPath.isOut_eq_true _
      (List.mem_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hf))
  have hf'o : X.isOut (X.inv f') = false := by
    have hm : f' ∈ Q := List.mem_of_getLast? hf'
    rw [hX.isOut_inv_apply (hret.isStrandPath.notMem_bdry _ hm),
      hret.isStrandPath.isOut_eq_true _ hm]
    rfl
  have horient : ∀ k (hk : k < (X.sideList ζ P).length),
      X.isOut (X.sideList ζ P)[k] = decide (¬Even (sideExp ζ k)) := by
    intro k hk
    have hl := sidePoint_lt hk
    rw [getElem_sideList' hk, hX.isOut_rot_pow_apply (hPg.2 _ hl).1,
      hX.isOut_inv_apply (hPg.1 _ (by omega)).1, (hPg.1 _ (by omega)).2]
    split_ifs with h <;> simp [h]
  have h1 := horient k₁ hk₁
  have h2 := horient k₂ hk₂
  rw [hk₁f, hfo] at h1
  rw [hk₂f, hf'o] at h2
  have hlen := length_sideList' (X := X) ζ P
  refine ⟨k₁, k₂, hk₁, hk₂, hk₁f, hk₂f, ?_⟩
  cases ζ <;> simp only [sideExp, sidePoint] at h1 h2 hk₁a hk₂c <;>
    rcases Nat.mod_two_eq_zero_or_one k₁ with e1 | e1 <;>
    rcases Nat.mod_two_eq_zero_or_one k₂ with e2 | e2 <;>
    simp [e1, e2, Nat.even_iff] at h1 h2 <;>
    simp only [hugExponent, StrandSide.sign_right, StrandSide.sign_left] <;>
    split_ifs with hca <;> constructor <;> (try intro) <;> omega

end SideLists

/-! ### Boundary-parallel arcs of a cut hug -/

section CutHugs

variable {X : TripleData H b}

/-- `σ^{-k}(y) = σ^{6-k}(y)` at a triple point. -/
private theorem rot_zpow_neg' (hX : X.IsPreTripleDiagram) {y : H}
    (hy : ¬X.IsBoundaryVertex (X.vertexOf y)) {k : ℕ} (hk : k ≤ 6) :
    (X.rot ^ (-(k : ℤ))) y = (X.rot ^ (6 - k)) y := by
  conv_lhs => rw [← hX.rot_pow_six_apply hy]
  rw [← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add,
    show -(k : ℤ) + ((6 : ℕ) : ℤ) = ((6 - k : ℕ) : ℤ) by omega, zpow_natCast]

omit [Fintype H] [DecidableEq H] in
private theorem eq_of_getElem?_eq' {α : Type*} {L : List α} (hL : L.Nodup) {x y : ℕ} {d : α}
    (hx : L[x]? = some d) (hy : L[y]? = some d) : x = y := by
  obtain ⟨hx', rfl⟩ := List.getElem?_eq_some_iff.1 hx
  obtain ⟨hy', h⟩ := List.getElem?_eq_some_iff.1 hy
  exact hL.getElem_inj_iff.1 h.symm

private theorem hugExponent_eq_one_or (ζ : StrandSide) (a c : ℕ) :
    hugExponent ζ a c = 1 ∨ hugExponent ζ a c = -1 := by
  cases ζ <;> simp only [hugExponent, StrandSide.sign_right, StrandSide.sign_left] <;>
    split_ifs <;> norm_num

omit [Fintype H] [DecidableEq H] in
/-- The index in the cut list of the leg at the position `t` steps clockwise from `r`. -/
private theorem val_cutEndIndex_finRotate_pow {L : List H} {s : ℕ} (hev : Even L.length)
    (r : Fin (2 * (L.length / 2))) (t : ℕ) :
    (cutEndIndex L s ((finRotate _ ^ t) r) : ℕ) = ((cutEndIndex L s r : ℕ) + t) % L.length := by
  have h2 : 2 * (L.length / 2) = L.length := by obtain ⟨u, hu⟩ := hev; omega
  simp only [cutEndIndex]
  have e : ∀ m, m = L.length → ((r : ℕ) + t) % m = ((r : ℕ) + t) % L.length := by
    rintro m rfl; rfl
  rw [val_finRotate_pow', e _ h2, Nat.mod_add_mod, Nat.mod_add_mod, add_right_comm]

/-- An arc `Q` of a cut `X.cut K L s` along a list `L` ending with the `ζ` list of a simple
strand path `P`, which is a returning path of `P` and is boundary-parallel in the cut along the
interval whose interior positions carry the darts of the `ζ` list strictly between its two ends,
hugs `P`. -/
private theorem hugs_of_isBoundaryParallel_cut (hX : X.IsTripleDiagram) {K : Finset H}
    {L : List H} {s : ℕ} (hc : X.IsCutData K L) (hev : Even L.length)
    (hY : (X.cut K L s).IsTripleDiagram) {P : List H} {ζ : StrandSide} {pre : List H}
    (hL : L = pre ++ X.sideList ζ P) {Q : List {d // d ∈ K}} {j : Fin (L.length / 2)}
    (hQ : Q.map Sum.inl = (X.cut K L s).arc j) {a c : ℕ}
    (hret : X.IsReturningPath P ζ (Q.map Subtype.val) a c)
    {I : Finset (Fin (2 * (L.length / 2)))} (hB : (X.cut K L s).IsBoundaryParallel j I)
    (hI : ∀ r, r ∈ intervalInterior (X.cut K L s).strandPerm j I ↔
      L[(cutEndIndex L s r : ℕ)] ∈ X.hugDarts P ζ (Q.map Subtype.val)) :
    X.Hugs P ζ (Q.map Subtype.val) a c := by
  set Y := X.cut K L s with hYdef
  have hinv := hX.inv_involutive
  have hpre := hX.toIsPreTripleDiagram
  have hYp := hY.toIsPreTripleDiagram
  have h2N : 2 * (L.length / 2) = L.length := by obtain ⟨t, ht⟩ := hev; omega
  set n := Q.length with hn
  have hlen : Y.arcLength j = n := by rw [← length_arc, ← hQ, List.length_map]
  have hn1 : 1 ≤ n := by have := hYp.arcLength_ne_zero j; omega
  -- the darts of the arc
  have hdart : ∀ l (hl : l < n), Y.arcDart j l = .inl Q[l] := fun l hl =>
    arcDart_eq_of_map_eq_arc hQ hl
  have hinvQ : ∀ l (hl : l + 1 < n), X.inv Q[l].1 ∉ L ∧
      Y.inv (Y.arcDart j l) = .inl ⟨X.inv Q[l].1, hc.inv_mem _ Q[l].2⟩ := by
    intro l hl
    have hYi : Y.inv (Y.arcDart j l) = .inl ⟨X.inv Q[l].1, hc.inv_mem _ Q[l].2⟩ := by
      rw [hdart l (by omega), hYdef, hc.cut_inv_inl hinv]
    refine ⟨?_, hYi⟩
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (hYp.arcLength_ne_zero j)
    have h := (Y.arcLength_eq_succ_iff.1 hm).2 l (by omega)
    unfold RunsToEndpoint at h
    rw [hYi] at h
    obtain ⟨d, hdL, hd⟩ := hc.cut_not_isBoundaryVertex_iff.1 h
    rwa [← Sum.inl_injective hd] at hdL
  have hrotQ : ∀ l (hl : l + 1 < n) (k : ℕ), ∃ hm : (X.rot ^ k) (X.inv Q[l].1) ∈ K,
      (Y.rot ^ k) (Y.inv (Y.arcDart j l)) = .inl ⟨(X.rot ^ k) (X.inv Q[l].1), hm⟩ := by
    intro l hl k
    obtain ⟨h1, -, h2⟩ := hc.cut_rot_pow_inl_of_notMem (s := s) ⟨X.inv Q[l].1, hc.inv_mem _ Q[l].2⟩
      (hinvQ l hl).1 k
    exact ⟨h1, by rwa [(hinvQ l hl).2]⟩
  have htripQ : ∀ l (hl : l + 1 < n), ¬X.IsBoundaryVertex (X.vertexOf (X.inv Q[l].1)) :=
    fun l hl => hc.not_isBoundaryVertex _ (hc.inv_mem _ Q[l].2) (hinvQ l hl).1
  -- the legs of the cut
  have hleg : ∀ r, Y.endDart r = .inl ⟨L[(cutEndIndex L s r : ℕ)], hc.getElem_mem _⟩ := by
    intro r
    rw [hYdef, cut_endDart, hc.cutListDart_eq]
  have hlegInv : ∀ r, Y.inv (Y.endDart r) =
      .inl ⟨X.inv L[(cutEndIndex L s r : ℕ)], hc.inv_mem _ (hc.getElem_mem _)⟩ := by
    intro r
    rw [hleg, hYdef, hc.cut_inv_inl hinv]
  -- the two ends of `Q`
  have hlegp : L[(cutEndIndex L s (sourceIndex j) : ℕ)] = Q[0].1 := by
    have h := hleg (sourceIndex j)
    rw [show Y.endDart (sourceIndex j) = Y.arcDart j 0 from rfl, hdart 0 (by omega)] at h
    exact (congrArg Subtype.val (Sum.inl_injective h)).symm
  have hlegq : L[(cutEndIndex L s (Y.arcEndIndex j) : ℕ)] = X.inv Q[n - 1].1 := by
    have h := hleg (Y.arcEndIndex j)
    rw [endDart_arcEndIndex hY j, hlen, hdart (n - 1) (by omega), hYdef,
      hc.cut_inv_inl hinv] at h
    exact (congrArg Subtype.val (Sum.inl_injective h)).symm
  have hhead : (Q.map Subtype.val).head? = some Q[0].1 := by
    rw [List.head?_map, List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    rfl
  have hlast : (Q.map Subtype.val).getLast? = some Q[n - 1].1 := by
    rw [List.getLast?_map, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    rfl
  obtain ⟨k₁, k₂, hk₁, hk₂, hk₁f, hk₂f, hk12, hor⟩ :=
    exists_indices_of_isReturningPath hpre hret hhead hlast
  have hLnd : L.Nodup := hc.nodup
  have hsnd : (X.sideList ζ P).Nodup := by
    have := hLnd
    rw [hL] at this
    exact (List.nodup_append.1 this).2.1
  have hLside : ∀ t (ht : t < (X.sideList ζ P).length),
      L[pre.length + t]? = some (X.sideList ζ P)[t] := by
    intro t ht
    rw [hL, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem ht]
  have hLside' : ∀ t, L[pre.length + t]? = (X.sideList ζ P)[t]? := by
    intro t
    rw [hL, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  have hx₁ : (cutEndIndex L s (sourceIndex j) : ℕ) = pre.length + k₁ := by
    refine eq_of_getElem?_eq' hLnd (d := Q[0].1) ?_ ?_
    · rw [List.getElem?_eq_getElem (cutEndIndex L s (sourceIndex j)).isLt, hlegp]
    · rw [hLside k₁ hk₁, hk₁f]
  have hx₂ : (cutEndIndex L s (Y.arcEndIndex j) : ℕ) = pre.length + k₂ := by
    refine eq_of_getElem?_eq' hLnd (d := X.inv Q[n - 1].1) ?_ ?_
    · rw [List.getElem?_eq_getElem (cutEndIndex L s (Y.arcEndIndex j)).isLt, hlegq]
    · rw [hLside k₂ hk₂, hk₂f]
  have hLlen : pre.length + (X.sideList ζ P).length = L.length := by
    rw [hL, List.length_append]
  -- the darts `J` strictly between the two ends
  have hJ : X.hugDarts P ζ (Q.map Subtype.val) =
      if k₁ < k₂ then ((X.sideList ζ P).drop (k₁ + 1)).take (k₂ - k₁ - 1)
      else (((X.sideList ζ P).take k₁).drop (k₂ + 1)).reverse := by
    rw [hugDarts_eq' hhead hlast]
    have e1 : (X.sideList ζ P).idxOf Q[0].1 = k₁ := by
      rw [← hk₁f]; exact hsnd.idxOf_getElem _ _
    have e2 : (X.sideList ζ P).idxOf (X.inv Q[n - 1].1) = k₂ := by
      rw [← hk₂f]; exact hsnd.idxOf_getElem _ _
    rw [e1, e2]
  have hJnd : (X.hugDarts P ζ (Q.map Subtype.val)).Nodup := by
    rw [hJ]
    split_ifs
    · exact hsnd.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
    · exact List.nodup_reverse.2 (hsnd.sublist ((List.drop_sublist _ _).trans
        (List.take_sublist _ _)))
  have hJsub : ∀ d ∈ X.hugDarts P ζ (Q.map Subtype.val), d ∈ L := by
    intro d hd
    rw [hJ] at hd
    rw [hL]
    refine List.mem_append_right _ ?_
    split_ifs at hd
    · exact (List.drop_subset _ _) ((List.take_subset _ _) hd)
    · exact (List.take_subset _ _) ((List.drop_subset _ _) (List.mem_reverse.1 hd))
  -- `|J| = 2(n - 1)`
  have hcardI := hB.two_mul_arcLength_sub_one hY
  rw [hlen] at hcardI
  have hlenJ : (X.hugDarts P ζ (Q.map Subtype.val)).length = 2 * (n - 1) := by
    rw [← List.toFinset_card_of_nodup hJnd, hcardI]
    have himg : (intervalInterior Y.strandPerm j I).image
        (fun r => L[(cutEndIndex L s r : ℕ)]) = (X.hugDarts P ζ (Q.map Subtype.val)).toFinset := by
      ext d
      rw [mem_image, List.mem_toFinset]
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact (hI r).1 hr
      · intro hd
        obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem (hJsub d hd)
        obtain ⟨r, hr⟩ := cutEndIndex_surjective (H := H) (s := s) hev ⟨x, hx⟩
        exact ⟨r, (hI r).2 (by simpa only [hr] using hd), by simp only [hr]⟩
    rw [← himg, card_image_of_injective]
    intro r r' h
    exact cutEndIndex_injective (Fin.ext (hLnd.getElem_inj_iff.1 h))
  refine ⟨hret, ?_, by rw [hlenJ, List.length_map], ?_⟩
  · -- the interior points of `Q` are pairwise distinct
    rw [List.nodup_iff_injective_get]
    rintro ⟨u, hu⟩ ⟨v, hv⟩ h
    simp only [interiorPoints, List.length_map, List.length_dropLast] at hu hv
    simp only [interiorPoints, List.get_eq_getElem, List.getElem_map, List.getElem_dropLast] at h
    have hS := hB.2.1 u v (by rw [hlen]; omega) (by rw [hlen]; omega)
    rw [(hinvQ u (by omega)).2, (hinvQ v (by omega)).2, hYdef,
      hc.cut_vertexOf_inl_of_notMem _ (hinvQ u (by omega)).1,
      hc.cut_vertexOf_inl_of_notMem _ (hinvQ v (by omega)).1] at hS
    exact Fin.ext (hS (by rw [h]))
  -- the relations `d̄_{2j-1} = σ^{νs}(f̄_j)`, `d̄_{2j} = σ^{2νs}(f̄_j)`
  intro jj hjj
  rw [List.length_map] at hjj
  have hQj : (Q.map Subtype.val)[jj]? = some Q[jj].1 := by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)]
    rfl
  rw [hQj, Option.map_some, Option.map_some]
  have hy := htripQ jj (by omega)
  have hlt := (cutEndIndex L s (sourceIndex j)).isLt
  have hNe : NeZero (2 * (L.length / 2)) := ⟨by omega⟩
  have hjjl : jj + 1 < Y.arcLength j := by rw [hlen]; omega
  have hrel : ∀ (r : Fin (2 * (L.length / 2))) (k : ℕ),
      Y.inv (Y.endDart r) = (Y.rot ^ k) (Y.inv (Y.arcDart j jj)) →
        X.inv L[(cutEndIndex L s r : ℕ)] = (X.rot ^ k) (X.inv Q[jj].1) := by
    intro r k h
    obtain ⟨hm, hr⟩ := hrotQ jj (by omega) k
    rw [hlegInv, hr] at h
    exact congrArg Subtype.val (Sum.inl_injective h)
  have hentry : ∀ (r : Fin (2 * (L.length / 2))) (t : ℕ),
      (cutEndIndex L s r : ℕ) = pre.length + t →
        (X.sideList ζ P)[t]? = some L[(cutEndIndex L s r : ℕ)] := by
    intro r t ht
    rw [← hLside', ← ht, List.getElem?_eq_getElem]
  have hval := fun t => val_cutEndIndex_finRotate_pow (s := s) hev (sourceIndex j) t
  have hvalq := fun t => val_cutEndIndex_finRotate_pow (s := s) hev (Y.arcEndIndex j) t
  rcases hB.1 with hI1 | hI2
  · -- `I` runs clockwise from the source of `Q` to its target
    have hcI : (intervalInterior Y.strandPerm j I).card + 2 =
        ((Y.arcEndIndex j - sourceIndex j : Fin (2 * (L.length / 2))) : ℕ) + 1 := by
      rw [hB.1.card_intervalInterior, hI1, card_cyclicIcc]
      rfl
    have hdlt := (Y.arcEndIndex j - sourceIndex j : Fin (2 * (L.length / 2))).isLt
    have hxq := hval ((Y.arcEndIndex j - sourceIndex j : Fin (2 * (L.length / 2))) : ℕ)
    rw [finRotate_pow_val_sub', hx₂, hx₁] at hxq
    have hp1 : (finRotate _ ^ (0 + 1)) (sourceIndex j) ∈ intervalInterior Y.strandPerm j I := by
      rw [intervalInterior, hI1, mem_cyclicIcc_sdiff_iff]
      exact ⟨0, by change 0 + 1 < ((Y.arcEndIndex j - sourceIndex j : Fin _) : ℕ); omega, rfl⟩
    have hp1J := (hI _).1 hp1
    rw [hJ] at hp1J
    have hlt12 : k₁ < k₂ := by
      by_contra hcon
      have h21 : k₂ < k₁ := by omega
      rw [if_neg hcon] at hp1J
      obtain ⟨t, ht, hte⟩ := List.getElem_of_mem hp1J
      obtain ⟨hl, hent⟩ := drop_take_reverse_getElem?' (X.sideList ζ P) h21 hk₁
      have h1 := hent t (by rw [← hl]; exact ht)
      rw [List.getElem?_eq_getElem ht, hte, ← hLside'] at h1
      have heq := eq_of_getElem?_eq' hLnd (List.getElem?_eq_getElem _) h1.symm
      rw [hval, hx₁] at heq
      rcases Nat.lt_or_ge (pre.length + k₁ + (0 + 1)) L.length with h | h
      · rw [Nat.mod_eq_of_lt h] at heq; omega
      · rw [show pre.length + k₁ + (0 + 1) = L.length by omega, Nat.mod_self] at heq; omega
    have hE : hugExponent ζ a c = -1 := hor.1 hlt12
    have hxd : pre.length + k₂ = pre.length + k₁ +
        ((Y.arcEndIndex j - sourceIndex j : Fin (2 * (L.length / 2))) : ℕ) := by
      rcases Nat.lt_or_ge (pre.length + k₁ +
          ((Y.arcEndIndex j - sourceIndex j : Fin (2 * (L.length / 2))) : ℕ)) L.length with h | h
      · rwa [Nat.mod_eq_of_lt h] at hxq
      · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at hxq
        omega
    obtain ⟨-, hentJ⟩ := take_drop_getElem?' (X.sideList ζ P) (i := k₁) hk₂
    rw [hJ, if_pos hlt12, hE]
    obtain ⟨hs5, hs4⟩ := hB.inv_endDart_of_eq_cyclicIcc hY hI1 hjjl
    have e5 := hrel _ 5 hs5
    have e4 := hrel _ 4 hs4
    have hv5 := hval (2 * jj + 1)
    have hv4 := hval (2 * jj + 2)
    rw [hx₁, Nat.mod_eq_of_lt (by omega)] at hv5 hv4
    rw [hentJ _ (by omega), hentJ _ (by omega),
      hentry ((finRotate _ ^ (2 * jj + 1)) (sourceIndex j)) (k₁ + 1 + 2 * jj) (by omega),
      hentry ((finRotate _ ^ (2 * jj + 2)) (sourceIndex j)) (k₁ + 1 + (2 * jj + 1)) (by omega),
      Option.map_some, Option.map_some, e5, e4]
    have z1 := rot_zpow_neg' hpre hy (k := 1) (by norm_num)
    have z2 := rot_zpow_neg' hpre hy (k := 2) (by norm_num)
    norm_num at z1 z2 ⊢
    rw [z1, z2]
    exact ⟨rfl, rfl⟩
  · -- `I` runs clockwise from the target of `Q` to its source
    have hcI : (intervalInterior Y.strandPerm j I).card + 2 =
        ((sourceIndex j - Y.arcEndIndex j : Fin (2 * (L.length / 2))) : ℕ) + 1 := by
      rw [hB.1.card_intervalInterior, hI2, card_cyclicIcc]
      rfl
    have hdlt := (sourceIndex j - Y.arcEndIndex j : Fin (2 * (L.length / 2))).isLt
    have hxp := hvalq ((sourceIndex j - Y.arcEndIndex j : Fin (2 * (L.length / 2))) : ℕ)
    rw [finRotate_pow_val_sub', hx₂, hx₁] at hxp
    have hq1 : (finRotate _ ^ (0 + 1)) (Y.arcEndIndex j) ∈ intervalInterior Y.strandPerm j I := by
      rw [intervalInterior, hI2, pair_comm, mem_cyclicIcc_sdiff_iff]
      exact ⟨0, by change 0 + 1 < ((sourceIndex j - Y.arcEndIndex j : Fin _) : ℕ); omega, rfl⟩
    have hq1J := (hI _).1 hq1
    rw [hJ] at hq1J
    have hlt21 : ¬k₁ < k₂ := by
      intro hcon
      rw [if_pos hcon] at hq1J
      obtain ⟨t, ht, hte⟩ := List.getElem_of_mem hq1J
      obtain ⟨hl, hent⟩ := take_drop_getElem?' (X.sideList ζ P) (i := k₁) hk₂
      have h1 := hent t (by rw [← hl]; exact ht)
      rw [List.getElem?_eq_getElem ht, hte, ← hLside'] at h1
      have heq := eq_of_getElem?_eq' hLnd (List.getElem?_eq_getElem _) h1.symm
      rw [hvalq, hx₂] at heq
      rcases Nat.lt_or_ge (pre.length + k₂ + (0 + 1)) L.length with h | h
      · rw [Nat.mod_eq_of_lt h] at heq; omega
      · rw [show pre.length + k₂ + (0 + 1) = L.length by omega, Nat.mod_self] at heq; omega
    have h21 : k₂ < k₁ := by omega
    have hE : hugExponent ζ a c = 1 := by
      rcases hugExponent_eq_one_or ζ a c with h | h
      · exact h
      · exact absurd (hor.2 h) hlt21
    have hxd : pre.length + k₁ = pre.length + k₂ +
        ((sourceIndex j - Y.arcEndIndex j : Fin (2 * (L.length / 2))) : ℕ) := by
      rcases Nat.lt_or_ge (pre.length + k₂ +
          ((sourceIndex j - Y.arcEndIndex j : Fin (2 * (L.length / 2))) : ℕ)) L.length with h | h
      · rwa [Nat.mod_eq_of_lt h] at hxp
      · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at hxp; omega
    obtain ⟨-, hentJ⟩ := drop_take_reverse_getElem?' (X.sideList ζ P) h21 hk₁
    rw [hJ, if_neg hlt21, hE]
    have hll : n - 2 - jj + 1 < Y.arcLength j := by rw [hlen]; omega
    obtain ⟨hs2, hs1⟩ := hB.inv_endDart_of_eq_cyclicIcc' hY hI2 hll
    rw [hlen, show n - 2 - (n - 2 - jj) = jj by omega] at hs2 hs1
    rw [← pow_one Y.rot] at hs1
    have e2 := hrel _ 2 hs2
    have e1 := hrel _ 1 hs1
    have hv2 := hvalq (2 * (n - 2 - jj) + 1)
    have hv1 := hvalq (2 * (n - 2 - jj) + 2)
    rw [hx₂, Nat.mod_eq_of_lt (by omega)] at hv2 hv1
    change (cutEndIndex L s ((finRotate _ ^ (2 * (n - 2 - jj) + 1))
      (targetIndex (Y.strandPerm j))) : ℕ) = _ at hv2
    change (cutEndIndex L s ((finRotate _ ^ (2 * (n - 2 - jj) + 2))
      (targetIndex (Y.strandPerm j))) : ℕ) = _ at hv1
    rw [hentJ _ (by omega), hentJ _ (by omega),
      hentry ((finRotate _ ^ (2 * (n - 2 - jj) + 2)) (targetIndex (Y.strandPerm j)))
        (k₁ - 1 - 2 * jj) (by omega),
      hentry ((finRotate _ ^ (2 * (n - 2 - jj) + 1)) (targetIndex (Y.strandPerm j)))
        (k₁ - 1 - (2 * jj + 1)) (by omega), Option.map_some, Option.map_some, e1, e2]
    refine ⟨?_, ?_⟩
    · rw [zpow_one, pow_one]
    · rw [mul_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]

/-- **A boundary-parallel returning arc hugs.** Let `S` be the simple arc from `s_i` of a triple
diagram `X`, `ζ` a side with `N_ζ ≥ 2`, and `Q = (f₁, …, f_n)` an arc of `Y = X|_{S,ζ}` (whose
darts are the `Sum.inl f_l`, `f_l ∈ H_ζ(S)`) that is a returning path of `S` on side `ζ` from
`z_{a+1}` to `z_{c+1}`. Suppose `Q` is boundary-parallel in `Y` along the interval `I` of its pair
whose interior positions are those of the darts of the `ζ` list of `S` lying strictly between `f₁`
and `f̄_n` in that list (`hugDarts`): the legs of `Y` at the interior positions of `I` are exactly
these darts. Then `Q` hugs `S`. -/
@[cluster_algebras "lem_cut_boundary_parallel_hugs"]
theorem IsSimpleArc.hugs_of_isBoundaryParallel_arcCut {i : Fin b} (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) {ζ : StrandSide} (hN : 2 ≤ (X.arcCutList i ζ).length)
    {Q : List {d // d ∈ X.arcSideDarts i ζ}} {j : Fin ((X.arcCutList i ζ).length / 2)}
    (hQ : Q.map Sum.inl = (X.arcCut i ζ).arc j) {a c : ℕ}
    (hret : X.IsReturningPath (X.arc i) ζ (Q.map Subtype.val) a c)
    {I : Finset (Fin (2 * ((X.arcCutList i ζ).length / 2)))}
    (hB : (X.arcCut i ζ).IsBoundaryParallel j I)
    (hI : ∀ r, r ∈ intervalInterior (X.arcCut i ζ).strandPerm j I ↔
      ∃ d ∈ X.hugDarts (X.arc i) ζ (Q.map Subtype.val), ∃ hd : d ∈ X.arcSideDarts i ζ,
        (X.arcCut i ζ).endDart r = .inl ⟨d, hd⟩) :
    X.Hugs (X.arc i) ζ (Q.map Subtype.val) a c := by
  have hc := hS.isCutData_arcCutList hX ζ
  refine hugs_of_isBoundaryParallel_cut hX hc (even_length_arcCutList ζ)
    (hS.isTripleDiagram_arcCut hX ζ hN) (arcCutList_eq_append ζ) hQ hret hB fun r => ?_
  refine (hI r).trans ⟨?_, ?_⟩
  · rintro ⟨d, hd, hdK, he⟩
    rw [arcCut, cut_endDart, hc.cutListDart_eq] at he
    have := congrArg Subtype.val (Sum.inl_injective he)
    simp only at this
    rwa [this]
  · intro h
    exact ⟨_, h, _, by rw [arcCut, cut_endDart, hc.cutListDart_eq]⟩

/-- **A boundary-parallel arc of the inside hugs.** Let `M` be a convex monogon of a triple
diagram `X` with inside `ζ`, winding function `h` and `m ≥ 2` darts, and `Q = (f₁, …, f_n)` an arc
of its inside `X|_M` (whose darts are the `Sum.inl f_l`, `f_l` inside darts) that is
boundary-parallel in `X|_M` along the interval `I` of its pair whose interior positions are those
of the darts of the inside list strictly between `f₁` and `f̄_n` in that list (`hugDarts`): the
legs of `X|_M` at the interior positions of `I` are exactly these darts. Then `Q` hugs `M` (it is
a returning path of `M` on side `ζ` from some `z_{a+1}` to some `z_{c+1}`). -/
@[cluster_algebras "lem_monogon_cut_hugs"]
theorem IsConvexMonogon.hugs_of_isBoundaryParallel_monogonCut {P : List H} {ζ : StrandSide}
    {h : X.faceOrbits → ℤ} (hX : X.IsTripleDiagram) (hM : X.IsConvexMonogon P ζ)
    (hh : X.IsMonogonWindingFunction P h) (hm : 2 ≤ P.length)
    {Q : List {d // d ∈ X.insideDarts P ζ h}} {j : Fin ((X.insideList ζ P).length / 2)}
    (hQ : Q.map Sum.inl = (X.monogonCut P ζ h).arc j)
    {I : Finset (Fin (2 * ((X.insideList ζ P).length / 2)))}
    (hB : (X.monogonCut P ζ h).IsBoundaryParallel j I)
    (hI : ∀ r, r ∈ intervalInterior (X.monogonCut P ζ h).strandPerm j I ↔
      ∃ d ∈ X.hugDarts P ζ (Q.map Subtype.val), ∃ hd : d ∈ X.insideDarts P ζ h,
        (X.monogonCut P ζ h).endDart r = .inl ⟨d, hd⟩) :
    ∃ a c, X.Hugs P ζ (Q.map Subtype.val) a c := by
  obtain ⟨Q', hQ', a, c, hret⟩ := hM.exists_isReturningPath_arc_monogonCut hX hh hm j
  have hQQ : Q' = Q := (List.map_injective_iff.2 Sum.inl_injective) (hQ'.trans hQ.symm)
  subst hQQ
  have hc := hM.isCutData_insideDarts hX hh
  have hev : Even (X.insideList ζ P).length := by
    rw [length_insideList]
    exact even_two_mul _
  refine ⟨a, c, hugs_of_isBoundaryParallel_cut hX hc hev (hM.isTripleDiagram_monogonCut hX hh hm)
    (pre := []) (List.nil_append _).symm hQ hret hB fun r => ?_⟩
  refine (hI r).trans ⟨?_, ?_⟩
  · rintro ⟨d, hd, hdK, he⟩
    rw [monogonCut, cut_endDart, hc.cutListDart_eq] at he
    have := congrArg Subtype.val (Sum.inl_injective he)
    simp only at this
    rwa [this]
  · intro h
    exact ⟨_, h, _, by rw [monogonCut, cut_endDart, hc.cutListDart_eq]⟩

end CutHugs

/-! ### The strand permutation of the cut along a boundary-parallel arc -/

section CutPermutation

variable {X : TripleData H b} {i : Fin b}

/-- The involution exchanging `2l` and `2l + 1`. -/
private def pairSwap (w : ℕ) : ℕ := if w % 2 = 0 then w + 1 else w - 1

private theorem pairSwap_pairSwap (w : ℕ) : pairSwap (pairSwap w) = w := by
  unfold pairSwap; split_ifs <;> omega

private theorem pairSwap_lt {w k : ℕ} (hw : w < 2 * k) : pairSwap w < 2 * k := by
  unfold pairSwap; split_ifs <;> omega

/-- The position of the leg behind entry `x` of a cut list: with `A, E` the two ends of a run of
`c` positions, the entry `x < c` sits at the position `x + 1` steps clockwise from `A`, and the
entry `c + w` belongs to the position `pairSwap w + 1` steps clockwise from `E`. -/
private def legPos {n : ℕ} (A E : Fin n) (c x : ℕ) : Fin n :=
  if x < c then (finRotate n ^ (x + 1)) A else (finRotate n ^ (pairSwap (x - c) + 1)) E

variable (X) in
/-- For an arc boundary-parallel along `I`, the position `r` of `X` behind the entry `x` of the cut
list on the side `η` opposite to `I`: the entry is the leg `n_r` at an `η` position, or the dart
`σ³ n̄_r` opposite to `n̄_r` at a point of the arc, for `r` interior to `I`. -/
private def oppLegPos (i : Fin b) (I : Finset (Fin (2 * b))) (x : ℕ) : Fin (2 * b) :=
  legPos (X.arcSideStart i (intervalSide X.strandPerm i I).opposite)
    (X.arcSideEnd i (intervalSide X.strandPerm i I).opposite)
    (((X.arcSideEnd i (intervalSide X.strandPerm i I).opposite -
      X.arcSideStart i (intervalSide X.strandPerm i I).opposite : Fin (2 * b)) : ℕ) - 1) x

/-- `oppLegPos` depends on `X` only through `π_X(i)`. -/
private theorem oppLegPos_congr {H' : Type*} [Fintype H'] [DecidableEq H'] {X' : TripleData H' b}
    (h : X.strandPerm i = X'.strandPerm i) (I : Finset (Fin (2 * b))) :
    X.oppLegPos i I = X'.oppLegPos i I := by
  have h1 : intervalSide X.strandPerm i I = intervalSide X'.strandPerm i I := by
    simp only [intervalSide, h]
  have h2 : ∀ ζ, X.arcSideStart i ζ = X'.arcSideStart i ζ := by
    intro ζ; cases ζ <;> simp [arcSideStart, arcEndIndex, h]
  have h3 : ∀ ζ, X.arcSideEnd i ζ = X'.arcSideEnd i ζ := by
    intro ζ; cases ζ <;> simp [arcSideEnd, arcEndIndex, h]
  unfold oppLegPos
  rw [h1, h2, h3]

/-- The two sides of a simple arc are disjoint. -/
private theorem disjoint_arcSideDarts_opposite (ζ : StrandSide) :
    Disjoint (X.arcSideDarts i ζ) (X.arcSideDarts i ζ.opposite) := by
  cases ζ
  · exact disjoint_rightSide_leftSide
  · exact disjoint_rightSide_leftSide.symm

/-- The entries of the cut list on the side `η` opposite to `I`, for an arc boundary-parallel
along `I`: the entry `x` is the leg `n_r` (a dart of that side) or `σ³ n̄_r` with `r` interior to
`I`, for `r = oppLegPos X i I x`. -/
private theorem oppLegPos_spec (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hB : X.IsBoundaryParallel i I) {η : StrandSide}
    (hη : η = (intervalSide X.strandPerm i I).opposite) {x : ℕ}
    (hx : x < (X.arcCutList i η).length) :
    (X.endDart (X.oppLegPos i I x) ∈ X.arcSideDarts i η ∧
      (X.arcCutList i η)[x]? = some (X.endDart (X.oppLegPos i I x))) ∨
    (X.oppLegPos i I x ∈ intervalInterior X.strandPerm i I ∧
      (X.arcCutList i η)[x]? = some ((X.rot ^ 3) (X.inv (X.endDart (X.oppLegPos i I x))))) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ, intervalSide X.strandPerm i I = ζ := ⟨_, rfl⟩
  rw [hζ] at hη
  subst hη
  have hc := hB.2.1.isCutData_arcCutList hX ζ.opposite
  have hlen : (X.arcCutList i ζ.opposite).length =
      ((X.arcSideEnd i ζ.opposite - X.arcSideStart i ζ.opposite : Fin (2 * b)) : ℕ) - 1 +
        2 * (X.arcLength i - 1) := by
    rw [arcCutList_eq_append, List.length_append, List.length_map, List.length_range,
      length_sideList_arc]
  have hk := hB.two_mul_arcLength_sub_one hX
  have hcard := hB.1.card_intervalInterior_eq (X := X)
  rw [hζ] at hcard
  unfold oppLegPos legPos
  rw [hζ]
  set c := ((X.arcSideEnd i ζ.opposite - X.arcSideStart i ζ.opposite : Fin (2 * b)) : ℕ) - 1
    with hc_def
  split_ifs with hxc
  · left
    have h := getElem?_arcCutList_of_lt (X := X) (i := i) ζ.opposite (t := x) (by omega)
    exact ⟨hc.mem_of_mem_list _ (List.mem_of_getElem? h), h⟩
  · right
    have hu : pairSwap (x - c) < 2 * (X.arcLength i - 1) := pairSwap_lt (by omega)
    have h := hB.getElem?_arcCutList_opposite hX hζ hu
    have e : (if pairSwap (x - c) % 2 = 0 then pairSwap (x - c) + 1 else pairSwap (x - c) - 1) =
        x - c := pairSwap_pairSwap _
    rw [← hc_def, e, show c + (x - c) = x by omega, ← arcSideEnd_opposite] at h
    refine ⟨?_, h⟩
    rw [hB.1.mem_intervalInterior_iff (X := X), hζ]
    exact ⟨pairSwap (x - c), by omega, by rw [arcSideEnd_opposite]⟩

/-- `oppLegPos X i I` is injective on the indices of the cut list on the side opposite to `I`. -/
private theorem oppLegPos_injOn (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hB : X.IsBoundaryParallel i I) {η : StrandSide}
    (hη : η = (intervalSide X.strandPerm i I).opposite) {x y : ℕ}
    (hx : x < (X.arcCutList i η).length) (hy : y < (X.arcCutList i η).length)
    (h : X.oppLegPos i I x = X.oppLegPos i I y) : x = y := by
  have hc := hB.2.1.isCutData_arcCutList hX η
  have hside := hB.arcSideDarts_intervalSide hX
  have hmemζ : ∀ r ∈ intervalInterior X.strandPerm i I,
      X.endDart r ∈ X.arcSideDarts i (intervalSide X.strandPerm i I) := by
    intro r hr
    rw [hside, mem_biUnion]
    exact ⟨r, hr, mem_insert_self _ _⟩
  have hdisj := disjoint_left.1
    (disjoint_arcSideDarts_opposite (X := X) (i := i) (intervalSide X.strandPerm i I))
  rw [← hη] at hdisj
  rcases oppLegPos_spec hX hB hη hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;>
    rcases oppLegPos_spec hX hB hη hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
  · rw [h] at hx2
    exact eq_of_getElem?_eq' hc.nodup hx2 hy2
  · rw [h] at hx1
    exact absurd hx1 (hdisj (hmemζ _ hy1))
  · rw [← h] at hy1
    exact absurd hy1 (hdisj (hmemζ _ hx1))
  · rw [h] at hx2
    exact eq_of_getElem?_eq' hc.nodup hx2 hy2

private theorem isStrandPath_cons' {Q : List H} (hQ : X.IsStrandPath Q) {d : H}
    (hd : d ∉ X.bdry) (ho : X.isOut d = true) (hstep : ∀ e ∈ Q.head?, X.StrandStep d e) :
    X.IsStrandPath (d :: Q) := by
  obtain ⟨hne, hb, ho', hch⟩ := hQ
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_cons.1 he with rfl | he
    exacts [hd, hb e he]
  · intro e he
    rcases List.mem_cons.1 he with rfl | he
    exacts [ho, ho' e he]
  · obtain ⟨e, Q', rfl⟩ := List.exists_cons_of_ne_nil hne
    exact List.IsChain.cons_cons (hstep e rfl) hch

private theorem isStrandPath_concat' {Q : List H} (hQ : X.IsStrandPath Q) {d : H}
    (hd : d ∉ X.bdry) (ho : X.isOut d = true) (hstep : ∀ e ∈ Q.getLast?, X.StrandStep e d) :
    X.IsStrandPath (Q ++ [d]) := by
  obtain ⟨hne, hb, ho', hch⟩ := hQ
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact hb e he
    · rwa [List.mem_singleton.1 he]
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact ho' e he
    · rwa [List.mem_singleton.1 he]
  · rw [List.isChain_append]
    refine ⟨hch, List.IsChain.singleton _, fun e he e' he' => ?_⟩
    rw [List.head?_singleton, Option.mem_def, Option.some.injEq] at he'
    subst he'
    exact hstep e he

/-- A strand path from `a_j` whose last dart `g` has `ḡ = n_r` is the arc from `s_j`, which
therefore ends at `ε(r)`. -/
private theorem arcEndIndex_eq_of_isStrandPath (hX : X.IsTripleDiagram) {P : List H} {j : Fin b}
    {r : Fin (2 * b)} {g : H} (hP : X.IsStrandPath P)
    (hhead : P.head? = some (X.endDart (sourceIndex j))) (hlast : P.getLast? = some g)
    (hg : X.inv g = X.endDart r) : X.arcEndIndex j = r := by
  have hrun : X.RunsToEndpoint g := by
    change X.IsBoundaryVertex (X.vertexOf (X.inv g))
    rw [hg]
    exact (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2
  have harc := eq_arc_of_isStrandPath hP hhead (fun e he => by
    rw [hlast, Option.mem_def, Option.some.injEq] at he
    rw [← he]; exact hrun)
  have hm := hX.toIsPreTripleDiagram.arcLength_ne_zero j
  have hlast' : X.arcDart j (X.arcLength j - 1) = g := by
    have h := hlast
    rw [harc, List.getLast?_eq_getElem?, length_arc,
      List.getElem?_eq_getElem (by rw [length_arc]; omega), getElem_arc, Option.some.injEq] at h
    exact h
  apply hX.endpoint_injective
  change X.vertexOf (X.endDart (X.arcEndIndex j)) = X.vertexOf (X.endDart r)
  rw [endDart_arcEndIndex hX, hlast', hg]

/-- For an arc boundary-parallel along `I` and every arc `u` of the cut `Y` on the side `η`
opposite to `I`, the positions of `X` behind the legs of `Y` at the source and at the target of `u`
are the source `s_j` and the target `t_{π(j)}` of one arc `j` of `X`. -/
private theorem exists_oppLegPos_arcCut (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hB : X.IsBoundaryParallel i I) {η : StrandSide}
    (hη : η = (intervalSide X.strandPerm i I).opposite) (hN : 2 ≤ (X.arcCutList i η).length)
    (u : Fin ((X.arcCutList i η).length / 2)) :
    ∃ j : Fin b,
      X.oppLegPos i I (cutEndIndex (X.arcCutList i η) η.cutShift (sourceIndex u)) =
        sourceIndex j ∧
      X.oppLegPos i I (cutEndIndex (X.arcCutList i η) η.cutShift
          (targetIndex ((X.arcCut i η).strandPerm u))) = targetIndex (X.strandPerm j) := by
  have hS := hB.2.1
  have hc := hS.isCutData_arcCutList hX η
  have hinv := hX.inv_involutive
  have hpre := hX.toIsPreTripleDiagram
  have hY := hS.isTripleDiagram_arcCut hX η hN
  have hYp := hY.toIsPreTripleDiagram
  have hA := (X.arcCut i η).isStrandPath_arc hYp (hYp.arcLength_ne_zero u)
  obtain ⟨Q, hQ, hQX⟩ := hS.exists_isStrandPath_of_isStrandPath_arcCut hX η hA
  have hlenQ : (X.arcCut i η).arcLength u = Q.length := by
    rw [← length_arc, hQ, List.length_map]
  have hQ0 : 0 < Q.length := by have := hYp.arcLength_ne_zero u; omega
  have hdart : ∀ l (hl : l < Q.length), (X.arcCut i η).arcDart u l = .inl Q[l] := fun l hl =>
    arcDart_eq_of_map_eq_arc hQ.symm hl
  have hleg : ∀ r, (X.arcCut i η).endDart r =
      .inl ⟨(X.arcCutList i η)[(cutEndIndex (X.arcCutList i η) η.cutShift r : ℕ)],
        hc.getElem_mem _⟩ := by
    intro r
    rw [arcCut, cut_endDart, hc.cutListDart_eq]
  -- the first and the last dart of `Q`
  have hfirst : (X.arcCutList i η)[(cutEndIndex (X.arcCutList i η) η.cutShift
      (sourceIndex u) : ℕ)]? = some Q[0].1 := by
    rw [List.getElem?_eq_getElem (cutEndIndex _ _ _).isLt]
    have h := hleg (sourceIndex u)
    rw [show (X.arcCut i η).endDart (sourceIndex u) = (X.arcCut i η).arcDart u 0 from rfl,
      hdart 0 hQ0] at h
    exact congrArg some (congrArg Subtype.val (Sum.inl_injective h)).symm
  have hlastQ : (X.arcCutList i η)[(cutEndIndex (X.arcCutList i η) η.cutShift
      (targetIndex ((X.arcCut i η).strandPerm u)) : ℕ)]? = some (X.inv Q[Q.length - 1].1) := by
    rw [List.getElem?_eq_getElem (cutEndIndex _ _ _).isLt]
    have h := hleg ((X.arcCut i η).arcEndIndex u)
    rw [endDart_arcEndIndex hY u, hlenQ, hdart _ (by omega), arcCut, hc.cut_inv_inl hinv] at h
    exact congrArg some (congrArg Subtype.val (Sum.inl_injective h)).symm
  have hQg := (X.isStrandPath_iff_getElem.1 hQX).2
  simp only [List.length_map, List.getElem_map] at hQg
  have hcutlen := (cutEndIndex (X.arcCutList i η) η.cutShift (sourceIndex u)).isLt
  have hcutlen' := (cutEndIndex (X.arcCutList i η) η.cutShift
    (targetIndex ((X.arcCut i η).strandPerm u))).isLt
  -- a triple point at the reverse of the leg of an interior position
  have htrip : ∀ r ∈ intervalInterior X.strandPerm i I,
      ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.endDart r))) := fun r hr =>
    (X.mem_internalVertices.1 (hB.2.2.2 r hr).1).2
  have hlastQ' : (Q.map Subtype.val).getLast? = some Q[Q.length - 1].1 := by
    rw [List.getLast?_map, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    rfl
  have hheadQ' : (Q.map Subtype.val).head? = some Q[0].1 := by
    rw [List.head?_map, List.head?_eq_getElem?, List.getElem?_eq_getElem hQ0]
    rfl
  have hsrc : ∀ r : Fin (2 * b), X.isOut (X.endDart r) = true → ∃ j, r = sourceIndex j := by
    intro r hr
    rcases exists_sourceIndex_or_targetIndex r with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨j, rfl⟩
    · rw [hX.isOut_target] at hr; exact absurd hr (by decide)
  -- the source of `u`: a strand path `P₀` from the leg at `s_j` to the last dart of `Q`
  obtain ⟨P₀, hP₀, hP₀head, hP₀last⟩ : ∃ P₀ : List H, X.IsStrandPath P₀ ∧
      P₀.head? = some (X.endDart (X.oppLegPos i I (cutEndIndex (X.arcCutList i η) η.cutShift
        (sourceIndex u)))) ∧ P₀.getLast? = some Q[Q.length - 1].1 := by
    rcases oppLegPos_spec hX hB hη hcutlen with ⟨-, h2⟩ | ⟨h1, h2⟩
    · rw [hfirst, Option.some.injEq] at h2
      exact ⟨Q.map Subtype.val, hQX, by rw [hheadQ', h2], hlastQ'⟩
    · rw [hfirst, Option.some.injEq] at h2
      have hr := htrip _ h1
      have hout : X.isOut (X.endDart (X.oppLegPos i I (cutEndIndex (X.arcCutList i η)
          η.cutShift (sourceIndex u)))) = true := by
        have h3 := (hQg.1 0 hQ0).2
        rw [h2, hpre.isOut_rot_pow_apply hr, hpre.isOut_inv_apply (hX.endDart_notMem_bdry _),
          if_neg (by decide)] at h3
        simpa using h3
      have hstep : ∀ e ∈ (Q.map Subtype.val).head?, X.StrandStep (X.endDart (X.oppLegPos i I
          (cutEndIndex (X.arcCutList i η) η.cutShift (sourceIndex u)))) e := by
        intro e he
        rw [hheadQ', Option.mem_def, Option.some.injEq] at he
        rw [← he, h2]
        exact ⟨hr, rfl⟩
      refine ⟨_ :: Q.map Subtype.val, isStrandPath_cons' hQX (hX.endDart_notMem_bdry _) hout
        hstep, rfl, ?_⟩
      rw [List.getLast?_cons, hlastQ']
      rfl
  obtain ⟨j, hj⟩ : ∃ j, X.oppLegPos i I (cutEndIndex (X.arcCutList i η) η.cutShift
      (sourceIndex u)) = sourceIndex j := by
    apply hsrc
    have hmem : X.endDart (X.oppLegPos i I (cutEndIndex (X.arcCutList i η) η.cutShift
        (sourceIndex u))) ∈ P₀ := List.mem_of_head? hP₀head
    exact hP₀.isOut_eq_true _ hmem
  refine ⟨j, hj, ?_⟩
  rw [hj] at hP₀head
  -- the target of `u`
  rcases oppLegPos_spec hX hB hη hcutlen' with ⟨-, h2⟩ | ⟨h1, h2⟩
  · rw [hlastQ, Option.some.injEq] at h2
    exact (arcEndIndex_eq_of_isStrandPath hX hP₀ hP₀head hP₀last h2).symm
  · rw [hlastQ, Option.some.injEq] at h2
    have hr := htrip _ h1
    have hnb : X.inv (X.endDart (X.oppLegPos i I (cutEndIndex (X.arcCutList i η) η.cutShift
        (targetIndex ((X.arcCut i η).strandPerm u))))) ∉ X.bdry := fun h =>
      hX.endDart_notMem_bdry _ (by have := hX.inv_mem_bdry _ h; rwa [hinv] at this)
    have hout : X.isOut (X.inv (X.endDart (X.oppLegPos i I (cutEndIndex (X.arcCutList i η)
        η.cutShift (targetIndex ((X.arcCut i η).strandPerm u)))))) = true := by
      have h3 := (hQg.1 _ (by omega : Q.length - 1 < Q.length)).2
      have h4 := hpre.isOut_inv_apply ((hQg.1 _ (by omega : Q.length - 1 < Q.length)).1)
      rw [h3, h2, hpre.isOut_rot_pow_apply hr, if_neg (by decide)] at h4
      simpa using h4
    have hstep : ∀ e ∈ P₀.getLast?, X.StrandStep e (X.inv (X.endDart (X.oppLegPos i I
        (cutEndIndex (X.arcCutList i η) η.cutShift
          (targetIndex ((X.arcCut i η).strandPerm u)))))) := by
      intro e he
      rw [hP₀last, Option.mem_def, Option.some.injEq] at he
      subst he
      refine ⟨?_, ?_⟩
      · change ¬X.IsBoundaryVertex (X.vertexOf (X.inv Q[Q.length - 1].1))
        rw [h2, X.vertexOf_rot_pow_apply]
        exact hr
      · rw [h2, ← Equiv.Perm.mul_apply, ← pow_add, hpre.rot_pow_six_apply hr]
    have hP₁ := isStrandPath_concat' hP₀ hnb hout hstep
    have hhead' : (P₀ ++ [X.inv (X.endDart (X.oppLegPos i I (cutEndIndex (X.arcCutList i η)
        η.cutShift (targetIndex ((X.arcCut i η).strandPerm u)))))]).head? =
          some (X.endDart (sourceIndex j)) := by
      rw [List.head?_append, hP₀head]; rfl
    exact (arcEndIndex_eq_of_isStrandPath hX hP₁ hhead' (by simp) (hinv _)).symm

/-- For an arc boundary-parallel along `I`, the cut list on the side opposite to `I` has
`2b - 2` entries. -/
private theorem length_arcCutList_opposite (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hB : X.IsBoundaryParallel i I) :
    (X.arcCutList i (intervalSide X.strandPerm i I).opposite).length = 2 * b - 2 := by
  have hlen : (X.arcCutList i (intervalSide X.strandPerm i I).opposite).length =
      ((X.arcSideEnd i (intervalSide X.strandPerm i I).opposite -
        X.arcSideStart i (intervalSide X.strandPerm i I).opposite : Fin (2 * b)) : ℕ) - 1 +
        2 * (X.arcLength i - 1) := by
    rw [arcCutList_eq_append, List.length_append, List.length_map, List.length_range,
      length_sideList_arc]
  have hk := hB.two_mul_arcLength_sub_one hX
  have hcard := hB.1.card_intervalInterior_eq (X := X)
  have hsum := val_sub_arcSide_add (X := X) (i := i) (intervalSide X.strandPerm i I)
  omega

/-- **The cut along a boundary-parallel arc has a determined strand permutation.** Let `X, X'` be
triple diagrams with `b` arcs and `π_X = π_{X'}`, let `I` be an interval of `i`, and let the arcs
`S, S'` from `s_i` be boundary-parallel along `I`, with `η` the side opposite to that of `I`. Then
`X|_{S,η}` and `X'|_{S',η}` have `b - 1` arcs and the same strand permutation: their arcs with the
same label end at targets with the same label. -/
@[cluster_algebras "lem_boundary_parallel_cut_permutation"]
theorem IsBoundaryParallel.arcCut_strandPerm_eq {H' : Type*} [Fintype H'] [DecidableEq H']
    {X' : TripleData H' b} (hX : X.IsTripleDiagram) (hX' : X'.IsTripleDiagram)
    (hπ : X.strandPerm = X'.strandPerm) {I : Finset (Fin (2 * b))}
    (hB : X.IsBoundaryParallel i I) (hB' : X'.IsBoundaryParallel i I) {η : StrandSide}
    (hη : η = (intervalSide X.strandPerm i I).opposite) :
    (X.arcCutList i η).length / 2 = b - 1 ∧ (X'.arcCutList i η).length / 2 = b - 1 ∧
      ∀ (u : Fin ((X.arcCutList i η).length / 2)) (u' : Fin ((X'.arcCutList i η).length / 2)),
        (u : ℕ) = u' → ((X.arcCut i η).strandPerm u : ℕ) = (X'.arcCut i η).strandPerm u' := by
  have hη' : η = (intervalSide X'.strandPerm i I).opposite := by rwa [← hπ]
  have hlen : (X.arcCutList i η).length = 2 * b - 2 := by
    rw [hη]; exact length_arcCutList_opposite hX hB
  have hlen' : (X'.arcCutList i η).length = 2 * b - 2 := by
    rw [hη']; exact length_arcCutList_opposite hX' hB'
  refine ⟨by omega, by omega, fun u u' huu' => ?_⟩
  have hu := u.isLt
  have hN : 2 ≤ (X.arcCutList i η).length := by omega
  have hN' : 2 ≤ (X'.arcCutList i η).length := by omega
  obtain ⟨j, hj1, hj2⟩ := exists_oppLegPos_arcCut hX hB hη hN u
  obtain ⟨j', hj1', hj2'⟩ := exists_oppLegPos_arcCut hX' hB' hη' hN' u'
  have hcong : X'.oppLegPos i I = X.oppLegPos i I :=
    (oppLegPos_congr (congrFun hπ i) I).symm
  rw [hcong] at hj1' hj2'
  have hsrc : (cutEndIndex (X'.arcCutList i η) η.cutShift (sourceIndex u') : ℕ) =
      cutEndIndex (X.arcCutList i η) η.cutShift (sourceIndex u) := by
    simp only [cutEndIndex, sourceIndex_val, hlen, hlen', huu']
  rw [hsrc, hj1] at hj1'
  obtain rfl := sourceIndex_injective hj1'
  rw [← hπ, ← hj2] at hj2'
  have htgt := oppLegPos_injOn hX hB hη (cutEndIndex _ _ _).isLt
    (by rw [hlen, ← hlen']; exact (cutEndIndex _ _ _).isLt) hj2'.symm
  simp only [cutEndIndex, targetIndex_val, hlen, hlen'] at htgt
  have h1 := ((X.arcCut i η).strandPerm u).isLt
  have h2 := ((X'.arcCut i η).strandPerm u').isLt
  have hm : 2 * ((X.arcCut i η).strandPerm u : ℕ) + 1 ≡
      2 * ((X'.arcCut i η).strandPerm u' : ℕ) + 1 [MOD 2 * b - 2] :=
    Nat.ModEq.add_right_cancel' _ htgt
  unfold Nat.ModEq at hm
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
  omega

end CutPermutation

/-! ### Coordinates of the darts around a boundary-parallel arc -/

section GlueCoordinates

variable {X : TripleData H b} {i : Fin b}

variable (X i) in
/-- The dart `σ^e(ē_{l+1})` at the triple point `z_{l+1}` of the arc from `s_i`. -/
private def zDart (l e : ℕ) : H := (X.rot ^ e) (X.inv (X.arcDart i l))

variable (X) in
/-- The dart `σ^e(n_r)` at the endpoint `ε(r)`. -/
private def eDart (r : Fin (2 * b)) (e : ℕ) : H := (X.rot ^ e) (X.endDart r)

/-- At a vertex with `n > 0` darts, `σⁿ` fixes every dart. -/
private theorem rot_pow_card_apply {d : H} {n : ℕ} (hn : 0 < n) (hcard : (X.vertexOf d).card = n) :
    (X.rot ^ n) d = d := by
  have hmem : (X.rot ^ n) d ∈ X.vertexOf d :=
    X.mem_vertexOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))
  obtain ⟨k, hk, hkd⟩ := X.exists_pow_apply_eq_of_card_vertexOf hcard hmem
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa using hkd.symm
  · exfalso
    have hve : X.vertexOf ((X.rot ^ k) d) = X.vertexOf d := X.vertexOf_rot_pow_apply k d
    have h1 : (X.rot ^ (n - k)) ((X.rot ^ k) d) = (X.rot ^ 0) ((X.rot ^ k) d) := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hk.le, hkd, pow_zero]
      rfl
    have := X.pow_apply_injective_of_card_vertexOf (by rw [hve, hcard]) (by omega) hn h1
    omega

/-- The endpoint `ε(r)` has three darts. -/
private theorem card_endpoint (hX : X.IsTripleDiagram) (r : Fin (2 * b)) :
    (X.vertexOf (X.endDart r)).card = 3 :=
  (hX.boundaryVertex_card _ (hX.endpoint_mem r)).1

/-- The leg `n_r` is the only dart of `ε(r)` outside `B`. -/
private theorem eq_endDart_of_mem_endpoint (hX : X.IsTripleDiagram) {r : Fin (2 * b)} {d : H}
    (hd : d ∈ X.vertexOf (X.endDart r)) (hdB : d ∉ X.bdry) : d = X.endDart r := by
  have h := hX.boundaryVertex_card _ (hX.endpoint_mem r)
  have hsum := card_filter_add_card_filter_not (s := X.endpoint r) (· ∈ X.bdry)
  rw [h.1, h.2] at hsum
  have h1 : ((X.endpoint r).filter (· ∉ X.bdry)).card = 1 := by omega
  obtain ⟨x, hx⟩ := card_eq_one.1 h1
  have hd' : d ∈ (X.endpoint r).filter (· ∉ X.bdry) := mem_filter.2 ⟨hd, hdB⟩
  have hn' : X.endDart r ∈ (X.endpoint r).filter (· ∉ X.bdry) :=
    mem_filter.2 ⟨X.self_mem_vertexOf _, hX.endDart_notMem_bdry r⟩
  rw [hx, mem_singleton] at hd' hn'
  rw [hd', hn']

private theorem rot_eDart (hX : X.IsTripleDiagram) (r : Fin (2 * b)) (e : ℕ) :
    X.rot (X.eDart r e) = X.eDart r ((e + 1) % 3) := by
  unfold eDart
  rw [← Equiv.Perm.mul_apply, ← pow_succ']
  conv_lhs => rw [← Nat.mod_add_div (e + 1) 3, pow_add, pow_mul, Equiv.Perm.mul_apply,
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
      (rot_pow_card_apply (by norm_num) (card_endpoint hX r)) ((e + 1) / 3)]

private theorem rot_zDart (hX : X.IsTripleDiagram) {l : ℕ} (hl : l + 1 < X.arcLength i)
    (e : ℕ) : X.rot (X.zDart i l e) = X.zDart i l ((e + 1) % 6) := by
  unfold zDart
  rw [← Equiv.Perm.mul_apply, ← pow_succ', hX.toIsPreTripleDiagram.rot_pow_mod_six]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (hX.toIsPreTripleDiagram.arcLength_ne_zero i)
  exact (X.arcLength_eq_succ_iff.1 hm).2 l (by omega)

private theorem not_isBoundaryVertex_zDart (hX : X.IsTripleDiagram) {l : ℕ}
    (hl : l + 1 < X.arcLength i) (e : ℕ) : ¬X.IsBoundaryVertex (X.vertexOf (X.zDart i l e)) := by
  unfold zDart
  rw [X.vertexOf_rot_pow_apply]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (hX.toIsPreTripleDiagram.arcLength_ne_zero i)
  exact (X.arcLength_eq_succ_iff.1 hm).2 l (by omega)

private theorem isBoundaryVertex_eDart (hX : X.IsTripleDiagram) (r : Fin (2 * b)) (e : ℕ) :
    X.IsBoundaryVertex (X.vertexOf (X.eDart r e)) := by
  unfold eDart
  rw [X.vertexOf_rot_pow_apply]
  exact (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2

/-- The vertex `v(ē_{l+1})` of a dart of the arc is passed through by the arc. -/
private theorem passesThrough_zDart (hX : X.IsTripleDiagram) {l : ℕ}
    (hl : l + 1 < X.arcLength i) (e : ℕ) :
    X.PassesThrough (X.arc i).toFinset (X.vertexOf (X.zDart i l e)) := by
  refine ⟨X.vertexOf_mem_internalVertices.2 (not_isBoundaryVertex_zDart hX hl e),
    X.arcDart i (l + 1), mem_arc_toFinset.2 ⟨l + 1, hl, rfl⟩, ?_⟩
  unfold zDart
  rw [arcDart_succ_eq hX hl, X.vertexOf_rot_pow_apply, X.vertexOf_rot_pow_apply]

private theorem zDart_inj (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) {l l' e e' : ℕ}
    (hl : l + 1 < X.arcLength i) (hl' : l' + 1 < X.arcLength i) (he : e < 6) (he' : e' < 6)
    (h : X.zDart i l e = X.zDart i l' e') : l = l' ∧ e = e' := by
  have hv := congrArg X.vertexOf h
  unfold zDart at hv
  rw [X.vertexOf_rot_pow_apply, X.vertexOf_rot_pow_apply] at hv
  obtain rfl := hS l l' hl hl' hv
  refine ⟨rfl, X.pow_apply_injective_of_card_vertexOf ?_ he he' h⟩
  exact hX.internalVertex_card _ (X.vertexOf_mem_internalVertices.2
    (by have := not_isBoundaryVertex_zDart hX hl 0; simpa [zDart] using this))

private theorem eDart_inj (hX : X.IsTripleDiagram) {r r' : Fin (2 * b)} {e e' : ℕ} (he : e < 3)
    (he' : e' < 3) (h : X.eDart r e = X.eDart r' e') : r = r' ∧ e = e' := by
  have hv := congrArg X.vertexOf h
  unfold eDart at hv
  rw [X.vertexOf_rot_pow_apply, X.vertexOf_rot_pow_apply] at hv
  obtain rfl := hX.endpoint_injective hv
  exact ⟨rfl, X.pow_apply_injective_of_card_vertexOf (card_endpoint hX r) he he' h⟩

private theorem zDart_ne_eDart (hX : X.IsTripleDiagram) {l : ℕ} (hl : l + 1 < X.arcLength i)
    (e : ℕ) (r : Fin (2 * b)) (e' : ℕ) : X.zDart i l e ≠ X.eDart r e' := fun h =>
  not_isBoundaryVertex_zDart hX hl e (h ▸ isBoundaryVertex_eDart hX r e')

/-- The darts `σ^e(n_r)`, `e ∈ {1, 2}`, of an endpoint are the darts of `B` there. -/
private theorem eDart_mem_bdry_iff (hX : X.IsTripleDiagram) (r : Fin (2 * b)) {e : ℕ}
    (he : e < 3) : X.eDart r e ∈ X.bdry ↔ e ≠ 0 := by
  constructor
  · rintro h rfl
    exact hX.endDart_notMem_bdry r h
  · intro he0
    by_contra hB
    exact he0 <| X.pow_apply_injective_of_card_vertexOf (card_endpoint hX r) he
      (by norm_num : 0 < 3) <| (eq_endDart_of_mem_endpoint hX (X.mem_vertexOf.2
        (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))) hB).trans (by simp)

/-- `(σ n_r)̄ = σ²(n_{r+1})`: the dart `β_r` of the exterior runs from `ε(r + 1)` to `ε(r)`. -/
private theorem inv_eDart_one (hX : X.IsTripleDiagram) (r : Fin (2 * b)) :
    X.inv (X.eDart r 1) = X.eDart (finRotate (2 * b) r) 2 := by
  rw [show X.inv (X.eDart r 1) = X.exteriorDart r by simp [eDart, exteriorDart]]
  have hext := exteriorDart_mem_exterior hX r
  have hv := vertexOf_exteriorDart hX r
  have hσ : X.rot (X.exteriorDart r) = X.endDart (finRotate (2 * b) r) := by
    apply eq_endDart_of_mem_endpoint hX
    · have : X.rot (X.exteriorDart r) ∈ X.vertexOf (X.exteriorDart r) :=
        X.mem_vertexOf.2 (Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _))
      rw [hv] at this
      exact this
    · exact (X.mem_exterior.1 hext).2
  have h3 := rot_pow_card_apply (X := X) (d := X.exteriorDart r) (n := 3) (by norm_num)
    (by rw [hv]; exact card_endpoint hX _)
  unfold eDart
  rw [← hσ, ← Equiv.Perm.mul_apply, ← pow_succ]
  exact h3.symm

/-- Every dart around an arc boundary-parallel along `I` is a dart `σ^e(ē_{l+1})` at a point of
the arc, a dart `σ^e(n_r)` at an endpoint, or a dart of the side opposite to `I` outside its cut
list. -/
private theorem dart_cases (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hB : X.IsBoundaryParallel i I) (d : H) :
    (∃ l e, l + 1 < X.arcLength i ∧ e < 6 ∧ d = X.zDart i l e) ∨
    (∃ r e, e < 3 ∧ d = X.eDart r e) ∨
    (d ∈ X.arcSideDarts i (intervalSide X.strandPerm i I).opposite ∧
      d ∉ X.arcCutList i (intervalSide X.strandPerm i I).opposite) := by
  by_cases hb : X.IsBoundaryVertex (X.vertexOf d)
  · right; left
    obtain ⟨r, hr⟩ := hX.exists_endpoint_eq _ (X.vertexOf_mem_boundaryVertices.2 hb)
    have hd : d ∈ X.vertexOf (X.endDart r) := by
      change d ∈ X.endpoint r
      rw [hr]
      exact X.self_mem_vertexOf d
    obtain ⟨k, hk, hkd⟩ := X.exists_pow_apply_eq_of_card_vertexOf (card_endpoint hX r) hd
    exact ⟨r, k, hk, hkd.symm⟩
  by_cases hp : X.PassesThrough (X.arc i).toFinset (X.vertexOf d)
  · left
    obtain ⟨-, e, he, hev⟩ := hp
    obtain ⟨t, ht, rfl⟩ := mem_arc_toFinset.1 he
    rcases t with _ | l
    · exfalso
      apply hb
      rw [← hev]
      exact (X.mem_boundaryVertices.1 (hX.endpoint_mem (sourceIndex i))).2
    · have hv : X.vertexOf (X.arcDart i (l + 1)) = X.vertexOf (X.inv (X.arcDart i l)) := by
        rw [arcDart_succ_eq hX ht, X.vertexOf_rot_pow_apply]
      have hd : d ∈ X.vertexOf (X.inv (X.arcDart i l)) := by
        rw [← hv, hev]
        exact X.self_mem_vertexOf d
      have hz := not_isBoundaryVertex_zDart hX (i := i) ht 0
      simp only [zDart, pow_zero, Equiv.Perm.one_apply] at hz
      obtain ⟨k, hk, hkd⟩ := X.exists_pow_apply_eq_of_card_vertexOf
        (hX.internalVertex_card _ (X.vertexOf_mem_internalVertices.2 hz)) hd
      exact ⟨l, k, ht, hk, hkd.symm⟩
  · right; right
    obtain ⟨ζ, hζ⟩ : ∃ ζ, intervalSide X.strandPerm i I = ζ := ⟨_, rfl⟩
    rw [hζ]
    have hdB : d ∉ X.bdry := fun h => hb ⟨d, X.self_mem_vertexOf d, h⟩
    have hdA : d ∉ X.arcDarts i := by
      intro h
      rcases mem_union.1 h with h | h
      · exact hp ⟨X.vertexOf_mem_internalVertices.2 hb, d, h, rfl⟩
      · obtain ⟨e, he, rfl⟩ := mem_image.1 h
        obtain ⟨t, ht, rfl⟩ := mem_arc_toFinset.1 he
        by_cases ht' : t + 1 < X.arcLength i
        · exact hp (by have := passesThrough_zDart hX ht' 0; simpa [zDart] using this)
        · apply hb
          rw [show t = X.arcLength i - 1 by omega, ← endDart_arcEndIndex hX]
          exact (X.mem_boundaryVertices.1 (hX.endpoint_mem _)).2
    have hside : d ∈ X.rightSide i ∨ d ∈ X.leftSide i := by
      have h := hB.2.1.arcDarts_union_rightSide_union_leftSide hX
      have hd : d ∈ X.bdryᶜ := mem_compl.2 hdB
      rw [← h, mem_union, mem_union] at hd
      rcases hd with (hd | hd) | hd
      · exact absurd hd hdA
      · exact Or.inl hd
      · exact Or.inr hd
    have hnotζ : d ∉ X.arcSideDarts i ζ := by
      have := hB.arcSideDarts_intervalSide hX
      rw [hζ] at this
      rw [this, mem_biUnion]
      rintro ⟨r, hr, hd⟩
      rcases mem_insert.1 hd with rfl | hd
      · exact hb (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2
      · rw [mem_singleton.1 hd] at hp
        exact hp (hB.2.2.2 r hr)
    have hK : d ∈ X.arcSideDarts i ζ.opposite := by
      cases ζ
      · rcases hside with h | h
        · exact absurd h hnotζ
        · exact h
      · rcases hside with h | h
        · exact h
        · exact absurd h hnotζ
    exact ⟨hK, notMem_arcCutList_of_avoided hX (X.vertexOf_mem_internalVertices.2 hb) hp⟩

/-- The entries of a cut list in coordinates: with `c` the number of positions on side `ζ`, the
entry `x < c` is the leg `n_r` at the position `r` that is `x + 1` steps clockwise from
`arcSideStart i ζ`, and the entry `c + j` is the entry `j` of the `ζ` list. -/
private theorem getElem?_arcCutList_coord (ζ : StrandSide) {x : ℕ}
    (hx : x < (X.arcCutList i ζ).length) :
    (X.arcCutList i ζ)[x]? = some
      (if x < ((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1 then
        X.eDart ((finRotate (2 * b) ^ (x + 1)) (X.arcSideStart i ζ)) 0
      else X.zDart i (sidePoint ζ (X.arcLength i)
          (x - (((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1)))
        (sideExp ζ (x - (((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1)))) := by
  have hlen : (X.arcCutList i ζ).length =
      ((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1 +
        2 * (X.arcLength i - 1) := by
    rw [arcCutList_eq_append, List.length_append, List.length_map, List.length_range,
      length_sideList_arc]
  split_ifs with hxc
  · rw [getElem?_arcCutList_of_lt ζ (by omega)]
    simp [eDart]
  · have h := getElem?_arcCutList_add (X := X) (i := i) ζ
      (x - (((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1))
    rw [show ((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1 +
      (x - (((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1)) = x by omega] at h
    rw [h, List.getElem?_eq_getElem (by rw [length_sideList_arc]; omega)]
    congr 1
    cases ζ
    · rw [getElem_sideList_arc_right]
      rfl
    · rw [getElem_sideList_arc_left]
      simp only [zDart, sidePoint, sideExp]
      congr 3

/-- The point index of `n̄_r` for the position `r` that is `t + 1` steps clockwise from
`arcSideStart i ζ` (`ζ` the side of the interval): `m - 2 - ⌊t/2⌋` on the right and `⌊t/2⌋` on
the left, for an arc of `m` darts. -/
private def zetaPoint : StrandSide → ℕ → ℕ → ℕ
  | .right, m, t => m - 2 - t / 2
  | .left, _, t => t / 2

/-- The exponent `e` with `n̄_r = σ^e(ē_{l+1})` for the position `r` that is `t + 1` steps
clockwise from `arcSideStart i ζ`: `2 - t mod 2` on the right and `5 - t mod 2` on the left. -/
private def zetaExp : StrandSide → ℕ → ℕ
  | .right, t => 2 - t % 2
  | .left, t => 5 - t % 2

/-- **The shape of a boundary-parallel arc** in coordinates: for the position `r` that is `t + 1`
steps clockwise from `arcSideStart i ζ`, `ζ` the side of `I`, `n̄_r` is the dart
`σ^{zetaExp}(ē_{zetaPoint + 1})`. -/
private theorem inv_eDart_interior (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hB : X.IsBoundaryParallel i I) {ζ : StrandSide} (hζ : intervalSide X.strandPerm i I = ζ)
    {t : ℕ} (ht : t < 2 * (X.arcLength i - 1)) :
    X.inv (X.eDart ((finRotate (2 * b) ^ (t + 1)) (X.arcSideStart i ζ)) 0) =
      X.zDart i (zetaPoint ζ (X.arcLength i) t) (zetaExp ζ t) := by
  simp only [eDart, pow_zero, Equiv.Perm.one_apply, zDart]
  obtain ⟨l, hl, rfl | rfl⟩ : ∃ l, l + 1 < X.arcLength i ∧ (t = 2 * l ∨ t = 2 * l + 1) :=
    ⟨t / 2, by omega, by omega⟩
  · cases ζ
    · have hI : I = cyclicIcc (targetIndex (X.strandPerm i)) (sourceIndex i) := by
        unfold intervalSide at hζ
        split_ifs at hζ with h
        rcases hB.1 with h' | h'
        · exact absurd h' h
        · exact h'
      have := (hB.inv_endDart_of_eq_cyclicIcc' hX hI (l := l) hl).1
      simp only [zetaPoint, zetaExp, show 2 * l / 2 = l by omega, show 2 * l % 2 = 0 by omega]
      exact this
    · have hI : I = cyclicIcc (sourceIndex i) (targetIndex (X.strandPerm i)) := by
        unfold intervalSide at hζ
        split_ifs at hζ with h
        exact h
      have := (hB.inv_endDart_of_eq_cyclicIcc hX hI (l := l) hl).1
      simp only [zetaPoint, zetaExp, show 2 * l / 2 = l by omega, show 2 * l % 2 = 0 by omega]
      exact this
  · cases ζ
    · have hI : I = cyclicIcc (targetIndex (X.strandPerm i)) (sourceIndex i) := by
        unfold intervalSide at hζ
        split_ifs at hζ with h
        rcases hB.1 with h' | h'
        · exact absurd h' h
        · exact h'
      have := (hB.inv_endDart_of_eq_cyclicIcc' hX hI (l := l) hl).2
      simp only [zetaPoint, zetaExp, show (2 * l + 1) / 2 = l by omega,
        show (2 * l + 1) % 2 = 1 by omega, show 2 * l + 1 + 1 = 2 * l + 2 by omega]
      rw [pow_one]
      exact this
    · have hI : I = cyclicIcc (sourceIndex i) (targetIndex (X.strandPerm i)) := by
        unfold intervalSide at hζ
        split_ifs at hζ with h
        exact h
      have := (hB.inv_endDart_of_eq_cyclicIcc hX hI (l := l) hl).2
      simp only [zetaPoint, zetaExp, show (2 * l + 1) / 2 = l by omega,
        show (2 * l + 1) % 2 = 1 by omega, show 2 * l + 1 + 1 = 2 * l + 2 by omega]
      exact this

end GlueCoordinates

/-! ### Gluing along a boundary-parallel arc -/

section Glue

/-- The properties of the bijection of darts of an isomorphism `Y → Y'` of triple data whose
numbers of arcs agree as numbers. -/
private structure IsIsoEquiv {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {n n' : ℕ} (Y : TripleData α n) (Y' : TripleData β n') (Ψ : α ≃ β) : Prop where
  /-- `Ψ(d̄) = Ψ(d)̄`. -/
  map_inv : ∀ d, Ψ (Y.inv d) = Y'.inv (Ψ d)
  /-- `Ψ(σ d) = σ'(Ψ d)`. -/
  map_rot : ∀ d, Ψ (Y.rot d) = Y'.rot (Ψ d)
  /-- `Ψ(B) = B'`. -/
  mem_bdry_iff : ∀ d, Ψ d ∈ Y'.bdry ↔ d ∈ Y.bdry
  /-- `o'(Ψ d) = o(d)` off `B`. -/
  map_isOut : ∀ d, d ∉ Y.bdry → Y'.isOut (Ψ d) = Y.isOut d
  /-- `Ψ(ε(r)) = ε'(r)`. -/
  map_endpoint : ∀ (r : Fin (2 * n)) (r' : Fin (2 * n')), (r : ℕ) = r' →
    (Y.endpoint r).map Ψ.toEmbedding = Y'.endpoint r'
  /-- `Ψ` maps endpoints to endpoints and triple points to triple points. -/
  isBoundaryVertex_iff : ∀ d,
    Y'.IsBoundaryVertex (Y'.vertexOf (Ψ d)) ↔ Y.IsBoundaryVertex (Y.vertexOf d)

private theorem IsIsoEquiv.of_iso {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {n : ℕ} {Y : TripleData α n} {Y' : TripleData β n} (Ψ : Y.Iso Y') :
    IsIsoEquiv Y Y' Ψ.toEquiv where
  map_inv := Ψ.map_inv
  map_rot := Ψ.map_rot
  mem_bdry_iff := Ψ.mem_bdry_iff
  map_isOut := Ψ.map_isOut
  map_endpoint r r' h := by
    obtain rfl := Fin.ext h
    exact Ψ.map_endpoint r
  isBoundaryVertex_iff := Ψ.isBoundaryVertex_vertexOf_iff

/-- Isomorphic triple data (with numbers of arcs equal as numbers) have a bijection of darts with
the properties of an isomorphism, whose inverse has them too. -/
private theorem HIsomorphic.exists_isIsoEquiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {n n' : ℕ} {Y : TripleData α n} {Y' : TripleData β n'}
    (h : Y.HIsomorphic Y') : ∃ Ψ : α ≃ β, IsIsoEquiv Y Y' Ψ ∧ IsIsoEquiv Y' Y Ψ.symm := by
  obtain ⟨rfl, ⟨Ψ⟩⟩ := h
  exact ⟨Ψ.toEquiv, IsIsoEquiv.of_iso Ψ, IsIsoEquiv.of_iso Ψ.symm⟩

variable {H' : Type*} [Fintype H'] [DecidableEq H']

/-- The map of the darts of `K` induced by a bijection `Ψ` of the darts of two cuts (the value
`d₀` is a default). -/
private noncomputable def cutDartMap {K : Finset H} {N N' : ℕ} {K' : Finset H'}
    (Ψ : CutDart K N ≃ CutDart K' N') (d₀ : H') (d : H) : H' :=
  if hd : d ∈ K then Sum.elim Subtype.val (fun _ => d₀) (Ψ (.inl ⟨d, hd⟩)) else d₀

variable {b' : ℕ} {X : TripleData H b} {X' : TripleData H' b'} {K : Finset H} {L : List H}
  {K' : Finset H'} {L' : List H'} {s : ℕ}

omit [Fintype H] [Fintype H'] in
/-- A bijection of the darts of two cuts preserving `B` maps the darts over `K` to darts over
`K'`. -/
private theorem cutDartMap_spec {Ψ : CutDart K L.length ≃ CutDart K' L'.length}
    (hΨ : IsIsoEquiv (X.cut K L s) (X'.cut K' L' s) Ψ) (d₀ : H') {d : H} (hd : d ∈ K) :
    ∃ hm : cutDartMap Ψ d₀ d ∈ K', Ψ (.inl ⟨d, hd⟩) = .inl ⟨cutDartMap Ψ d₀ d, hm⟩ := by
  unfold cutDartMap
  rw [dif_pos hd]
  rcases h : Ψ (.inl ⟨d, hd⟩) with y | y
  · exact ⟨y.2, rfl⟩
  · exfalso
    have := (hΨ.mem_bdry_iff (.inl ⟨d, hd⟩)).1
    rw [h, IsCutData.mem_cut_bdry, IsCutData.mem_cut_bdry] at this
    simp at this

/-- A bijection of the darts of two cuts with the properties of an isomorphism maps the leg `g_x`
to the leg `g'_x`. -/
private theorem cutDartMap_getElem (hc : X.IsCutData K L) (hc' : X'.IsCutData K' L')
    (hev : Even L.length) (hlen : L.length = L'.length)
    {Ψ : CutDart K L.length ≃ CutDart K' L'.length}
    (hΨ : IsIsoEquiv (X.cut K L s) (X'.cut K' L' s) Ψ) (d₀ : H') {x : ℕ} (hx : x < L.length) :
    cutDartMap Ψ d₀ L[x] = L'[x]'(by omega) := by
  obtain ⟨r, hr⟩ := cutEndIndex_surjective (H := H) (L := L) (s := s) hev ⟨x, hx⟩
  have hr' : (r : ℕ) < 2 * (L'.length / 2) := by have := r.isLt; omega
  have hend := hΨ.map_endpoint r ⟨r, hr'⟩ rfl
  rw [hc.cut_endpoint, hc'.cut_endpoint, hr] at hend
  have hidx : cutEndIndex L' s ⟨(r : ℕ), hr'⟩ = ⟨x, by omega⟩ := by
    apply Fin.ext
    have := congrArg Fin.val hr
    simp only [cutEndIndex] at this ⊢
    rw [← hlen]
    exact this
  rw [hidx] at hend
  have hmem : Ψ (.inl ⟨L[x], hc.getElem_mem ⟨x, hx⟩⟩) ∈ cutTriple K' L' ⟨x, by omega⟩ := by
    rw [← hend, mem_map_equiv, Equiv.symm_apply_apply]
    simp [cutTriple, hc.cutListDart_eq]
  obtain ⟨hm, he⟩ := cutDartMap_spec hΨ d₀ (hc.getElem_mem ⟨x, hx⟩)
  rw [he] at hmem
  simp only [cutTriple, hc'.cutListDart_eq, mem_insert, mem_singleton, reduceCtorEq,
    or_false, Sum.inl.injEq] at hmem
  exact congrArg Subtype.val hmem

/-- A bijection of the darts of two cuts with the properties of an isomorphism maps darts over
`K` outside `L` (at triple points) to darts over `K'` outside `L'`. -/
private theorem cutDartMap_notMem (hc : X.IsCutData K L) (hc' : X'.IsCutData K' L')
    {Ψ : CutDart K L.length ≃ CutDart K' L'.length}
    (hΨ : IsIsoEquiv (X.cut K L s) (X'.cut K' L' s) Ψ) (d₀ : H') {d : H} (hd : d ∈ K)
    (hdL : d ∉ L) : cutDartMap Ψ d₀ d ∉ L' := by
  obtain ⟨hm, he⟩ := cutDartMap_spec hΨ d₀ hd
  have h1 := hc.cut_not_isBoundaryVertex_vertexOf_inl (s := s) (d := ⟨d, hd⟩) hdL
  rw [← hΨ.isBoundaryVertex_iff, he] at h1
  obtain ⟨y, hyL, hy⟩ := hc'.cut_not_isBoundaryVertex_iff.1 h1
  rw [← Sum.inl_injective hy] at hyL
  exact hyL

/-- The orientation of the darts at the points of an arc: `σ^e(ē_{l+1})` is `out` exactly when
`e` is odd. -/
private theorem isOut_zDart (hX : X.IsTripleDiagram) {i : Fin b} {l : ℕ}
    (hl : l + 1 < X.arcLength i) (e : ℕ) :
    X.isOut (X.zDart i l e) = if Even e then false else true := by
  have hpre := hX.toIsPreTripleDiagram
  have hP := X.isStrandPath_arc hpre (hpre.arcLength_ne_zero i)
  have hmem : X.arcDart i l ∈ X.arc i :=
    List.mem_toFinset.1 (mem_arc_toFinset.2 ⟨l, by omega, rfl⟩)
  have hz := not_isBoundaryVertex_zDart hX hl 0
  simp only [zDart, pow_zero, Equiv.Perm.one_apply] at hz
  unfold zDart
  rw [hpre.isOut_rot_pow_apply hz, hpre.isOut_inv_apply (hP.notMem_bdry _ hmem),
    hP.isOut_eq_true _ hmem]
  split_ifs <;> rfl

/-- The orientation of a leg: `n_r` is `out` exactly at the sources, the positions `2j` of
`Fin (2b)`. -/
private theorem isOut_endDart (hX : X.IsTripleDiagram) (r : Fin (2 * b)) :
    X.isOut (X.endDart r) = decide ((r : ℕ) % 2 = 0) := by
  rcases exists_sourceIndex_or_targetIndex r with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [hX.isOut_source]
    simp
  · rw [hX.isOut_target]
    simp [targetIndex_val]

/-- The endpoint `ε(r)` consists of the darts `σ^e(n_r)`, `e < 3`. -/
private theorem endpoint_eq_image (hX : X.IsTripleDiagram) (r : Fin (2 * b)) :
    X.endpoint r = (range 3).image (X.eDart r) := by
  ext d
  rw [mem_image]
  constructor
  · intro hd
    obtain ⟨k, hk, hkd⟩ := X.exists_pow_apply_eq_of_card_vertexOf (card_endpoint hX r) hd
    exact ⟨k, mem_range.2 hk, hkd⟩
  · rintro ⟨k, -, rfl⟩
    exact X.mem_vertexOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))

variable {i : Fin b}

/-- The map gluing `ψ` along the arc from `s_i`: in coordinates around that arc,
`σ^e(ē_{l+1}) ↦ σ'^e(ē'_{l+1})` and `σ^e(n_r) ↦ σ'^e(n'_r)`; on the remaining darts, `ψ`. -/
private noncomputable def glueFun {b : ℕ} (X : TripleData H b) (X' : TripleData H' b) (i : Fin b)
    (ψ : H → H') (d : H) : H' :=
  open Classical in
  if h : ∃ p : ℕ × ℕ, p.1 + 1 < X.arcLength i ∧ p.2 < 6 ∧ d = X.zDart i p.1 p.2 then
    X'.zDart i (Classical.choose h).1 (Classical.choose h).2
  else if h' : ∃ p : Fin (2 * b) × ℕ, p.2 < 3 ∧ d = X.eDart p.1 p.2 then
    X'.eDart (Classical.choose h').1 (Classical.choose h').2
  else ψ d

private theorem glueFun_zDart {X' : TripleData H' b} (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) (ψ : H → H') {l e : ℕ} (hl : l + 1 < X.arcLength i) (he : e < 6) :
    glueFun X X' i ψ (X.zDart i l e) = X'.zDart i l e := by
  have h : ∃ p : ℕ × ℕ, p.1 + 1 < X.arcLength i ∧ p.2 < 6 ∧
      X.zDart i l e = X.zDart i p.1 p.2 := ⟨(l, e), hl, he, rfl⟩
  rw [glueFun, dif_pos h]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec h
  obtain ⟨e1, e2⟩ := zDart_inj hX hS hl h1 he h2 h3
  rw [← e1, ← e2]

private theorem glueFun_eDart {X' : TripleData H' b} (hX : X.IsTripleDiagram) (ψ : H → H')
    (r : Fin (2 * b)) {e : ℕ} (he : e < 3) :
    glueFun X X' i ψ (X.eDart r e) = X'.eDart r e := by
  have h0 : ¬∃ p : ℕ × ℕ, p.1 + 1 < X.arcLength i ∧ p.2 < 6 ∧
      X.eDart r e = X.zDart i p.1 p.2 := by
    rintro ⟨p, hp, -, hpe⟩
    exact zDart_ne_eDart hX hp p.2 r e hpe.symm
  have h : ∃ p : Fin (2 * b) × ℕ, p.2 < 3 ∧ X.eDart r e = X.eDart p.1 p.2 := ⟨(r, e), he, rfl⟩
  rw [glueFun, dif_neg h0, dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  obtain ⟨e1, e2⟩ := eDart_inj hX he h1 h2
  rw [← e1, ← e2]

private theorem glueFun_of_avoided {X' : TripleData H' b} (hX : X.IsTripleDiagram) (ψ : H → H')
    {d : H} (hint : ¬X.IsBoundaryVertex (X.vertexOf d))
    (hpass : ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) :
    glueFun X X' i ψ d = ψ d := by
  have h0 : ¬∃ p : ℕ × ℕ, p.1 + 1 < X.arcLength i ∧ p.2 < 6 ∧ d = X.zDart i p.1 p.2 := by
    rintro ⟨p, hp, -, rfl⟩
    exact hpass (passesThrough_zDart hX hp p.2)
  have h1 : ¬∃ p : Fin (2 * b) × ℕ, p.2 < 3 ∧ d = X.eDart p.1 p.2 := by
    rintro ⟨p, -, rfl⟩
    exact hint (isBoundaryVertex_eDart hX p.1 p.2)
  rw [glueFun, dif_neg h0, dif_neg h1]

/-- The map `glueFun X X' i (cutDartMap Ψ d₀)` in coordinates, for arcs boundary-parallel along
the same interval of diagrams with the same `π(i)` and a bijection `Ψ` of the darts of their cuts
on the side `η` opposite to `I` with the properties of an isomorphism. -/
private theorem glueFun_spec {X' : TripleData H' b} (hX : X.IsTripleDiagram)
    (hX' : X'.IsTripleDiagram) (hπ : X.strandPerm i = X'.strandPerm i)
    {I : Finset (Fin (2 * b))} (hB : X.IsBoundaryParallel i I)
    (hB' : X'.IsBoundaryParallel i I) {η : StrandSide}
    (hη : η = (intervalSide X.strandPerm i I).opposite)
    {Ψ : CutDart (X.arcSideDarts i η) (X.arcCutList i η).length ≃
      CutDart (X'.arcSideDarts i η) (X'.arcCutList i η).length}
    (hΨ : IsIsoEquiv (X.cut (X.arcSideDarts i η) (X.arcCutList i η) η.cutShift)
      (X'.cut (X'.arcSideDarts i η) (X'.arcCutList i η) η.cutShift) Ψ) (d₀ : H') :
    (∀ l e, l + 1 < X.arcLength i → e < 6 →
      glueFun X X' i (cutDartMap Ψ d₀) (X.zDart i l e) = X'.zDart i l e) ∧
    (∀ r e, e < 3 → glueFun X X' i (cutDartMap Ψ d₀) (X.eDart r e) = X'.eDart r e) ∧
    (∀ d ∈ X.arcSideDarts i η, glueFun X X' i (cutDartMap Ψ d₀) d = cutDartMap Ψ d₀ d) := by
  have hS := hB.2.1
  have hc := hS.isCutData_arcCutList hX η
  have hc' := hB'.2.1.isCutData_arcCutList hX' η
  have hη' : η = (intervalSide X'.strandPerm i I).opposite := by
    rw [hη]; simp only [intervalSide, hπ]
  have hstart : ∀ ζ, X.arcSideStart i ζ = X'.arcSideStart i ζ := by
    intro ζ; cases ζ <;> simp [arcSideStart, arcEndIndex, hπ]
  have hend : ∀ ζ, X.arcSideEnd i ζ = X'.arcSideEnd i ζ := by
    intro ζ; cases ζ <;> simp [arcSideEnd, arcEndIndex, hπ]
  have hint : intervalInterior X.strandPerm i I = intervalInterior X'.strandPerm i I := by
    simp only [intervalInterior, hπ]
  have hm : X.arcLength i = X'.arcLength i := by
    have h1 := hB.two_mul_arcLength_sub_one hX
    have h2 := hB'.two_mul_arcLength_sub_one hX'
    have := hX.toIsPreTripleDiagram.arcLength_ne_zero i
    have := hX'.toIsPreTripleDiagram.arcLength_ne_zero i
    rw [hint] at h1
    omega
  have hlen : (X.arcCutList i η).length = (X'.arcCutList i η).length := by
    have h1 := length_arcCutList_opposite hX hB
    have h2 := length_arcCutList_opposite hX' hB'
    rw [← hη] at h1
    rw [← hη'] at h2
    rw [h1, h2]
  have hlenX : (X.arcCutList i η).length =
      ((X.arcSideEnd i η - X.arcSideStart i η : Fin (2 * b)) : ℕ) - 1 +
        2 * (X.arcLength i - 1) := by
    rw [arcCutList_eq_append, List.length_append, List.length_map, List.length_range,
      length_sideList_arc]
  have hzX := fun l e (hl : l + 1 < X.arcLength i) (he : e < 6) =>
    glueFun_zDart (X' := X') hX hS (cutDartMap Ψ d₀) hl he
  have heX := fun r e (he : e < 3) =>
    glueFun_eDart (X' := X') (i := i) hX (cutDartMap Ψ d₀) r he
  refine ⟨hzX, heX, fun d hd => ?_⟩
  by_cases hdL : d ∈ X.arcCutList i η
  · obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hdL
    rw [cutDartMap_getElem hc hc' (even_length_arcCutList η) hlen hΨ d₀ hx]
    have h1 := getElem?_arcCutList_coord (X := X) (i := i) η hx
    have h2 := getElem?_arcCutList_coord (X := X') (i := i) η (x := x) (by omega)
    rw [← hstart, ← hend, ← hm] at h2
    rw [List.getElem?_eq_getElem hx, Option.some.injEq] at h1
    rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at h2
    rw [h1, h2]
    split_ifs with hxc
    · exact heX _ 0 (by norm_num)
    · apply hzX
      · cases η <;> simp only [sidePoint] <;> omega
      · cases η <;> simp only [sideExp] <;> omega
  · obtain ⟨hint', hpass⟩ := hS.avoided_of_mem_arcSideDarts hX hd hdL
    exact glueFun_of_avoided hX _ (X.mem_internalVertices.1 hint').2 hpass

/-- **Gluing along a boundary-parallel arc.** Let `X, X'` be triple diagrams with `b` arcs and
`π_X(i) = π_{X'}(i)`, let `I` be an interval of `i`, and let the arcs `S` of `X` and `S'` of `X'`
from `s_i` be boundary-parallel along `I`. Let `η` be the side opposite to the side of `I`. If
`X|_{S,η}` is isomorphic to `X'|_{S',η}`, then `X` is isomorphic to `X'`. -/
@[cluster_algebras "lem_boundary_parallel_glue"]
theorem IsBoundaryParallel.isomorphic_of_hIsomorphic_arcCut {X' : TripleData H' b}
    (hX : X.IsTripleDiagram) (hX' : X'.IsTripleDiagram) (hπ : X.strandPerm i = X'.strandPerm i)
    {I : Finset (Fin (2 * b))} (hB : X.IsBoundaryParallel i I)
    (hB' : X'.IsBoundaryParallel i I) {η : StrandSide}
    (hη : η = (intervalSide X.strandPerm i I).opposite)
    (hiso : (X.arcCut i η).HIsomorphic (X'.arcCut i η)) : X.Isomorphic X' := by
  have hπ' : X'.strandPerm i = X.strandPerm i := hπ.symm
  obtain ⟨ζ, hζ⟩ : ∃ ζ, intervalSide X.strandPerm i I = ζ := ⟨_, rfl⟩
  have hζ' : intervalSide X'.strandPerm i I = ζ := by rw [← hζ]; simp only [intervalSide, hπ]
  have hη' : η = (intervalSide X'.strandPerm i I).opposite := by rw [hζ', hη, hζ]
  have hS := hB.2.1
  have hS' := hB'.2.1
  have hc := hS.isCutData_arcCutList hX η
  have hc' := hS'.isCutData_arcCutList hX' η
  have hinv := hX.inv_involutive
  have hinv' := hX'.inv_involutive
  have hstart : ∀ ζ, X.arcSideStart i ζ = X'.arcSideStart i ζ := by
    intro ζ; cases ζ <;> simp [arcSideStart, arcEndIndex, hπ]
  have hend : ∀ ζ, X.arcSideEnd i ζ = X'.arcSideEnd i ζ := by
    intro ζ; cases ζ <;> simp [arcSideEnd, arcEndIndex, hπ]
  have hq : X.arcEndIndex i = X'.arcEndIndex i := by simp [arcEndIndex, hπ]
  have hint : intervalInterior X.strandPerm i I = intervalInterior X'.strandPerm i I := by
    simp only [intervalInterior, hπ]
  have hk := hB.two_mul_arcLength_sub_one hX
  have hm : X.arcLength i = X'.arcLength i := by
    have h2 := hB'.two_mul_arcLength_sub_one hX'
    have := hX.toIsPreTripleDiagram.arcLength_ne_zero i
    have := hX'.toIsPreTripleDiagram.arcLength_ne_zero i
    rw [← hint] at h2
    omega
  have hm1 := hX.toIsPreTripleDiagram.arcLength_ne_zero i
  have hcard := hB.1.card_intervalInterior_eq (X := X)
  rw [hζ] at hcard
  have hlenX : (X.arcCutList i η).length =
      ((X.arcSideEnd i η - X.arcSideStart i η : Fin (2 * b)) : ℕ) - 1 +
        2 * (X.arcLength i - 1) := by
    rw [arcCutList_eq_append, List.length_append, List.length_map, List.length_range,
      length_sideList_arc]
  obtain ⟨Ψ, hΨ, hΨ'⟩ := HIsomorphic.exists_isIsoEquiv
    (Y := X.cut (X.arcSideDarts i η) (X.arcCutList i η) η.cutShift)
    (Y' := X'.cut (X'.arcSideDarts i η) (X'.arcCutList i η) η.cutShift) hiso
  obtain ⟨hθz, hθe, hθK⟩ := glueFun_spec hX hX' hπ hB hB' hη hΨ (X'.arcDart i 0)
  obtain ⟨hθz', hθe', hθK'⟩ := glueFun_spec hX' hX hπ' hB' hB hη' hΨ' (X.arcDart i 0)
  set ψ := cutDartMap Ψ (X'.arcDart i 0) with hψdef
  set ψ' := cutDartMap Ψ.symm (X.arcDart i 0) with hψ'def
  set θ := glueFun X X' i ψ with hθdef
  set θ' := glueFun X' X i ψ' with hθ'def
  -- the map `ψ` of the darts of `H_η(S)`
  have hψspec : ∀ d (hd : d ∈ X.arcSideDarts i η), ∃ hm : ψ d ∈ X'.arcSideDarts i η,
      Ψ (.inl ⟨d, hd⟩) = .inl ⟨ψ d, hm⟩ := fun d hd => cutDartMap_spec hΨ _ hd
  have hψ'spec : ∀ d (hd : d ∈ X'.arcSideDarts i η), ∃ hm : ψ' d ∈ X.arcSideDarts i η,
      Ψ.symm (.inl ⟨d, hd⟩) = .inl ⟨ψ' d, hm⟩ := fun d hd => cutDartMap_spec hΨ' _ hd
  have hψK : ∀ d ∈ X.arcSideDarts i η, ψ d ∈ X'.arcSideDarts i η := fun d hd => (hψspec d hd).1
  have hψ'K : ∀ d ∈ X'.arcSideDarts i η, ψ' d ∈ X.arcSideDarts i η :=
    fun d hd => (hψ'spec d hd).1
  have hψ'ψ : ∀ d ∈ X.arcSideDarts i η, ψ' (ψ d) = d := by
    intro d hd
    obtain ⟨hm', he⟩ := hψspec d hd
    simp only [hψ'def, cutDartMap, dif_pos hm']
    rw [← he, Equiv.symm_apply_apply]
    rfl
  have hψψ' : ∀ d ∈ X'.arcSideDarts i η, ψ (ψ' d) = d := by
    intro d hd
    obtain ⟨hm', he⟩ := hψ'spec d hd
    simp only [hψdef, cutDartMap, dif_pos hm']
    rw [← he, Equiv.apply_symm_apply]
    rfl
  have hψinv : ∀ d ∈ X.arcSideDarts i η, ψ (X.inv d) = X'.inv (ψ d) := by
    intro d hd
    obtain ⟨hm', he⟩ := hψspec d hd
    obtain ⟨hm2, he2⟩ := hψspec (X.inv d) (hc.inv_mem _ hd)
    have := hΨ.map_inv (.inl ⟨d, hd⟩)
    rw [hc.cut_inv_inl hinv, he2, he, hc'.cut_inv_inl hinv'] at this
    exact congrArg Subtype.val (Sum.inl_injective this)
  have hψrot : ∀ d ∈ X.arcSideDarts i η, d ∉ X.arcCutList i η →
      ψ (X.rot d) = X'.rot (ψ d) := by
    intro d hd hdL
    have hdL' := cutDartMap_notMem hc hc' hΨ (X'.arcDart i 0) hd hdL
    obtain ⟨hm', he⟩ := hψspec d hd
    obtain ⟨hm2, he2⟩ := hψspec (X.rot d) (hc.rot_mem hd hdL)
    have := hΨ.map_rot (.inl ⟨d, hd⟩)
    rw [hc.cut_rot_inl_of_notMem ⟨d, hd⟩ hdL, he2, he,
      hc'.cut_rot_inl_of_notMem ⟨ψ d, hm'⟩ hdL'] at this
    exact congrArg Subtype.val (Sum.inl_injective this)
  have hψout : ∀ d ∈ X.arcSideDarts i η, X'.isOut (ψ d) = X.isOut d := by
    intro d hd
    obtain ⟨hm', he⟩ := hψspec d hd
    have := hΨ.map_isOut (.inl ⟨d, hd⟩) (by rw [IsCutData.mem_cut_bdry]; simp)
    rw [he] at this
    exact this
  -- `θ` is a bijection
  have hl' : ∀ l, l + 1 < X.arcLength i → l + 1 < X'.arcLength i := fun l hl => by omega
  have hleft : ∀ d, θ' (θ d) = d := by
    intro d
    rcases dart_cases hX hB d with ⟨l, e, hl, he, rfl⟩ | ⟨r, e, he, rfl⟩ | ⟨hdK, hdL⟩
    · rw [hθz l e hl he, hθz' l e (hl' l hl) he]
    · rw [hθe r e he, hθe' r e he]
    · rw [← hη] at hdK hdL
      rw [hθK d hdK, hθK' _ (hψK d hdK), hψ'ψ d hdK]
  have hright : ∀ d, θ (θ' d) = d := by
    intro d
    rcases dart_cases hX' hB' d with ⟨l, e, hl, he, rfl⟩ | ⟨r, e, he, rfl⟩ | ⟨hdK, hdL⟩
    · rw [hθz' l e hl he, hθz l e (by omega) he]
    · rw [hθe' r e he, hθe r e he]
    · rw [← hη'] at hdK hdL
      rw [hθK' d hdK, hθK _ (hψ'K d hdK), hψψ' d hdK]
  -- the generators of the relation `θ(d̄) = θ(d)̄`
  have key : ∀ d, θ (X.inv d) = X'.inv (θ d) →
      θ (X.inv (X.inv d)) = X'.inv (θ (X.inv d)) := by
    intro d h
    rw [hinv d, h, hinv']
  have gK : ∀ d ∈ X.arcSideDarts i η, θ (X.inv d) = X'.inv (θ d) := fun d hd => by
    rw [hθK _ (hc.inv_mem _ hd), hθK d hd, hψinv d hd]
  have harc : ∀ l, l < X.arcLength i → θ (X.arcDart i l) = X'.arcDart i l := by
    intro l hl
    rcases l with _ | l
    · have := hθe (sourceIndex i) 0 (by norm_num)
      simpa [eDart] using this
    · rw [arcDart_succ_eq hX hl, arcDart_succ_eq hX' (by omega)]
      exact hθz l 3 (by omega) (by norm_num)
  have hinvarc : ∀ l, l < X.arcLength i → θ (X.inv (X.arcDart i l)) = X'.inv (X'.arcDart i l) := by
    intro l hl
    by_cases hl1 : l + 1 < X.arcLength i
    · have := hθz l 0 hl1 (by norm_num)
      simpa [zDart] using this
    · rw [show l = X.arcLength i - 1 by omega, ← endDart_arcEndIndex hX, hm,
        ← endDart_arcEndIndex hX']
      have := hθe (X.arcEndIndex i) 0 (by norm_num)
      simp only [eDart, pow_zero, Equiv.Perm.one_apply] at this
      rw [this, hq]
  have gA : ∀ l, l < X.arcLength i → θ (X.inv (X.arcDart i l)) = X'.inv (θ (X.arcDart i l)) :=
    fun l hl => by rw [hinvarc l hl, harc l hl]
  have gN : ∀ t, t < 2 * (X.arcLength i - 1) →
      θ (X.inv (X.eDart ((finRotate (2 * b) ^ (t + 1)) (X.arcSideStart i ζ)) 0)) =
        X'.inv (θ (X.eDart ((finRotate (2 * b) ^ (t + 1)) (X.arcSideStart i ζ)) 0)) := by
    intro t ht
    have h1 := inv_eDart_interior hX hB hζ ht
    have h2 := inv_eDart_interior hX' hB' hζ' (t := t) (by omega)
    rw [← hstart, ← hm] at h2
    rw [h1, hθz _ _ (by cases ζ <;> simp only [zetaPoint] <;> omega)
      (by cases ζ <;> simp only [zetaExp] <;> omega), hθe _ 0 (by norm_num), ← h2]
  have gE1 : ∀ r, θ (X.inv (X.eDart r 1)) = X'.inv (θ (X.eDart r 1)) := by
    intro r
    rw [inv_eDart_one hX, hθe _ 2 (by norm_num), hθe r 1 (by norm_num), inv_eDart_one hX']
  -- the darts of the side `η` in coordinates
  have hKz : ∀ l j, l + 1 < X.arcLength i → j < 2 * (X.arcLength i - 1) →
      sidePoint η (X.arcLength i) j = l → X.zDart i l (sideExp η j) ∈ X.arcSideDarts i η := by
    intro l j hl hj hjl
    have h := getElem?_arcCutList_coord (X := X) (i := i) η
      (x := ((X.arcSideEnd i η - X.arcSideStart i η : Fin (2 * b)) : ℕ) - 1 + j) (by omega)
    rw [if_neg (by omega), Nat.add_sub_cancel_left, hjl] at h
    exact hc.mem_of_mem_list _ (List.mem_of_getElem? h)
  have hKe : ∀ t, t + 1 < ((X.arcSideEnd i η - X.arcSideStart i η : Fin (2 * b)) : ℕ) →
      X.eDart ((finRotate (2 * b) ^ (t + 1)) (X.arcSideStart i η)) 0 ∈ X.arcSideDarts i η := by
    intro t ht
    have h := getElem?_arcCutList_coord (X := X) (i := i) η (x := t) (by omega)
    rw [if_pos (by omega)] at h
    exact hc.mem_of_mem_list _ (List.mem_of_getElem? h)
  have hηv : η = ζ.opposite := by rw [hη, hζ]
  have hz_gen : ∀ t, t < 2 * (X.arcLength i - 1) → ∀ l e, zetaPoint ζ (X.arcLength i) t = l →
      zetaExp ζ t = e → θ (X.inv (X.zDart i l e)) = X'.inv (θ (X.zDart i l e)) := by
    intro t ht l e h1 h2
    subst h1 h2
    rw [← inv_eDart_interior hX hB hζ ht]
    exact key _ (gN t ht)
  have he_gen : ∀ j, j < 2 * (X.arcLength i - 1) → ∀ l e, l + 1 < X.arcLength i →
      sidePoint η (X.arcLength i) j = l → sideExp η j = e →
        θ (X.inv (X.zDart i l e)) = X'.inv (θ (X.zDart i l e)) := by
    intro j hj l e hl h1 h2
    subst h2
    exact gK _ (hKz l j hl hj h1)
  have hmapinv : ∀ d, θ (X.inv d) = X'.inv (θ d) := by
    intro d
    rcases dart_cases hX hB d with ⟨l, e, hl, he, rfl⟩ | ⟨r, e, he, rfl⟩ | ⟨hdK, -⟩
    · obtain rfl | rfl | rfl | rfl | rfl | rfl :
          e = 0 ∨ e = 3 ∨ e = 1 ∨ e = 2 ∨ e = 4 ∨ e = 5 := by omega
      · have hz : X.zDart i l 0 = X.inv (X.arcDart i l) := by simp [zDart]
        rw [hz]
        exact key _ (gA l (by omega))
      · have hz : X.zDart i l 3 = X.arcDart i (l + 1) := (arcDart_succ_eq hX hl).symm
        rw [hz]
        exact gA (l + 1) hl
      all_goals cases ζ <;> simp only [StrandSide.opposite] at hηv
      · exact hz_gen (2 * (X.arcLength i - 2 - l) + 1) (by omega) l 1
          (by simp only [zetaPoint]; omega) (by simp only [zetaExp]; omega)
      · exact he_gen (2 * l) (by omega) l 1 hl (by rw [hηv]; simp only [sidePoint]; omega)
          (by rw [hηv]; simp only [sideExp]; omega)
      · exact hz_gen (2 * (X.arcLength i - 2 - l)) (by omega) l 2
          (by simp only [zetaPoint]; omega) (by simp only [zetaExp]; omega)
      · exact he_gen (2 * l + 1) (by omega) l 2 hl (by rw [hηv]; simp only [sidePoint]; omega)
          (by rw [hηv]; simp only [sideExp]; omega)
      · exact he_gen (2 * (X.arcLength i - 2 - l)) (by omega) l 4 hl
          (by rw [hηv]; simp only [sidePoint]; omega) (by rw [hηv]; simp only [sideExp]; omega)
      · exact hz_gen (2 * l + 1) (by omega) l 4
          (by simp only [zetaPoint]; omega) (by simp only [zetaExp]; omega)
      · exact he_gen (2 * (X.arcLength i - 2 - l) + 1) (by omega) l 5 hl
          (by rw [hηv]; simp only [sidePoint]; omega) (by rw [hηv]; simp only [sideExp]; omega)
      · exact hz_gen (2 * l) (by omega) l 5
          (by simp only [zetaPoint]; omega) (by simp only [zetaExp]; omega)
    · obtain rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 := by omega
      · by_cases hp : r = sourceIndex i
        · subst hp
          have hz : X.eDart (sourceIndex i) 0 = X.arcDart i 0 := by simp [eDart]
          rw [hz]
          exact gA 0 (by omega)
        by_cases hq' : r = X.arcEndIndex i
        · subst hq'
          have hz : X.eDart (X.arcEndIndex i) 0 = X.inv (X.arcDart i (X.arcLength i - 1)) := by
            simp only [eDart, pow_zero, Equiv.Perm.one_apply]
            exact endDart_arcEndIndex hX i
          rw [hz]
          exact key _ (gA _ (by omega))
        rcases exists_eq_finRotate_pow_arcSideStart hp hq' ζ with ⟨u, hu, rfl⟩ | ⟨t, ht, rfl⟩
        · exact gN u (by omega)
        · rw [← hηv] at ht ⊢
          exact gK _ (hKe t ht)
      · exact gE1 r
      · have hz : X.eDart r 2 = X.inv (X.eDart ((finRotate (2 * b)).symm r) 1) := by
          rw [inv_eDart_one hX, Equiv.apply_symm_apply]
        rw [hz]
        exact key _ (gE1 _)
    · rw [← hη] at hdK
      exact gK d hdK
  have hmaprot : ∀ d, θ (X.rot d) = X'.rot (θ d) := by
    intro d
    rcases dart_cases hX hB d with ⟨l, e, hl, he, rfl⟩ | ⟨r, e, he, rfl⟩ | ⟨hdK, hdL⟩
    · rw [rot_zDart hX hl, hθz l _ hl (Nat.mod_lt _ (by norm_num)), hθz l e hl he,
        rot_zDart hX' (hl' l hl)]
    · rw [rot_eDart hX, hθe r _ (Nat.mod_lt _ (by norm_num)), hθe r e he, rot_eDart hX']
    · rw [← hη] at hdK hdL
      rw [hθK _ (hc.rot_mem hdK hdL), hθK d hdK, hψrot d hdK hdL]
  have hmapbdry : ∀ d, θ d ∈ X'.bdry ↔ d ∈ X.bdry := by
    intro d
    rcases dart_cases hX hB d with ⟨l, e, hl, he, rfl⟩ | ⟨r, e, he, rfl⟩ | ⟨hdK, hdL⟩
    · rw [hθz l e hl he]
      exact iff_of_false
        (fun h => not_isBoundaryVertex_zDart hX' (hl' l hl) e ⟨_, X'.self_mem_vertexOf _, h⟩)
        (fun h => not_isBoundaryVertex_zDart hX hl e ⟨_, X.self_mem_vertexOf _, h⟩)
    · rw [hθe r e he, eDart_mem_bdry_iff hX' r he, eDart_mem_bdry_iff hX r he]
    · rw [← hη] at hdK hdL
      rw [hθK d hdK]
      exact iff_of_false (hc'.notMem_bdry _ (hψK d hdK)) (hc.notMem_bdry _ hdK)
  have hmapout : ∀ d, d ∉ X.bdry → X'.isOut (θ d) = X.isOut d := by
    intro d hdB
    rcases dart_cases hX hB d with ⟨l, e, hl, he, rfl⟩ | ⟨r, e, he, rfl⟩ | ⟨hdK, hdL⟩
    · rw [hθz l e hl he, isOut_zDart hX hl, isOut_zDart hX' (hl' l hl)]
    · obtain rfl : e = 0 := by_contra fun h => hdB ((eDart_mem_bdry_iff hX r he).2 h)
      rw [hθe r 0 he]
      simp only [eDart, pow_zero, Equiv.Perm.one_apply]
      rw [isOut_endDart hX, isOut_endDart hX']
    · rw [← hη] at hdK
      rw [hθK d hdK, hψout d hdK]
  let E : H ≃ H' := ⟨θ, θ', hleft, hright⟩
  have hmapend : ∀ r, (X.endpoint r).map E.toEmbedding = X'.endpoint r := by
    intro r
    rw [endpoint_eq_image hX, endpoint_eq_image hX', Finset.map_eq_image, Finset.image_image]
    exact Finset.image_congr fun e he => hθe r e (mem_range.1 he)
  exact ⟨⟨E, hmapinv, hmaprot, hmapbdry, hmapout, hmapend⟩⟩

end Glue

/-! ### Boundary-parallel arcs of a cut, read in the cut diagram -/

section CutShape

variable {α : Type*} [Fintype α] [DecidableEq α] {n₀ : ℕ} {Z : TripleData α n₀}

/-- **The shape of a boundary-parallel arc of a cut**, read in the diagram `Z` that is cut: let
`Q = (f₁, …, f_n)` be an arc of `Z.cut K L s` (its darts are the `Sum.inl f_l`) that is
boundary-parallel along `I'`. Then `Q` is a strand path of `Z` with the leg `L[x₁]` as first dart
and `L[x₂]` as reverse of its last dart (`x₁, x₂` the indices of its two ends), its interior
points are pairwise distinct triple points, and either `I'` runs clockwise from the source of
`Q` and `L[x₁ + 2l + 1]̄ = σ⁵ f̄_{l+1}`, `L[x₁ + 2l + 2]̄ = σ⁴ f̄_{l+1}`, or `I'` runs clockwise
from its target and `L[x₂ + 2l + 1]̄ = σ² f̄_{n-1-l}`, `L[x₂ + 2l + 2]̄ = σ f̄_{n-1-l}` (indices
modulo the length of `L`). -/
private theorem bp_cut_shape (hZ : Z.IsPreTripleDiagram) {K : Finset α} {L : List α} {s : ℕ}
    (hc : Z.IsCutData K L) (hev : Even L.length) (hY : (Z.cut K L s).IsTripleDiagram)
    {Q : List {d // d ∈ K}} {j : Fin (L.length / 2)} (hQ : Q.map Sum.inl = (Z.cut K L s).arc j)
    {I' : Finset (Fin (2 * (L.length / 2)))} (hB : (Z.cut K L s).IsBoundaryParallel j I') :
    0 < Q.length ∧ Z.IsStrandPath (Q.map Subtype.val) ∧
    2 * (Q.length - 1) = (intervalInterior (Z.cut K L s).strandPerm j I').card ∧
    L[(cutEndIndex L s (sourceIndex j) : ℕ)]? = (Q.map Subtype.val).head? ∧
    L[(cutEndIndex L s ((Z.cut K L s).arcEndIndex j) : ℕ)]? =
      (Q.map Subtype.val).getLast?.map Z.inv ∧
    (∀ l (hl : l + 1 < Q.length), Z.inv (Q[l]'(by omega)).1 ∉ L ∧
      ¬Z.IsBoundaryVertex (Z.vertexOf (Z.inv (Q[l]'(by omega)).1))) ∧
    (∀ l l' (hl : l + 1 < Q.length) (hl' : l' + 1 < Q.length),
      Z.vertexOf (Z.inv (Q[l]'(by omega)).1) = Z.vertexOf (Z.inv (Q[l']'(by omega)).1) →
        l = l') ∧
    ((I' = cyclicIcc (sourceIndex j) ((Z.cut K L s).arcEndIndex j) ∧
      (∀ r, r ∈ intervalInterior (Z.cut K L s).strandPerm j I' ↔
        ∃ u, u < 2 * (Q.length - 1) ∧ r = (finRotate _ ^ (u + 1)) (sourceIndex j)) ∧
      ∀ l (hl : l + 1 < Q.length),
        L[((cutEndIndex L s (sourceIndex j) : ℕ) + (2 * l + 1)) % L.length]?.map Z.inv =
          some ((Z.rot ^ 5) (Z.inv (Q[l]'(by omega)).1)) ∧
        L[((cutEndIndex L s (sourceIndex j) : ℕ) + (2 * l + 2)) % L.length]?.map Z.inv =
          some ((Z.rot ^ 4) (Z.inv (Q[l]'(by omega)).1))) ∨
     (I' = cyclicIcc ((Z.cut K L s).arcEndIndex j) (sourceIndex j) ∧
      (∀ r, r ∈ intervalInterior (Z.cut K L s).strandPerm j I' ↔
        ∃ u, u < 2 * (Q.length - 1) ∧ r = (finRotate _ ^ (u + 1)) ((Z.cut K L s).arcEndIndex j)) ∧
      ∀ l (hl : l + 1 < Q.length),
        L[((cutEndIndex L s ((Z.cut K L s).arcEndIndex j) : ℕ) + (2 * l + 1)) % L.length]?.map
          Z.inv = some ((Z.rot ^ 2) (Z.inv (Q[Q.length - 2 - l]'(by omega)).1)) ∧
        L[((cutEndIndex L s ((Z.cut K L s).arcEndIndex j) : ℕ) + (2 * l + 2)) % L.length]?.map
          Z.inv = some (Z.rot (Z.inv (Q[Q.length - 2 - l]'(by omega)).1)))) := by
  set Y := Z.cut K L s with hYdef
  have hinv := hZ.inv_involutive
  have hYp := hY.toIsPreTripleDiagram
  have hlen : Y.arcLength j = Q.length := by rw [← length_arc, ← hQ, List.length_map]
  have hn1 : 0 < Q.length := by have := hYp.arcLength_ne_zero j; omega
  have hdart : ∀ l (hl : l < Q.length), Y.arcDart j l = .inl Q[l] := fun l hl =>
    arcDart_eq_of_map_eq_arc hQ hl
  have hinvQ : ∀ l (hl : l + 1 < Q.length), Z.inv Q[l].1 ∉ L ∧
      Y.inv (Y.arcDart j l) = .inl ⟨Z.inv Q[l].1, hc.inv_mem _ Q[l].2⟩ := by
    intro l hl
    have hYi : Y.inv (Y.arcDart j l) = .inl ⟨Z.inv Q[l].1, hc.inv_mem _ Q[l].2⟩ := by
      rw [hdart l (by omega), hYdef, hc.cut_inv_inl hinv]
    refine ⟨?_, hYi⟩
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (hYp.arcLength_ne_zero j)
    have h := (Y.arcLength_eq_succ_iff.1 hm).2 l (by omega)
    unfold RunsToEndpoint at h
    rw [hYi] at h
    obtain ⟨d, hdL, hd⟩ := hc.cut_not_isBoundaryVertex_iff.1 h
    rwa [← Sum.inl_injective hd] at hdL
  have hrotQ : ∀ l (hl : l + 1 < Q.length) (k : ℕ), ∃ hm : (Z.rot ^ k) (Z.inv Q[l].1) ∈ K,
      (Y.rot ^ k) (Y.inv (Y.arcDart j l)) = .inl ⟨(Z.rot ^ k) (Z.inv Q[l].1), hm⟩ := by
    intro l hl k
    obtain ⟨h1, -, h2⟩ := hc.cut_rot_pow_inl_of_notMem (s := s) ⟨Z.inv Q[l].1, hc.inv_mem _ Q[l].2⟩
      (hinvQ l hl).1 k
    exact ⟨h1, by rwa [(hinvQ l hl).2]⟩
  have hleg : ∀ r, Y.endDart r = .inl ⟨L[(cutEndIndex L s r : ℕ)], hc.getElem_mem _⟩ := by
    intro r
    rw [hYdef, cut_endDart, hc.cutListDart_eq]
  have hlegInv : ∀ r, Y.inv (Y.endDart r) =
      .inl ⟨Z.inv L[(cutEndIndex L s r : ℕ)], hc.inv_mem _ (hc.getElem_mem _)⟩ := by
    intro r
    rw [hleg, hYdef, hc.cut_inv_inl hinv]
  have hrel : ∀ (r : Fin (2 * (L.length / 2))) l (hl : l + 1 < Q.length) (k : ℕ),
      Y.inv (Y.endDart r) = (Y.rot ^ k) (Y.inv (Y.arcDart j l)) →
        L[(cutEndIndex L s r : ℕ)]?.map Z.inv = some ((Z.rot ^ k) (Z.inv Q[l].1)) := by
    intro r l hl k h
    obtain ⟨hm, hr⟩ := hrotQ l hl k
    rw [hlegInv, hr] at h
    rw [List.getElem?_eq_getElem (cutEndIndex L s r).isLt, Option.map_some]
    exact congrArg some (congrArg Subtype.val (Sum.inl_injective h))
  have hpos : ∀ (r : Fin (2 * (L.length / 2))) (t : ℕ),
      (cutEndIndex L s ((finRotate _ ^ t) r) : ℕ) = ((cutEndIndex L s r : ℕ) + t) % L.length :=
    fun r t => val_cutEndIndex_finRotate_pow hev r t
  have hQX : Z.IsStrandPath (Q.map Subtype.val) := by
    have hA := Y.isStrandPath_arc hYp (hYp.arcLength_ne_zero j)
    rw [← hQ] at hA
    obtain ⟨Q', hQ', hQ'X⟩ := hc.exists_isStrandPath_of_isStrandPath_cut hZ hA
    rwa [(List.map_injective_iff.2 Sum.inl_injective) hQ']
  have hcardI := hB.two_mul_arcLength_sub_one hY
  rw [hlen] at hcardI
  have hNe : NeZero (2 * (L.length / 2)) := ⟨by have := hYp.one_le; omega⟩
  refine ⟨hn1, hQX, hcardI, ?_, ?_, fun l hl => ⟨(hinvQ l hl).1, hc.not_isBoundaryVertex _
    (hc.inv_mem _ Q[l].2) (hinvQ l hl).1⟩, fun l l' hl hl' h => ?_, ?_⟩
  · rw [List.head?_map, List.head?_eq_getElem?, List.getElem?_eq_getElem hn1,
      List.getElem?_eq_getElem (cutEndIndex _ _ _).isLt]
    have h := hleg (sourceIndex j)
    rw [show Y.endDart (sourceIndex j) = Y.arcDart j 0 from rfl, hdart 0 hn1] at h
    exact congrArg some (congrArg Subtype.val (Sum.inl_injective h)).symm
  · rw [List.getLast?_map, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (l := Q) (by omega),
      List.getElem?_eq_getElem (cutEndIndex _ _ _).isLt]
    have h := hleg (Y.arcEndIndex j)
    rw [endDart_arcEndIndex hY j, hlen, hdart _ (by omega), hYdef, hc.cut_inv_inl hinv] at h
    exact congrArg some (congrArg Subtype.val (Sum.inl_injective h)).symm
  · have hS := hB.2.1 l l' (by rw [hlen]; omega) (by rw [hlen]; omega)
    rw [(hinvQ l hl).2, (hinvQ l' hl').2, hYdef,
      hc.cut_vertexOf_inl_of_notMem _ (hinvQ l hl).1,
      hc.cut_vertexOf_inl_of_notMem _ (hinvQ l' hl').1] at hS
    exact hS (by rw [h])
  rcases hB.1 with hI1 | hI2
  · left
    have hcI : (intervalInterior Y.strandPerm j I').card + 2 =
        ((Y.arcEndIndex j - sourceIndex j : Fin (2 * (L.length / 2))) : ℕ) + 1 := by
      rw [hB.1.card_intervalInterior, hI1, card_cyclicIcc]
      rfl
    refine ⟨hI1, fun r => ?_, fun l hl => ?_⟩
    · rw [intervalInterior, hI1, mem_cyclicIcc_sdiff_iff]
      change (∃ t, t + 1 < ((Y.arcEndIndex j - sourceIndex j : Fin _) : ℕ) ∧ _) ↔ _
      constructor <;> rintro ⟨t, ht, rfl⟩ <;> exact ⟨t, by omega, rfl⟩
    · have hjl : l + 1 < Y.arcLength j := by rwa [hlen]
      obtain ⟨hs5, hs4⟩ := hB.inv_endDart_of_eq_cyclicIcc hY hI1 hjl
      have e5 := hrel _ l hl 5 hs5
      have e4 := hrel _ l hl 4 hs4
      rw [hpos] at e5 e4
      exact ⟨e5, e4⟩
  · right
    have hcI : (intervalInterior Y.strandPerm j I').card + 2 =
        ((sourceIndex j - Y.arcEndIndex j : Fin (2 * (L.length / 2))) : ℕ) + 1 := by
      rw [hB.1.card_intervalInterior, hI2, card_cyclicIcc]
      rfl
    refine ⟨hI2, fun r => ?_, fun l hl => ?_⟩
    · rw [intervalInterior, hI2, pair_comm, mem_cyclicIcc_sdiff_iff]
      change (∃ t, t + 1 < ((sourceIndex j - Y.arcEndIndex j : Fin _) : ℕ) ∧ _) ↔ _
      constructor <;> rintro ⟨t, ht, rfl⟩ <;> exact ⟨t, by omega, rfl⟩
    · have hjl : l + 1 < Y.arcLength j := by rwa [hlen]
      obtain ⟨hs2, hs1⟩ := hB.inv_endDart_of_eq_cyclicIcc' hY hI2 hjl
      rw [hlen] at hs2 hs1
      rw [← pow_one Y.rot] at hs1
      have e2 := hrel _ (Q.length - 2 - l) (by omega) 2 hs2
      have e1 := hrel _ (Q.length - 2 - l) (by omega) 1 hs1
      rw [hpos] at e2 e1
      rw [pow_one] at e1
      exact ⟨e2, e1⟩

/-- An arc through a dart `d` that lies at an endpoint and whose reverse lies at an endpoint is
the single dart `d` or `d̄`. -/
private theorem arc_eq_single (hZ : Z.IsPreTripleDiagram) {j : Fin n₀} {d : α}
    (hd : d ∈ Z.arcDarts j) (hb : Z.IsBoundaryVertex (Z.vertexOf d))
    (hb' : Z.IsBoundaryVertex (Z.vertexOf (Z.inv d))) :
    Z.arcLength j = 1 ∧ (Z.endDart (sourceIndex j) = d ∨ Z.endDart (sourceIndex j) = Z.inv d) := by
  have hinv := hZ.inv_involutive
  have key : ∀ e, e ∈ Z.arc j → Z.IsBoundaryVertex (Z.vertexOf e) →
      Z.IsBoundaryVertex (Z.vertexOf (Z.inv e)) →
        Z.arcLength j = 1 ∧ Z.endDart (sourceIndex j) = e := by
    intro e he hbe hbe'
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (hZ.arcLength_ne_zero j)
    obtain ⟨k, hk, rfl⟩ := mem_arc_toFinset.1 (List.mem_toFinset.2 he)
    rcases k with _ | k
    · refine ⟨(Z.arcLength_eq_succ_iff (m := 0)).2 ⟨hbe', fun k hk => absurd hk
        (Nat.not_lt_zero _)⟩, rfl⟩
    · exact absurd hbe (Z.strandStep_arcDart hm (k := k) (by omega)).not_isBoundaryVertex
  rcases mem_union.1 hd with h | h
  · obtain ⟨h1, h2⟩ := key d (List.mem_toFinset.1 h) hb hb'
    exact ⟨h1, Or.inl h2⟩
  · obtain ⟨e, he, rfl⟩ := mem_image.1 h
    rw [hinv] at hb'
    obtain ⟨h1, h2⟩ := key e (List.mem_toFinset.1 he) hb' hb
    exact ⟨h1, Or.inr (by rw [hinv]; exact h2)⟩

end CutShape

section NestedCut

variable {X : TripleData H b}

/-- The cut list of a single-dart arc of a cut: let `A` be an arc of `Y = X.cut K L s` consisting
of one dart, with its two ends at the legs `g_{t-1}` and `g_c` of `Y` (`t - 1 < t < c` indices of
`L`), and let `θ` be the side of `A` containing the leg `g_t`. Then the `θ` cut list of `A` is
`(g_t, …, g_{c-1})`. -/
private theorem arcCutList_of_single {K : Finset H} {L : List H} {s : ℕ} (hc : X.IsCutData K L)
    (hev : Even L.length) (hY : (X.cut K L s).IsTripleDiagram) {j₀ : Fin (L.length / 2)}
    (hlen : (X.cut K L s).arcLength j₀ = 1) {t c : ℕ} (ht : 1 ≤ t) (htc : t < c)
    (hcN : c < L.length)
    (hends : ((cutEndIndex L s (sourceIndex j₀) : ℕ) = t - 1 ∧
        (cutEndIndex L s ((X.cut K L s).arcEndIndex j₀) : ℕ) = c) ∨
      ((cutEndIndex L s (sourceIndex j₀) : ℕ) = c ∧
        (cutEndIndex L s ((X.cut K L s).arcEndIndex j₀) : ℕ) = t - 1))
    {θ : StrandSide}
    (hθ : (Sum.inl ⟨L[t]'(by omega), hc.getElem_mem ⟨t, by omega⟩⟩ : CutDart K L.length) ∈
      (X.cut K L s).arcSideDarts j₀ θ) :
    ((X.cut K L s).arcCutList j₀ θ).length = c - t ∧
      ∀ u (hu : u < c - t), ((X.cut K L s).arcCutList j₀ θ)[u]? =
        some (Sum.inl ⟨L[t + u]'(by omega), hc.getElem_mem ⟨t + u, by omega⟩⟩) := by
  set Y := X.cut K L s with hYdef
  have hS₀ : Y.IsSimpleArc j₀ := fun k l hk hl _ => by omega
  have hleg : ∀ r, Y.endDart r = .inl ⟨L[(cutEndIndex L s r : ℕ)], hc.getElem_mem _⟩ := by
    intro r
    rw [hYdef, cut_endDart, hc.cutListDart_eq]
  have hNpos : 2 * (L.length / 2) = L.length := by obtain ⟨u, hu⟩ := hev; omega
  have hpos := fun r m => val_cutEndIndex_finRotate_pow (H := H) (s := s) hev r m
  -- the position of `g_t` is on side `θ`
  obtain ⟨rt, hrt⟩ := cutEndIndex_surjective (H := H) (L := L) (s := s) hev ⟨t, by omega⟩
  have hrtv : (cutEndIndex L s rt : ℕ) = t := by rw [hrt]
  have hp : rt ≠ sourceIndex j₀ := by
    rintro rfl
    rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hq : rt ≠ Y.arcEndIndex j₀ := by
    rintro rfl
    rcases hends with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega
  have hrun : ∃ u, u + 1 < ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ) ∧
      rt = (finRotate _ ^ (u + 1)) (Y.arcSideStart j₀ θ) := by
    rcases exists_eq_finRotate_pow_arcSideStart (X := Y) hp hq θ with h | ⟨u, hu, hru⟩
    · exact h
    · exfalso
      have hmem := getElem?_arcCutList_of_lt (X := Y) (i := j₀) θ.opposite hu
      have hK := (hS₀.isCutData_arcCutList hY θ.opposite).mem_of_mem_list _
        (List.mem_of_getElem? hmem)
      rw [← hru, hleg, show (⟨L[(cutEndIndex L s rt : ℕ)], hc.getElem_mem _⟩ : {d // d ∈ K}) =
        ⟨L[t]'(by omega), hc.getElem_mem ⟨t, by omega⟩⟩ from Subtype.ext (by simp only [hrt])]
        at hK
      exact disjoint_left.1 (disjoint_arcSideDarts_opposite (X := Y) (i := j₀) θ) hθ hK
  obtain ⟨ut, hut, hrt'⟩ := hrun
  -- the ends of the run of side `θ`
  have hAE : (cutEndIndex L s (Y.arcSideStart j₀ θ) : ℕ) = t - 1 ∧
      (cutEndIndex L s (Y.arcSideEnd j₀ θ) : ℕ) = c := by
    have hd := (Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _).isLt
    have hE := hpos (Y.arcSideStart j₀ θ) ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ)
    rw [finRotate_pow_val_sub'] at hE
    have hR := hpos (Y.arcSideStart j₀ θ) (ut + 1)
    rw [← hrt', hrtv] at hR
    have hcases : ((cutEndIndex L s (Y.arcSideStart j₀ θ) : ℕ) = t - 1 ∧
        (cutEndIndex L s (Y.arcSideEnd j₀ θ) : ℕ) = c) ∨
        ((cutEndIndex L s (Y.arcSideStart j₀ θ) : ℕ) = c ∧
        (cutEndIndex L s (Y.arcSideEnd j₀ θ) : ℕ) = t - 1) := by
      cases θ <;> simp only [arcSideStart, arcSideEnd, arcEndIndex] at hends ⊢ <;> tauto
    rcases hcases with h | ⟨h1, h2⟩
    · exact h
    · exfalso
      rw [h1] at hE hR
      rw [h2] at hE
      rcases Nat.lt_or_ge (c + ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ))
        L.length with h3 | h3
      · rw [Nat.mod_eq_of_lt h3] at hE; omega
      · rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)] at hE
        rcases Nat.lt_or_ge (c + (ut + 1)) L.length with h4 | h4
        · rw [Nat.mod_eq_of_lt h4] at hR; omega
        · rw [Nat.mod_eq_sub_mod h4, Nat.mod_eq_of_lt (by omega)] at hR; omega
  have hd₀ : ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ) = c - t + 1 := by
    have hd := (Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _).isLt
    have hE := hpos (Y.arcSideStart j₀ θ) ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ)
    rw [finRotate_pow_val_sub', hAE.1, hAE.2] at hE
    rcases Nat.lt_or_ge (t - 1 + ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ))
      L.length with h3 | h3
    · rw [Nat.mod_eq_of_lt h3] at hE; omega
    · rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)] at hE; omega
  have hsl : Y.sideList θ (Y.arc j₀) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [length_sideList_arc, hlen]
  refine ⟨?_, fun u hu => ?_⟩
  · rw [arcCutList_eq_append, hsl, List.append_nil, List.length_map, List.length_range, hd₀]
    omega
  · rw [arcCutList_eq_append, hsl, List.append_nil, List.getElem?_map,
      List.getElem?_range (by omega), Option.map_some, hleg]
    congr 3
    have := hpos (Y.arcSideStart j₀ θ) (u + 1)
    rw [hAE.1, Nat.mod_eq_of_lt (by omega)] at this
    simp only [this]
    congr 1
    omega

end NestedCut


/-! ### Rails from boundary-parallel strands (the combing step) -/

section StepTwoRail

variable {X : TripleData H b} {i : Fin b}

/-- The points of a rail built along the `ζ` list `(λ₀, λ₁, …)` of a simple arc from the entries
`λ_{base}, λ_{base+2}, …, λ_{base+2r}` (the points `x_j = v(λ_{base+2j})`) and darts
`η_{1,0}, …, η_{r,0}` at triple points avoided by the arc are pairwise distinct triple points. -/
private theorem railPoints_aux (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) {ζ : StrandSide}
    {base r : ℕ} (hbase : Even base)
    (hlen : base + 2 * r + 1 < (X.sideList ζ (X.arc i)).length) (eta : ℕ → H)
    (heta_int : ∀ l, 1 ≤ l → l ≤ r → ¬X.IsBoundaryVertex (X.vertexOf (eta l)))
    (heta_inj : ∀ l l', 1 ≤ l → l ≤ r → 1 ≤ l' → l' ≤ r →
      X.vertexOf (eta l) = X.vertexOf (eta l') → l = l')
    (heta_avoid : ∀ l, 1 ≤ l → l ≤ r → ∀ e ∈ X.arc i,
      X.vertexOf (eta l) ≠ X.vertexOf e ∧ X.vertexOf (eta l) ≠ X.vertexOf (X.inv e)) (d₀ : H) :
    (∀ a ∈ RailLabel.pointSet r r, X.vertexOf (Sum.elim
      (fun j => X.rot.symm ((X.sideList ζ (X.arc i)).getD (base + 2 * j) d₀)) eta a) ∈
        X.internalVertices) ∧
    Set.InjOn (fun a => X.vertexOf (Sum.elim
      (fun j => X.rot.symm ((X.sideList ζ (X.arc i)).getD (base + 2 * j) d₀)) eta a))
      (RailLabel.pointSet r r) := by
  have hlenΛ := length_sideList_arc (X := X) (i := i) ζ
  have hvx : ∀ j, j ≤ r → X.vertexOf (X.rot.symm ((X.sideList ζ (X.arc i)).getD (base + 2 * j)
      d₀)) = X.vertexOf (X.inv (X.arcDart i (sidePoint ζ (X.arcLength i) (base + 2 * j)))) := by
    intro j hj
    have hk : base + 2 * j < (X.sideList ζ (X.arc i)).length := by omega
    have h1 : X.vertexOf (X.rot.symm ((X.sideList ζ (X.arc i)).getD (base + 2 * j) d₀)) =
        X.vertexOf ((X.sideList ζ (X.arc i)).getD (base + 2 * j) d₀) := by
      conv_rhs => rw [← Equiv.apply_symm_apply X.rot ((X.sideList ζ (X.arc i)).getD _ d₀)]
      rw [X.vertexOf_rot]
    rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some,
      getElem_sideList' hk, X.vertexOf_rot_pow_apply, getElem_arc, length_arc]
  have hsp : ∀ j, j ≤ r → sidePoint ζ (X.arcLength i) (base + 2 * j) + 1 < X.arcLength i := by
    intro j hj
    have := sidePoint_lt (X := X) (P := X.arc i) (ζ := ζ) (k := base + 2 * j) (by omega)
    rwa [length_arc] at this
  obtain ⟨c, hc⟩ := hbase
  refine ⟨fun a ha => ?_, fun a ha a' ha' h => ?_⟩
  · rcases a with j | l <;> simp only [RailLabel.pointSet, Finset.inl_mem_disjSum,
      Finset.inr_mem_disjSum, mem_range, mem_Icc] at ha <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · rw [hvx j (by omega)]
      have := not_isBoundaryVertex_zDart hX (hsp j (by omega)) 0
      simp only [zDart, pow_zero, Equiv.Perm.one_apply] at this
      exact X.vertexOf_mem_internalVertices.2 this
    · exact X.vertexOf_mem_internalVertices.2 (heta_int l ha.1 ha.2)
  · simp only [mem_coe] at ha ha'
    rcases a with j | l <;> rcases a' with j' | l' <;> simp only [RailLabel.pointSet,
      Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, mem_range, mem_Icc] at ha ha' <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [hvx j (by omega), hvx j' (by omega)] at h
      have := hS _ _ (hsp j (by omega)) (hsp j' (by omega)) h
      congr 1
      cases ζ <;> simp only [sidePoint] at this <;> omega
    · exfalso
      rw [hvx j (by omega)] at h
      exact (heta_avoid l' ha'.1 ha'.2 _ (List.mem_toFinset.1 (mem_arc_toFinset.2
        ⟨_, hsp j (by omega) |>.trans' (Nat.lt_succ_self _), rfl⟩))).2 h.symm
    · exfalso
      rw [hvx j' (by omega)] at h
      exact (heta_avoid l ha.1 ha.2 _ (List.mem_toFinset.1 (mem_arc_toFinset.2
        ⟨_, hsp j' (by omega) |>.trans' (Nat.lt_succ_self _), rfl⟩))).2 h
    · congr 1
      exact heta_inj l l' ha.1 ha.2 ha'.1 ha'.2 h

omit [Fintype H] [DecidableEq H] in
private theorem rot_pow_succ_symm_apply (X : TripleData H b) (k : ℕ) (y : H) :
    (X.rot ^ (k + 1)) (X.rot.symm y) = (X.rot ^ k) y := by
  rw [pow_succ, Equiv.Perm.mul_apply, Equiv.apply_symm_apply]

/-- Consecutive entries of the `ζ` list of an arc, with `getD`. -/
private theorem sideList_steps (hX : X.IsTripleDiagram) (ζ : StrandSide) (d₀ : H) :
    (∀ v, Even v → v + 1 < (X.sideList ζ (X.arc i)).length →
      (X.sideList ζ (X.arc i))[v + 1]? = some (X.rot ((X.sideList ζ (X.arc i)).getD v d₀))) ∧
    (∀ v, Even v → v + 2 < (X.sideList ζ (X.arc i)).length →
      X.inv ((X.rot ^ 2) ((X.sideList ζ (X.arc i)).getD v d₀)) =
        X.rot.symm ((X.sideList ζ (X.arc i)).getD (v + 2) d₀)) := by
  have hpre := hX.toIsPreTripleDiagram
  have hP := X.isStrandPath_arc hpre (hpre.arcLength_ne_zero i)
  have hlenΛ := length_sideList_arc (X := X) (i := i) ζ
  refine ⟨fun v hv hv1 => ?_, fun v hv hv2 => ?_⟩
  · obtain ⟨c, rfl⟩ := hv
    obtain ⟨l, hl, lam, h1, h2, -, -⟩ := exists_getElem?_sideList hP ζ (u := c)
      (by rw [length_arc]; omega)
    rw [show c + c = 2 * c by ring, List.getD_eq_getElem?_getD, h1]
    exact h2
  · obtain ⟨c, rfl⟩ := hv
    obtain ⟨lam, lam', h1, h2, h3⟩ := inv_rot_pow_two_getElem?_sideList hpre hP ζ (u := c)
      (by rw [length_arc]; omega)
    rw [show c + c = 2 * c by ring, List.getD_eq_getElem?_getD, h1,
      List.getD_eq_getElem?_getD, h2]
    exact h3

/-- **A rail from relations along the side list**: let `(λ₀, λ₁, …)` be the `ζ` list of a simple
arc `S` and `η_{1,0}, …, η_{r,0}` (`r ≥ 1`) darts at pairwise distinct triple points avoided by
`S`, with `η_{l,k} = σ^k(η_{l,0})`, such that `λ̄_w = η_{1,0}`, `λ̄_{w+2l-1} = η_{l,5}` and
`λ̄_{w+2l} = η_{l,4}` for `l ∈ [1, r]`, and `η̄_{l,3} = η_{l+1,0}` for `l ∈ [1, r - 1]`, where
`w + 2r + 1` is at most the length of the list. If `w` is odd, there is an aligned rail of length
`r` along `S` on side `ζ` with these `η_{l,0}` whose facing darts are among `λ_{w-1}, …, λ_{w+2r}`;
if `w` is even and `λ_{w+2r+1}` exists, there is such a staggered rail whose facing darts are among
`λ_w, …, λ_{w+2r+1}`. -/
private theorem exists_rail_of_relations (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {ζ : StrandSide} {w r : ℕ} (hr : 1 ≤ r)
    (hwa : w + 2 * r + 1 ≤ (X.sideList ζ (X.arc i)).length) (eta : ℕ → H)
    (heta_int : ∀ l, 1 ≤ l → l ≤ r → ¬X.IsBoundaryVertex (X.vertexOf (eta l)))
    (heta_inj : ∀ l l', 1 ≤ l → l ≤ r → 1 ≤ l' → l' ≤ r →
      X.vertexOf (eta l) = X.vertexOf (eta l') → l = l')
    (heta_avoid : ∀ l, 1 ≤ l → l ≤ r → ∀ e ∈ X.arc i,
      X.vertexOf (eta l) ≠ X.vertexOf e ∧ X.vertexOf (eta l) ≠ X.vertexOf (X.inv e))
    (h0 : (X.sideList ζ (X.arc i))[w]?.map X.inv = some (eta 1))
    (h5 : ∀ l, 1 ≤ l → l ≤ r →
      (X.sideList ζ (X.arc i))[w + 2 * l - 1]?.map X.inv = some ((X.rot ^ 5) (eta l)))
    (h4 : ∀ l, 1 ≤ l → l ≤ r →
      (X.sideList ζ (X.arc i))[w + 2 * l]?.map X.inv = some ((X.rot ^ 4) (eta l)))
    (h3 : ∀ l, 1 ≤ l → l < r → X.inv ((X.rot ^ 3) (eta l)) = eta (l + 1)) :
    (Odd w → ∃ R : X.AlignedRail r, R.IsAlong (X.arc i) ζ ∧ R.eta r = eta r ∧
      ∀ d ∈ R.facingDarts, ∃ v, w - 1 ≤ v ∧ v ≤ w + 2 * r ∧
        (X.sideList ζ (X.arc i))[v]? = some d) ∧
    (Even w → w + 2 * r + 1 < (X.sideList ζ (X.arc i)).length →
      ∃ R : X.StaggeredRail r, R.IsAlong (X.arc i) ζ ∧ R.eta r = eta r ∧
        (∀ d ∈ R.facingDarts, ∃ v, w ≤ v ∧ v ≤ w + 2 * r + 1 ∧
          (X.sideList ζ (X.arc i))[v]? = some d) ∧
        (X.sideList ζ (X.arc i))[w + 2 * r + 1]? =
          some (X.railDart R.rho R.eta (RailLabel.rho r 2))) := by
  set Λ := X.sideList ζ (X.arc i) with hΛ
  have hΛlen : (X.sideList ζ (X.arc i)).length = Λ.length := rfl
  set d₀ := X.arcDart i 0
  obtain ⟨F1, F2⟩ := sideList_steps (X := X) (i := i) hX ζ d₀
  rw [← hΛ] at F1 F2
  have hget : ∀ v, v < Λ.length → Λ[v]? = some (Λ.getD v d₀) := fun v hv => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]
  have hinvget : ∀ v, v < Λ.length → ∀ y, Λ[v]?.map X.inv = some y → X.inv (Λ.getD v d₀) = y :=
    fun v hv y h => by rwa [hget v hv, Option.map_some, Option.some.injEq] at h
  -- the facing darts of a rail with `ρ_{j,0} = σ⁻¹(λ_{base+2j})`
  have hface : ∀ base, Even base → base + 2 * r + 1 < Λ.length → ∀ (P : X.RailPoints r r),
      P.rho = (fun j => X.rot.symm (Λ.getD (base + 2 * j) d₀)) →
        P.facingDarts = (Λ.drop base).take (2 * (r + 1)) := by
    intro base hbase hlen P hP
    apply List.ext_getElem?
    intro k
    rcases lt_or_ge k (2 * (r + 1)) with hk | hk
    · rw [List.getElem?_take_of_lt hk, List.getElem?_drop,
        List.getElem?_eq_getElem (by simp; omega)]
      simp only [RailPoints.facingDarts, List.getElem_map, List.getElem_range]
      change some ((X.rot ^ (k % 2 + 1)) (P.rho (k / 2))) = _
      rw [hP, rot_pow_succ_symm_apply]
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · rw [h, pow_zero, Equiv.Perm.one_apply, show base + 2 * (k / 2) = base + k by omega,
          hget _ (by omega)]
      · rw [h, pow_one, ← F1 _ (by obtain ⟨c, hc⟩ := hbase; exact ⟨c + k / 2, by omega⟩)
          (by omega), show base + 2 * (k / 2) + 1 = base + k by omega]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hmemface : ∀ base, Even base → base + 2 * r + 1 < Λ.length → ∀ (P : X.RailPoints r r),
      P.rho = (fun j => X.rot.symm (Λ.getD (base + 2 * j) d₀)) → ∀ d ∈ P.facingDarts,
        ∃ v, base ≤ v ∧ v ≤ base + 2 * r + 1 ∧ Λ[v]? = some d := by
    intro base hbase hlen P hP d hd
    rw [hface base hbase hlen P hP] at hd
    obtain ⟨k, hkd⟩ := List.mem_iff_getElem?.1 hd
    rw [List.getElem?_take] at hkd
    split_ifs at hkd with hk
    · rw [List.getElem?_drop] at hkd
      exact ⟨base + k, by omega, by omega, hkd⟩
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨hmem, hinj⟩ := railPoints_aux hX hS (ζ := ζ) (base := w - 1) ⟨c, by omega⟩
      (by omega) eta heta_int heta_inj heta_avoid d₀
    let P : X.RailPoints r r :=
      ⟨fun j => X.rot.symm (Λ.getD (w - 1 + 2 * j) d₀), eta, hmem, hinj⟩
    refine ⟨{ P with
      inv_rho_three := fun j hj => ?_
      inv_eta_three := fun j hj => ?_
      inv_rho_one := fun j hj1 hj2 => ?_
      inv_rho_two := fun j hj1 hj2 => ?_ }, ⟨?_, fun j hj1 hj2 => heta_avoid j hj1 hj2⟩, rfl,
      fun d hd => ?_⟩
    · change X.inv ((X.rot ^ 3) (X.rot.symm (Λ.getD (w - 1 + 2 * j) d₀))) =
        (X.rot ^ 0) (X.rot.symm (Λ.getD (w - 1 + 2 * (j + 1)) d₀))
      rw [rot_pow_succ_symm_apply, F2 _ ⟨c + j, by omega⟩ (by omega), pow_zero,
        Equiv.Perm.one_apply, show w - 1 + 2 * (j + 1) = w - 1 + 2 * j + 2 by ring]
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · change X.inv ((X.rot ^ 2) (X.rot.symm (Λ.getD (w - 1 + 2 * 0) d₀))) = (X.rot ^ 0) (eta 1)
        rw [rot_pow_succ_symm_apply, pow_one, pow_zero, Equiv.Perm.one_apply]
        have h := F1 (w - 1) ⟨c, by omega⟩ (by omega)
        rw [show w - 1 + 1 = w by omega] at h
        rw [show w - 1 + 2 * 0 = w - 1 by ring]
        rw [h, Option.map_some, Option.some.injEq] at h0
        exact h0
      · change X.inv (X.railDart _ eta (if j = 0 then _ else RailLabel.eta j 3)) = (X.rot ^ 0) _
        rw [if_neg (by omega), pow_zero, Equiv.Perm.one_apply]
        exact h3 j hj0 hj
    · change X.inv ((X.rot ^ 1) (X.rot.symm (Λ.getD (w - 1 + 2 * j) d₀))) = (X.rot ^ 5) (eta j)
      rw [rot_pow_succ_symm_apply, pow_zero, Equiv.Perm.one_apply]
      have h := h5 j hj1 hj2
      rw [show w + 2 * j - 1 = w - 1 + 2 * j by omega] at h
      exact hinvget _ (by omega) _ h
    · change X.inv ((X.rot ^ 2) (X.rot.symm (Λ.getD (w - 1 + 2 * j) d₀))) = (X.rot ^ 4) (eta j)
      rw [rot_pow_succ_symm_apply, pow_one]
      have h := F1 (w - 1 + 2 * j) ⟨c + j, by omega⟩ (by omega)
      rw [show w - 1 + 2 * j + 1 = w + 2 * j by omega] at h
      have h' := h4 j hj1 hj2
      rw [h, Option.map_some, Option.some.injEq] at h'
      exact h'
    · rw [hface (w - 1) ⟨c, by omega⟩ (by omega) P rfl]
      exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix
    · obtain ⟨v, h1, h2, h3⟩ := hmemface (w - 1) ⟨c, by omega⟩ (by omega) P rfl d hd
      exact ⟨v, h1, by omega, h3⟩
  · rintro ⟨c, hc⟩ hlt
    obtain ⟨hmem, hinj⟩ := railPoints_aux hX hS (ζ := ζ) (base := w) ⟨c, hc⟩ (by omega) eta
      heta_int heta_inj heta_avoid d₀
    let P : X.RailPoints r r := ⟨fun j => X.rot.symm (Λ.getD (w + 2 * j) d₀), eta, hmem, hinj⟩
    refine ⟨{ P with
      one_le := hr
      inv_rho_three := fun j hj => ?_
      inv_rho_zero_one := ?_
      inv_eta_three := fun j hj1 hj2 => ?_
      inv_rho_two := fun j hj1 hj2 => ?_
      inv_rho_one := fun j hj1 hj2 => ?_ }, ⟨?_, fun j hj1 hj2 => heta_avoid j hj1 hj2⟩, rfl,
      fun d hd => ?_, ?_⟩
    · change X.inv ((X.rot ^ 3) (X.rot.symm (Λ.getD (w + 2 * j) d₀))) =
        (X.rot ^ 0) (X.rot.symm (Λ.getD (w + 2 * (j + 1)) d₀))
      rw [rot_pow_succ_symm_apply, F2 _ ⟨c + j, by omega⟩ (by omega), pow_zero,
        Equiv.Perm.one_apply, show w + 2 * (j + 1) = w + 2 * j + 2 by ring]
    · change X.inv ((X.rot ^ 1) (X.rot.symm (Λ.getD (w + 2 * 0) d₀))) = (X.rot ^ 0) (eta 1)
      rw [rot_pow_succ_symm_apply, pow_zero, Equiv.Perm.one_apply, Equiv.Perm.one_apply,
        show w + 2 * 0 = w by ring]
      exact hinvget _ (by omega) _ h0
    · change X.inv ((X.rot ^ 3) (eta j)) = (X.rot ^ 0) (eta (j + 1))
      rw [pow_zero, Equiv.Perm.one_apply]
      exact h3 j hj1 hj2
    · change X.inv ((X.rot ^ 2) (X.rot.symm (Λ.getD (w + 2 * (j - 1)) d₀))) =
        (X.rot ^ 5) (eta j)
      rw [rot_pow_succ_symm_apply, pow_one]
      have h := F1 (w + 2 * (j - 1)) ⟨c + (j - 1), by omega⟩ (by omega)
      rw [show w + 2 * (j - 1) + 1 = w + 2 * j - 1 by omega] at h
      have h' := h5 j hj1 hj2
      rw [h, Option.map_some, Option.some.injEq] at h'
      exact h'
    · change X.inv ((X.rot ^ 1) (X.rot.symm (Λ.getD (w + 2 * j) d₀))) = (X.rot ^ 4) (eta j)
      rw [rot_pow_succ_symm_apply, pow_zero, Equiv.Perm.one_apply]
      exact hinvget _ (by omega) _ (h4 j hj1 hj2)
    · rw [hface w ⟨c, hc⟩ (by omega) P rfl]
      exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix
    · exact hmemface w ⟨c, hc⟩ (by omega) P rfl d hd
    · change _ = some ((X.rot ^ 2) (X.rot.symm (Λ.getD (w + 2 * r) d₀)))
      rw [rot_pow_succ_symm_apply, pow_one]
      exact F1 _ ⟨c + r, by omega⟩ (by omega)

omit [Fintype H] [DecidableEq H] in
private theorem getElem_eq_of_eq' {l : List H} {k k' : ℕ} (h : k = k') (hk : k < l.length) :
    l[k] = l[k']'(h ▸ hk) := by
  subst h; rfl

/-- **A rail from a strand path**: let `Q = (f₁, …, f_n)`, `n ≥ 2`, be a strand path of `X` whose
interior points are pairwise distinct and avoided by the simple arc `S`, with `ζ` list
`(λ₀, λ₁, …)`, and let `w + 2(n - 1) + 1` be at most the length of the list. Suppose either
`f₁ = g`, `f̄_n = λ_w`, `λ̄_{w+2l-1} = σ² f̄_{n-l}` and `λ̄_{w+2l} = σ f̄_{n-l}`, or `f₁ = λ_w`,
`f̄_n = g`, `λ̄_{w+2l-1} = σ⁵ f̄_l` and `λ̄_{w+2l} = σ⁴ f̄_l` (`l ∈ [1, n - 1]`). Then with
`r = n - 1` there is an aligned rail (`w` odd) or a staggered rail (`w` even, `λ_{w+2r+1}`
existing) of length `r` along `S` on side `ζ` with `η_{r,3} = ḡ`, whose facing darts are among
`λ_{w-1}, …, λ_{w+2r}`, respectively `λ_w, …, λ_{w+2r+1}`. -/
private theorem exists_rail_of_strandPath (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {ζ : StrandSide} {Q : List H} (hQ : X.IsStrandPath Q) (hn : 2 ≤ Q.length)
    (hnd : ∀ l l' (hl : l + 1 < Q.length) (hl' : l' + 1 < Q.length),
      X.vertexOf (X.inv Q[l]) = X.vertexOf (X.inv Q[l']) → l = l')
    (havoid : ∀ l (hl : l + 1 < Q.length), ∀ e ∈ X.arc i,
      X.vertexOf (X.inv Q[l]) ≠ X.vertexOf e ∧ X.vertexOf (X.inv Q[l]) ≠ X.vertexOf (X.inv e))
    {g : H} {w : ℕ} (hwa : w + 2 * (Q.length - 1) + 1 ≤ (X.sideList ζ (X.arc i)).length)
    (hrel : (Q[0]'(by omega) = g ∧
        (X.sideList ζ (X.arc i))[w]? = some (X.inv (Q[Q.length - 1]'(by omega))) ∧
        ∀ l (hl : l + 1 < Q.length),
          (X.sideList ζ (X.arc i))[w + (2 * l + 1)]?.map X.inv =
            some ((X.rot ^ 2) (X.inv (Q[Q.length - 2 - l]'(by omega)))) ∧
          (X.sideList ζ (X.arc i))[w + (2 * l + 2)]?.map X.inv =
            some (X.rot (X.inv (Q[Q.length - 2 - l]'(by omega))))) ∨
      (X.inv (Q[Q.length - 1]'(by omega)) = g ∧
        (X.sideList ζ (X.arc i))[w]? = some (Q[0]'(by omega)) ∧
        ∀ l (hl : l + 1 < Q.length),
          (X.sideList ζ (X.arc i))[w + (2 * l + 1)]?.map X.inv =
            some ((X.rot ^ 5) (X.inv Q[l])) ∧
          (X.sideList ζ (X.arc i))[w + (2 * l + 2)]?.map X.inv =
            some ((X.rot ^ 4) (X.inv Q[l])))) :
    (Odd w → ∃ R : X.AlignedRail (Q.length - 1), R.IsAlong (X.arc i) ζ ∧
      X.railDart R.rho R.eta (RailLabel.eta (Q.length - 1) 3) = X.inv g ∧
      ∀ d ∈ R.facingDarts, ∃ v, w - 1 ≤ v ∧ v ≤ w + 2 * (Q.length - 1) ∧
        (X.sideList ζ (X.arc i))[v]? = some d) ∧
    (Even w → w + 2 * (Q.length - 1) + 1 < (X.sideList ζ (X.arc i)).length →
      ∃ R : X.StaggeredRail (Q.length - 1), R.IsAlong (X.arc i) ζ ∧
        X.railDart R.rho R.eta (RailLabel.eta (Q.length - 1) 3) = X.inv g ∧
        (∀ d ∈ R.facingDarts, ∃ v, w ≤ v ∧ v ≤ w + 2 * (Q.length - 1) + 1 ∧
          (X.sideList ζ (X.arc i))[v]? = some d) ∧
        (X.sideList ζ (X.arc i))[w + 2 * (Q.length - 1) + 1]? =
          some (X.railDart R.rho R.eta (RailLabel.rho (Q.length - 1) 2))) := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  have hQg := (X.isStrandPath_iff_getElem.1 hQ).2
  have hstep : ∀ k (hk : k + 1 < Q.length), Q[k + 1] = (X.rot ^ 3) (X.inv Q[k]) ∧
      ¬X.IsBoundaryVertex (X.vertexOf (X.inv Q[k])) := fun k hk => ⟨(hQg.2 k hk).2, (hQg.2 k hk).1⟩
  have hsix : ∀ k (hk : k + 1 < Q.length) (e : ℕ), (X.rot ^ (e + 6)) (X.inv Q[k]) =
      (X.rot ^ e) (X.inv Q[k]) := by
    intro k hk e
    rw [pow_add, Equiv.Perm.mul_apply, hpre.rot_pow_six_apply (hstep k hk).2]
  have hvQ : ∀ k (hk : k + 1 < Q.length), X.vertexOf Q[k + 1] = X.vertexOf (X.inv Q[k]) := by
    intro k hk
    rw [(hstep k hk).1, X.vertexOf_rot_pow_apply]
  set r := Q.length - 1 with hr
  have hr1 : 1 ≤ r := by omega
  set d₀ := X.arcDart i 0
  -- the general facts, to be fed to `exists_rail_of_relations`
  have key : ∀ (eta : ℕ → H) (idx : ℕ → ℕ)
      (hidx : ∀ l, 1 ≤ l → l ≤ r → idx l + 1 < Q.length),
      (∀ l (hl1 : 1 ≤ l) (hl2 : l ≤ r),
        X.vertexOf (eta l) = X.vertexOf (X.inv (Q[idx l]'(by
          have := hidx l hl1 hl2; omega)))) →
      (∀ l l', 1 ≤ l → l ≤ r → 1 ≤ l' → l' ≤ r → idx l = idx l' → l = l') →
      (∀ l, 1 ≤ l → l ≤ r → ¬X.IsBoundaryVertex (X.vertexOf (eta l))) ∧
      (∀ l l', 1 ≤ l → l ≤ r → 1 ≤ l' → l' ≤ r →
        X.vertexOf (eta l) = X.vertexOf (eta l') → l = l') ∧
      (∀ l, 1 ≤ l → l ≤ r → ∀ e ∈ X.arc i,
        X.vertexOf (eta l) ≠ X.vertexOf e ∧ X.vertexOf (eta l) ≠ X.vertexOf (X.inv e)) := by
    intro eta idx hidx hv huniq
    refine ⟨fun l hl1 hl2 => ?_, fun l l' hl1 hl2 hl1' hl2' h => ?_, fun l hl1 hl2 => ?_⟩
    · rw [hv l hl1 hl2]; exact (hstep _ (hidx l hl1 hl2)).2
    · exact huniq l l' hl1 hl2 hl1' hl2' (hnd _ _ (hidx l hl1 hl2) (hidx l' hl1' hl2')
        (by rw [← hv l hl1 hl2, ← hv l' hl1' hl2', h]))
    · rw [hv l hl1 hl2]; exact havoid _ (hidx l hl1 hl2)
  rcases hrel with ⟨hg, hw, hrel⟩ | ⟨hg, hw, hrel⟩
  · -- `f₁ = g`: `η_{l,0} = f_{n-l+1}`
    set eta : ℕ → H := fun l => Q.getD (Q.length - l) d₀ with heta
    have heta' : ∀ l (hl1 : 1 ≤ l) (hl2 : l ≤ r), eta l = Q[Q.length - l]'(by omega) := by
      intro l hl1 hl2
      simp only [heta, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show Q.length - l <
        Q.length by omega), Option.getD_some]
    have heta3 : ∀ l (hl1 : 1 ≤ l) (hl2 : l ≤ r) (e : ℕ), (X.rot ^ e) (eta l) =
        (X.rot ^ (e + 3)) (X.inv (Q[Q.length - l - 1]'(by omega))) := by
      intro l hl1 hl2 e
      rw [heta' l hl1 hl2, getElem_eq_of_eq' (show Q.length - l = Q.length - l - 1 + 1 by omega),
        (hstep _ (by omega)).1, ← Equiv.Perm.mul_apply, ← pow_add]
    obtain ⟨hint, hinj, havoid'⟩ := key eta (fun l => Q.length - l - 1) (fun l hl1 hl2 => by omega)
      (fun l hl1 hl2 => by
        rw [heta' l hl1 hl2, getElem_eq_of_eq' (show Q.length - l = Q.length - l - 1 + 1 by omega),
          hvQ _ (by omega)])
      (fun l l' hl1 hl2 hl1' hl2' h => by omega)
    have h0 : (X.sideList ζ (X.arc i))[w]?.map X.inv = some (eta 1) := by
      rw [hw, Option.map_some, hinv, heta' 1 le_rfl hr1]
    have h5 : ∀ l, 1 ≤ l → l ≤ r → (X.sideList ζ (X.arc i))[w + 2 * l - 1]?.map X.inv =
        some ((X.rot ^ 5) (eta l)) := by
      intro l hl1 hl2
      have := (hrel (l - 1) (by omega)).1
      rw [show w + (2 * (l - 1) + 1) = w + 2 * l - 1 by omega] at this
      rw [this, heta3 l hl1 hl2, show 5 + 3 = 2 + 6 by rfl, hsix _ (by omega),
        getElem_eq_of_eq' (show Q.length - 2 - (l - 1) = Q.length - l - 1 by omega)]
    have h4 : ∀ l, 1 ≤ l → l ≤ r → (X.sideList ζ (X.arc i))[w + 2 * l]?.map X.inv =
        some ((X.rot ^ 4) (eta l)) := by
      intro l hl1 hl2
      have := (hrel (l - 1) (by omega)).2
      rw [show w + (2 * (l - 1) + 2) = w + 2 * l by omega] at this
      rw [this, heta3 l hl1 hl2, show 4 + 3 = 1 + 6 by rfl, hsix _ (by omega), pow_one,
        getElem_eq_of_eq' (show Q.length - 2 - (l - 1) = Q.length - l - 1 by omega)]
    have h3 : ∀ l, 1 ≤ l → l < r → X.inv ((X.rot ^ 3) (eta l)) = eta (l + 1) := by
      intro l hl1 hl2
      rw [heta3 l hl1 hl2.le, show 3 + 3 = 0 + 6 by rfl, hsix _ (by omega), pow_zero,
        Equiv.Perm.one_apply, hinv, heta' (l + 1) (by omega) (by omega),
        getElem_eq_of_eq' (show Q.length - l - 1 = Q.length - (l + 1) by omega)]
    have hη3 : (X.rot ^ 3) (eta r) = X.inv g := by
      rw [heta3 r hr1 le_rfl, show 3 + 3 = 0 + 6 by rfl, hsix _ (by omega), pow_zero,
        Equiv.Perm.one_apply, ← hg, getElem_eq_of_eq' (show Q.length - r - 1 = 0 by omega)]
    obtain ⟨hA, hSt⟩ := exists_rail_of_relations hX hS hr1 hwa eta hint hinj havoid' h0 h5 h4 h3
    refine ⟨fun hw => ?_, fun hw hlt => ?_⟩
    · obtain ⟨R, hR1, hR2, hR3⟩ := hA hw
      exact ⟨R, hR1, by change (X.rot ^ 3) (R.eta r) = _; rw [hR2, hη3], hR3⟩
    · obtain ⟨R, hR1, hR2, hR3, hR4⟩ := hSt hw hlt
      exact ⟨R, hR1, by change (X.rot ^ 3) (R.eta r) = _; rw [hR2, hη3], hR3, hR4⟩
  · -- `f̄_n = g`: `η_{l,0} = f̄_l`
    set eta : ℕ → H := fun l => X.inv (Q.getD (l - 1) d₀) with heta
    have heta' : ∀ l (hl1 : 1 ≤ l) (hl2 : l ≤ r), eta l = X.inv (Q[l - 1]'(by omega)) := by
      intro l hl1 hl2
      simp only [heta, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show l - 1 <
        Q.length by omega), Option.getD_some]
    obtain ⟨hint, hinj, havoid'⟩ := key eta (fun l => l - 1) (fun l hl1 hl2 => by omega)
      (fun l hl1 hl2 => by rw [heta' l hl1 hl2]) (fun l l' hl1 hl2 hl1' hl2' h => by omega)
    have h0 : (X.sideList ζ (X.arc i))[w]?.map X.inv = some (eta 1) := by
      rw [hw, Option.map_some, heta' 1 le_rfl hr1]
    have h5 : ∀ l, 1 ≤ l → l ≤ r → (X.sideList ζ (X.arc i))[w + 2 * l - 1]?.map X.inv =
        some ((X.rot ^ 5) (eta l)) := by
      intro l hl1 hl2
      have := (hrel (l - 1) (by omega)).1
      rw [show w + (2 * (l - 1) + 1) = w + 2 * l - 1 by omega] at this
      rw [this, heta' l hl1 hl2]
    have h4 : ∀ l, 1 ≤ l → l ≤ r → (X.sideList ζ (X.arc i))[w + 2 * l]?.map X.inv =
        some ((X.rot ^ 4) (eta l)) := by
      intro l hl1 hl2
      have := (hrel (l - 1) (by omega)).2
      rw [show w + (2 * (l - 1) + 2) = w + 2 * l by omega] at this
      rw [this, heta' l hl1 hl2]
    have h3 : ∀ l, 1 ≤ l → l < r → X.inv ((X.rot ^ 3) (eta l)) = eta (l + 1) := by
      intro l hl1 hl2
      rw [heta' l hl1 hl2.le, heta' (l + 1) (by omega) (by omega)]
      congr 1
      rw [← (hstep (l - 1) (by omega)).1]
      congr 1
      omega
    have hη3 : (X.rot ^ 3) (eta r) = X.inv g := by
      rw [heta' r hr1 le_rfl, ← (hstep (r - 1) (by omega)).1, ← hg, hinv]
      congr 1
      omega
    obtain ⟨hA, hSt⟩ := exists_rail_of_relations hX hS hr1 hwa eta hint hinj havoid' h0 h5 h4 h3
    refine ⟨fun hw => ?_, fun hw hlt => ?_⟩
    · obtain ⟨R, hR1, hR2, hR3⟩ := hA hw
      exact ⟨R, hR1, by change (X.rot ^ 3) (R.eta r) = _; rw [hR2, hη3], hR3⟩
    · obtain ⟨R, hR1, hR2, hR3, hR4⟩ := hSt hw hlt
      exact ⟨R, hR1, by change (X.rot ^ 3) (R.eta r) = _; rw [hR2, hη3], hR3, hR4⟩

/-- A triple point avoided by the arc from `s_i` is not the vertex of a dart of the arc or of the
reverse of one. -/
private theorem ne_vertexOf_of_avoided (hX : X.IsTripleDiagram) {v : Finset H}
    (hint : v ∈ X.internalVertices) (hpass : ¬X.PassesThrough (X.arc i).toFinset v) :
    ∀ e ∈ X.arc i, v ≠ X.vertexOf e ∧ v ≠ X.vertexOf (X.inv e) := by
  intro e he
  refine ⟨fun h => hpass ⟨hint, e, List.mem_toFinset.2 he, h.symm⟩, fun h => ?_⟩
  obtain ⟨t, ht, rfl⟩ := mem_arc_toFinset.1 (List.mem_toFinset.2 he)
  by_cases ht' : t + 1 < X.arcLength i
  · exact hpass (by have := passesThrough_zDart hX ht' 0; simpa [zDart, h] using this)
  · apply (X.mem_internalVertices.1 hint).2
    rw [h, show t = X.arcLength i - 1 by omega, ← endDart_arcEndIndex hX]
    exact (X.mem_boundaryVertices.1 (hX.endpoint_mem _)).2

/-- A strand path `Q` satisfying the relations of the shape of a boundary-parallel arc against the
`ζ` list `(λ₀, …, λ_{2k-1})` of `S`, whose `ζ` cut list is `(g₀, …, g_{2k-1}, λ₀, …, λ_{2k-1})`,
gives an aligned or a staggered rail along `S` on side `ζ`. -/
private theorem stepTwoRail_finish (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {ζ : StrandSide} {k : ℕ} (hL : (X.arcCutList i ζ).length = 4 * k)
    (hΛ : (X.sideList ζ (X.arc i)).length = 2 * k)
    (hLΛ : ∀ v, (X.arcCutList i ζ)[2 * k + v]? = (X.sideList ζ (X.arc i))[v]?)
    {t a w : ℕ} (ht : t < 2 * k)
    (ht' : ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∈ X.sideList ζ (X.arc i))
    (ha : (t = 0 ∧ a = 2 * k) ∨
      (0 < t ∧ (X.arcCutList i ζ)[t - 1]?.map X.inv = (X.sideList ζ (X.arc i))[a]?))
    {Q : List H} (hQ : X.IsStrandPath Q) (hn : 2 ≤ Q.length)
    (hnd : ∀ l l' (hl : l + 1 < Q.length) (hl' : l' + 1 < Q.length),
      X.vertexOf (X.inv Q[l]) = X.vertexOf (X.inv Q[l']) → l = l')
    (havoid : ∀ l (hl : l + 1 < Q.length), ∀ e ∈ X.arc i,
      X.vertexOf (X.inv Q[l]) ≠ X.vertexOf e ∧ X.vertexOf (X.inv Q[l]) ≠ X.vertexOf (X.inv e))
    (hwa : w + 2 * (Q.length - 1) + 1 = a)
    (hrel : (Q[0]'(by omega) = (X.arcCutList i ζ)[t]'(by omega) ∧
        (X.sideList ζ (X.arc i))[w]? = some (X.inv (Q[Q.length - 1]'(by omega))) ∧
        ∀ l (hl : l + 1 < Q.length),
          (X.sideList ζ (X.arc i))[w + (2 * l + 1)]?.map X.inv =
            some ((X.rot ^ 2) (X.inv (Q[Q.length - 2 - l]'(by omega)))) ∧
          (X.sideList ζ (X.arc i))[w + (2 * l + 2)]?.map X.inv =
            some (X.rot (X.inv (Q[Q.length - 2 - l]'(by omega))))) ∨
      (X.inv (Q[Q.length - 1]'(by omega)) = (X.arcCutList i ζ)[t]'(by omega) ∧
        (X.sideList ζ (X.arc i))[w]? = some (Q[0]'(by omega)) ∧
        ∀ l (hl : l + 1 < Q.length),
          (X.sideList ζ (X.arc i))[w + (2 * l + 1)]?.map X.inv =
            some ((X.rot ^ 5) (X.inv Q[l])) ∧
          (X.sideList ζ (X.arc i))[w + (2 * l + 2)]?.map X.inv =
            some ((X.rot ^ 4) (X.inv Q[l])))) :
    (∃ r, 1 ≤ r ∧ ∃ R : X.AlignedRail r, R.IsAlong (X.arc i) ζ ∧
      (X.arcCutList i ζ)[t]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3)) ∧
      ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∉ R.facingDarts) ∨
    (∃ r, 1 ≤ r ∧ ∃ R : X.StaggeredRail r, R.IsAlong (X.arc i) ζ ∧
      (X.arcCutList i ζ)[t]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3)) ∧
      ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∈ R.facingDarts →
        X.inv g = X.railDart R.rho R.eta (RailLabel.rho r 2)) := by
  have hinv := hX.inv_involutive
  have hc := hS.isCutData_arcCutList hX ζ
  have hY := hS.isTripleDiagram_arcCut hX ζ (by omega)
  have hev := even_length_arcCutList (X := X) (i := i) ζ
  have hs : ζ.cutShift ≤ 1 := by cases ζ <;> simp [StrandSide.cutShift]
  have ha2 : a ≤ 2 * k := by
    rcases ha with ⟨-, rfl⟩ | ⟨-, h⟩
    · exact le_rfl
    · rw [List.getElem?_eq_getElem (by omega), Option.map_some] at h
      have := (List.getElem?_eq_some_iff.1 h.symm).1
      omega
  -- the `ζ` list has no repetition
  have hΛnd : ∀ (v v' : ℕ) (d : H), (X.sideList ζ (X.arc i))[v]? = some d →
      (X.sideList ζ (X.arc i))[v']? = some d → v = v' := by
    intro v v' d hv hv'
    rw [← hLΛ] at hv hv'
    have := eq_of_getElem?_eq' hc.nodup hv hv'
    omega
  have hgt : (X.arcCutList i ζ)[t]?.map X.inv =
      some (X.inv ((X.arcCutList i ζ)[t]'(by omega))) := by
    rw [List.getElem?_eq_getElem (by omega), Option.map_some]
  -- chords do not cross: for `t' < t - 1`, `ḡ_{t'} = λ_v` with `v > a`
  have hchord : 0 < t → ∀ t', t' + 1 < t → ∀ g ∈ (X.arcCutList i ζ)[t']?, ∀ v : ℕ,
      (X.sideList ζ (X.arc i))[v]? = some (X.inv g) → a < v := by
    intro ht0 t' ht'' g hg v hv
    rcases ha with ⟨rfl, -⟩ | ⟨-, ha'⟩
    · omega
    rw [List.getElem?_eq_getElem (by omega), Option.map_some] at ha'
    rw [Option.mem_def, List.getElem?_eq_getElem (by omega), Option.some.injEq] at hg
    subst hg
    have haΛ : a < 2 * k := by
      have := (List.getElem?_eq_some_iff.1 ha'.symm).1
      omega
    by_contra hva
    rcases lt_or_eq_of_le (not_lt.1 hva) with hva | rfl
    · have hv' := hv
      rw [← hLΛ, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.1 hv).1; omega),
        Option.some.injEq] at hv'
      have ha'' := ha'.symm
      rw [← hLΛ, List.getElem?_eq_getElem (by omega), Option.some.injEq] at ha''
      exact hc.inv_getElem_ne_of_lt hinv hs hY hev (t := t') (v := t - 1) (u := 2 * k + v)
        (w := 2 * k + a) (by omega) (by omega) (by omega) (by omega) hv'.symm ha''.symm
    · rw [hv] at ha'
      have := hinv.injective (Option.some_injective _ ha')
      have := hc.nodup.getElem_inj_iff.1 this
      omega
  obtain ⟨hAl, hSt⟩ := exists_rail_of_strandPath hX hS hQ hn hnd havoid (by omega) hrel
  rcases Nat.even_or_odd w with hw | hw
  · -- `w` even: a staggered rail
    have hat : 0 < t ∧ a < 2 * k := by
      rcases ha with ⟨rfl, rfl⟩ | ⟨ht0, h⟩
      · exfalso
        obtain ⟨c, hc'⟩ := hw
        omega
      · refine ⟨ht0, ?_⟩
        rw [List.getElem?_eq_getElem (by omega), Option.map_some] at h
        have := (List.getElem?_eq_some_iff.1 h.symm).1
        omega
    obtain ⟨R, hR1, hR2, hR3, hR4⟩ := hSt hw (by omega)
    refine Or.inr ⟨Q.length - 1, by omega, R, hR1, by rw [hgt, hR2], ?_⟩
    intro t' ht'' g hg hmem
    obtain ⟨v, hv1, hv2, hv3⟩ := hR3 _ hmem
    rcases lt_or_eq_of_le (Nat.le_sub_one_of_lt ht'') with ht3 | rfl
    · exact absurd (hchord hat.1 t' (by omega) g hg v hv3) (by omega)
    · rcases ha with ⟨rfl, -⟩ | ⟨-, ha'⟩
      · omega
      rw [Option.mem_def.1 hg, Option.map_some] at ha'
      rw [hwa] at hR4
      rw [← ha'] at hR4
      exact Option.some_injective _ hR4
  · -- `w` odd: an aligned rail
    obtain ⟨R, hR1, hR2, hR3⟩ := hAl hw
    refine Or.inl ⟨Q.length - 1, by omega, R, hR1, by rw [hgt, hR2], ?_⟩
    intro t' ht'' g hg hmem
    obtain ⟨v, hv1, hv2, hv3⟩ := hR3 _ hmem
    have ht0 : 0 < t := by omega
    rcases lt_or_eq_of_le (Nat.le_sub_one_of_lt ht'') with ht3 | rfl
    · exact absurd (hchord ht0 t' (by omega) g hg v hv3) (by omega)
    · rcases ha with ⟨rfl, -⟩ | ⟨-, ha'⟩
      · omega
      rw [Option.mem_def.1 hg, Option.map_some] at ha'
      have := hΛnd _ _ _ hv3 ha'.symm
      omega

/-- For a simple arc with `k` triple points whose side `ζ` has `2k` positions, the `ζ` list has
`2k` entries and the `ζ` cut list is `(g₀, …, g_{2k-1}, λ₀, …, λ_{2k-1})`. -/
private theorem stepTwo_lists (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hI : IsIntervalOf X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ}
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k) (hS : X.IsSimpleArc i)
    (hSk : {v | X.PassesThrough (X.arc i).toFinset v}.ncard = k) :
    (X.sideList ζ (X.arc i)).length = 2 * k ∧ (X.arcCutList i ζ).length = 4 * k ∧
      ∀ v, (X.arcCutList i ζ)[2 * k + v]? = (X.sideList ζ (X.arc i))[v]? := by
  have hm1 := hX.toIsPreTripleDiagram.arcLength_ne_zero i
  have hm : X.arcLength i = k + 1 := by have := hS.ncard_passesThrough hX; omega
  have hΛ : (X.sideList ζ (X.arc i)).length = 2 * k := by rw [length_sideList_arc]; omega
  have hcard := hI.card_intervalInterior_eq (X := X)
  rw [hζ] at hcard
  have hlegs : ((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1 = 2 * k := by
    omega
  refine ⟨hΛ, ?_, fun v => ?_⟩
  · rw [arcCutList_eq_append, List.length_append, List.length_map, List.length_range, hΛ]
    omega
  · rw [← hlegs]
    exact getElem?_arcCutList_add ζ v

/-- **A boundary-parallel strand in the nested cut gives a rail**, the case `t = 0`. Let `X` be a
triple diagram, `I` an interval of `i` with side `ζ` and `2k ≥ 2` interior positions, and let the
arc `S` from `s_i` be simple with `k` triple points. Let `(g₀, …, g_{2k-1}, λ₀, …, λ_{2k-1})` be
the `ζ` cut list of `S` (the legs at the interior positions of `I` followed by the `ζ` list), and
suppose `ḡ₀` is not a dart of the `ζ` list. Suppose that the arc `Q` of `Y₂ = X|_{S,ζ}` through
`g₀` (its darts are the `Sum.inl f`, `f ∈ H_ζ(S)`) has the other end leg `λ_w`, and is
boundary-parallel in `Y₂` along an interval `I₂` of its pair whose interior positions are those of
`λ_{w+1}, …, λ_{2k-1}`. Then `X` has an aligned rail or a staggered rail of some length `r ≥ 1`
along `S` on side `ζ` with `η_{r,3} = ḡ₀`. -/
@[cluster_algebras "lem_step_two_rail"]
theorem IsSimpleArc.exists_rail_of_isBoundaryParallel_arcCut (hX : X.IsTripleDiagram)
    {I : Finset (Fin (2 * b))} (hI : IsIntervalOf X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k) (hS : X.IsSimpleArc i)
    (hSk : {v | X.PassesThrough (X.arc i).toFinset v}.ncard = k)
    (hg0 : ∀ g ∈ (X.arcCutList i ζ)[0]?, X.inv g ∉ X.sideList ζ (X.arc i))
    {j₂ : Fin ((X.arcCutList i ζ).length / 2)} {Q : List {d // d ∈ X.arcSideDarts i ζ}}
    (hQ : Q.map Sum.inl = (X.arcCut i ζ).arc j₂) {w : ℕ} (hw : w < 2 * k)
    (hends : ((Q.map Subtype.val).head? = (X.arcCutList i ζ)[0]? ∧
        (Q.map Subtype.val).getLast?.map X.inv = (X.sideList ζ (X.arc i))[w]?) ∨
      ((Q.map Subtype.val).head? = (X.sideList ζ (X.arc i))[w]? ∧
        (Q.map Subtype.val).getLast?.map X.inv = (X.arcCutList i ζ)[0]?))
    {I₂ : Finset (Fin (2 * ((X.arcCutList i ζ).length / 2)))}
    (hB₂ : (X.arcCut i ζ).IsBoundaryParallel j₂ I₂)
    (hI₂ : ∀ r, r ∈ intervalInterior (X.arcCut i ζ).strandPerm j₂ I₂ ↔
      ∃ v, w < v ∧ v < 2 * k ∧ ∃ d ∈ (X.sideList ζ (X.arc i))[v]?,
        ∃ hd : d ∈ X.arcSideDarts i ζ, (X.arcCut i ζ).endDart r = .inl ⟨d, hd⟩) :
    (∃ r, 1 ≤ r ∧ ∃ R : X.AlignedRail r, R.IsAlong (X.arc i) ζ ∧
      (X.arcCutList i ζ)[0]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3))) ∨
    (∃ r, 1 ≤ r ∧ ∃ R : X.StaggeredRail r, R.IsAlong (X.arc i) ζ ∧
      (X.arcCutList i ζ)[0]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3))) := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  obtain ⟨hΛ, hL, hLΛ⟩ := stepTwo_lists hX hI hζ hk hS hSk
  have hc := hS.isCutData_arcCutList hX ζ
  have hev := even_length_arcCutList (X := X) (i := i) ζ
  have hY := hS.isTripleDiagram_arcCut hX ζ (by omega)
  obtain ⟨hn0, hQX, hcardQ, hhead, hlast, htrip, hsimple, hO4⟩ :=
    bp_cut_shape (K := X.arcSideDarts i ζ) (L := X.arcCutList i ζ) (s := ζ.cutShift) hpre hc
      hev hY hQ hB₂
  have hidx : ∀ x y, x < (X.arcCutList i ζ).length →
      (X.arcCutList i ζ)[x]? = (X.arcCutList i ζ)[y]? → x = y := fun x y hx h =>
    eq_of_getElem?_eq' hc.nodup (List.getElem?_eq_getElem hx) (by rw [← h,
      List.getElem?_eq_getElem hx])
  have hx₁lt := (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₂)).isLt
  have hx₂lt := (cutEndIndex (X.arcCutList i ζ) ζ.cutShift ((X.arcCut i ζ).arcEndIndex j₂)).isLt
  have hends' : ((cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₂) : ℕ) = 0 ∧
      (cutEndIndex (X.arcCutList i ζ) ζ.cutShift ((X.arcCut i ζ).arcEndIndex j₂) : ℕ) =
        2 * k + w) ∨
      ((cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₂) : ℕ) = 2 * k + w ∧
      (cutEndIndex (X.arcCutList i ζ) ζ.cutShift ((X.arcCut i ζ).arcEndIndex j₂) : ℕ) = 0) := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hidx _ _ hx₁lt (hhead.trans h1),
        hidx _ _ hx₂lt (hlast.trans (h2.trans (hLΛ w).symm))⟩
    · exact Or.inr ⟨hidx _ _ hx₁lt (hhead.trans (h1.trans (hLΛ w).symm)),
        hidx _ _ hx₂lt (hlast.trans h2)⟩
  -- `Q` has at least two darts, as `ḡ₀` is not in the `ζ` list
  have hn2 : 2 ≤ Q.length := by
    by_contra hn
    obtain ⟨f, rfl⟩ := List.length_eq_one_iff.1 (show Q.length = 1 by omega)
    simp only [List.map_cons, List.map_nil, List.head?_cons, List.getLast?_singleton,
      Option.map_some] at hends
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hg0 _ (Option.mem_def.2 h1.symm) (List.mem_of_getElem? h2.symm)
    · have := hg0 _ (Option.mem_def.2 h2.symm)
      rw [hinv] at this
      exact this (List.mem_of_getElem? h1.symm)
  -- the legs at the interior positions of `I₂`
  have hlegI : ∀ r, r ∈ intervalInterior (X.arcCut i ζ).strandPerm j₂ I₂ ↔
      ∃ v, w < v ∧ v < 2 * k ∧ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ) = 2 * k + v := by
    intro r
    rw [hI₂ r]
    constructor
    · rintro ⟨v, hv1, hv2, d, hd, hdK, he⟩
      refine ⟨v, hv1, hv2, hidx _ _ (cutEndIndex _ _ r).isLt ?_⟩
      rw [arcCut, cut_endDart, hc.cutListDart_eq] at he
      have hdd := congrArg Subtype.val (Sum.inl_injective he)
      rw [List.getElem?_eq_getElem (cutEndIndex _ _ r).isLt, hLΛ]
      simp only at hdd
      rw [hdd]
      exact (Option.mem_def.1 hd).symm
    · rintro ⟨v, hv1, hv2, hr⟩
      have hv : (X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ)]? =
          (X.sideList ζ (X.arc i))[v]? := by rw [hr, hLΛ]
      rw [List.getElem?_eq_getElem (cutEndIndex _ _ r).isLt] at hv
      exact ⟨v, hv1, hv2, _, Option.mem_def.2 hv.symm, hc.getElem_mem _,
        by rw [arcCut, cut_endDart, hc.cutListDart_eq]⟩
  have hcard2 : (intervalInterior (X.arcCut i ζ).strandPerm j₂ I₂).card = 2 * k - 1 - w := by
    have himg : (intervalInterior (X.arcCut i ζ).strandPerm j₂ I₂).image
        (fun r => (cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ)) =
          (Ioo w (2 * k)).image (fun v => 2 * k + v) := by
      ext x
      simp only [mem_image, mem_Ioo]
      constructor
      · rintro ⟨r, hr, rfl⟩
        obtain ⟨v, hv1, hv2, hv⟩ := (hlegI r).1 hr
        exact ⟨v, ⟨hv1, hv2⟩, hv.symm⟩
      · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
        obtain ⟨r, hr⟩ := cutEndIndex_surjective (H := H) (L := X.arcCutList i ζ)
          (s := ζ.cutShift) hev ⟨2 * k + v, by omega⟩
        exact ⟨r, (hlegI r).2 ⟨v, hv1, hv2, by rw [hr]⟩, by rw [hr]⟩
    rw [← card_image_of_injective _ (fun r r' h => cutEndIndex_injective (Fin.ext h)), himg,
      card_image_of_injective _ (fun a c h => by simpa using h), Nat.card_Ioo]
    omega
  have hcardQ' : 2 * (Q.length - 1) =
      (intervalInterior (X.arcCut i ζ).strandPerm j₂ I₂).card := hcardQ
  have hwa : w + 2 * ((Q.map Subtype.val).length - 1) + 1 = 2 * k := by
    rw [List.length_map]
    omega
  have hQg : ∀ l (hl : l < Q.length), (Q.map Subtype.val)[l]'(by simpa using hl) = Q[l].1 :=
    fun l hl => List.getElem_map _
  have havoid : ∀ l (hl : l + 1 < (Q.map Subtype.val).length), ∀ e ∈ X.arc i,
      X.vertexOf (X.inv (Q.map Subtype.val)[l]) ≠ X.vertexOf e ∧
        X.vertexOf (X.inv (Q.map Subtype.val)[l]) ≠ X.vertexOf (X.inv e) := by
    intro l hl
    rw [List.length_map] at hl
    rw [hQg l (by omega)]
    obtain ⟨hint, hpass⟩ := hS.avoided_of_mem_arcSideDarts hX (hc.inv_mem _ Q[l].2)
      (htrip l hl).1
    exact ne_vertexOf_of_avoided hX hint hpass
  have hnd : ∀ l l' (hl : l + 1 < (Q.map Subtype.val).length)
      (hl' : l' + 1 < (Q.map Subtype.val).length),
      X.vertexOf (X.inv (Q.map Subtype.val)[l]) = X.vertexOf (X.inv (Q.map Subtype.val)[l']) →
        l = l' := by
    intro l l' hl hl' h
    rw [List.length_map] at hl hl'
    rw [hQg l (by omega), hQg l' (by omega)] at h
    exact hsimple l l' hl hl' h
  have hQlen : (Q.map Subtype.val).length = Q.length := List.length_map _
  have hn2' : 2 ≤ (Q.map Subtype.val).length := by rw [List.length_map]; exact hn2
  have hQhead : (Q.map Subtype.val).head? = some (Q.map Subtype.val)[0] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have hQlast : (Q.map Subtype.val).getLast? =
      some (Q.map Subtype.val)[(Q.map Subtype.val).length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have hmod : ∀ x, 2 * k ≤ x → x < 4 * k →
      (X.arcCutList i ζ)[x % (X.arcCutList i ζ).length]? =
        (X.sideList ζ (X.arc i))[x - 2 * k]? := by
    intro x hx1 hx2
    rw [hL, Nat.mod_eq_of_lt hx2, ← hLΛ, show 2 * k + (x - 2 * k) = x by omega]
  obtain h | h := stepTwoRail_finish hX hS hL hΛ hLΛ (t := 0) (by omega)
    (fun t' ht' => absurd ht' (Nat.not_lt_zero _)) (Or.inl ⟨rfl, rfl⟩) hQX hn2' hnd havoid hwa
    (by
    rcases hO4 with ⟨-, hint1, hrel1⟩ | ⟨-, hint2, hrel2⟩
    · -- `I₂` runs clockwise from the source of `Q`, which is `λ_w`
      have hp1 := (hint1 ((finRotate _ ^ (0 + 1)) (sourceIndex j₂))).2 ⟨0, by omega, rfl⟩
      obtain ⟨v, hv1, hv2, hv⟩ := (hlegI _).1 hp1
      rw [val_cutEndIndex_finRotate_pow hev] at hv
      have hx : (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₂) : ℕ) = 2 * k + w ∧
          (cutEndIndex (X.arcCutList i ζ) ζ.cutShift ((X.arcCut i ζ).arcEndIndex j₂) : ℕ) =
            0 := by
        rcases hends' with ⟨h1, -⟩ | h
        · rw [h1, hL, Nat.mod_eq_of_lt (by omega)] at hv
          omega
        · exact h
      refine Or.inr ⟨?_, ?_, fun l hl => ?_⟩
      · have h := hlast
        rw [hQlast, Option.map_some] at h
        change (X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ) ζ.cutShift
          ((X.arcCut i ζ).arcEndIndex j₂) : ℕ)]? = _ at h
        rw [hx.2, List.getElem?_eq_getElem (by omega)] at h
        exact (Option.some_injective _ h).symm
      · rw [← hLΛ, ← hx.1, hhead, hQhead]
      · rw [List.length_map] at hl
        obtain ⟨h5, h4⟩ := hrel1 l hl
        rw [hx.1, show 2 * k + w + (2 * l + 1) = 2 * k + (w + (2 * l + 1)) by ring] at h5
        rw [hx.1, show 2 * k + w + (2 * l + 2) = 2 * k + (w + (2 * l + 2)) by ring] at h4
        rw [hmod (2 * k + (w + (2 * l + 1))) (by omega) (by omega),
          Nat.add_sub_cancel_left] at h5
        rw [hmod (2 * k + (w + (2 * l + 2))) (by omega) (by omega),
          Nat.add_sub_cancel_left] at h4
        rw [hQg l (by omega)]
        exact ⟨h5, h4⟩
    · -- `I₂` runs clockwise from the target of `Q`, whose reverse is `λ_w`
      have hq1 := (hint2 ((finRotate _ ^ (0 + 1)) ((X.arcCut i ζ).arcEndIndex j₂))).2
        ⟨0, by omega, rfl⟩
      obtain ⟨v, hv1, hv2, hv⟩ := (hlegI _).1 hq1
      rw [val_cutEndIndex_finRotate_pow hev] at hv
      have hx : (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₂) : ℕ) = 0 ∧
          (cutEndIndex (X.arcCutList i ζ) ζ.cutShift ((X.arcCut i ζ).arcEndIndex j₂) : ℕ) =
            2 * k + w := by
        rcases hends' with h | ⟨-, h2⟩
        · exact h
        · rw [h2, hL, Nat.mod_eq_of_lt (by omega)] at hv
          omega
      refine Or.inl ⟨?_, ?_, fun l hl => ?_⟩
      · have h := hhead
        rw [hQhead, hx.1, List.getElem?_eq_getElem (by omega)] at h
        exact (Option.some_injective _ h).symm
      · have h := hlast
        rw [hQlast, Option.map_some] at h
        change (X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ) ζ.cutShift
          ((X.arcCut i ζ).arcEndIndex j₂) : ℕ)]? = _ at h
        rw [hx.2, hLΛ] at h
        exact h
      · rw [List.length_map] at hl
        obtain ⟨h2, h1⟩ := hrel2 l hl
        change (X.arcCutList i ζ)[((cutEndIndex (X.arcCutList i ζ) ζ.cutShift
          ((X.arcCut i ζ).arcEndIndex j₂) : ℕ) + (2 * l + 1)) % _]?.map X.inv = _ at h2
        change (X.arcCutList i ζ)[((cutEndIndex (X.arcCutList i ζ) ζ.cutShift
          ((X.arcCut i ζ).arcEndIndex j₂) : ℕ) + (2 * l + 2)) % _]?.map X.inv = _ at h1
        rw [hx.2, show 2 * k + w + (2 * l + 1) = 2 * k + (w + (2 * l + 1)) by ring] at h2
        rw [hx.2, show 2 * k + w + (2 * l + 2) = 2 * k + (w + (2 * l + 2)) by ring] at h1
        rw [hmod (2 * k + (w + (2 * l + 1))) (by omega) (by omega),
          Nat.add_sub_cancel_left] at h2
        rw [hmod (2 * k + (w + (2 * l + 2))) (by omega) (by omega),
          Nat.add_sub_cancel_left] at h1
        rw [hQg _ (by simp; omega)]
        simp only [List.length_map]
        exact ⟨h2, h1⟩)
  · obtain ⟨r, hr, R, h1, h2, -⟩ := h
    exact Or.inl ⟨r, hr, R, h1, h2⟩
  · obtain ⟨r, hr, R, h1, h2, -⟩ := h
    exact Or.inr ⟨r, hr, R, h1, h2⟩

set_option maxHeartbeats 400000 in
-- The proof reads the shape of `Q` through two nested cuts and is long.
private theorem IsSimpleArc.exists_rail_of_arcLength_eq_one_arcCut (hX : X.IsTripleDiagram)
    {I : Finset (Fin (2 * b))} (hI : IsIntervalOf X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ}
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k) (hS : X.IsSimpleArc i)
    (hSk : {v | X.PassesThrough (X.arc i).toFinset v}.ncard = k) {t : ℕ} (ht0 : 0 < t)
    (ht : t < 2 * k)
    (ht' : ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∈ X.sideList ζ (X.arc i))
    (hgt : ∀ g ∈ (X.arcCutList i ζ)[t]?, X.inv g ∉ X.sideList ζ (X.arc i)) {a : ℕ}
    (ha : (X.arcCutList i ζ)[t - 1]?.map X.inv = (X.sideList ζ (X.arc i))[a]?)
    (hc : X.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ))
    (hL : (X.arcCutList i ζ).length = 4 * k) (haΛ : a < 2 * k)
    {j₀ : Fin ((X.arcCutList i ζ).length / 2)} (hlenA : (X.arcCut i ζ).arcLength j₀ = 1)
    {θ : StrandSide} (hlen₂ : ((X.arcCut i ζ).arcCutList j₀ θ).length = 2 * k + a - t)
    (hL₂ : ∀ u (hu : u < 2 * k + a - t), ((X.arcCut i ζ).arcCutList j₀ θ)[u]? =
      some (Sum.inl ⟨(X.arcCutList i ζ)[t + u]'(by omega), hc.getElem_mem ⟨t + u, by omega⟩⟩))
    {j₂ : Fin (((X.arcCut i ζ).arcCutList j₀ θ).length / 2)}
    {Q₂ : List {d // d ∈ (X.arcCut i ζ).arcSideDarts j₀ θ}}
    (hQ₂ : Q₂.map Sum.inl = ((X.arcCut i ζ).arcCut j₀ θ).arc j₂)
    {Q : List {d // d ∈ X.arcSideDarts i ζ}} (hQQ : Q₂.map Subtype.val = Q.map Sum.inl)
    {w : ℕ} (hw : w < a)
    (hends : ((Q.map Subtype.val).head? = (X.arcCutList i ζ)[t]? ∧
        (Q.map Subtype.val).getLast?.map X.inv = (X.sideList ζ (X.arc i))[w]?) ∨
      ((Q.map Subtype.val).head? = (X.sideList ζ (X.arc i))[w]? ∧
        (Q.map Subtype.val).getLast?.map X.inv = (X.arcCutList i ζ)[t]?))
    {I₂ : Finset (Fin (2 * (((X.arcCut i ζ).arcCutList j₀ θ).length / 2)))}
    (hB₂ : ((X.arcCut i ζ).arcCut j₀ θ).IsBoundaryParallel j₂ I₂)
    (hI₂ : ∀ r, r ∈ intervalInterior ((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂ I₂ ↔
      ∃ v, w < v ∧ v < a ∧ ∃ d ∈ (X.sideList ζ (X.arc i))[v]?, ∃ (hd : d ∈ X.arcSideDarts i ζ)
        (hd' : (Sum.inl ⟨d, hd⟩ : CutDart _ _) ∈ (X.arcCut i ζ).arcSideDarts j₀ θ),
        ((X.arcCut i ζ).arcCut j₀ θ).endDart r = .inl ⟨.inl ⟨d, hd⟩, hd'⟩) :
    (∃ r, 1 ≤ r ∧ ∃ R : X.AlignedRail r, R.IsAlong (X.arc i) ζ ∧
      (X.arcCutList i ζ)[t]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3)) ∧
      ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∉ R.facingDarts) ∨
    (∃ r, 1 ≤ r ∧ ∃ R : X.StaggeredRail r, R.IsAlong (X.arc i) ζ ∧
      (X.arcCutList i ζ)[t]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3)) ∧
      ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∈ R.facingDarts →
        X.inv g = X.railDart R.rho R.eta (RailLabel.rho r 2)) := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  obtain ⟨hΛ, -, hLΛ⟩ := stepTwo_lists hX hI hζ hk hS hSk
  have hev := even_length_arcCutList (X := X) (i := i) ζ
  have hYt := hS.isTripleDiagram_arcCut hX ζ (by omega)
  have hYp := hYt.toIsPreTripleDiagram
  have hidx : ∀ x y, x < (X.arcCutList i ζ).length →
      (X.arcCutList i ζ)[x]? = (X.arcCutList i ζ)[y]? → x = y := fun x y hx h =>
    eq_of_getElem?_eq' hc.nodup (List.getElem?_eq_getElem hx) (by rw [← h,
      List.getElem?_eq_getElem hx])
  have hinvY : ∀ d : {d // d ∈ X.arcSideDarts i ζ},
      (X.arcCut i ζ).inv (.inl d) = .inl ⟨X.inv d.1, hc.inv_mem _ d.2⟩ :=
    fun d => hc.cut_inv_inl hinv d
  -- the nested cut `Y₂`
  have hS₀ : (X.arcCut i ζ).IsSimpleArc j₀ := fun k l hk hl _ => by omega
  have hc₂ := hS₀.isCutData_arcCutList hYt θ
  have hev₂ := even_length_arcCutList (X := X.arcCut i ζ) (i := j₀) θ
  have hY₂ := hS₀.isTripleDiagram_arcCut hYt θ (by omega)
  obtain ⟨hn0, hQ₂Y, hcardQ, hhead, hlast, htrip, hsimple, hO4⟩ :=
    bp_cut_shape (K := (X.arcCut i ζ).arcSideDarts j₀ θ) (L := (X.arcCut i ζ).arcCutList j₀ θ)
      (s := θ.cutShift) hYp hc₂ hev₂ hY₂ hQ₂ hB₂
  have hQlen : Q₂.length = Q.length := by
    have := congrArg List.length hQQ
    simpa using this
  have hQ₂get : ∀ l (hl : l < Q₂.length), (Q₂[l]).1 = .inl (Q[l]'(by omega)) := by
    intro l hl
    have := congrArg (fun P => P[l]?) hQQ
    simp only [List.getElem?_map, List.getElem?_eq_getElem hl,
      List.getElem?_eq_getElem (show l < Q.length by omega), Option.map_some,
      Option.some.injEq] at this
    exact this
  have hL₂get : ∀ u (hu : u < ((X.arcCut i ζ).arcCutList j₀ θ).length),
      ((X.arcCut i ζ).arcCutList j₀ θ)[u] =
        .inl ⟨(X.arcCutList i ζ)[t + u]'(by omega), hc.getElem_mem ⟨t + u, by omega⟩⟩ := by
    intro u hu
    have := hL₂ u (by omega)
    rw [List.getElem?_eq_getElem hu] at this
    exact Option.some_injective _ this
  -- the darts of `Q` in `X`
  have hQX : X.IsStrandPath (Q.map Subtype.val) := by
    rw [hQQ] at hQ₂Y
    obtain ⟨Q'', hQ'', hQ''X⟩ := hc.exists_isStrandPath_of_isStrandPath_cut hpre
      (s := ζ.cutShift) hQ₂Y
    rwa [(List.map_injective_iff.2 Sum.inl_injective) hQ'']
  have htripX : ∀ l (hl : l + 1 < Q.length),
      X.inv (Q[l]'(by omega)).1 ∉ X.arcCutList i ζ := by
    intro l hl
    have h := (htrip l (by omega)).2
    rw [hQ₂get l (by omega), hinvY] at h
    obtain ⟨d, hdL, hd⟩ := hc.cut_not_isBoundaryVertex_iff.1 h
    rwa [← Sum.inl_injective hd] at hdL
  have hndY : ∀ l l' (hl : l + 1 < Q.length) (hl' : l' + 1 < Q.length),
      X.vertexOf (X.inv (Q[l]'(by omega)).1) = X.vertexOf (X.inv (Q[l']'(by omega)).1) →
        l = l' := by
    intro l l' hl hl' h
    apply hsimple l l' (by omega) (by omega)
    rw [hQ₂get l (by omega), hQ₂get l' (by omega), hinvY, hinvY]
    change (X.cut _ _ ζ.cutShift).vertexOf _ = (X.cut _ _ ζ.cutShift).vertexOf _
    rw [hc.cut_vertexOf_inl_of_notMem _ (htripX l hl),
      hc.cut_vertexOf_inl_of_notMem _ (htripX l' hl'), h]
  -- the two ends of `Q`, read in `X`
  have hx₁lt := (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift (sourceIndex j₂)).isLt
  have hx₂lt := (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
    (((X.arcCut i ζ).arcCut j₀ θ).arcEndIndex j₂)).isLt
  have hheadX : (X.arcCutList i ζ)[t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
      (sourceIndex j₂) : ℕ)]? = (Q.map Subtype.val).head? := by
    have h := hhead
    rw [hQQ, hL₂ _ (by omega), List.head?_map, List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < Q.length by omega), Option.map_some,
      Option.some.injEq] at h
    rw [List.head?_map, List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < Q.length by omega), Option.map_some,
      List.getElem?_eq_getElem (by omega)]
    exact congrArg some (congrArg Subtype.val (Sum.inl_injective h))
  have hlastX : (X.arcCutList i ζ)[t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
      (((X.arcCut i ζ).arcCut j₀ θ).arcEndIndex j₂) : ℕ)]? =
      (Q.map Subtype.val).getLast?.map X.inv := by
    have h := hlast
    change ((X.arcCut i ζ).arcCutList j₀ θ)[(cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ)
      θ.cutShift (((X.arcCut i ζ).arcCut j₀ θ).arcEndIndex j₂) : ℕ)]? = _ at h
    rw [hQQ, hL₂ _ (by omega), List.getLast?_map, List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show Q.length - 1 < Q.length by omega), Option.map_some,
      Option.map_some, hinvY, Option.some.injEq] at h
    rw [List.getLast?_map, List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show Q.length - 1 < Q.length by omega), Option.map_some,
      Option.map_some, List.getElem?_eq_getElem (by omega)]
    rw [show (X.arcCutList i ζ)[t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
      (((X.arcCut i ζ).arcCut j₀ θ).arcEndIndex j₂) : ℕ)] = X.inv (Q[Q.length - 1]'(by omega)).1
      from congrArg Subtype.val (Sum.inl_injective h)]
  have hends' : ((cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
      (sourceIndex j₂) : ℕ) = 0 ∧ (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
      (((X.arcCut i ζ).arcCut j₀ θ).arcEndIndex j₂) : ℕ) = 2 * k - t + w) ∨
      ((cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift (sourceIndex j₂) : ℕ) =
        2 * k - t + w ∧ (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
      (((X.arcCut i ζ).arcCut j₀ θ).arcEndIndex j₂) : ℕ) = 0) := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := hidx _ _ (by omega) (hheadX.trans h1)
      have e2 := hidx _ _ (by omega) (hlastX.trans (h2.trans (hLΛ w).symm))
      omega
    · have e1 := hidx _ _ (by omega) (hheadX.trans (h1.trans (hLΛ w).symm))
      have e2 := hidx _ _ (by omega) (hlastX.trans h2)
      omega
  -- `Q` has at least two darts, as `ḡ_t` is not in the `ζ` list
  have hn2 : 2 ≤ Q.length := by
    by_contra hn
    obtain ⟨f, rfl⟩ := List.length_eq_one_iff.1 (show Q.length = 1 by omega)
    simp only [List.map_cons, List.map_nil, List.head?_cons, List.getLast?_singleton,
      Option.map_some] at hends
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hgt _ (Option.mem_def.2 h1.symm) (List.mem_of_getElem? h2.symm)
    · have := hgt _ (Option.mem_def.2 h2.symm)
      rw [hinv] at this
      exact this (List.mem_of_getElem? h1.symm)
  -- the legs of `Y₂` at the interior positions of `I₂`
  have hleg₂ : ∀ r, ((X.arcCut i ζ).arcCut j₀ θ).endDart r =
      .inl ⟨((X.arcCut i ζ).arcCutList j₀ θ)[(cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ)
        θ.cutShift r : ℕ)], hc₂.getElem_mem _⟩ := by
    intro r
    change ((X.arcCut i ζ).cut _ _ θ.cutShift).endDart r = _
    rw [cut_endDart, hc₂.cutListDart_eq]
  have hlegI : ∀ r, r ∈ intervalInterior ((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂ I₂ ↔
      ∃ v, w < v ∧ v < a ∧ (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift r : ℕ) =
        2 * k - t + v := by
    intro r
    rw [hI₂ r]
    have hrl := (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift r).isLt
    constructor
    · rintro ⟨v, hv1, hv2, d, hd, hdK, hdK', he⟩
      refine ⟨v, hv1, hv2, ?_⟩
      rw [hleg₂] at he
      have h1 := congrArg Subtype.val (Sum.inl_injective he)
      simp only at h1
      rw [hL₂get _ hrl] at h1
      have h2 := congrArg Subtype.val (Sum.inl_injective h1)
      simp only at h2
      have h3 : (X.arcCutList i ζ)[t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ)
          θ.cutShift r : ℕ)]? = (X.arcCutList i ζ)[2 * k + v]? := by
        rw [List.getElem?_eq_getElem (by omega), h2, hLΛ]
        exact (Option.mem_def.1 hd).symm
      have := hidx _ _ (by omega) h3
      omega
    · rintro ⟨v, hv1, hv2, hr⟩
      have hv : (X.sideList ζ (X.arc i))[v]? = some ((X.arcCutList i ζ)[t +
          (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift r : ℕ)]'(by omega)) := by
        rw [← hLΛ, show 2 * k + v = t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ)
          θ.cutShift r : ℕ) by omega, List.getElem?_eq_getElem]
      have hmem := hc₂.getElem_mem ⟨_, hrl⟩
      rw [hL₂get _ hrl] at hmem
      exact ⟨v, hv1, hv2, _, Option.mem_def.2 hv, hc.getElem_mem ⟨_, by omega⟩, hmem, by
        rw [hleg₂]; congr 1; exact Subtype.ext (hL₂get _ hrl)⟩
  have hcard2 : (intervalInterior ((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂ I₂).card =
      a - 1 - w := by
    have himg : (intervalInterior ((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂ I₂).image
        (fun r => (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift r : ℕ)) =
          (Ioo w a).image (fun v => 2 * k - t + v) := by
      ext x
      simp only [mem_image, mem_Ioo]
      constructor
      · rintro ⟨r, hr, rfl⟩
        obtain ⟨v, hv1, hv2, hv⟩ := (hlegI r).1 hr
        exact ⟨v, ⟨hv1, hv2⟩, hv.symm⟩
      · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
        obtain ⟨r, hr⟩ := cutEndIndex_surjective (H := CutDart (X.arcSideDarts i ζ)
          (X.arcCutList i ζ).length) (L := (X.arcCut i ζ).arcCutList j₀ θ)
          (s := θ.cutShift) hev₂ ⟨2 * k - t + v, by omega⟩
        exact ⟨r, (hlegI r).2 ⟨v, hv1, hv2, by rw [hr]⟩, by rw [hr]⟩
    rw [← card_image_of_injective _ (fun r r' h => cutEndIndex_injective (Fin.ext h)), himg,
      card_image_of_injective _ (fun a c h => by simpa using h), Nat.card_Ioo]
    omega
  replace hcardQ : 2 * (Q₂.length - 1) =
      (intervalInterior ((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂ I₂).card := hcardQ
  have hwa : w + 2 * ((Q.map Subtype.val).length - 1) + 1 = a := by
    rw [List.length_map]
    omega
  -- the relations of the shape of `Q` in `Y₂`, read in `X`
  have htransfer : ∀ (idx : ℕ) (hidx' : idx < 2 * k + a - t) l (hl : l + 1 < Q.length) (e : ℕ),
      ((X.arcCut i ζ).arcCutList j₀ θ)[idx]?.map (X.arcCut i ζ).inv =
        some (((X.arcCut i ζ).rot ^ e) ((X.arcCut i ζ).inv (Q₂[l]'(by omega)).1)) →
      (X.arcCutList i ζ)[t + idx]?.map X.inv =
        some ((X.rot ^ e) (X.inv (Q[l]'(by omega)).1)) := by
    intro idx hidx' l hl e h
    rw [hL₂ idx hidx', Option.map_some, hinvY, hQ₂get l (by omega), hinvY] at h
    obtain ⟨hm, -, hr⟩ := hc.cut_rot_pow_inl_of_notMem (s := ζ.cutShift)
      ⟨X.inv (Q[l]'(by omega)).1, hc.inv_mem _ (Q[l]'(by omega)).2⟩ (htripX l hl) e
    change some (Sum.inl _) = some (((X.cut _ _ ζ.cutShift).rot ^ e) _) at h
    rw [hr, Option.some.injEq] at h
    rw [List.getElem?_eq_getElem (by omega), Option.map_some]
    exact congrArg some (congrArg Subtype.val (Sum.inl_injective h))
  have hQg : ∀ l (hl : l < Q.length), (Q.map Subtype.val)[l]'(by simpa using hl) = Q[l].1 :=
    fun l hl => List.getElem_map _
  have hQlen' : (Q.map Subtype.val).length = Q.length := List.length_map _
  have hn2' : 2 ≤ (Q.map Subtype.val).length := by omega
  have hQhead : (Q.map Subtype.val).head? = some (Q.map Subtype.val)[0] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have hQlast : (Q.map Subtype.val).getLast? =
      some (Q.map Subtype.val)[(Q.map Subtype.val).length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have havoid : ∀ l (hl : l + 1 < (Q.map Subtype.val).length), ∀ e ∈ X.arc i,
      X.vertexOf (X.inv (Q.map Subtype.val)[l]) ≠ X.vertexOf e ∧
        X.vertexOf (X.inv (Q.map Subtype.val)[l]) ≠ X.vertexOf (X.inv e) := by
    intro l hl
    rw [hQlen'] at hl
    rw [hQg l (by omega)]
    obtain ⟨hint, hpass⟩ := hS.avoided_of_mem_arcSideDarts hX (hc.inv_mem _ Q[l].2)
      (htripX l hl)
    exact ne_vertexOf_of_avoided hX hint hpass
  have hnd : ∀ l l' (hl : l + 1 < (Q.map Subtype.val).length)
      (hl' : l' + 1 < (Q.map Subtype.val).length),
      X.vertexOf (X.inv (Q.map Subtype.val)[l]) = X.vertexOf (X.inv (Q.map Subtype.val)[l']) →
        l = l' := by
    intro l l' hl hl' h
    rw [hQlen'] at hl hl'
    rw [hQg l (by omega), hQg l' (by omega)] at h
    exact hndY l l' hl hl' h
  have hpos2 := fun r m => val_cutEndIndex_finRotate_pow (H := CutDart (X.arcSideDarts i ζ)
    (X.arcCutList i ζ).length) (L := (X.arcCut i ζ).arcCutList j₀ θ) (s := θ.cutShift) hev₂ r m
  exact stepTwoRail_finish hX hS hL hΛ hLΛ ht ht' (Or.inr ⟨ht0, ha⟩) hQX hn2' hnd havoid hwa
    (by
    rcases hO4 with ⟨-, hint1, hrel1⟩ | ⟨-, hint2, hrel2⟩
    · -- `I₂` runs clockwise from the source of `Q`, which is `λ_w`
      have hp1 := (hint1 ((finRotate _ ^ (0 + 1)) (sourceIndex j₂))).2 ⟨0, by omega, rfl⟩
      obtain ⟨v, hv1, hv2, hv⟩ := (hlegI _).1 hp1
      rw [hpos2] at hv
      have hx : (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
          (sourceIndex j₂) : ℕ) = 2 * k - t + w ∧
          (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
            (((X.arcCut i ζ).arcCut j₀ θ).arcEndIndex j₂) : ℕ) = 0 := by
        rcases hends' with ⟨h1, -⟩ | h
        · rw [h1, hlen₂, Nat.mod_eq_of_lt (by omega)] at hv
          omega
        · exact h
      refine Or.inr ⟨?_, ?_, fun l hl => ?_⟩
      · have h := hlastX
        rw [hQlast, Option.map_some, hx.2, Nat.add_zero,
          List.getElem?_eq_getElem (by omega)] at h
        exact (Option.some_injective _ h).symm
      · rw [← hLΛ, show 2 * k + w = t + (2 * k - t + w) by omega, ← hx.1, hheadX, hQhead]
      · rw [hQlen'] at hl
        obtain ⟨h5, h4⟩ := hrel1 l (by omega)
        rw [hx.1, hlen₂, Nat.mod_eq_of_lt (by omega)] at h5 h4
        have h5' := htransfer _ (by omega) l hl 5 h5
        have h4' := htransfer _ (by omega) l hl 4 h4
        rw [show t + (2 * k - t + w + (2 * l + 1)) = 2 * k + (w + (2 * l + 1)) by omega,
          hLΛ] at h5'
        rw [show t + (2 * k - t + w + (2 * l + 2)) = 2 * k + (w + (2 * l + 2)) by omega,
          hLΛ] at h4'
        rw [hQg l (by omega)]
        exact ⟨h5', h4'⟩
    · -- `I₂` runs clockwise from the target of `Q`, whose reverse is `λ_w`
      have hq1 := (hint2 ((finRotate _ ^ (0 + 1))
        (((X.arcCut i ζ).arcCut j₀ θ).arcEndIndex j₂))).2 ⟨0, by omega, rfl⟩
      obtain ⟨v, hv1, hv2, hv⟩ := (hlegI _).1 hq1
      rw [hpos2] at hv
      have hx : (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
          (sourceIndex j₂) : ℕ) = 0 ∧
          (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
            (((X.arcCut i ζ).arcCut j₀ θ).arcEndIndex j₂) : ℕ) = 2 * k - t + w := by
        rcases hends' with h | ⟨-, h2⟩
        · exact h
        · rw [h2, hlen₂, Nat.mod_eq_of_lt (by omega)] at hv
          omega
      refine Or.inl ⟨?_, ?_, fun l hl => ?_⟩
      · have h := hheadX
        rw [hQhead, hx.1, Nat.add_zero, List.getElem?_eq_getElem (by omega)] at h
        exact (Option.some_injective _ h).symm
      · have h := hlastX
        rw [hQlast, Option.map_some, hx.2,
          show t + (2 * k - t + w) = 2 * k + w by omega, hLΛ] at h
        exact h
      · rw [hQlen'] at hl
        obtain ⟨h2, h1⟩ := hrel2 l (by omega)
        change ((X.arcCut i ζ).arcCutList j₀ θ)[((cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ)
          θ.cutShift (((X.arcCut i ζ).arcCut j₀ θ).arcEndIndex j₂) : ℕ) + (2 * l + 1)) %
            _]?.map (X.arcCut i ζ).inv = _ at h2
        change ((X.arcCut i ζ).arcCutList j₀ θ)[((cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ)
          θ.cutShift (((X.arcCut i ζ).arcCut j₀ θ).arcEndIndex j₂) : ℕ) + (2 * l + 2)) %
            _]?.map (X.arcCut i ζ).inv = _ at h1
        rw [hx.2, hlen₂, Nat.mod_eq_of_lt (by omega)] at h2 h1
        rw [← pow_one (X.arcCut i ζ).rot] at h1
        have h2' := htransfer _ (by omega) (Q₂.length - 2 - l) (by omega) 2 h2
        have h1' := htransfer _ (by omega) (Q₂.length - 2 - l) (by omega) 1 h1
        rw [show t + (2 * k - t + w + (2 * l + 1)) = 2 * k + (w + (2 * l + 1)) by omega,
          hLΛ] at h2'
        rw [show t + (2 * k - t + w + (2 * l + 2)) = 2 * k + (w + (2 * l + 2)) by omega,
          hLΛ, pow_one] at h1'
        rw [hQg _ (by omega)]
        simp only [hQlen', ← hQlen]
        exact ⟨h2', h1'⟩)

/-- **A boundary-parallel strand in the nested cut gives a rail**, the case `t ≥ 1`. Let `X` be a
triple diagram, `I` an interval of `i` with side `ζ` and `2k` interior positions, and let the arc
`S` from `s_i` be simple with `k` triple points. Let `(g₀, …, g_{2k-1}, λ₀, …, λ_{2k-1})` be the
`ζ` cut list of `S` (the legs at the interior positions of `I` followed by the `ζ` list). Let
`t ≥ 1` be such that `ḡ_{t'}` is a dart of the `ζ` list for every `t' < t` and `ḡ_t` is not, and
let `λ_a = ḡ_{t-1}`. Let `A` be the arc of `Y = X|_{S,ζ}` through `g_{t-1}`, `θ` the side of `A`
containing (the position of) `g_t`, and `Y₂ = Y|_{A,θ}`. Suppose that the arc `Q` of `Y₂` through
`g_t` (its darts are the `Sum.inl (Sum.inl f)`, `f ∈ H_ζ(S)`) has the other end leg `λ_w`, `w < a`,
and is boundary-parallel in `Y₂` along an interval `I₂` of its pair whose interior positions are
those of `λ_{w+1}, …, λ_{a-1}`. Then `X` has an aligned rail or a staggered rail of some length
`r ≥ 1` along `S` on side `ζ` with `η_{r,3} = ḡ_t`, such that for every `t' < t` the dart `ḡ_{t'}`
is not among `ρ_{0,1}, ρ_{0,2}, …, ρ_{r,1}, ρ_{r,2}` unless it is the dart `ρ_{r,2}` of a staggered
rail. -/
@[cluster_algebras "lem_step_two_rail"]
theorem IsSimpleArc.exists_rail_of_isBoundaryParallel_arcCut_arcCut (hX : X.IsTripleDiagram)
    {I : Finset (Fin (2 * b))} (hI : IsIntervalOf X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ}
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k) (hS : X.IsSimpleArc i)
    (hSk : {v | X.PassesThrough (X.arc i).toFinset v}.ncard = k) {t : ℕ} (ht0 : 0 < t)
    (ht : t < 2 * k)
    (ht' : ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∈ X.sideList ζ (X.arc i))
    (hgt : ∀ g ∈ (X.arcCutList i ζ)[t]?, X.inv g ∉ X.sideList ζ (X.arc i)) {a : ℕ}
    (ha : (X.arcCutList i ζ)[t - 1]?.map X.inv = (X.sideList ζ (X.arc i))[a]?)
    {j₀ : Fin ((X.arcCutList i ζ).length / 2)}
    (hA : ∃ g ∈ (X.arcCutList i ζ)[t - 1]?, ∃ hg : g ∈ X.arcSideDarts i ζ,
      (Sum.inl ⟨g, hg⟩ : CutDart _ _) ∈ (X.arcCut i ζ).arcDarts j₀)
    {θ : StrandSide}
    (hθ : ∃ g ∈ (X.arcCutList i ζ)[t]?, ∃ hg : g ∈ X.arcSideDarts i ζ,
      (Sum.inl ⟨g, hg⟩ : CutDart _ _) ∈ (X.arcCut i ζ).arcSideDarts j₀ θ)
    {j₂ : Fin (((X.arcCut i ζ).arcCutList j₀ θ).length / 2)}
    {Q₂ : List {d // d ∈ (X.arcCut i ζ).arcSideDarts j₀ θ}}
    (hQ₂ : Q₂.map Sum.inl = ((X.arcCut i ζ).arcCut j₀ θ).arc j₂)
    {Q : List {d // d ∈ X.arcSideDarts i ζ}} (hQQ : Q₂.map Subtype.val = Q.map Sum.inl)
    {w : ℕ} (hw : w < a)
    (hends : ((Q.map Subtype.val).head? = (X.arcCutList i ζ)[t]? ∧
        (Q.map Subtype.val).getLast?.map X.inv = (X.sideList ζ (X.arc i))[w]?) ∨
      ((Q.map Subtype.val).head? = (X.sideList ζ (X.arc i))[w]? ∧
        (Q.map Subtype.val).getLast?.map X.inv = (X.arcCutList i ζ)[t]?))
    {I₂ : Finset (Fin (2 * (((X.arcCut i ζ).arcCutList j₀ θ).length / 2)))}
    (hB₂ : ((X.arcCut i ζ).arcCut j₀ θ).IsBoundaryParallel j₂ I₂)
    (hI₂ : ∀ r, r ∈ intervalInterior ((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂ I₂ ↔
      ∃ v, w < v ∧ v < a ∧ ∃ d ∈ (X.sideList ζ (X.arc i))[v]?, ∃ (hd : d ∈ X.arcSideDarts i ζ)
        (hd' : (Sum.inl ⟨d, hd⟩ : CutDart _ _) ∈ (X.arcCut i ζ).arcSideDarts j₀ θ),
        ((X.arcCut i ζ).arcCut j₀ θ).endDart r = .inl ⟨.inl ⟨d, hd⟩, hd'⟩) :
    (∃ r, 1 ≤ r ∧ ∃ R : X.AlignedRail r, R.IsAlong (X.arc i) ζ ∧
      (X.arcCutList i ζ)[t]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3)) ∧
      ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∉ R.facingDarts) ∨
    (∃ r, 1 ≤ r ∧ ∃ R : X.StaggeredRail r, R.IsAlong (X.arc i) ζ ∧
      (X.arcCutList i ζ)[t]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3)) ∧
      ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∈ R.facingDarts →
        X.inv g = X.railDart R.rho R.eta (RailLabel.rho r 2)) := by
  have hinv := hX.inv_involutive
  obtain ⟨hΛ, hL, hLΛ⟩ := stepTwo_lists hX hI hζ hk hS hSk
  have hc := hS.isCutData_arcCutList hX ζ
  have hev := even_length_arcCutList (X := X) (i := i) ζ
  have hYt := hS.isTripleDiagram_arcCut hX ζ (by omega)
  have hYp := hYt.toIsPreTripleDiagram
  have haΛ : a < 2 * k := by
    rw [List.getElem?_eq_getElem (by omega), Option.map_some] at ha
    have := (List.getElem?_eq_some_iff.1 ha.symm).1
    omega
  have hidx : ∀ x y, x < (X.arcCutList i ζ).length →
      (X.arcCutList i ζ)[x]? = (X.arcCutList i ζ)[y]? → x = y := fun x y hx h =>
    eq_of_getElem?_eq' hc.nodup (List.getElem?_eq_getElem hx) (by rw [← h,
      List.getElem?_eq_getElem hx])
  have hlegY : ∀ r, (X.arcCut i ζ).endDart r =
      .inl ⟨(X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ)],
        hc.getElem_mem _⟩ := by
    intro r
    rw [arcCut, cut_endDart, hc.cutListDart_eq]
  have hinvY : ∀ d : {d // d ∈ X.arcSideDarts i ζ},
      (X.arcCut i ζ).inv (.inl d) = .inl ⟨X.inv d.1, hc.inv_mem _ d.2⟩ :=
    fun d => hc.cut_inv_inl hinv d
  -- the legs of `Y` lie at endpoints
  have hbY : ∀ x (hx : x < (X.arcCutList i ζ).length),
      (X.arcCut i ζ).IsBoundaryVertex ((X.arcCut i ζ).vertexOf
        (.inl ⟨(X.arcCutList i ζ)[x], hc.getElem_mem ⟨x, hx⟩⟩)) := by
    intro x hx
    obtain ⟨r, hr⟩ := cutEndIndex_surjective (H := H) (L := X.arcCutList i ζ)
      (s := ζ.cutShift) hev ⟨x, hx⟩
    have := ((X.arcCut i ζ).mem_boundaryVertices.1 (hYt.endpoint_mem r)).2
    change (X.arcCut i ζ).IsBoundaryVertex ((X.arcCut i ζ).vertexOf
      ((X.arcCut i ζ).endDart r)) at this
    rw [hlegY] at this
    simpa only [hr] using this
  -- `ḡ_{t-1} = λ_a`
  have hlam : X.inv (X.arcCutList i ζ)[t - 1] = (X.arcCutList i ζ)[2 * k + a] := by
    rw [List.getElem?_eq_getElem (by omega), Option.map_some, ← hLΛ,
      List.getElem?_eq_getElem (by omega)] at ha
    exact Option.some_injective _ ha
  -- the arc `A` is the single dart `g_{t-1}` or `λ_a`
  obtain ⟨g₁, hg₁, hg₁K, hg₁A⟩ := hA
  rw [Option.mem_def, List.getElem?_eq_getElem (by omega), Option.some.injEq] at hg₁
  subst hg₁
  have hb₁ := hbY (t - 1) (by omega)
  have hb₁' : (X.arcCut i ζ).IsBoundaryVertex ((X.arcCut i ζ).vertexOf ((X.arcCut i ζ).inv
      (.inl ⟨(X.arcCutList i ζ)[t - 1], hg₁K⟩))) := by
    rw [hinvY]
    have := hbY (2 * k + a) (by omega)
    simpa only [hlam] using this
  obtain ⟨hlenA, hsrcA⟩ := arc_eq_single hYp hg₁A hb₁ hb₁'
  have hendA : (X.arcCut i ζ).endDart ((X.arcCut i ζ).arcEndIndex j₀) =
      (X.arcCut i ζ).inv ((X.arcCut i ζ).endDart (sourceIndex j₀)) := by
    rw [endDart_arcEndIndex hYt, hlenA]
    rfl
  have hcEq : ∀ r x (hx : x < (X.arcCutList i ζ).length),
      (X.arcCut i ζ).endDart r = .inl ⟨(X.arcCutList i ζ)[x], hc.getElem_mem ⟨x, hx⟩⟩ →
        (cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ) = x := by
    intro r x hx h
    rw [hlegY] at h
    have h' := congrArg Subtype.val (Sum.inl_injective h)
    have h1 : (X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ)]? =
        (X.arcCutList i ζ)[x]? := by
      rw [List.getElem?_eq_getElem (cutEndIndex _ _ r).isLt, List.getElem?_eq_getElem hx]
      exact congrArg some h'
    exact hidx _ _ (cutEndIndex _ _ r).isLt h1
  have hends₀ : ((cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₀) : ℕ) = t - 1 ∧
      (cutEndIndex (X.arcCutList i ζ) ζ.cutShift ((X.arcCut i ζ).arcEndIndex j₀) : ℕ) =
        2 * k + a) ∨
      ((cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₀) : ℕ) = 2 * k + a ∧
      (cutEndIndex (X.arcCutList i ζ) ζ.cutShift ((X.arcCut i ζ).arcEndIndex j₀) : ℕ) =
        t - 1) := by
    rcases hsrcA with h | h
    · refine Or.inl ⟨hcEq _ _ (by omega) h, hcEq _ (2 * k + a) (by omega) ?_⟩
      rw [hendA, h, hinvY]
      simp only [hlam]
    · refine Or.inr ⟨hcEq _ (2 * k + a) (by omega) ?_, hcEq _ (t - 1) (by omega) ?_⟩
      · rw [h, hinvY]
        simp only [hlam]
      · rw [hendA, h, hYp.inv_involutive]
  -- the side `θ` and the cut list of `A`
  obtain ⟨g₂, hg₂, hg₂K, hg₂θ⟩ := hθ
  rw [Option.mem_def, List.getElem?_eq_getElem (by omega), Option.some.injEq] at hg₂
  subst hg₂
  obtain ⟨hlen₂, hL₂⟩ := arcCutList_of_single hc hev hYt hlenA (t := t) (c := 2 * k + a)
    (by omega) (by omega) (by omega) hends₀ hg₂θ
  replace hlen₂ : ((X.arcCut i ζ).arcCutList j₀ θ).length = 2 * k + a - t := hlen₂
  replace hL₂ : ∀ u (hu : u < 2 * k + a - t), ((X.arcCut i ζ).arcCutList j₀ θ)[u]? =
      some (Sum.inl ⟨(X.arcCutList i ζ)[t + u]'(by omega),
        hc.getElem_mem ⟨t + u, by omega⟩⟩) := hL₂
  exact hS.exists_rail_of_arcLength_eq_one_arcCut hX hI hζ hk hSk ht0 ht ht' hgt ha hc hL haΛ
    hlenA hlen₂ hL₂ hQ₂ hQQ hw hends hB₂ hI₂

end StepTwoRail

end TripleData

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.RailPaths
public import ClusterAlgebras.Plabic.MonogonCut
public import ClusterAlgebras.Plabic.BoundaryParallel
public import ClusterAlgebras.Plabic.External
public import ClusterAlgebras.Plabic.ThurstonMoves
public import ClusterAlgebras.Plabic.SwivelBadgons

/-!
# Returning paths under push-offs and combings

D. Thurston's straightening of the arcs of a triple diagram replaces the rotation along *rails*
(runs of triple points beside a simple strand path) by the *push-off* of a closed aligned rail or
by the *aligned* or *staggered combing* of an aligned or staggered rail. This file controls what
these local replacements do to the returning paths and to the convex monogons of the strand path
along which the rail runs, and shows that a parallel digon produces a parallel returning path.
The badgons under swivel moves,
`ClusterAlgebras.TripleData.hasBadgon_swivelMove_of_isParallelDigon` and
`ClusterAlgebras.TripleData.hasBadgon_swivelMove`, are in `ClusterAlgebras.Plabic.SwivelBadgons`,
which this file re-exports.

* A push-off along a simple arc `S` keeps a parallel returning path `U` of `S` whose ends avoid
  the inner darts of the rail, unless the push-off has a monogon: the strand path `U` avoids the
  points of the rail after its first dart, so it is a strand path of the push-off, and its ends
  keep their order in the side list.
* A push-off along a convex monogon `M` gives a convex monogon: the new strand path is a monogon
  with the same corner, and its inside is reachable from its inside list without crossing it.
* A combing along a simple arc `S` without returning paths on the side `ζ` gives an arc without
  returning paths on that side: the side `H_ζ(S')` of the new arc is contained in
  `(H_ζ(S) \ D) ∪ L'`, `D` the darts at the points of the rail and `L'` the new block of the side
  list, so a returning path of the new arc avoids `D` after its first dart, and it extends, through
  the points `y_j` of the rail, to a returning path of `S`.
* A triple diagram without monogons that has a parallel digon has a simple arc with a parallel
  returning path: one of the two strand paths of a suitable parallel digon runs along an arc, and
  the other one leaves it on one side and comes back to it, on the same side, further along.

## Main results

* `ClusterAlgebras.TripleData.ClosedAlignedRail.hasMonogon_or_isReturningPath_pushOff`: a
  push-off keeps an outer parallel returning path.
* `ClusterAlgebras.TripleData.AlignedRail.forall_not_isReturningPath_alignedComb`,
  `ClusterAlgebras.TripleData.StaggeredRail.forall_not_isReturningPath_staggeredComb`: a combing
  creates no returning path.
* `ClusterAlgebras.TripleData.exists_isReturningPath_of_hasParallelDigon`: a parallel digon yields
  a parallel returning path.
* `ClusterAlgebras.TripleData.ClosedAlignedRail.isConvexMonogon_pushOff`: a push-off keeps a
  convex monogon convex.

## Implementation notes

* Positions in lists are `0`-indexed, as in `ClusterAlgebras.Plabic.MinimalTriple`: the
  interior point `z_{l+1}` of a strand path `P` is `v(P[l]̄)`, and a returning path from `z_{a+1}`
  to `z_{c+1}` is `IsReturningPath P ζ Q a c`.
* FWZ state these results for triple diagrams. The push-off and the two combings of a
  triple diagram are triple diagrams move-equivalent to it
  (`ClusterAlgebras.TripleDiagram.exists_moveEquivalent_pushOff`,
  `ClusterAlgebras.TripleDiagram.exists_moveEquivalent_alignedComb`,
  `ClusterAlgebras.TripleDiagram.exists_moveEquivalent_staggeredComb`); this is used where the
  sides or the convexity of the new strand path are needed. The result on push-offs and returning
  paths only uses the conditions of a pre-triple diagram, and is stated for those; there the
  simplicity of the arc is part of the hypothesis that `U` is a returning path of it.
* The side `ζ` of a simple arc is the set `arcSide i v` of darts on which its winding function is
  `v`, with `v = -1` on the right and `v = 0` on the left.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset RailLabel

namespace TripleData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}

/-! ### Local replacements of the rotation -/

section LocalReplacement

variable {X X' : TripleData H b} {D : Finset H}

omit [Fintype H] [DecidableEq H] in
private theorem rot_pow_apply_of_notMem (hrot : ∀ d ∉ D, X'.rot d = X.rot d)
    (hD : ∀ d, X.rot d ∈ D ↔ d ∈ D) {d : H} (hd : d ∉ D) (k : ℕ) :
    (X'.rot ^ k) d = (X.rot ^ k) d ∧ (X.rot ^ k) d ∉ D := by
  induction k with
  | zero => exact ⟨rfl, hd⟩
  | succ k ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih.1, hrot _ ih.2]
    exact ⟨rfl, fun h => ih.2 ((hD _).1 h)⟩

private theorem vertexOf_eq_of_notMem (hrot : ∀ d ∉ D, X'.rot d = X.rot d)
    (hD : ∀ d, X.rot d ∈ D ↔ d ∈ D) {d : H} (hd : d ∉ D) :
    X'.vertexOf d = X.vertexOf d := by
  ext e
  rw [RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf]
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    rw [(rot_pow_apply_of_notMem hrot hD hd k).1]
    exact ⟨k, by simp⟩
  · intro h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    rw [← (rot_pow_apply_of_notMem hrot hD hd k).1]
    exact ⟨k, by simp⟩

omit [Fintype H] [DecidableEq H] in
private theorem rot_mem_iff_of_local (hrot : ∀ d ∉ D, X'.rot d = X.rot d)
    (hD : ∀ d, X.rot d ∈ D ↔ d ∈ D) (d : H) : X'.rot d ∈ D ↔ d ∈ D := by
  constructor
  · intro h
    by_contra hd
    rw [hrot d hd] at h
    exact hd ((hD d).1 h)
  · intro hd
    by_contra h
    have hz : X.rot.symm (X'.rot d) ∉ D := fun hz => h (by simpa using (hD _).2 hz)
    have : X'.rot (X.rot.symm (X'.rot d)) = X'.rot d := by simp [hrot _ hz]
    exact hz (by rwa [X'.rot.injective this])

private theorem mem_of_mem_vertexOf_of_local (hrot : ∀ d ∉ D, X'.rot d = X.rot d)
    (hD : ∀ d, X.rot d ∈ D ↔ d ∈ D) {d e : H} (hd : d ∈ D) (he : e ∈ X'.vertexOf d) : e ∈ D := by
  obtain ⟨k, rfl⟩ := (X'.mem_vertexOf.1 he).exists_nat_pow_eq
  clear he
  induction k with
  | zero => simpa using hd
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact (rot_mem_iff_of_local hrot hD _).2 ih

end LocalReplacement

/-! ### Strand paths and side lists -/

/-- Two strand paths with the same first dart and the same length are equal. -/
private theorem eq_of_isStrandPath {X : TripleData H b} {P Q : List H} (hP : X.IsStrandPath P)
    (hQ : X.IsStrandPath Q) (hh : P.head? = Q.head?) (hl : P.length = Q.length) : P = Q := by
  have hPg := (X.isStrandPath_iff_getElem.1 hP).2.2
  have hQg := (X.isStrandPath_iff_getElem.1 hQ).2.2
  refine List.ext_getElem hl fun t h₁ h₂ => ?_
  induction t with
  | zero =>
    rw [List.head?_eq_getElem?, List.head?_eq_getElem?, List.getElem?_eq_getElem h₁,
      List.getElem?_eq_getElem h₂] at hh
    exact Option.some_injective _ hh
  | succ t ih =>
    rw [(hPg t h₁).2, (hQg t h₂).2, ih (by omega) (by omega)]

variable {X : TripleData H b}

omit [Fintype H] [DecidableEq H] in
private theorem getElem?_flatMap_two' {α β : Type*} (f : α → List β)
    (hf : ∀ x, (f x).length = 2) :
    ∀ (L : List α) (u j : ℕ), j < 2 → (L.flatMap f)[2 * u + j]? = L[u]?.bind fun x => (f x)[j]?
  | [], u, j, _ => by simp
  | x :: L, 0, j, hj => by
    rw [List.flatMap_cons, List.getElem?_append_left (by rw [hf]; omega)]
    simp
  | x :: L, u + 1, j, hj => by
    rw [List.flatMap_cons, List.getElem?_append_right (by rw [hf]; omega), hf,
      show 2 * (u + 1) + j - 2 = 2 * u + j by omega, getElem?_flatMap_two' f hf L u j hj]
    simp

omit [Fintype H] [DecidableEq H] in
private theorem length_flatMap_two' {α β : Type*} (f : α → List β) (hf : ∀ x, (f x).length = 2) :
    ∀ L : List α, (L.flatMap f).length = 2 * L.length
  | [] => by simp
  | x :: L => by
    rw [List.flatMap_cons, List.length_append, hf, length_flatMap_two' f hf L, List.length_cons]
    ring

omit [Fintype H] [DecidableEq H] in
private theorem length_sideList' (ζ : StrandSide) (P : List H) :
    (X.sideList ζ P).length = 2 * (P.length - 1) := by
  cases ζ <;>
  · simp only [sideList]
    rw [length_flatMap_two' _ (fun x => by simp [sideDarts])]
    simp

omit [Fintype H] [DecidableEq H] in
/-- The entries of the right list: `λ_{2u+k} = σ^{k+1}(ē_{u+1})` (`0`-indexed `P[u]`). -/
private theorem getElem?_sideList_right' {P : List H} {u k : ℕ} (hk : k < 2)
    (hu : u + 2 ≤ P.length) :
    (X.sideList .right P)[2 * u + k]? = some ((X.rot ^ (k + 1)) (X.inv (P[u]'(by omega)))) := by
  simp only [sideList]
  rw [getElem?_flatMap_two' _ (fun x => by simp [sideDarts]) _ u k hk,
    List.getElem?_eq_getElem (by simp; omega), List.getElem_dropLast]
  interval_cases k <;> simp [sideDarts, pow_two]

omit [Fintype H] [DecidableEq H] in
/-- The entries of the left list: `λ_{2u+k} = σ^{k+4}(ē_{m-1-u})` (`0`-indexed
`P[m - 2 - u]`). -/
private theorem getElem?_sideList_left' {P : List H} {u k : ℕ} (hk : k < 2)
    (hu : u + 2 ≤ P.length) :
    (X.sideList .left P)[2 * u + k]? =
      some ((X.rot ^ (k + 4)) (X.inv (P[P.length - 2 - u]'(by omega)))) := by
  simp only [sideList]
  have e : P.dropLast.reverse[u]? = some (P[P.length - 2 - u]'(by omega)) := by
    rw [List.getElem?_reverse (by simp; omega)]
    simp only [List.length_dropLast, List.getElem?_dropLast]
    rw [if_pos (by omega), show P.length - 1 - 1 - u = P.length - 2 - u by omega,
      List.getElem?_eq_getElem (by omega)]
  rw [getElem?_flatMap_two' _ (fun x => by simp [sideDarts]) _ u k hk, e]
  interval_cases k <;> simp [sideDarts]

/-- Two interior points at the same vertex of a strand path with distinct interior points have the
same index. -/
private theorem eq_of_vertexOf_inv_eq_of_nodup {P : List H} (hP : (X.interiorPoints P).Nodup)
    {l l' : ℕ} (hl : l + 1 < P.length) (hl' : l' + 1 < P.length)
    (h : X.vertexOf (X.inv P[l]) = X.vertexOf (X.inv P[l'])) : l = l' := by
  simp only [interiorPoints] at hP
  have e1 : (P.dropLast.map fun e => X.vertexOf (X.inv e))[l]'(by simp; omega) =
      X.vertexOf (X.inv P[l]) := by simp
  have e2 : (P.dropLast.map fun e => X.vertexOf (X.inv e))[l']'(by simp; omega) =
      X.vertexOf (X.inv P[l']) := by simp
  exact (hP.getElem_inj_iff).1 (by rw [e1, e2, h])

/-- Two interior points of a simple strand path at the same vertex have the same index. -/
private theorem eq_of_vertexOf_inv_eq' {P : List H} (hP : X.IsSimpleStrandPath P) {l l' : ℕ}
    (hl : l + 1 < P.length) (hl' : l' + 1 < P.length)
    (h : X.vertexOf (X.inv P[l]) = X.vertexOf (X.inv P[l'])) : l = l' :=
  eq_of_vertexOf_inv_eq_of_nodup hP.nodup hl hl' h

omit [Fintype H] [DecidableEq H] in
/-- The entries of the `ζ` list: the side darts at the interior points. -/
private theorem mem_sideList_iff' {P : List H} {ζ : StrandSide} {d : H} :
    d ∈ X.sideList ζ P ↔ ∃ l, ∃ hl : l + 1 < P.length, d ∈ X.sideDarts ζ (P[l]'(by omega)) := by
  have hdl : ∀ e, e ∈ P.dropLast ↔ ∃ l, ∃ hl : l + 1 < P.length, P[l]'(by omega) = e := by
    intro e
    rw [List.mem_iff_getElem]
    constructor
    · rintro ⟨l, hl, rfl⟩
      simp only [List.length_dropLast] at hl
      exact ⟨l, by omega, by simp⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, by simp; omega, by simp⟩
  cases ζ <;> simp only [sideList, List.mem_flatMap, List.mem_reverse, hdl] <;>
  · constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, h⟩
      exact ⟨l, hl, h⟩
    · rintro ⟨l, hl, h⟩
      exact ⟨_, ⟨l, hl, rfl⟩, h⟩

/-- The side darts at `v(ē)` lie at `v(ē)`. -/
private theorem vertexOf_of_mem_sideDarts' {ζ : StrandSide} {e f : H}
    (hf : f ∈ X.sideDarts ζ e) : X.vertexOf f = X.vertexOf (X.inv e) := by
  cases ζ <;> simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hf <;>
    rcases hf with rfl | rfl <;> simp [X.vertexOf_rot_pow_apply, X.vertexOf_rot]

/-- The `ζ` list of a simple strand path has no repeated entry. -/
private theorem nodup_sideList' (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsSimpleStrandPath P) (ζ : StrandSide) : (X.sideList ζ P).Nodup := by
  have hPg := X.isStrandPath_iff_getElem.1 hP.isStrandPath
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hj
  rw [length_sideList'] at hj
  have key : ∀ (e : ℕ) (u u' k k' : ℕ) (hk : k < 2) (hk' : k' < 2) (pos : ℕ → ℕ)
      (hpos : ∀ u, u + 2 ≤ P.length → pos u + 1 < P.length)
      (hposinj : ∀ u u', u + 2 ≤ P.length → u' + 2 ≤ P.length → pos u = pos u' → u = u')
      (he : e + 1 < 6) (hu : u + 2 ≤ P.length) (hu' : u' + 2 ≤ P.length),
      (X.rot ^ (k + e)) (X.inv (P[pos u]'(by have := hpos u hu; omega))) =
        (X.rot ^ (k' + e)) (X.inv (P[pos u']'(by have := hpos u' hu'; omega))) →
        u = u' ∧ k = k' := by
    intro e u u' k k' hk hk' pos hpos hposinj he hu hu' h
    have hv := congrArg X.vertexOf h
    rw [X.vertexOf_rot_pow_apply, X.vertexOf_rot_pow_apply] at hv
    have huu := hposinj u u' hu hu' (eq_of_vertexOf_inv_eq' hP (hpos u hu) (hpos u' hu') hv)
    subst huu
    refine ⟨rfl, ?_⟩
    have := (hX.rot_pow_six (hPg.2.2 (pos u) (hpos u hu)).1).2 _ _ (by omega) (by omega) h
    omega
  obtain ⟨u, k, hk, rfl⟩ : ∃ u k, k < 2 ∧ i = 2 * u + k := ⟨i / 2, i % 2, by omega, by omega⟩
  obtain ⟨u', k', hk', rfl⟩ : ∃ u k, k < 2 ∧ j = 2 * u + k := ⟨j / 2, j % 2, by omega, by omega⟩
  cases ζ with
  | right =>
    rw [getElem?_sideList_right' hk (by omega), getElem?_sideList_right' hk' (by omega), ne_eq,
      Option.some_inj]
    intro h
    have := key 1 u u' k k' hk hk' id (fun u hu => by simp; omega) (fun u u' _ _ h => h)
      (by norm_num) (by omega) (by omega) h
    omega
  | left =>
    rw [getElem?_sideList_left' hk (by omega), getElem?_sideList_left' hk' (by omega), ne_eq,
      Option.some_inj]
    intro h
    have := key 4 u u' k k' hk hk' (fun u => P.length - 2 - u) (fun u hu => by omega)
      (fun u u' hu hu' h => by omega) (by norm_num) (by omega) (by omega) h
    omega

/-- The vertex of the reverse of a dart of a strand path is the vertex of the next dart, or the
end of the path. -/
private theorem vertexOf_inv_mem_of_isStrandPath {P : List H} (hP : X.IsStrandPath P) {e : H}
    (he : e ∈ P) : (∃ e' ∈ P, X.vertexOf (X.inv e) = X.vertexOf e') ∨
      X.vertexOf (X.inv e) = X.pathEnd P := by
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem he
  by_cases hl' : l + 1 < P.length
  · have hs := (X.isStrandPath_iff_getElem.1 hP).2.2 l hl'
    exact Or.inl ⟨_, List.getElem_mem hl', hs.vertexOf_eq.symm⟩
  · right
    have hlast : P.getLast? = some P[l] := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      congr 2
      omega
    rw [X.pathEnd_of_getLast? hlast]

/-- The interior point `z_{l+1} = v(ē_{l+1})` of a strand path is one of its interior points. -/
private theorem mem_interiorPoints' {P : List H} {l : ℕ} (hl : l + 1 < P.length) :
    X.vertexOf (X.inv (P[l]'(by omega))) ∈ X.interiorPoints P := by
  simp only [interiorPoints, List.mem_map]
  exact ⟨P[l]'(by omega), List.mem_iff_getElem.2 ⟨l, by simp; omega, by simp⟩, rfl⟩

omit [Fintype H] [DecidableEq H] in
/-- The entry of index `t` of the `ζ` list is a side dart at the interior point of index `t / 2`
(right) or `m - 2 - t / 2` (left), `m` the length of the path. -/
private theorem exists_mem_sideDarts_of_getElem? {P : List H} {ζ : StrandSide} {t : ℕ} {f : H}
    (h : (X.sideList ζ P)[t]? = some f) :
    ∃ a, ∃ ha : a + 1 < P.length, f ∈ X.sideDarts ζ (P[a]'(by omega)) ∧
      (ζ = .right → t / 2 = a) ∧ (ζ = .left → t / 2 + a + 2 = P.length) := by
  obtain ⟨ht, -⟩ := List.getElem?_eq_some_iff.1 h
  rw [length_sideList'] at ht
  obtain ⟨u, k, hk, rfl⟩ : ∃ u k, k < 2 ∧ t = 2 * u + k := ⟨t / 2, t % 2, by omega, by omega⟩
  cases ζ with
  | right =>
    rw [getElem?_sideList_right' hk (by omega), Option.some_inj] at h
    refine ⟨u, by omega, ?_, fun _ => by omega, fun h => absurd h (by decide)⟩
    subst h
    interval_cases k <;> simp [sideDarts, pow_two]
  | left =>
    rw [getElem?_sideList_left' hk (by omega), Option.some_inj] at h
    refine ⟨P.length - 2 - u, by omega, ?_, fun h => absurd h (by decide), fun _ => by omega⟩
    subst h
    interval_cases k <;> simp [sideDarts]

omit [Fintype H] [DecidableEq H] in
/-- A side dart at the interior point of index `a` is an entry of the `ζ` list, of index `t` with
`t / 2 = a` (right) or `t / 2 = m - 2 - a` (left). -/
private theorem exists_getElem?_of_mem_sideDarts {P : List H} {ζ : StrandSide} {a : ℕ}
    (ha : a + 1 < P.length) {f : H} (hf : f ∈ X.sideDarts ζ (P[a]'(by omega))) :
    ∃ t, (X.sideList ζ P)[t]? = some f ∧
      (ζ = .right → t / 2 = a) ∧ (ζ = .left → t / 2 + a + 2 = P.length) := by
  cases ζ with
  | right =>
    simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · refine ⟨2 * a + 0, ?_, fun _ => by omega, fun h => absurd h (by decide)⟩
      rw [getElem?_sideList_right' (by norm_num) (by omega)]
      simp
    · refine ⟨2 * a + 1, ?_, fun _ => by omega, fun h => absurd h (by decide)⟩
      rw [getElem?_sideList_right' (by norm_num) (by omega)]
  | left =>
    have e : P[P.length - 2 - (P.length - 2 - a)]'(by omega) = P[a] := by
      congr 1
      omega
    simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · refine ⟨2 * (P.length - 2 - a) + 0, ?_, fun h => absurd h (by decide), fun _ => by omega⟩
      rw [getElem?_sideList_left' (by norm_num) (by omega), e]
    · refine ⟨2 * (P.length - 2 - a) + 1, ?_, fun h => absurd h (by decide), fun _ => by omega⟩
      rw [getElem?_sideList_left' (by norm_num) (by omega), e]

omit [Fintype H] [DecidableEq H] in
/-- Replacing a block `F` of a list by a block `B` with the same first and last entries and two
entries fewer shifts the entries after the block by `2`. -/
private theorem getElem?_append_shift {L₁ F B L₂ : List H} {t : ℕ}
    (hFB : F.length = B.length + 2) (hB : 0 < B.length) (h0 : F[0]? = B[0]?)
    (hlast : F[F.length - 1]? = B[B.length - 1]?)
    (ht : t ≤ L₁.length ∨ L₁.length + F.length - 1 ≤ t) :
    (L₁ ++ B ++ L₂)[if t ≤ L₁.length then t else t - 2]? = (L₁ ++ F ++ L₂)[t]? := by
  rw [List.append_assoc, List.append_assoc]
  split_ifs with h
  · rcases Nat.lt_or_ge t L₁.length with h' | h'
    · rw [List.getElem?_append_left h', List.getElem?_append_left h']
    · obtain rfl : t = L₁.length := by omega
      have e1 : (L₁ ++ (B ++ L₂))[L₁.length]? = B[0]? := by
        rw [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_append_left hB]
      have e2 : (L₁ ++ (F ++ L₂))[L₁.length]? = F[0]? := by
        rw [List.getElem?_append_right le_rfl, Nat.sub_self,
          List.getElem?_append_left (by omega)]
      rw [e1, e2, h0]
  · have e1 : (L₁ ++ (B ++ L₂))[t - 2]? = (B ++ L₂)[t - 2 - L₁.length]? :=
      List.getElem?_append_right (by omega)
    have e2 : (L₁ ++ (F ++ L₂))[t]? = (F ++ L₂)[t - L₁.length]? :=
      List.getElem?_append_right (by omega)
    rw [e1, e2]
    rcases Nat.lt_or_ge (t - L₁.length) F.length with h' | h'
    · rw [show t - L₁.length = F.length - 1 by omega, List.getElem?_append_left (by omega),
        show t - 2 - L₁.length = B.length - 1 by omega, List.getElem?_append_left (by omega),
        hlast]
    · rw [List.getElem?_append_right h', List.getElem?_append_right (by omega)]
      congr 1
      omega

omit [Fintype H] [DecidableEq H] in
private theorem getElem?_append_mid {L₁ F L₂ : List H} {t : ℕ} (h1 : L₁.length ≤ t)
    (h2 : t < L₁.length + F.length) : (L₁ ++ F ++ L₂)[t]? = F[t - L₁.length]? := by
  rw [List.append_assoc, List.getElem?_append_right h1, List.getElem?_append_left (by omega)]

private theorem RailPoints.dart_eta' {p q : ℕ} (R : X.RailPoints p q) (j k : ℕ) :
    R.dart (RailLabel.eta j k) = (X.rot ^ k) (R.eta j) := rfl

private theorem RailPoints.getElem?_facingDarts' {p q : ℕ} (R : X.RailPoints p q) {s : ℕ}
    (hs : s < 2 * (p + 1)) :
    R.facingDarts[s]? = some (R.dart (RailLabel.rho (s / 2) (s % 2 + 1))) := by
  simp [RailPoints.facingDarts, hs]

private theorem mem_interiorPoints_iff' {P : List H} {z : Finset H} :
    z ∈ X.interiorPoints P ↔ ∃ t, ∃ ht : t + 1 < P.length, z = X.vertexOf (X.inv P[t]) := by
  unfold interiorPoints
  constructor
  · intro hz
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
    rw [List.length_dropLast] at ht
    exact ⟨t, by omega, by rw [List.getElem_dropLast]⟩
  · rintro ⟨t, ht, rfl⟩
    exact List.mem_map.2 ⟨P[t], List.mem_iff_getElem.2 ⟨t, by simp; omega, by simp⟩, rfl⟩

/-- The darts of a rail lie at triple points. -/
private theorem rail_not_isBoundaryVertex_of_mem_darts {X : TripleData H b} {p q : ℕ}
    (R : X.RailPoints p q) {d : H} (hd : d ∈ R.darts) : ¬X.IsBoundaryVertex (X.vertexOf d) := by
  obtain ⟨a', ha', hda⟩ := R.mem_darts.1 hd
  rw [X.vertexOf_eq_of_mem hda]
  exact (X.mem_internalVertices.1 (R.vertexOf_mem a' ha')).2

/-! ### Closed aligned rails along a simple strand path -/

namespace ClosedAlignedRail

variable {n : ℕ}

/-- The labels `ρ_{0,1}`, `η_{j,1}`, `η_{j,2}` (`j ∈ [1, n - 1]`) and `ρ_{n,2}` of the block that a
push-off puts into the side list. -/
private def IsBlockLabel (n : ℕ) (l : RailLabel) : Prop :=
  l = rho 0 1 ∨ l = rho n 2 ∨ ∃ j, 1 ≤ j ∧ j ≤ n - 1 ∧ (l = eta j 1 ∨ l = eta j 2)

/-- The block `(ρ_{0,1}, η_{1,1}, η_{1,2}, …, η_{n-1,1}, η_{n-1,2}, ρ_{n,2})` of the side list
after a push-off. -/
private def pushOffBlock (R : X.ClosedAlignedRail n) : List H :=
  R.railPoints.dart (rho 0 1) :: ((List.range' 1 (n - 1)).flatMap fun j =>
    [R.railPoints.dart (eta j 1), R.railPoints.dart (eta j 2)]) ++ [R.railPoints.dart (rho n 2)]

private theorem mem_pushOffBlock (R : X.ClosedAlignedRail n) {d : H} :
    d ∈ R.pushOffBlock ↔ ∃ l, IsBlockLabel n l ∧ d = R.railPoints.dart l := by
  simp only [pushOffBlock, IsBlockLabel, List.mem_append, List.mem_cons, List.mem_flatMap,
    List.mem_range'_1, List.not_mem_nil, or_false]
  constructor
  · rintro ((rfl | ⟨j, ⟨hj1, hj2⟩, rfl | rfl⟩) | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inr ⟨j, hj1, by omega, Or.inl rfl⟩), rfl⟩
    · exact ⟨_, Or.inr (Or.inr ⟨j, hj1, by omega, Or.inr rfl⟩), rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
  · rintro ⟨l, rfl | rfl | ⟨j, hj1, hj2, rfl | rfl⟩, rfl⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr rfl
    · exact Or.inl (Or.inr ⟨j, ⟨hj1, by omega⟩, Or.inl rfl⟩)
    · exact Or.inl (Or.inr ⟨j, ⟨hj1, by omega⟩, Or.inr rfl⟩)

private theorem isBlockLabel_mem_labelSet {l : RailLabel} (hl : IsBlockLabel n l) :
    l ∈ labelSet n (n - 1) := by
  rcases hl with rfl | rfl | ⟨j, hj1, hj2, rfl | rfl⟩
  · exact rho_mem_labelSet (Nat.zero_le _) (by norm_num)
  · exact rho_mem_labelSet le_rfl (by norm_num)
  · exact eta_mem_labelSet hj1 hj2 (by norm_num)
  · exact eta_mem_labelSet hj1 hj2 (by norm_num)

private theorem dart_mem_pushOffBlock_iff (hX : X.IsPreTripleDiagram) (R : X.ClosedAlignedRail n)
    {l : RailLabel} (hl : l ∈ labelSet n (n - 1)) :
    R.railPoints.dart l ∈ R.pushOffBlock ↔ IsBlockLabel n l := by
  rw [mem_pushOffBlock]
  constructor
  · rintro ⟨l', hb, he⟩
    rwa [RailPoints.injOn_dart hX hl (isBlockLabel_mem_labelSet hb) he]
  · exact fun hb => ⟨l, hb, rfl⟩

/-- At the point `x_j` of a rail along a simple strand path on side `ζ`, the side darts of the
path are `ρ_{j,1}, ρ_{j,2}`. -/
private theorem _root_.ClusterAlgebras.TripleData.RailPoints.exists_sideDarts_eq'
    (hX : X.IsPreTripleDiagram) {p q : ℕ} (R : X.RailPoints p q)
    {P : List H} (hP : X.IsSimpleStrandPath P) {ζ : StrandSide} (hR : R.IsAlong P ζ) {j : ℕ}
    (hj : j ≤ p) :
    ∃ l, ∃ hl : l + 1 < P.length, X.vertexOf (R.rho j) = X.vertexOf (X.inv P[l]) ∧
      X.sideDarts ζ P[l] = [R.dart (rho j 1), R.dart (rho j 2)] := by
  obtain ⟨l, hl, hv, hr, hlft⟩ := RailPoints.IsAlong.exists_pass hX hP hR j hj
  refine ⟨l, hl, hv, ?_⟩
  have e3 : ∀ (k : ℕ) (x : H), (X.rot ^ k) ((X.rot ^ 3) x) = (X.rot ^ (k + 3)) x := fun k x => by
    rw [pow_add, Equiv.Perm.mul_apply]
  cases ζ with
  | right =>
    obtain ⟨h1, -⟩ := hr rfl
    change _ = [(X.rot ^ 1) (R.rho j), (X.rot ^ 2) (R.rho j)]
    rw [h1, pow_one]
    rfl
  | left =>
    obtain ⟨h1, -⟩ := hlft rfl
    have hs := (X.isStrandPath_iff_getElem.1 hP.isStrandPath).2.2 l hl
    change _ = [(X.rot ^ 1) (R.rho j), (X.rot ^ 2) (R.rho j)]
    rw [h1, hs.2, e3, e3]
    rfl

/-- A dart at a vertex of a strand path along which a rail runs lies at a point of the rail iff
that vertex is a point `x_j`. -/
private theorem _root_.ClusterAlgebras.TripleData.RailPoints.mem_darts_iff_of_along'
    {p q : ℕ} (R : X.RailPoints p q) {P : List H}
    {ζ : StrandSide} (hR : R.IsAlong P ζ) {d e : H} (he : e ∈ P)
    (hde : X.vertexOf d = X.vertexOf e ∨ X.vertexOf d = X.vertexOf (X.inv e)) :
    d ∈ R.darts ↔ ∃ j ≤ p, X.vertexOf d = X.vertexOf (R.rho j) := by
  rw [RailPoints.mem_darts]
  constructor
  · rintro ⟨a | a, ha, hd⟩
    · simp only [pointSet, mem_disjSum, mem_range, Sum.inl.injEq] at ha
      exact ⟨a, by simpa using ha, X.vertexOf_eq_of_mem hd⟩
    · have ha' : 1 ≤ a ∧ a ≤ q := by simpa [pointSet] using ha
      have hv : X.vertexOf d = X.vertexOf (R.eta a) := X.vertexOf_eq_of_mem hd
      obtain ⟨h1, h2⟩ := hR.2 a ha'.1 ha'.2 e he
      rcases hde with h | h
      · exact absurd (hv.symm.trans h) h1
      · exact absurd (hv.symm.trans h) h2
  · rintro ⟨j, hj, hv⟩
    refine ⟨.inl j, by simp [pointSet]; omega, ?_⟩
    change d ∈ X.vertexOf (R.rho j)
    rw [← hv]
    exact X.self_mem_vertexOf d

/-- At the point `x_j` of a closed aligned rail along a simple strand path on side `ζ`, the side
darts of the path are `ρ_{j,1}, ρ_{j,2}`. -/
private theorem exists_sideDarts_eq (hX : X.IsPreTripleDiagram) (R : X.ClosedAlignedRail n)
    {P : List H} (hP : X.IsSimpleStrandPath P) {ζ : StrandSide} (hR : R.IsAlong P ζ) {j : ℕ}
    (hj : j ≤ n) :
    ∃ l, ∃ hl : l + 1 < P.length, X.vertexOf (R.rho j) = X.vertexOf (X.inv P[l]) ∧
      X.sideDarts ζ P[l] = [R.railPoints.dart (rho j 1), R.railPoints.dart (rho j 2)] :=
  R.railPoints.exists_sideDarts_eq' hX hP hR hj

/-- A dart at a vertex of a strand path along which the rail runs lies at a point of the rail iff
that vertex is a point `x_j`. -/
private theorem mem_darts_iff_of_along (R : X.ClosedAlignedRail n) {P : List H}
    {ζ : StrandSide} (hR : R.IsAlong P ζ) {d e : H} (he : e ∈ P)
    (hde : X.vertexOf d = X.vertexOf e ∨ X.vertexOf d = X.vertexOf (X.inv e)) :
    d ∈ R.railPoints.darts ↔ ∃ j ≤ n, X.vertexOf d = X.vertexOf (R.rho j) :=
  R.railPoints.mem_darts_iff_of_along' hR he hde

/-- The reverse of a dart of the rail that is not in the block of the push-off and, at the points
`x_j`, is one of `ρ_{j,1}, ρ_{j,2}`, is again such a dart of the rail. -/
private theorem exists_inv_dart_eq (hX : X.IsPreTripleDiagram) (R : X.ClosedAlignedRail n)
    {l : RailLabel} (hl : l ∈ labelSet n (n - 1))
    (hk : ∀ j k, l = rho j k → k = 1 ∨ k = 2) (hB : ¬IsBlockLabel n l) :
    ∃ l' ∈ labelSet n (n - 1), ¬IsBlockLabel n l' ∧
      X.inv (R.railPoints.dart l) = R.railPoints.dart l' := by
  have hn := R.one_le
  have rA : ∀ j < n - 1, X.inv (R.railPoints.dart (alignedEta j 3)) =
      R.railPoints.dart (eta (j + 1) 0) := R.inv_eta_three
  have rB : ∀ j, 1 ≤ j → j ≤ n - 1 →
      X.inv (R.railPoints.dart (rho j 1)) = R.railPoints.dart (eta j 5) := R.inv_rho_one
  have rC : ∀ j, 1 ≤ j → j ≤ n - 1 →
      X.inv (R.railPoints.dart (rho j 2)) = R.railPoints.dart (eta j 4) := R.inv_rho_two
  have rD : X.inv (R.railPoints.dart (alignedEta (n - 1) 3)) = R.railPoints.dart (rho n 1) :=
    R.inv_eta_three_last
  have flip : ∀ {d e : H}, X.inv d = e → X.inv e = d := fun h => by rw [← h, hX.inv_inv_apply]
  rcases mem_labelSet.1 hl with ⟨j, hj, k, hk6, rfl⟩ | ⟨j, hj1, hj2, k, hk6, rfl⟩
  · rcases hk j k rfl with rfl | rfl
    · have hj0 : j ≠ 0 := fun h => hB (Or.inl (by rw [h]))
      by_cases hjn : j = n
      · subst hjn
        refine ⟨alignedEta (j - 1) 3, alignedEta_mem_labelSet (by omega) (by norm_num), ?_,
          flip rD⟩
        intro hb
        by_cases h1 : j - 1 = 0
        · simp [alignedEta, h1, alignedIndex, IsBlockLabel, rho, eta] at hb
          omega
        · simp [alignedEta, h1, IsBlockLabel, rho, eta] at hb
      · exact ⟨eta j 5, eta_mem_labelSet (by omega) (by omega) (by norm_num),
          by simp [IsBlockLabel, rho, eta], rB j (by omega) (by omega)⟩
    · have hjn : j ≠ n := fun h => hB (Or.inr (Or.inl (by rw [h])))
      by_cases hj0 : j = 0
      · subst hj0
        by_cases hn1 : n = 1
        · subst hn1
          refine ⟨rho 1 1, rho_mem_labelSet le_rfl (by norm_num),
            by simp [IsBlockLabel, rho, eta], ?_⟩
          simpa [alignedEta, alignedIndex] using rD
        · refine ⟨eta 1 0, eta_mem_labelSet le_rfl (by omega) (by norm_num),
            by simp [IsBlockLabel, rho, eta], ?_⟩
          simpa [alignedEta, alignedIndex] using rA 0 (by omega)
      · exact ⟨eta j 4, eta_mem_labelSet (by omega) (by omega) (by norm_num),
          by simp [IsBlockLabel, rho, eta], rC j (by omega) (by omega)⟩
  · have hk1 : k ≠ 1 := fun h => hB (Or.inr (Or.inr ⟨j, hj1, hj2, Or.inl (by rw [h])⟩))
    have hk2 : k ≠ 2 := fun h => hB (Or.inr (Or.inr ⟨j, hj1, hj2, Or.inr (by rw [h])⟩))
    interval_cases k
    · by_cases hj : j = 1
      · subst hj
        refine ⟨rho 0 2, rho_mem_labelSet (by omega) (by norm_num), ?_, ?_⟩
        · simp [IsBlockLabel, rho, eta]
          omega
        · exact flip (by simpa [alignedEta, alignedIndex] using rA 0 (by omega))
      · refine ⟨eta (j - 1) 3, eta_mem_labelSet (by omega) (by omega) (by norm_num),
          by simp [IsBlockLabel, rho, eta], ?_⟩
        have := rA (j - 1) (by omega)
        rw [show j - 1 + 1 = j by omega] at this
        exact flip (by simpa [alignedEta, show j - 1 ≠ 0 by omega] using this)
    · exact absurd rfl hk1
    · exact absurd rfl hk2
    · by_cases hj : j = n - 1
      · subst hj
        refine ⟨rho n 1, rho_mem_labelSet le_rfl (by norm_num), ?_, ?_⟩
        · simp [IsBlockLabel, rho, eta]
          omega
        · simpa [alignedEta, show n - 1 ≠ 0 by omega] using rD
      · refine ⟨eta (j + 1) 0, eta_mem_labelSet (by omega) (by omega) (by norm_num),
          by simp [IsBlockLabel, rho, eta], ?_⟩
        simpa [alignedEta, show j ≠ 0 by omega] using rA j (by omega)
    · refine ⟨rho j 2, rho_mem_labelSet (by omega) (by norm_num), ?_, flip (rC j hj1 hj2)⟩
      simp [IsBlockLabel, rho, eta]
      omega
    · refine ⟨rho j 1, rho_mem_labelSet (by omega) (by norm_num), ?_, flip (rB j hj1 hj2)⟩
      simp [IsBlockLabel, rho, eta]
      omega

end ClosedAlignedRail

/-! ### A push-off keeps a convex monogon convex -/

namespace ClosedAlignedRail

variable {n : ℕ}

/-- **A push-off keeps a convex monogon convex**. Let `M = (e₁, …, e_m)` be a convex monogon of a
triple diagram `X` with inside `ζ`, `n ≥ 1`, and `X'` the push-off of a closed aligned rail of
length `n` of `X` along `M` on side `ζ`. Then the strand path `M'` of `X'` with first dart `e₁` and
`m - 1` darts is a convex monogon of `X'` with inside `ζ`. -/
@[cluster_algebras "lem_push_off_convex"]
theorem isConvexMonogon_pushOff (hX : X.IsTripleDiagram) {M : List H} {ζ : StrandSide}
    (hM : X.IsConvexMonogon M ζ) (R : X.ClosedAlignedRail n) (hR : R.IsAlong M ζ)
    {M' : List H} (hM' : R.pushOff.IsStrandPath M') (hlen : M'.length + 1 = M.length)
    (hhead : M'.head? = M.head?) : R.pushOff.IsConvexMonogon M' ζ := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv : Function.Involutive X.inv := hX.inv_involutive
  have hn := R.one_le
  set X' := R.pushOff with hX'def
  set RP := R.railPoints with hRP
  set D := RP.darts with hDdef
  have hR' : RP.IsAlong M ζ := hR
  have hrot : ∀ d ∉ D, X'.rot d = X.rot d := fun d hd => R.pushOff_rot_of_notMem hd
  have hDrot : ∀ d, X.rot d ∈ D ↔ d ∈ D := RP.rot_mem_darts_iff
  obtain ⟨hX'tri, -⟩ := TripleDiagram.exists_moveEquivalent_pushOff ⟨H, X, hX⟩ R
  obtain ⟨P', hP's, hP'len, hP'head, hP'last, hfilt, L₁, L₂, hsl, hsl'⟩ :=
    exists_isSimpleStrandPath_pushOff hpre R hM.isSimpleStrandPath hR'
  obtain rfl : M' = P' :=
    eq_of_isStrandPath hM' hP's.isStrandPath (hhead.trans hP'head.symm) (by omega)
  have hsl'' : X'.sideList ζ M' = L₁ ++ R.pushOffBlock ++ L₂ := hsl'
  -- the darts at the points of the rail
  have hD : ∀ d ∈ D, X.vertexOf d ⊆ D := by
    intro d hd e he
    obtain ⟨a, ha, hda⟩ := RP.mem_darts.1 hd
    rw [X.vertexOf_eq_of_mem hda] at he
    exact RP.mem_darts.2 ⟨a, ha, he⟩
  have hDbdry : ∀ d ∈ D, d ∉ X.bdry := fun d hd hdB =>
    rail_not_isBoundaryVertex_of_mem_darts RP hd ⟨d, X.self_mem_vertexOf d, hdB⟩
  -- the first and last darts of `M`
  have h0 : 0 < M.length := hM.length_pos
  have hMhead : M.head? = some M[0] := by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
  have hMlast : M.getLast? = some M[M.length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have hstart : X.pathStart M = X.vertexOf M[0] := X.pathStart_of_head? hMhead
  have hend : X.vertexOf (X.inv M[M.length - 1]) = X.vertexOf M[0] := by
    rw [← X.pathEnd_of_getLast? hMlast, hM.isMonogon.pathEnd_eq, hstart]
  have hxD : ∀ d ∈ X.vertexOf M[0], d ∉ D := by
    intro d hd hdD
    obtain ⟨j, hj, hv⟩ := (mem_darts_iff_of_along R hR (List.getElem_mem h0)
      (Or.inl (X.vertexOf_eq_of_mem hd))).1 hdD
    obtain ⟨l, hl, hvl, -⟩ := exists_sideDarts_eq hpre R hM.isSimpleStrandPath hR hj
    apply hM.isSimpleStrandPath.pathStart_notMem
    rw [hstart, show X.vertexOf M[0] = X.vertexOf (X.inv M[l]) from
      (X.vertexOf_eq_of_mem hd).symm.trans (hv.trans hvl)]
    exact mem_interiorPoints' hl
  have he1D : M[0] ∉ D := hxD _ (X.self_mem_vertexOf _)
  have hemD : X.inv M[M.length - 1] ∉ D := hxD _ (by rw [← hend]; exact X.self_mem_vertexOf _)
  have hv'1 : X'.vertexOf M[0] = X.vertexOf M[0] := vertexOf_eq_of_notMem hrot hDrot he1D
  have hv'm : X'.vertexOf (X'.inv M[M.length - 1]) = X.vertexOf M[0] :=
    (vertexOf_eq_of_notMem hrot hDrot hemD).trans hend
  have hxint : ¬X.IsBoundaryVertex (X.vertexOf M[0]) := by
    have := hM.isMonogon.pathStart_mem
    rw [hstart] at this
    exact (X.mem_internalVertices.1 this).2
  have hP'head0 : M'.head? = some M[0] := hP'head.trans hMhead
  have hP'last0 : M'.getLast? = some M[M.length - 1] := hP'last.trans hMlast
  have hP'start : X'.pathStart M' = X.vertexOf M[0] := by
    rw [X'.pathStart_of_head? hP'head0, hv'1]
  -- `M'` is a monogon of `X'`
  have hP'mono : X'.IsMonogon M' := by
    refine ⟨hP's.isStrandPath, ?_, ?_, ?_⟩
    · rw [hP'start, ← hv'1]
      exact X'.vertexOf_mem_internalVertices.2 (by rwa [hv'1])
    · rw [X'.pathEnd_of_getLast? hP'last0, hv'm, hP'start]
    · intro e₁ he₁ eₘ heₘ
      rw [hP'head0, Option.mem_some_iff] at he₁
      rw [hP'last0, Option.mem_some_iff] at heₘ
      subst he₁ heₘ
      rw [(rot_pow_apply_of_notMem hrot hDrot he1D 3).1]
      exact hM.isMonogon.inv_ne _ (by rw [hMhead]; rfl) _ (by rw [hMlast]; rfl)
  -- the corner condition
  have hcorner : ∀ e₁ ∈ M'.head?, ∀ eₘ ∈ M'.getLast?, X'.IsInsideCorner ζ e₁ eₘ := by
    intro e₁ he₁ eₘ heₘ
    rw [hP'head0, Option.mem_some_iff] at he₁
    rw [hP'last0, Option.mem_some_iff] at heₘ
    subst he₁ heₘ
    have hc := hM.isInsideCorner _ (by rw [hMhead]; rfl) _ (by rw [hMlast]; rfl)
    cases ζ with
    | right =>
      change X'.rot (X.inv M[M.length - 1]) = M[0]
      rw [hrot _ hemD]
      exact hc
    | left =>
      change X'.rot M[0] = X.inv M[M.length - 1]
      rw [hrot _ he1D]
      exact hc
  -- the inside darts
  obtain ⟨h, hh, -⟩ := existsUnique_isMonogonWindingFunction hX hM.isMonogon hM.isSimpleStrandPath
  set K := X.insideDarts M ζ h with hKdef
  have hKinv : ∀ d ∈ K, X.inv d ∈ K := fun d hd => (inv_mem_insideDarts_iff hpre hh h0 d).2 hd
  have hKrot : ∀ d ∈ K, ¬X.IsBoundaryVertex (X.vertexOf d) →
      (∀ e ∈ M, X.vertexOf d ≠ X.vertexOf e ∧ X.vertexOf d ≠ X.vertexOf (X.inv e)) →
      X.rot d ∈ K ∧ X.rot.symm d ∈ K := fun d hd hb hav =>
    ⟨(mem_insideDarts_iff_of_forall_ne hX hM.isMonogon hh hb (fun e he => (hav e he).1)
        (X.rot_mem_vertexOf d)).2 hd,
      (mem_insideDarts_iff_of_forall_ne hX hM.isMonogon hh hb (fun e he => (hav e he).1)
        (X.rot_symm_mem_vertexOf d)).2 hd⟩
  have hsideK : ∀ d ∈ X.sideList ζ M, d ∈ K := fun d hd =>
    hM.mem_insideDarts_of_mem_insideList hX hh hd
  have hKrho : ∀ j ≤ n, ∀ k < 6, RP.dart (rho j k) ∈ K → k = 1 ∨ k = 2 := by
    intro j hj k hk hK
    obtain ⟨l, hl, hvl, hsd⟩ := exists_sideDarts_eq hpre R hM.isSimpleStrandPath hR hj
    have hmem : RP.dart (rho j k) ∈ X.vertexOf (X.inv M[l]) := by
      rw [← hvl]
      exact RP.dart_mem_vertexOf (rho j k)
    have := (hM.mem_insideDarts_iff_mem_sideDarts hX hh hl hmem).1 hK
    rw [hsd] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h' | h'
    · have := RailPoints.injOn_dart hpre (rho_mem_labelSet hj hk)
        (rho_mem_labelSet hj (by norm_num)) h'
      simp only [rho, Prod.mk.injEq] at this
      exact Or.inl this.2
    · have := RailPoints.injOn_dart hpre (rho_mem_labelSet hj hk)
        (rho_mem_labelSet hj (by norm_num)) h'
      simp only [rho, Prod.mk.injEq] at this
      exact Or.inr this.2
  have hrhoside : ∀ j ≤ n, RP.dart (rho j 1) ∈ X.sideList ζ M ∧
      RP.dart (rho j 2) ∈ X.sideList ζ M := by
    intro j hj
    obtain ⟨l, hl, -, hsd⟩ := exists_sideDarts_eq hpre R hM.isSimpleStrandPath hR hj
    exact ⟨mem_sideList_iff'.2 ⟨l, hl, by rw [hsd, hRP]; simp⟩,
      mem_sideList_iff'.2 ⟨l, hl, by rw [hsd, hRP]; simp⟩⟩
  have hKeta : ∀ j, 1 ≤ j → j ≤ n - 1 → ∀ k < 6, RP.dart (eta j k) ∈ K := by
    intro j hj1 hj2 k hk
    have e5 : RP.dart (eta j 5) = X.inv (RP.dart (rho j 1)) := (R.inv_rho_one j hj1 hj2).symm
    have h5 : RP.dart (eta j 5) ∈ K := by
      rw [e5]
      exact hKinv _ (hsideK _ (hrhoside j (by omega)).1)
    have hvy : ∀ k, X.vertexOf (RP.dart (eta j k)) = X.vertexOf (RP.eta j) := fun k =>
      X.vertexOf_eq_of_mem (RP.dart_mem_vertexOf (eta j k))
    have hyb : ¬X.IsBoundaryVertex (X.vertexOf (RP.dart (eta j 5))) := by
      rw [hvy]
      exact (X.mem_internalVertices.1 (RP.vertexOf_mem (.inr j) (by simp [pointSet]; omega))).2
    have hyav : ∀ e ∈ M, X.vertexOf (RP.dart (eta j 5)) ≠ X.vertexOf e := fun e he => by
      rw [hvy]
      exact (hR'.2 j hj1 hj2 e he).1
    have hmem : RP.dart (eta j k) ∈ X.vertexOf (RP.dart (eta j 5)) := by
      rw [hvy, ← hvy k]
      exact X.self_mem_vertexOf _
    exact (mem_insideDarts_iff_of_forall_ne hX hM.isMonogon hh hyb hyav hmem).2 h5
  -- the block of the new side list
  set L' := R.pushOffBlock.toFinset with hL'def
  have hL'sub : L' ⊆ D ∩ K := by
    intro d hd
    obtain ⟨l, hlB, rfl⟩ := (mem_pushOffBlock R).1 (List.mem_toFinset.1 hd)
    refine mem_inter.2 ⟨RP.dart_mem_darts (isBlockLabel_mem_labelSet hlB), ?_⟩
    rcases hlB with rfl | rfl | ⟨j, hj1, hj2, rfl | rfl⟩
    · exact hsideK _ (hrhoside 0 (Nat.zero_le _)).1
    · exact hsideK _ (hrhoside n le_rfl).2
    · exact hKeta j hj1 hj2 1 (by norm_num)
    · exact hKeta j hj1 hj2 2 (by norm_num)
  have hL'inv : ∀ d ∈ (D ∩ K) \ L', X.inv d ∈ (D ∩ K) \ L' := by
    intro d hd
    obtain ⟨hdDK, hdL⟩ := mem_sdiff.1 hd
    obtain ⟨hdD, hdK⟩ := mem_inter.1 hdDK
    obtain ⟨l, hl, rfl⟩ : ∃ l ∈ labelSet n (n - 1), RP.dart l = d := by
      rw [hDdef, ← RailPoints.image_dart hpre] at hdD
      exact mem_image.1 hdD
    have hlB : ¬IsBlockLabel n l := fun hb =>
      hdL (List.mem_toFinset.2 ((mem_pushOffBlock R).2 ⟨l, hb, rfl⟩))
    have hk : ∀ j k, l = rho j k → k = 1 ∨ k = 2 := by
      rintro j k rfl
      have : j ≤ n ∧ k < 6 := by simpa [labelSet, pointSet, rho] using hl
      exact hKrho j this.1 k this.2 hdK
    obtain ⟨l', hl', hl'B, he⟩ := exists_inv_dart_eq hpre R hl hk hlB
    rw [he]
    refine mem_sdiff.2 ⟨mem_inter.2 ⟨RP.dart_mem_darts hl', he ▸ hKinv _ hdK⟩, fun h' => hl'B ?_⟩
    exact (dart_mem_pushOffBlock_iff hpre R hl').1 (List.mem_toFinset.1 h')
  have hL'list : ∀ d ∈ L', d ∈ X'.sideList ζ M' := by
    intro d hd
    rw [hsl'']
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_toFinset.1 hd))
  have hpts : ∀ v ∈ X.internalVertices, Disjoint v D →
      (∃ e ∈ M, v = X.vertexOf e ∨ v = X.vertexOf (X.inv e)) →
      ∃ e ∈ M', v = X'.vertexOf e ∨ v = X'.vertexOf (X'.inv e) := by
    rintro v - hvD ⟨e, he, hve⟩
    obtain ⟨e₀, he₀, hve₀⟩ : ∃ e₀ ∈ M, v = X.vertexOf e₀ := by
      rcases hve with h' | h'
      · exact ⟨e, he, h'⟩
      · rcases vertexOf_inv_mem_of_isStrandPath hM.isMonogon.isStrandPath he with
          ⟨e', he', h''⟩ | h''
        · exact ⟨e', he', h'.trans h''⟩
        · refine ⟨M[0], List.getElem_mem h0, ?_⟩
          rw [h', h'', hM.isMonogon.pathEnd_eq, hstart]
    have he₀D : e₀ ∉ D := fun h' =>
      disjoint_left.1 hvD (by rw [hve₀]; exact X.self_mem_vertexOf e₀) h'
    have he₀P' : e₀ ∈ M' := by
      have : e₀ ∈ M.filter (· ∉ D) := List.mem_filter.2 ⟨he₀, by simpa using he₀D⟩
      rw [← hfilt] at this
      exact (List.mem_filter.1 this).1
    exact ⟨e₀, he₀P', Or.inl (by rw [hve₀, vertexOf_eq_of_notMem hrot hDrot he₀D])⟩
  have hcl := reach_of_local_replacement (X := X) (X' := X') rfl rfl hinv hrot hD
    (P := M) (P' := M') (ζ := ζ) (K := K) (L' := L') hKinv hKrot hL'sub hL'inv hL'list hpts
  -- the darts of the side list of `M'` lie in `(K \ D) ∪ L'`
  have hnotD : ∀ d, d ∈ L₁ ∨ d ∈ L₂ → d ∉ D := by
    intro d hdL hdD
    have hdM : d ∈ X.sideList ζ M := by
      rw [hsl]
      rcases hdL with h' | h' <;> simp [h']
    obtain ⟨l, hl, hds⟩ := mem_sideList_iff'.1 hdM
    have hvd := vertexOf_of_mem_sideDarts' hds
    obtain ⟨j, hj, hvj⟩ := (mem_darts_iff_of_along R hR (List.getElem_mem (by omega))
      (Or.inr hvd)).1 hdD
    obtain ⟨l', hl', hvl', hsd'⟩ := exists_sideDarts_eq hpre R hM.isSimpleStrandPath hR hj
    obtain rfl : l = l' :=
      eq_of_vertexOf_inv_eq' hM.isSimpleStrandPath hl hl' (hvd.symm.trans (hvj.trans hvl'))
    rw [hsd'] at hds
    have hdF : d ∈ RP.facingDarts := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hds
      rcases hds with rfl | rfl
      · rw [← RP.getElem_facingDarts_two_mul hj]
        exact List.getElem_mem _
      · rw [← RP.getElem_facingDarts_two_mul_add_one hj]
        exact List.getElem_mem _
    have hnd := nodup_sideList' hpre hM.isSimpleStrandPath ζ
    rw [hsl] at hnd
    rcases hdL with h' | h'
    · exact List.disjoint_of_nodup_append (List.Nodup.of_append_left hnd) h' hdF
    · rw [List.append_assoc] at hnd
      exact List.disjoint_of_nodup_append (List.Nodup.of_append_right hnd) hdF h'
  have hST : {d | d ∈ X'.sideList ζ M'} ⊆ ((K \ D) ∪ L' : Finset H) := by
    intro d hd
    simp only [Set.mem_setOf_eq] at hd
    rw [hsl''] at hd
    rw [mem_coe]
    rcases List.mem_append.1 hd with hd | hd
    · rcases List.mem_append.1 hd with hd | hd
      · exact mem_union_left _ (mem_sdiff.2 ⟨hsideK d (by rw [hsl]; simp [hd]),
          hnotD d (Or.inl hd)⟩)
      · exact mem_union_right _ (List.mem_toFinset.2 hd)
    · exact mem_union_left _ (mem_sdiff.2 ⟨hsideK d (by rw [hsl]; simp [hd]),
        hnotD d (Or.inr hd)⟩)
  have hT : X'.IsClosedOff M' ((K \ D) ∪ L' : Finset H) := by
    refine ⟨fun d hd => mem_coe.2 (hcl.1 d (mem_coe.1 hd)), fun d hd hb hav => ?_⟩
    have := hcl.2 d (mem_coe.1 hd) hb (fun e he => ⟨hav e he, ?_⟩)
    · exact ⟨mem_coe.2 this.1, mem_coe.2 this.2⟩
    rcases vertexOf_inv_mem_of_isStrandPath hP's.isStrandPath he with ⟨e', he', h'⟩ | h'
    · rw [h']
      exact hav e' he'
    · rw [h', hP'mono.pathEnd_eq, X'.pathStart_of_head? hP'head0]
      exact hav _ (List.mem_of_mem_head? hP'head0)
  have hK' : ∀ d ∈ X'.avoidingClosure M' {d | d ∈ X'.sideList ζ M'},
      ¬X'.IsBoundaryVertex (X'.vertexOf d) := by
    intro d hd
    have hdT := X'.avoidingClosure_subset hST hT hd
    rcases mem_union.1 (mem_coe.1 hdT) with h' | h'
    · obtain ⟨hdK, hdD⟩ := mem_sdiff.1 h'
      rw [vertexOf_eq_of_notMem hrot hDrot hdD]
      exact fun hb => hM.notMem_insideDarts_of_isBoundaryVertex hX hh hb hdK
    · have hdD := (mem_inter.1 (hL'sub h')).1
      rintro ⟨e, he, heB⟩
      exact hDbdry e (mem_of_mem_vertexOf_of_local hrot hDrot hdD he) heB
  exact isConvexMonogon_of_avoidingClosure (X := X') hX'tri hP'mono hP's hcorner hK'

end ClosedAlignedRail


/-! ### A push-off keeps an outer parallel returning path -/

namespace ClosedAlignedRail

variable {n : ℕ}

private theorem length_pushOffBlock (R : X.ClosedAlignedRail n) :
    R.pushOffBlock.length = 2 * n := by
  have hn := R.one_le
  simp only [pushOffBlock, List.length_append, List.length_cons, List.length_nil]
  rw [length_flatMap_two' _ (fun _ => rfl), List.length_range']
  omega

private theorem getElem?_pushOffBlock_zero (R : X.ClosedAlignedRail n) :
    R.pushOffBlock[0]? = some (R.railPoints.dart (rho 0 1)) := by
  simp [pushOffBlock]

private theorem getElem?_pushOffBlock_last (R : X.ClosedAlignedRail n) :
    R.pushOffBlock[R.pushOffBlock.length - 1]? = some (R.railPoints.dart (rho n 2)) := by
  rw [← List.getLast?_eq_getElem?]
  exact List.getLast?_concat

/-- After its first dart, a returning path whose first dart and the reverse of whose last dart
avoid the inner darts `ρ_{0,2}, ρ_{j,1}, ρ_{j,2}, ρ_{n,1}` of a closed aligned rail along the path
meets no point of the rail. -/
private theorem notMem_darts_of_isReturningPath (hX : X.IsPreTripleDiagram)
    (R : X.ClosedAlignedRail n) {P : List H} {ζ : StrandSide} (hR : R.IsAlong P ζ) {U : List H}
    {a c : ℕ} (hU : X.IsReturningPath P ζ U a c)
    (hfirst : ∀ f ∈ U.head?, f ≠ R.railPoints.dart (rho 0 2) ∧
      f ≠ R.railPoints.dart (rho n 1) ∧ ∀ j, 1 ≤ j → j ≤ n - 1 →
        f ≠ R.railPoints.dart (rho j 1) ∧ f ≠ R.railPoints.dart (rho j 2))
    (hlast : ∀ g ∈ U.getLast?, ∀ j, 1 ≤ j → j ≤ n - 1 →
        X.inv g ≠ R.railPoints.dart (rho j 1) ∧ X.inv g ≠ R.railPoints.dart (rho j 2)) :
    ∀ p (hp : p + 1 < U.length), ∀ d ∈ X.vertexOf U[p + 1], d ∉ R.railPoints.darts := by
  have hn := R.one_le
  have hS : X.IsSimpleStrandPath P := hU.isSimpleStrandPath
  have hR' : R.railPoints.IsAlong P ζ := hR
  have hUs := hU.isStrandPath
  have hUg := X.isStrandPath_iff_getElem.1 hUs
  have hq : 0 < U.length := List.length_pos_iff.2 hUs.ne_nil
  have hUhead : U.head? = some U[0] := by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hq]
  have hUlast : U.getLast? = some U[U.length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  obtain ⟨hf1, hf2, hf3⟩ := hfirst _ hUhead
  have hl3 := hlast _ hUlast
  have hint : ∀ t (ht : t + 1 < U.length), ∀ e ∈ P,
      X.vertexOf (X.inv U[t]) ≠ X.vertexOf e ∧ X.vertexOf (X.inv U[t]) ≠ X.vertexOf (X.inv e) :=
    fun t ht => hU.interiorPoints_ne _ (mem_interiorPoints' ht)
  have hintx : ∀ t (ht : t + 1 < U.length), ∀ j ≤ n,
      X.vertexOf (X.inv U[t]) ≠ X.vertexOf (R.rho j) := by
    intro t ht j hj h
    obtain ⟨l, hl, hv, -⟩ := exists_sideDarts_eq hX R hS hR hj
    exact (hint t ht _ (List.getElem_mem (by omega : l < P.length))).2 (h.trans hv)
  have hnotx : ∀ p (hp : p + 1 < U.length), ∀ j ≤ n,
      X.vertexOf U[p + 1] ≠ X.vertexOf (R.rho j) := fun p hp j hj => by
    rw [(hUg.2.2 p hp).vertexOf_eq]
    exact hintx p hp j hj
  obtain ⟨e₀, he₀, f₀, hf₀, hf₀s⟩ := hU.head?_mem
  have hla := hU.lt_left
  obtain rfl : e₀ = P[a] := Option.some_injective _ (he₀.symm.trans
    (List.getElem?_eq_getElem (by omega)))
  obtain rfl : f₀ = U[0] := Option.some_injective _ (hf₀.symm.trans hUhead)
  have hU0v : X.vertexOf U[0] = X.vertexOf (X.inv P[a]) := vertexOf_of_mem_sideDarts' hf₀s
  have hy0 : ∀ j, 1 ≤ j → j ≤ n - 1 → X.vertexOf U[0] ≠ X.vertexOf (R.eta j) := fun j h1 h2 h =>
    (hR'.2 j h1 h2 _ (List.getElem_mem (by omega))).2 (h.symm.trans hU0v)
  have hyint : ∀ j, 1 ≤ j → j ≤ n - 1 → ¬X.IsBoundaryVertex (X.vertexOf (R.eta j)) :=
    fun j h1 h2 =>
      (X.mem_internalVertices.1 (R.railPoints.vertexOf_mem (.inr j)
        (by simp [pointSet]; omega))).2
  have hrot3eta : ∀ j, 1 ≤ j → j ≤ n - 1 → ∀ k,
      (X.rot ^ 3) (R.railPoints.dart (eta j k)) = R.railPoints.dart (eta j ((k + 3) % 6)) := by
    intro j h1 h2 k
    rw [RailPoints.dart_eta', RailPoints.dart_eta', ← Equiv.Perm.mul_apply, ← pow_add]
    exact (hX.rot_pow_mod_six (hyint j h1 h2) _).trans
      (by rw [show (3 + k) % 6 = (k + 3) % 6 by omega]; rfl)
  have hprev : ∀ p (hp : p + 1 < U.length), X.inv U[p] = (X.rot ^ 3) U[p + 1] := by
    intro p hp
    rw [(hUg.2.2 p hp).2, hX.rot_pow_three_rot_pow_three (hUg.2.2 p hp).1]
  have rA : ∀ j < n - 1, X.inv (R.railPoints.dart (alignedEta j 3)) =
      R.railPoints.dart (eta (j + 1) 0) := R.inv_eta_three
  have rB : ∀ j, 1 ≤ j → j ≤ n - 1 →
      X.inv (R.railPoints.dart (rho j 1)) = R.railPoints.dart (eta j 5) := R.inv_rho_one
  have rC : ∀ j, 1 ≤ j → j ≤ n - 1 →
      X.inv (R.railPoints.dart (rho j 2)) = R.railPoints.dart (eta j 4) := R.inv_rho_two
  have rD : X.inv (R.railPoints.dart (alignedEta (n - 1) 3)) = R.railPoints.dart (rho n 1) :=
    R.inv_eta_three_last
  have flip : ∀ {d e : H}, X.inv d = e → X.inv e = d := fun h => by rw [← h, hX.inv_inv_apply]
  have hvrho : ∀ j k, X.vertexOf (R.railPoints.dart (rho j k)) = X.vertexOf (R.rho j) :=
    fun j k => X.vertexOf_eq_of_mem (R.railPoints.dart_mem_vertexOf (rho j k))
  have hveta : ∀ j k, X.vertexOf (R.railPoints.dart (eta j k)) = X.vertexOf (R.eta j) :=
    fun j k => X.vertexOf_eq_of_mem (R.railPoints.dart_mem_vertexOf (eta j k))
  have hfirst_x : ∀ p (hp : p < U.length), ∀ j ≤ n,
      X.vertexOf U[p] = X.vertexOf (R.rho j) → p = 0 := by
    intro p hp j hj h
    rcases p with _ | p
    · rfl
    · exact absurd h (hnotx p hp j hj)
  have hlast_x : ∀ p (hp : p < U.length), ∀ j ≤ n,
      X.vertexOf (X.inv U[p]) = X.vertexOf (R.rho j) → p + 1 = U.length := by
    intro p hp j hj h
    by_contra h'
    exact hintx p (by omega) j hj h
  have hC3 : ∀ j, 1 ≤ j → j ≤ n - 1 → ∀ p (hp : p + 1 < U.length),
      U[p + 1] ≠ R.railPoints.dart (eta j 3) := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro h1 h2 p hp heq
      have hinvp : X.inv U[p] = R.railPoints.dart (eta (j + 1) 0) := by
        rw [hprev p hp, heq, hrot3eta (j + 1) h1 h2 3]
      have hUp : U[p] = R.railPoints.dart (alignedEta j 3) := by
        rw [← hX.inv_inv_apply U[p], hinvp]
        exact flip (rA j (by omega))
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have hUp' : U[p] = R.railPoints.dart (rho 0 2) := by
          simpa [alignedEta, alignedIndex] using hUp
        obtain rfl : p = 0 :=
          hfirst_x p (by omega) 0 (Nat.zero_le _) (by rw [hUp']; exact hvrho 0 2)
        exact hf1 hUp'
      · have hUp' : U[p] = R.railPoints.dart (eta j 3) := by
          simpa [alignedEta, show j ≠ 0 by omega] using hUp
        rcases p with _ | p
        · exact hy0 j hj0 (by omega) (by rw [hUp']; exact hveta j 3)
        · exact ih hj0 (by omega) p (by omega) hUp'
  have hC0 : ∀ m j, j + m = n - 1 → 1 ≤ j → ∀ p (hp : p + 1 < U.length),
      U[p + 1] ≠ R.railPoints.dart (eta j 0) := by
    intro m
    induction m with
    | zero =>
      intro j hjm h1 p hp heq
      have hinvp : X.inv U[p] = R.railPoints.dart (eta j 3) := by
        rw [hprev p hp, heq, hrot3eta j h1 (by omega) 0]
      have hUp : U[p] = R.railPoints.dart (rho n 1) := by
        rw [← hX.inv_inv_apply U[p], hinvp]
        simpa [alignedEta, show n - 1 = j by omega, show j ≠ 0 by omega] using rD
      obtain rfl : p = 0 := hfirst_x p (by omega) n le_rfl (by rw [hUp]; exact hvrho n 1)
      exact hf2 hUp
    | succ m ih =>
      intro j hjm h1 p hp heq
      have hinvp : X.inv U[p] = R.railPoints.dart (eta j 3) := by
        rw [hprev p hp, heq, hrot3eta j h1 (by omega) 0]
      have hUp : U[p] = R.railPoints.dart (eta (j + 1) 0) := by
        rw [← hX.inv_inv_apply U[p], hinvp]
        simpa [alignedEta, show j ≠ 0 by omega] using rA j (by omega)
      rcases p with _ | p
      · exact hy0 (j + 1) (by omega) (by omega) (by rw [hUp]; exact hveta _ _)
      · exact ih (j + 1) (by omega) (by omega) p (by omega) hUp
  have hnoty : ∀ p (hp : p + 1 < U.length), ∀ j, 1 ≤ j → j ≤ n - 1 →
      X.vertexOf U[p + 1] ≠ X.vertexOf (R.eta j) := by
    intro p hp j h1 h2 hv
    have hmem : U[p + 1] ∈ X.vertexOf (R.railPoints.eta j) := by
      rw [show R.railPoints.eta j = R.eta j from rfl, ← hv]
      exact X.self_mem_vertexOf _
    obtain ⟨k, hk, hk'⟩ := X.exists_pow_apply_eq_of_card_vertexOf (d := R.railPoints.eta j)
      (hX.internalVertex_card _ (R.railPoints.vertexOf_mem (.inr j)
        (by simp [pointSet]; omega))) hmem
    have hUeq : U[p + 1] = R.railPoints.dart (eta j k) := by
      rw [RailPoints.dart_eta', hk']
    have hidx : p + 2 = U.length → U[U.length - 1] = U[p + 1] := fun h => by
      congr 1
      omega
    interval_cases k
    · exact hC0 (n - 1 - j) j (by omega) h1 p hp hUeq
    · have hinvp : X.inv U[p] = R.railPoints.dart (eta j 4) := by
        rw [hprev p hp, hUeq, hrot3eta j h1 h2 1]
      have hUp : U[p] = R.railPoints.dart (rho j 2) := by
        rw [← hX.inv_inv_apply U[p], hinvp]
        exact flip (rC j h1 h2)
      obtain rfl : p = 0 := hfirst_x p (by omega) j (by omega) (by rw [hUp]; exact hvrho j 2)
      exact (hf3 j h1 h2).2 hUp
    · have hinvp : X.inv U[p] = R.railPoints.dart (eta j 5) := by
        rw [hprev p hp, hUeq, hrot3eta j h1 h2 2]
      have hUp : U[p] = R.railPoints.dart (rho j 1) := by
        rw [← hX.inv_inv_apply U[p], hinvp]
        exact flip (rB j h1 h2)
      obtain rfl : p = 0 := hfirst_x p (by omega) j (by omega) (by rw [hUp]; exact hvrho j 1)
      exact (hf3 j h1 h2).1 hUp
    · exact hC3 j h1 h2 p hp hUeq
    · have hinv : X.inv U[p + 1] = R.railPoints.dart (rho j 2) := by
        rw [hUeq]
        exact flip (rC j h1 h2)
      have := hlast_x (p + 1) hp j (by omega) (by rw [hinv]; exact hvrho j 2)
      exact (hl3 j h1 h2).2 (by rw [hidx this]; exact hinv)
    · have hinv : X.inv U[p + 1] = R.railPoints.dart (rho j 1) := by
        rw [hUeq]
        exact flip (rB j h1 h2)
      have := hlast_x (p + 1) hp j (by omega) (by rw [hinv]; exact hvrho j 1)
      exact (hl3 j h1 h2).1 (by rw [hidx this]; exact hinv)
  intro p hp d hd hdD
  obtain ⟨a', ha', hda⟩ := R.railPoints.mem_darts.1 hdD
  have hv : X.vertexOf U[p + 1] = X.vertexOf (Sum.elim R.railPoints.rho R.railPoints.eta a') :=
    (X.vertexOf_eq_of_mem hd).symm.trans (X.vertexOf_eq_of_mem hda)
  rcases a' with j | j
  · have hj : j ≤ n := by simp [pointSet] at ha'; omega
    exact hnotx p hp j hj hv
  · have hj : 1 ≤ j ∧ j ≤ n - 1 := by simpa [pointSet] using ha'
    exact hnoty p hp j hj.1 hj.2 hv


/-- For a closed aligned rail of length `1`, a strand path of the push-off from `ρ_{0,1}` back to
`ρ_{1,2}`, or from `ρ_{1,2}` back to `ρ_{0,1}`, is a monogon: both darts lie at the vertex
`(ρ_{0,0}, ρ_{0,1}, ρ_{1,2}, ρ_{1,3}, ρ_{0,2}, ρ_{0,3})` of the push-off. -/
private theorem hasMonogon_pushOff_one (hX : X.IsPreTripleDiagram) (R : X.ClosedAlignedRail 1)
    {U : List H} (hUs' : R.pushOff.IsStrandPath U) (hq : 0 < U.length)
    (hUhead : U.head? = some U[0]) (hUlast : U.getLast? = some U[U.length - 1])
    (hends : (U[0] = R.railPoints.dart (rho 0 1) ∧
        X.inv U[U.length - 1] = R.railPoints.dart (rho 1 2)) ∨
        (U[0] = R.railPoints.dart (rho 1 2) ∧
          X.inv U[U.length - 1] = R.railPoints.dart (rho 0 1))) :
    R.pushOff.HasMonogon := by
  have hrot : ∀ d ∉ R.railPoints.darts, R.pushOff.rot d = X.rot d := fun d hd =>
    R.pushOff_rot_of_notMem hd
  have hDrot : ∀ d, X.rot d ∈ R.railPoints.darts ↔ d ∈ R.railPoints.darts :=
    R.railPoints.rot_mem_darts_iff
  have hDint : ∀ d ∈ R.railPoints.darts, ¬X.IsBoundaryVertex (X.vertexOf d) :=
    fun _ hd => rail_not_isBoundaryVertex_of_mem_darts R.railPoints hd
  have hl : ([alignedEta 0 5, alignedEta 0 2, rho 1 2, rho 1 3, alignedEta 0 3, rho 0 3].map
      R.railPoints.dart) ∈ R.pushOffTuples :=
    List.mem_map.2 ⟨_, by simp [pushOffLabels], rfl⟩
  have r1 : R.pushOff.rot (R.railPoints.dart (rho 0 1)) = R.railPoints.dart (rho 1 2) := by
    simpa [alignedEta, alignedIndex] using R.pushOff_rot_getElem hX hl 1 (by simp)
  have r2 : R.pushOff.rot (R.railPoints.dart (rho 1 2)) = R.railPoints.dart (rho 1 3) := by
    simpa [alignedEta, alignedIndex] using R.pushOff_rot_getElem hX hl 2 (by simp)
  have r3 : R.pushOff.rot (R.railPoints.dart (rho 1 3)) = R.railPoints.dart (rho 0 2) := by
    simpa [alignedEta, alignedIndex] using R.pushOff_rot_getElem hX hl 3 (by simp)
  have r4 : R.pushOff.rot (R.railPoints.dart (rho 0 2)) = R.railPoints.dart (rho 0 3) := by
    simpa [alignedEta, alignedIndex] using R.pushOff_rot_getElem hX hl 4 (by simp)
  have hne : ∀ j k j' k', j ≤ 1 → k < 6 → j' ≤ 1 → k' < 6 → (j ≠ j' ∨ k ≠ k') →
      R.railPoints.dart (rho j k) ≠ R.railPoints.dart (rho j' k') := by
    intro j k j' k' hj hk hj' hk' hjk h
    have := RailPoints.injOn_dart hX (rho_mem_labelSet hj hk) (rho_mem_labelSet hj' hk') h
    simp only [rho, Prod.mk.injEq, Sum.inl.injEq] at this
    omega
  have hv12 : R.pushOff.vertexOf (R.railPoints.dart (rho 1 2)) =
      R.pushOff.vertexOf (R.railPoints.dart (rho 0 1)) := by
    rw [← r1, R.pushOff.vertexOf_rot]
  have hU0D : U[0] ∈ R.railPoints.darts := by
    rcases hends with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact R.railPoints.dart_mem_darts (rho_mem_labelSet (Nat.zero_le _) (by norm_num))
    · exact R.railPoints.dart_mem_darts (rho_mem_labelSet le_rfl (by norm_num))
  refine ⟨U, hUs', ?_, ?_, ?_⟩
  · rw [R.pushOff.pathStart_of_head? hUhead]
    refine R.pushOff.vertexOf_mem_internalVertices.2 ?_
    rintro ⟨d, hd, hdB⟩
    exact hDint d (mem_of_mem_vertexOf_of_local hrot hDrot hU0D hd)
      (X.isBoundaryVertex_vertexOf_of_mem hdB)
  · rw [R.pushOff.pathEnd_of_getLast? hUlast, R.pushOff.pathStart_of_head? hUhead]
    change R.pushOff.vertexOf (X.inv U[U.length - 1]) = R.pushOff.vertexOf U[0]
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hv12
    · exact hv12.symm
  · intro e₁ he₁ eₘ heₘ
    rw [hUhead, Option.mem_some_iff] at he₁
    rw [hUlast, Option.mem_some_iff] at heₘ
    subst he₁ heₘ
    change X.inv U[U.length - 1] ≠ R.pushOff.rot (R.pushOff.rot (R.pushOff.rot U[0]))
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · rw [r1, r2, r3]
      exact hne 1 2 0 2 le_rfl (by norm_num) (Nat.zero_le _) (by norm_num) (by omega)
    · rw [r2, r3, r4]
      exact hne 0 1 0 3 (Nat.zero_le _) (by norm_num) (Nat.zero_le _) (by norm_num) (by omega)

/-- **A push-off keeps an outer parallel returning path**. Let `S` be the simple arc from `s_i` of
a pre-triple diagram `X`, `ζ` a side, `n ≥ 1`, and `X'` the push-off of a closed aligned rail of
length `n` of `X` along `S` on side `ζ`. Let `U` be a parallel returning path of `S` on side `ζ`
such that neither its first dart nor the reverse of its last dart is one of `ρ_{0,2}`, `ρ_{n,1}`,
`ρ_{j,1}`, `ρ_{j,2}` (`j ∈ [1, n - 1]`). Then `X'` has a monogon, or `U` is a parallel returning
path on side `ζ` of the arc of `X'` from `s_i`. -/
@[cluster_algebras "lem_push_off_returning"]
theorem hasMonogon_or_isReturningPath_pushOff (hX : X.IsPreTripleDiagram) {i : Fin b}
    {ζ : StrandSide} (R : X.ClosedAlignedRail n) (hR : R.IsAlong (X.arc i) ζ) {U : List H}
    {a c : ℕ} (hU : X.IsReturningPath (X.arc i) ζ U a c) (hac : a < c)
    (hfirst : ∀ f ∈ U.head?, f ≠ R.railPoints.dart (rho 0 2) ∧
      f ≠ R.railPoints.dart (rho n 1) ∧ ∀ j, 1 ≤ j → j ≤ n - 1 →
        f ≠ R.railPoints.dart (rho j 1) ∧ f ≠ R.railPoints.dart (rho j 2))
    (hlast : ∀ g ∈ U.getLast?, X.inv g ≠ R.railPoints.dart (rho 0 2) ∧
      X.inv g ≠ R.railPoints.dart (rho n 1) ∧ ∀ j, 1 ≤ j → j ≤ n - 1 →
        X.inv g ≠ R.railPoints.dart (rho j 1) ∧ X.inv g ≠ R.railPoints.dart (rho j 2)) :
    R.pushOff.HasMonogon ∨
      ∃ a' c', a' < c' ∧ R.pushOff.IsReturningPath (R.pushOff.arc i) ζ U a' c' := by
  have hn := R.one_le
  have hS : X.IsSimpleStrandPath (X.arc i) := hU.isSimpleStrandPath
  have hR' : R.railPoints.IsAlong (X.arc i) ζ := hR
  obtain ⟨P', hP's, hP'len, hP'head, hP'last, hfilt, L₁, L₂, hsl, hsl'⟩ :=
    exists_isSimpleStrandPath_pushOff hX R hS hR'
  have hrot : ∀ d ∉ R.railPoints.darts, R.pushOff.rot d = X.rot d := fun d hd =>
    R.pushOff_rot_of_notMem hd
  have hDrot : ∀ d, X.rot d ∈ R.railPoints.darts ↔ d ∈ R.railPoints.darts :=
    R.railPoints.rot_mem_darts_iff
  have hDint : ∀ d ∈ R.railPoints.darts, ¬X.IsBoundaryVertex (X.vertexOf d) :=
    fun _ hd => rail_not_isBoundaryVertex_of_mem_darts R.railPoints hd
  have hsl'' : R.pushOff.sideList ζ P' = L₁ ++ R.pushOffBlock ++ L₂ := hsl'
  -- `P'` is the arc of `X'` from `s_i`
  have hS0 : 0 < (X.arc i).length := List.length_pos_iff.2 hS.isStrandPath.ne_nil
  have hShead : (X.arc i).head? = some (X.endDart (sourceIndex i)) := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hS0, X.getElem_arc]
    rfl
  have hSlast : (X.arc i).getLast? = some ((X.arc i)[(X.arc i).length - 1]'(by omega)) := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have hSend : X.RunsToEndpoint ((X.arc i)[(X.arc i).length - 1]'(by omega)) := by
    have hlen : X.arcLength i = ((X.arc i).length - 1) + 1 := by
      have := X.length_arc i
      omega
    have := (X.arcLength_eq_succ_iff.1 hlen).1
    rwa [X.getElem_arc]
  have hSendD : X.inv ((X.arc i)[(X.arc i).length - 1]'(by omega)) ∉ R.railPoints.darts :=
    fun h => hDint _ h hSend
  have hP'arc : P' = R.pushOff.arc i := by
    refine eq_arc_of_isStrandPath hP's.isStrandPath (hP'head.trans hShead) ?_
    intro e he
    rw [hP'last, hSlast, Option.mem_some_iff] at he
    subst he
    change R.pushOff.IsBoundaryVertex (R.pushOff.vertexOf (X.inv _))
    rw [vertexOf_eq_of_notMem hrot hDrot hSendD]
    exact hSend
  rw [← hP'arc]
  -- basic facts on `U`
  have hUs := hU.isStrandPath
  have hUg := X.isStrandPath_iff_getElem.1 hUs
  have hq : 0 < U.length := List.length_pos_iff.2 hUs.ne_nil
  have hUhead : U.head? = some U[0] := by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hq]
  have hUlast : U.getLast? = some U[U.length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have hint : ∀ t (ht : t + 1 < U.length), ∀ e ∈ X.arc i,
      X.vertexOf (X.inv U[t]) ≠ X.vertexOf e ∧ X.vertexOf (X.inv U[t]) ≠ X.vertexOf (X.inv e) :=
    fun t ht => hU.interiorPoints_ne _ (mem_interiorPoints' ht)
  have hUD := notMem_darts_of_isReturningPath hX R hR hU hfirst
    (fun g hg j h1 h2 => (hlast g hg).2.2 j h1 h2)
  have hinvD : ∀ t (ht : t + 1 < U.length), X.inv U[t] ∉ R.railPoints.darts := fun t ht =>
    hUD t ht _ (by rw [(hUg.2.2 t ht).vertexOf_eq]; exact X.self_mem_vertexOf _)
  -- `U` is a strand path of `X'`
  have hUs' : R.pushOff.IsStrandPath U := by
    refine R.pushOff.isStrandPath_iff_getElem.2
      ⟨hUs.ne_nil, fun t ht => hUg.2.1 t ht, fun t ht => ?_⟩
    have hs := hUg.2.2 t ht
    refine ⟨?_, ?_⟩
    · change ¬R.pushOff.IsBoundaryVertex (R.pushOff.vertexOf (X.inv U[t]))
      rw [vertexOf_eq_of_notMem hrot hDrot (hinvD t ht)]
      exact hs.1
    · change U[t + 1] = (R.pushOff.rot ^ 3) (X.inv U[t])
      rw [(rot_pow_apply_of_notMem hrot hDrot (hinvD t ht) 3).1]
      exact hs.2
  -- the positions of the ends of `U` in the two side lists
  obtain ⟨e₀, he₀, f₀, hf₀, hf₀s⟩ := hU.head?_mem
  have hla := hU.lt_left
  have hlc := hU.lt_right
  obtain rfl : e₀ = (X.arc i)[a] := Option.some_injective _ (he₀.symm.trans
    (List.getElem?_eq_getElem (by omega)))
  obtain rfl : f₀ = U[0] := Option.some_injective _ (hf₀.symm.trans hUhead)
  obtain ⟨e₁, he₁, g₀, hg₀, hg₀s⟩ := hU.getLast?_mem
  obtain rfl : e₁ = (X.arc i)[c] := Option.some_injective _ (he₁.symm.trans
    (List.getElem?_eq_getElem (by omega)))
  obtain rfl : g₀ = U[U.length - 1] := Option.some_injective _ (hg₀.symm.trans hUlast)
  have hF : R.railPoints.facingDarts.length = 2 * (n + 1) := R.railPoints.length_facingDarts
  have hB : R.pushOffBlock.length = 2 * n := length_pushOffBlock R
  have hF0 : R.railPoints.facingDarts[0]? = some (R.railPoints.dart (rho 0 1)) := by
    rw [RailPoints.getElem?_facingDarts' _ (by omega)]
  have hF3 : n = 1 → R.railPoints.facingDarts[3]? = some (R.railPoints.dart (rho 1 2)) := by
    rintro rfl
    rw [RailPoints.getElem?_facingDarts' _ (by omega)]
  have hFlast : R.railPoints.facingDarts[R.railPoints.facingDarts.length - 1]? =
      R.pushOffBlock[R.pushOffBlock.length - 1]? := by
    rw [getElem?_pushOffBlock_last, hF, RailPoints.getElem?_facingDarts' _ (by omega)]
    congr 3 <;> omega
  have hexcl : ∀ f, (f ≠ R.railPoints.dart (rho 0 2) ∧ f ≠ R.railPoints.dart (rho n 1) ∧
      ∀ j, 1 ≤ j → j ≤ n - 1 →
        f ≠ R.railPoints.dart (rho j 1) ∧ f ≠ R.railPoints.dart (rho j 2)) →
      ∀ t, (X.sideList ζ (X.arc i))[t]? = some f →
        t ≤ L₁.length ∨ L₁.length + 2 * n + 1 ≤ t := by
    rintro f ⟨h1, h2, h3⟩ t ht
    by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨s, rfl⟩ : ∃ s, t = L₁.length + s := ⟨t - L₁.length, by omega⟩
    rw [hsl, getElem?_append_mid (by omega) (by rw [hF]; omega), Nat.add_sub_cancel_left,
      RailPoints.getElem?_facingDarts' _ (by omega), Option.some_inj] at ht
    rcases (show s = 1 ∨ s = 2 * n ∨ (2 ≤ s ∧ s ≤ 2 * n - 1) by omega) with hs | hs | hs
    · subst hs
      exact h1 ht.symm
    · subst hs
      rw [show 2 * n / 2 = n by omega, show 2 * n % 2 + 1 = 1 by omega] at ht
      exact h2 ht.symm
    · rcases Nat.mod_two_eq_zero_or_one s with hm | hm <;> rw [hm] at ht
      · exact (h3 (s / 2) (by omega) (by omega)).1 ht.symm
      · exact (h3 (s / 2) (by omega) (by omega)).2 ht.symm
  obtain ⟨tU, htU, htU1, htU2⟩ := exists_getElem?_of_mem_sideDarts hla hf₀s
  obtain ⟨tV, htV, htV1, htV2⟩ := exists_getElem?_of_mem_sideDarts hlc hg₀s
  have htUa := hexcl _ (hfirst _ hUhead) tU htU
  have htVa := hexcl _ (hlast _ hUlast) tV htV
  have hshift : ∀ t f, (t ≤ L₁.length ∨ L₁.length + 2 * n + 1 ≤ t) →
      (X.sideList ζ (X.arc i))[t]? = some f →
      (R.pushOff.sideList ζ P')[if t ≤ L₁.length then t else t - 2]? = some f := by
    intro t f ht hf
    rw [hsl'', getElem?_append_shift (by rw [hF, hB]; ring) (by omega)
      (by rw [hF0, getElem?_pushOffBlock_zero]) hFlast (by rw [hF]; omega), ← hsl, hf]
  have hsU := hshift tU _ htUa htU
  have hsV := hshift tV _ htVa htV
  generalize htU'def : (if tU ≤ L₁.length then tU else tU - 2) = tU' at hsU
  generalize htV'def : (if tV ≤ L₁.length then tV else tV - 2) = tV' at hsV
  have htU' : (tU ≤ L₁.length ∧ tU' = tU) ∨ (L₁.length + 2 * n + 1 ≤ tU ∧ tU' = tU - 2) := by
    split_ifs at htU'def <;> omega
  have htV' : (tV ≤ L₁.length ∧ tV' = tV) ∨ (L₁.length + 2 * n + 1 ≤ tV ∧ tV' = tV - 2) := by
    split_ifs at htV'def <;> omega
  obtain ⟨a', ha', hU0', ha'1, ha'2⟩ := exists_mem_sideDarts_of_getElem? hsU
  obtain ⟨c', hc', hV', hc'1, hc'2⟩ := exists_mem_sideDarts_of_getElem? hsV
  have hcmp : a' ≤ c' ∧ (a' = c' → n = 1 ∧
      ((tU = L₁.length ∧ tV = L₁.length + 3) ∨ (tV = L₁.length ∧ tU = L₁.length + 3))) := by
    cases ζ with
    | right =>
      have := htU1 rfl
      have := htV1 rfl
      have := ha'1 rfl
      have := hc'1 rfl
      omega
    | left =>
      have := htU2 rfl
      have := htV2 rfl
      have := ha'2 rfl
      have := hc'2 rfl
      omega
  rcases Nat.lt_or_ge a' c' with hlt | hge
  · -- `U` is a parallel returning path of the new arc
    right
    refine ⟨a', c', hlt, hP's, hUs', ha', hc',
      ⟨P'[a'], List.getElem?_eq_getElem _, U[0], hUhead, hU0'⟩,
      ⟨P'[c'], List.getElem?_eq_getElem _, U[U.length - 1], hUlast, hV'⟩, ?_⟩
    intro z hz e he
    obtain ⟨t, ht, rfl⟩ := mem_interiorPoints_iff'.1 hz
    change R.pushOff.vertexOf (X.inv U[t]) ≠ _ ∧ R.pushOff.vertexOf (X.inv U[t]) ≠ _
    rw [vertexOf_eq_of_notMem hrot hDrot (hinvD t ht)]
    have hzD : ∀ d ∈ X.vertexOf (X.inv U[t]), d ∉ R.railPoints.darts := by
      rw [← (hUg.2.2 t ht).vertexOf_eq]
      exact hUD t ht
    have key : ∀ e' ∈ P', X.vertexOf (X.inv U[t]) ≠ R.pushOff.vertexOf e' := by
      intro e' he' h
      by_cases he'D : e' ∈ R.railPoints.darts
      · exact hzD e' (by rw [h]; exact R.pushOff.self_mem_vertexOf e') he'D
      · have he'S : e' ∈ X.arc i := by
          have : e' ∈ P'.filter (· ∉ R.railPoints.darts) :=
            List.mem_filter.2 ⟨he', by simpa using he'D⟩
          rw [hfilt] at this
          exact (List.mem_filter.1 this).1
        rw [vertexOf_eq_of_notMem hrot hDrot he'D] at h
        exact (hint t ht e' he'S).1 h
    refine ⟨key e he, fun h => ?_⟩
    rcases vertexOf_inv_mem_of_isStrandPath hP's.isStrandPath he with ⟨e', he', h'⟩ | h'
    · exact key e' he' (h.trans h')
    · have hend : R.pushOff.pathEnd P' =
          X.vertexOf (X.inv ((X.arc i)[(X.arc i).length - 1]'(by omega))) := by
        rw [R.pushOff.pathEnd_of_getLast? (hP'last.trans hSlast)]
        exact vertexOf_eq_of_notMem hrot hDrot hSendD
      exact (hint t ht _ (List.getElem_mem _)).2 (h.trans (h'.trans hend))
  · -- the two ends of `U` lie at one vertex of `X'`: a monogon
    left
    obtain ⟨hn1, hpos⟩ := hcmp.2 (by omega)
    subst hn1
    have hsl0 : (X.sideList ζ (X.arc i))[L₁.length]? = some (R.railPoints.dart (rho 0 1)) := by
      rw [hsl, getElem?_append_mid le_rfl (by rw [hF]; omega),
        show L₁.length - L₁.length = 0 from Nat.sub_self _, hF0]
    have hsl3 : (X.sideList ζ (X.arc i))[L₁.length + 3]? =
        some (R.railPoints.dart (rho 1 2)) := by
      rw [hsl, getElem?_append_mid (by omega) (by rw [hF]; omega), Nat.add_sub_cancel_left,
        hF3 rfl]
    have hends : (U[0] = R.railPoints.dart (rho 0 1) ∧
        X.inv U[U.length - 1] = R.railPoints.dart (rho 1 2)) ∨
        (U[0] = R.railPoints.dart (rho 1 2) ∧
          X.inv U[U.length - 1] = R.railPoints.dart (rho 0 1)) := by
      rcases hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at htU
        rw [h2] at htV
        exact Or.inl ⟨Option.some_injective _ (htU.symm.trans hsl0),
          Option.some_injective _ (htV.symm.trans hsl3)⟩
      · rw [h1] at htV
        rw [h2] at htU
        exact Or.inr ⟨Option.some_injective _ (htU.symm.trans hsl3),
          Option.some_injective _ (htV.symm.trans hsl0)⟩
    exact hasMonogon_pushOff_one hX R hUs' hq hUhead hUlast hends

end ClosedAlignedRail

/-! ### A parallel digon yields a parallel returning path -/

/-- The forward orbit of `e` under the strand map consists of `out` darts at triple points: `e`
lies on a closed strand of `out` darts. -/
private def OnClosedStrand (X : TripleData H b) (e : H) : Prop :=
  ∀ e' ∈ X.strandOrbit e, ¬X.IsBoundaryVertex (X.vertexOf e') ∧ X.isOut e' = true

private theorem strandOrbit_subset {X : TripleData H b} {e e' : H} (h : e' ∈ X.strandOrbit e) :
    X.strandOrbit e' ⊆ X.strandOrbit e := by
  intro d hd
  obtain ⟨k, rfl⟩ := X.mem_strandOrbit.1 h
  obtain ⟨m, rfl⟩ := X.mem_strandOrbit.1 hd
  exact X.mem_strandOrbit.2 ⟨m + k, by rw [Function.iterate_add_apply]⟩

private theorem OnClosedStrand.of_mem {X : TripleData H b} {e e' : H} (he : X.OnClosedStrand e)
    (h : e' ∈ X.strandOrbit e) : X.OnClosedStrand e' := fun d hd => he d (strandOrbit_subset h hd)

private theorem self_mem_strandOrbit (X : TripleData H b) (e : H) : e ∈ X.strandOrbit e :=
  X.mem_strandOrbit.2 ⟨0, rfl⟩

private theorem strandMap_mem_strandOrbit (X : TripleData H b) (e : H) :
    X.strandMap e ∈ X.strandOrbit e :=
  X.mem_strandOrbit.2 ⟨1, rfl⟩

/-- A dart of an arc does not lie on a closed strand. -/
private theorem not_onClosedStrand_of_mem_arc {X : TripleData H b} {j : Fin b} {e : H}
    (he : e ∈ X.arc j) : ¬X.OnClosedStrand e := by
  intro hC
  obtain ⟨k, hk, rfl⟩ := mem_arc_toFinset.1 (List.mem_toFinset.2 he)
  obtain ⟨m, hm⟩ : ∃ m, X.arcLength j = m + 1 := ⟨X.arcLength j - 1, by omega⟩
  have hend := (X.arcLength_eq_succ_iff.1 hm).1
  have hmem : X.strandMap (X.arcDart j m) ∈ X.strandOrbit (X.arcDart j k) := by
    refine X.mem_strandOrbit.2 ⟨m - k + 1, ?_⟩
    rw [Function.iterate_succ_apply', arcDart, arcDart, ← Function.iterate_add_apply,
      show m - k + k = m by omega]
  have := (hC _ hmem).1
  rw [X.strandMap_of_runsToEndpoint hend] at this
  exact this hend

/-- The two strand paths of a parallel digon may be exchanged. -/
private theorem IsParallelDigon.symm {X : TripleData H b} {P Q : List H} {x y : Finset H}
    (h : X.IsParallelDigon P Q x y) : X.IsParallelDigon Q P x y :=
  ⟨h.ne, h.mem_left, h.mem_right, h.isStrandPath_snd, h.isStrandPath_fst, h.pathStart_snd,
    h.pathEnd_snd, h.pathStart_fst, h.pathEnd_fst, h.head?_ne.symm, h.getLast?_ne.symm⟩

/-- **Reduction to a digon along an arc.** A triple diagram without monogons that has a parallel
digon has a parallel digon whose first strand path starts with a dart of an arc. -/
private theorem exists_isParallelDigon_head_mem_arc {X : TripleData H b} (hX : X.IsTripleDiagram)
    (hmono : ¬X.HasMonogon) (hdig : X.HasParallelDigon) :
    ∃ P Q x y, X.IsParallelDigon P Q x y ∧ ∃ j, ∃ p ∈ P.head?, p ∈ X.arc j := by
  have hpre := hX.toIsPreTripleDiagram
  obtain ⟨P₀, Q₀, x₀, y₀, hd⟩ := hdig
  have hP0 : 0 < P₀.length := List.length_pos_iff.2 hd.isStrandPath_fst.ne_nil
  have hhead : P₀.head? = some P₀[0] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hP0]
  have hpB : P₀[0] ∉ X.bdry := hd.isStrandPath_fst.notMem_bdry _ (List.getElem_mem hP0)
  have hpO : X.isOut P₀[0] = true := hd.isStrandPath_fst.isOut_eq_true _ (List.getElem_mem hP0)
  rcases X.mem_arc_or_forall_strandOrbit hpre hpB hpO with ⟨j, hj⟩ | hpC
  · exact ⟨P₀, Q₀, x₀, y₀, hd, j, P₀[0], hhead, hj⟩
  by_contra hcon
  have hnotB : ∀ e, ¬X.IsBoundaryVertex (X.vertexOf e) → e ∉ X.bdry := fun e he heB =>
    he ⟨e, X.self_mem_vertexOf e, heB⟩
  -- every triple point carrying an `out` dart on a closed strand is closed
  have hall : ∀ e, ¬X.IsBoundaryVertex (X.vertexOf e) → X.OnClosedStrand e →
      ∀ e' ∈ X.vertexOf e, X.isOut e' = true → X.OnClosedStrand e' := by
    intro e he heC e' he' he'o
    by_contra he'C
    have hve : X.vertexOf e' = X.vertexOf e := X.vertexOf_eq_of_mem he'
    have he'B : e' ∉ X.bdry := hnotB e' (by rwa [hve])
    rcases X.mem_arc_or_forall_strandOrbit hpre he'B he'o with ⟨j, hj⟩ | h
    · have hC : X.IsClosedStrand (X.strandOrbit e) :=
        ⟨e, hnotB e he, rfl, fun d hd => (heC d hd).1⟩
      have hgC : e' ∉ X.strandOrbit e := fun h' => he'C (heC.of_mem h')
      have hpass : X.PassesThrough (X.strandOrbit e) (X.vertexOf e') := by
        refine ⟨by rw [hve]; exact X.vertexOf_mem_internalVertices.2 he, e,
          self_mem_strandOrbit X e, hve.symm⟩
      obtain ⟨P, Q, x, y, hPQ, -, hQT⟩ := exists_isParallelDigon_of_isClosedStrand hX hmono hC
        (fun d hd => (heC d hd).2) (T := (X.arc j).toFinset) (Or.inl ⟨j, rfl⟩)
        (List.mem_toFinset.2 hj) hgC hpass
      have hQ0 : 0 < Q.length := List.length_pos_iff.2 hPQ.isStrandPath_snd.ne_nil
      exact hcon ⟨Q, P, x, y, hPQ.symm, j, Q[0],
        by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hQ0]; rfl,
        List.mem_toFinset.1 (hQT _ (List.getElem_mem hQ0))⟩
    · exact he'C h
  -- the darts at closed triple points form a nonempty set closed under `σ` and the involution
  let Kp : H → Prop := fun d => ¬X.IsBoundaryVertex (X.vertexOf d) ∧
    ∀ e' ∈ X.vertexOf d, X.isOut e' = true → X.OnClosedStrand e'
  have hKrot : ∀ d, Kp d → Kp (X.rot d) := fun d hd => by
    simpa only [Kp, X.vertexOf_rot] using hd
  have hKinv : ∀ d, Kp d → Kp (X.inv d) := by
    intro d ⟨hdb, hdC⟩
    have hdB : d ∉ X.bdry := hnotB d hdb
    by_cases hdo : X.isOut d = true
    · have hC := hdC d (X.self_mem_vertexOf d) hdo
      have hr : ¬X.RunsToEndpoint d := fun hr => by
        have := (hC _ (strandMap_mem_strandOrbit X d)).1
        rw [X.strandMap_of_runsToEndpoint hr] at this
        exact this hr
      have hC' : X.OnClosedStrand (X.strandMap d) := hC.of_mem (strandMap_mem_strandOrbit X d)
      have hv : X.vertexOf (X.strandMap d) = X.vertexOf (X.inv d) := by
        rw [X.strandMap_of_not_runsToEndpoint hr]
        exact X.vertexOf_rot_pow_apply 3 _
      have hb : ¬X.IsBoundaryVertex (X.vertexOf (X.strandMap d)) :=
        (hC' _ (self_mem_strandOrbit X _)).1
      refine ⟨by rwa [← hv], fun e' he' he'o => ?_⟩
      rw [← hv] at he'
      exact hall _ hb hC' e' he' he'o
    · have hdo' : X.isOut d = false := by simpa using hdo
      have hinvo : X.isOut (X.inv d) = true := by rw [hpre.isOut_inv_apply hdB, hdo']; rfl
      have h3o : X.isOut ((X.rot ^ 3) d) = true := by
        rw [hpre.isOut_rot_pow_three_apply hdb, hdo']; rfl
      have h3C := hdC _ (X.rot_pow_apply_mem_vertexOf 3 d) h3o
      have hr : ¬X.RunsToEndpoint (X.inv d) := by
        change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.inv d)))
        rwa [hpre.inv_inv_apply]
      have hS : X.strandMap (X.inv d) = (X.rot ^ 3) d := by
        rw [X.strandMap_of_not_runsToEndpoint hr, hpre.inv_inv_apply]
        rfl
      have hinvC : X.OnClosedStrand (X.inv d) := by
        rcases X.mem_arc_or_forall_strandOrbit hpre (hpre.inv_notMem_bdry hdB) hinvo with
          ⟨j, hj⟩ | h
        · exfalso
          obtain ⟨k, hk, hkd⟩ := mem_arc_toFinset.1 (List.mem_toFinset.2 hj)
          have hk1 : k + 1 < X.arcLength j := by
            by_contra hk1
            obtain ⟨m, hm⟩ : ∃ m, X.arcLength j = m + 1 := ⟨X.arcLength j - 1, by omega⟩
            have := (X.arcLength_eq_succ_iff.1 hm).1
            rw [show m = k by omega, hkd] at this
            exact hr this
          have hmem : (X.rot ^ 3) d ∈ X.arc j := by
            rw [← hS, ← hkd, ← arcDart_succ]
            exact List.mem_toFinset.1 (mem_arc_toFinset.2 ⟨k + 1, hk1, rfl⟩)
          exact not_onClosedStrand_of_mem_arc hmem h3C
        · exact h
      have hb : ¬X.IsBoundaryVertex (X.vertexOf (X.inv d)) :=
        (hinvC _ (self_mem_strandOrbit X _)).1
      exact ⟨hb, fun e' he' he'o => hall _ hb hinvC e' he' he'o⟩
  have hK0 : Kp P₀[0] := by
    have hb : ¬X.IsBoundaryVertex (X.vertexOf P₀[0]) := by
      have h1 := hd.pathStart_fst
      have h2 := hd.mem_left
      rw [X.pathStart_of_head? hhead] at h1
      rw [← h1] at h2
      exact X.vertexOf_mem_internalVertices.1 h2
    exact ⟨hb, fun e' he' he'o => hall _ hb hpC e' he' he'o⟩
  have hreach : ∀ e, X.Reach P₀[0] e → Kp e := by
    intro e he
    induction he with
    | refl => exact hK0
    | rot _ ih => exact hKrot _ ih
    | inv _ ih => exact hKinv _ ih
  obtain ⟨f, hf, hfB, -⟩ := hX.exists_orbit
  obtain ⟨d, rfl⟩ := X.mem_faceOrbits.1 hf
  have hdB : d ∈ X.bdry := hfB (X.self_mem_faceOf d)
  exact (hreach d (hX.toIsDiskMap.toIsConnected.reach _ d)).1 ⟨d, X.self_mem_vertexOf d, hdB⟩

/-- All the darts of a triple point avoided by a simple arc lie on the side of one of them. -/
private theorem mem_arcSide_of_mem_vertexOf' {X : TripleData H b} (hX : X.IsTripleDiagram)
    {i : Fin b} (hS : X.IsSimpleArc i) {v : ℤ} {x e : H}
    (hx : X.vertexOf x ∈ X.internalVertices)
    (hpass : ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf x)) (hxv : x ∈ X.arcSide i v)
    (he : e ∈ X.vertexOf x) : e ∈ X.arcSide i v := by
  have hxx := X.self_mem_vertexOf x
  rcases hS.forall_mem_rightSide_or_forall_mem_leftSide hX hx hpass with h | h
  · have := (mem_arcSide.1 hxv).2.2.symm.trans (mem_arcSide.1 (h x hxx)).2.2
    rw [this]
    exact h e he
  · have := (mem_arcSide.1 hxv).2.2.symm.trans (mem_arcSide.1 (h x hxx)).2.2
    rw [this]
    exact h e he

/-- A strand path whose interior points are not points of a simple arc stays on one side of it. -/
private theorem forall_mem_arcSide_of_isStrandPath {X : TripleData H b} (hX : X.IsTripleDiagram)
    {i : Fin b} (hS : X.IsSimpleArc i) {v : ℤ} {R : List H} (hR : X.IsStrandPath R)
    (hpass : ∀ j (hj : j + 1 < R.length),
      ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf (X.inv R[j])))
    (h0 : ∀ r ∈ R.head?, r ∈ X.arcSide i v) : ∀ j (hj : j < R.length), R[j] ∈ X.arcSide i v := by
  have hRg := X.isStrandPath_iff_getElem.1 hR
  intro j hj
  induction j with
  | zero => exact h0 _ (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hj]; rfl)
  | succ j ih =>
    have hinv := hS.inv_mem_arcSide hX (ih (by omega))
    have hs := hRg.2.2 j hj
    have hmem : R[j + 1] ∈ X.vertexOf (X.inv R[j]) := by
      rw [← hs.vertexOf_eq]
      exact X.self_mem_vertexOf _
    exact mem_arcSide_of_mem_vertexOf' hX hS (X.vertexOf_mem_internalVertices.2 hs.1)
      (hpass j hj) hinv hmem

/-- A strand path whose interior points are not points of a simple arc stays on one side of it. -/
private theorem inv_getLast_mem_arcSide {X : TripleData H b} (hX : X.IsTripleDiagram) {i : Fin b}
    (hS : X.IsSimpleArc i) {v : ℤ} {R : List H} (hR : X.IsStrandPath R)
    (hpass : ∀ j (hj : j + 1 < R.length),
      ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf (X.inv R[j])))
    (h0 : ∀ r ∈ R.head?, r ∈ X.arcSide i v) : ∀ g ∈ R.getLast?, X.inv g ∈ X.arcSide i v := by
  have hR0 : 0 < R.length := List.length_pos_iff.2 hR.ne_nil
  intro g hg
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), Option.mem_some_iff] at hg
  subst hg
  exact hS.inv_mem_arcSide hX
    (forall_mem_arcSide_of_isStrandPath hX hS hR hpass h0 _ (by omega))

/-- The darts at a triple point `z_{l+1}` of a simple arc: `σᵏ(ē_{l+1})`. -/
private theorem exists_rot_pow_of_mem_arc {X : TripleData H b} (hX : X.IsTripleDiagram)
    {i : Fin b} {l : ℕ} (hl : l + 1 < (X.arc i).length) {d : H}
    (hd : d ∈ X.vertexOf (X.inv (X.arc i)[l])) :
    ∃ k < 6, d = (X.rot ^ k) (X.inv (X.arcDart i l)) := by
  have hSg := (X.isStrandPath_iff_getElem.1 (X.isStrandPath_arc hX.toIsPreTripleDiagram
    (by rw [← X.length_arc]; omega))).2.2 l hl
  rw [X.getElem_arc] at hd hSg
  obtain ⟨k, hk, hk'⟩ := X.exists_pow_apply_eq_of_card_vertexOf
    (hX.internalVertex_card _ (X.vertexOf_mem_internalVertices.2 hSg.1)) hd
  exact ⟨k, hk, hk'.symm⟩

/-- A dart at a triple point `z_{l+1}` of a simple arc lying on a side of it is a side dart of
that side. -/
private theorem mem_sideDarts_of_mem_arcSide {X : TripleData H b} (hX : X.IsTripleDiagram)
    {i : Fin b} (hS : X.IsSimpleArc i) {l : ℕ} (hl : l + 1 < (X.arc i).length) {d : H}
    (hd : d ∈ X.vertexOf (X.inv (X.arc i)[l])) {v : ℤ} (hdv : d ∈ X.arcSide i v) :
    (v = -1 ∧ d ∈ X.sideDarts .right (X.arc i)[l]) ∨
      (v = 0 ∧ d ∈ X.sideDarts .left (X.arc i)[l]) := by
  have hl' : l + 1 < X.arcLength i := by rwa [← X.length_arc]
  obtain ⟨k, hk, rfl⟩ := exists_rot_pow_of_mem_arc hX hl hd
  have hA : ∀ e ∈ X.arcDarts i, e ∉ X.arcSide i v := fun e he hv =>
    disjoint_left.1 (disjoint_arcDarts_arcSide v) he hv
  have hval : ∀ w, (X.rot ^ k) (X.inv (X.arcDart i l)) ∈ X.arcSide i w → v = w := fun w hw =>
    (mem_arcSide.1 hdv).2.2.symm.trans (mem_arcSide.1 hw).2.2
  have hR := hS.rot_pow_inv_arcDart_mem_rightSide hX hl'
  have hL := hS.rot_pow_inv_arcDart_mem_leftSide hX hl'
  rw [X.getElem_arc]
  interval_cases k
  · exact absurd hdv (hA _ (inv_arcDart_mem_arcDarts (by omega)))
  · rw [pow_one] at hdv ⊢
    exact Or.inl ⟨hval _ (by rw [pow_one]; exact hR.1), by simp [sideDarts]⟩
  · exact Or.inl ⟨hval _ hR.2, by simp [sideDarts]⟩
  · rw [← arcDart_succ_eq hX hl'] at hdv
    exact absurd hdv (hA _ (arcDart_mem_arcDarts (by omega)))
  · exact Or.inr ⟨hval _ hL.1, by simp [sideDarts]⟩
  · exact Or.inr ⟨hval _ hL.2, by simp [sideDarts]⟩

/-- An `out` dart at a triple point `z_{l+1}` of a simple arc that is not a dart of the arc lies on
one of its sides. -/
private theorem mem_arcSide_of_isOut {X : TripleData H b} (hX : X.IsTripleDiagram) {i : Fin b}
    (hS : X.IsSimpleArc i) {l : ℕ} (hl : l + 1 < (X.arc i).length) {d : H}
    (hd : d ∈ X.vertexOf (X.inv (X.arc i)[l])) (hdo : X.isOut d = true) (hdS : d ∉ X.arc i) :
    d ∈ X.rightSide i ∨ d ∈ X.leftSide i := by
  have hpre := hX.toIsPreTripleDiagram
  have hl' : l + 1 < X.arcLength i := by rwa [← X.length_arc]
  obtain ⟨k, hk, rfl⟩ := exists_rot_pow_of_mem_arc hX hl hd
  have hR := hS.rot_pow_inv_arcDart_mem_rightSide hX hl'
  have hL := hS.rot_pow_inv_arcDart_mem_leftSide hX hl'
  interval_cases k
  · exfalso
    have hP := X.isStrandPath_arc hpre (i := i) (by omega)
    have hm : X.arcDart i l ∈ X.arc i := by
      rw [← X.getElem_arc i l (by rw [X.length_arc]; omega)]
      exact List.getElem_mem _
    rw [pow_zero, Equiv.Perm.one_apply, hpre.isOut_inv_apply (hP.notMem_bdry _ hm),
      hP.isOut_eq_true _ hm] at hdo
    exact Bool.false_ne_true hdo
  · exact Or.inl (by rw [pow_one]; exact hR.1)
  · exact Or.inl hR.2
  · exfalso
    rw [← arcDart_succ_eq hX hl'] at hdS
    apply hdS
    rw [← X.getElem_arc i (l + 1) (by rw [X.length_arc]; omega)]
    exact List.getElem_mem _
  · exact Or.inr hL.1
  · exact Or.inr hL.2

/-- A strand path `Q` avoiding the darts of a simple arc `S`, from the triple point `z_{lx+1}` of
`S` to its triple point `z_{ly+1}` with `lx < ly`, contains a parallel returning path of `S`: the
part of `Q` between two of its consecutive points on `S` whose index increases. -/
private theorem exists_isReturningPath_of_isStrandPath {X : TripleData H b}
    (hX : X.IsTripleDiagram) {i : Fin b} (hS : X.IsSimpleArc i) {Q : List H}
    (hQ : X.IsStrandPath Q) (hQS : ∀ q ∈ Q, q ∉ X.arc i) {lx ly : ℕ}
    (hlx : lx + 1 < (X.arc i).length) (hly : ly + 1 < (X.arc i).length) (hlxy : lx < ly)
    (hx : X.pathStart Q = X.vertexOf (X.inv (X.arc i)[lx]))
    (hy : X.pathEnd Q = X.vertexOf (X.inv (X.arc i)[ly])) :
    ∃ ζ Q' a c, a < c ∧ X.IsReturningPath (X.arc i) ζ Q' a c := by
  classical
  have hSs : X.IsSimpleStrandPath (X.arc i) := hS.isSimpleStrandPath hX
  have hSg := (X.isStrandPath_iff_getElem.1 hSs.isStrandPath).2.2
  have hQg := X.isStrandPath_iff_getElem.1 hQ
  have hq : 0 < Q.length := List.length_pos_iff.2 hQ.ne_nil
  have hQhead : Q.head? = some Q[0] := by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hq]
  have hQlast : Q.getLast? = some Q[Q.length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  -- the vertices of the darts of `S` and of their reverses
  have hS0B : X.IsBoundaryVertex (X.vertexOf (X.arc i)[0]) := by
    rw [X.getElem_arc]
    exact (X.mem_boundaryVertices.1 (hX.endpoint_mem _)).2
  have hSlastB : X.IsBoundaryVertex (X.vertexOf (X.inv (X.arc i)[(X.arc i).length - 1])) := by
    have hlen : X.arcLength i = ((X.arc i).length - 1) + 1 := by
      have := X.length_arc i
      omega
    have := (X.arcLength_eq_succ_iff.1 hlen).1
    rwa [X.getElem_arc]
  have hvS : ∀ k (hk : k < (X.arc i).length), X.IsBoundaryVertex (X.vertexOf (X.arc i)[k]) ∨
      ∃ l, ∃ hl : l + 1 < (X.arc i).length,
        X.vertexOf (X.arc i)[k] = X.vertexOf (X.inv (X.arc i)[l]) := by
    intro k hk
    rcases k with _ | k
    · exact Or.inl hS0B
    · exact Or.inr ⟨k, hk, (hSg k hk).vertexOf_eq⟩
  have hvSinv : ∀ k (hk : k < (X.arc i).length),
      X.IsBoundaryVertex (X.vertexOf (X.inv (X.arc i)[k])) ∨
      ∃ l, ∃ hl : l + 1 < (X.arc i).length,
        X.vertexOf (X.inv (X.arc i)[k]) = X.vertexOf (X.inv (X.arc i)[l]) := by
    intro k hk
    by_cases hk' : k + 1 < (X.arc i).length
    · exact Or.inr ⟨k, hk', rfl⟩
    · left
      have e : (X.arc i)[k] = (X.arc i)[(X.arc i).length - 1] := by
        congr 1
        omega
      rw [e]
      exact hSlastB
  have hSinj : ∀ {l l'} (hl : l + 1 < (X.arc i).length) (hl' : l' + 1 < (X.arc i).length),
      X.vertexOf (X.inv (X.arc i)[l]) = X.vertexOf (X.inv (X.arc i)[l']) → l = l' :=
    fun hl hl' h => eq_of_vertexOf_inv_eq' hSs hl hl' h
  -- the vertices of `Q`
  obtain ⟨V, hVdef⟩ : ∃ V : ℕ → Finset H, ∀ s,
      V s = if h : s < Q.length then X.vertexOf Q[s] else X.pathEnd Q := ⟨_, fun _ => rfl⟩
  have hV : ∀ s (hs : s < Q.length), V (s + 1) = X.vertexOf (X.inv Q[s]) := by
    intro s hs
    rw [hVdef]
    split_ifs with h
    · exact (hQg.2.2 s h).vertexOf_eq
    · rw [X.pathEnd_of_getLast? hQlast]
      congr 3
      omega
  have hV0 : V 0 = X.vertexOf (X.inv (X.arc i)[lx]) := by
    rw [hVdef, dif_pos hq, ← hx, X.pathStart_of_head? hQhead]
  have hVend : V Q.length = X.vertexOf (X.inv (X.arc i)[ly]) := by
    rw [hVdef, dif_neg (lt_irrefl _), hy]
  have hVint : ∀ s, 1 ≤ s → s ≤ Q.length → ¬X.IsBoundaryVertex (V s) := by
    intro s hs1 hs2
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [hV s (by omega)]
    by_cases h : s + 1 < Q.length
    · exact (hQg.2.2 s h).1
    · have hend : X.pathEnd Q = X.vertexOf (X.inv Q[s]) :=
        X.pathEnd_of_getLast? (by
          rw [List.getLast?_eq_getElem?, show Q.length - 1 = s by omega,
            List.getElem?_eq_getElem])
      have : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.arc i)[ly])) := (hSg ly hly).1
      rw [← hy, hend] at this
      exact this
  -- the first point after the start with a larger index, and the last point on `S` before it
  have hex : ∃ s, s ≤ Q.length ∧ ∃ l, ∃ hl : l + 1 < (X.arc i).length,
      V s = X.vertexOf (X.inv (X.arc i)[l]) ∧ lx < l := ⟨Q.length, le_rfl, ly, hly, hVend, hlxy⟩
  obtain ⟨t₂, ⟨ht₂n, l₂, hl₂, hVt₂, hlx₂⟩, hmin⟩ : ∃ t₂, (t₂ ≤ Q.length ∧ ∃ l,
      ∃ hl : l + 1 < (X.arc i).length, V t₂ = X.vertexOf (X.inv (X.arc i)[l]) ∧ lx < l) ∧
      ∀ s < t₂, ¬(s ≤ Q.length ∧ ∃ l, ∃ hl : l + 1 < (X.arc i).length,
        V s = X.vertexOf (X.inv (X.arc i)[l]) ∧ lx < l) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩
  have ht₂0 : 0 < t₂ := by
    rcases Nat.eq_zero_or_pos t₂ with h0 | h0
    · rw [h0, hV0] at hVt₂
      have := hSinj hlx hl₂ hVt₂
      omega
    · exact h0
  obtain ⟨t₁, ⟨l₁, hl₁, hVt₁⟩, ht₁le, hgap⟩ : ∃ t₁, (∃ l, ∃ hl : l + 1 < (X.arc i).length,
      V t₁ = X.vertexOf (X.inv (X.arc i)[l])) ∧ t₁ ≤ t₂ - 1 ∧
      ∀ s, t₁ < s → s ≤ t₂ - 1 → ¬∃ l, ∃ hl : l + 1 < (X.arc i).length,
        V s = X.vertexOf (X.inv (X.arc i)[l]) :=
    ⟨Nat.findGreatest (fun s => ∃ l, ∃ hl : l + 1 < (X.arc i).length,
        V s = X.vertexOf (X.inv (X.arc i)[l])) (t₂ - 1),
      Nat.findGreatest_spec (P := fun s => ∃ l, ∃ hl : l + 1 < (X.arc i).length,
        V s = X.vertexOf (X.inv (X.arc i)[l])) (m := 0) (Nat.zero_le _) ⟨lx, hlx, hV0⟩,
      Nat.findGreatest_le _, fun s h1 h2 => Nat.findGreatest_is_greatest h1 h2⟩
  have hl₁x : l₁ ≤ lx := by
    by_contra h
    exact hmin t₁ (by omega) ⟨by omega, l₁, hl₁, hVt₁, by omega⟩
  -- the part of `Q` between them
  obtain ⟨Q', hQ'len, hQ'get⟩ : ∃ Q' : List H, ∃ _ : Q'.length = t₂ - t₁,
      ∀ j (hj : j < Q'.length), Q'[j] = Q[t₁ + j]'(by omega) :=
    ⟨(Q.drop t₁).take (t₂ - t₁), by simp; omega, fun j hj => by simp⟩
  have hQ's : X.IsStrandPath Q' := by
    refine X.isStrandPath_iff_getElem.2 ⟨List.ne_nil_of_length_pos (by omega), fun j hj => ?_,
      fun j hj => ?_⟩
    · rw [hQ'get]
      exact hQg.2.1 _ _
    · rw [hQ'get, hQ'get]
      exact hQg.2.2 (t₁ + j) (by omega)
  have hQ'inv : ∀ j (hj : j + 1 < Q'.length), X.vertexOf (X.inv Q'[j]) = V (t₁ + j + 1) := by
    intro j hj
    rw [hQ'get, hV (t₁ + j) (by omega)]
  have hnotS : ∀ j (hj : j + 1 < Q'.length), ∀ e ∈ X.arc i,
      X.vertexOf (X.inv Q'[j]) ≠ X.vertexOf e ∧
        X.vertexOf (X.inv Q'[j]) ≠ X.vertexOf (X.inv e) := by
    intro j hj e he
    rw [hQ'inv j hj]
    have hint := hVint (t₁ + j + 1) (by omega) (by omega)
    have hno := hgap (t₁ + j + 1) (by omega) (by omega)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hvS k hk with hb | ⟨l, hl, hv⟩
      · exact hint (h ▸ hb)
      · exact hno ⟨l, hl, h.trans hv⟩
    · rcases hvSinv k hk with hb | ⟨l, hl, hv⟩
      · exact hint (h ▸ hb)
      · exact hno ⟨l, hl, h.trans hv⟩
  have hpass : ∀ j (hj : j + 1 < Q'.length),
      ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf (X.inv Q'[j])) := by
    rintro j hj ⟨-, d, hd, hdv⟩
    exact (hnotS j hj d (List.mem_toFinset.1 hd)).1 hdv.symm
  -- the sides of the ends
  have hQ'0 : Q'[0]'(by omega) = Q[t₁]'(by omega) := by rw [hQ'get]; simp
  have hQ'head : Q'.head? = some (Q[t₁]'(by omega)) := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega), hQ'0]
  have hQ'last : Q'.getLast? = some (Q[t₂ - 1]'(by omega)) := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), hQ'get]
    congr 2
    omega
  have hfirstv : Q[t₁]'(by omega) ∈ X.vertexOf (X.inv (X.arc i)[l₁]) := by
    have : V t₁ = X.vertexOf (Q[t₁]'(by omega)) := by rw [hVdef, dif_pos (by omega)]
    rw [← hVt₁, this]
    exact X.self_mem_vertexOf _
  have hlastv : X.inv (Q[t₂ - 1]'(by omega)) ∈ X.vertexOf (X.inv (X.arc i)[l₂]) := by
    have : V t₂ = X.vertexOf (X.inv (Q[t₂ - 1]'(by omega))) := by
      rw [← hV (t₂ - 1) (by omega)]
      congr 1
      omega
    rw [← hVt₂, this]
    exact X.self_mem_vertexOf _
  have hfirstS : Q[t₁]'(by omega) ∉ X.arc i := hQS _ (List.getElem_mem _)
  have hfirsto : X.isOut (Q[t₁]'(by omega)) = true := (hQg.2.1 t₁ (by omega)).2
  have key : ∀ v : ℤ, Q[t₁]'(by omega) ∈ X.arcSide i v →
      X.inv (Q[t₂ - 1]'(by omega)) ∈ X.arcSide i v :=
    fun v hv => inv_getLast_mem_arcSide hX hS hQ's hpass
      (fun r hr => by rw [hQ'head, Option.mem_some_iff] at hr; rw [← hr]; exact hv) _ hQ'last
  have hret : ∀ ζ, Q[t₁]'(by omega) ∈ X.sideDarts ζ (X.arc i)[l₁] →
      X.inv (Q[t₂ - 1]'(by omega)) ∈ X.sideDarts ζ (X.arc i)[l₂] →
      X.IsReturningPath (X.arc i) ζ Q' l₁ l₂ := fun ζ h1 h2 =>
    ⟨hSs, hQ's, hl₁, hl₂, ⟨_, List.getElem?_eq_getElem _, _, hQ'head, h1⟩,
      ⟨_, List.getElem?_eq_getElem _, _, hQ'last, h2⟩, fun z hz e he => by
        obtain ⟨j, hj, rfl⟩ := mem_interiorPoints_iff'.1 hz
        exact hnotS j hj e he⟩
  rcases mem_arcSide_of_isOut hX hS hl₁ hfirstv hfirsto hfirstS with h | h
  · have h1 := mem_sideDarts_of_mem_arcSide hX hS hl₁ hfirstv h
    have h2 := mem_sideDarts_of_mem_arcSide hX hS hl₂ hlastv (key _ h)
    refine ⟨.right, Q', l₁, l₂, by omega, hret _ ?_ ?_⟩
    · rcases h1 with ⟨-, h1⟩ | ⟨h1, -⟩
      · exact h1
      · norm_num at h1
    · rcases h2 with ⟨-, h2⟩ | ⟨h2, -⟩
      · exact h2
      · norm_num at h2
  · have h1 := mem_sideDarts_of_mem_arcSide hX hS hl₁ hfirstv h
    have h2 := mem_sideDarts_of_mem_arcSide hX hS hl₂ hlastv (key _ h)
    refine ⟨.left, Q', l₁, l₂, by omega, hret _ ?_ ?_⟩
    · rcases h1 with ⟨h1, -⟩ | ⟨-, h1⟩
      · norm_num at h1
      · exact h1
    · rcases h2 with ⟨h2, -⟩ | ⟨-, h2⟩
      · norm_num at h2
      · exact h2

/-- **A parallel digon yields a parallel returning path**. Let `X` be a triple diagram without
monogons that has a parallel digon. Then `X` has a simple arc `S`, from `s_i` say, and a side `ζ`
with `N_ζ ≥ 2` such that `S` has a parallel returning path on side `ζ`. -/
@[cluster_algebras "lem_parallel_digon_returning"]
theorem exists_isReturningPath_of_hasParallelDigon {X : TripleData H b} (hX : X.IsTripleDiagram)
    (hmono : ¬X.HasMonogon) (hdig : X.HasParallelDigon) :
    ∃ (i : Fin b) (ζ : StrandSide), X.IsSimpleArc i ∧ 2 ≤ (X.arcCutList i ζ).length ∧
      ∃ Q a c, a < c ∧ X.IsReturningPath (X.arc i) ζ Q a c := by
  have hpre := hX.toIsPreTripleDiagram
  obtain ⟨P, Q, x, y, hd, i, p, hp, hpS⟩ := exists_isParallelDigon_head_mem_arc hX hmono hdig
  -- the arc `S` from `s_i` is simple
  have hnd := X.nodup_interiorPoints_arc hpre hmono i
  have hS : X.IsSimpleArc i := by
    intro k l hk hl h
    rw [← X.length_arc] at hk hl
    rw [← X.getElem_arc i k (by omega), ← X.getElem_arc i l (by omega)] at h
    exact eq_of_vertexOf_inv_eq_of_nodup hnd hk hl h
  have hSs : X.IsSimpleStrandPath (X.arc i) := hS.isSimpleStrandPath hX
  have hSg := (X.isStrandPath_iff_getElem.1 hSs.isStrandPath).2.2
  have hSinj : ∀ {l l'} (hl : l + 1 < (X.arc i).length) (hl' : l' + 1 < (X.arc i).length),
      X.vertexOf (X.inv (X.arc i)[l]) = X.vertexOf (X.inv (X.arc i)[l']) → l = l' :=
    fun hl hl' h => eq_of_vertexOf_inv_eq' hSs hl hl' h
  have hSlen : 0 < (X.arc i).length := List.length_pos_iff.2 hSs.isStrandPath.ne_nil
  have hS0B : X.IsBoundaryVertex (X.vertexOf (X.arc i)[0]) := by
    rw [X.getElem_arc]
    exact (X.mem_boundaryVertices.1 (hX.endpoint_mem _)).2
  have hSlast : ∀ k (hk : k < (X.arc i).length), ¬X.RunsToEndpoint (X.arc i)[k] →
      k + 1 < (X.arc i).length := by
    intro k hk hr
    by_contra hk'
    have hlen : X.arcLength i = k + 1 := by
      have := X.length_arc i
      omega
    have := (X.arcLength_eq_succ_iff.1 hlen).1
    rw [X.getElem_arc] at hr
    exact hr this
  -- `P` runs along `S`
  have hPg := X.isStrandPath_iff_getElem.1 hd.isStrandPath_fst
  have hP0 : 0 < P.length := List.length_pos_iff.2 hd.isStrandPath_fst.ne_nil
  have hPhead : P.head? = some P[0] := by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hP0]
  have hPlast : P.getLast? = some P[P.length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  obtain rfl : p = P[0] := Option.some_injective _ (hp.symm.trans hPhead)
  obtain ⟨k₀, hk₀, hk₀P⟩ := List.getElem_of_mem hpS
  have hyint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[P.length - 1])) := by
    rw [← X.pathEnd_of_getLast? hPlast, hd.pathEnd_fst]
    exact (X.mem_internalVertices.1 hd.mem_right).2
  have hPnr : ∀ t (ht : t < P.length), ¬X.RunsToEndpoint P[t] := by
    intro t ht
    by_cases ht' : t + 1 < P.length
    · exact (hPg.2.2 t ht').1
    · have e : P[t] = P[P.length - 1] := by
        congr 1
        omega
      rw [e]
      exact hyint
  have hPS : ∀ t (ht : t < P.length), ∃ h : k₀ + t + 1 < (X.arc i).length,
      P[t] = (X.arc i)[k₀ + t] := by
    intro t ht
    induction t with
    | zero =>
      refine ⟨hSlast k₀ hk₀ (by rw [hk₀P]; exact hPnr 0 hP0), hk₀P.symm⟩
    | succ t ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      have e : P[t + 1] = (X.arc i)[k₀ + t + 1] := by
        rw [(hPg.2.2 t ht).2, h2, ← (hSg (k₀ + t) h1).2]
      exact ⟨hSlast _ (by omega) (show ¬X.RunsToEndpoint (X.arc i)[k₀ + t + 1] by
        rw [← e]; exact hPnr _ ht), e⟩
  have hxint : ¬X.IsBoundaryVertex x := (X.mem_internalVertices.1 hd.mem_left).2
  have hxv : x = X.vertexOf P[0] := by rw [← hd.pathStart_fst, X.pathStart_of_head? hPhead]
  have hk₀1 : 1 ≤ k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | h0
    · subst h0
      exact absurd (hxv ▸ hk₀P ▸ hS0B) hxint
    · exact h0
  have hlx : k₀ - 1 + 1 < (X.arc i).length := by omega
  have hx : x = X.vertexOf (X.inv (X.arc i)[k₀ - 1]) := by
    rw [hxv, ← hk₀P, ← (hSg (k₀ - 1) hlx).vertexOf_eq]
    congr 2
    omega
  obtain ⟨hly, hPlastS⟩ := hPS (P.length - 1) (by omega)
  have hy : y = X.vertexOf (X.inv (X.arc i)[k₀ + (P.length - 1)]) := by
    rw [← hd.pathEnd_fst, X.pathEnd_of_getLast? hPlast, hPlastS]
  -- `Q` avoids the darts of `S`
  have hQg := X.isStrandPath_iff_getElem.1 hd.isStrandPath_snd
  have hQ0 : 0 < Q.length := List.length_pos_iff.2 hd.isStrandPath_snd.ne_nil
  have hQhead : Q.head? = some Q[0] := by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hQ0]
  have hQS : ∀ t (ht : t < Q.length), Q[t] ∉ X.arc i := by
    intro t ht
    induction t with
    | zero =>
      intro hm
      obtain ⟨k', hk', hk'Q⟩ := List.getElem_of_mem hm
      have hv : X.vertexOf (X.arc i)[k'] = x := by
        rw [hk'Q, ← hd.pathStart_snd, X.pathStart_of_head? hQhead]
      rcases k' with _ | k'
      · exact hxint (hv ▸ hS0B)
      · rw [(hSg k' hk').vertexOf_eq, hx] at hv
        have := hSinj hk' hlx hv
        apply hd.head?_ne
        rw [hPhead, hQhead, ← hk'Q, hk₀P.symm]
        congr 2
        omega
    | succ t ih =>
      intro hm
      obtain ⟨k', hk', hk'Q⟩ := List.getElem_of_mem hm
      have hs := hQg.2.2 t ht
      rcases k' with _ | k'
      · apply hs.1
        change X.IsBoundaryVertex (X.vertexOf (X.inv Q[t]))
        rw [← hs.vertexOf_eq, ← hk'Q]
        exact hS0B
      · apply ih (by omega)
        have h3 : (X.rot ^ 3) (X.inv Q[t]) = (X.rot ^ 3) (X.inv (X.arc i)[k']) := by
          rw [← hs.2, ← hk'Q, (hSg k' hk').2]
        have := X.inv.injective ((X.rot ^ 3).injective h3)
        rw [this]
        exact List.getElem_mem _
  obtain ⟨ζ, Q', a, c, hac, hQ'⟩ := exists_isReturningPath_of_isStrandPath hX hS
    hd.isStrandPath_snd (fun q hq => by
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hq
      exact hQS t ht) hlx hly (by omega)
    (by rw [hd.pathStart_snd, hx]) (by rw [hd.pathEnd_snd, hy])
  refine ⟨i, ζ, hS, ?_, Q', a, c, hac, hQ'⟩
  -- the cut list contains the `ζ` list, which has at least two darts
  have hlen : 2 ≤ 2 * (X.arcLength i - 1) := by
    have := X.length_arc i
    have := hQ'.lt_right
    omega
  cases ζ with
  | right =>
    simp only [arcCutList, rightCutList, List.length_append, List.length_map]
    rw [length_flatMap_two' _ (fun _ => rfl)]
    simp only [List.length_range]
    omega
  | left =>
    simp only [arcCutList, leftCutList, List.length_append, List.length_map]
    rw [length_flatMap_two' _ (fun _ => rfl)]
    simp only [List.length_reverse, List.length_range]
    omega

/-! ### A combing creates no returning path -/

/-- The value `-1` (right) or `0` (left) of the winding function of a simple arc on a side. -/
private def sideValue : StrandSide → ℤ
  | .right => -1
  | .left => 0

/-- The `ζ` list of a simple arc lies on its side `ζ`. -/
private theorem mem_arcSide_of_mem_sideList {X : TripleData H b} (hX : X.IsTripleDiagram)
    {i : Fin b} (hS : X.IsSimpleArc i) {ζ : StrandSide} {d : H}
    (hd : d ∈ X.sideList ζ (X.arc i)) : d ∈ X.arcSide i (sideValue ζ) := by
  obtain ⟨k, hk, h⟩ := mem_sideList_arc.1 hd
  cases ζ <;> simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at h
  · rcases h with rfl | rfl
    · exact (hS.rot_pow_inv_arcDart_mem_rightSide hX hk).1
    · exact (hS.rot_pow_inv_arcDart_mem_rightSide hX hk).2
  · rcases h with rfl | rfl
    · exact (hS.rot_pow_inv_arcDart_mem_leftSide hX hk).1
    · exact (hS.rot_pow_inv_arcDart_mem_leftSide hX hk).2

/-- An arc ends at an endpoint. -/
private theorem isBoundaryVertex_pathEnd_arc {X : TripleData H b} (hX : X.IsPreTripleDiagram)
    (i : Fin b) : X.IsBoundaryVertex (X.pathEnd (X.arc i)) := by
  have h0 := hX.arcLength_ne_zero i
  obtain ⟨m, hm⟩ : ∃ m, X.arcLength i = m + 1 := ⟨X.arcLength i - 1, by omega⟩
  have hend := (X.arcLength_eq_succ_iff.1 hm).1
  have hlast : (X.arc i).getLast? = some (X.arcDart i m) := by
    rw [List.getLast?_eq_getElem?, X.length_arc, hm, show m + 1 - 1 = m by omega,
      List.getElem?_eq_getElem (by rw [X.length_arc]; omega), X.getElem_arc]
  rw [X.pathEnd_of_getLast? hlast]
  exact hend

private theorem vertexOf_subset_of_rot_mem_iff {X : TripleData H b} {D : Finset H}
    (hDrot : ∀ d, X.rot d ∈ D ↔ d ∈ D) {d : H} (hd : d ∈ D) : X.vertexOf d ⊆ D := by
  intro e he
  obtain ⟨k, rfl⟩ := (X.mem_vertexOf.1 he).exists_nat_pow_eq
  clear he
  induction k with
  | zero => simpa using hd
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact (hDrot _).2 ih

/-- **Sides after a local replacement along a simple arc.** Let `X'` be obtained from the triple
diagram `X` by changing the rotation on a set `D` of darts at triple points, closed under `σ`,
keeping the strand permutation, and let the arcs `S`, `S'` from `s_i` of `X`, `X'` be simple, with
the same darts outside `D`, and with `ζ` lists `L₁ ++ F ++ L₂` and `L₁ ++ B ++ L₂`, where the
`ζ` darts of `S` in `D` are those of `F`, the darts of `B` lie in `D ∩ H_ζ(S)`, and the reverse of
a dart of `(D ∩ H_ζ(S)) \ B` lies there too. Then `H_ζ(S') ⊆ (H_ζ(S) \ D) ∪ B`. -/
private theorem arcSide_subset_of_local {X X' : TripleData H b} (hX : X.IsTripleDiagram)
    (hX' : X'.IsTripleDiagram) (hinv : X'.inv = X.inv) (hbdry : X'.bdry = X.bdry)
    (hend : X'.endDart = X.endDart) (hperm : X'.strandPerm = X.strandPerm) {D : Finset H}
    (hDrot : ∀ d, X.rot d ∈ D ↔ d ∈ D) (hrot : ∀ d ∉ D, X'.rot d = X.rot d)
    (hDint : ∀ d ∈ D, ¬X.IsBoundaryVertex (X.vertexOf d)) {i : Fin b} (hS : X.IsSimpleArc i)
    (hS' : X'.IsSimpleArc i) (hfilt : (X'.arc i).filter (· ∉ D) = (X.arc i).filter (· ∉ D))
    {ζ : StrandSide} {L₁ F L₂ B : List H} (hsl : X.sideList ζ (X.arc i) = L₁ ++ F ++ L₂)
    (hsl' : X'.sideList ζ (X'.arc i) = L₁ ++ B ++ L₂)
    (hF : ∀ d ∈ X.sideList ζ (X.arc i), d ∈ D → d ∈ F)
    (hB : ∀ d ∈ B, d ∈ D ∧ d ∈ X.arcSide i (sideValue ζ))
    (hpair : ∀ d ∈ D, d ∈ X.arcSide i (sideValue ζ) → d ∉ B → X.inv d ∈ D ∧ X.inv d ∉ B) :
    ∀ d ∈ X'.arcSide i (sideValue ζ), d ∈ (X.arcSide i (sideValue ζ) \ D) ∪ B.toFinset := by
  have hpre := hX.toIsPreTripleDiagram
  have hpre' := hX'.toIsPreTripleDiagram
  have hSs := hS.isSimpleStrandPath hX
  have hSs' := hS'.isSimpleStrandPath hX'
  set K := X.arcSide i (sideValue ζ) with hKdef
  have hKinv : ∀ d ∈ K, X.inv d ∈ K := fun d hd => hS.inv_mem_arcSide hX hd
  have hDv : ∀ d ∈ D, X.vertexOf d ⊆ D := fun d hd => vertexOf_subset_of_rot_mem_iff hDrot hd
  have hDB : ∀ d ∈ D, d ∉ X.bdry := fun d hd hdB => hDint d hd ⟨d, X.self_mem_vertexOf d, hdB⟩
  have hKrot : ∀ d ∈ K, ¬X.IsBoundaryVertex (X.vertexOf d) →
      (∀ e ∈ X.arc i, X.vertexOf d ≠ X.vertexOf e ∧ X.vertexOf d ≠ X.vertexOf (X.inv e)) →
      X.rot d ∈ K ∧ X.rot.symm d ∈ K := by
    intro d hd hb hav
    have hpass : ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d) := by
      rintro ⟨-, e, he, hve⟩
      exact (hav e (List.mem_toFinset.1 he)).1 hve.symm
    have hint := X.vertexOf_mem_internalVertices.2 hb
    exact ⟨mem_arcSide_of_mem_vertexOf' hX hS hint hpass hd (X.rot_mem_vertexOf d),
      mem_arcSide_of_mem_vertexOf' hX hS hint hpass hd (X.rot_symm_mem_vertexOf d)⟩
  have hBsub : B.toFinset ⊆ D ∩ K := fun d hd => mem_inter.2 (hB d (List.mem_toFinset.1 hd))
  have hpair' : ∀ d ∈ (D ∩ K) \ B.toFinset, X.inv d ∈ (D ∩ K) \ B.toFinset := by
    intro d hd
    obtain ⟨hdDK, hdB⟩ := mem_sdiff.1 hd
    obtain ⟨hdD, hdK⟩ := mem_inter.1 hdDK
    obtain ⟨h1, h2⟩ := hpair d hdD hdK (fun h => hdB (List.mem_toFinset.2 h))
    exact mem_sdiff.2 ⟨mem_inter.2 ⟨h1, hKinv d hdK⟩, fun h => h2 (List.mem_toFinset.1 h)⟩
  have hL'list : ∀ d ∈ B.toFinset, d ∈ X'.sideList ζ (X'.arc i) := by
    intro d hd
    rw [hsl']
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_toFinset.1 hd))
  have hpts : ∀ v ∈ X.internalVertices, Disjoint v D →
      (∃ e ∈ X.arc i, v = X.vertexOf e ∨ v = X.vertexOf (X.inv e)) →
      ∃ e ∈ X'.arc i, v = X'.vertexOf e ∨ v = X'.vertexOf (X'.inv e) := by
    rintro v hv hvD ⟨e, he, hve⟩
    obtain ⟨e₀, he₀, hve₀⟩ : ∃ e₀ ∈ X.arc i, v = X.vertexOf e₀ := by
      rcases hve with h' | h'
      · exact ⟨e, he, h'⟩
      · rcases vertexOf_inv_mem_of_isStrandPath hSs.isStrandPath he with ⟨e', he', h''⟩ | h''
        · exact ⟨e', he', h'.trans h''⟩
        · exact absurd (h'.trans h'' ▸ isBoundaryVertex_pathEnd_arc hpre i)
            (X.mem_internalVertices.1 hv).2
    have he₀D : e₀ ∉ D := fun h' =>
      disjoint_left.1 hvD (by rw [hve₀]; exact X.self_mem_vertexOf e₀) h'
    have he₀P' : e₀ ∈ X'.arc i := by
      have : e₀ ∈ (X.arc i).filter (· ∉ D) := List.mem_filter.2 ⟨he₀, by simpa using he₀D⟩
      rw [← hfilt] at this
      exact (List.mem_filter.1 this).1
    exact ⟨e₀, he₀P', Or.inl (by rw [hve₀, vertexOf_eq_of_notMem hrot hDrot he₀D])⟩
  have hcl := reach_of_local_replacement (X := X) (X' := X') hinv hbdry hX.inv_involutive hrot hDv
    (P := X.arc i) (P' := X'.arc i) (ζ := ζ) (K := K) (L' := B.toFinset) hKinv hKrot hBsub
    hpair' hL'list hpts
  -- the darts of the `ζ` list of `S'`
  have hnd := nodup_sideList' hpre hSs ζ
  rw [hsl] at hnd
  have hside' : ∀ d ∈ X'.sideList ζ (X'.arc i), d ∈ (K \ D) ∪ B.toFinset := by
    intro d hd
    rw [hsl'] at hd
    have hL : ∀ d, (d ∈ L₁ ∨ d ∈ L₂) → d ∈ K \ D := by
      intro d hdL
      have hdS : d ∈ X.sideList ζ (X.arc i) := by
        rw [hsl]
        rcases hdL with h' | h' <;> simp [h']
      refine mem_sdiff.2 ⟨mem_arcSide_of_mem_sideList hX hS hdS, fun hdD => ?_⟩
      have hdF := hF d hdS hdD
      rcases hdL with h' | h'
      · exact List.disjoint_of_nodup_append (List.Nodup.of_append_left hnd) h' hdF
      · rw [List.append_assoc] at hnd
        exact List.disjoint_of_nodup_append (List.Nodup.of_append_right hnd) hdF h'
    rcases List.mem_append.1 hd with hd | hd
    · rcases List.mem_append.1 hd with hd | hd
      · exact mem_union_left _ (hL d (Or.inl hd))
      · exact mem_union_right _ (List.mem_toFinset.2 hd)
    · exact mem_union_left _ (hL d (Or.inr hd))
  -- the legs at the `ζ` positions
  have hEI : X'.arcEndIndex i = X.arcEndIndex i := by simp only [arcEndIndex, hperm]
  have hleg : ∀ r, X.endDart r ∉ D := fun r hr =>
    hDint _ hr (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2
  have hcut : ∀ d ∈ X'.arcCutList i ζ, d ∈ (K \ D) ∪ B.toFinset := by
    intro d hd
    cases ζ with
    | right =>
      rcases mem_rightCutList.1 hd with ⟨r, hr, rfl⟩ | ⟨k, hk, h⟩
      · have hr' : X.IsRightPosition i r := by
          simpa only [IsRightPosition, rightRun, rightRunLength, hEI] using hr
        rw [hend]
        exact mem_union_left _ (mem_sdiff.2 ⟨hS.endDart_mem_rightSide hX hr', hleg r⟩)
      · exact hside' d (mem_sideList_arc.2 ⟨k, hk, by simpa [sideDarts] using h⟩)
    | left =>
      rcases mem_leftCutList.1 hd with ⟨r, hr, rfl⟩ | ⟨k, hk, h⟩
      · have hr' : X.IsLeftPosition i r := by
          simpa only [IsLeftPosition, hEI] using hr
        rw [hend]
        exact mem_union_left _ (mem_sdiff.2 ⟨hS.endDart_mem_leftSide hX hr', hleg r⟩)
      · exact hside' d (mem_sideList_arc.2 ⟨k, hk, by simpa [sideDarts] using h⟩)
  -- `(K \ D) ∪ B` is closed in `X'`
  set T : Finset H := (K \ D) ∪ B.toFinset with hTdef
  have hclinv : ∀ d ∈ (T : Set H), X'.inv d ∈ (T : Set H) :=
    fun d hd => mem_coe.2 (hcl.1 d (mem_coe.1 hd))
  have hclrot : ∀ d ∈ (T : Set H), X'.vertexOf d ∈ X'.internalVertices →
      ¬X'.PassesThrough (X'.arc i).toFinset (X'.vertexOf d) →
      X'.rot d ∈ (T : Set H) ∧ X'.rot.symm d ∈ (T : Set H) := by
    intro d hd hint hpass
    have hav : ∀ e ∈ X'.arc i, X'.vertexOf d ≠ X'.vertexOf e ∧
        X'.vertexOf d ≠ X'.vertexOf (X'.inv e) := by
      have h1 : ∀ e ∈ X'.arc i, X'.vertexOf d ≠ X'.vertexOf e := fun e he h =>
        hpass ⟨hint, e, List.mem_toFinset.2 he, h.symm⟩
      refine fun e he => ⟨h1 e he, fun h => ?_⟩
      rcases vertexOf_inv_mem_of_isStrandPath hSs'.isStrandPath he with ⟨e', he', h''⟩ | h''
      · exact h1 e' he' (h.trans h'')
      · exact (X'.mem_internalVertices.1 hint).2
          (h.trans h'' ▸ isBoundaryVertex_pathEnd_arc hpre' i)
    have := hcl.2 d (mem_coe.1 hd) (X'.mem_internalVertices.1 hint).2 hav
    exact ⟨mem_coe.2 this.1, mem_coe.2 this.2⟩
  intro d hd
  cases ζ with
  | right =>
    exact mem_coe.1 ((hS'.isLeast_rightSide hX').2 ⟨fun d hd => mem_coe.2 (hcut d hd), hclinv,
      hclrot⟩ (mem_coe.2 hd))
  | left =>
    exact mem_coe.1 ((hS'.isLeast_leftSide hX').2 ⟨fun d hd => mem_coe.2 (hcut d hd), hclinv,
      hclrot⟩ (mem_coe.2 hd))

omit [Fintype H] [DecidableEq H] in
private theorem isChain_append_tail {r : H → H → Prop} {A B : List H} (hA : A.IsChain r)
    (hB : B.IsChain r) (h : A.getLast? = B.head?) : (A ++ B.tail).IsChain r := by
  rcases B with _ | ⟨c, B⟩
  · simpa using hA
  · rw [List.tail_cons, List.isChain_append]
    refine ⟨hA, hB.tail, fun x hx y hy => ?_⟩
    rw [h, List.head?_cons, Option.mem_some_iff] at hx
    subst hx
    rcases B with _ | ⟨d, B⟩
    · simp at hy
    · rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy
      exact (List.isChain_cons_cons.1 hB).1

omit [Fintype H] [DecidableEq H] in
private theorem getLast?_append_tail {A B : List H} (h : A.getLast? = B.head?) :
    (A ++ B.tail).getLast? = B.getLast? := by
  rcases B with _ | ⟨c, B⟩
  · simp only [List.head?_nil, List.getLast?_eq_none_iff] at h
    simp [h]
  · rcases B with _ | ⟨d, B⟩
    · simpa using h
    · rw [List.tail_cons, List.getLast?_append, List.getLast?_cons_cons]
      obtain ⟨x, hx⟩ : ∃ x, (d :: B).getLast? = some x :=
        ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
      rw [hx]
      rfl

omit [Fintype H] [DecidableEq H] in
private theorem isBoundaryVertex_iff_of_bdry {X X' : TripleData H b} (h : X'.bdry = X.bdry)
    (v : Finset H) : X'.IsBoundaryVertex v ↔ X.IsBoundaryVertex v := by
  unfold DiskMap.IsBoundaryVertex
  rw [h]

/-- The interior points of a strand path avoid a set of vertices as soon as the vertices of its
darts after the first one do. -/
private theorem interiorPoints_of_tail {X : TripleData H b} {P : List H} (hP : X.IsStrandPath P)
    {G : Finset H → Prop} (h : ∀ d ∈ P.tail, G (X.vertexOf d)) :
    ∀ z ∈ X.interiorPoints P, G z := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := mem_interiorPoints_iff'.1 hz
  rw [← ((X.isStrandPath_iff_getElem.1 hP).2.2 t ht).vertexOf_eq]
  apply h
  rw [← List.getElem_tail (by simp; omega)]
  exact List.getElem_mem _

/-- **No returning path after a local replacement along a simple arc.** In the setting of
`arcSide_subset_of_local`, suppose moreover that every dart `ℓ` of `B` is the last dart of a walk
of `X` starting with a `ζ` dart of `S` whose interior points are not points of `S`. If `S` has no
returning path on side `ζ`, then neither has `S'`. -/
private theorem not_isReturningPath_of_local {X X' : TripleData H b} (hX : X.IsTripleDiagram)
    (hX' : X'.IsTripleDiagram) (hinv : X'.inv = X.inv) (hbdry : X'.bdry = X.bdry)
    (hend : X'.endDart = X.endDart) (hout : X'.isOut = X.isOut)
    (hperm : X'.strandPerm = X.strandPerm) {D : Finset H}
    (hDrot : ∀ d, X.rot d ∈ D ↔ d ∈ D) (hrot : ∀ d ∉ D, X'.rot d = X.rot d)
    (hDint : ∀ d ∈ D, ¬X.IsBoundaryVertex (X.vertexOf d)) {i : Fin b} (hS : X.IsSimpleArc i)
    (hS' : X'.IsSimpleArc i) (hfilt : (X'.arc i).filter (· ∉ D) = (X.arc i).filter (· ∉ D))
    {ζ : StrandSide} {L₁ F L₂ B : List H} (hsl : X.sideList ζ (X.arc i) = L₁ ++ F ++ L₂)
    (hsl' : X'.sideList ζ (X'.arc i) = L₁ ++ B ++ L₂)
    (hF : ∀ d ∈ X.sideList ζ (X.arc i), d ∈ D → d ∈ F)
    (hB : ∀ d ∈ B, d ∈ D ∧ d ∈ X.arcSide i (sideValue ζ))
    (hpair : ∀ d ∈ D, d ∈ X.arcSide i (sideValue ζ) → d ∉ B → X.inv d ∈ D ∧ X.inv d ∉ B)
    (hW : ∀ ℓ ∈ B, ∃ W : List H, W.getLast? = some ℓ ∧ W.IsChain X.StrandStep ∧
      (∀ w ∈ W, w ∉ X.bdry) ∧ (∀ w ∈ W.head?, w ∈ X.sideList ζ (X.arc i)) ∧
      ∀ w ∈ W.dropLast, ∀ e ∈ X.arc i,
        X.vertexOf (X.inv w) ≠ X.vertexOf e ∧ X.vertexOf (X.inv w) ≠ X.vertexOf (X.inv e))
    (hret : ∀ Q a c, ¬X.IsReturningPath (X.arc i) ζ Q a c) :
    ∀ Q a c, ¬X'.IsReturningPath (X'.arc i) ζ Q a c := by
  intro R' a c hR'
  have hpre := hX.toIsPreTripleDiagram
  have hsub := arcSide_subset_of_local hX hX' hinv hbdry hend hperm hDrot hrot hDint hS hS'
    hfilt hsl hsl' hF hB hpair
  have hSs := hS.isSimpleStrandPath hX
  have hDv : ∀ d ∈ D, X.vertexOf d ⊆ D := fun d hd => vertexOf_subset_of_rot_mem_iff hDrot hd
  -- the darts of `R'`
  have hRs := hR'.isStrandPath
  have hRg := X'.isStrandPath_iff_getElem.1 hRs
  have hq : 0 < R'.length := List.length_pos_iff.2 hRs.ne_nil
  have hRhead : R'.head? = some R'[0] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hq]
  have hRlast : R'.getLast? = some R'[R'.length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have hint' : ∀ t (ht : t + 1 < R'.length), ∀ e ∈ X'.arc i,
      X'.vertexOf (X'.inv R'[t]) ≠ X'.vertexOf e ∧
        X'.vertexOf (X'.inv R'[t]) ≠ X'.vertexOf (X'.inv e) :=
    fun t ht => hR'.interiorPoints_ne _ (mem_interiorPoints' ht)
  have hpass' : ∀ j (hj : j + 1 < R'.length),
      ¬X'.PassesThrough (X'.arc i).toFinset (X'.vertexOf (X'.inv R'[j])) := by
    rintro j hj ⟨-, d, hd, hdv⟩
    exact (hint' j hj d (List.mem_toFinset.1 hd)).1 hdv.symm
  obtain ⟨e₀, he₀, f₀, hf₀, hf₀s⟩ := hR'.head?_mem
  obtain rfl : e₀ = (X'.arc i)[a]'(by have := hR'.lt_left; omega) :=
    Option.some_injective _ (he₀.symm.trans (List.getElem?_eq_getElem _))
  obtain rfl : f₀ = R'[0] := Option.some_injective _ (hf₀.symm.trans hRhead)
  obtain ⟨e₁, he₁, g₀, hg₀, hg₀s⟩ := hR'.getLast?_mem
  obtain rfl : e₁ = (X'.arc i)[c]'(by have := hR'.lt_right; omega) :=
    Option.some_injective _ (he₁.symm.trans (List.getElem?_eq_getElem _))
  obtain rfl : g₀ = R'[R'.length - 1] := Option.some_injective _ (hg₀.symm.trans hRlast)
  have hfirst' : R'[0] ∈ X'.sideList ζ (X'.arc i) := mem_sideList_iff'.2 ⟨a, hR'.lt_left, hf₀s⟩
  have hlast' : X.inv R'[R'.length - 1] ∈ X'.sideList ζ (X'.arc i) := by
    rw [← hinv]
    exact mem_sideList_iff'.2 ⟨c, hR'.lt_right, hg₀s⟩
  have hall := forall_mem_arcSide_of_isStrandPath hX' hS' hRs hpass' (fun r hr => by
    rw [hRhead, Option.mem_some_iff] at hr
    rw [← hr]
    exact mem_arcSide_of_mem_sideList hX' hS' hfirst')
  -- after its first dart, `R'` avoids `D`
  have hRD : ∀ p (hp : p + 1 < R'.length), R'[p + 1] ∉ D := by
    intro p hp
    rcases mem_union.1 (hsub _ (hall (p + 1) hp)) with h | h
    · exact (mem_sdiff.1 h).2
    · exfalso
      have hB' : R'[p + 1] ∈ X'.sideList ζ (X'.arc i) := by
        rw [hsl']
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_toFinset.1 h))
      obtain ⟨l, hl, hds⟩ := mem_sideList_iff'.1 hB'
      have hv := vertexOf_of_mem_sideDarts' hds
      have hv' := (hRg.2.2 p hp).vertexOf_eq
      exact (hint' p hp _ (List.getElem_mem (by omega : l < (X'.arc i).length))).2
        (hv'.symm.trans hv)
  have hRvD : ∀ p (hp : p + 1 < R'.length), ∀ d ∈ X.vertexOf R'[p + 1], d ∉ D := by
    intro p hp d hd hdD
    exact hRD p hp (hDv d hdD (by rw [X.vertexOf_eq_of_mem hd]; exact X.self_mem_vertexOf _))
  have hRv : ∀ p (hp : p + 1 < R'.length), X'.vertexOf R'[p + 1] = X.vertexOf R'[p + 1] :=
    fun p hp => vertexOf_eq_of_notMem hrot hDrot (hRD p hp)
  have hinvD : ∀ t (ht : t + 1 < R'.length), X.inv R'[t] ∉ D := by
    intro t ht
    apply hRvD t ht
    rw [← hRv t ht, (hRg.2.2 t ht).vertexOf_eq, hinv]
    exact X'.self_mem_vertexOf _
  -- `R'` is a walk of `X`
  have hRB : ∀ t (ht : t < R'.length), R'[t] ∉ X.bdry := fun t ht => by
    rw [← hbdry]
    exact (hRg.2.1 t ht).1
  have hRch : R'.IsChain X.StrandStep := by
    rw [List.isChain_iff_getElem]
    intro t ht
    have hs := hRg.2.2 t ht
    have hv : X'.vertexOf (X.inv R'[t]) = X.vertexOf (X.inv R'[t]) :=
      vertexOf_eq_of_notMem hrot hDrot (hinvD t ht)
    refine ⟨?_, ?_⟩
    · have h1 := hs.1
      change ¬X'.IsBoundaryVertex (X'.vertexOf (X'.inv R'[t])) at h1
      rw [hinv, hv, isBoundaryVertex_iff_of_bdry hbdry] at h1
      exact h1
    · rw [hs.2, hinv, (rot_pow_apply_of_notMem hrot hDrot (hinvD t ht) 3).1]
  -- the ends of `R'` in the `ζ` list of `S`
  have hsideS : ∀ d ∈ X'.sideList ζ (X'.arc i), d ∉ B → d ∈ X.sideList ζ (X.arc i) := by
    intro d hd hdB
    rw [hsl'] at hd
    rw [hsl]
    rcases List.mem_append.1 hd with hd | hd
    · rcases List.mem_append.1 hd with hd | hd
      · simp [hd]
      · exact absurd hd hdB
    · simp [hd]
  obtain ⟨W₁, hW₁last, hW₁ch, hW₁B, hW₁head, hW₁int⟩ : ∃ W : List H,
      W.getLast? = some R'[0] ∧ W.IsChain X.StrandStep ∧
      (∀ w ∈ W, w ∉ X.bdry) ∧ (∀ w ∈ W.head?, w ∈ X.sideList ζ (X.arc i)) ∧
      ∀ w ∈ W.dropLast, ∀ e ∈ X.arc i,
        X.vertexOf (X.inv w) ≠ X.vertexOf e ∧ X.vertexOf (X.inv w) ≠ X.vertexOf (X.inv e) := by
    by_cases h : R'[0] ∈ B
    · exact hW _ h
    · refine ⟨[R'[0]], rfl, List.isChain_singleton _, ?_, ?_, ?_⟩
      · simpa using hRB 0 hq
      · simpa using hsideS _ hfirst' h
      · simp
  obtain ⟨W₂, hW₂last, hW₂ch, hW₂B, hW₂head, hW₂int⟩ : ∃ W : List H,
      W.getLast? = some (X.inv R'[R'.length - 1]) ∧ W.IsChain X.StrandStep ∧
      (∀ w ∈ W, w ∉ X.bdry) ∧ (∀ w ∈ W.head?, w ∈ X.sideList ζ (X.arc i)) ∧
      ∀ w ∈ W.dropLast, ∀ e ∈ X.arc i,
        X.vertexOf (X.inv w) ≠ X.vertexOf e ∧ X.vertexOf (X.inv w) ≠ X.vertexOf (X.inv e) := by
    by_cases h : X.inv R'[R'.length - 1] ∈ B
    · exact hW _ h
    · refine ⟨[X.inv R'[R'.length - 1]], rfl, List.isChain_singleton _, ?_, ?_, ?_⟩
      · simpa using hpre.inv_notMem_bdry (hRB _ (by omega))
      · simpa using hsideS _ hlast' h
      · simp
  -- the walk `W₁ R' W₂⁻¹` of `X`
  set Z₂ := W₂.reverse.map X.inv with hZ₂def
  have hZ₂ch : Z₂.IsChain X.StrandStep := by
    rw [hZ₂def, List.isChain_map, List.isChain_reverse]
    exact hW₂ch.imp fun _ _ h => h.inv_inv hpre
  have hZ₂head : Z₂.head? = some R'[R'.length - 1] := by
    rw [hZ₂def, List.head?_map, List.head?_reverse, hW₂last]
    simp [hpre.inv_inv_apply]
  have hZ₂last : Z₂.getLast? = W₂.head?.map X.inv := by
    rw [hZ₂def, List.getLast?_map, List.getLast?_reverse]
  have hZ₂tail : ∀ z ∈ Z₂.tail, ∃ w ∈ W₂.dropLast, z = X.inv w := by
    intro z hz
    rw [hZ₂def, ← List.map_tail, List.tail_reverse] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    exact ⟨w, List.mem_reverse.1 hw, rfl⟩
  have hZ₂B : ∀ z ∈ Z₂, z ∉ X.bdry := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    exact hpre.inv_notMem_bdry (hW₂B w (List.mem_reverse.1 hw))
  set M := R' ++ Z₂.tail with hMdef
  have hMch : M.IsChain X.StrandStep := isChain_append_tail hRch hZ₂ch (hRlast.trans hZ₂head.symm)
  have hMhead : M.head? = some R'[0] := by
    rw [hMdef, List.head?_append, hRhead]
    rfl
  have hMlast : M.getLast? = Z₂.getLast? := getLast?_append_tail (hRlast.trans hZ₂head.symm)
  set Rl := W₁ ++ M.tail with hRldef
  have hRlch : Rl.IsChain X.StrandStep := isChain_append_tail hW₁ch hMch (hW₁last.trans hMhead.symm)
  have hRllast : Rl.getLast? = Z₂.getLast? :=
    (getLast?_append_tail (hW₁last.trans hMhead.symm)).trans hMlast
  obtain ⟨k, K', hW₁eq⟩ : ∃ k K', W₁ = k :: K' := by
    rcases W₁ with _ | ⟨k, K'⟩
    · simp at hW₁last
    · exact ⟨k, K', rfl⟩
  have hRlB : ∀ x ∈ Rl, x ∉ X.bdry := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hW₁B x hx
    · rcases List.mem_append.1 (List.mem_of_mem_tail hx) with hx | hx
      · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
        exact hRB t ht
      · exact hZ₂B x (List.mem_of_mem_tail hx)
  have hkout : X.isOut k = true := by
    have h1 := X.isOut_eq_of_isChain hpre (K := K') (k := k) (by rw [← hW₁eq]; exact hW₁B)
      (by rw [← hW₁eq]; exact hW₁ch) R'[0] (by rw [← hW₁eq]; exact List.mem_of_getLast? hW₁last)
    rw [← h1, ← hout]
    exact (hRg.2.1 0 hq).2
  have hRls : X.IsStrandPath Rl :=
    X.isStrandPath_of_isChain hpre (by rw [hRldef, hW₁eq]; simp) hRlB hRlch
      (by simp only [hRldef, hW₁eq, List.cons_append, List.head_cons]; exact hkout)
  -- its first dart and the reverse of its last dart are `ζ` darts of `S`
  have hk : k ∈ X.sideList ζ (X.arc i) := hW₁head k (by rw [hW₁eq]; rfl)
  obtain ⟨a₀, ha₀, hka₀⟩ := mem_sideList_iff'.1 hk
  obtain ⟨w₂, hw₂⟩ : ∃ w, W₂.head? = some w := by
    rcases W₂ with _ | ⟨w, W⟩
    · simp at hW₂last
    · exact ⟨w, rfl⟩
  have hw₂S : w₂ ∈ X.sideList ζ (X.arc i) := hW₂head w₂ hw₂
  obtain ⟨c₀, hc₀, hwc₀⟩ := mem_sideList_iff'.1 hw₂S
  have hRllast' : Rl.getLast? = some (X.inv w₂) := by rw [hRllast, hZ₂last, hw₂]; rfl
  -- its interior points are not points of `S`
  have hgood : ∀ d ∈ Rl.tail, ∀ e ∈ X.arc i,
      X.vertexOf d ≠ X.vertexOf e ∧ X.vertexOf d ≠ X.vertexOf (X.inv e) := by
    intro d hd
    rw [hRldef, List.tail_append_of_ne_nil (by rw [hW₁eq]; simp)] at hd
    rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hd
      rw [List.getElem_tail]
      have hs := (List.isChain_iff_getElem.1 hW₁ch) t (by simp at ht; omega)
      rw [hs.vertexOf_eq]
      exact hW₁int _ (List.mem_iff_getElem.2 ⟨t, by simp at ht ⊢; omega, by simp⟩)
    · rw [hMdef, List.tail_append_of_ne_nil hRs.ne_nil] at hd
      rcases List.mem_append.1 hd with hd | hd
      · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hd
        rw [List.getElem_tail]
        have ht' : t + 1 < R'.length := by simp at ht; omega
        have hzD := hRvD t ht'
        have hzint : ¬X.IsBoundaryVertex (X.vertexOf R'[t + 1]) := by
          rw [← isBoundaryVertex_iff_of_bdry hbdry, ← hRv t ht', (hRg.2.2 t ht').vertexOf_eq]
          exact (hRg.2.2 t ht').1
        have hpt : ∀ e ∈ X.arc i, X.vertexOf R'[t + 1] ≠ X.vertexOf e := by
          intro e he h
          have heD : e ∉ D := hzD e (by rw [h]; exact X.self_mem_vertexOf e)
          have heS' : e ∈ X'.arc i := by
            have : e ∈ (X.arc i).filter (· ∉ D) := List.mem_filter.2 ⟨he, by simpa using heD⟩
            rw [← hfilt] at this
            exact (List.mem_filter.1 this).1
          apply (hint' t ht' e heS').1
          rw [← (hRg.2.2 t ht').vertexOf_eq, hRv t ht', h, vertexOf_eq_of_notMem hrot hDrot heD]
        refine fun e he => ⟨hpt e he, fun h => ?_⟩
        rcases vertexOf_inv_mem_of_isStrandPath hSs.isStrandPath he with ⟨e', he', h'⟩ | h'
        · exact hpt e' he' (h.trans h')
        · exact hzint (h.trans h' ▸ isBoundaryVertex_pathEnd_arc hpre i)
      · obtain ⟨w, hw, rfl⟩ := hZ₂tail d hd
        exact hW₂int w hw
  have hRlret : X.IsReturningPath (X.arc i) ζ Rl a₀ c₀ :=
    ⟨hSs, hRls, ha₀, hc₀, ⟨_, List.getElem?_eq_getElem _, k,
      by rw [hRldef, hW₁eq]; rfl, hka₀⟩,
      ⟨_, List.getElem?_eq_getElem _, X.inv w₂, hRllast', by rw [hpre.inv_inv_apply]; exact hwc₀⟩,
      fun z hz e he => interiorPoints_of_tail (G := fun z => ∀ e ∈ X.arc i,
        z ≠ X.vertexOf e ∧ z ≠ X.vertexOf (X.inv e)) hRls hgood z hz e he⟩
  exact hret Rl a₀ c₀ hRlret

/-- After a local replacement of the rotation on a set of darts at triple points, a strand path
with the first and last darts of the arc from `s_i` is the arc from `s_i`. -/
private theorem eq_arc_of_local {X X' : TripleData H b} (hX : X.IsPreTripleDiagram)
    (hinv : X'.inv = X.inv) (hbdry : X'.bdry = X.bdry) (hend : X'.endDart = X.endDart)
    {D : Finset H} (hDrot : ∀ d, X.rot d ∈ D ↔ d ∈ D) (hrot : ∀ d ∉ D, X'.rot d = X.rot d)
    (hDint : ∀ d ∈ D, ¬X.IsBoundaryVertex (X.vertexOf d)) {i : Fin b} {P' : List H}
    (hP' : X'.IsStrandPath P') (hhead : P'.head? = (X.arc i).head?)
    (hlast : P'.getLast? = (X.arc i).getLast?) : P' = X'.arc i := by
  have hS0 : 0 < (X.arc i).length := by
    rw [X.length_arc]
    exact Nat.pos_of_ne_zero (hX.arcLength_ne_zero i)
  have hShead : (X.arc i).head? = some (X'.endDart (sourceIndex i)) := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hS0, X.getElem_arc, hend]
    rfl
  refine eq_arc_of_isStrandPath hP' (hhead.trans hShead) ?_
  intro e he
  rw [hlast] at he
  have hend' : X.IsBoundaryVertex (X.vertexOf (X.inv e)) := by
    have := isBoundaryVertex_pathEnd_arc hX i
    rwa [X.pathEnd_of_getLast? he] at this
  have heD : X.inv e ∉ D := fun h => hDint _ h hend'
  change X'.IsBoundaryVertex (X'.vertexOf (X'.inv e))
  rw [hinv, vertexOf_eq_of_notMem hrot hDrot heD, isBoundaryVertex_iff_of_bdry hbdry]
  exact hend'

/-- The arc from `s_i` is simple as soon as it is a simple strand path. -/
private theorem isSimpleArc_of_isSimpleStrandPath {X : TripleData H b} {i : Fin b}
    (h : X.IsSimpleStrandPath (X.arc i)) : X.IsSimpleArc i := by
  intro k l hk hl hv
  rw [← X.length_arc] at hk hl
  rw [← X.getElem_arc i k (by omega), ← X.getElem_arc i l (by omega)] at hv
  exact eq_of_vertexOf_inv_eq' h hk hl hv

/-- The darts `ρ_{j,1}, ρ_{j,2}` of a point `x_j` of a rail are facing darts. -/
theorem RailPoints.dart_rho_mem_facingDarts {X : TripleData H b} {p q : ℕ} (R : X.RailPoints p q)
    {j : ℕ} (hj : j ≤ p) :
    R.dart (RailLabel.rho j 1) ∈ R.facingDarts ∧ R.dart (RailLabel.rho j 2) ∈ R.facingDarts :=
  ⟨R.getElem_facingDarts_two_mul hj ▸ List.getElem_mem _,
    R.getElem_facingDarts_two_mul_add_one hj ▸ List.getElem_mem _⟩

/-- The darts of the `ζ` list of a simple strand path at the points of a rail along it on side `ζ`
are its facing darts `ρ_{j,1}, ρ_{j,2}`. -/
private theorem rail_mem_facingDarts_of_mem_darts {X : TripleData H b}
    (hX : X.IsPreTripleDiagram) {p q : ℕ} (R : X.RailPoints p q) {P : List H}
    (hP : X.IsSimpleStrandPath P) {ζ : StrandSide} (hR : R.IsAlong P ζ) {d : H}
    (hd : d ∈ X.sideList ζ P) (hdD : d ∈ R.darts) : d ∈ R.facingDarts := by
  obtain ⟨l, hl, hds⟩ := mem_sideList_iff'.1 hd
  have hvd := vertexOf_of_mem_sideDarts' hds
  obtain ⟨j, hj, hvj⟩ := (R.mem_darts_iff_of_along' hR (List.getElem_mem (by omega))
    (Or.inr hvd)).1 hdD
  obtain ⟨l', hl', hvl', hsd'⟩ := R.exists_sideDarts_eq' hX hP hR hj
  obtain rfl : l = l' := eq_of_vertexOf_inv_eq' hP hl hl' (hvd.symm.trans (hvj.trans hvl'))
  rw [hsd'] at hds
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hds
  rcases hds with rfl | rfl
  · exact (R.dart_rho_mem_facingDarts hj).1
  · exact (R.dart_rho_mem_facingDarts hj).2

/-- The facing darts of a rail along a simple strand path are darts of its side list. -/
private theorem rail_mem_sideList_of_mem_facingDarts {X : TripleData H b} {p q : ℕ}
    (R : X.RailPoints p q) {P : List H} {ζ : StrandSide} (hR : R.IsAlong P ζ) {d : H}
    (hd : d ∈ R.facingDarts) : d ∈ X.sideList ζ P := by
  obtain ⟨s, t, hst⟩ := hR.1
  rw [← hst]
  simp [hd]

/-- At a point `y_j` of a rail along a simple arc, all the darts lie on the side of one of them. -/
private theorem rail_dart_eta_mem_arcSide {X : TripleData H b} (hX : X.IsTripleDiagram)
    {p q : ℕ} (R : X.RailPoints p q) {i : Fin b} (hS : X.IsSimpleArc i) {ζ : StrandSide}
    (hR : R.IsAlong (X.arc i) ζ) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ q) {v : ℤ} {k₀ : ℕ}
    (h : R.dart (eta j k₀) ∈ X.arcSide i v) (k : ℕ) : R.dart (eta j k) ∈ X.arcSide i v := by
  have hv : ∀ k, X.vertexOf (R.dart (eta j k)) = X.vertexOf (R.eta j) := fun k =>
    X.vertexOf_eq_of_mem (R.dart_mem_vertexOf (eta j k))
  have hint : X.vertexOf (R.dart (eta j k₀)) ∈ X.internalVertices := by
    rw [hv]
    exact R.vertexOf_mem (.inr j) (by simp [pointSet]; omega)
  have hpass : ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf (R.dart (eta j k₀))) := by
    rintro ⟨-, e, he, hve⟩
    rw [hv] at hve
    exact (hR.2 j hj1 hjq e (List.mem_toFinset.1 he)).1 hve.symm
  refine mem_arcSide_of_mem_vertexOf' hX hS hint hpass h ?_
  rw [hv, ← hv k]
  exact X.self_mem_vertexOf _

/-- A strand step into a point `y_j` of a rail: if `ē = η_{j,k}`, then `e` is followed by
`η_{j,k+3}`. -/
private theorem rail_strandStep_of_inv_eq {X : TripleData H b} (hX : X.IsPreTripleDiagram)
    {p q : ℕ} (R : X.RailPoints p q) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ q) {e : H} {k : ℕ}
    (he : X.inv e = R.dart (eta j k)) :
    X.StrandStep e (R.dart (eta j ((k + 3) % 6))) := by
  have hint : ¬X.IsBoundaryVertex (X.vertexOf (R.eta j)) :=
    (X.mem_internalVertices.1 (R.vertexOf_mem (.inr j) (by simp [pointSet]; omega))).2
  refine ⟨?_, ?_⟩
  · change ¬X.IsBoundaryVertex (X.vertexOf (X.inv e))
    rw [he, X.vertexOf_eq_of_mem (R.dart_mem_vertexOf (eta j k))]
    exact hint
  · rw [he, RailPoints.dart_eta', RailPoints.dart_eta', ← Equiv.Perm.mul_apply, ← pow_add,
      hX.rot_pow_mod_six hint (3 + k), Nat.add_comm 3 k]

/-- The reverse of a dart arriving at a point `y_j` of a rail along a strand path lies at a vertex
that is not a vertex of the path. -/
private theorem rail_avoids_of_inv_eq {X : TripleData H b} {p q : ℕ} (R : X.RailPoints p q)
    {P : List H} {ζ : StrandSide} (hR : R.IsAlong P ζ) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ q)
    {e : H} {k : ℕ} (he : X.inv e = R.dart (eta j k)) :
    ∀ e' ∈ P, X.vertexOf (X.inv e) ≠ X.vertexOf e' ∧
      X.vertexOf (X.inv e) ≠ X.vertexOf (X.inv e') := by
  rw [he, X.vertexOf_eq_of_mem (R.dart_mem_vertexOf (eta j k))]
  exact hR.2 j hj1 hjq

/-- A dart at a triple point `z_{l+1}` of a simple arc lying on its side `ζ` is a `ζ` dart. -/
private theorem mem_sideDarts_of_mem_arcSide' {X : TripleData H b} (hX : X.IsTripleDiagram)
    {i : Fin b} (hS : X.IsSimpleArc i) {l : ℕ} (hl : l + 1 < (X.arc i).length) {d : H}
    (hd : d ∈ X.vertexOf (X.inv (X.arc i)[l])) {ζ : StrandSide}
    (hdv : d ∈ X.arcSide i (sideValue ζ)) : d ∈ X.sideDarts ζ (X.arc i)[l] := by
  rcases mem_sideDarts_of_mem_arcSide hX hS hl hd hdv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    cases ζ <;> simp_all [sideValue]

/-- The darts `ρ_{j,k}` of a rail along a simple arc on side `ζ` that lie on that side are
`ρ_{j,1}, ρ_{j,2}`. -/
private theorem rail_rho_mem_arcSide {X : TripleData H b} (hX : X.IsTripleDiagram) {p q : ℕ}
    (R : X.RailPoints p q) {i : Fin b} (hS : X.IsSimpleArc i) {ζ : StrandSide}
    (hR : R.IsAlong (X.arc i) ζ) {j k : ℕ} (hj : j ≤ p) (hk : k < 6)
    (h : R.dart (rho j k) ∈ X.arcSide i (sideValue ζ)) : k = 1 ∨ k = 2 := by
  have hpre := hX.toIsPreTripleDiagram
  obtain ⟨l, hl, hvl, hsd⟩ := R.exists_sideDarts_eq' hpre (hS.isSimpleStrandPath hX) hR hj
  have hmem : R.dart (rho j k) ∈ X.vertexOf (X.inv (X.arc i)[l]) := by
    rw [← hvl]
    exact R.dart_mem_vertexOf (rho j k)
  have := mem_sideDarts_of_mem_arcSide' hX hS hl hmem h
  rw [hsd] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with h' | h' <;>
  · have := RailPoints.injOn_dart hpre (rho_mem_labelSet hj hk)
      (rho_mem_labelSet hj (by norm_num)) h'
    simp only [rho, Prod.mk.injEq] at this
    omega

namespace AlignedRail

variable {r : ℕ}

/-- The labels `ρ_{0,1}`, `η_{j,1}`, `η_{j,2}` (`j ∈ [1, r]`) and `η_{r,3}` of the block that an
aligned combing puts into the side list. -/
private def IsCombBlockLabel (r : ℕ) (l : RailLabel) : Prop :=
  l = rho 0 1 ∨ l = eta r 3 ∨ ∃ j, 1 ≤ j ∧ j ≤ r ∧ (l = eta j 1 ∨ l = eta j 2)

/-- The block `(ρ_{0,1}, η_{1,1}, η_{1,2}, …, η_{r,1}, η_{r,2}, η_{r,3})` of the side list after an
aligned combing. -/
private def combBlock (R : X.AlignedRail r) : List H :=
  R.dart (rho 0 1) :: ((List.range' 1 r).flatMap fun j => [R.dart (eta j 1), R.dart (eta j 2)]) ++
    [R.dart (eta r 3)]

private theorem mem_combBlock (R : X.AlignedRail r) {d : H} :
    d ∈ R.combBlock ↔ ∃ l, IsCombBlockLabel r l ∧ d = R.dart l := by
  simp only [combBlock, IsCombBlockLabel, List.mem_append, List.mem_cons, List.mem_flatMap,
    List.mem_range'_1, List.not_mem_nil, or_false]
  constructor
  · rintro ((rfl | ⟨j, ⟨hj1, hj2⟩, rfl | rfl⟩) | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inr ⟨j, hj1, by omega, Or.inl rfl⟩), rfl⟩
    · exact ⟨_, Or.inr (Or.inr ⟨j, hj1, by omega, Or.inr rfl⟩), rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
  · rintro ⟨l, rfl | rfl | ⟨j, hj1, hj2, rfl | rfl⟩, rfl⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr rfl
    · exact Or.inl (Or.inr ⟨j, ⟨hj1, by omega⟩, Or.inl rfl⟩)
    · exact Or.inl (Or.inr ⟨j, ⟨hj1, by omega⟩, Or.inr rfl⟩)

private theorem isCombBlockLabel_mem_labelSet (hr : 1 ≤ r) {l : RailLabel}
    (hl : IsCombBlockLabel r l) : l ∈ labelSet r r := by
  rcases hl with rfl | rfl | ⟨j, hj1, hj2, rfl | rfl⟩
  · exact rho_mem_labelSet (Nat.zero_le _) (by norm_num)
  · exact eta_mem_labelSet hr le_rfl (by norm_num)
  · exact eta_mem_labelSet hj1 hj2 (by norm_num)
  · exact eta_mem_labelSet hj1 hj2 (by norm_num)

/-- The reverse of a dart of an aligned rail that is not in the block of the combing and, at the
points `x_j`, is one of `ρ_{j,1}, ρ_{j,2}`, is again such a dart of the rail. -/
private theorem exists_inv_dart_eq_comb (hX : X.IsPreTripleDiagram) (hr : 1 ≤ r)
    (R : X.AlignedRail r) {l : RailLabel} (hl : l ∈ labelSet r r)
    (hk : ∀ j k, l = rho j k → k = 1 ∨ k = 2) (hB : ¬IsCombBlockLabel r l) :
    ∃ l' ∈ labelSet r r, ¬IsCombBlockLabel r l' ∧ X.inv (R.dart l) = R.dart l' := by
  have rA : ∀ j < r, X.inv (R.dart (alignedEta j 3)) = R.dart (eta (j + 1) 0) := R.inv_eta_three
  have rB : ∀ j, 1 ≤ j → j ≤ r → X.inv (R.dart (rho j 1)) = R.dart (eta j 5) := R.inv_rho_one
  have rC : ∀ j, 1 ≤ j → j ≤ r → X.inv (R.dart (rho j 2)) = R.dart (eta j 4) := R.inv_rho_two
  have flip : ∀ {d e : H}, X.inv d = e → X.inv e = d := fun h => by rw [← h, hX.inv_inv_apply]
  rcases mem_labelSet.1 hl with ⟨j, hj, k, hk6, rfl⟩ | ⟨j, hj1, hj2, k, hk6, rfl⟩
  · rcases hk j k rfl with rfl | rfl
    · have hj0 : j ≠ 0 := fun h => hB (Or.inl (by rw [h]))
      exact ⟨eta j 5, eta_mem_labelSet (by omega) hj (by norm_num),
        by simp [IsCombBlockLabel, rho, eta], rB j (by omega) hj⟩
    · by_cases hj0 : j = 0
      · subst hj0
        refine ⟨eta 1 0, eta_mem_labelSet le_rfl hr (by norm_num),
          by simp [IsCombBlockLabel, rho, eta], ?_⟩
        simpa [alignedEta, alignedIndex] using rA 0 (by omega)
      · exact ⟨eta j 4, eta_mem_labelSet (by omega) hj (by norm_num),
          by simp [IsCombBlockLabel, rho, eta], rC j (by omega) hj⟩
  · have hk1 : k ≠ 1 := fun h => hB (Or.inr (Or.inr ⟨j, hj1, hj2, Or.inl (by rw [h])⟩))
    have hk2 : k ≠ 2 := fun h => hB (Or.inr (Or.inr ⟨j, hj1, hj2, Or.inr (by rw [h])⟩))
    interval_cases k
    · by_cases hj : j = 1
      · subst hj
        refine ⟨rho 0 2, rho_mem_labelSet (by omega) (by norm_num),
          by simp [IsCombBlockLabel, rho, eta], ?_⟩
        exact flip (by simpa [alignedEta, alignedIndex] using rA 0 (by omega))
      · refine ⟨eta (j - 1) 3, eta_mem_labelSet (by omega) (by omega) (by norm_num), ?_, ?_⟩
        · simp [IsCombBlockLabel, rho, eta]
          omega
        · have := rA (j - 1) (by omega)
          rw [show j - 1 + 1 = j by omega] at this
          exact flip (by simpa [alignedEta, show j - 1 ≠ 0 by omega] using this)
    · exact absurd rfl hk1
    · exact absurd rfl hk2
    · have hjr : j ≠ r := fun h => hB (Or.inr (Or.inl (by rw [h])))
      refine ⟨eta (j + 1) 0, eta_mem_labelSet (by omega) (by omega) (by norm_num),
        by simp [IsCombBlockLabel, rho, eta], ?_⟩
      simpa [alignedEta, show j ≠ 0 by omega] using rA j (by omega)
    · exact ⟨rho j 2, rho_mem_labelSet hj2 (by norm_num), by simp [IsCombBlockLabel, rho, eta],
        flip (rC j hj1 hj2)⟩
    · refine ⟨rho j 1, rho_mem_labelSet hj2 (by norm_num), ?_, flip (rB j hj1 hj2)⟩
      simp [IsCombBlockLabel, rho, eta]
      omega

/-- **A combing creates no returning path**, aligned case. Let `S` be the simple arc from `s_i` of
a triple diagram `X`, `ζ` a side, `r ≥ 1`, and `X'` the aligned combing of an aligned rail of
length `r` of `X` along `S` on side `ζ`. If `S` has no returning path on side `ζ` in `X`, then the
arc of `X'` from `s_i` has no returning path on side `ζ`. -/
@[cluster_algebras "lem_comb_no_return"]
theorem forall_not_isReturningPath_alignedComb (hX : X.IsTripleDiagram) {i : Fin b}
    (hS : X.IsSimpleArc i) {ζ : StrandSide} (hr : 1 ≤ r) (R : X.AlignedRail r)
    (hR : R.IsAlong (X.arc i) ζ) (hret : ∀ Q a c, ¬X.IsReturningPath (X.arc i) ζ Q a c) :
    ∀ Q a c, ¬R.alignedComb.IsReturningPath (R.alignedComb.arc i) ζ Q a c := by
  have hpre := hX.toIsPreTripleDiagram
  have hSs := hS.isSimpleStrandPath hX
  have hR' : R.toRailPoints.IsAlong (X.arc i) ζ := hR
  obtain ⟨hX', hmove⟩ := TripleDiagram.exists_moveEquivalent_alignedComb ⟨H, X, hX⟩ hr R
  have hperm : R.alignedComb.strandPerm = X.strandPerm := hmove.strandPerm_eq
  obtain ⟨P', hP's, -, hP'head, hP'last, hfilt, L₁, L₂, hsl, hsl'⟩ :=
    exists_isSimpleStrandPath_alignedComb hpre hr R hSs hR'
  have rA : ∀ j < r, X.inv (R.dart (alignedEta j 3)) = R.dart (eta (j + 1) 0) := R.inv_eta_three
  have rB : ∀ j, 1 ≤ j → j ≤ r → X.inv (R.dart (rho j 1)) = R.dart (eta j 5) := R.inv_rho_one
  have rC : ∀ j, 1 ≤ j → j ≤ r → X.inv (R.dart (rho j 2)) = R.dart (eta j 4) := R.inv_rho_two
  have hDrot : ∀ d, X.rot d ∈ R.darts ↔ d ∈ R.darts := R.rot_mem_darts_iff
  have hrot : ∀ d ∉ R.darts, R.alignedComb.rot d = X.rot d := fun d hd =>
    R.alignedComb_rot_of_notMem hd
  have hDint : ∀ d ∈ R.darts, ¬X.IsBoundaryVertex (X.vertexOf d) := fun d hd =>
    rail_not_isBoundaryVertex_of_mem_darts R.toRailPoints hd
  have hDB : ∀ d ∈ R.darts, d ∉ X.bdry := fun d hd hdB =>
    hDint d hd ⟨d, X.self_mem_vertexOf d, hdB⟩
  obtain rfl : P' = R.alignedComb.arc i :=
    eq_arc_of_local (X' := R.alignedComb) hpre rfl rfl rfl hDrot hrot hDint hP's.isStrandPath
      hP'head hP'last
  have hS' := isSimpleArc_of_isSimpleStrandPath hP's
  have hsl'' : R.alignedComb.sideList ζ (R.alignedComb.arc i) = L₁ ++ R.combBlock ++ L₂ := hsl'
  have hfacing : ∀ j ≤ r, R.dart (rho j 1) ∈ R.facingDarts ∧ R.dart (rho j 2) ∈ R.facingDarts :=
    fun _ hj => R.toRailPoints.dart_rho_mem_facingDarts hj
  have hFS : ∀ d ∈ R.facingDarts, d ∈ X.sideList ζ (X.arc i) := fun d hd =>
    rail_mem_sideList_of_mem_facingDarts R.toRailPoints hR hd
  have hFK : ∀ d ∈ R.facingDarts, d ∈ X.arcSide i (sideValue ζ) := fun d hd =>
    mem_arcSide_of_mem_sideList hX hS (hFS d hd)
  have hKeta : ∀ j, 1 ≤ j → j ≤ r → ∀ k, R.dart (eta j k) ∈ X.arcSide i (sideValue ζ) := by
    intro j h1 h2 k
    have h5 : R.dart (eta j 5) ∈ X.arcSide i (sideValue ζ) := by
      rw [← rB j h1 h2]
      exact hS.inv_mem_arcSide hX (hFK _ (hfacing j h2).1)
    exact rail_dart_eta_mem_arcSide hX R.toRailPoints hS hR h1 h2 h5 k
  have hB : ∀ d ∈ R.combBlock, d ∈ R.darts ∧ d ∈ X.arcSide i (sideValue ζ) := by
    intro d hd
    obtain ⟨l, hlB, rfl⟩ := (mem_combBlock R).1 hd
    refine ⟨R.dart_mem_darts (isCombBlockLabel_mem_labelSet hr hlB), ?_⟩
    rcases hlB with rfl | rfl | ⟨j, hj1, hj2, rfl | rfl⟩
    · exact hFK _ (hfacing 0 (Nat.zero_le _)).1
    · exact hKeta r hr le_rfl 3
    · exact hKeta j hj1 hj2 1
    · exact hKeta j hj1 hj2 2
  have hpair : ∀ d ∈ R.darts, d ∈ X.arcSide i (sideValue ζ) → d ∉ R.combBlock →
      X.inv d ∈ R.darts ∧ X.inv d ∉ R.combBlock := by
    intro d hdD hdK hdB
    rw [← RailPoints.image_dart hpre] at hdD
    obtain ⟨l, hl, rfl⟩ := mem_image.1 hdD
    have hlB : ¬IsCombBlockLabel r l := fun hb => hdB ((mem_combBlock R).2 ⟨l, hb, rfl⟩)
    have hk : ∀ j k, l = rho j k → k = 1 ∨ k = 2 := by
      rintro j k rfl
      have : j ≤ r ∧ k < 6 := by simpa [labelSet, pointSet, rho] using hl
      exact rail_rho_mem_arcSide hX R.toRailPoints hS hR this.1 this.2 hdK
    obtain ⟨l', hl', hl'B, he⟩ := exists_inv_dart_eq_comb hpre hr R hl hk hlB
    rw [he]
    refine ⟨R.dart_mem_darts hl', fun h => hl'B ?_⟩
    obtain ⟨l'', hb, heq⟩ := (mem_combBlock R).1 h
    rwa [RailPoints.injOn_dart hpre hl' (isCombBlockLabel_mem_labelSet hr hb) heq]
  have hDl : ∀ l ∈ labelSet r r, R.dart l ∉ X.bdry := fun l hl => hDB _ (R.dart_mem_darts hl)
  have hW : ∀ ℓ ∈ R.combBlock, ∃ W : List H, W.getLast? = some ℓ ∧ W.IsChain X.StrandStep ∧
      (∀ w ∈ W, w ∉ X.bdry) ∧ (∀ w ∈ W.head?, w ∈ X.sideList ζ (X.arc i)) ∧
      ∀ w ∈ W.dropLast, ∀ e ∈ X.arc i,
        X.vertexOf (X.inv w) ≠ X.vertexOf e ∧ X.vertexOf (X.inv w) ≠ X.vertexOf (X.inv e) := by
    intro ℓ hℓ
    obtain ⟨l, hlB, rfl⟩ := (mem_combBlock R).1 hℓ
    rcases hlB with rfl | rfl | ⟨j, hj1, hj2, rfl | rfl⟩
    · refine ⟨[R.dart (rho 0 1)], rfl, List.isChain_singleton _, ?_, ?_, by simp⟩
      · simpa using hDl _ (rho_mem_labelSet (Nat.zero_le _) (by norm_num))
      · simpa using hFS _ (hfacing 0 (Nat.zero_le _)).1
    · refine ⟨(List.range (r + 1)).map fun t => R.dart (alignedEta t 3), ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.getLast?_map, List.getLast?_range]
        simp [alignedEta, show r ≠ 0 by omega]
      · rw [List.isChain_iff_getElem]
        intro t ht
        simp only [List.length_map, List.length_range] at ht
        simp only [List.getElem_map, List.getElem_range]
        have := rail_strandStep_of_inv_eq hpre R.toRailPoints (j := t + 1) (by omega) (by omega)
          (k := 0) (rA t (by omega))
        simpa [alignedEta] using this
      · intro w hw
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
        exact hDl _ (alignedEta_mem_labelSet (by simp at ht; omega) (by norm_num))
      · intro w hw
        simp only [List.head?_map, Option.mem_def, Option.map_eq_some_iff] at hw
        obtain ⟨t, ht, rfl⟩ := hw
        have ht0 : t = 0 := by
          rw [List.head?_eq_getElem?, List.getElem?_range (by omega)] at ht
          exact (Option.some_injective _ ht).symm
        subst ht0
        simpa [alignedEta, alignedIndex] using hFS _ (hfacing 0 (Nat.zero_le _)).2
      · intro w hw
        rw [← List.map_dropLast, List.range_succ, List.dropLast_concat] at hw
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
        simp only [List.mem_range] at ht
        exact rail_avoids_of_inv_eq R.toRailPoints hR (j := t + 1) (by omega) (by omega)
          (rA t (by omega))
    · refine ⟨[R.dart (rho j 2), R.dart (eta j 1)], rfl, ?_, ?_, ?_, ?_⟩
      · have := rail_strandStep_of_inv_eq hpre R.toRailPoints hj1 hj2 (rC j hj1 hj2)
        simpa using this
      · intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hDl _ (rho_mem_labelSet hj2 (by norm_num))
        · exact hDl _ (eta_mem_labelSet hj1 hj2 (by norm_num))
      · simpa using hFS _ (hfacing j hj2).2
      · intro w hw
        simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        subst hw
        exact rail_avoids_of_inv_eq R.toRailPoints hR hj1 hj2 (rC j hj1 hj2)
    · refine ⟨[R.dart (rho j 1), R.dart (eta j 2)], rfl, ?_, ?_, ?_, ?_⟩
      · have := rail_strandStep_of_inv_eq hpre R.toRailPoints hj1 hj2 (rB j hj1 hj2)
        simpa using this
      · intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hDl _ (rho_mem_labelSet hj2 (by norm_num))
        · exact hDl _ (eta_mem_labelSet hj1 hj2 (by norm_num))
      · simpa using hFS _ (hfacing j hj2).1
      · intro w hw
        simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        subst hw
        exact rail_avoids_of_inv_eq R.toRailPoints hR hj1 hj2 (rB j hj1 hj2)
  exact not_isReturningPath_of_local hX hX' rfl rfl rfl rfl hperm hDrot hrot hDint hS hS'
    hfilt hsl hsl'' (fun d hd hdD => rail_mem_facingDarts_of_mem_darts hpre R.toRailPoints hSs hR
      hd hdD) hB hpair hW hret

end AlignedRail

namespace StaggeredRail

variable {r : ℕ}

/-- The labels `η_{j,1}`, `η_{j,2}` (`j ∈ [1, r]`), `η_{r,3}` and `ρ_{r,2}` of the block that a
staggered combing puts into the side list. -/
private def IsCombBlockLabel (r : ℕ) (l : RailLabel) : Prop :=
  l = rho r 2 ∨ l = eta r 3 ∨ ∃ j, 1 ≤ j ∧ j ≤ r ∧ (l = eta j 1 ∨ l = eta j 2)

/-- The block `(η_{1,1}, η_{1,2}, …, η_{r,1}, η_{r,2}, η_{r,3}, ρ_{r,2})` of the side list after a
staggered combing. -/
private def combBlock (R : X.StaggeredRail r) : List H :=
  ((List.range' 1 r).flatMap fun j => [R.dart (eta j 1), R.dart (eta j 2)]) ++
    [R.dart (eta r 3), R.dart (rho r 2)]

private theorem mem_combBlock (R : X.StaggeredRail r) {d : H} :
    d ∈ R.combBlock ↔ ∃ l, IsCombBlockLabel r l ∧ d = R.dart l := by
  simp only [combBlock, IsCombBlockLabel, List.mem_append, List.mem_cons, List.mem_flatMap,
    List.mem_range'_1, List.not_mem_nil, or_false]
  constructor
  · rintro (⟨j, ⟨hj1, hj2⟩, rfl | rfl⟩ | rfl | rfl)
    · exact ⟨_, Or.inr (Or.inr ⟨j, hj1, by omega, Or.inl rfl⟩), rfl⟩
    · exact ⟨_, Or.inr (Or.inr ⟨j, hj1, by omega, Or.inr rfl⟩), rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inl rfl, rfl⟩
  · rintro ⟨l, rfl | rfl | ⟨j, hj1, hj2, rfl | rfl⟩, rfl⟩
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl ⟨j, ⟨hj1, by omega⟩, Or.inl rfl⟩
    · exact Or.inl ⟨j, ⟨hj1, by omega⟩, Or.inr rfl⟩

private theorem isCombBlockLabel_mem_labelSet (hr : 1 ≤ r) {l : RailLabel}
    (hl : IsCombBlockLabel r l) : l ∈ labelSet r r := by
  rcases hl with rfl | rfl | ⟨j, hj1, hj2, rfl | rfl⟩
  · exact rho_mem_labelSet le_rfl (by norm_num)
  · exact eta_mem_labelSet hr le_rfl (by norm_num)
  · exact eta_mem_labelSet hj1 hj2 (by norm_num)
  · exact eta_mem_labelSet hj1 hj2 (by norm_num)

/-- The reverse of a dart of a staggered rail that is not in the block of the combing and, at the
points `x_j`, is one of `ρ_{j,1}, ρ_{j,2}`, is again such a dart of the rail. -/
private theorem exists_inv_dart_eq_comb (hX : X.IsPreTripleDiagram) (R : X.StaggeredRail r)
    {l : RailLabel} (hl : l ∈ labelSet r r)
    (hk : ∀ j k, l = rho j k → k = 1 ∨ k = 2) (hB : ¬IsCombBlockLabel r l) :
    ∃ l' ∈ labelSet r r, ¬IsCombBlockLabel r l' ∧ X.inv (R.dart l) = R.dart l' := by
  have hr := R.one_le
  have r01 : X.inv (R.dart (rho 0 1)) = R.dart (eta 1 0) := R.inv_rho_zero_one
  have rE : ∀ j, 1 ≤ j → j < r → X.inv (R.dart (eta j 3)) = R.dart (eta (j + 1) 0) :=
    R.inv_eta_three
  have rF : ∀ j, 1 ≤ j → j ≤ r → X.inv (R.dart (rho (j - 1) 2)) = R.dart (eta j 5) :=
    R.inv_rho_two
  have rG : ∀ j, 1 ≤ j → j ≤ r → X.inv (R.dart (rho j 1)) = R.dart (eta j 4) := R.inv_rho_one
  have flip : ∀ {d e : H}, X.inv d = e → X.inv e = d := fun h => by rw [← h, hX.inv_inv_apply]
  rcases mem_labelSet.1 hl with ⟨j, hj, k, hk6, rfl⟩ | ⟨j, hj1, hj2, k, hk6, rfl⟩
  · rcases hk j k rfl with rfl | rfl
    · by_cases hj0 : j = 0
      · subst hj0
        exact ⟨eta 1 0, eta_mem_labelSet le_rfl hr (by norm_num),
          by simp [IsCombBlockLabel, rho, eta], r01⟩
      · exact ⟨eta j 4, eta_mem_labelSet (by omega) hj (by norm_num),
          by simp [IsCombBlockLabel, rho, eta], rG j (by omega) hj⟩
    · have hjr : j ≠ r := fun h => hB (Or.inl (by rw [h]))
      refine ⟨eta (j + 1) 5, eta_mem_labelSet (by omega) (by omega) (by norm_num),
        by simp [IsCombBlockLabel, rho, eta], ?_⟩
      have := rF (j + 1) (by omega) (by omega)
      rwa [show j + 1 - 1 = j by omega] at this
  · have hk1 : k ≠ 1 := fun h => hB (Or.inr (Or.inr ⟨j, hj1, hj2, Or.inl (by rw [h])⟩))
    have hk2 : k ≠ 2 := fun h => hB (Or.inr (Or.inr ⟨j, hj1, hj2, Or.inr (by rw [h])⟩))
    interval_cases k
    · by_cases hj : j = 1
      · subst hj
        refine ⟨rho 0 1, rho_mem_labelSet (by omega) (by norm_num), ?_, flip r01⟩
        simp [IsCombBlockLabel, rho, eta]
      · refine ⟨eta (j - 1) 3, eta_mem_labelSet (by omega) (by omega) (by norm_num), ?_, ?_⟩
        · simp [IsCombBlockLabel, rho, eta]
          omega
        · have := rE (j - 1) (by omega) (by omega)
          rw [show j - 1 + 1 = j by omega] at this
          exact flip this
    · exact absurd rfl hk1
    · exact absurd rfl hk2
    · have hjr : j ≠ r := fun h => hB (Or.inr (Or.inl (by rw [h])))
      exact ⟨eta (j + 1) 0, eta_mem_labelSet (by omega) (by omega) (by norm_num),
        by simp [IsCombBlockLabel, rho, eta], rE j hj1 (by omega)⟩
    · refine ⟨rho j 1, rho_mem_labelSet hj2 (by norm_num), ?_, flip (rG j hj1 hj2)⟩
      simp [IsCombBlockLabel, rho, eta]
    · refine ⟨rho (j - 1) 2, rho_mem_labelSet (by omega) (by norm_num), ?_, flip (rF j hj1 hj2)⟩
      simp [IsCombBlockLabel, rho, eta]
      omega

/-- **A combing creates no returning path**, staggered case. Let `S` be the simple arc from `s_i`
of a triple diagram `X`, `ζ` a side, and `X'` the staggered combing of a staggered rail of length
`r ≥ 1` of `X` along `S` on side `ζ`. If `S` has no returning path on side `ζ` in `X`, then the
arc of `X'` from `s_i` has no returning path on side `ζ`. -/
@[cluster_algebras "lem_comb_no_return"]
theorem forall_not_isReturningPath_staggeredComb (hX : X.IsTripleDiagram) {i : Fin b}
    (hS : X.IsSimpleArc i) {ζ : StrandSide} (R : X.StaggeredRail r)
    (hR : R.IsAlong (X.arc i) ζ) (hret : ∀ Q a c, ¬X.IsReturningPath (X.arc i) ζ Q a c) :
    ∀ Q a c, ¬R.staggeredComb.IsReturningPath (R.staggeredComb.arc i) ζ Q a c := by
  have hpre := hX.toIsPreTripleDiagram
  have hr := R.one_le
  have hSs := hS.isSimpleStrandPath hX
  have hR' : R.toRailPoints.IsAlong (X.arc i) ζ := hR
  obtain ⟨hX', hmove⟩ := TripleDiagram.exists_moveEquivalent_staggeredComb ⟨H, X, hX⟩ R
  have hperm : R.staggeredComb.strandPerm = X.strandPerm := hmove.strandPerm_eq
  obtain ⟨P', hP's, -, hP'head, hP'last, hfilt, L₁, L₂, hsl, hsl'⟩ :=
    exists_isSimpleStrandPath_staggeredComb hpre R hSs hR'
  have r01 : X.inv (R.dart (rho 0 1)) = R.dart (eta 1 0) := R.inv_rho_zero_one
  have rE : ∀ j, 1 ≤ j → j < r → X.inv (R.dart (eta j 3)) = R.dart (eta (j + 1) 0) :=
    R.inv_eta_three
  have rF : ∀ j, 1 ≤ j → j ≤ r → X.inv (R.dart (rho (j - 1) 2)) = R.dart (eta j 5) :=
    R.inv_rho_two
  have rG : ∀ j, 1 ≤ j → j ≤ r → X.inv (R.dart (rho j 1)) = R.dart (eta j 4) := R.inv_rho_one
  have hDrot : ∀ d, X.rot d ∈ R.darts ↔ d ∈ R.darts := R.rot_mem_darts_iff
  have hrot : ∀ d ∉ R.darts, R.staggeredComb.rot d = X.rot d := fun d hd =>
    R.staggeredComb_rot_of_notMem hd
  have hDint : ∀ d ∈ R.darts, ¬X.IsBoundaryVertex (X.vertexOf d) := fun d hd =>
    rail_not_isBoundaryVertex_of_mem_darts R.toRailPoints hd
  have hDB : ∀ d ∈ R.darts, d ∉ X.bdry := fun d hd hdB =>
    hDint d hd ⟨d, X.self_mem_vertexOf d, hdB⟩
  obtain rfl : P' = R.staggeredComb.arc i :=
    eq_arc_of_local (X' := R.staggeredComb) hpre rfl rfl rfl hDrot hrot hDint hP's.isStrandPath
      hP'head hP'last
  have hS' := isSimpleArc_of_isSimpleStrandPath hP's
  have hsl'' : R.staggeredComb.sideList ζ (R.staggeredComb.arc i) = L₁ ++ R.combBlock ++ L₂ :=
    hsl'
  have hfacing : ∀ j ≤ r, R.dart (rho j 1) ∈ R.facingDarts ∧ R.dart (rho j 2) ∈ R.facingDarts :=
    fun _ hj => R.toRailPoints.dart_rho_mem_facingDarts hj
  have hFS : ∀ d ∈ R.facingDarts, d ∈ X.sideList ζ (X.arc i) := fun d hd =>
    rail_mem_sideList_of_mem_facingDarts R.toRailPoints hR hd
  have hFK : ∀ d ∈ R.facingDarts, d ∈ X.arcSide i (sideValue ζ) := fun d hd =>
    mem_arcSide_of_mem_sideList hX hS (hFS d hd)
  have hKeta : ∀ j, 1 ≤ j → j ≤ r → ∀ k, R.dart (eta j k) ∈ X.arcSide i (sideValue ζ) := by
    intro j h1 h2 k
    have h5 : R.dart (eta j 5) ∈ X.arcSide i (sideValue ζ) := by
      rw [← rF j h1 h2]
      exact hS.inv_mem_arcSide hX (hFK _ (hfacing (j - 1) (by omega)).2)
    exact rail_dart_eta_mem_arcSide hX R.toRailPoints hS hR h1 h2 h5 k
  have hB : ∀ d ∈ R.combBlock, d ∈ R.darts ∧ d ∈ X.arcSide i (sideValue ζ) := by
    intro d hd
    obtain ⟨l, hlB, rfl⟩ := (mem_combBlock R).1 hd
    refine ⟨R.dart_mem_darts (isCombBlockLabel_mem_labelSet hr hlB), ?_⟩
    rcases hlB with rfl | rfl | ⟨j, hj1, hj2, rfl | rfl⟩
    · exact hFK _ (hfacing r le_rfl).2
    · exact hKeta r hr le_rfl 3
    · exact hKeta j hj1 hj2 1
    · exact hKeta j hj1 hj2 2
  have hpair : ∀ d ∈ R.darts, d ∈ X.arcSide i (sideValue ζ) → d ∉ R.combBlock →
      X.inv d ∈ R.darts ∧ X.inv d ∉ R.combBlock := by
    intro d hdD hdK hdB
    rw [← RailPoints.image_dart hpre] at hdD
    obtain ⟨l, hl, rfl⟩ := mem_image.1 hdD
    have hlB : ¬IsCombBlockLabel r l := fun hb => hdB ((mem_combBlock R).2 ⟨l, hb, rfl⟩)
    have hk : ∀ j k, l = rho j k → k = 1 ∨ k = 2 := by
      rintro j k rfl
      have : j ≤ r ∧ k < 6 := by simpa [labelSet, pointSet, rho] using hl
      exact rail_rho_mem_arcSide hX R.toRailPoints hS hR this.1 this.2 hdK
    obtain ⟨l', hl', hl'B, he⟩ := exists_inv_dart_eq_comb hpre R hl hk hlB
    rw [he]
    refine ⟨R.dart_mem_darts hl', fun h => hl'B ?_⟩
    obtain ⟨l'', hb, heq⟩ := (mem_combBlock R).1 h
    rwa [RailPoints.injOn_dart hpre hl' (isCombBlockLabel_mem_labelSet hr hb) heq]
  have hDl : ∀ l ∈ labelSet r r, R.dart l ∉ X.bdry := fun l hl => hDB _ (R.dart_mem_darts hl)
  -- the walk `ρ_{0,1}, η_{1,3}, …, η_{r,3}`
  set f : ℕ → H := fun t => if t = 0 then R.dart (rho 0 1) else R.dart (eta t 3) with hfdef
  have hf : ∀ t < r, X.inv (f t) = R.dart (eta (t + 1) 0) := by
    intro t ht
    by_cases h0 : t = 0
    · subst h0
      simpa [hfdef] using r01
    · simpa [hfdef, h0] using rE t (by omega) ht
  have hW : ∀ ℓ ∈ R.combBlock, ∃ W : List H, W.getLast? = some ℓ ∧ W.IsChain X.StrandStep ∧
      (∀ w ∈ W, w ∉ X.bdry) ∧ (∀ w ∈ W.head?, w ∈ X.sideList ζ (X.arc i)) ∧
      ∀ w ∈ W.dropLast, ∀ e ∈ X.arc i,
        X.vertexOf (X.inv w) ≠ X.vertexOf e ∧ X.vertexOf (X.inv w) ≠ X.vertexOf (X.inv e) := by
    intro ℓ hℓ
    obtain ⟨l, hlB, rfl⟩ := (mem_combBlock R).1 hℓ
    rcases hlB with rfl | rfl | ⟨j, hj1, hj2, rfl | rfl⟩
    · refine ⟨[R.dart (rho r 2)], rfl, List.isChain_singleton _, ?_, ?_, by simp⟩
      · simpa using hDl _ (rho_mem_labelSet le_rfl (by norm_num))
      · simpa using hFS _ (hfacing r le_rfl).2
    · refine ⟨(List.range (r + 1)).map f, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.getLast?_map, List.getLast?_range]
        simp [hfdef, show r ≠ 0 by omega]
      · rw [List.isChain_iff_getElem]
        intro t ht
        simp only [List.length_map, List.length_range] at ht
        simp only [List.getElem_map, List.getElem_range]
        have := rail_strandStep_of_inv_eq hpre R.toRailPoints (j := t + 1) (by omega) (by omega)
          (k := 0) (hf t (by omega))
        simpa [hfdef] using this
      · intro w hw
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
        by_cases h0 : t = 0
        · simpa [hfdef, h0] using hDl _ (rho_mem_labelSet (Nat.zero_le _) (by norm_num))
        · simpa [hfdef, h0] using hDl _ (eta_mem_labelSet (by omega)
            (by simp at ht; omega) (by norm_num))
      · intro w hw
        simp only [List.head?_map, Option.mem_def, Option.map_eq_some_iff] at hw
        obtain ⟨t, ht, rfl⟩ := hw
        have ht0 : t = 0 := by
          rw [List.head?_eq_getElem?, List.getElem?_range (by omega)] at ht
          exact (Option.some_injective _ ht).symm
        subst ht0
        simpa [hfdef] using hFS _ (hfacing 0 (Nat.zero_le _)).1
      · intro w hw
        rw [← List.map_dropLast, List.range_succ, List.dropLast_concat] at hw
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
        simp only [List.mem_range] at ht
        exact rail_avoids_of_inv_eq R.toRailPoints hR (j := t + 1) (by omega) (by omega)
          (hf t ht)
    · refine ⟨[R.dart (rho j 1), R.dart (eta j 1)], rfl, ?_, ?_, ?_, ?_⟩
      · have := rail_strandStep_of_inv_eq hpre R.toRailPoints hj1 hj2 (rG j hj1 hj2)
        simpa using this
      · intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hDl _ (rho_mem_labelSet hj2 (by norm_num))
        · exact hDl _ (eta_mem_labelSet hj1 hj2 (by norm_num))
      · simpa using hFS _ (hfacing j hj2).1
      · intro w hw
        simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        subst hw
        exact rail_avoids_of_inv_eq R.toRailPoints hR hj1 hj2 (rG j hj1 hj2)
    · refine ⟨[R.dart (rho (j - 1) 2), R.dart (eta j 2)], rfl, ?_, ?_, ?_, ?_⟩
      · have := rail_strandStep_of_inv_eq hpre R.toRailPoints hj1 hj2 (rF j hj1 hj2)
        simpa using this
      · intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hDl _ (rho_mem_labelSet (by omega) (by norm_num))
        · exact hDl _ (eta_mem_labelSet hj1 hj2 (by norm_num))
      · simpa using hFS _ (hfacing (j - 1) (by omega)).2
      · intro w hw
        simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        subst hw
        exact rail_avoids_of_inv_eq R.toRailPoints hR hj1 hj2 (rF j hj1 hj2)
  exact not_isReturningPath_of_local hX hX' rfl rfl rfl rfl hperm hDrot hrot hDint hS hS'
    hfilt hsl hsl'' (fun d hd hdD => rail_mem_facingDarts_of_mem_darts hpre R.toRailPoints hSs hR
      hd hdD) hB hpair hW hret

end StaggeredRail


end TripleData

end ClusterAlgebras

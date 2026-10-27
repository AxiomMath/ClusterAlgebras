/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.TripleMoves
public import ClusterAlgebras.Plabic.ClosedStrands

/-!
# Strand paths along rails

A rail (aligned, closed aligned or staggered) along a simple strand path `P = (e₁, …, e_m)` on the
side `ζ` follows `P`: its points `x₀, …, x_N` are consecutive interior points of `P`, and its named
darts are the darts of `P` entering and leaving them. The push-off and the two combings replace the
rotation at the points of the rail; the strand path `P` is then replaced by a simple strand path of
the new diagram with the same ends, and its `ζ` list changes only in the block of the rail.

## Main results

* `ClusterAlgebras.TripleData.RailPoints.IsAlong.exists_pass`: a rail along a strand path follows
  it.

## Implementation notes

* Positions in lists are `0`-indexed, as in `ClusterAlgebras.Plabic.MinimalTriple`: the
  interior point `z_{l+1}` of a strand path `P` is `v(P[l]̄)`, and the `ζ` list `(λ₀, λ₁, …)` is
  `sideList ζ P`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset RailLabel

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

/-! ### Entries of the side lists -/

/-- Entries of a list built from blocks of length two. -/
private theorem getElem?_flatMap_two {α β : Type*} (f : α → List β)
    (hf : ∀ x, (f x).length = 2) :
    ∀ (L : List α) (u j : ℕ), j < 2 → (L.flatMap f)[2 * u + j]? = L[u]?.bind fun x => (f x)[j]?
  | [], u, j, _ => by simp
  | x :: L, 0, j, hj => by
    rw [List.flatMap_cons, List.getElem?_append_left (by rw [hf]; omega)]
    simp
  | x :: L, u + 1, j, hj => by
    rw [List.flatMap_cons, List.getElem?_append_right (by rw [hf]; omega), hf,
      show 2 * (u + 1) + j - 2 = 2 * u + j by omega, getElem?_flatMap_two f hf L u j hj]
    simp

omit [Fintype H] [DecidableEq H] in
private theorem length_flatMap_two {α β : Type*} (f : α → List β) (hf : ∀ x, (f x).length = 2) :
    ∀ L : List α, (L.flatMap f).length = 2 * L.length
  | [] => by simp
  | x :: L => by
    rw [List.flatMap_cons, List.length_append, hf, length_flatMap_two f hf L, List.length_cons]
    ring

omit [Fintype H] [DecidableEq H] in
/-- The `ζ` list of `(e₁, …, e_m)` has `2(m - 1)` entries. -/
private theorem length_sideList (ζ : StrandSide) (P : List H) :
    (X.sideList ζ P).length = 2 * (P.length - 1) := by
  cases ζ <;>
  · simp only [sideList]
    rw [length_flatMap_two _ (fun x => by simp [sideDarts])]
    simp

omit [Fintype H] [DecidableEq H] in
/-- The entries of the right list: `λ_{2u+k} = σ^{k+1}(ē_{u+1})` (`0`-indexed `P[u]`). -/
private theorem getElem?_sideList_right {P : List H} {u k : ℕ} (hk : k < 2)
    (hu : u + 2 ≤ P.length) :
    (X.sideList .right P)[2 * u + k]? = some ((X.rot ^ (k + 1)) (X.inv (P[u]'(by omega)))) := by
  simp only [sideList]
  rw [getElem?_flatMap_two _ (fun x => by simp [sideDarts]) _ u k hk,
    List.getElem?_eq_getElem (by simp; omega), List.getElem_dropLast]
  interval_cases k <;> simp [sideDarts, pow_two]

omit [Fintype H] [DecidableEq H] in
/-- The entries of the left list: `λ_{2u+k} = σ^{k+4}(ē_{m-1-u})` (`0`-indexed
`P[m - 2 - u]`). -/
private theorem getElem?_sideList_left {P : List H} {u k : ℕ} (hk : k < 2) (hu : u + 2 ≤ P.length) :
    (X.sideList .left P)[2 * u + k]? =
      some ((X.rot ^ (k + 4)) (X.inv (P[P.length - 2 - u]'(by omega)))) := by
  simp only [sideList]
  have e : P.dropLast.reverse[u]? = some (P[P.length - 2 - u]'(by omega)) := by
    rw [List.getElem?_reverse (by simp; omega)]
    simp only [List.length_dropLast, List.getElem?_dropLast]
    rw [if_pos (by omega), show P.length - 1 - 1 - u = P.length - 2 - u by omega,
      List.getElem?_eq_getElem (by omega)]
  rw [getElem?_flatMap_two _ (fun x => by simp [sideDarts]) _ u k hk, e]
  interval_cases k <;> simp [sideDarts]

/-! ### Strand paths -/

/-- In a strand path, `σ³(ē_l) = e_{l+1}` (`0`-indexed). -/
private theorem rot_pow_three_inv_getElem {P : List H} (hP : X.IsStrandPath P) {l : ℕ}
    (hl : l + 1 < P.length) : (X.rot ^ 3) (X.inv P[l]) = P[l + 1] :=
  (((X.isStrandPath_iff_getElem.1 hP).2.2 l hl).2).symm

/-- In a strand path, `v(ē_l)` is a triple point for `l < m` (`0`-indexed). -/
private theorem not_isBoundaryVertex_inv_getElem {P : List H} (hP : X.IsStrandPath P) {l : ℕ}
    (hl : l + 1 < P.length) : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[l])) :=
  ((X.isStrandPath_iff_getElem.1 hP).2.2 l hl).1

omit [Fintype H] [DecidableEq H] in
private theorem rot_pow_four_eq (d : H) : (X.rot ^ 4) d = X.rot ((X.rot ^ 3) d) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

/-- Two darts of a simple strand path's interior points at the same vertex have the same index. -/
private theorem eq_of_vertexOf_inv_eq {P : List H} (hP : X.IsSimpleStrandPath P) {l l' : ℕ}
    (hl : l + 1 < P.length) (hl' : l' + 1 < P.length)
    (h : X.vertexOf (X.inv P[l]) = X.vertexOf (X.inv P[l'])) : l = l' := by
  have hnd := hP.nodup
  simp only [interiorPoints] at hnd
  have e1 : (P.dropLast.map fun e => X.vertexOf (X.inv e))[l]'(by simp; omega) =
      X.vertexOf (X.inv P[l]) := by simp
  have e2 : (P.dropLast.map fun e => X.vertexOf (X.inv e))[l']'(by simp; omega) =
      X.vertexOf (X.inv P[l']) := by simp
  exact (hnd.getElem_inj_iff).1 (by rw [e1, e2, h])

/-! ### A rail along a strand path follows it -/

namespace RailPoints

variable {p q : ℕ} {R : X.RailPoints p q}

private theorem dart_rho (R : X.RailPoints p q) (j k : ℕ) :
    R.dart (RailLabel.rho j k) = (X.rot ^ k) (R.rho j) :=
  rfl

private theorem dart_eta (R : X.RailPoints p q) (j k : ℕ) :
    R.dart (RailLabel.eta j k) = (X.rot ^ k) (R.eta j) :=
  rfl

private theorem getElem?_facingDarts (R : X.RailPoints p q) {i : ℕ} (hi : i < 2 * (p + 1)) :
    R.facingDarts[i]? = some (R.dart (RailLabel.rho (i / 2) (i % 2 + 1))) := by
  simp [facingDarts, hi]

/-- **A rail along a strand path follows it**, right side: if a rail with points `x₀, …, x_p` is
along the simple strand path `P = (e₁, …, e_m)` on the right, there is `c` with `x_j = z_{c+j+1}`,
`ρ_{j,0} = ē_{c+j+1}` and `ρ_{j,3} = e_{c+j+2}` (`0`-indexed `P[c + j]`, `P[c + j + 1]`) for every
`j ∈ [0, p]`, and the block `(ρ_{0,1}, …, ρ_{p,2})` starts at the entry `2c` of the right list. -/
theorem IsAlong.exists_right {P : List H} (hP : X.IsSimpleStrandPath P)
    (hR : R.IsAlong P .right) :
    ∃ c, ∃ _ : c + p + 2 ≤ P.length, (∃ t, X.sideList .right P =
      (X.sideList .right P).take (2 * c) ++ R.facingDarts ++ t) ∧
      ∀ j (hj : j ≤ p), R.rho j = X.inv (P[c + j]'(by omega)) ∧
        R.dart (RailLabel.rho j 3) = P[c + j + 1]'(by omega) := by
  obtain ⟨s, t, hst⟩ := hR.1
  have hlen := length_sideList (X := X) .right P
  have hlen' : s.length + 2 * (p + 1) + t.length = 2 * (P.length - 1) := by
    rw [← hlen, ← hst]
    simp
    omega
  have hentry : ∀ i, i < 2 * (p + 1) →
      (X.sideList .right P)[s.length + i]? = some (R.dart (RailLabel.rho (i / 2) (i % 2 + 1))) := by
    intro i hi
    rw [← hst, List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simp; omega), getElem?_facingDarts R hi]
  obtain ⟨c, hc⟩ : ∃ c, s.length = 2 * c := by
    rcases Nat.even_or_odd' s.length with ⟨u, hu | hu⟩
    · exact ⟨u, hu⟩
    exfalso
    have h1 := hentry 0 (by omega)
    have h2 := hentry 1 (by omega)
    rw [hu, show 2 * u + 1 + 0 = 2 * u + 1 by omega,
      getElem?_sideList_right (by omega) (by omega)] at h1
    rw [hu, show 2 * u + 1 + 1 = 2 * (u + 1) + 0 by omega,
      getElem?_sideList_right (by omega) (by omega)] at h2
    simp only [Option.some_inj, Nat.zero_div, Nat.zero_mod, zero_add, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceAdd] at h1 h2
    have hv1 := congrArg X.vertexOf h1
    have hv2 := congrArg X.vertexOf h2
    rw [X.vertexOf_rot_pow_apply, dart_rho, X.vertexOf_rot_pow_apply] at hv1 hv2
    have := eq_of_vertexOf_inv_eq hP (l := u) (l' := u + 1) (by omega) (by omega)
      (hv1.trans hv2.symm)
    omega
  refine ⟨c, by omega, ⟨t, ?_⟩, fun j hj => ?_⟩
  · have : (X.sideList .right P).take (2 * c) = s := by
      rw [← hst, ← hc, List.append_assoc, List.take_left]
    rw [this, hst]
  have h := hentry (2 * j) (by omega)
  rw [hc, show 2 * c + 2 * j = 2 * (c + j) + 0 by omega,
    getElem?_sideList_right (by omega) (by omega)] at h
  simp only [Option.some_inj, show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega,
    zero_add, pow_one, dart_rho] at h
  have hρ : R.rho j = X.inv (P[c + j]'(by omega)) := (X.rot.injective h).symm
  refine ⟨hρ, ?_⟩
  rw [dart_rho, hρ, rot_pow_three_inv_getElem hP.isStrandPath]

/-- **A rail along a strand path follows it**, left side: if a rail with points `x₀, …, x_p` is
along the simple strand path `P = (e₁, …, e_m)` on the left, there is `c` with `x_j = z_{c-j+1}`,
`ρ_{j,0} = e_{c-j+2}` and `ρ_{j,3} = ē_{c-j+1}` (`0`-indexed `P[c - j + 1]`, `P[c - j]`) for every
`j ∈ [0, p]`, and the block `(ρ_{0,1}, …, ρ_{p,2})` starts at the entry `2(m - 2 - c)` of the left
list. -/
theorem IsAlong.exists_left (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsSimpleStrandPath P) (hR : R.IsAlong P .left) :
    ∃ c, ∃ _ : p ≤ c ∧ c + 2 ≤ P.length, (∃ t, X.sideList .left P =
      (X.sideList .left P).take (2 * (P.length - 2 - c)) ++ R.facingDarts ++ t) ∧
      ∀ j (hj : j ≤ p), R.rho j = P[c - j + 1]'(by omega) ∧
        R.dart (RailLabel.rho j 3) = X.inv (P[c - j]'(by omega)) := by
  obtain ⟨s, t, hst⟩ := hR.1
  have hlen := length_sideList (X := X) .left P
  have hlen' : s.length + 2 * (p + 1) + t.length = 2 * (P.length - 1) := by
    rw [← hlen, ← hst]
    simp
    omega
  have hentry : ∀ i, i < 2 * (p + 1) →
      (X.sideList .left P)[s.length + i]? = some (R.dart (RailLabel.rho (i / 2) (i % 2 + 1))) := by
    intro i hi
    rw [← hst, List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simp; omega), getElem?_facingDarts R hi]
  obtain ⟨v, hv⟩ : ∃ v, s.length = 2 * v := by
    rcases Nat.even_or_odd' s.length with ⟨u, hu | hu⟩
    · exact ⟨u, hu⟩
    exfalso
    have h1 := hentry 0 (by omega)
    have h2 := hentry 1 (by omega)
    rw [hu, show 2 * u + 1 + 0 = 2 * u + 1 by omega,
      getElem?_sideList_left (by omega) (by omega)] at h1
    rw [hu, show 2 * u + 1 + 1 = 2 * (u + 1) + 0 by omega,
      getElem?_sideList_left (by omega) (by omega)] at h2
    simp only [Option.some_inj, Nat.zero_div, Nat.zero_mod, zero_add, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceAdd] at h1 h2
    have hv1 := congrArg X.vertexOf h1
    have hv2 := congrArg X.vertexOf h2
    rw [X.vertexOf_rot_pow_apply, dart_rho, X.vertexOf_rot_pow_apply] at hv1 hv2
    have := eq_of_vertexOf_inv_eq hP (l := P.length - 2 - u) (l' := P.length - 2 - (u + 1))
      (by omega) (by omega) (hv1.trans hv2.symm)
    omega
  refine ⟨P.length - 2 - v, ⟨by omega, by omega⟩, ⟨t, ?_⟩, fun j hj => ?_⟩
  · have : (X.sideList .left P).take (2 * (P.length - 2 - (P.length - 2 - v))) = s := by
      rw [show P.length - 2 - (P.length - 2 - v) = v by omega, ← hst, ← hv, List.append_assoc,
        List.take_left]
    rw [this, hst]
  have h := hentry (2 * j) (by omega)
  rw [hv, show 2 * v + 2 * j = 2 * (v + j) + 0 by omega,
    getElem?_sideList_left (by omega) (by omega)] at h
  simp only [Option.some_inj, show 2 * j / 2 = j by omega, show 2 * j % 2 = 0 by omega,
    zero_add, pow_one, dart_rho] at h
  have hidx : P.length - 2 - (v + j) = P.length - 2 - v - j := by omega
  have hl : P.length - 2 - v - j + 1 < P.length := by omega
  have hρ : R.rho j = P[P.length - 2 - v - j + 1] := by
    rw [rot_pow_four_eq] at h
    rw [← rot_pow_three_inv_getElem hP.isStrandPath hl]
    have := (X.rot.injective h).symm
    simp only [hidx] at this
    exact this
  refine ⟨by simp only [hρ], ?_⟩
  rw [dart_rho, hρ, ← rot_pow_three_inv_getElem hP.isStrandPath hl,
    hX.rot_pow_three_rot_pow_three (not_isBoundaryVertex_inv_getElem hP.isStrandPath hl)]

/-- **A rail along a strand path follows it**: if a rail with points `x₀, …, x_p` is along the
simple strand path `P = (e₁, …, e_m)` on the side `ζ`, then every `x_j` is an interior point
`z_{l+1} = v(ē_{l+1})` of `P` (`0`-indexed `l`, `ē_{l+1} = P[l]̄`), with `ρ_{j,0} = ē_{l+1}` and
`ρ_{j,3} = e_{l+2}` if `ζ` is right, and `ρ_{j,0} = e_{l+2}` and `ρ_{j,3} = ē_{l+1}` if `ζ` is
left. -/
@[cluster_algebras "lem_rail_along_pass"]
theorem IsAlong.exists_pass (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsSimpleStrandPath P) {ζ : StrandSide} (hR : R.IsAlong P ζ) (j : ℕ) (hj : j ≤ p) :
    ∃ l, ∃ hl : l + 1 < P.length,
      X.vertexOf (R.rho j) = X.vertexOf (X.inv P[l]) ∧
      (ζ = .right → R.rho j = X.inv P[l] ∧ R.dart (RailLabel.rho j 3) = P[l + 1]) ∧
      (ζ = .left → R.rho j = P[l + 1] ∧ R.dart (RailLabel.rho j 3) = X.inv P[l]) := by
  cases ζ with
  | right =>
    obtain ⟨c, hc, -, h⟩ := hR.exists_right hP
    obtain ⟨h1, h2⟩ := h j hj
    exact ⟨c + j, by omega, by rw [h1], fun _ => ⟨h1, h2⟩, fun h => absurd h (by decide)⟩
  | left =>
    obtain ⟨c, ⟨hpc, hc⟩, -, h⟩ := hR.exists_left hX hP
    obtain ⟨h1, h2⟩ := h j hj
    refine ⟨c - j, by omega, ?_, fun h => absurd h (by decide), fun _ => ⟨h1, h2⟩⟩
    rw [h1, ← rot_pow_three_inv_getElem hP.isStrandPath (by omega), X.vertexOf_rot_pow_apply]

end RailPoints

/-! ### Replacing the rotation along a stretch of a strand path -/

omit [Fintype H] [DecidableEq H] in
private theorem getElem_idx {α : Type*} (l : List α) {i j : ℕ} (h : i = j) (hi : i < l.length) :
    l[i] = l[j]'(h ▸ hi) := by
  subst h
  rfl

omit [Fintype H] [DecidableEq H] in
private theorem take_flatMap_two {α β : Type*} (f : α → List β) (hf : ∀ x, (f x).length = 2) :
    ∀ (L : List α) (k : ℕ), (L.flatMap f).take (2 * k) = (L.take k).flatMap f
  | [], k => by simp
  | x :: L, 0 => by simp
  | x :: L, k + 1 => by
    rw [List.flatMap_cons, List.take_append, List.take_of_length_le (by rw [hf]; omega), hf,
      show 2 * (k + 1) - 2 = 2 * k by omega, take_flatMap_two f hf L k, List.take_succ_cons,
      List.flatMap_cons]

omit [Fintype H] [DecidableEq H] in
private theorem drop_flatMap_two {α β : Type*} (f : α → List β) (hf : ∀ x, (f x).length = 2) :
    ∀ (L : List α) (k : ℕ), (L.flatMap f).drop (2 * k) = (L.drop k).flatMap f
  | [], k => by simp
  | x :: L, 0 => by simp
  | x :: L, k + 1 => by
    rw [List.flatMap_cons, List.drop_append, List.drop_eq_nil_of_le (by rw [hf]; omega), hf,
      show 2 * (k + 1) - 2 = 2 * k by omega, drop_flatMap_two f hf L k, List.drop_succ_cons,
      List.nil_append]

omit [Fintype H] [DecidableEq H] in
private theorem length_sideDarts (ζ : StrandSide) (e : H) : (X.sideDarts ζ e).length = 2 := by
  cases ζ <;> rfl

omit [Fintype H] [DecidableEq H] in
private theorem take_append_append {α : Type*} {A B C : List α} {n : ℕ} (h : A.length = n) :
    (A ++ B ++ C).take n = A := by
  rw [List.append_assoc]
  exact List.take_left' h

omit [Fintype H] [DecidableEq H] in
private theorem drop_append_append {α : Type*} {A B C : List α} {n : ℕ}
    (h : A.length + B.length = n) : (A ++ B ++ C).drop n = C :=
  List.drop_left' (by rw [List.length_append, h])

omit [Fintype H] [DecidableEq H] in
private theorem filter_eq_singleton_filter {α : Type*} (p : α → Bool) {L : List α} {x : α}
    (h0 : L.head? = some x) (ht : ∀ y ∈ L.tail, p y = false) : L.filter p = [x].filter p := by
  cases L with
  | nil => simp at h0
  | cons y L =>
    simp only [List.head?_cons, Option.some_inj] at h0
    subst h0
    rw [List.filter_cons, List.filter_cons, List.filter_eq_nil_iff.2 (by simpa using ht)]
    simp

section Splice

variable {X' : TripleData H b} {D : Finset H}

private theorem mem_vertexOf_rot_pow (k : ℕ) (d : H) : (X.rot ^ k) d ∈ X.vertexOf d :=
  X.mem_vertexOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))

private theorem rot_pow_apply_of_disjoint (hrot : ∀ d ∉ D, X'.rot d = X.rot d) {d : H}
    (hd : Disjoint (X.vertexOf d) D) (k : ℕ) : (X'.rot ^ k) d = (X.rot ^ k) d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
    exact hrot _ (Finset.disjoint_left.1 hd (mem_vertexOf_rot_pow k d))

private theorem vertexOf_eq_of_disjoint (hrot : ∀ d ∉ D, X'.rot d = X.rot d) {d : H}
    (hd : Disjoint (X.vertexOf d) D) : X'.vertexOf d = X.vertexOf d := by
  ext e
  rw [X'.mem_vertexOf, X.mem_vertexOf]
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    rw [rot_pow_apply_of_disjoint hrot hd k]
    exact Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)
  · intro h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    rw [← rot_pow_apply_of_disjoint hrot hd k]
    exact Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)

omit [Fintype H] [DecidableEq H] in
private theorem isBoundaryVertex_congr (hbdry : X'.bdry = X.bdry) {v : Finset H} :
    X'.IsBoundaryVertex v ↔ X.IsBoundaryVertex v := by
  simp only [DiskMap.IsBoundaryVertex, hbdry]

private theorem strandStep_of_disjoint (hinv : X'.inv = X.inv) (hbdry : X'.bdry = X.bdry)
    (hrot : ∀ d ∉ D, X'.rot d = X.rot d) {e e' : H} (h : X.StrandStep e e')
    (hd : Disjoint (X.vertexOf (X.inv e)) D) : X'.StrandStep e e' := by
  refine ⟨?_, ?_⟩
  · unfold RunsToEndpoint
    rw [hinv, vertexOf_eq_of_disjoint hrot hd, isBoundaryVertex_congr hbdry]
    exact h.1
  · rw [hinv, rot_pow_apply_of_disjoint hrot hd]
    exact h.2

private theorem sideDarts_eq_of_disjoint (hinv : X'.inv = X.inv)
    (hrot : ∀ d ∉ D, X'.rot d = X.rot d) (ζ : StrandSide) {e : H}
    (hd : Disjoint (X.vertexOf (X.inv e)) D) : X'.sideDarts ζ e = X.sideDarts ζ e := by
  have h1 := rot_pow_apply_of_disjoint hrot hd 1
  rw [pow_one, pow_one] at h1
  cases ζ <;> simp only [sideDarts, hinv, h1, rot_pow_apply_of_disjoint hrot hd]

omit [Fintype H] [DecidableEq H] in
private theorem getElem_mem_dropLast {α : Type*} {l : List α} {i : ℕ} (hi : i + 1 < l.length) :
    l[i] ∈ l.dropLast := by
  rw [← List.getElem_dropLast (by simp; omega)]
  exact List.getElem_mem _

omit [Fintype H] [DecidableEq H] in
private theorem mem_dropLast_iff {α : Type*} {l : List α} {x : α} :
    x ∈ l.dropLast ↔ ∃ i, ∃ hi : i + 1 < l.length, l[i] = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_dropLast] at hi
    exact ⟨i, by omega, (List.getElem_dropLast _).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by simp; omega, List.getElem_dropLast _⟩

/-- **Replacing the rotation along a stretch of a strand path.** Let `X'` have the darts,
involution, boundary and orientation of `X`, and a rotation agreeing with that of `X` outside `D`.
Let `P` be a simple strand path of `X` whose interior points `z_{s+1}, …, z_{s+N+1}` (`0`-indexed
`s, …, s + N`) lie in `D`, the others and the ends avoiding `D`. Let `P'` agree with `P` up to
index `s`, and from index `s + K` on with `P` shifted by `N + 1 - K`, and let its interior points
of index `s, …, s + K - 1` be new pairwise distinct triple points of `X'` inside `D`, joined by
strand steps of `X'`. Then `P'` is a simple strand path of `X'` with the ends of `P`, the darts of
`P` outside `D`, and side lists obtained by replacing the block of the points in `D`. -/
private theorem splice (hinv : X'.inv = X.inv)
    (hbdry : X'.bdry = X.bdry) (hout : X'.isOut = X.isOut) (hrot : ∀ d ∉ D, X'.rot d = X.rot d)
    {P P' : List H} (hP : X.IsSimpleStrandPath P) {s N K : ℕ} (hK : 1 ≤ K)
    (hs : s + N + 2 ≤ P.length) (hlen : P'.length + N + 1 = P.length + K)
    (hpre : ∀ i (hi : i ≤ s), P'[i]'(by omega) = P[i]'(by omega))
    (hsuf : ∀ i (hi : s + K ≤ i) (hi' : i < P'.length), P'[i] = P[i + N + 1 - K]'(by omega))
    (hstart : Disjoint (X.vertexOf (P[0]'(by omega))) D)
    (hend : Disjoint (X.vertexOf (X.inv (P[P.length - 1]'(by omega)))) D)
    (hold : ∀ l (hl : l + 1 < P.length), (l < s ∨ s + N < l) →
      Disjoint (X.vertexOf (X.inv P[l])) D)
    (hin : ∀ l (_hl : s ≤ l) (hl' : l ≤ s + N), X.vertexOf (X.inv (P[l]'(by omega))) ⊆ D)
    (hnewstep : ∀ t (ht : s ≤ t) (ht' : t < s + K),
      (X'.rot ^ 3) (X.inv (P'[t]'(by omega))) = P'[t + 1]'(by omega))
    (hnewD : ∀ t (_ht : s ≤ t) (ht' : t < s + K), X'.vertexOf (X.inv (P'[t]'(by omega))) ⊆ D)
    (hnewbd : ∀ t (_ht : s ≤ t) (ht' : t < s + K),
      ¬X'.IsBoundaryVertex (X'.vertexOf (X.inv (P'[t]'(by omega)))))
    (hnewinj : ∀ t (_ht : s ≤ t) (ht' : t < s + K) t' (_hu : s ≤ t') (hu' : t' < s + K),
      X'.vertexOf (X.inv (P'[t]'(by omega))) = X'.vertexOf (X.inv (P'[t']'(by omega))) → t = t')
    (hnewdart : ∀ t (_ht : s < t) (ht' : t < s + K),
      P'[t]'(by omega) ∉ X.bdry ∧ X.isOut (P'[t]'(by omega)) = true) :
    X'.IsSimpleStrandPath P' ∧ P'.head? = P.head? ∧ P'.getLast? = P.getLast? ∧
      P'.filter (· ∉ D) = P.filter (· ∉ D) ∧
      X'.sideList .right P' = (X.sideList .right P).take (2 * s) ++
        ((P'.drop s).take K).flatMap (X'.sideDarts .right) ++
        (X.sideList .right P).drop (2 * (s + N + 1)) ∧
      X'.sideList .left P' = (X.sideList .left P).take (2 * (P.length - 2 - (s + N))) ++
        ((P'.drop s).take K).reverse.flatMap (X'.sideDarts .left) ++
        (X.sideList .left P).drop (2 * (P.length - 1 - s)) := by
  have hPg := X.isStrandPath_iff_getElem.1 hP.isStrandPath
  have hstepOld : ∀ l (hl : l + 1 < P.length), X.StrandStep P[l] (P[l + 1]) := hPg.2.2
  have hwold : ∀ t (ht : t + 1 < P'.length), (t < s ∨ s + K ≤ t) →
      ∃ l, ∃ hl : l + 1 < P.length, (l < s ∨ s + N < l) ∧ (t < s → l = t) ∧
        (s + K ≤ t → l = t + N + 1 - K) ∧ P'[t] = P[l] := by
    intro t ht h
    rcases h with h | h
    · exact ⟨t, by omega, Or.inl h, fun _ => rfl, fun h' => by omega, hpre t (by omega)⟩
    · exact ⟨t + N + 1 - K, by omega, Or.inr (by omega), fun h' => by omega, fun _ => rfl,
        hsuf t h (by omega)⟩
  have hSP : X'.IsStrandPath P' := by
    rw [isStrandPath_iff_getElem]
    refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
    · intro h
      rw [h, List.length_nil] at hlen
      omega
    · rw [hbdry, hout]
      by_cases h1 : t ≤ s
      · rw [hpre t h1]
        exact hPg.2.1 t (by omega)
      by_cases h2 : t < s + K
      · exact hnewdart t (by omega) h2
      · rw [hsuf t (by omega) ht]
        exact hPg.2.1 _ (by omega)
    · by_cases h2 : s ≤ t ∧ t < s + K
      · refine ⟨?_, ?_⟩
        · unfold RunsToEndpoint
          rw [hinv]
          exact hnewbd t h2.1 h2.2
        · rw [hinv]
          exact (hnewstep t h2.1 h2.2).symm
      by_cases h1 : t < s
      · rw [hpre t (by omega), hpre (t + 1) (by omega)]
        exact strandStep_of_disjoint hinv hbdry hrot (hstepOld t (by omega))
          (hold t (by omega) (Or.inl h1))
      · rw [hsuf t (by omega) (by omega), hsuf (t + 1) (by omega) ht,
          getElem_idx P (show t + 1 + N + 1 - K = t + N + 1 - K + 1 by omega)]
        exact strandStep_of_disjoint hinv hbdry hrot (hstepOld _ (by omega))
          (hold _ (by omega) (Or.inr (by omega)))
  have hwold' : ∀ t (ht : t + 1 < P'.length), (t < s ∨ s + K ≤ t) →
      ∃ l, ∃ hl : l + 1 < P.length, (l < s ∨ s + N < l) ∧ (t < s → l = t) ∧
        (s + K ≤ t → l = t + N + 1 - K) ∧
        X'.vertexOf (X'.inv P'[t]) = X.vertexOf (X.inv P[l]) ∧
        Disjoint (X.vertexOf (X.inv P[l])) D := by
    intro t ht h
    obtain ⟨l, hl, h1, h2, h3, h4⟩ := hwold t ht h
    refine ⟨l, hl, h1, h2, h3, ?_, hold l hl h1⟩
    rw [h4, hinv, vertexOf_eq_of_disjoint hrot (hold l hl h1)]
  have hnew_ne_old : ∀ t (ht : s ≤ t) (ht' : t < s + K) {d : H}, Disjoint (X.vertexOf d) D →
      X'.vertexOf (X.inv (P'[t]'(by omega))) ≠ X.vertexOf d := by
    intro t ht ht' d hd h
    have hm := X'.self_mem_vertexOf (X.inv (P'[t]'(by omega)))
    rw [h] at hm
    exact Finset.disjoint_left.1 hd hm (hnewD t ht ht' (X'.self_mem_vertexOf _))
  have hold_mem : ∀ l (hl : l + 1 < P.length), X.vertexOf (X.inv P[l]) ∈ X.interiorPoints P :=
    fun l hl => List.mem_map.2 ⟨P[l], getElem_mem_dropLast hl, rfl⟩
  have hnodup : (X'.interiorPoints P').Nodup := by
    rw [List.nodup_iff_getElem?_ne_getElem?]
    intro i j hij hj
    simp only [interiorPoints, List.length_map, List.length_dropLast] at hj
    simp only [interiorPoints, List.getElem?_map, List.getElem?_dropLast,
      if_pos (show i < P'.length - 1 by omega), if_pos hj,
      List.getElem?_eq_getElem (show i < P'.length by omega),
      List.getElem?_eq_getElem (show j < P'.length by omega), Option.map_some, ne_eq,
      Option.some_inj]
    intro h
    by_cases hi' : s ≤ i ∧ i < s + K
    · by_cases hj' : s ≤ j ∧ j < s + K
      · rw [hinv] at h
        exact absurd (hnewinj i hi'.1 hi'.2 j hj'.1 hj'.2 h) (by omega)
      · obtain ⟨l, hl, hl1, -, -, hv, hd⟩ := hwold' j (by omega) (by omega)
        rw [hv, hinv] at h
        exact hnew_ne_old i hi'.1 hi'.2 hd h
    · obtain ⟨l, hl, hl1, hl2, hl3, hv, hd⟩ := hwold' i (by omega) (by omega)
      by_cases hj' : s ≤ j ∧ j < s + K
      · rw [hv, hinv] at h
        exact hnew_ne_old j hj'.1 hj'.2 hd h.symm
      · obtain ⟨l', hl', hl1', hl2', hl3', hv', hd'⟩ := hwold' j (by omega) (by omega)
        rw [hv, hv'] at h
        have := eq_of_vertexOf_inv_eq hP hl hl' h
        omega
  have hP'0 : P'[0]'(by omega) = P[0]'(by omega) := hpre 0 (Nat.zero_le _)
  have hP'last : P'[P'.length - 1]'(by omega) = P[P.length - 1]'(by omega) := by
    rw [hsuf _ (by omega) (by omega)]
    exact getElem_idx P (by omega) _
  have hstartP' : X'.pathStart P' = X.vertexOf (P[0]'(by omega)) := by
    rw [X'.pathStart_of_head?
        (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]), hP'0,
      vertexOf_eq_of_disjoint hrot hstart]
  have hendP' : X'.pathEnd P' = X.vertexOf (X.inv (P[P.length - 1]'(by omega))) := by
    rw [X'.pathEnd_of_getLast?
        (by rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]), hP'last,
      hinv, vertexOf_eq_of_disjoint hrot hend]
  have hnotint : ∀ {d : H}, Disjoint (X.vertexOf d) D → X.vertexOf d ∉ X.interiorPoints P →
      X.vertexOf d ∉ X'.interiorPoints P' := by
    intro d hd hni hm
    obtain ⟨e, he, hev⟩ := List.mem_map.1 hm
    obtain ⟨t, ht, rfl⟩ := mem_dropLast_iff.1 he
    by_cases ht' : s ≤ t ∧ t < s + K
    · rw [hinv] at hev
      exact hnew_ne_old t ht'.1 ht'.2 hd hev
    · obtain ⟨l, hl, -, -, -, hv, -⟩ := hwold' t ht (by omega)
      rw [hv] at hev
      exact hni (hev ▸ hold_mem l hl)
  have hstartP : X.pathStart P = X.vertexOf (P[0]'(by omega)) :=
    X.pathStart_of_head? (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)])
  have hendP : X.pathEnd P = X.vertexOf (X.inv (P[P.length - 1]'(by omega))) :=
    X.pathEnd_of_getLast? (by rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)])
  have hSSP : X'.IsSimpleStrandPath P' :=
    ⟨hSP, hnodup, hstartP' ▸ hnotint hstart (hstartP ▸ hP.pathStart_notMem),
      hendP' ▸ hnotint hend (hendP ▸ hP.pathEnd_notMem)⟩
  set A := P.take s with hAdef
  set B' := (P'.drop s).take K with hB'def
  set Bo := (P.drop s).take (N + 1) with hBodef
  set C := P.dropLast.drop (s + N + 1) with hCdef
  have hlA : A.length = s := by simp [hAdef]; omega
  have hlBo : Bo.length = N + 1 := by simp [hBodef]; omega
  have hlC : C.length = P.length - 2 - (s + N) := by simp [hCdef]; omega
  have hdl' : P'.dropLast = A ++ B' ++ C := by
    apply List.ext_getElem (by simp [hAdef, hB'def, hCdef]; omega)
    intro i h1 h2
    simp only [List.length_dropLast] at h1
    rw [List.getElem_dropLast]
    by_cases ha : i < s
    · rw [List.getElem_append_left (by simp [hAdef, hB'def]; omega),
        List.getElem_append_left (by simp [hAdef]; omega), List.getElem_take]
      exact hpre i (by omega)
    by_cases hb : i < s + K
    · rw [List.getElem_append_left (by simp [hAdef, hB'def]; omega),
        List.getElem_append_right (by simp [hAdef]; omega)]
      simp only [hB'def, List.getElem_take, List.getElem_drop, hlA]
      exact getElem_idx P' (by omega) _
    · rw [List.getElem_append_right (by simp [hAdef, hB'def]; omega)]
      simp only [hCdef, List.getElem_drop, List.getElem_dropLast, List.length_append, hlA,
        hB'def, List.length_take, List.length_drop]
      rw [hsuf i (by omega) (by omega)]
      exact getElem_idx P (by omega) _
  have hdl : P.dropLast = A ++ Bo ++ C := by
    apply List.ext_getElem (by simp [hAdef, hBodef, hCdef]; omega)
    intro i h1 h2
    simp only [List.length_dropLast] at h1
    rw [List.getElem_dropLast]
    by_cases ha : i < s
    · rw [List.getElem_append_left (by simp [hAdef, hBodef]; omega),
        List.getElem_append_left (by simp [hAdef]; omega), List.getElem_take]
    by_cases hb : i < s + N + 1
    · rw [List.getElem_append_left (by simp [hAdef, hBodef]; omega),
        List.getElem_append_right (by simp [hAdef]; omega)]
      simp only [hBodef, List.getElem_take, List.getElem_drop, hlA]
      exact getElem_idx P (by omega) _
    · rw [List.getElem_append_right (by simp [hAdef, hBodef]; omega)]
      simp only [hCdef, List.getElem_drop, List.getElem_dropLast, List.length_append, hlA, hlBo]
      exact getElem_idx P (by omega) _
  have hAx : ∀ ζ, ∀ x ∈ A, X'.sideDarts ζ x = X.sideDarts ζ x := fun ζ x hx => by
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [hAdef, List.length_take] at ht
    simp only [hAdef, List.getElem_take]
    exact sideDarts_eq_of_disjoint hinv hrot ζ (hold t (by omega) (Or.inl (by omega)))
  have hCx : ∀ ζ, ∀ x ∈ C, X'.sideDarts ζ x = X.sideDarts ζ x := fun ζ x hx => by
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [hCdef, List.length_drop, List.length_dropLast] at ht
    simp only [hCdef, List.getElem_drop, List.getElem_dropLast]
    exact sideDarts_eq_of_disjoint hinv hrot ζ (hold _ (by omega) (Or.inr (by omega)))
  have hlf : ∀ (ζ : StrandSide) (L : List H), (L.flatMap (X.sideDarts ζ)).length = 2 * L.length :=
    fun ζ L => length_flatMap_two _ (length_sideDarts ζ) L
  have hlfr : ∀ (ζ : StrandSide) (L : List H),
      (L.reverse.flatMap (X.sideDarts ζ)).length = 2 * L.length :=
    fun ζ L => by rw [hlf, List.length_reverse]
  refine ⟨hSSP, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by omega), hP'0]
  · rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by omega), hP'last]
  · have hne' : P' ≠ [] := hSP.ne_nil
    have hne : P ≠ [] := hP.isStrandPath.ne_nil
    have e1 : P' = A ++ B' ++ C ++ [P[P.length - 1]'(by omega)] := by
      rw [← hdl', ← hP'last]
      conv_lhs => rw [← List.dropLast_append_getLast hne']
      rw [List.getLast_eq_getElem]
    have e2 : P = A ++ Bo ++ C ++ [P[P.length - 1]'(by omega)] := by
      rw [← hdl]
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      rw [List.getLast_eq_getElem]
    have hBo : Bo.filter (fun x => decide (x ∉ D)) =
        [P[s]'(by omega)].filter (fun x => decide (x ∉ D)) := by
      apply filter_eq_singleton_filter
      · rw [hBodef, List.head?_take, if_neg (show N + 1 ≠ 0 by omega), List.head?_drop,
          List.getElem?_eq_getElem (show s < P.length by omega)]
      · intro y hy
        obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hy
        simp only [List.length_tail, hlBo] at ht
        simp only [List.getElem_tail, hBodef, List.getElem_take, List.getElem_drop,
          decide_eq_false_iff_not, not_not]
        rw [← getElem_idx P (show s + t + 1 = s + (t + 1) by omega) (by omega),
          ← rot_pow_three_inv_getElem hP.isStrandPath (by omega)]
        exact hin (s + t) (by omega) (by omega) (mem_vertexOf_rot_pow 3 _)
    have hB' : B'.filter (fun x => decide (x ∉ D)) =
        [P[s]'(by omega)].filter (fun x => decide (x ∉ D)) := by
      apply filter_eq_singleton_filter
      · rw [hB'def, List.head?_take, if_neg (show K ≠ 0 by omega), List.head?_drop,
          List.getElem?_eq_getElem (show s < P'.length by omega), hpre s le_rfl]
      · intro y hy
        obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hy
        simp only [List.length_tail, hB'def, List.length_take, List.length_drop] at ht
        simp only [List.getElem_tail, hB'def, List.getElem_take, List.getElem_drop,
          decide_eq_false_iff_not, not_not]
        rw [← getElem_idx P' (show s + t + 1 = s + (t + 1) by omega) (by omega),
          ← hnewstep (s + t) (by omega) (by omega)]
        exact hnewD (s + t) (by omega) (by omega) (mem_vertexOf_rot_pow 3 _)
    have hB : B'.filter (fun x => decide (x ∉ D)) = Bo.filter (fun x => decide (x ∉ D)) := by
      rw [hB', hBo]
    rw [e1]
    conv_rhs => rw [e2]
    simp only [List.filter_append, hB]
  · simp only [sideList]
    rw [hdl', hdl, List.flatMap_append, List.flatMap_append,
      List.flatMap_congr (hAx .right), List.flatMap_congr (hCx .right),
      take_flatMap_two _ (length_sideDarts .right), drop_flatMap_two _ (length_sideDarts .right),
      take_append_append hlA, drop_append_append (by rw [hlA, hlBo]; omega)]
  · have hold' : X.sideList .left P = C.reverse.flatMap (X.sideDarts .left) ++
        Bo.reverse.flatMap (X.sideDarts .left) ++ A.reverse.flatMap (X.sideDarts .left) := by
      simp only [sideList]
      rw [hdl]
      simp only [List.reverse_append, List.flatMap_append, List.append_assoc]
    have hnew' : X'.sideList .left P' = C.reverse.flatMap (X.sideDarts .left) ++
        B'.reverse.flatMap (X'.sideDarts .left) ++ A.reverse.flatMap (X.sideDarts .left) := by
      simp only [sideList]
      rw [hdl']
      simp only [List.reverse_append, List.flatMap_append, List.append_assoc]
      rw [List.flatMap_congr (fun x hx => hAx .left x (List.mem_reverse.1 hx)),
        List.flatMap_congr (fun x hx => hCx .left x (List.mem_reverse.1 hx))]
    rw [hnew', hold', take_append_append (by rw [hlfr, hlC]),
      drop_append_append (by rw [hlfr, hlfr, hlC, hlBo]; omega)]

end Splice

/-! ### Prescribed rotations along a rail -/

section Prescribed

variable {σ : Equiv.Perm H} {D : Finset H} {hD : ∀ d, σ d ∈ D ↔ d ∈ D} {cs : List (List H)}

omit [Fintype H] in
private theorem prescribedRot_pow_tuple (hnd : cs.flatten.Nodup) (hsub : ∀ x ∈ cs.flatten, x ∈ D)
    {T : ℕ → H} (hl : (List.range 6).map T ∈ cs) (a k : ℕ) (ha : a < 6) :
    (prescribedRot σ D hD cs ^ k) (T a) = T ((a + k) % 6) := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt ha]
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    have := prescribedRot_apply_getElem (hD := hD) hnd hsub hl ((a + k) % 6)
      (by simp only [List.length_map, List.length_range]; omega)
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range] at this
    rw [this]
    congr 1
    omega

omit [Fintype H] in
private theorem prescribedRot_sameCycle_tuple (hnd : cs.flatten.Nodup)
    (hsub : ∀ x ∈ cs.flatten, x ∈ D) {T : ℕ → H} (hl : (List.range 6).map T ∈ cs) {a : ℕ}
    (ha : a < 6) {e : H} : (prescribedRot σ D hD cs).SameCycle (T a) e ↔ ∃ a' < 6, T a' = e := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨(a + (k % 6).toNat) % 6, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← prescribedRot_pow_tuple (hD := hD) hnd hsub hl a _ ha]
    have hk : k = (k % 6).toNat + 6 * (k / 6) := by omega
    conv_rhs => rw [hk]
    rw [zpow_add, zpow_mul, Equiv.Perm.mul_apply, zpow_natCast]
    congr 1
    have h6 : ((prescribedRot σ D hD cs) ^ (6 : ℤ)) (T a) = T a := by
      rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast,
        prescribedRot_pow_tuple hnd hsub hl a 6 ha]
      congr 1
      omega
    exact (Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h6 _).symm
  · rintro ⟨a', ha', rfl⟩
    refine ⟨((a' + 6 - a : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast, prescribedRot_pow_tuple hnd hsub hl a _ ha]
    congr 1
    omega

end Prescribed

omit [Fintype H] [DecidableEq H] in
private theorem getElem_splice_left {α : Type*} (P M C : List α) {s i : ℕ} (hs : s < P.length)
    (hi : i ≤ s) : (P.take (s + 1) ++ M ++ C)[i]'(by simp; omega) = P[i]'(by omega) := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
    List.getElem_take]

omit [Fintype H] [DecidableEq H] in
private theorem getElem_splice_mid {α : Type*} (P M C : List α) {s i : ℕ} (hs : s < P.length)
    (hi : s < i) (hi' : i < s + 1 + M.length) :
    (P.take (s + 1) ++ M ++ C)[i]'(by simp; omega) = M[i - s - 1]'(by omega) := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
  simp only [List.length_take]
  exact getElem_idx M (by omega) _

omit [Fintype H] [DecidableEq H] in
private theorem getElem_splice_right {α : Type*} (P M C : List α) {s i : ℕ} (hs : s < P.length)
    (hi : s + 1 + M.length ≤ i) (hi' : i < s + 1 + M.length + C.length) :
    (P.take (s + 1) ++ M ++ C)[i]'(by simp; omega) = C[i - s - 1 - M.length]'(by omega) := by
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.length_append, List.length_take]
  exact getElem_idx C (by omega) _

namespace RailPoints

variable {p q : ℕ}

/-- A vertex avoids the darts of the points of a rail iff it is none of these points. -/
private theorem disjoint_vertexOf_darts_iff (R : X.RailPoints p q) (d : H) :
    Disjoint (X.vertexOf d) R.darts ↔
      ∀ a ∈ pointSet p q, X.vertexOf d ≠ X.vertexOf (Sum.elim R.rho R.eta a) := by
  rw [darts, Finset.disjoint_biUnion_right]
  refine forall₂_congr fun a ha => ⟨fun h he => ?_, fun h => ?_⟩
  · rw [he] at h
    exact Finset.disjoint_left.1 h (X.self_mem_vertexOf _) (X.self_mem_vertexOf _)
  · rw [Finset.disjoint_left]
    intro x hx hx'
    exact h ((X.vertexOf_eq_of_mem hx).symm.trans (X.vertexOf_eq_of_mem hx'))

private theorem vertexOf_subset_darts (R : X.RailPoints p q) {a : ℕ ⊕ ℕ} (ha : a ∈ pointSet p q) :
    X.vertexOf (Sum.elim R.rho R.eta a) ⊆ R.darts :=
  Finset.subset_biUnion_of_mem (fun a => X.vertexOf (Sum.elim R.rho R.eta a)) ha

/-- The darts at the points of a rail are not in `B`. -/
private theorem notMem_bdry_of_mem_darts (R : X.RailPoints p q) {d : H} (hd : d ∈ R.darts) :
    d ∉ X.bdry := by
  obtain ⟨a, ha, hda⟩ := R.mem_darts.1 hd
  have hv := R.vertexOf_mem a ha
  rw [← X.vertexOf_eq_of_mem hda] at hv
  exact X.notMem_bdry_of_not_isBoundaryVertex (X.mem_internalVertices.1 hv).2

private theorem mem_pointSet_inl {j : ℕ} : Sum.inl j ∈ pointSet p q ↔ j ≤ p := by
  simp only [pointSet, Finset.inl_mem_disjSum, Finset.mem_range]
  omega

private theorem mem_pointSet_inr {j : ℕ} : Sum.inr j ∈ pointSet p q ↔ 1 ≤ j ∧ j ≤ q := by
  simp [pointSet]

/-- The vertices of a simple strand path away from the points `x_j` of a rail along it avoid the
darts of the rail. -/
private theorem disjoint_of_isAlong {R : X.RailPoints p q} {P : List H}
    (hP : X.IsSimpleStrandPath P) {ζ : StrandSide} (hR : R.IsAlong P ζ) {s : ℕ}
    (hx : ∀ j ≤ p, ∃ l, ∃ hl : l + 1 < P.length, s ≤ l ∧ l ≤ s + p ∧
      X.vertexOf (R.rho j) = X.vertexOf (X.inv P[l])) :
    (∀ l (hl : l + 1 < P.length), (l < s ∨ s + p < l) →
      Disjoint (X.vertexOf (X.inv P[l])) R.darts) ∧
    (∀ hP0 : 0 < P.length, Disjoint (X.vertexOf P[0]) R.darts) ∧
    (∀ hP0 : 0 < P.length, Disjoint (X.vertexOf (X.inv P[P.length - 1])) R.darts) := by
  have hmem : ∀ l (hl : l + 1 < P.length), X.vertexOf (X.inv P[l]) ∈ X.interiorPoints P :=
    fun l hl => List.mem_map.2 ⟨P[l], getElem_mem_dropLast hl, rfl⟩
  refine ⟨fun l hl hls => ?_, fun hP0 => ?_, fun hP0 => ?_⟩ <;>
    rw [disjoint_vertexOf_darts_iff] <;> rintro (j | j) ha
  · obtain ⟨l', hl', h1, h2, hv⟩ := hx j (mem_pointSet_inl.1 ha)
    intro h
    simp only [Sum.elim_inl] at h
    have := eq_of_vertexOf_inv_eq hP hl hl' (h.trans hv)
    omega
  · obtain ⟨h1, h2⟩ := mem_pointSet_inr.1 ha
    exact fun h => (hR.2 j h1 h2 _ (List.getElem_mem _)).2 (by simpa using h.symm)
  · obtain ⟨l', hl', h1, h2, hv⟩ := hx j (mem_pointSet_inl.1 ha)
    intro h
    simp only [Sum.elim_inl] at h
    have hs : X.pathStart P = X.vertexOf P[0] :=
      X.pathStart_of_head? (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hP0])
    exact hP.pathStart_notMem (hs ▸ h ▸ hv ▸ hmem l' hl')
  · obtain ⟨h1, h2⟩ := mem_pointSet_inr.1 ha
    exact fun h => (hR.2 j h1 h2 _ (List.getElem_mem _)).1 (by simpa using h.symm)
  · obtain ⟨l', hl', h1, h2, hv⟩ := hx j (mem_pointSet_inl.1 ha)
    intro h
    simp only [Sum.elim_inl] at h
    have he : X.pathEnd P = X.vertexOf (X.inv P[P.length - 1]) :=
      X.pathEnd_of_getLast? (by rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem])
    exact hP.pathEnd_notMem (he ▸ h ▸ hv ▸ hmem l' hl')
  · obtain ⟨h1, h2⟩ := mem_pointSet_inr.1 ha
    exact fun h => (hR.2 j h1 h2 _ (List.getElem_mem _)).2 (by simpa using h.symm)

end RailPoints

omit [Fintype H] [DecidableEq H] in
private theorem flatMap_two_ext {α γ β : Type*} (f : α → List β) (g : γ → List β) :
    ∀ (L : List α) (L' : List γ), L.length = L'.length →
      (∀ u (h1 : u < L.length) (h2 : u < L'.length), f L[u] = g L'[u]) →
      L.flatMap f = L'.flatMap g
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: L, y :: L', h, hfg => by
    have h0 := hfg 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [List.flatMap_cons, List.flatMap_cons, h0,
      flatMap_two_ext f g L L' (by simpa using h) fun u h1 h2 =>
        hfg (u + 1) (by simp; omega) (by simp; omega)]

/-- The diagram `X` with its rotation replaced by `σ'`. -/
private abbrev withRot (X : TripleData H b) (σ' : Equiv.Perm H) : TripleData H b :=
  { X with rot := σ' }

/-- **Strand paths along a rail, generically.** Let `R` be a rail along the simple strand path `P`
on side `ζ`, and let the rotation be replaced on the darts of `R` by tuples `cs`, among which are
`K ≥ 1` tuples `(T i 0, …, T i 5)` with `T i 3̄ = T (i + 1) 0`, `T 0 0 = ρ_{0,0}` and
`T (K - 1) 3 = ρ_{p,3}`. Then the new diagram has a simple strand path through these tuples, with
the ends and the darts outside `D` of `P`, whose `ζ` list replaces the block of `R` by the darts
`T i 1, T i 2`. -/
private theorem splice_rail (hX : X.IsPreTripleDiagram) {p q : ℕ} (R : X.RailPoints p q)
    {cs : List (List H)} (hnd : cs.flatten.Nodup) (hsub : ∀ x ∈ cs.flatten, x ∈ R.darts)
    {P : List H} (hP : X.IsSimpleStrandPath P) {ζ : StrandSide} (hR : R.IsAlong P ζ)
    {K : ℕ} (hK : 1 ≤ K) (T : ℕ → ℕ → H) (hT : ∀ i < K, (List.range 6).map (T i) ∈ cs)
    (hTinj : ∀ i < K, ∀ i' < K, ∀ a < 6, T i a = T i' 0 → i = i')
    (hchain : ∀ i, i + 1 < K → X.inv (T i 3) = T (i + 1) 0)
    (hstart : T 0 0 = R.rho 0) (hend : T (K - 1) 3 = R.dart (RailLabel.rho p 3))
    (hout : ∀ i, i + 1 < K → (X.isOut (T i 3) = true ↔ ζ = .right)) :
    ∃ P', (withRot X (prescribedRot X.rot R.darts R.rot_mem_darts_iff cs)).IsSimpleStrandPath P' ∧
      P'.length + p + 1 = P.length + K ∧ P'.head? = P.head? ∧ P'.getLast? = P.getLast? ∧
      P'.filter (· ∉ R.darts) = P.filter (· ∉ R.darts) ∧
      ∃ L₁ L₂, X.sideList ζ P = L₁ ++ R.facingDarts ++ L₂ ∧
        (withRot X (prescribedRot X.rot R.darts R.rot_mem_darts_iff cs)).sideList ζ P' =
          L₁ ++ (List.range K).flatMap (fun i => [T i 1, T i 2]) ++ L₂ := by
  set X' := withRot X (prescribedRot X.rot R.darts R.rot_mem_darts_iff cs) with hX'
  have hinv : X'.inv = X.inv := rfl
  have hrot : ∀ d ∉ R.darts, X'.rot d = X.rot d := fun d hd =>
    prescribedRot_apply_of_notMem (hD := R.rot_mem_darts_iff) hsub hd
  have hpow : ∀ i < K, ∀ a < 6, ∀ k, (X'.rot ^ k) (T i a) = T i ((a + k) % 6) :=
    fun i hi a ha k => prescribedRot_pow_tuple (hD := R.rot_mem_darts_iff) hnd hsub (hT i hi) a k ha
  have hvert : ∀ i < K, ∀ a < 6, ∀ e, e ∈ X'.vertexOf (T i a) ↔ ∃ a' < 6, T i a' = e :=
    fun i hi a ha e => by
      rw [X'.mem_vertexOf]
      exact prescribedRot_sameCycle_tuple (hD := R.rot_mem_darts_iff) hnd hsub (hT i hi) ha
  have hTD : ∀ i < K, ∀ a < 6, T i a ∈ R.darts := fun i hi a ha =>
    hsub _ (List.mem_flatten.2 ⟨_, hT i hi, List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩⟩)
  have hnewD : ∀ i < K, ∀ a < 6, X'.vertexOf (T i a) ⊆ R.darts := fun i hi a ha e he => by
    obtain ⟨a', ha', rfl⟩ := (hvert i hi a ha e).1 he
    exact hTD i hi a' ha'
  have hnewbd : ∀ i < K, ∀ a < 6, ¬X'.IsBoundaryVertex (X'.vertexOf (T i a)) := by
    rintro i hi a ha ⟨e, he, heB⟩
    exact R.notMem_bdry_of_mem_darts (hnewD i hi a ha he) heB
  have hnewinj : ∀ i < K, ∀ i' < K, ∀ a < 6, ∀ a' < 6,
      X'.vertexOf (T i a) = X'.vertexOf (T i' a') → i = i' := by
    intro i hi i' hi' a ha a' ha' h
    have : T i' 0 ∈ X'.vertexOf (T i a) := by
      rw [h, hvert i' hi' a' ha']
      exact ⟨0, by norm_num, rfl⟩
    obtain ⟨b', hb', hb⟩ := (hvert i hi a ha _).1 this
    exact hTinj i hi i' hi' b' hb' hb
  have hTB : ∀ i < K, ∀ a < 6, T i a ∉ X.bdry := fun i hi a ha =>
    R.notMem_bdry_of_mem_darts (hTD i hi a ha)
  cases ζ with
  | right =>
    obtain ⟨c, hc, ⟨t, ht⟩, hρ⟩ := hR.exists_right hP
    set M := (List.range (K - 1)).map (fun i => T i 3) with hM
    set P' := P.take (c + 1) ++ M ++ P.drop (c + p + 1) with hP'
    have hMl : M.length = K - 1 := by simp [hM]
    have hP'l : P'.length = c + 1 + (K - 1) + (P.length - (c + p + 1)) := by
      simp only [hP', List.length_append, List.length_take, List.length_drop, hMl]
      omega
    have hlen : P'.length + p + 1 = P.length + K := by omega
    have hpre : ∀ i (hi : i ≤ c), P'[i]'(by omega) = P[i]'(by omega) := fun i hi =>
      getElem_splice_left P M _ (by omega) hi
    have hsuf : ∀ i (hi : c + K ≤ i) (hi' : i < P'.length),
        P'[i] = P[i + p + 1 - K]'(by omega) := by
      intro i hi hi'
      rw [getElem_splice_right P M _ (by omega) (by omega) (by simp; omega)]
      simp only [List.getElem_drop, hMl]
      exact getElem_idx P (by omega) _
    have hinvP' : ∀ i (hi : i < K), X.inv (P'[c + i]'(by omega)) = T i 0 := by
      intro i hi
      rcases i with _ | i
      · rw [getElem_idx P' (Nat.add_zero c), hpre c le_rfl, hstart, (hρ 0 (Nat.zero_le _)).1]
        simp only [Nat.add_zero]
      · rw [getElem_splice_mid P M _ (by omega) (by omega) (by omega)]
        simp only [hM, List.getElem_map, List.getElem_range,
          show c + (i + 1) - c - 1 = i by omega]
        exact hchain i (by omega)
    have hP'succ : ∀ i (hi : i < K), P'[c + i + 1]'(by omega) = T i 3 := by
      intro i hi
      by_cases hiK : i + 1 < K
      · rw [getElem_splice_mid P M _ (by omega) (by omega) (by omega)]
        simp only [hM, List.getElem_map, List.getElem_range, show c + i + 1 - c - 1 = i by omega]
      · rw [getElem_splice_right P M _ (by omega) (by omega) (by simp; omega)]
        simp only [List.getElem_drop, hMl]
        obtain rfl : i = K - 1 := by omega
        rw [hend, (hρ p le_rfl).2]
        exact getElem_idx P (by omega) _
    have hidx : ∀ t (ht : c ≤ t) (ht' : t < c + K),
        P'[t]'(by omega) = P'[c + (t - c)]'(by omega) := fun t ht ht' =>
      getElem_idx P' (by omega) _
    have hnewstep : ∀ t (ht : c ≤ t) (ht' : t < c + K),
        (X'.rot ^ 3) (X.inv (P'[t]'(by omega))) = P'[t + 1]'(by omega) := by
      intro t ht ht'
      rw [hidx t ht ht', hinvP' _ (by omega), hpow _ (by omega) 0 (by norm_num),
        getElem_idx P' (show t + 1 = c + (t - c) + 1 by omega), hP'succ _ (by omega)]
    obtain ⟨hold, hstart', hend'⟩ := RailPoints.disjoint_of_isAlong hP hR (s := c)
      fun j hj => ⟨c + j, by omega, by omega, by omega, by rw [(hρ j hj).1]⟩
    have hin : ∀ l (hl : c ≤ l) (hl' : l ≤ c + p),
        X.vertexOf (X.inv (P[l]'(by omega))) ⊆ R.darts := by
      intro l hl hl'
      have := R.vertexOf_subset_darts (a := Sum.inl (l - c)) (by simp [pointSet]; omega)
      simp only [Sum.elim_inl, (hρ (l - c) (by omega)).1] at this
      rwa [← getElem_idx P (show l = c + (l - c) by omega)] at this
    have hnewD' : ∀ t (ht : c ≤ t) (ht' : t < c + K),
        X'.vertexOf (X.inv (P'[t]'(by omega))) ⊆ R.darts := fun t ht ht' => by
      rw [hidx t ht ht', hinvP' _ (by omega)]
      exact hnewD _ (by omega) 0 (by norm_num)
    have hnewbd' : ∀ t (ht : c ≤ t) (ht' : t < c + K),
        ¬X'.IsBoundaryVertex (X'.vertexOf (X.inv (P'[t]'(by omega)))) := fun t ht ht' => by
      rw [hidx t ht ht', hinvP' _ (by omega)]
      exact hnewbd _ (by omega) 0 (by norm_num)
    have hnewinj' : ∀ t (ht : c ≤ t) (ht' : t < c + K) t' (hu : c ≤ t') (hu' : t' < c + K),
        X'.vertexOf (X.inv (P'[t]'(by omega))) = X'.vertexOf (X.inv (P'[t']'(by omega))) →
          t = t' := fun t ht ht' t' hu hu' h => by
      rw [hidx t ht ht', hidx t' hu hu', hinvP' _ (by omega), hinvP' _ (by omega)] at h
      have := hnewinj _ (by omega) _ (by omega) 0 (by norm_num) 0 (by norm_num) h
      omega
    have hnewdart : ∀ t (ht : c < t) (ht' : t < c + K),
        P'[t]'(by omega) ∉ X.bdry ∧ X.isOut (P'[t]'(by omega)) = true := fun t ht ht' => by
      rw [getElem_idx P' (show t = c + (t - c - 1) + 1 by omega), hP'succ _ (by omega)]
      exact ⟨hTB _ (by omega) 3 (by norm_num), (hout _ (by omega)).2 rfl⟩
    obtain ⟨hS, hh, hl, hf, hright, -⟩ := splice (X' := X') hinv rfl rfl hrot hP hK
      (by omega) hlen hpre hsuf (hstart' (by omega)) (hend' (by omega)) hold hin hnewstep
      hnewD' hnewbd' hnewinj' hnewdart
    refine ⟨P', hS, hlen, hh, hl, hf, (X.sideList .right P).take (2 * c), t, ht, ?_⟩
    have hSl := length_sideList (X := X) .right P
    have hdrop : (X.sideList .right P).drop (2 * (c + p + 1)) = t := by
      conv_lhs => rw [ht]
      exact drop_append_append (by simp; omega)
    rw [hright, hdrop]
    congr 2
    apply flatMap_two_ext _ _ _ _ (by simp; omega)
    intro u h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_range, sideDarts]
    have h1 := hpow u (by simpa using h2) 0 (by norm_num) 1
    rw [pow_one] at h1
    rw [hinv, hinvP' u (by simpa using h2), h1, hpow u (by simpa using h2) 0 (by norm_num)]
  | left =>
    obtain ⟨c, ⟨hpc, hc⟩, ⟨t, ht⟩, hρ⟩ := hR.exists_left hX hP
    set M := (List.range (K - 1)).map (fun i => T (K - 1 - i) 0) with hM
    set P' := P.take (c - p + 1) ++ M ++ P.drop (c + 1) with hP'
    have hMl : M.length = K - 1 := by simp [hM]
    have hP'l : P'.length = c - p + 1 + (K - 1) + (P.length - (c + 1)) := by
      simp only [hP', List.length_append, List.length_take, List.length_drop, hMl]
      omega
    have hlen : P'.length + p + 1 = P.length + K := by omega
    have hpre : ∀ i (hi : i ≤ c - p), P'[i]'(by omega) = P[i]'(by omega) := fun i hi =>
      getElem_splice_left P M _ (by omega) hi
    have hsuf : ∀ i (hi : c - p + K ≤ i) (hi' : i < P'.length),
        P'[i] = P[i + p + 1 - K]'(by omega) := by
      intro i hi hi'
      rw [getElem_splice_right P M _ (by omega) (by omega) (by simp; omega)]
      simp only [List.getElem_drop, hMl]
      exact getElem_idx P (by omega) _
    have hinvP' : ∀ i (hi : i < K), X.inv (P'[c - p + i]'(by omega)) = T (K - 1 - i) 3 := by
      intro i hi
      rcases i with _ | i
      · rw [getElem_idx P' (Nat.add_zero (c - p)), hpre (c - p) le_rfl, Nat.sub_zero, hend,
          (hρ p le_rfl).2]
      · rw [getElem_splice_mid P M _ (by omega) (by omega) (by omega)]
        simp only [hM, List.getElem_map, List.getElem_range,
          show c - p + (i + 1) - (c - p) - 1 = i by omega]
        have := hchain (K - 1 - (i + 1)) (by omega)
        rw [show K - 1 - (i + 1) + 1 = K - 1 - i by omega] at this
        rw [← this, hX.inv_inv_apply]
    have hP'succ : ∀ i (hi : i < K), P'[c - p + i + 1]'(by omega) = T (K - 1 - i) 0 := by
      intro i hi
      by_cases hiK : i + 1 < K
      · rw [getElem_splice_mid P M _ (by omega) (by omega) (by omega)]
        simp only [hM, List.getElem_map, List.getElem_range,
          show c - p + i + 1 - (c - p) - 1 = i by omega]
      · rw [getElem_splice_right P M _ (by omega) (by omega) (by simp; omega)]
        simp only [List.getElem_drop, hMl]
        obtain rfl : i = K - 1 := by omega
        rw [Nat.sub_self, hstart, (hρ 0 (Nat.zero_le _)).1]
        exact getElem_idx P (by omega) _
    have hidx : ∀ t (ht : c - p ≤ t) (ht' : t < c - p + K),
        P'[t]'(by omega) = P'[c - p + (t - (c - p))]'(by omega) := fun t ht ht' =>
      getElem_idx P' (by omega) _
    have hnewstep : ∀ t (ht : c - p ≤ t) (ht' : t < c - p + K),
        (X'.rot ^ 3) (X.inv (P'[t]'(by omega))) = P'[t + 1]'(by omega) := by
      intro t ht ht'
      rw [hidx t ht ht', hinvP' _ (by omega), hpow _ (by omega) 3 (by norm_num),
        show (3 + 3) % 6 = 0 from rfl,
        getElem_idx P' (show t + 1 = c - p + (t - (c - p)) + 1 by omega), hP'succ _ (by omega)]
    obtain ⟨hold, hstart', hend'⟩ := RailPoints.disjoint_of_isAlong hP hR (s := c - p)
      fun j hj => ⟨c - j, by omega, by omega, by omega, by
        rw [(hρ j hj).1, ← rot_pow_three_inv_getElem hP.isStrandPath (by omega),
          X.vertexOf_rot_pow_apply]⟩
    have hin : ∀ l (hl : c - p ≤ l) (hl' : l ≤ c - p + p),
        X.vertexOf (X.inv (P[l]'(by omega))) ⊆ R.darts := by
      intro l hl hl'
      have := R.vertexOf_subset_darts (a := Sum.inl (c - l)) (by simp [pointSet]; omega)
      simp only [Sum.elim_inl, (hρ (c - l) (by omega)).1] at this
      rw [← rot_pow_three_inv_getElem hP.isStrandPath (by omega), X.vertexOf_rot_pow_apply]
        at this
      rwa [← getElem_idx P (show l = c - (c - l) by omega)] at this
    have hnewD' : ∀ t (ht : c - p ≤ t) (ht' : t < c - p + K),
        X'.vertexOf (X.inv (P'[t]'(by omega))) ⊆ R.darts := fun t ht ht' => by
      rw [hidx t ht ht', hinvP' _ (by omega)]
      exact hnewD _ (by omega) 3 (by norm_num)
    have hnewbd' : ∀ t (ht : c - p ≤ t) (ht' : t < c - p + K),
        ¬X'.IsBoundaryVertex (X'.vertexOf (X.inv (P'[t]'(by omega)))) := fun t ht ht' => by
      rw [hidx t ht ht', hinvP' _ (by omega)]
      exact hnewbd _ (by omega) 3 (by norm_num)
    have hnewinj' : ∀ t (ht : c - p ≤ t) (ht' : t < c - p + K) t' (hu : c - p ≤ t')
        (hu' : t' < c - p + K),
        X'.vertexOf (X.inv (P'[t]'(by omega))) = X'.vertexOf (X.inv (P'[t']'(by omega))) →
          t = t' := fun t ht ht' t' hu hu' h => by
      rw [hidx t ht ht', hidx t' hu hu', hinvP' _ (by omega), hinvP' _ (by omega)] at h
      have := hnewinj _ (by omega) _ (by omega) 3 (by norm_num) 3 (by norm_num) h
      omega
    have hnewdart : ∀ t (ht : c - p < t) (ht' : t < c - p + K),
        P'[t]'(by omega) ∉ X.bdry ∧ X.isOut (P'[t]'(by omega)) = true := fun t ht ht' => by
      rw [getElem_idx P' (show t = c - p + (t - (c - p) - 1) + 1 by omega),
        hP'succ _ (by omega)]
      refine ⟨hTB _ (by omega) 0 (by norm_num), ?_⟩
      have hj := hchain (K - 1 - (t - (c - p) - 1) - 1) (by omega)
      rw [show K - 1 - (t - (c - p) - 1) - 1 + 1 = K - 1 - (t - (c - p) - 1) by omega] at hj
      rw [← hj, hX.isOut_inv_apply (hTB _ (by omega) 3 (by norm_num))]
      have := hout (K - 1 - (t - (c - p) - 1) - 1) (by omega)
      simpa using this
    obtain ⟨hS, hh, hl, hf, -, hleft⟩ := splice (X' := X') hinv rfl rfl hrot hP hK
      (by omega) hlen hpre hsuf (hstart' (by omega)) (hend' (by omega)) hold hin hnewstep
      hnewD' hnewbd' hnewinj' hnewdart
    refine ⟨P', hS, hlen, hh, hl, hf, (X.sideList .left P).take (2 * (P.length - 2 - c)), t, ht,
      ?_⟩
    have hSl := length_sideList (X := X) .left P
    have hdrop : (X.sideList .left P).drop (2 * (P.length - 1 - (c - p))) = t := by
      conv_lhs => rw [ht]
      exact drop_append_append (by simp; omega)
    rw [hleft, hdrop, show c - p + p = c by omega]
    congr 2
    have hrev : ∀ u (hu : u < K), ((P'.drop (c - p)).take K).reverse[u]'(by simp; omega) =
        P'[c - p + (K - 1 - u)]'(by omega) := by
      intro u hu
      simp only [List.getElem_reverse, List.getElem_take, List.getElem_drop]
      exact getElem_idx P' (by simp; omega) _
    apply flatMap_two_ext _ _ _ _ (by simp; omega)
    intro u h1 h2
    simp only [List.length_range] at h2
    rw [hrev u h2]
    simp only [List.getElem_range, sideDarts]
    rw [hinv, hinvP' _ (by omega), hpow _ (by omega) 3 (by norm_num),
      hpow _ (by omega) 3 (by norm_num), show K - 1 - (K - 1 - u) = u by omega]

omit [Fintype H] [DecidableEq H] in
/-- Regrouping a list of pairs `[f 0, g 0, f 1, g 1, …]`. -/
private theorem flatMap_range_pair {β : Type*} (f g : ℕ → β) :
    ∀ K, 1 ≤ K → (List.range K).flatMap (fun i => [f i, g i]) =
      f 0 :: ((List.range' 1 (K - 1)).flatMap fun j => [g (j - 1), f j]) ++ [g (K - 1)]
  | 0, h => absurd h (by norm_num)
  | 1, _ => rfl
  | K + 2, _ => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_pair f g (K + 1) (by omega),
      show K + 2 - 1 = K + 1 by omega, List.range'_concat, List.flatMap_append]
    simp [Nat.add_comm]

omit [Fintype H] in
private theorem eq_of_mem_getElem? {α : Type*} {cs : List (List α)} (hnd : cs.flatten.Nodup)
    {i i' : ℕ} {l l' : List α} (hl : cs[i]? = some l) (hl' : cs[i']? = some l') {x : α}
    (hx : x ∈ l) (hx' : x ∈ l') : i = i' := by
  have hpw := (List.nodup_flatten.1 hnd).2
  rw [List.pairwise_iff_getElem] at hpw
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hl
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hl'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hpw i i' hi hi' h hx hx'
  · exact hpw i' i hi' hi h hx' hx

namespace RailPoints

variable {p q : ℕ}

/-- The named darts `ρ_{j,0}` of a rail along a strand path on the right are `in`, on the left
`out`. -/
theorem IsAlong.isOut_rho (hX : X.IsPreTripleDiagram) {R : X.RailPoints p q} {P : List H}
    (hP : X.IsSimpleStrandPath P) {ζ : StrandSide} (hR : R.IsAlong P ζ) {j : ℕ} (hj : j ≤ p) :
    X.isOut (R.rho j) = true ↔ ζ = .left := by
  have hPg := X.isStrandPath_iff_getElem.1 hP.isStrandPath
  obtain ⟨l, hl, -, hr, hlft⟩ := hR.exists_pass hX hP j hj
  cases ζ with
  | right =>
    rw [(hr rfl).1, hX.isOut_inv_apply (hPg.2.1 l (by omega)).1, (hPg.2.1 l (by omega)).2]
    simp
  | left =>
    rw [(hlft rfl).1, (hPg.2.1 (l + 1) hl).2]
    simp

/-- The orientation of `ρ_{j,k} = σ^k(ρ_{j,0})`. -/
private theorem isOut_dart_rho (hX : X.IsPreTripleDiagram) (R : X.RailPoints p q) {j : ℕ}
    (hj : j ≤ p) (k : ℕ) :
    X.isOut (R.dart (RailLabel.rho j k)) =
      if Even k then X.isOut (R.rho j) else !X.isOut (R.rho j) := by
  rw [dart_rho]
  refine hX.isOut_rot_pow_apply ?_ k
  have := R.vertexOf_mem (Sum.inl j) (by simp [pointSet]; omega)
  exact (X.mem_internalVertices.1 this).2

end RailPoints

/-! ### The strand path after a push-off -/

namespace ClosedAlignedRail

variable {n : ℕ}

/-- The labels of the `i`-th tuple of the first item of the push-off. -/
private def firstLabels (n i : ℕ) : List RailLabel :=
  if i + 1 < n then
    [alignedEta i 5, alignedEta i 2, alignedEta (i + 1) 1, rho (i + 1) 1, alignedEta i 3, rho i 3]
  else
    [alignedEta (n - 1) 5, alignedEta (n - 1) 2, rho n 2, rho n 3, alignedEta (n - 1) 3,
      rho (n - 1) 3]

private theorem getElem?_pushOffLabels {i : ℕ} (hi : i < n) :
    (pushOffLabels n)[i]? = some (firstLabels n i) := by
  unfold pushOffLabels firstLabels
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
  split_ifs with h
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map, List.length_range]
    rw [show i - (n - 1) = 0 by omega]
    rfl

/-- **The strand path after a push-off**. Let `P = (e₁, …, e_m)` be a simple strand path of `X`,
`ζ` a side, and `X'` the push-off of a closed aligned rail of length `n` along `P` on side `ζ`,
with `D` the set of darts at its points. Then `X'` has a simple strand path with `m - 1` darts,
first dart `e₁` and last dart `e_m`, whose darts not in `D` are those of `P` (in the same order),
and whose `ζ` list is that of `P` with the block `(ρ_{0,1}, ρ_{0,2}, …, ρ_{n,1}, ρ_{n,2})` replaced
by `(ρ_{0,1}, η_{1,1}, η_{1,2}, …, η_{n-1,1}, η_{n-1,2}, ρ_{n,2})`.

Only the conditions of a pre-triple diagram on `X` are used. -/
@[cluster_algebras "lem_push_off_path"]
theorem exists_isSimpleStrandPath_pushOff (hX : X.IsPreTripleDiagram) (R : X.ClosedAlignedRail n)
    {P : List H} (hP : X.IsSimpleStrandPath P) {ζ : StrandSide} (hR : R.IsAlong P ζ) :
    ∃ P', R.pushOff.IsSimpleStrandPath P' ∧ P'.length + 1 = P.length ∧
      P'.head? = P.head? ∧ P'.getLast? = P.getLast? ∧
      P'.filter (· ∉ R.railPoints.darts) = P.filter (· ∉ R.railPoints.darts) ∧
      ∃ L₁ L₂, X.sideList ζ P = L₁ ++ R.railPoints.facingDarts ++ L₂ ∧
        R.pushOff.sideList ζ P' = L₁ ++ (R.railPoints.dart (rho 0 1) ::
          ((List.range' 1 (n - 1)).flatMap fun j =>
            [R.railPoints.dart (eta j 1), R.railPoints.dart (eta j 2)]) ++
          [R.railPoints.dart (rho n 2)]) ++ L₂ := by
  have hn := R.one_le
  set RP := R.railPoints with hRP
  set T : ℕ → ℕ → H := fun i k => RP.dart ((firstLabels n i).getD k (rho 0 0)) with hTdef
  have hTmap : ∀ i, (List.range 6).map (T i) = (firstLabels n i).map RP.dart := by
    intro i
    simp only [hTdef, firstLabels]
    split_ifs <;> rfl
  have hcs : ∀ i < n, R.pushOffTuples[i]? = some ((List.range 6).map (T i)) := by
    intro i hi
    rw [pushOffTuples, List.getElem?_map, getElem?_pushOffLabels hi, hTmap]
    rfl
  have hnd := R.nodup_flatten_pushOffTuples hX
  have hsub : ∀ x ∈ R.pushOffTuples.flatten, x ∈ RP.darts := fun x hx => by
    rw [← R.toFinset_flatten_pushOffTuples hX]
    exact List.mem_toFinset.2 hx
  have hT : ∀ i < n, (List.range 6).map (T i) ∈ R.pushOffTuples := fun i hi =>
    List.mem_of_getElem? (hcs i hi)
  have hTinj : ∀ i < n, ∀ i' < n, ∀ a < 6, T i a = T i' 0 → i = i' := by
    intro i hi i' hi' a ha h
    refine eq_of_mem_getElem? hnd (hcs i hi) (hcs i' hi') (x := T i a)
      (List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩)
      (List.mem_map.2 ⟨0, List.mem_range.2 (by norm_num), h.symm⟩)
  have hT3 : ∀ i, i + 1 < n → T i 3 = RP.dart (rho (i + 1) 1) := fun i hi => by
    simp [hTdef, firstLabels, hi]
  have hT0 : ∀ i, 1 ≤ i → i < n → T i 0 = RP.dart (eta i 5) := fun i h1 h2 => by
    simp only [hTdef, firstLabels]
    split_ifs with h
    · simp [alignedEta, show i ≠ 0 by omega]
    · simp [alignedEta, show n - 1 = i by omega, show i ≠ 0 by omega]
  have hchain : ∀ i, i + 1 < n → X.inv (T i 3) = T (i + 1) 0 := fun i hi => by
    rw [hT3 i hi, hT0 (i + 1) (by omega) hi]
    exact R.inv_rho_one (i + 1) (by omega) (by omega)
  have hstart : T 0 0 = RP.rho 0 := by
    simp only [hTdef, firstLabels]
    split_ifs with h
    · simp [alignedEta, alignedIndex, RailPoints.dart_rho]
    · have h' : n - 1 = 0 := by omega
      simp [h', alignedEta, alignedIndex, RailPoints.dart_rho]
  have hend : T (n - 1) 3 = RP.dart (rho n 3) := by
    simp [hTdef, firstLabels, show ¬(n - 1 + 1 < n) by omega]
  have hout : ∀ i, i + 1 < n → (X.isOut (T i 3) = true ↔ ζ = .right) := fun i hi => by
    rw [hT3 i hi, RailPoints.isOut_dart_rho hX RP (by omega) 1]
    have := RailPoints.IsAlong.isOut_rho hX hP hR (j := i + 1) (by omega)
    cases ζ <;> simp_all
  obtain ⟨P', hS, hlen, hh, hl, hf, L₁, L₂, h1, h2⟩ := splice_rail hX RP hnd hsub hP hR hn T hT
    hTinj hchain hstart hend hout
  refine ⟨P', hS, by omega, hh, hl, hf, L₁, L₂, h1, ?_⟩
  have hblock : (List.range n).flatMap (fun i => [T i 1, T i 2]) =
      RP.dart (rho 0 1) :: ((List.range' 1 (n - 1)).flatMap fun j =>
        [RP.dart (eta j 1), RP.dart (eta j 2)]) ++ [RP.dart (rho n 2)] := by
    rw [flatMap_range_pair _ _ n hn]
    congr 1
    · congr 1
      · simp only [hTdef, firstLabels]
        split_ifs with h
        · simp [alignedEta, alignedIndex]
        · have h' : n - 1 = 0 := by omega
          simp [h', alignedEta, alignedIndex]
      · refine List.flatMap_congr fun j hj => ?_
        obtain ⟨h1, h2⟩ : 1 ≤ j ∧ j < n := by rw [List.mem_range'_1] at hj; omega
        have e : j - 1 + 1 = j := by omega
        simp only [hTdef, firstLabels, e, if_pos h2]
        split_ifs with h
        · simp [alignedEta, show j ≠ 0 by omega]
        · simp [alignedEta, show j ≠ 0 by omega, show n - 1 = j by omega]
    · simp [hTdef, firstLabels, show ¬(n - 1 + 1 < n) by omega]
  rw [show R.pushOff = withRot X (prescribedRot X.rot RP.darts RP.rot_mem_darts_iff
    R.pushOffTuples) from rfl, h2, hblock]

end ClosedAlignedRail

/-! ### The strand paths after the combings -/

namespace AlignedRail

variable {r : ℕ}

/-- The labels of the `i`-th tuple of the first item of the aligned combing. -/
private def firstLabels (r i : ℕ) : List RailLabel :=
  if i < r then
    [alignedEta i 5, alignedEta i 2, alignedEta (i + 1) 1, rho (i + 1) 1, alignedEta i 3, rho i 3]
  else
    [alignedEta r 5, alignedEta r 2, alignedEta r 3, rho r 3, rho r 4, alignedEta r 4]

private theorem getElem?_alignedCombLabels {i : ℕ} (hi : i < r + 1) :
    (alignedCombLabels r)[i]? = some (firstLabels r i) := by
  unfold alignedCombLabels firstLabels
  rw [List.getElem?_append_left (by simp; omega)]
  split_ifs with h
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map, List.length_range]
    rw [show i - r = 0 by omega]
    rfl

/-- **The strand path after an aligned combing**. Let `P = (e₁, …, e_m)` be a simple strand path
of `X`, `ζ` a side, `r ≥ 1`, and `X'` the aligned combing of an aligned rail of length `r` along
`P` on side `ζ`, with `D` the set of darts at its points. Then `X'` has a simple strand path with
`m` darts, first dart `e₁` and last dart `e_m`, whose darts not in `D` are those of `P` (in the
same order), and whose `ζ` list is that of `P` with the block
`(ρ_{0,1}, ρ_{0,2}, …, ρ_{r,1}, ρ_{r,2})` replaced by
`(ρ_{0,1}, η_{1,1}, η_{1,2}, …, η_{r,1}, η_{r,2}, η_{r,3})`.

Only the conditions of a pre-triple diagram on `X` are used. -/
@[cluster_algebras "lem_comb_aligned_path"]
theorem exists_isSimpleStrandPath_alignedComb (hX : X.IsPreTripleDiagram) (hr : 1 ≤ r)
    (R : X.AlignedRail r) {P : List H} (hP : X.IsSimpleStrandPath P) {ζ : StrandSide}
    (hR : R.IsAlong P ζ) :
    ∃ P', R.alignedComb.IsSimpleStrandPath P' ∧ P'.length = P.length ∧
      P'.head? = P.head? ∧ P'.getLast? = P.getLast? ∧
      P'.filter (· ∉ R.darts) = P.filter (· ∉ R.darts) ∧
      ∃ L₁ L₂, X.sideList ζ P = L₁ ++ R.facingDarts ++ L₂ ∧
        R.alignedComb.sideList ζ P' = L₁ ++ (R.dart (rho 0 1) ::
          ((List.range' 1 r).flatMap fun j => [R.dart (eta j 1), R.dart (eta j 2)]) ++
          [R.dart (eta r 3)]) ++ L₂ := by
  set RP := R.toRailPoints with hRP
  set T : ℕ → ℕ → H := fun i k => RP.dart ((firstLabels r i).getD k (rho 0 0)) with hTdef
  have hTmap : ∀ i, (List.range 6).map (T i) = (firstLabels r i).map RP.dart := by
    intro i
    simp only [hTdef, firstLabels]
    split_ifs <;> rfl
  have hcs : ∀ i < r + 1, R.alignedCombTuples[i]? = some ((List.range 6).map (T i)) := by
    intro i hi
    rw [alignedCombTuples, List.getElem?_map, getElem?_alignedCombLabels hi, hTmap]
    rfl
  have hnd := R.nodup_flatten_alignedCombTuples hX
  have hsub : ∀ x ∈ R.alignedCombTuples.flatten, x ∈ RP.darts := fun x hx => by
    rw [← R.toFinset_flatten_alignedCombTuples hX]
    exact List.mem_toFinset.2 hx
  have hT : ∀ i < r + 1, (List.range 6).map (T i) ∈ R.alignedCombTuples := fun i hi =>
    List.mem_of_getElem? (hcs i hi)
  have hTinj : ∀ i < r + 1, ∀ i' < r + 1, ∀ a < 6, T i a = T i' 0 → i = i' := by
    intro i hi i' hi' a ha h
    refine eq_of_mem_getElem? hnd (hcs i hi) (hcs i' hi') (x := T i a)
      (List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩)
      (List.mem_map.2 ⟨0, List.mem_range.2 (by norm_num), h.symm⟩)
  have hT3 : ∀ i, i < r → T i 3 = RP.dart (rho (i + 1) 1) := fun i hi => by
    simp [hTdef, firstLabels, hi]
  have hT0 : ∀ i, 1 ≤ i → i ≤ r → T i 0 = RP.dart (eta i 5) := fun i h1 h2 => by
    simp only [hTdef, firstLabels]
    split_ifs with h
    · simp [alignedEta, show i ≠ 0 by omega]
    · simp [alignedEta, show r = i by omega, show i ≠ 0 by omega]
  have hchain : ∀ i, i + 1 < r + 1 → X.inv (T i 3) = T (i + 1) 0 := fun i hi => by
    rw [hT3 i (by omega), hT0 (i + 1) (by omega) (by omega)]
    exact R.inv_rho_one (i + 1) (by omega) (by omega)
  have hstart : T 0 0 = RP.rho 0 := by
    simp [hTdef, firstLabels, show 0 < r by omega, alignedEta, alignedIndex,
      RailPoints.dart_rho]
  have hend : T (r + 1 - 1) 3 = RP.dart (rho r 3) := by
    simp [hTdef, firstLabels]
  have hout : ∀ i, i + 1 < r + 1 → (X.isOut (T i 3) = true ↔ ζ = .right) := fun i hi => by
    rw [hT3 i (by omega), RailPoints.isOut_dart_rho hX RP (by omega) 1]
    have := RailPoints.IsAlong.isOut_rho hX hP hR (j := i + 1) (by omega)
    cases ζ <;> simp_all
  obtain ⟨P', hS, hlen, hh, hl, hf, L₁, L₂, h1, h2⟩ := splice_rail hX RP hnd hsub hP hR
    (K := r + 1) (by omega) T hT hTinj hchain hstart hend hout
  refine ⟨P', hS, by omega, hh, hl, hf, L₁, L₂, h1, ?_⟩
  have hT1 : ∀ i ≤ r, T i 1 = RP.dart (alignedEta i 2) := fun i hi => by
    simp only [hTdef, firstLabels]
    split_ifs with h
    · rfl
    · obtain rfl : i = r := by omega
      rfl
  have hT2 : ∀ i < r, T i 2 = RP.dart (alignedEta (i + 1) 1) := fun i hi => by
    simp only [hTdef, firstLabels, if_pos hi]
    rfl
  have hT2r : T r 2 = RP.dart (eta r 3) := by
    simp only [hTdef, firstLabels, if_neg (lt_irrefl r)]
    change RP.dart (alignedEta r 3) = _
    rw [alignedEta, if_neg (show r ≠ 0 by omega)]
  have hblock : (List.range (r + 1)).flatMap (fun i => [T i 1, T i 2]) =
      RP.dart (rho 0 1) :: ((List.range' 1 r).flatMap fun j =>
        [RP.dart (eta j 1), RP.dart (eta j 2)]) ++ [RP.dart (eta r 3)] := by
    rw [flatMap_range_pair _ _ (r + 1) (by omega), Nat.add_sub_cancel, hT1 0 (Nat.zero_le _),
      hT2r]
    congr 2
    refine List.flatMap_congr fun j hj => ?_
    obtain ⟨h1, h2⟩ : 1 ≤ j ∧ j < r + 1 := by rw [List.mem_range'_1] at hj; omega
    rw [hT2 (j - 1) (by omega), hT1 j (by omega), show j - 1 + 1 = j by omega, alignedEta,
      alignedEta, if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 0 by omega)]
  rw [show R.alignedComb = withRot X (prescribedRot X.rot RP.darts RP.rot_mem_darts_iff
    R.alignedCombTuples) from rfl, h2, hblock]

end AlignedRail

namespace StaggeredRail

variable {r : ℕ}

/-- The labels of the `i`-th tuple of the first item of the staggered combing. -/
private def firstLabels (r i : ℕ) : List RailLabel :=
  if i = 0 then [rho 0 0, eta 1 1, eta 1 2, rho 0 1, rho 0 2, rho 0 5]
  else if i < r then [eta i 0, eta (i + 1) 1, eta (i + 1) 2, eta i 3, rho i 2, rho (i - 1) 3]
  else [eta r 0, eta r 3, rho r 2, rho r 3, eta r 4, rho (r - 1) 3]

private theorem getElem?_staggeredCombLabels (hr : 1 ≤ r) {i : ℕ} (hi : i < r + 1) :
    (staggeredCombLabels r)[i]? = some (firstLabels r i) := by
  unfold staggeredCombLabels firstLabels
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
  split_ifs with h0 h
  · subst h0
    rfl
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega),
      List.getElem?_map]
    simp only [List.length_singleton]
    rw [List.getElem?_range' (by omega)]
    simp only [Option.map_some, Nat.one_mul]
    rw [show 1 + (i - 1) = i by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_singleton, List.length_map, List.length_range']
    rw [show i - (1 + (r - 1)) = 0 by omega]
    rfl

/-- **The strand path after a staggered combing**. Let `P = (e₁, …, e_m)` be a simple strand path
of `X`, `ζ` a side, and `X'` the staggered combing of a staggered rail of length `r` along `P` on
side `ζ`, with `D` the set of darts at its points. Then `X'` has a simple strand path with `m`
darts, first dart `e₁` and last dart `e_m`, whose darts not in `D` are those of `P` (in the same
order), and whose `ζ` list is that of `P` with the block `(ρ_{0,1}, ρ_{0,2}, …, ρ_{r,1}, ρ_{r,2})`
replaced by `(η_{1,1}, η_{1,2}, …, η_{r,1}, η_{r,2}, η_{r,3}, ρ_{r,2})`.

Only the conditions of a pre-triple diagram on `X` are used. -/
@[cluster_algebras "lem_comb_staggered_path"]
theorem exists_isSimpleStrandPath_staggeredComb (hX : X.IsPreTripleDiagram)
    (R : X.StaggeredRail r) {P : List H} (hP : X.IsSimpleStrandPath P) {ζ : StrandSide}
    (hR : R.IsAlong P ζ) :
    ∃ P', R.staggeredComb.IsSimpleStrandPath P' ∧ P'.length = P.length ∧
      P'.head? = P.head? ∧ P'.getLast? = P.getLast? ∧
      P'.filter (· ∉ R.darts) = P.filter (· ∉ R.darts) ∧
      ∃ L₁ L₂, X.sideList ζ P = L₁ ++ R.facingDarts ++ L₂ ∧
        R.staggeredComb.sideList ζ P' = L₁ ++ (((List.range' 1 r).flatMap fun j =>
          [R.dart (eta j 1), R.dart (eta j 2)]) ++ [R.dart (eta r 3), R.dart (rho r 2)]) ++
          L₂ := by
  have hr := R.one_le
  set RP := R.toRailPoints with hRP
  set T : ℕ → ℕ → H := fun i k => RP.dart ((firstLabels r i).getD k (rho 0 0)) with hTdef
  have hTmap : ∀ i, (List.range 6).map (T i) = (firstLabels r i).map RP.dart := by
    intro i
    simp only [hTdef, firstLabels]
    split_ifs <;> rfl
  have hcs : ∀ i < r + 1, R.staggeredCombTuples[i]? = some ((List.range 6).map (T i)) := by
    intro i hi
    rw [staggeredCombTuples, List.getElem?_map, getElem?_staggeredCombLabels hr hi, hTmap]
    rfl
  have hnd := R.nodup_flatten_staggeredCombTuples hX
  have hsub : ∀ x ∈ R.staggeredCombTuples.flatten, x ∈ RP.darts := fun x hx => by
    rw [← R.toFinset_flatten_staggeredCombTuples hX]
    exact List.mem_toFinset.2 hx
  have hT : ∀ i < r + 1, (List.range 6).map (T i) ∈ R.staggeredCombTuples := fun i hi =>
    List.mem_of_getElem? (hcs i hi)
  have hTinj : ∀ i < r + 1, ∀ i' < r + 1, ∀ a < 6, T i a = T i' 0 → i = i' := by
    intro i hi i' hi' a ha h
    refine eq_of_mem_getElem? hnd (hcs i hi) (hcs i' hi') (x := T i a)
      (List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩)
      (List.mem_map.2 ⟨0, List.mem_range.2 (by norm_num), h.symm⟩)
  have hT0 : ∀ i, 1 ≤ i → i ≤ r → T i 0 = RP.dart (eta i 0) := fun i h1 h2 => by
    simp only [hTdef, firstLabels, if_neg (show i ≠ 0 by omega)]
    split_ifs with h
    · rfl
    · simp [show r = i by omega]
  have hchain : ∀ i, i + 1 < r + 1 → X.inv (T i 3) = T (i + 1) 0 := fun i hi => by
    rw [hT0 (i + 1) (by omega) (by omega)]
    rcases i with _ | i
    · exact R.inv_rho_zero_one
    · simp only [hTdef, firstLabels, if_neg (Nat.succ_ne_zero i), if_pos (show i + 1 < r by omega)]
      exact R.inv_eta_three (i + 1) (by omega) (by omega)
  have hstart : T 0 0 = RP.rho 0 := by
    simp [hTdef, firstLabels, RailPoints.dart_rho]
  have hend : T (r + 1 - 1) 3 = RP.dart (rho r 3) := by
    simp [hTdef, firstLabels, show r ≠ 0 by omega]
  have hout : ∀ i, i + 1 < r + 1 → (X.isOut (T i 3) = true ↔ ζ = .right) := fun i hi => by
    have h0 := RailPoints.IsAlong.isOut_rho hX hP hR (j := 0) (Nat.zero_le _)
    rcases i with _ | i
    · have e : T 0 3 = RP.dart (rho 0 1) := by simp [hTdef, firstLabels]
      rw [e, RailPoints.isOut_dart_rho hX RP (Nat.zero_le _) 1]
      cases ζ <;> simp_all
    · have hi' : i + 1 < r := by omega
      have e : T (i + 1) 3 = RP.dart (eta (i + 1) 3) := by simp [hTdef, firstLabels, hi']
      rw [e]
      have hη : ¬X.IsBoundaryVertex (X.vertexOf (RP.eta (i + 1))) := by
        have := RP.vertexOf_mem (Sum.inr (i + 1)) (by simp [pointSet]; omega)
        exact (X.mem_internalVertices.1 this).2
      have e5 := R.inv_rho_two (i + 1) (by omega) (by omega)
      have hB : RP.dart (rho i 2) ∉ X.bdry :=
        RailPoints.notMem_bdry_of_mem_darts RP (RP.dart_mem_darts
          (rho_mem_labelSet (by omega) (by norm_num)))
      have h3 : X.isOut (RP.dart (eta (i + 1) 3)) = X.isOut (RP.dart (eta (i + 1) 5)) := by
        rw [RailPoints.dart_eta, RailPoints.dart_eta, hX.isOut_rot_pow_apply hη,
          hX.isOut_rot_pow_apply hη]
        simp [show ¬Even 3 by decide, show ¬Even 5 by decide]
      rw [h3, show RP.dart (eta (i + 1) 5) = X.inv (RP.dart (rho i 2)) from e5.symm,
        hX.isOut_inv_apply hB, RailPoints.isOut_dart_rho hX RP (by omega) 2]
      have : X.isOut (RP.rho i) = true ↔ ζ = .left :=
        RailPoints.IsAlong.isOut_rho hX hP hR (j := i) (by omega)
      rw [if_pos (by decide : Even 2)]
      cases ζ <;> cases h : X.isOut (RP.rho i) <;> simp [h] at this ⊢
  obtain ⟨P', hS, hlen, hh, hl, hf, L₁, L₂, h1, h2⟩ := splice_rail hX RP hnd hsub hP hR
    (K := r + 1) (by omega) T hT hTinj hchain hstart hend hout
  refine ⟨P', hS, by omega, hh, hl, hf, L₁, L₂, h1, ?_⟩
  have hblock : (List.range (r + 1)).flatMap (fun i => [T i 1, T i 2]) =
      ((List.range' 1 r).flatMap fun j => [RP.dart (eta j 1), RP.dart (eta j 2)]) ++
        [RP.dart (eta r 3), RP.dart (rho r 2)] := by
    rw [List.range_succ, List.flatMap_append, List.range'_eq_map_range, List.flatMap_map]
    congr 1
    · refine List.flatMap_congr fun i hi => ?_
      have hi' := List.mem_range.1 hi
      simp only [hTdef, firstLabels]
      split_ifs with h0
      · subst h0
        simp
      · simp [show i + 1 = 1 + i by omega]
    · simp [hTdef, firstLabels, show r ≠ 0 by omega]
  rw [show R.staggeredComb = withRot X (prescribedRot X.rot RP.darts RP.rot_mem_darts_iff
    R.staggeredCombTuples) from rfl, h2, hblock]

end StaggeredRail

/-! ### A hugging anti-parallel returning path gives a closed aligned rail -/

/-- Two interior points of a strand path with pairwise distinct interior points coincide only
at the same index. -/
private theorem eq_of_nodup_interiorPoints {P : List H} (hnd : (X.interiorPoints P).Nodup)
    {l l' : ℕ} (hl : l + 1 < P.length) (hl' : l' + 1 < P.length)
    (h : X.vertexOf (X.inv P[l]) = X.vertexOf (X.inv P[l'])) : l = l' := by
  simp only [interiorPoints] at hnd
  have e1 : (P.dropLast.map fun e => X.vertexOf (X.inv e))[l]'(by simp; omega) =
      X.vertexOf (X.inv P[l]) := by simp
  have e2 : (P.dropLast.map fun e => X.vertexOf (X.inv e))[l']'(by simp; omega) =
      X.vertexOf (X.inv P[l']) := by simp
  exact (hnd.getElem_inj_iff).1 (by rw [e1, e2, h])

/-- The `ζ` list of a simple strand path has no repeated entry. -/
private theorem nodup_sideList (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsSimpleStrandPath P) (ζ : StrandSide) : (X.sideList ζ P).Nodup := by
  have hPg := X.isStrandPath_iff_getElem.1 hP.isStrandPath
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hj
  rw [length_sideList] at hj
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
    have huu := hposinj u u' hu hu' (eq_of_vertexOf_inv_eq hP (hpos u hu) (hpos u' hu') hv)
    subst huu
    refine ⟨rfl, ?_⟩
    have := (hX.rot_pow_six (hPg.2.2 (pos u) (hpos u hu)).1).2 _ _ (by omega) (by omega) h
    omega
  obtain ⟨u, k, hk, rfl⟩ : ∃ u k, k < 2 ∧ i = 2 * u + k := ⟨i / 2, i % 2, by omega, by omega⟩
  obtain ⟨u', k', hk', rfl⟩ : ∃ u k, k < 2 ∧ j = 2 * u + k := ⟨j / 2, j % 2, by omega, by omega⟩
  cases ζ with
  | right =>
    rw [getElem?_sideList_right hk (by omega), getElem?_sideList_right hk' (by omega), ne_eq,
      Option.some_inj]
    intro h
    have := key 1 u u' k k' hk hk' id (fun u hu => by simp; omega) (fun u u' _ _ h => h)
      (by norm_num) (by omega) (by omega) h
    omega
  | left =>
    rw [getElem?_sideList_left hk (by omega), getElem?_sideList_left hk' (by omega), ne_eq,
      Option.some_inj]
    intro h
    have := key 4 u u' k k' hk hk' (fun u => P.length - 2 - u) (fun u hu => by omega)
      (fun u u' hu hu' h => by omega) (by norm_num) (by omega) (by omega) h
    omega

/-- The interior point `z_{l+1}` of a strand path `P` is the vertex of `P[l]̄`. -/
theorem getElem?_interiorPoints {P : List H} {l : ℕ} (hl : l + 1 < P.length) :
    (X.interiorPoints P)[l]? = some (X.vertexOf (X.inv (P[l]'(by omega)))) := by
  rw [interiorPoints, List.getElem?_map, List.getElem?_dropLast, if_pos (by omega),
    List.getElem?_eq_getElem (by omega)]
  rfl

/-- The interior points of `P` are the vertices of `P[k]̄` for `k + 1 < P.length`. -/
theorem mem_interiorPoints_iff_exists_getElem {P : List H} {v : Finset H} :
    v ∈ X.interiorPoints P ↔ ∃ k, ∃ hk : k + 1 < P.length, X.vertexOf (X.inv P[k]) = v := by
  simp only [interiorPoints, List.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨k, hk, rfl⟩ := mem_dropLast_iff.1 he
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨P[k], getElem_mem_dropLast hk, rfl⟩

omit [Fintype H] [DecidableEq H] in
private theorem rot_zpow_neg_one_eq {d : H} (h : (X.rot ^ 6) d = d) :
    (X.rot ^ (-1 : ℤ)) d = (X.rot ^ 5) d := by
  rw [zpow_neg_one, Equiv.Perm.inv_eq_iff_eq, ← Equiv.Perm.mul_apply, ← pow_succ']
  exact h.symm

omit [Fintype H] [DecidableEq H] in
private theorem rot_zpow_neg_two_eq {d : H} (h : (X.rot ^ 6) d = d) :
    (X.rot ^ (2 * -1 : ℤ)) d = (X.rot ^ 4) d := by
  rw [show (2 * -1 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
    Equiv.Perm.inv_eq_iff_eq, ← Equiv.Perm.mul_apply, ← pow_add]
  exact h.symm

/-- Rail points from interior points of a strand path and of a returning path of it. -/
private theorem railPoints_of_returning {P Q : List H} {ζ : StrandSide} {a b : ℕ}
    (hQ : X.IsReturningPath P ζ Q a b) (hQnd : (X.interiorPoints Q).Nodup) {N M : ℕ}
    {rho eta : ℕ → H} {px py : ℕ → ℕ}
    (hpx : ∀ j ≤ N, ∃ h : px j + 1 < P.length,
      X.vertexOf (rho j) = X.vertexOf (X.inv P[px j]))
    (hpxinj : ∀ j ≤ N, ∀ j' ≤ N, px j = px j' → j = j')
    (hpy : ∀ i, 1 ≤ i → i ≤ M → ∃ h : py i + 1 < Q.length,
      X.vertexOf (eta i) = X.vertexOf (X.inv Q[py i]))
    (hpyinj : ∀ i i', 1 ≤ i → i ≤ M → 1 ≤ i' → i' ≤ M → py i = py i' → i = i') :
    (∀ c ∈ pointSet N M, X.vertexOf (Sum.elim rho eta c) ∈ X.internalVertices) ∧
      Set.InjOn (fun c => X.vertexOf (Sum.elim rho eta c)) (pointSet N M) ∧
      ∀ i, 1 ≤ i → i ≤ M → ∀ e ∈ P,
        X.vertexOf (eta i) ≠ X.vertexOf e ∧ X.vertexOf (eta i) ≠ X.vertexOf (X.inv e) := by
  have hPg := X.isStrandPath_iff_getElem.1 hQ.isSimpleStrandPath.isStrandPath
  have hQg := X.isStrandPath_iff_getElem.1 hQ.isStrandPath
  have hQint : ∀ k (hk : k + 1 < Q.length), X.vertexOf (X.inv Q[k]) ∈ X.interiorPoints Q :=
    fun k hk => List.mem_map.2 ⟨Q[k], getElem_mem_dropLast hk, rfl⟩
  have hy : ∀ i, 1 ≤ i → i ≤ M → ∀ e ∈ P,
      X.vertexOf (eta i) ≠ X.vertexOf e ∧ X.vertexOf (eta i) ≠ X.vertexOf (X.inv e) := by
    intro i h1 h2 e he
    obtain ⟨hk, hv⟩ := hpy i h1 h2
    rw [hv]
    exact hQ.interiorPoints_ne _ (hQint _ hk) e he
  refine ⟨?_, ?_, hy⟩
  · rintro (j | i) hc
    · obtain ⟨hk, hv⟩ := hpx j (by simpa [pointSet] using hc)
      simp only [Sum.elim_inl, hv]
      exact X.vertexOf_mem_internalVertices.2 (hPg.2.2 _ hk).1
    · obtain ⟨h1, h2⟩ : 1 ≤ i ∧ i ≤ M := by simpa [pointSet] using hc
      obtain ⟨hk, hv⟩ := hpy i h1 h2
      simp only [Sum.elim_inr, hv]
      exact X.vertexOf_mem_internalVertices.2 (hQg.2.2 _ hk).1
  · rintro (j | i) hc (j' | i') hc' h
    · obtain ⟨hk, hv⟩ := hpx j (by simpa [pointSet] using hc)
      obtain ⟨hk', hv'⟩ := hpx j' (by simpa [pointSet] using hc')
      simp only [Sum.elim_inl, hv, hv'] at h
      rw [hpxinj j (by simpa [pointSet] using hc) j' (by simpa [pointSet] using hc')
        (eq_of_vertexOf_inv_eq hQ.isSimpleStrandPath hk hk' h)]
    · obtain ⟨hk, hv⟩ := hpx j (by simpa [pointSet] using hc)
      obtain ⟨h1, h2⟩ : 1 ≤ i' ∧ i' ≤ M := by simpa [pointSet] using hc'
      simp only [Sum.elim_inl, Sum.elim_inr] at h
      exact absurd (h.symm.trans hv) (hy i' h1 h2 _ (List.getElem_mem _)).2
    · obtain ⟨hk, hv⟩ := hpx j' (by simpa [pointSet] using hc')
      obtain ⟨h1, h2⟩ : 1 ≤ i ∧ i ≤ M := by simpa [pointSet] using hc
      simp only [Sum.elim_inl, Sum.elim_inr] at h
      exact absurd (h.trans hv) (hy i h1 h2 _ (List.getElem_mem _)).2
    · obtain ⟨h1, h2⟩ : 1 ≤ i ∧ i ≤ M := by simpa [pointSet] using hc
      obtain ⟨h1', h2'⟩ : 1 ≤ i' ∧ i' ≤ M := by simpa [pointSet] using hc'
      obtain ⟨hk, hv⟩ := hpy i h1 h2
      obtain ⟨hk', hv'⟩ := hpy i' h1' h2'
      simp only [Sum.elim_inr, hv, hv'] at h
      rw [hpyinj i i' h1 h2 h1' h2' (eq_of_nodup_interiorPoints hQnd hk hk' h)]

/-- A closed aligned rail from its points and its relations. -/
private def closedAlignedRailOf {n : ℕ} (hn : 1 ≤ n) (RP : X.RailPoints n (n - 1))
    (h3 : ∀ j < n - 1, X.inv (X.railDart RP.rho RP.eta (rho j 3)) =
      X.railDart RP.rho RP.eta (rho (j + 1) 0))
    (he3 : ∀ j < n - 1, X.inv (X.railDart RP.rho RP.eta (alignedEta j 3)) =
      X.railDart RP.rho RP.eta (eta (j + 1) 0))
    (h1 : ∀ j, 1 ≤ j → j ≤ n - 1 → X.inv (X.railDart RP.rho RP.eta (rho j 1)) =
      X.railDart RP.rho RP.eta (eta j 5))
    (h2 : ∀ j, 1 ≤ j → j ≤ n - 1 → X.inv (X.railDart RP.rho RP.eta (rho j 2)) =
      X.railDart RP.rho RP.eta (eta j 4))
    (h3l : X.inv (X.railDart RP.rho RP.eta (rho (n - 1) 3)) =
      X.railDart RP.rho RP.eta (rho n 0))
    (he3l : X.inv (X.railDart RP.rho RP.eta (alignedEta (n - 1) 3)) =
      X.railDart RP.rho RP.eta (rho n 1)) : X.ClosedAlignedRail n where
  rho := RP.rho
  eta := RP.eta
  vertexOf_mem c hc := RP.vertexOf_mem c ((mem_pointSet_iff_eq_or_mem hn).2 (Or.inr hc))
  injOn_vertexOf c hc c' hc' h := RP.injOn_vertexOf ((mem_pointSet_iff_eq_or_mem hn).2
    (Or.inr hc)) ((mem_pointSet_iff_eq_or_mem hn).2 (Or.inr hc')) h
  inv_rho_three := h3
  inv_eta_three := he3
  inv_rho_one := h1
  inv_rho_two := h2
  one_le := hn
  vertexOf_rho_mem := RP.vertexOf_mem (Sum.inl n) ((mem_pointSet_iff_eq_or_mem hn).2 (Or.inl rfl))
  vertexOf_rho_ne c hc h := by
    have := RP.injOn_vertexOf ((mem_pointSet_iff_eq_or_mem hn).2 (Or.inl rfl))
      ((mem_pointSet_iff_eq_or_mem hn).2 (Or.inr hc)) h
    subst this
    simp [pointSet] at hc
    omega
  inv_rho_three_last := h3l
  inv_eta_three_last := he3l

/-- **A hugging anti-parallel returning path gives a closed aligned rail**. Let `P = (e₁, …, e_m)`
be a simple strand path, `ζ` a side, and `Q = (f₁, …, f_n)` an anti-parallel returning path of `P`
on side `ζ` from `z_{a+1}` to `z_{b+1}` (`0`-indexed `a > b`) that hugs `P`. Then `X` has a closed
aligned rail of length `n` along `P` on side `ζ`, whose points are `z_{b+1}, …, z_{a+1}` and the
interior points of `Q`, and whose darts `ρ_{0,2}`, `ρ_{n,1}` are `f₁` and `f̄_n` in some order. -/
@[cluster_algebras "lem_antiparallel_hug_rail"]
theorem Hugs.exists_closedAlignedRail (hX : X.IsPreTripleDiagram) {P Q : List H}
    {ζ : StrandSide} {a b : ℕ} (hQ : X.Hugs P ζ Q a b) (hba : b < a) :
    ∃ R : X.ClosedAlignedRail Q.length, R.IsAlong P ζ ∧
      (∀ v, (∃ c ∈ pointSet Q.length (Q.length - 1), X.vertexOf (Sum.elim R.rho R.eta c) = v) ↔
        ((∃ l, b ≤ l ∧ l ≤ a ∧ (X.interiorPoints P)[l]? = some v) ∨
          v ∈ X.interiorPoints Q)) ∧
      ∀ f₁ ∈ Q.head?, ∀ fₙ ∈ Q.getLast?,
        (R.railPoints.dart (rho 0 2) = f₁ ∧ R.railPoints.dart (rho Q.length 1) = X.inv fₙ) ∨
        (R.railPoints.dart (rho 0 2) = X.inv fₙ ∧ R.railPoints.dart (rho Q.length 1) = f₁) := by
  have hR := hQ.isReturningPath
  have hP := hR.isSimpleStrandPath
  have hPg := X.isStrandPath_iff_getElem.1 hP.isStrandPath
  have hQg := X.isStrandPath_iff_getElem.1 hR.isStrandPath
  have hQne := hR.isStrandPath.ne_nil
  have ha := hR.lt_left
  have hb := hR.lt_right
  have hn1 : 1 ≤ Q.length := List.length_pos_iff.2 hQne
  obtain ⟨f₁, hf₁⟩ : ∃ f, Q.head? = some f := ⟨_, List.head?_eq_some_head hQne⟩
  obtain ⟨fₙ, hfₙ⟩ : ∃ f, Q.getLast? = some f := ⟨_, List.getLast?_eq_some_getLast hQne⟩
  have hf₁0 : f₁ = Q[0] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hf₁
    exact (Option.some_inj.1 hf₁).symm
  have hfₙ0 : fₙ = Q[Q.length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hfₙ
    exact (Option.some_inj.1 hfₙ).symm
  have hQout : ∀ k (hk : k < Q.length), X.isOut (X.inv Q[k]) = false := fun k hk => by
    rw [hX.isOut_inv_apply (hQg.2.1 k hk).1, (hQg.2.1 k hk).2]; rfl
  have hPout : ∀ k (hk : k < P.length), X.isOut (X.inv P[k]) = false := fun k hk => by
    rw [hX.isOut_inv_apply (hPg.2.1 k hk).1, (hPg.2.1 k hk).2]; rfl
  have hPtp : ∀ k (hk : k + 1 < P.length), ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[k])) :=
    fun k hk => (hPg.2.2 k hk).1
  have hQtp : ∀ k (hk : k + 1 < Q.length), ¬X.IsBoundaryVertex (X.vertexOf (X.inv Q[k])) :=
    fun k hk => (hQg.2.2 k hk).1
  have hQstep : ∀ k (hk : k + 1 < Q.length), (X.rot ^ 3) (X.inv Q[k]) = Q[k + 1] :=
    fun k hk => rot_pow_three_inv_getElem hR.isStrandPath hk
  have hPstep : ∀ k (hk : k + 1 < P.length), (X.rot ^ 3) (X.inv P[k]) = P[k + 1] :=
    fun k hk => rot_pow_three_inv_getElem hP.isStrandPath hk
  obtain ⟨e, he, f, hf, hfe⟩ := hR.head?_mem
  obtain ⟨e', he', f', hf', hfe'⟩ := hR.getLast?_mem
  rw [List.getElem?_eq_getElem (by omega), Option.mem_def, Option.some_inj] at he he'
  rw [Option.mem_def, hf₁, Option.some_inj] at hf
  rw [Option.mem_def, hfₙ, Option.some_inj] at hf'
  subst he he' hf hf'
  have hf₁out : X.isOut f₁ = true := by rw [hf₁0]; exact (hQg.2.1 0 (by omega)).2
  have hfₙin : X.isOut (X.inv fₙ) = false := by rw [hfₙ0]; exact hQout _ (by omega)
  have hlen := hQ.length_hugDarts
  have hhug := hQ.inv_hugDarts
  have hLl := length_sideList (X := X) ζ P
  have hLnd : (X.sideList ζ P).Nodup := nodup_sideList hX hP ζ
  have hidx : ∀ {i : ℕ} {x : H}, (X.sideList ζ P)[i]? = some x →
      (X.sideList ζ P).idxOf x = i := by
    intro i x h
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
    exact hLnd.idxOf_getElem i hi
  have hinfix : ∀ s k, ((X.sideList ζ P).drop s).take k <:+: X.sideList ζ P := fun s k =>
    (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix
  have hmod : ∀ d, ¬X.IsBoundaryVertex (X.vertexOf d) → ∀ k k',
      (X.rot ^ k) ((X.rot ^ k') d) = (X.rot ^ ((k + k') % 6)) d := by
    intro d hd k k'
    rw [← Equiv.Perm.mul_apply, ← pow_add, hX.rot_pow_mod_six hd]
  cases ζ with
  | right =>
    have hf₁e : f₁ = X.rot (X.inv P[a]) := by
      simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hfe
      rcases hfe with h | h
      · exact h
      · exfalso
        rw [h, hX.isOut_rot_pow_apply (hPtp a ha), hPout a (by omega)] at hf₁out
        simp at hf₁out
    have hfₙe : X.inv fₙ = (X.rot ^ 2) (X.inv P[b]) := by
      simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hfe'
      rcases hfe' with h | h
      · exfalso
        rw [h, hX.isOut_rot_apply (hPtp b hb), hPout b (by omega)] at hfₙin
        simp at hfₙin
      · exact h
    have hLa : (X.sideList .right P)[2 * a]? = some f₁ := by
      rw [show 2 * a = 2 * a + 0 from rfl, getElem?_sideList_right (by norm_num) (by omega), hf₁e,
        zero_add, pow_one]
    have hLb : (X.sideList .right P)[2 * b + 1]? = some (X.inv fₙ) := by
      rw [getElem?_sideList_right (by norm_num) (by omega), hfₙe]
    have hJ : X.hugDarts P .right Q =
        (((X.sideList .right P).take (2 * a)).drop (2 * b + 2)).reverse := by
      simp only [hugDarts, hf₁, hfₙ, hidx hLa, hidx hLb]
      rw [if_neg (by omega)]
    have hna : Q.length = a - b := by
      rw [hJ] at hlen
      simp only [List.length_reverse, List.length_drop, List.length_take, hLl] at hlen
      omega
    have hJk : ∀ k, k < 2 * (Q.length - 1) → (X.hugDarts P .right Q)[k]? =
        (X.sideList .right P)[2 * a - 1 - k]? := by
      intro k hk
      rw [hJ, List.getElem?_reverse (by simp [hLl]; omega)]
      simp only [List.length_drop, List.length_take, hLl, List.getElem?_drop, List.getElem?_take]
      rw [if_pos (by omega)]
      congr 1
      omega
    have hexp : hugExponent .right a b = 1 := by simp [hugExponent, hba]
    have hug1 : ∀ j (hj : j < Q.length - 1),
        X.inv ((X.rot ^ 2) (X.inv (P[a - 1 - j]'(by omega)))) =
          X.rot (X.inv (Q[j]'(by omega))) := by
      intro j hj
      have h := (hhug j hj).1
      rw [hJk _ (by omega), show 2 * a - 1 - 2 * j = 2 * (a - 1 - j) + 1 by omega,
        getElem?_sideList_right (by norm_num) (by omega), List.getElem?_eq_getElem (by omega),
        hexp] at h
      simpa using h
    have hug2 : ∀ j (hj : j < Q.length - 1),
        X.inv (X.rot (X.inv (P[a - 1 - j]'(by omega)))) =
          (X.rot ^ 2) (X.inv (Q[j]'(by omega))) := by
      intro j hj
      have h := (hhug j hj).2
      rw [hJk _ (by omega), show 2 * a - 1 - (2 * j + 1) = 2 * (a - 1 - j) + 0 by omega,
        getElem?_sideList_right (by norm_num) (by omega), List.getElem?_eq_getElem (by omega),
        hexp, show (2 : ℤ) * 1 = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
      simpa using h
    obtain ⟨rho, hrho⟩ : ∃ rho : ℕ → H, ∀ k (hk : k ≤ Q.length),
        rho k = X.inv (P[b + k]'(by omega)) :=
      ⟨fun k => X.inv ((P[b + k]?).getD f₁), fun k hk => by
        simp [List.getElem?_eq_getElem (show b + k < P.length by omega)]⟩
    obtain ⟨eta, heta⟩ : ∃ eta : ℕ → H, ∀ i (h1 : 1 ≤ i) (h2 : i ≤ Q.length - 1),
        eta i = Q[Q.length - i]'(by omega) :=
      ⟨fun i => (Q[Q.length - i]?).getD f₁, fun i h1 h2 => by
        simp [List.getElem?_eq_getElem (show Q.length - i < Q.length by omega)]⟩
    have heta3 : ∀ i (h1 : 1 ≤ i) (h2 : i ≤ Q.length - 1),
        eta i = (X.rot ^ 3) (X.inv (Q[Q.length - 1 - i]'(by omega))) := fun i h1 h2 => by
      rw [heta i h1 h2, hQstep _ (by omega)]
      exact getElem_idx Q (by omega) _
    have hfacts := railPoints_of_returning hR hQ.nodup (N := Q.length) (M := Q.length - 1)
      (rho := rho) (eta := eta) (px := fun j => b + j) (py := fun i => Q.length - 1 - i)
      (fun j hj => ⟨by omega, by rw [hrho j hj]⟩) (fun j _ j' _ h => by omega)
      (fun i h1 h2 => ⟨by omega, by rw [heta3 i h1 h2, X.vertexOf_rot_pow_apply]⟩)
      (fun i i' _ _ _ _ h => by omega)
    let RP : X.RailPoints Q.length (Q.length - 1) := ⟨rho, eta, hfacts.1, hfacts.2.1⟩
    have hrd : ∀ j k, X.railDart RP.rho RP.eta (RailLabel.rho j k) = (X.rot ^ k) (rho j) :=
      fun _ _ => rfl
    have hed : ∀ j k, X.railDart RP.rho RP.eta (RailLabel.eta j k) = (X.rot ^ k) (eta j) :=
      fun _ _ => rfl
    have hP_a : X.inv (P[b + Q.length]'(by omega)) = X.inv (P[a]'(by omega)) := by
      congr 1
      exact getElem_idx P (by omega) _
    have h3 : ∀ j ≤ Q.length - 1, X.inv (X.railDart RP.rho RP.eta (RailLabel.rho j 3)) =
        X.railDart RP.rho RP.eta (RailLabel.rho (j + 1) 0) := by
      intro j hj
      rw [hrd, hrd, hrho j (by omega), hrho (j + 1) (by omega), pow_zero, Equiv.Perm.one_apply,
        hPstep (b + j) (by omega)]
      rfl
    have he3 : ∀ j ≤ Q.length - 1, X.inv (X.railDart RP.rho RP.eta (alignedEta j 3)) =
        if j + 1 < Q.length then X.railDart RP.rho RP.eta (RailLabel.eta (j + 1) 0)
        else X.railDart RP.rho RP.eta (RailLabel.rho Q.length 1) := by
      intro j hj
      rcases j with _ | j
      · change X.inv ((X.rot ^ 2) (rho 0)) = _
        rw [hrho 0 (by omega), getElem_idx P (Nat.add_zero b), ← hfₙe, hX.inv_inv_apply]
        split_ifs with h
        · rw [hed, heta 1 le_rfl (by omega), pow_zero, Equiv.Perm.one_apply, hfₙ0]
        · rw [hrd, hrho _ le_rfl, hP_a, pow_one, ← hf₁e, hfₙ0, hf₁0]
          exact getElem_idx Q (by omega) _
      · simp only [alignedEta, if_neg (Nat.succ_ne_zero j)]
        rw [hed, heta3 (j + 1) (by omega) (by omega),
          hX.rot_pow_three_rot_pow_three (hQtp _ (by omega)), hX.inv_inv_apply]
        split_ifs with h
        · rw [hed, heta (j + 1 + 1) (by omega) (by omega), pow_zero, Equiv.Perm.one_apply]
          exact getElem_idx Q (by omega) _
        · rw [hrd, hrho _ le_rfl, hP_a, pow_one, ← hf₁e, hf₁0]
          exact getElem_idx Q (by omega) _
    have h1 : ∀ j, 1 ≤ j → j ≤ Q.length - 1 →
        X.inv (X.railDart RP.rho RP.eta (RailLabel.rho j 1)) =
          X.railDart RP.rho RP.eta (RailLabel.eta j 5) := by
      intro j hj1 hj2
      rw [hrd, hed, hrho j (by omega), heta3 j hj1 hj2, hmod _ (hQtp _ (by omega)), pow_one]
      have := hug2 (Q.length - 1 - j) (by omega)
      rw [getElem_idx P (show a - 1 - (Q.length - 1 - j) = b + j by omega)] at this
      exact this
    have h2 : ∀ j, 1 ≤ j → j ≤ Q.length - 1 →
        X.inv (X.railDart RP.rho RP.eta (RailLabel.rho j 2)) =
          X.railDart RP.rho RP.eta (RailLabel.eta j 4) := by
      intro j hj1 hj2
      rw [hrd, hed, hrho j (by omega), heta3 j hj1 hj2, hmod _ (hQtp _ (by omega)),
        show (4 + 3) % 6 = 1 from rfl, pow_one]
      have := hug1 (Q.length - 1 - j) (by omega)
      rw [getElem_idx P (show a - 1 - (Q.length - 1 - j) = b + j by omega)] at this
      exact this
    let R := closedAlignedRailOf (X := X) hn1 RP (fun j hj => h3 j (by omega))
      (fun j hj => by rw [he3 j (by omega), if_pos (by omega)])
      h1 h2 (by have := h3 (Q.length - 1) le_rfl; rwa [Nat.sub_add_cancel hn1] at this)
      (by rw [he3 _ le_rfl, if_neg (by omega)])
    have hRrho : ∀ j, R.rho j = rho j := fun _ => rfl
    have hReta : ∀ j, R.eta j = eta j := fun _ => rfl
    have hRd : ∀ j k, R.railPoints.dart (RailLabel.rho j k) = (X.rot ^ k) (rho j) :=
      fun _ _ => rfl
    have hfacing : R.railPoints.facingDarts =
        ((X.sideList .right P).drop (2 * b)).take (2 * (Q.length + 1)) := by
      apply List.ext_getElem?
      intro k
      by_cases hk : k < 2 * (Q.length + 1)
      · rw [RailPoints.getElem?_facingDarts _ hk, List.getElem?_take, if_pos hk,
          List.getElem?_drop, show 2 * b + k = 2 * (b + k / 2) + k % 2 by omega,
          getElem?_sideList_right (by omega) (by omega), hRd, hrho _ (by omega)]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    refine ⟨R, ⟨hfacing ▸ hinfix _ _, hfacts.2.2⟩, fun v => ?_, ?_⟩
    · constructor
      · rintro ⟨(j | i), hc, rfl⟩
        · have hj : j ≤ Q.length := by simpa [pointSet] using hc
          refine Or.inl ⟨b + j, by omega, by omega, ?_⟩
          rw [getElem?_interiorPoints (by omega)]
          simp only [Sum.elim_inl, hRrho, hrho j hj]
        · obtain ⟨h1, h2⟩ : 1 ≤ i ∧ i ≤ Q.length - 1 := by simpa [pointSet] using hc
          refine Or.inr (mem_interiorPoints_iff_exists_getElem.2 ⟨Q.length - 1 - i, by omega, ?_⟩)
          simp only [Sum.elim_inr, hReta, heta3 i h1 h2, X.vertexOf_rot_pow_apply]
      · rintro (⟨l, hl1, hl2, hl⟩ | hv)
        · refine ⟨Sum.inl (l - b), by simp [pointSet]; omega, ?_⟩
          rw [getElem?_interiorPoints (by omega), Option.some_inj] at hl
          rw [← hl]
          simp only [Sum.elim_inl, hRrho, hrho _ (by omega : l - b ≤ Q.length)]
          congr 2
          exact getElem_idx P (by omega) _
        · obtain ⟨k, hk, rfl⟩ := mem_interiorPoints_iff_exists_getElem.1 hv
          refine ⟨Sum.inr (Q.length - 1 - k), by simp [pointSet]; omega, ?_⟩
          simp only [Sum.elim_inr, hReta, heta3 _ (by omega : 1 ≤ Q.length - 1 - k)
            (by omega), X.vertexOf_rot_pow_apply]
          congr 2
          exact getElem_idx Q (by omega) _
    · intro g₁ hg₁ gₙ hgₙ
      rw [Option.mem_def, hf₁, Option.some_inj] at hg₁
      rw [Option.mem_def, hfₙ, Option.some_inj] at hgₙ
      subst hg₁ hgₙ
      right
      refine ⟨?_, ?_⟩
      · rw [hRd, hrho 0 (by omega), getElem_idx P (Nat.add_zero b), hfₙe]
      · rw [hRd, hrho _ le_rfl, hP_a, pow_one, hf₁e]
  | left =>
    have hf₁e : f₁ = (X.rot ^ 5) (X.inv P[a]) := by
      simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hfe
      rcases hfe with h | h
      · exfalso
        rw [h, hX.isOut_rot_pow_apply (hPtp a ha), hPout a (by omega)] at hf₁out
        simp [show Even 4 by decide] at hf₁out
      · exact h
    have hfₙe : X.inv fₙ = (X.rot ^ 4) (X.inv P[b]) := by
      simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hfe'
      rcases hfe' with h | h
      · exact h
      · exfalso
        rw [h, hX.isOut_rot_pow_apply (hPtp b hb), hPout b (by omega)] at hfₙin
        simp [show ¬Even 5 by decide] at hfₙin
    have hLa : (X.sideList .left P)[2 * (P.length - 2 - a) + 1]? = some f₁ := by
      rw [getElem?_sideList_left (by norm_num) (by omega), hf₁e]
      congr 3
      exact getElem_idx P (by omega) _
    have hLb : (X.sideList .left P)[2 * (P.length - 2 - b)]? = some (X.inv fₙ) := by
      rw [show 2 * (P.length - 2 - b) = 2 * (P.length - 2 - b) + 0 from rfl,
        getElem?_sideList_left (by norm_num) (by omega), hfₙe]
      congr 3
      exact getElem_idx P (by omega) _
    have hJ : X.hugDarts P .left Q = ((X.sideList .left P).drop
        (2 * (P.length - 2 - a) + 2)).take (2 * (a - b) - 2) := by
      simp only [hugDarts, hf₁, hfₙ, hidx hLa, hidx hLb]
      rw [if_pos (by omega), show 2 * (P.length - 2 - a) + 1 + 1 = 2 * (P.length - 2 - a) + 2 by
        omega, show 2 * (P.length - 2 - b) - (2 * (P.length - 2 - a) + 1) - 1 = 2 * (a - b) - 2 by
        omega]
    have hna : Q.length = a - b := by
      rw [hJ] at hlen
      simp only [List.length_drop, List.length_take, hLl] at hlen
      omega
    have hJk : ∀ k, k < 2 * (Q.length - 1) → (X.hugDarts P .left Q)[k]? =
        (X.sideList .left P)[2 * (P.length - 2 - a) + 2 + k]? := by
      intro k hk
      rw [hJ, List.getElem?_take, if_pos (by omega), List.getElem?_drop]
    have hexp : hugExponent .left a b = -1 := by simp [hugExponent, hba]
    have hug1 : ∀ j (hj : j < Q.length - 1),
        X.inv ((X.rot ^ 4) (X.inv (P[a - 1 - j]'(by omega)))) =
          (X.rot ^ 5) (X.inv (Q[j]'(by omega))) := by
      intro j hj
      have h := (hhug j hj).1
      rw [hJk _ (by omega), show 2 * (P.length - 2 - a) + 2 + 2 * j =
          2 * (P.length - 2 - a + 1 + j) + 0 by omega,
        getElem?_sideList_left (by norm_num) (by omega), List.getElem?_eq_getElem (by omega),
        hexp] at h
      simp only [Option.map_some, Option.some_inj, zero_add] at h
      rw [← rot_zpow_neg_one_eq (hX.rot_pow_six_apply (hQtp j (by omega))), ← h]
      congr 3
      exact getElem_idx P (by omega) _
    have hug2 : ∀ j (hj : j < Q.length - 1),
        X.inv ((X.rot ^ 5) (X.inv (P[a - 1 - j]'(by omega)))) =
          (X.rot ^ 4) (X.inv (Q[j]'(by omega))) := by
      intro j hj
      have h := (hhug j hj).2
      rw [hJk _ (by omega), show 2 * (P.length - 2 - a) + 2 + (2 * j + 1) =
          2 * (P.length - 2 - a + 1 + j) + 1 by omega,
        getElem?_sideList_left (by norm_num) (by omega), List.getElem?_eq_getElem (by omega),
        hexp] at h
      simp only [Option.map_some, Option.some_inj] at h
      rw [← rot_zpow_neg_two_eq (hX.rot_pow_six_apply (hQtp j (by omega))), ← h]
      congr 3
      exact getElem_idx P (by omega) _
    obtain ⟨rho, hrho⟩ : ∃ rho : ℕ → H, ∀ k (hk : k ≤ Q.length),
        rho k = P[a - k + 1]'(by omega) :=
      ⟨fun k => (P[a - k + 1]?).getD f₁, fun k hk => by
        simp [List.getElem?_eq_getElem (show a - k + 1 < P.length by omega)]⟩
    have hrho3 : ∀ k (hk : k ≤ Q.length),
        rho k = (X.rot ^ 3) (X.inv (P[a - k]'(by omega))) := fun k hk => by
      rw [hrho k hk, hPstep _ (by omega)]
    obtain ⟨eta, heta⟩ : ∃ eta : ℕ → H, ∀ i (h1 : 1 ≤ i) (h2 : i ≤ Q.length - 1),
        eta i = X.inv (Q[i - 1]'(by omega)) :=
      ⟨fun i => X.inv ((Q[i - 1]?).getD f₁), fun i h1 h2 => by
        simp [List.getElem?_eq_getElem (show i - 1 < Q.length by omega)]⟩
    have hfacts := railPoints_of_returning hR hQ.nodup (N := Q.length) (M := Q.length - 1)
      (rho := rho) (eta := eta) (px := fun j => a - j) (py := fun i => i - 1)
      (fun j hj => ⟨by omega, by rw [hrho3 j hj, X.vertexOf_rot_pow_apply]⟩)
      (fun j _ j' _ h => by omega)
      (fun i h1 h2 => ⟨by omega, by rw [heta i h1 h2]⟩)
      (fun i i' _ _ _ _ h => by omega)
    let RP : X.RailPoints Q.length (Q.length - 1) := ⟨rho, eta, hfacts.1, hfacts.2.1⟩
    have hrd : ∀ j k, X.railDart RP.rho RP.eta (RailLabel.rho j k) = (X.rot ^ k) (rho j) :=
      fun _ _ => rfl
    have hed : ∀ j k, X.railDart RP.rho RP.eta (RailLabel.eta j k) = (X.rot ^ k) (eta j) :=
      fun _ _ => rfl
    have hP_b : X.inv (P[a - Q.length]'(by omega)) = X.inv (P[b]'(by omega)) := by
      congr 1
      exact getElem_idx P (by omega) _
    have hrhon : (X.rot ^ 1) (rho Q.length) = X.inv fₙ := by
      rw [hrho3 _ le_rfl, hmod _ (hPtp _ (by omega)), hP_b, hfₙe]
    have hrho0 : (X.rot ^ 2) (rho 0) = f₁ := by
      rw [hrho3 0 (by omega), hmod _ (hPtp _ (by omega)), hf₁e]
      rfl
    have h3 : ∀ j ≤ Q.length - 1, X.inv (X.railDart RP.rho RP.eta (RailLabel.rho j 3)) =
        X.railDart RP.rho RP.eta (RailLabel.rho (j + 1) 0) := by
      intro j hj
      rw [hrd, hrd, hrho3 j (by omega), hX.rot_pow_three_rot_pow_three (hPtp _ (by omega)),
        hX.inv_inv_apply, pow_zero, Equiv.Perm.one_apply, hrho (j + 1) (by omega)]
      exact getElem_idx P (by omega) _
    have he3 : ∀ j ≤ Q.length - 1, X.inv (X.railDart RP.rho RP.eta (alignedEta j 3)) =
        if j + 1 < Q.length then X.railDart RP.rho RP.eta (RailLabel.eta (j + 1) 0)
        else X.railDart RP.rho RP.eta (RailLabel.rho Q.length 1) := by
      intro j hj
      rcases j with _ | j
      · change X.inv ((X.rot ^ 2) (rho 0)) = _
        rw [hrho0]
        split_ifs with h
        · rw [hed, heta 1 le_rfl (by omega), pow_zero, Equiv.Perm.one_apply, hf₁0]
          rfl
        · rw [hrd, hrhon, hfₙ0, hf₁0]
          congr 1
          exact getElem_idx Q (by omega) _
      · simp only [alignedEta, if_neg (Nat.succ_ne_zero j)]
        rw [hed, heta (j + 1) (by omega) (by omega), hQstep _ (by omega)]
        split_ifs with h
        · rw [hed, heta (j + 1 + 1) (by omega) (by omega), pow_zero, Equiv.Perm.one_apply]
          rfl
        · rw [hrd, hrhon, hfₙ0]
          congr 1
          exact getElem_idx Q (by omega) _
    have h1 : ∀ j, 1 ≤ j → j ≤ Q.length - 1 →
        X.inv (X.railDart RP.rho RP.eta (RailLabel.rho j 1)) =
          X.railDart RP.rho RP.eta (RailLabel.eta j 5) := by
      intro j hj1 hj2
      rw [hrd, hed, hrho3 j (by omega), heta j hj1 hj2, hmod _ (hPtp _ (by omega))]
      have := hug1 (j - 1) (by omega)
      rw [getElem_idx P (show a - 1 - (j - 1) = a - j by omega)] at this
      exact this
    have h2 : ∀ j, 1 ≤ j → j ≤ Q.length - 1 →
        X.inv (X.railDart RP.rho RP.eta (RailLabel.rho j 2)) =
          X.railDart RP.rho RP.eta (RailLabel.eta j 4) := by
      intro j hj1 hj2
      rw [hrd, hed, hrho3 j (by omega), heta j hj1 hj2, hmod _ (hPtp _ (by omega))]
      have := hug2 (j - 1) (by omega)
      rw [getElem_idx P (show a - 1 - (j - 1) = a - j by omega)] at this
      exact this
    let R := closedAlignedRailOf (X := X) hn1 RP (fun j hj => h3 j (by omega))
      (fun j hj => by rw [he3 j (by omega), if_pos (by omega)])
      h1 h2 (by have := h3 (Q.length - 1) le_rfl; rwa [Nat.sub_add_cancel hn1] at this)
      (by rw [he3 _ le_rfl, if_neg (by omega)])
    have hRrho : ∀ j, R.rho j = rho j := fun _ => rfl
    have hReta : ∀ j, R.eta j = eta j := fun _ => rfl
    have hRd : ∀ j k, R.railPoints.dart (RailLabel.rho j k) = (X.rot ^ k) (rho j) :=
      fun _ _ => rfl
    have hfacing : R.railPoints.facingDarts =
        ((X.sideList .left P).drop (2 * (P.length - 2 - a))).take (2 * (Q.length + 1)) := by
      apply List.ext_getElem?
      intro k
      by_cases hk : k < 2 * (Q.length + 1)
      · rw [RailPoints.getElem?_facingDarts _ hk, List.getElem?_take, if_pos hk,
          List.getElem?_drop, show 2 * (P.length - 2 - a) + k =
            2 * (P.length - 2 - a + k / 2) + k % 2 by omega,
          getElem?_sideList_left (by omega) (by omega), hRd, hrho3 _ (by omega),
          hmod _ (hPtp _ (by omega))]
        congr 3
        · omega
        · exact getElem_idx P (by omega) _
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    refine ⟨R, ⟨hfacing ▸ hinfix _ _, hfacts.2.2⟩, fun v => ?_, ?_⟩
    · constructor
      · rintro ⟨(j | i), hc, rfl⟩
        · have hj : j ≤ Q.length := by simpa [pointSet] using hc
          refine Or.inl ⟨a - j, by omega, by omega, ?_⟩
          rw [getElem?_interiorPoints (by omega)]
          simp only [Sum.elim_inl, hRrho, hrho3 j hj, X.vertexOf_rot_pow_apply]
        · obtain ⟨h1, h2⟩ : 1 ≤ i ∧ i ≤ Q.length - 1 := by simpa [pointSet] using hc
          refine Or.inr (mem_interiorPoints_iff_exists_getElem.2 ⟨i - 1, by omega, ?_⟩)
          simp only [Sum.elim_inr, hReta, heta i h1 h2]
      · rintro (⟨l, hl1, hl2, hl⟩ | hv)
        · refine ⟨Sum.inl (a - l), by simp [pointSet]; omega, ?_⟩
          rw [getElem?_interiorPoints (by omega), Option.some_inj] at hl
          rw [← hl]
          simp only [Sum.elim_inl, hRrho, hrho3 _ (by omega : a - l ≤ Q.length),
            X.vertexOf_rot_pow_apply]
          congr 2
          exact getElem_idx P (by omega) _
        · obtain ⟨k, hk, rfl⟩ := mem_interiorPoints_iff_exists_getElem.1 hv
          refine ⟨Sum.inr (k + 1), by simp [pointSet]; omega, ?_⟩
          simp only [Sum.elim_inr, hReta, heta (k + 1) (by omega) (by omega)]
          rfl
    · intro g₁ hg₁ gₙ hgₙ
      rw [Option.mem_def, hf₁, Option.some_inj] at hg₁
      rw [Option.mem_def, hfₙ, Option.some_inj] at hgₙ
      subst hg₁ hgₙ
      exact Or.inl ⟨by rw [hRd, hrho0], by rw [hRd, hrhon]⟩

end TripleData

end ClusterAlgebras

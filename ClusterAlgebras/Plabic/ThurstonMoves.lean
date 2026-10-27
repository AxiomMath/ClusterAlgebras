/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.MinimalTriple
public import ClusterAlgebras.Plabic.Rails
public import ClusterAlgebras.Plabic.Swivel

/-!
# The push-off and the combings are sequences of swivel moves

FWZ Exercise 7.6.9 asserts three move-equivalences between explicit local pictures of triple
diagrams: the push-off along a closed aligned rail, and the combings along an aligned and along a
staggered rail. This file proves them by exhibiting the swivel moves.

## Main results

* `ClusterAlgebras.TripleDiagram.exists_moveEquivalent_alignedComb`: the aligned combing of an
  aligned rail of length `r ≥ 1` is a triple diagram move-equivalent to the diagram.
* `ClusterAlgebras.TripleDiagram.exists_moveEquivalent_pushOff`: the push-off along a closed
  aligned rail is a triple diagram move-equivalent to the diagram.
* `ClusterAlgebras.TripleDiagram.exists_moveEquivalent_staggeredComb`: the staggered combing of a
  staggered rail is a triple diagram move-equivalent to the diagram.

## The swivel moves

A swivel move does not rename darts, so a move "at `ρ_{j,k}`" is a move at the digon through the
dart that is `ρ_{j,k}` in the original diagram.

* The aligned combing of an aligned rail of length `r` is reached by `2r` moves: for
  `k = 0, …, r - 1`, the moves at `ρ_{k+1,2}` and at `ρ_{k,3}`. After the moves of round `k` the
  rotation is the aligned combing of the rail cut down to length `k + 1`: the round replaces the
  tuple `(η_{k,5}, η_{k,2}, η_{k,3}, ρ_{k,3}, ρ_{k,4}, η_{k,4})` and the rotations at `x_{k+1}` and
  `y_{k+1}` by the three tuples of the combing that involve them.
* The push-off along a closed aligned rail of length `n` is reached by `2n - 1` moves: the
  `2(n - 1)` moves of the aligned combing of its aligned rail of length `n - 1`, then the move at
  `ρ_{n-1,3}`.
* The staggered combing of a staggered rail of length `r` is reached by `2r` moves: for
  `k = 0, …, r - 1`, the moves at `ρ_{k,2}` and at `ρ_{k,3}`.

Each round is a computation on `18` (or `12`) darts, carried out once and for all on labels
`Fin 18` (`Fin 12`): the swivel rotation of a rotation that permutes the darts named by an
injective `w : L → H` as `s : L → L` permutes them as `labelSwivel s` (`swivelRot_apply_label`),
and the digon conditions are conditions on `s` (`isDigon_faceOf_of_label`); both are then checked
by `decide`.

## Implementation notes

* An intermediate diagram `Y` is described relative to the original `X` and a list `T` of tuples of
  rail labels by `TripleData.AgreesOn`: `Y` sends each entry of each tuple to the next one, and
  agrees with `X` on the darts no tuple names. Two diagrams agreeing on the same tuples have the
  same rotation (`AgreesOn.rot_eq`).

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset RailLabel

namespace TripleData

/-! ### Swivel moves on labelled darts -/

/-- The swivel rotation on labels: if a rotation permutes the darts named by `w` as `s`, the
swivel rotation at `w l₁` (with `φ(w l₁) = w l₂`) permutes them as `labelSwivel s l₁ l₂`. It
mirrors `TripleData.swivelRot`. -/
def labelSwivel {L : Type*} [DecidableEq L] (s : L → L) (l₁ l₂ : L) (l : L) : L :=
  s ((Equiv.swap l₁ (s^[4] l₂) * Equiv.swap l₁ (s^[2] l₁))
    ((Equiv.swap (s^[4] l₁) (s^[2] l₂) * Equiv.swap (s^[4] l₁) l₂) l))

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

section Label

variable {L : Type*} [DecidableEq L] {Y : TripleData H b} {w : L → H} {s : L → L}

omit [Fintype H] [DecidableEq H] [DecidableEq L] in
/-- If the rotation permutes the darts named by `w` as `s`, then its `n`-th power permutes them as
`s^[n]`. -/
theorem rot_pow_apply_label (hs : ∀ l, Y.rot (w l) = w (s l)) (n : ℕ) (l : L) :
    (Y.rot ^ n) (w l) = w (s^[n] l) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => rw [pow_succ, Equiv.Perm.mul_apply, hs, ih, Function.iterate_succ_apply]

omit [Fintype H] in
/-- **The swivel rotation on labelled darts.** If `σ` permutes the darts named by an injective `w`
as `s`, and `d̄₁ = w m₁` with `s m₁ = l₂` for `d₁ = w l₁`, then the swivel rotation at `d₁`
permutes them as `labelSwivel s l₁ l₂`, and is `σ` on the other darts. -/
theorem swivelRot_apply_label (hw : Function.Injective w) (hs : ∀ l, Y.rot (w l) = w (s l))
    {l₁ m₁ l₂ : L} (h₁ : Y.inv (w l₁) = w m₁) (h₂ : s m₁ = l₂) :
    (∀ l, Y.swivelRot (w l₁) (w l) = w (labelSwivel s l₁ l₂ l)) ∧
      ∀ z, z ∉ Set.range w → Y.swivelRot (w l₁) z = Y.rot z := by
  have hφ : Y.facePerm (w l₁) = w l₂ := by
    change Y.rot (Y.inv (w l₁)) = _
    rw [h₁, hs, h₂]
  have hp := rot_pow_apply_label hs
  refine ⟨fun l => ?_, fun z hz => ?_⟩
  · simp only [swivelRot, labelSwivel, Equiv.Perm.mul_apply, hφ, hp, hw.swap_apply, hs]
  · have hne : ∀ l, z ≠ w l := fun l h => hz ⟨l, h.symm⟩
    simp only [swivelRot, Equiv.Perm.mul_apply, hφ, hp]
    rw [Equiv.swap_apply_of_ne_of_ne (hne _) (hne _), Equiv.swap_apply_of_ne_of_ne (hne _) (hne _),
      Equiv.swap_apply_of_ne_of_ne (hne _) (hne _), Equiv.swap_apply_of_ne_of_ne (hne _) (hne _)]

end Label

/-- The orbit of `a` under a permutation of a finite type is any set containing `a`, closed under
the permutation, all of whose elements lie in the orbit of `a`. -/
private theorem filter_sameCycle_eq' {α : Type*} [Fintype α] [DecidableEq α] {f : Equiv.Perm α}
    {a : α} {S : Finset α} (ha : a ∈ S) (hS : ∀ y ∈ S, f y ∈ S)
    (hreach : ∀ y ∈ S, f.SameCycle a y) :
    ({e ∈ univ | f.SameCycle a e} : Finset α) = S := by
  ext y
  simp only [mem_filter, mem_univ, true_and]
  refine ⟨fun h => ?_, hreach y⟩
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using ha
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hS _ ih

/-- An internal face of two darts at distinct vertices exchanged by the face permutation is a
digon. -/
theorem isDigon_faceOf_of_facePerm {X : TripleData H b} {d₁ d₂ : H} (h₁ : X.facePerm d₁ = d₂)
    (h₂ : X.facePerm d₂ = d₁) (hB₁ : d₁ ∉ X.bdry) (hB₂ : d₂ ∉ X.bdry)
    (hv : X.vertexOf d₁ ≠ X.vertexOf d₂) : X.IsDigon (X.faceOf d₁) := by
  have hface : X.faceOf d₁ = {d₁, d₂} := by
    refine filter_sameCycle_eq' (by simp) ?_ ?_
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy ⊢
      rcases hy with rfl | rfl
      · exact Or.inr h₁
      · exact Or.inl h₂
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Equiv.Perm.SameCycle.refl _ _
      · exact ⟨1, by rw [zpow_one, h₁]⟩
  rw [hface]
  refine ⟨?_, d₁, by rw [h₁], by rwa [h₁]⟩
  rw [DiskMap.mem_internalFaces, DiskMap.mem_faces]
  refine ⟨⟨fun he => ?_, hface ▸ X.faceOf_mem_faceOrbits d₁⟩, ?_⟩
  · have : d₁ ∈ X.exterior := he ▸ (by simp)
    exact hB₁ (X.exterior_subset_bdry this)
  · rw [disjoint_left]
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    exacts [hB₁, hB₂]

section Label

variable {L : Type*} [DecidableEq L] {Y : TripleData H b} {w : L → H} {s : L → L}

omit [DecidableEq L] in
/-- **A digon on labelled darts.** If `σ` permutes the darts named by an injective `w` as `s`, and
`w l₁, w l₂` are darts outside `B` with `d̄₁ = w m₁`, `s m₁ = l₂`, `d̄₂ = w m₂`, `s m₂ = l₁`, where
`l₂` lies outside a set of labels containing `l₁` and closed under `s`, then `f(w l₁)` is a
digon. -/
theorem isDigon_faceOf_of_label (hw : Function.Injective w) (hs : ∀ l, Y.rot (w l) = w (s l))
    {l₁ m₁ l₂ m₂ : L} (h₁ : Y.inv (w l₁) = w m₁) (h₂ : s m₁ = l₂) (h₃ : Y.inv (w l₂) = w m₂)
    (h₄ : s m₂ = l₁) (hB₁ : w l₁ ∉ Y.bdry) (hB₂ : w l₂ ∉ Y.bdry) (S : Finset L) (hS₁ : l₁ ∈ S)
    (hS : ∀ x ∈ S, s x ∈ S) (hS₂ : l₂ ∉ S) : Y.IsDigon (Y.faceOf (w l₁)) := by
  have hφ₁ : Y.facePerm (w l₁) = w l₂ := by
    change Y.rot (Y.inv (w l₁)) = _
    rw [h₁, hs, h₂]
  have hφ₂ : Y.facePerm (w l₂) = w l₁ := by
    change Y.rot (Y.inv (w l₂)) = _
    rw [h₃, hs, h₄]
  refine isDigon_faceOf_of_facePerm hφ₁ hφ₂ hB₁ hB₂ fun hv => ?_
  have hmem : w l₂ ∈ Y.vertexOf (w l₁) := hv ▸ Y.self_mem_vertexOf _
  obtain ⟨n, hn⟩ := (Y.mem_vertexOf.1 hmem).exists_nat_pow_eq
  rw [rot_pow_apply_label hs] at hn
  have hiter : ∀ n, s^[n] l₁ ∈ S := fun n => by
    induction n with
    | zero => exact hS₁
    | succ n ih => rw [Function.iterate_succ_apply']; exact hS _ ih
  exact hS₂ (hw hn ▸ hiter n)

end Label

/-- A swivel move at a digon of a triple diagram gives a move-equivalent triple diagram. -/
theorem exists_moveEquivalent_swivelMove {H : Type} [Fintype H] [DecidableEq H]
    {Y : TripleData H b} (hY : Y.IsTripleDiagram) {d₁ : H} (hd : Y.IsDigon (Y.faceOf d₁)) :
    ∃ h : (Y.swivelMove d₁).IsTripleDiagram,
      TripleDiagram.MoveEquivalent { Dart := H, data := Y, isTripleDiagram := hY }
        { Dart := H, data := Y.swivelMove d₁, isTripleDiagram := h } :=
  ⟨hd.isTripleDiagram_swivelMove hY,
    TripleDiagram.MoveEquivalent.of_isSwivelMove ⟨d₁, hd, Isomorphic.refl _⟩⟩

/-- **One swivel move on labelled darts.** Under the hypotheses of `isDigon_faceOf_of_label`, the
swivel move at `w l₁` is a triple diagram move-equivalent to `Y`, it permutes the darts named by
`w` as `labelSwivel s l₁ l₂`, and it agrees with `Y` on the other darts. -/
theorem exists_swivelMove_label {H : Type} [Fintype H] [DecidableEq H] {L : Type*}
    [DecidableEq L] {Y : TripleData H b} (hY : Y.IsTripleDiagram) {w : L → H}
    (hw : Function.Injective w) {s : L → L} (hs : ∀ l, Y.rot (w l) = w (s l))
    {l₁ m₁ l₂ m₂ : L} (h₁ : Y.inv (w l₁) = w m₁) (h₂ : s m₁ = l₂) (h₃ : Y.inv (w l₂) = w m₂)
    (h₄ : s m₂ = l₁) (hB₁ : w l₁ ∉ Y.bdry) (hB₂ : w l₂ ∉ Y.bdry) (S : Finset L) (hS₁ : l₁ ∈ S)
    (hS : ∀ x ∈ S, s x ∈ S) (hS₂ : l₂ ∉ S) :
    ∃ h : (Y.swivelMove (w l₁)).IsTripleDiagram,
      TripleDiagram.MoveEquivalent { Dart := H, data := Y, isTripleDiagram := hY }
        { Dart := H, data := Y.swivelMove (w l₁), isTripleDiagram := h } ∧
      (∀ l, (Y.swivelMove (w l₁)).rot (w l) = w (labelSwivel s l₁ l₂ l)) ∧
      ∀ z, z ∉ Set.range w → (Y.swivelMove (w l₁)).rot z = Y.rot z := by
  obtain ⟨h, hmv⟩ := exists_moveEquivalent_swivelMove hY
    (isDigon_faceOf_of_label hw hs h₁ h₂ h₃ h₄ hB₁ hB₂ S hS₁ hS hS₂)
  exact ⟨h, hmv, swivelRot_apply_label hw hs h₁ h₂⟩

/-! ### The three local computations -/

/-- The rotation of three triple points `u = (0, …, 5)`, `p = (6, …, 11)`, `q = (12, …, 17)`. -/
def cyc18 : Fin 18 → Fin 18 := ![1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 6, 13, 14, 15, 16, 17, 12]

/-- The rotation of two triple points `u = (0, …, 5)`, `p = (6, …, 11)`. -/
def cyc12 : Fin 12 → Fin 12 := ![1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 6]

/-- The cycles `(u₀, u₁, q₁, p₁, u₂, u₃)`, `(q₅, q₂, q₃, p₃, p₄, q₄)`, `(p₂, p₅, u₄, u₅, p₀, q₀)`
of one round of the aligned combing. -/
def alignedRound : Fin 18 → Fin 18 :=
  ![1, 13, 3, 0, 5, 6, 12, 2, 11, 10, 16, 4, 8, 7, 15, 9, 17, 14]

/-- The cycles `(u₀, q₁, q₂, u₁, u₂, u₅)`, `(q₀, q₃, p₂, p₃, q₄, u₃)`, `(p₀, p₁, p₄, p₅, u₄, q₅)`
of one round of the staggered combing. -/
def staggeredRound : Fin 18 → Fin 18 :=
  ![13, 2, 5, 12, 17, 0, 7, 10, 9, 16, 11, 4, 15, 14, 1, 8, 3, 6]

/-- The cycles `(u₀, u₁, p₂, p₃, u₂, u₃)`, `(p₄, p₅, u₄, u₅, p₀, p₁)` of the last move of the
push-off. -/
def pushOffRound : Fin 12 → Fin 12 := ![1, 8, 3, 0, 5, 6, 7, 10, 9, 2, 11, 4]

/-- The swivel moves at labels `8` and then `3` turn `cyc18` into `alignedRound`. -/
theorem labelSwivel_alignedRound : labelSwivel (labelSwivel cyc18 8 17) 3 12 = alignedRound := by
  decide +kernel

/-- The swivel moves at labels `2` and then `3` turn `cyc18` into `staggeredRound`. -/
theorem labelSwivel_staggeredRound :
    labelSwivel (labelSwivel cyc18 2 12) 3 7 = staggeredRound := by
  decide +kernel

/-- The swivel move at label `3` turns `cyc12` into `pushOffRound`. -/
theorem labelSwivel_pushOffRound : labelSwivel cyc12 3 7 = pushOffRound := by
  decide +kernel

variable {H : Type} [Fintype H] [DecidableEq H]

/-- **One round of the aligned combing.** Let `u, p, q` be three triple points of a triple diagram
`Y`, with darts `w 0, …, w 5`, `w 6, …, w 11`, `w 12, …, w 17` in rotation order, such that
`ū₃ = p₀`, `ū₂ = q₀`, `p̄₁ = q₅` and `p̄₂ = q₄`. The swivel moves at `p₂` and then at `u₃` give a
move-equivalent triple diagram with the cycles `alignedRound` on these darts, and `σ` elsewhere. -/
theorem exists_alignedRound {Y : TripleData H b} (hY : Y.IsTripleDiagram) {w : Fin 18 → H}
    (hw : Function.Injective w) (hs : ∀ l, Y.rot (w l) = w (cyc18 l))
    (h36 : Y.inv (w 3) = w 6) (h212 : Y.inv (w 2) = w 12) (h717 : Y.inv (w 7) = w 17)
    (h816 : Y.inv (w 8) = w 16) (hB : ∀ l, w l ∉ Y.bdry) :
    ∃ h : ((Y.swivelMove (w 8)).swivelMove (w 3)).IsTripleDiagram,
      TripleDiagram.MoveEquivalent { Dart := H, data := Y, isTripleDiagram := hY }
        { Dart := H, data := (Y.swivelMove (w 8)).swivelMove (w 3), isTripleDiagram := h } ∧
      (∀ l, ((Y.swivelMove (w 8)).swivelMove (w 3)).rot (w l) = w (alignedRound l)) ∧
      ∀ z, z ∉ Set.range w → ((Y.swivelMove (w 8)).swivelMove (w 3)).rot z = Y.rot z := by
  have hinv := hY.toIsPreTripleDiagram.inv_involutive
  have h177 : Y.inv (w 17) = w 7 := by rw [← h717, hinv]
  obtain ⟨h₁, hmv₁, hs₁, ho₁⟩ := exists_swivelMove_label hY hw hs h816 (by decide) h177
    (by decide) (hB 8) (hB 17) {6, 7, 8, 9, 10, 11} (by decide) (by decide) (by decide)
  have h122 : Y.inv (w 12) = w 2 := by rw [← h212, hinv]
  obtain ⟨h₂, hmv₂, hs₂, ho₂⟩ := exists_swivelMove_label h₁ hw hs₁ h36 (by decide) h122
    (by decide) (hB 3) (hB 12) {0, 1, 2, 3, 4, 5} (by decide) (by decide) (by decide)
  refine ⟨h₂, hmv₁.trans hmv₂, fun l => ?_, fun z hz => ?_⟩
  · rw [hs₂, labelSwivel_alignedRound]
  · rw [ho₂ z hz, ho₁ z hz]

/-- **One round of the staggered combing.** Let `u, p, q` be three triple points of a triple
diagram `Y`, with darts `w 0, …, w 5`, `w 6, …, w 11`, `w 12, …, w 17` in rotation order, such that
`ū₁ = q₀`, `ū₃ = p₀`, `ū₂ = q₅` and `p̄₁ = q₄`. The swivel moves at `u₂` and then at `u₃` give a
move-equivalent triple diagram with the cycles `staggeredRound` on these darts, and `σ`
elsewhere. -/
theorem exists_staggeredRound {Y : TripleData H b} (hY : Y.IsTripleDiagram) {w : Fin 18 → H}
    (hw : Function.Injective w) (hs : ∀ l, Y.rot (w l) = w (cyc18 l))
    (h112 : Y.inv (w 1) = w 12) (h36 : Y.inv (w 3) = w 6) (h217 : Y.inv (w 2) = w 17)
    (h716 : Y.inv (w 7) = w 16) (hB : ∀ l, w l ∉ Y.bdry) :
    ∃ h : ((Y.swivelMove (w 2)).swivelMove (w 3)).IsTripleDiagram,
      TripleDiagram.MoveEquivalent { Dart := H, data := Y, isTripleDiagram := hY }
        { Dart := H, data := (Y.swivelMove (w 2)).swivelMove (w 3), isTripleDiagram := h } ∧
      (∀ l, ((Y.swivelMove (w 2)).swivelMove (w 3)).rot (w l) = w (staggeredRound l)) ∧
      ∀ z, z ∉ Set.range w → ((Y.swivelMove (w 2)).swivelMove (w 3)).rot z = Y.rot z := by
  have hinv := hY.toIsPreTripleDiagram.inv_involutive
  have h121 : Y.inv (w 12) = w 1 := by rw [← h112, hinv]
  have h167 : Y.inv (w 16) = w 7 := by rw [← h716, hinv]
  obtain ⟨h₁, hmv₁, hs₁, ho₁⟩ := exists_swivelMove_label hY hw hs h217 (by decide) h121
    (by decide) (hB 2) (hB 12) {0, 1, 2, 3, 4, 5} (by decide) (by decide) (by decide)
  obtain ⟨h₂, hmv₂, hs₂, ho₂⟩ := exists_swivelMove_label h₁ hw hs₁ h36 (by decide) h716
    (by decide) (hB 3) (hB 7) {3, 4, 12, 15, 16, 17} (by decide) (by decide) (by decide)
  refine ⟨h₂, hmv₁.trans hmv₂, fun l => ?_, fun z hz => ?_⟩
  · rw [hs₂, labelSwivel_staggeredRound]
  · rw [ho₂ z hz, ho₁ z hz]

/-- **The last move of the push-off.** Let `u, p` be two triple points of a triple diagram `Y`,
with darts `w 0, …, w 5` and `w 6, …, w 11` in rotation order, such that `ū₃ = p₀` and `ū₂ = p₁`.
The swivel move at `u₃` gives a move-equivalent triple diagram with the cycles `pushOffRound` on
these darts, and `σ` elsewhere. -/
theorem exists_pushOffRound {Y : TripleData H b} (hY : Y.IsTripleDiagram) {w : Fin 12 → H}
    (hw : Function.Injective w) (hs : ∀ l, Y.rot (w l) = w (cyc12 l))
    (h36 : Y.inv (w 3) = w 6) (h27 : Y.inv (w 2) = w 7) (hB : ∀ l, w l ∉ Y.bdry) :
    ∃ h : (Y.swivelMove (w 3)).IsTripleDiagram,
      TripleDiagram.MoveEquivalent { Dart := H, data := Y, isTripleDiagram := hY }
        { Dart := H, data := Y.swivelMove (w 3), isTripleDiagram := h } ∧
      (∀ l, (Y.swivelMove (w 3)).rot (w l) = w (pushOffRound l)) ∧
      ∀ z, z ∉ Set.range w → (Y.swivelMove (w 3)).rot z = Y.rot z := by
  have hinv := hY.toIsPreTripleDiagram.inv_involutive
  have h72 : Y.inv (w 7) = w 2 := by rw [← h27, hinv]
  obtain ⟨h₁, hmv₁, hs₁, ho₁⟩ := exists_swivelMove_label hY hw hs h36 (by decide) h72
    (by decide) (hB 3) (hB 7) {0, 1, 2, 3, 4, 5} (by decide) (by decide) (by decide)
  refine ⟨h₁, hmv₁, fun l => ?_, ho₁⟩
  rw [hs₁, labelSwivel_pushOffRound]

/-! ### Diagrams described by tuples of rail labels -/

section Agrees

variable {H : Type*}

/-- The data `X` with its rotation replaced by `ρ`. -/
def withRot (X : TripleData H b) (ρ : Equiv.Perm H) : TripleData H b := { X with rot := ρ }

/-- `Y` **agrees with the tuples `T` over `X`** (for darts named by rail labels through `dart`):
the rotation of `Y` sends each entry of each tuple of `T` to the next one, cyclically, and agrees
with the rotation of `X` on the darts named by no entry of `T`. -/
def AgreesOn (X Y : TripleData H b) (dart : RailLabel → H) (T : List (List RailLabel)) : Prop :=
  (∀ t ∈ T, ∀ (i : ℕ) (hi : i < t.length),
    Y.rot (dart t[i]) = dart (t[(i + 1) % t.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)))) ∧
  ∀ z, (∀ l ∈ T.flatten, dart l ≠ z) → Y.rot z = X.rot z

variable {X Y Y' : TripleData H b} {dart : RailLabel → H} {T : List (List RailLabel)}

/-- Two diagrams agreeing with the same tuples over `X` have the same rotation. -/
theorem AgreesOn.rot_eq (h : AgreesOn X Y dart T) (h' : AgreesOn X Y' dart T) :
    Y.rot = Y'.rot := by
  ext z
  by_cases hz : ∃ l ∈ T.flatten, dart l = z
  · obtain ⟨l, hl, rfl⟩ := hz
    obtain ⟨t, ht, hlt⟩ := List.mem_flatten.1 hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hlt
    rw [h.1 t ht i hi, h'.1 t ht i hi]
  · push Not at hz
    rw [h.2 z hz, h'.2 z hz]

/-- If a tuple of `T` is `cs` read through `lab`, and `g` permutes `cs` cyclically, then the
rotation of a diagram agreeing with `T` acts on the darts of `cs` as `g`. -/
theorem AgreesOn.rot_apply_of_cycle {L : Type*} (h : AgreesOn X Y dart T) {lab : L → RailLabel}
    {g : L → L} {cs : List L} (hc : cs.map lab ∈ T)
    (hcyc : ∀ (i : ℕ) (hi : i < cs.length),
      g cs[i] = (cs[(i + 1) % cs.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi))))
    {x : L} (hx : x ∈ cs) : Y.rot (dart (lab x)) = dart (lab (g x)) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := h.1 _ hc i (by simpa using hi)
  simp only [List.getElem_map, List.length_map] at this
  rw [this, hcyc i hi]

/-- A tuple naming new darts, on which `X` already rotates as prescribed, can be added. -/
theorem AgreesOn.append (h : AgreesOn X Y dart T) {t : List RailLabel}
    (ht : ∀ x ∈ t, ∀ l ∈ T.flatten, dart l ≠ dart x)
    (hrot : ∀ (i : ℕ) (hi : i < t.length),
      X.rot (dart t[i]) = dart (t[(i + 1) % t.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)))) :
    AgreesOn X Y dart (T ++ [t]) := by
  refine ⟨fun t' ht' i hi => ?_, fun z hz => h.2 z fun l hl => hz l ?_⟩
  · rcases List.mem_append.1 ht' with ht' | ht'
    · exact h.1 t' ht' i hi
    · rw [List.mem_singleton] at ht'
      subst ht'
      rw [h.2 _ (ht _ (List.getElem_mem hi)), hrot i hi]
  · rw [List.flatten_append]
    exact List.mem_append_left _ hl

/-- **A round of moves, on tuples.** Let `Y` agree with `T` over `X`, and let `Y₂` permute the
darts named by `lab : L → RailLabel` as `g` and agree with `Y` elsewhere. Suppose every tuple of
`T'` is either a cycle `cs` of `g` read through `lab`, or a tuple of `T` naming none of these
darts; every tuple of `T` is a tuple of `T'` or names only these darts; and `T'` names all of
them. Then `Y₂` agrees with `T'` over `X`. -/
theorem AgreesOn.round {L : Type*} {Y₂ : TripleData H b} {T' : List (List RailLabel)}
    (h : AgreesOn X Y dart T) {lab : L → RailLabel} {g : L → L} {S : Set RailLabel}
    (hinj : Set.InjOn dart S) (hlabS : ∀ l, lab l ∈ S) (hTS : ∀ t ∈ T, ∀ x ∈ t, x ∈ S)
    (hrot : ∀ l, Y₂.rot (dart (lab l)) = dart (lab (g l)))
    (hoff : ∀ z, (∀ l, dart (lab l) ≠ z) → Y₂.rot z = Y.rot z) (C : List (List L))
    (hcyc : ∀ cs ∈ C, ∀ (i : ℕ) (hi : i < cs.length),
      g cs[i] = (cs[(i + 1) % cs.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi))))
    (hT' : ∀ t ∈ T', (∃ cs ∈ C, cs.map lab = t) ∨ (t ∈ T ∧ ∀ x ∈ t, ∀ l, x ≠ lab l))
    (hT : ∀ t ∈ T, t ∈ T' ∨ ∀ x ∈ t, ∃ l, x = lab l) (hcov : ∀ l, lab l ∈ T'.flatten) :
    AgreesOn X Y₂ dart T' := by
  refine ⟨fun t ht i hi => ?_, fun z hz => ?_⟩
  · rcases hT' t ht with ⟨cs, hc, rfl⟩ | ⟨htT, hdisj⟩
    · simp only [List.getElem_map, List.length_map]
      rw [hrot, hcyc cs hc i (by simpa using hi)]
    · have hne : ∀ l, dart (lab l) ≠ dart t[i] := fun l he =>
        hdisj _ (List.getElem_mem hi) l
          (hinj (hTS t htT _ (List.getElem_mem hi)) (hlabS l) he.symm)
      rw [hoff _ hne, h.1 t htT i hi]
  · have hne : ∀ l, dart (lab l) ≠ z := fun l => hz _ (hcov l)
    rw [hoff z hne]
    refine h.2 z fun l hl => ?_
    obtain ⟨t, ht, hlt⟩ := List.mem_flatten.1 hl
    rcases hT t ht with ht' | hsub
    · exact hz l (List.mem_flatten.2 ⟨t, ht', hlt⟩)
    · obtain ⟨l', rfl⟩ := hsub l hlt
      exact hne l'

end Agrees

/-! ### Rails: the darts at their points -/

section RailFacts

variable {H : Type*} [Fintype H] [DecidableEq H] {X : TripleData H b} {p q : ℕ}

/-- The six labels `(a, 0), …, (a, 5)` of the darts at the point `a` of a rail, in rotation
order. -/
def pointCycle (a : ℕ ⊕ ℕ) : List RailLabel := (List.range 6).map fun m => (a, m)

/-- At a point of a rail of a pre-triple diagram, `σ(c_{a,m}) = c_{a,m+1}`, indices modulo `6`. -/
theorem RailPoints.rot_dart (hX : X.IsPreTripleDiagram) (P : X.RailPoints p q) {a : ℕ ⊕ ℕ}
    (ha : a ∈ pointSet p q) (m : ℕ) : X.rot (P.dart (a, m)) = P.dart (a, (m + 1) % 6) := by
  have hint := X.mem_internalVertices.1 (P.vertexOf_mem a ha)
  change X.rot ((X.rot ^ m) _) = (X.rot ^ ((m + 1) % 6)) _
  rw [← Equiv.Perm.mul_apply, ← pow_succ', hX.rot_pow_mod_six hint.2]

/-- A dart at a point of a rail is not in `B`. -/
theorem RailPoints.dart_notMem_bdry (P : X.RailPoints p q) {l : RailLabel}
    (hl : l ∈ labelSet p q) : P.dart l ∉ X.bdry := fun h =>
  (X.mem_internalVertices.1 (P.vertexOf_mem l.1 (mem_product.1 hl).1)).2
    ⟨_, P.dart_mem_vertexOf l, h⟩

/-- A diagram agrees with the cycle of a point of a rail over itself. -/
theorem RailPoints.agreesOn_pointCycle (hX : X.IsPreTripleDiagram) (P : X.RailPoints p q)
    {Y : TripleData H b} {T : List (List RailLabel)} (h : AgreesOn X Y P.dart T)
    {a : ℕ ⊕ ℕ} (ha : a ∈ pointSet p q) (hT : ∀ x ∈ T.flatten, x ∈ labelSet p q)
    (hnot : ∀ x ∈ T.flatten, x.1 ≠ a) : AgreesOn X Y P.dart (T ++ [pointCycle a]) := by
  refine h.append (fun x hx l hl he => ?_) fun i hi => ?_
  · simp only [pointCycle, List.mem_map, List.mem_range] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    have := injOn_dart hX (hT l hl) (mem_product.2 ⟨ha, mem_range.2 hm⟩) he
    exact hnot l hl (by rw [this])
  · simp only [pointCycle, List.length_map, List.length_range] at hi ⊢
    simp only [List.getElem_map, List.getElem_range]
    exact P.rot_dart hX ha i

end RailFacts

/-- `labelSet p q` is monotone in `p` and in `q`. -/
theorem labelSet_mono {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') :
    labelSet p q ⊆ labelSet p' q' := by
  intro x hx
  rw [mem_labelSet] at hx ⊢
  rcases hx with ⟨j, hj, m, hm, rfl⟩ | ⟨j, h1, h2, m, hm, rfl⟩
  · exact Or.inl ⟨j, by omega, m, hm, rfl⟩
  · exact Or.inr ⟨j, h1, by omega, m, hm, rfl⟩

/-- A diagram agreeing with tuples of labels at the first `k` points agrees with them and the
cycles of the points `x_{k+1}` and `y_{k+1}` of a rail. -/
theorem RailPoints.agreesOn_pointCycle_inl_inr {H : Type*} [Fintype H] [DecidableEq H]
    {X Y : TripleData H b} {r k : ℕ} (hX : X.IsPreTripleDiagram) (P : X.RailPoints r r)
    {T : List (List RailLabel)} (h : AgreesOn X Y P.dart T) (hk : k < r)
    (hT : ∀ x ∈ T.flatten, x ∈ labelSet k k) :
    AgreesOn X Y P.dart (T ++ [pointCycle (.inl (k + 1))] ++ [pointCycle (.inr (k + 1))]) := by
  have hS : ∀ x ∈ T.flatten, x ∈ labelSet r r := fun x hx => labelSet_mono hk.le hk.le (hT x hx)
  have hK : ∀ x ∈ T.flatten, x.1 ≠ .inl (k + 1) ∧ x.1 ≠ .inr (k + 1) := fun x hx => by
    have := hT x hx
    rw [mem_labelSet] at this
    rcases this with ⟨j, hj, m, hm, rfl⟩ | ⟨j, h1, h2, m, hm, rfl⟩ <;>
      simp [RailLabel.rho, RailLabel.eta] <;> omega
  refine P.agreesOn_pointCycle hX (P.agreesOn_pointCycle hX h ?_ hS fun x hx => (hK x hx).1)
    ?_ ?_ ?_
  · simp [pointSet]
    omega
  · simp [pointSet]
    omega
  · intro x hx
    simp only [List.flatten_append, List.mem_append, List.flatten_cons, List.flatten_nil,
      List.append_nil] at hx
    rcases hx with hx | hx
    · exact hS x hx
    · simp only [pointCycle, List.mem_map, List.mem_range] at hx
      obtain ⟨m, hm, rfl⟩ := hx
      exact mem_product.2 ⟨by simp [pointSet]; omega, mem_range.2 hm⟩
  · intro x hx
    simp only [List.flatten_append, List.mem_append, List.flatten_cons, List.flatten_nil,
      List.append_nil] at hx
    rcases hx with hx | hx
    · exact (hK x hx).2
    · simp only [pointCycle, List.mem_map, List.mem_range] at hx
      obtain ⟨m, hm, rfl⟩ := hx
      simp

/-- Tuples of labels at the first `k` points, together with the cycles of `x_{k+1}` and
`y_{k+1}`, have their labels in `labelSet r` for `k < r`. -/
theorem mem_labelSet_of_mem_append_pointCycle {r k : ℕ} {T : List (List RailLabel)} (hk : k < r)
    (hT : ∀ x ∈ T.flatten, x ∈ labelSet k k) :
    ∀ t ∈ T ++ [pointCycle (.inl (k + 1))] ++ [pointCycle (.inr (k + 1))], ∀ x ∈ t,
      x ∈ labelSet r r := by
  intro t ht x hx
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with (ht | rfl) | rfl
  · exact labelSet_mono hk.le hk.le (hT x (List.mem_flatten.2 ⟨t, ht, hx⟩))
  · simp only [pointCycle, List.mem_map, List.mem_range] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact rho_mem_labelSet hk hm
  · simp only [pointCycle, List.mem_map, List.mem_range] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact eta_mem_labelSet (by omega) hk hm

/-- If `Y` agrees with `T` and two further cycles, where the labels `0, …, 5`, `6, …, 11` and
`12, …, 17` read through `lab` are a tuple of `T` and the two cycles, then the rotation of `Y`
acts on these darts as `cyc18`. -/
theorem AgreesOn.rot_apply_cyc18 {H : Type*} {X Y : TripleData H b} {dart : RailLabel → H}
    {T : List (List RailLabel)} {c₁ c₂ : List RailLabel} (h : AgreesOn X Y dart (T ++ [c₁] ++ [c₂]))
    {lab : Fin 18 → RailLabel} (h₀ : ([0, 1, 2, 3, 4, 5] : List (Fin 18)).map lab ∈ T)
    (h₁ : ([6, 7, 8, 9, 10, 11] : List (Fin 18)).map lab = c₁)
    (h₂ : ([12, 13, 14, 15, 16, 17] : List (Fin 18)).map lab = c₂) (l : Fin 18) :
    Y.rot (dart (lab l)) = dart (lab (cyc18 l)) := by
  have hC : ∀ l : Fin 18, l ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 18)) ∨
      l ∈ ([6, 7, 8, 9, 10, 11] : List (Fin 18)) ∨
      l ∈ ([12, 13, 14, 15, 16, 17] : List (Fin 18)) := by decide
  rcases hC l with hl | hl | hl
  · exact h.rot_apply_of_cycle (List.mem_append_left _ (List.mem_append_left _ h₀)) (by decide) hl
  · exact h.rot_apply_of_cycle (List.mem_append_left _ (List.mem_append_right _
      (by rw [h₁]; exact List.mem_singleton_self _))) (by decide) hl
  · exact h.rot_apply_of_cycle (List.mem_append_right _
      (by rw [h₂]; exact List.mem_singleton_self _)) (by decide) hl

/-- If `Y` agrees with `T` and a further cycle, where the labels `0, …, 5` and `6, …, 11` read
through `lab` are a tuple of `T` and the cycle, then the rotation of `Y` acts on these darts as
`cyc12`. -/
theorem AgreesOn.rot_apply_cyc12 {H : Type*} {X Y : TripleData H b} {dart : RailLabel → H}
    {T : List (List RailLabel)} {c : List RailLabel} (h : AgreesOn X Y dart (T ++ [c]))
    {lab : Fin 12 → RailLabel} (h₀ : ([0, 1, 2, 3, 4, 5] : List (Fin 12)).map lab ∈ T)
    (h₁ : ([6, 7, 8, 9, 10, 11] : List (Fin 12)).map lab = c) (l : Fin 12) :
    Y.rot (dart (lab l)) = dart (lab (cyc12 l)) := by
  have hC : ∀ l : Fin 12, l ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 12)) ∨
      l ∈ ([6, 7, 8, 9, 10, 11] : List (Fin 12)) := by decide
  rcases hC l with hl | hl
  · exact h.rot_apply_of_cycle (List.mem_append_left _ h₀) (by decide) hl
  · exact h.rot_apply_of_cycle (List.mem_append_right _
      (by rw [h₁]; exact List.mem_singleton_self _)) (by decide) hl

/-! ### The aligned combing -/

/-- The labels of the `18` darts of round `k` of the aligned combing: the tuple
`(η_{k,5}, η_{k,2}, η_{k,3}, ρ_{k,3}, ρ_{k,4}, η_{k,4})`, then the darts at `x_{k+1}` and at
`y_{k+1}`. -/
def alignedRoundLabels (k : ℕ) : Fin 18 → RailLabel :=
  ![alignedEta k 5, alignedEta k 2, alignedEta k 3, rho k 3, rho k 4, alignedEta k 4,
    rho (k + 1) 0, rho (k + 1) 1, rho (k + 1) 2, rho (k + 1) 3, rho (k + 1) 4, rho (k + 1) 5,
    eta (k + 1) 0, eta (k + 1) 1, eta (k + 1) 2, eta (k + 1) 3, eta (k + 1) 4, eta (k + 1) 5]

/-- The `18` labels of round `k` of the aligned combing are distinct. -/
theorem alignedRoundLabels_injective (k : ℕ) : Function.Injective (alignedRoundLabels k) := by
  rw [← List.nodup_ofFn]
  rcases k with _ | k
  · decide +kernel
  · simp [alignedRoundLabels, List.ofFn_succ, alignedEta, rho, eta]

/-- For `k < r`, the labels of round `k` of the aligned combing lie in `labelSet r r`. -/
theorem alignedRoundLabels_mem {k r : ℕ} (hk : k < r) (l : Fin 18) :
    alignedRoundLabels k l ∈ labelSet r r := by
  fin_cases l <;> simp only [alignedRoundLabels] <;>
    first
    | exact alignedEta_mem_labelSet (by omega) (by norm_num)
    | exact rho_mem_labelSet (by omega) (by norm_num)
    | exact eta_mem_labelSet (by omega) (by omega) (by norm_num)

/-- The tuples of `alignedCombLabels r`, listed explicitly. -/
theorem mem_alignedCombLabels_iff {r : ℕ} {t : List RailLabel} :
    t ∈ alignedCombLabels r ↔
      (∃ j < r, t = [alignedEta j 5, alignedEta j 2, alignedEta (j + 1) 1, rho (j + 1) 1,
        alignedEta j 3, rho j 3]) ∨
      t = [alignedEta r 5, alignedEta r 2, alignedEta r 3, rho r 3, rho r 4, alignedEta r 4] ∨
      ∃ j, 1 ≤ j ∧ j ≤ r ∧
        t = [rho j 2, rho j 5, rho (j - 1) 4, alignedEta (j - 1) 4, rho j 0, alignedEta j 0] := by
  simp only [alignedCombLabels, List.mem_append, List.mem_map, List.mem_range, List.mem_range'_1,
    List.mem_singleton]
  constructor
  · rintro ((⟨j, hj, rfl⟩ | rfl) | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨j, by omega, by omega, rfl⟩)
  · rintro (⟨j, hj, rfl⟩ | rfl | ⟨j, hj1, hj2, rfl⟩)
    · exact Or.inl (Or.inl ⟨j, hj, rfl⟩)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨j, ⟨by omega, by omega⟩, rfl⟩

/-- The labels of the aligned combing of length `k` are pairwise distinct. -/
theorem nodup_flatten_alignedCombLabels (k : ℕ) : (alignedCombLabels k).flatten.Nodup := by
  have htf : (alignedCombLabels k).flatten.toFinset = labelSet k k := by
    ext x
    rw [List.mem_toFinset]
    exact ⟨mem_labelSet_of_mem_alignedCombLabels, mem_alignedCombLabels_of_mem_labelSet⟩
  have h : (alignedCombLabels k).flatten.length ≤ (alignedCombLabels k).flatten.toFinset.card := by
    rw [htf, card_labelSet, length_flatten_alignedCombLabels]
  rw [List.card_toFinset] at h
  rw [← (List.dedup_sublist _).eq_of_length_le h]
  exact List.nodup_dedup _

/-- The tuples of the aligned combing of length `k` other than the last name none of the darts of
round `k`: they are disjoint from the last tuple, and the other darts of round `k` lie at
`x_{k+1}` and `y_{k+1}`. -/
theorem alignedRoundLabels_ne_of_mem {k : ℕ} {t : List RailLabel} (ht : t ∈ alignedCombLabels k)
    (hne : t ≠ [alignedEta k 5, alignedEta k 2, alignedEta k 3, rho k 3, rho k 4, alignedEta k 4]) :
    ∀ x ∈ t, ∀ l, x ≠ alignedRoundLabels k l := by
  intro x hx l hxl
  have hlast : [alignedEta k 5, alignedEta k 2, alignedEta k 3, rho k 3, rho k 4,
      alignedEta k 4] ∈ alignedCombLabels k := mem_alignedCombLabels_iff.2 (Or.inr (Or.inl rfl))
  have hx' : x ∈ labelSet k k :=
    mem_labelSet_of_mem_alignedCombLabels (List.mem_flatten.2 ⟨t, ht, hx⟩)
  haveI : Std.Symm (List.Disjoint (α := RailLabel)) := ⟨fun _ _ h => h.symm⟩
  have hdisj := (List.nodup_flatten.1 (nodup_flatten_alignedCombLabels k)).2.forall ht hlast hne
  rcases Nat.lt_or_ge l.val 6 with hl | hl
  · refine List.disjoint_left.1 hdisj hx ?_
    rw [hxl]
    obtain ⟨l, hl'⟩ := l
    interval_cases l <;> simp [alignedRoundLabels]
  · subst hxl
    obtain ⟨l, hl'⟩ := l
    rw [mem_labelSet] at hx'
    interval_cases l <;> simp [alignedRoundLabels, rho, eta] at hx'

/-- The cycles of `alignedRound`, as lists of labels in `Fin 18`. -/
def alignedRoundCycles : List (List (Fin 18)) :=
  [[0, 1, 13, 7, 2, 3], [17, 14, 15, 9, 10, 16], [8, 11, 4, 5, 6, 12]]

/-- The tuples of the aligned combing of length `k + 1`: the three new ones, and old ones. -/
theorem alignedCombLabels_succ_cases {k : ℕ} {t : List RailLabel}
    (ht : t ∈ alignedCombLabels (k + 1)) :
    (∃ cs ∈ alignedRoundCycles, cs.map (alignedRoundLabels k) = t) ∨
      (t ∈ alignedCombLabels k ∧ ∀ x ∈ t, ∀ l, x ≠ alignedRoundLabels k l) := by
  rw [mem_alignedCombLabels_iff] at ht
  rcases ht with ⟨j, hj, rfl⟩ | rfl | ⟨j, hj1, hj2, rfl⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have hm : [alignedEta j 5, alignedEta j 2, alignedEta (j + 1) 1, rho (j + 1) 1,
          alignedEta j 3, rho j 3] ∈ alignedCombLabels k :=
        mem_alignedCombLabels_iff.2 (Or.inl ⟨j, hj, rfl⟩)
      refine Or.inr ⟨hm, alignedRoundLabels_ne_of_mem hm fun h => ?_⟩
      simp only [List.cons.injEq, rho, Prod.mk.injEq] at h
      omega
    · refine Or.inl ⟨_, List.mem_cons_self .., ?_⟩
      simp [alignedRoundLabels, alignedEta]
  · refine Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    simp [alignedRoundLabels, alignedEta]
  · rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · have hm : [rho j 2, rho j 5, rho (j - 1) 4, alignedEta (j - 1) 4, rho j 0,
          alignedEta j 0] ∈ alignedCombLabels k :=
        mem_alignedCombLabels_iff.2 (Or.inr (Or.inr ⟨j, hj1, by omega, rfl⟩))
      refine Or.inr ⟨hm, alignedRoundLabels_ne_of_mem hm fun h => ?_⟩
      simp only [List.cons.injEq, rho, Prod.mk.injEq] at h
      omega
    · obtain rfl : j = k + 1 := by omega
      refine Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        ?_⟩
      simp [alignedRoundLabels, alignedEta]

/-- Each tuple of the aligned combing of length `k`, or a cycle of `x_{k+1}` or `y_{k+1}`, is a
tuple of the aligned combing of length `k + 1` or consists of labels of round `k`. -/
theorem alignedCombLabels_append_pointCycle_cases {k : ℕ} {t : List RailLabel}
    (ht : t ∈ alignedCombLabels k ++ [pointCycle (.inl (k + 1))] ++ [pointCycle (.inr (k + 1))]) :
    t ∈ alignedCombLabels (k + 1) ∨ ∀ x ∈ t, ∃ l, x = alignedRoundLabels k l := by
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with (ht | rfl) | rfl
  · rcases mem_alignedCombLabels_iff.1 ht with ⟨j, hj, rfl⟩ | rfl | ⟨j, hj1, hj2, rfl⟩
    · exact Or.inl (mem_alignedCombLabels_iff.2 (Or.inl ⟨j, by omega, rfl⟩))
    · refine Or.inr fun x hx => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]
    · exact Or.inl (mem_alignedCombLabels_iff.2 (Or.inr (Or.inr ⟨j, hj1, by omega, rfl⟩)))
  · refine Or.inr fun x hx => ?_
    simp only [pointCycle, List.mem_map, List.mem_range] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨⟨6 + m, by omega⟩, by interval_cases m <;> rfl⟩
  · refine Or.inr fun x hx => ?_
    simp only [pointCycle, List.mem_map, List.mem_range] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨⟨12 + m, by omega⟩, by interval_cases m <;> rfl⟩

section Aligned

variable {H : Type} [Fintype H] [DecidableEq H] {X : TripleData H b} {r : ℕ}

/-- **The aligned combing, round by round.** For `k ≤ r`, some triple diagram move-equivalent to
`X` agrees over `X` with the tuples of the aligned combing of length `k`. -/
theorem AlignedRail.exists_agreesOn (hX : X.IsTripleDiagram) (R : X.AlignedRail r) :
    ∀ k ≤ r, ∃ ρ : Equiv.Perm H, ∃ h : (X.withRot ρ).IsTripleDiagram,
      TripleDiagram.MoveEquivalent { Dart := H, data := X, isTripleDiagram := hX }
        { Dart := H, data := X.withRot ρ, isTripleDiagram := h } ∧
      AgreesOn X (X.withRot ρ) R.dart (alignedCombLabels k) := by
  have hP := hX.toIsPreTripleDiagram
  have hinj := RailPoints.injOn_dart (P := R.toRailPoints) hP
  intro k hk
  induction k with
  | zero =>
    refine ⟨X.rot, hX, TripleDiagram.MoveEquivalent.refl _, ?_⟩
    have h0 : alignedCombLabels 0 = [] ++ [pointCycle (.inl 0)] := by decide +kernel
    rw [h0]
    exact R.toRailPoints.agreesOn_pointCycle hP ⟨fun t ht => by simp at ht, fun _ _ => rfl⟩
      (by simp [pointSet]) (by simp) (by simp)
  | succ k ih =>
    obtain ⟨ρ, hρ, hmv, hag⟩ := ih (by omega)
    have hk' : k < r := by omega
    have hmemL := alignedRoundLabels_mem hk'
    set w : Fin 18 → H := fun l => R.dart (alignedRoundLabels k l)
    have hw : Function.Injective w := fun i j e =>
      alignedRoundLabels_injective k (hinj (hmemL i) (hmemL j) e)
    have hag2 := R.toRailPoints.agreesOn_pointCycle_inl_inr hP hag hk' fun _ hx =>
      mem_labelSet_of_mem_alignedCombLabels hx
    have hlast : [alignedEta k 5, alignedEta k 2, alignedEta k 3, rho k 3, rho k 4,
        alignedEta k 4] ∈ alignedCombLabels k := mem_alignedCombLabels_iff.2 (Or.inr (Or.inl rfl))
    have hs : ∀ l, (X.withRot ρ).rot (w l) = w (cyc18 l) := hag2.rot_apply_cyc18 hlast rfl rfl
    obtain ⟨h₂, hmv₂, hrot₂, hoff₂⟩ := exists_alignedRound hρ hw hs (R.inv_rho_three k hk')
      (R.inv_eta_three k hk') (R.inv_rho_one (k + 1) (by omega) (by omega))
      (R.inv_rho_two (k + 1) (by omega) (by omega))
      (fun l => R.toRailPoints.dart_notMem_bdry (hmemL l))
    refine ⟨_, h₂, hmv.trans hmv₂, ?_⟩
    refine hag2.round (S := labelSet r r) hinj hmemL
      (mem_labelSet_of_mem_append_pointCycle hk' fun _ hx =>
        mem_labelSet_of_mem_alignedCombLabels hx) hrot₂
      (fun z hz => hoff₂ z (by rintro ⟨l, rfl⟩; exact hz l rfl)) alignedRoundCycles
      (by decide) ?_ (fun _ => alignedCombLabels_append_pointCycle_cases)
      fun l => mem_alignedCombLabels_of_mem_labelSet (alignedRoundLabels_mem (Nat.lt_succ_self k) l)
    · intro t ht
      rcases alignedCombLabels_succ_cases ht with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_append_left _ (List.mem_append_left _ h1), h2⟩

/-- The aligned combing agrees over `X` with its tuples. -/
theorem AlignedRail.agreesOn_alignedComb (hX : X.IsPreTripleDiagram) (R : X.AlignedRail r) :
    AgreesOn X R.alignedComb R.dart (alignedCombLabels r) := by
  refine ⟨fun t ht i hi => ?_, fun z hz => ?_⟩
  · have hmem : t.map R.dart ∈ R.alignedCombTuples := List.mem_map_of_mem ht
    have := R.alignedComb_rot_getElem hX hmem i (by rw [List.length_map]; exact hi)
    simp only [List.getElem_map, List.length_map] at this
    exact this
  · refine R.alignedComb_rot_of_notMem fun hz' => ?_
    rw [← R.toFinset_flatten_alignedCombTuples hX, List.mem_toFinset, alignedCombTuples,
      ← List.map_flatten, List.mem_map] at hz'
    obtain ⟨l, hl, rfl⟩ := hz'
    exact hz l hl rfl

end Aligned

/-! ### The push-off -/

/-- The labels of the `12` darts of the last move of the push-off along a closed aligned rail of
length `m + 1`: the tuple `(η_{m,5}, η_{m,2}, η_{m,3}, ρ_{m,3}, ρ_{m,4}, η_{m,4})`, then the darts
at `x_{m+1}`. -/
def pushOffRoundLabels (m : ℕ) : Fin 12 → RailLabel :=
  ![alignedEta m 5, alignedEta m 2, alignedEta m 3, rho m 3, rho m 4, alignedEta m 4,
    rho (m + 1) 0, rho (m + 1) 1, rho (m + 1) 2, rho (m + 1) 3, rho (m + 1) 4, rho (m + 1) 5]

/-- The labels of the last round of the push-off are the first `12` labels of round `m` of the
aligned combing. -/
theorem pushOffRoundLabels_eq (m : ℕ) (l : Fin 12) :
    pushOffRoundLabels m l = alignedRoundLabels m (Fin.castLE (by norm_num) l) := by
  fin_cases l <;> rfl

/-- The `12` labels of the last round of the push-off are distinct. -/
theorem pushOffRoundLabels_injective (m : ℕ) : Function.Injective (pushOffRoundLabels m) :=
  fun i j h => Fin.castLE_injective _ (alignedRoundLabels_injective m
    (by rwa [pushOffRoundLabels_eq, pushOffRoundLabels_eq] at h))

/-- The labels of the last round of the push-off lie in `labelSet (m + 1) (m + 1 - 1)`. -/
theorem pushOffRoundLabels_mem (m : ℕ) (l : Fin 12) :
    pushOffRoundLabels m l ∈ labelSet (m + 1) (m + 1 - 1) := by
  fin_cases l <;> simp only [pushOffRoundLabels] <;>
    first
    | exact alignedEta_mem_labelSet (by omega) (by norm_num)
    | exact rho_mem_labelSet (by omega) (by norm_num)

/-- The tuples of `pushOffLabels (m + 1)`, listed explicitly. -/
theorem mem_pushOffLabels_succ_iff {m : ℕ} {t : List RailLabel} :
    t ∈ pushOffLabels (m + 1) ↔
      (∃ j < m, t = [alignedEta j 5, alignedEta j 2, alignedEta (j + 1) 1, rho (j + 1) 1,
        alignedEta j 3, rho j 3]) ∨
      t = [alignedEta m 5, alignedEta m 2, rho (m + 1) 2, rho (m + 1) 3, alignedEta m 3, rho m 3] ∨
      (∃ j, 1 ≤ j ∧ j ≤ m ∧
        t = [rho j 2, rho j 5, rho (j - 1) 4, alignedEta (j - 1) 4, rho j 0, alignedEta j 0]) ∨
      t = [rho (m + 1) 4, rho (m + 1) 5, rho m 4, alignedEta m 4, rho (m + 1) 0,
        rho (m + 1) 1] := by
  simp only [pushOffLabels, Nat.add_sub_cancel, List.mem_append, List.mem_map, List.mem_range,
    List.mem_range'_1, List.mem_singleton]
  constructor
  · rintro (((⟨j, hj, rfl⟩ | rfl) | ⟨j, hj, rfl⟩) | rfl)
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨j, by omega, by omega, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (⟨j, hj, rfl⟩ | rfl | ⟨j, hj1, hj2, rfl⟩ | rfl)
    · exact Or.inl (Or.inl (Or.inl ⟨j, hj, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr rfl))
    · exact Or.inl (Or.inr ⟨j, ⟨by omega, by omega⟩, rfl⟩)
    · exact Or.inr rfl

/-- The cycles of `pushOffRound`, as lists of labels in `Fin 12`. -/
def pushOffRoundCycles : List (List (Fin 12)) := [[0, 1, 8, 9, 2, 3], [10, 11, 4, 5, 6, 7]]

/-- The tuples of the push-off along a closed aligned rail of length `m + 1`: the two new ones,
and those of the aligned combing of length `m`. -/
theorem pushOffLabels_succ_cases {m : ℕ} {t : List RailLabel} (ht : t ∈ pushOffLabels (m + 1)) :
    (∃ cs ∈ pushOffRoundCycles, cs.map (pushOffRoundLabels m) = t) ∨
      (t ∈ alignedCombLabels m ∧ ∀ x ∈ t, ∀ l, x ≠ pushOffRoundLabels m l) := by
  have hold : ∀ t ∈ alignedCombLabels m, t ≠ [alignedEta m 5, alignedEta m 2, alignedEta m 3,
      rho m 3, rho m 4, alignedEta m 4] → ∀ x ∈ t, ∀ l, x ≠ pushOffRoundLabels m l :=
    fun t ht hne x hx l => by
      rw [pushOffRoundLabels_eq]
      exact alignedRoundLabels_ne_of_mem ht hne x hx _
  rcases mem_pushOffLabels_succ_iff.1 ht with ⟨j, hj, rfl⟩ | rfl | ⟨j, hj1, hj2, rfl⟩ | rfl
  · have hm := mem_alignedCombLabels_iff.2 (Or.inl ⟨j, hj, rfl⟩)
    refine Or.inr ⟨hm, hold _ hm fun h => ?_⟩
    simp only [List.cons.injEq, rho, Prod.mk.injEq] at h
    omega
  · exact Or.inl ⟨_, List.mem_cons_self .., rfl⟩
  · have hm := mem_alignedCombLabels_iff.2 (Or.inr (Or.inr ⟨j, hj1, hj2, rfl⟩))
    refine Or.inr ⟨hm, hold _ hm fun h => ?_⟩
    simp only [List.cons.injEq, rho, Prod.mk.injEq] at h
    omega
  · exact Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩

/-- Each tuple of the aligned combing of length `m`, or the cycle of `x_{m+1}`, is a tuple of the
push-off of length `m + 1` or consists of labels of its last round. -/
theorem alignedCombLabels_append_pointCycle_pushOff_cases {m : ℕ} {t : List RailLabel}
    (ht : t ∈ alignedCombLabels m ++ [pointCycle (.inl (m + 1))]) :
    t ∈ pushOffLabels (m + 1) ∨ ∀ x ∈ t, ∃ l, x = pushOffRoundLabels m l := by
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | rfl
  · rcases mem_alignedCombLabels_iff.1 ht with ⟨j, hj, rfl⟩ | rfl | ⟨j, hj1, hj2, rfl⟩
    · exact Or.inl (mem_pushOffLabels_succ_iff.2 (Or.inl ⟨j, hj, rfl⟩))
    · refine Or.inr fun x hx => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]
    · exact Or.inl (mem_pushOffLabels_succ_iff.2 (Or.inr (Or.inr (Or.inl ⟨j, hj1, hj2, rfl⟩))))
  · refine Or.inr fun x hx => ?_
    simp only [pointCycle, List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨6 + k, by omega⟩, by interval_cases k <;> rfl⟩

section PushOff

variable {H : Type} [Fintype H] [DecidableEq H] {X : TripleData H b} {n : ℕ}

/-- The push-off agrees over `X` with its tuples. -/
theorem ClosedAlignedRail.agreesOn_pushOff (hX : X.IsPreTripleDiagram)
    (R : X.ClosedAlignedRail n) : AgreesOn X R.pushOff R.railPoints.dart (pushOffLabels n) := by
  refine ⟨fun t ht i hi => ?_, fun z hz => ?_⟩
  · have hmem : t.map R.railPoints.dart ∈ R.pushOffTuples := List.mem_map_of_mem ht
    have := R.pushOff_rot_getElem hX hmem i (by rw [List.length_map]; exact hi)
    simp only [List.getElem_map, List.length_map] at this
    exact this
  · refine R.pushOff_rot_of_notMem fun hz' => ?_
    rw [← R.toFinset_flatten_pushOffTuples hX, List.mem_toFinset, ClosedAlignedRail.pushOffTuples,
      ← List.map_flatten, List.mem_map] at hz'
    obtain ⟨l, hl, rfl⟩ := hz'
    exact hz l hl rfl

/-- **The push-off by swivel moves.** Some triple diagram move-equivalent to `X` agrees over `X`
with the tuples of the push-off: the aligned combing of the aligned rail of length `n - 1`, then
the swivel move at `ρ_{n-1,3}`. -/
theorem ClosedAlignedRail.exists_agreesOn (hX : X.IsTripleDiagram) (R : X.ClosedAlignedRail n) :
    ∃ ρ : Equiv.Perm H, ∃ h : (X.withRot ρ).IsTripleDiagram,
      TripleDiagram.MoveEquivalent { Dart := H, data := X, isTripleDiagram := hX }
        { Dart := H, data := X.withRot ρ, isTripleDiagram := h } ∧
      AgreesOn X (X.withRot ρ) R.railPoints.dart (pushOffLabels n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := R.one_le; omega⟩
  have hP := hX.toIsPreTripleDiagram
  have hinj := RailPoints.injOn_dart (P := R.railPoints) hP
  obtain ⟨ρ, hρ, hmv, hag⟩ := R.toAlignedRail.exists_agreesOn hX m (by omega)
  replace hag : AgreesOn X (X.withRot ρ) R.railPoints.dart (alignedCombLabels m) := hag
  have hmemL := pushOffRoundLabels_mem m
  set w : Fin 12 → H := fun l => R.railPoints.dart (pushOffRoundLabels m l)
  have hw : Function.Injective w := fun i j e =>
    pushOffRoundLabels_injective m (hinj (hmemL i) (hmemL j) e)
  have hcombS : ∀ x ∈ (alignedCombLabels m).flatten, x ∈ labelSet (m + 1) (m + 1 - 1) :=
    fun x hx => labelSet_mono (by omega) (by omega) (mem_labelSet_of_mem_alignedCombLabels hx)
  have hcombK : ∀ x ∈ (alignedCombLabels m).flatten, x.1 ≠ .inl (m + 1) := fun x hx => by
    have := mem_labelSet_of_mem_alignedCombLabels hx
    rw [mem_labelSet] at this
    rcases this with ⟨j, hj, k, hk, rfl⟩ | ⟨j, h1, h2, k, hk, rfl⟩ <;> simp [rho, eta]
    omega
  have hag2 : AgreesOn X (X.withRot ρ) R.railPoints.dart
      (alignedCombLabels m ++ [pointCycle (.inl (m + 1))]) :=
    R.railPoints.agreesOn_pointCycle hP hag (by simp [pointSet]) hcombS hcombK
  have hlast : [alignedEta m 5, alignedEta m 2, alignedEta m 3, rho m 3, rho m 4,
      alignedEta m 4] ∈ alignedCombLabels m := mem_alignedCombLabels_iff.2 (Or.inr (Or.inl rfl))
  have hs : ∀ l, (X.withRot ρ).rot (w l) = w (cyc12 l) := hag2.rot_apply_cyc12 hlast rfl
  obtain ⟨h₂, hmv₂, hrot₂, hoff₂⟩ := exists_pushOffRound hρ hw hs R.inv_rho_three_last
    R.inv_eta_three_last (fun l => R.railPoints.dart_notMem_bdry (hmemL l))
  refine ⟨_, h₂, hmv.trans hmv₂, ?_⟩
  refine hag2.round (S := labelSet (m + 1) (m + 1 - 1)) hinj hmemL ?_ hrot₂
    (fun z hz => hoff₂ z (by rintro ⟨l, rfl⟩; exact hz l rfl)) pushOffRoundCycles
    (by decide) ?_ (fun _ => alignedCombLabels_append_pointCycle_pushOff_cases)
    fun l => mem_pushOffLabels_of_mem_labelSet (by omega) (hmemL l)
  · intro t ht x hx
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hcombS x (List.mem_flatten.2 ⟨t, ht, hx⟩)
    · simp only [pointCycle, List.mem_map, List.mem_range] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      exact rho_mem_labelSet le_rfl hk
  · intro t ht
    rcases pushOffLabels_succ_cases ht with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨List.mem_append_left _ h1, h2⟩

end PushOff

/-! ### The staggered combing -/

/-- The tuples of the state after `k` rounds of the staggered combing: the rotation at `x₀` for
`k = 0`, and the staggered combing of length `k` for `k ≥ 1`. -/
def staggeredState : ℕ → List (List RailLabel)
  | 0 => [pointCycle (.inl 0)]
  | k + 1 => staggeredCombLabels (k + 1)

/-- The labels of the `18` darts of round `k` of the staggered combing: the tuple `u` of the state
`k` (the rotation at `x₀` for `k = 0`, and
`(η_{k,0}, η_{k,3}, ρ_{k,2}, ρ_{k,3}, η_{k,4}, ρ_{k-1,3})` for `k ≥ 1`), then the darts at
`x_{k+1}` and at `y_{k+1}`. -/
def staggeredRoundLabels : ℕ → Fin 18 → RailLabel
  | 0 => ![rho 0 0, rho 0 1, rho 0 2, rho 0 3, rho 0 4, rho 0 5,
      rho 1 0, rho 1 1, rho 1 2, rho 1 3, rho 1 4, rho 1 5,
      eta 1 0, eta 1 1, eta 1 2, eta 1 3, eta 1 4, eta 1 5]
  | k + 1 => ![eta (k + 1) 0, eta (k + 1) 3, rho (k + 1) 2, rho (k + 1) 3, eta (k + 1) 4, rho k 3,
      rho (k + 2) 0, rho (k + 2) 1, rho (k + 2) 2, rho (k + 2) 3, rho (k + 2) 4, rho (k + 2) 5,
      eta (k + 2) 0, eta (k + 2) 1, eta (k + 2) 2, eta (k + 2) 3, eta (k + 2) 4, eta (k + 2) 5]

/-- The `18` labels of round `k` of the staggered combing are distinct. -/
theorem staggeredRoundLabels_injective (k : ℕ) : Function.Injective (staggeredRoundLabels k) := by
  rw [← List.nodup_ofFn]
  rcases k with _ | k
  · decide +kernel
  · simp [staggeredRoundLabels, List.ofFn_succ, rho, eta]

/-- For `k < r`, the labels of round `k` of the staggered combing lie in `labelSet r r`. -/
theorem staggeredRoundLabels_mem {k r : ℕ} (hk : k < r) (l : Fin 18) :
    staggeredRoundLabels k l ∈ labelSet r r := by
  rcases k with _ | k <;> fin_cases l <;> simp only [staggeredRoundLabels] <;>
    first
    | exact rho_mem_labelSet (by omega) (by norm_num)
    | exact eta_mem_labelSet (by omega) (by omega) (by norm_num)

/-- For `r ≥ 1`, the tuples of `staggeredCombLabels r`, listed explicitly. -/
theorem mem_staggeredCombLabels_iff {r : ℕ} (hr : 1 ≤ r) {t : List RailLabel} :
    t ∈ staggeredCombLabels r ↔
      t = [rho 0 0, eta 1 1, eta 1 2, rho 0 1, rho 0 2, rho 0 5] ∨
      (∃ j, 1 ≤ j ∧ j < r ∧
        t = [eta j 0, eta (j + 1) 1, eta (j + 1) 2, eta j 3, rho j 2, rho (j - 1) 3]) ∨
      t = [eta r 0, eta r 3, rho r 2, rho r 3, eta r 4, rho (r - 1) 3] ∨
      t = [rho 1 0, rho 1 1, rho 1 4, rho 1 5, rho 0 4, eta 1 5] ∨
      ∃ j, 2 ≤ j ∧ j ≤ r ∧ t = [rho j 0, rho j 1, rho j 4, rho j 5, eta (j - 1) 4, eta j 5] := by
  simp only [staggeredCombLabels, List.mem_append, List.mem_map, List.mem_range'_1,
    List.mem_singleton]
  constructor
  · rintro ((((rfl | ⟨j, hj, rfl⟩) | rfl) | rfl) | ⟨j, hj, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨j, by omega, by omega, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, by omega, by omega, rfl⟩)))
  · rintro (rfl | ⟨j, hj1, hj2, rfl⟩ | rfl | rfl | ⟨j, hj1, hj2, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, ⟨by omega, by omega⟩, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr rfl))
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨j, ⟨by omega, by omega⟩, rfl⟩

/-- The last tuple of the state `k + 1` of the staggered combing. -/
theorem staggeredState_last (k : ℕ) :
    ([0, 1, 2, 3, 4, 5] : List (Fin 18)).map (staggeredRoundLabels k) ∈ staggeredState k := by
  rcases k with _ | k
  · exact List.mem_singleton_self _
  · exact (mem_staggeredCombLabels_iff (by omega)).2 (Or.inr (Or.inr (Or.inl rfl)))

/-- Every label in a tuple of the state `k` of the staggered combing lies in `labelSet k k`. -/
theorem mem_labelSet_of_mem_staggeredState {k : ℕ} {x : RailLabel}
    (hx : x ∈ (staggeredState k).flatten) : x ∈ labelSet k k := by
  rcases k with _ | k
  · simp only [staggeredState, List.flatten_cons, List.flatten_nil, List.append_nil, pointCycle,
      List.mem_map, List.mem_range] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact rho_mem_labelSet le_rfl hm
  · exact mem_labelSet_of_mem_staggeredCombLabels (by omega) hx

/-- The cycles of `staggeredRound`, as lists of labels in `Fin 18`. -/
def staggeredRoundCycles : List (List (Fin 18)) :=
  [[0, 13, 14, 1, 2, 5], [12, 15, 8, 9, 16, 3], [6, 7, 10, 11, 4, 17]]

/-- The tuples of the staggered combing of length `k + 1`: the three new ones, and old ones. -/
theorem staggeredCombLabels_succ_cases {k : ℕ} {t : List RailLabel}
    (ht : t ∈ staggeredCombLabels (k + 1)) :
    (∃ cs ∈ staggeredRoundCycles, cs.map (staggeredRoundLabels k) = t) ∨
      (t ∈ staggeredState k ∧ ∀ x ∈ t, ∀ l, x ≠ staggeredRoundLabels k l) := by
  have new1 : ([0, 13, 14, 1, 2, 5] : List (Fin 18)) ∈ staggeredRoundCycles :=
    List.mem_cons_self ..
  have new2 : ([12, 15, 8, 9, 16, 3] : List (Fin 18)) ∈ staggeredRoundCycles :=
    List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have new3 : ([6, 7, 10, 11, 4, 17] : List (Fin 18)) ∈ staggeredRoundCycles :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  rcases k with _ | k
  · rw [mem_staggeredCombLabels_iff le_rfl] at ht
    rcases ht with rfl | ⟨j, hj1, hj2, rfl⟩ | rfl | rfl | ⟨j, hj1, hj2, rfl⟩
    · exact Or.inl ⟨_, new1, rfl⟩
    · omega
    · exact Or.inl ⟨_, new2, rfl⟩
    · exact Or.inl ⟨_, new3, rfl⟩
    · omega
  · have hold : ∀ t ∈ staggeredState (k + 1), t ≠ [eta (k + 1) 0, eta (k + 1) 3, rho (k + 1) 2,
        rho (k + 1) 3, eta (k + 1) 4, rho k 3] →
        ∀ x ∈ t, ∀ l, x ≠ staggeredRoundLabels (k + 1) l := by
      intro t ht hne x hx l
      rw [staggeredState, mem_staggeredCombLabels_iff (by omega)] at ht
      rcases ht with rfl | ⟨j, hj1, hj2, rfl⟩ | rfl | rfl | ⟨j, hj1, hj2, rfl⟩
      rotate_left 2
      · exact absurd rfl hne
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        fin_cases l <;> rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [staggeredRoundLabels, rho, eta] <;> omega
    have hst : ∀ {t}, t ∈ staggeredCombLabels (k + 1) → t ∈ staggeredState (k + 1) := id
    rw [mem_staggeredCombLabels_iff (by omega)] at ht
    rcases ht with rfl | ⟨j, hj1, hj2, rfl⟩ | rfl | rfl | ⟨j, hj1, hj2, rfl⟩
    · have hm := hst ((mem_staggeredCombLabels_iff (by omega)).2 (Or.inl rfl))
      exact Or.inr ⟨hm, hold _ hm (by simp [rho, eta])⟩
    · rcases Nat.lt_or_ge j (k + 1) with hj | hj
      · have hm := hst ((mem_staggeredCombLabels_iff (by omega)).2
          (Or.inr (Or.inl ⟨j, hj1, hj, rfl⟩)))
        exact Or.inr ⟨hm, hold _ hm (by simp [rho, eta]; try omega)⟩
      · obtain rfl : j = k + 1 := by omega
        exact Or.inl ⟨_, new1, by simp [staggeredRoundLabels]⟩
    · exact Or.inl ⟨_, new2, by simp [staggeredRoundLabels]⟩
    · have hm := hst ((mem_staggeredCombLabels_iff (by omega)).2 (Or.inr (Or.inr (Or.inr
        (Or.inl rfl)))))
      exact Or.inr ⟨hm, hold _ hm (by simp [rho, eta])⟩
    · rcases Nat.lt_or_ge j (k + 2) with hj | hj
      · have hm := hst ((mem_staggeredCombLabels_iff (by omega)).2
          (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hj1, by omega, rfl⟩)))))
        exact Or.inr ⟨hm, hold _ hm (by simp [rho, eta]; try omega)⟩
      · obtain rfl : j = k + 2 := by omega
        exact Or.inl ⟨_, new3, by simp [staggeredRoundLabels]⟩

/-- The tuples of the state `k` of the staggered combing: tuples of the staggered combing of length
`k + 1`, or naming only darts of round `k`. -/
theorem staggeredState_cases {k : ℕ} {t : List RailLabel} (ht : t ∈ staggeredState k) :
    t ∈ staggeredCombLabels (k + 1) ∨ ∀ x ∈ t, ∃ l, x = staggeredRoundLabels k l := by
  rcases k with _ | k
  · refine Or.inr fun x hx => ?_
    simp only [staggeredState, List.mem_singleton] at ht
    subst ht
    simp only [pointCycle, List.mem_map, List.mem_range] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨⟨m, by omega⟩, by interval_cases m <;> rfl⟩
  · rw [staggeredState, mem_staggeredCombLabels_iff (by omega)] at ht
    have hiff := fun t => @mem_staggeredCombLabels_iff (k + 2) (by omega) t
    rcases ht with rfl | ⟨j, hj1, hj2, rfl⟩ | rfl | rfl | ⟨j, hj1, hj2, rfl⟩
    · exact Or.inl ((hiff _).2 (Or.inl rfl))
    · exact Or.inl ((hiff _).2 (Or.inr (Or.inl ⟨j, hj1, by omega, rfl⟩)))
    · refine Or.inr fun x hx => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, by simp [staggeredRoundLabels]⟩]
    · exact Or.inl ((hiff _).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inl ((hiff _).2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hj1, by omega, rfl⟩)))))

/-- The label `6 + m` of round `k` of the staggered combing is the dart `m` at `x_{k+1}`. -/
theorem staggeredRoundLabels_p (k m : ℕ) (hm : m < 6) :
    staggeredRoundLabels k ⟨6 + m, by omega⟩ = (.inl (k + 1), m) := by
  rcases k with _ | k <;> interval_cases m <;> rfl

/-- The label `12 + m` of round `k` of the staggered combing is the dart `m` at `y_{k+1}`. -/
theorem staggeredRoundLabels_q (k m : ℕ) (hm : m < 6) :
    staggeredRoundLabels k ⟨12 + m, by omega⟩ = (.inr (k + 1), m) := by
  rcases k with _ | k <;> interval_cases m <;> rfl

/-- The labels `6, …, 11` of round `k` of the staggered combing are the rotation at `x_{k+1}`. -/
theorem staggeredRound_pointCycle_inl (k : ℕ) :
    ([6, 7, 8, 9, 10, 11] : List (Fin 18)).map (staggeredRoundLabels k) =
      pointCycle (.inl (k + 1)) := by
  rcases k with _ | k <;> rfl

/-- The labels `12, …, 17` of round `k` of the staggered combing are the rotation at `y_{k+1}`. -/
theorem staggeredRound_pointCycle_inr (k : ℕ) :
    ([12, 13, 14, 15, 16, 17] : List (Fin 18)).map (staggeredRoundLabels k) =
      pointCycle (.inr (k + 1)) := by
  rcases k with _ | k <;> rfl

section Staggered

variable {H : Type} [Fintype H] [DecidableEq H] {X : TripleData H b} {r : ℕ}

/-- The relations of a staggered rail at the darts of round `k`. -/
theorem StaggeredRail.inv_round (R : X.StaggeredRail r) {k : ℕ} (hk : k < r) :
    X.inv (R.dart (staggeredRoundLabels k 1)) = R.dart (staggeredRoundLabels k 12) ∧
      X.inv (R.dart (staggeredRoundLabels k 3)) = R.dart (staggeredRoundLabels k 6) ∧
      X.inv (R.dart (staggeredRoundLabels k 2)) = R.dart (staggeredRoundLabels k 17) ∧
      X.inv (R.dart (staggeredRoundLabels k 7)) = R.dart (staggeredRoundLabels k 16) := by
  rcases k with _ | k
  · exact ⟨R.inv_rho_zero_one, R.inv_rho_three 0 hk, R.inv_rho_two 1 le_rfl (by omega),
      R.inv_rho_one 1 le_rfl (by omega)⟩
  · exact ⟨R.inv_eta_three (k + 1) (by omega) hk, R.inv_rho_three (k + 1) hk,
      R.inv_rho_two (k + 2) (by omega) (by omega), R.inv_rho_one (k + 2) (by omega) (by omega)⟩

/-- **The staggered combing, round by round.** For `k ≤ r`, some triple diagram move-equivalent to
`X` agrees over `X` with the tuples of the state `k` of the staggered combing. -/
theorem StaggeredRail.exists_agreesOn (hX : X.IsTripleDiagram) (R : X.StaggeredRail r) :
    ∀ k ≤ r, ∃ ρ : Equiv.Perm H, ∃ h : (X.withRot ρ).IsTripleDiagram,
      TripleDiagram.MoveEquivalent { Dart := H, data := X, isTripleDiagram := hX }
        { Dart := H, data := X.withRot ρ, isTripleDiagram := h } ∧
      AgreesOn X (X.withRot ρ) R.dart (staggeredState k) := by
  have hP := hX.toIsPreTripleDiagram
  have hinj := RailPoints.injOn_dart (P := R.toRailPoints) hP
  intro k hk
  induction k with
  | zero =>
    refine ⟨X.rot, hX, TripleDiagram.MoveEquivalent.refl _, ?_⟩
    exact R.toRailPoints.agreesOn_pointCycle hP (T := [])
      ⟨fun t ht => by simp at ht, fun _ _ => rfl⟩ (by simp [pointSet]) (by simp) (by simp)
  | succ k ih =>
    obtain ⟨ρ, hρ, hmv, hag⟩ := ih (by omega)
    have hk' : k < r := by omega
    have hmemL := staggeredRoundLabels_mem hk'
    set w : Fin 18 → H := fun l => R.dart (staggeredRoundLabels k l)
    have hw : Function.Injective w := fun i j e =>
      staggeredRoundLabels_injective k (hinj (hmemL i) (hmemL j) e)
    have hag2 := R.toRailPoints.agreesOn_pointCycle_inl_inr hP hag hk' fun _ hx =>
      mem_labelSet_of_mem_staggeredState hx
    have hs : ∀ l, (X.withRot ρ).rot (w l) = w (cyc18 l) := hag2.rot_apply_cyc18
      (staggeredState_last k) (staggeredRound_pointCycle_inl k) (staggeredRound_pointCycle_inr k)
    obtain ⟨i1, i3, i2, i7⟩ := R.inv_round hk'
    obtain ⟨h₂, hmv₂, hrot₂, hoff₂⟩ := exists_staggeredRound hρ hw hs i1 i3 i2 i7
      (fun l => R.toRailPoints.dart_notMem_bdry (hmemL l))
    refine ⟨_, h₂, hmv.trans hmv₂, ?_⟩
    refine hag2.round (S := labelSet r r) hinj hmemL
      (mem_labelSet_of_mem_append_pointCycle hk' fun _ hx =>
        mem_labelSet_of_mem_staggeredState hx) hrot₂
      (fun z hz => hoff₂ z (by rintro ⟨l, rfl⟩; exact hz l rfl)) staggeredRoundCycles
      (by decide) ?_ ?_ ?_
    · intro t ht
      rcases staggeredCombLabels_succ_cases ht with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_append_left _ (List.mem_append_left _ h1), h2⟩
    · intro t ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with (ht | rfl) | rfl
      · exact staggeredState_cases ht
      · refine Or.inr fun x hx => ?_
        simp only [pointCycle, List.mem_map, List.mem_range] at hx
        obtain ⟨m, hm, rfl⟩ := hx
        exact ⟨_, (staggeredRoundLabels_p k m hm).symm⟩
      · refine Or.inr fun x hx => ?_
        simp only [pointCycle, List.mem_map, List.mem_range] at hx
        obtain ⟨m, hm, rfl⟩ := hx
        exact ⟨_, (staggeredRoundLabels_q k m hm).symm⟩
    · intro l
      exact mem_staggeredCombLabels_of_mem_labelSet (by omega)
        (staggeredRoundLabels_mem (Nat.lt_succ_self k) l)

/-- The staggered combing agrees over `X` with its tuples. -/
theorem StaggeredRail.agreesOn_staggeredComb (hX : X.IsPreTripleDiagram)
    (R : X.StaggeredRail r) : AgreesOn X R.staggeredComb R.dart (staggeredCombLabels r) := by
  refine ⟨fun t ht i hi => ?_, fun z hz => ?_⟩
  · have hmem : t.map R.dart ∈ R.staggeredCombTuples := List.mem_map_of_mem ht
    have := R.staggeredComb_rot_getElem hX hmem i (by rw [List.length_map]; exact hi)
    simp only [List.getElem_map, List.length_map] at this
    exact this
  · refine R.staggeredComb_rot_of_notMem fun hz' => ?_
    rw [← R.toFinset_flatten_staggeredCombTuples hX, List.mem_toFinset, staggeredCombTuples,
      ← List.map_flatten, List.mem_map] at hz'
    obtain ⟨l, hl, rfl⟩ := hz'
    exact hz l hl rfl

end Staggered

end TripleData

namespace TripleDiagram

open TripleData

/-- **Combing an anti-parallel strand onto the rail** (FWZ Exercise 7.6.9, move (7.6.2)). Let `𝒳`
be a triple diagram, fix an aligned rail of length `r ≥ 1` of `𝒳`, and let `𝒳'` be its aligned
combing. Then `𝒳'` is a triple diagram move-equivalent to `𝒳`. -/
@[cluster_algebras "lem_comb_step"]
theorem exists_moveEquivalent_alignedComb {b : ℕ} (X : TripleDiagram b) {r : ℕ}
    (hr : 1 ≤ r) (R : X.data.AlignedRail r) :
    ∃ h : R.alignedComb.IsTripleDiagram,
      X.MoveEquivalent { Dart := X.Dart, data := R.alignedComb, isTripleDiagram := h } := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨ρ, h, hmv, hag⟩ := R.exists_agreesOn X.isTripleDiagram (r' + 1) le_rfl
  obtain rfl : ρ = R.alignedComb.rot :=
    hag.rot_eq (R.agreesOn_alignedComb X.isTripleDiagram.toIsPreTripleDiagram)
  exact ⟨h, hmv⟩

/-- **Pushing off a closed aligned rail** (FWZ Exercise 7.6.9, move (7.6.1)). Let `𝒳` be a triple
diagram, fix a closed aligned rail of `𝒳`, and let `𝒳'` be its push-off. Then `𝒳'` is a triple
diagram move-equivalent to `𝒳`. -/
@[cluster_algebras "lem_hug_antiparallel_push"]
theorem exists_moveEquivalent_pushOff {b : ℕ} (X : TripleDiagram b) {n : ℕ}
    (R : X.data.ClosedAlignedRail n) :
    ∃ h : R.pushOff.IsTripleDiagram,
      X.MoveEquivalent { Dart := X.Dart, data := R.pushOff, isTripleDiagram := h } := by
  obtain ⟨ρ, h, hmv, hag⟩ := R.exists_agreesOn X.isTripleDiagram
  obtain rfl : ρ = R.pushOff.rot :=
    hag.rot_eq (R.agreesOn_pushOff X.isTripleDiagram.toIsPreTripleDiagram)
  exact ⟨h, hmv⟩

/-- **Combing a parallel strand onto the rail** (FWZ Exercise 7.6.9, move (7.6.3)). Let `𝒳` be a
triple diagram, fix a staggered rail of length `r ≥ 1` of `𝒳`, and let `𝒳'` be its staggered
combing. Then `𝒳'` is a triple diagram move-equivalent to `𝒳`. -/
@[cluster_algebras "lem_comb_step_parallel"]
theorem exists_moveEquivalent_staggeredComb {b : ℕ} (X : TripleDiagram b) {r : ℕ}
    (R : X.data.StaggeredRail r) :
    ∃ h : R.staggeredComb.IsTripleDiagram,
      X.MoveEquivalent { Dart := X.Dart, data := R.staggeredComb, isTripleDiagram := h } := by
  obtain ⟨ρ, h, hmv, hag⟩ := R.exists_agreesOn X.isTripleDiagram r le_rfl
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := R.one_le; omega⟩
  obtain rfl : ρ = R.staggeredComb.rot :=
    hag.rot_eq (R.agreesOn_staggeredComb X.isTripleDiagram.toIsPreTripleDiagram)
  exact ⟨h, hmv⟩

end TripleDiagram

end ClusterAlgebras

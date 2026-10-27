/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.MutationTransport
public import ClusterAlgebras.WiringDiagram.BraidMutation

/-!
# A braid move is a mutation

The correspondence of `ClusterAlgebras.WiringDiagram.BraidMutation` is here shown to be an
isomorphism from `μ_Y(Q(D))` to `Q(D')`.

Two halves. The frozen vertices match because each of the site's four neighbours has one end among
the three crossings and the move sends it to another of the three, so no sentinel is created or
destroyed. The arrows match by comparing SIGNED counts — cancelling two-cycles changes no signed
count, and by `TwoCycleFree.eq_of_signedCount_eq` a two-cycle-free system is determined by them,
so the cancellation in the mutation rule never has to be chased. Where one chamber is the site the
four arrows simply reverse, which is `arrow_braidSite_iff` and `braidSite_arrow_iff` read once in
`D` and once in `D'`; away from the site the comparison is arithmetic in the two chambers' ends and
is discharged by `signed_arrowArith_eq`.

That is the braid move `(g, g + 1, g) ↦ (g + 1, g, g + 1)` that `braidMove` constructs. A braid
move `IsBraidMove D D' p` may also run the other way, `(g + 1, g, g + 1) ↦ (g, g + 1, g)`; then `D`
is the first-direction move of `D'` (`IsBraidMove.eq_braidMove_or`), and the isomorphism
`μ_Z(Q(D')) ≅ Q(D)` already built is turned round. Mutating it at `Z` gives
`Q(D') ≅ μ_Z(μ_Z(Q(D')))` against `μ_Y(Q(D))`, and mutating twice at one vertex restores the
arrows (`Quiver.mutationArrows_mutate_self`, proved here from signed counts). The results for both
directions are `IsBraidMove.existsUnique_equiv`, `IsBraidMove.exists_iso`,
`IsBraidMove.isoOfChamberSet` and `IsBraidMove.eq_of_chamberSet`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {n : ℕ}

namespace WiringDiagram

/-! ### The mutation rule, in signed counts

Comparing arrow counts directly would mean chasing the cancellation of two-cycles; comparing signed
counts does not, since cancelling changes no signed count. And by
`TwoCycleFree.eq_of_signedCount_eq` a two-cycle-free arrow system is determined by its signed
counts, so this loses nothing. -/

/-- **The signed count of a mutation**: reversed at the mutation vertex, and elsewhere corrected by
the two-paths through it, with the cancellation of two-cycles absorbed. -/
theorem signedCount_mutationArrows {V : Type*} [Fintype V] [DecidableEq V] (Q : Quiver V)
    (k i j : V) :
    signedCount (Q.mutationArrows k) i j =
      if i = k ∨ j = k then -signedCount Q.arrows i j
      else signedCount Q.arrows i j +
        (if i ∈ Q.frozen ∧ j ∈ Q.frozen then 0
          else (Q.arrows i k : ℤ) * (Q.arrows k j : ℤ) -
            (Q.arrows j k : ℤ) * (Q.arrows k i : ℤ)) := by
  have hkk : Q.arrows k k = 0 := Q.isArrowSystem k
  have step_right : ∀ u, Q.stepOne k u k = Q.arrows u k := fun u => by
    rw [Quiver.stepOne]
    split_ifs <;> simp [hkk]
  have step_left : ∀ u, Q.stepOne k k u = Q.arrows k u := fun u => by
    rw [Quiver.stepOne]
    split_ifs <;> simp [hkk]
  rw [Quiver.mutationArrows, signedCount_cancellation, signedCount, signedCount]
  by_cases h : i = k ∨ j = k
  · -- at the mutation vertex the two counts are exchanged, and no product survives
    rw [if_pos h, reversal, reversal, if_pos h, if_pos (Or.symm h)]
    rcases h with rfl | rfl
    · rw [step_right, step_left]
      ring
    · rw [step_left, step_right]
      ring
  · -- away from it each count gains the two-paths through the vertex, unless both ends are frozen
    rw [if_neg h, reversal, reversal, if_neg h, if_neg (fun hc => h (Or.symm hc)), Quiver.stepOne,
      Quiver.stepOne]
    by_cases hfr : i ∈ Q.frozen ∧ j ∈ Q.frozen
    · rw [if_pos hfr, if_pos (And.symm hfr), if_pos hfr]
      ring
    · rw [if_neg hfr, if_neg (fun hc => hfr (And.symm hc)), if_neg hfr]
      push_cast
      ring

/-! ### Mutating twice at one vertex

Running the isomorphism for one direction of a braid move backwards needs mutation at a vertex to
be an involution. On arrows that follows from the signed counts: the mutation reverses the arrows
at its vertex, so a second mutation there adds back the two-paths through it with the opposite
sign. -/

end WiringDiagram

namespace Quiver

variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']

/-- **Mutating twice at the same vertex restores the arrows.** At the vertex the first mutation
exchanges the two arrow counts, so the two-paths the second one adds through it are those the first
added, with the opposite sign; the signed counts are restored, and by
`TwoCycleFree.eq_of_signedCount_eq` so are the arrows. -/
theorem mutationArrows_mutate_self (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen) :
    (Q.mutate hk).mutationArrows k = Q.arrows := by
  -- at `k` a mutation exchanges the two arrow counts
  have hrev : ∀ u, Q.mutationArrows k u k = Q.arrows k u ∧
      Q.mutationArrows k k u = Q.arrows u k := by
    intro u
    have h1 := WiringDiagram.signedCount_mutationArrows Q k u k
    rw [if_pos (Or.inr rfl)] at h1
    simp only [signedCount] at h1
    rcases Q.twoCycleFree u k with h | h <;>
      rcases Q.twoCycleFree_mutationArrows k u k with h' | h' <;> omega
  refine TwoCycleFree.eq_of_signedCount_eq ((Q.mutate hk).twoCycleFree_mutationArrows k)
    Q.twoCycleFree ?_
  funext i j
  rw [WiringDiagram.signedCount_mutationArrows (Q.mutate hk) k i j, arrows_mutate, frozen_mutate,
    WiringDiagram.signedCount_mutationArrows Q k i j]
  by_cases h : i = k ∨ j = k
  · rw [if_pos h, if_pos h, neg_neg]
  · rw [if_neg h, if_neg h, (hrev i).1, (hrev i).2, (hrev j).1, (hrev j).2]
    split_ifs <;> ring

/-- **An isomorphism out of a mutation runs backwards**: if `e` is an isomorphism from `μ_k(Q)` to
`Q'` sending `k` to `k'`, then its inverse is an isomorphism from `μ_{k'}(Q')` to `Q`. Mutate `e⁻¹`
at `k'` (`Iso.mutate`) and undo the double mutation at `k` (`mutationArrows_mutate_self`). -/
def Iso.symmOfMutate {Q : Quiver V} {Q' : Quiver V'} {k : V} {hk : k ∉ Q.frozen}
    (e : (Q.mutate hk).Iso Q') {k' : V'} (hk' : k' ∉ Q'.frozen) (he : e.equiv k = k') :
    (Q'.mutate hk').Iso Q where
  equiv := e.equiv.symm
  mem_frozen_iff v := (e.symm.mutate hk').mem_frozen_iff v
  arrows_eq u v := by
    have hk2 : e.symm.equiv k' = k := he ▸ e.equiv.symm_apply_apply k
    have key : (Q.mutate hk).mutationArrows (e.symm.equiv k') = Q.arrows := by
      rw [hk2, mutationArrows_mutate_self]
    rw [← (e.symm.mutate hk').arrows_eq u v]
    exact (congrFun₂ key _ _).symm

/-- The underlying bijection of `Iso.symmOfMutate` is the inverse of that of `e`. -/
@[simp]
theorem Iso.symmOfMutate_equiv {Q : Quiver V} {Q' : Quiver V'} {k : V} {hk : k ∉ Q.frozen}
    (e : (Q.mutate hk).Iso Q') {k' : V'} (hk' : k' ∉ Q'.frozen) (he : e.equiv k = k') :
    (e.symmOfMutate hk' he).equiv = e.equiv.symm := rfl

end Quiver

namespace WiringDiagram

variable (D : WiringDiagram n) {p : ℕ}

/-! ### The arrow comparison

Every chamber but the site is one of the four neighbours or has no end among the three crossings,
and in either case its ends are known. The arrow conditions and the mutation rule are both
arithmetic in those ends, so the comparison is a finite case check. -/

/-- **A chamber other than the site** either is one of the four neighbours of the site, with its
gap and ends as there, or has no end at `p + 1`, `p + 2`, `p + 3`. -/
theorem ends_cases_of_ne_braidSite (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp) :
    ((c.gap : ℕ) = (D.levelAt p : ℕ) ∧ c.left ≤ p ∧ c.right = p + 1) ∨
      ((c.gap : ℕ) = (D.levelAt (p + 1) : ℕ) ∧ c.left ≤ p ∧ c.right = p + 2) ∨
      ((c.gap : ℕ) = (D.levelAt (p + 1) : ℕ) ∧ c.left = p + 2 ∧ p + 4 ≤ c.right) ∨
      ((c.gap : ℕ) = (D.levelAt p : ℕ) ∧ c.left = p + 3 ∧ p + 4 ≤ c.right) ∨
      (c.left ≠ p + 1 ∧ c.left ≠ p + 2 ∧ c.left ≠ p + 3 ∧
        c.right ≠ p + 1 ∧ c.right ≠ p + 2 ∧ c.right ≠ p + 3) := by
  have hlr := c.left_lt_right
  have hnl : c.left ≠ p + 1 := fun hcon => hc (D.eq_braidSite_of_left hp hcon)
  have hnr : c.right ≠ p + 3 := by
    intro hcon
    refine hc ?_
    have hgap : D.levelAt (p + 2) = c.gap :=
      c.levelAt_of_right_eq_succ (t := p + 2) (by omega) (by omega)
    have hga : c.gap = D.levelAt p := by rw [← hgap, hgg]
    have hlast : c.idx ≠ D.multiplicity c.gap := fun hlast => by
      have := c.right_eq_top_iff.2 hlast
      omega
    have hcr := c.countUpTo_right hlast
    rw [hcon, hga] at hcr
    have h5 := D.countUpTo_outer_add_three hp hgh hgg
    have h6 := D.countUpTo_braidSite_succ hp
    refine Chamber.ext' (by rw [gap_braidSite, hga]) ?_
    rw [idx_braidSite]
    omega
  by_cases h1 : c.right = p + 1
  · obtain rfl := D.eq_braidPred_of_right hp h1
    exact Or.inl ⟨by rw [gap_braidPred], D.left_braidPred_le hp, h1⟩
  by_cases h2 : c.right = p + 2
  · obtain rfl := D.eq_braidAdjPred_of_right hp h2
    exact Or.inr (Or.inl ⟨by rw [gap_braidAdjPred], D.left_braidAdjPred_le' hp hgh, h2⟩)
  by_cases h3 : c.left = p + 2
  · have hCr := D.lt_right_braidAdjSucc hp (Or.inl hgh) hgg
    obtain rfl := D.eq_braidAdjSucc_of_left hp h3
    exact Or.inr (Or.inr (Or.inl ⟨by rw [gap_braidAdjSucc], h3, by omega⟩))
  by_cases h4 : c.left = p + 3
  · obtain rfl := D.eq_braidSucc_of_left hp hgg h4
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [gap_braidSucc], h4, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hnl, h3, h4, h1, h2, hnr⟩)))

/-- **A chamber's left end, in the one formula covering every case**: the move exchanges the middle
and the third of the three crossings, as left ends. -/
theorem left_braidChamber_eq_ite (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp) :
    (D.braidChamber hp hgh hgg c).left =
      if c.left = p + 2 then p + 3 else if c.left = p + 3 then p + 2 else c.left := by
  by_cases h1 : c.left = p + 2
  · obtain rfl := D.eq_braidAdjSucc_of_left hp h1
    rw [D.left_braidChamber_braidAdjSucc hp hgh hgg, if_pos h1]
  by_cases h2 : c.left = p + 3
  · obtain rfl := D.eq_braidSucc_of_left hp hgg h2
    rw [D.left_braidChamber_braidSucc hp hgh hgg, if_neg h1, if_pos h2]
  · rw [if_neg h1, if_neg h2]
    exact D.left_braidChamber_eq hp hgh hgg hc h1 h2

/-- **A chamber's right end, in the one formula covering every case**: the move exchanges the first
and the middle of the three crossings, as right ends. -/
theorem right_braidChamber_eq_ite (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp) :
    (D.braidChamber hp hgh hgg c).right =
      if c.right = p + 1 then p + 2 else if c.right = p + 2 then p + 1 else c.right := by
  have hlr := c.left_lt_right
  by_cases h1 : c.right = p + 1
  · obtain rfl := D.eq_braidPred_of_right hp h1
    rw [D.right_braidChamber_braidPred hp hgh hgg, if_pos h1]
  by_cases h2 : c.right = p + 2
  · obtain rfl := D.eq_braidAdjPred_of_right hp h2
    rw [D.right_braidChamber_braidAdjPred hp hgh hgg, if_neg h1, if_pos h2]
  · rw [if_neg h1, if_neg h2]
    rcases D.ends_cases_of_ne_braidSite hp hgh hgg hc with
      ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, hl, hr⟩ | ⟨-, hl, hr⟩ | hu
    · exact absurd hr h1
    · exact absurd hr h2
    · have hw : D.braidWitness p c = p + 3 := by rw [braidWitness, if_pos hl]
      exact D.right_braidChamber_of_ge hp hgh hgg hc (by omega) (by omega)
    · have hw : D.braidWitness p c = p + 3 := by rw [braidWitness, if_neg (by omega), hl]
      exact D.right_braidChamber_of_ge hp hgh hgg hc (by omega) (by omega)
    · rcases Nat.lt_or_ge c.left (p + 1) with hl | hl
      · rcases Nat.lt_or_ge c.right (p + 1) with hr | hr
        · exact D.right_braidChamber_of_le hp hgh hgg hc (by omega)
        · have hs1 : c.InSpan p := c.inSpan_of_le_of_lt (by omega) (by omega) (by omega)
          have hs2 : c.InSpan (p + 1) := c.inSpan_of_le_of_lt (by omega) (by omega) (by omega)
          have hs3 : c.InSpan (p + 2) := c.inSpan_of_le_of_lt (by omega) (by omega) (by omega)
          exact (D.ends_braidChamber_of_gap_ne hp hgh hgg hc
            (c.levelAt_ne_gap (by omega) hs1 hs2) (c.levelAt_ne_gap (by omega) hs2 hs3)).2
      · have hw : D.braidWitness p c = c.left := by
          rw [braidWitness, if_neg (by omega)]
        exact D.right_braidChamber_of_ge hp hgh hgg hc (by omega) (by omega)

/-- **The arrows into the site, in arithmetic**: a chamber points at the site exactly when it ends
at the first of the three crossings or begins at the middle one. -/
theorem wiringArrows_braidSite_eq_ite (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (c : D.Chamber) :
    D.wiringArrows c (D.braidSite hp) = if c.right = p + 1 ∨ c.left = p + 2 then 1 else 0 := by
  have key : D.Arrow c (D.braidSite hp) ↔ (c.right = p + 1 ∨ c.left = p + 2) := by
    rw [D.arrow_braidSite_iff hp hadj hgg]
    exact or_congr ⟨fun h => h ▸ D.right_braidPred hp, D.eq_braidPred_of_right hp⟩
      ⟨fun h => h ▸ D.left_braidAdjSucc hp, D.eq_braidAdjSucc_of_left hp⟩
  rw [wiringArrows, if_congr key rfl rfl]

/-- **The arrows out of the site, in arithmetic**: the site points at a chamber exactly when that
chamber begins after the three crossings or ends at the middle one. -/
theorem braidSite_wiringArrows_eq_ite (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (c : D.Chamber) :
    D.wiringArrows (D.braidSite hp) c = if c.left = p + 3 ∨ c.right = p + 2 then 1 else 0 := by
  have key : D.Arrow (D.braidSite hp) c ↔ (c.left = p + 3 ∨ c.right = p + 2) := by
    rw [D.braidSite_arrow_iff hp hadj hgg]
    exact or_congr ⟨fun h => h ▸ D.left_braidSucc hp hgg, D.eq_braidSucc_of_left hp hgg⟩
      ⟨fun h => h ▸ D.right_braidAdjPred hp, D.eq_braidAdjPred_of_right hp⟩
  rw [wiringArrows, if_congr key rfl rfl]

/-- The replacement is the moved diagram's own site at `p`. -/
theorem braidReplacement_eq_braidSite (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.braidReplacement hp hgh hgg = (D.braidMove p hp hgh hgg).braidSite (p := p)
      (by rw [D.length_word_braidMove hp hgh hgg]; omega) := rfl

/-- **The arrows into the replacement are the reverses of the arrows out of the site.** Applying
`arrow_braidSite_iff` to the moved diagram names them as `B` and `F`, which the site points at. -/
theorem arrow_braidReplacement_iff (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (c : D.Chamber) :
    ((D.braidMove p hp hgh hgg).Arrow (D.braidChamber hp hgh hgg c)
        (D.braidReplacement hp hgh hgg) ↔
      (c = D.braidSucc hp ∨ c = D.braidAdjPred hp)) := by
  rw [D.braidReplacement_eq_braidSite hp hgh hgg,
    (D.braidMove p hp hgh hgg).arrow_braidSite_iff (p := p)
      (by rw [D.length_word_braidMove hp hgh hgg]; omega) (D.adj_braidMove hp hgh hgg)
      (D.gg_braidMove hp hgh hgg),
    ← D.braidChamber_braidAdjPred hp hgh hgg, ← D.braidChamber_braidSucc hp hgh hgg,
    (D.braidChamber_injective hp hgh hgg).eq_iff, (D.braidChamber_injective hp hgh hgg).eq_iff,
    or_comm]

/-- **The arrows out of the replacement are the reverses of the arrows into the site**, named as
`A` and `C`, the two that point at the site. -/
theorem braidReplacement_arrow_iff (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (c : D.Chamber) :
    ((D.braidMove p hp hgh hgg).Arrow (D.braidReplacement hp hgh hgg)
        (D.braidChamber hp hgh hgg c) ↔
      (c = D.braidPred hp ∨ c = D.braidAdjSucc hp)) := by
  rw [D.braidReplacement_eq_braidSite hp hgh hgg,
    (D.braidMove p hp hgh hgg).braidSite_arrow_iff (p := p)
      (by rw [D.length_word_braidMove hp hgh hgg]; omega) (D.adj_braidMove hp hgh hgg)
      (D.gg_braidMove hp hgh hgg),
    ← D.braidChamber_braidAdjSucc hp hgh hgg, ← D.braidChamber_braidPred hp hgh hgg,
    (D.braidChamber_injective hp hgh hgg).eq_iff, (D.braidChamber_injective hp hgh hgg).eq_iff,
    or_comm]

/-- **The comparison away from the site.** Both chambers keep their gaps and their boundedness;
their ends move only as `left_/right_braidChamber_eq_ite` says; and the ends they can have are the
five cases of `ends_cases_of_ne_braidSite`. That is the data `signed_arrowArith_eq` runs its case
check on. -/
theorem signedCount_braidChamber_of_ne (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {i j : D.Chamber} (hi : i ≠ D.braidSite hp)
    (hj : j ≠ D.braidSite hp) :
    signedCount (fun u v => (D.braidMove p hp hgh hgg).wiringArrows
        (D.braidChamber hp hgh hgg u) (D.braidChamber hp hgh hgg v)) i j =
      signedCount (D.wiringQuiver.mutationArrows (D.braidSite hp)) i j := by
  have hlen := D.length_word_braidMove hp hgh hgg
  rw [signedCount_mutationArrows D.wiringQuiver (D.braidSite hp) i j, if_neg (by tauto)]
  simp only [signedCount, arrows_wiringQuiver, mem_frozen_wiringQuiver]
  rw [D.wiringArrows_braidSite_eq_ite hp (Or.inl hgh) hgg i,
    D.braidSite_wiringArrows_eq_ite hp (Or.inl hgh) hgg j,
    D.wiringArrows_braidSite_eq_ite hp (Or.inl hgh) hgg j,
    D.braidSite_wiringArrows_eq_ite hp (Or.inl hgh) hgg i]
  simp only [wiringArrows_eq_ite, bounded_iff_arith,
    D.gap_braidChamber_of_ne hp hgh hgg hi, D.gap_braidChamber_of_ne hp hgh hgg hj, hlen]
  push_cast
  exact signed_arrowArith_eq hp hgh (D.left_braidChamber_eq_ite hp hgh hgg hi)
    (D.right_braidChamber_eq_ite hp hgh hgg hi) (D.left_braidChamber_eq_ite hp hgh hgg hj)
    (D.right_braidChamber_eq_ite hp hgh hgg hj) i.left_lt_right j.left_lt_right
    i.left_le_length j.left_le_length
    (fun hne => Chamber.left_eq_zero_of_left_eq (fun hc => hne (by rw [hc])))
    (fun hne => Chamber.right_eq_top_of_right_eq (fun hc => hne (by rw [hc])))
    (fun hne => Chamber.left_ne_right (fun hc => hne (by rw [hc])))
    (fun hne => Chamber.right_ne_left (fun hc => hne (by rw [hc])))
    (fun heq => Chamber.spans_of_gap_eq (Fin.val_inj.1 heq))
    (D.ends_cases_of_ne_braidSite hp hgh hgg hi) (D.ends_cases_of_ne_braidSite hp hgh hgg hj)

/-- **A braid move is a mutation, on signed arrow counts.** Three cases. Where one chamber is
the site, `arrow_braidSite_iff` and `braidSite_arrow_iff` applied to the moved diagram name the
arrows at the replacement, and they are precisely the reverses of the arrows at the site — no
arithmetic needed. Away from the site the comparison is `signedCount_braidChamber_of_ne`. -/
theorem signedCount_braidChamber (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (i j : D.Chamber) :
    signedCount (fun u v => (D.braidMove p hp hgh hgg).wiringArrows
        (D.braidChamber hp hgh hgg u) (D.braidChamber hp hgh hgg v)) i j =
      signedCount (D.wiringQuiver.mutationArrows (D.braidSite hp)) i j := by
  by_cases hi : i = D.braidSite hp
  · subst hi
    by_cases hj : j = D.braidSite hp
    · subst hj
      simp [signedCount]
    · -- the site's four arrows are exactly reversed at the replacement
      rw [signedCount_mutationArrows D.wiringQuiver (D.braidSite hp) _ _]
      simp only [signedCount, arrows_wiringQuiver, mem_frozen_wiringQuiver, true_or,
        if_true, D.braidChamber_braidSite hp hgh hgg, wiringArrows]
      rw [if_congr (D.braidReplacement_arrow_iff hp hgh hgg j) rfl rfl,
        if_congr (D.arrow_braidReplacement_iff hp hgh hgg j) rfl rfl,
        if_congr (D.braidSite_arrow_iff hp (Or.inl hgh) hgg j) rfl rfl,
        if_congr (D.arrow_braidSite_iff hp (Or.inl hgh) hgg j) rfl rfl]
      split_ifs <;> omega
  by_cases hj : j = D.braidSite hp
  · subst hj
    rw [signedCount_mutationArrows D.wiringQuiver (D.braidSite hp) _ _]
    simp only [signedCount, arrows_wiringQuiver, mem_frozen_wiringQuiver, or_true,
      if_true, D.braidChamber_braidSite hp hgh hgg, wiringArrows]
    rw [if_congr (D.arrow_braidReplacement_iff hp hgh hgg i) rfl rfl,
      if_congr (D.braidReplacement_arrow_iff hp hgh hgg i) rfl rfl,
      if_congr (D.arrow_braidSite_iff hp (Or.inl hgh) hgg i) rfl rfl,
      if_congr (D.braidSite_arrow_iff hp (Or.inl hgh) hgg i) rfl rfl]
    split_ifs <;> omega
  · exact D.signedCount_braidChamber_of_ne hp hgh hgg hi hj

/-- **The correspondence matches boundedness everywhere**, the site included: the site and the
replacement are both bounded, spanning the same three crossings. -/
theorem bounded_braidChamber_iff_bounded (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (v : D.Chamber) :
    (D.braidChamber hp hgh hgg v).Bounded ↔ v.Bounded := by
  by_cases hv : v = D.braidSite hp
  · subst hv
    rw [D.braidChamber_braidSite hp hgh hgg, D.braidReplacement_eq_braidSite hp hgh hgg]
    exact iff_of_true
      ((D.braidMove p hp hgh hgg).bounded_braidSite _ (D.adj_braidMove hp hgh hgg)
        (D.gg_braidMove hp hgh hgg))
      (D.bounded_braidSite hp (Or.inl hgh) hgg)
  · exact D.bounded_braidChamber_iff hp hgh hgg hv

/-- **The arrow counts agree.** Both arrow systems are two-cycle-free, so by
`TwoCycleFree.eq_of_signedCount_eq` their signed counts determine them, and those agree by
`signedCount_braidChamber`. -/
theorem arrows_braidChamber (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (u v : D.Chamber) :
    (D.braidMove p hp hgh hgg).wiringArrows (D.braidChamber hp hgh hgg u)
        (D.braidChamber hp hgh hgg v) =
      D.wiringQuiver.mutationArrows (D.braidSite hp) u v :=
  congrFun₂ (TwoCycleFree.eq_of_signedCount_eq
    (a := fun x y => (D.braidMove p hp hgh hgg).wiringArrows (D.braidChamber hp hgh hgg x)
      (D.braidChamber hp hgh hgg y))
    (fun _ _ => (D.braidMove p hp hgh hgg).twoCycleFree_wiringArrows _ _)
    (D.wiringQuiver.twoCycleFree_mutationArrows _)
    (funext₂ (D.signedCount_braidChamber hp hgh hgg))) u v

/-- **A braid move is a mutation.** The correspondence of `braidEquiv` — the site to the
replacement, every other chamber to the one carrying its chamber set — is an isomorphism from
`μ_Y(Q(D))` to `Q(D')`.

The two halves are `bounded_braidChamber_iff_bounded` for the frozen vertices and
`arrows_braidChamber` for the arrows. Away from the site the arrow counts change by exactly the
two-paths through it, and at the site the four arrows reverse, which is `arrow_braidSite_iff` and
`braidSite_arrow_iff` read once in `D` and once in `D'`. -/
def braidIso (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.wiringQuiver.mutate (k := D.braidSite hp)
        (by simpa using D.bounded_braidSite hp (Or.inl hgh) hgg)).Iso
      (D.braidMove p hp hgh hgg).wiringQuiver where
  equiv := D.braidEquiv hp hgh hgg
  mem_frozen_iff v := by
    rw [Quiver.frozen_mutate]
    simp only [mem_frozen_wiringQuiver, braidEquiv_apply]
    exact not_congr (D.bounded_braidChamber_iff_bounded hp hgh hgg v)
  arrows_eq u v := by
    rw [Quiver.arrows_mutate]
    simp only [arrows_wiringQuiver, braidEquiv_apply]
    exact D.arrows_braidChamber hp hgh hgg u v

/-- The underlying bijection of `braidIso` is `braidEquiv`. -/
@[simp]
theorem braidIso_equiv (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidIso hp hgh hgg).equiv = D.braidEquiv hp hgh hgg := rfl

/-- **The correspondence is the ONLY map sending the site to the replacement and keeping every
other chamber set**. Away from the site a chamber is pinned down by its gap and its chamber set,
and the gap follows from the chamber set. -/
theorem eq_braidChamber_of_chamberSet (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p)
    {e : D.Chamber → (D.braidMove p hp hgh hgg).Chamber}
    (hY : e (D.braidSite hp) = D.braidReplacement hp hgh hgg)
    (h : ∀ c, c ≠ D.braidSite hp → (e c).chamberSet = c.chamberSet) (c : D.Chamber) :
    e c = D.braidChamber hp hgh hgg c := by
  by_cases hc : c = D.braidSite hp
  · rw [hc, hY, D.braidChamber_braidSite hp hgh hgg]
  · refine Chamber.eq_of_gap_of_chamberSet ?_ ?_
    · rw [Chamber.gap_eq_of_chamberSet_eq (h c hc), D.gap_braidChamber_of_ne hp hgh hgg hc]
    · rw [h c hc, D.chamberSet_braidChamber_of_ne hp hgh hgg hc]

/-! ### Braid moves in either direction -/

/-- The constructed braid move, `(g, g + 1, g) ↦ (g + 1, g, g + 1)`, is a braid move. -/
theorem isBraidMove_braidMove (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) : IsBraidMove D (D.braidMove p hp hgh hgg) p :=
  ⟨hp, hgg, Or.inl hgh, rfl⟩

namespace IsBraidMove

variable {D D' : WiringDiagram n}

/-- **Every braid move is one of the two constructed ones**: either `D'` is `D.braidMove`, or
the move goes the other way and `D` is `D'.braidMove`. -/
theorem eq_braidMove_or (h : IsBraidMove D D' p) :
    (∃ (hp : p + 3 ≤ D.word.length) (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
        (hgg : D.levelAt (p + 2) = D.levelAt p), D' = D.braidMove p hp hgh hgg) ∨
      ∃ (hp : p + 3 ≤ D'.word.length)
        (hgh : (D'.levelAt p : ℕ) + 1 = (D'.levelAt (p + 1) : ℕ))
        (hgg : D'.levelAt (p + 2) = D'.levelAt p), D = D'.braidMove p hp hgh hgg := by
  obtain ⟨e0, e1, e2⟩ := h.levelAt_eq
  rcases h.2.2.1 with hup | hdown
  · exact Or.inl ⟨h.1, hup, h.2.1, ext' h.2.2.2⟩
  · have hgh : (D'.levelAt p : ℕ) + 1 = (D'.levelAt (p + 1) : ℕ) := by rwa [e0, e1]
    have hgg : D'.levelAt (p + 2) = D'.levelAt p := by rw [e0, e2]
    refine Or.inr ⟨h.length_le, hgh, hgg, eq_of_levelAt fun k hk => ?_⟩
    obtain ⟨f0, f1, f2⟩ := D'.levelAt_braidMove h.length_le hgh hgg
    by_cases hlt : k < p
    · rw [D'.levelAt_braidMove_of_lt h.length_le hgh hgg hlt, h.levelAt_of_lt hlt]
    by_cases hge : p + 3 ≤ k
    · rw [D'.levelAt_braidMove_of_ge h.length_le hgh hgg hge, h.levelAt_of_ge hge]
    obtain rfl | rfl | rfl : k = p ∨ k = p + 1 ∨ k = p + 2 := by omega
    · rw [f0, e1]
    · rw [f1, e0]
    · rw [f2, e1, h.2.1]

/-- **The site of a braid move is a mutable vertex of `Q(D)`**, being bounded. -/
theorem braidSite_notMem_frozen (h : IsBraidMove D D' p) :
    D.braidSite h.1 ∉ D.wiringQuiver.frozen := by
  simpa using D.bounded_braidSite h.1 h.2.2.1 h.2.1

/-- **At most one map sends the site to the replacement and keeps every other chamber set.** Away
from the site a chamber of `D'` is pinned down by its gap and its chamber set, and the gap follows
from the chamber set. -/
@[cluster_algebras "prop_braid_is_mutation"]
theorem eq_of_chamberSet (h : IsBraidMove D D' p) {e e' : D.Chamber → D'.Chamber}
    (hY : e (D.braidSite h.1) = D'.braidSite h.length_le)
    (hJ : ∀ c, c ≠ D.braidSite h.1 → (e c).chamberSet = c.chamberSet)
    (hY' : e' (D.braidSite h.1) = D'.braidSite h.length_le)
    (hJ' : ∀ c, c ≠ D.braidSite h.1 → (e' c).chamberSet = c.chamberSet) : e = e' := by
  funext c
  by_cases hc : c = D.braidSite h.1
  · rw [hc, hY, hY']
  · have hs : (e c).chamberSet = (e' c).chamberSet := by rw [hJ c hc, hJ' c hc]
    exact Chamber.eq_of_gap_of_chamberSet (Chamber.gap_eq_of_chamberSet_eq hs) hs

/-- **A braid move is a mutation**, in either direction: there is an isomorphism from
`μ_Y(Q(D))` to `Q(D')` sending the site `Y` to the replacement `Z` and keeping the chamber set of
every other chamber.

In the direction `braidMove` constructs this is `braidIso`. In the other, `D` is the
first-direction move of `D'`, whose replacement is `Y` and whose site is `Z`; `braidIso` for that
move is an isomorphism `μ_Z(Q(D')) ≅ Q(D)` sending `Z` to `Y`, and `Quiver.Iso.symmOfMutate` turns
it round, mutation at one vertex being an involution. -/
@[cluster_algebras "prop_braid_is_mutation"]
theorem exists_iso (h : IsBraidMove D D' p) :
    ∃ ψ : (D.wiringQuiver.mutate h.braidSite_notMem_frozen).Iso D'.wiringQuiver,
      ψ.equiv (D.braidSite h.1) = D'.braidSite h.length_le ∧
        ∀ c, c ≠ D.braidSite h.1 → (ψ.equiv c).chamberSet = c.chamberSet := by
  obtain ⟨hp, hgh, hgg, rfl⟩ | ⟨hp, hgh, hgg, rfl⟩ := h.eq_braidMove_or
  · exact ⟨D.braidIso hp hgh hgg, D.braidChamber_braidSite hp hgh hgg,
      fun c hc => D.chamberSet_braidChamber_of_ne hp hgh hgg hc⟩
  · have he : (D'.braidIso hp hgh hgg).equiv (D'.braidSite hp) =
        (D'.braidMove p hp hgh hgg).braidSite h.1 := D'.braidChamber_braidSite hp hgh hgg
    refine ⟨(D'.braidIso hp hgh hgg).symmOfMutate h.braidSite_notMem_frozen he,
      (Equiv.symm_apply_eq _).2 he.symm, fun c hc => ?_⟩
    have hcc : D'.braidChamber hp hgh hgg ((D'.braidEquiv hp hgh hgg).symm c) = c :=
      (D'.braidEquiv hp hgh hgg).apply_symm_apply c
    have hne : (D'.braidEquiv hp hgh hgg).symm c ≠ D'.braidSite hp :=
      fun hY => hc (by rw [← hcc, hY]; exact he)
    change ((D'.braidEquiv hp hgh hgg).symm c).chamberSet = c.chamberSet
    rw [← D'.chamberSet_braidChamber_of_ne hp hgh hgg hne, hcc]

/-- **Exactly one bijection of chambers sends the site to the replacement and keeps every other
chamber set**, for a braid move in either direction. -/
@[cluster_algebras "prop_braid_is_mutation"]
theorem existsUnique_equiv (h : IsBraidMove D D' p) :
    ∃! ψ : D.Chamber ≃ D'.Chamber, ψ (D.braidSite h.1) = D'.braidSite h.length_le ∧
      ∀ c, c ≠ D.braidSite h.1 → (ψ c).chamberSet = c.chamberSet := by
  obtain ⟨φ, hY, hJ⟩ := h.exists_iso
  exact ⟨φ.equiv, ⟨hY, hJ⟩, fun ψ hψ =>
    Equiv.coe_fn_injective (h.eq_of_chamberSet hψ.1 hψ.2 hY hJ)⟩

/-- **That bijection is an isomorphism from `μ_Y(Q(D))` to `Q(D')`**, for a braid move in either
direction: any bijection sending the site to the replacement and keeping every other chamber set
is the one of `exists_iso`, by `eq_of_chamberSet`. -/
@[cluster_algebras "prop_braid_is_mutation"]
def isoOfChamberSet (h : IsBraidMove D D' p) (ψ : D.Chamber ≃ D'.Chamber)
    (hY : ψ (D.braidSite h.1) = D'.braidSite h.length_le)
    (hJ : ∀ c, c ≠ D.braidSite h.1 → (ψ c).chamberSet = c.chamberSet) :
    (D.wiringQuiver.mutate h.braidSite_notMem_frozen).Iso D'.wiringQuiver where
  equiv := ψ
  mem_frozen_iff v := by
    obtain ⟨φ, hφY, hφJ⟩ := h.exists_iso
    rw [show ⇑ψ = ⇑φ.equiv from h.eq_of_chamberSet hY hJ hφY hφJ]
    exact φ.mem_frozen_iff v
  arrows_eq u v := by
    obtain ⟨φ, hφY, hφJ⟩ := h.exists_iso
    rw [show ⇑ψ = ⇑φ.equiv from h.eq_of_chamberSet hY hJ hφY hφJ]
    exact φ.arrows_eq u v

/-- The underlying bijection of `isoOfChamberSet ψ` is `ψ`. -/
@[simp]
theorem isoOfChamberSet_equiv (h : IsBraidMove D D' p) (ψ : D.Chamber ≃ D'.Chamber)
    (hY : ψ (D.braidSite h.1) = D'.braidSite h.length_le)
    (hJ : ∀ c, c ≠ D.braidSite h.1 → (ψ c).chamberSet = c.chamberSet) :
    (h.isoOfChamberSet ψ hY hJ).equiv = ψ := rfl

end IsBraidMove

end WiringDiagram

end ClusterAlgebras

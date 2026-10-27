/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.ChamberAtTime
public import ClusterAlgebras.TotalPositivity.ReducedWords

/-!
# Every permutation occurs in a wiring diagram

Every permutation `u` of the strands is one of the wire permutations `u_t` of some wiring
diagram, and consequently every nonempty proper subset `J` of the strands is the chamber set of
a chamber of some wiring diagram.

The proof counts inversions. Multiplying a permutation `v` on the right by the adjacent
transposition `s_g` reverses the relative order of exactly the pair of levels `g, g + 1`, so it
changes the number of inversions of `v` by one: down if `g` is a descent of `v`, up otherwise.
A permutation without descents is the identity and one without ascents is `w₀`, so from `u`
one can walk down to the identity in `inv(u)` steps and up to `w₀` in `N - inv(u)` steps. The
first walk, read backwards, spells `u` as a word of length `inv(u)`; appending the second gives
a word of length `N` with product `w₀`, that is a wiring diagram, whose `inv(u)`-th partial
product is `u`.

## Main results

* `ClusterAlgebras.WiringDiagram.exists_wire_eq`: every permutation of the strands is `u_t`
  for some wiring diagram and some `t ∈ [0, N]`.
* `ClusterAlgebras.WiringDiagram.exists_chamberSet_eq`: every nonempty proper subset of the
  strands is the chamber set of a chamber of some wiring diagram.

## Implementation notes

Indices are 0-based, as in `ClusterAlgebras.WiringDiagram.Basic`: there are `n + 2` strands,
and FWZ's `{u(1), …, u(k)}` is the image of the first `k` levels `Finset.Iic g.castSucc`
under `u`, where the gap `g` has `g + 1 = k`. The inversion count is
`ClusterAlgebras.inversionNumber`, and the walk down to the identity is
`ClusterAlgebras.exists_isReducedWord`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 1.
-/

@[expose] public section

namespace ClusterAlgebras

namespace WiringDiagram

variable {n : ℕ}

open Finset

/-- A permutation other than `w₀` has an ascent. -/
private theorem exists_ascent {v : Equiv.Perm (Fin (n + 2))} (hv : v ≠ Fin.revPerm) :
    ∃ g : Fin (n + 1), v g.castSucc < v g.succ := by
  by_contra hcon
  push Not at hcon
  have hanti : Antitone v := Fin.antitone_iff_succ_le.2 hcon
  have hmono : Monotone ⇑(v * Fin.revPerm : Equiv.Perm (Fin (n + 2))) := fun a b hab => by
    simpa using hanti (Fin.rev_le_rev.2 hab)
  exact hv ((mul_eq_one_iff_eq_inv.1 ((Equiv.Perm.monotone_iff _).1 hmono)).trans
    Fin.revPerm_symm)

/-- **Up to `w₀`.** A permutation with `N - k` inversions reaches `w₀` after multiplying on the
right by `k` adjacent transpositions. -/
private theorem exists_word_mul_prod_eq_revPerm :
    ∀ (k : ℕ) (v : Equiv.Perm (Fin (n + 2))), inversionNumber v + k = (n + 2).choose 2 →
      ∃ l : List (Fin (n + 1)), l.length = k ∧ v * (l.map gapSwap).prod = Fin.revPerm := by
  intro k
  induction k with
  | zero =>
    intro v hv
    refine ⟨[], rfl, ?_⟩
    by_contra hne
    obtain ⟨g, hg⟩ := exists_ascent (v := v) (by simpa using hne)
    have := inversionNumber_mul_gapSwap_of_lt v hg
    have := inversionNumber_le_choose (v * gapSwap g)
    omega
  | succ k ih =>
    intro v hv
    have hne : v ≠ Fin.revPerm := by
      rintro rfl
      rw [inversionNumber_revPerm] at hv
      omega
    obtain ⟨g, hg⟩ := exists_ascent hne
    obtain ⟨l, hl, hprod⟩ :=
      ih (v * gapSwap g) (by rw [inversionNumber_mul_gapSwap_of_lt v hg]; omega)
    refine ⟨g :: l, by simp [hl], ?_⟩
    rw [List.map_cons, List.prod_cons, ← mul_assoc, hprod]

/-- **Every permutation occurs in a wiring diagram.** For every permutation `u` of the strands
there are a wiring diagram `D` and a moment `t ∈ [0, N]` with `u_t = u`. -/
@[cluster_algebras "lem_permutation_in_wiring_diagram"]
theorem exists_wire_eq (u : Equiv.Perm (Fin (n + 2))) :
    ∃ (D : WiringDiagram n) (t : ℕ), t ≤ D.word.length ∧ D.wire t = u := by
  have hle := inversionNumber_le_choose u
  obtain ⟨l₁, hprod₁, hl₁⟩ := exists_isReducedWord u
  obtain ⟨l₂, hl₂, hprod₂⟩ :=
    exists_word_mul_prod_eq_revPerm ((n + 2).choose 2 - inversionNumber u) u (by omega)
  refine ⟨⟨l₁ ++ l₂, by simp [hl₁, hl₂]; omega, ?_⟩, l₁.length, by simp, ?_⟩
  · rw [List.map_append, List.prod_append, hprod₁, hprod₂]
  · rw [wire, List.map_append, List.take_left' (by simp), hprod₁]

/-- **Every nonempty proper subset of the strands is a chamber set.** For `∅ ≠ J ⊊ [1, n]`
there are a wiring diagram `D` and a chamber `c` of `D` with `J(c) = J`. -/
@[cluster_algebras "lem_flag_set_is_chamber_set"]
theorem exists_chamberSet_eq {J : Finset (Fin (n + 2))} (hJ : J.Nonempty)
    (hJ' : J ≠ Finset.univ) : ∃ (D : WiringDiagram n) (c : D.Chamber), c.chamberSet = J := by
  have hpos := hJ.card_pos
  have hlt : #J < n + 2 := by simpa using (card_lt_iff_ne_univ _).2 hJ'
  let g : Fin (n + 1) := ⟨#J - 1, by omega⟩
  obtain ⟨u, hu⟩ := Equiv.Perm.exists_map_finset_eq (Iic g.castSucc) J (by simp [g]; omega)
  obtain ⟨D, t, ht, hwire⟩ := exists_wire_eq u
  obtain ⟨c, -, hc⟩ := D.exists_chamberSet_eq_map_wire ht g
  exact ⟨D, c, by rw [hc, hwire, hu]⟩

end WiringDiagram

end ClusterAlgebras

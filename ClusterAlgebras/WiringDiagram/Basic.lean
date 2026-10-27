/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.WiringDiagram.Word

/-!
# Wiring diagrams

A wiring diagram on `n + 2` strands is a picture of the strands in a strip, crossing pairwise.
Such pictures, up to isotopy, correspond to reduced decompositions of the longest permutation
`w₀`, so a wiring diagram is taken here to be a reduced word for `w₀`, and every notion is
built combinatorially from that word.

## Implementation notes

* Strands are `Fin (n+2)` and gaps are `Fin (n+1)`, so there are at least two strands. A gap
  `g` separates the adjacent levels `g.castSucc` and `g.succ`. Everything is 0-based.

* `w₀` is `Fin.revPerm`, the permutation `ℓ ↦ Fin.rev ℓ`.

* The word is a `List`, not a function on positions. `List.take` gives the partial products
  `u_t`, and `List.count` gives the level multiplicities, which is how `multiplicity` is
  defined. Positions are 0-based indices into the list.

* Reduced-word theory is not used. There is no `CoxeterSystem` instance for
  `Equiv.Perm (Fin n)` in Mathlib and no longest-element API, so `w₀` is written out and
  `bijective_crossedPair` is proved by counting: each unordered pair of wires must reverse its
  relative order, a crossing reverses exactly one pair's order because the two levels it
  exchanges are adjacent, and there are as many positions as pairs.
-/

@[expose] public section

namespace ClusterAlgebras

variable {n : ℕ}

attribute [cluster_algebras "def_wiring_diagram"] WiringDiagram

namespace WiringDiagram

/-- A wiring diagram is determined by its word: the other two fields are proofs. -/
theorem ext' {D D' : WiringDiagram n} (h : D.word = D'.word) : D = D' := by
  cases D; cases D'; subst h; rfl

variable (D : WiringDiagram n)

attribute [cluster_algebras "def_wire_positions"] wire

/-- Before any crossing every wire is at its own level. -/
@[simp]
theorem wire_zero : D.wire 0 = 1 := by simp [wire]

/-- Each crossing multiplies on the right by the transposition at its gap:
`u_{t+1} = u_t s_{i_t}`. -/
theorem wire_succ {t : ℕ} (ht : t < D.word.length) :
    D.wire (t + 1) = D.wire t * gapSwap (D.levelAt t) := by
  have ht' : t < (D.word.map gapSwap).length := by simpa using ht
  rw [wire, wire, List.prod_take_succ _ t ht', List.getElem_map, levelAt,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]

/-- After all the crossings the wires have been reversed: the word spells `w₀`. -/
theorem wire_length : D.wire D.word.length = Fin.revPerm := by
  rw [wire, List.take_of_length_le (by simp), D.prod_eq]

/-- Before any crossing every wire sits at its own level. -/
@[simp]
theorem levelOf_zero (v : Fin (n + 2)) : D.levelOf 0 v = v := by
  rw [levelOf, D.wire_zero]; rfl

/-- After all the crossings wire `v` sits at level `Fin.rev v`. -/
theorem levelOf_length (v : Fin (n + 2)) : D.levelOf D.word.length v = Fin.rev v := by
  simp [levelOf, D.wire_length]

/-- A crossing moves the levels by the adjacent transposition at its gap. -/
theorem levelOf_succ {t : ℕ} (ht : t < D.word.length) (v : Fin (n + 2)) :
    D.levelOf (t + 1) v = gapSwap (D.levelAt t) (D.levelOf t v) := by
  rw [levelOf, levelOf, D.wire_succ ht]; rfl

attribute [cluster_algebras "def_level_multiplicity"] multiplicity

/-! ### Reading a short stretch of the word

The two moves each replace a stretch of two or three entries, so both need that stretch spelled
out in terms of `levelAt`. -/

/-- `levelAt` in terms of `getElem?`, which is total. -/
theorem levelAt_eq_getElem? (k : ℕ) : D.levelAt k = D.word[k]?.getD 0 := by
  rw [levelAt, List.getD_eq_getElem?_getD]

/-- `levelAt` at a genuine position is the word's entry there. -/
theorem levelAt_eq_getElem {k : ℕ} (hk : k < D.word.length) : D.levelAt k = D.word[k] := by
  rw [levelAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

/-- The two entries of the word at positions `p` and `p + 1`. -/
theorem take_two_drop_word {p : ℕ} (hp : p + 2 ≤ D.word.length) :
    (D.word.drop p).take 2 = [D.levelAt p, D.levelAt (p + 1)] := by
  have h1 : p < D.word.length := by omega
  have h2 : p + 1 < D.word.length := by omega
  rw [D.levelAt_eq_getElem h1, D.levelAt_eq_getElem h2,
    List.drop_eq_getElem_cons h1, List.take_succ_cons, List.drop_eq_getElem_cons h2,
    List.take_succ_cons]
  simp

/-- The three entries of the word at positions `p`, `p + 1` and `p + 2`. -/
theorem take_three_drop_word {p : ℕ} (hp : p + 3 ≤ D.word.length) :
    (D.word.drop p).take 3 = [D.levelAt p, D.levelAt (p + 1), D.levelAt (p + 2)] := by
  have h1 : p < D.word.length := by omega
  have h2 : p + 1 < D.word.length := by omega
  have h3 : p + 2 < D.word.length := by omega
  rw [D.levelAt_eq_getElem h1, D.levelAt_eq_getElem h2, D.levelAt_eq_getElem h3,
    List.drop_eq_getElem_cons h1, List.take_succ_cons, List.drop_eq_getElem_cons h2,
    List.take_succ_cons, List.drop_eq_getElem_cons h3, List.take_succ_cons]
  simp

/-! ### The two moves

Both replace a stretch of the word by another of the same length whose product is the same, so
both go through one construction. -/

/-- Replacing a stretch of `D`'s word by one of the same length and the same product gives
another wiring diagram. -/
def splice (p : ℕ) (new : List (Fin (n + 1))) (hp : p + new.length ≤ D.word.length)
    (hprod : (new.map gapSwap).prod = (((D.word.drop p).take new.length).map gapSwap).prod) :
    WiringDiagram n where
  word := spliceWord D.word p new
  length_eq := by rw [length_spliceWord hp, D.length_eq]
  prod_eq := by rw [prod_map_spliceWord gapSwap hprod, D.prod_eq]

/-- The word of a splice is the spliced word. -/
@[simp]
theorem word_splice {p : ℕ} {new : List (Fin (n + 1))} {hp hprod} :
    (D.splice p new hp hprod).word = spliceWord D.word p new := rfl

/-- The **commutation move**: sliding the crossings at positions `p` and `p + 1`, at
non-adjacent gaps, past one another. -/
@[cluster_algebras "lem_commutation_invariance"]
def commutationMove (p : ℕ) (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) : WiringDiagram n :=
  D.splice p [D.levelAt (p + 1), D.levelAt p] (by simpa using hp) (by
    rw [show ([D.levelAt (p + 1), D.levelAt p] : List (Fin (n + 1))).length = 2 from rfl,
      D.take_two_drop_word hp]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact gapSwap_comm hne.symm)

/-- The **braid move**: replacing the factor `(g, h, g)` at position `p` by `(h, g, h)` when the
two gaps are adjacent. It produces a wiring diagram by the braid relation. -/
def braidMove (p : ℕ) (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) : WiringDiagram n :=
  D.splice p [D.levelAt (p + 1), D.levelAt p, D.levelAt (p + 1)] (by simpa using hp) (by
    rw [show ([D.levelAt (p + 1), D.levelAt p, D.levelAt (p + 1)] :
        List (Fin (n + 1))).length = 3 from rfl, D.take_three_drop_word hp, hgg]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (gapSwap_braid hgh).symm)

/-! ### Every gap is crossed

The set of wires lying at or below a gap can only change at a crossing of that gap, and it
does change between the two ends of the word, so every gap is crossed. -/

/-- Membership in `belowSet`, unfolded. -/
@[simp]
theorem mem_belowSet {t : ℕ} {g : Fin (n + 1)} {v : Fin (n + 2)} :
    v ∈ D.belowSet t g ↔ D.levelOf t v ≤ g.castSucc := by
  simp [belowSet]

/-- **A crossing at another gap does not change which wires lie below `g`.** The two levels a
crossing exchanges are adjacent, so if its gap is not `g` then both lie on the same side
of `g`. -/
theorem belowSet_succ_of_ne {t : ℕ} (ht : t < D.word.length) {g : Fin (n + 1)}
    (h : D.levelAt t ≠ g) : D.belowSet (t + 1) g = D.belowSet t g := by
  ext v
  rw [mem_belowSet, mem_belowSet, D.levelOf_succ ht]
  set h' := D.levelAt t with hh
  set x := D.levelOf t v with hx
  -- the two exchanged levels have values `h'` and `h' + 1`, and `h' ≠ g`
  have hne : (h' : ℕ) ≠ (g : ℕ) := fun hc => h (Fin.ext hc)
  by_cases hc1 : x = h'.castSucc
  · rw [hc1, gapSwap_castSucc]
    simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
    omega
  · by_cases hc2 : x = h'.succ
    · rw [hc2, gapSwap_succ]
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
      omega
    · rw [gapSwap_of_ne _ hc1 hc2]

/-- **Every gap is crossed at least once.** The wire `0` lies below every gap at the start and
below none at the end, since `w₀` sends it to the top level. -/
@[cluster_algebras "lem_every_level_occurs"]
theorem one_le_multiplicity (g : Fin (n + 1)) : 1 ≤ D.multiplicity g := by
  rcases Nat.eq_zero_or_pos (D.multiplicity g) with h | h
  · -- no crossing at `g`, so the set below `g` never changes
    exfalso
    have hconst : ∀ t ≤ D.word.length, D.belowSet t g = D.belowSet 0 g := by
      intro t ht
      induction t with
      | zero => rfl
      | succ t ih =>
        have htl : t < D.word.length := by omega
        rw [D.belowSet_succ_of_ne htl ?_, ih (by omega)]
        -- the level at `t` is not `g`, since `g` never occurs in the word
        intro hc
        have hmem : g ∈ D.word := by
          rw [← hc, levelAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl]
          exact List.getElem_mem htl
        rw [multiplicity, List.count_eq_zero] at h
        exact h hmem
    have h0 : (0 : Fin (n + 2)) ∈ D.belowSet 0 g := by simp
    have hN : (0 : Fin (n + 2)) ∉ D.belowSet D.word.length g := by
      rw [mem_belowSet, D.levelOf_length]
      simp only [Fin.le_def, Fin.val_rev, Fin.val_castSucc, Fin.val_zero]
      have := g.isLt
      omega
    rw [hconst D.word.length le_rfl] at hN
    exact hN h0
  · exact h

/-! ### Each pair of wires crosses exactly once

The counting argument, in place of reduced-word theory: a crossing reverses the order of
exactly one pair of wires, every pair has its order reversed between the two ends of the word,
and there are as many positions as pairs. -/

/-- The unordered pair of wires that cross at position `t`: the wires occupying the two levels
that the crossing exchanges. -/
def crossedPair (t : ℕ) : Sym2 (Fin (n + 2)) :=
  s(D.wire t (D.levelAt t).castSucc, D.wire t (D.levelAt t).succ)

/-- The two wires crossing at a position are distinct. -/
theorem crossedPair_not_isDiag (t : ℕ) : ¬(D.crossedPair t).IsDiag := by
  rw [crossedPair, Sym2.mk_isDiag_iff]
  intro hc
  have := (D.wire t).injective hc
  exact absurd (congrArg Fin.val this) (by simp)

/-- **Away from its own crossing, a pair of wires keeps its relative order.** -/
theorem levelOf_lt_iff_succ {t : ℕ} (ht : t < D.word.length) {v w : Fin (n + 2)}
    (h : D.crossedPair t ≠ s(v, w)) :
    (D.levelOf (t + 1) v < D.levelOf (t + 1) w ↔ D.levelOf t v < D.levelOf t w) := by
  rw [D.levelOf_succ ht, D.levelOf_succ ht]
  refine gapSwap_lt_iff ?_ ?_
  · rintro ⟨hx, hy⟩
    refine h ?_
    have hxv : D.levelOf t v = (D.levelAt t).castSucc := Fin.ext hx
    have hyw : D.levelOf t w = (D.levelAt t).succ := Fin.ext hy
    rw [crossedPair, ← hxv, ← hyw]
    simp [levelOf]
  · rintro ⟨hx, hy⟩
    refine h ?_
    have hxv : D.levelOf t v = (D.levelAt t).succ := Fin.ext hx
    have hyw : D.levelOf t w = (D.levelAt t).castSucc := Fin.ext hy
    rw [crossedPair, ← hxv, ← hyw, Sym2.eq_swap]
    simp [levelOf]

/-- **The relative order of two wires is unchanged over any stretch containing none of their
crossings.** -/
theorem levelOf_lt_iff_of_forall {v w : Fin (n + 2)} {r : ℕ} (hr : r ≤ D.word.length)
    (h : ∀ s < r, D.crossedPair s ≠ s(v, w)) :
    (D.levelOf r v < D.levelOf r w ↔ v < w) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [D.levelOf_lt_iff_succ (by omega) (h r (by omega))]
    exact ih (by omega) fun s hs => h s (by omega)

/-- **The relative order of two wires is unchanged over any stretch containing none of their
crossings**, this time comparing the two ends of the stretch rather than one end and the labels. -/
theorem levelOf_lt_iff_of_le {v w : Fin (n + 2)} {r : ℕ} :
    ∀ t, r ≤ t → t ≤ D.word.length → (∀ s, r ≤ s → s < t → D.crossedPair s ≠ s(v, w)) →
      (D.levelOf t v < D.levelOf t w ↔ D.levelOf r v < D.levelOf r w) := by
  intro t hrt
  induction t, hrt using Nat.le_induction with
  | base => intro _ _; rfl
  | succ k hk ih =>
    intro hkl h
    rw [D.levelOf_lt_iff_succ (by omega) (h k (by omega) (by omega))]
    exact ih (by omega) fun s hs1 hs2 => h s hs1 (by omega)

/-- **Each pair of distinct wires crosses at some position.** Wire `v` starts at level `v` and
ends at level `Fin.rev v`, so for two distinct wires the order of their levels is reversed
between the two ends of the word; since only their own crossing can reverse it, one of the
crossings must be theirs. -/
theorem exists_crossedPair_eq {v w : Fin (n + 2)} (hvw : v ≠ w) :
    ∃ t < D.word.length, D.crossedPair t = s(v, w) := by
  by_contra hcon
  push Not at hcon
  have hend := D.levelOf_lt_iff_of_forall (r := D.word.length) le_rfl fun s hs => hcon s hs
  rw [D.levelOf_length, D.levelOf_length, Fin.rev_lt_rev] at hend
  rcases lt_or_gt_of_ne hvw with hlt | hlt
  · exact absurd (hend.2 hlt) (by omega)
  · exact absurd (hend.1 hlt) (by omega)

/-- **Each pair of wires crosses exactly once**: the map sending a position to the pair of wires
crossing there is a bijection onto the two-element subsets of the strands. -/
@[cluster_algebras "lem_crossing_pairs_bijection"]
theorem bijective_crossedPair :
    Function.Bijective fun t : Fin D.word.length =>
      (⟨D.crossedPair t, D.crossedPair_not_isDiag t⟩ :
        {e : Sym2 (Fin (n + 2)) // ¬e.IsDiag}) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with | _ v w => ?_
    have hvw : v ≠ w := by simpa [Sym2.mk_isDiag_iff] using he
    obtain ⟨t, ht, hte⟩ := D.exists_crossedPair_eq hvw
    exact ⟨⟨t, ht⟩, Subtype.ext hte⟩
  · rw [Fintype.card_fin, Sym2.card_subtype_not_diag, Fintype.card_fin, D.length_eq]

/-- The position at which a given pair of distinct wires crosses is unique. -/
theorem crossedPair_injOn {s t : ℕ} (hs : s < D.word.length) (ht : t < D.word.length)
    (h : D.crossedPair s = D.crossedPair t) : s = t := by
  have := D.bijective_crossedPair.injective
    (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) (Subtype.ext h)
  simpa using this

/-- **At a crossing the wire arriving from below has the smaller label.** The two wires cross
only at this position, so their order is the one they started with, and the one below started
lower. -/
@[cluster_algebras "lem_lower_wire_smaller"]
theorem wire_castSucc_lt_wire_succ {t : ℕ} (ht : t < D.word.length) :
    D.wire t (D.levelAt t).castSucc < D.wire t (D.levelAt t).succ := by
  set v := D.wire t (D.levelAt t).castSucc with hv
  set w := D.wire t (D.levelAt t).succ with hw
  -- no earlier position crosses this pair, by uniqueness
  have hno : ∀ s < t, D.crossedPair s ≠ s(v, w) := by
    intro s hs hc
    exact absurd (D.crossedPair_injOn (by omega) ht (hc.trans (by rw [crossedPair])))
      (by omega)
  have hord := D.levelOf_lt_iff_of_forall (r := t) (by omega) hno
  -- at time `t` the two wires sit at the two levels of the crossing, which are in order
  have hlv : D.levelOf t v = (D.levelAt t).castSucc := by simp [levelOf, hv]
  have hlw : D.levelOf t w = (D.levelAt t).succ := by simp [levelOf, hw]
  rw [hlv, hlw] at hord
  exact hord.1 (by simp [Fin.lt_def])

end WiringDiagram

end ClusterAlgebras

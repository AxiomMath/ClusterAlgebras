/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.ChamberAtTime
public import ClusterAlgebras.WiringDiagram.Commutation
public import ClusterAlgebras.WiringDiagram.BraidIso

/-!
# Commutations, braid moves and chamber sets

The two local moves on wiring diagrams in FWZ's Chapter 1, and what they do to chamber sets.
A **commutation** exchanges two adjacent letters `i_p, i_{p+1}` of the word with
`|i_p - i_{p+1}| ≥ 2`; every chamber set of the new diagram is then a chamber set of the old
one. A **braid move** replaces a factor `(g, h, g)` with `|g - h| = 1` by `(h, g, h)`; every
chamber set of the new diagram other than that of the replacement `Z` is a chamber set of the old
one. The site `Y` and the replacement `Z` carry the sets `S ∪ {β}` and `S ∪ {α, γ}`, in one order
or the other, for some `S` and some `α < β < γ` outside it, and the four sets `S ∪ {α}`,
`S ∪ {γ}`, `S ∪ {α, β}`, `S ∪ {β, γ}` are all chamber sets of the old diagram. These are the six
sets of the three-term relation for flag minors, which is what makes a braid move act on chamber
minors as a mutation.

## Main definitions

* `WiringDiagram.IsCommutation D D' p`: `D'` is obtained from `D` by the commutation at `p`.

The braid move `WiringDiagram.IsBraidMove D D' p`, in either direction, is defined in
`ClusterAlgebras.WiringDiagram.Braid`.

## Main results

* `WiringDiagram.IsCommutation.exists_chamberSet_eq`: a commutation creates no chamber set.
* `WiringDiagram.IsBraidMove.exists_chamberSet_eq`: a braid move creates no chamber set other
  than that of its replacement.
* `WiringDiagram.IsBraidMove.exists_exchange_sets`: the chamber sets of the site and the
  replacement, and the four chamber sets around them.

## Implementation notes

* Indices are 0-based, as in `ClusterAlgebras.WiringDiagram.Basic`: FWZ's position `p` is
  the word index `p`, read as the letters at `p` and `p + 1` (or `p`, `p + 1`, `p + 2`), and
  FWZ's level `ℓ` is `ℓ - 1`. FWZ's `u_{p-1}` is `D.wire p`.
* `WiringDiagram.braidMove` constructs only the braid move `(g, g + 1, g) ↦ (g + 1, g, g + 1)`.
  FWZ allow `|g - h| = 1` in both directions, and the opposite one at `p` on `D` is the
  diagram `D'` with `D = D'.braidMove p …`. `IsBraidMove` covers both, as a relation on the words;
  `IsBraidMove.eq_braidMove_or` (in `ClusterAlgebras.WiringDiagram.BraidIso`) identifies each
  instance with one of the two constructions. The site of the move is `D.braidSite` and the
  replacement is `D'.braidSite`, which in the first direction is `D.braidReplacement` by
  definition.
* FWZ state the exchange as an equality of unordered pairs
  `{J(Y), J(Z)} = {S ∪ {β}, S ∪ {α, γ}}`. The two sets on the right have different sizes, so this
  is exactly the disjunction of the two ordered equalities, which is how it is stated here.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras, Chapter 1*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### Splicing, entry by entry -/

section Splice

variable {α : Type*}

/-- A list of the same length that agrees with `l` outside the stretch of length `new.length` at
`p`, and with `new` on it, is the splice. -/
theorem eq_spliceWord_of_getElem? {l m new : List α} {p : ℕ} (hp : p + new.length ≤ l.length)
    (hout : ∀ i, i < p ∨ p + new.length ≤ i → m[i]? = l[i]?)
    (hmid : ∀ i < new.length, m[p + i]? = new[i]?) : m = spliceWord l p new := by
  refine List.ext_getElem? fun i => ?_
  by_cases h1 : i < p
  · rw [getElem?_spliceWord_left (by omega) h1, hout i (Or.inl h1)]
  by_cases h2 : p + new.length ≤ i
  · rw [getElem?_spliceWord_right (by omega) h2, hout i (Or.inr h2)]
  obtain ⟨j, rfl⟩ : ∃ j, i = p + j := ⟨i - p, by omega⟩
  rw [getElem?_spliceWord_mid (by omega) (by omega), hmid j (by omega)]

/-- Exchanging two adjacent entries is splicing in the exchanged pair. -/
theorem set_set_eq_spliceWord {l : List α} {p : ℕ} (hp : p + 2 ≤ l.length) (a b : α) :
    (l.set p a).set (p + 1) b = spliceWord l p [a, b] := by
  refine eq_spliceWord_of_getElem? (by simpa using hp) (fun i hi => ?_) (fun i hi => ?_)
  · simp only [List.length_cons, List.length_nil] at hi
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · obtain _ | _ | i := i
    · simp [show p < l.length by omega]
    · simp [show p + 1 < l.length by omega]
    · simp only [List.length_cons, List.length_nil] at hi
      omega

/-- Splicing at `p` leaves the first `p` entries alone. -/
theorem take_spliceWord {l new : List α} {p : ℕ} (hp : p ≤ l.length) :
    (spliceWord l p new).take p = l.take p := by
  simp [spliceWord, hp]

end Splice

namespace WiringDiagram

variable {n : ℕ}

/-! ### Reading a diagram off its levels -/

/-- At a genuine position the word's entry is the level of the crossing there. -/
theorem getElem?_word (D : WiringDiagram n) {k : ℕ} (hk : k < D.word.length) :
    D.word[k]? = some (D.levelAt k) := by
  rw [D.levelAt_eq_getElem hk, List.getElem?_eq_getElem hk]

/-- The wires after `t` crossings depend only on the first `t` letters. -/
theorem wire_eq_of_take_eq {D E : WiringDiagram n} {t : ℕ}
    (h : D.word.take t = E.word.take t) : D.wire t = E.wire t := by
  rw [wire, wire, ← List.map_take, ← List.map_take, h]

/-- The wire at level `x` after `t` crossings sits at level `x`. -/
@[simp]
theorem levelOf_wire (D : WiringDiagram n) (t : ℕ) (x : Fin (n + 2)) :
    D.levelOf t (D.wire t x) = x :=
  (D.wire t).symm_apply_apply x

/-- A wire is the one at level `x` exactly when it sits at level `x`. -/
theorem eq_wire_iff (D : WiringDiagram n) {t : ℕ} {v x : Fin (n + 2)} :
    v = D.wire t x ↔ D.levelOf t v = x :=
  (Equiv.symm_apply_eq _).symm

/-! ### Commutations -/

/-- `D'` is obtained from `D` by the **commutation** at `p`: the letters at `p` and `p + 1` are
at gaps at distance at least two, and `D'` exchanges them, leaving every other letter alone. -/
@[cluster_algebras "def_commutation_move"]
def IsCommutation (D D' : WiringDiagram n) (p : ℕ) : Prop :=
  p + 2 ≤ D.word.length ∧
    ((D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) ∧
    D'.word = (D.word.set p (D.levelAt (p + 1))).set (p + 1) (D.levelAt p)

/-- **A commutation is the commutation move.** -/
theorem IsCommutation.eq_commutationMove {D D' : WiringDiagram n} {p : ℕ}
    (h : IsCommutation D D' p) : D' = D.commutationMove p h.1 h.2.1 :=
  ext' (h.2.2.trans (by rw [commutationMove, word_splice, set_set_eq_spliceWord h.1]))

/-- The commutation move is a commutation. -/
theorem isCommutation_commutationMove (D : WiringDiagram n) {p : ℕ}
    (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) :
    IsCommutation D (D.commutationMove p hp hne) p :=
  ⟨hp, hne, by rw [commutationMove, word_splice, set_set_eq_spliceWord hp]⟩

/-- **A commutation creates no chamber set**: every chamber set of `D'` is one of `D`. -/
@[cluster_algebras "lem_commutation_chamber_sets"]
theorem IsCommutation.exists_chamberSet_eq {D D' : WiringDiagram n} {p : ℕ}
    (h : IsCommutation D D' p) (c' : D'.Chamber) :
    ∃ c : D.Chamber, c.chamberSet = c'.chamberSet := by
  obtain ⟨hp, hne, hw⟩ := h
  obtain rfl : D' = D.commutationMove p hp hne := IsCommutation.eq_commutationMove ⟨hp, hne, hw⟩
  exact ⟨(D.commEquiv hp hne).symm c', by
    rw [← D.chamberSet_commEquiv hp hne, Equiv.apply_symm_apply]⟩

/-! ### Braid moves in both directions -/

namespace IsBraidMove

variable {D D' : WiringDiagram n} {p : ℕ}

/-- Before the move the wires of the two diagrams agree. -/
theorem wire_eq (h : IsBraidMove D D' p) : D'.wire p = D.wire p :=
  wire_eq_of_take_eq (by rw [h.2.2.2, take_spliceWord (by have := h.1; omega)])

end IsBraidMove

/-- The constructed braid move undone, `(g + 1, g, g + 1) ↦ (g, g + 1, g)`, is a braid move. -/
theorem isBraidMove_braidMove_reverse (D' : WiringDiagram n) {p : ℕ} (hp : p + 3 ≤ D'.word.length)
    (hgh : (D'.levelAt p : ℕ) + 1 = (D'.levelAt (p + 1) : ℕ))
    (hgg : D'.levelAt (p + 2) = D'.levelAt p) : IsBraidMove (D'.braidMove p hp hgh hgg) D' p := by
  have hlen := D'.length_word_braidMove hp hgh hgg
  obtain ⟨e0, e1, -⟩ := D'.levelAt_braidMove hp hgh hgg
  refine ⟨by rw [hlen]; exact hp, D'.gg_braidMove hp hgh hgg, D'.adj_braidMove hp hgh hgg, ?_⟩
  rw [e0, e1]
  refine eq_spliceWord_of_getElem? (by simpa [hlen] using hp) (fun i hi => ?_) (fun i hi => ?_)
  · simp only [List.length_cons, List.length_nil] at hi
    rw [braidMove, word_splice]
    rcases hi with hi | hi
    · rw [getElem?_spliceWord_left (by omega) hi]
    · rw [getElem?_spliceWord_right (by omega) (by simpa using hi)]
  · obtain _ | _ | _ | i := i
    · simpa using D'.getElem?_word (k := p) (by omega)
    · simpa using D'.getElem?_word (k := p + 1) (by omega)
    · simpa [hgg] using D'.getElem?_word (k := p + 2) (by omega)
    · simp only [List.length_cons, List.length_nil] at hi
      omega

/-- **A braid move creates no chamber set other than its replacement's**, in the direction
`WiringDiagram.braidMove` constructs. -/
theorem exists_chamberSet_eq_of_ne_braidReplacement (D : WiringDiagram n) {p : ℕ}
    (hp : p + 3 ≤ D.word.length) (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (c' : (D.braidMove p hp hgh hgg).Chamber)
    (hc' : c' ≠ D.braidReplacement hp hgh hgg) :
    ∃ c : D.Chamber, c.chamberSet = c'.chamberSet := by
  refine ⟨(D.braidEquiv hp hgh hgg).symm c', ?_⟩
  have hne : (D.braidEquiv hp hgh hgg).symm c' ≠ D.braidSite hp := by
    intro hc
    apply hc'
    rw [← (D.braidEquiv hp hgh hgg).apply_symm_apply c', hc, braidEquiv_apply,
      braidChamber_braidSite]
  rw [← D.chamberSet_braidChamber_of_ne hp hgh hgg hne, ← braidEquiv_apply,
    Equiv.apply_symm_apply]

/-- **A braid move creates no chamber set other than its replacement's**: every chamber set of
`D'` other than that of the replacement `Z` is one of `D`. -/
@[cluster_algebras "lem_braid_other_chamber_sets"]
theorem IsBraidMove.exists_chamberSet_eq {D D' : WiringDiagram n} {p : ℕ}
    (h : IsBraidMove D D' p) (c' : D'.Chamber) (hc' : c' ≠ D'.braidSite h.length_le) :
    ∃ c : D.Chamber, c.chamberSet = c'.chamberSet := by
  obtain ⟨hp, hgh, hgg, rfl⟩ | ⟨hp, hgh, hgg, rfl⟩ := h.eq_braidMove_or
  · exact D.exists_chamberSet_eq_of_ne_braidReplacement hp hgh hgg c' hc'
  · exact ⟨D'.braidChamber hp hgh hgg c', D'.chamberSet_braidChamber_of_ne hp hgh hgg hc'⟩

/-! ### The exchange sets of a braid move -/

/-- **The exchange sets of a braid move, by direction.** There are `S` and `α < β < γ` outside
it such that the site and the replacement carry `S ∪ {β}` and `S ∪ {α, γ}` when the middle gap
is the upper one, and `S ∪ {α, γ}` and `S ∪ {β}` when it is the lower one; and `S ∪ {α}`,
`S ∪ {γ}`, `S ∪ {α, β}`, `S ∪ {β, γ}` are chamber sets of `D`. -/
theorem IsBraidMove.exists_exchange_sets_of_direction {D D' : WiringDiagram n} {p : ℕ}
    (h : IsBraidMove D D' p) :
    ∃ (S : Finset (Fin (n + 2))) (α β γ : Fin (n + 2)), α < β ∧ β < γ ∧ α ∉ S ∧ β ∉ S ∧ γ ∉ S ∧
      ((D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) →
        (D.braidSite h.1).chamberSet = S ∪ {β} ∧
          (D'.braidSite h.length_le).chamberSet = S ∪ {α, γ}) ∧
      ((D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ) →
        (D.braidSite h.1).chamberSet = S ∪ {α, γ} ∧
          (D'.braidSite h.length_le).chamberSet = S ∪ {β}) ∧
      (∃ c : D.Chamber, c.chamberSet = S ∪ {α}) ∧ (∃ c : D.Chamber, c.chamberSet = S ∪ {γ}) ∧
      (∃ c : D.Chamber, c.chamberSet = S ∪ {α, β}) ∧
      (∃ c : D.Chamber, c.chamberSet = S ∪ {β, γ}) := by
  have hp := h.1
  have hgg := h.2.1
  have hlen := h.length_word
  obtain ⟨e0, -, -⟩ := h.levelAt_eq
  -- the level of a wire after each of the three crossings, from its level before them
  have l1 : ∀ v, D.levelOf (p + 1) v = gapSwap (D.levelAt p) (D.levelOf p v) :=
    D.levelOf_succ (by omega)
  have l2 : ∀ v, D.levelOf (p + 2) v =
      gapSwap (D.levelAt (p + 1)) (gapSwap (D.levelAt p) (D.levelOf p v)) := fun v => by
    rw [D.levelOf_succ (t := p + 1) (by omega), l1]
  have l3 : ∀ v, D.levelOf (p + 3) v = gapSwap (D.levelAt p)
      (gapSwap (D.levelAt (p + 1)) (gapSwap (D.levelAt p) (D.levelOf p v))) := fun v => by
    rw [D.levelOf_succ (t := p + 2) (by omega), l2, hgg]
  have l1' : ∀ v, D'.levelOf (p + 1) v = gapSwap (D.levelAt (p + 1)) (D.levelOf p v) :=
    fun v => by rw [D'.levelOf_succ (by omega), e0, levelOf, levelOf, h.wire_eq]
  -- the wire at a level after the second crossing, from the wire there before the first
  have w2 : ∀ x, D.wire (p + 2) x =
      D.wire p (gapSwap (D.levelAt p) (gapSwap (D.levelAt (p + 1)) x)) := fun x => by
    rw [D.wire_succ (t := p + 1) (by omega), D.wire_succ (by omega)]
    rfl
  -- the wire arriving at a crossing from below has the smaller label
  have ord : ∀ t < D.word.length, ∀ a b : Fin (n + 2), (a : ℕ) = D.levelAt t →
      (b : ℕ) = D.levelAt t + 1 → D.wire t a < D.wire t b := by
    intro t ht a b ha hb
    obtain rfl : a = (D.levelAt t).castSucc := Fin.ext ha
    obtain rfl : b = (D.levelAt t).succ := Fin.ext hb
    exact D.wire_castSucc_lt_wire_succ ht
  have cg : ∀ {a b a' b' : Fin (n + 2)}, a = a' → b = b' →
      D.wire p a < D.wire p b → D.wire p a' < D.wire p b' := by
    rintro _ _ _ _ rfl rfl hab
    exact hab
  have ex : ∀ t ≤ D.word.length, ∀ (g : Fin (n + 1)) (s : Finset (Fin (n + 2))),
      D.belowSet t g = s → ∃ c : D.Chamber, c.chamberSet = s := fun t ht g s hs => by
    obtain ⟨c, -, hc⟩ := D.exists_chamberSet_eq_belowSet ht g
    exact ⟨c, hc.trans hs⟩
  have hY : (D.braidSite h.1).chamberSet = D.belowSet (p + 1) (D.levelAt p) :=
    Chamber.chamberSet_eq_belowSet _ (by omega) (D.inSpan_chamberAt _ _)
  have hZ : (D'.braidSite h.length_le).chamberSet = D'.belowSet (p + 1) (D.levelAt (p + 1)) := by
    rw [Chamber.chamberSet_eq_belowSet (D'.braidSite h.length_le) (t := p + 1) (by omega)
      (D'.inSpan_chamberAt _ _), gap_braidSite, e0]
  have hb := (D.levelAt p).isLt
  have hb' := (D.levelAt (p + 1)).isLt
  rcases h.2.2.1 with hup | hdown
  · -- the letters are `e, e + 1, e`
    obtain ⟨e, hg, hh⟩ : ∃ e, (D.levelAt p : ℕ) = e ∧ (D.levelAt (p + 1) : ℕ) = e + 1 :=
      ⟨_, rfl, hup.symm⟩
    refine ⟨Finset.univ.filter (fun v => (D.levelOf p v : ℕ) < e), D.wire p ⟨e, by omega⟩,
      D.wire p ⟨e + 1, by omega⟩, D.wire p ⟨e + 2, by omega⟩, ?_, ?_, ?_, ?_, ?_,
      fun _ => ⟨?_, ?_⟩, fun hc => absurd hc (by omega),
      ex p (by omega) (D.levelAt p) _ ?_, ex (p + 3) (by omega) (D.levelAt p) _ ?_,
      ex p (by omega) (D.levelAt (p + 1)) _ ?_, ex (p + 2) (by omega) (D.levelAt (p + 1)) _ ?_⟩
    · exact ord p (by omega) _ _ hg.symm (by dsimp only; omega)
    · have := ord (p + 2) (by omega) ⟨e, by omega⟩ ⟨e + 1, by omega⟩
        (by rw [hgg]; dsimp only; omega) (by rw [hgg]; dsimp only; omega)
      rw [w2, w2] at this
      exact cg (Fin.ext (by simp only [gapSwap_val]; split_ifs <;> omega))
        (Fin.ext (by simp only [gapSwap_val]; split_ifs <;> omega)) this
    all_goals first
      | (simp; done)
      | ext v
        simp only [hY, hZ, mem_belowSet, l1, l2, l3, l1', Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, eq_wire_iff]
        simp only [Fin.le_def, Fin.ext_iff, Fin.val_castSucc, gapSwap_val]
        (try split_ifs) <;> omega
  · -- the letters are `e + 1, e, e + 1`
    obtain ⟨e, hh, hg⟩ : ∃ e, (D.levelAt (p + 1) : ℕ) = e ∧ (D.levelAt p : ℕ) = e + 1 :=
      ⟨_, rfl, hdown.symm⟩
    refine ⟨Finset.univ.filter (fun v => (D.levelOf p v : ℕ) < e), D.wire p ⟨e, by omega⟩,
      D.wire p ⟨e + 1, by omega⟩, D.wire p ⟨e + 2, by omega⟩, ?_, ?_, ?_, ?_, ?_,
      fun hc => absurd hc (by omega), fun _ => ⟨?_, ?_⟩,
      ex p (by omega) (D.levelAt (p + 1)) _ ?_, ex (p + 2) (by omega) (D.levelAt (p + 1)) _ ?_,
      ex p (by omega) (D.levelAt p) _ ?_, ex (p + 3) (by omega) (D.levelAt p) _ ?_⟩
    · have := ord (p + 2) (by omega) ⟨e + 1, by omega⟩ ⟨e + 2, by omega⟩
        (by rw [hgg]; dsimp only; omega) (by rw [hgg]; dsimp only; omega)
      rw [w2, w2] at this
      exact cg (Fin.ext (by simp only [gapSwap_val]; split_ifs <;> omega))
        (Fin.ext (by simp only [gapSwap_val]; split_ifs <;> omega)) this
    · exact ord p (by omega) _ _ (by dsimp only; omega) (by dsimp only; omega)
    all_goals first
      | (simp; done)
      | ext v
        simp only [hY, hZ, mem_belowSet, l1, l2, l3, l1', Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, eq_wire_iff]
        simp only [Fin.le_def, Fin.ext_iff, Fin.val_castSucc, gapSwap_val]
        (try split_ifs) <;> omega

/-- **The exchange sets of a braid move.** There are `S` and `α < β < γ` outside it such that the
chamber sets of the site `Y` and the replacement `Z` are `S ∪ {β}` and `S ∪ {α, γ}`, in one order
or the other, and `S ∪ {α}`, `S ∪ {γ}`, `S ∪ {α, β}`, `S ∪ {β, γ}` are chamber sets of `D`. -/
@[cluster_algebras "lem_braid_exchange_sets"]
theorem IsBraidMove.exists_exchange_sets {D D' : WiringDiagram n} {p : ℕ}
    (h : IsBraidMove D D' p) :
    ∃ (S : Finset (Fin (n + 2))) (α β γ : Fin (n + 2)), α < β ∧ β < γ ∧ α ∉ S ∧ β ∉ S ∧ γ ∉ S ∧
      (((D.braidSite h.1).chamberSet = S ∪ {β} ∧
          (D'.braidSite h.length_le).chamberSet = S ∪ {α, γ}) ∨
        ((D.braidSite h.1).chamberSet = S ∪ {α, γ} ∧
          (D'.braidSite h.length_le).chamberSet = S ∪ {β})) ∧
      (∃ c : D.Chamber, c.chamberSet = S ∪ {α}) ∧ (∃ c : D.Chamber, c.chamberSet = S ∪ {γ}) ∧
      (∃ c : D.Chamber, c.chamberSet = S ∪ {α, β}) ∧
      (∃ c : D.Chamber, c.chamberSet = S ∪ {β, γ}) := by
  obtain ⟨S, α, β, γ, hαβ, hβγ, hα, hβ, hγ, hup, hdown, h1, h2, h3, h4⟩ :=
    h.exists_exchange_sets_of_direction
  refine ⟨S, α, β, γ, hαβ, hβγ, hα, hβ, hγ, ?_, h1, h2, h3, h4⟩
  rcases h.2.2.1 with h' | h'
  exacts [Or.inl (hup h'), Or.inr (hdown h')]

/-- **The exchange sets of the constructed braid move** `(g, g + 1, g) ↦ (g + 1, g, g + 1)`: the
site carries `S ∪ {β}` and the replacement `S ∪ {α, γ}`. -/
theorem exists_exchange_sets_braidMove (D : WiringDiagram n) {p : ℕ}
    (hp : p + 3 ≤ D.word.length) (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    ∃ (S : Finset (Fin (n + 2))) (α β γ : Fin (n + 2)), α < β ∧ β < γ ∧ α ∉ S ∧ β ∉ S ∧ γ ∉ S ∧
      (D.braidSite hp).chamberSet = S ∪ {β} ∧
      (D.braidReplacement hp hgh hgg).chamberSet = S ∪ {α, γ} ∧
      (∃ c : D.Chamber, c.chamberSet = S ∪ {α}) ∧ (∃ c : D.Chamber, c.chamberSet = S ∪ {γ}) ∧
      (∃ c : D.Chamber, c.chamberSet = S ∪ {α, β}) ∧
      (∃ c : D.Chamber, c.chamberSet = S ∪ {β, γ}) := by
  obtain ⟨S, α, β, γ, hαβ, hβγ, hα, hβ, hγ, hup, -, h1, h2, h3, h4⟩ :=
    (D.isBraidMove_braidMove hp hgh hgg).exists_exchange_sets_of_direction
  obtain ⟨hY, hZ⟩ := hup hgh
  exact ⟨S, α, β, γ, hαβ, hβγ, hα, hβ, hγ, hY, hZ, h1, h2, h3, h4⟩

end WiringDiagram

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.WiringDiagram.Chamber

/-!
# The special wiring diagram

For `k ≥ 2` strands, the special wiring diagram `D₀ = D₀^{(k)}` of [FWZ] is the word obtained by
concatenating, for `j = 1, 2, …, k - 1` in turn, the blocks `(j, j - 1, …, 1)`. Its product is
the longest permutation `w₀`, so it is a wiring diagram, and its chambers are as simple as can
be: the gap `g` is crossed once in each of the blocks `j ≥ g`, at the position
`π_g(j) = binom(j, 2) + j - g + 1`, so `m_g(D₀) = k - g`, and the chamber `(g, i)` has chamber
set the solid interval `[i + 1, i + g]`. Consequently the chamber sets of `D₀` are the solid
intervals `[a, d]` with `d - a ≤ k - 2`, each exactly once, and the chamber with chamber set
`[a, d]` is bounded exactly when `a ≥ 2` and `d ≤ k - 1`.

## Main definitions

* `ClusterAlgebras.specialWord n`: the word `D₀` on `k = n + 2` strands.
* `ClusterAlgebras.specialPos g b`: the position of the crossing of gap `g` in block `b`, the
  0-based form of `π_g(j)`.
* `ClusterAlgebras.specialWiringDiagram n`: `D₀` as a `WiringDiagram n`.
* `ClusterAlgebras.specialChamber a d`: the chamber of `D₀` whose chamber set is the interval
  `[a, d]`.

## Main results

* `ClusterAlgebras.prod_specialWord`: the product of `D₀` is `w₀`.
* `ClusterAlgebras.multiplicity_specialWiringDiagram`: `m_g(D₀) = k - g`.
* `ClusterAlgebras.levelAt_specialWiringDiagram_eq_iff`: the crossings of gap `g` are exactly at
  the positions `π_g(j)`.
* `ClusterAlgebras.chamberSet_specialWiringDiagram`: the chamber `(g, i)` has chamber set
  `[i + 1, i + g]`.
* `ClusterAlgebras.eq_specialChamber_iff`, `ClusterAlgebras.bounded_specialWiringDiagram_iff`:
  chambers of `D₀` are named by their chamber sets, and which of them are bounded.

## Implementation notes

`WiringDiagram n` has `k = n + 2` strands and is 0-based throughout, so the 1-based indices of
[FWZ] are shifted as follows.

* Strands (wires and levels) are `Fin (n + 2)`: the strand `ℓ ∈ [1, k]` is `ℓ - 1`.
* Gaps, which are the letters of the word, are `Fin (n + 1)`: the letter `g ∈ [1, k-1]` is
  `g - 1`.
* Blocks are indexed by `b ∈ [0, n]`: the block `j ∈ [1, k - 1]`, which is `(j, j - 1, …, 1)`,
  is the block `b = j - 1`, which reads `(b, b - 1, …, 0)`.
* Positions in the word are 0-based indices into the list: the position `p` is `p - 1`. Block
  `b` occupies the indices `binom(b + 1, 2), …, binom(b + 1, 2) + b`.
* So `π_g(j)` is `specialPos (g - 1) (j - 1) + 1`, where
  `specialPos g b = binom(b + 1, 2) + (b - g)` is the index of the letter `g` in block `b`.
* A chamber `(g, i)` with `g ∈ [1, k - 1]` and `i ∈ [0, k - g]` is the `Chamber` with
  `gap = g - 1` and `idx = i`. Its chamber set `[i + 1, i + g]` becomes the 0-based interval
  `[idx, idx + gap]` of `Fin (n + 2)`, and `m_g(D₀) = k - g` becomes
  `multiplicity gap = n + 1 - gap`.

The figure of `D₀` in [FWZ] has several crossings at the same abscissa; any reading order of
those gives the same chambers up to commutations, and the order fixed here is the one in which
each block is read from its top letter down.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6.
-/

@[expose] public section

namespace ClusterAlgebras

variable {n : ℕ}

open WiringDiagram

/-! ### The word -/

/-- The block `(b, b - 1, …, 0)` of gaps of `Fin (n + 1)`, the 0-based form of the block
`(j, j - 1, …, 1)` of [FWZ] with `j = b + 1`. Only `b ≤ n` is used; past that the block is
truncated at the top gap `n`. -/
def specialBlock (n b : ℕ) : List (Fin (n + 1)) :=
  ((List.finRange (n + 1)).take (b + 1)).reverse

/-- The **special wiring diagram** `D₀` on `n + 2` strands, as a word: the concatenation of the
blocks `(b, b - 1, …, 0)` for `b = 0, 1, …, n`. In 1-based letters this is the concatenation
of `(j, j - 1, …, 1)` for `j = 1, …, k - 1`, where `k = n + 2`. -/
@[cluster_algebras "def_special_wiring_diagram"]
def specialWord (n : ℕ) : List (Fin (n + 1)) :=
  (List.range (n + 1)).flatMap (specialBlock n)

/-- The 0-based index in `specialWord n` of the letter `g` of the block `b`, for `g ≤ b`:
block `b` starts at index `binom(b + 1, 2)` and reads `b, b - 1, …`, so its letter `g` comes
`b - g` places in. The 1-based position `π_g(j) = binom(j, 2) + j - g + 1` of [FWZ], with
1-based `g` and `j`, is `specialPos (g - 1) (j - 1) + 1`. -/
@[cluster_algebras "def_special_wiring_diagram"]
def specialPos (g b : ℕ) : ℕ := (b + 1).choose 2 + (b - g)

private theorem choose_two_succ (m : ℕ) : (m + 1).choose 2 = m.choose 2 + m := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

/-- For `b ≤ n`, the block `b` has `b + 1` letters, one per gap at or below `b`. -/
theorem length_specialBlock {b : ℕ} (hb : b ≤ n) : (specialBlock n b).length = b + 1 := by
  simp [specialBlock]
  omega

/-- The block `b` reads `b, b - 1, …, 0`. -/
theorem getElem?_specialBlock {b s : ℕ} (hb : b ≤ n) (hs : s ≤ b) :
    (specialBlock n b)[s]? = some ⟨b - s, by omega⟩ := by
  have hlen : s < (specialBlock n b).length := by
    rw [length_specialBlock hb]
    omega
  rw [List.getElem?_eq_getElem hlen]
  simp [specialBlock, List.getElem_reverse]
  omega

private theorem flatMap_range_succ {α : Type*} (f : ℕ → List α) (m : ℕ) :
    (List.range (m + 1)).flatMap f = (List.range m).flatMap f ++ f m := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `m` blocks have `binom(m + 1, 2)` letters in all. -/
theorem length_flatMap_specialBlock {m : ℕ} (hm : m ≤ n + 1) :
    ((List.range m).flatMap (specialBlock n)).length = (m + 1).choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [flatMap_range_succ, List.length_append, ih (by omega), length_specialBlock (by omega),
      choose_two_succ (m + 1)]

/-- `D₀` has `binom(n + 2, 2)` letters, one per pair of strands. -/
theorem length_specialWord : (specialWord n).length = (n + 2).choose 2 :=
  length_flatMap_specialBlock le_rfl

/-- **The letters of `D₀`**: the letter `s` places into the block `b` is the gap `b - s`. -/
theorem getElem?_specialWord {b s : ℕ} (hb : b ≤ n) (hs : s ≤ b) :
    (specialWord n)[(b + 1).choose 2 + s]? = some ⟨b - s, by omega⟩ := by
  have hsplit : List.range (n + 1) =
      List.range (b + 1) ++ (List.range (n - b)).map (b + 1 + ·) := by
    rw [← List.range_add]
    congr 1
    omega
  rw [specialWord, hsplit, List.flatMap_append, List.getElem?_append_left, flatMap_range_succ,
    List.getElem?_append_right, length_flatMap_specialBlock (by omega), Nat.add_sub_cancel_left,
    getElem?_specialBlock hb hs]
  · rw [length_flatMap_specialBlock (by omega)]
    omega
  · rw [length_flatMap_specialBlock (by omega), choose_two_succ (b + 1)]
    omega

/-- The index `s ≤ b + 1` places into the block `b`, possibly just past it, is at most the
length of `D₀`. -/
theorem le_length_specialWord {b s : ℕ} (hb : b ≤ n) (hs : s ≤ b + 1) :
    (b + 1).choose 2 + s ≤ (specialWord n).length := by
  rw [length_specialWord]
  have h1 := choose_two_succ (b + 1)
  have h2 : (b + 1 + 1).choose 2 ≤ (n + 2).choose 2 := Nat.choose_le_choose 2 (by omega)
  omega

/-- The index `s` places into the block `b` is an index of `D₀`. -/
theorem lt_length_specialWord {b s : ℕ} (hb : b ≤ n) (hs : s ≤ b) :
    (b + 1).choose 2 + s < (specialWord n).length :=
  le_length_specialWord hb (s := s + 1) (by omega)

/-- The letter `s` places into the block `b`, as an element. -/
theorem getElem_specialWord {b s : ℕ} (hb : b ≤ n) (hs : s ≤ b)
    (ht : (b + 1).choose 2 + s < (specialWord n).length) :
    (specialWord n)[(b + 1).choose 2 + s] = ⟨b - s, by omega⟩ :=
  Option.some.inj ((List.getElem?_eq_getElem ht).symm.trans (getElem?_specialWord hb hs))

/-- **Every index of `D₀` lies in some block**: an index below `binom(m + 1, 2)` is `s` places
into a block `b < m`, with `s ≤ b`. -/
theorem exists_eq_choose_two_add {m t : ℕ} (ht : t < (m + 1).choose 2) :
    ∃ b < m, ∃ s ≤ b, t = (b + 1).choose 2 + s := by
  induction m with
  | zero => simp at ht
  | succ m ih =>
    rw [choose_two_succ (m + 1)] at ht
    by_cases h : t < (m + 1).choose 2
    · obtain ⟨b, hb, s, hs, rfl⟩ := ih h
      exact ⟨b, by omega, s, hs, rfl⟩
    · exact ⟨m, by omega, t - (m + 1).choose 2, by omega, by omega⟩

/-! ### The wires

After the first `b` blocks the wires `0, …, b` sit in reverse order, which is the permutation
`w^{(b+1)}` of [FWZ]; the letters `b, b - 1, …` of the next block then carry the wire at level
`b + 1` down through the levels below it. The level of each wire at every position is given in
closed form by `specialLevel`, which is all that the multiplicities and chamber sets need. -/

/-- The level, as a natural number, of the wire `v` after the first `b` blocks of `D₀` and the
first `s ≤ b + 1` letters of the block `b`. After `b` blocks the wires `0, …, b` sit in reverse
order (wire `v ≤ b` at level `b - v`); the letters `b, …, b - s + 1` then carry the wire `b + 1`
down to the level `b + 1 - s` and move each of the wires `0, …, s - 1` up by one level. -/
def specialLevel (b s v : ℕ) : ℕ :=
  if v < s then b + 1 - v else if v ≤ b then b - v else if v = b + 1 then b + 1 - s else v

/-- Induction over the positions of `D₀`, block by block and letter by letter. -/
private theorem special_induction {P : ℕ → ℕ → Prop} (h0 : P 0 0)
    (hstep : ∀ b s, b ≤ n → s ≤ b → P b s → P b (s + 1))
    (hnext : ∀ b, b < n → P b (b + 1) → P (b + 1) 0) :
    ∀ b ≤ n, ∀ s ≤ b + 1, P b s := by
  intro b hb
  induction b with
  | zero =>
    intro s hs
    interval_cases s
    · exact h0
    · exact hstep 0 0 hb le_rfl h0
  | succ b ih =>
    have hb0 : P (b + 1) 0 := hnext b (by omega) (ih (by omega) (b + 1) le_rfl)
    intro s hs
    induction s with
    | zero => exact hb0
    | succ s ihs => exact hstep (b + 1) s hb (by omega) (ihs (by omega))

/-- **The wire levels along `D₀`**: after the first `b` blocks and `s` further letters, the
inverse of the partial product sends the wire `v` to the level `specialLevel b s v`. -/
theorem prod_take_specialWord_symm {b s : ℕ} (hb : b ≤ n) (hs : s ≤ b + 1) (v : Fin (n + 2)) :
    ((((specialWord n).map gapSwap).take ((b + 1).choose 2 + s)).prod.symm v : ℕ) =
      specialLevel b s v := by
  revert v
  refine special_induction (n := n) (P := fun b s => ∀ v : Fin (n + 2),
    ((((specialWord n).map gapSwap).take ((b + 1).choose 2 + s)).prod.symm v : ℕ) =
      specialLevel b s v) ?_ ?_ ?_ b hb s hs
  · intro v
    simp only [zero_add, Nat.choose_succ_self, List.take_zero, List.prod_nil]
    change (v : ℕ) = _
    simp only [specialLevel]
    split_ifs <;> omega
  · intro b s hb hs ih v
    have ht := lt_length_specialWord hb hs
    have ht' : (b + 1).choose 2 + s < ((specialWord n).map gapSwap).length := by simpa using ht
    rw [← add_assoc, List.prod_take_succ _ _ ht', List.getElem_map, getElem_specialWord hb hs ht]
    change (((gapSwap _).trans _).symm v : ℕ) = _
    rw [Equiv.symm_trans_apply, gapSwap, Equiv.symm_swap, ← gapSwap, gapSwap_val, ih v]
    simp only [specialLevel]
    split_ifs <;> omega
  · intro b hb ih v
    rw [add_zero, choose_two_succ (b + 1), ih v]
    simp only [specialLevel]
    split_ifs <;> omega

/-- **`D₀` spells `w₀`**: after all `n + 1` blocks every wire `v` sits at level `n + 1 - v`. -/
@[cluster_algebras "lem_special_wiring_is_wiring"]
theorem prod_specialWord : ((specialWord n).map gapSwap).prod = Fin.revPerm := by
  have htake : ((specialWord n).map gapSwap).take ((n + 1).choose 2 + (n + 1)) =
      (specialWord n).map gapSwap :=
    List.take_of_length_le (by rw [List.length_map, length_specialWord, choose_two_succ (n + 1)])
  have hs : ((specialWord n).map gapSwap).prod.symm = Fin.revPerm := by
    ext v
    rw [Fin.revPerm_apply, Fin.val_rev, ← htake, prod_take_specialWord_symm le_rfl le_rfl,
      specialLevel]
    split_ifs <;> omega
  rw [← Equiv.symm_symm ((specialWord n).map gapSwap).prod, hs, Fin.revPerm_symm]

/-- The **special wiring diagram** `D₀` on `k = n + 2` strands: the word `specialWord n` has one
letter per pair of strands and spells `w₀`, so it is a wiring diagram. -/
@[cluster_algebras "def_special_wiring_diagram", cluster_algebras "lem_special_wiring_is_wiring"]
def specialWiringDiagram (n : ℕ) : WiringDiagram n where
  word := specialWord n
  length_eq := length_specialWord
  prod_eq := prod_specialWord

/-! ### Crossings, levels and chamber sets of `D₀` -/

/-- The word of `D₀` is `specialWord n`. -/
@[simp]
theorem word_specialWiringDiagram : (specialWiringDiagram n).word = specialWord n := rfl

/-- The crossing `s` places into the block `b` of `D₀` is at the gap `b - s`. -/
theorem levelAt_specialWiringDiagram {b s : ℕ} (hb : b ≤ n) (hs : s ≤ b) :
    (specialWiringDiagram n).levelAt ((b + 1).choose 2 + s) = ⟨b - s, by omega⟩ := by
  rw [WiringDiagram.levelAt_eq_getElem?, word_specialWiringDiagram, getElem?_specialWord hb hs,
    Option.getD_some]

/-- The levels of the wires of `D₀` after the first `b` blocks and `s` further letters. -/
theorem levelOf_specialWiringDiagram {b s : ℕ} (hb : b ≤ n) (hs : s ≤ b + 1) (v : Fin (n + 2)) :
    ((specialWiringDiagram n).levelOf ((b + 1).choose 2 + s) v : ℕ) = specialLevel b s v :=
  prod_take_specialWord_symm hb hs v

/-- The number of crossings of the gap `g` among the first `b` blocks of `D₀` and `s` further
letters: one in each earlier block from `g` on, and one more if the letters `b, …, b - s + 1`
include `g`. -/
theorem countUpTo_specialWiringDiagram (g : Fin (n + 1)) {b s : ℕ} (hb : b ≤ n)
    (hs : s ≤ b + 1) :
    (specialWiringDiagram n).countUpTo g ((b + 1).choose 2 + s) =
      (b - g) + if (g : ℕ) ≤ b ∧ b < g + s then 1 else 0 := by
  refine special_induction (n := n) (P := fun b s =>
    (specialWiringDiagram n).countUpTo g ((b + 1).choose 2 + s) =
      (b - g) + if (g : ℕ) ≤ b ∧ b < g + s then 1 else 0) ?_ ?_ ?_ b hb s hs
  · simp only [zero_add, Nat.choose_succ_self, WiringDiagram.countUpTo_zero]
    split_ifs <;> omega
  · intro b s hb hs ih
    have ht := lt_length_specialWord hb hs
    rw [← add_assoc, WiringDiagram.countUpTo_succ _ ht, ih, levelAt_specialWiringDiagram hb hs]
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  · intro b hb ih
    rw [add_zero, choose_two_succ (b + 1), ih]
    split_ifs <;> omega

/-- **`m_g(D₀) = k - g`**: in the 0-based gaps, the gap `g` is crossed `n + 1 - g` times, once
in each block `b ≥ g`. -/
@[cluster_algebras "lem_special_wiring_chambers"]
theorem multiplicity_specialWiringDiagram (g : Fin (n + 1)) :
    (specialWiringDiagram n).multiplicity g = n + 1 - g := by
  rw [← WiringDiagram.countUpTo_length, word_specialWiringDiagram, length_specialWord,
    choose_two_succ (n + 1), countUpTo_specialWiringDiagram g le_rfl le_rfl]
  have := g.isLt
  split_ifs <;> omega

/-- The crossing at index `specialPos g b` of `D₀` is at the gap `g`. -/
theorem levelAt_specialPos {g : Fin (n + 1)} {b : ℕ} (hgb : (g : ℕ) ≤ b) (hb : b ≤ n) :
    (specialWiringDiagram n).levelAt (specialPos g b) = g := by
  rw [specialPos, levelAt_specialWiringDiagram hb (by omega)]
  ext
  simp only
  omega

/-- The index `specialPos g b` is an index of `D₀`. -/
theorem specialPos_lt_length {g b : ℕ} (hb : b ≤ n) :
    specialPos g b < (specialWiringDiagram n).word.length :=
  lt_length_specialWord hb (by omega)

/-- The positions `π_g(j)` increase with `j`. -/
theorem specialPos_lt_specialPos {g b b' : ℕ} (hbb' : b < b') :
    specialPos g b < specialPos g b' := by
  have h1 := choose_two_succ (b + 1)
  have h2 : (b + 1 + 1).choose 2 ≤ (b' + 1).choose 2 := Nat.choose_le_choose 2 (by omega)
  rw [specialPos, specialPos]
  omega

/-- **The crossings of gap `g` in `D₀` are at the positions `π_g(j)`, `j ∈ [g, k - 1]`**: in
0-based terms, an index `t` of `D₀` carries a crossing of the gap `g` exactly when
`t = specialPos g b` for a block `b ∈ [g, n]`. -/
@[cluster_algebras "lem_special_wiring_chambers"]
theorem levelAt_specialWiringDiagram_eq_iff (g : Fin (n + 1)) (t : ℕ) :
    (t < (specialWiringDiagram n).word.length ∧ (specialWiringDiagram n).levelAt t = g) ↔
      ∃ b, (g : ℕ) ≤ b ∧ b ≤ n ∧ t = specialPos g b := by
  constructor
  · rintro ⟨ht, hg⟩
    rw [word_specialWiringDiagram, length_specialWord] at ht
    obtain ⟨b, hb, s, hs, rfl⟩ := exists_eq_choose_two_add ht
    rw [levelAt_specialWiringDiagram (by omega) hs, Fin.ext_iff] at hg
    simp only at hg
    exact ⟨b, by omega, by omega, by rw [specialPos]; omega⟩
  · rintro ⟨b, hgb, hb, rfl⟩
    exact ⟨specialPos_lt_length hb, levelAt_specialPos hgb hb⟩

/-- The wires below the gap `g` after the first `b` blocks of `D₀` and `s` further letters. -/
theorem mem_belowSet_specialWiringDiagram {g : Fin (n + 1)} {b s : ℕ} (hb : b ≤ n)
    (hs : s ≤ b + 1) (v : Fin (n + 2)) :
    v ∈ (specialWiringDiagram n).belowSet ((b + 1).choose 2 + s) g ↔
      specialLevel b s v ≤ g := by
  rw [WiringDiagram.mem_belowSet, Fin.le_def, levelOf_specialWiringDiagram hb hs,
    Fin.val_castSucc]

/-- **The chamber `(g, i)` of `D₀` has chamber set `[i + 1, i + g]`.** In the 0-based
conventions a chamber `c` of `D₀` has gap `c.gap = g - 1` and index `c.idx = i`, and its chamber
set is the interval `[c.idx, c.idx + c.gap]` of strands. Every index `0 ≤ i ≤ k - g` occurs,
since `c.idx` ranges up to `multiplicity c.gap = k - g`. -/
@[cluster_algebras "lem_special_wiring_chambers"]
theorem chamberSet_specialWiringDiagram (c : (specialWiringDiagram n).Chamber) :
    c.chamberSet = ({v | c.idx ≤ (v : ℕ) ∧ (v : ℕ) ≤ c.idx + c.gap} : Finset (Fin (n + 2))) := by
  have hidx := c.idx_le
  rw [multiplicity_specialWiringDiagram] at hidx
  have hg := c.gap.isLt
  rcases Nat.eq_zero_or_pos c.idx with h0 | hpos
  · rw [c.chamberSet_eq_belowSet (t := 0) (Nat.zero_le _) (by rw [Chamber.InSpan,
      WiringDiagram.countUpTo_zero, h0])]
    ext v
    rw [show (0 : ℕ) = (0 + 1).choose 2 + 0 from rfl,
      mem_belowSet_specialWiringDiagram (Nat.zero_le _) (Nat.zero_le _), Finset.mem_filter,
      specialLevel, h0]
    simp only [Finset.mem_univ, true_and]
    split_ifs <;> omega
  · set b := (c.gap : ℕ) + c.idx - 1 with hbdef
    have hb : b ≤ n := by omega
    have hs : c.idx ≤ b + 1 := by omega
    have hspan : c.InSpan ((b + 1).choose 2 + c.idx) := by
      rw [Chamber.InSpan, countUpTo_specialWiringDiagram _ hb hs]
      split_ifs <;> omega
    rw [c.chamberSet_eq_belowSet (le_length_specialWord hb hs) hspan]
    ext v
    rw [mem_belowSet_specialWiringDiagram hb hs, Finset.mem_filter, specialLevel]
    simp only [Finset.mem_univ, true_and]
    split_ifs <;> omega

/-- Membership in a chamber set of `D₀`: the chamber `c` has chamber set
`[c.idx, c.idx + c.gap]`. -/
theorem mem_chamberSet_specialWiringDiagram (c : (specialWiringDiagram n).Chamber)
    (v : Fin (n + 2)) :
    v ∈ c.chamberSet ↔ c.idx ≤ (v : ℕ) ∧ (v : ℕ) ≤ c.idx + c.gap := by
  rw [chamberSet_specialWiringDiagram]
  simp

/-! ### The ends of the chambers of `D₀` -/

/-- **The chamber `(g, i)` of `D₀` with `i ≥ 1` starts just after the crossing `π_g(g + i - 1)`.**
In 0-based terms its left position is `specialPos c.gap (c.gap + c.idx - 1) + 1`. -/
theorem left_specialWiringDiagram (c : (specialWiringDiagram n).Chamber) (h : 1 ≤ c.idx) :
    c.left = specialPos c.gap (c.gap + c.idx - 1) + 1 := by
  have hidx := c.idx_le
  rw [multiplicity_specialWiringDiagram] at hidx
  have hb : (c.gap : ℕ) + c.idx - 1 ≤ n := by omega
  have hlev := levelAt_specialPos (g := c.gap) (b := c.gap + c.idx - 1) (by omega) hb
  have hlt := specialPos_lt_length (n := n) (g := c.gap) hb
  have hc : c = (specialWiringDiagram n).chamberAt c.gap (specialPos c.gap (c.gap + c.idx - 1) + 1)
      hlt := by
    refine Chamber.ext' rfl ?_
    rw [WiringDiagram.idx_chamberAt, specialPos, add_assoc,
      countUpTo_specialWiringDiagram _ hb (by omega)]
    split_ifs <;> omega
  have := (specialWiringDiagram n).left_chamberAt_succ hlt hlev
  rwa [← hc] at this

/-- **The chamber `(g, i)` of `D₀` with `i < k - g` ends just after the crossing `π_g(g + i)`.**
In 0-based terms its right position is `specialPos c.gap (c.gap + c.idx) + 1`. -/
theorem right_specialWiringDiagram (c : (specialWiringDiagram n).Chamber)
    (h : c.idx < n + 1 - c.gap) :
    c.right = specialPos c.gap (c.gap + c.idx) + 1 := by
  have hb : (c.gap : ℕ) + c.idx ≤ n := by omega
  have hlev := levelAt_specialPos (g := c.gap) (b := c.gap + c.idx) (by omega) hb
  have hlt := specialPos_lt_length (n := n) (g := c.gap) hb
  have hc : c = (specialWiringDiagram n).chamberAt c.gap (specialPos c.gap (c.gap + c.idx))
      hlt.le := by
    refine Chamber.ext' rfl ?_
    rw [WiringDiagram.idx_chamberAt, specialPos, countUpTo_specialWiringDiagram _ hb (by omega)]
    split_ifs <;> omega
  have := (specialWiringDiagram n).right_chamberAt hlt hlev hlt.le
  rwa [← hc] at this

/-- **The bounded chambers of `D₀`** are those whose chamber set `[a, d]` has `a ≥ 2` and
`d ≤ k - 1` (in 1-based strands); in 0-based terms, `1 ≤ c.idx` and
`c.idx + c.gap ≤ n`. -/
theorem bounded_specialWiringDiagram_iff (c : (specialWiringDiagram n).Chamber) :
    c.Bounded ↔ 1 ≤ c.idx ∧ c.idx + c.gap ≤ n := by
  have hidx := c.idx_le
  rw [multiplicity_specialWiringDiagram] at hidx
  rw [← not_not (a := c.Bounded), Chamber.not_bounded_iff, multiplicity_specialWiringDiagram]
  omega

/-! ### Naming the chambers of `D₀` by their chamber sets -/

/-- The chamber of `D₀` whose chamber set is the interval `[a, d]` of 0-based strands, for
`a ≤ d ≤ n + 1` and `d - a ≤ n` (the interval is not all of the strands). It lies in the gap
`d - a` and has index `a`. -/
def specialChamber (a d : ℕ) (had : a ≤ d) (hd : d ≤ n + 1) (hda : d ≤ a + n) :
    (specialWiringDiagram n).Chamber where
  gap := ⟨d - a, by omega⟩
  idx := a
  idx_le := by
    rw [multiplicity_specialWiringDiagram]
    simp only
    omega

/-- The chamber with chamber set `[a, d]` lies in the gap `d - a`. -/
@[simp]
theorem gap_specialChamber {a d : ℕ} (had : a ≤ d) (hd : d ≤ n + 1) (hda : d ≤ a + n) :
    ((specialChamber a d had hd hda).gap : ℕ) = d - a := rfl

/-- The chamber with chamber set `[a, d]` has index `a`. -/
@[simp]
theorem idx_specialChamber {a d : ℕ} (had : a ≤ d) (hd : d ≤ n + 1) (hda : d ≤ a + n) :
    (specialChamber a d had hd hda).idx = a := rfl

/-- The chamber `specialChamber a d` has chamber set `[a, d]`. -/
theorem mem_chamberSet_specialChamber {a d : ℕ} (had : a ≤ d) (hd : d ≤ n + 1)
    (hda : d ≤ a + n) (v : Fin (n + 2)) :
    v ∈ (specialChamber a d had hd hda).chamberSet ↔ a ≤ (v : ℕ) ∧ (v : ℕ) ≤ d := by
  rw [mem_chamberSet_specialWiringDiagram, idx_specialChamber, gap_specialChamber]
  omega

/-- **A chamber of `D₀` is named by its chamber set**: it is `specialChamber a d` exactly when its
chamber set is `[a, d]`. -/
theorem eq_specialChamber_iff (c : (specialWiringDiagram n).Chamber) {a d : ℕ} (had : a ≤ d)
    (hd : d ≤ n + 1) (hda : d ≤ a + n) :
    c = specialChamber a d had hd hda ↔
      ∀ v : Fin (n + 2), v ∈ c.chamberSet ↔ a ≤ (v : ℕ) ∧ (v : ℕ) ≤ d := by
  refine ⟨by rintro rfl; exact mem_chamberSet_specialChamber had hd hda, fun h => ?_⟩
  have hidx := c.idx_le
  rw [multiplicity_specialWiringDiagram] at hidx
  have hg := c.gap.isLt
  simp only [mem_chamberSet_specialWiringDiagram] at h
  have h1 := h ⟨a, by omega⟩
  have h2 := h ⟨c.idx, by omega⟩
  have h3 := h ⟨d, by omega⟩
  have h4 := h ⟨c.idx + c.gap, by omega⟩
  simp only at h1 h2 h3 h4
  exact Chamber.ext' (Fin.ext (by rw [gap_specialChamber]; omega))
    (by rw [idx_specialChamber]; omega)

/-- Every chamber of `D₀` is `specialChamber` of the ends of its chamber set. -/
theorem eq_specialChamber (c : (specialWiringDiagram n).Chamber) :
    c = specialChamber c.idx (c.idx + c.gap) (by omega)
      (by have := c.idx_le; rw [multiplicity_specialWiringDiagram] at this; omega)
      (by have := c.gap.isLt; omega) :=
  Chamber.ext' (Fin.ext (by simp)) rfl

end ClusterAlgebras

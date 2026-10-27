/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.DoubleWiring.Move
public import ClusterAlgebras.TotalPositivity.ReducedWords

/-!
# Double wiring diagrams as reduced words: swaps and braids

A double wiring diagram on `n + 2` strands is a word of coloured crossings whose thick and thin
subwords are both reduced words for the longest permutation `w₀` of `Fin (n + 2)`. Reading a thick
crossing of level `i` as the letter `i` and a thin one as the letter `i + (n + 2)` turns it into a
word in the adjacent transpositions of `Fin (2 * (n + 2))`, the *interleaved word*, whose product
acts as `w₀` on each half. That word is reduced, and conversely every reduced word for this
product omits the letter `n + 1` and comes from a double wiring diagram. The theorem of
Matsumoto and Tits for `S_{2(n+2)}` therefore connects any two double wiring diagrams by
*swaps* (exchanges of two adjacent crossings) and *braids* inside one colour, and sorting these
steps gives the local moves of [FWZ], Chapter 1.

## Main definitions

* `DoubleWiringDiagram.IsSwap`, `DoubleWiringDiagram.IsBraid`: the swap and the braid at a
  position.
* `interleavedWord`: the interleaved word of a sequence of coloured crossings, and
  `interleavedLetter`, its letter for a single crossing.

## Main results

* `interleavedWord_prod_apply`: the product of an interleaved word acts as the product of the
  thick levels on the first `n + 2` points and as the shifted product of the thin levels on the
  last `n + 2` points.
* `prod_interleavedWord_eq_iff`: hence two interleaved words have the same product if and only if
  their thick subwords and their thin subwords do.
* `DoubleWiringDiagram.inversionNumber_prod_interleavedWord`,
  `DoubleWiringDiagram.isReducedWord_interleavedWord`: the interleaved word of a double wiring
  diagram is a reduced word.
* `DoubleWiringDiagram.reflTransGen_isSwap_or_isBraid`: any two double wiring diagrams are
  connected by swaps and braids.
* `DoubleWiringDiagram.reflTransGen_localMove`: any two double wiring diagrams are connected by
  swaps of crossings of different levels and local moves in either direction.

## Implementation notes

* Positions are `0`-based, and levels are `Fin (n + 1)`, so the `n` strands of [FWZ] are `n + 2`
  here and `[1, n - 1]` is `Fin (n + 1)`. The letters of the interleaved word live in
  `Fin (2 * n + 3)`, the gaps of `Fin (2 * n + 4)`, and the letter `n + 1` (the letter `n` of
  [FWZ]) is the gap between the two halves.
* [FWZ] proves `interleavedWord_prod_apply` through the direct-sum homomorphism
  `Equiv.Perm.sumCongrHom`; here it is proved pointwise by induction on the word, which is what
  the statement (a pointwise one) asks for.
* The permutation `π` of [FWZ] (`w₀` on each half) is never named: it is the product of the
  interleaved word of the given diagram `D`, and `prod_interleavedWord_eq` shows every double
  wiring diagram has the same product.
* A swap of two equal crossings (same level and colour) changes nothing; in
  `reflTransGen_localMove` such a step is dropped, which is the deletion of repeated diagrams in
  [FWZ].

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 1.
-/

@[expose] public section

namespace ClusterAlgebras

namespace DoubleWiringDiagram

variable {n : ℕ}

/-- `D'` is obtained from `D` by the **swap at `p`**: the crossings at the (0-based) positions
`p` and `p + 1` are exchanged, each keeping its level and colour, and all other crossings are
unchanged. The common prefix `l` has length `p`. -/
@[cluster_algebras "def_double_swap"]
def IsSwap (D D' : DoubleWiringDiagram n) (p : ℕ) : Prop :=
  ∃ (l r : List (Fin (n + 1) × Colour)) (a b : Fin (n + 1) × Colour),
    l.length = p ∧ D.word = l ++ [a, b] ++ r ∧ D'.word = l ++ [b, a] ++ r

/-- `D'` is obtained from `D` by the **braid at `p`**: the crossings at the (0-based) positions
`p`, `p + 1`, `p + 2` all have one colour `e` and levels `g, h, g` with `|g - h| = 1`, and `D'`
replaces them by crossings of colour `e` and levels `h, g, h`, all other crossings unchanged. -/
@[cluster_algebras "def_double_braid"]
def IsBraid (D D' : DoubleWiringDiagram n) (p : ℕ) : Prop :=
  ∃ (l r : List (Fin (n + 1) × Colour)) (e : Colour) (g h : Fin (n + 1)),
    ((g : ℕ) + 1 = h ∨ (h : ℕ) + 1 = g) ∧ l.length = p ∧
      D.word = l ++ [(g, e), (h, e), (g, e)] ++ r ∧ D'.word = l ++ [(h, e), (g, e), (h, e)] ++ r

end DoubleWiringDiagram

section Letter

variable {n : ℕ}

/-- The **letter of one coloured crossing** in the interleaved word: `i` for a thick crossing of
level `i`, and `i + (n + 2)` for a thin one. -/
def interleavedLetter (x : Fin (n + 1) × Colour) : Fin (2 * n + 3) :=
  match x.2 with
    | .thick => ⟨x.1, by omega⟩
    | .thin => ⟨x.1 + (n + 2), by omega⟩

/-- The **interleaved word** of a sequence of coloured crossings on `n + 2` strands: a word in the
adjacent transpositions of `Fin (2 * (n + 2))`, in which a thick crossing of (0-based) level `i`
is the letter `i` and a thin one is the letter `i + (n + 2)`. The letter `n + 1`, the gap between
the two halves, never occurs. -/
@[cluster_algebras "def_interleaved_word"]
def interleavedWord (E : List (Fin (n + 1) × Colour)) : List (Fin (2 * n + 3)) :=
  E.map interleavedLetter

/-- The interleaved word is the word of the letters of the crossings. -/
theorem interleavedWord_eq_map (E : List (Fin (n + 1) × Colour)) :
    interleavedWord E = E.map interleavedLetter := rfl

/-- The letter of a thick crossing is its level. -/
@[simp]
theorem val_interleavedLetter_thick (i : Fin (n + 1)) :
    ((interleavedLetter (i, .thick) : Fin (2 * n + 3)) : ℕ) = i := rfl

/-- The letter of a thin crossing is its level shifted by `n + 2`. -/
@[simp]
theorem val_interleavedLetter_thin (i : Fin (n + 1)) :
    ((interleavedLetter (i, .thin) : Fin (2 * n + 3)) : ℕ) = i + (n + 2) := rfl

/-- A crossing is determined by its letter. -/
theorem interleavedLetter_injective :
    Function.Injective (interleavedLetter : Fin (n + 1) × Colour → Fin (2 * n + 3)) := by
  rintro ⟨i, c⟩ ⟨j, d⟩ h
  rw [Fin.ext_iff] at h
  cases c <;> cases d <;> simp at h <;> first | omega | (simp [Fin.ext_iff]; omega)

/-- A sequence of coloured crossings is determined by its interleaved word. -/
theorem interleavedWord_injective :
    Function.Injective (interleavedWord : List (Fin (n + 1) × Colour) → List (Fin (2 * n + 3))) :=
  List.map_injective_iff.2 interleavedLetter_injective

/-- The interleaved word has one letter per crossing. -/
@[simp]
theorem length_interleavedWord (E : List (Fin (n + 1) × Colour)) :
    (interleavedWord E).length = E.length :=
  List.length_map _

end Letter

/-- **The product of an interleaved word** acts as the product `σ` of the thick levels on the
first `n + 2` points and as the product `τ` of the thin levels, shifted by `n + 2`, on the last
`n + 2` points. -/
@[cluster_algebras "lem_interleaved_word_product"]
theorem interleavedWord_prod_apply {n : ℕ} (E : List (Fin (n + 1) × Colour)) (ℓ : Fin (n + 2)) :
    ((interleavedWord E).map gapSwap).prod ⟨ℓ, by omega⟩ =
        ⟨(((subword E .thick).map gapSwap).prod ℓ : ℕ), by omega⟩ ∧
      ((interleavedWord E).map gapSwap).prod ⟨ℓ + (n + 2), by omega⟩ =
        ⟨(((subword E .thin).map gapSwap).prod ℓ : ℕ) + (n + 2), by omega⟩ := by
  induction E generalizing ℓ with
  | nil => simp [interleavedWord, subword]
  | cons a E ih =>
    obtain ⟨i, c⟩ := a
    obtain ⟨ih₁, ih₂⟩ := ih ℓ
    rw [interleavedWord_eq_map] at ih₁ ih₂ ⊢
    cases c <;>
    · simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih₁, ih₂, subword,
        List.filter_cons, reduceCtorEq, decide_true, decide_false, if_true, if_false,
        Bool.false_eq_true]
      refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;>
      · simp only [gapSwap_val, val_interleavedLetter_thick, val_interleavedLetter_thin] <;>
          split_ifs <;> omega

section Product

variable {n : ℕ}

/-- A permutation of `Fin (2 * (n + 2))` is determined by its values on the two halves. -/
theorem perm_ext_of_halves {f g : Equiv.Perm (Fin (2 * n + 3 + 1))}
    (h₁ : ∀ ℓ : Fin (n + 2), f ⟨ℓ, by omega⟩ = g ⟨ℓ, by omega⟩)
    (h₂ : ∀ ℓ : Fin (n + 2), f ⟨ℓ + (n + 2), by omega⟩ = g ⟨ℓ + (n + 2), by omega⟩) :
    f = g := by
  ext1 x
  by_cases hx : (x : ℕ) < n + 2
  · simpa using h₁ ⟨x, hx⟩
  · convert h₂ ⟨x - (n + 2), by omega⟩ using 2 <;> exact Fin.ext (by simp; omega)

/-- **Two interleaved words have the same product if and only if their subwords of each colour
do.** -/
theorem prod_interleavedWord_eq_iff {E F : List (Fin (n + 1) × Colour)} :
    ((interleavedWord E).map gapSwap).prod = ((interleavedWord F).map gapSwap).prod ↔
      ∀ e, ((subword E e).map gapSwap).prod = ((subword F e).map gapSwap).prod := by
  refine ⟨fun h e => ?_, fun h => perm_ext_of_halves (fun ℓ => ?_) (fun ℓ => ?_)⟩
  · ext ℓ
    have hE := interleavedWord_prod_apply E ℓ
    have hF := interleavedWord_prod_apply F ℓ
    rw [h] at hE
    cases e
    · simpa [hE.1] using hF.1
    · simpa [hE.2] using hF.2
  · simp [(interleavedWord_prod_apply E ℓ).1, (interleavedWord_prod_apply F ℓ).1, h]
  · simp [(interleavedWord_prod_apply E ℓ).2, (interleavedWord_prod_apply F ℓ).2, h]

/-- The lengths of the thick and thin subwords add up to the length of the sequence. -/
theorem length_subword_thick_add_length_subword_thin (E : List (Fin (n + 1) × Colour)) :
    (subword E .thick).length + (subword E .thin).length = E.length := by
  induction E with
  | nil => rfl
  | cons a E ih =>
    obtain ⟨i, c⟩ := a
    cases c <;> simp [subword] at ih ⊢ <;> omega

end Product

namespace DoubleWiringDiagram

open Finset

variable {n : ℕ}

/-- **All double wiring diagrams have the same interleaved product**, the permutation acting as
`w₀` on each half. -/
theorem prod_interleavedWord_eq (D E : DoubleWiringDiagram n) :
    ((interleavedWord D.word).map gapSwap).prod = ((interleavedWord E.word).map gapSwap).prod :=
  prod_interleavedWord_eq_iff.2 fun e => by rw [D.prod_subword, E.prod_subword]

/-- The interleaved product of a double wiring diagram has as many inversions as the diagram has
crossings. -/
theorem inversionNumber_prod_interleavedWord (D : DoubleWiringDiagram n) :
    inversionNumber ((interleavedWord D.word).map gapSwap).prod = D.word.length := by
  refine le_antisymm (by simpa using inversionNumber_prod_le (interleavedWord D.word)) ?_
  set π := ((interleavedWord D.word).map gapSwap).prod with hπ
  have h₁ : ∀ ℓ : Fin (n + 2), ((π ⟨ℓ, by omega⟩ : Fin _) : ℕ) = n + 1 - ℓ := fun ℓ => by
    rw [hπ, (interleavedWord_prod_apply D.word ℓ).1]
    simp [D.prod_subword]
  have h₂ : ∀ ℓ : Fin (n + 2), ((π ⟨ℓ + (n + 2), by omega⟩ : Fin _) : ℕ) =
      n + 1 - ℓ + (n + 2) := fun ℓ => by
    rw [hπ, (interleavedWord_prod_apply D.word ℓ).2]
    simp [D.prod_subword]
  let e₁ : Fin (n + 2) × Fin (n + 2) ↪ Fin (2 * n + 3 + 1) × Fin (2 * n + 3 + 1) :=
    ⟨fun p => (⟨p.1, by omega⟩, ⟨p.2, by omega⟩), fun p q h => by
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)⟩
  let e₂ : Fin (n + 2) × Fin (n + 2) ↪ Fin (2 * n + 3 + 1) × Fin (2 * n + 3 + 1) :=
    ⟨fun p => (⟨p.1 + (n + 2), by omega⟩, ⟨p.2 + (n + 2), by omega⟩), fun p q h => by
      simp only [Prod.mk.injEq, Fin.mk.injEq, Nat.add_right_cancel_iff] at h
      exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)⟩
  set S : Finset (Fin (n + 2) × Fin (n + 2)) := {p | p.1 < p.2}
  have hsub : S.map e₁ ∪ S.map e₂ ⊆
      ({p | p.1 < p.2 ∧ π p.2 < π p.1} : Finset (Fin (2 * n + 3 + 1) × Fin (2 * n + 3 + 1))) := by
    intro p hp
    simp only [S, mem_union, mem_map, mem_filter, mem_univ, true_and] at hp
    simp only [mem_filter, mem_univ, true_and, Fin.lt_def]
    rcases hp with ⟨⟨a, b⟩, hab, rfl⟩ | ⟨⟨a, b⟩, hab, rfl⟩ <;>
      simp only [e₁, e₂, Function.Embedding.coeFn_mk, h₁, h₂, Fin.lt_def] at hab ⊢ <;> omega
  have hdisj : Disjoint (S.map e₁) (S.map e₂) := by
    refine disjoint_left.2 fun p hp hp' => ?_
    simp only [mem_map] at hp hp'
    obtain ⟨⟨a, b⟩, -, rfl⟩ := hp
    obtain ⟨⟨c, d⟩, -, h⟩ := hp'
    simp only [e₁, e₂, Function.Embedding.coeFn_mk, Prod.mk.injEq, Fin.mk.injEq] at h
    omega
  calc D.word.length = #(S.map e₁ ∪ S.map e₂) := by
        rw [card_union_of_disjoint hdisj, card_map, card_map, card_filter_fst_lt_snd,
          ← D.length_subword_add_length_subword, D.length_subword, D.length_subword]
    _ ≤ _ := card_le_card hsub

/-- **The interleaved word of a double wiring diagram is reduced**, for the common interleaved
product of all double wiring diagrams. -/
theorem isReducedWord_interleavedWord (D E : DoubleWiringDiagram n) :
    IsReducedWord ((interleavedWord D.word).map gapSwap).prod (interleavedWord E.word) :=
  ⟨(prod_interleavedWord_eq D E).symm, by
    rw [inversionNumber_prod_interleavedWord, length_interleavedWord, D.length_word,
      E.length_word]⟩

/-- **A sequence with the interleaved product and length of a double wiring diagram is one.** -/
theorem exists_word_eq (D : DoubleWiringDiagram n) {E : List (Fin (n + 1) × Colour)}
    (hprod : ((interleavedWord E).map gapSwap).prod =
      ((interleavedWord D.word).map gapSwap).prod)
    (hlen : E.length = D.word.length) : ∃ D' : DoubleWiringDiagram n, D'.word = E := by
  have hsub : ∀ e, ((subword E e).map gapSwap).prod = Fin.revPerm := fun e => by
    rw [prod_interleavedWord_eq_iff.1 hprod e, D.prod_subword]
  have hle : ∀ e, (n + 2).choose 2 ≤ (subword E e).length := fun e => by
    simpa [hsub, inversionNumber_revPerm] using inversionNumber_prod_le (subword E e)
  have hsum := length_subword_thick_add_length_subword_thin E
  have hD := D.length_subword_add_length_subword
  rw [D.length_subword, D.length_subword] at hD
  have hthick := hle .thick
  have hthin := hle .thin
  refine ⟨⟨E, fun e => ?_, hsub⟩, rfl⟩
  cases e <;> omega

/-- A double wiring diagram is determined by its word. -/
theorem word_injective : Function.Injective (word : DoubleWiringDiagram n → _) := by
  rintro ⟨w, _, _⟩ ⟨w', _, _⟩ (rfl : w = w')
  rfl

/-- **An elementary move of the interleaved word is a swap or a braid.** An elementary move
(commutation or braid move) of the interleaved word of `E` is the interleaved word of a double
wiring diagram obtained from `E` by a swap or a braid. -/
theorem exists_isSwap_or_isBraid_of_isWordMove (E : DoubleWiringDiagram n)
    {c : List (Fin (2 * n + 3))} (h : IsWordMove (interleavedWord E.word) c) :
    ∃ E' : DoubleWiringDiagram n, interleavedWord E'.word = c ∧
      ((∃ p, E.IsSwap E' p) ∨ ∃ p, E.IsBraid E' p) := by
  have hprod := h.prod_eq
  rcases h with ⟨l, r, g, h, -, hE, rfl⟩ | ⟨l, r, g, h, hgh, hE, rfl⟩
  · rw [interleavedWord_eq_map, List.append_assoc, List.map_eq_append_iff] at hE
    obtain ⟨l', m', hw, rfl, hm⟩ := hE
    simp only [List.cons_append, List.nil_append, List.map_eq_cons_iff] at hm
    obtain ⟨a, m₁, rfl, rfl, b, r', rfl, rfl, rfl⟩ := hm
    obtain ⟨E', hE'⟩ := E.exists_word_eq (E := l' ++ [b, a] ++ r')
      (by rw [← hprod]; simp [interleavedWord_eq_map]) (by simp [hw])
    exact ⟨E', by simp [hE', interleavedWord_eq_map],
      Or.inl ⟨l'.length, l', r', a, b, rfl, by simp [hw], hE'⟩⟩
  · rw [interleavedWord_eq_map, List.append_assoc, List.map_eq_append_iff] at hE
    obtain ⟨l', m', hw, rfl, hm⟩ := hE
    simp only [List.cons_append, List.nil_append, List.map_eq_cons_iff] at hm
    obtain ⟨a, m₁, rfl, rfl, b, m₂, rfl, rfl, a₂, r', rfl, ha₂, rfl⟩ := hm
    rw [interleavedLetter_injective ha₂] at hw
    obtain ⟨i, c⟩ := a
    obtain ⟨j, d⟩ := b
    have hi := i.isLt
    have hj := j.isLt
    obtain ⟨rfl, hij⟩ : c = d ∧ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) := by
      cases c <;> cases d <;>
        simp only [val_interleavedLetter_thick, val_interleavedLetter_thin] at hgh <;>
        first | exact ⟨rfl, by omega⟩ | (exfalso; omega)
    obtain ⟨E', hE'⟩ := E.exists_word_eq (E := l' ++ [(j, c), (i, c), (j, c)] ++ r')
      (by rw [← hprod]; simp [interleavedWord_eq_map]) (by simp [hw])
    exact ⟨E', by simp [hE', interleavedWord_eq_map],
      Or.inr ⟨l'.length, l', r', c, i, j, hij, rfl, by simp [hw], hE'⟩⟩

/-- **Double wiring diagrams are connected by swaps and braids**: there are `r ≥ 0` and double
wiring diagrams `D = E₀, …, E_r = D'` with each `E_k` obtained from `E_{k-1}` by a swap or a
braid. -/
@[cluster_algebras "thm_double_matsumoto_tits"]
theorem reflTransGen_isSwap_or_isBraid (D D' : DoubleWiringDiagram n) :
    Relation.ReflTransGen
      (fun E E' : DoubleWiringDiagram n => (∃ p, E.IsSwap E' p) ∨ ∃ p, E.IsBraid E' p) D D' := by
  have key : ∀ c, Relation.ReflTransGen IsWordMove (interleavedWord D.word) c →
      ∃ E : DoubleWiringDiagram n, interleavedWord E.word = c ∧
        Relation.ReflTransGen
          (fun E E' : DoubleWiringDiagram n => (∃ p, E.IsSwap E' p) ∨ ∃ p, E.IsBraid E' p) D E := by
    intro c hc
    induction hc with
    | refl => exact ⟨D, rfl, .refl⟩
    | tail _ hbc ih =>
      obtain ⟨E, rfl, hDE⟩ := ih
      obtain ⟨E', rfl, hEE'⟩ := E.exists_isSwap_or_isBraid_of_isWordMove hbc
      exact ⟨E', rfl, hDE.tail hEE'⟩
  obtain ⟨E, hE, hDE⟩ := key _ ((isReducedWord_interleavedWord D D).reflTransGen_isWordMove
    (isReducedWord_interleavedWord D D'))
  rwa [word_injective (interleavedWord_injective hE)] at hDE

/-- Any two double wiring diagrams `D` and `D'` are related by local moves and swaps of two
adjacent crossings of different levels: there are `r ≥ 0` and double wiring diagrams
`D = E₀, …, E_r = D'` such that each step is a swap at some `p` of two crossings of different
levels, or a local move from `E_{k-1}` to `E_k`, or a local move from `E_k` to `E_{k-1}`. -/
@[cluster_algebras "thm_double_local_moves_connect"]
theorem reflTransGen_localMove (D D' : DoubleWiringDiagram n) :
    Relation.ReflTransGen
      (fun E E' : DoubleWiringDiagram n =>
        (∃ p, E.IsSwap E' p ∧ E.levelAt p ≠ E.levelAt (p + 1)) ∨ (∃ p, LocalMove E E' p) ∨
          ∃ p, LocalMove E' E p) D D' := by
  refine Relation.ReflTransGen.lift' id (fun E E' hEE' => ?_) (reflTransGen_isSwap_or_isBraid D D')
  rcases hEE' with ⟨p, l, r, a, b, rfl, hE, hE'⟩ | ⟨p, l, r, e, g, h, hgh, rfl, hE, hE'⟩
  · by_cases hlev : E.levelAt l.length = E.levelAt (l.length + 1)
    · have hab : a.1 = b.1 := by simpa [levelAt, hE] using hlev
      obtain ⟨i, c⟩ := a
      obtain ⟨j, d⟩ := b
      obtain rfl : i = j := hab
      cases c <;> cases d
      · obtain rfl := word_injective (hE.trans hE'.symm)
        exact .refl
      · exact .single (Or.inr (Or.inl ⟨l.length, Or.inr ⟨i, by simp [hE, hE'],
          by simp [hE, hE'], by simp [hE], by simp [hE']⟩⟩))
      · exact .single (Or.inr (Or.inr ⟨l.length, Or.inr ⟨i, by simp [hE, hE'],
          by simp [hE, hE'], by simp [hE'], by simp [hE]⟩⟩))
      · obtain rfl := word_injective (hE.trans hE'.symm)
        exact .refl
    · exact .single (Or.inl ⟨l.length, ⟨l, r, a, b, rfl, hE, hE'⟩, hlev⟩)
  · rcases hgh with hgh | hgh
    · exact .single (Or.inr (Or.inl ⟨l.length, Or.inl ⟨e, g, h, hgh, by simp [hE, hE'],
        by simp [hE, hE'], by simp [hE], by simp [hE']⟩⟩))
    · exact .single (Or.inr (Or.inr ⟨l.length, Or.inl ⟨e, h, g, hgh, by simp [hE, hE'],
        by simp [hE, hE'], by simp [hE'], by simp [hE]⟩⟩))

end DoubleWiringDiagram

end ClusterAlgebras

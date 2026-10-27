/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.ReducedWords
public import ClusterAlgebras.TotalPositivity.Moves

/-!
# The theorem of Matsumoto and Tits for wiring diagrams

Any two wiring diagrams on the same strands are connected by a finite chain of commutations and
braid moves. This is the case of the longest permutation `w₀` of the theorem of Matsumoto and
Tits that any two reduced words for an element of a Coxeter group are related by braid
relations.

The longest permutation `w₀ = Fin.revPerm` inverts every pair of positions, so its inversion
number is the number `(n + 2).choose 2` of pairs of strands. The word of a wiring diagram has
exactly that length and product `w₀`, so it is a reduced word for `w₀`, and any two reduced
words for `w₀` are joined by elementary moves on words. Each elementary move preserves the
length and the product, so every word along the way is again the word of a wiring diagram, and
an elementary move of words is then a commutation or a braid move of the corresponding
diagrams.

## Main results

* `ClusterAlgebras.WiringDiagram.isReducedWord_word`: the word of a wiring diagram is a reduced
  word for `w₀`.
* `ClusterAlgebras.WiringDiagram.reflTransGen_isCommutation_or_isBraidMove`: the theorem of
  Matsumoto and Tits for wiring diagrams.

## Implementation notes

* The chain `D = E₀, E₁, …, E_r = D'` of FWZ is expressed as `Relation.ReflTransGen` of
  the relation "obtained by a commutation at some position, or by a braid move at some
  position"; `r = 0` is allowed, as in FWZ.
* The braid moves are `WiringDiagram.IsBraidMove`, which allows both directions
  `(g, h, g) ↦ (h, g, h)` with `|g - h| = 1`. The elementary moves of words are
  `IsWordMove`, whose position is the length of the common prefix; that length is the position
  at which the corresponding commutation or braid move of diagrams takes place.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras, Chapter 1*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace WiringDiagram

variable {n : ℕ}

/-- **The word of a wiring diagram is a reduced word for `w₀`**: it has product `w₀` and length
the number of pairs of strands, which is the inversion number of `w₀`. -/
theorem isReducedWord_word (D : WiringDiagram n) : IsReducedWord Fin.revPerm D.word :=
  ⟨D.prod_eq, by rw [D.length_eq, inversionNumber_revPerm]⟩

/-- **An elementary move of the word of a wiring diagram is a commutation or a braid move.**
If `b` is obtained from `D.word` by an elementary move, then `b` is the word of a wiring diagram
`E` obtained from `D` by a commutation or a braid move. -/
theorem exists_isCommutation_or_isBraidMove_of_isWordMove (D : WiringDiagram n)
    {b : List (Fin (n + 1))} (h : IsWordMove D.word b) :
    ∃ E : WiringDiagram n,
      E.word = b ∧ ((∃ p, IsCommutation D E p) ∨ ∃ p, IsBraidMove D E p) := by
  have hlen : b.length = D.word.length := by
    rcases h with ⟨l, r, g, h, -, ha, hb⟩ | ⟨l, r, g, h, -, ha, hb⟩ <;> simp [ha, hb]
  let E : WiringDiagram n :=
    ⟨b, hlen.trans D.length_eq, (IsWordMove.prod_eq h).trans D.prod_eq⟩
  refine ⟨E, rfl, ?_⟩
  rcases h with ⟨l, r, g, h, hgh, ha, hb⟩ | ⟨l, r, g, h, hgh, ha, hb⟩
  · have h0 : D.levelAt l.length = g := by simp [levelAt, ha, List.getD_eq_getElem?_getD]
    have h1 : D.levelAt (l.length + 1) = h := by
      simp [levelAt, ha, List.getD_eq_getElem?_getD]
    refine Or.inl ⟨l.length, by simp [ha], ?_, ?_⟩
    · rw [h0, h1]; omega
    · change b = _
      rw [h0, h1, hb, ha]
      simp
  · have h0 : D.levelAt l.length = g := by simp [levelAt, ha, List.getD_eq_getElem?_getD]
    have h1 : D.levelAt (l.length + 1) = h := by
      simp [levelAt, ha, List.getD_eq_getElem?_getD]
    have h2 : D.levelAt (l.length + 2) = g := by
      simp [levelAt, ha, List.getD_eq_getElem?_getD]
    refine Or.inr ⟨l.length, by simp [ha], by rw [h0, h2], by rw [h0, h1]; exact hgh, ?_⟩
    change b = _
    rw [h0, h1, hb, ha]
    simp [spliceWord]

/-- **Matsumoto–Tits.** Any two wiring diagrams on the same strands are connected by a chain of
commutations and braid moves: `Relation.ReflTransGen` says there are `r ≥ 0` and wiring diagrams
`D = E₀, E₁, …, E_r = D'` with each `E_k` obtained from `E_{k-1}` by a commutation or a braid
move. The braid moves are `IsBraidMove`, which allows both directions `(g, h, g) ↦ (h, g, h)`
with `|g - h| = 1`. -/
@[cluster_algebras "thm_matsumoto_tits"]
theorem reflTransGen_isCommutation_or_isBraidMove (D D' : WiringDiagram n) :
    Relation.ReflTransGen
      (fun E E' : WiringDiagram n => (∃ p, IsCommutation E E' p) ∨ ∃ p, IsBraidMove E E' p)
      D D' := by
  have key : ∀ b, Relation.ReflTransGen IsWordMove D.word b → ∃ E : WiringDiagram n,
      E.word = b ∧ Relation.ReflTransGen
        (fun E E' : WiringDiagram n => (∃ p, IsCommutation E E' p) ∨ ∃ p, IsBraidMove E E' p)
        D E := by
    intro b hb
    induction hb with
    | refl => exact ⟨D, rfl, .refl⟩
    | tail _ hcd ih =>
      obtain ⟨E, rfl, hE⟩ := ih
      obtain ⟨F, hF, hEF⟩ := E.exists_isCommutation_or_isBraidMove_of_isWordMove hcd
      exact ⟨F, hF, hE.tail hEF⟩
  obtain ⟨E, hE, hDE⟩ :=
    key D'.word (D.isReducedWord_word.reflTransGen_isWordMove D'.isReducedWord_word)
  rwa [ext' hE] at hDE

end WiringDiagram

end ClusterAlgebras

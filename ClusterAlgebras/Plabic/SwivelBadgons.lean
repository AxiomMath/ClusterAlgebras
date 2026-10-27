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

/-!
# Badgons under swivel moves

A swivel move at a digon of a triple diagram keeps a badgon: walks along strands of `X` that avoid
`L* = {d₁, d̄₁, d₂, d̄₂}` are walks of the swivel move, and a parallel digon running along the two
strands through the digon gives a badgon of it.

* Let `X'` be the swivel move of a triple diagram `X` at a digon `{d₁, d₂}` with corners `x, y`,
  and `L* = {d₁, d̄₁, d₂, d̄₂}`. A walk of `X` along strands whose first and last darts lie outside
  `L*` is, up to darts of `L*`, a walk of `X'` with the same ends. A badgon of `X` away from `x, y`
  is therefore a badgon of `X'`; a walk from `x ∪ y` back to `x ∪ y` gives a monogon, a closed
  strand or, with a dart of `L*`, a parallel digon of `X'`; and a parallel digon with one corner
  `x` gives a parallel digon of `X'` after prepending a dart of `L*` to one of its sides, except
  when its sides run along the two strands through the digon, which is
  `hasBadgon_swivelMove_of_isParallelDigon`.

## Main results

* `ClusterAlgebras.TripleData.hasBadgon_swivelMove_of_isParallelDigon`: a parallel digon with a
  corner at a digon, running along the two strands through it, gives a badgon of the swivel move.
* `ClusterAlgebras.TripleData.hasBadgon_swivelMove`: badgons propagate through swivel moves.

## Implementation notes

* The badgons in `hasBadgon_swivelMove` are handled through walks along strands read in either
  direction, rather than through FWZ's case analysis on the four strands through the
  digon: a walk read backwards along the reverses of its darts is again a walk, so the two
  orientations of the strands need no separate treatment, and the symmetry exchanging `d₁` and
  `d₂` reduces a corner `y` to a corner `x`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset RailLabel

namespace TripleData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}

private theorem head?_eq_some_getElem {α : Type*} {l : List α} (h : 0 < l.length) :
    l.head? = some l[0] := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h]

private theorem getLast?_eq_some_getElem {α : Type*} {l : List α} (h : 0 < l.length) :
    l.getLast? = some l[l.length - 1] := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]

/-! ### Walks along strands -/

section Walks

variable {X : TripleData H b}

/-- **(M)** A walk of a pre-triple diagram from a triple point `u` back to `u`, arriving along
another pass than the one it leaves along, gives a monogon (read backwards if its darts are
`in`). -/
private theorem hasMonogon_of_isChain (hX : X.IsPreTripleDiagram) {K : List H} (hne : K ≠ [])
    (hB : ∀ k ∈ K, k ∉ X.bdry) (hK : K.IsChain X.StrandStep)
    (hint : ¬X.IsBoundaryVertex (X.vertexOf (K.head hne)))
    (hloop : X.vertexOf (X.inv (K.getLast hne)) = X.vertexOf (K.head hne))
    (hpass : X.inv (K.getLast hne) ≠ (X.rot ^ 3) (K.head hne)) : X.HasMonogon := by
  have hhead : K.head? = some (K.head hne) := List.head?_eq_some_head hne
  have hlast : K.getLast? = some (K.getLast hne) := List.getLast?_eq_some_getLast hne
  cases hout : X.isOut (K.head hne)
  · have hP := X.isStrandPath_reverse_map_inv_of_isChain hX hne hB hK hout
    have hh' : (K.reverse.map X.inv).head? = some (X.inv (K.getLast hne)) := by
      rw [List.head?_map, List.head?_reverse, hlast]
      rfl
    have hl' : (K.reverse.map X.inv).getLast? = some (X.inv (K.head hne)) := by
      rw [List.getLast?_map, List.getLast?_reverse, hhead]
      rfl
    have hint' : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (K.getLast hne))) := by rwa [hloop]
    refine ⟨K.reverse.map X.inv, hP, ?_, ?_, ?_⟩
    · rw [X.pathStart_of_head? hh', hloop]
      exact X.vertexOf_mem_internalVertices.2 hint
    · rw [X.pathEnd_of_getLast? hl', X.pathStart_of_head? hh', hX.inv_inv_apply, hloop]
    · intro e₁ he₁ eₘ heₘ
      rw [hh', Option.mem_some_iff] at he₁
      rw [hl', Option.mem_some_iff] at heₘ
      subst he₁ heₘ
      rw [hX.inv_inv_apply]
      intro h
      apply hpass
      rw [h, hX.rot_pow_three_rot_pow_three hint']
  · have hP := X.isStrandPath_of_isChain hX hne hB hK hout
    refine ⟨K, hP, ?_, ?_, ?_⟩
    · rw [X.pathStart_of_head? hhead]
      exact X.vertexOf_mem_internalVertices.2 hint
    · rw [X.pathEnd_of_getLast? hlast, X.pathStart_of_head? hhead, hloop]
    · intro e₁ he₁ eₘ heₘ
      rw [hhead, Option.mem_some_iff] at he₁
      rw [hlast, Option.mem_some_iff] at heₘ
      subst he₁ heₘ
      exact hpass

/-- **(W)** Two walks of a pre-triple diagram with darts of one orientation, from a triple point to
another one, with distinct first darts and distinct last darts, give a parallel digon. -/
private theorem hasParallelDigon_of_isChain (hX : X.IsPreTripleDiagram) {A B : List H}
    (hA : A ≠ []) (hB : B ≠ []) (hAB : ∀ k ∈ A, k ∉ X.bdry) (hBB : ∀ k ∈ B, k ∉ X.bdry)
    (hAc : A.IsChain X.StrandStep) (hBc : B.IsChain X.StrandStep)
    (horient : X.isOut (A.head hA) = X.isOut (B.head hB))
    (hs : X.vertexOf (A.head hA) = X.vertexOf (B.head hB))
    (he : X.vertexOf (X.inv (A.getLast hA)) = X.vertexOf (X.inv (B.getLast hB)))
    (hsint : ¬X.IsBoundaryVertex (X.vertexOf (A.head hA)))
    (heint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (A.getLast hA))))
    (hne : X.vertexOf (A.head hA) ≠ X.vertexOf (X.inv (A.getLast hA)))
    (hhead : A.head hA ≠ B.head hB) (hlast : A.getLast hA ≠ B.getLast hB) :
    X.HasParallelDigon := by
  have hAh : A.head? = some (A.head hA) := List.head?_eq_some_head hA
  have hBh : B.head? = some (B.head hB) := List.head?_eq_some_head hB
  have hAl : A.getLast? = some (A.getLast hA) := List.getLast?_eq_some_getLast hA
  have hBl : B.getLast? = some (B.getLast hB) := List.getLast?_eq_some_getLast hB
  cases hout : X.isOut (A.head hA)
  · have hPA := X.isStrandPath_reverse_map_inv_of_isChain hX hA hAB hAc hout
    have hPB := X.isStrandPath_reverse_map_inv_of_isChain hX hB hBB hBc (horient ▸ hout)
    have hh : ∀ (K : List H) (hK : K ≠ []), (K.reverse.map X.inv).head? =
        some (X.inv (K.getLast hK)) := fun K hK => by
      rw [List.head?_map, List.head?_reverse, List.getLast?_eq_some_getLast hK]
      rfl
    have hl : ∀ (K : List H) (hK : K ≠ []), (K.reverse.map X.inv).getLast? =
        some (X.inv (K.head hK)) := fun K hK => by
      rw [List.getLast?_map, List.getLast?_reverse, List.head?_eq_some_head hK]
      rfl
    refine ⟨A.reverse.map X.inv, B.reverse.map X.inv, X.vertexOf (X.inv (A.getLast hA)),
      X.vertexOf (A.head hA), ⟨hne.symm, X.vertexOf_mem_internalVertices.2 heint,
        X.vertexOf_mem_internalVertices.2 hsint, hPA, hPB, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [X.pathStart_of_head? (hh A hA)]
    · rw [X.pathEnd_of_getLast? (hl A hA), hX.inv_inv_apply]
    · rw [X.pathStart_of_head? (hh B hB), he]
    · rw [X.pathEnd_of_getLast? (hl B hB), hX.inv_inv_apply, hs]
    · rw [hh A hA, hh B hB]
      exact fun h => hlast (X.inv.injective (Option.some_injective _ h))
    · rw [hl A hA, hl B hB]
      exact fun h => hhead (X.inv.injective (Option.some_injective _ h))
  · have hPA := X.isStrandPath_of_isChain hX hA hAB hAc hout
    have hPB := X.isStrandPath_of_isChain hX hB hBB hBc (horient ▸ hout)
    refine ⟨A, B, X.vertexOf (A.head hA), X.vertexOf (X.inv (A.getLast hA)),
      ⟨hne, X.vertexOf_mem_internalVertices.2 hsint, X.vertexOf_mem_internalVertices.2 heint,
        hPA, hPB, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [X.pathStart_of_head? hAh]
    · rw [X.pathEnd_of_getLast? hAl]
    · rw [X.pathStart_of_head? hBh, hs]
    · rw [X.pathEnd_of_getLast? hBl, he]
    · rw [hAh, hBh]
      exact fun h => hhead (Option.some_injective _ h)
    · rw [hAl, hBl]
      exact fun h => hlast (Option.some_injective _ h)

omit [Fintype H] [DecidableEq H] in
/-- **Shortening a walk**: a chain has a sub-chain without repeated entries with the same first and
last entries. -/
private theorem exists_isChain_nodup {r : H → H → Prop} :
    ∀ (n : ℕ) (K : List H), K.length = n → K.IsChain r → K ≠ [] →
      ∃ K' : List H, K'.IsChain r ∧ K'.head? = K.head? ∧ K'.getLast? = K.getLast? ∧ K'.Nodup ∧
        ∀ k ∈ K', k ∈ K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hn hK hne
    by_cases hnd : K.Nodup
    · exact ⟨K, hK, rfl, rfl, hnd, fun _ h => h⟩
    rw [List.nodup_iff_getElem?_ne_getElem?] at hnd
    push Not at hnd
    obtain ⟨a, c, hac, hc, heq⟩ := hnd
    have ha : a < K.length := by omega
    rw [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hc, Option.some_inj] at heq
    set K₁ := K.take a ++ K.drop c with hK₁
    have hlen : K₁.length < n := by simp [hK₁]; omega
    have hK₁c : K₁.IsChain r := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0
        simpa [hK₁] using hK.drop c
      · rw [hK₁, List.isChain_append]
        refine ⟨hK.take a, hK.drop c, fun x hx y hy => ?_⟩
        rw [List.getLast?_take, if_neg (by omega), List.getElem?_eq_getElem (by omega),
          Option.some_or, Option.mem_some_iff] at hx
        rw [List.head?_drop, List.getElem?_eq_getElem hc, Option.mem_some_iff] at hy
        subst hx hy
        rw [← heq]
        have := (List.isChain_iff_getElem.1 hK) (a - 1) (by omega)
        simpa [show a - 1 + 1 = a by omega] using this
    have hK₁ne : K₁ ≠ [] := by
      intro h
      have := congrArg List.length h
      simp [hK₁] at this
      omega
    obtain ⟨K', h1, h2, h3, h4, h5⟩ := ih _ hlen K₁ rfl hK₁c hK₁ne
    refine ⟨K', h1, ?_, ?_, h4, fun k hk => ?_⟩
    · rw [h2, hK₁]
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0
        rw [List.take_zero, List.nil_append, List.head?_drop, List.getElem?_eq_getElem hc, ← heq,
          List.head?_eq_getElem?, List.getElem?_eq_getElem ha]
      · rw [List.head?_append, List.head?_take, if_neg (by omega), List.head?_eq_getElem?,
          List.getElem?_eq_getElem (by omega : 0 < K.length), Option.some_or]
    · rw [h3, hK₁, List.getLast?_append_of_ne_nil _ (by simp; omega), List.getLast?_drop,
        if_neg (by omega)]
    · rcases List.mem_append.1 (h5 k hk) with h | h
      · exact List.mem_of_mem_take h
      · exact List.mem_of_mem_drop h

/-- **(M)** for a segment `K[i], …, K[j]` of a walk. -/
private theorem hasMonogon_of_segment (hX : X.IsPreTripleDiagram) {K : List H}
    (hB : ∀ k ∈ K, k ∉ X.bdry) (hK : K.IsChain X.StrandStep) {i j : ℕ} (hij : i ≤ j)
    (hj : j < K.length) (hint : ¬X.IsBoundaryVertex (X.vertexOf (K[i]'(by omega))))
    (hloop : X.vertexOf (X.inv K[j]) = X.vertexOf (K[i]'(by omega)))
    (hpass : X.inv K[j] ≠ (X.rot ^ 3) (K[i]'(by omega))) : X.HasMonogon := by
  set K' := (K.drop i).take (j - i + 1) with hK'
  have hlen : K'.length = j - i + 1 := by simp [hK']; omega
  have hne : K' ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hhead : K'.head hne = K[i]'(by omega) := by
    rw [List.head_eq_getElem]
    simp [hK']
  have hlast : K'.getLast hne = K[j] := by
    rw [List.getLast_eq_getElem]
    simp only [hK', List.getElem_take, List.getElem_drop]
    congr 1
    simp at hlen ⊢
    omega
  refine hasMonogon_of_isChain hX hne
    (fun k hk => hB k (List.mem_of_mem_drop (List.mem_of_mem_take hk))) ((hK.drop i).take _)
    ?_ ?_ ?_
  · rw [hhead]
    exact hint
  · rw [hhead, hlast]
    exact hloop
  · rw [hhead, hlast]
    exact hpass

/-- In a pre-triple diagram without monogons, a walk without repeated darts from a triple point to
another vertex passes through pairwise distinct vertices. -/
private theorem vertices_ne_of_isChain (hX : X.IsPreTripleDiagram) (hmono : ¬X.HasMonogon)
    {K : List H} (hK0 : 0 < K.length) (hB : ∀ k ∈ K, k ∉ X.bdry) (hK : K.IsChain X.StrandStep)
    (hnd : K.Nodup) (hint : ¬X.IsBoundaryVertex (X.vertexOf K[0]))
    (hend : X.vertexOf (X.inv K[K.length - 1]) ≠ X.vertexOf K[0]) :
    (∀ t (ht : t < K.length), X.vertexOf (X.inv K[t]) ≠ X.vertexOf K[0]) ∧
      ∀ s t (hs : s < t) (ht : t < K.length),
        X.vertexOf (X.inv (K[s]'(by omega))) ≠ X.vertexOf (X.inv K[t]) := by
  have hKg := List.isChain_iff_getElem.1 hK
  have hnd' := List.nodup_iff_injective_get.1 hnd
  have hinj : ∀ s t (hs : s < K.length) (ht : t < K.length), K[s] = K[t] → s = t :=
    fun s t hs ht h => congrArg Fin.val (hnd' (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) h)
  refine ⟨fun t ht h => ?_, fun s t hs ht h => ?_⟩
  · by_cases hlast : t + 1 = K.length
    · apply hend
      have e : K[t] = K[K.length - 1] := by
        congr 1
        omega
      rw [← e]
      exact h
    · apply hmono
      refine hasMonogon_of_segment hX hB hK (Nat.zero_le t) ht hint h fun hp => ?_
      have := (hKg t (by omega)).2
      rw [hp, hX.rot_pow_three_rot_pow_three hint] at this
      exact absurd (hinj _ _ (by omega) (by omega) this) (by omega)
  · apply hmono
    have hs1 := hKg s (by omega)
    refine hasMonogon_of_segment hX hB hK (i := s + 1) (by omega) ht
      (by rw [hs1.vertexOf_eq]; exact hs1.1) (by rw [hs1.vertexOf_eq]; exact h.symm) fun hp => ?_
    rw [hs1.2, hX.rot_pow_three_rot_pow_three hs1.1] at hp
    exact absurd (hinj _ _ (by omega) (by omega) (X.inv.injective hp)) (by omega)

/-- A walk without repeated darts in a pre-triple diagram without monogons, entered from the dart
`ℓ`, comes back to the vertex `v(ℓ)` only at its end. -/
private theorem vertexOf_inv_ne_of_strandStep (hX : X.IsPreTripleDiagram) (hmono : ¬X.HasMonogon)
    {K : List H} (hK0 : 0 < K.length) (hB : ∀ k ∈ K, k ∉ X.bdry) (hK : K.IsChain X.StrandStep)
    {ℓ : H} (hℓB : ℓ ∉ X.bdry) (hℓ : X.StrandStep ℓ K[0])
    (hℓint : ¬X.IsBoundaryVertex (X.vertexOf ℓ))
    (hD1 : ∀ t (ht : t < K.length), X.vertexOf (X.inv K[t]) ≠ X.vertexOf K[0])
    (hend : X.vertexOf (X.inv K[K.length - 1]) ≠ X.vertexOf ℓ) :
    ∀ t (ht : t < K.length), X.vertexOf (X.inv K[t]) ≠ X.vertexOf ℓ := by
  have hKg := List.isChain_iff_getElem.1 hK
  intro t ht h
  by_cases hlast : t + 1 = K.length
  · apply hend
    have e : K[t] = K[K.length - 1] := by
      congr 1
      omega
    rw [← e]
    exact h
  · apply hmono
    have hc : (ℓ :: K).IsChain X.StrandStep := by
      rcases K with _ | ⟨k, K⟩
      · simp at hK0
      · exact List.isChain_cons_cons.2 ⟨hℓ, hK⟩
    refine hasMonogon_of_segment hX (K := ℓ :: K)
      (fun k hk => (List.mem_cons.1 hk).elim (fun h => h ▸ hℓB) (hB k)) hc (i := 0) (j := t + 1)
      (Nat.zero_le _) (by simp; omega) hℓint h fun hp => ?_
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hp
    have := (hKg t (by omega)).2
    rw [hp, hX.rot_pow_three_rot_pow_three hℓint] at this
    apply hD1 (t + 1) (by omega)
    rw [this, hℓ.vertexOf_eq]

/-- Two walks with a common dart agree backwards from it. -/
private theorem getElem_sub_eq_of_isChain {A B : List H} (hA : A.IsChain X.StrandStep)
    (hB : B.IsChain X.StrandStep) {i j : ℕ} (hi : i < A.length) (hj : j < B.length)
    (h : A[i] = B[j]) : ∀ m (hmi : m ≤ i) (hmj : m ≤ j), A[i - m] = B[j - m] := by
  intro m
  induction m with
  | zero => simpa using h
  | succ m ih =>
    intro hmi hmj
    have h1 := ((List.isChain_iff_getElem.1 hA) (i - (m + 1)) (by omega)).2
    have h2 := ((List.isChain_iff_getElem.1 hB) (j - (m + 1)) (by omega)).2
    have e1 : A[i - (m + 1) + 1] = A[i - m] := by congr 1; omega
    have e2 : B[j - (m + 1) + 1] = B[j - m] := by congr 1; omega
    rw [e1] at h1
    rw [e2] at h2
    have := ih (by omega) (by omega)
    rw [h1, h2] at this
    exact X.inv.injective ((X.rot ^ 3).injective this)

/-- **Cutting two walks** from a common vertex at the first vertex of the second walk that lies on
the first one. -/
private theorem exists_cut {A₀ B₀ : List H} (hA0 : 0 < A₀.length) (hB0 : 0 < B₀.length)
    (hAc : A₀.IsChain X.StrandStep) (hBc : B₀.IsChain X.StrandStep)
    (hx : X.vertexOf A₀[0] = X.vertexOf B₀[0])
    (hw : X.vertexOf (X.inv A₀[A₀.length - 1]) = X.vertexOf (X.inv B₀[B₀.length - 1]))
    (hD1A : ∀ t (ht : t < A₀.length), X.vertexOf (X.inv A₀[t]) ≠ X.vertexOf A₀[0])
    (hD1B : ∀ t (ht : t < B₀.length), X.vertexOf (X.inv B₀[t]) ≠ X.vertexOf B₀[0])
    (hhead : A₀[0] ≠ B₀[0]) :
    ∃ i j, ∃ (hi : i < A₀.length) (hj : j < B₀.length),
      X.vertexOf (X.inv A₀[i]) = X.vertexOf (X.inv B₀[j]) ∧ A₀[i] ≠ B₀[j] ∧
      ∀ j' (hj' : j' < j) t (ht : t < A₀.length),
        X.vertexOf (X.inv (B₀[j']'(by omega))) ≠ X.vertexOf (X.inv A₀[t]) := by
  classical
  have hex : ∃ j, ∃ hj : j < B₀.length, ∃ i, ∃ hi : i < A₀.length,
      X.vertexOf (X.inv B₀[j]) = X.vertexOf (X.inv A₀[i]) :=
    ⟨B₀.length - 1, by omega, A₀.length - 1, by omega, hw.symm⟩
  obtain ⟨hj, i, hi, hij⟩ := Nat.find_spec hex
  set j := Nat.find hex with hjdef
  refine ⟨i, j, hi, hj, hij.symm, fun h => ?_, fun j' hj' t ht h' =>
    Nat.find_min hex hj' ⟨by omega, t, ht, h'⟩⟩
  have hb := getElem_sub_eq_of_isChain hAc hBc hi hj h
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have e := hb i le_rfl hlt.le
    simp only [Nat.sub_self] at e
    have hs := ((List.isChain_iff_getElem.1 hBc) (j - i - 1) (by omega))
    have e' : B₀[j - i - 1 + 1] = B₀[j - i] := by congr 1; omega
    rw [e'] at hs
    apply hD1B (j - i - 1) (by omega)
    rw [← hs.vertexOf_eq, ← e, hx]
  · have e := hb i le_rfl (by omega)
    simp only [Nat.sub_self, show j - i = 0 by omega] at e
    exact hhead e
  · have e := hb j hgt.le le_rfl
    simp only [Nat.sub_self] at e
    have hs := ((List.isChain_iff_getElem.1 hAc) (i - j - 1) (by omega))
    have e' : A₀[i - j - 1 + 1] = A₀[i - j] := by congr 1; omega
    rw [e'] at hs
    apply hD1A (i - j - 1) (by omega)
    rw [← hs.vertexOf_eq, e, ← hx]

/-- **(C)** A walk of `X` closing up into a closed strand gives, through the swivel move at a
digon, a closed strand of the swivel move, hence a badgon of it. -/
private theorem hasBadgon_swivelMove_of_cycle (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {K : List H} (hK0 : 0 < K.length) (hB : ∀ k ∈ K, k ∉ X.bdry)
    (hK : K.IsChain X.StrandStep)
    (hint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv K[K.length - 1])))
    (hcyc : (X.rot ^ 3) (X.inv K[K.length - 1]) = K[0]) {z : H} (hz : z ∈ K)
    (hzL : z ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) :
    (X.swivelMove d₁).HasBadgon := by
  have hpre := hX.toIsPreTripleDiagram
  have hKg := List.isChain_iff_getElem.1 hK
  set Ls : Finset H := {d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} with hLs
  have hS : ∀ e ∈ K, ¬X.RunsToEndpoint e ∧ X.strandMap e ∈ K := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
    by_cases ht' : t + 1 < K.length
    · exact ⟨(hKg t ht').1, by rw [(hKg t ht').strandMap_eq]; exact List.getElem_mem _⟩
    · have e : K[t] = K[K.length - 1] := by congr 1; omega
      rw [e]
      refine ⟨hint, ?_⟩
      rw [X.strandMap_of_not_runsToEndpoint hint]
      change (X.rot ^ 3) (X.inv K[K.length - 1]) ∈ K
      rw [hcyc]
      exact List.getElem_mem _
  have hSiter : ∀ e ∈ K, ∀ m, X.strandMap^[m] e ∈ K := by
    intro e he m
    induction m with
    | zero => exact he
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact (hS _ ih).2
  have hKint : ∀ e ∈ K, ¬X.IsBoundaryVertex (X.vertexOf e) := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
    rcases t with _ | t
    · rw [← hcyc, X.vertexOf_rot_pow_apply]
      exact hint
    · rw [(hKg t ht).vertexOf_eq]
      exact (hKg t ht).1
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, -, -, hV₁, hV₂, hi₁, hi₂⟩ :=
    hd.exists_darts hpre
  have hLint : ∀ e ∈ Ls, ¬X.IsBoundaryVertex (X.vertexOf e) := by
    intro e he
    simp only [hLs, mem_insert, mem_singleton] at he
    rcases he with h | h | h | h <;> rw [h]
    · exact hi₁
    · rw [X.vertexOf_eq_of_mem (show X.inv d₁ ∈ X.vertexOf (X.facePerm d₁) by rw [hV₂]; simp)]
      exact hi₂
    · exact hi₂
    · rw [X.vertexOf_eq_of_mem (show X.inv (X.facePerm d₁) ∈ X.vertexOf d₁ by rw [hV₁]; simp)]
      exact hi₁
  set S' := (X.swivelMove d₁).strandMap with hS'def
  have key : ∀ m, (S'^[m] z ∈ K ∧ S'^[m] z ∉ Ls) ∨
      (S'^[m] z ∈ Ls ∧ S'^[m + 1] z ∈ K ∧ S'^[m + 1] z ∉ Ls) := by
    intro m
    induction m with
    | zero => exact Or.inl ⟨hz, hzL⟩
    | succ m ih =>
      rcases ih with ⟨hg, hgL⟩ | ⟨-, h1, h2⟩
      · obtain ⟨w', hw'L, ⟨k, hk, hSk, -⟩, ⟨k', hk', hS'k, hS'mid⟩⟩ :=
          exists_iterate_strandMap_swivelMove hpre hd hgL (hS _ hg).1
        have hw'K : w' ∈ K := hSk ▸ hSiter _ hg _
        interval_cases k'
        · left
          have e : S' (S'^[m] z) = w' := by simpa using hS'k
          rw [Function.iterate_succ_apply', e]
          exact ⟨hw'K, hw'L⟩
        · right
          have e : S'^[2] (S'^[m] z) = w' := hS'k
          refine ⟨?_, ?_, ?_⟩
          · rw [Function.iterate_succ_apply']
            have := hS'mid 1 le_rfl le_rfl
            rw [Function.iterate_one] at this
            exact this
          · rw [show m + 1 + 1 = 2 + m by omega, Function.iterate_add_apply, e]
            exact hw'K
          · rw [show m + 1 + 1 = 2 + m by omega, Function.iterate_add_apply, e]
            exact hw'L
      · exact Or.inl ⟨h1, h2⟩
  have hcl : (X.swivelMove d₁).IsClosedStrand ((X.swivelMove d₁).strandOrbit z) := by
    refine ⟨z, hB z hz, rfl, fun e he => ?_⟩
    obtain ⟨m, rfl⟩ := (X.swivelMove d₁).mem_strandOrbit.1 he
    rw [hd.isBoundaryVertex_swivelMove_iff hpre]
    rcases key m with ⟨h, -⟩ | ⟨h, -⟩
    · exact hKint _ h
    · exact hLint _ h
  by_contra h
  exact not_isClosedStrand_of_not_hasBadgon (hd.isTripleDiagram_swivelMove hX) h _ hcl

omit [Fintype H] [DecidableEq H] in
private theorem rot_pow_three_apply_perm (f : Equiv.Perm H) (e : H) : (f ^ 3) e = f (f (f e)) :=
  rfl

/-- A dart lies at `x` or at `y` exactly when its vertex is one of them. -/
private theorem mem_union_vertexOf_iff {d₁ z : H} :
    z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) ↔
      X.vertexOf z = X.vertexOf d₁ ∨ X.vertexOf z = X.vertexOf (X.facePerm d₁) := by
  rw [mem_union, X.mem_vertexOf_iff_vertexOf_eq, X.mem_vertexOf_iff_vertexOf_eq]

/-- Away from the digon, a step of a walk of `X` is a step of a walk of the swivel move. -/
private theorem strandStep_swivelMove (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {e e' : H} (h : X.StrandStep e e')
    (hxy : X.inv e ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) :
    (X.swivelMove d₁).StrandStep e e' := by
  refine ⟨?_, ?_⟩
  · change ¬(X.swivelMove d₁).IsBoundaryVertex ((X.swivelMove d₁).vertexOf (X.inv e))
    rw [hd.isBoundaryVertex_swivelMove_iff hX]
    exact h.1
  · rw [h.2]
    change (X.rot ^ 3) (X.inv e) = (X.swivelRot d₁ ^ 3) (X.inv e)
    have h1 : X.rot (X.inv e) ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun h' =>
      hxy (rot_mem_union_vertexOf_iff.1 h')
    have h2 : X.rot (X.rot (X.inv e)) ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun h' =>
      h1 (rot_mem_union_vertexOf_iff.1 h')
    rw [X.rot_pow_three_apply, rot_pow_three_apply_perm, swivelRot_apply_of_notMem hxy,
      swivelRot_apply_of_notMem h1, swivelRot_apply_of_notMem h2]

/-- Along a walk, the orientation is constant. -/
private theorem isOut_getElem_of_isChain (hX : X.IsPreTripleDiagram) {K : List H}
    (hB : ∀ k ∈ K, k ∉ X.bdry) (hK : K.IsChain X.StrandStep) :
    ∀ i (hi : i < K.length), X.isOut K[i] = X.isOut (K[0]'(by omega)) := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [((List.isChain_iff_getElem.1 hK) i hi).isOut_eq hX (hB _ (List.getElem_mem _)), ih]

/-- The reverse `k̄_n, …, k̄₀` of a walk `k₀, …, k_n` is a walk. -/
private theorem exists_reverse_walk (hX : X.IsPreTripleDiagram) {n : ℕ} {k : ℕ → H}
    (hk0B : k 0 ∉ X.bdry)
    (hkstep : ∀ j < n, ¬X.IsBoundaryVertex (X.vertexOf (X.inv (k j))) ∧
      k (j + 1) = (X.rot ^ 3) (X.inv (k j))) :
    ∃ E : List H, ∃ _ : E.length = n + 1, (∀ i (hi : i < E.length), E[i] = X.inv (k (n - i))) ∧
      E.IsChain X.StrandStep ∧ (∀ e ∈ E, e ∉ X.bdry) ∧ (∀ j ≤ n, k j ∉ X.bdry) ∧
      (∀ j ≤ n, X.isOut (k j) = X.isOut (k 0)) ∧ E.getLast? = some (X.inv (k 0)) := by
  have hkB : ∀ j ≤ n, k j ∉ X.bdry := by
    intro j hj
    rcases j with _ | j
    · exact hk0B
    · intro h
      apply (hkstep j (by omega)).1
      rw [← X.vertexOf_rot_pow_apply 3, ← (hkstep j (by omega)).2]
      exact ⟨_, X.self_mem_vertexOf _, h⟩
  set kl := (List.range (n + 1)).map k with hkl
  have hklc : kl.IsChain X.StrandStep := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [hkl, List.length_map, List.length_range] at hi
    simp only [hkl, List.getElem_map, List.getElem_range]
    exact ⟨(hkstep i (by omega)).1, (hkstep i (by omega)).2⟩
  have hklB : ∀ e ∈ kl, e ∉ X.bdry := by
    intro e he
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
    exact hkB j (by simp at hj; omega)
  have hklen : kl.length = n + 1 := by simp [hkl]
  refine ⟨kl.reverse.map X.inv, by simp [hkl], fun i hi => ?_, ?_, ?_, hkB, fun j hj => ?_, ?_⟩
  · simp only [hkl, List.getElem_map, List.getElem_reverse, List.getElem_range,
      List.length_map, List.length_range]
    congr 2
  · rw [List.isChain_map, List.isChain_reverse]
    exact hklc.imp fun _ _ h => h.inv_inv hX
  · intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact hX.inv_notMem_bdry (hklB e' (List.mem_reverse.1 he'))
  · have := isOut_getElem_of_isChain hX hklB hklc j (by omega)
    simpa [hkl] using this
  · rw [List.getLast?_map, List.getLast?_reverse, hkl, List.head?_map, List.head?_range,
      if_neg (by omega)]
    rfl

/-- The parallel digon case of the escape: the escape walk comes back to an inner vertex of `T'`;
in the swivel move, it continues along `T`, and runs beside `T'` to the end `u`. -/
private theorem hasParallelDigon_swivelMove_of_escape (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁))
    {T T' : List H} (hT0 : 0 < T.length) (hT'0 : 0 < T'.length)
    (hTB : ∀ e ∈ T, e ∉ X.bdry) (hT'B : ∀ e ∈ T', e ∉ X.bdry)
    (hTc : T.IsChain X.StrandStep) (hT'c : T'.IsChain X.StrandStep)
    (hu : X.vertexOf (X.inv T[T.length - 1]) = X.vertexOf (X.inv T'[T'.length - 1]))
    (huint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv T[T.length - 1])))
    (hux : X.vertexOf (X.inv T[T.length - 1]) ≠ X.vertexOf d₁)
    (huy : X.vertexOf (X.inv T[T.length - 1]) ≠ X.vertexOf (X.facePerm d₁))
    (hlast : T[T.length - 1] ≠ T'[T'.length - 1])
    {CS : H → Prop} (hCSinv : ∀ e, CS e → CS (X.inv e)) (hT'CS : ∀ e ∈ T', CS e)
    {CV : Finset H → Prop} (hCVx : CV (X.vertexOf d₁)) (hCVy : CV (X.vertexOf (X.facePerm d₁)))
    {k₁ : H} {r : ℕ}
    (hk₁v : X.vertexOf k₁ = X.vertexOf d₁ ∨ X.vertexOf k₁ = X.vertexOf (X.facePerm d₁))
    (hr : r < T.length) (hR : ((X.swivelMove d₁).rot ^ 3) k₁ = T[r])
    (hTxy : ∀ t, r ≤ t → ∀ (ht : t + 1 < T.length),
      X.vertexOf (X.inv T[t]) ≠ X.vertexOf d₁ ∧
        X.vertexOf (X.inv T[t]) ≠ X.vertexOf (X.facePerm d₁))
    (hT'xy : ∀ s (hs : s + 1 < T'.length), X.vertexOf (X.inv T'[s]) ≠ X.vertexOf d₁ ∧
      (X.vertexOf (X.inv T'[s]) = X.vertexOf (X.facePerm d₁) → s = 0))
    (horient : X.isOut k₁ ≠ X.isOut T'[0])
    {n : ℕ} {k : ℕ → H} (hk0 : k 0 = k₁)
    (hkstep : ∀ j < n, ¬X.IsBoundaryVertex (X.vertexOf (X.inv (k j))) ∧
      ¬CV (X.vertexOf (X.inv (k j))) ∧ k (j + 1) = (X.rot ^ 3) (X.inv (k j)))
    (hkC : ∀ j ≤ n, ¬CS (k j))
    {t : ℕ} (ht : t + 1 < T'.length)
    (htv : X.vertexOf (X.inv (k n)) = X.vertexOf (X.inv T'[t]))
    (hu'x : X.vertexOf (X.inv (k n)) ≠ X.vertexOf d₁)
    (hu'y : X.vertexOf (X.inv (k n)) ≠ X.vertexOf (X.facePerm d₁))
    (h4 : X.vertexOf (X.inv (k n)) ≠ X.vertexOf (X.inv T[T.length - 1])) :
    (X.swivelMove d₁).HasParallelDigon := by
  have hpre' := hX.toIsPreTripleDiagram
  set x := X.vertexOf d₁ with hxdef
  set y := X.vertexOf (X.facePerm d₁) with hydef
  obtain ⟨hi₁, hi₂⟩ := hd.not_isBoundaryVertex hpre'
  have hk₁int : ¬X.IsBoundaryVertex (X.vertexOf k₁) := by
    rcases hk₁v with h | h <;> rw [h]
    · exact hi₁
    · exact hi₂
  obtain ⟨E, hElen, hEget, hEc, hEB, hkB, hkout, hElast⟩ := exists_reverse_walk hpre'
    (k := k) (n := n) (by rw [hk0]; exact fun h => hk₁int ⟨k₁, X.self_mem_vertexOf _, h⟩)
    (fun j hj => ⟨(hkstep j hj).1, (hkstep j hj).2.2⟩)
  rw [hk0] at hkout hElast
  have hnC : ¬CS (X.inv (k n)) := fun h => hkC n le_rfl (by
    have := hCSinv _ h
    rwa [hpre'.inv_inv_apply] at this)
  set u' := X.vertexOf (X.inv (k n)) with hu'
  have hu'int : ¬X.IsBoundaryVertex u' := by
    rw [htv]
    exact ((List.isChain_iff_getElem.1 hT'c) t ht).1
  set X' := X.swivelMove d₁ with hX'def
  have hX'pre : X'.IsPreTripleDiagram := hd.isPreTripleDiagram_swivelMove hpre'
  have hnxy : ∀ e, X.vertexOf e ≠ x → X.vertexOf e ≠ y →
      e ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun e h1 h2 h =>
    (mem_union_vertexOf_iff.1 h).elim h1 h2
  have hv' : ∀ e, X.vertexOf e ≠ x → X.vertexOf e ≠ y → X'.vertexOf e = X.vertexOf e :=
    fun e h1 h2 => vertexOf_swivelMove_of_notMem (hnxy e h1 h2)
  have hbv' : ∀ e, X'.IsBoundaryVertex (X'.vertexOf e) ↔ X.IsBoundaryVertex (X.vertexOf e) :=
    fun e => hd.isBoundaryVertex_swivelMove_iff hpre' e
  -- the walk `k̄_n, …, k̄₀, T[r], …` of the swivel move
  set A' := E ++ T.drop r with hA'
  set B' := T'.drop (t + 1) with hB'
  have hA'len : A'.length = n + 1 + (T.length - r) := by simp [hA', hElen]
  have hB'len : B'.length = T'.length - (t + 1) := by simp [hB']
  have hEc' : E.IsChain X'.StrandStep := by
    rw [List.isChain_iff_getElem] at hEc ⊢
    intro i hi
    obtain ⟨m, hm⟩ : ∃ m, n - i = m + 1 := ⟨n - i - 1, by rw [hElen] at hi; omega⟩
    have hs := hkstep m (by rw [hElen] at hi; omega)
    have hv : X.vertexOf (k (n - i)) = X.vertexOf (X.inv (k m)) := by
      rw [hm, hs.2.2, X.vertexOf_rot_pow_apply]
    refine strandStep_swivelMove hpre' hd (hEc i hi) (hnxy _ ?_ ?_)
    · rw [hEget i (by omega), hpre'.inv_inv_apply, hv]
      intro h
      exact hs.2.1 (h ▸ hCVx)
    · rw [hEget i (by omega), hpre'.inv_inv_apply, hv]
      intro h
      exact hs.2.1 (h ▸ hCVy)
  have hTr' : (T.drop r).IsChain X'.StrandStep := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_drop] at hi
    simp only [List.getElem_drop]
    have hs := (List.isChain_iff_getElem.1 hTc) (r + i) (by omega)
    simp only [show r + (i + 1) = r + i + 1 from by omega]
    exact strandStep_swivelMove hpre' hd hs
      (hnxy _ (hTxy (r + i) (by omega) (by omega)).1 (hTxy (r + i) (by omega) (by omega)).2)
  have hA'c : A'.IsChain X'.StrandStep := by
    rw [hA', List.isChain_append]
    refine ⟨hEc', hTr', fun a ha c hc => ?_⟩
    rw [hElast, Option.mem_def, Option.some.injEq] at ha
    rw [List.head?_drop, List.getElem?_eq_getElem hr, Option.mem_def, Option.some.injEq] at hc
    subst ha hc
    refine ⟨?_, ?_⟩
    · change ¬X'.IsBoundaryVertex (X'.vertexOf (X.inv (X.inv k₁)))
      rw [hbv', hpre'.inv_inv_apply]
      exact hk₁int
    · change T[r] = (X'.rot ^ 3) (X.inv (X.inv k₁))
      rw [hpre'.inv_inv_apply, hR]
  have hB'c : B'.IsChain X'.StrandStep := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [hB', List.length_drop] at hi
    simp only [hB', List.getElem_drop]
    have hs := (List.isChain_iff_getElem.1 hT'c) (t + 1 + i) (by omega)
    simp only [show t + 1 + (i + 1) = t + 1 + i + 1 from by omega]
    have hxy := hT'xy (t + 1 + i) (by omega)
    exact strandStep_swivelMove hpre' hd hs (hnxy _ hxy.1 fun h => by
      have := hxy.2 h
      omega)
  have hA'ne : A' ≠ [] := List.ne_nil_of_length_pos (by rw [hA'len]; omega)
  have hB'ne : B' ≠ [] := List.ne_nil_of_length_pos (by rw [hB'len]; omega)
  have hA'h : A'.head hA'ne = X.inv (k n) := by
    apply Option.some_injective
    rw [← List.head?_eq_some_head hA'ne, hA', List.head?_append, List.head?_eq_getElem?,
      List.getElem?_eq_getElem (by omega), hEget 0 (by omega), Nat.sub_zero]
    rfl
  have hB'h : B'.head hB'ne = T'[t + 1] := by
    apply Option.some_injective
    rw [← List.head?_eq_some_head hB'ne, hB', List.head?_drop, List.getElem?_eq_getElem]
  have hA'l : A'.getLast hA'ne = T[T.length - 1] := by
    apply Option.some_injective
    rw [← List.getLast?_eq_some_getLast hA'ne, hA',
      List.getLast?_append_of_ne_nil _ (by simp; omega), List.getLast?_drop, if_neg (by omega),
      List.getLast?_eq_getElem?, List.getElem?_eq_getElem]
  have hB'l : B'.getLast hB'ne = T'[T'.length - 1] := by
    apply Option.some_injective
    rw [← List.getLast?_eq_some_getLast hB'ne, hB', List.getLast?_drop, if_neg (by omega),
      List.getLast?_eq_getElem?, List.getElem?_eq_getElem]
  have hT't : X.vertexOf T'[t + 1] = u' := by
    rw [((List.isChain_iff_getElem.1 hT'c) t ht).vertexOf_eq, htv]
  have hTlx := hux
  have hT'u : X.vertexOf (X.inv T'[T'.length - 1]) ≠ x := hu ▸ hux
  have hT'uy : X.vertexOf (X.inv T'[T'.length - 1]) ≠ y := hu ▸ huy
  refine (hasParallelDigon_of_isChain hX'pre hA'ne hB'ne ?_ ?_ hA'c hB'c ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_)
  · intro e he
    change e ∉ X.bdry
    rcases List.mem_append.1 he with he | he
    · exact hEB e he
    · exact hTB e (List.mem_of_mem_drop he)
  · intro e he
    exact hT'B e (List.mem_of_mem_drop he)
  · rw [hA'h, hB'h]
    change X.isOut (X.inv (k n)) = X.isOut T'[t + 1]
    rw [hpre'.isOut_inv_apply (hkB n le_rfl), hkout n le_rfl]
    rw [isOut_getElem_of_isChain hpre' hT'B hT'c (t + 1) (by omega)]
    revert horient
    cases X.isOut k₁ <;> cases X.isOut T'[0] <;> simp
  · rw [hA'h, hB'h, hv' _ (by rw [← hu']; exact hu'x) (by rw [← hu']; exact hu'y),
      hv' _ (by rw [hT't]; exact hu'x) (by rw [hT't]; exact hu'y), hT't]
  · rw [hA'l, hB'l]
    change X'.vertexOf (X.inv T[T.length - 1]) = X'.vertexOf (X.inv T'[T'.length - 1])
    rw [hv' _ hux huy, hv' _ hT'u hT'uy, hu]
  · rw [hA'h, hbv']
    exact hu'int
  · rw [hA'l, hbv']
    exact huint
  · rw [hA'h, hA'l]
    change X'.vertexOf (X.inv (k n)) ≠ X'.vertexOf (X.inv T[T.length - 1])
    rw [hv' _ (by rw [← hu']; exact hu'x) (by rw [← hu']; exact hu'y), hv' _ hux huy]
    exact h4
  · rw [hA'h, hB'h]
    intro h
    exact hnC (h ▸ hT'CS _ (List.getElem_mem _))
  · rw [hA'l, hB'l]
    exact hlast

/-- **The escape from the closed walk**. Let `T, T'` be walks of `X` from the corner `x` of the
digon to a vertex `u ∉ {x, y}`, the closed walk `C` made of them having the darts `CS` (with their
reverses) and the vertices `CV`. Let `k₁` be a dart at `x` or `y`, followed in `X` by the walk
`pre ++ T` and in the swivel move by `T.drop r`, and let `k₁, …, k_n` be a walk leaving `C` through
`k₁` and coming back to it. Then the swivel move has a badgon. -/
private theorem hasBadgon_swivelMove_of_escape (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) (hmono : ¬X.HasMonogon)
    {T T' : List H} (hT0 : 0 < T.length) (hT'0 : 0 < T'.length)
    (hTB : ∀ e ∈ T, e ∉ X.bdry) (hT'B : ∀ e ∈ T', e ∉ X.bdry)
    (hTc : T.IsChain X.StrandStep) (hT'c : T'.IsChain X.StrandStep)
    (hu : X.vertexOf (X.inv T[T.length - 1]) = X.vertexOf (X.inv T'[T'.length - 1]))
    (huint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv T[T.length - 1])))
    (hux : X.vertexOf (X.inv T[T.length - 1]) ≠ X.vertexOf d₁)
    (huy : X.vertexOf (X.inv T[T.length - 1]) ≠ X.vertexOf (X.facePerm d₁))
    (hlast : T[T.length - 1] ≠ T'[T'.length - 1])
    {CS : H → Prop} (hCSinv : ∀ e, CS e → CS (X.inv e)) (hTCS : ∀ e ∈ T, CS e)
    (hT'CS : ∀ e ∈ T', CS e)
    {CV : Finset H → Prop}
    (hCV : ∀ z, CV z → z = X.vertexOf d₁ ∨ z = X.vertexOf (X.inv T[T.length - 1]) ∨
      (∃ t, ∃ _ : t + 1 < T.length, z = X.vertexOf (X.inv T[t])) ∨
      ∃ t, ∃ _ : t + 1 < T'.length, z = X.vertexOf (X.inv T'[t]))
    (hCVx : CV (X.vertexOf d₁)) (hCVy : CV (X.vertexOf (X.facePerm d₁)))
    {k₁ : H} {pre : List H} {r : ℕ}
    (hk₁v : X.vertexOf k₁ = X.vertexOf d₁ ∨ X.vertexOf k₁ = X.vertexOf (X.facePerm d₁))
    (hk₁L : k₁ ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H))
    (hpre : (pre = [] ∧ r = 1) ∨ ∃ ℓ, pre = [ℓ] ∧ r = 0 ∧
      ℓ ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) ∧
      X.StrandStep ℓ T[0])
    (hW₀ : ∀ w ∈ (pre ++ T).head?, (X.rot ^ 3) k₁ = w)
    (hr : r < T.length) (hR : ((X.swivelMove d₁).rot ^ 3) k₁ = T[r])
    (hmonoset : ∀ z, z = X.vertexOf d₁ ∨ z = X.vertexOf (X.facePerm d₁) →
      z = X.vertexOf k₁ ∨ (∃ ℓ, pre = [ℓ] ∧ z = X.vertexOf (X.inv ℓ)) ∨
        ∃ t, ∃ _ : t + 1 < T.length, z = X.vertexOf (X.inv T[t]))
    (hTxy : ∀ t, r ≤ t → ∀ (ht : t + 1 < T.length),
      X.vertexOf (X.inv T[t]) ≠ X.vertexOf d₁ ∧
        X.vertexOf (X.inv T[t]) ≠ X.vertexOf (X.facePerm d₁))
    (hT'xy : ∀ s (hs : s + 1 < T'.length), X.vertexOf (X.inv T'[s]) ≠ X.vertexOf d₁ ∧
      (X.vertexOf (X.inv T'[s]) = X.vertexOf (X.facePerm d₁) → s = 0))
    (horient : X.isOut k₁ ≠ X.isOut T'[0])
    {n : ℕ} {k : ℕ → H} (hk0 : k 0 = k₁)
    (hkstep : ∀ j < n, ¬X.IsBoundaryVertex (X.vertexOf (X.inv (k j))) ∧
      ¬CV (X.vertexOf (X.inv (k j))) ∧ k (j + 1) = (X.rot ^ 3) (X.inv (k j)))
    (hkend : CV (X.vertexOf (X.inv (k n)))) (hkC : ∀ j ≤ n, ¬CS (k j)) :
    (X.swivelMove d₁).HasBadgon := by
  have hpre' := hX.toIsPreTripleDiagram
  set x := X.vertexOf d₁ with hxdef
  set y := X.vertexOf (X.facePerm d₁) with hydef
  set Ls : Finset H := {d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} with hLs
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, -, -, hV₁, hV₂, hi₁, hi₂⟩ :=
    hd.exists_darts hpre'
  have hLv : ∀ e ∈ Ls, X.vertexOf e = x ∨ X.vertexOf e = y := by
    intro e he
    simp only [hLs, mem_insert, mem_singleton] at he
    rcases he with h | h | h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr (X.vertexOf_eq_of_mem (show X.inv d₁ ∈ X.vertexOf (X.facePerm d₁) by
        rw [hV₂]; simp))
    · exact Or.inr rfl
    · exact Or.inl (X.vertexOf_eq_of_mem (show X.inv (X.facePerm d₁) ∈ X.vertexOf d₁ by
        rw [hV₁]; simp))
  have hLinv : ∀ e ∈ Ls, X.inv e ∈ Ls := by
    intro e he
    simp only [hLs, mem_insert, mem_singleton] at he ⊢
    rcases he with h | h | h | h <;> rw [h] <;> simp [hpre'.inv_inv_apply]
  have hxyint : ∀ z, z = x ∨ z = y → ¬X.IsBoundaryVertex z := by
    rintro z (rfl | rfl)
    · exact hi₁
    · exact hi₂
  have hk₁int : ¬X.IsBoundaryVertex (X.vertexOf k₁) := hxyint _ hk₁v
  -- the reversed walk `k̄_n, …, k̄₀`
  obtain ⟨E, hElen, hEget, hEc, hEB, hkB, hkout, hElast⟩ := exists_reverse_walk hpre'
    (k := k) (n := n) (by rw [hk0]; exact fun h => hk₁int ⟨k₁, X.self_mem_vertexOf _, h⟩)
    (fun j hj => ⟨(hkstep j hj).1, (hkstep j hj).2.2⟩)
  rw [hk0] at hkout hElast
  -- `k̄_n` is neither a dart of `C` nor of the digon
  have hnC : ¬CS (X.inv (k n)) := fun h => hkC n le_rfl (by
    have := hCSinv _ h
    rwa [hpre'.inv_inv_apply] at this)
  have hnL : X.inv (k n) ∉ Ls := by
    intro h
    have h' := hLinv _ h
    rw [hpre'.inv_inv_apply] at h'
    rcases n with _ | m
    · rw [hk0] at h'
      exact hk₁L h'
    · have := (hkstep m (by omega))
      have hv : X.vertexOf (k (m + 1)) = X.vertexOf (X.inv (k m)) := by
        rw [this.2.2, X.vertexOf_rot_pow_apply]
      rcases hLv _ h' with h'' | h''
      · exact this.2.1 (hv ▸ h'' ▸ hCVx)
      · exact this.2.1 (hv ▸ h'' ▸ hCVy)
  -- the walk `W = k̄_n, …, k̄₀, pre, T` of `X`
  have hpreT : (pre ++ T).IsChain X.StrandStep := by
    rcases hpre with ⟨rfl, -⟩ | ⟨ℓ, rfl, -, -, hℓ⟩
    · simpa using hTc
    · obtain ⟨t, T₁, hT₁⟩ : ∃ t T₁, T = t :: T₁ := ⟨T[0], T.tail, by
        rcases T with _ | ⟨t, T₁⟩
        · simp at hT0
        · rfl⟩
      subst hT₁
      exact List.isChain_cons_cons.2 ⟨hℓ, hTc⟩
  have hpreTB : ∀ e ∈ pre ++ T, e ∉ X.bdry := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · rcases hpre with ⟨rfl, -⟩ | ⟨ℓ, rfl, -, hℓL, -⟩
      · simp at he
      · rw [List.mem_singleton] at he
        subst he
        intro h
        exact hxyint _ (hLv _ hℓL) ⟨_, X.self_mem_vertexOf _, h⟩
    · exact hTB e he
  set W := E ++ (pre ++ T) with hW
  have hWc : W.IsChain X.StrandStep := by
    rw [hW, List.isChain_append]
    refine ⟨hEc, hpreT, fun a ha c hc => ?_⟩
    rw [hElast, Option.mem_def, Option.some.injEq] at ha
    subst ha
    refine ⟨?_, ?_⟩
    · change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.inv k₁)))
      rw [hpre'.inv_inv_apply]
      exact hk₁int
    · rw [hpre'.inv_inv_apply]
      exact (hW₀ c hc).symm
  have hWB : ∀ e ∈ W, e ∉ X.bdry := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact hEB e he
    · exact hpreTB e he
  have hWlen : W.length = n + 1 + (pre.length + T.length) := by simp [hW, hElen]
  have hW0 : W[0]'(by omega) = X.inv (k n) := by
    rw [List.getElem_append_left (by omega), hEget 0 (by omega), Nat.sub_zero]
  have hWE : ∀ i (hi : i ≤ n), W[i]'(by omega) = X.inv (k (n - i)) := by
    intro i hi
    rw [List.getElem_append_left (by omega), hEget i (by omega)]
  have hWpT : ∀ m (hm : m < pre.length + T.length),
      W[n + 1 + m]'(by omega) = (pre ++ T)[m]'(by simp; omega) := by
    intro m hm
    rw [List.getElem_append_right (by omega)]
    congr 1
    omega
  set u' := X.vertexOf (X.inv (k n)) with hu'
  have hu'int : ¬X.IsBoundaryVertex u' := by
    rcases hCV _ hkend with h | h | ⟨t, ht, h⟩ | ⟨t, ht, h⟩
    · rw [h]
      exact hi₁
    · rw [h]
      exact huint
    · rw [h]
      exact ((List.isChain_iff_getElem.1 hTc) t ht).1
    · rw [h]
      exact ((List.isChain_iff_getElem.1 hT'c) t ht).1
  have hW0v : X.vertexOf (W[0]'(by omega)) = u' := by rw [hW0]
  have hW0int : ¬X.IsBoundaryVertex (X.vertexOf (W[0]'(by omega))) := by rw [hW0v]; exact hu'int
  have hrot3 : ∀ e, ¬X.IsBoundaryVertex (X.vertexOf e) → ∀ c, (X.rot ^ 3) c = e →
      c = (X.rot ^ 3) e := by
    intro e he c hc
    rw [← hc, hX.toIsPreTripleDiagram.rot_pow_three_rot_pow_three]
    rw [← X.vertexOf_rot_pow_apply 3, hc]
    exact he
  -- the monogon cases
  by_cases h1 : u' = X.vertexOf k₁
  · exfalso
    refine hmono (hasMonogon_of_segment hpre' hWB hWc (Nat.zero_le n) (by omega) hW0int ?_ ?_)
    · rw [hWE n le_rfl, Nat.sub_self, hpre'.inv_inv_apply, hk0, hW0v, h1]
    · rw [hWE n le_rfl, Nat.sub_self, hpre'.inv_inv_apply, hk0, hW0]
      intro h
      have h' := hrot3 _ hk₁int _ h.symm
      have hm : (pre ++ T)[0]'(by simp; omega) = (X.rot ^ 3) k₁ :=
        (hW₀ _ (List.head?_eq_getElem? ▸ List.getElem?_eq_getElem (by simp; omega))).symm
      rw [← hm] at h'
      rcases hpre with ⟨rfl, -⟩ | ⟨ℓ, rfl, -, hℓL, -⟩
      · simp only [List.nil_append] at h'
        exact hnC (h' ▸ hTCS _ (List.getElem_mem _))
      · simp only [List.singleton_append, List.getElem_cons_zero] at h'
        exact hnL (h' ▸ hℓL)
  by_cases h2 : ∃ ℓ, pre = [ℓ] ∧ u' = X.vertexOf (X.inv ℓ)
  · exfalso
    obtain ⟨ℓ, hpl, hℓv⟩ := h2
    have hℓs : X.StrandStep ℓ T[0] := by
      rcases hpre with ⟨h, -⟩ | ⟨ℓ', h, -, -, hℓ'⟩
      · rw [h] at hpl
        simp at hpl
      · rw [h] at hpl
        simp only [List.cons.injEq, and_true] at hpl
        exact hpl ▸ hℓ'
    have hpl' : pre.length = 1 := by rw [hpl]; rfl
    have hWℓ : W[n + 1 + 0]'(by omega) = ℓ := by
      rw [hWpT 0 (by omega)]
      simp [hpl]
    refine hmono (hasMonogon_of_segment hpre' hWB hWc (j := n + 1 + 0) (Nat.zero_le _)
      (by omega) hW0int ?_ ?_)
    · rw [hWℓ, hW0v, hℓv]
    · rw [hWℓ, hW0]
      intro h
      have h' := hrot3 _ (by rw [← hℓv]; exact hu'int) _ h.symm
      rw [← hℓs.2] at h'
      exact hnC (h' ▸ hTCS _ (List.getElem_mem _))
  by_cases h3 : ∃ t, ∃ _ : t + 1 < T.length, u' = X.vertexOf (X.inv T[t])
  · exfalso
    obtain ⟨t, ht, htv⟩ := h3
    have hWt : W[n + 1 + (pre.length + t)]'(by omega) = T[t] := by
      rw [hWpT _ (by omega), List.getElem_append_right (by omega)]
      congr 1
      omega
    refine hmono (hasMonogon_of_segment hpre' hWB hWc (j := n + 1 + (pre.length + t))
      (Nat.zero_le _) (by omega) hW0int ?_ ?_)
    · rw [hWt, hW0v, htv]
    · rw [hWt, hW0]
      intro h
      have hs := (List.isChain_iff_getElem.1 hTc) t ht
      have h' := hrot3 _ (by rw [← htv]; exact hu'int) _ h.symm
      rw [← hs.2] at h'
      exact hnC (h' ▸ hTCS _ (List.getElem_mem _))
  have hWl : W[W.length - 1]'(by omega) = T[T.length - 1] := by
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    congr 1
    omega
  by_cases h4 : u' = X.vertexOf (X.inv T[T.length - 1])
  · by_cases hp : X.inv T[T.length - 1] = (X.rot ^ 3) (X.inv (k n))
    · refine hasBadgon_swivelMove_of_cycle hX hd (K := W) (by omega) hWB hWc ?_ ?_
        (z := W[0]'(by omega)) (List.getElem_mem _) (by rw [hW0]; exact hnL)
      · rw [hWl]
        exact huint
      · rw [hWl, hp, hX.toIsPreTripleDiagram.rot_pow_three_rot_pow_three hu'int, hW0]
    · exfalso
      refine hmono (hasMonogon_of_segment hpre' hWB hWc (j := W.length - 1) (Nat.zero_le _)
        (by omega) hW0int ?_ ?_)
      · rw [hWl, hW0v, h4]
      · rw [hWl, hW0]
        exact hp
  -- the remaining case: a parallel digon of the swivel move
  have hnot : ∀ z, z = x ∨ z = y → u' ≠ z := by
    rintro z hz rfl
    rcases hmonoset _ hz with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  obtain ⟨t, ht, htv⟩ : ∃ t, ∃ _ : t + 1 < T'.length, u' = X.vertexOf (X.inv T'[t]) := by
    rcases hCV _ hkend with h | h | h | h
    · exact absurd h (hnot _ (Or.inl rfl))
    · exact absurd h h4
    · exact absurd h h3
    · exact h
  exact Or.inr (hasParallelDigon_swivelMove_of_escape hX hd hT0 hT'0 hTB hT'B hTc hT'c hu huint
    hux huy hlast hCSinv hT'CS hCVx hCVy hk₁v hr hR hTxy hT'xy horient hk0 hkstep hkC ht htv
    (hnot x (Or.inl rfl)) (hnot y (Or.inr rfl)) h4)

/-! ### The closed walk of two walks -/

private theorem val_finRotate' {n : ℕ} (j : Fin n) :
    (finRotate n j : ℕ) = if (j : ℕ) + 1 < n then (j : ℕ) + 1 else 0 := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : j = Fin.last n
    · simp [h]
    · have : (j : ℕ) < n := Fin.val_lt_last h
      simp only [h, if_false, show (j : ℕ) + 1 < n + 1 by omega, if_true]

omit [Fintype H] [DecidableEq H] in
private theorem get_eq_getLast' {L : List H} (hne : L ≠ []) (i : Fin L.length)
    (hi : ¬(i : ℕ) + 1 < L.length) : L.get i = L.getLast hne := by
  rw [List.getLast_eq_getElem, List.get_eq_getElem]
  congr 1
  omega

omit [Fintype H] [DecidableEq H] in
private theorem get_eq_head' {L : List H} (hne : L ≠ []) (i : Fin L.length) (hi : (i : ℕ) = 0) :
    L.get i = L.head hne := by
  rw [List.head_eq_getElem, List.get_eq_getElem]
  congr 1

/-- A nonempty list of darts, consecutive darts of which are linked without turning back, whose
last dart is linked to its first, and whose darts have pairwise distinct vertices, is a simple
closed walk. -/
private theorem isSimpleClosedWalk_get' {R : RotationSystem H} {L : List H} (hne : L ≠ [])
    (hchain : L.IsChain fun d d' => R.vertexOf (R.inv d) = R.vertexOf d' ∧ d' ≠ R.inv d)
    (hlast : R.vertexOf (R.inv (L.getLast hne)) = R.vertexOf (L.head hne))
    (hlast' : L.head hne ≠ R.inv (L.getLast hne))
    (hnodup : (L.map R.vertexOf).Nodup) : R.IsSimpleClosedWalk L.get := by
  have hc := List.isChain_iff_getElem.1 hchain
  have hrot : ∀ (i : Fin L.length) (hi : (i : ℕ) + 1 < L.length),
      L.get (finRotate L.length i) = L[(i : ℕ) + 1]'hi := fun i hi => by
    have := val_finRotate' i
    rw [if_pos hi] at this
    rw [show finRotate L.length i = ⟨i + 1, hi⟩ from Fin.ext this]
    rfl
  have hrot' : ∀ i : Fin L.length, ¬(i : ℕ) + 1 < L.length →
      L.get (finRotate L.length i) = L.head hne := fun i hi => by
    have := val_finRotate' i
    rw [if_neg hi] at this
    exact get_eq_head' hne _ this
  refine ⟨List.length_pos_iff.2 hne, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · by_cases hi : (i : ℕ) + 1 < L.length
    · rw [hrot i hi]
      exact (hc i hi).1
    · rw [hrot' i hi, get_eq_getLast' hne i hi]
      exact hlast
  · by_cases hi : (i : ℕ) + 1 < L.length
    · rw [hrot i hi]
      exact (hc i hi).2
    · rw [hrot' i hi, get_eq_getLast' hne i hi]
      exact hlast'
  · have := (hnodup.getElem_inj_iff (i := i) (j := j) (hi := by simp)
      (hj := by simp)).1 (by simpa [List.getElem_map] using hij)
    exact Fin.ext this

/-- **The closed walk of two walks.** Two walks `A, B` without common vertices other than their
common start `x` and their common end `u ≠ x`, each with pairwise distinct vertices, with distinct
first darts and distinct last darts, form the simple closed walk `A` followed by `B` read backwards
along the reverses. -/
private theorem isSimpleClosedWalk_of_walks (hX : X.IsPreTripleDiagram) {A B : List H}
    (hA0 : 0 < A.length) (hB0 : 0 < B.length)
    (hAc : A.IsChain X.StrandStep) (hBc : B.IsChain X.StrandStep)
    (hx : X.vertexOf A[0] = X.vertexOf B[0])
    (hu : X.vertexOf (X.inv A[A.length - 1]) = X.vertexOf (X.inv B[B.length - 1]))
    (hD1A : ∀ t (ht : t < A.length), X.vertexOf (X.inv A[t]) ≠ X.vertexOf A[0])
    (hD2A : ∀ s t (hs : s < t) (ht : t < A.length),
      X.vertexOf (X.inv (A[s]'(by omega))) ≠ X.vertexOf (X.inv A[t]))
    (hD1B : ∀ t (ht : t < B.length), X.vertexOf (X.inv B[t]) ≠ X.vertexOf B[0])
    (hD2B : ∀ s t (hs : s < t) (ht : t < B.length),
      X.vertexOf (X.inv (B[s]'(by omega))) ≠ X.vertexOf (X.inv B[t]))
    (hcross : ∀ s (hs : s + 1 < B.length) t (ht : t < A.length),
      X.vertexOf (X.inv B[s]) ≠ X.vertexOf (X.inv A[t]))
    (hhead : A[0] ≠ B[0]) (hlast : A[A.length - 1] ≠ B[B.length - 1]) :
    X.IsSimpleClosedWalk (A ++ B.reverse.map X.inv).get := by
  have hAg := List.isChain_iff_getElem.1 hAc
  have hBg := List.isChain_iff_getElem.1 hBc
  have hfix : ∀ e, ¬X.IsBoundaryVertex (X.vertexOf e) → (X.rot ^ 3) e ≠ e := fun e he h => by
    have := (hX.rot_pow_six he).2 3 0 (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hne : A ++ B.reverse.map X.inv ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  have hne' : B.reverse.map X.inv ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  -- the vertices of the darts of `A` and of `B` read backwards
  have hvA : ∀ s (hs : s + 1 < A.length), X.vertexOf A[s + 1] = X.vertexOf (X.inv A[s]) :=
    fun s hs => (hAg s hs).vertexOf_eq
  refine isSimpleClosedWalk_get' hne ?_ ?_ ?_ ?_
  · rw [List.isChain_append]
    refine ⟨?_, ?_, fun a ha c hc => ?_⟩
    · exact hAc.imp fun e e' h => ⟨h.vertexOf_eq.symm, by rw [h.2]; exact hfix _ h.1⟩
    · rw [List.isChain_map, List.isChain_reverse]
      refine hBc.imp fun e e' h => ⟨?_, ?_⟩
      · rw [hX.inv_inv_apply, h.vertexOf_eq]
      · rw [hX.inv_inv_apply, h.2]
        exact (hfix _ h.1).symm
    · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega),
        Option.mem_some_iff] at ha
      rw [List.head?_map, List.head?_reverse, List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega)] at hc
      simp only [Option.map_some, Option.mem_some_iff] at hc
      subst ha hc
      exact ⟨hu, fun h => hlast (X.inv.injective h).symm⟩
  · rw [List.getLast_append_of_ne_nil _ hne', List.getLast_map, List.getLast_reverse,
      List.head_append_of_ne_nil (List.ne_nil_of_length_pos hA0), hX.inv_inv_apply,
      List.head_eq_getElem, List.head_eq_getElem, hx]
  · rw [List.getLast_append_of_ne_nil _ hne', List.getLast_map, List.getLast_reverse,
      List.head_append_of_ne_nil (List.ne_nil_of_length_pos hA0), hX.inv_inv_apply,
      List.head_eq_getElem, List.head_eq_getElem]
    exact hhead
  · rw [List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_iff_getElem?_ne_getElem?]
      intro s t hst ht
      simp only [List.length_map] at ht
      rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem ht]
      simp only [Option.map_some, ne_eq, Option.some.injEq]
      obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rcases s with _ | s
      · rw [hvA t ht]
        exact fun h => hD1A t (by omega) h.symm
      · rw [hvA s (by omega), hvA t ht]
        exact hD2A s t (by omega) (by omega)
    · rw [List.map_map, List.map_reverse, List.nodup_reverse, List.nodup_iff_getElem?_ne_getElem?]
      intro s t hst ht
      simp only [List.length_map] at ht
      rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem ht]
      simp only [Option.map_some, ne_eq, Option.some.injEq, Function.comp_apply]
      exact hD2B s t hst ht
    · intro a ha c hc hac
      subst hac
      obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem ha
      simp only [List.map_map, List.mem_map, List.mem_reverse, Function.comp_apply] at hc
      obtain ⟨e, he, hev⟩ := hc
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
      simp only [List.length_map] at hs
      simp only [List.getElem_map] at hev
      by_cases ht' : t + 1 < B.length
      · rcases s with _ | s
        · exact hD1B t ht (hev.trans (hx ▸ rfl))
        · rw [hvA s hs] at hev
          exact hcross t ht' s (by omega) hev
      · have e1 : B[t] = B[B.length - 1] := by congr 1; omega
        rw [e1, ← hu] at hev
        rcases s with _ | s
        · exact hD1A _ (by omega) hev
        · rw [hvA s hs] at hev
          exact hD2A s (A.length - 1) (by omega) (by omega) hev.symm

omit [Fintype H] [DecidableEq H] in
/-- The darts of the closed walk of two walks, with their reverses. -/
private theorem mem_walks_iff {A B : List H} {e : H} (hinv : Function.Involutive X.inv) :
    (∃ i, e = (A ++ B.reverse.map X.inv).get i ∨ e = X.inv ((A ++ B.reverse.map X.inv).get i)) ↔
      e ∈ A ∨ e ∈ B ∨ X.inv e ∈ A ∨ X.inv e ∈ B := by
  have hmem : ∀ d, (∃ i, d = (A ++ B.reverse.map X.inv).get i) ↔ d ∈ A ∨ X.inv d ∈ B := by
    intro d
    constructor
    · rintro ⟨i, rfl⟩
      rcases List.mem_append.1 (List.get_mem _ i) with h | h
      · exact Or.inl h
      · obtain ⟨c, hc, hce⟩ := List.mem_map.1 h
        right
        rw [← hce, hinv]
        exact List.mem_reverse.1 hc
    · rintro (h | h)
      · obtain ⟨i, hi⟩ := List.get_of_mem (List.mem_append_left _ h)
        exact ⟨i, hi.symm⟩
      · obtain ⟨i, hi⟩ := List.get_of_mem (List.mem_append_right A (List.mem_map.2
          ⟨X.inv d, List.mem_reverse.2 h, hinv d⟩))
        exact ⟨i, hi.symm⟩
  constructor
  · rintro ⟨i, h | h⟩
    · rcases (hmem e).1 ⟨i, h⟩ with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inr h'))
    · have : X.inv e = (A ++ B.reverse.map X.inv).get i := by rw [h, hinv]
      rcases (hmem _).1 ⟨i, this⟩ with h' | h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · rw [hinv] at h'
        exact Or.inr (Or.inl h')
  · rintro (h | h | h | h)
    · obtain ⟨i, hi⟩ := (hmem e).2 (Or.inl h)
      exact ⟨i, Or.inl hi⟩
    · obtain ⟨i, hi⟩ := (hmem (X.inv e)).2 (Or.inr (by rwa [hinv]))
      exact ⟨i, Or.inr (by rw [← hi, hinv])⟩
    · obtain ⟨i, hi⟩ := (hmem (X.inv e)).2 (Or.inl h)
      exact ⟨i, Or.inr (by rw [← hi, hinv])⟩
    · obtain ⟨i, hi⟩ := (hmem e).2 (Or.inr h)
      exact ⟨i, Or.inl hi⟩

/-- The vertices of the closed walk of two walks. -/
private theorem exists_vertexOf_walks_iff {A B : List H} (hA0 : 0 < A.length)
    (hB0 : 0 < B.length) (hAc : A.IsChain X.StrandStep)
    (hu : X.vertexOf (X.inv A[A.length - 1]) = X.vertexOf (X.inv B[B.length - 1])) {z : Finset H} :
    (∃ i, z = X.vertexOf ((A ++ B.reverse.map X.inv).get i)) ↔
      z = X.vertexOf A[0] ∨ z = X.vertexOf (X.inv A[A.length - 1]) ∨
        (∃ t, ∃ _ : t + 1 < A.length, z = X.vertexOf (X.inv A[t])) ∨
        ∃ t, ∃ _ : t + 1 < B.length, z = X.vertexOf (X.inv B[t]) := by
  have hAg := List.isChain_iff_getElem.1 hAc
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    simp only [List.get_eq_getElem, List.length_append, List.length_map,
      List.length_reverse] at hi ⊢
    by_cases hiA : i < A.length
    · rw [List.getElem_append_left hiA]
      rcases i with _ | t
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨t, hiA, (hAg t hiA).vertexOf_eq⟩))
    · rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_map, List.getElem_reverse]
      by_cases hs : B.length - 1 - (i - A.length) + 1 < B.length
      · exact Or.inr (Or.inr (Or.inr ⟨B.length - 1 - (i - A.length), hs, rfl⟩))
      · refine Or.inr (Or.inl ?_)
        rw [hu]
        congr 3
        omega
  · rintro (rfl | rfl | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨⟨0, by simp; omega⟩, by simp [List.getElem_append_left hA0]⟩
    · refine ⟨⟨A.length, by simp; omega⟩, ?_⟩
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right le_rfl]
      simp only [Nat.sub_self, List.getElem_map, List.getElem_reverse, hu, Nat.sub_zero]
    · refine ⟨⟨t + 1, by simp; omega⟩, ?_⟩
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left ht, (hAg t ht).vertexOf_eq]
    · refine ⟨⟨A.length + (B.length - 1 - t), by simp; omega⟩, ?_⟩
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_map, List.getElem_reverse]
      congr 3
      simp
      omega

/-- **The escape** from the closed walk of two walks, through a dart `k₁` at one of its vertices on
which its winding function is nonzero. -/
private theorem exists_escape_of_walks (hX : X.IsTripleDiagram) {A B : List H}
    (hA0 : 0 < A.length) (hB0 : 0 < B.length) (hAc : A.IsChain X.StrandStep)
    (hu : X.vertexOf (X.inv A[A.length - 1]) = X.vertexOf (X.inv B[B.length - 1]))
    (hw : X.IsSimpleClosedWalk (A ++ B.reverse.map X.inv).get)
    (hint : ∀ i, ¬X.IsBoundaryVertex (X.vertexOf ((A ++ B.reverse.map X.inv).get i)))
    {h : X.faceOrbits → ℤ}
    (hh : X.IsWindingFunction (X.walkCycle (A ++ B.reverse.map X.inv).get) h) {k₁ : H}
    (hk₁ : X.vertexOf k₁ = X.vertexOf A[0] ∨ X.vertexOf k₁ = X.vertexOf (X.inv A[A.length - 1]) ∨
        (∃ t, ∃ _ : t + 1 < A.length, X.vertexOf k₁ = X.vertexOf (X.inv A[t])) ∨
        ∃ t, ∃ _ : t + 1 < B.length, X.vertexOf k₁ = X.vertexOf (X.inv B[t]))
    (hk₁C : ¬(k₁ ∈ A ∨ k₁ ∈ B ∨ X.inv k₁ ∈ A ∨ X.inv k₁ ∈ B))
    (hk₁h : h (X.toFaceOrbit k₁) ≠ 0) :
    ∃ (n : ℕ) (k : ℕ → H), k 0 = k₁ ∧
      (∀ j < n, ¬X.IsBoundaryVertex (X.vertexOf (X.inv (k j))) ∧
        ¬(X.vertexOf (X.inv (k j)) = X.vertexOf A[0] ∨
          X.vertexOf (X.inv (k j)) = X.vertexOf (X.inv A[A.length - 1]) ∨
          (∃ t, ∃ _ : t + 1 < A.length, X.vertexOf (X.inv (k j)) = X.vertexOf (X.inv A[t])) ∨
          ∃ t, ∃ _ : t + 1 < B.length, X.vertexOf (X.inv (k j)) = X.vertexOf (X.inv B[t])) ∧
        k (j + 1) = (X.rot ^ 3) (X.inv (k j))) ∧
      (X.vertexOf (X.inv (k n)) = X.vertexOf A[0] ∨
        X.vertexOf (X.inv (k n)) = X.vertexOf (X.inv A[A.length - 1]) ∨
        (∃ t, ∃ _ : t + 1 < A.length, X.vertexOf (X.inv (k n)) = X.vertexOf (X.inv A[t])) ∨
        ∃ t, ∃ _ : t + 1 < B.length, X.vertexOf (X.inv (k n)) = X.vertexOf (X.inv B[t])) ∧
      ∀ j ≤ n, ¬(k j ∈ A ∨ k j ∈ B ∨ X.inv (k j) ∈ A ∨ X.inv (k j) ∈ B) := by
  have hinv := hX.inv_involutive
  have hV := fun z => exists_vertexOf_walks_iff (z := z) hA0 hB0 hAc hu
  obtain ⟨i₀, hi₀⟩ := (hV _).2 hk₁
  obtain ⟨n, k, hk0, hstep, ⟨i, hi⟩, hC⟩ := DiskMap.IsWindingFunction.exists_walk_escape
    hX.toIsDiskMap hw hint hh hk₁h ⟨i₀, hi₀⟩
    (fun i => ⟨fun h' => hk₁C ((mem_walks_iff hinv).1 ⟨i, Or.inl h'⟩),
      fun h' => hk₁C ((mem_walks_iff hinv).1 ⟨i, Or.inr h'⟩)⟩) rfl
  refine ⟨n, k, hk0, fun j hj => ⟨(hstep j hj).1, fun h' => ?_, (hstep j hj).2.2⟩,
    (hV _).1 ⟨i, hi⟩, fun j hj h' => ?_⟩
  · obtain ⟨i', hi'⟩ := (hV _).2 h'
    exact (hstep j hj).2.1 i' hi'
  · obtain ⟨i', hi'⟩ := (mem_walks_iff hinv).2 h'
    rcases hi' with hi' | hi'
    · exact (hC j hj).1 i' |>.1 hi'
    · exact (hC j hj).1 i' |>.2 hi'

/-- The cycle of a simple closed walk vanishes at a dart of the vertex `v(cᵢ)` other than `cᵢ` and
`c̄ᵢ₋₁`; such a dart is neither a dart of the walk nor the reverse of one. -/
private theorem walkCycle_eq_zero_of_vertexOf (hinv : Function.Involutive X.inv) {L : ℕ}
    {w : Fin L → H} (hw : X.IsSimpleClosedWalk w) {i j : Fin L} (hij : finRotate L j = i) {z : H}
    (hz : X.vertexOf z = X.vertexOf (w i)) (h1 : z ≠ w i) (h2 : z ≠ X.inv (w j)) :
    X.walkCycle w z = 0 ∧ ∀ i', z ≠ w i' ∧ z ≠ X.inv (w i') := by
  have key : ∀ i', z ≠ w i' ∧ z ≠ X.inv (w i') := by
    intro i'
    refine ⟨fun h => h1 ?_, fun h => h2 ?_⟩
    · have : i' = i := hw.injective_vertexOf (by simp only; rw [← h, hz])
      rw [h, this]
    · have : i' = j := hw.eq_of_vertexOf_inv_eq (i := j) (by rw [← h, hz, hij])
      rw [h, this]
  exact ⟨RotationSystem.walkCycle_eq_zero hinv (fun i' => (key i').1) fun i' => (key i').2, key⟩

private theorem finRotate_last {L : ℕ} (hL : 0 < L) :
    finRotate L ⟨L - 1, by omega⟩ = ⟨0, hL⟩ := by
  apply Fin.ext
  rw [val_finRotate']
  simp
  omega

private theorem finRotate_of_lt {L : ℕ} {i : ℕ} (hi : i + 1 < L) :
    finRotate L ⟨i, by omega⟩ = ⟨i + 1, hi⟩ := by
  apply Fin.ext
  rw [val_finRotate']
  simp [hi]

/-- The escape from the closed walk of two walks `A, B`, continuing along `T ∈ {A, B}`, with `T'`
the other one: the hypotheses of `hasBadgon_swivelMove_of_escape`, the escape walk being provided
by `exists_escape_of_walks`. The flag `swap` says whether `T = B`. -/
private theorem hasBadgon_swivelMove_of_walks (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) (hmono : ¬X.HasMonogon) {A B : List H}
    (hA0 : 0 < A.length) (hB0 : 0 < B.length)
    (hAB : ∀ e ∈ A, e ∉ X.bdry) (hBB : ∀ e ∈ B, e ∉ X.bdry)
    (hAc : A.IsChain X.StrandStep) (hBc : B.IsChain X.StrandStep)
    (hvA0 : X.vertexOf A[0] = X.vertexOf d₁)
    (hu : X.vertexOf (X.inv A[A.length - 1]) = X.vertexOf (X.inv B[B.length - 1]))
    (huint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv A[A.length - 1])))
    (hux : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf d₁)
    (huy : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf (X.facePerm d₁))
    (hlast : A[A.length - 1] ≠ B[B.length - 1])
    (hw : X.IsSimpleClosedWalk (A ++ B.reverse.map X.inv).get)
    (hint : ∀ i, ¬X.IsBoundaryVertex (X.vertexOf ((A ++ B.reverse.map X.inv).get i)))
    {h : X.faceOrbits → ℤ}
    (hh : X.IsWindingFunction (X.walkCycle (A ++ B.reverse.map X.inv).get) h)
    (hCVy : X.vertexOf (X.facePerm d₁) = X.vertexOf A[0] ∨
      X.vertexOf (X.facePerm d₁) = X.vertexOf (X.inv A[A.length - 1]) ∨
      (∃ t, ∃ _ : t + 1 < A.length, X.vertexOf (X.facePerm d₁) = X.vertexOf (X.inv A[t])) ∨
      ∃ t, ∃ _ : t + 1 < B.length, X.vertexOf (X.facePerm d₁) = X.vertexOf (X.inv B[t]))
    {k₁ : H} (hk₁v : X.vertexOf k₁ = X.vertexOf d₁ ∨ X.vertexOf k₁ = X.vertexOf (X.facePerm d₁))
    (hk₁C : ∀ i, k₁ ≠ (A ++ B.reverse.map X.inv).get i ∧
      k₁ ≠ X.inv ((A ++ B.reverse.map X.inv).get i))
    (hk₁h : h (X.toFaceOrbit k₁) ≠ 0)
    (hk₁L : k₁ ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H))
    (swap : Bool) {pre : List H} {r : ℕ}
    (hpre : (pre = [] ∧ r = 1) ∨ ∃ ℓ, pre = [ℓ] ∧ r = 0 ∧
      ℓ ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) ∧
      X.StrandStep ℓ ((if swap then B else A)[0]'(by cases swap <;> simpa)))
    (hW₀ : ∀ w ∈ (pre ++ if swap then B else A).head?, (X.rot ^ 3) k₁ = w)
    (hr : r < (if swap then B else A).length)
    (hR : ((X.swivelMove d₁).rot ^ 3) k₁ = (if swap then B else A)[r])
    (hmonoset : ∀ z, z = X.vertexOf d₁ ∨ z = X.vertexOf (X.facePerm d₁) →
      z = X.vertexOf k₁ ∨ (∃ ℓ, pre = [ℓ] ∧ z = X.vertexOf (X.inv ℓ)) ∨
        ∃ t, ∃ _ : t + 1 < (if swap then B else A).length,
          z = X.vertexOf (X.inv ((if swap then B else A)[t])))
    (hTxy : ∀ t, r ≤ t → ∀ (ht : t + 1 < (if swap then B else A).length),
      X.vertexOf (X.inv ((if swap then B else A)[t])) ≠ X.vertexOf d₁ ∧
        X.vertexOf (X.inv ((if swap then B else A)[t])) ≠ X.vertexOf (X.facePerm d₁))
    (hT'xy : ∀ s (hs : s + 1 < (if swap then A else B).length),
      X.vertexOf (X.inv ((if swap then A else B)[s])) ≠ X.vertexOf d₁ ∧
      (X.vertexOf (X.inv ((if swap then A else B)[s])) = X.vertexOf (X.facePerm d₁) → s = 0))
    (horient : X.isOut k₁ ≠ X.isOut ((if swap then A else B)[0]'(by cases swap <;> simpa))) :
    (X.swivelMove d₁).HasBadgon := by
  have hinv := hX.inv_involutive
  have hk₁pos : X.vertexOf k₁ = X.vertexOf A[0] ∨
      X.vertexOf k₁ = X.vertexOf (X.inv A[A.length - 1]) ∨
      (∃ t, ∃ _ : t + 1 < A.length, X.vertexOf k₁ = X.vertexOf (X.inv A[t])) ∨
      ∃ t, ∃ _ : t + 1 < B.length, X.vertexOf k₁ = X.vertexOf (X.inv B[t]) := by
    rcases hk₁v with h' | h'
    · exact Or.inl (h'.trans hvA0.symm)
    · exact h' ▸ hCVy
  have hk₁C' : ¬(k₁ ∈ A ∨ k₁ ∈ B ∨ X.inv k₁ ∈ A ∨ X.inv k₁ ∈ B) := fun h' => by
    obtain ⟨i, hi⟩ := (mem_walks_iff hinv).2 h'
    rcases hi with hi | hi
    · exact (hk₁C i).1 hi
    · exact (hk₁C i).2 hi
  obtain ⟨n, k, hk0, hkstep, hkend, hkC⟩ :=
    exists_escape_of_walks hX hA0 hB0 hAc hu hw hint hh hk₁pos hk₁C' hk₁h
  have hCS : ∀ e, (e ∈ A ∨ e ∈ B ∨ X.inv e ∈ A ∨ X.inv e ∈ B) →
      (X.inv e ∈ A ∨ X.inv e ∈ B ∨ X.inv (X.inv e) ∈ A ∨ X.inv (X.inv e) ∈ B) := by
    intro e he
    rw [hinv]
    rcases he with h' | h' | h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  have hCVx : X.vertexOf d₁ = X.vertexOf A[0] ∨
      X.vertexOf d₁ = X.vertexOf (X.inv A[A.length - 1]) ∨
      (∃ t, ∃ _ : t + 1 < A.length, X.vertexOf d₁ = X.vertexOf (X.inv A[t])) ∨
      ∃ t, ∃ _ : t + 1 < B.length, X.vertexOf d₁ = X.vertexOf (X.inv B[t]) :=
    Or.inl hvA0.symm
  cases swap with
  | false =>
    exact hasBadgon_swivelMove_of_escape hX hd hmono (T := A) (T' := B) hA0 hB0 hAB hBB hAc hBc hu
      huint hux huy hlast (CS := fun e => e ∈ A ∨ e ∈ B ∨ X.inv e ∈ A ∨ X.inv e ∈ B) hCS
      (fun e he => Or.inl he) (fun e he => Or.inr (Or.inl he))
      (CV := fun z => z = X.vertexOf A[0] ∨ z = X.vertexOf (X.inv A[A.length - 1]) ∨
        (∃ t, ∃ _ : t + 1 < A.length, z = X.vertexOf (X.inv A[t])) ∨
        ∃ t, ∃ _ : t + 1 < B.length, z = X.vertexOf (X.inv B[t]))
      (fun z hz => by
        rcases hz with h' | h'
        · exact Or.inl (h'.trans hvA0)
        · exact Or.inr h') hCVx hCVy hk₁v hk₁L hpre hW₀ hr hR hmonoset hTxy hT'xy horient hk0
      hkstep hkend hkC
  | true =>
    exact hasBadgon_swivelMove_of_escape hX hd hmono (T := B) (T' := A) hB0 hA0 hBB hAB hBc hAc
      hu.symm (by rw [← hu]; exact huint) (by rw [← hu]; exact hux) (by rw [← hu]; exact huy)
      (Ne.symm hlast) (CS := fun e => e ∈ A ∨ e ∈ B ∨ X.inv e ∈ A ∨ X.inv e ∈ B) hCS
      (fun e he => Or.inr (Or.inl he)) (fun e he => Or.inl he)
      (CV := fun z => z = X.vertexOf A[0] ∨ z = X.vertexOf (X.inv A[A.length - 1]) ∨
        (∃ t, ∃ _ : t + 1 < A.length, z = X.vertexOf (X.inv A[t])) ∨
        ∃ t, ∃ _ : t + 1 < B.length, z = X.vertexOf (X.inv B[t]))
      (fun z hz => by
        rcases hz with h' | h' | h' | h'
        · exact Or.inl (h'.trans hvA0)
        · exact Or.inr (Or.inl (h'.trans hu))
        · exact Or.inr (Or.inr (Or.inr h'))
        · exact Or.inr (Or.inr (Or.inl h'))) hCVx hCVy hk₁v hk₁L hpre hW₀ hr hR hmonoset hTxy
      hT'xy horient hk0 hkstep hkend hkC

/-- The closed walk of configuration I and its winding function: `h(f(b₃)) = h(f(a₃)) + 1`, and
neither `a₃` nor `b₃` is a dart of the walk or the reverse of one. -/
private theorem winding_walks_one (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {A B : List H}
    (hA1 : 1 < A.length) (hB0 : 0 < B.length)
    (hAc : A.IsChain X.StrandStep) (hBc : B.IsChain X.StrandStep)
    (hA0 : A[0] = d₁) (hB0d : B[0] = (X.rot ^ 2) d₁)
    (hu : X.vertexOf (X.inv A[A.length - 1]) = X.vertexOf (X.inv B[B.length - 1]))
    (huint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv A[A.length - 1])))
    (hD1A : ∀ t (ht : t < A.length), X.vertexOf (X.inv A[t]) ≠ X.vertexOf A[0])
    (hD2A : ∀ s t (hs : s < t) (ht : t < A.length),
      X.vertexOf (X.inv (A[s]'(by omega))) ≠ X.vertexOf (X.inv A[t]))
    (hD1B : ∀ t (ht : t < B.length), X.vertexOf (X.inv B[t]) ≠ X.vertexOf B[0])
    (hD2B : ∀ s t (hs : s < t) (ht : t < B.length),
      X.vertexOf (X.inv (B[s]'(by omega))) ≠ X.vertexOf (X.inv B[t]))
    (hcross : ∀ s (hs : s + 1 < B.length) t (ht : t < A.length),
      X.vertexOf (X.inv B[s]) ≠ X.vertexOf (X.inv A[t]))
    (hlast : A[A.length - 1] ≠ B[B.length - 1]) :
    X.IsSimpleClosedWalk (A ++ B.reverse.map X.inv).get ∧
      (∀ i, ¬X.IsBoundaryVertex (X.vertexOf ((A ++ B.reverse.map X.inv).get i))) ∧
      ∃ h : X.faceOrbits → ℤ, X.IsWindingFunction (X.walkCycle (A ++ B.reverse.map X.inv).get) h ∧
        h (X.toFaceOrbit ((X.rot ^ 3) (X.facePerm d₁))) = h (X.toFaceOrbit ((X.rot ^ 3) d₁)) + 1 ∧
        (∀ i, (X.rot ^ 3) d₁ ≠ (A ++ B.reverse.map X.inv).get i ∧
          (X.rot ^ 3) d₁ ≠ X.inv ((A ++ B.reverse.map X.inv).get i)) ∧
        (∀ i, (X.rot ^ 3) (X.facePerm d₁) ≠ (A ++ B.reverse.map X.inv).get i ∧
          (X.rot ^ 3) (X.facePerm d₁) ≠ X.inv ((A ++ B.reverse.map X.inv).get i)) := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -, -⟩ := hd.exists_swivel hpre
  have hφφ : X.rot (X.inv (X.facePerm d₁)) = d₁ := hd.facePerm_facePerm
  have hφ : X.rot (X.inv d₁) = X.facePerm d₁ := rfl
  have hfφ : X.toFaceOrbit (X.facePerm d₁) = X.toFaceOrbit d₁ := X.toFaceOrbit_facePerm d₁
  have ha₂ : (X.rot ^ 2) d₁ = a₂ := by rw [pow_two, Equiv.Perm.mul_apply, h1, h2]
  rw [ha₂] at hB0d
  have hne : ∀ i j (hi : i < 12) (hj : j < 12), i ≠ j →
      [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][i] ≠
        [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][j] :=
    fun i j hi hj hij h => hij ((hnd.getElem_inj_iff (hi := by simpa using hi)
      (hj := by simpa using hj)).1 h)
  set d₂ := X.facePerm d₁ with hd₂
  have hvx : ∀ z ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H), X.vertexOf z = X.vertexOf d₁ :=
    fun z hz => X.vertexOf_eq_of_mem (by rw [hV₁]; exact hz)
  have hvy : ∀ z ∈ ({d₂, b₁, b₂, b₃, b₄, X.inv d₁} : Finset H), X.vertexOf z = X.vertexOf d₂ :=
    fun z hz => X.vertexOf_eq_of_mem (by rw [hV₂]; exact hz)
  have hA1d : A[1] = b₂ := by
    rw [((List.isChain_iff_getElem.1 hAc) 0 hA1).2, hA0, X.rot_pow_three_apply, hφ, g1, g2]
  have hx : X.vertexOf A[0] = X.vertexOf B[0] := by rw [hA0, hB0d, hvx a₂ (by simp)]
  have hw := isSimpleClosedWalk_of_walks hpre (by omega) hB0 hAc hBc hx hu hD1A hD2A hD1B hD2B
    hcross (by rw [hA0, hB0d]; exact (hne 0 2 (by norm_num) (by norm_num) (by norm_num))) hlast
  set C := A ++ B.reverse.map X.inv with hC
  have hCl : C.length = A.length + B.length := by simp [hC]
  have hV := fun z => exists_vertexOf_walks_iff (z := z) (by omega) hB0 hAc hu
  have hint : ∀ i, ¬X.IsBoundaryVertex (X.vertexOf (C.get i)) := by
    intro i
    rcases (hV _).1 ⟨i, rfl⟩ with h | h | ⟨t, ht, h⟩ | ⟨t, ht, h⟩ <;> rw [h]
    · rw [hA0]
      exact hi₁
    · exact huint
    · exact ((List.isChain_iff_getElem.1 hAc) t ht).1
    · exact ((List.isChain_iff_getElem.1 hBc) t ht).1
  obtain ⟨h, hh, -⟩ := hX.toIsDiskMap.existsUnique_isWindingFunction_walkCycle hw
  have hC0 : C.get ⟨0, by omega⟩ = d₁ := by
    simp only [List.get_eq_getElem, hC]
    rw [List.getElem_append_left (by omega), hA0]
  have hC1 : C.get ⟨1, by omega⟩ = b₂ := by
    simp only [List.get_eq_getElem, hC]
    rw [List.getElem_append_left hA1, hA1d]
  have hCl1 : C.get ⟨C.length - 1, by omega⟩ = X.inv a₂ := by
    simp only [List.get_eq_getElem, hC]
    rw [List.getElem_append_right (by simp [hC] at hCl ⊢; omega)]
    simp only [List.getElem_map, List.getElem_reverse]
    rw [← hB0d]
    congr 2
    simp [hC] at hCl ⊢
    omega
  -- the cycle of `C` around `x` and `y`
  have cx : ∀ z, X.vertexOf z = X.vertexOf d₁ → z ≠ d₁ → z ≠ a₂ →
      X.walkCycle C.get z = 0 ∧ ∀ i, z ≠ C.get i ∧ z ≠ X.inv (C.get i) := fun z hz h1' h2' =>
    walkCycle_eq_zero_of_vertexOf hinv hw (finRotate_last (by omega))
      (by rw [hC0]; exact hz) (by rw [hC0]; exact h1') (by rw [hCl1, hinv]; exact h2')
  have cy : ∀ z, X.vertexOf z = X.vertexOf d₂ → z ≠ b₂ → z ≠ X.inv d₁ →
      X.walkCycle C.get z = 0 ∧ ∀ i, z ≠ C.get i ∧ z ≠ X.inv (C.get i) := fun z hz h1' h2' =>
    walkCycle_eq_zero_of_vertexOf hinv hw (finRotate_of_lt (i := 0) (L := C.length) (by omega))
      (by rw [hC1, hvy b₂ (by simp)]; exact hz) (by rw [hC1]; exact h1')
      (by rw [hC0]; exact h2')
  have ca₃ := cx a₃ (hvx _ (by simp)) (hne 3 0 (by norm_num) (by norm_num) (by norm_num))
    (hne 3 2 (by norm_num) (by norm_num) (by norm_num))
  have ca₄ := cx a₄ (hvx _ (by simp)) (hne 4 0 (by norm_num) (by norm_num) (by norm_num))
    (hne 4 2 (by norm_num) (by norm_num) (by norm_num))
  have cd₂' := cx (X.inv d₂) (hvx _ (by simp)) (hne 5 0 (by norm_num) (by norm_num) (by norm_num))
    (hne 5 2 (by norm_num) (by norm_num) (by norm_num))
  have cd₂ := cy d₂ rfl (hne 6 8 (by norm_num) (by norm_num) (by norm_num))
    (hne 6 11 (by norm_num) (by norm_num) (by norm_num))
  have cb₁ := cy b₁ (hvy _ (by simp)) (hne 7 8 (by norm_num) (by norm_num) (by norm_num))
    (hne 7 11 (by norm_num) (by norm_num) (by norm_num))
  have cb₃ := cy b₃ (hvy _ (by simp)) (hne 9 8 (by norm_num) (by norm_num) (by norm_num))
    (hne 9 11 (by norm_num) (by norm_num) (by norm_num))
  have cb₂ : X.walkCycle C.get b₂ = 1 := by rw [← hC1]; exact hw.walkCycle_apply_self _
  -- the rotation rule
  have r1 := hh.apply_rot hinv a₃
  rw [h4, ca₃.1, add_zero] at r1
  have r2 := hh.apply_rot hinv a₄
  rw [h5, ca₄.1, add_zero, r1] at r2
  have r3 := hh.apply_rot hinv (X.inv d₂)
  rw [hφφ, cd₂'.1, add_zero, r2] at r3
  have r4 := hh.apply_rot hinv d₂
  rw [g1, cd₂.1, add_zero, hfφ, r3] at r4
  have r5 := hh.apply_rot hinv b₁
  rw [g2, cb₁.1, add_zero, r4] at r5
  have r6 := hh.apply_rot hinv b₂
  rw [g3, cb₂, r5] at r6
  have ha₃ : (X.rot ^ 3) d₁ = a₃ := by rw [X.rot_pow_three_apply, h1, h2, h3]
  have hb₃ : (X.rot ^ 3) d₂ = b₃ := by rw [X.rot_pow_three_apply, g1, g2, g3]
  refine ⟨hw, hint, h, hh, ?_, ?_, ?_⟩
  · rw [ha₃, hb₃, r6]
  · rw [ha₃]
    exact ca₃.2
  · rw [hb₃]
    exact cb₃.2

/-- **Configuration I**: two walks from the corner `x` of the digon to a common vertex
`u ∉ {x, y}`, leaving `x` along `d₁` and along `a₂`, with no other common vertex, the second one
avoiding `y`. Then the swivel move has a badgon. -/
private theorem hasBadgon_swivelMove_of_walks_one (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) (hmono : ¬X.HasMonogon) {A B : List H}
    (hA1 : 1 < A.length) (hB0 : 0 < B.length)
    (hAB : ∀ e ∈ A, e ∉ X.bdry) (hBB : ∀ e ∈ B, e ∉ X.bdry)
    (hAc : A.IsChain X.StrandStep) (hBc : B.IsChain X.StrandStep)
    (hA0 : A[0] = d₁) (hB0d : B[0] = (X.rot ^ 2) d₁)
    (hu : X.vertexOf (X.inv A[A.length - 1]) = X.vertexOf (X.inv B[B.length - 1]))
    (huint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv A[A.length - 1])))
    (hux : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf d₁)
    (huy : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf (X.facePerm d₁))
    (hD1A : ∀ t (ht : t < A.length), X.vertexOf (X.inv A[t]) ≠ X.vertexOf A[0])
    (hD2A : ∀ s t (hs : s < t) (ht : t < A.length),
      X.vertexOf (X.inv (A[s]'(by omega))) ≠ X.vertexOf (X.inv A[t]))
    (hD1B : ∀ t (ht : t < B.length), X.vertexOf (X.inv B[t]) ≠ X.vertexOf B[0])
    (hD2B : ∀ s t (hs : s < t) (ht : t < B.length),
      X.vertexOf (X.inv (B[s]'(by omega))) ≠ X.vertexOf (X.inv B[t]))
    (hcross : ∀ s (hs : s + 1 < B.length) t (ht : t < A.length),
      X.vertexOf (X.inv B[s]) ≠ X.vertexOf (X.inv A[t]))
    (hBy : ∀ t (ht : t < B.length), X.vertexOf (X.inv B[t]) ≠ X.vertexOf (X.facePerm d₁))
    (hlast : A[A.length - 1] ≠ B[B.length - 1]) :
    (X.swivelMove d₁).HasBadgon := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  obtain ⟨hw, hint, h, hh, r6, ca₃, cb₃⟩ := winding_walks_one hX hd hA1 hB0 hAc hBc hA0 hB0d hu
    huint hD1A hD2A hD1B hD2B hcross hlast
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -, -⟩ := hd.exists_swivel hpre
  have hφφ : X.rot (X.inv (X.facePerm d₁)) = d₁ := hd.facePerm_facePerm
  have hφ : X.rot (X.inv d₁) = X.facePerm d₁ := rfl
  have ha₂ : (X.rot ^ 2) d₁ = a₂ := by rw [pow_two, Equiv.Perm.mul_apply, h1, h2]
  have ha₃ : (X.rot ^ 3) d₁ = a₃ := by rw [X.rot_pow_three_apply, h1, h2, h3]
  have hb₃ : (X.rot ^ 3) (X.facePerm d₁) = b₃ := by rw [X.rot_pow_three_apply, g1, g2, g3]
  rw [ha₂] at hB0d
  rw [ha₃, hb₃] at r6
  rw [ha₃] at ca₃
  rw [hb₃] at cb₃
  have hne : ∀ i j (hi : i < 12) (hj : j < 12), i ≠ j →
      [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][i] ≠
        [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][j] :=
    fun i j hi hj hij h => hij ((hnd.getElem_inj_iff (hi := by simpa using hi)
      (hj := by simpa using hj)).1 h)
  set d₂ := X.facePerm d₁ with hd₂
  have hvx : ∀ z ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H), X.vertexOf z = X.vertexOf d₁ :=
    fun z hz => X.vertexOf_eq_of_mem (by rw [hV₁]; exact hz)
  have hvy : ∀ z ∈ ({d₂, b₁, b₂, b₃, b₄, X.inv d₁} : Finset H), X.vertexOf z = X.vertexOf d₂ :=
    fun z hz => X.vertexOf_eq_of_mem (by rw [hV₂]; exact hz)
  have hA1d : A[1] = b₂ := by
    rw [((List.isChain_iff_getElem.1 hAc) 0 hA1).2, hA0, X.rot_pow_three_apply, hφ, g1, g2]
  have hyA : X.vertexOf (X.inv A[0]) = X.vertexOf d₂ := by
    rw [hA0]
    exact hvy _ (by simp)
  have hR3 : ∀ z, ((X.swivelMove d₁).rot ^ 3) z =
      X.swivelRot d₁ (X.swivelRot d₁ (X.swivelRot d₁ z)) := fun z => rfl
  have hvB0 : X.vertexOf B[0] = X.vertexOf d₁ := by rw [hB0d]; exact hvx _ (by simp)
  have hvA0 : X.vertexOf A[0] = X.vertexOf d₁ := by rw [hA0]
  have hCVy : X.vertexOf d₂ = X.vertexOf A[0] ∨
      X.vertexOf d₂ = X.vertexOf (X.inv A[A.length - 1]) ∨
      (∃ t, ∃ _ : t + 1 < A.length, X.vertexOf d₂ = X.vertexOf (X.inv A[t])) ∨
      ∃ t, ∃ _ : t + 1 < B.length, X.vertexOf d₂ = X.vertexOf (X.inv B[t]) :=
    Or.inr (Or.inr (Or.inl ⟨0, hA1, hyA.symm⟩))
  by_cases ha : h (X.toFaceOrbit a₃) = 0
  · -- case Ib: escape through `b₃`, continuing along `d₂` and `B`
    have hb₃out : X.isOut b₃ ≠ X.isOut d₁ := by
      have e3 : b₃ = (X.rot ^ 3) d₂ := by rw [X.rot_pow_three_apply, g1, g2, g3]
      have e1 : d₂ = X.rot (X.inv d₁) := hφ.symm
      rw [e3, hpre.isOut_rot_pow_three_apply hi₂, e1,
        hpre.isOut_rot_apply (by rw [hvy _ (by simp)]; exact hi₂),
        hpre.isOut_inv_apply (hd.notMem_bdry.1)]
      cases X.isOut d₁ <;> simp
    refine hasBadgon_swivelMove_of_walks hX hd hmono (by omega) hB0 hAB hBB hAc hBc hvA0 hu huint
      hux huy hlast hw hint hh hCVy (k₁ := b₃) (Or.inr (hvy _ (by simp))) cb₃
      (by rw [r6, ha]; norm_num)
      (by simp only [mem_insert, mem_singleton, not_or]
          exact ⟨hne 9 0 (by norm_num) (by norm_num) (by norm_num),
            hne 9 11 (by norm_num) (by norm_num) (by norm_num),
            hne 9 6 (by norm_num) (by norm_num) (by norm_num),
            hne 9 5 (by norm_num) (by norm_num) (by norm_num)⟩)
      true (pre := [d₂]) (r := 0)
      (Or.inr ⟨d₂, rfl, rfl, by
          simp only [mem_insert, mem_singleton]
          exact Or.inr (Or.inr (Or.inl rfl)), ⟨by
          change ¬X.IsBoundaryVertex (X.vertexOf (X.inv d₂))
          rw [hvx _ (by simp)]
          exact hi₁, by
          change B[0] = (X.rot ^ 3) (X.inv d₂)
          rw [hB0d, X.rot_pow_three_apply, hφφ, h1, h2]⟩⟩)
      (fun w hw' => by
        simp only [if_true, List.singleton_append, List.head?_cons, Option.mem_def,
          Option.some.injEq] at hw'
        rw [← hw', X.rot_pow_three_apply, g4, g5, hφ])
      hB0 (by rw [hR3, s9, s10, s11]; exact hB0d.symm)
      (fun z hz => by
        rcases hz with rfl | rfl
        · exact Or.inr (Or.inl ⟨d₂, rfl, (hvx _ (by simp)).symm⟩)
        · exact Or.inl (hvy _ (by simp)).symm)
      (fun t _ ht => ⟨by rw [← hvB0]; exact hD1B t (by simp at ht; omega),
        hBy t (by simp at ht; omega)⟩)
      (fun s' hs' => ⟨by rw [← hvA0]; exact hD1A s' (by simp at hs'; omega), fun hy => by
        by_contra hs0
        exact hD2A 0 s' (by omega) (by simp at hs'; omega) (hyA.trans hy.symm)⟩)
      (by simp only [if_true]; rw [hA0]; exact hb₃out)
  · -- case Ia: escape through `a₃`, continuing along `A`
    have ha₃out : X.isOut a₃ ≠ X.isOut a₂ := by
      rw [← h3, hpre.isOut_rot_apply (by rw [hvx _ (by simp)]; exact hi₁)]
      cases X.isOut a₂ <;> simp
    refine hasBadgon_swivelMove_of_walks hX hd hmono (by omega) hB0 hAB hBB hAc hBc hvA0 hu huint
      hux huy hlast hw hint hh hCVy (k₁ := a₃) (Or.inl (hvx _ (by simp))) ca₃ ha
      (by simp only [mem_insert, mem_singleton, not_or]
          exact ⟨hne 3 0 (by norm_num) (by norm_num) (by norm_num),
            hne 3 11 (by norm_num) (by norm_num) (by norm_num),
            hne 3 6 (by norm_num) (by norm_num) (by norm_num),
            hne 3 5 (by norm_num) (by norm_num) (by norm_num)⟩)
      false (pre := []) (r := 1) (Or.inl ⟨rfl, rfl⟩)
      (fun w hw' => by
        simp only [Bool.false_eq_true, if_false, List.nil_append, List.head?_eq_getElem?,
          List.getElem?_eq_getElem (by omega : 0 < A.length), Option.mem_def,
          Option.some.injEq] at hw'
        rw [← hw', hA0, X.rot_pow_three_apply, h4, h5, hφφ])
      hA1 (by rw [hR3, s2, s3, s4]; exact hA1d.symm)
      (fun z hz => by
        rcases hz with rfl | rfl
        · exact Or.inl (hvx _ (by simp)).symm
        · exact Or.inr (Or.inr ⟨0, hA1, hyA.symm⟩))
      (fun t ht ht' => ⟨by rw [← hvA0]; exact hD1A t (by simp at ht'; omega), fun hy =>
        hD2A 0 t (by omega) (by simp at ht'; omega) (hyA.trans hy.symm)⟩)
      (fun s' hs' => ⟨by rw [← hvB0]; exact hD1B s' (by simp at hs'; omega), fun hy =>
        absurd hy (hBy s' (by simp at hs'; omega))⟩)
      (by simp only [Bool.false_eq_true, if_false]; rw [hB0d]; exact ha₃out)

/-- The closed walk of configuration II and its winding function: `h(f(b₂)) = h(f(a₂)) + 1`, and
neither `a₂` nor `b₂` is a dart of the walk or the reverse of one. -/
private theorem winding_walks_two (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {A B : List H}
    (hA0 : 0 < A.length) (hB1 : 1 < B.length)
    (hAc : A.IsChain X.StrandStep) (hBc : B.IsChain X.StrandStep)
    (hA0d : A[0] = (X.rot ^ 3) d₁) (hB0d : B[0] = X.inv (X.facePerm d₁))
    (hu : X.vertexOf (X.inv A[A.length - 1]) = X.vertexOf (X.inv B[B.length - 1]))
    (huint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv A[A.length - 1])))
    (hD1A : ∀ t (ht : t < A.length), X.vertexOf (X.inv A[t]) ≠ X.vertexOf A[0])
    (hD2A : ∀ s t (hs : s < t) (ht : t < A.length),
      X.vertexOf (X.inv (A[s]'(by omega))) ≠ X.vertexOf (X.inv A[t]))
    (hD1B : ∀ t (ht : t < B.length), X.vertexOf (X.inv B[t]) ≠ X.vertexOf B[0])
    (hD2B : ∀ s t (hs : s < t) (ht : t < B.length),
      X.vertexOf (X.inv (B[s]'(by omega))) ≠ X.vertexOf (X.inv B[t]))
    (hcross : ∀ s (hs : s + 1 < B.length) t (ht : t < A.length),
      X.vertexOf (X.inv B[s]) ≠ X.vertexOf (X.inv A[t]))
    (hlast : A[A.length - 1] ≠ B[B.length - 1]) :
    X.IsSimpleClosedWalk (A ++ B.reverse.map X.inv).get ∧
      (∀ i, ¬X.IsBoundaryVertex (X.vertexOf ((A ++ B.reverse.map X.inv).get i))) ∧
      ∃ h : X.faceOrbits → ℤ, X.IsWindingFunction (X.walkCycle (A ++ B.reverse.map X.inv).get) h ∧
        h (X.toFaceOrbit ((X.rot ^ 2) (X.facePerm d₁))) = h (X.toFaceOrbit ((X.rot ^ 2) d₁)) + 1 ∧
        (∀ i, (X.rot ^ 2) d₁ ≠ (A ++ B.reverse.map X.inv).get i ∧
          (X.rot ^ 2) d₁ ≠ X.inv ((A ++ B.reverse.map X.inv).get i)) ∧
        (∀ i, (X.rot ^ 2) (X.facePerm d₁) ≠ (A ++ B.reverse.map X.inv).get i ∧
          (X.rot ^ 2) (X.facePerm d₁) ≠ X.inv ((A ++ B.reverse.map X.inv).get i)) := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hd.exists_swivel hpre
  have hφφ : X.rot (X.inv (X.facePerm d₁)) = d₁ := hd.facePerm_facePerm
  have hfφ : X.toFaceOrbit (X.facePerm d₁) = X.toFaceOrbit d₁ := X.toFaceOrbit_facePerm d₁
  have ha₃ : (X.rot ^ 3) d₁ = a₃ := by rw [X.rot_pow_three_apply, h1, h2, h3]
  rw [ha₃] at hA0d
  have hne : ∀ i j (hi : i < 12) (hj : j < 12), i ≠ j →
      [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][i] ≠
        [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][j] :=
    fun i j hi hj hij h => hij ((hnd.getElem_inj_iff (hi := by simpa using hi)
      (hj := by simpa using hj)).1 h)
  set d₂ := X.facePerm d₁ with hd₂
  have hvx : ∀ z ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H), X.vertexOf z = X.vertexOf d₁ :=
    fun z hz => X.vertexOf_eq_of_mem (by rw [hV₁]; exact hz)
  have hvy : ∀ z ∈ ({d₂, b₁, b₂, b₃, b₄, X.inv d₁} : Finset H), X.vertexOf z = X.vertexOf d₂ :=
    fun z hz => X.vertexOf_eq_of_mem (by rw [hV₂]; exact hz)
  have hB1d : B[1] = b₃ := by
    rw [((List.isChain_iff_getElem.1 hBc) 0 hB1).2, hB0d, hinv, X.rot_pow_three_apply, g1, g2, g3]
  have hx : X.vertexOf A[0] = X.vertexOf B[0] := by
    rw [hA0d, hB0d, hvx a₃ (by simp), hvx (X.inv d₂) (by simp)]
  have hw := isSimpleClosedWalk_of_walks hpre hA0 (by omega) hAc hBc hx hu hD1A hD2A hD1B hD2B
    hcross (by rw [hA0d, hB0d]; exact (hne 3 5 (by norm_num) (by norm_num) (by norm_num))) hlast
  set C := A ++ B.reverse.map X.inv with hC
  have hCl : C.length = A.length + B.length := by simp [hC]
  have hV := fun z => exists_vertexOf_walks_iff (z := z) hA0 (by omega) hAc hu
  have hint : ∀ i, ¬X.IsBoundaryVertex (X.vertexOf (C.get i)) := by
    intro i
    rcases (hV _).1 ⟨i, rfl⟩ with h | h | ⟨t, ht, h⟩ | ⟨t, ht, h⟩ <;> rw [h]
    · rw [hA0d, hvx a₃ (by simp)]
      exact hi₁
    · exact huint
    · exact ((List.isChain_iff_getElem.1 hAc) t ht).1
    · exact ((List.isChain_iff_getElem.1 hBc) t ht).1
  obtain ⟨h, hh, -⟩ := hX.toIsDiskMap.existsUnique_isWindingFunction_walkCycle hw
  have hC0 : C.get ⟨0, by omega⟩ = a₃ := by
    simp only [List.get_eq_getElem, hC]
    rw [List.getElem_append_left (by omega), hA0d]
  have hCl1 : C.get ⟨C.length - 1, by omega⟩ = d₂ := by
    simp only [List.get_eq_getElem, hC]
    rw [List.getElem_append_right (by simp [hC] at hCl ⊢; omega)]
    simp only [List.getElem_map, List.getElem_reverse]
    have e : B[B.length - 1 - (A.length + B.length - 1 - A.length)]'(by omega) = B[0] := by
      congr 1
      omega
    simp only [List.length_append, List.length_map, List.length_reverse] at *
    rw [e, hB0d, hinv]
  have hCl2 : C.get ⟨C.length - 2, by omega⟩ = X.inv b₃ := by
    simp only [List.get_eq_getElem, hC]
    rw [List.getElem_append_right (by simp [hC] at hCl ⊢; omega)]
    simp only [List.getElem_map, List.getElem_reverse]
    have e : B[B.length - 1 - (A.length + B.length - 2 - A.length)]'(by omega) = B[1] := by
      congr 1
      omega
    simp only [List.length_append, List.length_map, List.length_reverse] at *
    rw [e, hB1d]
  -- the cycle of `C` around `x` and `y`
  have cx : ∀ z, X.vertexOf z = X.vertexOf d₁ → z ≠ a₃ → z ≠ X.inv d₂ →
      X.walkCycle C.get z = 0 ∧ ∀ i, z ≠ C.get i ∧ z ≠ X.inv (C.get i) := fun z hz h1' h2' =>
    walkCycle_eq_zero_of_vertexOf hinv hw (finRotate_last (by omega))
      (by rw [hC0, hvx a₃ (by simp)]; exact hz) (by rw [hC0]; exact h1')
      (by rw [hCl1]; exact h2')
  have he : (⟨C.length - 2 + 1, by omega⟩ : Fin C.length) = ⟨C.length - 1, by omega⟩ :=
    Fin.ext (by simp only; omega)
  have cy : ∀ z, X.vertexOf z = X.vertexOf d₂ → z ≠ d₂ → z ≠ b₃ →
      X.walkCycle C.get z = 0 ∧ ∀ i, z ≠ C.get i ∧ z ≠ X.inv (C.get i) := fun z hz h1' h2' =>
    walkCycle_eq_zero_of_vertexOf hinv hw
      (finRotate_of_lt (i := C.length - 2) (L := C.length) (by omega))
      (by rw [he, hCl1]; exact hz) (by rw [he, hCl1]; exact h1')
      (by rw [hCl2, hinv]; exact h2')
  have ca₂ := cx a₂ (hvx _ (by simp)) (hne 2 3 (by norm_num) (by norm_num) (by norm_num))
    (hne 2 5 (by norm_num) (by norm_num) (by norm_num))
  have ca₄ := cx a₄ (hvx _ (by simp)) (hne 4 3 (by norm_num) (by norm_num) (by norm_num))
    (hne 4 5 (by norm_num) (by norm_num) (by norm_num))
  have cb₁ := cy b₁ (hvy _ (by simp)) (hne 7 6 (by norm_num) (by norm_num) (by norm_num))
    (hne 7 9 (by norm_num) (by norm_num) (by norm_num))
  have cb₂ := cy b₂ (hvy _ (by simp)) (hne 8 6 (by norm_num) (by norm_num) (by norm_num))
    (hne 8 9 (by norm_num) (by norm_num) (by norm_num))
  have ca₃ : X.walkCycle C.get a₃ = 1 := by rw [← hC0]; exact hw.walkCycle_apply_self _
  have cd₂ : X.walkCycle C.get d₂ = 1 := by rw [← hCl1]; exact hw.walkCycle_apply_self _
  have cd₂' : X.walkCycle C.get (X.inv d₂) = -1 := by
    rw [← hCl1]
    exact hw.walkCycle_apply_inv hinv _
  -- the rotation rule
  have r1 := hh.apply_rot hinv a₂
  rw [h3, ca₂.1, add_zero] at r1
  have r2 := hh.apply_rot hinv a₃
  rw [h4, ca₃, r1] at r2
  have r3 := hh.apply_rot hinv a₄
  rw [h5, ca₄.1, add_zero, r2] at r3
  have r4 := hh.apply_rot hinv (X.inv d₂)
  rw [hφφ, cd₂', r3] at r4
  have r5 := hh.apply_rot hinv d₂
  rw [g1, cd₂, hfφ, r4] at r5
  have r6 := hh.apply_rot hinv b₁
  rw [g2, cb₁.1, add_zero, r5] at r6
  have ha₂ : (X.rot ^ 2) d₁ = a₂ := by rw [pow_two, Equiv.Perm.mul_apply, h1, h2]
  have hb₂ : (X.rot ^ 2) d₂ = b₂ := by rw [pow_two, Equiv.Perm.mul_apply, g1, g2]
  refine ⟨hw, hint, h, hh, ?_, ?_, ?_⟩
  · rw [ha₂, hb₂, r6]
    ring
  · rw [ha₂]
    exact ca₂.2
  · rw [hb₂]
    exact cb₂.2

/-- **Configuration II**: two walks from the corner `x` of the digon to a common vertex
`u ∉ {x, y}`, leaving `x` along `a₃` and along `d̄₂`, with no other common vertex, the first one
avoiding `y`. Then the swivel move has a badgon. -/
private theorem hasBadgon_swivelMove_of_walks_two (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) (hmono : ¬X.HasMonogon) {A B : List H}
    (hA0 : 0 < A.length) (hB1 : 1 < B.length)
    (hAB : ∀ e ∈ A, e ∉ X.bdry) (hBB : ∀ e ∈ B, e ∉ X.bdry)
    (hAc : A.IsChain X.StrandStep) (hBc : B.IsChain X.StrandStep)
    (hA0d : A[0] = (X.rot ^ 3) d₁) (hB0d : B[0] = X.inv (X.facePerm d₁))
    (hu : X.vertexOf (X.inv A[A.length - 1]) = X.vertexOf (X.inv B[B.length - 1]))
    (huint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv A[A.length - 1])))
    (hux : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf d₁)
    (huy : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf (X.facePerm d₁))
    (hD1A : ∀ t (ht : t < A.length), X.vertexOf (X.inv A[t]) ≠ X.vertexOf A[0])
    (hD2A : ∀ s t (hs : s < t) (ht : t < A.length),
      X.vertexOf (X.inv (A[s]'(by omega))) ≠ X.vertexOf (X.inv A[t]))
    (hD1B : ∀ t (ht : t < B.length), X.vertexOf (X.inv B[t]) ≠ X.vertexOf B[0])
    (hD2B : ∀ s t (hs : s < t) (ht : t < B.length),
      X.vertexOf (X.inv (B[s]'(by omega))) ≠ X.vertexOf (X.inv B[t]))
    (hcross : ∀ s (hs : s + 1 < B.length) t (ht : t < A.length),
      X.vertexOf (X.inv B[s]) ≠ X.vertexOf (X.inv A[t]))
    (hAy : ∀ t (ht : t < A.length), X.vertexOf (X.inv A[t]) ≠ X.vertexOf (X.facePerm d₁))
    (hlast : A[A.length - 1] ≠ B[B.length - 1]) :
    (X.swivelMove d₁).HasBadgon := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  obtain ⟨hw, hint, h, hh, r6, ca₂, cb₂⟩ := winding_walks_two hX hd hA0 hB1 hAc hBc hA0d hB0d hu
    huint hD1A hD2A hD1B hD2B hcross hlast
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -, -⟩ := hd.exists_swivel hpre
  have hφφ : X.rot (X.inv (X.facePerm d₁)) = d₁ := hd.facePerm_facePerm
  have hφ : X.rot (X.inv d₁) = X.facePerm d₁ := rfl
  have ha₂ : (X.rot ^ 2) d₁ = a₂ := by rw [pow_two, Equiv.Perm.mul_apply, h1, h2]
  have ha₃ : (X.rot ^ 3) d₁ = a₃ := by rw [X.rot_pow_three_apply, h1, h2, h3]
  have hb₂ : (X.rot ^ 2) (X.facePerm d₁) = b₂ := by rw [pow_two, Equiv.Perm.mul_apply, g1, g2]
  rw [ha₃] at hA0d
  rw [ha₂, hb₂] at r6
  rw [ha₂] at ca₂
  rw [hb₂] at cb₂
  have hne : ∀ i j (hi : i < 12) (hj : j < 12), i ≠ j →
      [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][i] ≠
        [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][j] :=
    fun i j hi hj hij h => hij ((hnd.getElem_inj_iff (hi := by simpa using hi)
      (hj := by simpa using hj)).1 h)
  set d₂ := X.facePerm d₁ with hd₂
  have hvx : ∀ z ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv d₂} : Finset H), X.vertexOf z = X.vertexOf d₁ :=
    fun z hz => X.vertexOf_eq_of_mem (by rw [hV₁]; exact hz)
  have hvy : ∀ z ∈ ({d₂, b₁, b₂, b₃, b₄, X.inv d₁} : Finset H), X.vertexOf z = X.vertexOf d₂ :=
    fun z hz => X.vertexOf_eq_of_mem (by rw [hV₂]; exact hz)
  have hB1d : B[1] = b₃ := by
    rw [((List.isChain_iff_getElem.1 hBc) 0 hB1).2, hB0d, hinv, X.rot_pow_three_apply, g1, g2, g3]
  have hyB : X.vertexOf (X.inv B[0]) = X.vertexOf d₂ := by rw [hB0d, hinv]
  have hR3 : ∀ z, ((X.swivelMove d₁).rot ^ 3) z =
      X.swivelRot d₁ (X.swivelRot d₁ (X.swivelRot d₁ z)) := fun z => rfl
  have hvB0 : X.vertexOf B[0] = X.vertexOf d₁ := by rw [hB0d]; exact hvx _ (by simp)
  have hvA0 : X.vertexOf A[0] = X.vertexOf d₁ := by rw [hA0d]; exact hvx _ (by simp)
  have hCVy : X.vertexOf d₂ = X.vertexOf A[0] ∨
      X.vertexOf d₂ = X.vertexOf (X.inv A[A.length - 1]) ∨
      (∃ t, ∃ _ : t + 1 < A.length, X.vertexOf d₂ = X.vertexOf (X.inv A[t])) ∨
      ∃ t, ∃ _ : t + 1 < B.length, X.vertexOf d₂ = X.vertexOf (X.inv B[t]) :=
    Or.inr (Or.inr (Or.inr ⟨0, hB1, hyB.symm⟩))
  by_cases ha : h (X.toFaceOrbit a₂) = 0
  · -- case IIb: escape through `b₂`, continuing along `d̄₁` and `A`
    have hb₂out : X.isOut b₂ ≠ X.isOut (X.inv d₂) := by
      have e2 : b₂ = (X.rot ^ 2) d₂ := by rw [pow_two, Equiv.Perm.mul_apply, g1, g2]
      rw [e2, hpre.isOut_rot_pow_apply hi₂, if_pos (by decide),
        hpre.isOut_inv_apply (hd.notMem_bdry.2)]
      cases X.isOut d₂ <;> simp
    refine hasBadgon_swivelMove_of_walks hX hd hmono hA0 (by omega) hAB hBB hAc hBc hvA0 hu huint
      hux huy hlast hw hint hh hCVy (k₁ := b₂) (Or.inr (hvy _ (by simp))) cb₂
      (by rw [r6, ha]; norm_num)
      (by simp only [mem_insert, mem_singleton, not_or]
          exact ⟨hne 8 0 (by norm_num) (by norm_num) (by norm_num),
            hne 8 11 (by norm_num) (by norm_num) (by norm_num),
            hne 8 6 (by norm_num) (by norm_num) (by norm_num),
            hne 8 5 (by norm_num) (by norm_num) (by norm_num)⟩)
      false (pre := [X.inv d₁]) (r := 0)
      (Or.inr ⟨X.inv d₁, rfl, rfl, by simp, ⟨by
          change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.inv d₁)))
          rw [hinv]
          exact hi₁, by
          change A[0] = (X.rot ^ 3) (X.inv (X.inv d₁))
          rw [hA0d, hinv, X.rot_pow_three_apply, h1, h2, h3]⟩⟩)
      (fun w hw' => by
        simp only [Bool.false_eq_true, if_false, List.singleton_append, List.head?_cons,
          Option.mem_def, Option.some.injEq] at hw'
        rw [← hw', X.rot_pow_three_apply, g3, g4, g5])
      hA0 (by rw [hR3, s5, s6, s1]; exact hA0d.symm)
      (fun z hz => by
        rcases hz with rfl | rfl
        · exact Or.inr (Or.inl ⟨X.inv d₁, rfl, by rw [hinv]⟩)
        · exact Or.inl (hvy _ (by simp)).symm)
      (fun t _ ht => ⟨by rw [← hvA0]; exact hD1A t (by simp at ht; omega),
        hAy t (by simp at ht; omega)⟩)
      (fun s' hs' => ⟨by rw [← hvB0]; exact hD1B s' (by simp at hs'; omega), fun hy => by
        by_contra hs0
        exact hD2B 0 s' (by omega) (by simp at hs'; omega) (hyB.trans hy.symm)⟩)
      (by simp only [Bool.false_eq_true, if_false]; rw [hB0d]; exact hb₂out)
  · -- case IIa: escape through `a₂`, continuing along `B`
    have ha₂out : X.isOut a₂ ≠ X.isOut a₃ := by
      rw [← h3, hpre.isOut_rot_apply (by rw [hvx _ (by simp)]; exact hi₁)]
      cases X.isOut a₂ <;> simp
    refine hasBadgon_swivelMove_of_walks hX hd hmono hA0 (by omega) hAB hBB hAc hBc hvA0 hu huint
      hux huy hlast hw hint hh hCVy (k₁ := a₂) (Or.inl (hvx _ (by simp))) ca₂ ha
      (by simp only [mem_insert, mem_singleton, not_or]
          exact ⟨hne 2 0 (by norm_num) (by norm_num) (by norm_num),
            hne 2 11 (by norm_num) (by norm_num) (by norm_num),
            hne 2 6 (by norm_num) (by norm_num) (by norm_num),
            hne 2 5 (by norm_num) (by norm_num) (by norm_num)⟩)
      true (pre := []) (r := 1) (Or.inl ⟨rfl, rfl⟩)
      (fun w hw' => by
        simp only [if_true, List.nil_append, List.head?_eq_getElem?,
          List.getElem?_eq_getElem (by omega : 0 < B.length), Option.mem_def,
          Option.some.injEq] at hw'
        rw [← hw', hB0d, X.rot_pow_three_apply, h3, h4, h5])
      hB1 (by rw [hR3, s12, s7, s8]; exact hB1d.symm)
      (fun z hz => by
        rcases hz with rfl | rfl
        · exact Or.inl (hvx _ (by simp)).symm
        · exact Or.inr (Or.inr ⟨0, hB1, hyB.symm⟩))
      (fun t ht ht' => ⟨by rw [← hvB0]; exact hD1B t (by simp at ht'; omega), fun hy =>
        hD2B 0 t (by omega) (by simp at ht'; omega) (hyB.trans hy.symm)⟩)
      (fun s' hs' => ⟨by rw [← hvA0]; exact hD1A s' (by simp at hs'; omega), fun hy =>
        absurd hy (hAy s' (by simp at hs'; omega))⟩)
      (by simp only [if_true]; rw [hA0d]; exact ha₂out)

/-- Cutting two walks from `x` to `w` at their first common vertex `u`: prefixes `A, B` of them
ending at `u`, with distinct last darts and no other common vertex. -/
private theorem exists_cut_walks {A₀ B₀ : List H} (hA0 : 0 < A₀.length)
    (hB0 : 0 < B₀.length) (hAc : A₀.IsChain X.StrandStep) (hBc : B₀.IsChain X.StrandStep)
    (hx : X.vertexOf A₀[0] = X.vertexOf B₀[0])
    (hw : X.vertexOf (X.inv A₀[A₀.length - 1]) = X.vertexOf (X.inv B₀[B₀.length - 1]))
    (hwint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv A₀[A₀.length - 1])))
    (hD1A : ∀ t (ht : t < A₀.length), X.vertexOf (X.inv A₀[t]) ≠ X.vertexOf A₀[0])
    (hD2A : ∀ s t (hs : s < t) (ht : t < A₀.length),
      X.vertexOf (X.inv (A₀[s]'(by omega))) ≠ X.vertexOf (X.inv A₀[t]))
    (hD1B : ∀ t (ht : t < B₀.length), X.vertexOf (X.inv B₀[t]) ≠ X.vertexOf B₀[0])
    (hD2B : ∀ s t (hs : s < t) (ht : t < B₀.length),
      X.vertexOf (X.inv (B₀[s]'(by omega))) ≠ X.vertexOf (X.inv B₀[t]))
    (hhead : A₀[0] ≠ B₀[0]) :
    ∃ A B : List H, A <+: A₀ ∧ B <+: B₀ ∧ ∃ (hA : 0 < A.length) (hB : 0 < B.length),
      X.vertexOf (X.inv A[A.length - 1]) = X.vertexOf (X.inv B[B.length - 1]) ∧
      ¬X.IsBoundaryVertex (X.vertexOf (X.inv A[A.length - 1])) ∧
      A[A.length - 1] ≠ B[B.length - 1] ∧
      (∀ t (ht : t < A.length), X.vertexOf (X.inv A[t]) ≠ X.vertexOf A[0]) ∧
      (∀ s t (hs : s < t) (ht : t < A.length),
        X.vertexOf (X.inv (A[s]'(by omega))) ≠ X.vertexOf (X.inv A[t])) ∧
      (∀ t (ht : t < B.length), X.vertexOf (X.inv B[t]) ≠ X.vertexOf B[0]) ∧
      (∀ s t (hs : s < t) (ht : t < B.length),
        X.vertexOf (X.inv (B[s]'(by omega))) ≠ X.vertexOf (X.inv B[t])) ∧
      ∀ s (hs : s + 1 < B.length) t (ht : t < A.length),
        X.vertexOf (X.inv B[s]) ≠ X.vertexOf (X.inv A[t]) := by
  obtain ⟨i, j, hi, hj, hij, hne, hcr⟩ := exists_cut hA0 hB0 hAc hBc hx hw hD1A hD1B hhead
  have hAl : (A₀.take (i + 1)).length = i + 1 := by simp; omega
  have hBl : (B₀.take (j + 1)).length = j + 1 := by simp; omega
  have hAt : ∀ t (ht : t < (A₀.take (i + 1)).length), (A₀.take (i + 1))[t] = A₀[t]'(by
      simp at ht; omega) := fun t ht => by simp
  have hBt : ∀ t (ht : t < (B₀.take (j + 1)).length), (B₀.take (j + 1))[t] = B₀[t]'(by
      simp at ht; omega) := fun t ht => by simp
  have hAlast : (A₀.take (i + 1))[(A₀.take (i + 1)).length - 1]'(by omega) = A₀[i] := by
    rw [hAt]
    congr 1
    omega
  have hBlast : (B₀.take (j + 1))[(B₀.take (j + 1)).length - 1]'(by omega) = B₀[j] := by
    rw [hBt]
    congr 1
    omega
  have huint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv A₀[i])) := by
    by_cases hi' : i + 1 < A₀.length
    · exact ((List.isChain_iff_getElem.1 hAc) i hi').1
    · have e : A₀[i] = A₀[A₀.length - 1] := by congr 1; omega
      rw [e]
      exact hwint
  refine ⟨A₀.take (i + 1), B₀.take (j + 1), List.take_prefix _ _, List.take_prefix _ _,
    by omega, by omega, by rw [hAlast, hBlast]; exact hij, by rw [hAlast]; exact huint,
    by rw [hAlast, hBlast]; exact hne, fun t ht => ?_, fun s t hs ht => ?_, fun t ht => ?_,
    fun s t hs ht => ?_, fun s hs t ht => ?_⟩
  · rw [hAt, hAt]
    exact hD1A t _
  · rw [hAt, hAt]
    exact hD2A s t hs _
  · rw [hBt, hBt]
    exact hD1B t _
  · rw [hBt, hBt]
    exact hD2B s t hs _
  · rw [hBt, hAt]
    exact hcr s (by omega) t _

/-- Configuration I from two walks without repeated vertices from `x` to a common vertex `w`,
leaving `x` along `d₁` and `a₂`: cut them at their first common vertex. -/
private theorem hasBadgon_swivelMove_of_walks_from_one (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) (hmono : ¬X.HasMonogon) {A₀ B₀ : List H}
    (hA0 : 0 < A₀.length) (hB0 : 0 < B₀.length)
    (hAB : ∀ e ∈ A₀, e ∉ X.bdry) (hBB : ∀ e ∈ B₀, e ∉ X.bdry)
    (hAc : A₀.IsChain X.StrandStep) (hBc : B₀.IsChain X.StrandStep)
    (hA0d : A₀[0] = d₁) (hB0d : B₀[0] = (X.rot ^ 2) d₁)
    (hw : X.vertexOf (X.inv A₀[A₀.length - 1]) = X.vertexOf (X.inv B₀[B₀.length - 1]))
    (hwint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv A₀[A₀.length - 1])))
    (hwy : X.vertexOf (X.inv A₀[A₀.length - 1]) ≠ X.vertexOf (X.facePerm d₁))
    (hD1A : ∀ t (ht : t < A₀.length), X.vertexOf (X.inv A₀[t]) ≠ X.vertexOf A₀[0])
    (hD2A : ∀ s t (hs : s < t) (ht : t < A₀.length),
      X.vertexOf (X.inv (A₀[s]'(by omega))) ≠ X.vertexOf (X.inv A₀[t]))
    (hD1B : ∀ t (ht : t < B₀.length), X.vertexOf (X.inv B₀[t]) ≠ X.vertexOf B₀[0])
    (hD2B : ∀ s t (hs : s < t) (ht : t < B₀.length),
      X.vertexOf (X.inv (B₀[s]'(by omega))) ≠ X.vertexOf (X.inv B₀[t])) :
    (X.swivelMove d₁).HasBadgon := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂⟩ := hd.exists_darts hpre
  have hφφ : X.rot (X.inv (X.facePerm d₁)) = d₁ := hd.facePerm_facePerm
  have ha₂ : (X.rot ^ 2) d₁ = a₂ := by rw [pow_two, Equiv.Perm.mul_apply, h1, h2]
  have hvx : ∀ z ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁)} : Finset H),
      X.vertexOf z = X.vertexOf d₁ := fun z hz => X.vertexOf_eq_of_mem (by rw [hV₁]; exact hz)
  have hvy : ∀ z ∈ ({X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁} : Finset H),
      X.vertexOf z = X.vertexOf (X.facePerm d₁) :=
    fun z hz => X.vertexOf_eq_of_mem (by rw [hV₂]; exact hz)
  have hx : X.vertexOf A₀[0] = X.vertexOf B₀[0] := by rw [hA0d, hB0d, ha₂, hvx a₂ (by simp)]
  have hhead : A₀[0] ≠ B₀[0] := by
    rw [hA0d, hB0d, ha₂]
    intro h
    have := (hnd.getElem_inj_iff (i := 0) (j := 2) (hi := by simp) (hj := by simp)).1 h
    omega
  -- the second walk avoids `y`
  have hBy : ∀ t (ht : t < B₀.length), X.vertexOf (X.inv B₀[t]) ≠ X.vertexOf (X.facePerm d₁) :=
    vertexOf_inv_ne_of_strandStep hpre hmono hB0 hBB hBc (ℓ := X.facePerm d₁) hd.notMem_bdry.2
      ⟨by
        change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.facePerm d₁)))
        rw [hvx _ (by simp)]
        exact hi₁, by rw [hB0d, X.rot_pow_three_apply, hφφ, pow_two, Equiv.Perm.mul_apply]⟩ hi₂ hD1B
      (by rw [← hw]; exact hwy)
  obtain ⟨A, B, hpA, hpB, hA, hB, hu, huint, hlast, hD1A', hD2A', hD1B', hD2B', hcross⟩ :=
    exists_cut_walks hA0 hB0 hAc hBc hx hw hwint hD1A hD2A hD1B hD2B hhead
  have hA0' : A[0] = d₁ := (hpA.getElem hA).trans hA0d
  have hB0' : B[0] = (X.rot ^ 2) d₁ := (hpB.getElem hB).trans hB0d
  have hBy' : ∀ t (ht : t < B.length), X.vertexOf (X.inv B[t]) ≠ X.vertexOf (X.facePerm d₁) :=
    fun t ht => by rw [hpB.getElem ht]; exact hBy t _
  have huy : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf (X.facePerm d₁) := by
    rw [hu]
    exact hBy' _ (by omega)
  have hA1 : 1 < A.length := by
    by_contra h'
    apply huy
    have e : A[A.length - 1] = A[0] := by congr 1; omega
    rw [e, hA0']
    exact hvy _ (by simp)
  exact hasBadgon_swivelMove_of_walks_one hX hd hmono hA1 hB
    (fun e he => hAB e (hpA.subset he)) (fun e he => hBB e (hpB.subset he))
    (hAc.infix hpA.isInfix) (hBc.infix hpB.isInfix) hA0' hB0' hu huint
    (by rw [← hA0']; exact hD1A' _ (by omega)) huy hD1A' hD2A' hD1B' hD2B' hcross hBy' hlast

/-- Configuration II from two walks without repeated vertices from `x` to a common vertex `w`,
leaving `x` along `a₃` and `d̄₂`: cut them at their first common vertex. -/
private theorem hasBadgon_swivelMove_of_walks_from_two (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) (hmono : ¬X.HasMonogon) {A₀ B₀ : List H}
    (hA0 : 0 < A₀.length) (hB0 : 0 < B₀.length)
    (hAB : ∀ e ∈ A₀, e ∉ X.bdry) (hBB : ∀ e ∈ B₀, e ∉ X.bdry)
    (hAc : A₀.IsChain X.StrandStep) (hBc : B₀.IsChain X.StrandStep)
    (hA0d : A₀[0] = (X.rot ^ 3) d₁) (hB0d : B₀[0] = X.inv (X.facePerm d₁))
    (hw : X.vertexOf (X.inv A₀[A₀.length - 1]) = X.vertexOf (X.inv B₀[B₀.length - 1]))
    (hwint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv A₀[A₀.length - 1])))
    (hwy : X.vertexOf (X.inv A₀[A₀.length - 1]) ≠ X.vertexOf (X.facePerm d₁))
    (hD1A : ∀ t (ht : t < A₀.length), X.vertexOf (X.inv A₀[t]) ≠ X.vertexOf A₀[0])
    (hD2A : ∀ s t (hs : s < t) (ht : t < A₀.length),
      X.vertexOf (X.inv (A₀[s]'(by omega))) ≠ X.vertexOf (X.inv A₀[t]))
    (hD1B : ∀ t (ht : t < B₀.length), X.vertexOf (X.inv B₀[t]) ≠ X.vertexOf B₀[0])
    (hD2B : ∀ s t (hs : s < t) (ht : t < B₀.length),
      X.vertexOf (X.inv (B₀[s]'(by omega))) ≠ X.vertexOf (X.inv B₀[t])) :
    (X.swivelMove d₁).HasBadgon := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂⟩ := hd.exists_darts hpre
  have ha₃ : (X.rot ^ 3) d₁ = a₃ := by rw [X.rot_pow_three_apply, h1, h2, h3]
  have hvx : ∀ z ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁)} : Finset H),
      X.vertexOf z = X.vertexOf d₁ := fun z hz => X.vertexOf_eq_of_mem (by rw [hV₁]; exact hz)
  have hvy : ∀ z ∈ ({X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁} : Finset H),
      X.vertexOf z = X.vertexOf (X.facePerm d₁) :=
    fun z hz => X.vertexOf_eq_of_mem (by rw [hV₂]; exact hz)
  have hx : X.vertexOf A₀[0] = X.vertexOf B₀[0] := by
    rw [hA0d, hB0d, ha₃, hvx a₃ (by simp), hvx (X.inv (X.facePerm d₁)) (by simp)]
  have hhead : A₀[0] ≠ B₀[0] := by
    rw [hA0d, hB0d, ha₃]
    intro h
    have := (hnd.getElem_inj_iff (i := 3) (j := 5) (hi := by simp) (hj := by simp)).1 h
    omega
  -- the first walk avoids `y`
  have hAy : ∀ t (ht : t < A₀.length), X.vertexOf (X.inv A₀[t]) ≠ X.vertexOf (X.facePerm d₁) := by
    have := vertexOf_inv_ne_of_strandStep hpre hmono hA0 hAB hAc (ℓ := X.inv d₁)
      (hpre.inv_notMem_bdry hd.notMem_bdry.1)
      ⟨by
        change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.inv d₁)))
        rw [hinv]
        exact hi₁, by rw [hA0d, hinv]⟩ (by rw [hvy (X.inv d₁) (by simp)]; exact hi₂) hD1A
      (by rw [hvy (X.inv d₁) (by simp)]; exact hwy)
    intro t ht
    rw [← hvy (X.inv d₁) (by simp)]
    exact this t ht
  obtain ⟨A, B, hpA, hpB, hA, hB, hu, huint, hlast, hD1A', hD2A', hD1B', hD2B', hcross⟩ :=
    exists_cut_walks hA0 hB0 hAc hBc hx hw hwint hD1A hD2A hD1B hD2B hhead
  have hA0' : A[0] = (X.rot ^ 3) d₁ := (hpA.getElem hA).trans hA0d
  have hB0' : B[0] = X.inv (X.facePerm d₁) := (hpB.getElem hB).trans hB0d
  have hAy' : ∀ t (ht : t < A.length), X.vertexOf (X.inv A[t]) ≠ X.vertexOf (X.facePerm d₁) :=
    fun t ht => by rw [hpA.getElem ht]; exact hAy t _
  have huy : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf (X.facePerm d₁) :=
    hAy' _ (by omega)
  have hB1 : 1 < B.length := by
    by_contra h'
    apply huy
    have e : B[B.length - 1] = B[0] := by congr 1; omega
    rw [hu, e, hB0', hinv]
  exact hasBadgon_swivelMove_of_walks_two hX hd hmono hA hB1
    (fun e he => hAB e (hpA.subset he)) (fun e he => hBB e (hpB.subset he))
    (hAc.infix hpA.isInfix) (hBc.infix hpB.isInfix) hA0' hB0' hu huint
    (by
      have := hD1A' _ (show A.length - 1 < A.length by omega)
      rw [hA0', ha₃, hvx a₃ (by simp)] at this
      exact this) huy hD1A' hD2A' hD1B' hD2B' hcross hAy' hlast

/-- The two strand paths of a parallel digon with a corner `x`, read as walks from `x`. -/
private theorem exists_walks_of_isParallelDigon (hX : X.IsPreTripleDiagram) {P Q : List H}
    {x w : Finset H} (h : X.IsParallelDigon P Q x w ∨ X.IsParallelDigon P Q w x) :
    ∃ P₀ Q₀ : List H, ∃ (hP0 : 0 < P₀.length) (hQ0 : 0 < Q₀.length),
      (∀ e ∈ P₀, e ∉ X.bdry) ∧ (∀ e ∈ Q₀, e ∉ X.bdry) ∧ P₀.IsChain X.StrandStep ∧
      Q₀.IsChain X.StrandStep ∧ X.vertexOf P₀[0] = x ∧ X.vertexOf Q₀[0] = x ∧
      X.vertexOf (X.inv P₀[P₀.length - 1]) = w ∧ X.vertexOf (X.inv Q₀[Q₀.length - 1]) = w ∧
      P₀[P₀.length - 1] ≠ Q₀[Q₀.length - 1] ∧ P₀[0] ≠ Q₀[0] ∧ X.isOut P₀[0] = X.isOut Q₀[0] ∧
      x ∈ X.internalVertices ∧ w ∈ X.internalVertices ∧ x ≠ w ∧
      ((X.IsParallelDigon P Q x w ∧ P₀.head? = P.head? ∧ Q₀.head? = Q.head?) ∨
        (X.IsParallelDigon P Q w x ∧ P₀.head? = P.getLast?.map X.inv ∧
          Q₀.head? = Q.getLast?.map X.inv)) := by
  rcases h with h | h
  · have hP0 : 0 < P.length := List.length_pos_iff.2 h.isStrandPath_fst.ne_nil
    have hQ0 : 0 < Q.length := List.length_pos_iff.2 h.isStrandPath_snd.ne_nil
    have hPh := head?_eq_some_getElem hP0
    have hQh := head?_eq_some_getElem hQ0
    have hPl := getLast?_eq_some_getElem hP0
    have hQl := getLast?_eq_some_getElem hQ0
    refine ⟨P, Q, hP0, hQ0, h.isStrandPath_fst.notMem_bdry, h.isStrandPath_snd.notMem_bdry,
      h.isStrandPath_fst.isChain, h.isStrandPath_snd.isChain, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      h.mem_left, h.mem_right, h.ne, Or.inl ⟨h, rfl, rfl⟩⟩
    · rw [← h.pathStart_fst, X.pathStart_of_head? hPh]
    · rw [← h.pathStart_snd, X.pathStart_of_head? hQh]
    · rw [← h.pathEnd_fst, X.pathEnd_of_getLast? hPl]
    · rw [← h.pathEnd_snd, X.pathEnd_of_getLast? hQl]
    · intro he
      exact h.getLast?_ne (by rw [hPl, hQl, he])
    · intro he
      exact h.head?_ne (by rw [hPh, hQh, he])
    · rw [h.isStrandPath_fst.isOut_eq_true _ (List.getElem_mem _),
        h.isStrandPath_snd.isOut_eq_true _ (List.getElem_mem _)]
  · have hP0 : 0 < P.length := List.length_pos_iff.2 h.isStrandPath_fst.ne_nil
    have hQ0 : 0 < Q.length := List.length_pos_iff.2 h.isStrandPath_snd.ne_nil
    have hPh := head?_eq_some_getElem hP0
    have hQh := head?_eq_some_getElem hQ0
    have hPl := getLast?_eq_some_getElem hP0
    have hQl := getLast?_eq_some_getElem hQ0
    have hrev : ∀ (K : List H) (hK : 0 < K.length),
        (K.reverse.map X.inv)[0]'(by simp; omega) = X.inv K[K.length - 1] ∧
        (K.reverse.map X.inv)[(K.reverse.map X.inv).length - 1]'(by simp; omega) =
          X.inv K[0] := fun K hK => by
      constructor <;> simp only [List.getElem_map, List.getElem_reverse] <;> congr 2
      simp
    have hPS := h.isStrandPath_fst
    have hQS := h.isStrandPath_snd
    refine ⟨P.reverse.map X.inv, Q.reverse.map X.inv, by simp; omega, by simp; omega,
      fun e he => ?_, fun e he => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.mem_right, h.mem_left,
      h.ne.symm, Or.inr ⟨h, ?_, ?_⟩⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
      exact hX.inv_notMem_bdry (hPS.notMem_bdry c (List.mem_reverse.1 hc))
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
      exact hX.inv_notMem_bdry (hQS.notMem_bdry c (List.mem_reverse.1 hc))
    · rw [List.isChain_map, List.isChain_reverse]
      exact hPS.isChain.imp fun _ _ h' => h'.inv_inv hX
    · rw [List.isChain_map, List.isChain_reverse]
      exact hQS.isChain.imp fun _ _ h' => h'.inv_inv hX
    · rw [(hrev P hP0).1, ← h.pathEnd_fst, X.pathEnd_of_getLast? hPl]
    · rw [(hrev Q hQ0).1, ← h.pathEnd_snd, X.pathEnd_of_getLast? hQl]
    · rw [(hrev P hP0).2, hX.inv_inv_apply, ← h.pathStart_fst, X.pathStart_of_head? hPh]
    · rw [(hrev Q hQ0).2, hX.inv_inv_apply, ← h.pathStart_snd, X.pathStart_of_head? hQh]
    · rw [(hrev P hP0).2, (hrev Q hQ0).2]
      intro he
      exact h.head?_ne (by rw [hPh, hQh, X.inv.injective he])
    · rw [(hrev P hP0).1, (hrev Q hQ0).1]
      intro he
      exact h.getLast?_ne (by rw [hPl, hQl, X.inv.injective he])
    · rw [(hrev P hP0).1, (hrev Q hQ0).1,
        hX.isOut_inv_apply (hPS.notMem_bdry _ (List.getElem_mem _)),
        hX.isOut_inv_apply (hQS.notMem_bdry _ (List.getElem_mem _)),
        hPS.isOut_eq_true _ (List.getElem_mem _), hQS.isOut_eq_true _ (List.getElem_mem _)]
    · rw [List.head?_map, List.head?_reverse]
    · rw [List.head?_map, List.head?_reverse]

/-- A walk shortened to one without repeated darts, with its vertices pairwise distinct. -/
private theorem exists_short_walk (hX : X.IsPreTripleDiagram) (hmono : ¬X.HasMonogon)
    {K : List H} (hK0 : 0 < K.length) (hB : ∀ e ∈ K, e ∉ X.bdry) (hK : K.IsChain X.StrandStep)
    (hint : ¬X.IsBoundaryVertex (X.vertexOf K[0]))
    (hend : X.vertexOf (X.inv K[K.length - 1]) ≠ X.vertexOf K[0]) :
    ∃ K' : List H, ∃ hK'0 : 0 < K'.length, (∀ e ∈ K', e ∉ X.bdry) ∧ K'.IsChain X.StrandStep ∧
      K'[0] = K[0] ∧ K'[K'.length - 1] = K[K.length - 1] ∧
      (∀ t (ht : t < K'.length), X.vertexOf (X.inv K'[t]) ≠ X.vertexOf K'[0]) ∧
      ∀ s t (hs : s < t) (ht : t < K'.length),
        X.vertexOf (X.inv (K'[s]'(by omega))) ≠ X.vertexOf (X.inv K'[t]) := by
  obtain ⟨K', hc, hh, hl, hnd, hsub⟩ :=
    exists_isChain_nodup _ K rfl hK (List.ne_nil_of_length_pos hK0)
  have hK'0 : 0 < K'.length := by
    rcases K' with _ | ⟨k, K'⟩
    · simp [List.head?_eq_getElem?, List.getElem?_eq_getElem hK0] at hh
    · simp
  have h0 : K'[0] = K[0] := by
    rw [List.head?_eq_getElem?, List.head?_eq_getElem?, List.getElem?_eq_getElem hK'0,
      List.getElem?_eq_getElem hK0] at hh
    exact Option.some_injective _ hh
  have hl' : K'[K'.length - 1] = K[K.length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by omega)] at hl
    exact Option.some_injective _ hl
  have hB' : ∀ e ∈ K', e ∉ X.bdry := fun e he => hB e (hsub e he)
  obtain ⟨h1, h2⟩ := vertices_ne_of_isChain hX hmono hK'0 hB' hc hnd (by rw [h0]; exact hint)
    (by rw [h0, hl']; exact hend)
  exact ⟨K', hK'0, hB', hc, h0, hl', h1, h2⟩

/-- **A parallel digon on the two strands of the swivel digon**. Let `X'` be the swivel move of a
triple diagram `X` at a digon `{d₁, d₂}`, `d₂ = φ(d₁)`, with corners `x = v(d₁)` and `y = v(d₂)`
and rotations `(d̄₂, d₁, a₁, a₂, a₃, a₄)` at `x`, and suppose that `X` has no monogon. Let `(P, Q)`
be a parallel digon of `X` with corners `x` and `w ∉ {x, y}` such that the dart of `P` at `x` is
`d₁` or `a₃ = σ³(d₁)` and the dart of `Q` at `x` is `a₂ = σ²(d₁)` or `d̄₂`; the dart at `x` of a
strand path from `x` is its first dart, and of a strand path to `x` the reverse of its last dart.
Then `X'` has a badgon. -/
@[cluster_algebras "lem_badgon_digon_ab"]
theorem hasBadgon_swivelMove_of_isParallelDigon (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) (hmono : ¬X.HasMonogon) {P Q : List H} {w : Finset H}
    (hwy : w ≠ X.vertexOf (X.facePerm d₁))
    (hPQ : (X.IsParallelDigon P Q (X.vertexOf d₁) w ∧
        (P.head? = some d₁ ∨ P.head? = some ((X.rot ^ 3) d₁)) ∧
        (Q.head? = some ((X.rot ^ 2) d₁) ∨ Q.head? = some (X.inv (X.facePerm d₁)))) ∨
      (X.IsParallelDigon P Q w (X.vertexOf d₁) ∧
        (P.getLast?.map X.inv = some d₁ ∨ P.getLast?.map X.inv = some ((X.rot ^ 3) d₁)) ∧
        (Q.getLast?.map X.inv = some ((X.rot ^ 2) d₁) ∨
          Q.getLast?.map X.inv = some (X.inv (X.facePerm d₁))))) :
    (X.swivelMove d₁).HasBadgon := by
  have hpre := hX.toIsPreTripleDiagram
  obtain ⟨P₀, Q₀, hP0, hQ0, hPB, hQB, hPc, hQc, hPx, hQx, hPw, hQw, hlast, -, horient, hxint,
    hwint, hxw, hcase⟩ := exists_walks_of_isParallelDigon hpre (x := X.vertexOf d₁) (w := w)
      (hPQ.imp (fun h => h.1) (fun h => h.1))
  have hP0h := head?_eq_some_getElem hP0
  have hQ0h := head?_eq_some_getElem hQ0
  have hdarts : (P₀[0] = d₁ ∨ P₀[0] = (X.rot ^ 3) d₁) ∧
      (Q₀[0] = (X.rot ^ 2) d₁ ∨ Q₀[0] = X.inv (X.facePerm d₁)) := by
    rcases hPQ with ⟨h1, hp, hq⟩ | ⟨h1, hp, hq⟩ <;>
      rcases hcase with ⟨h2, hp', hq'⟩ | ⟨h2, hp', hq'⟩
    · rw [← hp', hP0h] at hp
      rw [← hq', hQ0h] at hq
      exact ⟨hp.imp (fun h => Option.some_injective _ h) (fun h => Option.some_injective _ h),
        hq.imp (fun h => Option.some_injective _ h) (fun h => Option.some_injective _ h)⟩
    · exact absurd (h1.pathStart_fst.symm.trans h2.pathStart_fst) hxw
    · exact absurd (h2.pathStart_fst.symm.trans h1.pathStart_fst) hxw
    · rw [← hp', hP0h] at hp
      rw [← hq', hQ0h] at hq
      exact ⟨hp.imp (fun h => Option.some_injective _ h) (fun h => Option.some_injective _ h),
        hq.imp (fun h => Option.some_injective _ h) (fun h => Option.some_injective _ h)⟩
  have hxint' := (X.mem_internalVertices.1 hxint).2
  have hwint' := (X.mem_internalVertices.1 hwint).2
  obtain ⟨P₁, hP₁0, hP₁B, hP₁c, hP₁0d, hP₁l, hD1P, hD2P⟩ := exists_short_walk hpre hmono hP0 hPB hPc
    (by rw [hPx]; exact hxint') (by rw [hPw, hPx]; exact hxw.symm)
  obtain ⟨Q₁, hQ₁0, hQ₁B, hQ₁c, hQ₁0d, hQ₁l, hD1Q, hD2Q⟩ := exists_short_walk hpre hmono hQ0 hQB hQc
    (by rw [hQx]; exact hxint') (by rw [hQw, hQx]; exact hxw.symm)
  have hw' : X.vertexOf (X.inv P₁[P₁.length - 1]) = X.vertexOf (X.inv Q₁[Q₁.length - 1]) := by
    rw [hP₁l, hQ₁l, hPw, hQw]
  have hwint'' : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P₁[P₁.length - 1])) := by
    rw [hP₁l, hPw]
    exact hwint'
  have hwy' : X.vertexOf (X.inv P₁[P₁.length - 1]) ≠ X.vertexOf (X.facePerm d₁) := by
    rw [hP₁l, hPw]
    exact hwy
  -- the orientations at `x`
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂⟩ := hd.exists_darts hpre
  have o2 : X.isOut ((X.rot ^ 2) d₁) = X.isOut d₁ := by
    rw [hpre.isOut_rot_pow_apply hi₁, if_pos (by decide)]
  have o3 : X.isOut ((X.rot ^ 3) d₁) = !X.isOut d₁ := hpre.isOut_rot_pow_three_apply hi₁
  have od₂ : X.isOut (X.inv (X.facePerm d₁)) = !X.isOut d₁ := by
    have hy : ¬X.IsBoundaryVertex (X.vertexOf (X.inv d₁)) := by
      rw [X.vertexOf_eq_of_mem (show X.inv d₁ ∈ X.vertexOf (X.facePerm d₁) by rw [hV₂]; simp)]
      exact hi₂
    rw [hpre.isOut_inv_apply hd.notMem_bdry.2, show X.facePerm d₁ = X.rot (X.inv d₁) from rfl,
      hpre.isOut_rot_apply hy, hpre.isOut_inv_apply hd.notMem_bdry.1]
    simp
  rcases hdarts with ⟨hp | hp, hq | hq⟩
  · exact hasBadgon_swivelMove_of_walks_from_one hX hd hmono hP₁0 hQ₁0 hP₁B hQ₁B hP₁c hQ₁c
      (by rw [hP₁0d, hp]) (by rw [hQ₁0d, hq]) hw' hwint'' hwy' hD1P hD2P hD1Q hD2Q
  · exfalso
    rw [hp, hq, od₂] at horient
    cases h : X.isOut d₁ <;> simp [h] at horient
  · exfalso
    rw [hp, hq, o2, o3] at horient
    cases h : X.isOut d₁ <;> simp [h] at horient
  · exact hasBadgon_swivelMove_of_walks_from_two hX hd hmono hP₁0 hQ₁0 hP₁B hQ₁B hP₁c hQ₁c
      (by rw [hP₁0d, hp]) (by rw [hQ₁0d, hq]) hw' hwint'' hwy' hD1P hD2P hD1Q hD2Q

/-- A walk closing up (its last dart followed by its first one) at triple points runs along a
closed strand, so a triple diagram with such a walk has a badgon. -/
private theorem hasBadgon_of_closed_walk (hX : X.IsTripleDiagram) {K : List H} (hK0 : 0 < K.length)
    (hB : ∀ k ∈ K, k ∉ X.bdry) (hK : K.IsChain X.StrandStep)
    (hint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv K[K.length - 1])))
    (hcyc : (X.rot ^ 3) (X.inv K[K.length - 1]) = K[0]) : X.HasBadgon := by
  have hKg := List.isChain_iff_getElem.1 hK
  have hS : ∀ e ∈ K, X.strandMap e ∈ K := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
    by_cases ht' : t + 1 < K.length
    · rw [(hKg t ht').strandMap_eq]
      exact List.getElem_mem _
    · have e : K[t] = K[K.length - 1] := by congr 1; omega
      rw [e, X.strandMap_of_not_runsToEndpoint hint]
      change (X.rot ^ 3) (X.inv K[K.length - 1]) ∈ K
      rw [hcyc]
      exact List.getElem_mem _
  have hSiter : ∀ m, X.strandMap^[m] K[0] ∈ K := by
    intro m
    induction m with
    | zero => exact List.getElem_mem _
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact hS _ ih
  have hKint : ∀ e ∈ K, ¬X.IsBoundaryVertex (X.vertexOf e) := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
    rcases t with _ | t
    · rw [← hcyc, X.vertexOf_rot_pow_apply]
      exact hint
    · rw [(hKg t ht).vertexOf_eq]
      exact (hKg t ht).1
  have hcl : X.IsClosedStrand (X.strandOrbit K[0]) := by
    refine ⟨K[0], hB _ (List.getElem_mem _), rfl, fun e he => ?_⟩
    obtain ⟨m, rfl⟩ := X.mem_strandOrbit.1 he
    exact hKint _ (hSiter m)
  by_contra h
  exact not_isClosedStrand_of_not_hasBadgon hX h _ hcl

/-- A dart not running to an endpoint is followed along its strand by its image under the strand
map. -/
private theorem strandStep_strandMap {e : H} (h : ¬X.RunsToEndpoint e) :
    X.StrandStep e (X.strandMap e) :=
  ⟨h, by rw [X.strandMap_of_not_runsToEndpoint h]; rfl⟩

/-- A dart runs to an endpoint in the swivel move exactly when it does in `X`. -/
private theorem runsToEndpoint_swivelMove_iff (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) (e : H) :
    (X.swivelMove d₁).RunsToEndpoint e ↔ X.RunsToEndpoint e :=
  hd.isBoundaryVertex_swivelMove_iff hX (X.inv e)

/-- Off `x ∪ y`, `σ'³ = σ³`. -/
private theorem rot_pow_three_swivelMove_of_notMem {d₁ z : H}
    (hz : z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) :
    ((X.swivelMove d₁).rot ^ 3) z = (X.rot ^ 3) z := by
  have h1 : X.rot z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun h' =>
    hz (rot_mem_union_vertexOf_iff.1 h')
  have h2 : X.rot (X.rot z) ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun h' =>
    h1 (rot_mem_union_vertexOf_iff.1 h')
  change (X.swivelRot d₁ ^ 3) z = _
  rw [X.rot_pow_three_apply, rot_pow_three_apply_perm, swivelRot_apply_of_notMem hz,
    swivelRot_apply_of_notMem h1, swivelRot_apply_of_notMem h2]

/-- The four darts `L* = {d₁, d̄₁, d₂, d̄₂}` of a digon: each lies at `x` or `y` and runs to the
other corner, and the strand through it continues with a dart outside `L*` at `x` or `y`. -/
private theorem mem_ls_facts (hX : X.IsPreTripleDiagram) {d₁ : H} (hd : X.IsDigon (X.faceOf d₁))
    {e : H} (he : e ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) :
    X.inv e ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) ∧ e ∉ X.bdry ∧
      (X.vertexOf e = X.vertexOf d₁ ∨ X.vertexOf e = X.vertexOf (X.facePerm d₁)) ∧
      X.vertexOf (X.inv e) ≠ X.vertexOf e ∧ ¬X.RunsToEndpoint e ∧
      (X.rot ^ 3) (X.inv e) ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) ∧
      (X.vertexOf ((X.rot ^ 3) (X.inv e)) = X.vertexOf d₁ ∨
        X.vertexOf ((X.rot ^ 3) (X.inv e)) = X.vertexOf (X.facePerm d₁)) := by
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂⟩ := hd.exists_darts hX
  have hφφ : X.rot (X.inv (X.facePerm d₁)) = d₁ := hd.facePerm_facePerm
  have hφ : X.rot (X.inv d₁) = X.facePerm d₁ := rfl
  have hxy := hd.vertexOf_ne
  obtain ⟨hB₁, hB₂⟩ := hd.notMem_bdry
  have hne : ∀ i j (hi : i < 12) (hj : j < 12), i ≠ j →
      [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][i] ≠
        [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][j] :=
    fun i j hi hj hij h => hij ((hnd.getElem_inj_iff (hi := by simpa using hi)
      (hj := by simpa using hj)).1 h)
  have nL : ∀ i (hi : i < 12), i ≠ 0 → i ≠ 11 → i ≠ 6 → i ≠ 5 →
      [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][i] ∉
        ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) := by
    intro i hi n0 n11 n6 n5
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hne i 0 hi (by norm_num) n0, hne i 11 hi (by norm_num) n11, hne i 6 hi (by norm_num) n6,
      hne i 5 hi (by norm_num) n5⟩
  have hvx : ∀ z ∈ ({d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁)} : Finset H),
      X.vertexOf z = X.vertexOf d₁ := fun z hz => X.vertexOf_eq_of_mem (by rw [hV₁]; exact hz)
  have hvy : ∀ z ∈ ({X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁} : Finset H),
      X.vertexOf z = X.vertexOf (X.facePerm d₁) :=
    fun z hz => X.vertexOf_eq_of_mem (by rw [hV₂]; exact hz)
  have hinv := hX.inv_inv_apply
  simp only [mem_insert, mem_singleton] at he
  rcases he with he | he | he | he <;> rw [he]
  · rw [X.rot_pow_three_apply, hφ, g1, g2]
    refine ⟨by simp, hB₁, Or.inl rfl, by rw [hvy (X.inv d₁) (by simp)]; exact hxy.symm, ?_,
      nL 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      Or.inr (hvy _ (by simp))⟩
    change ¬X.IsBoundaryVertex (X.vertexOf (X.inv d₁))
    rw [hvy (X.inv d₁) (by simp)]
    exact hi₂
  · rw [hinv, X.rot_pow_three_apply, h1, h2, h3]
    refine ⟨by simp, hX.inv_notMem_bdry hB₁, Or.inr (hvy _ (by simp)),
      by rw [hvy (X.inv d₁) (by simp)]; exact hxy, ?_,
      nL 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      Or.inl (hvx _ (by simp))⟩
    change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.inv d₁)))
    rw [hinv]
    exact hi₁
  · rw [X.rot_pow_three_apply, hφφ, h1, h2]
    refine ⟨by simp, hB₂, Or.inr rfl, by rw [hvx (X.inv (X.facePerm d₁)) (by simp)]; exact hxy, ?_,
      nL 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      Or.inl (hvx _ (by simp))⟩
    change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.facePerm d₁)))
    rw [hvx (X.inv (X.facePerm d₁)) (by simp)]
    exact hi₁
  · rw [hinv, X.rot_pow_three_apply, g1, g2, g3]
    refine ⟨by simp, hX.inv_notMem_bdry hB₂, Or.inl (hvx _ (by simp)),
      by rw [hvx (X.inv (X.facePerm d₁)) (by simp)]; exact hxy.symm, ?_,
      nL 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      Or.inr (hvy _ (by simp))⟩
    change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.inv (X.facePerm d₁))))
    rw [hinv]
    exact hi₂

/-- **Transport of walks** through the swivel move: a walk of `X` whose first and last darts lie
outside `L*` gives a walk of the swivel move with the same first and last darts. -/
private theorem exists_walk_swivelMove (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) :
    ∀ (n : ℕ) (K : List H) (hK0 : 0 < K.length), K.length = n → (∀ e ∈ K, e ∉ X.bdry) →
      K.IsChain X.StrandStep →
      K[0] ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) →
      K[K.length - 1] ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) →
      ∃ K' : List H, ∃ hK'0 : 0 < K'.length, (∀ e ∈ K', e ∉ X.bdry) ∧
        K'.IsChain (X.swivelMove d₁).StrandStep ∧ K'[0] = K[0] ∧
        K'[K'.length - 1] = K[K.length - 1] := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hK0 hn hB hK h0 hl
  have hKg := List.isChain_iff_getElem.1 hK
  by_cases h1 : K.length = 1
  · exact ⟨K, hK0, hB, List.isChain_iff_getElem.2 fun i hi => by omega, rfl, rfl⟩
  have hs0 := hKg 0 (by omega)
  obtain ⟨w, hwL, ⟨k, hk, hSk, hmid⟩, ⟨k', hk', hS'k, hS'mid⟩⟩ :=
    exists_iterate_strandMap_swivelMove hX hd h0 hs0.1
  -- the dart `w` is `K[m]`
  obtain ⟨m, hm1, hmK, hKm⟩ : ∃ m, 1 ≤ m ∧ ∃ hm : m < K.length, K[m] = w := by
    interval_cases k
    · refine ⟨1, le_rfl, by omega, ?_⟩
      rw [← hSk, Function.iterate_one, hs0.strandMap_eq]
    · have hK1 : K[1] ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) := by
        have := hmid 1 le_rfl le_rfl
        rwa [Function.iterate_one, hs0.strandMap_eq] at this
      have h2 : 2 < K.length := by
        by_contra h2
        have e : K[1] = K[K.length - 1] := by congr 1; omega
        exact hl (e ▸ hK1)
      refine ⟨2, by norm_num, h2, ?_⟩
      rw [← hSk, Function.iterate_succ_apply', Function.iterate_one, hs0.strandMap_eq,
        (hKg 1 h2).strandMap_eq]
  set Ls : Finset H := {d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} with hLs
  have hidx : ∀ i j (hi : i < K.length) (hj : j < K.length), i = j → K[i] = K[j] :=
    fun i j _ _ h => by subst h; rfl
  have hK₂0 : 0 < (K.drop m).length := by simp; omega
  obtain ⟨K'', hK''0, hB'', hK'', h0'', hl''⟩ := ih (K.drop m).length (by simp; omega) (K.drop m)
    hK₂0 rfl (fun e he => hB e (List.mem_of_mem_drop he)) (hK.drop m)
    (by simp only [List.getElem_drop, Nat.add_zero]; rw [hKm]; exact hwL)
    (by simp only [List.getElem_drop, List.length_drop]
        rw [hidx _ (K.length - 1) _ (by omega) (by omega)]; exact hl)
  have hl₂ : K''[K''.length - 1] = K[K.length - 1] := by
    rw [hl'']
    simp only [List.getElem_drop, List.length_drop]
    congr 1
    omega
  have h0₂ : K''[0] = w := by
    rw [h0'']
    simp only [List.getElem_drop, Nat.add_zero]
    exact hKm
  set X' := X.swivelMove d₁ with hX'
  have hnr : ¬X'.RunsToEndpoint K[0] := (runsToEndpoint_swivelMove_iff hX hd _).not.2 hs0.1
  obtain ⟨k'', K₃, rfl⟩ : ∃ k'' K₃, K'' = k'' :: K₃ := by
    rcases K'' with _ | ⟨k'', K₃⟩
    · simp at hK''0
    · exact ⟨k'', K₃, rfl⟩
  simp only [List.getElem_cons_zero] at h0₂
  interval_cases k'
  · refine ⟨K[0] :: k'' :: K₃, by simp, fun e he => ?_, ?_, rfl, ?_⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact hB _ (List.getElem_mem _)
      · exact hB'' e he
    · refine List.isChain_cons_cons.2 ⟨?_, hK''⟩
      rw [h0₂, ← hS'k, Function.iterate_one]
      exact strandStep_strandMap hnr
    · rw [← hl₂]
      simp
  · have hmidL := hS'mid 1 le_rfl le_rfl
    rw [Function.iterate_one] at hmidL
    obtain ⟨-, hmB, -, -, hmr, -, -⟩ := mem_ls_facts hX hd hmidL
    have hmr' : ¬X'.RunsToEndpoint (X'.strandMap K[0]) :=
      (runsToEndpoint_swivelMove_iff hX hd _).not.2 hmr
    refine ⟨K[0] :: X'.strandMap K[0] :: k'' :: K₃, by simp, fun e he => ?_, ?_, rfl, ?_⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact hB _ (List.getElem_mem _)
      rcases List.mem_cons.1 he with rfl | he
      · exact hmB
      · exact hB'' e he
    · refine List.isChain_cons_cons.2 ⟨strandStep_strandMap hnr,
        List.isChain_cons_cons.2 ⟨?_, hK''⟩⟩
      rw [h0₂, ← hS'k, Function.iterate_succ_apply', Function.iterate_one]
      exact strandStep_strandMap hmr'
    · rw [← hl₂]
      simp

/-- In the swivel move, a walk from `x ∪ y` back to `x ∪ y` whose first and last darts lie outside
`L*` gives a badgon: a monogon or a closed strand if it comes back to its first vertex, and a
parallel digon with one of the darts of `L*` otherwise. -/
private theorem hasBadgon_swivelMove_of_walk_xy (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {K : List H} (hK0 : 0 < K.length)
    (hB : ∀ e ∈ K, e ∉ X.bdry) (hK : K.IsChain (X.swivelMove d₁).StrandStep)
    (h0 : K[0] ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (hl : X.inv K[K.length - 1] ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (h0L : K[0] ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H))
    (hlL : K[K.length - 1] ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) :
    (X.swivelMove d₁).HasBadgon := by
  have hpre := hX.toIsPreTripleDiagram
  have hX' := hd.isTripleDiagram_swivelMove hX
  have hX'pre := hX'.toIsPreTripleDiagram
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂, -, -, -, -, -, -, -, -, -, -, -, -, hW₁, hW₂⟩ := hd.exists_swivel hpre
  have hne : ∀ i j (hi : i < 12) (hj : j < 12), i ≠ j →
      [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][i] ≠
        [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][j] :=
    fun i j hi hj hij h => hij ((hnd.getElem_inj_iff (hi := by simpa using hi)
      (hj := by simpa using hj)).1 h)
  obtain ⟨hB₁, hB₂⟩ := hd.notMem_bdry
  set X' := X.swivelMove d₁ with hX'def
  have hxy' : ∀ z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁),
      X'.vertexOf z = X'.vertexOf d₁ ∨ X'.vertexOf z = X'.vertexOf (X.facePerm d₁) := by
    intro z hz
    rw [hV₁, hV₂] at hz
    have hz' : z ∈ X'.vertexOf d₁ ∨ z ∈ X'.vertexOf (X.facePerm d₁) := by
      rw [hW₁, hW₂]
      simp only [mem_union, mem_insert, mem_singleton] at hz ⊢
      tauto
    exact hz'.imp X'.vertexOf_eq_of_mem X'.vertexOf_eq_of_mem
  have hint' : ∀ z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁),
      ¬X'.IsBoundaryVertex (X'.vertexOf z) := fun z hz =>
    (hd.vertexOf_swivelMove_of_mem hpre hz).2.1
  have vid₂ : X'.vertexOf (X.inv (X.facePerm d₁)) = X'.vertexOf d₁ :=
    X'.vertexOf_eq_of_mem (by rw [hW₁]; simp)
  have vid₁ : X'.vertexOf (X.inv d₁) = X'.vertexOf (X.facePerm d₁) :=
    X'.vertexOf_eq_of_mem (by rw [hW₂]; simp)
  -- the orientations of the darts of `L*`
  have hy : ¬X.IsBoundaryVertex (X.vertexOf (X.inv d₁)) := by
    rw [X.vertexOf_eq_of_mem (show X.inv d₁ ∈ X.vertexOf (X.facePerm d₁) by rw [hV₂]; simp)]
    exact hi₂
  have oid₁ : X.isOut (X.inv d₁) = !X.isOut d₁ := hpre.isOut_inv_apply hB₁
  have od₂ : X.isOut (X.facePerm d₁) = X.isOut d₁ := by
    rw [show X.facePerm d₁ = X.rot (X.inv d₁) from rfl, hpre.isOut_rot_apply hy, oid₁]
    simp
  have oid₂ : X.isOut (X.inv (X.facePerm d₁)) = !X.isOut d₁ := by
    rw [hpre.isOut_inv_apply hB₂, od₂]
  have hhd : K.head (List.ne_nil_of_length_pos hK0) = K[0] := List.head_eq_getElem _
  have hlt : K.getLast (List.ne_nil_of_length_pos hK0) = K[K.length - 1] :=
    List.getLast_eq_getElem _
  by_cases hv : X'.vertexOf (X.inv K[K.length - 1]) = X'.vertexOf K[0]
  · by_cases hp : X.inv K[K.length - 1] = (X'.rot ^ 3) K[0]
    · exact hasBadgon_of_closed_walk hX' hK0 hB hK (hint' _ hl)
        (by
          change (X'.rot ^ 3) (X.inv K[K.length - 1]) = K[0]
          rw [hp]
          exact hX'pre.rot_pow_three_rot_pow_three (hint' _ h0))
    · refine Or.inl (hasMonogon_of_isChain hX'pre (List.ne_nil_of_length_pos hK0) hB hK ?_ ?_ ?_)
      · rw [hhd]
        exact hint' _ h0
      · rw [hhd, hlt]
        exact hv
      · rw [hhd, hlt]
        exact hp
  · obtain ⟨s, hsL, hs0, hs1, hso⟩ : ∃ s ∈ ({d₁, X.inv d₁, X.facePerm d₁,
        X.inv (X.facePerm d₁)} : Finset H), X'.vertexOf s = X'.vertexOf K[0] ∧
        X'.vertexOf (X.inv s) = X'.vertexOf (X.inv K[K.length - 1]) ∧
        X.isOut s = X.isOut K[0] := by
      rcases hxy' _ h0 with hx0 | hy0 <;> rcases hxy' _ hl with hxl | hyl
      · exact absurd (hxl.trans hx0.symm) hv
      · by_cases ho : X.isOut d₁ = X.isOut K[0]
        · exact ⟨d₁, by simp, hx0.symm, by rw [vid₁, hyl], ho⟩
        · refine ⟨X.inv (X.facePerm d₁), by simp, by rw [vid₂, hx0],
            by rw [hpre.inv_inv_apply, hyl], ?_⟩
          rw [oid₂]
          revert ho
          cases X.isOut d₁ <;> cases X.isOut K[0] <;> simp
      · by_cases ho : X.isOut d₁ = X.isOut K[0]
        · exact ⟨X.facePerm d₁, by simp, hy0.symm, by rw [vid₂, hxl], by rw [od₂]; exact ho⟩
        · refine ⟨X.inv d₁, by simp, by rw [vid₁, hy0], by rw [hpre.inv_inv_apply, hxl], ?_⟩
          rw [oid₁]
          revert ho
          cases X.isOut d₁ <;> cases X.isOut K[0] <;> simp
      · exact absurd (hyl.trans hy0.symm) hv
    have hsB : s ∉ X.bdry := (mem_ls_facts hpre hd hsL).2.1
    refine Or.inr (hasParallelDigon_of_isChain hX'pre (A := K) (B := [s])
      (List.ne_nil_of_length_pos hK0) (List.cons_ne_nil _ _) hB
      (fun e he => by rw [List.mem_singleton.1 he]; exact hsB) hK (List.isChain_singleton _)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      simp only [hhd, hlt, List.head_cons, List.getLast_singleton]
    · exact hso.symm
    · exact hs0.symm
    · exact hs1.symm
    · exact hint' _ h0
    · exact hint' _ hl
    · exact fun h => hv h.symm
    · exact fun h => h0L (h ▸ hsL)
    · exact fun h => hlL (h ▸ hsL)

/-- **Trimming the head of a walk** starting at `x ∪ y`: dropping a first dart in `L*` leaves a
walk starting at `x ∪ y` outside `L*`. -/
private theorem exists_trim_head (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {K : List H} (hK0 : 0 < K.length)
    (hB : ∀ e ∈ K, e ∉ X.bdry) (hK : K.IsChain X.StrandStep)
    (h0 : K[0] ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (hex : ∃ e ∈ K, e ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) :
    ∃ K₁ : List H, ∃ hK₁0 : 0 < K₁.length, (∀ e ∈ K₁, e ∉ X.bdry) ∧ K₁.IsChain X.StrandStep ∧
      K₁[0] ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) ∧
      K₁[0] ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) ∧
      K₁[K₁.length - 1] = K[K.length - 1] ∧
      (K[0] ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) →
        K₁[0] = K[0]) ∧
      (K[0] ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) →
        K₁[0] = (X.rot ^ 3) (X.inv K[0])) := by
  by_cases h : K[0] ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)
  · have h2 : 1 < K.length := by
      obtain ⟨e, he, heL⟩ := hex
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
      by_contra h2
      have : t = 0 := by omega
      subst this
      exact heL h
    have hs := (List.isChain_iff_getElem.1 hK) 0 h2
    simp only [Nat.zero_add] at hs
    obtain ⟨-, -, -, -, -, hn, hm⟩ := mem_ls_facts hX hd h
    have hK1 : (K.drop 1)[0]'(by simp; omega) = K[1] := by simp
    refine ⟨K.drop 1, by simp; omega, fun e he => hB e (List.mem_of_mem_drop he), hK.drop 1, ?_,
      ?_, ?_, fun h' => absurd h h', fun _ => ?_⟩
    · rw [hK1, hs.2]
      exact hn
    · rw [hK1, hs.2]
      exact mem_union_vertexOf_iff.2 hm
    · simp only [List.getElem_drop, List.length_drop]
      congr 1
      omega
    · rw [hK1, hs.2]
  · exact ⟨K, hK0, hB, hK, h, h0, rfl, fun _ => rfl, fun h' => absurd h' h⟩

/-- **Trimming the end of a walk** ending at `x ∪ y`: dropping a last dart in `L*` leaves a walk
ending at `x ∪ y` with its last dart outside `L*`. -/
private theorem exists_trim_last (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {K : List H} (hK0 : 0 < K.length)
    (hB : ∀ e ∈ K, e ∉ X.bdry) (hK : K.IsChain X.StrandStep)
    (hl : X.inv K[K.length - 1] ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (h0 : K[0] ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) :
    ∃ K₁ : List H, ∃ hK₁0 : 0 < K₁.length, (∀ e ∈ K₁, e ∉ X.bdry) ∧ K₁.IsChain X.StrandStep ∧
      K₁[K₁.length - 1] ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) ∧
      X.inv K₁[K₁.length - 1] ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) ∧
      K₁[0] = K[0] := by
  by_cases h : K[K.length - 1] ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)
  · have h2 : 1 < K.length := by
      by_contra h2
      have e : K[0] = K[K.length - 1] := by congr 1; omega
      exact h0 (e ▸ h)
    have hs := ((List.isChain_iff_getElem.1 hK) (K.length - 2) (by omega)).inv_inv hX
    have e : K[K.length - 2 + 1] = K[K.length - 1] := by congr 1; omega
    rw [e] at hs
    have h' := (mem_ls_facts hX hd h).1
    obtain ⟨-, -, -, -, -, hn, hm⟩ := mem_ls_facts hX hd h'
    have hK₁l : (K.take (K.length - 1))[(K.take (K.length - 1)).length - 1]'(by simp; omega) =
        K[K.length - 2] := by
      simp only [List.getElem_take, List.length_take]
      congr 1
      omega
    refine ⟨K.take (K.length - 1), by simp; omega,
      fun e he => hB e (List.mem_of_mem_take he), hK.take _, ?_, ?_, by simp⟩
    · rw [hK₁l]
      intro hL
      apply hn
      rw [← hs.2]
      exact (mem_ls_facts hX hd hL).1
    · rw [hK₁l, hs.2]
      exact mem_union_vertexOf_iff.2 hm
  · exact ⟨K, hK0, hB, hK, h, hl, rfl⟩

/-- **A walk of `X` from `x ∪ y` back to `x ∪ y`** through a dart outside `L*` gives a badgon of
the swivel move. -/
private theorem hasBadgon_swivelMove_of_walk (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {K : List H} (hK0 : 0 < K.length)
    (hB : ∀ e ∈ K, e ∉ X.bdry) (hK : K.IsChain X.StrandStep)
    (h0 : K[0] ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (hl : X.inv K[K.length - 1] ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (hex : ∃ e ∈ K, e ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) :
    (X.swivelMove d₁).HasBadgon := by
  have hpre := hX.toIsPreTripleDiagram
  obtain ⟨K₁, hK₁0, hB₁, hK₁, h0L, h0m, hl₁, -, -⟩ := exists_trim_head hpre hd hK0 hB hK h0 hex
  obtain ⟨K₂, hK₂0, hB₂, hK₂, hlL, hlm, h0₂⟩ :=
    exists_trim_last hpre hd hK₁0 hB₁ hK₁ (by rw [hl₁]; exact hl) h0L
  obtain ⟨K', hK'0, hB', hK', h0', hl'⟩ := exists_walk_swivelMove hpre hd _ K₂ hK₂0 rfl hB₂ hK₂
    (by rw [h0₂]; exact h0L) hlL
  exact hasBadgon_swivelMove_of_walk_xy hX hd hK'0 hB' hK' (by rw [h0', h0₂]; exact h0m)
    (by rw [hl']; exact hlm) (by rw [h0', h0₂]; exact h0L) (by rw [hl']; exact hlL)

/-- **Monogons away from the digon** survive the swivel move. -/
private theorem hasMonogon_swivelMove_of_isMonogon (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {P : List H} (hP : X.IsMonogon P)
    (hvx : X.pathStart P ≠ X.vertexOf d₁) (hvy : X.pathStart P ≠ X.vertexOf (X.facePerm d₁)) :
    (X.swivelMove d₁).HasMonogon := by
  have hX'pre := hd.isPreTripleDiagram_swivelMove hX
  have hS := hP.isStrandPath
  have hP0 : 0 < P.length := List.length_pos_iff.2 hS.ne_nil
  have hPh := head?_eq_some_getElem hP0
  have hPl := getLast?_eq_some_getElem hP0
  have hv0 : X.vertexOf P[0] = X.pathStart P := (X.pathStart_of_head? hPh).symm
  have hvl : X.vertexOf (X.inv P[P.length - 1]) = X.pathStart P := by
    rw [← X.pathEnd_of_getLast? hPl]
    exact hP.pathEnd_eq
  have hnot : ∀ e, X.vertexOf e = X.pathStart P →
      e ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun e he h =>
    (mem_union_vertexOf_iff.1 h).elim (fun h' => hvx (he.symm.trans h'))
      (fun h' => hvy (he.symm.trans h'))
  have hnotL : ∀ e, X.vertexOf e = X.pathStart P →
      e ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) := fun e he hL =>
    hnot e he (mem_union_vertexOf_iff.2 (mem_ls_facts hX hd hL).2.2.1)
  obtain ⟨K', hK'0, hB', hK', h0', hl'⟩ := exists_walk_swivelMove hX hd _ P hP0 rfl
    hS.notMem_bdry hS.isChain (hnotL _ hv0) (fun hL => hnotL _ hvl (mem_ls_facts hX hd hL).1)
  have hint : ¬X.IsBoundaryVertex (X.pathStart P) := (X.mem_internalVertices.1 hP.pathStart_mem).2
  refine hasMonogon_of_isChain hX'pre (List.ne_nil_of_length_pos hK'0) hB' hK' ?_ ?_ ?_ <;>
    simp only [List.head_eq_getElem, List.getLast_eq_getElem, h0', hl', swivelMove_inv]
  · rw [hd.isBoundaryVertex_swivelMove_iff hX, hv0]
    exact hint
  · rw [vertexOf_swivelMove_of_notMem (hnot _ hvl), vertexOf_swivelMove_of_notMem (hnot _ hv0),
      hvl, hv0]
  · rw [rot_pow_three_swivelMove_of_notMem (hnot _ hv0)]
    exact hP.inv_ne _ hPh _ hPl

/-- **Parallel digons away from the digon** survive the swivel move. -/
private theorem hasParallelDigon_swivelMove_of_away (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {P Q : List H} {u w : Finset H}
    (h : X.IsParallelDigon P Q u w) (hux : u ≠ X.vertexOf d₁) (huy : u ≠ X.vertexOf (X.facePerm d₁))
    (hwx : w ≠ X.vertexOf d₁) (hwy : w ≠ X.vertexOf (X.facePerm d₁)) :
    (X.swivelMove d₁).HasParallelDigon := by
  have hX'pre := hd.isPreTripleDiagram_swivelMove hX
  have hPS := h.isStrandPath_fst
  have hQS := h.isStrandPath_snd
  have hP0 : 0 < P.length := List.length_pos_iff.2 hPS.ne_nil
  have hQ0 : 0 < Q.length := List.length_pos_iff.2 hQS.ne_nil
  have hPh := head?_eq_some_getElem hP0
  have hQh := head?_eq_some_getElem hQ0
  have hPl := getLast?_eq_some_getElem hP0
  have hQl := getLast?_eq_some_getElem hQ0
  have hP0v : X.vertexOf P[0] = u := by rw [← h.pathStart_fst, X.pathStart_of_head? hPh]
  have hQ0v : X.vertexOf Q[0] = u := by rw [← h.pathStart_snd, X.pathStart_of_head? hQh]
  have hPlv : X.vertexOf (X.inv P[P.length - 1]) = w := by
    rw [← h.pathEnd_fst, X.pathEnd_of_getLast? hPl]
  have hQlv : X.vertexOf (X.inv Q[Q.length - 1]) = w := by
    rw [← h.pathEnd_snd, X.pathEnd_of_getLast? hQl]
  have hnot : ∀ e, (X.vertexOf e = u ∨ X.vertexOf e = w) →
      e ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := by
    rintro e (he | he) h' <;> rcases mem_union_vertexOf_iff.1 h' with h'' | h''
    · exact hux (he.symm.trans h'')
    · exact huy (he.symm.trans h'')
    · exact hwx (he.symm.trans h'')
    · exact hwy (he.symm.trans h'')
  have hnotL : ∀ e, (X.vertexOf e = u ∨ X.vertexOf e = w) →
      e ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) := fun e he hL =>
    hnot e he (mem_union_vertexOf_iff.2 (mem_ls_facts hX hd hL).2.2.1)
  obtain ⟨P', hP'0, hBP', hP', hP'0d, hP'l⟩ := exists_walk_swivelMove hX hd _ P hP0 rfl
    hPS.notMem_bdry hPS.isChain (hnotL _ (Or.inl hP0v))
    (fun hL => hnotL _ (Or.inr hPlv) (mem_ls_facts hX hd hL).1)
  obtain ⟨Q', hQ'0, hBQ', hQ', hQ'0d, hQ'l⟩ := exists_walk_swivelMove hX hd _ Q hQ0 rfl
    hQS.notMem_bdry hQS.isChain (hnotL _ (Or.inl hQ0v))
    (fun hL => hnotL _ (Or.inr hQlv) (mem_ls_facts hX hd hL).1)
  refine hasParallelDigon_of_isChain hX'pre (List.ne_nil_of_length_pos hP'0)
    (List.ne_nil_of_length_pos hQ'0) hBP' hBQ' hP' hQ' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [List.head_eq_getElem, List.getLast_eq_getElem, hP'0d, hQ'0d, hP'l, hQ'l,
      swivelMove_inv, swivelMove_isOut]
  · rw [hPS.isOut_eq_true _ (List.getElem_mem _), hQS.isOut_eq_true _ (List.getElem_mem _)]
  · rw [vertexOf_swivelMove_of_notMem (hnot _ (Or.inl hP0v)),
      vertexOf_swivelMove_of_notMem (hnot _ (Or.inl hQ0v)), hP0v, hQ0v]
  · rw [vertexOf_swivelMove_of_notMem (hnot _ (Or.inr hPlv)),
      vertexOf_swivelMove_of_notMem (hnot _ (Or.inr hQlv)), hPlv, hQlv]
  · rw [hd.isBoundaryVertex_swivelMove_iff hX, hP0v]
    exact (X.mem_internalVertices.1 h.mem_left).2
  · rw [hd.isBoundaryVertex_swivelMove_iff hX, hPlv]
    exact (X.mem_internalVertices.1 h.mem_right).2
  · rw [vertexOf_swivelMove_of_notMem (hnot _ (Or.inl hP0v)),
      vertexOf_swivelMove_of_notMem (hnot _ (Or.inr hPlv)), hP0v, hPlv]
    exact h.ne
  · intro he
    exact h.head?_ne (by rw [hPh, hQh, he])
  · intro he
    exact h.getLast?_ne (by rw [hPl, hQl, he])

/-- At a digon `f(d₁)` of a pre-triple diagram, the swivel move at `φ(d₁)` is the swivel move at
`d₁`. -/
private theorem swivelMove_facePerm (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) : X.swivelMove (X.facePerm d₁) = X.swivelMove d₁ := by
  have hφφ := hd.facePerm_facePerm
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, -⟩ :=
    hd.exists_darts hX
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := X.swivelRot_of_darts h1 h2 h3 h4 h5 g1 g2 g3 g4 g5
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]; grind)
  have key : X.swivelRot (X.facePerm d₁) = X.swivelRot d₁ := by
    generalize hd₂ : X.facePerm d₁ = d₂ at *
    obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := X.swivelRot_of_darts (d₁ := d₂) g1 g2 g3 g4
      (by rw [hφφ]; exact g5) (by rw [hφφ]; exact h1) h2 h3 h4 h5
      (by rw [hφφ]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        not_or, List.nodup_nil, and_true]; grind)
    rw [hφφ] at t5 t6 t7
    ext z
    by_cases e1 : z = d₁
    · subst e1; rw [s1, t5]
    by_cases e2 : z = a₂
    · subst e2; rw [s2, t6]
    by_cases e3 : z = a₄
    · subst e3; rw [s4, t3]
    by_cases e4 : z = d₂
    · subst e4; rw [s5, t1]
    by_cases e5 : z = b₂
    · subst e5; rw [s6, t2]
    by_cases e6 : z = b₄
    · subst e6; rw [s3, t4]
    rw [s7 z e1 e2 e3 e4 e5 e6, t7 z e4 e5 e6 e1 e2 e3]
  unfold swivelMove
  rw [key]

/-- In the swivel move, the darts of `L*` still run between its two vertices at the digon. -/
private theorem vertexOf_inv_ne_swivelMove (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {e : H}
    (he : e ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) :
    (X.swivelMove d₁).vertexOf (X.inv e) ≠ (X.swivelMove d₁).vertexOf e := by
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, -, hnd, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hW₁, hW₂⟩ := hd.exists_swivel hX
  have hne : ∀ i j (hi : i < 12) (hj : j < 12), i ≠ j →
      [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][i] ≠
        [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][j] :=
    fun i j hi hj hij h => hij ((hnd.getElem_inj_iff (hi := by simpa using hi)
      (hj := by simpa using hj)).1 h)
  set X' := X.swivelMove d₁ with hX'
  have hx'y' : X'.vertexOf d₁ ≠ X'.vertexOf (X.facePerm d₁) := by
    intro h
    have : d₁ ∈ X'.vertexOf (X.facePerm d₁) := h ▸ X'.self_mem_vertexOf d₁
    rw [hW₂] at this
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h' | h' | h' | h' | h'
    · exact hne 0 11 (by norm_num) (by norm_num) (by norm_num) h'
    · exact hne 0 6 (by norm_num) (by norm_num) (by norm_num) h'
    · exact hne 0 9 (by norm_num) (by norm_num) (by norm_num) h'
    · exact hne 0 10 (by norm_num) (by norm_num) (by norm_num) h'
    · exact hne 0 1 (by norm_num) (by norm_num) (by norm_num) h'
    · exact hne 0 2 (by norm_num) (by norm_num) (by norm_num) h'
  have vid₂ : X'.vertexOf (X.inv (X.facePerm d₁)) = X'.vertexOf d₁ :=
    X'.vertexOf_eq_of_mem (by rw [hW₁]; simp)
  have vid₁ : X'.vertexOf (X.inv d₁) = X'.vertexOf (X.facePerm d₁) :=
    X'.vertexOf_eq_of_mem (by rw [hW₂]; simp)
  have hinv := hX.inv_inv_apply
  simp only [mem_insert, mem_singleton] at he
  rcases he with he | he | he | he <;> rw [he]
  · rw [vid₁]
    exact hx'y'.symm
  · rw [hinv, vid₁]
    exact hx'y'
  · rw [vid₂]
    exact hx'y'
  · rw [hinv, vid₂]
    exact hx'y'.symm

/-- **Prepending a dart of `L*`**: in the swivel move, a dart `e` at `x ∪ y` whose pass partner
`σ'³(e)` lies in `L*` is entered from the other vertex of the digon along `σ'³(e)` reversed. -/
private theorem exists_prepend_swivelMove (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {e : H} (he : e ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (hγ : ((X.swivelMove d₁).rot ^ 3) e ∈
      ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) :
    X.inv (((X.swivelMove d₁).rot ^ 3) e) ∈
        ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) ∧
      (X.swivelMove d₁).StrandStep (X.inv (((X.swivelMove d₁).rot ^ 3) e)) e ∧
      (X.swivelMove d₁).vertexOf (X.inv (((X.swivelMove d₁).rot ^ 3) e)) ≠
        (X.swivelMove d₁).vertexOf e ∧
      X.isOut (X.inv (((X.swivelMove d₁).rot ^ 3) e)) = X.isOut e := by
  have hpre := hX.toIsPreTripleDiagram
  have hX'pre := hd.isPreTripleDiagram_swivelMove hpre
  have hint : ¬(X.swivelMove d₁).IsBoundaryVertex ((X.swivelMove d₁).vertexOf e) :=
    (hd.vertexOf_swivelMove_of_mem hpre he).2.1
  have hiL := (mem_ls_facts hpre hd hγ).1
  obtain ⟨-, -, -, -, hr, -, -⟩ := mem_ls_facts hpre hd hiL
  refine ⟨hiL, ⟨(runsToEndpoint_swivelMove_iff hpre hd _).not.2 hr, ?_⟩, ?_, ?_⟩
  · change e = ((X.swivelMove d₁).rot ^ 3) (X.inv (X.inv (((X.swivelMove d₁).rot ^ 3) e)))
    rw [hpre.inv_inv_apply]
    exact (hX'pre.rot_pow_three_rot_pow_three hint).symm
  · have := vertexOf_inv_ne_swivelMove hpre hd hγ
    rwa [(X.swivelMove d₁).vertexOf_rot_pow_apply] at this
  · rw [hpre.isOut_inv_apply (mem_ls_facts hpre hd hγ).2.1]
    have := hX'pre.isOut_rot_pow_three_apply hint
    simp only [swivelMove_isOut] at this
    rw [this, Bool.not_not]

/-- The darts at `x ∪ y` outside `L*` whose pass partner in the swivel move lies outside `L*`:
`a₂, a₃, b₂, b₃`, with their vertices in the swivel move and their orientations. -/
private theorem eq_of_rot_pow_three_swivelMove_notMem (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {e : H} (he : e ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (heL : e ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H))
    (hγ : ((X.swivelMove d₁).rot ^ 3) e ∉
      ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) :
    (e = (X.rot ^ 2) d₁ ∧
        (X.swivelMove d₁).vertexOf e = (X.swivelMove d₁).vertexOf (X.facePerm d₁) ∧
        X.isOut e = X.isOut d₁) ∨
      (e = (X.rot ^ 3) d₁ ∧ (X.swivelMove d₁).vertexOf e = (X.swivelMove d₁).vertexOf d₁ ∧
        X.isOut e = !X.isOut d₁) ∨
      (e = (X.rot ^ 2) (X.facePerm d₁) ∧
        (X.swivelMove d₁).vertexOf e = (X.swivelMove d₁).vertexOf d₁ ∧ X.isOut e = X.isOut d₁) ∨
      (e = (X.rot ^ 3) (X.facePerm d₁) ∧
        (X.swivelMove d₁).vertexOf e = (X.swivelMove d₁).vertexOf (X.facePerm d₁) ∧
        X.isOut e = !X.isOut d₁) := by
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, hW₁, hW₂⟩ := hd.exists_swivel hX
  obtain ⟨hB₁, hB₂⟩ := hd.notMem_bdry
  have hy : ¬X.IsBoundaryVertex (X.vertexOf (X.inv d₁)) := by
    rw [X.vertexOf_eq_of_mem (show X.inv d₁ ∈ X.vertexOf (X.facePerm d₁) by rw [hV₂]; simp)]
    exact hi₂
  have od₂ : X.isOut (X.facePerm d₁) = X.isOut d₁ := by
    rw [show X.facePerm d₁ = X.rot (X.inv d₁) from rfl, hX.isOut_rot_apply hy,
      hX.isOut_inv_apply hB₁]
    simp
  have p2 : (X.rot ^ 2) d₁ = a₂ := by rw [pow_two, Equiv.Perm.mul_apply, h1, h2]
  have p3 : (X.rot ^ 3) d₁ = a₃ := by rw [X.rot_pow_three_apply, h1, h2, h3]
  have q2 : (X.rot ^ 2) (X.facePerm d₁) = b₂ := by rw [pow_two, Equiv.Perm.mul_apply, g1, g2]
  have q3 : (X.rot ^ 3) (X.facePerm d₁) = b₃ := by rw [X.rot_pow_three_apply, g1, g2, g3]
  have o2 : X.isOut a₂ = X.isOut d₁ := by
    rw [← p2, hX.isOut_rot_pow_apply hi₁, if_pos (by decide)]
  have o3 : X.isOut a₃ = !X.isOut d₁ := by rw [← p3, hX.isOut_rot_pow_three_apply hi₁]
  have o2' : X.isOut b₂ = X.isOut d₁ := by
    rw [← q2, hX.isOut_rot_pow_apply hi₂, if_pos (by decide), od₂]
  have o3' : X.isOut b₃ = !X.isOut d₁ := by rw [← q3, hX.isOut_rot_pow_three_apply hi₂, od₂]
  have hr : ∀ z, ((X.swivelMove d₁).rot ^ 3) z =
      X.swivelRot d₁ (X.swivelRot d₁ (X.swivelRot d₁ z)) :=
    fun z => rfl
  rw [hr] at hγ
  rw [hV₁, hV₂] at he
  simp only [mem_union, mem_insert, mem_singleton] at he
  simp only [mem_insert, mem_singleton, not_or] at heL hγ
  rcases he with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact absurd rfl heL.1
  · rw [s11, s12, s7] at hγ
    exact absurd rfl hγ.2.2.1
  · exact Or.inl ⟨p2.symm, X.swivelMove d₁ |>.vertexOf_eq_of_mem (by rw [hW₂]; simp), o2⟩
  · exact Or.inr (Or.inl ⟨p3.symm, X.swivelMove d₁ |>.vertexOf_eq_of_mem (by rw [hW₁]; simp), o3⟩)
  · rw [s3, s4, s5] at hγ
    exact absurd rfl hγ.2.2.2
  · exact absurd rfl heL.2.2.2
  · exact absurd rfl heL.2.2.1
  · rw [s4, s5, s6] at hγ
    exact absurd rfl hγ.1
  · exact Or.inr (Or.inr (Or.inl ⟨q2.symm, X.swivelMove d₁ |>.vertexOf_eq_of_mem
      (by rw [hW₁]; simp), o2'⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨q3.symm, X.swivelMove d₁ |>.vertexOf_eq_of_mem
      (by rw [hW₂]; simp), o3'⟩))
  · rw [s10, s11, s12] at hγ
    exact absurd rfl hγ.2.1
  · exact absurd rfl heL.2.1

/-- In the swivel move, the darts at `x ∪ y` lie at its vertices through `d₁` and `d₂`. -/
private theorem vertexOf_swivelMove_eq_or (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {z : H} (hz : z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) :
    (X.swivelMove d₁).vertexOf z = (X.swivelMove d₁).vertexOf d₁ ∨
      (X.swivelMove d₁).vertexOf z = (X.swivelMove d₁).vertexOf (X.facePerm d₁) := by
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, -, -, hV₁, hV₂, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, hW₁, hW₂⟩ := hd.exists_swivel hX
  rw [hV₁, hV₂] at hz
  have hz' : z ∈ (X.swivelMove d₁).vertexOf d₁ ∨
      z ∈ (X.swivelMove d₁).vertexOf (X.facePerm d₁) := by
    rw [hW₁, hW₂]
    simp only [mem_union, mem_insert, mem_singleton] at hz ⊢
    tauto
  exact hz'.imp (X.swivelMove d₁).vertexOf_eq_of_mem (X.swivelMove d₁).vertexOf_eq_of_mem

/-- Two walks of the swivel move from one vertex in `x ∪ y` to a common vertex `u ∉ {x, y}`, with
distinct first darts and distinct last darts of one orientation, form a parallel digon. -/
private theorem hasParallelDigon_swivelMove_of_heads_eq (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {A B : List H} (hA0 : 0 < A.length) (hB0 : 0 < B.length)
    (hAB : ∀ e ∈ A, e ∉ X.bdry) (hBB : ∀ e ∈ B, e ∉ X.bdry)
    (hAc : A.IsChain (X.swivelMove d₁).StrandStep) (hBc : B.IsChain (X.swivelMove d₁).StrandStep)
    (hA0m : A[0] ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (hv : (X.swivelMove d₁).vertexOf A[0] = (X.swivelMove d₁).vertexOf B[0])
    (hhead : A[0] ≠ B[0]) (horient : X.isOut A[0] = X.isOut B[0])
    (hu : X.vertexOf (X.inv A[A.length - 1]) = X.vertexOf (X.inv B[B.length - 1]))
    (huint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv A[A.length - 1])))
    (hux : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf d₁)
    (huy : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf (X.facePerm d₁))
    (hlast : A[A.length - 1] ≠ B[B.length - 1]) : (X.swivelMove d₁).HasParallelDigon := by
  have hpre := hX.toIsPreTripleDiagram
  have hX'pre := hd.isPreTripleDiagram_swivelMove hpre
  have hnA : X.inv A[A.length - 1] ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun h =>
    (mem_union_vertexOf_iff.1 h).elim hux huy
  have hnB : X.inv B[B.length - 1] ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) := fun h =>
    (mem_union_vertexOf_iff.1 h).elim (fun h' => hux (hu.trans h')) (fun h' => huy (hu.trans h'))
  refine hasParallelDigon_of_isChain hX'pre (List.ne_nil_of_length_pos hA0)
    (List.ne_nil_of_length_pos hB0) hAB hBB hAc hBc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [List.head_eq_getElem, List.getLast_eq_getElem, swivelMove_inv, swivelMove_isOut]
  · exact horient
  · exact hv
  · rw [vertexOf_swivelMove_of_notMem hnA, vertexOf_swivelMove_of_notMem hnB, hu]
  · exact (hd.vertexOf_swivelMove_of_mem hpre hA0m).2.1
  · rw [hd.isBoundaryVertex_swivelMove_iff hpre]
    exact huint
  · intro h
    apply hnA
    have : X.inv A[A.length - 1] ∈ (X.swivelMove d₁).vertexOf A[0] := by
      rw [h]
      exact (X.swivelMove d₁).self_mem_vertexOf _
    exact (hd.vertexOf_swivelMove_of_mem hpre hA0m).1 this
  · exact hhead
  · exact hlast

/-- **Parallel digons from a corner, in the swivel move.** Two walks of the swivel move from
`x ∪ y` to a common vertex `u ∉ {x, y}`, leaving along distinct darts outside `L*` of one
orientation and arriving along distinct darts, give a parallel digon of the swivel move, unless
their first darts are `{a₂, b₂}` or `{a₃, b₃}`. -/
private theorem hasParallelDigon_swivelMove_of_heads (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {A B : List H} (hA0 : 0 < A.length) (hB0 : 0 < B.length)
    (hAB : ∀ e ∈ A, e ∉ X.bdry) (hBB : ∀ e ∈ B, e ∉ X.bdry)
    (hAc : A.IsChain (X.swivelMove d₁).StrandStep) (hBc : B.IsChain (X.swivelMove d₁).StrandStep)
    (hA0m : A[0] ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (hB0m : B[0] ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))
    (hA0L : A[0] ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H))
    (hB0L : B[0] ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H))
    (hhead : A[0] ≠ B[0]) (horient : X.isOut A[0] = X.isOut B[0])
    (hu : X.vertexOf (X.inv A[A.length - 1]) = X.vertexOf (X.inv B[B.length - 1]))
    (huint : ¬X.IsBoundaryVertex (X.vertexOf (X.inv A[A.length - 1])))
    (hux : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf d₁)
    (huy : X.vertexOf (X.inv A[A.length - 1]) ≠ X.vertexOf (X.facePerm d₁))
    (hlast : A[A.length - 1] ≠ B[B.length - 1])
    (hab : ¬((A[0] = (X.rot ^ 2) d₁ ∧ B[0] = (X.rot ^ 2) (X.facePerm d₁)) ∨
      (A[0] = (X.rot ^ 2) (X.facePerm d₁) ∧ B[0] = (X.rot ^ 2) d₁) ∨
      (A[0] = (X.rot ^ 3) d₁ ∧ B[0] = (X.rot ^ 3) (X.facePerm d₁)) ∨
      (A[0] = (X.rot ^ 3) (X.facePerm d₁) ∧ B[0] = (X.rot ^ 3) d₁))) :
    (X.swivelMove d₁).HasParallelDigon := by
  have hpre := hX.toIsPreTripleDiagram
  have hxy' := fun z (hz : z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) =>
    vertexOf_swivelMove_eq_or hpre hd hz
  have two : ∀ z₁ z₂ z₃, z₁ ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) →
      z₂ ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) →
      z₃ ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) →
      (X.swivelMove d₁).vertexOf z₁ ≠ (X.swivelMove d₁).vertexOf z₂ →
      (X.swivelMove d₁).vertexOf z₃ ≠ (X.swivelMove d₁).vertexOf z₂ →
      (X.swivelMove d₁).vertexOf z₁ = (X.swivelMove d₁).vertexOf z₃ := by
    intro z₁ z₂ z₃ h₁ h₂ h₃ h12 h32
    rcases hxy' z₁ h₁ with e1 | e1 <;> rcases hxy' z₂ h₂ with e2 | e2 <;>
      rcases hxy' z₃ h₃ with e3 | e3 <;>
      first
        | exact e1.trans e3.symm
        | exact absurd (e1.trans e2.symm) h12
        | exact absurd (e3.trans e2.symm) h32
  have hlastc : ∀ (ℓ : H) (K : List H) (hK : 0 < K.length),
      (ℓ :: K)[(ℓ :: K).length - 1]'(by simp) = K[K.length - 1] := by
    intro ℓ K hK
    rcases K with _ | ⟨k, K⟩
    · simp at hK
    · simp
  have hchain : ∀ (ℓ : H) (K : List H) (hK : 0 < K.length),
      K.IsChain (X.swivelMove d₁).StrandStep → (X.swivelMove d₁).StrandStep ℓ K[0] →
      (ℓ :: K).IsChain (X.swivelMove d₁).StrandStep := by
    intro ℓ K hK hc hs
    refine hc.cons fun y hy => ?_
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hK, Option.mem_some_iff] at hy
    rw [← hy]
    exact hs
  by_cases hv : (X.swivelMove d₁).vertexOf A[0] = (X.swivelMove d₁).vertexOf B[0]
  · exact hasParallelDigon_swivelMove_of_heads_eq hX hd hA0 hB0 hAB hBB hAc hBc hA0m hv hhead
      horient hu huint hux huy hlast
  by_cases hγA : ((X.swivelMove d₁).rot ^ 3) A[0] ∈
      ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)
  · obtain ⟨hℓL, hstep, hvℓ, hoℓ⟩ := exists_prepend_swivelMove hX hd hA0m hγA
    obtain ⟨-, hℓB, hℓv, -⟩ := mem_ls_facts hpre hd hℓL
    have hℓm := mem_union_vertexOf_iff.2 hℓv
    refine hasParallelDigon_swivelMove_of_heads_eq hX hd (A := _ :: A) (by simp) hB0
      (fun e he => (List.mem_cons.1 he).elim (fun h => h ▸ hℓB) (hAB e)) hBB
      (hchain _ A hA0 hAc hstep) hBc hℓm (two _ _ _ hℓm hA0m hB0m hvℓ (fun h => hv h.symm))
      (fun h => hB0L (h ▸ hℓL)) (hoℓ.trans horient) ?_ ?_ ?_ ?_ ?_ <;>
      simp only [hlastc _ A hA0]
    · exact hu
    · exact huint
    · exact hux
    · exact huy
    · exact hlast
  by_cases hγB : ((X.swivelMove d₁).rot ^ 3) B[0] ∈
      ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)
  · obtain ⟨hℓL, hstep, hvℓ, hoℓ⟩ := exists_prepend_swivelMove hX hd hB0m hγB
    obtain ⟨-, hℓB, hℓv, -⟩ := mem_ls_facts hpre hd hℓL
    have hℓm := mem_union_vertexOf_iff.2 hℓv
    refine hasParallelDigon_swivelMove_of_heads_eq hX hd (B := _ :: B) hA0 (by simp) hAB
      (fun e he => (List.mem_cons.1 he).elim (fun h => h ▸ hℓB) (hBB e)) hAc
      (hchain _ B hB0 hBc hstep) hA0m (two _ _ _ hA0m hB0m hℓm hv hvℓ)
      (fun h => hA0L (h ▸ hℓL)) (horient.trans hoℓ.symm) ?_ huint hux huy ?_ <;>
      simp only [hlastc _ B hB0]
    · exact hu
    · exact hlast
  -- both first darts are among `a₂, a₃, b₂, b₃`
  have cA := eq_of_rot_pow_three_swivelMove_notMem hpre hd hA0m hA0L hγA
  have cB := eq_of_rot_pow_three_swivelMove_notMem hpre hd hB0m hB0L hγB
  exfalso
  rcases cA with ⟨ea, va, oa⟩ | ⟨ea, va, oa⟩ | ⟨ea, va, oa⟩ | ⟨ea, va, oa⟩ <;>
    rcases cB with ⟨eb, vb, ob⟩ | ⟨eb, vb, ob⟩ | ⟨eb, vb, ob⟩ | ⟨eb, vb, ob⟩ <;>
    first
      | exact hhead (ea.trans eb.symm)
      | exact hv (va.trans vb.symm)
      | exact hab (Or.inl ⟨ea, eb⟩)
      | exact hab (Or.inr (Or.inl ⟨ea, eb⟩))
      | exact hab (Or.inr (Or.inr (Or.inl ⟨ea, eb⟩)))
      | exact hab (Or.inr (Or.inr (Or.inr ⟨ea, eb⟩)))
      | (rw [oa, ob] at horient; revert horient; cases X.isOut d₁ <;> simp)

/-- The two strand paths of a parallel digon, in the other order. -/
private theorem isParallelDigon_comm {P Q : List H} {u w : Finset H}
    (h : X.IsParallelDigon P Q u w) : X.IsParallelDigon Q P u w :=
  ⟨h.ne, h.mem_left, h.mem_right, h.isStrandPath_snd, h.isStrandPath_fst, h.pathStart_snd,
    h.pathEnd_snd, h.pathStart_fst, h.pathEnd_fst, h.head?_ne.symm, h.getLast?_ne.symm⟩

/-- A parallel digon `(P, Q)` with corners `x` and `w ≠ y` gives a badgon of the swivel move when
the darts of `P` and `Q` at `x`, read off as the first darts of nonempty lists `P₀, Q₀`, are
`d₁` or `a₃` and `a₂` or `d̄₂` respectively. -/
private theorem hasBadgon_swivelMove_of_ab (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) (hmono : ¬X.HasMonogon) {P Q P₀ Q₀ : List H} {w : Finset H}
    (hwy : w ≠ X.vertexOf (X.facePerm d₁)) (hP0 : 0 < P₀.length) (hQ0 : 0 < Q₀.length)
    (hcase : (X.IsParallelDigon P Q (X.vertexOf d₁) w ∧ P₀.head? = P.head? ∧
        Q₀.head? = Q.head?) ∨
      (X.IsParallelDigon P Q w (X.vertexOf d₁) ∧ P₀.head? = P.getLast?.map X.inv ∧
        Q₀.head? = Q.getLast?.map X.inv))
    (hp : P₀[0] = d₁ ∨ P₀[0] = (X.rot ^ 3) d₁)
    (hq : Q₀[0] = (X.rot ^ 2) d₁ ∨ Q₀[0] = X.inv (X.facePerm d₁)) :
    (X.swivelMove d₁).HasBadgon := by
  have hP0h := head?_eq_some_getElem hP0
  have hQ0h := head?_eq_some_getElem hQ0
  refine hasBadgon_swivelMove_of_isParallelDigon hX hd hmono (P := P) (Q := Q) hwy ?_
  rcases hcase with ⟨h, hph, hqh⟩ | ⟨h, hph, hqh⟩
  · refine Or.inl ⟨h, ?_, ?_⟩
    · rw [← hph, hP0h]
      exact hp.imp (congrArg some) (congrArg some)
    · rw [← hqh, hQ0h]
      exact hq.imp (congrArg some) (congrArg some)
  · refine Or.inr ⟨h, ?_, ?_⟩
    · rw [← hph, hP0h]
      exact hp.imp (congrArg some) (congrArg some)
    · rw [← hqh, hQ0h]
      exact hq.imp (congrArg some) (congrArg some)

/-- The first dart at `x` of a walk, trimmed of a dart of `L*`: the dart itself if it is not in
`L*`, `b₂` after `d₁` and `b₃` after `d̄₂`. -/
private theorem trim_head_cases (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {p p₁ : H} (hp : X.vertexOf p = X.vertexOf d₁)
    (h1 : p ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) → p₁ = p)
    (h2 : p ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) →
      p₁ = (X.rot ^ 3) (X.inv p)) :
    (p ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) ∧ p₁ = p) ∨
      (p = d₁ ∧ p₁ = (X.rot ^ 2) (X.facePerm d₁) ∧ X.isOut p₁ = X.isOut p) ∨
      (p = X.inv (X.facePerm d₁) ∧ p₁ = (X.rot ^ 3) (X.facePerm d₁) ∧ X.isOut p₁ = X.isOut p) := by
  by_cases hL : p ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)
  · have hp₁ := h2 hL
    obtain ⟨-, hB, -, -, hr, -, -⟩ := mem_ls_facts hX hd hL
    have ho : X.isOut p₁ = X.isOut p := by
      rw [hp₁, hX.isOut_rot_pow_three_apply hr, hX.isOut_inv_apply hB, Bool.not_not]
    obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, -, -, -, hV₂, -, -⟩ :=
      hd.exists_darts hX
    have hxy := hd.vertexOf_ne
    simp only [mem_insert, mem_singleton] at hL
    rcases hL with e | e | e | e
    · refine Or.inr (Or.inl ⟨e, ?_, ho⟩)
      rw [hp₁, e]
      rfl
    · exfalso
      rw [e, X.vertexOf_eq_of_mem (show X.inv d₁ ∈ X.vertexOf (X.facePerm d₁) by rw [hV₂]; simp)]
        at hp
      exact hxy hp.symm
    · exact absurd (e ▸ hp).symm hxy
    · refine Or.inr (Or.inr ⟨e, ?_, ho⟩)
      rw [hp₁, e, hX.inv_inv_apply]
  · exact Or.inl ⟨hL, h1 hL⟩

/-- **Parallel digons with one corner at the digon**: if `X` has no monogon and a parallel digon
with corners `x` and `w ∉ {x, y}`, then the swivel move has a badgon. -/
private theorem hasBadgon_swivelMove_of_corner (hX : X.IsTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) (hmono : ¬X.HasMonogon) {P Q : List H} {w : Finset H}
    (hwx : w ≠ X.vertexOf d₁) (hwy : w ≠ X.vertexOf (X.facePerm d₁))
    (h : X.IsParallelDigon P Q (X.vertexOf d₁) w ∨ X.IsParallelDigon P Q w (X.vertexOf d₁)) :
    (X.swivelMove d₁).HasBadgon := by
  have hpre := hX.toIsPreTripleDiagram
  obtain ⟨P₀, Q₀, hP0, hQ0, hPB, hQB, hPc, hQc, hPx, hQx, hPw, hQw, hlast, hhead, horient, -,
    hwint, -, hcase⟩ := exists_walks_of_isParallelDigon hpre h
  have hcase' : (X.IsParallelDigon Q P (X.vertexOf d₁) w ∧ Q₀.head? = Q.head? ∧
        P₀.head? = P.head?) ∨
      (X.IsParallelDigon Q P w (X.vertexOf d₁) ∧ Q₀.head? = Q.getLast?.map X.inv ∧
        P₀.head? = P.getLast?.map X.inv) :=
    hcase.imp (fun ⟨h1, h2, h3⟩ => ⟨isParallelDigon_comm h1, h3, h2⟩)
      (fun ⟨h1, h2, h3⟩ => ⟨isParallelDigon_comm h1, h3, h2⟩)
  have hnw : ∀ e, X.vertexOf e = w → e ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) :=
    fun e he h' => (mem_union_vertexOf_iff.1 h').elim (fun h'' => hwx (he.symm.trans h''))
      (fun h'' => hwy (he.symm.trans h''))
  have hPlL : P₀[P₀.length - 1] ∉
      ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) := fun hL =>
    hnw _ hPw (mem_union_vertexOf_iff.2 (mem_ls_facts hpre hd (mem_ls_facts hpre hd hL).1).2.2.1)
  have hQlL : Q₀[Q₀.length - 1] ∉
      ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H) := fun hL =>
    hnw _ hQw (mem_union_vertexOf_iff.2 (mem_ls_facts hpre hd (mem_ls_facts hpre hd hL).1).2.2.1)
  obtain ⟨P₁, hP₁0, hP₁B, hP₁c, hP₁L, hP₁m, hP₁l, hP₁n, hP₁t⟩ := exists_trim_head hpre hd hP0 hPB
    hPc (mem_union_vertexOf_iff.2 (Or.inl hPx)) ⟨_, List.getElem_mem _, hPlL⟩
  obtain ⟨Q₁, hQ₁0, hQ₁B, hQ₁c, hQ₁L, hQ₁m, hQ₁l, hQ₁n, hQ₁t⟩ := exists_trim_head hpre hd hQ0 hQB
    hQc (mem_union_vertexOf_iff.2 (Or.inl hQx)) ⟨_, List.getElem_mem _, hQlL⟩
  obtain ⟨P', hP'0, hP'B, hP'c, hP'0d, hP'l⟩ := exists_walk_swivelMove hpre hd _ P₁ hP₁0 rfl hP₁B
    hP₁c hP₁L (by rw [hP₁l]; exact hPlL)
  obtain ⟨Q', hQ'0, hQ'B, hQ'c, hQ'0d, hQ'l⟩ := exists_walk_swivelMove hpre hd _ Q₁ hQ₁0 rfl hQ₁B
    hQ₁c hQ₁L (by rw [hQ₁l]; exact hQlL)
  -- the darts at `x` and `y`
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, hV₁, hV₂,
    hi₁, hi₂⟩ := hd.exists_darts hpre
  have hne : ∀ i j (hi : i < 12) (hj : j < 12), i ≠ j →
      [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][i] ≠
        [d₁, a₁, a₂, a₃, a₄, X.inv (X.facePerm d₁), X.facePerm d₁, b₁, b₂, b₃, b₄, X.inv d₁][j] :=
    fun i j hi hj hij h => hij ((hnd.getElem_inj_iff (hi := by simpa using hi)
      (hj := by simpa using hj)).1 h)
  have hxy := hd.vertexOf_ne
  have p2 : (X.rot ^ 2) d₁ = a₂ := by rw [pow_two, Equiv.Perm.mul_apply, h1, h2]
  have p3 : (X.rot ^ 3) d₁ = a₃ := by rw [X.rot_pow_three_apply, h1, h2, h3]
  have q2 : (X.rot ^ 2) (X.facePerm d₁) = b₂ := by rw [pow_two, Equiv.Perm.mul_apply, g1, g2]
  have q3 : (X.rot ^ 3) (X.facePerm d₁) = b₃ := by rw [X.rot_pow_three_apply, g1, g2, g3]
  have vq : ∀ k, X.vertexOf ((X.rot ^ k) (X.facePerm d₁)) ≠ X.vertexOf d₁ := fun k h' =>
    hxy (by rw [← h', X.vertexOf_rot_pow_apply])
  have hy : ¬X.IsBoundaryVertex (X.vertexOf (X.inv d₁)) := by
    rw [X.vertexOf_eq_of_mem (show X.inv d₁ ∈ X.vertexOf (X.facePerm d₁) by rw [hV₂]; simp)]
    exact hi₂
  have od₂ : X.isOut (X.inv (X.facePerm d₁)) = !X.isOut d₁ := by
    rw [hpre.isOut_inv_apply hd.notMem_bdry.2, show X.facePerm d₁ = X.rot (X.inv d₁) from rfl,
      hpre.isOut_rot_apply hy, hpre.isOut_inv_apply hd.notMem_bdry.1]
    simp
  -- the common data for the parallel digon of the swivel move
  have G := fun (hh : P₁[0] ≠ Q₁[0]) (ho : X.isOut P₁[0] = X.isOut Q₁[0])
      (hab : ¬((P₁[0] = (X.rot ^ 2) d₁ ∧ Q₁[0] = (X.rot ^ 2) (X.facePerm d₁)) ∨
        (P₁[0] = (X.rot ^ 2) (X.facePerm d₁) ∧ Q₁[0] = (X.rot ^ 2) d₁) ∨
        (P₁[0] = (X.rot ^ 3) d₁ ∧ Q₁[0] = (X.rot ^ 3) (X.facePerm d₁)) ∨
        (P₁[0] = (X.rot ^ 3) (X.facePerm d₁) ∧ Q₁[0] = (X.rot ^ 3) d₁))) =>
    (Or.inr (hasParallelDigon_swivelMove_of_heads hX hd hP'0 hQ'0 hP'B hQ'B hP'c hQ'c
      (by rw [hP'0d]; exact hP₁m) (by rw [hQ'0d]; exact hQ₁m) (by rw [hP'0d]; exact hP₁L)
      (by rw [hQ'0d]; exact hQ₁L) (by rw [hP'0d, hQ'0d]; exact hh)
      (by rw [hP'0d, hQ'0d]; exact ho) (by rw [hP'l, hQ'l, hP₁l, hQ₁l, hPw, hQw])
      (by rw [hP'l, hP₁l, hPw]; exact (X.mem_internalVertices.1 hwint).2)
      (by rw [hP'l, hP₁l, hPw]; exact hwx) (by rw [hP'l, hP₁l, hPw]; exact hwy)
      (by rw [hP'l, hQ'l, hP₁l, hQ₁l]; exact hlast)
      (by rw [hP'0d, hQ'0d]; exact hab)) : (X.swivelMove d₁).HasBadgon)
  rcases trim_head_cases hpre hd hPx hP₁n hP₁t with ⟨hpL, ep⟩ | ⟨ep, ep₁, op⟩ | ⟨ep, ep₁, op⟩ <;>
    rcases trim_head_cases hpre hd hQx hQ₁n hQ₁t with ⟨hqL, eq⟩ | ⟨eq, eq₁, oq⟩ | ⟨eq, eq₁, oq⟩
  · -- neither is trimmed: both first darts at `x`
    refine G (by rw [ep, eq]; exact hhead) (by rw [ep, eq]; exact horient) ?_
    rintro (⟨-, h'⟩ | ⟨h', -⟩ | ⟨-, h'⟩ | ⟨h', -⟩)
    · exact vq 2 (by rw [← h', eq]; exact hQx)
    · exact vq 2 (by rw [← h', ep]; exact hPx)
    · exact vq 3 (by rw [← h', eq]; exact hQx)
    · exact vq 3 (by rw [← h', ep]; exact hPx)
  · -- `Q₀` leaves along `d₁`
    by_cases hab : P₀[0] = (X.rot ^ 2) d₁
    · exact hasBadgon_swivelMove_of_ab hX hd hmono hwy hQ0 hP0 hcase' (Or.inl eq) (Or.inl hab)
    refine G (fun h' => vq 2 (by rw [← eq₁, ← h', ep]; exact hPx))
      (by rw [ep, oq]; exact horient) ?_
    rintro (⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h'⟩ | ⟨h', -⟩)
    · exact hab (ep ▸ h')
    · exact vq 2 (by rw [← h', ep]; exact hPx)
    · rw [eq₁, q2, q3] at h'
      exact hne 8 9 (by norm_num) (by norm_num) (by norm_num) h'
    · exact vq 3 (by rw [← h', ep]; exact hPx)
  · -- `Q₀` leaves along `d̄₂`
    by_cases hab : P₀[0] = (X.rot ^ 3) d₁
    · exact hasBadgon_swivelMove_of_ab hX hd hmono hwy hP0 hQ0 hcase (Or.inr hab) (Or.inr eq)
    refine G (fun h' => vq 3 (by rw [← eq₁, ← h', ep]; exact hPx))
      (by rw [ep, oq]; exact horient) ?_
    rintro (⟨-, h'⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩)
    · rw [eq₁, q2, q3] at h'
      exact hne 9 8 (by norm_num) (by norm_num) (by norm_num) h'
    · exact vq 2 (by rw [← h', ep]; exact hPx)
    · exact hab (ep ▸ h')
    · exact vq 3 (by rw [← h', ep]; exact hPx)
  · -- `P₀` leaves along `d₁`
    by_cases hab : Q₀[0] = (X.rot ^ 2) d₁
    · exact hasBadgon_swivelMove_of_ab hX hd hmono hwy hP0 hQ0 hcase (Or.inl ep) (Or.inl hab)
    refine G (fun h' => vq 2 (by rw [← ep₁, h', eq]; exact hQx))
      (by rw [eq, op]; exact horient) ?_
    rintro (⟨h', -⟩ | ⟨-, h'⟩ | ⟨h', -⟩ | ⟨h', -⟩)
    · rw [ep₁, q2, p2] at h'
      exact hne 8 2 (by norm_num) (by norm_num) (by norm_num) h'
    · exact hab (eq ▸ h')
    · rw [ep₁, q2, p3] at h'
      exact hne 8 3 (by norm_num) (by norm_num) (by norm_num) h'
    · rw [ep₁, q2, q3] at h'
      exact hne 8 9 (by norm_num) (by norm_num) (by norm_num) h'
  · exact absurd (ep.trans eq.symm) hhead
  · exfalso
    rw [ep, eq, od₂] at horient
    revert horient
    cases X.isOut d₁ <;> simp
  · -- `P₀` leaves along `d̄₂`
    by_cases hab : Q₀[0] = (X.rot ^ 3) d₁
    · exact hasBadgon_swivelMove_of_ab hX hd hmono hwy hQ0 hP0 hcase' (Or.inr hab) (Or.inr ep)
    refine G (fun h' => vq 3 (by rw [← ep₁, h', eq]; exact hQx))
      (by rw [eq, op]; exact horient) ?_
    rintro (⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h'⟩)
    · rw [ep₁, q3, p2] at h'
      exact hne 9 2 (by norm_num) (by norm_num) (by norm_num) h'
    · rw [ep₁, q3, q2] at h'
      exact hne 9 8 (by norm_num) (by norm_num) (by norm_num) h'
    · rw [ep₁, q3, p3] at h'
      exact hne 9 3 (by norm_num) (by norm_num) (by norm_num) h'
    · exact hab (eq ▸ h')
  · exfalso
    rw [ep, eq, od₂] at horient
    revert horient
    cases X.isOut d₁ <;> simp
  · exact absurd (ep.trans eq.symm) hhead

/-- A dart of `L*` is determined by its vertex and its orientation. -/
private theorem eq_of_mem_ls (hX : X.IsPreTripleDiagram) {d₁ : H} (hd : X.IsDigon (X.faceOf d₁))
    {e e' : H} (he : e ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H))
    (he' : e' ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H))
    (hv : X.vertexOf e = X.vertexOf e') (ho : X.isOut e = X.isOut e') : e = e' := by
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, -, -, hV₁, hV₂, -, hi₂⟩ :=
    hd.exists_darts hX
  obtain ⟨hB₁, hB₂⟩ := hd.notMem_bdry
  have hxy := hd.vertexOf_ne
  have vid₁ : X.vertexOf (X.inv d₁) = X.vertexOf (X.facePerm d₁) :=
    X.vertexOf_eq_of_mem (by rw [hV₂]; simp)
  have vid₂ : X.vertexOf (X.inv (X.facePerm d₁)) = X.vertexOf d₁ :=
    X.vertexOf_eq_of_mem (by rw [hV₁]; simp)
  have hy : ¬X.IsBoundaryVertex (X.vertexOf (X.inv d₁)) := by
    rw [vid₁]
    exact hi₂
  have oid₁ : X.isOut (X.inv d₁) = !X.isOut d₁ := hX.isOut_inv_apply hB₁
  have od₂ : X.isOut (X.facePerm d₁) = X.isOut d₁ := by
    rw [show X.facePerm d₁ = X.rot (X.inv d₁) from rfl, hX.isOut_rot_apply hy, oid₁]
    simp
  have oid₂ : X.isOut (X.inv (X.facePerm d₁)) = !X.isOut d₁ := by
    rw [hX.isOut_inv_apply hB₂, od₂]
  have hc : ∀ ℓ ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H),
      (X.vertexOf ℓ = X.vertexOf d₁ ∧ X.isOut ℓ = X.isOut d₁ ∧ ℓ = d₁) ∨
      (X.vertexOf ℓ = X.vertexOf d₁ ∧ X.isOut ℓ = !X.isOut d₁ ∧ ℓ = X.inv (X.facePerm d₁)) ∨
      (X.vertexOf ℓ = X.vertexOf (X.facePerm d₁) ∧ X.isOut ℓ = X.isOut d₁ ∧
        ℓ = X.facePerm d₁) ∨
      (X.vertexOf ℓ = X.vertexOf (X.facePerm d₁) ∧ X.isOut ℓ = !X.isOut d₁ ∧ ℓ = X.inv d₁) := by
    intro ℓ hℓ
    simp only [mem_insert, mem_singleton] at hℓ
    rcases hℓ with h | h | h | h <;> rw [h]
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inr ⟨vid₁, oid₁, rfl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, od₂, rfl⟩))
    · exact Or.inr (Or.inl ⟨vid₂, oid₂, rfl⟩)
  rcases hc e he with ⟨v1, o1, e1⟩ | ⟨v1, o1, e1⟩ | ⟨v1, o1, e1⟩ | ⟨v1, o1, e1⟩ <;>
    rcases hc e' he' with ⟨v2, o2, e2⟩ | ⟨v2, o2, e2⟩ | ⟨v2, o2, e2⟩ | ⟨v2, o2, e2⟩ <;>
    first
      | exact e1.trans e2.symm
      | exact absurd (v1.symm.trans (hv.trans v2)) hxy
      | exact absurd (v1.symm.trans (hv.trans v2)) hxy.symm
      | (rw [o1, o2] at ho; revert ho; cases X.isOut d₁ <;> simp)

/-- **Badgons propagate**. Let `X` be a triple diagram and `X'` its swivel move at a digon
`f(d₁)`. If `X` has a badgon, then so does `X'`. -/
@[cluster_algebras "lem_badgon_propagates"]
theorem hasBadgon_swivelMove (hX : X.IsTripleDiagram) {d₁ : H} (hd : X.IsDigon (X.faceOf d₁))
    (h : X.HasBadgon) : (X.swivelMove d₁).HasBadgon := by
  have hpre := hX.toIsPreTripleDiagram
  by_cases hmono : X.HasMonogon
  · obtain ⟨P, hP⟩ := hmono
    have hS := hP.isStrandPath
    have hP0 : 0 < P.length := List.length_pos_iff.2 hS.ne_nil
    have hPh := head?_eq_some_getElem hP0
    have hPl := getLast?_eq_some_getElem hP0
    have hv0 : X.vertexOf P[0] = X.pathStart P := (X.pathStart_of_head? hPh).symm
    have hvl : X.vertexOf (X.inv P[P.length - 1]) = X.pathStart P := by
      rw [← X.pathEnd_of_getLast? hPl]
      exact hP.pathEnd_eq
    by_cases hv : X.pathStart P = X.vertexOf d₁ ∨ X.pathStart P = X.vertexOf (X.facePerm d₁)
    · -- a monogon at `x` or `y`
      refine hasBadgon_swivelMove_of_walk hX hd hP0 hS.notMem_bdry hS.isChain
        (mem_union_vertexOf_iff.2 (by rw [hv0]; exact hv))
        (mem_union_vertexOf_iff.2 (by rw [hvl]; exact hv)) ?_
      by_cases h0 : P[0] ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)
      · have h2 : 1 < P.length := by
          by_contra h2
          have e : P[P.length - 1] = P[0] := by congr 1; omega
          apply (mem_ls_facts hpre hd h0).2.2.2.1
          have := hvl
          rw [e] at this
          rw [this, hv0]
        have hs := (List.isChain_iff_getElem.1 hS.isChain) 0 h2
        simp only [Nat.zero_add] at hs
        exact ⟨P[1], List.getElem_mem _, by rw [hs.2]; exact (mem_ls_facts hpre hd h0).2.2.2.2.2.1⟩
      · exact ⟨P[0], List.getElem_mem _, h0⟩
    · -- a monogon away from `x` and `y`
      push Not at hv
      exact Or.inl (hasMonogon_swivelMove_of_isMonogon hpre hd hP hv.1 hv.2)
  · rcases h with h | ⟨P, Q, u, w, hPQ⟩
    · exact absurd h hmono
    have hφφ := hd.facePerm_facePerm
    have hd₂ : X.IsDigon (X.faceOf (X.facePerm d₁)) := by
      rw [X.faceOf_facePerm]
      exact hd
    have hsw := swivelMove_facePerm hpre hd
    by_cases hu : u = X.vertexOf d₁ ∨ u = X.vertexOf (X.facePerm d₁) <;>
      by_cases hw : w = X.vertexOf d₁ ∨ w = X.vertexOf (X.facePerm d₁)
    · -- a parallel digon with corners `x` and `y`
      have key : ∀ R : List H, X.IsStrandPath R → X.pathStart R = u → X.pathEnd R = w →
          (∃ e ∈ R, e ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) →
          (X.swivelMove d₁).HasBadgon := by
        intro R hR hs he hex
        have hR0 : 0 < R.length := List.length_pos_iff.2 hR.ne_nil
        refine hasBadgon_swivelMove_of_walk hX hd hR0 hR.notMem_bdry hR.isChain ?_ ?_ hex
        · exact mem_union_vertexOf_iff.2
            (by rw [← X.pathStart_of_head? (head?_eq_some_getElem hR0), hs]; exact hu)
        · exact mem_union_vertexOf_iff.2
            (by rw [← X.pathEnd_of_getLast? (getLast?_eq_some_getElem hR0), he]; exact hw)
      by_cases hPex : ∃ e ∈ P,
          e ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)
      · exact key P hPQ.isStrandPath_fst hPQ.pathStart_fst hPQ.pathEnd_fst hPex
      by_cases hQex : ∃ e ∈ Q,
          e ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)
      · exact key Q hPQ.isStrandPath_snd hPQ.pathStart_snd hPQ.pathEnd_snd hQex
      exfalso
      push Not at hPex hQex
      have hP0 : 0 < P.length := List.length_pos_iff.2 hPQ.isStrandPath_fst.ne_nil
      have hQ0 : 0 < Q.length := List.length_pos_iff.2 hPQ.isStrandPath_snd.ne_nil
      have hPh := head?_eq_some_getElem hP0
      have hQh := head?_eq_some_getElem hQ0
      apply hPQ.head?_ne
      rw [hPh, hQh, eq_of_mem_ls hpre hd (hPex _ (List.getElem_mem _))
        (hQex _ (List.getElem_mem _))
        (by rw [← X.pathStart_of_head? hPh, ← X.pathStart_of_head? hQh, hPQ.pathStart_fst,
          hPQ.pathStart_snd])
        (by rw [hPQ.isStrandPath_fst.isOut_eq_true _ (List.getElem_mem _),
          hPQ.isStrandPath_snd.isOut_eq_true _ (List.getElem_mem _)])]
    · -- a parallel digon from a corner `x` or `y`
      push Not at hw
      rcases hu with rfl | rfl
      · exact hasBadgon_swivelMove_of_corner hX hd hmono hw.1 hw.2 (Or.inl hPQ)
      · rw [← hsw]
        exact hasBadgon_swivelMove_of_corner hX hd₂ hmono hw.2 (by rw [hφφ]; exact hw.1)
          (Or.inl hPQ)
    · -- a parallel digon to a corner `x` or `y`
      push Not at hu
      rcases hw with rfl | rfl
      · exact hasBadgon_swivelMove_of_corner hX hd hmono hu.1 hu.2 (Or.inr hPQ)
      · rw [← hsw]
        exact hasBadgon_swivelMove_of_corner hX hd₂ hmono hu.2 (by rw [hφφ]; exact hu.1)
          (Or.inr hPQ)
    · -- a parallel digon away from `x` and `y`
      push Not at hu hw
      exact Or.inr (hasParallelDigon_swivelMove_of_away hpre hd hPQ hu.1 hu.2 hw.1 hw.2)

end Walks

end TripleData

end ClusterAlgebras

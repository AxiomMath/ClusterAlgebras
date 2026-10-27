/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.CyclePlusVertex

/-!
# A diagram of type `E` with one more vertex

We show that a `2`-finite connected matrix obtained by adding one vertex to a diagram mutation
equivalent to one of Dynkin shape `E_n`, `n ∈ {6, 7, 8}`, is of Dynkin class `X` for a Dynkin
symbol `X` of rank `n + 1`. The mutation class of `E_n` is represented by the crown
`S^{n-4}_{1,2,1}`: an oriented unit `(n - 1)`-cycle with one pendant vertex.

## Main results

* `ClusterAlgebras.IsOrientedUnitCycle.exists_isOfDynkinClass_of_pendant`: a `2`-finite
  connected matrix consisting of an oriented unit `L`-cycle, `L ∈ {5, 6, 7}`, a pendant vertex
  attached to one cycle vertex by an edge of weight `1`, and one more vertex is of Dynkin class
  `X` for a Dynkin symbol `X` of rank `L + 2`.
* `ClusterAlgebras.exists_isOfDynkinClass_of_diagramEquiv_hasDynkinShape_E`: a `2`-finite
  connected matrix whose restriction away from one vertex is mutation equivalent to a matrix of
  Dynkin shape `E_n` is of Dynkin class `X` for a Dynkin symbol `X` of rank `n + 1`.

## Implementation notes

The indices of the configuration of
`ClusterAlgebras.IsOrientedUnitCycle.exists_isOfDynkinClass_of_pendant` are labelled
`0, …, L + 1`, the cycle vertex `cᵢ` at `i`, `v₁` at `L` and `u` at `L + 1`. Once `u` is
adjacent to at most one `c_j`, the weights of `B` in these positions are a function of `L`, `j`,
`α = w(u, c_j)` and `β = w(u, v₁)` only. Every subdiagram of extended Dynkin shape, crown,
chordless cycle and path of the case analysis is then given by a list of positions, and the
identity of its weights with the model is a finite computation, done by `decide` for each of the
three values of `L`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.10.
* [FZ] S. Fomin, A. Zelevinsky, *Cluster algebras II: Finite type classification*.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n N : ℕ}

/-! ### Auxiliary facts -/

section Aux

private theorem isOfDynkinClass_of_mutationEquiv' {B B' : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B') (h : MutationEquiv B B')
    {Xs : List DynkinSymbol} (h' : IsOfDynkinClass B' Xs) : IsOfDynkinClass B Xs :=
  h'.of_diagramEquiv hB hB' h.diagramEquiv

/-- An embedding of `[0, M)` into `[0, M]` missing `x` has image the complement of `x`. -/
private theorem range_eq_compl_singleton' {M : ℕ} (r : Fin M ↪ Fin (M + 1)) {x : Fin (M + 1)}
    (hx : x ∉ Set.range r) : Set.range r = {x}ᶜ := by
  classical
  ext y
  simp only [Set.mem_compl_singleton_iff]
  refine ⟨fun hy h => hx (h ▸ hy), fun hyx => ?_⟩
  by_contra hy
  have hsub : Finset.univ.map r ⊆ (Finset.univ.erase x).erase y := by
    intro z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hz
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => hy ⟨a, h⟩, fun h => hx ⟨a, h⟩⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin,
    Finset.card_erase_of_mem (by simpa using hyx), Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin] at this
  omega

end Aux

/-! ### Trees of shape `T_{a,b,c}` -/

section Tree

/-- A matrix of shape `T_{a,b,c}` has a mutation of Dynkin shape. -/
private theorem exists_of_isTShape_matrixMutationList {B : Matrix (Fin N) (Fin N) ℤ}
    (hB : IsTwoFinite B) {t : List (Fin N)} {a b c : ℕ}
    (h : IsTShape (diagramWeight (matrixMutationList le_rfl B t)) a b c) :
    ∃ X : DynkinSymbol, X.rank = N ∧ IsOfDynkinClass B [X] := by
  have hBt := hB.matrixMutationList t
  obtain ⟨X, hX, -⟩ := hBt.hasDynkinShape_of_isTreeDiagram h.isTreeDiagram
  exact ⟨X, hX.rank_eq, isOfDynkinClass_of_mutationEquiv' hB.1 hBt.1
    (mutationEquiv_matrixMutationList B t) hX.isOfDynkinClass⟩

end Tree

/-! ### The labelled configuration -/

section Table

/-- The index `x` of `[0, L + 2)`, read modulo `L + 2`. -/
private def pos (L x : ℕ) : Fin (L + 2) := ⟨x % (L + 2), Nat.mod_lt _ (by omega)⟩

private theorem val_pos' {L x : ℕ} (h : x < L + 2) : (pos L x : ℕ) = x := Nat.mod_eq_of_lt h

/-- The weights of the configuration, in the positions `0, …, L - 1` of the cycle, `L` of `v₁`
and `L + 1` of `u`: the cycle `(0, …, L - 1)` with weights `1`, the pair `{v₁, c₀}` of weight `1`,
`w(u, c_j) = α` and `w(u, v₁) = β`. -/
private def eTable (L j α β i k : ℕ) : ℕ :=
  if i = k then 0
  else if i < L ∧ k < L then (if (i + 1) % L = k ∨ (k + 1) % L = i then 1 else 0)
  else if (i = L ∧ k = 0) ∨ (i = 0 ∧ k = L) then 1
  else if (i = L + 1 ∧ k = j) ∨ (i = j ∧ k = L + 1) then α
  else if (i = L ∧ k = L + 1) ∨ (i = L + 1 ∧ k = L) then β
  else 0

private theorem eTable_pos_iff {L j α β i k : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    0 < eTable L j α β i k ↔ 0 < eTable L j 1 1 i k := by
  unfold eTable
  split_ifs <;> omega

/-- The enumeration `c₀, …, c_{L-1}, v₁, u` of `[0, L + 2)`. -/
private def labelMap {L : ℕ} (c : Fin L → Fin (L + 2)) (v₁ u : Fin (L + 2)) (i : Fin (L + 2)) :
    Fin (L + 2) :=
  if h : (i : ℕ) < L then c ⟨i, h⟩ else if (i : ℕ) = L then v₁ else u

private theorem labelMap_lt {L : ℕ} (c : Fin L → Fin (L + 2)) (v₁ u : Fin (L + 2))
    {i : Fin (L + 2)} (h : (i : ℕ) < L) : labelMap c v₁ u i = c ⟨i, h⟩ :=
  dif_pos h

private theorem labelMap_eq {L : ℕ} (c : Fin L → Fin (L + 2)) (v₁ u : Fin (L + 2))
    {i : Fin (L + 2)} (h : (i : ℕ) = L) : labelMap c v₁ u i = v₁ := by
  rw [labelMap, dif_neg (by omega), if_pos h]

private theorem labelMap_last {L : ℕ} (c : Fin L → Fin (L + 2)) (v₁ u : Fin (L + 2))
    {i : Fin (L + 2)} (h : (i : ℕ) = L + 1) : labelMap c v₁ u i = u := by
  rw [labelMap, dif_neg (by omega), if_neg (by omega)]

private theorem labelMap_injective {L : ℕ} {c : Fin L → Fin (L + 2)} {v₁ u : Fin (L + 2)}
    (hc : Function.Injective c) (hv₁ : v₁ ∉ Set.range c) (hu : u ∉ Set.range c) (hv₁u : v₁ ≠ u) :
    Function.Injective (labelMap c v₁ u) := by
  intro i k h
  have hi3 : (i : ℕ) < L ∨ (i : ℕ) = L ∨ (i : ℕ) = L + 1 := by omega
  have hk3 : (k : ℕ) < L ∨ (k : ℕ) = L ∨ (k : ℕ) = L + 1 := by omega
  rcases hi3 with hi | hi | hi <;> rcases hk3 with hk | hk | hk
  · rw [labelMap_lt _ _ _ hi, labelMap_lt _ _ _ hk] at h
    exact Fin.ext (by simpa using congrArg Fin.val (hc h))
  · rw [labelMap_lt _ _ _ hi, labelMap_eq _ _ _ hk] at h
    exact absurd ⟨_, h⟩ hv₁
  · rw [labelMap_lt _ _ _ hi, labelMap_last _ _ _ hk] at h
    exact absurd ⟨_, h⟩ hu
  · rw [labelMap_eq _ _ _ hi, labelMap_lt _ _ _ hk] at h
    exact absurd ⟨_, h.symm⟩ hv₁
  · rw [labelMap_eq _ _ _ hi, labelMap_eq _ _ _ hk] at h
    exact Fin.ext (by omega)
  · rw [labelMap_eq _ _ _ hi, labelMap_last _ _ _ hk] at h
    exact absurd h hv₁u
  · rw [labelMap_last _ _ _ hi, labelMap_lt _ _ _ hk] at h
    exact absurd ⟨_, h.symm⟩ hu
  · rw [labelMap_last _ _ _ hi, labelMap_eq _ _ _ hk] at h
    exact absurd h.symm hv₁u
  · rw [labelMap_last _ _ _ hi, labelMap_last _ _ _ hk] at h
    exact Fin.ext (by omega)

/-- The weights of an oriented unit cycle, in terms of positions. -/
private theorem IsOrientedUnitCycle.diagramWeight_eq_ite {L : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {c : Fin L → Fin n} (hc : IsOrientedUnitCycle B c) (a b : Fin L) :
    diagramWeight B (c a) (c b) =
      if (a : ℕ) ≠ b ∧ (((a : ℕ) + 1) % L = b ∨ ((b : ℕ) + 1) % L = a) then 1 else 0 := by
  by_cases hab : a = b
  · subst hab
    simp [hB.diagramWeight_self]
  have hadj := hc.1.2.2 a b hab
  rw [diagramGraph_adj] at hadj
  have hrot : (b = finRotate L a ∨ a = finRotate L b) ↔
      (((a : ℕ) + 1) % L = b ∨ ((b : ℕ) + 1) % L = a) := by
    rw [Fin.ext_iff, Fin.ext_iff, val_finRotate_eq_mod, val_finRotate_eq_mod]
    constructor <;> rintro (h | h) <;> omega
  split_ifs with h
  · rcases hrot.2 h.2 with h' | h'
    · rw [h']
      exact (hc.2 a).2
    · rw [h', diagramWeight_comm]
      exact (hc.2 b).2
  · by_contra h'
    exact h ⟨fun h => hab (Fin.ext h), hrot.1 (hadj.1 ⟨hc.1.2.1.ne hab, Nat.pos_of_ne_zero h'⟩)⟩

/-- The weights of the labelled configuration are those of `eTable`. -/
private theorem labelMap_weight {L : ℕ} {B : Matrix (Fin (L + 2)) (Fin (L + 2)) ℤ}
    (hBs : SkewSymmetrizable B) {c : Fin L → Fin (L + 2)} {v₁ u : Fin (L + 2)}
    (hv₁ : v₁ ∉ Set.range c) (hcyc : IsOrientedUnitCycle B c) (h0 : 0 < L)
    (hw : diagramWeight B v₁ (c ⟨0, h0⟩) = 1)
    (hadj : ∀ i : Fin L, (i : ℕ) ≠ 0 → ¬(diagramGraph B).Adj v₁ (c i)) {j α β : ℕ}
    (huc : ∀ a : Fin L, diagramWeight B u (c a) = if (a : ℕ) = j then α else 0)
    (huv : diagramWeight B u v₁ = β) (hj : j < L) (i k : Fin (L + 2)) :
    diagramWeight B (labelMap c v₁ u i) (labelMap c v₁ u k) = eTable L j α β i k := by
  have hcc := hcyc.diagramWeight_eq_ite hBs
  have hvc : ∀ a : Fin L, diagramWeight B v₁ (c a) = if (a : ℕ) = 0 then 1 else 0 := by
    intro a
    split_ifs with ha
    · rw [show a = ⟨0, h0⟩ from Fin.ext ha, hw]
    · by_contra h'
      exact hadj a ha ⟨fun h => hv₁ ⟨a, h.symm⟩, Nat.pos_of_ne_zero h'⟩
  have hvv := hBs.diagramWeight_self v₁
  have huu := hBs.diagramWeight_self u
  have hi3 : (i : ℕ) < L ∨ (i : ℕ) = L ∨ (i : ℕ) = L + 1 := by omega
  have hk3 : (k : ℕ) < L ∨ (k : ℕ) = L ∨ (k : ℕ) = L + 1 := by omega
  rcases hi3 with hi | hi | hi <;> rcases hk3 with hk | hk | hk <;>
    first
    | rw [labelMap_lt _ _ _ hi, labelMap_lt _ _ _ hk, hcc]
    | rw [labelMap_lt _ _ _ hi, labelMap_eq _ _ _ hk, diagramWeight_comm, hvc]
    | rw [labelMap_lt _ _ _ hi, labelMap_last _ _ _ hk, diagramWeight_comm, huc]
    | rw [labelMap_eq _ _ _ hi, labelMap_lt _ _ _ hk, hvc]
    | rw [labelMap_eq _ _ _ hi, labelMap_eq _ _ _ hk, hvv]
    | rw [labelMap_eq _ _ _ hi, labelMap_last _ _ _ hk, diagramWeight_comm, huv]
    | rw [labelMap_last _ _ _ hi, labelMap_lt _ _ _ hk, huc]
    | rw [labelMap_last _ _ _ hi, labelMap_eq _ _ _ hk, huv]
    | rw [labelMap_last _ _ _ hi, labelMap_last _ _ _ hk, huu]
  all_goals
    simp only [eTable]
    split_ifs <;> omega

/-- The arrows `cᵢ → cᵢ₊₁` of the labelled configuration. -/
private theorem labelMap_arrow {L : ℕ} {B : Matrix (Fin (L + 2)) (Fin (L + 2)) ℤ}
    {c : Fin L → Fin (L + 2)} {v₁ u : Fin (L + 2)} (hcyc : IsOrientedUnitCycle B c)
    (a k : Fin (L + 2)) (ha : (a : ℕ) < L) (hk : (k : ℕ) = ((a : ℕ) + 1) % L) :
    0 < B (labelMap c v₁ u a) (labelMap c v₁ u k) := by
  have hk' : (k : ℕ) < L := hk ▸ Nat.mod_lt _ (by omega)
  rw [labelMap_lt _ _ _ ha, labelMap_lt _ _ _ hk',
    show (⟨k, hk'⟩ : Fin L) = finRotate L ⟨a, ha⟩ from
      Fin.ext (by rwa [val_finRotate_eq_mod])]
  exact (hcyc.2 _).1

end Table

/-! ### The cases of the configuration -/

section Cases

variable {L : ℕ} {B : Matrix (Fin (L + 2)) (Fin (L + 2)) ℤ} {E : Fin (L + 2) ≃ Fin (L + 2)}
  {j α β : ℕ}

private theorem not_pos_of_pos' {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B)
    {a b : Fin n} (h : 0 < B a b) : ¬0 < B b a := by
  rcases hB.entries_sign a b with h' | h' | h' <;> omega

/-- A subdiagram on positions `ℓ` of the labelled configuration with the weights of a model. -/
private theorem exists_isShapeOf_of_eTable
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L j α β i k)
    {m : ℕ} (ℓ : Fin m → Fin (L + 2)) (hℓ : Function.Injective ℓ) (f : ℕ → ℕ → ℕ)
    (h : ∀ p q : Fin m, p ≠ q → eTable L j α β (ℓ p) (ℓ q) = orderedModel f p q) :
    ∃ v : Fin m ↪ Fin (L + 2), IsShapeOf (diagramWeight (B.submatrix v v)) m f :=
  ⟨⟨E ∘ ℓ, E.injective.comp hℓ⟩, Equiv.refl _, fun p q hpq => (hW _ _).trans (h p q hpq)⟩

/-- A crown shape of the labelled configuration, read through positions `ℓ`. -/
private theorem isCrownShape_of_eTable
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L j α β i k)
    (hA : ∀ a k : Fin (L + 2), (a : ℕ) < L → (k : ℕ) = ((a : ℕ) + 1) % L → 0 < B (E a) (E k))
    {s p q r : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hN : p + q + r + s = L + 2)
    (ℓ : Fin (L + 2) → Fin (L + 2)) (hℓ : Function.Injective ℓ)
    (hwt : ∀ i k : Fin (L + 2), i ≠ k →
      eTable L j α β (ℓ i) (ℓ k) = orderedModel (crownModel s p q r) i k)
    (harr : ∀ i k : Fin (L + 2), ((i : ℕ) + 1 = k ∧ (k : ℕ) ≤ s + 2) ∨
      ((i : ℕ) = s + 2 ∧ (k : ℕ) = 0) → (ℓ i : ℕ) < L ∧ (ℓ k : ℕ) = ((ℓ i : ℕ) + 1) % L) :
    IsCrownShape B s p q r := by
  refine ⟨hp, hq, hr, (finCongr hN).trans
    ((Equiv.ofBijective ℓ (Finite.injective_iff_bijective.1 hℓ)).trans E),
    fun i k hik => ?_, fun i k hik => ?_⟩
  · simp only [Equiv.trans_apply, finCongr_apply, Equiv.ofBijective_apply]
    rw [hW, hwt _ _ (fun h => hik (Fin.cast_injective hN h))]
    simp [orderedModel]
  · simp only [Equiv.trans_apply, finCongr_apply, Equiv.ofBijective_apply]
    obtain ⟨h1, h2⟩ := harr (Fin.cast hN i) (Fin.cast hN k) (by simpa using hik)
    exact hA _ _ h1 h2

/-- A `2`-finite crown has a mutation which is a tree, hence is of Dynkin class. -/
private theorem exists_of_isCrownShape {B : Matrix (Fin N) (Fin N) ℤ} (hB : IsTwoFinite B)
    {s p q r : ℕ} (hS : IsCrownShape B s p q r) :
    ∃ X : DynkinSymbol, X.rank = N ∧ IsOfDynkinClass B [X] := by
  obtain ⟨t, ht⟩ := exists_isTShape_matrixMutationList_of_isCrownShape hB.1 hS
  exact exists_of_isTShape_matrixMutationList hB ht

/-- The positions of a crown: the cycle rotated by `σ`, and the two last positions swapped when
`sw` holds. -/
private def ellCrown (L σ : ℕ) (sw : Bool) : Fin (L + 2) → Fin (L + 2) := fun i =>
  if (i : ℕ) < L then pos L (((i : ℕ) + σ) % L)
  else if sw then pos L (2 * L + 1 - (i : ℕ)) else pos L i

/-- The finite check that the positions `ellCrown L σ sw` exhibit a crown `S^{L-3}_{p,q,r}`. -/
private abbrev CrownCheck (L j α β σ : ℕ) (sw : Bool) (p q r : ℕ) : Prop :=
  Function.Injective (ellCrown L σ sw) ∧
    (∀ i k : Fin (L + 2), i ≠ k → eTable L j α β (ellCrown L σ sw i) (ellCrown L σ sw k) =
      orderedModel (crownModel (L - 3) p q r) i k) ∧
    ∀ i k : Fin (L + 2), ((i : ℕ) + 1 = k ∧ (k : ℕ) ≤ L - 3 + 2) ∨
      ((i : ℕ) = L - 3 + 2 ∧ (k : ℕ) = 0) →
        (ellCrown L σ sw i : ℕ) < L ∧
          (ellCrown L σ sw k : ℕ) = ((ellCrown L σ sw i : ℕ) + 1) % L

private theorem crownCheck_221 (hL : 5 ≤ L ∧ L ≤ 7) : CrownCheck L 1 1 0 0 false 2 2 1 := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

private theorem crownCheck_221' (hL : 5 ≤ L ∧ L ≤ 7) :
    CrownCheck L (L - 1) 1 0 (L - 1) true 2 2 1 := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

private theorem crownCheck_212 (hL : 5 ≤ L ∧ L ≤ 7) : CrownCheck L 2 1 0 0 false 2 1 2 := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

private theorem crownCheck_212' (hL : 5 ≤ L ∧ L ≤ 7) :
    CrownCheck L (L - 2) 1 0 (L - 2) true 2 1 2 := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

private theorem crownCheck_131 (hL : 5 ≤ L ∧ L ≤ 7) : CrownCheck L 0 0 1 (L - 1) false 1 3 1 := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

/-- A crown of the configuration gives a Dynkin class. -/
private theorem exists_of_crownCheck (hB : IsTwoFinite B)
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L j α β i k)
    (hA : ∀ a k : Fin (L + 2), (a : ℕ) < L → (k : ℕ) = ((a : ℕ) + 1) % L → 0 < B (E a) (E k))
    {σ : ℕ} {sw : Bool} {p q r : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hN : p + q + r + (L - 3) = L + 2) (h : CrownCheck L j α β σ sw p q r) :
    ∃ X : DynkinSymbol, X.rank = L + 2 ∧ IsOfDynkinClass B [X] :=
  exists_of_isCrownShape hB (isCrownShape_of_eTable hW hA hp hq hr hN _ h.1 h.2.1 h.2.2)

/-- The finite check that positions `ℓ` carry a subdiagram with the weights of the model `f`. -/
private abbrev SubCheck (L j α β m : ℕ) (ℓ : Fin m → Fin (L + 2)) (f : ℕ → ℕ → ℕ) : Prop :=
  Function.Injective ℓ ∧ ∀ p q : Fin m, p ≠ q → eTable L j α β (ℓ p) (ℓ q) = orderedModel f p q

/-- Positions `c_{j-1}, c_{j+1}, c_j, u`. -/
private def ellB3 (L j : ℕ) : Fin 4 → Fin (L + 2) :=
  ![pos L ((j + L - 1) % L), pos L ((j + 1) % L), pos L j, pos L (L + 1)]

/-- Positions `u, c_j, c_{j+1}`. -/
private def ellG2 (L j : ℕ) : Fin 3 → Fin (L + 2) :=
  ![pos L (L + 1), pos L j, pos L ((j + 1) % L)]

/-- Positions `c_{L-1}, c₁, c₀, v₁, u`. -/
private def ellD4 (L : ℕ) : Fin 5 → Fin (L + 2) :=
  ![pos L (L - 1), pos L 1, pos L 0, pos L L, pos L (L + 1)]

/-- Positions `u, v₁, c₀`. -/
private def ellG2' (L : ℕ) : Fin 3 → Fin (L + 2) :=
  ![pos L (L + 1), pos L L, pos L 0]

private theorem subCheck_B3 (hL : 5 ≤ L ∧ L ≤ 7) (hj : j < L) :
    SubCheck L j 2 0 4 (ellB3 L j) (bAffineModel 3) := by
  revert j
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

private theorem subCheck_G2 (hL : 5 ≤ L ∧ L ≤ 7) (hj : j < L) :
    SubCheck L j 3 0 3 (ellG2 L j) (g2AffineModel 1) := by
  revert j
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

private theorem subCheck_D4 (hL : 5 ≤ L ∧ L ≤ 7) :
    SubCheck L 0 1 0 5 (ellD4 L) (dAffineModel 4) := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

private theorem subCheck_B4 (hL : 5 ≤ L ∧ L ≤ 7) :
    SubCheck L 0 0 2 5 (ellD4 L) (bAffineModel 4) := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

private theorem subCheck_G2' (hL : 5 ≤ L ∧ L ≤ 7) :
    SubCheck L 0 0 3 3 (ellG2' L) (g2AffineModel 1) := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

/-- **`K = ∅`**: `u` is adjacent to `v₁` only. -/
private theorem exists_of_eTable_of_alpha_eq_zero (hL : 5 ≤ L ∧ L ≤ 7) (hB : IsTwoFinite B)
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L 0 0 β i k)
    (hA : ∀ a k : Fin (L + 2), (a : ℕ) < L → (k : ℕ) = ((a : ℕ) + 1) % L → 0 < B (E a) (E k))
    (hβ : 1 ≤ β) (hβ3 : β ≤ 3) :
    ∃ X : DynkinSymbol, X.rank = L + 2 ∧ IsOfDynkinClass B [X] := by
  interval_cases β
  · exact exists_of_crownCheck hB hW hA le_rfl (by norm_num) le_rfl (by omega) (crownCheck_131 hL)
  · obtain ⟨hinj, hval⟩ := subCheck_B4 hL
    obtain ⟨v, hv⟩ := exists_isShapeOf_of_eTable hW _ hinj _ hval
    exact absurd (hB.submatrix v) (not_isTwoFinite_of_isBAffineShape ⟨by norm_num, hv⟩)
  · obtain ⟨hinj, hval⟩ := subCheck_G2' hL
    obtain ⟨v, hv⟩ := exists_isShapeOf_of_eTable hW _ hinj _ hval
    exact absurd (hB.submatrix v) (not_isTwoFinite_of_isG2AffineShape ⟨Or.inl rfl, hv⟩)

end Cases

/-! ### The case `K = {c_j}` with `u` not adjacent to `v₁` -/

section CaseB

variable {L : ℕ} {B : Matrix (Fin (L + 2)) (Fin (L + 2)) ℤ} {E : Fin (L + 2) ≃ Fin (L + 2)}
  {j α β : ℕ}

/-- Positions of a subdiagram of shape `D₇^{(1)}` for `L = 7`, `j = 3`. -/
private def ellD7 : Fin 8 → Fin (7 + 2) := ![6, 7, 0, 1, 2, 3, 4, 8]

/-- Positions of a subdiagram of shape `D₇^{(1)}` for `L = 7`, `j = 4`. -/
private def ellD7' : Fin 8 → Fin (7 + 2) := ![1, 7, 0, 6, 5, 4, 3, 8]

/-- Positions of a tree of shape `T_{1,1,4}` for `L = 6`, `j = 3`, missing `c₁`. -/
private def ellT114 : Fin 7 → Fin (6 + 2) := ![3, 2, 7, 4, 5, 0, 6]

/-- `L = 6`, `j = 3`: the subdiagram on all indices but `c₁` has Dynkin shape `D₇`. -/
private theorem exists_of_eTable_six {B : Matrix (Fin (6 + 2)) (Fin (6 + 2)) ℤ}
    {E : Fin (6 + 2) ≃ Fin (6 + 2)} (hB : IsTwoFinite B) (hc : IsConnectedDiagram B)
    (hW : ∀ i k : Fin (6 + 2), diagramWeight B (E i) (E k) = eTable 6 3 1 0 i k) :
    ∃ X : DynkinSymbol, X.rank = 6 + 2 ∧ IsOfDynkinClass B [X] := by
  have hℓ : Function.Injective ellT114 := by decide
  have hval : ∀ p q : Fin 7, p ≠ q →
      eTable 6 3 1 0 (ellT114 p) (ellT114 q) = orderedModel (tShapeModel 1 1 4) p q := by
    decide
  have hmiss : ∀ p, ellT114 p ≠ 1 := by decide
  let r : Fin 7 ↪ Fin (7 + 1) := ⟨E ∘ ellT114, E.injective.comp hℓ⟩
  have hr : Set.range r = {E 1}ᶜ :=
    range_eq_compl_singleton' r (fun ⟨p, hp⟩ => hmiss p (E.injective hp))
  exact exists_isOfDynkinClass_of_diagramEquiv_hasDynkinShape_D (M := 7) (by norm_num) hB hc hr
    (hasDynkinShape_D_of_isTShape (skewSymmetrizable_submatrix hB.1 r) (by norm_num)
      (show IsTShape (diagramWeight (B.submatrix r r)) 1 1 (7 - 3) from
        ⟨Equiv.refl _, fun p q hpq => (hW _ _).trans (hval p q hpq)⟩))
    (DiagramEquiv.refl _)

/-- **`K = {c_j}`, `u` not adjacent to `v₁`.** -/
private theorem exists_of_eTable_of_beta_eq_zero (hL : 5 ≤ L ∧ L ≤ 7) (hB : IsTwoFinite B)
    (hc : IsConnectedDiagram B) (hj : j < L) (hα : 1 ≤ α) (hα3 : α ≤ 3)
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L j α 0 i k)
    (hA : ∀ a k : Fin (L + 2), (a : ℕ) < L → (k : ℕ) = ((a : ℕ) + 1) % L → 0 < B (E a) (E k)) :
    ∃ X : DynkinSymbol, X.rank = L + 2 ∧ IsOfDynkinClass B [X] := by
  interval_cases α
  · obtain rfl | rfl | rfl | rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ : j = 0 ∨ j = 1 ∨
        j = L - 1 ∨ j = 2 ∨ j = L - 2 ∨ (L = 6 ∧ j = 3) ∨ (L = 7 ∧ (j = 3 ∨ j = 4)) := by omega
    · obtain ⟨hinj, hval⟩ := subCheck_D4 hL
      obtain ⟨v, hv⟩ := exists_isShapeOf_of_eTable hW _ hinj _ hval
      exact absurd (hB.submatrix v) (not_isTwoFinite_of_isDAffineShape ⟨le_rfl, hv⟩)
    · exact exists_of_crownCheck hB hW hA (by norm_num) (by norm_num) le_rfl (by omega)
        (crownCheck_221 hL)
    · exact exists_of_crownCheck hB hW hA (by norm_num) (by norm_num) le_rfl (by omega)
        (crownCheck_221' hL)
    · exact exists_of_crownCheck hB hW hA (by norm_num) le_rfl (by norm_num) (by omega)
        (crownCheck_212 hL)
    · exact exists_of_crownCheck hB hW hA (by norm_num) le_rfl (by norm_num) (by omega)
        (crownCheck_212' hL)
    · exact exists_of_eTable_six hB hc hW
    · have h : SubCheck 7 3 1 0 8 ellD7 (dAffineModel 7) := by decide
      obtain ⟨v, hv⟩ := exists_isShapeOf_of_eTable hW _ h.1 _ h.2
      exact absurd (hB.submatrix v) (not_isTwoFinite_of_isDAffineShape ⟨by norm_num, hv⟩)
    · have h : SubCheck 7 4 1 0 8 ellD7' (dAffineModel 7) := by decide
      obtain ⟨v, hv⟩ := exists_isShapeOf_of_eTable hW _ h.1 _ h.2
      exact absurd (hB.submatrix v) (not_isTwoFinite_of_isDAffineShape ⟨by norm_num, hv⟩)
  · obtain ⟨hinj, hval⟩ := subCheck_B3 hL hj
    obtain ⟨v, hv⟩ := exists_isShapeOf_of_eTable hW _ hinj _ hval
    exact absurd (hB.submatrix v) (not_isTwoFinite_of_isBAffineShape ⟨le_rfl, hv⟩)
  · obtain ⟨hinj, hval⟩ := subCheck_G2 hL hj
    obtain ⟨v, hv⟩ := exists_isShapeOf_of_eTable hW _ hinj _ hval
    exact absurd (hB.submatrix v) (not_isTwoFinite_of_isG2AffineShape ⟨Or.inl rfl, hv⟩)

end CaseB

/-! ### The case `K = {c_j}` with `u` adjacent to `v₁` -/

section CaseD

variable {L : ℕ} {B : Matrix (Fin (L + 2)) (Fin (L + 2)) ℤ} {E : Fin (L + 2) ≃ Fin (L + 2)}
  {j α β : ℕ}

/-- A chordless cycle of the labelled configuration, read through positions `ℓ`. -/
private theorem isChordlessCycle_of_eTable
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L j α β i k)
    (hα : 1 ≤ α) (hβ : 1 ≤ β) {m : ℕ} (hm : 3 ≤ m) (ℓ : Fin m → Fin (L + 2))
    (hℓ : Function.Injective ℓ)
    (h : ∀ p q : Fin m, p ≠ q → (0 < eTable L j 1 1 (ℓ p) (ℓ q) ↔
      (q : ℕ) = ((p : ℕ) + 1) % m ∨ (p : ℕ) = ((q : ℕ) + 1) % m)) :
    IsChordlessCycle B (E ∘ ℓ) := by
  refine ⟨hm, E.injective.comp hℓ, fun p q hpq => ?_⟩
  rw [diagramGraph_adj, Function.comp_apply, Function.comp_apply, hW, eTable_pos_iff hα hβ,
    h p q hpq, Fin.ext_iff, Fin.ext_iff, val_finRotate_eq_mod, val_finRotate_eq_mod]
  exact ⟨And.right, fun h' => ⟨(E.injective.comp hℓ).ne hpq, h'⟩⟩

/-- A chordless cycle of a `2`-finite matrix with one arrow `x_{p₀} → x_{p₀+1}` has all arrows
`x_p → x_{p+1}`. -/
private theorem forall_pos_of_isChordlessCycle {B : Matrix (Fin n) (Fin n) ℤ} (hB : IsTwoFinite B)
    {m : ℕ} {x : Fin m → Fin n} (hx : IsChordlessCycle B x) (p₀ : Fin m)
    (h₀ : 0 < B (x p₀) (x (finRotate m p₀))) (p : Fin m) :
    0 < B (x p) (x (finRotate m p)) := by
  rcases (hB.isCyclicallyOriented_of_isChordlessCycle hx).1 with h | h
  · exact h p
  · exact absurd (h p₀) (not_pos_of_pos' hB.1 h₀)

private theorem finRotate_mk' {m p : ℕ} (hp : p + 1 < m) :
    finRotate m ⟨p, by omega⟩ = ⟨p + 1, hp⟩ :=
  Fin.ext (by rw [val_finRotate_eq_mod, Nat.mod_eq_of_lt hp])

/-- The cycle `(v₁, c₀, c₁, …, c_j, u)`. -/
private def ellCyc₁ (L j : ℕ) : Fin (j + 3) → Fin (L + 2) := fun p =>
  if (p : ℕ) = 0 then pos L L else if (p : ℕ) ≤ j + 1 then pos L ((p : ℕ) - 1) else pos L (L + 1)

/-- The cycle `(c₀, v₁, u, c_j, c_{j+1}, …, c_{L-1})`. -/
private def ellCyc₂ (L j : ℕ) : Fin (L - j + 3) → Fin (L + 2) := fun p =>
  if (p : ℕ) = 0 then pos L 0 else if (p : ℕ) = 1 then pos L L
  else if (p : ℕ) = 2 then pos L (L + 1) else pos L (j + (p : ℕ) - 3)

/-- The finite check that a sequence of positions is a chordless cycle when all of `α, β` are
positive. -/
private abbrev CycleCheck (L j m : ℕ) (ℓ : Fin m → Fin (L + 2)) : Prop :=
  Function.Injective ℓ ∧ ∀ p q : Fin m, p ≠ q → (0 < eTable L j 1 1 (ℓ p) (ℓ q) ↔
    (q : ℕ) = ((p : ℕ) + 1) % m ∨ (p : ℕ) = ((q : ℕ) + 1) % m)

private theorem cycleCheck_cyc (hL : 5 ≤ L ∧ L ≤ 7) (hj₂ : 2 ≤ j) (hjL : j ≤ L - 2) :
    CycleCheck L j (j + 3) (ellCyc₁ L j) ∧ CycleCheck L j (L - j + 3) (ellCyc₂ L j) := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> interval_cases j <;> decide

/-- **`K = {c_j}`, `u` adjacent to `v₁`, `c_j` not adjacent to `c₀`**: impossible, as two
chordless cycles force opposite arrows between `c₀` and `v₁`. -/
private theorem false_of_eTable_cycles (hL : 5 ≤ L ∧ L ≤ 7) (hB : IsTwoFinite B)
    (hj₂ : 2 ≤ j) (hjL : j ≤ L - 2) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L j α β i k)
    (hA : ∀ a k : Fin (L + 2), (a : ℕ) < L → (k : ℕ) = ((a : ℕ) + 1) % L → 0 < B (E a) (E k)) :
    False := by
  obtain ⟨⟨h1i, h1⟩, ⟨h2i, h2⟩⟩ := cycleCheck_cyc hL hj₂ hjL
  have hx₁ := isChordlessCycle_of_eTable hW hα hβ (by omega) _ h1i h1
  have hx₂ := isChordlessCycle_of_eTable hW hα hβ (by omega) _ h2i h2
  have hL2 : ∀ x, x < L + 2 → (pos L x : ℕ) = x := fun x hx => val_pos' hx
  have e₁ := forall_pos_of_isChordlessCycle hB hx₁ ⟨1, by omega⟩ (by
    rw [finRotate_mk' (by omega)]
    simp only [Function.comp_apply, ellCyc₁]
    simp only [show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega, if_false,
      show (1 : ℕ) ≤ j + 1 by omega, show (2 : ℕ) ≤ j + 1 by omega, if_true]
    exact hA _ _ (by rw [hL2 _ (by omega)]; omega)
      (by rw [hL2 _ (by omega), hL2 _ (by omega), Nat.mod_eq_of_lt (by omega)]))
    ⟨0, by omega⟩
  have e₂ := forall_pos_of_isChordlessCycle hB hx₂ ⟨3, by omega⟩ (by
    rw [finRotate_mk' (by omega)]
    simp only [Function.comp_apply, ellCyc₂]
    simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
      show (3 + 1 : ℕ) ≠ 0 by omega, show (3 + 1 : ℕ) ≠ 1 by omega,
      show (3 + 1 : ℕ) ≠ 2 by omega, if_false]
    exact hA _ _ (by rw [hL2 _ (by omega)]; omega)
      (by rw [hL2 _ (by omega), hL2 _ (by omega), Nat.mod_eq_of_lt (by omega)]; omega))
    ⟨0, by omega⟩
  rw [finRotate_mk' (by omega)] at e₁ e₂
  simp only [Function.comp_apply, ellCyc₁, ellCyc₂, if_true, show (0 + 1 : ℕ) ≠ 0 by omega,
    show (0 + 1 : ℕ) ≤ j + 1 by omega, if_false, Nat.sub_self] at e₁ e₂
  exact not_pos_of_pos' hB.1 e₁ (by simpa using e₂)

/-- The path `(v₁, u, c₁, …, c_{L-1})` if `j = 1`, `(v₁, u, c_{L-1}, …, c₁)` otherwise. -/
private def ellPath (L j : ℕ) : Fin (L + 1) → Fin (L + 2) := fun p =>
  if (p : ℕ) = 0 then pos L L else if (p : ℕ) = 1 then pos L (L + 1)
  else if j = 1 then pos L ((p : ℕ) - 1) else pos L (L + 1 - (p : ℕ))

private theorem ellPath_spec (hL : 5 ≤ L ∧ L ≤ 7) (hj : j = 1 ∨ j = L - 1) :
    Function.Injective (ellPath L j) ∧ (∀ p, ellPath L j p ≠ pos L 0) ∧
      ∀ p q : Fin (L + 1), p ≠ q → (0 < eTable L j 1 1 (ellPath L j p) (ellPath L j q) ↔
        (p : ℕ) + 1 = q ∨ (q : ℕ) + 1 = p) := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> rcases hj with rfl | rfl <;> decide

/-- **`K = {c_j}`, `u` adjacent to `v₁`, `c_j` adjacent to `c₀`**: the subdiagram on all
indices but `c₀` is a path. -/
private theorem exists_of_eTable_path (hL : 5 ≤ L ∧ L ≤ 7) (hB : IsTwoFinite B)
    (hc : IsConnectedDiagram B) (hj : j = 1 ∨ j = L - 1) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L j α β i k) :
    ∃ X : DynkinSymbol, X.rank = L + 2 ∧ IsOfDynkinClass B [X] := by
  obtain ⟨hinj, hmiss, hadj⟩ := ellPath_spec hL hj
  let r : Fin (L + 1) ↪ Fin (L + 1 + 1) := ⟨E ∘ ellPath L j, E.injective.comp hinj⟩
  have hr : Set.range r = {E (pos L 0)}ᶜ :=
    range_eq_compl_singleton' r (fun ⟨p, hp⟩ => hmiss p (E.injective hp))
  have hCp : IsPathDiagram (B.submatrix r r) := by
    refine ⟨Equiv.refl _, by omega, Function.injective_id, fun p q hpq => ?_⟩
    change (diagramGraph (B.submatrix r r)).Adj p q ↔ _
    rw [diagramGraph_adj]
    change p ≠ q ∧ 0 < diagramWeight B (E (ellPath L j p)) (E (ellPath L j q)) ↔ _
    rw [hW, eTable_pos_iff hα hβ, ← hadj p q hpq]
    exact ⟨And.right, fun h => ⟨hpq, h⟩⟩
  exact exists_isOfDynkinClass_of_diagramEquiv_isPathDiagram (M := L + 1) (by omega) hB hc hr
    (skewSymmetrizable_submatrix hB.1 r) hCp (DiagramEquiv.refl _)

end CaseD

/-! ### The triangle `(c₀, v₁, u)` -/

section Triangle

variable {L : ℕ} {B : Matrix (Fin (L + 2)) (Fin (L + 2)) ℤ} {E : Fin (L + 2) ≃ Fin (L + 2)}
  {α β : ℕ}

/-- If `i → k → j → i` and `w(i, k) w(k, j) = w(i, j)`, then `μ_k` removes the pair `{i, j}`. -/
private theorem diagramWeight_matrixMutation_eq_zero_of_triangle {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {i k j : Fin n} (hik : 0 < B i k) (hkj : 0 < B k j)
    (hji : 0 < B j i) (hw : diagramWeight B i k * diagramWeight B k j = diagramWeight B i j) :
    diagramWeight (matrixMutation le_rfl B k) i j = 0 := by
  obtain ⟨d, hd⟩ := id hB
  have hB' : SkewSymmetrizable (matrixMutation le_rfl B k) := ⟨d, hd.matrixMutation le_rfl k⟩
  have h₁ := (hB.skewSymmetrization_matrixMutation_of_pos_pos hik hkj).1
  have hij : B i j < 0 := (hd.pos_iff_neg j i).1 hji
  have h₂ := (hB.skewSymmetrization_apply i j).1
  rw [Real.sign_of_neg (by exact_mod_cast hij)] at h₂
  have h₃ := (hB'.skewSymmetrization_apply i j).2.1
  rw [h₁, h₂, ← Nat.cast_mul, hw] at h₃
  have : ((diagramWeight (matrixMutation le_rfl B k) i j : ℕ) : ℝ) = 0 := by
    rw [← h₃]
    ring
  exact_mod_cast this

/-- `μ_k` keeps the weight and the entry of a pair `{a, b}` one of whose indices is not adjacent
to `k`. -/
private theorem matrixMutation_of_diagramWeight_eq_zero {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {k a b : Fin n} (ha : a ≠ k) (hb : b ≠ k)
    (h₀ : diagramWeight B a k = 0 ∨ diagramWeight B b k = 0) :
    diagramWeight (matrixMutation le_rfl B k) a b = diagramWeight B a b ∧
      matrixMutation le_rfl B k a b = B a b := by
  have hz : ∀ x, diagramWeight B x k = 0 → B x k = 0 ∧ B k x = 0 := fun x hx => by
    refine ⟨?_, ?_⟩
    · by_contra h
      exact absurd ((hB.diagramWeight_pos_iff x k).2 h) (by omega)
    · by_contra h
      rw [diagramWeight_comm] at hx
      exact absurd ((hB.diagramWeight_pos_iff k x).2 h) (by omega)
  have e : matrixMutation le_rfl B k a b = B a b ∧ matrixMutation le_rfl B k b a = B b a := by
    rcases h₀ with h | h
    · obtain ⟨h₁, h₂⟩ := hz a h
      exact ⟨matrixMutation_apply_of_eq_zero le_rfl B k ha hb (Or.inl h₁),
        matrixMutation_apply_of_eq_zero le_rfl B k hb ha (Or.inr h₂)⟩
    · obtain ⟨h₁, h₂⟩ := hz b h
      exact ⟨matrixMutation_apply_of_eq_zero le_rfl B k ha hb (Or.inr h₂),
        matrixMutation_apply_of_eq_zero le_rfl B k hb ha (Or.inl h₁)⟩
  exact ⟨by rw [diagramWeight, diagramWeight, e.1, e.2], e.1⟩

/-- The triangle `(c₀, v₁, u)`. -/
private def ellTri (L : ℕ) : Fin 3 → Fin (L + 2) := ![pos L 0, pos L L, pos L (L + 1)]

private theorem ellTri_spec (hL : 5 ≤ L ∧ L ≤ 7) :
    CycleCheck L 0 3 (ellTri L) ∧ ∀ α < 4, ∀ β < 4,
      eTable L 0 α β (ellTri L 0) (ellTri L 1) = 1 ∧
      eTable L 0 α β (ellTri L 1) (ellTri L 2) = β ∧
      eTable L 0 α β (ellTri L 2) (ellTri L 0) = α := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

/-- The weights of a chordless triangle starting with weight `1`. -/
private theorem eq_of_isAdmissibleCycleWeights_three {w : Fin 3 → ℕ} {α β : ℕ} (hw₀ : w 0 = 1)
    (hw₁ : w 1 = β) (hw₂ : w 2 = α) (hadm : IsAdmissibleCycleWeights w) : α = β := by
  rcases hadm with h | ⟨h, hmem⟩ | ⟨h, -⟩
  · have := h 1
    have := h 2
    omega
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h' | h' | h' <;>
    · have e₀ := congrFun h' 0
      have e₁ := congrFun h' 1
      have e₂ := congrFun h' 2
      simp at e₀ e₁ e₂
      omega
  · omega

/-- `E i` is the index `v₁` exactly at the position `L`. -/
private theorem eq_pos_self_iff {i : Fin (L + 2)} : E i = E (pos L L) ↔ (i : ℕ) = L := by
  rw [E.injective.eq_iff, Fin.ext_iff, val_pos' (by omega)]

/-- After `μ_{v₁}` removes the pair `{u, c₀}`, the configuration has the weights of `eTable` with
`α = 0`. -/
private theorem matrixMutation_eTable_weight (hL : 2 ≤ L) (hBs : SkewSymmetrizable B)
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L 0 α β i k)
    (hzero : diagramWeight (matrixMutation le_rfl B (E (pos L L))) (E (pos L 0))
      (E (pos L (L + 1))) = 0) (i k : Fin (L + 2)) :
    diagramWeight (matrixMutation le_rfl B (E (pos L L))) (E i) (E k) = eTable L 0 0 β i k := by
  by_cases hik : i = k
  · subst hik
    obtain ⟨d, hd⟩ := hBs
    rw [SkewSymmetrizable.diagramWeight_self ⟨d, hd.matrixMutation le_rfl _⟩]
    simp [eTable]
  have hik' : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
  by_cases hp : ((i : ℕ) = 0 ∧ (k : ℕ) = L + 1) ∨ ((i : ℕ) = L + 1 ∧ (k : ℕ) = 0)
  · rcases hp with ⟨hi, hk⟩ | ⟨hi, hk⟩
    · rw [show i = pos L 0 from Fin.ext (by rw [hi, val_pos' (by omega)]),
        show k = pos L (L + 1) from Fin.ext (by rw [hk, val_pos' (by omega)]), hzero,
        val_pos' (by omega), val_pos' (by omega)]
      simp only [eTable]
      split_ifs <;> omega
    · rw [show i = pos L (L + 1) from Fin.ext (by rw [hi, val_pos' (by omega)]),
        show k = pos L 0 from Fin.ext (by rw [hk, val_pos' (by omega)]), diagramWeight_comm,
        hzero, val_pos' (by omega), val_pos' (by omega)]
      simp only [eTable]
      split_ifs <;> omega
  by_cases hiL : (i : ℕ) = L
  · have h := (eq_pos_self_iff (E := E)).2 hiL
    rw [h, (hBs.diagramWeight_matrixMutation_self (E (pos L L)) (E k)).2.1, ← h, hW]
    simp only [eTable]
    split_ifs <;> omega
  by_cases hkL : (k : ℕ) = L
  · have h := (eq_pos_self_iff (E := E)).2 hkL
    rw [h, (hBs.diagramWeight_matrixMutation_self (E (pos L L)) (E i)).1, ← h, hW]
    simp only [eTable]
    split_ifs <;> omega
  have h₀ : diagramWeight B (E i) (E (pos L L)) = 0 ∨
      diagramWeight B (E k) (E (pos L L)) = 0 := by
    rw [hW, hW, val_pos' (by omega)]
    simp only [eTable]
    split_ifs <;> omega
  rw [(matrixMutation_of_diagramWeight_eq_zero hBs (mt (eq_pos_self_iff (E := E)).1 hiL)
    (mt (eq_pos_self_iff (E := E)).1 hkL) h₀).1, hW]
  simp only [eTable]
  split_ifs <;> omega

/-- After `μ_{v₁}` removes the pair `{u, c₀}`, the configuration keeps the arrows of the cycle. -/
private theorem matrixMutation_eTable_arrow (hL : 2 ≤ L) (hBs : SkewSymmetrizable B)
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L 0 α β i k)
    (hA : ∀ a k : Fin (L + 2), (a : ℕ) < L → (k : ℕ) = ((a : ℕ) + 1) % L → 0 < B (E a) (E k))
    (a k : Fin (L + 2)) (ha : (a : ℕ) < L) (hk : (k : ℕ) = ((a : ℕ) + 1) % L) :
    0 < matrixMutation le_rfl B (E (pos L L)) (E a) (E k) := by
  have hkL : (k : ℕ) < L := hk ▸ Nat.mod_lt _ (by omega)
  have h₀ : diagramWeight B (E a) (E (pos L L)) = 0 ∨
      diagramWeight B (E k) (E (pos L L)) = 0 := by
    rw [hW, hW, val_pos' (by omega)]
    by_cases ha0 : (a : ℕ) = 0
    · rw [ha0, zero_add, Nat.mod_eq_of_lt (by omega)] at hk
      right
      simp only [eTable]
      split_ifs <;> omega
    · left
      simp only [eTable]
      split_ifs <;> omega
  rw [(matrixMutation_of_diagramWeight_eq_zero hBs (mt (eq_pos_self_iff (E := E)).1 (by omega))
    (mt (eq_pos_self_iff (E := E)).1 (by omega)) h₀).2]
  exact hA a k ha hk

/-- **`K = {c₀}`, `u` adjacent to `v₁`**: the triangle `(c₀, v₁, u)` is oriented with weights
`(1, 1, 1)` or `(1, 2, 2)`, and `μ_{v₁}` removes the pair `{u, c₀}`. -/
private theorem exists_of_eTable_triangle (hL : 5 ≤ L ∧ L ≤ 7) (hB : IsTwoFinite B)
    (hα : 1 ≤ α) (hα3 : α ≤ 3) (hβ : 1 ≤ β) (hβ3 : β ≤ 3)
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L 0 α β i k)
    (hA : ∀ a k : Fin (L + 2), (a : ℕ) < L → (k : ℕ) = ((a : ℕ) + 1) % L → 0 < B (E a) (E k)) :
    ∃ X : DynkinSymbol, X.rank = L + 2 ∧ IsOfDynkinClass B [X] := by
  obtain ⟨⟨hinj, hcyc⟩, hval⟩ := ellTri_spec hL
  obtain ⟨hv₀, hv₁, hv₂⟩ := hval α (by omega) β (by omega)
  have hx := isChordlessCycle_of_eTable hW hα hβ le_rfl _ hinj hcyc
  obtain ⟨hor, hadm⟩ := hB.isCyclicallyOriented_of_isChordlessCycle hx
  have hr₀ : finRotate 3 0 = 1 := by decide
  have hr₁ : finRotate 3 1 = 2 := by decide
  have hr₂ : finRotate 3 2 = 0 := by decide
  have hαβ : α = β := eq_of_isAdmissibleCycleWeights_three
    (by simp only [cycleWeights, hr₀, Function.comp_apply, hW, hv₀])
    (by simp only [cycleWeights, hr₁, Function.comp_apply, hW, hv₁])
    (by simp only [cycleWeights, hr₂, Function.comp_apply, hW, hv₂]) hadm
  have t₀ : ellTri L 0 = pos L 0 := rfl
  have t₁ : ellTri L 1 = pos L L := rfl
  have t₂ : ellTri L 2 = pos L (L + 1) := rfl
  rw [t₀, t₁] at hv₀
  rw [t₁, t₂] at hv₁
  rw [t₂, t₀] at hv₂
  have hzero : diagramWeight (matrixMutation le_rfl B (E (pos L L))) (E (pos L 0))
      (E (pos L (L + 1))) = 0 := by
    rcases hor with h | h
    · have a₀ := h 0
      have a₁ := h 1
      have a₂ := h 2
      simp only [Function.comp_apply, hr₀, hr₁, hr₂, t₀, t₁, t₂] at a₀ a₁ a₂
      refine diagramWeight_matrixMutation_eq_zero_of_triangle hB.1 a₀ a₁ a₂ ?_
      rw [hW, hW, diagramWeight_comm, hW, hv₀, hv₁, hv₂, hαβ, one_mul]
    · have a₀ := h 0
      have a₁ := h 1
      have a₂ := h 2
      simp only [Function.comp_apply, hr₀, hr₁, hr₂, t₀, t₁, t₂] at a₀ a₁ a₂
      rw [diagramWeight_comm]
      refine diagramWeight_matrixMutation_eq_zero_of_triangle hB.1 a₁ a₀ a₂ ?_
      rw [diagramWeight_comm, hW, diagramWeight_comm, hW, hW, hv₀, hv₁, hv₂, hαβ, mul_one]
  have hB₁ : IsTwoFinite (matrixMutation le_rfl B (E (pos L L))) :=
    hB.matrixMutationList [E (pos L L)]
  obtain ⟨X, hX, hXB⟩ := exists_of_eTable_of_alpha_eq_zero hL hB₁
    (matrixMutation_eTable_weight (by omega) hB.1 hW hzero)
    (matrixMutation_eTable_arrow (by omega) hB.1 hW hA) hβ hβ3
  exact ⟨X, hX, isOfDynkinClass_of_mutationEquiv' hB.1 hB₁.1
    (mutationEquiv_matrixMutation B _) hXB⟩

end Triangle

/-! ### The configuration of type `E` with one more vertex -/

/-- The labelled configuration with `u` adjacent to exactly one `c_j` is of Dynkin class. -/
private theorem exists_of_eTable {L : ℕ} {B : Matrix (Fin (L + 2)) (Fin (L + 2)) ℤ}
    {E : Fin (L + 2) ≃ Fin (L + 2)} {j α β : ℕ} (hL : 5 ≤ L ∧ L ≤ 7) (hB : IsTwoFinite B)
    (hc : IsConnectedDiagram B) (hj : j < L) (hα : 1 ≤ α) (hα3 : α ≤ 3) (hβ3 : β ≤ 3)
    (hW : ∀ i k : Fin (L + 2), diagramWeight B (E i) (E k) = eTable L j α β i k)
    (hA : ∀ a k : Fin (L + 2), (a : ℕ) < L → (k : ℕ) = ((a : ℕ) + 1) % L → 0 < B (E a) (E k)) :
    ∃ X : DynkinSymbol, X.rank = L + 2 ∧ IsOfDynkinClass B [X] := by
  rcases Nat.eq_zero_or_pos β with rfl | hβ
  · exact exists_of_eTable_of_beta_eq_zero hL hB hc hj hα hα3 hW hA
  · obtain rfl | h | ⟨h₂, h₃⟩ : j = 0 ∨ (j = 1 ∨ j = L - 1) ∨ (2 ≤ j ∧ j ≤ L - 2) := by omega
    · exact exists_of_eTable_triangle hL hB hα hα3 hβ hβ3 hW hA
    · exact exists_of_eTable_path hL hB hc h hα hβ hW
    · exact (false_of_eTable_cycles hL hB h₂ h₃ hα hβ hW hA).elim

/-- If `u` is adjacent to two vertices of the oriented unit cycle `c`, then `μ_u` inserts `u`
into the cycle, and `v₁` is a pendant vertex of a configuration with a longer cycle. -/
private theorem exists_of_adj_two {L : ℕ} (hL : 4 ≤ L) {B : Matrix (Fin (L + 2)) (Fin (L + 2)) ℤ}
    (hB : IsTwoFinite B) (hc : IsConnectedDiagram B) {c : Fin L → Fin (L + 2)}
    {v₁ u : Fin (L + 2)} (hv₁ : v₁ ∉ Set.range c) (hu : u ∉ Set.range c) (hv₁u : v₁ ≠ u)
    (hcyc : IsOrientedUnitCycle B c)
    (h₂ : ∃ i i', i ≠ i' ∧ (diagramGraph B).Adj u (c i) ∧ (diagramGraph B).Adj u (c i')) :
    ∃ X : DynkinSymbol, X.rank = L + 2 ∧ IsOfDynkinClass B [X] := by
  obtain ⟨p, -, -, -, -, -, hcyc'⟩ := hcyc.exists_adj_eq_of_isTwoFinite hB hL hu h₂
  have hB₁ : IsTwoFinite (matrixMutation le_rfl B u) := hB.matrixMutationList [u]
  have hv : v₁ ∉ Set.range (Fin.insertNth (α := fun _ => Fin (L + 2)) p.succ u c) := by
    rintro ⟨k, hk⟩
    rcases Fin.eq_self_or_eq_succAbove p.succ k with rfl | ⟨k', rfl⟩
    · rw [Fin.insertNth_apply_same] at hk
      exact hv₁u hk.symm
    · rw [Fin.insertNth_apply_succAbove] at hk
      exact hv₁ ⟨k', hk⟩
  obtain ⟨X, hX, hXB⟩ := IsOrientedUnitCycle.exists_isOfDynkinClass (L := L + 1) (by omega) hB₁
    ((hB.1.isConnectedDiagram_matrixMutation_iff u).2 hc) hv hcyc'
  exact ⟨X, hX, isOfDynkinClass_of_mutationEquiv' hB.1 hB₁.1
    (mutationEquiv_matrixMutation B u) hXB⟩

/-- In a connected diagram, an index of weight `0` to every index is the only index. -/
private theorem eq_of_forall_diagramWeight_eq_zero {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hc : IsConnectedDiagram B) {u v : Fin n}
    (h : ∀ x, diagramWeight B u x = 0) : v = u := by
  by_contra hvu
  refine (hB.isConnectedDiagram_iff.1 hc) ⟨{u}, ⟨u, Finset.mem_singleton_self u⟩,
    ⟨v, by simpa using hvu⟩, fun i hi k _ => ?_⟩
  rw [Finset.mem_singleton.1 hi]
  by_contra hne
  exact absurd ((hB.diagramWeight_pos_iff u k).2 hne) (by simp [h k])

/-- **The configuration of type `E` with one more vertex.** Let `L ∈ {5, 6, 7}` and let `B` be
a `2`-finite connected `(L + 2) × (L + 2)` matrix with an enumeration `c₁, …, c_L, v₁, u` of its
indices such that `(c₁, …, c_L)` is an oriented unit cycle, `w_B(v₁, c₁) = 1`, and `v₁` is
adjacent to no `cᵢ` with `i ≠ 1`. Then `B` is of Dynkin class `X` for a Dynkin symbol `X` of
rank `L + 2`. -/
@[cluster_algebras "lem_E_configuration"]
theorem IsOrientedUnitCycle.exists_isOfDynkinClass_of_pendant {L : ℕ} (hL : 5 ≤ L ∧ L ≤ 7)
    {B : Matrix (Fin (L + 2)) (Fin (L + 2)) ℤ} (hB : IsTwoFinite B) (hc : IsConnectedDiagram B)
    {c : Fin L → Fin (L + 2)} {v₁ u : Fin (L + 2)} (hv₁ : v₁ ∉ Set.range c)
    (hu : u ∉ Set.range c) (hv₁u : v₁ ≠ u) (hcyc : IsOrientedUnitCycle B c)
    (hw : diagramWeight B v₁ (c ⟨0, by omega⟩) = 1)
    (hadj : ∀ i : Fin L, (i : ℕ) ≠ 0 → ¬(diagramGraph B).Adj v₁ (c i)) :
    ∃ X : DynkinSymbol, X.rank = L + 2 ∧ IsOfDynkinClass B [X] := by
  by_cases h₂ : ∃ i i', i ≠ i' ∧ (diagramGraph B).Adj u (c i) ∧ (diagramGraph B).Adj u (c i')
  · exact exists_of_adj_two (by omega) hB hc hv₁ hu hv₁u hcyc h₂
  push Not at h₂
  have hE := labelMap_injective hcyc.1.2.1 hv₁ hu hv₁u
  set E : Fin (L + 2) ≃ Fin (L + 2) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hE)
  have hA : ∀ a k : Fin (L + 2), (a : ℕ) < L → (k : ℕ) = ((a : ℕ) + 1) % L →
      0 < B (E a) (E k) := fun a k ha hk => labelMap_arrow hcyc a k ha hk
  have hβ3 := hB.diagramWeight_le_three u v₁
  have hu0 : ∀ a : Fin L, ¬(diagramGraph B).Adj u (c a) → diagramWeight B u (c a) = 0 := by
    intro a h
    by_contra h'
    exact h ⟨fun h'' => hu ⟨a, h''.symm⟩, Nat.pos_of_ne_zero h'⟩
  by_cases hex : ∃ a, (diagramGraph B).Adj u (c a)
  · obtain ⟨a, ha⟩ := hex
    have huc : ∀ a' : Fin L, diagramWeight B u (c a') =
        if (a' : ℕ) = a then diagramWeight B u (c a) else 0 := by
      intro a'
      split_ifs with h
      · rw [show a' = a from Fin.ext h]
      · exact hu0 a' fun h' => h₂ a a' (fun h'' => h (by rw [h''])) ha h'
    have hW := labelMap_weight hB.1 hv₁ hcyc (by omega) hw hadj huc rfl a.isLt
    exact exists_of_eTable hL hB hc a.isLt ha.2 (hB.diagramWeight_le_three _ _) hβ3 hW hA
  push Not at hex
  have hW := labelMap_weight hB.1 hv₁ hcyc (by omega) hw hadj (j := 0) (α := 0)
    (fun a' => (hu0 a' (hex a')).trans (ite_self _).symm) rfl (by omega)
  refine exists_of_eTable_of_alpha_eq_zero hL hB hW hA (Nat.one_le_iff_ne_zero.2 fun h0 => ?_) hβ3
  refine hv₁u (eq_of_forall_diagramWeight_eq_zero hB.1 hc fun x => ?_)
  have hx : diagramWeight B (E (Fin.last (L + 1))) (E (E.symm x)) = _ :=
    hW (Fin.last (L + 1)) (E.symm x)
  rw [Equiv.apply_symm_apply, h0,
    show E (Fin.last (L + 1)) = u from labelMap_last c v₁ u (by simp)] at hx
  have := Fin.val_last (L + 1)
  rw [hx]
  unfold eTable
  split_ifs <;> omega

/-! ### A diagram of type `E` with one more vertex -/

section TypeE

/-- The crown `S^{L-3}_{1,2,1}` on `[0, L]`: the oriented unit cycle `(0, 1, …, L - 1)` and the
arrow `0 → L`. -/
private def crownY (L : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℤ := Matrix.of fun i k =>
  if ((i : ℕ) < L ∧ (k : ℕ) = ((i : ℕ) + 1) % L) ∨ ((i : ℕ) = 0 ∧ (k : ℕ) = L) then 1
  else if ((k : ℕ) < L ∧ (i : ℕ) = ((k : ℕ) + 1) % L) ∨ ((k : ℕ) = 0 ∧ (i : ℕ) = L) then -1
  else 0

/-- The positions of the crown `S^{L-3}_{1,2,1}` in `crownY L`: the cycle `(L - 1, 0, …, L - 2)`
and the branch `L` at `0`. -/
private def ellY (L : ℕ) : Fin (L + 1) → Fin (L + 1) := fun i =>
  if (i : ℕ) = 0 then ⟨L - 1, by omega⟩ else if (i : ℕ) < L then ⟨(i : ℕ) - 1, by omega⟩ else i

/-- The finite facts on `crownY L`. -/
private abbrev CrownYCheck (L : ℕ) : Prop :=
  (∀ i k : Fin (L + 1), crownY L i k = -crownY L k i) ∧
    Function.Injective (ellY L) ∧
    (∀ i k : Fin (L + 1), i ≠ k →
      diagramWeight (crownY L) (ellY L i) (ellY L k) =
        orderedModel (crownModel (L - 3) 1 2 1) i k) ∧
    (∀ i k : Fin (L + 1), ((i : ℕ) + 1 = k ∧ (k : ℕ) ≤ L - 3 + 2) ∨
      ((i : ℕ) = L - 3 + 2 ∧ (k : ℕ) = 0) → 0 < crownY L (ellY L i) (ellY L k)) ∧
    (∀ a b : Fin L, a ≠ b → (0 < diagramWeight (crownY L) a.castSucc b.castSucc ↔
      b = finRotate L a ∨ a = finRotate L b)) ∧
    (∀ a : Fin L, 0 < crownY L a.castSucc (finRotate L a).castSucc ∧
      diagramWeight (crownY L) a.castSucc (finRotate L a).castSucc = 1) ∧
    ∀ a : Fin L, diagramWeight (crownY L) (Fin.last L) a.castSucc = if (a : ℕ) = 0 then 1 else 0

private theorem crownY_spec {L : ℕ} (hL : 5 ≤ L ∧ L ≤ 7) : CrownYCheck L := by
  obtain ⟨h1, h2⟩ := hL
  interval_cases L <;> decide

private theorem skewSymmetrizable_crownY {L : ℕ} (hL : 5 ≤ L ∧ L ≤ 7) :
    SkewSymmetrizable (crownY L) :=
  ⟨fun _ => 1, fun _ => one_pos, fun i k => by simp [(crownY_spec hL).1 i k]⟩

private theorem isCrownShape_crownY {L : ℕ} (hL : 5 ≤ L ∧ L ≤ 7) :
    IsCrownShape (crownY L) (L - 3) 1 2 1 := by
  obtain ⟨-, hinj, hwt, harr, -⟩ := crownY_spec hL
  have hN : 1 + 2 + 1 + (L - 3) = L + 1 := by omega
  refine ⟨le_rfl, by norm_num, le_rfl, (finCongr hN).trans
    (Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)), fun i k hik => ?_,
    fun i k hik => ?_⟩
  · simp only [Equiv.trans_apply, finCongr_apply, Equiv.ofBijective_apply]
    rw [hwt _ _ (fun h => hik (Fin.cast_injective hN h))]
    simp [orderedModel]
  · simp only [Equiv.trans_apply, finCongr_apply, Equiv.ofBijective_apply]
    exact harr _ _ (by simpa using hik)

/-- A matrix of Dynkin shape `E_N` is of shape `T_{1,2,N-4}`. -/
private theorem HasDynkinShape.isTShape_E {C : Matrix (Fin N) (Fin N) ℤ}
    (hN : 6 ≤ N ∧ N ≤ 8) (h : HasDynkinShape C [DynkinSymbol.E N hN]) :
    IsTShape (diagramWeight C) 1 2 (N - 4) := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨e, he⟩ := isTShape_dynkinWeightedGraph_E hN
  exact ⟨e.trans σ, fun p q hpq => (hσ.2 _ _).trans (he p q hpq)⟩

/-- Two matrices of the same shape `T_{a,b,c}` have the same weights up to a permutation. -/
private theorem exists_perm_of_isTShape {M : ℕ} {B B' : Matrix (Fin M) (Fin M) ℤ}
    (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B') {a b c : ℕ}
    (h : IsTShape (diagramWeight B) a b c) (h' : IsTShape (diagramWeight B') a b c) :
    ∃ σ : Equiv.Perm (Fin M), ∀ i j, diagramWeight B' i j = diagramWeight B (σ i) (σ j) := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨e'.symm.trans e, fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    rw [hB'.diagramWeight_self, hB.diagramWeight_self]
  · have hne : e'.symm i ≠ e'.symm j := e'.symm.injective.ne hij
    have h₁ := he' _ _ hne
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h₁
    rw [h₁, Equiv.trans_apply, Equiv.trans_apply, he _ _ hne]

/-- A matrix of Dynkin shape `E_{L+1}` is diagram equivalent to the crown `crownY L`. -/
private theorem HasDynkinShape.diagramEquiv_crownY {L : ℕ} (hL : 5 ≤ L ∧ L ≤ 7)
    {hn : 6 ≤ L + 1 ∧ L + 1 ≤ 8} {C : Matrix (Fin (L + 1)) (Fin (L + 1)) ℤ}
    (hC : HasDynkinShape C [DynkinSymbol.E (L + 1) hn]) : DiagramEquiv C (crownY L) := by
  have hY := skewSymmetrizable_crownY hL
  obtain ⟨t, ht⟩ := exists_isTShape_matrixMutationList_of_isCrownShape hY (isCrownShape_crownY hL)
  have hYt := skewSymmetrizable_matrixMutationList hY t
  have hCs := hC.skewSymmetrizable
  have hTC := hC.isTShape_E hn
  rw [show L + 1 - 4 = L - 3 by omega] at hTC
  obtain ⟨σ, hσ⟩ := exists_perm_of_isTShape hCs hYt hTC ht
  exact (hTC.isTreeDiagram.diagramEquiv_of_diagramWeight_eq hCs hYt hσ).1.trans hCs hYt
    ((mutationEquiv_matrixMutationList (crownY L) t).diagramEquiv.symm hY hYt)

/-- A matrix whose diagram, read through `ρ`, is that of `crownY L` carries the configuration of
`IsOrientedUnitCycle.exists_isOfDynkinClass_of_pendant`: the oriented unit cycle
`ρ 0, …, ρ (L - 1)` and the pendant vertex `ρ L`. -/
private theorem isOrientedUnitCycle_of_crownY {L : ℕ} (hL : 5 ≤ L ∧ L ≤ 7)
    {B : Matrix (Fin (L + 2)) (Fin (L + 2)) ℤ} {ρ : Fin (L + 1) ↪ Fin (L + 2)}
    (hW : ∀ i k, diagramWeight (B.submatrix ρ ρ) i k = diagramWeight (crownY L) i k)
    (hA : ∀ i k, 0 < B.submatrix ρ ρ i k ↔ 0 < crownY L i k) :
    IsOrientedUnitCycle B (fun a : Fin L => ρ a.castSucc) ∧
      diagramWeight B (ρ (Fin.last L)) (ρ (Fin.castSucc ⟨0, by omega⟩)) = 1 ∧
      ∀ a : Fin L, (a : ℕ) ≠ 0 → ¬(diagramGraph B).Adj (ρ (Fin.last L)) (ρ a.castSucc) := by
  obtain ⟨-, -, -, -, hadjY, harrY, hv₁Y⟩ := crownY_spec hL
  refine ⟨⟨⟨by omega, fun a b hab => Fin.castSucc_injective _ (ρ.injective hab),
    fun a b hab => ?_⟩, fun a => ?_⟩, ?_, fun a ha h' => ?_⟩
  · rw [diagramGraph_adj, ← hadjY a b hab]
    change ρ a.castSucc ≠ ρ b.castSucc ∧
      0 < diagramWeight (B.submatrix ρ ρ) a.castSucc b.castSucc ↔ _
    rw [hW]
    exact ⟨And.right, fun h' => ⟨fun h'' => hab (Fin.castSucc_injective _ (ρ.injective h'')),
      h'⟩⟩
  · obtain ⟨h₁, h₂⟩ := harrY a
    refine ⟨(hA _ _).2 h₁, ?_⟩
    change diagramWeight (B.submatrix ρ ρ) a.castSucc (finRotate L a).castSucc = 1
    rw [hW, h₂]
  · change diagramWeight (B.submatrix ρ ρ) (Fin.last L) (Fin.castSucc ⟨0, by omega⟩) = 1
    rw [hW, hv₁Y]
    rfl
  · have h₂ := h'.2
    change 0 < diagramWeight (B.submatrix ρ ρ) (Fin.last L) a.castSucc at h₂
    rw [hW, hv₁Y, if_neg ha] at h₂
    exact lt_irrefl _ h₂

end TypeE

/-- **A diagram of type `E` with one more vertex.** Let `n ∈ {6, 7, 8}`, let `B` be a
`2`-finite connected `(n + 1) × (n + 1)` matrix, let `r` enumerate the indices other than `u`,
and let `C` have Dynkin shape `E_n` with `B^r ∼ C`. Then `B` is of Dynkin class `X` for a
Dynkin symbol `X` of rank `n + 1`. FWZ take `C` an orientation of `ω_{E_n}`; a matrix
of Dynkin shape `E_n` is a relabelling of one, which is more general. -/
@[cluster_algebras "lem_E_type_plus_vertex"]
theorem exists_isOfDynkinClass_of_diagramEquiv_hasDynkinShape_E {n : ℕ} (hn : 6 ≤ n ∧ n ≤ 8)
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hB : IsTwoFinite B) (hc : IsConnectedDiagram B)
    {u : Fin (n + 1)} {r : Fin n ↪ Fin (n + 1)} (hr : Set.range r = {u}ᶜ)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : HasDynkinShape C [DynkinSymbol.E n hn])
    (h : DiagramEquiv (B.submatrix r r) C) :
    ∃ X : DynkinSymbol, X.rank = n + 1 ∧ IsOfDynkinClass B [X] := by
  obtain ⟨L, rfl⟩ : ∃ L, n = L + 1 := ⟨n - 1, by omega⟩
  have hL : 5 ≤ L ∧ L ≤ 7 := by omega
  obtain ⟨s, π, -, hmut, -, hdiag⟩ :=
    (h.trans (skewSymmetrizable_submatrix hB.1 r) hC.skewSymmetrizable
      (hC.diagramEquiv_crownY hL)).exists_submatrix r
  set ρ : Fin (L + 1) ↪ Fin (L + 1 + 1) := π.toEmbedding.trans r with hρ
  have hBs := hB.matrixMutationList s
  obtain ⟨hW, hA⟩ :=
    ((skewSymmetrizable_submatrix hBs.1 ρ).diagram_eq_iff (skewSymmetrizable_crownY hL)).1 hdiag
  obtain ⟨hcyc, hw, hadj⟩ := isOrientedUnitCycle_of_crownY hL hW hA
  have hρu : ∀ x, ρ x ≠ u := fun x hx => (Set.ext_iff.1 hr u).1 ⟨π x, hx⟩ rfl
  obtain ⟨X, hX, hXB⟩ := hcyc.exists_isOfDynkinClass_of_pendant hL hBs
    (isConnectedDiagram_matrixMutationList hB.1 hc s) (v₁ := ρ (Fin.last L))
    (fun ⟨a, ha⟩ => (Fin.castSucc_lt_last a).ne (ρ.injective ha))
    (fun ⟨a, ha⟩ => hρu _ ha)
    (hρu _) hw hadj
  exact ⟨X, hX, isOfDynkinClass_of_mutationEquiv' hB.1 hBs.1 hmut hXB⟩

end ClusterAlgebras

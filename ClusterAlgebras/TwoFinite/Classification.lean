/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.EPlusVertex
public import ClusterAlgebras.Enumeration.Components

/-!
# Every `2`-finite diagram is of Dynkin class

We prove that every `2`-finite diagram is mutation equivalent to an orientation of a Dynkin
diagram (Fomin–Williams–Zelevinsky, Section 5.10). The connected case is by induction on the
number of vertices, removing a vertex whose removal keeps the diagram connected; the general case
splits the diagram into two parts with no adjacencies between them.

## Main results

* `ClusterAlgebras.isOfDynkinClass_append_of_split`: a matrix split into two parts with no
  adjacencies between them, whose restrictions are of Dynkin classes `X` and `Y`, is of Dynkin
  class `(X, Y)`.
* `ClusterAlgebras.IsTwoFinite.exists_isOfDynkinClass_of_isConnectedDiagram`: a connected
  `2`-finite `N × N` matrix with `N ≥ 1` is of Dynkin class `X` for a single Dynkin symbol `X` of
  rank `N`.
* `ClusterAlgebras.IsTwoFinite.exists_isOfDynkinClass`: a `2`-finite `N × N` matrix is of Dynkin
  class `X` for a list `X` of Dynkin symbols of total rank `N`.

## Implementation notes

The splitting lemma does not require both parts to be nonempty, and the classification of all
`2`-finite matrices also covers `N = 0`, where the empty list of Dynkin symbols works.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {N : ℕ}

/-! ### Block sums of Dynkin symbols and of matrices -/

/-- The total rank of a concatenation of lists of Dynkin symbols. -/
private theorem listRank_append (Xs Ys : List DynkinSymbol) :
    DynkinSymbol.listRank (Xs ++ Ys) = DynkinSymbol.listRank Xs + DynkinSymbol.listRank Ys := by
  induction Xs with
  | nil => simp [DynkinSymbol.listRank]
  | cons X Xs ih => simp [DynkinSymbol.listRank, ih, Nat.add_assoc]

/-- Block sums are associative up to relabelling. -/
private theorem exists_equiv_fromBlocks_assoc {r a b c : ℕ} (P : Matrix (Fin r) (Fin r) ℤ)
    (M : Matrix (Fin a) (Fin a) ℤ) (Q : Matrix (Fin c) (Fin c) ℤ) (L : Matrix (Fin b) (Fin b) ℤ)
    (e : Fin a ⊕ Fin c ≃ Fin b) (he : ∀ x y, L (e x) (e y) = fromBlocks M 0 0 Q x y) :
    ∃ e' : Fin (r + a) ⊕ Fin c ≃ Fin (r + b), ∀ x y,
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks P 0 0 L) (e' x) (e' y) =
        fromBlocks (reindex finSumFinEquiv finSumFinEquiv (fromBlocks P 0 0 M)) 0 0 Q x y := by
  refine ⟨(Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)).trans
    ((Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) e).trans finSumFinEquiv)), ?_⟩
  have hs := (finSumFinEquiv (m := r) (n := a)).surjective
  rintro (x | x) (y | y)
  all_goals try obtain ⟨x, rfl⟩ := hs x
  all_goals try obtain ⟨y, rfl⟩ := hs y
  all_goals try rcases x with x | x
  all_goals try rcases y with y | y
  all_goals simp [he]

/-- `C(X, Y)` is the block sum of `C(X)` and `C(Y)`, up to a relabelling of the indices. -/
private theorem exists_equiv_listCartan_append (Xs Ys : List DynkinSymbol) :
    ∃ e : Fin (DynkinSymbol.listRank Xs) ⊕ Fin (DynkinSymbol.listRank Ys) ≃
        Fin (DynkinSymbol.listRank (Xs ++ Ys)),
      ∀ x y, DynkinSymbol.listCartan (Xs ++ Ys) (e x) (e y) =
        fromBlocks (DynkinSymbol.listCartan Xs) 0 0 (DynkinSymbol.listCartan Ys) x y := by
  induction Xs with
  | nil =>
    refine ⟨Equiv.emptySum (Fin 0) _, ?_⟩
    rintro (x | x) (y | y)
    · exact x.elim0
    · exact x.elim0
    · exact y.elim0
    · rfl
  | cons X Xs ih =>
    obtain ⟨e, he⟩ := ih
    exact exists_equiv_fromBlocks_assoc X.cartan _ _ _ e he

/-- A block sum of skew-symmetrizable matrices, relabelled along a bijection, is
skew-symmetrizable. -/
private theorem SkewSymmetrizable.fromBlocks_submatrix {a b c : ℕ}
    {P : Matrix (Fin a) (Fin a) ℤ} {Q : Matrix (Fin b) (Fin b) ℤ} (hP : SkewSymmetrizable P)
    (hQ : SkewSymmetrizable Q) (f : Fin c ≃ Fin a ⊕ Fin b) :
    SkewSymmetrizable ((fromBlocks P 0 0 Q).submatrix f f) := by
  obtain ⟨dP, hdP⟩ := hP
  obtain ⟨dQ, hdQ⟩ := hQ
  refine ⟨fun i => Sum.elim dP dQ (f i), fun i => ?_, fun i j => ?_⟩
  · change 0 < Sum.elim dP dQ (f i)
    rcases f i with x | x
    exacts [hdP.1 x, hdQ.1 x]
  · change (Sum.elim dP dQ (f i) : ℤ) * fromBlocks P 0 0 Q (f i) (f j) =
      -((Sum.elim dP dQ (f j) : ℤ) * fromBlocks P 0 0 Q (f j) (f i))
    rcases f i with x | x <;> rcases f j with y | y
    · simpa using hdP.2 x y
    · simp
    · simp
    · simpa using hdQ.2 x y

/-- Mutations at indices of a part `I` with no adjacencies to its complement keep the splitting
and do not change the entries inside the complement. -/
private theorem SkewSymmetrizable.matrixMutationList_of_split {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B) {I : Finset (Fin n)}
    (hI : ∀ i ∈ I, ∀ j ∉ I, B i j = 0) {t : List (Fin n)} (ht : ∀ k ∈ t, k ∈ I) :
    SkewSymmetrizable (matrixMutationList le_rfl B t) ∧
      (∀ i ∈ I, ∀ j ∉ I, matrixMutationList le_rfl B t i j = 0) ∧
      ∀ j ∉ I, ∀ j' ∉ I, matrixMutationList le_rfl B t j j' = B j j' := by
  induction t generalizing B with
  | nil => exact ⟨hB, hI, fun _ _ _ _ => rfl⟩
  | cons k t ih =>
    have hk : k ∈ I := ht k List.mem_cons_self
    obtain ⟨d, hd⟩ := id hB
    have h₁ := hB.matrixMutation_eq_zero_of_split hI hk
    obtain ⟨h₂, h₃, h₄⟩ := ih ⟨d, hd.matrixMutation le_rfl k⟩
      (fun i hi j hj => (h₁.1 i hi j hj).1) (fun k' hk' => ht k' (List.mem_cons_of_mem _ hk'))
    refine ⟨h₂, h₃, fun j hj j' hj' => ?_⟩
    rw [matrixMutationList_cons, h₄ j hj j' hj', h₁.2 j hj j' hj']

/-- A splitting `I ⊔ Iᶜ` without adjacencies is also one of `Iᶜ ⊔ I`. -/
private theorem SkewSymmetrizable.split_compl {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {I : Finset (Fin n)} (hI : ∀ i ∈ I, ∀ j ∉ I, B i j = 0) :
    ∀ i ∈ Iᶜ, ∀ j ∉ Iᶜ, B i j = 0 := fun i hi j hj => by
  obtain ⟨d, hd⟩ := hB
  exact (hd.apply_eq_zero_comm j i).1 (hI j (by simpa using hj) i (Finset.mem_compl.1 hi))

/-- Mutating a matrix split into `I ⊔ Iᶜ`, with no adjacencies across, along `ι_I(s)` and then
`ι_{Iᶜ}(s')` gives the block sum of `μ_s(B_I)` and `μ_{s'}(B_{Iᶜ})`. -/
private theorem SkewSymmetrizable.matrixMutationList_append_of_split {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B) {I : Finset (Fin n)}
    (hsplit : ∀ i ∈ I, ∀ j ∉ I, B i j = 0) {s : List (Fin I.card)} {s' : List (Fin Iᶜ.card)}
    {B₂ : Matrix (Fin n) (Fin n) ℤ}
    (hB₂ : B₂ = matrixMutationList le_rfl B
      (s.map (I.orderEmbOfFin rfl) ++ s'.map (Iᶜ.orderEmbOfFin rfl))) :
    (∀ a b, B₂ (I.orderEmbOfFin rfl a) (I.orderEmbOfFin rfl b) =
      matrixMutationList le_rfl (componentRestriction B I) s a b) ∧
    (∀ a b, B₂ (Iᶜ.orderEmbOfFin rfl a) (Iᶜ.orderEmbOfFin rfl b) =
      matrixMutationList le_rfl (componentRestriction B Iᶜ) s' a b) ∧
    (∀ a b, B₂ (Iᶜ.orderEmbOfFin rfl a) (I.orderEmbOfFin rfl b) = 0) ∧
    ∀ a b, B₂ (I.orderEmbOfFin rfl a) (Iᶜ.orderEmbOfFin rfl b) = 0 := by
  subst hB₂
  set ιI := I.orderEmbOfFin rfl
  set ιJ := Iᶜ.orderEmbOfFin rfl
  have hmI : ∀ a, ιI a ∈ I := fun a => Finset.orderEmbOfFin_mem _ rfl a
  have hmJ : ∀ a, ιJ a ∈ Iᶜ := fun a => Finset.orderEmbOfFin_mem _ rfl a
  obtain ⟨hB₁, hsplit₁, hagree₁⟩ := hB.matrixMutationList_of_split hsplit
    (t := s.map ιI) (by simp only [List.mem_map]; rintro k ⟨a, -, rfl⟩; exact hmI a)
  set B₁ := matrixMutationList le_rfl B (s.map ιI) with hB₁def
  obtain ⟨hB₂, hsplit₂, hagree₂⟩ := hB₁.matrixMutationList_of_split (hB₁.split_compl hsplit₁)
    (t := s'.map ιJ) (by simp only [List.mem_map]; rintro k ⟨a, -, rfl⟩; exact hmJ a)
  rw [matrixMutationList_append, ← hB₁def]
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => hsplit₂ _ (hmJ a) _ (by simpa using hmI b),
    fun a b => ?_⟩
  · rw [hagree₂ _ (by simpa using hmI a) _ (by simpa using hmI b)]
    change _ = matrixMutationList le_rfl (B.submatrix ιI.toEmbedding ιI.toEmbedding) s a b
    rw [matrixMutationList_submatrix_embedding B ιI.toEmbedding s]
    rfl
  · have hJ : componentRestriction B Iᶜ = B₁.submatrix ιJ.toEmbedding ιJ.toEmbedding := by
      ext p q
      exact (hagree₁ _ (Finset.mem_compl.1 (hmJ p)) _ (Finset.mem_compl.1 (hmJ q))).symm
    rw [hJ, matrixMutationList_submatrix_embedding B₁ ιJ.toEmbedding s']
    rfl
  · obtain ⟨d, hd⟩ := hB₂
    exact (hd.apply_eq_zero_comm _ _).1 (hsplit₂ _ (hmJ b) _ (by simpa using hmI a))

/-- **Dynkin classes of a diagram split into two parts.** If `[1, N] = I ⊔ Iᶜ` with `bᵢⱼ = 0`
for `i ∈ I`, `j ∉ I`, and the restrictions `B_I`, `B_{Iᶜ}` (indices in increasing order) are of
Dynkin classes `X` and `Y`, then `B` is of Dynkin class `(X, Y)`. -/
@[cluster_algebras "lem_block_sum_dynkin_class"]
theorem isOfDynkinClass_append_of_split {B : Matrix (Fin N) (Fin N) ℤ} (hB : SkewSymmetrizable B)
    {I : Finset (Fin N)} (hsplit : ∀ i ∈ I, ∀ j ∉ I, B i j = 0)
    {Xs Ys : List DynkinSymbol} (hX : IsOfDynkinClass (componentRestriction B I) Xs)
    (hY : IsOfDynkinClass (componentRestriction B Iᶜ) Ys) :
    IsOfDynkinClass B (Xs ++ Ys) := by
  obtain ⟨CI, ⟨σI, hσI⟩, s, π, hs⟩ := hX
  obtain ⟨CJ, ⟨σJ, hσJ⟩, s', π', hs'⟩ := hY
  obtain ⟨e, he⟩ := exists_equiv_listCartan_append Xs Ys
  let E : Fin I.card ⊕ Fin Iᶜ.card ≃ Fin N := finSumEquivOfFinset rfl rfl
  have hEl : ∀ a, E (Sum.inl a) = I.orderEmbOfFin rfl a := finSumEquivOfFinset_inl rfl rfl
  have hEr : ∀ a, E (Sum.inr a) = Iᶜ.orderEmbOfFin rfl a := finSumEquivOfFinset_inr rfl rfl
  set B₂ := matrixMutationList le_rfl B
    (s.map (I.orderEmbOfFin rfl) ++ s'.map (Iᶜ.orderEmbOfFin rfl)) with hB₂def
  obtain ⟨hF₁, hF₂, hF₃, hF₄⟩ := hB.matrixMutationList_append_of_split hsplit hB₂def
  have hCI : SkewSymmetrizable CI := by simpa using hσI.1.submatrix_embedding σI.symm.toEmbedding
  have hCJ : SkewSymmetrizable CJ := by simpa using hσJ.1.submatrix_embedding σJ.symm.toEmbedding
  refine ⟨(fromBlocks CI 0 0 CJ).submatrix E.symm E.symm,
    ⟨e.symm.trans ((Equiv.sumCongr σI σJ).trans E), ?_, fun i j => ?_⟩,
    s.map (I.orderEmbOfFin rfl) ++ s'.map (Iᶜ.orderEmbOfFin rfl),
    E.symm.trans ((Equiv.sumCongr π π').trans E), ?_⟩
  · convert SkewSymmetrizable.fromBlocks_submatrix hCI hCJ
      (e.symm.trans (Equiv.sumCongr σI σJ)) using 1
    ext i j
    simp
  · obtain ⟨x, rfl⟩ := e.surjective i
    obtain ⟨y, rfl⟩ := e.surjective j
    simp only [diagramWeight, dynkinWeightedGraph, he, e.apply_eq_iff_eq, submatrix_apply,
      Equiv.trans_apply, Equiv.symm_apply_apply]
    rcases x with a | a <;> rcases y with b | b
    · simpa [diagramWeight, dynkinWeightedGraph] using hσI.2 a b
    · simp
    · simp
    · simpa [diagramWeight, dynkinWeightedGraph] using hσJ.2 a b
  · rw [← hB₂def, ClusterAlgebras.diagram_eq_iff]
    rw [ClusterAlgebras.diagram_eq_iff] at hs hs'
    intro i j
    obtain ⟨x, rfl⟩ := E.surjective i
    obtain ⟨y, rfl⟩ := E.surjective j
    simp only [map_apply, submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.sumCongr_apply]
    rcases x with a | a <;> rcases y with b | b
    · simpa [hEl, hF₁] using hs a b
    · simp [hEl, hEr, hF₃, hF₄]
    · simp [hEl, hEr, hF₃, hF₄]
    · simpa [hEr, hF₂] using hs' a b

/-- A relabelling `C^σ` of `C` with the identity enumeration as an induced path makes `C` a path
diagram. -/
private theorem isPathDiagram_of_isInducedPath_submatrix {K M : ℕ}
    {C : Matrix (Fin M) (Fin M) ℤ} (σ : Fin K ≃ Fin M) (h : IsInducedPath (C.submatrix σ σ) id) :
    IsPathDiagram C := by
  obtain rfl : K = M := by simpa using Fintype.card_congr σ
  refine ⟨σ, h.1, σ.injective, fun p q hpq => ?_⟩
  rw [← h.2.2 p q hpq]
  simp only [diagramGraph_adj, ne_eq, σ.apply_eq_iff_eq]
  rfl

/-- **Connected `2`-finite diagrams are of Dynkin class**: a connected `2`-finite `N × N`
matrix, `N ≥ 1`, is of Dynkin class `X` for a single Dynkin symbol `X` of rank `N`. -/
@[cluster_algebras "prop_connected_two_finite_dynkin_class"]
theorem IsTwoFinite.exists_isOfDynkinClass_of_isConnectedDiagram {B : Matrix (Fin N) (Fin N) ℤ}
    (hB : IsTwoFinite B) (hc : IsConnectedDiagram B) (hN : 1 ≤ N) :
    ∃ X : DynkinSymbol, X.rank = N ∧ IsOfDynkinClass B [X] := by
  induction N with
  | zero => omega
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · refine ⟨.A 1 le_rfl, rfl, HasDynkinShape.isOfDynkinClass ?_⟩
      exact hasDynkinShape_A_of_isInducedPath hB.1 le_rfl (v := Equiv.refl _)
        ⟨le_rfl, Function.injective_id, fun p q hpq => absurd (Fin.ext (by omega)) hpq⟩
        (fun p q h => absurd h (by omega))
    obtain ⟨u, hu⟩ := hc.exists_isConnectedDiagram_submatrix_succAbove hB.1
    let r : Fin M ↪ Fin (M + 1) := ⟨u.succAbove, Fin.succAbove_right_injective⟩
    have hr : Set.range r = {u}ᶜ := Fin.range_succAbove u
    obtain ⟨X, hX, C, ⟨σ, hσ⟩, h⟩ := ih (hB.submatrix r) hu hM
    have hCsk : SkewSymmetrizable C := by
      simpa using hσ.1.submatrix_embedding σ.symm.toEmbedding
    have key : ((∃ k hk, X = DynkinSymbol.A k hk) ∨ (∃ k hk, X = DynkinSymbol.B k hk) ∨
        (∃ k hk, X = DynkinSymbol.C k hk) ∨ X = DynkinSymbol.F₄ ∨ X = DynkinSymbol.G₂) →
        ∃ X' : DynkinSymbol, X'.rank = M + 1 ∧ IsOfDynkinClass B [X'] := fun hP =>
      exists_isOfDynkinClass_of_diagramEquiv_isPathDiagram hM hB hc hr hCsk
        (isPathDiagram_of_isInducedPath_submatrix σ
          (isInducedPath_id_of_isOrientationOfWeighted hP hσ)) h
    cases X with
    | A k hk => exact key (Or.inl ⟨k, hk, rfl⟩)
    | B k hk => exact key (Or.inr (Or.inl ⟨k, hk, rfl⟩))
    | C k hk => exact key (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
    | D k hk =>
      change k = M at hX
      subst hX
      exact exists_isOfDynkinClass_of_diagramEquiv_hasDynkinShape_D hk hB hc hr ⟨σ, hσ⟩ h
    | E k hk =>
      change k = M at hX
      subst hX
      exact exists_isOfDynkinClass_of_diagramEquiv_hasDynkinShape_E hk hB hc hr ⟨σ, hσ⟩ h
    | F₄ => exact key (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | G₂ => exact key (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- **Every `2`-finite diagram is mutation equivalent to an orientation of a Dynkin diagram**:
a `2`-finite `N × N` matrix is of Dynkin class `X` for a list `X` of Dynkin symbols of total
rank `N`. -/
@[cluster_algebras "prop_two_finite_dynkin_class"]
theorem IsTwoFinite.exists_isOfDynkinClass {B : Matrix (Fin N) (Fin N) ℤ} (hB : IsTwoFinite B) :
    ∃ Xs : List DynkinSymbol, DynkinSymbol.listRank Xs = N ∧ IsOfDynkinClass B Xs := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨[], rfl, HasDynkinShape.isOfDynkinClass ⟨Equiv.refl _, ?_, fun i => i.elim0⟩⟩
    exact ⟨fun _ => 1, fun i => i.elim0, fun i => i.elim0⟩
  by_cases hc : IsConnectedDiagram B
  · obtain ⟨X, hX, hBX⟩ := hB.exists_isOfDynkinClass_of_isConnectedDiagram hc hN
    exact ⟨[X], by simp [DynkinSymbol.listRank, hX], hBX⟩
  rw [hB.1.isConnectedDiagram_iff, not_not] at hc
  obtain ⟨I, hI, hIc, hsplit⟩ := hc
  have hcard : I.card + Iᶜ.card = N := by rw [Finset.card_add_card_compl, Fintype.card_fin]
  have h₁ : 0 < I.card := Finset.card_pos.2 hI
  have h₂ : 0 < Iᶜ.card := Finset.card_pos.2 hIc
  obtain ⟨Xs, hXs, hX⟩ := ih I.card (by omega) (hB.submatrix (I.orderEmbOfFin rfl).toEmbedding)
  obtain ⟨Ys, hYs, hY⟩ := ih Iᶜ.card (by omega) (hB.submatrix (Iᶜ.orderEmbOfFin rfl).toEmbedding)
  exact ⟨Xs ++ Ys, by rw [listRank_append, hXs, hYs, hcard],
    isOfDynkinClass_append_of_split hB.1 hsplit hX hY⟩

end ClusterAlgebras

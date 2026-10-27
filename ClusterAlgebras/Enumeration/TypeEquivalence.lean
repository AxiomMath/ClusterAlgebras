/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Enumeration.Components
public import ClusterAlgebras.TypeBC.Matrices
public import ClusterAlgebras.SkewSymmetrization

/-!
# Mutation equivalence of exchange matrices of finite type is detected by the type

Two skew-symmetrizable matrices whose Cartan counterparts are Cartan matrices of finite type are
mutation equivalent exactly when the Cartan counterparts have the same type. Consequently
the type of a seed pattern is unique.

## Main statements

* `ClusterAlgebras.DynkinSymbol.eq_of_listCartan_ne_zero`: each index of `C(X)` has at most one
  smaller neighbour.
* `ClusterAlgebras.exists_matrixMutationList_eq_of_cartanCounterpart_eq`: matrices with a
  common forest-shaped Cartan counterpart are related by mutations.
* `ClusterAlgebras.sameCartanType_iff_mutationEquiv`: matrices of finite type are mutation
  equivalent if and only if their Cartan counterparts have the same type.
* `ClusterAlgebras.IsSeedPattern.sameType_of_isPatternOfType`: the type of a seed pattern is
  unique.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

private theorem DynkinSymbol.eq_of_cartan_ne_zero (X : DynkinSymbol) {i i' j : Fin X.rank}
    (hi : i < j) (hi' : i' < j) (hij : X.cartan i j ≠ 0) (hi'j : X.cartan i' j ≠ 0) : i = i' := by
  rw [Fin.lt_def] at hi hi'
  rw [Fin.ext_iff]
  cases X <;>
    simp only [cartan, cartanA, cartanB, cartanC, cartanD, cartanE, cartanF₄, cartanG₂,
      cartanOfGraph, dynkinTreeD, dynkinTreeDRel, dynkinGraphE, dynkinERel,
      SimpleGraph.fromRel_adj, of_apply, Fin.ext_iff, ne_eq] at hij hi'j <;>
    split_ifs at hij hi'j <;> simp_all <;> omega

private theorem eq_of_reindex_fromBlocks_ne_zero {a b : ℕ} {M : Matrix (Fin a) (Fin a) ℤ}
    {N : Matrix (Fin b) (Fin b) ℤ}
    (hM : ∀ {i i' j}, i < j → i' < j → M i j ≠ 0 → M i' j ≠ 0 → i = i')
    (hN : ∀ {i i' j}, i < j → i' < j → N i j ≠ 0 → N i' j ≠ 0 → i = i')
    {i i' j : Fin (a + b)} (hi : i < j) (hi' : i' < j)
    (hij : reindex finSumFinEquiv finSumFinEquiv (fromBlocks M 0 0 N) i j ≠ 0)
    (hi'j : reindex finSumFinEquiv finSumFinEquiv (fromBlocks M 0 0 N) i' j ≠ 0) : i = i' := by
  simp only [reindex_apply, submatrix_apply] at hij hi'j
  revert hi hi' hij hi'j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i' <;>
    simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, ne_eq, not_true_eq_false, Fin.lt_def, Fin.ext_iff, Fin.val_castAdd,
      Fin.val_natAdd, IsEmpty.forall_iff, implies_true] <;>
    intro hi hi' hij hi'j
  · exact congrArg Fin.val (hM (Fin.lt_def.2 hi) (Fin.lt_def.2 hi') hij hi'j)
  all_goals first
    | omega
    | rw [hN (Fin.lt_def.2 (by omega)) (Fin.lt_def.2 (by omega)) hij hi'j]

/-- **Each index of a Dynkin Cartan matrix has at most one smaller neighbour**: for every `j`
there is at most one `i < j` with `C(X)ᵢⱼ ≠ 0`. -/
@[cluster_algebras "lem_dynkin_lower_neighbour"]
theorem DynkinSymbol.eq_of_listCartan_ne_zero (Xs : List DynkinSymbol)
    {i i' j : Fin (DynkinSymbol.listRank Xs)} (hi : i < j) (hi' : i' < j)
    (hij : DynkinSymbol.listCartan Xs i j ≠ 0) (hi'j : DynkinSymbol.listCartan Xs i' j ≠ 0) :
    i = i' := by
  induction Xs with
  | nil => exact Fin.elim0 i
  | cons X Xs ih => exact eq_of_reindex_fromBlocks_ne_zero X.eq_of_cartan_ne_zero ih hi hi' hij hi'j

private theorem isMatrixComponent_congr {C D : Matrix (Fin n) (Fin n) ℤ}
    (h : LinkedIn C = LinkedIn D) (I : Finset (Fin n)) :
    IsMatrixComponent C I ↔ IsMatrixComponent D I := by
  have : matrixComponent C = matrixComponent D := by
    funext i
    ext j
    rw [mem_matrixComponent, mem_matrixComponent, h]
  simp only [IsMatrixComponent, this]

private theorem apply_eq_zero_of_not_linkedIn {C : Matrix (Fin n) (Fin n) ℤ} {i j : Fin n}
    (h : ¬LinkedIn C i j) : C i j = 0 := by
  by_contra hij
  exact h (Relation.ReflTransGen.single hij)

private theorem SkewSymmetrizable.eq_matrixComponent {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : SkewSymmetrizable C) {I : Finset (Fin n)} (hI : IsMatrixComponent C I) {i : Fin n}
    (hi : i ∈ I) : I = matrixComponent C i :=
  (hC.existsUnique_isMatrixComponent i).unique ⟨hI, hi⟩
    ⟨⟨i, rfl⟩, mem_matrixComponent.2 Relation.ReflTransGen.refl⟩

private theorem SkewSymmetrizable.eq_of_mem_isMatrixComponent {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : SkewSymmetrizable C) {I J : Finset (Fin n)} (hI : IsMatrixComponent C I)
    (hJ : IsMatrixComponent C J) {i : Fin n} (hiI : i ∈ I) (hiJ : i ∈ J) : I = J :=
  (hC.eq_matrixComponent hI hiI).trans (hC.eq_matrixComponent hJ hiJ).symm

/-- Mutating `C` along `t` pushed into the component `I` keeps `C` skew-symmetrizable with the same
linking relation, mutates the restriction to `I` along `t`, and fixes every other component. -/
private theorem SkewSymmetrizable.matrixMutationList_map_orderEmbOfFin
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : SkewSymmetrizable C) {I : Finset (Fin n)}
    (hI : IsMatrixComponent C I) (t : List (Fin I.card)) :
    SkewSymmetrizable (matrixMutationList le_rfl C (t.map (I.orderEmbOfFin rfl))) ∧
      LinkedIn (matrixMutationList le_rfl C (t.map (I.orderEmbOfFin rfl))) = LinkedIn C ∧
      componentRestriction (matrixMutationList le_rfl C (t.map (I.orderEmbOfFin rfl))) I =
        matrixMutationList le_rfl (componentRestriction C I) t ∧
      ∀ J, IsMatrixComponent C J → J ≠ I →
        componentRestriction (matrixMutationList le_rfl C (t.map (I.orderEmbOfFin rfl))) J =
          componentRestriction C J := by
  induction t generalizing C with
  | nil => exact ⟨hC, rfl, rfl, fun _ _ _ => rfl⟩
  | cons k t ih =>
    obtain ⟨hC₁, hlink⟩ := hC.linkedIn_matrixMutation (I.orderEmbOfFin rfl k)
    have hlink' : LinkedIn (matrixMutation le_rfl C (I.orderEmbOfFin rfl k)) = LinkedIn C :=
      funext fun i => funext fun j => propext (hlink i j)
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih hC₁ ((isMatrixComponent_congr hlink' I).2 hI)
    simp only [List.map_cons, matrixMutationList_cons]
    refine ⟨h₁, h₂.trans hlink', ?_, fun J hJ hJI => ?_⟩
    · rw [h₃, componentRestriction_matrixMutation_orderEmbOfFin]
    · rw [h₄ J ((isMatrixComponent_congr hlink' J).2 hJ) hJI,
        componentRestriction_matrixMutation_of_notMem hJ]
      intro hk
      exact hJI (hC.eq_of_mem_isMatrixComponent hJ hI hk (I.orderEmbOfFin_mem rfl k))

/-- Two matrices with the same linking relation agreeing on every component are equal. -/
private theorem eq_of_componentRestriction_eq {C D : Matrix (Fin n) (Fin n) ℤ}
    (h : LinkedIn C = LinkedIn D)
    (hres : ∀ I, IsMatrixComponent C I → componentRestriction C I = componentRestriction D I) :
    C = D := by
  ext i j
  by_cases hij : LinkedIn C i j
  · have hiI : i ∈ matrixComponent C i := mem_matrixComponent.2 Relation.ReflTransGen.refl
    have hjI : j ∈ matrixComponent C i := mem_matrixComponent.2 hij
    have hrange := (matrixComponent C i).range_orderEmbOfFin rfl
    obtain ⟨p, hp⟩ : i ∈ Set.range ((matrixComponent C i).orderEmbOfFin rfl) := by rwa [hrange]
    obtain ⟨q, hq⟩ : j ∈ Set.range ((matrixComponent C i).orderEmbOfFin rfl) := by rwa [hrange]
    simpa only [componentRestriction, submatrix_apply, hp, hq] using
      congrFun (congrFun (hres _ ⟨i, rfl⟩) p) q
  · rw [apply_eq_zero_of_not_linkedIn hij,
      apply_eq_zero_of_not_linkedIn (C := D) (by rwa [← h])]

private theorem isTree_of_lower_unique {m : ℕ} {G : SimpleGraph (Fin m)} (hG : G.Connected)
    (hlow : ∀ i i' j : Fin m, i < j → i' < j → G.Adj i j → G.Adj i' j → i = i') : G.IsTree := by
  classical
  have key : ∀ a b : Fin m, G.Adj a b → ∃ i j, i < j ∧ G.Adj i j ∧ s(a, b) = s(i, j) := by
    intro a b hab
    rcases lt_or_gt_of_ne hab.ne with h | h
    · exact ⟨a, b, h, hab, rfl⟩
    · exact ⟨b, a, h, hab.symm, Sym2.eq_swap⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hG, le_antisymm ?_ hG.card_vert_le_card_edgeSet_add_one⟩
  obtain ⟨v⟩ := hG.nonempty
  let f : G.edgeSet → Fin m := fun e => e.1.sup
  have hf : Function.Injective f := by
    rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ heq
    induction e₁ using Sym2.inductionOn with | hf a b => ?_
    induction e₂ using Sym2.inductionOn with | hf c d => ?_
    obtain ⟨i, j, hij, hadj, hab⟩ := key a b h₁
    obtain ⟨i', j', hij', hadj', hcd⟩ := key c d h₂
    simp only [f, hab, hcd, Sym2.sup_mk, max_eq_right hij.le, max_eq_right hij'.le] at heq
    subst heq
    simp only [hab, hcd, hlow i i' j hij hij' hadj hadj']
  have h0 : (⟨0, v.pos⟩ : Fin m) ∉ Set.range f := by
    rintro ⟨⟨e, he⟩, hfe⟩
    induction e using Sym2.inductionOn with | hf a b => ?_
    obtain ⟨i, j, hij, -, hab⟩ := key a b he
    simp only [f, hab, Sym2.sup_mk, max_eq_right hij.le] at hfe
    subst hfe
    exact absurd hij (by simp [Fin.lt_def])
  have := Fintype.card_lt_of_injective_of_notMem f hf h0
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  simp only [Fintype.card_fin] at this
  omega

/-- Skew-symmetrizable matrices with the same Cartan counterpart have the same linking
relation. -/
private theorem linkedIn_eq_of_cartanCounterpart_eq {B B' : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B')
    (h : cartanCounterpart B = cartanCounterpart B') : LinkedIn B = LinkedIn B' := by
  obtain ⟨d, hd⟩ := hB
  obtain ⟨d', hd'⟩ := hB'
  have hne : (fun i j => B i j ≠ 0) = fun i j => B' i j ≠ 0 := by
    funext i j
    by_cases hij : i = j
    · subst hij
      simp [hd.apply_self_eq_zero, hd'.apply_self_eq_zero]
    · have := congrFun (congrFun h i) j
      simp only [cartanCounterpart, of_apply, if_neg hij, neg_inj] at this
      rw [ne_eq, ← abs_eq_zero, this, abs_eq_zero]
  unfold LinkedIn
  rw [hne]

/-- With a forest-shaped common Cartan counterpart `A`, the restrictions of `B` and `B'` to a
component of `B` are related by mutations. -/
private theorem exists_matrixMutationList_componentRestriction_eq
    {A B B' : Matrix (Fin n) (Fin n) ℤ}
    (hA : ∀ i i' j : Fin n, i < j → i' < j → A i j ≠ 0 → A i' j ≠ 0 → i = i')
    (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B') (hBA : cartanCounterpart B = A)
    (hB'A : cartanCounterpart B' = A) {I : Finset (Fin n)} (hI : IsMatrixComponent B I) :
    ∃ t, matrixMutationList le_rfl (componentRestriction B I) t = componentRestriction B' I := by
  have hlink := linkedIn_eq_of_cartanCounterpart_eq hB hB' (hBA.trans hB'A.symm)
  have hAsymm : ∀ x y, A x y ≠ 0 → A y x ≠ 0 := by
    obtain ⟨d, hd⟩ := hB
    subst hBA
    intro x y hxy
    by_cases h : x = y
    · subst h
      exact hxy
    · simp only [cartanCounterpart, of_apply, if_neg h, if_neg (Ne.symm h), ne_eq, neg_eq_zero,
        abs_eq_zero] at hxy ⊢
      rwa [← hd.apply_eq_zero_comm]
  obtain ⟨hBI, hcBI, hind, -⟩ := hB.componentRestriction_of_isMatrixComponent hI
  obtain ⟨hB'I, hcB'I, -, -⟩ := hB'.componentRestriction_of_isMatrixComponent
    ((isMatrixComponent_congr hlink I).1 hI)
  refine TypeBC.exists_matrixMutationList_eq_of_cartanCounterpart_eq hBI hB'I
    (by rw [hcBI, hcB'I, hBA, hB'A]) (isTree_of_lower_unique hind ?_)
  intro i i' j hi hi' hij hi'j
  rw [hcBI, hBA] at hij hi'j
  have hadj : ∀ {p q}, (coxeterGraph (componentRestriction A I)).Adj p q →
      A (I.orderEmbOfFin rfl p) (I.orderEmbOfFin rfl q) ≠ 0 := fun hpq =>
    (coxeterGraph_adj.1 hpq).2.elim id (hAsymm _ _)
  exact (I.orderEmbOfFin rfl).injective (hA _ _ _ ((I.orderEmbOfFin rfl).strictMono hi)
    ((I.orderEmbOfFin rfl).strictMono hi') (hadj hij) (hadj hi'j))

/-- Mutating `B` component by component along the components in `T`, each restriction can be
brought to the corresponding restriction of `B'`, leaving the other components alone. -/
private theorem SkewSymmetrizable.exists_matrixMutationList_of_forall_mem
    {B B' : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B)
    (htree : ∀ I, IsMatrixComponent B I →
      ∃ t, matrixMutationList le_rfl (componentRestriction B I) t = componentRestriction B' I)
    (T : Finset (Finset (Fin n))) (hT : ∀ I ∈ T, IsMatrixComponent B I) :
    ∃ s, SkewSymmetrizable (matrixMutationList le_rfl B s) ∧
      LinkedIn (matrixMutationList le_rfl B s) = LinkedIn B ∧
      (∀ I ∈ T, componentRestriction (matrixMutationList le_rfl B s) I =
        componentRestriction B' I) ∧
      ∀ J, IsMatrixComponent B J → J ∉ T →
        componentRestriction (matrixMutationList le_rfl B s) J = componentRestriction B J := by
  induction T using Finset.induction_on with
  | empty => exact ⟨[], hB, rfl, by simp, fun _ _ _ => rfl⟩
  | insert I T hIT ih =>
    obtain ⟨s, hs₁, hs₂, hs₃, hs₄⟩ := ih fun J hJ => hT J (Finset.mem_insert_of_mem hJ)
    have hI := hT I (Finset.mem_insert_self I T)
    obtain ⟨t, ht⟩ := htree I hI
    obtain ⟨h₁, h₂, h₃, h₄⟩ :=
      hs₁.matrixMutationList_map_orderEmbOfFin ((isMatrixComponent_congr hs₂ I).2 hI) t
    refine ⟨s ++ t.map (I.orderEmbOfFin rfl), ?_⟩
    rw [matrixMutationList_append]
    refine ⟨h₁, h₂.trans hs₂, fun J hJ => ?_, fun J hJ hJT => ?_⟩
    · rcases Finset.mem_insert.1 hJ with rfl | hJ
      · rw [h₃, hs₄ J hI hIT, ht]
      · rw [h₄ J ((isMatrixComponent_congr hs₂ J).2 (hT J (Finset.mem_insert_of_mem hJ)))
          (ne_of_mem_of_not_mem hJ hIT), hs₃ J hJ]
    · rw [h₄ J ((isMatrixComponent_congr hs₂ J).2 hJ)
          (fun h => hJT (h ▸ Finset.mem_insert_self _ _)),
        hs₄ J hJ fun h => hJT (Finset.mem_insert_of_mem h)]

/-- **Matrices with a common forest-shaped Cartan counterpart are related by mutations.** Let
`A` be an `n × n` matrix such that every `j` has at most one `i < j` with `aᵢⱼ ≠ 0`, and let
`B`, `B'` be skew-symmetrizable with `A(B) = A(B') = A`. Then `μ_s(B) = B'` for some finite
sequence `s`. -/
@[cluster_algebras "lem_common_cartan_mutation_equivalent"]
theorem exists_matrixMutationList_eq_of_cartanCounterpart_eq {A B B' : Matrix (Fin n) (Fin n) ℤ}
    (hA : ∀ i i' j : Fin n, i < j → i' < j → A i j ≠ 0 → A i' j ≠ 0 → i = i')
    (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B') (hBA : cartanCounterpart B = A)
    (hB'A : cartanCounterpart B' = A) :
    ∃ s : List (Fin n), matrixMutationList le_rfl B s = B' := by
  classical
  have hlink := linkedIn_eq_of_cartanCounterpart_eq hB hB' (hBA.trans hB'A.symm)
  obtain ⟨s, -, hs₂, hs₃, -⟩ := hB.exists_matrixMutationList_of_forall_mem
    (fun _ hI => exists_matrixMutationList_componentRestriction_eq hA hB hB' hBA hB'A hI)
    (Finset.univ.filter (IsMatrixComponent B)) (by simp)
  exact ⟨s, eq_of_componentRestriction_eq (hs₂.trans hlink) fun I hI =>
    hs₃ I (by simpa using (isMatrixComponent_congr hs₂ I).1 hI)⟩

private theorem SkewSymmetrizable.cartanCounterpart_eq_zero_of_isMatrixComponent
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : SkewSymmetrizable C) {I J : Finset (Fin n)}
    (hI : IsMatrixComponent C I) (hJ : IsMatrixComponent C J) (hIJ : I ≠ J) {i j : Fin n}
    (hi : i ∈ I) (hj : j ∈ J) : cartanCounterpart C i j = 0 := by
  have hij : i ≠ j := by
    rintro rfl
    exact hIJ (hC.eq_of_mem_isMatrixComponent hI hJ hi hj)
  have hC0 : C i j = 0 := by
    by_contra h
    have hjI : j ∈ I := by
      rw [hC.eq_matrixComponent hI hi]
      exact mem_matrixComponent.2 (Relation.ReflTransGen.single h)
    exact hIJ (hC.eq_of_mem_isMatrixComponent hI hJ hjI hj)
  simp [cartanCounterpart, hij, hC0]

private theorem sameCartanType_of_isOfDynkinType {A A' : Matrix (Fin n) (Fin n) ℤ}
    {Xs : List DynkinSymbol} (h : IsOfDynkinType A Xs) (h' : IsOfDynkinType A' Xs) :
    SameCartanType A A' := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨σ', hσ'⟩ := h'
  exact ⟨σ'.trans σ.symm, fun i j => by simp [hσ, hσ']⟩

/-- Matrices of finite type whose Cartan counterparts have the same type are mutation
equivalent. -/
private theorem SkewSymmetrizable.mutationEquiv_of_sameCartanType
    {B' B'' : Matrix (Fin n) (Fin n) ℤ} (hB' : SkewSymmetrizable B')
    (hB'' : SkewSymmetrizable B'') (hA' : IsCartanFiniteType (cartanCounterpart B'))
    (h : SameCartanType (cartanCounterpart B') (cartanCounterpart B'')) :
    MutationEquiv B' B'' := by
  obtain ⟨τ, hτ⟩ := h
  obtain ⟨Xs, σ, hσ⟩ := isOfDynkinType_of_isCartanFiniteType hA'
  let ρ := τ.trans σ
  have h₀' : cartanCounterpart (B'.submatrix σ.symm.toEmbedding σ.symm.toEmbedding) =
      DynkinSymbol.listCartan Xs := by
    rw [cartanCounterpart_submatrix]
    ext a b
    simp [hσ]
  have h₀'' : cartanCounterpart (B''.submatrix ρ.symm.toEmbedding ρ.symm.toEmbedding) =
      DynkinSymbol.listCartan Xs := by
    rw [cartanCounterpart_submatrix]
    ext a b
    simp [ρ, hτ, hσ]
  obtain ⟨s, hs⟩ := exists_matrixMutationList_eq_of_cartanCounterpart_eq
    (fun _ _ _ => DynkinSymbol.eq_of_listCartan_ne_zero Xs)
    (hB'.submatrix_embedding _) (hB''.submatrix_embedding _) h₀' h₀''
  rw [matrixMutationList_submatrix_embedding] at hs
  refine ⟨s.map σ.symm.toEmbedding, τ, ?_⟩
  ext i j
  simpa only [ρ, submatrix_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply,
    Equiv.trans_apply, Equiv.symm_trans_apply] using (congrFun (congrFun hs (ρ i)) (ρ j)).symm

/-- If `B'' = (μ_s(B'))^π` with `A(B')`, `A(B'')` of finite type, then for each component `I` of
`B'` the Cartan counterparts of the restrictions `B'_I` and `B''_{π⁻¹(I)}` are of the same
Dynkin type. -/
private theorem SkewSymmetrizable.exists_isOfDynkinType_componentRestriction
    {B' B'' : Matrix (Fin n) (Fin n) ℤ} (hB' : SkewSymmetrizable B')
    (hB'' : SkewSymmetrizable B'') (hA' : IsCartanFiniteType (cartanCounterpart B'))
    (hA'' : IsCartanFiniteType (cartanCounterpart B'')) {s : List (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : B'' = (matrixMutationList le_rfl B' s).submatrix π π)
    {I : Finset (Fin n)} (hI : IsMatrixComponent B' I) :
    ∃ X, IsOfDynkinType (cartanCounterpart (componentRestriction B' I)) [X] ∧
      IsOfDynkinType (cartanCounterpart (componentRestriction B'' (I.map π.symm.toEmbedding)))
        [X] := by
  have hcomp := hB'.isMatrixComponent_of_eq_submatrix hB'' hπ
  obtain ⟨hs₁, hs₂, hmeq⟩ := hcomp.2 I hI
  obtain ⟨-, -, hind', hfin'⟩ := hB'.componentRestriction_of_isMatrixComponent hI
  obtain ⟨-, -, hind'', hfin''⟩ :=
    hB''.componentRestriction_of_isMatrixComponent ((hcomp.1 _).2 ⟨_, hI, rfl⟩)
  obtain ⟨X, hX⟩ := cartan_killing (hfin' hA') hind'
  obtain ⟨Y, hY⟩ := cartan_killing (hfin'' hA'') hind''
  have hc := (Finset.card_map (s := I) π.symm.toEmbedding).symm
  set C := componentRestriction B'' (I.map π.symm.toEmbedding)
  have hY' :
      IsOfDynkinType (cartanCounterpart (C.submatrix (Fin.cast hc) (Fin.cast hc))) [Y] := by
    have := cartanCounterpart_submatrix C (finCongr hc).toEmbedding
    simp only [Equiv.coe_toEmbedding] at this
    change IsOfDynkinType (cartanCounterpart (C.submatrix (finCongr hc) (finCongr hc))) [Y]
    rw [this]
    exact hY.submatrix_equiv (finCongr hc)
  obtain rfl := MutationEquiv.eq_of_isOfDynkinType hs₁
    (hs₂.submatrix_embedding (finCongr hc).toEmbedding) hmeq hX hY'
  exact ⟨X, hX, hY⟩

private theorem SkewSymmetrizable.isOfDynkinType_ofFn_of_isMatrixComponent
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : SkewSymmetrizable C) {k : ℕ}
    (I : Fin k → Finset (Fin n)) (hI : ∀ q, IsMatrixComponent C (I q))
    (hIinj : Function.Injective I) (hcover : ∀ i, ∃! q, i ∈ I q) (X : Fin k → DynkinSymbol)
    (hX : ∀ q, IsOfDynkinType (cartanCounterpart (componentRestriction C (I q))) [X q]) :
    IsOfDynkinType (cartanCounterpart C) (List.ofFn X) := by
  refine isOfDynkinType_ofFn_of_blocks I hcover (fun q q' hqq' i hi j hj =>
    hC.cartanCounterpart_eq_zero_of_isMatrixComponent (hI q) (hI q') (hIinj.ne hqq') hi hj)
    X fun q => ?_
  rw [← componentRestriction, ← (hC.componentRestriction_of_isMatrixComponent (hI q)).2.1]
  exact hX q

/-- Mutation equivalent matrices of finite type have Cartan counterparts of the same type. -/
private theorem SkewSymmetrizable.sameCartanType_of_mutationEquiv
    {B' B'' : Matrix (Fin n) (Fin n) ℤ} (hB' : SkewSymmetrizable B')
    (hB'' : SkewSymmetrizable B'') (hA' : IsCartanFiniteType (cartanCounterpart B'))
    (hA'' : IsCartanFiniteType (cartanCounterpart B'')) (h : MutationEquiv B' B'') :
    SameCartanType (cartanCounterpart B') (cartanCounterpart B'') := by
  classical
  obtain ⟨s, π, hπ⟩ := h
  have hcomp := hB'.isMatrixComponent_of_eq_submatrix hB'' hπ
  let S := Finset.univ.filter (IsMatrixComponent B')
  let I : Fin S.card → Finset (Fin n) := fun q => (S.equivFin.symm q).1
  have hI : ∀ q, IsMatrixComponent B' (I q) := fun q =>
    (Finset.mem_filter.1 (S.equivFin.symm q).2).2
  have hIinj : Function.Injective I := fun q q' h =>
    S.equivFin.symm.injective (Subtype.ext h)
  let J : Fin S.card → Finset (Fin n) := fun q => (I q).map π.symm.toEmbedding
  have hJ : ∀ q, IsMatrixComponent B'' (J q) := fun q => (hcomp.1 _).2 ⟨_, hI q, rfl⟩
  have hJinj : Function.Injective J := fun q q' h => hIinj (Finset.map_injective _ h)
  choose X hX using fun q =>
    hB'.exists_isOfDynkinType_componentRestriction hB'' hA' hA'' hπ (hI q)
  have hcoverI : ∀ i, ∃! q, i ∈ I q := by
    intro i
    obtain ⟨K, ⟨hK, hiK⟩, huniq⟩ := hB'.existsUnique_isMatrixComponent i
    have hKS : K ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hK⟩
    refine ⟨S.equivFin ⟨K, hKS⟩, by simpa [I] using hiK, fun q hq => ?_⟩
    rw [← Equiv.symm_apply_eq]
    exact Subtype.ext (huniq _ ⟨hI q, hq⟩)
  exact sameCartanType_of_isOfDynkinType
    (hB'.isOfDynkinType_ofFn_of_isMatrixComponent I hI hIinj hcoverI X fun q => (hX q).1)
    (hB''.isOfDynkinType_ofFn_of_isMatrixComponent J hJ hJinj
      (fun i => by simpa [J] using hcoverI (π i)) X fun q => (hX q).2)

/-- **Mutation equivalence of exchange matrices of finite type is detected by the type.** For
skew-symmetrizable `B'`, `B''` whose Cartan counterparts are Cartan matrices of finite type,
`A(B')` and `A(B'')` have the same type if and only if `B'` and `B''` are mutation equivalent. -/
@[cluster_algebras "thm_type_mutation_equivalence"]
theorem sameCartanType_iff_mutationEquiv {B' B'' : Matrix (Fin n) (Fin n) ℤ}
    (hB' : SkewSymmetrizable B') (hB'' : SkewSymmetrizable B'')
    (hA' : IsCartanFiniteType (cartanCounterpart B'))
    (hA'' : IsCartanFiniteType (cartanCounterpart B'')) :
    SameCartanType (cartanCounterpart B') (cartanCounterpart B'') ↔ MutationEquiv B' B'' :=
  ⟨hB'.mutationEquiv_of_sameCartanType hB'' hA', hB'.sameCartanType_of_mutationEquiv hB'' hA' hA''⟩

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ}

/-- **The type of a seed pattern is unique.** If a seed pattern of rank `n` is of type `X` and
of type `Y`, then `C(X)` and `C(Y)` have the same type: `C(Y)_{σ(i) σ(j)} = C(X)ᵢⱼ` for a
bijection `σ` between their indices (both have `n` of them). -/
@[cluster_algebras "lem_pattern_type_unique"]
theorem IsSeedPattern.sameType_of_isPatternOfType (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {Xs Ys : List DynkinSymbol}
    (hX : IsPatternOfType hmn P Xs) (hY : IsPatternOfType hmn P Ys) :
    ∃ σ : Fin (DynkinSymbol.listRank Xs) ≃ Fin (DynkinSymbol.listRank Ys), ∀ i j,
      DynkinSymbol.listCartan Ys (σ i) (σ j) = DynkinSymbol.listCartan Xs i j := by
  obtain ⟨t, ht⟩ := hX
  obtain ⟨t', ht'⟩ := hY
  obtain ⟨s, hs⟩ := hP.exists_seedMutationSeq_eq hmn t t'
  have hskew : ∀ u, SkewSymmetrizable (principalPart hmn (P u).extExchangeMatrix) :=
    fun u => (hP.1 u).2
  have hequiv : MutationEquiv (principalPart hmn (P t).extExchangeMatrix)
      (principalPart hmn (P t').extExchangeMatrix) := by
    rw [hs, TypeBC.extExchangeMatrix_seedMutationSeq, TypeBC.principalPart_matrixMutationList]
    exact mutationEquiv_matrixMutationList _ _
  obtain ⟨τ, hτ⟩ := (sameCartanType_iff_mutationEquiv (hskew t) (hskew t')
    ht.isCartanFiniteType ht'.isCartanFiniteType).2 hequiv
  obtain ⟨σ, hσ⟩ := ht
  obtain ⟨ρ, hρ⟩ := ht'
  refine ⟨σ.symm.trans (τ.symm.trans ρ), fun a b => ?_⟩
  simp only [Equiv.trans_apply]
  rw [← hρ, hτ, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hσ, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

end ClusterAlgebras

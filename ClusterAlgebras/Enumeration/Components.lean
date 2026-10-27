/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Enumeration.Reindex
public import ClusterAlgebras.SkewSymmetrization

/-!
# Components of a skew-symmetrizable matrix

Two indices are *linked* in a skew-symmetrizable matrix `B` when a walk of nonzero entries joins
them; the classes are the *components* of `B`, which are the vertex sets of the connected
components of the Coxeter graph of `A(B)`. Mutation preserves the components and acts on each one
separately, so mutation equivalence matches the components of two matrices and makes their
restrictions mutation equivalent. This reduces the classification of mutation types to the
indecomposable case.

## Main definitions

* `ClusterAlgebras.LinkedIn B i j`: `i` and `j` are joined by a walk in `B`.
* `ClusterAlgebras.matrixComponent B i`: the component of `i` in `B`.
* `ClusterAlgebras.IsMatrixComponent B I`: `I` is a component of `B`.
* `ClusterAlgebras.componentRestriction B I`: the restriction `B_I`, indices of `I` in
  increasing order.

## Implementation notes

* `B_I` is `B.submatrix ι_I ι_I` for the increasing enumeration `ι_I = I.orderEmbOfFin rfl`; for
  a square matrix this is the restriction `matrixRestriction`, every index being mutable.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 5][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

/-! ### Components -/

/-- Indices `i, j` are **linked in `B`** when there is a walk `i = w₀, w₁, …, w_r = j`,
`r ≥ 0`, with `b_{w_{t-1} w_t} ≠ 0` for every `t`. -/
@[cluster_algebras "def_matrix_components"]
def LinkedIn (B : Matrix (Fin n) (Fin n) ℤ) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen fun i j => B i j ≠ 0

/-- The **component** of `i` in `B`: the set of indices linked to `i`. -/
@[cluster_algebras "def_matrix_components"]
noncomputable def matrixComponent (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Finset (Fin n) :=
  by classical exact Finset.univ.filter (LinkedIn B i)

/-- A **component** of `B`: a set of the form `matrixComponent B i`. -/
@[cluster_algebras "def_matrix_components"]
def IsMatrixComponent (B : Matrix (Fin n) (Fin n) ℤ) (I : Finset (Fin n)) : Prop :=
  ∃ i, I = matrixComponent B i

/-- The **restriction** `B_I` of a square matrix to `I ⊆ [1, n]`: the `|I| × |I|` matrix
`B^{ι_I}`, `ι_I` the increasing enumeration of `I`. -/
def componentRestriction {α : Type*} (B : Matrix (Fin n) (Fin n) α) (I : Finset (Fin n)) :
    Matrix (Fin I.card) (Fin I.card) α :=
  B.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl)

/-! ### Auxiliary facts about linking -/

/-- Membership in a component is linking: `j ∈ matrixComponent B i ↔ LinkedIn B i j`. -/
@[simp]
theorem mem_matrixComponent {B : Matrix (Fin n) (Fin n) ℤ} {i j : Fin n} :
    j ∈ matrixComponent B i ↔ LinkedIn B i j := by
  simp [matrixComponent]

/-- Every index lies in its own component. -/
@[simp]
theorem mem_matrixComponent_self (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    i ∈ matrixComponent B i :=
  mem_matrixComponent.2 Relation.ReflTransGen.refl

/-- The entries of the restriction `B_I`. -/
@[simp]
theorem componentRestriction_apply {α : Type*} (B : Matrix (Fin n) (Fin n) α)
    (I : Finset (Fin n)) (p q : Fin I.card) :
    componentRestriction B I p q = B (I.orderEmbOfFin rfl p) (I.orderEmbOfFin rfl q) :=
  rfl

/-- Linking in a simultaneous permutation `M^π` is linking of the images in `M`. -/
private theorem linkedIn_submatrix_perm (M : Matrix (Fin n) (Fin n) ℤ) (π : Equiv.Perm (Fin n))
    (i j : Fin n) : LinkedIn (M.submatrix π π) i j ↔ LinkedIn M (π i) (π j) := by
  unfold LinkedIn
  refine ⟨Relation.ReflTransGen.lift π fun _ _ hab => hab, fun h => ?_⟩
  simpa using Relation.ReflTransGen.lift (p := fun a b => M.submatrix π π a b ≠ 0) π.symm
    (fun a b hab => by simpa using hab) h

/-- Each step of a walk in `μ_k(M)` joins indices linked in `M`. -/
private theorem linkedIn_of_linkedIn_matrixMutation (M : Matrix (Fin n) (Fin n) ℤ) (k : Fin n)
    {i j : Fin n} (h : LinkedIn (matrixMutation le_rfl M k) i j) : LinkedIn M i j := by
  unfold LinkedIn at *
  refine Relation.ReflTransGen.lift' (p := fun i j => M i j ≠ 0) id (fun a b hab => ?_) h
  by_cases hk : a = Fin.castLE le_rfl k ∨ b = k
  · rw [matrixMutation_apply_of_eq le_rfl M k hk, neg_ne_zero] at hab
    exact Relation.ReflTransGen.single hab
  · push Not at hk
    by_cases hab' : M a b = 0
    · have h1 : M a k ≠ 0 ∧ M (Fin.castLE le_rfl k) b ≠ 0 := by
        by_contra hc
        rw [not_and_or, not_ne_iff, not_ne_iff] at hc
        exact hab (by rw [matrixMutation_apply_of_eq_zero le_rfl M k hk.1 hk.2 hc, hab'])
      exact Relation.ReflTransGen.tail (r := fun i j => M i j ≠ 0)
        (Relation.ReflTransGen.single (r := fun i j => M i j ≠ 0) h1.1) h1.2
    · exact Relation.ReflTransGen.single hab'

/-! ### Components of a matrix and of its Cartan counterpart -/

/-- **Being linked is an equivalence relation** for a skew-symmetrizable matrix. -/
@[cluster_algebras "lem_matrix_components"]
theorem SkewSymmetrizable.equivalence_linkedIn {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) : Equivalence (LinkedIn B) := by
  obtain ⟨d, hd⟩ := hB
  refine ⟨fun _ => Relation.ReflTransGen.refl, fun h => ?_, Relation.ReflTransGen.trans⟩
  unfold LinkedIn at *
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.head
      (fun h' => hbc ((IsSkewSymmetrizingVector.apply_eq_zero_comm hd _ _).2 h')) ih

/-- **The components partition the indices**: every index lies in exactly one component. -/
@[cluster_algebras "lem_matrix_components"]
theorem SkewSymmetrizable.existsUnique_isMatrixComponent {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (i : Fin n) : ∃! I, IsMatrixComponent B I ∧ i ∈ I := by
  refine ⟨matrixComponent B i,
    ⟨⟨i, rfl⟩, mem_matrixComponent_self B i⟩, ?_⟩
  rintro J ⟨⟨j, rfl⟩, hij⟩
  have he := hB.equivalence_linkedIn
  rw [mem_matrixComponent] at hij
  ext x
  simp only [mem_matrixComponent]
  exact ⟨fun h => he.trans (he.symm hij) h, he.trans hij⟩

/-- **The components of `B` are the vertex sets of the connected components of the Coxeter
graph of `A(B)`**: two indices are linked in `B` exactly when they are joined in the Coxeter
graph. -/
@[cluster_algebras "lem_matrix_components"]
theorem SkewSymmetrizable.linkedIn_iff_reachable {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (i j : Fin n) :
    LinkedIn B i j ↔ (coxeterGraph (cartanCounterpart B)).Reachable i j := by
  obtain ⟨d, hd⟩ := hB
  have hadj : (coxeterGraph (cartanCounterpart B)).Adj = fun a b => B a b ≠ 0 := by
    funext a b
    rw [coxeterGraph_adj]
    simp only [cartanCounterpart, Matrix.of_apply]
    refine propext ⟨fun ⟨hab, h⟩ => ?_, fun h => ?_⟩
    · rcases h with h | h
      · simpa [hab] using h
      · simp only [Ne.symm hab, if_false, ne_eq, neg_eq_zero, abs_eq_zero] at h
        exact fun h' => h ((IsSkewSymmetrizingVector.apply_eq_zero_comm hd a b).1 h')
    · have hab : a ≠ b := by
        rintro rfl
        exact h (IsSkewSymmetrizingVector.apply_self_eq_zero hd a)
      exact ⟨hab, Or.inl (by simpa [hab] using h)⟩
  rw [SimpleGraph.reachable_iff_reflTransGen, hadj]
  rfl

/-- **The restriction to a component**: for a component `I` of `B`, the matrix `B_I` is
skew-symmetrizable, `A(B_I) = A(B)_I`, `A(B_I)` is indecomposable, and if `A(B)` is a Cartan
matrix of finite type then so is `A(B_I)`. -/
@[cluster_algebras "lem_matrix_components"]
theorem SkewSymmetrizable.componentRestriction_of_isMatrixComponent
    {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B) {I : Finset (Fin n)}
    (hI : IsMatrixComponent B I) :
    SkewSymmetrizable (componentRestriction B I) ∧
      cartanCounterpart (componentRestriction B I) =
        componentRestriction (cartanCounterpart B) I ∧
      IsIndecomposable (cartanCounterpart (componentRestriction B I)) ∧
      (IsCartanFiniteType (cartanCounterpart B) →
        IsCartanFiniteType (cartanCounterpart (componentRestriction B I))) := by
  set ι := (I.orderEmbOfFin rfl).toEmbedding
  have hsk : SkewSymmetrizable (componentRestriction B I) := hB.submatrix_embedding ι
  have hcart : cartanCounterpart (componentRestriction B I) =
      componentRestriction (cartanCounterpart B) I :=
    cartanCounterpart_submatrix B ι
  refine ⟨hsk, hcart, ?_, fun hA => ?_⟩
  · obtain ⟨i, rfl⟩ := hI
    have hmem : ∀ r, ι r ∈ matrixComponent B i := Finset.orderEmbOfFin_mem _ rfl
    have hne : Nonempty (Fin (matrixComponent B i).card) :=
      ⟨⟨0, Finset.card_pos.2 ⟨i, mem_matrixComponent_self _ i⟩⟩⟩
    have he := hB.equivalence_linkedIn
    unfold IsIndecomposable
    rw [SimpleGraph.connected_iff]
    refine ⟨fun p q => (hsk.linkedIn_iff_reachable p q).1 ?_, hne⟩
    have key : ∀ x, LinkedIn B (ι p) x →
        ∃ r, ι r = x ∧ LinkedIn (componentRestriction B (matrixComponent B i)) p r := by
      intro x hx
      unfold LinkedIn at hx
      induction hx with
      | refl => exact ⟨p, rfl, Relation.ReflTransGen.refl⟩
      | @tail b c hab hbc ih =>
        obtain ⟨r, rfl, hr⟩ := ih
        have hc : c ∈ matrixComponent B i :=
          mem_matrixComponent.2 (he.trans (mem_matrixComponent.1 (hmem p))
            (Relation.ReflTransGen.tail hab hbc))
        obtain ⟨r', rfl⟩ : c ∈ Set.range ι := by
          simpa [ι, Finset.range_orderEmbOfFin] using hc
        exact ⟨r', rfl, Relation.ReflTransGen.tail hr hbc⟩
    obtain ⟨r, hr, hpr⟩ := key (ι q)
      (he.trans (he.symm (mem_matrixComponent.1 (hmem p))) (mem_matrixComponent.1 (hmem q)))
    rwa [ι.injective hr] at hpr
  · rw [hcart]
    exact hA.submatrix ι.injective

/-! ### Mutation and components -/

/-- **Mutation preserves skew-symmetrizability and the components**: `μ_k(B)` is
skew-symmetrizable, and two indices are linked in `μ_k(B)` exactly when they are linked in
`B`. -/
@[cluster_algebras "lem_components_mutation"]
theorem SkewSymmetrizable.linkedIn_matrixMutation {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (k : Fin n) :
    SkewSymmetrizable (matrixMutation le_rfl B k) ∧
      ∀ i j, LinkedIn (matrixMutation le_rfl B k) i j ↔ LinkedIn B i j := by
  obtain ⟨d, hd⟩ := hB
  refine ⟨⟨d, hd.matrixMutation le_rfl k⟩, fun i j =>
    ⟨linkedIn_of_linkedIn_matrixMutation B k, fun h => ?_⟩⟩
  refine linkedIn_of_linkedIn_matrixMutation (matrixMutation le_rfl B k) k ?_
  rwa [matrixMutation_matrixMutation le_rfl B k]

/-- **Mutation outside a component does not change its restriction**: if `k ∉ I` for a
component `I` of `B`, then `μ_k(B)_I = B_I`. FWZ take `B` skew-symmetrizable; that is
not needed. -/
@[cluster_algebras "lem_components_mutation"]
theorem componentRestriction_matrixMutation_of_notMem {B : Matrix (Fin n) (Fin n) ℤ}
    {I : Finset (Fin n)} (hI : IsMatrixComponent B I) {k : Fin n} (hk : k ∉ I) :
    componentRestriction (matrixMutation le_rfl B k) I = componentRestriction B I := by
  obtain ⟨i, rfl⟩ := hI
  ext p q
  simp only [componentRestriction, Matrix.submatrix_apply]
  have hmem : ∀ r, (matrixComponent B i).orderEmbOfFin rfl r ∈ matrixComponent B i :=
    Finset.orderEmbOfFin_mem _ rfl
  have hne : ∀ r, (matrixComponent B i).orderEmbOfFin rfl r ≠ k := fun r h => hk (h ▸ hmem r)
  refine matrixMutation_apply_of_eq_zero le_rfl B k (hne p) (hne q) (Or.inl ?_)
  by_contra h
  exact hk (mem_matrixComponent.2 ((mem_matrixComponent.1 (hmem p)).tail h))

/-- **Mutation inside a component mutates its restriction**: if `k = ι_I(q)` for a component
`I` of `B`, then `μ_k(B)_I = μ_q(B_I)`. This holds for every matrix `B` and every set `I`;
FWZ state it for a component of a skew-symmetrizable matrix. -/
@[cluster_algebras "lem_components_mutation"]
theorem componentRestriction_matrixMutation_orderEmbOfFin
    (B : Matrix (Fin n) (Fin n) ℤ) (I : Finset (Fin n)) (q : Fin I.card) :
    componentRestriction (matrixMutation le_rfl B (I.orderEmbOfFin rfl q)) I =
      matrixMutation le_rfl (componentRestriction B I) q := by
  have := matrixMutationList_submatrix_embedding B (I.orderEmbOfFin rfl).toEmbedding [q]
  simp only [matrixMutationList_singleton, List.map_cons, List.map_nil] at this
  exact this.symm

/-- Along a sequence of mutations, skew-symmetrizability and the linking relation persist, and
the restriction to each component stays in the mutation class of the original restriction. -/
private theorem SkewSymmetrizable.matrixMutationList_components {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (s : List (Fin n)) :
    SkewSymmetrizable (matrixMutationList le_rfl B s) ∧
      (∀ i j, LinkedIn (matrixMutationList le_rfl B s) i j ↔ LinkedIn B i j) ∧
      ∀ I, IsMatrixComponent B I →
        MutationEquiv (componentRestriction B I)
          (componentRestriction (matrixMutationList le_rfl B s) I) := by
  induction s generalizing B with
  | nil => exact ⟨hB, fun _ _ => Iff.rfl, fun I _ => MutationEquiv.refl _⟩
  | cons k s ih =>
    simp only [matrixMutationList_cons]
    obtain ⟨hsk, hlink⟩ := hB.linkedIn_matrixMutation k
    obtain ⟨h1, h2, h3⟩ := ih hsk
    refine ⟨h1, fun i j => (h2 i j).trans (hlink i j), fun I hI => ?_⟩
    have hI' : IsMatrixComponent (matrixMutation le_rfl B k) I := by
      obtain ⟨i, rfl⟩ := hI
      exact ⟨i, Finset.ext fun x => by simp only [mem_matrixComponent, hlink]⟩
    refine MutationEquiv.trans ?_ (h3 I hI')
    by_cases hk : k ∈ I
    · obtain ⟨q, rfl⟩ : k ∈ Set.range (I.orderEmbOfFin rfl) := by
        rwa [Finset.range_orderEmbOfFin]
      rw [componentRestriction_matrixMutation_orderEmbOfFin B I q]
      exact mutationEquiv_matrixMutation _ q
    · rw [componentRestriction_matrixMutation_of_notMem hI hk]

/-- Restricting `C^π` to `π⁻¹(I)` gives, read as an `|I| × |I|` matrix, a matrix mutation
equivalent to the restriction `C_I`. -/
theorem mutationEquiv_componentRestriction_submatrix_perm (C : Matrix (Fin n) (Fin n) ℤ)
    (π : Equiv.Perm (Fin n)) (I : Finset (Fin n)) :
    MutationEquiv (componentRestriction C I)
      ((componentRestriction (C.submatrix π π) (I.map π.symm.toEmbedding)).submatrix
        (Fin.cast (Finset.card_map _).symm) (Fin.cast (Finset.card_map _).symm)) := by
  set J := I.map π.symm.toEmbedding
  have hJ : J.card = I.card := Finset.card_map _
  have hmem : ∀ p : Fin I.card, π (J.orderEmbOfFin rfl (Fin.cast hJ.symm p)) ∈ I :=
    fun _ => Finset.mem_map_equiv.1 (J.orderEmbOfFin_mem rfl _)
  let f : Fin I.card → Fin I.card := fun p => (I.orderIsoOfFin rfl).symm ⟨_, hmem p⟩
  have hf : ∀ p, I.orderEmbOfFin rfl (f p) = π (J.orderEmbOfFin rfl (Fin.cast hJ.symm p)) := by
    intro p
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  have hfinj : Function.Injective f := fun p p' hpp' => by
    simpa [hf] using congrArg (I.orderEmbOfFin rfl) hpp'
  let ρ : Equiv.Perm (Fin I.card) := Equiv.ofBijective f hfinj.bijective_of_finite
  have hρ : (componentRestriction (C.submatrix π π) J).submatrix (Fin.cast hJ.symm)
      (Fin.cast hJ.symm) = (componentRestriction C I).submatrix ρ ρ := by
    ext p q
    simp only [componentRestriction, Matrix.submatrix_apply, ρ, Equiv.ofBijective_apply, hf]
  rw [hρ]
  exact mutationEquiv_submatrix _ ρ

/-- **Mutation equivalence matches the components.** If `B'' = (μ_s(B'))^π`, then the
components of `B''` are exactly the sets `π⁻¹(I)` for the components `I` of `B'`, and for each
component `I` of `B'` the restrictions `B'_I` and `B''_{π⁻¹(I)}` are skew-symmetrizable and
mutation equivalent; the second is read as an `|I| × |I|` matrix through `|π⁻¹(I)| = |I|`. -/
@[cluster_algebras "lem_mut_equiv_components"]
theorem SkewSymmetrizable.isMatrixComponent_of_eq_submatrix {B' B'' : Matrix (Fin n) (Fin n) ℤ}
    (hB' : SkewSymmetrizable B') (hB'' : SkewSymmetrizable B'') {s : List (Fin n)}
    {π : Equiv.Perm (Fin n)} (h : B'' = (matrixMutationList le_rfl B' s).submatrix π π) :
    (∀ J, IsMatrixComponent B'' J ↔ ∃ I, IsMatrixComponent B' I ∧ J = I.map π.symm.toEmbedding) ∧
      ∀ I, IsMatrixComponent B' I →
        SkewSymmetrizable (componentRestriction B' I) ∧
          SkewSymmetrizable (componentRestriction B'' (I.map π.symm.toEmbedding)) ∧
          MutationEquiv (componentRestriction B' I)
            ((componentRestriction B'' (I.map π.symm.toEmbedding)).submatrix
              (Fin.cast (Finset.card_map _).symm) (Fin.cast (Finset.card_map _).symm)) := by
  obtain ⟨hC, hlink, hequiv⟩ := hB'.matrixMutationList_components s
  set C := matrixMutationList le_rfl B' s
  subst h
  have hcomp : ∀ i, matrixComponent (C.submatrix π π) i =
      (matrixComponent B' (π i)).map π.symm.toEmbedding := by
    intro i
    ext x
    rw [Finset.mem_map_equiv, Equiv.symm_symm, mem_matrixComponent, mem_matrixComponent,
      linkedIn_submatrix_perm, hlink]
  refine ⟨fun J => ⟨?_, ?_⟩, fun I hI =>
    ⟨hB'.submatrix_embedding (I.orderEmbOfFin rfl).toEmbedding,
      hB''.submatrix_embedding (Finset.orderEmbOfFin _ rfl).toEmbedding, ?_⟩⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨π i, rfl⟩, hcomp i⟩
  · rintro ⟨I, ⟨a, rfl⟩, rfl⟩
    exact ⟨π.symm a, by rw [hcomp, Equiv.apply_symm_apply]⟩
  · exact (hequiv I hI).trans (mutationEquiv_componentRestriction_submatrix_perm C π I)

end ClusterAlgebras

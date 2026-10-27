/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Restriction.Enumeration

/-!
# Mutation classes of extended matrices, and heredity

Two `m × n` matrices are mutation equivalent when a sequence of mutations followed by a
simultaneous renumbering of rows and columns, keeping mutable indices mutable, carries the
first to the second [FWZ, Section 4.1]. The renumbering is a bijective restriction map from
`(m, n)` to itself.

## Main definitions

* `ClusterAlgebras.ExtMutationEquiv`: mutation equivalence of `m × n` matrices.
* `ClusterAlgebras.mutationClass`: the mutation class `[B]` of an `m × n` matrix `B`.
* `ClusterAlgebras.HasFiniteMatrixMutationType`: the mutation class of a matrix is finite.
* `ClusterAlgebras.IsHereditaryMatrixProperty`: a property of matrices preserved by
  restriction.
* `ClusterAlgebras.MutationClassEmbeddable`: some matrix of one mutation class is obtained by
  restriction from some matrix of another.

## Main results

* `ClusterAlgebras.isHereditaryMatrixProperty_hasFiniteMatrixMutationType`: finite mutation
  type is hereditary [FWZ, Proposition 4.1.4].
* `ClusterAlgebras.exists_obtainedByRestriction_iff_forall`: restriction descends to mutation
  classes [FWZ, Lemma 4.1.8].
* `ClusterAlgebras.MutationClassEmbeddable.matrixRestriction`: embeddability into a fixed
  class is hereditary [FWZ, remark after Definition 4.1.9].

## Implementation notes

* No skew-symmetrizability hypothesis is attached to the relation, to its symmetry, or to the
  two lemmas on mutation classes: mutation is an involution
  (`ClusterAlgebras.matrixMutation_matrixMutation`) for every matrix over a strictly ordered
  ring.
* The inverse of a bijective restriction map is built as a reindexing map
  (`ClusterAlgebras.ReindexingMap.symmOfBijective`), so that undoing a renumbering is again
  reindexing.
* A property of matrices is a predicate on `m × n` matrices over `R` for all `n ≤ m`, taking
  the proof of `n ≤ m` as an argument because mutation does.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 4][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {m n m' n' : ℕ}

namespace ReindexingMap

/-- There are finitely many reindexing maps between two shapes. -/
instance instFinite : Finite (ReindexingMap m' n' m n) :=
  Finite.of_injective _ DFunLike.coe_injective

/-- The **inverse** of a bijective restriction map from `(m, n)` to itself, as a reindexing
map. It keeps mutable indices mutable because the map it inverts sends frozen indices to
frozen ones. -/
noncomputable def symmOfBijective (π : ReindexingMap m n m n) (hr : π.IsRestriction)
    (hb : Function.Bijective π) : ReindexingMap m n m n where
  toFun := (Equiv.ofBijective π hb).symm
  injective := (Equiv.ofBijective π hb).symm.injective
  lt_of_lt p hp := by
    rw [← hr.val_lt_iff, ← Equiv.ofBijective_apply π hb, Equiv.apply_symm_apply]
    exact hp

/-- The map followed by its inverse is the identity. -/
@[simp]
theorem comp_symmOfBijective (π : ReindexingMap m n m n) (hr : π.IsRestriction)
    (hb : Function.Bijective π) : π.comp (π.symmOfBijective hr hb) = ReindexingMap.id m n :=
  ext fun p => (Equiv.ofBijective π hb).apply_symm_apply p

/-- The inverse of a bijective restriction map is a restriction map. -/
theorem isRestriction_symmOfBijective (π : ReindexingMap m n m n) (hr : π.IsRestriction)
    (hb : Function.Bijective π) : (π.symmOfBijective hr hb).IsRestriction := by
  intro p hp
  by_contra h
  have := (hr.val_lt_iff ((π.symmOfBijective hr hb) p)).mpr (not_le.mp h)
  have e : π ((π.symmOfBijective hr hb) p) = p := (Equiv.ofBijective π hb).apply_symm_apply p
  rw [e] at this
  omega

/-- The inverse of a bijective restriction map is bijective. -/
theorem bijective_symmOfBijective (π : ReindexingMap m n m n) (hr : π.IsRestriction)
    (hb : Function.Bijective π) : Function.Bijective (π.symmOfBijective hr hb) :=
  (Equiv.ofBijective π hb).symm.bijective

/-- The column map of `π` undoes that of its inverse. -/
theorem col_col_symmOfBijective (π : ReindexingMap m n m n) (hr : π.IsRestriction)
    (hb : Function.Bijective π) (h : n ≤ m) (q : Fin n) :
    π.col h ((π.symmOfBijective hr hb).col h q) = q := by
  change (π.comp (π.symmOfBijective hr hb)).col h q = q
  rw [comp_symmOfBijective, col_id, id]

end ReindexingMap

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Two `m × n` matrices are **mutation equivalent** when `B' = (μ_s B)^π` for a finite
sequence `s` of mutable directions and a bijective restriction map `π` from `(m, n)` to
itself, that is, a permutation of the indices mapping the mutable ones onto themselves.
For `m = n` this is `ClusterAlgebras.MutationEquiv`. -/
@[cluster_algebras "def_mut_equiv_ext"]
def ExtMutationEquiv (h : n ≤ m) (B B' : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ (s : List (Fin n)) (π : ReindexingMap m n m n), π.IsRestriction ∧ Function.Bijective π ∧
    B' = matrixReindex h (matrixMutationList h B s) π

omit [IsStrictOrderedRing R] in
/-- Every matrix is mutation equivalent to itself. -/
@[refl]
theorem ExtMutationEquiv.refl (h : n ≤ m) (B : Matrix (Fin m) (Fin n) R) :
    ExtMutationEquiv h B B :=
  ⟨[], ReindexingMap.id m n, ReindexingMap.isRestriction_id, Function.bijective_id, rfl⟩

omit [IsStrictOrderedRing R] in
/-- A matrix is mutation equivalent to any iterated mutation of it. -/
theorem extMutationEquiv_matrixMutationList (h : n ≤ m) (B : Matrix (Fin m) (Fin n) R)
    (s : List (Fin n)) : ExtMutationEquiv h B (matrixMutationList h B s) :=
  ⟨s, ReindexingMap.id m n, ReindexingMap.isRestriction_id, Function.bijective_id, rfl⟩

omit [IsStrictOrderedRing R] in
/-- **Mutation equivalence of extended matrices is transitive.** -/
@[cluster_algebras "lem_mut_equiv_ext_trans", trans]
theorem ExtMutationEquiv.trans {h : n ≤ m} {B B' B'' : Matrix (Fin m) (Fin n) R}
    (h₁ : ExtMutationEquiv h B B') (h₂ : ExtMutationEquiv h B' B'') :
    ExtMutationEquiv h B B'' := by
  obtain ⟨s, π, hπ, hπb, rfl⟩ := h₁
  obtain ⟨s', π', hπ', hπ'b, rfl⟩ := h₂
  refine ⟨s ++ s'.map (π.col h), π.comp π', hπ.comp hπ', hπb.comp hπ'b, ?_⟩
  rw [matrixMutationList_matrixReindex h h, matrixReindex_matrixReindex,
    matrixMutationList_append]

/-- **Mutation equivalence of extended matrices is symmetric.** -/
@[cluster_algebras "lem_mut_equiv_ext_symm", symm]
theorem ExtMutationEquiv.symm {h : n ≤ m} {B B' : Matrix (Fin m) (Fin n) R}
    (h₁ : ExtMutationEquiv h B B') : ExtMutationEquiv h B' B := by
  obtain ⟨s, π, hπ, hπb, rfl⟩ := h₁
  set σ := π.symmOfBijective hπ hπb
  refine ⟨s.reverse.map (σ.col h), σ, π.isRestriction_symmOfBijective hπ hπb,
    π.bijective_symmOfBijective hπ hπb, ?_⟩
  have hs : (s.reverse.map (σ.col h)).map (π.col h) = s.reverse := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id s.reverse]
    exact List.map_congr_left fun q _ => π.col_col_symmOfBijective hπ hπb h q
  rw [matrixMutationList_matrixReindex h h, hs, matrixMutationList_reverse_matrixMutationList,
    matrixReindex_matrixReindex, ReindexingMap.comp_symmOfBijective, matrixReindex_id]

/-- The **mutation class** `[B]` of an `m × n` matrix: the matrices `B` is mutation
equivalent to. -/
@[cluster_algebras "def_mutation_class"]
def mutationClass (h : n ≤ m) (B : Matrix (Fin m) (Fin n) R) : Set (Matrix (Fin m) (Fin n) R) :=
  {B' | ExtMutationEquiv h B B'}

omit [IsStrictOrderedRing R] in
/-- Membership in a mutation class. -/
@[simp]
theorem mem_mutationClass {h : n ≤ m} {B B' : Matrix (Fin m) (Fin n) R} :
    B' ∈ mutationClass h B ↔ ExtMutationEquiv h B B' :=
  Iff.rfl

omit [IsStrictOrderedRing R] in
/-- A matrix lies in its own mutation class. -/
theorem self_mem_mutationClass (h : n ≤ m) (B : Matrix (Fin m) (Fin n) R) :
    B ∈ mutationClass h B :=
  ExtMutationEquiv.refl h B

/-- An `m × n` matrix has **finite mutation type** when its mutation class is finite.
Matrices, unlike quivers, are not taken up to isomorphism here: the renumberings are already
inside the mutation class. -/
@[cluster_algebras "def_matrix_finite_mutation_type"]
def HasFiniteMatrixMutationType (h : n ≤ m) (B : Matrix (Fin m) (Fin n) R) : Prop :=
  (mutationClass h B).Finite

/-- A property `P` of matrices over `R` is **hereditary** when for every extended
skew-symmetrizable `m × n` matrix `B` with `P` and every `I ⊆ [0, m)`, the restriction
`B_I` has `P`. -/
@[cluster_algebras "def_hereditary"]
def IsHereditaryMatrixProperty
    (P : ∀ {m n : ℕ}, n ≤ m → Matrix (Fin m) (Fin n) R → Prop) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m) (B : Matrix (Fin m) (Fin n) R), ExtSkewSymmetrizable h B →
    P h B → ∀ I : Finset (Fin m), P (mutableCard_le_card n I) (matrixRestriction B I)

omit [IsStrictOrderedRing R] in
/-- **The mutation class of a reindexing lies in the reindexings of the mutation class**:
every matrix mutation equivalent to `Bʳ` is `D^{r ∘ π}` for some `D ∈ [B]` and some
reindexing map `π`. -/
theorem exists_of_extMutationEquiv_matrixReindex (h : n ≤ m) (h' : n' ≤ m')
    (B : Matrix (Fin m) (Fin n) R) (r : ReindexingMap m' n' m n)
    {C : Matrix (Fin m') (Fin n') R} (hC : ExtMutationEquiv h' (matrixReindex h' B r) C) :
    ∃ D ∈ mutationClass h B, ∃ π : ReindexingMap m' n' m' n',
      C = matrixReindex h' D (r.comp π) := by
  obtain ⟨s, π, -, -, rfl⟩ := hC
  exact ⟨_, extMutationEquiv_matrixMutationList h B (s.map (r.col h')), π,
    by rw [matrixMutationList_matrixReindex h h', matrixReindex_matrixReindex]⟩

omit [IsStrictOrderedRing R] in
/-- **Finite mutation type is hereditary** [FWZ, Proposition 4.1.4]. -/
@[cluster_algebras "prop_finite_mutation_type_hereditary"]
theorem isHereditaryMatrixProperty_hasFiniteMatrixMutationType :
    IsHereditaryMatrixProperty (R := R) fun h B => HasFiniteMatrixMutationType h B := by
  intro m n h B _ hB I
  set ι := enumerationMap n I
  have hle := mutableCard_le_card n I
  refine ((hB.prod (Set.finite_univ (α := ReindexingMap I.card (mutableCard n I)
    I.card (mutableCard n I)))).image fun x => matrixReindex hle x.1 (ι.comp x.2)).subset ?_
  intro C hC
  obtain ⟨D, hD, π, rfl⟩ := exists_of_extMutationEquiv_matrixReindex h hle B ι hC
  exact ⟨(D, π), ⟨hD, Set.mem_univ _⟩, rfl⟩

/-- **Restriction descends to mutation classes** [FWZ, Lemma 4.1.8]. For an `m × n` matrix `C`
and an `m' × n'` matrix `C'`, the following are equivalent: (i) some `B ∈ [C]` is obtained by
restriction from some `B' ∈ [C']`; (ii) every `B ∈ [C]` is obtained by restriction from some
`B' ∈ [C']`. -/
@[cluster_algebras "lem_restriction_classes"]
theorem exists_obtainedByRestriction_iff_forall (h : n ≤ m) (h' : n' ≤ m')
    (C : Matrix (Fin m) (Fin n) R) (C' : Matrix (Fin m') (Fin n') R) :
    (∃ B ∈ mutationClass h C, ∃ B' ∈ mutationClass h' C', ObtainedByRestriction h B B') ↔
      ∀ B ∈ mutationClass h C, ∃ B' ∈ mutationClass h' C', ObtainedByRestriction h B B' := by
  refine ⟨?_, fun hall => ⟨C, self_mem_mutationClass h C, hall C (self_mem_mutationClass h C)⟩⟩
  rintro ⟨B₀, hB₀, B₀', hB₀', r, hr, rfl⟩ B hB
  obtain ⟨s, π, hπ, -, rfl⟩ := hB₀.symm.trans hB
  refine ⟨matrixMutationList h' B₀' (s.map (r.col h)),
    hB₀'.trans (extMutationEquiv_matrixMutationList h' B₀' _), r.comp π, hr.comp hπ, ?_⟩
  rw [matrixMutationList_matrixReindex h' h, matrixReindex_matrixReindex]

/-- The class `[C]` of an `m × n` matrix is **embeddable** into the class `[C']` of an
`m' × n'` matrix, written `[C] ≤ [C']`, when some `B ∈ [C]` is obtained by restriction from
some `B' ∈ [C']`. -/
@[cluster_algebras "def_embeddable"]
def MutationClassEmbeddable (h : n ≤ m) (C : Matrix (Fin m) (Fin n) R) (h' : n' ≤ m')
    (C' : Matrix (Fin m') (Fin n') R) : Prop :=
  ∃ B ∈ mutationClass h C, ∃ B' ∈ mutationClass h' C', ObtainedByRestriction h B B'

/-- **Embeddability into a fixed class is hereditary**: if `[B] ≤ [C']` then
`[B_I] ≤ [C']` for every `I ⊆ [0, m)` [FWZ, remark after Definition 4.1.9]. -/
@[cluster_algebras "lem_embeddable_hereditary"]
theorem MutationClassEmbeddable.matrixRestriction {h : n ≤ m} {B : Matrix (Fin m) (Fin n) R}
    {h' : n' ≤ m'} {C' : Matrix (Fin m') (Fin n') R}
    (hB : MutationClassEmbeddable h B h' C') (I : Finset (Fin m)) :
    MutationClassEmbeddable (mutableCard_le_card n I) (ClusterAlgebras.matrixRestriction B I)
      h' C' := by
  obtain ⟨B', hB', r, hr, hrB⟩ :=
    (exists_obtainedByRestriction_iff_forall h h' B C').mp hB B (self_mem_mutationClass h B)
  refine ⟨_, self_mem_mutationClass _ _, B', hB', r.comp (enumerationMap n I),
    hr.comp (isRestriction_enumerationMap n I), ?_⟩
  rw [matrixRestriction_eq_matrixReindex, hrB, matrixReindex_matrixReindex]

end ClusterAlgebras

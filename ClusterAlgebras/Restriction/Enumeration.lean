/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Restriction.Reindexing

/-!
# Restricting a matrix to a set of indices

For `I ⊆ [0, m)` the *enumeration* `ι_I` lists the mutable elements of `I` (those below `n`)
in increasing order, followed by its frozen elements in increasing order
(`ClusterAlgebras.restrictionEnumeration`). It is a restriction map from
`(|I|, n_I)` to `(m, n)` with image `I` (`ClusterAlgebras.enumerationMap`), where `n_I` is
the number of mutable elements of `I` (`ClusterAlgebras.mutableCard`). The *restriction*
`B_I` of a matrix is its reindexing along `ι_I` (`ClusterAlgebras.matrixRestriction`), and a
matrix is *obtained by restriction* from another when it is a reindexing of it along some
restriction map (`ClusterAlgebras.ObtainedByRestriction`).

## Implementation notes

* Fomin, Williams and Zelevinsky label the rows and columns of `B_I` by `I` itself. Here they
  are renumbered by `ι_I`, so that `B_I` is again a matrix of the shape `Matrix (Fin m') (Fin n')`.

* The enumeration is `Fin.append` of the two increasing enumerations `Finset.orderEmbOfFin`, of
  the mutable and of the frozen elements of `I`, precomposed with the cast along
  `n_I + |I \ [0, n)| = |I|`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

variable {m n : ℕ}

/-- The number `n_I = |I ∩ [0, n)|` of mutable indices in `I`. -/
def mutableCard (n : ℕ) (I : Finset (Fin m)) : ℕ :=
  (I.filter fun i : Fin m => (i : ℕ) < n).card

/-- There are no more mutable indices in `I` than indices. -/
theorem mutableCard_le_card (n : ℕ) (I : Finset (Fin m)) : mutableCard n I ≤ I.card :=
  Finset.card_filter_le _ _

/-- The two halves of `I` add up to `I`. -/
theorem mutableCard_add_card_filter_not (n : ℕ) (I : Finset (Fin m)) :
    mutableCard n I + (I.filter fun i : Fin m => ¬(i : ℕ) < n).card = I.card :=
  Finset.card_filter_add_card_filter_not _

/-- The **enumeration** `ι_I` of `I ⊆ [0, m)`: its values at `0, …, n_I - 1` are the
elements of `I` below `n` in increasing order, and its values at `n_I, …, |I| - 1` are the
remaining elements of `I` in increasing order. -/
@[cluster_algebras "def_restriction_enumeration"]
def restrictionEnumeration (n : ℕ) (I : Finset (Fin m)) : Fin I.card → Fin m :=
  Fin.append ((I.filter fun i : Fin m => (i : ℕ) < n).orderEmbOfFin rfl)
      ((I.filter fun i : Fin m => ¬(i : ℕ) < n).orderEmbOfFin rfl) ∘
    Fin.cast (mutableCard_add_card_filter_not n I).symm

/-- On the first `n_I` positions the enumeration lists the mutable elements of `I`. -/
theorem restrictionEnumeration_castAdd (n : ℕ) (I : Finset (Fin m))
    (i : Fin (mutableCard n I)) :
    restrictionEnumeration n I
        (Fin.cast (mutableCard_add_card_filter_not n I)
          (Fin.castAdd (I.filter fun i : Fin m => ¬(i : ℕ) < n).card i)) =
      (I.filter fun i : Fin m => (i : ℕ) < n).orderEmbOfFin rfl i := by
  simp only [restrictionEnumeration, mutableCard, Function.comp_apply, Fin.cast_cast,
    Fin.cast_eq_self, Fin.append_left]

/-- On the remaining positions the enumeration lists the frozen elements of `I`. -/
theorem restrictionEnumeration_natAdd (n : ℕ) (I : Finset (Fin m))
    (j : Fin (I.filter fun i : Fin m => ¬(i : ℕ) < n).card) :
    restrictionEnumeration n I
        (Fin.cast (mutableCard_add_card_filter_not n I) (Fin.natAdd (mutableCard n I) j)) =
      (I.filter fun i : Fin m => ¬(i : ℕ) < n).orderEmbOfFin rfl j := by
  simp only [restrictionEnumeration, mutableCard, Function.comp_apply, Fin.cast_cast,
    Fin.cast_eq_self, Fin.append_right]

/-- Every position is a cast of a position in one of the two halves. -/
private theorem cases_cast (n : ℕ) (I : Finset (Fin m)) (p : Fin I.card) :
    (∃ i : Fin (mutableCard n I),
        p = Fin.cast (mutableCard_add_card_filter_not n I)
          (Fin.castAdd (I.filter fun i : Fin m => ¬(i : ℕ) < n).card i) ∧
          (p : ℕ) < mutableCard n I) ∨
      ∃ j : Fin (I.filter fun i : Fin m => ¬(i : ℕ) < n).card,
        p = Fin.cast (mutableCard_add_card_filter_not n I) (Fin.natAdd (mutableCard n I) j) ∧
          mutableCard n I ≤ (p : ℕ) := by
  have hp : p = Fin.cast (mutableCard_add_card_filter_not n I)
      (Fin.cast (mutableCard_add_card_filter_not n I).symm p) := by simp
  generalize Fin.cast (mutableCard_add_card_filter_not n I).symm p = q at hp
  induction q using Fin.addCases with
  | left i => exact Or.inl ⟨i, hp, by simp [hp]⟩
  | right j => exact Or.inr ⟨j, hp, by simp [hp]⟩

/-- The enumeration takes a value below `n` exactly at the first `n_I` positions. -/
theorem val_restrictionEnumeration_lt_iff (n : ℕ) (I : Finset (Fin m)) (p : Fin I.card) :
    (restrictionEnumeration n I p : ℕ) < n ↔ (p : ℕ) < mutableCard n I := by
  rcases cases_cast n I p with ⟨i, rfl, hi⟩ | ⟨j, rfl, hj⟩
  · rw [restrictionEnumeration_castAdd]
    have := Finset.mem_filter.mp ((I.filter fun i : Fin m => (i : ℕ) < n).orderEmbOfFin_mem rfl i)
    exact iff_of_true this.2 hi
  · rw [restrictionEnumeration_natAdd]
    have := Finset.mem_filter.mp ((I.filter fun i : Fin m => ¬(i : ℕ) < n).orderEmbOfFin_mem rfl j)
    exact iff_of_false this.2 (not_lt.mpr hj)

/-- Every value of the enumeration lies in `I`. -/
theorem restrictionEnumeration_mem (n : ℕ) (I : Finset (Fin m)) (p : Fin I.card) :
    restrictionEnumeration n I p ∈ I := by
  rcases cases_cast n I p with ⟨i, rfl, -⟩ | ⟨j, rfl, -⟩
  · rw [restrictionEnumeration_castAdd]
    exact (Finset.mem_filter.mp ((I.filter _).orderEmbOfFin_mem rfl i)).1
  · rw [restrictionEnumeration_natAdd]
    exact (Finset.mem_filter.mp ((I.filter _).orderEmbOfFin_mem rfl j)).1

/-- The enumeration is injective: it lists each element of `I` once. -/
theorem restrictionEnumeration_injective (n : ℕ) (I : Finset (Fin m)) :
    Function.Injective (restrictionEnumeration n I) := by
  intro p p' h
  have hlt := (val_restrictionEnumeration_lt_iff n I p).symm.trans
    (h ▸ val_restrictionEnumeration_lt_iff n I p')
  rcases cases_cast n I p with ⟨i, rfl, hi⟩ | ⟨j, rfl, hj⟩ <;>
    rcases cases_cast n I p' with ⟨i', rfl, hi'⟩ | ⟨j', rfl, hj'⟩
  · rw [restrictionEnumeration_castAdd, restrictionEnumeration_castAdd] at h
    rw [((I.filter fun i : Fin m => (i : ℕ) < n).orderEmbOfFin rfl).injective h]
  · exact absurd (hlt.mp hi) (not_lt.mpr hj')
  · exact absurd (hlt.mpr hi') (not_lt.mpr hj)
  · rw [restrictionEnumeration_natAdd, restrictionEnumeration_natAdd] at h
    rw [((I.filter fun i : Fin m => ¬(i : ℕ) < n).orderEmbOfFin rfl).injective h]

/-- The image of the enumeration is `I`. -/
@[simp]
theorem range_restrictionEnumeration (n : ℕ) (I : Finset (Fin m)) :
    Set.range (restrictionEnumeration n I) = I := by
  refine Set.Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨p, rfl⟩
    exact restrictionEnumeration_mem n I p
  · by_cases hxn : (x : ℕ) < n
    · have hx' : x ∈ I.filter fun i : Fin m => (i : ℕ) < n := Finset.mem_filter.mpr ⟨hx, hxn⟩
      rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin _ rfl] at hx'
      obtain ⟨i, rfl⟩ := hx'
      exact ⟨_, restrictionEnumeration_castAdd n I i⟩
    · have hx' : x ∈ I.filter fun i : Fin m => ¬(i : ℕ) < n := Finset.mem_filter.mpr ⟨hx, hxn⟩
      rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin _ rfl] at hx'
      obtain ⟨j, rfl⟩ := hx'
      exact ⟨_, restrictionEnumeration_natAdd n I j⟩

/-- The enumeration `ι_I` as a reindexing map from `(|I|, n_I)` to `(m, n)`. -/
@[cluster_algebras "lem_restriction_enumeration_map"]
def enumerationMap (n : ℕ) (I : Finset (Fin m)) : ReindexingMap I.card (mutableCard n I) m n where
  toFun := restrictionEnumeration n I
  injective := restrictionEnumeration_injective n I
  lt_of_lt p := (val_restrictionEnumeration_lt_iff n I p).mpr

/-- The reindexing map `enumerationMap n I` is the enumeration. -/
@[simp]
theorem coe_enumerationMap (n : ℕ) (I : Finset (Fin m)) :
    ⇑(enumerationMap n I) = restrictionEnumeration n I :=
  rfl

/-- **The enumeration of a subset is a restriction map**, from `(|I|, n_I)` to `(m, n)`. -/
@[cluster_algebras "lem_restriction_enumeration_map"]
theorem isRestriction_enumerationMap (n : ℕ) (I : Finset (Fin m)) :
    (enumerationMap n I).IsRestriction := fun p hp =>
  not_lt.mp fun h => absurd ((val_restrictionEnumeration_lt_iff n I p).mp h) (not_lt.mpr hp)

/-- **The image of the enumeration of `I` is `I`.** -/
@[cluster_algebras "lem_restriction_enumeration_map"]
theorem range_enumerationMap (n : ℕ) (I : Finset (Fin m)) :
    Set.range (enumerationMap n I) = I :=
  range_restrictionEnumeration n I

section Restriction

variable {α : Type*}

/-- The **restriction** `B_I` of `B` to `I ⊆ [0, m)`: the `|I| × n_I` matrix with entries
`(B_I)_{pq} = b_{ι_I(p) ι_I(q)}`, the reindexing of `B` along the enumeration of `I`. -/
@[cluster_algebras "def_matrix_restriction"]
def matrixRestriction (B : Matrix (Fin m) (Fin n) α) (I : Finset (Fin m)) :
    Matrix (Fin I.card) (Fin (mutableCard n I)) α :=
  matrixReindex (mutableCard_le_card n I) B (enumerationMap n I)

/-- The entries of a restricted matrix. -/
theorem matrixRestriction_apply (B : Matrix (Fin m) (Fin n) α) (I : Finset (Fin m))
    (p : Fin I.card) (q : Fin (mutableCard n I)) :
    matrixRestriction B I p q =
      B (restrictionEnumeration n I p) ((enumerationMap n I).col (mutableCard_le_card n I) q) :=
  rfl

/-- The restriction to `I` is the reindexing along the enumeration of `I`, `B_I = B^{ι_I}`. -/
theorem matrixRestriction_eq_matrixReindex (B : Matrix (Fin m) (Fin n) α) (I : Finset (Fin m)) :
    matrixRestriction B I = matrixReindex (mutableCard_le_card n I) B (enumerationMap n I) :=
  rfl

variable {m' n' : ℕ}

/-- The `m' × n'` matrix `B'` is **obtained from `B` by restriction** when `B' = Bʳ` for some
restriction map `r` from `(m', n')` to `(m, n)`. -/
@[cluster_algebras "def_obtained_by_restriction"]
def ObtainedByRestriction (h' : n' ≤ m') (B' : Matrix (Fin m') (Fin n') α)
    (B : Matrix (Fin m) (Fin n) α) : Prop :=
  ∃ r : ReindexingMap m' n' m n, r.IsRestriction ∧ B' = matrixReindex h' B r

/-- A restriction of `B` to a subset is obtained from `B` by restriction. -/
theorem obtainedByRestriction_matrixRestriction (B : Matrix (Fin m) (Fin n) α)
    (I : Finset (Fin m)) :
    ObtainedByRestriction (mutableCard_le_card n I) (matrixRestriction B I) B :=
  ⟨enumerationMap n I, isRestriction_enumerationMap n I, rfl⟩

end Restriction

end ClusterAlgebras

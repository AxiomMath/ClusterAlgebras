/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Attr
public import ClusterAlgebras.External

/-!
# Labeled seeds and seed mutation

A labeled seed pairs a *free generating tuple* of a field -- algebraically independent
elements generating it as a field over the ground field -- with an extended skew-symmetrizable
integer matrix.

## Main definitions

* `IsFreeGeneratingTuple`: algebraically independent elements generating a field.
* `SeedData`: an extended cluster together with an extended exchange matrix.
* `IsLabeledSeed`: the condition that a `SeedData` is a labeled seed.
* `seedMutation`: seed mutation in a given direction.
* `seedMutationSeq`: mutation along a sequence of directions.

## Implementation notes

Seed mutation is defined on the bare data `SeedData` of a seed, for any tuple and matrix;
`IsLabeledSeed` is a separate condition, which mutation preserves. [FWZ] takes the ground field
of characteristic zero throughout; the definitions here do not assume it, and the results that
need it carry it as a hypothesis.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 3.
-/

@[expose] public section

namespace ClusterAlgebras

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ}

/-- `x` is a **free generating tuple** of `F` over `K` when its entries are algebraically
independent over `K` and generate `F` as a field over `K`, that is, `F = K(x₁, …, xₘ)`. -/
@[cluster_algebras "def_free_generating_tuple"]
def IsFreeGeneratingTuple (x : Fin m → F) : Prop :=
  AlgebraicIndependent K x ∧ IntermediateField.adjoin K (Set.range x) = ⊤

variable {α : Type*} {n : ℕ}

/-- The **principal part** of an `m × n` matrix `B`, for `n ≤ m`: the `n × n` matrix formed
by its first `n` rows. It is the submatrix that `ExtSkewSymmetrizable` asks to be
skew-symmetrizable. -/
@[cluster_algebras "def_principal_part"]
def principalPart (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) α) : Matrix (Fin n) (Fin n) α :=
  B.submatrix (Fin.castLE hmn) id

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
/-- **Mutation commutes with taking the principal part.** Mutating `B` in direction `k` and
then keeping its first `n` rows gives the same `n × n` matrix as mutating its principal
part in direction `k`. -/
@[cluster_algebras "lem_principal_part_mutation"]
theorem principalPart_matrixMutation (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n) :
    principalPart hmn (matrixMutation hmn B k) = matrixMutation le_rfl (principalPart hmn B) k := by
  ext i j
  simp [principalPart, matrixMutation]

/-- **An extended skew-symmetrizable matrix is sign-antisymmetric.** -/
@[cluster_algebras "lem_ext_skew_symmetrizable_sign_antisymmetric"]
theorem ExtSkewSymmetrizable.signAntisymmetric (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) R}
    (hB : ExtSkewSymmetrizable hmn B) : SignAntisymmetric hmn B := by
  obtain ⟨d, hd⟩ := hB
  refine ⟨fun i => ?_, fun i j => hd.pos_iff_neg i j⟩
  have h := hd.2 i i
  simp only [Matrix.submatrix_apply, id] at h
  have h0 : (d i : R) * B (Fin.castLE hmn i) i = 0 := by linarith
  exact (mul_eq_zero.1 h0).resolve_left (hd.cast_pos (R := R) i).ne'

/-- **Sign-antisymmetry transposes vanishing entries.** -/
theorem SignAntisymmetric.eq_zero_of_eq_zero (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) R}
    (hsign : SignAntisymmetric hmn B) {j k : Fin n} (hb : B (Fin.castLE hmn j) k = 0) :
    B (Fin.castLE hmn k) j = 0 := by
  rcases lt_trichotomy (B (Fin.castLE hmn k) j) 0 with h | h | h
  · linarith [(hsign.2 j k).2 h]
  · exact h
  · linarith [(hsign.2 k j).1 h]

/-- The data of a labeled seed with none of its conditions: an *extended cluster*, an
`m`-tuple of elements of `F`, and an *extended exchange matrix*, an `m × n` integer matrix.
Seed mutation acts on this data, and `IsLabeledSeed` says when it is a labeled seed. -/
@[ext, cluster_algebras "def_labeled_seed"]
structure SeedData (F : Type*) (m n : ℕ) where
  /-- The extended cluster `x̃ = (x₁, …, xₘ)`. -/
  extCluster : Fin m → F
  /-- The extended exchange matrix `B̃`. -/
  extExchangeMatrix : Matrix (Fin m) (Fin n) ℤ

/-- `S` is a **labeled seed** in `F` over `K` when its extended cluster is a free generating
tuple of `F` over `K` and its extended exchange matrix is extended skew-symmetrizable. -/
@[cluster_algebras "def_labeled_seed"]
def IsLabeledSeed (hmn : n ≤ m) (S : SeedData F m n) : Prop :=
  IsFreeGeneratingTuple K S.extCluster ∧ ExtSkewSymmetrizable hmn S.extExchangeMatrix

variable {K}

/-- The **cluster** of `S`: the first `n` entries of its extended cluster. -/
@[cluster_algebras "def_cluster"]
def cluster (hmn : n ≤ m) (S : SeedData F m n) : Fin n → F :=
  fun i => S.extCluster (Fin.castLE hmn i)

/-- The **cluster variables** of `S`: the entries of its cluster. -/
@[cluster_algebras "def_cluster"]
def clusterVariables (hmn : n ≤ m) (S : SeedData F m n) : Set F :=
  Set.range (cluster hmn S)

/-- The **frozen variables** of `S`: the entries of its extended cluster in the positions
after the first `n`. -/
@[cluster_algebras "def_frozen_variables"]
def frozenVariables (S : SeedData F m n) : Set F :=
  S.extCluster '' {i | n ≤ (i : ℕ)}

/-- The **positive exchange monomial** `M⁺ₖ(x̃, B̃)`: the product of `xᵢ ^ bᵢₖ` over the rows
`i` with `bᵢₖ > 0`. -/
@[cluster_algebras "def_exchange_monomial_pos"]
def exchangeMonomialPos (x : Fin m → F) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) : F :=
  ∏ i ∈ Finset.univ.filter (fun i => 0 < B i k), x i ^ B i k

/-- The **negative exchange monomial** `M⁻ₖ(x̃, B̃)`: the product of `xᵢ ^ (-bᵢₖ)` over the
rows `i` with `bᵢₖ < 0`. -/
@[cluster_algebras "def_exchange_monomial_neg"]
def exchangeMonomialNeg (x : Fin m → F) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) : F :=
  ∏ i ∈ Finset.univ.filter (fun i => B i k < 0), x i ^ (-B i k)

/-- **Seed mutation** in direction `k`: the entry of the extended cluster in position `k` is
replaced by `(M⁺ₖ + M⁻ₖ) / xₖ`, every other entry is kept, and the extended exchange matrix
is mutated in direction `k`. When `xₖ ≠ 0` the new entry `x'ₖ` satisfies the *exchange
relation* `xₖ x'ₖ = M⁺ₖ + M⁻ₖ`; when `xₖ = 0` it is `0`. -/
@[cluster_algebras "def_seed_mutation"]
def seedMutation (hmn : n ≤ m) (S : SeedData F m n) (k : Fin n) : SeedData F m n where
  extCluster := Function.update S.extCluster (Fin.castLE hmn k)
    ((exchangeMonomialPos S.extCluster S.extExchangeMatrix k +
        exchangeMonomialNeg S.extCluster S.extExchangeMatrix k) /
      S.extCluster (Fin.castLE hmn k))
  extExchangeMatrix := matrixMutation hmn S.extExchangeMatrix k

section ExchangeMonomial

variable {x x' : Fin m → F} {B B' : Matrix (Fin m) (Fin n) ℤ} {k : Fin n}

/-- The positive exchange monomial only reads column `k` of the matrix, and the entries of
the tuple in the rows where that column is nonzero. -/
theorem exchangeMonomialPos_congr (hx : ∀ i, B i k ≠ 0 → x' i = x i)
    (hB : ∀ i, B' i k = B i k) :
    exchangeMonomialPos x' B' k = exchangeMonomialPos x B k := by
  simp only [exchangeMonomialPos, hB]
  exact Finset.prod_congr rfl fun i hi => by rw [hx i (Finset.mem_filter.1 hi).2.ne']

/-- The negative exchange monomial only reads column `k` of the matrix, and the entries of
the tuple in the rows where that column is nonzero. -/
theorem exchangeMonomialNeg_congr (hx : ∀ i, B i k ≠ 0 → x' i = x i)
    (hB : ∀ i, B' i k = B i k) :
    exchangeMonomialNeg x' B' k = exchangeMonomialNeg x B k := by
  simp only [exchangeMonomialNeg, hB]
  exact Finset.prod_congr rfl fun i hi => by rw [hx i (Finset.mem_filter.1 hi).2.ne]

/-- Negating the matrix turns the positive exchange monomial into the negative one. -/
@[simp]
theorem exchangeMonomialPos_neg : exchangeMonomialPos x (-B) k = exchangeMonomialNeg x B k := by
  simp only [exchangeMonomialPos, exchangeMonomialNeg, Matrix.neg_apply, neg_pos]

/-- Negating the matrix turns the negative exchange monomial into the positive one. -/
@[simp]
theorem exchangeMonomialNeg_neg : exchangeMonomialNeg x (-B) k = exchangeMonomialPos x B k := by
  simp only [exchangeMonomialPos, exchangeMonomialNeg, Matrix.neg_apply, neg_lt_zero, neg_neg]

/-- The positive exchange monomial as a product of natural powers over all rows. -/
theorem exchangeMonomialPos_eq_prod :
    exchangeMonomialPos x B k = ∏ i, x i ^ (B i k).toNat := by
  rw [exchangeMonomialPos, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [← zpow_natCast, Int.toNat_of_nonneg h.le]
  · rw [Int.toNat_eq_zero.2 (not_lt.1 h), pow_zero]

/-- The negative exchange monomial as a product of natural powers over all rows. -/
theorem exchangeMonomialNeg_eq_prod :
    exchangeMonomialNeg x B k = ∏ i, x i ^ (-B i k).toNat := by
  rw [exchangeMonomialNeg, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  · rw [Int.toNat_eq_zero.2 (by omega), pow_zero]

variable (K) in
/-- The exchange binomial lies in every subalgebra containing the entries of the tuple in
the rows where column `k` is nonzero. -/
theorem exchangeMonomialPos_add_exchangeMonomialNeg_mem (A : Subalgebra K F)
    (hx : ∀ i, B i k ≠ 0 → x i ∈ A) :
    exchangeMonomialPos x B k + exchangeMonomialNeg x B k ∈ A := by
  have key : ∀ e : Fin m → ℕ, (∀ i, e i ≠ 0 → B i k ≠ 0) → ∏ i, x i ^ e i ∈ A :=
    fun e he => Subalgebra.prod_mem _ fun i _ => by
      by_cases h0 : e i = 0
      · simp [h0]
      · exact pow_mem (hx i (he i h0)) _
  rw [exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod]
  exact add_mem (key _ fun i h hb => h (by simp [hb])) (key _ fun i h hb => h (by simp [hb]))

end ExchangeMonomial

/-- The entry of a labeled seed's extended exchange matrix in row `k` and column `k`
vanishes. -/
theorem IsLabeledSeed.extExchangeMatrix_castLE_self (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (k : Fin n) : S.extExchangeMatrix (Fin.castLE hmn k) k = 0 :=
  (hS.2.signAntisymmetric hmn).1 k

/-- Column `l` of the mutation of `B` in direction `k ≠ l` is column `l` of `B`, when the
entry of `B` in row `k` and column `l` vanishes. -/
theorem matrixMutation_apply_of_castLE_eq_zero (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) R}
    {k l : Fin n} (hkl : l ≠ k) (h : B (Fin.castLE hmn k) l = 0) (i : Fin m) :
    matrixMutation hmn B k i l = B i l := by
  by_cases hi : i = Fin.castLE hmn k
  · rw [hi, matrixMutation_apply_row, h, neg_zero]
  · exact matrixMutation_apply_of_eq_zero hmn B k hi hkl (Or.inr h)

/-- **The exchange binomial of a seed is nonzero.** The exchange binomial `M⁺ₖ + M⁻ₖ` of a
labeled seed is a nonzero element of `F`. This is where the characteristic of `K` matters:
when column `k` vanishes the binomial is `1 + 1`. -/
@[cluster_algebras "lem_exchange_binomial_nonzero"]
theorem IsLabeledSeed.exchangeMonomialPos_add_exchangeMonomialNeg_ne_zero [CharZero K]
    (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) (k : Fin n) :
    exchangeMonomialPos S.extCluster S.extExchangeMatrix k +
      exchangeMonomialNeg S.extCluster S.extExchangeMatrix k ≠ 0 := by
  classical
  set B := S.extExchangeMatrix
  set x := S.extCluster
  let ep : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (B i k).toNat
  let en : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (-B i k).toNat
  have hmono : ∀ e : Fin m →₀ ℕ,
      MvPolynomial.aeval x (MvPolynomial.monomial e (1 : K)) = ∏ i, x i ^ e i := fun e => by
    rw [MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ fun i => pow_zero _]
  have hp : MvPolynomial.monomial ep (1 : K) + MvPolynomial.monomial en 1 ≠ 0 := by
    by_cases he : ep = en
    · rw [he, ← map_add, one_add_one_eq_two, Ne, MvPolynomial.monomial_eq_zero]
      exact two_ne_zero
    · intro h
      simpa [MvPolynomial.coeff_monomial, Ne.symm he] using congrArg (MvPolynomial.coeff ep) h
  intro h
  apply hp
  refine (injective_iff_map_eq_zero _).1 hS.1.1 _ ?_
  rw [map_add, hmono, hmono]
  simpa [exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod, ep, en] using h

/-- **The exchange relation preserves algebraic independence.** Replacing the entry of an
algebraically independent tuple at `c` by `P / x c` keeps it algebraically independent, when
`P` is a nonzero element of every subalgebra containing the other entries. -/
theorem algebraicIndependent_update_div {x : Fin m → F} {c : Fin m} {P : F}
    (hind : AlgebraicIndependent K x) (hP : P ≠ 0)
    (hPmem : ∀ A : Subalgebra K F, (∀ i, i ≠ c → x i ∈ A) → P ∈ A) :
    AlgebraicIndependent K (Function.update x c (P / x c)) := by
  classical
  have hxc : x c ≠ 0 := hind.ne_zero c
  set y := P / x c
  have hon : AlgebraicIndepOn K (Function.update x c y) {c}ᶜ := by
    have hfun : (fun i : ↥({c}ᶜ : Set (Fin m)) => Function.update x c y i) =
        fun i : ↥({c}ᶜ : Set (Fin m)) => x i :=
      funext fun i => Function.update_of_ne i.2 _ _
    change AlgebraicIndependent K _
    rw [hfun]
    exact (AlgebraicIndepOn.univ.2 hind).mono (Set.subset_univ _)
  have himg : Function.update x c y '' {c}ᶜ = x '' {c}ᶜ :=
    Set.image_congr fun i hi => Function.update_of_ne hi _ _
  have htr : Transcendental (Algebra.adjoin K (Function.update x c y '' {c}ᶜ))
      (Function.update x c y c) := by
    rw [himg, Function.update_self]
    intro halg
    set A := Algebra.adjoin K (x '' {c}ᶜ)
    have hPA : P ∈ A := hPmem A fun i hi => Algebra.subset_adjoin ⟨i, hi, rfl⟩
    apply hind.transcendental_adjoin (s := {c}ᶜ) (i := c) (by simp)
    have heq : (⟨P, hPA⟩ : A) • y⁻¹ = x c := by
      change P * y⁻¹ = x c
      simp only [y]
      field_simp
    exact heq ▸ (IsAlgebraic.inv halg).smul (⟨P, hPA⟩ : A)
  have hins := hon.insert htr
  rw [Set.insert_eq, Set.union_compl_self] at hins
  exact AlgebraicIndepOn.univ.1 hins

/-- **The exchange relation preserves generation.** Replacing the entry of a field-generating
tuple at `c` by `P / x c` keeps it generating, when `P` is a nonzero element of every
subalgebra containing the other entries. -/
theorem adjoin_update_div_eq_top {x : Fin m → F} {c : Fin m} {P : F} (hxc : x c ≠ 0)
    (hP : P ≠ 0) (htop : IntermediateField.adjoin K (Set.range x) = ⊤)
    (hPmem : ∀ A : Subalgebra K F, (∀ i, i ≠ c → x i ∈ A) → P ∈ A) :
    IntermediateField.adjoin K (Set.range (Function.update x c (P / x c))) = ⊤ := by
  classical
  set y := P / x c
  set L := IntermediateField.adjoin K (Set.range (Function.update x c y))
  have hmem : ∀ i, Function.update x c y i ∈ L := fun i =>
    IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  have hoff : ∀ i, i ≠ c → x i ∈ L := fun i hi => by
    simpa [Function.update_of_ne hi] using hmem i
  rw [eq_top_iff, ← htop, IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = c
  · have hyL : y ∈ L := by simpa using hmem c
    have hxP : x c = P / y := by
      simp only [y]
      field_simp
    rw [hi, hxP]
    exact div_mem (hPmem L.toSubalgebra hoff) hyL
  · exact hoff i hi

/-- **Seed mutation yields a labeled seed.** -/
@[cluster_algebras "lem_seed_mutation_is_seed"]
theorem IsLabeledSeed.seedMutation [CharZero K] (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (k : Fin n) :
    IsLabeledSeed K hmn (ClusterAlgebras.seedMutation hmn S k) := by
  classical
  have hP := hS.exchangeMonomialPos_add_exchangeMonomialNeg_ne_zero hmn k
  have hdiag := hS.extExchangeMatrix_castLE_self hmn k
  obtain ⟨⟨hind, htop⟩, hB⟩ := hS
  set x := S.extCluster
  set B := S.extExchangeMatrix
  set c := Fin.castLE hmn k
  have hPmem : ∀ A : Subalgebra K F, (∀ i, i ≠ c → x i ∈ A) →
      exchangeMonomialPos x B k + exchangeMonomialNeg x B k ∈ A := fun A hA =>
    exchangeMonomialPos_add_exchangeMonomialNeg_mem K A fun i hi =>
      hA i fun hic => hi (by rwa [hic])
  exact ⟨⟨algebraicIndependent_update_div hind hP hPmem,
    adjoin_update_div_eq_top (hind.ne_zero c) hP htop hPmem⟩, hB.matrixMutation hmn k⟩

/-- **Seed mutation is an involution.** Mutating a labeled seed twice in the same direction
returns it. -/
@[cluster_algebras "lem_seed_mutation_involution"]
theorem seedMutation_seedMutation [CharZero K] (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (k : Fin n) :
    seedMutation hmn (seedMutation hmn S k) k = S := by
  classical
  have hP := hS.exchangeMonomialPos_add_exchangeMonomialNeg_ne_zero hmn k
  have hdiag := hS.extExchangeMatrix_castLE_self hmn k
  have hxc : S.extCluster (Fin.castLE hmn k) ≠ 0 := hS.1.1.ne_zero _
  obtain ⟨x, B⟩ := S
  dsimp only at hP hdiag hxc
  have hx : ∀ i, (-B) i k ≠ 0 → Function.update x (Fin.castLE hmn k)
      ((exchangeMonomialPos x B k + exchangeMonomialNeg x B k) / x (Fin.castLE hmn k)) i =
        x i := fun i hi =>
    Function.update_of_ne (fun hic => hi (by rw [hic, Matrix.neg_apply, hdiag, neg_zero])) _ _
  have hcol : ∀ i, matrixMutation hmn B k i k = (-B) i k := matrixMutation_apply_col hmn B k
  refine SeedData.ext ?_ (matrixMutation_matrixMutation hmn B k)
  simp only [seedMutation]
  rw [Function.update_idem, Function.update_self, exchangeMonomialPos_congr hx hcol,
    exchangeMonomialNeg_congr hx hcol, exchangeMonomialPos_neg, exchangeMonomialNeg_neg,
    Function.update_eq_self_iff, add_comm]
  field_simp

/-- **Mutation along a sequence** `s = [k₁, …, k_d]`: seed mutation in direction `k₁`, then
`k₂`, and so on up to `k_d`; the empty sequence changes nothing. The length `d` of `s` is
`s.length`. -/
@[cluster_algebras "def_mutation_sequence"]
def seedMutationSeq (hmn : n ≤ m) (S : SeedData F m n) (s : List (Fin n)) : SeedData F m n :=
  s.foldl (seedMutation hmn) S

/-- Mutation along the empty sequence changes nothing. -/
@[simp]
theorem seedMutationSeq_nil (hmn : n ≤ m) (S : SeedData F m n) :
    seedMutationSeq hmn S [] = S := rfl

/-- Mutation along `k :: s` is mutation in direction `k`, then along `s`. -/
@[simp]
theorem seedMutationSeq_cons (hmn : n ≤ m) (S : SeedData F m n) (k : Fin n)
    (s : List (Fin n)) :
    seedMutationSeq hmn S (k :: s) = seedMutationSeq hmn (seedMutation hmn S k) s := rfl

/-- Mutation along `s ++ s'` is mutation along `s`, then along `s'`. -/
@[simp]
theorem seedMutationSeq_append (hmn : n ≤ m) (S : SeedData F m n) (s s' : List (Fin n)) :
    seedMutationSeq hmn S (s ++ s') = seedMutationSeq hmn (seedMutationSeq hmn S s) s' :=
  List.foldl_append

/-- **Mutation along a sequence yields a labeled seed.** -/
@[cluster_algebras "lem_mutation_sequence_is_seed"]
theorem IsLabeledSeed.seedMutationSeq [CharZero K] (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (s : List (Fin n)) :
    IsLabeledSeed K hmn (ClusterAlgebras.seedMutationSeq hmn S s) := by
  induction s generalizing S with
  | nil => exact hS
  | cons k s ih => exact ih (hS.seedMutation hmn k)

/-- **Mutation along a sequence keeps every extended-cluster entry nonzero.** -/
@[cluster_algebras "lem_mutation_sequence_is_seed"]
theorem IsLabeledSeed.seedMutationSeq_extCluster_ne_zero [CharZero K] (hmn : n ≤ m)
    {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) (s : List (Fin n)) (i : Fin m) :
    (ClusterAlgebras.seedMutationSeq hmn S s).extCluster i ≠ 0 :=
  (hS.seedMutationSeq hmn s).1.1.ne_zero i

/-- **Negating the matrix of a labeled seed gives a labeled seed.** -/
@[cluster_algebras "lem_mutation_sequence_neg"]
theorem IsLabeledSeed.neg (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) :
    IsLabeledSeed K hmn { S with extExchangeMatrix := -S.extExchangeMatrix } := by
  obtain ⟨hx, d, hd⟩ := hS
  refine ⟨hx, d, hd.1, fun i j => ?_⟩
  have h := hd.2 i j
  simp only [Matrix.submatrix_apply, Matrix.neg_apply, id, mul_neg, neg_neg] at h ⊢
  linarith

/-- **Negating the matrix does not change the extended clusters.** Mutating along `s` from
`(x̃, -B̃)` gives the extended cluster obtained from `(x̃, B̃)`, and the negated matrix. -/
@[cluster_algebras "lem_mutation_sequence_neg"]
theorem seedMutationSeq_neg (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (s : List (Fin n)) :
    seedMutationSeq hmn { S with extExchangeMatrix := -S.extExchangeMatrix } s =
      { seedMutationSeq hmn S s with
        extExchangeMatrix := -(seedMutationSeq hmn S s).extExchangeMatrix } := by
  obtain ⟨-, hB⟩ := hS
  induction s generalizing S with
  | nil => rfl
  | cons k s ih =>
    rw [seedMutationSeq_cons, seedMutationSeq_cons, ← ih (hB.matrixMutation hmn k)]
    congr 1
    refine SeedData.ext ?_ (matrixMutation_neg hmn (hB.signAntisymmetric hmn).1 k)
    simp only [seedMutation, exchangeMonomialPos_neg, exchangeMonomialNeg_neg, add_comm]

/-- **Mutations in non-interacting directions commute.** If `bⱼₖ = 0` for distinct `j, k`,
mutating a labeled seed at `j` then `k` gives the same seed as at `k` then `j`. -/
@[cluster_algebras "lem_seed_mutation_commute"]
theorem seedMutation_comm (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S)
    {j k : Fin n} (hjk : j ≠ k) (hb : S.extExchangeMatrix (Fin.castLE hmn j) k = 0) :
    seedMutation hmn (seedMutation hmn S j) k = seedMutation hmn (seedMutation hmn S k) j := by
  classical
  have hsign := hS.2.signAntisymmetric hmn
  set x := S.extCluster
  set B := S.extExchangeMatrix
  have hkj := hsign.eq_zero_of_eq_zero hmn hb
  have hc : Fin.castLE hmn j ≠ Fin.castLE hmn k := fun h => hjk (by simpa [Fin.ext_iff] using h)
  have hup : ∀ {l c : Fin n} {v : F}, B (Fin.castLE hmn l) c = 0 →
      ∀ i, B i c ≠ 0 → Function.update x (Fin.castLE hmn l) v i = x i := fun h i hi =>
    Function.update_of_ne (fun hil => hi (by rwa [hil])) _ _
  refine SeedData.ext ?_ (matrixMutation_comm hmn hsign.1 hjk hb hkj)
  simp only [seedMutation]
  rw [Function.update_of_ne hc.symm, Function.update_of_ne hc,
    exchangeMonomialPos_congr (x := x) (B := B) (hup hb)
      (matrixMutation_apply_of_castLE_eq_zero hmn hjk.symm hb),
    exchangeMonomialNeg_congr (x := x) (B := B) (hup hb)
      (matrixMutation_apply_of_castLE_eq_zero hmn hjk.symm hb),
    exchangeMonomialPos_congr (x := x) (B := B) (hup hkj)
      (matrixMutation_apply_of_castLE_eq_zero hmn hjk hkj),
    exchangeMonomialNeg_congr (x := x) (B := B) (hup hkj)
      (matrixMutation_apply_of_castLE_eq_zero hmn hjk hkj)]
  exact Function.update_comm hc _ _ _

/-- The **generic seed** of an `m × n` integer matrix `B`: the indeterminates `X₁, …, Xₘ` of
the field of rational functions `ℚ(X₁, …, Xₘ)`, together with `B`. -/
@[cluster_algebras "lem_generic_seed"]
noncomputable def genericSeed (B : Matrix (Fin m) (Fin n) ℤ) :
    SeedData (FractionRing (MvPolynomial (Fin m) ℚ)) m n where
  extCluster i := algebraMap (MvPolynomial (Fin m) ℚ) _ (MvPolynomial.X i)
  extExchangeMatrix := B

/-- **The generic seed.** For an extended skew-symmetrizable integer matrix `B`, the
indeterminates of `ℚ(X₁, …, Xₘ)` together with `B` form a labeled seed over `ℚ`. -/
@[cluster_algebras "lem_generic_seed"]
theorem isLabeledSeed_genericSeed (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) ℤ}
    (hB : ExtSkewSymmetrizable hmn B) : IsLabeledSeed ℚ hmn (genericSeed B) := by
  set FR := FractionRing (MvPolynomial (Fin m) ℚ)
  refine ⟨⟨?_, ?_⟩, hB⟩
  · exact (MvPolynomial.algebraicIndependent_X (Fin m) ℚ).map'
      (f := (algebraMap (MvPolynomial (Fin m) ℚ) FR).toRatAlgHom) (IsFractionRing.injective _ _)
  · set L := IntermediateField.adjoin ℚ (Set.range (genericSeed B).extCluster)
    have hmem : ∀ p : MvPolynomial (Fin m) ℚ, algebraMap _ FR p ∈ L := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        rw [← RingHom.comp_apply, RingHom.ext_rat ((algebraMap _ FR).comp MvPolynomial.C)
          (algebraMap ℚ FR)]
        exact IntermediateField.algebraMap_mem L a
      | add p q hp hq =>
        rw [map_add]
        exact add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul]
        exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    rw [eq_top_iff]
    rintro z -
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin m) ℚ) z
    exact div_mem (hmem a) (hmem b)

end ClusterAlgebras

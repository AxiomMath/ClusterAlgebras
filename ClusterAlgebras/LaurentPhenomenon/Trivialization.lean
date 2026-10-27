/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Semifield.Universal
public import ClusterAlgebras.Seed
public import ClusterAlgebras.LaurentPhenomenon.ThreeMutations

/-!
# Extended clusters are subtraction-free, and deleting frozen rows

Two steps of the proof of the Laurent phenomenon.

The first says that the entries of every extended cluster obtained from a seed `(x̃, B̃)` by
mutations lie in the universal semifield `ℚ_sf(x̃)`: seed mutation only multiplies, adds and
divides.

The second compares mutation of `(x̃, B̃)` with mutation of a seed `(x̃', B̃')` obtained by
deleting frozen rows. Let `ι : [1, m'] → [1, m]` be injective and the identity on the first
`n` positions, and let `B̃'` be the matrix of rows `B̃_{ι(a) ·}`. Then row deletion commutes
with matrix mutation, and a semifield homomorphism `ψ : ℚ_sf(x̃) → ℚ_sf(x̃')` sending `x_{ι(a)}`
to `x'_a` and every other `xᵢ` to `1` sends the entry in position `ι(a)` of the extended
cluster of `μ_s(x̃, B̃)` to the entry in position `a` of that of `μ_s(x̃', B̃')`. When `x̃`
generates `F` freely over `𝕜` and `x̃'` is its subfamily `(x_{ι(a)})`, the seed `(x̃', B̃')` is a
labeled seed in `𝕜(x̃')`.

## Main results

* `seedMutationSeq_extCluster_mem_universalSemifield_self`: the entries of the extended cluster
  of `μ_s(x̃, B̃)` lie in `ℚ_sf(x̃)`.
* `matrixMutation_submatrix_rows`: deleting rows other than the first `n` commutes with mutation.
* `IsLabeledSeed.submatrix`: the seed `(x̃', B̃')` is a labeled seed in `𝕜(x̃')`.
* `FZSemifieldHom.coe_apply_seedMutationSeq_extCluster`: `ψ` intertwines mutation of
  `(x̃, B̃)` and mutation of `(x̃', B̃')`.

## Implementation notes

FWZ state the first result for a labeled seed. Their proof uses only the closure of
`ℚ_sf(x̃)` under products, sums and quotients, which holds with no hypothesis on `x̃`, so it is
stated for an arbitrary seed; the one-step and many-step versions are stated for every
`ℚ_sf(ỹ)` containing the entries of the seed.

FWZ take `I ⊆ [n + 1, m]`, `ι` the increasing bijection onto the complement of `I`,
and the seed `(x̃', B̃')` in the subfield `F' = 𝕜(x̃')` of `F`. The comparison of mutations
only uses that `ι` is injective and the identity on the first `n` positions, and that `ψ`
sends every `xᵢ` with `i` outside the range of `ι` to `1`; it holds for an arbitrary field
`F'` and tuple `x̃'` with `ψ(x_{ι(a)}) = x'_a`, and for an arbitrary `ℚ_sf(ỹ)` containing the
entries of `x̃`, and needs no hypothesis on the seeds. FWZ's `F' = 𝕜(x̃')` is the special
case `F' = 𝕜(x_{ι(1)}, …, x_{ι(m')})`, `x'_a = x_{ι(a)}`, of `IsLabeledSeed.submatrix`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 1–3*][FWZ16]
-/

@[expose] public section

namespace ClusterAlgebras

variable {F F' : Type*} [Field F] [Field F'] {m m' n : ℕ} {κ κ' : Type*} {y : κ → F}
  {y' : κ' → F'}

/-! ### Extended clusters are subtraction-free -/

section SubtractionFree

/-- `ℚ_sf(y)` is closed under finite products. -/
theorem prod_mem_universalSemifield {α : Type*} {s : Finset α} {f : α → F}
    (h : ∀ i ∈ s, f i ∈ universalSemifield y) : ∏ i ∈ s, f i ∈ universalSemifield y :=
  Finset.prod_induction f (· ∈ universalSemifield y) (fun _ _ => mul_mem_universalSemifield)
    one_mem_universalSemifield h

/-- The positive exchange monomial of a tuple of elements of `ℚ_sf(y)` lies in `ℚ_sf(y)`. -/
theorem exchangeMonomialPos_mem_universalSemifield {x : Fin m → F}
    (hx : ∀ i, x i ∈ universalSemifield y) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    exchangeMonomialPos x B k ∈ universalSemifield y := by
  rw [exchangeMonomialPos_eq_prod]
  exact prod_mem_universalSemifield fun i _ => pow_mem_universalSemifield (hx i) _

/-- The negative exchange monomial of a tuple of elements of `ℚ_sf(y)` lies in `ℚ_sf(y)`. -/
theorem exchangeMonomialNeg_mem_universalSemifield {x : Fin m → F}
    (hx : ∀ i, x i ∈ universalSemifield y) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    exchangeMonomialNeg x B k ∈ universalSemifield y := by
  rw [exchangeMonomialNeg_eq_prod]
  exact prod_mem_universalSemifield fun i _ => pow_mem_universalSemifield (hx i) _

/-- One mutation keeps the entries of an extended cluster in `ℚ_sf(y)`. -/
theorem seedMutation_extCluster_mem_universalSemifield (hmn : n ≤ m) {S : SeedData F m n}
    (hS : ∀ i, S.extCluster i ∈ universalSemifield y) (k : Fin n) (i : Fin m) :
    (seedMutation hmn S k).extCluster i ∈ universalSemifield y := by
  rcases eq_or_ne i (Fin.castLE hmn k) with rfl | hi
  · rw [seedMutation_extCluster_castLE_self]
    exact div_mem_universalSemifield (add_mem_universalSemifield
      (exchangeMonomialPos_mem_universalSemifield hS _ _)
      (exchangeMonomialNeg_mem_universalSemifield hS _ _)) (hS _)
  · rw [seedMutation_extCluster_of_ne hmn S hi]
    exact hS i

/-- Mutation along a sequence keeps the entries of an extended cluster in `ℚ_sf(y)`. -/
theorem seedMutationSeq_extCluster_mem_universalSemifield (hmn : n ≤ m) {S : SeedData F m n}
    (hS : ∀ i, S.extCluster i ∈ universalSemifield y) (s : List (Fin n)) (i : Fin m) :
    (seedMutationSeq hmn S s).extCluster i ∈ universalSemifield y := by
  induction s generalizing S with
  | nil => exact hS i
  | cons k s ih => exact ih (seedMutation_extCluster_mem_universalSemifield hmn hS k)

/-- **Extended clusters are subtraction-free.** Every entry of the extended cluster of
`μ_s(x̃, B̃)` lies in `ℚ_sf(x̃)`. FWZ assume `(x̃, B̃)` is a labeled seed; the proof does
not use it, so it is not assumed. -/
@[cluster_algebras "lem_cluster_variables_subtraction_free"]
theorem seedMutationSeq_extCluster_mem_universalSemifield_self (hmn : n ≤ m)
    (S : SeedData F m n) (s : List (Fin n)) (i : Fin m) :
    (seedMutationSeq hmn S s).extCluster i ∈ universalSemifield S.extCluster :=
  seedMutationSeq_extCluster_mem_universalSemifield hmn (mem_universalSemifield_self _) s i

end SubtractionFree

/-! ### Deleting frozen rows -/

section Trivialization

/-- **Deleting rows commutes with mutation.** If `ι` is injective and the identity on the first
`n` rows, keeping the rows `ι(1), …, ι(m')` of `B` and mutating in direction `k` gives the same
matrix as mutating `B` in direction `k` and then keeping those rows. -/
theorem matrixMutation_submatrix_rows {R : Type*} [CommRing R] [LinearOrder R] (hmn : n ≤ m)
    (hmn' : n ≤ m') (B : Matrix (Fin m) (Fin n) R) {ι : Fin m' → Fin m}
    (hι : Function.Injective ι) (hιn : ∀ k : Fin n, ι (Fin.castLE hmn' k) = Fin.castLE hmn k)
    (k : Fin n) :
    matrixMutation hmn' (B.submatrix ι id) k = (matrixMutation hmn B k).submatrix ι id := by
  ext a j
  have ha : a = Fin.castLE hmn' k ↔ ι a = Fin.castLE hmn k := by rw [← hιn, hι.eq_iff]
  simp [matrixMutation, hιn, ha]

variable {K : Type*} [Field K] [Algebra K F]

/-- **Deleting frozen rows gives a labeled seed.** Let `(x̃, B̃)` be a labeled seed in `F` over
`K` and let `ι` be injective and the identity on the first `n` positions. Then the subfamily
`x̃' = (x_{ι(a)})` and the matrix `B̃'` of rows `B̃_{ι(a) ·}` form a labeled seed in the field
`K(x̃')` over `K`. -/
@[cluster_algebras "lem_trivialization"]
theorem IsLabeledSeed.submatrix (hmn : n ≤ m) (hmn' : n ≤ m') {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) {ι : Fin m' → Fin m} (hι : Function.Injective ι)
    (hιn : ∀ k : Fin n, ι (Fin.castLE hmn' k) = Fin.castLE hmn k) :
    IsLabeledSeed K hmn'
      (⟨fun a => ⟨S.extCluster (ι a), IntermediateField.subset_adjoin K _ ⟨a, rfl⟩⟩,
        S.extExchangeMatrix.submatrix ι id⟩ :
        SeedData (IntermediateField.adjoin K (Set.range (S.extCluster ∘ ι))) m' n) := by
  refine ⟨⟨AlgebraicIndependent.of_comp (IntermediateField.val _) (hS.1.1.comp ι hι), ?_⟩, ?_⟩
  · apply IntermediateField.map_injective (IntermediateField.val _)
    rw [IntermediateField.adjoin_map, ← Set.range_comp]
    exact (IntermediateField.lift_top K _).symm
  · have h : (S.extExchangeMatrix.submatrix ι id).submatrix (Fin.castLE hmn') id =
        S.extExchangeMatrix.submatrix (Fin.castLE hmn) id := by
      ext i j
      simp [hιn]
    change SkewSymmetrizable _
    rw [h]
    exact hS.2

variable [CharZero F] [Fact (AlgebraicIndependent ℚ y)]

/-- A product in `ℚ_sf(y)`, seen in `F`, is the product in `F`. -/
theorem universalSemifield.coe_prod {α : Type*} (s : Finset α) (f : α → universalSemifield y) :
    ((∏ i ∈ s, f i : universalSemifield y) : F) = ∏ i ∈ s, (f i : F) :=
  map_prod (⟨⟨Subtype.val, rfl⟩, fun _ _ => rfl⟩ : universalSemifield y →* F) f s

variable [CharZero F'] [Fact (AlgebraicIndependent ℚ y')]
  (ψ : FZSemifieldHom (universalSemifield y) (universalSemifield y'))

/-- A semifield homomorphism `ψ` out of `ℚ_sf(y)` sends a product of natural powers of elements
`xᵢ` of `ℚ_sf(y)` to the product of the same powers of the `ψ(xᵢ)`. -/
theorem FZSemifieldHom.coe_apply_prod_pow {α : Type*} [Fintype α] {x : α → F}
    (hx : ∀ i, x i ∈ universalSemifield y) (e : α → ℕ) :
    (ψ ⟨∏ i, x i ^ e i, prod_mem_universalSemifield fun i _ =>
        pow_mem_universalSemifield (hx i) (e i)⟩ : F') =
      ∏ i, (ψ ⟨x i, hx i⟩ : F') ^ e i := by
  have h : (⟨∏ i, x i ^ e i, prod_mem_universalSemifield fun i _ =>
        pow_mem_universalSemifield (hx i) (e i)⟩ : universalSemifield y) =
      ∏ i, (⟨x i, hx i⟩ : universalSemifield y) ^ e i :=
    Subtype.ext (by rw [universalSemifield.coe_prod]; rfl)
  rw [h, map_prod, universalSemifield.coe_prod]
  simp only [map_pow]
  rfl

/-- If `ψ` sends `x_{ι(a)}` to `x'_a` and every `xᵢ` with `i` outside the range of the
injective map `ι` to `1`, then it sends `∏ᵢ xᵢ ^ eᵢ` to `∏ₐ (x'_a) ^ e_{ι(a)}`. -/
theorem FZSemifieldHom.coe_apply_prod_pow_of_injective {x : Fin m → F}
    (hx : ∀ i, x i ∈ universalSemifield y) {x' : Fin m' → F'} {ι : Fin m' → Fin m}
    (hι : Function.Injective ι) (hψ : ∀ a, (ψ ⟨x (ι a), hx (ι a)⟩ : F') = x' a)
    (hψ₁ : ∀ i ∉ Set.range ι, ψ ⟨x i, hx i⟩ = 1) (e : Fin m → ℕ) :
    (ψ ⟨∏ i, x i ^ e i, prod_mem_universalSemifield fun i _ =>
        pow_mem_universalSemifield (hx i) (e i)⟩ : F') = ∏ a, x' a ^ e (ι a) := by
  rw [ψ.coe_apply_prod_pow hx]
  refine (Fintype.prod_of_injective ι hι _ _ (fun i hi => ?_) fun a => ?_).symm
  · rw [hψ₁ i hi, universalSemifield.coe_one, one_pow]
  · rw [hψ a]

/-- Under the hypotheses of `FZSemifieldHom.coe_apply_prod_pow_of_injective`, `ψ` sends the
positive exchange monomial of `(x̃, B̃)` to that of `(x̃', B̃')`, where `B̃'` has rows
`B̃_{ι(a) ·}`. -/
theorem FZSemifieldHom.coe_apply_exchangeMonomialPos {x : Fin m → F}
    (hx : ∀ i, x i ∈ universalSemifield y) {x' : Fin m' → F'} {ι : Fin m' → Fin m}
    (hι : Function.Injective ι) (hψ : ∀ a, (ψ ⟨x (ι a), hx (ι a)⟩ : F') = x' a)
    (hψ₁ : ∀ i ∉ Set.range ι, ψ ⟨x i, hx i⟩ = 1) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    (ψ ⟨exchangeMonomialPos x B k, exchangeMonomialPos_mem_universalSemifield hx B k⟩ : F') =
      exchangeMonomialPos x' (B.submatrix ι id) k := by
  have h : (⟨exchangeMonomialPos x B k, exchangeMonomialPos_mem_universalSemifield hx B k⟩ :
      universalSemifield y) = ⟨∏ i, x i ^ (B i k).toNat, prod_mem_universalSemifield fun i _ =>
        pow_mem_universalSemifield (hx i) _⟩ :=
    Subtype.ext exchangeMonomialPos_eq_prod
  rw [h, ψ.coe_apply_prod_pow_of_injective hx hι hψ hψ₁, exchangeMonomialPos_eq_prod]
  rfl

/-- Under the hypotheses of `FZSemifieldHom.coe_apply_prod_pow_of_injective`, `ψ` sends the
negative exchange monomial of `(x̃, B̃)` to that of `(x̃', B̃')`, where `B̃'` has rows
`B̃_{ι(a) ·}`. -/
theorem FZSemifieldHom.coe_apply_exchangeMonomialNeg {x : Fin m → F}
    (hx : ∀ i, x i ∈ universalSemifield y) {x' : Fin m' → F'} {ι : Fin m' → Fin m}
    (hι : Function.Injective ι) (hψ : ∀ a, (ψ ⟨x (ι a), hx (ι a)⟩ : F') = x' a)
    (hψ₁ : ∀ i ∉ Set.range ι, ψ ⟨x i, hx i⟩ = 1) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    (ψ ⟨exchangeMonomialNeg x B k, exchangeMonomialNeg_mem_universalSemifield hx B k⟩ : F') =
      exchangeMonomialNeg x' (B.submatrix ι id) k := by
  have h : (⟨exchangeMonomialNeg x B k, exchangeMonomialNeg_mem_universalSemifield hx B k⟩ :
      universalSemifield y) = ⟨∏ i, x i ^ (-B i k).toNat, prod_mem_universalSemifield fun i _ =>
        pow_mem_universalSemifield (hx i) _⟩ :=
    Subtype.ext exchangeMonomialNeg_eq_prod
  rw [h, ψ.coe_apply_prod_pow_of_injective hx hι hψ hψ₁, exchangeMonomialNeg_eq_prod]
  rfl

/-- **One step of the comparison.** Let `ι` be injective and the identity on the first `n`
positions, let the matrix of `S'` have rows `B̃_{ι(a) ·}`, and let `ψ` send the entry of `S` in
position `ι(a)` to that of `S'` in position `a` and every other entry of `S` to `1`. Then `ψ`
sends the entry of `μₖ(S)` in position `ι(a)` to that of `μₖ(S')` in position `a`. -/
theorem FZSemifieldHom.coe_apply_seedMutation_extCluster (hmn : n ≤ m) (hmn' : n ≤ m')
    {S : SeedData F m n} {S' : SeedData F' m' n} (hS : ∀ i, S.extCluster i ∈ universalSemifield y)
    {ι : Fin m' → Fin m} (hι : Function.Injective ι)
    (hιn : ∀ k : Fin n, ι (Fin.castLE hmn' k) = Fin.castLE hmn k)
    (hB : S'.extExchangeMatrix = S.extExchangeMatrix.submatrix ι id)
    (hψ : ∀ a, (ψ ⟨S.extCluster (ι a), hS (ι a)⟩ : F') = S'.extCluster a)
    (hψ₁ : ∀ i ∉ Set.range ι, ψ ⟨S.extCluster i, hS i⟩ = 1) (k : Fin n) (a : Fin m') :
    (ψ ⟨(seedMutation hmn S k).extCluster (ι a),
        seedMutation_extCluster_mem_universalSemifield hmn hS k (ι a)⟩ : F') =
      (seedMutation hmn' S' k).extCluster a := by
  rcases eq_or_ne a (Fin.castLE hmn' k) with rfl | ha
  · have h : (⟨(seedMutation hmn S k).extCluster (ι (Fin.castLE hmn' k)),
          seedMutation_extCluster_mem_universalSemifield hmn hS k _⟩ : universalSemifield y) =
        (⟨_, exchangeMonomialPos_mem_universalSemifield hS S.extExchangeMatrix k⟩ +
          ⟨_, exchangeMonomialNeg_mem_universalSemifield hS S.extExchangeMatrix k⟩) /
          ⟨S.extCluster (ι (Fin.castLE hmn' k)), hS _⟩ :=
      Subtype.ext (by
        change (seedMutation hmn S k).extCluster _ = (_ + _) / S.extCluster _
        rw [hιn, seedMutation_extCluster_castLE_self])
    rw [h, map_div, map_add, universalSemifield.coe_div, universalSemifield.coe_add,
      ψ.coe_apply_exchangeMonomialPos hS hι hψ hψ₁, ψ.coe_apply_exchangeMonomialNeg hS hι hψ hψ₁,
      hψ, seedMutation_extCluster_castLE_self, hB]
  · have hia : ι a ≠ Fin.castLE hmn k := by rwa [← hιn, hι.ne_iff]
    have h : (⟨(seedMutation hmn S k).extCluster (ι a),
          seedMutation_extCluster_mem_universalSemifield hmn hS k _⟩ : universalSemifield y) =
        ⟨S.extCluster (ι a), hS _⟩ :=
      Subtype.ext (seedMutation_extCluster_of_ne hmn S hia)
    rw [h, hψ, seedMutation_extCluster_of_ne hmn' S' ha]

/-- **Deleting frozen rows specializes the frozen variables to one.** Let `ι` be injective and
the identity on the first `n` positions, let the matrix of `S'` have rows `B̃_{ι(a) ·}`, and let
`ψ : ℚ_sf(ỹ) → ℚ_sf(ỹ')` be a semifield homomorphism sending the entry of `S` in position `ι(a)`
to that of `S'` in position `a`, and every other entry of `S` to `1`. Then for every sequence
`s`, `ψ` sends the entry of `μ_s(S)` in position `ι(a)` to that of `μ_s(S')` in position `a`.

FWZ take `S = (x̃, B̃)` a labeled seed in `F`, `ỹ = x̃`, `ι` the increasing bijection
onto the complement of a set of frozen positions and `S'` the seed of
`IsLabeledSeed.submatrix`, in the subfield `F' = 𝕜(x̃')`; none of this is used. -/
@[cluster_algebras "lem_trivialization"]
theorem FZSemifieldHom.coe_apply_seedMutationSeq_extCluster (hmn : n ≤ m) (hmn' : n ≤ m')
    {S : SeedData F m n} {S' : SeedData F' m' n} (hS : ∀ i, S.extCluster i ∈ universalSemifield y)
    {ι : Fin m' → Fin m} (hι : Function.Injective ι)
    (hιn : ∀ k : Fin n, ι (Fin.castLE hmn' k) = Fin.castLE hmn k)
    (hB : S'.extExchangeMatrix = S.extExchangeMatrix.submatrix ι id)
    (hψ : ∀ a, (ψ ⟨S.extCluster (ι a), hS (ι a)⟩ : F') = S'.extCluster a)
    (hψ₁ : ∀ i ∉ Set.range ι, ψ ⟨S.extCluster i, hS i⟩ = 1) (s : List (Fin n)) (a : Fin m') :
    (ψ ⟨(seedMutationSeq hmn S s).extCluster (ι a),
        seedMutationSeq_extCluster_mem_universalSemifield hmn hS s (ι a)⟩ : F') =
      (seedMutationSeq hmn' S' s).extCluster a := by
  induction s generalizing S S' with
  | nil => exact hψ a
  | cons k s ih =>
    have hS₁ := seedMutation_extCluster_mem_universalSemifield hmn hS k
    refine ih hS₁ ?_ (ψ.coe_apply_seedMutation_extCluster hmn hmn' hS hι hιn hB hψ hψ₁ k)
      fun i hi => ?_
    · rw [seedMutation_extExchangeMatrix, seedMutation_extExchangeMatrix, hB,
        matrixMutation_submatrix_rows hmn hmn' _ hι hιn]
    · have hik : i ≠ Fin.castLE hmn k := fun h => hi ⟨Fin.castLE hmn' k, by rw [hιn, h]⟩
      have h : (⟨(seedMutation hmn S k).extCluster i, hS₁ i⟩ : universalSemifield y) =
          ⟨S.extCluster i, hS i⟩ :=
        Subtype.ext (seedMutation_extCluster_of_ne hmn S hik)
      rw [h, hψ₁ i hi]

end Trivialization

end ClusterAlgebras

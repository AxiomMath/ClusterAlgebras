/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeA.PluckerSeed
public import ClusterAlgebras.Cartan.Counterpart
public import ClusterAlgebras.Coefficients.ZSpanRescaling

/-!
# Seed patterns of type `A_n`

An arbitrary seed pattern of type `A_n` has the exchange matrices of a Plücker pattern
(`IsSeedPattern.exists_pluckerPattern_of_typeA`), and at the vertex where the Plücker pattern
carries the fan its extended exchange matrix has full `ℤ`-rank. The `ℤ`-span results on
rescalings then transfer finiteness, the labelling of cluster variables by diagonals, and the
counts from the Plücker pattern to the arbitrary one.

## Main results

* `ClusterAlgebras.IsSeedPattern.principalPart_propagate`: exchange matrices agreeing at one
  vertex agree everywhere.
* `ClusterAlgebras.TypeA.exists_labelledTriangulation_matrix_eq`: an exchange matrix whose
  Cartan counterpart is of type `A_n` is `B(T, λ)` for a labelled triangulation.
* `ClusterAlgebras.IsSeedPattern.tfae_isPatternOfType_A`: a seed pattern is of type `A_n` if
  and only if some (equivalently, every) exchange matrix is `B(T, λ)` for a labelled
  triangulation.
* `ClusterAlgebras.IsSeedPattern.isFiniteType_of_typeA`: **seed patterns of type `A_n` are of
  finite type**.
* `ClusterAlgebras.IsSeedPattern.exists_typeA_structure`: cluster variables of type `A_n` are
  labelled by diagonals.
* `ClusterAlgebras.IsSeedPattern.encard_patternClusterVariables_of_typeA`,
  `ClusterAlgebras.IsSeedPattern.encard_patternClusters_of_typeA`: **`n(n+3)/2` cluster
  variables and `c_{n+1} = binom(2n+2, n+1)/(n+2)` clusters**.

## Implementation notes

* "Of type `A_n`" is `IsPatternOfType hmn P [DynkinSymbol.A n hn]`.
* The comparison patterns live in the Plücker field over the same ground field `K` as the
  arbitrary pattern, as the `ℤ`-span results require.
* The labelling of cluster variables by diagonals is an injective map
  `χ : Sym2 (ZMod (n+3)) → F` on the diagonals (`Set.InjOn`), whose values off the diagonals
  are irrelevant.
* The number of classes of "representing the same unlabeled seed" is the `encard` of the set of
  its classes `{t' | Σ(t) ≈ Σ(t')}`, `t ∈ 𝕋ₙ`.
-/

@[expose] public section

namespace ClusterAlgebras

open TypeA

/-! ### Exchange matrices along a pattern -/

/-- **Exchange matrices agreeing at one vertex agree everywhere.** Let `P` and `P'` be seed
patterns of rank `n`, possibly over different ground fields, in different fields and with
different numbers of frozen variables. If the exchange matrices of `P t₀` and `P' t₀` are equal,
then those of `P t` and `P' t` are equal for every `t`.

This generalizes `IsSeedPattern.principalPart_eq_of_principalPart_eq`, which has a common
ground field. -/
@[cluster_algebras "lem_principal_parts_propagate"]
theorem IsSeedPattern.principalPart_propagate {K F K' F' : Type*} [Field K] [Field F]
    [Algebra K F] [Field K'] [Field F'] [Algebra K' F'] {m m' n : ℕ} {hmn : n ≤ m}
    {hm' : n ≤ m'} {P : RegularTree n → SeedData F m n} {P' : RegularTree n → SeedData F' m' n}
    (hP : IsSeedPattern K hmn P) (hP' : IsSeedPattern K' hm' P') {t₀ : RegularTree n}
    (h₀ : principalPart hmn (P t₀).extExchangeMatrix = principalPart hm' (P' t₀).extExchangeMatrix)
    (t : RegularTree n) :
    principalPart hmn (P t).extExchangeMatrix = principalPart hm' (P' t).extExchangeMatrix :=
  congrFun (RegularTree.eq_of_apply_eq_of_adj (fun k B => matrixMutation le_rfl B k)
    (P := fun t => principalPart hmn (P t).extExchangeMatrix)
    (P' := fun t => principalPart hm' (P' t).extExchangeMatrix)
    (fun k t t' h => by
      rw [hP.2 k t t' h, seedMutation_extExchangeMatrix, principalPart_matrixMutation])
    (fun k t t' h => by
      rw [hP'.2 k t t' h, seedMutation_extExchangeMatrix, principalPart_matrixMutation]) h₀) t

/-! ### Exchange matrices of type `A_n` -/

namespace TypeA

/-- Being of type `A_n` is being `C(A_n)` up to a simultaneous permutation of rows and columns. -/
private theorem isOfDynkinType_A_iff_exists_perm_typeA {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    IsOfDynkinType A [DynkinSymbol.A n hn] ↔
      ∃ π : Fin n ≃ Fin n, ∀ i j, A i j = cartanA n (π i) (π j) := by
  have key : ∀ i j : Fin n,
      DynkinSymbol.listCartan [DynkinSymbol.A n hn] i j = cartanA n i j := by
    intro i j
    simp only [DynkinSymbol.listCartan, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact (congrArg₂ (Matrix.fromBlocks (DynkinSymbol.A n hn).cartan 0 0
        (0 : Matrix (Fin 0) (Fin 0) ℤ))
        (finSumFinEquiv_symm_apply_castAdd (n := DynkinSymbol.listRank []) i)
        (finSumFinEquiv_symm_apply_castAdd (n := DynkinSymbol.listRank []) j)).trans
      (Matrix.fromBlocks_apply₁₁ _ _ _ _ _ _)
  exact ⟨fun ⟨σ, h⟩ => ⟨σ, fun i j => (h i j).trans (key _ _)⟩,
    fun ⟨σ, h⟩ => ⟨σ, fun i j => (h i j).trans (key _ _).symm⟩⟩

/-- The entries of `B(T, λ)` are the signed counts `β_T(λ(i), λ(j))`. -/
private theorem LabelledTriangulation.matrix_apply_eq_signedCount_typeA {n : ℕ}
    (L : LabelledTriangulation n) (i j : Fin n) :
    L.matrix i j = signedCount (polygonArrows L.triangulation) (L.label i) (L.label j) := by
  simp [LabelledTriangulation.matrix, principalPart, LabelledTriangulation.extMatrix]

/-- The entries of `C(A_n)`. -/
private theorem cartanA_apply_typeA {n : ℕ} (a b : Fin n) :
    cartanA n a b =
      if a = b then 2 else if (a : ℕ) + 1 = b ∨ (b : ℕ) + 1 = a then -1 else 0 := rfl

/-- The entries of a skew-symmetrizable `B` whose Cartan counterpart is `C(A_n)` up to the
permutation `π`: they vanish on the diagonal, are skew-symmetric, and off the diagonal have
absolute value `1` on the edges of the path and `0` elsewhere. -/
private theorem entries_of_perm_cartanA_typeA {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {π : Fin n ≃ Fin n}
    (hπ : ∀ i j, cartanCounterpart B i j = cartanA n (π i) (π j)) :
    (∀ i, B i i = 0) ∧ (∀ i j, B j i = -B i j) ∧ ∀ i j, i ≠ j →
      |B i j| = if (π i : ℕ) + 1 = π j ∨ (π j : ℕ) + 1 = π i then 1 else 0 := by
  obtain ⟨dv, hdpos, hdv⟩ := hB
  simp only [Int.cast_id] at hdv
  have hdiag : ∀ i, B i i = 0 := fun i => by
    have h2 : dv i * B i i = 0 := by linarith [hdv i i]
    exact (mul_eq_zero.1 h2).resolve_left (hdpos i).ne'
  have habs : ∀ i j, i ≠ j →
      |B i j| = if (π i : ℕ) + 1 = π j ∨ (π j : ℕ) + 1 = π i then 1 else 0 := by
    intro i j hij
    have h := hπ i j
    rw [cartanA_apply_typeA, if_neg (fun h => hij (π.injective h))] at h
    simp only [cartanCounterpart, Matrix.of_apply, if_neg hij] at h
    split_ifs at h ⊢ <;> linarith
  refine ⟨hdiag, fun i j => ?_, habs⟩
  by_cases hij : i = j
  · subst hij
    simp [hdiag]
  have h1 := habs i j hij
  have h2 := habs j i (Ne.symm hij)
  have h3 := hdv i j
  have hdi := hdpos i
  have hdj := hdpos j
  rw [if_congr Or.comm rfl rfl] at h2
  split_ifs at h1 h2
  · rcases abs_eq (zero_le_one' ℤ) |>.1 h1 with ha | ha <;>
      rcases abs_eq (zero_le_one' ℤ) |>.1 h2 with hb | hb <;>
      rw [ha, hb] at h3 ⊢ <;> omega
  · rw [abs_eq_zero.1 h1, abs_eq_zero.1 h2, neg_zero]

/-- **Exchange matrices of type `A_n` come from triangulations, (i).** A skew-symmetrizable
`n × n` integer matrix whose Cartan counterpart is of type `A_n` is `B(T, λ)` for some labelled
triangulation `(T, λ)` of the `(n+3)`-gon. -/
@[cluster_algebras "lem_type_A_matrix"]
theorem exists_labelledTriangulation_matrix_eq {n : ℕ} (hn : 1 ≤ n)
    {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B)
    (hA : IsOfDynkinType (cartanCounterpart B) [DynkinSymbol.A n hn]) :
    ∃ L : LabelledTriangulation n, L.matrix = B := by
  classical
  obtain ⟨π, hπ⟩ := (isOfDynkinType_A_iff_exists_perm_typeA hn _).1 hA
  obtain ⟨hdiag, hanti, habs⟩ := entries_of_perm_cartanA_typeA hB hπ
  set ε : Fin n → ℤ := fun p =>
    if h : (p : ℕ) + 1 < n then B (π.symm p) (π.symm ⟨p + 1, h⟩) else 1 with hεdef
  have hε : ∀ p : Fin n, (p : ℕ) + 1 < n → ε p = 1 ∨ ε p = -1 := by
    intro p hp
    have hne : π.symm p ≠ π.symm ⟨p + 1, hp⟩ := fun h => by
      simpa using congrArg Fin.val (π.symm.injective h)
    have h := habs _ _ hne
    simp only [Equiv.apply_symm_apply, true_or, if_true] at h
    rw [show ε p = B (π.symm p) (π.symm ⟨p + 1, hp⟩) from dif_pos hp]
    rcases abs_eq (zero_le_one' ℤ) |>.1 h with h | h <;> simp [h]
  obtain ⟨d, hd⟩ := exists_isPathListing hn ε hε
  have himg : Finset.univ.image (fun i => d (π i)) = Finset.univ.image d := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨a, h⟩ => ⟨π a, h⟩, fun ⟨a, h⟩ => ⟨π.symm a, by simp [h]⟩⟩
  refine ⟨⟨fun i => d (π i), hd.1.comp π.injective, himg ▸ hd.2.1⟩, ?_⟩
  ext i j
  rw [LabelledTriangulation.matrix_apply_eq_signedCount_typeA]
  change signedCount (polygonArrows (Finset.univ.image fun i => d (π i))) (d (π i)) (d (π j)) = _
  rw [himg, hd.2.2]
  by_cases h1 : (π j : ℕ) = π i + 1
  · rw [if_pos h1, hεdef]
    dsimp only
    rw [dif_pos (by omega)]
    have : (⟨π i + 1, by omega⟩ : Fin n) = π j := Fin.ext h1.symm
    rw [this, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · rw [if_neg h1]
    by_cases h2 : (π i : ℕ) = π j + 1
    · rw [if_pos h2, hεdef]
      dsimp only
      rw [dif_pos (by omega)]
      have : (⟨π j + 1, by omega⟩ : Fin n) = π i := Fin.ext h2.symm
      rw [this, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hanti, neg_neg]
    · rw [if_neg h2]
      by_cases hij : i = j
      · subst hij
        rw [hdiag]
      · have h := habs i j hij
        rw [if_neg (by omega)] at h
        exact (abs_eq_zero.1 h).symm

/-- **Exchange matrices of type `A_n` come from triangulations, (ii).** If `T` is the
triangulation `{d₁, …, dₙ}` of a path listing for some signs `ε₁, …, ε_{n-1} ∈ {1, -1}`
(`TypeA.exists_isPathListing`), then for every labelling `λ` of `T` the Cartan counterpart of
`B(T, λ)` is of type `A_n`. -/
@[cluster_algebras "lem_type_A_matrix"]
theorem IsPathListing.isOfDynkinType_cartanCounterpart {n : ℕ} (hn : 1 ≤ n)
    {d : Fin n → Sym2 (ZMod (n + 3))} {ε : Fin n → ℤ}
    (hε : ∀ p : Fin n, (p : ℕ) + 1 < n → ε p = 1 ∨ ε p = -1) (hd : IsPathListing d ε)
    (L : LabelledTriangulation n) (hL : L.triangulation = Finset.univ.image d) :
    IsOfDynkinType (cartanCounterpart L.matrix) [DynkinSymbol.A n hn] := by
  classical
  have hmem : ∀ i, ∃ p, d p = L.label i := fun i => by
    have h : L.label i ∈ L.triangulation := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rw [hL] at h
    simpa using h
  choose π hπ using hmem
  have hπinj : Function.Injective π := fun i j h => L.injective (by rw [← hπ, ← hπ, h])
  set e := Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπinj)
  refine (isOfDynkinType_A_iff_exists_perm_typeA hn _).2 ⟨e, fun i j => ?_⟩
  have he : ∀ i, e i = π i := fun _ => rfl
  rw [he, he, cartanA_apply_typeA]
  by_cases hij : i = j
  · subst hij
    simp [cartanCounterpart]
  have hπij : π i ≠ π j := fun h => hij (hπinj h)
  rw [if_neg hπij]
  simp only [cartanCounterpart, Matrix.of_apply, if_neg hij,
    LabelledTriangulation.matrix_apply_eq_signedCount_typeA, hL, ← hπ, hd.2.2]
  by_cases h1 : (π j : ℕ) = π i + 1
  · rw [if_pos h1, if_pos (Or.inl h1.symm)]
    rcases hε (π i) (by omega) with h | h <;> simp [h]
  · rw [if_neg h1]
    by_cases h2 : (π i : ℕ) = π j + 1
    · rw [if_pos h2, if_pos (Or.inr h2.symm)]
      rcases hε (π j) (by omega) with h | h <;> simp [h]
    · rw [if_neg h2, if_neg (by omega)]
      simp

/-- Two non-crossing diagonals lie in a common triangulation. -/
theorem exists_isTriangulation_mem_mem {m : ℕ} [NeZero m] {δ δ' : Sym2 (ZMod m)}
    (hδ : IsDiagonal δ) (hδ' : IsDiagonal δ') (hc : ¬Cross δ δ') :
    ∃ T, IsTriangulation T ∧ δ ∈ T ∧ δ' ∈ T := by
  classical
  obtain ⟨T, hT, hsub⟩ := exists_isTriangulation_superset (S := {δ, δ'})
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro e (rfl | rfl)
      exacts [hδ, hδ'])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro e (rfl | rfl) f (rfl | rfl)
      exacts [not_cross_self _, hc, fun h => hc h.symm, not_cross_self _])
  exact ⟨T, hT, hsub (by simp), hsub (by simp)⟩

end TypeA

/-! ### Seed patterns of type `A_n` -/

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- A seed pattern whose exchange matrix at `t` is `B(T, λ)` has the exchange matrices of the
Plücker pattern through `Σ(T, λ)` placed at `t`. -/
private theorem IsSeedPattern.exists_pluckerPattern_of_principalPart_eq_typeA [CharZero K]
    {hmn : n ≤ m} {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    {t : RegularTree n} {L : LabelledTriangulation n}
    (hL : principalPart hmn (P t).extExchangeMatrix = L.matrix) :
    ∃ Pl : RegularTree n → SeedData (pluckerField K n) (2 * n + 3) n,
      IsSeedPattern K (le_two_mul_add_three n) Pl ∧ Pl t = pluckerSeed K L ∧
      ∀ t', principalPart (le_two_mul_add_three n) (Pl t').extExchangeMatrix =
        principalPart hmn (P t').extExchangeMatrix := by
  obtain ⟨Pl, hPl, h₁⟩ := exists_isSeedPattern_pluckerSeed K L t
  refine ⟨Pl, hPl, h₁, IsSeedPattern.principalPart_propagate hPl hP (t₀ := t) ?_⟩
  rw [h₁, hL]
  rfl

/-- **Seed patterns of type `A_n` are those with a triangulation exchange matrix**. For a
seed pattern `P` of rank `n ≥ 1` the following are equivalent: (a) `P` is of type `A_n`; (b)
some exchange matrix of `P` is `B(T, λ)` for a labelled triangulation `(T, λ)` of the
`(n+3)`-gon; (c) every exchange matrix of `P` is of this form. -/
@[cluster_algebras "lem_type_A_triangulation"]
theorem IsSeedPattern.tfae_isPatternOfType_A [CharZero K] (hn : 1 ≤ n) (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) :
    List.TFAE [IsPatternOfType hmn P [DynkinSymbol.A n hn],
      ∃ (t : RegularTree n) (L : LabelledTriangulation n),
        principalPart hmn (P t).extExchangeMatrix = L.matrix,
      ∀ t : RegularTree n, ∃ L : LabelledTriangulation n,
        principalPart hmn (P t).extExchangeMatrix = L.matrix] := by
  tfae_have 1 → 2 := by
    rintro ⟨t, ht⟩
    obtain ⟨L, hL⟩ := exists_labelledTriangulation_matrix_eq hn (hP.1 t).2 ht
    exact ⟨t, L, hL.symm⟩
  tfae_have 2 → 3 := by
    rintro ⟨t, L, hL⟩ t'
    obtain ⟨Pl, hPl, h₁, hpp⟩ := hP.exists_pluckerPattern_of_principalPart_eq_typeA hL
    obtain ⟨L', hL', -⟩ := TypeA.IsSeedPattern.existsUnique_pluckerSeed hPl h₁ t'
    exact ⟨L', by rw [← hpp, hL']; rfl⟩
  tfae_have 3 → 1 := by
    intro h
    obtain ⟨L, hL⟩ := h RegularTree.root
    obtain ⟨Pl, hPl, h₁, hpp⟩ := hP.exists_pluckerPattern_of_principalPart_eq_typeA hL
    obtain ⟨d, hd⟩ := exists_isPathListing hn (fun _ => -1) (fun _ _ => Or.inr rfl)
    obtain ⟨s, L', hs, hL'⟩ :=
      TypeA.IsSeedPattern.exists_pluckerSeed_triangulation_eq hPl h₁ hd.2.1
    refine ⟨s, ?_⟩
    rw [← hpp s, hs]
    exact IsPathListing.isOfDynkinType_cartanCounterpart hn (fun _ _ => Or.inr rfl) hd L' hL'
  tfae_finish

/-- **Comparison with the Plücker pattern.** For a seed pattern `P` of type `A_n` over `K`
there are vertices `t₁, t₂`, a labelled triangulation `(T₁, λ₁)` and a seed pattern `Pl` in the
Plücker field `𝓕ₙ` over `K` with `Pl(t₁) = Σ(T₁, λ₁)`, the same exchange matrices as `P` at
every vertex, and `B̃_P(t₂)` satisfying the `ℤ`-span condition with respect to `B̃_{Pl}(t₂)`. -/
@[cluster_algebras "lem_type_A_comparison"]
theorem IsSeedPattern.exists_pluckerPattern_of_typeA [CharZero K] (hn : 1 ≤ n) (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hA : IsPatternOfType hmn P [DynkinSymbol.A n hn]) :
    ∃ (t₁ t₂ : RegularTree n) (L₁ : LabelledTriangulation n)
      (Pl : RegularTree n → SeedData (pluckerField K n) (2 * n + 3) n),
      IsSeedPattern K (le_two_mul_add_three n) Pl ∧ Pl t₁ = pluckerSeed K L₁ ∧
      (∀ t, principalPart (le_two_mul_add_three n) (Pl t).extExchangeMatrix =
        principalPart hmn (P t).extExchangeMatrix) ∧
      ZSpanCondition (P t₂).extExchangeMatrix (Pl t₂).extExchangeMatrix := by
  obtain ⟨t₁, ht₁⟩ := hA
  obtain ⟨L₁, hL₁⟩ := exists_labelledTriangulation_matrix_eq hn (hP.1 t₁).2 ht₁
  obtain ⟨Pl, hPl, h₁, hpp⟩ := hP.exists_pluckerPattern_of_principalPart_eq_typeA hL₁.symm
  obtain ⟨t₂, L₂, h₂, hfan⟩ := TypeA.IsSeedPattern.exists_pluckerSeed_triangulation_eq hPl h₁
    (isTriangulation_fanTriangulation (m := n + 3) (by omega))
  refine ⟨t₁, t₂, L₁, Pl, hPl, h₁, hpp, ?_⟩
  rw [h₂]
  exact zSpanCondition_of_span_eq_top (L₂.span_range_extMatrix_eq_top hfan) _

/-- **Seed patterns of type `A_n` are of finite type**. No condition is imposed on the frozen
rows or on the number of frozen variables. -/
@[cluster_algebras "thm_type_A_finite"]
theorem IsSeedPattern.isFiniteType_of_typeA [CharZero K] (hn : 1 ≤ n) (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hA : IsPatternOfType hmn P [DynkinSymbol.A n hn]) : IsFiniteType P := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : CharZero (pluckerField K n) :=
    charZero_of_injective_algebraMap (algebraMap K (pluckerField K n)).injective
  obtain ⟨t₁, t₂, L₁, Pl, hPl, h₁, hpp, hZ⟩ := hP.exists_pluckerPattern_of_typeA hn hmn hA
  have := (TypeA.IsSeedPattern.isFiniteType_of_pluckerSeed hPl h₁).to_subtype
  let g : Set.range Pl → SeedData F m n := fun S => P S.2.choose
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨⟨Pl t, t, rfl⟩, hPl.eq_of_eq_of_zSpanCondition (le_two_mul_add_three n) hmn hP
    (hpp t₂) hZ (Set.mem_range.1 (⟨Pl t, t, rfl⟩ : Set.range Pl).2).choose_spec⟩

/-- Mutation in direction `k` changes the `k`-th cluster variable of a labeled seed. -/
private theorem IsLabeledSeed.seedMutation_extCluster_castLE_ne_typeA {hmn : n ≤ m}
    {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) (k : Fin n) :
    (ClusterAlgebras.seedMutation hmn S k).extCluster (Fin.castLE hmn k) ≠
      S.extCluster (Fin.castLE hmn k) := by
  classical
  simp only [ClusterAlgebras.seedMutation, Function.update_self]
  intro h
  set c := Fin.castLE hmn k
  set x := S.extCluster
  set B := S.extExchangeMatrix
  have hxc : x c ≠ 0 := hS.1.1.ne_zero c
  rw [div_eq_iff hxc] at h
  have hBc : B c k = 0 := hS.extExchangeMatrix_castLE_self hmn k
  let ep : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (B i k).toNat
  let en : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (-B i k).toNat
  have hmono : ∀ e : Fin m →₀ ℕ,
      MvPolynomial.aeval x (MvPolynomial.monomial e (1 : K)) = ∏ i, x i ^ e i := fun e => by
    rw [MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ fun i => pow_zero _]
  set f : MvPolynomial (Fin m) K := MvPolynomial.X c ^ 2 - MvPolynomial.monomial ep 1 -
    MvPolynomial.monomial en 1 with hfdef
  have hf : f ≠ 0 := by
    intro hf
    have h2 := congrArg (MvPolynomial.coeff (Finsupp.single c 2)) hf
    have hep : ep ≠ Finsupp.single c 2 := fun he => by
      have := congrArg (· c) he
      simp [ep, hBc] at this
    have hen : en ≠ Finsupp.single c 2 := fun he => by
      have := congrArg (· c) he
      simp [en, hBc] at this
    simp [f, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial, hep, hen] at h2
  apply hf
  refine (injective_iff_map_eq_zero _).1 hS.1.1 _ ?_
  rw [hfdef, map_sub, map_sub, hmono, hmono, map_pow, MvPolynomial.aeval_X]
  have hp : ∏ i, x i ^ ep i = exchangeMonomialPos x B k := by
    rw [exchangeMonomialPos_eq_prod]
    rfl
  have hn : ∏ i, x i ^ en i = exchangeMonomialNeg x B k := by
    rw [exchangeMonomialNeg_eq_prod]
    rfl
  rw [hp, hn]
  linear_combination -h

/-- Two labelled triangulations with the same triangulation give Plücker seeds representing the
same unlabeled seed. -/
private theorem LabelledTriangulation.sameUnlabeled_pluckerSeed_typeA (K : Type*) [Field K]
    {L L' : LabelledTriangulation n} (h : L.triangulation = L'.triangulation) :
    (pluckerSeed K L).SameUnlabeled (le_two_mul_add_three n) (pluckerSeed K L') := by
  classical
  have hmem : ∀ j, ∃ i, L.label i = L'.label j := fun j => by
    have h' : L'.label j ∈ L'.triangulation := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rw [← h] at h'
    simpa [LabelledTriangulation.triangulation] using h'
  choose f hf using hmem
  have hfinj : Function.Injective f := fun i j hij => L'.injective (by rw [← hf, ← hf, hij])
  set σ := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj)
  have hext : ∀ i, L'.extLabel i =
      L.extLabel (Equiv.Perm.extendMutable (le_two_mul_add_three n) σ i) := by
    intro i
    by_cases hi : (i : ℕ) < n
    · rw [Equiv.Perm.extendMutable_apply_of_lt _ _ hi, LabelledTriangulation.extLabel_castLE]
      change L'.extLabel i = L.label (f ⟨i, hi⟩)
      rw [hf]
      simp [LabelledTriangulation.extLabel, hi]
    · rw [Equiv.Perm.extendMutable_apply_of_le _ _ (not_lt.1 hi)]
      simp [LabelledTriangulation.extLabel, hi]
  refine ⟨σ, fun i => ?_, fun i j => ?_⟩
  · simp only [pluckerSeed, hext]
  · simp only [pluckerSeed, LabelledTriangulation.extMatrix, Matrix.of_apply, h, hext,
      Equiv.Perm.extendMutable_castLE]

/-- A labelling `χ` of the cluster variables of a seed pattern of type `A_n` by the diagonals,
compatible with flips and reaching every triangulation, is injective on the diagonals. -/
private theorem injOn_of_typeA_structure (hn : 1 ≤ n) {hmn : n ≤ m}
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    {Lt : RegularTree n → LabelledTriangulation n} {χ : Sym2 (ZMod (n + 3)) → F}
    (hχ : ∀ t i, cluster hmn (P t) i = χ ((Lt t).label i))
    (hflip : ∀ (k : Fin n) (t t' : RegularTree n), RegularTree.Adj k t t' →
      IsFlipReplacement (Lt t).triangulation ((Lt t).label k) ((Lt t').label k))
    (hiv : ∀ T : Finset (Sym2 (ZMod (n + 3))), IsTriangulation T →
      ∃ t, (Lt t).triangulation = T) :
    Set.InjOn χ {δ | IsDiagonal δ} := by
  have hm4 : 4 ≤ n + 3 := by omega
  have hlabel : ∀ (T : Finset (Sym2 (ZMod (n + 3)))) (t : RegularTree n),
      (Lt t).triangulation = T → ∀ δ ∈ T, ∃ i, (Lt t).label i = δ := by
    rintro T t rfl δ hδ
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hδ
    exact ⟨i, hi⟩
  intro δ hδ δ' hδ' heq
  by_contra hne
  by_cases hc : Cross δ δ'
  · obtain ⟨T, hTf⟩ := exists_isFlipReplacement_of_cross hδ hδ' hc
    obtain ⟨t, ht⟩ := hiv T hTf.1
    obtain ⟨k, hk⟩ := hlabel T t ht δ hTf.2.1
    obtain ⟨t', hadj⟩ := RegularTree.exists_adj t k
    have hrep := hflip k t t' hadj
    have hTt : IsTriangulation (Lt t).triangulation := ht ▸ hTf.1
    have hk' : (Lt t).label k ∈ (Lt t).triangulation :=
      Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have huniq : (Lt t').label k = δ' :=
      (IsTriangulation.existsUnique_isFlipReplacement hm4 hTt hk').unique hrep
        (by rw [hk, ht]; exact hTf)
    have e1 := hχ t k
    have e2 := hχ t' k
    rw [hk] at e1
    rw [huniq] at e2
    apply IsLabeledSeed.seedMutation_extCluster_castLE_ne_typeA (hP.1 t) k
    rw [← hP.2 k t t' hadj]
    exact (e2.trans (heq.symm.trans e1.symm) :)
  · obtain ⟨T, hT, hδT, hδ'T⟩ := exists_isTriangulation_mem_mem hδ hδ' hc
    obtain ⟨t, ht⟩ := hiv T hT
    obtain ⟨i, hi⟩ := hlabel T t ht δ hδT
    obtain ⟨i', hi'⟩ := hlabel T t ht δ' hδ'T
    have hii' : i ≠ i' := fun h => hne (by rw [← hi, ← hi', h])
    have e1 := hχ t i
    have e2 := hχ t i'
    rw [hi] at e1
    rw [hi'] at e2
    exact hii' (Fin.castLE_injective hmn ((hP.1 t).1.1.injective
      (e1.trans (heq.trans e2.symm) :)))

/-- **Cluster variables of type `A_n` are labelled by diagonals**. For a seed pattern `P` of
type `A_n` there are labelled triangulations `(T_t, λ_t)` of the `(n+3)`-gon, `t ∈ 𝕋ₙ`, and a
map `χ` from segments to `F`, injective on the diagonals, such that
(i) `x_{i;t} = χ(λ_t(i))`;
(ii) the exchange matrix of `P t` is `B(T_t, λ_t)`;
(iii) if `t —k— t'`, then `λ_{t'}(k)` is the replacement of `λ_t(k)` in `T_t`,
`T_{t'} = (T_t \ {λ_t(k)}) ∪ {λ_{t'}(k)}`, and `λ_{t'}(i) = λ_t(i)` for `i ≠ k`;
(iv) every triangulation is some `T_t`;
(v) if `T_t = T_{t'}`, then `P t` and `P t'` represent the same unlabeled seed. -/
@[cluster_algebras "lem_type_A_structure"]
theorem IsSeedPattern.exists_typeA_structure [CharZero K] (hn : 1 ≤ n) (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hA : IsPatternOfType hmn P [DynkinSymbol.A n hn]) :
    ∃ (Lt : RegularTree n → LabelledTriangulation n) (χ : Sym2 (ZMod (n + 3)) → F),
      Set.InjOn χ {δ | IsDiagonal δ} ∧
      (∀ t i, cluster hmn (P t) i = χ ((Lt t).label i)) ∧
      (∀ t, principalPart hmn (P t).extExchangeMatrix = (Lt t).matrix) ∧
      (∀ (k : Fin n) (t t' : RegularTree n), RegularTree.Adj k t t' →
        IsFlipReplacement (Lt t).triangulation ((Lt t).label k) ((Lt t').label k) ∧
        (Lt t').triangulation =
          flipTriangulation (Lt t).triangulation ((Lt t).label k) ((Lt t').label k) ∧
        (Lt t').label = Function.update (Lt t).label k ((Lt t').label k)) ∧
      (∀ T : Finset (Sym2 (ZMod (n + 3))), IsTriangulation T → ∃ t, (Lt t).triangulation = T) ∧
      ∀ t t', (Lt t).triangulation = (Lt t').triangulation →
        (P t).SameUnlabeled hmn (P t') := by
  classical
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : CharZero (pluckerField K n) :=
    charZero_of_injective_algebraMap (algebraMap K (pluckerField K n)).injective
  obtain ⟨t₁, t₂, L₁, Pl, hPl, h₁, hpp, hZ⟩ := hP.exists_pluckerPattern_of_typeA hn hmn hA
  choose Lt hLt hLtu using fun t => TypeA.IsSeedPattern.existsUnique_pluckerSeed hPl h₁ t
  have hcl : ∀ t i, cluster (le_two_mul_add_three n) (Pl t) i =
      pluckerVar K n ((Lt t).label i) := fun t i => by
    rw [hLt t]
    simp [cluster, pluckerSeed]
  have htransfer : ∀ t t' i j, (Lt t).label i = (Lt t').label j →
      cluster hmn (P t) i = cluster hmn (P t') j := fun t t' i j h =>
    hPl.cluster_eq_of_zSpanCondition (le_two_mul_add_three n) hmn hP (hpp t₂) hZ
      (by rw [hcl, hcl, h])
  have hiii : ∀ (k : Fin n) (t t' : RegularTree n), RegularTree.Adj k t t' →
      IsFlipReplacement (Lt t).triangulation ((Lt t).label k) ((Lt t').label k) ∧
      (Lt t').triangulation =
        flipTriangulation (Lt t).triangulation ((Lt t).label k) ((Lt t').label k) ∧
      (Lt t').label = Function.update (Lt t).label k ((Lt t').label k) := fun k t t' h =>
    TypeA.IsSeedPattern.isFlipReplacement_of_adj hPl h (hLt t) (hLt t')
  have hiv : ∀ T : Finset (Sym2 (ZMod (n + 3))), IsTriangulation T →
      ∃ t, (Lt t).triangulation = T := fun T hT => by
    obtain ⟨t, L, hL, hLT⟩ := TypeA.IsSeedPattern.exists_pluckerSeed_triangulation_eq hPl h₁ hT
    exact ⟨t, by rw [← hLtu t L hL, hLT]⟩
  set χ : Sym2 (ZMod (n + 3)) → F := fun δ =>
    if h : ∃ t i, (Lt t).label i = δ then cluster hmn (P h.choose) h.choose_spec.choose else 0
    with hχdef
  have hχ : ∀ t i, cluster hmn (P t) i = χ ((Lt t).label i) := fun t i => by
    have h : ∃ t' i', (Lt t').label i' = (Lt t).label i := ⟨t, i, rfl⟩
    rw [show χ ((Lt t).label i) = _ from dif_pos h]
    exact htransfer _ _ _ _ h.choose_spec.choose_spec.symm
  refine ⟨Lt, χ, injOn_of_typeA_structure hn hP hχ (fun k t t' h => (hiii k t t' h).1) hiv,
    hχ, fun t => by rw [← hpp t, hLt t]; rfl, hiii, hiv, fun t t' h => ?_⟩
  refine hPl.sameUnlabeled_of_zSpanCondition (le_two_mul_add_three n) hmn hP (hpp t₂) hZ ?_
  rw [hLt t, hLt t']
  exact LabelledTriangulation.sameUnlabeled_pluckerSeed_typeA K h

/-- The structure of a seed pattern of type `A_n` in the form the counts use: the cluster of
`P t`, as a set, is `χ(T_t)`. -/
private theorem IsSeedPattern.exists_clusterVariables_eq_image_typeA [CharZero K] (hn : 1 ≤ n)
    {hmn : n ≤ m} {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hA : IsPatternOfType hmn P [DynkinSymbol.A n hn]) :
    ∃ (Lt : RegularTree n → LabelledTriangulation n) (χ : Sym2 (ZMod (n + 3)) → F),
      Set.InjOn χ {δ | IsDiagonal δ} ∧
      (∀ t, clusterVariables hmn (P t) = χ '' ↑(Lt t).triangulation) ∧
      (∀ T : Finset (Sym2 (ZMod (n + 3))), IsTriangulation T → ∃ t, (Lt t).triangulation = T) ∧
      ∀ t t', (Lt t).triangulation = (Lt t').triangulation →
        (P t).SameUnlabeled hmn (P t') := by
  obtain ⟨Lt, χ, hinj, hχ, -, -, hiv, hv⟩ := hP.exists_typeA_structure hn hmn hA
  refine ⟨Lt, χ, hinj, fun t => ?_, hiv, hv⟩
  ext x
  simp only [clusterVariables, Set.mem_range, LabelledTriangulation.triangulation,
    Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, (hχ t i).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, hχ t i⟩

/-- The diagonals of a triangulation are diagonals. -/
private theorem IsTriangulation.coe_subset_setOf_isDiagonal_typeA {N : ℕ} [NeZero N]
    {T : Finset (Sym2 (ZMod N))} (hT : IsTriangulation T) :
    (↑T : Set (Sym2 (ZMod N))) ⊆ {δ | IsDiagonal δ} :=
  fun δ hδ => hT.isDiagonal δ hδ

/-- **The number of cluster variables in type `A_n`**: a seed pattern of type `A_n` has exactly
`n(n+3)/2` cluster variables. -/
@[cluster_algebras "prop_type_A_counts"]
theorem IsSeedPattern.encard_patternClusterVariables_of_typeA [CharZero K] (hn : 1 ≤ n)
    (hmn : n ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hA : IsPatternOfType hmn P [DynkinSymbol.A n hn]) :
    (patternClusterVariables hmn P).encard = (n * (n + 3) / 2 : ℕ) := by
  classical
  obtain ⟨Lt, χ, hinj, hcv, hiv, -⟩ := hP.exists_clusterVariables_eq_image_typeA hn hA
  have h : patternClusterVariables hmn P = χ '' {δ | IsDiagonal δ} := by
    ext x
    simp only [patternClusterVariables, Set.mem_iUnion, hcv]
    constructor
    · rintro ⟨t, δ, hδ, rfl⟩
      exact ⟨δ, (Lt t).isTriangulation.coe_subset_setOf_isDiagonal_typeA hδ, rfl⟩
    · rintro ⟨δ, hδ, rfl⟩
      obtain ⟨T, hT, hδT, -⟩ := exists_isTriangulation_mem_mem hδ hδ (not_cross_self δ)
      obtain ⟨t, ht⟩ := hiv T hT
      exact ⟨t, δ, by rw [ht]; exact hδT, rfl⟩
  have hd : {δ : Sym2 (ZMod (n + 3)) | IsDiagonal δ} =
      ↑(Finset.univ.filter fun δ : Sym2 (ZMod (n + 3)) => IsDiagonal δ) := by
    ext
    simp
  rw [h, hinj.encard_image, hd, Set.encard_coe_eq_coe_finsetCard,
    card_filter_isDiagonal (m := n + 3) (by omega), Nat.add_sub_cancel, Nat.mul_comm]

/-- **The number of clusters in type `A_n`**: a seed pattern of type `A_n` has exactly
`c_{n+1}` clusters. -/
@[cluster_algebras "prop_type_A_counts"]
theorem IsSeedPattern.encard_patternClusters_of_typeA [CharZero K] (hn : 1 ≤ n) (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hA : IsPatternOfType hmn P [DynkinSymbol.A n hn]) :
    (patternClusters hmn P).encard = catalanNumber (n + 1) := by
  obtain ⟨Lt, χ, hinj, hcv, hiv, -⟩ := hP.exists_clusterVariables_eq_image_typeA hn hA
  have h : patternClusters hmn P =
      (fun T : Finset (Sym2 (ZMod (n + 3))) => χ '' ↑T) '' {T | IsTriangulation T} := by
    ext X
    simp only [patternClusters, Set.mem_range, hcv, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, (Lt t).isTriangulation, rfl⟩
    · rintro ⟨T, hT, rfl⟩
      obtain ⟨t, ht⟩ := hiv T hT
      exact ⟨t, by rw [ht]⟩
  have hinj' : Set.InjOn (fun T : Finset (Sym2 (ZMod (n + 3))) => χ '' ↑T)
      {T | IsTriangulation T} := fun T hT T' hT' hTT' =>
    Finset.coe_injective ((hinj.image_eq_image_iff hT.coe_subset_setOf_isDiagonal_typeA
      hT'.coe_subset_setOf_isDiagonal_typeA).1 hTT')
  rw [h, hinj'.encard_image, encard_setOf_isTriangulation (m := n + 3) (by omega)]
  rfl

/-- **The number of clusters in type `A_n`, closed form**: `binom(2n+2, n+1)/(n+2)`. -/
@[cluster_algebras "prop_type_A_counts"]
theorem IsSeedPattern.encard_patternClusters_of_typeA_eq_centralBinom [CharZero K]
    (hn : 1 ≤ n) (hmn : n ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hA : IsPatternOfType hmn P [DynkinSymbol.A n hn]) :
    (patternClusters hmn P).encard = (Nat.centralBinom (n + 1) / (n + 2) : ℕ) := by
  rw [hP.encard_patternClusters_of_typeA hn hmn hA, catalanNumber, catalan_eq_centralBinom_div]

omit [Field F] in
/-- Representing the same unlabeled seed is an equivalence relation on the vertices of `𝕋ₙ`,
for any assignment of seeds. -/
@[cluster_algebras "lem_type_A_unlabeled_seeds"]
theorem equivalence_sameUnlabeled (hmn : n ≤ m) (P : RegularTree n → SeedData F m n) :
    Equivalence fun t t' => (P t).SameUnlabeled hmn (P t') :=
  ⟨fun t => SeedData.SameUnlabeled.refl hmn (P t), fun h => h.symm, fun h h' => h.trans h'⟩

/-- **The number of unlabeled seeds in type `A_n`.** For a seed pattern of type `A_n`, the
relation "`P t` and `P t'` represent the same unlabeled seed" has exactly `c_{n+1}` classes. -/
@[cluster_algebras "lem_type_A_unlabeled_seeds"]
theorem IsSeedPattern.encard_sameUnlabeled_classes_of_typeA [CharZero K] (hn : 1 ≤ n)
    (hmn : n ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hA : IsPatternOfType hmn P [DynkinSymbol.A n hn]) :
    (Set.range fun t => {t' | (P t).SameUnlabeled hmn (P t')}).encard = catalanNumber (n + 1) := by
  obtain ⟨Lt, χ, hinj, hcv, hiv, hv⟩ := hP.exists_clusterVariables_eq_image_typeA hn hA
  have hiff : ∀ t t', (P t).SameUnlabeled hmn (P t') ↔
      (Lt t').triangulation = (Lt t).triangulation := by
    refine fun t t' => ⟨fun ⟨σ, hx, _⟩ => ?_, fun h => hv t t' h.symm⟩
    have hc : clusterVariables hmn (P t') = clusterVariables hmn (P t) := by
      ext x
      simp only [clusterVariables, Set.mem_range, cluster, hx, Equiv.Perm.extendMutable_castLE]
      exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩, fun ⟨i, hi⟩ => ⟨σ.symm i, by simpa using hi⟩⟩
    rw [hcv, hcv] at hc
    exact Finset.coe_injective ((hinj.image_eq_image_iff
      (Lt t').isTriangulation.coe_subset_setOf_isDiagonal_typeA
      (Lt t).isTriangulation.coe_subset_setOf_isDiagonal_typeA).1 hc)
  set S : Finset (Sym2 (ZMod (n + 3))) → Set (RegularTree n) :=
    fun T => {t' | (Lt t').triangulation = T} with hSdef
  have h : (Set.range fun t => {t' | (P t).SameUnlabeled hmn (P t')}) =
      S '' {T | IsTriangulation T} := by
    ext X
    simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq, hiff, hSdef]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, (Lt t).isTriangulation, rfl⟩
    · rintro ⟨T, hT, rfl⟩
      obtain ⟨t, ht⟩ := hiv T hT
      exact ⟨t, by rw [ht]⟩
  have hinj' : Set.InjOn S {T | IsTriangulation T} := by
    intro T hT T' hT' hTT'
    obtain ⟨t, ht⟩ := hiv T hT
    have hmem : t ∈ S T := ht
    rw [hTT'] at hmem
    exact ht.symm.trans hmem
  rw [h, hinj'.encard_image, encard_setOf_isTriangulation (m := n + 3) (by omega)]
  rfl

/-- **The number of unlabeled seeds in type `A_n`, closed form**: `binom(2n+2, n+1)/(n+2)`. -/
@[cluster_algebras "lem_type_A_unlabeled_seeds"]
theorem IsSeedPattern.encard_sameUnlabeled_classes_of_typeA_eq_centralBinom [CharZero K]
    (hn : 1 ≤ n) (hmn : n ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hA : IsPatternOfType hmn P [DynkinSymbol.A n hn]) :
    (Set.range fun t => {t' | (P t).SameUnlabeled hmn (P t')}).encard =
      (Nat.centralBinom (n + 1) / (n + 2) : ℕ) := by
  rw [hP.encard_sameUnlabeled_classes_of_typeA hn hmn hA, catalanNumber,
    catalan_eq_centralBinom_div]

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Coefficients.DummyExtension
public import ClusterAlgebras.TypeE.Certificate
public import ClusterAlgebras.TypeE.CertificateData.E6Cert
public import ClusterAlgebras.TypeE.CertificateData.E6Ref
public import ClusterAlgebras.TypeE.CertificateData.E7Cert
public import ClusterAlgebras.TypeE.CertificateData.E7ECert
public import ClusterAlgebras.TypeE.CertificateData.E7Ref
public import ClusterAlgebras.TypeE.CertificateData.E8Cert
public import ClusterAlgebras.TypeE.CertificateData.E8Ref

/-!
# Seed patterns of types `E₆`, `E₇`, `E₈`

We prove that seed patterns of types `E₆`, `E₇` and `E₈` are of finite type and count their
cluster variables and clusters ([FWZ], Section 5.6 and the `E`-columns of the table of
Section 5.9). Type `E₈` is handled by an exchange certificate for the matrix of the triangulated
`2 × 4` grid quiver, which is a reference matrix for `E₈` and has rows spanning `ℤ⁸`. Types `E₆`
and `E₇` are of finite type because a pattern of type `E_n` extends, by one mutable vertex and
freezing, to a pattern of type `E_{n+1}`. Their counts come from certificates for the linear
orientations, and for `E₇` (whose exchange matrices are singular) also for one extra frozen row.

## Main definitions

* `ClusterAlgebras.matrixE8Grid`: the `8 × 8` matrix `B_{E₈}` of the triangulated grid quiver.
* `ClusterAlgebras.matrixLinearE n`: the linear orientation `B_{E_n}` of the `E_n` tree.
* `ClusterAlgebras.matrixLinearE7Ext`: the `8 × 7` matrix `B̃_{E₇}`.

## Main results

* `ClusterAlgebras.IsSeedPattern.isFiniteType_and_encard_E8`: patterns of type `E₈`.
* `ClusterAlgebras.IsSeedPattern.isFiniteType_of_principalPart_eq_submatrix`: finite type passes
  to a leading principal block.
* `ClusterAlgebras.IsSeedPattern.isFiniteType_of_isPatternOfType_E`: every seed pattern of type
  `E₆`, `E₇` or `E₈` is of finite type.
* `ClusterAlgebras.IsSeedPattern.encard_of_isPatternOfType_E6` (and `E7`, `E8`): the numbers of
  cluster variables and of clusters.

## Implementation notes

* Indices are `Fin`, so the vertex `i` of [FWZ] is `i - 1` here. In `matrixLinearE n` the arrows
  `i → i + 1`, `i ∈ [1, n - 2]`, and `3 → n` are the pairs `(i, i + 1)` with `i + 1 ≤ n - 2` and
  `(2, n - 1)`, that is the edge relation `dynkinERel n` of `C(E_n)`; the extra row of `B̃_{E₇}`
  is `e₇`, here the unit vector at `6`.
* The computational propositions (exchange certificates and reference matrices) are stated
  existentially and proved from the data in `ClusterAlgebras.TypeE.CertificateData`, checked by
  the kernel (`decide +kernel`, no `native_decide`) through
  `CertificateCheck.Raw.nonempty_exchangeCertificate` and `CertificateCheck.eq_orientMatrix`.
* The hypotheses "every seed pattern (of type `E_{n+1}`, or with a given exchange matrix) is of
  finite type" quantify over all fields in the universe of the field of the pattern in the
  conclusion, which is the universe of the field of rational functions over it that the proof
  of `IsSeedPattern.isFiniteType_of_principalPart_eq_submatrix` builds. They are discharged by
  `IsSeedPattern.isFiniteType_of_isPatternOfType_E`, which is universe-polymorphic.
* `IsSeedPattern.isFiniteType_of_principalPart_eq_submatrix` is stated for `n ≤ N` and without
  `n ≥ 1`; the hypothesis `1 ≤ n < N` of [FWZ] is not needed (for `n = N` the hypothesis applies
  directly, and a pattern of rank `0` has one seed).
* Freezing the vertices `n + 1, …, N` of the ambient seed and keeping all indices is the
  reindexing along the identity of the row indices, read as a reindexing map from `(m', n)` to
  `(m', N)`. Every seed of the frozen pattern is then the reindexing of a seed of the ambient
  pattern along this map, so its cluster variables are cluster variables of the ambient pattern;
  this is the case of the seed-subpattern argument that is needed, without the general notion of
  a seed subpattern.
* In `IsSeedPattern.isFiniteType_of_isPatternOfType_E_of_succ` the new vertex is the last index
  `n` of `Fin (n + 1)`, so that the exchange matrix of `Σ̄(t₁)` is the leading block, and the
  bijection to the indices of `C(E_{n+1})` is `σ` extended by the last index followed by the
  transposition of `n - 1` and `n`; the needed entries of `C(E_n)` and `C(E_{n+1})` are compared
  by a finite computation.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*.
-/

@[expose] public section

universe v

namespace ClusterAlgebras

open Matrix

/-! ### Type `E₈` -/

/-- The **`E₈` grid matrix** `B_{E₈}`: the exchange matrix of the triangulated `2 × 4` grid
quiver `T_{2,4}`, with vertices `0, …, 7`. -/
@[cluster_algebras "def_exc_E8_grid"]
def matrixE8Grid : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 1, 0, 0, 1, -1, 0, 0;
    -1, 0, 1, 0, 0, 1, -1, 0;
    0, -1, 0, 1, 0, 0, 1, -1;
    0, 0, -1, 0, 0, 0, 0, 1;
    -1, 0, 0, 0, 0, 1, 0, 0;
    1, -1, 0, 0, -1, 0, 1, 0;
    0, 1, -1, 0, 0, -1, 0, 1;
    0, 0, 1, -1, 0, 0, -1, 0]

/-- The matrix `V` of the `E₈` computation, a left inverse of `B_{E₈}`. -/
@[cluster_algebras "prop_exc_E8_computation"]
def matrixE8GridLeftInv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 0, -1, 0, -1, 0, -1, -1;
    0, 0, -1, -1, 0, 0, 0, -1;
    1, 1, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, -1, 0, 0, -1;
    1, 0, 0, 1, 0, 0, -1, 0;
    0, 0, -1, 0, 0, 0, -1, -1;
    1, 0, 0, 0, 1, 1, 0, 0;
    1, 1, 0, 1, 0, 1, 0, 0]

/-- **The `E₈` computation**, (a): `V B_{E₈}` is the identity matrix. -/
@[cluster_algebras "prop_exc_E8_computation"]
theorem matrixE8GridLeftInv_mul : matrixE8GridLeftInv * matrixE8Grid = 1 := by
  decide

/-- If `V B = 1` for integer (or any commutative ring) matrices, then the rows of `B` span the
whole free module: `v = (v V) B` is a combination of the rows of `B`. -/
private theorem span_range_eq_top_of_mul_eq_one {ι κ R : Type*} [Finite ι] [Fintype κ]
    [DecidableEq ι] [CommRing R] {V : Matrix ι κ R} {B : Matrix κ ι R} (h : V * B = 1) :
    Submodule.span R (Set.range B) = ⊤ := by
  have := Fintype.ofFinite ι
  refine Submodule.eq_top_iff'.2 fun v => ?_
  have hv : v = (v ᵥ* V) ᵥ* B := by rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
  rw [hv, Matrix.vecMul_eq_sum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- A skew-symmetric integer matrix is skew-symmetrizable, with skew-symmetrizing vector
`(1, …, 1)`. -/
private theorem skewSymmetrizable_of_transpose_eq_neg {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : Bᵀ = -B) : SkewSymmetrizable B := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun i j => ?_⟩
  have := congrFun (congrFun h j) i
  simp only [transpose_apply, neg_apply] at this
  simp [this]

/-- **The `E₈` computation**, (a): the rows of `B_{E₈}` span `ℤ⁸`. -/
@[cluster_algebras "prop_exc_E8_computation"]
theorem span_range_matrixE8Grid : Submodule.span ℤ (Set.range matrixE8Grid) = ⊤ :=
  span_range_eq_top_of_mul_eq_one matrixE8GridLeftInv_mul

/-- **The `E₈` computation**, (a): `B_{E₈}` is skew-symmetric. -/
@[cluster_algebras "prop_exc_E8_computation"]
theorem transpose_matrixE8Grid : matrixE8Gridᵀ = -matrixE8Grid := by
  decide

/-- **The `E₈` computation**, (b): there is an exchange certificate for `B_{E₈}` with `128`
variables and `25080` seeds. Checked by the kernel on the certificate data of
`ClusterAlgebras.TypeE.CertificateData.E8`. -/
@[cluster_algebras "prop_exc_E8_computation"]
theorem nonempty_exchangeCertificate_matrixE8Grid :
    Nonempty (ExchangeCertificate le_rfl matrixE8Grid 128 25080) := by
  have h : matrixE8Grid = CertificateData.E8.initMatrix := by
    ext i j
    revert i j
    decide +kernel
  rw [h]
  exact CertificateData.E8.nonempty_exchangeCertificate le_rfl

/-- **The `E₈` computation**, (c): `B_{E₈}` is a reference matrix for `E₈`. Checked by the kernel
(a mutation sequence of length at most `9` for each of the `2⁷` sign patterns on the `E₈`
tree, `ClusterAlgebras.TypeE.CertificateData.E8Ref`). -/
@[cluster_algebras "prop_exc_E8_computation"]
theorem isReferenceMatrix_matrixE8Grid :
    IsReferenceMatrix (.E 8 (by decide)) matrixE8Grid := by
  intro P hP hA
  obtain ⟨w, τ, h⟩ := CertificateData.E8Ref.exists_matrixMutationList_eq P hP hA
  have href : CertificateData.E8Ref.refMatrix = matrixE8Grid := by
    ext i j
    revert i j
    decide +kernel
  refine ⟨w, τ, ?_⟩
  rw [relabelMatrix_self]
  exact h.trans (congrArg (fun B => Matrix.submatrix B τ τ) href)

variable {K : Type*} [Field K]

/-- **Seed patterns of type `E₈`**: every seed pattern of type `E₈` is of finite type, has
exactly `128` cluster variables, and has exactly `25080` clusters. -/
@[cluster_algebras "lem_exc_E8"]
theorem IsSeedPattern.isFiniteType_and_encard_E8 [CharZero K] {F : Type*} [Field F]
    [Algebra K F] {m : ℕ} (hmn : 8 ≤ m) {P : RegularTree 8 → SeedData F m 8}
    (hP : IsSeedPattern K hmn P) (hX : IsPatternOfType hmn P [.E 8 (by decide)]) :
    IsFiniteType P ∧ (patternClusterVariables hmn P).encard = 128 ∧
      (patternClusters hmn P).encard = 25080 := by
  obtain ⟨C⟩ := nonempty_exchangeCertificate_matrixE8Grid
  exact ExchangeCertificate.isFiniteType_and_encard_of_isPatternOfType
    (skewSymmetrizable_of_transpose_eq_neg transpose_matrixE8Grid) isReferenceMatrix_matrixE8Grid
    le_rfl rfl span_range_matrixE8Grid C C hmn hP hX

/-! ### Types `E₆` and `E₇` inside type `E₈` -/

/-- **Finite type passes to a leading principal block.** Let `C` be a skew-symmetrizable `N × N`
integer matrix such that every seed pattern of rank `N` (over `K`, in a field in the universe
of `F`) in which `C` is the exchange matrix of some seed is of finite type. If the exchange
matrix of `Σ̄(t₁)`, for a seed pattern `Σ̄` of rank `n ≤ N`, is the leading `n × n` block
`(cᵢⱼ)_{i,j ∈ [1,n]}` of `C`, then `Σ̄` is of finite type. FWZ assume `1 ≤ n < N`. -/
@[cluster_algebras "lem_exc_extension_finite"]
theorem IsSeedPattern.isFiniteType_of_principalPart_eq_submatrix [CharZero K] {n N : ℕ}
    (hnN : n ≤ N) {C : Matrix (Fin N) (Fin N) ℤ} (hC : SkewSymmetrizable C)
    (hfin : ∀ (F' : Type v) [Field F'] [Algebra K F'] (m' : ℕ) (hm' : N ≤ m')
      (P' : RegularTree N → SeedData F' m' N), IsSeedPattern K hm' P' →
        (∃ t, principalPart hm' (P' t).extExchangeMatrix = C) → IsFiniteType P')
    {F : Type v} [Field F] [Algebra K F] {m : ℕ} (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t₁ : RegularTree n}
    (ht₁ : principalPart hmn (P t₁).extExchangeMatrix =
      C.submatrix (Fin.castLE hnN) (Fin.castLE hnN)) :
    IsFiniteType P := by
  classical
  set d := N - n
  have hN : N ≤ m + d := by omega
  have h' : n ≤ m + d := hmn.trans (Nat.le_add_right m d)
  set B := (P t₁).extExchangeMatrix
  let F' := FractionRing (MvPolynomial (Fin d) F)
  let z : Fin d → F' := fun i => algebraMap (MvPolynomial (Fin d) F) F' (MvPolynomial.X i)
  have hz : IsFreeGeneratingTuple F z := isFreeGeneratingTuple_X F
  have hlab := IsLabeledSeed.extendDummy (K := K) (F' := F') hmn h' (hP.1 t₁) hz.1 hz.2
  let Ct : Matrix (Fin (m + d)) (Fin N) ℤ := Matrix.of fun p j =>
    if hp : (p : ℕ) < N then C ⟨p, hp⟩ j
    else if hj : (j : ℕ) < n then B ⟨p - d, by omega⟩ ⟨j, hj⟩ else 0
  have hCt : principalPart hN Ct = C := by
    ext i j
    simp [Ct, principalPart]
  let S' : SeedData F' (m + d) N := ⟨Fin.append (algebraMap F F' ∘ (P t₁).extCluster) z, Ct⟩
  have hS' : IsLabeledSeed K hN S' := ⟨hlab.1, (hCt ▸ hC : SkewSymmetrizable (principalPart hN Ct))⟩
  obtain ⟨P', hP', hP't⟩ := exists_isSeedPattern (K := K) hN RegularTree.root hS'
  have hfinP' : IsFiniteType P' := hfin F' (m + d) hN P' hP' ⟨.root, hP't ▸ hCt⟩
  let r : ReindexingMap (m + d) n (m + d) N :=
    ⟨id, Function.injective_id, fun _ hp => hp.trans_le hnN⟩
  have hr : ∀ B' : Matrix (Fin (m + d)) (Fin N) ℤ, r.IsClosedFor h' B' :=
    ReindexingMap.isClosedFor_of_surjective Function.surjective_id h'
  have hS₀ : IsLabeledSeed K h' (S'.reindex h' r) := ⟨hS'.1, hS'.2.matrixReindex hN h' r⟩
  obtain ⟨Q, hQ, hQt⟩ := exists_isSeedPattern (K := K) h' t₁ hS₀
  have hsub : ∀ u, ∃ u', Q u = (P' u').reindex h' r := by
    intro u
    obtain ⟨u', hu'⟩ := hP'.seedMutationSeq_mem_range hN .root
      ((t₁.word.reverse ++ u.word).map (r.col h'))
    refine ⟨u', ?_⟩
    rw [hQ.apply_eq_seedMutationSeq h' t₁ u, hQt, ← hP't, seedMutationSeq_reindex hN h' _ (hr _),
      hu']
  have hfinQ : (patternClusterVariables h' Q).Finite := by
    refine (hfinP'.finite_iUnion_clusterVariables hN).subset ?_
    rintro _ ⟨_, ⟨u, rfl⟩, ⟨p, rfl⟩⟩
    obtain ⟨u', hu'⟩ := hsub u
    refine Set.mem_iUnion.2 ⟨u', r.col h' p, ?_⟩
    rw [hu']
    rfl
  have hB : principalPart h' (Q t₁).extExchangeMatrix =
      principalPart hmn (P t₁).extExchangeMatrix := by
    rw [hQt, ht₁]
    ext i j
    simp only [principalPart, submatrix_apply, SeedData.reindex_extExchangeMatrix,
      matrixReindex_apply, S', Ct, r, of_apply]
    rw [dif_pos (by simp; omega)]
    rfl
  have hZ : ZSpanCondition (P t₁).extExchangeMatrix (Q t₁).extExchangeMatrix := by
    intro i
    by_cases hi : (i : ℕ) < n
    · refine Submodule.subset_span ⟨⟨i, by omega⟩, ?_⟩
      ext j
      simp only [hQt, SeedData.reindex_extExchangeMatrix, matrixReindex_apply, S', Ct, r,
        of_apply]
      rw [dif_pos (by simp; omega)]
      exact (congrFun (congrFun ht₁ ⟨i, hi⟩) j).symm
    · refine Submodule.subset_span ⟨⟨i + d, by omega⟩, ?_⟩
      ext j
      simp only [hQt, SeedData.reindex_extExchangeMatrix, matrixReindex_apply, S', Ct, r,
        of_apply]
      rw [dif_neg (by simp; omega), dif_pos (by simp)]
      congr 1
      ext
      simp
  rw [hP.isFiniteType_iff hmn]
  exact finite_patternClusterVariables_of_cluster_eq h' hmn
    (hQ.cluster_eq_of_cluster_eq_of_zSpanCondition h' hmn hP hB hZ) hfinQ

/-- A matrix is of type `[X]` exactly when it is a simultaneous permutation of `C(X)`. -/
private theorem isOfDynkinType_singleton_iff {k : ℕ} {A : Matrix (Fin k) (Fin k) ℤ}
    {X : DynkinSymbol} :
    IsOfDynkinType A [X] ↔ ∃ σ : Fin k ≃ Fin X.rank, ∀ i j, A i j = X.cartan (σ i) (σ j) :=
  ⟨fun ⟨σ, h⟩ => ⟨σ, fun i j => (h i j).trans (DynkinSymbol.listCartan_singleton_apply X _ _)⟩,
    fun ⟨σ, h⟩ => ⟨σ, fun i j =>
      (h i j).trans (DynkinSymbol.listCartan_singleton_apply X _ _).symm⟩⟩

/-- For `n ∈ {6, 7}`, the transposition of `n - 1` and `n` maps the edges of `E_n`, read in
`Fin (n + 1)`, onto the edges of `E_{n+1}` not containing `n - 1`. -/
private theorem cartanE_succ_swap_castSucc {n : ℕ} (hn : n = 6 ∨ n = 7) (a b : Fin n) :
    cartanE (n + 1) (Equiv.swap ⟨n - 1, by omega⟩ (Fin.last n) a.castSucc)
      (Equiv.swap ⟨n - 1, by omega⟩ (Fin.last n) b.castSucc) = cartanE n a b := by
  rcases hn with rfl | rfl <;> revert a b <;> decide

/-- For `n ∈ {6, 7}`, the vertex `n - 1` of `E_{n+1}` is a leaf joined only to `n - 2`. -/
private theorem cartanE_succ_swap_last {n : ℕ} (hn : n = 6 ∨ n = 7) (b : Fin n) :
    cartanE (n + 1) (Equiv.swap ⟨n - 1, by omega⟩ (Fin.last n) (Fin.last n))
      (Equiv.swap ⟨n - 1, by omega⟩ (Fin.last n) b.castSucc) =
        if (b : ℕ) = n - 2 then -1 else 0 := by
  rcases hn with rfl | rfl <;> revert b <;> decide

/-- For `n ∈ {6, 7}`, the vertex `n - 1` of `E_{n+1}` is a leaf joined only to `n - 2`. -/
private theorem cartanE_succ_swap_castSucc_last {n : ℕ} (hn : n = 6 ∨ n = 7) (a : Fin n) :
    cartanE (n + 1) (Equiv.swap ⟨n - 1, by omega⟩ (Fin.last n) a.castSucc)
      (Equiv.swap ⟨n - 1, by omega⟩ (Fin.last n) (Fin.last n)) =
        if (a : ℕ) = n - 2 then -1 else 0 := by
  rcases hn with rfl | rfl <;> revert a <;> decide

/-- **From type `E_{n+1}` to type `E_n`**, `n ∈ {6, 7}`: if every seed pattern of type
`E_{n+1}` (over `K`, in a field in the universe of `F`) is of finite type, then every seed
pattern of type `E_n` is of finite type. -/
@[cluster_algebras "lem_exc_E_step"]
theorem IsSeedPattern.isFiniteType_of_isPatternOfType_E_of_succ [CharZero K] {n : ℕ}
    (hn : n = 6 ∨ n = 7)
    (hfin : ∀ (F' : Type v) [Field F'] [Algebra K F'] (m' : ℕ) (hm' : n + 1 ≤ m')
      (P' : RegularTree (n + 1) → SeedData F' m' (n + 1)), IsSeedPattern K hm' P' →
        IsPatternOfType hm' P' [.E (n + 1) (by omega)] → IsFiniteType P')
    {F : Type v} [Field F] [Algebra K F] {m : ℕ} (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hX : IsPatternOfType hmn P [.E n (by omega)]) :
    IsFiniteType P := by
  classical
  obtain ⟨t₁, ht₁⟩ := hX
  set B := principalPart hmn (P t₁).extExchangeMatrix
  have hskew : ∀ i j, B i j = -B j i := (hP.1 t₁).2.eq_neg_of_isOfDynkinType_E ht₁
  obtain ⟨σ, hσ⟩ := isOfDynkinType_singleton_iff.1 ht₁
  change Fin n ≃ Fin n at σ
  change ∀ i j, cartanCounterpart B i j = cartanE n (σ i) (σ j) at hσ
  set u : Fin n := σ.symm ⟨n - 2, by omega⟩ with hu
  let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j =>
    if hi : (i : ℕ) < n then
      if hj : (j : ℕ) < n then B ⟨i, hi⟩ ⟨j, hj⟩ else if (⟨i, hi⟩ : Fin n) = u then -1 else 0
    else if hj : (j : ℕ) < n then (if (⟨j, hj⟩ : Fin n) = u then 1 else 0) else 0
  have hC₁ : ∀ a b : Fin n, C a.castSucc b.castSucc = B a b :=
    fun a b => by simp [C]
  have hC₂ : ∀ b : Fin n, C (Fin.last n) b.castSucc = if b = u then 1 else 0 :=
    fun b => by simp [C]
  have hC₃ : ∀ a : Fin n, C a.castSucc (Fin.last n) = if a = u then -1 else 0 :=
    fun a => by simp [C]
  have hC₄ : C (Fin.last n) (Fin.last n) = 0 := by simp [C]
  have hCs : ∀ i j, C i j = -C j i := by
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    · rw [hC₄, neg_zero]
    · rw [hC₂, hC₃]
      split_ifs <;> simp
    · rw [hC₂, hC₃]
      split_ifs <;> simp
    · rw [hC₁, hC₁, hskew]
  have hCss : SkewSymmetrizable C :=
    ⟨fun _ => 1, fun _ => one_pos, fun i j => by simp [hCs i j]⟩
  have hsub : principalPart hmn (P t₁).extExchangeMatrix =
      C.submatrix (Fin.castLE (Nat.le_succ n)) (Fin.castLE (Nat.le_succ n)) := by
    ext i j
    simp [C, B]
  let τ : Fin (n + 1) ≃ Fin (n + 1) :=
    ((finSuccEquivLast.trans σ.optionCongr).trans finSuccEquivLast.symm).trans
      (Equiv.swap ⟨n - 1, by omega⟩ (Fin.last n))
  have hτ₁ : ∀ a : Fin n,
      τ a.castSucc = Equiv.swap ⟨n - 1, by omega⟩ (Fin.last n) (σ a).castSucc :=
    fun a => by simp [τ]
  have hτ₂ : τ (Fin.last n) = Equiv.swap ⟨n - 1, by omega⟩ (Fin.last n) (Fin.last n) := by
    simp [τ]
  have hiff : ∀ b : Fin n, b = u ↔ ((σ b : Fin n) : ℕ) = n - 2 := by
    intro b
    rw [hu, Equiv.eq_symm_apply, Fin.ext_iff]
  have hCtype : IsOfDynkinType (cartanCounterpart C) [.E (n + 1) (by omega)] := by
    refine isOfDynkinType_singleton_iff.2 ⟨τ, fun i j => ?_⟩
    change cartanCounterpart C i j = cartanE (n + 1) (τ i) (τ j)
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    · simp [cartanCounterpart, hτ₂, cartanE, cartanOfGraph]
    · rename_i b
      rw [hτ₂, hτ₁, cartanE_succ_swap_last hn]
      simp only [cartanCounterpart, of_apply, hC₂, (Fin.castSucc_lt_last b).ne', if_false]
      by_cases hb : b = u
      · simp [if_pos hb, if_pos ((hiff b).1 hb)]
      · simp [if_neg hb, if_neg (fun h => hb ((hiff b).2 h))]
    · rename_i a
      rw [hτ₂, hτ₁, cartanE_succ_swap_castSucc_last hn]
      simp only [cartanCounterpart, of_apply, hC₃, (Fin.castSucc_lt_last a).ne, if_false]
      by_cases ha : a = u
      · simp [if_pos ha, if_pos ((hiff a).1 ha)]
      · simp [if_neg ha, if_neg (fun h => ha ((hiff a).2 h))]
    · rename_i a b
      rw [hτ₁, hτ₁, cartanE_succ_swap_castSucc hn, ← hσ]
      simp only [cartanCounterpart, of_apply, hC₁, Fin.castSucc_inj]
  exact hP.isFiniteType_of_principalPart_eq_submatrix (Nat.le_succ n) hCss
    (fun F' _ _ m' hm' P' hP' ⟨t, ht⟩ => hfin F' m' hm' P' hP' ⟨t, by rw [ht]; exact hCtype⟩)
    hmn hsub

/-- **Seed patterns of types `E₆`, `E₇`, `E₈` are of finite type.** -/
@[cluster_algebras "thm_type_E_finite"]
theorem IsSeedPattern.isFiniteType_of_isPatternOfType_E [CharZero K] {F : Type*} [Field F]
    [Algebra K F] {n m : ℕ} (hn : 6 ≤ n ∧ n ≤ 8) (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hX : IsPatternOfType hmn P [.E n hn]) :
    IsFiniteType P := by
  obtain rfl | rfl | rfl : n = 6 ∨ n = 7 ∨ n = 8 := by omega
  · exact hP.isFiniteType_of_isPatternOfType_E_of_succ (Or.inl rfl)
      (fun _ _ _ _ hm' _ hP' hX' => hP'.isFiniteType_of_isPatternOfType_E_of_succ (Or.inr rfl)
        (fun _ _ _ _ hm'' _ hP'' hX'' => (hP''.isFiniteType_and_encard_E8 hm'' hX'').1) hm' hX')
      hmn hX
  · exact hP.isFiniteType_of_isPatternOfType_E_of_succ (Or.inr rfl)
      (fun _ _ _ _ hm' _ hP' hX' => (hP'.isFiniteType_and_encard_E8 hm' hX').1) hmn hX
  · exact (hP.isFiniteType_and_encard_E8 hmn hX).1

/-! ### Counting in types `E₆` and `E₇` -/

/-- **The linear `E_n` matrix** `B_{E_n}`: `b_{i,i+1} = 1`, `b_{i+1,i} = -1` for
`i ∈ [1, n - 2]`, `b_{3n} = 1`, `b_{n3} = -1`, and all other entries `0`, the matrix of the
orientation of the `E_n` tree with arrows `i → i + 1` and `3 → n`. Here the arrows are the
pairs related by `dynkinERel n`. FWZ use `n ∈ {6, 7}`; the matrix is defined for every
`n`. -/
@[cluster_algebras "def_exc_E6_E7_matrices"]
def matrixLinearE (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if dynkinERel n i j then 1 else if dynkinERel n j i then -1 else 0

/-- **The extended `E₇` matrix** `B̃_{E₇}`: the `8 × 7` matrix whose first seven rows are those of
`B_{E₇}` and whose eighth row is `(0, 0, 0, 0, 0, 0, 1)`. -/
@[cluster_algebras "def_exc_E6_E7_matrices"]
def matrixLinearE7Ext : Matrix (Fin 8) (Fin 7) ℤ :=
  Matrix.of fun i j =>
    if h : (i : ℕ) < 7 then matrixLinearE 7 ⟨i, h⟩ j else if (j : ℕ) = 6 then 1 else 0

/-- **The `E₆` computation**, (a): the rows of `B_{E₆}` span `ℤ⁶`. -/
@[cluster_algebras "prop_exc_E6_computation"]
theorem span_range_matrixLinearE_six : Submodule.span ℤ (Set.range (matrixLinearE 6)) = ⊤ :=
  span_range_eq_top_of_mul_eq_one (V := !![0, -1, 0, 0, 0, -1; 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -1; 0, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1; 1, 0, 1, 0, 1, 0]) (by decide)

/-- **The `E₆` computation**, (b): there is an exchange certificate for `B_{E₆}` with `42`
variables and `833` seeds. Checked by the kernel on the certificate data of
`ClusterAlgebras.TypeE.CertificateData.E6`. -/
@[cluster_algebras "prop_exc_E6_computation"]
theorem nonempty_exchangeCertificate_matrixLinearE_six :
    Nonempty (ExchangeCertificate le_rfl (matrixLinearE 6) 42 833) := by
  have h : matrixLinearE 6 = CertificateData.E6.initMatrix := by
    ext i j
    revert i j
    decide +kernel
  rw [h]
  exact CertificateData.E6.nonempty_exchangeCertificate le_rfl

/-- **The `E₆` computation**, (c): `B_{E₆}` is a reference matrix for `E₆`. Checked by the kernel
(`ClusterAlgebras.TypeE.CertificateData.E6Ref`). -/
@[cluster_algebras "prop_exc_E6_computation"]
theorem isReferenceMatrix_matrixLinearE_six :
    IsReferenceMatrix (.E 6 (by decide)) (matrixLinearE 6) := by
  intro P hP hA
  obtain ⟨w, τ, h⟩ := CertificateData.E6Ref.exists_matrixMutationList_eq P hP hA
  have href : CertificateData.E6Ref.refMatrix = matrixLinearE 6 := by
    ext i j
    revert i j
    decide +kernel
  refine ⟨w, τ, ?_⟩
  rw [relabelMatrix_self]
  exact h.trans (congrArg (fun B => Matrix.submatrix B τ τ) href)

/-- **The `E₇` computation**, (a): the rows of `B̃_{E₇}` span `ℤ⁷`. -/
@[cluster_algebras "prop_exc_E7_computation"]
theorem span_range_matrixLinearE7Ext : Submodule.span ℤ (Set.range matrixLinearE7Ext) = ⊤ :=
  span_range_eq_top_of_mul_eq_one (V := !![0, -1, 0, 0, 0, 0, -1, 0;
    1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, -1, 0; 1, 0, 1, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, -1, 0, 0; 1, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 0, 0, 0, 0, 1]) (by decide)

/-- **The `E₇` computation**, (b): there are exchange certificates for `B_{E₇}` and for `B̃_{E₇}`,
each with `70` variables and `4160` seeds. Checked by the kernel on the certificate data of
`ClusterAlgebras.TypeE.CertificateData.E7` and `.E7E`. -/
@[cluster_algebras "prop_exc_E7_computation"]
theorem nonempty_exchangeCertificate_matrixLinearE_seven :
    Nonempty (ExchangeCertificate le_rfl (matrixLinearE 7) 70 4160) ∧
      Nonempty (ExchangeCertificate (by decide : 7 ≤ 8) matrixLinearE7Ext 70 4160) := by
  have h₁ : matrixLinearE 7 = CertificateData.E7.initMatrix := by
    ext i j
    revert i j
    decide +kernel
  have h₂ : matrixLinearE7Ext = CertificateData.E7E.initMatrix := by
    ext i j
    revert i j
    decide +kernel
  rw [h₁, h₂]
  exact ⟨CertificateData.E7.nonempty_exchangeCertificate le_rfl,
    CertificateData.E7E.nonempty_exchangeCertificate _⟩

/-- **The `E₇` computation**, (c): `B_{E₇}` is a reference matrix for `E₇`. Checked by the kernel
(`ClusterAlgebras.TypeE.CertificateData.E7Ref`). -/
@[cluster_algebras "prop_exc_E7_computation"]
theorem isReferenceMatrix_matrixLinearE_seven :
    IsReferenceMatrix (.E 7 (by decide)) (matrixLinearE 7) := by
  intro P hP hA
  obtain ⟨w, τ, h⟩ := CertificateData.E7Ref.exists_matrixMutationList_eq P hP hA
  have href : CertificateData.E7Ref.refMatrix = matrixLinearE 7 := by
    ext i j
    revert i j
    decide +kernel
  refine ⟨w, τ, ?_⟩
  rw [relabelMatrix_self]
  exact h.trans (congrArg (fun B => Matrix.submatrix B τ τ) href)

variable {F : Type*} [Field F] [Algebra K F] {m : ℕ}

/-- **Cluster variables and clusters in type `E₆`**: a seed pattern of type `E₆` has `42`
cluster variables and `833` clusters. -/
@[cluster_algebras "prop_type_E_counts"]
theorem IsSeedPattern.encard_of_isPatternOfType_E6 [CharZero K] (hmn : 6 ≤ m)
    {P : RegularTree 6 → SeedData F m 6} (hP : IsSeedPattern K hmn P)
    (hX : IsPatternOfType hmn P [.E 6 (by decide)]) :
    (patternClusterVariables hmn P).encard = 42 ∧ (patternClusters hmn P).encard = 833 := by
  obtain ⟨C⟩ := nonempty_exchangeCertificate_matrixLinearE_six
  exact (ExchangeCertificate.isFiniteType_and_encard_of_isPatternOfType
    (skewSymmetrizable_of_transpose_eq_neg (by decide)) isReferenceMatrix_matrixLinearE_six
    le_rfl rfl span_range_matrixLinearE_six C C hmn hP hX).2

/-- **Cluster variables and clusters in type `E₇`**: a seed pattern of type `E₇` has `70`
cluster variables and `4160` clusters. -/
@[cluster_algebras "prop_type_E_counts"]
theorem IsSeedPattern.encard_of_isPatternOfType_E7 [CharZero K] (hmn : 7 ≤ m)
    {P : RegularTree 7 → SeedData F m 7} (hP : IsSeedPattern K hmn P)
    (hX : IsPatternOfType hmn P [.E 7 (by decide)]) :
    (patternClusterVariables hmn P).encard = 70 ∧ (patternClusters hmn P).encard = 4160 := by
  obtain ⟨⟨C₀⟩, ⟨C₁⟩⟩ := nonempty_exchangeCertificate_matrixLinearE_seven
  exact (ExchangeCertificate.isFiniteType_and_encard_of_isPatternOfType
    (skewSymmetrizable_of_transpose_eq_neg (by decide)) isReferenceMatrix_matrixLinearE_seven
    (by decide : 7 ≤ 8) (by decide) span_range_matrixLinearE7Ext C₀ C₁ hmn hP hX).2

/-- **Cluster variables and clusters in type `E₈`**: a seed pattern of type `E₈` has `128`
cluster variables and `25080` clusters. -/
@[cluster_algebras "prop_type_E_counts"]
theorem IsSeedPattern.encard_of_isPatternOfType_E8 [CharZero K] (hmn : 8 ≤ m)
    {P : RegularTree 8 → SeedData F m 8} (hP : IsSeedPattern K hmn P)
    (hX : IsPatternOfType hmn P [.E 8 (by decide)]) :
    (patternClusterVariables hmn P).encard = 128 ∧ (patternClusters hmn P).encard = 25080 :=
  (hP.isFiniteType_and_encard_E8 hmn hX).2

end ClusterAlgebras

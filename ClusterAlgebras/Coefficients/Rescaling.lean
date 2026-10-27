/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Tropical.A2PeriodFive
public import ClusterAlgebras.YPattern.YHat
public import ClusterAlgebras.Coefficients.PatternSemifield
public import ClusterAlgebras.Coefficients.TripleMatrix

/-!
# Rescaling a seed pattern

Let `Σ` be a seed pattern of rank `n` in a field `F` over `K`, with `Σ(t) = (x̃(t), B̃(t))`,
`x̃(t) = (x_{1;t}, …, x_{m;t})`, `ŷ(t)` its `ŷ`-tuple and `B(t)` the principal part of `B̃(t)`.
Fix a vertex `t₀` and put `x̃ = x̃(t₀)`; every `x_{i;t}` and every `ŷ_{k;t}` lies in the
universal semifield `ℚ_sf(x̃)`. Let `x̄ = (x̄₁, …, x̄_{m̄})` be a free generating tuple of a second
field `F̄` over `K`, let `T̄ = Trop(q̄_{n+1}, …, q̄_{m̄})`, and let `ε̄ : T̄ → F̄` be the monomial
evaluation at the frozen variables `x̄_{n+1}, …, x̄_{m̄}`.

Given semifield homomorphisms `φ : ℚ_sf(x̃) → T̄` and `ψ : ℚ_sf(x̃) → ℚ_sf(x̄)` with
`ψ(xᵢ) = x̄ᵢ ε̄(φ(xᵢ))` for `i ≤ n` and `ψ(xᵢ) = ε̄(φ(xᵢ))` for `i > n`, put
`x̄_{i;t} = ψ(x_{i;t}) / ε̄(φ(x_{i;t}))` and `ȳ_{k;t} = φ(ŷ_{k;t})`. The *rescaling theorem*
says that `t ↦ (x̄(t), ȳ(t), B(t))` is a labeled seed pattern of triples in `F̄`, with frozen
variables `x̄_{n+1}, …, x̄_{m̄}`.

The proof checks the edge condition one edge `t —k— t'` at a time. The exchange matrices
mutate because principal parts commute with mutation. Applying `φ` to the mutation rule for
the `ŷ`'s gives the tropical rule for the `ȳ`'s, `φ` preserving products, inverses and the
auxiliary addition. The cluster variables other than `x̄_{k;t}` do not move. For `x̄_{k;t}`,
applying `ψ` and `φ` to the exchange relation `x_{k;t} x_{k;t'} = M⁺ + M⁻`, and using
`M⁺ / M⁻ = ŷ_{k;t}`, gives the exchange relation of mutation of triples, with
`ε̄(ȳ / (ȳ ⊕ 1))` and `ε̄(1 / (ȳ ⊕ 1))` as coefficients. Finally the triple at `t₀` has
extended cluster `x̄`, so it is a labeled seed triple, and mutation preserves labeled seed
triples.

## Main results

* `ClusterAlgebras.IsSeedPattern.isTriplePattern_rescaling`: the rescaling theorem.
* `ClusterAlgebras.IsLabeledSeed.rescaling_seedMutation`: the edge condition, for one labeled
  seed `S` and its mutation `μₖ(S)`.
* `ClusterAlgebras.FZSemifieldHom.rescaling_cluster_seedMutation_self`: the rescaled exchange
  relation.
* `ClusterAlgebras.IsLabeledSeed.mutation_coeff_apply_yHat`: the rescaled coefficients mutate
  tropically.
* `ClusterAlgebras.IsTriplePattern.of_isSeedTriple`: a family of triples following mutation of
  triples along every edge, and a labeled seed triple at one vertex, is a pattern of triples.
* `ClusterAlgebras.IsFreeGeneratingTuple.algebraicIndependent_rat`: a free generating tuple of
  a field of characteristic zero is algebraically independent over `ℚ`.

## Implementation notes

* Indices start at `0`: the indices `i ∈ [1, n]` of [FWZ] are the `i : Fin m` of value below
  `n`, and the indices `i ∈ [n+1, m]` are those with `n ≤ i`. The tuples `x̄(t)` and `ȳ(t)` are
  indexed by `Fin n`, and the entry `x_{i;t}` for `i : Fin n` is the entry of `x̃(t)` in
  position `Fin.castLE hmn i`.
* The universal semifields `ℚ_sf(x̃)` and `ℚ_sf(x̄)` carry their semifield structures under the
  instance arguments `[CharZero F] [Fact (AlgebraicIndependent ℚ x̃)]` and
  `[CharZero F̄] [Fact (AlgebraicIndependent ℚ x̄)]`, which the types of `φ` and `ψ` need. They
  follow from the hypotheses of [FWZ]: a field over `K` of characteristic zero has
  characteristic zero (`Algebra.charZero_of_charZero`), and the extended cluster of a labeled
  seed and a free generating tuple are then algebraically independent over `ℚ`
  (`IsLabeledSeed.algebraicIndependent_rat`, `IsFreeGeneratingTuple.algebraicIndependent_rat`).
  Conversely `K` has characteristic zero as soon as `F` does, so the hypothesis that `K` has
  characteristic zero is not stated separately.
* The map `ε̄` of [FWZ] is the monomial evaluation `monomialEvaluation` at
  `(x̄_{n+1}, …, x̄_{m̄})`, a homomorphism into `F̄ˣ`. The statements use its value in `F̄`,
  `tropicalEval`, which is `monomialEvaluation` followed by the inclusion `F̄ˣ → F̄`
  (`coe_monomialEvaluation`) and needs no proof that the `x̄ᵢ` are nonzero.
* [FWZ] assumes `n ≥ 1`; nothing here uses it, so it is not assumed.
* An element `z` of `F` known to lie in `ℚ_sf(x̃)` is passed to `φ` and `ψ` as `⟨z, h⟩`. For the
  entries of `Σ(t)` the membership proofs are `IsSeedPattern.extCluster_mem_universalSemifield`
  and `IsSeedPattern.yHat_mem_universalSemifield`, the remark preceding Theorem 4.3.3 in
  [FWZ].
* The steps of the proof are stated for a single labeled seed `S` and an arbitrary `S'` with
  `S' = μₖ(S)`, the entries of both lying in an arbitrary `ℚ_sf(y)`; the theorem applies them to
  `S = Σ(t)` and `S' = Σ(t')` with `y = x̃(t₀)`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 4–5*, Section 4.3, Theorem 4.3.3.
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### Algebraic independence over `ℚ` -/

/-- A free generating tuple of a field `F` of characteristic zero over `K` is algebraically
independent over `ℚ`. -/
theorem IsFreeGeneratingTuple.algebraicIndependent_rat {K F : Type*} [Field K] [Field F]
    [Algebra K F] [CharZero F] {m : ℕ} {x : Fin m → F} (hx : IsFreeGeneratingTuple K x) :
    AlgebraicIndependent ℚ x :=
  haveI : CharZero K := (algebraMap K F).charZero
  hx.1.restrictScalars (algebraMap ℚ K).injective

/-! ### Patterns of triples from one labeled seed triple -/

/-- A family of triples on `𝕋ₙ` that follows mutation of triples along every edge, and is a
labeled seed triple at one vertex, is a labeled seed pattern of triples (step 2 of the proof of
the rescaling theorem): mutation preserves labeled seed triples. -/
theorem IsTriplePattern.of_isSeedTriple {K F' : Type*} [Field K] [CharZero K] [Field F']
    [Algebra K F'] {m' n : ℕ} (hm' : n ≤ m') {frozen : FrozenIndex m' n → F'}
    {Q : RegularTree n → SeedTriple F' m' n}
    (hQ : ∀ k t t', RegularTree.Adj k t t' → Q t' = (Q t).mutation frozen k)
    {t₀ : RegularTree n} (h₀ : IsSeedTriple K frozen (Q t₀)) : IsTriplePattern K frozen Q := by
  refine ⟨fun t => ?_, hQ⟩
  obtain ⟨d, s, κ, h0, hl, hs⟩ := RegularTree.exists_walk t₀ t
  have key : ∀ e : Fin (d + 1), IsSeedTriple K frozen (Q (s e)) := by
    intro e
    induction e using Fin.induction with
    | zero => rwa [h0]
    | succ e ih => rw [hQ _ _ _ (hs e)]; exact ih.mutation hm' _
  rw [← hl]
  exact key _

variable {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F'] {ι ι' : Type*}
  {y : ι → F} {y' : ι' → F'} [Fact (AlgebraicIndependent ℚ y)]
  [Fact (AlgebraicIndependent ℚ y')]

/-! ### Products of powers -/

section Products

variable {κ : Type*} [Fintype κ]
  (ψ : FZSemifieldHom (universalSemifield y) (universalSemifield y'))
  (φ : FZSemifieldHom (universalSemifield y) (TropicalSemifield κ)) {e : κ → F'}

/-- If `ψ(xᵢ) = zᵢ ε(φ(xᵢ))` for every `i`, with `ε` the evaluation at nonzero elements `eᵢ`, then
`ψ(∏ᵢ xᵢ ^ dᵢ) = (∏ᵢ zᵢ ^ dᵢ) ε(φ(∏ᵢ xᵢ ^ dᵢ))`. -/
theorem FZSemifieldHom.coe_apply_prod_pow_eq_mul_tropicalEval (he : ∀ i, e i ≠ 0) {α : Type*}
    [Fintype α] {x : α → F} (hx : ∀ i, x i ∈ universalSemifield y) {z : α → F'}
    (hz : ∀ i, (ψ ⟨x i, hx i⟩ : F') = z i * tropicalEval e (φ ⟨x i, hx i⟩)) (d : α → ℕ) :
    (ψ ⟨∏ i, x i ^ d i, prod_mem_universalSemifield fun i _ =>
        pow_mem_universalSemifield (hx i) (d i)⟩ : F') =
      (∏ i, z i ^ d i) * tropicalEval e (φ ⟨∏ i, x i ^ d i, prod_mem_universalSemifield
        fun i _ => pow_mem_universalSemifield (hx i) (d i)⟩) := by
  have h : (⟨∏ i, x i ^ d i, prod_mem_universalSemifield fun i _ =>
        pow_mem_universalSemifield (hx i) (d i)⟩ : universalSemifield y) =
      ∏ i, (⟨x i, hx i⟩ : universalSemifield y) ^ d i :=
    Subtype.ext (by rw [universalSemifield.coe_prod]; rfl)
  rw [ψ.coe_apply_prod_pow hx, h, map_prod, ← coe_monomialEvaluation e he, map_prod,
    Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, map_pow, Units.val_pow_eq_pow_val, coe_monomialEvaluation, hz, mul_pow]

end Products

/-! ### The exchange relation -/

section Exchange

variable {κ : Type*} [Fintype κ]
  (ψ : FZSemifieldHom (universalSemifield y) (universalSemifield y'))
  (φ : FZSemifieldHom (universalSemifield y) (TropicalSemifield κ)) {e : κ → F'} {m n : ℕ}

/-- **The rescaled exchange relation** (step 1(d) of the proof of the rescaling theorem). Let
`S' = μₖ(S)`, with all entries of `S` and `S'` in `ℚ_sf(y)`, and let `c`, `c'` be tuples with
`ψ(xᵢ) = cᵢ ε(φ(xᵢ))` and `ψ(x'ₖ) = c'ₖ ε(φ(x'ₖ))` for the cluster variables, and
`ψ(xᵢ) = ε(φ(xᵢ))` for the frozen variables. Then `c'ₖ` is given by the exchange relation of
mutation of triples for `(c, φ(ŷ), B)`, `B` the principal part of the matrix of `S`. -/
theorem FZSemifieldHom.rescaling_cluster_seedMutation_self (he : ∀ i, e i ≠ 0) (hmn : n ≤ m)
    {S S' : SeedData F m n} (k : Fin n) (hS' : S' = seedMutation hmn S k)
    (hx : ∀ i, S.extCluster i ∈ universalSemifield y)
    (hx' : ∀ i, S'.extCluster i ∈ universalSemifield y) (hy : yHat S k ∈ universalSemifield y)
    {c c' : Fin n → F'}
    (hc : ∀ i : Fin n, (ψ ⟨S.extCluster (Fin.castLE hmn i), hx _⟩ : F') =
      c i * tropicalEval e (φ ⟨S.extCluster (Fin.castLE hmn i), hx _⟩))
    (hc' : (ψ ⟨S'.extCluster (Fin.castLE hmn k), hx' _⟩ : F') =
      c' k * tropicalEval e (φ ⟨S'.extCluster (Fin.castLE hmn k), hx' _⟩))
    (hfrozen : ∀ i : Fin m, n ≤ (i : ℕ) →
      (ψ ⟨S.extCluster i, hx i⟩ : F') = tropicalEval e (φ ⟨S.extCluster i, hx i⟩)) :
    c' k = (tropicalEval e (φ ⟨yHat S k, hy⟩ / (φ ⟨yHat S k, hy⟩ + 1)) *
          exchangeMonomialPos c (principalPart hmn S.extExchangeMatrix) k +
        tropicalEval e (1 / (φ ⟨yHat S k, hy⟩ + 1)) *
          exchangeMonomialNeg c (principalPart hmn S.extExchangeMatrix) k) / c k := by
  subst hS'
  set x := S.extCluster
  set B := S.extExchangeMatrix
  have hx0 : ∀ i, x i ≠ 0 := fun i => universalSemifield.coe_ne_zero Fact.out ⟨x i, hx i⟩
  -- the tuple `z` extends `c` by `1` on the frozen positions
  set z : Fin m → F' := fun i => if h : (i : ℕ) < n then c ⟨i, h⟩ else 1 with hzdef
  have hz : ∀ i, (ψ ⟨x i, hx i⟩ : F') = z i * tropicalEval e (φ ⟨x i, hx i⟩) := by
    intro i
    by_cases hi : (i : ℕ) < n
    · simp only [hzdef, hi, dite_true]
      exact hc ⟨i, hi⟩
    · simp only [hzdef, hi, dite_false, one_mul]
      exact hfrozen i (not_lt.1 hi)
  have hzpos : ∏ i, z i ^ (B i k).toNat = exchangeMonomialPos c (principalPart hmn B) k := by
    have h1 : ∏ i : FrozenIndex m n, z i.1 ^ (B i.1 k).toNat = 1 :=
      Finset.prod_eq_one fun i _ => by simp [hzdef, not_lt.2 i.2]
    rw [exchangeMonomialPos_eq_prod, ← prod_castLE_mul_prod_frozenIndex hmn, h1, mul_one]
    exact Finset.prod_congr rfl fun j _ => by simp [hzdef, principalPart]
  have hzneg : ∏ i, z i ^ (-B i k).toNat = exchangeMonomialNeg c (principalPart hmn B) k := by
    have h1 : ∏ i : FrozenIndex m n, z i.1 ^ (-B i.1 k).toNat = 1 :=
      Finset.prod_eq_one fun i _ => by simp [hzdef, not_lt.2 i.2]
    rw [exchangeMonomialNeg_eq_prod, ← prod_castLE_mul_prod_frozenIndex hmn, h1, mul_one]
    exact Finset.prod_congr rfl fun j _ => by simp [hzdef, principalPart]
  -- the exchange monomials as elements of `ℚ_sf(y)`
  set Mp : universalSemifield y := ⟨exchangeMonomialPos x B k,
    exchangeMonomialPos_mem_universalSemifield hx B k⟩ with hMp
  set Mn : universalSemifield y := ⟨exchangeMonomialNeg x B k,
    exchangeMonomialNeg_mem_universalSemifield hx B k⟩ with hMn
  have hψMp : (ψ Mp : F') = exchangeMonomialPos c (principalPart hmn B) k *
      tropicalEval e (φ Mp) := by
    have h : Mp = ⟨∏ i, x i ^ (B i k).toNat, prod_mem_universalSemifield fun i _ =>
        pow_mem_universalSemifield (hx i) _⟩ := Subtype.ext exchangeMonomialPos_eq_prod
    rw [h, ψ.coe_apply_prod_pow_eq_mul_tropicalEval φ he hx hz, hzpos]
  have hψMn : (ψ Mn : F') = exchangeMonomialNeg c (principalPart hmn B) k *
      tropicalEval e (φ Mn) := by
    have h : Mn = ⟨∏ i, x i ^ (-B i k).toNat, prod_mem_universalSemifield fun i _ =>
        pow_mem_universalSemifield (hx i) _⟩ := Subtype.ext exchangeMonomialNeg_eq_prod
    rw [h, ψ.coe_apply_prod_pow_eq_mul_tropicalEval φ he hx hz, hzneg]
  -- `M⁺ₖ = M⁻ₖ ŷₖ`
  have hMpn : Mp = Mn * ⟨yHat S k, hy⟩ :=
    Subtype.ext (exchangeMonomialPos_eq_exchangeMonomialNeg_mul hx0)
  -- the exchange relation `xₖ x'ₖ = M⁺ₖ + M⁻ₖ` in `ℚ_sf(y)`
  set u : universalSemifield y := ⟨x (Fin.castLE hmn k), hx _⟩ with hu
  set u' : universalSemifield y := ⟨(seedMutation hmn S k).extCluster (Fin.castLE hmn k),
    hx' _⟩ with hu'
  have hexch : u * u' = Mp + Mn := by
    refine Subtype.ext ?_
    simp only [hu, hu', hMp, hMn, universalSemifield.coe_mul, universalSemifield.coe_add,
      seedMutation_extCluster_castLE_self]
    exact mul_div_cancel₀ _ (hx0 _)
  have hψ : (ψ u : F') * ψ u' = ψ Mp + ψ Mn := by
    rw [← universalSemifield.coe_mul, ← universalSemifield.coe_add, ← map_mul, ← map_add,
      hexch]
  have hφ : φ u * φ u' = (φ ⟨yHat S k, hy⟩ + 1) * φ Mn := by
    rw [← map_mul, hexch, map_add, hMpn, map_mul, add_mul, one_mul, mul_comm]
  have hε0 : ∀ a, tropicalEval e a ≠ 0 := tropicalEval_ne_zero he
  have hck : c k ≠ 0 := by
    intro h0
    have h := hc k
    rw [h0, zero_mul] at h
    exact universalSemifield.coe_ne_zero Fact.out _ h
  have hprod : tropicalEval e (φ u) * tropicalEval e (φ u') =
      tropicalEval e (φ ⟨yHat S k, hy⟩ + 1) * tropicalEval e (φ Mn) := by
    rw [← tropicalEval_mul he, hφ, tropicalEval_mul he]
  have h := hψ
  rw [hψMp, hψMn, hMpn, map_mul, tropicalEval_mul he, hc',
    show (ψ u : F') = c k * tropicalEval e (φ u) from hc k] at h
  rw [tropicalEval_div he, tropicalEval_div he, tropicalEval_one, eq_div_iff hck]
  have h1 := hε0 (φ ⟨yHat S k, hy⟩ + 1)
  have h2 := hε0 (φ Mn)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, ← add_div, eq_div_iff h1]
  apply mul_right_cancel₀ h2
  linear_combination h - c k * c' k * hprod

end Exchange

/-! ### One edge of the rescaled pattern -/

section Edge

variable {K : Type*} [Field K] [Algebra K F] {m n m' : ℕ}
  (ψ : FZSemifieldHom (universalSemifield y) (universalSemifield y'))
  (φ : FZSemifieldHom (universalSemifield y) (TropicalSemifield (FrozenIndex m' n)))

omit [CharZero F'] in
/-- **The rescaled coefficients mutate tropically** (step 1(b) of the proof of the rescaling
theorem). If `S` is a labeled seed whose `ŷ`-tuple and that of `μₖ(S)` lie in `ℚ_sf(y)`, then
`φ(ŷ(μₖ(S)))` is the coefficient tuple of the mutation in direction `k` of any triple with
coefficient tuple `φ(ŷ(S))` and exchange matrix the principal part of the matrix of `S`. -/
theorem IsLabeledSeed.mutation_coeff_apply_yHat (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (k : Fin n) (hy : ∀ j, yHat S j ∈ universalSemifield y)
    (hy' : ∀ j, yHat (ClusterAlgebras.seedMutation hmn S k) j ∈ universalSemifield y)
    (frozen : FrozenIndex m' n → F') (c : Fin n → F') :
    (SeedTriple.mutation frozen
        ⟨c, fun j => φ ⟨yHat S j, hy j⟩, principalPart hmn S.extExchangeMatrix⟩ k).coeff =
      fun j => φ ⟨yHat (ClusterAlgebras.seedMutation hmn S k) j, hy' j⟩ := by
  haveI : CharZero K := (algebraMap K F).charZero
  funext j
  rcases eq_or_ne j k with rfl | hjk
  · rw [SeedTriple.mutation_coeff_self]
    have h : (⟨yHat (ClusterAlgebras.seedMutation hmn S j) j, hy' j⟩ : universalSemifield y) =
        (⟨yHat S j, hy j⟩)⁻¹ :=
      Subtype.ext (yHat_seedMutation_self hmn hS j)
    rw [h, map_inv]
  rcases le_total (S.extExchangeMatrix (Fin.castLE hmn k) j) 0 with hb | hb
  · rw [SeedTriple.mutation_coeff_of_nonpos _ _ _ hjk hb]
    have h : (⟨yHat (ClusterAlgebras.seedMutation hmn S k) j, hy' j⟩ : universalSemifield y) =
        ⟨yHat S j, hy j⟩ * (⟨yHat S k, hy k⟩ + 1) ^ (-S.extExchangeMatrix (Fin.castLE hmn k) j) :=
      Subtype.ext (yHat_seedMutation_of_nonpos hmn hS hjk hb)
    rw [h, map_mul, map_zpow, map_add, map_one]
    rfl
  · rw [SeedTriple.mutation_coeff_of_nonneg _ _ _ hjk hb]
    have h : (⟨yHat (ClusterAlgebras.seedMutation hmn S k) j, hy' j⟩ : universalSemifield y) =
        ⟨yHat S j, hy j⟩ *
          ((⟨yHat S k, hy k⟩)⁻¹ + 1) ^ (-S.extExchangeMatrix (Fin.castLE hmn k) j) :=
      Subtype.ext (yHat_seedMutation_of_nonneg hmn hS hjk hb)
    rw [h, map_mul, map_zpow, map_add, map_one, map_inv]
    rfl

/-- **One edge of the rescaled pattern** (step 1 of the proof of the rescaling theorem). Let
`S` be a labeled seed and `S' = μₖ(S)`, with all entries and `ŷ`'s of `S` and `S'` in
`ℚ_sf(y)`, let `c`, `c'` be tuples with `ψ(xᵢ) = cᵢ ε(φ(xᵢ))` and `ψ(x'ᵢ) = c'ᵢ ε(φ(x'ᵢ))` for
the cluster variables of `S` and `S'`, and `ψ(xᵢ) = ε(φ(xᵢ))` for the frozen variables of `S`,
where `ε` is the evaluation at nonzero frozen variables. Then the triple
`(c', φ(ŷ(S')), B(S'))` is the mutation in direction `k` of `(c, φ(ŷ(S)), B(S))`. -/
theorem IsLabeledSeed.rescaling_seedMutation (hmn : n ≤ m) {S S' : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (k : Fin n) (hS' : S' = ClusterAlgebras.seedMutation hmn S k)
    (hx : ∀ i, S.extCluster i ∈ universalSemifield y)
    (hx' : ∀ i, S'.extCluster i ∈ universalSemifield y)
    (hy : ∀ j, yHat S j ∈ universalSemifield y) (hy' : ∀ j, yHat S' j ∈ universalSemifield y)
    {frozen : FrozenIndex m' n → F'} (hfrozen₀ : ∀ i, frozen i ≠ 0) {c c' : Fin n → F'}
    (hc : ∀ i : Fin n, (ψ ⟨S.extCluster (Fin.castLE hmn i), hx _⟩ : F') =
      c i * tropicalEval frozen (φ ⟨S.extCluster (Fin.castLE hmn i), hx _⟩))
    (hc' : ∀ i : Fin n, (ψ ⟨S'.extCluster (Fin.castLE hmn i), hx' _⟩ : F') =
      c' i * tropicalEval frozen (φ ⟨S'.extCluster (Fin.castLE hmn i), hx' _⟩))
    (hfrozen : ∀ i : Fin m, n ≤ (i : ℕ) →
      (ψ ⟨S.extCluster i, hx i⟩ : F') = tropicalEval frozen (φ ⟨S.extCluster i, hx i⟩)) :
    (⟨c', fun j => φ ⟨yHat S' j, hy' j⟩, principalPart hmn S'.extExchangeMatrix⟩ :
        SeedTriple F' m' n) =
      SeedTriple.mutation frozen
        ⟨c, fun j => φ ⟨yHat S j, hy j⟩, principalPart hmn S.extExchangeMatrix⟩ k := by
  subst hS'
  set T : SeedTriple F' m' n :=
    ⟨c, fun j => φ ⟨yHat S j, hy j⟩, principalPart hmn S.extExchangeMatrix⟩
  have hcluster : c' = (T.mutation frozen k).cluster := by
    funext j
    rcases eq_or_ne j k with rfl | hjk
    · change c' j = Function.update c j _ j
      rw [Function.update_self]
      exact ψ.rescaling_cluster_seedMutation_self φ hfrozen₀ hmn j rfl hx hx' (hy j) hc (hc' j)
        hfrozen
    · rw [SeedTriple.mutation_cluster_of_ne _ _ _ hjk]
      have he : (⟨(ClusterAlgebras.seedMutation hmn S k).extCluster (Fin.castLE hmn j),
          hx' _⟩ : universalSemifield y) = ⟨S.extCluster (Fin.castLE hmn j), hx _⟩ :=
        Subtype.ext (seedMutation_extCluster_of_ne hmn S ((Fin.castLE_injective hmn).ne hjk))
      have h := hc' j
      rw [he, hc j] at h
      exact (mul_right_cancel₀ (tropicalEval_ne_zero hfrozen₀ _) h).symm
  have hcoeff : (fun j => φ ⟨yHat (ClusterAlgebras.seedMutation hmn S k) j, hy' j⟩) =
      (T.mutation frozen k).coeff :=
    (hS.mutation_coeff_apply_yHat φ hmn k hy hy' frozen c).symm
  have hmat : principalPart hmn (ClusterAlgebras.seedMutation hmn S k).extExchangeMatrix =
      (T.mutation frozen k).exchangeMatrix := by
    rw [SeedTriple.mutation_exchangeMatrix, seedMutation_extExchangeMatrix,
      principalPart_matrixMutation]
  rw [hcluster, hcoeff, hmat]

end Edge

/-! ### The rescaling theorem -/

/-- **Rescaling a seed pattern** ([FWZ], Theorem 4.3.3). Let `Σ = P` be a seed pattern of rank `n`
in `F` over `K`, with matrices of size `m × n`, let `t₀ ∈ 𝕋ₙ` and `x̃ = (x₁, …, xₘ) = x̃(t₀)`. Let
`x̄ = x'` be a free generating tuple of `F̄ = F'` over `K`, of length `m̄ = m'`, let
`T̄ = Trop(q̄_{n+1}, …, q̄_{m̄})` (`TropicalSemifield (FrozenIndex m' n)`), and let `ε̄` be the
monomial evaluation at `(x̄_{n+1}, …, x̄_{m̄})` (it enters through its value `tropicalEval` in
`F̄`, see `coe_monomialEvaluation`). Let `φ : ℚ_sf(x̃) → T̄` and `ψ : ℚ_sf(x̃) → ℚ_sf(x̄)` be
semifield homomorphisms with `ψ(xᵢ) = x̄ᵢ ε̄(φ(xᵢ))` for the positions `i < n` and
`ψ(xᵢ) = ε̄(φ(xᵢ))` for `n ≤ i`. Let `x̄(t) = xb t` in `F̄ⁿ` and `ȳ(t) = yb t` in `T̄ⁿ` satisfy
`ψ(x_{i;t}) = x̄_{i;t} ε̄(φ(x_{i;t}))` and `ȳ_{k;t} = φ(ŷ_{k;t})` for all `t` and all `i, k`. Then
`t ↦ (x̄(t), ȳ(t), B(t))`, `B(t)` the principal part of `B̃(t)`, is a labeled seed pattern of
triples of rank `n` in `F̄` over `K` with frozen variables `x̄_{n+1}, …, x̄_{m̄}`.

[FWZ] takes `K` of characteristic zero; here `F` and `F̄` are assumed of characteristic
zero, which is equivalent. The instance arguments `Fact (AlgebraicIndependent ℚ x̃)` and
`Fact (AlgebraicIndependent ℚ x̄)`, needed for the semifield structures of `ℚ_sf(x̃)` and
`ℚ_sf(x̄)`, follow from the hypotheses by `IsLabeledSeed.algebraicIndependent_rat` (applied to
`hP.1 t₀`) and `IsFreeGeneratingTuple.algebraicIndependent_rat` (applied to `hx'`). The hypothesis
`n ≥ 1` of [FWZ] is not needed. -/
@[cluster_algebras "thm_rescaling"]
theorem IsSeedPattern.isTriplePattern_rescaling {K F F' : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero F] [Field F'] [Algebra K F'] [CharZero F'] {m n m' : ℕ}
    (hmn : n ≤ m) (hm' : n ≤ m') {P : RegularTree n → SeedData F m n}
    (hP : IsSeedPattern K hmn P) (t₀ : RegularTree n)
    [Fact (AlgebraicIndependent ℚ (P t₀).extCluster)] {x' : Fin m' → F'}
    (hx' : IsFreeGeneratingTuple K x') [Fact (AlgebraicIndependent ℚ x')]
    (φ : FZSemifieldHom (universalSemifield (P t₀).extCluster)
      (TropicalSemifield (FrozenIndex m' n)))
    (ψ : FZSemifieldHom (universalSemifield (P t₀).extCluster) (universalSemifield x'))
    (hψ : ∀ (i : Fin m) (hi : (i : ℕ) < n),
      (ψ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩ : F') =
        x' ⟨i, hi.trans_le hm'⟩ * tropicalEval (fun a : FrozenIndex m' n => x' a)
          (φ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩))
    (hψ' : ∀ i : Fin m, n ≤ (i : ℕ) →
      (ψ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩ : F') =
        tropicalEval (fun a : FrozenIndex m' n => x' a)
          (φ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩))
    (xb : RegularTree n → Fin n → F')
    (yb : RegularTree n → Fin n → TropicalSemifield (FrozenIndex m' n))
    (hxb : ∀ t (i : Fin n),
      (ψ ⟨(P t).extCluster (Fin.castLE hmn i),
          hP.extCluster_mem_universalSemifield hmn t₀ t _⟩ : F') =
        xb t i * tropicalEval (fun a : FrozenIndex m' n => x' a)
          (φ ⟨(P t).extCluster (Fin.castLE hmn i),
            hP.extCluster_mem_universalSemifield hmn t₀ t _⟩))
    (hyb : ∀ t k, yb t k = φ ⟨yHat (P t) k, hP.yHat_mem_universalSemifield hmn t₀ t k⟩) :
    IsTriplePattern K (fun i : FrozenIndex m' n => x' i)
      fun t => ⟨xb t, yb t, principalPart hmn (P t).extExchangeMatrix⟩ := by
  set frozen : FrozenIndex m' n → F' := fun i => x' i with hfrozen
  have hfrozen₀ : ∀ i, frozen i ≠ 0 := fun i => hx'.1.ne_zero _
  obtain rfl : yb = fun t k => φ ⟨yHat (P t) k, hP.yHat_mem_universalSemifield hmn t₀ t k⟩ :=
    funext fun t => funext (hyb t)
  -- the frozen variables of every seed are those of `P t₀`
  have hfr : ∀ t (i : Fin m), n ≤ (i : ℕ) →
      (ψ ⟨(P t).extCluster i, hP.extCluster_mem_universalSemifield hmn t₀ t i⟩ : F') =
        tropicalEval frozen
          (φ ⟨(P t).extCluster i, hP.extCluster_mem_universalSemifield hmn t₀ t i⟩) := by
    intro t i hi
    have he : (⟨(P t).extCluster i, hP.extCluster_mem_universalSemifield hmn t₀ t i⟩ :
        universalSemifield (P t₀).extCluster) =
          ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩ :=
      Subtype.ext (congrFun (hP.frozenTuple_eq hmn t t₀) ⟨i, hi⟩)
    rw [he]
    exact hψ' i hi
  haveI : CharZero K := (algebraMap K F).charZero
  refine IsTriplePattern.of_isSeedTriple hm' (fun k t t' h => ?_) (t₀ := t₀) ⟨?_, (hP.1 t₀).2⟩
  · exact (hP.1 t).rescaling_seedMutation ψ φ hmn k (hP.2 k t t' h)
      (hP.extCluster_mem_universalSemifield hmn t₀ t)
      (hP.extCluster_mem_universalSemifield hmn t₀ t')
      (hP.yHat_mem_universalSemifield hmn t₀ t) (hP.yHat_mem_universalSemifield hmn t₀ t')
      hfrozen₀ (hxb t) (hxb t') (hfr t)
  · convert hx' using 1
    funext i
    by_cases hi : (i : ℕ) < n
    · simp only [SeedTriple.extCluster, hi, dite_true]
      have h := (hxb t₀ ⟨i, hi⟩).symm.trans (hψ ⟨i, hi.trans_le hmn⟩ hi)
      exact mul_right_cancel₀ (tropicalEval_ne_zero hfrozen₀ _) h
    · simp only [SeedTriple.extCluster, hi, dite_false, hfrozen]

end ClusterAlgebras

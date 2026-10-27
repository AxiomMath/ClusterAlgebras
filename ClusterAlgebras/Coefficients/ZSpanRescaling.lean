/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Coefficients.CoveringMatrix
public import ClusterAlgebras.Coefficients.Rescaling
public import ClusterAlgebras.Coefficients.ZSpan
public import ClusterAlgebras.Subpattern.SeedReindex

/-!
# Coincidences of seeds transfer under the `ℤ`-span condition

Let `Σ` and `Σ̄` be seed patterns of rank `n` in fields `F` and `F̄` over `K`, with matrices of
sizes `m × n` and `m̄ × n` and the same principal parts, and suppose that at some vertex `t₀` the
extended exchange matrix `B̃̄(t₀)` satisfies the `ℤ`-span condition with respect to `B̃(t₀)`:
`B̃̄(t₀) = Ψ B̃(t₀)` for an integer matrix `Ψ`. FWZ's Corollary 4.3.5 says that every coincidence
among the seeds of `Σ`, labeled or unlabeled, also holds among the seeds of `Σ̄`.

The proof goes through the rescaling theorem. Write `x̃ = x̃(t₀)` and `x̄` for the extended cluster
of `Σ̄(t₀)`. The semifield homomorphisms `φ : ℚ_sf(x̃) → Trop(q̄_{n+1}, …, q̄_{m̄})` with
`φ(xⱼ) = ∏_{i > n} q̄ᵢ ^ Ψᵢⱼ` and `ψ : ℚ_sf(x̃) → ℚ_sf(x̄)` with `ψ(xⱼ) = x̄ⱼ ε̄(φ(xⱼ))` for
`j ≤ n` and `ψ(xⱼ) = ε̄(φ(xⱼ))` for `j > n` rescale `Σ` to a pattern of triples, whose initial
extended matrix is `Ψ' B̃(t₀)` for the covering matrix `Ψ'` of `φ`. The covering matrix agrees with
`Ψ` in its frozen rows, and its first `n` rows are unit vectors, so `Ψ' B̃(t₀) = B̃̄(t₀)`. Since a
pattern of triples is determined by one triple, the rescaled pattern is the pattern of triples of
`Σ̄`: the triple of `Σ̄(t)` is `((ψ(x_{i;t}) / ε̄(φ(x_{i;t})))ᵢ, (φ(ŷ_{k;t}))ₖ, B(t))`, a function
of `Σ(t)`. A seed being determined by its triple and its frozen variables, coincidences of seeds of
`Σ` give coincidences of seeds of `Σ̄`; for unlabeled seeds the same argument is applied to the
seed obtained from `Σ̄(t)` by the permutation relating `Σ(t)` and `Σ(t')`.

## Main definitions

* `Equiv.Perm.extendMutable`: the permutation `σ̂` of `Fin m` extending a permutation `σ` of the
  mutable positions `Fin n` by the identity on the frozen positions.
* `ClusterAlgebras.ReindexingMap.ofMutablePerm`: `σ̂` as a reindexing map.
* `ClusterAlgebras.SeedData.SameUnlabeled`: two seeds represent the same unlabeled seed.

## Main results

* `ClusterAlgebras.IsSeedPattern.exists_rescaling_of_zSpanCondition`: under the `ℤ`-span
  condition, the cluster variables and coefficients of `Σ̄` are obtained from those of `Σ` by
  semifield homomorphisms `φ`, `ψ` as in the rescaling theorem.
* `ClusterAlgebras.IsSeedPattern.eq_of_eq_of_zSpanCondition`: `Σ(t) = Σ(t')` implies
  `Σ̄(t) = Σ̄(t')`.
* `ClusterAlgebras.IsSeedPattern.sameUnlabeled_of_zSpanCondition`: if `Σ(t)` and `Σ(t')`
  represent the same unlabeled seed, so do `Σ̄(t)` and `Σ̄(t')`.
* `ClusterAlgebras.SeedData.sameUnlabeled_iff_exists_eq_reindex`: two seeds represent the same
  unlabeled seed exactly when one is the reindexing of the other along some `σ̂`; together with
  `refl`, `symm` and `trans`, this makes `SameUnlabeled` an equivalence relation.

## Implementation notes

* Indices start at `0`: FWZ's `i ∈ [1, n]` are the `i : Fin m` of value below `n`, and
  the cluster variable `x_{i;t}` for `i : Fin n` is the entry of `x̃(t)` in position
  `Fin.castLE hmn i`.
* FWZ assume that `Σ` and `Σ̄` have the same principal part `B(t)` at every vertex `t`.
  Only agreement at `t₀` is assumed here; it implies agreement everywhere, principal parts
  mutating by matrix mutation (`IsSeedPattern.principalPart_eq_of_principalPart_eq`). This is a
  generalisation.
* FWZ work over a field `K` of characteristic zero. As in the rescaling theorem, `F` and
  `F̄` are assumed to have characteristic zero, which is equivalent. In the lemma producing `φ`
  and `ψ`, whose statement needs the semifield structures of `ℚ_sf(x̃)` and `ℚ_sf(x̄)`, the
  algebraic independence of `x̃` and `x̄` over `ℚ` enters as instance arguments
  `Fact (AlgebraicIndependent ℚ _)`; they follow from the hypotheses by
  `IsFreeGeneratingTuple.algebraicIndependent_rat`, and the two theorems derive them.
* The proof of the lemma takes `φ` with `φ(xⱼ) = ∏_{i > n} q̄ᵢ ^ Ψᵢⱼ` for any `Ψ` with
  `B̃̄(t₀) = Ψ B̃(t₀)`. FWZ first replace the first `n` rows of `Ψ` by unit vectors; this
  is not needed, since the covering matrix of `φ` has unit vectors there anyway and only its
  frozen rows are compared with `Ψ`.
* `ψ` is defined by its values `ψ(xⱼ) = x̄ⱼ ε̄(φ(xⱼ))` and `ψ(xⱼ) = ε̄(φ(xⱼ))`, the hypotheses of
  the rescaling theorem, rather than by `ψ(xⱼ) = ∏ᵢ x̄ᵢ ^ Ψᵢⱼ`; the two agree
  (`coe_apply_eq_prod_zpow_coveringMatrix`), and the former is what the rescaling theorem uses.
* The two theorems are derived from the lemma through
  `IsSeedPattern.cluster_eq_of_zSpanCondition` and
  `IsSeedPattern.coefficientTuple_eq_of_zSpanCondition`: equal cluster variables, respectively
  equal `ŷ`-variables, of `Σ` give equal cluster variables, respectively equal coefficients, of
  `Σ̄`, whatever the positions and vertices.
* A seed is determined by its triple and its frozen variables for all seed data
  (`SeedData.eq_of_toSeedTriple_eq`), so FWZ's verification that the permuted seed
  `Σ̄^σ` is a labeled seed is not needed.
* The permutation `σ̂` of the definition of unlabeled seeds is Mathlib's
  `Equiv.Perm.viaFintypeEmbedding` along `Fin.castLEEmb`, and the permuted seed is
  `SeedData.reindex` along the reindexing map `σ̂`. `SameUnlabeled` itself is stated entrywise,
  as in FWZ.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 4–5*, Section 4.3, Corollary 4.3.5.
-/

@[expose] public section

namespace Equiv.Perm

variable {m n : ℕ} (hmn : n ≤ m) (σ τ : Equiv.Perm (Fin n))

/-- The permutation `σ̂` of `Fin m` that is `σ` on the mutable positions `Fin.castLE hmn i` and
the identity on the frozen positions `n ≤ i`. -/
def extendMutable : Equiv.Perm (Fin m) :=
  σ.viaFintypeEmbedding (Fin.castLEEmb hmn)

/-- `σ̂` sends the mutable position of `i` to the mutable position of `σ i`. -/
@[simp]
theorem extendMutable_castLE (i : Fin n) :
    σ.extendMutable hmn (Fin.castLE hmn i) = Fin.castLE hmn (σ i) :=
  viaFintypeEmbedding_apply_image σ (Fin.castLEEmb hmn) i

/-- `σ̂` is `σ` on the mutable positions. -/
theorem extendMutable_apply_of_lt {i : Fin m} (hi : (i : ℕ) < n) :
    σ.extendMutable hmn i = Fin.castLE hmn (σ ⟨i, hi⟩) :=
  extendMutable_castLE hmn σ ⟨i, hi⟩

/-- `σ̂` fixes the frozen positions. -/
theorem extendMutable_apply_of_le {i : Fin m} (hi : n ≤ (i : ℕ)) : σ.extendMutable hmn i = i :=
  viaFintypeEmbedding_apply_notMem_range σ _ fun ⟨j, hj⟩ => by
    subst hj
    exact absurd j.2 (not_lt.2 (by simpa using hi))

/-- `σ̂` preserves the set of mutable positions. -/
theorem val_extendMutable_lt_iff (i : Fin m) : (σ.extendMutable hmn i : ℕ) < n ↔ (i : ℕ) < n := by
  by_cases hi : (i : ℕ) < n
  · simp [extendMutable_apply_of_lt hmn σ hi, hi]
  · rw [extendMutable_apply_of_le hmn σ (not_lt.1 hi)]

/-- The extension of the identity is the identity. -/
@[simp]
theorem extendMutable_one : (1 : Equiv.Perm (Fin n)).extendMutable hmn = 1 :=
  extendDomain_one _

/-- Extension is multiplicative. -/
theorem extendMutable_mul : (σ * τ).extendMutable hmn = σ.extendMutable hmn * τ.extendMutable hmn :=
  (extendDomain_mul ..).symm

/-- Extension commutes with inversion. -/
theorem extendMutable_inv : σ⁻¹.extendMutable hmn = (σ.extendMutable hmn)⁻¹ :=
  (extendDomain_inv ..).symm

end Equiv.Perm

namespace ClusterAlgebras

/-! ### Permuting the mutable positions of a seed -/

section SameUnlabeled

variable {F : Type*} {m n : ℕ}

namespace ReindexingMap

variable (hmn : n ≤ m) (σ : Equiv.Perm (Fin n))

/-- The reindexing map `σ̂` from `(m, n)` to itself given by a permutation `σ` of the mutable
positions, extended by the identity on the frozen positions. -/
def ofMutablePerm : ReindexingMap m n m n where
  toFun := σ.extendMutable hmn
  injective := (σ.extendMutable hmn).injective
  lt_of_lt p := (σ.val_extendMutable_lt_iff hmn p).2

/-- The underlying map of `ReindexingMap.ofMutablePerm hmn σ` is `σ̂`. -/
@[simp]
theorem coe_ofMutablePerm : ⇑(ofMutablePerm hmn σ) = σ.extendMutable hmn :=
  rfl

/-- The column map of `σ̂` is `σ`. -/
@[simp]
theorem col_ofMutablePerm : (ofMutablePerm hmn σ).col hmn = σ := by
  funext q
  exact Fin.ext (by simp)

end ReindexingMap

/-- Two seeds `(x̃, B̃)` and `(x̃', B̃')` **represent the same unlabeled seed** if there is a
permutation `σ` of the mutable positions such that, with `σ̂` the permutation of all positions
that is `σ` on the mutable ones and the identity on the frozen ones, `x'ᵢ = x_{σ̂ i}` and
`b'ᵢⱼ = b_{σ̂ i, σ j}` for all `i` and `j`. -/
@[cluster_algebras "def_unlabeled_same"]
def SeedData.SameUnlabeled (hmn : n ≤ m) (S S' : SeedData F m n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), (∀ i, S'.extCluster i = S.extCluster (σ.extendMutable hmn i)) ∧
    ∀ i j, S'.extExchangeMatrix i j = S.extExchangeMatrix (σ.extendMutable hmn i) (σ j)

namespace SeedData

variable {hmn : n ≤ m} {S S' S'' : SeedData F m n}

/-- Two seeds represent the same unlabeled seed exactly when one is the reindexing of the other
along `σ̂` for a permutation `σ` of the mutable positions. -/
theorem sameUnlabeled_iff_exists_eq_reindex :
    S.SameUnlabeled hmn S' ↔
      ∃ σ : Equiv.Perm (Fin n), S' = S.reindex hmn (ReindexingMap.ofMutablePerm hmn σ) := by
  refine exists_congr fun σ => ⟨fun ⟨hx, hB⟩ => SeedData.ext (funext hx) (Matrix.ext fun i j => ?_),
    ?_⟩
  · rw [hB, reindex_extExchangeMatrix, matrixReindex_apply,
      ReindexingMap.col_ofMutablePerm]
    rfl
  · rintro rfl
    refine ⟨fun _ => rfl, fun i j => ?_⟩
    rw [reindex_extExchangeMatrix, matrixReindex_apply,
      ReindexingMap.col_ofMutablePerm]
    rfl

namespace SameUnlabeled

variable (hmn S) in
/-- A seed represents the same unlabeled seed as itself. -/
@[refl]
protected theorem refl : S.SameUnlabeled hmn S :=
  ⟨1, by simp, by simp⟩

/-- Representing the same unlabeled seed is symmetric. -/
@[symm]
protected theorem symm (h : S.SameUnlabeled hmn S') : S'.SameUnlabeled hmn S := by
  obtain ⟨σ, hx, hB⟩ := h
  refine ⟨σ⁻¹, fun i => ?_, fun i j => ?_⟩
  · simp [hx, Equiv.Perm.extendMutable_inv]
  · simp [hB, Equiv.Perm.extendMutable_inv]

/-- Representing the same unlabeled seed is transitive. -/
protected theorem trans (h : S.SameUnlabeled hmn S') (h' : S'.SameUnlabeled hmn S'') :
    S.SameUnlabeled hmn S'' := by
  obtain ⟨σ, hx, hB⟩ := h
  obtain ⟨τ, hx', hB'⟩ := h'
  refine ⟨σ * τ, fun i => ?_, fun i j => ?_⟩
  · rw [hx', hx, Equiv.Perm.extendMutable_mul, Equiv.Perm.mul_apply]
  · rw [hB', hB, Equiv.Perm.extendMutable_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

end SameUnlabeled

end SeedData

namespace SeedData

variable (hmn : n ≤ m) (S : SeedData F m n) (σ : Equiv.Perm (Fin n))

/-- Permuting the mutable positions by `σ` does not change the frozen variables. -/
@[simp]
theorem frozenTuple_reindex_ofMutablePerm :
    (S.reindex hmn (ReindexingMap.ofMutablePerm hmn σ)).frozenTuple = S.frozenTuple := by
  funext a
  simp [frozenTuple, Equiv.Perm.extendMutable_apply_of_le hmn σ a.2]

/-- Permuting the mutable positions by `σ` permutes the cluster by `σ`. -/
@[simp]
theorem cluster_reindex_ofMutablePerm (i : Fin n) :
    cluster hmn (S.reindex hmn (ReindexingMap.ofMutablePerm hmn σ)) i = cluster hmn S (σ i) := by
  simp [cluster]

/-- Permuting the mutable positions by `σ` permutes the coefficient tuple by `σ`. -/
@[simp]
theorem coefficientTuple_reindex_ofMutablePerm (k : Fin n) :
    coefficientTuple (S.reindex hmn (ReindexingMap.ofMutablePerm hmn σ)).extExchangeMatrix k =
      coefficientTuple S.extExchangeMatrix (σ k) := by
  ext a
  simp [Equiv.Perm.extendMutable_apply_of_le hmn σ a.2]

/-- Permuting the mutable positions by `σ` conjugates the principal part by `σ`. -/
@[simp]
theorem principalPart_reindex_ofMutablePerm :
    principalPart hmn (S.reindex hmn (ReindexingMap.ofMutablePerm hmn σ)).extExchangeMatrix =
      (principalPart hmn S.extExchangeMatrix).submatrix σ σ := by
  ext i j
  simp [principalPart]

variable [Field F] in
/-- Permuting the mutable positions by `σ` permutes the `ŷ`-tuple by `σ`:
`ŷ_k(σ̂ S) = ŷ_{σ k}(S)`. -/
@[simp]
theorem yHat_reindex_ofMutablePerm (k : Fin n) :
    yHat (S.reindex hmn (ReindexingMap.ofMutablePerm hmn σ)) k = yHat S (σ k) := by
  simp only [yHat, reindex_extCluster, reindex_extExchangeMatrix, matrixReindex_apply,
    ReindexingMap.col_ofMutablePerm, ReindexingMap.coe_ofMutablePerm, Function.comp_apply]
  exact Equiv.prod_comp (σ.extendMutable hmn) fun i => S.extCluster i ^ S.extExchangeMatrix i (σ k)

end SeedData

end SameUnlabeled

/-! ### Transfer of coefficients -/

section Transfer

variable {K F F' : Type*} [Field K] [Field F] [Algebra K F] [Field F'] [Algebra K F'] {m n m' : ℕ}
  (hmn : n ≤ m) (hm' : n ≤ m') {P : RegularTree n → SeedData F m n}
  {P' : RegularTree n → SeedData F' m' n}

/-- Two seed patterns with the same principal part at one vertex have the same principal part at
every vertex: principal parts mutate by matrix mutation. -/
theorem IsSeedPattern.principalPart_eq_of_principalPart_eq (hP : IsSeedPattern K hmn P)
    (hP' : IsSeedPattern K hm' P') {t₀ : RegularTree n}
    (h₀ : principalPart hmn (P t₀).extExchangeMatrix = principalPart hm' (P' t₀).extExchangeMatrix)
    (t : RegularTree n) :
    principalPart hmn (P t).extExchangeMatrix = principalPart hm' (P' t).extExchangeMatrix := by
  have key := RegularTree.eq_of_apply_eq_of_adj (fun k B => matrixMutation le_rfl B k)
    (P := fun t => principalPart hmn (P t).extExchangeMatrix)
    (P' := fun t => principalPart hm' (P' t).extExchangeMatrix)
    (fun k t t' h => by
      rw [hP.2 k t t' h, seedMutation_extExchangeMatrix, principalPart_matrixMutation])
    (fun k t t' h => by
      rw [hP'.2 k t t' h, seedMutation_extExchangeMatrix, principalPart_matrixMutation]) h₀
  exact congrFun key t

/-- **Coefficients transfer under the `ℤ`-span condition.** Let `Σ = P` and `Σ̄ = P'` be seed
patterns of rank `n` in `F` and in `F̄ = F'` over `K`, with matrices of sizes `m × n` and
`m̄ × n` (`m̄ = m'`), and let `t₀` be a vertex at which `Σ` and `Σ̄` have the same principal part
and `B̃̄(t₀)` satisfies the `ℤ`-span condition with respect to `B̃(t₀)`. Let `x̃ = x̃(t₀)`, let
`x̄ = (x̄₁, …, x̄_{m̄})` be the extended cluster of `Σ̄(t₀)`, let `(x̄(t), ȳ(t), B̄(t))` be the
triple of `Σ̄(t)`, and let `ε̄` be the monomial evaluation at `(x̄_{n+1}, …, x̄_{m̄})`. Then there
are semifield homomorphisms `φ : ℚ_sf(x̃) → Trop(q̄_{n+1}, …, q̄_{m̄})` and
`ψ : ℚ_sf(x̃) → ℚ_sf(x̄)` with `ψ(xᵢ) = x̄ᵢ ε̄(φ(xᵢ))` for `i < n` and `ψ(xᵢ) = ε̄(φ(xᵢ))` for
`n ≤ i`, such that `ψ(x_{i;t}) = x̄_{i;t} ε̄(φ(x_{i;t}))` and `ȳ_{k;t} = φ(ŷ_{k;t})` for all `t`,
`i` and `k`.

Agreement of the principal parts at `t₀` implies agreement at every vertex
(`IsSeedPattern.principalPart_eq_of_principalPart_eq`). The instance arguments
`Fact (AlgebraicIndependent ℚ x̃)` and `Fact (AlgebraicIndependent ℚ x̄)`, which give `ℚ_sf(x̃)`
and `ℚ_sf(x̄)` their semifield structures, follow from the other hypotheses by
`IsLabeledSeed.algebraicIndependent_rat`; the characteristic-zero hypotheses on `F` and `F'`
follow from characteristic zero of `K`. -/
@[cluster_algebras "lem_z_span_rescaling"]
theorem IsSeedPattern.exists_rescaling_of_zSpanCondition [CharZero F] [CharZero F']
    (hP : IsSeedPattern K hmn P) (hP' : IsSeedPattern K hm' P') (t₀ : RegularTree n)
    (hB : principalPart hmn (P t₀).extExchangeMatrix = principalPart hm' (P' t₀).extExchangeMatrix)
    (hZ : ZSpanCondition (P' t₀).extExchangeMatrix (P t₀).extExchangeMatrix)
    [Fact (AlgebraicIndependent ℚ (P t₀).extCluster)]
    [Fact (AlgebraicIndependent ℚ (P' t₀).extCluster)] :
    ∃ (φ : FZSemifieldHom (universalSemifield (P t₀).extCluster)
        (TropicalSemifield (FrozenIndex m' n)))
      (ψ : FZSemifieldHom (universalSemifield (P t₀).extCluster)
        (universalSemifield (P' t₀).extCluster)),
      (∀ (i : Fin m) (hi : (i : ℕ) < n),
        (ψ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩ : F') =
          (P' t₀).extCluster ⟨i, hi.trans_le hm'⟩ *
            tropicalEval (fun a : FrozenIndex m' n => (P' t₀).extCluster a)
              (φ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩)) ∧
      (∀ i : Fin m, n ≤ (i : ℕ) →
        (ψ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩ : F') =
          tropicalEval (fun a : FrozenIndex m' n => (P' t₀).extCluster a)
            (φ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩)) ∧
      (∀ t (i : Fin n),
        (ψ ⟨(P t).extCluster (Fin.castLE hmn i),
            hP.extCluster_mem_universalSemifield hmn t₀ t _⟩ : F') =
          ((P' t).toSeedTriple hm').cluster i *
            tropicalEval (fun a : FrozenIndex m' n => (P' t₀).extCluster a)
              (φ ⟨(P t).extCluster (Fin.castLE hmn i),
                hP.extCluster_mem_universalSemifield hmn t₀ t _⟩)) ∧
      ∀ t k, ((P' t).toSeedTriple hm').coeff k =
        φ ⟨yHat (P t) k, hP.yHat_mem_universalSemifield hmn t₀ t k⟩ := by
  classical
  obtain ⟨Ψ, hΨ⟩ := zSpanCondition_iff_exists_mul.1 hZ
  have hx' : IsFreeGeneratingTuple K (P' t₀).extCluster := (hP'.1 t₀).1
  set frozen : FrozenIndex m' n → F' := fun a => (P' t₀).extCluster a with hfrozen
  have hfr₀ : ∀ a, frozen a ≠ 0 := fun a => hx'.1.ne_zero _
  have hev : ∀ y, tropicalEval frozen y ∈ universalSemifield (P' t₀).extCluster := fun y =>
    prod_mem_universalSemifield fun a _ =>
      zpow_mem_universalSemifield (mem_universalSemifield_self _ _) _
  -- `φ(xⱼ) = ∏_{i ≥ n} q̄ᵢ ^ Ψᵢⱼ`
  set φ := universalSemifieldLift (P t₀).extCluster fun j =>
    TropicalSemifield.monomial fun a : FrozenIndex m' n => Ψ a.1 j with hφdef
  have hφ : ∀ j, φ ⟨(P t₀).extCluster j, mem_universalSemifield_self _ j⟩ =
      TropicalSemifield.monomial fun a : FrozenIndex m' n => Ψ a.1 j :=
    universalSemifieldLift_apply_self _
  -- `ψ(xⱼ) = x̄ⱼ ε̄(φ(xⱼ))` for `j < n` and `ψ(xⱼ) = ε̄(φ(xⱼ))` otherwise
  set f : Fin m → universalSemifield (P' t₀).extCluster := fun j =>
    if h : (j : ℕ) < n then
      ⟨(P' t₀).extCluster ⟨j, h.trans_le hm'⟩, mem_universalSemifield_self _ _⟩ *
        ⟨tropicalEval frozen (φ ⟨(P t₀).extCluster j, mem_universalSemifield_self _ j⟩), hev _⟩
    else ⟨tropicalEval frozen (φ ⟨(P t₀).extCluster j, mem_universalSemifield_self _ j⟩), hev _⟩
    with hfdef
  set ψ := universalSemifieldLift (P t₀).extCluster f with hψdef
  have hψ : ∀ (i : Fin m) (hi : (i : ℕ) < n),
      (ψ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩ : F') =
        (P' t₀).extCluster ⟨i, hi.trans_le hm'⟩ *
          tropicalEval frozen (φ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩) := by
    intro i hi
    rw [hψdef, universalSemifieldLift_apply_self, hfdef]
    dsimp only
    rw [dif_pos hi, universalSemifield.coe_mul]
  have hψ' : ∀ i : Fin m, n ≤ (i : ℕ) →
      (ψ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩ : F') =
        tropicalEval frozen (φ ⟨(P t₀).extCluster i, mem_universalSemifield_self _ i⟩) := by
    intro i hi
    rw [hψdef, universalSemifieldLift_apply_self, hfdef]
    dsimp only
    rw [dif_neg (not_lt.2 hi)]
  -- the rescaled pattern `Π`
  set xb : RegularTree n → Fin n → F' := fun t i =>
    (ψ ⟨(P t).extCluster (Fin.castLE hmn i), hP.extCluster_mem_universalSemifield hmn t₀ t _⟩ :
      F') / tropicalEval frozen (φ ⟨(P t).extCluster (Fin.castLE hmn i),
        hP.extCluster_mem_universalSemifield hmn t₀ t _⟩) with hxbdef
  have hxb : ∀ t (i : Fin n),
      (ψ ⟨(P t).extCluster (Fin.castLE hmn i),
          hP.extCluster_mem_universalSemifield hmn t₀ t _⟩ : F') =
        xb t i * tropicalEval frozen (φ ⟨(P t).extCluster (Fin.castLE hmn i),
          hP.extCluster_mem_universalSemifield hmn t₀ t _⟩) := fun t i =>
    (div_mul_cancel₀ _ (tropicalEval_ne_zero hfr₀ _)).symm
  set yb : RegularTree n → Fin n → TropicalSemifield (FrozenIndex m' n) := fun t k =>
    φ ⟨yHat (P t) k, hP.yHat_mem_universalSemifield hmn t₀ t k⟩ with hybdef
  have hRes := hP.isTriplePattern_rescaling hmn hm' t₀ hx' φ ψ hψ hψ' xb yb hxb fun _ _ => rfl
  have hTr := hP'.isTriplePattern_toSeedTriple hm' t₀
  -- `Π` and the triples of `Σ̄` agree at `t₀`
  have h₀ : (⟨xb t₀, yb t₀, principalPart hmn (P t₀).extExchangeMatrix⟩ : SeedTriple F' m' n) =
      (P' t₀).toSeedTriple hm' := by
    have hcl : xb t₀ = cluster hm' (P' t₀) := funext fun i => by
      rw [hxbdef]
      dsimp only
      rw [hψ (Fin.castLE hmn i) i.2, mul_div_cancel_right₀ _ (tropicalEval_ne_zero hfr₀ _)]
      rfl
    have hco : yb t₀ = coefficientTuple (P' t₀).extExchangeMatrix := funext fun k => by
      ext a
      have hc := congrFun (congrFun (tripleExtendedMatrix_eq_coveringMatrix_mul hmn (P t₀) φ
        (yb t₀) fun _ => rfl) a.1) k
      rw [tripleExtendedMatrix_apply_frozenIndex] at hc
      rw [hc, exponent_coefficientTuple, hΨ, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coveringMatrix_apply_frozenIndex, hφ, TropicalSemifield.exponent_monomial]
    simp only [SeedData.toSeedTriple, hcl, hco, hB]
  have heq := hRes.eq_of_apply_eq hTr h₀
  have ht : ∀ t, (P' t).toSeedTriple hm' =
      ⟨xb t, yb t, principalPart hmn (P t).extExchangeMatrix⟩ := fun t => (congrFun heq t).symm
  refine ⟨φ, ψ, hψ, hψ', fun t i => ?_, fun t k => ?_⟩
  · rw [ht t]
    exact hxb t i
  · rw [ht t]

variable [CharZero F] [CharZero F']

/-- **Cluster variables transfer under the `ℤ`-span condition.** In the situation of
`IsSeedPattern.exists_rescaling_of_zSpanCondition`, if the cluster variables of `Σ` in
positions `i` at `t` and `j` at `t'` coincide, so do those of `Σ̄`. -/
theorem IsSeedPattern.cluster_eq_of_zSpanCondition (hP : IsSeedPattern K hmn P)
    (hP' : IsSeedPattern K hm' P') {t₀ : RegularTree n}
    (hB : principalPart hmn (P t₀).extExchangeMatrix = principalPart hm' (P' t₀).extExchangeMatrix)
    (hZ : ZSpanCondition (P' t₀).extExchangeMatrix (P t₀).extExchangeMatrix)
    {t t' : RegularTree n} {i j : Fin n}
    (h : cluster hmn (P t) i = cluster hmn (P t') j) :
    cluster hm' (P' t) i = cluster hm' (P' t') j := by
  haveI : Fact (AlgebraicIndependent ℚ (P t₀).extCluster) :=
    ⟨(hP.1 t₀).1.algebraicIndependent_rat⟩
  haveI : Fact (AlgebraicIndependent ℚ (P' t₀).extCluster) :=
    ⟨(hP'.1 t₀).1.algebraicIndependent_rat⟩
  obtain ⟨φ, ψ, -, -, hx, -⟩ := hP.exists_rescaling_of_zSpanCondition hmn hm' hP' t₀ hB hZ
  have h₁ := hx t i
  have h₂ := hx t' j
  have he : (⟨(P t).extCluster (Fin.castLE hmn i),
      hP.extCluster_mem_universalSemifield hmn t₀ t _⟩ : universalSemifield (P t₀).extCluster) =
        ⟨(P t').extCluster (Fin.castLE hmn j), hP.extCluster_mem_universalSemifield hmn t₀ t' _⟩ :=
    Subtype.ext h
  rw [he] at h₁
  have hfr₀ : ∀ a : FrozenIndex m' n, (P' t₀).extCluster a ≠ 0 := fun a =>
    (hP'.1 t₀).1.1.ne_zero _
  exact mul_right_cancel₀ (tropicalEval_ne_zero hfr₀ _) (h₁.symm.trans h₂)

/-- **Coefficients transfer under the `ℤ`-span condition.** In the situation of
`IsSeedPattern.exists_rescaling_of_zSpanCondition`, if the `ŷ`-variables of `Σ` in positions `k`
at `t` and `l` at `t'` coincide, then the coefficients of `Σ̄` in these positions coincide. -/
theorem IsSeedPattern.coefficientTuple_eq_of_zSpanCondition (hP : IsSeedPattern K hmn P)
    (hP' : IsSeedPattern K hm' P') {t₀ : RegularTree n}
    (hB : principalPart hmn (P t₀).extExchangeMatrix = principalPart hm' (P' t₀).extExchangeMatrix)
    (hZ : ZSpanCondition (P' t₀).extExchangeMatrix (P t₀).extExchangeMatrix)
    {t t' : RegularTree n} {k l : Fin n} (h : yHat (P t) k = yHat (P t') l) :
    coefficientTuple (P' t).extExchangeMatrix k = coefficientTuple (P' t').extExchangeMatrix l := by
  haveI : Fact (AlgebraicIndependent ℚ (P t₀).extCluster) :=
    ⟨(hP.1 t₀).1.algebraicIndependent_rat⟩
  haveI : Fact (AlgebraicIndependent ℚ (P' t₀).extCluster) :=
    ⟨(hP'.1 t₀).1.algebraicIndependent_rat⟩
  obtain ⟨φ, ψ, -, -, -, hy⟩ := hP.exists_rescaling_of_zSpanCondition hmn hm' hP' t₀ hB hZ
  have he : (⟨yHat (P t) k, hP.yHat_mem_universalSemifield hmn t₀ t k⟩ :
      universalSemifield (P t₀).extCluster) =
        ⟨yHat (P t') l, hP.yHat_mem_universalSemifield hmn t₀ t' l⟩ :=
    Subtype.ext h
  exact (hy t k).trans ((congrArg φ he).trans (hy t' l).symm)

/-- **Coincident seeds transfer under the `ℤ`-span condition** (FWZ, Corollary 4.3.5, for
labeled seeds). Let `Σ = P` and `Σ̄ = P'` be seed patterns of rank `n` in `F` and in `F'` over
`K`, and let `t₀` be a vertex at which they have the same principal part and `B̃̄(t₀)`
satisfies the `ℤ`-span condition with respect to `B̃(t₀)`. If `Σ(t) = Σ(t')`, then
`Σ̄(t) = Σ̄(t')`.

FWZ assume that the principal parts agree at every vertex; agreement at `t₀` suffices.
The characteristic-zero hypotheses on `F` and `F'` follow from FWZ's on `K`. -/
@[cluster_algebras "thm_z_span_labeled"]
theorem IsSeedPattern.eq_of_eq_of_zSpanCondition (hP : IsSeedPattern K hmn P)
    (hP' : IsSeedPattern K hm' P') {t₀ : RegularTree n}
    (hB : principalPart hmn (P t₀).extExchangeMatrix = principalPart hm' (P' t₀).extExchangeMatrix)
    (hZ : ZSpanCondition (P' t₀).extExchangeMatrix (P t₀).extExchangeMatrix)
    {t t' : RegularTree n} (h : P t = P t') : P' t = P' t' := by
  have hpp := hP.principalPart_eq_of_principalPart_eq hmn hm' hP' hB
  refine SeedData.eq_of_toSeedTriple_eq hm' ?_ (hP'.frozenTuple_eq hm' t t')
  simp only [SeedData.toSeedTriple, SeedTriple.mk.injEq]
  exact ⟨funext fun i => hP.cluster_eq_of_zSpanCondition hmn hm' hP' hB hZ (by rw [h]),
    funext fun k => hP.coefficientTuple_eq_of_zSpanCondition hmn hm' hP' hB hZ (by rw [h]),
    by rw [← hpp t, ← hpp t', h]⟩

/-- **Coincident unlabeled seeds transfer under the `ℤ`-span condition** (FWZ, Corollary 4.3.5,
for unlabeled seeds). Let `Σ = P` and `Σ̄ = P'` be seed patterns of rank `n` in `F` and in `F'`
over `K`, and let `t₀` be a vertex at which they have the same principal part and `B̃̄(t₀)`
satisfies the `ℤ`-span condition with respect to `B̃(t₀)`. If `Σ(t)` and `Σ(t')` represent the
same unlabeled seed, so do `Σ̄(t)` and `Σ̄(t')`, with the same permutation.

FWZ assume that the principal parts agree at every vertex; agreement at `t₀` suffices.
The characteristic-zero hypotheses on `F` and `F'` follow from FWZ's on `K`. -/
@[cluster_algebras "thm_z_span_unlabeled"]
theorem IsSeedPattern.sameUnlabeled_of_zSpanCondition (hP : IsSeedPattern K hmn P)
    (hP' : IsSeedPattern K hm' P') {t₀ : RegularTree n}
    (hB : principalPart hmn (P t₀).extExchangeMatrix = principalPart hm' (P' t₀).extExchangeMatrix)
    (hZ : ZSpanCondition (P' t₀).extExchangeMatrix (P t₀).extExchangeMatrix)
    {t t' : RegularTree n} (h : (P t).SameUnlabeled hmn (P t')) :
    (P' t).SameUnlabeled hm' (P' t') := by
  obtain ⟨σ, hσ⟩ := SeedData.sameUnlabeled_iff_exists_eq_reindex.1 h
  have hpp := hP.principalPart_eq_of_principalPart_eq hmn hm' hP' hB
  refine SeedData.sameUnlabeled_iff_exists_eq_reindex.2 ⟨σ, SeedData.eq_of_toSeedTriple_eq hm' ?_
    (by rw [SeedData.frozenTuple_reindex_ofMutablePerm, hP'.frozenTuple_eq hm' t' t])⟩
  simp only [SeedData.toSeedTriple, SeedTriple.mk.injEq]
  refine ⟨funext fun i => ?_, funext fun k => ?_, ?_⟩
  · rw [SeedData.cluster_reindex_ofMutablePerm]
    exact hP.cluster_eq_of_zSpanCondition hmn hm' hP' hB hZ
      (by rw [hσ, SeedData.cluster_reindex_ofMutablePerm])
  · rw [SeedData.coefficientTuple_reindex_ofMutablePerm]
    exact hP.coefficientTuple_eq_of_zSpanCondition hmn hm' hP' hB hZ
      (by rw [hσ, SeedData.yHat_reindex_ofMutablePerm])
  · rw [SeedData.principalPart_reindex_ofMutablePerm, ← hpp t', ← hpp t, hσ,
      SeedData.principalPart_reindex_ofMutablePerm]

end Transfer

end ClusterAlgebras

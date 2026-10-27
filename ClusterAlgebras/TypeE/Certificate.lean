/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.ClusterAlgebra
public import ClusterAlgebras.Laurent.Expansion
public import ClusterAlgebras.TypeE.Relabel
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Exchange certificates

An *exchange certificate* for an integer matrix `B̃₀` consists of finitely many integer Laurent
polynomials `v₁, …, v_N` and finitely many abstract seeds `(α_a, B̃_a)`, with the outcome of every
mutation of every listed seed up to relabelling, subject to finitely many identities between
integer matrices and Laurent polynomials. A certificate for `B̃₀` describes every seed pattern
through every seed `(x̃, B̃₀)`: it is of finite type, with exactly `N` cluster variables and
exactly `M` clusters. Together with a reference matrix and the `ℤ`-span condition, a pair of
certificates gives finite type and the counts for every seed pattern of a given type; this
replaces the computer search by which [FWZ] establish finite type for `E₈`.

## Main definitions

* `ClusterAlgebras.LaurentRing m`: the ring `L_m = ℤ[X₁^{±1}, …, X_m^{±1}]`.
* `ClusterAlgebras.LaurentRing.eval x f`: the evaluation `ev_x̃(f) = ∑ₐ f(a) x̃^a`.
* `ClusterAlgebras.ExchangeCertificate hmn B₀ N M`: an exchange certificate for `B̃₀` with `N`
  variables and `M` seeds.
* `ClusterAlgebras.ExchangeCertificate.seed C x a`: the seed `S_a` of a certificate evaluated at
  `x̃`.

## Main statements

* `ClusterAlgebras.LaurentRing.exists_ringHom_eval_injective`: evaluation at an algebraically
  independent tuple is an injective ring homomorphism.
* `ClusterAlgebras.ExchangeCertificate.exists_apply_eq_relabel_seed`,
  `ClusterAlgebras.ExchangeCertificate.isFiniteType_and_encard`: an exchange certificate
  describes the seed pattern.
* `ClusterAlgebras.ExchangeCertificate.isFiniteType_and_encard_of_isPatternOfType`: finite type
  and counts from a pair of certificates.

## Implementation notes

* `L_m` is `AddMonoidAlgebra ℤ (Fin m → ℤ)`: the finitely supported functions `ℤ^m → ℤ` with
  pointwise addition and the convolution product, `X^a` being the indicator
  `AddMonoidAlgebra.single a 1`. Mathlib has no multivariate Laurent polynomial ring
  (`LaurentPolynomial` is univariate); the localization of `MvPolynomial (Fin m) ℤ` at the
  monomials would be isomorphic, but its elements are not finitely supported functions on `ℤ^m`,
  and the coefficient-wise identities of a certificate are statements about `Finsupp`s.
* The evaluation is a plain function of the tuple `x̃`, and is defined for every tuple (Lean's
  `x⁻¹` is total); that it is a ring homomorphism, and injective, for an algebraically independent
  tuple is `ClusterAlgebras.LaurentRing.exists_ringHom_eval_injective`.
* Indices are `Fin`, so the seed `1` is `⟨0, _⟩`, the variables `v₁, …, v_n` are
  `v (Fin.castLE _ i)`, and the frozen indices `[n + 1, m]` are those of value at least `n`.
* The data (i)–(iii) of a certificate are the data fields of `ExchangeCertificate`; its
  conditions (T1)–(T3), (D1)–(D4) are its `Prop` fields, together with the conditions in (i) and
  (ii) (`v_i = X_i`, injectivity of `α_a`, `α₁ = id`, `B̃₁ = B̃₀`). The implicit conditions
  `n ≤ N` (needed to state `v_i = X_i` for `i ∈ [1, n]`) and `M ≥ 1` (needed to name the seed
  `1`) are the fields `le_card_var` and `card_seed_pos`. That `B̃₀` is extended
  skew-symmetrizable is not part of the structure: nothing in the conditions uses it.
* In (T3) the exponents `b^a_{ik}` and `-b^a_{ik}` are positive, so they are taken as natural
  numbers by `Int.toNat`; `L_m` is a ring, not a field, so the integer powers of
  `exchangeMonomialPos` are not available there.
* `ClusterAlgebras.ExchangeCertificate.isFiniteType_and_encard_of_isPatternOfType` is stated for
  patterns of rank `X.rank`, the rank of every pattern of type `[X]`. In its proof the auxiliary
  patterns with trivial and with full rank coefficients are taken in the fields of rational
  functions `K(X₁, …, Xₙ)` and `K(X₁, …, X_{m₁})`, rather than in `K(x̄₁, …, x̄ₙ)` and a purely
  transcendental extension of it: the transfer of coincidences of cluster variables compares
  patterns in different fields, and only the exchange matrices at one vertex enter it.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

/-! ### Laurent polynomials in `m` indeterminates -/

/-- The ring `L_m = ℤ[X₁^{±1}, …, X_m^{±1}]` of **integer Laurent polynomials** in `m`
indeterminates: the finitely supported functions `f : ℤ^m → ℤ`, with pointwise addition and the
convolution product `(fg)(c) = ∑_{a + b = c} f(a) g(b)`. -/
@[cluster_algebras "def_exc_laurent_ring"]
abbrev LaurentRing (m : ℕ) : Type :=
  AddMonoidAlgebra ℤ (Fin m → ℤ)

namespace LaurentRing

variable {m : ℕ}

/-- The Laurent monomial `X^a`, the function equal to `1` at `a` and to `0` elsewhere. -/
@[cluster_algebras "def_exc_laurent_ring"]
noncomputable def monomial (a : Fin m → ℤ) : LaurentRing m :=
  AddMonoidAlgebra.single a 1

/-- The indeterminate `Xᵢ = X^{eᵢ}`, `eᵢ` the `i`th unit vector. -/
@[cluster_algebras "def_exc_laurent_ring"]
noncomputable def X (i : Fin m) : LaurentRing m :=
  monomial (Pi.single i 1)

/-- The **evaluation** `ev_x̃(f) = ∑ₐ f(a) x̃^a` of a Laurent polynomial at an `m`-tuple `x̃` of
elements of a field, where `x̃^a = ∏ᵢ xᵢ^{aᵢ}`. FWZ evaluate only at tuples of nonzero
elements; the formula makes sense for every tuple. -/
@[cluster_algebras "def_exc_laurent_ring"]
noncomputable def eval {F : Type*} [Field F] (x : Fin m → F) (f : LaurentRing m) : F :=
  f.coeff.sum fun a c => (c : F) * ∏ i, x i ^ a i

/-- The identity of `L_m` is `X^0`. -/
@[cluster_algebras "lem_exc_laurent_evaluation", simp]
theorem monomial_zero : monomial (0 : Fin m → ℤ) = 1 :=
  rfl

/-- `X^a X^b = X^{a+b}`. -/
@[cluster_algebras "lem_exc_laurent_evaluation", simp]
theorem monomial_mul_monomial (a b : Fin m → ℤ) : monomial a * monomial b = monomial (a + b) := by
  simp [monomial, AddMonoidAlgebra.single_mul_single]

/-- `ev_x̃(X^a) = x̃^a`. -/
@[simp]
theorem eval_monomial {F : Type*} [Field F] (x : Fin m → F) (a : Fin m → ℤ) :
    eval x (monomial a) = ∏ i, x i ^ a i := by
  change (Finsupp.single _ (1 : ℤ)).sum _ = _
  rw [Finsupp.sum_single_index (by simp), Int.cast_one, one_mul]

/-- **Evaluation of Laurent polynomials**: `ev_x̃(Xᵢ) = xᵢ`. -/
@[cluster_algebras "lem_exc_laurent_evaluation", simp]
theorem eval_X {F : Type*} [Field F] (x : Fin m → F) (i : Fin m) : eval x (X i) = x i := by
  rw [X, eval_monomial, Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- **Evaluation of Laurent polynomials**: if `F` has characteristic zero and the entries of
`x̃` are algebraically independent over `ℚ`, then `ev_x̃` is an injective ring homomorphism. -/
@[cluster_algebras "lem_exc_laurent_evaluation"]
theorem exists_ringHom_eval_injective {F : Type*} [Field F] [CharZero F] {x : Fin m → F}
    (hx : AlgebraicIndependent ℚ x) :
    ∃ φ : LaurentRing m →+* F, ⇑φ = eval x ∧ Function.Injective φ := by
  let g : Multiplicative (Fin m → ℤ) →* F :=
    { toFun := fun a => ∏ i, x i ^ (a.toAdd i)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [toAdd_mul, Pi.add_apply, zpow_add₀ (hx.ne_zero _), Finset.prod_mul_distrib] }
  let φ : LaurentRing m →+* F := (AddMonoidAlgebra.lift ℤ F (Fin m → ℤ) g).toRingHom
  have hφ : ∀ f, φ f = Finsupp.linearCombination ℤ (fun a : Fin m → ℤ => ∏ i, x i ^ a i) f :=
    fun f => by simp [φ, g, AddMonoidAlgebra.lift_apply, Finsupp.linearCombination_apply]
  refine ⟨φ, funext fun f => ?_, (injective_iff_map_eq_zero φ).2 fun f hf => ?_⟩
  · rw [hφ, Finsupp.linearCombination_apply]
    simp only [zsmul_eq_mul, eval]
    rfl
  · have hli : LinearIndependent ℤ (fun a : Fin m → ℤ => ∏ i, x i ^ a i) := by
      convert (linearIndependent_laurentMonomial hx).comp _
        Finsupp.equivFunOnFinite.symm.injective using 1
      funext a
      simp [laurentMonomial, Finsupp.prod_fintype]
    exact linearIndependent_iff.1 hli f ((hφ f).symm.trans hf)

end LaurentRing

/-! ### Exchange certificates -/

namespace TypeE

variable {m n N : ℕ}

/-- The tuple `w^a = (w^a_1, …, w^a_m)` of a listed seed: `w^a_i = v_{α_a(i)}` for a mutable
index `i` and `w^a_i = X_i` for a frozen one. -/
noncomputable def extTuple (v : Fin N → LaurentRing m) (α : Fin n → Fin N) :
    Fin m → LaurentRing m :=
  fun i => if h : (i : ℕ) < n then v (α ⟨i, h⟩) else LaurentRing.X i

/-- The positive exchange monomial `∏_{i : b_{ik} > 0} wᵢ^{b_{ik}}` in a commutative monoid, the
exponents being natural numbers. -/
def monomialPos {R : Type*} [CommMonoid R] (w : Fin m → R) (B : Matrix (Fin m) (Fin n) ℤ)
    (k : Fin n) : R :=
  ∏ i ∈ Finset.univ.filter (fun i => 0 < B i k), w i ^ (B i k).toNat

/-- The negative exchange monomial `∏_{i : b_{ik} < 0} wᵢ^{-b_{ik}}` in a commutative monoid, the
exponents being natural numbers. -/
def monomialNeg {R : Type*} [CommMonoid R] (w : Fin m → R) (B : Matrix (Fin m) (Fin n) ℤ)
    (k : Fin n) : R :=
  ∏ i ∈ Finset.univ.filter (fun i => B i k < 0), w i ^ (-B i k).toNat

end TypeE

variable {m n : ℕ}

/-- An **exchange certificate** for an `m × n` integer matrix `B̃₀` with `N` variables and `M`
seeds consists of
* (i) Laurent polynomials `v₁, …, v_N ∈ L_m` (`var`) with `vᵢ = Xᵢ` for `i ∈ [1, n]`;
* (ii) for each seed `a`, an injective map `α_a : [1, n] → [1, N]` (`seedVar a`) and an `m × n`
  integer matrix `B̃_a` (`seedMatrix a`), with `α₁ = id` and `B̃₁ = B̃₀`;
* (iii) for each seed `a` and direction `k`, a seed `ν(a, k)` (`next a k`) and a permutation
  `π_{a,k}` of `[1, n]` (`perm a k`);

such that, with `w^a` the tuple `TypeE.extTuple var (seedVar a)`, for all `a` and `k`, with
`a' = ν(a, k)` and `π = π_{a,k}`:
* (T1) `μ_k(B̃_a) = B̃_{a'}^π`;
* (T2) `α_{a'}(π(j)) = α_a(j)` for `j ≠ k`;
* (T3) `v_{α_a(k)} v_{α_{a'}(π(k))} = ∏_{b^a_{ik} > 0} (w^a_i)^{b^a_{ik}} +
  ∏_{b^a_{ik} < 0} (w^a_i)^{-b^a_{ik}}` in `L_m`;

and moreover
* (D1) the `vᵢ` are pairwise distinct;
* (D2) the sets `α_a([1, n])` are pairwise distinct;
* (D3) every `c ∈ [1, N]` lies in some `α_a([1, n])`;
* (D4) every seed is reached from the seed `1` by finitely many transitions `a ↦ ν(a, k)`.

The seed `1` of FWZ is `⟨0, card_seed_pos⟩` here. -/
@[cluster_algebras "def_exc_certificate"]
structure ExchangeCertificate (hmn : n ≤ m) (B₀ : Matrix (Fin m) (Fin n) ℤ) (N M : ℕ) where
  /-- There are at least `n` variables, so that `v₁, …, v_n` exist. -/
  le_card_var : n ≤ N
  /-- There is at least one seed, the seed `1`. -/
  card_seed_pos : 0 < M
  /-- (i) The Laurent polynomials `v₁, …, v_N`. -/
  var : Fin N → LaurentRing m
  /-- (i) `vᵢ = Xᵢ` for `i ∈ [1, n]`. -/
  var_castLE : ∀ i : Fin n, var (Fin.castLE le_card_var i) = LaurentRing.X (Fin.castLE hmn i)
  /-- (ii) The map `α_a : [1, n] → [1, N]` listing the cluster of the seed `a`. -/
  seedVar : Fin M → Fin n → Fin N
  /-- (ii) Each `α_a` is injective. -/
  seedVar_injective : ∀ a, Function.Injective (seedVar a)
  /-- (ii) The matrix `B̃_a` of the seed `a`. -/
  seedMatrix : Fin M → Matrix (Fin m) (Fin n) ℤ
  /-- (ii) `α₁(i) = i`. -/
  seedVar_zero : seedVar ⟨0, card_seed_pos⟩ = Fin.castLE le_card_var
  /-- (ii) `B̃₁ = B̃₀`. -/
  seedMatrix_zero : seedMatrix ⟨0, card_seed_pos⟩ = B₀
  /-- (iii) The seed `ν(a, k)` obtained by mutating the seed `a` in direction `k`. -/
  next : Fin M → Fin n → Fin M
  /-- (iii) The permutation `π_{a,k}` relabelling `ν(a, k)` into the mutation. -/
  perm : Fin M → Fin n → Equiv.Perm (Fin n)
  /-- (T1) `μ_k(B̃_a) = B̃_{ν(a,k)}^{π_{a,k}}`. -/
  matrixMutation_eq : ∀ a k,
    matrixMutation hmn (seedMatrix a) k = relabelMatrix hmn (seedMatrix (next a k)) (perm a k)
  /-- (T2) `α_{ν(a,k)}(π_{a,k}(j)) = α_a(j)` for `j ≠ k`. -/
  seedVar_next : ∀ a k j, j ≠ k → seedVar (next a k) (perm a k j) = seedVar a j
  /-- (T3) The exchange relation in `L_m`. -/
  exchange : ∀ a k,
    var (seedVar a k) * var (seedVar (next a k) (perm a k k)) =
      TypeE.monomialPos (TypeE.extTuple var (seedVar a)) (seedMatrix a) k +
        TypeE.monomialNeg (TypeE.extTuple var (seedVar a)) (seedMatrix a) k
  /-- (D1) The `vᵢ` are pairwise distinct. -/
  var_injective : Function.Injective var
  /-- (D2) The sets `α_a([1, n])` are pairwise distinct. -/
  range_seedVar_injective : Function.Injective fun a => Set.range (seedVar a)
  /-- (D3) Every variable index lies in some `α_a([1, n])`. -/
  exists_mem_range_seedVar : ∀ c, ∃ a, c ∈ Set.range (seedVar a)
  /-- (D4) Every seed is reached from the seed `1` by transitions. -/
  exists_foldl_next : ∀ a, ∃ ks : List (Fin n), ks.foldl next ⟨0, card_seed_pos⟩ = a

/-- Relabelling a seed by the identity permutation does nothing. -/
@[simp]
theorem SeedData.relabel_one {F : Type*} {hmn : n ≤ m} (S : SeedData F m n) :
    S.relabel hmn 1 = S := by
  refine SeedData.ext (funext fun i => ?_) ?_
  · rw [SeedData.relabel_extCluster, Equiv.Perm.extendMutable_one, Equiv.Perm.one_apply]
  · rw [SeedData.relabel_extExchangeMatrix, relabelMatrix_one]

namespace ExchangeCertificate

variable {hmn : n ≤ m} {B₀ : Matrix (Fin m) (Fin n) ℤ} {N M : ℕ}

/-- The seed `S_a = ((ev(w^a_1), …, ev(w^a_m)), B̃_a)` of the seed `a` of a certificate, evaluated
at `x̃`. -/
@[cluster_algebras "lem_exc_certificate_sound"]
noncomputable def seed (C : ExchangeCertificate hmn B₀ N M) {F : Type*} [Field F]
    (x : Fin m → F) (a : Fin M) : SeedData F m n where
  extCluster i := LaurentRing.eval x (TypeE.extTuple C.var (C.seedVar a) i)
  extExchangeMatrix := C.seedMatrix a

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem extTuple_castLE (v : Fin N → LaurentRing m) (α : Fin n → Fin N) (k : Fin n) :
    TypeE.extTuple v α (Fin.castLE hmn k) = v (α k) := by
  simp [TypeE.extTuple]

private theorem extTuple_of_le (v : Fin N → LaurentRing m) (α : Fin n → Fin N) {i : Fin m}
    (hi : n ≤ (i : ℕ)) : TypeE.extTuple v α i = LaurentRing.X i := by
  simp [TypeE.extTuple, not_lt.2 hi]

private theorem monomialPos_eq_prod {R : Type*} [CommMonoid R] (w : Fin m → R)
    (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    TypeE.monomialPos w B k = ∏ i, w i ^ (B i k).toNat := by
  rw [TypeE.monomialPos, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · rw [Int.toNat_eq_zero.2 (not_lt.1 h), pow_zero]

private theorem monomialNeg_eq_prod {R : Type*} [CommMonoid R] (w : Fin m → R)
    (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    TypeE.monomialNeg w B k = ∏ i, w i ^ (-B i k).toNat := by
  rw [TypeE.monomialNeg, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · rw [Int.toNat_eq_zero.2 (by omega), pow_zero]

private theorem map_monomialPos (φ : LaurentRing m →+* F) (w : Fin m → LaurentRing m)
    (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    φ (TypeE.monomialPos w B k) = exchangeMonomialPos (fun i => φ (w i)) B k := by
  simp only [monomialPos_eq_prod, exchangeMonomialPos_eq_prod, map_prod, map_pow]

private theorem map_monomialNeg (φ : LaurentRing m →+* F) (w : Fin m → LaurentRing m)
    (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    φ (TypeE.monomialNeg w B k) = exchangeMonomialNeg (fun i => φ (w i)) B k := by
  simp only [monomialNeg_eq_prod, exchangeMonomialNeg_eq_prod, map_prod, map_pow]

variable (C : ExchangeCertificate hmn B₀ N M)

private theorem seed_extCluster_castLE (x : Fin m → F) (a : Fin M) (k : Fin n) :
    (C.seed x a).extCluster (Fin.castLE hmn k) = LaurentRing.eval x (C.var (C.seedVar a k)) := by
  simp only [seed, extTuple_castLE]

private theorem seed_extCluster_of_le (x : Fin m → F) (a : Fin M) {i : Fin m}
    (hi : n ≤ (i : ℕ)) : (C.seed x a).extCluster i = x i := by
  simp only [seed, extTuple_of_le _ _ hi, LaurentRing.eval_X]

/-- The seed `S₁` of a certificate evaluated at `x̃` is `(x̃, B̃₀)`. -/
private theorem seed_zero {S : SeedData F m n} (hS : S.extExchangeMatrix = B₀) :
    C.seed S.extCluster ⟨0, C.card_seed_pos⟩ = S := by
  refine SeedData.ext (funext fun i => ?_) (C.seedMatrix_zero.trans hS.symm)
  by_cases hi : (i : ℕ) < n
  · obtain ⟨i, rfl⟩ : ∃ j : Fin n, Fin.castLE hmn j = i := ⟨⟨i, hi⟩, rfl⟩
    rw [seed_extCluster_castLE, C.seedVar_zero, C.var_castLE, LaurentRing.eval_X]
  · exact seed_extCluster_of_le C _ _ (not_lt.1 hi)

/-- If the `k`th entry of `S_a` is nonzero, then `μ_k(S_a) = S_{ν(a,k)}^{π_{a,k}}`. -/
private theorem seedMutation_seed (x : Fin m → F) (φ : LaurentRing m →+* F)
    (hφ : ⇑φ = LaurentRing.eval x) (a : Fin M) (k : Fin n)
    (hk : (C.seed x a).extCluster (Fin.castLE hmn k) ≠ 0) :
    seedMutation hmn (C.seed x a) k = (C.seed x (C.next a k)).relabel hmn (C.perm a k) := by
  have hS : ∀ b, (C.seed x b).extCluster =
      fun i => φ (TypeE.extTuple C.var (C.seedVar b) i) := fun b => by
    funext i
    simp [seed, hφ]
  refine SeedData.ext (funext fun j => ?_) (C.matrixMutation_eq a k)
  simp only [seedMutation, SeedData.relabel_extCluster]
  by_cases hj : (j : ℕ) < n
  · obtain ⟨j, rfl⟩ : ∃ j' : Fin n, Fin.castLE hmn j' = j := ⟨⟨j, hj⟩, rfl⟩
    rw [Equiv.Perm.extendMutable_castLE, seed_extCluster_castLE C x (C.next a k)]
    by_cases hjk : j = k
    · subst hjk
      rw [Function.update_self, eq_comm, eq_div_iff hk]
      have h := congrArg φ (C.exchange a j)
      rw [map_mul, map_add, map_monomialPos, map_monomialNeg, ← hS] at h
      rw [seed_extCluster_castLE] at hk ⊢
      rw [show (C.seed x a).extExchangeMatrix = C.seedMatrix a from rfl, ← h, hφ, mul_comm]
    · rw [Function.update_of_ne (fun h => hjk (Fin.castLE_injective hmn h)),
        seed_extCluster_castLE, C.seedVar_next a k j hjk]
  · have hjk : j ≠ Fin.castLE hmn k := by
      rintro rfl
      exact hj (by simp)
    rw [Function.update_of_ne hjk, Equiv.Perm.extendMutable_apply_of_le hmn _ (not_lt.1 hj),
      seed_extCluster_of_le C _ _ (not_lt.1 hj), seed_extCluster_of_le C _ _ (not_lt.1 hj)]

/-- If `Σ(t) = S_a^π` and `t —q— t'`, then `Σ(t') = S_{a'}^{π' ∘ π}` with `k = π(q)`,
`a' = ν(a, k)`, `π' = π_{a,k}`. -/
private theorem apply_eq_relabel_seed_of_adj {P : RegularTree n → SeedData F m n}
    (hP : IsSeedPattern K hmn P) (x : Fin m → F) (φ : LaurentRing m →+* F)
    (hφ : ⇑φ = LaurentRing.eval x) {t t' : RegularTree n} {q : Fin n}
    (hq : RegularTree.Adj q t t') {a : Fin M} {π : Equiv.Perm (Fin n)}
    (h : P t = (C.seed x a).relabel hmn π) :
    P t' = (C.seed x (C.next a (π q))).relabel hmn (C.perm a (π q) * π) := by
  have hne : (C.seed x a).extCluster (Fin.castLE hmn (π q)) ≠ 0 := by
    have := (hP.1 t).1.1.ne_zero (Fin.castLE hmn q)
    rwa [h, SeedData.relabel_extCluster, Equiv.Perm.extendMutable_castLE] at this
  rw [hP.2 q t t' hq, h, seedMutation_relabel, seedMutation_seed C x φ hφ a (π q) hne,
    SeedData.relabel_relabel]

/-- Evaluation at the extended cluster of a seed of a pattern is an injective ring
homomorphism. -/
private theorem exists_ringHom [CharZero K] {P : RegularTree n → SeedData F m n}
    (hP : IsSeedPattern K hmn P) (t₀ : RegularTree n) :
    ∃ φ : LaurentRing m →+* F, ⇑φ = LaurentRing.eval (P t₀).extCluster ∧
      Function.Injective φ := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  exact LaurentRing.exists_ringHom_eval_injective
    ((hP.1 t₀).1.1.restrictScalars (algebraMap ℚ K).injective)

/-- The cluster variables of `S_a^π` are `{ev(v_c) : c ∈ α_a([1, n])}`. -/
private theorem clusterVariables_relabel_seed (x : Fin m → F) (a : Fin M)
    (π : Equiv.Perm (Fin n)) :
    clusterVariables hmn ((C.seed x a).relabel hmn π) =
      (fun c => LaurentRing.eval x (C.var c)) '' Set.range (C.seedVar a) := by
  ext z
  simp only [clusterVariables, Set.mem_range, Set.mem_image, SeedData.cluster_relabel]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨π i, rfl⟩, by rw [cluster, seed_extCluster_castLE]⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨π⁻¹ i, by
      rw [cluster, Equiv.Perm.coe_inv, Equiv.apply_symm_apply, seed_extCluster_castLE]⟩

/-- **An exchange certificate describes the seed pattern**, (a): if `Σ(t₀) = (x̃, B̃₀)`, every
seed of `Σ` is a relabelling `S_a^π` of one of the seeds `S_a` of the certificate evaluated at
`x̃`. -/
@[cluster_algebras "lem_exc_certificate_sound"]
theorem exists_apply_eq_relabel_seed [CharZero K] (C : ExchangeCertificate hmn B₀ N M)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t₀ : RegularTree n}
    (ht₀ : (P t₀).extExchangeMatrix = B₀) (t : RegularTree n) :
    ∃ (a : Fin M) (π : Equiv.Perm (Fin n)), P t = (C.seed (P t₀).extCluster a).relabel hmn π := by
  obtain ⟨φ, hφ, -⟩ := exists_ringHom hP t₀
  obtain ⟨d, s, κ, hs0, hsd, hadj⟩ := RegularTree.exists_walk t₀ t
  have key : ∀ i (hi : i ≤ d), ∃ (a : Fin M) (π : Equiv.Perm (Fin n)),
      P (s ⟨i, by omega⟩) = (C.seed (P t₀).extCluster a).relabel hmn π := by
    intro i hi
    induction i with
    | zero =>
      refine ⟨⟨0, C.card_seed_pos⟩, 1, ?_⟩
      rw [SeedData.relabel_one, C.seed_zero ht₀]
      exact congrArg P hs0
    | succ i ih =>
      obtain ⟨a, π, h⟩ := ih (by omega)
      exact ⟨_, _, apply_eq_relabel_seed_of_adj C hP _ φ hφ (hadj ⟨i, by omega⟩) h⟩
  obtain ⟨a, π, h⟩ := key d le_rfl
  exact ⟨a, π, hsd ▸ h⟩

/-- **An exchange certificate describes the seed pattern**, (b): if `Σ(t₀) = (x̃, B̃₀)`, every
seed `S_a` of the certificate evaluated at `x̃` occurs, up to relabelling, as a seed of `Σ`. -/
@[cluster_algebras "lem_exc_certificate_sound"]
theorem exists_relabel_seed_eq_apply [CharZero K] (C : ExchangeCertificate hmn B₀ N M)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t₀ : RegularTree n}
    (ht₀ : (P t₀).extExchangeMatrix = B₀) (a : Fin M) :
    ∃ (t : RegularTree n) (π : Equiv.Perm (Fin n)),
      (C.seed (P t₀).extCluster a).relabel hmn π = P t := by
  obtain ⟨φ, hφ, -⟩ := exists_ringHom hP t₀
  obtain ⟨ks, rfl⟩ := C.exists_foldl_next a
  suffices ∀ (ks : List (Fin n)) (b : Fin M) (t : RegularTree n) (π : Equiv.Perm (Fin n)),
      P t = (C.seed (P t₀).extCluster b).relabel hmn π →
        ∃ (t' : RegularTree n) (π' : Equiv.Perm (Fin n)),
          P t' = (C.seed (P t₀).extCluster (ks.foldl C.next b)).relabel hmn π' by
    obtain ⟨t, π, h⟩ := this ks _ t₀ 1 (by rw [SeedData.relabel_one, C.seed_zero ht₀])
    exact ⟨t, π, h.symm⟩
  intro ks
  induction ks with
  | nil => exact fun b t π h => ⟨t, π, h⟩
  | cons k ks ih =>
    intro b t π h
    obtain ⟨t', ht'⟩ := t.exists_adj (π⁻¹ k)
    have h' := apply_eq_relabel_seed_of_adj C hP _ φ hφ ht' h
    rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h'
    exact ih _ _ _ h'

/-- The clusters of a pattern with a certificate are the evaluated certificate clusters. -/
theorem patternClusters_eq_range [CharZero K] (C : ExchangeCertificate hmn B₀ N M)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t₀ : RegularTree n}
    (ht₀ : (P t₀).extExchangeMatrix = B₀) :
    patternClusters hmn P = Set.range (fun a => (fun c => LaurentRing.eval (P t₀).extCluster
      (C.var c)) '' Set.range (C.seedVar a)) := by
  ext Y
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨a, π, h⟩ := C.exists_apply_eq_relabel_seed hP ht₀ t
    exact ⟨a, by dsimp only; rw [h, clusterVariables_relabel_seed]⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨t, π, h⟩ := C.exists_relabel_seed_eq_apply hP ht₀ a
    exact ⟨t, by dsimp only; rw [← h, clusterVariables_relabel_seed]⟩

/-- The cluster variables of a pattern with a certificate are the evaluated certificate
variables. -/
theorem patternClusterVariables_eq_range [CharZero K] (C : ExchangeCertificate hmn B₀ N M)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t₀ : RegularTree n}
    (ht₀ : (P t₀).extExchangeMatrix = B₀) :
    patternClusterVariables hmn P =
      Set.range (fun c => LaurentRing.eval (P t₀).extCluster (C.var c)) := by
  ext z
  simp only [patternClusterVariables, Set.mem_iUnion]
  constructor
  · rintro ⟨t, hz⟩
    obtain ⟨a, π, h⟩ := C.exists_apply_eq_relabel_seed hP ht₀ t
    rw [h, clusterVariables_relabel_seed] at hz
    obtain ⟨c, -, rfl⟩ := hz
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨a, hc⟩ := C.exists_mem_range_seedVar c
    obtain ⟨t, π, h⟩ := C.exists_relabel_seed_eq_apply hP ht₀ a
    refine ⟨t, ?_⟩
    rw [← h, clusterVariables_relabel_seed]
    exact ⟨c, hc, rfl⟩

/-- **An exchange certificate describes the seed pattern**, (c): if `Σ(t₀) = (x̃, B̃₀)`, then `Σ`
is of finite type, its set of cluster variables is `{ev(v₁), …, ev(v_N)}` with exactly `N`
elements, and its clusters are the `M` sets `{ev(v_c) : c ∈ α_a([1, n])}`, exactly `M` of
them. -/
@[cluster_algebras "lem_exc_certificate_sound"]
theorem isFiniteType_and_encard [CharZero K] (C : ExchangeCertificate hmn B₀ N M)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t₀ : RegularTree n}
    (ht₀ : (P t₀).extExchangeMatrix = B₀) :
    IsFiniteType P ∧
      patternClusterVariables hmn P = Set.range (fun c => LaurentRing.eval (P t₀).extCluster
        (C.var c)) ∧
      (patternClusterVariables hmn P).encard = N ∧
      patternClusters hmn P = Set.range (fun a => (fun c => LaurentRing.eval (P t₀).extCluster
        (C.var c)) '' Set.range (C.seedVar a)) ∧
      (patternClusters hmn P).encard = M := by
  obtain ⟨φ, hφ, hinj⟩ := exists_ringHom hP t₀
  set g : Fin N → F := fun c => LaurentRing.eval (P t₀).extCluster (C.var c) with hg_def
  have hg : Function.Injective g := fun c c' h =>
    C.var_injective (hinj (by simpa only [hg_def, hφ] using h))
  have hclus := C.patternClusters_eq_range hP ht₀
  have hvars := C.patternClusterVariables_eq_range hP ht₀
  refine ⟨?_, hvars, ?_, hclus, ?_⟩
  · refine (Set.finite_range fun p : Fin M × Equiv.Perm (Fin n) =>
      (C.seed (P t₀).extCluster p.1).relabel hmn p.2).subset ?_
    rintro _ ⟨t, rfl⟩
    obtain ⟨a, π, h⟩ := C.exists_apply_eq_relabel_seed hP ht₀ t
    exact ⟨(a, π), h.symm⟩
  · rw [hvars, ← Set.image_univ, hg.encard_image, Set.encard_univ]
    simp
  · have h : Function.Injective fun a => g '' Set.range (C.seedVar a) :=
      (Set.image_injective.2 hg).comp C.range_seedVar_injective
    rw [hclus, ← Set.image_univ, h.encard_image, Set.encard_univ]
    simp

/-- If some seed of a pattern has exchange matrix a relabelling of `B̃₀`, a certificate for `B̃₀`
counts the cluster variables and clusters of the pattern. -/
theorem encard_of_extExchangeMatrix_eq_relabelMatrix [CharZero K]
    (C : ExchangeCertificate hmn B₀ N M) {Q : RegularTree n → SeedData F m n}
    (hQ : IsSeedPattern K hmn Q) {t : RegularTree n} {ρ : Equiv.Perm (Fin n)}
    (hQt : (Q t).extExchangeMatrix = relabelMatrix hmn B₀ ρ) :
    (patternClusterVariables hmn Q).encard = N ∧ (patternClusters hmn Q).encard = M := by
  obtain ⟨R, hR, hRt⟩ := hQ.exists_apply_eq_relabel hmn t ρ⁻¹
  have hRB : (R t).extExchangeMatrix = B₀ := by
    rw [hRt, SeedData.relabel_extExchangeMatrix, hQt]
    exact relabelMatrix_relabelMatrix_inv hmn B₀ ρ
  obtain ⟨-, -, hN, -, hM⟩ := C.isFiniteType_and_encard hR hRB
  obtain ⟨-, hvars, hclus, -⟩ := hQ.range_eq_of_apply_eq_relabel hmn hR hRt
  exact ⟨hvars ▸ hN, hclus ▸ hM⟩

end ExchangeCertificate

/-- A labeled seed with the indeterminates of `K(X₁, …, Xₘ)` as cluster and a relabelling of an
extended skew-symmetrizable matrix as exchange matrix extends to a seed pattern. -/
theorem exists_isSeedPattern_fractionRing (K : Type*) [Field K] [CharZero K] (hmn : n ≤ m)
    {B : Matrix (Fin m) (Fin n) ℤ} (hB : ExtSkewSymmetrizable hmn B) (t : RegularTree n)
    (ρ : Equiv.Perm (Fin n)) :
    ∃ Q : RegularTree n → SeedData (FractionRing (MvPolynomial (Fin m) K)) m n,
      IsSeedPattern K hmn Q ∧ (Q t).extExchangeMatrix = relabelMatrix hmn B ρ := by
  obtain ⟨Q, hQ, hQt⟩ := exists_isSeedPattern hmn t
    (⟨isFreeGeneratingTuple_X (m := m) K, hB.relabelMatrix hmn ρ⟩ : IsLabeledSeed K hmn
      (⟨fun i => algebraMap (MvPolynomial (Fin m) K) (FractionRing (MvPolynomial (Fin m) K))
        (MvPolynomial.X i), relabelMatrix hmn B ρ⟩ : SeedData _ m n))
  exact ⟨Q, hQ, by rw [hQt]⟩

/-- **Finite type and counts from a pair of certificates.** Let `X` be a Dynkin symbol, `B₀` a
skew-symmetrizable reference matrix for `X`, and `B̃₁` an `m₁ × X.rank` integer matrix with
principal part `B₀` whose rows span `ℤ^{X.rank}` (possibly `B̃₁ = B₀`). If there are exchange
certificates for `B₀` and for `B̃₁`, both with `N` variables and `M` seeds, then every seed
pattern of type `X` is of finite type, has exactly `N` cluster variables and exactly `M`
clusters. -/
@[cluster_algebras "lem_exc_counts_from_certificates"]
theorem ExchangeCertificate.isFiniteType_and_encard_of_isPatternOfType {K F : Type*} [Field K]
    [CharZero K] [Field F] [Algebra K F] {X : DynkinSymbol}
    {B₀ : Matrix (Fin X.rank) (Fin X.rank) ℤ} (hB₀ : SkewSymmetrizable B₀)
    (href : IsReferenceMatrix X B₀) {m₁ : ℕ} (hm₁ : X.rank ≤ m₁)
    {B₁ : Matrix (Fin m₁) (Fin X.rank) ℤ} (hB₁ : principalPart hm₁ B₁ = B₀)
    (hspan : Submodule.span ℤ (Set.range B₁) = ⊤) {N M : ℕ}
    (C₀ : ExchangeCertificate le_rfl B₀ N M) (C₁ : ExchangeCertificate hm₁ B₁ N M)
    (hmn : X.rank ≤ m) {P : RegularTree X.rank → SeedData F m X.rank}
    (hP : IsSeedPattern K hmn P) (hX : IsPatternOfType hmn P [X]) :
    IsFiniteType P ∧ (patternClusterVariables hmn P).encard = N ∧
      (patternClusters hmn P).encard = M := by
  obtain ⟨t, ρ, hρ⟩ := hP.exists_principalPart_eq_relabelMatrix href hmn hX
  have hB₀ext : ExtSkewSymmetrizable (le_rfl : X.rank ≤ X.rank) B₀ := by
    simpa [ExtSkewSymmetrizable] using hB₀
  obtain ⟨Q₀, hQ₀, hQ₀t⟩ :=
    exists_isSeedPattern_fractionRing K (le_rfl : X.rank ≤ X.rank) hB₀ext t ρ
  have hB₁ext : ExtSkewSymmetrizable hm₁ B₁ := by
    change SkewSymmetrizable (principalPart hm₁ B₁)
    rwa [hB₁]
  obtain ⟨Q₁, hQ₁, hQ₁t⟩ := exists_isSeedPattern_fractionRing K hm₁ hB₁ext t ρ
  obtain ⟨hN₀, hM₀⟩ := C₀.encard_of_extExchangeMatrix_eq_relabelMatrix hQ₀ hQ₀t
  obtain ⟨hN₁, hM₁⟩ := C₁.encard_of_extExchangeMatrix_eq_relabelMatrix hQ₁ hQ₁t
  have hB₁t : principalPart hm₁ (Q₁ t).extExchangeMatrix =
      principalPart hmn (P t).extExchangeMatrix := by
    rw [hQ₁t, hρ, ← hB₁]
    exact principalPart_relabelMatrix hm₁ B₁ ρ
  have hZ₁ : ZSpanCondition (P t).extExchangeMatrix (Q₁ t).extExchangeMatrix := by
    rw [hQ₁t]
    exact zSpanCondition_of_span_eq_top (span_range_relabelMatrix hm₁ hspan ρ) _
  have h₁ := encard_patternClusterVariables_le_of_cluster_eq hm₁ hmn (P := Q₁) (P' := P)
    (hQ₁.cluster_eq_of_cluster_eq_of_zSpanCondition hm₁ hmn hP hB₁t hZ₁)
  have hB₀t : principalPart hmn (P t).extExchangeMatrix =
      principalPart le_rfl (Q₀ t).extExchangeMatrix := by
    rw [hQ₀t, hρ]
    rfl
  have hZ₀ : ZSpanCondition (Q₀ t).extExchangeMatrix (P t).extExchangeMatrix := by
    rw [hQ₀t, ← hρ]
    exact zSpanCondition_principalPart hmn _
  have h₀ := encard_patternClusterVariables_le_of_cluster_eq hmn le_rfl (P := P) (P' := Q₀)
    (hP.cluster_eq_of_cluster_eq_of_zSpanCondition hmn le_rfl hQ₀ hB₀t hZ₀)
  rw [hN₁, hM₁] at h₁
  rw [hN₀, hM₀] at h₀
  have hN : (patternClusterVariables hmn P).encard = N := le_antisymm h₁.1 h₀.1
  exact ⟨(hP.isFiniteType_iff hmn).2 (Set.finite_of_encard_eq_coe hN), hN,
    le_antisymm h₁.2 h₀.2⟩

end ClusterAlgebras

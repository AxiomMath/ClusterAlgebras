/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Defs.MatrixMutationEquiv
public import ClusterAlgebras.LaurentPhenomenon.Trivialization
public import ClusterAlgebras.RankTwo.Shape
public import ClusterAlgebras.Semifield.Basic
public import ClusterAlgebras.FiniteType.Basic
public import ClusterAlgebras.Subpattern.SeedReindex
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The rank-two case and `2`-finiteness

FWZ's Section 5.1. A seed of rank two is mutated alternately in its two directions; the
sequence of seeds and the cluster variables it produces are its *zigzag*. When the exchange
matrix is `±[[0, b], [-c, 0]]` with `bc ≥ 4`, a homomorphism to the *max-plus semifield*
turns the exchange relations along the zigzag into a real recurrence taking infinitely many
values, so the pattern has infinitely many cluster variables. Freezing all but two indices
then shows that the exchange matrices of a pattern of finite type are *`2`-finite*.

## Main definitions

* `ClusterAlgebras.zigzagSeed`, `ClusterAlgebras.zigzagVar`: the zigzag of a seed of rank two.
* `ClusterAlgebras.MaxPlusSemifield`: the max-plus semifield `U`.
* `ClusterAlgebras.weylS₁`, `ClusterAlgebras.weylS₂`: the generators of the rank-two Weyl group.
* `ClusterAlgebras.IsTwoFinite`: a `2`-finite matrix.

## Main statements

* `ClusterAlgebras.IsSeedPattern.infinite_patternClusterVariables_of_rankTwo`: a rank-two
  pattern with `bc ≥ 4` has infinitely many cluster variables.
* `ClusterAlgebras.finite_weylGroup_iff`: the rank-two Weyl group is finite exactly when
  `bc ≤ 3`.
* `ClusterAlgebras.IsSeedPattern.isTwoFinite_of_isFiniteType`: the exchange matrices of a
  pattern of finite type are `2`-finite.

## Implementation notes

* FWZ's positions `1` and `2` are `0` and `1` in `Fin 2`, so the direction `ℓ(k)` of the
  `k`-th mutation is `0` for even `k` and `1` for odd `k`.
* The max-plus semifield is `Multiplicative ℝ` with the auxiliary addition
  `u^r ⊕ u^s = u^{max(r, s)}`; `MaxPlusSemifield.u r` is `u^r`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-! ### The zigzag of a seed of rank two -/

/-- The direction `ℓ(k)` of the `k`-th mutation of the zigzag: `0` for even `k` and `1` for odd
`k`. -/
@[cluster_algebras "def_rank_two_zigzag"]
def zigzagDir (k : ℕ) : Fin 2 :=
  if Even k then 0 else 1

/-- The seeds of the **zigzag** of a seed `S` of rank two: `S₀ = S` and
`S_{k+1} = μ_{ℓ(k)}(S_k)`. -/
@[cluster_algebras "def_rank_two_zigzag"]
def zigzagSeed (hm : 2 ≤ m) (S : SeedData F m 2) : ℕ → SeedData F m 2
  | 0 => S
  | k + 1 => seedMutation hm (zigzagSeed hm S k) (zigzagDir k)

/-- The elements `v_k` of the **zigzag** of a seed `S` of rank two: `v₀` and `v₁` are the
entries of the extended cluster of `S` in its two mutable positions, and `v_{k+2}` is the entry
in position `ℓ(k)` of the extended cluster of `S_{k+1}`, the one the `k`-th mutation
produced. -/
@[cluster_algebras "def_rank_two_zigzag"]
def zigzagVar (hm : 2 ≤ m) (S : SeedData F m 2) : ℕ → F
  | 0 => S.extCluster (Fin.castLE hm 0)
  | 1 => S.extCluster (Fin.castLE hm 1)
  | k + 2 => (zigzagSeed hm S (k + 1)).extCluster (Fin.castLE hm (zigzagDir k))

/-- The exponent `e_k` of the zigzag's exchange relations: `|b₂₁|` for even `k` and `|b₁₂|` for
odd `k`, read off the exchange matrix of the initial seed. -/
@[cluster_algebras "lem_rank_two_zigzag"]
def zigzagExp (hm : 2 ≤ m) (S : SeedData F m 2) (k : ℕ) : ℕ :=
  if Even k then (S.extExchangeMatrix (Fin.castLE hm 1) 0).natAbs
  else (S.extExchangeMatrix (Fin.castLE hm 0) 1).natAbs

/-- The direction of the zigzag has period two. -/
theorem zigzagDir_add_two (k : ℕ) : zigzagDir (k + 2) = zigzagDir k := by
  simp [zigzagDir, Nat.even_add]

/-- Consecutive directions of the zigzag differ. -/
theorem zigzagDir_succ_ne (k : ℕ) : zigzagDir (k + 1) ≠ zigzagDir k := by
  unfold zigzagDir
  rcases Nat.even_or_odd k with h | h
  · simp [h, Nat.even_add_one]
  · simp [Nat.not_even_iff_odd.2 h, h]

/-- Consecutive directions of the zigzag differ, read as row indices. -/
theorem castLE_zigzagDir_succ_ne (hm : 2 ≤ m) (k : ℕ) :
    Fin.castLE hm (zigzagDir (k + 1)) ≠ Fin.castLE hm (zigzagDir k) :=
  fun h => zigzagDir_succ_ne k (Fin.castLE_injective hm h)

/-- The zigzag starts at `S`. -/
@[simp] theorem zigzagSeed_zero (hm : 2 ≤ m) (S : SeedData F m 2) : zigzagSeed hm S 0 = S := rfl

/-- The `(k + 1)`-st seed of the zigzag is the mutation of the `k`-th in direction `ℓ(k)`. -/
theorem zigzagSeed_succ (hm : 2 ≤ m) (S : SeedData F m 2) (k : ℕ) :
    zigzagSeed hm S (k + 1) = seedMutation hm (zigzagSeed hm S k) (zigzagDir k) := rfl

/-- `v_{k+2}` is the entry in position `ℓ(k)` of `S_{k+1}`. -/
theorem zigzagVar_add_two (hm : 2 ≤ m) (S : SeedData F m 2) (k : ℕ) :
    zigzagVar hm S (k + 2) = (zigzagSeed hm S (k + 1)).extCluster (Fin.castLE hm (zigzagDir k)) :=
  rfl

/-- **The zigzag lists the cluster variables along a path**, part (a): each `S_k` is a labeled
seed with the frozen entries of the initial seed, carrying `v_k` in position `ℓ(k)` and `v_{k+1}`
in the other mutable position. The frozen entries are kept position by position, which is
stronger than keeping the set of frozen variables. -/
@[cluster_algebras "lem_rank_two_zigzag"]
theorem IsLabeledSeed.zigzagSeed_spec [CharZero K] (hm : 2 ≤ m) {S : SeedData F m 2}
    (hS : IsLabeledSeed K hm S) (k : ℕ) :
    IsLabeledSeed K hm (zigzagSeed hm S k) ∧
      (∀ i : Fin m, 2 ≤ (i : ℕ) → (zigzagSeed hm S k).extCluster i = S.extCluster i) ∧
      (zigzagSeed hm S k).extCluster (Fin.castLE hm (zigzagDir k)) = zigzagVar hm S k ∧
      (zigzagSeed hm S k).extCluster (Fin.castLE hm (zigzagDir (k + 1))) =
        zigzagVar hm S (k + 1) := by
  induction k with
  | zero => exact ⟨hS, fun _ _ => rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2, -, h4⟩ := ih
    refine ⟨h1.seedMutation hm _, fun i hi => ?_, ?_, ?_⟩
    · rw [zigzagSeed_succ, seedMutation_extCluster_of_ne, h2 i hi]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    · rw [zigzagSeed_succ, seedMutation_extCluster_of_ne _ _ (castLE_zigzagDir_succ_ne hm k), h4]
    · rw [zigzagDir_add_two, ← zigzagVar_add_two]

/-- **The zigzag lists the cluster variables along a path**, part (b): the exchange matrix of
`S_k` is `(-1)ᵏ B`, where `B` is the exchange matrix of the initial seed. -/
@[cluster_algebras "lem_rank_two_zigzag"]
theorem IsLabeledSeed.principalPart_zigzagSeed [CharZero K] (hm : 2 ≤ m) {S : SeedData F m 2}
    (hS : IsLabeledSeed K hm S) (k : ℕ) :
    principalPart hm (zigzagSeed hm S k).extExchangeMatrix =
      (-1 : ℤ) ^ k • principalPart hm S.extExchangeMatrix := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hSk := (hS.zigzagSeed_spec hm k).1
    change principalPart hm (matrixMutation hm (zigzagSeed hm S k).extExchangeMatrix
      (zigzagDir k)) = _
    have hsk : SkewSymmetrizable (principalPart hm (zigzagSeed hm S k).extExchangeMatrix) := hSk.2
    rw [principalPart_matrixMutation, hsk.matrixMutation_eq_neg_of_fin_two, ih, pow_succ, mul_comm,
      mul_smul, neg_one_smul]

/-- An index below `2` is one of the two positions `ℓ(k)`, `ℓ(k + 1)`. -/
theorem eq_castLE_zigzagDir_or (hm : 2 ≤ m) (k : ℕ) {i : Fin m} (hi : (i : ℕ) < 2) :
    i = Fin.castLE hm (zigzagDir k) ∨ i = Fin.castLE hm (zigzagDir (k + 1)) := by
  have hne := zigzagDir_succ_ne k
  have h1 := (zigzagDir k).isLt
  have h2 := (zigzagDir (k + 1)).isLt
  have hne' : (zigzagDir (k + 1) : ℕ) ≠ zigzagDir k := fun h => hne (Fin.ext h)
  simp only [Fin.ext_iff, Fin.val_castLE]
  omega

/-- The factorization of a product of powers of the entries of `S_k` into a monomial in the
frozen variables of `S` and a power of `v_{k+1}`. -/
theorem IsLabeledSeed.prod_zigzagSeed_pow [CharZero K] (hm : 2 ≤ m) {S : SeedData F m 2}
    (hS : IsLabeledSeed K hm S) (k : ℕ) (e : Fin m → ℕ)
    (he : e (Fin.castLE hm (zigzagDir k)) = 0) :
    ∏ i, (zigzagSeed hm S k).extCluster i ^ e i =
      (∏ i, S.extCluster i ^ (if 2 ≤ (i : ℕ) then e i else 0)) *
        zigzagVar hm S (k + 1) ^ e (Fin.castLE hm (zigzagDir (k + 1))) := by
  obtain ⟨-, h2, -, h4⟩ := hS.zigzagSeed_spec hm k
  rw [← Fintype.prod_ite_eq (Fin.castLE hm (zigzagDir (k + 1)))
    (fun i => zigzagVar hm S (k + 1) ^ e i), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : 2 ≤ (i : ℕ)
  · have hne : Fin.castLE hm (zigzagDir (k + 1)) ≠ i := by
      intro h
      rw [← h, Fin.val_castLE] at hi
      exact absurd (zigzagDir (k + 1)).isLt (by omega)
    rw [if_pos hi, if_neg hne, mul_one, h2 i hi]
  · rw [if_neg hi, pow_zero, one_mul]
    rcases eq_castLE_zigzagDir_or hm k (not_le.1 hi) with rfl | rfl
    · rw [if_neg (castLE_zigzagDir_succ_ne hm k), he, pow_zero]
    · rw [if_pos rfl, h4]

/-- **The zigzag lists the cluster variables along a path**, part (c): the exchange relations
`v_k v_{k+2} = p_k v_{k+1}^{e_k} + q_k` with monomials `p_k`, `q_k` in the frozen variables
`x₃, …, xₘ` of the initial seed with nonnegative exponents. -/
@[cluster_algebras "lem_rank_two_zigzag"]
theorem IsLabeledSeed.zigzagVar_exchange [CharZero K] (hm : 2 ≤ m) {S : SeedData F m 2}
    (hS : IsLabeledSeed K hm S) (k : ℕ) :
    ∃ p q : Fin m → ℕ, (∀ i : Fin m, (i : ℕ) < 2 → p i = 0 ∧ q i = 0) ∧
      zigzagVar hm S k * zigzagVar hm S (k + 2) =
        (∏ i, S.extCluster i ^ p i) * zigzagVar hm S (k + 1) ^ zigzagExp hm S k +
          ∏ i, S.extCluster i ^ q i := by
  obtain ⟨hT, -, h3, -⟩ := hS.zigzagSeed_spec hm k
  set T := zigzagSeed hm S k
  set l := zigzagDir k
  set l' := zigzagDir (k + 1)
  set a := T.extExchangeMatrix (Fin.castLE hm l') l with ha
  have hdiag : T.extExchangeMatrix (Fin.castLE hm l) l = 0 :=
    hT.extExchangeMatrix_castLE_self hm l
  have hx : T.extCluster (Fin.castLE hm l) ≠ 0 := hT.1.1.ne_zero _
  have hexp : a.natAbs = zigzagExp hm S k := by
    have hpp := congrFun (congrFun (hS.principalPart_zigzagSeed hm k) l') l
    simp only [principalPart, Matrix.smul_apply, Matrix.submatrix_apply, id, smul_eq_mul] at hpp
    rw [ha, hpp, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
    simp only [l, l', zigzagExp, zigzagDir]
    rcases Nat.even_or_odd k with he | ho
    · simp [he, Nat.even_add_one]
    · simp [Nat.not_even_iff_odd.2 ho, ho]
  have hrel : zigzagVar hm S k * zigzagVar hm S (k + 2) =
      exchangeMonomialPos T.extCluster T.extExchangeMatrix l +
        exchangeMonomialNeg T.extCluster T.extExchangeMatrix l := by
    rw [zigzagVar_add_two, zigzagSeed_succ, seedMutation_extCluster_castLE_self, ← h3,
      mul_div_cancel₀ _ hx]
  have hd1 : (T.extExchangeMatrix (Fin.castLE hm l) l).toNat = 0 := by rw [hdiag]; rfl
  have hd2 : (-T.extExchangeMatrix (Fin.castLE hm l) l).toNat = 0 := by rw [hdiag]; rfl
  rw [hrel, exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod,
    hS.prod_zigzagSeed_pow hm k _ hd1, hS.prod_zigzagSeed_pow hm k _ hd2, ← ha, ← hexp]
  set ep : Fin m → ℕ := fun i => if 2 ≤ (i : ℕ) then (T.extExchangeMatrix i l).toNat else 0
  set en : Fin m → ℕ := fun i => if 2 ≤ (i : ℕ) then (-T.extExchangeMatrix i l).toNat else 0
  have hp : ∀ i : Fin m, (i : ℕ) < 2 → ep i = 0 ∧ en i = 0 :=
    fun i hi => ⟨if_neg (by omega), if_neg (by omega)⟩
  rcases le_or_gt 0 a with h | h
  · refine ⟨ep, en, hp, ?_⟩
    rw [show a.toNat = a.natAbs by omega, Int.toNat_eq_zero.2 (by omega), pow_zero, mul_one]
  · refine ⟨en, ep, fun i hi => (hp i hi).symm, ?_⟩
    rw [Int.toNat_eq_zero.2 h.le, pow_zero, mul_one, add_comm,
      show (-a).toNat = a.natAbs by omega]

/-! ### The max-plus semifield -/

/-- The **max-plus semifield** `U`: the set `ℝ`, written multiplicatively as `{u^r : r ∈ ℝ}`,
with product `u^r u^s = u^{r+s}` and auxiliary addition `u^r ⊕ u^s = u^{max(r, s)}`. The
underlying multiplicative group is `Multiplicative ℝ`. -/
@[cluster_algebras "def_max_plus_semifield"]
def MaxPlusSemifield : Type :=
  Multiplicative ℝ

namespace MaxPlusSemifield

/-- The element `u^r` of the max-plus semifield. -/
@[cluster_algebras "def_max_plus_semifield"]
def u (r : ℝ) : MaxPlusSemifield :=
  Multiplicative.ofAdd r

/-- The exponent `r` of an element `u^r` of the max-plus semifield. -/
def exponent (p : MaxPlusSemifield) : ℝ :=
  Multiplicative.toAdd p

/-- The exponent of `u^r` is `r`. -/
@[simp]
theorem exponent_u (r : ℝ) : exponent (u r) = r :=
  rfl

/-- Every element of the max-plus semifield is `u^r` for its exponent `r`. -/
@[simp]
theorem u_exponent (p : MaxPlusSemifield) : u (exponent p) = p :=
  rfl

/-- The product of the max-plus semifield, `u^r u^s = u^{r+s}`: the group `Multiplicative ℝ`. -/
@[cluster_algebras "def_max_plus_semifield"]
instance instCommGroup : CommGroup MaxPlusSemifield :=
  inferInstanceAs (CommGroup (Multiplicative ℝ))

/-- The auxiliary addition of the max-plus semifield, `u^r ⊕ u^s = u^{max(r, s)}`. -/
@[cluster_algebras "def_max_plus_semifield"]
instance instAdd : Add MaxPlusSemifield :=
  ⟨fun p q => u (max (exponent p) (exponent q))⟩

/-- `u^r u^s = u^{r+s}`. -/
@[simp]
theorem u_mul_u (r s : ℝ) : u r * u s = u (r + s) :=
  rfl

/-- `u^r ⊕ u^s = u^{max(r, s)}`. -/
@[simp]
theorem u_add_u (r s : ℝ) : u r + u s = u (max r s) :=
  rfl

/-- The exponent of a product is the sum of the exponents. -/
theorem exponent_mul (p q : MaxPlusSemifield) : exponent (p * q) = exponent p + exponent q :=
  rfl

/-- The exponent of an auxiliary sum is the maximum of the exponents. -/
theorem exponent_add (p q : MaxPlusSemifield) :
    exponent (p + q) = max (exponent p) (exponent q) :=
  rfl

/-- The auxiliary addition is commutative and associative, `max` being so. -/
instance instAddCommSemigroup : AddCommSemigroup MaxPlusSemifield where
  add_assoc p q r := by
    change u (max (max (exponent p) (exponent q)) (exponent r)) =
      u (max (exponent p) (max (exponent q) (exponent r)))
    rw [max_assoc]
  add_comm p q := by
    change u (max (exponent p) (exponent q)) = u (max (exponent q) (exponent p))
    rw [max_comm]

/-- **The max-plus semifield is a semifield.** Under the product it is the additive group of
`ℝ`, and `max(r, s) + t = max(r + t, s + t)` is the distributive law. -/
@[cluster_algebras "lem_max_plus_semifield"]
instance instFZSemifield : FZSemifield MaxPlusSemifield where
  __ := instCommGroup
  __ := instAddCommSemigroup
  add_mul p q r := by
    change u (max (exponent p) (exponent q) + exponent r) =
      u (max (exponent p + exponent r) (exponent q + exponent r))
    rw [max_add_add_right]

/-- The unit `u⁰` of the max-plus semifield has exponent `0`. -/
@[simp]
theorem exponent_one : exponent 1 = 0 :=
  rfl

/-- The exponent of `(u^r)ⁿ` is `n r`. -/
theorem exponent_pow (p : MaxPlusSemifield) (n : ℕ) : exponent (p ^ n) = n * exponent p := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, exponent_mul, ih]; push_cast; ring

end MaxPlusSemifield

/-- For positive integers `b, c` with `bc ≥ 4`, positive sequences `f, g` with
`f_j + f_{j+1} = c g_j`, `g_j + g_{j+1} = b f_{j+1}` and `f` strictly increasing. -/
private theorem exists_strictMono_maxPlus_solution {b c : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hbc : 4 ≤ b * c) :
    ∃ r₀ r₁ : ℝ, 0 < r₀ ∧ 0 < r₁ ∧ ∃ f g : ℕ → ℝ, f 0 = r₀ ∧ g 0 = r₁ ∧
      (∀ j, 0 < f j) ∧ (∀ j, 0 < g j) ∧ (∀ j, f j + f (j + 1) = c * g j) ∧
      (∀ j, g j + g (j + 1) = b * f (j + 1)) ∧ StrictMono f := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  rcases (Nat.lt_or_ge 4 (b * c)) with hlt | hle
  · set N : ℝ := (b : ℝ) * c with hN
    have hN5 : (5 : ℝ) ≤ N := by
      have : (5 : ℕ) ≤ b * c := hlt
      rw [hN]; exact_mod_cast this
    set s := Real.sqrt (N * (N - 4)) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = N * (N - 4) := Real.sq_sqrt (by nlinarith)
    set l : ℝ := ((N - 2) + s) / 2 with hl
    have hl1 : 1 < l := by rw [hl]; linarith
    have hlq : l * N = l ^ 2 + 2 * l + 1 := by rw [hl]; nlinarith
    refine ⟨c, l + 1, hc', by linarith, fun j => l ^ j * c, fun j => l ^ j * (l + 1),
      by simp, by simp, fun j => by positivity, fun j => by positivity, fun j => ?_,
      fun j => ?_, ?_⟩
    · dsimp only; rw [pow_succ]; ring
    · dsimp only; rw [pow_succ]
      have : (b : ℝ) * (l ^ j * l * c) = l ^ j * (l * N) := by rw [hN]; ring
      rw [this, hlq]; ring
    · intro i j hij
      have := pow_lt_pow_right₀ hl1 hij
      simp only
      nlinarith
  · have h4' : (b : ℝ) * c = 4 := by exact_mod_cast le_antisymm hle hbc
    refine ⟨1, b, one_pos, hb', fun j => 2 * j + 1, fun j => (j + 1) * b,
      by simp, by simp, fun j => by positivity, fun j => by positivity, fun j => ?_,
      fun j => ?_, ?_⟩
    · push_cast; nlinarith
    · push_cast; nlinarith
    · intro i j hij
      simp only
      have : (i : ℝ) < j := by exact_mod_cast hij
      linarith

/-- **A max-plus recurrence that grows.** For positive integers `b, c` with `bc ≥ 4`, and
`e_k = c` for even `k`, `e_k = b` for odd `k`, there are positive reals `r₀, r₁` such that the
real sequence determined by `r_k + r_{k+2} = max(e_k r_{k+1}, 0)` takes infinitely many
values. The recurrence determines the sequence from `r₀, r₁`, so it is stated for every
sequence satisfying it. -/
@[cluster_algebras "lem_max_plus_recurrence"]
theorem exists_maxPlus_recurrence_infinite {b c : ℕ} (hb : 0 < b) (hc : 0 < c) (hbc : 4 ≤ b * c) :
    ∃ r₀ r₁ : ℝ, 0 < r₀ ∧ 0 < r₁ ∧ ∀ r : ℕ → ℝ, r 0 = r₀ → r 1 = r₁ →
      (∀ k, r k + r (k + 2) = max ((if Even k then (c : ℝ) else b) * r (k + 1)) 0) →
        (Set.range r).Infinite := by
  obtain ⟨r₀, r₁, h₀, h₁, f, g, hf0, hg0, hfpos, hgpos, hfrec, hgrec, hmono⟩ :=
    exists_strictMono_maxPlus_solution hb hc hbc
  refine ⟨r₀, r₁, h₀, h₁, fun r hr0 hr1 hrec => ?_⟩
  have key : ∀ j, r (2 * j) = f j ∧ r (2 * j + 1) = g j := by
    intro j
    induction j with
    | zero => exact ⟨by simpa [hf0] using hr0, by simpa [hg0] using hr1⟩
    | succ j ih =>
      have e1 := hrec (2 * j)
      rw [if_pos (even_two_mul j), ih.2, ih.1, max_eq_left (by nlinarith [hgpos j])] at e1
      have h1 : r (2 * (j + 1)) = f (j + 1) := by
        rw [show 2 * j + 2 = 2 * (j + 1) by ring] at e1
        linarith [hfrec j]
      refine ⟨h1, ?_⟩
      have e2 := hrec (2 * j + 1)
      rw [if_neg (Nat.not_even_bit1 j), show 2 * j + 1 + 1 = 2 * (j + 1) by ring, h1, ih.2,
        max_eq_left (by nlinarith [hfpos (j + 1)]),
        show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring] at e2
      linarith [hgrec j]
  have hinj : Function.Injective fun j => r (2 * j) := fun i j hij => by
    simp only [(key _).1] at hij
    exact hmono.injective hij
  exact (Set.infinite_range_of_injective hinj).mono (by
    rintro _ ⟨j, rfl⟩
    exact ⟨_, rfl⟩)

/-- The elements of the zigzag of a seed `Σ(t₀)` of a rank-two pattern are cluster variables of
the pattern. -/
private theorem IsSeedPattern.zigzagVar_mem_patternClusterVariables [CharZero K] (hm : 2 ≤ m)
    {P : RegularTree 2 → SeedData F m 2} (hP : IsSeedPattern K hm P) (t₀ : RegularTree 2)
    (k : ℕ) : zigzagVar hm (P t₀) k ∈ patternClusterVariables hm P := by
  have hseed : ∀ k, ∃ t, P t = zigzagSeed hm (P t₀) k := by
    intro k
    induction k with
    | zero => exact ⟨t₀, rfl⟩
    | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨t', ht'⟩ := t.exists_adj (zigzagDir k)
      exact ⟨t', by rw [hP.2 _ _ _ ht', ht]; rfl⟩
  obtain ⟨t, ht⟩ := hseed k
  refine Set.mem_iUnion.2 ⟨t, zigzagDir k, ?_⟩
  simp only [cluster, ht]
  exact ((hP.1 t₀).zigzagSeed_spec hm k).2.2.1

omit [Field F] in
/-- The exponents of the zigzag of a seed with exchange matrix `ε [[0, b], [-c, 0]]` are `c` and
`b` alternately. -/
private theorem zigzagExp_eq_of_principalPart_eq (hm : 2 ≤ m) {S : SeedData F m 2} {ε b c : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hb : 0 < b) (hc : 0 < c)
    (hB : principalPart hm S.extExchangeMatrix = ε • !![0, b; -c, 0]) (k : ℕ) :
    (zigzagExp hm S k : ℝ) = if Even k then ((c.toNat : ℕ) : ℝ) else ((b.toNat : ℕ) : ℝ) := by
  have h10 : S.extExchangeMatrix (Fin.castLE hm 1) 0 = ε * -c := by
    simpa [principalPart] using congrFun (congrFun hB 1) 0
  have h01 : S.extExchangeMatrix (Fin.castLE hm 0) 1 = ε * b := by
    simpa [principalPart] using congrFun (congrFun hB 0) 1
  unfold zigzagExp
  split_ifs
  · rw [h10]
    congr 1
    rcases hε with rfl | rfl <;> simp <;> omega
  · rw [h01]
    congr 1
    rcases hε with rfl | rfl <;> simp <;> omega

open MaxPlusSemifield in
/-- **Tropicalizing the zigzag.** For a labeled seed `S` of rank two and reals `r₀, r₁`, there is
a function `G : F → ℝ` taking `v₀, v₁` to `r₀, r₁` and turning the exchange relations of the
zigzag into `G(v_k) + G(v_{k+2}) = max(e_k G(v_{k+1}), 0)`: the exponent of a homomorphism
from the universal semifield of `S` to the max-plus semifield. -/
private theorem IsLabeledSeed.exists_maxPlus_zigzag [CharZero K] (hm : 2 ≤ m)
    {S : SeedData F m 2} (hS : IsLabeledSeed K hm S) (r₀ r₁ : ℝ) :
    ∃ G : F → ℝ, G (zigzagVar hm S 0) = r₀ ∧ G (zigzagVar hm S 1) = r₁ ∧
      ∀ k, G (zigzagVar hm S k) + G (zigzagVar hm S (k + 2)) =
        max ((zigzagExp hm S k : ℝ) * G (zigzagVar hm S (k + 1))) 0 := by
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : Fact (AlgebraicIndependent ℚ S.extCluster) :=
    ⟨hS.1.1.restrictScalars (algebraMap ℚ K).injective⟩
  have hU : ∀ k i, (zigzagSeed hm S k).extCluster i ∈ universalSemifield S.extCluster := by
    intro k
    induction k with
    | zero => exact mem_universalSemifield_self _
    | succ k ih => exact seedMutation_extCluster_mem_universalSemifield hm ih _
  have hvU : ∀ k, zigzagVar hm S k ∈ universalSemifield S.extCluster := fun k =>
    (hS.zigzagSeed_spec hm k).2.2.1 ▸ hU k _
  set f : Fin m → MaxPlusSemifield := fun i =>
    if i = Fin.castLE hm 0 then u r₀ else if i = Fin.castLE hm 1 then u r₁ else 1 with hf
  set ψ := universalSemifieldLift S.extCluster f
  have hψ : ∀ i, ψ ⟨S.extCluster i, mem_universalSemifield_self _ i⟩ = f i :=
    universalSemifieldLift_apply_self f
  set G : F → ℝ := fun z =>
    if h : z ∈ universalSemifield S.extCluster then exponent (ψ ⟨z, h⟩) else 0
  have hGv : ∀ k, G (zigzagVar hm S k) = exponent (ψ ⟨_, hvU k⟩) := fun k => dif_pos (hvU k)
  have h10ne : (Fin.castLE hm 1 : Fin m) ≠ Fin.castLE hm 0 := by
    simp [Fin.ext_iff]
  have hmono : ∀ p : Fin m → ℕ, (∀ i : Fin m, (i : ℕ) < 2 → p i = 0) →
      ∏ i, f i ^ p i = 1 := by
    intro p hp
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : (i : ℕ) < 2
    · rw [hp i hi, pow_zero]
    · have h0 : i ≠ Fin.castLE hm 0 := fun h => by rw [h] at hi; simp at hi
      have h1 : i ≠ Fin.castLE hm 1 := fun h => by rw [h] at hi; simp at hi
      simp [hf, h0, h1]
  refine ⟨G, ?_, ?_, fun k => ?_⟩
  · rw [hGv]
    exact congrArg exponent (hψ (Fin.castLE hm 0)) |>.trans (by simp [hf])
  · rw [hGv]
    exact congrArg exponent (hψ (Fin.castLE hm 1)) |>.trans (by simp [hf, h10ne])
  obtain ⟨p, q, hpq, hrel⟩ := hS.zigzagVar_exchange hm k
  have key : (⟨_, hvU k⟩ : universalSemifield S.extCluster) * ⟨_, hvU (k + 2)⟩ =
      (∏ i, (⟨S.extCluster i, mem_universalSemifield_self _ i⟩ :
        universalSemifield S.extCluster) ^ p i) * ⟨_, hvU (k + 1)⟩ ^ zigzagExp hm S k +
      ∏ i, (⟨S.extCluster i, mem_universalSemifield_self _ i⟩ :
        universalSemifield S.extCluster) ^ q i := by
    apply Subtype.ext
    simp only [universalSemifield.coe_mul, universalSemifield.coe_add,
      universalSemifield.coe_pow, universalSemifield.coe_prod]
    exact hrel
  have key' := congrArg (fun z => exponent (ψ z)) key
  simp only [map_mul, map_add, map_prod, map_pow, hψ, hmono p (fun i hi => (hpq i hi).1),
    hmono q (fun i hi => (hpq i hi).2), one_mul, exponent_mul, exponent_add, exponent_pow,
    exponent_one] at key'
  simp only [hGv, key']

/-- **A rank-two pattern with `bc ≥ 4` has infinitely many cluster variables.** If the exchange
matrix of one seed of a seed pattern of rank two is `ε [[0, b], [-c, 0]]` with `ε = ±1` and
positive integers `b, c` with `bc ≥ 4`, then the pattern has infinitely many cluster variables,
and in particular it is not of finite type. -/
@[cluster_algebras "lem_rank_two_infinite"]
theorem IsSeedPattern.infinite_patternClusterVariables_of_rankTwo [CharZero K] (hm : 2 ≤ m)
    {P : RegularTree 2 → SeedData F m 2} (hP : IsSeedPattern K hm P) (t₀ : RegularTree 2)
    {ε b c : ℤ} (hε : ε = 1 ∨ ε = -1) (hb : 0 < b) (hc : 0 < c) (hbc : 4 ≤ b * c)
    (hB : principalPart hm (P t₀).extExchangeMatrix = ε • !![0, b; -c, 0]) :
    (patternClusterVariables hm P).Infinite ∧ ¬IsFiniteType P := by
  have hbc' : 4 ≤ b.toNat * c.toNat := by
    have : ((b.toNat * c.toNat : ℕ) : ℤ) = b * c := by
      push_cast [Int.toNat_of_nonneg hb.le, Int.toNat_of_nonneg hc.le]
      ring
    omega
  obtain ⟨r₀, r₁, -, -, hrec⟩ :=
    exists_maxPlus_recurrence_infinite (b := b.toNat) (c := c.toNat) (by omega) (by omega) hbc'
  obtain ⟨G, hG0, hG1, hGrec⟩ := (hP.1 t₀).exists_maxPlus_zigzag hm r₀ r₁
  have hinf := hrec (G ∘ zigzagVar hm (P t₀)) hG0 hG1 fun k => by
    simp only [Function.comp_apply, hGrec, zigzagExp_eq_of_principalPart_eq hm hε hb hc hB]
  have hrange : (Set.range (zigzagVar hm (P t₀))).Infinite :=
    Set.Infinite.of_image G (by rwa [← Set.range_comp])
  have hinfP : (patternClusterVariables hm P).Infinite :=
    hrange.mono (Set.range_subset_iff.2 (hP.zigzagVar_mem_patternClusterVariables hm t₀))
  exact ⟨hinfP, fun h => hinfP (h.finite_iUnion_clusterVariables hm)⟩

/-! ### The rank-two Weyl group -/

/-- The reflection `s₁ = [[-1, b], [0, 1]]`, an element of `GL₂(ℤ)` equal to its own
inverse. -/
@[cluster_algebras "prop_weyl_rank_two"]
def weylS₁ (b : ℤ) : GL (Fin 2) ℤ where
  val := !![-1, b; 0, 1]
  inv := !![-1, b; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The reflection `s₂ = [[1, 0], [c, -1]]`, an element of `GL₂(ℤ)` equal to its own
inverse. -/
@[cluster_algebras "prop_weyl_rank_two"]
def weylS₂ (c : ℤ) : GL (Fin 2) ℤ where
  val := !![1, 0; c, -1]
  inv := !![1, 0; c, -1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `s₁² = 1`. -/
theorem weylS₁_mul_self (b : ℤ) : weylS₁ b * weylS₁ b = 1 :=
  Units.ext (weylS₁ b).val_inv

/-- `s₂² = 1`. -/
theorem weylS₂_mul_self (c : ℤ) : weylS₂ c * weylS₂ c = 1 :=
  Units.ext (weylS₂ c).val_inv

/-- The product `w = s₁ s₂ = [[bc - 1, -b], [c, -1]]`. -/
theorem val_weylS₁_mul_weylS₂ (b c : ℤ) :
    ((weylS₁ b * weylS₂ c : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![b * c - 1, -b; c, -1] := by
  rw [Units.val_mul]
  change !![-1, b; 0, 1] * !![1, 0; c, -1] = _
  rw [Matrix.mul_fin_two]
  congr 1
  ring_nf

/-- The subgroup generated by two involutions `s, t` consists of the powers of `w = s t` and
their products with `s`. -/
private theorem closure_pair_subset_of_mul_self {G : Type*} [Group G] {s t : G} (hs : s * s = 1)
    (ht : t * t = 1) :
    ((Subgroup.closure {s, t} : Subgroup G) : Set G) ⊆
      Set.range (fun k : ℤ => (s * t) ^ k) ∪ Set.range (fun k : ℤ => (s * t) ^ k * s) := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set w := s * t
  have hconj : ∀ k : ℤ, s * w ^ k * s⁻¹ = w ^ (-k) := fun k => by
    rw [← conj_zpow, zpow_neg, ← inv_zpow]
    congr 1
    simp only [w, mul_inv_rev, hsinv, htinv, mul_assoc]
    rw [← mul_assoc s s, hs, one_mul]
  have hsw : ∀ k : ℤ, s * w ^ k = w ^ (-k) * s := fun k => by
    rw [← hconj k, hsinv, mul_assoc, hs, mul_one]
  let H : Subgroup G :=
    { carrier := Set.range (fun k : ℤ => w ^ k) ∪ Set.range (fun k : ℤ => w ^ k * s)
      mul_mem' := by
        rintro _ _ (⟨a, rfl⟩ | ⟨a, rfl⟩) (⟨b, rfl⟩ | ⟨b, rfl⟩)
        · exact Or.inl ⟨a + b, zpow_add _ _ _⟩
        · exact Or.inr ⟨a + b, by simp only; rw [zpow_add, mul_assoc]⟩
        · refine Or.inr ⟨a - b, ?_⟩
          simp only
          rw [mul_assoc, hsw, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
        · refine Or.inl ⟨a - b, ?_⟩
          simp only
          rw [mul_assoc, ← mul_assoc s, hsw, mul_assoc, hs, mul_one, ← zpow_add, sub_eq_add_neg]
      one_mem' := Or.inl ⟨0, zpow_zero _⟩
      inv_mem' := by
        rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
        · exact Or.inl ⟨-a, zpow_neg _ _⟩
        · refine Or.inr ⟨a, ?_⟩
          simp only
          rw [mul_inv_rev, hsinv, ← zpow_neg, hsw, neg_neg] }
  have hle : Subgroup.closure {s, t} ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Or.inr ⟨0, by simp⟩
    · refine Or.inr ⟨-1, ?_⟩
      simp only [w, zpow_neg_one, mul_inv_rev, htinv, hsinv, mul_assoc, hs, mul_one]
  exact hle

/-- For integers `b, c` with `bc > 3`, the `(0, 0)` entries of the powers of
`w = s₁ s₂` are strictly increasing, so the rank-two Weyl group is infinite. -/
private theorem not_finite_weylGroup {b c : ℤ} (hlt : 3 < b * c) :
    ¬((Subgroup.closure {weylS₁ b, weylS₂ c} : Subgroup (GL (Fin 2) ℤ)) :
      Set (GL (Fin 2) ℤ)).Finite := by
  intro hfin
  set w := weylS₁ b * weylS₂ c
  set M : Matrix (Fin 2) (Fin 2) ℤ := !![b * c - 1, -b; c, -1] with hM
  set a : ℕ → ℤ := fun k => (M ^ k) 0 0 with ha
  have hval : ∀ k : ℕ, ((w ^ k : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = M ^ k := fun k => by
    rw [Units.val_pow_eq_pow_val, val_weylS₁_mul_weylS₂ b c]
  have hsq : M * M = (b * c - 2) • M - 1 := by
    rw [hM, Matrix.mul_fin_two, Matrix.smul_of, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hrec : ∀ k, a (k + 2) = (b * c - 2) * a (k + 1) - a k := by
    intro k
    simp only [ha]
    rw [pow_add, pow_two, hsq, Matrix.mul_sub, Matrix.mul_smul, ← pow_succ, Matrix.mul_one]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have h0 : a 0 = 1 := by simp [ha]
  have h1 : a 1 = b * c - 1 := by simp [ha, hM]
  have hmono : ∀ k, 1 ≤ a k ∧ a k < a (k + 1) := by
    intro k
    induction k with
    | zero => rw [h0, zero_add, h1]; omega
    | succ k ih =>
      refine ⟨by omega, ?_⟩
      rw [hrec k]
      nlinarith
  have hinj : Function.Injective fun k : ℕ => w ^ k := by
    intro i j hij
    apply (strictMono_nat_of_lt_succ fun k => (hmono k).2).injective
    have := congrArg (fun g : GL (Fin 2) ℤ => (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0) hij
    simpa only [hval] using this
  have hwmem : w ∈ Subgroup.closure {weylS₁ b, weylS₂ c} :=
    mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  refine Set.infinite_range_of_injective hinj (hfin.subset ?_)
  rintro _ ⟨k, rfl⟩
  exact pow_mem hwmem k

/-- For integers `b, c`, both positive or both zero, with `bc ≤ 3`, `w = s₁ s₂` has order
dividing `12`, so the rank-two Weyl group is finite. -/
private theorem finite_weylGroup {b c : ℤ} (hbc : (0 < b ∧ 0 < c) ∨ (b = 0 ∧ c = 0))
    (hle : b * c ≤ 3) :
    ((Subgroup.closure {weylS₁ b, weylS₂ c} : Subgroup (GL (Fin 2) ℤ)) :
      Set (GL (Fin 2) ℤ)).Finite := by
  set w := weylS₁ b * weylS₂ c
  have hw12 : w ^ 12 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, val_weylS₁_mul_weylS₂ b c, Units.val_one]
    rcases hbc with ⟨hb, hc⟩ | ⟨rfl, rfl⟩
    · have hb3 : b ≤ 3 := by nlinarith
      have hc3 : c ≤ 3 := by nlinarith
      interval_cases b <;> interval_cases c <;> simp at hle ⊢ <;>
        simp [pow_succ, Matrix.one_fin_two]
    · simp [pow_succ, Matrix.one_fin_two]
  have hfo : IsOfFinOrder w := isOfFinOrder_iff_pow_eq_one.2 ⟨12, by norm_num, hw12⟩
  have hz : (Set.range fun k : ℤ => w ^ k).Finite := by
    simpa [Subgroup.coe_zpowers] using hfo.finite_zpowers
  refine (hz.union (hz.image (· * weylS₁ b))).subset ?_
  refine (closure_pair_subset_of_mul_self (weylS₁_mul_self b) (weylS₂_mul_self c)).trans ?_
  rintro _ (h | ⟨k, rfl⟩)
  · exact Or.inl h
  · exact Or.inr ⟨_, ⟨k, rfl⟩, rfl⟩

/-- **The rank-two Weyl group is finite exactly when `bc ≤ 3`.** For integers `b, c`, both
positive or both zero, the subgroup of `GL₂(ℤ)` generated by `s₁` and `s₂` is finite if and only
if `bc ≤ 3`. -/
@[cluster_algebras "prop_weyl_rank_two"]
theorem finite_weylGroup_iff {b c : ℤ} (hbc : (0 < b ∧ 0 < c) ∨ (b = 0 ∧ c = 0)) :
    ((Subgroup.closure {weylS₁ b, weylS₂ c} : Subgroup (GL (Fin 2) ℤ)) : Set (GL (Fin 2) ℤ)).Finite
      ↔ b * c ≤ 3 :=
  ⟨fun hfin => not_lt.1 fun hlt => not_finite_weylGroup hlt hfin, finite_weylGroup hbc⟩

/-! ### `2`-finite matrices -/

/-- A skew-symmetrizable `n × n` integer matrix `B` is **`2`-finite** when
`|b'ᵢⱼ b'ⱼᵢ| ≤ 3` for every matrix `B'` mutation equivalent to `B` and all `i, j`. -/
@[cluster_algebras "def_two_finite"]
def IsTwoFinite (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  SkewSymmetrizable B ∧ ∀ B' : Matrix (Fin n) (Fin n) ℤ, MutationEquiv B B' →
    ∀ i j, |B' i j * B' j i| ≤ 3

/-- Mutation along a sequence commutes with taking the principal part. -/
private theorem principalPart_matrixMutationList {R : Type*} [CommRing R] [LinearOrder R]
    (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (ks : List (Fin n)) :
    principalPart hmn (matrixMutationList hmn B ks) =
      matrixMutationList le_rfl (principalPart hmn B) ks := by
  induction ks generalizing B with
  | nil => rfl
  | cons k ks ih =>
    rw [matrixMutationList_cons, matrixMutationList_cons, ih, principalPart_matrixMutation]

/-- A permutation of `Fin m` taking the positions `0, 1` to two given distinct positions. -/
private theorem exists_perm_apply_castLE_eq (hm : 2 ≤ m) {a b : Fin m} (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin m), σ (Fin.castLE hm 0) = a ∧ σ (Fin.castLE hm 1) = b := by
  have h01 : (Fin.castLE hm 0 : Fin m) ≠ Fin.castLE hm 1 := by simp [Fin.ext_iff]
  set τ := Equiv.swap (Fin.castLE hm 0) a
  have hτ : τ (Fin.castLE hm 1) ≠ a := by
    intro h
    rw [← Equiv.swap_apply_left (Fin.castLE hm 0) a] at h
    exact h01 (τ.injective h).symm
  refine ⟨Equiv.swap (τ (Fin.castLE hm 1)) b * τ, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hτ.symm hab]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/-- The **cluster variables of a rank-two pattern through a reindexed seed** of `P` are cluster
variables of `P`, when the reindexing map is surjective. -/
theorem IsSeedPattern.patternClusterVariables_subset_of_reindex [CharZero K] (hmn : n ≤ m)
    (hm : 2 ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    {Q : RegularTree 2 → SeedData F m 2} (hQ : IsSeedPattern K hm Q) (u : RegularTree n)
    {r : ReindexingMap m 2 m n} (hr : Function.Surjective r)
    (hQu : Q .root = (P u).reindex hm r) :
    patternClusterVariables hm Q ⊆ patternClusterVariables hmn P := by
  rintro _ ⟨_, ⟨t', rfl⟩, p, rfl⟩
  obtain ⟨u', hu'⟩ := hP.seedMutationSeq_mem_range hmn u (t'.word.map (r.col hm))
  refine Set.mem_iUnion.2 ⟨u', r.col hm p, ?_⟩
  rw [hQ.apply_eq_seedMutationSeq_root hm t', hQu,
    seedMutationSeq_reindex hmn hm _ (ReindexingMap.isClosedFor_of_surjective hr hm _), ← hu']
  rfl

/-- A rank-two pattern through a labeled seed `S` with `|b₁₂ b₂₁| > 3` has infinitely many
cluster variables. -/
private theorem IsSeedPattern.infinite_of_three_lt_abs [CharZero K] (hm : 2 ≤ m)
    {Q : RegularTree 2 → SeedData F m 2} (hQ : IsSeedPattern K hm Q) {S : SeedData F m 2}
    (hS : IsLabeledSeed K hm S) (hQ0 : Q .root = S)
    (hlt : 3 < |principalPart hm S.extExchangeMatrix 0 1 *
      principalPart hm S.extExchangeMatrix 1 0|) :
    (patternClusterVariables hm Q).Infinite := by
  obtain ⟨ε, hε, b, c, hbc, h00, h11, h01, h10⟩ :=
    (show SkewSymmetrizable (principalPart hm S.extExchangeMatrix) from hS.2).exists_rankTwo_shape
  rw [h01, h10] at hlt
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hprod : ε * b * -(ε * c) = -(b * c) := by linear_combination (-(b * c)) * hε2
  rw [hprod, abs_neg] at hlt
  obtain ⟨hb, hc⟩ : 0 < b ∧ 0 < c := hbc.resolve_right (by rintro ⟨rfl, rfl⟩; simp at hlt)
  rw [abs_of_pos (mul_pos hb hc)] at hlt
  have hshape : principalPart hm (Q .root).extExchangeMatrix = ε • !![0, b; -c, 0] := by
    rw [hQ0]
    ext p q
    fin_cases p <;> fin_cases q <;> simp [h00, h11, h01, h10]
  exact (hQ.infinite_patternClusterVariables_of_rankTwo hm .root hε hb hc (by omega) hshape).1

/-- In a pattern of finite type, `|bᵢⱼ bⱼᵢ| ≤ 3` for the exchange matrix of every seed: otherwise
the rank-two pattern through the seed with the two positions `i, j` moved to the front would
have infinitely many cluster variables. -/
private theorem IsSeedPattern.abs_mul_le_three [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hfin : IsFiniteType P)
    (u : RegularTree n) (i j : Fin n) :
    |(P u).extExchangeMatrix (Fin.castLE hmn i) j * (P u).extExchangeMatrix (Fin.castLE hmn j) i|
      ≤ 3 := by
  by_contra hlt
  push Not at hlt
  have hij : i ≠ j := by
    rintro rfl
    rw [(hP.1 u).extExchangeMatrix_castLE_self hmn i, zero_mul, abs_zero] at hlt
    omega
  have hm : 2 ≤ m := (show 2 ≤ n by by_contra h; exact hij (Fin.ext (by omega))).trans hmn
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_apply_castLE_eq hm
    (a := Fin.castLE hmn i) (b := Fin.castLE hmn j) (fun h => hij (Fin.castLE_injective hmn h))
  have hσlt : ∀ p : Fin m, (p : ℕ) < 2 → (σ p : ℕ) < n := by
    intro p hp
    obtain rfl | rfl : p = Fin.castLE hm 0 ∨ p = Fin.castLE hm 1 := by
      simp only [Fin.ext_iff, Fin.val_castLE]
      omega
    · rw [hσ0]; simp
    · rw [hσ1]; simp
  set r : ReindexingMap m 2 m n := ⟨σ, σ.injective, hσlt⟩
  have hr0 : r.col hm 0 = i := Fin.ext (by simp [r, ReindexingMap.val_col, hσ0])
  have hr1 : r.col hm 1 = j := Fin.ext (by simp [r, ReindexingMap.val_col, hσ1])
  have hSd : IsLabeledSeed K hm ((P u).reindex hm r) := by
    refine ⟨⟨(hP.1 u).1.1.comp σ σ.injective, ?_⟩, (hP.1 u).2.matrixReindex hmn hm r⟩
    change IntermediateField.adjoin K (Set.range ((P u).extCluster ∘ σ)) = ⊤
    rw [σ.surjective.range_comp]
    exact (hP.1 u).1.2
  obtain ⟨Q, hQ, hQ0⟩ := exists_isSeedPattern (K := K) hm RegularTree.root hSd
  set Bu := (P u).extExchangeMatrix
  have e01 : principalPart hm ((P u).reindex hm r).extExchangeMatrix 0 1 =
      Bu (Fin.castLE hmn i) j := by
    change Bu (σ (Fin.castLE hm 0)) (r.col hm 1) = _
    rw [hσ0, hr1]
  have e10 : principalPart hm ((P u).reindex hm r).extExchangeMatrix 1 0 =
      Bu (Fin.castLE hmn j) i := by
    change Bu (σ (Fin.castLE hm 1)) (r.col hm 0) = _
    rw [hσ1, hr0]
  rw [← e01, ← e10] at hlt
  exact hQ.infinite_of_three_lt_abs hm hSd hQ0 hlt ((hfin.finite_iUnion_clusterVariables hmn).subset
    (hP.patternClusterVariables_subset_of_reindex hmn hm hQ u σ.surjective hQ0))

/-- For every vertex `t`, the exchange matrix of the seed at `t` of a seed pattern of finite type
is `2`-finite. -/
@[cluster_algebras "lem_finite_type_two_finite"]
theorem IsSeedPattern.isTwoFinite_of_isFiniteType [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hfin : IsFiniteType P)
    (t : RegularTree n) : IsTwoFinite (principalPart hmn (P t).extExchangeMatrix) := by
  refine ⟨(hP.1 t).2, fun B' hB' i j => ?_⟩
  obtain ⟨ks, π, rfl⟩ := hB'
  obtain ⟨u, hu⟩ := hP.seedMutationSeq_mem_range hmn t ks
  have hBu : principalPart hmn (P u).extExchangeMatrix =
      matrixMutationList le_rfl (principalPart hmn (P t).extExchangeMatrix) ks := by
    rw [hu, seedMutationSeq_extExchangeMatrix_eq_matrixMutationList,
      principalPart_matrixMutationList]
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply, ← hBu]
  exact hP.abs_mul_le_three hmn hfin u (π i) (π j)

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeBC.FoldingFinite
public import ClusterAlgebras.TypeD.Reduction
public import ClusterAlgebras.TypeA.Finite

/-!
# Seed patterns of type `B_n` are of finite type

Every seed pattern of type `B_n` is of finite type [FWZ, §5.5]. The proof folds `D_{n+1}` (or
`A_3` when `n = 2`) along the involution exchanging its two short legs: an action with a single
nontrivial orbit makes every admissible matrix globally foldable, which replaces the tagged
triangulations of a punctured polygon used in [FWZ].

## Main definitions

* `ClusterAlgebras.typeBUnfoldingMatrix n`: the `(n + 1) × (n + 1)` matrix `D^{(n)}`.
* `ClusterAlgebras.iotaB n`: the involution `ι_B` of `Fin (n + 1)` exchanging `n - 1` and `n`.
* `ClusterAlgebras.thetaB n hn`: the orbit labelling `θ_B` of the action of `ι_B`.

## Main results

* `ClusterAlgebras.cartanCounterpart_typeBUnfoldingMatrix`: `A(D^{(n)}) = C(D_{n+1})`, `n ≥ 3`.
* `ClusterAlgebras.isGloballyFoldable_typeBUnfoldingMatrix`: `D^{(n)}` is globally foldable.
* `ClusterAlgebras.foldedMatrix_thetaB_typeBUnfoldingMatrix`: `(D^{(n)})ᴳ = M(B_n)`.
* `ClusterAlgebras.IsSeedPattern.isFiniteType_of_isPatternOfType_B`: every seed pattern of type
  `B_n` is of finite type.

## Implementation notes

* Indices are `Fin (n + 1)`, so the index `i` of [FWZ] is `i - 1` here. In [FWZ], `D^{(n)}` has
  `d_{i,i+1} = 1`, `d_{i+1,i} = -1` for `i ∈ [1, n-1]` and `d_{n-1,n+1} = 1`, `d_{n+1,n-1} = -1`;
  here the entries `1` are at `(i, i + 1)` for `i + 1 < n` and at `(n - 2, n)`. The involution
  `ι_B` is `Equiv.swap (n - 1) n` on `Fin (n + 1)`. The labelling `θ_B` has `θ_B(0) = {n - 1, n}`
  and `θ_B(q) = {n - 1 - q}` for `q ∈ [1, n - 1]`.
* The action of `G = ℤ/2ℤ` by `ι` is modelled by the subgroup `Subgroup.zpowers ι` of
  `Equiv.Perm (Fin (n + 1))`, acting through its inclusion. For an involution `ι ≠ 1` this group
  is cyclic of order two, its nontrivial element acts by `ι`, and its orbits are the sets
  `{i, ι i}` (`TypeBC.mem_orbit_zpowers_iff`).
* `θ_B` is built from representatives (`TypeBC.orbitLabellingOfReps`), the least element
  `n - 1 - q` of each orbit; `thetaB_orbit_zero` and `thetaB_orbit_of_pos` describe its orbits.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 5][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix MulAction

/-! ### The unfolding -/

/-- The matrix **`D^{(n)}`** of the unfolding of type `B_n`: the `(n + 1) × (n + 1)` matrix with
`d_{i,i+1} = 1`, `d_{i+1,i} = -1` for `i ∈ [1, n-1]`, `d_{n-1,n+1} = 1`, `d_{n+1,n-1} = -1`, all
other entries `0`. With indices shifted down by one: `1` at `(i, i + 1)` for `i + 1 < n` and at
`(n - 2, n)`, and `-1` at the transposed positions. -/
@[cluster_algebras "def_type_B_unfolding"]
def typeBUnfoldingMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  of fun i j =>
    if (i : ℕ) + 1 = j ∧ (j : ℕ) < n then 1
    else if (j : ℕ) + 1 = i ∧ (i : ℕ) < n then -1
    else if (i : ℕ) + 2 = n ∧ (j : ℕ) = n then 1
    else if (j : ℕ) + 2 = n ∧ (i : ℕ) = n then -1
    else 0

/-- The involution **`ι_B`** of `Fin (n + 1)`, exchanging `n - 1` and `n` and fixing every other
index. -/
@[cluster_algebras "def_type_B_unfolding"]
def iotaB (n : ℕ) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap ⟨n - 1, by omega⟩ (Fin.last n)

/-- `ι_B` is an involution. -/
theorem iotaB_mul_self (n : ℕ) : iotaB n * iotaB n = 1 :=
  Equiv.swap_mul_self _ _

/-- The values of `ι_B`: it exchanges `n - 1` and `n` and fixes every other index. -/
theorem iotaB_val (n : ℕ) (x : Fin (n + 1)) :
    (iotaB n x : ℕ) = if (x : ℕ) = n - 1 then n else if (x : ℕ) = n then n - 1 else x := by
  by_cases h₁ : (x : ℕ) = n - 1
  · rw [if_pos h₁, show x = ⟨n - 1, by omega⟩ from Fin.ext h₁, iotaB, Equiv.swap_apply_left,
      Fin.val_last]
  · by_cases h₂ : (x : ℕ) = n
    · rw [if_neg h₁, if_pos h₂, show x = Fin.last n from Fin.ext h₂, iotaB,
        Equiv.swap_apply_right]
    · rw [if_neg h₁, if_neg h₂, iotaB, Equiv.swap_apply_of_ne_of_ne
        (fun h => h₁ (by rw [h])) (fun h => h₂ (by rw [h, Fin.val_last]))]

/-- The representative `n - 1 - q` of the orbit labelled `q` by `θ_B`. -/
def thetaBRep (n : ℕ) (q : Fin n) : Fin (n + 1) :=
  ⟨n - 1 - q, by omega⟩

/-- Distinct labels of `θ_B` have representatives in distinct orbits of `ι_B`. -/
theorem thetaBRep_inj (n : ℕ) (p q : Fin n)
    (h : thetaBRep n q ∈ orbit (Subgroup.zpowers (iotaB n)) (thetaBRep n p)) : p = q := by
  rw [TypeBC.mem_orbit_zpowers_iff (iotaB_mul_self n)] at h
  rcases h with h | h
  · simp only [thetaBRep, Fin.ext_iff] at h
    ext; omega
  · have h' := congrArg Fin.val h
    rw [iotaB_val] at h'
    simp only [thetaBRep, Fin.val_mk] at h'
    have := p.isLt
    have := q.isLt
    ext
    split_ifs at h' <;> omega

/-- Every index lies in the `ι_B`-orbit of a representative of `θ_B`. -/
theorem thetaBRep_surj {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) :
    ∃ p, i ∈ orbit (Subgroup.zpowers (iotaB n)) (thetaBRep n p) := by
  simp only [TypeBC.mem_orbit_zpowers_iff (iotaB_mul_self n)]
  by_cases hi : (i : ℕ) + 1 < n
  · exact ⟨⟨n - 1 - i, by omega⟩, Or.inl (by ext; simp [thetaBRep]; omega)⟩
  · refine ⟨⟨0, by omega⟩, ?_⟩
    by_cases hi' : (i : ℕ) = n - 1
    · exact Or.inl (by ext; simp [thetaBRep]; omega)
    · right
      have h0 : thetaBRep n ⟨0, by omega⟩ = ⟨n - 1, by omega⟩ := by ext; simp [thetaBRep]
      rw [h0, iotaB, Equiv.swap_apply_left]
      ext; simp only [Fin.val_last]; omega

/-- The orbit labelling **`θ_B`** of the action of `ι_B` on `Fin (n + 1)` (all indices mutable):
`θ_B(0) = {n - 1, n}` and `θ_B(q) = {n - 1 - q}` for `q ∈ [1, n - 1]`. -/
@[cluster_algebras "def_type_B_unfolding"]
noncomputable def thetaB (n : ℕ) (hn : 2 ≤ n) :
    OrbitLabelling (Subgroup.zpowers (iotaB n)) (n + 1) (n + 1) n n :=
  TypeBC.orbitLabellingOfReps (thetaBRep n) (thetaBRep_inj n) (thetaBRep_surj (by omega))

/-- The orbit `θ_B(0)` is `{n - 1, n}`. -/
@[cluster_algebras "def_type_B_unfolding"]
theorem thetaB_orbit_zero (n : ℕ) (hn : 2 ≤ n) :
    (thetaB n hn).orbit ⟨0, by omega⟩ = {⟨n - 1, by omega⟩, Fin.last n} := by
  ext i
  rw [thetaB, TypeBC.mem_orbit_orbitLabellingOfReps,
    TypeBC.mem_orbit_zpowers_iff (iotaB_mul_self n),
    Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff, Fin.ext_iff, Fin.ext_iff,
    iotaB_val]
  simp only [thetaBRep, Fin.val_last]
  split_ifs <;> omega

/-- For `q ≥ 1`, the orbit `θ_B(q)` is the singleton `{n - 1 - q}`. -/
@[cluster_algebras "def_type_B_unfolding"]
theorem thetaB_orbit_of_pos (n : ℕ) (hn : 2 ≤ n) (q : Fin n) (hq : 1 ≤ (q : ℕ)) :
    (thetaB n hn).orbit q = {⟨n - 1 - q, by omega⟩} := by
  ext i
  rw [thetaB, TypeBC.mem_orbit_orbitLabellingOfReps,
    TypeBC.mem_orbit_zpowers_iff (iotaB_mul_self n),
    Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff, Fin.ext_iff, iotaB_val]
  have := q.isLt
  simp only [thetaBRep]
  split_ifs <;> omega

/-- The least element of the orbit `θ_B(p)` is `n - 1 - p`. -/
theorem thetaB_rep_val (n : ℕ) (hn : 2 ≤ n) (p : Fin n) :
    ((thetaB n hn).rep p : ℕ) = n - 1 - p := by
  have hmem := (thetaB n hn).rep_mem p
  rcases Nat.eq_zero_or_pos (p : ℕ) with h0 | hp
  · rw [show p = ⟨0, by omega⟩ from Fin.ext h0] at hmem ⊢
    have hle := (thetaB n hn).rep_le (p := ⟨0, by omega⟩) (i := ⟨n - 1, by omega⟩)
      (by rw [thetaB_orbit_zero]; simp)
    rw [thetaB_orbit_zero, Finset.mem_insert, Finset.mem_singleton] at hmem
    rw [Fin.le_iff_val_le_val] at hle
    rcases hmem with h | h
    · rw [h]
      rfl
    · rw [h, Fin.val_last] at hle
      dsimp only at hle
      omega
  · rw [thetaB_orbit_of_pos n hn p hp, Finset.mem_singleton] at hmem
    rw [hmem]

/-! ### The unfolding is globally foldable -/

/-- **`D^{(n)}` is skew-symmetric.** -/
@[cluster_algebras "lem_type_B_unfolding"]
theorem typeBUnfoldingMatrix_apply_eq_neg (n : ℕ) (i j : Fin (n + 1)) :
    typeBUnfoldingMatrix n i j = -typeBUnfoldingMatrix n j i := by
  simp only [typeBUnfoldingMatrix, of_apply]
  split_ifs <;> omega

/-- **The Cartan counterpart of `D^{(n)}` is `C(D_{n+1})`** for `n ≥ 3`. -/
@[cluster_algebras "lem_type_B_unfolding"]
theorem cartanCounterpart_typeBUnfoldingMatrix {n : ℕ} (_hn : 3 ≤ n) :
    cartanCounterpart (typeBUnfoldingMatrix n) = cartanD (n + 1) := by
  ext i j
  simp only [cartanCounterpart, cartanD, cartanOfGraph, dynkinTreeD, typeBUnfoldingMatrix, of_apply,
    SimpleGraph.fromRel_adj, dynkinTreeDRel, Fin.ext_iff]
  split_ifs <;> simp_all
  omega

/-- **For `n = 2`, the Cartan counterpart of `D^{(2)}` has the same type as `C(A_3)`**: `D^{(2)}`
is the matrix of the quiver `2 ← 1 → 3`. -/
@[cluster_algebras "lem_type_B_unfolding"]
theorem sameCartanType_cartanA_three_typeBUnfoldingMatrix_two :
    SameCartanType (cartanA 3) (cartanCounterpart (typeBUnfoldingMatrix 2)) := by
  refine ⟨Equiv.swap 0 1, ?_⟩
  decide

/-- Every element of the group generated by `ι_B` acts as `1` or as `ι_B`. -/
theorem coe_zpowers_iotaB_eq (n : ℕ) (g : Subgroup.zpowers (iotaB n)) :
    (g : Equiv.Perm (Fin (n + 1))) = 1 ∨ (g : Equiv.Perm (Fin (n + 1))) = iotaB n := by
  obtain ⟨g, hg⟩ := g
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have h2 : iotaB n ^ (2 : ℤ) = 1 := by rw [zpow_two, iotaB_mul_self]
  rcases Int.even_or_odd' k with ⟨r, rfl | rfl⟩
  · left
    change iotaB n ^ (2 * r) = 1
    rw [_root_.zpow_mul, h2, _root_.one_zpow]
  · right
    change iotaB n ^ (2 * r + 1) = iotaB n
    rw [_root_.zpow_add_one, _root_.zpow_mul, h2, _root_.one_zpow, one_mul]

/-- `ι_B` preserves the entries of `D^{(n)}`: `d_{ι(i) ι(j)} = d_{ij}`. -/
theorem typeBUnfoldingMatrix_iotaB (n : ℕ) (i j : Fin (n + 1)) :
    typeBUnfoldingMatrix n (iotaB n i) (iotaB n j) = typeBUnfoldingMatrix n i j := by
  have := i.isLt
  have := j.isLt
  simp only [typeBUnfoldingMatrix, of_apply, iotaB_val]
  split_ifs <;> omega

/-- `d_{i, ι(i)} = 0`. -/
theorem typeBUnfoldingMatrix_apply_iotaB_self (n : ℕ) (i : Fin (n + 1)) :
    typeBUnfoldingMatrix n i (iotaB n i) = 0 := by
  have := i.isLt
  simp only [typeBUnfoldingMatrix, of_apply, iotaB_val]
  split_ifs <;> omega

/-- `d_{ij} d_{ι(i) j} ≥ 0`. -/
theorem typeBUnfoldingMatrix_mul_iotaB_nonneg (n : ℕ) (i j : Fin (n + 1)) :
    0 ≤ typeBUnfoldingMatrix n i j * typeBUnfoldingMatrix n (iotaB n i) j := by
  have := i.isLt
  have := j.isLt
  simp only [typeBUnfoldingMatrix, of_apply, iotaB_val]
  split_ifs <;> omega

/-- **`D^{(n)}` is admissible** for the action of `ι_B`, all indices being mutable. -/
@[cluster_algebras "lem_type_B_unfolding"]
theorem isGroupAdmissible_typeBUnfoldingMatrix {n : ℕ} (_hn : 2 ≤ n) :
    IsGroupAdmissible (Subgroup.zpowers (iotaB n)) le_rfl (typeBUnfoldingMatrix n) := by
  refine ⟨fun g i j j' hj => ?_, fun i i' hi => ?_, fun i i' hi j => ?_⟩
  · change j' = g • j at hj
    subst hj
    rcases coe_zpowers_iotaB_eq n g with h | h <;>
      simp only [Subgroup.smul_def, Equiv.Perm.smul_def, h, Equiv.Perm.one_apply,
        typeBUnfoldingMatrix_iotaB]
  · change i' ∈ orbit _ i at hi
    change typeBUnfoldingMatrix n i i' = 0
    rcases (TypeBC.mem_orbit_zpowers_iff (iotaB_mul_self n)).1 hi with rfl | rfl
    · have := typeBUnfoldingMatrix_apply_eq_neg n i' i'
      omega
    · exact typeBUnfoldingMatrix_apply_iotaB_self n i
  · rcases (TypeBC.mem_orbit_zpowers_iff (iotaB_mul_self n)).1 hi with rfl | rfl
    · exact mul_self_nonneg _
    · exact typeBUnfoldingMatrix_mul_iotaB_nonneg n i j

/-- **`D^{(n)}` is globally foldable** for the action of `ι_B` and every orbit labelling. -/
@[cluster_algebras "lem_type_B_unfolding"]
theorem isGloballyFoldable_typeBUnfoldingMatrix {n : ℕ} (hn : 2 ≤ n) {mG nG : ℕ}
    (θ : OrbitLabelling (Subgroup.zpowers (iotaB n)) (n + 1) (n + 1) mG nG) :
    IsGloballyFoldable θ le_rfl (typeBUnfoldingMatrix n) := by
  refine TypeBC.isGloballyFoldable_of_isSinglePairAction θ le_rfl (a := ⟨n - 1, by omega⟩)
    (b := Fin.last n) ⟨fun h => by simp [Fin.ext_iff] at h; omega, fun i i' => ?_⟩
    (isGroupAdmissible_typeBUnfoldingMatrix hn) (typeBUnfoldingMatrix_apply_eq_neg n)
  rw [TypeBC.mem_orbit_zpowers_iff (iotaB_mul_self n)]
  have := i.isLt
  have := i'.isLt
  simp only [Fin.ext_iff, iotaB_val, Fin.val_castLE, Fin.val_last]
  split_ifs <;> omega

/-- **The folding of `D^{(n)}` is `M(B_n)`**: `(D^{(n)})ᴳ = M(B_n)` for the orbit labelling
`θ_B`. -/
@[cluster_algebras "lem_type_B_unfolding"]
theorem foldedMatrix_thetaB_typeBUnfoldingMatrix {n : ℕ} (hn : 2 ≤ n) :
    foldedMatrix (thetaB n hn) (typeBUnfoldingMatrix n) = typeBMatrix n := by
  ext p q
  have hc : ((thetaB n hn).colRep q : ℕ) = n - 1 - q := thetaB_rep_val n hn _
  have := q.isLt
  rw [foldedMatrix_apply]
  rcases Nat.eq_zero_or_pos (p : ℕ) with h0 | hp
  · rw [show p = ⟨0, by omega⟩ from Fin.ext h0, thetaB_orbit_zero,
      Finset.sum_pair (by simp [Fin.ext_iff]; omega)]
    simp only [typeBUnfoldingMatrix, typeBMatrix, of_apply, Fin.val_last, hc, true_and, and_true]
    split_ifs <;> first | contradiction | omega
  · rw [thetaB_orbit_of_pos n hn p hp, Finset.sum_singleton]
    have := p.isLt
    simp only [typeBUnfoldingMatrix, typeBMatrix, of_apply, hc]
    split_ifs <;> omega

/-! ### Finite type -/

/-- The Cartan matrix of a one-symbol list is the Cartan matrix of the symbol. -/
theorem DynkinSymbol.typeB_listCartan_singleton (X : DynkinSymbol) (h : listRank [X] = X.rank)
    (a b : Fin (listRank [X])) :
    listCartan [X] a b = X.cartan (Fin.cast h a) (Fin.cast h b) := by
  have key : ∀ c : Fin (listRank [X]), finSumFinEquiv.symm c = Sum.inl (Fin.cast h c) := by
    intro c
    rw [Equiv.symm_apply_eq]
    ext
    rfl
  simp only [listCartan, reindex_apply, submatrix_apply, key, fromBlocks_apply₁₁]

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- For `n ≥ 2`, every seed pattern of type `B_n` is of finite type. -/
@[cluster_algebras "thm_type_B_finite"]
theorem IsSeedPattern.isFiniteType_of_isPatternOfType_B [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hn : 2 ≤ n)
    (hX : IsPatternOfType hmn P [DynkinSymbol.B n hn]) : IsFiniteType P := by
  obtain ⟨t, σ, hσ⟩ := hX
  refine TypeBC.isFiniteType_of_sameCartanType_foldedMatrix
    ⟨_, isSkewSymmetrizingVector_typeBMatrix n⟩
    (isFiniteTree_coxeterGraph_cartanCounterpart_typeBMatrix (by omega)) (thetaB n hn)
    (typeBUnfoldingMatrix_apply_eq_neg n) (isGloballyFoldable_typeBUnfoldingMatrix hn _)
    (foldedMatrix_thetaB_typeBUnfoldingMatrix hn) ?_ hmn hP (t := t) ?_
  · rintro F' _ _ m' hm' P' hP' ⟨t', ht'⟩
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · obtain ⟨π, hπ⟩ := sameCartanType_cartanA_three_typeBUnfoldingMatrix_two
      have hr : DynkinSymbol.listRank [DynkinSymbol.A 3 (by norm_num)] = 3 := rfl
      refine hP'.isFiniteType_of_typeA (by norm_num) hm'
        ⟨t', π.trans (finCongr hr.symm), fun i j => ?_⟩
      rw [DynkinSymbol.typeB_listCartan_singleton _ hr, ht', hπ]
      simp [DynkinSymbol.cartan]
      rfl
    · have hr : DynkinSymbol.listRank [DynkinSymbol.D (n + 1) (by omega)] = n + 1 := rfl
      refine hP'.isFiniteType_of_isPatternOfType_D (by omega) hm'
        ⟨t', finCongr hr.symm, fun i j => ?_⟩
      rw [DynkinSymbol.typeB_listCartan_singleton _ hr, ht',
        cartanCounterpart_typeBUnfoldingMatrix h3]
      simp [DynkinSymbol.cartan]
      rfl
  · have hr : DynkinSymbol.listRank [DynkinSymbol.B n hn] = n := rfl
    refine ⟨(σ.trans (finCongr hr)).symm, fun i j => ?_⟩
    rw [hσ, DynkinSymbol.typeB_listCartan_singleton _ hr, cartanCounterpart_typeBMatrix]
    simp [DynkinSymbol.cartan]
    rfl

end ClusterAlgebras

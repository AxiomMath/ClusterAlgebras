/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeBC.Symmetric
public import ClusterAlgebras.TypeBC.FoldingFinite
public import ClusterAlgebras.TypeA.Finite

/-!
# Seed patterns of type `C_n` are of finite type, and types `B_n`, `C_n` are different

Every seed pattern of type `C_n` is of finite type [FWZ, §5.5]. The proof folds `A_{2n-1}` along
the involution `ι_C`, with global foldability proved through centrally symmetric triangulations of
the `(2n + 2)`-gon. Moreover, no seed pattern is of both types `B_n` and `C_n`.

## Main definitions

* `ClusterAlgebras.typeCUnfoldingMatrix n`: the `(2n - 1) × (2n - 1)` matrix `U^{(n)}`.
* `ClusterAlgebras.thetaC n hn`: the orbit labelling `θ_C` of the action of `ι_C`.
* `ClusterAlgebras.typeCInitialTriangulation n`, `ClusterAlgebras.typeCInitialLabelling n`:
  the centrally symmetric triangulation `T₀` and its labelling `λ₀`.

## Main results

* `ClusterAlgebras.triangulationMatrix_typeCInitial`: `B(T₀, λ₀) = U^{(n)}`.
* `ClusterAlgebras.isGloballyFoldable_typeCUnfoldingMatrix`: `U^{(n)}` is globally foldable.
* `ClusterAlgebras.foldedMatrix_thetaC_typeCUnfoldingMatrix`: `(U^{(n)})ᴳ = M(C_n)`.
* `ClusterAlgebras.IsSeedPattern.isFiniteType_of_isPatternOfType_C`: every seed pattern of type
  `C_n` is of finite type.
* `ClusterAlgebras.IsSeedPattern.not_isPatternOfType_B_and_C`: no seed pattern is of both types
  `B_n` and `C_n`.

## Implementation notes

* Labels are shifted down by one. In [FWZ], `U^{(n)}` has `u_{p,p+1} = 1`, `u_{p+1,p} = -1` for
  `p ∈ [1, n-1]` and `u_{p,p-1} = 1`, `u_{p-1,p} = -1` for `p ∈ [n+1, 2n-1]`; here the entries `1`
  are at `(p, p + 1)` for `p + 1 ≤ n - 1` and at `(p, p - 1)` for `p ≥ n`: every arrow points
  towards the middle label `n - 1`. The labelling `θ_C` has `θ_C(q) = {n - 1 - q, n - 1 + q}` (in
  [FWZ], `θ_C(1) = {n}` and `θ_C(q) = {n + 1 - q, n - 1 + q}`).
* Polygon vertices are elements of `ZMod (2n + 2)`, written through natural number casts; the
  representatives `[1, 2n + 2]` of [FWZ] are these casts (the representative `2n + 2` is `0`).
  `T₀ = {{i, n+2} : i ∈ [1, n]} ∪ {{1, j} : j ∈ [n+3, 2n+1]}`. The labelling `λ₀` sends the label
  `p ≥ n - 1` (the label `n + r` of [FWZ], `r = p - n + 1`) to `{p - n + 2, n + 2}` and the label
  `p < n - 1` (the label `n - r` of [FWZ], `r = n - 1 - p`) to `{1, 2n + 1 - p}`.
* `θ_C` is built from the representatives `n - 1 - q` (`TypeBC.orbitLabellingOfReps`), and the
  action of `ℤ/2ℤ` by `ι_C` is that of `Subgroup.zpowers (TypeBC.iotaC n)`.
* The proof of finiteness uses the finiteness of seed patterns of type `A_{2n-1}`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 5][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix MulAction

/-! ### The unfolding -/

/-- The matrix **`U^{(n)}`** of the unfolding of type `C_n`, the matrix of the quiver
`n' → ⋯ → 2' → 1 ← 2 ← ⋯ ← n` with its vertices numbered along the path: the
`(2n - 1) × (2n - 1)` matrix with `u_{p,p+1} = 1`, `u_{p+1,p} = -1` for `p ∈ [1, n-1]` and
`u_{p,p-1} = 1`, `u_{p-1,p} = -1` for `p ∈ [n+1, 2n-1]`. With indices shifted down by one: `1`
at `(p, p + 1)` for `p + 1 ≤ n - 1` and at `(p, p - 1)` for `p ≥ n`, `-1` at the transposed
positions. -/
@[cluster_algebras "def_type_C_unfolding"]
def typeCUnfoldingMatrix (n : ℕ) : Matrix (Fin (2 * n - 1)) (Fin (2 * n - 1)) ℤ :=
  of fun p q =>
    if (p : ℕ) + 1 = q ∧ (q : ℕ) + 1 ≤ n then 1
    else if (q : ℕ) + 1 = p ∧ (p : ℕ) + 1 ≤ n then -1
    else if (q : ℕ) + 1 = p ∧ n ≤ (p : ℕ) then 1
    else if (p : ℕ) + 1 = q ∧ n ≤ (q : ℕ) then -1
    else 0

/-- The representative `n - 1 - q` of the orbit labelled `q` by `θ_C`. -/
def thetaCRep (n : ℕ) (q : Fin n) : Fin (2 * n - 1) :=
  ⟨n - 1 - q, by omega⟩

/-- Distinct labels of `θ_C` have representatives in distinct orbits of `ι_C`. -/
theorem thetaCRep_inj (n : ℕ) (p q : Fin n)
    (h : thetaCRep n q ∈ orbit (Subgroup.zpowers (TypeBC.iotaC n)) (thetaCRep n p)) :
    p = q := by
  rw [TypeBC.mem_orbit_zpowers_iff (TypeBC.iotaC_mul_self n)] at h
  have hp := p.isLt
  have hq := q.isLt
  rcases h with h | h <;>
    simp only [thetaCRep, Fin.ext_iff, TypeBC.iotaC_val] at h <;>
    exact Fin.ext (by omega)

/-- Every label lies in the `ι_C`-orbit of a representative of `θ_C`. -/
theorem thetaCRep_surj {n : ℕ} (hn : 1 ≤ n) (i : Fin (2 * n - 1)) :
    ∃ p, i ∈ orbit (Subgroup.zpowers (TypeBC.iotaC n)) (thetaCRep n p) := by
  simp only [TypeBC.mem_orbit_zpowers_iff (TypeBC.iotaC_mul_self n)]
  have hi := i.isLt
  by_cases h : (i : ℕ) + 1 ≤ n
  · exact ⟨⟨n - 1 - i, by omega⟩, Or.inl (Fin.ext (by simp only [thetaCRep, Fin.val_mk]; omega))⟩
  · refine ⟨⟨i + 1 - n, by omega⟩, Or.inr ?_⟩
    ext
    rw [TypeBC.iotaC_val]
    simp only [thetaCRep, Fin.val_mk]
    omega

/-- The orbit labelling **`θ_C`** of the action of `ι_C` on `Fin (2n - 1)` (all indices
mutable): `θ_C(q) = {n - 1 - q, n - 1 + q}`, so `θ_C(0) = {n - 1}`. -/
@[cluster_algebras "def_type_C_unfolding"]
noncomputable def thetaC (n : ℕ) (hn : 2 ≤ n) :
    OrbitLabelling (Subgroup.zpowers (TypeBC.iotaC n)) (2 * n - 1) (2 * n - 1) n n :=
  TypeBC.orbitLabellingOfReps (thetaCRep n) (thetaCRep_inj n) (thetaCRep_surj (by omega))

/-- **The orbits `θ_C(q)`** are `{n - 1 - q, n - 1 + q}`. -/
@[cluster_algebras "def_type_C_unfolding"]
theorem thetaC_orbit (n : ℕ) (hn : 2 ≤ n) (q : Fin n) :
    (thetaC n hn).orbit q = {⟨n - 1 - q, by omega⟩, ⟨n - 1 + q, by omega⟩} := by
  ext i
  rw [thetaC, TypeBC.mem_orbit_orbitLabellingOfReps,
    TypeBC.mem_orbit_zpowers_iff (TypeBC.iotaC_mul_self n), Finset.mem_insert,
    Finset.mem_singleton]
  have := q.isLt
  simp only [Fin.ext_iff, TypeBC.iotaC_val, thetaCRep]
  omega

/-- The least element of the orbit `θ_C(q)` is `n - 1 - q`. -/
theorem thetaC_rep_val (n : ℕ) (hn : 2 ≤ n) (q : Fin n) :
    ((thetaC n hn).rep q : ℕ) = n - 1 - q := by
  have hmem := (thetaC n hn).rep_mem q
  have hle := (thetaC n hn).rep_le (p := q) (i := ⟨n - 1 - q, by omega⟩)
    (by rw [thetaC_orbit]; simp)
  rw [thetaC_orbit, Finset.mem_insert, Finset.mem_singleton] at hmem
  rw [Fin.le_iff_val_le_val] at hle
  rcases hmem with h | h
  · rw [h]
  · rw [h] at hle ⊢
    dsimp only at hle ⊢
    omega

/-- The **centrally symmetric triangulation `T₀`** of the `(2n + 2)`-gon:
`{{i, n+2} : i ∈ [1, n]} ∪ {{1, j} : j ∈ [n+3, 2n+1]}`. -/
@[cluster_algebras "def_type_C_unfolding"]
def typeCInitialTriangulation (n : ℕ) : Finset (Sym2 (ZMod (2 * n + 2))) :=
  (Finset.Icc 1 n).image (fun i : ℕ => s((i : ZMod (2 * n + 2)), ((n + 2 : ℕ) : ZMod (2 * n + 2))))
    ∪ (Finset.Icc (n + 3) (2 * n + 1)).image
      (fun j : ℕ => s((1 : ZMod (2 * n + 2)), (j : ZMod (2 * n + 2))))

/-- The **labelling `λ₀`** of `T₀`: the label `p ≥ n - 1` goes to `{p - n + 2, n + 2}` and the
label `p < n - 1` to `{1, 2n + 1 - p}`. -/
@[cluster_algebras "def_type_C_unfolding"]
def typeCInitialLabelling (n : ℕ) (p : Fin (2 * n - 1)) : Sym2 (ZMod (2 * n + 2)) :=
  if n - 1 ≤ (p : ℕ) then
    s(((p + 2 - n : ℕ) : ZMod (2 * n + 2)), ((n + 2 : ℕ) : ZMod (2 * n + 2)))
  else s((1 : ZMod (2 * n + 2)), ((2 * n + 1 - p : ℕ) : ZMod (2 * n + 2)))

/-! ### The initial triangulation: computations on representatives

Every vertex of the `(2n + 2)`-gon is the cast of its representative `val < 2n + 2`; the
statements below translate betweenness, crossing, sides, membership in `T₀` and equality of
segments into linear arithmetic on representatives, which `omega` then decides. -/

section Initial

variable {n : ℕ}

private theorem typeC_cast_ne {a b : ℕ} (ha : a < 2 * n + 2) (hb : b < 2 * n + 2) (h : a ≠ b) :
    (a : ZMod (2 * n + 2)) ≠ b :=
  fun h' => h ((TypeA.natCast_inj_of_lt ha hb).1 h')

private theorem typeC_cast_eq_of {a b : ℕ}
    (h : a = b ∨ a = b + (2 * n + 2) ∨ b = a + (2 * n + 2)) :
    (a : ZMod (2 * n + 2)) = b := by
  rcases h with rfl | rfl | rfl
  · rfl
  all_goals rw [Nat.cast_add, ZMod.natCast_self, add_zero]

private theorem typeC_sym2_eq_of {a b c d : ℕ}
    (h : ((a = c ∨ a = c + (2 * n + 2) ∨ c = a + (2 * n + 2)) ∧
        (b = d ∨ b = d + (2 * n + 2) ∨ d = b + (2 * n + 2))) ∨
      ((a = d ∨ a = d + (2 * n + 2) ∨ d = a + (2 * n + 2)) ∧
        (b = c ∨ b = c + (2 * n + 2) ∨ c = b + (2 * n + 2)))) :
    s((a : ZMod (2 * n + 2)), (b : ZMod (2 * n + 2))) =
      s((c : ZMod (2 * n + 2)), (d : ZMod (2 * n + 2))) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [typeC_cast_eq_of h1, typeC_cast_eq_of h2]
  · rw [typeC_cast_eq_of h1, typeC_cast_eq_of h2, Sym2.eq_swap]

private theorem typeC_cross_iff {a b c d : ℕ} (ha : a < 2 * n + 2) (hb : b < 2 * n + 2)
    (hc : c < 2 * n + 2) (hd : d < 2 * n + 2) :
    Cross s((a : ZMod (2 * n + 2)), (b : ZMod (2 * n + 2)))
        s((c : ZMod (2 * n + 2)), (d : ZMod (2 * n + 2))) ↔
      ((((a < c ∧ c < b) ∨ (c < b ∧ b < a) ∨ (b < a ∧ a < c)) ∧
        ((b < d ∧ d < a) ∨ (d < a ∧ a < b) ∨ (a < b ∧ b < d))) ∨
       (((a < d ∧ d < b) ∨ (d < b ∧ b < a) ∨ (b < a ∧ a < d)) ∧
        ((b < c ∧ c < a) ∨ (c < a ∧ a < b) ∨ (a < b ∧ b < c)))) := by
  rw [TypeA.cross_mk_iff, TypeA.sbtw_natCast_iff ha hc hb, TypeA.sbtw_natCast_iff hb hd ha,
    TypeA.sbtw_natCast_iff ha hd hb, TypeA.sbtw_natCast_iff hb hc ha]

private theorem typeC_cast_eq_succ_iff {a b : ℕ} (ha : a < 2 * n + 2) (hb : b < 2 * n + 2) :
    (b : ZMod (2 * n + 2)) = a + 1 ↔ b = a + 1 ∨ (a + 1 = 2 * n + 2 ∧ b = 0) := by
  rw [← Nat.cast_add_one]
  by_cases h : a + 1 < 2 * n + 2
  · rw [TypeA.natCast_inj_of_lt hb h]
    omega
  · have h' : a + 1 = 2 * n + 2 := by omega
    rw [h', ZMod.natCast_self, ← Nat.cast_zero (R := ZMod (2 * n + 2)),
      TypeA.natCast_inj_of_lt hb (by omega)]
    omega

private theorem typeC_isSide_iff {a b : ℕ} (ha : a < 2 * n + 2) (hb : b < 2 * n + 2) :
    IsSide s((a : ZMod (2 * n + 2)), (b : ZMod (2 * n + 2))) ↔
      b = a + 1 ∨ a = b + 1 ∨ (a + 1 = 2 * n + 2 ∧ b = 0) ∨ (b + 1 = 2 * n + 2 ∧ a = 0) := by
  rw [TypeA.isSide_mk_iff, typeC_cast_eq_succ_iff ha hb, typeC_cast_eq_succ_iff hb ha]
  omega

/-- Membership in `T₀`, read on the representatives. -/
private theorem typeC_mem_iff (hn : 2 ≤ n) {a b : ℕ} (ha : a < 2 * n + 2) (hb : b < 2 * n + 2) :
    s((a : ZMod (2 * n + 2)), (b : ZMod (2 * n + 2))) ∈ typeCInitialTriangulation n ↔
      (1 ≤ a ∧ a ≤ n ∧ b = n + 2) ∨ (1 ≤ b ∧ b ≤ n ∧ a = n + 2) ∨
        (a = 1 ∧ n + 3 ≤ b ∧ b ≤ 2 * n + 1) ∨ (b = 1 ∧ n + 3 ≤ a ∧ a ≤ 2 * n + 1) := by
  simp only [typeCInitialTriangulation, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
  rw [← Nat.cast_one (R := ZMod (2 * n + 2))]
  constructor
  · rintro (⟨i, ⟨hi1, hi2⟩, he⟩ | ⟨j, ⟨hj1, hj2⟩, he⟩) <;>
      rw [TypeA.sym2_natCast_eq_iff (by omega) (by omega) ha hb] at he <;> omega
  · rintro (⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩)
    · exact Or.inl ⟨a, ⟨h1, h2⟩, rfl⟩
    · exact Or.inl ⟨b, ⟨h1, h2⟩, Sym2.eq_swap⟩
    · exact Or.inr ⟨b, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr ⟨a, ⟨h1, h2⟩, Sym2.eq_swap⟩

/-- Segments of `T₀`, read on the representatives. -/
private theorem typeC_mem_segments_iff (hn : 2 ≤ n) {a b : ℕ} (ha : a < 2 * n + 2)
    (hb : b < 2 * n + 2) :
    s((a : ZMod (2 * n + 2)), (b : ZMod (2 * n + 2))) ∈ segments (typeCInitialTriangulation n) ↔
      ((1 ≤ a ∧ a ≤ n ∧ b = n + 2) ∨ (1 ≤ b ∧ b ≤ n ∧ a = n + 2) ∨
        (a = 1 ∧ n + 3 ≤ b ∧ b ≤ 2 * n + 1) ∨ (b = 1 ∧ n + 3 ≤ a ∧ a ≤ 2 * n + 1)) ∨
      (b = a + 1 ∨ a = b + 1 ∨ (a + 1 = 2 * n + 2 ∧ b = 0) ∨ (b + 1 = 2 * n + 2 ∧ a = 0)) := by
  rw [mem_segments, typeC_mem_iff hn ha hb, typeC_isSide_iff ha hb]

/-- Maximality of `T₀` for a diagonal `{a, b}` with `a < b`. -/
private theorem typeC_maximal_of_lt (hn : 2 ≤ n) {a b : ℕ} (ha : a < 2 * n + 2)
    (hb : b < 2 * n + 2) (hab : a < b)
    (hside : ¬(b = a + 1 ∨ a = b + 1 ∨ (a + 1 = 2 * n + 2 ∧ b = 0) ∨
      (b + 1 = 2 * n + 2 ∧ a = 0)))
    (hne : ¬((1 ≤ a ∧ a ≤ n ∧ b = n + 2) ∨ (1 ≤ b ∧ b ≤ n ∧ a = n + 2) ∨
        (a = 1 ∧ n + 3 ≤ b ∧ b ≤ 2 * n + 1) ∨ (b = 1 ∧ n + 3 ≤ a ∧ a ≤ 2 * n + 1))) :
    ∃ f ∈ typeCInitialTriangulation n,
      Cross s((a : ZMod (2 * n + 2)), (b : ZMod (2 * n + 2))) f := by
  by_cases h0 : a = 0
  · subst h0
    by_cases h1 : b ≤ n + 1
    · exact ⟨_, (typeC_mem_iff hn (a := 1) (b := n + 2) (by omega) (by omega)).2 (by omega),
        (typeC_cross_iff ha hb (by omega) (by omega)).2 (by omega)⟩
    · exact ⟨_, (typeC_mem_iff hn (a := 1) (b := b + 1) (by omega) (by omega)).2 (by omega),
        (typeC_cross_iff ha hb (by omega) (by omega)).2 (by omega)⟩
  by_cases h1 : a = 1
  · subst h1
    exact ⟨_, (typeC_mem_iff hn (a := b - 1) (b := n + 2) (by omega) (by omega)).2 (by omega),
      (typeC_cross_iff ha hb (by omega) (by omega)).2 (by omega)⟩
  by_cases h2 : a ≤ n + 1
  · by_cases h3 : b ≤ n + 1
    · exact ⟨_, (typeC_mem_iff hn (a := a + 1) (b := n + 2) (by omega) (by omega)).2 (by omega),
        (typeC_cross_iff ha hb (by omega) (by omega)).2 (by omega)⟩
    · exact ⟨_, (typeC_mem_iff hn (a := 1) (b := n + 2) (by omega) (by omega)).2 (by omega),
        (typeC_cross_iff ha hb (by omega) (by omega)).2 (by omega)⟩
  by_cases h4 : a = n + 2
  · exact ⟨_, (typeC_mem_iff hn (a := 1) (b := b - 1) (by omega) (by omega)).2 (by omega),
      (typeC_cross_iff ha hb (by omega) (by omega)).2 (by omega)⟩
  · exact ⟨_, (typeC_mem_iff hn (a := 1) (b := a + 1) (by omega) (by omega)).2 (by omega),
      (typeC_cross_iff ha hb (by omega) (by omega)).2 (by omega)⟩

/-- **`T₀` is a triangulation** of the `(2n + 2)`-gon. -/
private theorem typeC_isTriangulation (hn : 2 ≤ n) :
    IsTriangulation (typeCInitialTriangulation n) where
  isDiagonal e he := by
    induction e using Sym2.ind with | _ x y => ?_
    obtain ⟨a, ha, rfl⟩ := TypeA.exists_natCast_eq x
    obtain ⟨b, hb, rfl⟩ := TypeA.exists_natCast_eq y
    rw [typeC_mem_iff hn ha hb] at he
    refine ⟨fun h => ?_, ?_⟩
    · rw [Sym2.mk_isDiag_iff, TypeA.natCast_inj_of_lt ha hb] at h
      omega
    · rw [typeC_isSide_iff ha hb]
      omega
  noncrossing e he f hf := by
    induction e using Sym2.ind with | _ x y => ?_
    induction f using Sym2.ind with | _ z w => ?_
    obtain ⟨a, ha, rfl⟩ := TypeA.exists_natCast_eq x
    obtain ⟨b, hb, rfl⟩ := TypeA.exists_natCast_eq y
    obtain ⟨c, hc, rfl⟩ := TypeA.exists_natCast_eq z
    obtain ⟨d, hd, rfl⟩ := TypeA.exists_natCast_eq w
    rw [typeC_mem_iff hn ha hb] at he
    rw [typeC_mem_iff hn hc hd] at hf
    rw [typeC_cross_iff ha hb hc hd]
    rcases he with he | he | he | he <;> rcases hf with hf | hf | hf | hf <;> omega
  maximal e he hne := by
    induction e using Sym2.ind with | _ x y => ?_
    obtain ⟨a, ha, rfl⟩ := TypeA.exists_natCast_eq x
    obtain ⟨b, hb, rfl⟩ := TypeA.exists_natCast_eq y
    have hab : a ≠ b := fun h => he.1 (Sym2.mk_isDiag_iff.2 (by rw [h]))
    have hside := mt (typeC_isSide_iff ha hb).2 he.2
    rw [typeC_mem_iff hn ha hb] at hne
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact typeC_maximal_of_lt hn ha hb h hside hne
    · rw [Sym2.eq_swap]
      exact typeC_maximal_of_lt hn hb ha h (by omega) (by omega)

private theorem typeC_lab_ge {p : Fin (2 * n - 1)} (h : n - 1 ≤ (p : ℕ)) :
    typeCInitialLabelling n p =
      s((((p : ℕ) + 2 - n : ℕ) : ZMod (2 * n + 2)), ((n + 2 : ℕ) : ZMod (2 * n + 2))) :=
  if_pos h

private theorem typeC_lab_lt {p : Fin (2 * n - 1)} (h : (p : ℕ) < n - 1) :
    typeCInitialLabelling n p =
      s(((1 : ℕ) : ZMod (2 * n + 2)), ((2 * n + 1 - p : ℕ) : ZMod (2 * n + 2))) := by
  rw [typeCInitialLabelling, if_neg (by omega), Nat.cast_one]

private theorem typeC_lab_ge_mk {k : ℕ} (hk : k < 2 * n - 1) (h : n - 1 ≤ k) :
    typeCInitialLabelling n ⟨k, hk⟩ =
      s(((k + 2 - n : ℕ) : ZMod (2 * n + 2)), ((n + 2 : ℕ) : ZMod (2 * n + 2))) :=
  typeC_lab_ge h

private theorem typeC_lab_lt_mk {k : ℕ} (hk : k < 2 * n - 1) (h : k < n - 1) :
    typeCInitialLabelling n ⟨k, hk⟩ =
      s(((1 : ℕ) : ZMod (2 * n + 2)), ((2 * n + 1 - k : ℕ) : ZMod (2 * n + 2))) :=
  typeC_lab_lt h

/-- The two cases of the definition of `λ₀`. -/
private theorem typeC_lab_cases (p : Fin (2 * n - 1)) :
    ((p : ℕ) < n - 1 ∧ typeCInitialLabelling n p =
      s(((1 : ℕ) : ZMod (2 * n + 2)), ((2 * n + 1 - p : ℕ) : ZMod (2 * n + 2)))) ∨
    (n - 1 ≤ (p : ℕ) ∧ typeCInitialLabelling n p =
      s((((p : ℕ) + 2 - n : ℕ) : ZMod (2 * n + 2)), ((n + 2 : ℕ) : ZMod (2 * n + 2)))) :=
  (Nat.lt_or_ge (p : ℕ) (n - 1)).imp (fun hp => ⟨hp, typeC_lab_lt hp⟩)
    fun hp => ⟨hp, typeC_lab_ge hp⟩

/-- `λ₀` is a bijection onto `T₀`. -/
private theorem typeC_isTriangulationLabelling (hn : 2 ≤ n) :
    TypeBC.IsTriangulationLabelling (typeCInitialTriangulation n) (typeCInitialLabelling n) := by
  refine ⟨fun p q h => Fin.ext ?_, ?_⟩
  · have hp := p.isLt
    have hq := q.isLt
    obtain ⟨hp', ep⟩ | ⟨hp', ep⟩ := typeC_lab_cases p <;>
      obtain ⟨hq', eq⟩ | ⟨hq', eq⟩ := typeC_lab_cases q <;>
      rw [ep, eq, TypeA.sym2_natCast_eq_iff (by omega) (by omega) (by omega) (by omega)] at h <;>
      omega
  · ext e
    simp only [Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨p, rfl⟩
      have hp := p.isLt
      obtain ⟨hp', ep⟩ | ⟨hp', ep⟩ := typeC_lab_cases p <;>
        rw [ep, typeC_mem_iff hn (by omega) (by omega)] <;> omega
    · intro he
      induction e using Sym2.ind with | _ x y => ?_
      obtain ⟨a, ha, rfl⟩ := TypeA.exists_natCast_eq x
      obtain ⟨b, hb, rfl⟩ := TypeA.exists_natCast_eq y
      rw [typeC_mem_iff hn ha hb] at he
      rcases he with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact ⟨⟨a + n - 2, by omega⟩, by
          rw [typeC_lab_ge_mk _ (by omega)]
          exact typeC_sym2_eq_of (by omega)⟩
      · exact ⟨⟨b + n - 2, by omega⟩, by
          rw [typeC_lab_ge_mk _ (by omega)]
          exact typeC_sym2_eq_of (by omega)⟩
      · exact ⟨⟨2 * n + 1 - b, by omega⟩, by
          rw [typeC_lab_lt_mk _ (by omega)]
          exact typeC_sym2_eq_of (by omega)⟩
      · exact ⟨⟨2 * n + 1 - a, by omega⟩, by
          rw [typeC_lab_lt_mk _ (by omega)]
          exact typeC_sym2_eq_of (by omega)⟩

/-- `λ₀(ι_C(p)) = ω(λ₀(p))`. -/
private theorem typeC_lab_iotaC (p : Fin (2 * n - 1)) :
    typeCInitialLabelling n (TypeBC.iotaC n p) =
      (typeCInitialLabelling n p).map (TypeBC.halfTurn n) := by
  have hp := p.isLt
  have hι := TypeBC.iotaC_val n p
  obtain ⟨h1, e1⟩ | ⟨h1, e1⟩ := typeC_lab_cases p <;>
    obtain ⟨h2, e2⟩ | ⟨h2, e2⟩ := typeC_lab_cases (TypeBC.iotaC n p) <;>
    rw [e1, e2, Sym2.map_mk] <;> simp only [TypeBC.halfTurn, ← Nat.cast_add] <;>
    exact typeC_sym2_eq_of (by omega)

/-- `ι_C` is an involution, pointwise. -/
private theorem typeC_iotaC_iotaC (p : Fin (2 * n - 1)) :
    TypeBC.iotaC n (TypeBC.iotaC n p) = p :=
  DFunLike.congr_fun (TypeBC.iotaC_mul_self n) p

end Initial

/-- **The initial symmetric triangulation.** For `n ≥ 2`, `T₀` is a centrally symmetric
triangulation of the convex `(2n + 2)`-gon and `(T₀, λ₀)` is a symmetric labelled
triangulation. -/
@[cluster_algebras "lem_type_C_initial_triangulation"]
theorem isSymmetricLabelledTriangulation_typeCInitial {n : ℕ} (hn : 2 ≤ n) :
    TypeBC.IsSymmetricLabelledTriangulation n (typeCInitialTriangulation n)
      (typeCInitialLabelling n) := by
  have hlab := typeC_isTriangulationLabelling hn
  have hmem : ∀ e, e ∈ typeCInitialTriangulation n ↔ ∃ p, typeCInitialLabelling n p = e :=
    fun e => by rw [← Finset.mem_coe, ← hlab.2, Set.mem_range]
  refine ⟨typeC_isTriangulation hn, ?_, hlab, typeC_lab_iotaC⟩
  ext e
  rw [Finset.mem_image]
  constructor
  · rintro ⟨e', he', rfl⟩
    obtain ⟨p, rfl⟩ := (hmem e').1 he'
    rw [← typeC_lab_iotaC p]
    exact (hmem _).2 ⟨_, rfl⟩
  · intro he
    obtain ⟨p, rfl⟩ := (hmem e).1 he
    refine ⟨typeCInitialLabelling n (TypeBC.iotaC n p), (hmem _).2 ⟨_, rfl⟩, ?_⟩
    rw [← typeC_lab_iotaC, typeC_iotaC_iotaC]

section InitialMatrix

variable {n : ℕ}

/-- The entries `1` of `B(T₀, λ₀)`: at `(p, p + 1)` for `p + 1 ≤ n - 1` (the triangle
`{1, 2n - p, 2n + 1 - p}`) and at `(p, p - 1)` for `p ≥ n` (the triangle
`{p + 1 - n, p + 2 - n, n + 2}`). -/
private theorem typeC_entry_one (hn : 2 ≤ n) {p q : Fin (2 * n - 1)}
    (h : ((p : ℕ) + 1 = q ∧ (q : ℕ) + 1 ≤ n) ∨ ((q : ℕ) + 1 = p ∧ n ≤ (p : ℕ))) :
    TypeBC.triangulationMatrix (typeCInitialTriangulation n) (typeCInitialLabelling n) p q =
      1 := by
  have hT := typeC_isTriangulation hn
  have hℓ := typeC_isTriangulationLabelling hn
  have hp := p.isLt
  have hq := q.isLt
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have ep : typeCInitialLabelling n p =
        s(((2 * n + 1 - p : ℕ) : ZMod (2 * n + 2)), ((1 : ℕ) : ZMod (2 * n + 2))) := by
      rw [typeC_lab_lt (by omega), Sym2.eq_swap]
    have eq : typeCInitialLabelling n q =
        s(((1 : ℕ) : ZMod (2 * n + 2)), ((2 * n - p : ℕ) : ZMod (2 * n + 2))) := by
      obtain ⟨h, e⟩ | ⟨h, e⟩ := typeC_lab_cases q <;> rw [e] <;>
        exact typeC_sym2_eq_of (by omega)
    refine TypeBC.triangulationMatrix_apply_eq_one hT hℓ ?_ ?_ ep eq
    · exact TypeBC.isTriangle_of_mem_segments (typeC_cast_ne (by omega) (by omega) (by omega))
        (typeC_cast_ne (by omega) (by omega) (by omega))
        (typeC_cast_ne (by omega) (by omega) (by omega))
        ((typeC_mem_segments_iff hn (by omega) (by omega)).2 (by omega))
        ((typeC_mem_segments_iff hn (by omega) (by omega)).2 (by omega))
        ((typeC_mem_segments_iff hn (by omega) (by omega)).2 (by omega))
    · exact (TypeA.sbtw_natCast_iff (by omega) (by omega) (by omega)).2 (by omega)
  · have ep : typeCInitialLabelling n p =
        s((((p : ℕ) + 2 - n : ℕ) : ZMod (2 * n + 2)), ((n + 2 : ℕ) : ZMod (2 * n + 2))) :=
      typeC_lab_ge (by omega)
    have eq : typeCInitialLabelling n q =
        s(((n + 2 : ℕ) : ZMod (2 * n + 2)), (((p : ℕ) + 1 - n : ℕ) : ZMod (2 * n + 2))) := by
      rw [typeC_lab_ge (by omega)]
      exact typeC_sym2_eq_of (by omega)
    refine TypeBC.triangulationMatrix_apply_eq_one hT hℓ ?_ ?_ ep eq
    · exact TypeBC.isTriangle_of_mem_segments (typeC_cast_ne (by omega) (by omega) (by omega))
        (typeC_cast_ne (by omega) (by omega) (by omega))
        (typeC_cast_ne (by omega) (by omega) (by omega))
        ((typeC_mem_segments_iff hn (by omega) (by omega)).2 (by omega))
        ((typeC_mem_segments_iff hn (by omega) (by omega)).2 (by omega))
        ((typeC_mem_segments_iff hn (by omega) (by omega)).2 (by omega))
    · exact (TypeA.sbtw_natCast_iff (by omega) (by omega) (by omega)).2 (by omega)

/-- The vanishing entries of `B(T₀, λ₀)` off the diagonal: two non-adjacent labels have no
common triangle, since two of their endpoints are not joined by a segment of `T₀`. The case
`q < n - 1 ≤ p` follows by skew-symmetry. -/
private theorem typeC_entry_zero (hn : 2 ≤ n) {p q : Fin (2 * n - 1)} (hpq : p ≠ q)
    (h1 : ¬(((p : ℕ) + 1 = q ∧ (q : ℕ) + 1 ≤ n) ∨ ((q : ℕ) + 1 = p ∧ n ≤ (p : ℕ))))
    (h2 : ¬(((q : ℕ) + 1 = p ∧ (p : ℕ) + 1 ≤ n) ∨ ((p : ℕ) + 1 = q ∧ n ≤ (q : ℕ))))
    (hc : ¬((q : ℕ) < n - 1 ∧ n - 1 ≤ (p : ℕ))) :
    TypeBC.triangulationMatrix (typeCInitialTriangulation n) (typeCInitialLabelling n) p q =
      0 := by
  have hT := typeC_isTriangulation hn
  have hℓ := typeC_isTriangulationLabelling hn
  have hp := p.isLt
  have hq := q.isLt
  have hpq' : (p : ℕ) ≠ q := fun h => hpq (Fin.ext h)
  by_contra hne
  obtain ⟨Δ, hΔ, hpΔ, hqΔ⟩ := (TypeBC.triangulationMatrix_apply_ne_zero_iff hT hℓ hpq).1 hne
  have seg : ∀ a b : ℕ, a < 2 * n + 2 → b < 2 * n + 2 → a ≠ b → (a : ZMod (2 * n + 2)) ∈ Δ →
      (b : ZMod (2 * n + 2)) ∈ Δ → (a = b + 1 ∨ b = a + 1 ∨ (a = 1 ∧ n + 3 ≤ b) ∨
        (b = 1 ∧ n + 3 ≤ a) ∨ (a = n + 2 ∧ b ≤ n) ∨ (b = n + 2 ∧ a ≤ n) ∨
        (a + 1 = 2 * n + 2 ∧ b = 0) ∨ (b + 1 = 2 * n + 2 ∧ a = 0)) := by
    intro a b ha hb hab h1 h2
    have h := hΔ.2 _ h1 _ h2 (typeC_cast_ne ha hb hab)
    rw [typeC_mem_segments_iff hn ha hb] at h
    omega
  rcases Nat.lt_or_ge (p : ℕ) (n - 1) with hp' | hp' <;>
    rcases Nat.lt_or_ge (q : ℕ) (n - 1) with hq' | hq'
  · rw [typeC_lab_lt hp', Finset.mk_mem_sym2_iff] at hpΔ
    rw [typeC_lab_lt hq', Finset.mk_mem_sym2_iff] at hqΔ
    have := seg _ _ (by omega) (by omega) (by omega) hpΔ.2 hqΔ.2
    omega
  · rw [typeC_lab_lt hp', Finset.mk_mem_sym2_iff] at hpΔ
    rw [typeC_lab_ge hq', Finset.mk_mem_sym2_iff] at hqΔ
    by_cases hq'' : (q : ℕ) = n - 1
    · have := seg _ _ (by omega) (by omega) (by omega) hqΔ.2 hpΔ.2
      omega
    · have := seg _ _ (by omega) (by omega) (by omega) hqΔ.1 hpΔ.2
      omega
  · exact hc ⟨hq', hp'⟩
  · rw [typeC_lab_ge hp', Finset.mk_mem_sym2_iff] at hpΔ
    rw [typeC_lab_ge hq', Finset.mk_mem_sym2_iff] at hqΔ
    have := seg _ _ (by omega) (by omega) (by omega) hpΔ.1 hqΔ.1
    omega

end InitialMatrix

/-- **The matrix of the initial symmetric triangulation**: `B(T₀, λ₀) = U^{(n)}` for `n ≥ 2`. -/
@[cluster_algebras "lem_type_C_initial_matrix"]
theorem triangulationMatrix_typeCInitial {n : ℕ} (hn : 2 ≤ n) :
    TypeBC.triangulationMatrix (typeCInitialTriangulation n) (typeCInitialLabelling n) =
      typeCUnfoldingMatrix n := by
  ext p q
  have hp := p.isLt
  have hq := q.isLt
  have hU : typeCUnfoldingMatrix n p q =
      if ((p : ℕ) + 1 = q ∧ (q : ℕ) + 1 ≤ n) ∨ ((q : ℕ) + 1 = p ∧ n ≤ (p : ℕ)) then 1
      else if ((q : ℕ) + 1 = p ∧ (p : ℕ) + 1 ≤ n) ∨ ((p : ℕ) + 1 = q ∧ n ≤ (q : ℕ)) then -1
      else 0 := by
    simp only [typeCUnfoldingMatrix, of_apply]
    split_ifs <;> omega
  rw [hU]
  split_ifs with h1 h2
  · exact typeC_entry_one hn h1
  · rw [TypeBC.triangulationMatrix_apply_eq_neg, typeC_entry_one hn h2]
  · by_cases hpq : p = q
    · subst hpq
      have := TypeBC.triangulationMatrix_apply_eq_neg (typeCInitialTriangulation n)
        (typeCInitialLabelling n) p p
      omega
    · by_cases hc : (q : ℕ) < n - 1 ∧ n - 1 ≤ (p : ℕ)
      · rw [TypeBC.triangulationMatrix_apply_eq_neg,
          typeC_entry_zero hn (Ne.symm hpq) h2 h1 (by omega), neg_zero]
      · exact typeC_entry_zero hn hpq h1 h2 hc

/-! ### The unfolding is globally foldable -/

/-- **`U^{(n)}` is skew-symmetric.** -/
@[cluster_algebras "lem_type_C_unfolding"]
theorem typeCUnfoldingMatrix_apply_eq_neg (n : ℕ) (p q : Fin (2 * n - 1)) :
    typeCUnfoldingMatrix n p q = -typeCUnfoldingMatrix n q p := by
  simp only [typeCUnfoldingMatrix, of_apply]
  split_ifs <;> omega

/-- **The Cartan counterpart of `U^{(n)}` is `C(A_{2n-1})`.** Stated for every `n`. -/
@[cluster_algebras "lem_type_C_unfolding"]
theorem cartanCounterpart_typeCUnfoldingMatrix (n : ℕ) :
    cartanCounterpart (typeCUnfoldingMatrix n) = cartanA (2 * n - 1) := by
  ext i j
  simp only [cartanCounterpart, cartanA, typeCUnfoldingMatrix, of_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- The entries of `U^{(n)}` in the left half: `u_{n-1-p, n-1-q}`. -/
theorem typeCUnfoldingMatrix_left (n : ℕ) (p q : Fin n) :
    typeCUnfoldingMatrix n ⟨n - 1 - p, by omega⟩ ⟨n - 1 - q, by omega⟩ =
      if (p : ℕ) = q + 1 then 1 else if (q : ℕ) = p + 1 then -1 else 0 := by
  have := p.isLt
  have := q.isLt
  simp only [typeCUnfoldingMatrix, of_apply]
  split_ifs <;> omega

/-- The entries of `U^{(n)}` from the right half to the left half: `u_{n-1+p, n-1-q}`,
`p ≥ 1`. -/
theorem typeCUnfoldingMatrix_right (n : ℕ) (hn : 2 ≤ n) (p q : Fin n) (hp : 0 < (p : ℕ)) :
    typeCUnfoldingMatrix n ⟨n - 1 + p, by omega⟩ ⟨n - 1 - q, by omega⟩ =
      if (p : ℕ) = 1 ∧ (q : ℕ) = 0 then 1 else 0 := by
  have := p.isLt
  have := q.isLt
  simp only [typeCUnfoldingMatrix, of_apply]
  split_ifs <;> omega

/-- The columns of the orbit `θ_C(r)` are `{n - 1 - r, ι_C(n - 1 - r)}`. -/
theorem thetaC_cols (n : ℕ) (hn : 2 ≤ n) (r : Fin n) :
    (thetaC n hn).cols le_rfl r = {thetaCRep n r, TypeBC.iotaC n (thetaCRep n r)} := by
  ext j
  rw [OrbitLabelling.mem_cols, Finset.mem_insert, Finset.mem_singleton]
  change j ∈ (thetaC n hn).orbit r ↔ _
  rw [thetaC, TypeBC.mem_orbit_orbitLabellingOfReps,
    TypeBC.mem_orbit_zpowers_iff (TypeBC.iotaC_mul_self n)]

/-- **`U^{(n)}` is globally foldable** for the action of `ι_C` and the orbit labelling `θ_C`. -/
@[cluster_algebras "lem_type_C_unfolding"]
theorem isGloballyFoldable_typeCUnfoldingMatrix {n : ℕ} (hn : 2 ≤ n) :
    IsGloballyFoldable (thetaC n hn) le_rfl (typeCUnfoldingMatrix n) := by
  have key : ∀ (ρ : List (Fin n)) (T : Finset (Sym2 (ZMod (2 * n + 2))))
      (ℓ : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))),
      TypeBC.IsSymmetricLabelledTriangulation n T ℓ →
      ∃ (T' : Finset (Sym2 (ZMod (2 * n + 2)))) (ℓ' : Fin (2 * n - 1) → Sym2 (ZMod (2 * n + 2))),
        TypeBC.IsSymmetricLabelledTriangulation n T' ℓ' ∧
        matrixMutationList le_rfl (TypeBC.triangulationMatrix T ℓ)
          (orbitSeq (thetaC n hn) le_rfl ρ) = TypeBC.triangulationMatrix T' ℓ' := by
    intro ρ
    induction ρ with
    | nil => exact fun T ℓ h => ⟨T, ℓ, h, rfl⟩
    | cons r ρ ih =>
      intro T ℓ h
      obtain ⟨T₁, ℓ₁, h₁, e₁⟩ := h.exists_matrixMutationList hn (thetaCRep n r)
      rw [orbitSeq, List.flatMap_cons, matrixMutationList_append, thetaC_cols n hn r, ← e₁]
      exact ih T₁ ℓ₁ h₁
  rw [← triangulationMatrix_typeCInitial hn]
  have h0 := isSymmetricLabelledTriangulation_typeCInitial hn
  refine ⟨h0.isGroupAdmissible hn, fun ρ => ?_⟩
  obtain ⟨T', ℓ', h', e'⟩ := key ρ _ _ h0
  rw [e']
  exact h'.isGroupAdmissible hn

/-- **The folding of `U^{(n)}` is `M(C_n)`**: `(U^{(n)})ᴳ = M(C_n)` for the orbit labelling
`θ_C`. -/
@[cluster_algebras "lem_type_C_unfolding"]
theorem foldedMatrix_thetaC_typeCUnfoldingMatrix {n : ℕ} (hn : 2 ≤ n) :
    foldedMatrix (thetaC n hn) (typeCUnfoldingMatrix n) = typeCMatrix n := by
  ext p q
  have hc : (thetaC n hn).colRep q = ⟨n - 1 - q, by omega⟩ :=
    Fin.ext (thetaC_rep_val n hn _)
  have := p.isLt
  have := q.isLt
  rw [foldedMatrix_apply, thetaC_orbit, hc]
  rcases Nat.eq_zero_or_pos (p : ℕ) with h0 | hp
  · rw [show (⟨n - 1 + p, by omega⟩ : Fin (2 * n - 1)) = ⟨n - 1 - p, by omega⟩ from
      Fin.ext (by simp only; omega), Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
      Finset.sum_singleton, typeCUnfoldingMatrix_left]
    simp only [typeCMatrix, of_apply]
    split_ifs <;> omega
  · rw [Finset.sum_pair (by simp only [ne_eq, Fin.mk.injEq]; omega), typeCUnfoldingMatrix_left,
      typeCUnfoldingMatrix_right n hn p q hp]
    simp only [typeCMatrix, of_apply]
    split_ifs <;> omega

/-! ### Finite type -/

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- **Seed patterns of type `C_n` are of finite type**: for `n ≥ 3`, every seed pattern of type
`C_n` is of finite type. -/
@[cluster_algebras "thm_type_C_finite"]
theorem IsSeedPattern.isFiniteType_of_isPatternOfType_C [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hn : 3 ≤ n)
    (hX : IsPatternOfType hmn P [DynkinSymbol.C n hn]) : IsFiniteType P := by
  obtain ⟨t, ht⟩ := hX
  have hN : 1 ≤ 2 * n - 1 := by omega
  refine TypeBC.isFiniteType_of_sameCartanType_foldedMatrix
    ⟨_, isSkewSymmetrizingVector_typeCMatrix n⟩
    (isFiniteTree_coxeterGraph_cartanCounterpart_typeCMatrix (by omega)) (thetaC n (by omega))
    (typeCUnfoldingMatrix_apply_eq_neg n) (isGloballyFoldable_typeCUnfoldingMatrix (by omega))
    (foldedMatrix_thetaC_typeCUnfoldingMatrix (by omega)) ?_ hmn hP (t := t) ?_
  · rintro F' _ _ m' hm' P' hP' ⟨t', ht'⟩
    refine hP'.isFiniteType_of_typeA hN hm' ⟨t', ?_⟩
    refine (TypeBC.isOfDynkinType_singleton_iff (DynkinSymbol.A _ hN) _).2 ?_
    rw [ht', cartanCounterpart_typeCUnfoldingMatrix]
    exact ⟨Equiv.refl _, fun i j => rfl⟩
  · rw [cartanCounterpart_typeCMatrix]
    exact TypeBC.sameCartanType_symm
      ((TypeBC.isOfDynkinType_singleton_iff (DynkinSymbol.C n hn) _).1 ht)

/-! ### Types `B_n` and `C_n` are different -/

omit [Field K] [Algebra K F] in
/-- A skew-symmetrizing vector of the principal part survives mutation along a sequence. -/
private theorem typeC_isSkewSymmetrizingVector_matrixMutationList (hmn : n ≤ m)
    {B : Matrix (Fin m) (Fin n) ℤ} {d : Fin n → ℤ}
    (hd : IsSkewSymmetrizingVector (principalPart hmn B) d) (s : List (Fin n)) :
    IsSkewSymmetrizingVector (principalPart hmn (matrixMutationList hmn B s)) d := by
  induction s generalizing B with
  | nil => exact hd
  | cons k s ih => exact ih (IsSkewSymmetrizingVector.submatrix_matrixMutation hmn hd k)

/-- **No seed pattern is of both types `B_n` and `C_n`**: for `n ≥ 3`, no seed pattern of rank
`n` is both of type `B_n` and of type `C_n`. -/
@[cluster_algebras "prop_type_B_not_C"]
theorem IsSeedPattern.not_isPatternOfType_B_and_C [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hn : 3 ≤ n) :
    ¬(IsPatternOfType hmn P [DynkinSymbol.B n (Nat.le_of_succ_le hn)] ∧
      IsPatternOfType hmn P [DynkinSymbol.C n hn]) := by
  rintro ⟨hB, hC⟩
  obtain ⟨t₁, π, hπ⟩ :=
    (IsSeedPattern.isPatternOfType_B_iff hmn hP (Nat.le_of_succ_le hn)).1 hB
  obtain ⟨t₂, σ, hσ⟩ := (IsSeedPattern.isPatternOfType_C_iff hmn hP hn).1 hC
  set d : Fin n → ℤ := fun k => if ((π.symm k : Fin n) : ℕ) = 0 then 1 else 2 with hd_def
  have hd₁ : IsSkewSymmetrizingVector (principalPart hmn (P t₁).extExchangeMatrix) d := by
    refine ⟨fun k => by simp only [hd_def]; split_ifs <;> norm_num, fun k l => ?_⟩
    have h := (isSkewSymmetrizingVector_typeBMatrix n).2 (π.symm k) (π.symm l)
    rw [← hπ, ← hπ] at h
    simpa only [Equiv.apply_symm_apply, hd_def] using h
  have hd₂ : IsSkewSymmetrizingVector (principalPart hmn (P t₂).extExchangeMatrix) d := by
    obtain ⟨s, hs⟩ := hP.exists_seedMutationSeq_eq hmn t₁ t₂
    rw [hs, TypeBC.extExchangeMatrix_seedMutationSeq]
    exact typeC_isSkewSymmetrizingVector_matrixMutationList hmn hd₁ s
  have h₁ := hd₂.2 (σ ⟨0, by omega⟩) (σ ⟨1, by omega⟩)
  have h₂ := hd₂.2 (σ ⟨1, by omega⟩) (σ ⟨2, by omega⟩)
  rw [hσ, hσ] at h₁ h₂
  simp only [typeCMatrix, of_apply, Int.cast_id] at h₁ h₂
  norm_num at h₁ h₂
  have e₁ : ((π.symm (σ ⟨1, by omega⟩) : Fin n) : ℕ) = 0 := by
    by_contra h
    simp only [hd_def, if_neg h] at h₁
    split_ifs at h₁ <;> omega
  have e₂ : ((π.symm (σ ⟨2, by omega⟩) : Fin n) : ℕ) = 0 := by
    by_contra h
    simp only [hd_def, if_neg h, if_pos e₁] at h₂
    omega
  have := σ.injective (π.symm.injective (Fin.ext (e₁.trans e₂.symm)))
  simp [Fin.ext_iff] at this

end ClusterAlgebras

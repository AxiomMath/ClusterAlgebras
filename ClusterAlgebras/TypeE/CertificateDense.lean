/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificatePack
public import ClusterAlgebras.TypeE.CertificateCore

/-!
# Checking exchange relations by evaluation at a power of two

The exchange relations `v_X v_Y = ∏ P + ∏ Q` of a certificate are identities in
`L_m = ℤ[X₁^{±1}, …, X_m^{±1}]` between Laurent polynomials with nonnegative coefficients. This
file checks one of them by evaluating both sides at `Xᵢ = 2^{k wᵢ}`, with mixed-radix weights
`wᵢ = r₀ ⋯ r_{i-1}`, `rᵢ` the width in `Xᵢ` of the exponent box of `v_X v_Y`
(`CertificateCheck.evalW`). A Laurent polynomial with exponents in a box of widths `rᵢ` and
coefficients in `[0, 2^k)` is determined by this value, its coefficients being the base-`2^k`
digits (`CertificateCheck.eq_of_evalW_eq`). Coefficients are bounded through the sums of the
coefficients of the variables (`CertificateCheck.augment`).

Each side is then a single natural number: a variable is packed into one number, the binary
digits of its terms placed at their keys and summed in rounds of adjacent pairs
(`CertificateCheck.evalBlocks`), and products are products of numbers. Every operation of the
check is a GMP-backed `Nat` operation in the kernel, their number grows with the number of terms
of the variables rather than with that of the expanded product, and the kernel never builds the
expanded product. The check itself, `CertificateCheck.Raw.relOKD`, is defined in
`ClusterAlgebras.TypeE.CertificateCore`, which imports nothing beyond the core library.

The main statement is `CertificateCheck.Raw.toL_relOKD`.
-/

@[expose] public section

namespace ClusterAlgebras

namespace CertificateCheck

/-! ### Blocks -/

/-- The product of the first `n + 1` values of `f` is `f n` times that of the first `n`. -/
theorem prodBelow_succ (n : ℕ) (f : ℕ → ℕ) : prodBelow (n + 1) f = f n * prodBelow n f :=
  rfl

/-- `Nat.div a b` is `a / b`. -/
theorem nat_div_eq' (a b : ℕ) : Nat.div a b = a / b :=
  rfl

/-- `Nat.mod a b` is `a % b`. -/
theorem nat_mod_eq' (a b : ℕ) : Nat.mod a b = a % b :=
  rfl

/-- Shifting `a` left by `b` bits multiplies it by `2 ^ b`. -/
theorem nat_shiftLeft_eq' (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b :=
  Nat.shiftLeft_eq a b

/-- The number `c · 2^{k a}` of a block `(a, c)`. -/
def blockVal (k : ℕ) (t : ℕ × ℕ) : ℕ :=
  t.2 * 2 ^ (k * t.1)

/-- The value of the block `comb k x y` is the sum of the values of the blocks `x` and `y`. -/
theorem blockVal_comb (k : ℕ) (x y : ℕ × ℕ) :
    blockVal k (comb k x y) = blockVal k x + blockVal k y := by
  obtain ⟨a, c⟩ := x
  obtain ⟨b, d⟩ := y
  simp only [comb, nat_blt_eq_decide, Bool.cond_decide]
  split_ifs with h
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt h
    simp only [blockVal, nat_shiftLeft_eq', Nat.add_eq, Nat.mul_eq, Nat.sub_eq,
      show a + e + 1 - a = e + 1 by omega, Nat.mul_add, pow_add]
    ring
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
    simp only [blockVal, nat_shiftLeft_eq', Nat.add_eq, Nat.mul_eq, Nat.sub_eq,
      show b + e - b = e by omega, Nat.mul_add, pow_add]
    ring

/-- Combining adjacent pairs of blocks by `pairs` preserves the sum of their values. -/
theorem sum_blockVal_pairs (k : ℕ) : ∀ l : List (ℕ × ℕ),
    ((pairs k l).map (blockVal k)).sum = (l.map (blockVal k)).sum
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
    rw [pairs, List.map_cons, List.sum_cons, blockVal_comb, sum_blockVal_pairs k rest]
    simp [add_assoc]

/-- Folding a list of blocks by `comb` gives a block whose value is the sum of their values. -/
theorem blockVal_foldr_comb (k : ℕ) (l : List (ℕ × ℕ)) :
    blockVal k (l.foldr (comb k) (0, 0)) = (l.map (blockVal k)).sum := by
  induction l with
  | nil => simp [blockVal]
  | cons x l ih => rw [List.foldr_cons, blockVal_comb, ih, List.map_cons, List.sum_cons]

/-- The value of the block `collapse k f l` is the sum of the values of the blocks of `l`. -/
theorem blockVal_collapse (k : ℕ) : ∀ (f : ℕ) (l : List (ℕ × ℕ)),
    blockVal k (collapse k f l) = (l.map (blockVal k)).sum
  | 0, [] => by simp [collapse, blockVal]
  | _ + 1, [] => by simp [collapse, blockVal]
  | _, [x] => by simp [collapse]
  | 0, x :: y :: rest => by rw [collapse, blockVal_foldr_comb]
  | f + 1, x :: y :: rest => by rw [collapse, blockVal_collapse k f, sum_blockVal_pairs]

/-- `evalBlocks k l` is the sum of the values `c · 2^{k a}` of the blocks `(a, c)` of `l`. -/
theorem evalBlocks_eq (k : ℕ) (l : List (ℕ × ℕ)) :
    evalBlocks k l = (l.map (blockVal k)).sum := by
  rw [← blockVal_collapse k 16 l, evalBlocks, nat_shiftLeft_eq', Nat.mul_eq, blockVal]

/-! ### Term codes -/

/-- The base-`32` number with digits `d 0, …, d (m - 1)` is `∑_{j < m} d j · 32^j`. -/
theorem ofDigits_map_range (d : ℕ → ℕ) : ∀ m : ℕ,
    Nat.ofDigits 32 ((List.range m).map d) = ∑ j ∈ Finset.range m, d j * 32 ^ j
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ofDigits_map_range d m,
      Finset.sum_range_succ, List.length_map, List.length_range, List.map_singleton,
      Nat.ofDigits_singleton, mul_comm (32 ^ m)]

/-- `unitCode m i` is the base-`32` number with digit `17` at `i`, `16` at the other positions
below `m`, and `1` at position `m`. -/
theorem unitCode_eq (m i : ℕ) : unitCode m i =
    Nat.ofDigits 32 ((List.range m).map (fun j => bif Nat.beq j i then 17 else 16) ++ [1]) := by
  rw [Nat.ofDigits_append, ofDigits_map_range, List.length_map, List.length_range,
    Nat.ofDigits_singleton, unitCode, sumBelow_eq, mul_one]
  rfl

/-- The code `unitCode m i` decodes to the term `(unitExp m i, 1)`, that is, to `Xᵢ`. -/
theorem decodeTerm_unitCode (m i : ℕ) : decodeTerm m (unitCode m i) = (unitExp m i, 1) := by
  set L := (List.range m).map (fun j => bif Nat.beq j i then 17 else 16) ++ [1] with hL
  have hlt : ∀ l ∈ L, l < 32 := by
    intro l hl
    simp only [hL, List.mem_append, List.mem_map, List.mem_singleton] at hl
    rcases hl with ⟨j, -, rfl⟩ | rfl
    · cases Nat.beq j i <;> decide
    · decide
  have hlen : ((List.range m).map (fun j => bif Nat.beq j i then 17 else 16)).length = m := by
    simp
  have hdiv : ∀ j, unitCode m i / 32 ^ j = Nat.ofDigits 32 (L.drop j) := fun j => by
    rw [unitCode_eq]
    exact Nat.ofDigits_div_pow_eq_ofDigits_drop j (by decide) L hlt
  refine Prod.ext ?_ ?_
  · simp only [decodeTerm, unitExp]
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.1 hj
    have hjL : j < L.length := by
      simp [hL]
      omega
    have hd : digit (unitCode m i) 32 j = bif Nat.beq j i then 17 else 16 := by
      rw [digit, nat_div_eq', Nat.pow_eq, hdiv, List.drop_eq_getElem_cons hjL, nat_mod_eq',
        Nat.ofDigits_mod_eq_head!, List.head!_cons]
      simp only [hL, List.getElem_append_left (hlen ▸ hj : j < _), List.getElem_map,
        List.getElem_range]
      cases Nat.beq j i <;> rfl
    rw [hd, nat_beq_eq_decide]
    by_cases h : j = i <;> simp [h]
  · simp only [decodeTerm, nat_div_eq', Nat.pow_eq, hdiv, hL, List.drop_left' hlen,
      Nat.ofDigits_singleton]
    norm_num

/-- `loDig cs i` is at most the digit of exponent `i` of every code in `cs`. -/
theorem loDig_le {cs : List ℕ} {x : ℕ} (hx : x ∈ cs) (i : ℕ) : loDig cs i ≤ dg x i := by
  induction cs with
  | nil => cases hx
  | cons y cs ih =>
    simp only [loDig, List.foldr_cons, nat_blt_eq_decide, Bool.cond_decide] at ih ⊢
    rcases List.mem_cons.1 hx with rfl | hx
    · split_ifs <;> omega
    · have := ih hx
      split_ifs <;> omega

/-- `hiDig cs i` is at least the digit of exponent `i` of every code in `cs`. -/
theorem le_hiDig {cs : List ℕ} {x : ℕ} (hx : x ∈ cs) (i : ℕ) : dg x i ≤ hiDig cs i := by
  induction cs with
  | nil => cases hx
  | cons y cs ih =>
    simp only [hiDig, List.foldr_cons, nat_blt_eq_decide, Bool.cond_decide] at ih ⊢
    rcases List.mem_cons.1 hx with rfl | hx
    · split_ifs <;> omega
    · have := ih hx
      split_ifs <;> omega

/-! ### Evaluation at powers of two -/

/-- `e ↦ ∑ᵢ eᵢ wᵢ`. -/
def weightHom (m : ℕ) (w : ℕ → ℕ) : (Fin m → ℤ) →+ ℤ where
  toFun e := ∑ i, e i * (w i : ℤ)
  map_zero' := by simp
  map_add' e e' := by simp [add_mul, Finset.sum_add_distrib]

/-- `weightHom m w e = ∑ᵢ eᵢ wᵢ`. -/
theorem weightHom_apply (m : ℕ) (w : ℕ → ℕ) (e : Fin m → ℤ) :
    weightHom m w e = ∑ i, e i * (w i : ℤ) :=
  rfl

/-- `T ↦ 2^k` on `ℤ[T^{±1}]`. -/
noncomputable def evalTwo (k : ℕ) : AddMonoidAlgebra ℤ ℤ →+* ℚ :=
  (AddMonoidAlgebra.lift ℤ ℚ ℤ ((Units.coeHom ℚ).comp
    (zpowersHom ℚˣ (Units.mk0 ((2 : ℚ) ^ k) (by positivity))))).toRingHom

/-- `evalTwo k` sends `c Tⁿ` to `c (2^k)ⁿ`. -/
theorem evalTwo_single (k : ℕ) (n c : ℤ) :
    evalTwo k (AddMonoidAlgebra.single n c) = c * ((2 : ℚ) ^ k) ^ n := by
  change AddMonoidAlgebra.lift ℤ ℚ ℤ _ (AddMonoidAlgebra.single n c) = _
  rw [AddMonoidAlgebra.lift_single]
  simp [zsmul_eq_mul, Units.val_zpow_eq_zpow_val]

/-- `Xᵢ ↦ 2^{k wᵢ}` on `L_m`. -/
noncomputable def evalW (m k : ℕ) (w : ℕ → ℕ) : LaurentRing m →+* ℚ :=
  (evalTwo k).comp (AddMonoidAlgebra.mapDomainRingHom ℤ (weightHom m w))

/-- `evalW m k w` sends the monomial `c Xᵉ` to `c (2^k)^{∑ᵢ eᵢ wᵢ}`. -/
theorem evalW_single (m k : ℕ) (w : ℕ → ℕ) (e : Fin m → ℤ) (c : ℤ) :
    evalW m k w (AddMonoidAlgebra.single e c) = c * ((2 : ℚ) ^ k) ^ weightHom m w e := by
  change evalTwo k (Finsupp.mapDomain (weightHom m w) (Finsupp.single e c)) = _
  rw [Finsupp.mapDomain_single]
  exact evalTwo_single k _ c

/-- The sum of the coefficients, `Xᵢ ↦ 1`. -/
noncomputable def augment (m : ℕ) : LaurentRing m →+* ℤ :=
  (AddMonoidAlgebra.lift ℤ ℤ (Fin m → ℤ) 1).toRingHom

/-- The sum of the coefficients of the monomial `c Xᵉ` is `c`. -/
theorem augment_single (m : ℕ) (e : Fin m → ℤ) (c : ℤ) :
    augment m (AddMonoidAlgebra.single e c) = c := by
  simp [augment, AddMonoidAlgebra.lift_single]

/-- `augment m f` is the sum of the coefficients of `f` over its support. -/
theorem augment_eq_sum (m : ℕ) (f : LaurentRing m) : augment m f = ∑ e ∈ f.support, f e := by
  simp [augment, AddMonoidAlgebra.lift_apply, Finsupp.sum]

/-! ### Nonnegative coefficients -/

/-- A sum of Laurent polynomials with nonnegative coefficients has nonnegative coefficients. -/
theorem nonneg_add {m : ℕ} {f g : LaurentRing m} (hf : ∀ e, 0 ≤ f e) (hg : ∀ e, 0 ≤ g e) :
    ∀ e, 0 ≤ (f + g) e := fun e => by
  change 0 ≤ f e + g e
  exact add_nonneg (hf e) (hg e)

/-- A product of Laurent polynomials with nonnegative coefficients has nonnegative
coefficients. -/
theorem nonneg_mul {m : ℕ} {f g : LaurentRing m} (hf : ∀ e, 0 ≤ f e) (hg : ∀ e, 0 ≤ g e) :
    ∀ e, 0 ≤ (f * g) e := fun e => by
  classical
  rw [AddMonoidAlgebra.mul_apply]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  dsimp only
  split_ifs
  exacts [mul_nonneg (hf a) (hg b), le_rfl]

/-- The coefficients of `1` are nonnegative. -/
theorem nonneg_one (m : ℕ) : ∀ e, 0 ≤ (1 : LaurentRing m) e := fun e => by
  classical
  rw [AddMonoidAlgebra.one_def, Finsupp.single_apply]
  split_ifs <;> norm_num

/-- A power of a Laurent polynomial with nonnegative coefficients has nonnegative
coefficients. -/
theorem nonneg_pow {m : ℕ} {f : LaurentRing m} (hf : ∀ e, 0 ≤ f e) :
    ∀ n : ℕ, ∀ e, 0 ≤ (f ^ n) e
  | 0 => by simpa using nonneg_one m
  | n + 1 => by
    rw [pow_succ]
    exact nonneg_mul (nonneg_pow hf n) hf

/-- Each coefficient of a Laurent polynomial with nonnegative coefficients is at most the sum of
its coefficients. -/
theorem le_augment {m : ℕ} {f : LaurentRing m} (hf : ∀ e, 0 ≤ f e) (e : Fin m → ℤ) :
    f e ≤ augment m f := by
  rw [augment_eq_sum]
  by_cases he : e ∈ f.support
  · exact Finset.single_le_sum (fun e _ => hf e) he
  · rw [Finsupp.notMem_support_iff.1 he]
    exact Finset.sum_nonneg fun e _ => hf e

/-! ### Boxes -/

/-- The box of exponent vectors `e` with `loᵢ ≤ eᵢ ≤ hiᵢ`. -/
def boxI (m : ℕ) (lo hi : Fin m → ℤ) : Set (Fin m → ℤ) :=
  {e | ∀ i, lo i ≤ e i ∧ e i ≤ hi i}

/-- The box of exponent vectors `e` with `Gᵢ ≤ eᵢ < Gᵢ + rᵢ`. -/
def boxR (m : ℕ) (G : Fin m → ℤ) (r : ℕ → ℕ) : Set (Fin m → ℤ) :=
  {e | ∀ i, G i ≤ e i ∧ e i < G i + r i}

/-- If the supports of `f` and `g` lie in the boxes `[lo, hi]` and `[lo', hi']`, that of `f * g`
lies in `[lo + lo', hi + hi']`. -/
theorem support_mul_subset_boxI {m : ℕ} {lo hi lo' hi' : Fin m → ℤ} {f g : LaurentRing m}
    (hf : ↑f.support ⊆ boxI m lo hi) (hg : ↑g.support ⊆ boxI m lo' hi') :
    ↑(f * g).support ⊆ boxI m (lo + lo') (hi + hi') := by
  classical
  intro e he
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_mul f g he)
  intro i
  simp only [Pi.add_apply]
  constructor <;> linarith [(hf hx i).1, (hf hx i).2, (hg hy i).1, (hg hy i).2]

/-- The support of `1` lies in the box `[0, 0]`. -/
theorem support_one_subset_boxI (m : ℕ) : ↑(1 : LaurentRing m).support ⊆ boxI m 0 0 := by
  classical
  intro e he
  obtain rfl : e = 0 := by simpa using Finsupp.support_single_subset (Finset.mem_coe.1 he)
  intro i
  simp

/-- If the support of `f` lies in the box `[lo, hi]`, that of `f ^ n` lies in
`[n • lo, n • hi]`. -/
theorem support_pow_subset_boxI {m : ℕ} {lo hi : Fin m → ℤ} {f : LaurentRing m}
    (hf : ↑f.support ⊆ boxI m lo hi) :
    ∀ n : ℕ, ↑(f ^ n).support ⊆ boxI m (n • lo) (n • hi)
  | 0 => by simpa using support_one_subset_boxI m
  | n + 1 => by
    rw [pow_succ, succ_nsmul, succ_nsmul]
    exact support_mul_subset_boxI (support_pow_subset_boxI hf n) hf

/-- The box `[lo, hi]` is contained in `[lo', hi']` when `lo' ≤ lo` and `hi ≤ hi'`. -/
theorem boxI_mono {m : ℕ} {lo hi lo' hi' : Fin m → ℤ} (hlo : ∀ i, lo' i ≤ lo i)
    (hhi : ∀ i, hi i ≤ hi' i) : boxI m lo hi ⊆ boxI m lo' hi' :=
  fun _ he i => ⟨(hlo i).trans (he i).1, (he i).2.trans (hhi i)⟩

/-! ### Mixed radix -/

/-- `∑_{i ≤ m} eᵢ wᵢ` is `∑_{i < m} eᵢ wᵢ + e_m w_m`. -/
theorem weightHom_succ (m : ℕ) (w : ℕ → ℕ) (e : Fin (m + 1) → ℤ) :
    weightHom (m + 1) w e = weightHom m w (fun i => e i.castSucc) + e (Fin.last m) * w m := by
  simp [weightHom_apply, Fin.sum_univ_castSucc]

/-- If `0 ≤ eᵢ < rᵢ` for all `i`, then `0 ≤ ∑ᵢ eᵢ r₀ ⋯ r_{i-1} < r₀ ⋯ r_{m-1}`. -/
theorem weightHom_bounds {r : ℕ → ℕ} : ∀ {m : ℕ} {e : Fin m → ℤ}, (∀ i, 0 ≤ e i ∧ e i < r i) →
    0 ≤ weightHom m (fun i => prodBelow i r) e ∧
      weightHom m (fun i => prodBelow i r) e < prodBelow m r
  | 0, e, _ => by simp [weightHom_apply, prodBelow]
  | m + 1, e, he => by
    rw [weightHom_succ]
    have ih := weightHom_bounds (m := m) (e := fun i => e i.castSucc) fun i => he _
    have hl := he (Fin.last m)
    simp only [Fin.val_last] at hl
    rw [prodBelow_succ]
    push_cast
    constructor
    · exact add_nonneg ih.1 (mul_nonneg hl.1 (by positivity))
    · have : e (Fin.last m) + 1 ≤ r m := by omega
      nlinarith

/-- The mixed-radix value `e ↦ ∑ᵢ eᵢ r₀ ⋯ r_{i-1}` is injective on the box `[0, r)`. -/
theorem weightHom_injOn {r : ℕ → ℕ} : ∀ {m : ℕ},
    Set.InjOn (weightHom m (fun i => prodBelow i r)) (boxR m 0 r)
  | 0 => fun e _ e' _ _ => funext fun i => i.elim0
  | m + 1 => fun e he e' he' h => by
    have he0 : ∀ i, 0 ≤ e i ∧ e i < r i := fun i => by simpa using he i
    have he0' : ∀ i, 0 ≤ e' i ∧ e' i < r i := fun i => by simpa using he' i
    rw [weightHom_succ, weightHom_succ] at h
    have b := weightHom_bounds (r := r) (e := fun i => e i.castSucc) fun i => he0 _
    have b' := weightHom_bounds (r := r) (e := fun i => e' i.castSucc) fun i => he0' _
    have hlast : e (Fin.last m) = e' (Fin.last m) := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt <;> nlinarith
    rw [hlast, add_left_inj] at h
    have hinit := weightHom_injOn (r := r) (m := m)
      (fun i => by simpa using he0 i.castSucc) (fun i => by simpa using he0' i.castSucc) h
    funext i
    cases i using Fin.lastCases with
    | last => exact hlast
    | cast i => exact congrFun hinit i

/-! ### Digits -/

/-- If the exponents of `u ∈ ℤ[T^{±1}]` lie in `[0, M)`, then
`evalTwo k u = ∑_{j < M} u_j (2^k)^j`. -/
theorem evalTwo_eq_sum {k M : ℕ} {u : AddMonoidAlgebra ℤ ℤ}
    (hu : ∀ n ∈ u.support, 0 ≤ n ∧ n < M) :
    evalTwo k u = ∑ j ∈ Finset.range M, (u j : ℚ) * ((2 : ℚ) ^ k) ^ j := by
  classical
  have hsub : u.support ⊆ (Finset.range M).map ⟨Nat.cast, Nat.cast_injective⟩ := by
    intro n hn
    obtain ⟨h0, h1⟩ := hu n hn
    refine Finset.mem_map.2 ⟨n.toNat, Finset.mem_range.2 (by omega), ?_⟩
    simp [Int.toNat_of_nonneg h0]
  have hu' : u = ∑ n ∈ u.support, AddMonoidAlgebra.single n (u n) :=
    (Finsupp.sum_single u).symm
  conv_lhs => rw [hu']
  rw [map_sum, Finset.sum_subset hsub, Finset.sum_map]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Function.Embedding.coeFn_mk, evalTwo_single, zpow_natCast]
  · intro n _ hn
    rw [Finsupp.notMem_support_iff.1 hn, AddMonoidAlgebra.single_zero, map_zero]

/-- A Laurent polynomial in one variable with exponents in `[0, M)` and coefficients in `[0, 2^k)`
is determined by its value at `T = 2^k`. -/
theorem eq_of_evalTwo_eq {k M : ℕ} {u u' : AddMonoidAlgebra ℤ ℤ}
    (hu : ∀ n ∈ u.support, 0 ≤ n ∧ n < M) (hu' : ∀ n ∈ u'.support, 0 ≤ n ∧ n < M)
    (hc : ∀ n, 0 ≤ u n ∧ u n < 2 ^ k) (hc' : ∀ n, 0 ≤ u' n ∧ u' n < 2 ^ k)
    (h : evalTwo k u = evalTwo k u') : u = u' := by
  rw [evalTwo_eq_sum hu, evalTwo_eq_sum hu'] at h
  have hcast : ∀ v : AddMonoidAlgebra ℤ ℤ, (∀ n, 0 ≤ v n ∧ v n < 2 ^ k) →
      ∑ j ∈ Finset.range M, (v j : ℚ) * ((2 : ℚ) ^ k) ^ j =
        ((∑ j ∈ Finset.range M, (v j).toNat * (2 ^ k) ^ j : ℕ) : ℚ) := fun v hv => by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((v j).toNat : ℚ) = ((v j).toNat : ℤ) by norm_cast, Int.toNat_of_nonneg (hv j).1]
  rw [hcast u hc, hcast u' hc', Nat.cast_inj] at h
  have hlt : ∀ v : AddMonoidAlgebra ℤ ℤ, (∀ n, 0 ≤ v n ∧ v n < 2 ^ k) →
      ∀ j < M, (v j).toNat < 2 ^ k := fun v hv j _ => by
    have h := hv j
    have : ((v j).toNat : ℤ) < ((2 ^ k : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h.1]
      push_cast
      exact h.2
    exact_mod_cast this
  have hd := sum_mul_pow_injOn (hlt u hc) (hlt u' hc') h
  ext n
  by_cases hn : 0 ≤ n ∧ n < M
  · have := hd n.toNat (by omega)
    have h1 := (hc n).1
    have h2 := (hc' n).1
    rw [Int.toNat_of_nonneg hn.1] at this
    omega
  · rw [Finsupp.notMem_support_iff.1 fun h => hn (hu n h),
      Finsupp.notMem_support_iff.1 fun h => hn (hu' n h)]

/-- If `f` has support in the box `[0, r)` and coefficients in `[0, 2^k)`, then so do the
coefficients of its image under the mixed-radix map `e ↦ ∑ᵢ eᵢ r₀ ⋯ r_{i-1}`. -/
theorem mapDomain_bounds {m k : ℕ} {r : ℕ → ℕ} {f : LaurentRing m}
    (hf : ↑f.support ⊆ boxR m 0 r) (hc : ∀ e, 0 ≤ f e ∧ f e < 2 ^ k) (n : ℤ) :
    0 ≤ Finsupp.mapDomain (weightHom m fun i => prodBelow i r) f n ∧
      Finsupp.mapDomain (weightHom m fun i => prodBelow i r) f n < 2 ^ k := by
  classical
  by_cases hn : ∃ e ∈ boxR m 0 r, weightHom m (fun i => prodBelow i r) e = n
  · obtain ⟨e, he, rfl⟩ := hn
    rw [Finsupp.mapDomain_apply' _ _ hf weightHom_injOn he]
    exact hc e
  · have : n ∉ (Finsupp.mapDomain (weightHom m fun i => prodBelow i r) f).support := by
      intro h
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h)
      exact hn ⟨e, hf he, rfl⟩
    rw [Finsupp.notMem_support_iff.1 this]
    norm_num

/-- **Digits.** A Laurent polynomial with exponents in the box `[G, G + r)` and coefficients in
`[0, 2^k)` is determined by its value at `Xᵢ = 2^{k wᵢ}`, `wᵢ = r₀ ⋯ r_{i-1}`. -/
theorem eq_of_evalW_eq {m k : ℕ} {G : Fin m → ℤ} {r : ℕ → ℕ} {f g : LaurentRing m}
    (hf : ↑f.support ⊆ boxR m G r) (hg : ↑g.support ⊆ boxR m G r)
    (hcf : ∀ e, 0 ≤ f e ∧ f e < 2 ^ k) (hcg : ∀ e, 0 ≤ g e ∧ g e < 2 ^ k)
    (h : evalW m k (fun i => prodBelow i r) f = evalW m k (fun i => prodBelow i r) g) :
    f = g := by
  set s : LaurentRing m := AddMonoidAlgebra.single (-G) 1 with hs
  have hshift : ∀ (x : LaurentRing m) (e : Fin m → ℤ), (s * x) e = x (G + e) := fun x e => by
    rw [hs, AddMonoidAlgebra.single_mul_apply, neg_neg, one_mul]
  have hsupp : ∀ x : LaurentRing m, ↑x.support ⊆ boxR m G r → ↑(s * x).support ⊆ boxR m 0 r := by
    intro x hx e he
    have hne : x (G + e) ≠ 0 := by
      rw [← hshift]
      exact Finsupp.mem_support_iff.1 he
    have hb := hx (Finsupp.mem_support_iff.2 hne)
    intro i
    have := hb i
    simp only [Pi.add_apply, Pi.zero_apply, zero_add] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hc : ∀ x : LaurentRing m, (∀ e, 0 ≤ x e ∧ x e < 2 ^ k) →
      ∀ e, 0 ≤ (s * x) e ∧ (s * x) e < 2 ^ k := fun x hx e => by
    rw [hshift]
    exact hx _
  have hsuppΦ : ∀ x : LaurentRing m, ↑x.support ⊆ boxR m 0 r →
      ∀ n ∈ (Finsupp.mapDomain (weightHom m fun i => prodBelow i r) x).support,
        0 ≤ n ∧ n < prodBelow m r := by
    classical
    intro x hx n hn
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hn)
    exact weightHom_bounds fun i => by simpa using hx he i
  have h' : evalTwo k (Finsupp.mapDomain (weightHom m fun i => prodBelow i r) (s * f)) =
      evalTwo k (Finsupp.mapDomain (weightHom m fun i => prodBelow i r) (s * g)) := by
    change evalW m k _ (s * f) = evalW m k _ (s * g)
    rw [map_mul, map_mul, h]
  have hΦ := eq_of_evalTwo_eq (hsuppΦ _ (hsupp f hf)) (hsuppΦ _ (hsupp g hg))
    (mapDomain_bounds (hsupp f hf) (hc f hcf)) (mapDomain_bounds (hsupp g hg) (hc g hcg)) h'
  have hu : AddMonoidAlgebra.single G (1 : ℤ) * s = 1 := by
    rw [hs, AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul]
    rfl
  calc f = (AddMonoidAlgebra.single G 1 * s) * f := by rw [hu, one_mul]
    _ = AddMonoidAlgebra.single G 1 * (s * g) := by
      rw [mul_assoc,
        Finsupp.mapDomain_injOn (boxR m 0 r) weightHom_injOn (hsupp f hf) (hsupp g hg) hΦ]
    _ = g := by rw [← mul_assoc, hu, one_mul]

/-! ### Term lists given by codes -/

/-- The exponent of `Xᵢ` in the term with code `x` is the digit `dg x i` minus `16`. -/
theorem expFun_decodeTerm (m x : ℕ) :
    expFun m (decodeTerm m x).1 = fun i : Fin m => ((dg x i : ℕ) : ℤ) - 16 := by
  funext i
  simp [expFun, decodeTerm, List.getD_eq_getElem?_getD]

/-- The exponents of the Laurent polynomial with term codes `cs` lie in the box
`[loDig cs - 16, hiDig cs - 16]`. -/
theorem support_toL_codes_subset (m : ℕ) (cs : List ℕ) :
    ↑(Poly.toL m (cs.map (decodeTerm m))).support ⊆
      boxI m (fun i => (loDig cs i : ℤ) - 16) (fun i => (hiDig cs i : ℤ) - 16) := by
  classical
  suffices ∀ p : List ℕ, (∀ x ∈ p, x ∈ cs) → ↑(Poly.toL m (p.map (decodeTerm m))).support ⊆
      boxI m (fun i => (loDig cs i : ℤ) - 16) (fun i => (hiDig cs i : ℤ) - 16) from
    this cs fun _ h => h
  intro p hp
  induction p with
  | nil => exact fun e he => absurd rfl (Finset.mem_coe.1 he |> Finsupp.mem_support_iff.1)
  | cons x p ih =>
    rw [List.map_cons, Poly.toL_cons]
    refine (Finset.coe_subset.2 Finsupp.support_add).trans ?_
    rw [Finset.coe_union]
    refine Set.union_subset ?_ (ih fun y hy => hp y (List.mem_cons_of_mem _ hy))
    intro e he
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset (Finset.mem_coe.1 he))
    have hx := hp x (List.mem_cons_self ..)
    intro i
    rw [expFun_decodeTerm]
    have h1 := loDig_le hx i
    have h2 := le_hiDig hx i
    constructor <;> push_cast <;> omega

/-- The Laurent polynomial with term codes `cs` has nonnegative coefficients. -/
theorem nonneg_toL_codes (m : ℕ) (cs : List ℕ) :
    ∀ e, 0 ≤ (Poly.toL m (cs.map (decodeTerm m))) e := by
  classical
  induction cs with
  | nil => exact fun _ => le_rfl
  | cons x cs ih =>
    intro e
    rw [List.map_cons, Poly.toL_cons]
    refine nonneg_add (fun e => ?_) ih e
    rw [AddMonoidAlgebra.single_apply]
    split_ifs
    · simp [decodeTerm]
    · exact le_rfl

/-- The sum of the coefficients of the Laurent polynomial with term codes `cs` is `csum m cs`. -/
theorem augment_toL_codes (m : ℕ) (cs : List ℕ) :
    augment m (Poly.toL m (cs.map (decodeTerm m))) = csum m cs := by
  induction cs with
  | nil => simp [csum]
  | cons x cs ih =>
    rw [List.map_cons, Poly.toL_cons, map_add, ih, augment_single]
    simp [csum, decodeTerm, nat_div_eq', Nat.pow_eq]

/-- If the digits of the code `x` are at least `lo`, the weight `∑ᵢ eᵢ wᵢ` of the exponent `e` of
its term is that of `lo - 16` plus `termKey m lo w x`. -/
theorem weightHom_expFun_decodeTerm (m : ℕ) (w lo : ℕ → ℕ) {x : ℕ}
    (hx : ∀ i < m, lo i ≤ dg x i) :
    weightHom m w (expFun m (decodeTerm m x).1) =
      weightHom m w (fun i => (lo i : ℤ) - 16) + termKey m lo w x := by
  rw [termKey, sumBelow_eq, ← Fin.sum_univ_eq_sum_range (fun i => Nat.mul (Nat.sub (dg x i)
    (lo i)) (w i)), expFun_decodeTerm, weightHom_apply, weightHom_apply, Nat.cast_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.mul_eq, Nat.sub_eq, Nat.cast_mul, Nat.cast_sub (hx i i.2)]
  ring

/-- The value at `Xᵢ = 2^{k wᵢ}` of the Laurent polynomial with term codes `cs` is
`(2^k)^{∑ᵢ (loDig cs i - 16) wᵢ}` times `atomNum m k w cs`. -/
theorem evalW_toL_codes (m k : ℕ) (w : ℕ → ℕ) (cs : List ℕ) :
    evalW m k w (Poly.toL m (cs.map (decodeTerm m))) =
      ((2 : ℚ) ^ k) ^ weightHom m w (fun i => (loDig cs i : ℤ) - 16) * (atomNum m k w cs : ℚ) := by
  have hu : ((2 : ℚ) ^ k) ≠ 0 := by positivity
  suffices ∀ p : List ℕ, (∀ x ∈ p, x ∈ cs) → evalW m k w (Poly.toL m (p.map (decodeTerm m))) =
      ((2 : ℚ) ^ k) ^ weightHom m w (fun i => (loDig cs i : ℤ) - 16) *
        (((p.map fun x => (termKey m (loDig cs) w x, Nat.div x (Nat.pow 32 m))).map
          (blockVal k)).sum : ℕ) by
    rw [this cs fun _ h => h, atomNum, evalBlocks_eq]
  intro p hp
  induction p with
  | nil => simp
  | cons x p ih =>
    rw [List.map_cons, Poly.toL_cons, map_add, ih fun y hy => hp y (List.mem_cons_of_mem _ hy),
      evalW_single, weightHom_expFun_decodeTerm m w (loDig cs)
        fun i _ => loDig_le (hp x (List.mem_cons_self ..)) i,
      zpow_add₀ hu, zpow_natCast]
    simp only [List.map_cons, List.sum_cons, blockVal, decodeTerm, nat_div_eq', Nat.pow_eq,
      Int.cast_natCast]
    push_cast
    rw [pow_mul]
    ring

/-! ### Distinct variables -/

/-- If `distOKD codes m k w c c'` holds, the Laurent polynomials with term codes `codes c` and
`codes c'` are distinct. -/
theorem toL_codes_ne_of_distOKD {codes : ℕ → List ℕ} {m k : ℕ} {w : ℕ → ℕ} {c c' : ℕ}
    (h : distOKD codes m k w c c' = true) :
    Poly.toL m ((codes c).map (decodeTerm m)) ≠ Poly.toL m ((codes c').map (decodeTerm m)) := by
  intro he
  have hu : ((2 : ℚ) ^ k) ≠ 0 := by positivity
  have hΛ : ∀ cs : List ℕ, weightHom m w (fun i => (loDig cs i : ℤ) - 16) =
      (loKey m w cs : ℤ) - 16 * ∑ i : Fin m, (w i : ℤ) := fun cs => by
    rw [weightHom_apply, loKey, sumBelow_eq, ← Fin.sum_univ_eq_sum_range
      (fun i => Nat.mul (loDig cs i) (w i)), Nat.cast_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.mul_eq, Nat.cast_mul]
    ring
  have hE := congrArg (fun f => evalW m k w f * ((2 : ℚ) ^ k) ^ (16 * ∑ i : Fin m, (w i : ℤ))) he
  simp only [evalW_toL_codes, hΛ, mul_comm _ (((2 : ℚ) ^ k) ^ (16 * ∑ i : Fin m, (w i : ℤ))),
    ← mul_assoc, ← zpow_add₀ hu, add_sub_cancel, zpow_natCast, ← pow_mul] at hE
  simp only [distOKD, Bool.not_eq_true', nat_beq_eq_decide, decide_eq_false_iff_not,
    nat_shiftLeft_eq', Nat.mul_eq] at h
  apply h
  have : ((atomNum m k w (codes c) * 2 ^ (k * loKey m w (codes c)) : ℕ) : ℚ) =
      ((atomNum m k w (codes c') * 2 ^ (k * loKey m w (codes c')) : ℕ) : ℚ) := by
    push_cast
    linear_combination hE
  exact_mod_cast this

/-! ### Atoms and monomials -/

namespace Raw

variable (R : Raw)

/-- If `codes c` are term codes of the variables `R.var c` for `c < N`, then the terms with codes
`atomCodes codes m N c` are those of the atom `R.atom m N c`. -/
theorem atomCodes_map {codes : ℕ → List ℕ} {m N : ℕ}
    (hcodes : ∀ c < N, R.var c = (codes c).map (decodeTerm m)) (c : ℕ) :
    (atomCodes codes m N c).map (decodeTerm m) = R.atom m N c := by
  simp only [atomCodes, atom, nat_blt_eq_decide, Bool.cond_decide]
  split_ifs with hc
  · exact (hcodes c hc).symm
  · rw [List.map_singleton, decodeTerm_unitCode]
    rfl

variable {R}

/-- The value at `Xᵢ = 2^{k wᵢ}` of the product of the atoms `l` is
`(2^k)^{∑ᵢ (monoLo codes m N l i - 16 d) wᵢ}` times `monoNum codes m N k w l`, where
`d = degAtoms l`. -/
theorem evalW_toL_prodAtoms {codes : ℕ → List ℕ} {m N : ℕ}
    (hcodes : ∀ c < N, R.var c = (codes c).map (decodeTerm m)) (k : ℕ) (w : ℕ → ℕ) :
    ∀ l : List (ℕ × ℕ), evalW m k w (Poly.toL m (R.prodAtoms m N l)) =
      ((2 : ℚ) ^ k) ^ weightHom m w (fun i => (monoLo codes m N l i : ℤ) - 16 * degAtoms l) *
        (monoNum codes m N k w l : ℚ)
  | [] => by
    rw [toL_prodAtoms]
    simp [monoLo, monoNum, degAtoms, weightHom_apply]
  | t :: l => by
    have hu : ((2 : ℚ) ^ k) ≠ 0 := by positivity
    rw [toL_prodAtoms, List.map_cons, List.prod_cons, map_mul, ← toL_prodAtoms,
      evalW_toL_prodAtoms hcodes k w l, map_pow, ← atomCodes_map R hcodes, evalW_toL_codes]
    have hfun : (fun i : Fin m => ((monoLo codes m N (t :: l) i : ℕ) : ℤ) - 16 * degAtoms (t :: l))
        = t.2 • (fun i : Fin m => ((loDig (atomCodes codes m N t.1) i : ℕ) : ℤ) - 16) +
          (fun i : Fin m => ((monoLo codes m N l i : ℕ) : ℤ) - 16 * degAtoms l) := by
      funext i
      simp only [monoLo, degAtoms, List.map_cons, List.sum_cons, Nat.mul_eq, Pi.add_apply,
        Pi.smul_apply]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    rw [hfun, map_add, map_nsmul, zpow_add₀ hu, nsmul_eq_mul, mul_comm ((t.2 : ℕ) : ℤ),
      zpow_mul, zpow_natCast]
    simp only [monoNum, List.foldr_cons, Nat.mul_eq, Nat.pow_eq]
    push_cast
    ring

/-- The exponents of the product of the atoms `l` lie in the box
`[monoLo codes m N l - 16 d, monoHi codes m N l - 16 d]`, where `d = degAtoms l`. -/
theorem support_toL_prodAtoms_subset {codes : ℕ → List ℕ} {m N : ℕ}
    (hcodes : ∀ c < N, R.var c = (codes c).map (decodeTerm m)) :
    ∀ l : List (ℕ × ℕ), ↑(Poly.toL m (R.prodAtoms m N l)).support ⊆
      boxI m (fun i => (monoLo codes m N l i : ℤ) - 16 * degAtoms l)
        (fun i => (monoHi codes m N l i : ℤ) - 16 * degAtoms l)
  | [] => by
    rw [toL_prodAtoms]
    have h0 : (fun i : Fin m => ((monoLo codes m N [] i : ℕ) : ℤ) - 16 * degAtoms []) = 0 := by
      funext i
      simp [monoLo, degAtoms]
    have h0' : (fun i : Fin m => ((monoHi codes m N [] i : ℕ) : ℤ) - 16 * degAtoms []) = 0 := by
      funext i
      simp [monoHi, degAtoms]
    rw [h0, h0']
    exact support_one_subset_boxI m
  | t :: l => by
    rw [toL_prodAtoms, List.map_cons, List.prod_cons, ← toL_prodAtoms, ← atomCodes_map R hcodes]
    have h := support_mul_subset_boxI (support_pow_subset_boxI
      (support_toL_codes_subset m (atomCodes codes m N t.1)) t.2)
      (support_toL_prodAtoms_subset hcodes l)
    refine h.trans (boxI_mono (fun i => le_of_eq ?_) (fun i => le_of_eq ?_)) <;>
    · simp only [monoLo, monoHi, degAtoms, List.map_cons, List.sum_cons, Nat.mul_eq, Pi.add_apply,
        Pi.smul_apply]
      simp only [nsmul_eq_mul]
      push_cast
      ring

/-- The product of the atoms `l` has nonnegative coefficients. -/
theorem nonneg_toL_prodAtoms {codes : ℕ → List ℕ} {m N : ℕ}
    (hcodes : ∀ c < N, R.var c = (codes c).map (decodeTerm m)) (l : List (ℕ × ℕ)) :
    ∀ e, 0 ≤ (Poly.toL m (R.prodAtoms m N l)) e := by
  rw [toL_prodAtoms]
  induction l with
  | nil => exact nonneg_one m
  | cons t l ih =>
    rw [List.map_cons, List.prod_cons, ← atomCodes_map R hcodes]
    exact nonneg_mul (nonneg_pow (nonneg_toL_codes m _) _) ih

/-- The sum of the coefficients of the product of the atoms `l` is `monoSum codes m N l`. -/
theorem augment_toL_prodAtoms {codes : ℕ → List ℕ} {m N : ℕ}
    (hcodes : ∀ c < N, R.var c = (codes c).map (decodeTerm m)) (l : List (ℕ × ℕ)) :
    augment m (Poly.toL m (R.prodAtoms m N l)) = monoSum codes m N l := by
  rw [toL_prodAtoms]
  induction l with
  | nil => simp [monoSum]
  | cons t l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih, map_pow, ← atomCodes_map R hcodes,
      augment_toL_codes]
    simp [monoSum, Nat.pow_eq]

/-! ### The relation check -/

/-- If `R.monoBoxOK codes m N r l` holds, then for `i < m`, with `d = degAtoms l`,
`relLo + 16 d ≤ monoLo + 32` and `monoHi + 32 ≤ relHi + 16 d` in exponent `i`. -/
theorem monoBoxOK_spec {codes : ℕ → List ℕ} {m N r : ℕ} {l : List (ℕ × ℕ)}
    (h : R.monoBoxOK codes m N r l = true) (i : ℕ) (hi : i < m) :
    R.relLo codes m N r i + 16 * degAtoms l ≤ monoLo codes m N l i + 32 ∧
      monoHi codes m N l i + 32 ≤ R.relHi codes m N r i + 16 * degAtoms l := by
  simpa only [Bool.and_eq_true, nat_ble_eq_decide, decide_eq_true_eq, Nat.add_eq,
    Nat.mul_eq] using allBelow_iff.1 h i hi

/-- If `R.monoBoxOK codes m N r l` holds, the weight of `monoLo codes m N l - 16 · degAtoms l` is
that of `R.relLo codes m N r - 32` plus `R.monoShift codes m N r l`. -/
theorem weightHom_monoLo {codes : ℕ → List ℕ} {m N r : ℕ} {l : List (ℕ × ℕ)}
    (h : R.monoBoxOK codes m N r l = true) :
    weightHom m (R.relW codes m N r)
        (fun i => (monoLo codes m N l i : ℤ) - 16 * degAtoms l) =
      weightHom m (R.relW codes m N r) (fun i => (R.relLo codes m N r i : ℤ) - 32) +
        R.monoShift codes m N r l := by
  rw [monoShift, sumBelow_eq, ← Fin.sum_univ_eq_sum_range (fun i => Nat.mul (Nat.sub
    (Nat.add (monoLo codes m N l i) 32) (Nat.add (R.relLo codes m N r i)
      (Nat.mul 16 (degAtoms l)))) (R.relW codes m N r i)), weightHom_apply, weightHom_apply,
    Nat.cast_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hb := (monoBoxOK_spec h i i.2).1
  rw [Nat.mul_eq, Nat.sub_eq, Nat.add_eq, Nat.add_eq, Nat.mul_eq, Nat.cast_mul,
    Nat.cast_sub hb]
  push_cast
  ring

/-- A Laurent polynomial with nonnegative coefficients whose coefficient sum is below `2 ^ k` has
all its coefficients in `[0, 2 ^ k)`. -/
theorem coeff_bounds_of_augment_lt {m k : ℕ} {f : LaurentRing m} (hf : ∀ e, 0 ≤ f e)
    (h : augment m f < 2 ^ k) : ∀ e, 0 ≤ f e ∧ f e < 2 ^ k :=
  fun e => ⟨hf e, (le_augment hf e).trans_lt h⟩

/-- For an atom `c < N`, its value is given by its list of codes. -/
theorem var_eq_atomCodes {codes : ℕ → List ℕ} {m N c : ℕ}
    (hcodes : ∀ c < N, R.var c = (codes c).map (decodeTerm m)) (hc : c < N) :
    R.var c = (atomCodes codes m N c).map (decodeTerm m) := by
  rw [atomCodes_map R hcodes]
  simp [atom, nat_blt_eq_decide, hc]

/-- The box `[relLo - 32, relHi - 32]` of the relation `r` lies in the box of radix `relRad`. -/
theorem boxI_subset_boxR_relRad (codes : ℕ → List ℕ) (m N r : ℕ) :
    boxI m (fun i => (R.relLo codes m N r i : ℤ) - 32) (fun i => (R.relHi codes m N r i : ℤ) - 32)
      ⊆ boxR m (fun i => (R.relLo codes m N r i : ℤ) - 32) (R.relRad codes m N r) := by
  intro e he i
  have := he i
  simp only [relRad, Nat.add_eq, Nat.sub_eq] at this ⊢
  omega

/-- If `R.monoBoxOK codes m N r l` holds, the exponents of the product of the atoms `l` lie in
the box of the relation `r`. -/
theorem support_toL_prodAtoms_subset_boxR {codes : ℕ → List ℕ} {m N r : ℕ}
    (hcodes : ∀ c < N, R.var c = (codes c).map (decodeTerm m)) {l : List (ℕ × ℕ)}
    (hl : R.monoBoxOK codes m N r l = true) :
    ↑(Poly.toL m (R.prodAtoms m N l)).support ⊆
      boxR m (fun i => (R.relLo codes m N r i : ℤ) - 32) (R.relRad codes m N r) := by
  refine (support_toL_prodAtoms_subset hcodes l).trans ((boxI_mono (fun i => ?_)
    (fun i => ?_)).trans (boxI_subset_boxR_relRad (R := R) codes m N r))
  · have := (monoBoxOK_spec hl i i.2).1
    omega
  · have := (monoBoxOK_spec hl i i.2).2
    omega

/-- The exponents of `v_X v_Y` lie in the box of the relation `r`. -/
theorem support_toL_mul_subset_boxR {codes : ℕ → List ℕ} {m N r : ℕ}
    (hcodes : ∀ c < N, R.var c = (codes c).map (decodeTerm m)) (hX : R.relX r < N)
    (hY : R.relY r < N) :
    ↑(Poly.toL m (R.var (R.relX r)) * Poly.toL m (R.var (R.relY r))).support ⊆
      boxR m (fun i => (R.relLo codes m N r i : ℤ) - 32) (R.relRad codes m N r) := by
  rw [var_eq_atomCodes hcodes hX, var_eq_atomCodes hcodes hY]
  refine (support_mul_subset_boxI (support_toL_codes_subset m _)
    (support_toL_codes_subset m _)).trans ((boxI_mono (fun i => le_of_eq ?_)
      (fun i => le_of_eq ?_)).trans (boxI_subset_boxR_relRad (R := R) codes m N r)) <;>
  · simp only [relLo, relHi, Nat.add_eq, Pi.add_apply]
    push_cast
    ring

/-- The weight of `relLo - 32` is the sum of the weights of `loDig - 16` for `v_X` and `v_Y`. -/
theorem weightHom_relLo (codes : ℕ → List ℕ) (m N r : ℕ) :
    weightHom m (R.relW codes m N r) (fun i => (R.relLo codes m N r i : ℤ) - 32) =
      weightHom m (R.relW codes m N r)
          (fun i => (loDig (atomCodes codes m N (R.relX r)) i : ℤ) - 16) +
        weightHom m (R.relW codes m N r)
          (fun i => (loDig (atomCodes codes m N (R.relY r)) i : ℤ) - 16) := by
  rw [← map_add]
  congr 1
  funext i
  simp only [relLo, Nat.add_eq, Pi.add_apply]
  push_cast
  ring

/-- **Soundness of the relation check by evaluation.** -/
theorem toL_relOKD {codes : ℕ → List ℕ} {m N r : ℕ}
    (hcodes : ∀ c < N, R.var c = (codes c).map (decodeTerm m))
    (h : R.relOKD codes m N r = true) :
    Poly.toL m (R.var (R.relX r)) * Poly.toL m (R.var (R.relY r)) =
      Poly.toL m (R.prodAtoms m N (R.relPos r)) + Poly.toL m (R.prodAtoms m N (R.relNeg r)) := by
  simp only [relOKD, Bool.and_eq_true, nat_blt_eq_decide, nat_beq_eq_decide,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hX, hY⟩, hP⟩, hQ⟩, hK⟩, heq⟩ := h
  have hvX := var_eq_atomCodes hcodes hX
  have hvY := var_eq_atomCodes hcodes hY
  set K := R.relK codes m N r
  have hgbox : ↑(Poly.toL m (R.prodAtoms m N (R.relPos r)) +
      Poly.toL m (R.prodAtoms m N (R.relNeg r))).support ⊆
        boxR m (fun i => (R.relLo codes m N r i : ℤ) - 32) (R.relRad codes m N r) := by
    classical
    refine (Finset.coe_subset.2 Finsupp.support_add).trans ?_
    rw [Finset.coe_union]
    exact Set.union_subset (support_toL_prodAtoms_subset_boxR hcodes hP)
      (support_toL_prodAtoms_subset_boxR hcodes hQ)
  have hbound : ((R.relBound codes m N r : ℕ) : ℤ) < 2 ^ K := by exact_mod_cast hK
  have hcf : ∀ e, 0 ≤ (Poly.toL m (R.var (R.relX r)) * Poly.toL m (R.var (R.relY r))) e ∧
      (Poly.toL m (R.var (R.relX r)) * Poly.toL m (R.var (R.relY r))) e < 2 ^ K := by
    rw [hvX, hvY]
    refine coeff_bounds_of_augment_lt (nonneg_mul (nonneg_toL_codes m _) (nonneg_toL_codes m _))
      (lt_of_le_of_lt ?_ hbound)
    rw [map_mul, augment_toL_codes, augment_toL_codes, relBound]
    exact_mod_cast le_max_left _ _
  have hcg := coeff_bounds_of_augment_lt (nonneg_add (nonneg_toL_prodAtoms hcodes (R.relPos r))
    (nonneg_toL_prodAtoms hcodes (R.relNeg r))) (lt_of_le_of_lt (by
      rw [map_add, augment_toL_prodAtoms hcodes, augment_toL_prodAtoms hcodes, relBound]
      exact_mod_cast le_max_right _ _) hbound)
  refine eq_of_evalW_eq (k := K) (support_toL_mul_subset_boxR hcodes hX hY) hgbox hcf hcg ?_
  change evalW m K (R.relW codes m N r) _ = evalW m K (R.relW codes m N r) _
  have hu : ((2 : ℚ) ^ K) ≠ 0 := by positivity
  rw [map_mul, map_add, hvX, hvY, evalW_toL_codes, evalW_toL_codes, evalW_toL_prodAtoms hcodes,
    evalW_toL_prodAtoms hcodes, weightHom_monoLo hP, weightHom_monoLo hQ, weightHom_relLo (R := R)]
  simp only [zpow_add₀ hu, zpow_natCast]
  have heq' := congrArg (fun n : ℕ => (n : ℚ)) heq
  simp only [nat_shiftLeft_eq', Nat.mul_eq, Nat.add_eq] at heq'
  push_cast at heq'
  rw [← pow_mul, ← pow_mul]
  linear_combination ((2 : ℚ) ^ K) ^ weightHom m (R.relW codes m N r)
      (fun i => (loDig (atomCodes codes m N (R.relX r)) i : ℤ) - 16) *
    ((2 : ℚ) ^ K) ^ weightHom m (R.relW codes m N r)
      (fun i => (loDig (atomCodes codes m N (R.relY r)) i : ℤ) - 16) * heq'

end Raw

end CertificateCheck

end ClusterAlgebras

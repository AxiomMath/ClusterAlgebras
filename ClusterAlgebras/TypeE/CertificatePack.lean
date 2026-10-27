/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.CertificateCheck

/-!
# Checking exchange relations through a univariate packing

The exchange relations `v_X v_Y = ∏ P + ∏ Q` of a certificate are identities in
`L_m = ℤ[X₁^{±1}, …, X_m^{±1}]`. Checking them term by term on exponent vectors is slow in the
kernel; this file checks them instead after the ring homomorphism
`Φ : L_m → ℤ[T^{±1}]`, `X^e ↦ T^{∑ eᵢ Bⁱ}` (`CertificateCheck.packRingHom`), on term lists
with natural-number keys and coefficients, so that every comparison and every addition is a
single GMP-backed `Nat` operation.

`Φ` is injective on Laurent polynomials whose exponents have entries of absolute value at most
`D` when `2D < B` (`CertificateCheck.packHom_injOn`); the check bounds the exponents of the
variables by `β` and the degrees of the monomials, so that both sides of every relation have
exponents in that box. Negative exponents are removed by multiplying each packed variable by a
power of `T` (`CertificateCheck.vshift`), and coefficients are required to be nonnegative, as
those of cluster variables are.

The main statement is `CertificateCheck.Raw.toL_relOKN`; the certificates of type `E` check
their relations by evaluation instead (`CertificateCheck.Raw.toL_relOKD`).
-/

@[expose] public section

namespace ClusterAlgebras

namespace CertificateCheck

/-! ### Univariate term lists with natural keys and coefficients -/

/-- A univariate polynomial `∑ c T^k` with natural-number keys `k` and coefficients `c`. -/
abbrev NPoly : Type := List (ℕ × ℕ)

namespace NPoly

/-- The interpretation of a term list in `ℤ[T^{±1}] = AddMonoidAlgebra ℤ ℤ`. -/
noncomputable def toZ (p : NPoly) : AddMonoidAlgebra ℤ ℤ :=
  (p.map fun t => AddMonoidAlgebra.single (t.1 : ℤ) (t.2 : ℤ)).sum

/-- The empty term list interprets as `0`. -/
@[simp] theorem toZ_nil : toZ [] = 0 := rfl

/-- The interpretation of `t :: p` is `t.2 T^{t.1} + toZ p`. -/
@[simp] theorem toZ_cons (t : ℕ × ℕ) (p : NPoly) :
    toZ (t :: p) = AddMonoidAlgebra.single (t.1 : ℤ) (t.2 : ℤ) + toZ p := by
  simp [toZ]

/-- Insertion of one term into a term list, combining equal keys. -/
def mergeAux (x : ℕ × ℕ) (xs : NPoly) (rec : NPoly → NPoly) : NPoly → NPoly
  | [] => x :: xs
  | y :: ys =>
    bif Nat.beq x.1 y.1 then (x.1, Nat.add x.2 y.2) :: rec ys
    else bif Nat.blt y.1 x.1 then x :: rec (y :: ys)
    else y :: mergeAux x xs rec ys

/-- The sum of two term lists, by merging. -/
def merge : NPoly → NPoly → NPoly
  | [], ys => ys
  | x :: xs, ys => mergeAux x xs (merge xs) ys

/-- If `rec zs` interprets as `toZ xs + toZ zs` for every `zs`, then `mergeAux x xs rec ys`
interprets as `toZ (x :: xs) + toZ ys`. -/
theorem toZ_mergeAux (x : ℕ × ℕ) (xs : NPoly) (rec : NPoly → NPoly)
    (hrec : ∀ zs, toZ (rec zs) = toZ xs + toZ zs) :
    ∀ ys, toZ (mergeAux x xs rec ys) = toZ (x :: xs) + toZ ys
  | [] => by simp [mergeAux]
  | y :: ys => by
    unfold mergeAux
    cases h1 : Nat.beq x.1 y.1
    · cases h2 : Nat.blt y.1 x.1
      · simp only [cond_false, toZ_cons, toZ_mergeAux x xs rec hrec ys]
        abel
      · simp only [cond_false, cond_true, toZ_cons, hrec]
        abel
    · have h := Nat.eq_of_beq_eq_true h1
      simp only [cond_true, toZ_cons, hrec, h, Nat.add_eq, Nat.cast_add,
        AddMonoidAlgebra.single_add]
      abel

/-- Merging two term lists interprets as the sum of their interpretations. -/
theorem toZ_merge : ∀ p q : NPoly, toZ (merge p q) = toZ p + toZ q
  | [], q => by simp [merge]
  | x :: xs, q => by
    rw [merge, toZ_mergeAux x xs (merge xs) (fun zs => toZ_merge xs zs)]

/-- Merging adjacent pairs of a list of term lists. -/
def mergePairs : List NPoly → List NPoly
  | p :: q :: rest => merge p q :: mergePairs rest
  | ls => ls

/-- Merging adjacent pairs preserves the sum of the interpretations. -/
theorem sum_map_toZ_mergePairs : ∀ ls : List NPoly,
    ((mergePairs ls).map toZ).sum = (ls.map toZ).sum
  | [] => rfl
  | [p] => rfl
  | p :: q :: rest => by
    rw [mergePairs, List.map_cons, List.sum_cons, toZ_merge, sum_map_toZ_mergePairs rest]
    simp [add_assoc]

/-- The sum of a list of term lists, by rounds of pairwise merges. -/
def mergeAll : ℕ → List NPoly → NPoly
  | _, [] => []
  | _, [p] => p
  | 0, p :: q :: rest => (p :: q :: rest).foldr merge []
  | f + 1, p :: q :: rest => mergeAll f (mergePairs (p :: q :: rest))

/-- Folding `merge` over a list of term lists interprets as the sum of their interpretations. -/
theorem toZ_foldr_merge (ls : List NPoly) : toZ (ls.foldr merge []) = (ls.map toZ).sum := by
  induction ls with
  | nil => rfl
  | cons p ls ih => rw [List.foldr_cons, toZ_merge, ih, List.map_cons, List.sum_cons]

/-- `mergeAll f ls` interprets as the sum of the interpretations of the term lists in `ls`. -/
theorem toZ_mergeAll : ∀ (f : ℕ) (ls : List NPoly), toZ (mergeAll f ls) = (ls.map toZ).sum
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | _, [p] => by simp [mergeAll]
  | 0, p :: q :: rest => by rw [mergeAll, toZ_foldr_merge]
  | f + 1, p :: q :: rest => by rw [mergeAll, toZ_mergeAll f, sum_map_toZ_mergePairs]

/-- A term list multiplied by one term. -/
def scale (t : ℕ × ℕ) (q : NPoly) : NPoly :=
  q.map fun s => (Nat.add t.1 s.1, Nat.mul t.2 s.2)

/-- Scaling by the term `t` interprets as multiplication by `t.2 T^{t.1}`. -/
theorem toZ_scale (t : ℕ × ℕ) (q : NPoly) :
    toZ (scale t q) = AddMonoidAlgebra.single (t.1 : ℤ) (t.2 : ℤ) * toZ q := by
  induction q with
  | nil => simp [scale]
  | cons s q ih =>
    simp only [scale, List.map_cons, toZ_cons] at ih ⊢
    rw [ih, mul_add, AddMonoidAlgebra.single_mul_single, Nat.add_eq, Nat.mul_eq, Nat.cast_add,
      Nat.cast_mul]

/-- The product of two term lists. -/
def mul (p q : NPoly) : NPoly :=
  mergeAll 16 (p.map fun t => scale t q)

/-- The product of two term lists interprets as the product of their interpretations. -/
theorem toZ_mul (p q : NPoly) : toZ (mul p q) = toZ p * toZ q := by
  rw [mul, toZ_mergeAll, List.map_map]
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [List.map_cons, List.sum_cons, Function.comp_apply, toZ_scale, ih, toZ_cons, add_mul]

/-- The term list of `1`. -/
def one : NPoly := [(0, 1)]

/-- The term list `one` interprets as `1`. -/
theorem toZ_one : toZ one = 1 := by
  simp [one]

/-- A power of a term list. -/
def pow (p : NPoly) : ℕ → NPoly
  | 0 => one
  | k + 1 => mul (pow p k) p

/-- `pow p k` interprets as the `k`-th power of `toZ p`. -/
theorem toZ_pow (p : NPoly) : ∀ k, toZ (pow p k) = toZ p ^ k
  | 0 => by rw [pow, toZ_one, pow_zero]
  | k + 1 => by rw [pow, toZ_mul, toZ_pow p k, pow_succ]

/-- Multiplication by `T^d`. -/
def shift (d : ℕ) (p : NPoly) : NPoly :=
  p.map fun t => (Nat.add t.1 d, t.2)

/-- `shift d p` interprets as `T^d * toZ p`. -/
theorem toZ_shift (d : ℕ) (p : NPoly) :
    toZ (shift d p) = AddMonoidAlgebra.single (d : ℤ) 1 * toZ p := by
  induction p with
  | nil => simp [shift]
  | cons t p ih =>
    simp only [shift, List.map_cons, toZ_cons] at ih ⊢
    rw [ih, mul_add, AddMonoidAlgebra.single_mul_single, one_mul, Nat.add_eq, Nat.cast_add,
      add_comm (d : ℤ)]

end NPoly

/-! ### The packing homomorphism -/

/-- `∑ᵢ eᵢ Bⁱ` for an exponent list. -/
def packExp (m B : ℕ) (e : List ℤ) : ℤ :=
  ((List.range m).map fun i => e.getD i 0 * (B : ℤ) ^ i).sum

/-- The packing `e ↦ ∑ᵢ eᵢ Bⁱ` of exponent vectors. -/
def packHom (m B : ℕ) : (Fin m → ℤ) →+ ℤ where
  toFun e := ∑ i, e i * (B : ℤ) ^ (i : ℕ)
  map_zero' := by simp
  map_add' e e' := by simp [add_mul, Finset.sum_add_distrib]

/-- A sum over `Finset.range m` is the sum of the list `(List.range m).map f`. -/
theorem finset_sum_range_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range m, f i = ((List.range m).map f).sum := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Finset.sum_range_succ, List.sum_range_succ, ih]

/-- The packing of `expFun m e` is `packExp m B e`. -/
theorem packHom_expFun (m B : ℕ) (e : List ℤ) : packHom m B (expFun m e) = packExp m B e := by
  change ∑ i : Fin m, e.getD i 0 * (B : ℤ) ^ (i : ℕ) = _
  rw [Fin.sum_univ_eq_sum_range (fun i => e.getD i 0 * (B : ℤ) ^ i), finset_sum_range_eq]
  rfl

/-- The box of exponent vectors with entries of absolute value at most `D`. -/
def box (m D : ℕ) : Set (Fin m → ℤ) :=
  {e | ∀ i, |e i| ≤ D}

/-- If `2D < B`, two exponent vectors with entries of absolute value at most `D` and equal sums
`∑ eᵢ Bⁱ` are equal. -/
theorem sum_mul_pow_inj {B D : ℕ} (hB : 2 * D < B) :
    ∀ (m : ℕ) (e e' : Fin m → ℤ), (∀ i, |e i| ≤ D) → (∀ i, |e' i| ≤ D) →
      ∑ i, e i * (B : ℤ) ^ (i : ℕ) = ∑ i, e' i * (B : ℤ) ^ (i : ℕ) → e = e'
  | 0, e, e', _, _, _ => funext fun i => i.elim0
  | m + 1, e, e', he, he', h => by
    have hfac : ∀ f : Fin (m + 1) → ℤ,
        ∑ i : Fin m, f i.succ * (B : ℤ) ^ ((i.succ : Fin (m + 1)) : ℕ)
        = B * ∑ i : Fin m, f i.succ * (B : ℤ) ^ (i : ℕ) := fun f => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_succ, pow_succ]
      ring
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hfac, hfac] at h
    simp only [Fin.val_zero, pow_zero, mul_one] at h
    have hB0 : (B : ℤ) ≠ 0 := by
      have : 0 < B := by omega
      exact_mod_cast this.ne'
    have h0 : e 0 = e' 0 := by
      have hd : (B : ℤ) ∣ e 0 - e' 0 :=
        ⟨∑ i : Fin m, e' i.succ * (B : ℤ) ^ (i : ℕ) - ∑ i : Fin m, e i.succ * (B : ℤ) ^ (i : ℕ),
          by linear_combination h⟩
      have hlt : |e 0 - e' 0| < B := by
        have := abs_sub (e 0) (e' 0)
        have h1 := he 0
        have h2 := he' 0
        have : (2 * D : ℤ) < B := by exact_mod_cast hB
        linarith
      linarith [Int.eq_zero_of_abs_lt_dvd hd hlt]
    have htail := sum_mul_pow_inj hB m (fun i => e i.succ) (fun i => e' i.succ)
      (fun i => he _) (fun i => he' _) (mul_left_cancel₀ hB0 (by linarith))
    funext i
    cases i using Fin.cases with
    | zero => exact h0
    | succ i => exact congrFun htail i

/-- If `2D < B`, the packing `packHom m B` is injective on the box `box m D`. -/
theorem packHom_injOn {m B D : ℕ} (hB : 2 * D < B) : Set.InjOn (packHom m B) (box m D) :=
  fun e he e' he' h => sum_mul_pow_inj hB m e e' he he' h

/-- The ring homomorphism `Φ : L_m → ℤ[T^{±1}]`, `X^e ↦ T^{∑ eᵢ Bⁱ}`. -/
noncomputable def packRingHom (m B : ℕ) : LaurentRing m →+* AddMonoidAlgebra ℤ ℤ :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (packHom m B)

/-- `packRingHom m B` sends the monomial `c X^a` to `c T^{packHom m B a}`. -/
theorem packRingHom_single (m B : ℕ) (a : Fin m → ℤ) (c : ℤ) :
    packRingHom m B (AddMonoidAlgebra.single a c) =
      AddMonoidAlgebra.single (packHom m B a) c := by
  simp [packRingHom]

/-- Packing a term list, multiplied by `T^s`. -/
def npack (m B s : ℕ) (p : Poly) : NPoly :=
  p.map fun t => ((packExp m B t.1 + s).toNat, t.2.toNat)

/-- If every term of `p` has nonnegative shifted packed exponent and nonnegative coefficient, then
`npack m B s p` interprets as `T^s * packRingHom m B (Poly.toL m p)`. -/
theorem toZ_npack {m B s : ℕ} {p : Poly} (hp : ∀ t ∈ p, 0 ≤ packExp m B t.1 + s ∧ 0 ≤ t.2) :
    NPoly.toZ (npack m B s p) =
      AddMonoidAlgebra.single (s : ℤ) 1 * packRingHom m B (Poly.toL m p) := by
  induction p with
  | nil => simp [npack]
  | cons t p ih =>
    have ht := hp t (List.mem_cons_self ..)
    simp only [npack, List.map_cons, NPoly.toZ_cons] at ih ⊢
    rw [ih fun t' ht' => hp t' (List.mem_cons_of_mem _ ht'), Poly.toL_cons, map_add, mul_add,
      packRingHom_single, AddMonoidAlgebra.single_mul_single, one_mul, packHom_expFun,
      Int.toNat_of_nonneg ht.1, Int.toNat_of_nonneg ht.2, add_comm (s : ℤ)]

/-- A shift making every packed exponent of a term list nonnegative. -/
def vshift (m B : ℕ) (p : Poly) : ℕ :=
  (p.map fun t => (-packExp m B t.1).toNat).foldr max 0

/-- Shifting by `vshift m B p` makes the packed exponent of every term of `p` nonnegative. -/
theorem le_vshift {m B : ℕ} {p : Poly} {t : List ℤ × ℤ} (ht : t ∈ p) :
    0 ≤ packExp m B t.1 + vshift m B p := by
  have key : ∀ q : Poly, t ∈ q → (-packExp m B t.1).toNat ≤ vshift m B q := by
    intro q hq
    induction q with
    | nil => cases hq
    | cons s q ih =>
      simp only [vshift, List.map_cons, List.foldr_cons] at ih ⊢
      rcases List.mem_cons.1 hq with rfl | hq
      · exact le_max_left _ _
      · exact (ih hq).trans (le_max_right _ _)
  have := key p ht
  have h2 := Int.self_le_toNat (-packExp m B t.1)
  omega

/-! ### Supports in boxes -/

/-- `box m a` is monotone in the radius `a`. -/
theorem box_mono {m a b : ℕ} (h : a ≤ b) : box m a ⊆ box m b :=
  fun _ he i => (he i).trans (by exact_mod_cast h)

/-- The sum of vectors in `box m a` and `box m b` lies in `box m (a + b)`. -/
theorem add_mem_box {m a b : ℕ} {e e' : Fin m → ℤ} (he : e ∈ box m a) (he' : e' ∈ box m b) :
    e + e' ∈ box m (a + b) := fun i => by
  have := abs_add_le (e i) (e' i)
  have h1 := he i
  have h2 := he' i
  simp only [Pi.add_apply, Nat.cast_add]
  linarith

/-- If the supports of `f` and `g` lie in `box m a` and `box m b`, the support of `f * g` lies in
`box m (a + b)`. -/
theorem support_mul_subset_box {m a b : ℕ} {f g : LaurentRing m} (hf : ↑f.support ⊆ box m a)
    (hg : ↑g.support ⊆ box m b) : ↑(f * g).support ⊆ box m (a + b) := by
  classical
  intro e he
  have := AddMonoidAlgebra.support_mul f g (Finset.mem_coe.1 he)
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 this
  exact add_mem_box (hf hx) (hg hy)

/-- The support of `1` lies in every box. -/
theorem support_one_subset_box (m a : ℕ) : ↑(1 : LaurentRing m).support ⊆ box m a := by
  intro e he
  have : e = 0 := by
    classical
    have h := Finsupp.support_single_subset (Finset.mem_coe.1 he)
    simpa using h
  subst this
  intro i
  simp

/-- If the support of `f` lies in `box m a`, the support of `f ^ k` lies in `box m (a * k)`. -/
theorem support_pow_subset_box {m a : ℕ} {f : LaurentRing m} (hf : ↑f.support ⊆ box m a) :
    ∀ k : ℕ, ↑(f ^ k).support ⊆ box m (a * k)
  | 0 => by simpa using support_one_subset_box m 0
  | k + 1 => by
    rw [pow_succ, Nat.mul_succ]
    exact support_mul_subset_box (support_pow_subset_box hf k) hf

/-- If every exponent of the term list `p` has its first `m` entries of absolute value at most `β`,
the support of `Poly.toL m p` lies in `box m β`. -/
theorem support_toL_subset_box {m β : ℕ} {p : Poly}
    (hp : ∀ t ∈ p, ∀ i < m, |t.1.getD i 0| ≤ β) : ↑(Poly.toL m p).support ⊆ box m β := by
  classical
  induction p with
  | nil => intro e he; exact absurd rfl (Finset.mem_coe.1 he |> Finsupp.mem_support_iff.1)
  | cons t p ih =>
    rw [Poly.toL_cons]
    refine (Finset.coe_subset.2 Finsupp.support_add).trans ?_
    rw [Finset.coe_union]
    refine Set.union_subset ?_ (ih fun t' ht' => hp t' (List.mem_cons_of_mem _ ht'))
    intro e he
    have := Finsupp.support_single_subset (Finset.mem_coe.1 he)
    rw [Finset.mem_singleton] at this
    subst this
    exact fun i => hp t (List.mem_cons_self ..) i i.2

/-! ### The relation check -/

/-- `Nat.ble a b` is the decision of `a ≤ b`. -/
theorem nat_ble_eq_decide (a b : ℕ) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.2 (by simp [Nat.ble_eq])

namespace Raw

variable (R : Raw)

/-- The packing shift of an atom. -/
def atomShift (m N B c : ℕ) : ℕ :=
  vshift m B (R.atom m N c)

/-- The packed atom. -/
def atomN (m N B c : ℕ) : NPoly :=
  npack m B (R.atomShift m N B c) (R.atom m N c)

/-- The packed product of the powers of the atoms of a list. -/
def nprodAtoms (m N B : ℕ) : List (ℕ × ℕ) → NPoly
  | [] => NPoly.one
  | t :: l => NPoly.mul (NPoly.pow (R.atomN m N B t.1) t.2) (nprodAtoms m N B l)

/-- The packing shift of the product of the powers of the atoms of a list. -/
def nshAtoms (m N B : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | t :: l => R.atomShift m N B t.1 * t.2 + nshAtoms m N B l

/-- The variable `c` has nonnegative coefficients and exponents of absolute value at most
`β`. -/
def varOK (m β c : ℕ) : Bool :=
  (R.var c).all fun t => decide (0 ≤ t.2) && allBelow m fun i => decide (|t.1.getD i 0| ≤ β)

/-- The relation `r` holds, checked through the packing with base `B` and box `D`. -/
def relOKN (m N B β D r : ℕ) : Bool :=
  Nat.blt (R.relX r) N && Nat.blt (R.relY r) N && Nat.blt (2 * D) B && Nat.ble 1 β &&
    Nat.ble (2 * β) D && Nat.ble (β * degAtoms (R.relPos r)) D &&
    Nat.ble (β * degAtoms (R.relNeg r)) D &&
    decide (NPoly.shift
        (max (R.atomShift m N B (R.relX r) + R.atomShift m N B (R.relY r))
          (max (R.nshAtoms m N B (R.relPos r)) (R.nshAtoms m N B (R.relNeg r))) -
          (R.atomShift m N B (R.relX r) + R.atomShift m N B (R.relY r)))
        (NPoly.mul (R.atomN m N B (R.relX r)) (R.atomN m N B (R.relY r))) =
      NPoly.merge
        (NPoly.shift
          (max (R.atomShift m N B (R.relX r) + R.atomShift m N B (R.relY r))
            (max (R.nshAtoms m N B (R.relPos r)) (R.nshAtoms m N B (R.relNeg r))) -
            R.nshAtoms m N B (R.relPos r))
          (R.nprodAtoms m N B (R.relPos r)))
        (NPoly.shift
          (max (R.atomShift m N B (R.relX r) + R.atomShift m N B (R.relY r))
            (max (R.nshAtoms m N B (R.relPos r)) (R.nshAtoms m N B (R.relNeg r))) -
            R.nshAtoms m N B (R.relNeg r))
          (R.nprodAtoms m N B (R.relNeg r))))

variable {R}

/-- If `1 ≤ β` and every variable below `N` satisfies `varOK m β`, every term of `R.atom m N c` has
nonnegative coefficient and exponent entries of absolute value at most `β`. -/
theorem atom_terms {m N β c : ℕ} (hβ : 1 ≤ β) (hvar : ∀ c < N, R.varOK m β c = true) :
    ∀ t ∈ R.atom m N c, 0 ≤ t.2 ∧ ∀ i < m, |t.1.getD i 0| ≤ β := by
  intro t ht
  simp only [atom, nat_blt_eq_decide, Bool.cond_decide] at ht
  split_ifs at ht with hc
  · have := List.all_eq_true.1 (hvar c hc) t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, allBelow_iff] at this
    exact this
  · simp only [unitPoly, List.mem_singleton] at ht
    subst ht
    refine ⟨zero_le_one, fun i hi => ?_⟩
    simp only [unitExp, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    split_ifs <;> simp [hβ]

/-- The packed atom `R.atomN m N B c` interprets as
`T^s * packRingHom m B (Poly.toL m (R.atom m N c))`, where `s = R.atomShift m N B c`. -/
theorem toZ_atomN {m N B β c : ℕ} (hβ : 1 ≤ β) (hvar : ∀ c < N, R.varOK m β c = true) :
    NPoly.toZ (R.atomN m N B c) = AddMonoidAlgebra.single (R.atomShift m N B c : ℤ) 1 *
      packRingHom m B (Poly.toL m (R.atom m N c)) :=
  toZ_npack fun t ht => ⟨le_vshift ht, (atom_terms hβ hvar t ht).1⟩

/-- `R.nprodAtoms m N B l` interprets as `T^s * packRingHom m B (Poly.toL m (R.prodAtoms m N l))`,
where `s = R.nshAtoms m N B l`. -/
theorem toZ_nprodAtoms {m N B β : ℕ} (hβ : 1 ≤ β) (hvar : ∀ c < N, R.varOK m β c = true) :
    ∀ l : List (ℕ × ℕ), NPoly.toZ (R.nprodAtoms m N B l) =
      AddMonoidAlgebra.single (R.nshAtoms m N B l : ℤ) 1 *
        packRingHom m B (Poly.toL m (R.prodAtoms m N l))
  | [] => by
    rw [nprodAtoms, nshAtoms, NPoly.toZ_one, prodAtoms, List.foldl_nil, Poly.toL_one, map_one,
      mul_one]
    rfl
  | t :: l => by
    rw [nprodAtoms, NPoly.toZ_mul, NPoly.toZ_pow, toZ_nprodAtoms hβ hvar l, toZ_atomN hβ hvar,
      nshAtoms, toL_prodAtoms, toL_prodAtoms, List.map_cons, List.prod_cons, map_mul, map_pow,
      mul_pow, AddMonoidAlgebra.single_pow, one_pow]
    rw [show (R.atomShift m N B t.1 * t.2 + R.nshAtoms m N B l : ℕ) =
      (R.atomShift m N B t.1 * t.2 : ℕ) + R.nshAtoms m N B l from rfl, Nat.cast_add,
      ← one_mul (1 : ℤ), ← AddMonoidAlgebra.single_mul_single, nsmul_eq_mul, Nat.cast_mul]
    ring_nf

/-- The support of `Poly.toL m (R.prodAtoms m N l)` lies in `box m (β * degAtoms l)`. -/
theorem support_prodAtoms_subset_box {m N β : ℕ} (hβ : 1 ≤ β)
    (hvar : ∀ c < N, R.varOK m β c = true) (l : List (ℕ × ℕ)) :
    ↑(Poly.toL m (R.prodAtoms m N l)).support ⊆ box m (β * degAtoms l) := by
  rw [toL_prodAtoms]
  induction l with
  | nil => simpa [degAtoms] using support_one_subset_box m 0
  | cons t l ih =>
    rw [List.map_cons, List.prod_cons, degAtoms, List.map_cons, List.sum_cons, mul_add]
    exact support_mul_subset_box (support_pow_subset_box
      (support_toL_subset_box fun t' ht' => (atom_terms hβ hvar t' ht').2) _) ih

/-- Multiplication by the monomial `T^S` is cancellable in `ℤ[T^{±1}]`. -/
theorem single_cancel {S : ℤ} {f g : AddMonoidAlgebra ℤ ℤ}
    (h : AddMonoidAlgebra.single S 1 * f = AddMonoidAlgebra.single S 1 * g) : f = g := by
  have hu : AddMonoidAlgebra.single (-S) (1 : ℤ) * AddMonoidAlgebra.single S 1 = 1 := by
    rw [AddMonoidAlgebra.single_mul_single, neg_add_cancel, one_mul]
    rfl
  calc f = (AddMonoidAlgebra.single (-S) 1 * AddMonoidAlgebra.single S 1) * f := by
        rw [hu, one_mul]
    _ = (AddMonoidAlgebra.single (-S) 1 * AddMonoidAlgebra.single S 1) * g := by
        rw [mul_assoc, h, ← mul_assoc]
    _ = g := by rw [hu, one_mul]

/-- **Soundness of the packed relation check.** If every variable below `N` satisfies
`R.varOK m β` and `R.relOKN m N B β D r` holds, then the exchange relation `r` holds in `L_m`. -/
theorem toL_relOKN {m N B β D r : ℕ} (hvar : ∀ c < N, R.varOK m β c = true)
    (h : R.relOKN m N B β D r = true) :
    Poly.toL m (R.var (R.relX r)) * Poly.toL m (R.var (R.relY r)) =
      Poly.toL m (R.prodAtoms m N (R.relPos r)) + Poly.toL m (R.prodAtoms m N (R.relNeg r)) := by
  simp only [relOKN, Bool.and_eq_true, nat_blt_eq_decide, nat_ble_eq_decide,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hX, hY⟩, hB⟩, hβ⟩, h2β⟩, hP⟩, hQ⟩, heq⟩ := h
  have hatX : R.atom m N (R.relX r) = R.var (R.relX r) := by
    simp [atom, nat_blt_eq_decide, hX]
  have hatY : R.atom m N (R.relY r) = R.var (R.relY r) := by
    simp [atom, nat_blt_eq_decide, hY]
  set SX := R.atomShift m N B (R.relX r) + R.atomShift m N B (R.relY r)
  set SP := R.nshAtoms m N B (R.relPos r)
  set SQ := R.nshAtoms m N B (R.relNeg r)
  set S := max SX (max SP SQ)
  have hz := congrArg NPoly.toZ heq
  rw [NPoly.toZ_shift, NPoly.toZ_merge, NPoly.toZ_shift, NPoly.toZ_shift, NPoly.toZ_mul,
    toZ_atomN hβ hvar, toZ_atomN hβ hvar, toZ_nprodAtoms hβ hvar, toZ_nprodAtoms hβ hvar,
    hatX, hatY] at hz
  have hS : ∀ T : ℕ, T ≤ S → AddMonoidAlgebra.single ((S - T : ℕ) : ℤ) (1 : ℤ) *
      AddMonoidAlgebra.single (T : ℤ) 1 = AddMonoidAlgebra.single (S : ℤ) 1 := fun T hT => by
    rw [AddMonoidAlgebra.single_mul_single, one_mul, ← Nat.cast_add, Nat.sub_add_cancel hT]
  have hX' : SX ≤ S := le_max_left _ _
  have hP' : SP ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have hQ' : SQ ≤ S := (le_max_right _ _).trans (le_max_right _ _)
  have hsplit : ∀ a b : ℕ, AddMonoidAlgebra.single ((a + b : ℕ) : ℤ) (1 : ℤ) =
      AddMonoidAlgebra.single (a : ℤ) 1 * AddMonoidAlgebra.single (b : ℤ) 1 := fun a b => by
    rw [AddMonoidAlgebra.single_mul_single, one_mul, Nat.cast_add]
  have e1 : AddMonoidAlgebra.single ((S - SX : ℕ) : ℤ) (1 : ℤ) *
      (AddMonoidAlgebra.single (R.atomShift m N B (R.relX r) : ℤ) 1 *
          packRingHom m B (Poly.toL m (R.var (R.relX r))) *
        (AddMonoidAlgebra.single (R.atomShift m N B (R.relY r) : ℤ) 1 *
          packRingHom m B (Poly.toL m (R.var (R.relY r))))) =
      AddMonoidAlgebra.single (S : ℤ) 1 * packRingHom m B
        (Poly.toL m (R.var (R.relX r)) * Poly.toL m (R.var (R.relY r))) := by
    rw [← hS SX hX', hsplit, map_mul]
    ring
  have e2 : ∀ T : ℕ, T ≤ S → ∀ f : AddMonoidAlgebra ℤ ℤ,
      AddMonoidAlgebra.single ((S - T : ℕ) : ℤ) (1 : ℤ) * (AddMonoidAlgebra.single (T : ℤ) 1 * f) =
        AddMonoidAlgebra.single (S : ℤ) 1 * f := fun T hT f => by
    rw [← mul_assoc, hS T hT]
  rw [e1, e2 SP hP', e2 SQ hQ'] at hz
  have hz' : AddMonoidAlgebra.single (S : ℤ) 1 *
      packRingHom m B (Poly.toL m (R.var (R.relX r)) * Poly.toL m (R.var (R.relY r))) =
    AddMonoidAlgebra.single (S : ℤ) 1 * packRingHom m B
      (Poly.toL m (R.prodAtoms m N (R.relPos r)) + Poly.toL m (R.prodAtoms m N (R.relNeg r))) := by
    rw [hz, map_add, mul_add]
  have hΦ := single_cancel hz'
  have hbox : ∀ f : LaurentRing m, ↑f.support ⊆ box m D →
      f ∈ {w : (Fin m → ℤ) →₀ ℤ | ↑w.support ⊆ box m D} := fun f hf => hf
  refine Finsupp.mapDomain_injOn (box m D) (packHom_injOn hB) (hbox _ ?_) (hbox _ ?_) hΦ
  · refine (support_mul_subset_box (a := β) (b := β) (support_toL_subset_box fun t ht => ?_)
      (support_toL_subset_box fun t ht => ?_)).trans (box_mono (by omega))
    · exact (atom_terms hβ hvar t (hatX ▸ ht)).2
    · exact (atom_terms hβ hvar t (hatY ▸ ht)).2
  · classical
    refine (Finset.coe_subset.2 Finsupp.support_add).trans ?_
    rw [Finset.coe_union]
    exact Set.union_subset
      ((support_prodAtoms_subset_box hβ hvar _).trans (box_mono hP))
      ((support_prodAtoms_subset_box hβ hvar _).trans (box_mono hQ))

end Raw

end CertificateCheck

end ClusterAlgebras

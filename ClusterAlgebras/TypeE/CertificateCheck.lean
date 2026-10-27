/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.Certificate
public import ClusterAlgebras.TypeE.CertificateCore

/-!
# A kernel-checkable checker for exchange certificates

For the types `E₆`, `E₇`, `E₈`, `F₄` and `G₂`, the existence of exchange certificates is a
computational statement. This file reduces the existence of an exchange certificate to
finitely many Boolean checks on explicit, compactly encoded data, each of which is evaluated by
the Lean kernel (`decide +kernel`). No `native_decide` is used anywhere.

## Polynomials

Integer Laurent polynomials are represented as lists of terms `(e, c)`, `e : List ℤ` an exponent
vector read with `List.getD` (so missing entries are `0`), `c : ℤ` a coefficient. The
interpretation `CertificateCheck.Poly.toL m p` in `LaurentRing m` is the sum of the monomials
`c X^e`. Addition is a merge of term lists and multiplication a balanced merge of scaled copies;
both are shown to commute with `toL` for *all* lists, so no invariant of the representation is
ever needed for the identities (T3). Distinctness of variables (D1) is shown by exhibiting, for
each pair, an exponent at which the coefficients differ (`Poly.coeffAt`).

## Seeds and transitions

The data of a certificate are given by functions of natural numbers (`CertificateCheck.Raw`):
variable `c`, entry `i` of the cluster of seed `a`, digit `(i, j)` of the matrix of seed `a`, the
transitions `(ν(a, k), π_{a,k})`, an index into a table of verified exchange relations, and a
spanning tree of the transition graph. Matrix entries are stored as digits with a bias.

A transition `(a, k)` leading to an earlier seed is checked as the reverse of the transition
`(ν(a, k), π_{a,k}(k))`, mutation being an involution (`CertificateCheck.Raw.revOK`); the others
are checked in full (`CertificateCheck.Raw.fwdOK`). There, the mutation rule (T1) is checked on
matrices packed into single natural numbers, the outer product of column and row `k` being one
multiplication (`CertificateCheck.Raw.mutPackOK`), and the exchange monomials of (T3) are compared
with those of the relation through the numbers `∑ e · 16^c` (`CertificateCheck.atomKey`). All of
these are GMP-backed `Nat` operations in the kernel.

The main statement is `CertificateCheck.Raw.nonempty_exchangeCertificate`.
-/

@[expose] public section

namespace ClusterAlgebras

namespace CertificateCheck

/-! ### Bounded checks -/

/-- `anyBelow n p`: some `i < n` has `p i`. -/
def anyBelow (n : ℕ) (p : ℕ → Bool) : Bool :=
  !allBelow n fun i => !p i

/-- `anyBelow n p` holds if and only if `p i` holds for some `i < n`. -/
theorem anyBelow_iff {n : ℕ} {p : ℕ → Bool} : anyBelow n p = true ↔ ∃ i < n, p i = true := by
  rw [anyBelow, Bool.not_eq_true', ← Bool.not_eq_true, allBelow_iff]
  push Not
  simp

/-- `sumBelow n f` is the sum of `f i` over `i < n`. -/
theorem sumBelow_eq (n : ℕ) (f : ℕ → ℕ) : sumBelow n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact Nat.add_comm _ _

/-! ### Keys of monomials -/

/-- The key `∑ e · 16^c` of a list of atoms `c` with exponents `e`. -/
def atomKey (l : List (ℕ × ℕ)) : ℕ :=
  l.foldr (fun t acc => Nat.add (Nat.mul t.2 (Nat.pow 16 t.1)) acc) 0

/-- The key of `t :: l` is `16^c e` plus the key of `l`, where `t = (c, e)`. -/
theorem atomKey_cons (t : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    atomKey (t :: l) = 16 ^ t.1 * t.2 + atomKey l := by
  simp only [atomKey, List.foldr_cons, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, mul_comm]

/-- The key of a concatenation is the sum of the keys. -/
theorem atomKey_append (l l' : List (ℕ × ℕ)) : atomKey (l ++ l') = atomKey l + atomKey l' := by
  induction l with
  | nil => simp [atomKey]
  | cons t l ih => rw [List.cons_append, atomKey_cons, atomKey_cons, ih, Nat.add_assoc]

/-- The key of the atoms `F i`, `i < m`, is the sum over `i < m` of `16^c e` for `F i = (c, e)`,
missing atoms contributing `0`. -/
theorem atomKey_filterMap_range (F : ℕ → Option (ℕ × ℕ)) : ∀ m : ℕ,
    atomKey ((List.range m).filterMap F) = sumBelow m fun i => (F i).elim 0 fun t => 16 ^ t.1 * t.2
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.filterMap_append, atomKey_append, sumBelow_succ,
      atomKey_filterMap_range F m, Nat.add_comm]
    congr 1
    cases h : F m <;> simp [atomKey, h, mul_comm]

/-- A list of atoms whose atoms increase strictly and whose exponents lie in `[1, 15]`; such a
list is determined by its key (`CertificateCheck.atomKey_injOn`). -/
def AtomsGood (l : List (ℕ × ℕ)) : Prop :=
  l.Pairwise (fun s t => s.1 < t.1) ∧ ∀ t ∈ l, 1 ≤ t.2 ∧ t.2 < 16

/-- The check of `CertificateCheck.AtomsGood`. -/
def atomsOK : List (ℕ × ℕ) → Bool
  | [] => true
  | [t] => Nat.ble 1 t.2 && Nat.blt t.2 16
  | t :: s :: l => Nat.ble 1 t.2 && Nat.blt t.2 16 && Nat.blt t.1 s.1 && atomsOK (s :: l)

/-- A list of atoms passing `atomsOK` is good. -/
theorem atomsGood_of_atomsOK : ∀ {l : List (ℕ × ℕ)}, atomsOK l = true → AtomsGood l
  | [], _ => ⟨List.Pairwise.nil, by simp⟩
  | [t], h => by
    simp only [atomsOK, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    exact ⟨List.pairwise_singleton _ _, by simpa using h⟩
  | t :: s :: l, h => by
    simp only [atomsOK, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨hp, hb⟩ := atomsGood_of_atomsOK h4
    refine ⟨List.Pairwise.cons (fun u hu => ?_) hp, fun u hu => ?_⟩
    · rcases List.mem_cons.1 hu with rfl | hu
      · exact h3
      · exact h3.trans (List.rel_of_pairwise_cons hp hu)
    · rcases List.mem_cons.1 hu with rfl | hu
      · exact ⟨h1, h2⟩
      · exact hb u hu

/-- If every atom of `l` is at least `c`, then `16^c` divides the key of `l`. -/
theorem pow_dvd_atomKey {c : ℕ} : ∀ {l : List (ℕ × ℕ)}, (∀ t ∈ l, c ≤ t.1) → 16 ^ c ∣ atomKey l
  | [], _ => dvd_zero _
  | t :: l, h => by
    rw [atomKey_cons]
    exact dvd_add (dvd_mul_of_dvd_left (pow_dvd_pow 16 (h t (List.mem_cons_self ..))) _)
      (pow_dvd_atomKey fun u hu => h u (List.mem_cons_of_mem _ hu))

/-- The key of a good list `t :: l` is `16^c (e + 16 u)` for some `u`, where `t = (c, e)`. -/
theorem exists_atomKey_eq_of_atomsGood {t : ℕ × ℕ} {l : List (ℕ × ℕ)} (h : AtomsGood (t :: l)) :
    ∃ u, atomKey (t :: l) = 16 ^ t.1 * (t.2 + 16 * u) := by
  obtain ⟨u, hu⟩ := pow_dvd_atomKey (c := t.1 + 1) (l := l) fun s hs =>
    List.rel_of_pairwise_cons h.1 hs
  exact ⟨u, by rw [atomKey_cons, hu, pow_succ]; ring⟩

/-- The key of a good nonempty list of atoms is positive. -/
theorem atomKey_pos_of_atomsGood {t : ℕ × ℕ} {l : List (ℕ × ℕ)} (h : AtomsGood (t :: l)) :
    0 < atomKey (t :: l) := by
  obtain ⟨u, hu⟩ := exists_atomKey_eq_of_atomsGood h
  have := (h.2 t (List.mem_cons_self ..)).1
  rw [hu]
  exact Nat.mul_pos (by positivity) (by omega)

/-- If two good lists of atoms have the same key, the first atom of the first is not below the
first atom of the second. -/
theorem not_lt_fst_of_atomKey_eq {t t' : ℕ × ℕ} {l l' : List (ℕ × ℕ)}
    (h : AtomsGood (t :: l)) (h' : AtomsGood (t' :: l'))
    (hk : atomKey (t :: l) = atomKey (t' :: l')) : ¬t.1 < t'.1 := by
  intro hlt
  obtain ⟨u, hu⟩ := exists_atomKey_eq_of_atomsGood h
  have he := h.2 t (List.mem_cons_self ..)
  obtain ⟨w, hw⟩ : 16 ^ t.1 * 16 ∣ atomKey (t' :: l') := by
    rw [← pow_succ]
    exact pow_dvd_atomKey fun s hs => by
      rcases List.mem_cons.1 hs with rfl | hs
      · exact hlt
      · exact hlt.trans (List.rel_of_pairwise_cons h'.1 hs)
  rw [← hk, hu, mul_assoc] at hw
  have := Nat.eq_of_mul_eq_mul_left (by positivity) hw
  omega

/-- Two good lists of atoms with the same key are equal. -/
theorem atomKey_injOn : ∀ {l l' : List (ℕ × ℕ)}, AtomsGood l → AtomsGood l' →
    atomKey l = atomKey l' → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h', hk => ((atomKey_pos_of_atomsGood h').ne hk).elim
  | _ :: _, [], h, _, hk => ((atomKey_pos_of_atomsGood h).ne' hk).elim
  | t :: l, t' :: l', h, h', hk => by
    obtain ⟨u, hu⟩ := exists_atomKey_eq_of_atomsGood h
    obtain ⟨u', hu'⟩ := exists_atomKey_eq_of_atomsGood h'
    have he := h.2 t (List.mem_cons_self ..)
    have he' := h'.2 t' (List.mem_cons_self ..)
    have hc : t.1 = t'.1 := le_antisymm (not_lt.1 (not_lt_fst_of_atomKey_eq h' h hk.symm))
      (not_lt.1 (not_lt_fst_of_atomKey_eq h h' hk))
    rw [hu, hu', hc] at hk
    have hk' := Nat.eq_of_mul_eq_mul_left (by positivity) hk
    have h2 : t.2 = t'.2 := by omega
    have htail : atomKey l = atomKey l' := by
      have e1 := atomKey_cons t l
      have e2 := atomKey_cons t' l'
      rw [hu] at e1
      rw [hu', ← hc] at e2
      have : u = u' := by omega
      rw [mul_add] at e1 e2
      rw [(Nat.add_left_cancel e1).symm, (Nat.add_left_cancel e2).symm, this]
    rw [atomKey_injOn ⟨h.1.of_cons, fun s hs => h.2 s (List.mem_cons_of_mem _ hs)⟩
      ⟨h'.1.of_cons, fun s hs => h'.2 s (List.mem_cons_of_mem _ hs)⟩ htail]
    exact congrArg (· :: l') (Prod.ext hc h2)

/-! ### Laurent polynomials as term lists -/

/-- The exponent vector `Fin m → ℤ` of a list of integers, missing entries being `0`. -/
def expFun (m : ℕ) (e : List ℤ) : Fin m → ℤ := fun i => e.getD i 0

/-- Pointwise sum of exponent lists, the shorter one being padded with zeros. -/
def addE : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addE as bs

/-- Each entry of `addE a b` is the sum of the corresponding entries of `a` and `b`. -/
theorem getD_addE : ∀ (a b : List ℤ) (i : ℕ), (addE a b).getD i 0 = a.getD i 0 + b.getD i 0
  | [], b, i => by simp [addE]
  | a :: as, [], i => by simp [addE]
  | a :: as, b :: bs, 0 => by simp [addE]
  | a :: as, b :: bs, i + 1 => by
    simp only [addE, List.getD_cons_succ]
    exact getD_addE as bs i

/-- The exponent vector of `addE a b` is the sum of those of `a` and `b`. -/
theorem expFun_addE (m : ℕ) (a b : List ℤ) : expFun m (addE a b) = expFun m a + expFun m b := by
  funext i
  simp only [expFun, Pi.add_apply]
  exact getD_addE a b i

/-- Lexicographic comparison of exponent lists; only used to keep term lists short, never for
soundness. -/
def ltE : List ℤ → List ℤ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then ltE as bs else decide (a < b)

namespace Poly

variable (m : ℕ)

/-- The Laurent polynomial `∑ c X^e` of a term list. -/
noncomputable def toL (p : Poly) : LaurentRing m :=
  (p.map fun t => AddMonoidAlgebra.single (expFun m t.1) t.2).sum

/-- The empty term list is the zero polynomial. -/
@[simp] theorem toL_nil : toL m [] = 0 := rfl

/-- The polynomial of `(e, c) :: p` is `c X^e` plus that of `p`. -/
@[simp] theorem toL_cons (t : List ℤ × ℤ) (p : Poly) :
    toL m (t :: p) = AddMonoidAlgebra.single (expFun m t.1) t.2 + toL m p := by
  simp [toL]

/-- The polynomial of a concatenation of term lists is the sum of their polynomials. -/
@[simp] theorem toL_append (p q : Poly) : toL m (p ++ q) = toL m p + toL m q := by
  simp [toL]

/-- Insertion of one term into a term list, combining equal exponents. -/
def mergeAux (x : List ℤ × ℤ) (xs : Poly) (rec : Poly → Poly) : Poly → Poly
  | [] => x :: xs
  | y :: ys =>
    if x.1 = y.1 then
      (if x.2 + y.2 = 0 then rec ys else (x.1, x.2 + y.2) :: rec ys)
    else if ltE y.1 x.1 then x :: rec (y :: ys)
    else y :: mergeAux x xs rec ys

/-- The sum of two term lists, by merging. -/
def merge : Poly → Poly → Poly
  | [], ys => ys
  | x :: xs, ys => mergeAux x xs (merge xs) ys

variable {m}

/-- If `rec zs` represents the sum of `xs` and `zs` for every `zs`, then `mergeAux x xs rec ys`
represents the sum of `x :: xs` and `ys`. -/
theorem toL_mergeAux (x : List ℤ × ℤ) (xs : Poly) (rec : Poly → Poly)
    (hrec : ∀ zs, toL m (rec zs) = toL m xs + toL m zs) :
    ∀ ys, toL m (mergeAux x xs rec ys) = toL m (x :: xs) + toL m ys
  | [] => by simp [mergeAux]
  | y :: ys => by
    unfold mergeAux
    split_ifs with h1 h2 h3
    · have : AddMonoidAlgebra.single (expFun m y.1) x.2 +
          AddMonoidAlgebra.single (expFun m y.1) y.2 = 0 := by
        rw [← AddMonoidAlgebra.single_add, h2, AddMonoidAlgebra.single_zero]
      simp only [hrec, toL_cons, h1]
      linear_combination (-1 : LaurentRing m) * this
    · simp only [hrec, toL_cons, h1, AddMonoidAlgebra.single_add]
      abel
    · simp only [hrec, toL_cons]
      abel
    · simp only [toL_cons, toL_mergeAux x xs rec hrec ys]
      abel

/-- `merge p q` represents the sum of the polynomials of `p` and `q`. -/
theorem toL_merge : ∀ p q : Poly, toL m (merge p q) = toL m p + toL m q
  | [], q => by simp [merge]
  | x :: xs, q => by
    rw [merge, toL_mergeAux x xs (merge xs) (fun zs => toL_merge xs zs)]

/-- Merging adjacent pairs of a list of term lists. -/
def mergePairs : List Poly → List Poly
  | p :: q :: rest => merge p q :: mergePairs rest
  | ls => ls

/-- Merging adjacent pairs preserves the sum of the polynomials of a list of term lists. -/
theorem sum_map_toL_mergePairs : ∀ ls : List Poly,
    ((mergePairs ls).map (toL m)).sum = (ls.map (toL m)).sum
  | [] => rfl
  | [p] => rfl
  | p :: q :: rest => by
    rw [mergePairs, List.map_cons, List.sum_cons, toL_merge, sum_map_toL_mergePairs rest]
    simp [add_assoc]

/-- The sum of a list of term lists, by rounds of pairwise merges (`fuel` rounds, then a fold). -/
def mergeAll : ℕ → List Poly → Poly
  | _, [] => []
  | _, [p] => p
  | 0, p :: q :: rest => (p :: q :: rest).foldr merge []
  | f + 1, p :: q :: rest => mergeAll f (mergePairs (p :: q :: rest))

/-- Folding a list of term lists with `merge` represents the sum of their polynomials. -/
theorem toL_foldr_merge (ls : List Poly) : toL m (ls.foldr merge []) = (ls.map (toL m)).sum := by
  induction ls with
  | nil => rfl
  | cons p ls ih => rw [List.foldr_cons, toL_merge, ih, List.map_cons, List.sum_cons]

/-- `mergeAll f ls` represents the sum of the polynomials of the term lists `ls`. -/
theorem toL_mergeAll : ∀ (f : ℕ) (ls : List Poly), toL m (mergeAll f ls) = (ls.map (toL m)).sum
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | _, [p] => by simp [mergeAll]
  | 0, p :: q :: rest => by rw [mergeAll, toL_foldr_merge]
  | f + 1, p :: q :: rest => by
    rw [mergeAll, toL_mergeAll f, sum_map_toL_mergePairs]

/-- A term list multiplied by one term. -/
def scale (t : List ℤ × ℤ) (q : Poly) : Poly :=
  q.map fun s => (addE t.1 s.1, t.2 * s.2)

/-- `scale (e, c) q` represents `c X^e` times the polynomial of `q`. -/
theorem toL_scale (t : List ℤ × ℤ) (q : Poly) :
    toL m (scale t q) = AddMonoidAlgebra.single (expFun m t.1) t.2 * toL m q := by
  induction q with
  | nil => simp [scale]
  | cons s q ih =>
    simp only [scale, List.map_cons, toL_cons] at ih ⊢
    rw [ih, mul_add, AddMonoidAlgebra.single_mul_single, expFun_addE]

/-- The product of two term lists. -/
def mul (p q : Poly) : Poly :=
  mergeAll 16 (p.map fun t => scale t q)

/-- `mul p q` represents the product of the polynomials of `p` and `q`. -/
theorem toL_mul (p q : Poly) : toL m (mul p q) = toL m p * toL m q := by
  rw [mul, toL_mergeAll, List.map_map]
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [List.map_cons, List.sum_cons, Function.comp_apply, toL_scale, ih, toL_cons, add_mul]

variable (m) in
/-- The term list of the constant `1`, with an exponent list of length `m`. -/
def one : Poly := [(List.replicate m 0, 1)]

/-- `one m` represents the constant `1`. -/
theorem toL_one : toL m (one m) = 1 := by
  simp only [one, toL_cons, toL_nil, add_zero]
  have : expFun m (List.replicate m 0) = 0 := by
    funext i
    simp [expFun, List.getD_eq_getElem?_getD, i.2]
  rw [this]
  rfl

variable (m) in
/-- A power of a term list. -/
def pow (p : Poly) : ℕ → Poly
  | 0 => one m
  | k + 1 => mul (pow p k) p

/-- `pow m p k` represents the `k`-th power of the polynomial of `p`. -/
theorem toL_pow (p : Poly) : ∀ k, toL m (pow m p k) = toL m p ^ k
  | 0 => by rw [pow, toL_one, pow_zero]
  | k + 1 => by rw [pow, toL_mul, toL_pow p k, pow_succ]

/-- The coefficient of `X^e` read off a term list. -/
def coeffAt (m : ℕ) (p : Poly) (e : List ℤ) : ℤ :=
  (p.map fun t => bif allBelow m (fun i => decide (t.1.getD i 0 = e.getD i 0)) then t.2 else 0).sum

/-- The coefficient of `X^e` in the polynomial of `p` is `coeffAt m p e`. -/
theorem toL_apply (p : Poly) (e : List ℤ) : (toL m p) (expFun m e) = coeffAt m p e := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [toL_cons, AddMonoidAlgebra.coe_add, Pi.add_apply, ih]
    simp only [coeffAt, List.map_cons, List.sum_cons]
    classical
    rw [AddMonoidAlgebra.single_apply]
    congr 1
    have key : allBelow m (fun i => decide (t.1.getD i 0 = e.getD i 0)) = true ↔
        expFun m t.1 = expFun m e := by
      rw [allBelow_iff, funext_iff]
      simp only [decide_eq_true_eq, expFun]
      exact ⟨fun h i => h i i.2, fun h i hi => h ⟨i, hi⟩⟩
    by_cases hk : expFun m t.1 = expFun m e
    · rw [if_pos hk, key.2 hk]
      rfl
    · have hf : allBelow m (fun i => decide (t.1.getD i 0 = e.getD i 0)) = false := by
        rw [← Bool.not_eq_true, key]
        exact hk
      rw [if_neg hk, hf]
      rfl

end Poly

/-! ### Raw certificates -/

/-- The exponent list of `X_i`. -/
def unitExp (m i : ℕ) : List ℤ :=
  (List.range m).map fun j => if j = i then 1 else 0

/-- The term list of `X_i`. -/
def unitPoly (m i : ℕ) : Poly :=
  [(unitExp m i, 1)]

/-- For `i < m`, `unitPoly m i` represents the variable `X_i`. -/
theorem toL_unitPoly {m i : ℕ} (hi : i < m) :
    Poly.toL m (unitPoly m i) = LaurentRing.X ⟨i, hi⟩ := by
  have : expFun m (unitExp m i) = Pi.single ⟨i, hi⟩ 1 := by
    funext j
    simp only [expFun, unitExp, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range j.2, Option.map_some, Option.getD_some, Pi.single_apply, Fin.ext_iff]
  simp only [unitPoly, Poly.toL_cons, Poly.toL_nil, add_zero, this]
  rfl

/-- The mutation rule for one entry, on biased digits: `t` is the digit of entry `(i, j)` of
`μ_k(B)` when `D` gives the digits of `B`. -/
def mutOK (b : ℕ) (D : ℕ → ℕ → ℕ) (k i j t : ℕ) : Bool :=
  bif Nat.beq i k || Nat.beq j k then Nat.beq (t + D i j) (2 * b)
  else bif Nat.blt b (D i k) && Nat.blt b (D k j) then
    Nat.beq t (D i j + (D i k - b) * (D k j - b))
  else bif Nat.blt (D i k) b && Nat.blt (D k j) b then
    Nat.beq (t + (b - D i k) * (b - D k j)) (D i j)
  else Nat.beq t (D i j)

/-- `Nat.beq a b` is the decision of `a = b`. -/
theorem nat_beq_eq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.2 (by simp [Nat.beq_eq])

/-- `Nat.blt a b` is the decision of `a < b`. -/
theorem nat_blt_eq_decide (a b : ℕ) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.2 (by simp [Nat.blt_eq])

/-- If `mutOK` holds, then `t - b` is the entry `(i, j)` of the mutation in direction `k` of the
matrix with entries `D i j - b`. -/
theorem mutOK_spec {b : ℕ} {D : ℕ → ℕ → ℕ} {k i j t : ℕ} (h : mutOK b D k i j t = true) :
    ((t : ℤ) - b) =
      if i = k ∨ j = k then -((D i j : ℤ) - b)
      else if 0 < (D i k : ℤ) - b ∧ 0 < (D k j : ℤ) - b then
        ((D i j : ℤ) - b) + ((D i k : ℤ) - b) * ((D k j : ℤ) - b)
      else if (D i k : ℤ) - b < 0 ∧ (D k j : ℤ) - b < 0 then
        ((D i j : ℤ) - b) - ((D i k : ℤ) - b) * ((D k j : ℤ) - b)
      else (D i j : ℤ) - b := by
  simp only [mutOK, nat_beq_eq_decide, nat_blt_eq_decide, ← Bool.decide_or, ← Bool.decide_and,
    Bool.cond_decide] at h
  split_ifs at h with h1 h2 h3 <;> simp only [decide_eq_true_eq] at h
  · rw [if_pos h1]
    omega
  · rw [if_neg h1, if_pos (by omega), h]
    push_cast [Nat.cast_sub h2.1.le, Nat.cast_sub h2.2.le]
    ring
  · rw [if_neg h1, if_neg (by omega), if_pos (by omega)]
    have h' : ((t + (b - D i k) * (b - D k j) : ℕ) : ℤ) = (D i j : ℤ) := by rw [h]
    push_cast [Nat.cast_sub h3.1.le, Nat.cast_sub h3.2.le] at h'
    linear_combination h'
  · rw [if_neg h1, if_neg (by omega), if_neg (by omega), h]

/-! ### Packed matrices

An `m × n` matrix `f` with entries below `4096` is packed into the number
`CertificateCheck.dsum m n f = ∑ f i j · 4096^{i n + j}`, which determines it
(`CertificateCheck.dsum_injOn`). -/

/-- The packing `∑ f i j · 4096^{i n + j}` of an `m × n` array. -/
def dsum (m n : ℕ) (f : ℕ → ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f i j * 4096 ^ (i * n + j)

/-- The packing is additive. -/
theorem dsum_add (m n : ℕ) (f g : ℕ → ℕ → ℕ) :
    dsum m n f + dsum m n g = dsum m n fun i j => f i j + g i j := by
  simp only [dsum, ← Finset.sum_add_distrib, add_mul]

/-- A number with `N` digits below `B` in base `B` is less than `B^N`. -/
theorem sum_mul_pow_lt {B : ℕ} : ∀ {N : ℕ} {x : ℕ → ℕ}, (∀ p < N, x p < B) →
    ∑ p ∈ Finset.range N, x p * B ^ p < B ^ N
  | 0, _, _ => by simp
  | N + 1, x, hx => by
    rw [Finset.sum_range_succ]
    have hS := sum_mul_pow_lt (N := N) fun p hp => hx p (by omega)
    calc ∑ p ∈ Finset.range N, x p * B ^ p + x N * B ^ N < B ^ N + x N * B ^ N := by omega
      _ = (x N + 1) * B ^ N := by ring
      _ ≤ B * B ^ N := Nat.mul_le_mul_right _ (hx N (by omega))
      _ = B ^ (N + 1) := by ring

/-- Two sequences of `N` digits below `B` with the same value in base `B` agree. -/
theorem sum_mul_pow_injOn {B : ℕ} : ∀ {N : ℕ} {x y : ℕ → ℕ}, (∀ p < N, x p < B) →
    (∀ p < N, y p < B) →
    ∑ p ∈ Finset.range N, x p * B ^ p = ∑ p ∈ Finset.range N, y p * B ^ p → ∀ p < N, x p = y p
  | 0, _, _, _, _, _ => fun p hp => absurd hp (Nat.not_lt_zero p)
  | N + 1, x, y, hx, hy, h => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
    have hS := sum_mul_pow_lt (N := N) fun p hp => hx p (by omega)
    have hS' := sum_mul_pow_lt (N := N) fun p hp => hy p (by omega)
    have hpos : 0 < B ^ N := pow_pos (by have := hx N (by omega); omega) _
    have hN : x N = y N := by
      simpa only [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hS, Nat.div_eq_of_lt hS',
        zero_add] using congrArg (· / B ^ N) h
    rw [hN] at h
    have ih := sum_mul_pow_injOn (N := N) (fun p hp => hx p (by omega))
      (fun p hp => hy p (by omega)) (Nat.add_right_cancel h)
    intro p hp
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
    exacts [ih p hp, hN]

/-- The packing of an `m × n` array is the base-`4096^n` number whose digits are the packed
rows. -/
theorem dsum_eq (m n : ℕ) (f : ℕ → ℕ → ℕ) :
    dsum m n f = ∑ i ∈ Finset.range m,
      (∑ j ∈ Finset.range n, f i j * 4096 ^ j) * (4096 ^ n) ^ i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, ← pow_mul, mul_comm n i]
  ring

/-- Two `m × n` arrays with entries below `4096` and the same packing agree. -/
theorem dsum_injOn {m n : ℕ} {x y : ℕ → ℕ → ℕ} (hx : ∀ i < m, ∀ j < n, x i j < 4096)
    (hy : ∀ i < m, ∀ j < n, y i j < 4096) (h : dsum m n x = dsum m n y) :
    ∀ i < m, ∀ j < n, x i j = y i j := by
  rw [dsum_eq, dsum_eq] at h
  have hrow := sum_mul_pow_injOn (fun i hi => sum_mul_pow_lt (hx i hi))
    (fun i hi => sum_mul_pow_lt (hy i hi)) h
  exact fun i hi => sum_mul_pow_injOn (hx i hi) (hy i hi) (hrow i hi)

/-! ### Transitions checked as reverses -/

variable {m n : ℕ}

/-- Mutation in direction `k` is an involution on integer matrices. -/
theorem matrixMutation_matrixMutation_int (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ)
    (k : Fin n) : matrixMutation hmn (matrixMutation hmn B k) k = B := by
  ext i j
  by_cases h : i = Fin.castLE hmn k ∨ j = k
  · rw [matrixMutation_apply_of_eq hmn _ k h, matrixMutation_apply_of_eq hmn _ k h, neg_neg]
  · push Not at h
    rw [matrixMutation_apply_of_ne hmn _ k h.1 h.2, matrixMutation_apply_col,
      matrixMutation_apply_row, matrixMutation_apply_of_ne hmn _ k h.1 h.2]
    simp only [neg_pos, neg_lt_zero]
    by_cases h1 : 0 < B i k ∧ 0 < B (Fin.castLE hmn k) j
    · have h2 : ¬(B i k < 0 ∧ B (Fin.castLE hmn k) j < 0) := fun h2 => by linarith [h1.1, h2.1]
      simp only [if_pos h1, if_neg h2]
      ring
    · by_cases h2 : B i k < 0 ∧ B (Fin.castLE hmn k) j < 0
      · simp only [if_pos h2, if_neg h1]
        ring
      · simp only [if_neg h1, if_neg h2]

/-- Across the reverse of a transition: if `μ_k(A) = B^σ`, the entry `(k, k)` of `A` is `0` and
the tuples `w_A`, `w_B` agree along `σ̂` away from row `k`, then the exchange monomials of `B` in
direction `σ(k)` are those of `A` in direction `k`, exchanged. -/
theorem monomial_relabel {M : Type*} [CommMonoid M] (hmn : n ≤ m)
    {A B : Matrix (Fin m) (Fin n) ℤ} {σ : Equiv.Perm (Fin n)} {k : Fin n}
    (hT1 : matrixMutation hmn A k = relabelMatrix hmn B σ) (hkk : A (Fin.castLE hmn k) k = 0)
    {wA wB : Fin m → M} (hw : ∀ i, i ≠ Fin.castLE hmn k → wB (σ.extendMutable hmn i) = wA i) :
    TypeE.monomialPos wB B (σ k) = TypeE.monomialNeg wA A k ∧
      TypeE.monomialNeg wB B (σ k) = TypeE.monomialPos wA A k := by
  have hcol : ∀ i, B (σ.extendMutable hmn i) (σ k) = -A i k := fun i => by
    have := congrArg (fun C : Matrix (Fin m) (Fin n) ℤ => C i k) hT1
    simp only [matrixMutation_apply_col, relabelMatrix_apply] at this
    exact this.symm
  unfold TypeE.monomialPos TypeE.monomialNeg
  constructor <;> rw [Finset.prod_filter, Finset.prod_filter] <;>
    refine (Fintype.prod_equiv (σ.extendMutable hmn) _ _ fun i => ?_).symm <;>
    rw [hcol] <;> by_cases hi : i = Fin.castLE hmn k
  · subst hi
    simp [hkk]
  · rw [hw i hi]
    simp only [neg_pos]
  · subst hi
    simp [hkk]
  · rw [hw i hi, neg_neg]
    simp only [neg_lt_zero]

/-- If `β ∘ σ` agrees with `α` away from `k`, then the extended tuples of `β` and `α` agree along
`σ̂` away from row `k`. -/
theorem extTuple_extendMutable_of_ne {N : ℕ} (hmn : n ≤ m) (v : Fin N → LaurentRing m)
    {α β : Fin n → Fin N} {σ : Equiv.Perm (Fin n)} {k : Fin n}
    (h : ∀ j, j ≠ k → β (σ j) = α j) (i : Fin m) (hi : i ≠ Fin.castLE hmn k) :
    TypeE.extTuple v β (σ.extendMutable hmn i) = TypeE.extTuple v α i := by
  by_cases hin : (i : ℕ) < n
  · have hik : (⟨i, hin⟩ : Fin n) ≠ k := fun hj => hi (Fin.ext (by simp [← hj]))
    rw [Equiv.Perm.extendMutable_apply_of_lt hmn _ hin]
    simp only [TypeE.extTuple, Fin.val_castLE, dif_pos hin, dif_pos (σ ⟨i, hin⟩).2]
    rw [← h ⟨i, hin⟩ hik]
  · rw [Equiv.Perm.extendMutable_apply_of_le hmn _ (not_lt.1 hin)]
    simp only [TypeE.extTuple, dif_neg hin]

/-- If `μ_{σ(k)}(B) = A^{σ⁻¹}`, then `μ_k(A) = B^σ`. -/
theorem matrixMutation_eq_relabelMatrix_of_inv (hmn : n ≤ m)
    {A B : Matrix (Fin m) (Fin n) ℤ} {σ : Equiv.Perm (Fin n)} {k : Fin n}
    (e : matrixMutation hmn B (σ k) = relabelMatrix hmn A σ⁻¹) :
    matrixMutation hmn A k = relabelMatrix hmn B σ := by
  have e2 : matrixMutation hmn (relabelMatrix hmn B σ) k = A := by
    have := matrixMutationList_relabelMatrix hmn B σ [k]
    rw [matrixMutationList_singleton, List.map_singleton, matrixMutationList_singleton] at this
    rw [this, e, relabelMatrix_relabelMatrix, inv_mul_cancel]
    ext i j
    simp only [relabelMatrix_apply, Equiv.Perm.extendMutable_one, Equiv.Perm.one_apply]
  rw [← e2, matrixMutation_matrixMutation_int]

namespace Raw

variable (R : Raw)

/-- The entry `(i, j)` of `B̃_a`. -/
def entry (a i j : ℕ) : ℤ :=
  (R.matD a i j : ℤ) - R.bias

/-- The term list of an atom: `v_c` for `c < N`, `X_{c - N}` otherwise. -/
def atom (m N c : ℕ) : Poly :=
  bif Nat.blt c N then R.var c else unitPoly m (c - N)

/-- The product of the powers of the atoms of a list. -/
def prodAtoms (m N : ℕ) (l : List (ℕ × ℕ)) : Poly :=
  l.foldl (fun acc t => Poly.mul acc (Poly.pow m (R.atom m N t.1) t.2)) (Poly.one m)

/-- The atom of row `i` of the seed `a`. -/
def atomOf (n N a i : ℕ) : ℕ :=
  bif Nat.blt i n then R.alpha a i else N + i

/-- The rows with a positive entry in column `k` of `B̃_a`, as atoms with exponents. -/
def posAtoms (m n N a k : ℕ) : List (ℕ × ℕ) :=
  (List.range m).filterMap fun i =>
    bif Nat.blt R.bias (R.matD a i k) then some (R.atomOf n N a i, R.matD a i k - R.bias)
    else none

/-- The rows with a negative entry in column `k` of `B̃_a`, as atoms with exponents. -/
def negAtoms (m n N a k : ℕ) : List (ℕ × ℕ) :=
  (List.range m).filterMap fun i =>
    bif Nat.blt (R.matD a i k) R.bias then some (R.atomOf n N a i, R.bias - R.matD a i k)
    else none

/-- The key of `posAtoms`, computed without building the list. -/
def posKey (m n N a k : ℕ) : ℕ :=
  sumBelow m fun i => bif Nat.blt R.bias (R.matD a i k) then
    Nat.mul (R.matD a i k - R.bias) (Nat.pow 16 (R.atomOf n N a i)) else 0

/-- The key of `negAtoms`, computed without building the list. -/
def negKey (m n N a k : ℕ) : ℕ :=
  sumBelow m fun i => bif Nat.blt (R.matD a i k) R.bias then
    Nat.mul (R.bias - R.matD a i k) (Nat.pow 16 (R.atomOf n N a i)) else 0

/-- The monomials of the relation `r` are good lists of atoms (`CertificateCheck.AtomsGood`), so
that they are determined by their keys. -/
def relShapeOK (r : ℕ) : Bool :=
  atomsOK (R.relPos r) && atomsOK (R.relNeg r)

/-- The transition `(a, k)` matches relation `r`, up to the order of the factors and of the
monomials, the monomials being compared through their keys. -/
def relMatchKey (x y pk nk r : ℕ) : Bool :=
  ((Nat.beq x (R.relX r) && Nat.beq y (R.relY r)) ||
      (Nat.beq x (R.relY r) && Nat.beq y (R.relX r))) &&
    ((Nat.beq pk (atomKey (R.relPos r)) && Nat.beq nk (atomKey (R.relNeg r))) ||
      (Nat.beq pk (atomKey (R.relNeg r)) && Nat.beq nk (atomKey (R.relPos r))))

/-- The relabelled row index: `π(i)` for a mutable row, `i` for a frozen one. -/
def extIdx (n : ℕ) (π : ℕ → ℕ) (i : ℕ) : ℕ :=
  bif Nat.blt i n then π i else i

/-- Conditions (i) and (ii) at the seed `1`: `α₁ = id` and `vᵢ = Xᵢ`. -/
def initOK (m n : ℕ) : Bool :=
  allBelow n fun i => Nat.beq (R.alpha 0 i) i && decide (R.var i = unitPoly m i)

/-- The cluster of the seed `a` is strictly increasing with values below `N`. -/
def seedOK (n N a : ℕ) : Bool :=
  allBelow n (fun i => Nat.blt (R.alpha a i) N) &&
    allBelow (n - 1) fun i => Nat.blt (R.alpha a i) (R.alpha a (i + 1))

/-- A code of the cluster of the seed `a`; it depends on `α_a` only. -/
def code (n N a : ℕ) : ℕ :=
  ((List.range n).map (R.alpha a)).foldl (fun acc x => acc * N + x) 0

/-- The codes of consecutive seeds increase, for (D2). -/
def lexOK (n N a : ℕ) : Bool :=
  Nat.blt (R.code n N a) (R.code n N (a + 1))

/-- `B̃_a`, packed (`CertificateCheck.dsum`). -/
def packMat (m n a : ℕ) : ℕ :=
  sumBelow m fun i => sumBelow n fun j => Nat.mul (R.matD a i j) (Nat.pow 4096 (i * n + j))

/-- `B̃_{ν(a,k)}^{π_{a,k}}`, packed. -/
def packNext (m n a k : ℕ) : ℕ :=
  sumBelow m fun i => sumBelow n fun j =>
    Nat.mul (R.matD (R.next a k) (extIdx n (R.perm a k) i) (R.perm a k j))
      (Nat.pow 4096 (i * n + j))

/-- Row `k` and column `k` of the array `f`, packed. -/
def packRowCol (m n k : ℕ) (f : ℕ → ℕ → ℕ) : ℕ :=
  Nat.add (sumBelow n fun j => Nat.mul (f k j) (Nat.pow 4096 (k * n + j)))
    (sumBelow m fun i => bif Nat.beq i k then 0 else Nat.mul (f i k) (Nat.pow 4096 (i * n + k)))

/-- The positive entries of column `k` of `B̃_a` off row `k`, packed with stride `4096^n`. -/
def colPos (m n a k : ℕ) : ℕ :=
  sumBelow m fun i => bif Nat.beq i k then 0 else bif Nat.blt R.bias (R.matD a i k) then
    Nat.mul (R.matD a i k - R.bias) (Nat.pow 4096 (i * n)) else 0

/-- The negative entries of column `k` of `B̃_a` off row `k`, negated, packed with stride
`4096^n`. -/
def colNeg (m n a k : ℕ) : ℕ :=
  sumBelow m fun i => bif Nat.beq i k then 0 else bif Nat.blt (R.matD a i k) R.bias then
    Nat.mul (R.bias - R.matD a i k) (Nat.pow 4096 (i * n)) else 0

/-- The positive entries of row `k` of `B̃_a` off column `k`, packed. -/
def rowPos (n a k : ℕ) : ℕ :=
  sumBelow n fun j => bif Nat.beq j k then 0 else bif Nat.blt R.bias (R.matD a k j) then
    Nat.mul (R.matD a k j - R.bias) (Nat.pow 4096 j) else 0

/-- The negative entries of row `k` of `B̃_a` off column `k`, negated, packed. -/
def rowNeg (n a k : ℕ) : ℕ :=
  sumBelow n fun j => bif Nat.beq j k then 0 else bif Nat.blt (R.matD a k j) R.bias then
    Nat.mul (R.bias - R.matD a k j) (Nat.pow 4096 j) else 0

/-- The mutation rule (T1) at the transition `(a, k)` on packed matrices: with `p`, `q` the
positive and `p'`, `q'` the negated negative parts of column and row `k`, entrywise
`t + 2 [row or column k] d + p' q' = d + 2 [row or column k] b + p q`. The products of the outer
products are single multiplications of packed numbers, and only `B̃_{ν(a,k)}` is read entry by
entry. With digits below `16` no packed sum carries, so the equation holds entrywise, which is
`mutOK` (`CertificateCheck.Raw.mutOK_of_mutPackOK`). -/
def mutPackOK (m n a k : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.add (R.packNext m n a k) (packRowCol m n k fun i j => Nat.mul 2 (R.matD a i j)))
      (Nat.mul (R.colNeg m n a k) (R.rowNeg n a k)))
    (Nat.add (Nat.add (R.packMat m n a) (packRowCol m n k fun _ _ => Nat.mul 2 R.bias))
      (Nat.mul (R.colPos m n a k) (R.rowPos n a k)))

/-- The conditions (T1), (T2), (T3) on the transition `(a, k)`, with `π_{a,k}` a permutation,
checked in full: (T1) on packed matrices, and (T3) by comparing the keys of the exchange
monomials with those of the relation. -/
def fwdOK (m n N M numRel a k : ℕ) : Bool :=
  Nat.blt (R.next a k) M &&
    allBelow n (fun j => Nat.blt (R.perm a k j) n) &&
    allBelow n (fun j => Nat.beq j k ||
      (Nat.beq (R.alpha (R.next a k) (R.perm a k j)) (R.alpha a j) &&
        !Nat.beq (R.perm a k j) (R.perm a k k))) &&
    R.mutPackOK m n a k &&
    (Nat.blt (R.rel a k) numRel &&
      R.relMatchKey (R.alpha a k) (R.alpha (R.next a k) (R.perm a k k))
        (R.posKey m n N a k) (R.negKey m n N a k) (R.rel a k))

/-- The transition `(a, k)` undoes the transition `(b, π_{a,k}(k))`, `b = ν(a, k) < a`:
`ν(b, π_{a,k}(k)) = a`, `π_{b, π_{a,k}(k)} ∘ π_{a,k} = id`, and the diagonal entry `(k, k)` of
`B̃_a` is `0`. Mutation being an involution, (T1), (T2), (T3) at `(a, k)` follow from the same
conditions at `(b, π_{a,k}(k))`, which are checked in full. -/
def revOK (n a k : ℕ) : Bool :=
  Nat.blt (R.next a k) a && Nat.blt (R.perm a k k) n &&
    Nat.beq (R.next (R.next a k) (R.perm a k k)) a && Nat.beq (R.matD a k k) R.bias &&
    allBelow n fun j => Nat.blt (R.perm a k j) n &&
      Nat.beq (R.perm (R.next a k) (R.perm a k k) (R.perm a k j)) j

/-- The check of the transition `(a, k)`: in full when it leads to a later seed (`a < ν(a, k)`),
and as the reverse of a transition checked in full otherwise. -/
def transOK (m n N M numRel a k : ℕ) : Bool :=
  bif Nat.blt a (R.next a k) then R.fwdOK m n N M numRel a k else R.revOK n a k

/-- The relation `r` holds: `v_X v_Y = ∏ P + ∏ Q`. -/
def relOK (m N r : ℕ) : Bool :=
  Nat.blt (R.relX r) N && Nat.blt (R.relY r) N &&
    decide (Poly.mul (R.var (R.relX r)) (R.var (R.relY r)) =
      Poly.merge (R.prodAtoms m N (R.relPos r)) (R.prodAtoms m N (R.relNeg r)))

/-- The variables `c` and `c'` differ: some exponent has different coefficients. -/
def distOK (m c c' : ℕ) : Bool :=
  (R.var c ++ R.var c').any fun t =>
    !decide (Poly.coeffAt m (R.var c) t.1 = Poly.coeffAt m (R.var c') t.1)

/-- (D3) for the variable `c`. -/
def coverOK (n M c : ℕ) : Bool :=
  Nat.blt (R.cover c) M && anyBelow n fun i => Nat.beq (R.alpha (R.cover c) i) c

/-- The spanning tree at the seed `a`, for (D4). -/
def treeOK (n M a : ℕ) : Bool :=
  Nat.beq a 0 ||
    (Nat.blt (R.parent a) M && Nat.blt (R.parentDir a) n &&
      Nat.beq (R.next (R.parent a) (R.parentDir a)) a &&
      Nat.beq (R.depth (R.parent a) + 1) (R.depth a))

/-! ### What the checks say -/

variable {R}

/-- If `initOK` holds, then `α₁(i) = i` and `vᵢ = Xᵢ` for `i < n`. -/
theorem initOK_spec {m n : ℕ} (h : R.initOK m n = true) {i : ℕ} (hi : i < n) :
    R.alpha 0 i = i ∧ R.var i = unitPoly m i := by
  simpa [nat_beq_eq_decide] using allBelow_iff.1 h i hi

/-- If `seedOK` holds, then the cluster of the seed `a` takes values below `N` and is strictly
increasing. -/
theorem seedOK_spec {n N a : ℕ} (h : R.seedOK n N a = true) :
    (∀ i < n, R.alpha a i < N) ∧ ∀ i j, i < j → j < n → R.alpha a i < R.alpha a j := by
  simp only [seedOK, Bool.and_eq_true, allBelow_iff, nat_blt_eq_decide, decide_eq_true_eq] at h
  refine ⟨h.1, fun i j hij hj => ?_⟩
  induction j, hij using Nat.le_induction with
  | base => exact h.2 i (by omega)
  | succ j hij ih => exact (ih (by omega)).trans (h.2 j (by omega))

/-- `packMat` is the packing of the digits of `B̃_a`. -/
theorem packMat_eq (m n a : ℕ) : R.packMat m n a = dsum m n fun i j => R.matD a i j := by
  simp only [packMat, sumBelow_eq, dsum, Nat.mul_eq, Nat.pow_eq]

/-- `packNext` is the packing of the digits of `B̃_{ν(a,k)}^{π_{a,k}}`. -/
theorem packNext_eq (m n a k : ℕ) : R.packNext m n a k = dsum m n fun i j =>
    R.matD (R.next a k) (extIdx n (R.perm a k) i) (R.perm a k j) := by
  simp only [packNext, sumBelow_eq, dsum, Nat.mul_eq, Nat.pow_eq]

/-- For `k < m` and `k < n`, `packRowCol` is the packing of the array that agrees with `f` on row
`k` and column `k` and vanishes elsewhere. -/
theorem packRowCol_eq {m n k : ℕ} (hkm : k < m) (hkn : k < n) (f : ℕ → ℕ → ℕ) :
    packRowCol m n k f =
      dsum m n fun i j => if i = k then f k j else if j = k then f i k else 0 := by
  simp only [packRowCol, sumBelow_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, nat_beq_eq_decide,
    Bool.cond_decide, dsum]
  have inner : ∀ i, ∑ j ∈ Finset.range n,
      (if i = k then f k j else if j = k then f i k else 0) * 4096 ^ (i * n + j) =
        (if i = k then ∑ j ∈ Finset.range n, f k j * 4096 ^ (k * n + j) else 0) +
          (if i = k then 0 else f i k * 4096 ^ (i * n + k)) := by
    intro i
    by_cases hi : i = k
    · subst hi
      simp
    · simp only [hi, if_false, zero_add, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' (Finset.range n) k, if_pos (Finset.mem_range.2 hkn)]
  rw [Finset.sum_congr rfl fun i _ => inner i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range m) k, if_pos (Finset.mem_range.2 hkm)]

/-- The product of `colPos` and `rowPos` is the packing of the outer product of the positive parts
of column `k` and row `k` of `B̃_a`, off row and column `k`. -/
theorem colPos_mul_rowPos (m n a k : ℕ) : R.colPos m n a k * R.rowPos n a k = dsum m n fun i j =>
    (if i = k then 0 else if R.bias < R.matD a i k then R.matD a i k - R.bias else 0) *
      (if j = k then 0 else if R.bias < R.matD a k j then R.matD a k j - R.bias else 0) := by
  simp only [colPos, rowPos, sumBelow_eq, Nat.mul_eq, Nat.pow_eq, nat_beq_eq_decide,
    nat_blt_eq_decide, Bool.cond_decide, dsum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- The product of `colNeg` and `rowNeg` is the packing of the outer product of the negated
negative parts of column `k` and row `k` of `B̃_a`, off row and column `k`. -/
theorem colNeg_mul_rowNeg (m n a k : ℕ) : R.colNeg m n a k * R.rowNeg n a k = dsum m n fun i j =>
    (if i = k then 0 else if R.matD a i k < R.bias then R.bias - R.matD a i k else 0) *
      (if j = k then 0 else if R.matD a k j < R.bias then R.bias - R.matD a k j else 0) := by
  simp only [colNeg, rowNeg, sumBelow_eq, Nat.mul_eq, Nat.pow_eq, nat_beq_eq_decide,
    nat_blt_eq_decide, Bool.cond_decide, dsum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- The entrywise equation of `mutPackOK` at `(i, j)` implies `mutOK` there. -/
theorem mutOK_of_digit_eq {b : ℕ} {D : ℕ → ℕ → ℕ} {k i j t : ℕ}
    (e : t + (if i = k then 2 * D k j else if j = k then 2 * D i k else 0) +
        (if i = k then 0 else if D i k < b then b - D i k else 0) *
          (if j = k then 0 else if D k j < b then b - D k j else 0) =
      D i j + (if i = k then 2 * b else if j = k then 2 * b else 0) +
        (if i = k then 0 else if b < D i k then D i k - b else 0) *
          (if j = k then 0 else if b < D k j then D k j - b else 0)) :
    mutOK b D k i j t = true := by
  simp only [mutOK, nat_beq_eq_decide, nat_blt_eq_decide, ← Bool.decide_or, ← Bool.decide_and,
    Bool.cond_decide]
  by_cases hik : i = k
  · subst hik
    simp only [true_or, if_pos, zero_mul, add_zero, decide_eq_true_eq] at e ⊢
    omega
  by_cases hjk : j = k
  · subst hjk
    simp only [hik, or_true, if_true, if_false, mul_zero, add_zero, decide_eq_true_eq] at e ⊢
    omega
  simp only [hik, hjk, or_self, if_false, add_zero] at e ⊢
  by_cases h1 : b < D i k ∧ b < D k j
  · simp only [h1, and_self, if_true, decide_eq_true_eq, not_lt_of_gt h1.1, not_lt_of_gt h1.2,
      if_false, zero_mul] at e ⊢
    omega
  by_cases h2 : D i k < b ∧ D k j < b
  · simp only [h2, and_self, if_true, if_false, decide_eq_true_eq, not_lt_of_gt h2.1,
      not_lt_of_gt h2.2, mul_zero] at e ⊢
    omega
  · simp only [h1, h2, if_false, decide_eq_true_eq]
    have hpp : (if b < D i k then D i k - b else 0) *
        (if b < D k j then D k j - b else 0) = 0 := by
      by_cases h3 : b < D i k
      · have h4 : ¬b < D k j := fun h4 => h1 ⟨h3, h4⟩
        simp [h4]
      · simp [h3]
    have hnn : (if D i k < b then b - D i k else 0) *
        (if D k j < b then b - D k j else 0) = 0 := by
      by_cases h3 : D i k < b
      · have h4 : ¬D k j < b := fun h4 => h2 ⟨h3, h4⟩
        simp [h4]
      · simp [h3]
    rw [hpp, hnn] at e
    omega

/-- With bias and digits below `16`, `mutPackOK` implies `mutOK` at every entry of
`B̃_{ν(a,k)}^{π_{a,k}}`. -/
theorem mutOK_of_mutPackOK {m n a k : ℕ} (hkn : k < n) (hnm : n ≤ m) (hb : R.bias < 16)
    (hdig : ∀ a i j, R.matD a i j < 16) (h : R.mutPackOK m n a k = true) :
    ∀ i < m, ∀ j < n, mutOK R.bias (R.matD a) k i j
      (R.matD (R.next a k) (extIdx n (R.perm a k) i) (R.perm a k j)) = true := by
  have hkm : k < m := by omega
  simp only [mutPackOK, nat_beq_eq_decide, decide_eq_true_eq, Nat.add_eq, Nat.mul_eq] at h
  rw [packNext_eq, packMat_eq, packRowCol_eq hkm hkn, packRowCol_eq hkm hkn, colPos_mul_rowPos,
    colNeg_mul_rowNeg, dsum_add, dsum_add, dsum_add, dsum_add] at h
  have hP : ∀ x : ℕ, x < 16 → (if R.bias < x then x - R.bias else 0) ≤ 15 := fun x hx => by
    split_ifs <;> omega
  have hN : ∀ x : ℕ, (if x < R.bias then R.bias - x else 0) ≤ 15 := fun x => by
    split_ifs <;> omega
  have hz : ∀ (c : Prop) [Decidable c] (x : ℕ), x ≤ 15 → (if c then 0 else x) ≤ 15 :=
    fun c _ x hx => by split_ifs <;> omega
  intro i hi j hj
  have e := dsum_injOn (fun i _ j _ => ?_) (fun i _ j _ => ?_) h i hi j hj
  · exact mutOK_of_digit_eq e
  · have ht := hdig (R.next a k) (extIdx n (R.perm a k) i) (R.perm a k j)
    have hd1 := hdig a k j
    have hd2 := hdig a i k
    have hm := Nat.mul_le_mul (hz (i = k) _ (hN (R.matD a i k)))
      (hz (j = k) _ (hN (R.matD a k j)))
    have hr : (if i = k then 2 * R.matD a k j else if j = k then 2 * R.matD a i k else 0) ≤ 30 := by
      split_ifs <;> omega
    omega
  · have hd := hdig a i j
    have hm := Nat.mul_le_mul (hz (i = k) _ (hP (R.matD a i k) (hdig a i k)))
      (hz (j = k) _ (hP (R.matD a k j) (hdig a k j)))
    have hr : (if i = k then 2 * R.bias else if j = k then 2 * R.bias else 0) ≤ 30 := by
      split_ifs <;> omega
    omega

/-- The conditions asserted by `fwdOK` at the transition `(a, k)`. -/
theorem fwdOK_spec {m n N M numRel a k : ℕ} (hkn : k < n) (hnm : n ≤ m) (hb : R.bias < 16)
    (hdig : ∀ a i j, R.matD a i j < 16) (h : R.fwdOK m n N M numRel a k = true) :
    R.next a k < M ∧ (∀ j < n, R.perm a k j < n) ∧
      (∀ j < n, j ≠ k → R.alpha (R.next a k) (R.perm a k j) = R.alpha a j ∧
        R.perm a k j ≠ R.perm a k k) ∧
      (∀ i < m, ∀ j < n, mutOK R.bias (R.matD a) k i j
        (R.matD (R.next a k) (extIdx n (R.perm a k) i) (R.perm a k j)) = true) ∧
      R.rel a k < numRel ∧
      R.relMatchKey (R.alpha a k) (R.alpha (R.next a k) (R.perm a k k))
        (R.posKey m n N a k) (R.negKey m n N a k) (R.rel a k) = true := by
  simp only [fwdOK, Bool.and_eq_true, allBelow_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := h
  refine ⟨by simpa [nat_blt_eq_decide] using h1, fun j hj => by
    simpa [nat_blt_eq_decide] using h2 j hj, fun j hj hjk => ?_,
    mutOK_of_mutPackOK hkn hnm hb hdig h4, by simpa [nat_blt_eq_decide] using h5, h6⟩
  simpa only [nat_beq_eq_decide, Bool.or_eq_true, decide_eq_true_eq, hjk, false_or,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] using h3 j hj

/-- The conditions asserted by `revOK` at the transition `(a, k)`. -/
theorem revOK_spec {n a k : ℕ} (h : R.revOK n a k = true) :
    R.next a k < a ∧ R.perm a k k < n ∧ R.next (R.next a k) (R.perm a k k) = a ∧
      R.matD a k k = R.bias ∧
      ∀ j < n, R.perm a k j < n ∧ R.perm (R.next a k) (R.perm a k k) (R.perm a k j) = j := by
  simpa only [revOK, Bool.and_eq_true, allBelow_iff, nat_blt_eq_decide, nat_beq_eq_decide,
    decide_eq_true_eq, and_assoc] using h

/-- If `transOK` holds and `a < ν(a, k)`, then `fwdOK` holds. -/
theorem fwdOK_of_transOK {m n N M numRel a k : ℕ} (h : R.transOK m n N M numRel a k = true)
    (ha : a < R.next a k) : R.fwdOK m n N M numRel a k = true := by
  simpa [transOK, nat_blt_eq_decide, ha] using h

/-- If `transOK` holds and `ν(a, k) ≤ a`, then `revOK` holds. -/
theorem revOK_of_transOK {m n N M numRel a k : ℕ} (h : R.transOK m n N M numRel a k = true)
    (ha : ¬a < R.next a k) : R.revOK n a k = true := by
  simpa [transOK, nat_blt_eq_decide, ha] using h

/-- `posKey` is the key of `posAtoms`. -/
theorem posKey_eq (m n N a k : ℕ) : R.posKey m n N a k = atomKey (R.posAtoms m n N a k) := by
  rw [posKey, posAtoms, atomKey_filterMap_range]
  congr 1
  funext i
  cases R.bias.blt (R.matD a i k) <;> simp [Nat.mul_eq, Nat.pow_eq, mul_comm]

/-- `negKey` is the key of `negAtoms`. -/
theorem negKey_eq (m n N a k : ℕ) : R.negKey m n N a k = atomKey (R.negAtoms m n N a k) := by
  rw [negKey, negAtoms, atomKey_filterMap_range]
  congr 1
  funext i
  cases (R.matD a i k).blt R.bias <;> simp [Nat.mul_eq, Nat.pow_eq, mul_comm]

/-- If the cluster of the seed `a` is strictly increasing with values below `N`, then the atoms of
its rows are strictly increasing. -/
theorem atomOf_lt_atomOf {n N a : ℕ} (hN : ∀ i < n, R.alpha a i < N)
    (hmono : ∀ i j, i < j → j < n → R.alpha a i < R.alpha a j) {i j : ℕ} (hij : i < j) :
    R.atomOf n N a i < R.atomOf n N a j := by
  simp only [atomOf, nat_blt_eq_decide, Bool.cond_decide]
  split_ifs with hi hj hj
  · exact hmono i j hij hj
  · have := hN i hi
    omega
  · omega
  · omega

/-- For a strictly increasing cluster with values below `N` and column digits below
`bias + 16`, `posAtoms` is a good list of atoms. -/
theorem atomsGood_posAtoms {m n N a k : ℕ} (hN : ∀ i < n, R.alpha a i < N)
    (hmono : ∀ i j, i < j → j < n → R.alpha a i < R.alpha a j)
    (hb : ∀ i < m, R.matD a i k < R.bias + 16) : AtomsGood (R.posAtoms m n N a k) := by
  refine ⟨List.Pairwise.filterMap _ (fun i j hij x hx y hy => ?_) List.pairwise_lt_range,
    fun t ht => ?_⟩
  · simp only [nat_blt_eq_decide, Bool.cond_decide] at hx hy
    split_ifs at hx hy
    cases hx
    cases hy
    exact atomOf_lt_atomOf hN hmono hij
  · obtain ⟨i, hi, hti⟩ := List.mem_filterMap.1 ht
    simp only [nat_blt_eq_decide, Bool.cond_decide] at hti
    split_ifs at hti with h
    cases hti
    have := hb i (List.mem_range.1 hi)
    exact ⟨by omega, by omega⟩

/-- For a strictly increasing cluster with values below `N` and bias below `16`, `negAtoms` is a
good list of atoms. -/
theorem atomsGood_negAtoms {m n N a k : ℕ} (hN : ∀ i < n, R.alpha a i < N)
    (hmono : ∀ i j, i < j → j < n → R.alpha a i < R.alpha a j) (hb : R.bias < 16) :
    AtomsGood (R.negAtoms m n N a k) := by
  refine ⟨List.Pairwise.filterMap _ (fun i j hij x hx y hy => ?_) List.pairwise_lt_range,
    fun t ht => ?_⟩
  · simp only [nat_blt_eq_decide, Bool.cond_decide] at hx hy
    split_ifs at hx hy
    cases hx
    cases hy
    exact atomOf_lt_atomOf hN hmono hij
  · obtain ⟨i, -, hti⟩ := List.mem_filterMap.1 ht
    simp only [nat_blt_eq_decide, Bool.cond_decide] at hti
    split_ifs at hti with h
    cases hti
    exact ⟨by omega, by omega⟩

/-- For good lists `pos` and `neg` and a relation `r` of the right shape, `relMatchKey` implies
that the factors and the monomials agree with those of `r`, up to order. -/
theorem relMatchKey_spec {x y : ℕ} {pos neg : List (ℕ × ℕ)} {r : ℕ} (hpos : AtomsGood pos)
    (hneg : AtomsGood neg) (hshape : R.relShapeOK r = true)
    (h : R.relMatchKey x y (atomKey pos) (atomKey neg) r = true) :
    ((x = R.relX r ∧ y = R.relY r) ∨ (x = R.relY r ∧ y = R.relX r)) ∧
      ((pos = R.relPos r ∧ neg = R.relNeg r) ∨ (pos = R.relNeg r ∧ neg = R.relPos r)) := by
  simp only [relShapeOK, Bool.and_eq_true] at hshape
  have gP := atomsGood_of_atomsOK hshape.1
  have gN := atomsGood_of_atomsOK hshape.2
  simp only [relMatchKey, Bool.and_eq_true, Bool.or_eq_true, nat_beq_eq_decide,
    decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨atomKey_injOn hpos gP h1, atomKey_injOn hneg gN h2⟩
  · exact Or.inr ⟨atomKey_injOn hpos gN h1, atomKey_injOn hneg gP h2⟩

/-- The conditions asserted by `relOK` for the relation `r`, on term lists. -/
theorem relOK_spec {m N r : ℕ} (h : R.relOK m N r = true) :
    R.relX r < N ∧ R.relY r < N ∧
      Poly.mul (R.var (R.relX r)) (R.var (R.relY r)) =
        Poly.merge (R.prodAtoms m N (R.relPos r)) (R.prodAtoms m N (R.relNeg r)) := by
  simpa [relOK, nat_blt_eq_decide, and_assoc] using h

/-- If `relOK` holds, the relation `r` holds in `LaurentRing m`. -/
theorem toL_relOK {m N r : ℕ} (h : R.relOK m N r = true) :
    Poly.toL m (R.var (R.relX r)) * Poly.toL m (R.var (R.relY r)) =
      Poly.toL m (R.prodAtoms m N (R.relPos r)) + Poly.toL m (R.prodAtoms m N (R.relNeg r)) := by
  have hL := congrArg (Poly.toL m) (relOK_spec h).2.2
  rwa [Poly.toL_mul, Poly.toL_merge] at hL

/-- If `distOK` holds, the variables `v_c` and `v_{c'}` are distinct. -/
theorem toL_ne_of_distOK {m c c' : ℕ} (h : R.distOK m c c' = true) :
    Poly.toL m (R.var c) ≠ Poly.toL m (R.var c') := by
  simp only [distOK, List.any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨t, -, ht⟩ := h
  intro he
  apply ht
  rw [← Poly.toL_apply, ← Poly.toL_apply]
  exact congrArg (fun f => f (expFun m t.1)) he

/-- If `coverOK` holds, the variable `c` lies in the cluster of the seed `cover c < M`. -/
theorem coverOK_spec {n M c : ℕ} (h : R.coverOK n M c = true) :
    R.cover c < M ∧ ∃ i < n, R.alpha (R.cover c) i = c := by
  simpa only [coverOK, Bool.and_eq_true, anyBelow_iff, nat_beq_eq_decide, nat_blt_eq_decide,
    decide_eq_true_eq] using h

/-- If `treeOK` holds at a seed `a ≠ 0`, then `a` is reached from its parent by one transition and
its depth is one more than its parent's. -/
theorem treeOK_spec {n M a : ℕ} (h : R.treeOK n M a = true) (ha : a ≠ 0) :
    R.parent a < M ∧ R.parentDir a < n ∧ R.next (R.parent a) (R.parentDir a) = a ∧
      R.depth (R.parent a) + 1 = R.depth a := by
  simpa [treeOK, nat_beq_eq_decide, nat_blt_eq_decide, ha, and_assoc] using h

/-- `prodAtoms` represents the product of the powers of the atoms of a list. -/
theorem toL_prodAtoms (m N : ℕ) (l : List (ℕ × ℕ)) :
    Poly.toL m (R.prodAtoms m N l) =
      (l.map fun t => Poly.toL m (R.atom m N t.1) ^ t.2).prod := by
  suffices ∀ acc, Poly.toL m (l.foldl (fun acc t => Poly.mul acc (Poly.pow m (R.atom m N t.1) t.2))
      acc) = Poly.toL m acc * (l.map fun t => Poly.toL m (R.atom m N t.1) ^ t.2).prod by
    rw [prodAtoms, this, Poly.toL_one, one_mul]
  induction l with
  | nil => simp
  | cons t l ih =>
    intro acc
    rw [List.foldl_cons, ih, Poly.toL_mul, Poly.toL_pow, List.map_cons, List.prod_cons, mul_assoc]

/-- The product of `g` over `l.filterMap F` is the product over `l` of `g` at `F i`, with `1` where
`F i` is `none`. -/
theorem prod_map_filterMap {α β M : Type*} [CommMonoid M] (l : List α) (F : α → Option β)
    (g : β → M) :
    ((l.filterMap F).map g).prod = (l.map fun i => (F i).elim 1 g).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filterMap_cons, List.map_cons, List.prod_cons, ← ih]
    cases F x <;> simp

/-- The product over `Finset.range m` equals the product of the list `List.range m`. -/
theorem prod_range_eq_prod_map_range {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∏ i ∈ Finset.range m, f i = ((List.range m).map f).prod := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Finset.prod_range_succ, List.prod_range_succ, ih]

/-- The variables of a raw certificate in `L_m`. -/
noncomputable def varL (m : ℕ) (R : Raw) (c : ℕ) : LaurentRing m :=
  Poly.toL m (R.var c)

/-- The atom of row `i` of the seed `a` represents entry `i` of the extended cluster of `a`. -/
theorem toL_atom_atomOf {m n N a : ℕ} (hN : ∀ i < n, R.alpha a i < N)
    (α : Fin n → Fin N) (hα : ∀ i : Fin n, (α i : ℕ) = R.alpha a i) (i : Fin m) :
    Poly.toL m (R.atom m N (R.atomOf n N a i)) =
      TypeE.extTuple (fun c : Fin N => varL m R c) α i := by
  simp only [TypeE.extTuple, atomOf, atom, nat_blt_eq_decide, Bool.cond_decide]
  by_cases hi : (i : ℕ) < n
  · rw [if_pos hi, dif_pos hi, if_pos (hN i hi), varL, ← hα ⟨i, hi⟩]
  · rw [if_neg hi, dif_neg hi, if_neg (by omega), Nat.add_sub_cancel_left, toL_unitPoly i.2]

/-- The positive exchange monomial of the seed `a` in direction `k` is represented by
`prodAtoms` of `posAtoms`. -/
theorem monomialPos_eq {m n N a k : ℕ} (hN : ∀ i < n, R.alpha a i < N)
    (α : Fin n → Fin N) (hα : ∀ i : Fin n, (α i : ℕ) = R.alpha a i) (kk : Fin n)
    (hk : (kk : ℕ) = k) :
    TypeE.monomialPos (TypeE.extTuple (fun c : Fin N => varL m R c) α)
        (Matrix.of fun (i : Fin m) (j : Fin n) => R.entry a i j) kk =
      Poly.toL m (R.prodAtoms m N (R.posAtoms m n N a k)) := by
  rw [toL_prodAtoms, posAtoms, prod_map_filterMap, TypeE.monomialPos, Finset.prod_filter,
    ← prod_range_eq_prod_map_range, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Matrix.of_apply, entry, nat_blt_eq_decide, Bool.cond_decide, hk]
  by_cases h : R.bias < R.matD a i k
  · rw [if_pos (by omega), if_pos h, Option.elim_some, toL_atom_atomOf hN α hα]
    congr 1
    omega
  · rw [if_neg (by omega), if_neg h]
    rfl

/-- The negative exchange monomial of the seed `a` in direction `k` is represented by
`prodAtoms` of `negAtoms`. -/
theorem monomialNeg_eq {m n N a k : ℕ} (hN : ∀ i < n, R.alpha a i < N)
    (α : Fin n → Fin N) (hα : ∀ i : Fin n, (α i : ℕ) = R.alpha a i) (kk : Fin n)
    (hk : (kk : ℕ) = k) :
    TypeE.monomialNeg (TypeE.extTuple (fun c : Fin N => varL m R c) α)
        (Matrix.of fun (i : Fin m) (j : Fin n) => R.entry a i j) kk =
      Poly.toL m (R.prodAtoms m N (R.negAtoms m n N a k)) := by
  rw [toL_prodAtoms, negAtoms, prod_map_filterMap, TypeE.monomialNeg, Finset.prod_filter,
    ← prod_range_eq_prod_map_range, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Matrix.of_apply, entry, nat_blt_eq_decide, Bool.cond_decide, hk]
  by_cases h : R.matD a i k < R.bias
  · rw [if_pos (by omega), if_pos h, Option.elim_some, toL_atom_atomOf hN α hα]
    congr 1
    omega
  · rw [if_neg (by omega), if_neg h]
    rfl

/-- If the codes of consecutive seeds increase, then codes increase strictly along all seeds below
`M`. -/
theorem code_lt_code {n N M : ℕ} (hlex : ∀ a, a + 1 < M → R.lexOK n N a = true) {a b : ℕ}
    (hab : a < b) (hb : b < M) : R.code n N a < R.code n N b := by
  induction b, hab using Nat.le_induction with
  | base => simpa [lexOK, nat_blt_eq_decide] using hlex a hb
  | succ b hab ih =>
    exact (ih (by omega)).trans (by simpa [lexOK, nat_blt_eq_decide] using hlex b hb)

/-- If the variables `v_c` are pairwise distinct, then `c ↦ v_c` is injective on `Fin N`. -/
theorem varL_injective {m N : ℕ}
    (hdist : ∀ c' < N, ∀ c < c', Poly.toL m (R.var c) ≠ Poly.toL m (R.var c')) :
    Function.Injective fun c : Fin N => varL m R c := by
  intro c c' h
  rcases lt_trichotomy (c : ℕ) c' with hlt | heq | hgt
  · exact absurd h (hdist c' c'.2 c hlt)
  · exact Fin.ext heq
  · exact absurd h.symm (hdist c c.2 c' hgt)

/-- If the codes of consecutive seeds increase, then seeds with the same cluster coincide. -/
theorem injective_range_of_lexOK {n N M : ℕ} (sv : Fin M → Fin n → Fin N)
    (hsv : ∀ a i, (sv a i : ℕ) = R.alpha a i) (hmono : ∀ a, StrictMono (sv a))
    (hlex : ∀ a, a + 1 < M → R.lexOK n N a = true) :
    Function.Injective fun a => Set.range (sv a) := by
  intro a b h
  have hf : sv a = sv b := ((hmono a).range_inj (hmono b)).1 h
  have hcode : R.code n N a = R.code n N b := by
    unfold code
    congr 1
    refine List.map_congr_left fun i hi => ?_
    exact (hsv a ⟨i, List.mem_range.1 hi⟩).symm.trans
      ((congrArg (fun f => ((f ⟨i, List.mem_range.1 hi⟩ : Fin N) : ℕ)) hf).trans (hsv b _))
  rcases lt_trichotomy (a : ℕ) b with hlt | heq | hgt
  · exact absurd hcode (code_lt_code hlex hlt b.2).ne
  · exact Fin.ext heq
  · exact absurd hcode.symm (code_lt_code hlex hgt a.2).ne

/-- If `treeOK` holds at all seeds below `M`, then every seed is reached from the seed `0` by a
sequence of transitions. -/
theorem exists_foldl_eq_of_treeOK {n M : ℕ} (hM : 0 < M) (nx : Fin M → Fin n → Fin M)
    (hnx : ∀ a k, (nx a k : ℕ) = R.next a k) (htree : ∀ a < M, R.treeOK n M a = true)
    (a : Fin M) : ∃ ks : List (Fin n), ks.foldl nx ⟨0, hM⟩ = a := by
  suffices ∀ d (a : ℕ) (ha : a < M), R.depth a = d →
      ∃ ks : List (Fin n), ks.foldl nx ⟨0, hM⟩ = ⟨a, ha⟩ from this _ a a.2 rfl
  intro d
  induction d with
  | zero =>
    intro a ha hd
    rcases eq_or_ne a 0 with rfl | h0a
    · exact ⟨[], rfl⟩
    · have := (treeOK_spec (htree a ha) h0a).2.2.2
      omega
  | succ d ih =>
    intro a ha hd
    rcases eq_or_ne a 0 with rfl | h0a
    · exact ⟨[], rfl⟩
    · obtain ⟨hp, hk, hnext, hdep⟩ := treeOK_spec (htree a ha) h0a
      obtain ⟨ks, hks⟩ := ih (R.parent a) hp (by omega)
      refine ⟨ks ++ [⟨R.parentDir a, hk⟩], ?_⟩
      rw [List.foldl_append, hks, List.foldl_cons, List.foldl_nil]
      exact Fin.ext ((hnx ⟨R.parent a, hp⟩ ⟨R.parentDir a, hk⟩).trans hnext)

/-- The extension of a permutation `σ` of `Fin n` agrees with `extIdx n π` when `σ` agrees
with `π`. -/
theorem val_extendMutable_eq_extIdx {m n : ℕ} (hmn : n ≤ m) {σ : Equiv.Perm (Fin n)}
    {π : ℕ → ℕ} (hσ : ∀ j : Fin n, (σ j : ℕ) = π j) (i : Fin m) :
    (σ.extendMutable hmn i : ℕ) = extIdx n π i := by
  simp only [extIdx, nat_blt_eq_decide, Bool.cond_decide]
  by_cases hi : (i : ℕ) < n
  · rw [Equiv.Perm.extendMutable_apply_of_lt hmn _ hi, if_pos hi, Fin.val_castLE, hσ]
  · rw [Equiv.Perm.extendMutable_apply_of_le hmn _ (by omega), if_neg hi]

/-- If `seedOK` and `transOK` hold at `(a, k)`, then the permutation `π(a, k)` is injective. -/
theorem injective_perm_of_transOK {m n N M numRel a k : ℕ} (hkn : k < n) (hmn : n ≤ m)
    (hbias : R.bias < 16) (hdig : ∀ a i j, R.matD a i j < 16) (hseed : R.seedOK n N a = true)
    (htrans : R.transOK m n N M numRel a k = true) {pf : Fin n → Fin n}
    (hpf : ∀ j, (pf j : ℕ) = R.perm a k j) : Function.Injective pf := by
  intro j j' h
  replace h : R.perm a k j = R.perm a k j' := by rw [← hpf, ← hpf, h]
  by_cases ha : a < R.next a k
  · have hT2 := (fwdOK_spec hkn hmn hbias hdig (fwdOK_of_transOK htrans ha)).2.2.1
    by_cases hj : (j : ℕ) = k <;> by_cases hj' : (j' : ℕ) = k
    · exact Fin.ext (hj.trans hj'.symm)
    · exact absurd (h.symm.trans (by rw [hj])) (hT2 j' j'.2 hj').2
    · exact absurd (h.trans (by rw [hj'])) (hT2 j j.2 hj).2
    · have smono : StrictMono fun i : Fin n => R.alpha a i :=
        fun i i' hii' => (seedOK_spec hseed).2 i i' hii' i'.2
      exact smono.injective ((hT2 j j.2 hj).1.symm.trans (h ▸ (hT2 j' j'.2 hj').1))
  · have hr := (revOK_spec (revOK_of_transOK htrans ha)).2.2.2.2
    have h1 := (hr j j.2).2
    rw [h] at h1
    exact Fin.ext (h1.symm.trans (hr j' j'.2).2)

/-- A forward transition `(a, k)` passing `fwdOK` mutates the matrix of `a` in direction `k` to
the matrix of `next a k` relabelled by `σ`. -/
theorem matrixMutation_eq_relabelMatrix_of_fwdOK {m n N M numRel a : ℕ} (hmn : n ≤ m)
    (hbias : R.bias < 16) (hdig : ∀ a i j, R.matD a i j < 16) (k : Fin n)
    (hfw : R.fwdOK m n N M numRel a k = true) {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ j : Fin n, (σ j : ℕ) = R.perm a k j) :
    matrixMutation hmn (Matrix.of fun (i : Fin m) (j : Fin n) => R.entry a i j) k =
      relabelMatrix hmn (Matrix.of fun (i : Fin m) (j : Fin n) => R.entry (R.next a k) i j) σ := by
  ext i j
  rw [relabelMatrix_apply]
  have key := mutOK_spec ((fwdOK_spec k.2 hmn hbias hdig hfw).2.2.2.1 i i.2 j j.2)
  change matrixMutation hmn _ k i j = R.entry (R.next a k)
    ((σ.extendMutable hmn i : Fin m) : ℕ) ((σ j : Fin n) : ℕ)
  rw [val_extendMutable_eq_extIdx hmn hσ i, hσ, entry, key]
  simp only [matrixMutation, Matrix.of_apply, entry, Fin.ext_iff, Fin.val_castLE]

/-- A forward transition `(a, k)` passing `fwdOK` satisfies the exchange relation of `a` in
direction `k`. -/
theorem exchange_of_fwdOK {m n N M numRel a : ℕ} (hmn : n ≤ m) (hbias : R.bias < 16)
    (hdig : ∀ a i j, R.matD a i j < 16) (hseed : R.seedOK n N a = true) (k : Fin n)
    (hfw : R.fwdOK m n N M numRel a k = true)
    (hrel : ∀ r < numRel, Poly.toL m (R.var (R.relX r)) * Poly.toL m (R.var (R.relY r)) =
      Poly.toL m (R.prodAtoms m N (R.relPos r)) + Poly.toL m (R.prodAtoms m N (R.relNeg r)))
    (hshape : ∀ r < numRel, R.relShapeOK r = true)
    (α : Fin n → Fin N) (hα : ∀ i : Fin n, (α i : ℕ) = R.alpha a i) :
    varL m R (R.alpha a k) * varL m R (R.alpha (R.next a k) (R.perm a k k)) =
      TypeE.monomialPos (TypeE.extTuple (fun c : Fin N => varL m R c) α)
          (Matrix.of fun (i : Fin m) (j : Fin n) => R.entry a i j) k +
        TypeE.monomialNeg (TypeE.extTuple (fun c : Fin N => varL m R c) α)
          (Matrix.of fun (i : Fin m) (j : Fin n) => R.entry a i j) k := by
  have hsd := seedOK_spec hseed
  rw [monomialPos_eq hsd.1 α hα k rfl, monomialNeg_eq hsd.1 α hα k rfl]
  obtain ⟨-, -, -, -, hr, hmatch⟩ := fwdOK_spec k.2 hmn hbias hdig hfw
  have hb : ∀ i < m, R.matD a i k < R.bias + 16 := fun i _ => by
    have := hdig a i k
    omega
  have hL := hrel _ hr
  rw [posKey_eq, negKey_eq] at hmatch
  obtain ⟨hxy, hpn⟩ := relMatchKey_spec (atomsGood_posAtoms hsd.1 hsd.2 hb)
    (atomsGood_negAtoms hsd.1 hsd.2 hbias) (hshape _ hr) hmatch
  change Poly.toL m (R.var (R.alpha a k)) *
    Poly.toL m (R.var (R.alpha (R.next a k) (R.perm a k k))) = _
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rcases hpn with ⟨hp, hn⟩ | ⟨hp, hn⟩ <;>
    rw [hx, hy, hp, hn] <;> linear_combination hL

/-- If `transOK` holds at `(a, k)` with `a < M`, then `ν(a, k) < M`. -/
theorem next_lt_of_transOK {m n N M numRel a k : ℕ} (hkn : k < n) (hmn : n ≤ m)
    (hbias : R.bias < 16) (hdig : ∀ a i j, R.matD a i j < 16) (haM : a < M)
    (htrans : R.transOK m n N M numRel a k = true) : R.next a k < M := by
  by_cases ha : a < R.next a k
  · exact (fwdOK_spec hkn hmn hbias hdig (fwdOK_of_transOK htrans ha)).1
  · exact (revOK_spec (revOK_of_transOK htrans ha)).1.trans haM

/-- If `transOK` holds at `(a, k)`, then `π(a, k)` maps `[0, n)` to itself. -/
theorem perm_lt_of_transOK {m n N M numRel a k : ℕ} (hkn : k < n) (hmn : n ≤ m)
    (hbias : R.bias < 16) (hdig : ∀ a i j, R.matD a i j < 16)
    (htrans : R.transOK m n N M numRel a k = true) : ∀ j < n, R.perm a k j < n := by
  by_cases ha : a < R.next a k
  · exact (fwdOK_spec hkn hmn hbias hdig (fwdOK_of_transOK htrans ha)).2.1
  · exact fun j hj => ((revOK_spec (revOK_of_transOK htrans ha)).2.2.2.2 j hj).1

/-- A reverse transition `(a, k)` passing `revOK` is the inverse of the forward transition
`(ν(a, k), π(a, k)(k))`, and the diagonal entry `(k, k)` of the matrix of `a` vanishes. -/
theorem inverse_of_revOK {m n M : ℕ} (hmn : n ≤ m) {nx : Fin M → Fin n → Fin M}
    {pm : Fin M → Fin n → Equiv.Perm (Fin n)} {sm : Fin M → Matrix (Fin m) (Fin n) ℤ}
    (hnx : ∀ a k, (nx a k : ℕ) = R.next a k) (hpm : ∀ a k j, (pm a k j : ℕ) = R.perm a k j)
    (hsm : ∀ a, sm a = Matrix.of fun (i : Fin m) (j : Fin n) => R.entry a i j)
    {a : Fin M} {k : Fin n} (hrv : R.revOK n a k = true) :
    (nx a k : ℕ) < R.next (nx a k) (pm a k k) ∧ nx (nx a k) (pm a k k) = a ∧
      pm (nx a k) (pm a k k) = (pm a k)⁻¹ ∧ sm a (Fin.castLE hmn k) k = 0 := by
  obtain ⟨h1, -, h3, h4, h5⟩ := revOK_spec hrv
  refine ⟨by simpa only [hnx, hpm, h3] using h1, Fin.ext (by simpa only [hnx, hpm] using h3),
    Equiv.ext fun x => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := (pm a k).surjective x
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    exact Fin.ext (by simpa only [hnx, hpm] using (h5 j j.2).2)
  · rw [hsm]
    simp only [Matrix.of_apply, entry, Fin.val_castLE, h4, sub_self]

/-- If every transition passes `transOK`, the seed data read off a raw certificate satisfy the
mutation (T1), cluster (T2) and exchange (T3) identities of an exchange certificate. -/
theorem exchange_identities_of_transOK {m n N M numRel : ℕ} (hmn : n ≤ m) (hbias : R.bias < 16)
    (hdig : ∀ a i j, R.matD a i j < 16) (hseed : ∀ a < M, R.seedOK n N a = true)
    (htrans : ∀ a < M, ∀ k < n, R.transOK m n N M numRel a k = true)
    (hrel : ∀ r < numRel, Poly.toL m (R.var (R.relX r)) * Poly.toL m (R.var (R.relY r)) =
      Poly.toL m (R.prodAtoms m N (R.relPos r)) + Poly.toL m (R.prodAtoms m N (R.relNeg r)))
    (hshape : ∀ r < numRel, R.relShapeOK r = true)
    {sv : Fin M → Fin n → Fin N} {nx : Fin M → Fin n → Fin M}
    {pm : Fin M → Fin n → Equiv.Perm (Fin n)} {sm : Fin M → Matrix (Fin m) (Fin n) ℤ}
    (hsv : ∀ a i, (sv a i : ℕ) = R.alpha a i) (hnx : ∀ a k, (nx a k : ℕ) = R.next a k)
    (hpm : ∀ a k j, (pm a k j : ℕ) = R.perm a k j)
    (hsm : ∀ a, sm a = Matrix.of fun (i : Fin m) (j : Fin n) => R.entry a i j) :
    (∀ a k, matrixMutation hmn (sm a) k = relabelMatrix hmn (sm (nx a k)) (pm a k)) ∧
      (∀ a k j, j ≠ k → sv (nx a k) (pm a k j) = sv a j) ∧
      ∀ a k, varL m R (sv a k) * varL m R (sv (nx a k) (pm a k k)) =
        TypeE.monomialPos (TypeE.extTuple (fun c : Fin N => varL m R c) (sv a)) (sm a) k +
          TypeE.monomialNeg (TypeE.extTuple (fun c : Fin N => varL m R c) (sv a)) (sm a) k := by
  have hfw : ∀ (a : Fin M) (k : Fin n), (a : ℕ) < R.next a k →
      R.fwdOK m n N M numRel a k = true :=
    fun a k ha => fwdOK_of_transOK (htrans a a.2 k k.2) ha
  have hrev := fun (a : Fin M) (k : Fin n) (ha : ¬(a : ℕ) < R.next a k) =>
    inverse_of_revOK hmn hnx hpm hsm (revOK_of_transOK (htrans a a.2 k k.2) ha)
  have hT1f : ∀ (a : Fin M) (k : Fin n), (a : ℕ) < R.next a k →
      matrixMutation hmn (sm a) k = relabelMatrix hmn (sm (nx a k)) (pm a k) := fun a k ha => by
    rw [hsm, hsm, hnx]
    exact matrixMutation_eq_relabelMatrix_of_fwdOK hmn hbias hdig k (hfw a k ha) (hpm a k)
  have hT2f : ∀ (a : Fin M) (k : Fin n), (a : ℕ) < R.next a k → ∀ j, j ≠ k →
      sv (nx a k) (pm a k j) = sv a j := fun a k ha j hjk => Fin.ext <| by
    simpa only [hsv, hnx, hpm] using
      ((fwdOK_spec k.2 hmn hbias hdig (hfw a k ha)).2.2.1 j j.2 fun h => hjk (Fin.ext h)).1
  have hT3f : ∀ (a : Fin M) (k : Fin n), (a : ℕ) < R.next a k →
      varL m R (sv a k) * varL m R (sv (nx a k) (pm a k k)) =
        TypeE.monomialPos (TypeE.extTuple (fun c : Fin N => varL m R c) (sv a)) (sm a) k +
          TypeE.monomialNeg (TypeE.extTuple (fun c : Fin N => varL m R c) (sv a)) (sm a) k :=
    fun a k ha => by
      rw [hsm]
      simp only [hsv, hnx, hpm]
      exact exchange_of_fwdOK hmn hbias hdig (hseed a a.2) k (hfw a k ha) hrel hshape (sv a) (hsv a)
  have hT1 : ∀ a k, matrixMutation hmn (sm a) k = relabelMatrix hmn (sm (nx a k)) (pm a k) := by
    intro a k
    by_cases ha : (a : ℕ) < R.next a k
    · exact hT1f a k ha
    obtain ⟨hbf, hb, hσ, -⟩ := hrev a k ha
    have e := hT1f _ _ hbf
    rw [hb, hσ] at e
    exact matrixMutation_eq_relabelMatrix_of_inv hmn e
  have hT2 : ∀ a k j, j ≠ k → sv (nx a k) (pm a k j) = sv a j := by
    intro a k j hjk
    by_cases ha : (a : ℕ) < R.next a k
    · exact hT2f a k ha j hjk
    obtain ⟨hbf, hb, hσ, -⟩ := hrev a k ha
    have := hT2f _ _ hbf (pm a k j) fun h => hjk ((pm a k).injective h)
    rw [hb, hσ, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at this
    exact this.symm
  refine ⟨hT1, hT2, fun a k => ?_⟩
  by_cases ha : (a : ℕ) < R.next a k
  · exact hT3f a k ha
  obtain ⟨hbf, hb, hσ, hkk⟩ := hrev a k ha
  have e := hT3f _ _ hbf
  rw [hb, hσ, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at e
  obtain ⟨hP, hN⟩ := monomial_relabel hmn (hT1 a k) hkk
    (extTuple_extendMutable_of_ne hmn (fun c : Fin N => varL m R c) (hT2 a k))
  rw [hP, hN] at e
  rw [mul_comm, e, add_comm]

/-- **Soundness of the checker.** If a raw certificate passes all checks, then there is an
exchange certificate for `B₀` with `N` variables and `M` seeds. -/
theorem nonempty_exchangeCertificate {m n N M numRel : ℕ} (hmn : n ≤ m)
    (B₀ : Matrix (Fin m) (Fin n) ℤ) (R : Raw) (hnN : n ≤ N) (hM : 0 < M)
    (hinit : R.initOK m n = true)
    (h0 : ∀ (i : Fin m) (j : Fin n), R.entry 0 i j = B₀ i j)
    (hbias : R.bias < 16) (hdig : ∀ a i j, R.matD a i j < 16)
    (hseed : ∀ a < M, R.seedOK n N a = true)
    (hlex : ∀ a, a + 1 < M → R.lexOK n N a = true)
    (htrans : ∀ a < M, ∀ k < n, R.transOK m n N M numRel a k = true)
    (hrel : ∀ r < numRel, Poly.toL m (R.var (R.relX r)) * Poly.toL m (R.var (R.relY r)) =
      Poly.toL m (R.prodAtoms m N (R.relPos r)) + Poly.toL m (R.prodAtoms m N (R.relNeg r)))
    (hshape : ∀ r < numRel, R.relShapeOK r = true)
    (hdist : ∀ c' < N, ∀ c < c', Poly.toL m (R.var c) ≠ Poly.toL m (R.var c'))
    (hcover : ∀ c < N, R.coverOK n M c = true)
    (htree : ∀ a < M, R.treeOK n M a = true) :
    Nonempty (ExchangeCertificate hmn B₀ N M) := by
  have hsd := fun (a : Fin M) => seedOK_spec (hseed a a.2)
  have hnM : ∀ (a : Fin M) (k : Fin n), R.next a k < M := fun a k =>
    next_lt_of_transOK k.2 hmn hbias hdig a.2 (htrans a a.2 k k.2)
  have hpn : ∀ (a : Fin M) (k : Fin n), ∀ j < n, R.perm a k j < n := fun a k =>
    perm_lt_of_transOK k.2 hmn hbias hdig (htrans a a.2 k k.2)
  let sv : Fin M → Fin n → Fin N := fun a i => ⟨R.alpha a i, (hsd a).1 i i.2⟩
  let nx : Fin M → Fin n → Fin M := fun a k => ⟨R.next a k, hnM a k⟩
  let pf : Fin M → Fin n → Fin n → Fin n := fun a k j => ⟨R.perm a k j, hpn a k j j.2⟩
  have smono : ∀ a, StrictMono (sv a) := fun a i j hij => (hsd a).2 i j hij j.2
  have pinj : ∀ a k, Function.Injective (pf a k) := fun a k =>
    injective_perm_of_transOK k.2 hmn hbias hdig (hseed a a.2) (htrans a a.2 k k.2) fun _ => rfl
  let pm : Fin M → Fin n → Equiv.Perm (Fin n) := fun a k =>
    Equiv.ofBijective (pf a k) (Finite.injective_iff_bijective.1 (pinj a k))
  let sm : Fin M → Matrix (Fin m) (Fin n) ℤ := fun a => Matrix.of fun i j => R.entry a i j
  obtain ⟨hT1, hT2, hT3⟩ := exchange_identities_of_transOK (sv := sv) (nx := nx) (pm := pm)
    (sm := sm) hmn hbias hdig hseed htrans hrel hshape (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) fun _ => rfl
  exact ⟨{
    le_card_var := hnN
    card_seed_pos := hM
    var := fun c => varL m R c
    var_castLE := fun i => by
      change Poly.toL m (R.var i) = _
      rw [(initOK_spec hinit i.2).2, toL_unitPoly (lt_of_lt_of_le i.2 hmn)]
      rfl
    seedVar := sv
    seedVar_injective := fun a => (smono a).injective
    seedMatrix := sm
    seedVar_zero := funext fun i => Fin.ext (initOK_spec hinit i.2).1
    seedMatrix_zero := Matrix.ext h0
    next := nx
    perm := pm
    matrixMutation_eq := hT1
    seedVar_next := hT2
    exchange := hT3
    var_injective := varL_injective hdist
    range_seedVar_injective := injective_range_of_lexOK sv (fun _ _ => rfl) smono hlex
    exists_mem_range_seedVar := fun c =>
      have ⟨hcM, i, hi, hc⟩ := coverOK_spec (hcover c c.2)
      ⟨⟨R.cover c, hcM⟩, ⟨i, hi⟩, Fin.ext hc⟩
    exists_foldl_next := exists_foldl_eq_of_treeOK hM nx (fun _ _ => rfl) htree }⟩

end Raw

end CertificateCheck

end ClusterAlgebras

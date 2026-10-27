/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.QuasiCartan.Basic

/-!
# A positive companion is admissible

A positive quasi-Cartan companion of a skew-symmetrizable matrix satisfies the sign condition on
every chordless cycle (Barot–Geiss–Zelevinsky, Proposition 1.4). Consequently a matrix whose
Cartan counterpart is of finite type has no chordless cycle and satisfies the
Barot–Geiss–Zelevinsky condition.

## Main results

* `ClusterAlgebras.IsPositiveQuasiCartan.satisfiesQCSignCondition`: a positive quasi-Cartan
  companion `A` of `B` satisfies the sign condition on every chordless cycle of `B`.
* `ClusterAlgebras.SkewSymmetrizable.satisfiesBGZ_of_isCartanFiniteType`: if the Cartan
  counterpart of `B` is of finite type, then `B` has no chordless cycle and satisfies the
  Barot–Geiss–Zelevinsky condition.

## Implementation notes

The finite-type statement is derived from positivity of the Cartan counterpart, so it does not
rely on the Cartan–Killing classification of Dynkin diagrams.

## References

* S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.11.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

/-! ### Auxiliary lemmas -/

/-- A product over `ℤ/p` is the product over `[0, p - 1]` along the natural cast. -/
private lemma prod_zmod_eq_prod_range {p : ℕ} [NeZero p] (σ : ZMod p → ℝ) :
    ∏ s, σ s = ∏ t ∈ Finset.range p, σ t := by
  refine Finset.prod_nbij' (fun s => s.val) (fun t => (t : ZMod p))
    (fun s _ => by simpa using ZMod.val_lt s) (by simp) (by simp) (fun t ht => ?_) (by simp)
  simp [ZMod.val_cast_of_lt (by simpa using ht : t < p)]

/-- A sign function `σ` on `ℤ/p` with `∏ₛ σₛ = 1` is a coboundary: there are signs `εₛ`
with `ε_{s+1} = σₛ εₛ` for every `s ∈ ℤ/p`. -/
private lemma exists_sign_coboundary {p : ℕ} [NeZero p] (σ : ZMod p → ℝ)
    (hσ : ∀ s, σ s ^ 2 = 1) (hprod : ∏ s, σ s = 1) :
    ∃ ε : ZMod p → ℝ, (∀ s, ε s ^ 2 = 1) ∧ ∀ s, ε (s + 1) = σ s * ε s := by
  refine ⟨fun s => ∏ t ∈ Finset.range s.val, σ t, fun s => ?_, fun s => ?_⟩
  · rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun t _ => hσ t
  · have hs := ZMod.val_lt s
    by_cases h : s.val + 1 < p
    · have h1 : (s + 1).val = s.val + 1 := by
        rw [ZMod.val_add_of_lt] <;> rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      simp only [h1, Finset.prod_range_succ, ZMod.natCast_zmod_val]
      ring
    · have h0 : s + 1 = 0 := by
        have : ((s.val + 1 : ℕ) : ZMod p) = 0 := by
          rw [show s.val + 1 = p by omega]
          exact ZMod.natCast_self p
        simpa using this
      have hsucc := Finset.prod_range_succ (fun t : ℕ => σ t) s.val
      rw [show s.val + 1 = p by omega, ← prod_zmod_eq_prod_range, hprod,
        ZMod.natCast_zmod_val] at hsucc
      simp only [h0, ZMod.val_zero, Finset.prod_range_zero]
      linarith

/-- The contribution of one edge to the quadratic form: if `(dᵢ a)² = dᵢ dⱼ a b`,
`a b ≥ 1` and `e = ±1` with `e a < 0`, then `e dᵢ a / √(dᵢ dⱼ) ≤ -1`. -/
private lemma edge_term_le {di dj a b : ℤ} {e : ℝ} (hdi : 0 < di) (hdj : 0 < dj)
    (hsq : (di * a) ^ 2 = di * dj * (a * b)) (hab : 1 ≤ a * b) (he : e ^ 2 = 1)
    (hneg : e * a < 0) :
    e * (di * a) / (√(di : ℝ) * √(dj : ℝ)) ≤ -1 := by
  have hdi' : (0 : ℝ) < di := by exact_mod_cast hdi
  have hdj' : (0 : ℝ) < dj := by exact_mod_cast hdj
  have hr : 0 < √(di : ℝ) * √(dj : ℝ) := by positivity
  have hsq' : ((di : ℝ) * a) ^ 2 = di * dj * (a * b) := by exact_mod_cast hsq
  have hab' : (1 : ℝ) ≤ a * b := by exact_mod_cast hab
  have hy : e * (di * a) < 0 := by
    rw [show e * (di * a) = di * (e * a) by ring]
    exact mul_neg_of_pos_of_neg hdi' hneg
  have hy2 : (√(di : ℝ) * √(dj : ℝ)) ^ 2 ≤ (e * (di * a)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hdi'.le, Real.sq_sqrt hdj'.le, mul_pow, he, one_mul, hsq']
    nlinarith [mul_pos hdi' hdj']
  rw [div_le_iff₀ hr]
  nlinarith

/-- Along a cycle `ℤ/p` with nonzero integer weights `c s`, an even number of them positive, there
are signs `ε` with `ε s ε (s + 1) c s < 0` for every `s`. -/
private lemma exists_sign_mul_neg {p : ℕ} [NeZero p] (c : ZMod p → ℤ) (hc0 : ∀ s, c s ≠ 0)
    (heven : Even (Finset.univ.filter fun s => 0 < c s).card) :
    ∃ ε : ZMod p → ℝ, (∀ s, ε s ^ 2 = 1) ∧ ∀ s, ε s * ε (s + 1) * (c s : ℝ) < 0 := by
  set σ : ZMod p → ℝ := fun s => if 0 < c s then -1 else 1 with hσdef
  have hσ2 : ∀ s, σ s ^ 2 = 1 := fun s => by
    simp only [hσdef]
    split_ifs <;> norm_num
  have hσc : ∀ s, σ s * (c s : ℝ) < 0 := by
    intro s
    simp only [hσdef]
    split_ifs with h
    · have : (0 : ℝ) < c s := by exact_mod_cast h
      linarith
    · have : (c s : ℝ) < 0 := by exact_mod_cast lt_of_le_of_ne (not_lt.1 h) (hc0 s)
      linarith
  have hprod : ∏ s, σ s = 1 := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one,
      heven.neg_one_pow]
  obtain ⟨ε, hε2, hεσ⟩ := exists_sign_coboundary σ hσ2 hprod
  refine ⟨ε, hε2, fun s => ?_⟩
  rw [show ε s * ε (s + 1) * (c s : ℝ) = ε s ^ 2 * (σ s * (c s : ℝ)) by rw [hεσ]; ring,
    hε2, one_mul]
  exact hσc s

/-- The quadratic form of `DA` at a vector supported on the image of an injective `v`, as a double
sum over the indices of `v`. -/
private lemma dotProduct_mulVec_eq_sum {A : Matrix (Fin n) (Fin n) ℤ} (d : Fin n → ℤ) {p : ℕ}
    [NeZero p] {v : ZMod p → Fin n} (hv : Function.Injective v) (g : ZMod p → ℝ)
    {x : Fin n → ℝ} (hxv : ∀ s, x (v s) = g s) (hxout : ∀ i ∉ Set.range v, x i = 0) :
    x ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ x) =
      ∑ s, ∑ t, g s * ((d (v s) : ℝ) * A (v s) (v t) * g t) := by
  simp only [dotProduct, mulVec, diagonal_mul, map_apply]
  refine (Fintype.sum_of_injective v hv _ _ (fun i hi => by rw [hxout i hi, zero_mul])
    fun s => ?_).symm
  rw [hxv, Finset.mul_sum]
  exact Fintype.sum_of_injective v hv _ _
    (fun i hi => by rw [hxout i hi, mul_zero, mul_zero]) fun t => by rw [hxv]

/-- The quadratic form of `DA` along a chordless cycle, at the vector `ε s / √(d (v s))` with
signs `ε` making every edge term negative, is nonpositive: each diagonal term is `2` and each
edge contributes at most `-2`. -/
private lemma sum_cycle_nonpos {A : Matrix (Fin n) (Fin n) ℤ} {d : Fin n → ℤ}
    (hd : IsSymmetrizer A d) (hdiag : ∀ i, A i i = 2) {p : ℕ} [NeZero p] {v : ZMod p → Fin n}
    (hne1 : ∀ s : ZMod p, s ≠ s + 1) (hne2 : ∀ s : ZMod p, s ≠ s - 1)
    (hne3 : ∀ s : ZMod p, s + 1 ≠ s - 1)
    (hzero : ∀ s t, t ≠ s → t ≠ s + 1 → t ≠ s - 1 → A (v s) (v t) = 0)
    (hc0 : ∀ s, A (v s) (v (s + 1)) ≠ 0) {ε : ZMod p → ℝ} (hε2 : ∀ s, ε s ^ 2 = 1)
    (hεc : ∀ s, ε s * ε (s + 1) * (A (v s) (v (s + 1)) : ℝ) < 0) :
    ∑ s, ∑ t, ε s / √(d (v s) : ℝ) * ((d (v s) : ℝ) * A (v s) (v t) *
      (ε t / √(d (v t) : ℝ))) ≤ 0 := by
  set g : ZMod p → ℝ := fun s => ε s / √(d (v s) : ℝ) with hgdef
  set q : ZMod p → ZMod p → ℝ := fun s t => g s * ((d (v s) : ℝ) * A (v s) (v t) * g t)
    with hqdef
  change ∑ s, ∑ t, q s t ≤ 0
  have hdpos : ∀ i, (0 : ℝ) < d i := fun i => by exact_mod_cast hd.1 i
  have hsplit : ∀ s, ∑ t, q s t = q s s + q s (s + 1) + q s (s - 1) := by
    intro s
    rw [← Finset.sum_subset (Finset.subset_univ {s, s + 1, s - 1}), Finset.sum_insert,
      Finset.sum_insert, Finset.sum_singleton, add_assoc]
    · simp only [Finset.mem_singleton]
      exact hne3 s
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne1 s, hne2 s⟩
    · intro t _ ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      simp only [hqdef, hzero s t ht.1 ht.2.1 ht.2.2, Int.cast_zero, mul_zero, zero_mul]
  have hshift : ∑ s, q s (s - 1) = ∑ s, q s (s + 1) := by
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod p))]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right, hqdef]
    have h' : (d (v (s + 1)) : ℝ) * A (v (s + 1)) (v s) = d (v s) * A (v s) (v (s + 1)) := by
      exact_mod_cast hd.2 (v (s + 1)) (v s)
    rw [h']
    ring
  have hqdiag : ∀ s, q s s = 2 := by
    intro s
    have hsd : √(d (v s) : ℝ) ^ 2 = d (v s) := Real.sq_sqrt (hdpos _).le
    have : q s s = 2 * d (v s) * (ε s ^ 2 / √(d (v s) : ℝ) ^ 2) := by
      simp only [hqdef, hgdef, hdiag]
      push_cast
      ring
    rw [this, hε2, hsd]
    field_simp [(hdpos (v s)).ne']
  have hqedge : ∀ s, q s (s + 1) ≤ -1 := by
    intro s
    have hsq := hd.sq_eq (v s) (v (s + 1))
    calc q s (s + 1) = ε s * ε (s + 1) * (d (v s) * A (v s) (v (s + 1))) /
        (√(d (v s) : ℝ) * √(d (v (s + 1)) : ℝ)) := by
          simp only [hqdef, hgdef]
          ring
      _ ≤ -1 := edge_term_le (hd.1 (v s)) (hd.1 (v (s + 1))) hsq.1 (hsq.2 (hc0 s))
          (show (ε s * ε (s + 1)) ^ 2 = 1 by rw [mul_pow, hε2, hε2, one_mul]) (hεc s)
  rw [Finset.sum_congr rfl fun s _ => hsplit s, Finset.sum_add_distrib, hshift,
    ← Finset.sum_add_distrib]
  refine Finset.sum_nonpos fun s _ => ?_
  linarith [hqdiag s, hqedge s]

/-! ### The sign condition -/

/-- **A positive companion is admissible**: a positive quasi-Cartan companion `A` of `B`
satisfies the sign condition on every chordless cycle of `B`. -/
@[cluster_algebras "lem_qc_positive_sign_condition"]
theorem IsPositiveQuasiCartan.satisfiesQCSignCondition {B A : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hA : IsQuasiCartanCompanion B A) (hpos : IsPositiveQuasiCartan A)
    {Z : Finset (Fin n)} (hZ : IsQCChordlessCycle B Z) : SatisfiesQCSignCondition B A Z := by
  obtain ⟨p, v, hv⟩ := hZ
  have hp : 3 ≤ p := hv.1
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨-, d, hd, hdef⟩ := hpos
  unfold SatisfiesQCSignCondition
  rw [hv.ncard_posEdges_eq hd]
  by_contra hodd
  have hne1 : ∀ s : ZMod p, s ≠ s + 1 := fun s => (hv.add_one_ne_self s).symm
  have hne2 : ∀ s : ZMod p, s ≠ s - 1 := fun s h =>
    hv.add_one_ne_self (s - 1) (by linear_combination h)
  have hne3 : ∀ s : ZMod p, s + 1 ≠ s - 1 := fun s h =>
    hv.add_one_add_one_ne_self (s - 1) (by linear_combination h)
  have hc0 : ∀ s, A (v s) (v (s + 1)) ≠ 0 := by
    intro s
    obtain ⟨hedge, -, hcomp⟩ := ((hB.isQCEdge_iff (v s) (v (s + 1))).2.2
      (hv.2.1.ne (hne1 s)))
    exact (hcomp A hA).2 (hedge.1 ((hv.2.2.2 s (s + 1) (hne1 s)).2 (Or.inl rfl)))
  have hzero : ∀ s t, t ≠ s → t ≠ s + 1 → t ≠ s - 1 → A (v s) (v t) = 0 := by
    intro s t hts ht1 ht2
    by_contra h
    obtain ⟨hedge, -, hcomp⟩ := ((hB.isQCEdge_iff (v s) (v t)).2.2 (hv.2.1.ne (Ne.symm hts)))
    exact ((hv.2.2.2 s t (Ne.symm hts)).1 (hedge.2 ((hcomp A hA).1 h))).elim ht1 ht2
  obtain ⟨ε, hε2, hεc⟩ :=
    exists_sign_mul_neg (fun s => A (v s) (v (s + 1))) hc0 (by simpa using hodd)
  set x : Fin n → ℝ := Function.extend v (fun s => ε s / √(d (v s) : ℝ)) 0
  have hxv : ∀ s, x (v s) = ε s / √(d (v s) : ℝ) := fun s => hv.2.1.extend_apply _ 0 s
  have hx0 : x ≠ 0 := by
    intro h
    have h0 := congrFun h (v 0)
    rw [hxv, Pi.zero_apply, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · simpa [h0] using hε2 0
    · exact (Real.sqrt_pos.2 (by exact_mod_cast hd.1 (v 0))).ne' h0
  have := hdef x hx0
  rw [dotProduct_mulVec_eq_sum d hv.2.1 _ hxv fun i hi =>
    Function.extend_apply' _ (0 : Fin n → ℝ) i hi] at this
  exact not_lt.2 (sum_cycle_nonpos hd hA.1.1 hne1 hne2 hne3 hzero hc0 hε2 hεc) this

/-- **A Cartan counterpart of finite type gives the condition**: if `A(B)` is a Cartan matrix of
finite type, then `B` has no chordless cycle and satisfies the Barot–Geiss–Zelevinsky
condition. -/
@[cluster_algebras "lem_qc_finite_type_counterpart"]
theorem SkewSymmetrizable.satisfiesBGZ_of_isCartanFiniteType {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hA : IsCartanFiniteType (cartanCounterpart B)) :
    (∀ Z, ¬IsQCChordlessCycle B Z) ∧ SatisfiesBGZ B := by
  obtain ⟨hcomp, hiff⟩ := hB.isQuasiCartanCompanion_cartanCounterpart
  have hpos := hiff.2 hA
  have hno : ∀ Z, ¬IsQCChordlessCycle B Z := by
    intro Z hZ
    have h := hpos.satisfiesQCSignCondition hB hcomp hZ
    unfold SatisfiesQCSignCondition at h
    have hempty : {e | e ∈ qcEdgesOf B Z ∧
        ∃ i j, e = s(i, j) ∧ 0 < cartanCounterpart B i j} = ∅ := by
      ext e
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
      intro he i j hij hpos'
      by_cases hij' : i = j
      · obtain ⟨i', j', he', hne, -⟩ := he.1
        rw [hij, hij'] at he'
        rcases Sym2.eq_iff.1 he' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hne (by rw [← h1, ← h2])
      · simp only [cartanCounterpart, of_apply, if_neg hij'] at hpos'
        linarith [abs_nonneg (B i j)]
    rw [hempty, Set.ncard_empty] at h
    exact Nat.not_odd_zero h
  exact ⟨hno, fun Z hZ => absurd hZ (hno Z), cartanCounterpart B, hcomp, hpos⟩

end ClusterAlgebras

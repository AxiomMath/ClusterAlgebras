/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Order.Ring.Units
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Subtraction-free expressions

Let `y = (y_s)_{s ∈ S}` be a family of elements of a commutative ring `A`. An element `w ∈ A` is
*subtraction-free in `y`* if `Q(y) w = P(y)` for nonzero polynomials `P, Q` with coefficients in
`ℕ` such that `Q(y) ≠ 0`; informally, `w` is a ratio of two polynomials in the `y_s` written
without subtraction.

Subtraction-free elements are stable under exchange relations `w v = a₁ a₂ + b₁ b₂`: if
`a₁, a₂, b₁, b₂, v` are subtraction-free and `v ≠ 0`, then so is `w`. A subtraction-free element
takes values in any additively closed subgroup `K₊` of the multiplicative group of a ring `K`
under every ring homomorphism `φ : A → K` sending each `y_s` into `K₊`; for `K₊` the positive
reals inside `ℝ` or `ℂ`, this says that `φ(w)` is positive whenever every `φ(y_s)` is.

## Main definitions

* `ClusterAlgebras.IsSubtractionFree y w`: the element `w` is subtraction-free in `y`.

## Main results

* `ClusterAlgebras.IsSubtractionFree.of_mul_eq_add`: subtraction-free elements are stable under
  exchange relations `w v = a₁ a₂ + b₁ b₂` with `v ≠ 0`.
* `ClusterAlgebras.IsSubtractionFree.exists_mem_coe_eq_map`: a subtraction-free element is sent
  into every additively closed subgroup `K₊ ≤ Kˣ` containing the images of the `y_s`.
* `ClusterAlgebras.IsSubtractionFree.pos`, `ClusterAlgebras.IsSubtractionFree.exists_pos_real`:
  the cases `K₊ = ℝ_{>0}` inside `ℝ` and inside `ℂ`.

## Implementation notes

* **No integral-domain or finiteness hypotheses in the definition.** `IsSubtractionFree` is
  defined for any commutative ring `A` and any index type `S`. The exchange lemma assumes
  `[IsDomain A]`; the positivity lemma assumes neither.

* **`P(y)` is `MvPolynomial.aeval y P`**, evaluation along the `ℕ`-algebra structure that every
  semiring carries.

* **The subgroup `K₊` and its additive closure.** `K₊` is a `Subgroup Kˣ` and closure under
  addition is phrased on the underlying elements: for `a, b ∈ K₊` there is `c ∈ K₊` with
  `c = a + b` in `K`. Membership of an element `x ∈ K` in `K₊` is `∃ u ∈ K₊, (u : K) = x`. The
  ring `K` need only be a commutative semiring.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapter 1*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial

variable {A : Type*} [CommRing A] {S : Type*}

/-- An element `w` of a commutative ring `A` is **subtraction-free** in a family `y = (y_s)` of
elements of `A` if there are nonzero polynomials `P, Q` with coefficients in `ℕ` such that
`Q(y) ≠ 0` and `Q(y) w = P(y)`, where `P(y)` is the evaluation `MvPolynomial.aeval y P` along the
`ℕ`-algebra structure of `A`. -/
@[cluster_algebras "def_subtraction_free"]
def IsSubtractionFree {A : Type*} [CommRing A] {S : Type*} (y : S → A) (w : A) : Prop :=
  ∃ P Q : MvPolynomial S ℕ, P ≠ 0 ∧ Q ≠ 0 ∧ MvPolynomial.aeval y Q ≠ 0 ∧
    MvPolynomial.aeval y Q * w = MvPolynomial.aeval y P

namespace IsSubtractionFree

/-- Each member `y_s` of the family is subtraction-free in `y`, with `P = Y_s` and `Q = 1`. -/
theorem self [Nontrivial A] (y : S → A) (s : S) : IsSubtractionFree y (y s) :=
  ⟨X s, 1, X_ne_zero s, one_ne_zero, by simp, by simp⟩

/-- The constant `1` is subtraction-free in any family, with `P = Q = 1`. -/
theorem one [Nontrivial A] (y : S → A) : IsSubtractionFree y 1 :=
  ⟨1, 1, one_ne_zero, one_ne_zero, by simp, by simp⟩

/-- In `ℕ[Y_S]` a sum vanishes only if its summands do. -/
private lemma eq_zero_of_add_eq_zero {p q : MvPolynomial S ℕ} (h : p + q = 0) : p = 0 := by
  ext m
  have := congrArg (coeff m) h
  simp only [coeff_add, coeff_zero] at this ⊢
  omega

/-- **Subtraction-free elements are stable under exchange relations.** If `a₁, a₂, b₁, b₂, v`
are subtraction-free in `y`, `v ≠ 0`, and `w v = a₁ a₂ + b₁ b₂`, then `w` is subtraction-free
in `y`. -/
@[cluster_algebras "lem_subtraction_free_exchange"]
theorem of_mul_eq_add [IsDomain A] {y : S → A} {a₁ a₂ b₁ b₂ v w : A}
    (ha₁ : IsSubtractionFree y a₁) (ha₂ : IsSubtractionFree y a₂) (hb₁ : IsSubtractionFree y b₁)
    (hb₂ : IsSubtractionFree y b₂) (hv : IsSubtractionFree y v) (hv0 : v ≠ 0)
    (h : w * v = a₁ * a₂ + b₁ * b₂) : IsSubtractionFree y w := by
  obtain ⟨P₁, Q₁, hP₁, hQ₁, hQ₁y, e₁⟩ := ha₁
  obtain ⟨P₂, Q₂, hP₂, hQ₂, hQ₂y, e₂⟩ := ha₂
  obtain ⟨P₃, Q₃, hP₃, hQ₃, hQ₃y, e₃⟩ := hb₁
  obtain ⟨P₄, Q₄, hP₄, hQ₄, hQ₄y, e₄⟩ := hb₂
  obtain ⟨Pv, Qv, hPv, hQv, hQvy, ev⟩ := hv
  have hPvy : aeval y Pv ≠ 0 := ev ▸ mul_ne_zero hQvy hv0
  refine ⟨(P₁ * P₂ * Q₃ * Q₄ + P₃ * P₄ * Q₁ * Q₂) * Qv, Q₁ * Q₂ * Q₃ * Q₄ * Pv,
    mul_ne_zero (fun h0 ↦ ?_) hQv, by simp [*], by simp [*], ?_⟩
  · simpa [hP₁, hP₂, hQ₃, hQ₄] using eq_zero_of_add_eq_zero h0
  · simp only [map_mul, map_add]
    rw [← e₁, ← e₂, ← e₃, ← e₄, ← ev]
    linear_combination (aeval y Q₁ * aeval y Q₂ * aeval y Q₃ * aeval y Q₄ * aeval y Qv) * h

/-- **Subtraction-free elements are positive.** Let `K₊` be a subgroup of the group of units of
a commutative semiring `K` which is closed under addition, and let `φ : A → K` be a ring
homomorphism sending every `y_s` into `K₊`. Then `φ` sends every element subtraction-free in `y`
into `K₊`. -/
@[cluster_algebras "lem_subtraction_free_positive"]
theorem exists_mem_coe_eq_map {K : Type*} [CommSemiring K] {y : S → A} {w : A}
    (hw : IsSubtractionFree y w) (Kp : Subgroup Kˣ)
    (hadd : ∀ a ∈ Kp, ∀ b ∈ Kp, ∃ c ∈ Kp, (c : K) = a + b) (φ : A →+* K)
    (hy : ∀ s, ∃ u ∈ Kp, (u : K) = φ (y s)) : ∃ u ∈ Kp, (u : K) = φ w := by
  set M : Submonoid K := Kp.toSubmonoid.map (Units.coeHom K)
  have hM (x : K) : x ∈ M ↔ ∃ u ∈ Kp, (u : K) = x := Submonoid.mem_map
  have hMadd {a b : K} (ha : a ∈ M) (hb : b ∈ M) : a + b ∈ M := by
    obtain ⟨u, hu, rfl⟩ := (hM a).1 ha
    obtain ⟨u', hu', rfl⟩ := (hM b).1 hb
    exact (hM _).2 (hadd u hu u' hu')
  have hMnat (n : ℕ) : ((n + 1 : ℕ) : K) ∈ M := by
    induction n with
    | zero => simp
    | succ n ih => simpa [Nat.cast_succ] using hMadd ih M.one_mem
  have hMsum {s : Finset (S →₀ ℕ)} (hs : s.Nonempty) {f : (S →₀ ℕ) → K}
      (hf : ∀ i ∈ s, f i ∈ M) : ∑ i ∈ s, f i ∈ M := by
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => simpa using hf a (by simp)
    | cons a s ha hs ih =>
      rw [Finset.sum_cons]
      exact hMadd (hf a (by simp)) (ih fun i hi ↦ hf i (by simp [hi]))
  have key (P : MvPolynomial S ℕ) (hP : P ≠ 0) : φ (aeval y P) ∈ M := by
    rw [show φ (aeval y P) = aeval (φ ∘ y) P from
      DFunLike.congr_fun (comp_aeval y φ.toNatAlgHom) P, aeval_eq_eval₂Hom, coe_eval₂Hom,
      eval₂_eq]
    refine hMsum (support_nonempty.2 hP) fun d hd ↦
      M.mul_mem ?_ (M.prod_mem fun i _ ↦ M.pow_mem ((hM _).2 (hy i)) _)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (mem_support_iff.1 hd)
    simpa [hn] using hMnat n
  obtain ⟨P, Q, hP, hQ, -, e⟩ := hw
  obtain ⟨uP, huP, huP'⟩ := (hM _).1 (key P hP)
  obtain ⟨uQ, huQ, huQ'⟩ := (hM _).1 (key Q hQ)
  refine ⟨uQ⁻¹ * uP, Kp.mul_mem (Kp.inv_mem huQ) huP, ?_⟩
  rw [Units.val_mul, Units.inv_mul_eq_iff_eq_mul, huP', huQ', ← map_mul, e]

/-- A subtraction-free element is positive under every ring homomorphism to `ℝ` that is positive
on the family `y`. -/
theorem pos {y : S → A} {w : A} (hw : IsSubtractionFree y w) (φ : A →+* ℝ)
    (hy : ∀ s, 0 < φ (y s)) : 0 < φ w := by
  obtain ⟨u, hu, e⟩ := hw.exists_mem_coe_eq_map (Units.posSubgroup ℝ)
    (fun a ha b hb ↦
      have hab := add_pos ((Units.mem_posSubgroup a).1 ha) ((Units.mem_posSubgroup b).1 hb)
      ⟨Units.mk0 _ hab.ne', (Units.mem_posSubgroup _).2 hab, rfl⟩) φ
    (fun s ↦ ⟨Units.mk0 _ (hy s).ne', (Units.mem_posSubgroup _).2 (hy s), rfl⟩)
  exact e ▸ (Units.mem_posSubgroup u).1 hu

/-- A subtraction-free element is sent to a positive real number by every ring homomorphism to
`ℂ` that sends each `y_s` to a positive real number. -/
theorem exists_pos_real {y : S → A} {w : A} (hw : IsSubtractionFree y w) (φ : A →+* ℂ)
    (hy : ∀ s, ∃ r : ℝ, 0 < r ∧ φ (y s) = r) : ∃ r : ℝ, 0 < r ∧ φ w = r := by
  let f : ℝˣ →* ℂˣ := Units.map Complex.ofRealHom.toMonoidHom
  have hf (x : ℝˣ) : ((f x : ℂˣ) : ℂ) = ((x : ℝ) : ℂ) := rfl
  have hadd : ∀ a ∈ (Units.posSubgroup ℝ).map f, ∀ b ∈ (Units.posSubgroup ℝ).map f,
      ∃ c ∈ (Units.posSubgroup ℝ).map f, (c : ℂ) = a + b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hab : 0 < (a : ℝ) + b :=
      add_pos ((Units.mem_posSubgroup a).1 ha) ((Units.mem_posSubgroup b).1 hb)
    exact ⟨f (Units.mk0 _ hab.ne'), ⟨_, (Units.mem_posSubgroup _).2 hab, rfl⟩, by simp [hf]⟩
  have hy' (s : S) : ∃ u ∈ (Units.posSubgroup ℝ).map f, (u : ℂ) = φ (y s) := by
    obtain ⟨r, hr, e⟩ := hy s
    exact ⟨f (Units.mk0 r hr.ne'), ⟨_, (Units.mem_posSubgroup _).2 hr, rfl⟩, by simp [hf, e]⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, e⟩ := hw.exists_mem_coe_eq_map _ hadd φ hy'
  exact ⟨x, (Units.mem_posSubgroup x).1 hx, by rw [← e, hf]⟩

end IsSubtractionFree

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.WithZero

/-!
# Semifields in the sense of Fomin–Zelevinsky

A *semifield* in the sense of Fomin and Zelevinsky is an abelian group `P`, written
multiplicatively, together with a commutative and associative *auxiliary addition* `⊕` over
which the multiplication distributes. Unlike a field it has no zero and no additive inverses;
the positive reals, the universal semifield of subtraction-free rational functions and the
tropical semifields are the basic examples. A semifield homomorphism preserves both
operations.

A polynomial `P = ∑ₐ cₐ Yᵃ` with coefficients in `ℕ` can be evaluated at a tuple `f` of
elements of a semifield `S` as soon as `P ≠ 0`: the value is the `⊕`-sum, over the exponent
vectors `a` with `cₐ > 0`, of `cₐ` copies of `fᵃ = ∏ᵢ fᵢ ^ aᵢ`. This evaluation turns sums of
nonzero polynomials into `⊕`-sums and products into products, and commutes with semifield
homomorphisms.

## Main definitions

* `ClusterAlgebras.FZSemifield`: a semifield in the sense of Fomin–Zelevinsky.
* `ClusterAlgebras.FZSemifieldHom`: a homomorphism of such semifields.
* `ClusterAlgebras.FZSemifield.polyValue`: the value `P(f)_S` of a polynomial with coefficients
  in `ℕ` at a tuple `f` of elements of a semifield `S`.

## Main results

* `ClusterAlgebras.FZSemifield.polyValue_add`, `ClusterAlgebras.FZSemifield.polyValue_mul`:
  evaluation of nonzero polynomials respects sums and products.
* `ClusterAlgebras.FZSemifield.map_polyValue`: a semifield homomorphism commutes with
  evaluation.

## Implementation notes

The auxiliary addition `⊕` is written `+`: the class extends `AddCommSemigroup`, and the
instance `FZSemifield.toDistrib` makes the distributive laws `add_mul` and `mul_add` available.
The name `FZSemifield` avoids Mathlib's `Semifield`, which is a commutative division semiring
and in particular has a zero.

FWZ only ask a homomorphism to preserve products and `⊕`-sums, so that is what the
structure `FZSemifieldHom` records; preservation of `1`, inverses and quotients is a theorem,
because the source of a homomorphism is a group.

FWZ evaluate polynomials in `m` variables; here the variables are indexed by an
arbitrary type `ι`. To evaluate, the semifield `S` is embedded in the commutative semiring
`WithZero S` obtained by adjoining an absorbing zero, in which a sum of `c` copies of an
element `x` is the scalar multiple `c • x`. The value of `P` in `WithZero S` is the sum over the
support of `P` of `P.coeff a • fᵃ`, which is `MvPolynomial.eval₂` along the canonical map
`ℕ → WithZero S`; it is nonzero when `P ≠ 0`, and `polyValue f P` is the element of `S` it comes
from. FWZ leave the value of the zero polynomial undefined; `polyValue f 0` is `1`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 1–3*][FWZ16]
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial

/-- A **semifield** in the sense of Fomin–Zelevinsky: an abelian group, written
multiplicatively, together with a commutative and associative *auxiliary addition* `⊕`,
written `+`, such that `(p ⊕ q) r = p r ⊕ q r`. There is no zero and there are no additive
inverses. -/
@[cluster_algebras "def_semifield"]
class FZSemifield (P : Type*) extends CommGroup P, AddCommSemigroup P where
  /-- Multiplication distributes over the auxiliary addition. -/
  protected add_mul (p q r : P) : (p + q) * r = p * r + q * r

namespace FZSemifield

variable {S : Type*} [FZSemifield S]

/-- The multiplication of a semifield distributes over its auxiliary addition on both sides. -/
instance (priority := 100) toDistrib : Distrib S where
  right_distrib := FZSemifield.add_mul
  left_distrib a b c := by rw [mul_comm, FZSemifield.add_mul, mul_comm, mul_comm c]

/-- Adjoining an absorbing zero to a semifield gives a commutative semiring. -/
instance instCommSemiringWithZero : CommSemiring (WithZero S) where
  __ : AddCommMonoid (WithZero S) := inferInstance
  __ : CommMonoidWithZero (WithZero S) := inferInstance
  left_distrib := left_distrib
  right_distrib := right_distrib

/-- In `WithZero S` a sum with a nonzero summand is nonzero: `S` is closed under `⊕`. -/
theorem withZero_add_ne_zero {x y : WithZero S} (hx : x ≠ 0) : x + y ≠ 0 := by
  induction x <;> induction y <;> simp_all [← WithZero.coe_add]

/-- In `WithZero S` a positive multiple of an element of `S` is nonzero. -/
theorem withZero_nsmul_coe_ne_zero {n : ℕ} (hn : n ≠ 0) (x : S) :
    n • (x : WithZero S) ≠ 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [succ_nsmul, add_comm]
  exact withZero_add_ne_zero WithZero.coe_ne_zero

end FZSemifield

/-- A **homomorphism of semifields** `P → P'`: a map preserving products and the auxiliary
addition. It then also preserves `1`, inverses and quotients, since `P` is a group; see
`FZSemifieldHom.toMonoidHom`. -/
@[cluster_algebras "def_semifield_hom"]
structure FZSemifieldHom (P P' : Type*) [FZSemifield P] [FZSemifield P'] extends
    P →ₙ* P', P →ₙ+ P'

/-- The underlying additive map of a semifield homomorphism: it preserves the auxiliary
addition. -/
add_decl_doc FZSemifieldHom.toAddHom

namespace FZSemifieldHom

variable {P P' P'' : Type*} [FZSemifield P] [FZSemifield P'] [FZSemifield P'']

/-- A semifield homomorphism is a function. -/
instance instFunLike : FunLike (FZSemifieldHom P P') P P' where
  coe φ := φ.toFun
  coe_injective φ ψ h := by
    obtain ⟨⟨_, _⟩, _⟩ := φ
    obtain ⟨⟨_, _⟩, _⟩ := ψ
    congr

/-- A semifield homomorphism preserves products. -/
instance instMulHomClass : MulHomClass (FZSemifieldHom P P') P P' where
  map_mul φ := φ.map_mul'

/-- A semifield homomorphism preserves the auxiliary addition. -/
instance instAddHomClass : AddHomClass (FZSemifieldHom P P') P P' where
  map_add φ := φ.map_add'

/-- A semifield homomorphism preserves `1`. -/
protected theorem map_one (φ : FZSemifieldHom P P') : φ 1 = 1 :=
  mul_eq_left.1 (by rw [← map_mul, one_mul])

/-- A semifield homomorphism is a monoid homomorphism. -/
instance instMonoidHomClass : MonoidHomClass (FZSemifieldHom P P') P P' where
  map_one := FZSemifieldHom.map_one

/-- The underlying monoid homomorphism of a semifield homomorphism. -/
def toMonoidHom (φ : FZSemifieldHom P P') : P →* P' :=
  MonoidHomClass.toMonoidHom φ

/-- The underlying function of `φ.toMonoidHom` is `φ`. -/
@[simp]
theorem coe_toMonoidHom (φ : FZSemifieldHom P P') : ⇑φ.toMonoidHom = φ :=
  rfl

/-- The underlying function of `φ.toMulHom` is `φ`. -/
@[simp]
theorem coe_toMulHom (φ : FZSemifieldHom P P') : ⇑φ.toMulHom = φ :=
  rfl

/-- The underlying function of `φ.toAddHom` is `φ`. -/
@[simp]
theorem coe_toAddHom (φ : FZSemifieldHom P P') : ⇑φ.toAddHom = φ :=
  rfl

/-- The semifield homomorphism built from a multiplicative map preserving `⊕` is that map. -/
@[simp]
theorem coe_mk (φ : P →ₙ* P') (h : ∀ x y, φ.toFun (x + y) = φ.toFun x + φ.toFun y) :
    ⇑(⟨φ, h⟩ : FZSemifieldHom P P') = φ :=
  rfl

/-- Two semifield homomorphisms agreeing at every point are equal. -/
@[ext]
theorem ext {φ ψ : FZSemifieldHom P P'} (h : ∀ x, φ x = ψ x) : φ = ψ :=
  DFunLike.ext _ _ h

variable (P) in
/-- The identity homomorphism of a semifield. -/
protected def id : FZSemifieldHom P P where
  toFun := id
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The identity homomorphism is the identity function. -/
@[simp]
theorem coe_id : ⇑(FZSemifieldHom.id P) = id :=
  rfl

/-- The composite of two semifield homomorphisms. -/
def comp (ψ : FZSemifieldHom P' P'') (φ : FZSemifieldHom P P') : FZSemifieldHom P P'' where
  toFun := ψ ∘ φ
  map_mul' x y := by simp
  map_add' x y := by simp

/-- The composite homomorphism is the composite function. -/
@[simp]
theorem coe_comp (ψ : FZSemifieldHom P' P'') (φ : FZSemifieldHom P P') :
    ⇑(ψ.comp φ) = ψ ∘ φ :=
  rfl

/-- A semifield homomorphism `φ : P → P'` extends to the ring homomorphism
`WithZero P →+* WithZero P'` sending `0` to `0`. -/
def withZeroMap (φ : FZSemifieldHom P P') : WithZero P →+* WithZero P' where
  __ := WithZero.map' φ.toMonoidHom
  map_add' x y := by
    induction x <;> induction y <;> simp [← WithZero.coe_add]

/-- `φ.withZeroMap` extends `φ`. -/
@[simp]
theorem withZeroMap_coe (φ : FZSemifieldHom P P') (x : P) : φ.withZeroMap x = φ x :=
  rfl

end FZSemifieldHom

namespace FZSemifield

variable {S S' ι : Type*} [FZSemifield S] [FZSemifield S']

/-- The value of `P ∈ ℕ[Y]` at `f` in the commutative semiring `WithZero S`: the sum over the
support of `P` of `P.coeff a` copies of `fᵃ = ∏ᵢ fᵢ ^ aᵢ`. -/
noncomputable def polyValueWithZero (f : ι → S) (P : MvPolynomial ι ℕ) : WithZero S :=
  ∑ a ∈ P.support, P.coeff a • ((a.prod fun i k => f i ^ k : S) : WithZero S)

/-- The value computed in `WithZero S` is the evaluation `eval₂` of `P` at the image of `f`. -/
theorem polyValueWithZero_eq_eval₂ (f : ι → S) (P : MvPolynomial ι ℕ) :
    polyValueWithZero f P =
      eval₂ (Nat.castRingHom (WithZero S)) (fun i => (f i : WithZero S)) P := by
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only
  rw [nsmul_eq_mul, Finsupp.prod, Finsupp.prod, ← WithZero.coeMonoidHom_apply, map_prod]
  simp only [WithZero.coeMonoidHom_apply, WithZero.coe_pow, eq_natCast]
  rfl

/-- The value in `WithZero S` of a nonzero polynomial is nonzero. -/
theorem polyValueWithZero_ne_zero (f : ι → S) {P : MvPolynomial ι ℕ} (hP : P ≠ 0) :
    polyValueWithZero f P ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := support_nonempty.2 hP
  rw [polyValueWithZero, ← Finset.add_sum_erase _ _ ha]
  exact withZero_add_ne_zero (withZero_nsmul_coe_ne_zero (mem_support_iff.1 ha) _)

/-- The **value** `P(f)_S` of a polynomial `P` with coefficients in `ℕ` at a tuple `f` of
elements of a semifield `S`: for `P ≠ 0`, the `⊕`-sum, over the exponent vectors `a` in the
support of `P`, of `P.coeff a` copies of `fᵃ = ∏ᵢ fᵢ ^ aᵢ`. The sum is formed in `WithZero S`
(see `polyValueWithZero`), where it is nonzero, and `polyValue f P` is the element of `S` it
comes from. The value of the zero polynomial, left undefined by FWZ, is `1`. -/
@[cluster_algebras "def_semifield_polynomial_value"]
noncomputable def polyValue (f : ι → S) (P : MvPolynomial ι ℕ) : S :=
  haveI := Classical.propDecidable (polyValueWithZero f P = 0)
  if h : polyValueWithZero f P = 0 then 1 else WithZero.unzero h

/-- For `P ≠ 0`, the value `polyValue f P` is the value computed in `WithZero S`. -/
theorem coe_polyValue (f : ι → S) {P : MvPolynomial ι ℕ} (hP : P ≠ 0) :
    (↑(polyValue f P) : WithZero S) = polyValueWithZero f P := by
  rw [polyValue, dif_neg (polyValueWithZero_ne_zero f hP), WithZero.coe_unzero]

/-- For `P ≠ 0`, the value `polyValue f P`, seen in `WithZero S`, is the evaluation
`eval₂` of `P` at the image of `f`. -/
theorem coe_polyValue_eq_eval₂ (f : ι → S) {P : MvPolynomial ι ℕ} (hP : P ≠ 0) :
    (↑(polyValue f P) : WithZero S) =
      eval₂ (Nat.castRingHom (WithZero S)) (fun i => (f i : WithZero S)) P := by
  rw [coe_polyValue f hP, polyValueWithZero_eq_eval₂]

/-- The junk value of the zero polynomial is `1`. -/
@[simp]
theorem polyValue_zero (f : ι → S) : polyValue f 0 = 1 := by
  simp [polyValue, polyValueWithZero]

/-- The value of a sum of nonzero polynomials is the `⊕`-sum of their values. -/
@[cluster_algebras "lem_semifield_polynomial_value_hom"]
theorem polyValue_add (f : ι → S) {P Q : MvPolynomial ι ℕ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    polyValue f (P + Q) = polyValue f P + polyValue f Q := by
  have hPQ : P + Q ≠ 0 := by
    obtain ⟨a, ha⟩ := support_nonempty.2 hP
    refine ne_zero_iff.2 ⟨a, ?_⟩
    have := mem_support_iff.1 ha
    rw [coeff_add]
    omega
  apply WithZero.coe_injective
  simp only [WithZero.coe_add, coe_polyValue_eq_eval₂ f hP, coe_polyValue_eq_eval₂ f hQ,
    coe_polyValue_eq_eval₂ f hPQ, eval₂_add]

/-- The value of a product of nonzero polynomials is the product of their values. -/
@[cluster_algebras "lem_semifield_polynomial_value_hom"]
theorem polyValue_mul (f : ι → S) {P Q : MvPolynomial ι ℕ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    polyValue f (P * Q) = polyValue f P * polyValue f Q := by
  have hPQ : P * Q ≠ 0 := mul_ne_zero hP hQ
  apply WithZero.coe_injective
  simp only [WithZero.coe_mul, coe_polyValue_eq_eval₂ f hP, coe_polyValue_eq_eval₂ f hQ,
    coe_polyValue_eq_eval₂ f hPQ, eval₂_mul]

/-- The value of the nonzero monomial `c Yᵃ` is the sum of `c` copies of `fᵃ`, computed in
`WithZero S`. -/
theorem coe_polyValue_monomial (f : ι → S) (a : ι →₀ ℕ) {c : ℕ} (hc : c ≠ 0) :
    (↑(polyValue f (monomial a c)) : WithZero S) =
      c • ((a.prod fun i k => f i ^ k : S) : WithZero S) := by
  classical
  rw [coe_polyValue f (by simpa using hc), polyValueWithZero, support_monomial, if_neg hc,
    Finset.sum_singleton, coeff_monomial, if_pos rfl]

/-- The value of the monomial `Yᵃ` is `fᵃ = ∏ᵢ fᵢ ^ aᵢ`. -/
@[simp]
theorem polyValue_monomial_one (f : ι → S) (a : ι →₀ ℕ) :
    polyValue f (monomial a 1) = a.prod fun i k => f i ^ k := by
  apply WithZero.coe_injective
  rw [coe_polyValue_monomial f a one_ne_zero, one_smul]

/-- The value of the variable `Yᵢ` is `fᵢ`. -/
@[simp]
theorem polyValue_X (f : ι → S) (i : ι) : polyValue f (X i) = f i := by
  simp [X]

/-- The value of the constant polynomial `1` is `1`. -/
@[simp]
theorem polyValue_one (f : ι → S) : polyValue f 1 = 1 := by
  simpa using polyValue_monomial_one f 0

/-- The value of a positive constant `c`, computed in `WithZero S`, is `c`, the sum of `c`
copies of `1`. -/
theorem coe_polyValue_C (f : ι → S) {c : ℕ} (hc : c ≠ 0) :
    (↑(polyValue f (C c)) : WithZero S) = c := by
  rw [coe_polyValue_eq_eval₂ f (by rwa [Ne, C_eq_zero]), eval₂_C, eq_natCast]

/-- A semifield homomorphism commutes with the evaluation of nonzero polynomials. -/
theorem map_polyValue (φ : FZSemifieldHom S S') (f : ι → S) {P : MvPolynomial ι ℕ}
    (hP : P ≠ 0) : φ (polyValue f P) = polyValue (φ ∘ f) P := by
  apply WithZero.coe_injective
  rw [← FZSemifieldHom.withZeroMap_coe, coe_polyValue_eq_eval₂ f hP,
    coe_polyValue_eq_eval₂ _ hP, eval₂_comp_left,
    Subsingleton.elim (φ.withZeroMap.comp _) (Nat.castRingHom _)]
  rfl

end FZSemifield

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Semifield.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# The universal semifield

Let `F` be a field and `y = (yᵢ)` a family of elements of `F`. The *universal semifield*
`ℚ_sf(y)` is the set of `z ∈ F` for which there are nonzero polynomials `P, Q` with
coefficients in `ℕ` such that `Q(y) z = P(y)`: the values at `y` of the subtraction-free
rational functions.

The set contains `1` and every `yᵢ`, and is closed under the product, the sum and the inverse
of `F`. When `F` has characteristic zero and `y` is algebraically independent over `ℚ`, no
nonzero polynomial with coefficients in `ℕ` vanishes at `y`; then `0 ∉ ℚ_sf(y)`, and with the
multiplication of `F` and with `⊕` the addition of `F`, `ℚ_sf(y)` is a semifield.

It is the free semifield on `y`: for every semifield `S` and every family `f` of elements of
`S` there is exactly one semifield homomorphism `φ : ℚ_sf(y) → S` with `φ(yᵢ) = fᵢ`, namely
`φ(z) = P(f)_S / Q(f)_S` whenever `Q(y) z = P(y)`. It is well defined because two
representations `P / Q` and `P' / Q'` of `z` satisfy `P Q' = P' Q` as polynomials, by
algebraic independence.

## Main definitions

* `ClusterAlgebras.universalSemifield`: the universal semifield `ℚ_sf(y)`, as a subset of `F`.
* `ClusterAlgebras.instFZSemifieldUniversalSemifield`: its semifield structure.
* `ClusterAlgebras.universalSemifieldLift`: the semifield homomorphism `ℚ_sf(y) → S` sending
  `yᵢ` to `fᵢ`.

## Main results

* `ClusterAlgebras.zero_notMem_universalSemifield`, `ClusterAlgebras.mem_universalSemifield_self`:
  `0 ∉ ℚ_sf(y)` and `yᵢ ∈ ℚ_sf(y)`.
* `ClusterAlgebras.universalSemifield.exists_hom`: existence in the universal property.
* `ClusterAlgebras.universalSemifield.hom_ext`: uniqueness in the universal property.

## Implementation notes

FWZ index the family by `[1, m]`; here it is indexed by an arbitrary type `ι`.
FWZ assume throughout that `F` has characteristic zero and that `y` is algebraically
independent over `ℚ`. Neither hypothesis is needed to define the set, nor for the closure of the
set under products, sums and inverses, so those carry no hypothesis; the hypotheses are
assumed where they are used, that is, for `0 ∉ ℚ_sf(y)`, for the semifield structure and for
the universal property.

The operations `*`, `+`, `⁻¹`, `/`, `1` and the powers of `ℚ_sf(y)` are defined on the subtype
unconditionally, as the restrictions of those of `F`, so that their coercions to `F` are true by
definition. The semifield structure needs `0 ∉ ℚ_sf(y)` for `z z⁻¹ = 1`; since an instance
cannot take a hypothesis as an argument, it assumes `Fact (AlgebraicIndependent ℚ y)`.

FWZ define `ℚ_sf(y)` by subtraction-free expressions with positive rational
coefficients; clearing the denominators of the coefficients shows that this is the same set.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 1–3*][FWZ16]
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial FZSemifield

variable {F ι : Type*} [Field F] {y : ι → F}

/-- The **universal semifield** `ℚ_sf(y)` of a family `y` of elements of a field `F`: the set
of `z ∈ F` for which there are nonzero polynomials `P, Q` with coefficients in `ℕ` such that
`Q(y) z = P(y)`. FWZ take `F` of characteristic zero and `y` algebraically independent
over `ℚ`; neither is needed to define the set, so they are assumed only by the results that
use them. -/
@[cluster_algebras "def_universal_semifield"]
def universalSemifield (y : ι → F) : Set F :=
  {z | ∃ P Q : MvPolynomial ι ℕ, P ≠ 0 ∧ Q ≠ 0 ∧ aeval y Q * z = aeval y P}

/-- Membership in `ℚ_sf(y)`: `z = P(y) / Q(y)` for nonzero `P, Q` with coefficients in `ℕ`. -/
theorem mem_universalSemifield {z : F} :
    z ∈ universalSemifield y ↔
      ∃ P Q : MvPolynomial ι ℕ, P ≠ 0 ∧ Q ≠ 0 ∧ aeval y Q * z = aeval y P :=
  Iff.rfl

/-! ### Closure properties -/

/-- A sum of polynomials with coefficients in `ℕ` with a nonzero summand is nonzero: there is
no cancellation. -/
private theorem add_ne_zero_of_left {P Q : MvPolynomial ι ℕ} (hP : P ≠ 0) : P + Q ≠ 0 := by
  obtain ⟨a, ha⟩ := ne_zero_iff.1 hP
  exact ne_zero_iff.2 ⟨a, by rw [coeff_add]; omega⟩

variable (y) in
/-- The value at `y` of a nonzero polynomial with coefficients in `ℕ` lies in `ℚ_sf(y)`. -/
theorem aeval_mem_universalSemifield {P : MvPolynomial ι ℕ} (hP : P ≠ 0) :
    aeval y P ∈ universalSemifield y :=
  ⟨P, 1, hP, one_ne_zero, by simp⟩

variable (y) in
/-- Each entry `yᵢ` of `y` lies in `ℚ_sf(y)`. -/
@[cluster_algebras "lem_universal_semifield_is_semifield"]
theorem mem_universalSemifield_self (i : ι) : y i ∈ universalSemifield y := by
  simpa using aeval_mem_universalSemifield y (X_ne_zero (R := ℕ) i)

/-- `1 ∈ ℚ_sf(y)`. -/
theorem one_mem_universalSemifield : (1 : F) ∈ universalSemifield y := by
  simpa using aeval_mem_universalSemifield y (one_ne_zero (α := MvPolynomial ι ℕ))

/-- `ℚ_sf(y)` is closed under the product of `F`. -/
theorem mul_mem_universalSemifield {z w : F} (hz : z ∈ universalSemifield y)
    (hw : w ∈ universalSemifield y) : z * w ∈ universalSemifield y := by
  obtain ⟨P, Q, hP, hQ, h⟩ := hz
  obtain ⟨P', Q', hP', hQ', h'⟩ := hw
  refine ⟨P * P', Q * Q', mul_ne_zero hP hP', mul_ne_zero hQ hQ', ?_⟩
  rw [map_mul, map_mul, ← h, ← h']
  ring

/-- `ℚ_sf(y)` is closed under the addition of `F`. -/
theorem add_mem_universalSemifield {z w : F} (hz : z ∈ universalSemifield y)
    (hw : w ∈ universalSemifield y) : z + w ∈ universalSemifield y := by
  obtain ⟨P, Q, hP, hQ, h⟩ := hz
  obtain ⟨P', Q', hP', hQ', h'⟩ := hw
  refine ⟨P * Q' + P' * Q, Q * Q', add_ne_zero_of_left (mul_ne_zero hP hQ'),
    mul_ne_zero hQ hQ', ?_⟩
  rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
  ring

/-- `ℚ_sf(y)` is closed under the inverse of `F`. This needs no hypothesis on `y`: if
`0 ∈ ℚ_sf(y)` then `0⁻¹ = 0` lies in it. -/
theorem inv_mem_universalSemifield {z : F} (hz : z ∈ universalSemifield y) :
    z⁻¹ ∈ universalSemifield y := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simpa using hz
  obtain ⟨P, Q, hP, hQ, h⟩ := hz
  exact ⟨Q, P, hQ, hP, by rw [← h, mul_inv_cancel_right₀ hz0]⟩

/-- `ℚ_sf(y)` is closed under the quotient of `F`. -/
theorem div_mem_universalSemifield {z w : F} (hz : z ∈ universalSemifield y)
    (hw : w ∈ universalSemifield y) : z / w ∈ universalSemifield y := by
  rw [div_eq_mul_inv]
  exact mul_mem_universalSemifield hz (inv_mem_universalSemifield hw)

/-- `ℚ_sf(y)` is closed under natural powers. -/
theorem pow_mem_universalSemifield {z : F} (hz : z ∈ universalSemifield y) (n : ℕ) :
    z ^ n ∈ universalSemifield y := by
  induction n with
  | zero => simpa using one_mem_universalSemifield
  | succ n ih => simpa [pow_succ] using mul_mem_universalSemifield ih hz

/-- `ℚ_sf(y)` is closed under integer powers. -/
theorem zpow_mem_universalSemifield {z : F} (hz : z ∈ universalSemifield y) (n : ℤ) :
    z ^ n ∈ universalSemifield y := by
  cases n with
  | ofNat n => simpa using pow_mem_universalSemifield hz n
  | negSucc n => simpa using inv_mem_universalSemifield (pow_mem_universalSemifield hz (n + 1))

/-! ### Algebraic independence and nonvanishing -/

/-- If `F` has characteristic zero and `y` is algebraically independent over `ℚ`, then
evaluation at `y` is injective on polynomials with coefficients in `ℕ`. -/
theorem aeval_nat_injective [CharZero F] (hy : AlgebraicIndependent ℚ y) :
    Function.Injective (aeval y : MvPolynomial ι ℕ →ₐ[ℕ] F) := by
  intro P Q h
  apply map_injective (algebraMap ℕ ℚ) Nat.cast_injective
  apply algebraicIndependent_iff_injective_aeval.1 hy
  simpa [aeval_map_algebraMap] using h

/-- If `F` has characteristic zero and `y` is algebraically independent over `ℚ`, then no
nonzero polynomial with coefficients in `ℕ` vanishes at `y`. -/
theorem aeval_nat_ne_zero [CharZero F] (hy : AlgebraicIndependent ℚ y) {P : MvPolynomial ι ℕ}
    (hP : P ≠ 0) : aeval y P ≠ 0 :=
  (map_ne_zero_iff _ (aeval_nat_injective hy)).2 hP

/-- `0 ∉ ℚ_sf(y)` exactly when no nonzero polynomial with coefficients in `ℕ` vanishes at `y`. -/
theorem zero_notMem_universalSemifield_iff :
    0 ∉ universalSemifield y ↔ ∀ P : MvPolynomial ι ℕ, P ≠ 0 → aeval y P ≠ 0 := by
  refine ⟨fun h P hP hP0 => h ⟨P, 1, hP, one_ne_zero, by simp [hP0]⟩, ?_⟩
  rintro h ⟨P, Q, hP, -, hPQ⟩
  exact h P hP (by simpa using hPQ.symm)

/-- If `F` has characteristic zero and `y` is algebraically independent over `ℚ`, then
`0 ∉ ℚ_sf(y)`. -/
@[cluster_algebras "lem_universal_semifield_is_semifield"]
theorem zero_notMem_universalSemifield [CharZero F] (hy : AlgebraicIndependent ℚ y) :
    0 ∉ universalSemifield y :=
  zero_notMem_universalSemifield_iff.2 fun _ => aeval_nat_ne_zero hy

/-! ### The operations -/

/-- The product of `ℚ_sf(y)`, that of `F`. -/
instance instMulUniversalSemifield : Mul (universalSemifield y) :=
  ⟨fun a b => ⟨a * b, mul_mem_universalSemifield a.2 b.2⟩⟩

/-- The unit of `ℚ_sf(y)`, that of `F`. -/
instance instOneUniversalSemifield : One (universalSemifield y) :=
  ⟨⟨1, one_mem_universalSemifield⟩⟩

/-- The inverse of `ℚ_sf(y)`, that of `F`. -/
instance instInvUniversalSemifield : Inv (universalSemifield y) :=
  ⟨fun a => ⟨a⁻¹, inv_mem_universalSemifield a.2⟩⟩

/-- The quotient of `ℚ_sf(y)`, that of `F`. -/
instance instDivUniversalSemifield : Div (universalSemifield y) :=
  ⟨fun a b => ⟨a / b, div_mem_universalSemifield a.2 b.2⟩⟩

/-- The auxiliary addition `⊕` of `ℚ_sf(y)`, the addition of `F`. -/
instance instAddUniversalSemifield : Add (universalSemifield y) :=
  ⟨fun a b => ⟨a + b, add_mem_universalSemifield a.2 b.2⟩⟩

/-- The natural powers of `ℚ_sf(y)`, those of `F`. -/
instance instPowNatUniversalSemifield : Pow (universalSemifield y) ℕ :=
  ⟨fun a n => ⟨a ^ n, pow_mem_universalSemifield a.2 n⟩⟩

/-- The integer powers of `ℚ_sf(y)`, those of `F`. -/
instance instPowIntUniversalSemifield : Pow (universalSemifield y) ℤ :=
  ⟨fun a n => ⟨a ^ n, zpow_mem_universalSemifield a.2 n⟩⟩

namespace universalSemifield

/-- The product of `ℚ_sf(y)` is that of `F`. -/
@[simp, norm_cast, cluster_algebras "lem_universal_semifield_is_semifield"]
theorem coe_mul (a b : universalSemifield y) : ((a * b : universalSemifield y) : F) = a * b :=
  rfl

/-- The unit of `ℚ_sf(y)` is that of `F`. -/
@[simp, norm_cast]
theorem coe_one : ((1 : universalSemifield y) : F) = 1 :=
  rfl

/-- The inverse in `ℚ_sf(y)` is that of `F`. -/
@[simp, norm_cast]
theorem coe_inv (a : universalSemifield y) : ((a⁻¹ : universalSemifield y) : F) = (a : F)⁻¹ :=
  rfl

/-- The quotient in `ℚ_sf(y)` is that of `F`. -/
@[simp, norm_cast]
theorem coe_div (a b : universalSemifield y) : ((a / b : universalSemifield y) : F) = a / b :=
  rfl

/-- The auxiliary addition `⊕` of `ℚ_sf(y)` is the addition of `F`. -/
@[simp, norm_cast, cluster_algebras "lem_universal_semifield_is_semifield"]
theorem coe_add (a b : universalSemifield y) : ((a + b : universalSemifield y) : F) = a + b :=
  rfl

/-- The natural powers in `ℚ_sf(y)` are those of `F`. -/
@[simp, norm_cast]
theorem coe_pow (a : universalSemifield y) (n : ℕ) :
    ((a ^ n : universalSemifield y) : F) = (a : F) ^ n :=
  rfl

/-- The integer powers in `ℚ_sf(y)` are those of `F`. -/
@[simp, norm_cast]
theorem coe_zpow (a : universalSemifield y) (n : ℤ) :
    ((a ^ n : universalSemifield y) : F) = (a : F) ^ n :=
  rfl

/-- The product in `ℚ_sf(y)` of two elements given by their values in `F`. -/
theorem mk_mul_mk {z w : F} (hz : z ∈ universalSemifield y) (hw : w ∈ universalSemifield y) :
    (⟨z, hz⟩ * ⟨w, hw⟩ : universalSemifield y) = ⟨z * w, mul_mem_universalSemifield hz hw⟩ :=
  rfl

/-- The sum in `ℚ_sf(y)` of two elements given by their values in `F`. -/
theorem mk_add_mk {z w : F} (hz : z ∈ universalSemifield y) (hw : w ∈ universalSemifield y) :
    (⟨z, hz⟩ + ⟨w, hw⟩ : universalSemifield y) = ⟨z + w, add_mem_universalSemifield hz hw⟩ :=
  rfl

/-- The inverse in `ℚ_sf(y)` of an element given by its value in `F`. -/
theorem mk_inv {z : F} (hz : z ∈ universalSemifield y) :
    (⟨z, hz⟩⁻¹ : universalSemifield y) = ⟨z⁻¹, inv_mem_universalSemifield hz⟩ :=
  rfl

/-- The quotient in `ℚ_sf(y)` of two elements given by their values in `F`. -/
theorem mk_div_mk {z w : F} (hz : z ∈ universalSemifield y) (hw : w ∈ universalSemifield y) :
    (⟨z, hz⟩ / ⟨w, hw⟩ : universalSemifield y) = ⟨z / w, div_mem_universalSemifield hz hw⟩ :=
  rfl

/-- An element of `ℚ_sf(y)` is nonzero, when `F` has characteristic zero and `y` is
algebraically independent over `ℚ`. -/
theorem coe_ne_zero [CharZero F] (hy : AlgebraicIndependent ℚ y) (a : universalSemifield y) :
    (a : F) ≠ 0 :=
  fun h => zero_notMem_universalSemifield hy (h ▸ a.2)

end universalSemifield

/-! ### The semifield structure -/

open universalSemifield in
/-- **`ℚ_sf(y)` is a semifield** under the multiplication of `F`, with `⊕` the addition of `F`,
when `F` has characteristic zero and `y` is algebraically independent over `ℚ`. -/
@[cluster_algebras "lem_universal_semifield_is_semifield"]
instance instFZSemifieldUniversalSemifield [CharZero F] [Fact (AlgebraicIndependent ℚ y)] :
    FZSemifield (universalSemifield y) where
  __ := Subtype.coe_injective.commMonoid _ coe_one coe_mul coe_pow
  __ := Subtype.coe_injective.addCommSemigroup _ coe_add
  zpow n a := a ^ n
  div_eq_mul_inv a b := Subtype.ext (div_eq_mul_inv (a : F) b)
  zpow_zero' a := Subtype.ext (zpow_zero (a : F))
  zpow_succ' n a := Subtype.ext (DivInvMonoid.zpow_succ' n (a : F))
  zpow_neg' n a := Subtype.ext (DivInvMonoid.zpow_neg' n (a : F))
  inv_mul_cancel a := Subtype.ext (inv_mul_cancel₀ (coe_ne_zero Fact.out a))
  add_mul a b c := Subtype.ext (add_mul (a : F) b c)

section Structure

variable [CharZero F] [Fact (AlgebraicIndependent ℚ y)]

namespace universalSemifield

/-- The value in `ℚ_sf(y)` of a nonzero polynomial with coefficients in `ℕ` at a family `g` of
elements of `ℚ_sf(y)` is its value in `F` at the family of their coercions. -/
theorem coe_polyValue {κ : Type*} (g : κ → universalSemifield y) {P : MvPolynomial κ ℕ}
    (hP : P ≠ 0) :
    ((polyValue g P : universalSemifield y) : F) = aeval (fun i => (g i : F)) P := by
  let ρ : WithZero (universalSemifield y) →+* F :=
    { WithZero.lift' (⟨⟨Subtype.val, rfl⟩, fun _ _ => rfl⟩ : universalSemifield y →* F) with
      map_add' a b := by
        induction a <;> induction b <;> simp [← WithZero.coe_add] }
  have hρ (a : universalSemifield y) : ρ a = a := WithZero.lift'_coe _ a
  have h1 : ρ.comp (Nat.castRingHom _) = algebraMap ℕ F := Subsingleton.elim _ _
  have h2 : ρ ∘ (fun i => (g i : WithZero (universalSemifield y))) = fun i => (g i : F) :=
    funext fun i => hρ (g i)
  rw [← hρ, coe_polyValue_eq_eval₂ g hP, eval₂_comp_left, h1, h2, aeval_def]

/-- The value at `y` of a nonzero polynomial with coefficients in `ℕ`, as an element of
`ℚ_sf(y)`, is its value in the semifield `ℚ_sf(y)` at the generators `yᵢ`. -/
theorem mk_aeval_eq_polyValue {P : MvPolynomial ι ℕ} (hP : P ≠ 0) :
    (⟨aeval y P, aeval_mem_universalSemifield y hP⟩ : universalSemifield y) =
      polyValue (fun i => ⟨y i, mem_universalSemifield_self y i⟩) P := by
  ext
  rw [universalSemifield.coe_polyValue _ hP]

/-- An element `z` of `ℚ_sf(y)` with `Q(y) z = P(y)` is the quotient of the elements `P(y)` and
`Q(y)` of `ℚ_sf(y)`. -/
theorem mk_eq_div {z : F} (hz : z ∈ universalSemifield y) {P Q : MvPolynomial ι ℕ}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (h : aeval y Q * z = aeval y P) :
    (⟨z, hz⟩ : universalSemifield y) =
      ⟨aeval y P, aeval_mem_universalSemifield y hP⟩ /
        ⟨aeval y Q, aeval_mem_universalSemifield y hQ⟩ :=
  Subtype.ext (eq_div_of_mul_eq (aeval_nat_ne_zero Fact.out hQ) (by rw [mul_comm, h]))

end universalSemifield

variable {S : Type*} [FZSemifield S]

/-- A semifield homomorphism out of `ℚ_sf(y)` sends the value at `y` of a nonzero polynomial with
coefficients in `ℕ` to its value at the images of the generators `yᵢ`. -/
theorem FZSemifieldHom.apply_aeval (φ : FZSemifieldHom (universalSemifield y) S)
    {P : MvPolynomial ι ℕ} (hP : P ≠ 0) :
    φ ⟨aeval y P, aeval_mem_universalSemifield y hP⟩ =
      polyValue (fun i => φ ⟨y i, mem_universalSemifield_self y i⟩) P := by
  rw [universalSemifield.mk_aeval_eq_polyValue hP, map_polyValue φ _ hP]
  rfl

/-- A semifield homomorphism `φ` out of `ℚ_sf(y)` is determined by its values on the generators:
if `Q(y) z = P(y)`, then `φ(z) = P(f)_S / Q(f)_S` with `fᵢ = φ(yᵢ)`. -/
theorem FZSemifieldHom.apply_of_mul_eq (φ : FZSemifieldHom (universalSemifield y) S) {z : F}
    (hz : z ∈ universalSemifield y) {P Q : MvPolynomial ι ℕ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : aeval y Q * z = aeval y P) :
    φ ⟨z, hz⟩ = polyValue (fun i => φ ⟨y i, mem_universalSemifield_self y i⟩) P /
      polyValue (fun i => φ ⟨y i, mem_universalSemifield_self y i⟩) Q := by
  rw [universalSemifield.mk_eq_div hz hP hQ h, map_div, φ.apply_aeval hP, φ.apply_aeval hQ]

/-- **Uniqueness in the universal property of `ℚ_sf(y)`.** Two semifield homomorphisms out of
`ℚ_sf(y)` that agree on the generators `yᵢ` are equal. -/
@[cluster_algebras "lem_universal_semifield_unique"]
theorem universalSemifield.hom_ext {φ φ' : FZSemifieldHom (universalSemifield y) S}
    (h : ∀ i, φ ⟨y i, mem_universalSemifield_self y i⟩ =
      φ' ⟨y i, mem_universalSemifield_self y i⟩) :
    φ = φ' := by
  ext ⟨z, hz⟩
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := hz
  rw [φ.apply_of_mul_eq _ hP hQ hPQ, φ'.apply_of_mul_eq _ hP hQ hPQ, funext h]

/-- Two representations `P / Q` and `P' / Q'` of the same element of `ℚ_sf(y)` give the same
quotient of values in any semifield. -/
private theorem polyValue_div_polyValue_eq (f : ι → S) {z : F} {P Q P' Q' : MvPolynomial ι ℕ}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hP' : P' ≠ 0) (hQ' : Q' ≠ 0) (h : aeval y Q * z = aeval y P)
    (h' : aeval y Q' * z = aeval y P') :
    polyValue f P / polyValue f Q = polyValue f P' / polyValue f Q' := by
  have hpoly : P * Q' = P' * Q := by
    apply aeval_nat_injective (y := y) Fact.out
    rw [map_mul, map_mul, ← h, ← h']
    ring
  rw [div_eq_div_iff_mul_eq_mul, ← polyValue_mul f hP hQ', ← polyValue_mul f hP' hQ, hpoly]

/-- The quotient of values computed from the chosen representation of `z ∈ ℚ_sf(y)` is that
computed from any other representation. -/
private theorem polyValue_div_polyValue_choose (f : ι → S) {z : F}
    (hz : z ∈ universalSemifield y) {P Q : MvPolynomial ι ℕ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : aeval y Q * z = aeval y P) :
    polyValue f hz.choose / polyValue f hz.choose_spec.choose = polyValue f P / polyValue f Q :=
  have h₀ := hz.choose_spec.choose_spec
  polyValue_div_polyValue_eq f h₀.1 h₀.2.1 hP hQ h₀.2.2 h

variable (y) in
/-- The semifield homomorphism `ℚ_sf(y) → S` sending each generator `yᵢ` to `fᵢ`: it sends `z`
with `Q(y) z = P(y)` to `P(f)_S / Q(f)_S`. -/
noncomputable def universalSemifieldLift (f : ι → S) : FZSemifieldHom (universalSemifield y) S where
  toFun z := polyValue f z.2.choose / polyValue f z.2.choose_spec.choose
  map_mul' := by
    rintro ⟨z, P, Q, hP, hQ, h⟩ ⟨w, P', Q', hP', hQ', h'⟩
    simp only [universalSemifield.mk_mul_mk]
    rw [polyValue_div_polyValue_choose f _ hP hQ h, polyValue_div_polyValue_choose f _ hP' hQ' h',
      polyValue_div_polyValue_choose f _ (mul_ne_zero hP hP') (mul_ne_zero hQ hQ')
        (by rw [map_mul, map_mul, ← h, ← h']; ring),
      polyValue_mul f hP hP', polyValue_mul f hQ hQ', mul_div_mul_comm]
  map_add' := by
    rintro ⟨z, P, Q, hP, hQ, h⟩ ⟨w, P', Q', hP', hQ', h'⟩
    have hPQ := mul_ne_zero hP hQ'
    have hP'Q := mul_ne_zero hP' hQ
    simp only [universalSemifield.mk_add_mk]
    rw [polyValue_div_polyValue_choose f _ hP hQ h, polyValue_div_polyValue_choose f _ hP' hQ' h',
      polyValue_div_polyValue_choose f _ (add_ne_zero_of_left (Q := P' * Q) hPQ)
        (mul_ne_zero hQ hQ')
        (by rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']; ring),
      polyValue_add f hPQ hP'Q, polyValue_mul f hP hQ', polyValue_mul f hP' hQ,
      polyValue_mul f hQ hQ', div_eq_mul_inv, add_mul, ← div_eq_mul_inv, ← div_eq_mul_inv,
      mul_div_mul_right_eq_div, mul_comm (polyValue f Q), mul_div_mul_right_eq_div]

/-- The homomorphism `universalSemifieldLift y f` sends `z` with `Q(y) z = P(y)` to
`P(f)_S / Q(f)_S`. -/
theorem universalSemifieldLift_apply (f : ι → S) {z : F} (hz : z ∈ universalSemifield y)
    {P Q : MvPolynomial ι ℕ} (hP : P ≠ 0) (hQ : Q ≠ 0) (h : aeval y Q * z = aeval y P) :
    universalSemifieldLift y f ⟨z, hz⟩ = polyValue f P / polyValue f Q :=
  polyValue_div_polyValue_choose f hz hP hQ h

/-- The homomorphism `universalSemifieldLift y f` sends `P(y)` to `P(f)_S`. -/
theorem universalSemifieldLift_apply_aeval (f : ι → S) {P : MvPolynomial ι ℕ} (hP : P ≠ 0) :
    universalSemifieldLift y f ⟨aeval y P, aeval_mem_universalSemifield y hP⟩ = polyValue f P := by
  rw [universalSemifieldLift_apply f _ hP one_ne_zero (by simp), polyValue_one, div_one]

/-- The homomorphism `universalSemifieldLift y f` sends each generator `yᵢ` to `fᵢ`. -/
@[simp]
theorem universalSemifieldLift_apply_self (f : ι → S) (i : ι) :
    universalSemifieldLift y f ⟨y i, mem_universalSemifield_self y i⟩ = f i := by
  simpa using universalSemifieldLift_apply_aeval (y := y) f (X_ne_zero (R := ℕ) i)

/-- **Existence in the universal property of `ℚ_sf(y)`.** For every family `f` of elements of a
semifield `S` there is a semifield homomorphism `ℚ_sf(y) → S` sending each `yᵢ` to `fᵢ`. -/
@[cluster_algebras "lem_universal_semifield_exists"]
theorem universalSemifield.exists_hom (f : ι → S) :
    ∃ φ : FZSemifieldHom (universalSemifield y) S,
      ∀ i, φ ⟨y i, mem_universalSemifield_self y i⟩ = f i :=
  ⟨universalSemifieldLift y f, universalSemifieldLift_apply_self f⟩

/-- A semifield homomorphism out of `ℚ_sf(y)` sending each `yᵢ` to `fᵢ` is
`universalSemifieldLift y f`. -/
theorem eq_universalSemifieldLift {f : ι → S} {φ : FZSemifieldHom (universalSemifield y) S}
    (h : ∀ i, φ ⟨y i, mem_universalSemifield_self y i⟩ = f i) : φ = universalSemifieldLift y f :=
  universalSemifield.hom_ext fun i => by rw [h, universalSemifieldLift_apply_self]

end Structure

end ClusterAlgebras

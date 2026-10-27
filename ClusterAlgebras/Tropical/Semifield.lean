/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Semifield.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Tropical.Basic

/-!
# Tropical semifields

The *tropical semifield* `Trop(q_i : i ∈ ι)` is the multiplicative group of Laurent monomials
`∏ᵢ qᵢ ^ aᵢ`, `a ∈ ℤ^ι`, in formal variables `qᵢ`, with the auxiliary addition
`∏ᵢ qᵢ ^ aᵢ ⊕ ∏ᵢ qᵢ ^ bᵢ = ∏ᵢ qᵢ ^ min(aᵢ, bᵢ)`.

A Laurent monomial is recorded by its exponent vector, one entry of Mathlib's `Tropical ℤ` per
variable: in `Tropical ℤ` the product is the sum of the underlying integers and the sum is their
minimum. So `TropicalSemifield ι` is `ι → Tropical ℤ` with the pointwise operations, and it is a
semifield in the sense of Fomin–Zelevinsky.

FWZ take `ι = [1, ℓ]`. The definition makes sense for any index type, so none is
fixed here; for a finite `ι` every element is the product `∏ᵢ qᵢ ^ aᵢ` of powers of the
generators (`TropicalSemifield.prod_q_zpow`).

## Main definitions

* `ClusterAlgebras.TropicalSemifield`: the tropical semifield.
* `ClusterAlgebras.TropicalSemifield.monomial`: the Laurent monomial with a given exponent
  vector.
* `ClusterAlgebras.TropicalSemifield.exponent`: the exponent vector of an element.
* `ClusterAlgebras.TropicalSemifield.q`: the generator `qᵢ`.

## Main results

* `ClusterAlgebras.TropicalSemifield.instFZSemifield`: the tropical semifield is a semifield.
-/

@[expose] public section

namespace ClusterAlgebras

open Tropical

/-- The **tropical semifield** `Trop(q_i : i ∈ ι)`: the Laurent monomials `∏ᵢ qᵢ ^ aᵢ` in formal
variables `qᵢ`, recorded by their exponent vectors `a : ι → ℤ`, with the product of monomials
and the auxiliary addition `∏ᵢ qᵢ ^ aᵢ ⊕ ∏ᵢ qᵢ ^ bᵢ = ∏ᵢ qᵢ ^ min(aᵢ, bᵢ)`. Each exponent is
stored in Mathlib's `Tropical ℤ`, whose product is the sum and whose sum is the minimum. -/
@[cluster_algebras "def_tropical_semifield"]
def TropicalSemifield (ι : Type*) : Type _ :=
  ι → Tropical ℤ

namespace TropicalSemifield

variable {ι : Type*}

/-- The multiplicative group of Laurent monomials: exponent vectors add under multiplication. -/
instance instCommGroup : CommGroup (TropicalSemifield ι) :=
  inferInstanceAs (CommGroup (ι → Tropical ℤ))

/-- The auxiliary addition: exponent vectors combine by the componentwise minimum. -/
instance instAddCommSemigroup : AddCommSemigroup (TropicalSemifield ι) :=
  inferInstanceAs (AddCommSemigroup (ι → Tropical ℤ))

/-- **The tropical semifield is a semifield.** In exponents, `⊕` is the componentwise minimum
and the product is componentwise addition, and `min(aᵢ, bᵢ) + cᵢ = min(aᵢ + cᵢ, bᵢ + cᵢ)` is the
distributive law. -/
@[cluster_algebras "lem_tropical_semifield"]
instance instFZSemifield : FZSemifield (TropicalSemifield ι) where
  __ := instCommGroup
  __ := instAddCommSemigroup
  add_mul p q r := funext fun i => add_mul (p i) (q i) (r i)

/-- The Laurent monomial `∏ᵢ qᵢ ^ aᵢ` with exponent vector `a`. -/
@[cluster_algebras "def_tropical_semifield"]
def monomial (a : ι → ℤ) : TropicalSemifield ι :=
  fun i => trop (a i)

/-- The exponent vector `a` of a Laurent monomial `∏ᵢ qᵢ ^ aᵢ`. -/
def exponent (y : TropicalSemifield ι) : ι → ℤ :=
  fun i => untrop (y i)

/-- The exponent vector of the monomial with exponent vector `a` is `a`. -/
@[simp]
theorem exponent_monomial (a : ι → ℤ) : exponent (monomial a) = a :=
  rfl

/-- Every element is the monomial with its own exponent vector. -/
@[simp]
theorem monomial_exponent (y : TropicalSemifield ι) : monomial (exponent y) = y :=
  rfl

/-- An element of the tropical semifield is determined by its exponent vector. -/
theorem exponent_injective : Function.Injective (exponent : TropicalSemifield ι → ι → ℤ) :=
  fun _ _ h => funext fun i => untrop_injective (congrFun h i)

/-- Distinct exponent vectors give distinct monomials. -/
theorem monomial_injective : Function.Injective (monomial : (ι → ℤ) → TropicalSemifield ι) :=
  fun _ _ h => congrArg exponent h

/-- Two elements of the tropical semifield with the same exponent vector are equal. -/
@[ext]
theorem ext {y y' : TropicalSemifield ι} (h : ∀ i, exponent y i = exponent y' i) : y = y' :=
  exponent_injective (funext h)

/-- The identity `1` has exponent vector `0`. -/
@[simp]
theorem exponent_one : exponent (1 : TropicalSemifield ι) = 0 :=
  rfl

/-- The exponent vector of a product is the sum of the exponent vectors. -/
@[simp]
theorem exponent_mul (y y' : TropicalSemifield ι) : exponent (y * y') = exponent y + exponent y' :=
  rfl

/-- The exponent vector of an inverse is the negated exponent vector. -/
@[simp]
theorem exponent_inv (y : TropicalSemifield ι) : exponent y⁻¹ = -exponent y :=
  rfl

/-- The exponent vector of a quotient is the difference of the exponent vectors. -/
@[simp]
theorem exponent_div (y y' : TropicalSemifield ι) : exponent (y / y') = exponent y - exponent y' :=
  rfl

/-- In exponents, the auxiliary addition of the tropical semifield is the componentwise
minimum. -/
@[simp]
theorem exponent_add (y y' : TropicalSemifield ι) (i : ι) :
    exponent (y + y') i = min (exponent y i) (exponent y' i) :=
  untrop_add (y i) (y' i)

/-- The exponent vector of `y ^ k`, for an integer `k`, is `k` times that of `y`. -/
@[simp]
theorem exponent_zpow (y : TropicalSemifield ι) (k : ℤ) : exponent (y ^ k) = k • exponent y := by
  funext i
  exact untrop_zpow (y i) k

/-- The exponent vector of `y ^ k`, for a natural number `k`, is `k` times that of `y`. -/
@[simp]
theorem exponent_pow (y : TropicalSemifield ι) (k : ℕ) : exponent (y ^ k) = k • exponent y := by
  funext i
  exact untrop_pow (y i) k

/-- The monomial with exponent vector `a + b` is the product of those with exponent vectors `a`
and `b`. -/
theorem monomial_add (a b : ι → ℤ) : monomial (a + b) = monomial a * monomial b :=
  rfl

/-- The monomial with exponent vector `0` is `1`. -/
@[simp]
theorem monomial_zero : monomial (0 : ι → ℤ) = 1 :=
  rfl

/-- The exponent vector of a finite product is the sum of the exponent vectors of the factors. -/
@[simp]
theorem exponent_prod {κ : Type*} (s : Finset κ) (f : κ → TropicalSemifield ι) :
    exponent (∏ k ∈ s, f k) = ∑ k ∈ s, exponent (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, exponent_mul, ih]

variable [DecidableEq ι]

/-- The generator `qᵢ` of the tropical semifield: the monomial with exponent vector the `i`-th
unit vector. -/
@[cluster_algebras "def_tropical_semifield"]
def q (i : ι) : TropicalSemifield ι :=
  monomial (Pi.single i 1)

/-- The exponent vector of the generator `qᵢ` is the `i`-th unit vector. -/
@[simp]
theorem exponent_q (i : ι) : exponent (q i) = Pi.single i 1 :=
  rfl

/-- Every element of the tropical semifield over a finite index type is the Laurent monomial
`∏ᵢ qᵢ ^ aᵢ` in the generators, `a` being its exponent vector. -/
theorem prod_q_zpow [Fintype ι] (y : TropicalSemifield ι) :
    ∏ i, q i ^ exponent y i = y := by
  ext j
  rw [exponent_prod]
  simp [Finset.sum_apply, Pi.single_apply]

end TropicalSemifield

end ClusterAlgebras

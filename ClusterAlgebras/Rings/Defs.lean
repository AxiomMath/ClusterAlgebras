/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.Minor
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Polynomial rings and rings of invariants of matrices

This file defines the polynomial ring `ℂ[z]` in the entries of a generic `p × q` matrix, the left
substitution `σ_g` and the ring `ℂ[z]^G` of invariants of a set `G` of matrices, the
one-parameter substitutions `Θ_{ij}`, the lower unitriangular matrices `U_p`, the coordinate ring
`ℂ[SL_k] = ℂ[z]/⟨det z - 1⟩` and its `U`-invariants, the Plücker ring `R_{a,b}`, the rotation of
the columns, the cyclic shift of a set of columns, and the specialization of the last `k` columns
of a `k × 2k` matrix.

## Main definitions

* `ClusterAlgebras.complexGenericMatrix p q`: the generic `p × q` matrix over `ℂ`.
* `ClusterAlgebras.leftSubst q g`, `ClusterAlgebras.invariants q G`: `σ_g` and `ℂ[z]^G`.
* `ClusterAlgebras.oneParamSubst q i j`: `Θ_{ij} : ℂ[z] → ℂ[z][t]`.
* `ClusterAlgebras.lowerUnitriangular p`: the set `U_p`.
* `ClusterAlgebras.SLCoord k`, `ClusterAlgebras.slQuot k`, `ClusterAlgebras.slUInvariants k`:
  `ℂ[SL_k]`, the quotient map `π`, and `ℂ[SL_k]^U`.
* `ClusterAlgebras.pluckerRing a b`: `R_{a,b} = ℂ[z]^{SL_a(ℂ)}`.
* `ClusterAlgebras.rotation a b`: the rotation `ρ` of the columns.
* `ClusterAlgebras.cyclicShift i J`: `(J + i) mod b`.
* `ClusterAlgebras.matSpecialization k`, `matColSet`, `matRowSet`: `φ`, `L(J)` and `K(J)`.

## Implementation notes

* Indices are 0-based: row `i` and column `j` of a matrix are `i - 1 : Fin p` and
  `j - 1 : Fin q`. A set `J ⊆ [1, b]` of columns is a `Finset (Fin b)`.
* The elementary matrix `E_{ij}(s) = 1 + s e_{ij}` is Mathlib's `Matrix.transvection i j s`, and
  is used under that name.
* `ℂ[z]^G` is defined for any set `G` of matrices. Each `σ_g` is a `ℂ`-algebra homomorphism, so
  the invariants form a `ℂ`-subalgebra whatever `G` is, and no group structure is assumed.
* `ℂ[SL_k]^U` is likewise a `ℂ`-subalgebra of `ℂ[SL_k]`: its elements are the classes having a
  representative `f` with `σ_u(f) - f ∈ ⟨det z - 1⟩` for every `u ∈ U_k`.
* The cyclic shift `(J + i) mod b` of a set of columns is the image of `J` under the `i`-th power
  of `finRotate b`, the cyclic permutation `j ↦ j + 1 mod b`.
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial

/-! ### The generic matrix over `ℂ` -/

/-- The polynomial ring `ℂ[z] = ℂ[z_{ij} : i ∈ [1, p], j ∈ [1, q]]`. -/
abbrev ComplexPoly (p q : ℕ) : Type := MvPolynomial (Fin p × Fin q) ℂ

/-- The **generic `p × q` matrix over `ℂ`**: the image of the generic matrix `genericMatrix` under
the ring homomorphism `ℤ[z] → ℂ[z]` fixing every `z_{ij}`. Its entries are the indeterminates. -/
@[cluster_algebras "def_complex_generic_matrix"]
noncomputable def complexGenericMatrix (p q : ℕ) : Matrix (Fin p) (Fin q) (ComplexPoly p q) :=
  (genericMatrix (Fin p) (Fin q)).map (MvPolynomial.map (Int.castRingHom ℂ))

/-- The entries of the generic matrix over `ℂ` are the indeterminates. -/
@[cluster_algebras "def_complex_generic_matrix", simp]
theorem complexGenericMatrix_apply {p q : ℕ} (i : Fin p) (j : Fin q) :
    complexGenericMatrix p q i j = X (i, j) := by
  simp [complexGenericMatrix, genericMatrix, Matrix.mvPolynomialX_apply]

/-- The generic matrix over `ℂ` is Mathlib's `Matrix.mvPolynomialX` over `ℂ`. -/
theorem complexGenericMatrix_eq_mvPolynomialX (p q : ℕ) :
    complexGenericMatrix p q = Matrix.mvPolynomialX (Fin p) (Fin q) ℂ := by
  ext i j
  simp [Matrix.mvPolynomialX_apply]

/-! ### Left substitution and invariants -/

/-- The **left substitution** `σ_g` for a complex `p × p` matrix `g`: the `ℂ`-algebra endomorphism
of `ℂ[z]` with `σ_g(z_{ij}) = ∑ₗ g_{il} z_{lj}`, which substitutes `gz` for `z`. -/
@[cluster_algebras "def_left_substitution"]
noncomputable def leftSubst {p : ℕ} (q : ℕ) (g : Matrix (Fin p) (Fin p) ℂ) :
    ComplexPoly p q →ₐ[ℂ] ComplexPoly p q :=
  aeval fun ij => ∑ l, C (g ij.1 l) * X (l, ij.2)

/-- `σ_g(z_{ij}) = ∑ₗ g_{il} z_{lj}`. -/
@[simp]
theorem leftSubst_X {p q : ℕ} (g : Matrix (Fin p) (Fin p) ℂ) (i : Fin p) (j : Fin q) :
    leftSubst q g (X (i, j)) = ∑ l, C (g i l) * X (l, j) := by
  simp [leftSubst]

/-- `σ_g` substitutes `gz` for the generic matrix `z`. -/
theorem map_leftSubst_complexGenericMatrix {p q : ℕ} (g : Matrix (Fin p) (Fin p) ℂ) :
    (complexGenericMatrix p q).map (leftSubst q g) =
      g.map (algebraMap ℂ (ComplexPoly p q)) * complexGenericMatrix p q := by
  ext i j
  simp [Matrix.mul_apply, MvPolynomial.algebraMap_eq]

/-- The **invariants** `ℂ[z]^G = {f ∈ ℂ[z] : σ_g(f) = f for every g ∈ G}` of a set `G` of complex
`p × p` matrices, a `ℂ`-subalgebra of `ℂ[z]`. -/
@[cluster_algebras "def_left_substitution"]
noncomputable def invariants {p : ℕ} (q : ℕ) (G : Set (Matrix (Fin p) (Fin p) ℂ)) :
    Subalgebra ℂ (ComplexPoly p q) where
  carrier := {f | ∀ g ∈ G, leftSubst q g f = f}
  mul_mem' {f f'} hf hf' g hg := by rw [map_mul, hf g hg, hf' g hg]
  add_mem' {f f'} hf hf' g hg := by rw [map_add, hf g hg, hf' g hg]
  algebraMap_mem' c g _ := (leftSubst q g).commutes c

/-- Membership in `ℂ[z]^G`. -/
theorem mem_invariants {p q : ℕ} {G : Set (Matrix (Fin p) (Fin p) ℂ)} {f : ComplexPoly p q} :
    f ∈ invariants q G ↔ ∀ g ∈ G, leftSubst q g f = f :=
  Iff.rfl

/-- The **one-parameter substitution** `Θ_{ij} : ℂ[z] → ℂ[z][t]`, the `ℂ`-algebra homomorphism
with `Θ_{ij}(z_{il}) = z_{il} + t z_{jl}` and `Θ_{ij}(z_{i'l}) = z_{i'l}` for `i' ≠ i`. -/
@[cluster_algebras "def_one_parameter_substitution"]
noncomputable def oneParamSubst {p : ℕ} (q : ℕ) (i j : Fin p) :
    ComplexPoly p q →ₐ[ℂ] Polynomial (ComplexPoly p q) :=
  aeval fun al => if al.1 = i then Polynomial.C (X al) + Polynomial.X * Polynomial.C (X (j, al.2))
    else Polynomial.C (X al)

/-- The set `U_p` of **lower unitriangular** complex `p × p` matrices: `u_{ii} = 1` for all `i`
and `u_{ij} = 0` for `i < j`. -/
@[cluster_algebras "def_unipotent_group"]
def lowerUnitriangular (p : ℕ) : Set (Matrix (Fin p) (Fin p) ℂ) :=
  {u | (∀ i, u i i = 1) ∧ ∀ i j, i < j → u i j = 0}

/-! ### The coordinate ring of `SL_k` -/

/-- The polynomial `det z - 1 ∈ ℂ[z]` for the generic `k × k` matrix `z`. -/
noncomputable def detSubOne (k : ℕ) : ComplexPoly k k :=
  (complexGenericMatrix k k).det - 1

/-- The **coordinate ring** `ℂ[SL_k] = ℂ[z]/⟨det z - 1⟩`. -/
@[cluster_algebras "def_coordinate_ring_sl"]
abbrev SLCoord (k : ℕ) : Type := ComplexPoly k k ⧸ Ideal.span {detSubOne k}

/-- The quotient map `π : ℂ[z] → ℂ[SL_k]`. -/
@[cluster_algebras "def_coordinate_ring_sl"]
noncomputable def slQuot (k : ℕ) : ComplexPoly k k →ₐ[ℂ] SLCoord k :=
  Ideal.Quotient.mkₐ ℂ _

/-- The **`U`-invariants** `ℂ[SL_k]^U`: the elements `π(f)` of `ℂ[SL_k]` such that
`σ_u(f) - f ∈ ⟨det z - 1⟩` for every `u ∈ U_k`, a `ℂ`-subalgebra of `ℂ[SL_k]`. -/
@[cluster_algebras "def_coordinate_ring_sl"]
noncomputable def slUInvariants (k : ℕ) : Subalgebra ℂ (SLCoord k) where
  carrier := {a | ∃ f, slQuot k f = a ∧
    ∀ u ∈ lowerUnitriangular k, leftSubst k u f - f ∈ Ideal.span {detSubOne k}}
  mul_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨f', rfl, hf'⟩
    refine ⟨f * f', map_mul _ _ _, fun u hu => ?_⟩
    have : leftSubst k u (f * f') - f * f' =
        leftSubst k u f * (leftSubst k u f' - f') + (leftSubst k u f - f) * f' := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ (hf' u hu)) (Ideal.mul_mem_right _ _ (hf u hu))
  add_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨f', rfl, hf'⟩
    refine ⟨f + f', map_add _ _ _, fun u hu => ?_⟩
    have : leftSubst k u (f + f') - (f + f') = (leftSubst k u f - f) + (leftSubst k u f' - f') := by
      rw [map_add]; ring
    rw [this]
    exact add_mem (hf u hu) (hf' u hu)
  algebraMap_mem' c := ⟨algebraMap ℂ _ c, (slQuot k).commutes c, fun u _ => by simp⟩

/-- Membership in `ℂ[SL_k]^U`. -/
theorem mem_slUInvariants {k : ℕ} {a : SLCoord k} :
    a ∈ slUInvariants k ↔ ∃ f, slQuot k f = a ∧
      ∀ u ∈ lowerUnitriangular k, leftSubst k u f - f ∈ Ideal.span {detSubOne k} :=
  Iff.rfl

/-! ### The Plücker ring -/

/-- The **Plücker ring** `R_{a,b} = ℂ[z]^{SL_a(ℂ)}`: the polynomials in the entries of the generic
`a × b` matrix invariant under left multiplication by complex `a × a` matrices of determinant
`1`. -/
@[cluster_algebras "def_plucker_ring"]
noncomputable def pluckerRing (a b : ℕ) : Subalgebra ℂ (ComplexPoly a b) :=
  invariants b {g | g.det = 1}

/-! ### Rotation and cyclic shifts of the columns -/

/-- The **rotation** `ρ` of the columns: the `ℂ`-algebra endomorphism of `ℂ[z]`, `z` the generic
`a × b` matrix, with `ρ(z_{rj}) = z_{r,j-1}` for `j ∈ [2, b]` and `ρ(z_{r1}) = (-1)^{a-1} z_{rb}`
(1-based; here column `0` goes to `(-1)^{a-1}` times column `b - 1`). -/
@[cluster_algebras "def_rotation_map"]
noncomputable def rotation (a b : ℕ) : ComplexPoly a b →ₐ[ℂ] ComplexPoly a b :=
  aeval fun rj =>
    if h : (rj.2 : ℕ) = 0 then C ((-1) ^ (a - 1)) * X (rj.1, ⟨b - 1, by have := rj.2.isLt; omega⟩)
    else X (rj.1, ⟨rj.2 - 1, by have := rj.2.isLt; omega⟩)

/-- The **cyclic shift** `(J + i) mod b` of a set `J` of columns: the image of `J` under the
`i`-th power of the cyclic permutation `j ↦ j + 1 mod b`. -/
@[cluster_algebras "def_rectangles_seed"]
def cyclicShift {b : ℕ} (i : ℤ) (J : Finset (Fin b)) : Finset (Fin b) :=
  J.map ((finRotate b ^ i : Equiv.Perm (Fin b)) : Fin b ↪ Fin b)

/-! ### Specializing the last `k` columns -/

/-- The **specialization of the last `k` columns** `φ : ℂ[z] → ℂ[y]`, `z` the generic `k × 2k`
matrix and `y` the generic `k × k` matrix: `φ(z_{rj}) = y_{rj}` for `j ∈ [1, k]`, and for
`j ∈ [1, k]`, `φ(z_{r,k+j}) = (-1)^{j-1}` if `r = k + 1 - j` and `0` otherwise. With 0-based
indices, column `c ≥ k` goes to `(-1)^{c - k}` times the unit vector of row `2k - 1 - c`. -/
@[cluster_algebras "def_mat_specialization"]
noncomputable def matSpecialization (k : ℕ) : ComplexPoly k (2 * k) →ₐ[ℂ] ComplexPoly k k :=
  aeval fun rc =>
    if h : (rc.2 : ℕ) < k then X (rc.1, ⟨rc.2, h⟩)
    else if (rc.1 : ℕ) + (rc.2 : ℕ) = 2 * k - 1 then C ((-1) ^ ((rc.2 : ℕ) - k)) else 0

/-- `L(J) = J ∩ [1, k]`, the columns of `J` among the first `k`, as columns of `y`. -/
@[cluster_algebras "def_mat_specialization"]
def matColSet (k : ℕ) (J : Finset (Fin (2 * k))) : Finset (Fin k) :=
  Finset.univ.filter fun j => (⟨j, by have := j.isLt; omega⟩ : Fin (2 * k)) ∈ J

/-- `K(J) = [1, k] \ {k + 1 - j : k + j ∈ J}`, as rows of `y`: with 0-based indices, the rows `r`
such that column `2k - 1 - r` is not in `J`. -/
@[cluster_algebras "def_mat_specialization"]
def matRowSet (k : ℕ) (J : Finset (Fin (2 * k))) : Finset (Fin k) :=
  Finset.univ.filter fun r => (⟨2 * k - 1 - r, by have := r.isLt; omega⟩ : Fin (2 * k)) ∉ J

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.Complex.Basic

/-!
# Minors, Plücker coordinates and flag minors

The determinantal vocabulary of total positivity: the minor `Δ_{I,J}` of a matrix, totally
positive matrices, the generic matrix, Plücker coordinates of a `k × m` matrix, the Grassmannian
of `k`-planes and its totally positive part, and the flag minors `P_J`.

## Main definitions

* `minor`: the minor `Δ_{I,J}(z)` on rows `I` and columns `J`.
* `IsTotallyPositive`: every square minor of a real square matrix is positive.
* `genericMatrix`: the matrix of indeterminates `z_{ij}` over `ℤ`.
* `pluckerCoord`: the Plücker coordinate `P_J(z)` of a `k × m` matrix.
* `grassmannian`, `tpGrassmannian`: `Gr_{k,m}` and its totally positive part `Gr⁺_{k,m}`.
* `flagMinor`: the flag minor `P_J(z) = Δ_{[1,|J|],J}(z)`.
* `IsFlagTotallyPositive`: every flag minor on a nonempty proper column set is positive.

## Main results

* `minor_genericMatrix_ne_zero`: every square minor of the generic matrix is nonzero.
* `pluckerCoord_pair`: the Plücker coordinates of a `2 × m` matrix written out.
* `flagMinor_eq_pluckerCoord`: for a `k × m` matrix and `|J| = k` the flag minor is the Plücker
  coordinate.

## Implementation notes

* Rows and columns are indexed by linearly ordered types rather than sets of positive integers.
  `Finset.orderEmbOfFin` is the increasing enumeration, so the minor is the determinant of
  `z.submatrix (I.orderEmbOfFin _) (J.orderEmbOfFin _)`. An `m × n` matrix is the case `Fin m`,
  `Fin n`, with 0-based indices.

* The minor is total, with junk value `0` when `|I| ≠ |J|`; `minor_of_card_eq` recovers the
  defining determinant. The case `I = J = ∅` gives `1`, the empty determinant, so nonemptiness is
  assumed in the positivity definitions.

* `genericMatrix ι κ` is a reducible abbreviation of `Matrix.mvPolynomialX` with coefficients
  in `ℤ`.

* `grassmannian k m` is the set of `k`-dimensional subspaces of `ℂ^m`. Mathlib's
  `Module.Grassmannian` parametrises quotients of rank `k`, the dual convention.

* "Positive real number" in `ℂ` is `∃ r : ℝ, 0 < r ∧ w = r`, which needs no order on `ℂ`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 1.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {R S : Type*} [CommRing R] [CommRing S] {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]

/-! ### Minors -/

/-- The **minor** `Δ_{I,J}(z)`: for finite sets `I` of rows and `J` of columns with
`|I| = |J| = k`, listed increasingly as `i₁ < ⋯ < i_k` and `j₁ < ⋯ < j_k`, the determinant of the
`k × k` matrix `(z_{i_s j_t})`. When `|I| ≠ |J|` it is `0`, a junk value no statement relies on. -/
@[cluster_algebras "def_minor"]
def minor (z : Matrix ι κ R) (I : Finset ι) (J : Finset κ) : R :=
  if h : J.card = I.card then (z.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h)).det else 0

/-- On sets of equal size the minor is the determinant of the submatrix they cut out, rows and
columns taken in increasing order. -/
theorem minor_of_card_eq (z : Matrix ι κ R) {I : Finset ι} {J : Finset κ} {k : ℕ}
    (hI : I.card = k) (hJ : J.card = k) :
    minor z I J = (z.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hI
  rw [minor, dif_pos hJ]

/-- A ring homomorphism carries a minor of `z` to the same minor of its image. -/
theorem RingHom.map_minor (f : R →+* S) (z : Matrix ι κ R) (I : Finset ι) (J : Finset κ) :
    f (minor z I J) = minor (z.map f) I J := by
  unfold minor
  split_ifs
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]
  · exact map_zero f

/-! ### Totally positive matrices -/

/-- A real `n × n` matrix is **totally positive** if every minor `Δ_{I,J}` with `I`, `J` nonempty
of the same size is positive. -/
@[cluster_algebras "def_totally_positive"]
def IsTotallyPositive {n : ℕ} (z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ I J : Finset (Fin n), I.Nonempty → I.card = J.card → 0 < minor z I J

/-! ### The generic matrix -/

/-- The **generic `ι × κ` matrix**: its entries are the indeterminates `z_{ij}` of the integer
polynomial ring `ℤ[z_{ij} : i ∈ ι, j ∈ κ]`. This is Mathlib's `Matrix.mvPolynomialX` with
coefficients in `ℤ`. -/
@[cluster_algebras "def_generic_matrix"]
noncomputable abbrev genericMatrix (ι κ : Type*) : Matrix ι κ (MvPolynomial (ι × κ) ℤ) :=
  Matrix.mvPolynomialX ι κ ℤ

/-- Evaluating the generic matrix at `x`, the ring homomorphism sending each `z_{ij}` to `x_{ij}`,
gives back `x`. -/
@[simp]
theorem genericMatrix_map_eval₂Hom {ι κ : Type*} (x : Matrix ι κ R) :
    (genericMatrix ι κ).map (MvPolynomial.eval₂Hom (Int.castRingHom R) fun p => x p.1 p.2) =
      x := by
  ext i j
  simp [genericMatrix, Matrix.mvPolynomialX_apply]

/-- **Every square minor of the generic matrix is nonzero**: if `|I| = |J|` then
`Δ_{I,J}(z) ≠ 0`. -/
theorem minor_genericMatrix_ne_zero {I : Finset ι} {J : Finset κ} (h : I.card = J.card) :
    minor (genericMatrix ι κ) I J ≠ 0 := by
  classical
  set eI := I.orderEmbOfFin rfl
  set eJ := J.orderEmbOfFin h.symm
  let x : Matrix ι κ ℤ := fun a b => if ∃ l, eI l = a ∧ eJ l = b then 1 else 0
  intro h0
  have h1 := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) fun p => x p.1 p.2) h0
  rw [RingHom.map_minor, genericMatrix_map_eval₂Hom, map_zero,
    minor_of_card_eq x rfl h.symm] at h1
  have hsub : x.submatrix eI eJ = 1 := by
    ext s t
    simp [x, one_apply]
  rw [hsub, det_one] at h1
  exact one_ne_zero h1

/-! ### Plücker coordinates -/

/-- The **Plücker coordinate** `P_J(z) = Δ_{[1,k],J}(z)` of a `k × m` matrix `z`, for a set `J` of
`k` columns: the minor on all the rows and the columns `J`. -/
@[cluster_algebras "def_plucker_coordinate"]
def pluckerCoord {k : ℕ} (z : Matrix (Fin k) κ R) (J : Finset κ) : R :=
  minor z Finset.univ J

/-- The increasing enumeration of all of `Fin k` is the identity. -/
theorem orderEmbOfFin_univ_fin {k : ℕ} (h : (Finset.univ : Finset (Fin k)).card = k) (i : Fin k) :
    (Finset.univ : Finset (Fin k)).orderEmbOfFin h i = i :=
  (congrFun (Finset.orderEmbOfFin_unique h (f := id) (by simp) strictMono_id) i).symm

/-- For `|J| = k` the Plücker coordinate is the maximal minor on the columns `J`. -/
theorem pluckerCoord_eq_det {k : ℕ} (z : Matrix (Fin k) κ R) {J : Finset κ} (hJ : J.card = k) :
    pluckerCoord z J = (z.submatrix id (J.orderEmbOfFin hJ)).det := by
  rw [pluckerCoord, minor_of_card_eq z (Finset.card_fin k) hJ]
  congr 2
  exact funext (orderEmbOfFin_univ_fin _)

/-- A ring homomorphism carries a Plücker coordinate of `z` to that of its image. -/
theorem RingHom.map_pluckerCoord (f : R →+* S) {k : ℕ} (z : Matrix (Fin k) κ R) (J : Finset κ) :
    f (pluckerCoord z J) = pluckerCoord (z.map f) J :=
  RingHom.map_minor f z _ J

/-- **Plücker coordinates of a `2 × m` matrix**, written out: for `a < b`,
`P_{ab}(z) = z_{1a} z_{2b} - z_{1b} z_{2a}` (0-based rows here). -/
theorem pluckerCoord_pair (z : Matrix (Fin 2) κ R) {a b : κ} (hab : a < b) :
    pluckerCoord z {a, b} = z 0 a * z 1 b - z 0 b * z 1 a := by
  have hcard : ({a, b} : Finset κ).card = 2 := Finset.card_pair hab.ne
  rw [pluckerCoord_eq_det z hcard, Matrix.det_fin_two]
  have hf := Finset.orderEmbOfFin_unique hcard (f := ![a, b])
    (fun x => by fin_cases x <;> simp) (by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all)
  simp [← congrFun hf 0, ← congrFun hf 1]

/-! ### The Grassmannian and its totally positive part -/

/-- The **Grassmannian** `Gr_{k,m}`: the set of `k`-dimensional complex linear subspaces of
`ℂ^m`. -/
@[cluster_algebras "def_grassmannian"]
def grassmannian (k m : ℕ) : Set (Submodule ℂ (Fin m → ℂ)) :=
  {V | Module.finrank ℂ V = k}

/-- The **totally positive Grassmannian** `Gr⁺_{k,m}`: the subspaces `V ∈ Gr_{k,m}` spanned by the
rows of a complex `k × m` matrix `z` whose rows form a basis of `V` and all of whose Plücker
coordinates `P_J(z)`, `|J| = k`, are positive real numbers. -/
@[cluster_algebras "def_tp_grassmannian"]
def tpGrassmannian (k m : ℕ) : Set (Submodule ℂ (Fin m → ℂ)) :=
  {V | V ∈ grassmannian k m ∧ ∃ z : Matrix (Fin k) (Fin m) ℂ,
    LinearIndependent ℂ z ∧ Submodule.span ℂ (Set.range z) = V ∧
      ∀ J : Finset (Fin m), J.card = k → ∃ r : ℝ, 0 < r ∧ pluckerCoord z J = r}

/-! ### Flag minors -/

/-- The first `k` rows `{0, …, k - 1}` of `Fin p`, the rows `[1,k]` in 1-based indexing. -/
def initialRows (p k : ℕ) : Finset (Fin p) := Finset.univ.filter fun i => (i : ℕ) < k

/-- A row is initial exactly when its index is below `k`. -/
@[simp]
theorem mem_initialRows {p k : ℕ} {i : Fin p} : i ∈ initialRows p k ↔ (i : ℕ) < k := by
  simp [initialRows]

/-- There are `k` initial rows when `k ≤ p`. -/
theorem card_initialRows {p k : ℕ} (hk : k ≤ p) : (initialRows p k).card = k := by
  rw [initialRows, Fin.card_filter_val_lt, min_eq_right hk]

/-- The **flag minor** `P_J(z) = Δ_{[1,|J|],J}(z)`: the minor on the first `|J|` rows and the
columns `J`. It is meaningful when `|J|` is at most the number of rows `p`; otherwise it is the
junk value of `minor`. -/
@[cluster_algebras "def_flag_minor"]
def flagMinor {p : ℕ} (z : Matrix (Fin p) κ R) (J : Finset κ) : R :=
  minor z (initialRows p J.card) J

/-- A ring homomorphism carries a flag minor of `z` to that of its image. -/
theorem RingHom.map_flagMinor (f : R →+* S) {p : ℕ} (z : Matrix (Fin p) κ R) (J : Finset κ) :
    f (flagMinor z J) = flagMinor (z.map f) J :=
  RingHom.map_minor f z _ J

/-- **The notations agree**: for a `k × m` matrix and `|J| = k` the flag minor is the Plücker
coordinate. -/
theorem flagMinor_eq_pluckerCoord {k : ℕ} (z : Matrix (Fin k) κ R) {J : Finset κ}
    (hJ : J.card = k) : flagMinor z J = pluckerCoord z J := by
  rw [flagMinor, pluckerCoord, hJ]
  congr
  ext i
  simp [initialRows]

/-- A complex `n × n` matrix is **flag totally positive** if every flag minor `P_J(z)` with `J` a
nonempty proper subset of `[1,n]` is a positive real number. -/
@[cluster_algebras "def_flag_totally_positive"]
def IsFlagTotallyPositive {n : ℕ} (z : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ J : Finset (Fin n), J.Nonempty → J ≠ Finset.univ → ∃ r : ℝ, 0 < r ∧ flagMinor z J = r

end ClusterAlgebras

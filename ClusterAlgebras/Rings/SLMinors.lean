/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.Defs
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Minors on `SL_k` and rescaling a row

Let `z` be the generic `k × k` matrix over `ℂ` and `π : ℂ[z] → ℂ[SL_k] = ℂ[z]/⟨det z - 1⟩` the
quotient map. Dividing one row `r` of `z` by `det z` gives a matrix of determinant `1` over the
field of fractions `ℂ(z)`, so substituting it for `z` defines a `ℂ`-algebra homomorphism
`s : ℂ[z] → ℂ(z)` which kills `det z - 1`, and hence factors through `π` as
`s̄ : ℂ[SL_k] → ℂ(z)`. By multilinearity of the determinant in the rows,
`s̄(π(Δ_{I,J}(z))) = (det z)^{-ε(I)} Δ_{I,J}(z)`, where `ε(I) = 1` if `r ∈ I` and `0` otherwise.

Since every square minor of `z` is a nonzero polynomial, it follows that no square minor
vanishes on `SL_k`: `π(Δ_{I,J}(z)) ≠ 0`.

## Main definitions

* `ClusterAlgebras.rowRescale r`: the substitution `s : ℂ[z] → ℂ(z)` of `z` by the matrix
  obtained from `z` by dividing row `r` by `det z`.
* `ClusterAlgebras.slRescale r`: the induced `ℂ`-algebra homomorphism `s̄ : ℂ[SL_k] → ℂ(z)`.

## Main results

* `ClusterAlgebras.minor_diagonal_mul`: `Δ_{I,J}(diag(d) M) = (∏_{i ∈ I} d_i) Δ_{I,J}(M)`.
* `ClusterAlgebras.slRescale_slQuot_minor`: `s̄(π(Δ_{I,J}(z))) = (det z)^{-ε(I)} Δ_{I,J}(z)`.
* `ClusterAlgebras.slQuot_minor_ne_zero`: `π(Δ_{I,J}(z)) ≠ 0` for `|I| = |J|`.

## Implementation notes

* FWZ rescale the first row and assume `k ≥ 1`. Any row `r : Fin k` works, and the
  existence of `r` is the only use of `k ≥ 1`; FWZ's homomorphism is `slRescale ⟨0, _⟩`.
* The rescaling formula holds for all `I` and `J`: when `|I| ≠ |J|` both sides vanish, the minor
  having junk value `0`.
* FWZ prove `slQuot_minor_ne_zero` for `k ≥ 1` by comparing top-degree homogeneous
  components. Here it is deduced from the rescaling instead: `s̄(π(Δ_{I,J}(z)))` is a power of
  `det z` times the nonzero polynomial `Δ_{I,J}(z)`, hence nonzero in the field `ℂ(z)`. For
  `k = 0` the polynomial `det z - 1` is `0`, so `π` is injective, and the statement holds without
  the hypothesis `k ≥ 1`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix MvPolynomial

/-! ### Minors of a product with a diagonal matrix -/

/-- **Rescaling rows multiplies minors.** For a diagonal matrix `diag(d)`,
`Δ_{I,J}(diag(d) M) = (∏_{i ∈ I} d_i) Δ_{I,J}(M)`: the determinant is multilinear in the rows. -/
theorem minor_diagonal_mul {R : Type*} [CommRing R] {ι κ : Type*} [LinearOrder ι]
    [LinearOrder κ] [Fintype ι] (d : ι → R) (M : Matrix ι κ R) (I : Finset ι) (J : Finset κ) :
    minor (diagonal d * M) I J = (∏ i ∈ I, d i) * minor M I J := by
  unfold minor
  split_ifs with h
  · have hsub : (diagonal d * M).submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h) =
        diagonal (fun l => d (I.orderEmbOfFin rfl l)) *
          M.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h) := by
      ext a b
      simp [diagonal_mul]
    rw [hsub, det_mul, det_diagonal]
    congr 1
    rw [← Finset.prod_coe_sort I]
    exact Fintype.prod_equiv (I.orderIsoOfFin rfl).toEquiv _ _ (fun l => by simp)
  · simp

/-! ### Nonvanishing of minors of the generic matrix -/

/-- The determinant of the generic `k × k` matrix over `ℂ` is a nonzero polynomial. -/
theorem det_complexGenericMatrix_ne_zero (k : ℕ) : (complexGenericMatrix k k).det ≠ 0 := by
  rw [complexGenericMatrix_eq_mvPolynomialX]
  exact det_mvPolynomialX_ne_zero _ _

/-- Every square minor of the generic matrix over `ℂ` is a nonzero polynomial. -/
theorem minor_complexGenericMatrix_ne_zero {p q : ℕ} {I : Finset (Fin p)} {J : Finset (Fin q)}
    (h : I.card = J.card) : minor (complexGenericMatrix p q) I J ≠ 0 := by
  rw [complexGenericMatrix, ← RingHom.map_minor]
  exact (map_ne_zero_iff _ (MvPolynomial.map_injective _ Int.cast_injective)).2
    (minor_genericMatrix_ne_zero h)

/-! ### Rescaling a row -/

/-- The substitution `s : ℂ[z] → ℂ(z)` which replaces the generic `k × k` matrix `z` by the matrix
obtained from `z` by dividing its row `r` by `det z`: `s(z_{rj}) = z_{rj} / det z` and
`s(z_{ij}) = z_{ij}` for `i ≠ r`. -/
noncomputable def rowRescale {k : ℕ} (r : Fin k) :
    ComplexPoly k k →ₐ[ℂ] FractionRing (ComplexPoly k k) :=
  aeval fun ij =>
    (if ij.1 = r then (algebraMap _ (FractionRing _) (complexGenericMatrix k k).det)⁻¹ else 1) *
      algebraMap (ComplexPoly k k) _ (X ij)

/-- `s` substitutes `diag(1, …, (det z)⁻¹, …, 1) z` for `z`, the entry `(det z)⁻¹` in row `r`. -/
theorem map_rowRescale_complexGenericMatrix {k : ℕ} (r : Fin k) :
    (complexGenericMatrix k k).map (rowRescale r) =
      diagonal (fun i => if i = r then
          (algebraMap _ (FractionRing _) (complexGenericMatrix k k).det)⁻¹ else 1) *
        (complexGenericMatrix k k).map (algebraMap _ _) := by
  ext i j
  simp [rowRescale, diagonal_mul]

/-- `s` divides the minor `Δ_{I,J}(z)` by `det z` if `r ∈ I`, and fixes it otherwise. -/
theorem rowRescale_minor {k : ℕ} (r : Fin k) (I J : Finset (Fin k)) :
    rowRescale r (minor (complexGenericMatrix k k) I J) =
      (if r ∈ I then (algebraMap _ (FractionRing _) (complexGenericMatrix k k).det)⁻¹ else 1) *
        algebraMap _ _ (minor (complexGenericMatrix k k) I J) := by
  rw [← AlgHom.coe_toRingHom, RingHom.map_minor, AlgHom.coe_toRingHom,
    map_rowRescale_complexGenericMatrix, minor_diagonal_mul, ← RingHom.map_minor,
    Finset.prod_ite_eq']

/-- `s(det z) = 1`. -/
theorem rowRescale_det {k : ℕ} (r : Fin k) : rowRescale r (complexGenericMatrix k k).det = 1 := by
  rw [← AlgHom.coe_toRingHom, RingHom.map_det, RingHom.mapMatrix_apply, AlgHom.coe_toRingHom,
    map_rowRescale_complexGenericMatrix, det_mul, det_diagonal, Finset.prod_ite_eq',
    if_pos (Finset.mem_univ r), ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact inv_mul_cancel₀ <| (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
    (det_complexGenericMatrix_ne_zero k)

/-- `s` vanishes on the ideal `⟨det z - 1⟩`. -/
theorem rowRescale_eq_zero_of_mem {k : ℕ} (r : Fin k) {f : ComplexPoly k k}
    (hf : f ∈ Ideal.span {detSubOne k}) : rowRescale r f = 0 := by
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hf
  rw [map_mul, detSubOne, map_sub, rowRescale_det, map_one, sub_self, mul_zero]

/-- **Rescaling a row on `SL_k`.** The `ℂ`-algebra homomorphism `s̄ : ℂ[SL_k] → ℂ(z)` induced by
the substitution `s = rowRescale r`, which kills `det z - 1`. -/
@[cluster_algebras "lem_sl_rescaling"]
noncomputable def slRescale {k : ℕ} (r : Fin k) : SLCoord k →ₐ[ℂ] FractionRing (ComplexPoly k k) :=
  Ideal.Quotient.liftₐ _ (rowRescale r) fun _ hf => rowRescale_eq_zero_of_mem r hf

/-- `s̄ ∘ π = s`. -/
@[simp]
theorem slRescale_slQuot {k : ℕ} (r : Fin k) (f : ComplexPoly k k) :
    slRescale r (slQuot k f) = rowRescale r f :=
  rfl

/-- **Rescaling a row on `SL_k`.** For every minor,
`s̄(π(Δ_{I,J}(z))) = (det z)^{-ε(I)} Δ_{I,J}(z)` in `ℂ(z)`, where `ε(I) = 1` if `r ∈ I` and
`ε(I) = 0` otherwise. -/
@[cluster_algebras "lem_sl_rescaling"]
theorem slRescale_slQuot_minor {k : ℕ} (r : Fin k) (I J : Finset (Fin k)) :
    slRescale r (slQuot k (minor (complexGenericMatrix k k) I J)) =
      algebraMap _ (FractionRing _) (complexGenericMatrix k k).det ^
          (-(if r ∈ I then 1 else 0 : ℤ)) *
        algebraMap _ _ (minor (complexGenericMatrix k k) I J) := by
  rw [slRescale_slQuot, rowRescale_minor]
  split_ifs <;> simp

/-! ### Minors do not vanish on `SL_k` -/

/-- **Minors do not vanish on `SL_k`.** For `|I| = |J|`, `π(Δ_{I,J}(z)) ≠ 0` in `ℂ[SL_k]`. -/
@[cluster_algebras "lem_sl_minor_nonzero"]
theorem slQuot_minor_ne_zero {k : ℕ} {I J : Finset (Fin k)} (h : I.card = J.card) :
    slQuot k (minor (complexGenericMatrix k k) I J) ≠ 0 := by
  intro h0
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [slQuot, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
      show detSubOne 0 = 0 by simp [detSubOne], Ideal.span_singleton_eq_bot.2 rfl,
      Ideal.mem_bot] at h0
    exact minor_complexGenericMatrix_ne_zero h h0
  · have h1 := congrArg (slRescale (⟨0, hk⟩ : Fin k)) h0
    rw [slRescale_slQuot_minor, map_zero] at h1
    have hinj := IsFractionRing.injective (ComplexPoly k k) (FractionRing (ComplexPoly k k))
    exact mul_ne_zero
      (zpow_ne_zero _ ((map_ne_zero_iff _ hinj).2 (det_complexGenericMatrix_ne_zero k)))
      ((map_ne_zero_iff _ hinj).2 (minor_complexGenericMatrix_ne_zero h)) h1

end ClusterAlgebras

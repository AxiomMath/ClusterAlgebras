/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.Defs
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Invariance of flag minors and Plücker coordinates

Left multiplication by a matrix `g` acts on the minors of a matrix `z` on its first rows through
the leading block of `g`. Two consequences are recorded here for the generic matrix `z` over `ℂ`
and the left substitution `σ_g`, which substitutes `gz` for `z`.

* If `u` is lower unitriangular, the rows `[1, r]` of `uz` are combinations of the rows `[1, r]`
  of `z` by the leading `r × r` block of `u`, which is unitriangular; so every flag minor is
  fixed: `σ_u(P_J(z)) = P_J(z)`, and `P_J(z) ∈ ℂ[z]^{U}`.
* If `z` is `a × b` and `g` is `a × a`, the columns `J` of `gz` are `g` times those of `z`, so
  `σ_g(P_J(z)) = det(g) P_J(z)`; in particular every Plücker coordinate lies in the Plücker ring
  `R_{a,b} = ℂ[z]^{SL_a}`.

## Main results

* `ClusterAlgebras.flagMinor_mul_of_lowerUnitriangular`: `P_J(uz) = P_J(z)` for a lower
  unitriangular `u` over any commutative ring.
* `ClusterAlgebras.leftSubst_flagMinor`, `ClusterAlgebras.flagMinor_mem_invariants`:
  `σ_u(P_J(z)) = P_J(z)` for `u ∈ U_p`, and `P_J(z) ∈ ℂ[z]^{U_p}`.
* `ClusterAlgebras.pluckerCoord_mul`: `P_J(gz) = det(g) P_J(z)` over any commutative ring.
* `ClusterAlgebras.leftSubst_pluckerCoord`, `ClusterAlgebras.pluckerCoord_mem_pluckerRing`:
  `σ_g(P_J(z)) = det(g) P_J(z)`, and `P_J(z) ∈ R_{a,b}`.

## Implementation notes

* The flag-minor invariance is usually stated for the generic `k × k` matrix and a nonempty
  `J`. Neither is needed: the argument works for the generic `p × q` matrix and any `J`. For
  `J = ∅` the flag minor is the empty determinant `1`, and for `|J| > p` it is the junk value `0`
  of `minor`; both are fixed.
* Likewise the Plücker identity holds for every set `J` of columns, not only those with `a`
  elements: when `|J| ≠ a` both sides are the junk value `0`.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {R : Type*} [CommRing R] {κ : Type*} [LinearOrder κ]

/-! ### Flag minors and lower unitriangular matrices -/

/-- The increasing enumeration of the first `r` rows of `Fin p` is `Fin.castLE`. -/
private theorem orderEmbOfFin_initialRows {p r : ℕ} (hr : r ≤ p)
    (h : (initialRows p r).card = r) (i : Fin r) :
    (initialRows p r).orderEmbOfFin h i = Fin.castLE hr i :=
  (congrFun (Finset.orderEmbOfFin_unique h (f := Fin.castLE hr)
    (fun x => by simp [initialRows]) (Fin.strictMono_castLE hr)) i).symm

/-- A minor on the first `r` rows is the determinant of the submatrix on the rows `Fin.castLE`. -/
private theorem minor_initialRows {p r : ℕ} (hr : r ≤ p) (z : Matrix (Fin p) κ R)
    {J : Finset κ} (hJ : J.card = r) :
    minor z (initialRows p r) J = (z.submatrix (Fin.castLE hr) (J.orderEmbOfFin hJ)).det := by
  rw [minor_of_card_eq z (card_initialRows hr) hJ]
  congr 2
  exact funext (orderEmbOfFin_initialRows hr _)

/-- **Flag minors are invariant under lower unitriangular matrices**: if `u` is lower
unitriangular (`u_{ii} = 1`, and `u_{ij} = 0` for `i < j`), then `P_J(uz) = P_J(z)`. -/
theorem flagMinor_mul_of_lowerUnitriangular {p : ℕ} {u : Matrix (Fin p) (Fin p) R}
    (hdiag : ∀ i, u i i = 1) (hlow : ∀ i j, i < j → u i j = 0) (z : Matrix (Fin p) κ R)
    (J : Finset κ) : flagMinor (u * z) J = flagMinor z J := by
  by_cases hr : J.card ≤ p
  · rw [flagMinor, flagMinor, minor_initialRows hr _ rfl, minor_initialRows hr _ rfl]
    set c : Fin J.card → Fin p := Fin.castLE hr
    set e := J.orderEmbOfFin rfl
    have hsub : (u * z).submatrix c e = u.submatrix c c * z.submatrix c e := by
      ext s t
      simp only [submatrix_apply, mul_apply]
      symm
      refine Fintype.sum_of_injective c (Fin.castLE_injective hr) _ _ ?_ fun _ => rfl
      intro l hl
      have hlt : c s < l := Fin.lt_def.2 (s.isLt.trans_le (not_lt.1 fun h => hl ⟨⟨l, h⟩, rfl⟩))
      rw [hlow _ _ hlt, zero_mul]
    have hdet : (u.submatrix c c).det = 1 := by
      have hbt : (u.submatrix c c).BlockTriangular OrderDual.toDual := fun i j hij =>
        hlow _ _ (Fin.strictMono_castLE hr (OrderDual.toDual_lt_toDual.mp hij))
      rw [det_of_lowerTriangular _ hbt]
      simp [hdiag]
    rw [hsub, det_mul, hdet, one_mul]
  · have h : (initialRows p J.card).card ≠ J.card := by
      rw [initialRows, Fin.card_filter_val_lt]; omega
    rw [flagMinor, flagMinor, minor, minor, dif_neg (Ne.symm h), dif_neg (Ne.symm h)]

/-- **Flag minors are invariant under lower unitriangular matrices**: for the generic `p × q`
matrix `z` over `ℂ`, `u ∈ U_p` and any set `J` of columns, `σ_u(P_J(z)) = P_J(z)`. -/
@[cluster_algebras "lem_flag_minor_unipotent_invariant"]
theorem leftSubst_flagMinor {p q : ℕ} {u : Matrix (Fin p) (Fin p) ℂ}
    (hu : u ∈ lowerUnitriangular p) (J : Finset (Fin q)) :
    leftSubst q u (flagMinor (complexGenericMatrix p q) J) =
      flagMinor (complexGenericMatrix p q) J := by
  have := RingHom.map_flagMinor (leftSubst q u).toRingHom (complexGenericMatrix p q) J
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this, map_leftSubst_complexGenericMatrix]
  exact flagMinor_mul_of_lowerUnitriangular (fun i => by simp [hu.1 i])
    (fun i j hij => by simp [hu.2 i j hij]) _ J

/-- Every flag minor of the generic `p × q` matrix over `ℂ` lies in `ℂ[z]^{U_p}`. -/
@[cluster_algebras "lem_flag_minor_unipotent_invariant"]
theorem flagMinor_mem_invariants {p q : ℕ} (J : Finset (Fin q)) :
    flagMinor (complexGenericMatrix p q) J ∈ invariants q (lowerUnitriangular p) :=
  fun _ hu => leftSubst_flagMinor hu J

/-! ### Plücker coordinates and left multiplication -/

/-- **Plücker coordinates are multiplied by the determinant**: for a `k × k` matrix `g` and a
`k × m` matrix `z`, `P_J(gz) = det(g) P_J(z)`. -/
theorem pluckerCoord_mul {k : ℕ} (g : Matrix (Fin k) (Fin k) R) (z : Matrix (Fin k) κ R)
    (J : Finset κ) : pluckerCoord (g * z) J = g.det * pluckerCoord z J := by
  by_cases hJ : J.card = k
  · rw [pluckerCoord_eq_det _ hJ, pluckerCoord_eq_det _ hJ, ← det_mul]
    congr 1
  · have h : J.card ≠ (Finset.univ : Finset (Fin k)).card := by simpa using hJ
    rw [pluckerCoord, pluckerCoord, minor, minor, dif_neg h, dif_neg h, mul_zero]

/-- **Plücker coordinates are `SL_a`-invariant**: for the generic `a × b` matrix `z` over `ℂ`, a
complex `a × a` matrix `g` and any set `J` of columns, `σ_g(P_J(z)) = det(g) P_J(z)`. -/
@[cluster_algebras "lem_plucker_sl_invariant"]
theorem leftSubst_pluckerCoord {a b : ℕ} (g : Matrix (Fin a) (Fin a) ℂ) (J : Finset (Fin b)) :
    leftSubst b g (pluckerCoord (complexGenericMatrix a b) J) =
      algebraMap ℂ (ComplexPoly a b) g.det * pluckerCoord (complexGenericMatrix a b) J := by
  have := RingHom.map_pluckerCoord (leftSubst b g).toRingHom (complexGenericMatrix a b) J
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this, map_leftSubst_complexGenericMatrix, pluckerCoord_mul, RingHom.map_det]
  rfl

/-- Every Plücker coordinate of the generic `a × b` matrix over `ℂ` lies in the Plücker ring
`R_{a,b}`. -/
@[cluster_algebras "lem_plucker_sl_invariant"]
theorem pluckerCoord_mem_pluckerRing {a b : ℕ} (J : Finset (Fin b)) :
    pluckerCoord (complexGenericMatrix a b) J ∈ pluckerRing a b := by
  intro g hg
  rw [leftSubst_pluckerCoord, Set.mem_setOf_eq.mp hg, map_one, one_mul]

end ClusterAlgebras

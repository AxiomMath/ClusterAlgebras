/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.Defs
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Minors of a generic matrix are irreducible

Let `z` be the generic `p × q` matrix over `ℂ`. Every minor `Δ_{I,J}(z)` with `I`, `J` nonempty of
the same size is an irreducible element of `ℂ[z]`; two different such minors do not divide one
another; and if a subring `R ⊆ ℂ[z]` containing `ℂ` contains a minor `D` and an element `f` that
`D` does not divide in `ℂ[z]`, then no prime element of `R` divides both `D` and `f` in `R`.

## Main results

* `ClusterAlgebras.irreducible_det_X_of_injective`: the determinant of a square matrix whose
  entries are pairwise distinct indeterminates is irreducible, over any integral domain.
* `ClusterAlgebras.irreducible_minor_complexGenericMatrix`: minors of the generic matrix are
  irreducible.
* `ClusterAlgebras.not_minor_complexGenericMatrix_dvd`: distinct minors do not divide one another.
* `ClusterAlgebras.not_dvd_of_prime_dvd_minor_complexGenericMatrix`: a minor and a non-multiple
  have no common prime factor in a subring containing `ℂ`.

Each result is first proved for the matrix `Matrix.mvPolynomialX ι κ K` of indeterminates over an
integral domain `K`, rows and columns indexed by linearly ordered types, and then read off for
`complexGenericMatrix p q`.

## Implementation notes

* **Irreducibility of the determinant** is proved by induction on the size, not by the degree
  argument of [FWZ]. Expanding along the first row, the determinant of an `(n+1) × (n+1)` matrix
  `N` of distinct indeterminates is `z₀₀ a + b` with `a` the complementary minor of the corner
  entry and `b` the determinant of `N` with its corner entry replaced by `0`; neither `a` nor `b`
  involves `z₀₀`. As a polynomial in `z₀₀` over the remaining indeterminates it has degree one, so
  it is irreducible as soon as `a` and `b` are relatively prime
  (`Polynomial.irreducible_C_mul_X_add_C`). For `n = 0`, `a = 1`. For `n ≥ 1`, `a` is irreducible
  by induction, and does not divide `b`: at the permutation matrix of the transposition of the
  first two rows, `b` evaluates to `-1` while `a` evaluates to `0`, its first row vanishing.
* **Distinct minors do not divide one another** by evaluating at a partial identity: the `0`/`1`
  matrix with `1` exactly at the positions `(i_s, j_s)` of `I` and `J` listed increasingly sends
  `Δ_{I,J}(z)` to `1` and `Δ_{I',J'}(z)` to `0` whenever `I' ⊄ I` or `J' ⊄ J`. If instead
  `I ⊆ I'` and `J ⊆ J'`, irreducibility makes a divisibility `Δ_{I,J} ∣ Δ_{I',J'}` symmetric, and
  the evaluation at the partial identity of `(I, J)` rules it out. This replaces [FWZ]'s comparison
  of the indeterminates occurring in the two minors.
* The second statement does not assume `I'` nonempty, as [FWZ] does: the empty minor `1` is not
  divisible by a minor of positive size.
* The subring of the third statement is a `ℂ`-subalgebra of `ℂ[z]`, which is exactly a subring
  containing `ℂ`. Its minor need not be nonempty: the empty minor is `1`, which divides every `f`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapter 6*;
  D. Serre, *Matrices*, for the irreducibility of the determinant.
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial Matrix

variable {K σ : Type*} [CommRing K]

/-! ### The determinant of a matrix of distinct indeterminates -/

/-- The matrix `(z_{e(i,j)})` of indeterminates with its `(0,0)` entry replaced by `0`, over the
polynomial ring in the indeterminates other than `z_{e(0,0)}`. -/
private noncomputable def offCornerMatrix {n : ℕ} (e : Fin (n + 1) × Fin (n + 1) → σ)
    (he : e.Injective) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial {w // w ≠ e (0, 0)} K) :=
  Matrix.of fun i j => if h : (i, j) = (0, 0) then 0 else X ⟨e (i, j), fun h' => h (he h')⟩

/-- The determinant of a matrix `N = (z_{e(i,j)})` of distinct indeterminates is irreducible as
soon as the complementary minor `a` of its corner entry is nonzero and relatively prime to the
determinant `b` of `N` with its corner entry replaced by `0`: viewed as a polynomial in
`z_{e(0,0)}`, `det N = a z_{e(0,0)} + b`. -/
private theorem irreducible_det_X_of_isRelPrime [IsDomain K] {n : ℕ}
    (e : Fin (n + 1) × Fin (n + 1) → σ) (he : e.Injective)
    (ha : ((offCornerMatrix (K := K) e he).submatrix Fin.succ Fin.succ).det ≠ 0)
    (h : IsRelPrime ((offCornerMatrix (K := K) e he).submatrix Fin.succ Fin.succ).det
      (offCornerMatrix e he).det) :
    Irreducible (Matrix.of fun i j => (X (e (i, j)) : MvPolynomial σ K)).det := by
  classical
  set v := e (0, 0)
  let iso : MvPolynomial σ K ≃ₐ[K] Polynomial (MvPolynomial {w // w ≠ v} K) :=
    (renameEquiv K (Equiv.optionSubtypeNe v).symm).trans (optionEquivLeft K _)
  have hX : ∀ i j, iso (X (e (i, j))) = Polynomial.C (offCornerMatrix e he i j) +
      if (i, j) = (0, 0) then Polynomial.X else 0 := by
    intro i j
    by_cases hij : (i, j) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
      simp [iso, offCornerMatrix, v]
    · have hne : e (i, j) ≠ v := fun h' => hij (he h')
      simp only [Prod.mk.injEq] at hij
      simp [iso, offCornerMatrix, hij, Equiv.optionSubtypeNe_symm_of_ne hne]
  have hsub : ∀ k : Fin n → Fin (n + 1),
      ((iso.mapMatrix (Matrix.of fun i j => (X (e (i, j)) : MvPolynomial σ K))).submatrix
        Fin.succ k).det = Polynomial.C ((offCornerMatrix e he).submatrix Fin.succ k).det := by
    intro k
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [hX, Fin.succ_ne_zero]
  have hdet : iso (Matrix.of fun i j => (X (e (i, j)) : MvPolynomial σ K)).det =
      Polynomial.C ((offCornerMatrix e he).submatrix Fin.succ Fin.succ).det * Polynomial.X +
        Polynomial.C (offCornerMatrix e he).det := by
    rw [AlgEquiv.map_det, det_succ_row_zero, det_succ_row_zero (offCornerMatrix e he)]
    simp only [hsub, Fin.sum_univ_succ, map_add, map_sum, map_mul, map_pow, map_neg, map_one]
    simp [hX, offCornerMatrix]
  rw [← MulEquiv.irreducible_iff iso, hdet]
  exact Polynomial.irreducible_C_mul_X_add_C ha h

/-- **The determinant of a square matrix of distinct indeterminates is irreducible**: for an
injective `e : [0, n] × [0, n] → σ`, `det (z_{e(i,j)})` is irreducible in `K[z_s : s ∈ σ]`, over
any integral domain `K`. -/
theorem irreducible_det_X_of_injective [IsDomain K] {n : ℕ}
    (e : Fin (n + 1) × Fin (n + 1) → σ) (he : e.Injective) :
    Irreducible (Matrix.of fun i j => (X (e (i, j)) : MvPolynomial σ K)).det := by
  classical
  induction n generalizing σ with
  | zero =>
    exact irreducible_det_X_of_isRelPrime e he (by simp) (by simp [isRelPrime_one_left])
  | succ n ih =>
    set e' : Fin (n + 1) × Fin (n + 1) → {w // w ≠ e (0, 0)} := fun ij =>
      ⟨e (ij.1.succ, ij.2.succ), fun h => by simpa [Fin.succ_ne_zero] using he h⟩
    have he' : e'.Injective := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      simpa [e', he.eq_iff, Fin.succ_inj] using h
    have hsub : (offCornerMatrix (K := K) e he).submatrix Fin.succ Fin.succ =
        Matrix.of fun i j => X (e' (i, j)) := by
      ext i j
      simp [offCornerMatrix, e', Fin.succ_ne_zero]
    have ha := ih e' he'
    rw [← hsub] at ha
    refine irreducible_det_X_of_isRelPrime e he ha.ne_zero
      (ha.isRelPrime_iff_not_dvd.2 fun hdvd => ?_)
    set s : Equiv.Perm (Fin (n + 2)) := Equiv.swap 0 1
    let f : {w // w ≠ e (0, 0)} → K := fun w => if ∃ i, e (i, s i) = w.1 then 1 else 0
    have hT : (offCornerMatrix e he).map (eval f) = s.permMatrix K := by
      ext i j
      by_cases hij : (i, j) = (0, 0)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
        simp [offCornerMatrix, s, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
          Equiv.swap_apply_left]
      · simp only [Prod.mk.injEq] at hij
        simp [offCornerMatrix, hij, f, he.eq_iff, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    have h2 := map_dvd (eval f) hdvd
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      ← Matrix.submatrix_map, hT, det_permutation] at h2
    have h0 : ((s.permMatrix K).submatrix Fin.succ Fin.succ).det = 0 := by
      refine det_eq_zero_of_row_eq_zero 0 fun j => ?_
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, s, (Fin.succ_ne_zero j).symm]
    rw [h0, zero_dvd_iff] at h2
    simp [s] at h2

/-! ### Minors of the matrix of indeterminates -/

variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]

/-- A minor `Δ_{I,J}` of the matrix `(z_{ij})` of indeterminates over an integral domain, with `I`
nonempty and `|I| = |J|`, is irreducible. -/
theorem irreducible_minor_mvPolynomialX [IsDomain K] {I : Finset ι} {J : Finset κ}
    (hI : I.Nonempty) (h : I.card = J.card) :
    Irreducible (minor (mvPolynomialX ι κ K) I J) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hI.card_pos.ne'
  rw [minor_of_card_eq _ hn (h ▸ hn)]
  convert irreducible_det_X_of_injective (K := K)
    (fun st : Fin (n + 1) × Fin (n + 1) =>
      (I.orderEmbOfFin hn st.1, J.orderEmbOfFin (h ▸ hn) st.2))
    ((I.orderEmbOfFin hn).injective.prodMap (J.orderEmbOfFin (h ▸ hn)).injective) using 2
  ext s t
  simp [mvPolynomialX_apply]

/-- If `I' ⊄ I` or `J' ⊄ J`, then `Δ_{I',J'}(z)` does not divide `Δ_{I,J}(z)` for `|I| = |J|`:
at the `0`/`1` matrix with `1` exactly at the positions `(i_s, j_s)`, `I` and `J` listed
increasingly, the first minor vanishes and the second is `1`. -/
theorem not_minor_mvPolynomialX_dvd_of_not_subset [Nontrivial K] {I I' : Finset ι}
    {J J' : Finset κ} (h : I.card = J.card) (h' : ¬I' ⊆ I ∨ ¬J' ⊆ J) :
    ¬minor (mvPolynomialX ι κ K) I' J' ∣ minor (mvPolynomialX ι κ K) I J := by
  classical
  set eI := I.orderEmbOfFin rfl
  set eJ := J.orderEmbOfFin h.symm
  let x : Matrix ι κ K := fun a b => if ∃ l, eI l = a ∧ eJ l = b then 1 else 0
  have hx : (mvPolynomialX ι κ K).map (eval fun ab => x ab.1 ab.2) = x := by
    ext a b
    simp [mvPolynomialX_apply]
  have h1 : minor x I J = 1 := by
    rw [minor_of_card_eq x rfl h.symm]
    convert det_one (n := Fin I.card) (R := K) using 2
    ext s t
    simp only [submatrix_apply, x, one_apply]
    rcases eq_or_ne s t with rfl | hst
    · simp [eI, eJ]
    · rw [if_neg hst, if_neg]
      rintro ⟨l, hl1, hl2⟩
      exact hst ((eI.injective hl1).symm.trans (eJ.injective hl2))
  have h0 : minor x I' J' = 0 := by
    unfold minor
    split_ifs with hc
    · rcases h' with hI | hJ
      · obtain ⟨i, hi, hiI⟩ := Finset.not_subset.1 hI
        obtain ⟨s, rfl⟩ : i ∈ Set.range (I'.orderEmbOfFin rfl) := by
          rwa [Finset.range_orderEmbOfFin]
        refine det_eq_zero_of_row_eq_zero s fun t => ?_
        simp only [submatrix_apply, x]
        rw [if_neg]
        rintro ⟨l, hl, -⟩
        exact hiI (hl ▸ I.orderEmbOfFin_mem rfl l)
      · obtain ⟨j, hj, hjJ⟩ := Finset.not_subset.1 hJ
        obtain ⟨t, rfl⟩ : j ∈ Set.range (J'.orderEmbOfFin hc) := by
          rwa [Finset.range_orderEmbOfFin]
        refine det_eq_zero_of_column_eq_zero t fun s => ?_
        simp only [submatrix_apply, x]
        rw [if_neg]
        rintro ⟨l, -, hl⟩
        exact hjJ (hl ▸ J.orderEmbOfFin_mem h.symm l)
    · rfl
  intro hd
  have := map_dvd (eval fun ab : ι × κ => x ab.1 ab.2) hd
  rw [RingHom.map_minor, RingHom.map_minor, hx, h0, h1, zero_dvd_iff] at this
  exact one_ne_zero this

/-- **Distinct minors of the matrix of indeterminates do not divide one another**: if `I` is
nonempty, `|I| = |J|`, `|I'| = |J'|` and `(I, J) ≠ (I', J')`, then `Δ_{I,J}(z) ∤ Δ_{I',J'}(z)`,
over any integral domain. -/
theorem not_minor_mvPolynomialX_dvd [IsDomain K] {I I' : Finset ι} {J J' : Finset κ}
    (hI : I.Nonempty) (h : I.card = J.card) (h' : I'.card = J'.card)
    (hne : (I, J) ≠ (I', J')) :
    ¬minor (mvPolynomialX ι κ K) I J ∣ minor (mvPolynomialX ι κ K) I' J' := by
  intro hd
  by_cases hs : I ⊆ I' ∧ J ⊆ J'
  · refine not_minor_mvPolynomialX_dvd_of_not_subset h ?_
      ((irreducible_minor_mvPolynomialX hI h).dvd_symm
        (irreducible_minor_mvPolynomialX (hI.mono hs.1) h') hd)
    by_contra hc
    push Not at hc
    exact hne (Prod.ext (hs.1.antisymm hc.1) (hs.2.antisymm hc.2))
  · exact not_minor_mvPolynomialX_dvd_of_not_subset h' (not_and_or.1 hs) hd

/-- **A minor and a non-multiple have no common prime factor in a subring**: if a `K`-subalgebra
`R` of `K[z]` contains a minor `D = Δ_{I,J}(z)`, `|I| = |J|`, and an element `f` not divisible by
`D` in `K[z]`, then no prime element of `R` divides both `D` and `f` in `R`. -/
theorem not_dvd_of_prime_dvd_minor_mvPolynomialX [IsDomain K]
    {R : Subalgebra K (MvPolynomial (ι × κ) K)} {I : Finset ι} {J : Finset κ}
    (h : I.card = J.card) (hD : minor (mvPolynomialX ι κ K) I J ∈ R)
    {f : MvPolynomial (ι × κ) K} (hf : f ∈ R) (hDf : ¬minor (mvPolynomialX ι κ K) I J ∣ f)
    {π : R} (hπ : Prime π) (hπD : π ∣ ⟨_, hD⟩) : ¬π ∣ ⟨f, hf⟩ := by
  intro hπf
  rcases I.eq_empty_or_nonempty with rfl | hI
  · obtain rfl : J = ∅ := Finset.card_eq_zero.1 h.symm
    exact hDf (by simp [minor])
  have hunit : ∀ x : R, IsUnit (x : MvPolynomial (ι × κ) K) → IsUnit x := by
    intro x hx
    obtain ⟨r, hr, hxr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hx
    have : x = algebraMap K R r := Subtype.ext (by simpa [MvPolynomial.algebraMap_eq] using hxr)
    exact this ▸ hr.map _
  obtain ⟨u, hu⟩ := hπD
  have hu' : minor (mvPolynomialX ι κ K) I J = π * u := by
    simpa using congrArg Subtype.val hu
  rcases (irreducible_minor_mvPolynomialX hI h).isUnit_or_isUnit hu' with h1 | h1
  · exact hπ.not_unit (hunit _ h1)
  · have : (⟨_, hD⟩ : R) ∣ π := by rw [← (hunit _ h1).dvd_mul_right, ← hu]
    exact hDf (by simpa using map_dvd R.val (this.trans hπf))

/-! ### Minors of the generic matrix over `ℂ` -/

/-- **Minors of a generic matrix are irreducible**: for the generic `p × q` matrix `z` over `ℂ`
and nonempty `I ⊆ [1, p]`, `J ⊆ [1, q]` with `|I| = |J|`, `Δ_{I,J}(z)` is irreducible in
`ℂ[z]`. -/
@[cluster_algebras "lem_minor_irreducible"]
theorem irreducible_minor_complexGenericMatrix {p q : ℕ} {I : Finset (Fin p)}
    {J : Finset (Fin q)} (hI : I.Nonempty) (h : I.card = J.card) :
    Irreducible (minor (complexGenericMatrix p q) I J) := by
  rw [complexGenericMatrix_eq_mvPolynomialX]
  exact irreducible_minor_mvPolynomialX hI h

/-- **Distinct minors do not divide one another**: for the generic `p × q` matrix `z` over `ℂ`
and pairs `(I, J) ≠ (I', J')` with `I` nonempty, `|I| = |J|` and `|I'| = |J'|`,
`Δ_{I,J}(z)` does not divide `Δ_{I',J'}(z)` in `ℂ[z]`. -/
@[cluster_algebras "lem_minors_not_divide"]
theorem not_minor_complexGenericMatrix_dvd {p q : ℕ} {I I' : Finset (Fin p)}
    {J J' : Finset (Fin q)} (hI : I.Nonempty) (h : I.card = J.card) (h' : I'.card = J'.card)
    (hne : (I, J) ≠ (I', J')) :
    ¬minor (complexGenericMatrix p q) I J ∣ minor (complexGenericMatrix p q) I' J' := by
  rw [complexGenericMatrix_eq_mvPolynomialX]
  exact not_minor_mvPolynomialX_dvd hI h h' hne

/-- **A minor and a non-multiple have no common prime factor in a subring**: let `R ⊆ ℂ[z]` be a
subring containing `ℂ`, `D = Δ_{I,J}(z)` a minor of the generic `p × q` matrix lying in `R`, and
`f ∈ R` not divisible by `D` in `ℂ[z]`. Then a prime element `π` of `R` dividing `D` in `R` does
not divide `f` in `R`. -/
@[cluster_algebras "lem_minor_coprime_subring"]
theorem not_dvd_of_prime_dvd_minor_complexGenericMatrix {p q : ℕ}
    {R : Subalgebra ℂ (ComplexPoly p q)} {I : Finset (Fin p)} {J : Finset (Fin q)}
    (h : I.card = J.card) (hD : minor (complexGenericMatrix p q) I J ∈ R)
    {f : ComplexPoly p q} (hf : f ∈ R) (hDf : ¬minor (complexGenericMatrix p q) I J ∣ f)
    {π : R} (hπ : Prime π) (hπD : π ∣ ⟨_, hD⟩) : ¬π ∣ ⟨f, hf⟩ := by
  revert hD hπD
  rw [complexGenericMatrix_eq_mvPolynomialX] at hDf ⊢
  intro hD hπD
  exact not_dvd_of_prime_dvd_minor_mvPolynomialX h hD hf hDf hπ hπD

end ClusterAlgebras

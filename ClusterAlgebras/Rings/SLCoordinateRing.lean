/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.MinorIrreducible
public import ClusterAlgebras.Rings.SLMinors
public import ClusterAlgebras.Rings.FreeTuple
public import ClusterAlgebras.Rings.InvariantUFD
public import ClusterAlgebras.Rings.PolynomialInvariants
public import ClusterAlgebras.Rings.Elementary
public import ClusterAlgebras.Rings.External
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The coordinate ring of `SL_k`

Let `z` be the generic `k × k` matrix over `ℂ`, `I = ⟨det z - 1⟩ ⊆ ℂ[z]`, and
`π : ℂ[z] → ℂ[SL_k] = ℂ[z]/I` the quotient map. This file proves three facts about `ℂ[SL_k]`.

First, `I` is a prime ideal, so `ℂ[SL_k]` is an integral domain. For `k ≥ 1` the polynomial `det z`
is irreducible and homogeneous of degree `k`; if `det z - 1 = gh`, then comparing the homogeneous
components of top degree gives `det z = g_top h_top`, so one of `g_top`, `h_top` is a nonzero
constant and the corresponding factor is a unit. Hence `det z - 1` is irreducible, and prime since
`ℂ[z]` is factorial. For `k = 0` the determinant of the empty matrix is `1`, so `I = 0`.

Second, algebraic independence passes from `ℂ[z]` to `ℂ[SL_k]`: if `f₁, …, f_r` are minors of `z`
such that `f₁, …, f_r, det z` are algebraically independent, then so are
`π(f₁), …, π(f_r)`. The rescaling `s̄ : ℂ[SL_k] → ℂ(z)` of the first row sends `π(fᵢ)` to
`gᵢ = (det z)^{-εᵢ} fᵢ`, and `g₁, …, g_r, det z` generate the same subfield of `ℂ(z)` as
`f₁, …, f_r, det z`, of transcendence degree `r + 1`; so they are algebraically independent.

Third, for `k ≥ 2` the ring `ℂ[SL_k]^U` of `U`-invariants is factorial. For `i > j` the
one-parameter substitution `Θ_{ij}` fixes `det z`, hence induces
`Θ̄_{ij} : ℂ[SL_k] → ℂ[SL_k][t]`, the identity at `t = 0`. Evaluating at `t = s` gives the left
substitution by the elementary matrix `E_{ij}(s)`, and these generate `U_k`; since a nonzero
polynomial over a domain has finitely many roots, `ℂ[SL_k]^U` is the ring of elements fixed by
every `Θ̄_{ij}`, which is factorial because `ℂ[SL_k]` is.

## Main definitions

* `ClusterAlgebras.slOneParamSubst i j hij`: the homomorphism `Θ̄_{ij} : ℂ[SL_k] → ℂ[SL_k][t]`
  induced by the one-parameter substitution `Θ_{ij}`, for `i ≠ j`.

## Main results

* `ClusterAlgebras.irreducible_sub_one_of_isHomogeneous`: if `φ` is an irreducible homogeneous
  polynomial of positive degree over a domain, then `φ - 1` is irreducible.
* `ClusterAlgebras.isPrime_span_detSubOne`: `⟨det z - 1⟩` is a prime ideal, and the instance
  `ClusterAlgebras.instIsDomainSLCoord` that `ℂ[SL_k]` is a domain.
* `ClusterAlgebras.algebraicIndependent_slQuot_comp`: images in `ℂ[SL_k]` of minors that are
  algebraically independent together with `det z` are algebraically independent.
* `ClusterAlgebras.slUInvariants_eq_fixedSubalgebra`: `ℂ[SL_k]^U` is the subalgebra of elements
  fixed by every `Θ̄_{ij}`, `i > j`.
* `ClusterAlgebras.uniqueFactorizationMonoid_slUInvariants`: `ℂ[SL_k]^U` is factorial.

## Implementation notes

* FWZ state the primality of `⟨det z - 1⟩` for `k ≥ 1`. For `k = 0` the ideal is `0`,
  which is prime since `ℂ[z] = ℂ` is a domain, so the statement is made for every `k`.
* FWZ state the passage of algebraic independence to `ℂ[SL_k]` for `k ≥ 1`. For `k = 0`
  its hypothesis fails, `det z = 1` being algebraic over `ℂ`, so no assumption on `k` is made.
  The tuple `f₁, …, f_r, det z` is `Fin.snoc f (det z)`.
* That `ℂ[SL_k]^U` is a subring of `ℂ[SL_k]` containing `ℂ` is the statement that it is a
  `ℂ`-subalgebra, which is how `slUInvariants` is defined.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6.
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial Matrix

/-! ### Top-degree homogeneous components -/

section Homogeneous

variable {σ R : Type*}

/-- The homogeneous component of degree `deg φ + deg ψ` of `φ ψ` is the product of the
homogeneous components of top degree of `φ` and `ψ`. -/
theorem homogeneousComponent_totalDegree_add_mul [CommSemiring R] (φ ψ : MvPolynomial σ R) :
    homogeneousComponent (φ.totalDegree + ψ.totalDegree) (φ * ψ) =
      homogeneousComponent φ.totalDegree φ * homogeneousComponent ψ.totalDegree ψ := by
  classical
  ext d
  rw [coeff_homogeneousComponent]
  split_ifs with hd
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    have hxd : x.1.degree + x.2.degree = φ.totalDegree + ψ.totalDegree := by
      rw [← hd, ← hx, map_add]
    by_cases h1 : x.1.degree = φ.totalDegree
    · rw [if_pos h1, if_pos (by omega)]
    · rcases lt_or_gt_of_ne h1 with h | h
      · rw [coeff_eq_zero_of_totalDegree_lt (f := ψ) (by rw [← Finsupp.degree_apply]; omega)]
        simp
      · rw [coeff_eq_zero_of_totalDegree_lt (f := φ) (by rw [← Finsupp.degree_apply]; omega)]
        simp
  · exact (((homogeneousComponent_isHomogeneous _ _).mul
      (homogeneousComponent_isHomogeneous _ _)).coeff_eq_zero hd).symm

/-- The homogeneous component of top degree of a nonzero polynomial is nonzero. -/
theorem homogeneousComponent_totalDegree_ne_zero [CommSemiring R] {φ : MvPolynomial σ R}
    (hφ : φ ≠ 0) : homogeneousComponent φ.totalDegree φ ≠ 0 := by
  obtain ⟨d, hd, hdeg⟩ := Finset.exists_mem_eq_sup φ.support (support_nonempty.2 hφ)
    fun s => s.sum fun _ e => e
  intro h0
  have := congrArg (coeff d) h0
  rw [coeff_homogeneousComponent, if_pos (by rw [Finsupp.degree_apply]; exact hdeg.symm),
    coeff_zero] at this
  exact mem_support_iff.1 hd this

/-- Over a domain, a polynomial whose homogeneous component of top degree is a unit is a unit. -/
theorem isUnit_of_isUnit_homogeneousComponent_totalDegree [CommRing R] [IsDomain R]
    {φ : MvPolynomial σ R} (h : IsUnit (homogeneousComponent φ.totalDegree φ)) : IsUnit φ := by
  obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.1 h
  have h0 : φ.totalDegree = 0 := by
    rw [← (homogeneousComponent_isHomogeneous φ.totalDegree φ).totalDegree h.ne_zero, hr,
      totalDegree_C]
  rwa [h0, homogeneousComponent_zero, ← totalDegree_eq_zero_iff_eq_C.1 h0] at h

/-- **An irreducible form minus one is irreducible.** If `φ` is an irreducible polynomial over a
domain, homogeneous of degree `n ≠ 0`, then `φ - 1` is irreducible. -/
theorem irreducible_sub_one_of_isHomogeneous [CommRing R] [IsDomain R] {φ : MvPolynomial σ R}
    {n : ℕ} (hφ : Irreducible φ) (hh : φ.IsHomogeneous n) (hn : n ≠ 0) :
    Irreducible (φ - 1) := by
  have hcomp : ∀ m, m ≠ 0 → homogeneousComponent m (φ - 1) = if m = n then φ else 0 := by
    intro m hm
    rw [map_sub, homogeneousComponent_of_mem hh,
      homogeneousComponent_of_mem (isHomogeneous_one σ R), if_neg hm, sub_zero]
  have hlow : ∀ ψ : MvPolynomial σ R, ψ.totalDegree < n → φ - 1 ≠ ψ := by
    rintro ψ hψ h
    have := hcomp n hn
    rw [h, homogeneousComponent_eq_zero _ _ hψ, if_pos rfl] at this
    exact hφ.ne_zero this.symm
  refine ⟨fun hu => ?_, fun g h hgh => ?_⟩
  · obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.1 hu
    exact hlow (C r) (by rw [totalDegree_C]; omega) hr
  · have hz : (0 : MvPolynomial σ R).totalDegree < n := by simpa using Nat.pos_of_ne_zero hn
    have hg : g ≠ 0 := fun h0 => hlow 0 hz (by rw [hgh, h0, zero_mul])
    have hh0 : h ≠ 0 := fun h0 => hlow 0 hz (by rw [hgh, h0, mul_zero])
    have hpos : g.totalDegree + h.totalDegree ≠ 0 := fun h0 =>
      hlow (g * h) (by have := totalDegree_mul g h; omega) hgh
    have hprod := homogeneousComponent_totalDegree_add_mul g h
    rw [← hgh, hcomp _ hpos] at hprod
    have hne := mul_ne_zero (homogeneousComponent_totalDegree_ne_zero hg)
      (homogeneousComponent_totalDegree_ne_zero hh0)
    split_ifs at hprod with hdeg
    · rw [hprod] at hφ
      exact (hφ.isUnit_or_isUnit rfl).imp isUnit_of_isUnit_homogeneousComponent_totalDegree
        isUnit_of_isUnit_homogeneousComponent_totalDegree
    · exact absurd hprod.symm hne

/-- The determinant of a square matrix of linear forms is homogeneous of degree its size. -/
theorem isHomogeneous_det_of_isHomogeneous [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n (MvPolynomial σ R)} (hM : ∀ i j, (M i j).IsHomogeneous 1) :
    M.det.IsHomogeneous (Fintype.card n) := by
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun e _ => ?_
  have h := IsHomogeneous.prod Finset.univ (fun i => M (e i) i) (fun _ => 1) fun i _ => hM _ _
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with he | he <;> simp [he, h, h.neg]

end Homogeneous

/-! ### `det z - 1` generates a prime ideal -/

/-- `det z` is homogeneous of degree `k`. -/
theorem isHomogeneous_det_complexGenericMatrix (k : ℕ) :
    (complexGenericMatrix k k).det.IsHomogeneous k := by
  simpa using isHomogeneous_det_of_isHomogeneous (M := complexGenericMatrix k k)
    fun i j => by simpa using isHomogeneous_X ℂ (i, j)

/-- `det z = Δ_{[1,k],[1,k]}(z)` is irreducible for `k ≥ 1`. -/
theorem irreducible_det_complexGenericMatrix {k : ℕ} (hk : k ≠ 0) :
    Irreducible (complexGenericMatrix k k).det := by
  have h := irreducible_minor_complexGenericMatrix (p := k) (q := k) (I := Finset.univ)
    (J := Finset.univ) (Finset.univ_nonempty_iff.2 ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩) rfl
  rw [← pluckerCoord, pluckerCoord_eq_det _ (Finset.card_fin k)] at h
  convert h using 2
  ext i j
  simp [orderEmbOfFin_univ_fin]

/-- The polynomial `det z - 1` generates a prime ideal of `ℂ[z]`, for every `k`; for `k = 0`,
`det z - 1 = 0` and the zero ideal of the domain `ℂ[z]` is prime. -/
@[cluster_algebras "lem_det_minus_one_prime"]
theorem isPrime_span_detSubOne (k : ℕ) : (Ideal.span {detSubOne k}).IsPrime := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [show detSubOne 0 = 0 by simp [detSubOne], Ideal.span_singleton_eq_bot.2 rfl]
    exact Ideal.isPrime_bot
  · have hirr := irreducible_sub_one_of_isHomogeneous (irreducible_det_complexGenericMatrix
      hk.ne') (isHomogeneous_det_complexGenericMatrix k) hk.ne'
    exact (Ideal.span_singleton_prime hirr.ne_zero).2 hirr.prime

/-- The coordinate ring `ℂ[SL_k]` is an integral domain. -/
@[cluster_algebras "lem_det_minus_one_prime"]
instance instIsDomainSLCoord (k : ℕ) : IsDomain (SLCoord k) :=
  haveI := isPrime_span_detSubOne k
  Ideal.Quotient.isDomain _

/-! ### Algebraic independence passes to `SL_k` -/

/-- Elements `y i` of an intermediate field `F` generate `F` as soon as their images generate
the field `F` of the ambient field. -/
private theorem adjoin_range_eq_top_of_lift {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} {y : ι → F}
    (h : IntermediateField.adjoin K (Set.range fun i => (y i : L)) = F) :
    IntermediateField.adjoin K (Set.range y) = ⊤ :=
  IntermediateField.lift_injective F <| by
    rwa [IntermediateField.lift_adjoin, IntermediateField.lift_top, ← Set.range_comp]

/-- Rescaling the elements `x i` by integer powers of `d` gives elements which, together with
`d`, generate a subfield of the field generated by the `x i` and `d`. -/
private theorem adjoin_range_snoc_le {K L : Type*} [Field K] [Field L] [Algebra K L] {r : ℕ}
    {x y : Fin r → L} {d : L} (e : Fin r → ℤ) (hy : ∀ i, y i = d ^ e i * x i) :
    IntermediateField.adjoin K (Set.range (Fin.snoc y d : Fin (r + 1) → L)) ≤
      IntermediateField.adjoin K (Set.range (Fin.snoc x d : Fin (r + 1) → L)) := by
  have hmem : ∀ i, (Fin.snoc x d : Fin (r + 1) → L) i ∈
      IntermediateField.adjoin K (Set.range (Fin.snoc x d : Fin (r + 1) → L)) :=
    fun i => IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  have hd := hmem (Fin.last r)
  rw [Fin.snoc_last] at hd
  refine IntermediateField.adjoin_le_iff.2 (Set.range_subset_iff.2 fun i => ?_)
  cases i using Fin.lastCases with
  | last => rwa [Fin.snoc_last]
  | cast i =>
    have hx := hmem i.castSucc
    rw [Fin.snoc_castSucc] at hx ⊢
    rw [hy]
    exact mul_mem (zpow_mem hd _) hx

/-- If `f₁, …, f_r` are minors of the generic `k × k` matrix `z` such that `f₁, …, f_r, det z`
are algebraically independent over `ℂ`, then `π(f₁), …, π(f_r)` are algebraically independent
over `ℂ`. -/
@[cluster_algebras "lem_sl_minors_independent"]
theorem algebraicIndependent_slQuot_comp {k r : ℕ} {f : Fin r → ComplexPoly k k}
    (hf : ∀ i, ∃ I J, f i = minor (complexGenericMatrix k k) I J)
    (hind : AlgebraicIndependent ℂ
      (Fin.snoc f (complexGenericMatrix k k).det : Fin (r + 1) → ComplexPoly k k)) :
    AlgebraicIndependent ℂ (slQuot k ∘ f) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := hind.transcendental (Fin.last r)
    rw [Fin.snoc_last, Matrix.det_isEmpty] at this
    exact absurd isAlgebraic_one this
  set K := FractionRing (ComplexPoly k k)
  set r₀ : Fin k := ⟨0, hk⟩
  set d : K := algebraMap _ K (complexGenericMatrix k k).det
  have hd : d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ K)).2
    (det_complexGenericMatrix_ne_zero k)
  have hε : ∀ i, ∃ e : ℤ, slRescale r₀ (slQuot k (f i)) = d ^ (-e) * algebraMap _ K (f i) := by
    intro i
    obtain ⟨I, J, hi⟩ := hf i
    exact ⟨_, by rw [hi, slRescale_slQuot_minor]⟩
  choose e he using hε
  set x : Fin (r + 1) → K := Fin.snoc (fun i => algebraMap _ K (f i)) d
  set y : Fin (r + 1) → K := Fin.snoc (fun i => slRescale r₀ (slQuot k (f i))) d
  set F := IntermediateField.adjoin ℂ (Set.range x)
  have hadj : IntermediateField.adjoin ℂ (Set.range y) = F :=
    le_antisymm (adjoin_range_snoc_le _ he) (adjoin_range_snoc_le e fun i => by
      rw [he, _root_.zpow_neg, mul_inv_cancel_left₀ (zpow_ne_zero _ hd)])
  set x' : Fin (r + 1) → F := fun i => ⟨x i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩
  set y' : Fin (r + 1) → F := fun i => ⟨y i, hadj.le (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)⟩
  have hx' : IsFreeGeneratingTuple ℂ x' := by
    refine ⟨AlgebraicIndependent.of_comp F.val ?_, adjoin_range_eq_top_of_lift rfl⟩
    have := hind.map' (f := IsScalarTower.toAlgHom ℂ (ComplexPoly k k) K)
      (IsFractionRing.injective _ K)
    rwa [Fin.comp_snoc] at this
  have hy' : IsFreeGeneratingTuple ℂ y' :=
    isFreeGeneratingTuple_of_trdeg_eq hx'.trdeg_eq (adjoin_range_eq_top_of_lift hadj)
  have hy : AlgebraicIndependent ℂ y := hy'.1.map' (f := F.val) Subtype.val_injective
  refine AlgebraicIndependent.of_comp (slRescale r₀) ?_
  convert hy.comp Fin.castSucc (Fin.castSucc_injective r) using 1
  ext i
  simp [y]

/-! ### The induced one-parameter substitutions on `SL_k` -/

section OneParam

variable {k : ℕ}

/-- Two polynomials have the same image in `ℂ[SL_k]` iff their difference lies in
`⟨det z - 1⟩`. -/
private theorem slQuot_eq_slQuot_iff {f g : ComplexPoly k k} :
    slQuot k f = slQuot k g ↔ f - g ∈ Ideal.span {detSubOne k} :=
  Ideal.Quotient.eq

/-- `σ_g(det z) = det g · det z`. -/
private theorem leftSubst_det (g : Matrix (Fin k) (Fin k) ℂ) :
    leftSubst k g (complexGenericMatrix k k).det = C g.det * (complexGenericMatrix k k).det := by
  rw [← AlgHom.coe_toRingHom, RingHom.map_det, RingHom.mapMatrix_apply, AlgHom.coe_toRingHom,
    map_leftSubst_complexGenericMatrix, det_mul, ← MvPolynomial.algebraMap_eq, RingHom.map_det]
  rfl

/-- `σ_g` maps `⟨det z - 1⟩` into itself when `det g = 1`. -/
private theorem leftSubst_mem_span_detSubOne {g : Matrix (Fin k) (Fin k) ℂ} (hg : g.det = 1)
    {f : ComplexPoly k k} (hf : f ∈ Ideal.span {detSubOne k}) :
    leftSubst k g f ∈ Ideal.span {detSubOne k} := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hf
  rw [map_mul, detSubOne, map_sub, leftSubst_det, hg, map_one, map_one, one_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- `Θ_{ij}(det z) = det z` for `i ≠ j`: `det(E_{ij}(s) z) = det z` for every `s ∈ ℂ`. -/
private theorem oneParamSubst_det {i j : Fin k} (hij : i ≠ j) :
    oneParamSubst k i j (complexGenericMatrix k k).det =
      Polynomial.C (complexGenericMatrix k k).det := by
  rw [← sub_eq_zero]
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine (Set.infinite_range_of_injective (C_injective (Fin k × Fin k) ℂ)).mono ?_
  rintro _ ⟨s, rfl⟩
  simp [eval_oneParamSubst, leftSubst_det, det_transvection_of_ne _ _ hij]

/-- `Θ_{ij}` followed by `π` on coefficients kills `⟨det z - 1⟩`, for `i ≠ j`. -/
theorem map_slQuot_oneParamSubst_eq_zero {i j : Fin k} (hij : i ≠ j) {f : ComplexPoly k k}
    (hf : f ∈ Ideal.span {detSubOne k}) :
    (oneParamSubst k i j f).map (slQuot k : ComplexPoly k k →+* SLCoord k) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hf
  have h0 : slQuot k (detSubOne k) = 0 := (slQuot_eq_slQuot_iff (g := 0)).2 (by simp)
  have hΘ : oneParamSubst k i j (detSubOne k) = Polynomial.C (detSubOne k) := by
    simp [detSubOne, oneParamSubst_det hij]
  rw [map_mul, hΘ, Polynomial.map_mul, Polynomial.map_C]
  simp [h0]

/-- The **induced one-parameter substitution** `Θ̄_{ij} : ℂ[SL_k] → ℂ[SL_k][t]`, `i ≠ j`: the
substitution `Θ_{ij}` followed by `π` on coefficients kills `det z - 1`, since `Θ_{ij}` fixes
`det z`, and so factors through `π`. -/
noncomputable def slOneParamSubst (i j : Fin k) (hij : i ≠ j) :
    SLCoord k →ₐ[ℂ] Polynomial (SLCoord k) :=
  Ideal.Quotient.liftₐ (Ideal.span {detSubOne k})
    ((Polynomial.mapAlgHom (slQuot k)).comp (oneParamSubst k i j))
    fun _ hf => map_slQuot_oneParamSubst_eq_zero hij hf

/-- `Θ̄_{ij}(π(f))` is `Θ_{ij}(f)` with `π` applied to its coefficients. -/
theorem slOneParamSubst_slQuot (i j : Fin k) (hij : i ≠ j) (f : ComplexPoly k k) :
    slOneParamSubst i j hij (slQuot k f) =
      (oneParamSubst k i j f).map (slQuot k : ComplexPoly k k →+* SLCoord k) :=
  rfl

/-- Evaluating `Θ̄_{ij}(π(f))` at `t = s ∈ ℂ` gives `π(σ_{E_{ij}(s)}(f))`. -/
theorem eval_slOneParamSubst_slQuot (i j : Fin k) (hij : i ≠ j) (s : ℂ) (f : ComplexPoly k k) :
    (slOneParamSubst i j hij (slQuot k f)).eval (algebraMap ℂ (SLCoord k) s) =
      slQuot k (leftSubst k (transvection i j s) f) := by
  rw [slOneParamSubst_slQuot, Polynomial.eval_map, ← (slQuot k).commutes s,
    MvPolynomial.algebraMap_eq, ← AlgHom.coe_toRingHom, Polynomial.eval₂_at_apply,
    eval_oneParamSubst]

/-- `Θ̄_{ij}` is the identity at `t = 0`. -/
@[simp]
theorem eval_zero_slOneParamSubst (i j : Fin k) (hij : i ≠ j) (a : SLCoord k) :
    (slOneParamSubst i j hij a).eval 0 = a := by
  obtain ⟨f, rfl⟩ : ∃ f, slQuot k f = a := Ideal.Quotient.mkₐ_surjective ℂ _ a
  have := eval_slOneParamSubst_slQuot i j hij 0 f
  rwa [map_zero, transvection_zero, leftSubst_one, AlgHom.id_apply] at this

/-- If `σ_E(f) - f ∈ ⟨det z - 1⟩` for every elementary matrix `E = E_{ij}(s)` with `i > j`, then
`σ_u(f) - f ∈ ⟨det z - 1⟩` and `det u = 1` for every finite product `u` of such matrices. -/
private theorem leftSubst_list_prod_sub_mem {f : ComplexPoly k k}
    (hE : ∀ t : Fin k × Fin k × ℂ, t.2.1 < t.1 →
      leftSubst k (transvection t.1 t.2.1 t.2.2) f - f ∈ Ideal.span {detSubOne k}) :
    ∀ l : List (Fin k × Fin k × ℂ), (∀ t ∈ l, t.2.1 < t.1) →
      leftSubst k (l.map fun t => transvection t.1 t.2.1 t.2.2).prod f - f ∈
          Ideal.span {detSubOne k} ∧
        (l.map fun t => transvection t.1 t.2.1 t.2.2).prod.det = 1
  | [], _ => by simp
  | t :: l, hl => by
    obtain ⟨ih₁, ih₂⟩ :=
      leftSubst_list_prod_sub_mem hE l fun t' h => hl t' (List.mem_cons_of_mem _ h)
    have ht := hl t List.mem_cons_self
    rw [List.map_cons, List.prod_cons, leftSubst_mul, AlgHom.comp_apply, det_mul, ih₂,
      det_transvection_of_ne _ _ ht.ne', mul_one]
    refine ⟨?_, rfl⟩
    have := add_mem (leftSubst_mem_span_detSubOne ih₂ (hE t ht)) ih₁
    rwa [map_sub, sub_add_sub_cancel] at this

/-- The family `(Θ̄_{ij})_{i > j}`. -/
noncomputable abbrev slLowerOneParamSubst (l : {ij : Fin k × Fin k // ij.2 < ij.1}) :
    SLCoord k →ₐ[ℂ] Polynomial (SLCoord k) :=
  slOneParamSubst l.1.1 l.1.2 l.2.ne'

/-- **`ℂ[SL_k]^U` is the ring of invariants of the one-parameter substitutions**: an element of
`ℂ[SL_k]` lies in `ℂ[SL_k]^U` if and only if it is fixed by every `Θ̄_{ij}`, `i > j`. -/
theorem slUInvariants_eq_fixedSubalgebra (k : ℕ) :
    slUInvariants k = fixedSubalgebra (slLowerOneParamSubst (k := k)) := by
  ext a
  rw [mem_slUInvariants, mem_fixedSubalgebra]
  constructor
  · rintro ⟨f, rfl, hf⟩ ⟨⟨i, j⟩, hji⟩
    rw [← sub_eq_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (Set.infinite_range_of_injective (algebraMap ℂ (SLCoord k)).injective).mono ?_
    rintro _ ⟨s, rfl⟩
    rw [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C,
      eval_slOneParamSubst_slQuot, sub_eq_zero, slQuot_eq_slQuot_iff]
    exact hf _ (transvection_mem_lowerUnitriangular hji s)
  · intro ha
    obtain ⟨f, rfl⟩ : ∃ f, slQuot k f = a := Ideal.Quotient.mkₐ_surjective ℂ _ a
    refine ⟨f, rfl, fun u hu => ?_⟩
    obtain ⟨l, hl, rfl⟩ := mem_lowerUnitriangular_iff_exists_list_transvection.1 hu
    refine (leftSubst_list_prod_sub_mem ?_ l hl).1
    rintro ⟨i, j, s⟩ hji
    have := congrArg (Polynomial.eval (algebraMap ℂ (SLCoord k) s)) (ha ⟨(i, j), hji⟩)
    rwa [Polynomial.eval_C, slLowerOneParamSubst, eval_slOneParamSubst_slQuot,
      slQuot_eq_slQuot_iff] at this

end OneParam

/-- For `k ≥ 2`, the `ℂ`-subalgebra `ℂ[SL_k]^U` of `ℂ[SL_k]` (a subring containing `ℂ`) is a
unique factorization domain. -/
@[cluster_algebras "prop_sl_u_factorial"]
theorem uniqueFactorizationMonoid_slUInvariants {k : ℕ} (hk : 2 ≤ k) :
    UniqueFactorizationMonoid (slUInvariants k) := by
  have := uniqueFactorizationMonoid_slCoord k hk
  rw [slUInvariants_eq_fixedSubalgebra]
  exact uniqueFactorizationMonoid_fixedSubalgebra fun l a => eval_zero_slOneParamSubst _ _ _ a

end ClusterAlgebras

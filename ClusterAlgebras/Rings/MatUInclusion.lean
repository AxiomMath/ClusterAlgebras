/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.FlagInvariance
public import ClusterAlgebras.Rings.OmegaCoprime
public import ClusterAlgebras.Rings.PolynomialInvariants
public import ClusterAlgebras.Rings.SpecialQuiver
public import ClusterAlgebras.Rings.StarfishUFD
public import ClusterAlgebras.Rings.WiringIndependence

/-!
# The cluster algebra of `Σ(D₀, λ)^{+det z}` lies in the polynomial invariants

Let `z` be the generic `k × k` matrix over `ℂ`, `k ≥ 2`, and let `D₀` be the special wiring
diagram `specialWiringDiagram` on `k` strands, with a chamber labelling `λ`. The seed `Σ(D₀, λ)`
has as entries the chamber minors of `D₀`; adding the dummy frozen variable `det z` gives the seed
`Σ⁺ = Σ(D₀, λ)^{+det z}`. It is a labeled seed in the subfield of `ℂ(z)` its entries generate,
and its cluster algebra lies in the ring `ℂ[z]^{U_k}` of polynomials invariant under the lower
unitriangular matrices.

Following [FWZ]: `R = ℂ[z]^{U_k}` is factorial, every entry of `Σ⁺` is a flag minor and so lies
in `R`, and the conditions of the Starfish lemma for factorial rings are checked on the chamber
minors and their exchanged partners, which are again flag minors (at the chambers of gap one) or
the polynomials `Ω = P_{Jb} P_{Jacd} - P_{Ja} P_{Jbcd}`. No two of these share a prime factor of
`R`, since no one of them divides the other in `ℂ[z]` and the chamber minors are minors of `z`.

## Main definitions

* `ClusterAlgebras.wiringSeedDet D L`: the seed `Σ(D, λ)^{+det z}`.

## Main results

* `ClusterAlgebras.clusterAlgebraOfSeed_map`: a homomorphism of fields carries the cluster algebra
  of a seed onto that of the image seed.
* `ClusterAlgebras.det_complexGenericMatrix_mem_invariants`: `det z` is invariant under every
  matrix of determinant one.
* `ClusterAlgebras.isLabeledSeed_wiringSeedDet`: `Σ(D, λ)^{+det z}` is a labeled seed in the field
  its entries generate.
* `ClusterAlgebras.clusterAlgebraOfSeed_wiringSeedDet_le`: `𝒜(Σ⁺) ⊆ ℂ[z]^{U_k}`, read in `ℂ(z)`.
* `ClusterAlgebras.exists_mem_invariants_of_mem_clusterAlgebraOfSeed_wiringSeedDet`: the same,
  for the seed read in the field its entries generate.

## Implementation notes

* The seed `Σ⁺` lives in `ℂ(z) = FractionRing ℂ[z]`, while the Starfish lemma is stated for seeds
  in the fraction field of the factorial ring `R = ℂ[z]^{U_k}`. The inclusion `R ⊆ ℂ[z]` extends to
  an embedding `Frac(R) → ℂ(z)`; the seed with the same entries, read in `Frac(R)`, is carried by
  it to `Σ⁺`, and with it its cluster algebra (`clusterAlgebraOfSeed_map`).
* "`y ∈ ℂ[z]^{U_k}`", for `y ∈ ℂ(z)`, is `y = f` for a polynomial `f ∈ ℂ[z]^{U_k}`, read in `ℂ(z)`.
* The labeled-seed statement holds for every wiring diagram, and the inclusion for every number
  `k = n + 2 ≥ 2` of strands: for `k = 2` there are no mutable indices. FWZ's `k ≥ 3` is
  dropped.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6.
-/

@[expose] public section

namespace ClusterAlgebras

open WiringDiagram

/-! ### Cluster algebras under a homomorphism of fields -/

section Map

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {m n : ℕ}

/-- **A homomorphism of fields carries the cluster algebra of a seed onto that of its image**:
`f(𝒜(x̃, B̃)) = 𝒜(f(x̃), B̃)`. -/
theorem clusterAlgebraOfSeed_map (hmn : n ≤ m) (f : F →ₐ[K] F') (S : SeedData F m n) :
    (clusterAlgebraOfSeed K hmn S).map f = clusterAlgebraOfSeed K hmn (S.map f) := by
  rw [clusterAlgebraOfSeed, clusterAlgebraOfSeed, AlgHom.map_adjoin, Set.image_union,
    Set.image_iUnion]
  congr 2
  · exact (frozenVariables_mk_comp S f).symm
  · refine Set.iUnion_congr fun s => ?_
    rw [← seedMutationSeq_map]
    exact (clusterVariables_mk_comp _ f hmn).symm

end Map

/-! ### The determinant is an invariant -/

/-- **`det z` is invariant under matrices of determinant one**: for a set `G` of complex `k × k`
matrices of determinant one, `det z ∈ ℂ[z]^G`. -/
theorem det_complexGenericMatrix_mem_invariants {k : ℕ} {G : Set (Matrix (Fin k) (Fin k) ℂ)}
    (hG : ∀ g ∈ G, g.det = 1) : (complexGenericMatrix k k).det ∈ invariants k G := by
  intro g hg
  have h := RingHom.map_det (leftSubst k g).toRingHom (complexGenericMatrix k k)
  have h' := RingHom.map_det (algebraMap ℂ (ComplexPoly k k)) g
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.mapMatrix_apply] at h h'
  rw [h, show (complexGenericMatrix k k).map (leftSubst k g) = _ from
    map_leftSubst_complexGenericMatrix g, Matrix.det_mul, ← h', hG g hg, map_one, one_mul]

/-- `det z ∈ ℂ[z]^{U_k}`. -/
theorem det_complexGenericMatrix_mem_invariants_lowerUnitriangular (k : ℕ) :
    (complexGenericMatrix k k).det ∈ invariants k (lowerUnitriangular k) :=
  det_complexGenericMatrix_mem_invariants fun u hu => by
    rw [Matrix.det_of_lowerTriangular u fun i j hij => hu.2 i j hij]
    simp [hu.1]

/-! ### Flag minors with no common prime factor -/

section FlagMinor

variable {k : ℕ}

/-- A flag minor of the generic `k × k` matrix with nonempty column set does not divide a flag
minor with a different column set. -/
theorem not_flagMinor_complexGenericMatrix_dvd {J J' : Finset (Fin k)} (hJ : J.Nonempty)
    (hne : J ≠ J') :
    ¬flagMinor (complexGenericMatrix k k) J ∣ flagMinor (complexGenericMatrix k k) J' := by
  have hc : ∀ J : Finset (Fin k), (initialRows k J.card).card = J.card := fun J =>
    card_initialRows (J.card_le_univ.trans_eq (Fintype.card_fin k))
  refine not_minor_complexGenericMatrix_dvd ?_ (hc J) (hc J') fun h => hne (Prod.ext_iff.1 h).2
  rw [← Finset.card_pos, hc J]
  exact hJ.card_pos

/-- A prime element of a subring `R ⊆ ℂ[z]` containing `ℂ` that divides a flag minor in `R` does
not divide an element of `R` that the flag minor does not divide in `ℂ[z]`. -/
theorem not_dvd_of_prime_dvd_flagMinor_complexGenericMatrix {R : Subalgebra ℂ (ComplexPoly k k)}
    {J : Finset (Fin k)} (hJ : flagMinor (complexGenericMatrix k k) J ∈ R)
    {f : ComplexPoly k k} (hf : f ∈ R) (hJf : ¬flagMinor (complexGenericMatrix k k) J ∣ f)
    {π : R} (hπ : Prime π) (hπJ : π ∣ ⟨_, hJ⟩) : ¬π ∣ ⟨f, hf⟩ :=
  not_dvd_of_prime_dvd_minor_complexGenericMatrix
    (card_initialRows (J.card_le_univ.trans_eq (Fintype.card_fin k))) hJ hf hJf hπ hπJ

end FlagMinor

/-! ### The seed `Σ(D, λ)^{+det z}` -/

section WiringSeedDet

variable {p m n : ℕ}

/-- The seed `Σ(D, λ)^{+det z}`: the seed `Σ(D, λ)` of a wiring diagram, with the dummy frozen
variable `det z` appended. -/
noncomputable abbrev wiringSeedDet (D : WiringDiagram p) (L : Labelling D.wiringQuiver m n) :
    SeedData (FractionRing (ComplexPoly (p + 2) (p + 2))) (m + 1) n :=
  (wiringSeed D L).extendDummy
    ![algebraMap _ (FractionRing (ComplexPoly (p + 2) (p + 2)))
      (complexGenericMatrix (p + 2) (p + 2)).det]

/-- **`Σ(D, λ)^{+det z}` is a labeled seed** over `ℂ` in the subfield of `ℂ(z)` generated by its
entries: the chamber minors and `det z` are algebraically independent, and the principal part of
the matrix is that of `Σ(D, λ)`. -/
@[cluster_algebras "lem_mat_u_cluster_inclusion"]
theorem isLabeledSeed_wiringSeedDet (D : WiringDiagram p) (L : Labelling D.wiringQuiver m n) :
    IsLabeledSeed ℂ (L.le.trans (Nat.le_add_right m 1)) ((wiringSeedDet D L).adjoinSelf ℂ) := by
  rw [isLabeledSeed_adjoinSelf_iff]
  refine ⟨algebraicIndependent_wiringSeed_extCluster_append_det D L, ?_⟩
  have hsub : (wiringSeedDet D L).extExchangeMatrix.submatrix
      (Fin.castLE (L.le.trans (Nat.le_add_right m 1))) id =
        (wiringSeed D L).extExchangeMatrix.submatrix (Fin.castLE L.le) id := by
    ext i j
    simp [extendDummy_castLE_eq_castAdd L.le]
  rw [ExtSkewSymmetrizable, hsub]
  exact (isLabeledSeed_wiringSeed D L).2

end WiringSeedDet

/-! ### The special seed -/

section Special

variable {n m n' : ℕ}

/-- **The exchanges of `Σ(D₀, λ)` stay in `ℂ[z]^{U_k}`.** At a mutable index `q`, the new entry of
`μ_q(Σ(D₀, λ))` is a polynomial `f ∈ ℂ[z]^{U_k}`, read in `ℂ(z)`, that the old entry, the chamber
minor of `λ(q)`, does not divide in `ℂ[z]`: a flag minor `P_{a,c}` at a chamber `{b}` of gap one,
and `Ω = P_{Jb} P_{Jacd} - P_{Ja} P_{Jbcd}` at a chamber `[b, c]` with `b < c`. -/
theorem exists_mem_invariants_seedMutation_wiringSeed_special
    (L : Labelling (specialWiringDiagram n).wiringQuiver m n') (q : Fin n') :
    ∃ f ∈ invariants (n + 2) (lowerUnitriangular (n + 2)),
      algebraMap (ComplexPoly (n + 2) (n + 2)) (FractionRing (ComplexPoly (n + 2) (n + 2))) f =
        (seedMutation L.le (wiringSeed (specialWiringDiagram n) L) q).extCluster
          (Fin.castLE L.le q) ∧
      ¬flagMinor (complexGenericMatrix (n + 2) (n + 2))
        (L.equiv (Fin.castLE L.le q)).chamberSet ∣ f := by
  set Y := L.equiv (Fin.castLE L.le q) with hY
  have hb : Y.Bounded := by
    have := L.notMem_frozen q
    rwa [mem_frozen_wiringQuiver, not_not] at this
  rw [bounded_specialWiringDiagram_iff] at hb
  have hmem := mem_chamberSet_specialWiringDiagram Y
  rcases Nat.eq_zero_or_pos (Y.gap : ℕ) with h0 | hpos
  · -- a chamber `{b}` of gap one
    obtain ⟨a, ha⟩ : ∃ a : Fin (n + 2), (a : ℕ) = Y.idx - 1 := ⟨⟨Y.idx - 1, by omega⟩, rfl⟩
    obtain ⟨b, hb'⟩ : ∃ b : Fin (n + 2), (b : ℕ) = Y.idx := ⟨⟨Y.idx, by omega⟩, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : Fin (n + 2), (c : ℕ) = Y.idx + 1 := ⟨⟨Y.idx + 1, by omega⟩, rfl⟩
    have hq : Y.chamberSet = {b} := by
      ext v
      rw [hmem, Finset.mem_singleton, Fin.ext_iff]
      omega
    refine ⟨_, flagMinor_mem_invariants {a, c},
      (seedMutation_wiringSeed_special_bottom L (a := a) (b := b) (c := c)
        (by omega) (by omega) q hq).symm, ?_⟩
    rw [hq]
    refine not_flagMinor_complexGenericMatrix_dvd (Finset.singleton_nonempty b) fun h => ?_
    have hbac : b ∈ ({a, c} : Finset (Fin (n + 2))) := h ▸ Finset.mem_singleton_self b
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hbac
    omega
  · -- a chamber `[b, c]` with `b < c`
    obtain ⟨a, ha⟩ : ∃ a : Fin (n + 2), (a : ℕ) = Y.idx - 1 := ⟨⟨Y.idx - 1, by omega⟩, rfl⟩
    obtain ⟨b, hb'⟩ : ∃ b : Fin (n + 2), (b : ℕ) = Y.idx := ⟨⟨Y.idx, by omega⟩, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : Fin (n + 2), (c : ℕ) = Y.idx + Y.gap :=
      ⟨⟨Y.idx + Y.gap, by omega⟩, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : Fin (n + 2), (d : ℕ) = Y.idx + Y.gap + 1 :=
      ⟨⟨Y.idx + Y.gap + 1, by omega⟩, rfl⟩
    have hab : (a : ℕ) + 1 = b := by omega
    have hbc : b < c := by rw [Fin.lt_def]; omega
    have hcd : (c : ℕ) + 1 = d := by omega
    have hq : Y.chamberSet = Finset.Icc b c := by
      ext v
      rw [hmem, Finset.mem_Icc, Fin.le_def, Fin.le_def]
      omega
    have hR : ∀ J, flagMinor (complexGenericMatrix (n + 2) (n + 2)) J ∈
        invariants (n + 2) (lowerUnitriangular (n + 2)) := flagMinor_mem_invariants
    refine ⟨_, sub_mem (mul_mem (hR _) (hR _)) (mul_mem (hR _) (hR _)),
      (seedMutation_wiringSeed_special_omega L hab hbc hcd q hq).symm, ?_⟩
    have hI : Finset.Icc b c = Finset.Ioo b c ∪ {b, c} := by
      ext v
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioo, Finset.mem_insert,
        Finset.mem_singleton, Fin.le_def, Fin.lt_def, Fin.ext_iff]
      omega
    rw [hq, hI]
    exact not_flagMinor_complexGenericMatrix_dvd_omega hab hbc hcd

/-- The embedding `Frac(ℂ[z]^{U_k}) → ℂ(z)` extending the inclusion `ℂ[z]^{U_k} ⊆ ℂ[z]`. -/
private noncomputable def invariantsLift (n : ℕ) :
    FractionRing (invariants (n + 2) (lowerUnitriangular (n + 2))) →ₐ[ℂ]
      FractionRing (ComplexPoly (n + 2) (n + 2)) :=
  IsFractionRing.liftAlgHom (g := (IsScalarTower.toAlgHom ℂ (ComplexPoly (n + 2) (n + 2))
      (FractionRing (ComplexPoly (n + 2) (n + 2)))).comp
        (invariants (n + 2) (lowerUnitriangular (n + 2))).val)
    ((IsFractionRing.injective (ComplexPoly (n + 2) (n + 2)) _).comp Subtype.val_injective)

private theorem invariantsLift_algebraMap (r : invariants (n + 2) (lowerUnitriangular (n + 2))) :
    invariantsLift n (algebraMap (invariants (n + 2) (lowerUnitriangular (n + 2)))
        (FractionRing (invariants (n + 2) (lowerUnitriangular (n + 2)))) r) =
      algebraMap (ComplexPoly (n + 2) (n + 2)) (FractionRing (ComplexPoly (n + 2) (n + 2)))
        (r : ComplexPoly (n + 2) (n + 2)) := by
  simp only [invariantsLift, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

/-- The entries of `Σ(D₀, λ)^{+det z}`, as elements of `ℂ[z]^{U_k}`. -/
private noncomputable def invariantsCluster
    (L : Labelling (specialWiringDiagram n).wiringQuiver m n') :
    Fin (m + 1) → invariants (n + 2) (lowerUnitriangular (n + 2)) :=
  Fin.append (fun i => ⟨flagMinor (complexGenericMatrix (n + 2) (n + 2)) (L.equiv i).chamberSet,
      flagMinor_mem_invariants _⟩)
    ![⟨(complexGenericMatrix (n + 2) (n + 2)).det,
      det_complexGenericMatrix_mem_invariants_lowerUnitriangular _⟩]

private theorem invariantsCluster_castLE
    (L : Labelling (specialWiringDiagram n).wiringQuiver m n') (i : Fin n') :
    invariantsCluster L (Fin.castLE (L.le.trans (Nat.le_add_right m 1)) i) =
      ⟨flagMinor (complexGenericMatrix (n + 2) (n + 2)) (L.equiv (Fin.castLE L.le i)).chamberSet,
        flagMinor_mem_invariants _⟩ :=
  Fin.append_left _ _ (Fin.castLE L.le i)

/-- The seed `Σ(D₀, λ)^{+det z}` read in `Frac(ℂ[z]^{U_k})`. -/
private noncomputable def invariantsSeed
    (L : Labelling (specialWiringDiagram n).wiringQuiver m n') :
    SeedData (FractionRing (invariants (n + 2) (lowerUnitriangular (n + 2)))) (m + 1) n' :=
  ⟨algebraMap (invariants (n + 2) (lowerUnitriangular (n + 2))) _ ∘ invariantsCluster L,
    (wiringSeedDet (specialWiringDiagram n) L).extExchangeMatrix⟩

private theorem map_invariantsSeed (L : Labelling (specialWiringDiagram n).wiringQuiver m n') :
    (invariantsSeed L).map (invariantsLift n) = wiringSeedDet (specialWiringDiagram n) L := by
  refine SeedData.ext (funext fun i => ?_) rfl
  induction i using Fin.addCases with
  | left i => simp [invariantsSeed, invariantsCluster, invariantsLift_algebraMap, wiringSeed]
  | right e =>
    simp [invariantsSeed, invariantsCluster, invariantsLift_algebraMap, Fin.fin_one_eq_zero e]

private theorem isLabeledSeed_invariantsSeed
    (L : Labelling (specialWiringDiagram n).wiringQuiver m n') :
    IsLabeledSeed ℂ (L.le.trans (Nat.le_add_right m 1)) ((invariantsSeed L).adjoinSelf ℂ) := by
  rw [isLabeledSeed_adjoinSelf_iff]
  have hD := (isLabeledSeed_adjoinSelf_iff ℂ _ _).1
    (isLabeledSeed_wiringSeedDet (specialWiringDiagram n) L)
  refine ⟨AlgebraicIndependent.of_comp (invariantsLift n) ?_, hD.2⟩
  have hc : invariantsLift n ∘ (invariantsSeed L).extCluster =
      (wiringSeedDet (specialWiringDiagram n) L).extCluster :=
    congrArg SeedData.extCluster (map_invariantsSeed L)
  rw [hc]
  exact hD.1

/-- Every chamber set of `D₀` is nonempty. -/
private theorem chamberSet_nonempty_specialWiringDiagram (c : (specialWiringDiagram n).Chamber) :
    c.chamberSet.Nonempty := by
  have hc := c.idx_le
  rw [multiplicity_specialWiringDiagram] at hc
  exact ⟨⟨c.idx, by omega⟩, (mem_chamberSet_specialWiringDiagram c _).2 ⟨le_rfl, by simp⟩⟩

/-- Distinct mutable chamber minors of `D₀` share no prime factor in `ℂ[z]^{U_k}`. -/
private theorem not_dvd_invariantsCluster_of_prime_dvd
    (L : Labelling (specialWiringDiagram n).wiringQuiver m n') {i j : Fin n'} (hij : i ≠ j)
    {p : invariants (n + 2) (lowerUnitriangular (n + 2))} (hp : Prime p)
    (hpi : p ∣ invariantsCluster L (Fin.castLE (L.le.trans (Nat.le_add_right m 1)) i)) :
    ¬p ∣ invariantsCluster L (Fin.castLE (L.le.trans (Nat.le_add_right m 1)) j) := by
  rw [invariantsCluster_castLE] at hpi ⊢
  refine not_dvd_of_prime_dvd_flagMinor_complexGenericMatrix _ _
    (not_flagMinor_complexGenericMatrix_dvd (chamberSet_nonempty_specialWiringDiagram _)
      fun he => hij ?_) hp hpi
  exact Fin.castLE_injective L.le
    (L.equiv.injective ((specialWiringDiagram n).chamberSet_injective he))

/-- **`𝒜(Σ⁺) ⊆ ℂ[z]^{U_k}`, read in `ℂ(z)`.** For a chamber labelling `λ` of the special wiring
diagram `D₀` on `k = n + 2` strands, the cluster algebra of `Σ(D₀, λ)^{+det z}`, a subalgebra of
`ℂ(z)`, lies in the image of `ℂ[z]^{U_k}`. -/
theorem clusterAlgebraOfSeed_wiringSeedDet_le
    (L : Labelling (specialWiringDiagram n).wiringQuiver m n') :
    clusterAlgebraOfSeed ℂ (L.le.trans (Nat.le_add_right m 1))
        (wiringSeedDet (specialWiringDiagram n) L) ≤
      (invariants (n + 2) (lowerUnitriangular (n + 2))).map
        (IsScalarTower.toAlgHom ℂ (ComplexPoly (n + 2) (n + 2))
          (FractionRing (ComplexPoly (n + 2) (n + 2)))) := by
  classical
  set h := L.le.trans (Nat.le_add_right m 1)
  set R := invariants (n + 2) (lowerUnitriangular (n + 2))
  have hval : ((invariantsSeed L).adjoinSelf ℂ).map
      ((invariantsLift n).comp (IntermediateField.val _)) =
        wiringSeedDet (specialWiringDiagram n) L := map_invariantsSeed L
  have hmut : ∀ q : Fin n', invariantsLift n
      ((seedMutation h ((invariantsSeed L).adjoinSelf ℂ) q).extCluster (Fin.castLE h q)) =
        (seedMutation L.le (wiringSeed (specialWiringDiagram n) L) q).extCluster
          (Fin.castLE L.le q) := fun q => by
    have := congrArg (fun T => T.extCluster (Fin.castLE h q))
      (seedMutation_map h ((invariantsLift n).comp (IntermediateField.val _))
        ((invariantsSeed L).adjoinSelf ℂ) q)
    simp only [SeedData.map_extCluster, Function.comp_apply, AlgHom.comp_apply] at this
    rw [hval, seedMutation_extendDummy L.le h] at this
    exact this.trans (SeedData.extendDummy_extCluster_castAdd _ _ (Fin.castLE L.le q))
  have hnew : ∀ q : Fin n', ∃ r : R, algebraMap R (FractionRing R) r =
      ((seedMutation h ((invariantsSeed L).adjoinSelf ℂ) q).extCluster (Fin.castLE h q)) ∧
        ∀ p : R, Prime p → p ∣ invariantsCluster L (Fin.castLE h q) → ¬p ∣ r := by
    intro q
    obtain ⟨f, hf, hfe, hfd⟩ := exists_mem_invariants_seedMutation_wiringSeed_special L q
    refine ⟨⟨f, hf⟩, (invariantsLift n).toRingHom.injective ?_, fun p hp hpx => ?_⟩
    · change invariantsLift n _ = invariantsLift n _
      rw [invariantsLift_algebraMap, hmut]
      exact hfe
    · rw [invariantsCluster_castLE] at hpx
      exact not_dvd_of_prime_dvd_flagMinor_complexGenericMatrix _ hf hfd hp hpx
  choose x' hx' hcop' using hnew
  intro y hy
  rw [← hval, ← clusterAlgebraOfSeed_map] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨r, hr⟩ := mem_range_algebraMap_of_mem_clusterAlgebraOfSeed h
    (isLabeledSeed_invariantsSeed L) (invariantsCluster L) (fun _ => rfl)
    (fun _ _ hij _ hp hpi => not_dvd_invariantsCluster_of_prime_dvd L hij hp hpi) x' hx' hcop' hw
  refine ⟨r, r.2, ?_⟩
  change _ = invariantsLift n (w : FractionRing R)
  rw [← hr, invariantsLift_algebraMap]
  rfl

/-- For a chamber labelling `λ` of the special wiring diagram `D₀` on `k = n + 2` strands, every
element `y` of `𝒜(Σ⁺)`, `Σ⁺ = Σ(D₀, λ)^{+det z}` read in the subfield of `ℂ(z)` generated by its
entries, is a polynomial `f ∈ ℂ[z]^{U_k}`, read in `ℂ(z)`. -/
@[cluster_algebras "lem_mat_u_cluster_inclusion"]
theorem exists_mem_invariants_of_mem_clusterAlgebraOfSeed_wiringSeedDet
    (L : Labelling (specialWiringDiagram n).wiringQuiver m n')
    {y : IntermediateField.adjoin ℂ
      (Set.range (wiringSeedDet (specialWiringDiagram n) L).extCluster)}
    (hy : y ∈ clusterAlgebraOfSeed ℂ (L.le.trans (Nat.le_add_right m 1))
      ((wiringSeedDet (specialWiringDiagram n) L).adjoinSelf ℂ)) :
    ∃ f ∈ invariants (n + 2) (lowerUnitriangular (n + 2)),
      algebraMap (ComplexPoly (n + 2) (n + 2)) (FractionRing (ComplexPoly (n + 2) (n + 2))) f =
        y := by
  have hy' : (y : FractionRing (ComplexPoly (n + 2) (n + 2))) ∈ clusterAlgebraOfSeed ℂ
      (L.le.trans (Nat.le_add_right m 1)) (wiringSeedDet (specialWiringDiagram n) L) := by
    have h1 : (y : FractionRing (ComplexPoly (n + 2) (n + 2))) ∈
        (clusterAlgebraOfSeed ℂ (L.le.trans (Nat.le_add_right m 1))
          ((wiringSeedDet (specialWiringDiagram n) L).adjoinSelf ℂ)).map
            (IntermediateField.val _) := ⟨y, hy, rfl⟩
    rwa [clusterAlgebraOfSeed_map, SeedData.map_val_adjoinSelf] at h1
  exact clusterAlgebraOfSeed_wiringSeedDet_le L hy'

end Special

end ClusterAlgebras

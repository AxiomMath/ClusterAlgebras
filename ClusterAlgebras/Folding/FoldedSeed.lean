/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Folding.SkewSymmetrizable
public import ClusterAlgebras.ClusterAlgebra
public import ClusterAlgebras.LaurentPhenomenon.Trivialization

/-!
# A folded seed is a labeled seed

Fix folding data: an action of `G` on the indices, an orbit labelling `θ`, a reference labeled
seed `Σ° = (w̃, B̃°)` in `F` over `𝕜` with `P = ℚ_sf(w̃)`, a free generating tuple `z̃` of `F^G`
over `𝕜` of length `m^G` with `P^G = ℚ_sf(z̃)`, and a surjective semifield homomorphism
`ψ : P → P^G`. If a seed `(x̃, B̃) = μ_s(Σ°)` is `(G, ψ)`-admissible, then its folding
`(x̃, B̃)^G` is a labeled seed in `F^G` over `𝕜`.

The folded matrix is extended skew-symmetrizable by
`ClusterAlgebras.extSkewSymmetrizable_foldedMatrix`. For the cluster, the seed `Σ°` is recovered
from `(x̃, B̃)` by mutating along the reverse of `s`, so the entries of `w̃` are subtraction-free
expressions in `x̃`. A semifield homomorphism out of `P` preserves products, quotients and the
addition, which in `P` and `P^G` are those of the fields, so it sends a subtraction-free expression
`P'(ũ)/Q(ũ)` in elements `uᵢ ∈ P` to `P'(ψ(ũ))/Q(ψ(ũ))`. Since `ψ(xᵢ) = x^G_p` for `i ∈ θ(p)`,
applying this twice shows that `ψ` takes `P` into the subfield `𝕜(x̃^G)`; as `ψ` is onto, the `z_j`
lie there too, and the entries of `x̃^G` generate `F^G`. Finally `F^G` has transcendence degree
`m^G` over `𝕜`, and a family of `m^G` elements over which `F^G` is algebraic is a transcendence
basis, so the entries of `x̃^G` are algebraically independent
(`ClusterAlgebras.IsFreeGeneratingTuple.of_adjoin_eq_top`).

## Main results

* `ClusterAlgebras.FZSemifieldHom.coe_apply_mem_subfield`: a semifield homomorphism
  `ψ : ℚ_sf(w̃) → ℚ_sf(z̃)` sends every element of `ℚ_sf(ũ)`, for `ũ` a family in `ℚ_sf(w̃)`, into
  any subfield containing the `ψ(uᵢ)`.
* `ClusterAlgebras.isLabeledSeed_foldedSeed`: FWZ's Lemma 4.4.6, the folding of a
  `(G, ψ)`-admissible seed `μ_s(Σ°)` is a labeled seed.

## Implementation notes

FWZ pass through the equality `ℚ_sf(x̃) = P`. The proof here uses only the inclusion of
the generators `w̃` in `ℚ_sf(x̃)`, and applies the computation of `ψ` on subtraction-free
expressions twice: once in the `xᵢ` for the `w_j`, then once in the `w_j` for an arbitrary
element of `P`. This avoids having to prove `x̃` algebraically independent over `ℚ`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Lemma 4.4.6.
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial FZSemifield

/-! ### Semifield homomorphisms on subtraction-free expressions -/

section SubtractionFree

variable {F FG κ ι ι' : Type*} [Field F] [CharZero F] {w : κ → F} [Fact (AlgebraicIndependent ℚ w)]
  [Field FG] [CharZero FG] {z : ι → FG} [Fact (AlgebraicIndependent ℚ z)]

/-- Let `ψ : ℚ_sf(w̃) → ℚ_sf(z̃)` be a semifield homomorphism and `ũ` a family of elements of
`ℚ_sf(w̃)`. If a subfield `L` contains every `ψ(uᵢ)`, then it contains `ψ(v)` for every `v` in
`ℚ_sf(w̃) ∩ ℚ_sf(ũ)`. -/
theorem FZSemifieldHom.coe_apply_mem_subfield
    (ψ : FZSemifieldHom (universalSemifield w) (universalSemifield z)) {u : ι' → F}
    (hu : ∀ i, u i ∈ universalSemifield w) {L : Subfield FG}
    (hL : ∀ i, (ψ ⟨u i, hu i⟩ : FG) ∈ L) {v : F} (hv : v ∈ universalSemifield w)
    (hvu : v ∈ universalSemifield u) : (ψ ⟨v, hv⟩ : FG) ∈ L := by
  obtain ⟨P, Q, hP, hQ, h⟩ := hvu
  set g : ι' → universalSemifield w := fun i => ⟨u i, hu i⟩
  have hg : ∀ {R : MvPolynomial ι' ℕ}, R ≠ 0 → ((polyValue g R : universalSemifield w) : F) =
      aeval u R := fun hR => universalSemifield.coe_polyValue g hR
  have hQ0 : aeval u Q ≠ 0 := by
    rw [← hg hQ]
    exact universalSemifield.coe_ne_zero Fact.out _
  have hv' : (⟨v, hv⟩ : universalSemifield w) = polyValue g P / polyValue g Q :=
    Subtype.ext (by
      rw [universalSemifield.coe_div, hg hP, hg hQ]
      exact eq_div_of_mul_eq hQ0 (by rw [mul_comm, h]))
  have hmem : ∀ R : MvPolynomial ι' ℕ, aeval (fun i => (ψ (g i) : FG)) R ∈ L := fun R =>
    MvPolynomial.eval₂_mem (fun _ _ => natCast_mem L _) hL
  rw [hv', map_div, map_polyValue ψ g hP, map_polyValue ψ g hQ, universalSemifield.coe_div,
    universalSemifield.coe_polyValue _ hP, universalSemifield.coe_polyValue _ hQ]
  exact div_mem (hmem P) (hmem Q)

end SubtractionFree

/-! ### The folded seed -/

variable {G : Type*} [Group G] {m n mG nG : ℕ} [MulAction G (Fin m)] {hmn : n ≤ m}
  {K : Type*} [Field K] [CharZero K] {F : Type*} [Field F] [CharZero F] [Algebra K F]
  {FG : Type*} [Field FG] [CharZero FG] [Algebra K FG]

/-- **FWZ's Lemma 4.4.6.** Given folding data with `ψ : ℚ_sf(w̃) → ℚ_sf(z̃)` surjective, if the
seed `μ_s(Σ°)` obtained from the reference seed `Σ° = (w̃, B̃°)` by mutation along `s` is
`(G, ψ)`-admissible, then its folding `μ_s(Σ°)^G` is a labeled seed in `F^G` over `K`. -/
@[cluster_algebras "lem_folded_seed_is_seed"]
theorem isLabeledSeed_foldedSeed {S₀ : SeedData F m n} (hS₀ : IsLabeledSeed K hmn S₀)
    [Fact (AlgebraicIndependent ℚ S₀.extCluster)] {z : Fin mG → FG}
    [Fact (AlgebraicIndependent ℚ z)] (hz : IsFreeGeneratingTuple K z)
    (θ : OrbitLabelling G m n mG nG)
    (ψ : FZSemifieldHom (universalSemifield S₀.extCluster) (universalSemifield z))
    (hψ : Function.Surjective ψ) (s : List (Fin n))
    (hadm : IsFoldAdmissibleSeed G hmn ψ (seedMutationSeq hmn S₀ s)) :
    IsLabeledSeed K θ.le (foldedSeed θ ψ (seedMutationSeq hmn S₀ s)) := by
  set S := seedMutationSeq hmn S₀ s
  refine ⟨hz.of_adjoin_eq_top ?_, extSkewSymmetrizable_foldedMatrix hadm.admissible hadm.skew θ⟩
  set L := IntermediateField.adjoin K (Set.range (foldedSeed θ ψ S).extCluster)
  -- `ψ(xᵢ) = x^G_p` for `i ∈ θ(p)`, so `ψ(xᵢ) ∈ L`.
  have hx : ∀ i, (ψ ⟨S.extCluster i, hadm.mem i⟩ : FG) ∈ L.toSubfield := by
    intro i
    have hi : (ψ ⟨S.extCluster i, hadm.mem i⟩ : FG) =
        (foldedSeed θ ψ S).extCluster (θ.label i) := by
      change _ = foldValue ψ (S.extCluster (θ.rep (θ.label i)))
      rw [← hadm.foldValue_eq i _ (θ.mem_orbit_of_mem (θ.mem_orbit_label i) (θ.rep_mem _)),
        foldValue_of_mem ψ (hadm.mem i)]
    rw [hi]
    exact IntermediateField.subset_adjoin K _ ⟨_, rfl⟩
  -- `Σ° = μ_{s̄}(x̃, B̃)`, so each `w_j` is subtraction-free in `x̃`, and `ψ(w_j) ∈ L`.
  have hrev : seedMutationSeq hmn S s.reverse = S₀ := by
    simpa using seedMutationSeq_seedMutationSeq_reverse hmn hS₀ s.reverse
  have hw : ∀ j, (ψ ⟨S₀.extCluster j, mem_universalSemifield_self _ j⟩ : FG) ∈ L.toSubfield :=
    fun j => ψ.coe_apply_mem_subfield hadm.mem hx _
      (hrev ▸ seedMutationSeq_extCluster_mem_universalSemifield_self hmn S s.reverse j)
  -- Every `z_j` is some `ψ(v)`, hence lies in `L`.
  rw [eq_top_iff, ← hz.2, IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  obtain ⟨⟨v, hv⟩, hvj⟩ := hψ ⟨z j, mem_universalSemifield_self z j⟩
  have := ψ.coe_apply_mem_subfield (fun j => mem_universalSemifield_self _ j) hw hv hv
  rwa [hvj] at this

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Folding.SeedMutation
public import ClusterAlgebras.Folding.SkewSymmetrizable
public import ClusterAlgebras.SeedPattern

/-!
# Folding: the folded seed pattern of a globally foldable seed

Fix folding data with reference seed `(x̃, B̃)`: an orbit labelling `θ` of the action of `G`
on the indices, a globally foldable matrix `B̃` whose principal part is skew-symmetric, and a
semifield homomorphism `ψ : ℚ_sf(x̃) → ℚ_sf(z̃)` with `ψ(x_i) = z_p` for every label `p` and
every `i ∈ θ(p)`.

Orbit mutation along a sequence `ρ = (r₁, …, r_d)` of mutable labels is mutation along the
orbit sequence `θ(ρ)* = (s_{θ(r₁)}, …, s_{θ(r_d)})`. This file shows, by induction on `ρ`
from the right, that every seed `μ_{θ(ρ)*}(x̃, B̃)` is `(G, ψ)`-admissible — global
foldability supplies the `G`-admissibility of the next matrix — and that its folded seed is
`μ_ρ(z̃, B̃ᴳ)`. Since `(z̃, B̃ᴳ)` is a labeled seed, it is the seed at any chosen vertex of a
seed pattern, and the seeds of that pattern are exactly the folded seeds
`(μ_{θ(ρ)*}(x̃, B̃))ᴳ`.

## Main results

* `ClusterAlgebras.isFoldAdmissibleSeed_seedMutationSeq_orbitSeq`: every `μ_{θ(ρ)*}(x̃, B̃)`
  is `(G, ψ)`-admissible.
* `ClusterAlgebras.foldedSeed_seedMutationSeq_orbitSeq`:
  `(μ_{θ(ρ)*}(x̃, B̃))ᴳ = μ_ρ(z̃, B̃ᴳ)`.
* `ClusterAlgebras.exists_isSeedPattern_foldedSeed`: for every vertex `t₀` of `𝕋_{nG}` there
  is a seed pattern `Π` with `Π(t₀) = (z̃, B̃ᴳ)` whose seeds are the folded seeds
  `(μ_{θ(ρ)*}(x̃, B̃))ᴳ`.

## Implementation notes

* The reference seed `S = (x̃, B̃)` itself fixes `P = ℚ_sf(x̃)`. The first two results use
  neither that `S` is a labeled seed nor that `z̃` is a free generating tuple, and assume
  neither. The third needs `z̃` free generating, to make `(z̃, B̃ᴳ)` a labeled seed, but not
  that `S` is labeled. This generalises [FWZ], where `(x̃, B̃)` is assumed to be a labeled seed.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Section 4.4.
-/

@[expose] public section

namespace ClusterAlgebras

variable {G : Type*} [Group G] {m n mG nG : ℕ} [MulAction G (Fin m)] {hmn : n ≤ m}
  {F : Type*} [Field F] [CharZero F] {FG : Type*} [Field FG] [CharZero FG]
  (θ : OrbitLabelling G m n mG nG) {S : SeedData F m n}
  [Fact (AlgebraicIndependent ℚ S.extCluster)]
  {z : Fin mG → FG} [Fact (AlgebraicIndependent ℚ z)]
  (ψ : FZSemifieldHom (universalSemifield S.extCluster) (universalSemifield z))

/-- **Orbit mutations of a globally foldable seed are admissible** (FWZ, Section 4.4). In the
folding setting, for every sequence `ρ` of mutable labels, the seed `μ_{θ(ρ)*}(x̃, B̃)` is
`(G, ψ)`-admissible. -/
@[cluster_algebras "lem_globally_foldable_admissible"]
theorem isFoldAdmissibleSeed_seedMutationSeq_orbitSeq
    (hfold : IsGloballyFoldable θ hmn S.extExchangeMatrix)
    (hskew : ∀ i j : Fin n,
      S.extExchangeMatrix (Fin.castLE hmn i) j = -S.extExchangeMatrix (Fin.castLE hmn j) i)
    (hψ : ∀ p, ∀ i ∈ θ.orbit p,
      (ψ ⟨S.extCluster i, mem_universalSemifield_self _ i⟩ : FG) = z p)
    (ρ : List (Fin nG)) :
    IsFoldAdmissibleSeed G hmn ψ (seedMutationSeq hmn S (orbitSeq θ hmn ρ)) := by
  induction ρ using List.reverseRecOn with
  | nil =>
    change IsFoldAdmissibleSeed G hmn ψ S
    refine ⟨mem_universalSemifield_self _, hfold.1, hskew, fun i i' hii' => ?_⟩
    rw [foldValue_of_mem ψ (mem_universalSemifield_self _ i),
      foldValue_of_mem ψ (mem_universalSemifield_self _ i'),
      hψ _ i (θ.mem_orbit_label i), hψ _ i' (θ.mem_of_mem_orbit (θ.mem_orbit_label i) hii')]
  | append_singleton ρ r ih =>
    have hρ : orbitSeq θ hmn (ρ ++ [r]) = orbitSeq θ hmn ρ ++ increasingSeq (θ.cols hmn r) := by
      simp [orbitSeq, List.flatMap_append]
    rw [hρ, seedMutationSeq_append]
    refine ih.seedMutationSeq_increasingSeq θ r ?_
    rw [seedMutationSeq_extExchangeMatrix_eq_matrixMutationList, ← matrixMutationList_append,
      ← hρ]
    exact hfold.2 (ρ ++ [r])

/-- **Folding commutes with orbit mutation along a sequence** (FWZ, Section 4.4). In the
folding setting, for every sequence `ρ` of mutable labels,
`(μ_{θ(ρ)*}(x̃, B̃))ᴳ = μ_ρ(z̃, B̃ᴳ)`. -/
@[cluster_algebras "lem_folded_sequence"]
theorem foldedSeed_seedMutationSeq_orbitSeq
    (hfold : IsGloballyFoldable θ hmn S.extExchangeMatrix)
    (hskew : ∀ i j : Fin n,
      S.extExchangeMatrix (Fin.castLE hmn i) j = -S.extExchangeMatrix (Fin.castLE hmn j) i)
    (hψ : ∀ p, ∀ i ∈ θ.orbit p,
      (ψ ⟨S.extCluster i, mem_universalSemifield_self _ i⟩ : FG) = z p)
    (ρ : List (Fin nG)) :
    foldedSeed θ ψ (seedMutationSeq hmn S (orbitSeq θ hmn ρ)) =
      seedMutationSeq θ.le ⟨z, foldedMatrix θ S.extExchangeMatrix⟩ ρ := by
  induction ρ using List.reverseRecOn with
  | nil =>
    refine SeedData.ext (funext fun p => ?_) rfl
    exact (foldValue_of_mem ψ (mem_universalSemifield_self _ _)).trans
      (hψ p _ (θ.rep_mem p))
  | append_singleton ρ r ih =>
    have hρ : orbitSeq θ hmn (ρ ++ [r]) = orbitSeq θ hmn ρ ++ increasingSeq (θ.cols hmn r) := by
      simp [orbitSeq, List.flatMap_append]
    rw [hρ, seedMutationSeq_append, foldedSeed_seedMutationSeq_increasingSeq θ
      (isFoldAdmissibleSeed_seedMutationSeq_orbitSeq θ ψ hfold hskew hψ ρ) r, ih,
      seedMutationSeq_append]
    rfl

/-- **The folded seed pattern** (FWZ, Section 4.4). In the folding setting, with `z̃` a free
generating tuple of `F^G` over `K`, for every vertex `t₀` of `𝕋_{nG}` there is a seed pattern
`Π` of rank `nG` in `F^G` over `K` with `Π(t₀) = (z̃, B̃ᴳ)`, whose seeds are exactly the
folded seeds `(μ_{θ(ρ)*}(x̃, B̃))ᴳ`, `ρ` ranging over the sequences of mutable labels. -/
@[cluster_algebras "thm_folded_seed_pattern"]
theorem exists_isSeedPattern_foldedSeed {K : Type*} [Field K] [CharZero K] [Algebra K FG]
    (hfold : IsGloballyFoldable θ hmn S.extExchangeMatrix)
    (hskew : ∀ i j : Fin n,
      S.extExchangeMatrix (Fin.castLE hmn i) j = -S.extExchangeMatrix (Fin.castLE hmn j) i)
    (hz : IsFreeGeneratingTuple K z)
    (hψ : ∀ p, ∀ i ∈ θ.orbit p,
      (ψ ⟨S.extCluster i, mem_universalSemifield_self _ i⟩ : FG) = z p)
    (t₀ : RegularTree nG) :
    ∃ Pat : RegularTree nG → SeedData FG mG nG, IsSeedPattern K θ.le Pat ∧
      Pat t₀ = ⟨z, foldedMatrix θ S.extExchangeMatrix⟩ ∧
      Set.range Pat = Set.range fun ρ : List (Fin nG) =>
        foldedSeed θ ψ (seedMutationSeq hmn S (orbitSeq θ hmn ρ)) := by
  obtain ⟨Pat, hPat, h₀⟩ := exists_isSeedPattern θ.le t₀
    (S₀ := ⟨z, foldedMatrix θ S.extExchangeMatrix⟩)
    ⟨hz, extSkewSymmetrizable_foldedMatrix hfold.1 hskew θ⟩
  refine ⟨Pat, hPat, h₀, Set.ext fun T => ⟨?_, ?_⟩⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨ρ, hρ⟩ := hPat.exists_seedMutationSeq_eq θ.le t₀ t
    exact ⟨ρ, by dsimp only; rw [foldedSeed_seedMutationSeq_orbitSeq θ ψ hfold hskew hψ, hρ, h₀]⟩
  · rintro ⟨ρ, rfl⟩
    dsimp only
    rw [foldedSeed_seedMutationSeq_orbitSeq θ ψ hfold hskew hψ, ← h₀]
    exact hPat.seedMutationSeq_mem_range θ.le t₀ ρ

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Coefficients.Trivialization
public import ClusterAlgebras.SeedPattern

/-!
# Transport of seeds along ring homomorphisms

Let `F` and `K` be fields, `R ⊆ F` a subring and `φ : R → K` a ring homomorphism. A seed
`(x̃, B̃)` in `F` whose entries lie in `R` can be carried to `K` by applying `φ` to its entries;
if `φ` sends some frozen variables `xᵢ`, `i ∈ I ⊆ [n + 1, m]`, to `1`, these can then be
deleted by the trivialization `Tr_I`. This file shows that the resulting operation
`(x̃, B̃) ↦ Tr_I(φ(x̃), B̃)` commutes with seed mutation, as long as the entry being mutated is
not sent to `0` and the mutated entry still lies in `R`; and deduces that it carries a seed
pattern whose entries lie in `R` to a seed pattern, as soon as it carries one of its seeds to
a labeled seed.

## Main results

* `ClusterAlgebras.seedMutation_trivialize_map`: seed mutation commutes with a ring
  homomorphism followed by a trivialization,
  `μₖ(Tr_I(φ(x̃), B̃)) = Tr_I(φ(x̃'), μₖ(B̃))`.
* `ClusterAlgebras.IsSeedPattern.exists_isSeedPattern_trivialize_map`: transporting a seed
  pattern along a ring homomorphism; if `Tr_I(φ(x̃(t₀)), B̃(t₀))` is a labeled seed in a
  subfield `F' ⊆ K`, then so is every `Tr_I(φ(x̃(t)), B̃(t))`, and they form a seed pattern.

## Implementation notes

* A seed of `F` with entries in the subring `R` is written as a seed `S : SeedData R m n`
  over `R`; the seed in `F` is `S.map (↑)` and its image under `φ` is `S.map φ`. Accordingly
  a seed pattern `Σ` in `F` all of whose entries lie in `R` is a family
  `Q : 𝕋ₙ → SeedData R m n` such that `t ↦ (Q t).map (↑)` is a seed pattern; every seed
  pattern in `F` with entries in `R` arises in this way, with `Σ(t) = (Q t).map (↑)` by
  definition.

* Indices start at `0`: FWZ's `I ⊆ [n + 1, m]` is `I : Finset (Fin m)` with `n ≤ i`
  for every `i ∈ I`, and position `k ∈ [1, n]` is `Fin.castLE hmn k` for `k : Fin n`.

* FWZ assume `xₖ ≠ 0` in `F` in `seedMutation_trivialize_map`. This follows from
  `φ(xₖ) ≠ 0`, as `φ(0) = 0`, so it is not stated.

* "`Tr_I(φ(x̃(t₀)), B̃(t₀))` is a labeled seed in the subfield `F'` of `K`" is stated as the
  existence of a labeled seed `S₀` in `F'`, an `IntermediateField` of `K` over the ground
  field `𝕜`, whose entries read in `K` are those of `Tr_I(φ(x̃(t₀)), B̃(t₀))`
  (`S₀.map (↑) = Tr_I(φ(x̃(t₀)), B̃(t₀))`). The conclusion is a seed pattern in `F'` whose seeds
  read in `K` are the `Tr_I(φ(x̃(t)), B̃(t))`.

* The hypothesis that `φ` sends the frozen variables `xᵢ`, `i ∈ I`, to `1` is stated at the
  vertex `t₀` only: the frozen variables of a seed pattern do not depend on the vertex.

* The ring homomorphism `φ` is not required to be compatible with the ground field `𝕜`: the
  seeds `Tr_I(φ(x̃(t)), B̃(t))` are labeled seeds over `𝕜` because one of them is.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6,
  Section 6.2.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

variable {m n : ℕ} {F K : Type*} [Field F] [Field K]

/-- **Seed mutation commutes with a ring homomorphism followed by a trivialization.** Let
`R ⊆ F` be a subring, `φ : R → K` a ring homomorphism, `S = (x̃, B̃)` a seed with entries in
`R`, `k ∈ [1, n]`, and suppose the entry `x'ₖ` in position `k` of `μₖ(x̃, B̃)`, computed in `F`,
lies in `R`, that `φ(xₖ) ≠ 0`, and that `φ(xᵢ) = 1` for every `i ∈ I ⊆ [n + 1, m]`. Then
`μₖ(Tr_I(φ(x̃), B̃)) = Tr_I(φ(x̃'), μₖ(B̃))`, where `x̃'` is `x̃` with its entry in position `k`
replaced by `x'ₖ`. -/
@[cluster_algebras "lem_seed_mutation_transport"]
theorem seedMutation_trivialize_map (hmn : n ≤ m) {R : Subring F} (S : SeedData R m n)
    (k : Fin n) {x' : R}
    (hx' : (seedMutation hmn (S.map ((↑) : R → F)) k).extCluster (Fin.castLE hmn k) = x')
    (φ : R →+* K) (hφk : φ (S.extCluster (Fin.castLE hmn k)) ≠ 0) {I : Finset (Fin m)}
    (hI : ∀ i ∈ I, n ≤ (i : ℕ)) (hφI : ∀ i ∈ I, φ (S.extCluster i) = 1) :
    seedMutation (le_card_univ_sdiff hmn hI) ((S.map φ).trivialize I) k =
      ((⟨Function.update S.extCluster (Fin.castLE hmn k) x',
          matrixMutation hmn S.extExchangeMatrix k⟩ : SeedData R m n).map φ).trivialize I := by
  classical
  obtain ⟨x, B⟩ := S
  dsimp only at hx' hφk hφI ⊢
  have hmn' := le_card_univ_sdiff hmn hI
  have hι : Function.Injective (restrictionEnumeration n (univ \ I)) :=
    restrictionEnumeration_injective n _
  have hιn := restrictionEnumeration_univ_sdiff_castLE hmn hI hmn'
  have hxc : (x (Fin.castLE hmn k) : F) ≠ 0 := fun h =>
    hφk (by rw [show x (Fin.castLE hmn k) = 0 from Subtype.ext h, map_zero])
  have hrel : x (Fin.castLE hmn k) * x' =
      (∏ i, x i ^ (B i k).toNat) + ∏ i, x i ^ (-B i k).toNat := by
    apply Subtype.ext
    rw [Subring.coe_mul, ← hx']
    simp only [seedMutation, SeedData.map_extCluster, SeedData.map_extExchangeMatrix,
      Function.update_self, exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod,
      Function.comp_apply]
    push_cast
    field_simp
  have hφ : ∀ e : Fin m → ℕ, φ (∏ i, x i ^ e i) =
      ∏ a, (φ (x (restrictionEnumeration n (univ \ I) a))) ^
        e (restrictionEnumeration n (univ \ I) a) := fun e => by
    rw [map_prod]
    refine (Fintype.prod_of_injective _ hι _ _ (fun i hi => ?_) fun a => by
      rw [map_pow]).symm
    rw [map_pow, hφI i (mem_of_notMem_range_restrictionEnumeration_univ_sdiff hi), one_pow]
  refine SeedData.ext (funext fun a => ?_) ?_
  · by_cases ha : a = Fin.castLE hmn' k
    · subst ha
      simp only [seedMutation, SeedData.trivialize_extCluster, SeedData.map_extCluster,
        SeedData.trivialize_extExchangeMatrix, SeedData.map_extExchangeMatrix,
        Function.update_self, Function.comp_apply, hιn, exchangeMonomialPos_eq_prod,
        exchangeMonomialNeg_eq_prod, Matrix.submatrix_apply, id]
      rw [eq_comm, eq_div_iff hφk, ← map_mul, mul_comm, hrel, map_add, hφ, hφ]
    · have hac : restrictionEnumeration n (univ \ I) a ≠ Fin.castLE hmn k := fun h =>
        ha (hι (h.trans (hιn k).symm))
      simp only [seedMutation, SeedData.trivialize_extCluster, SeedData.map_extCluster,
        Function.update_of_ne ha, Function.comp_apply, Function.update_of_ne hac]
  · exact matrixMutation_submatrix_rows hmn hmn' B hι hιn k

/-- Two seeds with entries in `R` at the two ends of an edge `t —k— t'` of a seed pattern: the
seed at `t'` is the seed at `t` with its entry in position `k` replaced, and its matrix mutated
in direction `k`. -/
private theorem eq_update_of_map_eq_seedMutation (hmn : n ≤ m) {R : Subring F}
    {S S' : SeedData R m n} {k : Fin n}
    (h : S'.map ((↑) : R → F) = seedMutation hmn (S.map ((↑) : R → F)) k) :
    S' = ⟨Function.update S.extCluster (Fin.castLE hmn k) (S'.extCluster (Fin.castLE hmn k)),
      matrixMutation hmn S.extExchangeMatrix k⟩ := by
  refine SeedData.ext (funext fun i => ?_) (congrArg SeedData.extExchangeMatrix h :)
  dsimp only
  by_cases hi : i = Fin.castLE hmn k
  · rw [hi, Function.update_self]
  · rw [Function.update_of_ne hi]
    exact Subtype.ext ((congrFun (congrArg SeedData.extCluster h) i).trans
      (Function.update_of_ne hi _ _))

variable {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 F] [Algebra 𝕜 K]

/-- One step of the transport along an edge `t —k— t'` of a seed pattern: if `φ` sends the frozen
variables `xᵢ`, `i ∈ I`, of the seed at `t` to `1` and `Tr_I(φ(x̃(t)), B̃(t))` is a labeled seed
in `F'`, then mutating it in direction `k` gives `Tr_I(φ(x̃(t')), B̃(t'))`, and both properties
hold at `t'`. -/
private theorem seedMutation_trivialize_map_of_adj [CharZero 𝕜] (hmn : n ≤ m) {R : Subring F}
    {Q : RegularTree n → SeedData R m n}
    (hQ : IsSeedPattern 𝕜 hmn fun t => (Q t).map ((↑) : R → F)) (φ : R →+* K)
    {I : Finset (Fin m)} (hI : ∀ i ∈ I, n ≤ (i : ℕ)) {F' : IntermediateField 𝕜 K} {k : Fin n}
    {t t' : RegularTree n} (hadj : RegularTree.Adj k t t')
    (h : (∀ i ∈ I, φ ((Q t).extCluster i) = 1) ∧
      ∃ S : SeedData F' (univ \ I).card n, IsLabeledSeed 𝕜 (le_card_univ_sdiff hmn hI) S ∧
        S.map ((↑) : F' → K) = ((Q t).map φ).trivialize I) :
    seedMutation (le_card_univ_sdiff hmn hI) (((Q t).map φ).trivialize I) k =
        ((Q t').map φ).trivialize I ∧
      (∀ i ∈ I, φ ((Q t').extCluster i) = 1) ∧
        ∃ S : SeedData F' (univ \ I).card n, IsLabeledSeed 𝕜 (le_card_univ_sdiff hmn hI) S ∧
          S.map ((↑) : F' → K) = ((Q t').map φ).trivialize I := by
  obtain ⟨hfr, S, hS, hSQ⟩ := h
  have hmn' := le_card_univ_sdiff hmn hI
  have hQt' := eq_update_of_map_eq_seedMutation hmn (hQ.2 k t t' hadj)
  have hφk : φ ((Q t).extCluster (Fin.castLE hmn k)) ≠ 0 := by
    have h := congrArg (fun S : SeedData K _ n => S.extCluster (Fin.castLE hmn' k)) hSQ
    simp only [SeedData.map_extCluster, SeedData.trivialize_extCluster, Function.comp_apply,
      restrictionEnumeration_univ_sdiff_castLE hmn hI hmn'] at h
    rw [← h]
    exact_mod_cast hS.1.1.ne_zero _
  have hmut : seedMutation hmn' (((Q t).map φ).trivialize I) k = ((Q t').map φ).trivialize I := by
    rw [seedMutation_trivialize_map hmn (Q t) k
      (congrArg (fun S : SeedData F m n => S.extCluster (Fin.castLE hmn k))
        (hQ.2 k t t' hadj)).symm φ hφk hI hfr, ← hQt']
  refine ⟨hmut, fun i hi => ?_, seedMutation hmn' S k, hS.seedMutation hmn' k, ?_⟩
  · have hik : i ≠ Fin.castLE hmn k := fun h => absurd (hI i hi) (not_le.2 (h ▸ k.isLt))
    rw [hQt']
    dsimp only
    rw [Function.update_of_ne hik, hfr i hi]
  · rw [← hmut, ← hSQ]
    exact seedMutation_map hmn' F'.val S k

/-- **Transporting a seed pattern along a ring homomorphism.** Let `Σ` be a seed pattern of
rank `n` in `F` over `𝕜` all of whose entries lie in a subring `R ⊆ F`, written
`Σ(t) = (Q t).map (↑)` for seeds `Q t` over `R`; let `φ : R → K` be a ring homomorphism to a
field `K` containing `𝕜`, and `I ⊆ [n + 1, m]` with `φ(xᵢ) = 1` for the frozen variables `xᵢ`,
`i ∈ I`, of `Σ`. If for some vertex `t₀` the seed `Tr_I(φ(x̃(t₀)), B̃(t₀))` is a labeled seed in
a subfield `F' ⊆ K` over `𝕜`, then `t ↦ Tr_I(φ(x̃(t)), B̃(t))` is a seed pattern in `F'` over
`𝕜`: there is a seed pattern in `F'` whose seed at `t`, read in `K`, is
`Tr_I(φ(x̃(t)), B̃(t))`. -/
@[cluster_algebras "lem_transport_pattern"]
theorem IsSeedPattern.exists_isSeedPattern_trivialize_map [CharZero 𝕜] (hmn : n ≤ m)
    {R : Subring F} {Q : RegularTree n → SeedData R m n}
    (hQ : IsSeedPattern 𝕜 hmn fun t => (Q t).map ((↑) : R → F)) (φ : R →+* K)
    {I : Finset (Fin m)} (hI : ∀ i ∈ I, n ≤ (i : ℕ)) (t₀ : RegularTree n)
    (hφI : ∀ i ∈ I, φ ((Q t₀).extCluster i) = 1) (F' : IntermediateField 𝕜 K)
    (hF' : ∃ S₀ : SeedData F' (univ \ I).card n,
      IsLabeledSeed 𝕜 (le_card_univ_sdiff hmn hI) S₀ ∧
        S₀.map ((↑) : F' → K) = ((Q t₀).map φ).trivialize I) :
    ∃ P' : RegularTree n → SeedData F' (univ \ I).card n,
      IsSeedPattern 𝕜 (le_card_univ_sdiff hmn hI) P' ∧
        ∀ t, (P' t).map ((↑) : F' → K) = ((Q t).map φ).trivialize I := by
  classical
  have hmn' := le_card_univ_sdiff hmn hI
  let G : RegularTree n → Prop := fun t => (∀ i ∈ I, φ ((Q t).extCluster i) = 1) ∧
    ∃ S : SeedData F' (univ \ I).card n, IsLabeledSeed 𝕜 hmn' S ∧
      S.map ((↑) : F' → K) = ((Q t).map φ).trivialize I
  have hG (t : RegularTree n) : G t := by
    obtain ⟨d, s, κ, h0, hl, hs⟩ := RegularTree.exists_walk t₀ t
    have (j : Fin (d + 1)) : G (s j) := by
      induction j using Fin.induction with
      | zero => exact h0 ▸ ⟨hφI, hF'⟩
      | succ j ih => exact (seedMutation_trivialize_map_of_adj hmn hQ φ hI (hs j) ih).2
    exact hl ▸ this (Fin.last d)
  choose P' hP' hP'Q using fun t => (hG t).2
  have hinj : ∀ {S S' : SeedData F' (univ \ I).card n},
      S.map ((↑) : F' → K) = S'.map ((↑) : F' → K) → S = S' := fun h =>
    SeedData.ext (funext fun a => Subtype.ext (congrFun (congrArg SeedData.extCluster h) a))
      (congrArg SeedData.extExchangeMatrix h :)
  refine ⟨P', ⟨hP', fun k t t' hadj => hinj ?_⟩, hP'Q⟩
  rw [hP'Q, ← (seedMutation_trivialize_map_of_adj hmn hQ φ hI hadj (hG t)).1, ← hP'Q]
  exact (seedMutation_map hmn' F'.val (P' t) k).symm

end ClusterAlgebras

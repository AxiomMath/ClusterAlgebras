/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.ExchangeMatrix
public import ClusterAlgebras.Restriction.Enumeration
public import ClusterAlgebras.Subpattern.SeedReindex

/-!
# Restricting a seed to a set of indices

For `I ⊆ [0, m)` the *restriction* of a seed `(x̃, B̃)` to `I` is
`(x̃, B̃)_I = ((x_{ι_I(0)}, …, x_{ι_I(|I| - 1)}), B̃_I)`, where `ι_I` is the enumeration of `I`
listing its mutable elements first (`ClusterAlgebras.SeedData.restrict`). It is the
reindexing of `(x̃, B̃)` along `ι_I` (`ClusterAlgebras.SeedData.restrict_eq_reindex`), so
FWZ's Lemma 4.2.4, that restriction commutes with mutation at an index of `I` when `ι_I` is
closed for `B̃`, is `ClusterAlgebras.seedMutation_reindex` with `r = ι_I`
(`ClusterAlgebras.seedMutation_restrict`).

For the extended exchange matrix `B̃(Q, λ)` of a quiver `Q` under a labelling `λ`,
closedness of `ι_I` has a reading in `Q`: with `U = λ(I)`, no arrow joins a mutable vertex of
`U` to a vertex outside `U`, in either direction
(`ClusterAlgebras.isClosedFor_enumerationMap_extExchangeMatrix_iff`).

## Main definitions

* `ClusterAlgebras.SeedData.restrict`: the restriction `(x̃, B̃)_I` of a seed to `I`.

## Main results

* `ClusterAlgebras.SeedData.restrict_eq_reindex`: `(x̃, B̃)_I = (x̃, B̃)^{ι_I}`.
* `ClusterAlgebras.seedMutation_restrict`: if `ι_I` is closed for `B̃`, then
  `μ_q((x̃, B̃)_I) = (μ_{ι_I(q)}(x̃, B̃))_I` (FWZ, Lemma 4.2.4).
* `ClusterAlgebras.isClosedFor_enumerationMap_extExchangeMatrix_iff`: `ι_I` is closed for
  `B̃(Q, λ)` if and only if `a(u, v) = a(v, u) = 0` for every mutable `u ∈ λ(I)` and every
  `v ∉ λ(I)`.

## Implementation notes

* FWZ's restricted seed (their Definition 4.2.3) is defined only when `ι_I` is closed for
  `B̃`. Here `SeedData.restrict` is defined for every `I`, and closedness is a hypothesis of
  the results that need it.

* FWZ index the restricted seed by `I` itself; here it is renumbered by `ι_I`, so that it is
  again a seed of the shape `SeedData F m' n'` with `m' = |I|` and `n' = n_I`, its mutable
  indices forming the initial segment `[0, n_I)`.

* The definition is given directly, by the formula above, rather than as an abbreviation
  of `SeedData.reindex`; the two agree by `rfl`, recorded as `SeedData.restrict_eq_reindex`,
  through which the results on reindexing apply.

* The quiver criterion is stated for a quiver whose vertex type is any finite type `V`,
  with `U` the image `I.map L.equiv.toEmbedding` of `I` under the labelling. The
  conditions `|V| = m` and `|V \ F| = n` are encoded in the labelling `L : Labelling Q m n`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 4–5*][FWZ17]
-/

@[expose] public section

namespace ClusterAlgebras

variable {m n : ℕ}

/-! ### The restricted seed -/

section Restrict

variable {F : Type*}

/-- The **restriction** `(x̃, B̃)_I` of a seed to `I ⊆ [0, m)`: its extended cluster is
`(x_{ι_I(0)}, …, x_{ι_I(|I| - 1)})` and its extended exchange matrix is the restricted matrix
`B̃_I`, where `ι_I` is the enumeration of `I`. -/
@[cluster_algebras "def_restricted_seed"]
def SeedData.restrict (S : SeedData F m n) (I : Finset (Fin m)) :
    SeedData F I.card (mutableCard n I) where
  extCluster := S.extCluster ∘ restrictionEnumeration n I
  extExchangeMatrix := matrixRestriction S.extExchangeMatrix I

/-- The extended cluster of a restricted seed. -/
@[simp]
theorem SeedData.restrict_extCluster (S : SeedData F m n) (I : Finset (Fin m)) :
    (S.restrict I).extCluster = S.extCluster ∘ restrictionEnumeration n I :=
  rfl

/-- The extended exchange matrix of a restricted seed. -/
@[simp]
theorem SeedData.restrict_extExchangeMatrix (S : SeedData F m n) (I : Finset (Fin m)) :
    (S.restrict I).extExchangeMatrix = matrixRestriction S.extExchangeMatrix I :=
  rfl

/-- **The restriction to `I` is the reindexing along the enumeration of `I`**:
`(x̃, B̃)_I = (x̃, B̃)^{ι_I}`. -/
theorem SeedData.restrict_eq_reindex (S : SeedData F m n) (I : Finset (Fin m)) :
    S.restrict I = S.reindex (mutableCard_le_card n I) (enumerationMap n I) :=
  rfl

end Restrict

/-! ### Restriction commutes with mutation -/

section SeedMutation

variable {F : Type*} [Field F]

/-- **Restriction commutes with mutation at an index of `I`** (FWZ, Lemma 4.2.4): if `ι_I` is
closed for `B̃`, then `μ_q((x̃, B̃)_I) = (μ_{ι_I(q)}(x̃, B̃))_I` for every `q < n_I`. This is
`seedMutation_reindex` along `r = ι_I`. -/
theorem seedMutation_restrict (h : n ≤ m) (S : SeedData F m n) {I : Finset (Fin m)}
    (hI : (enumerationMap n I).IsClosedFor (mutableCard_le_card n I) S.extExchangeMatrix)
    (q : Fin (mutableCard n I)) :
    seedMutation (mutableCard_le_card n I) (S.restrict I) q =
      (seedMutation h S ((enumerationMap n I).col (mutableCard_le_card n I) q)).restrict I :=
  seedMutation_reindex h (mutableCard_le_card n I) S hI q

/-- **Restriction commutes with mutation along a sequence of indices of `I`**: if `ι_I` is
closed for `B̃`, then `μ_s((x̃, B̃)_I) = (μ_{ι_I(s)}(x̃, B̃))_I`. -/
theorem seedMutationSeq_restrict (h : n ≤ m) (S : SeedData F m n) {I : Finset (Fin m)}
    (hI : (enumerationMap n I).IsClosedFor (mutableCard_le_card n I) S.extExchangeMatrix)
    (s : List (Fin (mutableCard n I))) :
    seedMutationSeq (mutableCard_le_card n I) (S.restrict I) s =
      (seedMutationSeq h S
        (s.map ((enumerationMap n I).col (mutableCard_le_card n I)))).restrict I :=
  seedMutationSeq_reindex h (mutableCard_le_card n I) S hI s

end SeedMutation

/-! ### Closedness for the matrix of a quiver -/

section Quiver

/-- The column map of the enumeration of `I` hits every mutable element of `I`: every element
of `I ∩ [0, n)` is `ι_I(q)` for some `q < n_I`. -/
theorem exists_val_col_enumerationMap_eq {I : Finset (Fin m)} {i : Fin m} (hi : i ∈ I)
    (hin : (i : ℕ) < n) :
    ∃ q : Fin (mutableCard n I),
      ((enumerationMap n I).col (mutableCard_le_card n I) q : ℕ) = i := by
  obtain ⟨p, rfl⟩ : i ∈ Set.range (enumerationMap n I) := by
    rwa [range_enumerationMap]
  refine ⟨⟨p, (val_restrictionEnumeration_lt_iff n I p).mp hin⟩, ?_⟩
  rw [ReindexingMap.val_col]
  rfl

/-- The column map of the enumeration of `I` takes its values in `I`. -/
theorem castLE_col_enumerationMap_mem (h : n ≤ m) (I : Finset (Fin m))
    (q : Fin (mutableCard n I)) :
    Fin.castLE h ((enumerationMap n I).col (mutableCard_le_card n I) q) ∈ I := by
  rw [ReindexingMap.castLE_col]
  exact restrictionEnumeration_mem n I _

variable {V : Type*} [Fintype V]

/-- **Closedness for the matrix of a quiver**: for a labelling `λ` of `Q` and `U = λ(I)`, the
enumeration `ι_I` is closed for `B̃(Q, λ)` if and only if `a(u, v) = a(v, u) = 0` for every
mutable vertex `u ∈ U` and every vertex `v ∉ U`. -/
@[cluster_algebras "lem_closed_iff_no_arrows"]
theorem isClosedFor_enumerationMap_extExchangeMatrix_iff (Q : Quiver V) (L : Labelling Q m n)
    (I : Finset (Fin m)) :
    (enumerationMap n I).IsClosedFor (mutableCard_le_card n I) (extExchangeMatrix Q L) ↔
      ∀ u ∈ I.map L.equiv.toEmbedding, u ∉ Q.frozen →
        ∀ v ∉ I.map L.equiv.toEmbedding, Q.arrows u v = 0 ∧ Q.arrows v u = 0 := by
  have hmem : ∀ i, L.equiv i ∈ I.map L.equiv.toEmbedding ↔ i ∈ I := fun i =>
    Finset.mem_map' L.equiv.toEmbedding
  have hrange : ∀ i, i ∈ Set.range (enumerationMap n I) ↔ i ∈ I := fun i => by
    rw [range_enumerationMap, Finset.mem_coe]
  refine ⟨fun hr u hu hfu v hv => ?_, fun hU q i hne => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨i, rfl⟩ := L.equiv.surjective v
    rw [Equiv.coe_toEmbedding] at hfu
    have hkn : (k : ℕ) < n := by
      rw [L.mem_frozen_iff] at hfu
      omega
    obtain ⟨q, hq⟩ := exists_val_col_enumerationMap_eq hk hkn
    have hcast : Fin.castLE L.le ((enumerationMap n I).col (mutableCard_le_card n I) q) = k :=
      Fin.ext hq
    have hzero := hr.eq_zero q (mt (hrange i).mp (mt (hmem i).mpr hv))
    simp only [extExchangeMatrix, Matrix.of_apply, hcast, signedCount] at hzero
    rw [Equiv.coe_toEmbedding]
    rcases Q.twoCycleFree (L.equiv k) (L.equiv i) with h0 | h0 <;> omega
  · by_contra hi
    obtain ⟨h1, h2⟩ := hU _ ((hmem _).mpr (castLE_col_enumerationMap_mem L.le I q))
      (L.notMem_frozen _) _ (mt (hmem i).mp (mt (hrange i).mpr hi))
    simp only [extExchangeMatrix, Matrix.of_apply, signedCount, h1, h2] at hne
    exact hne rfl

end Quiver

end ClusterAlgebras

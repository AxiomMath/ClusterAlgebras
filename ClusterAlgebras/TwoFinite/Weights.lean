/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.Defs
public import ClusterAlgebras.SkewSymmetrization

/-!
# Weights, arrows and the mutation rule

The elementary properties of weights and arrows of a skew-symmetrizable matrix, their relation
to the skew-symmetrization `S(B)` and the diagram `Γ(B)`, the mutation rule for weights and
arrows, and two facts about connectedness: mutation respects a splitting without adjacencies,
and a connected diagram has a vertex whose removal keeps it connected.

## Main results

* `ClusterAlgebras.SkewSymmetrizable.diag_eq_zero` and companions: the elementary properties of
  weights and arrows.
* `ClusterAlgebras.SkewSymmetrizable.skewSymmetrization_matrixMutation_of_eq` and companions:
  the mutation rule for `S(B)`.
* `ClusterAlgebras.SkewSymmetrizable.matrixMutation_eq_zero_of_split`: mutation respects a
  splitting without adjacencies.
* `ClusterAlgebras.IsConnectedDiagram.exists_isConnectedDiagram_submatrix_succAbove`: a connected
  diagram has a vertex whose removal keeps it connected.

## Implementation notes

* `S(B)` is `skewSymmetrization (B.map Int.cast)`, a real matrix.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n m : ℕ}

/-! ### Passing to real matrices -/

section Cast

/-- A skew-symmetrizing vector of an integer matrix skew-symmetrizes its real cast. -/
private theorem IsSkewSymmetrizingVector.map_intCast' {B : Matrix (Fin n) (Fin n) ℤ}
    {d : Fin n → ℤ} (hd : IsSkewSymmetrizingVector B d) :
    IsSkewSymmetrizingVector (B.map (Int.cast : ℤ → ℝ)) d :=
  ⟨hd.1, fun i j => by simpa using congrArg (Int.cast : ℤ → ℝ) (hd.2 i j)⟩

/-- The real cast of a skew-symmetrizable integer matrix is skew-symmetrizable. -/
theorem skewSymmetrizable_map_intCast {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) : SkewSymmetrizable (B.map (Int.cast : ℤ → ℝ)) :=
  let ⟨d, hd⟩ := hB
  ⟨d, hd.map_intCast'⟩

/-- Mutation commutes with the cast from integer to real matrices. -/
theorem matrixMutation_map_intCast (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    (matrixMutation hmn B k).map (Int.cast : ℤ → ℝ) =
      matrixMutation hmn (B.map (Int.cast : ℤ → ℝ)) k := by
  ext i j
  simp only [matrixMutation, Matrix.map_apply, Matrix.of_apply, Int.cast_pos, Int.cast_lt_zero]
  split_ifs <;> push_cast <;> rfl

/-- The weight, cast to `ℝ`, is the weight of the real cast. -/
private theorem cast_diagramWeight' (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (diagramWeight B i j : ℝ) = |(B i j : ℝ) * B j i| := by
  rw [diagramWeight, Nat.cast_natAbs]
  push_cast
  rfl

end Cast

/-! ### Skew-symmetrizability under mutation and reindexing -/

section Preservation

/-- A simultaneous reindexing `B^σ = (b_{σ(i) σ(j)})` of a skew-symmetrizable matrix is
skew-symmetrizable, for any map `σ` of the indices. -/
theorem skewSymmetrizable_submatrix {R : Type*} [CommRing R] {B : Matrix (Fin n) (Fin n) R}
    (hB : SkewSymmetrizable B) (σ : Fin m → Fin n) : SkewSymmetrizable (B.submatrix σ σ) :=
  let ⟨d, hd⟩ := hB
  ⟨d ∘ σ, fun i => hd.1 (σ i), fun i j => hd.2 (σ i) (σ j)⟩

/-- Mutation of a skew-symmetrizable square matrix keeps it skew-symmetrizable. -/
theorem skewSymmetrizable_matrixMutation {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {B : Matrix (Fin n) (Fin n) R} (hB : SkewSymmetrizable B)
    (k : Fin n) : SkewSymmetrizable (matrixMutation le_rfl B k) :=
  let ⟨d, hd⟩ := hB
  ⟨d, hd.matrixMutation le_rfl k⟩

/-- Mutation of a skew-symmetrizable square matrix along a sequence keeps it
skew-symmetrizable. -/
theorem skewSymmetrizable_matrixMutationList {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {B : Matrix (Fin n) (Fin n) R} (hB : SkewSymmetrizable B)
    (t : List (Fin n)) : SkewSymmetrizable (matrixMutationList le_rfl B t) := by
  induction t generalizing B with
  | nil => exact hB
  | cons k t ih => exact ih (skewSymmetrizable_matrixMutation hB k)

/-- A matrix of Dynkin shape `X` is skew-symmetrizable, being a relabelling of an orientation of
`ω_X`. -/
theorem HasDynkinShape.skewSymmetrizable {B : Matrix (Fin n) (Fin n) ℤ}
    {Xs : List DynkinSymbol} (h : HasDynkinShape B Xs) : SkewSymmetrizable B := by
  obtain ⟨σ, hσ, -⟩ := h
  simpa [Matrix.submatrix_submatrix] using skewSymmetrizable_submatrix hσ σ.symm

/-- A matrix of Dynkin shape `X`, `X` a single Dynkin symbol, has the size of the rank of `X`. -/
theorem HasDynkinShape.rank_eq {B : Matrix (Fin n) (Fin n) ℤ} {X : DynkinSymbol}
    (h : HasDynkinShape B [X]) : X.rank = n := by
  obtain ⟨σ, -⟩ := h
  simpa [DynkinSymbol.listRank] using Fintype.card_congr σ

end Preservation

/-! ### Elementary properties of weights and arrows -/

section WeightProps

variable {B B' : Matrix (Fin n) (Fin n) ℤ}

/-- A skew-symmetrizable matrix has zero diagonal. -/
@[cluster_algebras "lem_diagram_weight_props"]
theorem SkewSymmetrizable.diag_eq_zero (hB : SkewSymmetrizable B) (i : Fin n) : B i i = 0 :=
  let ⟨_, hd⟩ := hB
  hd.apply_self_eq_zero i

/-- The weight of a skew-symmetrizable matrix vanishes on the diagonal. -/
theorem SkewSymmetrizable.diagramWeight_self (hB : SkewSymmetrizable B) (i : Fin n) :
    diagramWeight B i i = 0 := by
  simp [diagramWeight, hB.diag_eq_zero i]

/-- The entries `bᵢⱼ`, `bⱼᵢ` of a skew-symmetrizable matrix are both zero or of opposite signs. -/
@[cluster_algebras "lem_diagram_weight_props"]
theorem SkewSymmetrizable.entries_sign (hB : SkewSymmetrizable B) (i j : Fin n) :
    (B i j = 0 ∧ B j i = 0) ∨ (0 < B i j ∧ B j i < 0) ∨ (B i j < 0 ∧ 0 < B j i) := by
  obtain ⟨d, hd⟩ := hB
  rcases lt_trichotomy (B i j) 0 with h | h | h
  · exact Or.inr (Or.inr ⟨h, (hd.pos_iff_neg j i).2 h⟩)
  · exact Or.inl ⟨h, (hd.apply_eq_zero_comm i j).1 h⟩
  · exact Or.inr (Or.inl ⟨h, (hd.pos_iff_neg i j).1 h⟩)

/-- The weight is positive exactly when `bᵢⱼ ≠ 0`. -/
@[cluster_algebras "lem_diagram_weight_props"]
theorem SkewSymmetrizable.diagramWeight_pos_iff (hB : SkewSymmetrizable B) (i j : Fin n) :
    0 < diagramWeight B i j ↔ B i j ≠ 0 := by
  obtain ⟨d, hd⟩ := hB
  rw [diagramWeight, Int.natAbs_pos, mul_ne_zero_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun h' => h ((hd.apply_eq_zero_comm i j).2 h')⟩⟩

/-- When `bᵢⱼ ≠ 0`, exactly one of the arrows `i → j` and `j → i` is present. -/
@[cluster_algebras "lem_diagram_weight_props"]
theorem SkewSymmetrizable.pos_xor_pos (hB : SkewSymmetrizable B) {i j : Fin n} (h : B i j ≠ 0) :
    Xor (0 < B i j) (0 < B j i) := by
  rcases hB.entries_sign i j with h' | h' | h'
  · exact absurd h'.1 h
  · exact Or.inl ⟨h'.1, fun h'' => lt_asymm h'' h'.2⟩
  · exact Or.inr ⟨h'.2, fun h'' => lt_asymm h'' h'.1⟩

/-- The entries of the skew-symmetrization: `sᵢⱼ = sgn(bᵢⱼ) √(w_B(i, j))`, so
`sᵢⱼ² = w_B(i, j)`, and `sᵢⱼ > 0` exactly when `i → j`. -/
@[cluster_algebras "lem_diagram_weight_props"]
theorem SkewSymmetrizable.skewSymmetrization_apply (hB : SkewSymmetrizable B) (i j : Fin n) :
    skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i j =
        Real.sign (B i j : ℝ) * √(diagramWeight B i j : ℝ) ∧
      skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i j ^ 2 = diagramWeight B i j ∧
      (0 < skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i j ↔ 0 < B i j) := by
  obtain ⟨d, hd⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · rw [ClusterAlgebras.skewSymmetrization_apply, cast_diagramWeight']
    rfl
  · rw [sq_skewSymmetrization, cast_diagramWeight']
    rfl
  · rw [hd.map_intCast'.pos_skewSymmetrization_iff]
    exact Int.cast_pos

/-- Two skew-symmetrizable matrices have the same diagram exactly when they have the same
weights and the same arrows. -/
@[cluster_algebras "lem_diagram_weight_props"]
theorem SkewSymmetrizable.diagram_eq_iff (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B') :
    diagram (B.map (Int.cast : ℤ → ℝ)) = diagram (B'.map (Int.cast : ℤ → ℝ)) ↔
      (∀ i j, diagramWeight B i j = diagramWeight B' i j) ∧ ∀ i j, (0 < B i j ↔ 0 < B' i j) := by
  obtain ⟨d, hd⟩ := hB
  obtain ⟨d', hd'⟩ := hB'
  have hw : ∀ i j, diagramWeight B i j = diagramWeight B' i j ↔
      |(B i j : ℝ) * B j i| = |(B' i j : ℝ) * B' j i| := fun i j => by
    rw [← cast_diagramWeight', ← cast_diagramWeight', Nat.cast_inj]
  rw [ClusterAlgebras.diagram_eq_iff]
  simp only [Matrix.map_apply, Int.cast_pos]
  refine ⟨fun h => ⟨fun i j => (hw i j).2 ?_, fun i j => (h i j).1⟩,
    fun ⟨hw', ha⟩ i j => ⟨ha i j, fun _ => (hw i j).1 (hw' i j)⟩⟩
  by_cases hij : 0 < B i j
  · exact (h i j).2 hij
  by_cases hji : 0 < B j i
  · rw [mul_comm, mul_comm (B' i j : ℝ)]
    exact (h j i).2 hji
  · have h₁ := hd.apply_eq_zero_of_not_pos hij hji
    have h₂ := hd'.apply_eq_zero_of_not_pos (mt (h i j).1.2 hij) (mt (h j i).1.2 hji)
    simp [h₁, h₂]

/-- If every weight of `B` is at most `1`, then `bᵢⱼ = sᵢⱼ ∈ {0, 1, -1}`. -/
@[cluster_algebras "lem_diagram_weight_props"]
theorem SkewSymmetrizable.entry_of_diagramWeight_le_one (hB : SkewSymmetrizable B)
    (hw : ∀ i j, diagramWeight B i j ≤ 1) (i j : Fin n) :
    (B i j : ℝ) = skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i j ∧
      (B i j = 0 ∨ B i j = 1 ∨ B i j = -1) := by
  have hone : B i j ≠ 0 → diagramWeight B i j = 1 := fun h =>
    le_antisymm (hw i j) ((hB.diagramWeight_pos_iff i j).2 h)
  have hval : B i j = 0 ∨ B i j = 1 ∨ B i j = -1 := by
    by_cases h0 : B i j = 0
    · exact Or.inl h0
    have h1 := hone h0
    rw [diagramWeight, Int.natAbs_mul, mul_eq_one] at h1
    exact Or.inr (Int.natAbs_eq_iff.1 h1.1)
  refine ⟨?_, hval⟩
  rw [(hB.skewSymmetrization_apply i j).1]
  rcases hval with h | h | h
  · simp [h]
  · rw [hone (by omega), h, Int.cast_one, Real.sign_of_pos one_pos]
    norm_num
  · rw [hone (by omega), h, Int.cast_neg, Int.cast_one, Real.sign_of_neg (by norm_num)]
    norm_num

/-- A skew-symmetrizable matrix all of whose weights are at most `1` is determined by its
arrows. -/
@[cluster_algebras "lem_diagram_weight_props"]
theorem SkewSymmetrizable.eq_of_diagramWeight_le_one (hB : SkewSymmetrizable B)
    (hB' : SkewSymmetrizable B') (hw : ∀ i j, diagramWeight B i j ≤ 1)
    (hw' : ∀ i j, diagramWeight B' i j ≤ 1) (harr : ∀ i j, 0 < B i j ↔ 0 < B' i j) :
    B = B' := by
  ext i j
  have h₁ := (hB.entry_of_diagramWeight_le_one hw i j).2
  have h₂ := (hB'.entry_of_diagramWeight_le_one hw' i j).2
  obtain ⟨d, hd⟩ := hB
  obtain ⟨d', hd'⟩ := hB'
  have hp := harr i j
  have hn : B i j < 0 ↔ B' i j < 0 := by
    rw [← hd.pos_iff_neg j i, ← hd'.pos_iff_neg j i]
    exact harr j i
  rcases h₁ with h | h | h <;> rcases h₂ with h' | h' | h' <;> simp [h, h'] at hp hn ⊢

/-- Reindexing along an injective map reads the weights and arrows of `B`:
`w_{B^r}(p, q) = w_B(r(p), r(q))` and `p → q` in `B^r` exactly when `r(p) → r(q)` in `B`. -/
@[cluster_algebras "lem_diagram_weight_props"]
theorem diagramWeight_submatrix (B : Matrix (Fin n) (Fin n) ℤ) (r : Fin m ↪ Fin n) (p q : Fin m) :
    diagramWeight (B.submatrix r r) p q = diagramWeight B (r p) (r q) ∧
      (0 < B.submatrix r r p q ↔ 0 < B (r p) (r q)) :=
  ⟨rfl, Iff.rfl⟩

/-- Matrices with the same diagram have reindexings with the same diagram. -/
@[cluster_algebras "lem_diagram_weight_props"]
theorem diagram_submatrix_eq_of_diagram_eq (h : diagram (B.map (Int.cast : ℤ → ℝ)) =
      diagram (B'.map (Int.cast : ℤ → ℝ))) (r : Fin m ↪ Fin n) :
    diagram ((B.submatrix r r).map (Int.cast : ℤ → ℝ)) =
      diagram ((B'.submatrix r r).map (Int.cast : ℤ → ℝ)) := by
  rw [ClusterAlgebras.diagram_eq_iff] at h ⊢
  exact fun p q => h (r p) (r q)

/-- `B` is connected exactly when no partition `[1, n] = I ⊔ J` into nonempty sets has
`bᵢⱼ = 0` for all `i ∈ I`, `j ∈ J`. -/
@[cluster_algebras "lem_diagram_weight_props"]
theorem SkewSymmetrizable.isConnectedDiagram_iff (hB : SkewSymmetrizable B) :
    IsConnectedDiagram B ↔
      ¬∃ I : Finset (Fin n), I.Nonempty ∧ Iᶜ.Nonempty ∧ ∀ i ∈ I, ∀ j ∉ I, B i j = 0 := by
  refine ⟨fun hc ⟨I, hI, hIc, hsep⟩ => ?_, fun hno P hP hPc => ?_⟩
  · obtain ⟨d, hd⟩ := hB
    obtain ⟨i, hi, j, hj, hij⟩ := hc (I : Set (Fin n)) (Finset.coe_nonempty.2 hI)
      (Finset.coe_compl I ▸ Finset.coe_nonempty.2 hIc)
    have h₁ := hsep i (Finset.mem_coe.1 hi) j (fun h => hj (Finset.mem_coe.2 h))
    rcases hij with h | h <;> simp [h₁, (hd.apply_eq_zero_comm i j).1 h₁] at h
  · classical
    by_contra hcon
    push Not at hcon
    refine hno ⟨Finset.univ.filter (· ∈ P), hP.imp fun i hi => by simpa using hi,
      hPc.imp fun j hj => by simpa using hj, fun i hi j hj => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    have h := hcon i hi j hj
    rcases hB.entries_sign i j with h' | h' | h'
    · exact h'.1
    · exact absurd (by simpa using h'.1) h.1
    · exact absurd (by simpa using h'.2) h.2

end WeightProps

/-! ### The mutation rule -/

section MutationRule

variable {B : Matrix (Fin n) (Fin n) ℤ}

/-- `S(μ_k(B)) = μ_k(S(B))` for an integer matrix `B`, read through the cast to `ℝ`. -/
private theorem SkewSymmetrizable.skewSymmetrization_map_matrixMutation'
    (hB : SkewSymmetrizable B) (k : Fin n) :
    skewSymmetrization ((matrixMutation le_rfl B k).map (Int.cast : ℤ → ℝ)) =
      matrixMutation le_rfl (skewSymmetrization (B.map (Int.cast : ℤ → ℝ))) k := by
  rw [matrixMutation_map_intCast]
  exact SkewSymmetrizable.skewSymmetrization_matrixMutation (skewSymmetrizable_map_intCast hB)
    le_rfl k

/-- An entry of `S(B)` is positive exactly when the entry of `B` is. -/
private theorem SkewSymmetrizable.skewSymmetrization_pos_iff' (hB : SkewSymmetrizable B)
    (i j : Fin n) :
    0 < skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i j ↔ 0 < B i j :=
  (hB.skewSymmetrization_apply i j).2.2

/-- An entry of `S(B)` is negative exactly when the entry of `B` is. -/
private theorem SkewSymmetrizable.skewSymmetrization_neg_iff' (hB : SkewSymmetrizable B)
    (i j : Fin n) :
    skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i j < 0 ↔ B i j < 0 := by
  obtain ⟨d, hd⟩ := id hB
  rw [(skewSymmetrizable_map_intCast hB).skewSymmetrization_apply_swap j i, neg_lt_zero,
    hB.skewSymmetrization_pos_iff', IsSkewSymmetrizingVector.pos_iff_neg hd]

/-- At an arrow `i → j`, the entry of `S(B)` is the square root of the weight. -/
theorem SkewSymmetrizable.skewSymmetrization_eq_sqrt (hB : SkewSymmetrizable B)
    {i j : Fin n} (h : 0 < B i j) :
    skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i j = √(diagramWeight B i j : ℝ) := by
  rw [(hB.skewSymmetrization_apply i j).1, Real.sign_of_pos (Int.cast_pos.2 h), one_mul]

/-- In rows and columns `k`, `s'ᵢⱼ = -sᵢⱼ`, where `S' = S(μ_k(B))`. -/
@[cluster_algebras "lem_diagram_mutation_rule"]
theorem SkewSymmetrizable.skewSymmetrization_matrixMutation_of_eq (hB : SkewSymmetrizable B)
    (k : Fin n) {i j : Fin n} (h : i = k ∨ j = k) :
    skewSymmetrization ((matrixMutation le_rfl B k).map (Int.cast : ℤ → ℝ)) i j =
      -skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i j := by
  rw [hB.skewSymmetrization_map_matrixMutation', matrixMutation_apply_of_eq _ _ _ h]

/-- If `i → k → j`, then `s'ᵢⱼ = sᵢⱼ + √(w_B(i, k) w_B(k, j))` and `s'ⱼᵢ = -s'ᵢⱼ`, where
`S' = S(μ_k(B))`. -/
@[cluster_algebras "lem_diagram_mutation_rule"]
theorem SkewSymmetrizable.skewSymmetrization_matrixMutation_of_pos_pos (hB : SkewSymmetrizable B)
    {i k j : Fin n} (hik : 0 < B i k) (hkj : 0 < B k j) :
    skewSymmetrization ((matrixMutation le_rfl B k).map (Int.cast : ℤ → ℝ)) i j =
        skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i j +
          √((diagramWeight B i k : ℝ) * diagramWeight B k j) ∧
      skewSymmetrization ((matrixMutation le_rfl B k).map (Int.cast : ℤ → ℝ)) j i =
        -skewSymmetrization ((matrixMutation le_rfl B k).map (Int.cast : ℤ → ℝ)) i j := by
  have hi : i ≠ k := by
    rintro rfl
    exact (lt_irrefl _) (hB.diag_eq_zero i ▸ hik)
  have hj : j ≠ k := by
    rintro rfl
    exact (lt_irrefl _) (hB.diag_eq_zero j ▸ hkj)
  refine ⟨?_, ?_⟩
  · rw [hB.skewSymmetrization_map_matrixMutation', matrixMutation_apply_of_ne _ _ _ hi hj,
      castLE_self,
      if_pos ⟨(hB.skewSymmetrization_pos_iff' i k).2 hik,
        (hB.skewSymmetrization_pos_iff' k j).2 hkj⟩,
      hB.skewSymmetrization_eq_sqrt hik, hB.skewSymmetrization_eq_sqrt hkj,
      ← Real.sqrt_mul (Nat.cast_nonneg _)]
  · obtain ⟨d, hd⟩ := hB
    exact SkewSymmetrizable.skewSymmetrization_apply_swap
      ⟨d, (hd.matrixMutation le_rfl k).map_intCast'⟩ i j

/-- If `i, j ≠ k` and neither `i → k → j` nor `j → k → i`, then `s'ᵢⱼ = sᵢⱼ`, where
`S' = S(μ_k(B))`. -/
@[cluster_algebras "lem_diagram_mutation_rule"]
theorem SkewSymmetrizable.skewSymmetrization_matrixMutation_of_not (hB : SkewSymmetrizable B)
    {i k j : Fin n} (hi : i ≠ k) (hj : j ≠ k) (h₁ : ¬(0 < B i k ∧ 0 < B k j))
    (h₂ : ¬(0 < B j k ∧ 0 < B k i)) :
    skewSymmetrization ((matrixMutation le_rfl B k).map (Int.cast : ℤ → ℝ)) i j =
      skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i j := by
  obtain ⟨d, hd⟩ := id hB
  have c₁ : ¬(0 < skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i k ∧
      0 < skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) k j) := fun h =>
    h₁ ⟨(hB.skewSymmetrization_pos_iff' i k).1 h.1, (hB.skewSymmetrization_pos_iff' k j).1 h.2⟩
  have c₂ : ¬(skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) i k < 0 ∧
      skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) k j < 0) := fun h =>
    h₂ ⟨(hd.pos_iff_neg j k).2 ((hB.skewSymmetrization_neg_iff' k j).1 h.2),
      (hd.pos_iff_neg k i).2 ((hB.skewSymmetrization_neg_iff' i k).1 h.1)⟩
  rw [hB.skewSymmetrization_map_matrixMutation', matrixMutation_apply_of_ne _ _ _ hi hj,
    castLE_self, if_neg c₁, if_neg c₂]

/-- **The weights at `k` are unchanged and the arrows at `k` are reversed** by `μ_k`. -/
@[cluster_algebras "lem_diagram_mutation_rule"]
theorem SkewSymmetrizable.diagramWeight_matrixMutation_self (hB : SkewSymmetrizable B)
    (k i : Fin n) :
    diagramWeight (matrixMutation le_rfl B k) i k = diagramWeight B i k ∧
      diagramWeight (matrixMutation le_rfl B k) k i = diagramWeight B k i ∧
      (0 < matrixMutation le_rfl B k i k ↔ 0 < B k i) ∧
      (0 < matrixMutation le_rfl B k k i ↔ 0 < B i k) := by
  obtain ⟨d, hd⟩ := hB
  have h₁ : matrixMutation le_rfl B k i k = -B i k := matrixMutation_apply_col _ _ _ _
  have h₂ : matrixMutation le_rfl B k k i = -B k i := matrixMutation_apply_row le_rfl B k i
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [diagramWeight, h₁, h₂, neg_mul_neg]
  · simp only [diagramWeight, h₁, h₂, neg_mul_neg]
  · rw [h₁, neg_pos]
    exact (hd.pos_iff_neg k i).symm
  · rw [h₂, neg_pos]
    exact (hd.pos_iff_neg i k).symm

/-- **Mutation at a source or a sink** keeps all weights, keeps the arrows not involving `k`,
and reverses the arrows involving `k`. -/
@[cluster_algebras "lem_diagram_mutation_rule"]
theorem SkewSymmetrizable.matrixMutation_of_isMatrixSource_or_isMatrixSink
    (hB : SkewSymmetrizable B) {k : Fin n} (hk : IsMatrixSource B k ∨ IsMatrixSink B k) :
    (∀ i j, diagramWeight (matrixMutation le_rfl B k) i j = diagramWeight B i j) ∧
      (∀ i j, i ≠ k → j ≠ k → (0 < matrixMutation le_rfl B k i j ↔ 0 < B i j)) ∧
      ∀ i, (0 < matrixMutation le_rfl B k i k ↔ 0 < B k i) ∧
        (0 < matrixMutation le_rfl B k k i ↔ 0 < B i k) := by
  obtain ⟨d, hd⟩ := id hB
  have hoff : ∀ i j, i ≠ k → j ≠ k → matrixMutation le_rfl B k i j = B i j := by
    intro i j hi hj
    have c : ¬(0 < B i k ∧ 0 < B k j) ∧ ¬(B i k < 0 ∧ B k j < 0) := by
      rcases hk with hk | hk
      · exact ⟨fun h => (hk i).not_gt ((hd.pos_iff_neg i k).1 h.1),
          fun h => (hk j).not_gt h.2⟩
      · exact ⟨fun h => (hk j).not_gt h.2,
          fun h => (hk i).not_gt ((hd.pos_iff_neg k i).2 h.1)⟩
    rw [matrixMutation_apply_of_ne _ _ _ hi hj, castLE_self, if_neg c.1, if_neg c.2]
  refine ⟨fun i j => ?_, fun i j hi hj => by rw [hoff i j hi hj],
    fun i => (hB.diagramWeight_matrixMutation_self k i).2.2⟩
  rcases eq_or_ne i k with rfl | hi
  · exact (hB.diagramWeight_matrixMutation_self i j).2.1
  rcases eq_or_ne j k with rfl | hj
  · exact (hB.diagramWeight_matrixMutation_self j i).1
  rw [diagramWeight, diagramWeight, hoff i j hi hj, hoff j i hj hi]

end MutationRule

/-! ### Connectedness -/

/-- **Mutation respects a splitting without adjacencies.** If `bᵢⱼ = 0` for all `i ∈ I`,
`j ∉ I`, and `k ∈ I`, then `μ_k(B)` has zero entries between `I` and its complement and the
entries of `B` inside the complement. -/
@[cluster_algebras "lem_no_edges_across"]
theorem SkewSymmetrizable.matrixMutation_eq_zero_of_split {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {I : Finset (Fin n)} (hI : ∀ i ∈ I, ∀ j ∉ I, B i j = 0)
    {k : Fin n} (hk : k ∈ I) :
    (∀ i ∈ I, ∀ j ∉ I, matrixMutation le_rfl B k i j = 0 ∧ matrixMutation le_rfl B k j i = 0) ∧
      ∀ j ∉ I, ∀ j' ∉ I, matrixMutation le_rfl B k j j' = B j j' := by
  obtain ⟨d, hd⟩ := hB
  have hI' : ∀ i ∈ I, ∀ j ∉ I, B j i = 0 := fun i hi j hj =>
    (hd.apply_eq_zero_comm i j).1 (hI i hi j hj)
  have hne : ∀ j ∉ I, j ≠ k := fun j hj h => hj (h ▸ hk)
  refine ⟨fun i hi j hj => ⟨?_, ?_⟩, fun j hj j' hj' => ?_⟩
  · rcases eq_or_ne i k with rfl | hik
    · rw [show matrixMutation le_rfl B i i j = -B i j from matrixMutation_apply_row le_rfl B i j,
        hI i hi j hj, neg_zero]
    · rw [matrixMutation_apply_of_eq_zero _ _ _ hik (hne j hj) (Or.inr (hI k hk j hj)),
        hI i hi j hj]
  · rcases eq_or_ne i k with rfl | hik
    · rw [matrixMutation_apply_of_eq _ _ _ (Or.inr rfl), hI' i hi j hj, neg_zero]
    · rw [matrixMutation_apply_of_eq_zero _ _ _ (hne j hj) hik (Or.inl (hI' k hk j hj)),
        hI' i hi j hj]
  · exact matrixMutation_apply_of_eq_zero _ _ _ (hne j hj) (hne j' hj') (Or.inl (hI' k hk j hj))

/-- **Mutation preserves connectedness**: `B` is connected exactly when `μ_k(B)` is. -/
@[cluster_algebras "lem_no_edges_across"]
theorem SkewSymmetrizable.isConnectedDiagram_matrixMutation_iff {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (k : Fin n) :
    IsConnectedDiagram (matrixMutation le_rfl B k) ↔ IsConnectedDiagram B := by
  have hB' : SkewSymmetrizable (matrixMutation le_rfl B k) :=
    skewSymmetrizable_matrixMutation hB k
  have key : ∀ C : Matrix (Fin n) (Fin n) ℤ, SkewSymmetrizable C →
      (∃ I : Finset (Fin n), I.Nonempty ∧ Iᶜ.Nonempty ∧ ∀ i ∈ I, ∀ j ∉ I, C i j = 0) →
      ∃ I : Finset (Fin n), I.Nonempty ∧ Iᶜ.Nonempty ∧
        ∀ i ∈ I, ∀ j ∉ I, matrixMutation le_rfl C k i j = 0 := by
    rintro C hC ⟨I, hI, hIc, hsep⟩
    by_cases hk : k ∈ I
    · exact ⟨I, hI, hIc, fun i hi j hj =>
        ((hC.matrixMutation_eq_zero_of_split hsep hk).1 i hi j hj).1⟩
    · obtain ⟨e, he⟩ := id hC
      have hsep' : ∀ i ∈ Iᶜ, ∀ j ∉ Iᶜ, C i j = 0 := fun i hi j hj =>
        (he.apply_eq_zero_comm j i).1
          (hsep j (by simpa using hj) i (Finset.mem_compl.1 hi))
      exact ⟨Iᶜ, hIc, by rwa [compl_compl], fun i hi j hj =>
        ((hC.matrixMutation_eq_zero_of_split hsep' (Finset.mem_compl.2 hk)).1 i hi j hj).1⟩
  rw [hB.isConnectedDiagram_iff, hB'.isConnectedDiagram_iff, not_iff_not]
  refine ⟨fun h => ?_, key B hB⟩
  simpa only [matrixMutation_matrixMutation] using key _ hB' h

/-- Mutation of a skew-symmetrizable matrix along a sequence keeps its diagram connected. -/
theorem isConnectedDiagram_matrixMutationList {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hc : IsConnectedDiagram B) (t : List (Fin n)) :
    IsConnectedDiagram (matrixMutationList le_rfl B t) := by
  induction t generalizing B with
  | nil => exact hc
  | cons k t ih =>
    exact ih (skewSymmetrizable_matrixMutation hB k)
      ((hB.isConnectedDiagram_matrixMutation_iff k).2 hc)

/-- **Connectedness of a skew-symmetrizable matrix is connectedness of its graph**: `Γ(B)` is
connected exactly when any two indices are joined by a walk in `G_B`. -/
theorem SkewSymmetrizable.isConnectedDiagram_iff_preconnected {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) : IsConnectedDiagram B ↔ (diagramGraph B).Preconnected := by
  obtain ⟨d, hd⟩ := id hB
  refine ⟨fun hc u v => ?_, fun hc P ⟨a, ha⟩ ⟨b, hb⟩ => ?_⟩
  · by_contra huv
    obtain ⟨i, hi, j, hj, hij⟩ :=
      hc {w | (diagramGraph B).Reachable u w} ⟨u, SimpleGraph.Reachable.refl u⟩ ⟨v, huv⟩
    have hne : B i j ≠ 0 := fun h0 => by
      rcases hij with h | h <;> simp [h0, (hd.apply_eq_zero_comm i j).1 h0] at h
    refine hj (SimpleGraph.Reachable.trans hi (SimpleGraph.Adj.reachable ⟨?_, ?_⟩))
    · rintro rfl
      exact hne (hB.diag_eq_zero i)
    · exact (hB.diagramWeight_pos_iff i j).2 hne
  · obtain ⟨p⟩ := hc a b
    obtain ⟨e, -, h₁, h₂⟩ := p.exists_boundary_dart P ha hb
    refine ⟨e.fst, h₁, e.snd, h₂, ?_⟩
    rcases hB.entries_sign e.fst e.snd with h | h | h
    · exact absurd h.1 ((hB.diagramWeight_pos_iff _ _).1 e.adj.2)
    · exact Or.inl (by simpa using h.1)
    · exact Or.inr (by simpa using h.2)

/-- **A connected diagram has a vertex whose removal keeps it connected.** For a connected
skew-symmetrizable `(N + 1) × (N + 1)` matrix `B`, there is `u` such that `B^ι` is connected,
`ι = u.succAbove` being the increasing enumeration of `[1, N + 1] ∖ {u}`. For `N = 0` the
reindexed `0 × 0` matrix is connected. -/
@[cluster_algebras "lem_non_cut_vertex"]
theorem IsConnectedDiagram.exists_isConnectedDiagram_submatrix_succAbove {N : ℕ}
    {B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ} (hB : SkewSymmetrizable B)
    (hc : IsConnectedDiagram B) :
    ∃ u : Fin (N + 1), IsConnectedDiagram (B.submatrix u.succAbove u.succAbove) := by
  have hG : (diagramGraph B).Connected :=
    (SimpleGraph.connected_iff _).2 ⟨hB.isConnectedDiagram_iff_preconnected.1 hc, inferInstance⟩
  obtain ⟨u, hu⟩ := hG.exists_preconnected_induce_compl_singleton_of_finite
  refine ⟨u, ?_⟩
  rw [(skewSymmetrizable_submatrix hB u.succAbove).isConnectedDiagram_iff_preconnected]
  choose f hf using fun a : ({u}ᶜ : Set (Fin (N + 1))) =>
    Fin.exists_succAbove_eq (Set.mem_compl_singleton_iff.1 a.2)
  refine hu.map ⟨f, fun {a b} hab => ?_⟩ fun p =>
    ⟨⟨u.succAbove p, Set.mem_compl_singleton_iff.2 (u.succAbove_ne p)⟩,
      Fin.succAbove_right_injective (hf _)⟩
  have hab' : (diagramGraph B).Adj a.1 b.1 := hab
  refine ⟨fun h => hab'.1 (by rw [← hf a, ← hf b, h]), ?_⟩
  change 0 < diagramWeight B (u.succAbove (f a)) (u.succAbove (f b))
  rw [hf a, hf b]
  exact hab'.2

end ClusterAlgebras

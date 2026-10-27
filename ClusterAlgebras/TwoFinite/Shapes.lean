/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.Equivalence
public import ClusterAlgebras.FiniteType.External
public import ClusterAlgebras.TypeBC.Matrices

/-!
# Recognising Dynkin shapes, and orientations of tree diagrams

Induced paths with the right weights, and trees of shapes `T_{1,1,N-3}` and `T_{1,2,N-4}`, have
Dynkin shapes; a matrix of Dynkin shape `X` is of Dynkin class `X`. All orientations of a tree
diagram are mutation equivalent, so in deciding whether a tree diagram is `2`-finite its
orientation may be chosen freely.

## Main results

* `ClusterAlgebras.hasDynkinShape_A_of_isInducedPath`, `hasDynkinShape_B_of_isInducedPath`,
  `hasDynkinShape_F₄_of_isInducedPath`, `hasDynkinShape_G₂_of_isInducedPath`: an induced path
  with the appropriate weights has Dynkin shape `A`, `B`, `F₄` or `G₂`.
* `ClusterAlgebras.hasDynkinShape_D_of_isTShape`, `hasDynkinShape_E_of_isTShape`: a tree of the
  appropriate `T`-shape has Dynkin shape `D` or `E`.
* `ClusterAlgebras.HasDynkinShape.isOfDynkinClass`: a matrix of Dynkin shape `X` is of Dynkin
  class `X`.
* `ClusterAlgebras.IsTreeDiagram.exists_matrixMutationList_arrows`: every orientation of a
  tree diagram is realised, with the same weights, by a sequence of mutations.
* `ClusterAlgebras.IsTreeDiagram.diagramEquiv_of_diagramWeight_eq`: a tree diagram and a matrix
  with the same weights up to relabelling have mutation equivalent diagrams.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n N : ℕ}

/-! ### Auxiliary facts on skew-symmetrizable matrices and Dynkin weighted graphs -/

section Aux

private theorem ne_zero_swap {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B)
    {i j : Fin n} (h : B i j ≠ 0) : B j i ≠ 0 := by
  have := hB.entries_sign i j
  omega

private theorem pos_iff_not_pos_swap {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B)
    {i j : Fin n} (h : B i j ≠ 0) : 0 < B i j ↔ ¬0 < B j i := by
  have := hB.entries_sign i j
  constructor <;> intro h' <;> omega

/-- The entries of `C(X)` for a single symbol, read through `C([X])`. -/
private theorem listCartan_singleton_castAdd (X : DynkinSymbol) (i j : Fin X.rank) :
    DynkinSymbol.listCartan [X] (Fin.castAdd (DynkinSymbol.listRank []) i)
      (Fin.castAdd (DynkinSymbol.listRank []) j) = X.cartan i j := by
  simp only [DynkinSymbol.listCartan, reindex_apply, submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁]

/-- `ω_X` for a single symbol `X`, in terms of `C(X)`. -/
private theorem dynkinWeightedGraph_singleton (X : DynkinSymbol)
    (i j : Fin (DynkinSymbol.listRank [X])) :
    dynkinWeightedGraph [X] i j = if (i : ℕ) = j then 0 else
      (X.cartan (Fin.cast (Nat.add_zero _) i) (Fin.cast (Nat.add_zero _) j) *
        X.cartan (Fin.cast (Nat.add_zero _) j) (Fin.cast (Nat.add_zero _) i)).natAbs := by
  simp only [dynkinWeightedGraph, Fin.ext_iff]
  rw [show DynkinSymbol.listCartan [X] i j = _ from listCartan_singleton_castAdd X _ _,
    show DynkinSymbol.listCartan [X] j i = _ from listCartan_singleton_castAdd X _ _]
  rfl

/-- The weight function of a path with the weight `f p` on the pair `{p, p + 1}`. -/
private def pathWeight (f : ℕ → ℕ) {M : ℕ} (i j : Fin M) : ℕ :=
  if (i : ℕ) + 1 = j then f i else if (j : ℕ) + 1 = i then f j else 0

private theorem dynkinWeightedGraph_A (N : ℕ) (hN : 1 ≤ N)
    (i j : Fin (DynkinSymbol.listRank [.A N hN])) :
    dynkinWeightedGraph [.A N hN] i j = pathWeight (fun _ => 1) i j := by
  rw [dynkinWeightedGraph_singleton, pathWeight]
  simp only [DynkinSymbol.cartan, cartanA, of_apply, Fin.ext_iff, Fin.val_cast]
  split_ifs <;> first | rfl | omega

private theorem dynkinWeightedGraph_B (N : ℕ) (hN : 2 ≤ N)
    (i j : Fin (DynkinSymbol.listRank [.B N hN])) :
    dynkinWeightedGraph [.B N hN] i j = pathWeight (fun p => if p = 0 then 2 else 1) i j := by
  rw [dynkinWeightedGraph_singleton, pathWeight]
  simp only [DynkinSymbol.cartan, cartanB, cartanA, of_apply, Fin.ext_iff, Fin.val_cast]
  split_ifs <;> first | rfl | omega

private theorem dynkinWeightedGraph_C (N : ℕ) (hN : 3 ≤ N)
    (i j : Fin (DynkinSymbol.listRank [.C N hN])) :
    dynkinWeightedGraph [.C N hN] i j = pathWeight (fun p => if p = 0 then 2 else 1) i j := by
  rw [dynkinWeightedGraph_singleton, pathWeight]
  simp only [DynkinSymbol.cartan, cartanC, cartanA, of_apply, Fin.ext_iff, Fin.val_cast]
  split_ifs <;> first | rfl | omega

private theorem dynkinWeightedGraph_F₄ (i j : Fin (DynkinSymbol.listRank [.F₄])) :
    dynkinWeightedGraph [.F₄] i j = pathWeight (fun p => if p = 1 then 2 else 1) i j := by
  rw [dynkinWeightedGraph_singleton, pathWeight]
  simp only [DynkinSymbol.cartan, cartanF₄, cartanA, of_apply, Fin.ext_iff, Fin.val_cast]
  have hi := i.isLt; have hj := j.isLt
  simp only [DynkinSymbol.listRank, DynkinSymbol.rank] at hi hj
  split_ifs <;> first | rfl | omega

private theorem dynkinWeightedGraph_G₂ (i j : Fin (DynkinSymbol.listRank [.G₂])) :
    dynkinWeightedGraph [.G₂] i j = pathWeight (fun _ => 3) i j := by
  rw [dynkinWeightedGraph_singleton, pathWeight]
  simp only [DynkinSymbol.cartan, cartanG₂, cartanA, of_apply, Fin.ext_iff, Fin.val_cast]
  have hi := i.isLt; have hj := j.isLt
  simp only [DynkinSymbol.listRank, DynkinSymbol.rank] at hi hj
  split_ifs <;> first | rfl | omega

/-- The weights of an induced path enumerating all indices. -/
private theorem diagramWeight_of_isInducedPath {B : Matrix (Fin N) (Fin N) ℤ}
    (hB : SkewSymmetrizable B) {v : Fin N → Fin N} (hv : IsInducedPath B v) (f : ℕ → ℕ)
    (hw : ∀ p q : Fin N, (p : ℕ) + 1 = q → diagramWeight B (v p) (v q) = f p) (i j : Fin N) :
    diagramWeight B (v i) (v j) = pathWeight f i j := by
  rw [pathWeight]
  split_ifs with h1 h2
  · exact hw i j h1
  · rw [diagramWeight_comm]; exact hw j i h2
  · by_cases hij : i = j
    · subst hij; exact hB.diagramWeight_self _
    · have := (hv.2.2 i j hij).not.mpr (by omega)
      rw [diagramGraph_adj, not_and, not_lt] at this
      exact Nat.le_zero.mp (this (hv.2.1.ne hij))

/-- An induced path enumerating all indices, with weights `f`, gives Dynkin shape `X` when
`ω_X` is the path with weights `f`. -/
private theorem hasDynkinShape_of_isInducedPath {B : Matrix (Fin N) (Fin N) ℤ}
    (hB : SkewSymmetrizable B) {X : DynkinSymbol} (h : DynkinSymbol.listRank [X] = N)
    {v : Fin N ≃ Fin N} (hv : IsInducedPath B v) (f : ℕ → ℕ)
    (hw : ∀ p q : Fin N, (p : ℕ) + 1 = q → diagramWeight B (v p) (v q) = f p)
    (hω : ∀ i j, dynkinWeightedGraph [X] i j = pathWeight f i j) : HasDynkinShape B [X] := by
  refine ⟨(finCongr h).trans v, skewSymmetrizable_submatrix hB _, fun i j => ?_⟩
  change diagramWeight B (v (Fin.cast h i)) (v (Fin.cast h j)) = _
  rw [diagramWeight_of_isInducedPath hB hv f hw, hω]
  simp only [pathWeight, Fin.val_cast]

/-- The identity is an induced path of a matrix whose weights are those of a path with
positive weights. -/
private theorem isInducedPath_id_of_pathWeight {M : ℕ} {C : Matrix (Fin M) (Fin M) ℤ}
    (hM : 1 ≤ M) (f : ℕ → ℕ) (hf : ∀ p, 0 < f p)
    (hC : ∀ i j, diagramWeight C i j = pathWeight f i j) : IsInducedPath C id := by
  refine ⟨hM, Function.injective_id, fun p q hpq => ?_⟩
  simp only [id, diagramGraph_adj, hC, pathWeight]
  have hpq' : (p : ℕ) ≠ q := fun h => hpq (Fin.ext h)
  split_ifs with h1 h2
  · simp [hpq, hf, h1]
  · simp [hpq, hf, h2]
  · simp only [lt_self_iff_false, and_false, false_iff]
    omega

/-- For distinct vertices, `|aᵢⱼ aⱼᵢ|` for the Cartan matrix of a simple graph `G` is `1` on
edges of `G` and `0` otherwise. -/
private theorem natAbs_cartanOfGraph_mul {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {i j : Fin n} (hij : i ≠ j) :
    (cartanOfGraph G i j * cartanOfGraph G j i).natAbs = if G.Adj i j then 1 else 0 := by
  simp only [cartanOfGraph, of_apply, hij, Ne.symm hij, if_false, G.adj_comm j i]
  split_ifs <;> rfl

/-- The position of the vertex `k` of `D_N` in the enumeration
`o, x₁, y₁, z₁, …, z_{N-3}` of `T_{1,1,N-3}`:
`o = N - 3`, `x₁ = N - 2`, `y₁ = N - 1` and `z_t = N - 3 - t`. -/
private def dPos (N k : ℕ) : ℕ :=
  if k + 3 = N then 0 else if k + 2 = N then 1 else if k + 1 = N then 2 else N - 1 - k

/-- The position of the vertex `k` of `E_N` in the enumeration
`o, x₁, y₁, y₂, z₁, …, z_{N-4}` of `T_{1,2,N-4}`:
`o = 2`, `x₁ = N - 1`, `(y₁, y₂) = (1, 0)` and `z_t = 2 + t`. -/
private def ePos (N k : ℕ) : ℕ :=
  if k = 2 then 0 else if k + 1 = N then 1 else if k = 1 then 2 else if k = 0 then 3 else k + 1

private theorem dPos_cases (N k : ℕ) :
    (k + 3 = N ∧ dPos N k = 0) ∨ (k + 2 = N ∧ dPos N k = 1) ∨
      (k + 1 = N ∧ dPos N k = 2) ∨
      (k + 3 ≠ N ∧ k + 2 ≠ N ∧ k + 1 ≠ N ∧ dPos N k = N - 1 - k) := by
  unfold dPos; split_ifs <;> omega

private theorem ePos_cases (N k : ℕ) :
    (k = 2 ∧ ePos N k = 0) ∨ (k ≠ 2 ∧ k + 1 = N ∧ ePos N k = 1) ∨
      (k = 1 ∧ k + 1 ≠ N ∧ ePos N k = 2) ∨ (k = 0 ∧ k + 1 ≠ N ∧ ePos N k = 3) ∨
      (2 < k ∧ k + 1 ≠ N ∧ ePos N k = k + 1) := by
  unfold ePos; split_ifs <;> omega

private theorem dPos_spec {N k l : ℕ} (hN : 4 ≤ N) (hk : k < N) (hl : l < N) :
    (if dPos N k < dPos N l then tShapeModel 1 1 (N - 3) (dPos N k) (dPos N l)
      else tShapeModel 1 1 (N - 3) (dPos N l) (dPos N k)) =
    if ((k + 1 = l ∧ l + 2 ≤ N) ∨ (k + 3 = N ∧ l + 1 = N)) ∨
      ((l + 1 = k ∧ k + 2 ≤ N) ∨ (l + 3 = N ∧ k + 1 = N)) then 1 else 0 := by
  have h1 := dPos_cases N k
  have h2 := dPos_cases N l
  generalize dPos N k = a at *
  generalize dPos N l = b at *
  unfold tShapeModel
  split_ifs <;> omega

private theorem ePos_spec {N k l : ℕ} (hN : 6 ≤ N) (hk : k < N) (hl : l < N) :
    (if ePos N k < ePos N l then tShapeModel 1 2 (N - 4) (ePos N k) (ePos N l)
      else tShapeModel 1 2 (N - 4) (ePos N l) (ePos N k)) =
    if ((k + 1 = l ∧ l + 2 ≤ N) ∨ (k = 2 ∧ l + 1 = N)) ∨
      ((l + 1 = k ∧ k + 2 ≤ N) ∨ (l = 2 ∧ k + 1 = N)) then 1 else 0 := by
  have h1 := ePos_cases N k
  have h2 := ePos_cases N l
  generalize ePos N k = a at *
  generalize ePos N l = b at *
  unfold tShapeModel
  split_ifs <;> omega

/-- The enumeration of the vertices of `D_N` as `o, x₁, y₁, z₁, …, z_{N-3}`. -/
private noncomputable def dPosEquiv (N : ℕ) (hN : 4 ≤ N) :
    Fin (DynkinSymbol.listRank [.D N hN]) ≃ Fin (1 + 1 + (N - 3) + 1) :=
  Equiv.ofBijective (fun k => ⟨dPos N k, by
      have := k.isLt
      simp only [DynkinSymbol.listRank, DynkinSymbol.rank] at this
      have := dPos_cases N k; omega⟩) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun k l hkl => ?_, by
      rw [Fintype.card_fin, Fintype.card_fin]
      simp only [DynkinSymbol.listRank, DynkinSymbol.rank]; omega⟩
    have hk := k.isLt; have hl := l.isLt
    simp only [DynkinSymbol.listRank, DynkinSymbol.rank] at hk hl
    have h := congrArg Fin.val hkl
    simp only at h
    have := dPos_cases N k; have := dPos_cases N l
    exact Fin.ext (by omega)

/-- The enumeration of the vertices of `E_N` as `o, x₁, y₁, y₂, z₁, …, z_{N-4}`. -/
private noncomputable def ePosEquiv (N : ℕ) (hN : 6 ≤ N ∧ N ≤ 8) :
    Fin (DynkinSymbol.listRank [.E N hN]) ≃ Fin (1 + 2 + (N - 4) + 1) :=
  Equiv.ofBijective (fun k => ⟨ePos N k, by
      have := k.isLt
      simp only [DynkinSymbol.listRank, DynkinSymbol.rank] at this
      have := ePos_cases N k; omega⟩) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun k l hkl => ?_, by
      rw [Fintype.card_fin, Fintype.card_fin]
      simp only [DynkinSymbol.listRank, DynkinSymbol.rank]; omega⟩
    have hk := k.isLt; have hl := l.isLt
    simp only [DynkinSymbol.listRank, DynkinSymbol.rank] at hk hl
    have h := congrArg Fin.val hkl
    simp only at h
    have := ePos_cases N k; have := ePos_cases N l
    exact Fin.ext (by omega)

/-- `ω_{D_N}` read through the enumeration of `T_{1,1,N-3}`. -/
private theorem dynkinWeightedGraph_D_eq (N : ℕ) (hN : 4 ≤ N)
    (i j : Fin (DynkinSymbol.listRank [.D N hN])) (hij : i ≠ j) :
    dynkinWeightedGraph [.D N hN] i j =
      orderedModel (tShapeModel 1 1 (N - 3)) (dPosEquiv N hN i) (dPosEquiv N hN j) := by
  have hi := i.isLt; have hj := j.isLt
  simp only [DynkinSymbol.listRank, DynkinSymbol.rank] at hi hj
  have hij' : Fin.cast (Nat.add_zero _) i ≠ Fin.cast (Nat.add_zero _) j :=
    fun h => hij (Fin.ext (congrArg Fin.val h))
  rw [dynkinWeightedGraph_singleton, if_neg (fun h => hij (Fin.ext h))]
  simp only [DynkinSymbol.cartan, cartanD]
  rw [natAbs_cartanOfGraph_mul (by exact hij')]
  simp only [orderedModel, dPosEquiv, Equiv.ofBijective_apply]
  rw [dPos_spec hN hi hj]
  simp only [dynkinTreeD, SimpleGraph.fromRel_adj, dynkinTreeDRel, Fin.val_cast, ne_eq]
  exact if_congr (and_iff_right hij') rfl rfl

/-- `ω_{E_N}` read through the enumeration of `T_{1,2,N-4}`. -/
private theorem dynkinWeightedGraph_E_eq (N : ℕ) (hN : 6 ≤ N ∧ N ≤ 8)
    (i j : Fin (DynkinSymbol.listRank [.E N hN])) (hij : i ≠ j) :
    dynkinWeightedGraph [.E N hN] i j =
      orderedModel (tShapeModel 1 2 (N - 4)) (ePosEquiv N hN i) (ePosEquiv N hN j) := by
  have hi := i.isLt; have hj := j.isLt
  simp only [DynkinSymbol.listRank, DynkinSymbol.rank] at hi hj
  have hij' : Fin.cast (Nat.add_zero _) i ≠ Fin.cast (Nat.add_zero _) j :=
    fun h => hij (Fin.ext (congrArg Fin.val h))
  rw [dynkinWeightedGraph_singleton, if_neg (fun h => hij (Fin.ext h))]
  simp only [DynkinSymbol.cartan, cartanE]
  rw [natAbs_cartanOfGraph_mul (by exact hij')]
  simp only [orderedModel, ePosEquiv, Equiv.ofBijective_apply]
  rw [ePos_spec hN.1 hi hj]
  simp only [dynkinGraphE, SimpleGraph.fromRel_adj, dynkinERel, Fin.val_cast, ne_eq]
  exact if_congr (and_iff_right hij') rfl rfl

/-- A matrix whose weights are those of a model `f` through an enumeration `e`, where `ω_X` has
the same model through an enumeration `τ`, has Dynkin shape `X`. -/
private theorem hasDynkinShape_of_isShapeOf {B : Matrix (Fin N) (Fin N) ℤ}
    (hB : SkewSymmetrizable B) {X : DynkinSymbol} {M : ℕ} {f : ℕ → ℕ → ℕ}
    (τ : Fin (DynkinSymbol.listRank [X]) ≃ Fin M)
    (hτ : ∀ i j, i ≠ j → dynkinWeightedGraph [X] i j = orderedModel f (τ i) (τ j))
    (h : IsShapeOf (diagramWeight B) M f) : HasDynkinShape B [X] := by
  obtain ⟨e, he⟩ := h
  refine ⟨τ.trans e, skewSymmetrizable_submatrix hB _, fun i j => ?_⟩
  change diagramWeight B (e (τ i)) (e (τ j)) = _
  by_cases hij : i = j
  · subst hij
    rw [hB.diagramWeight_self, dynkinWeightedGraph, if_pos rfl]
  · rw [he _ _ (τ.injective.ne hij), hτ i j hij]

end Aux

/-! ### Recognising Dynkin shapes -/

section Recognition

variable {B : Matrix (Fin N) (Fin N) ℤ}

/-- An induced path enumerating `[1, N]` with all weights `1` gives Dynkin shape `A_N`. -/
@[cluster_algebras "lem_dynkin_shape_recognition"]
theorem hasDynkinShape_A_of_isInducedPath (hB : SkewSymmetrizable B) (hN : 1 ≤ N)
    {v : Fin N ≃ Fin N} (hv : IsInducedPath B v)
    (hw : ∀ p q : Fin N, (p : ℕ) + 1 = q → diagramWeight B (v p) (v q) = 1) :
    HasDynkinShape B [DynkinSymbol.A N hN] :=
  hasDynkinShape_of_isInducedPath hB (Nat.add_zero N) hv (fun _ => 1) hw
    (dynkinWeightedGraph_A N hN)

/-- An induced path enumerating `[1, N]`, `N ≥ 2`, with weights `(2, 1, …, 1)` gives Dynkin
shape `B_N`. -/
@[cluster_algebras "lem_dynkin_shape_recognition"]
theorem hasDynkinShape_B_of_isInducedPath (hB : SkewSymmetrizable B) (hN : 2 ≤ N)
    {v : Fin N ≃ Fin N} (hv : IsInducedPath B v)
    (hw : ∀ p q : Fin N, (p : ℕ) + 1 = q →
      diagramWeight B (v p) (v q) = if (p : ℕ) = 0 then 2 else 1) :
    HasDynkinShape B [DynkinSymbol.B N hN] :=
  hasDynkinShape_of_isInducedPath hB (Nat.add_zero N) hv _ hw (dynkinWeightedGraph_B N hN)

/-- An induced path enumerating `[1, 4]` with weights `(1, 2, 1)` gives Dynkin shape `F₄`. -/
@[cluster_algebras "lem_dynkin_shape_recognition"]
theorem hasDynkinShape_F₄_of_isInducedPath {B : Matrix (Fin 4) (Fin 4) ℤ}
    (hB : SkewSymmetrizable B) {v : Fin 4 ≃ Fin 4} (hv : IsInducedPath B v)
    (hw : ∀ p q : Fin 4, (p : ℕ) + 1 = q →
      diagramWeight B (v p) (v q) = if (p : ℕ) = 1 then 2 else 1) :
    HasDynkinShape B [DynkinSymbol.F₄] :=
  hasDynkinShape_of_isInducedPath hB rfl hv _ hw dynkinWeightedGraph_F₄

/-- An induced path enumerating `[1, 2]` with weight `3` gives Dynkin shape `G₂`. -/
@[cluster_algebras "lem_dynkin_shape_recognition"]
theorem hasDynkinShape_G₂_of_isInducedPath {B : Matrix (Fin 2) (Fin 2) ℤ}
    (hB : SkewSymmetrizable B) {v : Fin 2 ≃ Fin 2} (hv : IsInducedPath B v)
    (hw : diagramWeight B (v 0) (v 1) = 3) : HasDynkinShape B [DynkinSymbol.G₂] := by
  refine hasDynkinShape_of_isInducedPath hB rfl hv (fun _ => 3) (fun p q hpq => ?_)
    dynkinWeightedGraph_G₂
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 1 := by omega
  exact hw

/-- A tree of shape `T_{1,1,N-3}`, `N ≥ 4`, has Dynkin shape `D_N`. -/
@[cluster_algebras "lem_dynkin_shape_recognition"]
theorem hasDynkinShape_D_of_isTShape (hB : SkewSymmetrizable B) (hN : 4 ≤ N)
    (hT : IsTShape (diagramWeight B) 1 1 (N - 3)) : HasDynkinShape B [DynkinSymbol.D N hN] :=
  hasDynkinShape_of_isShapeOf hB (dPosEquiv N hN) (dynkinWeightedGraph_D_eq N hN) hT

/-- A tree of shape `T_{1,2,N-4}`, `N ∈ {6, 7, 8}`, has Dynkin shape `E_N`. -/
@[cluster_algebras "lem_dynkin_shape_recognition"]
theorem hasDynkinShape_E_of_isTShape (hB : SkewSymmetrizable B) (hN : 6 ≤ N ∧ N ≤ 8)
    (hT : IsTShape (diagramWeight B) 1 2 (N - 4)) : HasDynkinShape B [DynkinSymbol.E N hN] :=
  hasDynkinShape_of_isShapeOf hB (ePosEquiv N hN) (dynkinWeightedGraph_E_eq N hN) hT

/-- Conversely `ω_{D_N}` is of shape `T_{1,1,N-3}` for `N ≥ 4`. -/
@[cluster_algebras "lem_dynkin_shape_recognition"]
theorem isTShape_dynkinWeightedGraph_D (hN : 4 ≤ N) :
    IsTShape (dynkinWeightedGraph [DynkinSymbol.D N hN]) 1 1 (N - 3) := by
  refine ⟨(dPosEquiv N hN).symm, fun p q hpq => ?_⟩
  rw [dynkinWeightedGraph_D_eq N hN _ _ ((dPosEquiv N hN).symm.injective.ne hpq),
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Conversely `ω_{E_N}` is of shape `T_{1,2,N-4}` for `N ∈ {6, 7, 8}`. -/
@[cluster_algebras "lem_dynkin_shape_recognition"]
theorem isTShape_dynkinWeightedGraph_E (hN : 6 ≤ N ∧ N ≤ 8) :
    IsTShape (dynkinWeightedGraph [DynkinSymbol.E N hN]) 1 2 (N - 4) := by
  refine ⟨(ePosEquiv N hN).symm, fun p q hpq => ?_⟩
  rw [dynkinWeightedGraph_E_eq N hN _ _ ((ePosEquiv N hN).symm.injective.ne hpq),
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- For `X` one of `A_N`, `B_N`, `C_N`, `F₄`, `G₂`, the identity enumeration is an induced
path of every orientation of `ω_X`. -/
@[cluster_algebras "lem_dynkin_shape_recognition"]
theorem isInducedPath_id_of_isOrientationOfWeighted {X : DynkinSymbol}
    (hX : (∃ k hk, X = DynkinSymbol.A k hk) ∨ (∃ k hk, X = DynkinSymbol.B k hk) ∨
      (∃ k hk, X = DynkinSymbol.C k hk) ∨ X = DynkinSymbol.F₄ ∨ X = DynkinSymbol.G₂)
    {C : Matrix (Fin (DynkinSymbol.listRank [X])) (Fin (DynkinSymbol.listRank [X])) ℤ}
    (hC : IsOrientationOfWeighted C (dynkinWeightedGraph [X])) : IsInducedPath C id := by
  rcases hX with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | rfl | rfl
  · exact isInducedPath_id_of_pathWeight hk _ (fun _ => one_pos)
      (fun i j => (hC.2 i j).trans (dynkinWeightedGraph_A k hk i j))
  · exact isInducedPath_id_of_pathWeight
      (by simp only [DynkinSymbol.listRank, DynkinSymbol.rank]; omega) _
      (fun _ => by split_ifs <;> norm_num)
      (fun i j => (hC.2 i j).trans (dynkinWeightedGraph_B k hk i j))
  · exact isInducedPath_id_of_pathWeight
      (by simp only [DynkinSymbol.listRank, DynkinSymbol.rank]; omega) _
      (fun _ => by split_ifs <;> norm_num)
      (fun i j => (hC.2 i j).trans (dynkinWeightedGraph_C k hk i j))
  · exact isInducedPath_id_of_pathWeight (by decide) _ (fun _ => by split_ifs <;> norm_num)
      (fun i j => (hC.2 i j).trans (dynkinWeightedGraph_F₄ i j))
  · exact isInducedPath_id_of_pathWeight (by decide) _ (fun _ => by norm_num)
      (fun i j => (hC.2 i j).trans (dynkinWeightedGraph_G₂ i j))

/-- A matrix of Dynkin shape `X` is of Dynkin class `X`. -/
@[cluster_algebras "lem_dynkin_shape_recognition"]
theorem HasDynkinShape.isOfDynkinClass {Xs : List DynkinSymbol} (h : HasDynkinShape B Xs) :
    IsOfDynkinClass B Xs :=
  ⟨B, h, [], 1, rfl⟩

end Recognition

/-! ### Orientations of a tree diagram -/

section SignPattern

variable {B : Matrix (Fin n) (Fin n) ℤ}

/-- The matrix with the entries of `B` up to sign, the entry at `(i, j)` taken nonnegative
exactly when `P i j` holds. -/
private def signedMatrix (B : Matrix (Fin n) (Fin n) ℤ) (P : Fin n → Fin n → Prop)
    [DecidableRel P] : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if P i j then |B i j| else -|B i j|

private theorem abs_signedMatrix (P : Fin n → Fin n → Prop) [DecidableRel P] (i j : Fin n) :
    |signedMatrix B P i j| = |B i j| := by
  simp only [signedMatrix, of_apply]
  split_ifs <;> simp

private theorem diagramWeight_signedMatrix (P : Fin n → Fin n → Prop) [DecidableRel P]
    (i j : Fin n) : diagramWeight (signedMatrix B P) i j = diagramWeight B i j := by
  simp only [diagramWeight, Int.natAbs_mul, ← Int.natAbs_abs (signedMatrix B P _ _),
    abs_signedMatrix, Int.natAbs_abs]

private theorem signedMatrix_pos_iff (P : Fin n → Fin n → Prop) [DecidableRel P] (i j : Fin n) :
    0 < signedMatrix B P i j ↔ P i j ∧ B i j ≠ 0 := by
  simp only [signedMatrix, of_apply]
  split_ifs with h
  · simp [h, abs_pos]
  · simp only [h, false_and, iff_false, not_lt, neg_nonpos]
    exact abs_nonneg _

/-- The Coxeter graph of the Cartan counterpart of `B` is the graph `G_B`. -/
private theorem coxeterGraph_cartanCounterpart (hB : SkewSymmetrizable B) :
    coxeterGraph (cartanCounterpart B) = diagramGraph B := by
  ext i j
  rw [coxeterGraph_adj, diagramGraph_adj, hB.diagramWeight_pos_iff]
  refine and_congr_right fun hij => ?_
  simp only [cartanCounterpart, of_apply, hij, Ne.symm hij, if_false, ne_eq, neg_eq_zero,
    abs_eq_zero]
  exact ⟨fun h => h.elim id fun h' => ne_zero_swap hB h', Or.inl⟩

/-- **Changing the signs of a tree diagram.** If `B` is a tree diagram and `P` picks exactly one
of `(i, j)` and `(j, i)` whenever `bᵢⱼ ≠ 0`, then some sequence of mutations takes `B` to the
matrix with entries `|bᵢⱼ|` where `P` holds and `-|bᵢⱼ|` elsewhere. -/
private theorem exists_matrixMutationList_eq_signedMatrix (hB : SkewSymmetrizable B)
    (hT : IsTreeDiagram B) (P : Fin n → Fin n → Prop) [DecidableRel P]
    (hP : ∀ i j, B i j ≠ 0 → (P i j ↔ ¬P j i)) :
    ∃ s : List (Fin n), matrixMutationList le_rfl B s = signedMatrix B P := by
  refine TypeBC.exists_matrixMutationList_eq_of_cartanCounterpart_eq hB ?_ ?_ ?_
  · obtain ⟨d, hd⟩ := hB
    refine ⟨d, hd.1, fun i j => ?_⟩
    simp only [Int.cast_id]
    by_cases hij : B i j = 0
    · have hji : B j i = 0 := by_contra fun h => ne_zero_swap ⟨d, hd⟩ h hij
      simp [signedMatrix, hij, hji]
    · have h : d i * B i j = -(d j * B j i) := by simpa only [Int.cast_id] using hd.2 i j
      have habs : d i * |B i j| = d j * |B j i| := by
        have := congrArg abs h
        rwa [abs_neg, abs_mul, abs_mul, abs_of_pos (hd.1 i), abs_of_pos (hd.1 j)] at this
      have hPij := hP i j hij
      simp only [signedMatrix, of_apply]
      by_cases hp : P i j
      · rw [if_pos hp, if_neg (hPij.mp hp)]; linarith
      · rw [if_neg hp, if_pos (by tauto)]; linarith
  · ext i j
    simp only [cartanCounterpart, of_apply, abs_signedMatrix]
  · rw [coxeterGraph_cartanCounterpart hB]
    exact hT

end SignPattern

/-- For every orientation `Q` of the tree `G_B` there is a sequence `t` such that `μ_t(B)` has
the weights of `B` and exactly the arrows of `Q`. -/
@[cluster_algebras "lem_tree_diagram_reorient"]
theorem IsTreeDiagram.exists_matrixMutationList_arrows {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hT : IsTreeDiagram B) {Q : ClusterAlgebras.Quiver (Fin n)}
    (hQ : Q.IsOrientation (diagramGraph B)) :
    ∃ t : List (Fin n),
      (∀ i j, diagramWeight (matrixMutationList le_rfl B t) i j = diagramWeight B i j) ∧
      ∀ i j, (0 < matrixMutationList le_rfl B t i j ↔ Q.arrows i j = 1) := by
  have hadj : ∀ i j, B i j ≠ 0 → Q.arrows i j + Q.arrows j i = 1 := fun i j h => by
    have hij : i ≠ j := fun hij => h (hij ▸ hB.diag_eq_zero i)
    exact (hQ.2 i j hij).1 ⟨hij, (hB.diagramWeight_pos_iff i j).mpr h⟩
  obtain ⟨t, ht⟩ :=
    exists_matrixMutationList_eq_signedMatrix hB hT (fun i j => Q.arrows i j = 1)
    (fun i j h => by have := hadj i j h; omega)
  refine ⟨t, fun i j => by rw [ht, diagramWeight_signedMatrix], fun i j => ?_⟩
  rw [ht, signedMatrix_pos_iff]
  refine ⟨And.left, fun h => ⟨h, fun h0 => ?_⟩⟩
  by_cases hij : i = j
  · subst hij
    have := Q.isArrowSystem i
    omega
  · have hn : ¬(diagramGraph B).Adj i j := by
      rw [diagramGraph_adj, hB.diagramWeight_pos_iff]
      exact fun h' => h'.2 h0
    have := ((hQ.2 i j hij).2 hn).1
    omega

/-- A tree diagram `B` and a matrix `B'` with `w_{B'}(i, j) = w_B(σ(i), σ(j))` for a permutation
`σ` have mutation equivalent diagrams; in particular `B` is `2`-finite exactly when `B'` is. -/
@[cluster_algebras "lem_tree_diagram_reorient"]
theorem IsTreeDiagram.diagramEquiv_of_diagramWeight_eq {B B' : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B') (hT : IsTreeDiagram B)
    {σ : Equiv.Perm (Fin n)} (hw : ∀ i j, diagramWeight B' i j = diagramWeight B (σ i) (σ j)) :
    DiagramEquiv B B' ∧ (IsTwoFinite B ↔ IsTwoFinite B') := by
  have hw' : ∀ i j, diagramWeight B i j = diagramWeight B' (σ.symm i) (σ.symm j) :=
    fun i j => by rw [hw, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  obtain ⟨s, hs⟩ := exists_matrixMutationList_eq_signedMatrix hB hT
    (fun i j => 0 < B' (σ.symm i) (σ.symm j)) (fun i j h => by
      refine pos_iff_not_pos_swap hB' ?_
      rw [← hB'.diagramWeight_pos_iff, ← hw']
      exact (hB.diagramWeight_pos_iff i j).mpr h)
  have hD : DiagramEquiv B B' := by
    refine ⟨s, σ, ?_⟩
    rw [hs, diagram_eq_iff]
    intro i j
    have hpos : 0 < signedMatrix B (fun i j => 0 < B' (σ.symm i) (σ.symm j)) (σ i) (σ j) ↔
        0 < B' i j := by
      rw [signedMatrix_pos_iff]
      simp only [Equiv.symm_apply_apply]
      refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
      rw [← hB.diagramWeight_pos_iff, ← hw, hB'.diagramWeight_pos_iff]
      exact h.ne'
    have hwt := (diagramWeight_signedMatrix (B := B)
      (fun i j => 0 < B' (σ.symm i) (σ.symm j)) (σ i) (σ j)).trans (hw i j).symm
    simp only [diagramWeight] at hwt
    have hwt' := congrArg (fun k : ℕ => ((k : ℤ) : ℝ)) hwt
    simp only [Int.natCast_natAbs, Int.cast_abs, Int.cast_mul] at hwt'
    simp only [map_apply, submatrix_apply, Int.cast_pos]
    exact ⟨hpos, fun _ => hwt'⟩
  exact ⟨hD, hD.isTwoFinite_iff hB hB'⟩

end ClusterAlgebras

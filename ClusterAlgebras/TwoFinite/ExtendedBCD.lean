/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.Cycles

/-!
# The extended Dynkin trees of types `B`, `C`, `D` are not `2`-finite

No matrix whose diagram is one of the extended Dynkin trees `B_k^{(1)}`, `C_k^{(1)}`,
`D_k^{(1)}` is `2`-finite. After reorienting the tree, one mutation either creates a weight `4`,
a non-cyclically oriented chordless cycle, or a subdiagram of the same kind with one vertex
fewer.

## Main results

* `ClusterAlgebras.not_isTwoFinite_of_isBAffineShape`: no matrix of shape `B_k^{(1)}`, `k ≥ 3`,
  is `2`-finite.
* `ClusterAlgebras.not_isTwoFinite_of_isCAffineShape`: no matrix of shape `C_k^{(1)}`, `k ≥ 2`,
  is `2`-finite.
* `ClusterAlgebras.not_isTwoFinite_of_isDAffineShape`: no matrix of shape `D_k^{(1)}`, `k ≥ 4`,
  is `2`-finite.

## Implementation notes

The induction on `k` is proved for every orientation of the tree, so the whole tree is never
reoriented. Only the arrows at the vertex `x₁` that is mutated matter, and each of its
neighbours other than `x₂` is a leaf: the arrow at a leaf is reversed, when needed, by the
mutation at that leaf, a source or a sink, which keeps all weights and all other arrows.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {N : ℕ}

/-! ### Mutation at a vertex of a tree -/

section Mutation

variable {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}

private theorem eq_zero_of_diagramWeight_eq_zero' (hC : SkewSymmetrizable C) {i j : Fin n}
    (h : diagramWeight C i j = 0) : C i j = 0 ∧ C j i = 0 := by
  have h1 : C i j = 0 := by
    by_contra h'
    have := (hC.diagramWeight_pos_iff i j).2 h'
    omega
  have := hC.entries_sign i j
  omega

private theorem ne_of_diagramWeight_pos (hC : SkewSymmetrizable C) {i j : Fin n}
    (h : 0 < diagramWeight C i j) : i ≠ j := by
  rintro rfl
  simp [hC.diagramWeight_self] at h

/-- Mutation at `c` keeps the weight of `i, j ≠ c` when one of them is not adjacent to `c`. -/
private theorem diagramWeight_matrixMutation_of_eq_zero' (hC : SkewSymmetrizable C)
    {c i j : Fin n} (hi : i ≠ c) (hj : j ≠ c)
    (h : diagramWeight C i c = 0 ∨ diagramWeight C c j = 0) :
    diagramWeight (matrixMutation le_rfl C c) i j = diagramWeight C i j := by
  have h' : (C i c = 0 ∧ C c i = 0) ∨ (C c j = 0 ∧ C j c = 0) :=
    h.imp (eq_zero_of_diagramWeight_eq_zero' hC) (eq_zero_of_diagramWeight_eq_zero' hC)
  rw [diagramWeight, diagramWeight,
    matrixMutation_apply_of_eq_zero _ _ _ hi hj (h'.imp And.left And.left),
    matrixMutation_apply_of_eq_zero _ _ _ hj hi (h'.symm.imp And.right And.right)]

/-- Mutation at `c` keeps the entry `bᵢⱼ` when `i, j` both point to `c` or both come from it. -/
private theorem matrixMutation_apply_of_sameSide' (hC : SkewSymmetrizable C) {c i j : Fin n}
    (hi : i ≠ c) (hj : j ≠ c) (h : (0 < C i c ∧ 0 < C j c) ∨ (0 < C c i ∧ 0 < C c j)) :
    matrixMutation le_rfl C c i j = C i j := by
  have h1 := hC.entries_sign i c
  have h2 := hC.entries_sign j c
  rw [matrixMutation_apply_of_ne _ _ _ hi hj, castLE_self, if_neg (by omega), if_neg (by omega)]

/-- Mutation at `c` keeps the weight of two neighbours of `c` on the same side of `c`. -/
private theorem diagramWeight_matrixMutation_of_iff_same (hC : SkewSymmetrizable C)
    {c i j : Fin n} (hi : i ≠ c) (hj : j ≠ c) (hic : 0 < diagramWeight C i c)
    (hjc : 0 < diagramWeight C j c) (h : 0 < C i c ↔ 0 < C j c) :
    diagramWeight (matrixMutation le_rfl C c) i j = diagramWeight C i j := by
  have h1 := (hC.diagramWeight_pos_iff i c).1 hic
  have h2 := (hC.diagramWeight_pos_iff j c).1 hjc
  have s1 := hC.entries_sign i c
  have s2 := hC.entries_sign j c
  have hs : (0 < C i c ∧ 0 < C j c) ∨ (0 < C c i ∧ 0 < C c j) := by
    by_cases hp : 0 < C i c
    · exact Or.inl ⟨hp, h.1 hp⟩
    · have := mt h.2 hp
      right
      omega
  rw [diagramWeight, diagramWeight, matrixMutation_apply_of_sameSide' hC hi hj hs,
    matrixMutation_apply_of_sameSide' hC hj hi (hs.imp And.symm And.symm)]

/-- Mutation at `c` along a path `i → c → j` with `bᵢⱼ = 0` creates an arrow `i → j` of weight
`w(i, c) w(c, j)`. -/
private theorem matrixMutation_of_through' (hC : SkewSymmetrizable C) {c i j : Fin n}
    (hi : i ≠ c) (hj : j ≠ c) (hij : C i j = 0) (h : 0 < C i c ∧ 0 < C c j) :
    0 < matrixMutation le_rfl C c i j ∧
      diagramWeight (matrixMutation le_rfl C c) i j =
        diagramWeight C i c * diagramWeight C c j := by
  have s := hC.entries_sign i j
  have s1 := hC.entries_sign i c
  have s2 := hC.entries_sign c j
  have hji : C j i = 0 := by omega
  have h1 : C c i < 0 := by omega
  have h2 : C j c < 0 := by omega
  have e1 : matrixMutation le_rfl C c i j = C i c * C c j := by
    rw [matrixMutation_apply_of_ne _ _ _ hi hj, castLE_self, if_pos h, hij, zero_add]
  have e2 : matrixMutation le_rfl C c j i = -(C j c * C c i) := by
    rw [matrixMutation_apply_of_ne _ _ _ hj hi, castLE_self, if_neg (by omega),
      if_pos ⟨h2, h1⟩, hji, zero_sub]
  refine ⟨e1 ▸ mul_pos h.1 h.2, ?_⟩
  rw [diagramWeight, diagramWeight, diagramWeight, e1, e2, ← Int.natAbs_mul,
    show C i c * C c j * -(C j c * C c i) = -(C i c * C c i * (C c j * C j c)) by ring,
    Int.natAbs_neg]

/-- Mutation at `c` along a path through `c` between non-adjacent `i, j` multiplies the
weights. -/
private theorem diagramWeight_matrixMutation_of_iff_through (hC : SkewSymmetrizable C)
    {c i j : Fin n} (hi : i ≠ c) (hj : j ≠ c) (hic : 0 < diagramWeight C i c)
    (hcj : 0 < diagramWeight C c j) (hij : diagramWeight C i j = 0)
    (h : 0 < C i c ↔ 0 < C c j) :
    diagramWeight (matrixMutation le_rfl C c) i j =
      diagramWeight C i c * diagramWeight C c j := by
  have h1 := (hC.diagramWeight_pos_iff i c).1 hic
  have h2 := (hC.diagramWeight_pos_iff c j).1 hcj
  have s1 := hC.entries_sign i c
  have s2 := hC.entries_sign c j
  have z := eq_zero_of_diagramWeight_eq_zero' hC hij
  by_cases hp : 0 < C i c
  · exact (matrixMutation_of_through' hC hi hj z.1 ⟨hp, h.1 hp⟩).2
  · have hq := mt h.2 hp
    rw [diagramWeight_comm (matrixMutation le_rfl C c) i j,
      (matrixMutation_of_through' hC hj hi z.2 ⟨by omega, by omega⟩).2, diagramWeight_comm C j c,
      diagramWeight_comm C c i, mul_comm]

/-- Reversing the arrow at a leaf `i` of a `2`-finite matrix, if needed, by a mutation at `i`:
the arrow between `i` and its neighbour `l` can be prescribed, keeping all weights and all
arrows away from `i`. -/
private theorem IsTwoFinite.exists_flip' (hC : IsTwoFinite C) {i l : Fin n}
    (hleaf : ∀ j, j ≠ l → diagramWeight C i j = 0) (hil : 0 < diagramWeight C i l) (q : Prop) :
    ∃ C' : Matrix (Fin n) (Fin n) ℤ, IsTwoFinite C' ∧
      (∀ a b, diagramWeight C' a b = diagramWeight C a b) ∧
      (∀ a b, a ≠ i → b ≠ i → (0 < C' a b ↔ 0 < C a b)) ∧ (0 < C' i l ↔ q) := by
  by_cases hq : 0 < C i l ↔ q
  · exact ⟨C, hC, fun _ _ => rfl, fun _ _ _ _ => Iff.rfl, hq⟩
  have hne := (hC.1.diagramWeight_pos_iff i l).1 hil
  have hs := hC.1.entries_sign i l
  have hz : ∀ j, j ≠ l → C i j = 0 := fun j hj =>
    (eq_zero_of_diagramWeight_eq_zero' hC.1 (hleaf j hj)).1
  have hsrc : IsMatrixSource C i ∨ IsMatrixSink C i := by
    by_cases hpos : 0 < C i l
    · exact Or.inl fun j => (eq_or_ne j l).elim (fun h => h ▸ hpos.le) fun h => (hz j h).ge
    · exact Or.inr fun j => (eq_or_ne j l).elim (fun h => h ▸ not_lt.1 hpos) fun h => (hz j h).le
  obtain ⟨hw, ha, hk⟩ := hC.1.matrixMutation_of_isMatrixSource_or_isMatrixSink hsrc
  refine ⟨matrixMutation le_rfl C i, hC.matrixMutationList [i], hw, ha, ?_⟩
  rw [(hk l).2, show 0 < C l i ↔ ¬0 < C i l from ⟨fun _ => by omega, fun _ => by omega⟩]
  tauto

/-- Prescribing the arrows at a list of leaves `L` attached to `x` by mutations at leaves. -/
private theorem IsTwoFinite.exists_orient' (hC : IsTwoFinite C) (x : Fin n) (σ : Fin n → Prop)
    (L : List (Fin n))
    (hL : ∀ ℓ ∈ L, 0 < diagramWeight C ℓ x ∧ ∀ j, j ≠ x → diagramWeight C ℓ j = 0) :
    ∃ C' : Matrix (Fin n) (Fin n) ℤ, IsTwoFinite C' ∧
      (∀ a b, diagramWeight C' a b = diagramWeight C a b) ∧
      (∀ a b, a ∉ L → b ∉ L → (0 < C' a b ↔ 0 < C a b)) ∧ ∀ ℓ ∈ L, (0 < C' ℓ x ↔ σ ℓ) := by
  induction L with
  | nil => exact ⟨C, hC, fun _ _ => rfl, fun _ _ _ _ => Iff.rfl, by simp⟩
  | cons ℓ L ih =>
    obtain ⟨C₁, hC₁, hw₁, ha₁, ho₁⟩ := ih fun ℓ' h => hL ℓ' (List.mem_cons_of_mem _ h)
    obtain ⟨hℓx, hℓ⟩ := hL ℓ (by simp)
    obtain ⟨C₂, hC₂, hw₂, ha₂, ho₂⟩ := hC₁.exists_flip' (i := ℓ) (l := x)
      (fun j hj => (hw₁ ℓ j).trans (hℓ j hj)) (by rwa [hw₁]) (σ ℓ)
    refine ⟨C₂, hC₂, fun a b => by rw [hw₂, hw₁], fun a b ha hb => ?_, fun ℓ' hℓ' => ?_⟩
    · simp only [List.mem_cons, not_or] at ha hb
      rw [ha₂ a b ha.1 hb.1, ha₁ a b ha.2 hb.2]
    · rcases eq_or_ne ℓ' ℓ with rfl | hne
      · exact ho₂
      · rw [ha₂ ℓ' x hne (ne_of_diagramWeight_pos hC.1 hℓx).symm]
        exact ho₁ ℓ' ((List.mem_cons.1 hℓ').resolve_left hne)

/-- **The fork mutation.** Let `L` be leaves attached to `x`, and `y ∉ L` another neighbour of
`x`. After reorienting the leaves, a mutation at `x` joins every leaf `ℓ` to `y` with weight
`w(ℓ, x) w(x, y)`, keeps the leaves pairwise non-adjacent, and keeps every weight of two indices
`i, j ≠ x` one of which is not adjacent to `x`. -/
private theorem IsTwoFinite.exists_fork (hC : IsTwoFinite C) (x y : Fin n) (L : List (Fin n))
    (hL : ∀ ℓ ∈ L, 0 < diagramWeight C ℓ x ∧ ∀ j, j ≠ x → diagramWeight C ℓ j = 0)
    (hxy : 0 < diagramWeight C x y) (hyL : y ∉ L) :
    ∃ C' : Matrix (Fin n) (Fin n) ℤ, IsTwoFinite C' ∧
      (∀ ℓ ∈ L, diagramWeight C' ℓ y = diagramWeight C ℓ x * diagramWeight C x y) ∧
      (∀ ℓ ∈ L, ∀ ℓ' ∈ L, diagramWeight C' ℓ ℓ' = 0) ∧
      ∀ i j, i ≠ x → j ≠ x → (diagramWeight C i x = 0 ∨ diagramWeight C x j = 0) →
        diagramWeight C' i j = diagramWeight C i j := by
  obtain ⟨C₁, hC₁, hw₁, ha₁, ho₁⟩ := hC.exists_orient' x (fun _ => 0 < C x y) L hL
  have hyx : y ≠ x := (ne_of_diagramWeight_pos hC.1 hxy).symm
  have hℓx : ∀ ℓ ∈ L, ℓ ≠ x := fun ℓ h => ne_of_diagramWeight_pos hC.1 (hL ℓ h).1
  have hxL : x ∉ L := fun h => hℓx x h rfl
  refine ⟨matrixMutation le_rfl C₁ x, hC₁.matrixMutationList [x], fun ℓ hℓ => ?_,
    fun ℓ hℓ ℓ' hℓ' => ?_, fun i j hi hj h => ?_⟩
  · rw [diagramWeight_matrixMutation_of_iff_through hC₁.1 (hℓx ℓ hℓ) hyx
      ((hw₁ ℓ x).trans_gt (hL ℓ hℓ).1) (by rwa [hw₁])
      ((hw₁ ℓ y).trans ((hL ℓ hℓ).2 y hyx)) ((ho₁ ℓ hℓ).trans (ha₁ x y hxL hyL).symm), hw₁,
      hw₁]
  · rw [diagramWeight_matrixMutation_of_iff_same hC₁.1 (hℓx ℓ hℓ) (hℓx ℓ' hℓ')
      ((hw₁ ℓ x).trans_gt (hL ℓ hℓ).1) ((hw₁ ℓ' x).trans_gt (hL ℓ' hℓ').1)
      ((ho₁ ℓ hℓ).trans (ho₁ ℓ' hℓ').symm), hw₁]
    exact (hL ℓ hℓ).2 ℓ' (hℓx ℓ' hℓ')
  · rw [diagramWeight_matrixMutation_of_eq_zero' hC₁.1 hi hj (by rwa [hw₁, hw₁]), hw₁]

end Mutation

/-! ### Shapes on positions -/

section Positions

variable {n : ℕ}

/-- The symmetric weight function on positions of a model `f`, read for `p < q`. -/
private def symModel (f : ℕ → ℕ → ℕ) (i j : ℕ) : ℕ :=
  if i < j then f i j else if j < i then f j i else 0

private theorem diagramWeight_eq_symModel {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : SkewSymmetrizable C) {f : ℕ → ℕ → ℕ}
    (hw : ∀ p q : Fin n, p ≠ q → diagramWeight C p q = orderedModel f p q) (p q : Fin n) :
    diagramWeight C p q = symModel f p q := by
  rcases eq_or_ne p q with rfl | hpq
  · rw [hC.diagramWeight_self]
    simp [symModel]
  · have : (p : ℕ) ≠ q := fun h => hpq (Fin.ext h)
    rw [hw p q hpq, orderedModel, symModel]
    split_ifs <;> first | rfl | omega

/-- Weights read for `p < q` only determine all weights through `orderedModel`. -/
private theorem diagramWeight_eq_orderedModel_of_lt {m : ℕ} {C : Matrix (Fin m) (Fin m) ℤ}
    {g : ℕ → ℕ → ℕ} (h : ∀ p q : Fin m, (p : ℕ) < q → diagramWeight C p q = g p q)
    (p q : Fin m) (hpq : p ≠ q) : diagramWeight C p q = orderedModel g p q := by
  rcases lt_or_gt_of_ne (fun h => hpq (Fin.ext h)) with h' | h'
  · rw [orderedModel, if_pos h', h p q h']
  · rw [orderedModel, if_neg (by omega), diagramWeight_comm, h q p h']

/-- The increasing enumeration of `[0, m] ∖ {c}`. -/
private def skipEmb (m c : ℕ) : Fin m ↪ Fin (m + 1) where
  toFun p := ⟨if (p : ℕ) < c then p else p + 1, by
    have := p.isLt
    split_ifs <;> omega⟩
  inj' p q h := by
    simp only [Fin.mk.injEq] at h
    apply Fin.ext
    split_ifs at h <;> omega

private theorem skipEmb_val (m c : ℕ) (p : Fin m) :
    ((p : ℕ) < c ∧ (skipEmb m c p : ℕ) = p) ∨ (c ≤ p ∧ (skipEmb m c p : ℕ) = p + 1) := by
  simp only [skipEmb, Function.Embedding.coeFn_mk]
  split_ifs <;> omega

private theorem skipEmb_ne (m c : ℕ) (p : Fin m) (h : c < m + 1) :
    skipEmb m c p ≠ ⟨c, h⟩ := fun e => by
  have := skipEmb_val m c p
  rw [e] at this
  simp only at this
  omega

/-- The fork mutation at the centre `c`, whose leaves are the positions `p < c` and whose other
neighbour is `c + 1`, followed by passing to the subdiagram on all indices but `c`. The weights of
the result are read off the model `f` of `C`: they form the model `g`. -/
private theorem IsTwoFinite.exists_skip {m : ℕ} {C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ}
    (hC : IsTwoFinite C) {f g : ℕ → ℕ → ℕ}
    (hF : ∀ i j : Fin (m + 1), diagramWeight C i j = symModel f i j) (c : ℕ) (hc : c + 1 < m + 1)
    (H1 : ∀ p < c, 0 < f p c ∧ ∀ j, j ≠ c → symModel f p j = 0)
    (H2 : 0 < f c (c + 1)) (H3 : ∀ p < c, g p c = f p c * f c (c + 1))
    (H4 : ∀ p q, p < q → q < c → g p q = 0) (H5 : ∀ p q, p < c → c + 1 ≤ q → g p q = 0)
    (H6 : ∀ q, c + 2 ≤ q → f c q = 0) (H7 : ∀ p q, c ≤ p → p < q → f (p + 1) (q + 1) = g p q) :
    ∃ C' : Matrix (Fin m) (Fin m) ℤ, IsTwoFinite C' ∧
      ∀ p q : Fin m, p ≠ q → diagramWeight C' p q = orderedModel g p q := by
  have hmem : ∀ i : Fin (m + 1),
      i ∈ (List.finRange (m + 1)).filter (fun i : Fin (m + 1) => decide ((i : ℕ) < c)) ↔
        (i : ℕ) < c := fun i => by
    simp
  have hsym : ∀ i j, i < j → symModel f i j = f i j := fun i j h => if_pos h
  obtain ⟨C', hC', h1, h2, h3⟩ := hC.exists_fork ⟨c, by omega⟩ ⟨c + 1, hc⟩
    ((List.finRange (m + 1)).filter (fun i : Fin (m + 1) => decide ((i : ℕ) < c)))
    (fun ℓ hℓ => by
      rw [hmem] at hℓ
      refine ⟨by rw [hF, Fin.val_mk, hsym _ _ hℓ]; exact (H1 ℓ hℓ).1, fun j hj => ?_⟩
      rw [hF]
      exact (H1 ℓ hℓ).2 j (fun h => hj (Fin.ext h)))
    (by rwa [hF, Fin.val_mk, Fin.val_mk, hsym c (c + 1) (by omega)])
    (by rw [hmem]; simp)
  refine ⟨C'.submatrix (skipEmb m c) (skipEmb m c), hC'.submatrix _, ?_⟩
  have hne : ∀ p, skipEmb m c p ≠ ⟨c, by omega⟩ := fun p => skipEmb_ne m c p _
  have hc0 : ∀ q : Fin m, c < (q : ℕ) →
      diagramWeight C ⟨c, by omega⟩ (skipEmb m c q) = 0 := fun q hq => by
    have := skipEmb_val m c q
    have hq' : (skipEmb m c q : ℕ) = (q : ℕ) + 1 := by omega
    rw [hF, Fin.val_mk, hsym c (skipEmb m c q : ℕ) (by omega), hq']
    exact H6 ((q : ℕ) + 1) (by omega)
  have key : ∀ p q : Fin m, (p : ℕ) < q →
      diagramWeight C' (skipEmb m c p) (skipEmb m c q) = g p q := by
    intro p q hpq
    have hp := skipEmb_val m c p
    have hq := skipEmb_val m c q
    by_cases hP : (p : ℕ) < c
    · have hp' : (skipEmb m c p : ℕ) = p := by omega
      have hpL := (hmem (skipEmb m c p)).2 (by omega)
      rcases lt_trichotomy (q : ℕ) c with hQ | hQ | hQ
      · rw [h2 _ hpL _ ((hmem _).2 (by omega)), H4 _ _ hpq hQ]
      · have hy : skipEmb m c q = ⟨c + 1, hc⟩ := Fin.ext (by
          change (skipEmb m c q : ℕ) = c + 1
          omega)
        rw [hy, h1 _ hpL, hF, hF, Fin.val_mk, Fin.val_mk, hp', hsym _ _ hP,
          hsym c (c + 1) (by omega), hQ, H3 _ hP]
      · rw [h3 _ _ (hne p) (hne q) (Or.inr (hc0 q hQ)), hF,
          (H1 (skipEmb m c p : ℕ) (by omega)).2 (skipEmb m c q : ℕ) (by omega),
          H5 _ _ hP (by omega)]
    · rw [h3 _ _ (hne p) (hne q) (Or.inr (hc0 q (by omega))), hF,
        hsym (skipEmb m c p : ℕ) (skipEmb m c q : ℕ) (by omega),
        show (skipEmb m c p : ℕ) = p + 1 by omega, show (skipEmb m c q : ℕ) = q + 1 by omega,
        H7 _ _ (by omega) hpq]
  exact diagramWeight_eq_orderedModel_of_lt (C := C'.submatrix (skipEmb m c) (skipEmb m c)) key

end Positions

/-! ### The induction on `k` -/

/-- `C_k^{(1)}`, `k ≥ 2`, on the indices themselves, for every orientation. -/
private theorem not_isTwoFinite_cAffine_core (k : ℕ) :
    ∀ C : Matrix (Fin (k + 3)) (Fin (k + 3)) ℤ,
      (∀ p q : Fin (k + 3), p ≠ q →
        diagramWeight C p q = orderedModel (cAffineModel (k + 2)) p q) →
      ¬IsTwoFinite C := by
  induction k with
  | zero =>
    intro C hw hC
    have hF := diagramWeight_eq_symModel hC.1 hw
    obtain ⟨C', hC', h1, -, -⟩ := hC.exists_fork 1 2 [0]
      (by simp only [hF]; decide) (by rw [hF]; decide) (by decide)
    have := hC'.diagramWeight_le_three 0 2
    rw [h1 0 (by simp), hF, hF] at this
    exact absurd this (by decide)
  | succ k ih =>
    intro C hw hC
    have hF := diagramWeight_eq_symModel hC.1 hw
    obtain ⟨C', hC', hw'⟩ := hC.exists_skip (m := k + 3) (g := cAffineModel (k + 2)) hF 1 (by omega)
      (fun p hp => by
        obtain rfl : p = 0 := by omega
        refine ⟨by simp [cAffineModel], fun j hj => ?_⟩
        unfold symModel cAffineModel
        split_ifs <;> omega)
      (by simp [cAffineModel])
      (fun p hp => by
        obtain rfl : p = 0 := by omega
        simp [cAffineModel])
      (fun p q h1 h2 => by omega)
      (fun p q h1 h2 => by
        unfold cAffineModel
        split_ifs <;> omega)
      (fun q h => by
        unfold cAffineModel
        split_ifs <;> omega)
      (fun p q h1 h2 => by
        unfold cAffineModel
        split_ifs <;> (try simp only [false_or] at *) <;> omega)
    exact ih C' hw' hC'

/-- `B_k^{(1)}`, `k ≥ 3`, on the indices themselves, for every orientation. -/
private theorem not_isTwoFinite_bAffine_core (k : ℕ) :
    ∀ C : Matrix (Fin (k + 4)) (Fin (k + 4)) ℤ,
      (∀ p q : Fin (k + 4), p ≠ q →
        diagramWeight C p q = orderedModel (bAffineModel (k + 3)) p q) →
      ¬IsTwoFinite C := by
  induction k with
  | zero =>
    intro C hw hC
    have hF := diagramWeight_eq_symModel hC.1 hw
    obtain ⟨C', hC', h1, h2, -⟩ := hC.exists_fork 2 3 [0, 1]
      (by simp only [hF]; decide) (by rw [hF]; decide) (by decide)
    have e03 : diagramWeight C' 0 3 = 2 := by rw [h1 0 (by simp), hF, hF]; decide
    have e13 : diagramWeight C' 1 3 = 2 := by rw [h1 1 (by simp), hF, hF]; decide
    have e01 : diagramWeight C' 0 1 = 0 := h2 0 (by simp) 1 (by simp)
    have e30 : diagramWeight C' 3 0 = 2 := by rw [diagramWeight_comm, e03]
    have e31 : diagramWeight C' 3 1 = 2 := by rw [diagramWeight_comm, e13]
    have e10 : diagramWeight C' 1 0 = 0 := by rw [diagramWeight_comm, e01]
    let r : Fin 3 ↪ Fin 4 := ⟨![0, 3, 1], by decide⟩
    refine not_isTwoFinite_cAffine_core 0 (C'.submatrix r r) (fun p q hpq => ?_)
      (hC'.submatrix r)
    change diagramWeight C' (r p) (r q) = _
    fin_cases p <;> fin_cases q
    all_goals first
      | exact absurd rfl hpq
      | simp [r, orderedModel, cAffineModel, e03, e13, e01, e30, e31, e10]
  | succ k ih =>
    intro C hw hC
    have hF := diagramWeight_eq_symModel hC.1 hw
    obtain ⟨C', hC', hw'⟩ := hC.exists_skip (m := k + 4) (g := bAffineModel (k + 3)) hF 2
      (by omega)
      (fun p hp => ⟨by unfold bAffineModel; split_ifs <;> omega,
        fun j hj => by unfold symModel bAffineModel; split_ifs <;> omega⟩)
      (by unfold bAffineModel; split_ifs <;> omega)
      (fun p hp => by unfold bAffineModel; split_ifs <;> omega)
      (fun p q h1 h2 => by unfold bAffineModel; split_ifs <;> omega)
      (fun p q h1 h2 => by unfold bAffineModel; split_ifs <;> omega)
      (fun q h => by unfold bAffineModel; split_ifs <;> omega)
      (fun p q h1 h2 => by unfold bAffineModel; split_ifs <;> omega)
    exact ih C' hw' hC'

/-- `D₄^{(1)}` with centre `2`, the leaves `0, 1` pointing to the centre and the leaves `3, 4`
pointing away from it, is not `2`-finite: the mutation at `2` creates a chordless `4`-cycle
`(0, 3, 1, 4)` which is not cyclically oriented. -/
private theorem not_isTwoFinite_matrixMutation_dAffine_four {C₁ : Matrix (Fin 5) (Fin 5) ℤ}
    (hS : SkewSymmetrizable C₁) (hW : ∀ i j, diagramWeight C₁ i j = symModel (dAffineModel 4) i j)
    (p02 : 0 < C₁ 0 2) (p12 : 0 < C₁ 1 2) (p23 : 0 < C₁ 2 3) (p24 : 0 < C₁ 2 4)
    (n32 : ¬0 < C₁ 3 2) (n42 : ¬0 < C₁ 4 2) : ¬IsTwoFinite (matrixMutation le_rfl C₁ 2) := by
  intro hC₂
  have z : ∀ i j : Fin 5, symModel (dAffineModel 4) i j = 0 → C₁ i j = 0 := fun i j h =>
    (eq_zero_of_diagramWeight_eq_zero' hS (by rw [hW]; exact h)).1
  obtain ⟨a03, w03⟩ := matrixMutation_of_through' hS (by decide) (by decide)
    (z 0 3 (by decide)) ⟨p02, p23⟩
  obtain ⟨a04, w04⟩ := matrixMutation_of_through' hS (by decide) (by decide)
    (z 0 4 (by decide)) ⟨p02, p24⟩
  obtain ⟨a13, w13⟩ := matrixMutation_of_through' hS (by decide) (by decide)
    (z 1 3 (by decide)) ⟨p12, p23⟩
  obtain ⟨a14, w14⟩ := matrixMutation_of_through' hS (by decide) (by decide)
    (z 1 4 (by decide)) ⟨p12, p24⟩
  have w01 := diagramWeight_matrixMutation_of_iff_same hS (c := 2) (i := 0) (j := 1)
    (by decide) (by decide) (by rw [hW]; decide) (by rw [hW]; decide) (iff_of_true p02 p12)
  have w34 := diagramWeight_matrixMutation_of_iff_same hS (c := 2) (i := 3) (j := 4)
    (by decide) (by decide) (by rw [hW]; decide) (by rw [hW]; decide) (iff_of_false n32 n42)
  rw [hW, hW] at w03 w04 w13 w14
  rw [hW] at w01 w34
  set C₂ := matrixMutation le_rfl C₁ 2
  have hcyc : IsChordlessCycle C₂ (![0, 3, 1, 4] : Fin 4 → Fin 5) := by
    refine ⟨by omega, by decide, fun p q hpq => ?_⟩
    rw [diagramGraph_adj]
    fin_cases p <;> fin_cases q
    all_goals first
      | exact absurd rfl hpq
      | simp [w03, w04, w13, w14, w01, w34, diagramWeight_comm C₂ 3, diagramWeight_comm C₂ 4,
          diagramWeight_comm C₂ 1 0, symModel, dAffineModel]
  obtain ⟨hor, -⟩ := hC₂.isCyclicallyOriented_of_isChordlessCycle hcyc
  have s13 := hC₂.1.entries_sign 1 3
  have s03 := hC₂.1.entries_sign 0 3
  rcases hor with h | h
  · have h1 := h 1
    simp only [Fin.isValue, cons_val_one, cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd,
      finRotate_apply, Fin.reduceAdd, cons_val] at h1
    omega
  · have h0 := h 0
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, finRotate_apply, zero_add,
      cons_val_one, cons_val_zero] at h0
    omega

/-- `D₄^{(1)}` on the indices themselves, for every orientation: after orienting the four leaves
towards and away from the centre `2`, the mutation at `2` creates a chordless `4`-cycle which is
not cyclically oriented. -/
private theorem not_isTwoFinite_dAffine_four (C : Matrix (Fin 5) (Fin 5) ℤ)
    (hw : ∀ p q : Fin 5, p ≠ q → diagramWeight C p q = orderedModel (dAffineModel 4) p q) :
    ¬IsTwoFinite C := by
  intro hC
  have hF := diagramWeight_eq_symModel hC.1 hw
  obtain ⟨C₁, hC₁, hw₁, -, ho₁⟩ := hC.exists_orient' 2 (fun ℓ => ℓ = 0 ∨ ℓ = 1) [0, 1, 3, 4]
    (by simp only [hF]; decide)
  have hW : ∀ i j, diagramWeight C₁ i j = symModel (dAffineModel 4) i j := fun i j =>
    (hw₁ i j).trans (hF i j)
  have hS := hC₁.1
  have n32 : ¬0 < C₁ 3 2 := fun h => absurd ((ho₁ 3 (by simp)).1 h) (by decide)
  have n42 : ¬0 < C₁ 4 2 := fun h => absurd ((ho₁ 4 (by simp)).1 h) (by decide)
  have p23 : 0 < C₁ 2 3 := by
    have hne := (hS.diagramWeight_pos_iff 3 2).1 (by rw [hW]; decide)
    have := hS.entries_sign 3 2
    omega
  have p24 : 0 < C₁ 2 4 := by
    have hne := (hS.diagramWeight_pos_iff 4 2).1 (by rw [hW]; decide)
    have := hS.entries_sign 4 2
    omega
  exact not_isTwoFinite_matrixMutation_dAffine_four hS hW ((ho₁ 0 (by simp)).2 (Or.inl rfl))
    ((ho₁ 1 (by simp)).2 (Or.inr rfl)) p23 p24 n32 n42 (hC₁.matrixMutationList [2])

/-- `D_k^{(1)}`, `k ≥ 4`, on the indices themselves, for every orientation. -/
private theorem not_isTwoFinite_dAffine_core (k : ℕ) :
    ∀ C : Matrix (Fin (k + 5)) (Fin (k + 5)) ℤ,
      (∀ p q : Fin (k + 5), p ≠ q →
        diagramWeight C p q = orderedModel (dAffineModel (k + 4)) p q) →
      ¬IsTwoFinite C := by
  induction k with
  | zero => exact not_isTwoFinite_dAffine_four
  | succ k ih =>
    intro C hw hC
    have hF := diagramWeight_eq_symModel hC.1 hw
    obtain ⟨C', hC', hw'⟩ := hC.exists_skip (m := k + 5) (g := dAffineModel (k + 4)) hF 2
      (by omega)
      (fun p hp => ⟨by unfold dAffineModel; split_ifs <;> omega,
        fun j hj => by unfold symModel dAffineModel; split_ifs <;> omega⟩)
      (by unfold dAffineModel; split_ifs <;> omega)
      (fun p hp => by unfold dAffineModel; split_ifs <;> omega)
      (fun p q h1 h2 => by unfold dAffineModel; split_ifs <;> omega)
      (fun p q h1 h2 => by unfold dAffineModel; split_ifs <;> omega)
      (fun q h => by unfold dAffineModel; split_ifs <;> omega)
      (fun p q h1 h2 => by unfold dAffineModel; split_ifs <;> omega)
    exact ih C' hw' hC'

/-! ### The three shapes -/

/-- **No matrix of shape `B_k^{(1)}`, `k ≥ 3`, is `2`-finite.** -/
@[cluster_algebras "lem_extended_BCD"]
theorem not_isTwoFinite_of_isBAffineShape {B : Matrix (Fin N) (Fin N) ℤ} {k : ℕ}
    (hS : IsBAffineShape (diagramWeight B) k) : ¬IsTwoFinite B := by
  obtain ⟨hk, e, he⟩ := hS
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  exact fun hB => not_isTwoFinite_bAffine_core k (B.submatrix e e) he
    (hB.submatrix e.toEmbedding)

/-- **No matrix of shape `C_k^{(1)}`, `k ≥ 2`, is `2`-finite.** -/
@[cluster_algebras "lem_extended_BCD"]
theorem not_isTwoFinite_of_isCAffineShape {B : Matrix (Fin N) (Fin N) ℤ} {k : ℕ}
    (hS : IsCAffineShape (diagramWeight B) k) : ¬IsTwoFinite B := by
  obtain ⟨hk, e, he⟩ := hS
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  exact fun hB => not_isTwoFinite_cAffine_core k (B.submatrix e e) he
    (hB.submatrix e.toEmbedding)

/-- **No matrix of shape `D_k^{(1)}`, `k ≥ 4`, is `2`-finite.** -/
@[cluster_algebras "lem_extended_BCD"]
theorem not_isTwoFinite_of_isDAffineShape {B : Matrix (Fin N) (Fin N) ℤ} {k : ℕ}
    (hS : IsDAffineShape (diagramWeight B) k) : ¬IsTwoFinite B := by
  obtain ⟨hk, e, he⟩ := hS
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 4 := ⟨k - 4, by omega⟩
  exact fun hB => not_isTwoFinite_dAffine_core k (B.submatrix e e) he
    (hB.submatrix e.toEmbedding)

end ClusterAlgebras

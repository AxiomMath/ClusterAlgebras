/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.Trees

/-!
# Adding a vertex to a Dynkin diagram: three local configurations

Three local configurations that arise when a vertex is added to a diagram of Dynkin class: a
vertex attached to an oriented unit cycle, a doubled triangle sliding along a linearly oriented
path, and a square of type `F₄` with a pendant vertex.

## Main results

* `ClusterAlgebras.IsOrientedUnitCycle.exists_adj_eq_of_isTwoFinite`: in a `2`-finite matrix, a
  vertex off an oriented unit cycle of length at least `4` adjacent to two cycle vertices is
  adjacent to exactly two consecutive ones, with weights `1`, and mutation at it inserts it into
  the cycle.
* `ClusterAlgebras.isLinearlyOrientedPath_matrixMutationList_of_doubledTriangle`: a linearly
  oriented path with a doubled triangle attached mutates to a linearly oriented path with
  weights `(1, …, 1, 2)`.
* `ClusterAlgebras.not_isTwoFinite_of_square_of_existsUnique_adj`: a chordless square of type
  `F₄` with a vertex adjacent to exactly one of its vertices is not `2`-finite.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

/-! ### Skew-symmetrizations of integer matrices -/

/-- `S(μ_t(B)) = μ_t(S(B))`. -/
private theorem skewSymmetrization_map_matrixMutationList {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (t : List (Fin n)) :
    skewSymmetrization ((matrixMutationList le_rfl B t).map (Int.cast : ℤ → ℝ)) =
      matrixMutationList le_rfl (skewSymmetrization (B.map (Int.cast : ℤ → ℝ))) t := by
  induction t generalizing B with
  | nil => rfl
  | cons k t ih =>
    rw [matrixMutationList_cons, matrixMutationList_cons,
      ih (skewSymmetrizable_matrixMutation hB k), matrixMutation_map_intCast,
      SkewSymmetrizable.skewSymmetrization_matrixMutation (skewSymmetrizable_map_intCast hB)
        le_rfl k]

/-- If `y → x`, then `s_{xy} = -√(w_B(x, y))`. -/
private theorem SkewSymmetrizable.skewSymmetrization_eq_neg_sqrt {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {x y : Fin n} (h : 0 < B y x) :
    skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) x y = -√(diagramWeight B x y : ℝ) := by
  have h' : B x y < 0 := by
    have := hB.entries_sign x y
    omega
  rw [(hB.skewSymmetrization_apply x y).1, Real.sign_of_neg (by exact_mod_cast h'), neg_one_mul]

/-- If `b_{xy} = 0`, then `s_{xy} = 0`. -/
private theorem SkewSymmetrizable.skewSymmetrization_eq_zero {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {x y : Fin n} (h : B x y = 0) :
    skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) x y = 0 := by
  rw [(hB.skewSymmetrization_apply x y).1, h]
  simp

/-- The weight and the arrow at `x, y` are read off `s_{xy}`. -/
private theorem SkewSymmetrizable.diagramWeight_of_skewSymmetrization_eq
    {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B) {x y : Fin n} {c : ℝ}
    (h : skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) x y = c) :
    (diagramWeight B x y : ℝ) = c ^ 2 ∧ (0 < B x y ↔ 0 < c) := by
  obtain ⟨-, h2, h3⟩ := hB.skewSymmetrization_apply x y
  rw [h] at h2 h3
  exact ⟨h2.symm, h3.symm⟩

/-- Non-adjacent indices have `b_{xy} = 0`. -/
private theorem SkewSymmetrizable.apply_eq_zero_of_not_adj {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {x y : Fin n} (h : ¬(diagramGraph B).Adj x y) : B x y = 0 := by
  rcases eq_or_ne x y with rfl | hxy
  · exact hB.diag_eq_zero x
  · by_contra h'
    exact h ⟨hxy, (hB.diagramWeight_pos_iff x y).2 h'⟩

/-- Two indices never carry arrows both ways. -/
private theorem SkewSymmetrizable.not_pos_of_pos {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {a b : Fin n} (h : 0 < B a b) : ¬0 < B b a :=
  fun h' => (hB.pos_xor_pos h.ne').elim (fun k => k.2 h') (fun k => k.2 h)

/-- Off the vertex `k` and away from the paths `x → k → y`, mutation at `k` changes neither the
weight nor the arrow. -/
private theorem SkewSymmetrizable.matrixMutation_pair_of_not {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {k x y : Fin n} (hx : x ≠ k) (hy : y ≠ k)
    (h₁ : ¬(0 < B x k ∧ 0 < B k y)) (h₂ : ¬(0 < B y k ∧ 0 < B k x)) :
    diagramWeight (matrixMutation le_rfl B k) x y = diagramWeight B x y ∧
      (0 < matrixMutation le_rfl B k x y ↔ 0 < B x y) := by
  have hS := hB.skewSymmetrization_matrixMutation_of_not hx hy h₁ h₂
  obtain ⟨-, a1, a2⟩ := (skewSymmetrizable_matrixMutation hB k).skewSymmetrization_apply x y
  obtain ⟨-, b1, b2⟩ := hB.skewSymmetrization_apply x y
  rw [hS] at a1 a2
  exact ⟨by exact_mod_cast a1.symm.trans b1, a2.symm.trans b2⟩

/-! ### Arcs of a cycle -/

/-- The successor map of `Fin L` is `i ↦ (i + 1) % L`. -/
theorem val_finRotate_eq_mod {L : ℕ} (i : Fin L) : (finRotate L i : ℕ) = (i + 1) % L := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by have := i.pos; omega⟩
  rw [coe_finRotate]
  split_ifs with h
  · subst h
    simp
  · rw [Nat.mod_eq_of_lt]
    have := Fin.val_lt_last h
    omega

/-- The successor map of `Fin N`, without `%`. -/
theorem val_finRotate_eq_ite {N : ℕ} (x : Fin N) :
    (finRotate N x : ℕ) = if (x : ℕ) + 1 = N then 0 else (x : ℕ) + 1 := by
  rw [val_finRotate_eq_mod]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The index `q + k` of a cycle of length `L`, read modulo `L`. -/
private def arcIdx {L : ℕ} (hL : 0 < L) (q : Fin L) (k : ℕ) : Fin L :=
  ⟨(q + k) % L, Nat.mod_lt _ hL⟩

/-- The successor of `q + k` is `q + (k + 1)`. -/
private theorem finRotate_arcIdx {L : ℕ} (hL : 0 < L) (q : Fin L) (k : ℕ) :
    finRotate L (arcIdx hL q k) = arcIdx hL q (k + 1) :=
  Fin.ext (by rw [val_finRotate_eq_mod]; simp only [arcIdx]; rw [Nat.mod_add_mod, add_assoc])

/-- `q + 0 = q`. -/
private theorem arcIdx_zero {L : ℕ} (hL : 0 < L) (q : Fin L) : arcIdx hL q 0 = q :=
  Fin.ext (by simp [arcIdx, Nat.mod_eq_of_lt q.isLt])

/-- `q + 1` is the successor of `q`. -/
private theorem arcIdx_one {L : ℕ} (hL : 0 < L) (q : Fin L) : arcIdx hL q 1 = finRotate L q := by
  rw [← finRotate_arcIdx, arcIdx_zero]

/-- `q + x = q + y` modulo `L` exactly when `x ≡ y` modulo `L`. -/
private theorem arcIdx_eq_arcIdx_iff {L : ℕ} (hL : 0 < L) (q : Fin L) (x y : ℕ) :
    arcIdx hL q x = arcIdx hL q y ↔ x % L = y % L := by
  rw [Fin.ext_iff]
  exact ⟨fun h => Nat.ModEq.add_left_cancel' _ h, fun h => Nat.ModEq.add_left _ h⟩

/-- Every index of the cycle is `q + k` for some `k < L`. -/
private theorem exists_arcIdx_eq {L : ℕ} (hL : 0 < L) (q i : Fin L) :
    ∃ k < L, arcIdx hL q k = i := by
  refine ⟨(i + L - q) % L, Nat.mod_lt _ hL, Fin.ext ?_⟩
  simp only [arcIdx]
  rw [Nat.add_mod_mod, show (q : ℕ) + (i + L - q) = i + L by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt i.isLt]

/-- Two arc indices `x, y < L` are equal exactly when `x = y`. -/
private theorem arcIdx_inj {L : ℕ} (hL : 0 < L) (q : Fin L) {x y : ℕ} (hx : x < L) (hy : y < L) :
    arcIdx hL q x = arcIdx hL q y ↔ x = y := by
  rw [arcIdx_eq_arcIdx_iff, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-- Adjacency along a chordless cycle, in arc coordinates. -/
private theorem IsChordlessCycle.adj_arcIdx {B : Matrix (Fin n) (Fin n) ℤ} {L : ℕ}
    {c : Fin L → Fin n} (hc : IsChordlessCycle B c) (hL : 0 < L) (q : Fin L) {x y : ℕ}
    (hx : x < L) (hy : y < L) (hxy : x ≠ y) :
    (diagramGraph B).Adj (c (arcIdx hL q x)) (c (arcIdx hL q y)) ↔
      y = x + 1 ∨ x = y + 1 ∨ (x + 1 = L ∧ y = 0) ∨ (y + 1 = L ∧ x = 0) := by
  rw [hc.2.2 _ _ (fun h => hxy ((arcIdx_inj hL q hx hy).1 h)), finRotate_arcIdx,
    finRotate_arcIdx, arcIdx_eq_arcIdx_iff, arcIdx_eq_arcIdx_iff, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy]
  rcases Nat.lt_or_ge (x + 1) L with h₁ | h₁ <;> rcases Nat.lt_or_ge (y + 1) L with h₂ | h₂
  · rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂]; omega
  · rw [Nat.mod_eq_of_lt h₁, show y + 1 = L by omega, Nat.mod_self]; omega
  · rw [show x + 1 = L by omega, Nat.mod_self, Nat.mod_eq_of_lt h₂]; omega
  · rw [show x + 1 = L by omega, Nat.mod_self, show y + 1 = L by omega]; omega

/-- If `P` holds at `q` and at `q + (L - 1)` but at no `q + k` with `0 < k < L - 1`, then `P`
holds exactly at `p = q + (L - 1)` and at its successor `q`. -/
private theorem forall_iff_of_gap {L : ℕ} (hL : 0 < L) {P : Fin L → Prop} (q : Fin L)
    (h0 : P q) (hmid : ∀ k, 0 < k → k < L - 1 → ¬P (arcIdx hL q k))
    (hlast : P (arcIdx hL q (L - 1))) :
    ∀ i, P i ↔ i = arcIdx hL q (L - 1) ∨ i = finRotate L (arcIdx hL q (L - 1)) := by
  intro i
  obtain ⟨k, hk, rfl⟩ := exists_arcIdx_eq hL q i
  rw [finRotate_arcIdx, show L - 1 + 1 = L by omega, arcIdx_inj hL q hk (by omega),
    arcIdx_eq_arcIdx_iff, Nat.mod_self, Nat.mod_eq_of_lt hk]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [arcIdx_zero, h0, or_true]
  rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt hk) with rfl | hk1
  · simp only [hlast, true_or]
  · exact iff_of_false (hmid k hk0 hk1) (by omega)

/-- The first neighbour of `P` after `q` along the cycle. -/
private theorem exists_first_arcIdx {L : ℕ} (hL : 0 < L) {P : Fin L → Prop} (q : Fin L)
    (h : ∃ i, i ≠ q ∧ P i) :
    ∃ d, 0 < d ∧ d < L ∧ P (arcIdx hL q d) ∧ ∀ k, 0 < k → k < d → ¬P (arcIdx hL q k) := by
  classical
  have hex : ∃ k, (0 < k ∧ k < L) ∧ P (arcIdx hL q k) := by
    obtain ⟨i, hi, hPi⟩ := h
    obtain ⟨k, hk, rfl⟩ := exists_arcIdx_eq hL q i
    refine ⟨k, ⟨Nat.pos_of_ne_zero fun h0 => hi ?_, hk⟩, hPi⟩
    rw [h0, arcIdx_zero]
  obtain ⟨⟨h1, h2⟩, h3⟩ := Nat.find_spec hex
  exact ⟨_, h1, h2, h3, fun k hk hkd hPk => Nat.find_min hex hkd ⟨⟨hk, by omega⟩, hPk⟩⟩

/-! ### The sub-cycles closed up by an outside vertex -/

/-- The cycle `(c_q, c_{q+1}, …, c_{q+d}, v)` formed by an arc of a cycle `c` and a vertex `v`. -/
private def arcCycle {L : ℕ} (hL : 0 < L) (c : Fin L → Fin n) (v : Fin n) (q : Fin L) (d : ℕ) :
    Fin (d + 2) → Fin n :=
  fun t => if (t : ℕ) ≤ d then c (arcIdx hL q t) else v

/-- The first `d + 1` entries of `arcCycle` are the arc `c_q, …, c_{q+d}`. -/
private theorem arcCycle_of_le {L : ℕ} (hL : 0 < L) (c : Fin L → Fin n) (v : Fin n) (q : Fin L)
    {d : ℕ} (t : Fin (d + 2)) (ht : (t : ℕ) ≤ d) : arcCycle hL c v q d t = c (arcIdx hL q t) :=
  if_pos ht

/-- The last entry of `arcCycle` is `v`. -/
private theorem arcCycle_last {L : ℕ} (hL : 0 < L) (c : Fin L → Fin n) (v : Fin n) (q : Fin L)
    (d : ℕ) : arcCycle hL c v q d (Fin.last (d + 1)) = v :=
  if_neg (by simp)

/-- The arc of a chordless cycle between two neighbours of an outside vertex `v`, closed up by
`v`, is a chordless cycle when `v` has no neighbour inside the arc and the arc is proper. -/
private theorem IsChordlessCycle.isChordlessCycle_arcCycle {B : Matrix (Fin n) (Fin n) ℤ}
    {L : ℕ} {c : Fin L → Fin n} (hc : IsChordlessCycle B c) (hL : 0 < L) {v : Fin n}
    (hv : v ∉ Set.range c) (q : Fin L) {d : ℕ} (hd1 : 1 ≤ d) (hd2 : d + 2 ≤ L)
    (h0 : (diagramGraph B).Adj v (c q)) (hd : (diagramGraph B).Adj v (c (arcIdx hL q d)))
    (hmid : ∀ k, 0 < k → k < d → ¬(diagramGraph B).Adj v (c (arcIdx hL q k))) :
    IsChordlessCycle B (arcCycle hL c v q d) := by
  have hvadj : ∀ s : ℕ, s ≤ d → ((diagramGraph B).Adj v (c (arcIdx hL q s)) ↔ s = 0 ∨ s = d) := by
    intro s hs
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · simp only [arcIdx_zero, h0, true_or]
    rcases eq_or_lt_of_le hs with rfl | hsd
    · simp only [hd, or_true]
    · exact iff_of_false (hmid s hs0 hsd) (by omega)
  have hrot : ∀ s t : Fin (d + 2), t = finRotate (d + 2) s ↔ (t : ℕ) = (s + 1) % (d + 2) :=
    fun s t => by rw [Fin.ext_iff, val_finRotate_eq_mod]
  refine ⟨by omega, ?_, fun s t hst => ?_⟩
  · intro s t hst
    simp only [arcCycle] at hst
    split_ifs at hst with hs ht ht
    · exact Fin.ext ((arcIdx_inj hL q (by omega) (by omega)).1 (hc.2.1 hst))
    · exact absurd ⟨_, hst⟩ hv
    · exact absurd ⟨_, hst.symm⟩ hv
    · exact Fin.ext (by omega)
  have hst' : (s : ℕ) ≠ t := fun h => hst (Fin.ext h)
  rw [hrot, hrot]
  simp only [arcCycle]
  split_ifs with hs ht ht
  · rw [hc.adj_arcIdx hL q (by omega) (by omega) hst',
      Nat.mod_eq_of_lt (by omega : (s : ℕ) + 1 < d + 2),
      Nat.mod_eq_of_lt (by omega : (t : ℕ) + 1 < d + 2)]
    omega
  · rw [(diagramGraph B).adj_comm, hvadj s hs, Nat.mod_eq_of_lt (by omega : (s : ℕ) + 1 < d + 2),
      show (t : ℕ) + 1 = d + 2 by omega, Nat.mod_self]
    omega
  · rw [hvadj t ht, Nat.mod_eq_of_lt (by omega : (t : ℕ) + 1 < d + 2),
      show (s : ℕ) + 1 = d + 2 by omega, Nat.mod_self]
    omega
  · omega

/-- **The sub-cycles `Z_a`**: in a `2`-finite matrix, a vertex `v` off an oriented cycle `c`
with neighbours `c_q` and `c_{q+d}` and none strictly between them along a proper arc
receives the arrows `c_{q+d} → v → c_q`. -/
private theorem IsTwoFinite.pos_of_arc {B : Matrix (Fin n) (Fin n) ℤ} (hB : IsTwoFinite B)
    {L : ℕ} {c : Fin L → Fin n} (hc : IsChordlessCycle B c)
    (hco : ∀ i, 0 < B (c i) (c (finRotate L i))) (hL : 0 < L) {v : Fin n}
    (hv : v ∉ Set.range c) (q : Fin L) {d : ℕ} (hd1 : 1 ≤ d) (hd2 : d + 2 ≤ L)
    (h0 : (diagramGraph B).Adj v (c q)) (hd : (diagramGraph B).Adj v (c (arcIdx hL q d)))
    (hmid : ∀ k, 0 < k → k < d → ¬(diagramGraph B).Adj v (c (arcIdx hL q k))) :
    0 < B (c (arcIdx hL q d)) v ∧ 0 < B v (c q) ∧
      IsAdmissibleCycleWeights (cycleWeights B (arcCycle hL c v q d)) := by
  have hZ := hc.isChordlessCycle_arcCycle hL hv q hd1 hd2 h0 hd hmid
  obtain ⟨hor, hadm⟩ := hB.isCyclicallyOriented_of_isChordlessCycle hZ
  have e1 : finRotate (d + 2) ⟨d, by omega⟩ = Fin.last (d + 1) :=
    Fin.ext (by rw [val_finRotate_eq_mod]; exact Nat.mod_eq_of_lt (by simp))
  have e2 : finRotate (d + 2) (Fin.last (d + 1)) = ⟨0, by omega⟩ :=
    Fin.ext (by rw [val_finRotate_eq_mod]; simp)
  have e3 : finRotate (d + 2) ⟨0, by omega⟩ = ⟨1, by omega⟩ :=
    Fin.ext (by
      rw [val_finRotate_eq_mod]
      exact Nat.mod_eq_of_lt (by change 0 + 1 < d + 2; omega))
  have z0 : arcCycle hL c v q d ⟨0, by omega⟩ = c q := by
    rw [arcCycle_of_le _ _ _ _ _ (Nat.zero_le _), arcIdx_zero]
  have z1 : arcCycle hL c v q d ⟨1, by omega⟩ = c (finRotate L q) := by
    rw [arcCycle_of_le _ _ _ _ _ (by simpa using hd1), ← arcIdx_zero hL q, finRotate_arcIdx,
      arcIdx_zero]
  have zd : arcCycle hL c v q d ⟨d, by omega⟩ = c (arcIdx hL q d) :=
    arcCycle_of_le _ _ _ _ _ le_rfl
  have zl := arcCycle_last hL c v q d
  rcases hor with hor | hor
  · have h₁ := hor ⟨d, by omega⟩
    have h₂ := hor (Fin.last (d + 1))
    rw [e1, zd, zl] at h₁
    rw [e2, zl, z0] at h₂
    exact ⟨h₁, h₂, hadm⟩
  · exfalso
    have := hor ⟨0, by omega⟩
    rw [e3, z0, z1] at this
    exact hB.1.not_pos_of_pos (hco q) this

/-! ### Inserting a vertex into a cycle -/

/-- The value of `s.succAbove i`. -/
private theorem val_succAbove' {L : ℕ} (s : Fin (L + 1)) (i : Fin L) :
    (s.succAbove i : ℕ) = if (i : ℕ) < s then (i : ℕ) else (i : ℕ) + 1 := by
  by_cases h : (i : ℕ) < s
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa), Fin.val_castSucc, if_pos h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega), Fin.val_succ, if_neg h]

/-- The successor map of the cycle `(c₁, …, c_p, v, c_{p+1}, …, c_L)`, at the old indices. -/
private theorem finRotate_succ_succAbove {L : ℕ} (p i : Fin L) :
    finRotate (L + 1) (p.succ.succAbove i) =
      if i = p then p.succ else p.succ.succAbove (finRotate L i) := by
  have hL : 0 < L := Fin.pos p
  split_ifs with h
  · subst h
    rw [Fin.ext_iff, val_finRotate_eq_ite, val_succAbove', Fin.val_succ]
    split_ifs <;> omega
  · have h' : (i : ℕ) ≠ p := fun h'' => h (Fin.ext h'')
    rw [Fin.ext_iff, val_finRotate_eq_ite, val_succAbove', val_succAbove', Fin.val_succ,
      val_finRotate_eq_ite]
    have := i.isLt
    split_ifs <;> omega

/-- The successor map of the cycle `(c₁, …, c_p, v, c_{p+1}, …, c_L)`, at the new index. -/
private theorem finRotate_succ_self {L : ℕ} (p : Fin L) :
    finRotate (L + 1) p.succ = p.succ.succAbove (finRotate L p) := by
  have hL : 0 < L := Fin.pos p
  rw [Fin.ext_iff, val_finRotate_eq_ite, val_succAbove', Fin.val_succ,
    val_finRotate_eq_ite]
  have := p.isLt
  split_ifs <;> omega

/-! ### A vertex attached to an oriented unit cycle -/

/-- `finRotate L` has no fixed point for `L ≥ 2`. -/
private theorem finRotate_ne_self {L : ℕ} (hL : 2 ≤ L) (p : Fin L) : finRotate L p ≠ p := by
  intro h
  have h' := congrArg Fin.val h
  have := p.isLt
  rw [val_finRotate_eq_ite] at h'
  split_ifs at h' <;> omega

/-- The square of `finRotate L` has no fixed point for `L ≥ 3`. -/
theorem finRotate_finRotate_ne_self {L : ℕ} (hL : 3 ≤ L) (p : Fin L) :
    finRotate L (finRotate L p) ≠ p := by
  intro h
  have h' := congrArg Fin.val h
  have := p.isLt
  rw [val_finRotate_eq_ite, val_finRotate_eq_ite] at h'
  split_ifs at h' <;> omega

/-- In a `2`-finite matrix, a vertex `v` off an oriented chordless cycle `c` with at least two
neighbours on `c` has exactly two neighbours on it, and they are consecutive: `c_p` and
`c_{p+1}`. -/
private theorem IsTwoFinite.exists_adj_iff_of_isChordlessCycle {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : IsTwoFinite B) {L : ℕ} (hL : 0 < L) {c : Fin L → Fin n} (hc : IsChordlessCycle B c)
    (hor : ∀ i, 0 < B (c i) (c (finRotate L i))) {v : Fin n} (hv : v ∉ Set.range c)
    (h2 : ∃ i i', i ≠ i' ∧ (diagramGraph B).Adj v (c i) ∧ (diagramGraph B).Adj v (c i')) :
    ∃ p : Fin L, ∀ i, (diagramGraph B).Adj v (c i) ↔ i = p ∨ i = finRotate L p := by
  obtain ⟨i, i', hii', hi, hi'⟩ := h2
  obtain ⟨d₀, hd₀, hd₀L, hPd₀, hmid₀⟩ := exists_first_arcIdx hL (P := fun j =>
    (diagramGraph B).Adj v (c j)) i ⟨i', hii'.symm, hi'⟩
  by_cases h₀ : d₀ = L - 1
  · subst h₀
    exact ⟨_, forall_iff_of_gap hL i hi hmid₀ hPd₀⟩
  obtain ⟨hpos₁, -, -⟩ := hB.pos_of_arc hc hor hL hv i hd₀ (by omega) hi hPd₀ hmid₀
  have hq₁ : arcIdx hL i d₀ ≠ i := by
    conv_rhs => rw [← arcIdx_zero hL i]
    rw [Ne, arcIdx_inj hL i hd₀L hL]
    omega
  obtain ⟨d₁, hd₁, hd₁L, hPd₁, hmid₁⟩ := exists_first_arcIdx hL (P := fun j =>
    (diagramGraph B).Adj v (c j)) (arcIdx hL i d₀) ⟨i, hq₁.symm, hi⟩
  by_cases h₁ : d₁ = L - 1
  · subst h₁
    exact ⟨_, forall_iff_of_gap hL _ hPd₀ hmid₁ hPd₁⟩
  obtain ⟨-, hpos₂, -⟩ := hB.pos_of_arc hc hor hL hv _ hd₁ (by omega) hPd₀ hPd₁ hmid₁
  exact (hB.1.not_pos_of_pos hpos₁ hpos₂).elim

/-- The weights of an admissible triangle `(c_p, c_{p+1}, v)` with `w(c_p, c_{p+1}) = 1`: the two
weights at `v` are both `1` or both `2`. -/
private theorem diagramWeight_eq_of_isAdmissibleCycleWeights_arcCycle
    {B : Matrix (Fin n) (Fin n) ℤ} {L : ℕ} (hL : 0 < L) {c : Fin L → Fin n} {v : Fin n}
    {p : Fin L} (hw : diagramWeight B (c p) (c (finRotate L p)) = 1)
    (hadm : IsAdmissibleCycleWeights (cycleWeights B (arcCycle hL c v p 1))) :
    (diagramWeight B (c (finRotate L p)) v = 1 ∧ diagramWeight B v (c p) = 1) ∨
      (diagramWeight B (c (finRotate L p)) v = 2 ∧ diagramWeight B v (c p) = 2) := by
  have z0 : arcCycle hL c v p 1 0 = c p := by
    rw [arcCycle_of_le _ _ _ _ _ (by decide)]
    exact congrArg c (arcIdx_zero hL p)
  have z1 : arcCycle hL c v p 1 1 = c (finRotate L p) := by
    rw [arcCycle_of_le _ _ _ _ _ (by decide)]
    exact congrArg c (arcIdx_one hL p)
  have z2 : arcCycle hL c v p 1 2 = v := arcCycle_last hL c v p 1
  have w0 : cycleWeights B (arcCycle hL c v p 1) 0 = 1 := by
    rwa [cycleWeights, show finRotate (1 + 2) 0 = 1 by decide, z0, z1]
  have w1 : cycleWeights B (arcCycle hL c v p 1) 1 = diagramWeight B (c (finRotate L p)) v := by
    rw [cycleWeights, show finRotate (1 + 2) 1 = 2 by decide, z1, z2]
  have w2 : cycleWeights B (arcCycle hL c v p 1) 2 = diagramWeight B v (c p) := by
    rw [cycleWeights, show finRotate (1 + 2) 2 = 0 by decide, z2, z0]
  rcases hadm with hall | ⟨h3, hmem⟩ | ⟨h4, -⟩
  · exact Or.inl ⟨w1 ▸ hall 1, w2 ▸ hall 2⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    have e : ∀ f : Fin 3 → ℕ, (cycleWeights B (arcCycle hL c v p 1) ∘ Fin.cast h3.symm) = f →
        f 0 = 1 ∧ f 1 = diagramWeight B (c (finRotate L p)) v ∧
          f 2 = diagramWeight B v (c p) := by
      rintro f rfl
      exact ⟨w0, w1, w2⟩
    rcases hmem with h | h | h <;> obtain ⟨e0, e1, e2⟩ := e _ h <;>
      simp [-finRotate_apply] at e0 e1 e2
    exact Or.inr ⟨e1.symm, e2.symm⟩
  · omega

/-- Mutation at a vertex `v` off a cycle `c`, with `c_{p+1} → v → c_p` and no other neighbour on
`c`, changes neither the weight nor the arrow between `c_i` and `c_j` unless `{c_i, c_j}` is
`{c_p, c_{p+1}}`. -/
private theorem SkewSymmetrizable.matrixMutation_pair_of_ne_finRotate
    {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B) {L : ℕ} {c : Fin L → Fin n}
    {v : Fin n} (hcv : ∀ i, c i ≠ v) {p : Fin L}
    (hp : ∀ i, (diagramGraph B).Adj v (c i) ↔ i = p ∨ i = finRotate L p)
    (hA : 0 < B (c (finRotate L p)) v) (hA' : 0 < B v (c p)) (i j : Fin L)
    (h₁ : ¬(i = finRotate L p ∧ j = p)) (h₂ : ¬(j = finRotate L p ∧ i = p)) :
    diagramWeight (matrixMutation le_rfl B v) (c i) (c j) = diagramWeight B (c i) (c j) ∧
      (0 < matrixMutation le_rfl B v (c i) (c j) ↔ 0 < B (c i) (c j)) := by
  have harr : ∀ a b, 0 < B (c a) v → 0 < B v (c b) → a = finRotate L p ∧ b = p := by
    intro a b ha hb
    have hav : (diagramGraph B).Adj v (c a) := ⟨(hcv a).symm, by
      rw [diagramWeight_comm]; exact (hB.diagramWeight_pos_iff _ _).2 ha.ne'⟩
    rcases (hp a).1 hav with rfl | rfl
    · exact (hB.not_pos_of_pos ha hA').elim
    rcases (hp b).1 ⟨(hcv b).symm, (hB.diagramWeight_pos_iff _ _).2 hb.ne'⟩ with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact (hB.not_pos_of_pos hA hb).elim
  exact hB.matrixMutation_pair_of_not (hcv i) (hcv j) (fun h => h₁ (harr i j h.1 h.2))
    (fun h => h₂ (harr j i h.1 h.2))

/-- If `v` is adjacent to exactly the consecutive vertices `c_p`, `c_{p+1}` of an oriented unit
cycle of a `2`-finite `B`, the two weights at `v` are not both `2`. -/
private theorem IsTwoFinite.not_diagramWeight_eq_two {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : IsTwoFinite B) {L : ℕ} (hL : 3 ≤ L) {c : Fin L → Fin n} (hc : IsOrientedUnitCycle B c)
    {v : Fin n} (hcv : ∀ i, c i ≠ v) {p : Fin L}
    (hp : ∀ i, (diagramGraph B).Adj v (c i) ↔ i = p ∨ i = finRotate L p)
    (hA : 0 < B (c (finRotate L p)) v) (hA' : 0 < B v (c p))
    (hw1 : diagramWeight B (c (finRotate L p)) v = 2) (hw2 : diagramWeight B v (c p) = 2) :
    False := by
  obtain ⟨hcc, hco⟩ := hc
  have hcw : diagramWeight B (c p) (c (finRotate L p)) = 1 := (hco p).2
  have hunch := hB.1.matrixMutation_pair_of_ne_finRotate hcv hp hA hA'
  have hS := hB.1.skewSymmetrization_matrixMutation_of_pos_pos hA hA'
  set B' := matrixMutation le_rfl B v
  have hB's : SkewSymmetrizable B' := skewSymmetrizable_matrixMutation hB.1 v
  have hS1 : skewSymmetrization (B'.map (Int.cast : ℤ → ℝ)) (c (finRotate L p)) (c p) = 1 := by
    rw [hS.1, hB.1.skewSymmetrization_eq_neg_sqrt (hco p).1,
      diagramWeight_comm B (c (finRotate L p)) (c p), hcw, hw1, hw2,
      show ((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have hwex : diagramWeight B' (c (finRotate L p)) (c p) = 1 := by
    simpa using (hB's.diagramWeight_of_skewSymmetrization_eq hS1).1
  have hw' : ∀ i j, diagramWeight B' (c i) (c j) = diagramWeight B (c i) (c j) := by
    intro i j
    by_cases h₁ : i = finRotate L p ∧ j = p
    · rw [h₁.1, h₁.2, hwex, diagramWeight_comm, hcw]
    by_cases h₂ : j = finRotate L p ∧ i = p
    · rw [h₂.1, h₂.2, diagramWeight_comm B', hwex, hcw]
    exact (hunch i j h₁ h₂).1
  have hcc' : IsChordlessCycle B' c := ⟨hcc.1, hcc.2.1, fun i j hij => by
    rw [← hcc.2.2 i j hij, diagramGraph_adj, diagramGraph_adj, hw']⟩
  have hB'2 : IsTwoFinite B' := by
    simpa only [matrixMutationList_singleton] using hB.matrixMutationList [v]
  rcases (hB'2.isCyclicallyOriented_of_isChordlessCycle hcc').1 with h | h
  · have := (hB's.skewSymmetrization_apply (c p) (c (finRotate L p))).2.2.2 (h p)
    rw [hS.2, hS1] at this
    norm_num at this
  · have := (hunch _ _ (fun h' => finRotate_ne_self (by omega) p h'.2)
      (fun h' => finRotate_finRotate_ne_self hL p h'.2)).2.1 (h (finRotate L p))
    exact hB.1.not_pos_of_pos (hco _).1 this

/-- With both weights at `v` equal to `1`, the mutation at `v` removes the edge `c_p c_{p+1}`. -/
private theorem IsOrientedUnitCycle.diagramWeight_matrixMutation_eq_zero
    {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B) {L : ℕ} {c : Fin L → Fin n}
    (hc : IsOrientedUnitCycle B c) {v : Fin n} {p : Fin L}
    (hA : 0 < B (c (finRotate L p)) v) (hA' : 0 < B v (c p))
    (hw1 : diagramWeight B (c (finRotate L p)) v = 1) (hw2 : diagramWeight B v (c p) = 1) :
    diagramWeight (matrixMutation le_rfl B v) (c (finRotate L p)) (c p) = 0 := by
  have hcw : diagramWeight B (c p) (c (finRotate L p)) = 1 := (hc.2 p).2
  have hS : skewSymmetrization ((matrixMutation le_rfl B v).map (Int.cast : ℤ → ℝ))
      (c (finRotate L p)) (c p) = 0 := by
    rw [(hB.skewSymmetrization_matrixMutation_of_pos_pos hA hA').1,
      hB.skewSymmetrization_eq_neg_sqrt (hc.2 p).1,
      diagramWeight_comm B (c (finRotate L p)) (c p), hcw, hw1, hw2]
    norm_num
  simpa using ((skewSymmetrizable_matrixMutation hB v).diagramWeight_of_skewSymmetrization_eq hS).1

/-- With both weights at `v` equal to `1`, after the mutation at `v` two indices `c_i ≠ c_j` of the
cycle are adjacent exactly when they are consecutive along the cycle, other than `c_p, c_{p+1}`. -/
private theorem IsOrientedUnitCycle.adj_matrixMutation_iff {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) {L : ℕ} (hL : 3 ≤ L) {c : Fin L → Fin n}
    (hc : IsOrientedUnitCycle B c) {v : Fin n} (hcv : ∀ i, c i ≠ v) {p : Fin L}
    (hp : ∀ i, (diagramGraph B).Adj v (c i) ↔ i = p ∨ i = finRotate L p)
    (hA : 0 < B (c (finRotate L p)) v) (hA' : 0 < B v (c p))
    (hw1 : diagramWeight B (c (finRotate L p)) v = 1) (hw2 : diagramWeight B v (c p) = 1)
    {i j : Fin L} (hij : i ≠ j) :
    (diagramGraph (matrixMutation le_rfl B v)).Adj (c i) (c j) ↔
      (i ≠ p ∧ j = finRotate L i) ∨ (j ≠ p ∧ i = finRotate L j) := by
  have hwex := hc.diagramWeight_matrixMutation_eq_zero hB hA hA' hw1 hw2
  have hrotp2 := finRotate_finRotate_ne_self hL p
  by_cases h₁ : i = finRotate L p ∧ j = p
  · rw [h₁.1, h₁.2, diagramGraph_adj, hwex]
    simp only [lt_self_iff_false, and_false, false_iff, not_or, not_and]
    exact ⟨fun _ h => hrotp2 h.symm, fun h => absurd rfl h⟩
  by_cases h₂ : j = finRotate L p ∧ i = p
  · rw [h₂.1, h₂.2, diagramGraph_adj, diagramWeight_comm, hwex]
    simp only [lt_self_iff_false, and_false, false_iff, not_or, not_and]
    exact ⟨fun h => absurd rfl h, fun _ h => hrotp2 h.symm⟩
  rw [diagramGraph_adj, (hB.matrixMutation_pair_of_ne_finRotate hcv hp hA hA' i j h₁ h₂).1,
    ← diagramGraph_adj, hc.1.2.2 i j hij]
  exact ⟨fun h => h.imp (fun h => ⟨fun hi => h₂ ⟨hi ▸ h, hi⟩, h⟩)
    (fun h => ⟨fun hj => h₁ ⟨hj ▸ h, hj⟩, h⟩), fun h => h.imp And.right And.right⟩

/-- `(c₁, …, c_{s-1}, v, c_s, …, c_L)` has pairwise distinct entries when the `cᵢ` do and `v` is
not among them. -/
private theorem injective_insertNth {L N : ℕ} {c : Fin L → Fin N} (hc : Function.Injective c)
    {v : Fin N} (hcv : ∀ i, c i ≠ v) (s : Fin (L + 1)) :
    Function.Injective (Fin.insertNth (α := fun _ => Fin N) s v c) := by
  have hZs : Fin.insertNth (α := fun _ => Fin N) s v c s = v := Fin.insertNth_apply_same _ _ _
  have hZa : ∀ i, Fin.insertNth (α := fun _ => Fin N) s v c (s.succAbove i) = c i :=
    Fin.insertNth_apply_succAbove _ _ _
  intro x y hxy
  rcases Fin.eq_self_or_eq_succAbove s x with hx | ⟨i, rfl⟩ <;>
    rcases Fin.eq_self_or_eq_succAbove s y with hy | ⟨j, rfl⟩
  · rw [hx, hy]
  · rw [hx, hZs, hZa] at hxy
    exact absurd hxy.symm (hcv j)
  · rw [hy, hZs, hZa] at hxy
    exact absurd hxy (hcv i)
  · rw [hZa, hZa] at hxy
    rw [hc hxy]

/-- With both weights at `v` equal to `1`, `(c₁, …, c_p, v, c_{p+1}, …, c_L)` is an oriented
unit cycle of `μ_v(B)`. -/
private theorem IsOrientedUnitCycle.isOrientedUnitCycle_insertNth
    {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B) {L : ℕ} (hL : 3 ≤ L)
    {c : Fin L → Fin n} (hc : IsOrientedUnitCycle B c) {v : Fin n} (hcv : ∀ i, c i ≠ v)
    {p : Fin L} (hp : ∀ i, (diagramGraph B).Adj v (c i) ↔ i = p ∨ i = finRotate L p)
    (hA : 0 < B (c (finRotate L p)) v) (hA' : 0 < B v (c p))
    (hw1 : diagramWeight B (c (finRotate L p)) v = 1) (hw2 : diagramWeight B v (c p) = 1) :
    IsOrientedUnitCycle (matrixMutation le_rfl B v)
      (Fin.insertNth (α := fun _ => Fin n) p.succ v c) := by
  have hrotp2 := finRotate_finRotate_ne_self hL p
  have hunch := hB.matrixMutation_pair_of_ne_finRotate hcv hp hA hA'
  have hvw := hB.diagramWeight_matrixMutation_self v
  set B' := matrixMutation le_rfl B v
  set Z : Fin (L + 1) → Fin n := Fin.insertNth (α := fun _ => Fin n) p.succ v c
  have hZs : Z p.succ = v := Fin.insertNth_apply_same _ _ _
  have hZa : ∀ i, Z (p.succ.succAbove i) = c i := Fin.insertNth_apply_succAbove _ _ _
  have hrA := finRotate_succ_succAbove p
  have hrS := finRotate_succ_self p
  have hadjv : ∀ j, (diagramGraph B').Adj v (c j) ↔ j = p ∨ j = finRotate L p := fun j => by
    rw [← hp j, diagramGraph_adj, diagramGraph_adj, (hvw (c j)).2.1]
  refine ⟨⟨by omega, injective_insertNth hc.1.2.1 hcv p.succ, ?_⟩, ?_⟩
  · intro x y hxy
    rcases Fin.eq_self_or_eq_succAbove p.succ x with rfl | ⟨i, rfl⟩ <;>
      rcases Fin.eq_self_or_eq_succAbove p.succ y with rfl | ⟨j, rfl⟩
    · exact absurd rfl hxy
    · rw [hZs, hZa, hadjv, hrS, hrA, Fin.succAbove_right_inj]
      split_ifs with hj
      · exact iff_of_true (Or.inl hj) (Or.inr rfl)
      · rw [or_iff_right hj, or_iff_left (Fin.succAbove_ne _ _).symm]
    · rw [hZs, hZa, (diagramGraph B').adj_comm, hadjv, hrS, hrA, Fin.succAbove_right_inj]
      split_ifs with hi
      · exact iff_of_true (Or.inl hi) (Or.inl rfl)
      · rw [or_iff_right hi, or_iff_right (Fin.succAbove_ne _ _).symm]
    · have hij : i ≠ j := fun h => hxy (h ▸ rfl)
      rw [hZa, hZa, hc.adj_matrixMutation_iff hB hL hcv hp hA hA' hw1 hw2 hij, hrA, hrA]
      split_ifs with hi hj hj
      · exact absurd (hi.trans hj.symm) hij
      · simp only [Fin.succAbove_right_inj, Fin.succAbove_ne, hi, hj, ne_eq, not_true_eq_false,
          not_false_eq_true, false_and, true_and, false_or]
      · simp only [Fin.succAbove_right_inj, Fin.succAbove_ne, hi, hj, ne_eq, not_true_eq_false,
          not_false_eq_true, false_and, true_and, or_false]
      · simp only [Fin.succAbove_right_inj, hi, hj, ne_eq, not_false_eq_true, true_and]
  · intro x
    rcases Fin.eq_self_or_eq_succAbove p.succ x with rfl | ⟨i, rfl⟩
    · rw [cycleWeights, hrS, hZs, hZa, (hvw _).2.2.2, (hvw _).2.1, diagramWeight_comm]
      exact ⟨hA, hw1⟩
    · rw [cycleWeights, hrA]
      split_ifs with hi
      · rw [hi, hZs, hZa, (hvw _).2.2.1, (hvw _).1, diagramWeight_comm]
        exact ⟨hA', hw2⟩
      · rw [hZa, hZa]
        have h₁ : ¬(i = finRotate L p ∧ finRotate L i = p) := fun h => hrotp2 (h.1 ▸ h.2)
        have h₂ : ¬(finRotate L i = finRotate L p ∧ i = p) := fun h => hi h.2
        rw [(hunch _ _ h₁ h₂).1, (hunch _ _ h₁ h₂).2]
        exact hc.2 i

/-- **A vertex attached to an oriented unit cycle.** Let `B` be `2`-finite, `(c₁, …, c_L)` an
oriented unit cycle of `B` with `L ≥ 4`, and `v` an index off the cycle adjacent to at least
two of the `cᵢ`. Then for some `p` the `cᵢ` adjacent to `v` are exactly `c_p` and `c_{p+1}`,
both weights at `v` are `1`, `c_{p+1} → v → c_p`, and
`(c₁, …, c_p, v, c_{p+1}, …, c_L)` is an oriented unit cycle of `μ_v(B)`; this last sequence is
`Fin.insertNth p.succ v c`. -/
@[cluster_algebras "lem_vertex_on_unit_cycle"]
theorem IsOrientedUnitCycle.exists_adj_eq_of_isTwoFinite {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : IsTwoFinite B) {L : ℕ} (hL : 4 ≤ L) {c : Fin L → Fin n} (hc : IsOrientedUnitCycle B c)
    {v : Fin n} (hv : v ∉ Set.range c)
    (h2 : ∃ i i', i ≠ i' ∧ (diagramGraph B).Adj v (c i) ∧ (diagramGraph B).Adj v (c i')) :
    ∃ p : Fin L, (∀ i, (diagramGraph B).Adj v (c i) ↔ i = p ∨ i = finRotate L p) ∧
      diagramWeight B v (c p) = 1 ∧ diagramWeight B v (c (finRotate L p)) = 1 ∧
      0 < B (c (finRotate L p)) v ∧ 0 < B v (c p) ∧
      IsOrientedUnitCycle (matrixMutation le_rfl B v)
        (Fin.insertNth (α := fun _ => Fin n) p.succ v c) := by
  have hL0 : 0 < L := by omega
  have hcv : ∀ i, c i ≠ v := fun i h => hv ⟨i, h⟩
  have hor : ∀ i, 0 < B (c i) (c (finRotate L i)) := fun i => (hc.2 i).1
  obtain ⟨p, hp⟩ := hB.exists_adj_iff_of_isChordlessCycle hL0 hc.1 hor hv h2
  obtain ⟨hA, hA', hadm⟩ := hB.pos_of_arc hc.1 hor hL0 hv p le_rfl (by omega)
    ((hp p).2 (Or.inl rfl)) (by rw [arcIdx_one]; exact (hp _).2 (Or.inr rfl))
    (fun k hk hk' => by omega)
  rw [arcIdx_one] at hA
  rcases diagramWeight_eq_of_isAdmissibleCycleWeights_arcCycle hL0 (hc.2 p).2 hadm with
    ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
  · exact ⟨p, hp, hw2, (diagramWeight_comm _ _ _).trans hw1, hA, hA',
      hc.isOrientedUnitCycle_insertNth hB.1 (by omega) hcv hp hA hA' hw1 hw2⟩
  · exact (hB.not_diagramWeight_eq_two (by omega) hc hcv hp hA hA' hw1 hw2).elim

/-! ### Sliding a doubled triangle along a path -/

/-- Mutation of a real square matrix, entrywise. -/
private theorem matrixMutation_apply_real {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (k α β : Fin N) :
    matrixMutation le_rfl M k α β = if α = k ∨ β = k then -M α β else
      M α β + max 0 (M α k) * max 0 (M k β) - max 0 (-M α k) * max 0 (-M k β) := by
  split_ifs with h
  · exact matrixMutation_apply_of_eq _ _ _ h
  · push Not at h
    exact matrixMutation_apply_of_ne_eq_max _ _ _ h.1 h.2

/-- The skew-symmetrization of the initial diagram of the sliding triangle. -/
private noncomputable def slideS₀ (m a : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun α β =>
    if (α : ℕ) = m then
      (if (β : ℕ) = a then √2 else if (β : ℕ) = a + 1 then -√2 else 0)
    else if (β : ℕ) = m then
      (if (α : ℕ) = a + 1 then √2 else if (α : ℕ) = a then -√2 else 0)
    else if (β : ℕ) = α + 1 then 1
    else if (α : ℕ) = β + 1 then -1
    else 0

/-- The skew-symmetrization of the diagram `Δ_j` of the sliding triangle, on the positions
`0, …, m - 1` of the path and `m` of the extra vertex. -/
private noncomputable def slideS (m j : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun α β =>
    if (α : ℕ) = m then
      (if (β : ℕ) = j then -√2 else if (β : ℕ) = j + 1 ∧ j + 1 < m then √2 else 0)
    else if (β : ℕ) = m then
      (if (α : ℕ) = j then √2 else if (α : ℕ) = j + 1 ∧ j + 1 < m then -√2 else 0)
    else if (β : ℕ) = α + 1 then (if (α : ℕ) = j then -1 else 1)
    else if (α : ℕ) = β + 1 then (if (β : ℕ) = j then 1 else -1)
    else 0

/-- Mutation at `u` turns the initial diagram into `Δ_a`. -/
private theorem matrixMutation_slideS₀ {m a : ℕ} (ha : a + 1 < m) :
    matrixMutation le_rfl (slideS₀ m a) (Fin.last m) = slideS m a := by
  have hr : (0 : ℝ) < √2 := by positivity
  have h1 : ∀ α : Fin (m + 1), max 0 (slideS₀ m a α (Fin.last m)) =
      if (α : ℕ) = a + 1 then √2 else 0 := fun α => by
    simp only [slideS₀, of_apply, Fin.val_last]
    split_ifs <;> first | omega | simp [hr.le]
  have h2 : ∀ α : Fin (m + 1), max 0 (-slideS₀ m a α (Fin.last m)) =
      if (α : ℕ) = a then √2 else 0 := fun α => by
    simp only [slideS₀, of_apply, Fin.val_last]
    split_ifs <;> first | omega | simp [hr.le]
  have h3 : ∀ β : Fin (m + 1), max 0 (slideS₀ m a (Fin.last m) β) =
      if (β : ℕ) = a then √2 else 0 := fun β => by
    simp only [slideS₀, of_apply, Fin.val_last]
    split_ifs <;> first | omega | simp [hr.le]
  have h4 : ∀ β : Fin (m + 1), max 0 (-slideS₀ m a (Fin.last m) β) =
      if (β : ℕ) = a + 1 then √2 else 0 := fun β => by
    simp only [slideS₀, of_apply, Fin.val_last]
    split_ifs <;> first | omega | simp [hr.le]
  ext α β
  rw [matrixMutation_apply_real, h1, h2, h3, h4]
  simp only [slideS, slideS₀, of_apply, Fin.ext_iff, Fin.val_last]
  have : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  rcases (by omega : (α : ℕ) = a ∨ (α : ℕ) = a + 1 ∨ (α : ℕ) = m ∨
    ((α : ℕ) ≠ a ∧ (α : ℕ) ≠ a + 1 ∧ (α : ℕ) ≠ m)) with h | h | h | h <;>
  rcases (by omega : (β : ℕ) = a ∨ (β : ℕ) = a + 1 ∨ (β : ℕ) = m ∨
    ((β : ℕ) ≠ a ∧ (β : ℕ) ≠ a + 1 ∧ (β : ℕ) ≠ m)) with h' | h' | h' | h' <;>
  · simp (disch := omega) only [if_pos, if_neg]
    all_goals (try split_ifs) <;> first | omega | linarith

/-- Mutation at `p_{j+1}` turns `Δ_j` into `Δ_{j+1}`. -/
private theorem matrixMutation_slideS {m j : ℕ} (hj : j + 1 < m) :
    matrixMutation le_rfl (slideS m j) ⟨j + 1, by omega⟩ = slideS m (j + 1) := by
  have hr : (0 : ℝ) < √2 := by positivity
  have hrr : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have h1 : ∀ α : Fin (m + 1), max 0 (slideS m j α ⟨j + 1, by omega⟩) =
      if (α : ℕ) = m then √2 else 0 := fun α => by
    simp only [slideS, of_apply, true_and]
    split_ifs <;> first | omega | simp [hr.le]
  have h2 : ∀ α : Fin (m + 1), max 0 (-slideS m j α ⟨j + 1, by omega⟩) =
      if (α : ℕ) = m then 0 else if (α : ℕ) = j then 1 else if (α : ℕ) = j + 2 then 1
      else 0 := fun α => by
    simp only [slideS, of_apply, true_and]
    split_ifs <;> first | omega | simp [hr.le]
  have h3 : ∀ β : Fin (m + 1), max 0 (slideS m j ⟨j + 1, by omega⟩ β) =
      if (β : ℕ) = m then 0 else if (β : ℕ) = j then 1 else if (β : ℕ) = j + 2 then 1
      else 0 := fun β => by
    simp only [slideS, of_apply, true_and]
    split_ifs <;> first | omega | simp [hr.le]
  have h4 : ∀ β : Fin (m + 1), max 0 (-slideS m j ⟨j + 1, by omega⟩ β) =
      if (β : ℕ) = m then √2 else 0 := fun β => by
    simp only [slideS, of_apply, true_and]
    split_ifs <;> first | omega | simp [hr.le]
  ext α β
  rw [matrixMutation_apply_real]
  split_ifs with hk
  · simp only [Fin.ext_iff] at hk
    simp only [slideS, of_apply]
    rcases hk with hk | hk <;> split_ifs <;> first | linarith | omega
  · rw [h1, h2, h3, h4]
    simp only [Fin.ext_iff, not_or] at hk
    obtain ⟨hk1, hk2⟩ := hk
    simp only [slideS, of_apply]
    by_cases hα : (α : ℕ) = m
    · simp only [hα, ↓reduceIte]
      split_ifs <;> first | linarith | omega
    by_cases hβ : (β : ℕ) = m
    · simp only [hα, hβ, ↓reduceIte]
      split_ifs <;> first | linarith | omega
    simp only [hα, hβ, ↓reduceIte, mul_zero, zero_mul, sub_zero, add_zero]
    split_ifs <;> first | linarith | omega

/-- Mutation along `p_{a+1}, …, p_{a+t}` turns `Δ_a` into `Δ_{a+t}`. -/
private theorem matrixMutationList_slideS {m a : ℕ} :
    ∀ t : ℕ, a + t < m → ∀ l : List (Fin (m + 1)),
      l.map Fin.val = List.Ico (a + 1) (a + 1 + t) →
        matrixMutationList le_rfl (slideS m a) l = slideS m (a + t)
  | 0, _, l, hl => by
    simp only [Nat.add_zero, List.Ico.self_empty, List.map_eq_nil_iff] at hl
    subst hl
    rfl
  | t + 1, ht, l, hl => by
    rw [show a + 1 + (t + 1) = a + 1 + t + 1 by ring, List.Ico.succ_top (by omega)] at hl
    obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 hl
    obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.1 h₂
    rw [matrixMutationList_append, matrixMutationList_slideS t (by omega) l₁ h₁,
      matrixMutationList_singleton,
      show x = ⟨a + t + 1, by omega⟩ from Fin.ext (by simp only [hx]; omega),
      matrixMutation_slideS (by omega)]
    rfl

/-- The positions `a + 1, …, m - 1` of the path after `a`. -/
private theorem map_val_filter_finRange_lt {m : ℕ} (a : Fin m) :
    (((List.finRange m).filter (fun i => a < i)).map Fin.castSucc).map Fin.val =
      List.Ico (a + 1) m := by
  rw [List.map_map]
  have h1 : (Fin.val ∘ Fin.castSucc : Fin m → ℕ) = Fin.val := rfl
  have h2 : (fun i : Fin m => decide (a < i)) =
      (fun x : ℕ => decide ((a : ℕ) + 1 ≤ x)) ∘ Fin.val := by
    funext i
    exact decide_eq_decide.2 (by rw [Fin.lt_def]; omega)
  have h3 : (List.finRange m).map Fin.val = List.range m := by simp
  rw [h1, h2, ← List.filter_map, h3, ← List.Ico.zero_bot,
    List.Ico.filter_le_of_le (Nat.zero_le _)]

/-- In `Δ_{m-1}` the adjacent positions are the consecutive ones. -/
private theorem slideS_last_ne_zero {m : ℕ} (hm : 1 ≤ m) (α β : Fin (m + 1)) :
    slideS m (m - 1) α β ≠ 0 ↔ (β : ℕ) = α + 1 ∨ (α : ℕ) = β + 1 := by
  have : (0 : ℝ) < √2 := by positivity
  simp only [slideS, of_apply]
  split_ifs <;> constructor <;> intro h <;> first | omega | exact absurd rfl h | norm_num

/-- In `Δ_{m-1}` every position points to the next one. -/
private theorem slideS_last_pos {m : ℕ} (hm : 1 ≤ m) {α β : Fin (m + 1)}
    (h : (α : ℕ) + 1 = β) : 0 < slideS m (m - 1) α β := by
  have : (0 : ℝ) < √2 := by positivity
  simp only [slideS, of_apply]
  split_ifs <;> first | omega | norm_num

/-- The weights of `Δ_{m-1}` along the path: `(1, …, 1, 2)`. -/
private theorem slideS_last_sq {m : ℕ} (hm : 1 ≤ m) {α β : Fin (m + 1)}
    (h : (α : ℕ) + 1 = β) : slideS m (m - 1) α β ^ 2 = if (β : ℕ) = m then 2 else 1 := by
  simp only [slideS, of_apply]
  split_ifs <;> first | omega | norm_num

/-- The row of `u` in `S(B)` for the initial diagram of the sliding triangle. -/
private theorem skewSymmetrization_apply_eq_slideS₀_last_castSucc {m : ℕ}
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hB : SkewSymmetrizable B)
    {p : Fin m → Fin (m + 1)} {u : Fin (m + 1)} {a a' : Fin m} (ha : (a : ℕ) + 1 = a')
    (hadj : ∀ i, (diagramGraph B).Adj u (p i) ↔ i = a ∨ i = a')
    (hua' : 0 < B (p a') u) (hua : 0 < B u (p a)) (hwa : diagramWeight B u (p a) = 2)
    (hwa' : diagramWeight B u (p a') = 2) (j : Fin m) :
    skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) u (p j) =
      slideS₀ m a (Fin.last m) (Fin.castSucc j) := by
  have := j.isLt
  by_cases h1 : j = a
  · subst h1
    rw [hB.skewSymmetrization_eq_sqrt hua, hwa]
    simp (disch := omega) only [slideS₀, of_apply, Fin.val_last, ↓reduceIte, Fin.val_castSucc]
    norm_num
  by_cases h2 : j = a'
  · subst h2
    have h1' : (j : ℕ) ≠ a := by omega
    rw [hB.skewSymmetrization_eq_neg_sqrt hua', hwa']
    simp (disch := omega) only [slideS₀, of_apply, Fin.val_last, ↓reduceIte, Fin.val_castSucc,
      if_neg, if_pos]
    norm_num
  rw [hB.skewSymmetrization_eq_zero (hB.apply_eq_zero_of_not_adj fun h => by
    rcases (hadj j).1 h with h | h <;> contradiction)]
  have h1' : (j : ℕ) ≠ a := fun h => h1 (Fin.ext h)
  have h2' : (j : ℕ) ≠ a' := fun h => h2 (Fin.ext h)
  simp (disch := omega) only [slideS₀, of_apply, Fin.val_last, ↓reduceIte, Fin.val_castSucc,
    if_neg]

/-- The column of `u` in `S(B)` for the initial diagram of the sliding triangle. -/
private theorem skewSymmetrization_apply_eq_slideS₀_castSucc_last {m : ℕ}
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hB : SkewSymmetrizable B)
    {p : Fin m → Fin (m + 1)} {u : Fin (m + 1)} {a a' : Fin m} (ha : (a : ℕ) + 1 = a')
    (hadj : ∀ i, (diagramGraph B).Adj u (p i) ↔ i = a ∨ i = a')
    (hua' : 0 < B (p a') u) (hua : 0 < B u (p a)) (hwa : diagramWeight B u (p a) = 2)
    (hwa' : diagramWeight B u (p a') = 2) (i : Fin m) :
    skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) (p i) u =
      slideS₀ m a (Fin.castSucc i) (Fin.last m) := by
  have := i.isLt
  by_cases h1 : i = a
  · subst h1
    rw [hB.skewSymmetrization_eq_neg_sqrt hua, diagramWeight_comm, hwa]
    simp (disch := omega) only [slideS₀, of_apply, Fin.val_last, ↓reduceIte, Fin.val_castSucc,
      if_neg]
    norm_num
  by_cases h2 : i = a'
  · subst h2
    have h1' : (i : ℕ) ≠ a := by omega
    rw [hB.skewSymmetrization_eq_sqrt hua', diagramWeight_comm, hwa']
    simp (disch := omega) only [slideS₀, of_apply, Fin.val_last, ↓reduceIte, Fin.val_castSucc,
      if_neg, if_pos]
    norm_num
  rw [hB.skewSymmetrization_eq_zero (hB.apply_eq_zero_of_not_adj fun h => by
    rcases (hadj i).1 h.symm with h | h <;> contradiction)]
  have h1' : (i : ℕ) ≠ a := fun h => h1 (Fin.ext h)
  have h2' : (i : ℕ) ≠ a' := fun h => h2 (Fin.ext h)
  simp (disch := omega) only [slideS₀, of_apply, Fin.val_last, ↓reduceIte, Fin.val_castSucc,
    if_pos, if_neg]

/-- The entries of `S(B)` along the path for the initial diagram of the sliding triangle. -/
private theorem skewSymmetrization_apply_eq_slideS₀_castSucc_castSucc {m : ℕ}
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hB : SkewSymmetrizable B)
    {p : Fin m → Fin (m + 1)} (hp : IsLinearlyOrientedPath B p)
    (hp1 : ∀ i j : Fin m, (i : ℕ) + 1 = j → diagramWeight B (p i) (p j) = 1) (a : ℕ)
    (i j : Fin m) :
    skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) (p i) (p j) =
      slideS₀ m a (Fin.castSucc i) (Fin.castSucc j) := by
  have := i.isLt
  have := j.isLt
  by_cases h1 : (i : ℕ) + 1 = j
  · rw [hB.skewSymmetrization_eq_sqrt (hp.2 i j h1), hp1 i j h1]
    simp (disch := omega) only [slideS₀, of_apply, Fin.val_castSucc, if_pos, if_neg]
    norm_num
  by_cases h2 : (j : ℕ) + 1 = i
  · rw [hB.skewSymmetrization_eq_neg_sqrt (hp.2 j i h2), diagramWeight_comm, hp1 j i h2]
    simp (disch := omega) only [slideS₀, of_apply, Fin.val_castSucc, if_pos, if_neg]
    norm_num
  have h0 : B (p i) (p j) = 0 := hB.apply_eq_zero_of_not_adj fun h => by
    by_cases hij : i = j
    · subst hij
      exact h.1 rfl
    · exact ((hp.1.2.2 i j hij).1 h).elim h1 h2
  rw [hB.skewSymmetrization_eq_zero h0]
  simp (disch := omega) only [slideS₀, of_apply, Fin.val_castSucc, if_pos, if_neg]

/-- The skew-symmetrization of the initial diagram of the sliding triangle, read along
`(p₁, …, p_m, u)`, is `slideS₀`. -/
private theorem skewSymmetrization_snoc_eq_slideS₀ {m : ℕ}
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hB : SkewSymmetrizable B)
    {p : Fin m → Fin (m + 1)} {u : Fin (m + 1)} (hp : IsLinearlyOrientedPath B p)
    (hp1 : ∀ i j : Fin m, (i : ℕ) + 1 = j → diagramWeight B (p i) (p j) = 1)
    {a a' : Fin m} (ha : (a : ℕ) + 1 = a')
    (hadj : ∀ i, (diagramGraph B).Adj u (p i) ↔ i = a ∨ i = a')
    (hua' : 0 < B (p a') u) (hua : 0 < B u (p a)) (hwa : diagramWeight B u (p a) = 2)
    (hwa' : diagramWeight B u (p a') = 2) (α β : Fin (m + 1)) :
    skewSymmetrization (B.map (Int.cast : ℤ → ℝ)) (Fin.snoc (α := fun _ => Fin (m + 1)) p u α)
      (Fin.snoc (α := fun _ => Fin (m + 1)) p u β) = slideS₀ m a α β := by
  have heC : ∀ i, Fin.snoc (α := fun _ => Fin (m + 1)) p u (Fin.castSucc i) = p i :=
    fun i => Fin.snoc_castSucc (α := fun _ => _) ..
  have heL : Fin.snoc (α := fun _ => Fin (m + 1)) p u (Fin.last m) = u :=
    Fin.snoc_last (α := fun _ => _) ..
  induction α using Fin.lastCases with
  | last =>
    induction β using Fin.lastCases with
    | last =>
      rw [heL, hB.skewSymmetrization_eq_zero (hB.diag_eq_zero u)]
      simp (disch := omega) only [slideS₀, of_apply, Fin.val_last, ↓reduceIte, if_neg]
    | cast j =>
      rw [heL, heC, skewSymmetrization_apply_eq_slideS₀_last_castSucc hB ha hadj hua' hua hwa hwa']
  | cast i =>
    induction β using Fin.lastCases with
    | last =>
      rw [heL, heC, skewSymmetrization_apply_eq_slideS₀_castSucc_last hB ha hadj hua' hua hwa hwa']
    | cast j => rw [heC, heC, skewSymmetrization_apply_eq_slideS₀_castSucc_castSucc hB hp hp1]

/-- Mutating the initial diagram of the sliding triangle along `u, p_{a+1}, …, p_{m-1}` gives
`Δ_{m-1}`, read on positions. -/
private theorem submatrix_skewSymmetrization_matrixMutationList_eq_slideS {m : ℕ}
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hB : SkewSymmetrizable B)
    {p : Fin m → Fin (m + 1)} {u : Fin (m + 1)} {a : Fin m} (ha : (a : ℕ) + 1 < m)
    {π : Equiv.Perm (Fin (m + 1))} (hπC : ∀ i, π (Fin.castSucc i) = p i)
    (hπL : π (Fin.last m) = u)
    (hS₀ : (skewSymmetrization (B.map (Int.cast : ℤ → ℝ))).submatrix π π = slideS₀ m a) :
    (skewSymmetrization ((matrixMutationList le_rfl B
      (u :: ((List.finRange m).filter (fun i => a < i)).map p)).map
        (Int.cast : ℤ → ℝ))).submatrix π π = slideS m (m - 1) := by
  have hs : u :: ((List.finRange m).filter (fun i => a < i)).map p =
      (Fin.last m :: ((List.finRange m).filter (fun i => a < i)).map Fin.castSucc).map π := by
    rw [List.map_cons, List.map_map, hπL]
    congr 2
    funext i
    exact (hπC i).symm
  rw [skewSymmetrization_map_matrixMutationList hB, hs, ← matrixMutationList_submatrix,
    hS₀, matrixMutationList_cons, matrixMutation_slideS₀ ha,
    matrixMutationList_slideS (m - 1 - a) (by omega) _
      (by rw [map_val_filter_finRange_lt]; congr 1; omega),
    show (a : ℕ) + (m - 1 - a) = m - 1 by omega]

/-- A matrix with an enumeration `(e₀, …, e_m)` of its indices, in which consecutive indices
are exactly the adjacent ones and the weights are `(1, …, 1, 2)`, has Dynkin shape `B_{m+1}`. -/
private theorem hasDynkinShape_B_of_adj_iff {m : ℕ} (hm : 2 ≤ m)
    {C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hC : SkewSymmetrizable C)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (hadj : ∀ α β : Fin (m + 1), α ≠ β →
      ((diagramGraph C).Adj (e α) (e β) ↔ (α : ℕ) + 1 = β ∨ (β : ℕ) + 1 = α))
    (hw : ∀ α β : Fin (m + 1), (α : ℕ) + 1 = β →
      diagramWeight C (e α) (e β) = if (β : ℕ) = m then 2 else 1) :
    HasDynkinShape C [DynkinSymbol.B (m + 1) (by omega)] := by
  let v : Fin (m + 1) ≃ Fin (m + 1) := Fin.revPerm.trans e
  have hv : ∀ i, v i = e (Fin.rev i) := fun _ => rfl
  refine hasDynkinShape_B_of_isInducedPath hC (by omega) (v := v) ⟨by omega, v.injective,
    fun i j hij => ?_⟩ fun i j hij => ?_
  · rw [hv, hv, hadj _ _ (Fin.rev_injective.ne hij), Fin.val_rev, Fin.val_rev]
    have := i.isLt
    have := j.isLt
    omega
  · rw [hv, hv, diagramWeight_comm, hw _ _ (by rw [Fin.val_rev, Fin.val_rev]; omega), Fin.val_rev]
    have := i.isLt
    split_ifs <;> omega

/-- **Sliding a doubled triangle along a path.** Let `m ≥ 2` and let `p₁, …, p_m, u` enumerate
`[1, m + 1]`, with `(p₁, …, p_m)` a linearly oriented induced path of `B` with all weights `1`,
and, for some `a`, the indices adjacent to `u` exactly `p_a` and `p_{a+1}`, with
`p_{a+1} → u → p_a` and both weights at `u` equal to `2`. Then for
`s = (u, p_{a+1}, p_{a+2}, …, p_m)`, the sequence `(p₁, …, p_m, u)` is a linearly oriented
induced path of `μ_s(B)` with weights `(1, …, 1, 2)`; consequently `B` is of Dynkin class
`B_{m+1}`. -/
@[cluster_algebras "lem_sliding_triangle"]
theorem isLinearlyOrientedPath_matrixMutationList_of_doubledTriangle {m : ℕ} (hm : 2 ≤ m)
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hB : SkewSymmetrizable B)
    {p : Fin m → Fin (m + 1)} {u : Fin (m + 1)} (hu : u ∉ Set.range p)
    (hp : IsLinearlyOrientedPath B p)
    (hp1 : ∀ i j : Fin m, (i : ℕ) + 1 = j → diagramWeight B (p i) (p j) = 1)
    {a a' : Fin m} (ha : (a : ℕ) + 1 = a')
    (hadj : ∀ i, (diagramGraph B).Adj u (p i) ↔ i = a ∨ i = a')
    (hua' : 0 < B (p a') u) (hua : 0 < B u (p a)) (hwa : diagramWeight B u (p a) = 2)
    (hwa' : diagramWeight B u (p a') = 2) :
    IsLinearlyOrientedPath
        (matrixMutationList le_rfl B (u :: ((List.finRange m).filter (fun i => a < i)).map p))
        (Fin.snoc (α := fun _ => Fin (m + 1)) p u) ∧
      (∀ i j : Fin (m + 1), (i : ℕ) + 1 = j →
        diagramWeight
            (matrixMutationList le_rfl B (u :: ((List.finRange m).filter (fun i => a < i)).map p))
            (Fin.snoc (α := fun _ => Fin (m + 1)) p u i)
            (Fin.snoc (α := fun _ => Fin (m + 1)) p u j) =
          if (j : ℕ) = m then 2 else 1) ∧
      IsOfDynkinClass B [DynkinSymbol.B (m + 1) (by omega)] := by
  have hm1 : (a : ℕ) + 1 < m := ha ▸ a'.isLt
  set e : Fin (m + 1) → Fin (m + 1) := Fin.snoc (α := fun _ => Fin (m + 1)) p u
  have heC : ∀ i, e (Fin.castSucc i) = p i := fun i => Fin.snoc_castSucc (α := fun _ => _) ..
  have heL : e (Fin.last m) = u := Fin.snoc_last (α := fun _ => _) ..
  have heinj : Function.Injective e := Fin.snoc_injective_of_injective hp.1.2.1 hu
  let π : Equiv.Perm (Fin (m + 1)) := Equiv.ofBijective e (Finite.injective_iff_bijective.1 heinj)
  have hS₀ : (skewSymmetrization (B.map (Int.cast : ℤ → ℝ))).submatrix π π = slideS₀ m a :=
    Matrix.ext fun α β =>
      skewSymmetrization_snoc_eq_slideS₀ hB hp hp1 ha hadj hua' hua hwa hwa' α β
  have hSC := submatrix_skewSymmetrization_matrixMutationList_eq_slideS hB hm1 (π := π) heC heL hS₀
  set s := u :: ((List.finRange m).filter (fun i => a < i)).map p
  set C := matrixMutationList le_rfl B s
  have hC : SkewSymmetrizable C := skewSymmetrizable_matrixMutationList hB s
  have hWA : ∀ α β : Fin (m + 1), (diagramWeight C (e α) (e β) : ℝ) = slideS m (m - 1) α β ^ 2 ∧
      (0 < C (e α) (e β) ↔ 0 < slideS m (m - 1) α β) := fun α β =>
    hC.diagramWeight_of_skewSymmetrization_eq (congrFun (congrFun hSC α) β)
  have hadjC : ∀ α β : Fin (m + 1), α ≠ β →
      ((diagramGraph C).Adj (e α) (e β) ↔ (α : ℕ) + 1 = β ∨ (β : ℕ) + 1 = α) := by
    intro α β hαβ
    rw [diagramGraph_adj, ← Nat.cast_pos (α := ℝ), (hWA α β).1]
    have := slideS_last_ne_zero (m := m) (by omega) α β
    exact ⟨fun h => by have := this.1 (sq_pos_iff.1 h.2); omega,
      fun h => ⟨heinj.ne hαβ, sq_pos_iff.2 (this.2 (by omega))⟩⟩
  have hwC : ∀ α β : Fin (m + 1), (α : ℕ) + 1 = β →
      diagramWeight C (e α) (e β) = if (β : ℕ) = m then 2 else 1 := by
    intro α β h
    have := (hWA α β).1
    rw [slideS_last_sq (by omega) h] at this
    split_ifs at this ⊢ <;> exact_mod_cast this
  exact ⟨⟨⟨by omega, heinj, hadjC⟩, fun α β h => (hWA α β).2.2 (slideS_last_pos (by omega) h)⟩,
    hwC, C, hasDynkinShape_B_of_adj_iff hm hC π hadjC hwC,
    (mutationEquiv_matrixMutationList B s).diagramEquiv⟩

/-! ### A square of type `F₄` with a pendant vertex -/

/-- A subdiagram `B^v` has the model `f` when its weights at positions `p < q` are `f p q`. -/
theorem isShapeOf_submatrix_of_lt {B : Matrix (Fin n) (Fin n) ℤ} {m : ℕ}
    {v : Fin m → Fin n} {f : ℕ → ℕ → ℕ}
    (h : ∀ p q : Fin m, p < q → diagramWeight B (v p) (v q) = f p q) :
    IsShapeOf (diagramWeight (B.submatrix v v)) m f := by
  refine ⟨Equiv.refl _, fun p q hpq => ?_⟩
  simp only [Equiv.refl_apply, orderedModel]
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · rw [if_pos (show (p : ℕ) < q from hlt)]
    exact h p q hlt
  · rw [if_neg (show ¬ (p : ℕ) < q from by omega)]
    exact (diagramWeight_comm _ _ _).trans (h q p hlt)

/-- A configuration with `y – a` of positive weight, `a – b` of weight `2`, `a – c` of weight
`1`, and no other pair among `y, a, b, c` adjacent, is not `2`-finite. -/
private theorem not_isTwoFinite_of_pendant {B : Matrix (Fin n) (Fin n) ℤ} {y a b c : Fin n}
    (hya : y ≠ a) (hyb : y ≠ b) (hyc : y ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hwya : 0 < diagramWeight B y a) (hwyb : diagramWeight B y b = 0)
    (hwyc : diagramWeight B y c = 0) (hwab : diagramWeight B a b = 2)
    (hwac : diagramWeight B a c = 1) (hwbc : diagramWeight B b c = 0) : ¬IsTwoFinite B := by
  intro hB
  have h3 := hB.diagramWeight_le_three y a
  have hc : diagramWeight B c a = 1 := (diagramWeight_comm _ _ _).trans hwac
  have hcb : diagramWeight B c b = 0 := (diagramWeight_comm _ _ _).trans hwbc
  have hcy : diagramWeight B c y = 0 := (diagramWeight_comm _ _ _).trans hwyc
  interval_cases hw : diagramWeight B y a
  · -- `B₃^{(1)}` on `(y, c, a, b)`
    have hinj : Function.Injective ![y, c, a, b] := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    refine not_isTwoFinite_of_isBAffineShape (k := 3) ⟨le_rfl, ?_⟩ (hB.submatrix ⟨_, hinj⟩)
    refine isShapeOf_submatrix_of_lt fun p q hpq => ?_
    fin_cases p <;> fin_cases q <;> simp_all [bAffineModel]
  · -- `C₂^{(1)}` on `(y, a, b)`
    have hinj : Function.Injective ![y, a, b] := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    refine not_isTwoFinite_of_isCAffineShape (k := 2) ⟨le_rfl, ?_⟩ (hB.submatrix ⟨_, hinj⟩)
    refine isShapeOf_submatrix_of_lt fun p q hpq => ?_
    fin_cases p <;> fin_cases q <;> simp_all [cAffineModel]
  · -- `G₂^{(1)}(2)` on `(y, a, b)`
    have hinj : Function.Injective ![y, a, b] := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    refine not_isTwoFinite_of_isG2AffineShape (a := 2) ⟨by norm_num, ?_⟩
      (hB.submatrix ⟨_, hinj⟩)
    refine isShapeOf_submatrix_of_lt fun p q hpq => ?_
    fin_cases p <;> fin_cases q <;> simp_all [g2AffineModel]

/-- **A square of type `F₄` with a pendant vertex is not `2`-finite.** If `(x₁, x₂, x₃, x₄)` is
a chordless cycle of `B` with weights `(2, 1, 2, 1)` or `(1, 2, 1, 2)` and `y` is adjacent to
exactly one of the `xᵢ`, then `B` is not `2`-finite. -/
@[cluster_algebras "lem_square_plus_vertex"]
theorem not_isTwoFinite_of_square_of_existsUnique_adj {B : Matrix (Fin n) (Fin n) ℤ}
    {x : Fin 4 → Fin n} (hx : IsChordlessCycle B x)
    (hw : cycleWeights B x = ![2, 1, 2, 1] ∨ cycleWeights B x = ![1, 2, 1, 2]) {y : Fin n}
    (hy : ∃! i, (diagramGraph B).Adj y (x i)) : ¬IsTwoFinite B := by
  obtain ⟨i, hi, huniq⟩ := hy
  have hadj : ∀ p q : Fin 4, p ≠ q →
      ((diagramGraph B).Adj (x p) (x q) ↔ q = finRotate 4 p ∨ p = finRotate 4 q) := hx.2.2
  have hxinj := hx.2.1
  have hyx : ∀ j, y ≠ x j := by
    rintro j rfl
    have h1 := huniq (finRotate 4 j) ((hadj j _ (by fin_cases j <;> decide)).2 (Or.inl rfl))
    have h2 := huniq ((finRotate 4).symm j)
      ((hadj j _ (by fin_cases j <;> decide)).2 (Or.inr (by simp)))
    have h3 : finRotate 4 (finRotate 4 j) = j := by rw [h1, ← h2]; simp
    fin_cases j <;> revert h3 <;> decide
  have hzero : ∀ j, j ≠ i → diagramWeight B y (x j) = 0 := fun j hj => by
    by_contra h
    exact hj (huniq j ⟨hyx j, Nat.pos_of_ne_zero h⟩)
  have hnon : ∀ p q : Fin 4, p ≠ q → q ≠ finRotate 4 p → p ≠ finRotate 4 q →
      diagramWeight B (x p) (x q) = 0 := fun p q hpq h1 h2 => by
    by_contra h
    exact ((hadj p q hpq).1 ⟨hxinj.ne hpq, Nat.pos_of_ne_zero h⟩).elim h1 h2
  set j := finRotate 4 i with hj
  set k := (finRotate 4).symm i with hk
  have hkj : diagramWeight B (x i) (x k) = cycleWeights B x k := by
    rw [diagramWeight_comm, cycleWeights, hk, Equiv.apply_symm_apply]
  have hfacts : ∀ i : Fin 4, finRotate 4 i ≠ i ∧ (finRotate 4).symm i ≠ i ∧
      finRotate 4 i ≠ (finRotate 4).symm i ∧
      (finRotate 4).symm i ≠ finRotate 4 (finRotate 4 i) := by decide
  obtain ⟨h1, h2, h3, h4⟩ := hfacts i
  have hjk : diagramWeight B (x j) (x k) = 0 :=
    hnon j k h3 h4 (by rwa [hk, Equiv.apply_symm_apply])
  have hcases : (cycleWeights B x i = 2 ∧ cycleWeights B x k = 1) ∨
      (cycleWeights B x i = 1 ∧ cycleWeights B x k = 2) := by
    rw [hk]
    fin_cases i <;> rcases hw with hw | hw <;> rw [hw] <;> decide
  have hyi := hi.2
  rcases hcases with ⟨hci, hck⟩ | ⟨hci, hck⟩
  · exact not_isTwoFinite_of_pendant (hyx i) (hyx j) (hyx k) (hxinj.ne h1.symm)
      (hxinj.ne h2.symm) (hxinj.ne h3) hyi (hzero j h1) (hzero k h2) hci (hkj.trans hck) hjk
  · exact not_isTwoFinite_of_pendant (hyx i) (hyx k) (hyx j) (hxinj.ne h2.symm)
      (hxinj.ne h1.symm) (hxinj.ne h3.symm) hyi (hzero k h2) (hzero j h1) (hkj.trans hck) hci
      (by rwa [diagramWeight_comm])

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.ExtendedFGE

/-!
# `2`-finite tree diagrams are Dynkin

A tree diagram with weights at most `3` either has the Dynkin shape of a single Dynkin symbol or
contains a subdiagram of an extended Dynkin shape; the latter are not `2`-finite, so a `2`-finite
tree diagram is Dynkin.

## Main results

* `ClusterAlgebras.IsTreeDiagram.hasDynkinShape_or_isExtendedDynkinShape`: a tree diagram with
  weights at most `3` has Dynkin shape or contains a subdiagram of extended Dynkin shape.
* `ClusterAlgebras.IsTwoFinite.hasDynkinShape_of_isTreeDiagram`: a `2`-finite tree diagram has
  Dynkin shape.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {N : ℕ}

section Graph

variable {V : Type*} {G : SimpleGraph V}

/-- **No chords in an acyclic graph.** Let `s` be injective on the positions `[0, M)`, and let
`A` be a symmetric relation on positions whose pairs are edges of `G` and which connects every
position to `root` (each position other than `root` is related to one of smaller rank `r`).
Then every edge of `G` between two positions is a pair of `A`: any other edge would close a
cycle. -/
private theorem model_of_adj (hG : G.IsAcyclic) {M : ℕ} {s : ℕ → V}
    (hs : ∀ i j, i < M → j < M → s i = s j → i = j) (A : ℕ → ℕ → Prop)
    (hA : ∀ p q, A p q → A q p) (hE : ∀ p q, p < M → q < M → A p q → G.Adj (s p) (s q))
    (root : ℕ) (r : ℕ → ℕ)
    (hpar : ∀ p, p < M → p ≠ root → ∃ q, q < M ∧ r q < r p ∧ A p q)
    {p q : ℕ} (hp : p < M) (hq : q < M) (hadj : G.Adj (s p) (s q)) : A p q := by
  by_contra hn
  have key : ∀ t, t < M → (G.deleteEdges {s(s p, s q)}).Reachable (s root) (s t) := by
    intro t
    induction h : r t using Nat.strong_induction_on generalizing t with
    | _ d ih =>
      intro ht
      by_cases htr : t = root
      · subst htr; rfl
      obtain ⟨t', ht', hr, hA'⟩ := hpar t ht htr
      refine (ih (r t') (h ▸ hr) t' rfl ht').trans (SimpleGraph.Adj.reachable ?_)
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨(hE t t' ht ht' hA').symm, ?_⟩
      rw [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hn (hs _ _ ht' hp h1 ▸ hs _ _ ht hq h2 ▸ hA _ _ hA')
      · exact hn (hs _ _ ht' hq h1 ▸ hs _ _ ht hp h2 ▸ hA')
  exact SimpleGraph.isBridge_iff.1 (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hG hadj)
    ((key p hp).symm.trans (key q hq))

/-- A set of vertices of a connected graph containing a vertex and closed under adjacency is
everything. -/
private theorem mem_of_closed (hG : G.Connected) {S : Set V} {x : V}
    (hx : x ∈ S) (hS : ∀ a b, a ∈ S → G.Adj a b → b ∈ S) (y : V) : y ∈ S := by
  obtain ⟨p⟩ := hG.preconnected x y
  induction p with
  | nil => exact hx
  | cons h p ih => exact ih (hS _ _ hx h)

/-- `z 0, z 1, …, z k` is a path of `G`: its vertices are pairwise distinct and consecutive
ones are adjacent. -/
private def IsSeqPath (G : SimpleGraph V) (z : ℕ → V) (k : ℕ) : Prop :=
  (∀ i j, i ≤ k → j ≤ k → z i = z j → i = j) ∧ ∀ i, i < k → G.Adj (z i) (z (i + 1))

/-- In an acyclic graph, two vertices of a path are adjacent iff their positions are
consecutive. -/
private theorem IsSeqPath.adj_iff (hG : G.IsAcyclic) {z : ℕ → V} {k : ℕ}
    (hz : IsSeqPath G z k) {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k) :
    G.Adj (z i) (z j) ↔ i + 1 = j ∨ j + 1 = i := by
  refine ⟨model_of_adj hG (M := k + 1) (fun a b ha hb => hz.1 a b (by omega) (by omega))
    (fun p q => p + 1 = q ∨ q + 1 = p) (fun p q h => h.symm)
    (fun p q hp hq h => by
      rcases h with rfl | rfl
      · exact hz.2 p (by omega)
      · exact (hz.2 q (by omega)).symm)
    0 id (fun p hp hp0 => ⟨p - 1, by omega, by simp only [id]; omega, by omega⟩)
    (by omega) (by omega), ?_⟩
  rintro (rfl | rfl)
  · exact hz.2 i (by omega)
  · exact (hz.2 j (by omega)).symm

/-- Distinct positions of a path carry distinct vertices. -/
private theorem IsSeqPath.ne {z : ℕ → V} {k : ℕ} (hz : IsSeqPath G z k) {i j : ℕ} (hi : i ≤ k)
    (hj : j ≤ k) (hij : i ≠ j) : z i ≠ z j := fun h => hij (hz.1 i j hi hj h)

/-- An initial segment of a path is a path. -/
private theorem IsSeqPath.mono {z : ℕ → V} {k : ℕ} (hz : IsSeqPath G z k) {l : ℕ} (hl : l ≤ k) :
    IsSeqPath G z l :=
  ⟨fun i j hi hj h => hz.1 i j (by omega) (by omega) h, fun i hi => hz.2 i (by omega)⟩

/-- A final segment of a path is a path. -/
private theorem IsSeqPath.shift {z : ℕ → V} {k : ℕ} (hz : IsSeqPath G z k) {a : ℕ} (ha : a ≤ k) :
    IsSeqPath G (fun t => z (a + t)) (k - a) :=
  ⟨fun i j hi hj h => Nat.add_left_cancel (hz.1 _ _ (by omega) (by omega) h),
    fun i hi => by simpa [Nat.add_assoc] using hz.2 (a + i) (by omega)⟩

/-- A path read backwards is a path. -/
private theorem IsSeqPath.reverse {z : ℕ → V} {k : ℕ} (hz : IsSeqPath G z k) :
    IsSeqPath G (fun t => z (k - t)) k :=
  ⟨fun i j hi hj h => by have := hz.1 _ _ (by omega) (by omega) h; omega,
    fun i hi => by
      have := (hz.2 (k - (i + 1)) (by omega)).symm
      rwa [show k - (i + 1) + 1 = k - i by omega] at this⟩

/-- A path extends by a vertex off it adjacent to its last vertex. -/
private theorem IsSeqPath.snoc {z : ℕ → V} {k : ℕ} (hz : IsSeqPath G z k) {b : V}
    (hb : ∀ i, i ≤ k → z i ≠ b) (hadj : G.Adj (z k) b) :
    IsSeqPath G (fun t => if t ≤ k then z t else b) (k + 1) := by
  refine ⟨fun i j hi hj h => ?_, fun i hi => ?_⟩
  · by_cases hik : i ≤ k <;> by_cases hjk : j ≤ k <;> simp only [hik, hjk, if_true, if_false] at h
    · exact hz.1 i j hik hjk h
    · exact absurd h (hb i hik)
    · exact absurd h.symm (hb j hjk)
    · omega
  · by_cases hik : i + 1 ≤ k
    · simp only [show i ≤ k by omega, hik, if_true]
      exact hz.2 i hik
    · simp only [show i ≤ k by omega, hik, if_true, if_false]
      rwa [show i = k by omega]

/-- A path extends by a vertex off it adjacent to its first vertex. -/
private theorem IsSeqPath.cons {z : ℕ → V} {k : ℕ} (hz : IsSeqPath G z k) {a : V}
    (ha : ∀ i, i ≤ k → z i ≠ a) (hadj : G.Adj a (z 0)) :
    IsSeqPath G (fun t => if t = 0 then a else z (t - 1)) (k + 1) := by
  refine ⟨fun i j hi hj h => ?_, fun i hi => ?_⟩
  · by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0 <;>
      simp only [hi0, hj0, if_true, if_false] at h
    · omega
    · exact absurd h.symm (ha _ (by omega))
    · exact absurd h (ha _ (by omega))
    · have := hz.1 _ _ (by omega) (by omega) h
      omega
  · by_cases hi0 : i = 0
    · subst hi0
      simpa using hadj
    · simp only [hi0, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      have := hz.2 (i - 1) (by omega)
      rwa [show i - 1 + 1 = i by omega] at this

/-- In a connected graph, any two vertices are joined by a path. -/
private theorem exists_isSeqPath (hG : G.Connected) (u v : V) :
    ∃ z k, IsSeqPath G z k ∧ z 0 = u ∧ z k = v := by
  classical
  obtain ⟨p, hp⟩ := (hG.preconnected u v).some.toPath
  exact ⟨p.getVert, p.length, ⟨fun i j hi hj h => hp.getVert_injOn hi hj h,
    fun i hi => p.adj_getVert_succ hi⟩, p.getVert_zero, p.getVert_length⟩

/-- At most two distinct neighbours. -/
private def AtMostTwoNeighbors (G : SimpleGraph V) (x : V) : Prop :=
  ∀ a b c, G.Adj x a → G.Adj x b → G.Adj x c → a = b ∨ a = c ∨ b = c

/-- In an acyclic graph, the last vertex of a path whose neighbours all lie on the path is
adjacent only to the previous one. -/
private theorem IsSeqPath.eq_of_adj_last (hG : G.IsAcyclic) {z : ℕ → V} {k : ℕ}
    (hz : IsSeqPath G z k) (hend : ∀ w, G.Adj (z k) w → ∃ i, i ≤ k ∧ z i = w) {w : V}
    (hw : G.Adj (z k) w) : w = z (k - 1) := by
  obtain ⟨i, hi, rfl⟩ := hend w hw
  rcases (hz.adj_iff hG le_rfl hi).1 hw with h | h
  · omega
  · rw [show k - 1 = i by omega]

/-- An interior vertex of a path with at most two neighbours is adjacent only to its two
neighbours on the path. -/
private theorem IsSeqPath.eq_of_adj_interior {z : ℕ → V} {k : ℕ} (hz : IsSeqPath G z k)
    {t : ℕ} (ht0 : 0 < t) (htk : t < k) (hdeg : AtMostTwoNeighbors G (z t)) {w : V}
    (hw : G.Adj (z t) w) : w = z (t - 1) ∨ w = z (t + 1) := by
  have h1 : G.Adj (z t) (z (t - 1)) := by
    have := hz.2 (t - 1) (by omega)
    rw [show t - 1 + 1 = t by omega] at this
    exact this.symm
  rcases hdeg _ _ _ h1 (hz.2 t htk) hw with h | h | h
  · exact absurd h (hz.ne (by omega) (by omega) (by omega))
  · exact Or.inl h.symm
  · exact Or.inr h.symm

end Graph

section FinGraph

variable {G : SimpleGraph (Fin N)}

/-- A path in a graph on `N` vertices has length less than `N`. -/
private theorem IsSeqPath.lt {z : ℕ → Fin N} {k : ℕ} (hz : IsSeqPath G z k) : k < N := by
  have := Fintype.card_le_of_injective (fun i : Fin (k + 1) => z i)
    (fun i j h => Fin.ext (hz.1 i j (by omega) (by omega) h))
  simp only [Fintype.card_fin] at this
  omega

/-- Every path extends, keeping its first `k + 1` vertices, to a path whose last vertex has
all its neighbours on the path. -/
private theorem IsSeqPath.exists_maximal {z : ℕ → Fin N} {k : ℕ} (hz : IsSeqPath G z k) :
    ∃ z' k', k ≤ k' ∧ (∀ t, t ≤ k → z' t = z t) ∧ IsSeqPath G z' k' ∧
      ∀ w, G.Adj (z' k') w → ∃ i, i ≤ k' ∧ z' i = w := by
  classical
  induction h : N - k using Nat.strong_induction_on generalizing z k with
  | _ d ih =>
    by_cases hc : ∀ w, G.Adj (z k) w → ∃ i, i ≤ k ∧ z i = w
    · exact ⟨z, k, le_rfl, fun _ _ => rfl, hz, hc⟩
    push Not at hc
    obtain ⟨b, hb, hb'⟩ := hc
    have hlt := hz.lt
    obtain ⟨z'', k'', hk, hpre, hp, hend⟩ := ih (N - (k + 1)) (by omega) (hz.snoc hb' hb) rfl
    refine ⟨z'', k'', by omega, fun t ht => ?_, hp, hend⟩
    rw [hpre t (by omega)]
    simp [ht]

end FinGraph

section Weights

variable {B : Matrix (Fin N) (Fin N) ℤ}

/-- Distinct non-adjacent indices have weight `0`. -/
private theorem diagramWeight_eq_zero_of_not_adj {i j : Fin N} (hij : i ≠ j)
    (h : ¬(diagramGraph B).Adj i j) : diagramWeight B i j = 0 := by
  rw [diagramGraph_adj] at h
  push Not at h
  have := h hij
  omega

/-- The symmetric reading of a model `f` recorded on pairs `p < q`. -/
private theorem symm_model (f : ℕ → ℕ → ℕ) (p q : ℕ) :
    (if p < q then f p q else f q p) = (if q < p then f q p else f p q) := by
  rcases lt_trichotomy p q with h | rfl | h
  · simp [h, not_lt_of_gt h]
  · rfl
  · simp [h, not_lt_of_gt h]

/-- **Weights of a configuration in a tree diagram.** If the positions `[0, M)` of an injective
family `s` of indices of a tree diagram are connected by the pairs of positive model weight
`f`, and the weights of `B` agree with `f` on those pairs, then they agree with `f` on all
pairs: an additional edge would close a cycle. -/
private theorem diagramWeight_eq_model (hT : IsTreeDiagram B) {M : ℕ} {s : ℕ → Fin N}
    (hs : ∀ i j, i < M → j < M → s i = s j → i = j) (f : ℕ → ℕ → ℕ)
    (hE : ∀ p q, p < q → q < M → 0 < f p q → diagramWeight B (s p) (s q) = f p q)
    (root : ℕ) (r : ℕ → ℕ)
    (hpar : ∀ p, p < M → p ≠ root → ∃ q, q < M ∧ r q < r p ∧
      0 < (if p < q then f p q else f q p)) :
    ∀ p q, p < q → q < M → diagramWeight B (s p) (s q) = f p q := by
  intro p q hpq hq
  by_cases hf : 0 < f p q
  · exact hE p q hpq hq hf
  have hne : s p ≠ s q := fun h => absurd (hs p q (by omega) hq h) (by omega)
  rw [show f p q = 0 by omega]
  refine diagramWeight_eq_zero_of_not_adj hne fun hadj => hf ?_
  have := model_of_adj (G := diagramGraph B) hT.isAcyclic hs
    (fun a b => a ≠ b ∧ 0 < (if a < b then f a b else f b a))
    (fun a b h => ⟨h.1.symm, by rw [← symm_model]; exact h.2⟩)
    (fun a b ha hb h => by
      have hab : s a ≠ s b := fun h' => h.1 (hs a b ha hb h')
      refine ⟨hab, ?_⟩
      rcases lt_or_gt_of_ne h.1 with h' | h'
      · have h2 := h.2
        simp only [h', if_true] at h2
        rwa [hE a b h' hb h2]
      · have h2 := h.2
        simp only [not_lt_of_gt h', if_false] at h2
        rwa [diagramWeight_comm, hE b a h' ha h2])
    root r (fun a ha har => by
      obtain ⟨b, hb, hr, h⟩ := hpar a ha har
      exact ⟨b, hb, hr, by rintro rfl; exact hr.false, h⟩) (by omega) hq hadj
  simpa [hpq] using this.2

/-- A configuration with the weights of a model gives a subdiagram of that shape. -/
private theorem exists_embedding_isShapeOf {M : ℕ} {s : ℕ → Fin N}
    (hs : ∀ i j, i < M → j < M → s i = s j → i = j) (f : ℕ → ℕ → ℕ)
    (h : ∀ p q, p < q → q < M → diagramWeight B (s p) (s q) = f p q) :
    ∃ v : Fin M ↪ Fin N, IsShapeOf (diagramWeight (B.submatrix v v)) M f := by
  refine ⟨⟨fun i => s i, fun i j hij => Fin.ext (hs i j i.2 j.2 hij)⟩, Equiv.refl _,
    fun p q hpq => ?_⟩
  simp only [Equiv.refl_apply, orderedModel, diagramWeight, Function.Embedding.coeFn_mk,
    submatrix_apply]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hpq) with h' | h'
  · simp only [h', if_true]
    exact h p q h' q.2
  · simp only [not_lt_of_gt h', if_false]
    rw [← h q p h' p.2, diagramWeight, mul_comm]

/-- A configuration with the weights of a model and meeting every index makes `B` of that
shape. -/
private theorem isShapeOf_of_surjective {M : ℕ} {s : ℕ → Fin N}
    (hs : ∀ i j, i < M → j < M → s i = s j → i = j) (hsurj : ∀ x, ∃ i, i < M ∧ s i = x)
    (f : ℕ → ℕ → ℕ) (h : ∀ p q, p < q → q < M → diagramWeight B (s p) (s q) = f p q) :
    M = N ∧ IsShapeOf (diagramWeight B) M f := by
  have hbij : Function.Bijective (fun i : Fin M => s i) :=
    ⟨fun i j hij => Fin.ext (hs i j i.2 j.2 hij), fun x => by
      obtain ⟨i, hi, rfl⟩ := hsurj x
      exact ⟨⟨i, hi⟩, rfl⟩⟩
  refine ⟨by simpa using Fintype.card_congr (Equiv.ofBijective _ hbij), Equiv.ofBijective _ hbij,
    fun p q hpq => ?_⟩
  simp only [Equiv.ofBijective_apply, orderedModel]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hpq) with h' | h'
  · simp only [h', if_true]
    exact h p q h' q.2
  · simp only [not_lt_of_gt h', if_false]
    rw [← h q p h' p.2, diagramWeight_comm]

/-- A path of a tree diagram with the weights of a path model gives a subdiagram of that
shape. -/
private theorem exists_embedding_isShapeOf_path (hT : IsTreeDiagram B) {z : ℕ → Fin N} {k : ℕ}
    (hz : IsSeqPath (diagramGraph B) z k) (f : ℕ → ℕ → ℕ)
    (hf : ∀ p q, p < q → q ≤ k → f p q = if p + 1 = q then diagramWeight B (z p) (z q) else 0) :
    ∃ v : Fin (k + 1) ↪ Fin N, IsShapeOf (diagramWeight (B.submatrix v v)) (k + 1) f := by
  refine exists_embedding_isShapeOf (fun i j hi hj h => hz.1 i j (by omega) (by omega) h) f
    fun p q hpq hq => ?_
  rw [hf p q hpq (by omega)]
  split_ifs with h
  · rfl
  · refine diagramWeight_eq_zero_of_not_adj (hz.ne (by omega) (by omega) (by omega)) ?_
    rw [hz.adj_iff hT.isAcyclic (by omega) (by omega)]
    omega

/-- A path of a tree diagram through all indices is an induced path. -/
private theorem exists_isInducedPath (hT : IsTreeDiagram B) {z : ℕ → Fin N}
    (hz : IsSeqPath (diagramGraph B) z (N - 1)) (hN : 1 ≤ N) :
    ∃ v : Fin N ≃ Fin N, (∀ i, v i = z i) ∧ IsInducedPath B v := by
  have hinj : Function.Injective (fun i : Fin N => z i) :=
    fun i j hij => Fin.ext (hz.1 i j (by omega) (by omega) hij)
  have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, rfl⟩
  refine ⟨Equiv.ofBijective _ hbij, fun i => rfl, hN, (Equiv.ofBijective _ hbij).injective,
    fun p q hpq => ?_⟩
  simp only [Equiv.ofBijective_apply]
  exact hz.adj_iff hT.isAcyclic (by omega) (by omega)

end Weights

section Cases

variable {B : Matrix (Fin N) (Fin N) ℤ}

/-- Three distinct vertices `u, v, y` with `u ∼ v ∼ y` form a path. -/
private theorem isSeqPath_three {V : Type*} {G : SimpleGraph V} {u v y : V} (huy : u ≠ y)
    (huv : G.Adj u v) (hvy : G.Adj v y) :
    IsSeqPath G (fun t => if t = 0 then u else if t = 1 then v else y) 2 := by
  have h1 := huv.ne
  have h2 := hvy.ne
  refine ⟨fun i j hi hj h => ?_, fun i hi => ?_⟩
  · interval_cases i <;> interval_cases j <;> simp_all [eq_comm]
  · interval_cases i <;> simp_all

/-- Three distinct indices force `N ≥ 3`. -/
private theorem three_le_of_ne {x y z : Fin N} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    3 ≤ N := by
  have := x.2; have := y.2; have := z.2
  have := Fin.val_ne_of_ne hxy; have := Fin.val_ne_of_ne hxz; have := Fin.val_ne_of_ne hyz
  omega

/-- **Weight `3`**: an edge `{u, v}` of weight `3` with a further edge `{v, y}` gives
`(u, v, y)` of shape `G₂^{(1)}(w(v, y))`. -/
private theorem extended_of_weight_three_aux (hT : IsTreeDiagram B)
    (hw : ∀ i j, diagramWeight B i j ≤ 3) {u v y : Fin N} (huv : (diagramGraph B).Adj u v)
    (h3 : diagramWeight B u v = 3) (hvy : (diagramGraph B).Adj v y) (huy : u ≠ y) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix e e)) := by
  obtain ⟨e, he⟩ := exists_embedding_isShapeOf_path hT (isSeqPath_three huy huv hvy)
    (g2AffineModel (diagramWeight B v y)) fun p q hpq hq => by
      interval_cases q <;> interval_cases p <;> simp [g2AffineModel, h3]
  refine ⟨3, e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, ?_, he⟩))))))⟩
  have := hvy.2
  have := hw v y
  omega

/-- **Weight `3`** with `N ≥ 3`: a subdiagram of shape `G₂^{(1)}(a)`. -/
private theorem extended_of_weight_three (hT : IsTreeDiagram B)
    (hw : ∀ i j, diagramWeight B i j ≤ 3) (hN : 3 ≤ N) {u v : Fin N}
    (huv : (diagramGraph B).Adj u v) (h3 : diagramWeight B u v = 3) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix e e)) := by
  by_cases hv : ∃ y, (diagramGraph B).Adj v y ∧ u ≠ y
  · obtain ⟨y, hvy, huy⟩ := hv
    exact extended_of_weight_three_aux hT hw huv h3 hvy huy
  by_cases hu : ∃ y, (diagramGraph B).Adj u y ∧ v ≠ y
  · obtain ⟨y, huy, hvy⟩ := hu
    exact extended_of_weight_three_aux hT hw huv.symm (by rw [diagramWeight_comm, h3]) huy hvy
  push Not at hu hv
  have hall := mem_of_closed hT.connected (S := {x | x = u ∨ x = v}) (Or.inl rfl)
    (fun a b ha hab => by
      rcases ha with rfl | rfl
      · exact Or.inr (hu b hab).symm
      · exact Or.inl (hv b hab).symm)
  have h0 := hall ⟨0, by omega⟩
  have h1 := hall ⟨1, by omega⟩
  have h2 := hall ⟨2, by omega⟩
  simp only [Set.mem_setOf_eq, Fin.ext_iff] at h0 h1 h2
  omega

/-- The other endpoint of an edge `{a, b}` of weight `2` at one of its endpoints `x`. -/
private theorem other_endpoint {a b x : Fin N} (hab : (diagramGraph B).Adj a b)
    (h2 : diagramWeight B a b = 2) (hx : x = a ∨ x = b) :
    ∃ x', (x' = a ∨ x' = b) ∧ (diagramGraph B).Adj x' x ∧ diagramWeight B x' x = 2 ∧
      s(x', x) = s(a, b) := by
  rcases hx with rfl | rfl
  · exact ⟨b, Or.inr rfl, hab.symm, by rw [diagramWeight_comm, h2], Sym2.eq_swap⟩
  · exact ⟨a, Or.inl rfl, hab, h2, rfl⟩

/-- Two distinct edges of weight `2` lie on a path whose first and last edges they are. -/
private theorem exists_path_weight_two_ends (hT : IsTreeDiagram B) {a b c d : Fin N}
    (hab : (diagramGraph B).Adj a b) (hcd : (diagramGraph B).Adj c d)
    (h1 : diagramWeight B a b = 2) (h2 : diagramWeight B c d = 2) (hne : s(a, b) ≠ s(c, d)) :
    ∃ k, 2 ≤ k ∧ ∃ z, IsSeqPath (diagramGraph B) z k ∧ diagramWeight B (z 0) (z 1) = 2 ∧
      diagramWeight B (z (k - 1)) (z k) = 2 := by
  classical
  have hQ : ∃ L, ∃ x y z, (x = a ∨ x = b) ∧ (y = c ∨ y = d) ∧
      IsSeqPath (diagramGraph B) z L ∧ z 0 = x ∧ z L = y := by
    obtain ⟨z, L, hz, h0, hL⟩ := exists_isSeqPath hT.connected a c
    exact ⟨L, a, c, z, Or.inl rfl, Or.inl rfl, hz, h0, hL⟩
  obtain ⟨x, y, z, hx, hy, hz, hz0, hzL⟩ := Nat.find_spec hQ
  set L := Nat.find hQ
  obtain ⟨x', hx', hx'x, hwx, hsx⟩ := other_endpoint hab h1 hx
  obtain ⟨y', hy', hy'y, hwy, hsy⟩ := other_endpoint hcd h2 hy
  have hxz : ∀ i, i ≤ L → z i ≠ x' := by
    intro i hi hzi
    have hi0 : i ≠ 0 := by rintro rfl; exact hx'x.ne (hzi.symm.trans hz0)
    refine Nat.find_min hQ (m := L - i) (by omega) ⟨x', y, fun t => z (i + t), hx', hy,
      hz.shift hi, by simpa using hzi, ?_⟩
    simpa [show i + (L - i) = L by omega] using hzL
  have hyz : ∀ i, i ≤ L → z i ≠ y' := by
    intro i hi hzi
    have hiL : i ≠ L := by rintro rfl; exact hy'y.ne (hzi.symm.trans hzL)
    exact Nat.find_min hQ (m := i) (by omega) ⟨x, y', z, hx, hy', hz.mono hi, hz0, hzi⟩
  have hxy : x' ≠ y' := by
    intro he
    have hL0 : L = 0 := Nat.eq_zero_of_le_zero (Nat.find_min' hQ ⟨x', y', fun _ => x', hx', hy',
      ⟨fun i j hi hj _ => by omega, fun i hi => by omega⟩, rfl, he⟩)
    have : x = y := by rw [← hz0, ← hzL, hL0]
    exact hne (by rw [← hsx, ← hsy, he, this])
  have hz1 := hz.snoc hyz (by rw [hzL]; exact hy'y.symm)
  have hz2 := hz1.cons (a := x') (fun i hi => by
      by_cases h : i ≤ L
      · simpa only [h, if_true] using hxz i h
      · simpa only [h, if_false] using hxy.symm)
    (by simp only [Nat.zero_le, if_true, hz0]; exact hx'x)
  refine ⟨L + 2, by omega, _, hz2, ?_, ?_⟩
  · simp [hz0, hwx]
  · simp only [show L + 2 - 1 = L + 1 by omega, Nat.add_one_ne_zero, if_false, le_rfl,
      if_true, show L + 1 - 1 = L by omega, hzL]
    rw [diagramWeight_comm]
    simpa [diagramWeight_comm] using hwy

/-- **Two edges of weight `2`**: a shortest path whose first and last edges have weight `2` is
of shape `C_k^{(1)}`. -/
private theorem extended_of_two_weight_two (hT : IsTreeDiagram B)
    (hw : ∀ i j, diagramWeight B i j ≤ 3)
    (h3 : ¬(3 ≤ N ∧ ∃ u v, (diagramGraph B).Adj u v ∧ diagramWeight B u v = 3))
    {a b c d : Fin N} (hab : (diagramGraph B).Adj a b) (hcd : (diagramGraph B).Adj c d)
    (h1 : diagramWeight B a b = 2) (h2 : diagramWeight B c d = 2) (hne : s(a, b) ≠ s(c, d)) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix e e)) := by
  classical
  have hP := exists_path_weight_two_ends hT hab hcd h1 h2 hne
  obtain ⟨hk2, z, hz, hz0, hzk⟩ := Nat.find_spec hP
  set k := Nat.find hP
  have hN : 3 ≤ N := three_le_of_ne (hz.ne (i := 0) (j := 1) (by omega) (by omega) (by omega))
    (hz.ne (i := 0) (j := 2) (by omega) (by omega) (by omega))
    (hz.ne (i := 1) (j := 2) (by omega) (by omega) (by omega))
  have hinner : ∀ t, 1 ≤ t → t + 2 ≤ k → diagramWeight B (z t) (z (t + 1)) = 1 := by
    intro t ht1 ht2
    have hadj := hz.2 t (by omega)
    have h0 := hadj.2
    have h3' : diagramWeight B (z t) (z (t + 1)) ≠ 3 := fun h => h3 ⟨hN, _, _, hadj, h⟩
    have h2' : diagramWeight B (z t) (z (t + 1)) ≠ 2 := fun h =>
      Nat.find_min hP (m := t + 1) (by omega) ⟨by omega, z, hz.mono (by omega), hz0, by simpa⟩
    have := hw (z t) (z (t + 1))
    omega
  obtain ⟨e, he⟩ := exists_embedding_isShapeOf_path hT hz (cAffineModel k) fun p q hpq hq => by
    simp only [cAffineModel]
    by_cases hpq1 : p + 1 = q
    · subst hpq1
      simp only [hq, and_self, if_true]
      by_cases hp0 : p = 0
      · subst hp0; simp [hz0]
      by_cases hpk : p + 1 = k
      · simp only [hpk, or_true, if_true]
        rw [← hzk, show k - 1 = p by omega, ← hpk]
      · simp only [hp0, hpk, or_self, if_false]
        exact (hinner p (by omega) (by omega)).symm
    · simp [hpq1]
  exact ⟨k + 1, e, Or.inr (Or.inl ⟨k, hk2, he⟩)⟩

/-- Two of three distinct neighbours of `x` avoid a given vertex. -/
private theorem exists_two_neighbors_ne {V : Type*} {G : SimpleGraph V} {x n₁ n₂ n₃ : V}
    (h₁ : G.Adj x n₁) (h₂ : G.Adj x n₂) (h₃ : G.Adj x n₃) (h₁₂ : n₁ ≠ n₂) (h₁₃ : n₁ ≠ n₃)
    (h₂₃ : n₂ ≠ n₃) (t : V) : ∃ a b, G.Adj x a ∧ G.Adj x b ∧ a ≠ b ∧ a ≠ t ∧ b ≠ t := by
  by_cases ht₁ : n₁ = t
  · subst ht₁; exact ⟨n₂, n₃, h₂, h₃, h₂₃, h₁₂.symm, h₁₃.symm⟩
  by_cases ht₂ : n₂ = t
  · subst ht₂; exact ⟨n₁, n₃, h₁, h₃, h₁₃, ht₁, h₂₃.symm⟩
  · exact ⟨n₁, n₂, h₁, h₂, h₁₂, ht₁, ht₂⟩

/-- In an acyclic graph, a neighbour of the first vertex of a path other than the second
vertex is off the path. -/
private theorem IsSeqPath.ne_of_adj_first {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {z : ℕ → V} {k : ℕ} (hz : IsSeqPath G z k) {a : V} (ha : G.Adj (z 0) a) (ha1 : a ≠ z 1)
    (i : ℕ) (hi : i ≤ k) : z i ≠ a := by
  rintro rfl
  rcases Nat.lt_or_ge i 2 with h | h
  · interval_cases i
    · exact ha.ne rfl
    · exact ha1 rfl
  · have := (hz.adj_iff hG (Nat.zero_le _) hi).1 ha
    omega

/-- A shortest path from `x` to an edge `{p₀, q₀}` of weight `2`, continued along the edge. -/
private theorem exists_isSeqPath_to_edge (hT : IsTreeDiagram B) {p₀ q₀ : Fin N}
    (hpq : (diagramGraph B).Adj p₀ q₀) (hw₂ : diagramWeight B p₀ q₀ = 2) (x : Fin N) :
    ∃ L Y, IsSeqPath (diagramGraph B) Y (L + 1) ∧ Y 0 = x ∧ s(Y L, Y (L + 1)) = s(p₀, q₀) ∧
      diagramWeight B (Y L) (Y (L + 1)) = 2 := by
  classical
  have hQ : ∃ L, ∃ z y, (z = p₀ ∨ z = q₀) ∧ IsSeqPath (diagramGraph B) y L ∧ y 0 = x ∧
      y L = z := by
    obtain ⟨y, L, hy, h0, hL⟩ := exists_isSeqPath hT.connected x p₀
    exact ⟨L, p₀, y, Or.inl rfl, hy, h0, hL⟩
  obtain ⟨z, y, hz, hy, hy0, hyL⟩ := Nat.find_spec hQ
  set L := Nat.find hQ
  obtain ⟨z', -, hz'z, hwz, hsz⟩ := other_endpoint hpq hw₂ hz
  have hyz : ∀ i, i ≤ L → y i ≠ z' := by
    intro i hi hyi
    have hiL : i ≠ L := by rintro rfl; exact hz'z.ne (hyi.symm.trans hyL)
    have hz' : z' = p₀ ∨ z' = q₀ := by
      simpa using congrArg (fun e : Sym2 (Fin N) => z' ∈ e) hsz
    exact Nat.find_min hQ (m := i) (by omega) ⟨z', y, hz', hy.mono hi, hy0, hyi⟩
  have hY := hy.snoc hyz (by rw [hyL]; exact hz'z.symm)
  set Y := fun t => if t ≤ L then y t else z'
  have hYL : Y L = z := by simp [Y, hyL]
  have hYL1 : Y (L + 1) = z' := by simp [Y]
  refine ⟨L, Y, hY, by simp [Y, hy0], by rw [hYL, hYL1, ← hsz, Sym2.eq_swap], ?_⟩
  rwa [hYL, hYL1, diagramWeight_comm]

/-- Two distinct vertices `a, b` followed by a path avoiding them are pairwise distinct. -/
private theorem injOn_cons_cons {V : Type*} {G : SimpleGraph V} {Y : ℕ → V} {k M : ℕ}
    (hY : IsSeqPath G Y k) {a b : V} (hab : a ≠ b) (haY : ∀ i, i ≤ k → Y i ≠ a)
    (hbY : ∀ i, i ≤ k → Y i ≠ b) {S : ℕ → V} (hS0 : S 0 = a) (hS1 : S 1 = b)
    (hS : ∀ p, 2 ≤ p → S p = Y (p - 2)) (hM : M ≤ k + 3) :
    ∀ i j, i < M → j < M → S i = S j → i = j := by
  intro i j hi hj h
  rcases Nat.lt_or_ge i 2 with hi2 | hi2 <;> rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases i <;> interval_cases j
    · rfl
    · rw [hS0, hS1] at h; exact absurd h hab
    · rw [hS0, hS1] at h; exact absurd h.symm hab
    · rfl
  · interval_cases i
    · rw [hS0, hS j hj2] at h; exact absurd h.symm (haY _ (by omega))
    · rw [hS1, hS j hj2] at h; exact absurd h.symm (hbY _ (by omega))
  · interval_cases j
    · rw [hS0, hS i hi2] at h; exact absurd h (haY _ (by omega))
    · rw [hS1, hS i hi2] at h; exact absurd h (hbY _ (by omega))
  · rw [hS i hi2, hS j hj2] at h
    have := hY.1 _ _ (by omega) (by omega) h
    omega

/-- **A path `x = Y 0, …, Y (L + 1)` with weights `1, …, 1, 2` and two further neighbours `a, b`
of `x` off the path, with weight `1`**: a subdiagram of shape `B_{L+3}^{(1)}`. -/
private theorem extended_of_bAffine_config (hT : IsTreeDiagram B) {x a b : Fin N}
    {Y : ℕ → Fin N} {L : ℕ} (hY : IsSeqPath (diagramGraph B) Y (L + 1)) (hY0 : Y 0 = x)
    (hab : a ≠ b) (haY : ∀ i, i ≤ L + 1 → Y i ≠ a) (hbY : ∀ i, i ≤ L + 1 → Y i ≠ b)
    (hwa : diagramWeight B a x = 1) (hwb : diagramWeight B b x = 1)
    (hwY : ∀ t, t < L → diagramWeight B (Y t) (Y (t + 1)) = 1)
    (hwlast : diagramWeight B (Y L) (Y (L + 1)) = 2) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix e e)) := by
  obtain ⟨k, hk⟩ : ∃ k, k = L + 3 := ⟨_, rfl⟩
  set S : ℕ → Fin N := fun p => if p = 0 then a else if p = 1 then b else Y (p - 2)
  have hS0 : S 0 = a := rfl
  have hS1 : S 1 = b := rfl
  have hS : ∀ p, 2 ≤ p → S p = Y (p - 2) := fun p hp => by
    simp only [S, show p ≠ 0 by omega, show p ≠ 1 by omega, if_false]
  clear_value S
  have hinj := injOn_cons_cons (M := k + 1) hY hab haY hbY hS0 hS1 hS (by omega)
  have hmodel := diagramWeight_eq_model hT hinj (bAffineModel k)
    (fun p q hpq hq hf => by
      simp only [bAffineModel] at hf ⊢
      split_ifs at hf ⊢ with H1 H2
      · rcases H1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hp, rfl, hq'⟩
        · rw [hS0, hS 2 le_rfl]; simpa [hY0] using hwa
        · rw [hS1, hS 2 le_rfl]; simpa [hY0] using hwb
        · rw [hS p hp, hS (p + 1) (by omega), show p + 1 - 2 = p - 2 + 1 by omega]
          exact hwY _ (by omega)
      · obtain ⟨hp', hq'⟩ := H2
        rw [hp', hq', hS _ (by omega), hS _ (by omega), show k - 1 - 2 = L by omega,
          show k - 2 = L + 1 by omega]
        exact hwlast
      · omega)
    2 (fun p => if p < 2 then 1 else p - 2) (fun p hp hp2 => by
      rcases Nat.lt_or_ge p 2 with h | h
      · refine ⟨2, by omega, by simp [h], ?_⟩
        simp only [h, if_true, bAffineModel]
        interval_cases p <;> simp
      · refine ⟨p - 1, by omega, by simp [show ¬p < 2 by omega, show ¬p - 1 < 2 by omega]; omega,
          ?_⟩
        simp only [show ¬p < p - 1 by omega, if_false, bAffineModel]
        split_ifs <;> omega)
  obtain ⟨e, he⟩ := exists_embedding_isShapeOf hinj (bAffineModel k) hmodel
  exact ⟨k + 1, e, Or.inl ⟨k, by omega, he⟩⟩

/-- **One edge of weight `2` and a vertex `x` of degree at least `3`**: with the path from `x`
to the far endpoint of the edge, two further neighbours of `x` give a subdiagram of shape
`B_k^{(1)}`. -/
private theorem extended_of_weight_two_of_three_neighbors (hT : IsTreeDiagram B)
    (hw : ∀ i j, diagramWeight B i j ≤ 3)
    (h3 : ¬(3 ≤ N ∧ ∃ u v, (diagramGraph B).Adj u v ∧ diagramWeight B u v = 3))
    (h22 : ∀ a b c d, (diagramGraph B).Adj a b → (diagramGraph B).Adj c d →
      diagramWeight B a b = 2 → diagramWeight B c d = 2 → s(a, b) = s(c, d))
    {p₀ q₀ : Fin N} (hpq : (diagramGraph B).Adj p₀ q₀) (hw₂ : diagramWeight B p₀ q₀ = 2)
    {x n₁ n₂ n₃ : Fin N} (h₁ : (diagramGraph B).Adj x n₁) (h₂ : (diagramGraph B).Adj x n₂)
    (h₃ : (diagramGraph B).Adj x n₃) (h₁₂ : n₁ ≠ n₂) (h₁₃ : n₁ ≠ n₃) (h₂₃ : n₂ ≠ n₃) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix e e)) := by
  have hN := three_le_of_ne h₁₂ h₁₃ h₂₃
  obtain ⟨L, Y, hY, hY0, hYs, hwlast⟩ := exists_isSeqPath_to_edge hT hpq hw₂ x
  obtain ⟨a, b, ha, hb, hab, ha1, hb1⟩ := exists_two_neighbors_ne h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ (Y 1)
  have haY := hY.ne_of_adj_first hT.isAcyclic (by rw [hY0]; exact ha) ha1
  have hbY := hY.ne_of_adj_first hT.isAcyclic (by rw [hY0]; exact hb) hb1
  have hw1 : ∀ i j, (diagramGraph B).Adj i j → s(i, j) ≠ s(Y L, Y (L + 1)) →
      diagramWeight B i j = 1 := fun i j hij hne => by
    have := hij.2; have := hw i j
    have : diagramWeight B i j ≠ 3 := fun h => h3 ⟨hN, i, j, hij, h⟩
    have : diagramWeight B i j ≠ 2 := fun h => hne (by rw [h22 i j p₀ q₀ hij hpq h hw₂, hYs])
    omega
  have hwx : ∀ c, (diagramGraph B).Adj x c → (∀ i, i ≤ L + 1 → Y i ≠ c) →
      diagramWeight B c x = 1 := fun c hc hcY => hw1 c x hc.symm (by
    rw [Ne, Sym2.eq_iff]; rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hcY L (by omega) h.symm
    · exact hcY (L + 1) le_rfl h.symm)
  refine extended_of_bAffine_config hT hY hY0 hab haY hbY (hwx a ha haY) (hwx b hb hbY)
    (fun t ht => hw1 _ _ (hY.2 t (by omega)) ?_) hwlast
  rw [Ne, Sym2.eq_iff]; rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact absurd (hY.1 _ _ (by omega) (by omega) h) (by omega)
  · exact absurd (hY.1 _ _ (by omega) (by omega) h) (by omega)

/-- `diagramWeight_eq_model` when all edges have weight `1`. -/
private theorem diagramWeight_eq_model_of_unit (hT : IsTreeDiagram B)
    (hw1 : ∀ i j, (diagramGraph B).Adj i j → diagramWeight B i j = 1) {M : ℕ} {s : ℕ → Fin N}
    (hs : ∀ i j, i < M → j < M → s i = s j → i = j) (f : ℕ → ℕ → ℕ)
    (hf : ∀ p q, f p q ≤ 1)
    (hE : ∀ p q, p < q → q < M → 0 < f p q → (diagramGraph B).Adj (s p) (s q))
    (root : ℕ) (r : ℕ → ℕ)
    (hpar : ∀ p, p < M → p ≠ root → ∃ q, q < M ∧ r q < r p ∧
      0 < (if p < q then f p q else f q p)) :
    ∃ v : Fin M ↪ Fin N, IsShapeOf (diagramWeight (B.submatrix v v)) M f :=
  exists_embedding_isShapeOf hs f (diagramWeight_eq_model hT hs f (fun p q hpq hq h => by
    rw [hw1 _ _ (hE p q hpq hq h)]; have := hf p q; omega) root r hpar)

/-- **A vertex with four neighbours**, all weights `1`: a subdiagram of shape `D₄^{(1)}`. -/
private theorem extended_of_four_neighbors (hT : IsTreeDiagram B)
    (hw1 : ∀ i j, (diagramGraph B).Adj i j → diagramWeight B i j = 1)
    {o n₁ n₂ n₃ n₄ : Fin N} (h₁ : (diagramGraph B).Adj o n₁) (h₂ : (diagramGraph B).Adj o n₂)
    (h₃ : (diagramGraph B).Adj o n₃) (h₄ : (diagramGraph B).Adj o n₄) (h₁₂ : n₁ ≠ n₂)
    (h₁₃ : n₁ ≠ n₃) (h₁₄ : n₁ ≠ n₄) (h₂₃ : n₂ ≠ n₃) (h₂₄ : n₂ ≠ n₄) (h₃₄ : n₃ ≠ n₄) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix e e)) := by
  have := h₁.ne; have := h₂.ne; have := h₃.ne; have := h₄.ne
  obtain ⟨e, he⟩ := diagramWeight_eq_model_of_unit (M := 4 + 1) hT hw1
    (s := fun p => [n₁, n₂, o, n₃, n₄].getD p o)
    (fun i j hi hj h => by
      interval_cases i <;> interval_cases j <;> simp_all [eq_comm])
    (dAffineModel 4) (fun p q => by simp only [dAffineModel]; split_ifs <;> omega)
    (fun p q hpq hq hf => by
      interval_cases q <;> interval_cases p <;>
        simp only [dAffineModel, OfNat.one_ne_ofNat, and_false, zero_ne_one, and_self,
          nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, zero_add, Nat.reduceSub, Nat.one_le_ofNat,
          and_true, OfNat.zero_ne_ofNat, Nat.add_one_sub_one, or_self, ↓reduceIte,
          lt_self_iff_false, Std.le_refl, Nat.reduceEqDiff, or_false, Order.lt_one_iff,
          List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.getD_some, Nat.reduceLT,
          List.getElem_cons_succ, one_ne_zero, Nat.not_ofNat_le_one, or_true, Nat.one_lt_ofNat,
          Nat.succ_ne_self, Nat.reduceLeDiff, OfNat.ofNat_ne_one, Nat.lt_add_one] at hf ⊢ <;>
        first | exact h₁.symm | exact h₂.symm | exact h₃ | exact h₄)
    2 (fun p => if p = 2 then 0 else 1) (fun p hp hp2 => ⟨2, by omega, by simp [hp2],
      by interval_cases p <;> simp_all [dAffineModel]⟩)
  exact ⟨5, e, Or.inr (Or.inr (Or.inl ⟨4, le_rfl, he⟩))⟩

/-- In an acyclic graph, a vertex off a path of length at least `1` is not adjacent to both of
its ends. -/
private theorem IsSeqPath.not_adj_last_of_adj_first {V : Type*} {G : SimpleGraph V}
    (hG : G.IsAcyclic) {z : ℕ → V} {k : ℕ} (hz : IsSeqPath G z k) (hk : 1 ≤ k) {a : V}
    (ha : ∀ i, i ≤ k → z i ≠ a) (h0 : G.Adj a (z 0)) : ¬G.Adj a (z k) := by
  intro hk'
  have h := hz.cons ha h0
  have := ((h.adj_iff hG (i := 0) (j := k + 1) (by omega) le_rfl).1 (by simpa using hk'))
  omega

/-- Two vertices `a, b`, a path `y 0, …, y L` and two vertices `c, d`, all pairwise distinct,
listed one after the other, are pairwise distinct. -/
private theorem injOn_dAffine {V : Type*} {G : SimpleGraph V} {y : ℕ → V} {L : ℕ}
    (hy : IsSeqPath G y L) {a b c d : V} {S : ℕ → V} (hSa : S 0 = a) (hSb : S 1 = b)
    (hSy : ∀ p, 2 ≤ p → p ≤ L + 2 → S p = y (p - 2)) (hSc : S (L + 3) = c)
    (hSd : S (L + 4) = d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (haY : ∀ i, i ≤ L → y i ≠ a) (hbY : ∀ i, i ≤ L → y i ≠ b)
    (hcY : ∀ i, i ≤ L → y i ≠ c) (hdY : ∀ i, i ≤ L → y i ≠ d) :
    ∀ i j, i < L + 4 + 1 → j < L + 4 + 1 → S i = S j → i = j := by
  have key : ∀ p, p < L + 5 → (p = 0 ∧ S p = a) ∨ (p = 1 ∧ S p = b) ∨
      (2 ≤ p ∧ p ≤ L + 2 ∧ S p = y (p - 2)) ∨ (p = L + 3 ∧ S p = c) ∨ (p = L + 4 ∧ S p = d) := by
    intro p hp
    rcases (by omega : p = 0 ∨ p = 1 ∨ (2 ≤ p ∧ p ≤ L + 2) ∨ p = L + 3 ∨ p = L + 4) with
      rfl | rfl | ⟨h1, h2⟩ | rfl | rfl
    · exact Or.inl ⟨rfl, hSa⟩
    · exact Or.inr (Or.inl ⟨rfl, hSb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, hSy p h1 h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hSc⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hSd⟩)))
  intro i j hi hj h
  rcases key i hi with ⟨hi', hSi⟩ | ⟨hi', hSi⟩ | ⟨hi1, hi2, hSi⟩ | ⟨hi', hSi⟩ | ⟨hi', hSi⟩ <;>
  rcases key j hj with ⟨hj', hSj⟩ | ⟨hj', hSj⟩ | ⟨hj1, hj2, hSj⟩ | ⟨hj', hSj⟩ | ⟨hj', hSj⟩ <;>
  rw [hSi, hSj] at h <;>
  first
    | omega
    | exact absurd h ‹_›
    | exact absurd h.symm ‹_›
    | exact absurd h (haY _ (by omega))
    | exact absurd h.symm (haY _ (by omega))
    | exact absurd h (hbY _ (by omega))
    | exact absurd h.symm (hbY _ (by omega))
    | exact absurd h (hcY _ (by omega))
    | exact absurd h.symm (hcY _ (by omega))
    | exact absurd h (hdY _ (by omega))
    | exact absurd h.symm (hdY _ (by omega))
    | (have := hy.1 _ _ (by omega) (by omega) h; omega)

/-- Every position of the model `D_{L+4}^{(1)}` but `2` is adjacent to a position of smaller
rank. -/
private theorem dAffineModel_exists_lower (L p : ℕ) (hp : p < L + 4 + 1) (hp2 : p ≠ 2) :
    ∃ q, q < L + 4 + 1 ∧
      (if q < 2 then 1 else if q ≤ L + 2 then q - 2 else L + 1) <
        (if p < 2 then 1 else if p ≤ L + 2 then p - 2 else L + 1) ∧
      0 < (if p < q then dAffineModel (L + 4) p q else dAffineModel (L + 4) q p) := by
  rcases Nat.lt_or_ge p 2 with h | h
  · refine ⟨2, by omega, by simp [h], ?_⟩
    simp only [h, if_true, dAffineModel]
    interval_cases p <;> simp
  rcases Nat.lt_or_ge (L + 2) p with h' | h'
  · refine ⟨L + 2, by omega, by
      simp [show ¬p < 2 by omega, show ¬p ≤ L + 2 by omega], ?_⟩
    simp only [show ¬p < L + 2 by omega, if_false, dAffineModel]
    split_ifs <;> omega
  · refine ⟨p - 1, by omega, by
      simp [show ¬p < 2 by omega, show p ≤ L + 2 by omega, show p - 1 ≤ L + 2 by omega,
        show ¬p - 1 < 2 by omega]; omega, ?_⟩
    simp only [show ¬p < p - 1 by omega, if_false, dAffineModel]
    split_ifs <;> omega

/-- **A path `x = y 0, …, y L = x'`, two further neighbours `a, b` of `x` and two further
neighbours `c, d` of `x'`**, all off the path and pairwise distinct, all weights `1`: a
subdiagram of shape `D_{L+4}^{(1)}`. -/
private theorem extended_of_dAffine_config (hT : IsTreeDiagram B)
    (hw1 : ∀ i j, (diagramGraph B).Adj i j → diagramWeight B i j = 1) {x x' a b c d : Fin N}
    {y : ℕ → Fin N} {L : ℕ} (hy : IsSeqPath (diagramGraph B) y L) (hy0 : y 0 = x)
    (hyL : y L = x') (ha : (diagramGraph B).Adj x a) (hb : (diagramGraph B).Adj x b)
    (hc : (diagramGraph B).Adj x' c) (hd : (diagramGraph B).Adj x' d) (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (haY : ∀ i, i ≤ L → y i ≠ a) (hbY : ∀ i, i ≤ L → y i ≠ b) (hcY : ∀ i, i ≤ L → y i ≠ c)
    (hdY : ∀ i, i ≤ L → y i ≠ d) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix e e)) := by
  set S : ℕ → Fin N := fun p => if p = 0 then a else if p = 1 then b else
    if p ≤ L + 2 then y (p - 2) else if p = L + 3 then c else d
  have hSa : S 0 = a := rfl
  have hSb : S 1 = b := rfl
  have hSy : ∀ p, 2 ≤ p → p ≤ L + 2 → S p = y (p - 2) := fun p h1 h2 => by
    simp only [S, show p ≠ 0 by omega, show p ≠ 1 by omega, h2, if_true, if_false]
  have hSc : S (L + 3) = c := by simp [S]
  have hSd : S (L + 4) = d := by simp [S, show ¬L + 4 ≤ L + 2 by omega]
  clear_value S
  obtain ⟨e, he⟩ := diagramWeight_eq_model_of_unit (M := L + 4 + 1) hT hw1 (s := S)
    (injOn_dAffine hy hSa hSb hSy hSc hSd hab hac had hbc hbd hcd haY hbY hcY hdY)
    (dAffineModel (L + 4)) (fun p q => by simp only [dAffineModel]; split_ifs <;> omega)
    (fun p q hpq hq hf => by
      simp only [dAffineModel] at hf
      split_ifs at hf with H
      · rcases H with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hp, rfl, hq'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hSa, hSy 2 le_rfl (by omega)]; simpa [hy0] using ha.symm
        · rw [hSb, hSy 2 le_rfl (by omega)]; simpa [hy0] using hb.symm
        · rw [hSy p hp (by omega), hSy (p + 1) (by omega) (by omega),
            show p + 1 - 2 = p - 2 + 1 by omega]
          exact hy.2 _ (by omega)
        · rw [hSy (L + 4 - 2) (by omega) (by omega), show L + 4 - 2 - 2 = L by omega, hyL,
            show L + 4 - 1 = L + 3 by omega, hSc]
          exact hc
        · rw [hSy (L + 4 - 2) (by omega) (by omega), show L + 4 - 2 - 2 = L by omega, hyL, hSd]
          exact hd
      · omega)
    2 (fun p => if p < 2 then 1 else if p ≤ L + 2 then p - 2 else L + 1)
    (dAffineModel_exists_lower L)
  exact ⟨L + 4 + 1, e, Or.inr (Or.inr (Or.inl ⟨L + 4, by omega, he⟩))⟩

/-- **Two vertices of degree `3`**, all weights `1`: with the path joining them, two further
neighbours of each give a subdiagram of shape `D_k^{(1)}`. -/
private theorem extended_of_two_branch_points (hT : IsTreeDiagram B)
    (hw1 : ∀ i j, (diagramGraph B).Adj i j → diagramWeight B i j = 1) {x x' : Fin N}
    (hxx' : x ≠ x')
    (hx : ∃ a b c, (diagramGraph B).Adj x a ∧ (diagramGraph B).Adj x b ∧
      (diagramGraph B).Adj x c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hx' : ∃ a b c, (diagramGraph B).Adj x' a ∧ (diagramGraph B).Adj x' b ∧
      (diagramGraph B).Adj x' c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix e e)) := by
  have hac := hT.isAcyclic
  obtain ⟨y, L, hy, hy0, hyL⟩ := exists_isSeqPath hT.connected x x'
  have hL : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with rfl | h
    · exact absurd (hy0.symm.trans hyL) hxx'
    · exact h
  obtain ⟨n₁, n₂, n₃, h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ := hx
  obtain ⟨a, b, ha, hb, hab, ha1, hb1⟩ := exists_two_neighbors_ne h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ (y 1)
  obtain ⟨n₁, n₂, n₃, h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ := hx'
  obtain ⟨c, d, hc, hd, hcd, hc1, hd1⟩ :=
    exists_two_neighbors_ne h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ (y (L - 1))
  have haY := hy.ne_of_adj_first hac (by rw [hy0]; exact ha) ha1
  have hbY := hy.ne_of_adj_first hac (by rw [hy0]; exact hb) hb1
  have hr := hy.reverse
  have hcY' := hr.ne_of_adj_first hac (a := c) (by simpa [hyL] using hc) (by simpa using hc1)
  have hdY' := hr.ne_of_adj_first hac (a := d) (by simpa [hyL] using hd) (by simpa using hd1)
  have hcY : ∀ i, i ≤ L → y i ≠ c := fun i hi => by
    simpa [show L - (L - i) = i by omega] using hcY' (L - i) (by omega)
  have hdY : ∀ i, i ≤ L → y i ≠ d := fun i hi => by
    simpa [show L - (L - i) = i by omega] using hdY' (L - i) (by omega)
  have hna : ∀ e, (diagramGraph B).Adj x e → (∀ i, i ≤ L → y i ≠ e) → ¬(diagramGraph B).Adj x' e :=
    fun e he hY he' => hy.not_adj_last_of_adj_first hac hL hY (by rw [hy0]; exact he.symm)
      (by rw [hyL]; exact he'.symm)
  exact extended_of_dAffine_config hT hw1 hy hy0 hyL ha hb hc hd hab
    (by rintro rfl; exact hna a ha haY hc) (by rintro rfl; exact hna a ha haY hd)
    (by rintro rfl; exact hna b hb hbY hc) (by rintro rfl; exact hna b hb hbY hd) hcd haY hbY hcY
    hdY

/-! #### Trees with exactly one branch point -/

/-- An arm `o = X 0, X 1, …, X α` at `o`: a path from `o` whose vertices other than `o` are
adjacent only to their neighbours on the path. -/
private def IsArm {V : Type*} (G : SimpleGraph V) (o : V) (X : ℕ → V) (α : ℕ) : Prop :=
  1 ≤ α ∧ IsSeqPath G X α ∧ X 0 = o ∧ ∀ t, 1 ≤ t → t ≤ α → ∀ w, G.Adj (X t) w →
    w = X (t - 1) ∨ (t < α ∧ w = X (t + 1))

/-- In a tree in which every vertex other than `o` has at most two neighbours, every
neighbour `u` of `o` starts an arm at `o`. -/
private theorem exists_isArm {G : SimpleGraph (Fin N)} (hG : G.IsAcyclic) {o u : Fin N}
    (hu : G.Adj o u) (hdeg : ∀ x, x ≠ o → AtMostTwoNeighbors G x) :
    ∃ X α, IsArm G o X α ∧ X 1 = u := by
  have hz : IsSeqPath G (fun t => if t = 0 then o else u) 1 :=
    ⟨fun i j hi hj h => by
      interval_cases i <;> interval_cases j <;> simp_all [hu.ne, hu.ne.symm],
      fun i hi => by interval_cases i; simpa using hu⟩
  obtain ⟨X, α, hα, hpre, hX, hend⟩ := hz.exists_maximal
  have hX0 : X 0 = o := by simpa using hpre 0 (by omega)
  have hX1 : X 1 = u := by simpa using hpre 1 le_rfl
  refine ⟨X, α, ⟨hα, hX, hX0, fun t ht1 htα w hw => ?_⟩, hX1⟩
  rcases Nat.lt_or_ge t α with h | h
  · have hne : X t ≠ o := by rw [← hX0]; exact hX.ne (by omega) (by omega) (by omega)
    rcases hX.eq_of_adj_interior (by omega) h (hdeg _ hne) hw with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h, h'⟩
  · obtain rfl : t = α := by omega
    exact Or.inl (hX.eq_of_adj_last hG hend hw)

/-- Two arms at `o` starting with distinct neighbours of `o` are disjoint away from `o`. -/
private theorem IsArm.disjoint {V : Type*} {G : SimpleGraph V} {o : V} {X Y : ℕ → V}
    {α β : ℕ} (hX : IsArm G o X α) (hY : IsArm G o Y β) (h1 : X 1 ≠ Y 1) :
    ∀ i j, 1 ≤ i → i ≤ α → 1 ≤ j → j ≤ β → X i ≠ Y j := by
  have := hX.1
  have := hY.1
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hi1 hiα hj1 hjβ hij
    have hY0 : ∀ t, 1 ≤ t → t ≤ β → Y t ≠ o := fun t ht1 htβ h =>
      absurd (hY.2.1.1 t 0 htβ (Nat.zero_le _) (h.trans hY.2.2.1.symm)) (by omega)
    have hX0 : ∀ t, 1 ≤ t → t ≤ α → X t ≠ o := fun t ht1 htα h =>
      absurd (hX.2.1.1 t 0 htα (Nat.zero_le _) (h.trans hX.2.2.1.symm)) (by omega)
    rcases Nat.lt_or_ge i 2 with hi | hi
    · obtain rfl : i = 1 := by omega
      have hadj : G.Adj (Y j) o := by
        rw [← hij, ← hX.2.2.1]; exact (hX.2.1.2 0 (by omega)).symm
      rcases hY.2.2.2 j hj1 hjβ o hadj with h | ⟨hjβ', h⟩
      · rcases Nat.lt_or_ge j 2 with hj | hj
        · obtain rfl : j = 1 := by omega
          exact h1 hij
        · exact hY0 (j - 1) (by omega) (by omega) h.symm
      · exact hY0 (j + 1) (by omega) (by omega) h.symm
    · have hadj : G.Adj (Y j) (X (i - 1)) := by
        rw [← hij]
        have := hX.2.1.2 (i - 1) (by omega)
        rw [show i - 1 + 1 = i by omega] at this
        exact this.symm
      rcases hY.2.2.2 j hj1 hjβ _ hadj with h | ⟨hjβ', h⟩
      · rcases Nat.lt_or_ge j 2 with hj | hj
        · obtain rfl : j = 1 := by omega
          exact hX0 (i - 1) (by omega) (by omega) (h.trans hY.2.2.1)
        · exact ih (i - 1) (by omega) (j - 1) (by omega) (by omega) (by omega) (by omega) h
      · exact ih (i - 1) (by omega) (j + 1) (by omega) (by omega) (by omega) (by omega) h

/-- The enumeration `o, X 1, …, X a, Y 1, …, Y b, Z 1, …, Z c` of a tree `T_{a,b,c}`. -/
private def spiderSeq {V : Type*} (X Y Z : ℕ → V) (a b : ℕ) (p : ℕ) : V :=
  if p ≤ a then X p else if p ≤ a + b then Y (p - a) else Z (p - a - b)

/-- The positions `0, …, a` of `spiderSeq` carry `X`. -/
private theorem spiderSeq_of_le {V : Type*} {X Y Z : ℕ → V} {a b p : ℕ} (h : p ≤ a) :
    spiderSeq X Y Z a b p = X p := by
  rw [spiderSeq, if_pos h]

/-- The positions `a + 1, …, a + b` of `spiderSeq` carry `Y`. -/
private theorem spiderSeq_of_lt_of_le {V : Type*} {X Y Z : ℕ → V} {a b p : ℕ} (h : a < p)
    (h' : p ≤ a + b) : spiderSeq X Y Z a b p = Y (p - a) := by
  rw [spiderSeq, if_neg (by omega), if_pos h']

/-- The positions after `a + b` of `spiderSeq` carry `Z`. -/
private theorem spiderSeq_of_lt {V : Type*} {X Y Z : ℕ → V} {a b p : ℕ} (h : a + b < p) :
    spiderSeq X Y Z a b p = Z (p - a - b) := by
  rw [spiderSeq, if_neg (by omega), if_neg (by omega)]

/-- The positions `0, …, a + b + c` of `spiderSeq` carry pairwise distinct vertices. -/
private theorem spiderSeq_injOn {V : Type*} {G : SimpleGraph V} {o : V} {X Y Z : ℕ → V}
    {α β γ : ℕ} (hX : IsArm G o X α) (hY : IsArm G o Y β) (hZ : IsArm G o Z γ)
    (hXY : X 1 ≠ Y 1) (hXZ : X 1 ≠ Z 1) (hYZ : Y 1 ≠ Z 1) {a b c : ℕ} (ha : a ≤ α)
    (hb : b ≤ β) (hc : c ≤ γ) :
    ∀ i j, i < a + b + c + 1 → j < a + b + c + 1 → spiderSeq X Y Z a b i =
      spiderSeq X Y Z a b j → i = j := by
  have dXY := hX.disjoint hY hXY
  have dXZ := hX.disjoint hZ hXZ
  have dYZ := hY.disjoint hZ hYZ
  have hX0 := hX.2.2.1
  have hY0 := hY.2.2.1
  have hZ0 := hZ.2.2.1
  have key : ∀ p, (p ≤ a ∧ spiderSeq X Y Z a b p = X p) ∨
      (a < p ∧ p ≤ a + b ∧ spiderSeq X Y Z a b p = Y (p - a)) ∨
      (a + b < p ∧ spiderSeq X Y Z a b p = Z (p - a - b)) := by
    intro p
    by_cases h1 : p ≤ a
    · exact Or.inl ⟨h1, spiderSeq_of_le h1⟩
    by_cases h2 : p ≤ a + b
    · exact Or.inr (Or.inl ⟨by omega, h2, spiderSeq_of_lt_of_le (by omega) h2⟩)
    · exact Or.inr (Or.inr ⟨by omega, spiderSeq_of_lt (by omega)⟩)
  intro i j hi hj h
  rcases key i with ⟨hi1, hSi⟩ | ⟨hi1, hi2, hSi⟩ | ⟨hi1, hSi⟩ <;>
  rcases key j with ⟨hj1, hSj⟩ | ⟨hj1, hj2, hSj⟩ | ⟨hj1, hSj⟩ <;>
  rw [hSi, hSj] at h
  · exact hX.2.1.1 i j (by omega) (by omega) h
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have := hY.2.1.1 0 (j - a) (by omega) (by omega) (hY0.trans (hX0.symm.trans h))
      omega
    · exact absurd h (dXY i (j - a) hi0 (by omega) (by omega) (by omega))
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have := hZ.2.1.1 0 (j - a - b) (by omega) (by omega) (hZ0.trans (hX0.symm.trans h))
      omega
    · exact absurd h (dXZ i (j - a - b) hi0 (by omega) (by omega) (by omega))
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have := hY.2.1.1 0 (i - a) (by omega) (by omega) (hY0.trans (hX0.symm.trans h.symm))
      omega
    · exact absurd h.symm (dXY j (i - a) hj0 (by omega) (by omega) (by omega))
  · have := hY.2.1.1 _ _ (by omega) (by omega) h
    omega
  · exact absurd h (dYZ (i - a) (j - a - b) (by omega) (by omega) (by omega) (by omega))
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have := hZ.2.1.1 0 (i - a - b) (by omega) (by omega)
        (hZ0.trans (hX0.symm.trans h.symm))
      omega
    · exact absurd h.symm (dXZ j (i - a - b) hj0 (by omega) (by omega) (by omega))
  · exact absurd h.symm (dYZ (j - a) (i - a - b) (by omega) (by omega) (by omega) (by omega))
  · have := hZ.2.1.1 _ _ (by omega) (by omega) h
    omega

/-- Initial segments of three arms at `o` form a subdiagram of shape `T_{a,b,c}`. -/
private theorem spiderSeq_spec (hT : IsTreeDiagram B)
    (hw1 : ∀ i j, (diagramGraph B).Adj i j → diagramWeight B i j = 1) {o : Fin N}
    {X Y Z : ℕ → Fin N} {α β γ : ℕ} (hX : IsArm (diagramGraph B) o X α)
    (hY : IsArm (diagramGraph B) o Y β) (hZ : IsArm (diagramGraph B) o Z γ)
    (hXY : X 1 ≠ Y 1) (hXZ : X 1 ≠ Z 1) (hYZ : Y 1 ≠ Z 1) {a b c : ℕ} (ha : a ≤ α)
    (hb : b ≤ β) (hc : c ≤ γ) :
    (∀ i j, i < a + b + c + 1 → j < a + b + c + 1 → spiderSeq X Y Z a b i =
      spiderSeq X Y Z a b j → i = j) ∧
    ∀ p q, p < q → q < a + b + c + 1 →
      diagramWeight B (spiderSeq X Y Z a b p) (spiderSeq X Y Z a b q) = tShapeModel a b c p q := by
  have hX0 := hX.2.2.1
  have hY0 := hY.2.2.1
  have hZ0 := hZ.2.2.1
  have hinj := spiderSeq_injOn hX hY hZ hXY hXZ hYZ ha hb hc
  refine ⟨hinj, diagramWeight_eq_model hT hinj (tShapeModel a b c) (fun p q hpq hq hf => ?_) 0
    id (fun p hp hp0 => ⟨if p = a + 1 ∨ p = a + b + 1 then 0 else p - 1, by
      split_ifs <;> omega, by simp only [id]; split_ifs <;> omega, by
      simp only [tShapeModel]; split_ifs <;> omega⟩)⟩
  have hf1 : tShapeModel a b c p q = 1 := by
    simp only [tShapeModel] at hf ⊢
    split_ifs at hf ⊢ <;> omega
  rw [hf1]
  refine hw1 _ _ ?_
  simp only [tShapeModel] at hf
  split_ifs at hf with H
  · rcases H with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · subst h1
      rw [spiderSeq_of_le (by omega), spiderSeq_of_le h2]
      exact hX.2.1.2 p (by omega)
    · subst h1 h2
      rw [spiderSeq_of_le (by omega), spiderSeq_of_lt_of_le (by omega) (by omega), hX0, ← hY0,
        show a + 1 - a = 0 + 1 by omega]
      exact hY.2.1.2 0 (by omega)
    · subst h2
      rw [spiderSeq_of_lt_of_le (by omega) (by omega), spiderSeq_of_lt_of_le (by omega) (by omega),
        show p + 1 - a = p - a + 1 by omega]
      exact hY.2.1.2 _ (by omega)
    · subst h1 h2
      rw [spiderSeq_of_le (by omega), spiderSeq_of_lt (by omega), hX0, ← hZ0,
        show a + b + 1 - a - b = 0 + 1 by omega]
      exact hZ.2.1.2 0 (by omega)
    · subst h2
      rw [spiderSeq_of_lt (by omega), spiderSeq_of_lt (by omega),
        show p + 1 - a - b = p - a - b + 1 by omega]
      exact hZ.2.1.2 _ (by omega)
  · omega

/-- Three full arms at `o`, where `o` has no other neighbours, meet every vertex. -/
private theorem spiderSeq_surjective {V : Type*} {G : SimpleGraph V} (hG : G.Connected) {o : V}
    {X Y Z : ℕ → V} {α β γ : ℕ} (hX : IsArm G o X α) (hY : IsArm G o Y β) (hZ : IsArm G o Z γ)
    (hnb : ∀ w, G.Adj o w → w = X 1 ∨ w = Y 1 ∨ w = Z 1) (x : V) :
    ∃ p, p < α + β + γ + 1 ∧ spiderSeq X Y Z α β p = x := by
  have := hX.1
  have := hY.1
  have := hZ.1
  refine mem_of_closed hG (S := {x | ∃ p, p < α + β + γ + 1 ∧ spiderSeq X Y Z α β p = x})
    ⟨0, by omega, by rw [spiderSeq_of_le (Nat.zero_le _), hX.2.2.1]⟩ ?_ x
  rintro _ w ⟨p, hp, rfl⟩ hw
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [spiderSeq_of_le (Nat.zero_le _), hX.2.2.1] at hw
    rcases hnb w hw with rfl | rfl | rfl
    · exact ⟨1, by omega, spiderSeq_of_le (by omega)⟩
    · exact ⟨α + 1, by omega, by rw [spiderSeq_of_lt_of_le (by omega) (by omega),
        show α + 1 - α = 1 by omega]⟩
    · exact ⟨α + β + 1, by omega, by rw [spiderSeq_of_lt (by omega),
        show α + β + 1 - α - β = 1 by omega]⟩
  by_cases h1 : p ≤ α
  · rw [spiderSeq_of_le h1] at hw
    rcases hX.2.2.2 p hp0 h1 w hw with rfl | ⟨h, rfl⟩
    · exact ⟨p - 1, by omega, spiderSeq_of_le (by omega)⟩
    · exact ⟨p + 1, by omega, spiderSeq_of_le (by omega)⟩
  by_cases h2 : p ≤ α + β
  · rw [spiderSeq_of_lt_of_le (by omega) h2] at hw
    rcases hY.2.2.2 (p - α) (by omega) (by omega) w hw with rfl | ⟨h, rfl⟩
    · by_cases h3 : p - α = 1
      · refine ⟨0, by omega, ?_⟩
        rw [spiderSeq_of_le (Nat.zero_le _), hX.2.2.1, h3, hY.2.2.1]
      · exact ⟨p - 1, by omega, by
          rw [spiderSeq_of_lt_of_le (by omega) (by omega), show p - 1 - α = p - α - 1 by omega]⟩
    · exact ⟨p + 1, by omega, by
        rw [spiderSeq_of_lt_of_le (by omega) (by omega), show p + 1 - α = p - α + 1 by omega]⟩
  · rw [spiderSeq_of_lt (by omega)] at hw
    rcases hZ.2.2.2 (p - α - β) (by omega) (by omega) w hw with rfl | ⟨h, rfl⟩
    · by_cases h3 : p - α - β = 1
      · refine ⟨0, by omega, ?_⟩
        rw [spiderSeq_of_le (Nat.zero_le _), hX.2.2.1, h3, hZ.2.2.1]
      · exact ⟨p - 1, by omega, by
          rw [spiderSeq_of_lt (by omega), show p - 1 - α - β = p - α - β - 1 by omega]⟩
    · exact ⟨p + 1, by omega, by
        rw [spiderSeq_of_lt (by omega), show p + 1 - α - β = p - α - β + 1 by omega]⟩

/-- **Exactly one vertex of degree `3`**, all weights `1`, arms of lengths `α ≤ β ≤ γ`: the
tree `T_{α,β,γ}` is `D_N` or `E_N`, or contains `T_{1,2,5}`, `T_{1,3,3}` or `T_{2,2,2}`. -/
private theorem spider_conclusion (hB : SkewSymmetrizable B) (hT : IsTreeDiagram B)
    (hw1 : ∀ i j, (diagramGraph B).Adj i j → diagramWeight B i j = 1) {o : Fin N}
    {X Y Z : ℕ → Fin N} {α β γ : ℕ} (hX : IsArm (diagramGraph B) o X α)
    (hY : IsArm (diagramGraph B) o Y β) (hZ : IsArm (diagramGraph B) o Z γ)
    (hXY : X 1 ≠ Y 1) (hXZ : X 1 ≠ Z 1) (hYZ : Y 1 ≠ Z 1)
    (hnb : ∀ w, (diagramGraph B).Adj o w → w = X 1 ∨ w = Y 1 ∨ w = Z 1)
    (hαβ : α ≤ β) (hβγ : β ≤ γ) :
    (∃ X : DynkinSymbol, HasDynkinShape B [X]) ∨
      ∃ (m : ℕ) (v : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix v v)) := by
  have hα := hX.1
  have hsurj := spiderSeq_surjective hT.connected hX hY hZ hnb
  by_cases h2 : 2 ≤ α
  · obtain ⟨hinj, hw⟩ := spiderSeq_spec hT hw1 hX hY hZ hXY hXZ hYZ (a := 2) (b := 2) (c := 2)
      h2 (by omega) (by omega)
    obtain ⟨e, he⟩ := exists_embedding_isShapeOf hinj _ hw
    exact Or.inr ⟨_, e, Or.inr (Or.inr (Or.inr (Or.inl he)))⟩
  obtain rfl : α = 1 := by omega
  by_cases h3 : 3 ≤ β
  · obtain ⟨hinj, hw⟩ := spiderSeq_spec hT hw1 hX hY hZ hXY hXZ hYZ (a := 1) (b := 3) (c := 3)
      le_rfl h3 (by omega)
    obtain ⟨e, he⟩ := exists_embedding_isShapeOf hinj _ hw
    exact Or.inr ⟨_, e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))⟩
  by_cases h1 : β = 1
  · subst h1
    obtain ⟨hinj, hw⟩ := spiderSeq_spec hT hw1 hX hY hZ hXY hXZ hYZ le_rfl le_rfl le_rfl
    obtain ⟨hN, hS⟩ := isShapeOf_of_surjective hinj hsurj _ hw
    refine Or.inl ⟨_, hasDynkinShape_D_of_isTShape hB (by omega) ?_⟩
    rwa [show N - 3 = γ by omega]
  obtain rfl : β = 2 := by omega
  by_cases h5 : 5 ≤ γ
  · obtain ⟨hinj, hw⟩ := spiderSeq_spec hT hw1 hX hY hZ hXY hXZ hYZ (a := 1) (b := 2) (c := 5)
      le_rfl le_rfl h5
    obtain ⟨e, he⟩ := exists_embedding_isShapeOf hinj _ hw
    exact Or.inr ⟨_, e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))⟩
  · obtain ⟨hinj, hw⟩ := spiderSeq_spec hT hw1 hX hY hZ hXY hXZ hYZ le_rfl le_rfl le_rfl
    obtain ⟨hN, hS⟩ := isShapeOf_of_surjective hinj hsurj _ hw
    refine Or.inl ⟨_, hasDynkinShape_E_of_isTShape hB (by omega) ?_⟩
    rwa [show N - 4 = γ by omega]

/-- **Exactly one vertex `o` of degree `3`**, all weights `1`. -/
private theorem spider_main (hB : SkewSymmetrizable B) (hT : IsTreeDiagram B)
    (hw1 : ∀ i j, (diagramGraph B).Adj i j → diagramWeight B i j = 1) {o u₁ u₂ u₃ : Fin N}
    (h₁ : (diagramGraph B).Adj o u₁) (h₂ : (diagramGraph B).Adj o u₂)
    (h₃ : (diagramGraph B).Adj o u₃) (h₁₂ : u₁ ≠ u₂) (h₁₃ : u₁ ≠ u₃) (h₂₃ : u₂ ≠ u₃)
    (hnb : ∀ w, (diagramGraph B).Adj o w → w = u₁ ∨ w = u₂ ∨ w = u₃)
    (hdeg : ∀ x, x ≠ o → AtMostTwoNeighbors (diagramGraph B) x) :
    (∃ X : DynkinSymbol, HasDynkinShape B [X]) ∨
      ∃ (m : ℕ) (v : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix v v)) := by
  obtain ⟨X₁, l₁, hX₁, rfl⟩ := exists_isArm hT.isAcyclic h₁ hdeg
  obtain ⟨X₂, l₂, hX₂, rfl⟩ := exists_isArm hT.isAcyclic h₂ hdeg
  obtain ⟨X₃, l₃, hX₃, rfl⟩ := exists_isArm hT.isAcyclic h₃ hdeg
  have p1 := fun w hw => (hnb w hw).elim Or.inl (fun h => h.elim (Or.inr ∘ Or.inr)
    (Or.inr ∘ Or.inl))
  have p2 := fun w hw => (hnb w hw).elim (Or.inr ∘ Or.inl) (fun h => h.elim Or.inl
    (Or.inr ∘ Or.inr))
  have p3 := fun w hw => (hnb w hw).elim (Or.inr ∘ Or.inl) (fun h => h.elim
    (Or.inr ∘ Or.inr) Or.inl)
  have p4 := fun w hw => (hnb w hw).elim (Or.inr ∘ Or.inr) (fun h => h.elim Or.inl
    (Or.inr ∘ Or.inl))
  have p5 := fun w hw => (hnb w hw).elim (Or.inr ∘ Or.inr) (fun h => h.elim
    (Or.inr ∘ Or.inl) Or.inl)
  rcases le_total l₁ l₂ with h12 | h12 <;> rcases le_total l₂ l₃ with h23 | h23 <;>
    rcases le_total l₁ l₃ with h13 | h13
  · exact spider_conclusion hB hT hw1 hX₁ hX₂ hX₃ h₁₂ h₁₃ h₂₃ hnb h12 h23
  · exact spider_conclusion hB hT hw1 hX₁ hX₂ hX₃ h₁₂ h₁₃ h₂₃ hnb h12 h23
  · exact spider_conclusion hB hT hw1 hX₁ hX₃ hX₂ h₁₃ h₁₂ h₂₃.symm p1 h13 h23
  · exact spider_conclusion hB hT hw1 hX₃ hX₁ hX₂ h₁₃.symm h₂₃.symm h₁₂ p3 h13 h12
  · exact spider_conclusion hB hT hw1 hX₂ hX₁ hX₃ h₁₂.symm h₂₃ h₁₃ p2 h12 h13
  · exact spider_conclusion hB hT hw1 hX₂ hX₃ hX₁ h₂₃ h₁₂.symm h₁₃.symm p4 h23 h13
  · exact spider_conclusion hB hT hw1 hX₃ hX₂ hX₁ h₂₃.symm h₁₃.symm h₁₂.symm p5 h23 h12
  · exact spider_conclusion hB hT hw1 hX₃ hX₂ hX₁ h₂₃.symm h₁₃.symm h₁₂.symm p5 h23 h12

/-! #### Trees without branch points -/

/-- A tree all of whose vertices have at most two neighbours is a path through all vertices. -/
private theorem exists_isSeqPath_of_atMostTwoNeighbors {G : SimpleGraph (Fin N)}
    (hG : G.IsTree) (hdeg : ∀ x, AtMostTwoNeighbors G x) :
    ∃ y, IsSeqPath G y (N - 1) := by
  have hac := hG.isAcyclic
  have hN : 0 < N := Fin.pos_iff_nonempty.2 hG.connected.nonempty
  have h0 : ∀ v : Fin N, IsSeqPath G (fun _ => v) 0 :=
    fun v => ⟨fun i j hi hj _ => by omega, fun i hi => by omega⟩
  obtain ⟨z, k, -, -, hz, hzend⟩ := (h0 ⟨0, hN⟩).exists_maximal
  have hleaf : ∀ w w', G.Adj (z k) w → G.Adj (z k) w' → w = w' := by
    intro w w' hw hw'
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨i, hi, rfl⟩ := hzend w hw
      obtain rfl : i = 0 := by omega
      exact absurd hw (G.irrefl)
    · rw [hz.eq_of_adj_last hac hzend hw, hz.eq_of_adj_last hac hzend hw']
  obtain ⟨y, l, -, hpre, hy, hyend⟩ := (h0 (z k)).exists_maximal
  have hy0 : y 0 = z k := by simpa using hpre 0 le_rfl
  have hall := mem_of_closed hG.connected (S := {x | ∃ i, i ≤ l ∧ y i = x}) ⟨0, by omega, rfl⟩
    (by
      rintro _ w ⟨i, hi, rfl⟩ hw
      rcases Nat.lt_or_ge i l with h | h
      · rcases Nat.eq_zero_or_pos i with rfl | hi0
        · refine ⟨1, by omega, ?_⟩
          rw [hy0] at hw
          exact hleaf _ _ (by rw [← hy0]; exact hy.2 0 (by omega)) hw
        · rcases hy.eq_of_adj_interior hi0 h (hdeg _) hw with rfl | rfl
          · exact ⟨i - 1, by omega, rfl⟩
          · exact ⟨i + 1, by omega, rfl⟩
      · obtain rfl : i = l := by omega
        exact hyend w hw)
  have hbij : Function.Bijective (fun i : Fin (l + 1) => y i) :=
    ⟨fun i j hij => Fin.ext (hy.1 i j (by omega) (by omega) hij), fun x => by
      obtain ⟨i, hi, rfl⟩ := hall x
      exact ⟨⟨i, by omega⟩, rfl⟩⟩
  have := Fintype.card_congr (Equiv.ofBijective _ hbij)
  simp only [Fintype.card_fin] at this
  rw [show N - 1 = l by omega]
  exact ⟨y, hy⟩

/-- On a path whose weights are at most `2`, with a single edge `{y t, y (t + 1)}` of weight `2`,
the weights are `2` at `t` and `1` elsewhere. -/
private theorem path_weight_eq_ite (hw : ∀ i j, diagramWeight B i j ≤ 3)
    (h22 : ∀ a b c d, (diagramGraph B).Adj a b → (diagramGraph B).Adj c d →
      diagramWeight B a b = 2 → diagramWeight B c d = 2 → s(a, b) = s(c, d))
    {y : ℕ → Fin N} {k : ℕ} (hy : IsSeqPath (diagramGraph B) y k)
    (hthree : ∀ t, t < k → diagramWeight B (y t) (y (t + 1)) ≠ 3) {t : ℕ} (ht : t < k)
    (ht2 : diagramWeight B (y t) (y (t + 1)) = 2) :
    ∀ s, s < k → diagramWeight B (y s) (y (s + 1)) = if s = t then 2 else 1 := by
  intro s hs
  split_ifs with h
  · rw [h, ht2]
  · have := (hy.2 s hs).2; have := hthree s hs; have := hw (y s) (y (s + 1))
    have : diagramWeight B (y s) (y (s + 1)) ≠ 2 := fun h2 => by
      have := h22 _ _ _ _ (hy.2 s hs) (hy.2 t ht) h2 ht2
      rw [Sym2.eq_iff] at this
      rcases this with ⟨h1, -⟩ | ⟨h1, h1'⟩
      · exact h (hy.1 _ _ (by omega) (by omega) h1)
      · have := hy.1 _ _ (by omega) (by omega) h1
        have := hy.1 _ _ (by omega) (by omega) h1'
        omega
    omega

/-- **A path of weights `1, …, 1, 2, 1, …, 1` on at least five vertices, the weight `2` on
neither end edge**: a subdiagram of shape `F₄^{(1)}`. -/
private theorem extended_of_path_weight_two (hT : IsTreeDiagram B) {y : ℕ → Fin N}
    (hy : IsSeqPath (diagramGraph B) y (N - 1)) {t : ℕ} (ht : t < N - 1)
    (hg : ∀ s, s < N - 1 → diagramWeight B (y s) (y (s + 1)) = if s = t then 2 else 1)
    (ht0 : t ≠ 0) (htN : t ≠ N - 2) (hN4 : N ≠ 4) :
    ∃ (m : ℕ) (v : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix v v)) := by
  by_cases ht1 : t = 1
  · subst ht1
    obtain ⟨e, he⟩ := exists_embedding_isShapeOf_path hT (hy.mono (l := 4) (by omega))
      f4AffineModel fun p q hpq hq => by
        simp only [f4AffineModel]
        by_cases h : p + 1 = q
        · subst h
          rw [hg p (by omega)]
          simp [hq]
        · simp [h]
    exact ⟨5, e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))))⟩
  · have hz := (hy.mono (l := t + 2) (by omega)).reverse.mono (l := 4) (by omega)
    obtain ⟨e, he⟩ := exists_embedding_isShapeOf_path hT hz f4AffineModel fun p q hpq hq => by
        simp only [f4AffineModel]
        by_cases h : p + 1 = q
        · subst h
          rw [diagramWeight_comm, show t + 2 - p = t + 2 - (p + 1) + 1 by omega,
            hg _ (by omega)]
          simp only [hq, and_self, if_true]
          split_ifs <;> omega
        · simp [h]
    exact ⟨5, e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))))⟩

/-- **No vertex of degree `3`**: the tree is a path, of Dynkin shape `A_N`, `B_N`, `F₄` or `G₂`
or containing a subdiagram of shape `F₄^{(1)}`. -/
private theorem path_main (hB : SkewSymmetrizable B) (hT : IsTreeDiagram B)
    (hw : ∀ i j, diagramWeight B i j ≤ 3)
    (h3 : ¬(3 ≤ N ∧ ∃ u v, (diagramGraph B).Adj u v ∧ diagramWeight B u v = 3))
    (h22 : ∀ a b c d, (diagramGraph B).Adj a b → (diagramGraph B).Adj c d →
      diagramWeight B a b = 2 → diagramWeight B c d = 2 → s(a, b) = s(c, d))
    (hdeg : ∀ x, AtMostTwoNeighbors (diagramGraph B) x) :
    (∃ X : DynkinSymbol, HasDynkinShape B [X]) ∨
      ∃ (m : ℕ) (v : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix v v)) := by
  have hN : 1 ≤ N := Fin.pos_iff_nonempty.2 hT.connected.nonempty
  obtain ⟨y, hy⟩ := exists_isSeqPath_of_atMostTwoNeighbors hT hdeg
  obtain ⟨v, hv, hvp⟩ := exists_isInducedPath hT hy hN
  by_cases hthree : ∃ t, t < N - 1 ∧ diagramWeight B (y t) (y (t + 1)) = 3
  · obtain ⟨t, ht, ht3⟩ := hthree
    have hN2 : N = 2 := by
      by_contra hne
      exact h3 ⟨by omega, _, _, hy.2 t ht, ht3⟩
    subst hN2
    obtain rfl : t = 0 := by omega
    exact Or.inl ⟨_, hasDynkinShape_G₂_of_isInducedPath hB hvp (by rw [hv, hv]; exact ht3)⟩
  push Not at hthree
  by_cases htwo : ∃ t, t < N - 1 ∧ diagramWeight B (y t) (y (t + 1)) = 2
  swap
  · push Not at htwo
    refine Or.inl ⟨_, hasDynkinShape_A_of_isInducedPath hB hN hvp fun p q hpq => ?_⟩
    rw [hv, hv, ← hpq]
    have := (hy.2 p (by omega)).2
    have := hthree p (by omega)
    have := htwo p (by omega)
    have := hw (y p) (y (p + 1))
    omega
  obtain ⟨t, ht, ht2⟩ := htwo
  have hg := path_weight_eq_ite hw h22 hy hthree ht ht2
  by_cases ht0 : t = 0
  · subst ht0
    refine Or.inl ⟨_, hasDynkinShape_B_of_isInducedPath hB (by omega) hvp fun p q hpq => ?_⟩
    rw [hv, hv, ← hpq, hg p (by omega)]
  by_cases htN : t = N - 2
  · obtain ⟨v', hv', hvp'⟩ := exists_isInducedPath hT hy.reverse hN
    refine Or.inl ⟨_, hasDynkinShape_B_of_isInducedPath hB (by omega) hvp' fun p q hpq => ?_⟩
    rw [hv', hv', ← hpq, diagramWeight_comm, show N - 1 - (p : ℕ) = N - 1 - (p + 1) + 1 by omega,
      hg _ (by omega)]
    simp only [htN]
    split_ifs <;> omega
  by_cases hN4 : N = 4
  · subst hN4
    obtain rfl : t = 1 := by omega
    exact Or.inl ⟨_, hasDynkinShape_F₄_of_isInducedPath hB hvp fun p q hpq => by
      rw [hv, hv, ← hpq, hg p (by omega)]⟩
  exact Or.inr (extended_of_path_weight_two hT hy ht hg ht0 htN hN4)

end Cases

/-- **A tree that is not Dynkin contains an extended Dynkin tree.** A skew-symmetrizable
`N × N` tree diagram with all weights at most `3` either has Dynkin shape `X` for a single
Dynkin symbol `X` (of rank `N`), or has pairwise distinct indices `v₁, …, v_m` such that the
subdiagram `B^{(v₁, …, v_m)}` is of an extended Dynkin shape. -/
@[cluster_algebras "lem_non_dynkin_tree"]
theorem IsTreeDiagram.hasDynkinShape_or_isExtendedDynkinShape {B : Matrix (Fin N) (Fin N) ℤ}
    (hB : SkewSymmetrizable B) (hT : IsTreeDiagram B) (hw : ∀ i j, diagramWeight B i j ≤ 3) :
    (∃ X : DynkinSymbol, HasDynkinShape B [X]) ∨
      ∃ (m : ℕ) (v : Fin m ↪ Fin N), IsExtendedDynkinShape (diagramWeight (B.submatrix v v)) := by
  classical
  by_cases hW3 : 3 ≤ N ∧ ∃ u v, (diagramGraph B).Adj u v ∧ diagramWeight B u v = 3
  · obtain ⟨hN, u, v, huv, huv3⟩ := hW3
    exact Or.inr (extended_of_weight_three hT hw hN huv huv3)
  by_cases hW22 : ∃ a b c d, (diagramGraph B).Adj a b ∧ (diagramGraph B).Adj c d ∧
      diagramWeight B a b = 2 ∧ diagramWeight B c d = 2 ∧ s(a, b) ≠ s(c, d)
  · obtain ⟨a, b, c, d, hab, hcd, h1, h2, hne⟩ := hW22
    exact Or.inr (extended_of_two_weight_two hT hw hW3 hab hcd h1 h2 hne)
  have hW22' : ∀ a b c d, (diagramGraph B).Adj a b → (diagramGraph B).Adj c d →
      diagramWeight B a b = 2 → diagramWeight B c d = 2 → s(a, b) = s(c, d) :=
    fun a b c d hab hcd h1 h2 => by_contra fun hne => hW22 ⟨a, b, c, d, hab, hcd, h1, h2, hne⟩
  by_cases hD3 : ∃ x a b c, (diagramGraph B).Adj x a ∧ (diagramGraph B).Adj x b ∧
      (diagramGraph B).Adj x c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
  swap
  · refine path_main hB hT hw hW3 hW22' fun x a b c ha hb hc => ?_
    by_contra hcon
    push Not at hcon
    exact hD3 ⟨x, a, b, c, ha, hb, hc, hcon⟩
  obtain ⟨x, n₁, n₂, n₃, h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ := hD3
  have hN := three_le_of_ne h₁₂ h₁₃ h₂₃
  by_cases hW2 : ∃ u v, (diagramGraph B).Adj u v ∧ diagramWeight B u v = 2
  · obtain ⟨p, q, hpq, hpq2⟩ := hW2
    exact Or.inr (extended_of_weight_two_of_three_neighbors hT hw hW3 hW22' hpq hpq2 h₁ h₂ h₃
      h₁₂ h₁₃ h₂₃)
  have hw1 : ∀ i j, (diagramGraph B).Adj i j → diagramWeight B i j = 1 := fun i j h => by
    have := h.2; have := hw i j
    have : diagramWeight B i j ≠ 2 := fun h' => hW2 ⟨i, j, h, h'⟩
    have : diagramWeight B i j ≠ 3 := fun h' => hW3 ⟨hN, i, j, h, h'⟩
    omega
  by_cases hD4 : ∃ o a b c d, (diagramGraph B).Adj o a ∧ (diagramGraph B).Adj o b ∧
      (diagramGraph B).Adj o c ∧ (diagramGraph B).Adj o d ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧
      b ≠ d ∧ c ≠ d
  · obtain ⟨o, a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ := hD4
    exact Or.inr (extended_of_four_neighbors hT hw1 ha hb hc hd hab hac had hbc hbd hcd)
  by_cases hD33 : ∃ x', x' ≠ x ∧ ∃ a b c, (diagramGraph B).Adj x' a ∧ (diagramGraph B).Adj x' b ∧
      (diagramGraph B).Adj x' c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
  · obtain ⟨x', hx', hx'3⟩ := hD33
    exact Or.inr (extended_of_two_branch_points hT hw1 hx'.symm
      ⟨n₁, n₂, n₃, h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ hx'3)
  refine spider_main hB hT hw1 h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ (fun w hw' => ?_) fun y hy a b c ha hb hc => ?_
  · by_contra hcon
    push Not at hcon
    exact hD4 ⟨x, n₁, n₂, n₃, w, h₁, h₂, h₃, hw', h₁₂, h₁₃, fun h => hcon.1 h.symm, h₂₃,
      fun h => hcon.2.1 h.symm, fun h => hcon.2.2 h.symm⟩
  · by_contra hcon
    push Not at hcon
    exact hD33 ⟨y, hy, a, b, c, ha, hb, hc, hcon⟩

/-- **`2`-finite tree diagrams are Dynkin**: a `2`-finite tree diagram has Dynkin shape `X` for a
single Dynkin symbol `X`, and is in particular of Dynkin class `X`. -/
@[cluster_algebras "prop_trees_dynkin"]
theorem IsTwoFinite.hasDynkinShape_of_isTreeDiagram {B : Matrix (Fin N) (Fin N) ℤ}
    (hB : IsTwoFinite B) (hT : IsTreeDiagram B) :
    ∃ X : DynkinSymbol, HasDynkinShape B [X] ∧ IsOfDynkinClass B [X] := by
  rcases hT.hasDynkinShape_or_isExtendedDynkinShape hB.1 hB.diagramWeight_le_three with
    ⟨X, hX⟩ | ⟨m, v, hv⟩
  · exact ⟨X, hX, hX.isOfDynkinClass⟩
  · exfalso
    have h2 := hB.submatrix v
    rcases hv with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | hk | hk | hk | hk | ⟨a, hk⟩
    · exact not_isTwoFinite_of_isBAffineShape hk h2
    · exact not_isTwoFinite_of_isCAffineShape hk h2
    · exact not_isTwoFinite_of_isDAffineShape hk h2
    · exact not_isTwoFinite_of_isE6AffineShape hk h2
    · exact not_isTwoFinite_of_isE7AffineShape hk h2
    · exact not_isTwoFinite_of_isE8AffineShape hk h2
    · exact not_isTwoFinite_of_isF4AffineShape hk h2
    · exact not_isTwoFinite_of_isG2AffineShape hk h2

end ClusterAlgebras

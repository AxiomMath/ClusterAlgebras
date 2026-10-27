/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.FamilyCollapse

/-!
# Branches of rooted trees in plabic graphs

The branches of a rooted tree `T` of a plabic graph, one for each dart of its interval, are rooted
trees with the same root (`RootedTree.branchTree`). A rooted tree can be transported along an
embedding of its darts into another plabic graph (`RootedTree.IsEmbedding.tree`), and the plabic
graph of the transported tree is isomorphic to that of the original.

## Main definitions

* `ClusterAlgebras.PlabicData.RootedTree.branchTree`: the branch of a rooted tree at a dart of its
  interval, as a rooted tree with the same root.
* `ClusterAlgebras.PlabicData.RootedTree.IsEmbedding`: embeddings of the darts of a rooted tree
  into another plabic graph, and `RootedTree.IsEmbedding.tree`, the transported rooted tree.

## Implementation notes

* A connected graph whose edges are the pairs `{d, ι d}` of a set of darts has at least as many
  edges as vertices minus one (`card_le_card_image_pair_add_one`); this bounds the branches.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function _root_.Equiv _root_.Equiv.Perm

/-! ### Connected graphs given by darts -/

/-- Collapsing each pair `{d, ι d}` of darts in `D` to a common value `F d` does not increase the
number of values. -/
private theorem card_image_le_card_image_pair {H β : Type*} [DecidableEq H] [DecidableEq β]
    (ι : H → H) (D : Finset H) (F : H → β) (hF : ∀ d ∈ D, F (ι d) = F d) (x₀ : β) :
    (D.image F).card ≤ (D.image fun d => ({d, ι d} : Finset H)).card := by
  let g : Finset H → β := fun e =>
    if he : ∃ d ∈ D, ({d, ι d} : Finset H) = e then F he.choose else x₀
  have : D.image F = (D.image fun d => ({d, ι d} : Finset H)).image g := by
    rw [Finset.image_image]
    refine Finset.image_congr fun d hd => ?_
    have hex : ∃ d' ∈ D, ({d', ι d'} : Finset H) = {d, ι d} := ⟨d, hd, rfl⟩
    simp only [Function.comp, g, dif_pos hex]
    obtain ⟨hc, hce⟩ := hex.choose_spec
    generalize hex.choose = c at hc hce ⊢
    have hmem : c ∈ ({d, ι d} : Finset H) := hce ▸ Finset.mem_insert_self _ _
    rcases Finset.mem_insert.1 hmem with h | h
    · rw [h]
    · rw [Finset.mem_singleton.1 h, hF d hd]
  rw [this]
  exact Finset.card_image_le

/-- **A connected graph on `V` has at least `|V| - 1` edges**, for a graph whose edges are the
pairs `{d, ι d}` of darts `d ∈ D` joining the vertices `vtx d` and `vtx (ι d)`. -/
theorem card_le_card_image_pair_add_one {H α : Type*} [DecidableEq H]
    (vtx : H → α) (ι : H → H) (hι : Function.Involutive ι) (D : Finset H)
    (hD : ∀ d ∈ D, ι d ∈ D) (V : Finset α) (r : α) (hr : r ∈ V)
    (hends : ∀ d ∈ D, vtx d ∈ V)
    (hconn : ∀ u ∈ V,
      Relation.ReflTransGen (fun u u' => ∃ d ∈ D, vtx d = u ∧ vtx (ι d) = u') r u) :
    V.card ≤ (D.image fun d => ({d, ι d} : Finset H)).card + 1 := by
  classical
  let Γ : SimpleGraph V :=
    SimpleGraph.fromRel fun u u' => ∃ d ∈ D, vtx d = (u : α) ∧ vtx (ι d) = (u' : α)
  have hreach : ∀ u (hu : u ∈ V), Γ.Reachable ⟨r, hr⟩ ⟨u, hu⟩ := by
    intro u hu
    have h := hconn u hu
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail u₁ u₂ h₁ h₂ ih =>
      obtain ⟨d, hd, rfl, rfl⟩ := h₂
      have hu₁ : vtx d ∈ V := hends d hd
      refine (ih hu₁).trans ?_
      by_cases heq : vtx d = vtx (ι d)
      · rw [show (⟨vtx d, hu₁⟩ : V) = ⟨vtx (ι d), hu⟩ from Subtype.ext heq]
      · exact SimpleGraph.Adj.reachable
          ((SimpleGraph.fromRel_adj _ _ _).2 ⟨fun h => heq (congrArg Subtype.val h),
            Or.inl ⟨d, hd, rfl, rfl⟩⟩)
  have hconn' : Γ.Connected := by
    haveI : Nonempty V := ⟨⟨r, hr⟩⟩
    exact .mk fun u w => (hreach u u.2).symm.trans (hreach w w.2)
  have h1 := hconn'.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h1
  let F : H → Sym2 V := fun d =>
    if h : d ∈ D then s(⟨vtx d, hends d h⟩, ⟨vtx (ι d), hends _ (hD d h)⟩)
    else s(⟨r, hr⟩, ⟨r, hr⟩)
  have hF : ∀ d ∈ D, F (ι d) = F d := by
    intro d hd
    simp only [F, dif_pos hd, dif_pos (hD d hd), hι d]
    exact Sym2.eq_swap
  have hsub : Γ.edgeSet ⊆ (D.image F : Set (Sym2 V)) := by
    intro e he
    induction e using Sym2.ind with
    | h u w =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he
      obtain ⟨-, ⟨d, hd, h1, h2⟩ | ⟨d, hd, h1, h2⟩⟩ := he
      · refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨d, hd, ?_⟩)
        simp only [F, dif_pos hd]
        congr 1 <;> exact Subtype.ext ‹_›
      · refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨d, hd, ?_⟩)
        simp only [F, dif_pos hd]
        rw [Sym2.eq_swap]
        congr 1 <;> exact Subtype.ext ‹_›
  have h2 : Nat.card Γ.edgeSet ≤ (D.image F).card := by
    rw [← Set.ncard_coe_finset, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  have h3 := card_image_le_card_image_pair ι D F hF s(⟨r, hr⟩, ⟨r, hr⟩)
  omega

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-! ### Branches of a rooted tree -/

namespace RootedTree

variable (T : G.RootedTree)

/-- Adjacency along the edges of `T` between two non-root vertices. -/
def NonRootAdj (u u' : Finset H) : Prop :=
  u ∈ T.nonRoot ∧ u' ∈ T.nonRoot ∧ G.TreeAdj T.nonRoot u u'

/-- A vertex lies in the branch of `T` at `a` if and only if it is a non-root vertex joined to the
vertex of `ā` by a path of adjacent non-root vertices. -/
theorem mem_branch {a : H} {w : Finset H} :
    w ∈ T.branch a ↔ w ∈ T.nonRoot ∧
      Relation.ReflTransGen T.NonRootAdj (G.vertexOf (G.inv a)) w := by
  classical
  unfold branch
  rw [mem_filter]
  rfl

/-- Adjacency between non-root vertices of `T` is symmetric. -/
theorem nonRootAdj_symm (hG : G.IsPlabicGraph) {u u' : Finset H} (h : T.NonRootAdj u u') :
    T.NonRootAdj u' u := by
  obtain ⟨hu, hu', d, hd, rfl, rfl⟩ := h
  exact ⟨hu', hu, G.inv d, T.inv_mem_darts hG hd, rfl, by rw [hG.inv_involutive]⟩

/-- Paths of adjacent non-root vertices of `T` can be reversed. -/
theorem reflTransGen_nonRootAdj_symm (hG : G.IsPlabicGraph) {u u' : Finset H}
    (h : Relation.ReflTransGen T.NonRootAdj u u') : Relation.ReflTransGen T.NonRootAdj u' u := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (T.nonRootAdj_symm hG hstep) ih

/-- For a dart of the interval, the other end of its edge is a non-root vertex. -/
theorem vertexOf_inv_mem_nonRoot_of_mem_root {d : H} (hd : d ∈ T.darts) (hr : d ∈ T.root) :
    G.vertexOf (G.inv d) ∈ T.nonRoot := by
  rcases (G.mem_treeDarts.1 hd).2 with h | h
  · rw [T.mem_root_iff.1 hr] at h
    exact absurd h T.root_notMem_nonRoot
  · exact h

/-- Every non-root vertex lies in the branch at some dart of the interval. -/
theorem exists_mem_branch {w : Finset H} (hw : w ∈ T.nonRoot) :
    ∃ i < T.intervalLength, w ∈ T.branch ((G.rot ^ i) T.intervalStart) := by
  have key : ∀ u, Relation.ReflTransGen (G.TreeAdj T.nonRoot) T.root u →
      u = T.root ∨ ∃ i < T.intervalLength, u ∈ T.branch ((G.rot ^ i) T.intervalStart) := by
    intro u hu
    induction hu with
    | refl => exact Or.inl rfl
    | @tail u u' _ hstep ih =>
      obtain ⟨d, hd, rfl, rfl⟩ := hstep
      rcases ih with hroot | ⟨i, hi, hbr⟩
      · obtain ⟨i, hi, rfl⟩ := T.exists_eq_pow_of_mem_root hd (T.mem_root_iff.2 hroot)
        refine Or.inr ⟨i, hi, (T.mem_branch).2 ⟨?_, .refl⟩⟩
        exact T.vertexOf_inv_mem_nonRoot_of_mem_root hd (T.mem_root_iff.2 hroot)
      · have hdW := ((T.mem_branch).1 hbr).1
        rcases mem_insert.1 (T.vertexOf_inv_mem d hdW) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨i, hi, (T.mem_branch).2 ⟨h, ((T.mem_branch).1 hbr).2.tail
            ⟨hdW, h, d, hd, rfl, rfl⟩⟩⟩
  rcases key w (T.reflTransGen_treeAdj w (mem_insert_of_mem hw)) with h | h
  · exact absurd (h ▸ hw) T.root_notMem_nonRoot
  · exact h

/-- A path of non-root vertices avoids the darts of the interval. -/
private theorem reflTransGen_of_nonRootAdj {D' : Finset H}
    (hD' : ∀ d ∈ T.darts, G.vertexOf d ∈ T.nonRoot → G.vertexOf (G.inv d) ∈ T.nonRoot → d ∈ D')
    {u u' : Finset H} (h : Relation.ReflTransGen T.NonRootAdj u u') :
    Relation.ReflTransGen (fun u u' => ∃ d ∈ D', G.vertexOf d = u ∧ G.vertexOf (G.inv d) = u')
      u u' := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨hu, hu', d, hd, rfl, rfl⟩ := hstep
    exact ih.tail ⟨d, hD' d hd hu hu', rfl, rfl⟩

/-- If a vertex lies in the branches at two distinct darts `a_i`, `a_i'` of the interval, every
vertex of `T` is reachable from the root without the edge at `a_i`. -/
private theorem reflTransGen_root_of_mem_branch_of_mem_branch (hG : G.IsPlabicGraph) {i i' : ℕ}
    (hi : i < T.intervalLength) (hi' : i' < T.intervalLength) (hne : i ≠ i') {w : Finset H}
    (hwi : w ∈ T.branch ((G.rot ^ i) T.intervalStart))
    (hwi' : w ∈ T.branch ((G.rot ^ i') T.intervalStart)) :
    ∀ u ∈ insert T.root T.nonRoot, Relation.ReflTransGen
      (fun u u' => ∃ d ∈ T.darts.filter fun d => d ≠ (G.rot ^ i) T.intervalStart ∧
        d ≠ G.inv ((G.rot ^ i) T.intervalStart), G.vertexOf d = u ∧ G.vertexOf (G.inv d) = u')
      T.root u := by
  have hinv := hG.inv_involutive
  have hk := T.intervalLength_lt_card
  set a := (G.rot ^ i) T.intervalStart
  have haD : a ∈ T.darts := T.pow_intervalStart_mem_darts hi
  have haR : a ∈ T.root := T.pow_intervalStart_mem_root i
  set D' := T.darts.filter fun d => d ≠ a ∧ d ≠ G.inv a
  have hD'mem : ∀ d, d ∈ D' ↔ d ∈ T.darts ∧ d ≠ a ∧ d ≠ G.inv a := fun d => mem_filter
  have hWD' : ∀ d ∈ T.darts, G.vertexOf d ∈ T.nonRoot → G.vertexOf (G.inv d) ∈ T.nonRoot →
      d ∈ D' := by
    intro d hd h1 h2
    refine (hD'mem d).2 ⟨hd, ?_, ?_⟩
    · rintro rfl
      exact T.root_notMem_nonRoot (T.mem_root_iff.1 haR ▸ h1)
    · rintro rfl
      rw [hinv] at h2
      exact T.root_notMem_nonRoot (T.mem_root_iff.1 haR ▸ h2)
  have hstart : ∀ l < T.intervalLength, l ≠ i →
      (fun u u' => ∃ d ∈ D', G.vertexOf d = u ∧ G.vertexOf (G.inv d) = u') T.root
        (G.vertexOf (G.inv ((G.rot ^ l) T.intervalStart))) := by
    intro l hl hli
    refine ⟨(G.rot ^ l) T.intervalStart, (hD'mem _).2 ⟨T.pow_intervalStart_mem_darts hl, ?_, ?_⟩,
      T.mem_root_iff.1 (T.pow_intervalStart_mem_root l), rfl⟩
    · intro h
      exact hli (T.pow_intervalStart_injective (by omega) (by omega) h)
    · intro h
      have h1 := T.vertexOf_inv_mem_nonRoot_of_mem_root haD haR
      rw [← h, T.mem_root_iff.1 (T.pow_intervalStart_mem_root l)] at h1
      exact T.root_notMem_nonRoot h1
  intro u hu
  rcases mem_insert.1 hu with rfl | hu
  · exact .refl
  obtain ⟨l, hl, hul⟩ := T.exists_mem_branch hu
  rcases eq_or_ne l i with rfl | hli
  · exact .head (hstart i' hi' (Ne.symm hne)) (T.reflTransGen_of_nonRootAdj hWD'
      ((((T.mem_branch).1 hwi').2.trans (T.reflTransGen_nonRootAdj_symm hG
        ((T.mem_branch).1 hwi).2)).trans ((T.mem_branch).1 hul).2))
  · exact .head (hstart l hl hli) (T.reflTransGen_of_nonRootAdj hWD' ((T.mem_branch).1 hul).2)

/-- The branches at distinct darts of the interval are disjoint. -/
theorem disjoint_branch (hG : G.IsPlabicGraph) {i i' : ℕ} (hi : i < T.intervalLength)
    (hi' : i' < T.intervalLength) (hne : i ≠ i') :
    Disjoint (T.branch ((G.rot ^ i) T.intervalStart))
      (T.branch ((G.rot ^ i') T.intervalStart)) := by
  have hinv := hG.inv_involutive
  rw [Finset.disjoint_left]
  intro w hwi hwi'
  set a := (G.rot ^ i) T.intervalStart
  have haD : a ∈ T.darts := T.pow_intervalStart_mem_darts hi
  let D' := T.darts.filter fun d => d ≠ a ∧ d ≠ G.inv a
  have hD'mem : ∀ d, d ∈ D' ↔ d ∈ T.darts ∧ d ≠ a ∧ d ≠ G.inv a := fun d => mem_filter
  have hconn := T.reflTransGen_root_of_mem_branch_of_mem_branch hG hi hi' hne hwi hwi'
  have hbound := card_le_card_image_pair_add_one G.vertexOf G.inv hinv D'
    (fun d hd => by
      obtain ⟨hdD, h1, h2⟩ := (hD'mem d).1 hd
      refine (hD'mem _).2 ⟨T.inv_mem_darts hG hdD, fun h => h2 (by rw [← h, hinv]), fun h => h1
        (hinv.injective h)⟩)
    (insert T.root T.nonRoot) T.root (mem_insert_self _ _)
    (fun d hd => by
      rcases T.vertexOf_mem_or_eq_root hG ((hD'mem d).1 hd).1 with h | h
      · exact mem_insert_of_mem h
      · exact h ▸ mem_insert_self _ _) hconn
  rw [card_insert_of_notMem T.root_notMem_nonRoot] at hbound
  have hsub : (D'.image fun d => ({d, G.inv d} : Finset H)) ⊆
      (T.darts.image G.edgeOf).erase (G.edgeOf a) := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := mem_image.1 he
    obtain ⟨hdD, h1, h2⟩ := (hD'mem d).1 hd
    refine mem_erase.2 ⟨fun h => ?_, mem_image.2 ⟨d, hdD, rfl⟩⟩
    rcases (G.edgeOf_eq_edgeOf_iff hinv).1 h with h | h
    · exact h1 h
    · exact h2 h
  have hcard := card_le_card hsub
  rw [card_erase_of_mem (mem_image.2 ⟨a, haD, rfl⟩), T.card_image_edgeOf] at hcard
  have := T.nonRoot_nonempty.card_pos
  omega

/-- The darts of the edges of the branch at `a_i`. -/
noncomputable abbrev branchDarts (i : ℕ) : Finset H :=
  G.treeDarts (T.branch ((G.rot ^ i) T.intervalStart))

/-- The branch at `a_i` consists of non-root vertices of `T`. -/
theorem branch_subset (i : ℕ) : T.branch ((G.rot ^ i) T.intervalStart) ⊆ T.nonRoot :=
  fun _ hw => ((T.mem_branch).1 hw).1

/-- The darts of the branch at `a_i` are darts of `T`. -/
theorem branchDarts_subset (i : ℕ) : T.branchDarts i ⊆ T.darts := by
  intro d hd
  obtain ⟨hB, h⟩ := G.mem_treeDarts.1 hd
  exact G.mem_treeDarts.2 ⟨hB, h.imp (fun h => T.branch_subset i h) (fun h => T.branch_subset i h)⟩

/-- The ends of an edge of the branch at `a_i` lie in the branch or at the root. -/
theorem vertexOf_mem_branch_or_eq_root (hG : G.IsPlabicGraph) {i : ℕ} {d : H}
    (hd : d ∈ T.branchDarts i) :
    G.vertexOf d ∈ T.branch ((G.rot ^ i) T.intervalStart) ∨ G.vertexOf d = T.root := by
  rcases (G.mem_treeDarts.1 hd).2 with h | h
  · exact Or.inl h
  · have hW := T.branch_subset i h
    have := T.vertexOf_inv_mem (G.inv d) hW
    rw [hG.inv_involutive] at this
    rcases mem_insert.1 this with h' | h'
    · exact Or.inr h'
    · refine Or.inl ((T.mem_branch).2 ⟨h', ((T.mem_branch).1 h).2.tail ⟨hW, h', G.inv d,
        T.inv_mem_darts hG (T.branchDarts_subset i hd), rfl, by rw [hG.inv_involutive]⟩⟩)

/-- The darts of the branch at `a_i` are closed under the involution. -/
theorem inv_mem_branchDarts (hG : G.IsPlabicGraph) {i : ℕ} {d : H} (hd : d ∈ T.branchDarts i) :
    G.inv d ∈ T.branchDarts i := by
  obtain ⟨hB, h⟩ := G.mem_treeDarts.1 hd
  refine G.mem_treeDarts.2 ⟨fun h' => hB (hG.inv_mem_bdry_iff.1 h'), ?_⟩
  rw [hG.inv_involutive]
  exact h.symm

/-- Every dart of `T` is a dart of a branch. -/
theorem exists_mem_branchDarts {d : H} (hd : d ∈ T.darts) :
    ∃ i < T.intervalLength, d ∈ T.branchDarts i := by
  obtain ⟨hB, h⟩ := G.mem_treeDarts.1 hd
  rcases h with h | h
  · obtain ⟨i, hi, hw⟩ := T.exists_mem_branch h
    exact ⟨i, hi, G.mem_treeDarts.2 ⟨hB, Or.inl hw⟩⟩
  · obtain ⟨i, hi, hw⟩ := T.exists_mem_branch h
    exact ⟨i, hi, G.mem_treeDarts.2 ⟨hB, Or.inr hw⟩⟩

/-- The darts of distinct branches are disjoint. -/
theorem disjoint_branchDarts (hG : G.IsPlabicGraph) {i i' : ℕ} (hi : i < T.intervalLength)
    (hi' : i' < T.intervalLength) (hne : i ≠ i') :
    Disjoint (T.branchDarts i) (T.branchDarts i') := by
  rw [Finset.disjoint_left]
  intro d hd hd'
  have hdisj := Finset.disjoint_left.1 (T.disjoint_branch hG hi hi' hne)
  rcases (G.mem_treeDarts.1 hd).2 with h | h
  · rcases T.vertexOf_mem_branch_or_eq_root hG hd' with h' | h'
    · exact hdisj h h'
    · exact T.root_notMem_nonRoot (h' ▸ T.branch_subset i h)
  · rcases T.vertexOf_mem_branch_or_eq_root hG (T.inv_mem_branchDarts hG hd') with h' | h'
    · exact hdisj h h'
    · exact T.root_notMem_nonRoot (h' ▸ T.branch_subset i h)

/-- The dart `a_i` is a dart of the branch at `a_i`. -/
theorem pow_intervalStart_mem_branchDarts {i : ℕ} (hi : i < T.intervalLength) :
    (G.rot ^ i) T.intervalStart ∈ T.branchDarts i :=
  G.mem_treeDarts.2 ⟨T.notMem_bdry_of_mem_darts (T.pow_intervalStart_mem_darts hi),
    Or.inr ((T.mem_branch).2 ⟨T.vertexOf_inv_mem_nonRoot_of_mem_root
      (T.pow_intervalStart_mem_darts hi) (T.pow_intervalStart_mem_root i), .refl⟩)⟩

/-- A path of non-root vertices from the far end of `a_i` is a path in the branch at `a_i`. -/
theorem reflTransGen_treeAdj_branch {i : ℕ} {u : Finset H}
    (h : Relation.ReflTransGen T.NonRootAdj (G.vertexOf (G.inv ((G.rot ^ i) T.intervalStart))) u) :
    Relation.ReflTransGen (G.TreeAdj (T.branch ((G.rot ^ i) T.intervalStart)))
      (G.vertexOf (G.inv ((G.rot ^ i) T.intervalStart))) u := by
  induction h with
  | refl => exact .refl
  | @tail u₁ u₂ h₁ hstep ih =>
    obtain ⟨hu₁, hu₂, d, hd, rfl, rfl⟩ := hstep
    exact ih.tail ⟨d, G.mem_treeDarts.2 ⟨T.notMem_bdry_of_mem_darts hd,
      Or.inl ((T.mem_branch).2 ⟨hu₁, h₁⟩)⟩, rfl, rfl⟩

/-- The branch at `a_i` has at least as many edges as non-root vertices. -/
theorem card_branch_le_card_image_edgeOf_branchDarts (hG : G.IsPlabicGraph) {i : ℕ}
    (hi : i < T.intervalLength) :
    (T.branch ((G.rot ^ i) T.intervalStart)).card ≤ ((T.branchDarts i).image G.edgeOf).card := by
  have h := card_le_card_image_pair_add_one G.vertexOf G.inv hG.inv_involutive (T.branchDarts i)
    (fun d hd => T.inv_mem_branchDarts hG hd) (insert T.root (T.branch ((G.rot ^ i)
      T.intervalStart))) T.root (mem_insert_self _ _)
    (fun d hd => by
      rcases T.vertexOf_mem_branch_or_eq_root hG hd with h | h
      · exact mem_insert_of_mem h
      · exact h ▸ mem_insert_self _ _)
    (fun u hu => by
      rcases mem_insert.1 hu with rfl | hu
      · exact .refl
      · exact Relation.ReflTransGen.head ⟨_, T.pow_intervalStart_mem_branchDarts hi,
          T.mem_root_iff.1 (T.pow_intervalStart_mem_root i), rfl⟩
          (T.reflTransGen_treeAdj_branch ((T.mem_branch).1 hu).2))
  rw [card_insert_of_notMem fun h' => T.root_notMem_nonRoot (T.branch_subset i h')] at h
  exact Nat.le_of_add_le_add_right h

/-- The branch at `a_i` has as many edges as non-root vertices. -/
theorem card_image_edgeOf_branchDarts (hG : G.IsPlabicGraph) {i : ℕ}
    (hi : i < T.intervalLength) :
    ((T.branchDarts i).image G.edgeOf).card = (T.branch ((G.rot ^ i) T.intervalStart)).card := by
  have hinv := hG.inv_involutive
  set k := T.intervalLength
  have hdartsU : T.darts = (range k).biUnion T.branchDarts := by
    ext d
    simp only [mem_biUnion, mem_range]
    exact ⟨T.exists_mem_branchDarts,
      fun ⟨l, _, hl⟩ => T.branchDarts_subset l hl⟩
  have hWU : T.nonRoot = (range k).biUnion fun l => T.branch ((G.rot ^ l) T.intervalStart) := by
    ext w
    simp only [mem_biUnion, mem_range]
    exact ⟨T.exists_mem_branch, fun ⟨l, _, hl⟩ => T.branch_subset l hl⟩
  have hsumD : ∑ l ∈ range k, 2 * ((T.branchDarts l).image G.edgeOf).card = 2 * T.nonRoot.card := by
    rw [← T.card_darts hG, hdartsU, card_biUnion fun l hl l' hl' hne =>
      T.disjoint_branchDarts hG (mem_range.1 hl) (mem_range.1 hl') hne]
    exact sum_congr rfl fun l _ => (G.card_eq_two_mul_card_image_edgeOf hinv hG.inv_ne
      fun d hd => T.inv_mem_branchDarts hG hd).symm
  have hsumW : ∑ l ∈ range k, (T.branch ((G.rot ^ l) T.intervalStart)).card = T.nonRoot.card := by
    rw [hWU, card_biUnion fun l hl l' hl' hne =>
      T.disjoint_branch hG (mem_range.1 hl) (mem_range.1 hl') hne]
  have heq := (sum_eq_sum_iff_of_le (s := range k)
    (f := fun l => 2 * (T.branch ((G.rot ^ l) T.intervalStart)).card)
    (g := fun l => 2 * ((T.branchDarts l).image G.edgeOf).card)
    fun l hl => Nat.mul_le_mul_left 2
      (T.card_branch_le_card_image_edgeOf_branchDarts hG (mem_range.1 hl))).1 (by
      rw [← mul_sum, hsumW, hsumD]) i (mem_range.2 hi)
  omega

/-- The first dart of the interval is the dart of `D_T` at the root whose predecessor is not in
`D_T`. -/
theorem eq_intervalStart_of_rot_symm_notMem {a : H} (ha : a ∈ T.darts) (hr : a ∈ T.root)
    (h : G.rot.symm a ∉ T.darts) : a = T.intervalStart := by
  obtain ⟨j, hj, rfl⟩ := T.exists_eq_pow_of_mem_root ha hr
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rfl
  · exfalso
    apply h
    have : G.rot.symm ((G.rot ^ j) T.intervalStart) = (G.rot ^ (j - 1)) T.intervalStart := by
      rw [Equiv.symm_apply_eq, ← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hj0]
    rw [this]
    exact T.pow_intervalStart_mem_darts (by omega)

/-- The only dart of the branch at `a_i` at the root is `a_i`. -/
theorem eq_of_mem_branchDarts_of_mem_root (hG : G.IsPlabicGraph) {i : ℕ}
    (hi : i < T.intervalLength) {d : H} (hd : d ∈ T.branchDarts i) (hr : d ∈ T.root) :
    d = (G.rot ^ i) T.intervalStart := by
  obtain ⟨l, hl, rfl⟩ := T.exists_eq_pow_of_mem_root (T.branchDarts_subset i hd) hr
  by_contra hne
  have hli : l ≠ i := fun h => hne (by rw [h])
  have h1 : G.vertexOf (G.inv ((G.rot ^ l) T.intervalStart)) ∈
      T.branch ((G.rot ^ i) T.intervalStart) := by
    rcases (G.mem_treeDarts.1 hd).2 with h | h
    · exact absurd (T.mem_root_iff.1 hr ▸ T.branch_subset i h) T.root_notMem_nonRoot
    · exact h
  have h2 : G.vertexOf (G.inv ((G.rot ^ l) T.intervalStart)) ∈
      T.branch ((G.rot ^ l) T.intervalStart) :=
    (T.mem_branch).2 ⟨T.vertexOf_inv_mem_nonRoot_of_mem_root (T.pow_intervalStart_mem_darts hl)
      (T.pow_intervalStart_mem_root l), .refl⟩
  exact Finset.disjoint_left.1 (T.disjoint_branch hG hl hi hli) h2 h1

/-- The root of `T` has at least two darts. -/
theorem one_lt_card_root : 1 < T.root.card := by
  have := T.one_le_intervalLength
  have := T.intervalLength_lt_card
  omega

/-- The predecessor of `a_i` is not a dart of the branch at `a_i`. -/
theorem rot_symm_pow_notMem_branchDarts (hG : G.IsPlabicGraph) {i : ℕ}
    (hi : i < T.intervalLength) : G.rot.symm ((G.rot ^ i) T.intervalStart) ∉ T.branchDarts i := by
  intro h
  have hr : G.rot.symm ((G.rot ^ i) T.intervalStart) ∈ T.root := by
    rw [T.mem_root_iff, ← (T.mem_root_iff).1 (T.pow_intervalStart_mem_root i)]
    exact (G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf _))
  have heq := T.eq_of_mem_branchDarts_of_mem_root hG hi h hr
  have hfix : (G.rot ^ 1) ((G.rot ^ i) T.intervalStart) = (G.rot ^ i) T.intervalStart := by
    rw [pow_one]
    conv_lhs => rw [← heq]
    exact G.rot.apply_symm_apply _
  have := card_vertexOf_le_of_pow_apply_eq one_pos hfix
  rw [T.mem_root_iff.1 (T.pow_intervalStart_mem_root i)] at this
  have := T.one_lt_card_root
  omega

/-- The branch of `T` at `a_i`, as a `RootedTree` with root `v`, non-root vertices `W_i` and
interval `(a_i)`. -/
noncomputable def branchTree (hG : G.IsPlabicGraph) {i : ℕ} (hi : i < T.intervalLength) :
    G.RootedTree where
  root := T.root
  nonRoot := T.branch ((G.rot ^ i) T.intervalStart)
  root_mem_vertices := T.root_mem_vertices
  nonRoot_nonempty := ⟨_, (T.mem_branch).2 ⟨T.vertexOf_inv_mem_nonRoot_of_mem_root
    (T.pow_intervalStart_mem_darts hi) (T.pow_intervalStart_mem_root i), .refl⟩⟩
  nonRoot_subset := (T.branch_subset i).trans T.nonRoot_subset
  root_notMem_nonRoot := fun h => T.root_notMem_nonRoot (T.branch_subset i h)
  vertexOf_inv_mem := fun d hd => by
    have hW := T.branch_subset i hd
    rcases mem_insert.1 (T.vertexOf_inv_mem d hW) with h | h
    · exact h ▸ mem_insert_self _ _
    · exact mem_insert_of_mem ((T.mem_branch).2 ⟨h, ((T.mem_branch).1 hd).2.tail
        ⟨hW, h, d, T.mem_darts_of_vertexOf_mem hW, rfl, rfl⟩⟩)
  exists_interval := by
    refine ⟨(G.rot ^ i) T.intervalStart, T.pow_intervalStart_mem_root i, 1, le_rfl,
      T.one_lt_card_root, fun d hd => ⟨fun h => ⟨0, one_pos, ?_⟩, ?_⟩, ?_⟩
    · exact (T.eq_of_mem_branchDarts_of_mem_root hG hi h hd).symm
    · rintro ⟨j, hj, rfl⟩
      obtain rfl : j = 0 := by omega
      exact T.pow_intervalStart_mem_branchDarts hi
    · exact T.rot_symm_pow_notMem_branchDarts hG hi
  card_image_edgeOf := T.card_image_edgeOf_branchDarts hG hi
  reflTransGen_treeAdj := fun u hu => by
    rcases mem_insert.1 hu with rfl | hu
    · exact .refl
    · exact Relation.ReflTransGen.head ⟨_, T.pow_intervalStart_mem_branchDarts hi,
        T.mem_root_iff.1 (T.pow_intervalStart_mem_root i), rfl⟩
        (T.reflTransGen_treeAdj_branch ((T.mem_branch).1 hu).2)

/-- The root of the branch tree at `a_i` is the root of `T`. -/
theorem branchTree_root (hG : G.IsPlabicGraph) {i : ℕ} (hi : i < T.intervalLength) :
    (T.branchTree hG hi).root = T.root := rfl

/-- The non-root vertices of the branch tree at `a_i` are the branch at `a_i`. -/
theorem branchTree_nonRoot (hG : G.IsPlabicGraph) {i : ℕ} (hi : i < T.intervalLength) :
    (T.branchTree hG hi).nonRoot = T.branch ((G.rot ^ i) T.intervalStart) := rfl

/-- The darts of the branch tree at `a_i` are the darts of the branch at `a_i`. -/
theorem branchTree_darts (hG : G.IsPlabicGraph) {i : ℕ} (hi : i < T.intervalLength) :
    (T.branchTree hG hi).darts = T.branchDarts i := rfl

/-- The interval of the branch tree at `a_i` starts at `a_i`. -/
theorem branchTree_intervalStart (hG : G.IsPlabicGraph) {i : ℕ} (hi : i < T.intervalLength) :
    (T.branchTree hG hi).intervalStart = (G.rot ^ i) T.intervalStart :=
  ((T.branchTree hG hi).eq_intervalStart_of_rot_symm_notMem
    (T.pow_intervalStart_mem_branchDarts hi) (T.pow_intervalStart_mem_root i)
    (T.rot_symm_pow_notMem_branchDarts hG hi)).symm

end RootedTree

/-! ### Transporting a rooted tree along an embedding -/

section Transport

variable {H' : Type} [Fintype H'] [DecidableEq H'] {b' : ℕ} {G' : PlabicData H' b'}

/-- An embedding of the darts of a rooted tree `T` of `G` into the darts of `G'` that respects the
involutions and the rotations along `T`, avoids `B'`, keeps the interval an interval of a vertex of
`G'`, and keeps the colours. -/
structure RootedTree.IsEmbedding (T : G.RootedTree) (G' : PlabicData H' b') (f : H → H') :
    Prop where
  /-- The map `f` is injective on the darts of `T`. -/
  injOn : Set.InjOn f T.darts
  /-- The map `f` commutes with the involutions on the darts of `T`. -/
  map_inv : ∀ d ∈ T.darts, f (G.inv d) = G'.inv (f d)
  /-- The map `f` commutes with the rotations along the darts of `T`. -/
  map_rot : ∀ d ∈ T.darts, G.rot d ∈ T.darts → f (G.rot d) = G'.rot (f d)
  /-- The image of a dart of `T` is not in `B'`. -/
  notMem_bdry : ∀ d ∈ T.darts, f d ∉ G'.bdry
  /-- The rotation of the image of the last dart of the interval is not the image of a dart of
  `T`. -/
  rot_intervalEnd_notMem : G'.rot (f T.intervalEnd) ∉ T.darts.image f
  /-- The inverse rotation of the image of `a₁` is not an image of a dart of `T`. -/
  rot_symm_intervalStart_notMem : G'.rot.symm (f T.intervalStart) ∉ T.darts.image f
  /-- The vertex of the image of `a₁` has more darts than the interval of `T`. -/
  intervalLength_lt_card : T.intervalLength < (G'.vertexOf (f T.intervalStart)).card
  /-- The map `f` preserves colours. -/
  colour : ∀ d ∈ T.darts, G'.colour (f d) = G.colour d

namespace RootedTree.IsEmbedding

variable {T : G.RootedTree} {f : H → H'} (hf : T.IsEmbedding G' f)

include hf

/-- An embedding commutes with the powers of the rotation at a non-root vertex. -/
theorem map_rot_pow_of_vertexOf_mem {d : H} (hd : G.vertexOf d ∈ T.nonRoot) (n : ℕ) :
    f ((G.rot ^ n) d) = (G'.rot ^ n) (f d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : G.vertexOf ((G.rot ^ n) d) ∈ T.nonRoot := by rwa [G.vertexOf_pow_apply]
    rw [pow_succ', Perm.mul_apply, hf.map_rot _ (T.mem_darts_of_vertexOf_mem hn)
      (T.rot_mem_darts_of_vertexOf_mem hn), ih, pow_succ', Perm.mul_apply]

/-- An embedding commutes with the powers of the rotation along the interval. -/
theorem map_rot_pow_intervalStart {j : ℕ} (hj : j < T.intervalLength) :
    f ((G.rot ^ j) T.intervalStart) = (G'.rot ^ j) (f T.intervalStart) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Perm.mul_apply, hf.map_rot _ (T.pow_intervalStart_mem_darts (by omega))
      (by rw [← Perm.mul_apply, ← pow_succ']; exact T.pow_intervalStart_mem_darts hj),
      ih (by omega), pow_succ', Perm.mul_apply]

/-- The image of a non-root vertex is a vertex. -/
theorem vertexOf_map_of_vertexOf_mem {d : H} (hd : G.vertexOf d ∈ T.nonRoot) :
    G'.vertexOf (f d) = (G.vertexOf d).image f := by
  ext y
  rw [RotationSystem.mem_vertexOf, mem_image]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    exact ⟨(G.rot ^ n) d, (G.mem_vertexOf).2 (sameCycle_pow_apply_self _ d n),
      hf.map_rot_pow_of_vertexOf_mem hd n⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨n, rfl⟩ := ((G.mem_vertexOf).1 he).exists_nat_pow_eq
    rw [hf.map_rot_pow_of_vertexOf_mem hd n]
    exact sameCycle_pow_apply_self _ _ n

/-- The image of a dart of the interval lies at the vertex of the image of `a₁`. -/
theorem vertexOf_map_of_mem_root {d : H} (hd : d ∈ T.darts) (hr : d ∈ T.root) :
    G'.vertexOf (f d) = G'.vertexOf (f T.intervalStart) := by
  obtain ⟨j, hj, rfl⟩ := T.exists_eq_pow_of_mem_root hd hr
  rw [hf.map_rot_pow_intervalStart hj, G'.vertexOf_pow_apply]

/-- The image of a dart of `T`: the image of a non-root vertex, or the image root. -/
theorem vertexOf_map_cases (hG : G.IsPlabicGraph) {d : H} (hd : d ∈ T.darts) :
    (G.vertexOf d ∈ T.nonRoot ∧ G'.vertexOf (f d) = (G.vertexOf d).image f) ∨
      (G.vertexOf d = T.root ∧ G'.vertexOf (f d) = G'.vertexOf (f T.intervalStart)) := by
  rcases T.vertexOf_mem_or_eq_root hG hd with h | h
  · exact Or.inl ⟨h, hf.vertexOf_map_of_vertexOf_mem h⟩
  · exact Or.inr ⟨h, hf.vertexOf_map_of_mem_root hd (T.mem_root_iff.2 h)⟩

omit [Fintype H'] [DecidableEq H'] hf in
/-- Every non-root vertex of `T` is the vertex of some dart. -/
theorem exists_vertexOf_eq {w : Finset H} (hw : w ∈ T.nonRoot) :
    ∃ d, G.vertexOf d = w :=
  G.mem_vertices.1 (G.mem_internalVertices.1 (T.nonRoot_subset hw)).1

omit [Fintype H'] [DecidableEq H'] hf in
/-- A dart lying in a non-root vertex `w` of `T` has vertex `w`. -/
theorem vertexOf_eq_of_mem_nonRoot {w : Finset H} (hw : w ∈ T.nonRoot) {e : H}
    (he : e ∈ w) : G.vertexOf e = w := by
  obtain ⟨d, rfl⟩ := exists_vertexOf_eq hw
  exact G.vertexOf_eq_of_mem he

omit [Fintype H'] [DecidableEq H'] hf in
/-- A dart lying in a non-root vertex of `T` is a dart of `T`. -/
theorem mem_darts_of_mem_nonRoot {w : Finset H} (hw : w ∈ T.nonRoot) {e : H} (he : e ∈ w) :
    e ∈ T.darts :=
  T.mem_darts_of_vertexOf_mem ((vertexOf_eq_of_mem_nonRoot hw he).symm ▸ hw)

omit [Fintype H] [DecidableEq H] hf in
/-- A dart whose vertex is the image of a non-root vertex is the image of a dart of that vertex. -/
theorem exists_eq_of_vertexOf_eq {w : Finset H} {x : H'}
    (hx : G'.vertexOf x = w.image f) : ∃ e ∈ w, f e = x := by
  simpa using (hx ▸ G'.self_mem_vertexOf x : x ∈ w.image f)

/-- The images of the non-root vertices are vertices of `G'`. -/
theorem image_eq_vertexOf {w : Finset H} (hw : w ∈ T.nonRoot) :
    ∃ d, w.image f = G'.vertexOf (f d) ∧ G.vertexOf d = w := by
  obtain ⟨d, hd⟩ := exists_vertexOf_eq hw
  exact ⟨d, by rw [hf.vertexOf_map_of_vertexOf_mem (hd ▸ hw), hd], hd⟩

/-- The darts of the transported tree are the images of the darts of `T`. -/
theorem treeDarts_image (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) :
    G'.treeDarts (T.nonRoot.image (Finset.image f)) = T.darts.image f := by
  ext x
  rw [G'.mem_treeDarts, mem_image, mem_image, mem_image]
  constructor
  · rintro ⟨-, ⟨w, hw, hx⟩ | ⟨w, hw, hx⟩⟩
    · obtain ⟨e, he, rfl⟩ := exists_eq_of_vertexOf_eq hx.symm
      exact ⟨e, mem_darts_of_mem_nonRoot hw he, rfl⟩
    · obtain ⟨e, he, hex⟩ := exists_eq_of_vertexOf_eq hx.symm
      have heD := mem_darts_of_mem_nonRoot hw he
      refine ⟨G.inv e, T.inv_mem_darts hG heD, ?_⟩
      rw [hf.map_inv e heD, hex, hG'.inv_involutive]
  · rintro ⟨d, hd, rfl⟩
    refine ⟨hf.notMem_bdry d hd, ?_⟩
    rcases (G.mem_treeDarts.1 hd).2 with h | h
    · exact Or.inl ⟨_, h, (hf.vertexOf_map_of_vertexOf_mem h).symm⟩
    · refine Or.inr ⟨_, h, ?_⟩
      rw [← hf.map_inv d hd, hf.vertexOf_map_of_vertexOf_mem h]

/-- The vertex of the image of a dart of `T`, as the image of its vertex under the map `φ` sending
`v` to the vertex of `f a₁` and a non-root vertex `w` to `f '' w`. -/
theorem vertexOf_map_eq (hG : G.IsPlabicGraph) {d : H} (hd : d ∈ T.darts) :
    G'.vertexOf (f d) = if G.vertexOf d = T.root then G'.vertexOf (f T.intervalStart)
      else (G.vertexOf d).image f := by
  rcases hf.vertexOf_map_cases hG hd with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [if_neg fun h'' : G.vertexOf d = T.root => T.root_notMem_nonRoot (h'' ▸ h), h']
  · rw [if_pos h, h']

/-- The vertex of the image of `a₁` is not the image of a non-root vertex. -/
theorem root_notMem_image : G'.vertexOf (f T.intervalStart) ∉
    T.nonRoot.image (Finset.image f) := by
  intro h
  obtain ⟨w, hw, heq⟩ := mem_image.1 h
  obtain ⟨e, he, hfe⟩ := exists_eq_of_vertexOf_eq heq.symm
  have := hf.injOn (mem_darts_of_mem_nonRoot hw he) T.intervalStart_mem_darts hfe
  rw [← vertexOf_eq_of_mem_nonRoot hw he, this, ← T.root_eq_vertexOf_intervalStart] at hw
  exact T.root_notMem_nonRoot hw

/-- A dart of `T` whose image lies at the vertex of the image of `a₁` lies at the root. -/
theorem mem_root_of_map_mem (hG : G.IsPlabicGraph) {e : H} (heD : e ∈ T.darts)
    (hx : f e ∈ G'.vertexOf (f T.intervalStart)) : e ∈ T.root := by
  rcases hf.vertexOf_map_cases hG heD with ⟨h, h'⟩ | ⟨h, -⟩
  · exfalso
    refine root_notMem_image hf ?_
    rw [← G'.vertexOf_eq_of_mem hx, h']
    exact mem_image_of_mem _ h
  · exact T.mem_root_iff.2 h

/-- The images of the darts of `T` have as many edges as `T` has non-root vertices. -/
theorem card_image_edgeOf_image (hG : G.IsPlabicGraph) :
    ((T.darts.image f).image G'.edgeOf).card = (T.nonRoot.image (Finset.image f)).card := by
  have himg : (T.darts.image f).image G'.edgeOf =
      (T.darts.image G.edgeOf).image (Finset.image f) := by
    rw [image_image, image_image]
    refine image_congr fun d hd => ?_
    simp only [Function.comp, RotationSystem.edgeOf, image_insert, image_singleton,
      hf.map_inv d hd]
  rw [himg, card_image_of_injOn, T.card_image_edgeOf, card_image_of_injOn]
  · have key : ∀ {w w'}, w ∈ T.nonRoot → w' ∈ T.nonRoot → w.image f = w'.image f →
        w ⊆ w' := by
      intro w w' hw hw' heq d hd
      have : f d ∈ w'.image f := heq ▸ mem_image_of_mem f hd
      obtain ⟨d', hd', hfd⟩ := mem_image.1 this
      rwa [← hf.injOn (mem_darts_of_mem_nonRoot hw' hd') (mem_darts_of_mem_nonRoot hw hd) hfd]
    exact fun w hw w' hw' heq => (key hw hw' heq).antisymm (key hw' hw heq.symm)
  · intro e he e' he' heq
    obtain ⟨d, hd, rfl⟩ := mem_image.1 he
    obtain ⟨d', hd', rfl⟩ := mem_image.1 he'
    have hdd : f d ∈ (G.edgeOf d').image f :=
      heq ▸ mem_image_of_mem f (G.mem_edgeOf.2 (Or.inl rfl))
    obtain ⟨d'', hd'', hfd⟩ := mem_image.1 hdd
    have hd''D : d'' ∈ T.darts := by
      rcases G.mem_edgeOf.1 hd'' with rfl | rfl
      · exact hd'
      · exact T.inv_mem_darts hG hd'
    obtain rfl := hf.injOn hd''D hd hfd
    rcases G.mem_edgeOf.1 hd'' with h | h
    · rw [h]
    · rw [h, (G.edgeOf_eq_edgeOf_iff hG.inv_involutive).2 (Or.inr rfl)]

/-- **The transported tree.** -/
noncomputable def tree (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) : G'.RootedTree where
  root := G'.vertexOf (f T.intervalStart)
  nonRoot := T.nonRoot.image (Finset.image f)
  root_mem_vertices := G'.vertexOf_mem_vertices _
  nonRoot_nonempty := T.nonRoot_nonempty.image _
  nonRoot_subset := by
    intro w' hw'
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hw'
    obtain ⟨d, hdw, hd⟩ := image_eq_vertexOf hf hw
    rw [hdw]
    refine G'.mem_internalVertices.2 ⟨G'.vertexOf_mem_vertices _, ?_⟩
    rintro ⟨y, hy, hyB⟩
    rw [← hdw] at hy
    obtain ⟨e, he, rfl⟩ := mem_image.1 hy
    exact hf.notMem_bdry e (mem_darts_of_mem_nonRoot hw he) hyB
  root_notMem_nonRoot := root_notMem_image hf
  vertexOf_inv_mem := by
    intro x hx
    obtain ⟨w, hw, heq⟩ := mem_image.1 hx
    obtain ⟨e, he, rfl⟩ := exists_eq_of_vertexOf_eq heq.symm
    have hew : G.vertexOf e ∈ T.nonRoot := (vertexOf_eq_of_mem_nonRoot hw he).symm ▸ hw
    have heD : e ∈ T.darts := T.mem_darts_of_vertexOf_mem hew
    rw [← hf.map_inv e heD, vertexOf_map_eq hf hG (T.inv_mem_darts hG heD)]
    split_ifs with h
    · exact mem_insert_self _ _
    · rcases mem_insert.1 (T.vertexOf_inv_mem e hew) with h' | h'
      · exact absurd h' h
      · exact mem_insert_of_mem (mem_image_of_mem _ h')
  exists_interval := by
    refine ⟨f T.intervalStart, G'.self_mem_vertexOf _, T.intervalLength, T.one_le_intervalLength,
      hf.intervalLength_lt_card, fun x hx => ?_, ?_⟩
    · rw [treeDarts_image hf hG hG', mem_image]
      constructor
      · rintro ⟨e, heD, rfl⟩
        obtain ⟨j, hj, rfl⟩ := T.exists_eq_pow_of_mem_root heD (hf.mem_root_of_map_mem hG heD hx)
        exact ⟨j, hj, (hf.map_rot_pow_intervalStart hj).symm⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨_, T.pow_intervalStart_mem_darts hj, hf.map_rot_pow_intervalStart hj⟩
    · rw [treeDarts_image hf hG hG']
      exact hf.rot_symm_intervalStart_notMem
  card_image_edgeOf := by
    rw [treeDarts_image hf hG hG']
    exact hf.card_image_edgeOf_image hG
  reflTransGen_treeAdj := by
    intro u' hu'
    let φ : Finset H → Finset H' := fun u =>
      if u = T.root then G'.vertexOf (f T.intervalStart) else u.image f
    have hstep : ∀ u u₂, G.TreeAdj T.nonRoot u u₂ →
        G'.TreeAdj (T.nonRoot.image (Finset.image f)) (φ u) (φ u₂) := by
      rintro _ _ ⟨d, hd, rfl, rfl⟩
      refine ⟨f d, by simpa [treeDarts_image hf hG hG'] using mem_image_of_mem f hd, ?_, ?_⟩
      · exact vertexOf_map_eq hf hG hd
      · rw [← hf.map_inv d hd]
        exact vertexOf_map_eq hf hG (T.inv_mem_darts hG hd)
    have hpath : ∀ u, Relation.ReflTransGen (G.TreeAdj T.nonRoot) T.root u →
        Relation.ReflTransGen (G'.TreeAdj (T.nonRoot.image (Finset.image f)))
          (G'.vertexOf (f T.intervalStart)) (φ u) := by
      intro u hu
      simpa [φ] using Relation.ReflTransGen.lift φ hstep hu
    rcases mem_insert.1 hu' with rfl | hu'
    · exact .refl
    · obtain ⟨w, hw, rfl⟩ := mem_image.1 hu'
      simpa [φ, show w ≠ T.root from fun h => T.root_notMem_nonRoot (h ▸ hw)] using
        hpath w (T.reflTransGen_treeAdj w (mem_insert_of_mem hw))

/-- The root of the transported tree is the vertex of the image of `a₁`. -/
theorem tree_root (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) :
    (hf.tree hG hG').root = G'.vertexOf (f T.intervalStart) := rfl

/-- The darts of the transported tree are the images of the darts of `T`. -/
theorem tree_darts (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) :
    (hf.tree hG hG').darts = T.darts.image f :=
  treeDarts_image hf hG hG'

/-- The interval of the transported tree starts at the image of `a₁`. -/
theorem tree_intervalStart (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) :
    (hf.tree hG hG').intervalStart = f T.intervalStart := by
  refine ((hf.tree hG hG').eq_intervalStart_of_rot_symm_notMem ?_ (G'.self_mem_vertexOf _) ?_).symm
  · rw [tree_darts]
    exact mem_image_of_mem f T.intervalStart_mem_darts
  · rw [tree_darts]
    exact hf.rot_symm_intervalStart_notMem

/-- The bijection from the darts of `P_T` to the darts of the plabic graph of the transported
tree, for internal roots. -/
noncomputable def dartEquiv (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (hv : ¬G.IsBoundaryVertex T.root)
    (hv' : ¬G'.IsBoundaryVertex (G'.vertexOf (f T.intervalStart))) :
    T.Dart ≃ (hf.tree hG hG').Dart :=
  Equiv.ofBijective (fun x => ⟨Sum.map f id x.1, by
    rcases x with ⟨d | (_ | _ | _ | _), hx⟩
    · change f d ∈ (hf.tree hG hG').darts
      rw [tree_darts]
      exact mem_image_of_mem f hx
    all_goals trivial⟩) ⟨by
    rintro ⟨d | l, hx⟩ ⟨d' | l', hy⟩ h <;> simp only [Subtype.mk.injEq, Sum.map_inl,
      Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, id] at h
    · exact Subtype.ext (congrArg Sum.inl (hf.injOn hx hy h))
    · exact Subtype.ext (congrArg Sum.inr h), by
    rintro ⟨d' | l, hx⟩
    · have : d' ∈ T.darts.image f := by rwa [← tree_darts hf hG hG']
      obtain ⟨d, hd, rfl⟩ := mem_image.1 this
      exact ⟨⟨.inl d, hd⟩, rfl⟩
    · refine ⟨⟨.inr l, ?_⟩, rfl⟩
      rcases l with _ | _ | _ | _ <;> trivial⟩

/-- The plabic graph of the transported tree is isomorphic to `P_T`, for internal roots. -/
theorem tree_plabicData_isomorphic (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (hv : ¬G.IsBoundaryVertex T.root)
    (hv' : ¬G'.IsBoundaryVertex (G'.vertexOf (f T.intervalStart))) :
    T.plabicData.Isomorphic (hf.tree hG hG').plabicData := by
  set T' := hf.tree hG hG' with hT'
  have hv'' : ¬G'.IsBoundaryVertex T'.root := hv'
  have hD' : T'.darts = T.darts.image f := tree_darts hf hG hG'
  let e := hf.dartEquiv hG hG' hv hv'
  have he : ∀ x, ((e x : T'.Dart) : H' ⊕ LollipopDart) = Sum.map f id x.1 := fun _ => rfl
  refine ⟨isoOfMapLeg e (fun x => Subtype.ext ?_) (fun x => Subtype.ext ?_) (fun x => ?_)
    (fun x _ => ?_) (fun i => Subtype.ext ?_)⟩
  · rw [he, T'.coe_inv_plabicData hG', he, T.coe_inv_plabicData hG]
    rcases x with ⟨d | l, hx⟩
    · simp only [Sum.map_inl]
      rw [hf.map_inv d hx]
    · rfl
  · rw [he, T'.coe_rot_plabicData hG', he, T.coe_rot_plabicData hG]
    rcases x with ⟨d | (_ | _ | _ | _), hx⟩
    · change Sum.map f id (T.rotAux (.inl d)) = T'.rotAux (.inl (f d))
      simp only [RootedTree.rotAux, if_neg hv, if_neg hv'']
      by_cases h : G.rot d ∈ T.darts
      · rw [if_pos h, if_pos (by rw [hD', ← hf.map_rot d hx h]; exact mem_image_of_mem f h),
          Sum.map_inl, hf.map_rot d hx h]
      · have hend := T.eq_intervalEnd hG hx h
        rw [if_neg h, if_neg (by rw [hD', hend]; exact hf.rot_intervalEnd_notMem)]
        rfl
    · change Sum.map f id (T.rotAux (.inr .e)) = T'.rotAux (.inr .e)
      simp only [RootedTree.rotAux, if_neg hv, if_neg hv'']
      rfl
    · rfl
    · rfl
    · change Sum.map f id (T.rotAux (.inr .gBar)) = T'.rotAux (.inr .gBar)
      simp only [RootedTree.rotAux]
      rw [show T'.intervalStart = f T.intervalStart from tree_intervalStart hf hG hG']
      rfl
  · rw [T'.mem_bdry_plabicData, T.mem_bdry_plabicData]
    rcases x with ⟨d | (_ | _ | _ | _), hx⟩ <;>
      simp [RootedTree.dartE, RootedTree.dartEBar, e, dartEquiv]
  · change T'.colourAux (e x : H' ⊕ LollipopDart) = T.colourAux x.1
    rw [he]
    rcases x with ⟨d | l, hx⟩
    · exact hf.colour d hx
    · change G'.colour T'.intervalStart = G.colour T.intervalStart
      rw [tree_intervalStart hf hG hG']
      exact hf.colour _ T.intervalStart_mem_darts
  · change ((e T.legDart : T'.Dart) : H' ⊕ LollipopDart) = (T'.legDart : H' ⊕ LollipopDart)
    rw [he, RootedTree.legDart, RootedTree.legDart, dif_neg hv, dif_neg hv'']
    rfl

end RootedTree.IsEmbedding

/-- The length of the interval of `T` is the number of darts of `T` at the root. -/
theorem RootedTree.intervalLength_eq_card (T : G.RootedTree) :
    T.intervalLength = (T.root.filter (· ∈ T.darts)).card := by
  have : T.root.filter (· ∈ T.darts) =
      (range T.intervalLength).image fun j => (G.rot ^ j) T.intervalStart := by
    ext d
    simp only [mem_filter, mem_image, mem_range]
    constructor
    · rintro ⟨hr, hd⟩
      exact T.exists_eq_pow_of_mem_root hd hr
    · rintro ⟨j, hj, rfl⟩
      exact ⟨T.pow_intervalStart_mem_root j, T.pow_intervalStart_mem_darts hj⟩
  rw [this, card_image_of_injOn, card_range]
  intro i hi j hj h
  have := T.intervalLength_lt_card
  exact T.pow_intervalStart_injective (by have := mem_range.1 (mem_coe.1 hi); omega)
    (by have := mem_range.1 (mem_coe.1 hj); omega) h

namespace RootedTree.IsEmbedding

variable {T : G.RootedTree} {f : H → H'} (hf : T.IsEmbedding G' f)

include hf

/-- The transported tree has an interval of the same length as `T`. -/
theorem tree_intervalLength (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) :
    (hf.tree hG hG').intervalLength = T.intervalLength := by
  rw [intervalLength_eq_card, intervalLength_eq_card, tree_darts]
  have : (hf.tree hG hG').root.filter (· ∈ T.darts.image f) =
      (T.root.filter (· ∈ T.darts)).image f := by
    ext x
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hx, e, heD, rfl⟩
      exact ⟨e, ⟨hf.mem_root_of_map_mem hG heD hx, heD⟩, rfl⟩
    · rintro ⟨e, ⟨hr, heD⟩, rfl⟩
      have hm : f e ∈ (hf.tree hG hG').root := by
        rw [tree_root, ← hf.vertexOf_map_of_mem_root heD hr]
        exact G'.self_mem_vertexOf _
      exact ⟨hm, e, heD, rfl⟩
  rw [this]
  exact card_image_of_injOn fun x hx y hy h =>
    hf.injOn (mem_filter.1 (Finset.mem_coe.1 hx)).2 (mem_filter.1 (Finset.mem_coe.1 hy)).2 h

end RootedTree.IsEmbedding

end Transport

end PlabicData

end ClusterAlgebras

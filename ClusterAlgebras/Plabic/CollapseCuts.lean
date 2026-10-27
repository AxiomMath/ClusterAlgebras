/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.ReducedCollapse

/-!
# Cuts of plabic tuples and collapses

The removal of a bivalent vertex `{p, σ p}` and the contraction along an edge `{p, p̄}` are both
*cuts*: the tuple on the darts other than `p, q` whose involution and rotation are the first
returns of `ι ∘ (p q)` and `σ ∘ (p q)`. This file develops the first returns of a permutation to a
subset, cuts of plabic tuples, the isomorphisms of collapses matching two families
(`CollapseMatch`), the absorption of a lollipop into a collapse, and shows that the collapse of a
cut is the cut of the collapse. It also collects facts on trees and lollipops used by the collapse
steps.

## Main results

* `ClusterAlgebras.PlabicData.bivalentRemoval_eq_cutData`,
  `ClusterAlgebras.PlabicData.contractEdge_eq_cutData`: bivalent removals and edge contractions
  are cuts.
* `ClusterAlgebras.PlabicData.isomorphic_collapse_of_cut`,
  `ClusterAlgebras.PlabicData.isomorphic_collapse_cut_of_eq`: the collapse of a cut is isomorphic
  to the cut of the collapse.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function _root_.Equiv _root_.Equiv.Perm

/-! ### First returns -/

-- Note: TreeSubstitution.lean has private copies of some of these first-return helpers;
-- `coe_firstReturn_of_simulation` here is the more general form.
section FirstReturn

variable {X X' : Type*}

/-- `z` is reached from `x` by a positive number of steps of `π` whose intermediate points lie
outside `Y`. -/
private def ReachOutside (π : Perm X) (Y : Set X) (x z : X) : Prop :=
  ∃ m, 0 < m ∧ (π ^ m) x = z ∧ ∀ j, 0 < j → j < m → (π ^ j) x ∉ Y

private theorem ReachOutside.single (π : Perm X) (Y : Set X) (x : X) :
    ReachOutside π Y x (π x) :=
  ⟨1, one_pos, by rw [pow_one], fun j hj hj1 => by omega⟩

private theorem ReachOutside.trans {π : Perm X} {Y : Set X} {x w z : X}
    (h₁ : ReachOutside π Y x w) (hw : w ∉ Y) (h₂ : ReachOutside π Y w z) :
    ReachOutside π Y x z := by
  obtain ⟨m, hm, rfl, hmin⟩ := h₁
  obtain ⟨n, hn, rfl, hmin'⟩ := h₂
  refine ⟨n + m, by omega, by rw [pow_add, Perm.mul_apply], fun j hj hjn => ?_⟩
  rcases lt_trichotomy j m with hjm | rfl | hjm
  · exact hmin j hj hjm
  · exact hw
  · have : (π ^ j) x = (π ^ (j - m)) ((π ^ m) x) := by
      rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hjm.le]
    rw [this]
    exact hmin' _ (by omega) (by omega)

private theorem ReachOutside.of_eq {π : Perm X} {Y : Set X} {x z : X} (h : π x = z) :
    ReachOutside π Y x z :=
  h ▸ ReachOutside.single π Y x

private theorem coe_firstReturn_of_reachOutside [Finite X] {π : Perm X} {Y : Set X} {y : Y}
    {z : X} (h : ReachOutside π Y y z) (hz : z ∈ Y) : (firstReturn π Y y : X) = z := by
  obtain ⟨m, hm, rfl, hmin⟩ := h
  exact coe_firstReturn_of_pow hm hz hmin

/-- **Simulation of first returns.** Let `Q` be a set whose complement is invariant under `σ`. If
`φ` maps the points of `K` outside `Q` into `Y` and the other points outside `Q` outside `Y`, and
every step `x ↦ σ x` from a point outside `Q` is followed by a run of `π` from `φ x` to `φ (σ x)`
outside `Y`, then `φ` carries the first return of `σ` to `K` to the first return of `π` to `Y`,
at the points of `K` outside `Q`. -/
private theorem coe_firstReturn_of_simulation [Finite X] [Finite X'] {σ : Perm X} {K : Set X}
    {π : Perm X'} {Y : Set X'} (φ : X → X') (Q : Set X) (hK : ∀ x, x ∉ Q → (φ x ∈ Y ↔ x ∈ K))
    (hQ : ∀ x, x ∉ Q → σ x ∉ Q)
    (hstep : ∀ x, x ∉ Q → ReachOutside π Y (φ x) (φ (σ x))) (x : K) (hxQ : (x : X) ∉ Q) :
    (firstReturn π Y ⟨φ x, (hK x hxQ).2 x.2⟩ : X') = φ (firstReturn σ K x) := by
  have hnQ : ∀ n : ℕ, (σ ^ n) (x : X) ∉ Q := by
    intro n
    induction n with
    | zero => exact hxQ
    | succ n ih => rw [pow_succ', Perm.mul_apply]; exact hQ _ ih
  have hFQ : (firstReturn σ K x : X) ∉ Q := by rw [coe_firstReturn]; exact hnQ _
  apply coe_firstReturn_of_reachOutside _ ((hK _ hFQ).2 (firstReturn σ K x).2)
  rw [coe_firstReturn]
  have key : ∀ n, 0 < n → (∀ j, 0 < j → j < n → (σ ^ j) (x : X) ∉ K) →
      ReachOutside π Y (φ x) (φ ((σ ^ n) x)) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro _ hmin
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hstep x hxQ
      · have h1 := ih hn fun j hj hjn => hmin j hj (by omega)
        have h2 : (σ ^ (n + 1)) (x : X) = σ ((σ ^ n) x) := by rw [pow_succ', Perm.mul_apply]
        rw [h2]
        exact h1.trans (fun h => hmin n hn (by omega) ((hK _ (hnQ n)).1 h)) (hstep _ (hnQ n))
  exact key _ (firstReturnTime_pos x) fun j hj hjm => pow_apply_notMem_of_lt_firstReturnTime hj hjm

/-- A run of `σ` outside `C` from `z` to `w`, started instead by a step `y ↦ π y = σ z` of a
permutation `π` agreeing with `σ` outside `C`, is a run of `π` from `y` to `w` outside `Y ⊆ C`. -/
private theorem ReachOutside.of_head {σ π : Perm X} {C Y : Set X} {y z w : X}
    (hYC : Y ⊆ C) (h : ReachOutside σ C z w) (hy : π y = σ z) (hπ : ∀ u, u ∉ C → π u = σ u) :
    ReachOutside π Y y w := by
  obtain ⟨m, hm, rfl, hmin⟩ := h
  have key : ∀ j, 1 ≤ j → j ≤ m → (π ^ j) y = (σ ^ j) z := by
    intro j hj1 hjm
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simpa using hy
      · rw [pow_succ', Perm.mul_apply, ih hj0 (by omega), hπ _ (hmin j hj0 (by omega)),
          ← Perm.mul_apply, ← pow_succ']
  exact ⟨m, hm, key m hm le_rfl, fun j hj hjm h => hmin j hj hjm (hYC (key j hj hjm.le ▸ h))⟩

/-- The first return of `y` to `Y` agrees with its first return to `Y'` when `Y = Y'`. -/
theorem coe_firstReturn_congr [Finite X] (π : Perm X) {Y Y' : Set X} (hY : Y = Y') (y : X)
    (hy : y ∈ Y) (hy' : y ∈ Y') : (firstReturn π Y ⟨y, hy⟩ : X) = firstReturn π Y' ⟨y, hy'⟩ := by
  subst hY
  rfl

/-- The first return to `S' ⊆ S` of the first return to `S` is the first return to `S'`. -/
theorem coe_coe_firstReturn_firstReturnPerm [Finite X] (π : Perm X) {S : Set X}
    {S' : Set S} {T : Set X} (hT : ∀ x, x ∈ T ↔ ∃ h : x ∈ S, (⟨x, h⟩ : S) ∈ S') (y : S') :
    ((firstReturn (firstReturnPerm π S) S' y : S) : X) =
      firstReturn π T ⟨((y : S) : X), (hT _).2 ⟨(y : S).2, y.2⟩⟩ := by
  set F := firstReturnPerm π S with hFdef
  have hTS : ∀ x : S, (x : X) ∈ T ↔ x ∈ S' := fun x => by
    rw [hT]
    exact ⟨fun ⟨_, h'⟩ => h', fun h => ⟨x.2, h⟩⟩
  have hF : ∀ z : S, ((F z : S) : X) = (π ^ firstReturnTime π S z) z := fun z => by
    rw [hFdef, coe_firstReturnPerm, coe_firstReturn]
  have claim : ∀ k : ℕ, ∀ z : S, 0 < k → (F ^ k) z ∈ S' →
      (∀ j, 0 < j → j < k → (F ^ j) z ∉ S') →
      ∃ n, 0 < n ∧ (π ^ n) (z : X) = (((F ^ k) z : S) : X) ∧
        ∀ j, 0 < j → j < n → (π ^ j) (z : X) ∉ T := by
    intro k
    induction k with
    | zero => intro z h; omega
    | succ k ih =>
      intro z _ hk hmin
      have hm : 0 < firstReturnTime π S z := firstReturnTime_pos z
      have hmS : ∀ j, 0 < j → j < firstReturnTime π S z → (π ^ j) (z : X) ∉ T :=
        fun j hj hjm hT' => pow_apply_notMem_of_lt_firstReturnTime hj hjm ((hT _).1 hT').1
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨_, hm, by rw [zero_add, pow_one, hF], hmS⟩
      · have hk' : (F ^ k) (F z) ∈ S' := by rwa [← Perm.mul_apply, ← pow_succ]
        obtain ⟨n', hn', heq, hmin'⟩ := ih (F z) hk0 hk' fun j hj hjk => by
          rw [← Perm.mul_apply, ← pow_succ]
          exact hmin (j + 1) (by omega) (by omega)
        refine ⟨firstReturnTime π S z + n', by omega, ?_, ?_⟩
        · rw [pow_succ, Perm.mul_apply, ← heq, hF, add_comm, pow_add, Perm.mul_apply]
        · intro j hj hjn
          rcases lt_trichotomy j (firstReturnTime π S z) with hjm | rfl | hjm
          · exact hmS j hj hjm
          · rw [← hF, hTS]
            have := hmin 1 one_pos (by omega)
            rwa [pow_one] at this
          · have : (π ^ j) (z : X) = (π ^ (j - firstReturnTime π S z)) (F z : X) := by
              rw [hF, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hjm.le]
            rw [this]
            exact hmin' _ (by omega) (by omega)
  obtain ⟨n, hn, heq, hmin⟩ := claim (firstReturnTime F S' y) y (firstReturnTime_pos y)
    (pow_firstReturnTime_apply_mem y) fun j hj hjk => pow_apply_notMem_of_lt_firstReturnTime hj hjk
  rw [coe_firstReturn, ← heq]
  refine (coe_firstReturn_of_pow (π := π) (Y := T)
    (y := ⟨((y : S) : X), (hT _).2 ⟨(y : S).2, y.2⟩⟩) hn ?_ hmin).symm
  change (π ^ n) ((y : S) : X) ∈ T
  rw [heq, hTS]
  exact pow_firstReturnTime_apply_mem y

private theorem reachOutside_firstReturn [Finite X] (π : Perm X) (Y : Set X) (y : Y) :
    ReachOutside π Y y (firstReturn π Y y) :=
  ⟨firstReturnTime π Y y, firstReturnTime_pos y, rfl,
    fun _ hj hjm => pow_apply_notMem_of_lt_firstReturnTime hj hjm⟩

private theorem coe_swap_subtype' [DecidableEq X] {S : Set X} (p q y : S) :
    ((swap p q y : S) : X) = swap (p : X) q y := by
  rw [swap_apply_def, swap_apply_def]
  split_ifs <;> simp_all [Subtype.ext_iff]

/-- **A detour through a cycle outside `Y`.** If `q` lies in a union `Q` of cycles of `σ` disjoint
from `Y` and `p ∉ Q`, then `σ ∘ (p q)` runs from `p` to `σ p` through the cycle of `q`, outside
`Y`. -/
private theorem reachOutside_mul_swap [Finite X] [DecidableEq X] {σ : Perm X} {Y Q : Set X}
    {p q : X} (hQ : ∀ x, σ x ∈ Q ↔ x ∈ Q) (hp : p ∉ Q) (hq : q ∈ Q) (hQY : ∀ x ∈ Q, x ∉ Y) :
    ReachOutside (σ * swap p q) Y p (σ p) := by
  set π := σ * swap p q with hπ
  have hex : ∃ m, 0 < m ∧ (σ ^ m) q = q :=
    ⟨orderOf σ, orderOf_pos σ, by rw [pow_orderOf_eq_one, Perm.one_apply]⟩
  classical
  set m := Nat.find hex with hm
  obtain ⟨hm0, hmq⟩ := Nat.find_spec hex
  have hmin : ∀ j, 0 < j → j < m → (σ ^ j) q ≠ q := fun j hj hjm h =>
    Nat.find_min hex hjm ⟨hj, h⟩
  have hQpow : ∀ j : ℕ, (σ ^ j) q ∈ Q := by
    intro j
    induction j with
    | zero => exact hq
    | succ j ih => rw [pow_succ', Perm.mul_apply]; exact (hQ _).2 ih
  have key : ∀ j, 1 ≤ j → j ≤ m → (π ^ j) p = (σ ^ j) q := by
    intro j hj1 hjm
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [zero_add, pow_one, pow_one, hπ, Perm.mul_apply, swap_apply_left]
      · rw [pow_succ', Perm.mul_apply, ih hj0 (by omega), hπ, Perm.mul_apply,
          swap_apply_of_ne_of_ne (fun h => hp (by rw [← h]; exact hQpow j)) (hmin j hj0 (by omega)),
          ← Perm.mul_apply, ← pow_succ']
  refine ⟨m + 1, by omega, ?_, fun j hj hjm => ?_⟩
  · rw [pow_succ', Perm.mul_apply, key m hm0 le_rfl, hmq, hπ, Perm.mul_apply, swap_apply_right]
  · rw [key j hj (by omega)]
    exact hQY _ (hQpow j)

end FirstReturn

/-! ### Graphs given by darts -/


namespace PlabicData

/-! ### Parallel edges of trees -/

section Parallel

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

-- Note: ReducedCollapse.lean has a private copy of this lemma.
/-- In a rooted tree, the two ends of an edge `{d, d̄}` of the tree are not joined by a path of
other edges of the tree. -/
theorem RootedTree.not_reflTransGen_of_mem_darts (hG : G.IsPlabicGraph)
    (T : G.RootedTree) {d : H} (hd : d ∈ T.darts)
    (h : Relation.ReflTransGen (fun u u' => ∃ e ∈ T.darts, e ≠ d ∧ e ≠ G.inv d ∧
      G.vertexOf e = u ∧ G.vertexOf (G.inv e) = u') (G.vertexOf d) (G.vertexOf (G.inv d))) :
    False := by
  have hinv := hG.inv_involutive
  set D' := T.darts.filter fun e => e ≠ d ∧ e ≠ G.inv d with hD'
  have hD'mem : ∀ e, e ∈ D' ↔ e ∈ T.darts ∧ e ≠ d ∧ e ≠ G.inv d := fun e => mem_filter
  set R : Finset H → Finset H → Prop :=
    fun u u' => ∃ e ∈ D', G.vertexOf e = u ∧ G.vertexOf (G.inv e) = u' with hR
  have hRsymm : ∀ u u', R u u' → R u' u := by
    rintro u u' ⟨e, he, rfl, rfl⟩
    obtain ⟨heD, h1, h2⟩ := (hD'mem e).1 he
    refine ⟨G.inv e, (hD'mem _).2 ⟨T.inv_mem_darts hG heD, fun h' => h2 ?_, fun h' => h1 ?_⟩,
      rfl, by rw [hinv]⟩
    · rw [← h', hinv]
    · exact hinv.injective h'
  have hpath : Relation.ReflTransGen R (G.vertexOf d) (G.vertexOf (G.inv d)) := by
    refine Relation.ReflTransGen.mono (fun u u' ⟨e, he, h1, h2, h3, h4⟩ => ?_) h
    exact ⟨e, (hD'mem e).2 ⟨he, h1, h2⟩, h3, h4⟩
  have hconn : ∀ u ∈ insert T.root T.nonRoot, Relation.ReflTransGen R T.root u := by
    intro u hu
    have h0 := T.reflTransGen_treeAdj u hu
    induction h0 with
    | refl => exact .refl
    | @tail u₁ u₂ _ hstep ih =>
      obtain ⟨e, heD, rfl, rfl⟩ := hstep
      have ih' := ih (by
        rcases T.vertexOf_mem_or_eq_root hG heD with h' | h'
        · exact mem_insert_of_mem h'
        · rw [h']; exact mem_insert_self _ _)
      by_cases h1 : e = d
      · subst h1
        exact ih'.trans hpath
      by_cases h2 : e = G.inv d
      · subst h2
        rw [hinv]
        have hrev : ∀ {u u'}, Relation.ReflTransGen R u u' → Relation.ReflTransGen R u' u := by
          intro u u' hp
          induction hp with
          | refl => exact .refl
          | tail _ hs ih => exact Relation.ReflTransGen.head (hRsymm _ _ hs) ih
        exact ih'.trans (hrev hpath)
      · exact ih'.tail ⟨e, (hD'mem e).2 ⟨heD, h1, h2⟩, rfl, rfl⟩
  have hbound := card_le_card_image_pair_add_one G.vertexOf G.inv hinv D'
    (fun e he => by
      obtain ⟨heD, h1, h2⟩ := (hD'mem e).1 he
      refine (hD'mem _).2 ⟨T.inv_mem_darts hG heD, fun h' => h2 (by rw [← h', hinv]),
        fun h' => h1 (hinv.injective h')⟩)
    (insert T.root T.nonRoot) T.root (mem_insert_self _ _)
    (fun e he => by
      rcases T.vertexOf_mem_or_eq_root hG ((hD'mem e).1 he).1 with h' | h'
      · exact mem_insert_of_mem h'
      · rw [h']; exact mem_insert_self _ _) hconn
  rw [card_insert_of_notMem T.root_notMem_nonRoot] at hbound
  have hsub : (D'.image fun e => ({e, G.inv e} : Finset H)) ⊆
      (T.darts.image G.edgeOf).erase (G.edgeOf d) := by
    intro s hs
    obtain ⟨e, he, rfl⟩ := mem_image.1 hs
    obtain ⟨heD, h1, h2⟩ := (hD'mem e).1 he
    refine mem_erase.2 ⟨fun h' => ?_, mem_image.2 ⟨e, heD, rfl⟩⟩
    rcases (G.edgeOf_eq_edgeOf_iff hinv).1 h' with h' | h'
    · exact h1 h'
    · exact h2 h'
  have hcard := card_le_card hsub
  rw [card_erase_of_mem (mem_image.2 ⟨d, hd, rfl⟩), T.card_image_edgeOf] at hcard
  have := T.nonRoot_nonempty.card_pos
  omega

-- Note: ReducedCollapse.lean has a private copy of this lemma.
/-- A rooted tree has no two distinct edges with the same ends. -/
theorem RootedTree.false_of_parallel (hG : G.IsPlabicGraph) (T : G.RootedTree) {d e : H}
    (hd : d ∈ T.darts) (he : e ∈ T.darts) (h1 : e ≠ d) (h2 : e ≠ G.inv d)
    (hv : G.vertexOf e = G.vertexOf d) (hv' : G.vertexOf (G.inv e) = G.vertexOf (G.inv d)) :
    False :=
  T.not_reflTransGen_of_mem_darts hG hd (Relation.ReflTransGen.single ⟨e, he, h1, h2, hv, hv'⟩)

end Parallel

/-! ### Lollipop graphs -/

section Lollipops

variable {H : Type*} [Fintype H] [DecidableEq H]

-- Note: Reduced.lean has a private copy of this lemma.
/-- A plabic graph with one boundary vertex in which the dart across the leg forms a vertex by
itself, of colour `c`, is isomorphic to the lollipop graph `L_c`. -/
theorem lollipopGraph_isomorphic {X : PlabicData H 1} (hX : X.IsPlabicGraph) {c : Shade}
    (h₁ : (X.vertexOf (X.inv (X.leg 0))).card = 1) (hc : X.colour (X.inv (X.leg 0)) = c) :
    (lollipopGraph c).Isomorphic X := by
  have hinv := hX.inv_involutive
  have hdeg := hX.boundaryVertex_card
  have hv₀ : X.IsBoundaryVertex (X.vertexOf (X.leg 0)) :=
    X.vertexOf_mem_boundaryVertices.1 (hX.bvertex_mem 0)
  obtain ⟨ex, hex, hex₀, hiex₀⟩ := hX.exists_exterior 0
  rw [show finRotate 1 0 = 0 from Subsingleton.elim _ _] at hex₀
  have hexB := X.exterior_subset_bdry hex
  have hrex := (X.mem_exterior.1 hex).2
  have hx₀B := hX.leg_notMem_bdry 0
  have hbarB : X.inv ex ∈ X.bdry := hX.inv_mem_bdry _ hexB
  have notB_eq : ∀ y ∈ X.bvertex 0, y ∉ X.bdry → y = X.leg 0 := fun y hy hyB => by
    have : y ∈ (X.bvertex 0).filter (· ∉ X.bdry) := mem_filter.2 ⟨hy, hyB⟩
    rwa [hX.filter_bvertex_notMem_bdry 0, mem_singleton] at this
  have hrot_mem : ∀ y ∈ X.bvertex 0, X.rot y ∈ X.bvertex 0 := fun y hy => by
    unfold bvertex at hy ⊢
    rw [← X.vertexOf_eq_of_mem hy]
    exact X.rot_mem_vertexOf y
  have hne₁ : X.inv ex ≠ ex := hX.inv_ne ex
  have tri : ∀ y ∈ X.bvertex 0, y = ex ∨ y = X.inv ex ∨ y = X.leg 0 := by
    intro y hy
    by_cases hyB : y ∈ X.bdry
    · by_contra hcon
      simp only [not_or] at hcon
      exact DiskMap.not_three_mem_bdry hdeg hv₀ hex₀ hiex₀ hy hexB hbarB hyB hne₁.symm
        (Ne.symm hcon.1) (Ne.symm hcon.2.1)
    · exact Or.inr (Or.inr (notB_eq y hy hyB))
  have e₁ : X.rot ex = X.leg 0 := notB_eq _ (hrot_mem _ hex₀) hrex
  have e₂ : X.rot (X.leg 0) = X.inv ex := by
    rcases tri _ (hrot_mem _ (X.leg_mem_bvertex 0)) with h | h | h
    · exact absurd (by rw [e₁, h]) (DiskMap.rot_rot_ne_of_isBoundaryVertex hdeg
        (X.isBoundaryVertex_vertexOf_of_mem hexB))
    · exact h
    · exact absurd h (DiskMap.rot_ne_of_isBoundaryVertex hdeg hv₀)
  have e₃ : X.rot (X.inv ex) = ex := by
    rcases tri _ (hrot_mem _ hiex₀) with h | h | h
    · exact h
    · exact absurd h (DiskMap.rot_ne_of_isBoundaryVertex hdeg
        (X.isBoundaryVertex_vertexOf_of_mem hbarB))
    · exact absurd (X.rot.injective (h.trans e₁.symm)) hne₁
  have e₄ : X.rot (X.inv (X.leg 0)) = X.inv (X.leg 0) := by
    obtain ⟨a, ha⟩ := card_eq_one.1 h₁
    have m₁ := X.self_mem_vertexOf (X.inv (X.leg 0))
    have m₂ := X.rot_mem_vertexOf (X.inv (X.leg 0))
    rw [ha, mem_singleton] at m₁ m₂
    exact m₂.trans m₁.symm
  have hg₀ : X.inv (X.leg 0) ∉ X.bvertex 0 := fun h =>
    not_isBoundaryVertex_inv_leg' hX (by rwa [X.vertexOf_eq_of_mem h])
  have n₁ : ex ≠ X.inv ex := hne₁.symm
  have n₂ : ex ≠ X.leg 0 := fun h => hx₀B (h ▸ hexB)
  have n₃ : ex ≠ X.inv (X.leg 0) := fun h => hg₀ (h ▸ hex₀)
  have n₄ : X.inv ex ≠ X.leg 0 := fun h => hx₀B (h ▸ hbarB)
  have n₅ : X.inv ex ≠ X.inv (X.leg 0) := fun h => hg₀ (h ▸ hiex₀)
  have n₆ : X.leg 0 ≠ X.inv (X.leg 0) := (hX.inv_ne _).symm
  let f : LollipopDart → H
    | .e => ex
    | .eBar => X.inv ex
    | .g => X.leg 0
    | .gBar => X.inv (X.leg 0)
  have hf : Function.Injective f := by
    intro a a' h
    cases a <;> cases a' <;> first
      | rfl
      | exact absurd h n₁ | exact absurd h n₂ | exact absurd h n₃ | exact absurd h n₄
      | exact absurd h n₅ | exact absurd h n₆ | exact absurd h.symm n₁ | exact absurd h.symm n₂
      | exact absurd h.symm n₃ | exact absurd h.symm n₄ | exact absurd h.symm n₅
      | exact absurd h.symm n₆
  have hsurj : ∀ y, X.Reach ex y → y ∈ Set.range f := by
    intro y hy
    induction hy with
    | refl => exact ⟨.e, rfl⟩
    | rot _ ih =>
      obtain ⟨a, rfl⟩ := ih
      cases a
      exacts [⟨.g, e₁.symm⟩, ⟨.e, e₃.symm⟩, ⟨.eBar, e₂.symm⟩, ⟨.gBar, e₄.symm⟩]
    | inv _ ih =>
      obtain ⟨a, rfl⟩ := ih
      cases a
      exacts [⟨.eBar, rfl⟩, ⟨.e, (hinv ex).symm⟩, ⟨.gBar, rfl⟩, ⟨.g, (hinv _).symm⟩]
  have hL : ∀ d : LollipopDart, (lollipopGraph c).IsBoundaryVertex ((lollipopGraph c).vertexOf d) ∨
      d = .gBar := by
    cases c <;> decide
  have r₁ : (lollipopGraph c).rot .e = .g := by cases c <;> decide
  have r₂ : (lollipopGraph c).rot .eBar = .e := by cases c <;> decide
  have r₃ : (lollipopGraph c).rot .g = .eBar := by cases c <;> decide
  have r₄ : (lollipopGraph c).rot .gBar = .gBar := by cases c <;> decide
  refine ⟨Iso.ofEquivOfMapLeg (Equiv.ofBijective f ⟨hf, fun y => hsurj y (hX.reach ex y)⟩)
    (fun d => ?_) (fun d => ?_) (fun d => ?_) (fun d hd => ?_) fun i => ?_⟩
  · cases d
    exacts [rfl, (hinv ex).symm, rfl, (hinv _).symm]
  · cases d
    · change f ((lollipopGraph c).rot .e) = _
      rw [r₁]
      exact e₁.symm
    · change f ((lollipopGraph c).rot .eBar) = _
      rw [r₂]
      exact e₃.symm
    · change f ((lollipopGraph c).rot .g) = _
      rw [r₃]
      exact e₂.symm
    · change f ((lollipopGraph c).rot .gBar) = _
      rw [r₄]
      exact e₄.symm
  · cases d
    · exact iff_of_true hexB (by cases c <;> decide)
    · exact iff_of_true hbarB (by cases c <;> decide)
    · exact iff_of_false hx₀B (by cases c <;> decide)
    · exact iff_of_false (fun h => hx₀B (hX.inv_mem_bdry_iff.1 h)) (by cases c <;> decide)
  · rcases hL d with h | rfl
    · exact absurd h hd
    · exact hc
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl


end Lollipops

section LollipopColour

/-- The lollipop graph is `ε`-irreducible. -/
private theorem isIrreducible_lollipopPlabicGraph'' (c : Shade) (ε : Fin 2) :
    PlabicGraph.IsIrreducible ε (lollipopPlabicGraph c) := by
  intro Q' hs
  have k₁ : ∀ x : LollipopDart, ((lollipopGraph c).vertexOf x).card ≠ 2 := by
    cases c <;> decide
  have k₂ : ∀ x : LollipopDart, (lollipopGraph c).vertexOf x ∈ (lollipopGraph c).internalVertices →
      (lollipopGraph c).vertexOf ((lollipopGraph c).inv x) ∈ (lollipopGraph c).internalVertices →
      False := by
    cases c <;> decide
  rcases hs with ⟨x, hx, -, -⟩ | ⟨x, hx, -⟩
  · exact k₁ x hx.card_vertexOf
  · exact k₂ x hx.mem_internalVertices hx.inv_mem_internalVertices

/-- Two `{M2, M3}`-equivalent lollipop graphs have the same colour. -/
theorem eq_of_moveEquivalent_lollipopPlabicGraph {c c' : Shade}
    (h : PlabicGraph.MoveEquivalent {.m2, .m3} (lollipopPlabicGraph c)
      (lollipopPlabicGraph c')) : c = c' := by
  have hf : ∀ c, (lollipopPlabicGraph c).data.faces.card = 1 := fun c => by
    change (lollipopGraph c).faces.card = 1
    rw [faces_lollipopGraph]
    rfl
  have hb : ∀ c, (lollipopPlabicGraph c).data.boundaryVertices.card = 1 := fun c =>
    card_boundaryVertices_lollipopGraph c
  obtain ⟨θ⟩ := PlabicGraph.isomorphic_of_moveEquivalent_of_isIrreducible
    (Q := lollipopPlabicGraph c) (Q' := lollipopPlabicGraph c')
    (hb c) (hf c) (hb c') (hf c') h (isIrreducible_lollipopPlabicGraph'' c 0)
    (isIrreducible_lollipopPlabicGraph'' c' 0)
  have hint : ¬(lollipopPlabicGraph c).data.IsBoundaryVertex
      ((lollipopPlabicGraph c).data.vertexOf .gBar) := by
    change ¬(lollipopGraph c).IsBoundaryVertex ((lollipopGraph c).vertexOf .gBar)
    cases c <;> decide
  have h2 := θ.map_colour .gBar hint
  change c' = c at h2
  exact h2.symm

end LollipopColour

section SmallTree

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- A rooted tree with a boundary root and one non-root vertex is the edge of the leg: its darts
are `a₁ = g_i` and `ā₁`, and its non-root vertex is `{ā₁}`. -/
theorem RootedTree.darts_eq_of_card_nonRoot_eq_one (hG : G.IsPlabicGraph)
    (T : G.RootedTree) (_hb : G.IsBoundaryVertex T.root) (h1 : T.nonRoot.card = 1) :
    T.darts = {T.intervalStart, G.inv T.intervalStart} ∧
      G.vertexOf (G.inv T.intervalStart) = {G.inv T.intervalStart} := by
  have ha := T.intervalStart_mem_darts
  have hia := T.inv_mem_darts hG ha
  have hne : T.intervalStart ≠ G.inv T.intervalStart := (hG.inv_ne _).symm
  have hD : T.darts = {T.intervalStart, G.inv T.intervalStart} := by
    refine (eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
    · rcases mem_insert.1 hx with rfl | hx
      · exact ha
      · rwa [mem_singleton.1 hx]
    · rw [T.card_darts hG, h1, card_pair hne]
  refine ⟨hD, ?_⟩
  have hW := T.vertexOf_inv_mem_nonRoot_of_mem_root ha T.intervalStart_mem_root
  refine eq_singleton_iff_unique_mem.2 ⟨G.self_mem_vertexOf _, fun y hy => ?_⟩
  have hyD : y ∈ T.darts := T.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_eq_of_mem hy])
  rw [hD, mem_insert, mem_singleton] at hyD
  rcases hyD with rfl | rfl
  · exfalso
    have : G.vertexOf (G.inv T.intervalStart) = T.root := by
      rw [← G.vertexOf_eq_of_mem hy, ← T.root_eq_vertexOf_intervalStart]
    exact T.root_notMem_nonRoot (this ▸ hW)
  · rfl

/-- The plabic graph of a rooted tree with a boundary root and one non-root vertex `u` is the
lollipop graph of the colour of `u`. -/
theorem RootedTree.lollipop_isomorphic_of_card_nonRoot_eq_one (hG : G.IsPlabicGraph)
    (T : G.RootedTree) (hb : G.IsBoundaryVertex T.root) (h1 : T.nonRoot.card = 1) :
    (lollipopGraph (G.colour (G.inv T.intervalStart))).Isomorphic T.plabicData := by
  obtain ⟨hD, hu⟩ := T.darts_eq_of_card_nonRoot_eq_one hG hb h1
  have hP := T.isPlabicGraph_plabicData hG
  have hia : G.inv T.intervalStart ∈ T.darts := T.inv_mem_darts hG T.intervalStart_mem_darts
  have hleg : T.plabicData.leg 0 = ⟨.inl T.intervalStart, T.intervalStart_mem_darts⟩ := by
    change T.legDart = _
    rw [RootedTree.legDart, dif_pos hb]
  have hinvleg : T.plabicData.inv (T.plabicData.leg 0) = ⟨.inl (G.inv T.intervalStart), hia⟩ := by
    rw [hleg, T.inv_inl hG]
  have hrot : G.rot (G.inv T.intervalStart) = G.inv T.intervalStart := by
    have := G.rot_mem_vertexOf (G.inv T.intervalStart)
    rwa [hu, mem_singleton] at this
  have hrot' : T.plabicData.rot ⟨.inl (G.inv T.intervalStart), hia⟩ =
      ⟨.inl (G.inv T.intervalStart), hia⟩ := by
    rw [T.rot_inl_of_mem hG hia (by rwa [hrot])]
    exact Subtype.ext (by simp [hrot])
  refine lollipopGraph_isomorphic hP ?_ ?_
  · rw [hinvleg]
    refine card_eq_one.2 ⟨_, eq_singleton_iff_unique_mem.2 ⟨T.plabicData.self_mem_vertexOf _,
      fun y hy => ?_⟩⟩
    obtain ⟨n, rfl⟩ := ((T.plabicData.mem_vertexOf).1 hy).exists_nat_pow_eq
    induction n with
    | zero => rfl
    | succ n ih =>
      have hmem : (T.plabicData.rot ^ n) ⟨.inl (G.inv T.intervalStart), hia⟩ ∈
          T.plabicData.vertexOf ⟨.inl (G.inv T.intervalStart), hia⟩ := by
        rw [RotationSystem.mem_vertexOf]
        exact sameCycle_pow_apply_self _ _ _
      rw [pow_succ', Perm.mul_apply, ih hmem, hrot']
  · rw [hinvleg]
    rfl

end SmallTree

/-! ### Cuts -/

section Cut

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {b : ℕ}

-- Note: TreeSubstitution.lean has private copies of `cutData` and its companion lemmas.
/-- The **cut** of `Q` along two darts `p, q`: the tuple on `{p, q}ᶜ` whose involution and rotation
are the first returns of `ι ∘ (p q)` and `σ ∘ (p q)`, with the boundary, colours and legs of `Q`.
Removals of bivalent vertices and contractions of edges are cuts. -/
noncomputable def cutData (Q : PlabicData Y b) (p q : Y)
    (hleg : ∀ i, Q.leg i ∈ ({p, q}ᶜ : Set Y)) : PlabicData ({p, q}ᶜ : Set Y) b where
  inv := firstReturnPerm (Q.inv * swap p q) _
  rot := firstReturnPerm (Q.rot * swap p q) _
  bdry := Q.bdry.subtype (· ∈ ({p, q}ᶜ : Set Y))
  colour y := Q.colour y
  leg i := ⟨Q.leg i, hleg i⟩

omit [Fintype Y] [DecidableEq Y] in
private theorem plabicData_ext {Q Q' : PlabicData Y b} (h₁ : Q.inv = Q'.inv)
    (h₂ : Q.rot = Q'.rot) (h₃ : Q.bdry = Q'.bdry) (h₄ : Q.colour = Q'.colour)
    (h₅ : Q.leg = Q'.leg) : Q = Q' := by
  rcases Q with ⟨⟨⟨i, r⟩, B⟩, c, l⟩
  rcases Q' with ⟨⟨⟨i', r'⟩, B'⟩, c', l'⟩
  simp only at h₁ h₂ h₃ h₄ h₅
  subst h₁ h₂ h₃ h₄ h₅
  rfl

/-- The removal of a bivalent vertex `{d, σ d}` is the cut along `d, σ d`. -/
theorem bivalentRemoval_eq_cutData {Q : PlabicData Y b} (hQ : Q.IsPlabicGraph) {d : Y}
    (hd : Q.IsBivalentRemovable d) :
    Q.bivalentRemoval hQ hd = cutData Q d (Q.rot d) (hd.leg_mem hQ) := by
  have hinv := hQ.inv_involutive
  refine plabicData_ext ?_ ?_ rfl rfl rfl
  · ext y
    have hy := y.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
    change _ = (firstReturn (Q.inv * swap d (Q.rot d)) _ y : Y)
    by_cases h₁ : (y : Y) = Q.inv d
    · rw [coe_bivalentRemoval_inv_of_eq_inv hQ hd h₁]
      have e₁ : ((Q.inv * swap d (Q.rot d)) ^ 1) (y : Y) = d := by
        rw [pow_one, Perm.mul_apply, swap_apply_of_ne_of_ne hy.1 hy.2, h₁, hinv]
      have e₂ : ((Q.inv * swap d (Q.rot d)) ^ 2) (y : Y) = Q.inv (Q.rot d) := by
        rw [pow_succ', Perm.mul_apply, e₁, Perm.mul_apply, swap_apply_left]
      rw [coe_firstReturn_of_pow (m := 2) (by norm_num) (e₂ ▸ hd.inv_rot_mem hQ), e₂]
      intro j hj hj2
      obtain rfl : j = 1 := by omega
      rw [e₁]
      simp
    · by_cases h₂ : (y : Y) = Q.inv (Q.rot d)
      · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hQ hd h₂]
        have e₁ : ((Q.inv * swap d (Q.rot d)) ^ 1) (y : Y) = Q.rot d := by
          rw [pow_one, Perm.mul_apply, swap_apply_of_ne_of_ne hy.1 hy.2, h₂, hinv]
        have e₂ : ((Q.inv * swap d (Q.rot d)) ^ 2) (y : Y) = Q.inv d := by
          rw [pow_succ', Perm.mul_apply, e₁, Perm.mul_apply, swap_apply_right]
        rw [coe_firstReturn_of_pow (m := 2) (by norm_num) (e₂ ▸ hd.inv_mem hQ), e₂]
        intro j hj hj2
        obtain rfl : j = 1 := by omega
        rw [e₁]
        simp
      · rw [coe_bivalentRemoval_inv_of_ne hQ hd h₁ h₂]
        have e : (Q.inv * swap d (Q.rot d)) y = Q.inv y := by
          rw [Perm.mul_apply, swap_apply_of_ne_of_ne hy.1 hy.2]
        have hmem : Q.inv y ∈ ({d, Q.rot d}ᶜ : Set Y) := by
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨fun h => h₁ ((hinv _).symm.trans (congrArg Q.inv h)),
            fun h => h₂ ((hinv _).symm.trans (congrArg Q.inv h))⟩
        rw [coe_firstReturn_of_apply_mem (e ▸ hmem), e]
  · ext y
    have hy := y.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
    change (Q.rot y : Y) = (firstReturn (Q.rot * swap d (Q.rot d)) _ y : Y)
    have e : (Q.rot * swap d (Q.rot d)) y = Q.rot y := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hy.1 hy.2]
    rw [coe_firstReturn_of_apply_mem (e ▸ (hd.rot_mem_iff y).2 y.2), e]

/-- The contraction along `{d, d̄}` is the cut along `d, d̄`. -/
theorem contractEdge_eq_cutData {Q : PlabicData Y b} (hinv : Involutive Q.inv) {d : Y}
    (hleg : ∀ i, Q.leg i ∈ (({d, Q.inv d} : Set Y)ᶜ : Set Y)) :
    Q.contractEdge d hleg = cutData Q d (Q.inv d) hleg := by
  refine plabicData_ext ?_ rfl rfl rfl rfl
  ext y
  change _ = (firstReturn (Q.inv * swap d (Q.inv d)) _ y : Y)
  have hy := mem_compl_pair_iff.1 y.2
  have e : (Q.inv * swap d (Q.inv d)) y = Q.inv y := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hy.1 hy.2]
  rw [coe_contractEdge_inv hinv,
    coe_firstReturn_of_apply_mem (e ▸ (apply_mem_compl_pair_iff hinv d y).2 y.2), e]

variable {Q : PlabicData Y b} {p q : Y} {hleg : ∀ i, Q.leg i ∈ ({p, q}ᶜ : Set Y)}

-- Note: Excision.lean has a private copy of this lemma.
omit [Fintype Y] [DecidableEq Y] in
/-- A dart lies in `{p, q}ᶜ` if and only if it differs from both `p` and `q`. -/
theorem mem_compl_pair {x : Y} : x ∈ ({p, q}ᶜ : Set Y) ↔ x ≠ p ∧ x ≠ q := by
  simp [not_or]

private theorem coe_cutData_inv (x : ({p, q}ᶜ : Set Y)) :
    ((cutData Q p q hleg).inv x : Y) = firstReturn (Q.inv * swap p q) ({p, q}ᶜ : Set Y) x :=
  rfl

private theorem coe_cutData_inv_of_mem {x : ({p, q}ᶜ : Set Y)} (h : Q.inv x ∈ ({p, q}ᶜ : Set Y)) :
    ((cutData Q p q hleg).inv x : Y) = Q.inv x := by
  have hx := mem_compl_pair.1 x.2
  have e : (Q.inv * swap p q) x = Q.inv x := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2]
  rw [coe_cutData_inv, coe_firstReturn_of_apply_mem (e ▸ h), e]

private theorem mem_cutData_bdry {x : ({p, q}ᶜ : Set Y)} :
    x ∈ (cutData Q p q hleg).bdry ↔ (x : Y) ∈ Q.bdry :=
  mem_subtype

end Cut

/-! ### Isomorphisms between collapses -/

section CollapseIso

variable {H H₁ H₂ : Type} [Fintype H] [DecidableEq H] [Fintype H₁] [DecidableEq H₁] [Fintype H₂]
  [DecidableEq H₂] {b : ℕ}

/-- The colour of `ḡ_i` in a collapse is the colour of a member whose tree contains `g_i`, when
all such members have the same colour. -/
theorem collapseColour_inv_leg_of_mem {G : PlabicData H b} (hG : G.IsPlabicGraph)
    {𝒯 : Finset (G.RootedTree × Shade)} {p : G.RootedTree × Shade} (hp : p ∈ 𝒯) {i : Fin b}
    (hi : G.leg i ∈ p.1.darts) (hc : ∀ q ∈ 𝒯, G.leg i ∈ q.1.darts → q.2 = p.2) :
    G.collapseColour 𝒯 (G.inv (G.leg i)) = p.2 := by
  have hex : ∃ q ∈ 𝒯, ∃ j, G.leg j ∈ q.1.darts ∧ G.inv (G.leg i) = G.inv (G.leg j) :=
    ⟨p, hp, i, hi, rfl⟩
  classical
  rw [collapseColour, dif_pos hex]
  obtain ⟨hq, j, hj, hij⟩ := hex.choose_spec
  have hij' : i = j := hG.leg_injective (G.inv.injective hij)
  subst hij'
  exact hc _ hq hj

variable {G₁ : PlabicData H₁ b} {G₂ : PlabicData H₂ b}
  {𝒯₁ : Finset (G₁.RootedTree × Shade)} {𝒯₂ : Finset (G₂.RootedTree × Shade)}

variable (G₁ G₂ 𝒯₁ 𝒯₂) in
/-- The hypotheses under which an injection `j` of darts induces an isomorphism of collapses
`G₂/𝒯₂ → G₁/𝒯₁`: `j` maps the kept darts of `G₂` onto those of `G₁`, the legs to the legs, and
commutes with the involutions and the first returns of the rotations on the kept darts; the labels
whose legs lie in the trees, and the colours of the corresponding members, agree. -/
structure CollapseMatch (j : H₂ → H₁) : Prop where
  /-- `j` is injective. -/
  injective : Injective j
  /-- `j` matches the kept darts. -/
  mem_core_iff : ∀ x, j x ∈ G₁.collapseCore 𝒯₁ ↔ x ∈ G₂.collapseCore 𝒯₂
  /-- Every kept dart of `G₁` comes from a dart of `G₂`. -/
  exists_eq : ∀ y ∈ G₁.collapseCore 𝒯₁, ∃ x, j x = y
  /-- `j` maps legs to legs. -/
  map_leg : ∀ i, j (G₂.leg i) = G₁.leg i
  /-- The labels whose legs lie in the trees agree. -/
  leg_mem_iff : ∀ i, G₂.leg i ∈ G₂.familyDarts 𝒯₂ ↔ G₁.leg i ∈ G₁.familyDarts 𝒯₁
  /-- `j` commutes with the involutions on the kept darts. -/
  map_inv : ∀ x ∈ G₂.collapseCore 𝒯₂, G₂.inv x ∈ G₂.collapseCore 𝒯₂ →
    j (G₂.inv x) = G₁.inv (j x)
  /-- `j` commutes with the first returns of the rotations to the kept darts. -/
  map_rot : ∀ x (hx : x ∈ G₂.collapseCore 𝒯₂),
    j (firstReturn G₂.rot (G₂.collapseCore 𝒯₂) ⟨x, hx⟩) =
      firstReturn G₁.rot (G₁.collapseCore 𝒯₁) ⟨j x, (mem_core_iff x).2 hx⟩
  /-- `j` matches the boundary darts. -/
  mem_bdry_iff : ∀ x ∈ G₂.collapseCore 𝒯₂, j x ∈ G₁.bdry ↔ x ∈ G₂.bdry
  /-- `j` keeps the colours of the kept darts. -/
  colour : ∀ x ∈ G₂.collapseCore 𝒯₂, G₁.colour (j x) = G₂.colour x
  /-- Members of the two families containing the same leg have the same colour. -/
  colour_leg : ∀ i, ∀ p₁ ∈ 𝒯₁, ∀ p₂ ∈ 𝒯₂, G₁.leg i ∈ p₁.1.darts → G₂.leg i ∈ p₂.1.darts →
    p₁.2 = p₂.2
  /-- Members of `𝒯₁` containing the same leg have the same colour. -/
  colour_leg₁ : ∀ i, ∀ p ∈ 𝒯₁, ∀ p' ∈ 𝒯₁, G₁.leg i ∈ p.1.darts → G₁.leg i ∈ p'.1.darts →
    p.2 = p'.2

section CollapseMatchAPI

variable {j : H₂ → H₁} (h : CollapseMatch G₁ G₂ 𝒯₁ 𝒯₂ j) (hG₁ : G₁.IsPlabicGraph)
  (hG₂ : G₂.IsPlabicGraph)

include h hG₁ hG₂

/-- The map of darts of the collapses: `j` on the kept darts, and `ḡ_i ↦ ḡ_i`. -/
noncomputable def CollapseMatch.toFun (x : G₂.collapseDarts 𝒯₂) : G₁.collapseDarts 𝒯₁ :=
  if hx : (x : H₂) ∈ G₂.collapseCore 𝒯₂ then ⟨j x, Or.inl ((h.mem_core_iff x).2 hx)⟩
  else ⟨G₁.inv (j (G₂.inv x)), by
    obtain ⟨i, hi, hxi⟩ := x.2.resolve_left hx
    rw [hxi, hG₂.inv_involutive, h.map_leg]
    exact Or.inr ⟨i, (h.leg_mem_iff i).1 hi, rfl⟩⟩

omit hG₁ in
private theorem CollapseMatch.coe_toFun_of_mem {x : G₂.collapseDarts 𝒯₂}
    (hx : (x : H₂) ∈ G₂.collapseCore 𝒯₂) :
    (h.toFun hG₂ x : H₁) = j x := by
  rw [CollapseMatch.toFun, dif_pos hx]

omit hG₁ in
private theorem CollapseMatch.coe_toFun_inv_leg {x : G₂.collapseDarts 𝒯₂} {i : Fin b}
    (hi : G₂.leg i ∈ G₂.familyDarts 𝒯₂) (hx : (x : H₂) = G₂.inv (G₂.leg i)) :
    (h.toFun hG₂ x : H₁) = G₁.inv (G₁.leg i) := by
  have hx' : (x : H₂) ∉ G₂.collapseCore 𝒯₂ := hx ▸ inv_leg_notMem_collapseCore hG₂ hi
  rw [CollapseMatch.toFun, dif_neg hx']
  change G₁.inv (j (G₂.inv x)) = _
  rw [hx, hG₂.inv_involutive, h.map_leg]

private theorem CollapseMatch.toFun_mem_core_iff (x : G₂.collapseDarts 𝒯₂) :
    (h.toFun hG₂ x : H₁) ∈ G₁.collapseCore 𝒯₁ ↔ (x : H₂) ∈ G₂.collapseCore 𝒯₂ := by
  by_cases hx : (x : H₂) ∈ G₂.collapseCore 𝒯₂
  · rw [h.coe_toFun_of_mem hG₂ hx]
    exact iff_of_true ((h.mem_core_iff x).2 hx) hx
  · obtain ⟨i, hi, hxi⟩ := x.2.resolve_left hx
    rw [h.coe_toFun_inv_leg hG₂ hi hxi]
    exact iff_of_false (inv_leg_notMem_collapseCore hG₁ ((h.leg_mem_iff i).1 hi)) hx

/-- The map of darts of the collapses induced by a `CollapseMatch` is injective. -/
theorem CollapseMatch.toFun_injective : Injective (h.toFun hG₂) := by
  intro x y hxy
  have hcore : (x : H₂) ∈ G₂.collapseCore 𝒯₂ ↔ (y : H₂) ∈ G₂.collapseCore 𝒯₂ := by
    rw [← h.toFun_mem_core_iff hG₁ hG₂ x, ← h.toFun_mem_core_iff hG₁ hG₂ y, hxy]
  by_cases hx : (x : H₂) ∈ G₂.collapseCore 𝒯₂
  · have hy := hcore.1 hx
    have := congrArg Subtype.val hxy
    rw [h.coe_toFun_of_mem hG₂ hx, h.coe_toFun_of_mem hG₂ hy] at this
    exact Subtype.ext (h.injective this)
  · have hy : (y : H₂) ∉ G₂.collapseCore 𝒯₂ := fun hy => hx (hcore.2 hy)
    obtain ⟨i, hi, hxi⟩ := x.2.resolve_left hx
    obtain ⟨i', hi', hyi⟩ := y.2.resolve_left hy
    have := congrArg Subtype.val hxy
    rw [h.coe_toFun_inv_leg hG₂ hi hxi, h.coe_toFun_inv_leg hG₂ hi' hyi] at this
    have hii : i = i' := hG₁.leg_injective (G₁.inv.injective this)
    subst hii
    exact Subtype.ext (hxi.trans hyi.symm)

omit hG₁ in
/-- The map of darts of the collapses induced by a `CollapseMatch` is surjective. -/
theorem CollapseMatch.toFun_surjective : Surjective (h.toFun hG₂) := by
  intro y
  by_cases hy : (y : H₁) ∈ G₁.collapseCore 𝒯₁
  · obtain ⟨x, hx⟩ := h.exists_eq _ hy
    have hxK : x ∈ G₂.collapseCore 𝒯₂ := (h.mem_core_iff x).1 (hx ▸ hy)
    refine ⟨⟨x, Or.inl hxK⟩, Subtype.ext ?_⟩
    rw [h.coe_toFun_of_mem hG₂ hxK]
    exact hx
  · obtain ⟨i, hi, hyi⟩ := y.2.resolve_left hy
    refine ⟨⟨G₂.inv (G₂.leg i), Or.inr ⟨i, (h.leg_mem_iff i).2 hi, rfl⟩⟩, Subtype.ext ?_⟩
    rw [h.coe_toFun_inv_leg hG₂ ((h.leg_mem_iff i).2 hi) rfl, hyi]

/-- **Isomorphism of collapses** from a `CollapseMatch`. -/
noncomputable def CollapseMatch.iso : (G₂.collapse 𝒯₂).Iso (G₁.collapse 𝒯₁) :=
  Iso.ofEquivOfMapLeg (Equiv.ofBijective _ ⟨h.toFun_injective hG₁ hG₂, h.toFun_surjective hG₂⟩)
    (fun x => by
      apply Subtype.ext
      simp only [Equiv.ofBijective_apply]
      have hinv₂ := hG₂.inv_involutive
      have hinv₁ := hG₁.inv_involutive
      rw [coe_collapse_inv hG₁]
      by_cases hx : (x : H₂) ∈ G₂.collapseCore 𝒯₂
      · rw [h.coe_toFun_of_mem hG₂ hx]
        by_cases hix : ((G₂.collapse 𝒯₂).inv x : H₂) ∈ G₂.collapseCore 𝒯₂
        · rw [h.coe_toFun_of_mem hG₂ hix, coe_collapse_inv hG₂]
          rw [coe_collapse_inv hG₂] at hix
          exact h.map_inv x hx hix
        · obtain ⟨i, hi, hxi⟩ := ((G₂.collapse 𝒯₂).inv x).2.resolve_left hix
          rw [h.coe_toFun_inv_leg hG₂ hi hxi]
          rw [coe_collapse_inv hG₂] at hxi
          have : (x : H₂) = G₂.leg i := by rw [← hinv₂ (x : H₂), hxi, hinv₂]
          rw [this, h.map_leg]
      · obtain ⟨i, hi, hxi⟩ := x.2.resolve_left hx
        rw [h.coe_toFun_inv_leg hG₂ hi hxi, hinv₁]
        have hix : ((G₂.collapse 𝒯₂).inv x : H₂) = G₂.leg i := by
          rw [coe_collapse_inv hG₂, hxi, hinv₂]
        rw [h.coe_toFun_of_mem hG₂ (by rw [hix]; exact G₂.leg_mem_collapseCore 𝒯₂ i), hix,
          h.map_leg])
    (fun x => by
      apply Subtype.ext
      simp only [Equiv.ofBijective_apply]
      by_cases hx : (x : H₂) ∈ G₂.collapseCore 𝒯₂
      · have hx' := (h.toFun_mem_core_iff hG₁ hG₂ x).2 hx
        have hr : ((G₂.collapse 𝒯₂).rot x : H₂) ∈ G₂.collapseCore 𝒯₂ := by
          rw [coe_collapse_rot_of_mem hx]; exact Subtype.property _
        rw [h.coe_toFun_of_mem hG₂ hr, coe_collapse_rot_of_mem hx,
          coe_collapse_rot_of_mem hx', h.map_rot x hx]
        have e : (⟨j x, (h.mem_core_iff x).2 hx⟩ : G₁.collapseCore 𝒯₁) = ⟨_, hx'⟩ :=
          Subtype.ext (h.coe_toFun_of_mem hG₂ hx).symm
        rw [e]
      · have hx' : (h.toFun hG₂ x : H₁) ∉ G₁.collapseCore 𝒯₁ :=
          fun h' => hx ((h.toFun_mem_core_iff hG₁ hG₂ x).1 h')
        rw [coe_collapse_rot_of_notMem hx']
        congr 2
        exact Subtype.ext (coe_collapse_rot_of_notMem hx))
    (fun x => by
      simp only [Equiv.ofBijective_apply, mem_collapse_bdry]
      by_cases hx : (x : H₂) ∈ G₂.collapseCore 𝒯₂
      · rw [h.coe_toFun_of_mem hG₂ hx]
        exact h.mem_bdry_iff x hx
      · have hx' : (h.toFun hG₂ x : H₁) ∉ G₁.collapseCore 𝒯₁ :=
          fun h' => hx ((h.toFun_mem_core_iff hG₁ hG₂ x).1 h')
        exact iff_of_false (fun hB => hx' (mem_collapseCore_of_mem_bdry hB))
          (fun hB => hx (mem_collapseCore_of_mem_bdry hB)))
    (fun x _ => by
      change G₁.collapseColour 𝒯₁ (h.toFun hG₂ x) = G₂.collapseColour 𝒯₂ x
      by_cases hx : (x : H₂) ∈ G₂.collapseCore 𝒯₂
      · rw [collapseColour_of_mem_collapseCore hG₂ hx,
          collapseColour_of_mem_collapseCore hG₁ ((h.toFun_mem_core_iff hG₁ hG₂ x).2 hx),
          h.coe_toFun_of_mem hG₂ hx]
        exact h.colour x hx
      · obtain ⟨i, hi, hxi⟩ := x.2.resolve_left hx
        have hi₁ := (h.leg_mem_iff i).1 hi
        obtain ⟨p₂, hp₂, hip₂⟩ := mem_familyDarts.1 hi
        obtain ⟨p₁, hp₁, hip₁⟩ := mem_familyDarts.1 hi₁
        rw [h.coe_toFun_inv_leg hG₂ hi hxi, hxi,
          collapseColour_inv_leg_of_mem hG₁ hp₁ hip₁
            (fun q hq hiq => h.colour_leg₁ i q hq p₁ hp₁ hiq hip₁),
          collapseColour_inv_leg_of_mem hG₂ hp₂ hip₂
            (fun q hq hiq => (h.colour_leg i p₁ hp₁ q hq hip₁ hiq).symm.trans
              (h.colour_leg i p₁ hp₁ p₂ hp₂ hip₁ hip₂))]
        exact h.colour_leg i p₁ hp₁ p₂ hp₂ hip₁ hip₂)
    (fun i => by
      apply Subtype.ext
      simp only [Equiv.ofBijective_apply]
      rw [h.coe_toFun_of_mem hG₂ (G₂.leg_mem_collapseCore 𝒯₂ i)]
      exact h.map_leg i)

end CollapseMatchAPI

end CollapseIso

/-! ### Cutting inside the trees -/

section CutInside

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b} {p q : H}
  {hleg : ∀ i, G.leg i ∈ ({p, q}ᶜ : Set H)}

/-- **Cutting inside the trees.** Let `𝒯` be a family of trees of `G` whose darts contain `p` and
`q`, and `𝒯c` a family of the cut of `G` along `p, q` whose darts are those of `𝒯` other than `p`
and `q`. Suppose that `p` or `q` lies in a union `Q` of cycles of `σ` without kept darts. Then the
collapses are isomorphic: the cut takes place inside the deleted darts. -/
private theorem collapseMatch_cutData (hG : G.IsPlabicGraph)
    (hGc : (cutData G p q hleg).IsPlabicGraph)
    {𝒯 : Finset (G.RootedTree × Shade)}
    {𝒯c : Finset ((cutData G p q hleg).RootedTree × Shade)}
    (hD : ∀ x : ({p, q}ᶜ : Set H),
      x ∈ (cutData G p q hleg).familyDarts 𝒯c ↔ (x : H) ∈ G.familyDarts 𝒯)
    (hp : p ∈ G.familyDarts 𝒯) (hq : q ∈ G.familyDarts 𝒯) (Q : Set H)
    (hQ : ∀ x, G.rot x ∈ Q ↔ x ∈ Q) (hQK : ∀ x ∈ Q, x ∉ G.collapseCore 𝒯) (hpq : p ∈ Q ∨ q ∈ Q)
    (hcol : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯c, G.leg i ∈ p₁.1.darts →
      (cutData G p q hleg).leg i ∈ p₂.1.darts → p₁.2 = p₂.2)
    (hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2) :
    CollapseMatch G (cutData G p q hleg) 𝒯 𝒯c Subtype.val := by
  have hinv := hG.inv_involutive
  have hlegp : ∀ i, G.leg i ≠ p := fun i h => (mem_compl_pair.1 (hleg i)).1 h
  have hlegq : ∀ i, G.leg i ≠ q := fun i h => (mem_compl_pair.1 (hleg i)).2 h
  have hcore : ∀ x : ({p, q}ᶜ : Set H),
      (x : H) ∈ G.collapseCore 𝒯 ↔ x ∈ (cutData G p q hleg).collapseCore 𝒯c := by
    intro x
    change ((x : H) ∉ G.familyDarts 𝒯 ∨ ∃ i, (x : H) = G.leg i) ↔
      (x ∉ (cutData G p q hleg).familyDarts 𝒯c ∨ ∃ i, x = (cutData G p q hleg).leg i)
    rw [hD x]
    refine or_congr Iff.rfl (exists_congr fun i => ?_)
    rw [Subtype.ext_iff]
    rfl
  have hpK : p ∉ G.collapseCore 𝒯 := by
    rintro (h | ⟨i, hi⟩)
    · exact h hp
    · exact hlegp i hi.symm
  have hqK : q ∉ G.collapseCore 𝒯 := by
    rintro (h | ⟨i, hi⟩)
    · exact h hq
    · exact hlegq i hi.symm
  have hmemK : ∀ y ∈ G.collapseCore 𝒯, y ∈ ({p, q}ᶜ : Set H) := fun y hy =>
    mem_compl_pair.2 ⟨fun h => hpK (h ▸ hy), fun h => hqK (h ▸ hy)⟩
  refine
    { injective := Subtype.val_injective
      mem_core_iff := hcore
      exists_eq := fun y hy => ⟨⟨y, hmemK y hy⟩, rfl⟩
      map_leg := fun i => rfl
      leg_mem_iff := fun i => hD _
      map_inv := ?_
      map_rot := ?_
      mem_bdry_iff := fun x _ => mem_cutData_bdry.symm
      colour := fun x _ => rfl
      colour_leg := hcol
      colour_leg₁ := hcol₁ }
  · intro x hx hix
    by_cases h : G.inv x ∈ ({p, q}ᶜ : Set H)
    · exact coe_cutData_inv_of_mem h
    · exfalso
      have hxD : (x : H) ∈ G.familyDarts 𝒯 := by
        have : G.inv x = p ∨ G.inv x = q := by
          by_contra h'
          exact h (mem_compl_pair.2 (not_or.1 h'))
        rcases this with h' | h'
        · have hx' : (x : H) = G.inv p := (hinv (x : H)).symm.trans (congrArg G.inv h')
          rw [hx']
          exact inv_mem_familyDarts hG hp
        · have hx' : (x : H) = G.inv q := (hinv (x : H)).symm.trans (congrArg G.inv h')
          rw [hx']
          exact inv_mem_familyDarts hG hq
      rcases (hcore x).2 hx with h' | ⟨i, hi⟩
      · exact h' hxD
      · have hxi : x = (cutData G p q hleg).leg i := Subtype.ext hi
        have hi' : (cutData G p q hleg).leg i ∈ (cutData G p q hleg).familyDarts 𝒯c := by
          rw [← hxi]; exact (hD x).2 hxD
        have := inv_leg_notMem_collapseCore hGc hi'
        rw [← hxi] at this
        exact this hix
  · intro x hx
    have hT : ∀ y, y ∈ G.collapseCore 𝒯 ↔ ∃ h : y ∈ ({p, q}ᶜ : Set H),
        (⟨y, h⟩ : ({p, q}ᶜ : Set H)) ∈ (cutData G p q hleg).collapseCore 𝒯c := fun y =>
      ⟨fun hy => ⟨hmemK y hy, (hcore ⟨y, _⟩).1 hy⟩, fun ⟨h, hy⟩ => (hcore ⟨y, h⟩).2 hy⟩
    have e1 := coe_coe_firstReturn_firstReturnPerm (G.rot * swap p q) hT ⟨x, hx⟩
    change ((firstReturn (firstReturnPerm (G.rot * swap p q) _) _ ⟨x, hx⟩ : _) : H) = _
    rw [e1]
    have := coe_firstReturn_of_simulation (σ := G.rot) (K := G.collapseCore 𝒯)
      (π := G.rot * swap p q) (Y := G.collapseCore 𝒯) id Q (fun _ _ => Iff.rfl)
      (fun y hy h => hy ((hQ y).1 h)) ?_ ⟨x, (hcore x).2 hx⟩ (fun h => hQK _ h ((hcore x).2 hx))
    · exact this
    intro y hy
    by_cases hyp : y = p
    · subst hyp
      rcases hpq with h | h
      · exact absurd h hy
      · exact reachOutside_mul_swap hQ hy h hQK
    by_cases hyq : y = q
    · subst hyq
      rcases hpq with h | h
      · rw [swap_comm]
        exact reachOutside_mul_swap hQ hy h hQK
      · exact absurd h hy
    exact ReachOutside.of_eq (by simp only [id, Perm.mul_apply, swap_apply_of_ne_of_ne hyp hyq])

end CutInside

/-! ### Absorbing a lollipop into a tree -/

section Absorb

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- The dart `ḡ_i` of a leg in the trees of a family is not a leg. -/
theorem inv_leg_ne_leg (hG : G.IsPlabicGraph) {𝒯 : Finset (G.RootedTree × Shade)}
    {i : Fin b} (hi : G.leg i ∈ G.familyDarts 𝒯) (j : Fin b) : G.inv (G.leg i) ≠ G.leg j := by
  obtain ⟨p, -, hp⟩ := mem_familyDarts.1 hi
  exact p.1.ne_leg_of_vertexOf_mem hG (p.1.vertexOf_inv_leg_mem hG hp) j

/-- **Absorbing a lollipop.** Let `𝒯₂` be a family whose darts are those of `𝒯₁` together with a
leg `g_i` and the dart `ℓ = ḡ_i`, where `g_i ∉ D(𝒯₁)` and all darts at the vertex of `ℓ` other than
`ℓ` lie in `D(𝒯₁)`. In `G/𝒯₁` the vertex of `ℓ` is a lollipop `{ℓ}` at `i`; in `G/𝒯₂` the dart
`ℓ = ḡ_i` is the lollipop produced by the collapse. If the colours match, the collapses are
isomorphic. -/
noncomputable def collapseIsoAbsorb (hG : G.IsPlabicGraph)
    {𝒯₁ 𝒯₂ : Finset (G.RootedTree × Shade)} {i : Fin b}
    (hD : ∀ x, x ∈ G.familyDarts 𝒯₂ ↔
      x ∈ G.familyDarts 𝒯₁ ∨ x = G.leg i ∨ x = G.inv (G.leg i))
    (hi : G.leg i ∉ G.familyDarts 𝒯₁)
    (hfix : ∀ y ∈ G.vertexOf (G.inv (G.leg i)), y ≠ G.inv (G.leg i) → y ∈ G.familyDarts 𝒯₁)
    (hcol : ∀ p ∈ 𝒯₂, G.leg i ∈ p.1.darts → p.2 = G.colour (G.inv (G.leg i)))
    (hcolj : ∀ j, ∀ p₁ ∈ 𝒯₁, ∀ p₂ ∈ 𝒯₂, G.leg j ∈ p₁.1.darts → G.leg j ∈ p₂.1.darts →
      p₁.2 = p₂.2)
    (hcol₁ : ∀ j, ∀ p ∈ 𝒯₁, ∀ p' ∈ 𝒯₁, G.leg j ∈ p.1.darts → G.leg j ∈ p'.1.darts →
      p.2 = p'.2) :
    (G.collapse 𝒯₁).Iso (G.collapse 𝒯₂) := by
  have hinv := hG.inv_involutive
  set ℓ := G.inv (G.leg i) with hℓ
  have hi₂ : G.leg i ∈ G.familyDarts 𝒯₂ := (hD _).2 (Or.inr (Or.inl rfl))
  have hℓleg : ∀ j, ℓ ≠ G.leg j := inv_leg_ne_leg hG hi₂
  have hℓD : ℓ ∉ G.familyDarts 𝒯₁ := fun h => hi (by
    have := inv_mem_familyDarts hG h
    rwa [hℓ, hinv] at this)
  have hℓK : ℓ ∈ G.collapseCore 𝒯₁ := Or.inl hℓD
  have hK₂ : ∀ x, x ∈ G.collapseCore 𝒯₂ ↔ x ∈ G.collapseCore 𝒯₁ ∧ x ≠ ℓ := by
    intro x
    change (x ∉ G.familyDarts 𝒯₂ ∨ ∃ j, x = G.leg j) ↔
      (x ∉ G.familyDarts 𝒯₁ ∨ ∃ j, x = G.leg j) ∧ x ≠ ℓ
    rw [hD]
    constructor
    · rintro (h | ⟨j, rfl⟩)
      · push Not at h
        exact ⟨Or.inl h.1, h.2.2⟩
      · exact ⟨Or.inr ⟨j, rfl⟩, (hℓleg j).symm⟩
    · rintro ⟨h | ⟨j, rfl⟩, hne⟩
      · by_cases hxi : x = G.leg i
        · exact Or.inr ⟨i, hxi⟩
        · exact Or.inl fun h' => by rcases h' with h' | h' | h' <;> tauto
      · exact Or.inr ⟨j, rfl⟩
  have hI : ∀ j, G.leg j ∈ G.familyDarts 𝒯₂ ↔ G.leg j ∈ G.familyDarts 𝒯₁ ∨ j = i := by
    intro j
    rw [hD]
    refine or_congr Iff.rfl ⟨fun h => ?_, fun h => Or.inl (h ▸ rfl)⟩
    rcases h with h | h
    · exact hG.leg_injective h
    · exact absurd h.symm (hℓleg j)
  have hS : ∀ x, x ∈ G.collapseDarts 𝒯₁ ↔ x ∈ G.collapseDarts 𝒯₂ := by
    intro x
    change (x ∈ G.collapseCore 𝒯₁ ∨ ∃ j, G.leg j ∈ G.familyDarts 𝒯₁ ∧ x = G.inv (G.leg j)) ↔
      (x ∈ G.collapseCore 𝒯₂ ∨ ∃ j, G.leg j ∈ G.familyDarts 𝒯₂ ∧ x = G.inv (G.leg j))
    rw [hK₂]
    simp only [hI]
    constructor
    · rintro (h | ⟨j, hj, rfl⟩)
      · by_cases hxℓ : x = ℓ
        · exact Or.inr ⟨i, Or.inr rfl, hxℓ⟩
        · exact Or.inl ⟨h, hxℓ⟩
      · exact Or.inr ⟨j, Or.inl hj, rfl⟩
    · rintro (⟨h, -⟩ | ⟨j, hj | rfl, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, rfl⟩
      · exact Or.inl hℓK
  -- the vertex of `ℓ` meets the kept darts of `𝒯₁` in `ℓ` alone
  have hvℓ : ∀ y ∈ G.vertexOf ℓ, y ∈ G.collapseCore 𝒯₁ → y = ℓ := by
    intro y hy hyK
    by_contra hne
    rcases hyK with h | ⟨j, rfl⟩
    · exact h (hfix y hy hne)
    · have hb : G.IsBoundaryVertex (G.vertexOf (G.leg j)) :=
        G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j)
      obtain ⟨p, -, hp⟩ := mem_familyDarts.1 hi₂
      have hW := p.1.vertexOf_inv_leg_mem hG hp
      rw [← hℓ, ← G.vertexOf_eq_of_mem hy] at hW
      exact (G.mem_internalVertices.1 (p.1.nonRoot_subset hW)).2 hb
  have hFR : ∀ x : G.collapseCore 𝒯₁, (firstReturn G.rot (G.collapseCore 𝒯₁) x : H) = ℓ →
      (x : H) = ℓ := by
    intro x hx
    have hmem : (x : H) ∈ G.vertexOf ℓ := by
      rw [← hx, coe_firstReturn]
      exact (G.mem_vertexOf).2 (sameCycle_pow_apply_self _ _ _).symm
    exact hvℓ _ hmem x.2
  refine Iso.ofEquivOfMapLeg (Equiv.subtypeEquivRight hS) (fun x => ?_) (fun x => ?_)
    (fun x => ?_) (fun x _ => ?_) (fun j => rfl)
  · apply Subtype.ext
    change ((G.collapse 𝒯₁).inv x : H) = ((G.collapse 𝒯₂).inv ⟨x, (hS x).1 x.2⟩ : H)
    rw [coe_collapse_inv hG, coe_collapse_inv hG]
  · apply Subtype.ext
    change ((G.collapse 𝒯₁).rot x : H) = ((G.collapse 𝒯₂).rot ⟨x, (hS x).1 x.2⟩ : H)
    by_cases hx₂ : (x : H) ∈ G.collapseCore 𝒯₂
    · have hx₁ := ((hK₂ x).1 hx₂).1
      rw [coe_collapse_rot_of_mem hx₁, coe_collapse_rot_of_mem (x := ⟨(x : H), (hS x).1 x.2⟩) hx₂]
      have hT : ∀ y, y ∈ G.collapseCore 𝒯₂ ↔ ∃ h : y ∈ G.collapseCore 𝒯₁,
          (⟨y, h⟩ : G.collapseCore 𝒯₁) ∈ {z : G.collapseCore 𝒯₁ | (z : H) ∈ G.collapseCore 𝒯₂} :=
        fun y => ⟨fun h => ⟨((hK₂ y).1 h).1, h⟩, fun ⟨_, h⟩ => h⟩
      have e1 := coe_coe_firstReturn_firstReturnPerm G.rot hT
        (⟨⟨x, hx₁⟩, hx₂⟩ : {z : G.collapseCore 𝒯₁ | (z : H) ∈ G.collapseCore 𝒯₂})
      have hmem : firstReturnPerm G.rot (G.collapseCore 𝒯₁) ⟨x, hx₁⟩ ∈
          {z : G.collapseCore 𝒯₁ | (z : H) ∈ G.collapseCore 𝒯₂} := by
        change ((firstReturnPerm G.rot (G.collapseCore 𝒯₁) ⟨x, hx₁⟩ :
          G.collapseCore 𝒯₁) : H) ∈ G.collapseCore 𝒯₂
        rw [coe_firstReturnPerm, hK₂]
        refine ⟨Subtype.property _, fun h => ((hK₂ x).1 hx₂).2 (hFR _ h)⟩
      rwa [coe_firstReturn_of_apply_mem hmem, coe_firstReturnPerm] at e1
    · rw [coe_collapse_rot_of_notMem (x := ⟨(x : H), (hS x).1 x.2⟩) hx₂]
      by_cases hx₁ : (x : H) ∈ G.collapseCore 𝒯₁
      · have hxℓ : (x : H) = ℓ := not_not.1 fun h => hx₂ ((hK₂ x).2 ⟨hx₁, h⟩)
        rw [coe_collapse_rot_of_mem hx₁]
        have hmem : (firstReturn G.rot (G.collapseCore 𝒯₁) ⟨x, hx₁⟩ : H) ∈ G.vertexOf ℓ := by
          rw [coe_firstReturn, ← hxℓ]
          exact (G.mem_vertexOf).2 (sameCycle_pow_apply_self _ _ _)
        rw [hvℓ _ hmem (Subtype.property _), hxℓ]
      · rw [coe_collapse_rot_of_notMem hx₁]
  · change ⟨x, (hS x).1 x.2⟩ ∈ (G.collapse 𝒯₂).bdry ↔ x ∈ (G.collapse 𝒯₁).bdry
    rw [mem_collapse_bdry, mem_collapse_bdry]
  · change G.collapseColour 𝒯₂ x = G.collapseColour 𝒯₁ x
    by_cases hx₂ : (x : H) ∈ G.collapseCore 𝒯₂
    · rw [collapseColour_of_mem_collapseCore hG hx₂,
        collapseColour_of_mem_collapseCore hG ((hK₂ x).1 hx₂).1]
    by_cases hx₁ : (x : H) ∈ G.collapseCore 𝒯₁
    · have hxℓ : (x : H) = ℓ := not_not.1 fun h => hx₂ ((hK₂ x).2 ⟨hx₁, h⟩)
      rw [collapseColour_of_mem_collapseCore hG hx₁, hxℓ]
      obtain ⟨p, hp, hip⟩ := mem_familyDarts.1 hi₂
      rw [collapseColour_inv_leg_of_mem hG hp hip
        (fun q hq hiq => (hcol q hq hiq).trans (hcol p hp hip).symm)]
      exact hcol p hp hip
    · obtain ⟨j, hj, hxj⟩ := x.2.resolve_left hx₁
      obtain ⟨p₁, hp₁, hjp₁⟩ := mem_familyDarts.1 hj
      obtain ⟨p₂, hp₂, hjp₂⟩ := mem_familyDarts.1 ((hI j).2 (Or.inl hj))
      rw [hxj, collapseColour_inv_leg_of_mem hG hp₁ hjp₁
          (fun q hq hjq => hcol₁ j q hq p₁ hp₁ hjq hjp₁),
        collapseColour_inv_leg_of_mem hG hp₂ hjp₂ (fun q hq hjq =>
          (hcolj j p₁ hp₁ q hq hjp₁ hjq).symm.trans (hcolj j p₁ hp₁ p₂ hp₂ hjp₁ hjp₂))]
      exact (hcolj j p₁ hp₁ p₂ hp₂ hjp₁ hjp₂).symm

end Absorb

/-! ### Cutting outside the trees -/

section CutOutside

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b} {p q : H}
  {hleg : ∀ i, G.leg i ∈ ({p, q}ᶜ : Set H)}

/-- A dart outside the trees of a family is a dart of the collapse. -/
private theorem mem_collapseDarts_of_notMem {𝒯 : Finset (G.RootedTree × Shade)} {x : H}
    (hx : x ∉ G.familyDarts 𝒯) : x ∈ G.collapseDarts 𝒯 :=
  Or.inl (Or.inl hx)

/-- The legs of the collapse avoid the darts `p, q` of the cut. -/
private theorem collapse_leg_mem_compl (hleg' : ∀ i, G.leg i ∈ ({p, q}ᶜ : Set H))
    {𝒯 : Finset (G.RootedTree × Shade)} (hp : p ∉ G.familyDarts 𝒯) (hq : q ∉ G.familyDarts 𝒯)
    (i : Fin b) :
    (G.collapse 𝒯).leg i ∈ ({(⟨p, mem_collapseDarts_of_notMem hp⟩ : G.collapseDarts 𝒯),
      ⟨q, mem_collapseDarts_of_notMem hq⟩}ᶜ : Set (G.collapseDarts 𝒯)) := by
  have h := mem_compl_pair.1 (hleg' i)
  exact mem_compl_pair.2 ⟨fun h' => h.1 (congrArg Subtype.val h'),
    fun h' => h.2 (congrArg Subtype.val h')⟩

variable (hG : G.IsPlabicGraph) (hGc : (cutData G p q hleg).IsPlabicGraph)
  {𝒯 : Finset (G.RootedTree × Shade)} {𝒯c : Finset ((cutData G p q hleg).RootedTree × Shade)}
  (hD : ∀ x : ({p, q}ᶜ : Set H),
    x ∈ (cutData G p q hleg).familyDarts 𝒯c ↔ (x : H) ∈ G.familyDarts 𝒯)
  (hp : p ∉ G.familyDarts 𝒯) (hq : q ∉ G.familyDarts 𝒯)

include hG hGc hD hp hq

omit hG hGc hp hq in
private theorem cutOutside_mem_core_iff (x : ({p, q}ᶜ : Set H)) :
    x ∈ (cutData G p q hleg).collapseCore 𝒯c ↔ (x : H) ∈ G.collapseCore 𝒯 := by
  change (x ∉ (cutData G p q hleg).familyDarts 𝒯c ∨ ∃ i, x = (cutData G p q hleg).leg i) ↔
    ((x : H) ∉ G.familyDarts 𝒯 ∨ ∃ i, (x : H) = G.leg i)
  rw [hD x]
  refine or_congr Iff.rfl (exists_congr fun i => ?_)
  rw [Subtype.ext_iff]
  rfl

omit hGc hD in
private theorem cutOutside_inv_leg {i : Fin b} (hi : G.leg i ∈ G.familyDarts 𝒯) :
    G.inv (G.leg i) ∈ ({p, q}ᶜ : Set H) := by
  have := inv_mem_familyDarts hG hi
  exact mem_compl_pair.2 ⟨fun h => hp (h ▸ this), fun h => hq (h ▸ this)⟩

omit hGc in
private theorem cutOutside_mem_darts_iff (x : ({p, q}ᶜ : Set H)) :
    x ∈ (cutData G p q hleg).collapseDarts 𝒯c ↔ (x : H) ∈ G.collapseDarts 𝒯 := by
  change (x ∈ (cutData G p q hleg).collapseCore 𝒯c ∨
      ∃ i, (cutData G p q hleg).leg i ∈ (cutData G p q hleg).familyDarts 𝒯c ∧
        x = (cutData G p q hleg).inv ((cutData G p q hleg).leg i)) ↔
    ((x : H) ∈ G.collapseCore 𝒯 ∨ ∃ i, G.leg i ∈ G.familyDarts 𝒯 ∧ (x : H) = G.inv (G.leg i))
  rw [cutOutside_mem_core_iff hD]
  refine or_congr Iff.rfl (exists_congr fun i => ?_)
  constructor
  · rintro ⟨hi, hx⟩
    have hi' : G.leg i ∈ G.familyDarts 𝒯 := (hD _).1 hi
    refine ⟨hi', ?_⟩
    rw [hx, coe_cutData_inv_of_mem (x := (cutData G p q hleg).leg i)
      (cutOutside_inv_leg hG hp hq hi')]
    rfl
  · rintro ⟨hi, hx⟩
    refine ⟨(hD _).2 hi, Subtype.ext ?_⟩
    rw [coe_cutData_inv_of_mem (x := (cutData G p q hleg).leg i)
      (cutOutside_inv_leg hG hp hq hi), hx]
    rfl

/-- **Cutting outside the trees.** If the darts `p, q` lie outside the trees of `𝒯`, and `𝒯c` is a
family of the cut of `G` along `p, q` with the same darts, then the collapse of the cut is
isomorphic to the cut of the collapse. -/
private noncomputable def collapseCutIso
    (hcol : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯c, G.leg i ∈ p₁.1.darts →
      (cutData G p q hleg).leg i ∈ p₂.1.darts → p₁.2 = p₂.2)
    (hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2) :
    ((cutData G p q hleg).collapse 𝒯c).Iso
      (cutData (G.collapse 𝒯) ⟨p, mem_collapseDarts_of_notMem hp⟩
        ⟨q, mem_collapseDarts_of_notMem hq⟩ (collapse_leg_mem_compl hleg hp hq)) := by
  set S := G.collapseDarts 𝒯 with hSdef
  set p' : S := ⟨p, mem_collapseDarts_of_notMem hp⟩ with hp'
  set q' : S := ⟨q, mem_collapseDarts_of_notMem hq⟩ with hq'
  have hpK : p ∈ G.collapseCore 𝒯 := Or.inl hp
  have hqK : q ∈ G.collapseCore 𝒯 := Or.inl hq
  have hswap : ∀ y : S, (y : H) ∈ G.collapseCore 𝒯 →
      ((swap p' q' y : S) : H) ∈ G.collapseCore 𝒯 := by
    intro y hy
    rw [coe_swap_subtype']
    rcases eq_or_ne (y : H) p with h | h
    · rwa [h, swap_apply_left]
    rcases eq_or_ne (y : H) q with h' | h'
    · rwa [h', swap_apply_right]
    rwa [swap_apply_of_ne_of_ne h h']
  have hK' : ∀ y : S, (y : H) ∈ ({p, q}ᶜ : Set H) ↔ y ∈ ({p', q'}ᶜ : Set S) := by
    intro y
    rw [mem_compl_pair, mem_compl_pair, Ne, Ne, Ne, Ne, Subtype.ext_iff, Subtype.ext_iff]
  let e : (cutData G p q hleg).collapseDarts 𝒯c ≃ ({p', q'}ᶜ : Set S) :=
    { toFun := fun x => ⟨⟨x.1.1, (cutOutside_mem_darts_iff hG hD hp hq x.1).1 x.2⟩,
        (hK' _).1 x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, (hK' _).2 y.2⟩,
        (cutOutside_mem_darts_iff hG hD hp hq _).2 y.1.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have he : ∀ x, ((e x : S) : H) = ((x : ({p, q}ᶜ : Set H)) : H) := fun x => rfl
  have hcolc : ∀ i, ∀ p₁ ∈ 𝒯c, ∀ p₂ ∈ 𝒯c, (cutData G p q hleg).leg i ∈ p₁.1.darts →
      (cutData G p q hleg).leg i ∈ p₂.1.darts → p₁.2 = p₂.2 := by
    intro i p₁ hp₁ p₂ hp₂ h₁ h₂
    have hi : G.leg i ∈ G.familyDarts 𝒯 := (hD _).1 (mem_familyDarts.2 ⟨p₁, hp₁, h₁⟩)
    obtain ⟨r, hr, hir⟩ := mem_familyDarts.1 hi
    exact (hcol i r hr p₁ hp₁ hir h₁).symm.trans (hcol i r hr p₂ hp₂ hir h₂)
  refine Iso.ofEquivOfMapLeg e (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x _ => ?_)
    (fun i => rfl)
  · -- the involutions
    apply Subtype.ext
    apply Subtype.ext
    rw [he, coe_collapse_inv hGc, coe_cutData_inv]
    change _ = ((firstReturn ((G.collapse 𝒯).inv * swap p' q') ({p', q'}ᶜ : Set S) (e x) :
      S) : H)
    exact coe_firstReturn_of_simulation (σ := (G.collapse 𝒯).inv * swap p' q')
      (K := ({p', q'}ᶜ : Set S)) (π := G.inv * swap p q) (Y := ({p, q}ᶜ : Set H))
      Subtype.val ∅ (fun y _ => hK' y) (fun _ h => h) (fun y _ => ReachOutside.of_eq (by
        rw [Perm.mul_apply, Perm.mul_apply, coe_collapse_inv hG, coe_swap_subtype']))
      (e x) (Set.notMem_empty _)
  · -- the rotations
    apply Subtype.ext
    apply Subtype.ext
    rw [he]
    change (((cutData G p q hleg).collapse 𝒯c).rot x : H) =
      ((firstReturn ((G.collapse 𝒯).rot * swap p' q') ({p', q'}ᶜ : Set S) (e x) : S) : H)
    by_cases hx : ((x : ({p, q}ᶜ : Set H)) : H) ∈ G.collapseCore 𝒯
    · have hxc := (cutOutside_mem_core_iff hD x.1).2 hx
      rw [coe_collapse_rot_of_mem hxc]
      set T : Set H := {y | ∃ h : y ∈ ({p, q}ᶜ : Set H),
        (⟨y, h⟩ : ({p, q}ᶜ : Set H)) ∈ (cutData G p q hleg).collapseCore 𝒯c} with hT
      have hTK : ∀ y, y ∈ T ↔ y ∈ G.collapseCore 𝒯 ∧ y ∈ ({p, q}ᶜ : Set H) := fun y =>
        ⟨fun ⟨h, hy⟩ => ⟨(cutOutside_mem_core_iff hD ⟨y, h⟩).1 hy, h⟩,
          fun ⟨hy, h⟩ => ⟨h, (cutOutside_mem_core_iff hD ⟨y, h⟩).2 hy⟩⟩
      have e1 := coe_coe_firstReturn_firstReturnPerm (G.rot * swap p q)
        (S' := (cutData G p q hleg).collapseCore 𝒯c) (T := T) (fun y => Iff.rfl) ⟨x.1, hxc⟩
      change ((firstReturn (firstReturnPerm (G.rot * swap p q) _) _ ⟨x.1, hxc⟩ : _) : H) = _
      rw [e1]
      exact coe_firstReturn_of_simulation (σ := (G.collapse 𝒯).rot * swap p' q')
        (K := ({p', q'}ᶜ : Set S)) (π := G.rot * swap p q) (Y := T) Subtype.val
        {y : S | (y : H) ∉ G.collapseCore 𝒯}
        (fun y hy => by
          replace hy : (y : H) ∈ G.collapseCore 𝒯 := not_not.1 hy
          rw [hTK, ← hK']
          exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩)
        (fun y hy => by
          replace hy : (y : H) ∈ G.collapseCore 𝒯 := not_not.1 hy
          refine not_not.2 ?_
          have hz := hswap y hy
          rw [Perm.mul_apply, coe_collapse_rot_of_mem hz]
          exact Subtype.property _)
        (fun y hy => by
          replace hy : (y : H) ∈ G.collapseCore 𝒯 := not_not.1 hy
          have hz := hswap y hy
          rw [Perm.mul_apply, coe_collapse_rot_of_mem hz]
          refine ReachOutside.of_head (C := G.collapseCore 𝒯) (fun z hz' => ((hTK z).1 hz').1)
            (reachOutside_firstReturn G.rot _ ⟨_, hz⟩) ?_ ?_
          · rw [Perm.mul_apply, coe_swap_subtype']
          · intro u hu
            rw [Perm.mul_apply, swap_apply_of_ne_of_ne (fun h => hu (by rwa [h]))
              (fun h => hu (by rwa [h]))])
        (e x) (not_not.2 hx)
    · have hxc : x.1 ∉ (cutData G p q hleg).collapseCore 𝒯c :=
        mt (cutOutside_mem_core_iff hD x.1).1 hx
      rw [coe_collapse_rot_of_notMem hxc]
      have hσ : ((G.collapse 𝒯).rot * swap p' q') (e x) = (e x : S) := by
        have hne1 : (e x : S) ≠ p' := fun h => hx (by rwa [← he, h])
        have hne2 : (e x : S) ≠ q' := fun h => hx (by rwa [← he, h])
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hne1 hne2]
        exact Subtype.ext (coe_collapse_rot_of_notMem hx)
      rw [coe_firstReturn_of_apply_mem (by rw [hσ]; exact (e x).2), hσ]
      rfl
  · -- the boundaries
    change e x ∈ (cutData (G.collapse 𝒯) p' q' _).bdry ↔ x ∈ ((cutData G p q hleg).collapse 𝒯c).bdry
    rw [mem_cutData_bdry, mem_collapse_bdry, mem_collapse_bdry, mem_cutData_bdry]
    rfl
  · -- the colours
    change G.collapseColour 𝒯 (e x : S) = (cutData G p q hleg).collapseColour 𝒯c x
    rw [he]
    by_cases hx : ((x : ({p, q}ᶜ : Set H)) : H) ∈ G.collapseCore 𝒯
    · rw [collapseColour_of_mem_collapseCore hG hx,
        collapseColour_of_mem_collapseCore hGc ((cutOutside_mem_core_iff hD x.1).2 hx)]
      rfl
    · have hxc : x.1 ∉ (cutData G p q hleg).collapseCore 𝒯c :=
        mt (cutOutside_mem_core_iff hD x.1).1 hx
      obtain ⟨i, hi, hxi⟩ := x.2.resolve_left hxc
      have hi' : G.leg i ∈ G.familyDarts 𝒯 := (hD _).1 hi
      obtain ⟨p₁, hp₁, hip₁⟩ := mem_familyDarts.1 hi'
      obtain ⟨p₂, hp₂, hip₂⟩ := mem_familyDarts.1 hi
      have hxi' : ((x : ({p, q}ᶜ : Set H)) : H) = G.inv (G.leg i) := by
        rw [hxi, coe_cutData_inv_of_mem (x := (cutData G p q hleg).leg i)
          (cutOutside_inv_leg hG hp hq hi')]
        rfl
      change G.collapseColour 𝒯 (x : H) = _
      rw [hxi', hxi, collapseColour_inv_leg_of_mem hG hp₁ hip₁
          (fun r hr hir => hcol₁ i r hr p₁ hp₁ hir hip₁),
        collapseColour_inv_leg_of_mem hGc hp₂ hip₂
          (fun r hr hir => hcolc i r hr p₂ hp₂ hir hip₂)]
      exact hcol i p₁ hp₁ p₂ hp₂ hip₁ hip₂

/-- **Cutting outside the trees**, with the darts of the cut of the collapse given as darts of the
collapse. -/
private theorem isomorphic_collapse_cutData
    (hcol : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯c, G.leg i ∈ p₁.1.darts →
      (cutData G p q hleg).leg i ∈ p₂.1.darts → p₁.2 = p₂.2)
    (hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2)
    (p' q' : G.collapseDarts 𝒯) (hp' : (p' : H) = p) (hq' : (q' : H) = q)
    (hleg' : ∀ i, (G.collapse 𝒯).leg i ∈ ({p', q'}ᶜ : Set (G.collapseDarts 𝒯))) :
    ((cutData G p q hleg).collapse 𝒯c).Isomorphic (cutData (G.collapse 𝒯) p' q' hleg') := by
  obtain rfl : p' = ⟨p, mem_collapseDarts_of_notMem hp⟩ := Subtype.ext hp'
  obtain rfl : q' = ⟨q, mem_collapseDarts_of_notMem hq⟩ := Subtype.ext hq'
  exact ⟨collapseCutIso hG hGc hD hp hq hcol hcol₁⟩

end CutOutside

/-! ### Cuts given by an equation -/

section CutEq

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b} {p q : H}
  {hleg : ∀ i, G.leg i ∈ ({p, q}ᶜ : Set H)}

/-- **Cutting inside the trees**, for a tuple `Gc` equal to the cut. -/
theorem isomorphic_collapse_of_cut (hG : G.IsPlabicGraph)
    {Gc : PlabicData ({p, q}ᶜ : Set H) b} (hGc : Gc = cutData G p q hleg)
    (hGcP : Gc.IsPlabicGraph) {𝒯 : Finset (G.RootedTree × Shade)}
    {𝒯c : Finset (Gc.RootedTree × Shade)}
    (hD : ∀ x : ({p, q}ᶜ : Set H), x ∈ Gc.familyDarts 𝒯c ↔ (x : H) ∈ G.familyDarts 𝒯)
    (hp : p ∈ G.familyDarts 𝒯) (hq : q ∈ G.familyDarts 𝒯) (Q : Set H)
    (hQ : ∀ x, G.rot x ∈ Q ↔ x ∈ Q) (hQK : ∀ x ∈ Q, x ∉ G.collapseCore 𝒯) (hpq : p ∈ Q ∨ q ∈ Q)
    (hcol : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯c, G.leg i ∈ p₁.1.darts → Gc.leg i ∈ p₂.1.darts → p₁.2 = p₂.2)
    (hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2) :
    (Gc.collapse 𝒯c).Isomorphic (G.collapse 𝒯) := by
  subst hGc
  exact ⟨(collapseMatch_cutData hG hGcP hD hp hq Q hQ hQK hpq hcol hcol₁).iso hG hGcP⟩

/-- **Cutting outside the trees**, for a tuple `Gc` equal to the cut. -/
theorem isomorphic_collapse_cut_of_eq (hG : G.IsPlabicGraph)
    {Gc : PlabicData ({p, q}ᶜ : Set H) b} (hGc : Gc = cutData G p q hleg)
    (hGcP : Gc.IsPlabicGraph) {𝒯 : Finset (G.RootedTree × Shade)}
    {𝒯c : Finset (Gc.RootedTree × Shade)}
    (hD : ∀ x : ({p, q}ᶜ : Set H), x ∈ Gc.familyDarts 𝒯c ↔ (x : H) ∈ G.familyDarts 𝒯)
    (hp : p ∉ G.familyDarts 𝒯) (hq : q ∉ G.familyDarts 𝒯)
    (hcol : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯c, G.leg i ∈ p₁.1.darts → Gc.leg i ∈ p₂.1.darts → p₁.2 = p₂.2)
    (hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2)
    (p' q' : G.collapseDarts 𝒯) (hp' : (p' : H) = p) (hq' : (q' : H) = q)
    (hleg' : ∀ i, (G.collapse 𝒯).leg i ∈ ({p', q'}ᶜ : Set (G.collapseDarts 𝒯))) :
    (Gc.collapse 𝒯c).Isomorphic (cutData (G.collapse 𝒯) p' q' hleg') := by
  subst hGc
  exact isomorphic_collapse_cutData hG hGcP hD hp hq hcol hcol₁ p' q' hp' hq' hleg'

end CutEq

/-! ### The inclusion of the complement of two darts -/

section ComplMap

variable {H : Type} [DecidableEq H]

/-- The inclusion of `{p, q}ᶜ` into itself, extended to all of `H` by a default value. -/
def toCompl (p q : H) (x₀ : ({p, q}ᶜ : Set H)) (x : H) : ({p, q}ᶜ : Set H) :=
  if h : x ∈ ({p, q}ᶜ : Set H) then ⟨x, h⟩ else x₀

/-- On a dart `x ∈ {p, q}ᶜ`, `toCompl p q x₀` is `x` itself. -/
theorem toCompl_of_mem {p q : H} {x₀ : ({p, q}ᶜ : Set H)} {x : H}
    (h : x ∈ ({p, q}ᶜ : Set H)) : toCompl p q x₀ x = ⟨x, h⟩ := by
  rw [toCompl, dif_pos h]

/-- `toCompl p q x₀` restricts to the identity on `{p, q}ᶜ`. -/
theorem toCompl_val {p q : H} {x₀ : ({p, q}ᶜ : Set H)} (x : ({p, q}ᶜ : Set H)) :
    toCompl p q x₀ x = x := by
  rw [toCompl_of_mem x.2]

/-- On a dart `x ∈ {p, q}ᶜ`, the underlying dart of `toCompl p q x₀ x` is `x`. -/
theorem coe_toCompl_of_mem {p q : H} {x₀ : ({p, q}ᶜ : Set H)} {x : H}
    (h : x ∈ ({p, q}ᶜ : Set H)) : (toCompl p q x₀ x : H) = x := by
  rw [toCompl_of_mem h]

/-- `toCompl p q x₀` is injective on `{p, q}ᶜ`. -/
theorem injOn_toCompl {p q : H} (x₀ : ({p, q}ᶜ : Set H)) :
    Set.InjOn (toCompl p q x₀) ({p, q}ᶜ : Set H) := by
  intro x hx y hy h
  rw [toCompl_of_mem hx, toCompl_of_mem hy] at h
  exact congrArg Subtype.val h

end ComplMap

end PlabicData

end ClusterAlgebras

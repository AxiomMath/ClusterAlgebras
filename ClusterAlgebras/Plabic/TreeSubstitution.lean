/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.FamilyCollapse

/-!
# Substitution into trees of plabic graphs

The plabic graph `P_T` of a rooted tree `T` of `G` can be replaced inside `G` by any plabic graph
`R` with one boundary vertex, a *`T`-filling*: the *substitution* `G[R]` splices the rotation of
`R` around the dart `ḡ` across its leg (or around its leg, for a boundary root) into the rotation
of `G` at the root, in place of the interval of `T`. A reduction step of `R` (the removal of a
bivalent vertex or the contraction of an edge between internal vertices of the same colour) is
then a local move of `G[R]`. Substituting `P_T` gives back `G`; reducing `P_T` as far as possible
gives `L_c`, and substituting `L_c` gives the collapse. Hence collapsing a tree, or a collapsing
family, is a sequence of moves (M2) and (M3).

## Main definitions

* `ClusterAlgebras.PlabicData.RootedTree.IsFilling`,
  `ClusterAlgebras.PlabicData.RootedTree.substitution`: `T`-fillings and the substitution `G[R]`;
  `ClusterAlgebras.PlabicData.familySubstitution` substitutes fillings into several trees at once.

## Main results

* `ClusterAlgebras.PlabicData.RootedTree.substitution_reductionStep`: a reduction step of the
  filling is a local move of the graph.
* `ClusterAlgebras.PlabicData.RootedTree.IsCollapsibleOfColour.moveEquivalent_collapse`: collapsing
  one tree is a sequence of moves (M2), (M3).
* `ClusterAlgebras.PlabicData.IsCollapsingFamily.moveEquivalent_collapse`: collapsing a family is a
  sequence of moves (M2), (M3).

## Implementation notes

* The darts of a `T`-filling `R` form an arbitrary finite type, and the darts of `G[R]` are those
  of `H ⊕ H_R` that survive; this disjoint union is FWZ's condition that `H_R` is disjoint
  from `H \ D_T`. FWZ's darts `e, ē` are the two darts of `B_R`, the dart `g_*` is the
  leg of `R`, and `ḡ` the dart across it. The rotation of `G[R]` is the first return to the
  surviving darts of `σ ⊔ σ_R` composed with the transposition of the last dart `a_k` of the
  interval and the attaching dart of `R` (`ḡ`, or the leg for a boundary root); this is
  FWZ's rotation.
* The substitution is defined for any family of trees and fillings, `familySubstitution`; the
  substitution into one tree is the case of a family indexed by `Unit`. The colour conditions on
  the fillings are not needed for `RootedTree.substitution_reductionStep`.
* `IsCollapsingFamily.moveEquivalent_collapse` is proved by substituting the plabic graphs of all
  the trees at once and reducing them one at a time, rather than by induction on the number of
  members; this avoids transporting the remaining trees into an intermediate collapse.
* Removals and contractions are both *cuts* `{p, q}ᶜ` with the first returns of `ι ∘ (p q)` and
  `σ ∘ (p q)`; first returns of first returns are first returns, which carries a cut of a filling
  to a cut of the substitution.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function _root_.Equiv _root_.Equiv.Perm

/-! ### First returns -/

-- Note: the first-return toolkit of this section parallels CollapseCuts.lean (downstream) and the
-- private `firstReturnPerm_mul_swap` in Reduced.lean, neither usable from here.
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

private theorem ReachOutside.step {π : Perm X} {Y : Set X} {x w z : X} (h₁ : π x = w)
    (hw : w ∉ Y) (h₂ : ReachOutside π Y w z) : ReachOutside π Y x z :=
  (h₁ ▸ ReachOutside.single π Y x).trans hw h₂

private theorem ReachOutside.of_eq {π : Perm X} {Y : Set X} {x z : X} (h : π x = z) :
    ReachOutside π Y x z :=
  h ▸ ReachOutside.single π Y x

private theorem coe_firstReturn_of_reachOutside [Finite X] {π : Perm X} {Y : Set X} {y : Y}
    {z : X} (h : ReachOutside π Y y z) (hz : z ∈ Y) : (firstReturn π Y y : X) = z := by
  obtain ⟨m, hm, rfl, hmin⟩ := h
  exact coe_firstReturn_of_pow hm hz hmin

/-- **Simulation of first returns.** If `φ` maps `K` into `Y` and its complement outside `Y`, and
every step `x ↦ σ x` is followed by a run of `π` from `φ x` to `φ (σ x)` outside `Y`, then `φ`
carries the first return of `σ` to `K` to the first return of `π` to `Y`. -/
private theorem coe_firstReturn_of_simulation [Finite X] [Finite X'] {σ : Perm X} {K : Set X}
    {π : Perm X'} {Y : Set X'} (φ : X → X') (hK : ∀ x, φ x ∈ Y ↔ x ∈ K)
    (hstep : ∀ x, ReachOutside π Y (φ x) (φ (σ x))) (x : K) :
    (firstReturn π Y ⟨φ x, (hK x).2 x.2⟩ : X') = φ (firstReturn σ K x) := by
  apply coe_firstReturn_of_reachOutside _ ((hK _).2 (firstReturn σ K x).2)
  rw [coe_firstReturn]
  have key : ∀ n, 0 < n → (∀ j, 0 < j → j < n → (σ ^ j) (x : X) ∉ K) →
      ReachOutside π Y (φ x) (φ ((σ ^ n) x)) := by
    intro n
    induction n with
    | zero =>
      intro h
      omega
    | succ n ih =>
      intro _ hmin
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hstep x
      · rw [pow_succ', Perm.mul_apply]
        exact (ih hn fun j hj hjn => hmin j hj (by omega)).trans
          (fun h => hmin n hn (by omega) ((hK _).1 h)) (hstep _)
  exact key _ (firstReturnTime_pos x) fun j hj hjm => pow_apply_notMem_of_lt_firstReturnTime hj hjm

/-- A map intertwining two permutations carries first returns to first returns. -/
private theorem coe_firstReturn_of_semiconj_map [Finite X] [Finite X'] {π : Perm X}
    {π' : Perm X'} (f : X → X') (h : ∀ x, f (π x) = π' (f x)) {S : Set X} {S' : Set X'}
    (hS : ∀ x, f x ∈ S' ↔ x ∈ S) (y : S) :
    (firstReturn π' S' ⟨f y, (hS y).2 y.2⟩ : X') = f (firstReturn π S y) :=
  coe_firstReturn_of_simulation f hS (fun x => ReachOutside.of_eq (h x).symm) y

/-- The first return to `S' ⊆ S` of the first return to `S` is the first return to `S'`. -/
private theorem coe_coe_firstReturn_firstReturnPerm [Finite X] (π : Perm X) {S : Set X}
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
    | zero =>
      intro z h
      omega
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

private theorem ReachOutside.tail {π : Perm X} {Y : Set X} {x z : X} (h : ReachOutside π Y x z)
    (hz : z ∈ Y) (hx : π x ∉ Y) : ReachOutside π Y (π x) z := by
  obtain ⟨m, hm, rfl, hmin⟩ := h
  have hm2 : 2 ≤ m := by
    by_contra h'
    obtain rfl : m = 1 := by omega
    exact hx (by simpa using hz)
  refine ⟨m - 1, by omega, ?_, fun j hj hjm => ?_⟩
  · rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega)]
  · rw [← Perm.mul_apply, ← pow_succ]
    exact hmin _ (by omega) (by omega)

/-- A run of `π₀` outside `S₀` is carried to a run of `π` outside `T` by a map intertwining `π₀`
and `π` at the points of the run. -/
private theorem ReachOutside.map {Y₀ : Type*} {π₀ : Perm Y₀} {S₀ : Set Y₀} {π : Perm X}
    {T : Set X} (f : Y₀ → X) (hS : ∀ z, z ∉ S₀ → f z ∉ T) {z w : Y₀}
    (hpath : ReachOutside π₀ S₀ z w) (h : ∀ u, (u = z ∨ u ∉ S₀) → f (π₀ u) = π (f u)) :
    ReachOutside π T (f z) (f w) := by
  obtain ⟨m, hm, rfl, hmin⟩ := hpath
  have key : ∀ n, n ≤ m → (π ^ n) (f z) = f ((π₀ ^ n) z) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [pow_succ', Perm.mul_apply, ih (by omega), pow_succ', Perm.mul_apply]
      refine (h _ ?_).symm
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · exact .inl rfl
      · exact .inr (hmin n hn0 (by omega))
  refine ⟨m, hm, key m le_rfl, fun j hj hjm => ?_⟩
  rw [key j hjm.le]
  exact hS _ (hmin j hj hjm)

private theorem coe_swap_subtype' [DecidableEq X] {S : Set X} (p q y : S) :
    ((swap p q y : S) : X) = swap (p : X) q y := by
  rw [swap_apply_def, swap_apply_def]
  split_ifs <;> simp_all [Subtype.ext_iff]

/-- Composing with a transposition of two points of `S` commutes with the first return to `S`. -/
private theorem firstReturnPerm_mul_swap' [Finite X] [DecidableEq X] (π : Perm X) {S : Set X}
    (p q : S) :
    firstReturnPerm (π * swap (p : X) q) S = firstReturnPerm π S * swap p q := by
  ext y
  simp only [Perm.mul_apply, coe_firstReturnPerm]
  refine coe_firstReturn_eq_of_eqOn_compl ?_ fun z hz => ?_
  · rw [Perm.mul_apply, coe_swap_subtype']
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (by rintro rfl; exact hz p.2)
      (by rintro rfl; exact hz q.2)]

/-- A property preserved by `π` is preserved along the orbits of `π`. -/
theorem SameCycle.of_invariant [Finite X] {π : Perm X} (P : X → Prop)
    (hP : ∀ x, P x → P (π x)) {x z : X} (hx : P x) (h : π.SameCycle x z) : P z := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  have key : ∀ n : ℕ, P ((π ^ n) x) := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [pow_succ', Perm.mul_apply]; exact hP _ ih
  exact key n

end FirstReturn

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-! ### Substitution into trees -/

namespace RootedTree

variable (T : G.RootedTree)

/-- The dart of a filling `R` that is glued to the root of `T`: the leg `g` of `R` if the root
is a boundary vertex, and the dart `ḡ` across the leg if the root is internal. -/
noncomputable def attachDart (R : PlabicGraph 1) : R.Dart :=
  if G.IsBoundaryVertex T.root then R.data.leg 0 else R.data.inv (R.data.leg 0)

/-- The darts of a filling `R` that do not appear in the substitution: `e, ē` (the darts of `B_R`),
and also `g, ḡ` if the root of `T` is internal. -/
def IsCutDart (R : PlabicGraph 1) (y : R.Dart) : Prop :=
  y ∈ R.data.bdry ∨
    (¬G.IsBoundaryVertex T.root ∧ (y = R.data.leg 0 ∨ y = R.data.inv (R.data.leg 0)))

/-- Being a cut dart of a filling is decidable. -/
instance (R : PlabicGraph 1) : DecidablePred (T.IsCutDart R) := fun y => by
  unfold IsCutDart; infer_instance

/-- A **`T`-filling**: a plabic graph `R` with one boundary vertex such that, if the root `v` of
`T` is internal, the vertex of `R` containing the dart `ḡ` across the leg `g` of `R` has the colour
`κ(v)` of the root. FWZ's darts `e, ē` are the two darts of `B_R`, FWZ's leg `g_*` is the leg of
`R`, and the darts of `R` are disjoint from those of `G` by construction of the substitution. -/
@[cluster_algebras "def_tree_substitution"]
def IsFilling (R : PlabicGraph 1) : Prop :=
  ¬G.IsBoundaryVertex T.root → R.data.colour (R.data.inv (R.data.leg 0)) = G.colour T.intervalStart

end RootedTree

section Substitution

variable {ι : Type} [Fintype ι] [DecidableEq ι] (T : ι → G.RootedTree) (R : ι → PlabicGraph 1)

/-- The darts of the substitution of the fillings `R j` into the trees `T j`, inside
`H ⊕ Σ j, H_{R j}`: the darts of `G` lying in no `D_{T j}`, and the darts of the `R j` that are not
cut. -/
def substDarts : Set (H ⊕ Σ j, (R j).Dart) :=
  {x | Sum.elim (fun d => ∀ j, d ∉ (T j).darts) (fun y => ¬(T y.1).IsCutDart (R y.1) y.2) x}

/-- Membership in the darts of the substitution is decidable. -/
instance : DecidablePred (· ∈ substDarts T R) := fun x => by
  unfold substDarts; rcases x with d | y <;> simp only [Set.mem_setOf_eq, Sum.elim_inl,
    Sum.elim_inr] <;> infer_instance

omit [Fintype ι] [DecidableEq ι] in
/-- A dart of `G` is a dart of the substitution if and only if it lies in no tree `T j`. -/
theorem inl_mem_substDarts {d : H} : (.inl d : H ⊕ Σ j, (R j).Dart) ∈ substDarts T R ↔
    ∀ j, d ∉ (T j).darts :=
  Iff.rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A dart of a filling `R j` is a dart of the substitution if and only if it is not cut. -/
theorem inr_mem_substDarts {y : Σ j, (R j).Dart} :
    (.inr y : H ⊕ Σ j, (R j).Dart) ∈ substDarts T R ↔ ¬(T y.1).IsCutDart (R y.1) y.2 :=
  Iff.rfl

/-- The gluing involution: it exchanges the last dart `a_k` of the interval of `T j`, a dart of
`G`, with the attaching dart of `R j`, for every `j`. -/
noncomputable def substGlueFun : H ⊕ (Σ j, (R j).Dart) → H ⊕ Σ j, (R j).Dart
  | .inl d => if h : ∃ j, (T j).intervalEnd = d then
      .inr ⟨h.choose, (T h.choose).attachDart (R h.choose)⟩ else .inl d
  | .inr y => if y.2 = (T y.1).attachDart (R y.1) then .inl (T y.1).intervalEnd else .inr y

omit [DecidableEq ι] in
/-- The gluing map is an involution when the last darts of the intervals of the `T j` are
distinct. -/
theorem substGlueFun_involutive (hinj : Injective fun j => (T j).intervalEnd) :
    Involutive (substGlueFun T R) := by
  rintro (d | ⟨j, y⟩)
  · by_cases h : ∃ j, (T j).intervalEnd = d
    · simp only [substGlueFun, dif_pos h, if_true]
      exact congrArg Sum.inl h.choose_spec
    · simp only [substGlueFun, dif_neg h]
  · by_cases hy : y = (T j).attachDart (R j)
    · subst hy
      have hex : ∃ j', (T j').intervalEnd = (T j).intervalEnd := ⟨j, rfl⟩
      have key : ∀ j' (_ : j' = j), (Sum.inr ⟨j', (T j').attachDart (R j')⟩ :
          H ⊕ Σ j, (R j).Dart) = .inr ⟨j, (T j).attachDart (R j)⟩ := by
        rintro _ rfl; rfl
      simp only [substGlueFun, if_true, dif_pos hex]
      exact key _ (hinj hex.choose_spec)
    · simp only [substGlueFun, hy, if_false]

open scoped Classical in
/-- The gluing involution as a permutation (the identity if the last darts of the intervals are
not distinct). -/
noncomputable def substGlue : Perm (H ⊕ Σ j, (R j).Dart) :=
  if h : Involutive (substGlueFun T R) then h.toPerm _ else 1

variable (G) in
/-- The involution of `G ⊔ ⨆ R j`. -/
def substInv : Perm (H ⊕ Σ j, (R j).Dart) :=
  Perm.sumCongr G.inv (Perm.sigmaCongrRight fun j => (R j).data.inv)

/-- The rotation of `G ⊔ ⨆ R j` glued along the intervals: `σ ⊔ σ_{R j}` composed with the gluing
involution. Its first return to the darts of the substitution is the rotation of the
substitution. -/
noncomputable def substRot : Perm (H ⊕ Σ j, (R j).Dart) :=
  Perm.sumCongr G.rot (Perm.sigmaCongrRight fun j => (R j).data.rot) * substGlue T R

omit [Fintype ι] [DecidableEq ι] in
/-- If the leg `g_i` of a plabic graph lies in some tree `T j`, then the leg of the corresponding
filling is a dart of the substitution. -/
theorem inr_leg_mem_substDarts (hG : G.IsPlabicGraph) (i : Fin b)
    (h : ∃ j, G.leg i ∈ (T j).darts) :
    (.inr ⟨h.choose, (R h.choose).data.leg 0⟩ : H ⊕ Σ j, (R j).Dart) ∈ substDarts T R := by
  rintro (h' | ⟨h', -⟩)
  · exact (R h.choose).isPlabicGraph.leg_notMem_bdry 0 h'
  · apply h'
    rw [(T h.choose).root_eq_bvertex_of_leg_mem hG h.choose_spec]
    exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)

/-- The legs of the substitution: the leg `g_i` of `G`, unless it lies in a tree `T j`, in which
case it is replaced by the leg of `R j`. -/
noncomputable def substLeg (hG : G.IsPlabicGraph) (i : Fin b) : substDarts T R :=
  if h : ∃ j, G.leg i ∈ (T j).darts then ⟨_, inr_leg_mem_substDarts T R hG i h⟩
  else ⟨.inl (G.leg i), fun j hj => h ⟨j, hj⟩⟩

/-- The **substitution** `G[(R_j)]` of fillings `R j` into a family of rooted trees `T j` of `G`:
the darts of `G` outside the trees and the darts of the fillings other than `e, ē` (and `g, ḡ`
for an internal root), with the involutions of `G` and of the `R j`, the rotation obtained by
replacing, at each root, the interval of `T j` by the rotation of `R j` around its attaching dart,
the boundary arcs of `G`, and the colours of `G` and of the `R j`. -/
noncomputable def familySubstitution (hG : G.IsPlabicGraph) : PlabicData (substDarts T R) b where
  inv := firstReturnPerm (substInv G R) (substDarts T R)
  rot := firstReturnPerm (substRot T R) (substDarts T R)
  bdry := (G.bdry.map Embedding.inl).subtype (· ∈ substDarts T R)
  colour x := Sum.elim G.colour (fun y => (R y.1).data.colour y.2) x.1
  leg i := substLeg T R hG i

end Substitution

/-- **Substitution into a tree**. For a rooted tree `T = (v, W)` of a plabic graph `G` and a
`T`-filling `R`, the substitution `G[R]` has the darts `(H \ D_T) ∪ (H_R \ {e, ē})` if `v = β(i)`
is a boundary vertex (the leg `g_i` of `G` being the leg of `R`), and
`(H \ D_T) ∪ (H_R \ {e, ē, g, ḡ})` if `v` is internal; the involutions of `G` and `R`; the rotation
`σ` of `G` on the darts of `G`, except at the root, and `σ_R` on the darts of `R`, except that the
cycle of `σ_R` through `ḡ` is spliced with the darts of `v` outside `D_T` in place of `ḡ` (internal
root), respectively the leg of `R` is followed by `σ(g_i)` (boundary root); the boundary arcs, the
colours and the labels of `G`; and the colours of `R`. -/
@[cluster_algebras "def_tree_substitution"]
noncomputable def RootedTree.substitution (hG : G.IsPlabicGraph) (T : G.RootedTree)
    (R : PlabicGraph 1) :
    PlabicData (substDarts (fun _ : Unit => T) fun _ => R) b :=
  familySubstitution (fun _ => T) (fun _ => R) hG

/-! ### The substitution: first facts -/

section SubstitutionAPI

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : ι → G.RootedTree} {R : ι → PlabicGraph 1}

omit [Fintype ι] [DecidableEq ι] in
/-- Equal indices give equal dependent pairs. -/
private theorem sigma_eq_of_eq {β : ι → Type} (f : ∀ j, β j) {j j' : ι} (h : j = j') :
    (⟨j, f j⟩ : Σ j, β j) = ⟨j', f j'⟩ := by
  subst h; rfl

omit [DecidableEq ι] in
/-- When the last darts of the intervals are distinct, the gluing permutation is the gluing
map. -/
theorem substGlue_apply (hinj : Injective fun j => (T j).intervalEnd) (x : H ⊕ Σ j, (R j).Dart) :
    substGlue T R x = substGlueFun T R x := by
  rw [substGlue, dif_pos (substGlueFun_involutive T R hinj)]
  rfl

omit [DecidableEq ι] in
/-- The gluing sends the last dart `a_k` of `T j` to the attaching dart of `R j`. -/
theorem substGlue_inl_intervalEnd (hinj : Injective fun j => (T j).intervalEnd) (j : ι) :
    substGlue T R (.inl (T j).intervalEnd) = .inr ⟨j, (T j).attachDart (R j)⟩ := by
  have hex : ∃ j', (T j').intervalEnd = (T j).intervalEnd := ⟨j, rfl⟩
  rw [substGlue_apply hinj]
  simp only [substGlueFun, dif_pos hex]
  exact congrArg Sum.inr (sigma_eq_of_eq (fun j => (T j).attachDart (R j)) (hinj hex.choose_spec))

omit [DecidableEq ι] in
/-- The gluing fixes a dart of `G` that is the last dart of no interval. -/
theorem substGlue_inl_of_forall_ne (hinj : Injective fun j => (T j).intervalEnd) {d : H}
    (h : ∀ j, (T j).intervalEnd ≠ d) : substGlue T R (.inl d) = .inl d := by
  rw [substGlue_apply hinj]
  simp only [substGlueFun, dif_neg (not_exists.2 h)]

omit [DecidableEq ι] in
/-- The gluing sends the attaching dart of `R j` to the last dart `a_k` of `T j`. -/
theorem substGlue_inr_attachDart (hinj : Injective fun j => (T j).intervalEnd) (j : ι) :
    substGlue T R (.inr ⟨j, (T j).attachDart (R j)⟩) = .inl (T j).intervalEnd := by
  rw [substGlue_apply hinj]
  simp [substGlueFun]

omit [DecidableEq ι] in
/-- The gluing fixes a dart of `R j` other than its attaching dart. -/
theorem substGlue_inr_of_ne (hinj : Injective fun j => (T j).intervalEnd) {j : ι} {y : (R j).Dart}
    (hy : y ≠ (T j).attachDart (R j)) : substGlue T R (.inr ⟨j, y⟩) = .inr ⟨j, y⟩ := by
  rw [substGlue_apply hinj]
  simp [substGlueFun, hy]

omit [DecidableEq ι] in
/-- The glued rotation agrees with `σ` at a dart of `G` that is the last dart of no interval. -/
theorem substRot_inl_of_forall_ne (hinj : Injective fun j => (T j).intervalEnd) {d : H}
    (h : ∀ j, (T j).intervalEnd ≠ d) : substRot T R (.inl d) = .inl (G.rot d) := by
  rw [substRot, Perm.mul_apply, substGlue_inl_of_forall_ne hinj h]
  rfl

omit [DecidableEq ι] in
/-- The glued rotation sends the last dart `a_k` of `T j` to the image under `σ_{R j}` of the
attaching dart of `R j`. -/
theorem substRot_inl_intervalEnd (hinj : Injective fun j => (T j).intervalEnd) (j : ι) :
    substRot T R (.inl (T j).intervalEnd) =
      .inr ⟨j, (R j).data.rot ((T j).attachDart (R j))⟩ := by
  rw [substRot, Perm.mul_apply, substGlue_inl_intervalEnd hinj]
  rfl

omit [DecidableEq ι] in
/-- The glued rotation sends the attaching dart of `R j` to `σ a_k`, for `a_k` the last dart of
`T j`. -/
theorem substRot_inr_attachDart (hinj : Injective fun j => (T j).intervalEnd) (j : ι) :
    substRot T R (.inr ⟨j, (T j).attachDart (R j)⟩) = .inl (G.rot (T j).intervalEnd) := by
  rw [substRot, Perm.mul_apply, substGlue_inr_attachDart hinj]
  rfl

omit [DecidableEq ι] in
/-- The glued rotation agrees with `σ_{R j}` at a dart of `R j` other than its attaching dart. -/
theorem substRot_inr_of_ne (hinj : Injective fun j => (T j).intervalEnd) {j : ι}
    {y : (R j).Dart} (hy : y ≠ (T j).attachDart (R j)) :
    substRot T R (.inr ⟨j, y⟩) = .inr ⟨j, (R j).data.rot y⟩ := by
  rw [substRot, Perm.mul_apply, substGlue_inr_of_ne hinj hy]
  rfl

omit [Fintype H] [DecidableEq H] [Fintype ι] [DecidableEq ι] in
/-- On darts of `G`, the involution of `G ⊔ ⨆ R j` is that of `G`. -/
theorem substInv_inl (d : H) : substInv G R (.inl d) = .inl (G.inv d) := rfl

omit [Fintype H] [DecidableEq H] [Fintype ι] [DecidableEq ι] in
/-- On darts of `R j`, the involution of `G ⊔ ⨆ R j` is that of `R j`. -/
theorem substInv_inr (y : Σ j, (R j).Dart) :
    substInv G R (.inr y) = .inr ⟨y.1, (R y.1).data.inv y.2⟩ := rfl

/-- A dart of a filling is cut if and only if the dart across it is cut. -/
theorem RootedTree.isCutDart_inv_iff (T₀ : G.RootedTree) (R₀ : PlabicGraph 1) (y : R₀.Dart) :
    T₀.IsCutDart R₀ (R₀.data.inv y) ↔ T₀.IsCutDart R₀ y := by
  have hR := R₀.isPlabicGraph
  have hinv := hR.inv_involutive
  unfold RootedTree.IsCutDart
  rw [hR.inv_mem_bdry_iff]
  constructor
  · rintro (h | ⟨hb, h | h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hb, Or.inr (by rw [← h, hinv])⟩
    · exact Or.inr ⟨hb, Or.inl (hinv.injective h)⟩
  · rintro (h | ⟨hb, rfl | rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hb, Or.inr rfl⟩
    · exact Or.inr ⟨hb, Or.inl (hinv _)⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The involution of `G ⊔ ⨆ R j` preserves the darts of the substitution. -/
theorem substInv_mem_iff (hG : G.IsPlabicGraph) (x : H ⊕ Σ j, (R j).Dart) :
    substInv G R x ∈ substDarts T R ↔ x ∈ substDarts T R := by
  rcases x with d | ⟨j, y⟩
  · rw [substInv_inl, inl_mem_substDarts, inl_mem_substDarts]
    refine forall_congr' fun j => not_congr ⟨fun h => ?_, (T j).inv_mem_darts hG⟩
    simpa [hG.inv_involutive d] using (T j).inv_mem_darts hG h
  · rw [substInv_inr, inr_mem_substDarts, inr_mem_substDarts]
    exact not_congr ((T j).isCutDart_inv_iff (R j) y)

omit [DecidableEq ι] in
/-- The involution of the substitution is the restriction of the involutions of `G` and the
`R j`. -/
theorem coe_familySubstitution_inv (hG : G.IsPlabicGraph) (x : substDarts T R) :
    ((G.familySubstitution T R hG).inv x : H ⊕ Σ j, (R j).Dart) = substInv G R x :=
  coe_firstReturn_of_apply_mem ((substInv_mem_iff hG _).2 x.2)

omit [DecidableEq ι] in
/-- The rotation of the substitution is the first return of the glued rotation to its darts. -/
theorem coe_familySubstitution_rot (hG : G.IsPlabicGraph) (x : substDarts T R) :
    ((G.familySubstitution T R hG).rot x : H ⊕ Σ j, (R j).Dart) =
      firstReturn (substRot T R) (substDarts T R) x :=
  rfl

omit [DecidableEq ι] in
/-- The boundary arcs of the substitution are those of `G`. -/
theorem mem_familySubstitution_bdry (hG : G.IsPlabicGraph) {x : substDarts T R} :
    x ∈ (G.familySubstitution T R hG).bdry ↔ ∃ d ∈ G.bdry, (x : H ⊕ Σ j, (R j).Dart) = .inl d := by
  change x ∈ (G.bdry.map Embedding.inl).subtype _ ↔ _
  rw [mem_subtype, mem_map]
  simp only [Embedding.inl_apply]
  exact ⟨fun ⟨d, hd, h⟩ => ⟨d, hd, h.symm⟩, fun ⟨d, hd, h⟩ => ⟨d, hd, h.symm⟩⟩

omit [DecidableEq ι] in
/-- The colour of a dart of the substitution is its colour in `G` or in `R j`. -/
theorem familySubstitution_colour (hG : G.IsPlabicGraph) (x : substDarts T R) :
    (G.familySubstitution T R hG).colour x =
      Sum.elim G.colour (fun y => (R y.1).data.colour y.2) (x : H ⊕ Σ j, (R j).Dart) :=
  rfl

omit [DecidableEq ι] in
/-- For pairwise disjoint trees, the leg `i` of the substitution is the leg of `R j` when `g_i`
lies in `T j`. -/
theorem coe_familySubstitution_leg_of_mem (hG : G.IsPlabicGraph)
    (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts) {i : Fin b} {j : ι}
    (h : G.leg i ∈ (T j).darts) :
    ((G.familySubstitution T R hG).leg i : H ⊕ Σ j, (R j).Dart) = .inr ⟨j, (R j).data.leg 0⟩ := by
  classical
  have hex : ∃ j, G.leg i ∈ (T j).darts := ⟨j, h⟩
  change (substLeg T R hG i : H ⊕ Σ j, (R j).Dart) = _
  rw [substLeg, dif_pos hex]
  refine congrArg Sum.inr (sigma_eq_of_eq (fun j => (R j).data.leg 0) ?_)
  by_contra hne
  exact Finset.disjoint_left.1 (hdisj hne) hex.choose_spec h

omit [DecidableEq ι] in
/-- The leg `i` of the substitution is the leg `g_i` of `G` when `g_i` lies in no tree. -/
theorem coe_familySubstitution_leg_of_notMem (hG : G.IsPlabicGraph) {i : Fin b}
    (h : ∀ j, G.leg i ∉ (T j).darts) :
    ((G.familySubstitution T R hG).leg i : H ⊕ Σ j, (R j).Dart) = .inl (G.leg i) := by
  change (substLeg T R hG i : H ⊕ Σ j, (R j).Dart) = _
  rw [substLeg, dif_neg (not_exists.2 h)]

omit [Fintype ι] [DecidableEq ι] in
/-- Pairwise disjoint trees have distinct last darts. -/
theorem intervalEnd_injective (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts) :
    Injective fun j => (T j).intervalEnd := by
  classical
  intro j j' h
  by_contra hne
  exact Finset.disjoint_left.1 (hdisj hne) (T j).intervalEnd_mem_darts
    (by simp only at h; rw [h]; exact (T j').intervalEnd_mem_darts)

end SubstitutionAPI

/-! ### Substituting the plabic graphs of the trees gives back `G` -/

/-- The plabic graph `P_T` of a rooted tree, bundled. -/
noncomputable def RootedTree.toPlabicGraph (hG : G.IsPlabicGraph) (T : G.RootedTree) :
    PlabicGraph 1 :=
  ⟨T.Dart, T.plabicData, T.isPlabicGraph_plabicData hG⟩

section SubstitutionSelf

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : ι → G.RootedTree} (hG : G.IsPlabicGraph)
  (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts)

/-- The dart of the substitution of the `P_{T j}` corresponding to a dart of `G`. -/
private noncomputable def selfMap (T : ι → G.RootedTree) (hG : G.IsPlabicGraph) (d : H) :
    H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart :=
  if h : ∃ j, d ∈ (T j).darts then .inr ⟨h.choose, ⟨.inl d, h.choose_spec⟩⟩ else .inl d

omit [DecidableEq ι] in
include hdisj in
private theorem selfMap_of_mem {d : H} {j : ι} (hd : d ∈ (T j).darts) :
    selfMap T hG d = .inr ⟨j, ⟨.inl d, hd⟩⟩ := by
  classical
  have hex : ∃ j, d ∈ (T j).darts := ⟨j, hd⟩
  rw [selfMap, dif_pos hex]
  have key : ∀ j' (hj' : d ∈ (T j').darts), j' = j →
      (Sum.inr ⟨j', ⟨.inl d, hj'⟩⟩ : H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart) =
        .inr ⟨j, ⟨.inl d, hd⟩⟩ := by
    rintro _ _ rfl; rfl
  refine key _ hex.choose_spec ?_
  by_contra hne
  exact Finset.disjoint_left.1 (hdisj hne) hex.choose_spec hd

omit [DecidableEq ι] in
private theorem selfMap_of_notMem {d : H} (hd : ∀ j, d ∉ (T j).darts) :
    selfMap T hG d = .inl d := by
  rw [selfMap, dif_neg (not_exists.2 hd)]

omit [DecidableEq ι] in
private theorem selfMap_mem (d : H) :
    selfMap T hG d ∈ substDarts T fun j => (T j).toPlabicGraph hG := by
  unfold selfMap
  split_ifs with h
  · set j := h.choose
    rintro (h' | ⟨hb, h' | h'⟩)
    · change _ ∈ (T j).plabicData.bdry at h'
      rcases (T j).mem_bdry_plabicData.1 h' with h'' | h'' <;>
        simp [RootedTree.dartE, RootedTree.dartEBar] at h''
    · change (⟨Sum.inl d, h.choose_spec⟩ : (T j).Dart) = (T j).legDart at h'
      rw [RootedTree.legDart, dif_neg hb] at h'
      simp at h'
    · change (⟨Sum.inl d, h.choose_spec⟩ : (T j).Dart) = (T j).plabicData.inv (T j).legDart at h'
      have h'' := congrArg Subtype.val h'
      rw [RootedTree.coe_inv_plabicData _ hG, RootedTree.legDart, dif_neg hb] at h''
      simp at h''
  · exact fun j hj => h ⟨j, hj⟩

end SubstitutionSelf

/-- For a boundary root, the leg of `P_T` is the dart `a₁` of `G`. -/
theorem RootedTree.legDart_of_isBoundaryVertex (T : G.RootedTree)
    (hb : G.IsBoundaryVertex T.root) :
    T.legDart = ⟨.inl T.intervalStart, T.intervalStart_mem_darts⟩ := by
  rw [RootedTree.legDart, dif_pos hb]

/-- For an internal root, the dart across the leg of `P_T` is the new dart `ḡ`. -/
theorem RootedTree.inv_legDart_of_not_isBoundaryVertex (hG : G.IsPlabicGraph) (T : G.RootedTree)
    (hb : ¬G.IsBoundaryVertex T.root) :
    T.plabicData.inv T.legDart = ⟨.inr .gBar, hb⟩ := by
  apply Subtype.ext
  rw [RootedTree.coe_inv_plabicData _ hG, RootedTree.legDart, dif_neg hb]
  rfl

/-- For a boundary root, the attaching dart of the plabic graph of `T` is the first dart `a₁`. -/
theorem RootedTree.attachDart_toPlabicGraph_of_isBoundaryVertex (hG : G.IsPlabicGraph)
    (T : G.RootedTree) (hb : G.IsBoundaryVertex T.root) :
    T.attachDart (T.toPlabicGraph hG) = ⟨.inl T.intervalStart, T.intervalStart_mem_darts⟩ := by
  rw [RootedTree.attachDart, if_pos hb]
  exact T.legDart_of_isBoundaryVertex hb

/-- For an internal root, the attaching dart of the plabic graph of `T` is `ḡ`. -/
theorem RootedTree.attachDart_toPlabicGraph_of_not_isBoundaryVertex (hG : G.IsPlabicGraph)
    (T : G.RootedTree) (hb : ¬G.IsBoundaryVertex T.root) :
    T.attachDart (T.toPlabicGraph hG) = ⟨.inr .gBar, hb⟩ := by
  rw [RootedTree.attachDart, if_neg hb]
  exact T.inv_legDart_of_not_isBoundaryVertex hG hb

/-- For an internal root, the rotation of the plabic graph of `T` sends `ḡ` to the first dart
`a₁`. -/
theorem RootedTree.rot_gBar (hG : G.IsPlabicGraph) (T : G.RootedTree)
    (hb : ¬G.IsBoundaryVertex T.root) :
    T.plabicData.rot ⟨.inr .gBar, hb⟩ = ⟨.inl T.intervalStart, T.intervalStart_mem_darts⟩ :=
  Subtype.ext (by rw [T.coe_rot_plabicData hG]; rfl)

/-- For an internal root, the rotation of the plabic graph of `T` sends the last dart `a_k` to
`ḡ`. -/
theorem RootedTree.rot_inl_intervalEnd (hG : G.IsPlabicGraph) (T : G.RootedTree)
    (hb : ¬G.IsBoundaryVertex T.root) :
    T.plabicData.rot ⟨.inl T.intervalEnd, T.intervalEnd_mem_darts⟩ = ⟨.inr .gBar, hb⟩ :=
  Subtype.ext (by
    rw [T.coe_rot_plabicData hG]
    simp [RootedTree.rotAux, T.rot_intervalEnd_notMem hG, hb])

section SubstitutionSelf

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : ι → G.RootedTree} (hG : G.IsPlabicGraph)
  (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts)

include hdisj

omit [Fintype ι] [DecidableEq ι] hdisj in
private theorem forall_intervalEnd_ne_of_notMem {d : H} (hd : ∀ j, d ∉ (T j).darts) (j : ι) :
    (T j).intervalEnd ≠ d := fun h => hd j (h ▸ (T j).intervalEnd_mem_darts)

omit [DecidableEq ι] in
omit [Fintype ι] in
private theorem forall_intervalEnd_ne_of_mem {d : H} {j : ι} (hd : d ∈ (T j).darts)
    (hne : d ≠ (T j).intervalEnd) (j' : ι) : (T j').intervalEnd ≠ d := by
  classical
  rintro rfl
  by_cases hj : j' = j
  · subst hj; exact hne rfl
  · exact Finset.disjoint_left.1 (hdisj hj) (T j').intervalEnd_mem_darts hd

omit [Fintype ι] [DecidableEq ι] hdisj in
private theorem inl_notMem_substDarts {R : ι → PlabicGraph 1} {d : H} {j : ι}
    (hd : d ∈ (T j).darts) : (.inl d : H ⊕ Σ j, (R j).Dart) ∉ substDarts T R :=
  fun h => h j hd

omit [DecidableEq ι] in
/-- From the dead copy of `a₁` of `T j`, the glued rotation reaches the dart of `P_{T j}`
corresponding to `a₁` outside the darts of the substitution. -/
private theorem reachOutside_intervalStart (j : ι) :
    ReachOutside (substRot T fun j => (T j).toPlabicGraph hG)
      (substDarts T fun j => (T j).toPlabicGraph hG)
      (.inl (T j).intervalStart) (selfMap T hG (T j).intervalStart) := by
  classical
  have hinj := intervalEnd_injective hdisj
  rw [selfMap_of_mem hG hdisj (T j).intervalStart_mem_darts]
  by_cases hb : G.IsBoundaryVertex (T j).root
  · have hend := (T j).intervalEnd_eq_intervalStart hG hb
    have e1 := substRot_inl_intervalEnd (R := fun j => (T j).toPlabicGraph hG) hinj j
    rw [(T j).attachDart_toPlabicGraph_of_isBoundaryVertex hG hb, hend] at e1
    have e1' : (T j).plabicData.rot ⟨.inl (T j).intervalStart, (T j).intervalStart_mem_darts⟩ =
        (T j).dartEBar := by
      rw [← (T j).legDart_of_isBoundaryVertex hb]; exact (T j).rot_legDart hG
    change _ = (Sum.inr ⟨j, (T j).plabicData.rot _⟩ : H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart) at e1
    rw [e1'] at e1
    have hcut : ∀ x : (T j).Dart, x ∈ (T j).plabicData.bdry →
        (.inr ⟨j, x⟩ : H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart) ∉
          substDarts T fun j => (T j).toPlabicGraph hG :=
      fun x hx h => h (Or.inl hx)
    have hattach : (T j).attachDart ((T j).toPlabicGraph hG) = (T j).legDart := by
      rw [(T j).attachDart_toPlabicGraph_of_isBoundaryVertex hG hb,
        (T j).legDart_of_isBoundaryVertex hb]
    have e2 := substRot_inr_of_ne (T := T) (R := fun j => (T j).toPlabicGraph hG) hinj
      (j := j) (y := (T j).dartEBar) (by rw [hattach]; exact (T j).legDart_ne_dartEBar.symm)
    change _ = (Sum.inr ⟨j, (T j).plabicData.rot _⟩ : H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart) at e2
    rw [(T j).rot_dartEBar hG] at e2
    have e3 := substRot_inr_of_ne (T := T) (R := fun j => (T j).toPlabicGraph hG) hinj
      (j := j) (y := (T j).dartE) (by rw [hattach]; exact (T j).dartE_ne_legDart)
    change _ = (Sum.inr ⟨j, (T j).plabicData.rot _⟩ : H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart) at e3
    rw [(T j).rot_dartE hG, (T j).legDart_of_isBoundaryVertex hb] at e3
    exact ReachOutside.step e1 (hcut _ ((T j).mem_bdry_plabicData.2 (Or.inr rfl)))
      (ReachOutside.step e2 (hcut _ ((T j).mem_bdry_plabicData.2 (Or.inl rfl)))
        (ReachOutside.of_eq e3))
  · have key : ∀ n i, n + i = (T j).intervalLength - 1 →
        ReachOutside (substRot T fun j => (T j).toPlabicGraph hG)
          (substDarts T fun j => (T j).toPlabicGraph hG)
          (.inl ((G.rot ^ i) (T j).intervalStart))
          (.inr ⟨j, ⟨.inl (T j).intervalStart, (T j).intervalStart_mem_darts⟩⟩) := by
      intro n
      induction n with
      | zero =>
        intro i hi
        rw [zero_add] at hi
        subst hi
        apply ReachOutside.of_eq
        have e := substRot_inl_intervalEnd (R := fun j => (T j).toPlabicGraph hG) hinj j
        rw [(T j).attachDart_toPlabicGraph_of_not_isBoundaryVertex hG hb] at e
        change _ = (Sum.inr ⟨j, (T j).plabicData.rot _⟩ :
          H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart) at e
        rw [(T j).rot_gBar hG hb] at e
        exact e
      | succ n ih =>
        intro i hi
        have hk := (T j).intervalLength_lt_card
        have hmem : (G.rot ^ i) (T j).intervalStart ∈ (T j).darts :=
          (T j).pow_intervalStart_mem_darts (by omega)
        have hne : (G.rot ^ i) (T j).intervalStart ≠ (T j).intervalEnd := by
          intro h
          have := (T j).pow_intervalStart_injective (i := i) (j := (T j).intervalLength - 1)
            (by omega) (by omega) h
          omega
        have e := substRot_inl_of_forall_ne (R := fun j => (T j).toPlabicGraph hG) hinj
          (forall_intervalEnd_ne_of_mem hdisj hmem hne)
        have e' : G.rot ((G.rot ^ i) (T j).intervalStart) =
            (G.rot ^ (i + 1)) (T j).intervalStart := by
          rw [pow_succ', Perm.mul_apply]
        rw [e'] at e
        exact ReachOutside.step e
          (inl_notMem_substDarts ((T j).pow_intervalStart_mem_darts (by omega)))
          (ih (i + 1) (by omega))
    simpa using key ((T j).intervalLength - 1) 0 (by omega)

omit [DecidableEq ι] in
/-- Each step of `σ` is followed by the glued rotation of the substitution of the `P_{T j}`. -/
private theorem reachOutside_selfMap (d : H) :
    ReachOutside (substRot T fun j => (T j).toPlabicGraph hG)
      (substDarts T fun j => (T j).toPlabicGraph hG)
      (selfMap T hG d) (selfMap T hG (G.rot d)) := by
  classical
  have hinj := intervalEnd_injective hdisj
  -- after `σ a_k`, the image of `σ a_k` is reached
  have hafter : ∀ j, (∃ j', G.rot (T j).intervalEnd ∈ (T j').darts ∧
      ReachOutside (substRot T fun j => (T j).toPlabicGraph hG)
      (substDarts T fun j => (T j).toPlabicGraph hG)
      (.inl (G.rot (T j).intervalEnd)) (selfMap T hG (G.rot (T j).intervalEnd))) ∨
      (∀ j', G.rot (T j).intervalEnd ∉ (T j').darts) := by
    intro j
    by_cases h : ∀ j', G.rot (T j).intervalEnd ∉ (T j').darts
    · exact Or.inr h
    · push Not at h
      obtain ⟨j', hj'⟩ := h
      have hjj : j ≠ j' := by rintro rfl; exact (T j).rot_intervalEnd_notMem hG hj'
      have hstart : G.rot (T j).intervalEnd = (T j').intervalStart :=
        (T j').rot_eq_intervalStart hG
          (fun h => Finset.disjoint_left.1 (hdisj hjj) (T j).intervalEnd_mem_darts h) hj'
      left
      refine ⟨j', hj', ?_⟩
      rw [hstart]
      exact reachOutside_intervalStart hG hdisj j'
  by_cases hd : ∃ j, d ∈ (T j).darts
  · obtain ⟨j, hd⟩ := hd
    rw [selfMap_of_mem hG hdisj hd]
    by_cases hrd : G.rot d ∈ (T j).darts
    · rw [selfMap_of_mem hG hdisj hrd]
      apply ReachOutside.of_eq
      have hne : (⟨.inl d, hd⟩ : (T j).Dart) ≠ (T j).attachDart ((T j).toPlabicGraph hG) := by
        by_cases hb : G.IsBoundaryVertex (T j).root
        · rw [(T j).attachDart_toPlabicGraph_of_isBoundaryVertex hG hb]
          intro h
          have h' : d = (T j).intervalStart := by simpa using h
          subst h'
          exact (T j).rot_intervalStart_notMem_of_isBoundaryVertex hG hb hrd
        · rw [(T j).attachDart_toPlabicGraph_of_not_isBoundaryVertex hG hb]
          simp
      rw [substRot_inr_of_ne (R := fun j => (T j).toPlabicGraph hG) hinj hne]
      change (Sum.inr ⟨j, (T j).plabicData.rot _⟩ : H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart) = _
      rw [(T j).rot_inl_of_mem hG hd hrd]
    · have hend := (T j).eq_intervalEnd hG hd hrd
      subst hend
      have hlast : ReachOutside (substRot T fun j => (T j).toPlabicGraph hG)
          (substDarts T fun j => (T j).toPlabicGraph hG)
          (.inr ⟨j, ⟨.inl (T j).intervalEnd, hd⟩⟩) (.inl (G.rot (T j).intervalEnd)) := by
        by_cases hb : G.IsBoundaryVertex (T j).root
        · have ha : (⟨.inl (T j).intervalEnd, hd⟩ : (T j).Dart) =
              (T j).attachDart ((T j).toPlabicGraph hG) := by
            rw [(T j).attachDart_toPlabicGraph_of_isBoundaryVertex hG hb]
            simp [(T j).intervalEnd_eq_intervalStart hG hb]
          rw [ha]
          exact ReachOutside.of_eq (substRot_inr_attachDart hinj j)
        · have hne : (⟨.inl (T j).intervalEnd, hd⟩ : (T j).Dart) ≠
              (T j).attachDart ((T j).toPlabicGraph hG) := by
            rw [(T j).attachDart_toPlabicGraph_of_not_isBoundaryVertex hG hb]
            simp
          have e1 := substRot_inr_of_ne (R := fun j => (T j).toPlabicGraph hG) hinj hne
          change _ = (Sum.inr ⟨j, (T j).plabicData.rot _⟩ :
            H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart) at e1
          rw [(T j).rot_inl_intervalEnd hG hb] at e1
          have e2 := substRot_inr_attachDart (R := fun j => (T j).toPlabicGraph hG) hinj j
          rw [(T j).attachDart_toPlabicGraph_of_not_isBoundaryVertex hG hb] at e2
          refine ReachOutside.step e1 (fun h => h (Or.inr ⟨hb, Or.inr ?_⟩)) (ReachOutside.of_eq e2)
          exact ((T j).inv_legDart_of_not_isBoundaryVertex hG hb).symm
      rcases hafter j with ⟨j', hj', h⟩ | h
      · exact hlast.trans (inl_notMem_substDarts hj') h
      · rw [selfMap_of_notMem hG h]
        exact hlast
  · push Not at hd
    rw [selfMap_of_notMem hG hd]
    by_cases hrd : ∃ j, G.rot d ∈ (T j).darts
    · obtain ⟨j, hrd⟩ := hrd
      have hstart := (T j).rot_eq_intervalStart hG (hd j) hrd
      have e := substRot_inl_of_forall_ne (R := fun j => (T j).toPlabicGraph hG) hinj
        (forall_intervalEnd_ne_of_notMem hd)
      rw [hstart] at e ⊢
      exact ReachOutside.step e (inl_notMem_substDarts (T j).intervalStart_mem_darts)
        (reachOutside_intervalStart hG hdisj j)
    · push Not at hrd
      rw [selfMap_of_notMem hG hrd]
      exact ReachOutside.of_eq (substRot_inl_of_forall_ne hinj
        (forall_intervalEnd_ne_of_notMem hd))

end SubstitutionSelf

section SubstitutionSelfIso

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : ι → G.RootedTree} (hG : G.IsPlabicGraph)
  (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts)

/-- A left inverse of `selfMap`. -/
private noncomputable def selfUnmap (T : ι → G.RootedTree) (hG : G.IsPlabicGraph) :
    (H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart) → H
  | .inl d => d
  | .inr y => Sum.elim id (fun _ => (T y.1).intervalStart) (show (T y.1).Dart from y.2).1

include hdisj

omit [DecidableEq ι] in
private theorem selfUnmap_selfMap (d : H) : selfUnmap T hG (selfMap T hG d) = d := by
  classical
  by_cases hd : ∃ j, d ∈ (T j).darts
  · obtain ⟨j, hd⟩ := hd
    rw [selfMap_of_mem hG hdisj hd]
    rfl
  · push Not at hd
    rw [selfMap_of_notMem hG hd]
    rfl

omit [DecidableEq ι] in
private theorem selfMap_selfUnmap {x : H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart}
    (hx : x ∈ substDarts T fun j => (T j).toPlabicGraph hG) :
    selfMap T hG (selfUnmap T hG x) = x := by
  classical
  rcases x with d | ⟨j, ⟨d | l, hy⟩⟩
  · exact selfMap_of_notMem hG hx
  · exact selfMap_of_mem hG hdisj hy
  · exfalso
    apply hx
    rcases l with _ | _ | _ | _
    · exact Or.inl ((T j).mem_bdry_plabicData.2 (Or.inl rfl))
    · exact Or.inl ((T j).mem_bdry_plabicData.2 (Or.inr rfl))
    · refine Or.inr ⟨hy, Or.inl ?_⟩
      change _ = (T j).legDart
      rw [RootedTree.legDart, dif_neg hy]
    · refine Or.inr ⟨hy, Or.inr ?_⟩
      change _ = (T j).plabicData.inv (T j).legDart
      rw [(T j).inv_legDart_of_not_isBoundaryVertex hG hy]

/-- The darts of `G` are in bijection with the darts of the substitution of the `P_{T j}`. -/
private noncomputable def selfEquiv : H ≃ substDarts T fun j => (T j).toPlabicGraph hG :=
  Equiv.ofBijective (fun d => ⟨selfMap T hG d, selfMap_mem hG d⟩)
    ⟨fun d d' h => by
      have h' := congrArg Subtype.val h
      simp only at h'
      have h'' := congrArg (selfUnmap T hG) h'
      rwa [selfUnmap_selfMap hG hdisj, selfUnmap_selfMap hG hdisj] at h'',
     fun x => ⟨selfUnmap T hG x, Subtype.ext (selfMap_selfUnmap hG hdisj x.2)⟩⟩

omit [DecidableEq ι] in
private theorem coe_selfEquiv (d : H) :
    (selfEquiv hG hdisj d : H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart) = selfMap T hG d :=
  rfl

omit [DecidableEq ι] in
private theorem selfMap_inv (d : H) :
    selfMap T hG (G.inv d) = substInv G (fun j => (T j).toPlabicGraph hG) (selfMap T hG d) := by
  classical
  by_cases hd : ∃ j, d ∈ (T j).darts
  · obtain ⟨j, hd⟩ := hd
    rw [selfMap_of_mem hG hdisj hd, selfMap_of_mem hG hdisj ((T j).inv_mem_darts hG hd),
      substInv_inr]
    change _ = (Sum.inr ⟨j, (T j).plabicData.inv _⟩ : H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart)
    rw [(T j).inv_inl hG hd]
  · push Not at hd
    have hd' : ∀ j, G.inv d ∉ (T j).darts := fun j h => hd j (by
      simpa [hG.inv_involutive d] using (T j).inv_mem_darts hG h)
    rw [selfMap_of_notMem hG hd, selfMap_of_notMem hG hd', substInv_inl]

/-- **Substituting the plabic graphs of the trees gives back `G`.** -/
private noncomputable def selfIso :
    G.Iso (G.familySubstitution T (fun j => (T j).toPlabicGraph hG) hG) :=
  isoOfMapLeg (selfEquiv hG hdisj)
    (fun d => Subtype.ext (by
      rw [coe_familySubstitution_inv, coe_selfEquiv, coe_selfEquiv, selfMap_inv hG hdisj]))
    (fun d => Subtype.ext (by
      rw [coe_familySubstitution_rot, coe_selfEquiv]
      have := coe_firstReturn_of_simulation (σ := G.rot) (K := Set.univ)
        (Y := substDarts T fun j => (T j).toPlabicGraph hG) (selfMap T hG)
        (fun x => ⟨fun _ => trivial, fun _ => selfMap_mem hG x⟩)
        (reachOutside_selfMap hG hdisj) ⟨d, trivial⟩
      rw [coe_firstReturn_of_apply_mem (π := G.rot) (Y := Set.univ) (y := ⟨d, trivial⟩)
        trivial] at this
      exact this.symm))
    (fun d => by
      rw [mem_familySubstitution_bdry, coe_selfEquiv]
      by_cases hd : ∃ j, d ∈ (T j).darts
      · obtain ⟨j, hd⟩ := hd
        rw [selfMap_of_mem hG hdisj hd]
        simp only [reduceCtorEq, and_false, exists_false, false_iff]
        exact (T j).notMem_bdry_of_mem_darts hd
      · push Not at hd
        rw [selfMap_of_notMem hG hd]
        simp)
    (fun d _ => by
      rw [familySubstitution_colour, coe_selfEquiv]
      by_cases hd : ∃ j, d ∈ (T j).darts
      · obtain ⟨j, hd⟩ := hd
        rw [selfMap_of_mem hG hdisj hd]
        rfl
      · push Not at hd
        rw [selfMap_of_notMem hG hd]
        rfl)
    (fun i => Subtype.ext (by
      rw [coe_selfEquiv]
      by_cases hi : ∃ j, G.leg i ∈ (T j).darts
      · obtain ⟨j, hi⟩ := hi
        rw [selfMap_of_mem hG hdisj hi, coe_familySubstitution_leg_of_mem hG hdisj hi]
        have hb : G.IsBoundaryVertex (T j).root := by
          rw [(T j).root_eq_bvertex_of_leg_mem hG hi]
          exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
        change _ = (Sum.inr ⟨j, (T j).legDart⟩ : H ⊕ Σ j, ((T j).toPlabicGraph hG).Dart)
        rw [(T j).legDart_of_isBoundaryVertex hb]
        have := (T j).leg_eq_intervalStart hG hi
        exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Subtype.ext (congrArg Sum.inl this))))
      · push Not at hi
        rw [selfMap_of_notMem hG hi, coe_familySubstitution_leg_of_notMem hG hi]))

omit [DecidableEq ι] in
/-- No leg of the substitution is a boundary arc. -/
theorem familySubstitution_legs_notMem (R : ι → PlabicGraph 1) (i : Fin b) :
    (G.familySubstitution T R hG).leg i ∉ (G.familySubstitution T R hG).bdry := by
  classical
  rw [mem_familySubstitution_bdry]
  rintro ⟨d, hd, h⟩
  by_cases hi : ∃ j, G.leg i ∈ (T j).darts
  · obtain ⟨j, hi⟩ := hi
    rw [coe_familySubstitution_leg_of_mem hG hdisj hi] at h
    simp at h
  · push Not at hi
    rw [coe_familySubstitution_leg_of_notMem hG hi, Sum.inl.injEq] at h
    exact hG.leg_notMem_bdry i (h ▸ hd)

/-- The substitution of the plabic graphs `P_{T j}` into a family of trees with disjoint darts is
isomorphic to `G`, and so is a plabic graph. -/
theorem isomorphic_familySubstitution_toPlabicGraph :
    G.Isomorphic (G.familySubstitution T (fun j => (T j).toPlabicGraph hG) hG) :=
  ⟨selfIso hG hdisj⟩

/-- Substituting into each tree `T j` its own plabic graph gives a plabic graph. -/
theorem isPlabicGraph_familySubstitution_toPlabicGraph :
    (G.familySubstitution T (fun j => (T j).toPlabicGraph hG) hG).IsPlabicGraph :=
  (selfIso hG hdisj).isPlabicGraph hG (familySubstitution_legs_notMem hG hdisj _)

end SubstitutionSelfIso

/-! ### Isomorphic fillings give isomorphic substitutions -/

-- Note: `IsPlabicGraph.rot_leg_mem_bdry` in Excision.lean (not imported here) states the same.
/-- At a boundary vertex `β(i)`, the dart `σ(g_i)` lies in `B`. -/
private theorem IsPlabicGraph.rot_leg_mem_bdry' (hG : G.IsPlabicGraph) (i : Fin b) :
    G.rot (G.leg i) ∈ G.bdry := by
  have hv : G.IsBoundaryVertex (G.vertexOf (G.leg i)) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  by_contra h
  exact DiskMap.rot_ne_of_isBoundaryVertex hG.boundaryVertex_card hv
    (DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card hv (G.rot_mem_vertexOf _)
      (G.self_mem_vertexOf _) h (hG.leg_notMem_bdry i))

/-- An isomorphism of fillings sends the attaching dart to the attaching dart. -/
theorem RootedTree.attachDart_iso (T₀ : G.RootedTree) {Q Q' : PlabicGraph 1}
    (θ : Q.data.Iso Q'.data) : θ.toEquiv (T₀.attachDart Q) = T₀.attachDart Q' := by
  have hl := Iso.map_leg Q.isPlabicGraph Q'.isPlabicGraph θ 0
  unfold RootedTree.attachDart
  split_ifs
  · exact hl
  · rw [θ.map_inv, hl]

/-- An isomorphism of fillings preserves cut darts. -/
theorem RootedTree.isCutDart_iso_iff (T₀ : G.RootedTree) {Q Q' : PlabicGraph 1}
    (θ : Q.data.Iso Q'.data) (y : Q.Dart) :
    T₀.IsCutDart Q' (θ.toEquiv y) ↔ T₀.IsCutDart Q y := by
  have hl := Iso.map_leg Q.isPlabicGraph Q'.isPlabicGraph θ 0
  unfold RootedTree.IsCutDart
  rw [θ.mem_bdry_iff, ← hl, ← θ.map_inv, θ.toEquiv.injective.eq_iff,
    θ.toEquiv.injective.eq_iff]

section SubstitutionIso

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : ι → G.RootedTree} (hG : G.IsPlabicGraph)
  (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts)

include hdisj

/-- A dart of a filling at its boundary vertex that survives in the substitution (the leg, for a
boundary root) lies at a boundary vertex of the substitution. -/
theorem isBoundaryVertex_familySubstitution_of_isBoundaryVertex {R : ι → PlabicGraph 1}
    {x : substDarts T R} {j : ι} {y : (R j).Dart} (hx : (x : H ⊕ Σ j, (R j).Dart) = .inr ⟨j, y⟩)
    (hy : (R j).data.IsBoundaryVertex ((R j).data.vertexOf y)) :
    (G.familySubstitution T R hG).IsBoundaryVertex ((G.familySubstitution T R hG).vertexOf x) := by
  have hinj := intervalEnd_injective hdisj
  have hlive : ¬(T j).IsCutDart (R j) y := by
    have := x.2
    rwa [hx] at this
  have hyB : y ∉ (R j).data.bdry := fun h => hlive (Or.inl h)
  obtain ⟨i₀, rfl⟩ := (R j).isPlabicGraph.exists_eq_leg_of_isBoundaryVertex hy hyB
  obtain rfl : i₀ = 0 := Subsingleton.elim _ _
  have hb : G.IsBoundaryVertex (T j).root := by
    by_contra hb
    exact hlive (Or.inr ⟨hb, Or.inl rfl⟩)
  obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.mem_boundaryVertices.2 ⟨(T j).root_mem_vertices, hb⟩)
  have hstart := (T j).intervalStart_eq_leg hG hi.symm
  have hend := (T j).intervalEnd_eq_intervalStart hG hb
  have hatt : (T j).attachDart (R j) = (R j).data.leg 0 := by
    rw [RootedTree.attachDart, if_pos hb]
  have e := substRot_inr_attachDart (R := R) hinj j
  rw [hatt, hend, hstart] at e
  have hBmem := hG.rot_leg_mem_bdry' i
  have hmem : (.inl (G.rot (G.leg i)) : H ⊕ Σ j, (R j).Dart) ∈ substDarts T R :=
    fun j' hj' => (T j').notMem_bdry_of_mem_darts hj' hBmem
  have hrot : ((G.familySubstitution T R hG).rot x : H ⊕ Σ j, (R j).Dart) =
      .inl (G.rot (G.leg i)) := by
    rw [coe_familySubstitution_rot, coe_firstReturn_of_apply_mem (by rw [hx, e]; exact hmem), hx, e]
  refine ⟨(G.familySubstitution T R hG).rot x, (G.familySubstitution T R hG).rot_mem_vertexOf x, ?_⟩
  rw [mem_familySubstitution_bdry]
  exact ⟨_, hBmem, hrot⟩

/-- A live dart of a filling at an internal vertex of the substitution lies at an internal vertex
of the filling. -/
theorem not_isBoundaryVertex_of_familySubstitution {R : ι → PlabicGraph 1}
    {x : substDarts T R} {j : ι} {y : (R j).Dart} (hx : (x : H ⊕ Σ j, (R j).Dart) = .inr ⟨j, y⟩)
    (h : ¬(G.familySubstitution T R hG).IsBoundaryVertex
      ((G.familySubstitution T R hG).vertexOf x)) :
    ¬(R j).data.IsBoundaryVertex ((R j).data.vertexOf y) :=
  fun hy => h (isBoundaryVertex_familySubstitution_of_isBoundaryVertex hG hdisj hx hy)

variable {R R' : ι → PlabicGraph 1}

/-- The bijection of ambient darts induced by maps of the fillings. -/
private def substMap (φ : ∀ j, (R j).Dart → (R' j).Dart) :
    H ⊕ (Σ j, (R j).Dart) → H ⊕ Σ j, (R' j).Dart :=
  Sum.map id fun y => ⟨y.1, φ y.1 y.2⟩

/-- **Isomorphic fillings give isomorphic substitutions.** -/
theorem familySubstitution_isomorphic (θ : ∀ j, (R j).data.Iso (R' j).data) :
    (G.familySubstitution T R hG).Isomorphic (G.familySubstitution T R' hG) := by
  have hinj := intervalEnd_injective hdisj
  have hinj' := intervalEnd_injective hdisj
  set Θ : (H ⊕ Σ j, (R j).Dart) ≃ (H ⊕ Σ j, (R' j).Dart) :=
    Equiv.sumCongr (Equiv.refl H) (Equiv.sigmaCongrRight fun j => (θ j).toEquiv) with hΘ
  have hΘx : ∀ x, Θ x = substMap (fun j => (θ j).toEquiv) x := fun x => by
    rcases x with d | y <;> rfl
  have hmem : ∀ x, Θ x ∈ substDarts T R' ↔ x ∈ substDarts T R := by
    rintro (d | ⟨j, y⟩)
    · exact Iff.rfl
    · exact not_congr ((T j).isCutDart_iso_iff (θ j) y)
  have hrot : ∀ x, Θ (substRot T R x) = substRot T R' (Θ x) := by
    rintro (d | ⟨j, y⟩)
    · by_cases h : ∃ j, (T j).intervalEnd = d
      · obtain ⟨j, rfl⟩ := h
        rw [substRot_inl_intervalEnd hinj]
        change (Sum.inr ⟨j, (θ j).toEquiv ((R j).data.rot ((T j).attachDart (R j)))⟩ :
          H ⊕ Σ j, (R' j).Dart) = substRot T R' (.inl (T j).intervalEnd)
        rw [substRot_inl_intervalEnd hinj', (θ j).map_rot, (T j).attachDart_iso (θ j)]
      · push Not at h
        rw [substRot_inl_of_forall_ne hinj h]
        change (Sum.inl (G.rot d) : H ⊕ Σ j, (R' j).Dart) = substRot T R' (.inl d)
        rw [substRot_inl_of_forall_ne hinj' h]
    · by_cases hy : y = (T j).attachDart (R j)
      · subst hy
        rw [substRot_inr_attachDart hinj]
        change (Sum.inl (G.rot (T j).intervalEnd) : H ⊕ Σ j, (R' j).Dart) =
          substRot T R' (.inr ⟨j, (θ j).toEquiv ((T j).attachDart (R j))⟩)
        rw [(T j).attachDart_iso (θ j), substRot_inr_attachDart hinj']
      · rw [substRot_inr_of_ne hinj hy]
        have hy' : (θ j).toEquiv y ≠ (T j).attachDart (R' j) := by
          rw [← (T j).attachDart_iso (θ j)]
          exact (θ j).toEquiv.injective.ne hy
        change (Sum.inr ⟨j, (θ j).toEquiv ((R j).data.rot y)⟩ : H ⊕ Σ j, (R' j).Dart) =
          substRot T R' (.inr ⟨j, (θ j).toEquiv y⟩)
        rw [substRot_inr_of_ne hinj' hy', (θ j).map_rot]
  have hinv : ∀ x, Θ (substInv G R x) = substInv G R' (Θ x) := by
    rintro (d | ⟨j, y⟩)
    · rfl
    · change (Sum.inr ⟨j, (θ j).toEquiv ((R j).data.inv y)⟩ : H ⊕ Σ j, (R' j).Dart) =
        Sum.inr ⟨j, (R' j).data.inv ((θ j).toEquiv y)⟩
      rw [(θ j).map_inv]
  refine ⟨isoOfMapLeg (Θ.subtypeEquiv fun x => (hmem x).symm) (fun x => Subtype.ext ?_)
    (fun x => Subtype.ext ?_) (fun x => ?_) (fun x hx => ?_) (fun i => Subtype.ext ?_)⟩
  · simp only [Equiv.subtypeEquiv_apply]
    rw [coe_familySubstitution_inv, coe_familySubstitution_inv, hinv]
  · simp only [Equiv.subtypeEquiv_apply]
    rw [coe_familySubstitution_rot, coe_familySubstitution_rot]
    exact (coe_firstReturn_of_semiconj_map Θ hrot hmem x).symm
  · simp only [mem_familySubstitution_bdry, Equiv.subtypeEquiv_apply]
    rcases x with ⟨d | y, hx⟩
    · simp [hΘ]
    · simp [hΘ]
  · rcases x with ⟨d | ⟨j, y⟩, hx⟩
    · rfl
    · simp only [familySubstitution_colour, Equiv.subtypeEquiv_apply]
      change (R' j).data.colour ((θ j).toEquiv y) = (R j).data.colour y
      exact (θ j).map_colour y (not_isBoundaryVertex_of_familySubstitution hG hdisj rfl hx)
  · simp only [Equiv.subtypeEquiv_apply]
    by_cases hi : ∃ j, G.leg i ∈ (T j).darts
    · obtain ⟨j, hi⟩ := hi
      rw [coe_familySubstitution_leg_of_mem hG hdisj hi,
        coe_familySubstitution_leg_of_mem hG hdisj hi]
      change (Sum.inr ⟨j, (θ j).toEquiv ((R j).data.leg 0)⟩ : H ⊕ Σ j, (R' j).Dart) = _
      rw [Iso.map_leg (R j).isPlabicGraph (R' j).isPlabicGraph]
    · push Not at hi
      rw [coe_familySubstitution_leg_of_notMem hG hi, coe_familySubstitution_leg_of_notMem hG hi]
      rfl

end SubstitutionIso

/-! ### Removals and contractions as cuts -/

section Cut

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {b' : ℕ}

-- Note: CollapseCuts.lean (downstream) has a public `cutData` with the same companion lemmas.
/-- The tuple on `{p, q}ᶜ` whose involution and rotation are the first returns of `ι ∘ (p q)` and
`σ ∘ (p q)`. Removals of bivalent vertices and contractions of edges are of this form. -/
private noncomputable def cutData (Q : PlabicData Y b') (p q : Y)
    (hleg : ∀ i, Q.leg i ∈ ({p, q}ᶜ : Set Y)) : PlabicData ({p, q}ᶜ : Set Y) b' where
  inv := firstReturnPerm (Q.inv * swap p q) _
  rot := firstReturnPerm (Q.rot * swap p q) _
  bdry := Q.bdry.subtype (· ∈ ({p, q}ᶜ : Set Y))
  colour y := Q.colour y
  leg i := ⟨Q.leg i, hleg i⟩

omit [Fintype Y] [DecidableEq Y] in
private theorem plabicData_ext {Q Q' : PlabicData Y b'} (h₁ : Q.inv = Q'.inv)
    (h₂ : Q.rot = Q'.rot) (h₃ : Q.bdry = Q'.bdry) (h₄ : Q.colour = Q'.colour)
    (h₅ : Q.leg = Q'.leg) : Q = Q' := by
  rcases Q with ⟨⟨⟨i, r⟩, B⟩, c, l⟩
  rcases Q' with ⟨⟨⟨i', r'⟩, B'⟩, c', l'⟩
  simp only at h₁ h₂ h₃ h₄ h₅
  subst h₁ h₂ h₃ h₄ h₅
  rfl

/-- The removal of a bivalent vertex `{d, σ d}` is the cut along `d, σ d`. -/
private theorem bivalentRemoval_eq_cutData {Q : PlabicData Y b'} (hQ : Q.IsPlabicGraph) {d : Y}
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
private theorem contractEdge_eq_cutData {Q : PlabicData Y b'} (hinv : Involutive Q.inv) {d : Y}
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

end Cut

/-! ### A reduction step of a filling is a local move of the substitution -/

section Lift

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : ι → G.RootedTree} (hG : G.IsPlabicGraph)
  (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts) {R R' : ι → PlabicGraph 1}

/-- Maps from the darts of `R' j` to the darts of `R j`, given by `f₀` at `j₀` and by `θ`
elsewhere. -/
private noncomputable def liftMap (j₀ : ι) (f₀ : (R' j₀).Dart → (R j₀).Dart)
    (θ : ∀ j, j ≠ j₀ → (R' j).Dart → (R j).Dart) (j : ι) : (R' j).Dart → (R j).Dart :=
  if h : j = j₀ then by subst h; exact f₀ else θ j h

omit [Fintype ι] in
private theorem liftMap_self (j₀ : ι) (f₀ : (R' j₀).Dart → (R j₀).Dart)
    (θ : ∀ j, j ≠ j₀ → (R' j).Dart → (R j).Dart) : liftMap j₀ f₀ θ j₀ = f₀ := by
  rw [liftMap, dif_pos rfl]

omit [Fintype ι] in
private theorem liftMap_of_ne (j₀ : ι) (f₀ : (R' j₀).Dart → (R j₀).Dart)
    (θ : ∀ j, j ≠ j₀ → (R' j).Dart → (R j).Dart) {j : ι} (h : j ≠ j₀) :
    liftMap j₀ f₀ θ j = θ j h := by
  rw [liftMap, dif_neg h]

/-- The cut of the `j₀`-th filling, bundled. -/
private noncomputable def cutGraph (j₀ : ι) {p q : (R j₀).Dart}
    (hlegc : ∀ i, (R j₀).data.leg i ∈ ({p, q}ᶜ : Set (R j₀).Dart))
    (hC : (cutData (R j₀).data p q hlegc).IsPlabicGraph) : PlabicGraph 1 :=
  ⟨_, cutData (R j₀).data p q hlegc, hC⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem coe_attachDart_cutGraph (j₀ : ι) {p q : (R j₀).Dart}
    (hp : ¬(T j₀).IsCutDart (R j₀) p) (hq : ¬(T j₀).IsCutDart (R j₀) q)
    (hlegc : ∀ i, (R j₀).data.leg i ∈ ({p, q}ᶜ : Set (R j₀).Dart))
    (hC : (cutData (R j₀).data p q hlegc).IsPlabicGraph) :
    @Subtype.val (R j₀).Dart (· ∈ ({p, q}ᶜ : Set (R j₀).Dart))
      ((T j₀).attachDart (cutGraph j₀ hlegc hC)) =
      (T j₀).attachDart (R j₀) := by
  unfold RootedTree.attachDart
  split_ifs with hb
  · rfl
  · have hl : (R j₀).data.leg 0 ∈ ({p, q}ᶜ : Set (R j₀).Dart) := hlegc 0
    have hlm : (R j₀).data.inv ((R j₀).data.leg 0) ∈ ({p, q}ᶜ : Set (R j₀).Dart) := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨fun h => hp (Or.inr ⟨hb, Or.inr h.symm⟩), fun h => hq (Or.inr ⟨hb, Or.inr h.symm⟩)⟩
    change ((firstReturn ((R j₀).data.inv * swap p q) _ _ : ({p, q}ᶜ : Set (R j₀).Dart)) :
      (R j₀).Dart) = _
    have e : ((R j₀).data.inv * swap p q) ((R j₀).data.leg 0) =
        (R j₀).data.inv ((R j₀).data.leg 0) := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hl
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hl.1 hl.2]
    exact (coe_firstReturn_of_apply_mem (π := (R j₀).data.inv * swap p q)
      (Y := ({p, q}ᶜ : Set (R j₀).Dart)) (y := ⟨(R j₀).data.leg 0, hl⟩)
      (by rwa [e])).trans e

omit [Fintype H] [Fintype ι] in
/-- A transposition of two points of a component commutes with the inclusion of the component. -/
private theorem swap_inr_sigma {β : ι → Type} [∀ j, DecidableEq (β j)] (j₀ : ι) (a c u : β j₀) :
    swap (.inr ⟨j₀, a⟩ : H ⊕ Σ j, β j) (.inr ⟨j₀, c⟩) (.inr ⟨j₀, u⟩) = .inr ⟨j₀, swap a c u⟩ := by
  rw [swap_apply_def, swap_apply_def]
  split_ifs <;> simp_all

omit [Fintype H] [Fintype ι] in
private theorem swap_inr_sigma_of_ne {β : ι → Type} [∀ j, DecidableEq (β j)] (j₀ : ι) (a c : β j₀)
    {x : H ⊕ Σ j, β j} (h : ∀ u, x = .inr ⟨j₀, u⟩ → u ≠ a ∧ u ≠ c) :
    swap (.inr ⟨j₀, a⟩ : H ⊕ Σ j, β j) (.inr ⟨j₀, c⟩) x = x :=
  swap_apply_of_ne_of_ne (fun hx => (h a hx).1 rfl) (fun hx => (h c hx).2 rfl)

include hdisj in
/-- **The substitution of a cut filling is the cut of the substitution.** If `R' j₀` is
isomorphic to the cut of `R j₀` along two surviving darts `p, q` other than the attaching dart,
and `R' j ≅ R j` for `j ≠ j₀`, then the substitution of the `R'` is isomorphic to the cut of the
substitution of the `R` along `p, q`. -/
private theorem familySubstitution_isomorphic_cutData (j₀ : ι) {p q : (R j₀).Dart}
    (hp : ¬(T j₀).IsCutDart (R j₀) p) (hq : ¬(T j₀).IsCutDart (R j₀) q)
    (hpa : p ≠ (T j₀).attachDart (R j₀)) (hqa : q ≠ (T j₀).attachDart (R j₀))
    (hlegc : ∀ i, (R j₀).data.leg i ∈ ({p, q}ᶜ : Set (R j₀).Dart))
    (hC : (cutData (R j₀).data p q hlegc).IsPlabicGraph)
    (θ₀ : (R' j₀).data.Iso (cutGraph j₀ hlegc hC).data)
    (θ : ∀ j, j ≠ j₀ → (R' j).data.Iso (R j).data)
    (P Q : substDarts T R) (hP : (P : H ⊕ Σ j, (R j).Dart) = .inr ⟨j₀, p⟩)
    (hQ : (Q : H ⊕ Σ j, (R j).Dart) = .inr ⟨j₀, q⟩)
    (hlegS : ∀ i, (G.familySubstitution T R hG).leg i ∈ ({P, Q}ᶜ : Set (substDarts T R))) :
    (G.familySubstitution T R' hG).Isomorphic
      (cutData (G.familySubstitution T R hG) P Q hlegS) := by
  have hinj := intervalEnd_injective hdisj
  -- the maps between the darts of the fillings
  set φ := liftMap j₀ (R := R) (R' := R')
    (fun y => (@Subtype.val (R j₀).Dart (· ∈ ({p, q}ᶜ : Set (R j₀).Dart)) (θ₀.toEquiv y)))
    (fun j h => (θ j h).toEquiv) with hφdef
  have hφ0 : ∀ y, φ j₀ y =
      (@Subtype.val (R j₀).Dart (· ∈ ({p, q}ᶜ : Set (R j₀).Dart)) (θ₀.toEquiv y)) :=
    fun y => by rw [hφdef, liftMap_self]
  have hφj : ∀ j (h : j ≠ j₀) y, φ j y = (θ j h).toEquiv y := fun j h y => by
    rw [hφdef, liftMap_of_ne _ _ _ h]
  have hφinj : ∀ j, Injective (φ j) := by
    intro j
    by_cases h : j = j₀
    · subst h
      intro y y' hyy
      rw [hφ0, hφ0] at hyy
      exact θ₀.toEquiv.injective (Subtype.ext hyy)
    · intro y y' hyy
      rw [hφj j h, hφj j h] at hyy
      exact (θ j h).toEquiv.injective hyy
  have hS0 : ∀ y, (@Subtype.val (R j₀).Dart (· ∈ ({p, q}ᶜ : Set (R j₀).Dart)) (θ₀.toEquiv y)) ∈
      ({p, q}ᶜ : Set (R j₀).Dart) := fun y => (θ₀.toEquiv y).2
  have hattach0 : φ j₀ ((T j₀).attachDart (R' j₀)) = (T j₀).attachDart (R j₀) := by
    rw [hφ0, (T j₀).attachDart_iso θ₀]
    exact coe_attachDart_cutGraph j₀ hp hq hlegc hC
  have hattachj : ∀ j (h : j ≠ j₀), φ j ((T j).attachDart (R' j)) = (T j).attachDart (R j) :=
    fun j h => by rw [hφj j h, (T j).attachDart_iso (θ j h)]
  have hattach : ∀ j y, φ j y = (T j).attachDart (R j) ↔ y = (T j).attachDart (R' j) := by
    intro j y
    by_cases h : j = j₀
    · subst h
      rw [← hattach0]
      exact (hφinj _).eq_iff
    · rw [← hattachj j h]
      exact (hφinj _).eq_iff
  have hattS : (T j₀).attachDart (R j₀) ∈ ({p, q}ᶜ : Set (R j₀).Dart) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hpa.symm, hqa.symm⟩
  set Ψ : (H ⊕ Σ j, (R' j).Dart) → H ⊕ Σ j, (R j).Dart := substMap φ with hΨdef
  have hΨl : ∀ d, Ψ (.inl d) = .inl d := fun d => rfl
  have hΨr : ∀ j y, Ψ (.inr ⟨j, y⟩) = .inr ⟨j, φ j y⟩ := fun j y => rfl
  have hΨinj : Injective Ψ := by
    rintro (d | ⟨j, y⟩) (d' | ⟨j', y'⟩) h
    · simpa [hΨl] using h
    · simp [hΨl, hΨr] at h
    · simp [hΨl, hΨr] at h
    · rw [hΨr, hΨr] at h
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      rw [hφinj j (eq_of_heq h)]
  -- the set of darts of the cut substitution, inside the ambient darts
  set Tc : Set (H ⊕ Σ j, (R j).Dart) :=
    {z | z ∈ substDarts T R ∧ z ≠ .inr ⟨j₀, p⟩ ∧ z ≠ .inr ⟨j₀, q⟩} with hTcdef
  have hcut0 : ∀ z : ({p, q}ᶜ : Set (R j₀).Dart),
      (T j₀).IsCutDart (cutGraph j₀ hlegc hC) z ↔ (T j₀).IsCutDart (R j₀) z := by
    intro z
    unfold RootedTree.IsCutDart
    have hb : z ∈ (cutGraph j₀ hlegc hC).data.bdry ↔ (z : (R j₀).Dart) ∈ (R j₀).data.bdry :=
      mem_subtype
    refine or_congr hb (and_congr_right fun hb' => or_congr ?_ ?_)
    · exact Subtype.ext_iff
    · have hatt := coe_attachDart_cutGraph j₀ hp hq hlegc hC
      unfold RootedTree.attachDart at hatt
      rw [if_neg hb', if_neg hb'] at hatt
      exact ⟨fun h => (congrArg Subtype.val h).trans hatt, fun h => Subtype.ext (h.trans hatt.symm)⟩
  have hmem : ∀ x', Ψ x' ∈ Tc ↔ x' ∈ substDarts T R' := by
    rintro (d | ⟨j, y⟩)
    · rw [hΨl]
      simp [hTcdef, inl_mem_substDarts]
    · rw [hΨr]
      simp only [hTcdef, Set.mem_setOf_eq, inr_mem_substDarts]
      by_cases h : j = j₀
      · subst h
        rw [hφ0]
        have hne := hS0 y
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
        simp only [ne_eq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and, hne.1, hne.2,
          not_false_eq_true, and_true]
        rw [← hcut0, (T j).isCutDart_iso_iff θ₀]
      · rw [hφj j h, (T j).isCutDart_iso_iff (θ j h)]
        simp [h]
  have hsurj : ∀ w ∈ Tc, ∃ x', Ψ x' = w := by
    rintro (d | ⟨j, u⟩) hw
    · exact ⟨.inl d, rfl⟩
    · by_cases h : j = j₀
      · subst h
        have hu : u ∈ ({p, q}ᶜ : Set (R j).Dart) := by
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨fun h' => hw.2.1 (by rw [h']), fun h' => hw.2.2 (by rw [h'])⟩
        refine ⟨.inr ⟨j, θ₀.toEquiv.symm ⟨u, hu⟩⟩, ?_⟩
        rw [hΨr, hφ0]
        simp
      · refine ⟨.inr ⟨j, (θ j h).toEquiv.symm u⟩, ?_⟩
        rw [hΨr, hφj j h]
        simp
  -- the rotation and involution of the cut substitution
  set sw := swap (.inr ⟨j₀, p⟩ : H ⊕ Σ j, (R j).Dart) (.inr ⟨j₀, q⟩) with hsw
  have hswP : swap (P : H ⊕ Σ j, (R j).Dart) Q = sw := by rw [hP, hQ]
  have hTc : ∀ x, x ∈ Tc ↔ ∃ h : x ∈ substDarts T R, (⟨x, h⟩ : substDarts T R) ∈
      ({P, Q}ᶜ : Set (substDarts T R)) := by
    intro x
    simp only [hTcdef, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or]
    constructor
    · rintro ⟨hx, h1, h2⟩
      exact ⟨hx, fun h => h1 (by rw [← hP, ← h]), fun h => h2 (by rw [← hQ, ← h])⟩
    · rintro ⟨hx, h1, h2⟩
      exact ⟨hx, fun h => h1 (Subtype.ext (h.trans hP.symm)),
        fun h => h2 (Subtype.ext (h.trans hQ.symm))⟩
  have hcutRot : ∀ z : ({P, Q}ᶜ : Set (substDarts T R)),
      (((cutData (G.familySubstitution T R hG) P Q hlegS).rot z : substDarts T R) :
        H ⊕ Σ j, (R j).Dart) =
        firstReturn (substRot T R * sw) Tc ⟨(z : substDarts T R), (hTc _).2 ⟨_, z.2⟩⟩ := by
    intro z
    change ((firstReturn ((G.familySubstitution T R hG).rot * swap P Q) _ z : substDarts T R) :
      H ⊕ Σ j, (R j).Dart) = _
    have : (G.familySubstitution T R hG).rot * swap P Q =
        firstReturnPerm (substRot T R * sw) (substDarts T R) := by
      rw [← hswP, firstReturnPerm_mul_swap']
      rfl
    rw [this, coe_coe_firstReturn_firstReturnPerm _ hTc]
  have hcutInv : ∀ z : ({P, Q}ᶜ : Set (substDarts T R)),
      (((cutData (G.familySubstitution T R hG) P Q hlegS).inv z : substDarts T R) :
        H ⊕ Σ j, (R j).Dart) =
        firstReturn (substInv G R * sw) Tc ⟨(z : substDarts T R), (hTc _).2 ⟨_, z.2⟩⟩ := by
    intro z
    change ((firstReturn ((G.familySubstitution T R hG).inv * swap P Q) _ z : substDarts T R) :
      H ⊕ Σ j, (R j).Dart) = _
    have : (G.familySubstitution T R hG).inv * swap P Q =
        firstReturnPerm (substInv G R * sw) (substDarts T R) := by
      rw [← hswP, firstReturnPerm_mul_swap']
      rfl
    rw [this, coe_coe_firstReturn_firstReturnPerm _ hTc]
  -- one step of the rotation of the fillings `R'`
  have hpq_ne_attach : ∀ u : (R j₀).Dart, u ≠ (T j₀).attachDart (R j₀) →
      swap p q u ≠ (T j₀).attachDart (R j₀) := fun u hu h =>
    hu ((swap p q).injective (h.trans (swap_apply_of_ne_of_ne hpa.symm hqa.symm).symm))
  have hπ : ∀ u, u ≠ (T j₀).attachDart (R j₀) →
      (substRot T R * sw) (.inr ⟨j₀, u⟩) = .inr ⟨j₀, ((R j₀).data.rot * swap p q) u⟩ := by
    intro u hu
    rw [Perm.mul_apply, hsw, swap_inr_sigma (β := fun j => (R j).Dart),
      substRot_inr_of_ne hinj (hpq_ne_attach u hu)]
    rfl
  have hπi : ∀ u, (substInv G R * sw) (.inr ⟨j₀, u⟩) =
      .inr ⟨j₀, ((R j₀).data.inv * swap p q) u⟩ := by
    intro u
    rw [Perm.mul_apply, hsw, swap_inr_sigma]
    rfl
  have hswfix : ∀ x : H ⊕ Σ j, (R j).Dart, (∀ u, x = .inr ⟨j₀, u⟩ → u ≠ p ∧ u ≠ q) →
      sw x = x := fun x h => swap_inr_sigma_of_ne (β := fun j => (R j).Dart) j₀ p q h
  have hswl : ∀ d, sw (.inl d) = .inl d := fun d => hswfix _ (by simp)
  have hswj : ∀ j (h : j ≠ j₀) (u : (R j).Dart), sw (.inr ⟨j, u⟩) = .inr ⟨j, u⟩ :=
    fun j h u => hswfix _ (by
      intro u' hu'
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at hu'
      exact absurd hu'.1 h)
  have hsw0 : ∀ y, sw (.inr ⟨j₀, φ j₀ y⟩) = .inr ⟨j₀, φ j₀ y⟩ := fun y => hswfix _ (by
    intro u hu
    simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hu
    have := hS0 y
    rw [← hφ0, hu] at this
    simpa [not_or] using this)
  have hf : ∀ z : (R j₀).Dart, z ∉ ({p, q}ᶜ : Set (R j₀).Dart) →
      (.inr ⟨j₀, z⟩ : H ⊕ Σ j, (R j).Dart) ∉ Tc := by
    intro z hz hzT
    simp only [Set.mem_compl_iff, not_not, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hzT.2.1 rfl
    · exact hzT.2.2 rfl
  have hstepRot : ∀ x', ReachOutside (substRot T R * sw) Tc (Ψ x') (Ψ (substRot T R' x')) := by
    rintro (d | ⟨j, y⟩)
    · by_cases hd : ∃ j, (T j).intervalEnd = d
      · obtain ⟨j, rfl⟩ := hd
        rw [substRot_inl_intervalEnd hinj, hΨl, hΨr]
        have e1 : (substRot T R * sw) (.inl (T j).intervalEnd) =
            .inr ⟨j, (R j).data.rot ((T j).attachDart (R j))⟩ := by
          rw [Perm.mul_apply, hswl, substRot_inl_intervalEnd hinj]
        by_cases h : j = j₀
        · subst h
          rw [hφ0, θ₀.map_rot]
          have hA : (θ₀.toEquiv ((T j).attachDart (R' j)) : ({p, q}ᶜ : Set (R j).Dart)) =
              ⟨(T j).attachDart (R j), hattS⟩ :=
            Subtype.ext (by rwa [← hφ0])
          rw [hA]
          change ReachOutside _ _ _ (Sum.inr ⟨j, ((firstReturn ((R j).data.rot * swap p q) _ _ :
            ({p, q}ᶜ : Set (R j).Dart)) : (R j).Dart)⟩ : H ⊕ Σ j, (R j).Dart)
          have hw : ((R j).data.rot * swap p q) ((T j).attachDart (R j)) =
              (R j).data.rot ((T j).attachDart (R j)) := by
            rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpa.symm hqa.symm]
          by_cases hwS : (R j).data.rot ((T j).attachDart (R j)) ∈ ({p, q}ᶜ : Set (R j).Dart)
          · rw [coe_firstReturn_of_apply_mem (by rwa [hw]), hw]
            exact ReachOutside.of_eq e1
          · refine ReachOutside.step e1 (hf _ hwS) ?_
            have hpath := (reachOutside_firstReturn ((R j).data.rot * swap p q)
              ({p, q}ᶜ : Set (R j).Dart) ⟨(T j).attachDart (R j), by
                rw [← hattach0, hφ0]; exact hS0 _⟩).tail (firstReturn _ _ _).2
                (by rwa [hw])
            rw [hw] at hpath
            refine ReachOutside.map (fun z => (.inr ⟨j, z⟩ : H ⊕ Σ j, (R j).Dart)) hf hpath ?_
            rintro u (rfl | hu)
            · exact (hπ _ fun h => hwS (by rwa [h])).symm
            · exact (hπ u fun h => hu (by rwa [h])).symm
        · rw [hφj j h, (θ j h).map_rot, (T j).attachDart_iso (θ j h)]
          exact ReachOutside.of_eq e1
      · push Not at hd
        rw [substRot_inl_of_forall_ne hinj hd, hΨl, hΨl]
        refine ReachOutside.of_eq ?_
        rw [Perm.mul_apply, hswl, substRot_inl_of_forall_ne hinj hd]
    · by_cases hy : y = (T j).attachDart (R' j)
      · subst hy
        rw [substRot_inr_attachDart hinj, hΨl, hΨr]
        have ha : φ j ((T j).attachDart (R' j)) = (T j).attachDart (R j) := (hattach j _).2 rfl
        refine ReachOutside.of_eq ?_
        rw [ha, Perm.mul_apply]
        by_cases h : j = j₀
        · subst h
          rw [hswfix _ (by
            intro u hu
            simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hu
            subst hu
            exact ⟨hpa.symm, hqa.symm⟩), substRot_inr_attachDart hinj]
        · rw [hswj j h, substRot_inr_attachDart hinj]
      · rw [substRot_inr_of_ne hinj hy, hΨr, hΨr]
        have hy' : φ j y ≠ (T j).attachDart (R j) := fun h => hy ((hattach j y).1 h)
        by_cases h : j = j₀
        · subst h
          rw [hφ0, hφ0, θ₀.map_rot]
          change ReachOutside _ _ _ (Sum.inr ⟨j, ((firstReturn ((R j).data.rot * swap p q) _ _ :
            ({p, q}ᶜ : Set (R j).Dart)) : (R j).Dart)⟩ : H ⊕ Σ j, (R j).Dart)
          refine ReachOutside.map (fun z => (.inr ⟨j, z⟩ : H ⊕ Σ j, (R j).Dart)) hf
            (reachOutside_firstReturn _ _ _) ?_
          rintro u (rfl | hu)
          · exact (hπ _ (by rwa [← hφ0])).symm
          · exact (hπ u fun h' => hu (by rwa [h'])).symm
        · rw [hφj j h, hφj j h, (θ j h).map_rot]
          refine ReachOutside.of_eq ?_
          rw [Perm.mul_apply, hswj j h, substRot_inr_of_ne hinj (by rwa [← hφj j h])]
  have hstepInv : ∀ x', ReachOutside (substInv G R * sw) Tc (Ψ x') (Ψ (substInv G R' x')) := by
    rintro (d | ⟨j, y⟩)
    · refine ReachOutside.of_eq ?_
      change (substInv G R * sw) (.inl d) = .inl (G.inv d)
      rw [Perm.mul_apply, hswl]
      rfl
    · by_cases h : j = j₀
      · subst h
        rw [substInv_inr, hΨr, hΨr]
        simp only
        rw [hφ0, hφ0, θ₀.map_inv]
        change ReachOutside _ _ _ (Sum.inr ⟨j, ((firstReturn ((R j).data.inv * swap p q) _ _ :
          ({p, q}ᶜ : Set (R j).Dart)) : (R j).Dart)⟩ : H ⊕ Σ j, (R j).Dart)
        exact ReachOutside.map (fun z => (.inr ⟨j, z⟩ : H ⊕ Σ j, (R j).Dart)) hf
          (reachOutside_firstReturn _ _ _) fun u _ => (hπi u).symm
      · rw [substInv_inr, hΨr, hΨr]
        simp only
        rw [hφj j h, hφj j h, (θ j h).map_inv]
        refine ReachOutside.of_eq ?_
        rw [Perm.mul_apply, hswj j h]
        rfl
  -- the bijection of darts
  have hΨS : ∀ x' : substDarts T R', Ψ x' ∈ Tc := fun x' => (hmem x').2 x'.2
  let e : substDarts T R' ≃ ({P, Q}ᶜ : Set (substDarts T R)) :=
    Equiv.ofBijective (fun x' => ⟨⟨Ψ x', (hΨS x').1⟩, ((hTc _).1 (hΨS x')).2⟩)
      ⟨fun x y h => Subtype.ext (hΨinj (congrArg (fun z : ({P, Q}ᶜ : Set (substDarts T R)) =>
          ((z : substDarts T R) : H ⊕ Σ j, (R j).Dart)) h)),
        fun z => by
          obtain ⟨x', hx'⟩ := hsurj _ ((hTc _).2 ⟨_, z.2⟩)
          refine ⟨⟨x', (hmem x').1 (hx' ▸ (hTc _).2 ⟨_, z.2⟩)⟩, ?_⟩
          exact Subtype.ext (Subtype.ext hx')⟩
  have he : ∀ x', (((e x' : substDarts T R)) : H ⊕ Σ j, (R j).Dart) = Ψ x' := fun _ => rfl
  refine ⟨isoOfMapLeg e (fun x' => Subtype.ext (Subtype.ext ?_)) (fun x' => Subtype.ext
    (Subtype.ext ?_)) (fun x' => ?_) (fun x' hx' => ?_) (fun i => Subtype.ext (Subtype.ext ?_))⟩
  · rw [he, hcutInv]
    exact (coe_firstReturn_of_simulation Ψ hmem hstepInv x').symm
  · rw [he, hcutRot]
    exact (coe_firstReturn_of_simulation Ψ hmem hstepRot x').symm
  · refine Finset.mem_subtype.trans ?_
    rw [mem_familySubstitution_bdry, mem_familySubstitution_bdry, he]
    rcases x' with ⟨d | ⟨j, y⟩, hx⟩
    · simp [hΨl]
    · simp [hΨr]
  · change (G.familySubstitution T R hG).colour (e x') = _
    rw [familySubstitution_colour, familySubstitution_colour, he]
    rcases x' with ⟨d | ⟨j, y⟩, hx⟩
    · rfl
    · have hint := not_isBoundaryVertex_of_familySubstitution hG hdisj (R := R') rfl hx'
      change (R j).data.colour (φ j y) = (R' j).data.colour y
      by_cases h : j = j₀
      · subst h
        rw [hφ0]
        exact θ₀.map_colour y hint
      · rw [hφj j h]
        exact (θ j h).map_colour y hint
  · change Ψ ((G.familySubstitution T R' hG).leg i) = ((G.familySubstitution T R hG).leg i : _)
    by_cases hi : ∃ j, G.leg i ∈ (T j).darts
    · obtain ⟨j, hi⟩ := hi
      rw [coe_familySubstitution_leg_of_mem hG hdisj hi,
        coe_familySubstitution_leg_of_mem hG hdisj hi, hΨr]
      by_cases h : j = j₀
      · subst h
        rw [hφ0]
        have hl := Iso.map_leg (R' j).isPlabicGraph hC θ₀ 0
        exact congrArg (fun z => (Sum.inr ⟨j, z⟩ : H ⊕ Σ j, (R j).Dart)) (congrArg Subtype.val hl)
      · rw [hφj j h, Iso.map_leg (R' j).isPlabicGraph (R j).isPlabicGraph]
    · push Not at hi
      rw [coe_familySubstitution_leg_of_notMem hG hi, coe_familySubstitution_leg_of_notMem hG hi]
      rfl

end Lift

/-! ### Vertices of the substitution at the darts of a filling -/

section SubstitutionVertices

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : ι → G.RootedTree} (hG : G.IsPlabicGraph)
  (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts) {R : ι → PlabicGraph 1}

include hdisj

omit hdisj in
/-- Two darts lying at one vertex of the substitution lie in one orbit of the glued rotation. -/
theorem sameCycle_substRot_of_mem_vertexOf {x z : substDarts T R}
    (h : z ∈ (G.familySubstitution T R hG).vertexOf x) :
    (substRot T R).SameCycle (x : H ⊕ Σ j, (R j).Dart) z :=
  (sameCycle_firstReturnPerm_iff (substRot T R) (substDarts T R)).1
    ((RotationSystem.mem_vertexOf _).1 h)

omit [DecidableEq ι] in
/-- The orbit of the glued rotation through a dart of a filling whose vertex does not contain the
attaching dart is the vertex of that dart in the filling. -/
theorem substRot_orbit_of_not_sameCycle {j : ι} {u : (R j).Dart}
    (hu : ¬(R j).data.rot.SameCycle u ((T j).attachDart (R j))) {z : H ⊕ Σ j, (R j).Dart}
    (h : (substRot T R).SameCycle (.inr ⟨j, u⟩) z) :
    ∃ w, z = .inr ⟨j, w⟩ ∧ (R j).data.rot.SameCycle u w := by
  classical
  have hinj := intervalEnd_injective hdisj
  refine SameCycle.of_invariant (π := substRot T R)
    (fun z => ∃ w, z = .inr ⟨j, w⟩ ∧ (R j).data.rot.SameCycle u w) ?_ ⟨u, rfl, .refl _ _⟩ h
  rintro _ ⟨w, rfl, hw⟩
  have hwa : w ≠ (T j).attachDart (R j) := by
    rintro rfl; exact hu hw
  exact ⟨_, substRot_inr_of_ne hinj hwa, hw.trans (Perm.SameCycle.refl _ _ |>.trans
    (Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)))⟩

omit [DecidableEq ι] in
/-- The orbit of the glued rotation through the attaching dart of `R j` meets the darts of `G`
only at the root of `T j`, and the darts of the fillings only in the orbits of their attaching
darts at trees with the same root. -/
theorem substRot_orbit_of_sameCycle {j : ι} {u : (R j).Dart}
    (hu : (R j).data.rot.SameCycle ((T j).attachDart (R j)) u) {z : H ⊕ Σ j, (R j).Dart}
    (h : (substRot T R).SameCycle (.inr ⟨j, u⟩) z) :
    Sum.elim (fun e => G.vertexOf e = (T j).root)
      (fun w => (T w.1).root = (T j).root ∧
        (R w.1).data.rot.SameCycle ((T w.1).attachDart (R w.1)) w.2) z := by
  classical
  have hinj := intervalEnd_injective hdisj
  refine SameCycle.of_invariant (π := substRot T R) (x := .inr ⟨j, u⟩)
    (Sum.elim (fun e => G.vertexOf e = (T j).root)
      (fun w => (T w.1).root = (T j).root ∧
        (R w.1).data.rot.SameCycle ((T w.1).attachDart (R w.1)) w.2)) ?_ ⟨rfl, hu⟩ h
  rintro (e | ⟨j', w⟩) hz
  · simp only [Sum.elim_inl] at hz
    by_cases he : ∃ j', (T j').intervalEnd = e
    · obtain ⟨j', rfl⟩ := he
      rw [substRot_inl_intervalEnd hinj]
      refine ⟨?_, Perm.sameCycle_apply_right.2 (.refl _ _)⟩
      rw [← hz]
      exact ((T j').mem_root_iff.1 (T j').intervalEnd_mem_root).symm
    · push Not at he
      rw [substRot_inl_of_forall_ne hinj he]
      simpa using hz
  · obtain ⟨hroot, hw⟩ := hz
    by_cases hwa : w = (T j').attachDart (R j')
    · subst hwa
      rw [substRot_inr_attachDart hinj]
      change G.vertexOf (G.rot _) = _
      rw [G.vertexOf_rot, (T j').mem_root_iff.1 (T j').intervalEnd_mem_root, hroot]
    · rw [substRot_inr_of_ne hinj hwa]
      exact ⟨hroot, hw.trans (Perm.sameCycle_apply_right.2 (.refl _ _))⟩

/-- A surviving dart of a filling at an internal vertex of the filling lies at an internal vertex
of the substitution. -/
theorem not_isBoundaryVertex_familySubstitution_of_inr {x : substDarts T R} {j : ι}
    {u : (R j).Dart} (hx : (x : H ⊕ Σ j, (R j).Dart) = .inr ⟨j, u⟩)
    (hu : ¬(R j).data.IsBoundaryVertex ((R j).data.vertexOf u)) :
    ¬(G.familySubstitution T R hG).IsBoundaryVertex
      ((G.familySubstitution T R hG).vertexOf x) := by
  rintro ⟨z, hz, hzB⟩
  have hs := sameCycle_substRot_of_mem_vertexOf hG hz
  rw [hx] at hs
  obtain ⟨d, hdB, hzd⟩ := (mem_familySubstitution_bdry hG).1 hzB
  rw [hzd] at hs
  by_cases hc : (R j).data.rot.SameCycle ((T j).attachDart (R j)) u
  · have h := substRot_orbit_of_sameCycle hdisj hc hs
    simp only [Sum.elim_inl] at h
    have hb : G.IsBoundaryVertex (T j).root := ⟨d, h ▸ G.self_mem_vertexOf d, hdB⟩
    apply hu
    have hatt : (T j).attachDart (R j) = (R j).data.leg 0 := by
      rw [RootedTree.attachDart, if_pos hb]
    rw [← (R j).data.vertexOf_eq_vertexOf_iff.2 hc, hatt]
    exact (R j).data.vertexOf_mem_boundaryVertices.1 ((R j).isPlabicGraph.bvertex_mem 0)
  · obtain ⟨w, hw, -⟩ := substRot_orbit_of_not_sameCycle hdisj (fun h => hc h.symm) hs
    simp at hw

/-- Surviving darts at distinct vertices of one filling lie at distinct vertices of the
substitution. -/
theorem vertexOf_familySubstitution_ne_of_inr {x x' : substDarts T R} {j : ι}
    {u u' : (R j).Dart} (hx : (x : H ⊕ Σ j, (R j).Dart) = .inr ⟨j, u⟩)
    (hx' : (x' : H ⊕ Σ j, (R j).Dart) = .inr ⟨j, u'⟩)
    (hne : (R j).data.vertexOf u ≠ (R j).data.vertexOf u') :
    (G.familySubstitution T R hG).vertexOf x ≠ (G.familySubstitution T R hG).vertexOf x' := by
  intro h
  have hmem : x' ∈ (G.familySubstitution T R hG).vertexOf x := by
    rw [h]; exact (G.familySubstitution T R hG).self_mem_vertexOf x'
  have hs := sameCycle_substRot_of_mem_vertexOf hG hmem
  rw [hx, hx'] at hs
  by_cases hc : (R j).data.rot.SameCycle ((T j).attachDart (R j)) u
  · have h' := substRot_orbit_of_sameCycle hdisj hc hs
    simp only [Sum.elim_inr] at h'
    exact hne ((R j).data.vertexOf_eq_vertexOf_iff.2 (hc.symm.trans h'.2))
  · obtain ⟨w, hw, hsw⟩ := substRot_orbit_of_not_sameCycle hdisj (fun h => hc h.symm) hs
    simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hw
    subst hw
    exact hne ((R j).data.vertexOf_eq_vertexOf_iff.2 hsw)

end SubstitutionVertices

/-! ### Reduction steps of fillings -/

/-- The vertex of a dart `x` with `σ (σ x) = x ≠ σ x` is `{x, σ x}`. -/
private theorem mem_vertexOf_of_rot_rot {Y : Type*} [Fintype Y] [DecidableEq Y] {b' : ℕ}
    {Q : PlabicData Y b'} {x z : Y} (h : Q.rot (Q.rot x) = x) (hz : z ∈ Q.vertexOf x) :
    z = x ∨ z = Q.rot x :=
  SameCycle.of_invariant (π := Q.rot) (fun z => z = x ∨ z = Q.rot x)
    (by rintro _ (rfl | rfl) <;> simp [h]) (Or.inl rfl) ((RotationSystem.mem_vertexOf _).1 hz)

section Step

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : ι → G.RootedTree} (hG : G.IsPlabicGraph)
  (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts)

include hdisj

/-- **A reduction step of a filling is a local move of the substitution**, for a family of trees.
If `R' j₀` is obtained from `R j₀` by an `ε`-reduction step (`ε = 0` for a boundary root and `1`
for an internal root), `R' j ≅ R j` for the other indices, and the substitution of the `R j` is a
plabic graph, then the substitution of the `R' j` is a plabic graph obtained from it by a local
move of type (M2) or (M3). -/
theorem familySubstitution_reductionStep {R R' : ι → PlabicGraph 1} (j₀ : ι)
    (hstep : PlabicGraph.IsReductionStep (if G.IsBoundaryVertex (T j₀).root then 0 else 1)
      (R j₀) (R' j₀))
    (hother : ∀ j, j ≠ j₀ → (R' j).data.Isomorphic (R j).data)
    (hS : (G.familySubstitution T R hG).IsPlabicGraph) :
    ∃ hS' : (G.familySubstitution T R' hG).IsPlabicGraph,
      PlabicGraph.IsReductionStep (if G.IsBoundaryVertex (T j₀).root then 0 else 1)
        ⟨_, _, hS⟩ ⟨_, _, hS'⟩ := by
  have hinj := intervalEnd_injective hdisj
  have hR := (R j₀).isPlabicGraph
  have hinvR := hR.inv_involutive
  let θ : ∀ j, j ≠ j₀ → (R' j).data.Iso (R j).data := fun j h => Classical.choice (hother j h)
  set S := G.familySubstitution T R hG with hSdef
  -- the leg of `R j₀` lies at its boundary vertex
  have hlegB : (R j₀).data.IsBoundaryVertex ((R j₀).data.vertexOf ((R j₀).data.leg 0)) :=
    (R j₀).data.vertexOf_mem_boundaryVertices.1 (hR.bvertex_mem 0)
  -- a dart at an internal vertex survives, unless it is `ḡ` for an internal root
  have hlive : ∀ y, ¬(R j₀).data.IsBoundaryVertex ((R j₀).data.vertexOf y) →
      (¬G.IsBoundaryVertex (T j₀).root → y ≠ (R j₀).data.inv ((R j₀).data.leg 0)) →
      ¬(T j₀).IsCutDart (R j₀) y ∧ y ≠ (T j₀).attachDart (R j₀) := by
    intro y hy hg
    have hyleg : y ≠ (R j₀).data.leg 0 := by rintro rfl; exact hy hlegB
    refine ⟨?_, ?_⟩
    · rintro (hB | ⟨hb, h | h⟩)
      · exact hy ((R j₀).data.isBoundaryVertex_vertexOf_of_mem hB)
      · exact hyleg h
      · exact hg hb h
    · unfold RootedTree.attachDart
      split_ifs with hb
      · exact hyleg
      · exact hg hb
  -- the legs of the substitution
  have hlegS : ∀ (y : (R j₀).Dart), ¬(R j₀).data.IsBoundaryVertex ((R j₀).data.vertexOf y) →
      ∀ (Px : substDarts T R), (Px : H ⊕ Σ j, (R j).Dart) = .inr ⟨j₀, y⟩ → ∀ i, S.leg i ≠ Px := by
    intro y hy Px hPx i h
    have hl := congrArg Subtype.val h
    rw [hPx] at hl
    by_cases hi : ∃ j, G.leg i ∈ (T j).darts
    · obtain ⟨j, hi⟩ := hi
      rw [hSdef, coe_familySubstitution_leg_of_mem hG hdisj hi] at hl
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at hl
      obtain ⟨rfl, hl⟩ := hl
      exact hy (eq_of_heq hl ▸ hlegB)
    · push Not at hi
      rw [hSdef, coe_familySubstitution_leg_of_notMem hG hi] at hl
      simp at hl
  have hlegS' : ∀ i, (G.familySubstitution T R' hG).leg i ∉
      (G.familySubstitution T R' hG).bdry := familySubstitution_legs_notMem hG hdisj R'
  rcases hstep with ⟨d, hd, hside, ⟨θ₀'⟩⟩ | ⟨d, he, ⟨θ₀'⟩⟩
  · -- removal of a bivalent vertex `{d, σ d}`
    have hgside : ¬G.IsBoundaryVertex (T j₀).root → ∀ y ∈ (R j₀).data.vertexOf d,
        y ≠ (R j₀).data.inv ((R j₀).data.leg 0) := by
      intro hb y hy h
      exact hside (by rw [if_neg hb]) 0 (h ▸ hy)
    have hd' : ¬(R j₀).data.IsBoundaryVertex ((R j₀).data.vertexOf ((R j₀).data.rot d)) := by
      rw [(R j₀).data.vertexOf_rot]; exact hd.not_isBoundaryVertex
    obtain ⟨hp, hpa⟩ := hlive d hd.not_isBoundaryVertex fun hb => hgside hb d
      ((R j₀).data.self_mem_vertexOf d)
    obtain ⟨hq, hqa⟩ := hlive _ hd' fun hb => hgside hb _ ((R j₀).data.rot_mem_vertexOf d)
    have hC : (cutData (R j₀).data d ((R j₀).data.rot d) (hd.leg_mem hR)).IsPlabicGraph := by
      rw [← bivalentRemoval_eq_cutData hR hd]
      exact isPlabicGraph_bivalentRemoval hR hd
    have θ₀ : (R' j₀).data.Iso (cutGraph j₀ (hd.leg_mem hR) hC).data := by
      change (R' j₀).data.Iso (cutData (R j₀).data d ((R j₀).data.rot d) (hd.leg_mem hR))
      rw [← bivalentRemoval_eq_cutData hR hd]
      exact θ₀'
    set P : substDarts T R := ⟨.inr ⟨j₀, d⟩, hp⟩ with hPdef
    have hrotP : ((S.rot P : substDarts T R) : H ⊕ Σ j, (R j).Dart) =
        .inr ⟨j₀, (R j₀).data.rot d⟩ := by
      rw [hSdef, coe_familySubstitution_rot,
        coe_firstReturn_of_apply_mem (by rwa [substRot_inr_of_ne hinj hpa]),
        substRot_inr_of_ne hinj hpa]
    have hrotrot : S.rot (S.rot P) = P := by
      apply Subtype.ext
      have e : substRot T R ((S.rot P : substDarts T R) : H ⊕ Σ j, (R j).Dart) =
          .inr ⟨j₀, d⟩ := by
        rw [hrotP, substRot_inr_of_ne hinj hqa]
        simp [hd.rot_rot]
      change (firstReturn (substRot T R) (substDarts T R) (S.rot P) : H ⊕ Σ j, (R j).Dart) = _
      rw [coe_firstReturn_of_apply_mem (by rwa [e]), e]
    have hPrem : S.IsBivalentRemovable P := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨z, hz, hzB⟩
        obtain ⟨e', -, he'⟩ := (mem_familySubstitution_bdry hG).1 hzB
        rcases mem_vertexOf_of_rot_rot hrotrot hz with rfl | rfl
        · simp [hPdef] at he'
        · rw [hrotP] at he'; simp at he'
      · have hne : S.rot P ≠ P := fun h => by
          have := congrArg Subtype.val h
          rw [hrotP] at this
          simp only [hPdef, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
          exact hd.rot_ne this
        have hsub : S.vertexOf P = {P, S.rot P} := by
          ext z
          simp only [mem_insert, mem_singleton]
          refine ⟨mem_vertexOf_of_rot_rot hrotrot, ?_⟩
          rintro (rfl | rfl)
          · exact S.self_mem_vertexOf _
          · exact S.rot_mem_vertexOf _
        rw [hsub, card_pair hne.symm]
      · intro h
        have := congrArg Subtype.val h
        rw [hrotP, hSdef, coe_familySubstitution_inv] at this
        simp only [hPdef, substInv_inr, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq,
          true_and] at this
        exact hd.inv_ne_rot this
    have hiso := familySubstitution_isomorphic_cutData hG hdisj (R' := R') j₀ hp hq hpa hqa
      (hd.leg_mem hR) hC θ₀ θ P (S.rot P) rfl hrotP (hPrem.leg_mem hS)
    rw [← bivalentRemoval_eq_cutData hS hPrem] at hiso
    obtain ⟨θ'⟩ := hiso
    have hS' := θ'.symm.isPlabicGraph (isPlabicGraph_bivalentRemoval hS hPrem) hlegS'
    refine ⟨hS', Or.inl ⟨P, hPrem, fun hε i hi => ?_, ⟨θ'⟩⟩⟩
    have hb : ¬G.IsBoundaryVertex (T j₀).root := by
      intro hb
      rw [if_pos hb] at hε
      exact absurd hε (by decide)
    have hne : ∀ y, ((S.inv (S.leg i) : substDarts T R) : H ⊕ Σ j, (R j).Dart) ≠
        .inr ⟨j₀, y⟩ := by
      intro y h'
      change ((G.familySubstitution T R hG).inv ((G.familySubstitution T R hG).leg i) :
        H ⊕ Σ j, (R j).Dart) = _ at h'
      rw [coe_familySubstitution_inv] at h'
      by_cases hl : ∃ j, G.leg i ∈ (T j).darts
      · obtain ⟨j, hl⟩ := hl
        rw [coe_familySubstitution_leg_of_mem hG hdisj hl, substInv_inr] at h'
        have hjb : G.IsBoundaryVertex (T j).root := by
          rw [(T j).root_eq_bvertex_of_leg_mem hG hl]
          exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
        simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h'
        obtain ⟨rfl, -⟩ := h'
        exact hb hjb
      · push Not at hl
        rw [coe_familySubstitution_leg_of_notMem hG hl, substInv_inl] at h'
        simp at h'
    rcases mem_vertexOf_of_rot_rot hrotrot hi with h | h
    · exact hne d (congrArg Subtype.val h)
    · exact hne _ ((congrArg Subtype.val h).trans hrotP)
  · -- contraction of an edge `{d, d̄}`
    have hdi : ¬(R j₀).data.IsBoundaryVertex ((R j₀).data.vertexOf d) := he.not_isBoundaryVertex
    have hdi' : ¬(R j₀).data.IsBoundaryVertex ((R j₀).data.vertexOf ((R j₀).data.inv d)) :=
      he.not_isBoundaryVertex_inv
    obtain ⟨hp, hpa⟩ := hlive d hdi fun _ h => hdi' (by
      rw [h, hinvR]; exact hlegB)
    obtain ⟨hq, hqa⟩ := hlive _ hdi' fun _ h => hdi (by
      rw [show d = (R j₀).data.leg 0 from hinvR.injective h]; exact hlegB)
    have hC : (cutData (R j₀).data d ((R j₀).data.inv d) (he.leg_mem hR)).IsPlabicGraph := by
      rw [← contractEdge_eq_cutData hinvR]
      exact hR.contractEdge he
    have θ₀ : (R' j₀).data.Iso (cutGraph j₀ (he.leg_mem hR) hC).data := by
      change (R' j₀).data.Iso (cutData (R j₀).data d ((R j₀).data.inv d) (he.leg_mem hR))
      rw [← contractEdge_eq_cutData hinvR]
      exact θ₀'
    set P : substDarts T R := ⟨.inr ⟨j₀, d⟩, hp⟩ with hPdef
    have hinvP : ((S.inv P : substDarts T R) : H ⊕ Σ j, (R j).Dart) =
        .inr ⟨j₀, (R j₀).data.inv d⟩ := by
      rw [hSdef, coe_familySubstitution_inv]
      rfl
    have hPcon : S.IsContractibleEdge P := by
      refine ⟨vertexOf_familySubstitution_ne_of_inr hG hdisj rfl hinvP he.vertexOf_ne,
        S.vertexOf_mem_internalVertices.2
          (not_isBoundaryVertex_familySubstitution_of_inr hG hdisj rfl hdi),
        S.vertexOf_mem_internalVertices.2
          (not_isBoundaryVertex_familySubstitution_of_inr hG hdisj hinvP hdi'), ?_⟩
      rw [hSdef, familySubstitution_colour, familySubstitution_colour, ← hSdef, hinvP]
      exact he.colour_inv
    have hiso := familySubstitution_isomorphic_cutData hG hdisj (R' := R') j₀ hp hq hpa hqa
      (he.leg_mem hR) hC θ₀ θ P (S.inv P) rfl hinvP (hPcon.leg_mem hS)
    rw [← contractEdge_eq_cutData hS.inv_involutive] at hiso
    obtain ⟨θ'⟩ := hiso
    have hS' := θ'.symm.isPlabicGraph (hS.contractEdge hPcon) hlegS'
    exact ⟨hS', Or.inr ⟨P, hPcon, ⟨θ'⟩⟩⟩

end Step

/-- A reduction step is a local move of type (M2) or (M3). -/
theorem _root_.ClusterAlgebras.PlabicGraph.IsReductionStep.isLocalMove {b' : ℕ} {ε : Fin 2}
    {Q Q' : PlabicGraph b'} (h : PlabicGraph.IsReductionStep ε Q Q') :
    PlabicGraph.IsLocalMove .m2 Q Q' ∨ PlabicGraph.IsLocalMove .m3 Q Q' := by
  rcases h with ⟨d, hd, -, hiso⟩ | ⟨d, h⟩
  · exact Or.inl (Or.inl ⟨d, hd, hiso⟩)
  · exact Or.inr (Or.inl ⟨d, h⟩)

/-- **A reduction step of the filling is a local move of the graph**. Let `G` be a plabic graph and
`T = (v, W)` a rooted tree of `G`; let `ε = 0` if `v` is a boundary vertex and `ε = 1` if `v` is
internal. Let `R` and `R'` be `T`-fillings such that `R'` is obtained from `R` by an `ε`-reduction
step and `G[R]` is a plabic graph. Then `G[R']` is a plabic graph obtained from `G[R]` by a local
move of type (M2) or (M3). (The colour conditions on the fillings are not needed.) -/
@[cluster_algebras "lem_tree_substitution_step"]
theorem RootedTree.substitution_reductionStep (hG : G.IsPlabicGraph) (T : G.RootedTree)
    {R R' : PlabicGraph 1}
    (hstep : PlabicGraph.IsReductionStep (if G.IsBoundaryVertex T.root then 0 else 1) R R')
    (hS : (T.substitution hG R).IsPlabicGraph) :
    ∃ hS' : (T.substitution hG R').IsPlabicGraph,
      PlabicGraph.IsLocalMove .m2 ⟨_, _, hS⟩ ⟨_, _, hS'⟩ ∨
        PlabicGraph.IsLocalMove .m3 ⟨_, _, hS⟩ ⟨_, _, hS'⟩ :=
  let ⟨hS', h⟩ := familySubstitution_reductionStep hG (T := fun _ : Unit => T)
    (fun _ _ h => (h rfl).elim) (R := fun _ => R) (R' := fun _ => R') () hstep
    (fun _ h => (h rfl).elim) hS
  ⟨hS', h.isLocalMove⟩

/-! ### Lollipops and reductions of plabic trees -/

section Lollipop

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

-- Note: Reduced.lean has a private unprimed copy; the prime avoids the clash.
/-- In a plabic graph with one boundary vertex, the dart across the leg lies at an internal
vertex. -/
theorem not_isBoundaryVertex_inv_leg' {X : PlabicData Y 1} (hX : X.IsPlabicGraph) :
    ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.leg 0))) := by
  intro hB
  obtain ⟨i, hi⟩ := hX.exists_bvertex_eq _ (X.vertexOf_mem_boundaryVertices.2 hB)
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hmem : X.inv (X.leg 0) ∈ (X.bvertex 0).filter (· ∉ X.bdry) := by
    rw [mem_filter, hi]
    exact ⟨X.self_mem_vertexOf _, fun h => hX.leg_notMem_bdry 0 (hX.inv_mem_bdry_iff.1 h)⟩
  rw [hX.filter_bvertex_notMem_bdry, mem_singleton] at hmem
  exact hX.inv_ne _ hmem

-- Note: Reduced.lean has a private unprimed copy.
/-- A plabic graph with one boundary vertex in which the dart across the leg forms a vertex by
itself, of colour `c`, is isomorphic to the lollipop graph `L_c`. -/
private theorem lollipopGraph_isomorphic' {X : PlabicData Y 1} (hX : X.IsPlabicGraph) {c : Shade}
    (h₁ : (X.vertexOf (X.inv (X.leg 0))).card = 1) (hc : X.colour (X.inv (X.leg 0)) = c) :
    (lollipopGraph c).Isomorphic X := by
  have hinv := hX.inv_involutive
  have hdeg := hX.boundaryVertex_card
  have hv₀ : X.IsBoundaryVertex (X.vertexOf (X.leg 0)) :=
    X.vertexOf_mem_boundaryVertices.1 (hX.bvertex_mem 0)
  obtain ⟨ex, hex, hex₀, hiex₀⟩ := hX.exists_exterior 0
  rw [show finRotate 1 0 = 0 from Subsingleton.elim _ _] at hex₀
  have hexB := X.exterior_subset_bdry hex
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
  have e₁ : X.rot ex = X.leg 0 := notB_eq _ (hrot_mem _ hex₀) (X.mem_exterior.1 hex).2
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
  let f : LollipopDart → Y
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
  refine ⟨isoOfMapLeg (Equiv.ofBijective f ⟨hf, fun y => hsurj y (hX.reach ex y)⟩)
    (fun d => ?_) (fun d => ?_) (fun d => ?_) (fun d hd => ?_) fun i => ?_⟩
  · cases d
    exacts [rfl, (hinv ex).symm, rfl, (hinv _).symm]
  · cases d
    · exact (congrArg f r₁).trans e₁.symm
    · exact (congrArg f r₂).trans e₃.symm
    · exact (congrArg f r₃).trans e₂.symm
    · exact (congrArg f r₄).trans e₄.symm
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

end Lollipop

section Reductions

open PlabicGraph

-- Note: Reduced.lean has a private unprimed copy.
/-- A `1`-reduction step keeps the colour of the dart across the leg. -/
private theorem colour_inv_leg_eq_of_isReductionStep' {A C : PlabicGraph 1}
    (h : IsReductionStep 1 A C) :
    C.data.colour (C.data.inv (C.data.leg 0)) = A.data.colour (A.data.inv (A.data.leg 0)) := by
  have hx := not_isBoundaryVertex_inv_leg' C.isPlabicGraph
  have hA := A.isPlabicGraph
  have hinv := hA.inv_involutive
  rcases h with ⟨d, hd, hside, ⟨θ⟩⟩ | ⟨d, he, ⟨θ⟩⟩
  · have hs := hside rfl 0
    have h₁ : A.data.leg 0 ≠ A.data.inv d := fun h =>
      hs (by rw [h, hinv]; exact A.data.self_mem_vertexOf d)
    have h₂ : A.data.leg 0 ≠ A.data.inv (A.data.rot d) := fun h =>
      hs (by rw [h, hinv]; exact A.data.rot_mem_vertexOf d)
    rw [← θ.map_colour _ hx, θ.map_inv,
      Iso.map_leg C.isPlabicGraph (isPlabicGraph_bivalentRemoval hA hd) θ, bivalentRemoval_colour,
      coe_bivalentRemoval_inv_of_ne (y := (A.data.bivalentRemoval hA hd).leg 0) hA hd h₁ h₂]
    rfl
  · rw [← θ.map_colour _ hx, θ.map_inv, Iso.map_leg C.isPlabicGraph (hA.contractEdge he) θ,
      contractEdge_colour, coe_contractEdge_inv hinv]
    rfl

/-- A plabic graph has a maximal sequence of `ε`-reduction steps: each step deletes two darts. -/
theorem exists_reflTransGen_isIrreducible {b' : ℕ} (ε : Fin 2) (Q : PlabicGraph b') :
    ∃ Q', Relation.ReflTransGen (IsReductionStep ε) Q Q' ∧ IsIrreducible ε Q' := by
  induction h : Fintype.card Q.Dart using Nat.strong_induction_on generalizing Q with
  | _ n ih =>
    by_cases hirr : IsIrreducible ε Q
    · exact ⟨Q, .refl, hirr⟩
    · unfold PlabicGraph.IsIrreducible at hirr
      push Not at hirr
      obtain ⟨Q₁, hQ₁⟩ := hirr
      have hlt : Fintype.card Q₁.Dart < n := by
        rw [← h]
        rcases hQ₁ with ⟨d, hd, -, ⟨θ⟩⟩ | ⟨d, he, ⟨θ⟩⟩ <;>
        · rw [Fintype.card_congr θ.toEquiv]
          exact Fintype.card_subtype_lt (x := d) (by simp)
      obtain ⟨Q', h₁, h₂⟩ := ih _ hlt Q₁ rfl
      exact ⟨Q', Relation.ReflTransGen.head hQ₁ h₁, h₂⟩

end Reductions

/-! ### Reducing all the fillings -/

section Chain

open PlabicGraph

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : ι → G.RootedTree} (hG : G.IsPlabicGraph)
  (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts)

include hdisj

/-- Equal plabic graphs are isomorphic. -/
private def isoOfEq {b' : ℕ} {A B : PlabicGraph b'} (h : A = B) : A.data.Iso B.data := by
  subst h
  exact Iso.refl _

/-- Pointwise isomorphic fillings give isomorphic substitutions. -/
private theorem familySubstitution_isomorphic_of_iso {R R' : ι → PlabicGraph 1}
    (θ : ∀ j, (R j).data.Iso (R' j).data) (hS : (G.familySubstitution T R hG).IsPlabicGraph) :
    ∃ hS' : (G.familySubstitution T R' hG).IsPlabicGraph,
      (PlabicGraph.mk _ _ hS).Isomorphic ⟨_, _, hS'⟩ := by
  obtain ⟨θ'⟩ := familySubstitution_isomorphic hG hdisj θ
  exact ⟨θ'.isPlabicGraph hS (familySubstitution_legs_notMem hG hdisj R'), ⟨θ'⟩⟩

/-- Pointwise isomorphic fillings give move-equivalent substitutions. -/
private theorem familySubstitution_moveEquivalent_of_iso {R R' : ι → PlabicGraph 1}
    (θ : ∀ j, (R j).data.Iso (R' j).data) (hS : (G.familySubstitution T R hG).IsPlabicGraph) :
    ∃ hS' : (G.familySubstitution T R' hG).IsPlabicGraph,
      MoveEquivalent {.m2, .m3} ⟨_, _, hS⟩ ⟨_, _, hS'⟩ := by
  obtain ⟨θ'⟩ := familySubstitution_isomorphic hG hdisj θ
  exact ⟨θ'.isPlabicGraph hS (familySubstitution_legs_notMem hG hdisj R'),
    MoveEquivalent.of_isomorphic ⟨θ'.symm⟩⟩

/-- **Reducing the fillings is a sequence of moves (M2), (M3) of the substitution.** If each `R j`
is obtained from `P j` by a sequence of `ε`-reduction steps (`ε = 0` for a boundary root and `1`
for an internal root), and the substitution of the `P j` is a plabic graph, then so is the
substitution of the `R j`, and the two are `{M2, M3}`-equivalent. -/
theorem familySubstitution_moveEquivalent {P R : ι → PlabicGraph 1}
    (hR : ∀ j, Relation.ReflTransGen
      (IsReductionStep (if G.IsBoundaryVertex (T j).root then 0 else 1)) (P j) (R j))
    (hP : (G.familySubstitution T P hG).IsPlabicGraph) :
    ∃ hR' : (G.familySubstitution T R hG).IsPlabicGraph,
      MoveEquivalent {.m2, .m3} ⟨_, _, hP⟩ ⟨_, _, hR'⟩ := by
  classical
  let F : Finset ι → ι → PlabicGraph 1 := fun s j => if j ∈ s then R j else P j
  have key : ∀ s : Finset ι, ∃ hS : (G.familySubstitution T (F s) hG).IsPlabicGraph,
      MoveEquivalent {.m2, .m3} ⟨_, _, hP⟩ ⟨_, _, hS⟩ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact familySubstitution_moveEquivalent_of_iso hG hdisj (R := P) (R' := F ∅)
        (fun j => isoOfEq (by simp [F])) hP
    | @insert a s ha ih =>
      obtain ⟨hS, hPS⟩ := ih
      let U : PlabicGraph 1 → ι → PlabicGraph 1 := fun Q j => if j = a then Q else F s j
      have inner : ∀ Q, Relation.ReflTransGen
          (IsReductionStep (if G.IsBoundaryVertex (T a).root then 0 else 1)) (P a) Q →
          ∃ hU : (G.familySubstitution T (U Q) hG).IsPlabicGraph,
            MoveEquivalent {.m2, .m3} ⟨_, _, hS⟩ ⟨_, _, hU⟩ := by
        intro Q hQ
        induction hQ with
        | refl =>
          exact familySubstitution_moveEquivalent_of_iso hG hdisj
            (fun j => isoOfEq (by by_cases h : j = a <;> simp [U, F, h, ha])) hS
        | @tail Q₁ Q₂ _ hstep ih =>
          obtain ⟨hU₁, h₁⟩ := ih
          have hstep' : IsReductionStep (if G.IsBoundaryVertex (T a).root then 0 else 1)
              (U Q₁ a) (U Q₂ a) := by
            simpa only [U, if_pos rfl] using hstep
          obtain ⟨hU₂, hmove⟩ := familySubstitution_reductionStep hG hdisj a hstep'
            (fun j hj => ⟨isoOfEq (by simp [U, hj])⟩) hU₁
          refine ⟨hU₂, h₁.trans (MoveEquivalent.of_moveStep (Or.inr ?_))⟩
          rcases hmove.isLocalMove with h | h
          · exact ⟨.m2, by simp, h⟩
          · exact ⟨.m3, by simp, h⟩
      obtain ⟨hU, hmove⟩ := inner (R a) (hR a)
      obtain ⟨hS', h'⟩ := familySubstitution_moveEquivalent_of_iso hG hdisj
        (R' := F (insert a s)) (fun j => isoOfEq (by by_cases h : j = a <;> simp [U, F, h])) hU
      exact ⟨hS', hPS.trans (hmove.trans h')⟩
  obtain ⟨hS, h⟩ := key Finset.univ
  obtain ⟨hR', h'⟩ := familySubstitution_moveEquivalent_of_iso hG hdisj (R' := R)
    (fun j => isoOfEq (by simp [F])) hS
  exact ⟨hR', h.trans h'⟩

/-- **Reducing the fillings of trees with internal roots is a sequence of `1`-reduction steps of
the substitution**, up to isomorphism. -/
theorem familySubstitution_reflTransGen_isReductionStep
    (hb : ∀ j, ¬G.IsBoundaryVertex (T j).root) {P R : ι → PlabicGraph 1}
    (hR : ∀ j, Relation.ReflTransGen (IsReductionStep 1) (P j) (R j))
    (hP : (G.familySubstitution T P hG).IsPlabicGraph) :
    ∃ hR' : (G.familySubstitution T R hG).IsPlabicGraph, ∃ C : PlabicGraph b,
      Relation.ReflTransGen (IsReductionStep 1) ⟨_, _, hP⟩ C ∧ C.Isomorphic ⟨_, _, hR'⟩ := by
  classical
  let F : Finset ι → ι → PlabicGraph 1 := fun s j => if j ∈ s then R j else P j
  have key : ∀ s : Finset ι, ∃ hS : (G.familySubstitution T (F s) hG).IsPlabicGraph,
      ∃ C : PlabicGraph b, Relation.ReflTransGen (IsReductionStep 1) ⟨_, _, hP⟩ C ∧
        C.Isomorphic ⟨_, _, hS⟩ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨hS, h⟩ := familySubstitution_isomorphic_of_iso hG hdisj (R := P) (R' := F ∅)
        (fun j => isoOfEq (by simp [F])) hP
      exact ⟨hS, _, .refl, h⟩
    | @insert a s ha ih =>
      obtain ⟨hS, C, hC, hCS⟩ := ih
      let U : PlabicGraph 1 → ι → PlabicGraph 1 := fun Q j => if j = a then Q else F s j
      have inner : ∀ Q, Relation.ReflTransGen (IsReductionStep 1) (P a) Q →
          ∃ hU : (G.familySubstitution T (U Q) hG).IsPlabicGraph, ∃ C' : PlabicGraph b,
            Relation.ReflTransGen (IsReductionStep 1) ⟨_, _, hP⟩ C' ∧
              C'.Isomorphic ⟨_, _, hU⟩ := by
        intro Q hQ
        induction hQ with
        | refl =>
          obtain ⟨hU, h⟩ := familySubstitution_isomorphic_of_iso hG hdisj
            (R := F s) (R' := U (P a))
            (fun j => isoOfEq (by by_cases h : j = a <;> simp [U, F, h, ha])) hS
          exact ⟨hU, C, hC, PlabicData.Isomorphic.trans _ hCS h⟩
        | @tail Q₁ Q₂ _ hstep ih =>
          obtain ⟨hU₁, C', hC', hC'U⟩ := ih
          have hstep' : IsReductionStep (if G.IsBoundaryVertex (T a).root then 0 else 1)
              (U Q₁ a) (U Q₂ a) := by
            simpa only [U, if_pos rfl, if_neg (hb a)] using hstep
          obtain ⟨hU₂, hred⟩ := familySubstitution_reductionStep hG hdisj a hstep'
            (fun j hj => ⟨isoOfEq (by simp [U, hj])⟩) hU₁
          rw [if_neg (hb a)] at hred
          exact ⟨hU₂, _, hC'.tail (IsReductionStep.of_isomorphic hC'U hred),
            PlabicData.Isomorphic.refl _⟩
      obtain ⟨hU, C', hC', hC'U⟩ := inner (R a) (hR a)
      obtain ⟨hS', h'⟩ := familySubstitution_isomorphic_of_iso hG hdisj
        (R := U (R a)) (R' := F (insert a s))
        (fun j => isoOfEq (by by_cases h : j = a <;> simp [U, F, h])) hU
      exact ⟨hS', C', hC', PlabicData.Isomorphic.trans _ hC'U h'⟩
  obtain ⟨hS, C, hC, hCS⟩ := key Finset.univ
  obtain ⟨hR', h'⟩ := familySubstitution_isomorphic_of_iso hG hdisj (R := F Finset.univ) (R' := R)
    (fun j => isoOfEq (by simp [F])) hS
  exact ⟨hR', C, hC, PlabicData.Isomorphic.trans _ hCS h'⟩

end Chain

/-! ### Maximal reductions of the plabic graph of a collapsible tree -/

section Terminal

open PlabicGraph

-- Note: Reduced.lean has a private unprimed copy.
/-- The lollipop graph is `ε`-irreducible. -/
private theorem isIrreducible_lollipopPlabicGraph' (c : Shade) (ε : Fin 2) :
    IsIrreducible ε (lollipopPlabicGraph c) := by
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

/-- A maximal sequence of `ε`-reduction steps from the plabic graph `P_T` of a collapsible tree of
colour `c` ends at a graph isomorphic to the lollipop graph `L_c`. -/
private theorem lollipop_isomorphic_of_isIrreducible (hG : G.IsPlabicGraph) {T : G.RootedTree}
    {c : Shade} (hc : T.IsCollapsibleOfColour c) {R : PlabicGraph 1}
    (hR : Relation.ReflTransGen (IsReductionStep (if G.IsBoundaryVertex T.root then 0 else 1))
      (T.toPlabicGraph hG) R)
    (hirr : IsIrreducible (if G.IsBoundaryVertex T.root then 0 else 1) R) :
    (lollipopGraph c).Isomorphic R.data := by
  have hPL : MoveEquivalent {.m2, .m3} (T.toPlabicGraph hG) (lollipopPlabicGraph c) :=
    hc.moveEquivalent
  by_cases hb : G.IsBoundaryVertex T.root
  · rw [if_pos hb] at hR hirr
    have hPR : MoveEquivalent {.m2, .m3} (T.toPlabicGraph hG) R :=
      Relation.ReflTransGen.mono (fun _ _ h => h.moveStep) hR
    have hfR : R.data.faces.card = 1 :=
      (MoveEquivalent.card_eq hPR).2.1.symm.trans (T.card_faces_plabicData hG)
    have hfL : (lollipopPlabicGraph c).data.faces.card = 1 := by
      change (lollipopGraph c).faces.card = 1
      rw [faces_lollipopGraph]
      rfl
    have θ := isomorphic_of_moveEquivalent_of_isIrreducible (Q := R) (Q' := lollipopPlabicGraph c)
      R.isPlabicGraph.card_boundaryVertices hfR
      (lollipopPlabicGraph c).isPlabicGraph.card_boundaryVertices hfL (hPR.symm.trans hPL) hirr
      (isIrreducible_lollipopPlabicGraph' c 0)
    exact PlabicData.Isomorphic.symm _ θ
  · rw [if_neg hb] at hR hirr
    have hcol : ∀ d ∈ T.root, G.colour d = c := by
      rcases hc.root_cases with h | h
      · exact h.2
      · exact absurd h.1 hb
    have hcard := (T.moveEquivalent_lollipopPlabicGraph_iff hG hb hcol hR hirr).1 hPL
    have hcolAll : ∀ R', Relation.ReflTransGen (IsReductionStep 1) (T.toPlabicGraph hG) R' →
        R'.data.colour (R'.data.inv (R'.data.leg 0)) = c := by
      intro R' h
      induction h with
      | refl =>
        change T.plabicData.colour (T.plabicData.inv T.legDart) = c
        rw [T.inv_legDart_of_not_isBoundaryVertex hG hb]
        exact hcol _ T.intervalStart_mem_root
      | tail _ hstep ih => exact (colour_inv_leg_eq_of_isReductionStep' hstep).trans ih
    exact lollipopGraph_isomorphic' R.isPlabicGraph hcard (hcolAll R hR)

end Terminal

/-! ### The collapse is the substitution of lollipops -/

/-- The trees of a collapsing family have pairwise disjoint sets of darts. -/
theorem IsCollapsingFamily.pairwise_disjoint_darts (hG : G.IsPlabicGraph)
    {𝒯 : Finset (G.RootedTree × Shade)} (h𝒯 : G.IsCollapsingFamily 𝒯) :
    Pairwise fun j j' : 𝒯 => Disjoint j.1.1.darts j'.1.1.darts := by
  intro j j' hne
  have hne' : j.1 ≠ j'.1 := fun h => hne (Subtype.ext h)
  exact j.1.1.disjoint_darts hG (h𝒯.disjoint_nonRoot _ j.2 _ j'.2 hne')
    (h𝒯.root_notMem_nonRoot _ j'.2 _ j.2 hne'.symm)

/-- The rotation of the lollipop graph sends `e` to `g`. -/
theorem lollipopGraph_rot_e (c : Shade) : (lollipopGraph c).rot .e = .g := by cases c <;> decide
/-- The rotation of the lollipop graph sends `ē` to `e`. -/
theorem lollipopGraph_rot_eBar (c : Shade) : (lollipopGraph c).rot .eBar = .e := by
  cases c <;> decide
/-- The rotation of the lollipop graph sends `g` to `ē`. -/
theorem lollipopGraph_rot_g (c : Shade) : (lollipopGraph c).rot .g = .eBar := by cases c <;> decide
/-- The rotation of the lollipop graph fixes `ḡ`. -/
theorem lollipopGraph_rot_gBar (c : Shade) : (lollipopGraph c).rot .gBar = .gBar := by
  cases c <;> decide

section CollapseIso

open PlabicGraph

variable {𝒯 : Finset (G.RootedTree × Shade)} [DecidableEq 𝒯]

/-- The darts of `G` in the substitution of lollipops: the first dart `g_i` of a tree with a
boundary root goes to the leg `g` of its lollipop; every other dart goes to itself. -/
private noncomputable def lolliMap (𝒯 : Finset (G.RootedTree × Shade)) [DecidableEq 𝒯] (d : H) :
    H ⊕ Σ j : 𝒯, (lollipopPlabicGraph j.1.2).Dart :=
  if h : ∃ j : 𝒯, d = j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root then
    .inr ⟨h.choose, LollipopDart.g⟩ else .inl d

/-- As `lolliMap`, sending moreover `ḡ_i` to the dart `ḡ` of the lollipop at `i`. -/
private noncomputable def lolliMap' (𝒯 : Finset (G.RootedTree × Shade)) [DecidableEq 𝒯] (d : H) :
    H ⊕ Σ j : 𝒯, (lollipopPlabicGraph j.1.2).Dart :=
  if h : ∃ j : 𝒯, d = G.inv j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root then
    .inr ⟨h.choose, LollipopDart.gBar⟩ else lolliMap 𝒯 d

variable (hG : G.IsPlabicGraph) (h𝒯 : G.IsCollapsingFamily 𝒯)

include hG h𝒯

private theorem lolliMap_start (j : 𝒯) (hb : G.IsBoundaryVertex j.1.1.root) :
    lolliMap 𝒯 j.1.1.intervalStart = .inr ⟨j, LollipopDart.g⟩ := by
  have hex : ∃ j' : 𝒯, j.1.1.intervalStart = j'.1.1.intervalStart ∧
      G.IsBoundaryVertex j'.1.1.root := ⟨j, rfl, hb⟩
  rw [lolliMap, dif_pos hex]
  refine congrArg Sum.inr (sigma_eq_of_eq (fun _ => LollipopDart.g) ?_)
  by_contra hne
  exact Finset.disjoint_left.1 (h𝒯.pairwise_disjoint_darts hG hne)
    ((congrArg (· ∈ (hex.choose).1.1.darts) hex.choose_spec.1).mpr
      (hex.choose).1.1.intervalStart_mem_darts)
    j.1.1.intervalStart_mem_darts

omit [DecidableEq 𝒯] hG h𝒯 in
private theorem lolliMap_of_not [DecidableEq 𝒯] {d : H}
    (h : ¬∃ j : 𝒯, d = j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root) :
    lolliMap 𝒯 d = .inl d := by
  rw [lolliMap, dif_neg h]

private theorem lolliMap'_inv_start (j : 𝒯) (hb : G.IsBoundaryVertex j.1.1.root) :
    lolliMap' 𝒯 (G.inv j.1.1.intervalStart) = .inr ⟨j, LollipopDart.gBar⟩ := by
  have hex : ∃ j' : 𝒯, G.inv j.1.1.intervalStart = G.inv j'.1.1.intervalStart ∧
      G.IsBoundaryVertex j'.1.1.root := ⟨j, rfl, hb⟩
  rw [lolliMap', dif_pos hex]
  refine congrArg Sum.inr (sigma_eq_of_eq (fun _ => LollipopDart.gBar) ?_)
  by_contra hne
  have h1 := hG.inv_involutive.injective hex.choose_spec.1
  exact Finset.disjoint_left.1 (h𝒯.pairwise_disjoint_darts hG hne)
    ((congrArg (· ∈ (hex.choose).1.1.darts) h1).mpr (hex.choose).1.1.intervalStart_mem_darts)
    j.1.1.intervalStart_mem_darts

omit [DecidableEq 𝒯] hG h𝒯 in
private theorem lolliMap'_of_not [DecidableEq 𝒯] {d : H}
    (h : ¬∃ j : 𝒯, d = G.inv j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root) :
    lolliMap' 𝒯 d = lolliMap 𝒯 d := by
  rw [lolliMap', dif_neg h]

omit [DecidableEq 𝒯] h𝒯 in
/-- The first dart of a tree with a boundary root is a leg. -/
private theorem exists_leg_eq_start (j : 𝒯) (hb : G.IsBoundaryVertex j.1.1.root) :
    ∃ i, j.1.1.root = G.bvertex i ∧ j.1.1.intervalStart = G.leg i := by
  obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _
    (G.mem_boundaryVertices.2 ⟨j.1.1.root_mem_vertices, hb⟩)
  exact ⟨i, hi.symm, j.1.1.intervalStart_eq_leg hG hi.symm⟩

end CollapseIso

private theorem lollipop_g_notMem : LollipopDart.g ∉ ({.e, .eBar} : Finset LollipopDart) := by
  decide

private theorem lollipop_gBar_notMem : LollipopDart.gBar ∉ ({.e, .eBar} : Finset LollipopDart) := by
  decide

section CollapseIso2

open PlabicGraph

variable {𝒯 : Finset (G.RootedTree × Shade)} [DecidableEq 𝒯]

/-- The trees of a family, indexed by its members. -/
private abbrev famT (𝒯 : Finset (G.RootedTree × Shade)) : 𝒯 → G.RootedTree := fun j => j.1.1

/-- The lollipop graphs of the colours of a family, indexed by its members. -/
private abbrev famL (𝒯 : Finset (G.RootedTree × Shade)) : 𝒯 → PlabicGraph 1 :=
  fun j => lollipopPlabicGraph j.1.2

omit [DecidableEq 𝒯] in
private theorem attachDart_famL_of_isBoundaryVertex {j : 𝒯} (hb : G.IsBoundaryVertex j.1.1.root) :
    (famT 𝒯 j).attachDart (famL 𝒯 j) = LollipopDart.g := by
  simp only [RootedTree.attachDart, famT, hb, if_true]
  rfl

omit [DecidableEq 𝒯] in
private theorem attachDart_famL_of_not_isBoundaryVertex {j : 𝒯}
    (hb : ¬G.IsBoundaryVertex j.1.1.root) :
    (famT 𝒯 j).attachDart (famL 𝒯 j) = LollipopDart.gBar := by
  simp only [RootedTree.attachDart, famT, hb, if_false]
  rfl

omit [DecidableEq 𝒯] in
private theorem isCutDart_famL_of_not_isBoundaryVertex {j : 𝒯}
    (hb : ¬G.IsBoundaryVertex j.1.1.root) (y : (famL 𝒯 j).Dart) :
    (famT 𝒯 j).IsCutDart (famL 𝒯 j) y := by
  change LollipopDart at y
  cases y
  · exact Or.inl (show LollipopDart.e ∈ ({.e, .eBar} : Finset LollipopDart) by decide)
  · exact Or.inl (show LollipopDart.eBar ∈ ({.e, .eBar} : Finset LollipopDart) by decide)
  · exact Or.inr ⟨hb, Or.inl rfl⟩
  · exact Or.inr ⟨hb, Or.inr rfl⟩

omit [DecidableEq 𝒯] in
private theorem isCutDart_famL_iff_of_isBoundaryVertex {j : 𝒯}
    (hb : G.IsBoundaryVertex j.1.1.root) (y : (famL 𝒯 j).Dart) :
    (famT 𝒯 j).IsCutDart (famL 𝒯 j) y ↔ y = LollipopDart.e ∨ y = LollipopDart.eBar := by
  have : ¬(¬G.IsBoundaryVertex (famT 𝒯 j).root) := not_not.2 hb
  unfold RootedTree.IsCutDart
  simp only [this, false_and, or_false]
  change LollipopDart at y
  have hB : (famL 𝒯 j).data.bdry = ({LollipopDart.e, LollipopDart.eBar} : Finset LollipopDart) :=
    rfl
  rw [hB]
  cases y
  · exact iff_of_true (Finset.mem_insert_self _ _) (Or.inl rfl)
  · exact iff_of_true (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (Or.inr rfl)
  · exact iff_of_false lollipop_g_notMem (by rintro (h | h) <;> cases h)
  · exact iff_of_false lollipop_gBar_notMem (by rintro (h | h) <;> cases h)

variable (hG : G.IsPlabicGraph) (h𝒯 : G.IsCollapsingFamily 𝒯)

include hG h𝒯

private theorem lolliMap_mem_iff (d : H) :
    lolliMap 𝒯 d ∈ substDarts (famT 𝒯) (famL 𝒯) ↔ d ∈ G.collapseCore 𝒯 := by
  by_cases hd : ∃ j : 𝒯, d = j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root
  · obtain ⟨j, rfl, hb⟩ := hd
    rw [lolliMap_start hG h𝒯 j hb, inr_mem_substDarts]
    obtain ⟨i, -, hi⟩ := exists_leg_eq_start hG j hb
    refine iff_of_true ?_ (hi ▸ G.leg_mem_collapseCore 𝒯 i)
    rw [isCutDart_famL_iff_of_isBoundaryVertex hb]
    simp
  · rw [lolliMap_of_not hd, inl_mem_substDarts]
    constructor
    · intro h
      exact Or.inl fun hD => by
        obtain ⟨p, hp, hdp⟩ := mem_familyDarts.1 hD
        exact h ⟨p, hp⟩ hdp
    · rintro (h | ⟨i, rfl⟩) j hj
      · exact h (mem_familyDarts.2 ⟨j.1, j.2, hj⟩)
      · refine hd ⟨j, j.1.1.leg_eq_intervalStart hG hj, ?_⟩
        rw [j.1.1.root_eq_bvertex_of_leg_mem hG hj]
        exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)

omit [DecidableEq 𝒯] in
/-- From the dead copy of the first dart `g_i` of a tree with a boundary root, the glued rotation
of the substitution of lollipops reaches the leg of the lollipop. -/
private theorem reachOutside_lolli_start (j : 𝒯) (hb : G.IsBoundaryVertex j.1.1.root) :
    ReachOutside (substRot (famT 𝒯) (famL 𝒯)) (substDarts (famT 𝒯) (famL 𝒯))
      (.inl j.1.1.intervalStart) (.inr ⟨j, LollipopDart.g⟩) := by
  classical
  have hinj := intervalEnd_injective (T := famT 𝒯) (h𝒯.pairwise_disjoint_darts hG)
  have hend := j.1.1.intervalEnd_eq_intervalStart hG hb
  have e1 := substRot_inl_intervalEnd (T := famT 𝒯) (R := famL 𝒯) hinj j
  simp only [famT] at e1
  rw [hend, attachDart_famL_of_isBoundaryVertex hb] at e1
  change _ = (Sum.inr ⟨j, (lollipopGraph j.1.2).rot LollipopDart.g⟩ :
    H ⊕ Σ j : 𝒯, (famL 𝒯 j).Dart) at e1
  rw [lollipopGraph_rot_g] at e1
  have e2 := substRot_inr_of_ne (T := famT 𝒯) (R := famL 𝒯) hinj (j := j)
    (y := LollipopDart.eBar) (by rw [attachDart_famL_of_isBoundaryVertex hb]; intro h; cases h)
  change _ = (Sum.inr ⟨j, (lollipopGraph j.1.2).rot LollipopDart.eBar⟩ :
    H ⊕ Σ j : 𝒯, (famL 𝒯 j).Dart) at e2
  rw [lollipopGraph_rot_eBar] at e2
  have e3 := substRot_inr_of_ne (T := famT 𝒯) (R := famL 𝒯) hinj (j := j)
    (y := LollipopDart.e) (by rw [attachDart_famL_of_isBoundaryVertex hb]; intro h; cases h)
  change _ = (Sum.inr ⟨j, (lollipopGraph j.1.2).rot LollipopDart.e⟩ :
    H ⊕ Σ j : 𝒯, (famL 𝒯 j).Dart) at e3
  rw [lollipopGraph_rot_e] at e3
  refine ReachOutside.step e1 ?_ (ReachOutside.step e2 ?_ (ReachOutside.of_eq e3))
  · exact fun h => h ((isCutDart_famL_iff_of_isBoundaryVertex hb _).2 (Or.inr rfl))
  · exact fun h => h ((isCutDart_famL_iff_of_isBoundaryVertex hb _).2 (Or.inl rfl))

/-- Each step of `σ` is followed by the glued rotation of the substitution of lollipops. -/
private theorem reachOutside_lolliMap (d : H) :
    ReachOutside (substRot (famT 𝒯) (famL 𝒯)) (substDarts (famT 𝒯) (famL 𝒯))
      (lolliMap 𝒯 d) (lolliMap 𝒯 (G.rot d)) := by
  have hdisj := h𝒯.pairwise_disjoint_darts hG
  have hinj := intervalEnd_injective (T := famT 𝒯) hdisj
  by_cases hd : ∃ j : 𝒯, d = j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root
  · obtain ⟨j, rfl, hb⟩ := hd
    rw [lolliMap_start hG h𝒯 j hb]
    obtain ⟨i, -, hleg⟩ := exists_leg_eq_start hG j hb
    have hBd : G.rot j.1.1.intervalStart ∈ G.bdry := hleg ▸ hG.rot_leg_mem_bdry' i
    have hnot : ¬∃ j' : 𝒯, G.rot j.1.1.intervalStart = j'.1.1.intervalStart ∧
        G.IsBoundaryVertex j'.1.1.root := fun ⟨j', h, _⟩ =>
      j'.1.1.notMem_bdry_of_mem_darts j'.1.1.intervalStart_mem_darts (h ▸ hBd)
    rw [lolliMap_of_not hnot]
    have e := substRot_inr_attachDart (T := famT 𝒯) (R := famL 𝒯) hinj j
    rw [attachDart_famL_of_isBoundaryVertex hb] at e
    simp only [famT] at e
    rw [j.1.1.intervalEnd_eq_intervalStart hG hb] at e
    exact ReachOutside.of_eq e
  · rw [lolliMap_of_not hd]
    by_cases hD : ∃ j : 𝒯, d ∈ j.1.1.darts
    · obtain ⟨j, hdj⟩ := hD
      by_cases hend : d = j.1.1.intervalEnd
      · have hb : ¬G.IsBoundaryVertex j.1.1.root := fun hb =>
          hd ⟨j, hend.trans (j.1.1.intervalEnd_eq_intervalStart hG hb), hb⟩
        subst hend
        have e1 := substRot_inl_intervalEnd (T := famT 𝒯) (R := famL 𝒯) hinj j
        rw [attachDart_famL_of_not_isBoundaryVertex hb] at e1
        change _ = (Sum.inr ⟨j, (lollipopGraph j.1.2).rot LollipopDart.gBar⟩ :
          H ⊕ Σ j : 𝒯, (famL 𝒯 j).Dart) at e1
        rw [lollipopGraph_rot_gBar] at e1
        have e2 := substRot_inr_attachDart (T := famT 𝒯) (R := famL 𝒯) hinj j
        rw [attachDart_famL_of_not_isBoundaryVertex hb] at e2
        have hnot : ¬∃ j' : 𝒯, G.rot j.1.1.intervalEnd = j'.1.1.intervalStart ∧
            G.IsBoundaryVertex j'.1.1.root := by
          rintro ⟨j', h, hb'⟩
          apply hb
          have hv : G.vertexOf (G.rot j.1.1.intervalEnd) = j'.1.1.root := by
            rw [h]; exact j'.1.1.mem_root_iff.1 j'.1.1.intervalStart_mem_root
          rw [G.vertexOf_rot, j.1.1.mem_root_iff.1 j.1.1.intervalEnd_mem_root] at hv
          rw [hv]
          exact hb'
        rw [lolliMap_of_not hnot]
        exact ReachOutside.step e1 (fun h => h (isCutDart_famL_of_not_isBoundaryVertex hb _))
          (ReachOutside.of_eq e2)
      · have hne : ∀ j', (famT 𝒯 j').intervalEnd ≠ d := by
          intro j' h
          by_cases hj : j' = j
          · subst hj; exact hend h.symm
          · exact Finset.disjoint_left.1 (hdisj hj) (famT 𝒯 j').intervalEnd_mem_darts (h ▸ hdj)
        have e := substRot_inl_of_forall_ne (R := famL 𝒯) hinj hne
        have hnot : ¬∃ j' : 𝒯, G.rot d = j'.1.1.intervalStart ∧
            G.IsBoundaryVertex j'.1.1.root := by
          rintro ⟨j', h, hb'⟩
          obtain ⟨i, -, hleg⟩ := exists_leg_eq_start hG j' hb'
          have hv : G.IsBoundaryVertex (G.vertexOf d) := by
            rw [← G.vertexOf_rot, h, hleg]
            exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
          exact DiskMap.rot_ne_of_isBoundaryVertex hG.boundaryVertex_card hv
            (DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card hv (G.rot_mem_vertexOf d)
              (G.self_mem_vertexOf d) (by rw [h, hleg]; exact hG.leg_notMem_bdry i)
              (j.1.1.notMem_bdry_of_mem_darts hdj))
        rw [lolliMap_of_not hnot]
        exact ReachOutside.of_eq e
    · push Not at hD
      have hne : ∀ j', (famT 𝒯 j').intervalEnd ≠ d := fun j' h =>
        hD j' (h ▸ (famT 𝒯 j').intervalEnd_mem_darts)
      have e := substRot_inl_of_forall_ne (R := famL 𝒯) hinj hne
      by_cases hs : ∃ j' : 𝒯, G.rot d = j'.1.1.intervalStart ∧ G.IsBoundaryVertex j'.1.1.root
      · obtain ⟨j', h, hb'⟩ := hs
        rw [h] at e ⊢
        rw [lolliMap_start hG h𝒯 j' hb']
        exact ReachOutside.step e (fun hm => hm j' j'.1.1.intervalStart_mem_darts)
          (reachOutside_lolli_start hG h𝒯 j' hb')
      · rw [lolliMap_of_not hs]
        exact ReachOutside.of_eq e

omit hG h𝒯 in
/-- A left inverse of `lolliMap'`. -/
private noncomputable def lolliUnmap (x : H ⊕ Σ j : 𝒯, (famL 𝒯 j).Dart) : H :=
  match x with
  | .inl d => d
  | .inr y => match (show LollipopDart from y.2) with
    | .gBar => G.inv y.1.1.1.intervalStart
    | _ => y.1.1.1.intervalStart

private theorem lolliUnmap_lolliMap' (d : H) : lolliUnmap (lolliMap' 𝒯 d) = d := by
  by_cases h₁ : ∃ j : 𝒯, d = G.inv j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root
  · obtain ⟨j, rfl, hb⟩ := h₁
    rw [lolliMap'_inv_start hG h𝒯 j hb]
    rfl
  · rw [lolliMap'_of_not h₁]
    by_cases h₂ : ∃ j : 𝒯, d = j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root
    · obtain ⟨j, rfl, hb⟩ := h₂
      rw [lolliMap_start hG h𝒯 j hb]
      rfl
    · rw [lolliMap_of_not h₂]
      rfl

omit [DecidableEq 𝒯] h𝒯 in
/-- The darts of the collapse are those of `K` and the darts `ḡ_i` across the first darts `g_i` of
the trees with a boundary root. -/
private theorem mem_collapseDarts_cases {x : H} (hx : x ∈ G.collapseDarts 𝒯) :
    (∃ j : 𝒯, x = G.inv j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root) ∨
      x ∈ G.collapseCore 𝒯 := by
  rcases hx with hx | ⟨i, hi, rfl⟩
  · exact Or.inr hx
  · obtain ⟨p, hp, hip⟩ := mem_familyDarts.1 hi
    refine Or.inl ⟨⟨p, hp⟩, by rw [p.1.leg_eq_intervalStart hG hip], ?_⟩
    rw [p.1.root_eq_bvertex_of_leg_mem hG hip]
    exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)

omit [DecidableEq 𝒯] h𝒯 in
private theorem inv_start_notMem_collapseCore (j : 𝒯) (hb : G.IsBoundaryVertex j.1.1.root) :
    G.inv j.1.1.intervalStart ∉ G.collapseCore 𝒯 := by
  obtain ⟨i, -, hleg⟩ := exists_leg_eq_start hG j hb
  rw [hleg]
  exact inv_leg_notMem_collapseCore hG (mem_familyDarts.2 ⟨j.1, j.2,
    hleg ▸ j.1.1.intervalStart_mem_darts⟩)

omit h𝒯 in
private theorem lolliMap'_of_mem_collapseCore {x : H} (hx : x ∈ G.collapseCore 𝒯) :
    lolliMap' 𝒯 x = lolliMap 𝒯 x :=
  lolliMap'_of_not fun ⟨j, h, hb⟩ => inv_start_notMem_collapseCore hG j hb (h ▸ hx)

private theorem lolliMap'_mem {x : H} (hx : x ∈ G.collapseDarts 𝒯) :
    lolliMap' 𝒯 x ∈ substDarts (famT 𝒯) (famL 𝒯) := by
  rcases mem_collapseDarts_cases hG hx with ⟨j, rfl, hb⟩ | hK
  · rw [lolliMap'_inv_start hG h𝒯 j hb, inr_mem_substDarts]
    rw [isCutDart_famL_iff_of_isBoundaryVertex hb]
    rintro (h | h) <;> cases h
  · rw [lolliMap'_of_mem_collapseCore hG hK]
    exact (lolliMap_mem_iff hG h𝒯 x).2 hK

private theorem lolliMap'_surj {z : H ⊕ Σ j : 𝒯, (famL 𝒯 j).Dart}
    (hz : z ∈ substDarts (famT 𝒯) (famL 𝒯)) :
    lolliUnmap z ∈ G.collapseDarts 𝒯 ∧ lolliMap' 𝒯 (lolliUnmap z) = z := by
  rcases z with d | ⟨j, l⟩
  · have hK : d ∈ G.collapseCore 𝒯 := (lolliMap_mem_iff hG h𝒯 d).1 (by
      have hd : ¬∃ j : 𝒯, d = j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root :=
        fun ⟨j, h, _⟩ => hz j (h ▸ j.1.1.intervalStart_mem_darts)
      rwa [lolliMap_of_not hd])
    refine ⟨G.collapseCore_subset 𝒯 hK, ?_⟩
    change lolliMap' 𝒯 d = _
    rw [lolliMap'_of_mem_collapseCore hG hK, lolliMap_of_not fun ⟨j, h, _⟩ =>
      hz j (h ▸ j.1.1.intervalStart_mem_darts)]
  · have hb : G.IsBoundaryVertex j.1.1.root := by
      by_contra hb
      exact hz (isCutDart_famL_of_not_isBoundaryVertex hb l)
    have hl := hz
    rw [inr_mem_substDarts] at hl
    change ¬(famT 𝒯 j).IsCutDart (famL 𝒯 j) l at hl
    rw [isCutDart_famL_iff_of_isBoundaryVertex hb] at hl
    obtain ⟨i, -, hleg⟩ := exists_leg_eq_start hG j hb
    have hiD : G.leg i ∈ G.familyDarts 𝒯 :=
      mem_familyDarts.2 ⟨j.1, j.2, hleg ▸ j.1.1.intervalStart_mem_darts⟩
    change LollipopDart at l
    cases l
    · exact absurd (Or.inl rfl) hl
    · exact absurd (Or.inr rfl) hl
    · have hK : j.1.1.intervalStart ∈ G.collapseCore 𝒯 := by
        rw [hleg]; exact G.leg_mem_collapseCore 𝒯 i
      refine ⟨G.collapseCore_subset 𝒯 hK, ?_⟩
      change lolliMap' 𝒯 j.1.1.intervalStart = _
      rw [lolliMap'_of_mem_collapseCore hG hK, lolliMap_start hG h𝒯 j hb]
    · refine ⟨show G.inv j.1.1.intervalStart ∈ G.collapseDarts 𝒯 from
        Or.inr ⟨i, hiD, by rw [hleg]⟩, ?_⟩
      change lolliMap' 𝒯 (G.inv j.1.1.intervalStart) = _
      rw [lolliMap'_inv_start hG h𝒯 j hb]

/-- The bijection between the darts of the collapse and of the substitution of lollipops. -/
private noncomputable def collapseLolliEquiv :
    G.collapseDarts 𝒯 ≃ substDarts (famT 𝒯) (famL 𝒯) :=
  Equiv.ofBijective (fun x => ⟨lolliMap' 𝒯 x, lolliMap'_mem hG h𝒯 x.2⟩)
    ⟨fun x y h => Subtype.ext (by
      have h' := congrArg (fun z : substDarts (famT 𝒯) (famL 𝒯) => lolliUnmap z.1) h
      simpa only [lolliUnmap_lolliMap' hG h𝒯] using h'),
     fun z => ⟨⟨_, (lolliMap'_surj hG h𝒯 z.2).1⟩, Subtype.ext (lolliMap'_surj hG h𝒯 z.2).2⟩⟩

private theorem coe_collapseLolliEquiv (x : G.collapseDarts 𝒯) :
    (collapseLolliEquiv hG h𝒯 x : H ⊕ Σ j : 𝒯, (famL 𝒯 j).Dart) = lolliMap' 𝒯 x :=
  rfl

/-- **The collapse is the substitution of lollipops**: `G/𝒯` is isomorphic to the substitution of
the lollipop graphs `L_c` into the trees of the members `(v, W, c)` of `𝒯`. -/
private theorem collapse_isomorphic_lollipops :
    (G.collapse 𝒯).Isomorphic (G.familySubstitution (famT 𝒯) (famL 𝒯) hG) := by
  have hdisj := h𝒯.pairwise_disjoint_darts hG
  have hinj := intervalEnd_injective (T := famT 𝒯) hdisj
  have hinv := hG.inv_involutive
  -- a dart of `K` that is not the first dart of a boundary tree is outside `D`
  have hKD : ∀ x ∈ G.collapseCore 𝒯,
      (¬∃ j : 𝒯, x = j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root) →
      ∀ j : 𝒯, x ∉ j.1.1.darts := by
    rintro x (hx | ⟨i, rfl⟩) hns j hj
    · exact hx (mem_familyDarts.2 ⟨j.1, j.2, hj⟩)
    · refine hns ⟨j, j.1.1.leg_eq_intervalStart hG hj, ?_⟩
      rw [j.1.1.root_eq_bvertex_of_leg_mem hG hj]
      exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  refine ⟨isoOfMapLeg (collapseLolliEquiv hG h𝒯) (fun x => Subtype.ext ?_) (fun x => Subtype.ext ?_)
    (fun x => ?_) (fun x hx => ?_) (fun i => Subtype.ext ?_)⟩
  · -- the involutions
    rw [coe_familySubstitution_inv, coe_collapseLolliEquiv, coe_collapseLolliEquiv,
      coe_collapse_inv hG]
    rcases mem_collapseDarts_cases hG x.2 with ⟨j, hx, hb⟩ | hK
    · rw [hx, hinv, lolliMap'_inv_start hG h𝒯 j hb,
        lolliMap'_of_mem_collapseCore hG (by
          obtain ⟨i, -, hleg⟩ := exists_leg_eq_start hG j hb
          rw [hleg]; exact G.leg_mem_collapseCore 𝒯 i), lolliMap_start hG h𝒯 j hb]
      rfl
    · rw [lolliMap'_of_mem_collapseCore hG hK]
      by_cases hs : ∃ j : 𝒯, (x : H) = j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root
      · obtain ⟨j, hx, hb⟩ := hs
        rw [hx, lolliMap_start hG h𝒯 j hb, lolliMap'_inv_start hG h𝒯 j hb]
        rfl
      · have hxD := hKD _ hK hs
        have hixD : ∀ j : 𝒯, G.inv x ∉ j.1.1.darts := fun j h =>
          hxD j (by simpa [hinv x] using j.1.1.inv_mem_darts hG h)
        rw [lolliMap_of_not hs, lolliMap'_of_not fun ⟨j, h, _⟩ => hixD j
          (by rw [h]; exact j.1.1.inv_mem_darts hG j.1.1.intervalStart_mem_darts),
          lolliMap_of_not fun ⟨j, h, _⟩ => hixD j (h ▸ j.1.1.intervalStart_mem_darts)]
        rfl
  · -- the rotations
    rw [coe_familySubstitution_rot, coe_collapseLolliEquiv]
    by_cases hK : (x : H) ∈ G.collapseCore 𝒯
    · rw [coe_collapse_rot_of_mem hK, lolliMap'_of_mem_collapseCore hG (firstReturn _ _ _).2]
      have hsim := coe_firstReturn_of_simulation (lolliMap 𝒯) (lolliMap_mem_iff hG h𝒯)
        (reachOutside_lolliMap hG h𝒯) ⟨x, hK⟩
      rw [← hsim]
      congr 2
      exact Subtype.ext (by rw [coe_collapseLolliEquiv, lolliMap'_of_mem_collapseCore hG hK])
    · rcases mem_collapseDarts_cases hG x.2 with ⟨j, hx, hb⟩ | hK'
      · rw [coe_collapse_rot_of_notMem hK]
        have hm : (collapseLolliEquiv hG h𝒯 x : H ⊕ Σ j : 𝒯, (famL 𝒯 j).Dart) =
            .inr ⟨j, LollipopDart.gBar⟩ := by
          rw [coe_collapseLolliEquiv, hx, lolliMap'_inv_start hG h𝒯 j hb]
        have e := substRot_inr_of_ne (T := famT 𝒯) (R := famL 𝒯) hinj (j := j)
          (y := LollipopDart.gBar)
          (by rw [attachDart_famL_of_isBoundaryVertex hb]; intro h; cases h)
        change _ = (Sum.inr ⟨j, (lollipopGraph j.1.2).rot LollipopDart.gBar⟩ :
          H ⊕ Σ j : 𝒯, (famL 𝒯 j).Dart) at e
        rw [lollipopGraph_rot_gBar] at e
        rw [coe_firstReturn_of_apply_mem (by rw [hm, e, ← hm]; exact Subtype.property _), hm,
          e, hx, lolliMap'_inv_start hG h𝒯 j hb]
      · exact absurd hK' hK
  · -- the boundary
    change (collapseLolliEquiv hG h𝒯 x) ∈ (G.familySubstitution (famT 𝒯) (famL 𝒯) hG).bdry ↔
      x ∈ G.bdry.subtype _
    rw [mem_familySubstitution_bdry, coe_collapseLolliEquiv, mem_subtype]
    constructor
    · rintro ⟨d, hd, h⟩
      have := congrArg lolliUnmap h
      rw [lolliUnmap_lolliMap' hG h𝒯] at this
      rwa [this]
    · intro hB
      have hK : (x : H) ∈ G.collapseCore 𝒯 := mem_collapseCore_of_mem_bdry hB
      have hns : ¬∃ j : 𝒯, (x : H) = j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root :=
        fun ⟨j, h, _⟩ => j.1.1.notMem_bdry_of_mem_darts j.1.1.intervalStart_mem_darts (h ▸ hB)
      exact ⟨x, hB, by rw [lolliMap'_of_mem_collapseCore hG hK, lolliMap_of_not hns]⟩
  · -- the colours
    rw [familySubstitution_colour, coe_collapseLolliEquiv]
    change _ = G.collapseColour 𝒯 x
    rcases mem_collapseDarts_cases hG x.2 with ⟨j, hxj, hb⟩ | hK
    · rw [hxj, lolliMap'_inv_start hG h𝒯 j hb]
      obtain ⟨i, -, hleg⟩ := exists_leg_eq_start hG j hb
      have hex : ∃ p ∈ 𝒯, ∃ i', G.leg i' ∈ p.1.darts ∧
          G.inv j.1.1.intervalStart = G.inv (G.leg i') :=
        ⟨j.1, j.2, i, hleg ▸ j.1.1.intervalStart_mem_darts, by rw [hleg]⟩
      rw [collapseColour, dif_pos hex]
      obtain ⟨hp, i', hi', heq⟩ := hex.choose_spec
      have heq' : j.1.1.intervalStart = G.leg i' := hinv.injective heq
      have hpj : hex.choose = j.1 := by
        by_contra hne
        exact Finset.disjoint_left.1 (h𝒯.pairwise_disjoint_darts hG
          (show (⟨hex.choose, hp⟩ : 𝒯) ≠ j from fun h => hne (congrArg Subtype.val h)))
          ((congrArg (· ∈ hex.choose.1.darts) heq').mpr hi') j.1.1.intervalStart_mem_darts
      rw [hpj]
      rfl
    · by_cases hs : ∃ j : 𝒯, (x : H) = j.1.1.intervalStart ∧ G.IsBoundaryVertex j.1.1.root
      · exfalso
        obtain ⟨j, hxj, hb⟩ := hs
        obtain ⟨i, -, hleg⟩ := exists_leg_eq_start hG j hb
        apply hx
        have hrot : ((G.collapse 𝒯).rot x : H) = G.rot x := by
          rw [coe_collapse_rot_of_mem hK]
          exact coe_firstReturn_of_apply_mem (mem_collapseCore_of_mem_bdry
            (by rw [hxj, hleg]; exact hG.rot_leg_mem_bdry' i))
        refine ⟨(G.collapse 𝒯).rot x, (G.collapse 𝒯).rot_mem_vertexOf x, ?_⟩
        rw [mem_collapse_bdry, hrot, hxj, hleg]
        exact hG.rot_leg_mem_bdry' i
      · rw [lolliMap'_of_mem_collapseCore hG hK, lolliMap_of_not hs]
        have hxD := hKD _ hK hs
        have hn : ¬∃ p ∈ 𝒯, ∃ i, G.leg i ∈ p.1.darts ∧ (x : H) = G.inv (G.leg i) := by
          rintro ⟨p, hp, i, hi, hxi⟩
          exact hxD ⟨p, hp⟩ (by rw [hxi]; exact p.1.inv_mem_darts hG hi)
        rw [collapseColour, dif_neg hn]
        rfl
  · -- the legs
    rw [coe_collapseLolliEquiv]
    change lolliMap' 𝒯 (G.leg i) = _
    rw [lolliMap'_of_mem_collapseCore hG (G.leg_mem_collapseCore 𝒯 i)]
    by_cases hi : ∃ j : 𝒯, G.leg i ∈ (famT 𝒯 j).darts
    · obtain ⟨j, hi⟩ := hi
      rw [coe_familySubstitution_leg_of_mem hG hdisj hi]
      have hb : G.IsBoundaryVertex j.1.1.root := by
        rw [j.1.1.root_eq_bvertex_of_leg_mem hG hi]
        exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
      rw [j.1.1.leg_eq_intervalStart hG hi, lolliMap_start hG h𝒯 j hb]
      rfl
    · push Not at hi
      rw [coe_familySubstitution_leg_of_notMem hG hi, lolliMap_of_not fun ⟨j, h, _⟩ =>
        hi j (h ▸ j.1.1.intervalStart_mem_darts)]

end CollapseIso2

/-! ### Collapsing is a sequence of moves -/

/-- **Collapsing a family is a sequence of moves (M2), (M3)**. Let `𝒯` be a collapsing family of a
plabic graph `G`. Then `G/𝒯` is a plabic graph `{M2, M3}`-equivalent to `G`. -/
@[cluster_algebras "lem_family_collapse_equivalent"]
theorem IsCollapsingFamily.moveEquivalent_collapse (hG : G.IsPlabicGraph)
    {𝒯 : Finset (G.RootedTree × Shade)} (h𝒯 : G.IsCollapsingFamily 𝒯) :
    ∃ h : (G.collapse 𝒯).IsPlabicGraph,
      PlabicGraph.MoveEquivalent {.m2, .m3} ⟨H, G, hG⟩ ⟨_, G.collapse 𝒯, h⟩ := by
  classical
  have hdisj := h𝒯.pairwise_disjoint_darts hG
  set ε : 𝒯 → Fin 2 := fun j => if G.IsBoundaryVertex j.1.1.root then 0 else 1
  have hterm := fun j : 𝒯 => exists_reflTransGen_isIrreducible (ε j) (j.1.1.toPlabicGraph hG)
  choose R hR hirr using hterm
  -- `G` is isomorphic to the substitution of the `P_T`
  have hP := isPlabicGraph_familySubstitution_toPlabicGraph (T := famT 𝒯) hG hdisj
  obtain ⟨θP⟩ := isomorphic_familySubstitution_toPlabicGraph (T := famT 𝒯) hG hdisj
  -- reduce all the `P_T`
  obtain ⟨hR', hPR⟩ := familySubstitution_moveEquivalent (T := famT 𝒯) hG hdisj
    (P := fun j => (famT 𝒯 j).toPlabicGraph hG) (R := R) hR hP
  -- the reductions are lollipops
  have θL : ∀ j : 𝒯, (R j).data.Iso (famL 𝒯 j).data := fun j =>
    Classical.choice (PlabicData.Isomorphic.symm _
      (lollipop_isomorphic_of_isIrreducible hG (h𝒯.isCollapsibleOfColour j.1 j.2) (hR j) (hirr j)))
  obtain ⟨θRL⟩ := familySubstitution_isomorphic hG hdisj θL
  obtain ⟨θC⟩ := collapse_isomorphic_lollipops hG h𝒯
  have hL := θRL.isPlabicGraph hR' (familySubstitution_legs_notMem hG hdisj _)
  have hC := θC.symm.isPlabicGraph hL fun i h => hG.leg_notMem_bdry i (mem_collapse_bdry.1 h)
  refine ⟨hC, ?_⟩
  refine (PlabicGraph.MoveEquivalent.of_isomorphic ⟨θP.symm⟩).trans (hPR.trans ?_)
  exact PlabicGraph.MoveEquivalent.of_isomorphic ⟨θC.trans θRL.symm⟩

/-- A collapsible tree of colour `c` forms a collapsing family `{(v, W, c)}` by itself. -/
theorem RootedTree.IsCollapsibleOfColour.isCollapsingFamily (hG : G.IsPlabicGraph)
    {T : G.RootedTree} {c : Shade} (hT : T.IsCollapsibleOfColour c) :
    G.IsCollapsingFamily {(T, c)} := by
  refine ⟨fun p hp => (mem_singleton.1 hp) ▸ hT, fun p hp q hq hne => ?_,
    fun p hp q hq hne => ?_, fun p hp => ?_⟩
  · exact absurd ((mem_singleton.1 hp).trans (mem_singleton.1 hq).symm) hne
  · exact absurd ((mem_singleton.1 hp).trans (mem_singleton.1 hq).symm) hne
  · obtain rfl := mem_singleton.1 hp
    -- the dart `σ a_k` follows the interval and is not a dart of `T`
    refine ⟨G.rot T.intervalEnd, ?_, fun q hq => ?_⟩
    · rw [T.mem_root_iff, G.vertexOf_rot, ← T.mem_root_iff]
      exact T.intervalEnd_mem_root
    · obtain rfl := mem_singleton.1 hq
      exact T.rot_intervalEnd_notMem hG

/-- **Collapsing one tree is a sequence of moves (M2), (M3)**. Let `G` be a plabic graph and
`(v, W)` a collapsible tree of colour `c` of `G`. Then `G/{(v, W, c)}` is a plabic graph
`{M2, M3}`-equivalent to `G`. -/
@[cluster_algebras "lem_tree_collapse_equivalent"]
theorem RootedTree.IsCollapsibleOfColour.moveEquivalent_collapse (hG : G.IsPlabicGraph)
    {T : G.RootedTree} {c : Shade} (hT : T.IsCollapsibleOfColour c) :
    ∃ h : (G.collapse {(T, c)}).IsPlabicGraph,
      PlabicGraph.MoveEquivalent {.m2, .m3} ⟨H, G, hG⟩ ⟨_, G.collapse {(T, c)}, h⟩ :=
  (hT.isCollapsingFamily hG).moveEquivalent_collapse hG

end PlabicData

end ClusterAlgebras

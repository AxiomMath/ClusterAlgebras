/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CollapseStepBivalent

/-!
# Collapse steps for edge contractions

Let `𝒯` be a collapsing family of a plabic graph `G`. If an edge of `G` is contracted, there is a
collapsing family of the new graph whose collapse is isomorphic to `G/𝒯` or obtained from it by a
contraction. This is case (V) of FWZ's proof. When the contracted edge has an endpoint at the root
of a tree, that tree is related to the modified tree by the removal of the root of a tree with one
interval dart, which is developed first.

## Main results

* `ClusterAlgebras.PlabicData.exists_isomorphic_contractEdge_collapse`: the edge lies outside the
  trees.
* `ClusterAlgebras.PlabicData.exists_collapse_contract_root`: the edge meets the root of a tree.
* `ClusterAlgebras.PlabicData.exists_collapse_contract_inside`: the edge lies inside a tree.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function _root_.Equiv _root_.Equiv.Perm

namespace PlabicData

/-! ### Removing the root of a tree with one interval dart -/

section RootRemoval

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- An edge of a tree is not a loop. -/
private theorem RootedTree.vertexOf_inv_ne (hG : G.IsPlabicGraph) (T : G.RootedTree) {d : H}
    (hd : d ∈ T.darts) : G.vertexOf d ≠ G.vertexOf (G.inv d) := fun h =>
  T.not_reflTransGen_of_mem_darts hG hd (h ▸ .refl)

variable (hG : G.IsPlabicGraph) (T : G.RootedTree) (hx : ¬G.IsBoundaryVertex T.root)
  (h1 : T.intervalLength = 1)
  (hne : (T.nonRoot.erase (G.vertexOf (G.inv T.intervalStart))).Nonempty)

include hG hx h1 hne

namespace RootRemoval

omit hx hne in
/-- The darts of the tree on `W \ {z}`, where `z = v(ā)` for the single interval dart `a` of `T`,
are the darts of `T` other than `a` and `ā`. -/
theorem mem_treeDarts_iff {e : H} :
    e ∈ G.treeDarts (T.nonRoot.erase (G.vertexOf (G.inv T.intervalStart))) ↔
      e ∈ T.darts ∧ e ≠ T.intervalStart ∧ e ≠ G.inv T.intervalStart := by
  have hinv := hG.inv_involutive
  set a := T.intervalStart with ha
  have hzW : G.vertexOf (G.inv a) ∈ T.nonRoot :=
    T.vertexOf_inv_mem_nonRoot_of_mem_root T.intervalStart_mem_darts T.intervalStart_mem_root
  have haR : G.vertexOf a = T.root := T.root_eq_vertexOf_intervalStart.symm
  -- a dart of `T` at the root is `a`
  have hroot : ∀ e ∈ T.darts, G.vertexOf e = T.root → e = a := fun e he her =>
    T.eq_intervalStart_of_intervalLength_eq_one h1 he (T.mem_root_iff.2 her)
  rw [mem_treeDarts, mem_erase, mem_erase]
  constructor
  · rintro ⟨hB, ⟨h1', h2'⟩ | ⟨h1', h2'⟩⟩
    · refine ⟨G.mem_treeDarts.2 ⟨hB, Or.inl h2'⟩, fun h => ?_, fun h => h1' (by rw [h])⟩
      rw [h, haR] at h2'; exact T.root_notMem_nonRoot h2'
    · refine ⟨G.mem_treeDarts.2 ⟨hB, Or.inr h2'⟩, fun h => h1' (by rw [h]), fun h => ?_⟩
      rw [h, hinv, haR] at h2'; exact T.root_notMem_nonRoot h2'
  · rintro ⟨heD, hea, hea'⟩
    refine ⟨T.notMem_bdry_of_mem_darts heD, ?_⟩
    have hieD := T.inv_mem_darts hG heD
    rcases T.vertexOf_mem_or_eq_root hG heD with h | h
    · by_cases hz : G.vertexOf e = G.vertexOf (G.inv a)
      · right
        refine ⟨fun h' => T.vertexOf_inv_ne hG heD (h'.symm ▸ hz), ?_⟩
        rcases T.vertexOf_mem_or_eq_root hG hieD with h'' | h''
        · exact h''
        · exact absurd (by rw [← hinv e, hroot _ hieD h'']) hea'
      · exact Or.inl ⟨hz, h⟩
    · exact absurd (hroot e heD h) hea

end RootRemoval

/-- **The tree with its root removed**: for a tree `T` whose interval is a single dart `a`, the
other end `z = v(ā)` of `a` is the root of the rooted tree `(z, W \ {z})`, whose interval is `z`
without `ā`. -/
noncomputable def rootRemovalTree : G.RootedTree :=
  have hinv := hG.inv_involutive
  have hD := fun e => RootRemoval.mem_treeDarts_iff hG T h1 (e := e)
  have hzW : G.vertexOf (G.inv T.intervalStart) ∈ T.nonRoot :=
    T.vertexOf_inv_mem_nonRoot_of_mem_root T.intervalStart_mem_darts T.intervalStart_mem_root
  have haD := T.intervalStart_mem_darts
  have hiaD := T.inv_mem_darts hG haD
  have hz2 : 2 ≤ (G.vertexOf (G.inv T.intervalStart)).card := by
    obtain ⟨w, hw⟩ := hne
    have hwW := (mem_erase.1 hw).2
    have hwz := (mem_erase.1 hw).1
    -- a path from `z` to `w` inside `W` leaves `z` by a dart other than `ā`
    have hpath : Relation.ReflTransGen T.NonRootAdj (G.vertexOf (G.inv T.intervalStart)) w := by
      obtain ⟨i, hi, hwi⟩ := T.exists_mem_branch hwW
      obtain rfl : i = 0 := by omega
      exact ((T.mem_branch).1 hwi).2
    obtain ⟨u, hu1, hu2⟩ : ∃ u, T.NonRootAdj (G.vertexOf (G.inv T.intervalStart)) u ∧
        u ≠ G.vertexOf (G.inv T.intervalStart) := by
      by_contra hcon
      push Not at hcon
      have : ∀ v, Relation.ReflTransGen T.NonRootAdj (G.vertexOf (G.inv T.intervalStart)) v →
          v = G.vertexOf (G.inv T.intervalStart) := by
        intro v hv
        induction hv with
        | refl => rfl
        | tail _ hs ih => rw [ih] at hs; exact hcon _ hs
      exact hwz (this w hpath)
    obtain ⟨-, huW', e, -, he1, he2⟩ := hu1
    have he' : e ≠ G.inv T.intervalStart := fun h => by
      rw [h, hinv, ← T.root_eq_vertexOf_intervalStart] at he2
      exact T.root_notMem_nonRoot (he2 ▸ huW')
    exact (card_pair he').symm.le.trans (card_le_card fun x hx => by
      rcases mem_insert.1 hx with rfl | hx
      · rw [← he1]; exact G.self_mem_vertexOf _
      · rw [mem_singleton.1 hx]; exact G.self_mem_vertexOf _)
  { root := G.vertexOf (G.inv T.intervalStart)
    nonRoot := T.nonRoot.erase (G.vertexOf (G.inv T.intervalStart))
    root_mem_vertices := G.vertexOf_mem_vertices _
    nonRoot_nonempty := hne
    nonRoot_subset := (erase_subset _ _).trans T.nonRoot_subset
    root_notMem_nonRoot := notMem_erase _ _
    vertexOf_inv_mem := by
      intro e he
      obtain ⟨hez, heW⟩ := mem_erase.1 he
      rcases mem_insert.1 (T.vertexOf_inv_mem e heW) with h | h
      · exfalso
        have hieD := T.mem_darts_of_vertexOf_mem heW
        have : G.inv e = T.intervalStart := T.eq_intervalStart_of_intervalLength_eq_one h1
          (T.inv_mem_darts hG hieD) (T.mem_root_iff.2 h)
        exact hez (by rw [← hinv e, this])
      · by_cases hz : G.vertexOf (G.inv e) = G.vertexOf (G.inv T.intervalStart)
        · rw [hz]; exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_erase.2 ⟨hz, h⟩)
    exists_interval := by
      refine ⟨G.rot (G.inv T.intervalStart), G.rot_mem_vertexOf _,
        (G.vertexOf (G.inv T.intervalStart)).card - 1, by omega, by omega, fun e he => ?_, ?_⟩
      · rw [hD]
        have heD : e ∈ T.darts := T.mem_darts_of_vertexOf_mem
          (by rwa [G.vertexOf_eq_of_mem he])
        have hea : e ≠ T.intervalStart := fun h => by
          have hv : G.vertexOf T.intervalStart = G.vertexOf (G.inv T.intervalStart) :=
            G.vertexOf_eq_of_mem (h ▸ he)
          exact T.root_notMem_nonRoot (by rwa [T.root_eq_vertexOf_intervalStart, hv])
        constructor
        · rintro ⟨-, -, hne'⟩
          obtain ⟨m, hm, rfl⟩ := exists_pow_lt_card he
          have hm0 : m ≠ 0 := by rintro rfl; exact hne' rfl
          refine ⟨m - 1, by omega, ?_⟩
          rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega)]
        · rintro ⟨j, hj, hje⟩
          refine ⟨heD, hea, fun h => ?_⟩
          rw [← hje, ← Perm.mul_apply, ← pow_succ] at h
          have := card_vertexOf_le_of_pow_apply_eq (G := G) (Nat.succ_pos j) h
          omega
      · rw [Equiv.symm_apply_apply, hD]
        exact fun h => h.2.2 rfl
    card_image_edgeOf := by
      have h2 := G.card_eq_two_mul_card_image_edgeOf hinv hG.inv_ne
        (S := G.treeDarts (T.nonRoot.erase (G.vertexOf (G.inv T.intervalStart))))
        fun e he => inv_mem_treeDarts' hG he
      have hD' : G.treeDarts (T.nonRoot.erase (G.vertexOf (G.inv T.intervalStart))) =
          (T.darts.erase T.intervalStart).erase (G.inv T.intervalStart) := by
        ext e
        rw [hD, mem_erase, mem_erase]
        tauto
      have h3 : (G.treeDarts (T.nonRoot.erase (G.vertexOf (G.inv T.intervalStart)))).card =
          T.darts.card - 2 := by
        rw [hD', card_erase_of_mem (mem_erase.2 ⟨fun h => hG.inv_ne _ h, hiaD⟩),
          card_erase_of_mem haD]
        rfl
      rw [card_erase_of_mem hzW]
      have := T.card_darts hG
      omega
    reflTransGen_treeAdj := by
      intro u hu
      rcases mem_insert.1 hu with rfl | hu
      · exact .refl
      obtain ⟨huz, huW⟩ := mem_erase.1 hu
      obtain ⟨i, hi, hui⟩ := T.exists_mem_branch huW
      obtain rfl : i = 0 := by omega
      refine ((T.mem_branch).1 hui).2.mono fun u₁ u₂ ⟨hu₁, hu₂, e, heD, he1, he2⟩ => ?_
      refine ⟨e, (hD e).2 ⟨heD, fun h => ?_, fun h => ?_⟩, he1, he2⟩
      · rw [h, ← T.root_eq_vertexOf_intervalStart] at he1
        exact T.root_notMem_nonRoot (he1 ▸ hu₁)
      · rw [h, hinv, ← T.root_eq_vertexOf_intervalStart] at he2
        exact T.root_notMem_nonRoot (he2 ▸ hu₂) }


namespace RootRemoval

omit hx in
private theorem darts_iff {e : H} : e ∈ (rootRemovalTree hG T h1 hne).darts ↔
    e ∈ T.darts ∧ e ≠ T.intervalStart ∧ e ≠ G.inv T.intervalStart :=
  mem_treeDarts_iff hG T h1

omit hx in
/-- The root of the tree with its root removed is the other end `v(ā)` of the interval dart `a`. -/
theorem root_eq :
    (rootRemovalTree hG T h1 hne).root = G.vertexOf (G.inv T.intervalStart) := rfl

omit hx in
/-- The non-root vertices of the tree with its root removed are those of `T` other than `v(ā)`. -/
theorem nonRoot_eq : (rootRemovalTree hG T h1 hne).nonRoot =
    T.nonRoot.erase (G.vertexOf (G.inv T.intervalStart)) := rfl

omit hx in
private theorem not_isBoundaryVertex_root :
    ¬G.IsBoundaryVertex (rootRemovalTree hG T h1 hne).root := fun h =>
  (G.mem_internalVertices.1 (T.nonRoot_subset (T.vertexOf_inv_mem_nonRoot_of_mem_root
    T.intervalStart_mem_darts T.intervalStart_mem_root))).2 h

omit hx in
private theorem intervalStart_eq :
    (rootRemovalTree hG T h1 hne).intervalStart = G.rot (G.inv T.intervalStart) := by
  have hinv := hG.inv_involutive
  set Tz := rootRemovalTree hG T h1 hne
  refine (Tz.eq_intervalStart_of_rot_symm_notMem ?_ (G.rot_mem_vertexOf _) ?_).symm
  · obtain ⟨j, hj, hj'⟩ := (Tz.mem_darts_iff_of_mem_root (Tz.intervalStart_mem_root)).1
      Tz.intervalStart_mem_darts
    -- `σ ā` is the first dart of the interval of `Tz`
    have := Tz.intervalStart_mem_darts
    rw [darts_iff] at this ⊢
    obtain ⟨hD, ha, hia⟩ := this
    have hz := Tz.intervalStart_mem_root
    rw [root_eq] at hz
    have hrz : G.rot (G.inv T.intervalStart) ∈ G.vertexOf (G.inv T.intervalStart) :=
      G.rot_mem_vertexOf _
    refine ⟨T.mem_darts_of_vertexOf_mem (by
      rw [G.vertexOf_rot]; exact T.vertexOf_inv_mem_nonRoot_of_mem_root T.intervalStart_mem_darts
        T.intervalStart_mem_root), fun h => ?_, fun h => ?_⟩
    · have hv : G.vertexOf (G.rot (G.inv T.intervalStart)) = G.vertexOf T.intervalStart := by rw [h]
      rw [G.vertexOf_rot] at hv
      exact T.vertexOf_inv_ne hG T.intervalStart_mem_darts hv.symm
    · -- `σ ā = ā` would make `z` a leaf, but `z` has another dart in `Tz`
      have hfix : ∀ n : ℕ, (G.rot ^ n) (G.inv T.intervalStart) = G.inv T.intervalStart := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ', Perm.mul_apply, ih, h]
      obtain ⟨n, hn⟩ := ((G.mem_vertexOf).1 hz).exists_nat_pow_eq
      rw [hfix] at hn
      exact hia hn.symm
  · rw [Equiv.symm_apply_apply, darts_iff]
    exact fun h => h.2.2 rfl


omit hG h1 hne in
/-- The dart `ḡ` of `P_T`. -/
def dartGBar : T.Dart := ⟨.inr .gBar, hx⟩

omit h1 hne in
/-- The rotation of `P_T` sends `ḡ` to the first dart of the interval of `T`. -/
theorem rot_dartGBar : T.plabicData.rot (dartGBar T hx) =
    ⟨.inl T.intervalStart, T.intervalStart_mem_darts⟩ :=
  Subtype.ext (by rw [T.coe_rot_plabicData hG]; rfl)

omit hG hx hne in
private theorem rot_intervalStart_notMem' : G.rot T.intervalStart ∉ T.darts := by
  intro h
  have hk := T.intervalLength_lt_card
  rw [h1] at hk
  have := T.eq_intervalStart_of_intervalLength_eq_one h1 h (by
    rw [T.mem_root_iff, G.vertexOf_rot, ← T.root_eq_vertexOf_intervalStart])
  have hpow : ∀ n : ℕ, (G.rot ^ n) T.intervalStart = T.intervalStart := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Perm.mul_apply, ih, this]
  have hsub : T.root ⊆ {T.intervalStart} := fun e he => by
    rw [T.mem_root_iff, T.root_eq_vertexOf_intervalStart] at he
    obtain ⟨n, rfl⟩ := ((G.vertexOf_eq_vertexOf_iff).1 he.symm).exists_nat_pow_eq
    rw [mem_singleton, hpow]
  have := card_le_card hsub
  rw [card_singleton] at this
  omega

omit hne in
private theorem rot_intervalStart_dart : T.plabicData.rot ⟨.inl T.intervalStart,
    T.intervalStart_mem_darts⟩ = dartGBar T hx :=
  Subtype.ext (by
    rw [T.coe_rot_plabicData hG]
    change T.rotAux (.inl T.intervalStart) = _
    simp [RootedTree.rotAux, rot_intervalStart_notMem' T h1, hx, dartGBar])

omit hne in
/-- The vertex `{ḡ, a}` of `P_T` is a removable bivalent vertex. -/
theorem isBivalentRemovable_dartGBar :
    T.plabicData.IsBivalentRemovable (dartGBar T hx) := by
  refine isBivalentRemovable_of_rot_rot ?_ ?_ ?_ ?_ ?_
  · rw [rot_dartGBar hG T hx, rot_intervalStart_dart hG T hx h1]
  · rw [rot_dartGBar hG T hx]
    exact fun h => by simpa [dartGBar] using congrArg Subtype.val h
  · rw [T.mem_bdry_plabicData]
    rintro (h | h) <;> simp [dartGBar, RootedTree.dartE, RootedTree.dartEBar] at h
  · rw [rot_dartGBar hG T hx, T.mem_bdry_plabicData]
    rintro (h | h) <;> simp [RootedTree.dartE, RootedTree.dartEBar] at h
  · rw [rot_dartGBar hG T hx]
    intro h
    have := congrArg Subtype.val h
    rw [T.coe_inv_plabicData hG] at this
    simp [dartGBar, LollipopDart.bar] at this

/-- **The plabic graph of the tree with its root removed** is the removal of the bivalent vertex
`{ḡ, a}` from `P_T`. -/
theorem plabicData_isomorphic :
    (T.plabicData.bivalentRemoval (T.isPlabicGraph_plabicData hG)
      (isBivalentRemovable_dartGBar hG T hx h1)).Isomorphic
      (rootRemovalTree hG T h1 hne).plabicData := by
  have hinv := hG.inv_involutive
  set Tz := rootRemovalTree hG T h1 hne with hTz
  set P := T.plabicData with hPdef
  have hP := T.isPlabicGraph_plabicData hG
  set δ := dartGBar T hx with hδdef
  have hδ := isBivalentRemovable_dartGBar hG T hx h1
  set a := T.intervalStart with ha
  have hrδ : P.rot δ = ⟨.inl a, T.intervalStart_mem_darts⟩ := rot_dartGBar hG T hx
  have hbz : ¬G.IsBoundaryVertex Tz.root := not_isBoundaryVertex_root hG T h1 hne
  have hD := fun e => darts_iff hG T h1 hne (e := e)
  have hstart : Tz.intervalStart = G.rot (G.inv a) := intervalStart_eq hG T h1 hne
  have hiaD : G.inv a ∈ T.darts := T.inv_mem_darts hG T.intervalStart_mem_darts
  have hσia : G.rot (G.inv a) ∈ Tz.darts := by rw [← hstart]; exact Tz.intervalStart_mem_darts
  -- the map of darts
  let ψ : H ⊕ LollipopDart → H ⊕ LollipopDart
    | .inl e => if e = G.inv a then .inr .gBar else .inl e
    | .inr l => .inr l
  have hmemS : ∀ s : ({δ, P.rot δ}ᶜ : Set T.Dart), (s : T.Dart).1 ≠ .inl a ∧
      (s : T.Dart).1 ≠ .inr .gBar := by
    intro s
    have := mem_compl_pair.1 s.2
    refine ⟨fun h => this.2 (Subtype.ext (h.trans (congrArg Subtype.val hrδ).symm)),
      fun h => this.1 (Subtype.ext h)⟩
  have hmap : ∀ s : ({δ, P.rot δ}ᶜ : Set T.Dart), Tz.IsDart (ψ (s : T.Dart).1) := by
    rintro ⟨⟨x | (_ | _ | _ | _), hx'⟩, hs⟩
    · by_cases h : x = G.inv a
      · change Tz.IsDart (if x = G.inv a then _ else _)
        rwa [if_pos h]
      · change Tz.IsDart (if x = G.inv a then _ else _)
        rw [if_neg h]
        exact (hD x).2 ⟨hx', fun h' => (hmemS ⟨_, hs⟩).1 (congrArg Sum.inl h'), h⟩
    · trivial
    · trivial
    · exact hbz
    · exact absurd rfl (hmemS ⟨_, hs⟩).2
  let χ : H ⊕ LollipopDart → H ⊕ LollipopDart
    | .inl e => .inl e
    | .inr .gBar => .inl (G.inv a)
    | .inr l => .inr l
  have hχ : ∀ s : ({δ, P.rot δ}ᶜ : Set T.Dart), χ (ψ (s : T.Dart).1) = (s : T.Dart).1 := by
    rintro ⟨⟨x | (_ | _ | _ | _), hx'⟩, hs⟩
    · by_cases h : x = G.inv a
      · subst h
        change χ (if G.inv a = G.inv a then _ else _) = _
        rw [if_pos rfl]
      · change χ (if x = G.inv a then _ else _) = _
        rw [if_neg h]
    · rfl
    · rfl
    · rfl
    · exact absurd rfl (hmemS ⟨_, hs⟩).2
  let e : ({δ, P.rot δ}ᶜ : Set T.Dart) ≃ Tz.Dart :=
    Equiv.ofBijective (fun s => ⟨ψ (s : T.Dart).1, hmap s⟩) ⟨by
      intro s s' h
      have := congrArg (fun t : Tz.Dart => χ t.1) h
      simp only [hχ] at this
      exact Subtype.ext (Subtype.ext this), by
      rintro ⟨y | (_ | _ | _ | _), hy⟩
      · obtain ⟨hyD, hya, hyia⟩ := (hD y).1 hy
        refine ⟨⟨⟨.inl y, hyD⟩, mem_compl_pair.2 ⟨fun h => ?_, fun h => ?_⟩⟩, ?_⟩
        · exact absurd (congrArg Subtype.val h) (fun h' => by cases h')
        · rw [hrδ] at h; exact hya (by simpa using congrArg Subtype.val h)
        · refine Subtype.ext ?_
          change (if y = G.inv a then _ else _) = _
          rw [if_neg hyia]
      · refine ⟨⟨⟨.inr .e, trivial⟩, mem_compl_pair.2 ⟨fun h => ?_, fun h => ?_⟩⟩, rfl⟩
        · exact absurd (congrArg Subtype.val h) (fun h' => by cases h')
        · rw [hrδ] at h; exact absurd (congrArg Subtype.val h) (fun h' => by cases h')
      · refine ⟨⟨⟨.inr .eBar, trivial⟩, mem_compl_pair.2 ⟨fun h => ?_, fun h => ?_⟩⟩, rfl⟩
        · exact absurd (congrArg Subtype.val h) (fun h' => by cases h')
        · rw [hrδ] at h; exact absurd (congrArg Subtype.val h) (fun h' => by cases h')
      · refine ⟨⟨⟨.inr .g, hx⟩, mem_compl_pair.2 ⟨fun h => ?_, fun h => ?_⟩⟩, rfl⟩
        · exact absurd (congrArg Subtype.val h) (fun h' => by cases h')
        · rw [hrδ] at h; exact absurd (congrArg Subtype.val h) (fun h' => by cases h')
      · refine ⟨⟨⟨.inl (G.inv a), hiaD⟩, mem_compl_pair.2 ⟨fun h => ?_, fun h => ?_⟩⟩, ?_⟩
        · exact absurd (congrArg Subtype.val h) (fun h' => by cases h')
        · rw [hrδ] at h
          exact hG.inv_ne a (by simpa using congrArg Subtype.val h)
        · refine Subtype.ext ?_
          change (if G.inv a = G.inv a then _ else _) = _
          rw [if_pos rfl]⟩
  have he : ∀ s, ((e s : Tz.Dart) : H ⊕ LollipopDart) = ψ (s : T.Dart).1 := fun _ => rfl
  have hψa : ψ (.inl (G.inv a)) = .inr .gBar := by
    change (if G.inv a = G.inv a then _ else _) = _
    rw [if_pos rfl]
  have hψne : ∀ x, x ≠ G.inv a → ψ (.inl x) = .inl x := fun x h => by
    change (if x = G.inv a then _ else _) = _
    rw [if_neg h]
  have hψr : ∀ l, ψ (.inr l) = .inr l := fun _ => rfl
  have hσia_ne : G.rot (G.inv a) ≠ G.inv a := ((hD _).1 hσia).2.2
  set R := P.bivalentRemoval hP hδ with hR
  refine ⟨Iso.ofEquivOfMapLeg e (fun s => Subtype.ext ?_) (fun s => Subtype.ext ?_) (fun s => ?_)
    (fun s hs => ?_) (fun i => Subtype.ext ?_)⟩
  · -- the involutions
    have hviδ : ((P.inv δ : T.Dart) : H ⊕ LollipopDart) = .inr .g := by
      rw [T.coe_inv_plabicData hG]; rfl
    have hvirδ : ((P.inv (P.rot δ) : T.Dart) : H ⊕ LollipopDart) = .inl (G.inv a) := by
      rw [T.coe_inv_plabicData hG, hrδ]; rfl
    rw [he, Tz.coe_inv_plabicData hG, he]
    by_cases h₁ : (s : T.Dart) = P.inv δ
    · rw [coe_bivalentRemoval_inv_of_eq_inv hP hδ h₁, hvirδ, h₁, hviδ, hψa, hψr]
      rfl
    by_cases h₂ : (s : T.Dart) = P.inv (P.rot δ)
    · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hP hδ h₂, hviδ, h₂, hvirδ, hψa, hψr]
      rfl
    rw [coe_bivalentRemoval_inv_of_ne hP hδ h₁ h₂, T.coe_inv_plabicData hG]
    rcases s with ⟨⟨x | l, hx'⟩, hs⟩
    · have h₂' : x ≠ G.inv a := fun h => h₂ (Subtype.ext (by rw [hvirδ, ← h]))
      have hxa : G.inv x ≠ G.inv a := fun h => (hmemS ⟨_, hs⟩).1
        (congrArg Sum.inl (G.inv.injective h))
      change ψ (.inl (G.inv x)) = Sum.map G.inv LollipopDart.bar (ψ (.inl x))
      rw [hψne _ hxa, hψne _ h₂']
      rfl
    · rfl
  · -- the rotations
    rw [he, coe_bivalentRemoval_rot, T.coe_rot_plabicData hG, Tz.coe_rot_plabicData hG, he]
    rcases s with ⟨⟨x | (_ | _ | _ | _), hx'⟩, hs⟩
    · have hxa : x ≠ a := fun h => (hmemS ⟨_, hs⟩).1 (congrArg Sum.inl h)
      have hσxD : G.rot x ∈ T.darts := by
        rcases T.vertexOf_mem_or_eq_root hG hx' with h | h
        · exact T.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_rot])
        · exact absurd (T.eq_intervalStart_of_intervalLength_eq_one h1 hx'
            (T.mem_root_iff.2 h)) hxa
      have hrx : T.rotAux (.inl x) = .inl (G.rot x) := if_pos hσxD
      change ψ (T.rotAux (.inl x)) = Tz.rotAux (ψ (.inl x))
      rw [hrx]
      by_cases hxia : x = G.inv a
      · subst hxia
        rw [hψa, hψne _ hσia_ne]
        change _ = Sum.inl Tz.intervalStart
        rw [hstart]
      rw [hψne _ hxia]
      by_cases hσ : G.rot x = G.inv a
      · rw [hσ, hψa]
        have hnot : G.rot x ∉ Tz.darts := fun h => ((hD _).1 h).2.2 hσ
        simp only [RootedTree.rotAux, hnot, hbz, if_false]
      · rw [hψne _ hσ]
        have hin : G.rot x ∈ Tz.darts := (hD _).2 ⟨hσxD, T.rot_ne_intervalStart hx', hσ⟩
        simp only [RootedTree.rotAux, hin, if_true]
    · change ψ (T.rotAux (.inr .e)) = Tz.rotAux (.inr .e)
      simp only [RootedTree.rotAux, hx, hbz, if_false]
      rfl
    · rfl
    · rfl
    · exact absurd rfl (hmemS ⟨_, hs⟩).2
  · -- the boundaries
    rw [mem_bivalentRemoval_bdry, Tz.mem_bdry_plabicData, T.mem_bdry_plabicData]
    rcases s with ⟨⟨x | (_ | _ | _ | _), hx'⟩, hs⟩
    · have hl : ∀ t : Tz.Dart, (t : H ⊕ LollipopDart) = ψ (.inl x) →
          ¬(t = Tz.dartE ∨ t = Tz.dartEBar) := by
        rintro t ht (rfl | rfl) <;>
        · by_cases hxia : x = G.inv a
          · rw [hxia, hψa] at ht; cases ht
          · rw [hψne _ hxia] at ht; cases ht
      refine iff_of_false (hl _ rfl) ?_
      rintro (h | h) <;> cases congrArg Subtype.val h
    · exact iff_of_true (Or.inl rfl) (Or.inl rfl)
    · exact iff_of_true (Or.inr rfl) (Or.inr rfl)
    · refine iff_of_false ?_ ?_ <;> rintro (h | h) <;> cases congrArg Subtype.val h
    · exact absurd rfl (hmemS ⟨_, hs⟩).2
  · -- the colours
    change Tz.colourAux (ψ (s : T.Dart).1) = T.colourAux (s : T.Dart).1
    rcases s with ⟨⟨x | l, hx'⟩, hs'⟩
    · by_cases hxia : x = G.inv a
      · subst hxia
        rw [hψa]
        change G.colour Tz.intervalStart = G.colour (G.inv a)
        rw [hstart]
        exact hG.colour_rot _ hbz
      · rw [hψne _ hxia]
        rfl
    · exfalso
      apply hs
      rcases l with _ | _ | _ | _
      · refine ⟨_, R.self_mem_vertexOf _, ?_⟩
        rw [mem_bivalentRemoval_bdry, T.mem_bdry_plabicData]
        exact Or.inl rfl
      · refine ⟨_, R.self_mem_vertexOf _, ?_⟩
        rw [mem_bivalentRemoval_bdry, T.mem_bdry_plabicData]
        exact Or.inr rfl
      · refine ⟨_, R.rot_mem_vertexOf _, ?_⟩
        rw [mem_bivalentRemoval_bdry, T.mem_bdry_plabicData]
        refine Or.inr (Subtype.ext ?_)
        rw [coe_bivalentRemoval_rot, T.coe_rot_plabicData hG]
        rfl
      · exact absurd rfl (hmemS ⟨_, hs'⟩).2
  · -- the legs
    change ψ ((P.leg i : T.Dart) : H ⊕ LollipopDart) = (Tz.legDart : _ ⊕ LollipopDart)
    change ψ (T.legDart : H ⊕ LollipopDart) = _
    rw [RootedTree.legDart, RootedTree.legDart, dif_neg hx, dif_neg hbz]

end RootRemoval

end RootRemoval


/-! ### Contracting an edge outside the trees -/

section ContractOutside

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {f : H} (he : G.IsContractibleEdge f)

include hG he

omit hG in
/-- The merged vertex has at least as many darts as an endpoint, when the other endpoint has at
least two darts. -/
private theorem card_mergedVertex_ge (h₂ : 2 ≤ (G.vertexOf (G.inv f)).card) :
    (G.vertexOf f).card ≤ (G.mergedVertex f).card := by
  have hdisj : Disjoint (G.vertexOf f) (G.vertexOf (G.inv f)) := by
    rw [disjoint_left]
    intro x hx hx'
    exact he.vertexOf_ne ((G.vertexOf_eq_of_mem hx).symm.trans (G.vertexOf_eq_of_mem hx'))
  have h := le_card_sdiff ({f, G.inv f} : Finset H) (G.vertexOf f ∪ G.vertexOf (G.inv f))
  rw [card_union_of_disjoint hdisj] at h
  have h3 : ({f, G.inv f} : Finset H).card ≤ 2 := card_le_two
  unfold mergedVertex
  omega

omit hG in
private theorem card_mergedVertex_ge' (h₁ : 2 ≤ (G.vertexOf f).card) :
    (G.vertexOf (G.inv f)).card ≤ (G.mergedVertex f).card := by
  have hdisj : Disjoint (G.vertexOf f) (G.vertexOf (G.inv f)) := by
    rw [disjoint_left]
    intro x hx hx'
    exact he.vertexOf_ne ((G.vertexOf_eq_of_mem hx).symm.trans (G.vertexOf_eq_of_mem hx'))
  have h := le_card_sdiff ({f, G.inv f} : Finset H) (G.vertexOf f ∪ G.vertexOf (G.inv f))
  rw [card_union_of_disjoint hdisj] at h
  have h3 : ({f, G.inv f} : Finset H).card ≤ 2 := card_le_two
  unfold mergedVertex
  omega

/-- The merged vertex has `|v(f)| + |v(f̄)| - 2` darts. -/
private theorem card_mergedVertex_add_two :
    (G.mergedVertex f).card + 2 = (G.vertexOf f).card + (G.vertexOf (G.inv f)).card := by
  have hdisj : Disjoint (G.vertexOf f) (G.vertexOf (G.inv f)) := by
    rw [disjoint_left]
    intro x hx hx'
    exact he.vertexOf_ne ((G.vertexOf_eq_of_mem hx).symm.trans (G.vertexOf_eq_of_mem hx'))
  have hsub : ({f, G.inv f} : Finset H) ⊆ G.vertexOf f ∪ G.vertexOf (G.inv f) := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact mem_union_left _ (G.self_mem_vertexOf _)
    · rw [mem_singleton.1 hx]; exact mem_union_right _ (G.self_mem_vertexOf _)
  have hne : f ≠ G.inv f := (hG.inv_ne f).symm
  have h := card_sdiff_add_card_eq_card hsub
  rw [card_union_of_disjoint hdisj, card_pair hne] at h
  unfold mergedVertex
  omega

/-- A tree whose non-root vertices avoid both endpoints embeds into the contraction, if its
interval leaves a dart of the merged vertex outside when the root is an endpoint. -/
private theorem contractOutside_isEmbedding (x₀ : (({f, G.inv f} : Set H)ᶜ : Set H))
    {T : G.RootedTree} (hyW : G.vertexOf f ∉ T.nonRoot) (hzW : G.vertexOf (G.inv f) ∉ T.nonRoot)
    (h2 : T.root = G.vertexOf f ∨ T.root = G.vertexOf (G.inv f) →
      T.intervalLength < (G.mergedVertex f).card) :
    T.IsEmbedding (G.contractEdge f (he.leg_mem hG)) (toCompl f (G.inv f) x₀) := by
  have hinv := hG.inv_involutive
  have hne := he.not_sameCycle
  -- the darts of `T` avoid `f` and `f̄`
  have hfT : f ∉ T.darts := fun h => by
    rcases T.vertexOf_mem_or_eq_root hG h with h' | h'
    · exact hyW h'
    · have := T.vertexOf_inv_mem_nonRoot_of_mem_root h (T.mem_root_iff.2 h')
      exact hzW this
  have hfT' : G.inv f ∉ T.darts := fun h => hfT (by
    have := T.inv_mem_darts hG h; rwa [hinv] at this)
  have hc : ∀ {e}, e ∈ T.darts → e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := fun {e} h =>
    mem_compl_pair_iff.2 ⟨fun h' => hfT (h' ▸ h), fun h' => hfT' (h' ▸ h)⟩
  -- a dart at an endpoint which is not the root is not a dart of `T`
  have hnotD : ∀ {e}, G.vertexOf e = G.vertexOf f ∨ G.vertexOf e = G.vertexOf (G.inv f) →
      G.vertexOf e ≠ T.root → e ∉ T.darts := by
    intro e hv hr heT
    rcases T.vertexOf_mem_or_eq_root hG heT with h | h
    · rcases hv with hv | hv
      · exact hyW (hv ▸ h)
      · exact hzW (hv ▸ h)
    · exact hr h
  have hM := card_mergedVertex_add_two hG he
  have hone : ∀ {e : H}, G.rot e = e → (G.vertexOf e).card ≤ 1 := fun {e} h =>
    card_vertexOf_le_of_pow_apply_eq (n := 1) one_pos (by rwa [pow_one])
  -- the interval and one more dart cannot fill the root
  have hfill : ∀ {x : H}, G.rot T.intervalEnd = x → G.rot x = T.intervalStart →
      (G.vertexOf T.intervalStart).card ≤ T.intervalLength + 1 := fun {x} hx1 hx2 => by
    refine card_vertexOf_le_of_pow_apply_eq (n := T.intervalLength + 1) (by omega) ?_
    have hk := T.one_le_intervalLength
    have hend : (G.rot ^ (T.intervalLength - 1)) T.intervalStart = T.intervalEnd := rfl
    rw [show T.intervalLength + 1 = T.intervalLength - 1 + 1 + 1 by omega, pow_succ',
      Perm.mul_apply, pow_succ', Perm.mul_apply, hend, hx1, hx2]
  have ha1r : G.vertexOf T.intervalStart = T.root := T.root_eq_vertexOf_intervalStart.symm
  refine ⟨fun e he' e' he'' h => injOn_toCompl x₀ (hc he') (hc he'') h, fun e he' => ?_,
    fun e he' he'' => ?_, fun e he' => ?_, ?_, ?_, ?_, fun e he' => ?_⟩
  · apply Subtype.ext
    rw [toCompl_of_mem (hc (T.inv_mem_darts hG he')), toCompl_of_mem (hc he'),
      coe_contractEdge_inv hinv]
  · apply Subtype.ext
    rw [toCompl_of_mem (hc he''), toCompl_of_mem (hc he'),
      coe_contractEdge_rot_of_mem (x := ⟨e, hc he'⟩) (hc he'')]
  · rw [toCompl_of_mem (hc he'), mem_contractEdge_bdry]
    exact T.notMem_bdry_of_mem_darts he'
  · -- the rotation leaves the interval at its end
    rw [toCompl_of_mem (hc T.intervalEnd_mem_darts)]
    have hend := T.intervalEnd_mem_darts
    have hrend := T.rot_intervalEnd_notMem hG
    have hendr : G.vertexOf T.intervalEnd = T.root := by
      rcases T.vertexOf_mem_or_eq_root hG hend with h' | h'
      · exact absurd (T.rot_mem_darts_of_vertexOf_mem h') hrend
      · exact h'
    -- the image of `a_k` is a dart `x` outside `T`
    have hgen : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H),
        (G.contractEdge f (he.leg_mem hG)).rot ⟨T.intervalEnd, hc hend⟩ = x →
        (x : H) ∉ T.darts →
        (G.contractEdge f (he.leg_mem hG)).rot ⟨T.intervalEnd, hc hend⟩ ∉
          T.darts.image (toCompl f (G.inv f) x₀) := by
      intro x hx hxT h
      rw [hx] at h
      obtain ⟨e, heT, hfe⟩ := mem_image.1 h
      have hval := congrArg Subtype.val hfe
      rw [coe_toCompl_of_mem (hc heT)] at hval
      exact hxT (hval ▸ heT)
    by_cases h1 : G.rot T.intervalEnd = f
    · have hroot : T.root = G.vertexOf f := by rw [← hendr, ← G.vertexOf_rot, h1]
      have hk := h2 (Or.inl hroot)
      by_cases hz1 : G.rot (G.inv f) = G.inv f
      · have hσfS : G.rot f ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2
          ⟨fun h => hfT (G.rot.injective (h1.trans h.symm) ▸ hend),
            fun h => he.vertexOf_ne (by rw [← G.vertexOf_rot f, h])⟩
        refine hgen ⟨_, hσfS⟩ (Subtype.ext (coe_contractEdge_rot_of_eq_of_eq h1 hz1 hσfS)) ?_
        intro hσf
        have ha := T.rot_eq_intervalStart hG hfT hσf
        have h3 := hfill h1 ha
        rw [ha1r, hroot] at h3
        have h4 := hone hz1
        omega
      · have hrzS : G.rot (G.inv f) ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2
          ⟨fun h => he.vertexOf_ne (by rw [← G.vertexOf_rot (G.inv f), h]), hz1⟩
        refine hgen ⟨_, hrzS⟩ (Subtype.ext (coe_contractEdge_rot_of_eq h1 hrzS)) ?_
        exact hnotD (Or.inr (G.vertexOf_rot _)) (by
          rw [G.vertexOf_rot, hroot]; exact Ne.symm he.vertexOf_ne)
    by_cases h2' : G.rot T.intervalEnd = G.inv f
    · have hroot : T.root = G.vertexOf (G.inv f) := by rw [← hendr, ← G.vertexOf_rot, h2']
      have hk := h2 (Or.inr hroot)
      by_cases hy1 : G.rot f = f
      · have hσzS : G.rot (G.inv f) ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2
          ⟨fun h => he.vertexOf_ne (by rw [← G.vertexOf_rot (G.inv f), h]),
            fun h => hfT' (G.rot.injective (h2'.trans h.symm) ▸ hend)⟩
        refine hgen ⟨_, hσzS⟩ (Subtype.ext (coe_contractEdge_rot_of_eq_inv_of_eq h2' hy1 hσzS)) ?_
        intro hσz
        have ha := T.rot_eq_intervalStart hG hfT' hσz
        have h3 := hfill h2' ha
        rw [ha1r, hroot] at h3
        have h4 := hone hy1
        omega
      · have hryS : G.rot f ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2
          ⟨hy1, fun h => he.vertexOf_ne (by rw [← G.vertexOf_rot f, h])⟩
        refine hgen ⟨_, hryS⟩ (Subtype.ext (coe_contractEdge_rot_of_eq_inv h2' hryS)) ?_
        exact hnotD (Or.inl (G.vertexOf_rot _)) (by
          rw [G.vertexOf_rot, hroot]; exact he.vertexOf_ne)
    · have hm : G.rot T.intervalEnd ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
        mem_compl_pair_iff.2 ⟨h1, h2'⟩
      exact hgen ⟨_, hm⟩ (Subtype.ext (coe_contractEdge_rot_of_mem hm)) hrend
  · -- the rotation enters the interval at its start
    rw [toCompl_of_mem (hc T.intervalStart_mem_darts)]
    have hstr := T.rot_symm_intervalStart_notMem
    have hgen : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H),
        (G.contractEdge f (he.leg_mem hG)).rot x = ⟨T.intervalStart, hc T.intervalStart_mem_darts⟩ →
        (x : H) ∉ T.darts →
        (G.contractEdge f (he.leg_mem hG)).rot.symm
          ⟨T.intervalStart, hc T.intervalStart_mem_darts⟩ ∉
          T.darts.image (toCompl f (G.inv f) x₀) := by
      intro x hx hxT h
      rw [← hx, Equiv.symm_apply_apply] at h
      obtain ⟨e, heT, hfe⟩ := mem_image.1 h
      have hval := congrArg Subtype.val hfe
      rw [coe_toCompl_of_mem (hc heT)] at hval
      exact hxT (hval ▸ heT)
    by_cases h1 : G.rot.symm T.intervalStart = f
    · have hσf : G.rot f = T.intervalStart := by rw [← h1, Equiv.apply_symm_apply]
      have hroot : T.root = G.vertexOf f := by rw [← ha1r, ← hσf, G.vertexOf_rot]
      have hk := h2 (Or.inl hroot)
      have hσfS : G.rot f ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := by
        rw [hσf]; exact hc T.intervalStart_mem_darts
      by_cases hz1 : G.rot (G.inv f) = G.inv f
      · have hx : G.rot (G.rot.symm f) = f := Equiv.apply_symm_apply _ _
        have hxS : G.rot.symm f ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := by
          refine mem_compl_pair_iff.2 ⟨fun h => ?_, fun h => he.vertexOf_ne ?_⟩
          · have h' := hx
            rw [h] at h'
            exact hfT (by rw [← h', hσf]; exact T.intervalStart_mem_darts)
          · rw [← h, ← G.vertexOf_rot (G.rot.symm f), hx]
        refine hgen ⟨_, hxS⟩ (Subtype.ext (by
          rwa [coe_contractEdge_rot_of_eq_of_eq (x := ⟨_, hxS⟩) hx hz1 hσfS])) ?_
        intro hxT
        have hxe := T.eq_intervalEnd hG hxT (by rwa [hx])
        have h3 := hfill (x := f) (by rw [← hxe, hx]) hσf
        rw [ha1r, hroot] at h3
        have h4 := hone hz1
        omega
      · have hx : G.rot (G.rot.symm (G.inv f)) = G.inv f := Equiv.apply_symm_apply _ _
        have hrz' : G.rot.symm (G.inv f) ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := by
          refine mem_compl_pair_iff.2 ⟨fun h => he.vertexOf_ne ?_, fun h => hz1 ?_⟩
          · have h' := G.vertexOf_rot (G.rot.symm (G.inv f))
            rw [hx, h] at h'
            exact h'.symm
          · conv_lhs => rw [← h]
            exact hx
        refine hgen ⟨_, hrz'⟩ (Subtype.ext (by
          rwa [coe_contractEdge_rot_of_eq_inv (x := ⟨_, hrz'⟩) hx hσfS])) ?_
        exact hnotD (Or.inr (by rw [← G.vertexOf_rot, hx])) (by
          rw [← G.vertexOf_rot, hx, hroot]; exact Ne.symm he.vertexOf_ne)
    by_cases h2' : G.rot.symm T.intervalStart = G.inv f
    · have hσf : G.rot (G.inv f) = T.intervalStart := by rw [← h2', Equiv.apply_symm_apply]
      have hroot : T.root = G.vertexOf (G.inv f) := by rw [← ha1r, ← hσf, G.vertexOf_rot]
      have hk := h2 (Or.inr hroot)
      have hσzS : G.rot (G.inv f) ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := by
        rw [hσf]; exact hc T.intervalStart_mem_darts
      by_cases hy1 : G.rot f = f
      · have hx : G.rot (G.rot.symm (G.inv f)) = G.inv f := Equiv.apply_symm_apply _ _
        have hxS : G.rot.symm (G.inv f) ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := by
          refine mem_compl_pair_iff.2 ⟨fun h => he.vertexOf_ne ?_, fun h => ?_⟩
          · have h' := G.vertexOf_rot (G.rot.symm (G.inv f))
            rw [hx, h] at h'
            exact h'.symm
          · have h' := hx
            rw [h] at h'
            exact hfT' (by rw [← h', hσf]; exact T.intervalStart_mem_darts)
        refine hgen ⟨_, hxS⟩ (Subtype.ext (by
          rwa [coe_contractEdge_rot_of_eq_inv_of_eq (x := ⟨_, hxS⟩) hx hy1 hσzS])) ?_
        intro hxT
        have hxe := T.eq_intervalEnd hG hxT (by rwa [hx])
        have h3 := hfill (x := G.inv f) (by rw [← hxe, hx]) hσf
        rw [ha1r, hroot] at h3
        have h4 := hone hy1
        omega
      · have hx : G.rot (G.rot.symm f) = f := Equiv.apply_symm_apply _ _
        have hry' : G.rot.symm f ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := by
          refine mem_compl_pair_iff.2 ⟨fun h => hy1 ?_, fun h => he.vertexOf_ne ?_⟩
          · conv_lhs => rw [← h]
            exact hx
          · rw [← h, ← G.vertexOf_rot (G.rot.symm f), hx]
        refine hgen ⟨_, hry'⟩ (Subtype.ext (by
          rwa [coe_contractEdge_rot_of_eq (x := ⟨_, hry'⟩) hx hσzS])) ?_
        exact hnotD (Or.inl (by rw [← G.vertexOf_rot, hx])) (by
          rw [← G.vertexOf_rot, hx, hroot]; exact he.vertexOf_ne)
    · have hmem : G.rot.symm T.intervalStart ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
        mem_compl_pair_iff.2 ⟨h1, h2'⟩
      refine hgen ⟨_, hmem⟩ (Subtype.ext (by
        rw [coe_contractEdge_rot_of_mem (x := ⟨_, hmem⟩) (by
          rw [Equiv.apply_symm_apply]; exact hc T.intervalStart_mem_darts),
          Equiv.apply_symm_apply])) hstr
  · rw [toCompl_of_mem (hc T.intervalStart_mem_darts), ← card_map (Embedding.subtype _)]
    by_cases hx : T.intervalStart ∈ G.vertexOf f ∪ G.vertexOf (G.inv f)
    · rw [map_vertexOf_contractEdge_of_mem hne hx]
      refine h2 ?_
      rcases mem_union.1 hx with h | h
      · exact Or.inl (by rw [T.root_eq_vertexOf_intervalStart, G.vertexOf_eq_of_mem h])
      · exact Or.inr (by rw [T.root_eq_vertexOf_intervalStart, G.vertexOf_eq_of_mem h])
    · rw [map_vertexOf_contractEdge_of_notMem hne hx, ← T.root_eq_vertexOf_intervalStart]
      exact T.intervalLength_lt_card
  · rw [toCompl_of_mem (hc he')]
    rfl

variable {𝒯 : Finset (G.RootedTree × Shade)} (h𝒯 : G.IsCollapsingFamily 𝒯)
  (hnl : (G.collapse 𝒯).IsNearlyLeafless)
  (hx : ∀ p ∈ 𝒯, G.vertexOf f ∉ p.1.nonRoot ∧ G.vertexOf (G.inv f) ∉ p.1.nonRoot)

include h𝒯 hnl hx

omit he h𝒯 hnl in
/-- The darts of the contracted edge are not darts of the trees. -/
private theorem contractOutside_notMem : f ∉ G.familyDarts 𝒯 ∧ G.inv f ∉ G.familyDarts 𝒯 := by
  have hinv := hG.inv_involutive
  have key : ∀ {e : H}, G.vertexOf e ∉ (𝒯.biUnion fun p => p.1.nonRoot) →
      G.vertexOf (G.inv e) ∉ (𝒯.biUnion fun p => p.1.nonRoot) → e ∉ G.familyDarts 𝒯 := by
    intro e h1 h2 h
    obtain ⟨p, hp, hep⟩ := mem_familyDarts.1 h
    rcases p.1.vertexOf_mem_or_eq_root hG hep with h' | h'
    · exact h1 (mem_biUnion.2 ⟨p, hp, h'⟩)
    · exact h2 (mem_biUnion.2 ⟨p, hp, p.1.vertexOf_inv_mem_nonRoot_of_mem_root hep
        (p.1.mem_root_iff.2 h')⟩)
  have hy : G.vertexOf f ∉ (𝒯.biUnion fun p => p.1.nonRoot) := fun h => by
    obtain ⟨p, hp, h⟩ := mem_biUnion.1 h; exact (hx p hp).1 h
  have hz : G.vertexOf (G.inv f) ∉ (𝒯.biUnion fun p => p.1.nonRoot) := fun h => by
    obtain ⟨p, hp, h⟩ := mem_biUnion.1 h; exact (hx p hp).2 h
  exact ⟨key hy hz, key hz (by rwa [hinv])⟩

/-- **Contracting an edge outside the trees**: the family is a collapsing family of the
contraction, whose collapse is the contraction of the collapse. -/
theorem exists_isomorphic_contractEdge_collapse :
    ∃ 𝒯' : Finset ((G.contractEdge f (he.leg_mem hG)).RootedTree × Shade),
      (G.contractEdge f (he.leg_mem hG)).IsCollapsingFamily 𝒯' ∧
      ∃ (f' : G.collapseDarts 𝒯) (he' : (G.collapse 𝒯).IsContractibleEdge f'),
        ((G.contractEdge f (he.leg_mem hG)).collapse 𝒯').Isomorphic
          ((G.collapse 𝒯).contractEdge f' (he'.leg_mem (h𝒯.moveEquivalent_collapse hG).1)) := by
  have hinv := hG.inv_involutive
  have hne := he.not_sameCycle
  obtain ⟨hfD, hfD'⟩ := contractOutside_notMem hG hx
  set X := G.collapse 𝒯 with hXdef
  have hX : X.IsPlabicGraph := (h𝒯.moveEquivalent_collapse hG).1
  have hfK : f ∈ G.collapseCore 𝒯 := Or.inl hfD
  have hfK' : G.inv f ∈ G.collapseCore 𝒯 := Or.inl hfD'
  set f' : G.collapseDarts 𝒯 := ⟨f, Or.inl hfK⟩ with hf'def
  have hif' : ((X.inv f' : G.collapseDarts 𝒯) : H) = G.inv f := coe_collapse_inv hG f'
  have hmap₁ : (X.vertexOf f').map (Embedding.subtype _) =
      (G.vertexOf f).filter (· ∈ G.collapseCore 𝒯) := map_collapse_vertexOf_of_mem hfK
  have hmap₂ : (X.vertexOf (X.inv f')).map (Embedding.subtype _) =
      (G.vertexOf (G.inv f)).filter (· ∈ G.collapseCore 𝒯) := by
    rw [map_collapse_vertexOf_of_mem (x := X.inv f') (by rwa [hif']), hif']
  have hint₁ : ¬X.IsBoundaryVertex (X.vertexOf f') := by
    rintro ⟨z, hz, hzB⟩
    apply he.not_isBoundaryVertex
    have : (z : H) ∈ (X.vertexOf f').map (Embedding.subtype _) := mem_map_of_mem _ hz
    rw [hmap₁] at this
    exact ⟨z, (mem_filter.1 this).1, mem_collapse_bdry.1 hzB⟩
  have hint₂ : ¬X.IsBoundaryVertex (X.vertexOf (X.inv f')) := by
    rintro ⟨z, hz, hzB⟩
    apply he.not_isBoundaryVertex_inv
    have : (z : H) ∈ (X.vertexOf (X.inv f')).map (Embedding.subtype _) := mem_map_of_mem _ hz
    rw [hmap₂] at this
    exact ⟨z, (mem_filter.1 this).1, mem_collapse_bdry.1 hzB⟩
  have hinvX := hX.inv_involutive
  have hX2 : 2 ≤ (X.vertexOf f').card := hnl.two_le_card_vertexOf hX hint₁ (by rwa [])
  have hX2' : 2 ≤ (X.vertexOf (X.inv f')).card :=
    hnl.two_le_card_vertexOf hX hint₂ (by rwa [hinvX])
  have hy2 : 2 ≤ (G.vertexOf f).card := by
    have := card_le_card (filter_subset (· ∈ G.collapseCore 𝒯) (G.vertexOf f))
    rw [← hmap₁, card_map] at this; omega
  have hz2 : 2 ≤ (G.vertexOf (G.inv f)).card := by
    have := card_le_card (filter_subset (· ∈ G.collapseCore 𝒯) (G.vertexOf (G.inv f)))
    rw [← hmap₂, card_map] at this; omega
  -- each endpoint keeps a dart other than the edge
  have hfree₁ : ∃ e ∈ G.vertexOf f, e ≠ f ∧ e ∉ G.familyDarts 𝒯 := by
    obtain ⟨e, he1, he2⟩ := exists_mem_ne hX2 f'
    have : (e : H) ∈ (G.vertexOf f).filter (· ∈ G.collapseCore 𝒯) := by
      rw [← hmap₁]; exact mem_map_of_mem _ he1
    obtain ⟨heY, heK⟩ := mem_filter.1 this
    refine ⟨e, heY, fun h => he2 (Subtype.ext h), fun h => ?_⟩
    rcases heK with h' | ⟨j, hj⟩
    · exact h' h
    · apply he.not_isBoundaryVertex
      rw [← G.vertexOf_eq_of_mem heY, hj]
      exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j)
  have hfree₂ : ∃ e ∈ G.vertexOf (G.inv f), e ≠ G.inv f ∧ e ∉ G.familyDarts 𝒯 := by
    obtain ⟨e, he1, he2⟩ := exists_mem_ne hX2' (X.inv f')
    have : (e : H) ∈ (G.vertexOf (G.inv f)).filter (· ∈ G.collapseCore 𝒯) := by
      rw [← hmap₂]; exact mem_map_of_mem _ he1
    obtain ⟨heY, heK⟩ := mem_filter.1 this
    refine ⟨e, heY, fun h => he2 (Subtype.ext (h.trans hif'.symm)), fun h => ?_⟩
    rcases heK with h' | ⟨j, hj⟩
    · exact h' h
    · apply he.not_isBoundaryVertex_inv
      rw [← G.vertexOf_eq_of_mem heY, hj]
      exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j)
  set x₀ : (({f, G.inv f} : Set H)ᶜ : Set H) := ⟨G.leg ⟨0, hG.one_le⟩, he.leg_mem hG _⟩
  have hemb := fun p (hp : p ∈ 𝒯) =>
    contractOutside_isEmbedding hG he x₀ (hx p hp).1 (hx p hp).2 fun h => by
      have hk := p.1.intervalLength_lt_card
      rcases h with h | h
      · rw [h] at hk; exact hk.trans_le (card_mergedVertex_ge he hz2)
      · rw [h] at hk; exact hk.trans_le (card_mergedVertex_ge' he hy2)
  have hGc : (G.contractEdge f (he.leg_mem hG)).IsPlabicGraph := hG.contractEdge he
  have hA := injOn_toCompl x₀
  have hDA : ∀ e ∈ G.familyDarts 𝒯, e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := fun e he' =>
    mem_compl_pair_iff.2 ⟨fun h => hfD (h ▸ he'), fun h => hfD' (h ▸ he')⟩
  have hsame : ∀ a c : H, a ∈ (({f, G.inv f} : Set H)ᶜ : Set H) →
      c ∈ (({f, G.inv f} : Set H)ᶜ : Set H) → G.rot.SameCycle a c →
      toCompl f (G.inv f) x₀ a ∈ (G.contractEdge f (he.leg_mem hG)).vertexOf
        (toCompl f (G.inv f) x₀ c) := fun a c ha hc h => by
    rw [RotationSystem.mem_vertexOf, toCompl_of_mem ha, toCompl_of_mem hc,
      sameCycle_contractEdge_rot_iff hne]
    exact Or.inl h.symm
  have hfree : ∀ p ∈ 𝒯, ∃ a ∈ (({f, G.inv f} : Set H)ᶜ : Set H), a ∉ G.familyDarts 𝒯 ∧
      toCompl f (G.inv f) x₀ a ∈ (G.contractEdge f (he.leg_mem hG)).vertexOf
        (toCompl f (G.inv f) x₀ p.1.intervalStart) := by
    intro p hp
    obtain ⟨a, ha, haq⟩ := h𝒯.exists_mem_root p hp
    have haD : a ∉ G.familyDarts 𝒯 := fun h => by
      obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
      exact haq r hr har
    have ha1S := hDA _ (mem_familyDarts.2 ⟨p, hp, p.1.intervalStart_mem_darts⟩)
    have hsc : G.rot.SameCycle p.1.intervalStart a := by
      rwa [← G.mem_vertexOf, ← p.1.root_eq_vertexOf_intervalStart]
    by_cases haS : a ∈ (({f, G.inv f} : Set H)ᶜ : Set H)
    · exact ⟨a, haS, haD, hsame _ _ haS ha1S hsc.symm⟩
    -- the free dart is an end of the edge: use a free dart of the other end
    have haf : a = f ∨ a = G.inv f := by
      by_contra h; exact haS (mem_compl_pair_iff.2 (not_or.1 h))
    rcases haf with rfl | rfl
    · obtain ⟨e, he1, he2, he3⟩ := hfree₂
      have heS : e ∈ (({a, G.inv a} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2
        ⟨fun h => he.vertexOf_ne (by rw [← G.vertexOf_eq_of_mem he1, h]), he2⟩
      refine ⟨e, heS, he3, ?_⟩
      rw [RotationSystem.mem_vertexOf, toCompl_of_mem heS, toCompl_of_mem ha1S,
        sameCycle_contractEdge_rot_iff hne]
      exact Or.inr (Or.inl ⟨hsc, ((G.mem_vertexOf).1 he1).symm⟩)
    · obtain ⟨e, he1, he2, he3⟩ := hfree₁
      have heS : e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2
        ⟨he2, fun h => he.vertexOf_ne (by rw [← G.vertexOf_eq_of_mem he1, h])⟩
      refine ⟨e, heS, he3, ?_⟩
      rw [RotationSystem.mem_vertexOf, toCompl_of_mem heS, toCompl_of_mem ha1S,
        sameCycle_contractEdge_rot_iff hne]
      exact Or.inr (Or.inr ⟨hsc, ((G.mem_vertexOf).1 he1).symm⟩)
  have hroot : ∀ p ∈ 𝒯, (G.contractEdge f (he.leg_mem hG)).IsBoundaryVertex
      ((G.contractEdge f (he.leg_mem hG)).vertexOf (toCompl f (G.inv f) x₀ p.1.intervalStart)) ↔
      G.IsBoundaryVertex p.1.root := fun p hp => by
    rw [isBoundaryVertex_vertexOf_contractEdge_iff he, coe_toCompl_of_mem (hDA _
      (mem_familyDarts.2 ⟨p, hp, p.1.intervalStart_mem_darts⟩)),
      ← p.1.root_eq_vertexOf_intervalStart]
  have h𝒯c := isCollapsingFamily_transportFamily hG hGc hemb h𝒯 hA hDA hroot hfree
  refine ⟨_, h𝒯c, f', ?_⟩
  have he' : X.IsContractibleEdge f' := by
    refine ⟨fun h => ?_, X.vertexOf_mem_internalVertices.2 hint₁,
      X.vertexOf_mem_internalVertices.2 hint₂, ?_⟩
    · have : f ∈ (G.vertexOf (G.inv f)).filter (· ∈ G.collapseCore 𝒯) := by
        rw [← hmap₂, ← h, hmap₁]; exact mem_filter.2 ⟨G.self_mem_vertexOf f, hfK⟩
      exact he.vertexOf_ne (G.vertexOf_eq_of_mem (mem_filter.1 this).1)
    · change G.collapseColour 𝒯 (X.inv f') = G.collapseColour 𝒯 f'
      rw [collapseColour_of_mem_collapseCore hG (by rwa [hif']),
        collapseColour_of_mem_collapseCore hG hfK, hif']
      exact he.colour_inv
  refine ⟨he', ?_⟩
  have hD : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H),
      x ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts
      (transportFamily hG hGc hemb) ↔ (x : H) ∈ G.familyDarts 𝒯 := by
    intro x
    rw [mem_familyDarts_transportFamily]
    constructor
    · rintro ⟨e, he1, rfl⟩
      rwa [coe_toCompl_of_mem (hDA e he1)]
    · intro h
      exact ⟨x, h, toCompl_val x⟩
  have hcol : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ transportFamily hG hGc hemb, G.leg i ∈ p₁.1.darts →
      (G.contractEdge f (he.leg_mem hG)).leg i ∈ p₂.1.darts → p₁.2 = p₂.2 := by
    intro i p₁ hp₁ p₂ hp₂ hi₁ hi₂
    obtain ⟨r, hr, hir, hrc⟩ := transportFamily_colour hG hGc hemb hA hDA (he.leg_mem hG i) hp₂
      (by rwa [toCompl_of_mem (he.leg_mem hG i)])
    rw [h𝒯.eq_of_mem_darts hG hp₁ hr hi₁ hir, hrc]
  have hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2 := fun i p₁ hp₁ p₂ hp₂ h₁ h₂ => by rw [h𝒯.eq_of_mem_darts hG hp₁ hp₂ h₁ h₂]
  have := isomorphic_collapse_cut_of_eq hG (contractEdge_eq_cutData hinv (he.leg_mem hG)) hGc hD
    hfD hfD' hcol hcol₁ f' (X.inv f') rfl hif' (he'.leg_mem hX)
  rw [contractEdge_eq_cutData hinvX]
  exact this

end ContractOutside

section FamilyDarts

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  {𝒯 : Finset (G.RootedTree × Shade)} {p₀ : G.RootedTree × Shade}

/-- A dart of a family lies in a chosen tree of it or in the rest of the family. -/
theorem mem_familyDarts_iff_mem_darts_or_mem_familyDarts_erase
    [DecidableEq (G.RootedTree × Shade)] (hp₀ : p₀ ∈ 𝒯) {y : H} :
    y ∈ G.familyDarts 𝒯 ↔ y ∈ p₀.1.darts ∨ y ∈ G.familyDarts (𝒯.erase p₀) := by
  constructor
  · intro h
    obtain ⟨q, hq, hyq⟩ := mem_familyDarts.1 h
    by_cases hqp : q = p₀
    · subst hqp
      exact Or.inl hyq
    · exact Or.inr (mem_familyDarts.2 ⟨q, mem_erase.2 ⟨hqp, hq⟩, hyq⟩)
  · rintro (h | h)
    · exact mem_familyDarts.2 ⟨p₀, hp₀, h⟩
    · obtain ⟨q, hq, hyq⟩ := mem_familyDarts.1 h
      exact mem_familyDarts.2 ⟨q, mem_of_mem_erase hq, hyq⟩

/-- Every root of a collapsing family has a dart outside the family. -/
theorem IsCollapsingFamily.exists_mem_root_notMem_familyDarts (h𝒯 : G.IsCollapsingFamily 𝒯)
    {q : G.RootedTree × Shade} (hq : q ∈ 𝒯) : ∃ a ∈ q.1.root, a ∉ G.familyDarts 𝒯 := by
  obtain ⟨a, ha, haq⟩ := h𝒯.exists_mem_root q hq
  exact ⟨a, ha, fun h => by
    obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
    exact haq r hr har⟩

/-- The darts of the other trees of a collapsing family avoid an edge of one of its trees. -/
theorem IsCollapsingFamily.mem_compl_pair_of_mem_familyDarts_erase
    [DecidableEq (G.RootedTree × Shade)] (hG : G.IsPlabicGraph) (h𝒯 : G.IsCollapsingFamily 𝒯)
    (hp₀ : p₀ ∈ 𝒯) {f : H} (hfD : f ∈ p₀.1.darts) (hifD : G.inv f ∈ p₀.1.darts)
    {e : H} (he : e ∈ G.familyDarts (𝒯.erase p₀)) :
    e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := by
  obtain ⟨q, hq, heq⟩ := mem_familyDarts.1 he
  have hdisj : Disjoint p₀.1.darts q.1.darts :=
    p₀.1.disjoint_darts hG (h𝒯.disjoint_nonRoot p₀ hp₀ q (mem_of_mem_erase hq)
      (ne_of_mem_erase hq).symm)
      (h𝒯.root_notMem_nonRoot q (mem_of_mem_erase hq) p₀ hp₀ (ne_of_mem_erase hq))
  refine mem_compl_pair_iff.2 ⟨fun h => ?_, fun h => ?_⟩
  · exact disjoint_left.1 hdisj hfD (h ▸ heq)
  · exact disjoint_left.1 hdisj hifD (h ▸ heq)

/-- No dart at a non-root vertex of a tree of a family lies in the core of its collapse. -/
theorem notMem_collapseCore_of_vertexOf_mem_nonRoot (hG : G.IsPlabicGraph) (hp₀ : p₀ ∈ 𝒯)
    {w : H} (hw : G.vertexOf w ∈ p₀.1.nonRoot) :
    ∀ x ∈ (G.vertexOf w : Set H), x ∉ G.collapseCore 𝒯 := by
  intro x hx'
  have hvx : G.vertexOf x = G.vertexOf w := G.vertexOf_eq_of_mem (mem_coe.1 hx')
  rintro (h | ⟨i, rfl⟩)
  · exact h (mem_familyDarts.2 ⟨p₀, hp₀, p₀.1.mem_darts_of_vertexOf_mem (hvx ▸ hw)⟩)
  · exact p₀.1.ne_leg_of_vertexOf_mem hG (hvx ▸ hw) i rfl

end FamilyDarts

/-! ### Contracting the edge of a thin internal root -/

section ContractRoot

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {f : H} (he : G.IsContractibleEdge f)
  {𝒯 : Finset (G.RootedTree × Shade)} (h𝒯 : G.IsCollapsingFamily 𝒯)
  (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1)
  {p₀ : G.RootedTree × Shade} (hp₀ : p₀ ∈ 𝒯) (hroot : p₀.1.root = G.vertexOf f)
  (hz : G.vertexOf (G.inv f) ∈ p₀.1.nonRoot)

include hG he h𝒯 hbr hp₀ hroot hz

open scoped Classical in
/-- **Contracting the edge of a thin root**: for a tree whose interval is the dart `f` at its
internal root `v(f)`, the tree with its root removed, moved to the merged vertex, replaces the tree
(or the tree is dropped when it has a single non-root vertex), and the collapse does not change. -/
theorem exists_collapse_contract_root :
    ∃ 𝒯' : Finset ((G.contractEdge f (he.leg_mem hG)).RootedTree × Shade),
      (G.contractEdge f (he.leg_mem hG)).IsCollapsingFamily 𝒯' ∧
      ((G.contractEdge f (he.leg_mem hG)).collapse 𝒯').Isomorphic (G.collapse 𝒯) := by
  have hinv := hG.inv_involutive
  have hne := he.not_sameCycle
  have hGc : (G.contractEdge f (he.leg_mem hG)).IsPlabicGraph := hG.contractEdge he
  set T₀ := p₀.1 with hT₀
  have h1 := hbr p₀ hp₀
  have hx : ¬G.IsBoundaryVertex T₀.root := by rw [hroot]; exact he.not_isBoundaryVertex
  have hifD : G.inv f ∈ T₀.darts := T₀.mem_darts_of_vertexOf_mem hz
  have hfD : f ∈ T₀.darts := hinv f ▸ T₀.inv_mem_darts hG hifD
  have hfr : f ∈ T₀.root := T₀.mem_root_iff.2 hroot.symm
  have ha : T₀.intervalStart = f :=
    (T₀.eq_intervalStart_of_intervalLength_eq_one h1 hfD hfr).symm
  have hy2 : 2 ≤ (G.vertexOf f).card := by
    have := T₀.intervalLength_lt_card; rw [h1, hroot] at this; omega
  have hyW : ∀ q ∈ 𝒯, G.vertexOf f ∉ q.1.nonRoot := fun q hq h => by
    by_cases hqp : q = p₀
    · subst hqp; exact T₀.root_notMem_nonRoot (hroot ▸ h)
    · exact h𝒯.root_notMem_nonRoot p₀ hp₀ q hq (Ne.symm hqp) (hroot ▸ h)
  have hzW : ∀ q ∈ 𝒯.erase p₀, G.vertexOf (G.inv f) ∉ q.1.nonRoot := fun q hq h =>
    disjoint_left.1 (h𝒯.disjoint_nonRoot p₀ hp₀ q (mem_of_mem_erase hq)
      (ne_of_mem_erase hq).symm) hz h
  have hdisj : ∀ q ∈ 𝒯.erase p₀, Disjoint T₀.darts q.1.darts := fun q hq =>
    T₀.disjoint_darts hG (h𝒯.disjoint_nonRoot p₀ hp₀ q (mem_of_mem_erase hq)
      (ne_of_mem_erase hq).symm)
      (h𝒯.root_notMem_nonRoot q (mem_of_mem_erase hq) p₀ hp₀ (ne_of_mem_erase hq))
  have hDA' : ∀ e ∈ G.familyDarts (𝒯.erase p₀), e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
    fun _ he' => h𝒯.mem_compl_pair_of_mem_familyDarts_erase hG hp₀ hfD hifD he'
  have hfreeD : ∀ q ∈ 𝒯, ∃ a ∈ q.1.root, a ∉ G.familyDarts 𝒯 := fun _ hq =>
    h𝒯.exists_mem_root_notMem_familyDarts hq
  have hfDf : f ∈ G.familyDarts 𝒯 := mem_familyDarts.2 ⟨p₀, hp₀, hfD⟩
  have hifDf : G.inv f ∈ G.familyDarts 𝒯 := mem_familyDarts.2 ⟨p₀, hp₀, hifD⟩
  have hnotDS : ∀ a, a ∉ G.familyDarts 𝒯 → a ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := fun a h =>
    mem_compl_pair_iff.2 ⟨fun h' => h (h' ▸ hfDf), fun h' => h (h' ▸ hifDf)⟩
  -- the other trees embed into the contraction
  set x₀ : (({f, G.inv f} : Set H)ᶜ : Set H) := ⟨G.leg ⟨0, hG.one_le⟩, he.leg_mem hG _⟩
  have hA := injOn_toCompl x₀
  have hM := card_mergedVertex_add_two hG he
  have hz1 : 1 ≤ (G.vertexOf (G.inv f)).card := card_pos.2 ⟨_, G.self_mem_vertexOf _⟩
  have hemb' : ∀ q ∈ 𝒯.erase p₀, q.1.IsEmbedding (G.contractEdge f (he.leg_mem hG))
      (toCompl f (G.inv f) x₀) := fun q hq =>
    contractOutside_isEmbedding hG he x₀ (hyW q (mem_of_mem_erase hq)) (hzW q hq) fun h => by
      rcases h with h | h
      · -- a root at `v(f)` has `f`, its interval and a free dart
        rw [hbr q (mem_of_mem_erase hq)]
        obtain ⟨g, hg, hgD⟩ := hfreeD q (mem_of_mem_erase hq)
        have hqa := q.1.intervalStart_mem_darts
        have hsub : ({f, q.1.intervalStart, g} : Finset H) ⊆ G.vertexOf f := by
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact G.self_mem_vertexOf _
          · rw [← h]; exact q.1.intervalStart_mem_root
          · rwa [← h]
        have hfa : f ≠ q.1.intervalStart := fun h' =>
          disjoint_left.1 (hdisj q hq) hfD (h' ▸ hqa)
        have hfg : f ≠ g := fun h' => hgD (h' ▸ hfDf)
        have hag : q.1.intervalStart ≠ g := fun h' =>
          hgD (h' ▸ mem_familyDarts.2 ⟨q, mem_of_mem_erase hq, hqa⟩)
        have := card_le_card hsub
        rw [card_insert_of_notMem (by simp [hfa, hfg]),
          card_pair hag] at this
        omega
      · exact absurd (h ▸ hz) (h𝒯.root_notMem_nonRoot q (mem_of_mem_erase hq) p₀ hp₀
          (ne_of_mem_erase hq))
  have hroot' : ∀ q ∈ 𝒯.erase p₀, (G.contractEdge f (he.leg_mem hG)).IsBoundaryVertex
      ((G.contractEdge f (he.leg_mem hG)).vertexOf (toCompl f (G.inv f) x₀ q.1.intervalStart)) ↔
      G.IsBoundaryVertex q.1.root := fun q hq => by
    rw [isBoundaryVertex_vertexOf_contractEdge_iff he, coe_toCompl_of_mem (hDA' _
      (mem_familyDarts.2 ⟨q, hq, q.1.intervalStart_mem_darts⟩)),
      ← q.1.root_eq_vertexOf_intervalStart]
  have hfree : ∀ q ∈ 𝒯.erase p₀, ∃ a ∈ (({f, G.inv f} : Set H)ᶜ : Set H),
      a ∉ G.familyDarts 𝒯 ∧ toCompl f (G.inv f) x₀ a ∈ (G.contractEdge f (he.leg_mem hG)).vertexOf
        (toCompl f (G.inv f) x₀ q.1.intervalStart) := fun q hq => by
    obtain ⟨a, ha', haD⟩ := hfreeD q (mem_of_mem_erase hq)
    have haS := hnotDS a haD
    have ha1S := hDA' _ (mem_familyDarts.2 ⟨q, hq, q.1.intervalStart_mem_darts⟩)
    refine ⟨a, haS, haD, ?_⟩
    rw [RotationSystem.mem_vertexOf, toCompl_of_mem haS, toCompl_of_mem ha1S,
      sameCycle_contractEdge_rot_iff hne]
    exact Or.inl (by rwa [← G.mem_vertexOf, ← q.1.root_eq_vertexOf_intervalStart])
  have hQ : ∀ x, G.rot x ∈ (G.vertexOf (G.inv f) : Set H) ↔
      x ∈ (G.vertexOf (G.inv f) : Set H) := fun x => by
    simp only [mem_coe, RotationSystem.mem_vertexOf, sameCycle_apply_right]
  have hQK : ∀ x ∈ (G.vertexOf (G.inv f) : Set H), x ∉ G.collapseCore 𝒯 :=
    notMem_collapseCore_of_vertexOf_mem_nonRoot hG hp₀ hz
  have hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2 := fun i p₁ hp₁ p₂ hp₂ h₁ h₂ => by rw [h𝒯.eq_of_mem_darts hG hp₁ hp₂ h₁ h₂]
  have hcolT : ∀ i, ∀ p₁ ∈ 𝒯, ∀ q' ∈ transportFamily hG hGc hemb', G.leg i ∈ p₁.1.darts →
      (G.contractEdge f (he.leg_mem hG)).leg i ∈ q'.1.darts → p₁.2 = q'.2 := by
    intro i p₁ hp₁ q' hq' h₁ h₂
    obtain ⟨r, hr, hir, hrc⟩ := transportFamily_colour hG hGc hemb' hA hDA' (he.leg_mem hG i) hq'
      (by rwa [toCompl_of_mem (he.leg_mem hG i)])
    rw [h𝒯.eq_of_mem_darts hG hp₁ (mem_of_mem_erase hr) h₁ hir, hrc]
  have hDo : ∀ y : (({f, G.inv f} : Set H)ᶜ : Set H), (∃ e ∈ G.familyDarts (𝒯.erase p₀),
      toCompl f (G.inv f) x₀ e = y) ↔ (y : H) ∈ G.familyDarts (𝒯.erase p₀) := fun y =>
    ⟨by rintro ⟨e, he', rfl⟩; rwa [coe_toCompl_of_mem (hDA' e he')], fun h => ⟨y, h, toCompl_val y⟩⟩
  have hfam : ∀ y : H, y ∈ G.familyDarts 𝒯 ↔ y ∈ T₀.darts ∨ y ∈ G.familyDarts (𝒯.erase p₀) :=
    fun _ => mem_familyDarts_iff_mem_darts_or_mem_familyDarts_erase hp₀
  have hcut := contractEdge_eq_cutData hinv (he.leg_mem hG)
  by_cases hne' : (T₀.nonRoot.erase (G.vertexOf (G.inv T₀.intervalStart))).Nonempty
  · -- the tree with its root removed, at the merged vertex
    set Tz := rootRemovalTree hG T₀ h1 hne' with hTz
    have hDz := fun e => RootRemoval.darts_iff hG T₀ h1 hne' (e := e)
    have hzr : Tz.root = G.vertexOf (G.inv f) := by rw [RootRemoval.root_eq, ha]
    have hz2 : 2 ≤ (G.vertexOf (G.inv f)).card := by
      have := Tz.intervalLength_lt_card
      have := Tz.one_le_intervalLength
      rw [hzr] at *
      omega
    have hembz : Tz.IsEmbedding (G.contractEdge f (he.leg_mem hG)) (toCompl f (G.inv f) x₀) :=
      contractOutside_isEmbedding hG he x₀ (by
        rw [RootRemoval.nonRoot_eq]; exact fun h => hyW p₀ hp₀ (mem_of_mem_erase h)) (by
        rw [RootRemoval.nonRoot_eq, ha]; exact notMem_erase _ _) fun _ => by
        have := Tz.intervalLength_lt_card
        rw [hzr] at this
        exact this.trans_le (card_mergedVertex_ge' he hy2)
    have hDzS : ∀ e ∈ Tz.darts, e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := fun e he' => by
      obtain ⟨-, h₁, h₂⟩ := (hDz e).1 he'
      rw [ha] at h₁ h₂
      exact mem_compl_pair_iff.2 ⟨h₁, h₂⟩
    set T' := hembz.tree hG hGc with hT'def
    have hc := h𝒯.isCollapsibleOfColour p₀ hp₀
    have hcolr : ∀ e ∈ T₀.root, G.colour e = p₀.2 := by
      rcases hc.root_cases with ⟨-, hcol⟩ | ⟨hb, -⟩
      · exact hcol
      · exact absurd hb hx
    -- `Tz` is collapsible of the colour of `T₀`
    have hTz : Tz.IsCollapsibleOfColour p₀.2 := by
      have hloc : PlabicGraph.IsLocalMove .m2 ⟨_, T₀.plabicData, hc.isPlabicGraph⟩
          ⟨_, Tz.plabicData, Tz.isPlabicGraph_plabicData hG⟩ :=
        Or.inl ⟨RootRemoval.dartGBar T₀ hx, RootRemoval.isBivalentRemovable_dartGBar hG T₀ hx h1,
          (RootRemoval.plabicData_isomorphic hG T₀ hx h1 hne').symm⟩
      refine ⟨Tz.isPlabicGraph_plabicData hG,
        (PlabicGraph.MoveEquivalent.of_isLocalMove (by simp) hloc).symm.trans hc.moveEquivalent,
        Or.inl ⟨RootRemoval.not_isBoundaryVertex_root hG T₀ h1 hne', fun e he' => ?_⟩⟩
      rw [hzr] at he'
      rw [hG.colour_eq_of_mem_vertexOf he.not_isBoundaryVertex_inv he', he.colour_inv]
      exact hcolr f hfr
    have hstartS := hDzS _ Tz.intervalStart_mem_darts
    have hv : (G.contractEdge f (he.leg_mem hG)).IsBoundaryVertex
        ((G.contractEdge f (he.leg_mem hG)).vertexOf (toCompl f (G.inv f) x₀ Tz.intervalStart)) ↔
        G.IsBoundaryVertex Tz.root := by
      rw [isBoundaryVertex_vertexOf_contractEdge_iff he, coe_toCompl_of_mem hstartS,
        ← Tz.root_eq_vertexOf_intervalStart]
    have hT' : T'.IsCollapsibleOfColour p₀.2 := hembz.isCollapsibleOfColour hG hGc hTz hv
    have hT'D : ∀ y ∈ T'.darts, ∃ e ∈ T₀.darts, e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) ∧
        toCompl f (G.inv f) x₀ e = y := fun y hy => by
      rw [hT'def, hembz.tree_darts hG hGc] at hy
      obtain ⟨e, he', rfl⟩ := mem_image.1 hy
      exact ⟨e, ((hDz e).1 he').1, hDzS e he', rfl⟩
    have hT'free : ∃ a ∈ (({f, G.inv f} : Set H)ᶜ : Set H), a ∉ G.familyDarts 𝒯 ∧
        toCompl f (G.inv f) x₀ a ∈ T'.root := by
      obtain ⟨a, ha', haD⟩ := hfreeD p₀ hp₀
      have haS := hnotDS a haD
      refine ⟨a, haS, haD, ?_⟩
      rw [hT'def, hembz.tree_root hG hGc, RotationSystem.mem_vertexOf, toCompl_of_mem haS,
        toCompl_of_mem hstartS, sameCycle_contractEdge_rot_iff hne]
      have h1' : Tz.intervalStart ∈ G.vertexOf (G.inv f) := hzr ▸ Tz.intervalStart_mem_root
      have h2' : a ∈ G.vertexOf f := hroot ▸ ha'
      exact Or.inr (Or.inr ⟨((G.mem_vertexOf).1 h1').symm, ((G.mem_vertexOf).1 h2').symm⟩)
    have h𝒯' := isCollapsingFamily_insert_transportFamily hG hGc h𝒯 hp₀ hemb' hA hDA' hroot'
      hfree hT' hT'D hT'free
    refine ⟨_, h𝒯', ?_⟩
    have hD : ∀ y : (({f, G.inv f} : Set H)ᶜ : Set H),
        y ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts
        (insert (T', p₀.2) (transportFamily hG hGc hemb')) ↔ (y : H) ∈ G.familyDarts 𝒯 := by
      intro y
      rw [mem_familyDarts_insert_transportFamily, hDo, hfam, hT'def, hembz.tree_darts hG hGc]
      refine or_congr ?_ Iff.rfl
      constructor
      · intro h
        obtain ⟨e, he', hey⟩ := mem_image.1 h
        rw [← hey, coe_toCompl_of_mem (hDzS e he')]
        exact ((hDz e).1 he').1
      · intro h
        have hy := mem_compl_pair_iff.1 y.2
        refine mem_image.2 ⟨y, (hDz _).2 ⟨h, ?_, ?_⟩, toCompl_val y⟩
        · rw [ha]; exact hy.1
        · rw [ha]; exact hy.2
    have hcol : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ insert (T', p₀.2) (transportFamily hG hGc hemb'),
        G.leg i ∈ p₁.1.darts → (G.contractEdge f (he.leg_mem hG)).leg i ∈ p₂.1.darts →
        p₁.2 = p₂.2 := by
      intro i p₁ hp₁ p₂ hp₂ h₁ h₂
      rcases mem_insert.1 hp₂ with rfl | hp₂
      · obtain ⟨e, he', heS, hey⟩ := hT'D _ h₂
        have : e = G.leg i := by
          have := congrArg Subtype.val hey
          rwa [coe_toCompl_of_mem heS] at this
        subst this
        rw [h𝒯.eq_of_mem_darts hG hp₁ hp₀ h₁ he']
      · exact hcolT i p₁ hp₁ p₂ hp₂ h₁ h₂
    exact isomorphic_collapse_of_cut hG hcut hGc hD hfDf hifDf _ hQ hQK
      (Or.inr (G.self_mem_vertexOf _)) hcol hcol₁
  · -- the tree is the single edge `{f, f̄}` and is dropped
    have hW1 : T₀.nonRoot = {G.vertexOf (G.inv f)} := by
      rw [ha, not_nonempty_iff_eq_empty] at hne'
      ext w
      rw [mem_singleton]
      constructor
      · intro hw
        by_contra h
        have : w ∈ T₀.nonRoot.erase (G.vertexOf (G.inv f)) := mem_erase.2 ⟨h, hw⟩
        rw [hne'] at this
        exact absurd this (notMem_empty w)
      · rintro rfl; exact hz
    have hD₀ : ∀ y ∈ T₀.darts, y = f ∨ y = G.inv f := by
      have hcard := T₀.card_darts hG
      rw [hW1, card_singleton] at hcard
      have hsub : ({f, G.inv f} : Finset H) ⊆ T₀.darts := by
        intro y hy
        rcases mem_insert.1 hy with rfl | hy
        · exact hfD
        · rwa [mem_singleton.1 hy]
      have heq := eq_of_subset_of_card_le hsub (by rw [hcard, card_pair (hG.inv_ne f).symm])
      intro y hy
      rw [← heq] at hy
      simpa using hy
    have h𝒯e := h𝒯.subset (erase_subset p₀ 𝒯)
    have h𝒯' := isCollapsingFamily_transportFamily hG hGc hemb' h𝒯e hA hDA' hroot' (fun q hq => by
      obtain ⟨a, haS, haD, hav⟩ := hfree q hq
      exact ⟨a, haS, fun h => haD ((hfam a).2 (Or.inr h)), hav⟩)
    refine ⟨_, h𝒯', ?_⟩
    have hD : ∀ y : (({f, G.inv f} : Set H)ᶜ : Set H),
        y ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts
        (transportFamily hG hGc hemb') ↔ (y : H) ∈ G.familyDarts 𝒯 := by
      intro y
      rw [mem_familyDarts_transportFamily, hDo, hfam]
      refine ⟨Or.inr, fun h => h.resolve_left fun h' => ?_⟩
      have hy := mem_compl_pair_iff.1 y.2
      rcases hD₀ _ h' with h'' | h''
      · exact hy.1 h''
      · exact hy.2 h''
    exact isomorphic_collapse_of_cut hG hcut hGc hD hfDf hifDf _ hQ hQK
      (Or.inr (G.self_mem_vertexOf _)) hcolT hcol₁

end ContractRoot

/-! ### Contracting an edge of a tree -/

section ContractTree

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- The vertex of the contraction along `{f, f̄}` corresponding to a vertex `w` of `G`: the merged
vertex if `w` is an endpoint of the edge, and `w` otherwise. -/
def contractV (f : H) (G : PlabicData H b) (w : Finset H) :
    Finset (({f, G.inv f} : Set H)ᶜ : Set H) :=
  (if f ∈ w ∨ G.inv f ∈ w then G.mergedVertex f else w).subtype
    (· ∈ (({f, G.inv f} : Set H)ᶜ : Set H))

variable (hG : G.IsPlabicGraph) {f : H} (he : G.IsContractibleEdge f)

/-- A dart lies at an endpoint iff its vertex is one of the endpoints. -/
theorem contractV_cond_iff (x : H) :
    (f ∈ G.vertexOf x ∨ G.inv f ∈ G.vertexOf x) ↔ x ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) := by
  rw [mem_union]
  refine or_congr ?_ ?_ <;> constructor <;> intro h <;>
    rw [G.vertexOf_eq_of_mem h] <;> exact G.self_mem_vertexOf _

include hG he in
/-- The vertices of the contraction are the images of the vertices of `G`. -/
theorem contractEdge_vertexOf_eq (x : (({f, G.inv f} : Set H)ᶜ : Set H)) :
    (G.contractEdge f (he.leg_mem hG)).vertexOf x = contractV f G (G.vertexOf x) := by
  have hne := he.not_sameCycle
  apply map_injective (Embedding.subtype (· ∈ (({f, G.inv f} : Set H)ᶜ : Set H)))
  rw [contractV, subtype_map]
  by_cases hx : (x : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f)
  · rw [if_pos ((contractV_cond_iff (G := G) (f := f) x).2 hx),
      map_vertexOf_contractEdge_of_mem hne hx]
    exact (filter_true_of_mem fun y hy => mem_compl_pair_iff.2 (mem_mergedVertex.1 hy).2).symm
  · rw [if_neg (mt (contractV_cond_iff (G := G) (f := f) x).1 hx),
      map_vertexOf_contractEdge_of_notMem hne hx]
    refine (filter_true_of_mem fun y hy => mem_compl_pair_of_notMem fun h => hx ?_).symm
    rwa [← contractV_cond_iff, ← G.vertexOf_eq_of_mem hy, contractV_cond_iff]

/-- `contractV` identifies the two endpoints and nothing else. -/
private theorem contractV_injOn {w w' : Finset H} (hw : w ∈ G.vertices) (hw' : w' ∈ G.vertices)
    (h : contractV f G w = contractV f G w') :
    w = w' ∨ ((w = G.vertexOf f ∨ w = G.vertexOf (G.inv f)) ∧
      (w' = G.vertexOf f ∨ w' = G.vertexOf (G.inv f))) := by
  obtain ⟨e, rfl⟩ := G.mem_vertices.1 hw
  obtain ⟨e', rfl⟩ := G.mem_vertices.1 hw'
  have key : ∀ x, (f ∈ G.vertexOf x ∨ G.inv f ∈ G.vertexOf x) ↔
      (G.vertexOf x = G.vertexOf f ∨ G.vertexOf x = G.vertexOf (G.inv f)) := fun x => by
    rw [contractV_cond_iff, mem_union]
    refine or_congr ⟨G.vertexOf_eq_of_mem, fun h => ?_⟩ ⟨G.vertexOf_eq_of_mem, fun h => ?_⟩ <;>
      rw [← h] <;> exact G.self_mem_vertexOf x
  -- a dart at a vertex which is not an endpoint lies in `H'`
  have hS : ∀ x, ¬(f ∈ G.vertexOf x ∨ G.inv f ∈ G.vertexOf x) →
      x ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := fun x hx =>
    mem_compl_pair_of_notMem (mt (contractV_cond_iff x).2 hx)
  by_cases h₁ : f ∈ G.vertexOf e ∨ G.inv f ∈ G.vertexOf e <;>
    by_cases h₂ : f ∈ G.vertexOf e' ∨ G.inv f ∈ G.vertexOf e'
  · exact Or.inr ⟨(key e).1 h₁, (key e').1 h₂⟩
  · exfalso
    have : (⟨e', hS e' h₂⟩ : (({f, G.inv f} : Set H)ᶜ : Set H)) ∈ contractV f G (G.vertexOf e) := by
      rw [h, contractV, mem_subtype, if_neg h₂]; exact G.self_mem_vertexOf e'
    rw [contractV, mem_subtype, if_pos h₁, mem_mergedVertex] at this
    exact h₂ ((contractV_cond_iff e').2 (mem_union.2 this.1))
  · exfalso
    have : (⟨e, hS e h₁⟩ : (({f, G.inv f} : Set H)ᶜ : Set H)) ∈ contractV f G (G.vertexOf e') := by
      rw [← h, contractV, mem_subtype, if_neg h₁]; exact G.self_mem_vertexOf e
    rw [contractV, mem_subtype, if_pos h₂, mem_mergedVertex] at this
    exact h₁ ((contractV_cond_iff e).2 (mem_union.2 this.1))
  · left
    have : (⟨e, hS e h₁⟩ : (({f, G.inv f} : Set H)ᶜ : Set H)) ∈ contractV f G (G.vertexOf e') := by
      rw [← h, contractV, mem_subtype, if_neg h₁]; exact G.self_mem_vertexOf e
    rw [contractV, mem_subtype, if_neg h₂] at this
    exact (G.vertexOf_eq_of_mem this)

include hG he in
/-- Each vertex of `G` gives a vertex of the contraction, internal iff the vertex is. -/
private theorem exists_contractV_eq {w : Finset H} (hw : w ∈ G.vertices) :
    ∃ x : (({f, G.inv f} : Set H)ᶜ : Set H),
      contractV f G w = (G.contractEdge f (he.leg_mem hG)).vertexOf x ∧
      (G.IsBoundaryVertex (G.vertexOf x) ↔ G.IsBoundaryVertex w) := by
  obtain ⟨e, rfl⟩ := G.mem_vertices.1 hw
  by_cases h : f ∈ G.vertexOf e ∨ G.inv f ∈ G.vertexOf e
  · obtain ⟨m, hm⟩ := mergedVertex_nonempty hG he
    have hmS : m ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
      mem_compl_pair_iff.2 (mem_mergedVertex.1 hm).2
    have hmu : m ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) := mem_union.2 (mem_mergedVertex.1 hm).1
    refine ⟨⟨m, hmS⟩, ?_, iff_of_false (fun hb => he.notMem_of_isBoundaryVertex hb hmu)
      (fun hb => he.notMem_of_isBoundaryVertex hb ((contractV_cond_iff e).1 h))⟩
    rw [contractEdge_vertexOf_eq hG he, contractV, contractV, if_pos h,
      if_pos ((contractV_cond_iff m).2 hmu)]
  · refine ⟨⟨e, mem_compl_pair_of_notMem (mt (contractV_cond_iff e).2 h)⟩, ?_, Iff.rfl⟩
    rw [contractEdge_vertexOf_eq hG he]

variable (T : G.RootedTree) (hy : G.vertexOf f ∈ T.nonRoot) (hz : G.vertexOf (G.inv f) ∈ T.nonRoot)

include hG he hy hz

namespace ContractTree

omit hG he in
/-- The root of `T` is neither endpoint of the edge `{f, f̄}`. -/
theorem root_ne : T.root ≠ G.vertexOf f ∧ T.root ≠ G.vertexOf (G.inv f) :=
  ⟨fun h => T.root_notMem_nonRoot (h ▸ hy), fun h => T.root_notMem_nonRoot (h ▸ hz)⟩

omit hG he in
/-- The darts at the root lie in `H'`. -/
theorem mem_compl_of_mem_root {e : H} (he' : e ∈ T.root) :
    e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := by
  have hr := root_ne T hy hz
  refine mem_compl_pair_of_notMem fun h => ?_
  rcases mem_union.1 h with h | h
  · exact hr.1 (by rw [← T.mem_root_iff.1 he', G.vertexOf_eq_of_mem h])
  · exact hr.2 (by rw [← T.mem_root_iff.1 he', G.vertexOf_eq_of_mem h])

/-- The image of the root of `T` in the contraction is the vertex of the first dart of the interval
of `T`. -/
theorem contractV_root : contractV f G T.root =
    (G.contractEdge f (he.leg_mem hG)).vertexOf
      ⟨T.intervalStart, mem_compl_of_mem_root T hy hz T.intervalStart_mem_root⟩ := by
  rw [contractEdge_vertexOf_eq hG he, ← T.root_eq_vertexOf_intervalStart]

/-- A dart `x` of the contraction lies at the image of a non-root vertex of `T` iff its vertex in
`G` is a non-root vertex of `T`. -/
theorem mem_image_iff (x : (({f, G.inv f} : Set H)ᶜ : Set H)) :
    (G.contractEdge f (he.leg_mem hG)).vertexOf x ∈ T.nonRoot.image (contractV f G) ↔
      G.vertexOf x ∈ T.nonRoot := by
  rw [contractEdge_vertexOf_eq hG he, mem_image]
  constructor
  · rintro ⟨w, hw, hwx⟩
    rcases contractV_injOn (G.mem_internalVertices.1 (T.nonRoot_subset hw)).1
      (G.vertexOf_mem_vertices _) hwx with h | ⟨-, h | h⟩
    · rwa [← h]
    · rwa [h]
    · rwa [h]
  · intro h
    exact ⟨_, h, rfl⟩

/-- A dart `x` of the contraction is a dart of the tree on the image of the non-root vertices of
`T` iff it is a dart of `T`. -/
theorem mem_treeDarts_iff (x : (({f, G.inv f} : Set H)ᶜ : Set H)) :
    x ∈ (G.contractEdge f (he.leg_mem hG)).treeDarts (T.nonRoot.image (contractV f G)) ↔
      (x : H) ∈ T.darts := by
  have hinv := hG.inv_involutive
  have hix : G.inv x ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
    (apply_mem_compl_pair_iff hinv f x).2 x.2
  have hcinv : (G.contractEdge f (he.leg_mem hG)).inv x = ⟨G.inv x, hix⟩ :=
    Subtype.ext (coe_contractEdge_inv hinv x)
  rw [mem_treeDarts, mem_treeDarts, mem_contractEdge_bdry, mem_image_iff hG he T hy hz, hcinv,
    mem_image_iff hG he T hy hz]

end ContractTree

/-- **The tree with the edge `{f, f̄}` contracted**, for an edge joining two non-root vertices of
`T`: a rooted tree of the contraction with the same root, whose non-root vertices are those of `T`
with the two endpoints merged. -/
noncomputable def contractTree : (G.contractEdge f (he.leg_mem hG)).RootedTree :=
  have hinv := hG.inv_involutive
  have hGc : (G.contractEdge f (he.leg_mem hG)).IsPlabicGraph := hG.contractEdge he
  have hD := ContractTree.mem_treeDarts_iff hG he T hy hz
  have hmem := ContractTree.mem_image_iff hG he T hy hz
  have hr := ContractTree.root_ne T hy hz
  have hrS := fun {e} (h : e ∈ T.root) => ContractTree.mem_compl_of_mem_root T hy hz h
  have hroot := ContractTree.contractV_root hG he T hy hz
  -- the rotation at the root is that of `G`
  have hrotS : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H), (x : H) ∈ T.root →
      G.rot x ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := fun x hx =>
    hrS (T.mem_root_iff.2 (by rw [G.vertexOf_rot]; exact T.mem_root_iff.1 hx))
  have hrot : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H), (x : H) ∈ T.root →
      (((G.contractEdge f (he.leg_mem hG)).rot x : (({f, G.inv f} : Set H)ᶜ : Set H)) : H) =
        G.rot x := fun x hx => coe_contractEdge_rot_of_mem (hrotS x hx)
  have hpow : ∀ (n : ℕ) (x : (({f, G.inv f} : Set H)ᶜ : Set H)), (x : H) ∈ T.root →
      ((((G.contractEdge f (he.leg_mem hG)).rot ^ n) x : (({f, G.inv f} : Set H)ᶜ : Set H)) : H) =
        (G.rot ^ n) x := by
    intro n
    induction n with
    | zero => intro x _; rfl
    | succ n ih =>
      intro x hx
      have hn : ((G.contractEdge f (he.leg_mem hG)).rot ^ n) x ∈
          ({y | (y : H) ∈ T.root} : Set (({f, G.inv f} : Set H)ᶜ : Set H)) := by
        change ((((G.contractEdge f (he.leg_mem hG)).rot ^ n) x : _) : H) ∈ T.root
        rw [ih x hx, T.mem_root_iff, G.vertexOf_pow_apply, T.mem_root_iff.1 hx]
      rw [pow_succ', Perm.mul_apply, hrot _ hn, ih x hx, pow_succ', Perm.mul_apply]
  { root := contractV f G T.root
    nonRoot := T.nonRoot.image (contractV f G)
    root_mem_vertices := by
      rw [hroot]; exact (G.contractEdge f (he.leg_mem hG)).vertexOf_mem_vertices _
    nonRoot_nonempty := T.nonRoot_nonempty.image _
    nonRoot_subset := by
      intro w' hw'
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hw'
      have hw₀ := G.mem_internalVertices.1 (T.nonRoot_subset hw)
      obtain ⟨x, hx, hxb⟩ := exists_contractV_eq hG he hw₀.1
      rw [hx]
      refine (G.contractEdge f (he.leg_mem hG)).vertexOf_mem_internalVertices.2 ?_
      rw [isBoundaryVertex_vertexOf_contractEdge_iff he, hxb]
      exact hw₀.2
    root_notMem_nonRoot := by
      intro h
      obtain ⟨w, hw, hwr⟩ := mem_image.1 h
      rcases contractV_injOn (G.mem_internalVertices.1 (T.nonRoot_subset hw)).1
        T.root_mem_vertices hwr with h' | ⟨-, h' | h'⟩
      · exact T.root_notMem_nonRoot (h' ▸ hw)
      · exact hr.1 h'
      · exact hr.2 h'
    vertexOf_inv_mem := by
      intro x hx
      have hxD : (x : H) ∈ T.darts := T.mem_darts_of_vertexOf_mem ((hmem x).1 hx)
      have hiD : ((G.contractEdge f (he.leg_mem hG)).inv x : H) ∈ T.darts :=
        (hD _).1 (inv_mem_treeDarts' hGc ((hD x).2 hxD))
      rw [contractEdge_vertexOf_eq hG he]
      rcases T.vertexOf_mem_or_eq_root hG hiD with h | h
      · exact mem_insert_of_mem (mem_image_of_mem _ h)
      · rw [h]; exact mem_insert_self _ _
    exists_interval := by
      refine ⟨⟨T.intervalStart, hrS T.intervalStart_mem_root⟩, ?_, T.intervalLength,
        T.one_le_intervalLength, ?_, fun e he' => ?_, ?_⟩
      · rw [hroot]; exact (G.contractEdge f (he.leg_mem hG)).self_mem_vertexOf _
      · rw [contractV, if_neg (fun h => by
          rcases h with h | h
          · exact hr.1 (T.mem_root_iff.1 h).symm
          · exact hr.2 (T.mem_root_iff.1 h).symm),
          card_subtype, filter_true_of_mem fun e he' => hrS he']
        exact T.intervalLength_lt_card
      · have he'r : (e : H) ∈ T.root := by
          rw [contractV, mem_subtype, if_neg (fun h => by
            rcases h with h | h
            · exact hr.1 (T.mem_root_iff.1 h).symm
            · exact hr.2 (T.mem_root_iff.1 h).symm)] at he'
          exact he'
        rw [hD, T.mem_darts_iff_of_mem_root he'r]
        refine exists_congr fun j => and_congr Iff.rfl ?_
        rw [Subtype.ext_iff, hpow j _ T.intervalStart_mem_root]
      · have hσ : (G.contractEdge f (he.leg_mem hG)).rot
            ⟨G.rot.symm T.intervalStart, hrS (T.mem_root_iff.2 (by
              rw [← G.vertexOf_rot, Equiv.apply_symm_apply, ← T.root_eq_vertexOf_intervalStart]))⟩ =
            ⟨T.intervalStart, hrS T.intervalStart_mem_root⟩ := by
          apply Subtype.ext
          rw [hrot _ (T.mem_root_iff.2 (by
            rw [← G.vertexOf_rot, Equiv.apply_symm_apply, ← T.root_eq_vertexOf_intervalStart]))]
          exact Equiv.apply_symm_apply _ _
        rw [← hσ, Equiv.symm_apply_apply, hD]
        exact T.rot_symm_intervalStart_notMem
    card_image_edgeOf := by
      set D' := (G.contractEdge f (he.leg_mem hG)).treeDarts (T.nonRoot.image (contractV f G))
      have h1 := (G.contractEdge f (he.leg_mem hG)).card_eq_two_mul_card_image_edgeOf
        hGc.inv_involutive hGc.inv_ne (S := D') fun y hy => inv_mem_treeDarts' hGc hy
      have hfD : f ∈ T.darts := T.mem_darts_of_vertexOf_mem hy
      have hifD : G.inv f ∈ T.darts := T.mem_darts_of_vertexOf_mem hz
      have h2 : D'.map (Embedding.subtype _) = (T.darts.erase f).erase (G.inv f) := by
        ext e
        simp only [mem_map, Embedding.coe_subtype, mem_erase]
        constructor
        · rintro ⟨y, hy', rfl⟩
          have := mem_compl_pair_iff.1 y.2
          exact ⟨this.2, this.1, (hD y).1 hy'⟩
        · rintro ⟨h2, h1, he'⟩
          exact ⟨⟨e, mem_compl_pair_iff.2 ⟨h1, h2⟩⟩, (hD _).2 he', rfl⟩
      have h3 : D'.card = T.darts.card - 2 := by
        rw [← card_map (Embedding.subtype _), h2, card_erase_of_mem, card_erase_of_mem hfD]
        · rfl
        · exact mem_erase.2 ⟨hG.inv_ne f, hifD⟩
      -- the two endpoints have one image
      have h4 : (T.nonRoot.image (contractV f G)).card + 1 = T.nonRoot.card := by
        have hzy : G.vertexOf (G.inv f) ∈ T.nonRoot.erase (G.vertexOf f) :=
          mem_erase.2 ⟨Ne.symm he.vertexOf_ne, hz⟩
        have himg : T.nonRoot.image (contractV f G) =
            (T.nonRoot.erase (G.vertexOf f)).image (contractV f G) := by
          rw [← insert_erase hy, image_insert, insert_erase hy]
          refine insert_eq_of_mem (mem_image.2 ⟨_, hzy, ?_⟩)
          rw [contractV, contractV, if_pos (Or.inr (G.self_mem_vertexOf _)),
            if_pos (Or.inl (G.self_mem_vertexOf _))]
        rw [himg, card_image_of_injOn, card_erase_of_mem hy]
        · have := T.nonRoot_nonempty.card_pos
          have : 1 ≤ T.nonRoot.card := card_pos.2 ⟨_, hy⟩
          omega
        · intro w hw w' hw' h
          have hw₁ := mem_erase.1 hw
          have hw₁' := mem_erase.1 hw'
          rcases contractV_injOn (G.mem_internalVertices.1 (T.nonRoot_subset hw₁.2)).1
            (G.mem_internalVertices.1 (T.nonRoot_subset hw₁'.2)).1 h with h' | ⟨h' | h', h'' | h''⟩
          · exact h'
          · exact absurd h' hw₁.1
          · exact absurd h' hw₁.1
          · exact absurd h'' hw₁'.1
          · exact h'.trans h''.symm
      have h5 := T.card_darts hG
      omega
    reflTransGen_treeAdj := by
      set W' := T.nonRoot.image (contractV f G)
      have hstep : ∀ u u₂, G.TreeAdj T.nonRoot u u₂ → Relation.ReflTransGen
          ((G.contractEdge f (he.leg_mem hG)).TreeAdj W') (contractV f G u) (contractV f G u₂) := by
        rintro _ _ ⟨e, he', rfl, rfl⟩
        by_cases h1 : e = f
        · subst h1
          rw [contractV, contractV, if_pos (Or.inl (G.self_mem_vertexOf _)),
            if_pos (Or.inr (G.self_mem_vertexOf _))]
        by_cases h2 : e = G.inv f
        · subst h2
          rw [hinv, contractV, contractV, if_pos (Or.inr (G.self_mem_vertexOf _)),
            if_pos (Or.inl (G.self_mem_vertexOf _))]
        have heS : e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2 ⟨h1, h2⟩
        have hieS : G.inv e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
          (apply_mem_compl_pair_iff hinv f e).2 heS
        refine Relation.ReflTransGen.single ⟨⟨e, heS⟩, (hD _).2 he', ?_, ?_⟩
        · rw [contractEdge_vertexOf_eq hG he]
        · have : (G.contractEdge f (he.leg_mem hG)).inv ⟨e, heS⟩ = ⟨G.inv e, hieS⟩ :=
            Subtype.ext (coe_contractEdge_inv hinv _)
          rw [this, contractEdge_vertexOf_eq hG he]
      intro u' hu'
      rcases mem_insert.1 hu' with rfl | hu'
      · exact .refl
      · obtain ⟨w, hw, rfl⟩ := mem_image.1 hu'
        exact Relation.ReflTransGen.lift' (contractV f G) hstep
          (T.reflTransGen_treeAdj w (mem_insert_of_mem hw)) }

namespace ContractTree

private theorem darts_iff (x : (({f, G.inv f} : Set H)ᶜ : Set H)) :
    x ∈ (contractTree hG he T hy hz).darts ↔ (x : H) ∈ T.darts :=
  mem_treeDarts_iff hG he T hy hz x

private theorem root_eq : (contractTree hG he T hy hz).root =
    (G.contractEdge f (he.leg_mem hG)).vertexOf
      ⟨T.intervalStart, mem_compl_of_mem_root T hy hz T.intervalStart_mem_root⟩ :=
  contractV_root hG he T hy hz

private theorem isBoundaryVertex_root_iff :
    (G.contractEdge f (he.leg_mem hG)).IsBoundaryVertex (contractTree hG he T hy hz).root ↔
      G.IsBoundaryVertex T.root := by
  rw [root_eq, isBoundaryVertex_vertexOf_contractEdge_iff he, ← T.root_eq_vertexOf_intervalStart]

private theorem intervalStart_eq : (contractTree hG he T hy hz).intervalStart =
    ⟨T.intervalStart, mem_compl_of_mem_root T hy hz T.intervalStart_mem_root⟩ := by
  refine ((contractTree hG he T hy hz).eq_intervalStart_of_rot_symm_notMem ?_ ?_ ?_).symm
  · rw [darts_iff]; exact T.intervalStart_mem_darts
  · rw [root_eq]; exact (G.contractEdge f (he.leg_mem hG)).self_mem_vertexOf _
  · have hrS := fun {e} (h : e ∈ T.root) => mem_compl_of_mem_root T hy hz h
    have hmem : G.rot.symm T.intervalStart ∈ T.root := T.mem_root_iff.2 (by
      rw [← G.vertexOf_rot, Equiv.apply_symm_apply, ← T.root_eq_vertexOf_intervalStart])
    have hσ : (G.contractEdge f (he.leg_mem hG)).rot ⟨G.rot.symm T.intervalStart, hrS hmem⟩ =
        ⟨T.intervalStart, hrS T.intervalStart_mem_root⟩ := by
      apply Subtype.ext
      rw [coe_contractEdge_rot_of_mem
        (by rw [Equiv.apply_symm_apply]; exact hrS T.intervalStart_mem_root)]
      exact Equiv.apply_symm_apply _ _
    rw [← hσ, Equiv.symm_apply_apply, darts_iff]
    exact T.rot_symm_intervalStart_notMem

end ContractTree

namespace ContractTree

omit hG he hz in
/-- The dart `f` of `P_T`. -/
def dartF : T.Dart := ⟨.inl f, T.mem_darts_of_vertexOf_mem hy⟩

omit he in
private theorem inv_dartF : T.plabicData.inv (dartF T hy) =
    ⟨.inl (G.inv f), T.mem_darts_of_vertexOf_mem hz⟩ :=
  T.inv_inl hG _

/-- `f` is a contractible edge of `P_T`. -/
theorem isContractibleEdge_dartF : T.plabicData.IsContractibleEdge (dartF T hy) := by
  have hfD := T.mem_darts_of_vertexOf_mem hy
  have hifD := T.mem_darts_of_vertexOf_mem hz
  -- the darts at non-root vertices lie at internal vertices of `P_T`
  have hint : ∀ {d} (hd : d ∈ T.darts), G.vertexOf d ∈ T.nonRoot →
      T.plabicData.vertexOf ⟨.inl d, hd⟩ ∈ T.plabicData.internalVertices := by
    intro d hd hW
    refine T.plabicData.vertexOf_mem_internalVertices.2 ?_
    rw [T.isBoundaryVertex_vertexOf_iff hG, T.vertexOf_dartE hG]
    simp only [mem_insert, mem_singleton]
    rintro (h | h | h)
    · exact absurd (congrArg Subtype.val h) (by simp [RootedTree.dartE])
    · have h' := congrArg Subtype.val h
      unfold RootedTree.legDart at h'
      split_ifs at h' with hb
      have hda : d = T.intervalStart := by simpa using h'
      exact T.root_notMem_nonRoot (by
        rwa [T.root_eq_vertexOf_intervalStart, ← hda])
    · exact absurd (congrArg Subtype.val h) (by simp [RootedTree.dartEBar])
  refine ⟨fun h => ?_, hint hfD hy, ?_, ?_⟩
  · have hmem : T.plabicData.inv (dartF T hy) ∈ T.plabicData.vertexOf (dartF T hy) := by
      rw [h]; exact T.plabicData.self_mem_vertexOf _
    rw [inv_dartF hG T hy hz] at hmem
    obtain ⟨d', h1, h2⟩ := T.exists_of_mem_vertexOf_inl hG hfD hy hmem
    have : G.inv f = d' := by simpa using h1
    rw [← this] at h2
    exact he.vertexOf_ne h2.symm
  · rw [inv_dartF hG T hy hz]; exact hint hifD hz
  · change T.colourAux (T.plabicData.inv (dartF T hy) : H ⊕ LollipopDart) = T.colourAux (.inl f)
    rw [inv_dartF hG T hy hz]
    exact he.colour_inv

/-- **The plabic graph of the tree with an edge contracted** is the contraction of `P_T` along
that edge. -/
theorem plabicData_isomorphic :
    (contractTree hG he T hy hz).plabicData.Isomorphic
      (T.plabicData.contractEdge (dartF T hy)
        ((isContractibleEdge_dartF hG he T hy hz).leg_mem (T.isPlabicGraph_plabicData hG))) := by
  have hinv := hG.inv_involutive
  set Tc := contractTree hG he T hy hz with hTc
  set P := T.plabicData with hPdef
  have hP := T.isPlabicGraph_plabicData hG
  have hGc : (G.contractEdge f (he.leg_mem hG)).IsPlabicGraph := hG.contractEdge he
  set δ := dartF T hy with hδdef
  have hδ := isContractibleEdge_dartF hG he T hy hz
  have hfD : f ∈ T.darts := T.mem_darts_of_vertexOf_mem hy
  have hifD : G.inv f ∈ T.darts := T.mem_darts_of_vertexOf_mem hz
  have hiδ : P.inv δ = ⟨.inl (G.inv f), hifD⟩ := inv_dartF hG T hy hz
  have hrS := fun {e} (h : e ∈ T.root) => mem_compl_of_mem_root T hy hz h
  set x₀ : (({f, G.inv f} : Set H)ᶜ : Set H) := ⟨T.intervalStart, hrS T.intervalStart_mem_root⟩
  set F : H ⊕ LollipopDart → (({f, G.inv f} : Set H)ᶜ : Set H) ⊕ LollipopDart :=
    Sum.map (toCompl f (G.inv f) x₀) id with hF
  have hbv := isBoundaryVertex_root_iff hG he T hy hz
  have hstart := intervalStart_eq hG he T hy hz
  have hD := darts_iff hG he T hy hz
  -- a dart `inl a` of the contraction is not `f` or `f̄`
  have hmemS : ∀ s : ({δ, P.inv δ}ᶜ : Set T.Dart), ∀ a, (s : T.Dart).1 = .inl a →
      a ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := by
    intro s a hs
    have := mem_compl_pair.1 s.2
    refine mem_compl_pair_iff.2 ⟨fun h => this.1 (Subtype.ext ?_), fun h => this.2 (Subtype.ext ?_)⟩
    · rw [hs, h]; rfl
    · rw [hs, h, hiδ]
  have hset : ∀ t : T.Dart, t.1 ≠ .inl f → t.1 ≠ .inl (G.inv f) →
      t ∈ ({δ, P.inv δ}ᶜ : Set T.Dart) := fun t h1 h2 =>
    mem_compl_pair.2 ⟨fun h => h1 (by rw [h]; rfl), fun h => h2 (by rw [h, hiδ])⟩
  have hmap : ∀ s : ({δ, P.inv δ}ᶜ : Set T.Dart), Tc.IsDart (F (s : T.Dart).1) := by
    rintro ⟨⟨a | l, ha⟩, hs⟩
    · change toCompl f (G.inv f) x₀ a ∈ Tc.darts
      rw [hD, coe_toCompl_of_mem (hmemS ⟨⟨_, ha⟩, hs⟩ a rfl)]
      exact ha
    · rcases l with _ | _ | _ | _
      · trivial
      · trivial
      · exact mt hbv.1 ha
      · exact mt hbv.1 ha
  let e : ({δ, P.inv δ}ᶜ : Set T.Dart) ≃ Tc.Dart :=
    Equiv.ofBijective (fun s => ⟨F (s : T.Dart).1, hmap s⟩) ⟨by
      rintro ⟨⟨a | l, ha⟩, hs⟩ ⟨⟨a' | l', ha'⟩, hs'⟩ h <;>
        simp only [Subtype.mk.injEq, hF, Sum.map_inl, Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq, id] at h
      · have := injOn_toCompl x₀ (hmemS ⟨⟨_, ha⟩, hs⟩ a rfl) (hmemS ⟨⟨_, ha'⟩, hs'⟩ a' rfl) h
        subst this
        rfl
      · subst h; rfl, by
      rintro ⟨y | l, hy'⟩
      · have hyD : (y : H) ∈ T.darts := (hD y).1 hy'
        have hs : (⟨.inl (y : H), hyD⟩ : T.Dart) ∈ ({δ, P.inv δ}ᶜ : Set T.Dart) :=
          hset _ (fun h => (mem_compl_pair_iff.1 y.2).1 (by simpa using h))
            (fun h => (mem_compl_pair_iff.1 y.2).2 (by simpa using h))
        refine ⟨⟨_, hs⟩, Subtype.ext ?_⟩
        change Sum.inl (toCompl f (G.inv f) x₀ y) = Sum.inl y
        rw [toCompl_val]
      · have hl : T.IsDart (.inr l) := by
          rcases l with _ | _ | _ | _
          · trivial
          · trivial
          · exact mt hbv.2 hy'
          · exact mt hbv.2 hy'
        exact ⟨⟨⟨.inr l, hl⟩, hset _ (by simp) (by simp)⟩, rfl⟩⟩
  have he_ : ∀ s, ((e s : Tc.Dart) : _ ⊕ LollipopDart) = F (s : T.Dart).1 := fun _ => rfl
  have hfa1 : toCompl f (G.inv f) x₀ T.intervalStart = Tc.intervalStart := by
    rw [hstart, toCompl_of_mem]
  -- the rotation of the contraction of `P_T`, where `P_T` does not run into the edge
  have hgen : ∀ s : ({δ, P.inv δ}ᶜ : Set T.Dart),
      P.rot (s : T.Dart) ∈ ({δ, P.inv δ}ᶜ : Set T.Dart) →
      (((P.contractEdge δ (hδ.leg_mem hP)).rot s : T.Dart) : H ⊕ LollipopDart) =
        T.rotAux (s : T.Dart).1 := fun s h => by
    rw [coe_contractEdge_rot_of_mem h, T.coe_rot_plabicData hG]
  have hσfD : G.rot f ∈ T.darts := T.rot_mem_darts_of_vertexOf_mem hy
  have hσzD : G.rot (G.inv f) ∈ T.darts := T.rot_mem_darts_of_vertexOf_mem hz
  have hPδ : P.rot δ = ⟨.inl (G.rot f), hσfD⟩ := T.rot_inl_of_mem hG hfD hσfD
  have hPiδ : P.rot (P.inv δ) = ⟨.inl (G.rot (G.inv f)), hσzD⟩ := by
    rw [hiδ]; exact T.rot_inl_of_mem hG hifD hσzD
  have hσf_ne : G.rot f ≠ G.inv f := fun h => he.vertexOf_ne (by rw [← G.vertexOf_rot f, h])
  have hσz_ne : G.rot (G.inv f) ≠ f := fun h =>
    he.vertexOf_ne (by rw [← G.vertexOf_rot (G.inv f), h])
  refine ⟨(Iso.ofEquivOfMapLeg e (fun s => Subtype.ext ?_) (fun s => Subtype.ext ?_)
    (fun s => ?_) (fun s _ => ?_) (fun i => Subtype.ext ?_)).symm⟩
  · -- the involutions
    rw [he_, Tc.coe_inv_plabicData hGc, he_, coe_contractEdge_inv hP.inv_involutive,
      T.coe_inv_plabicData hG]
    rcases s with ⟨⟨a | l, ha⟩, hs⟩
    · have haS := hmemS ⟨⟨_, ha⟩, hs⟩ a rfl
      have hiaS : G.inv a ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
        (apply_mem_compl_pair_iff hinv f a).2 haS
      simp only [hF, Sum.map_inl]
      congr 1
      apply Subtype.ext
      rw [coe_toCompl_of_mem hiaS, coe_contractEdge_inv hinv, coe_toCompl_of_mem haS]
    · rfl
  · -- the rotations
    rw [he_, Tc.coe_rot_plabicData hGc, he_]
    rcases s with ⟨⟨a | (_ | _ | _ | _), ha⟩, hs⟩
    · have haS := hmemS ⟨⟨_, ha⟩, hs⟩ a rfl
      have hFa : F (.inl a) = .inl ⟨a, haS⟩ := by simp only [hF, Sum.map_inl, toCompl_of_mem haS]
      rw [hFa]
      -- the rotation of the contraction at `a`, in `P_T` and in `G`
      have key : ∀ {c : H} (hc : c ∈ T.darts) (hcS : c ∈ (({f, G.inv f} : Set H)ᶜ : Set H)),
          (((P.contractEdge δ (hδ.leg_mem hP)).rot ⟨⟨.inl a, ha⟩, hs⟩ : T.Dart) =
            ⟨.inl c, hc⟩) →
          (((G.contractEdge f (he.leg_mem hG)).rot ⟨a, haS⟩ : (({f, G.inv f} : Set H)ᶜ : Set H)) =
            ⟨c, hcS⟩) →
          F (((P.contractEdge δ (hδ.leg_mem hP)).rot ⟨⟨.inl a, ha⟩, hs⟩ : T.Dart) :
            H ⊕ LollipopDart) = Tc.rotAux (.inl ⟨a, haS⟩) := by
        intro c hc hcS h1 h2
        rw [h1]
        change Sum.inl (toCompl f (G.inv f) x₀ c) = _
        rw [toCompl_of_mem hcS]
        simp only [RootedTree.rotAux, h2]
        rw [if_pos ((hD ⟨c, hcS⟩).2 hc)]
      by_cases h1 : G.rot a = f
      · have hPa : P.rot ⟨.inl a, ha⟩ = δ := by
          rw [T.rot_inl_of_mem hG ha (by rwa [h1])]
          exact Subtype.ext (by simp [h1, hδdef, dartF])
        by_cases hz1 : G.rot (G.inv f) = G.inv f
        · have hσfS : G.rot f ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2
            ⟨fun h => (mem_compl_pair_iff.1 haS).1 (G.rot.injective (h1.trans h.symm)), hσf_ne⟩
          refine key hσfD hσfS ?_ (Subtype.ext (coe_contractEdge_rot_of_eq_of_eq h1 hz1 hσfS))
          rw [coe_contractEdge_rot_of_eq_of_eq (x := ⟨⟨.inl a, ha⟩, hs⟩) hPa
            (by rw [hPiδ, hiδ]; exact Subtype.ext (by simp [hz1]))
            (hset _ (by rw [hPδ]; simpa using (mem_compl_pair_iff.1 hσfS).1)
              (by rw [hPδ]; simpa using hσf_ne)), hPδ]
        · have hσzS : G.rot (G.inv f) ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
            mem_compl_pair_iff.2 ⟨hσz_ne, hz1⟩
          refine key hσzD hσzS ?_ (Subtype.ext (coe_contractEdge_rot_of_eq h1 hσzS))
          rw [coe_contractEdge_rot_of_eq (x := ⟨⟨.inl a, ha⟩, hs⟩) hPa
            (hset _ (by rw [hPiδ]; simpa using hσz_ne) (by rw [hPiδ]; simpa using hz1)), hPiδ]
      by_cases h2 : G.rot a = G.inv f
      · have hPa : P.rot ⟨.inl a, ha⟩ = P.inv δ := by
          rw [T.rot_inl_of_mem hG ha (by rwa [h2]), hiδ]
          exact Subtype.ext (by simp [h2])
        by_cases hy1 : G.rot f = f
        · have hσzS : G.rot (G.inv f) ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2
            ⟨hσz_ne, fun h => (mem_compl_pair_iff.1 haS).2 (G.rot.injective (h2.trans h.symm))⟩
          refine key hσzD hσzS ?_ (Subtype.ext (coe_contractEdge_rot_of_eq_inv_of_eq h2 hy1 hσzS))
          rw [coe_contractEdge_rot_of_eq_inv_of_eq (x := ⟨⟨.inl a, ha⟩, hs⟩) hPa
            (by rw [hPδ]; exact Subtype.ext (by simp [hy1, hδdef, dartF]))
            (hset _ (by rw [hPiδ]; simpa using hσz_ne)
              (by rw [hPiδ]; simpa using (mem_compl_pair_iff.1 hσzS).2)), hPiδ]
        · have hσfS : G.rot f ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
            mem_compl_pair_iff.2 ⟨hy1, hσf_ne⟩
          refine key hσfD hσfS ?_ (Subtype.ext (coe_contractEdge_rot_of_eq_inv h2 hσfS))
          rw [coe_contractEdge_rot_of_eq_inv (x := ⟨⟨.inl a, ha⟩, hs⟩) hPa
            (hset _ (by rw [hPδ]; simpa using hy1) (by rw [hPδ]; simpa using hσf_ne)), hPδ]
      -- the rotation does not run into the edge
      have hraS : G.rot a ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2 ⟨h1, h2⟩
      have hPa : P.rot ⟨.inl a, ha⟩ ∈ ({δ, P.inv δ}ᶜ : Set T.Dart) := by
        refine hset _ ?_ ?_ <;> rw [T.coe_rot_plabicData hG] <;> simp only [RootedTree.rotAux] <;>
          split_ifs <;> simp [h1, h2]
      rw [hgen _ hPa]
      have hrot : (G.contractEdge f (he.leg_mem hG)).rot ⟨a, haS⟩ = ⟨G.rot a, hraS⟩ :=
        Subtype.ext (coe_contractEdge_rot_of_mem hraS)
      change F (T.rotAux (.inl a)) = Tc.rotAux (.inl ⟨a, haS⟩)
      simp only [RootedTree.rotAux, hrot]
      have hiff : (⟨G.rot a, hraS⟩ : (({f, G.inv f} : Set H)ᶜ : Set H)) ∈ Tc.darts ↔
          G.rot a ∈ T.darts := hD _
      by_cases h : G.rot a ∈ T.darts
      · rw [if_pos h, if_pos (hiff.2 h)]
        simp only [hF, Sum.map_inl, toCompl_of_mem hraS]
      · rw [if_neg h, if_neg (mt hiff.1 h)]
        by_cases hb : G.IsBoundaryVertex T.root
        · rw [if_pos hb, if_pos (hbv.2 hb)]; rfl
        · rw [if_neg hb, if_neg (mt hbv.1 hb)]; rfl
    · have hPe : P.rot ⟨.inr .e, ha⟩ ∈ ({δ, P.inv δ}ᶜ : Set T.Dart) := by
        refine hset _ ?_ ?_ <;> rw [T.coe_rot_plabicData hG] <;> simp only [RootedTree.rotAux] <;>
          split_ifs <;> simp [(mem_compl_pair_iff.1 (hrS T.intervalStart_mem_root)).1,
            (mem_compl_pair_iff.1 (hrS T.intervalStart_mem_root)).2]
      rw [hgen _ hPe]
      change F (T.rotAux (.inr .e)) = Tc.rotAux (.inr .e)
      simp only [RootedTree.rotAux]
      by_cases hb : G.IsBoundaryVertex T.root
      · rw [if_pos hb, if_pos (hbv.2 hb), ← hfa1]; rfl
      · rw [if_neg hb, if_neg (mt hbv.1 hb)]; rfl
    · rw [hgen _ (hset _ (by rw [T.coe_rot_plabicData hG]; simp [RootedTree.rotAux])
        (by rw [T.coe_rot_plabicData hG]; simp [RootedTree.rotAux]))]
      rfl
    · rw [hgen _ (hset _ (by rw [T.coe_rot_plabicData hG]; simp [RootedTree.rotAux])
        (by rw [T.coe_rot_plabicData hG]; simp [RootedTree.rotAux]))]
      rfl
    · have hPg : P.rot ⟨.inr .gBar, ha⟩ ∈ ({δ, P.inv δ}ᶜ : Set T.Dart) := by
        refine hset _ ?_ ?_ <;> rw [T.coe_rot_plabicData hG] <;>
          simp [RootedTree.rotAux, (mem_compl_pair_iff.1 (hrS T.intervalStart_mem_root)).1,
            (mem_compl_pair_iff.1 (hrS T.intervalStart_mem_root)).2]
      rw [hgen _ hPg]
      change F (T.rotAux (.inr .gBar)) = Tc.rotAux (.inr .gBar)
      simp only [RootedTree.rotAux, ← hfa1]
      rfl
  · -- the boundaries
    rw [mem_contractEdge_bdry, Tc.mem_bdry_plabicData, T.mem_bdry_plabicData]
    rcases s with ⟨⟨a | (_ | _ | _ | _), ha⟩, hs⟩ <;>
      simp [RootedTree.dartE, RootedTree.dartEBar, e, hF]
  · -- the colours
    change Tc.colourAux (F (s : T.Dart).1) = T.colourAux (s : T.Dart).1
    rcases s with ⟨⟨a | l, ha⟩, hs⟩
    · change (G.contractEdge f (he.leg_mem hG)).colour (toCompl f (G.inv f) x₀ a) = G.colour a
      rw [contractEdge_colour, coe_toCompl_of_mem (hmemS ⟨⟨_, ha⟩, hs⟩ a rfl)]
    · change (G.contractEdge f (he.leg_mem hG)).colour Tc.intervalStart = G.colour T.intervalStart
      rw [contractEdge_colour, hstart]
  · -- the legs
    change F ((P.leg i : T.Dart) : H ⊕ LollipopDart) = (Tc.legDart : _ ⊕ LollipopDart)
    change F (T.legDart : H ⊕ LollipopDart) = _
    rw [RootedTree.legDart, RootedTree.legDart]
    by_cases hb : G.IsBoundaryVertex T.root
    · rw [dif_pos hb, dif_pos (hbv.2 hb)]
      change Sum.inl (toCompl f (G.inv f) x₀ T.intervalStart) = Sum.inl Tc.intervalStart
      rw [hfa1]
    · rw [dif_neg hb, dif_neg (mt hbv.1 hb)]
      rfl

end ContractTree

end ContractTree

/-! ### Contracting an edge of a tree, in a family -/

section ContractInside

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {f : H} (he : G.IsContractibleEdge f)
  {𝒯 : Finset (G.RootedTree × Shade)} (h𝒯 : G.IsCollapsingFamily 𝒯)
  {p₀ : G.RootedTree × Shade} (hp₀ : p₀ ∈ 𝒯) (hy : G.vertexOf f ∈ p₀.1.nonRoot)
  (hz : G.vertexOf (G.inv f) ∈ p₀.1.nonRoot)

include hG he h𝒯 hp₀ hy hz

open scoped Classical in
/-- **Contracting an edge of a tree**: the tree with the edge contracted replaces the tree, or is
dropped when it becomes the edge of a lollipop, and the collapse does not change. -/
theorem exists_collapse_contract_inside :
    ∃ 𝒯' : Finset ((G.contractEdge f (he.leg_mem hG)).RootedTree × Shade),
      (G.contractEdge f (he.leg_mem hG)).IsCollapsingFamily 𝒯' ∧
      ((G.contractEdge f (he.leg_mem hG)).collapse 𝒯').Isomorphic (G.collapse 𝒯) := by
  have hinv := hG.inv_involutive
  have hne := he.not_sameCycle
  have hGc : (G.contractEdge f (he.leg_mem hG)).IsPlabicGraph := hG.contractEdge he
  set T₀ := p₀.1 with hT₀
  set Tc := contractTree hG he T₀ hy hz with hTc
  have hfD : f ∈ T₀.darts := T₀.mem_darts_of_vertexOf_mem hy
  have hifD : G.inv f ∈ T₀.darts := T₀.mem_darts_of_vertexOf_mem hz
  have hDc := ContractTree.darts_iff hG he T₀ hy hz
  have hrS := fun {e} (h : e ∈ T₀.root) => ContractTree.mem_compl_of_mem_root T₀ hy hz h
  have hDA' : ∀ e ∈ G.familyDarts (𝒯.erase p₀), e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
    fun _ he' => h𝒯.mem_compl_pair_of_mem_familyDarts_erase hG hp₀ hfD hifD he'
  have hfreeD : ∀ q ∈ 𝒯, ∃ a ∈ q.1.root, a ∉ G.familyDarts 𝒯 := fun _ hq =>
    h𝒯.exists_mem_root_notMem_familyDarts hq
  have hfDf : f ∈ G.familyDarts 𝒯 := mem_familyDarts.2 ⟨p₀, hp₀, hfD⟩
  have hifDf : G.inv f ∈ G.familyDarts 𝒯 := mem_familyDarts.2 ⟨p₀, hp₀, hifD⟩
  have hnotDS : ∀ a, a ∉ G.familyDarts 𝒯 → a ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := fun a h =>
    mem_compl_pair_iff.2 ⟨fun h' => h (h' ▸ hfDf), fun h' => h (h' ▸ hifDf)⟩
  set x₀ : (({f, G.inv f} : Set H)ᶜ : Set H) := ⟨G.leg ⟨0, hG.one_le⟩, he.leg_mem hG _⟩
  have hA := injOn_toCompl x₀
  have hothers : ∀ q ∈ 𝒯.erase p₀, G.vertexOf f ∉ q.1.nonRoot ∧
      G.vertexOf (G.inv f) ∉ q.1.nonRoot ∧ q.1.root ≠ G.vertexOf f ∧
      q.1.root ≠ G.vertexOf (G.inv f) := by
    intro q hq
    have hq' := mem_of_mem_erase hq
    have hqp := ne_of_mem_erase hq
    have hW := h𝒯.disjoint_nonRoot p₀ hp₀ q hq' (Ne.symm hqp)
    have hr := h𝒯.root_notMem_nonRoot q hq' p₀ hp₀ hqp
    exact ⟨fun h => disjoint_left.1 hW hy h, fun h => disjoint_left.1 hW hz h,
      fun h => hr (h ▸ hy), fun h => hr (h ▸ hz)⟩
  have hemb' : ∀ q ∈ 𝒯.erase p₀, q.1.IsEmbedding (G.contractEdge f (he.leg_mem hG))
      (toCompl f (G.inv f) x₀) := fun q hq =>
    contractOutside_isEmbedding hG he x₀ (hothers q hq).1 (hothers q hq).2.1 fun h => by
      rcases h with h | h
      · exact absurd h (hothers q hq).2.2.1
      · exact absurd h (hothers q hq).2.2.2
  have hroot' : ∀ q ∈ 𝒯.erase p₀, (G.contractEdge f (he.leg_mem hG)).IsBoundaryVertex
      ((G.contractEdge f (he.leg_mem hG)).vertexOf (toCompl f (G.inv f) x₀ q.1.intervalStart)) ↔
      G.IsBoundaryVertex q.1.root := fun q hq => by
    rw [isBoundaryVertex_vertexOf_contractEdge_iff he, coe_toCompl_of_mem (hDA' _
      (mem_familyDarts.2 ⟨q, hq, q.1.intervalStart_mem_darts⟩)),
      ← q.1.root_eq_vertexOf_intervalStart]
  have hsame : ∀ a c : H, a ∈ (({f, G.inv f} : Set H)ᶜ : Set H) →
      c ∈ (({f, G.inv f} : Set H)ᶜ : Set H) → G.rot.SameCycle c a →
      toCompl f (G.inv f) x₀ a ∈ (G.contractEdge f (he.leg_mem hG)).vertexOf
        (toCompl f (G.inv f) x₀ c) := fun a c ha hc h => by
    rw [RotationSystem.mem_vertexOf, toCompl_of_mem ha, toCompl_of_mem hc,
      sameCycle_contractEdge_rot_iff hne]
    exact Or.inl h
  have hfree : ∀ q ∈ 𝒯.erase p₀, ∃ a ∈ (({f, G.inv f} : Set H)ᶜ : Set H),
      a ∉ G.familyDarts 𝒯 ∧ toCompl f (G.inv f) x₀ a ∈ (G.contractEdge f (he.leg_mem hG)).vertexOf
        (toCompl f (G.inv f) x₀ q.1.intervalStart) := fun q hq => by
    obtain ⟨a, ha', haD⟩ := hfreeD q (mem_of_mem_erase hq)
    refine ⟨a, hnotDS a haD, haD, hsame _ _ (hnotDS a haD)
      (hDA' _ (mem_familyDarts.2 ⟨q, hq, q.1.intervalStart_mem_darts⟩)) ?_⟩
    rwa [← G.mem_vertexOf, ← q.1.root_eq_vertexOf_intervalStart]
  have hT'D : ∀ y ∈ Tc.darts, ∃ e ∈ T₀.darts, e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) ∧
      toCompl f (G.inv f) x₀ e = y := fun y hy' =>
    ⟨y, (hDc y).1 hy', y.2, toCompl_val y⟩
  have hT'free : ∃ a ∈ (({f, G.inv f} : Set H)ᶜ : Set H), a ∉ G.familyDarts 𝒯 ∧
      toCompl f (G.inv f) x₀ a ∈ Tc.root := by
    obtain ⟨a, ha', haD⟩ := hfreeD p₀ hp₀
    refine ⟨a, hnotDS a haD, haD, ?_⟩
    rw [hTc, ContractTree.root_eq, ← toCompl_of_mem (x₀ := x₀) (hrS T₀.intervalStart_mem_root)]
    refine hsame _ _ (hnotDS a haD) (hrS T₀.intervalStart_mem_root) ?_
    rwa [← G.mem_vertexOf, ← T₀.root_eq_vertexOf_intervalStart]
  set 𝒯p := insert (Tc, p₀.2) (transportFamily hG hGc hemb') with h𝒯p
  have hfam : ∀ y : H, y ∈ G.familyDarts 𝒯 ↔ y ∈ T₀.darts ∨ y ∈ G.familyDarts (𝒯.erase p₀) :=
    fun _ => mem_familyDarts_iff_mem_darts_or_mem_familyDarts_erase hp₀
  have hDo : ∀ y : (({f, G.inv f} : Set H)ᶜ : Set H), (∃ e ∈ G.familyDarts (𝒯.erase p₀),
      toCompl f (G.inv f) x₀ e = y) ↔ (y : H) ∈ G.familyDarts (𝒯.erase p₀) := fun y =>
    ⟨by rintro ⟨e, he', rfl⟩; rwa [coe_toCompl_of_mem (hDA' e he')], fun h => ⟨y, h, toCompl_val y⟩⟩
  have hD : ∀ y : (({f, G.inv f} : Set H)ᶜ : Set H),
      y ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯p ↔ (y : H) ∈ G.familyDarts 𝒯 := by
    intro y
    rw [mem_familyDarts_insert_transportFamily, hDo, hfam, hDc]
  have hQ : ∀ x, G.rot x ∈ (G.vertexOf (G.inv f) : Set H) ↔
      x ∈ (G.vertexOf (G.inv f) : Set H) := fun x => by
    simp only [mem_coe, RotationSystem.mem_vertexOf, sameCycle_apply_right]
  have hQK : ∀ x ∈ (G.vertexOf (G.inv f) : Set H), x ∉ G.collapseCore 𝒯 :=
    notMem_collapseCore_of_vertexOf_mem_nonRoot hG hp₀ hz
  have hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2 := fun i p₁ hp₁ p₂ hp₂ h₁ h₂ => by rw [h𝒯.eq_of_mem_darts hG hp₁ hp₂ h₁ h₂]
  have hcolT : ∀ i, ∀ p₁ ∈ 𝒯, ∀ q' ∈ transportFamily hG hGc hemb', G.leg i ∈ p₁.1.darts →
      (G.contractEdge f (he.leg_mem hG)).leg i ∈ q'.1.darts → p₁.2 = q'.2 := by
    intro i p₁ hp₁ q' hq' h₁ h₂
    obtain ⟨r, hr, hir, hrc⟩ := transportFamily_colour hG hGc hemb' hA hDA' (he.leg_mem hG i) hq'
      (by rwa [toCompl_of_mem (he.leg_mem hG i)])
    rw [h𝒯.eq_of_mem_darts hG hp₁ (mem_of_mem_erase hr) h₁ hir, hrc]
  have hcol : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯p, G.leg i ∈ p₁.1.darts →
      (G.contractEdge f (he.leg_mem hG)).leg i ∈ p₂.1.darts → p₁.2 = p₂.2 := by
    intro i p₁ hp₁ p₂ hp₂ h₁ h₂
    rcases mem_insert.1 hp₂ with rfl | hp₂
    · have : G.leg i ∈ T₀.darts := (hDc _).1 h₂
      rw [h𝒯.eq_of_mem_darts hG hp₁ hp₀ h₁ this]
    · exact hcolT i p₁ hp₁ p₂ hp₂ h₁ h₂
  have hisoP := isomorphic_collapse_of_cut hG (contractEdge_eq_cutData hinv (he.leg_mem hG)) hGc
    hD hfDf hifDf _ hQ hQK (Or.inr (G.self_mem_vertexOf _)) hcol hcol₁
  -- `P_{Tc}` is `{M2, M3}`-equivalent to `L_c`
  have hc := h𝒯.isCollapsibleOfColour p₀ hp₀
  have hPT' : PlabicGraph.MoveEquivalent {.m2, .m3}
      ⟨_, Tc.plabicData, Tc.isPlabicGraph_plabicData hGc⟩ (lollipopPlabicGraph p₀.2) := by
    have hloc : PlabicGraph.IsLocalMove .m3 ⟨_, T₀.plabicData, hc.isPlabicGraph⟩
        ⟨_, Tc.plabicData, Tc.isPlabicGraph_plabicData hGc⟩ :=
      Or.inl ⟨ContractTree.dartF T₀ hy, ContractTree.isContractibleEdge_dartF hG he T₀ hy hz,
        ContractTree.plabicData_isomorphic hG he T₀ hy hz⟩
    exact (PlabicGraph.MoveEquivalent.of_isLocalMove (by simp) hloc).symm.trans hc.moveEquivalent
  have hbv := ContractTree.isBoundaryVertex_root_iff hG he T₀ hy hz
  by_cases hdrop : G.IsBoundaryVertex T₀.root ∧ Tc.nonRoot.card = 1
  · -- the tree becomes the edge of a lollipop and is dropped
    obtain ⟨hb, h1⟩ := hdrop
    have hb' : (G.contractEdge f (he.leg_mem hG)).IsBoundaryVertex Tc.root := hbv.2 hb
    obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.mem_boundaryVertices.2 ⟨T₀.root_mem_vertices, hb⟩)
    have hi' : Tc.root = (G.contractEdge f (he.leg_mem hG)).bvertex i := by
      rw [hTc, ContractTree.root_eq, bvertex]
      congr 1
      apply Subtype.ext
      change T₀.intervalStart = G.leg i
      exact T₀.intervalStart_eq_leg hG hi.symm
    have hstart := Tc.intervalStart_eq_leg hGc hi'
    obtain ⟨hD', hu⟩ := Tc.darts_eq_of_card_nonRoot_eq_one hGc hb' h1
    have hcol' : (G.contractEdge f (he.leg_mem hG)).colour
        ((G.contractEdge f (he.leg_mem hG)).inv Tc.intervalStart) = p₀.2 := by
      obtain ⟨θ⟩ := Tc.lollipop_isomorphic_of_card_nonRoot_eq_one hGc hb' h1
      exact eq_of_moveEquivalent_lollipopPlabicGraph
        ((PlabicGraph.MoveEquivalent.of_isomorphic (S := {.m2, .m3})
          (G := lollipopPlabicGraph _) (G' := ⟨_, Tc.plabicData, Tc.isPlabicGraph_plabicData hGc⟩)
          ⟨θ.symm⟩).trans hPT')
    have h𝒯e := h𝒯.subset (erase_subset p₀ 𝒯)
    have hemb'' := isCollapsingFamily_transportFamily hG hGc hemb' h𝒯e hA hDA' hroot'
      (fun q hq => by
        obtain ⟨a, haS, haD, hav⟩ := hfree q hq
        exact ⟨a, haS, fun h => haD ((hfam a).2 (Or.inr h)), hav⟩)
    have hlegT₀ : G.leg i ∈ T₀.darts := by
      rw [← T₀.intervalStart_eq_leg hG hi.symm]; exact T₀.intervalStart_mem_darts
    refine ⟨_, hemb'', ?_⟩
    refine PlabicData.Isomorphic.trans _ ⟨collapseIsoAbsorb hGc (𝒯₂ := 𝒯p) (i := i) ?_ ?_ ?_ ?_ ?_
      ?_⟩ hisoP
    · intro y
      rw [mem_familyDarts_insert_transportFamily, hD', mem_insert, mem_singleton, ← hstart,
        ← mem_familyDarts_transportFamily hG hGc hemb']
      tauto
    · intro h
      obtain ⟨e, he', hfe⟩ := (mem_familyDarts_transportFamily hG hGc hemb').1 h
      have := congrArg Subtype.val hfe
      rw [coe_toCompl_of_mem (hDA' e he')] at this
      obtain ⟨q, hq, heq⟩ := mem_familyDarts.1 he'
      have he'' : e = G.leg i := this
      subst he''
      exact ne_of_mem_erase hq (h𝒯.eq_of_mem_darts hG (mem_of_mem_erase hq) hp₀ heq hlegT₀)
    · intro y hy' hne'
      rw [← hstart] at hy' hne'
      rw [hu, mem_singleton] at hy'
      exact absurd hy' hne'
    · intro p hp hip
      rcases mem_insert.1 hp with rfl | hp
      · rw [← hstart]
        exact hcol'.symm
      · exfalso
        obtain ⟨r, hr, hir, -⟩ := transportFamily_colour hG hGc hemb' hA hDA' (he.leg_mem hG i) hp
          (by rwa [toCompl_of_mem (he.leg_mem hG i)])
        exact ne_of_mem_erase hr (h𝒯.eq_of_mem_darts hG (mem_of_mem_erase hr) hp₀ hir hlegT₀)
    · intro j p₁ hp₁ p₂ hp₂ h₁ h₂
      rcases mem_insert.1 hp₂ with rfl | hp₂
      · exfalso
        obtain ⟨r, hr, hjr, -⟩ := transportFamily_colour hG hGc hemb' hA hDA' (he.leg_mem hG j)
          hp₁ (by rwa [toCompl_of_mem (he.leg_mem hG j)])
        have : G.leg j ∈ T₀.darts := (hDc _).1 h₂
        exact ne_of_mem_erase hr (h𝒯.eq_of_mem_darts hG (mem_of_mem_erase hr) hp₀ hjr this)
      · rw [hemb''.eq_of_mem_darts hGc hp₁ hp₂ h₁ h₂]
    · intro j p₁ hp₁ p₂ hp₂ h₁ h₂
      rw [hemb''.eq_of_mem_darts hGc hp₁ hp₂ h₁ h₂]
  · -- the tree stays collapsible
    have hT' : Tc.IsCollapsibleOfColour p₀.2 := by
      refine ⟨Tc.isPlabicGraph_plabicData hGc, hPT', ?_⟩
      rcases hc.root_cases with ⟨hb, hcol'⟩ | ⟨hb, h2⟩
      · refine Or.inl ⟨mt hbv.1 hb, fun y hy' => ?_⟩
        rw [contractEdge_colour]
        have : (y : H) ∈ T₀.root := by
          rw [hTc, ContractTree.root_eq, contractEdge_vertexOf_eq hG he, contractV, mem_subtype,
            if_neg] at hy'
          · rwa [← T₀.root_eq_vertexOf_intervalStart] at hy'
          · rw [← T₀.root_eq_vertexOf_intervalStart]
            have hr := ContractTree.root_ne T₀ hy hz
            rintro (h | h)
            · exact hr.1 (T₀.mem_root_iff.1 h).symm
            · exact hr.2 (T₀.mem_root_iff.1 h).symm
        exact hcol' _ this
      · refine Or.inr ⟨hbv.2 hb, ?_⟩
        have hpos : 0 < Tc.nonRoot.card := Tc.nonRoot_nonempty.card_pos
        have : Tc.nonRoot.card ≠ 1 := fun h => hdrop ⟨hb, h⟩
        omega
    exact ⟨𝒯p, isCollapsingFamily_insert_transportFamily hG hGc h𝒯 hp₀ hemb' hA hDA' hroot'
      hfree hT' hT'D hT'free, hisoP⟩

end ContractInside

/-! ### Contracting along `f̄` instead of `f` -/

section ContractInv

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {f : H} (he : G.IsContractibleEdge f)

include hG he

/-- The edge `{f̄, f}` is contractible as well. -/
theorem isContractibleEdge_inv : G.IsContractibleEdge (G.inv f) where
  vertexOf_ne := by rw [hG.inv_involutive]; exact he.vertexOf_ne.symm
  mem_internalVertices := he.inv_mem_internalVertices
  inv_mem_internalVertices := by rw [hG.inv_involutive]; exact he.mem_internalVertices
  colour_inv := by rw [hG.inv_involutive]; exact he.colour_inv.symm

/-- The contractions along `f` and along `f̄` are isomorphic. -/
theorem contractEdge_inv_isomorphic :
    (G.contractEdge f (he.leg_mem hG)).Isomorphic
      (G.contractEdge (G.inv f) ((isContractibleEdge_inv hG he).leg_mem hG)) := by
  have hinv := hG.inv_involutive
  have hY : (({f, G.inv f} : Set H)ᶜ : Set H) =
      (({G.inv f, G.inv (G.inv f)} : Set H)ᶜ : Set H) := by
    rw [hinv, Set.pair_comm]
  have hmem : ∀ x : H, x ∈ (({f, G.inv f} : Set H)ᶜ : Set H) ↔
      x ∈ (({G.inv f, G.inv (G.inv f)} : Set H)ᶜ : Set H) := fun x => by rw [hY]
  have hπ : G.rot * swap (G.inv f) (G.inv (G.inv f)) = G.rot * swap f (G.inv f) := by
    rw [hinv, swap_comm]
  refine ⟨Iso.ofEquivOfMapLeg (Equiv.subtypeEquivRight hmem) (fun x => Subtype.ext ?_)
    (fun x => Subtype.ext ?_) (fun x => ?_) (fun x _ => rfl) (fun i => rfl)⟩
  · change ((G.contractEdge f (he.leg_mem hG)).inv x : H) =
      ((G.contractEdge (G.inv f) ((isContractibleEdge_inv hG he).leg_mem hG)).inv
        ⟨x, (hmem x).1 x.2⟩ : H)
    rw [coe_contractEdge_inv hinv, coe_contractEdge_inv hinv]
  · change (firstReturn (G.rot * swap f (G.inv f)) _ x : H) =
      (firstReturn (G.rot * swap (G.inv f) (G.inv (G.inv f))) _ ⟨x, (hmem x).1 x.2⟩ : H)
    rw [hπ]
    exact coe_firstReturn_congr _ hY x x.2 _
  · rw [mem_contractEdge_bdry, mem_contractEdge_bdry]
    rfl

end ContractInv

end PlabicData

end ClusterAlgebras

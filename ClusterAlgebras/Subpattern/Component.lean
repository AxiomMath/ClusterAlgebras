/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Subpattern.Subpattern

/-!
# The seed subpattern of a connected component

The *connected component* `C(v)` of a vertex `v` of a quiver `Q = (V, F, a)` is the set of
vertices `u` reached from `v` by a sequence `v = w₀, w₁, …, w_r = u` of vertices with
`a(w_{e-1}, w_e) + a(w_e, w_{e-1}) > 0` at every step (`ClusterAlgebras.Quiver.component`).
No arrow joins a vertex of `C(v)` to a vertex outside it
(`ClusterAlgebras.Quiver.arrows_eq_zero_of_mem_component_of_notMem`).

Consequently, if the seed `Σ(t)` of a seed pattern `Σ` has extended exchange matrix
`B̃(Q, λ)`, the enumeration `ι_I` of `I = λ⁻¹(C(v))` is closed for it, and the restricted
seed `Σ(t)_I` is a labeled seed in `F' = K(x_i : i ∈ I)`. The seed pattern `Π` in `F'` with
`Π(∅) = Σ(t)_I` is then a seed subpattern of `Σ`, freezing nothing and relabelling by the
identity (`ClusterAlgebras.exists_isSeedSubpattern_component`). This is the third assertion
of Lemma 4.2.7 of [FWZ17]. For a mutable vertex `v` its rank `n_I` is at least `1`
(`ClusterAlgebras.one_le_mutableCard_component`).

## Main definitions

* `ClusterAlgebras.Quiver.component`: the connected component `C(v)` of a vertex `v`.

## Main results

* `ClusterAlgebras.Quiver.mem_component_iff_exists_fin`: the definition by sequences
  `w₀, …, w_r`, as in [FWZ17].
* `ClusterAlgebras.Quiver.arrows_eq_zero_of_mem_component_of_notMem`: no arrow leaves or
  enters a connected component.
* `ClusterAlgebras.exists_isSeedSubpattern_component`: a connected component gives a seed
  subpattern, whose seed at the root is the restricted seed `Σ(t)_I`.
* `ClusterAlgebras.one_le_mutableCard_component`: the component of a mutable vertex gives a
  subpattern of rank `n_I ≥ 1`.

## Implementation notes

* `Quiver.component` is the set of vertices `u` with
  `Relation.ReflTransGen (fun w w' => 0 < a(w, w') + a(w', w)) v u`. The reflexive
  transitive closure is the existence of a finite sequence `w₀, …, w_r`, `r ≥ 0`, of [FWZ17],
  and `Quiver.mem_component_iff_exists_fin` proves the two equivalent, with the sequence a
  map `Fin (r + 1) → V`. Mathlib's connected components are a quotient attached to its own
  `Quiver` class, or to a `SimpleGraph`; the quiver here is the project's `Quiver` structure,
  and the component is wanted as a set of vertices, so it is defined directly.

* The component is a `Set V`, so its definition needs no decidability. The index set
  `I = λ⁻¹(C(v))` enters the subpattern lemma as a `Finset (Fin m)` with
  `(I : Set (Fin m)) = λ⁻¹(C(v))`, which determines it.

* The field `F' = K(x_i : i ∈ I)` is `IntermediateField.adjoin K ((P t).extCluster '' I)`,
  the field of [FWZ17] verbatim. The seed of `Π` at the root is the restricted seed,
  read in `F` along the inclusion of `F'`; the restricted seed `Σ(t)_I` itself has its entries
  in `F`.

* Lemma 4.2.7 of [FWZ17] asks `v` to be mutable. The seed subpattern exists for every vertex
  `v`, because `IsSeedPattern` does not ask for a positive rank, so
  `exists_isSeedSubpattern_component` does not assume it, a generalisation. Mutability is
  what gives the rank `n_I ≥ 1` of the standing convention, recorded as
  `one_le_mutableCard_component`.

* [FWZ17] writes `Σ(t) = (x̃, B̃(Q, λ))`. Only the matrix is used, so the hypothesis is
  `(P t).extExchangeMatrix = extExchangeMatrix Q L`.

* The subpattern freezes `S = ∅`, after which there are `n - |∅|` mutable indices. This
  number is `n` by definition, so the relabelling `π` is `ReindexingMap.id` with no cast, and
  freezing at `∅` is the identity by `freezingFun_empty` and `matrixFreeze_empty`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 4–5*][FWZ17]
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### Connected components of a quiver -/

namespace Quiver

variable {V : Type*} [Fintype V] (Q : Quiver V)

/-- The **connected component** `C(v)` of a vertex `v` of a quiver: the vertices `u` for
which there is a sequence `v = w₀, w₁, …, w_r = u`, `r ≥ 0`, with
`a(w_{e-1}, w_e) + a(w_e, w_{e-1}) > 0` for every `e ∈ [1, r]`. -/
@[cluster_algebras "def_quiver_component"]
def component (v : V) : Set V :=
  {u | Relation.ReflTransGen (fun w w' => 0 < Q.arrows w w' + Q.arrows w' w) v u}

variable {Q}

/-- `u ∈ C(v)` exactly when `u` is reachable from `v` along steps joined by an arrow. -/
theorem mem_component_iff {v u : V} :
    u ∈ Q.component v ↔
      Relation.ReflTransGen (fun w w' => 0 < Q.arrows w w' + Q.arrows w' w) v u :=
  Iff.rfl

/-- **Membership in a connected component by sequences**: `u ∈ C(v)` exactly when there is a
sequence `v = w₀, w₁, …, w_r = u` of vertices with `a(w_{e-1}, w_e) + a(w_e, w_{e-1}) > 0`
for every step. -/
theorem mem_component_iff_exists_fin {v u : V} :
    u ∈ Q.component v ↔ ∃ (r : ℕ) (w : Fin (r + 1) → V), w 0 = v ∧ w (Fin.last r) = u ∧
      ∀ e : Fin r, 0 < Q.arrows (w e.castSucc) (w e.succ) + Q.arrows (w e.succ) (w e.castSucc) := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, fun _ => v, rfl, rfl, fun e => e.elim0⟩
    | @tail b c _ hbc ih =>
      obtain ⟨r, w, h0, hlast, hstep⟩ := ih
      refine ⟨r + 1, Fin.snoc w c, ?_, Fin.snoc_last _ _, fun e => ?_⟩
      · rw [← Fin.castSucc_zero, Fin.snoc_castSucc, h0]
      · induction e using Fin.lastCases with
        | last => rwa [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hlast]
        | cast i =>
          rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hstep i
  · rintro ⟨r, w, rfl, rfl, hstep⟩
    induction r with
    | zero => exact Relation.ReflTransGen.refl
    | succ r ih =>
      refine Relation.ReflTransGen.tail (ih (w ∘ Fin.castSucc) fun e => hstep e.castSucc) ?_
      simpa [Fin.succ_last] using hstep (Fin.last r)

/-- A vertex lies in its own connected component. -/
@[simp]
theorem mem_component_self (v : V) : v ∈ Q.component v :=
  Relation.ReflTransGen.refl

/-- A vertex joined by an arrow, in either direction, to a vertex of `C(v)` lies in `C(v)`. -/
theorem mem_component_of_mem_of_pos {v u w : V} (hu : u ∈ Q.component v)
    (huw : 0 < Q.arrows u w + Q.arrows w u) : w ∈ Q.component v :=
  Relation.ReflTransGen.tail hu huw

/-- **No arrow joins a connected component to its complement**: if `u ∈ C(v)` and `w ∉ C(v)`,
then `a(u, w) = a(w, u) = 0`. -/
theorem arrows_eq_zero_of_mem_component_of_notMem {v u w : V} (hu : u ∈ Q.component v)
    (hw : w ∉ Q.component v) : Q.arrows u w = 0 ∧ Q.arrows w u = 0 := by
  have : ¬0 < Q.arrows u w + Q.arrows w u := fun h => hw (mem_component_of_mem_of_pos hu h)
  omega

end Quiver

/-! ### The seed subpattern of a connected component -/

section Subpattern

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ} {V : Type*} [Fintype V]

/-- For a labelling `λ` of `Q` and `I = λ⁻¹(C(v))`, the enumeration `ι_I` is closed for
`B̃(Q, λ)`: no arrow joins a vertex of `C(v)` to one outside it. -/
theorem isClosedFor_enumerationMap_component (Q : Quiver V) (L : Labelling Q m n) (v : V)
    {I : Finset (Fin m)} (hI : (I : Set (Fin m)) = L.equiv ⁻¹' Q.component v) :
    (enumerationMap n I).IsClosedFor (mutableCard_le_card n I) (extExchangeMatrix Q L) := by
  have hmem : ∀ u, u ∈ I.map L.equiv.toEmbedding ↔ u ∈ Q.component v := fun u => by
    rw [Finset.mem_map_equiv, ← Finset.mem_coe, hI, Set.mem_preimage, Equiv.apply_symm_apply]
  rw [isClosedFor_enumerationMap_extExchangeMatrix_iff]
  exact fun u hu _ w hw =>
    Quiver.arrows_eq_zero_of_mem_component_of_notMem ((hmem u).mp hu) (mt (hmem w).mpr hw)

/-- **A connected component gives a seed subpattern** ([FWZ17], Lemma 4.2.7, third assertion):
let `P` be a seed pattern, `t` a vertex with `B̃(t) = B̃(Q, λ)`, `v` a vertex of `Q`,
`I = λ⁻¹(C(v))` and `F' = K(x_i : i ∈ I)`, the `x_i` being the extended cluster of `P(t)`.
Then there is a seed subpattern `P'` of `P` in `F'`, of rank `n_I`, whose seed at the root,
read in `F`, is the restricted seed `P(t)_I`.

Lemma 4.2.7 of [FWZ17] asks `v` to be mutable; the subpattern exists without it. Mutability gives
`n_I ≥ 1` (`one_le_mutableCard_component`). -/
@[cluster_algebras "lem_component_subpattern"]
theorem exists_isSeedSubpattern_component [CharZero K] {hmn : n ≤ m}
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t : RegularTree n)
    (Q : Quiver V) (L : Labelling Q m n) (hQ : (P t).extExchangeMatrix = extExchangeMatrix Q L)
    (v : V) {I : Finset (Fin m)} (hI : (I : Set (Fin m)) = L.equiv ⁻¹' Q.component v) :
    ∃ P' : RegularTree (mutableCard n I) →
        SeedData (IntermediateField.adjoin K ((P t).extCluster '' I)) I.card (mutableCard n I),
      IsSeedSubpattern hmn (mutableCard_le_card n I)
          (IntermediateField.adjoin K ((P t).extCluster '' I)).val P P' ∧
        (P' RegularTree.root).map (IntermediateField.adjoin K ((P t).extCluster '' I)).val
          = (P t).restrict I := by
  have hF : IntermediateField.adjoin K (Set.range ((P t).extCluster ∘ enumerationMap n I))
      = IntermediateField.adjoin K ((P t).extCluster '' I) := by
    rw [Set.range_comp, range_enumerationMap]
  rw [← hF]
  have h' := mutableCard_le_card n I
  obtain ⟨P', hP', hroot⟩ := exists_isSeedPattern h' RegularTree.root
    (IsLabeledSeed.reindexAdjoin K hmn h' (hP.1 t) (enumerationMap n I))
  have hr : (freezingMap hmn ∅).comp ((enumerationMap (n - (∅ : Finset (Fin n)).card) I).comp
      (ReindexingMap.id I.card (mutableCard n I))) = enumerationMap n I :=
    ReindexingMap.ext fun p => by
      rw [ReindexingMap.comp_apply, coe_freezingMap, freezingFun_empty]
      rfl
  have hmap : (P' RegularTree.root).map (IntermediateField.val _) = (P t).restrict I := by
    rw [hroot, SeedData.map_val_reindexAdjoin, SeedData.restrict_eq_reindex]
  refine ⟨P', isSeedSubpattern_of_map_eq_reindex hP' t RegularTree.root ∅ I rfl rfl
    (ReindexingMap.id _ _) ReindexingMap.isRestriction_id Function.bijective_id ?_ ?_, hmap⟩
  · rw [matrixFreeze_empty, hQ]
    exact isClosedFor_enumerationMap_component Q L v hI
  · rw [hr, hmap, SeedData.restrict_eq_reindex]

/-- **The component of a mutable vertex has a mutable index**: if `v` is a mutable vertex of
`Q` and `I = λ⁻¹(C(v))`, the rank `n_I` of the seed subpattern of
`exists_isSeedSubpattern_component` is at least `1`. -/
@[cluster_algebras "lem_component_subpattern"]
theorem one_le_mutableCard_component (Q : Quiver V) (L : Labelling Q m n) {v : V}
    (hv : v ∉ Q.frozen) {I : Finset (Fin m)}
    (hI : (I : Set (Fin m)) = L.equiv ⁻¹' Q.component v) : 1 ≤ mutableCard n I := by
  have hvI : L.equiv.symm v ∈ I := by
    rw [← Finset.mem_coe, hI, Set.mem_preimage, Equiv.apply_symm_apply]
    exact Quiver.mem_component_self v
  have hvn : (L.equiv.symm v : ℕ) < n := by
    have := (L.mem_frozen_iff (L.equiv.symm v)).not.mp
    rw [Equiv.apply_symm_apply] at this
    exact not_le.mp (this hv)
  exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hvI, hvn⟩⟩

end Subpattern

end ClusterAlgebras

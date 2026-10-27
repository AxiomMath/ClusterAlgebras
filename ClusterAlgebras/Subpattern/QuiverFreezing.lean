/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.ExchangeMatrix
public import ClusterAlgebras.Subpattern.Freezing

/-!
# Freezing a quiver

The *freezing* of a quiver `Q = (V, F, a)` at a set `S` of vertices is the quiver
`Fr_S(Q) = (V, F ∪ S, a')` in which the vertices of `S` are reclassified as frozen and the
arrows between two vertices of `F ∪ S` are removed: `a'(u, v) = 0` if `u, v ∈ F ∪ S`, and
`a'(u, v) = a(u, v)` otherwise (`ClusterAlgebras.Quiver.freeze`). It is again a quiver.

If `λ` is a labelling of `Q` and `S' = λ⁻¹(S)`, then `λ ∘ φ_{S'}` is a labelling of
`Fr_S(Q)` (`ClusterAlgebras.Labelling.freeze`), where `φ_{S'}` is the freezing map of `S'`,
and in this labelling the extended exchange matrix of `Fr_S(Q)` is the freezing of that of
`Q`, `B̃(Fr_S(Q), λ ∘ φ_{S'}) = Fr_{S'}(B̃(Q, λ))`
(`ClusterAlgebras.extExchangeMatrix_freeze`). This is freezing in the quiver case, following
[FWZ17, Definition 4.2.1].

## Main definitions

* `ClusterAlgebras.Quiver.freezeArrows`: the arrow system `a'` of the frozen quiver.
* `ClusterAlgebras.Quiver.freeze`: the freezing `Fr_S(Q)` of a quiver.
* `ClusterAlgebras.Labelling.mutablePreimage`: the set `S' = λ⁻¹(S)`, as a set of mutable
  indices.
* `ClusterAlgebras.Labelling.freeze`: the labelling `λ ∘ φ_{S'}` of `Fr_S(Q)`.

## Main results

* `ClusterAlgebras.Quiver.isArrowSystem_freezeArrows`,
  `ClusterAlgebras.Quiver.twoCycleFree_freezeArrows`,
  `ClusterAlgebras.Quiver.freezeArrows_eq_zero_of_frozen`: `Fr_S(Q)` is a quiver.
* `ClusterAlgebras.Labelling.map_castLE_mutablePreimage`: if `S` has no frozen vertex,
  `S'` is all of `λ⁻¹(S)`; `ClusterAlgebras.Labelling.card_mutablePreimage`: then
  `|S'| = |S|`, so `Fr_S(Q)` has `n - |S|` mutable vertices.
* `ClusterAlgebras.extExchangeMatrix_freeze`: `B̃(Fr_S(Q), λ ∘ φ_{S'}) = Fr_{S'}(B̃(Q, λ))`.

## Implementation notes

* FWZ assume `S ⊆ V \ F`. Neither the construction of `Fr_S(Q)`, nor the fact
  that it is a quiver, nor the labelling `λ ∘ φ_{S'}`, nor the identity of matrices needs
  this, so it is assumed (as `Disjoint S Q.frozen`) only where it is used: to show that
  `S'` is the whole preimage `λ⁻¹(S)` and that `|S'| = |S|`. Dropping it elsewhere is a
  generalisation.

* The freezing map acts on mutable indices `S' ⊆ [0, n)`, so `S'` is the `Finset (Fin n)`
  of the indices `j < n` with `λ(j) ∈ S`, the preimage of `S \ F`. When `S` has no frozen
  vertex this is the preimage `λ⁻¹(S)`, read in `[0, n)`
  (`Labelling.map_castLE_mutablePreimage`); in general it is the right set to freeze, and
  `λ ∘ φ_{S'}` is a labelling of `Fr_S(Q)` for every `S`.

* The number of mutable vertices of `Fr_S(Q)` is written `n - |S'|`, the type of the
  labelling being `Labelling (Q.freeze S) m (n - (L.mutablePreimage S).card)`, so that the
  identity of matrices is an equality of `m × (n - |S'|)` matrices, the type of
  `matrixFreeze L.le S'`. The count `n - |S|` is `Labelling.card_mutablePreimage`.

* As with `Quiver.mutate` and `Quiver.fullSubquiver`, the arrow system is a bare function
  (`Quiver.freezeArrows`) and the three quiver conditions on it are proved separately.

* The inverse of `λ ∘ φ_{S'}` is `Fintype.bijInv`, so that the labelling is computable.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 4–5*][FWZ17]
-/

@[expose] public section

namespace ClusterAlgebras

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Quiver

/-- The arrow system of the freezing of `Q` at `S`: no arrow joins two vertices of
`F ∪ S`, and the other arrow counts are those of `Q`. -/
def freezeArrows (Q : Quiver V) (S : Finset V) : V → V → ℕ :=
  fun u v => if u ∈ Q.frozen ∪ S ∧ v ∈ Q.frozen ∪ S then 0 else Q.arrows u v

/-- The frozen arrow system keeps the arrows out of a vertex outside `F ∪ S`. -/
theorem freezeArrows_of_notMem_left (Q : Quiver V) (S : Finset V) {u : V}
    (hu : u ∉ Q.frozen ∪ S) (v : V) : Q.freezeArrows S u v = Q.arrows u v :=
  if_neg fun h => hu h.1

/-- The frozen arrow system keeps the arrows into a vertex outside `F ∪ S`. -/
theorem freezeArrows_of_notMem_right (Q : Quiver V) (S : Finset V) (u : V) {v : V}
    (hv : v ∉ Q.frozen ∪ S) : Q.freezeArrows S u v = Q.arrows u v :=
  if_neg fun h => hv h.2

/-- Every frozen arrow count is `0` or the arrow count of `Q`. -/
theorem freezeArrows_eq_zero_or_eq (Q : Quiver V) (S : Finset V) (u v : V) :
    Q.freezeArrows S u v = 0 ∨ Q.freezeArrows S u v = Q.arrows u v :=
  ite_eq_or_eq _ _ _

/-- The frozen arrows form an arrow system: no vertex carries a loop, because no vertex
of `Q` does. -/
@[cluster_algebras "lem_quiver_freezing_is_quiver"]
theorem isArrowSystem_freezeArrows (Q : Quiver V) (S : Finset V) :
    IsArrowSystem (Q.freezeArrows S) := fun v =>
  (Q.freezeArrows_eq_zero_or_eq S v v).elim id fun h => h.trans (Q.isArrowSystem v)

/-- The frozen arrows are two-cycle-free, because those of `Q` are. -/
@[cluster_algebras "lem_quiver_freezing_is_quiver"]
theorem twoCycleFree_freezeArrows (Q : Quiver V) (S : Finset V) :
    TwoCycleFree (Q.freezeArrows S) := fun u v =>
  (Q.twoCycleFree u v).imp
    (fun h => (Q.freezeArrows_eq_zero_or_eq S u v).elim id fun h' => h'.trans h)
    (fun h => (Q.freezeArrows_eq_zero_or_eq S v u).elim id fun h' => h'.trans h)

/-- The frozen arrows join no two vertices of `F ∪ S`, by construction. -/
@[cluster_algebras "lem_quiver_freezing_is_quiver"]
theorem freezeArrows_eq_zero_of_frozen (Q : Quiver V) (S : Finset V) {u v : V}
    (hu : u ∈ Q.frozen ∪ S) (hv : v ∈ Q.frozen ∪ S) : Q.freezeArrows S u v = 0 :=
  if_pos ⟨hu, hv⟩

/-- The **freezing** `Fr_S(Q) = (V, F ∪ S, a')` of `Q` at `S ⊆ V`: the vertices of `S`
become frozen, and the arrows between two vertices of `F ∪ S` are removed. -/
@[cluster_algebras "def_quiver_freezing"]
def freeze (Q : Quiver V) (S : Finset V) : Quiver V where
  frozen := Q.frozen ∪ S
  arrows := Q.freezeArrows S
  isArrowSystem := Q.isArrowSystem_freezeArrows S
  twoCycleFree := Q.twoCycleFree_freezeArrows S
  frozen_eq_zero _ hu _ hv := Q.freezeArrows_eq_zero_of_frozen S hu hv

/-- The frozen vertices of `Fr_S(Q)` are those of `F ∪ S`. -/
@[simp]
theorem frozen_freeze (Q : Quiver V) (S : Finset V) : (Q.freeze S).frozen = Q.frozen ∪ S :=
  rfl

/-- The arrows of `Fr_S(Q)` are the frozen arrows. -/
@[simp]
theorem arrows_freeze (Q : Quiver V) (S : Finset V) : (Q.freeze S).arrows = Q.freezeArrows S :=
  rfl

/-- A vertex is frozen in `Fr_S(Q)` exactly when it is frozen in `Q` or lies in `S`. -/
theorem mem_frozen_freeze (Q : Quiver V) (S : Finset V) (v : V) :
    v ∈ (Q.freeze S).frozen ↔ v ∈ Q.frozen ∨ v ∈ S :=
  Finset.mem_union

end Quiver

variable {Q : Quiver V} {m n : ℕ}

namespace Labelling

/-- The **preimage** `S' = λ⁻¹(S)` of a set `S` of vertices, as the set of mutable indices
`j < n` with `λ(j) ∈ S`. If `S` has no frozen vertex, it is all of `λ⁻¹(S)`
(`Labelling.map_castLE_mutablePreimage`). -/
def mutablePreimage (L : Labelling Q m n) (S : Finset V) : Finset (Fin n) :=
  Finset.univ.filter fun j => L.equiv (Fin.castLE L.le j) ∈ S

/-- A mutable index lies in `S'` exactly when its vertex lies in `S`. -/
@[simp]
theorem mem_mutablePreimage (L : Labelling Q m n) (S : Finset V) (j : Fin n) :
    j ∈ L.mutablePreimage S ↔ L.equiv (Fin.castLE L.le j) ∈ S := by
  simp [mutablePreimage]

/-- **`S'` is the preimage `λ⁻¹(S)`**: if `S` has no frozen vertex, the indices of the
vertices of `S` are exactly the elements of `S'`, read as row indices. -/
@[cluster_algebras "lem_freezing_labelling"]
theorem map_castLE_mutablePreimage (L : Labelling Q m n) {S : Finset V}
    (hS : Disjoint S Q.frozen) :
    (L.mutablePreimage S).map (Fin.castLEEmb L.le) = S.map L.equiv.symm.toEmbedding := by
  ext i
  simp only [Finset.mem_map, mem_mutablePreimage, Fin.castLEEmb_apply,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, hj, L.equiv.symm_apply_apply _⟩
  · rintro ⟨v, hv, rfl⟩
    have hlt : (L.equiv.symm v : ℕ) < n := by
      rw [← not_le, ← L.mem_frozen_iff, Equiv.apply_symm_apply]
      exact Finset.disjoint_left.mp hS hv
    exact ⟨⟨_, hlt⟩, by simpa [Fin.castLE] using hv, by simp [Fin.castLE]⟩

/-- If `S` has no frozen vertex, then `|S'| = |S|`, so `Fr_S(Q)` has `n - |S|` mutable
vertices. -/
theorem card_mutablePreimage (L : Labelling Q m n) {S : Finset V}
    (hS : Disjoint S Q.frozen) : (L.mutablePreimage S).card = S.card := by
  rw [← Finset.card_map (Fin.castLEEmb L.le), L.map_castLE_mutablePreimage hS,
    Finset.card_map]

/-- The map `λ ∘ φ_{S'}` is a bijection. -/
theorem bijective_freeze (L : Labelling Q m n) (S : Finset V) :
    Function.Bijective fun p => L.equiv (freezingFun L.le (L.mutablePreimage S) p) :=
  L.equiv.bijective.comp (freezingFun_bijective L.le _)

/-- The labelling `λ ∘ φ_{S'}` of `Fr_S(Q)`, where `S' = λ⁻¹(S)`: the `p`-th vertex of
`Fr_S(Q)` is `λ(φ_{S'}(p))`, and the mutable vertices of `Fr_S(Q)` are those of index below
`n - |S'|`. -/
@[cluster_algebras "lem_freezing_labelling"]
def freeze (L : Labelling Q m n) (S : Finset V) :
    Labelling (Q.freeze S) m (n - (L.mutablePreimage S).card) where
  equiv :=
    { toFun := fun p => L.equiv (freezingFun L.le (L.mutablePreimage S) p)
      invFun := Fintype.bijInv (L.bijective_freeze S)
      left_inv := Fintype.leftInverse_bijInv (L.bijective_freeze S)
      right_inv := Fintype.rightInverse_bijInv (L.bijective_freeze S) }
  le := sub_card_le_of_le L.le _
  mem_frozen_iff p := by
    simp only [Equiv.coe_fn_mk, Quiver.mem_frozen_freeze]
    rcases lt_or_ge (p : ℕ) (n - (L.mutablePreimage S).card) with hp | hp
    · rw [freezingFun_of_lt L.le _ hp]
      have hk := Finset.mem_compl.mp ((L.mutablePreimage S)ᶜ.orderEmbOfFin_mem
        (card_compl_eq_sub_card _) ⟨p, hp⟩)
      rw [mem_mutablePreimage] at hk
      exact iff_of_false (not_or.mpr ⟨L.notMem_frozen _, hk⟩) (not_le.mpr hp)
    rcases lt_or_ge (p : ℕ) n with hp' | hp'
    · obtain ⟨k, hk, hpk⟩ := exists_mem_freezingFun_eq_castLE L.le _ hp hp'
      rw [hpk]
      exact iff_of_true (Or.inr ((L.mem_mutablePreimage S k).mp hk)) hp
    · rw [freezingFun_of_le L.le _ hp']
      exact iff_of_true (Or.inl ((L.mem_frozen_iff p).mpr hp')) hp

/-- The `p`-th vertex in the frozen labelling is `λ(φ_{S'}(p))`. -/
@[simp]
theorem freeze_equiv_apply (L : Labelling Q m n) (S : Finset V) (p : Fin m) :
    (L.freeze S).equiv p = L.equiv (freezingFun L.le (L.mutablePreimage S) p) :=
  rfl

end Labelling

/-- The extended exchange matrix of a frozen quiver is the frozen matrix:
`B̃(Fr_S(Q), λ ∘ φ_{S'}) = Fr_{S'}(B̃(Q, λ))`, where `S' = λ⁻¹(S)`. -/
@[cluster_algebras "lem_quiver_freezing_matrix"]
theorem extExchangeMatrix_freeze (L : Labelling Q m n) (S : Finset V) :
    extExchangeMatrix (Q.freeze S) (L.freeze S) =
      matrixFreeze L.le (L.mutablePreimage S) (extExchangeMatrix Q L) := by
  ext p q
  have hv := (L.freeze S).notMem_frozen q
  rw [Quiver.frozen_freeze] at hv
  simp only [extExchangeMatrix, matrixFreeze, Matrix.of_apply, Quiver.arrows_freeze,
    signedCount] at hv ⊢
  rw [Quiver.freezeArrows_of_notMem_right Q S _ hv,
    Quiver.freezeArrows_of_notMem_left Q S hv]
  rfl

end ClusterAlgebras

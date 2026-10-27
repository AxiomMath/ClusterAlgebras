/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Restriction.Enumeration
public import ClusterAlgebras.Restriction.FullSubquiver
public import ClusterAlgebras.ExchangeMatrix

/-!
# The labelling of a full subquiver

Let `Q = (V, F, a)` be a quiver with `m` vertices, `n` of them mutable, and let `λ` be a
labelling of `Q`. For `I ⊆ [0, m)` put `U = λ(I)`. Composing `λ` with the enumeration `ι_I`
of `I`, which lists the mutable elements of `I` before the frozen ones, numbers the vertices
of the full subquiver `Q_U` so that its `n_I` mutable vertices come first: `λ ∘ ι_I` is a
labelling of `Q_U` (`ClusterAlgebras.Labelling.restrict`). In that labelling the extended
exchange matrix of `Q_U` is the restriction to `I` of the extended exchange matrix of `Q`,
`B̃(Q_U, λ ∘ ι_I) = B̃(Q, λ)_I` (`ClusterAlgebras.extExchangeMatrix_fullSubquiver`).

## Main definitions

* `ClusterAlgebras.Labelling.restrict`: the labelling `λ ∘ ι_I` of `Q_{λ(I)}`.

## Main results

* `ClusterAlgebras.extExchangeMatrix_fullSubquiver`: `B̃(Q_U, λ ∘ ι_I) = B̃(Q, λ)_I`.

## Design decisions

* The set `U = λ(I)` is the image `I.map λ`, a `Finset V`, so that `Q_U` is the full
  subquiver `Quiver.fullSubquiver` on it, a quiver on the subtype `↥U`.

* The inverse of `λ ∘ ι_I` is `Fintype.bijInv`, the inverse of a bijection out of a finite
  type found by search, so that the labelling is computable.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras*,
  Chapter 4.
-/

@[expose] public section

namespace ClusterAlgebras

variable {V : Type*} [Fintype V] [DecidableEq V] {Q : Quiver V} {m n : ℕ}

omit [DecidableEq V] in
/-- The map `λ ∘ ι_I` from positions in `I` to the vertices of `U = λ(I)` is a bijection. -/
theorem Labelling.bijective_restrict (L : Labelling Q m n) (I : Finset (Fin m)) :
    Function.Bijective fun p : Fin I.card =>
      (⟨L.equiv (restrictionEnumeration n I p),
        Finset.mem_map_of_mem _ (restrictionEnumeration_mem n I p)⟩ :
          I.map L.equiv.toEmbedding) := by
  refine ⟨fun p p' h => restrictionEnumeration_injective n I
    (L.equiv.injective (congrArg Subtype.val h)), ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
  obtain ⟨p, hp⟩ : i ∈ Set.range (restrictionEnumeration n I) := by
    rw [range_restrictionEnumeration]
    exact hi
  exact ⟨p, Subtype.ext (by simp [hp])⟩

/-- **The restricted labelling** `λ ∘ ι_I` of the full subquiver `Q_U` on `U = λ(I)`: the
`p`-th vertex of `Q_U` is `λ(ι_I(p))`, and the mutable vertices of `Q_U` are those of index
below `n_I`. -/
@[cluster_algebras "lem_restricted_labelling"]
def Labelling.restrict (L : Labelling Q m n) (I : Finset (Fin m)) :
    Labelling (Q.fullSubquiver (I.map L.equiv.toEmbedding)) I.card (mutableCard n I) where
  equiv :=
    { toFun := fun p => ⟨L.equiv (restrictionEnumeration n I p),
        Finset.mem_map_of_mem _ (restrictionEnumeration_mem n I p)⟩
      invFun := Fintype.bijInv (L.bijective_restrict I)
      left_inv := Fintype.leftInverse_bijInv (L.bijective_restrict I)
      right_inv := Fintype.rightInverse_bijInv (L.bijective_restrict I) }
  le := mutableCard_le_card n I
  mem_frozen_iff p := by
    rw [Quiver.mem_frozen_fullSubquiver]
    simp only [Equiv.coe_fn_mk]
    rw [L.mem_frozen_iff, ← not_lt, ← not_lt, val_restrictionEnumeration_lt_iff]

/-- The `p`-th vertex in the restricted labelling is `λ(ι_I(p))`. -/
@[simp]
theorem Labelling.coe_restrict_equiv_apply (L : Labelling Q m n) (I : Finset (Fin m))
    (p : Fin I.card) :
    ((L.restrict I).equiv p : V) = L.equiv (restrictionEnumeration n I p) :=
  rfl

/-- **The extended exchange matrix of a full subquiver is a restriction**: for `U = λ(I)`,
`B̃(Q_U, λ ∘ ι_I) = B̃(Q, λ)_I`. Both entries at `(p, q)` are the signed count of arrows
between `λ(ι_I(p))` and `λ(ι_I(q))`, the arrows of `Q_U` being those of `Q`. -/
@[cluster_algebras "lem_full_subquiver_matrix"]
theorem extExchangeMatrix_fullSubquiver (L : Labelling Q m n) (I : Finset (Fin m)) :
    extExchangeMatrix (Q.fullSubquiver (I.map L.equiv.toEmbedding)) (L.restrict I) =
      matrixRestriction (extExchangeMatrix Q L) I := by
  ext p q
  rfl

end ClusterAlgebras

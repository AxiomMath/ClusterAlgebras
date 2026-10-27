/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeFG.F4

/-!
# Global foldability of the `E₆` lifts

The `E₆` quivers `Q_ε`, for `ε ∈ {1, -1}³`, are globally foldable for the action of `ℤ/2ℤ` on
`Fin 6` exchanging the two long arms of `E₆`. This is an exercise of [FWZ], stated here as an
`axiom`; the quiver of [FWZ]'s folding figure is `Q_{(-1, 1, -1)}`.

## Main results

* `isGloballyFoldable_matrixE₆Lift`: each `matrixE₆Lift ε` is globally foldable for the orbit
  labelling `e₆OrbitLabelling`.

## References

* [FWZ], Exercise `ex:E6F4`
-/


@[expose] public section

namespace ClusterAlgebras

namespace TypeFG

/-- For every `ε ∈ {1, -1}³`, the matrix `Q_ε` is globally foldable for the action of `ℤ/2ℤ`
on `Fin 6` and the orbit labelling `θ` of the `E₆` folding. -/
@[cluster_algebras "lem_fg_E6_foldable"]
axiom isGloballyFoldable_matrixE₆Lift (ε : Fin 3 → ℤˣ) :
    IsGloballyFoldable e₆OrbitLabelling le_rfl (matrixE₆Lift ε)

end TypeFG

end ClusterAlgebras

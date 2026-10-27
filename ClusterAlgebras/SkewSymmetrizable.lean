/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.External

/-!
# Mutation and sign-antisymmetry

An extended exchange matrix `B` is sign-antisymmetric when its principal part has zero diagonal
and `B i j > 0` exactly when `B j i < 0`. This file shows that matrix mutation preserves
sign-antisymmetry for extended skew-symmetrizable matrices.

## Main results

* `ClusterAlgebras.SignAntisymmetric.matrixMutation`: if `B` is sign-antisymmetric and extended
  skew-symmetrizable, then its mutation `μ_k(B)` in every direction `k` is sign-antisymmetric.

## Implementation notes

The proof uses that mutation preserves a skew-symmetrizing vector, which is taken from
`ClusterAlgebras.External`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}

/-- If `B` is sign-antisymmetric and extended skew-symmetrizable, then its mutation `μ_k(B)` in
any direction `k` is again sign-antisymmetric. -/
@[cluster_algebras "lem_matmut_preserves_sign_antisymmetric"]
theorem SignAntisymmetric.matrixMutation (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) R}
    (hB : SignAntisymmetric hmn B) (hskew : ExtSkewSymmetrizable hmn B) (k : Fin n) :
    SignAntisymmetric hmn (ClusterAlgebras.matrixMutation hmn B k) := by
  obtain ⟨d, hd⟩ := hskew.matrixMutation hmn k
  exact ⟨fun i => matrixMutation_diag_eq_zero hmn hB k i, fun i j => hd.pos_iff_neg i j⟩

end ClusterAlgebras

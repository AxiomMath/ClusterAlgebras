/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The cyclic shift of a square matrix

For an `n × n` matrix `B`, its cyclic shift `ρ(B)` has entries `ρ(B)ᵢⱼ = b_{π(i) π(j)}`, where
`π` is the permutation `i ↦ i - 1` of the indices, taken cyclically. FWZ index by
`[1, n]` with `π(1) = n`; here the indices are `Fin n`, so `π` sends `0` to `n - 1`, and it is
the inverse of Mathlib's `finRotate n`, which sends `i` to `i + 1` cyclically.

FWZ take `n ≥ 1`; nothing here uses it.
-/

@[expose] public section

namespace ClusterAlgebras

variable {α : Type*} {n : ℕ}

/-- The **cyclic shift** `ρ(B)` of an `n × n` matrix `B`: its entry in row `i` and column `j`
is the entry of `B` in row `π(i)` and column `π(j)`, where `π = (finRotate n)⁻¹` sends each
index `i` to `i - 1`, and `0` to `n - 1`. -/
@[cluster_algebras "def_cyclic_shift"]
def matrixCyclicShift (B : Matrix (Fin n) (Fin n) α) : Matrix (Fin n) (Fin n) α :=
  B.submatrix (finRotate n).symm (finRotate n).symm

/-- The entries of the cyclic shift. -/
@[simp]
theorem matrixCyclicShift_apply (B : Matrix (Fin n) (Fin n) α) (i j : Fin n) :
    matrixCyclicShift B i j = B ((finRotate n).symm i) ((finRotate n).symm j) :=
  rfl

end ClusterAlgebras

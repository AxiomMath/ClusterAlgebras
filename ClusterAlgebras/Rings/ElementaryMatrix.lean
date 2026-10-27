/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Data.Complex.Basic

/-!
# Elementary matrices

The elementary matrix `E_{ij}(s) = 1 + s e_{ij}` is Mathlib's `Matrix.transvection i j s`, the
identity plus `s` at position `(i, j)`.

## Main definitions

* `ClusterAlgebras.elementaryMatrix`: the complex `p × p` elementary matrix `E_{ij}(s)`.

## Main results

* `ClusterAlgebras.elementaryMatrix_eq`: `E_{ij}(s)` is the identity plus `s` times the matrix
  unit `e_{ij}`.

## Implementation notes

* FWZ take `p ≥ 2` and `i ≠ j`; the definition needs neither, and neither is assumed.
-/

@[expose] public section

namespace ClusterAlgebras

/-- The **elementary matrix** `E_{ij}(s) = 1 + s e_{ij}`: the complex `p × p` identity matrix
with `s` added at position `(i, j)`. This is Mathlib's `Matrix.transvection i j s`. -/
@[cluster_algebras "def_elementary_matrix"]
noncomputable abbrev elementaryMatrix {p : ℕ} (i j : Fin p) (s : ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.transvection i j s

/-- `E_{ij}(s)` is the identity plus `s` times the matrix unit `e_{ij}`. -/
@[cluster_algebras "def_elementary_matrix"]
theorem elementaryMatrix_eq {p : ℕ} (i j : Fin p) (s : ℂ) :
    elementaryMatrix i j s = 1 + s • Matrix.single i j 1 := by
  rw [elementaryMatrix, Matrix.transvection, Matrix.smul_single, smul_eq_mul, mul_one]

end ClusterAlgebras

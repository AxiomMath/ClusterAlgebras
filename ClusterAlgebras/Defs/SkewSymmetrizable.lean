/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.MatrixMutation

/-!
# Skew-symmetrizable matrices: the definitions

A square matrix is skew-symmetrizable when a tuple of positive integers rescales its rows
into a skew-symmetric matrix, and an `m × n` matrix is extended skew-symmetrizable when its
top `n × n` submatrix is.

The rescaling tuple is a definition of its own rather than being hidden inside the
existential, because two later results name a vector and compare it with another.

These live apart from the results about them so that `ClusterAlgebras.External` can state
the assumed FWZ exercise about them, and the results proved relative to that exercise can
then import the assumption.
-/

@[expose] public section

namespace ClusterAlgebras

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}

attribute [cluster_algebras "def_skew_symmetrizable"] IsSkewSymmetrizingVector

attribute [cluster_algebras "def_skew_symmetrizable"] SkewSymmetrizable

/-- `B` is **extended skew-symmetrizable** when its top `n × n` submatrix — the first
`n` rows — is skew-symmetrizable. -/
@[cluster_algebras "def_extended_skew_symmetrizable"]
def ExtSkewSymmetrizable (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) : Prop :=
  SkewSymmetrizable (B.submatrix (Fin.castLE hmn) id)

namespace IsSkewSymmetrizingVector

variable {B : Matrix (Fin n) (Fin n) R} {d : Fin n → ℤ}

/-- The rescaling factors are positive in `R`, not just in `ℤ`. -/
theorem cast_pos (hd : IsSkewSymmetrizingVector B d) (i : Fin n) : (0 : R) < (d i : R) := by
  exact_mod_cast hd.1 i

/-- **An entry is positive exactly when its mirror is negative.** The rescaling factors
are positive, so they cannot change a sign, and the defining identity then transfers the
sign across the diagonal. This is the only consequence of the identity that the results
below use. -/
theorem pos_iff_neg (hd : IsSkewSymmetrizingVector B d) (i j : Fin n) :
    0 < B i j ↔ B j i < 0 := by
  have hi := hd.cast_pos (R := R) i
  have hj := hd.cast_pos (R := R) j
  constructor <;> intro hb
  · nlinarith [mul_pos hi hb, hd.2 i j]
  · nlinarith [mul_neg_of_pos_of_neg hj hb, hd.2 i j]

end IsSkewSymmetrizingVector

end ClusterAlgebras

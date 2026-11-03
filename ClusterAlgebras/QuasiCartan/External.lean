/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ClusterAlgebras.QuasiCartan.Defs

/-!
# Mutation invariance of the Barot–Geiss–Zelevinsky condition

If a skew-symmetrizable integer matrix `B` satisfies the Barot–Geiss–Zelevinsky condition, then
so does every mutation of `B`. This is Lemma 4.1 of Barot, Geiss and Zelevinsky.

## Main results

* `SatisfiesBGZ.MatrixMutation`: mutation preserves the Barot–Geiss–Zelevinsky
  condition on skew-symmetrizable integer matrices.

## Implementation notes

The result is stated as the hypothesis `SatisfiesBGZ.MatrixMutation`.

## References

* M. Barot, C. Geiss, A. Zelevinsky, *Cluster algebras of finite type and positive
  symmetrizable matrices*, J. London Math. Soc. 73 (2006).
-/

@[expose] public section

namespace ClusterAlgebras

/-- If the skew-symmetrizable `n × n` integer matrix `B` satisfies the Barot–Geiss–Zelevinsky
condition, then so does its mutation `μ_k(B)` in every direction `k`. -/
@[cluster_algebras "ext_bgz_mutation_invariance"]
def SatisfiesBGZ.MatrixMutation : Prop :=
  ∀ {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (_ : SkewSymmetrizable B) (_ : SatisfiesBGZ B)
      (k : Fin n),
    SatisfiesBGZ (matrixMutation le_rfl B k)

end ClusterAlgebras

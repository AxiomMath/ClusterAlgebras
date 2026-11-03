/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ClusterAlgebras.Acyclic
public import ClusterAlgebras.Defs.MutationEquivalence
public import ClusterAlgebras.Defs.SkewSymmetrizable
public import ClusterAlgebras.Defs.SkewSymmetrization
public import ClusterAlgebras.TotalPositivity.Minor
public import ClusterAlgebras.Definitions

/-!
# Assumed results

The results that the library assumes rather than proves, each stated as a hypothesis
`def … : Prop`: identities about matrix and quiver mutation, the three-term Grassmann–Plücker
relation, the three-term relation for flag minors, and the Caldero–Keller theorem on mutation
equivalence of acyclic quivers. The library declares no `axiom`.

## Main results

* `PluckerCoordThreeTerm`: The three-term Grassmann–Plücker relation for `2 × m` matrices.
* `FlagMinorThreeTerm`: The three-term relation for flag minors.
* `MatrixMutationMatrixMutation`: Matrix mutation is an involution.
* `IsSkewSymmetrizingVector.SubmatrixMatrixMutation`: Matrix mutation preserves a
  skew-symmetrizing vector of the top square submatrix; `ExtSkewSymmetrizable.matrixMutation`
  derives from it that matrix mutation preserves extended skew-symmetrizability.
* `MatrixMutationNeg`: Matrix mutation commutes with negation.
* `MatrixMutationComm`: Matrix mutations at non-interacting indices commute.
* `Quiver.MutateMutate`: Quiver mutation is an involution.
* `SkewSymmetrizable.SkewSymmetrizationMatrixMutation`: Skew-symmetrization commutes with
  matrix mutation.
* `CalderoKeller`, stated in `ClusterAlgebras.Definitions`: Mutation equivalent acyclic quivers
  without frozen vertices are joined by mutations at sources and sinks.

All but the last are exercises in FWZ. Every result that depends on one of these takes it as an
explicit argument `(hX : X)`, so the assumptions a result rests on are visible in its statement.

## References

* S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*.
* P. Caldero, B. Keller, *From triangulated categories to cluster algebras II*,
  Ann. Sci. École Norm. Sup. (4) 39 (2006), no. 6, 983–1009.
-/

@[expose] public section

namespace ClusterAlgebras

universe u

/-! ### The three-term Grassmann–Plücker relation -/

attribute [cluster_algebras "lem_grassmann_plucker_three_term"]
    ClusterAlgebras.PluckerCoordThreeTerm
attribute [cluster_algebras "lem_matmut_involution"] ClusterAlgebras.MatrixMutationMatrixMutation
attribute [cluster_algebras "lem_matmut_preserves_skew_symmetrizable"]
    ClusterAlgebras.IsSkewSymmetrizingVector.SubmatrixMatrixMutation
attribute [cluster_algebras "lem_skew_symmetrization_mutation"]
    ClusterAlgebras.SkewSymmetrizable.SkewSymmetrizationMatrixMutation

/-! ### The three-term relation for flag minors -/

/-- **The three-term relation for flag minors.** For an `n × n` matrix, a set `S` of columns and
columns `a < b < c` outside `S`,
`P_{S∪{b}} P_{S∪{a,c}} = P_{S∪{a}} P_{S∪{b,c}} + P_{S∪{c}} P_{S∪{a,b}}`.

An exercise in FWZ, Section 1.3. -/
@[cluster_algebras "lem_flag_three_term"]
def FlagMinorThreeTerm : Prop :=
  ∀ {R : Type u} [CommRing R] {n : ℕ} (_ : 3 ≤ n) (z : Matrix (Fin n) (Fin n) R)
      (S : Finset (Fin n)) {a b c : Fin n} (_ : a ∉ S) (_ : b ∉ S) (_ : c ∉ S) (_ : a < b)
      (_ : b < c),
    flagMinor z (S ∪ {b}) * flagMinor z (S ∪ {a, c}) =
      flagMinor z (S ∪ {a}) * flagMinor z (S ∪ {b, c}) +
        flagMinor z (S ∪ {c}) * flagMinor z (S ∪ {a, b})

variable {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}

/-! ### Matrix mutation -/

/-- **Mutation preserves extended skew-symmetrizability.** If `B` is extended
skew-symmetrizable, then so is `μ_k(B)`. This follows from the preservation of a
skew-symmetrizing vector above. -/
@[cluster_algebras "lem_matmut_preserves_skew_symmetrizable"]
theorem ExtSkewSymmetrizable.matrixMutation
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{u}) (hmn : n ≤ m)
    {B : Matrix (Fin m) (Fin n) R}
    (hB : ExtSkewSymmetrizable hmn B) (k : Fin n) :
    ExtSkewSymmetrizable hmn (ClusterAlgebras.matrixMutation hmn B k) :=
  let ⟨d, hd⟩ := hB
  ⟨d, hSubmatrixMatrixMutation hmn hd k⟩

/-- **Mutation of a square matrix preserves a skew-symmetrizing vector.** If `d` skew-symmetrizes
`B`, then it skew-symmetrizes `μ_k(B)`. -/
theorem IsSkewSymmetrizingVector.matrixMutation
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{u})
    {B : Matrix (Fin n) (Fin n) R}
    {d : Fin n → ℤ} (hd : IsSkewSymmetrizingVector B d) (hnn : n ≤ n) (k : Fin n) :
    IsSkewSymmetrizingVector (ClusterAlgebras.matrixMutation hnn B k) d := by
  have hs : ∀ C : Matrix (Fin n) (Fin n) R, C.submatrix (Fin.castLE hnn) id = C := by
    intro C
    ext i j
    simp
  have h := hSubmatrixMatrixMutation hnn (C := B) (by rwa [hs]) k
  rwa [hs] at h

/-- **Matrix mutation commutes with negation**, `μ_k(-B) = -μ_k(B)`.

An exercise in FWZ on matrix mutation. -/
@[cluster_algebras "lem_matmut_neg"]
def MatrixMutationNeg : Prop :=
  ∀ {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ} (hmn : n ≤ m)
      (B : Matrix (Fin m) (Fin n) R) (k : Fin n),
    matrixMutation hmn (-B) k = -matrixMutation hmn B k

/-- **Matrix mutations at non-interacting indices commute.** If `k ≠ l` and
`b_{kl} = b_{lk} = 0`, then `μ_l(μ_k(B)) = μ_k(μ_l(B))`.

An exercise in FWZ on matrix mutation. -/
@[cluster_algebras "lem_matmut_commute"]
def MatrixMutationComm : Prop :=
  ∀ {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ} (hmn : n ≤ m)
      (B : Matrix (Fin m) (Fin n) R) {k l : Fin n} (_ : k ≠ l) (_ : B (Fin.castLE hmn k) l = 0)
      (_ : B (Fin.castLE hmn l) k = 0),
    matrixMutation hmn (matrixMutation hmn B k) l = matrixMutation hmn (matrixMutation hmn B l) k

/-! ### Quiver mutation -/

/-- **Quiver mutation is an involution**, `μ_k(μ_k(Q)) = Q` for a mutable vertex `k`.

An exercise in FWZ on quiver mutation. -/
@[cluster_algebras "lem_mut_involution"]
def Quiver.MutateMutate : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen),
      (Q.mutate hk).mutate hk = Q

/-! ### Skew-symmetrization and mutation -/

/-! ### The Caldero–Keller theorem

FWZ state it without proof; its proof uses cluster categories. -/

namespace Quiver

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The empty mutation path mutates only at sources and sinks. -/
@[simp]
theorem MutationPath.atSourceOrSink_nil (Q : Quiver V) : (MutationPath.nil Q).AtSourceOrSink :=
  trivial

/-- A mutation path starting with a mutation at `k` mutates only at sources and sinks if and only
if `k` is a source or a sink of `Q` and the rest of the path mutates only at sources and sinks of
`μ_k(Q)`. -/
@[simp]
theorem MutationPath.atSourceOrSink_cons {Q : Quiver V} {k : V} (hk : k ∉ Q.frozen)
    (p : (Q.mutate hk).MutationPath) :
    (MutationPath.cons hk p).AtSourceOrSink ↔
      (Q.IsSource k ∨ Q.IsSink k) ∧ p.AtSourceOrSink :=
  Iff.rfl

end Quiver

attribute [cluster_algebras "ext_caldero_keller"] ClusterAlgebras.CalderoKeller

end ClusterAlgebras

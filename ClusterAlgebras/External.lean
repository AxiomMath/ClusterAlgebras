/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Acyclic
public import ClusterAlgebras.Defs.MutationEquivalence
public import ClusterAlgebras.Defs.SkewSymmetrizable
public import ClusterAlgebras.Defs.SkewSymmetrization
public import ClusterAlgebras.TotalPositivity.Minor

/-!
# Assumed results

The results that the library assumes as axioms rather than proves: identities about matrix
and quiver mutation, the three-term Grassmann–Plücker relation, the three-term relation for
flag minors, and the Caldero–Keller theorem on mutation equivalence of acyclic quivers.

## Main results

* `pluckerCoord_three_term`: The three-term Grassmann–Plücker relation for `2 × m` matrices.
* `flagMinor_three_term`: The three-term relation for flag minors.
* `matrixMutation_matrixMutation`: Matrix mutation is an involution.
* `IsSkewSymmetrizingVector.submatrix_matrixMutation`: Matrix mutation preserves a
  skew-symmetrizing vector of the top square submatrix.
* `ExtSkewSymmetrizable.matrixMutation`: Matrix mutation preserves extended
  skew-symmetrizability.
* `matrixMutation_neg`: Matrix mutation commutes with negation.
* `matrixMutation_comm`: Matrix mutations at non-interacting indices commute.
* `Quiver.mutate_mutate`: Quiver mutation is an involution.
* `SkewSymmetrizable.skewSymmetrization_matrixMutation`: Skew-symmetrization commutes with
  matrix mutation.
* `caldero_keller`: Mutation equivalent acyclic quivers without frozen vertices are joined by
  mutations at sources and sinks.

## References

* S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*.
* P. Caldero, B. Keller, *From triangulated categories to cluster algebras II*,
  Ann. Sci. École Norm. Sup. (4) 39 (2006), no. 6, 983–1009.
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### The three-term Grassmann–Plücker relation -/

/-- **The three-term Grassmann–Plücker relation.** For a `2 × m` matrix and columns
`i < j < k < l`, `P_{ik} P_{jl} = P_{ij} P_{kl} + P_{il} P_{jk}`. -/
@[cluster_algebras "lem_grassmann_plucker_three_term"]
axiom pluckerCoord_three_term {R : Type*} [CommRing R] {m : ℕ} (hm : 4 ≤ m)
    (z : Matrix (Fin 2) (Fin m) R) {i j k l : Fin m} (hij : i < j) (hjk : j < k) (hkl : k < l) :
    pluckerCoord z {i, k} * pluckerCoord z {j, l} =
      pluckerCoord z {i, j} * pluckerCoord z {k, l} + pluckerCoord z {i, l} * pluckerCoord z {j, k}

/-! ### The three-term relation for flag minors -/

/-- **The three-term relation for flag minors.** For an `n × n` matrix, a set `S` of columns and
columns `a < b < c` outside `S`,
`P_{S∪{b}} P_{S∪{a,c}} = P_{S∪{a}} P_{S∪{b,c}} + P_{S∪{c}} P_{S∪{a,b}}`. -/
@[cluster_algebras "lem_flag_three_term"]
axiom flagMinor_three_term {R : Type*} [CommRing R] {n : ℕ} (hn : 3 ≤ n)
    (z : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)) {a b c : Fin n}
    (ha : a ∉ S) (hb : b ∉ S) (hc : c ∉ S) (hab : a < b) (hbc : b < c) :
    flagMinor z (S ∪ {b}) * flagMinor z (S ∪ {a, c}) =
      flagMinor z (S ∪ {a}) * flagMinor z (S ∪ {b, c}) +
        flagMinor z (S ∪ {c}) * flagMinor z (S ∪ {a, b})

variable {R : Type*} [CommRing R] [LinearOrder R] {m n : ℕ}

/-! ### Matrix mutation -/

/-- **Matrix mutation is an involution**, `μ_k(μ_k(B)) = B`. -/
@[cluster_algebras "lem_matmut_involution"]
axiom matrixMutation_matrixMutation [IsStrictOrderedRing R] (hmn : n ≤ m)
    (B : Matrix (Fin m) (Fin n) R) (k : Fin n) :
    matrixMutation hmn (matrixMutation hmn B k) k = B

/-- **Mutation preserves a skew-symmetrizing vector of the top submatrix.** If `d`
skew-symmetrizes the top `n × n` submatrix of `C`, then it skew-symmetrizes the top `n × n`
submatrix of `μ_k(C)`. -/
@[cluster_algebras "lem_matmut_preserves_skew_symmetrizable"]
axiom IsSkewSymmetrizingVector.submatrix_matrixMutation [IsStrictOrderedRing R] (hmn : n ≤ m)
    {C : Matrix (Fin m) (Fin n) R} {d : Fin n → ℤ}
    (hd : IsSkewSymmetrizingVector (C.submatrix (Fin.castLE hmn) id) d) (k : Fin n) :
    IsSkewSymmetrizingVector ((matrixMutation hmn C k).submatrix (Fin.castLE hmn) id) d

/-- **Mutation preserves extended skew-symmetrizability.** If `B` is extended
skew-symmetrizable, then so is `μ_k(B)`. -/
@[cluster_algebras "lem_matmut_preserves_skew_symmetrizable"]
theorem ExtSkewSymmetrizable.matrixMutation [IsStrictOrderedRing R] (hmn : n ≤ m)
    {B : Matrix (Fin m) (Fin n) R}
    (hB : ExtSkewSymmetrizable hmn B) (k : Fin n) :
    ExtSkewSymmetrizable hmn (ClusterAlgebras.matrixMutation hmn B k) :=
  let ⟨d, hd⟩ := hB
  ⟨d, hd.submatrix_matrixMutation hmn k⟩

/-- **Mutation of a square matrix preserves a skew-symmetrizing vector.** If `d` skew-symmetrizes
`B`, then it skew-symmetrizes `μ_k(B)`. -/
theorem IsSkewSymmetrizingVector.matrixMutation [IsStrictOrderedRing R]
    {B : Matrix (Fin n) (Fin n) R} {d : Fin n → ℤ} (hd : IsSkewSymmetrizingVector B d) (hnn : n ≤ n)
    (k : Fin n) :
    IsSkewSymmetrizingVector (ClusterAlgebras.matrixMutation hnn B k) d := by
  have hs : ∀ C : Matrix (Fin n) (Fin n) R, C.submatrix (Fin.castLE hnn) id = C := by
    intro C
    ext i j
    simp
  have h := IsSkewSymmetrizingVector.submatrix_matrixMutation hnn (C := B) (by rwa [hs]) k
  rwa [hs] at h

/-- **Matrix mutation commutes with negation.** If `B` has zero diagonal, then
`μ_k(-B) = -μ_k(B)`. -/
@[cluster_algebras "lem_matmut_neg"]
axiom matrixMutation_neg [IsStrictOrderedRing R] (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) R}
    (hB : ∀ i : Fin n, B (Fin.castLE hmn i) i = 0) (k : Fin n) :
    matrixMutation hmn (-B) k = -matrixMutation hmn B k

/-- **Matrix mutations at non-interacting indices commute.** If `B` has zero diagonal and
`b_{kl} = b_{lk} = 0`, then `μ_l(μ_k(B)) = μ_k(μ_l(B))`. -/
@[cluster_algebras "lem_matmut_commute"]
axiom matrixMutation_comm [IsStrictOrderedRing R] (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) R}
    (hB : ∀ i : Fin n, B (Fin.castLE hmn i) i = 0) {k l : Fin n} (hkl : k ≠ l)
    (hkl₀ : B (Fin.castLE hmn k) l = 0) (hlk₀ : B (Fin.castLE hmn l) k = 0) :
    matrixMutation hmn (matrixMutation hmn B k) l = matrixMutation hmn (matrixMutation hmn B l) k

/-! ### Quiver mutation -/

/-- **Quiver mutation is an involution**, `μ_k(μ_k(Q)) = Q` for a mutable vertex `k`. -/
@[cluster_algebras "lem_mut_involution"]
axiom Quiver.mutate_mutate {V : Type*} [Fintype V] [DecidableEq V] (Q : Quiver V) {k : V}
    (hk : k ∉ Q.frozen) : (Q.mutate hk).mutate hk = Q

/-! ### Skew-symmetrization and mutation -/

/-- **Skew-symmetrization commutes with mutation**, `S(μ_k(B)) = μ_k(S(B))`. -/
@[cluster_algebras "lem_skew_symmetrization_mutation"]
axiom SkewSymmetrizable.skewSymmetrization_matrixMutation {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : SkewSymmetrizable B) (hnn : n ≤ n) (k : Fin n) :
    skewSymmetrization (ClusterAlgebras.matrixMutation hnn B k) =
      ClusterAlgebras.matrixMutation hnn (skewSymmetrization B) k

/-! ### The Caldero–Keller theorem -/

universe u

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

/-- **Caldero–Keller.** Two mutation equivalent acyclic quivers without frozen vertices are
joined by a sequence of mutations performed only at sources and sinks. -/
@[cluster_algebras "ext_caldero_keller"]
axiom caldero_keller {V V' : Type u} [Fintype V] [Fintype V'] [DecidableEq V]
    {Q : Quiver V} {Q' : Quiver V'} (hQ : Acyclic Q) (hQ' : Acyclic Q')
    (hfQ : Q.frozen = ∅) (hfQ' : Q'.frozen = ∅) (h : Q.MutationEquivalent Q') :
    ∃ p : Q.MutationPath, p.AtSourceOrSink ∧ Nonempty (p.result.Iso Q')

/-- The Caldero–Keller theorem, in the form of the proposition `CalderoKeller`. -/
theorem calderoKeller : CalderoKeller.{u} :=
  fun hQ hQ' hfQ hfQ' h => caldero_keller hQ hQ' hfQ hfQ' h

end ClusterAlgebras

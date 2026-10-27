/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Cartan.Counterpart
public import ClusterAlgebras.Defs.MatrixMutationEquiv
public import ClusterAlgebras.TreeOrientation
public import ClusterAlgebras.FiniteType.External
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# The exchange matrices of types `B_n` and `C_n`

A seed pattern is of type `B_n` (resp. `C_n`) in the sense of [FWZ, §5.5] when one of its
exchange matrices is, up to a simultaneous permutation of rows and columns, the matrix `M(B_n)`
(resp. `M(C_n)`). This file shows that this agrees with `IsPatternOfType`, which asks that the
Cartan counterpart of some exchange matrix be of the given type: the Cartan counterparts of
`M(B_n)` and `M(C_n)` are `C(B_n)` and `C(C_n)`, their Coxeter graph is the path `P_n`, a tree,
and skew-symmetrizable matrices with the same tree-shaped Cartan counterpart are related by
mutations at sinks and sources.

## Main definitions

* `ClusterAlgebras.typeBMatrix n`, `ClusterAlgebras.typeCMatrix n`: the matrices `M(B_n)` and
  `M(C_n)`.

## Main results

* `ClusterAlgebras.TypeBC.isFiniteTree_pathGraph`: the path graph `P_n` is a tree.
* `ClusterAlgebras.cartanCounterpart_typeBMatrix`, `cartanCounterpart_typeCMatrix`:
  `A(M(B_n)) = C(B_n)` and `A(M(C_n)) = C(C_n)`.
* `ClusterAlgebras.TypeBC.exists_matrixMutationList_eq_of_cartanCounterpart_eq`: two
  skew-symmetrizable matrices with the same Cartan counterpart, whose Coxeter graph is a tree,
  are related by a sequence of mutations.
* `ClusterAlgebras.TypeBC.exists_principalPart_apply_eq_of_sameCartanType`: a seed pattern
  one of whose Cartan counterparts has the type of `A(M₀)`, `M₀` tree-shaped, has a seed whose
  exchange matrix is a simultaneous permutation of `M₀`.
* `ClusterAlgebras.IsSeedPattern.isPatternOfType_B_iff`,
  `ClusterAlgebras.IsSeedPattern.isPatternOfType_C_iff`: a seed pattern is of type `B_n`
  (resp. `C_n`) in the sense of `IsPatternOfType` if and only if one of its exchange matrices
  is a simultaneous permutation of `M(B_n)` (resp. `M(C_n)`).

## Implementation notes

* Indices are `Fin n`, so the index `i` of [FWZ] is `i - 1` here. `M(B_n)` has `-2` in position
  `(0, 1)`, `1` in position `(1, 0)`, `-1` in the positions `(i, i + 1)`, `i ≥ 1`, and `1` in
  the positions `(i + 1, i)`; `M(C_n)` has `-1` in position `(0, 1)` and `2` in position
  `(1, 0)`, and agrees with `M(B_n)` elsewhere. Both are defined for every `n`, and are zero for
  `n ≤ 1`.
* The path graph `P_n` is `SimpleGraph.pathGraph n`, whose adjacency is `u + 1 = v ∨ v + 1 = u`
  (`SimpleGraph.pathGraph_adj`), with edges `{i, i+1}`.
* `coxeterGraph` is defined for all integer matrices, and is applied here to Cartan
  counterparts.
* "`A(B(t))` and `A(M₀)` have the same type" is `SameCartanType (A(B(t))) (A(M₀))`; the relation
  is symmetric, so the order of the arguments is immaterial.
* In `ClusterAlgebras.TypeBC.exists_principalPart_apply_eq_of_sameCartanType` no hypothesis
  `n ≥ 1` is needed: it follows from the Coxeter graph being a tree, since a tree is nonempty.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

/-! ### The matrices `M(B_n)` and `M(C_n)` -/

/-- **The exchange matrix of type `B_n`**: the `n × n` matrix `M(B_n)` with `b₁₂ = -2`,
`b₂₁ = 1`, `b_{i,i+1} = -1` and `b_{i+1,i} = 1` for `i ∈ [2, n-1]`, all other entries `0`. Here,
with indices shifted down by one: `-2` at `(0, 1)`, `-1` at `(i, i + 1)` for `i ≥ 1`, and `1` at
`(i + 1, i)` for all `i`. -/
@[cluster_algebras "def_type_BC_matrices"]
def typeBMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then -2
    else if (i : ℕ) + 1 = j then -1
    else if (j : ℕ) + 1 = i then 1
    else 0

/-- **The exchange matrix of type `C_n`**: the matrix `M(C_n)`, defined as `M(B_n)` except
that `b₁₂ = -1` and `b₂₁ = 2`. Here, with indices shifted down by one: `2` at `(1, 0)`, `-1` at
`(i, i + 1)` for all `i`, and `1` at `(i + 1, i)` for `i ≥ 1`. -/
@[cluster_algebras "def_type_BC_matrices"]
def typeCMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j =>
    if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then 2
    else if (i : ℕ) + 1 = j then -1
    else if (j : ℕ) + 1 = i then 1
    else 0

/-! ### The path graph and the Cartan counterparts -/

/-- A walk in the path graph from `u ≤ k` to `v > k` crosses the edge `{k, k + 1}`. -/
theorem TypeBC.pathGraph_mem_edges_of_walk {n : ℕ} (k : ℕ) (hk : k + 1 < n) :
    ∀ {u v : Fin n} (p : (SimpleGraph.pathGraph n).Walk u v), (u : ℕ) ≤ k → k < v →
      s((⟨k, by omega⟩ : Fin n), ⟨k + 1, hk⟩) ∈ p.edges := by
  intro u v p
  induction p with
  | nil => omega
  | @cons a b c h p ih =>
    intro hu hv
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
    by_cases hb : (b : ℕ) ≤ k
    · exact Or.inr (ih hb hv)
    · left
      rw [SimpleGraph.pathGraph_adj] at h
      have ha : (a : ℕ) = k := by omega
      have hb' : (b : ℕ) = k + 1 := by omega
      rw [Sym2.eq_iff]
      left
      exact ⟨Fin.ext ha.symm, Fin.ext hb'.symm⟩

/-- **The path graph is a tree.** For `n ≥ 1` the graph `P_n` on `[1, n]` with edges
`{i, i+1}`, which is Mathlib's `SimpleGraph.pathGraph n`, is a finite tree. -/
@[cluster_algebras "lem_bc_path_graph_tree"]
theorem TypeBC.isFiniteTree_pathGraph {n : ℕ} (hn : 1 ≤ n) :
    IsFiniteTree (SimpleGraph.pathGraph n : FiniteSimpleGraph (Fin n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨SimpleGraph.pathGraph_connected m, ?_⟩
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro v w h
  rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges]
  intro p
  rw [SimpleGraph.pathGraph_adj] at h
  rcases h with h | h
  · have hk : (v : ℕ) + 1 < m + 1 := h ▸ w.isLt
    have := TypeBC.pathGraph_mem_edges_of_walk v hk p le_rfl (by omega)
    rwa [show (⟨v + 1, hk⟩ : Fin (m + 1)) = w from Fin.ext h] at this
  · have hk : (w : ℕ) + 1 < m + 1 := h ▸ v.isLt
    have := TypeBC.pathGraph_mem_edges_of_walk w hk p.reverse le_rfl (by omega)
    rwa [show (⟨w + 1, hk⟩ : Fin (m + 1)) = v from Fin.ext h, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse, Sym2.eq_swap] at this

/-- **`M(B_n)` is skew-symmetrizable**, with skew-symmetrizing vector `(1, 2, …, 2)`. -/
@[cluster_algebras "lem_type_BC_matrices_cartan"]
theorem isSkewSymmetrizingVector_typeBMatrix (n : ℕ) :
    IsSkewSymmetrizingVector (typeBMatrix n) (fun i => if (i : ℕ) = 0 then 1 else 2) := by
  refine ⟨fun i => by dsimp only; split_ifs <;> norm_num, fun i j => ?_⟩
  simp only [typeBMatrix, of_apply, Int.cast_id]
  split_ifs <;> omega

/-- **`M(C_n)` is skew-symmetrizable**, with skew-symmetrizing vector `(2, 1, …, 1)`. -/
@[cluster_algebras "lem_type_BC_matrices_cartan"]
theorem isSkewSymmetrizingVector_typeCMatrix (n : ℕ) :
    IsSkewSymmetrizingVector (typeCMatrix n) (fun i => if (i : ℕ) = 0 then 2 else 1) := by
  refine ⟨fun i => by dsimp only; split_ifs <;> norm_num, fun i j => ?_⟩
  simp only [typeCMatrix, of_apply, Int.cast_id]
  split_ifs <;> omega

/-- **The Cartan counterpart of `M(B_n)` is `C(B_n)`.** -/
@[cluster_algebras "lem_type_BC_matrices_cartan"]
theorem cartanCounterpart_typeBMatrix (n : ℕ) : cartanCounterpart (typeBMatrix n) = cartanB n := by
  ext i j
  simp only [cartanCounterpart, typeBMatrix, cartanB, cartanA, of_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- **The Cartan counterpart of `M(C_n)` is `C(C_n)`.** -/
@[cluster_algebras "lem_type_BC_matrices_cartan"]
theorem cartanCounterpart_typeCMatrix (n : ℕ) : cartanCounterpart (typeCMatrix n) = cartanC n := by
  ext i j
  simp only [cartanCounterpart, typeCMatrix, cartanC, cartanA, of_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- **The Coxeter graph of `A(M(B_n))` is the path graph `P_n`.** -/
@[cluster_algebras "lem_type_BC_matrices_cartan"]
theorem coxeterGraph_cartanCounterpart_typeBMatrix (n : ℕ) :
    coxeterGraph (cartanCounterpart (typeBMatrix n)) = SimpleGraph.pathGraph n := by
  ext u v
  rw [cartanCounterpart_typeBMatrix, coxeterGraph_adj, SimpleGraph.pathGraph_adj]
  simp only [cartanB, cartanA, of_apply, ne_eq, Fin.ext_iff]
  split_ifs <;> (try simp) <;> omega

/-- **The Coxeter graph of `A(M(C_n))` is the path graph `P_n`.** -/
@[cluster_algebras "lem_type_BC_matrices_cartan"]
theorem coxeterGraph_cartanCounterpart_typeCMatrix (n : ℕ) :
    coxeterGraph (cartanCounterpart (typeCMatrix n)) = SimpleGraph.pathGraph n := by
  ext u v
  rw [cartanCounterpart_typeCMatrix, coxeterGraph_adj, SimpleGraph.pathGraph_adj]
  simp only [cartanC, cartanA, of_apply, ne_eq, Fin.ext_iff]
  split_ifs <;> (try simp) <;> omega

/-- **The Coxeter graph of `A(M(B_n))` is a finite tree** for `n ≥ 1`. -/
@[cluster_algebras "lem_type_BC_matrices_cartan"]
theorem isFiniteTree_coxeterGraph_cartanCounterpart_typeBMatrix {n : ℕ} (hn : 1 ≤ n) :
    IsFiniteTree (coxeterGraph (cartanCounterpart (typeBMatrix n))) := by
  rw [coxeterGraph_cartanCounterpart_typeBMatrix]
  exact TypeBC.isFiniteTree_pathGraph hn

/-- **The Coxeter graph of `A(M(C_n))` is a finite tree** for `n ≥ 1`. -/
@[cluster_algebras "lem_type_BC_matrices_cartan"]
theorem isFiniteTree_coxeterGraph_cartanCounterpart_typeCMatrix {n : ℕ} (hn : 1 ≤ n) :
    IsFiniteTree (coxeterGraph (cartanCounterpart (typeCMatrix n))) := by
  rw [coxeterGraph_cartanCounterpart_typeCMatrix]
  exact TypeBC.isFiniteTree_pathGraph hn

/-! ### Changing the orientation -/

namespace TypeBC

variable {n : ℕ}

/-- The arrow counts `a_C(i, j)` of a square integer matrix: `1` if `cᵢⱼ > 0`, else `0`. -/
def signArrows (C : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℕ := if 0 < C i j then 1 else 0

/-- A skew-symmetrizable matrix has zero diagonal. -/
theorem diag_eq_zero_of_isSkewSymmetrizingVector {C : Matrix (Fin n) (Fin n) ℤ} {d : Fin n → ℤ}
    (hd : IsSkewSymmetrizingVector C d) (i : Fin n) : C i i = 0 := by
  have h := hd.2 i i
  simp only [Int.cast_id] at h
  exact (mul_eq_zero.1 (by linarith : d i * C i i = 0)).resolve_left (hd.1 i).ne'

/-- The sign arrows of a skew-symmetrizable `C` orient the Coxeter graph of `A(C)`. -/
theorem exists_isOrientation_signArrows {C : Matrix (Fin n) (Fin n) ℤ} {d : Fin n → ℤ}
    (hd : IsSkewSymmetrizingVector C d) :
    ∃ Q : Quiver (Fin n), Q.arrows = signArrows C ∧ Q.frozen = ∅ ∧
      Q.IsOrientation (coxeterGraph (cartanCounterpart C)) := by
  apply orientation_of_arrow_counts
  · intro v
    simp [signArrows, diag_eq_zero_of_isSkewSymmetrizingVector hd v]
  · intro u v h
    rw [coxeterGraph_adj] at h
    obtain ⟨huv, h⟩ := h
    have h1 := hd.pos_iff_neg u v
    have h2 := hd.pos_iff_neg v u
    simp only [cartanCounterpart, of_apply, if_neg huv, if_neg (Ne.symm huv), ne_eq, neg_eq_zero,
      abs_eq_zero] at h
    simp only [signArrows]
    split_ifs <;> omega
  · intro u v huv h
    rw [coxeterGraph_adj, not_and, not_or] at h
    have := (h huv).1
    simp only [cartanCounterpart, of_apply, if_neg huv, ne_eq, neg_eq_zero, abs_eq_zero,
      not_not] at this
    simp [signArrows, this]

/-- A skew-symmetrizable matrix is determined by its Cartan counterpart and its sign arrows. -/
theorem eq_of_cartanCounterpart_eq_of_signArrows_eq {C C' : Matrix (Fin n) (Fin n) ℤ}
    {d d' : Fin n → ℤ} (hd : IsSkewSymmetrizingVector C d) (hd' : IsSkewSymmetrizingVector C' d')
    (hA : cartanCounterpart C = cartanCounterpart C') (ha : signArrows C = signArrows C') :
    C = C' := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diag_eq_zero_of_isSkewSymmetrizingVector hd, diag_eq_zero_of_isSkewSymmetrizingVector hd']
  have habs : |C i j| = |C' i j| := by
    simpa [cartanCounterpart, hij] using congrFun (congrFun hA i) j
  have hij' := congrFun (congrFun ha i) j
  have hji' := congrFun (congrFun ha j) i
  have h1 := hd.pos_iff_neg j i
  have h2 := hd'.pos_iff_neg j i
  simp only [signArrows] at hij' hji'
  rcases abs_eq_abs.1 habs with h | h
  · exact h
  · split_ifs at hij' hji' <;> omega

/-- Mutation of a skew-symmetrizable matrix at an index `k` whose column is nonpositive, or whose
row is nonpositive, only negates the row and the column `k`. -/
theorem matrixMutation_eq_of_sourceOrSink {C : Matrix (Fin n) (Fin n) ℤ} {d : Fin n → ℤ}
    (hd : IsSkewSymmetrizingVector C d) {k : Fin n}
    (hk : (∀ v, C v k ≤ 0) ∨ ∀ v, C k v ≤ 0) (i j : Fin n) :
    matrixMutation le_rfl C k i j = if i = k ∨ j = k then -C i j else C i j := by
  by_cases h : i = k ∨ j = k
  · rw [if_pos h]
    exact matrixMutation_apply_of_eq le_rfl C k h
  · rw [not_or] at h
    rw [if_neg (not_or.2 h), matrixMutation_apply_of_ne le_rfl C k h.1 h.2]
    simp only [castLE_self]
    have h1 := hd.pos_iff_neg i k
    have h2 := hd.pos_iff_neg k i
    have h3 := hd.pos_iff_neg k j
    have h4 := hd.pos_iff_neg j k
    rcases hk with hk | hk <;> have := hk i <;> have := hk j <;> split_ifs <;> first | rfl | omega

/-- Mutation at a source or a sink keeps the Cartan counterpart. -/
theorem cartanCounterpart_matrixMutation_of_sourceOrSink {C : Matrix (Fin n) (Fin n) ℤ}
    {d : Fin n → ℤ} (hd : IsSkewSymmetrizingVector C d) {k : Fin n}
    (hk : (∀ v, C v k ≤ 0) ∨ ∀ v, C k v ≤ 0) :
    cartanCounterpart (matrixMutation le_rfl C k) = cartanCounterpart C := by
  ext i j
  simp only [cartanCounterpart, of_apply, matrixMutation_eq_of_sourceOrSink hd hk]
  split_ifs <;> simp

/-- Mutation at a source or a sink `k` reverses the sign arrows at `k`. -/
theorem signArrows_matrixMutation_of_sourceOrSink {C : Matrix (Fin n) (Fin n) ℤ}
    {d : Fin n → ℤ} (hd : IsSkewSymmetrizingVector C d) {k : Fin n}
    (hk : (∀ v, C v k ≤ 0) ∨ ∀ v, C k v ≤ 0) :
    signArrows (matrixMutation le_rfl C k) = reversal (signArrows C) k := by
  funext i j
  simp only [signArrows, reversal, matrixMutation_eq_of_sourceOrSink hd hk]
  have := hd.pos_iff_neg j i
  split_ifs <;> omega

/-- A mutation path at sources and sinks of the sign quiver of a skew-symmetrizable `C` is
followed by a sequence of matrix mutations of `C`, which keep the skew-symmetrizing vector and the
Cartan counterpart and whose sign quiver is the end of the path. -/
theorem exists_matrixMutationList_of_mutationPath :
    ∀ {Q : Quiver (Fin n)} (p : Q.MutationPath), p.AtSourceOrSink →
      ∀ (C : Matrix (Fin n) (Fin n) ℤ) {d : Fin n → ℤ}, IsSkewSymmetrizingVector C d →
        Q.arrows = signArrows C →
        ∃ s : List (Fin n), IsSkewSymmetrizingVector (matrixMutationList le_rfl C s) d ∧
          cartanCounterpart (matrixMutationList le_rfl C s) = cartanCounterpart C ∧
          p.result.arrows = signArrows (matrixMutationList le_rfl C s)
  | _, .nil _, _, C, _, hd, hQ => ⟨[], hd, rfl, hQ⟩
  | Q, .cons (k := k) hk p, hp, C, d, hd, hQ => by
      have hsk : (∀ v, C v k ≤ 0) ∨ ∀ v, C k v ≤ 0 := by
        refine hp.1.imp (fun hs v => ?_) (fun hs v => ?_) <;> have := hs v <;>
          rw [hQ, signArrows] at this <;> exact not_lt.1 fun h => by simp [h] at this
      have hQ' : (Q.mutate hk).arrows = signArrows (matrixMutation le_rfl C k) := by
        rw [signArrows_matrixMutation_of_sourceOrSink hd hsk, ← hQ]
        rcases hp.1 with hs | hs
        · exact Q.mutate_arrows_of_isSource hk hs
        · exact Q.mutate_arrows_of_isSink hk hs
      obtain ⟨s, hs1, hs2, hs3⟩ := exists_matrixMutationList_of_mutationPath p hp.2
        (matrixMutation le_rfl C k) (hd.matrixMutation le_rfl k) hQ'
      exact ⟨k :: s, hs1, hs2.trans (cartanCounterpart_matrixMutation_of_sourceOrSink hd hsk),
        hs3⟩

end TypeBC

/-- **Tree-shaped matrices with equal Cartan counterparts are related by mutations at sinks and
sources.** If `B` and `B'` are skew-symmetrizable `n × n` integer matrices with
`A(B) = A(B')` and the Coxeter graph of `A(B)` is a finite tree, then `μ_s(B) = B'` for some
finite sequence `s` of indices. -/
@[cluster_algebras "lem_tree_sign_patterns"]
theorem TypeBC.exists_matrixMutationList_eq_of_cartanCounterpart_eq {n : ℕ}
    {B B' : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B')
    (hA : cartanCounterpart B = cartanCounterpart B')
    (htree : IsFiniteTree (coxeterGraph (cartanCounterpart B))) :
    ∃ s : List (Fin n), matrixMutationList le_rfl B s = B' := by
  obtain ⟨d, hd⟩ := hB
  obtain ⟨d', hd'⟩ := hB'
  obtain ⟨Q, hQa, -, hQ⟩ := TypeBC.exists_isOrientation_signArrows hd
  obtain ⟨Q', hQa', -, hQ'⟩ := TypeBC.exists_isOrientation_signArrows hd'
  rw [← hA] at hQ'
  obtain ⟨p, hp, hpQ⟩ := Quiver.exists_mutationPath_of_isTreeOrientation htree hQ hQ'
  obtain ⟨s, hs1, hs2, hs3⟩ := TypeBC.exists_matrixMutationList_of_mutationPath p hp B hd hQa
  refine ⟨s, TypeBC.eq_of_cartanCounterpart_eq_of_signArrows_eq hs1 hd' (hs2.trans hA) ?_⟩
  rw [← hs3, hpQ, hQa']

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- The extended exchange matrix of a mutation along a sequence. -/
theorem TypeBC.extExchangeMatrix_seedMutationSeq (hmn : n ≤ m) (S : SeedData F m n)
    (s : List (Fin n)) :
    (seedMutationSeq hmn S s).extExchangeMatrix = matrixMutationList hmn S.extExchangeMatrix s := by
  induction s generalizing S with
  | nil => rfl
  | cons k s ih => exact ih (seedMutation hmn S k)

/-- The principal part commutes with mutation along a sequence. -/
theorem TypeBC.principalPart_matrixMutationList (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ)
    (s : List (Fin n)) :
    principalPart hmn (matrixMutationList hmn B s) =
      matrixMutationList le_rfl (principalPart hmn B) s := by
  induction s generalizing B with
  | nil => rfl
  | cons k s ih =>
    rw [matrixMutationList_cons, ih, principalPart_matrixMutation, matrixMutationList_cons]

/-- **A seed pattern whose Cartan type is a tree reaches a given matrix.** Let `M₀` be a
skew-symmetrizable `n × n` integer matrix whose Cartan counterpart has a finite tree as Coxeter
graph, and let `P` be a seed pattern with a vertex `t` such that `A(B(t))` and `A(M₀)` have the
same type. Then some seed `P t'` has exchange matrix `B(t')` with
`b_{π(i) π(j)}(t') = (M₀)ᵢⱼ` for a permutation `π`. -/
@[cluster_algebras "lem_pattern_reaches_standard"]
theorem TypeBC.exists_principalPart_apply_eq_of_sameCartanType [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    {M₀ : Matrix (Fin n) (Fin n) ℤ} (hM₀ : SkewSymmetrizable M₀)
    (htree : IsFiniteTree (coxeterGraph (cartanCounterpart M₀))) {t : RegularTree n}
    (ht : SameCartanType (cartanCounterpart (principalPart hmn (P t).extExchangeMatrix))
      (cartanCounterpart M₀)) :
    ∃ (t' : RegularTree n) (π : Equiv.Perm (Fin n)), ∀ i j,
      principalPart hmn (P t').extExchangeMatrix (π i) (π j) = M₀ i j := by
  obtain ⟨π, hπ⟩ := ht
  set Bt := principalPart hmn (P t).extExchangeMatrix with hBt
  obtain ⟨d, hd⟩ : SkewSymmetrizable Bt := ((hP.1 t).2 : _)
  have hB' : SkewSymmetrizable (Bt.submatrix π π) :=
    ⟨d ∘ π, fun i => hd.1 (π i), fun i j => hd.2 (π i) (π j)⟩
  have hA : cartanCounterpart (Bt.submatrix π π) = cartanCounterpart M₀ := by
    ext i j
    rw [hπ]
    simp [cartanCounterpart, π.injective.eq_iff]
  obtain ⟨s, hs⟩ := TypeBC.exists_matrixMutationList_eq_of_cartanCounterpart_eq hB' hM₀ hA
    (hA ▸ htree)
  obtain ⟨t', ht'⟩ := hP.seedMutationSeq_mem_range hmn t (s.map π)
  refine ⟨t', π, fun i j => ?_⟩
  rw [ht', TypeBC.extExchangeMatrix_seedMutationSeq, TypeBC.principalPart_matrixMutationList,
    ← hBt, ← hs, matrixMutationList_submatrix, submatrix_apply]

/-- The Cartan matrix of a one-symbol list is the Cartan matrix of the symbol. -/
theorem TypeBC.listCartan_singleton_apply (X : DynkinSymbol) (i j : Fin X.rank) :
    DynkinSymbol.listCartan [X] i j = X.cartan i j := by
  change fromBlocks X.cartan 0 0 (DynkinSymbol.listCartan [])
    (finSumFinEquiv.symm (Fin.castAdd (DynkinSymbol.listRank []) i))
    (finSumFinEquiv.symm (Fin.castAdd (DynkinSymbol.listRank []) j)) = _
  rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁]

/-- Having the same type is symmetric. -/
theorem TypeBC.sameCartanType_symm {A A' : Matrix (Fin n) (Fin n) ℤ} (h : SameCartanType A A') :
    SameCartanType A' A := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ.symm, fun i j => by rw [hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩

/-- Being of a type given by one symbol is having the same type as its Cartan matrix. -/
theorem TypeBC.isOfDynkinType_singleton_iff (X : DynkinSymbol)
    (A : Matrix (Fin X.rank) (Fin X.rank) ℤ) :
    IsOfDynkinType A [X] ↔ SameCartanType X.cartan A :=
  ⟨fun ⟨σ, h⟩ => ⟨σ, fun i j => (h i j).trans (TypeBC.listCartan_singleton_apply X _ _)⟩,
    fun ⟨σ, h⟩ => ⟨σ, fun i j => (h i j).trans (TypeBC.listCartan_singleton_apply X _ _).symm⟩⟩

omit [Field F] in
/-- A seed pattern with an exchange matrix that is a simultaneous permutation of `M₀` has a
Cartan counterpart of the same type as `A(M₀)`. -/
theorem TypeBC.sameCartanType_of_principalPart_apply_eq (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} {M₀ : Matrix (Fin n) (Fin n) ℤ} {t' : RegularTree n}
    {π : Equiv.Perm (Fin n)}
    (hπ : ∀ i j, principalPart hmn (P t').extExchangeMatrix (π i) (π j) = M₀ i j) :
    SameCartanType (cartanCounterpart M₀)
      (cartanCounterpart (principalPart hmn (P t').extExchangeMatrix)) := by
  refine ⟨π.symm, fun i j => ?_⟩
  simp only [cartanCounterpart, of_apply, ← hπ, Equiv.apply_symm_apply,
    π.symm.injective.eq_iff]

/-- **The patterns of type `B_n` as permuted `M(B_n)`.** For `n ≥ 2`, a seed pattern of
rank `n` is of type `B_n` if and only if one of its exchange matrices is a simultaneous
permutation of `M(B_n)`: `b_{π(i) π(j)}(t') = M(B_n)ᵢⱼ`. -/
@[cluster_algebras "lem_type_BC_standard_form"]
theorem IsSeedPattern.isPatternOfType_B_iff [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hn : 2 ≤ n) :
    IsPatternOfType hmn P [DynkinSymbol.B n hn] ↔
      ∃ (t' : RegularTree n) (π : Equiv.Perm (Fin n)), ∀ i j,
        principalPart hmn (P t').extExchangeMatrix (π i) (π j) = typeBMatrix n i j := by
  have key : ∀ A, IsOfDynkinType A [DynkinSymbol.B n hn] ↔
      SameCartanType (cartanCounterpart (typeBMatrix n)) A := by
    intro A
    rw [cartanCounterpart_typeBMatrix]
    exact TypeBC.isOfDynkinType_singleton_iff (DynkinSymbol.B n hn) A
  exact ⟨fun ⟨t, ht⟩ => TypeBC.exists_principalPart_apply_eq_of_sameCartanType hmn hP
      ⟨_, isSkewSymmetrizingVector_typeBMatrix n⟩
      (isFiniteTree_coxeterGraph_cartanCounterpart_typeBMatrix (by omega))
      (TypeBC.sameCartanType_symm ((key _).1 ht)),
    fun ⟨t', _, hπ⟩ => ⟨t', (key _).2 (TypeBC.sameCartanType_of_principalPart_apply_eq hmn hπ)⟩⟩

/-- **The patterns of type `C_n` as permuted `M(C_n)`.** For `n ≥ 3`, a seed pattern of
rank `n` is of type `C_n` if and only if one of its exchange matrices is a simultaneous
permutation of `M(C_n)`: `b_{π(i) π(j)}(t') = M(C_n)ᵢⱼ`. -/
@[cluster_algebras "lem_type_BC_standard_form"]
theorem IsSeedPattern.isPatternOfType_C_iff [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (hn : 3 ≤ n) :
    IsPatternOfType hmn P [DynkinSymbol.C n hn] ↔
      ∃ (t' : RegularTree n) (π : Equiv.Perm (Fin n)), ∀ i j,
        principalPart hmn (P t').extExchangeMatrix (π i) (π j) = typeCMatrix n i j := by
  have key : ∀ A, IsOfDynkinType A [DynkinSymbol.C n hn] ↔
      SameCartanType (cartanCounterpart (typeCMatrix n)) A := by
    intro A
    rw [cartanCounterpart_typeCMatrix]
    exact TypeBC.isOfDynkinType_singleton_iff (DynkinSymbol.C n hn) A
  exact ⟨fun ⟨t, ht⟩ => TypeBC.exists_principalPart_apply_eq_of_sameCartanType hmn hP
      ⟨_, isSkewSymmetrizingVector_typeCMatrix n⟩
      (isFiniteTree_coxeterGraph_cartanCounterpart_typeCMatrix (by omega))
      (TypeBC.sameCartanType_symm ((key _).1 ht)),
    fun ⟨t', _, hπ⟩ => ⟨t', (key _).2 (TypeBC.sameCartanType_of_principalPart_apply_eq hmn hπ)⟩⟩

end ClusterAlgebras

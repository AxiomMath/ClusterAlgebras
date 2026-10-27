/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.OrientationCheck

/-!
# The reference matrix for `E6`

Every exchange matrix `P` with `A(P) = C(E6)` is one of the `2^5` orientations of the
`E6` tree (`CertificateCheck.eq_orientMatrix`). For each orientation the table below gives a
mutation sequence `w`, of length at most `4`, and a permutation `τ` with
`μ_w(P) = (b_{τ(i) τ(j)})`, `B = refMatrix`; the kernel checks all of them.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E6Ref

open CertificateCheck

set_option maxRecDepth 100000

/-- The reference matrix. -/
def refMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
    -1, 0, 1, 0, 0, 0;
    0, -1, 0, 1, 0, 1;
    0, 0, -1, 0, 1, 0;
    0, 0, 0, -1, 0, 0;
    0, 0, -1, 0, 0, 0]

/-- The tails of the edges of the `E6` tree (the relation `dynkinERel 6`). -/
def src : Fin 5 → Fin 6 := ![0, 1, 2, 2, 3]

/-- The heads of the edges of the `E6` tree. -/
def dst : Fin 5 → Fin 6 := ![1, 2, 3, 5, 4]

/-- The index of a sign vector in the tables. -/
def code (ε : Fin 5 → Bool) : ℕ :=
  (List.finRange 5).foldr (fun e acc => (bif ε e then 1 else 0) + 2 * acc) 0

/-- The mutation sequences. -/
def wordTable : List (List (Fin 6)) :=
  [[5],
    [0, 5],
    [1, 0, 5],
    [1, 0, 5],
    [3, 4, 5],
    [0, 3, 4, 5],
    [0, 4, 5],
    [4, 5],
    [],
    [0],
    [1, 0],
    [1, 0],
    [3, 4],
    [0, 3, 4],
    [0, 4],
    [4],
    [4, 5],
    [0, 4, 5],
    [2, 1, 0],
    [2, 1, 0],
    [1, 0, 5],
    [1, 0, 5],
    [0, 5],
    [5],
    [4],
    [0, 4],
    [0, 3, 4],
    [3, 4],
    [1, 0],
    [1, 0],
    [0],
    []]

/-- The permutations. -/
def tauTable : List (List (Fin 6)) :=
  [[4, 3, 2, 1, 0, 5],
    [4, 3, 2, 1, 0, 5],
    [4, 3, 2, 1, 0, 5],
    [3, 4, 2, 1, 0, 5],
    [4, 3, 2, 1, 0, 5],
    [4, 3, 2, 1, 0, 5],
    [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5],
    [4, 3, 2, 1, 0, 5],
    [4, 3, 2, 1, 0, 5],
    [4, 3, 2, 1, 0, 5],
    [3, 4, 2, 1, 0, 5],
    [4, 3, 2, 1, 0, 5],
    [4, 3, 2, 1, 0, 5],
    [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5],
    [4, 3, 2, 1, 0, 5],
    [4, 3, 2, 1, 0, 5],
    [1, 0, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5],
    [1, 0, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5],
    [4, 3, 2, 1, 0, 5],
    [4, 3, 2, 1, 0, 5],
    [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5],
    [1, 0, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5]]

/-- The mutation sequence of an orientation. -/
def word (ε : Fin 5 → Bool) : List (Fin 6) :=
  wordTable.getD (code ε) []

/-- The permutation of an orientation. -/
def tau (ε : Fin 5 → Bool) (i : Fin 6) : Fin 6 :=
  (tauTable.getD (code ε) []).getD i 0

set_option maxHeartbeats 0 in
-- The kernel evaluation of the check exceeds the default heartbeat limit.
/-- For every orientation `ε`, mutating `orientMatrix src dst ε` along `word ε` gives
`refMatrix` relabelled by `tau ε`. -/
theorem mutation_check : ∀ ε : Fin 5 → Bool,
    matrixMutationList le_rfl (orientMatrix src dst ε) (word ε) =
      refMatrix.submatrix (tau ε) (tau ε) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of the check exceeds the default heartbeat limit.
/-- For every orientation `ε`, the map `tau ε` is a bijection. -/
theorem tau_bijective : ∀ ε : Fin 5 → Bool, Function.Bijective (tau ε) := by
  decide +kernel

/-- The Cartan matrix `cartanE 6` has `2` on the diagonal, `-1` at the pairs of vertices joined
by an edge `src e — dst e`, and `0` elsewhere. -/
theorem cartanE_eq : ∀ i j : Fin 6, cartanE 6 i j = if i = j then 2 else
    if (∃ e, src e = i ∧ dst e = j) ∨ (∃ e, src e = j ∧ dst e = i) then -1 else 0 := by
  decide +kernel

/-- No edge of the `E6` tree is a loop. -/
theorem src_ne_dst : ∀ e, src e ≠ dst e := by
  decide

/-- **Every exchange matrix of type `E6` mutates to a relabelling of `refMatrix`.** -/
theorem exists_matrixMutationList_eq (P : Matrix (Fin 6) (Fin 6) ℤ) (hP : SkewSymmetrizable P)
    (hA : cartanCounterpart P = cartanE 6) :
    ∃ (w : List (Fin 6)) (τ : Equiv.Perm (Fin 6)),
      matrixMutationList le_rfl P w = refMatrix.submatrix τ τ := by
  have hsym : (cartanCounterpart P).IsSymm := by
    rw [hA]
    unfold Matrix.IsSymm
    decide +kernel
  have h := eq_orientMatrix src dst src_ne_dst cartanE_eq
    (hP.eq_neg_of_isSymm_cartanCounterpart hsym) hA
  generalize (fun e => decide (0 < P (src e) (dst e))) = ε at h
  refine ⟨word ε, Equiv.ofBijective _ (tau_bijective ε), ?_⟩
  rw [Equiv.coe_ofBijective, h]
  exact mutation_check ε

end ClusterAlgebras.CertificateData.E6Ref

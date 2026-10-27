/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.OrientationCheck

/-!
# The reference matrix for `E7`

Every exchange matrix `P` with `A(P) = C(E7)` is one of the `2^6` orientations of the
`E7` tree (`CertificateCheck.eq_orientMatrix`). For each orientation the table below gives a
mutation sequence `w`, of length at most `5`, and a permutation `τ` with
`μ_w(P) = (b_{τ(i) τ(j)})`, `B = refMatrix`; the kernel checks all of them.

## Main results

* `exists_matrixMutationList_eq`: every skew-symmetrizable exchange matrix `P` with
  `A(P) = C(E7)` mutates to a relabelling of `refMatrix`.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E7Ref

open CertificateCheck

set_option maxRecDepth 100000

/-- The reference matrix. -/
def refMatrix : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, 1, 0, 0, 0, 0, 0;
    -1, 0, 1, 0, 0, 0, 0;
    0, -1, 0, 1, 0, 0, 1;
    0, 0, -1, 0, 1, 0, 0;
    0, 0, 0, -1, 0, 1, 0;
    0, 0, 0, 0, -1, 0, 0;
    0, 0, -1, 0, 0, 0, 0]

/-- The tails of the edges of the `E7` tree (the relation `dynkinERel 7`). -/
def src : Fin 6 → Fin 7 := ![0, 1, 2, 2, 3, 4]

/-- The heads of the edges of the `E7` tree. -/
def dst : Fin 6 → Fin 7 := ![1, 2, 3, 6, 4, 5]

/-- The index of a sign vector in the tables. -/
def code (ε : Fin 6 → Bool) : ℕ :=
  (List.finRange 6).foldr (fun e acc => (bif ε e then 1 else 0) + 2 * acc) 0

/-- The mutation sequences. -/
def wordTable : List (List (Fin 7)) :=
  [[2, 1, 0, 4, 5],
    [2, 1, 0, 4, 5],
    [0, 3, 4, 5, 6],
    [3, 4, 5, 6],
    [1, 0, 4, 5, 6],
    [1, 0, 4, 5, 6],
    [0, 4, 5, 6],
    [4, 5, 6],
    [1, 0, 3, 4, 5],
    [1, 0, 3, 4, 5],
    [0, 3, 4, 5],
    [3, 4, 5],
    [1, 0, 4, 5],
    [1, 0, 4, 5],
    [0, 4, 5],
    [4, 5],
    [2, 1, 0, 5],
    [2, 1, 0, 5],
    [2, 1, 0, 5],
    [2, 1, 0, 5],
    [1, 0, 5, 6],
    [1, 0, 5, 6],
    [0, 5, 6],
    [5, 6],
    [1, 0, 3, 4, 5],
    [1, 0, 3, 4, 5],
    [0, 3, 4, 5],
    [3, 4, 5],
    [1, 0, 5],
    [1, 0, 5],
    [0, 5],
    [5],
    [2, 1, 0, 4, 5],
    [2, 1, 0, 4, 5],
    [0, 3, 4, 5, 6],
    [3, 4, 5, 6],
    [3, 2, 1, 0],
    [3, 2, 1, 0],
    [0, 4, 5, 6],
    [4, 5, 6],
    [1, 0, 3, 4, 5],
    [1, 0, 3, 4, 5],
    [0, 3, 4, 5],
    [3, 4, 5],
    [1, 0, 4, 5],
    [1, 0, 4, 5],
    [0, 4, 5],
    [4, 5],
    [2, 1, 0],
    [2, 1, 0],
    [2, 1, 0],
    [2, 1, 0],
    [1, 0, 6],
    [1, 0, 6],
    [0, 6],
    [6],
    [6, 2, 1, 0],
    [6, 2, 1, 0],
    [0, 3, 4, 5],
    [3, 4, 5],
    [1, 0],
    [1, 0],
    [0],
    []]

/-- The permutations. -/
def tauTable : List (List (Fin 7)) :=
  [[2, 1, 0, 3, 5, 4, 6],
    [1, 2, 0, 3, 5, 4, 6],
    [0, 1, 2, 5, 4, 3, 6],
    [0, 1, 2, 5, 4, 3, 6],
    [1, 0, 2, 3, 5, 4, 6],
    [0, 1, 2, 3, 5, 4, 6],
    [0, 1, 2, 3, 5, 4, 6],
    [0, 1, 2, 3, 5, 4, 6],
    [1, 0, 2, 5, 4, 3, 6],
    [0, 1, 2, 5, 4, 3, 6],
    [0, 1, 2, 5, 4, 3, 6],
    [0, 1, 2, 5, 4, 3, 6],
    [1, 0, 2, 3, 5, 4, 6],
    [0, 1, 2, 3, 5, 4, 6],
    [0, 1, 2, 3, 5, 4, 6],
    [0, 1, 2, 3, 5, 4, 6],
    [2, 1, 0, 3, 4, 5, 6],
    [1, 2, 0, 3, 4, 5, 6],
    [1, 0, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [1, 0, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [1, 0, 2, 3, 5, 4, 6],
    [0, 1, 2, 3, 5, 4, 6],
    [0, 1, 2, 3, 5, 4, 6],
    [0, 1, 2, 3, 5, 4, 6],
    [1, 0, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [2, 1, 0, 3, 4, 5, 6],
    [1, 2, 0, 3, 4, 5, 6],
    [0, 1, 2, 5, 3, 4, 6],
    [0, 1, 2, 5, 3, 4, 6],
    [2, 1, 0, 3, 4, 5, 6],
    [1, 2, 0, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [1, 0, 2, 5, 3, 4, 6],
    [0, 1, 2, 5, 3, 4, 6],
    [0, 1, 2, 5, 3, 4, 6],
    [0, 1, 2, 5, 3, 4, 6],
    [1, 0, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [2, 1, 0, 3, 4, 5, 6],
    [1, 2, 0, 3, 4, 5, 6],
    [1, 0, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [1, 0, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [2, 1, 0, 3, 4, 5, 6],
    [1, 2, 0, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [1, 0, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 1, 2, 3, 4, 5, 6]]

/-- The mutation sequence of an orientation. -/
def word (ε : Fin 6 → Bool) : List (Fin 7) :=
  wordTable.getD (code ε) []

/-- The permutation of an orientation. -/
def tau (ε : Fin 6 → Bool) (i : Fin 7) : Fin 7 :=
  (tauTable.getD (code ε) []).getD i 0

set_option maxHeartbeats 0 in
-- The kernel evaluation of the check exceeds the default heartbeat limit.
/-- For every orientation `ε`, mutating `orientMatrix src dst ε` along `word ε` gives the
relabelling of `refMatrix` by `tau ε`. -/
theorem mutation_check : ∀ ε : Fin 6 → Bool,
    matrixMutationList le_rfl (orientMatrix src dst ε) (word ε) =
      refMatrix.submatrix (tau ε) (tau ε) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- The kernel evaluation of the check exceeds the default heartbeat limit.
/-- For every orientation `ε`, the map `tau ε` is a bijection. -/
theorem tau_bijective : ∀ ε : Fin 6 → Bool, Function.Bijective (tau ε) := by
  decide +kernel

/-- The Cartan matrix `cartanE 7` has diagonal entries `2`, entries `-1` at the endpoints of
an edge `src e — dst e`, and `0` elsewhere. -/
theorem cartanE_eq : ∀ i j : Fin 7, cartanE 7 i j = if i = j then 2 else
    if (∃ e, src e = i ∧ dst e = j) ∨ (∃ e, src e = j ∧ dst e = i) then -1 else 0 := by
  decide +kernel

/-- No edge of the `E7` tree is a loop. -/
theorem src_ne_dst : ∀ e, src e ≠ dst e := by
  decide

/-- **Every exchange matrix of type `E7` mutates to a relabelling of `refMatrix`.** -/
theorem exists_matrixMutationList_eq (P : Matrix (Fin 7) (Fin 7) ℤ) (hP : SkewSymmetrizable P)
    (hA : cartanCounterpart P = cartanE 7) :
    ∃ (w : List (Fin 7)) (τ : Equiv.Perm (Fin 7)),
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

end ClusterAlgebras.CertificateData.E7Ref

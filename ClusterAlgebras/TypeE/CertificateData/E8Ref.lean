/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.OrientationCheck

/-!
# The reference matrix for `E8`

Every exchange matrix `P` with `A(P) = C(E8)` is one of the `2^7` orientations of the
`E8` tree (`CertificateCheck.eq_orientMatrix`). For each orientation the table below gives a
mutation sequence `w`, of length at most `9`, and a permutation `τ` with
`μ_w(P) = (b_{τ(i) τ(j)})`, `B = refMatrix`; the kernel checks all of them.
-/

@[expose] public section

namespace ClusterAlgebras.CertificateData.E8Ref

open CertificateCheck

set_option maxRecDepth 100000

/-- The reference matrix. -/
def refMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 1, 0, 0, 1, -1, 0, 0;
    -1, 0, 1, 0, 0, 1, -1, 0;
    0, -1, 0, 1, 0, 0, 1, -1;
    0, 0, -1, 0, 0, 0, 0, 1;
    -1, 0, 0, 0, 0, 1, 0, 0;
    1, -1, 0, 0, -1, 0, 1, 0;
    0, 1, -1, 0, 0, -1, 0, 1;
    0, 0, 1, -1, 0, 0, -1, 0]

/-- The tails of the edges of the `E8` tree (the relation `dynkinERel 8`). -/
def src : Fin 7 → Fin 8 := ![0, 1, 2, 2, 3, 4, 5]

/-- The heads of the edges of the `E8` tree. -/
def dst : Fin 7 → Fin 8 := ![1, 2, 3, 7, 4, 5, 6]

/-- The index of a sign vector in the tables. -/
def code (ε : Fin 7 → Bool) : ℕ :=
  (List.finRange 7).foldr (fun e acc => (bif ε e then 1 else 0) + 2 * acc) 0

/-- The mutation sequences. -/
def wordTable : List (List (Fin 8)) :=
  [[1, 3, 2, 4, 5, 7, 2],
    [0, 1, 3, 2, 4, 5, 7, 2],
    [0, 1, 3, 2, 4, 5, 7, 2],
    [1, 3, 2, 4, 5, 7, 2],
    [2, 1, 3, 4, 5, 2, 7],
    [0, 2, 1, 3, 4, 5, 2, 7],
    [2, 1, 0, 7, 3, 4, 1, 5],
    [1, 2, 0, 3, 4, 5, 0, 7],
    [1, 3, 2, 4, 7, 5],
    [0, 1, 3, 2, 4, 7, 5],
    [0, 1, 3, 2, 4, 7, 5],
    [1, 3, 2, 4, 7, 5],
    [7, 2, 1, 3, 4, 5, 2, 7],
    [1, 2, 3, 1, 4, 5, 7, 3],
    [2, 3, 1, 4, 5, 7, 3],
    [0, 2, 3, 1, 4, 5, 7, 3],
    [2, 3, 1, 4, 5, 3, 7],
    [0, 2, 3, 1, 4, 5, 3, 7],
    [7, 2, 1, 3, 4, 5, 7, 2],
    [0, 7, 2, 1, 3, 4, 5, 7, 2],
    [1, 2, 3, 1, 4, 5, 7],
    [0, 1, 2, 3, 1, 4, 5, 7],
    [0, 1, 2, 3, 0, 4, 5, 7],
    [1, 2, 3, 0, 4, 5, 7],
    [0, 2, 1, 3, 4, 5, 7, 1],
    [2, 1, 3, 4, 5, 7, 1],
    [2, 1, 3, 4, 5, 7, 2],
    [0, 2, 1, 3, 4, 5, 7, 2],
    [1, 3, 2, 5, 4, 6, 7, 2],
    [0, 1, 3, 2, 5, 4, 6, 7, 2],
    [0, 2, 3, 1, 4, 5, 1, 7],
    [2, 3, 1, 4, 5, 1, 7],
    [2, 3, 1, 4, 5, 1, 7],
    [0, 2, 3, 1, 4, 5, 1, 7],
    [7, 2, 1, 3, 4, 5, 7, 2],
    [0, 7, 2, 1, 3, 4, 5, 7, 2],
    [2, 1, 3, 4, 2, 5, 7],
    [0, 2, 1, 3, 4, 2, 5, 7],
    [2, 1, 3, 4, 6, 5, 7, 1],
    [1, 2, 0, 3, 4, 0, 5, 7],
    [0, 2, 1, 3, 4, 5, 7, 1],
    [2, 1, 3, 4, 5, 7, 1],
    [2, 1, 3, 4, 5, 7, 2],
    [0, 2, 1, 3, 4, 5, 7, 2],
    [7, 2, 1, 3, 4, 2, 5, 7],
    [0, 7, 2, 1, 3, 4, 2, 5, 7],
    [0, 2, 3, 1, 4, 5, 3, 7],
    [2, 3, 1, 4, 5, 3, 7],
    [2, 1, 3, 4, 1, 5, 7],
    [0, 2, 1, 3, 4, 1, 5, 7],
    [0, 1, 2, 0, 3, 4, 2, 5, 7],
    [1, 2, 0, 3, 4, 2, 5, 7],
    [1, 3, 2, 4, 6, 7, 5],
    [2, 1, 3, 4, 5, 7, 2],
    [2, 1, 3, 4, 5, 7, 1],
    [1, 3, 2, 4, 6, 7, 5],
    [1, 2, 0, 3, 4, 5, 0, 7],
    [2, 1, 4, 3, 5, 6, 7, 1],
    [0, 2, 1, 3, 4, 5, 2, 7],
    [2, 1, 3, 4, 5, 2, 7],
    [1, 0, 2, 3, 4, 0, 5, 7],
    [1, 0, 2, 3, 4, 1, 5, 7],
    [0, 2, 3, 4, 1, 5, 7],
    [2, 3, 4, 1, 5, 7],
    [2, 3, 4, 1, 5, 7],
    [0, 2, 3, 4, 1, 5, 7],
    [1, 0, 2, 3, 4, 1, 5, 7],
    [1, 0, 2, 3, 4, 0, 5, 7],
    [2, 1, 3, 4, 5, 2, 7],
    [0, 2, 1, 3, 4, 5, 2, 7],
    [2, 1, 4, 3, 5, 6, 7, 1],
    [1, 2, 0, 3, 4, 5, 0, 7],
    [1, 3, 2, 4, 6, 7, 5],
    [2, 1, 3, 4, 5, 7, 1],
    [2, 1, 3, 4, 5, 7, 2],
    [1, 3, 2, 4, 6, 7, 5],
    [1, 2, 0, 3, 4, 2, 5, 7],
    [0, 1, 2, 0, 3, 4, 2, 5, 7],
    [0, 2, 1, 3, 4, 1, 5, 7],
    [2, 1, 3, 4, 1, 5, 7],
    [2, 3, 1, 4, 5, 3, 7],
    [0, 2, 3, 1, 4, 5, 3, 7],
    [0, 7, 2, 1, 3, 4, 2, 5, 7],
    [7, 2, 1, 3, 4, 2, 5, 7],
    [0, 2, 1, 3, 4, 5, 7, 2],
    [2, 1, 3, 4, 5, 7, 2],
    [2, 1, 3, 4, 5, 7, 1],
    [0, 2, 1, 3, 4, 5, 7, 1],
    [1, 2, 0, 3, 4, 0, 5, 7],
    [2, 1, 3, 4, 6, 5, 7, 1],
    [0, 2, 1, 3, 4, 2, 5, 7],
    [2, 1, 3, 4, 2, 5, 7],
    [0, 7, 2, 1, 3, 4, 5, 7, 2],
    [7, 2, 1, 3, 4, 5, 7, 2],
    [0, 2, 3, 1, 4, 5, 1, 7],
    [2, 3, 1, 4, 5, 1, 7],
    [2, 3, 1, 4, 5, 1, 7],
    [0, 2, 3, 1, 4, 5, 1, 7],
    [0, 1, 3, 2, 5, 4, 6, 7, 2],
    [1, 3, 2, 5, 4, 6, 7, 2],
    [0, 2, 1, 3, 4, 5, 7, 2],
    [2, 1, 3, 4, 5, 7, 2],
    [2, 1, 3, 4, 5, 7, 1],
    [0, 2, 1, 3, 4, 5, 7, 1],
    [1, 2, 3, 0, 4, 5, 7],
    [0, 1, 2, 3, 0, 4, 5, 7],
    [0, 1, 2, 3, 1, 4, 5, 7],
    [1, 2, 3, 1, 4, 5, 7],
    [0, 7, 2, 1, 3, 4, 5, 7, 2],
    [7, 2, 1, 3, 4, 5, 7, 2],
    [0, 2, 3, 1, 4, 5, 3, 7],
    [2, 3, 1, 4, 5, 3, 7],
    [0, 2, 3, 1, 4, 5, 7, 3],
    [2, 3, 1, 4, 5, 7, 3],
    [1, 2, 3, 1, 4, 5, 7, 3],
    [7, 2, 1, 3, 4, 5, 2, 7],
    [1, 3, 2, 4, 7, 5],
    [0, 1, 3, 2, 4, 7, 5],
    [0, 1, 3, 2, 4, 7, 5],
    [1, 3, 2, 4, 7, 5],
    [1, 2, 0, 3, 4, 5, 0, 7],
    [2, 1, 0, 7, 3, 4, 1, 5],
    [0, 2, 1, 3, 4, 5, 2, 7],
    [2, 1, 3, 4, 5, 2, 7],
    [1, 3, 2, 4, 5, 7, 2],
    [0, 1, 3, 2, 4, 5, 7, 2],
    [0, 1, 3, 2, 4, 5, 7, 2],
    [1, 3, 2, 4, 5, 7, 2]]

/-- The permutations. -/
def tauTable : List (List (Fin 8)) :=
  [[5, 2, 6, 3, 1, 0, 4, 7],
    [5, 2, 6, 3, 1, 0, 4, 7],
    [2, 5, 6, 3, 1, 0, 4, 7],
    [2, 5, 6, 3, 1, 0, 4, 7],
    [6, 7, 2, 5, 4, 0, 3, 1],
    [6, 7, 2, 5, 4, 0, 3, 1],
    [4, 6, 7, 3, 2, 5, 0, 1],
    [2, 6, 7, 5, 4, 0, 3, 1],
    [5, 2, 7, 3, 6, 0, 4, 1],
    [5, 2, 7, 3, 6, 0, 4, 1],
    [2, 5, 7, 3, 6, 0, 4, 1],
    [2, 5, 7, 3, 6, 0, 4, 1],
    [6, 7, 2, 5, 4, 0, 3, 1],
    [2, 3, 5, 6, 1, 0, 4, 7],
    [2, 3, 5, 6, 1, 0, 4, 7],
    [2, 3, 5, 6, 1, 0, 4, 7],
    [6, 7, 5, 2, 4, 0, 3, 1],
    [6, 7, 5, 2, 4, 0, 3, 1],
    [2, 3, 6, 5, 1, 0, 4, 7],
    [2, 3, 6, 5, 1, 0, 4, 7],
    [2, 5, 3, 7, 1, 0, 4, 6],
    [2, 5, 3, 7, 1, 0, 4, 6],
    [5, 2, 3, 7, 1, 0, 4, 6],
    [5, 2, 3, 7, 1, 0, 4, 6],
    [2, 6, 3, 5, 1, 0, 4, 7],
    [2, 6, 3, 5, 1, 0, 4, 7],
    [2, 3, 6, 5, 1, 0, 4, 7],
    [2, 3, 6, 5, 1, 0, 4, 7],
    [5, 2, 1, 4, 7, 3, 6, 0],
    [5, 2, 1, 4, 7, 3, 6, 0],
    [5, 2, 6, 7, 4, 0, 3, 1],
    [5, 2, 6, 7, 4, 0, 3, 1],
    [6, 0, 5, 4, 7, 2, 3, 1],
    [6, 0, 5, 4, 7, 2, 3, 1],
    [2, 3, 6, 1, 5, 0, 4, 7],
    [2, 3, 6, 1, 5, 0, 4, 7],
    [2, 3, 7, 1, 5, 0, 4, 6],
    [2, 3, 7, 1, 5, 0, 4, 6],
    [5, 1, 4, 2, 6, 7, 3, 0],
    [7, 2, 3, 1, 5, 0, 4, 6],
    [2, 6, 3, 1, 5, 0, 4, 7],
    [2, 6, 3, 1, 5, 0, 4, 7],
    [2, 3, 6, 1, 5, 0, 4, 7],
    [2, 3, 6, 1, 5, 0, 4, 7],
    [2, 3, 7, 1, 5, 0, 4, 6],
    [2, 3, 7, 1, 5, 0, 4, 6],
    [5, 4, 6, 0, 7, 2, 3, 1],
    [5, 4, 6, 0, 7, 2, 3, 1],
    [2, 5, 1, 3, 7, 0, 4, 6],
    [2, 5, 1, 3, 7, 0, 4, 6],
    [1, 2, 5, 3, 7, 0, 4, 6],
    [1, 2, 5, 3, 7, 0, 4, 6],
    [5, 2, 0, 4, 1, 7, 3, 6],
    [5, 4, 1, 6, 7, 2, 3, 0],
    [5, 1, 4, 6, 7, 2, 3, 0],
    [2, 5, 0, 4, 1, 7, 3, 6],
    [0, 5, 4, 6, 7, 2, 3, 1],
    [6, 1, 7, 0, 3, 5, 4, 2],
    [5, 4, 0, 6, 7, 2, 3, 1],
    [5, 4, 0, 6, 7, 2, 3, 1],
    [5, 1, 2, 3, 7, 0, 4, 6],
    [1, 5, 2, 3, 7, 0, 4, 6],
    [1, 5, 2, 3, 7, 0, 4, 6],
    [1, 5, 2, 3, 7, 0, 4, 6],
    [6, 2, 5, 4, 0, 7, 3, 1],
    [6, 2, 5, 4, 0, 7, 3, 1],
    [6, 2, 5, 4, 0, 7, 3, 1],
    [2, 6, 5, 4, 0, 7, 3, 1],
    [2, 3, 7, 1, 0, 5, 4, 6],
    [2, 3, 7, 1, 0, 5, 4, 6],
    [1, 6, 0, 7, 4, 2, 3, 5],
    [7, 2, 3, 1, 0, 5, 4, 6],
    [5, 2, 7, 3, 6, 0, 4, 1],
    [2, 6, 3, 1, 0, 5, 4, 7],
    [2, 3, 6, 1, 0, 5, 4, 7],
    [2, 5, 7, 3, 6, 0, 4, 1],
    [6, 5, 2, 4, 0, 7, 3, 1],
    [6, 5, 2, 4, 0, 7, 3, 1],
    [5, 2, 6, 4, 0, 7, 3, 1],
    [5, 2, 6, 4, 0, 7, 3, 1],
    [2, 3, 1, 7, 0, 5, 4, 6],
    [2, 3, 1, 7, 0, 5, 4, 6],
    [5, 4, 0, 6, 2, 7, 3, 1],
    [5, 4, 0, 6, 2, 7, 3, 1],
    [5, 4, 1, 6, 2, 7, 3, 0],
    [5, 4, 1, 6, 2, 7, 3, 0],
    [5, 1, 4, 6, 2, 7, 3, 0],
    [5, 1, 4, 6, 2, 7, 3, 0],
    [0, 5, 4, 6, 2, 7, 3, 1],
    [2, 6, 3, 5, 1, 0, 4, 7],
    [5, 4, 0, 6, 2, 7, 3, 1],
    [5, 4, 0, 6, 2, 7, 3, 1],
    [5, 4, 1, 6, 2, 7, 3, 0],
    [5, 4, 1, 6, 2, 7, 3, 0],
    [1, 7, 2, 3, 0, 5, 4, 6],
    [1, 7, 2, 3, 0, 5, 4, 6],
    [2, 5, 1, 0, 3, 7, 4, 6],
    [2, 5, 1, 0, 3, 7, 4, 6],
    [2, 5, 6, 3, 0, 4, 1, 7],
    [2, 5, 6, 3, 0, 4, 1, 7],
    [5, 4, 1, 2, 6, 7, 3, 0],
    [5, 4, 1, 2, 6, 7, 3, 0],
    [5, 1, 4, 2, 6, 7, 3, 0],
    [5, 1, 4, 2, 6, 7, 3, 0],
    [2, 5, 4, 0, 6, 7, 3, 1],
    [2, 5, 4, 0, 6, 7, 3, 1],
    [5, 2, 4, 0, 6, 7, 3, 1],
    [5, 2, 4, 0, 6, 7, 3, 1],
    [5, 4, 1, 2, 6, 7, 3, 0],
    [5, 4, 1, 2, 6, 7, 3, 0],
    [1, 0, 2, 5, 3, 7, 4, 6],
    [1, 0, 2, 5, 3, 7, 4, 6],
    [5, 4, 2, 1, 6, 7, 3, 0],
    [5, 4, 2, 1, 6, 7, 3, 0],
    [5, 4, 2, 1, 6, 7, 3, 0],
    [1, 0, 5, 2, 3, 7, 4, 6],
    [5, 2, 0, 4, 1, 7, 3, 6],
    [5, 2, 0, 4, 1, 7, 3, 6],
    [2, 5, 0, 4, 1, 7, 3, 6],
    [2, 5, 0, 4, 1, 7, 3, 6],
    [5, 1, 0, 2, 3, 7, 4, 6],
    [3, 1, 0, 4, 5, 2, 7, 6],
    [1, 0, 5, 2, 3, 7, 4, 6],
    [1, 0, 5, 2, 3, 7, 4, 6],
    [5, 2, 1, 4, 6, 7, 3, 0],
    [5, 2, 1, 4, 6, 7, 3, 0],
    [2, 5, 1, 4, 6, 7, 3, 0],
    [2, 5, 1, 4, 6, 7, 3, 0]]

/-- The mutation sequence of an orientation. -/
def word (ε : Fin 7 → Bool) : List (Fin 8) :=
  wordTable.getD (code ε) []

/-- The permutation of an orientation. -/
def tau (ε : Fin 7 → Bool) (i : Fin 8) : Fin 8 :=
  (tauTable.getD (code ε) []).getD i 0

/-! The check is evaluated in four pieces, by the values of `ε 0` and `ε 1`, each its own theorem,
so that the kernel's caches are dropped between them: evaluated at once, the check holds about
5 GB. -/

-- The kernel evaluation of the check exceeds the default heartbeat limit.
set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- `mutation_check` for the orientations `ε` with `ε 0 = false` and `ε 1 = false`. -/
private theorem mutation_check_ff : ∀ ε : Fin 7 → Bool, ε 0 = false → ε 1 = false →
    matrixMutationList le_rfl (orientMatrix src dst ε) (word ε) =
      refMatrix.submatrix (tau ε) (tau ε) := by
  decide +kernel

-- The kernel evaluation of the check exceeds the default heartbeat limit.
set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- `mutation_check` for the orientations `ε` with `ε 0 = false` and `ε 1 = true`. -/
private theorem mutation_check_ft : ∀ ε : Fin 7 → Bool, ε 0 = false → ε 1 = true →
    matrixMutationList le_rfl (orientMatrix src dst ε) (word ε) =
      refMatrix.submatrix (tau ε) (tau ε) := by
  decide +kernel

-- The kernel evaluation of the check exceeds the default heartbeat limit.
set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- `mutation_check` for the orientations `ε` with `ε 0 = true` and `ε 1 = false`. -/
private theorem mutation_check_tf : ∀ ε : Fin 7 → Bool, ε 0 = true → ε 1 = false →
    matrixMutationList le_rfl (orientMatrix src dst ε) (word ε) =
      refMatrix.submatrix (tau ε) (tau ε) := by
  decide +kernel

-- The kernel evaluation of the check exceeds the default heartbeat limit.
set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- `mutation_check` for the orientations `ε` with `ε 0 = true` and `ε 1 = true`. -/
private theorem mutation_check_tt : ∀ ε : Fin 7 → Bool, ε 0 = true → ε 1 = true →
    matrixMutationList le_rfl (orientMatrix src dst ε) (word ε) =
      refMatrix.submatrix (tau ε) (tau ε) := by
  decide +kernel

/-- For every orientation `ε`, mutating `orientMatrix src dst ε` along `word ε` gives `refMatrix`
relabelled by `tau ε`. -/
theorem mutation_check : ∀ ε : Fin 7 → Bool,
    matrixMutationList le_rfl (orientMatrix src dst ε) (word ε) =
      refMatrix.submatrix (tau ε) (tau ε) := by
  intro ε
  cases h0 : ε 0 <;> cases h1 : ε 1
  exacts [mutation_check_ff ε h0 h1, mutation_check_ft ε h0 h1, mutation_check_tf ε h0 h1,
    mutation_check_tt ε h0 h1]

-- The kernel evaluation of the check exceeds the default heartbeat limit.
set_option maxHeartbeats 0 in
-- The kernel evaluation of a certificate check exceeds the default heartbeat limit.
/-- For every orientation `ε`, the map `tau ε` is a bijection of `Fin 8`. -/
theorem tau_bijective : ∀ ε : Fin 7 → Bool, Function.Bijective (tau ε) := by
  decide +kernel

/-- The Cartan matrix `cartanE 8` has `2` on the diagonal, `-1` at the pairs joined by an edge
`src e`–`dst e` in either direction, and `0` elsewhere. -/
theorem cartanE_eq : ∀ i j : Fin 8, cartanE 8 i j = if i = j then 2 else
    if (∃ e, src e = i ∧ dst e = j) ∨ (∃ e, src e = j ∧ dst e = i) then -1 else 0 := by
  decide +kernel

/-- No edge of the `E8` tree is a loop: `src e ≠ dst e`. -/
theorem src_ne_dst : ∀ e, src e ≠ dst e := by
  decide

/-- **Every exchange matrix of type `E8` mutates to a relabelling of `refMatrix`.** -/
theorem exists_matrixMutationList_eq (P : Matrix (Fin 8) (Fin 8) ℤ) (hP : SkewSymmetrizable P)
    (hA : cartanCounterpart P = cartanE 8) :
    ∃ (w : List (Fin 8)) (τ : Equiv.Perm (Fin 8)),
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

end ClusterAlgebras.CertificateData.E8Ref

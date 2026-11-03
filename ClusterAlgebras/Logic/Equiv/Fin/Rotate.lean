/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The value of `finRotate`

`finRotate n` sends `r : Fin n` to `r + 1`, wrapping the last element round to `0`. This file
states that on values, for every `n`: as an `if` on `r + 1 = n` (`val_finRotate`), as an `if` on
`r + 1 < n` (`val_finRotate_eq_ite_lt`), and as `(r + 1) % n` (`val_finRotate_eq_mod`).
-/

@[expose] public section

namespace ClusterAlgebras

/-- The value of `finRotate n r`: `r + 1`, or `0` when `r` is the last element. -/
theorem val_finRotate {n : ℕ} (r : Fin n) :
    ((finRotate n r : Fin n) : ℕ) = if (r : ℕ) + 1 = n then (0 : ℕ) else (r : ℕ) + 1 := by
  cases n with
  | zero => exact r.elim0
  | succ n =>
    rw [coe_finRotate]
    simp only [Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega

/-- The value of `finRotate n r`: `r + 1` when `r + 1 < n`, and `0` otherwise. -/
theorem val_finRotate_eq_ite_lt {n : ℕ} (r : Fin n) :
    ((finRotate n r : Fin n) : ℕ) = if (r : ℕ) + 1 < n then (r : ℕ) + 1 else 0 := by
  rw [val_finRotate]
  have := r.isLt
  split_ifs <;> omega

/-- The value of `finRotate n r` is `(r + 1) % n`. -/
theorem val_finRotate_eq_mod {n : ℕ} (r : Fin n) :
    ((finRotate n r : Fin n) : ℕ) = ((r : ℕ) + 1) % n := by
  rw [val_finRotate]
  have := r.isLt
  split_ifs with h
  · rw [h, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by omega)]

end ClusterAlgebras

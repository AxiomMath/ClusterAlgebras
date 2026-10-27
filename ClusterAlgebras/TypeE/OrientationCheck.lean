/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeE.Relabel

/-!
# Orientations of a tree, for checking reference matrices

A reference matrix for `E₆`, `E₇` or `E₈` (`IsReferenceMatrix`) is checked by listing the
exchange matrices `P` with `A(P) = C(E_n)`: they are skew-symmetric
(`SkewSymmetrizable.eq_neg_of_isSymm_cartanCounterpart`), hence orientations of the `E_n` tree
(`CertificateCheck.eq_orientMatrix`), finitely many, and for each of them a mutation sequence is
checked by the kernel.
-/

@[expose] public section

namespace ClusterAlgebras

namespace CertificateCheck

/-! ### Orientations of a tree -/

/-- The orientation of the edges `(src e, dst e)` by signs `ε`: entry `(i, j)` is `±1` on an
edge, with `+1` at `(src e, dst e)` exactly when `ε e`, and `0` off the edges. -/
def orientMatrix {n E : ℕ} (src dst : Fin E → Fin n) (ε : Fin E → Bool) :
    Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    match (List.finRange E).find? (fun e => decide (src e = i ∧ dst e = j)) with
    | some e => if ε e then 1 else -1
    | none =>
      match (List.finRange E).find? (fun e => decide (src e = j ∧ dst e = i)) with
      | some e => if ε e then -1 else 1
      | none => 0

/-- An integer of absolute value `1` is `1` or `-1`. -/
theorem abs_eq_one_cases {x : ℤ} (h : |x| = 1) : x = 1 ∨ x = -1 := by
  rcases abs_cases x with ⟨h1, -⟩ | ⟨h1, -⟩ <;> [left; right] <;> linarith

/-- **A skew-symmetric matrix whose Cartan counterpart is that of a graph is an orientation of
it.** If `A` is the simply laced Cartan matrix of the graph with edges `(src e, dst e)`, every
`P` with `pᵢⱼ = -pⱼᵢ` and `A(P) = A` is the orientation of the edges by the signs of
`p_{src e, dst e}`. -/
theorem eq_orientMatrix {n E : ℕ} (src dst : Fin E → Fin n) (hL : ∀ e, src e ≠ dst e)
    {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : ∀ i j, A i j = if i = j then 2 else
      if (∃ e, src e = i ∧ dst e = j) ∨ (∃ e, src e = j ∧ dst e = i) then -1 else 0)
    {P : Matrix (Fin n) (Fin n) ℤ} (hskew : ∀ i j, P i j = -P j i)
    (hP : cartanCounterpart P = A) :
    P = orientMatrix src dst (fun e => decide (0 < P (src e) (dst e))) := by
  have hc : ∀ i j, i ≠ j → -|P i j| = A i j := fun i j hij => by
    rw [← hP, cartanCounterpart, Matrix.of_apply, if_neg hij]
  ext i j
  simp only [orientMatrix, Matrix.of_apply]
  split
  · rename_i e he
    obtain ⟨rfl, rfl⟩ := of_decide_eq_true
      (List.find?_some (p := fun e => decide (src e = i ∧ dst e = j)) he)
    have h1 := hc _ _ (hL e)
    rw [hA, if_neg (hL e), if_pos (Or.inl ⟨e, rfl, rfl⟩)] at h1
    rcases abs_eq_one_cases (by linarith : |P (src e) (dst e)| = 1) with h | h <;>
      simp [h]
  · rename_i hnone
    split
    · rename_i e he
      obtain ⟨rfl, rfl⟩ := of_decide_eq_true
        (List.find?_some (p := fun e => decide (src e = j ∧ dst e = i)) he)
      have h1 := hc _ _ (hL e).symm
      rw [hA, if_neg (hL e).symm, if_pos (Or.inr ⟨e, rfl, rfl⟩)] at h1
      rw [hskew]
      rcases abs_eq_one_cases (by linarith : |P (dst e) (src e)| = 1) with h | h
      · have : P (src e) (dst e) = -1 := by rw [hskew, h]
        simp [this]
      · have : P (src e) (dst e) = 1 := by rw [hskew, h]; rfl
        simp [this]
    · rename_i hnone'
      by_cases hij : i = j
      · subst hij
        linarith [hskew i i]
      · have h1 := hc _ _ hij
        rw [hA, if_neg hij, if_neg] at h1
        · exact abs_eq_zero.1 (by linarith)
        · rintro (⟨e, he1, he2⟩ | ⟨e, he1, he2⟩)
          · exact List.find?_eq_none.1 hnone e (List.mem_finRange e) (by simp [he1, he2])
          · exact List.find?_eq_none.1 hnone' e (List.mem_finRange e) (by simp [he1, he2])

end CertificateCheck

end ClusterAlgebras

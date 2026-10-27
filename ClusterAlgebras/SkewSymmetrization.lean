/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Defs.SkewSymmetrization
public import ClusterAlgebras.SkewSymmetrizable

/-!
# Skew-symmetrizability, skew-symmetrization and diagrams

For a skew-symmetrizable matrix `B`, the skew-symmetrization `S(B)` is the diagonal conjugation
of `B` by the square roots of any skew-symmetrizing vector `d`: `s i j = √(d i / d j) * b i j`.
Consequently `S(B)` is skew-symmetric, the diagram `Γ(B)` and `S(B)` determine each other,
mutation of diagrams is well defined, and a skew-symmetrizing vector of a matrix with connected
diagram is unique up to a scalar.

## Main results

* `IsSkewSymmetrizingVector.skewSymmetrization_apply`: `s i j = √(d i / d j) * b i j` for every
  skew-symmetrizing vector `d` of `B`.
* `SkewSymmetrizable.transpose_skewSymmetrization`: the skew-symmetrization of a
  skew-symmetrizable matrix is skew-symmetric.
* `diagram_eq_iff_skewSymmetrization_eq`: two skew-symmetrizable real matrices have the same
  diagram if and only if they have the same skew-symmetrization.
* `diagram_matrixMutation_eq_of_diagram_eq`: matrices with the same diagram have mutations with
  the same diagram.
* `IsSkewSymmetrizingVector.div_eq_div_of_connected`: if the diagram of `B` is connected, then
  for two skew-symmetrizing vectors `d`, `d'` the ratio `d i / d' i` does not depend on `i`.

## Implementation notes

* `IsSkewSymmetrizingVector.skewSymmetrization_apply` is stated for a given skew-symmetrizing
  vector rather than under `SkewSymmetrizable`, so that it applies to several vectors for the
  same matrix.

* The statements about mutation take the hypothesis `n ≤ n` that `matrixMutation` asks for, as
  the results in `ClusterAlgebras.SkewSymmetrizable` do, rather than fixing `le_rfl`.

* The uniqueness of the skew-symmetrizing vector is deduced from the division-free identity
  `IsSkewSymmetrizingVector.mul_eq_mul_of_apply_ne_zero`, `d i * d' j = d j * d' i` whenever
  `b i j ≠ 0`; the ratio statement `d i / d' i = d j / d' j` is then stated in `ℚ`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {n : ℕ}

/-! ### Consequences of the defining identity -/

section Ring

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {B : Matrix (Fin n) (Fin n) R} {d : Fin n → ℤ}

namespace IsSkewSymmetrizingVector

/-- **An entry vanishes exactly when its mirror does**: `b i j = 0 ↔ b j i = 0`. -/
theorem apply_eq_zero_comm (hd : IsSkewSymmetrizingVector B d) (i j : Fin n) :
    B i j = 0 ↔ B j i = 0 := by
  have h := hd.2 i j
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · rw [hb, mul_zero, eq_comm, neg_eq_zero] at h
    exact (mul_eq_zero.1 h).resolve_left (hd.cast_pos (R := R) j).ne'
  · rw [hb, mul_zero, neg_zero] at h
    exact (mul_eq_zero.1 h).resolve_left (hd.cast_pos (R := R) i).ne'

/-- **The diagonal of a skew-symmetrizable matrix vanishes.** -/
theorem apply_self_eq_zero (hd : IsSkewSymmetrizingVector B d) (i : Fin n) : B i i = 0 := by
  have h : (d i : R) * B i i = 0 := by linarith [hd.2 i i]
  exact (mul_eq_zero.1 h).resolve_left (hd.cast_pos (R := R) i).ne'

/-- **An entry neither of whose two directions is positive vanishes**: if neither `b i j`
nor `b j i` is positive, then `b i j = 0`. -/
theorem apply_eq_zero_of_not_pos (hd : IsSkewSymmetrizingVector B d) {i j : Fin n}
    (hij : ¬0 < B i j) (hji : ¬0 < B j i) : B i j = 0 := by
  rcases lt_trichotomy (B i j) 0 with hb | hb | hb
  · exact absurd ((hd.pos_iff_neg j i).2 hb) hji
  · exact hb
  · exact absurd hb hij

end IsSkewSymmetrizingVector

end Ring

/-! ### Skew-symmetrization -/

section Real

variable {B B' : Matrix (Fin n) (Fin n) ℝ} {d d' : Fin n → ℤ}

/-- `Real.sign x * |x| = x`, including at `x = 0`. -/
private theorem real_sign_mul_abs (x : ℝ) : Real.sign x * |x| = x := by
  rcases lt_trichotomy x 0 with h | h | h
  · simp [Real.sign_of_neg h, abs_of_neg h]
  · simp [h]
  · simp [Real.sign_of_pos h, abs_of_pos h]

namespace IsSkewSymmetrizingVector

/-- The mirror entry is `b j i = -((d i / d j) * b i j)`. -/
theorem apply_swap (hd : IsSkewSymmetrizingVector B d) (i j : Fin n) :
    B j i = -(((d i : ℝ) / (d j : ℝ)) * B i j) := by
  have hj := hd.cast_pos (R := ℝ) j
  have h := hd.2 i j
  field_simp
  linarith

/-- **The skew-symmetrization is the diagonal conjugation by the square roots of any
skew-symmetrizing vector**: `s i j = √(d i / d j) * b i j`. In particular the formula
defining `S(B)`, which mentions no vector, agrees with the conjugation by every one of
them. -/
@[cluster_algebras "lem_skew_symmetrization_conjugate"]
theorem skewSymmetrization_apply (hd : IsSkewSymmetrizingVector B d) (i j : Fin n) :
    skewSymmetrization B i j = √((d i : ℝ) / (d j : ℝ)) * B i j := by
  have hr : (0 : ℝ) < (d i : ℝ) / (d j : ℝ) :=
    div_pos (hd.cast_pos (R := ℝ) i) (hd.cast_pos (R := ℝ) j)
  have habs : |B i j * B j i| = ((d i : ℝ) / (d j : ℝ)) * B i j ^ 2 := by
    rw [hd.apply_swap i j, mul_neg, abs_neg,
      show B i j * (((d i : ℝ) / (d j : ℝ)) * B i j)
        = ((d i : ℝ) / (d j : ℝ)) * B i j ^ 2 by ring,
      abs_of_nonneg (mul_nonneg hr.le (sq_nonneg _))]
  rw [ClusterAlgebras.skewSymmetrization_apply, habs, Real.sqrt_mul hr.le,
    Real.sqrt_sq_eq_abs, mul_left_comm, real_sign_mul_abs]

/-- **Skew-symmetrization preserves the positive entries**: `0 < s i j ↔ 0 < b i j`. -/
theorem pos_skewSymmetrization_iff (hd : IsSkewSymmetrizingVector B d) (i j : Fin n) :
    0 < skewSymmetrization B i j ↔ 0 < B i j := by
  rw [hd.skewSymmetrization_apply i j]
  exact mul_pos_iff_of_pos_left
    (Real.sqrt_pos.2 (div_pos (hd.cast_pos (R := ℝ) i) (hd.cast_pos (R := ℝ) j)))

end IsSkewSymmetrizingVector

namespace SkewSymmetrizable

/-- Skew-symmetrization exchanges an entry for the negative of its mirror. -/
theorem skewSymmetrization_apply_swap (hB : SkewSymmetrizable B) (i j : Fin n) :
    skewSymmetrization B j i = -skewSymmetrization B i j := by
  obtain ⟨d, hd⟩ := hB
  have key : √((d j : ℝ) / (d i : ℝ)) * ((d i : ℝ) / (d j : ℝ)) = √((d i : ℝ) / (d j : ℝ)) := by
    rw [show ((d j : ℝ) / (d i : ℝ)) = (((d i : ℝ) / (d j : ℝ)))⁻¹ by rw [inv_div],
      Real.sqrt_inv, inv_mul_eq_div, Real.div_sqrt]
  rw [hd.skewSymmetrization_apply j i, hd.skewSymmetrization_apply i j, hd.apply_swap i j,
    mul_neg, ← mul_assoc, key]

/-- **The skew-symmetrization of a skew-symmetrizable matrix is skew-symmetric.** -/
@[cluster_algebras "lem_skew_symmetrization_is_skew"]
theorem transpose_skewSymmetrization (hB : SkewSymmetrizable B) :
    (skewSymmetrization B).transpose = -skewSymmetrization B := by
  ext i j
  simpa only [Matrix.transpose_apply, Matrix.neg_apply] using hB.skewSymmetrization_apply_swap i j

/-- Skew-symmetrizable matrices with the same diagram have the same skew-symmetrization. -/
theorem skewSymmetrization_eq_of_diagram_eq (hB : SkewSymmetrizable B)
    (hB' : SkewSymmetrizable B') (h : diagram B = diagram B') :
    skewSymmetrization B = skewSymmetrization B' := by
  obtain ⟨d, hd⟩ := hB
  obtain ⟨d', hd'⟩ := hB'
  rw [diagram_eq_iff] at h
  ext i j
  rcases lt_trichotomy 0 (B i j) with hb | hb | hb
  · rw [skewSymmetrization_apply_of_pos hb, skewSymmetrization_apply_of_pos ((h i j).1.1 hb),
      (h i j).2 hb]
  · have hji : B j i = 0 := (hd.apply_eq_zero_comm i j).1 hb.symm
    have hb' : B' i j = 0 :=
      hd'.apply_eq_zero_of_not_pos (fun hc => absurd ((h i j).1.2 hc) (by simp [← hb]))
        (fun hc => absurd ((h j i).1.2 hc) (by simp [hji]))
    rw [skewSymmetrization_apply_of_eq_zero hb.symm, skewSymmetrization_apply_of_eq_zero hb']
  · have hji : 0 < B j i := (hd.pos_iff_neg j i).2 hb
    rw [skewSymmetrization_apply_swap ⟨d, hd⟩ j i, skewSymmetrization_apply_swap ⟨d', hd'⟩ j i,
      skewSymmetrization_apply_of_pos hji,
      skewSymmetrization_apply_of_pos ((h j i).1.1 hji), (h j i).2 hji]

end SkewSymmetrizable

/-! ### Diagrams -/

/-- **The diagram and the skew-symmetrization carry the same information**: two
skew-symmetrizable real matrices have the same diagram exactly when they have the same
skew-symmetrization. -/
@[cluster_algebras "lem_diagram_determines_skew_symmetrization"]
theorem diagram_eq_iff_skewSymmetrization_eq (hB : SkewSymmetrizable B)
    (hB' : SkewSymmetrizable B') :
    diagram B = diagram B' ↔ skewSymmetrization B = skewSymmetrization B' := by
  refine ⟨hB.skewSymmetrization_eq_of_diagram_eq hB', fun h => ?_⟩
  obtain ⟨d, hd⟩ := hB
  obtain ⟨d', hd'⟩ := hB'
  rw [diagram_eq_iff]
  refine fun i j => ⟨?_, fun _ => ?_⟩
  · rw [← hd.pos_skewSymmetrization_iff i j, ← hd'.pos_skewSymmetrization_iff i j, h]
  · rw [← sq_skewSymmetrization B, ← sq_skewSymmetrization B', h]

/-- **Mutation of diagrams is well defined**: matrices with the same diagram have mutations
with the same diagram. -/
@[cluster_algebras "prop_diagram_mutation"]
theorem diagram_matrixMutation_eq_of_diagram_eq (hB : SkewSymmetrizable B)
    (hB' : SkewSymmetrizable B') (h : diagram B = diagram B') (hnn : n ≤ n) (k : Fin n) :
    diagram (matrixMutation hnn B k) = diagram (matrixMutation hnn B' k) := by
  obtain ⟨d, hd⟩ := hB
  obtain ⟨d', hd'⟩ := hB'
  rw [diagram_eq_iff_skewSymmetrization_eq ⟨d, hd.matrixMutation hnn k⟩
      ⟨d', hd'.matrixMutation hnn k⟩,
    SkewSymmetrizable.skewSymmetrization_matrixMutation ⟨d, hd⟩ hnn k,
    SkewSymmetrizable.skewSymmetrization_matrixMutation ⟨d', hd'⟩ hnn k,
    SkewSymmetrizable.skewSymmetrization_eq_of_diagram_eq ⟨d, hd⟩ ⟨d', hd'⟩ h]

/-! ### Uniqueness of the skew-symmetrizing vector -/

namespace IsSkewSymmetrizingVector

/-- **Two skew-symmetrizing vectors have the same ratio at the two ends of a nonzero
entry**: if `b i j ≠ 0`, then `d i * d' j = d j * d' i`. -/
theorem mul_eq_mul_of_apply_ne_zero (hd : IsSkewSymmetrizingVector B d)
    (hd' : IsSkewSymmetrizingVector B d') {i j : Fin n} (hij : B i j ≠ 0) :
    d i * d' j = d j * d' i := by
  have hji : B j i ≠ 0 := fun h => hij ((hd.apply_eq_zero_comm i j).2 h)
  have key : ((d i * d' j : ℤ) : ℝ) = ((d j * d' i : ℤ) : ℝ) := by
    push_cast
    refine mul_right_cancel₀ hji ?_
    linear_combination (d i : ℝ) * hd'.2 i j - (d' i : ℝ) * hd.2 i j
  exact_mod_cast key

/-- **A skew-symmetrizing vector of a matrix with connected diagram is unique up to a
scalar**: the ratio `d i / d' i` of two of them does not depend on `i`. -/
@[cluster_algebras "lem_skew_symmetrizing_vector_unique"]
theorem div_eq_div_of_connected (hΓ : (diagram B).Connected)
    (hd : IsSkewSymmetrizingVector B d) (hd' : IsSkewSymmetrizingVector B d') (i j : Fin n) :
    (d i : ℚ) / (d' i : ℚ) = (d j : ℚ) / (d' j : ℚ) := by
  have hclose : ∀ p q : Fin n, d p * d' i = d i * d' p → B p q ≠ 0 →
      d q * d' i = d i * d' q := by
    intro p q hp hpq
    refine mul_left_cancel₀ (hd.1 p).ne' ?_
    linear_combination (d q) * hp - (d i) * hd.mul_eq_mul_of_apply_ne_zero hd' hpq
  have huniv : {l : Fin n | d l * d' i = d i * d' l} = Set.univ := by
    refine hΓ.eq_univ ⟨i, rfl⟩ fun p hp q hq => ⟨fun hedge => ?_, fun hedge => ?_⟩
    · exact hq (hclose p q hp (mem_edges_diagram.1 hedge).ne')
    · refine hq (hclose p q hp fun hc => ?_)
      exact absurd ((hd.apply_eq_zero_comm p q).1 hc) (mem_edges_diagram.1 hedge).ne'
  have hj : d j * d' i = d i * d' j := huniv.symm.subset (Set.mem_univ j)
  have h1 : (d' i : ℚ) ≠ 0 := by exact_mod_cast (hd'.1 i).ne'
  have h2 : (d' j : ℚ) ≠ 0 := by exact_mod_cast (hd'.1 j).ne'
  rw [div_eq_div_iff h1 h2]
  exact_mod_cast hj.symm

end IsSkewSymmetrizingVector

end Real

end ClusterAlgebras

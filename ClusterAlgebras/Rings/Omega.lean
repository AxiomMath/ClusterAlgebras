/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.Defs
public import ClusterAlgebras.External

/-!
# The formula for `Ω`

For the generic `k × k` matrix `z` over `ℂ`, write `P_X` for the flag minor `P_X(z)`. For
`2 ≤ b < c ≤ k - 1` put `a = b - 1`, `d = c + 1` and `J = [b + 1, c - 1]`, and write `Ja` for
`J ∪ {a}`, `Jbcd` for `J ∪ {b, c, d}`, and so on. The formula for `Ω` is the identity
`P_{Jbc} (P_{Jb} P_{Jacd} - P_{Ja} P_{Jbcd}) = P_{Jabc} P_{Jcd} P_{Jb} + P_{Jab} P_{Jbcd} P_{Jc}`.

It follows from two instances of the three-term relation for flag minors: the one for `S = J`
and `a < b < c`, and the one for `S = J ∪ {c}` and `a < b < d`. Neither the consecutiveness of
`a, b` and of `c, d`, nor the shape of `J`, nor the matrix being generic, plays any role, and the
identity is proved first for any square matrix over a commutative ring, any columns
`a < b < c < d` and any set `S` of columns avoiding them.

## Main results

* `ClusterAlgebras.flagMinor_omega`: the identity for any matrix, any `a < b < c < d` and any `S`.
* `ClusterAlgebras.flagMinor_complexGenericMatrix_omega`: the formula for `Ω` for the generic
  matrix.
* `ClusterAlgebras.flagMinor_singleton_three_term`: the three-term relation for `S = ∅`, the
  gap-one analogue `P_{b-1} P_{b,b+1} + P_{b+1} P_{b-1,b} = P_b P_{b-1,b+1}`.

## Implementation notes

Columns are indexed by `Fin k`, so the 1-based column `j` is `j - 1 : Fin k`. The conditions
`2 ≤ b < c ≤ k - 1`, `a = b - 1`, `d = c + 1` become columns `a b c d : Fin k` with `a + 1 = b`,
`b < c` and `c + 1 = d`, and `J = [b + 1, c - 1]` becomes `Finset.Ioo b c`. The bound `k ≥ 4`
follows from the existence of four distinct columns and is not assumed.
-/

@[expose] public section

namespace ClusterAlgebras

/-- **The identity behind `Ω`.** For a square matrix `z` over a commutative ring, columns
`a < b < c < d` and a set `S` of columns containing none of them, with `P_X = P_X(z)`,
`P_{Sbc} (P_{Sb} P_{Sacd} - P_{Sa} P_{Sbcd}) = P_{Sabc} P_{Scd} P_{Sb} + P_{Sab} P_{Sbcd} P_{Sc}`,
where `Sbc = S ∪ {b, c}` and so on. -/
theorem flagMinor_omega {R : Type*} [CommRing R] {n : ℕ} (z : Matrix (Fin n) (Fin n) R)
    (S : Finset (Fin n)) {a b c d : Fin n} (ha : a ∉ S) (hb : b ∉ S) (hc : c ∉ S) (hd : d ∉ S)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    flagMinor z (S ∪ {b, c}) *
        (flagMinor z (S ∪ {b}) * flagMinor z (S ∪ {a, c, d}) -
          flagMinor z (S ∪ {a}) * flagMinor z (S ∪ {b, c, d})) =
      flagMinor z (S ∪ {a, b, c}) * flagMinor z (S ∪ {c, d}) * flagMinor z (S ∪ {b}) +
        flagMinor z (S ∪ {a, b}) * flagMinor z (S ∪ {b, c, d}) * flagMinor z (S ∪ {c}) := by
  have hn : 3 ≤ n := by
    have := d.isLt
    rw [Fin.lt_def] at hab hbc hcd
    omega
  have h₁ := flagMinor_three_term hn z S ha hb hc hab hbc
  have h₂ := flagMinor_three_term hn z (S ∪ {c}) (by simp [ha, (hab.trans hbc).ne])
    (by simp [hb, hbc.ne]) (by simp [hd, hcd.ne']) hab (hbc.trans hcd)
  have e : ∀ T U : Finset (Fin n), insert c T = U → S ∪ {c} ∪ T = S ∪ U := by
    rintro T U rfl
    rw [Finset.union_assoc, Finset.singleton_union]
  rw [e {b} {b, c} (Finset.pair_comm c b), e {a, d} {a, c, d} (by ext; simp; tauto),
    e {a} {a, c} (Finset.pair_comm c a), e {b, d} {b, c, d} (by ext; simp; tauto),
    e {d} {c, d} rfl, e {a, b} {a, b, c} (by ext; simp; tauto)] at h₂
  linear_combination flagMinor z (S ∪ {b}) * h₂ + flagMinor z (S ∪ {b, c, d}) * h₁

/-- **The formula for `Ω`.** Let `z` be the generic `k × k` matrix over `ℂ` and `P_X = P_X(z)`.
For columns `a, b, c, d` with `a + 1 = b < c` and `c + 1 = d`, and `J = (b, c)` the columns
strictly between `b` and `c`,
`P_{Jbc} (P_{Jb} P_{Jacd} - P_{Ja} P_{Jbcd}) = P_{Jabc} P_{Jcd} P_{Jb} + P_{Jab} P_{Jbcd} P_{Jc}`.

In 1-based indexing, `b` and `c` here are `b - 1` and `c - 1` for `2 ≤ b < c ≤ k - 1`, `a = b - 1`,
`d = c + 1` and `J = [b + 1, c - 1]`; the bound `k ≥ 4` is implied. -/
@[cluster_algebras "lem_omega_formula"]
theorem flagMinor_complexGenericMatrix_omega {k : ℕ} {a b c d : Fin k}
    (hab : (a : ℕ) + 1 = b) (hbc : b < c) (hcd : (c : ℕ) + 1 = d) :
    flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {b, c}) *
        (flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {b}) *
            flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {a, c, d}) -
          flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {a}) *
            flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {b, c, d})) =
      flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {a, b, c}) *
          flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {c, d}) *
          flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {b}) +
        flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {a, b}) *
          flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {b, c, d}) *
          flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {c}) := by
  have hab' : a < b := by rw [Fin.lt_def]; omega
  have hcd' : c < d := by rw [Fin.lt_def]; omega
  exact flagMinor_omega _ _ (by simp [hab'.not_gt]) (by simp) (by simp)
    (by simp [hcd'.le]) hab' hbc hcd'

/-- **The three-term relation for `S = ∅`.** For a square matrix `z` over a commutative ring
and columns `a < b < c`, `P_a P_{bc} + P_c P_{ab} = P_b P_{ac}`, where `P_X = P_X(z)`.

For the generic matrix and consecutive columns this is the gap-one analogue of the formula for
`Ω`: in 1-based indexing, `P_{b-1} P_{b,b+1} + P_{b+1} P_{b-1,b} = P_b P_{b-1,b+1}` for
`2 ≤ b ≤ k - 1`. -/
theorem flagMinor_singleton_three_term {R : Type*} [CommRing R] {n : ℕ}
    (z : Matrix (Fin n) (Fin n) R) {a b c : Fin n} (hab : a < b) (hbc : b < c) :
    flagMinor z {a} * flagMinor z {b, c} + flagMinor z {c} * flagMinor z {a, b} =
      flagMinor z {b} * flagMinor z {a, c} := by
  have hn : 3 ≤ n := by
    have := c.isLt
    rw [Fin.lt_def] at hab hbc
    omega
  simpa using (flagMinor_three_term hn z ∅ (Finset.notMem_empty a) (Finset.notMem_empty b)
    (Finset.notMem_empty c) hab hbc).symm

end ClusterAlgebras

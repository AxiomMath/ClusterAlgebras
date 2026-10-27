/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.WiringDiagram.Chamber

/-!
# The arithmetic of a braid move's arrow comparison

`braidIso` comes down to one identity: for two chambers, the signed arrow count of
`Q(D')` between their images equals the signed count of `Q(D)` plus the mutation's correction term.
Both sides are arithmetic in the two chambers' gaps and ends, so that identity is proved here
over plain naturals, with no chamber anywhere in sight.

That is not tidiness but necessity. `Chamber`'s `DecidableEq` runs through `chamberEquiv` and hence
`spanStart` over the word, so an `if` mentioning a concrete chamber sends `whnf` into the word:
an `example` about two named chambers timed out at a million heartbeats IN ITS STATEMENT. Over
naturals the same case analysis takes seconds.

The variables are a chamber's gap and its two ends, with `Li'` and `Ri'` the ends after the move —
the move exchanges `p + 2` with `p + 3` as left ends and `p + 1` with `p + 2` as right ends,
which is what `hLi` and its siblings say. `hci` and `hcj` are the five cases of
`ends_cases_of_ne_braidSite`: the four neighbours of the site, and a chamber with no end among the
three crossings.

Three facts have to be passed in because the case list does not imply them, and each is geometry
rather than arithmetic: two chambers at different gaps share no end (`hLL`, `hRR`, `hLR`, `hRL` —
an end is a crossing of the chamber's OWN gap), and two chambers at one gap have disjoint spans
unless they are equal (`hsame`).
-/

@[expose] public section

namespace ClusterAlgebras

namespace WiringDiagram

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_1_1 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = a)
    (hli : Li ≤ p)
    (hri : Ri = p + 1)
    (hgj : gj = a)
    (hlj : Lj ≤ p)
    (hrj : Rj = p + 1) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = p + 2 := by rw [hRi]; split_ifs; omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = p + 2 := by rw [hRj]; split_ifs; omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_1_2 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (hLL : gi ≠ gj → Li = Lj → Li = 0)
    (hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (hLR : gi ≠ gj → Li ≠ Rj)
    (hRL : gi ≠ gj → Ri ≠ Lj)
    (hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = a)
    (hli : Li ≤ p)
    (hri : Ri = p + 1)
    (hgj : gj = b)
    (hlj : Lj ≤ p)
    (hrj : Rj = p + 2) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = p + 2 := by rw [hRi]; split_ifs; omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = p + 1 := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_1_3 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = a)
    (hli : Li ≤ p)
    (hri : Ri = p + 1)
    (hgj : gj = b)
    (hlj : Lj = p + 2)
    (hrj : p + 4 ≤ Rj) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = p + 2 := by rw [hRi]; split_ifs; omega
  have eLj : Lj' = p + 3 := by rw [hLj]; split_ifs; omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_1_4 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (_hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (hlei : Li ≤ len)
    (hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = a)
    (hli : Li ≤ p)
    (hri : Ri = p + 1)
    (hgj : gj = a)
    (hlj : Lj = p + 3)
    (_hrj : p + 4 ≤ Rj) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = p + 2 := by rw [hRi]; split_ifs; omega
  have eLj : Lj' = p + 2 := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_1_5 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (_hgi : gi = a)
    (hli : Li ≤ p)
    (hri : Ri = p + 1)
    (huj0 : Lj ≠ p + 1)
    (huj1 : Lj ≠ p + 2)
    (huj2 : Lj ≠ p + 3)
    (huj3 : Rj ≠ p + 1)
    (huj4 : Rj ≠ p + 2)
    (huj5 : Rj ≠ p + 3) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = p + 2 := by rw [hRi]; split_ifs; omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  have hcorr : ((if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
      (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
      (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
      (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) = 0 := by
    have c2 : ¬(Lj = p + 3 ∨ Rj = p + 2) := by omega
    have c3 : ¬(Rj = p + 1 ∨ Lj = p + 2) := by omega
    rw [if_neg c2, if_neg c3]
    ring
  have hM : ArrowArith len Li (p + 2) gi Lj Rj gj ↔
      ArrowArith len Li Ri gi Lj Rj gj := by
    simp only [ArrowArith]
    omega
  have hM' : ArrowArith len Lj Rj gj Li (p + 2) gi ↔
      ArrowArith len Lj Rj gj Li Ri gi := by
    simp only [ArrowArith]
    omega
  rw [if_congr hM rfl rfl, if_congr hM' rfl rfl, hcorr, ite_self]
  ring

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_2_1 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (hLL : gi ≠ gj → Li = Lj → Li = 0)
    (hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (hLR : gi ≠ gj → Li ≠ Rj)
    (hRL : gi ≠ gj → Ri ≠ Lj)
    (hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = b)
    (hli : Li ≤ p)
    (hri : Ri = p + 2)
    (hgj : gj = a)
    (hlj : Lj ≤ p)
    (hrj : Rj = p + 1) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = p + 1 := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = p + 2 := by rw [hRj]; split_ifs; omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_2_2 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = b)
    (hli : Li ≤ p)
    (hri : Ri = p + 2)
    (hgj : gj = b)
    (hlj : Lj ≤ p)
    (hrj : Rj = p + 2) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = p + 1 := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = p + 1 := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_2_3 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = b)
    (hli : Li ≤ p)
    (hri : Ri = p + 2)
    (hgj : gj = b)
    (hlj : Lj = p + 2)
    (hrj : p + 4 ≤ Rj) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = p + 1 := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = p + 3 := by rw [hLj]; split_ifs; omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_2_4 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (_hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (hlei : Li ≤ len)
    (hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = b)
    (hli : Li ≤ p)
    (hri : Ri = p + 2)
    (hgj : gj = a)
    (hlj : Lj = p + 3)
    (_hrj : p + 4 ≤ Rj) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = p + 1 := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = p + 2 := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_2_5 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (_hgi : gi = b)
    (hli : Li ≤ p)
    (hri : Ri = p + 2)
    (huj0 : Lj ≠ p + 1)
    (huj1 : Lj ≠ p + 2)
    (huj2 : Lj ≠ p + 3)
    (huj3 : Rj ≠ p + 1)
    (huj4 : Rj ≠ p + 2)
    (huj5 : Rj ≠ p + 3) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = p + 1 := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  have hcorr : ((if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
      (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
      (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
      (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) = 0 := by
    have c2 : ¬(Lj = p + 3 ∨ Rj = p + 2) := by omega
    have c3 : ¬(Rj = p + 1 ∨ Lj = p + 2) := by omega
    rw [if_neg c2, if_neg c3]
    ring
  have hM : ArrowArith len Li (p + 1) gi Lj Rj gj ↔
      ArrowArith len Li Ri gi Lj Rj gj := by
    simp only [ArrowArith]
    omega
  have hM' : ArrowArith len Lj Rj gj Li (p + 1) gi ↔
      ArrowArith len Lj Rj gj Li Ri gi := by
    simp only [ArrowArith]
    omega
  rw [if_congr hM rfl rfl, if_congr hM' rfl rfl, hcorr, ite_self]
  ring

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_3_1 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = b)
    (hli : Li = p + 2)
    (hri : p + 4 ≤ Ri)
    (hgj : gj = a)
    (_hlj : Lj ≤ p)
    (hrj : Rj = p + 1) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = p + 3 := by rw [hLi]; split_ifs; omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = p + 2 := by rw [hRj]; split_ifs; omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_3_2 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = b)
    (hli : Li = p + 2)
    (hri : p + 4 ≤ Ri)
    (hgj : gj = b)
    (hlj : Lj ≤ p)
    (hrj : Rj = p + 2) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = p + 3 := by rw [hLi]; split_ifs; omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = p + 1 := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_3_3 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (_hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = b)
    (hli : Li = p + 2)
    (hri : p + 4 ≤ Ri)
    (hgj : gj = b)
    (hlj : Lj = p + 2)
    (hrj : p + 4 ≤ Rj) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = p + 3 := by rw [hLi]; split_ifs; omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = p + 3 := by rw [hLj]; split_ifs; omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_3_4 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (_hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (hLR : gi ≠ gj → Li ≠ Rj)
    (hRL : gi ≠ gj → Ri ≠ Lj)
    (hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = b)
    (hli : Li = p + 2)
    (hri : p + 4 ≤ Ri)
    (hgj : gj = a)
    (hlj : Lj = p + 3)
    (_hrj : p + 4 ≤ Rj) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = p + 3 := by rw [hLi]; split_ifs; omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = p + 2 := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_3_5 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (_hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (_hgi : gi = b)
    (hli : Li = p + 2)
    (hri : p + 4 ≤ Ri)
    (_huj0 : Lj ≠ p + 1)
    (huj1 : Lj ≠ p + 2)
    (huj2 : Lj ≠ p + 3)
    (huj3 : Rj ≠ p + 1)
    (huj4 : Rj ≠ p + 2)
    (huj5 : Rj ≠ p + 3) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = p + 3 := by rw [hLi]; split_ifs; omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  have hcorr : ((if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
      (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
      (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
      (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) = 0 := by
    have c2 : ¬(Lj = p + 3 ∨ Rj = p + 2) := by omega
    have c3 : ¬(Rj = p + 1 ∨ Lj = p + 2) := by omega
    rw [if_neg c2, if_neg c3]
    ring
  have hM : ArrowArith len (p + 3) Ri gi Lj Rj gj ↔
      ArrowArith len Li Ri gi Lj Rj gj := by
    simp only [ArrowArith]
    omega
  have hM' : ArrowArith len Lj Rj gj (p + 3) Ri gi ↔
      ArrowArith len Lj Rj gj Li Ri gi := by
    simp only [ArrowArith]
    omega
  rw [if_congr hM rfl rfl, if_congr hM' rfl rfl, hcorr, ite_self]
  ring

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_4_1 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = a)
    (hli : Li = p + 3)
    (_hri : p + 4 ≤ Ri)
    (hgj : gj = a)
    (_hlj : Lj ≤ p)
    (hrj : Rj = p + 1) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = p + 2 := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = p + 2 := by rw [hRj]; split_ifs; omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_4_2 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = a)
    (hli : Li = p + 3)
    (_hri : p + 4 ≤ Ri)
    (hgj : gj = b)
    (hlj : Lj ≤ p)
    (hrj : Rj = p + 2) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = p + 2 := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = p + 1 := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_4_3 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (_hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (hLR : gi ≠ gj → Li ≠ Rj)
    (hRL : gi ≠ gj → Ri ≠ Lj)
    (hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = a)
    (hli : Li = p + 3)
    (_hri : p + 4 ≤ Ri)
    (hgj : gj = b)
    (hlj : Lj = p + 2)
    (hrj : p + 4 ≤ Rj) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = p + 2 := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = p + 3 := by rw [hLj]; split_ifs; omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_4_4 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (_hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hgi : gi = a)
    (hli : Li = p + 3)
    (_hri : p + 4 ≤ Ri)
    (hgj : gj = a)
    (hlj : Lj = p + 3)
    (_hrj : p + 4 ≤ Rj) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = p + 2 := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = p + 2 := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_4_5 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (_hgi : gi = a)
    (hli : Li = p + 3)
    (_hri : p + 4 ≤ Ri)
    (_huj0 : Lj ≠ p + 1)
    (huj1 : Lj ≠ p + 2)
    (huj2 : Lj ≠ p + 3)
    (huj3 : Rj ≠ p + 1)
    (huj4 : Rj ≠ p + 2)
    (huj5 : Rj ≠ p + 3) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = p + 2 := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  have hcorr : ((if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
      (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
      (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
      (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) = 0 := by
    have c2 : ¬(Lj = p + 3 ∨ Rj = p + 2) := by omega
    have c3 : ¬(Rj = p + 1 ∨ Lj = p + 2) := by omega
    rw [if_neg c2, if_neg c3]
    ring
  have hM : ArrowArith len (p + 2) Ri gi Lj Rj gj ↔
      ArrowArith len Li Ri gi Lj Rj gj := by
    simp only [ArrowArith]
    omega
  have hM' : ArrowArith len Lj Rj gj (p + 2) Ri gi ↔
      ArrowArith len Lj Rj gj Li Ri gi := by
    simp only [ArrowArith]
    omega
  rw [if_congr hM rfl rfl, if_congr hM' rfl rfl, hcorr, ite_self]
  ring

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_5_1 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hui0 : Li ≠ p + 1)
    (hui1 : Li ≠ p + 2)
    (hui2 : Li ≠ p + 3)
    (hui3 : Ri ≠ p + 1)
    (hui4 : Ri ≠ p + 2)
    (hui5 : Ri ≠ p + 3)
    (_hgj : gj = a)
    (hlj : Lj ≤ p)
    (hrj : Rj = p + 1) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = p + 2 := by rw [hRj]; split_ifs; omega
  rw [eLi, eRi, eLj, eRj]
  have hcorr : ((if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
      (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
      (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
      (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) = 0 := by
    have c1 : ¬(Ri = p + 1 ∨ Li = p + 2) := by omega
    have c4 : ¬(Li = p + 3 ∨ Ri = p + 2) := by omega
    rw [if_neg c1, if_neg c4]
    ring
  have hM : ArrowArith len Li Ri gi Lj (p + 2) gj ↔
      ArrowArith len Li Ri gi Lj Rj gj := by
    simp only [ArrowArith]
    omega
  have hM' : ArrowArith len Lj (p + 2) gj Li Ri gi ↔
      ArrowArith len Lj Rj gj Li Ri gi := by
    simp only [ArrowArith]
    omega
  rw [if_congr hM rfl rfl, if_congr hM' rfl rfl, hcorr, ite_self]
  ring

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_5_2 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hui0 : Li ≠ p + 1)
    (hui1 : Li ≠ p + 2)
    (hui2 : Li ≠ p + 3)
    (hui3 : Ri ≠ p + 1)
    (hui4 : Ri ≠ p + 2)
    (hui5 : Ri ≠ p + 3)
    (_hgj : gj = b)
    (hlj : Lj ≤ p)
    (hrj : Rj = p + 2) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = p + 1 := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  have hcorr : ((if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
      (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
      (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
      (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) = 0 := by
    have c1 : ¬(Ri = p + 1 ∨ Li = p + 2) := by omega
    have c4 : ¬(Li = p + 3 ∨ Ri = p + 2) := by omega
    rw [if_neg c1, if_neg c4]
    ring
  have hM : ArrowArith len Li Ri gi Lj (p + 1) gj ↔
      ArrowArith len Li Ri gi Lj Rj gj := by
    simp only [ArrowArith]
    omega
  have hM' : ArrowArith len Lj (p + 1) gj Li Ri gi ↔
      ArrowArith len Lj Rj gj Li Ri gi := by
    simp only [ArrowArith]
    omega
  rw [if_congr hM rfl rfl, if_congr hM' rfl rfl, hcorr, ite_self]
  ring

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_5_3 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (hlri : Li < Ri)
    (_hlrj : Lj < Rj)
    (hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (_hui0 : Li ≠ p + 1)
    (hui1 : Li ≠ p + 2)
    (hui2 : Li ≠ p + 3)
    (hui3 : Ri ≠ p + 1)
    (hui4 : Ri ≠ p + 2)
    (hui5 : Ri ≠ p + 3)
    (_hgj : gj = b)
    (hlj : Lj = p + 2)
    (hrj : p + 4 ≤ Rj) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = p + 3 := by rw [hLj]; split_ifs; omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  have hcorr : ((if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
      (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
      (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
      (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) = 0 := by
    have c1 : ¬(Ri = p + 1 ∨ Li = p + 2) := by omega
    have c4 : ¬(Li = p + 3 ∨ Ri = p + 2) := by omega
    rw [if_neg c1, if_neg c4]
    ring
  have hM : ArrowArith len Li Ri gi (p + 3) Rj gj ↔
      ArrowArith len Li Ri gi Lj Rj gj := by
    simp only [ArrowArith]
    omega
  have hM' : ArrowArith len (p + 3) Rj gj Li Ri gi ↔
      ArrowArith len Lj Rj gj Li Ri gi := by
    simp only [ArrowArith]
    omega
  rw [if_congr hM rfl rfl, if_congr hM' rfl rfl, hcorr, ite_self]
  ring

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_5_4 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (_hui0 : Li ≠ p + 1)
    (hui1 : Li ≠ p + 2)
    (hui2 : Li ≠ p + 3)
    (hui3 : Ri ≠ p + 1)
    (hui4 : Ri ≠ p + 2)
    (hui5 : Ri ≠ p + 3)
    (_hgj : gj = a)
    (hlj : Lj = p + 3)
    (_hrj : p + 4 ≤ Rj) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = p + 2 := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  have hcorr : ((if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
      (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
      (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
      (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) = 0 := by
    have c1 : ¬(Ri = p + 1 ∨ Li = p + 2) := by omega
    have c4 : ¬(Li = p + 3 ∨ Ri = p + 2) := by omega
    rw [if_neg c1, if_neg c4]
    ring
  have hM : ArrowArith len Li Ri gi (p + 2) Rj gj ↔
      ArrowArith len Li Ri gi Lj Rj gj := by
    simp only [ArrowArith]
    omega
  have hM' : ArrowArith len (p + 2) Rj gj Li Ri gi ↔
      ArrowArith len Lj Rj gj Li Ri gi := by
    simp only [ArrowArith]
    omega
  rw [if_congr hM rfl rfl, if_congr hM' rfl rfl, hcorr, ite_self]
  ring

set_option maxHeartbeats 2000000 in
-- a twenty-hypothesis case split; see the module docstring
private theorem arith_5_5 {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (_hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (_hlei : Li ≤ len)
    (_hlej : Lj ≤ len)
    (_hLL : gi ≠ gj → Li = Lj → Li = 0)
    (_hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (_hLR : gi ≠ gj → Li ≠ Rj)
    (_hRL : gi ≠ gj → Ri ≠ Lj)
    (_hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (_hui0 : Li ≠ p + 1)
    (hui1 : Li ≠ p + 2)
    (hui2 : Li ≠ p + 3)
    (hui3 : Ri ≠ p + 1)
    (hui4 : Ri ≠ p + 2)
    (hui5 : Ri ≠ p + 3)
    (huj0 : Lj ≠ p + 1)
    (huj1 : Lj ≠ p + 2)
    (huj2 : Lj ≠ p + 3)
    (huj3 : Rj ≠ p + 1)
    (huj4 : Rj ≠ p + 2)
    (huj5 : Rj ≠ p + 3) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  have eLi : Li' = Li := by rw [hLi]; split_ifs <;> omega
  have eRi : Ri' = Ri := by rw [hRi]; split_ifs <;> omega
  have eLj : Lj' = Lj := by rw [hLj]; split_ifs <;> omega
  have eRj : Rj' = Rj := by rw [hRj]; split_ifs <;> omega
  rw [eLi, eRi, eLj, eRj]
  simp only [ArrowArith]
  norm_num
  split_ifs <;> omega

/-- **The arrow comparison, over plain naturals.** For two chambers classified by
`ends_cases_of_ne_braidSite`, the signed arrow count after the move equals the signed count before
it plus the mutation's correction term. Twenty-five cases: the four neighbours of the site against
each other, against an untouched chamber, and two untouched chambers. -/
theorem signed_arrowArith_eq {p a b len Li Ri Lj Rj Li' Ri' Lj' Rj' gi gj : ℕ}
    (hp : p + 3 ≤ len)
    (hab : a + 1 = b)
    (hLi : Li' = if Li = p + 2 then p + 3 else if Li = p + 3 then p + 2 else Li)
    (hRi : Ri' = if Ri = p + 1 then p + 2 else if Ri = p + 2 then p + 1 else Ri)
    (hLj : Lj' = if Lj = p + 2 then p + 3 else if Lj = p + 3 then p + 2 else Lj)
    (hRj : Rj' = if Rj = p + 1 then p + 2 else if Rj = p + 2 then p + 1 else Rj)
    (hlri : Li < Ri)
    (hlrj : Lj < Rj)
    (hlei : Li ≤ len)
    (hlej : Lj ≤ len)
    (hLL : gi ≠ gj → Li = Lj → Li = 0)
    (hRR : gi ≠ gj → Ri = Rj → Ri = len + 1)
    (hLR : gi ≠ gj → Li ≠ Rj)
    (hRL : gi ≠ gj → Ri ≠ Lj)
    (hsame : gi = gj → (Li = Lj ∧ Ri = Rj) ∨ Ri ≤ Lj ∨ Rj ≤ Li)
    (hci : (gi = a ∧ Li ≤ p ∧ Ri = p + 1) ∨
        (gi = b ∧ Li ≤ p ∧ Ri = p + 2) ∨
        (gi = b ∧ Li = p + 2 ∧ p + 4 ≤ Ri) ∨
        (gi = a ∧ Li = p + 3 ∧ p + 4 ≤ Ri) ∨
        (Li ≠ p + 1 ∧ Li ≠ p + 2 ∧ Li ≠ p + 3 ∧
          Ri ≠ p + 1 ∧ Ri ≠ p + 2 ∧ Ri ≠ p + 3))
    (hcj : (gj = a ∧ Lj ≤ p ∧ Rj = p + 1) ∨
        (gj = b ∧ Lj ≤ p ∧ Rj = p + 2) ∨
        (gj = b ∧ Lj = p + 2 ∧ p + 4 ≤ Rj) ∨
        (gj = a ∧ Lj = p + 3 ∧ p + 4 ≤ Rj) ∨
        (Lj ≠ p + 1 ∧ Lj ≠ p + 2 ∧ Lj ≠ p + 3 ∧
          Rj ≠ p + 1 ∧ Rj ≠ p + 2 ∧ Rj ≠ p + 3)) :
    ((if ArrowArith len Li' Ri' gi Lj' Rj' gj then (1 : ℤ) else 0) -
        (if ArrowArith len Lj' Rj' gj Li' Ri' gi then (1 : ℤ) else 0)) =
      ((if ArrowArith len Li Ri gi Lj Rj gj then (1 : ℤ) else 0) -
          (if ArrowArith len Lj Rj gj Li Ri gi then (1 : ℤ) else 0)) +
        (if ¬(Li ≠ 0 ∧ Ri ≠ len + 1) ∧ ¬(Lj ≠ 0 ∧ Rj ≠ len + 1) then 0
          else (if Ri = p + 1 ∨ Li = p + 2 then (1 : ℤ) else 0) *
              (if Lj = p + 3 ∨ Rj = p + 2 then (1 : ℤ) else 0) -
            (if Rj = p + 1 ∨ Lj = p + 2 then (1 : ℤ) else 0) *
              (if Li = p + 3 ∨ Ri = p + 2 then (1 : ℤ) else 0)) := by
  rcases hci with ⟨hgi, hli, hri⟩ | ⟨hgi, hli, hri⟩ | ⟨hgi, hli, hri⟩ |
      ⟨hgi, hli, hri⟩ | ⟨hui0, hui1, hui2, hui3, hui4, hui5⟩
  · rcases hcj with ⟨hgj, hlj, hrj⟩ | ⟨hgj, hlj, hrj⟩ | ⟨hgj, hlj, hrj⟩ |
        ⟨hgj, hlj, hrj⟩ | ⟨huj0, huj1, huj2, huj3, huj4, huj5⟩
    · exact arith_1_1 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_1_2 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_1_3 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_1_4 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_1_5 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri huj0 huj1 huj2 huj3 huj4 huj5
  · rcases hcj with ⟨hgj, hlj, hrj⟩ | ⟨hgj, hlj, hrj⟩ | ⟨hgj, hlj, hrj⟩ |
        ⟨hgj, hlj, hrj⟩ | ⟨huj0, huj1, huj2, huj3, huj4, huj5⟩
    · exact arith_2_1 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_2_2 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_2_3 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_2_4 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_2_5 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri huj0 huj1 huj2 huj3 huj4 huj5
  · rcases hcj with ⟨hgj, hlj, hrj⟩ | ⟨hgj, hlj, hrj⟩ | ⟨hgj, hlj, hrj⟩ |
        ⟨hgj, hlj, hrj⟩ | ⟨huj0, huj1, huj2, huj3, huj4, huj5⟩
    · exact arith_3_1 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_3_2 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_3_3 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_3_4 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_3_5 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri huj0 huj1 huj2 huj3 huj4 huj5
  · rcases hcj with ⟨hgj, hlj, hrj⟩ | ⟨hgj, hlj, hrj⟩ | ⟨hgj, hlj, hrj⟩ |
        ⟨hgj, hlj, hrj⟩ | ⟨huj0, huj1, huj2, huj3, huj4, huj5⟩
    · exact arith_4_1 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_4_2 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_4_3 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_4_4 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri hgj hlj hrj
    · exact arith_4_5 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hgi hli hri huj0 huj1 huj2 huj3 huj4 huj5
  · rcases hcj with ⟨hgj, hlj, hrj⟩ | ⟨hgj, hlj, hrj⟩ | ⟨hgj, hlj, hrj⟩ |
        ⟨hgj, hlj, hrj⟩ | ⟨huj0, huj1, huj2, huj3, huj4, huj5⟩
    · exact arith_5_1 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hui0 hui1 hui2 hui3 hui4 hui5 hgj hlj hrj
    · exact arith_5_2 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hui0 hui1 hui2 hui3 hui4 hui5 hgj hlj hrj
    · exact arith_5_3 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hui0 hui1 hui2 hui3 hui4 hui5 hgj hlj hrj
    · exact arith_5_4 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hui0 hui1 hui2 hui3 hui4 hui5 hgj hlj hrj
    · exact arith_5_5 hp hab hLi hRi hLj hRj hlri hlrj hlei hlej hLL
        hRR hLR hRL hsame hui0 hui1 hui2 hui3 hui4 hui5 huj0 huj1 huj2 huj3 huj4 huj5

end WiringDiagram

end ClusterAlgebras

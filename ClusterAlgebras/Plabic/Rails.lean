/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.TripleDiagram

/-!
# Rails, the push-off and the combings

Several move-equivalences of triple diagrams in [FWZ] relate explicit local pictures of triple
diagrams. Each left-hand picture is a *rail*: a run of consecutive triple
points `x₀, x₁, …` of one strand together with triple points `y₁, y₂, …` of a second strand
running alongside, each `y_j` joined to the first strand by a pair of edges. The darts of a triple
point `u` are indexed from a named dart `c` of `u` counterclockwise, as `σ^k(c)`; for the rails
these are `ρ_{j,k} = σ^k(ρ_{j,0})` at `x_j` and `η_{j,k} = σ^k(η_{j,0})` at `y_j`.

* An *aligned rail* of length `r ≥ 0` has points `x₀, …, x_r, y₁, …, y_r` with
  `ρ̄_{j,3} = ρ_{j+1,0}`, `η̄_{j,3} = η_{j+1,0}` (`j ∈ [0, r - 1]`) and `ρ̄_{j,1} = η_{j,5}`,
  `ρ̄_{j,2} = η_{j,4}` (`j ∈ [1, r]`), with the convention `η_{0,3} = ρ_{0,2}`.
* A *closed aligned rail* of length `n ≥ 1` is an aligned rail of length `n - 1` together with a
  further triple point `x_n` and a dart `ρ_{n,0}` at it with `ρ̄_{n-1,3} = ρ_{n,0}` and
  `η̄_{n-1,3} = ρ_{n,1}`.
* A *staggered rail* of length `r ≥ 1` has points `x₀, …, x_r, y₁, …, y_r` with
  `ρ̄_{j,3} = ρ_{j+1,0}` (`j ∈ [0, r - 1]`), `ρ̄_{0,1} = η_{1,0}`, `η̄_{j,3} = η_{j+1,0}`
  (`j ∈ [1, r - 1]`), `ρ̄_{j-1,2} = η_{j,5}` and `ρ̄_{j,1} = η_{j,4}` (`j ∈ [1, r]`).

The right-hand pictures keep the darts, the involution, the boundary, the labelling and the
orientation, and change the rotation on the set `D` of darts at the points of the rail: there it is
prescribed by a list of `6`-tuples `(u₀, …, u₅)`, meaning `σ'(u_k) = u_{k+1}` (indices modulo
`6`); outside `D` it is `σ`. These are the *push-off* of a closed aligned rail, the *aligned
combing* of an aligned rail and the *staggered combing* of a staggered rail. In each case every
dart of `D` occurs exactly once among the entries of the tuples, so that `σ'` has the tuples as
its cycles on `D`.

## Main definitions

* `ClusterAlgebras.TripleData.AlignedRail`: aligned rails.
* `ClusterAlgebras.TripleData.ClosedAlignedRail`: closed aligned rails.
* `ClusterAlgebras.TripleData.StaggeredRail`: staggered rails.
* `ClusterAlgebras.TripleData.ClosedAlignedRail.pushOff`: the push-off along a closed aligned rail.
* `ClusterAlgebras.TripleData.AlignedRail.alignedComb`: the aligned combing.
* `ClusterAlgebras.TripleData.StaggeredRail.staggeredComb`: the staggered combing.

## Main results

* `ClusterAlgebras.TripleData.ClosedAlignedRail.nodup_flatten_pushOffTuples`,
  `toFinset_flatten_pushOffTuples`, `pushOff_rot_of_notMem`, `pushOff_rot_getElem`: the push-off
  is well defined.
* `ClusterAlgebras.TripleData.AlignedRail.nodup_flatten_alignedCombTuples`,
  `toFinset_flatten_alignedCombTuples`, `alignedComb_rot_of_notMem`, `alignedComb_rot_getElem`:
  the aligned combing is well defined.
* `ClusterAlgebras.TripleData.StaggeredRail.nodup_flatten_staggeredCombTuples`,
  `toFinset_flatten_staggeredCombTuples`, `staggeredComb_rot_of_notMem`,
  `staggeredComb_rot_getElem`: the staggered combing is well defined.

## Implementation notes

* **Labels.** The darts of a rail are named by *rail labels* `(a, k) : (ℕ ⊕ ℕ) × ℕ`:
  `RailLabel.rho j k = (inl j, k)` names `ρ_{j,k}` and `RailLabel.eta j k = (inr j, k)` names
  `η_{j,k}`. A rail records the darts `ρ_{j,0}` and `η_{j,0}` as functions `rho eta : ℕ → H`, of
  which only the values at the indices of its points matter, and `TripleData.railDart rho eta`
  sends a label to its dart `σ^k(ρ_{j,0})` or `σ^k(η_{j,0})`. The convention
  `(η_{0,2}, η_{0,3}, η_{0,4}, η_{0,5}) = (ρ_{0,1}, ρ_{0,2}, ρ_{0,5}, ρ_{0,0})` of aligned rails
  is the label `RailLabel.alignedEta j k`, which is `η_{j,k}` for `j ≥ 1`. The tuples of each
  construction are first written as lists of labels (`pushOffLabels`, `alignedCombLabels`,
  `staggeredCombLabels`), which are independent of the diagram; that every label of a point of the
  rail occurs exactly once among them is a statement about labels alone.
* **The rotation.** Given a set `D` of darts closed under `σ` and a list of tuples, the rotation
  `prescribedRot` is the product of the cyclic permutations `List.formPerm` of the tuples, followed
  by `σ` on the darts outside `D`. It is a permutation and is computable whatever the tuples are;
  when the entries of the tuples are distinct darts of `D`, it agrees with `σ` outside `D` and has
  the tuples as its cycles (`prescribedRot_apply_of_notMem`, `prescribedRot_apply_getElem`).
* **Examples.** The last section evaluates the smallest instances of the three constructions by
  `decide`, on explicit triple diagrams whose triple points are the points of the rail.
* **Lengths.** The aligned combing is defined, and is well defined, for aligned rails of every
  length `r ≥ 0`; FWZ require `r ≥ 1`, and for `r = 0` the single tuple is the rotation at
  `x₀`, so that the combing is the diagram itself. The push-off and the staggered combing require
  the length `n ≥ 1`, resp. `r ≥ 1`, which is a field of the rail.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Orbits of the rotation at a vertex of known size -/

namespace RotationSystem

variable {H : Type*} [Fintype H] [DecidableEq H] (R : RotationSystem H)

/-- At a vertex with `n` darts, the darts `σ^i(d)` for `i < n` are pairwise distinct. -/
theorem pow_apply_injective_of_card_vertexOf {d : H} {n i j : ℕ} (hcard : (R.vertexOf d).card = n)
    (hi : i < n) (hj : j < n) (h : (R.rot ^ i) d = (R.rot ^ j) d) : i = j := by
  wlog hij : i < j generalizing i j
  · rcases Nat.lt_or_ge j i with h' | h'
    · exact (this hj hi h.symm h').symm
    · omega
  have hper : (R.rot ^ (j - i)) ((R.rot ^ i) d) = (R.rot ^ i) d := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hij.le]
    exact h.symm
  have hve : R.vertexOf ((R.rot ^ i) d) = R.vertexOf d :=
    R.vertexOf_eq_of_mem
      (R.mem_vertexOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)))
  generalize (R.rot ^ i) d = e at hper hve
  have hsub : R.vertexOf e ⊆ (range (j - i)).image fun k => (R.rot ^ k) e := by
    intro x hx
    obtain ⟨N, hN⟩ := (R.mem_vertexOf.1 hx).exists_nat_pow_eq
    have hpp : Function.IsPeriodicPt R.rot (j - i) e := by
      change (⇑R.rot)^[j - i] e = e
      rw [Equiv.Perm.iterate_eq_pow, hper]
    have hmod := hpp.iterate_mod_apply N
    rw [Equiv.Perm.iterate_eq_pow, Equiv.Perm.iterate_eq_pow] at hmod
    exact mem_image.2 ⟨N % (j - i), mem_range.2 (Nat.mod_lt _ (by omega)), hmod.trans hN⟩
  have := (card_le_card hsub).trans card_image_le
  rw [hve, hcard, card_range] at this
  omega

/-- At a vertex with `n` darts, every dart of the vertex of `d` is `σ^k(d)` for some `k < n`. -/
theorem exists_pow_apply_eq_of_card_vertexOf {d e : H} {n : ℕ} (hcard : (R.vertexOf d).card = n)
    (he : e ∈ R.vertexOf d) : ∃ k < n, (R.rot ^ k) d = e := by
  have hsub : (range n).image (fun k => (R.rot ^ k) d) ⊆ R.vertexOf d := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := mem_image.1 hx
    exact R.mem_vertexOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))
  have hcardim : ((range n).image (fun k => (R.rot ^ k) d)).card = n := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    exact R.pow_apply_injective_of_card_vertexOf hcard (mem_range.1 hi) (mem_range.1 hj) h
  rw [← eq_of_subset_of_card_le hsub (by rw [hcard, hcardim])] at he
  obtain ⟨k, hk, rfl⟩ := mem_image.1 he
  exact ⟨k, mem_range.1 hk, rfl⟩

end RotationSystem

/-! ### Rotations with prescribed cycles -/

/-- A list whose length is at most the number of its distinct entries has no duplicates. -/
private theorem nodup_of_length_le_card_toFinset {α : Type*} [DecidableEq α] {l : List α}
    (h : l.length ≤ l.toFinset.card) : l.Nodup := by
  rw [List.card_toFinset] at h
  rw [← (List.dedup_sublist l).eq_of_length_le h]
  exact List.nodup_dedup l

section PrescribedRot

variable {H : Type*} [DecidableEq H]

/-- The permutation that agrees with `σ` outside a set `D` of darts closed under `σ` and is
prescribed on `D` by a list `cs` of tuples, `(u₀, …, u_{m-1})` meaning `u_k ↦ u_{k+1}` (indices
modulo `m`): the product of the cyclic permutations `List.formPerm` of the tuples, followed by `σ`
on the darts outside `D`. When the entries of the tuples are distinct darts of `D`, its cycles on
`D` are the tuples (`prescribedRot_apply_getElem`) and it agrees with `σ` outside `D`
(`prescribedRot_apply_of_notMem`). -/
def prescribedRot (σ : Equiv.Perm H) (D : Finset H) (hD : ∀ d, σ d ∈ D ↔ d ∈ D)
    (cs : List (List H)) : Equiv.Perm H :=
  @Equiv.Perm.ofSubtype H (fun d => d ∉ D) _ (σ.subtypePerm fun d => not_congr (hD d)) *
    (cs.map List.formPerm).prod

/-- A dart that is no entry of the tuples is fixed by the product of their cyclic permutations. -/
theorem prod_map_formPerm_apply_of_notMem {cs : List (List H)} {x : H} (hx : x ∉ cs.flatten) :
    (cs.map List.formPerm).prod x = x := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatten_cons, List.mem_append, not_or] at hx
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hx.2,
      List.formPerm_apply_of_notMem hx.1]

/-- If the entries of the tuples are distinct, the product of their cyclic permutations acts on
the entries of a tuple `l` as the cyclic permutation of `l`. -/
theorem prod_map_formPerm_apply_of_mem {cs : List (List H)} (hnd : cs.flatten.Nodup) {l : List H}
    (hl : l ∈ cs) {x : H} (hx : x ∈ l) : (cs.map List.formPerm).prod x = l.formPerm x := by
  induction cs with
  | nil => simp at hl
  | cons c cs ih =>
    rw [List.flatten_cons, List.nodup_append] at hnd
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    rcases List.mem_cons.1 hl with rfl | hl
    · have hx' : x ∉ cs.flatten := fun h => hnd.2.2 x hx x h rfl
      rw [prod_map_formPerm_apply_of_notMem hx']
    · rw [ih hnd.2.1 hl]
      exact List.formPerm_apply_of_notMem fun h =>
        hnd.2.2 _ h _ (List.mem_flatten.2 ⟨l, hl, List.formPerm_apply_mem_of_mem hx⟩) rfl

variable {σ : Equiv.Perm H} {D : Finset H} {hD : ∀ d, σ d ∈ D ↔ d ∈ D} {cs : List (List H)}

/-- If the entries of the tuples lie in `D`, the prescribed rotation agrees with `σ` outside
`D`. -/
theorem prescribedRot_apply_of_notMem (hsub : ∀ x ∈ cs.flatten, x ∈ D) {d : H} (hd : d ∉ D) :
    prescribedRot σ D hD cs d = σ d := by
  rw [prescribedRot, Equiv.Perm.mul_apply,
    prod_map_formPerm_apply_of_notMem fun h => hd (hsub d h),
    Equiv.Perm.ofSubtype_apply_of_mem (p := fun d => d ∉ D) _ hd, Equiv.Perm.subtypePerm_apply]

/-- If the entries of the tuples are distinct darts of `D`, the prescribed rotation sends the
`i`-th entry of a tuple `l` to the next one, `l[(i + 1) % |l|]`. -/
theorem prescribedRot_apply_getElem (hnd : cs.flatten.Nodup) (hsub : ∀ x ∈ cs.flatten, x ∈ D)
    {l : List H} (hl : l ∈ cs) (i : ℕ) (hi : i < l.length) :
    prescribedRot σ D hD cs l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) := by
  have hlnd : l.Nodup := (List.nodup_flatten.1 hnd).1 l hl
  rw [prescribedRot, Equiv.Perm.mul_apply,
    prod_map_formPerm_apply_of_mem hnd hl (List.getElem_mem hi),
    List.formPerm_apply_getElem _ hlnd]
  refine Equiv.Perm.ofSubtype_apply_of_not_mem _ (not_not.2 (hsub _ ?_))
  exact List.mem_flatten.2 ⟨l, hl, List.getElem_mem _⟩

end PrescribedRot

/-! ### Rail labels -/

/-- A **rail label** `(a, k)` names the dart `σ^k(c_a)` of a rail, where `c_a` is the named dart of
the point `a`: `a = inl j` is the point `x_j` with named dart `ρ_{j,0}`, and `a = inr j` is the
point `y_j` with named dart `η_{j,0}`. -/
abbrev RailLabel : Type := (ℕ ⊕ ℕ) × ℕ

namespace RailLabel

/-- The label of `ρ_{j,k} = σ^k(ρ_{j,0})`, a dart at `x_j`. -/
def rho (j k : ℕ) : RailLabel := (.inl j, k)

/-- The label of `η_{j,k} = σ^k(η_{j,0})`, a dart at `y_j`. -/
def eta (j k : ℕ) : RailLabel := (.inr j, k)

/-- The index `k'` with `η_{0,k} = ρ_{0,k'}` in the convention of aligned rails:
`(η_{0,2}, η_{0,3}, η_{0,4}, η_{0,5}) = (ρ_{0,1}, ρ_{0,2}, ρ_{0,5}, ρ_{0,0})`. The other values are
not used. -/
def alignedIndex : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 4 => 5
  | _ => 0

/-- The label of `η_{j,k}` with the convention of aligned rails: `η_{j,k}` for `j ≥ 1`, and
`(η_{0,2}, η_{0,3}, η_{0,4}, η_{0,5}) = (ρ_{0,1}, ρ_{0,2}, ρ_{0,5}, ρ_{0,0})`. -/
def alignedEta (j k : ℕ) : RailLabel := if j = 0 then rho 0 (alignedIndex k) else eta j k

/-- The points `x₀, …, x_p, y₁, …, y_q` of a rail: `inl j` for `j ∈ [0, p]` and `inr j` for
`j ∈ [1, q]`. -/
def pointSet (p q : ℕ) : Finset (ℕ ⊕ ℕ) := (range (p + 1)).disjSum (Icc 1 q)

/-- The labels of the darts at the points `x₀, …, x_p, y₁, …, y_q` of a rail: the labels `(a, k)`
of a point `a` and `k ∈ [0, 5]`. -/
def labelSet (p q : ℕ) : Finset RailLabel := pointSet p q ×ˢ range 6

/-- The label `ρ_{j,k}` with `j ≤ p` and `k < 6` lies in `labelSet p q`. -/
theorem rho_mem_labelSet {p q j k : ℕ} (hj : j ≤ p) (hk : k < 6) : rho j k ∈ labelSet p q := by
  simp [rho, labelSet, pointSet]
  omega

/-- The label `η_{j,k}` with `1 ≤ j ≤ q` and `k < 6` lies in `labelSet p q`. -/
theorem eta_mem_labelSet {p q j k : ℕ} (hj : 1 ≤ j) (hj' : j ≤ q) (hk : k < 6) :
    eta j k ∈ labelSet p q := by
  simp [eta, labelSet, pointSet]
  omega

/-- The label `alignedEta j k` with `j ≤ q` and `k < 6` lies in `labelSet p q`. -/
theorem alignedEta_mem_labelSet {p q j k : ℕ} (hj : j ≤ q) (hk : k < 6) :
    alignedEta j k ∈ labelSet p q := by
  unfold alignedEta
  split_ifs with h
  · exact rho_mem_labelSet (Nat.zero_le _) (by unfold alignedIndex; split <;> omega)
  · exact eta_mem_labelSet (by omega) hj hk

/-- The labels in `labelSet p q` are the `ρ_{j,k}` with `j ≤ p` and the `η_{j,k}` with
`1 ≤ j ≤ q`, for `k < 6`. -/
theorem mem_labelSet {p q : ℕ} {x : RailLabel} :
    x ∈ labelSet p q ↔
      (∃ j ≤ p, ∃ k < 6, x = rho j k) ∨ ∃ j, 1 ≤ j ∧ j ≤ q ∧ ∃ k < 6, x = eta j k := by
  obtain ⟨a | a, k⟩ := x <;> simp [labelSet, pointSet, rho, eta]
  omega

/-- There are `6 (p + 1 + q)` labels of darts at the points of a rail. -/
theorem card_labelSet (p q : ℕ) : (labelSet p q).card = 6 * (p + 1 + q) := by
  simp only [labelSet, pointSet, card_product, card_disjSum, card_range, Nat.card_Icc]
  omega

/-- For `n ≥ 1`, the points `x₀, …, x_n, y₁, …, y_{n-1}` are `x_n` together with the points
`x₀, …, x_{n-1}, y₁, …, y_{n-1}`. -/
theorem mem_pointSet_iff_eq_or_mem {n : ℕ} (hn : 1 ≤ n) {a : ℕ ⊕ ℕ} :
    a ∈ pointSet n (n - 1) ↔ a = .inl n ∨ a ∈ pointSet (n - 1) (n - 1) := by
  cases a <;> simp [pointSet]
  omega

end RailLabel

open RailLabel

/-! ### The tuples of the three constructions, as labels -/

/-- The `2n` tuples of the push-off along a closed aligned rail of length `n`, as labels,
`η` read with the convention of aligned rails:
`(η_{j,5}, η_{j,2}, η_{j+1,1}, ρ_{j+1,1}, η_{j,3}, ρ_{j,3})` for `j ∈ [0, n - 2]`,
`(η_{n-1,5}, η_{n-1,2}, ρ_{n,2}, ρ_{n,3}, η_{n-1,3}, ρ_{n-1,3})`,
`(ρ_{j,2}, ρ_{j,5}, ρ_{j-1,4}, η_{j-1,4}, ρ_{j,0}, η_{j,0})` for `j ∈ [1, n - 1]`, and
`(ρ_{n,4}, ρ_{n,5}, ρ_{n-1,4}, η_{n-1,4}, ρ_{n,0}, ρ_{n,1})`. -/
def pushOffLabels (n : ℕ) : List (List RailLabel) :=
  (List.range (n - 1)).map (fun j =>
      [alignedEta j 5, alignedEta j 2, alignedEta (j + 1) 1, rho (j + 1) 1, alignedEta j 3,
        rho j 3]) ++
    [[alignedEta (n - 1) 5, alignedEta (n - 1) 2, rho n 2, rho n 3, alignedEta (n - 1) 3,
      rho (n - 1) 3]] ++
    (List.range' 1 (n - 1)).map (fun j =>
      [rho j 2, rho j 5, rho (j - 1) 4, alignedEta (j - 1) 4, rho j 0, alignedEta j 0]) ++
    [[rho n 4, rho n 5, rho (n - 1) 4, alignedEta (n - 1) 4, rho n 0, rho n 1]]

/-- The `2r + 1` tuples of the aligned combing of an aligned rail of length `r`, as labels,
`η` read with the convention of aligned rails:
`(η_{j,5}, η_{j,2}, η_{j+1,1}, ρ_{j+1,1}, η_{j,3}, ρ_{j,3})` for `j ∈ [0, r - 1]`,
`(η_{r,5}, η_{r,2}, η_{r,3}, ρ_{r,3}, ρ_{r,4}, η_{r,4})`, and
`(ρ_{j,2}, ρ_{j,5}, ρ_{j-1,4}, η_{j-1,4}, ρ_{j,0}, η_{j,0})` for `j ∈ [1, r]`. -/
def alignedCombLabels (r : ℕ) : List (List RailLabel) :=
  (List.range r).map (fun j =>
      [alignedEta j 5, alignedEta j 2, alignedEta (j + 1) 1, rho (j + 1) 1, alignedEta j 3,
        rho j 3]) ++
    [[alignedEta r 5, alignedEta r 2, alignedEta r 3, rho r 3, rho r 4, alignedEta r 4]] ++
    (List.range' 1 r).map (fun j =>
      [rho j 2, rho j 5, rho (j - 1) 4, alignedEta (j - 1) 4, rho j 0, alignedEta j 0])

/-- The `2r + 1` tuples of the staggered combing of a staggered rail of length `r`, as labels:
`(ρ_{0,0}, η_{1,1}, η_{1,2}, ρ_{0,1}, ρ_{0,2}, ρ_{0,5})`,
`(η_{j,0}, η_{j+1,1}, η_{j+1,2}, η_{j,3}, ρ_{j,2}, ρ_{j-1,3})` for `j ∈ [1, r - 1]`,
`(η_{r,0}, η_{r,3}, ρ_{r,2}, ρ_{r,3}, η_{r,4}, ρ_{r-1,3})`,
`(ρ_{1,0}, ρ_{1,1}, ρ_{1,4}, ρ_{1,5}, ρ_{0,4}, η_{1,5})`, and
`(ρ_{j,0}, ρ_{j,1}, ρ_{j,4}, ρ_{j,5}, η_{j-1,4}, η_{j,5})` for `j ∈ [2, r]`. -/
def staggeredCombLabels (r : ℕ) : List (List RailLabel) :=
  [[rho 0 0, eta 1 1, eta 1 2, rho 0 1, rho 0 2, rho 0 5]] ++
    (List.range' 1 (r - 1)).map (fun j =>
      [eta j 0, eta (j + 1) 1, eta (j + 1) 2, eta j 3, rho j 2, rho (j - 1) 3]) ++
    [[eta r 0, eta r 3, rho r 2, rho r 3, eta r 4, rho (r - 1) 3]] ++
    [[rho 1 0, rho 1 1, rho 1 4, rho 1 5, rho 0 4, eta 1 5]] ++
    (List.range' 2 (r - 1)).map (fun j =>
      [rho j 0, rho j 1, rho j 4, rho j 5, eta (j - 1) 4, eta j 5])

/-- Each tuple of the push-off has `6` entries. -/
theorem length_of_mem_pushOffLabels {n : ℕ} {l : List RailLabel} (hl : l ∈ pushOffLabels n) :
    l.length = 6 := by
  simp only [pushOffLabels, List.mem_append, List.mem_map, List.mem_singleton] at hl
  rcases hl with ((⟨j, -, rfl⟩ | rfl) | ⟨j, -, rfl⟩) | rfl <;> rfl

/-- Each tuple of the aligned combing has `6` entries. -/
theorem length_of_mem_alignedCombLabels {r : ℕ} {l : List RailLabel}
    (hl : l ∈ alignedCombLabels r) : l.length = 6 := by
  simp only [alignedCombLabels, List.mem_append, List.mem_map, List.mem_singleton] at hl
  rcases hl with (⟨j, -, rfl⟩ | rfl) | ⟨j, -, rfl⟩ <;> rfl

/-- Each tuple of the staggered combing has `6` entries. -/
theorem length_of_mem_staggeredCombLabels {r : ℕ} {l : List RailLabel}
    (hl : l ∈ staggeredCombLabels r) : l.length = 6 := by
  simp only [staggeredCombLabels, List.mem_append, List.mem_map, List.mem_singleton] at hl
  rcases hl with (((rfl | ⟨j, -, rfl⟩) | rfl) | rfl) | ⟨j, -, rfl⟩ <;> rfl

private theorem mem_pushOffLabels_A {n j : ℕ} {x : RailLabel} (hj : j < n - 1)
    (hx : x ∈ [alignedEta j 5, alignedEta j 2, alignedEta (j + 1) 1, rho (j + 1) 1,
      alignedEta j 3, rho j 3]) : x ∈ (pushOffLabels n).flatten :=
  List.mem_flatten.2 ⟨_, List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_map_of_mem (f := fun j => [alignedEta j 5, alignedEta j 2,
      alignedEta (j + 1) 1, rho (j + 1) 1, alignedEta j 3, rho j 3]) (List.mem_range.2 hj)))), hx⟩

private theorem mem_pushOffLabels_B {n j : ℕ} {x : RailLabel} (hj : j + 1 = n)
    (hx : x ∈ [alignedEta j 5, alignedEta j 2, rho (j + 1) 2, rho (j + 1) 3, alignedEta j 3,
      rho j 3]) : x ∈ (pushOffLabels n).flatten := by
  subst hj
  exact List.mem_flatten.2 ⟨_, List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_singleton_self _))), by simpa using hx⟩

private theorem mem_pushOffLabels_C {n j : ℕ} {x : RailLabel} (hj : j + 1 < n)
    (hx : x ∈ [rho (j + 1) 2, rho (j + 1) 5, rho j 4, alignedEta j 4, rho (j + 1) 0,
      alignedEta (j + 1) 0]) : x ∈ (pushOffLabels n).flatten :=
  List.mem_flatten.2 ⟨_, List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨j + 1, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩)), by simpa using hx⟩

private theorem mem_pushOffLabels_E {n j : ℕ} {x : RailLabel} (hj : j + 1 = n)
    (hx : x ∈ [rho (j + 1) 4, rho (j + 1) 5, rho j 4, alignedEta j 4, rho (j + 1) 0,
      rho (j + 1) 1]) : x ∈ (pushOffLabels n).flatten := by
  subst hj
  exact List.mem_flatten.2 ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
    by simpa using hx⟩

private theorem rho_mem_flatten_pushOffLabels {n j k : ℕ} (hn : 1 ≤ n) (hj : j ≤ n)
    (hk : k < 6) : rho j k ∈ (pushOffLabels n).flatten := by
  interval_cases k
  · -- ρ_{j,0}
    rcases j with _ | j
    · rcases Nat.lt_or_ge 0 (n - 1) with h | h
      · exact mem_pushOffLabels_A (j := 0) h (by simp [alignedEta, alignedIndex])
      · exact mem_pushOffLabels_B (j := 0) (by omega) (by simp [alignedEta, alignedIndex])
    · rcases Nat.lt_or_ge (j + 1) n with h | h
      · exact mem_pushOffLabels_C h (by simp)
      · exact mem_pushOffLabels_E (j := j) (by omega) (by simp)
  · -- ρ_{j,1}
    rcases j with _ | j
    · rcases Nat.lt_or_ge 0 (n - 1) with h | h
      · exact mem_pushOffLabels_A (j := 0) h (by simp [alignedEta, alignedIndex])
      · exact mem_pushOffLabels_B (j := 0) (by omega) (by simp [alignedEta, alignedIndex])
    · rcases Nat.lt_or_ge (j + 1) n with h | h
      · exact mem_pushOffLabels_A (j := j) (by omega) (by simp)
      · exact mem_pushOffLabels_E (j := j) (by omega) (by simp)
  · -- ρ_{j,2}
    rcases j with _ | j
    · rcases Nat.lt_or_ge 0 (n - 1) with h | h
      · exact mem_pushOffLabels_A (j := 0) h (by simp [alignedEta, alignedIndex])
      · exact mem_pushOffLabels_B (j := 0) (by omega) (by simp [alignedEta, alignedIndex])
    · rcases Nat.lt_or_ge (j + 1) n with h | h
      · exact mem_pushOffLabels_C h (by simp)
      · exact mem_pushOffLabels_B (j := j) (by omega) (by simp)
  · -- ρ_{j,3}
    rcases Nat.lt_or_ge j (n - 1) with h | h
    · exact mem_pushOffLabels_A h (by simp)
    · rcases Nat.lt_or_ge j n with h' | h'
      · exact mem_pushOffLabels_B (j := j) (by omega) (by simp)
      · obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        exact mem_pushOffLabels_B (j := j) (by omega) (by simp)
  · -- ρ_{j,4}
    rcases Nat.lt_or_ge (j + 1) n with h | h
    · exact mem_pushOffLabels_C h (by simp)
    · rcases Nat.lt_or_ge j n with h' | h'
      · exact mem_pushOffLabels_E (j := j) (by omega) (by simp)
      · obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        exact mem_pushOffLabels_E (j := j) (by omega) (by simp)
  · -- ρ_{j,5}
    rcases j with _ | j
    · rcases Nat.lt_or_ge 1 n with h | h
      · exact mem_pushOffLabels_C (j := 0) h (by simp [alignedEta, alignedIndex])
      · exact mem_pushOffLabels_E (j := 0) (by omega) (by simp [alignedEta, alignedIndex])
    · rcases Nat.lt_or_ge (j + 1) n with h | h
      · exact mem_pushOffLabels_C h (by simp)
      · exact mem_pushOffLabels_E (j := j) (by omega) (by simp)

private theorem eta_mem_flatten_pushOffLabels {n j k : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ n - 1)
    (hk : k < 6) : eta j k ∈ (pushOffLabels n).flatten := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  interval_cases k
  · exact mem_pushOffLabels_C (j := j) (by omega) (by simp [alignedEta])
  · exact mem_pushOffLabels_A (j := j) (by omega) (by simp [alignedEta])
  · rcases Nat.lt_or_ge (j + 1) (n - 1) with h | h
    · exact mem_pushOffLabels_A h (by simp [alignedEta])
    · exact mem_pushOffLabels_B (j := j + 1) (by omega) (by simp [alignedEta])
  · rcases Nat.lt_or_ge (j + 1) (n - 1) with h | h
    · exact mem_pushOffLabels_A h (by simp [alignedEta])
    · exact mem_pushOffLabels_B (j := j + 1) (by omega) (by simp [alignedEta])
  · rcases Nat.lt_or_ge (j + 2) n with h | h
    · exact mem_pushOffLabels_C (j := j + 1) h (by simp [alignedEta])
    · exact mem_pushOffLabels_E (j := j + 1) (by omega) (by simp [alignedEta])
  · rcases Nat.lt_or_ge (j + 1) (n - 1) with h | h
    · exact mem_pushOffLabels_A h (by simp [alignedEta])
    · exact mem_pushOffLabels_B (j := j + 1) (by omega) (by simp [alignedEta])

/-- For `n ≥ 1`, every label of `labelSet n (n - 1)` is an entry of a tuple of the push-off. -/
theorem mem_pushOffLabels_of_mem_labelSet {n : ℕ} (hn : 1 ≤ n) {x : RailLabel}
    (hx : x ∈ labelSet n (n - 1)) : x ∈ (pushOffLabels n).flatten := by
  rcases mem_labelSet.1 hx with ⟨j, hj, k, hk, rfl⟩ | ⟨j, hj1, hj, k, hk, rfl⟩
  exacts [rho_mem_flatten_pushOffLabels hn hj hk, eta_mem_flatten_pushOffLabels hj1 hj hk]

/-- For `n ≥ 1`, the tuples of the push-off have `6 (n + 1 + (n - 1))` entries in total. -/
theorem length_flatten_pushOffLabels {n : ℕ} (hn : 1 ≤ n) :
    (pushOffLabels n).flatten.length = 6 * (n + 1 + (n - 1)) := by
  simp [pushOffLabels, List.length_flatten, Function.comp_def]
  omega

/-- Every entry of a tuple of the push-off lies in `labelSet n (n - 1)`. -/
theorem mem_labelSet_of_mem_pushOffLabels {n : ℕ} {x : RailLabel}
    (hx : x ∈ (pushOffLabels n).flatten) : x ∈ labelSet n (n - 1) := by
  simp only [pushOffLabels, List.flatten_append, List.mem_append, List.mem_flatten, List.mem_map,
    List.mem_range, List.mem_range', List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ((⟨l, ⟨j, hj, rfl⟩, hx⟩ | ⟨l, rfl, hx⟩) | ⟨l, ⟨j, ⟨i, hi, rfl⟩, rfl⟩, hx⟩) |
      ⟨l, rfl, hx⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact rho_mem_labelSet (by omega) (by omega)
    | exact alignedEta_mem_labelSet (by omega) (by omega)

/-- The tuples of the aligned combing have `6 (r + 1 + r)` entries in total. -/
theorem length_flatten_alignedCombLabels (r : ℕ) :
    (alignedCombLabels r).flatten.length = 6 * (r + 1 + r) := by
  simp [alignedCombLabels, List.length_flatten, Function.comp_def]
  omega

/-- Every entry of a tuple of the aligned combing lies in `labelSet r r`. -/
theorem mem_labelSet_of_mem_alignedCombLabels {r : ℕ} {x : RailLabel}
    (hx : x ∈ (alignedCombLabels r).flatten) : x ∈ labelSet r r := by
  simp only [alignedCombLabels, List.flatten_append, List.mem_append, List.mem_flatten,
    List.mem_map, List.mem_range, List.mem_range', List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with (⟨l, ⟨j, hj, rfl⟩, hx⟩ | ⟨l, rfl, hx⟩) | ⟨l, ⟨j, ⟨i, hi, rfl⟩, rfl⟩, hx⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact rho_mem_labelSet (by omega) (by omega)
    | exact alignedEta_mem_labelSet (by omega) (by omega)

private theorem mem_alignedCombLabels_A {r j : ℕ} {x : RailLabel} (hj : j < r)
    (hx : x ∈ [alignedEta j 5, alignedEta j 2, alignedEta (j + 1) 1, rho (j + 1) 1,
      alignedEta j 3, rho j 3]) : x ∈ (alignedCombLabels r).flatten :=
  List.mem_flatten.2 ⟨_, List.mem_append_left _ (List.mem_append_left _
    (List.mem_map_of_mem (f := fun j => [alignedEta j 5, alignedEta j 2,
      alignedEta (j + 1) 1, rho (j + 1) 1, alignedEta j 3, rho j 3]) (List.mem_range.2 hj))), hx⟩

private theorem mem_alignedCombLabels_B {r : ℕ} {x : RailLabel}
    (hx : x ∈ [alignedEta r 5, alignedEta r 2, alignedEta r 3, rho r 3, rho r 4,
      alignedEta r 4]) : x ∈ (alignedCombLabels r).flatten :=
  List.mem_flatten.2 ⟨_, List.mem_append_left _
    (List.mem_append_right _ (List.mem_singleton_self _)), hx⟩

private theorem mem_alignedCombLabels_C {r j : ℕ} {x : RailLabel} (hj : j + 1 ≤ r)
    (hx : x ∈ [rho (j + 1) 2, rho (j + 1) 5, rho j 4, alignedEta j 4, rho (j + 1) 0,
      alignedEta (j + 1) 0]) : x ∈ (alignedCombLabels r).flatten :=
  List.mem_flatten.2 ⟨_, List.mem_append_right _
    (List.mem_map.2 ⟨j + 1, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩), by simpa using hx⟩

private theorem rho_mem_flatten_alignedCombLabels {r j k : ℕ} (hj : j ≤ r) (hk : k < 6) :
    rho j k ∈ (alignedCombLabels r).flatten := by
  interval_cases k
  · rcases j with _ | j
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · exact mem_alignedCombLabels_B (by simp [alignedEta, alignedIndex])
      · exact mem_alignedCombLabels_A (j := 0) hr (by simp [alignedEta, alignedIndex])
    · exact mem_alignedCombLabels_C hj (by simp)
  · rcases j with _ | j
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · exact mem_alignedCombLabels_B (by simp [alignedEta, alignedIndex])
      · exact mem_alignedCombLabels_A (j := 0) hr (by simp [alignedEta, alignedIndex])
    · exact mem_alignedCombLabels_A (j := j) (by omega) (by simp)
  · rcases j with _ | j
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · exact mem_alignedCombLabels_B (by simp [alignedEta, alignedIndex])
      · exact mem_alignedCombLabels_A (j := 0) hr (by simp [alignedEta, alignedIndex])
    · exact mem_alignedCombLabels_C hj (by simp)
  · rcases Nat.lt_or_ge j r with h | h
    · exact mem_alignedCombLabels_A h (by simp)
    · obtain rfl : j = r := by omega
      exact mem_alignedCombLabels_B (by simp)
  · rcases Nat.lt_or_ge j r with h | h
    · exact mem_alignedCombLabels_C (j := j) h (by simp)
    · obtain rfl : j = r := by omega
      exact mem_alignedCombLabels_B (by simp)
  · rcases j with _ | j
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · exact mem_alignedCombLabels_B (by simp [alignedEta, alignedIndex])
      · exact mem_alignedCombLabels_C (j := 0) hr (by simp [alignedEta, alignedIndex])
    · exact mem_alignedCombLabels_C hj (by simp)

private theorem eta_mem_flatten_alignedCombLabels {r j k : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ r)
    (hk : k < 6) : eta j k ∈ (alignedCombLabels r).flatten := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  interval_cases k
  · exact mem_alignedCombLabels_C hj (by simp [alignedEta])
  · exact mem_alignedCombLabels_A (j := j) (by omega) (by simp [alignedEta])
  · rcases Nat.lt_or_ge (j + 1) r with h | h
    · exact mem_alignedCombLabels_A h (by simp [alignedEta])
    · obtain rfl : j + 1 = r := by omega
      exact mem_alignedCombLabels_B (by simp [alignedEta])
  · rcases Nat.lt_or_ge (j + 1) r with h | h
    · exact mem_alignedCombLabels_A h (by simp [alignedEta])
    · obtain rfl : j + 1 = r := by omega
      exact mem_alignedCombLabels_B (by simp [alignedEta])
  · rcases Nat.lt_or_ge (j + 1) r with h | h
    · exact mem_alignedCombLabels_C (j := j + 1) h (by simp [alignedEta])
    · obtain rfl : j + 1 = r := by omega
      exact mem_alignedCombLabels_B (by simp [alignedEta])
  · rcases Nat.lt_or_ge (j + 1) r with h | h
    · exact mem_alignedCombLabels_A h (by simp [alignedEta])
    · obtain rfl : j + 1 = r := by omega
      exact mem_alignedCombLabels_B (by simp [alignedEta])

/-- Every label of `labelSet r r` is an entry of a tuple of the aligned combing. -/
theorem mem_alignedCombLabels_of_mem_labelSet {r : ℕ} {x : RailLabel}
    (hx : x ∈ labelSet r r) : x ∈ (alignedCombLabels r).flatten := by
  rcases mem_labelSet.1 hx with ⟨j, hj, k, hk, rfl⟩ | ⟨j, hj1, hj, k, hk, rfl⟩
  exacts [rho_mem_flatten_alignedCombLabels hj hk, eta_mem_flatten_alignedCombLabels hj1 hj hk]

/-- For `r ≥ 1`, the tuples of the staggered combing have `6 (r + 1 + r)` entries in total. -/
theorem length_flatten_staggeredCombLabels {r : ℕ} (hr : 1 ≤ r) :
    (staggeredCombLabels r).flatten.length = 6 * (r + 1 + r) := by
  simp [staggeredCombLabels, List.length_flatten, Function.comp_def]
  omega

/-- For `r ≥ 1`, every entry of a tuple of the staggered combing lies in `labelSet r r`. -/
theorem mem_labelSet_of_mem_staggeredCombLabels {r : ℕ} (hr : 1 ≤ r) {x : RailLabel}
    (hx : x ∈ (staggeredCombLabels r).flatten) : x ∈ labelSet r r := by
  simp only [staggeredCombLabels, List.flatten_append, List.mem_append, List.mem_flatten,
    List.mem_map, List.mem_range', List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (((⟨l, rfl, hx⟩ | ⟨l, ⟨j, ⟨i, hi, rfl⟩, rfl⟩, hx⟩) | ⟨l, rfl, hx⟩) |
      ⟨l, rfl, hx⟩) | ⟨l, ⟨j, ⟨i, hi, rfl⟩, rfl⟩, hx⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact rho_mem_labelSet (by omega) (by omega)
    | exact eta_mem_labelSet (by omega) (by omega) (by omega)

private theorem mem_staggeredCombLabels_F {r : ℕ} {x : RailLabel}
    (hx : x ∈ [rho 0 0, eta 1 1, eta 1 2, rho 0 1, rho 0 2, rho 0 5]) :
    x ∈ (staggeredCombLabels r).flatten :=
  List.mem_flatten.2 ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_singleton_self _)))), hx⟩

private theorem mem_staggeredCombLabels_A {r j : ℕ} {x : RailLabel} (hj : j + 1 < r)
    (hx : x ∈ [eta (j + 1) 0, eta (j + 2) 1, eta (j + 2) 2, eta (j + 1) 3, rho (j + 1) 2,
      rho j 3]) : x ∈ (staggeredCombLabels r).flatten :=
  List.mem_flatten.2 ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _
      (List.mem_map.2 ⟨j + 1, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩)))),
    by simpa using hx⟩

private theorem mem_staggeredCombLabels_B {r j : ℕ} {x : RailLabel} (hj : j + 1 = r)
    (hx : x ∈ [eta (j + 1) 0, eta (j + 1) 3, rho (j + 1) 2, rho (j + 1) 3, eta (j + 1) 4,
      rho j 3]) : x ∈ (staggeredCombLabels r).flatten := by
  subst hj
  exact List.mem_flatten.2 ⟨_, List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_singleton_self _))), by simpa using hx⟩

private theorem mem_staggeredCombLabels_G {r : ℕ} {x : RailLabel}
    (hx : x ∈ [rho 1 0, rho 1 1, rho 1 4, rho 1 5, rho 0 4, eta 1 5]) :
    x ∈ (staggeredCombLabels r).flatten :=
  List.mem_flatten.2 ⟨_, List.mem_append_left _
    (List.mem_append_right _ (List.mem_singleton_self _)), hx⟩

private theorem mem_staggeredCombLabels_C {r j : ℕ} {x : RailLabel} (hj : j + 2 ≤ r)
    (hx : x ∈ [rho (j + 2) 0, rho (j + 2) 1, rho (j + 2) 4, rho (j + 2) 5, eta (j + 1) 4,
      eta (j + 2) 5]) : x ∈ (staggeredCombLabels r).flatten :=
  List.mem_flatten.2 ⟨_, List.mem_append_right _
    (List.mem_map.2 ⟨j + 2, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩), by simpa using hx⟩

private theorem rho_mem_flatten_staggeredCombLabels {r j k : ℕ} (hr : 1 ≤ r) (hj : j ≤ r)
    (hk : k < 6) : rho j k ∈ (staggeredCombLabels r).flatten := by
  rcases j with _ | j
  · interval_cases k
    · exact mem_staggeredCombLabels_F (by simp)
    · exact mem_staggeredCombLabels_F (by simp)
    · exact mem_staggeredCombLabels_F (by simp)
    · rcases Nat.lt_or_ge 1 r with h | h
      · exact mem_staggeredCombLabels_A (j := 0) h (by simp)
      · exact mem_staggeredCombLabels_B (j := 0) (by omega) (by simp)
    · exact mem_staggeredCombLabels_G (by simp)
    · exact mem_staggeredCombLabels_F (by simp)
  · interval_cases k
    · rcases j with _ | j
      · exact mem_staggeredCombLabels_G (by simp)
      · exact mem_staggeredCombLabels_C (j := j) (by omega) (by simp)
    · rcases j with _ | j
      · exact mem_staggeredCombLabels_G (by simp)
      · exact mem_staggeredCombLabels_C (j := j) (by omega) (by simp)
    · rcases Nat.lt_or_ge (j + 1) r with h | h
      · exact mem_staggeredCombLabels_A h (by simp)
      · exact mem_staggeredCombLabels_B (j := j) (by omega) (by simp)
    · rcases Nat.lt_or_ge (j + 2) r with h | h
      · exact mem_staggeredCombLabels_A (j := j + 1) h (by simp)
      · rcases Nat.lt_or_ge (j + 1) r with h' | h'
        · exact mem_staggeredCombLabels_B (j := j + 1) (by omega) (by simp)
        · exact mem_staggeredCombLabels_B (j := j) (by omega) (by simp)
    · rcases j with _ | j
      · exact mem_staggeredCombLabels_G (by simp)
      · exact mem_staggeredCombLabels_C (j := j) (by omega) (by simp)
    · rcases j with _ | j
      · exact mem_staggeredCombLabels_G (by simp)
      · exact mem_staggeredCombLabels_C (j := j) (by omega) (by simp)

private theorem eta_mem_flatten_staggeredCombLabels {r j k : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ r)
    (hk : k < 6) : eta j k ∈ (staggeredCombLabels r).flatten := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  interval_cases k
  · rcases Nat.lt_or_ge (j + 1) r with h | h
    · exact mem_staggeredCombLabels_A h (by simp)
    · exact mem_staggeredCombLabels_B (j := j) (by omega) (by simp)
  · rcases j with _ | j
    · exact mem_staggeredCombLabels_F (by simp)
    · exact mem_staggeredCombLabels_A (j := j) (by omega) (by simp)
  · rcases j with _ | j
    · exact mem_staggeredCombLabels_F (by simp)
    · exact mem_staggeredCombLabels_A (j := j) (by omega) (by simp)
  · rcases Nat.lt_or_ge (j + 1) r with h | h
    · exact mem_staggeredCombLabels_A h (by simp)
    · exact mem_staggeredCombLabels_B (j := j) (by omega) (by simp)
  · rcases Nat.lt_or_ge (j + 1) r with h | h
    · exact mem_staggeredCombLabels_C (j := j) (by omega) (by simp)
    · exact mem_staggeredCombLabels_B (j := j) (by omega) (by simp)
  · rcases j with _ | j
    · exact mem_staggeredCombLabels_G (by simp)
    · exact mem_staggeredCombLabels_C (j := j) (by omega) (by simp)

/-- For `r ≥ 1`, every label of `labelSet r r` is an entry of a tuple of the staggered combing. -/
theorem mem_staggeredCombLabels_of_mem_labelSet {r : ℕ} (hr : 1 ≤ r) {x : RailLabel}
    (hx : x ∈ labelSet r r) : x ∈ (staggeredCombLabels r).flatten := by
  rcases mem_labelSet.1 hx with ⟨j, hj, k, hk, rfl⟩ | ⟨j, hj1, hj, k, hk, rfl⟩
  exacts [rho_mem_flatten_staggeredCombLabels hr hj hk,
    eta_mem_flatten_staggeredCombLabels hj1 hj hk]

/-! ### Rails -/

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)

/-- The dart named by a rail label, for named darts `ρ_{j,0} = rho j` and `η_{j,0} = eta j`:
`ρ_{j,k} = σ^k(ρ_{j,0})` for `RailLabel.rho j k` and `η_{j,k} = σ^k(η_{j,0})` for
`RailLabel.eta j k`. -/
def railDart (rho eta : ℕ → H) (l : RailLabel) : H := (X.rot ^ l.2) (Sum.elim rho eta l.1)

/-- The points of a rail: pairwise distinct triple points `x₀, …, x_p` and `y₁, …, y_q`, given by
a dart `ρ_{j,0} = rho j` at `x_j` (`j ∈ [0, p]`) and a dart `η_{j,0} = eta j` at `y_j`
(`j ∈ [1, q]`). The values of `rho` and `eta` at other indices are not used. -/
structure RailPoints (p q : ℕ) where
  /-- The dart `ρ_{j,0}` at `x_j`. -/
  rho : ℕ → H
  /-- The dart `η_{j,0}` at `y_j`. -/
  eta : ℕ → H
  /-- Each point is a triple point. -/
  vertexOf_mem : ∀ a ∈ pointSet p q, X.vertexOf (Sum.elim rho eta a) ∈ X.internalVertices
  /-- The points are pairwise distinct. -/
  injOn_vertexOf : Set.InjOn (fun a => X.vertexOf (Sum.elim rho eta a)) (pointSet p q)

namespace RailPoints

variable {X} {p q : ℕ} (P : X.RailPoints p q)

/-- The dart named by a rail label. -/
def dart : RailLabel → H := X.railDart P.rho P.eta

/-- The set `D` of darts at the points of the rail. -/
def darts : Finset H := (pointSet p q).biUnion fun a => X.vertexOf (Sum.elim P.rho P.eta a)

/-- A dart lies in `D` if and only if it is a dart at one of the points of the rail. -/
theorem mem_darts {d : H} :
    d ∈ P.darts ↔ ∃ a ∈ pointSet p q, d ∈ X.vertexOf (Sum.elim P.rho P.eta a) :=
  mem_biUnion

/-- The set of darts at the points of a rail is closed under the rotation. -/
theorem rot_mem_darts_iff (d : H) : X.rot d ∈ P.darts ↔ d ∈ P.darts := by
  simp only [mem_darts, RotationSystem.mem_vertexOf, Equiv.Perm.sameCycle_apply_right]

/-- The dart named by the label `(a, k)` is a dart at the point `a`. -/
theorem dart_mem_vertexOf (l : RailLabel) : P.dart l ∈ X.vertexOf (Sum.elim P.rho P.eta l.1) :=
  X.mem_vertexOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))

/-- The dart named by a label of the rail lies in `D`. -/
theorem dart_mem_darts {l : RailLabel} (hl : l ∈ labelSet p q) : P.dart l ∈ P.darts :=
  P.mem_darts.2 ⟨l.1, (mem_product.1 hl).1, P.dart_mem_vertexOf l⟩

variable {P}

/-- In a pre-triple diagram the darts of a rail named by distinct labels are distinct. -/
theorem injOn_dart (hX : X.IsPreTripleDiagram) : Set.InjOn P.dart (labelSet p q) := by
  rintro ⟨a₁, k₁⟩ h₁ ⟨a₂, k₂⟩ h₂ h
  simp only [coe_product, Set.mem_prod, mem_coe, mem_range, labelSet] at h₁ h₂
  have hv : X.vertexOf (Sum.elim P.rho P.eta a₁) = X.vertexOf (Sum.elim P.rho P.eta a₂) := by
    rw [← X.vertexOf_eq_of_mem (P.dart_mem_vertexOf (a₁, k₁)),
      ← X.vertexOf_eq_of_mem (P.dart_mem_vertexOf (a₂, k₂)), h]
  obtain rfl := P.injOn_vertexOf h₁.1 h₂.1 hv
  obtain rfl := X.pow_apply_injective_of_card_vertexOf
    (hX.internalVertex_card _ (P.vertexOf_mem a₁ h₁.1)) h₁.2 h₂.2 h
  rfl

/-- In a pre-triple diagram every dart at a point of a rail is named by a label. -/
theorem image_dart (hX : X.IsPreTripleDiagram) : (labelSet p q).image P.dart = P.darts := by
  ext d
  rw [mem_image, mem_darts]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact P.mem_darts.1 (P.dart_mem_darts hl)
  · rintro ⟨a, ha, hd⟩
    obtain ⟨k, hk, rfl⟩ := X.exists_pow_apply_eq_of_card_vertexOf
      (hX.internalVertex_card _ (P.vertexOf_mem a ha)) hd
    exact ⟨(a, k), mem_product.2 ⟨ha, mem_range.2 hk⟩, rfl⟩

/-- If a list of labels lists every label of the rail and has `6` entries for each point, then
the darts it names are pairwise distinct. -/
theorem nodup_map_dart (hX : X.IsPreTripleDiagram) {L : List RailLabel}
    (hL : ∀ x, x ∈ L ↔ x ∈ labelSet p q) (hlen : L.length = 6 * (p + 1 + q)) :
    (L.map P.dart).Nodup := by
  have htf : L.toFinset = labelSet p q := Finset.ext fun x => by simp [hL]
  exact (nodup_of_length_le_card_toFinset (by rw [htf, card_labelSet, hlen])).map_on
    fun x hx y hy h => injOn_dart hX ((hL x).1 hx) ((hL y).1 hy) h

/-- If a list of labels lists every label of the rail, the darts it names are those of `D`. -/
theorem toFinset_map_dart (hX : X.IsPreTripleDiagram) {L : List RailLabel}
    (hL : ∀ x, x ∈ L ↔ x ∈ labelSet p q) : (L.map P.dart).toFinset = P.darts := by
  rw [← image_dart hX]
  ext d
  simp [hL]

/-- The darts named by labels of the rail lie in `D`. -/
theorem mem_darts_of_mem_map_dart {L : List RailLabel} (hL : ∀ x ∈ L, x ∈ labelSet p q) {d : H}
    (hd : d ∈ L.map P.dart) : d ∈ P.darts := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hd
  exact P.dart_mem_darts (hL l hl)

end RailPoints

/-- An **aligned rail of length `r`** of a triple diagram: pairwise distinct triple points
`x₀, …, x_r, y₁, …, y_r`, a dart `ρ_{j,0}` at each `x_j` and a dart `η_{j,0}` at each `y_j`, such
that, with `ρ_{j,k} = σ^k(ρ_{j,0})`, `η_{j,k} = σ^k(η_{j,0})` and the convention
`η_{0,3} = ρ_{0,2}`, `ρ̄_{j,3} = ρ_{j+1,0}` and `η̄_{j,3} = η_{j+1,0}` for `j ∈ [0, r - 1]`, and
`ρ̄_{j,1} = η_{j,5}` and `ρ̄_{j,2} = η_{j,4}` for `j ∈ [1, r]`. -/
@[cluster_algebras "def_aligned_rail"]
structure AlignedRail (r : ℕ) extends X.RailPoints r r where
  /-- `ρ̄_{j,3} = ρ_{j+1,0}` for `j ∈ [0, r - 1]`. -/
  inv_rho_three : ∀ j < r,
    X.inv (X.railDart rho eta (RailLabel.rho j 3)) = X.railDart rho eta (RailLabel.rho (j + 1) 0)
  /-- `η̄_{j,3} = η_{j+1,0}` for `j ∈ [0, r - 1]`, with `η_{0,3} = ρ_{0,2}`. -/
  inv_eta_three : ∀ j < r,
    X.inv (X.railDart rho eta (alignedEta j 3)) = X.railDart rho eta (RailLabel.eta (j + 1) 0)
  /-- `ρ̄_{j,1} = η_{j,5}` for `j ∈ [1, r]`. -/
  inv_rho_one : ∀ j, 1 ≤ j → j ≤ r →
    X.inv (X.railDart rho eta (RailLabel.rho j 1)) = X.railDart rho eta (RailLabel.eta j 5)
  /-- `ρ̄_{j,2} = η_{j,4}` for `j ∈ [1, r]`. -/
  inv_rho_two : ∀ j, 1 ≤ j → j ≤ r →
    X.inv (X.railDart rho eta (RailLabel.rho j 2)) = X.railDart rho eta (RailLabel.eta j 4)

/-- A **closed aligned rail of length `n ≥ 1`**: an aligned rail of length `n - 1`, a triple point
`x_n` distinct from its points and a dart `ρ_{n,0}` at `x_n` such that, with
`ρ_{n,k} = σ^k(ρ_{n,0})` and the convention `η_{0,3} = ρ_{0,2}`, `ρ̄_{n-1,3} = ρ_{n,0}` and
`η̄_{n-1,3} = ρ_{n,1}`. Its points are `x₀, …, x_n, y₁, …, y_{n-1}`. -/
@[cluster_algebras "def_closed_aligned_rail"]
structure ClosedAlignedRail (n : ℕ) extends X.AlignedRail (n - 1) where
  /-- The length is at least `1`. -/
  one_le : 1 ≤ n
  /-- `x_n` is a triple point. -/
  vertexOf_rho_mem : X.vertexOf (rho n) ∈ X.internalVertices
  /-- `x_n` is distinct from the points of the aligned rail. -/
  vertexOf_rho_ne : ∀ a ∈ pointSet (n - 1) (n - 1),
    X.vertexOf (rho n) ≠ X.vertexOf (Sum.elim rho eta a)
  /-- `ρ̄_{n-1,3} = ρ_{n,0}`. -/
  inv_rho_three_last :
    X.inv (X.railDart rho eta (RailLabel.rho (n - 1) 3)) = X.railDart rho eta (RailLabel.rho n 0)
  /-- `η̄_{n-1,3} = ρ_{n,1}`, with `η_{0,3} = ρ_{0,2}`. -/
  inv_eta_three_last :
    X.inv (X.railDart rho eta (alignedEta (n - 1) 3)) = X.railDart rho eta (RailLabel.rho n 1)

/-- A **staggered rail of length `r ≥ 1`**: pairwise distinct triple points
`x₀, …, x_r, y₁, …, y_r`, a dart `ρ_{j,0}` at each `x_j` and a dart `η_{j,0}` at each `y_j`, such
that, with `ρ_{j,k} = σ^k(ρ_{j,0})` and `η_{j,k} = σ^k(η_{j,0})`, `ρ̄_{j,3} = ρ_{j+1,0}` for
`j ∈ [0, r - 1]`, `ρ̄_{0,1} = η_{1,0}`, `η̄_{j,3} = η_{j+1,0}` for `j ∈ [1, r - 1]`, and
`ρ̄_{j-1,2} = η_{j,5}` and `ρ̄_{j,1} = η_{j,4}` for `j ∈ [1, r]`. -/
@[cluster_algebras "def_staggered_rail"]
structure StaggeredRail (r : ℕ) extends X.RailPoints r r where
  /-- The length is at least `1`. -/
  one_le : 1 ≤ r
  /-- `ρ̄_{j,3} = ρ_{j+1,0}` for `j ∈ [0, r - 1]`. -/
  inv_rho_three : ∀ j < r,
    X.inv (X.railDart rho eta (RailLabel.rho j 3)) = X.railDart rho eta (RailLabel.rho (j + 1) 0)
  /-- `ρ̄_{0,1} = η_{1,0}`. -/
  inv_rho_zero_one :
    X.inv (X.railDart rho eta (RailLabel.rho 0 1)) = X.railDart rho eta (RailLabel.eta 1 0)
  /-- `η̄_{j,3} = η_{j+1,0}` for `j ∈ [1, r - 1]`. -/
  inv_eta_three : ∀ j, 1 ≤ j → j < r →
    X.inv (X.railDart rho eta (RailLabel.eta j 3)) = X.railDart rho eta (RailLabel.eta (j + 1) 0)
  /-- `ρ̄_{j-1,2} = η_{j,5}` for `j ∈ [1, r]`. -/
  inv_rho_two : ∀ j, 1 ≤ j → j ≤ r →
    X.inv (X.railDart rho eta (RailLabel.rho (j - 1) 2)) = X.railDart rho eta (RailLabel.eta j 5)
  /-- `ρ̄_{j,1} = η_{j,4}` for `j ∈ [1, r]`. -/
  inv_rho_one : ∀ j, 1 ≤ j → j ≤ r →
    X.inv (X.railDart rho eta (RailLabel.rho j 1)) = X.railDart rho eta (RailLabel.eta j 4)

/-! ### The push-off along a closed aligned rail -/

namespace ClosedAlignedRail

variable {X} {n : ℕ} (R : X.ClosedAlignedRail n)

/-- The points `x₀, …, x_n, y₁, …, y_{n-1}` of a closed aligned rail of length `n`. -/
def railPoints : X.RailPoints n (n - 1) where
  rho := R.rho
  eta := R.eta
  vertexOf_mem a ha := by
    rcases (mem_pointSet_iff_eq_or_mem R.one_le).1 ha with rfl | ha
    · exact R.vertexOf_rho_mem
    · exact R.toRailPoints.vertexOf_mem a ha
  injOn_vertexOf a ha a' ha' h := by
    rcases (mem_pointSet_iff_eq_or_mem R.one_le).1 ha with rfl | ha <;>
      rcases (mem_pointSet_iff_eq_or_mem R.one_le).1 ha' with rfl | ha'
    · rfl
    · exact absurd h (R.vertexOf_rho_ne a' ha')
    · exact absurd h.symm (R.vertexOf_rho_ne a ha)
    · exact R.toRailPoints.injOn_vertexOf ha ha' h

/-- The `2n` tuples of darts prescribing the rotation of the push-off: the darts named by
`pushOffLabels n`. -/
def pushOffTuples : List (List H) := (pushOffLabels n).map (List.map R.railPoints.dart)

/-- The **push-off** along a closed aligned rail of length `n`: the rotation `σ'` agrees with `σ`
outside the set `D` of darts at the points of the rail, and is prescribed on `D` by the `2n` tuples
`(η_{j,5}, η_{j,2}, η_{j+1,1}, ρ_{j+1,1}, η_{j,3}, ρ_{j,3})` for `j ∈ [0, n - 2]`,
`(η_{n-1,5}, η_{n-1,2}, ρ_{n,2}, ρ_{n,3}, η_{n-1,3}, ρ_{n-1,3})`,
`(ρ_{j,2}, ρ_{j,5}, ρ_{j-1,4}, η_{j-1,4}, ρ_{j,0}, η_{j,0})` for `j ∈ [1, n - 1]`, and
`(ρ_{n,4}, ρ_{n,5}, ρ_{n-1,4}, η_{n-1,4}, ρ_{n,0}, ρ_{n,1})`, with the convention
`(η_{0,2}, η_{0,3}, η_{0,4}, η_{0,5}) = (ρ_{0,1}, ρ_{0,2}, ρ_{0,5}, ρ_{0,0})`; the rest of the data
is that of the diagram. -/
@[cluster_algebras "def_push_off"]
def pushOff : TripleData H b :=
  { X with
    rot := prescribedRot X.rot R.railPoints.darts R.railPoints.rot_mem_darts_iff R.pushOffTuples }

/-- The push-off has the involution of the diagram. -/
@[simp]
theorem pushOff_inv : R.pushOff.inv = X.inv := rfl

/-- The push-off has the boundary of the diagram. -/
@[simp]
theorem pushOff_bdry : R.pushOff.bdry = X.bdry := rfl

/-- The push-off has the endpoint darts `endDart` of the diagram. -/
@[simp]
theorem pushOff_endDart : R.pushOff.endDart = X.endDart := rfl

/-- The push-off has the orientation of the diagram. -/
@[simp]
theorem pushOff_isOut : R.pushOff.isOut = X.isOut := rfl

/-- Each tuple of darts of the push-off has `6` entries. -/
theorem length_of_mem_pushOffTuples {l : List H} (hl : l ∈ R.pushOffTuples) : l.length = 6 := by
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
  rw [List.length_map, length_of_mem_pushOffLabels hl']

private theorem mem_pushOffLabels_iff (hn : 1 ≤ n) (x : RailLabel) :
    x ∈ (pushOffLabels n).flatten ↔ x ∈ labelSet n (n - 1) :=
  ⟨mem_labelSet_of_mem_pushOffLabels, mem_pushOffLabels_of_mem_labelSet hn⟩

private theorem mem_darts_of_mem_pushOffTuples {d : H} (hd : d ∈ R.pushOffTuples.flatten) :
    d ∈ R.railPoints.darts := by
  rw [pushOffTuples, ← List.map_flatten] at hd
  exact R.railPoints.mem_darts_of_mem_map_dart (fun _ => mem_labelSet_of_mem_pushOffLabels)
    hd

/-- The entries of the `2n` tuples of the push-off are pairwise distinct. -/
@[cluster_algebras "lem_push_off_cycles"]
theorem nodup_flatten_pushOffTuples (hX : X.IsPreTripleDiagram) :
    R.pushOffTuples.flatten.Nodup := by
  rw [pushOffTuples, ← List.map_flatten]
  exact R.railPoints.nodup_map_dart hX (mem_pushOffLabels_iff R.one_le)
    (length_flatten_pushOffLabels R.one_le)

/-- The entries of the `2n` tuples of the push-off are the darts at the points of the rail. -/
@[cluster_algebras "lem_push_off_cycles"]
theorem toFinset_flatten_pushOffTuples (hX : X.IsPreTripleDiagram) :
    R.pushOffTuples.flatten.toFinset = R.railPoints.darts := by
  rw [pushOffTuples, ← List.map_flatten]
  exact R.railPoints.toFinset_map_dart hX (mem_pushOffLabels_iff R.one_le)

/-- The rotation of the push-off agrees with `σ` outside the darts at the points of the rail. -/
@[cluster_algebras "lem_push_off_cycles"]
theorem pushOff_rot_of_notMem {d : H} (hd : d ∉ R.railPoints.darts) : R.pushOff.rot d = X.rot d :=
  prescribedRot_apply_of_notMem (hD := R.railPoints.rot_mem_darts_iff)
    (fun _ => R.mem_darts_of_mem_pushOffTuples) hd

/-- The rotation of the push-off has the `2n` tuples as cycles, sending each entry to the next
one. -/
@[cluster_algebras "lem_push_off_cycles"]
theorem pushOff_rot_getElem (hX : X.IsPreTripleDiagram) {l : List H} (hl : l ∈ R.pushOffTuples)
    (i : ℕ) (hi : i < l.length) :
    R.pushOff.rot l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) :=
  prescribedRot_apply_getElem (hD := R.railPoints.rot_mem_darts_iff)
    (R.nodup_flatten_pushOffTuples hX)
    (fun _ => R.mem_darts_of_mem_pushOffTuples) hl i hi

end ClosedAlignedRail

/-! ### The aligned combing -/

namespace AlignedRail

variable {X} {r : ℕ} (R : X.AlignedRail r)

/-- The `2r + 1` tuples of darts prescribing the rotation of the aligned combing:
the darts named by `alignedCombLabels r`. -/
def alignedCombTuples : List (List H) := (alignedCombLabels r).map (List.map R.dart)

/-- The **aligned combing** of an aligned rail of length `r`: the rotation `σ'` agrees with `σ`
outside the set `D` of darts at the points of the rail, and is prescribed on `D` by the `2r + 1`
tuples `(η_{j,5}, η_{j,2}, η_{j+1,1}, ρ_{j+1,1}, η_{j,3}, ρ_{j,3})` for `j ∈ [0, r - 1]`,
`(η_{r,5}, η_{r,2}, η_{r,3}, ρ_{r,3}, ρ_{r,4}, η_{r,4})`, and
`(ρ_{j,2}, ρ_{j,5}, ρ_{j-1,4}, η_{j-1,4}, ρ_{j,0}, η_{j,0})` for `j ∈ [1, r]`, with the convention
`(η_{0,2}, η_{0,3}, η_{0,4}, η_{0,5}) = (ρ_{0,1}, ρ_{0,2}, ρ_{0,5}, ρ_{0,0})`; the rest of the data
is that of the diagram. -/
@[cluster_algebras "def_comb_aligned"]
def alignedComb : TripleData H b :=
  { X with rot := prescribedRot X.rot R.darts R.rot_mem_darts_iff R.alignedCombTuples }

/-- The aligned combing has the involution of the diagram. -/
@[simp]
theorem alignedComb_inv : R.alignedComb.inv = X.inv := rfl

/-- The aligned combing has the boundary of the diagram. -/
@[simp]
theorem alignedComb_bdry : R.alignedComb.bdry = X.bdry := rfl

/-- The aligned combing has the endpoint darts `endDart` of the diagram. -/
@[simp]
theorem alignedComb_endDart : R.alignedComb.endDart = X.endDart := rfl

/-- The aligned combing has the orientation of the diagram. -/
@[simp]
theorem alignedComb_isOut : R.alignedComb.isOut = X.isOut := rfl

/-- Each tuple of darts of the aligned combing has `6` entries. -/
theorem length_of_mem_alignedCombTuples {l : List H} (hl : l ∈ R.alignedCombTuples) :
    l.length = 6 := by
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
  rw [List.length_map, length_of_mem_alignedCombLabels hl']

private theorem mem_alignedCombLabels_iff (x : RailLabel) :
    x ∈ (alignedCombLabels r).flatten ↔ x ∈ labelSet r r :=
  ⟨mem_labelSet_of_mem_alignedCombLabels, mem_alignedCombLabels_of_mem_labelSet⟩

private theorem mem_darts_of_mem_alignedCombTuples {d : H}
    (hd : d ∈ R.alignedCombTuples.flatten) : d ∈ R.darts := by
  rw [alignedCombTuples, ← List.map_flatten] at hd
  exact R.mem_darts_of_mem_map_dart (fun _ => mem_labelSet_of_mem_alignedCombLabels) hd

/-- The entries of the `2r + 1` tuples of the aligned combing are pairwise distinct. -/
@[cluster_algebras "lem_comb_aligned_cycles"]
theorem nodup_flatten_alignedCombTuples (hX : X.IsPreTripleDiagram) :
    R.alignedCombTuples.flatten.Nodup := by
  rw [alignedCombTuples, ← List.map_flatten]
  exact RailPoints.nodup_map_dart hX mem_alignedCombLabels_iff
    (length_flatten_alignedCombLabels r)

/-- The entries of the `2r + 1` tuples of the aligned combing are the darts at the points of the
rail. -/
@[cluster_algebras "lem_comb_aligned_cycles"]
theorem toFinset_flatten_alignedCombTuples (hX : X.IsPreTripleDiagram) :
    R.alignedCombTuples.flatten.toFinset = R.darts := by
  rw [alignedCombTuples, ← List.map_flatten]
  exact RailPoints.toFinset_map_dart hX mem_alignedCombLabels_iff

/-- The rotation of the aligned combing agrees with `σ` outside the darts at the points of the
rail. -/
@[cluster_algebras "lem_comb_aligned_cycles"]
theorem alignedComb_rot_of_notMem {d : H} (hd : d ∉ R.darts) : R.alignedComb.rot d = X.rot d :=
  prescribedRot_apply_of_notMem (hD := R.rot_mem_darts_iff)
    (fun _ => R.mem_darts_of_mem_alignedCombTuples) hd

/-- The rotation of the aligned combing has the `2r + 1` tuples as cycles, sending each entry to
the next one. -/
@[cluster_algebras "lem_comb_aligned_cycles"]
theorem alignedComb_rot_getElem (hX : X.IsPreTripleDiagram) {l : List H}
    (hl : l ∈ R.alignedCombTuples) (i : ℕ) (hi : i < l.length) :
    R.alignedComb.rot l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) :=
  prescribedRot_apply_getElem (hD := R.rot_mem_darts_iff) (R.nodup_flatten_alignedCombTuples hX)
    (fun _ => R.mem_darts_of_mem_alignedCombTuples) hl i hi

end AlignedRail

/-! ### The staggered combing -/

namespace StaggeredRail

variable {X} {r : ℕ} (R : X.StaggeredRail r)

/-- The `2r + 1` tuples of darts prescribing the rotation of the staggered combing:
the darts named by `staggeredCombLabels r`. -/
def staggeredCombTuples : List (List H) := (staggeredCombLabels r).map (List.map R.dart)

/-- The **staggered combing** of a staggered rail of length `r`: the rotation
`σ'` agrees with `σ` outside the set `D` of darts at the points of the rail, and is
prescribed on `D` by the `2r + 1` tuples `(ρ_{0,0}, η_{1,1}, η_{1,2}, ρ_{0,1}, ρ_{0,2}, ρ_{0,5})`,
`(η_{j,0}, η_{j+1,1}, η_{j+1,2}, η_{j,3}, ρ_{j,2}, ρ_{j-1,3})` for `j ∈ [1, r - 1]`,
`(η_{r,0}, η_{r,3}, ρ_{r,2}, ρ_{r,3}, η_{r,4}, ρ_{r-1,3})`,
`(ρ_{1,0}, ρ_{1,1}, ρ_{1,4}, ρ_{1,5}, ρ_{0,4}, η_{1,5})` and
`(ρ_{j,0}, ρ_{j,1}, ρ_{j,4}, ρ_{j,5}, η_{j-1,4}, η_{j,5})` for `j ∈ [2, r]`; the rest of the data
is that of the diagram. -/
@[cluster_algebras "def_comb_staggered"]
def staggeredComb : TripleData H b :=
  { X with rot := prescribedRot X.rot R.darts R.rot_mem_darts_iff R.staggeredCombTuples }

/-- The staggered combing has the involution of the diagram. -/
@[simp]
theorem staggeredComb_inv : R.staggeredComb.inv = X.inv := rfl

/-- The staggered combing has the boundary of the diagram. -/
@[simp]
theorem staggeredComb_bdry : R.staggeredComb.bdry = X.bdry := rfl

/-- The staggered combing has the endpoint darts `endDart` of the diagram. -/
@[simp]
theorem staggeredComb_endDart : R.staggeredComb.endDart = X.endDart := rfl

/-- The staggered combing has the orientation of the diagram. -/
@[simp]
theorem staggeredComb_isOut : R.staggeredComb.isOut = X.isOut := rfl

/-- Each tuple of darts of the staggered combing has `6` entries. -/
theorem length_of_mem_staggeredCombTuples {l : List H} (hl : l ∈ R.staggeredCombTuples) :
    l.length = 6 := by
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
  rw [List.length_map, length_of_mem_staggeredCombLabels hl']

private theorem mem_staggeredCombLabels_iff (hr : 1 ≤ r) (x : RailLabel) :
    x ∈ (staggeredCombLabels r).flatten ↔ x ∈ labelSet r r :=
  ⟨mem_labelSet_of_mem_staggeredCombLabels hr, mem_staggeredCombLabels_of_mem_labelSet hr⟩

private theorem mem_darts_of_mem_staggeredCombTuples {d : H}
    (hd : d ∈ R.staggeredCombTuples.flatten) : d ∈ R.darts := by
  rw [staggeredCombTuples, ← List.map_flatten] at hd
  exact R.mem_darts_of_mem_map_dart
    (fun _ => mem_labelSet_of_mem_staggeredCombLabels R.one_le) hd

/-- The entries of the `2r + 1` tuples of the staggered combing are pairwise distinct. -/
@[cluster_algebras "lem_comb_staggered_cycles"]
theorem nodup_flatten_staggeredCombTuples (hX : X.IsPreTripleDiagram) :
    R.staggeredCombTuples.flatten.Nodup := by
  rw [staggeredCombTuples, ← List.map_flatten]
  exact RailPoints.nodup_map_dart hX (mem_staggeredCombLabels_iff R.one_le)
    (length_flatten_staggeredCombLabels R.one_le)

/-- The entries of the `2r + 1` tuples of the staggered combing are the darts at the points of the
rail. -/
@[cluster_algebras "lem_comb_staggered_cycles"]
theorem toFinset_flatten_staggeredCombTuples (hX : X.IsPreTripleDiagram) :
    R.staggeredCombTuples.flatten.toFinset = R.darts := by
  rw [staggeredCombTuples, ← List.map_flatten]
  exact RailPoints.toFinset_map_dart hX (mem_staggeredCombLabels_iff R.one_le)

/-- The rotation of the staggered combing agrees with `σ` outside the darts at the points of the
rail. -/
@[cluster_algebras "lem_comb_staggered_cycles"]
theorem staggeredComb_rot_of_notMem {d : H} (hd : d ∉ R.darts) :
    R.staggeredComb.rot d = X.rot d :=
  prescribedRot_apply_of_notMem (hD := R.rot_mem_darts_iff)
    (fun _ => R.mem_darts_of_mem_staggeredCombTuples) hd

/-- The rotation of the staggered combing has the `2r + 1` tuples as cycles, sending each entry to
the next one. -/
@[cluster_algebras "lem_comb_staggered_cycles"]
theorem staggeredComb_rot_getElem (hX : X.IsPreTripleDiagram) {l : List H}
    (hl : l ∈ R.staggeredCombTuples) (i : ℕ) (hi : i < l.length) :
    R.staggeredComb.rot l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) :=
  prescribedRot_apply_getElem (hD := R.rot_mem_darts_iff)
    (R.nodup_flatten_staggeredCombTuples hX)
    (fun _ => R.mem_darts_of_mem_staggeredCombTuples) hl i hi

end StaggeredRail

/-! ### Examples

The smallest instances of the three constructions, checked by `decide`. Each rail is the whole
diagram: its points are the triple points, the darts `6p, …, 6p + 5` of the `p`-th triple point
(the points `x₀, x₁, …` and then `y₁, y₂, …`) are listed counterclockwise, and every dart not
joined to another point runs to an endpoint. For length `1` the examples check the darts of the
rail, the tuples, that the new rotation agrees with `σ` outside the rail and has the tuples as
cycles, that the new diagram satisfies Euler's relation, and that the strand permutation is
unchanged; for length `2` they check the darts and the cycles.
-/

namespace RailExamples

/-- The function `Fin N → Fin N` reading its values off a list. -/
private def listFun (N : ℕ) [NeZero N] (l : List ℕ) (i : Fin N) : Fin N :=
  Fin.ofNat N (l.getD i.val 0)

/-- The permutation of `Fin N` reading its values and those of its inverse off two lists. -/
private def listPerm (N : ℕ) [NeZero N] (l l' : List ℕ)
    (h₁ : ∀ i, listFun N l' (listFun N l i) = i) (h₂ : ∀ i, listFun N l (listFun N l' i) = i) :
    Equiv.Perm (Fin N) :=
  ⟨listFun N l, listFun N l', h₁, h₂⟩

/-- The data of a triple diagram with 4 arcs whose triple points are the points of the rail
`closedOneRail`. -/
private def closedOneDiagram : TripleData (Fin 36) 4 where
  inv := listPerm 36
    [30, 27, 7, 6, 12, 33, 3, 2, 24, 21, 18, 15, 4, 35, 16, 11, 14, 19, 10, 17, 22, 9, 20, 25, 8,
      23, 28, 1, 26, 31, 0, 29, 34, 5, 32, 13]
    [30, 27, 7, 6, 12, 33, 3, 2, 24, 21, 18, 15, 4, 35, 16, 11, 14, 19, 10, 17, 22, 9, 20, 25, 8,
      23, 28, 1, 26, 31, 0, 29, 34, 5, 32, 13]
    (by decide) (by decide)
  rot := listPerm 36
    [1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 6, 14, 12, 13, 17, 15, 16, 20, 18, 19, 23, 21, 22, 26,
      24, 25, 29, 27, 28, 32, 30, 31, 35, 33, 34]
    [5, 0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10, 13, 14, 12, 16, 17, 15, 19, 20, 18, 22, 23, 21, 25,
      26, 24, 28, 29, 27, 31, 32, 30, 34, 35, 33]
    (by decide) (by decide)
  bdry := univ.filter fun d => 12 ≤ d.val ∧ d.val % 3 ≠ 0
  endDart r := Fin.ofNat 36 (12 + 3 * r.val)
  isOut d :=
    [false, true, false, true, false, true, false, true, false, true, false, true, true, false,
      false, false, false, false, true, false, false, false, false, false, true, false, false,
      false, false, false, true, false, false, false, false, false].getD d.val false

/-- A closed aligned rail of length 1: `ρ_{j,0}` is the dart `6j` and `η_{j,0}` the
dart `6(1 + j)`. -/
private def closedOneRail : closedOneDiagram.ClosedAlignedRail 1 where
  rho j := Fin.ofNat 36 (6 * j)
  eta j := Fin.ofNat 36 (6 * (1 + j))
  vertexOf_mem := by simp only [DiskMap.vertexOf_mem_internalVertices]; decide
  injOn_vertexOf := by simp only [Set.InjOn, mem_coe]; decide
  inv_rho_three := by decide +kernel
  inv_eta_three := by decide +kernel
  inv_rho_one := fun j h₁ h₂ => by omega
  inv_rho_two := fun j h₁ h₂ => by omega
  one_le := by decide +kernel
  vertexOf_rho_mem := by rw [DiskMap.vertexOf_mem_internalVertices]; decide
  vertexOf_rho_ne := by decide +kernel
  inv_rho_three_last := by decide +kernel
  inv_eta_three_last := by decide +kernel

-- The darts at the points of the rail.
example : closedOneRail.railPoints.darts.card = 12 := by decide +kernel
-- The tuples prescribing the new rotation, as darts.
example : closedOneRail.pushOffTuples =
    [[0, 1, 8, 9, 2, 3], [10, 11, 4, 5, 6, 7]] := by
  decide +kernel
-- The new rotation agrees with `σ` outside the rail and has the tuples as cycles on it.
example : ∀ d, d ∉ closedOneRail.railPoints.darts →
    closedOneRail.pushOff.rot d = closedOneDiagram.rot d := by
  decide +kernel
example : ∀ l ∈ closedOneRail.pushOffTuples, ∀ i (hi : i < l.length),
    closedOneRail.pushOff.rot l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
  decide +kernel
-- The numbers of vertices, edges and faces of the new diagram. Each is its own kernel
-- evaluation, so that the kernel's caches are dropped between them.
private theorem closedOne_card_vertices : closedOneRail.pushOff.vertices.card = 10 := by
  decide +kernel
private theorem closedOne_card_edges : closedOneRail.pushOff.edges.card = 18 := by
  decide +kernel
private theorem closedOne_card_faceOrbits : closedOneRail.pushOff.faceOrbits.card = 10 := by
  decide +kernel
-- The new diagram satisfies Euler's relation.
example :
    (closedOneRail.pushOff.vertices.card : ℤ) - closedOneRail.pushOff.edges.card +
      closedOneRail.pushOff.faceOrbits.card = 2 := by
  rw [closedOne_card_vertices, closedOne_card_edges, closedOne_card_faceOrbits]
  norm_num
-- The strand permutation, `i ↦ π(i)` (`0`-indexed), is unchanged.
example : ∀ i, closedOneDiagram.strandPerm i = [2, 3, 0, 1].getD i.val 0 := by
  decide +kernel
example : closedOneRail.pushOff.strandPerm = closedOneDiagram.strandPerm := by
  decide +kernel

/-- The data of a triple diagram with 5 arcs whose triple points are the points of the rail
`alignedOneRail`. -/
private def alignedOneDiagram : TripleData (Fin 48) 5 where
  inv := listPerm 48
    [42, 39, 12, 6, 18, 45, 3, 17, 16, 27, 24, 21, 2, 36, 33, 30, 8, 7, 4, 47, 22, 11, 20, 25,
      10, 23, 28, 9, 26, 31, 15, 29, 34, 14, 32, 37, 13, 35, 40, 1, 38, 43, 0, 41, 46, 5, 44, 19]
    [42, 39, 12, 6, 18, 45, 3, 17, 16, 27, 24, 21, 2, 36, 33, 30, 8, 7, 4, 47, 22, 11, 20, 25,
      10, 23, 28, 9, 26, 31, 15, 29, 34, 14, 32, 37, 13, 35, 40, 1, 38, 43, 0, 41, 46, 5, 44, 19]
    (by decide) (by decide)
  rot := listPerm 48
    [1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 6, 13, 14, 15, 16, 17, 12, 20, 18, 19, 23, 21, 22, 26,
      24, 25, 29, 27, 28, 32, 30, 31, 35, 33, 34, 38, 36, 37, 41, 39, 40, 44, 42, 43, 47, 45, 46]
    [5, 0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10, 17, 12, 13, 14, 15, 16, 19, 20, 18, 22, 23, 21, 25,
      26, 24, 28, 29, 27, 31, 32, 30, 34, 35, 33, 37, 38, 36, 40, 41, 39, 43, 44, 42, 46, 47, 45]
    (by decide) (by decide)
  bdry := univ.filter fun d => 18 ≤ d.val ∧ d.val % 3 ≠ 0
  endDart r := Fin.ofNat 48 (18 + 3 * r.val)
  isOut d :=
    [false, true, false, true, false, true, false, true, false, true, false, true, true, false,
      true, false, true, false, true, false, false, false, false, false, true, false, false,
      false, false, false, true, false, false, false, false, false, true, false, false, false,
      false, false, true, false, false, false, false, false].getD d.val false

/-- A aligned rail of length 1: `ρ_{j,0}` is the dart `6j` and `η_{j,0}` the
dart `6(1 + j)`. -/
private def alignedOneRail : alignedOneDiagram.AlignedRail 1 where
  rho j := Fin.ofNat 48 (6 * j)
  eta j := Fin.ofNat 48 (6 * (1 + j))
  vertexOf_mem := by simp only [DiskMap.vertexOf_mem_internalVertices]; decide
  injOn_vertexOf := by simp only [Set.InjOn, mem_coe]; decide
  inv_rho_three := by decide +kernel
  inv_eta_three := by decide +kernel
  inv_rho_one := fun j h₁ h₂ => by interval_cases j; decide
  inv_rho_two := fun j h₁ h₂ => by interval_cases j; decide

-- The darts at the points of the rail.
example : alignedOneRail.darts.card = 18 := by decide +kernel
-- The tuples prescribing the new rotation, as darts.
example : alignedOneRail.alignedCombTuples =
    [[0, 1, 13, 7, 2, 3], [17, 14, 15, 9, 10, 16], [8, 11, 4, 5, 6, 12]] := by
  decide +kernel
-- The new rotation agrees with `σ` outside the rail and has the tuples as cycles on it.
example : ∀ d, d ∉ alignedOneRail.darts →
    alignedOneRail.alignedComb.rot d = alignedOneDiagram.rot d := by
  decide +kernel
example : ∀ l ∈ alignedOneRail.alignedCombTuples, ∀ i (hi : i < l.length),
    alignedOneRail.alignedComb.rot l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
  decide +kernel
-- The numbers of vertices, edges and faces of the new diagram. Each is its own kernel
-- evaluation, so that the kernel's caches are dropped between them.
private theorem alignedOne_card_vertices : alignedOneRail.alignedComb.vertices.card = 13 := by
  decide +kernel
private theorem alignedOne_card_edges : alignedOneRail.alignedComb.edges.card = 24 := by
  decide +kernel
private theorem alignedOne_card_faceOrbits : alignedOneRail.alignedComb.faceOrbits.card = 13 := by
  decide +kernel
-- The new diagram satisfies Euler's relation.
example :
    (alignedOneRail.alignedComb.vertices.card : ℤ) - alignedOneRail.alignedComb.edges.card +
      alignedOneRail.alignedComb.faceOrbits.card = 2 := by
  rw [alignedOne_card_vertices, alignedOne_card_edges, alignedOne_card_faceOrbits]
  norm_num
-- The strand permutation, `i ↦ π(i)` (`0`-indexed), is unchanged.
example : ∀ i, alignedOneDiagram.strandPerm i = [3, 2, 4, 0, 1].getD i.val 0 := by
  decide +kernel
example : alignedOneRail.alignedComb.strandPerm = alignedOneDiagram.strandPerm := by
  decide +kernel

/-- The data of a triple diagram with 5 arcs whose triple points are the points of the rail
`staggeredOneRail`. -/
private def staggeredOneDiagram : TripleData (Fin 48) 5 where
  inv := listPerm 48
    [42, 12, 17, 6, 18, 45, 3, 16, 30, 27, 24, 21, 1, 39, 36, 33, 7, 2, 4, 47, 22, 11, 20, 25,
      10, 23, 28, 9, 26, 31, 8, 29, 34, 15, 32, 37, 14, 35, 40, 13, 38, 43, 0, 41, 46, 5, 44, 19]
    [42, 12, 17, 6, 18, 45, 3, 16, 30, 27, 24, 21, 1, 39, 36, 33, 7, 2, 4, 47, 22, 11, 20, 25,
      10, 23, 28, 9, 26, 31, 8, 29, 34, 15, 32, 37, 14, 35, 40, 13, 38, 43, 0, 41, 46, 5, 44, 19]
    (by decide) (by decide)
  rot := listPerm 48
    [1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 6, 13, 14, 15, 16, 17, 12, 20, 18, 19, 23, 21, 22, 26,
      24, 25, 29, 27, 28, 32, 30, 31, 35, 33, 34, 38, 36, 37, 41, 39, 40, 44, 42, 43, 47, 45, 46]
    [5, 0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10, 17, 12, 13, 14, 15, 16, 19, 20, 18, 22, 23, 21, 25,
      26, 24, 28, 29, 27, 31, 32, 30, 34, 35, 33, 37, 38, 36, 40, 41, 39, 43, 44, 42, 46, 47, 45]
    (by decide) (by decide)
  bdry := univ.filter fun d => 18 ≤ d.val ∧ d.val % 3 ≠ 0
  endDart r := Fin.ofNat 48 (18 + 3 * r.val)
  isOut d :=
    [false, true, false, true, false, true, false, true, false, true, false, true, false, true,
      false, true, false, true, true, false, false, false, false, false, true, false, false,
      false, false, false, true, false, false, false, false, false, true, false, false, false,
      false, false, true, false, false, false, false, false].getD d.val false

/-- A staggered rail of length 1: `ρ_{j,0}` is the dart `6j` and `η_{j,0}` the
dart `6(1 + j)`. -/
private def staggeredOneRail : staggeredOneDiagram.StaggeredRail 1 where
  rho j := Fin.ofNat 48 (6 * j)
  eta j := Fin.ofNat 48 (6 * (1 + j))
  vertexOf_mem := by simp only [DiskMap.vertexOf_mem_internalVertices]; decide
  injOn_vertexOf := by simp only [Set.InjOn, mem_coe]; decide
  one_le := by decide +kernel
  inv_rho_three := by decide +kernel
  inv_rho_zero_one := by decide +kernel
  inv_eta_three := fun j h₁ h₂ => by omega
  inv_rho_two := fun j h₁ h₂ => by interval_cases j; decide
  inv_rho_one := fun j h₁ h₂ => by interval_cases j; decide

-- The darts at the points of the rail.
example : staggeredOneRail.darts.card = 18 := by decide +kernel
-- The tuples prescribing the new rotation, as darts.
example : staggeredOneRail.staggeredCombTuples =
    [[0, 13, 14, 1, 2, 5], [12, 15, 8, 9, 16, 3], [6, 7, 10, 11, 4, 17]] := by
  decide +kernel
-- The new rotation agrees with `σ` outside the rail and has the tuples as cycles on it.
example : ∀ d, d ∉ staggeredOneRail.darts →
    staggeredOneRail.staggeredComb.rot d = staggeredOneDiagram.rot d := by
  decide +kernel
example : ∀ l ∈ staggeredOneRail.staggeredCombTuples, ∀ i (hi : i < l.length),
    staggeredOneRail.staggeredComb.rot l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
  decide +kernel
-- The numbers of vertices, edges and faces of the new diagram. Each is its own kernel
-- evaluation, so that the kernel's caches are dropped between them.
private theorem staggeredOne_card_vertices : staggeredOneRail.staggeredComb.vertices.card = 13 := by
  decide +kernel
private theorem staggeredOne_card_edges : staggeredOneRail.staggeredComb.edges.card = 24 := by
  decide +kernel
private theorem staggeredOne_card_faceOrbits :
    staggeredOneRail.staggeredComb.faceOrbits.card = 13 := by
  decide +kernel
-- The new diagram satisfies Euler's relation.
example :
    (staggeredOneRail.staggeredComb.vertices.card : ℤ) - staggeredOneRail.staggeredComb.edges.card +
      staggeredOneRail.staggeredComb.faceOrbits.card = 2 := by
  rw [staggeredOne_card_vertices, staggeredOne_card_edges, staggeredOne_card_faceOrbits]
  norm_num
-- The strand permutation, `i ↦ π(i)` (`0`-indexed), is unchanged.
example : ∀ i, staggeredOneDiagram.strandPerm i = [2, 3, 0, 4, 1].getD i.val 0 := by
  decide +kernel
example : staggeredOneRail.staggeredComb.strandPerm = staggeredOneDiagram.strandPerm := by
  decide +kernel

/-- The data of a triple diagram with 6 arcs whose triple points are the points of the rail
`closedTwoRail`. -/
private def closedTwoDiagram : TripleData (Fin 60) 6 where
  inv := listPerm 60
    [54, 51, 18, 6, 24, 57, 3, 23, 22, 12, 30, 27, 9, 21, 42, 39, 36, 33, 2, 48, 45, 13, 8, 7, 4,
      59, 28, 11, 26, 31, 10, 29, 34, 17, 32, 37, 16, 35, 40, 15, 38, 43, 14, 41, 46, 20, 44, 49,
      19, 47, 52, 1, 50, 55, 0, 53, 58, 5, 56, 25]
    [54, 51, 18, 6, 24, 57, 3, 23, 22, 12, 30, 27, 9, 21, 42, 39, 36, 33, 2, 48, 45, 13, 8, 7, 4,
      59, 28, 11, 26, 31, 10, 29, 34, 17, 32, 37, 16, 35, 40, 15, 38, 43, 14, 41, 46, 20, 44, 49,
      19, 47, 52, 1, 50, 55, 0, 53, 58, 5, 56, 25]
    (by decide) (by decide)
  rot := listPerm 60
    [1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 6, 13, 14, 15, 16, 17, 12, 19, 20, 21, 22, 23, 18, 26,
      24, 25, 29, 27, 28, 32, 30, 31, 35, 33, 34, 38, 36, 37, 41, 39, 40, 44, 42, 43, 47, 45, 46,
      50, 48, 49, 53, 51, 52, 56, 54, 55, 59, 57, 58]
    [5, 0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10, 17, 12, 13, 14, 15, 16, 23, 18, 19, 20, 21, 22, 25,
      26, 24, 28, 29, 27, 31, 32, 30, 34, 35, 33, 37, 38, 36, 40, 41, 39, 43, 44, 42, 46, 47, 45,
      49, 50, 48, 52, 53, 51, 55, 56, 54, 58, 59, 57]
    (by decide) (by decide)
  bdry := univ.filter fun d => 24 ≤ d.val ∧ d.val % 3 ≠ 0
  endDart r := Fin.ofNat 60 (24 + 3 * r.val)
  isOut d :=
    [false, true, false, true, false, true, false, true, false, true, false, true, false, true,
      false, true, false, true, true, false, true, false, true, false, true, false, false, false,
      false, false, true, false, false, false, false, false, true, false, false, false, false,
      false, true, false, false, false, false, false, true, false, false, false, false, false,
      true, false, false, false, false, false].getD d.val false

/-- A closed aligned rail of length 2: `ρ_{j,0}` is the dart `6j` and `η_{j,0}` the
dart `6(2 + j)`. -/
private def closedTwoRail : closedTwoDiagram.ClosedAlignedRail 2 where
  rho j := Fin.ofNat 60 (6 * j)
  eta j := Fin.ofNat 60 (6 * (2 + j))
  vertexOf_mem := by simp only [DiskMap.vertexOf_mem_internalVertices]; decide
  injOn_vertexOf := by simp only [Set.InjOn, mem_coe]; decide
  inv_rho_three := by decide +kernel
  inv_eta_three := by decide +kernel
  inv_rho_one := fun j h₁ h₂ => by interval_cases j; decide
  inv_rho_two := fun j h₁ h₂ => by interval_cases j; decide
  one_le := by decide +kernel
  vertexOf_rho_mem := by rw [DiskMap.vertexOf_mem_internalVertices]; decide
  vertexOf_rho_ne := by decide +kernel
  inv_rho_three_last := by decide +kernel
  inv_eta_three_last := by decide +kernel

-- The darts at the points of the rail.
example : closedTwoRail.railPoints.darts.card = 24 := by decide +kernel
-- The tuples prescribing the new rotation, as darts.
example : closedTwoRail.pushOffTuples =
    [[0, 1, 19, 7, 2, 3], [23, 20, 14, 15, 21, 9], [8, 11, 4, 5, 6, 18], [16, 17, 10, 22, 12,
      13]] := by
  decide +kernel
-- The new rotation has the tuples as cycles.
example : ∀ l ∈ closedTwoRail.pushOffTuples, ∀ i (hi : i < l.length),
    closedTwoRail.pushOff.rot l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
  decide +kernel

/-- The data of a triple diagram with 7 arcs whose triple points are the points of the rail
`alignedTwoRail`. -/
private def alignedTwoDiagram : TripleData (Fin 72) 7 where
  inv := listPerm 72
    [66, 63, 18, 6, 30, 69, 3, 23, 22, 12, 36, 33, 9, 29, 28, 45, 42, 39, 2, 60, 57, 24, 8, 7,
      21, 54, 51, 48, 14, 13, 4, 71, 34, 11, 32, 37, 10, 35, 40, 17, 38, 43, 16, 41, 46, 15, 44,
      49, 27, 47, 52, 26, 50, 55, 25, 53, 58, 20, 56, 61, 19, 59, 64, 1, 62, 67, 0, 65, 70, 5,
      68, 31]
    [66, 63, 18, 6, 30, 69, 3, 23, 22, 12, 36, 33, 9, 29, 28, 45, 42, 39, 2, 60, 57, 24, 8, 7,
      21, 54, 51, 48, 14, 13, 4, 71, 34, 11, 32, 37, 10, 35, 40, 17, 38, 43, 16, 41, 46, 15, 44,
      49, 27, 47, 52, 26, 50, 55, 25, 53, 58, 20, 56, 61, 19, 59, 64, 1, 62, 67, 0, 65, 70, 5,
      68, 31]
    (by decide) (by decide)
  rot := listPerm 72
    [1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 6, 13, 14, 15, 16, 17, 12, 19, 20, 21, 22, 23, 18, 25,
      26, 27, 28, 29, 24, 32, 30, 31, 35, 33, 34, 38, 36, 37, 41, 39, 40, 44, 42, 43, 47, 45, 46,
      50, 48, 49, 53, 51, 52, 56, 54, 55, 59, 57, 58, 62, 60, 61, 65, 63, 64, 68, 66, 67, 71, 69,
      70]
    [5, 0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10, 17, 12, 13, 14, 15, 16, 23, 18, 19, 20, 21, 22, 29,
      24, 25, 26, 27, 28, 31, 32, 30, 34, 35, 33, 37, 38, 36, 40, 41, 39, 43, 44, 42, 46, 47, 45,
      49, 50, 48, 52, 53, 51, 55, 56, 54, 58, 59, 57, 61, 62, 60, 64, 65, 63, 67, 68, 66, 70, 71,
      69]
    (by decide) (by decide)
  bdry := univ.filter fun d => 30 ≤ d.val ∧ d.val % 3 ≠ 0
  endDart r := Fin.ofNat 72 (30 + 3 * r.val)
  isOut d :=
    [false, true, false, true, false, true, false, true, false, true, false, true, false, true,
      false, true, false, true, true, false, true, false, true, false, true, false, true, false,
      true, false, true, false, false, false, false, false, true, false, false, false, false,
      false, true, false, false, false, false, false, true, false, false, false, false, false,
      true, false, false, false, false, false, true, false, false, false, false, false, true,
      false, false, false, false, false].getD d.val false

/-- A aligned rail of length 2: `ρ_{j,0}` is the dart `6j` and `η_{j,0}` the
dart `6(2 + j)`. -/
private def alignedTwoRail : alignedTwoDiagram.AlignedRail 2 where
  rho j := Fin.ofNat 72 (6 * j)
  eta j := Fin.ofNat 72 (6 * (2 + j))
  vertexOf_mem := by simp only [DiskMap.vertexOf_mem_internalVertices]; decide
  injOn_vertexOf := by simp only [Set.InjOn, mem_coe]; decide
  inv_rho_three := by decide +kernel
  inv_eta_three := by decide +kernel
  inv_rho_one := fun j h₁ h₂ => by interval_cases j <;> decide
  inv_rho_two := fun j h₁ h₂ => by interval_cases j <;> decide

-- The darts at the points of the rail.
example : alignedTwoRail.darts.card = 30 := by decide +kernel
-- The tuples prescribing the new rotation, as darts.
example : alignedTwoRail.alignedCombTuples =
    [[0, 1, 19, 7, 2, 3], [23, 20, 25, 13, 21, 9], [29, 26, 27, 15, 16, 28], [8, 11, 4, 5, 6,
      18], [14, 17, 10, 22, 12, 24]] := by
  decide +kernel
-- The new rotation has the tuples as cycles.
example : ∀ l ∈ alignedTwoRail.alignedCombTuples, ∀ i (hi : i < l.length),
    alignedTwoRail.alignedComb.rot l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
  decide +kernel

/-- The data of a triple diagram with 7 arcs whose triple points are the points of the rail
`staggeredTwoRail`. -/
private def staggeredTwoDiagram : TripleData (Fin 72) 7 where
  inv := listPerm 72
    [66, 18, 23, 6, 30, 69, 3, 22, 29, 12, 36, 33, 9, 28, 48, 45, 42, 39, 1, 63, 60, 24, 7, 2,
      21, 57, 54, 51, 13, 8, 4, 71, 34, 11, 32, 37, 10, 35, 40, 17, 38, 43, 16, 41, 46, 15, 44,
      49, 14, 47, 52, 27, 50, 55, 26, 53, 58, 25, 56, 61, 20, 59, 64, 19, 62, 67, 0, 65, 70, 5,
      68, 31]
    [66, 18, 23, 6, 30, 69, 3, 22, 29, 12, 36, 33, 9, 28, 48, 45, 42, 39, 1, 63, 60, 24, 7, 2,
      21, 57, 54, 51, 13, 8, 4, 71, 34, 11, 32, 37, 10, 35, 40, 17, 38, 43, 16, 41, 46, 15, 44,
      49, 14, 47, 52, 27, 50, 55, 26, 53, 58, 25, 56, 61, 20, 59, 64, 19, 62, 67, 0, 65, 70, 5,
      68, 31]
    (by decide) (by decide)
  rot := listPerm 72
    [1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 6, 13, 14, 15, 16, 17, 12, 19, 20, 21, 22, 23, 18, 25,
      26, 27, 28, 29, 24, 32, 30, 31, 35, 33, 34, 38, 36, 37, 41, 39, 40, 44, 42, 43, 47, 45, 46,
      50, 48, 49, 53, 51, 52, 56, 54, 55, 59, 57, 58, 62, 60, 61, 65, 63, 64, 68, 66, 67, 71, 69,
      70]
    [5, 0, 1, 2, 3, 4, 11, 6, 7, 8, 9, 10, 17, 12, 13, 14, 15, 16, 23, 18, 19, 20, 21, 22, 29,
      24, 25, 26, 27, 28, 31, 32, 30, 34, 35, 33, 37, 38, 36, 40, 41, 39, 43, 44, 42, 46, 47, 45,
      49, 50, 48, 52, 53, 51, 55, 56, 54, 58, 59, 57, 61, 62, 60, 64, 65, 63, 67, 68, 66, 70, 71,
      69]
    (by decide) (by decide)
  bdry := univ.filter fun d => 30 ≤ d.val ∧ d.val % 3 ≠ 0
  endDart r := Fin.ofNat 72 (30 + 3 * r.val)
  isOut d :=
    [false, true, false, true, false, true, false, true, false, true, false, true, false, true,
      false, true, false, true, false, true, false, true, false, true, false, true, false, true,
      false, true, true, false, false, false, false, false, true, false, false, false, false,
      false, true, false, false, false, false, false, true, false, false, false, false, false,
      true, false, false, false, false, false, true, false, false, false, false, false, true,
      false, false, false, false, false].getD d.val false

/-- A staggered rail of length 2: `ρ_{j,0}` is the dart `6j` and `η_{j,0}` the
dart `6(2 + j)`. -/
private def staggeredTwoRail : staggeredTwoDiagram.StaggeredRail 2 where
  rho j := Fin.ofNat 72 (6 * j)
  eta j := Fin.ofNat 72 (6 * (2 + j))
  vertexOf_mem := by simp only [DiskMap.vertexOf_mem_internalVertices]; decide
  injOn_vertexOf := by simp only [Set.InjOn, mem_coe]; decide
  one_le := by decide +kernel
  inv_rho_three := by decide +kernel
  inv_rho_zero_one := by decide +kernel
  inv_eta_three := fun j h₁ h₂ => by interval_cases j; decide
  inv_rho_two := fun j h₁ h₂ => by interval_cases j <;> decide
  inv_rho_one := fun j h₁ h₂ => by interval_cases j <;> decide

-- The darts at the points of the rail.
example : staggeredTwoRail.darts.card = 30 := by decide +kernel
-- The tuples prescribing the new rotation, as darts.
example : staggeredTwoRail.staggeredCombTuples =
    [[0, 19, 20, 1, 2, 5], [18, 25, 26, 21, 8, 3], [24, 27, 14, 15, 28, 9], [6, 7, 10, 11, 4,
      23], [12, 13, 16, 17, 22, 29]] := by
  decide +kernel
-- The new rotation has the tuples as cycles.
example : ∀ l ∈ staggeredTwoRail.staggeredCombTuples, ∀ i (hi : i < l.length),
    staggeredTwoRail.staggeredComb.rot l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
  decide +kernel

end RailExamples

end TripleData

end ClusterAlgebras

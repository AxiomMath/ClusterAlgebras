/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.TripleDiagram
public import ClusterAlgebras.Plabic.Winding

/-!
# The two sides of a simple arc

Let `X` be a triple diagram with `b` arcs. An arc `S = (e₁, …, e_m)` of `X` is *simple* if its
triple points `z_l = v(ē_l)`, `l ∈ [1, m - 1]`, are pairwise distinct. At each `z_l` the arc enters
along `ē_l` and leaves along `e_{l+1} = σ³(ē_l)`; the darts `σ ē_l, σ² ē_l` are on its right and
`σ⁴ ē_l, σ⁵ ē_l` on its left.

The two sides are defined by a winding function. Let `S` run from `s_i = ε(p)` to
`t_{π(i)} = ε(q)`, let `n_r` be the dart of `ε(r)` not in `B`, and `β_r` the dart of the exterior
`f_∞` at `ε(r + 1)` running to `ε(r)`. The darts `e₁, …, e_m` followed by `β̄_q, …, β̄_{p-1}`
(the *right run* `q, q + 1, …, p - 1`) form a closed walk with pairwise distinct vertices, and its
cycle `c_S` (`1` on these darts, `-1` on their reverses) has a unique winding function `h`
(`h(f_∞) = 0`, `h(f(d̄)) - h(f(d)) = c_S(d)`). It takes the value `-1` to the right of `S` and `0`
to its left, and only these values. The darts not in `B` and not on `S` thus split into the right
side `H_right(S)` (`h = -1`) and the left side `H_left(S)` (`h = 0`). Locally, a side contains
the legs `n_r` at the positions on that side and the darts on that side at the triple points of
`S`, listed in the *cut lists*; globally it is everything reachable from its cut list without
crossing `S`.

## Main definitions

* `ClusterAlgebras.TripleData.IsSimpleArc`, `ClusterAlgebras.TripleData.arcDarts`: simple arcs and
  their darts.
* `ClusterAlgebras.TripleData.arcCycle`, `ClusterAlgebras.TripleData.IsArcWindingFunction`: the
  cycle `c_S` and the winding functions of a simple arc.
* `ClusterAlgebras.TripleData.arcSide`, `TripleData.rightSide`, `TripleData.leftSide`: the two
  sides of a simple arc.
* `ClusterAlgebras.TripleData.rightCutList`, `TripleData.leftCutList`: the cut lists.

## Main results

* `ClusterAlgebras.TripleData.arcDart_succ_eq`,
  `ClusterAlgebras.TripleData.IsSimpleArc.rot_pow_inv_arcDart_mem_arcDarts_iff`,
  `ClusterAlgebras.TripleData.isOut_rot_pow_inv_arcDart`: the darts of a simple arc at its triple
  points.
* `ClusterAlgebras.TripleData.IsSimpleArc.existsUnique_isArcWindingFunction`: a simple arc has a
  unique winding function.
* `ClusterAlgebras.TripleData.IsArcWindingFunction.apply_arcDart`, `apply_inv_arcDart`,
  `apply_eq_neg_one_or_zero`: the winding function takes the values `0` and `-1`.
* `ClusterAlgebras.TripleData.IsSimpleArc.arcDarts_union_rightSide_union_leftSide`,
  `ClusterAlgebras.TripleData.disjoint_arcDarts_arcSide`,
  `ClusterAlgebras.TripleData.disjoint_rightSide_leftSide`, and (1)–(4)
  `IsSimpleArc.inv_mem_arcSide`, `IsSimpleArc.forall_mem_rightSide_or_forall_mem_leftSide`,
  `IsSimpleArc.rot_pow_inv_arcDart_mem_rightSide`, `IsSimpleArc.rot_pow_inv_arcDart_mem_leftSide`,
  `IsSimpleArc.endDart_mem_rightSide`, `IsSimpleArc.endDart_mem_leftSide`: the local description
  of the sides.
* `ClusterAlgebras.TripleData.IsSimpleArc.mem_rightCutList_or_of_mem_rightSide`,
  `IsSimpleArc.mem_leftCutList_or_of_mem_leftSide`,
  `IsSimpleArc.mem_rightSide_of_mem_rightCutList`, `IsSimpleArc.mem_leftSide_of_mem_leftCutList`:
  where the darts of a side lie.
* `ClusterAlgebras.TripleData.IsSimpleArc.isLeast_rightSide`,
  `ClusterAlgebras.TripleData.IsSimpleArc.isLeast_leftSide`: sides by reachability.

## Implementation notes

* **Indices.** Darts of the arc from `s_{i+1}` are `0`-indexed: FWZ's `e_l` is
  `X.arcDart i (l - 1)`, so its triple point `z_l` is `v(X.arcDart i (l - 1)̄)` and the condition
  `l ∈ [1, m - 1]` reads `l - 1 + 1 < m`. Endpoint labels are `0`-indexed as in
  `ClusterAlgebras.TripleData`: `r : Fin (2 * b)` is FWZ's `r + 1`, `p = sourceIndex i` and
  `q = arcEndIndex i = targetIndex (π(i))`.
* **Positions.** The clockwise distance from `q` to `r` is the value of `r - q` in `Fin (2 * b)`.
  The right run is the set of `r` with `r - q < p - q`, the right positions are those with
  `0 < r - q < p - q`, the left positions those with `0 < r - p < q - p`.
* **The darts `β_r`.** The dart `β_r` is defined as `(σ n_r)̄` (`exteriorDart`): by the rotation
  at a labelled boundary vertex it is the dart of `f_∞` at `ε(r + 1)` running to `ε(r)`
  (`exteriorDart_mem_exterior`, `vertexOf_exteriorDart`, `vertexOf_inv_exteriorDart`).
* **The cycle.** `c_S` is defined as `1` on the darts `e_l` and `β̄_r` (`r` in the right run), `-1`
  on their reverses and `0` elsewhere; these darts are pairwise distinct and distinct from their
  reverses, which gives the values of [FWZ]. It is the cycle of the closed walk `arcWalk`
  (`arcCycle_eq_walkCycle`), a simple closed walk of the underlying disk map, so that the results
  on winding functions of simple closed walks apply.
* **Sides.** [FWZ] defines the sides through the winding function `h`, which is unique.
  Here the sides are defined through a chosen winding function `arcWinding`, and any winding
  function may be used to compute them (`IsArcWindingFunction.eq_arcWinding`). Both sides are
  instances of `arcSide i v`, the darts off `B` and off `S` on which the winding function is `v`.
* **Reachability.** The smallest set of [FWZ] is expressed with `IsLeast` in the lattice of
  sets of darts.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Clockwise distances in `Fin n` -/

section CyclicDistance

variable {n : ℕ}

private theorem fin_val_sub (a c : Fin n) :
    ((a - c : Fin n) : ℕ) = if (c : ℕ) ≤ a then (a : ℕ) - c else n + (a : ℕ) - c := by
  split_ifs with h
  · exact Fin.coe_sub_iff_le.2 h
  · exact Fin.coe_sub_iff_lt.2 (not_le.1 h)

private theorem val_finRotate' (j : Fin n) :
    (finRotate n j : ℕ) = if (j : ℕ) + 1 < n then (j : ℕ) + 1 else 0 := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : j = Fin.last n
    · subst h; simp
    · have : (j : ℕ) < n := Fin.val_lt_last h
      simp only [h, if_false, show (j : ℕ) + 1 < n + 1 by omega, if_true]

private theorem val_finRotate_pow (q : Fin n) (s : ℕ) :
    ((finRotate n ^ s) q : ℕ) = ((q : ℕ) + s) % n := by
  induction s with
  | zero => simp [Nat.mod_eq_of_lt q.isLt]
  | succ s ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, val_finRotate', ih, ← add_assoc, Nat.add_mod _ 1]
    have hn := q.pos
    have hx := Nat.mod_lt ((q : ℕ) + s) hn
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [Nat.mod_eq_of_lt h1]
      split_ifs with h
      · rw [Nat.mod_eq_of_lt h]
      · rw [show ((q : ℕ) + s) % n + 1 = n by omega, Nat.mod_self]
    · have : n = 1 := by omega
      subst this
      simp [Nat.mod_one]

private theorem val_finRotate_pow_of_lt (q : Fin n) {s : ℕ} (hs : s < n) :
    ((finRotate n ^ s) q : ℕ) = if (q : ℕ) + s < n then (q : ℕ) + s else (q : ℕ) + s - n := by
  rw [val_finRotate_pow]
  have := q.isLt
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The `s`-th clockwise successor of `q` lies at clockwise distance `s` from `q`. -/
private theorem val_finRotate_pow_sub (q : Fin n) {s : ℕ} (hs : s < n) :
    (((finRotate n ^ s) q - q : Fin n) : ℕ) = s := by
  rw [fin_val_sub, val_finRotate_pow_of_lt q hs]
  have := q.isLt
  split_ifs <;> omega

/-- Walking clockwise from `q` by the clockwise distance from `q` to `r` reaches `r`. -/
private theorem finRotate_pow_val_sub (r q : Fin n) :
    (finRotate n ^ ((r - q : Fin n) : ℕ)) q = r := by
  have hlt := (r - q).isLt
  apply Fin.ext
  rw [val_finRotate_pow_of_lt q hlt, fin_val_sub]
  have := q.isLt
  have := r.isLt
  split_ifs <;> omega

private theorem val_sub_add_val_sub {p q : Fin n} (h : p ≠ q) :
    ((p - q : Fin n) : ℕ) + ((q - p : Fin n) : ℕ) = n := by
  have h' : (p : ℕ) ≠ q := fun e => h (Fin.ext e)
  rw [fin_val_sub, fin_val_sub]
  have := q.isLt
  have := p.isLt
  split_ifs <;> omega

private theorem val_sub_eq_zero_iff {r q : Fin n} : ((r - q : Fin n) : ℕ) = 0 ↔ r = q := by
  constructor
  · intro h
    rw [← finRotate_pow_val_sub r q, h, pow_zero, Equiv.Perm.one_apply]
  · rintro rfl
    rw [fin_val_sub]
    simp

private theorem finRotate_pow_add (q : Fin n) (s t : ℕ) :
    (finRotate n ^ (s + t)) q = (finRotate n ^ s) ((finRotate n ^ t) q) := by
  rw [pow_add, Equiv.Perm.mul_apply]

private theorem finRotate_pow_succ (q : Fin n) (s : ℕ) :
    (finRotate n ^ (s + 1)) q = finRotate n ((finRotate n ^ s) q) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

end CyclicDistance

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)

/-! ### Simple arcs -/

/-- The label `q` of the endpoint `t_{π(i)} = ε(q)` at which the arc from `s_i` ends
(`0`-indexed: `targetIndex (π_X(i))`). -/
def arcEndIndex (i : Fin b) : Fin (2 * b) := targetIndex (X.strandPerm i)

/-- The **darts** of the arc `(e₁, …, e_m)` from `s_i`: the `e_l` and the `ē_l`, `l ∈ [1, m]`. -/
@[cluster_algebras "def_simple_arc"]
def arcDarts (i : Fin b) : Finset H := (X.arc i).toFinset ∪ (X.arc i).toFinset.image X.inv

/-- A **simple arc**: the arc `(e₁, …, e_m)` from `s_i` is simple if its triple points
`z_l = v(ē_l)`, `l ∈ [1, m - 1]`, are pairwise distinct. With `0`-indexed darts
`e_{k+1} = X.arcDart i k`, the condition reads: `v(ē_{k+1}) = v(ē_{l+1})` with `k + 1 < m` and
`l + 1 < m` implies `k = l`. -/
@[cluster_algebras "def_simple_arc"]
def IsSimpleArc (i : Fin b) : Prop :=
  ∀ k l, k + 1 < X.arcLength i → l + 1 < X.arcLength i →
    X.vertexOf (X.inv (X.arcDart i k)) = X.vertexOf (X.inv (X.arcDart i l)) → k = l

/-! ### Positions and the cycle of a simple arc -/

/-- The clockwise distance `p - q` from the end `ε(q)` of the arc from `s_i` to its start
`ε(p)`, the number of positions in its right run. -/
def rightRunLength (i : Fin b) : ℕ := ((sourceIndex i - X.arcEndIndex i : Fin (2 * b)) : ℕ)

/-- The **right run** `q, q + 1, …, p - 1` of the arc from `s_i = ε(p)` to `t_{π(i)} = ε(q)`:
the labels `r` at clockwise distance less than `p - q` from `q`. -/
def rightRun (i : Fin b) : Finset (Fin (2 * b)) :=
  {r | ((r - X.arcEndIndex i : Fin (2 * b)) : ℕ) < X.rightRunLength i}

/-- The **right positions** `q + 1, …, p - 1` of the arc from `s_i = ε(p)` to `t_{π(i)} = ε(q)`. -/
def IsRightPosition (i : Fin b) (r : Fin (2 * b)) : Prop :=
  r ≠ X.arcEndIndex i ∧ r ∈ X.rightRun i

/-- The **left positions** `p + 1, …, q - 1` of the arc from `s_i = ε(p)` to `t_{π(i)} = ε(q)`. -/
def IsLeftPosition (i : Fin b) (r : Fin (2 * b)) : Prop :=
  r ≠ sourceIndex i ∧
    ((r - sourceIndex i : Fin (2 * b)) : ℕ) < ((X.arcEndIndex i - sourceIndex i : Fin (2 * b)) : ℕ)

/-- The dart `β_r` of the exterior at `ε(r + 1)` running to `ε(r)`, defined as `(σ n_r)̄`; see
`exteriorDart_mem_exterior`, `vertexOf_exteriorDart` and `vertexOf_inv_exteriorDart`. -/
def exteriorDart (r : Fin (2 * b)) : H := X.inv (X.rot (X.endDart r))

/-- The darts on which the cycle of the arc from `s_i` is `1`: the darts `e_l` of the arc and the
darts `β̄_r` for `r` in its right run. -/
def arcPositiveDarts (i : Fin b) : Finset H :=
  (X.arc i).toFinset ∪ (X.rightRun i).image fun r => X.inv (X.exteriorDart r)

/-- The **cycle** `c_S : H → ℤ` of a simple arc `S = (e₁, …, e_m)` from `s_i`:
`c_S(e_l) = 1`, `c_S(ē_l) = -1`, `c_S(β̄_r) = 1` and `c_S(β_r) = -1` for `r` in the right run of
`S`, and `c_S = 0` on all other darts. -/
@[cluster_algebras "def_arc_winding"]
def arcCycle (i : Fin b) (d : H) : ℤ :=
  if d ∈ X.arcPositiveDarts i then 1 else if X.inv d ∈ X.arcPositiveDarts i then -1 else 0

/-- A **winding function** of the simple arc from `s_i`: a function `h : Φ → ℤ` on the orbits of
`φ` with `h(f_∞) = 0` and `h(f(d̄)) - h(f(d)) = c_S(d)` for every dart `d`. -/
@[cluster_algebras "def_arc_winding"]
abbrev IsArcWindingFunction (i : Fin b) (h : X.faceOrbits → ℤ) : Prop :=
  X.IsWindingFunction (X.arcCycle i) h

/-- The closed walk `e₁, …, e_m, β̄_q, β̄_{q+1}, …, β̄_{p-1}` around the right of the arc from
`s_i = ε(p)` to `t_{π(i)} = ε(q)`, indexed by `Fin (m + (p - q))`. -/
def arcWalk (i : Fin b) (j : Fin (X.arcLength i + X.rightRunLength i)) : H :=
  if (j : ℕ) < X.arcLength i then X.arcDart i j
  else X.inv (X.exteriorDart ((finRotate (2 * b) ^ ((j : ℕ) - X.arcLength i)) (X.arcEndIndex i)))

/-! ### Basic facts on triple diagrams -/

section Basic

variable {X} (hX : X.IsTripleDiagram)

include hX

private theorem inv_inv' (d : H) : X.inv (X.inv d) = d := hX.inv_involutive d

private theorem inv_mem_bdry_iff' {d : H} : X.inv d ∈ X.bdry ↔ d ∈ X.bdry :=
  hX.toIsDiskMap.inv_mem_bdry_iff

omit hX in
private theorem vertexOf_rot_pow' (n : ℕ) (d : H) : X.vertexOf ((X.rot ^ n) d) = X.vertexOf d :=
  X.vertexOf_eq_of_mem (X.mem_vertexOf.2 (Equiv.Perm.sameCycle_pow_right.2
    (Equiv.Perm.SameCycle.refl _ _)))

omit hX in
private theorem notMem_bdry_of_internal {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) :
    d ∉ X.bdry := fun h => hd (X.isBoundaryVertex_vertexOf_of_mem h)

private theorem isBoundaryVertex_endpoint' (r : Fin (2 * b)) :
    X.IsBoundaryVertex (X.vertexOf (X.endDart r)) :=
  (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2

/-- At a triple point, `σ⁶ d = d` and `d, σ d, …, σ⁵ d` are distinct. -/
private theorem rot_pow_six' {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) :
    (X.rot ^ 6) d = d ∧ ∀ i j : ℕ, i < 6 → j < 6 → (X.rot ^ i) d = (X.rot ^ j) d → i = j := by
  have h : ({y | X.rot.SameCycle d y} : Finset H).card = 6 :=
    hX.internalVertex_card _ (X.vertexOf_mem_internalVertices.2 hd)
  set f := X.rot
  have hx : f d ≠ d := by
    intro hfx
    have : ({y | f.SameCycle d y} : Finset H) = {d} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun h => (h.eq_of_left hfx).symm, fun h => h ▸ Equiv.Perm.SameCycle.refl _ _⟩
    rw [this] at h
    simp at h
  have hsupp : (f.cycleOf d).support = ({y | f.SameCycle d y} : Finset H) := by
    ext y
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    simp [hx]
  have hc : (f.cycleOf d).support.card = 6 := hsupp ▸ h
  refine ⟨?_, fun i j hi hj hij => ?_⟩
  · have := f.pow_mod_card_support_cycleOf_self_apply 6 d
    rw [hc] at this
    simpa using this.symm
  · have hl : (f.toList d).length = 6 := by rw [Equiv.Perm.length_toList, hc]
    have e1 := Equiv.Perm.getElem_toList f d i (by omega)
    have e2 := Equiv.Perm.getElem_toList f d j (by omega)
    exact ((Equiv.Perm.nodup_toList f d).getElem_inj_iff (hi := by omega) (hj := by omega)).1
      (by rw [e1, e2, hij])

private theorem rot_pow_mod_six' {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) (n : ℕ) :
    (X.rot ^ n) d = (X.rot ^ (n % 6)) d := by
  conv_lhs => rw [← Nat.mod_add_div n 6, pow_add, pow_mul, Equiv.Perm.mul_apply,
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (rot_pow_six' hX hd).1 (n / 6)]

/-- A dart at the vertex of `d` (a triple point) is `σʲ d` for some `j < 6`. -/
private theorem exists_rot_pow_of_mem {d e : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d))
    (he : e ∈ X.vertexOf d) : ∃ j < 6, e = (X.rot ^ j) d := by
  obtain ⟨n, hn⟩ := (X.mem_vertexOf.1 he).exists_nat_pow_eq
  exact ⟨n % 6, Nat.mod_lt _ (by norm_num), by rw [← hn, rot_pow_mod_six' hX hd]⟩

private theorem isOut_rot_pow' {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) (n : ℕ) :
    X.isOut ((X.rot ^ n) d) = (X.isOut d ^^ decide (Odd n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hX.isOut_rot ((X.rot ^ n) d) (by rwa [vertexOf_rot_pow'])
    rw [pow_succ', Equiv.Perm.mul_apply]
    rw [ih] at h
    revert h
    cases X.isOut (X.rot ((X.rot ^ n) d)) <;> cases X.isOut d <;>
      by_cases ho : Odd n <;> simp [ho, Nat.odd_add_one]

private theorem isOut_inv' {d : H} (hd : d ∉ X.bdry) : X.isOut (X.inv d) = !X.isOut d := by
  have := hX.isOut_inv d hd
  revert this
  cases X.isOut (X.inv d) <;> cases X.isOut d <;> simp

/-! #### The darts `β_r` -/

/-- The rotation at `ε(r)`: `σ n_r = β̄_r` with `β_r` the dart of the exterior at `ε(r + 1)`
running to `ε(r)`. -/
private theorem exteriorDart_spec (r : Fin (2 * b)) :
    X.exteriorDart r ∈ X.exterior ∧ X.exteriorDart r ∈ X.endpoint (finRotate (2 * b) r) ∧
      X.inv (X.exteriorDart r) ∈ X.endpoint r := by
  obtain ⟨β, hβe, hβv, hβi⟩ := hX.exists_exterior r
  obtain ⟨p, hpe, hpv, -⟩ := hX.exists_exterior ((finRotate (2 * b)).symm r)
  rw [Equiv.apply_symm_apply] at hpv
  have key := DiskMap.rot_cycle_of_mem_boundaryVertices (M := X.toDiskMap) hX.inv_involutive
    hX.inv_mem_bdry hX.boundaryVertex_card hX.exists_orbit (hX.endpoint_mem r) hpe hpv hβe hβi
    (X.self_mem_vertexOf (X.endDart r)) (hX.endDart_notMem_bdry r)
  have : X.exteriorDart r = β := by
    rw [exteriorDart, key.2.2.2, inv_inv' hX]
  rw [this]
  exact ⟨hβe, hβv, hβi⟩

/-- `β_r` lies in the exterior `f_∞`. -/
theorem exteriorDart_mem_exterior (r : Fin (2 * b)) : X.exteriorDart r ∈ X.exterior :=
  (exteriorDart_spec hX r).1

/-- `β_r` lies at `ε(r + 1)`. -/
theorem vertexOf_exteriorDart (r : Fin (2 * b)) :
    X.vertexOf (X.exteriorDart r) = X.endpoint (finRotate (2 * b) r) :=
  X.vertexOf_eq_of_mem (exteriorDart_spec hX r).2.1

/-- `β_r` runs to `ε(r)`. -/
theorem vertexOf_inv_exteriorDart (r : Fin (2 * b)) :
    X.vertexOf (X.inv (X.exteriorDart r)) = X.endpoint r :=
  X.vertexOf_eq_of_mem (exteriorDart_spec hX r).2.2

/-- The rotation at `ε(r + 1)` sends `β_r` to `n_{r+1}`. -/
theorem rot_exteriorDart (r : Fin (2 * b)) :
    X.rot (X.exteriorDart r) = X.endDart (finRotate (2 * b) r) := by
  have hpv : X.exteriorDart r ∈ X.endpoint (finRotate (2 * b) r) := (exteriorDart_spec hX r).2.1
  have hq := exteriorDart_spec hX (finRotate (2 * b) r)
  exact (DiskMap.rot_cycle_of_mem_boundaryVertices (M := X.toDiskMap) hX.inv_involutive
    hX.inv_mem_bdry hX.boundaryVertex_card hX.exists_orbit (hX.endpoint_mem _)
    (exteriorDart_mem_exterior hX r) hpv hq.1 hq.2.2
    (X.self_mem_vertexOf _) (hX.endDart_notMem_bdry _)).2.2.1

private theorem exteriorDart_mem_bdry (r : Fin (2 * b)) : X.exteriorDart r ∈ X.bdry :=
  X.exterior_subset_bdry (exteriorDart_mem_exterior hX r)

private theorem inv_exteriorDart_mem_bdry (r : Fin (2 * b)) :
    X.inv (X.exteriorDart r) ∈ X.bdry :=
  (inv_mem_bdry_iff' hX).2 (exteriorDart_mem_bdry hX r)

/-- The reverse of a dart of the exterior is not in the exterior. -/
private theorem inv_notMem_exterior {d : H} (hd : d ∈ X.exterior) : X.inv d ∉ X.exterior :=
  fun h => disjoint_left.1 hX.toIsDiskMap.disjoint_exterior_map_inv h
    (mem_map_equiv.2 (by rw [Equiv.symm_apply_apply]; exact hd))

private theorem exteriorDart_injective : Function.Injective X.exteriorDart := by
  intro r s h
  apply hX.endpoint_injective
  rw [← vertexOf_inv_exteriorDart hX, h, vertexOf_inv_exteriorDart hX]

/-! #### Arcs -/

/-- In a triple diagram every arc reaches an endpoint. -/
private theorem arcLength_pos (i : Fin b) : 0 < X.arcLength i := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  have hr := X.arcLength_eq_zero_iff.1 h0
  have hS : ∀ k, X.strandMap (X.arcDart i k) = (X.rot ^ 3) (X.inv (X.arcDart i k)) := fun k => by
    rw [strandMap, if_neg (hr k)]
  -- the map `S` is injective along the orbit of `a_i`, so this orbit returns to `a_i`
  obtain ⟨a, c, hne, hac⟩ := Finite.exists_ne_map_eq_of_infinite (X.arcDart i)
  have hinj : ∀ k l, X.arcDart i (k + 1) = X.arcDart i (l + 1) → X.arcDart i k = X.arcDart i l :=
    fun k l h => by
      rw [arcDart_succ, arcDart_succ, hS, hS] at h
      exact X.inv.injective ((X.rot ^ 3).injective h)
  have back : ∀ a c, a < c → X.arcDart i a = X.arcDart i c → X.arcDart i 0 = X.arcDart i (c - a) :=
    by
    intro a
    induction a with
    | zero => intro c _ h; simpa using h
    | succ a ih =>
      intro c hlt h
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [show c' + 1 - (a + 1) = c' - a by omega]
      exact ih c' (by omega) (hinj a c' h)
  obtain ⟨t, ht⟩ : ∃ t, X.arcDart i 0 = X.arcDart i (t + 1) := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨c - a - 1, by rw [back a c hlt hac]; congr 1; omega⟩
    · exact ⟨a - c - 1, by rw [back c a hlt hac.symm]; congr 1; omega⟩
  apply hr t
  change X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart i t)))
  rw [← vertexOf_rot_pow' 3, ← hS t, ← arcDart_succ, ← ht, arcDart_zero]
  exact isBoundaryVertex_endpoint' hX _

private theorem not_runsToEndpoint_arcDart {i : Fin b} {k : ℕ} (hk : k + 1 < X.arcLength i) :
    ¬X.RunsToEndpoint (X.arcDart i k) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (arcLength_pos hX i).ne'
  exact (X.arcLength_eq_succ_iff.1 hm).2 k (by omega)

private theorem runsToEndpoint_arcDart_last (i : Fin b) :
    X.RunsToEndpoint (X.arcDart i (X.arcLength i - 1)) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (arcLength_pos hX i).ne'
  rw [hm, Nat.succ_sub_one]
  exact (X.arcLength_eq_succ_iff.1 hm).1

/-- Consecutive darts of an arc: `e_{l+1} = σ³(ē_l)` for `l ∈ [1, m - 1]` (here
`e_{k+1}` is `X.arcDart i k`). -/
@[cluster_algebras "lem_simple_arc_darts"]
theorem arcDart_succ_eq {i : Fin b} {k : ℕ} (hk : k + 1 < X.arcLength i) :
    X.arcDart i (k + 1) = (X.rot ^ 3) (X.inv (X.arcDart i k)) := by
  rw [arcDart_succ, strandMap, if_neg (not_runsToEndpoint_arcDart hX hk)]

private theorem vertexOf_arcDart_succ {i : Fin b} {k : ℕ} (hk : k + 1 < X.arcLength i) :
    X.vertexOf (X.arcDart i (k + 1)) = X.vertexOf (X.inv (X.arcDart i k)) := by
  rw [arcDart_succ_eq hX hk, vertexOf_rot_pow']

/-- The darts of an arc are `out` darts not in `B`. -/
private theorem arcDart_notMem_bdry_isOut {i : Fin b} {k : ℕ} (hk : k < X.arcLength i) :
    X.arcDart i k ∉ X.bdry ∧ X.isOut (X.arcDart i k) = true := by
  induction k with
  | zero => exact ⟨hX.endDart_notMem_bdry _, hX.isOut_source i⟩
  | succ k ih =>
    obtain ⟨hB, hO⟩ := ih (by omega)
    have hr := not_runsToEndpoint_arcDart hX hk
    have hiB : X.inv (X.arcDart i k) ∉ X.bdry := fun h => hB ((inv_mem_bdry_iff' hX).1 h)
    rw [arcDart_succ_eq hX hk]
    refine ⟨notMem_bdry_of_internal (by rwa [vertexOf_rot_pow']), ?_⟩
    rw [isOut_rot_pow' hX hr, isOut_inv' hX hB, hO]
    decide

private theorem arcDart_notMem_bdry {i : Fin b} {k : ℕ} (hk : k < X.arcLength i) :
    X.arcDart i k ∉ X.bdry :=
  (arcDart_notMem_bdry_isOut hX hk).1

private theorem inv_arcDart_notMem_bdry {i : Fin b} {k : ℕ} (hk : k < X.arcLength i) :
    X.inv (X.arcDart i k) ∉ X.bdry := fun h =>
  arcDart_notMem_bdry hX hk ((inv_mem_bdry_iff' hX).1 h)

private theorem isOut_arcDart {i : Fin b} {k : ℕ} (hk : k < X.arcLength i) :
    X.isOut (X.arcDart i k) = true :=
  (arcDart_notMem_bdry_isOut hX hk).2

private theorem isOut_inv_arcDart {i : Fin b} {k : ℕ} (hk : k < X.arcLength i) :
    X.isOut (X.inv (X.arcDart i k)) = false := by
  rw [isOut_inv' hX (arcDart_notMem_bdry hX hk), isOut_arcDart hX hk]
  rfl

/-- The unique dart not in `B` at an endpoint `ε(r)` is `n_r`. -/
private theorem eq_endDart {d : H} {r : Fin (2 * b)} (hd : d ∉ X.bdry)
    (hv : X.vertexOf d = X.endpoint r) : d = X.endDart r :=
  DiskMap.eq_of_notMem_bdry hX.boundaryVertex_card (x := X.endDart r)
    (isBoundaryVertex_endpoint' hX r)
    (by
      rw [show X.vertexOf (X.endDart r) = X.endpoint r from rfl, ← hv]
      exact X.self_mem_vertexOf d)
    (X.self_mem_vertexOf _) hd (hX.endDart_notMem_bdry r)

/-- The arc from `s_i` ends at `ε(q)`, `q = arcEndIndex i`: its last dart `e_m` satisfies
`ē_m = n_q`. -/
theorem endDart_arcEndIndex (i : Fin b) :
    X.endDart (X.arcEndIndex i) = X.inv (X.arcDart i (X.arcLength i - 1)) := by
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero (arcLength_pos hX i).ne'
  have hM' : X.arcLength i - 1 = M := by omega
  rw [hM']
  have heB : X.inv (X.arcDart i M) ∉ X.bdry := inv_arcDart_notMem_bdry hX (by omega)
  have hr : X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart i M))) := by
    have := runsToEndpoint_arcDart_last hX i
    rwa [hM'] at this
  obtain ⟨r, hr'⟩ := hX.exists_endpoint_eq _ (X.vertexOf_mem_boundaryVertices.2 hr)
  have her : X.inv (X.arcDart i M) = X.endDart r := eq_endDart hX heB hr'.symm
  have hout : X.isOut (X.endDart r) = false := by
    rw [← her]
    exact isOut_inv_arcDart hX (by omega)
  obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := exists_sourceIndex_or_targetIndex r
  · simp [hX.isOut_source j] at hout
  · have hT := X.target_strandPerm hM ⟨j, hr'⟩
    have : X.arcEndIndex i = targetIndex j := hX.endpoint_injective (hT.trans hr'.symm)
    rw [this, ← her]

end Basic

/-! ### The darts of a simple arc -/

section Darts

variable {X} {i : Fin b}

/-- A dart lies on the arc from `s_i` iff it is one of its darts `X.arcDart i t`. -/
theorem mem_arc_toFinset {d : H} :
    d ∈ (X.arc i).toFinset ↔ ∃ t < X.arcLength i, X.arcDart i t = d := by
  simp [arc]

/-- The darts of the arc from `s_i` are its darts `X.arcDart i t` and their inverses. -/
theorem mem_arcDarts {d : H} :
    d ∈ X.arcDarts i ↔ ∃ t < X.arcLength i, d = X.arcDart i t ∨ d = X.inv (X.arcDart i t) := by
  simp only [arcDarts, mem_union, mem_image, mem_arc_toFinset]
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨y, ⟨t, ht, rfl⟩, rfl⟩)
    · exact ⟨t, ht, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inr rfl⟩
  · rintro ⟨t, ht, rfl | rfl⟩
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr ⟨_, ⟨t, ht, rfl⟩, rfl⟩

/-- Each dart `X.arcDart i t` of the arc from `s_i` is among its darts. -/
theorem arcDart_mem_arcDarts {t : ℕ} (ht : t < X.arcLength i) : X.arcDart i t ∈ X.arcDarts i :=
  mem_arcDarts.2 ⟨t, ht, Or.inl rfl⟩

/-- The inverse of each dart `X.arcDart i t` of the arc from `s_i` is among its darts. -/
theorem inv_arcDart_mem_arcDarts {t : ℕ} (ht : t < X.arcLength i) :
    X.inv (X.arcDart i t) ∈ X.arcDarts i :=
  mem_arcDarts.2 ⟨t, ht, Or.inr rfl⟩

variable (hX : X.IsTripleDiagram)

include hX

/-- The darts of an arc are not in `B`. -/
theorem notMem_bdry_of_mem_arcDarts {d : H} (hd : d ∈ X.arcDarts i) : d ∉ X.bdry := by
  obtain ⟨t, ht, rfl | rfl⟩ := mem_arcDarts.1 hd
  · exact arcDart_notMem_bdry hX ht
  · exact inv_arcDart_notMem_bdry hX ht

/-- The darts of an arc are closed under `d ↦ d̄`. -/
theorem inv_mem_arcDarts {d : H} (hd : d ∈ X.arcDarts i) : X.inv d ∈ X.arcDarts i := by
  obtain ⟨t, ht, rfl | rfl⟩ := mem_arcDarts.1 hd
  · exact inv_arcDart_mem_arcDarts ht
  · rw [inv_inv' hX]
    exact arcDart_mem_arcDarts ht

/-- The only darts of a simple arc at its triple point `z_{k+1} = v(ē_{k+1})` are `ē_{k+1}` and
`e_{k+2}`. -/
private theorem eq_of_mem_arcDarts_of_vertexOf_eq (hS : X.IsSimpleArc i) {k : ℕ}
    (hk : k + 1 < X.arcLength i) {y : H} (hy : y ∈ X.arcDarts i)
    (hv : X.vertexOf y = X.vertexOf (X.inv (X.arcDart i k))) :
    y = X.inv (X.arcDart i k) ∨ y = X.arcDart i (k + 1) := by
  have hz : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart i k))) :=
    not_runsToEndpoint_arcDart hX hk
  obtain ⟨t, ht, rfl | rfl⟩ := mem_arcDarts.1 hy
  · rcases t with _ | t
    · rw [arcDart_zero] at hv
      exact absurd (hv ▸ isBoundaryVertex_endpoint' hX _) hz
    · rw [vertexOf_arcDart_succ hX ht] at hv
      rw [hS t k (by omega) hk hv]
      exact Or.inr rfl
  · by_cases ht' : t + 1 < X.arcLength i
    · rw [hS t k ht' hk hv]
      exact Or.inl rfl
    · have hlast := runsToEndpoint_arcDart_last hX i
      rw [show X.arcLength i - 1 = t by omega] at hlast
      exact absurd (hv ▸ hlast) hz

/-- **The darts of a simple arc at its triple points**: among the six darts `σʲ(ē_l)`,
`j ∈ [0, 5]`, of `z_l`, `l ∈ [1, m - 1]`, exactly `ē_l` and `e_{l+1} = σ³(ē_l)` are darts of the
arc. Here `l = k + 1`. -/
@[cluster_algebras "lem_simple_arc_darts"]
theorem IsSimpleArc.rot_pow_inv_arcDart_mem_arcDarts_iff (hS : X.IsSimpleArc i) {k : ℕ}
    (hk : k + 1 < X.arcLength i) {j : ℕ} (hj : j < 6) :
    (X.rot ^ j) (X.inv (X.arcDart i k)) ∈ X.arcDarts i ↔ j = 0 ∨ j = 3 := by
  have hz : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart i k))) :=
    not_runsToEndpoint_arcDart hX hk
  constructor
  · intro hmem
    rcases eq_of_mem_arcDarts_of_vertexOf_eq hX hS hk hmem (vertexOf_rot_pow' _ _) with h | h
    · left
      exact (rot_pow_six' hX hz).2 j 0 hj (by norm_num) (by simpa using h)
    · right
      rw [arcDart_succ_eq hX hk] at h
      exact (rot_pow_six' hX hz).2 j 3 hj (by norm_num) h
  · rintro (rfl | rfl)
    · simpa using inv_arcDart_mem_arcDarts (X := X) (i := i) (t := k) (by omega)
    · rw [← arcDart_succ_eq hX hk]
      exact arcDart_mem_arcDarts hk

/-- **The darts of a simple arc at its triple points**, orientations: at `z_l = v(ē_l)`,
`o(σʲ ē_l)` is `in` for `j` even and `out` for `j` odd. Here `l = k + 1`, and the arc need not be
simple. -/
@[cluster_algebras "lem_simple_arc_darts"]
theorem isOut_rot_pow_inv_arcDart {k : ℕ} (hk : k + 1 < X.arcLength i) (j : ℕ) :
    X.isOut ((X.rot ^ j) (X.inv (X.arcDart i k))) = decide (Odd j) := by
  rw [isOut_rot_pow' hX (not_runsToEndpoint_arcDart hX hk), isOut_inv_arcDart hX (by omega)]
  simp

end Darts

/-! ### Positions -/

section Positions

variable {X} {i : Fin b}

private theorem arcEndIndex_ne_sourceIndex : X.arcEndIndex i ≠ sourceIndex i :=
  (sourceIndex_ne_targetIndex _ _).symm

private theorem rightRunLength_pos : 0 < X.rightRunLength i := by
  rw [rightRunLength, Nat.pos_iff_ne_zero, Ne, val_sub_eq_zero_iff]
  exact arcEndIndex_ne_sourceIndex.symm

private theorem rightRunLength_lt : X.rightRunLength i < 2 * b :=
  (sourceIndex i - X.arcEndIndex i).isLt

private theorem finRotate_pow_rightRunLength :
    (finRotate (2 * b) ^ X.rightRunLength i) (X.arcEndIndex i) = sourceIndex i :=
  finRotate_pow_val_sub _ _

private theorem val_sub_arcEndIndex {t : ℕ} (ht : t < 2 * b) :
    (((finRotate (2 * b) ^ t) (X.arcEndIndex i) - X.arcEndIndex i : Fin (2 * b)) : ℕ) = t :=
  val_finRotate_pow_sub _ ht

private theorem mem_rightRun_iff {r : Fin (2 * b)} :
    r ∈ X.rightRun i ↔
      ∃ t < X.rightRunLength i, (finRotate (2 * b) ^ t) (X.arcEndIndex i) = r := by
  simp only [rightRun, mem_filter, mem_univ, true_and]
  refine ⟨fun h => ⟨_, h, finRotate_pow_val_sub _ _⟩, ?_⟩
  rintro ⟨t, ht, rfl⟩
  rwa [val_sub_arcEndIndex (ht.trans rightRunLength_lt)]

private theorem finRotate_pow_mem_rightRun {t : ℕ} (ht : t < X.rightRunLength i) :
    (finRotate (2 * b) ^ t) (X.arcEndIndex i) ∈ X.rightRun i :=
  mem_rightRun_iff.2 ⟨t, ht, rfl⟩

/-- Every label other than `p` and `q` is a right position or a left position. -/
theorem isRightPosition_or_isLeftPosition {r : Fin (2 * b)} (hp : r ≠ sourceIndex i)
    (hq : r ≠ X.arcEndIndex i) : X.IsRightPosition i r ∨ X.IsLeftPosition i r := by
  rcases lt_or_ge ((r - X.arcEndIndex i : Fin (2 * b)) : ℕ) (X.rightRunLength i) with h | h
  · exact Or.inl ⟨hq, by simpa [rightRun] using h⟩
  · refine Or.inr ⟨hp, ?_⟩
    have hrq : (r : ℕ) ≠ X.arcEndIndex i := fun e => hq (Fin.ext e)
    have hrp : (r : ℕ) ≠ sourceIndex i := fun e => hp (Fin.ext e)
    have hpq : (sourceIndex i : ℕ) ≠ X.arcEndIndex i := fun e =>
      arcEndIndex_ne_sourceIndex (Fin.ext e.symm)
    have := r.isLt
    have := (sourceIndex i).isLt
    have := (X.arcEndIndex i).isLt
    rw [rightRunLength, fin_val_sub, fin_val_sub] at h
    rw [fin_val_sub, fin_val_sub]
    split_ifs at h ⊢ <;> omega

end Positions

/-! ### The closed walk around the right of a simple arc -/

section Walk

variable {X} {i : Fin b}

private theorem arcWalk_of_lt (j : Fin (X.arcLength i + X.rightRunLength i))
    (hj : (j : ℕ) < X.arcLength i) : X.arcWalk i j = X.arcDart i j :=
  if_pos hj

private theorem arcWalk_of_ge (j : Fin (X.arcLength i + X.rightRunLength i))
    (hj : X.arcLength i ≤ j) :
    X.arcWalk i j = X.inv (X.exteriorDart
      ((finRotate (2 * b) ^ ((j : ℕ) - X.arcLength i)) (X.arcEndIndex i))) :=
  if_neg (by omega)

/-- The darts of the walk are the darts on which the cycle is `1`. -/
private theorem mem_arcPositiveDarts_iff {d : H} :
    d ∈ X.arcPositiveDarts i ↔ ∃ j, X.arcWalk i j = d := by
  simp only [arcPositiveDarts, mem_union, mem_arc_toFinset, mem_image, mem_rightRun_iff]
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨r, ⟨t, ht, rfl⟩, rfl⟩)
    · exact ⟨⟨t, by omega⟩, arcWalk_of_lt _ ht⟩
    · refine ⟨⟨X.arcLength i + t, by omega⟩, ?_⟩
      rw [arcWalk_of_ge _ (by simp)]
      simp
  · rintro ⟨j, rfl⟩
    by_cases hj : (j : ℕ) < X.arcLength i
    · exact Or.inl ⟨j, hj, (arcWalk_of_lt j hj).symm⟩
    · refine Or.inr ⟨_, ⟨(j : ℕ) - X.arcLength i, by omega, rfl⟩, ?_⟩
      rw [arcWalk_of_ge j (by omega)]

variable (hX : X.IsTripleDiagram)

include hX

private theorem arcWalk_vertexOf_inv (j : Fin (X.arcLength i + X.rightRunLength i)) :
    X.vertexOf (X.inv (X.arcWalk i j)) =
      X.vertexOf (X.arcWalk i (finRotate (X.arcLength i + X.rightRunLength i) j)) := by
  have hm := arcLength_pos hX i
  have ha := rightRunLength_pos (X := X) (i := i)
  have hn := val_finRotate' j
  have hj := j.isLt
  by_cases h1 : (j : ℕ) + 1 < X.arcLength i
  · have hn' : ((finRotate _ j : Fin _) : ℕ) = (j : ℕ) + 1 := by
      rw [hn, if_pos (by omega)]
    rw [arcWalk_of_lt j (by omega), arcWalk_of_lt (finRotate _ j) (by omega), hn',
      vertexOf_arcDart_succ hX h1]
  by_cases h2 : (j : ℕ) + 1 = X.arcLength i
  · have hn' : ((finRotate _ j : Fin _) : ℕ) = X.arcLength i := by
      rw [hn, if_pos (by omega)]
      omega
    rw [arcWalk_of_lt j (by omega), arcWalk_of_ge (finRotate _ j) (by omega), hn', Nat.sub_self,
      pow_zero, Equiv.Perm.one_apply, vertexOf_inv_exteriorDart hX,
      show (j : ℕ) = X.arcLength i - 1 by omega, ← endDart_arcEndIndex hX]
    rfl
  have hge : X.arcLength i ≤ j := by omega
  rw [arcWalk_of_ge j hge, inv_inv' hX, vertexOf_exteriorDart hX, ← finRotate_pow_succ]
  by_cases h3 : (j : ℕ) + 1 < X.arcLength i + X.rightRunLength i
  · have hn' : ((finRotate _ j : Fin _) : ℕ) = (j : ℕ) + 1 := by
      rw [hn, if_pos (by omega)]
    rw [arcWalk_of_ge (finRotate _ j) (by omega), hn', vertexOf_inv_exteriorDart hX,
      show (j : ℕ) + 1 - X.arcLength i = (j : ℕ) - X.arcLength i + 1 by omega]
  · have hn' : ((finRotate _ j : Fin _) : ℕ) = 0 := by
      rw [hn, if_neg (by omega)]
    rw [arcWalk_of_lt (finRotate _ j) (by omega), hn', arcDart_zero,
      show (j : ℕ) - X.arcLength i + 1 = X.rightRunLength i by omega,
      finRotate_pow_rightRunLength]
    rfl

private theorem arcWalk_ne_inv (j : Fin (X.arcLength i + X.rightRunLength i)) :
    X.arcWalk i (finRotate (X.arcLength i + X.rightRunLength i) j) ≠ X.inv (X.arcWalk i j) := by
  have hm := arcLength_pos hX i
  have ha := rightRunLength_pos (X := X) (i := i)
  have hn := val_finRotate' j
  have hj := j.isLt
  by_cases h1 : (j : ℕ) + 1 < X.arcLength i
  · have hn' : ((finRotate _ j : Fin _) : ℕ) = (j : ℕ) + 1 := by
      rw [hn, if_pos (by omega)]
    rw [arcWalk_of_lt (finRotate _ j) (by omega), arcWalk_of_lt j (by omega), hn']
    intro h
    have h' := congrArg X.isOut h
    rw [isOut_arcDart hX h1, isOut_inv_arcDart hX (by omega)] at h'
    cases h'
  by_cases h2 : (j : ℕ) + 1 = X.arcLength i
  · have hn' : ((finRotate _ j : Fin _) : ℕ) = X.arcLength i := by
      rw [hn, if_pos (by omega)]
      omega
    rw [arcWalk_of_lt j (by omega), arcWalk_of_ge (finRotate _ j) (by omega)]
    intro h
    exact inv_arcDart_notMem_bdry hX (by omega) (h ▸ inv_exteriorDart_mem_bdry hX _)
  have hge : X.arcLength i ≤ j := by omega
  rw [arcWalk_of_ge j hge, inv_inv' hX]
  by_cases h3 : (j : ℕ) + 1 < X.arcLength i + X.rightRunLength i
  · have hn' : ((finRotate _ j : Fin _) : ℕ) = (j : ℕ) + 1 := by
      rw [hn, if_pos (by omega)]
    rw [arcWalk_of_ge (finRotate _ j) (by omega)]
    intro h
    exact inv_notMem_exterior hX (exteriorDart_mem_exterior hX _)
      (h ▸ exteriorDart_mem_exterior hX _)
  · have hn' : ((finRotate _ j : Fin _) : ℕ) = 0 := by
      rw [hn, if_neg (by omega)]
    rw [arcWalk_of_lt (finRotate _ j) (by omega)]
    intro h
    exact arcDart_notMem_bdry hX (by omega) (h ▸ exteriorDart_mem_bdry hX _)

/-- The vertex of the `j`-th dart of the walk: `ε(p)` for `j = 0`, the triple point
`z_j = v(ē_j)` for `0 < j < m`, and `ε(q + (j - m))` for `j ≥ m`. -/
private theorem vertexOf_arcWalk (j : Fin (X.arcLength i + X.rightRunLength i)) :
    ((j : ℕ) = 0 → X.vertexOf (X.arcWalk i j) = X.endpoint (sourceIndex i)) ∧
    (∀ k, (j : ℕ) = k + 1 → k + 1 < X.arcLength i →
      X.vertexOf (X.arcWalk i j) = X.vertexOf (X.inv (X.arcDart i k))) ∧
    (X.arcLength i ≤ j → X.vertexOf (X.arcWalk i j) =
      X.endpoint ((finRotate (2 * b) ^ ((j : ℕ) - X.arcLength i)) (X.arcEndIndex i))) := by
  have hm := arcLength_pos hX i
  refine ⟨fun h => ?_, fun k h hk => ?_, fun h => ?_⟩
  · rw [arcWalk_of_lt _ (by omega), h, arcDart_zero]
    rfl
  · rw [arcWalk_of_lt _ (by omega), h, vertexOf_arcDart_succ hX hk]
  · rw [arcWalk_of_ge _ h, vertexOf_inv_exteriorDart hX]

private theorem injective_vertexOf_arcWalk (hS : X.IsSimpleArc i) :
    Function.Injective fun j => X.vertexOf (X.arcWalk i j) := by
  have hm := arcLength_pos hX i
  have ha := rightRunLength_pos (X := X) (i := i)
  have hlt := rightRunLength_lt (X := X) (i := i)
  have bdry : ∀ r, X.IsBoundaryVertex (X.endpoint r) := isBoundaryVertex_endpoint' hX
  have key : ∀ j j' : Fin (X.arcLength i + X.rightRunLength i), (j : ℕ) ≤ j' →
      X.vertexOf (X.arcWalk i j) = X.vertexOf (X.arcWalk i j') → j = j' := by
    intro j j' hle h
    obtain ⟨A, B, C⟩ := vertexOf_arcWalk hX j
    obtain ⟨A', B', C'⟩ := vertexOf_arcWalk hX j'
    have hj' := j'.isLt
    apply Fin.ext
    by_cases hj0 : (j : ℕ) = 0
    · by_cases hj'0 : (j' : ℕ) = 0
      · omega
      by_cases hj'm : (j' : ℕ) < X.arcLength i
      · have hk := B' ((j' : ℕ) - 1) (by omega) (by omega)
        rw [A hj0, hk] at h
        exact absurd (h ▸ bdry _) (not_runsToEndpoint_arcDart hX (by omega))
      · rw [A hj0, C' (by omega)] at h
        have := congrArg (fun r : Fin (2 * b) => ((r - X.arcEndIndex i : Fin (2 * b)) : ℕ))
          (hX.endpoint_injective h)
        simp only [val_sub_arcEndIndex (show (j' : ℕ) - X.arcLength i < 2 * b by omega)] at this
        change X.rightRunLength i = _ at this
        omega
    by_cases hjm : (j : ℕ) < X.arcLength i
    · have hk := B ((j : ℕ) - 1) (by omega) (by omega)
      by_cases hj'm : (j' : ℕ) < X.arcLength i
      · have hk' := B' ((j' : ℕ) - 1) (by omega) (by omega)
        rw [hk, hk'] at h
        have := hS _ _ (by omega) (by omega) h
        omega
      · rw [hk, C' (by omega)] at h
        exact absurd (h ▸ bdry _) (not_runsToEndpoint_arcDart hX (by omega))
    · rw [C (by omega), C' (by omega)] at h
      have := congrArg (fun r : Fin (2 * b) => ((r - X.arcEndIndex i : Fin (2 * b)) : ℕ))
        (hX.endpoint_injective h)
      simp only [val_sub_arcEndIndex (show (j' : ℕ) - X.arcLength i < 2 * b by omega),
        val_sub_arcEndIndex (show (j : ℕ) - X.arcLength i < 2 * b by omega)] at this
      omega
  intro j j' h
  rcases le_total (j : ℕ) j' with hle | hle
  · exact key j j' hle h
  · exact (key j' j hle h.symm).symm

/-- The darts `e₁, …, e_m, β̄_q, …, β̄_{p-1}` of a simple arc and of its right run form a simple
closed walk. -/
theorem IsSimpleArc.isSimpleClosedWalk_arcWalk (hS : X.IsSimpleArc i) :
    X.IsSimpleClosedWalk (X.arcWalk i) where
  pos := by have := arcLength_pos hX i; omega
  vertexOf_inv := arcWalk_vertexOf_inv hX
  ne_inv := arcWalk_ne_inv hX
  injective_vertexOf := injective_vertexOf_arcWalk hX hS

/-- The cycle of a simple arc is the cycle of the closed walk `arcWalk`. -/
theorem IsSimpleArc.arcCycle_eq_walkCycle (hS : X.IsSimpleArc i) :
    X.arcCycle i = X.walkCycle (X.arcWalk i) := by
  have hw := hS.isSimpleClosedWalk_arcWalk hX
  funext d
  unfold arcCycle
  split_ifs with h1 h2
  · obtain ⟨j, rfl⟩ := mem_arcPositiveDarts_iff.1 h1
    exact (hw.walkCycle_apply_self j).symm
  · obtain ⟨j, hj⟩ := mem_arcPositiveDarts_iff.1 h2
    rw [show d = X.inv (X.arcWalk i j) by rw [hj, inv_inv' hX]]
    exact (hw.walkCycle_apply_inv hX.inv_involutive j).symm
  · refine (RotationSystem.walkCycle_eq_zero hX.inv_involutive (fun j hj => h1 ?_)
      fun j hj => h2 ?_).symm
    · exact mem_arcPositiveDarts_iff.2 ⟨j, hj.symm⟩
    · exact mem_arcPositiveDarts_iff.2 ⟨j, by rw [hj, inv_inv' hX]⟩

/-- **A simple arc has a unique winding function**. -/
@[cluster_algebras "lem_arc_winding_exists"]
theorem IsSimpleArc.existsUnique_isArcWindingFunction (hS : X.IsSimpleArc i) :
    ∃! h : X.faceOrbits → ℤ, X.IsArcWindingFunction i h := by
  change ∃! h : X.faceOrbits → ℤ, X.IsWindingFunction (X.arcCycle i) h
  rw [hS.arcCycle_eq_walkCycle hX]
  exact DiskMap.IsDiskMap.existsUnique_isWindingFunction_walkCycle hX.toIsDiskMap
    (hS.isSimpleClosedWalk_arcWalk hX)

end Walk

/-! ### The values of the winding function -/

section Values

variable {X} {i : Fin b} (hX : X.IsTripleDiagram)

include hX

private theorem exteriorDart_notMem_arcPositiveDarts (r : Fin (2 * b)) :
    X.exteriorDart r ∉ X.arcPositiveDarts i := by
  simp only [arcPositiveDarts, mem_union, mem_arc_toFinset, mem_image, not_or, not_exists,
    not_and]
  exact ⟨fun t ht h => arcDart_notMem_bdry hX ht (h ▸ exteriorDart_mem_bdry hX r),
    fun s _ h => inv_notMem_exterior hX (exteriorDart_mem_exterior hX s)
      (h ▸ exteriorDart_mem_exterior hX r)⟩

private theorem inv_exteriorDart_mem_arcPositiveDarts_iff (r : Fin (2 * b)) :
    X.inv (X.exteriorDart r) ∈ X.arcPositiveDarts i ↔ r ∈ X.rightRun i := by
  simp only [arcPositiveDarts, mem_union, mem_arc_toFinset, mem_image]
  constructor
  · rintro (⟨t, ht, h⟩ | ⟨s, hs, h⟩)
    · exact absurd (h ▸ inv_exteriorDart_mem_bdry hX r) (arcDart_notMem_bdry hX ht)
    · rwa [← exteriorDart_injective hX (X.inv.injective h)]
  · intro hr
    exact Or.inr ⟨r, hr, rfl⟩

/-- The cycle of an arc at `β_r` is `-1` for `r` in its right run and `0` otherwise. -/
theorem arcCycle_exteriorDart (r : Fin (2 * b)) :
    X.arcCycle i (X.exteriorDart r) = if r ∈ X.rightRun i then -1 else 0 := by
  rw [arcCycle, if_neg (exteriorDart_notMem_arcPositiveDarts hX r)]
  simp only [inv_exteriorDart_mem_arcPositiveDarts_iff hX]

omit hX in
/-- The cycle of an arc is `1` at its darts: `c_S(e_l) = 1`. -/
theorem arcCycle_arcDart {t : ℕ} (ht : t < X.arcLength i) : X.arcCycle i (X.arcDart i t) = 1 :=
  if_pos (mem_union_left _ (mem_arc_toFinset.2 ⟨t, ht, rfl⟩))

/-- The cycle of an arc is `-1` at the reverses of its darts: `c_S(ē_l) = -1`. -/
theorem arcCycle_inv_arcDart {t : ℕ} (ht : t < X.arcLength i) :
    X.arcCycle i (X.inv (X.arcDart i t)) = -1 := by
  have h1 : X.inv (X.arcDart i t) ∉ X.arcPositiveDarts i := by
    simp only [arcPositiveDarts, mem_union, mem_arc_toFinset, mem_image, not_or, not_exists,
      not_and]
    refine ⟨fun s hs h => ?_, fun r _ h => ?_⟩
    · have h' := congrArg X.isOut h
      rw [isOut_arcDart hX hs, isOut_inv_arcDart hX ht] at h'
      cases h'
    · exact inv_arcDart_notMem_bdry hX ht (h ▸ inv_exteriorDart_mem_bdry hX r)
  have h2 : X.arcDart i t ∈ X.arcPositiveDarts i :=
    mem_union_left _ (mem_arc_toFinset.2 ⟨t, ht, rfl⟩)
  rw [arcCycle, if_neg h1, inv_inv' hX, if_pos h2]

/-- The cycle of an arc is `1` at `β̄_r` for `r` in its right run. -/
theorem arcCycle_inv_exteriorDart {r : Fin (2 * b)} (hr : r ∈ X.rightRun i) :
    X.arcCycle i (X.inv (X.exteriorDart r)) = 1 :=
  if_pos ((inv_exteriorDart_mem_arcPositiveDarts_iff hX r).2 hr)

/-- The cycle of an arc vanishes on the darts that are neither in `B` nor on the arc. -/
theorem arcCycle_eq_zero {d : H} (hdB : d ∉ X.bdry) (hd : d ∉ X.arcDarts i) :
    X.arcCycle i d = 0 := by
  have hpos : ∀ {y}, y ∈ X.arcPositiveDarts i → y ∉ X.bdry → y ∈ X.arcDarts i := by
    intro y hy hyB
    simp only [arcPositiveDarts, mem_union, mem_image] at hy
    rcases hy with hy | ⟨r, -, rfl⟩
    · exact mem_union_left _ hy
    · exact absurd (inv_exteriorDart_mem_bdry hX r) hyB
  have h1 : d ∉ X.arcPositiveDarts i := fun h => hd (hpos h hdB)
  have h2 : X.inv d ∉ X.arcPositiveDarts i := fun h => hd (by
    simpa only [inv_inv' hX] using
      inv_mem_arcDarts hX (hpos h fun hB => hdB ((inv_mem_bdry_iff' hX).1 hB)))
  rw [arcCycle, if_neg h1, if_neg h2]

variable {h : X.faceOrbits → ℤ}

private theorem IsArcWindingFunction.walk (hS : X.IsSimpleArc i)
    (hh : X.IsArcWindingFunction i h) : X.IsWindingFunction (X.walkCycle (X.arcWalk i)) h := by
  have h' : X.IsWindingFunction (X.arcCycle i) h := hh
  rwa [hS.arcCycle_eq_walkCycle hX] at h'

private theorem IsArcWindingFunction.apply_arcDart_zero (hh : X.IsArcWindingFunction i h) :
    h (X.toFaceOrbit (X.arcDart i 0)) = -1 := by
  have ha := rightRunLength_pos (X := X) (i := i)
  set r := (finRotate (2 * b) ^ (X.rightRunLength i - 1)) (X.arcEndIndex i) with hr_def
  have hr : r ∈ X.rightRun i := finRotate_pow_mem_rightRun (by omega)
  have hrot : X.rot (X.exteriorDart r) = X.arcDart i 0 := by
    rw [rot_exteriorDart hX, hr_def, ← finRotate_pow_succ, Nat.sub_add_cancel ha,
      finRotate_pow_rightRunLength, arcDart_zero]
  have := DiskMap.IsWindingFunction.apply_rot hX.inv_involutive hh (X.exteriorDart r)
  rw [hrot, DiskMap.IsWindingFunction.apply_toFaceOrbit_of_mem_exterior hX.toIsDiskMap hh
    (exteriorDart_mem_exterior hX r), arcCycle_exteriorDart hX, if_pos hr] at this
  simpa using this

/-- **The winding function takes the values `0` and `-1`**: to the right of each dart `e_l` of a
simple arc, `h(f(e_l)) = -1`. Here `e_l = X.arcDart i t`, `t = l - 1`. -/
@[cluster_algebras "lem_arc_winding_values"]
theorem IsArcWindingFunction.apply_arcDart (hS : X.IsSimpleArc i)
    (hh : X.IsArcWindingFunction i h) {t : ℕ} (ht : t < X.arcLength i) :
    h (X.toFaceOrbit (X.arcDart i t)) = -1 := by
  have hm := arcLength_pos hX i
  have e := DiskMap.IsWindingFunction.walk_apply_eq hX.inv_involutive
    (hS.isSimpleClosedWalk_arcWalk hX) (hh.walk hX hS) ⟨t, by omega⟩ ⟨0, by omega⟩
  rw [arcWalk_of_lt ⟨t, _⟩ ht, arcWalk_of_lt ⟨0, _⟩ hm] at e
  exact e.trans (hh.apply_arcDart_zero hX)

/-- **The winding function takes the values `0` and `-1`**: to the left of each dart `e_l` of a
simple arc, `h(f(ē_l)) = 0`. Here `e_l = X.arcDart i t`, `t = l - 1`. -/
@[cluster_algebras "lem_arc_winding_values"]
theorem IsArcWindingFunction.apply_inv_arcDart (hS : X.IsSimpleArc i)
    (hh : X.IsArcWindingFunction i h) {t : ℕ} (ht : t < X.arcLength i) :
    h (X.toFaceOrbit (X.inv (X.arcDart i t))) = 0 := by
  have e := DiskMap.IsWindingFunction.walk_apply_inv (hS.isSimpleClosedWalk_arcWalk hX)
    (hh.walk hX hS) ⟨t, by omega⟩
  rw [arcWalk_of_lt ⟨t, _⟩ ht] at e
  rw [e, hh.apply_arcDart hX hS ht]
  rfl

/-- **The winding function takes the values `0` and `-1`**: every value of the winding function of
a simple arc is `-1` or `0`. -/
@[cluster_algebras "lem_arc_winding_values"]
theorem IsArcWindingFunction.apply_eq_neg_one_or_zero (hS : X.IsSimpleArc i)
    (hh : X.IsArcWindingFunction i h) (f : X.faceOrbits) : h f = -1 ∨ h f = 0 := by
  have hm := arcLength_pos hX i
  have e := DiskMap.IsWindingFunction.walk_values hX.toIsDiskMap
    (hS.isSimpleClosedWalk_arcWalk hX) (hh.walk hX hS) ⟨0, by omega⟩ f
  rw [arcWalk_of_lt ⟨0, _⟩ hm, hh.apply_arcDart_zero hX] at e
  omega

end Values

/-! ### The sides of a simple arc -/

/-- A winding function of the simple arc from `s_i`, chosen among the winding functions (it is
unique, `IsSimpleArc.existsUnique_isArcWindingFunction`); `0` if there is none. -/
noncomputable def arcWinding (i : Fin b) : X.faceOrbits → ℤ :=
  open Classical in if h : ∃ h, X.IsArcWindingFunction i h then h.choose else 0

/-- The darts on the side of the arc from `s_i` where its winding function takes the value `v`:
the darts not in `B` and not on the arc with `h(f(d)) = v`. The two sides are `v = -1`
(`rightSide`) and `v = 0` (`leftSide`). -/
@[cluster_algebras "def_arc_side"]
noncomputable def arcSide (i : Fin b) (v : ℤ) : Finset H :=
  {d | d ∉ X.bdry ∧ d ∉ X.arcDarts i ∧ X.arcWinding i (X.toFaceOrbit d) = v}

/-- The darts **on the right** `H_right(S)` of the simple arc `S` from `s_i`: the darts `d ∉ B`
that are not darts of `S` with `h(f(d)) = -1`. -/
@[cluster_algebras "def_arc_side"]
noncomputable abbrev rightSide (i : Fin b) : Finset H := X.arcSide i (-1)

/-- The darts **on the left** `H_left(S)` of the simple arc `S` from `s_i`: the darts `d ∉ B` that
are not darts of `S` with `h(f(d)) = 0`. -/
@[cluster_algebras "def_arc_side"]
noncomputable abbrev leftSide (i : Fin b) : Finset H := X.arcSide i 0

section Sides

variable {X} {i : Fin b}

/-- A dart lies on the side `v` of the arc from `s_i` iff it is not in `B`, not a dart of the
arc, and the winding function takes the value `v` on its face. -/
theorem mem_arcSide {v : ℤ} {d : H} :
    d ∈ X.arcSide i v ↔ d ∉ X.bdry ∧ d ∉ X.arcDarts i ∧ X.arcWinding i (X.toFaceOrbit d) = v := by
  simp [arcSide]

/-- The two sides of a simple arc are disjoint. -/
@[cluster_algebras "lem_arc_side_local"]
theorem disjoint_rightSide_leftSide : Disjoint (X.rightSide i) (X.leftSide i) := by
  refine disjoint_left.2 fun d h1 h2 => ?_
  have := (mem_arcSide.1 h1).2.2.symm.trans (mem_arcSide.1 h2).2.2
  omega

/-- A side of a simple arc contains no dart of the arc. -/
@[cluster_algebras "lem_arc_side_local"]
theorem disjoint_arcDarts_arcSide (v : ℤ) : Disjoint (X.arcDarts i) (X.arcSide i v) :=
  disjoint_left.2 fun _ h1 h2 => (mem_arcSide.1 h2).2.1 h1

variable (hX : X.IsTripleDiagram)

include hX

/-- For a simple arc, `arcWinding` is a winding function of the arc. -/
theorem IsSimpleArc.isArcWindingFunction_arcWinding (hS : X.IsSimpleArc i) :
    X.IsArcWindingFunction i (X.arcWinding i) := by
  have hex := (hS.existsUnique_isArcWindingFunction hX).exists
  rw [arcWinding, dif_pos hex]
  exact hex.choose_spec

/-- Any winding function of a simple arc is the chosen one. -/
theorem IsArcWindingFunction.eq_arcWinding (hS : X.IsSimpleArc i) {h : X.faceOrbits → ℤ}
    (hh : X.IsArcWindingFunction i h) : h = X.arcWinding i :=
  (hS.existsUnique_isArcWindingFunction hX).unique hh (hS.isArcWindingFunction_arcWinding hX)

/-- The sides of a simple arc may be computed with any winding function. -/
theorem IsArcWindingFunction.mem_arcSide_iff (hS : X.IsSimpleArc i) {h : X.faceOrbits → ℤ}
    (hh : X.IsArcWindingFunction i h) {v : ℤ} {d : H} :
    d ∈ X.arcSide i v ↔ d ∉ X.bdry ∧ d ∉ X.arcDarts i ∧ h (X.toFaceOrbit d) = v := by
  rw [mem_arcSide, hh.eq_arcWinding hX hS]

/-- **Local description of the sides**: the darts not in `B` are the darts of the simple arc, the
darts on its right and the darts on its left (and these sets are pairwise disjoint:
`disjoint_arcDarts_arcSide`, `disjoint_rightSide_leftSide`). -/
@[cluster_algebras "lem_arc_side_local"]
theorem IsSimpleArc.arcDarts_union_rightSide_union_leftSide (hS : X.IsSimpleArc i) :
    X.arcDarts i ∪ X.rightSide i ∪ X.leftSide i = X.bdryᶜ := by
  ext d
  rw [mem_union, mem_union, mem_compl]
  constructor
  · rintro ((h | h) | h)
    · exact notMem_bdry_of_mem_arcDarts hX h
    · exact (mem_arcSide.1 h).1
    · exact (mem_arcSide.1 h).1
  · intro hB
    by_cases hd : d ∈ X.arcDarts i
    · exact Or.inl (Or.inl hd)
    rcases (hS.isArcWindingFunction_arcWinding hX).apply_eq_neg_one_or_zero hX hS
      (X.toFaceOrbit d) with h | h
    · exact Or.inl (Or.inr (mem_arcSide.2 ⟨hB, hd, h⟩))
    · exact Or.inr (mem_arcSide.2 ⟨hB, hd, h⟩)

/-- **Local description of the sides**, (1): `d` and `d̄` lie on the same side. -/
@[cluster_algebras "lem_arc_side_local"]
theorem IsSimpleArc.inv_mem_arcSide (hS : X.IsSimpleArc i) {v : ℤ} {d : H}
    (hd : d ∈ X.arcSide i v) : X.inv d ∈ X.arcSide i v := by
  obtain ⟨hB, hA, hv⟩ := mem_arcSide.1 hd
  refine mem_arcSide.2 ⟨fun h => hB ((inv_mem_bdry_iff' hX).1 h), fun h => hA ?_, ?_⟩
  · simpa only [inv_inv' hX] using inv_mem_arcDarts hX h
  · have := (hS.isArcWindingFunction_arcWinding hX).sub_eq d
    rw [arcCycle_eq_zero hX hB hA] at this
    omega

/-- The arc darts at a vertex not passed through by the arc: none. -/
private theorem notMem_arcDarts_of_not_passesThrough {x e : H}
    (hpass : ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf x))
    (hx : X.vertexOf x ∈ X.internalVertices) (he : e ∈ X.vertexOf x) : e ∉ X.arcDarts i := by
  have hv := X.vertexOf_eq_of_mem he
  intro hA
  obtain ⟨t, ht, rfl | rfl⟩ := mem_arcDarts.1 hA
  · exact hpass ⟨hx, _, mem_arc_toFinset.2 ⟨t, ht, rfl⟩, hv⟩
  · by_cases ht' : t + 1 < X.arcLength i
    · refine hpass ⟨hx, _, mem_arc_toFinset.2 ⟨t + 1, ht', rfl⟩, ?_⟩
      rw [vertexOf_arcDart_succ hX ht', hv]
    · have hlast := runsToEndpoint_arcDart_last hX i
      rw [show X.arcLength i - 1 = t by omega] at hlast
      exact (X.mem_internalVertices.1 hx).2 (hv ▸ hlast)

/-- **Local description of the sides**, (2): all the darts of a triple point that the simple arc
does not pass through lie on the same side. -/
@[cluster_algebras "lem_arc_side_local"]
theorem IsSimpleArc.forall_mem_rightSide_or_forall_mem_leftSide (hS : X.IsSimpleArc i) {x : H}
    (hx : X.vertexOf x ∈ X.internalVertices)
    (hpass : ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf x)) :
    (∀ e ∈ X.vertexOf x, e ∈ X.rightSide i) ∨ (∀ e ∈ X.vertexOf x, e ∈ X.leftSide i) := by
  have hg := hS.isArcWindingFunction_arcWinding hX
  have hint : ¬X.IsBoundaryVertex (X.vertexOf x) := (X.mem_internalVertices.1 hx).2
  have hB : ∀ e ∈ X.vertexOf x, e ∉ X.bdry := fun e he =>
    notMem_bdry_of_internal (by rwa [X.vertexOf_eq_of_mem he])
  have hA : ∀ e ∈ X.vertexOf x, e ∉ X.arcDarts i := fun e he =>
    notMem_arcDarts_of_not_passesThrough hX hpass hx he
  have hc : ∀ e ∈ X.vertexOf x, X.arcCycle i e = 0 := fun e he =>
    arcCycle_eq_zero hX (hB e he) (hA e he)
  have hval : ∀ e ∈ X.vertexOf x,
      X.arcWinding i (X.toFaceOrbit e) = X.arcWinding i (X.toFaceOrbit x) := fun e he =>
    RotationSystem.apply_toFaceOrbit_eq_of_mem_vertexOf hX.inv_involutive hg.sub_eq hc he
  rcases hg.apply_eq_neg_one_or_zero hX hS (X.toFaceOrbit x) with h | h
  · exact Or.inl fun e he => mem_arcSide.2 ⟨hB e he, hA e he, (hval e he).trans h⟩
  · exact Or.inr fun e he => mem_arcSide.2 ⟨hB e he, hA e he, (hval e he).trans h⟩

/-- The values of the winding function around a triple point `z_{k+1}` of a simple arc. -/
private theorem arcWinding_rot_pow_inv_arcDart (hS : X.IsSimpleArc i) {k : ℕ}
    (hk : k + 1 < X.arcLength i) :
    X.arcWinding i (X.toFaceOrbit ((X.rot ^ 1) (X.inv (X.arcDart i k)))) = -1 ∧
    X.arcWinding i (X.toFaceOrbit ((X.rot ^ 2) (X.inv (X.arcDart i k)))) = -1 ∧
    X.arcWinding i (X.toFaceOrbit ((X.rot ^ 4) (X.inv (X.arcDart i k)))) = 0 ∧
    X.arcWinding i (X.toFaceOrbit ((X.rot ^ 5) (X.inv (X.arcDart i k)))) = 0 := by
  have hg := hS.isArcWindingFunction_arcWinding hX
  have hw := hS.isSimpleClosedWalk_arcWalk hX
  set y := X.inv (X.arcDart i k) with hy
  have hz : ¬X.IsBoundaryVertex (X.vertexOf y) := not_runsToEndpoint_arcDart hX hk
  have hc0 : ∀ j, j < 6 → j ≠ 0 → j ≠ 3 → X.arcCycle i ((X.rot ^ j) y) = 0 := fun j hj h0 h3 =>
    arcCycle_eq_zero hX (notMem_bdry_of_internal (by rwa [vertexOf_rot_pow']))
      (fun h => by
        rcases (hS.rot_pow_inv_arcDart_mem_arcDarts_iff hX hk hj).1 h with h | h <;> contradiction)
  have hcy : X.arcCycle i y = -1 := by
    have := hw.walkCycle_apply_inv hX.inv_involutive ⟨k, by omega⟩
    rwa [arcWalk_of_lt ⟨k, _⟩ (by simp; omega), ← hS.arcCycle_eq_walkCycle hX] at this
  have hc3 : X.arcCycle i ((X.rot ^ 3) y) = 1 := by
    have := hw.walkCycle_apply_self ⟨k + 1, by omega⟩
    rw [hy, ← arcDart_succ_eq hX hk]
    rwa [arcWalk_of_lt ⟨k + 1, _⟩ (by simpa using hk), ← hS.arcCycle_eq_walkCycle hX] at this
  have step : ∀ j, X.arcWinding i (X.toFaceOrbit ((X.rot ^ (j + 1)) y)) =
      X.arcWinding i (X.toFaceOrbit ((X.rot ^ j) y)) + X.arcCycle i ((X.rot ^ j) y) := fun j => by
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact DiskMap.IsWindingFunction.apply_rot hX.inv_involutive hg _
  have h0 : X.arcWinding i (X.toFaceOrbit ((X.rot ^ 0) y)) = 0 := by
    rw [pow_zero, Equiv.Perm.one_apply]
    exact hg.apply_inv_arcDart hX hS (by omega)
  have h1 := step 0
  rw [h0, pow_zero, Equiv.Perm.one_apply, hcy] at h1
  have h2 := step 1
  rw [h1, hc0 1 (by norm_num) (by norm_num) (by norm_num)] at h2
  have h3 := step 2
  rw [h2, hc0 2 (by norm_num) (by norm_num) (by norm_num)] at h3
  have h4 := step 3
  rw [h3, hc3] at h4
  have h5 := step 4
  rw [h4, hc0 4 (by norm_num) (by norm_num) (by norm_num)] at h5
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h4, by simpa using h5⟩

/-- **Local description of the sides**, (3): at the triple point `z_l = v(ē_l)` of a simple arc,
`σ ē_l` and `σ² ē_l` lie on the right. Here `l = k + 1`. -/
@[cluster_algebras "lem_arc_side_local"]
theorem IsSimpleArc.rot_pow_inv_arcDart_mem_rightSide (hS : X.IsSimpleArc i) {k : ℕ}
    (hk : k + 1 < X.arcLength i) :
    X.rot (X.inv (X.arcDart i k)) ∈ X.rightSide i ∧
      (X.rot ^ 2) (X.inv (X.arcDart i k)) ∈ X.rightSide i := by
  have hz : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart i k))) :=
    not_runsToEndpoint_arcDart hX hk
  obtain ⟨h1, h2, -, -⟩ := arcWinding_rot_pow_inv_arcDart hX hS hk
  rw [pow_one] at h1
  refine ⟨mem_arcSide.2 ⟨notMem_bdry_of_internal (by rwa [X.vertexOf_rot]), fun h => ?_, h1⟩,
    mem_arcSide.2 ⟨notMem_bdry_of_internal (by rwa [vertexOf_rot_pow']), fun h => ?_, h2⟩⟩
  · rcases (hS.rot_pow_inv_arcDart_mem_arcDarts_iff hX hk (j := 1) (by norm_num)).1
      (by rwa [pow_one]) with h | h <;> norm_num at h
  · rcases (hS.rot_pow_inv_arcDart_mem_arcDarts_iff hX hk (by norm_num)).1 h with h | h <;>
      norm_num at h

/-- **Local description of the sides**, (3): at the triple point `z_l = v(ē_l)` of a simple arc,
`σ⁴ ē_l` and `σ⁵ ē_l` lie on the left. Here `l = k + 1`. -/
@[cluster_algebras "lem_arc_side_local"]
theorem IsSimpleArc.rot_pow_inv_arcDart_mem_leftSide (hS : X.IsSimpleArc i) {k : ℕ}
    (hk : k + 1 < X.arcLength i) :
    (X.rot ^ 4) (X.inv (X.arcDart i k)) ∈ X.leftSide i ∧
      (X.rot ^ 5) (X.inv (X.arcDart i k)) ∈ X.leftSide i := by
  have hz : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart i k))) :=
    not_runsToEndpoint_arcDart hX hk
  obtain ⟨-, -, h4, h5⟩ := arcWinding_rot_pow_inv_arcDart hX hS hk
  refine ⟨mem_arcSide.2 ⟨notMem_bdry_of_internal (by rwa [vertexOf_rot_pow']), fun h => ?_, h4⟩,
    mem_arcSide.2 ⟨notMem_bdry_of_internal (by rwa [vertexOf_rot_pow']), fun h => ?_, h5⟩⟩
  · rcases (hS.rot_pow_inv_arcDart_mem_arcDarts_iff hX hk (by norm_num)).1 h with h | h <;>
      norm_num at h
  · rcases (hS.rot_pow_inv_arcDart_mem_arcDarts_iff hX hk (by norm_num)).1 h with h | h <;>
      norm_num at h

/-- The legs `n_r` that are darts of the arc from `s_i = ε(p)` to `ε(q)` are `n_p = e₁` and
`n_q = ē_m`. -/
theorem endDart_mem_arcDarts_iff {r : Fin (2 * b)} :
    X.endDart r ∈ X.arcDarts i ↔ r = sourceIndex i ∨ r = X.arcEndIndex i := by
  have hm := arcLength_pos hX i
  constructor
  · intro h
    have hb := isBoundaryVertex_endpoint' hX r
    obtain ⟨t, ht, e | e⟩ := mem_arcDarts.1 h
    · rcases t with _ | t
      · rw [arcDart_zero] at e
        exact Or.inl (hX.endpoint_injective (by rw [endpoint, endpoint, e]))
      · rw [e, vertexOf_arcDart_succ hX ht] at hb
        exact absurd hb (not_runsToEndpoint_arcDart hX ht)
    · by_cases ht' : t + 1 < X.arcLength i
      · rw [e] at hb
        exact absurd hb (not_runsToEndpoint_arcDart hX ht')
      · right
        rw [show t = X.arcLength i - 1 by omega, ← endDart_arcEndIndex hX] at e
        exact hX.endpoint_injective (by rw [endpoint, endpoint, e])
  · rintro (rfl | rfl)
    · exact arcDart_mem_arcDarts hm
    · rw [endDart_arcEndIndex hX]
      exact inv_arcDart_mem_arcDarts (by omega)

/-- The value of the winding function at a leg `n_r`, through `n_r = σ(β_{r-1})`. -/
private theorem arcWinding_endDart (hS : X.IsSimpleArc i) (r' : Fin (2 * b)) :
    X.arcWinding i (X.toFaceOrbit (X.endDart (finRotate (2 * b) r'))) =
      if r' ∈ X.rightRun i then -1 else 0 := by
  have hg := hS.isArcWindingFunction_arcWinding hX
  have := DiskMap.IsWindingFunction.apply_rot hX.inv_involutive hg (X.exteriorDart r')
  rwa [rot_exteriorDart hX, DiskMap.IsWindingFunction.apply_toFaceOrbit_of_mem_exterior
    hX.toIsDiskMap hg (exteriorDart_mem_exterior hX r'), arcCycle_exteriorDart hX, zero_add]
    at this

/-- **Local description of the sides**, (4): the leg `n_r` at a right position `r` lies on the
right. -/
@[cluster_algebras "lem_arc_side_local"]
theorem IsSimpleArc.endDart_mem_rightSide (hS : X.IsSimpleArc i) {r : Fin (2 * b)}
    (hr : X.IsRightPosition i r) : X.endDart r ∈ X.rightSide i := by
  obtain ⟨hq, hrun⟩ := hr
  have hrun' : ((r - X.arcEndIndex i : Fin (2 * b)) : ℕ) < X.rightRunLength i := by
    simpa [rightRun] using hrun
  have hpos : 0 < ((r - X.arcEndIndex i : Fin (2 * b)) : ℕ) :=
    Nat.pos_of_ne_zero fun h => hq (val_sub_eq_zero_iff.1 h)
  set r' := (finRotate (2 * b) ^ (((r - X.arcEndIndex i : Fin (2 * b)) : ℕ) - 1))
    (X.arcEndIndex i) with hr'
  have hrr : finRotate (2 * b) r' = r := by
    rw [hr', ← finRotate_pow_succ, Nat.sub_add_cancel hpos, finRotate_pow_val_sub]
  have hr'run : r' ∈ X.rightRun i := finRotate_pow_mem_rightRun (by omega)
  have hval := arcWinding_endDart hX hS r'
  rw [hrr, if_pos hr'run] at hval
  refine mem_arcSide.2 ⟨hX.endDart_notMem_bdry r, fun h => ?_, hval⟩
  rcases (endDart_mem_arcDarts_iff hX).1 h with h | h
  · rw [h, rightRunLength] at hrun'
    omega
  · exact hq h

/-- **Local description of the sides**, (4): the leg `n_r` at a left position `r` lies on the
left. -/
@[cluster_algebras "lem_arc_side_local"]
theorem IsSimpleArc.endDart_mem_leftSide (hS : X.IsSimpleArc i) {r : Fin (2 * b)}
    (hr : X.IsLeftPosition i r) : X.endDart r ∈ X.leftSide i := by
  obtain ⟨hp, hlt⟩ := hr
  have hpos : 0 < ((r - sourceIndex i : Fin (2 * b)) : ℕ) :=
    Nat.pos_of_ne_zero fun h => hp (val_sub_eq_zero_iff.1 h)
  have hsum := val_sub_add_val_sub (arcEndIndex_ne_sourceIndex (X := X) (i := i)).symm
  set s := ((r - sourceIndex i : Fin (2 * b)) : ℕ) with hs
  set r' := (finRotate (2 * b) ^ (s - 1 + X.rightRunLength i)) (X.arcEndIndex i) with hr'
  have hrr : finRotate (2 * b) r' = r := by
    rw [hr', ← finRotate_pow_succ, show s - 1 + X.rightRunLength i + 1 = s + X.rightRunLength i
      by omega, finRotate_pow_add, finRotate_pow_rightRunLength, hs, finRotate_pow_val_sub]
  have hr'run : r' ∉ X.rightRun i := by
    intro h
    simp only [rightRun, mem_filter, mem_univ, true_and] at h
    have hlt' : s - 1 + X.rightRunLength i < 2 * b := by
      change s - 1 + ((sourceIndex i - X.arcEndIndex i : Fin (2 * b)) : ℕ) < 2 * b
      omega
    rw [hr', val_sub_arcEndIndex hlt'] at h
    omega
  have hval := arcWinding_endDart hX hS r'
  rw [hrr, if_neg hr'run] at hval
  refine mem_arcSide.2 ⟨hX.endDart_notMem_bdry r, fun h => ?_, hval⟩
  rcases (endDart_mem_arcDarts_iff hX).1 h with h | h
  · exact hp h
  · have : s = ((X.arcEndIndex i - sourceIndex i : Fin (2 * b)) : ℕ) := by rw [hs, h]
    omega

end Sides

/-! ### Cut lists -/

/-- The **right cut list** of the simple arc `S = (e₁, …, e_m)` from `s_i = ε(p)` to `ε(q)`:
`(n_{q+1}, …, n_{p-1}, σ ē₁, σ² ē₁, …, σ ē_{m-1}, σ² ē_{m-1})`, the legs at the right positions in
clockwise order, then the darts on the right at the triple points of `S`. -/
@[cluster_algebras "def_arc_cut_list"]
def rightCutList (i : Fin b) : List H :=
  (List.range (X.rightRunLength i - 1)).map
      (fun t => X.endDart ((finRotate (2 * b) ^ (t + 1)) (X.arcEndIndex i))) ++
    (List.range (X.arcLength i - 1)).flatMap fun k =>
      [X.rot (X.inv (X.arcDart i k)), (X.rot ^ 2) (X.inv (X.arcDart i k))]

/-- The **left cut list** of the simple arc `S = (e₁, …, e_m)` from `s_i = ε(p)` to `ε(q)`:
`(n_{p+1}, …, n_{q-1}, σ⁴ ē_{m-1}, σ⁵ ē_{m-1}, …, σ⁴ ē₁, σ⁵ ē₁)`, the legs at the left positions
in clockwise order, then the darts on the left at the triple points of `S`. -/
@[cluster_algebras "def_arc_cut_list"]
def leftCutList (i : Fin b) : List H :=
  (List.range (((X.arcEndIndex i - sourceIndex i : Fin (2 * b)) : ℕ) - 1)).map
      (fun t => X.endDart ((finRotate (2 * b) ^ (t + 1)) (sourceIndex i))) ++
    (List.range (X.arcLength i - 1)).reverse.flatMap fun k =>
      [(X.rot ^ 4) (X.inv (X.arcDart i k)), (X.rot ^ 5) (X.inv (X.arcDart i k))]

section CutLists

variable {X} {i : Fin b}

/-- The members of the right cut list of the arc from `s_i`: the legs `X.endDart r` at the right
positions `r`, and the darts `σ ē_k`, `σ² ē_k` for `k + 1 < m`. -/
theorem mem_rightCutList {d : H} :
    d ∈ X.rightCutList i ↔ (∃ r, X.IsRightPosition i r ∧ d = X.endDart r) ∨
      ∃ k, k + 1 < X.arcLength i ∧
        (d = X.rot (X.inv (X.arcDart i k)) ∨ d = (X.rot ^ 2) (X.inv (X.arcDart i k))) := by
  have hlt := rightRunLength_lt (X := X) (i := i)
  simp only [rightCutList, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false]
  refine or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨_, ⟨fun h => ?_, ?_⟩, rfl⟩
    · have := congrArg (fun r : Fin (2 * b) => ((r - X.arcEndIndex i : Fin (2 * b)) : ℕ)) h
      simp only [val_sub_arcEndIndex (show t + 1 < 2 * b by omega)] at this
      rw [val_sub_eq_zero_iff.2 rfl] at this
      omega
    · exact finRotate_pow_mem_rightRun (by omega)
  · rintro ⟨r, ⟨hq, hrun⟩, rfl⟩
    have hrun' : ((r - X.arcEndIndex i : Fin (2 * b)) : ℕ) < X.rightRunLength i := by
      simpa [rightRun] using hrun
    have hpos : 0 < ((r - X.arcEndIndex i : Fin (2 * b)) : ℕ) :=
      Nat.pos_of_ne_zero fun h => hq (val_sub_eq_zero_iff.1 h)
    refine ⟨((r - X.arcEndIndex i : Fin (2 * b)) : ℕ) - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hpos, finRotate_pow_val_sub]
  · rintro ⟨k, hk, h⟩
    exact ⟨k, by omega, h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, by omega, h⟩

/-- The members of the left cut list of the arc from `s_i`: the legs `X.endDart r` at the left
positions `r`, and the darts `σ⁴ ē_k`, `σ⁵ ē_k` for `k + 1 < m`. -/
theorem mem_leftCutList {d : H} :
    d ∈ X.leftCutList i ↔ (∃ r, X.IsLeftPosition i r ∧ d = X.endDart r) ∨
      ∃ k, k + 1 < X.arcLength i ∧
        (d = (X.rot ^ 4) (X.inv (X.arcDart i k)) ∨ d = (X.rot ^ 5) (X.inv (X.arcDart i k))) := by
  have hlt := (X.arcEndIndex i - sourceIndex i).isLt
  simp only [leftCutList, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_reverse, List.mem_cons, List.not_mem_nil, or_false]
  refine or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨_, ⟨fun h => ?_, ?_⟩, rfl⟩
    · have := congrArg (fun r : Fin (2 * b) => ((r - sourceIndex i : Fin (2 * b)) : ℕ)) h
      simp only [val_finRotate_pow_sub (sourceIndex i) (show t + 1 < 2 * b by omega)] at this
      rw [val_sub_eq_zero_iff.2 rfl] at this
      omega
    · rw [val_finRotate_pow_sub (sourceIndex i) (show t + 1 < 2 * b by omega)]
      omega
  · rintro ⟨r, ⟨hp, hlt'⟩, rfl⟩
    have hpos : 0 < ((r - sourceIndex i : Fin (2 * b)) : ℕ) :=
      Nat.pos_of_ne_zero fun h => hp (val_sub_eq_zero_iff.1 h)
    refine ⟨((r - sourceIndex i : Fin (2 * b)) : ℕ) - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hpos, finRotate_pow_val_sub]
  · rintro ⟨k, hk, h⟩
    exact ⟨k, by omega, h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, by omega, h⟩

variable (hX : X.IsTripleDiagram)

include hX

/-- A dart on a side of a simple arc is a leg at a position other than `p` and `q`, a dart
`σʲ ē_l` (`j ≠ 0, 3`) at a triple point of the arc, or a dart at a triple point that the arc does
not pass through. -/
private theorem mem_arcSide_cases (hS : X.IsSimpleArc i) {v : ℤ} {d : H}
    (hd : d ∈ X.arcSide i v) :
    (∃ r, r ≠ sourceIndex i ∧ r ≠ X.arcEndIndex i ∧ d = X.endDart r) ∨
    (∃ k j, k + 1 < X.arcLength i ∧ j < 6 ∧ j ≠ 0 ∧ j ≠ 3 ∧
      d = (X.rot ^ j) (X.inv (X.arcDart i k))) ∨
    (X.vertexOf d ∈ X.internalVertices ∧ ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) := by
  obtain ⟨hB, hA, -⟩ := mem_arcSide.1 hd
  by_cases hb : X.IsBoundaryVertex (X.vertexOf d)
  · obtain ⟨r, hr⟩ := hX.exists_endpoint_eq _ (X.vertexOf_mem_boundaryVertices.2 hb)
    have hdr := eq_endDart hX hB hr.symm
    refine Or.inl ⟨r, fun h => hA ?_, fun h => hA ?_, hdr⟩ <;>
      rw [hdr] <;> exact (endDart_mem_arcDarts_iff hX).2 (by tauto)
  have hx : X.vertexOf d ∈ X.internalVertices := X.vertexOf_mem_internalVertices.2 hb
  by_cases hpass : X.PassesThrough (X.arc i).toFinset (X.vertexOf d)
  · obtain ⟨-, y, hy, hyv⟩ := hpass
    obtain ⟨t, ht, rfl⟩ := mem_arc_toFinset.1 hy
    rcases t with _ | k
    · rw [arcDart_zero] at hyv
      exact absurd (hyv ▸ isBoundaryVertex_endpoint' hX _) hb
    · rw [vertexOf_arcDart_succ hX ht] at hyv
      have hz : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart i k))) :=
        not_runsToEndpoint_arcDart hX ht
      have hmem : d ∈ X.vertexOf (X.inv (X.arcDart i k)) := by
        rw [hyv]
        exact X.self_mem_vertexOf d
      obtain ⟨j, hj, rfl⟩ := exists_rot_pow_of_mem hX hz hmem
      have h03 : ¬(j = 0 ∨ j = 3) := fun h =>
        hA ((hS.rot_pow_inv_arcDart_mem_arcDarts_iff hX ht hj).2 h)
      exact Or.inr (Or.inl ⟨k, j, ht, hj, fun h => h03 (Or.inl h), fun h => h03 (Or.inr h), rfl⟩)
  · exact Or.inr (Or.inr ⟨hx, hpass⟩)

/-- **Where the darts of a side lie**: a dart on the right of a simple arc lies in the right cut
list or at a triple point that the arc does not pass through. -/
@[cluster_algebras "lem_arc_side_darts"]
theorem IsSimpleArc.mem_rightCutList_or_of_mem_rightSide (hS : X.IsSimpleArc i) {d : H}
    (hd : d ∈ X.rightSide i) :
    d ∈ X.rightCutList i ∨
      (X.vertexOf d ∈ X.internalVertices ∧ ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) := by
  have hnl : d ∉ X.leftSide i := disjoint_left.1 disjoint_rightSide_leftSide hd
  rcases mem_arcSide_cases hX hS hd with ⟨r, hp, hq, rfl⟩ | ⟨k, j, hk, hj, h0, h3, rfl⟩ | h
  · left
    rcases isRightPosition_or_isLeftPosition hp hq with hr | hr
    · exact mem_rightCutList.2 (Or.inl ⟨r, hr, rfl⟩)
    · exact absurd (hS.endDart_mem_leftSide hX hr) hnl
  · interval_cases j
    · exact absurd rfl h0
    · exact Or.inl (mem_rightCutList.2 (Or.inr ⟨k, hk, Or.inl (pow_one X.rot ▸ rfl)⟩))
    · exact Or.inl (mem_rightCutList.2 (Or.inr ⟨k, hk, Or.inr rfl⟩))
    · exact absurd rfl h3
    · exact absurd (hS.rot_pow_inv_arcDart_mem_leftSide hX hk).1 hnl
    · exact absurd (hS.rot_pow_inv_arcDart_mem_leftSide hX hk).2 hnl
  · exact Or.inr h

/-- **Where the darts of a side lie**: a dart on the left of a simple arc lies in the left cut list
or at a triple point that the arc does not pass through. -/
@[cluster_algebras "lem_arc_side_darts"]
theorem IsSimpleArc.mem_leftCutList_or_of_mem_leftSide (hS : X.IsSimpleArc i) {d : H}
    (hd : d ∈ X.leftSide i) :
    d ∈ X.leftCutList i ∨
      (X.vertexOf d ∈ X.internalVertices ∧ ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) := by
  have hnr : d ∉ X.rightSide i := disjoint_right.1 disjoint_rightSide_leftSide hd
  rcases mem_arcSide_cases hX hS hd with ⟨r, hp, hq, rfl⟩ | ⟨k, j, hk, hj, h0, h3, rfl⟩ | h
  · left
    rcases isRightPosition_or_isLeftPosition hp hq with hr | hr
    · exact absurd (hS.endDart_mem_rightSide hX hr) hnr
    · exact mem_leftCutList.2 (Or.inl ⟨r, hr, rfl⟩)
  · interval_cases j
    · exact absurd rfl h0
    · exact absurd (by simpa using (hS.rot_pow_inv_arcDart_mem_rightSide hX hk).1) hnr
    · exact absurd (hS.rot_pow_inv_arcDart_mem_rightSide hX hk).2 hnr
    · exact absurd rfl h3
    · exact Or.inl (mem_leftCutList.2 (Or.inr ⟨k, hk, Or.inl rfl⟩))
    · exact Or.inl (mem_leftCutList.2 (Or.inr ⟨k, hk, Or.inr rfl⟩))
  · exact Or.inr h

/-- **Where the darts of a side lie**: every dart of the right cut list of a simple arc lies on its
right. -/
@[cluster_algebras "lem_arc_side_darts"]
theorem IsSimpleArc.mem_rightSide_of_mem_rightCutList (hS : X.IsSimpleArc i) {d : H}
    (hd : d ∈ X.rightCutList i) : d ∈ X.rightSide i := by
  rcases mem_rightCutList.1 hd with ⟨r, hr, rfl⟩ | ⟨k, hk, rfl | rfl⟩
  · exact hS.endDart_mem_rightSide hX hr
  · exact (hS.rot_pow_inv_arcDart_mem_rightSide hX hk).1
  · exact (hS.rot_pow_inv_arcDart_mem_rightSide hX hk).2

/-- **Where the darts of a side lie**: every dart of the left cut list of a simple arc lies on its
left. -/
@[cluster_algebras "lem_arc_side_darts"]
theorem IsSimpleArc.mem_leftSide_of_mem_leftCutList (hS : X.IsSimpleArc i) {d : H}
    (hd : d ∈ X.leftCutList i) : d ∈ X.leftSide i := by
  rcases mem_leftCutList.1 hd with ⟨r, hr, rfl⟩ | ⟨k, hk, rfl | rfl⟩
  · exact hS.endDart_mem_leftSide hX hr
  · exact (hS.rot_pow_inv_arcDart_mem_leftSide hX hk).1
  · exact (hS.rot_pow_inv_arcDart_mem_leftSide hX hk).2

/-- A side of a simple arc contains all the darts of a triple point avoided by the arc as soon as
it contains one of them. -/
private theorem mem_arcSide_of_mem_vertexOf (hS : X.IsSimpleArc i) {v : ℤ} {x e : H}
    (hx : X.vertexOf x ∈ X.internalVertices)
    (hpass : ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf x)) (hxv : x ∈ X.arcSide i v)
    (he : e ∈ X.vertexOf x) : e ∈ X.arcSide i v := by
  have hxx := X.self_mem_vertexOf x
  rcases hS.forall_mem_rightSide_or_forall_mem_leftSide hX hx hpass with h | h <;>
  · rw [(mem_arcSide.1 hxv).2.2.symm.trans (mem_arcSide.1 (h x hxx)).2.2]
    exact h e he

/-- Sides by reachability, for a side `arcSide i v` and a list `Λ` of its darts containing all its
darts at endpoints and at the triple points of the arc. -/
private theorem isLeast_arcSide (hS : X.IsSimpleArc i) {v : ℤ} {Λ : List H}
    (h₁ : ∀ d ∈ Λ, d ∈ X.arcSide i v)
    (h₂ : ∀ d ∈ X.arcSide i v, d ∈ Λ ∨
      (X.vertexOf d ∈ X.internalVertices ∧ ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d))) :
    IsLeast {K : Set H | (∀ d ∈ Λ, d ∈ K) ∧ (∀ d ∈ K, X.inv d ∈ K) ∧
      ∀ d ∈ K, X.vertexOf d ∈ X.internalVertices →
        ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d) → X.rot d ∈ K ∧ X.rot.symm d ∈ K}
      (X.arcSide i v : Set H) := by
  refine ⟨⟨fun d hd => mem_coe.2 (h₁ d hd), fun d hd => mem_coe.2 (hS.inv_mem_arcSide hX hd),
    fun d hd hx hp => ⟨mem_coe.2 (mem_arcSide_of_mem_vertexOf hX hS hx hp hd
      (X.rot_mem_vertexOf d)), mem_coe.2 (mem_arcSide_of_mem_vertexOf hX hS hx hp hd
      (X.rot_symm_mem_vertexOf d))⟩⟩, ?_⟩
  rintro K ⟨hK₁, hK₂, hK₃⟩ d hd
  by_contra hdK
  have key : ∀ y, X.Reach d y → y ∈ X.arcSide i v ∧ y ∉ K := by
    intro y hy
    induction hy with
    | refl => exact ⟨hd, hdK⟩
    | @rot y _ ih =>
      obtain ⟨hy, hyK⟩ := ih
      rcases h₂ y hy with hΛ | ⟨hx, hp⟩
      · exact absurd (hK₁ y hΛ) hyK
      refine ⟨mem_arcSide_of_mem_vertexOf hX hS hx hp hy (X.rot_mem_vertexOf y), fun h => hyK ?_⟩
      have := (hK₃ _ h (by rwa [X.vertexOf_rot]) (by rwa [X.vertexOf_rot])).2
      rwa [Equiv.symm_apply_apply] at this
    | @inv y _ ih =>
      obtain ⟨hy, hyK⟩ := ih
      refine ⟨hS.inv_mem_arcSide hX hy, fun h => hyK ?_⟩
      have := hK₂ _ h
      rwa [inv_inv' hX] at this
  have hm := arcLength_pos hX i
  have := (key _ (hX.toIsDiskMap.toIsConnected.reach d (X.arcDart i 0))).1
  exact (mem_arcSide.1 this).2.1 (arcDart_mem_arcDarts hm)

/-- **Sides by reachability**: the right side of a simple arc is the smallest set of darts
containing the right cut list and closed under `d ↦ d̄` and under `d ↦ σ^{±1}(d)` for darts `d` at
triple points through which the arc does not pass. -/
@[cluster_algebras "lem_arc_side_reach"]
theorem IsSimpleArc.isLeast_rightSide (hS : X.IsSimpleArc i) :
    IsLeast {K : Set H | (∀ d ∈ X.rightCutList i, d ∈ K) ∧ (∀ d ∈ K, X.inv d ∈ K) ∧
      ∀ d ∈ K, X.vertexOf d ∈ X.internalVertices →
        ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d) → X.rot d ∈ K ∧ X.rot.symm d ∈ K}
      (X.rightSide i : Set H) :=
  isLeast_arcSide hX hS (fun _ hd => hS.mem_rightSide_of_mem_rightCutList hX hd)
    (fun _ hd => hS.mem_rightCutList_or_of_mem_rightSide hX hd)

/-- **Sides by reachability**: the left side of a simple arc is the smallest set of darts
containing the left cut list and closed under `d ↦ d̄` and under `d ↦ σ^{±1}(d)` for darts `d` at
triple points through which the arc does not pass. -/
@[cluster_algebras "lem_arc_side_reach"]
theorem IsSimpleArc.isLeast_leftSide (hS : X.IsSimpleArc i) :
    IsLeast {K : Set H | (∀ d ∈ X.leftCutList i, d ∈ K) ∧ (∀ d ∈ K, X.inv d ∈ K) ∧
      ∀ d ∈ K, X.vertexOf d ∈ X.internalVertices →
        ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d) → X.rot d ∈ K ∧ X.rot.symm d ∈ K}
      (X.leftSide i : Set H) :=
  isLeast_arcSide hX hS (fun _ hd => hS.mem_leftSide_of_mem_leftCutList hX hd)
    (fun _ hd => hS.mem_leftCutList_or_of_mem_leftSide hX hd)

end CutLists

end TripleData

end ClusterAlgebras

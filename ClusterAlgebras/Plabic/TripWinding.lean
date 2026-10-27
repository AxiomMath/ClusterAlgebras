/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DecoratedPermutation
public import ClusterAlgebras.Plabic.Trips

/-!
# The cycle and the winding function of a trip

Let `G` be a plabic graph with `b` boundary vertices and let `i` be a label with
`j = π_G(i) ≠ i`. The one-way trip `(d₁, …, d_m)` from `i` runs from `β(i)` to `β(j)`; closing it
up with the exterior arcs from `β(j)` back to `β(i)` gives a closed walk, recorded as its *cycle*
`c_i : H → ℤ`: off the boundary darts, `c_i(d)` is `[d ∈ darts(i)] - [d̄ ∈ darts(i)]`, and on the
boundary darts it is `±1` on the exterior arcs from `β(x + 1)` to `β(x)` with `x ∈ [i, j)_b`. A
*winding function* of the trip is a function `h` on the orbits of the face permutation `φ` with
`h(f_∞) = 0` whose jump across every dart `d`, from the face `f(d)` on its right to the face
`f(d̄)` on its left, is `c_i(d)`; the faces with `h = 1` are those to the left of the trip.

A set `D` of darts off the boundary is *pendant* at a vertex `w` if it is closed under reversal
and every dart of `D` away from `w` lies at an internal vertex all of whose darts lie in `D`:
the edges of a part of the graph attached to the rest only at `w`. The trip from `i` has
*pendant self-crossings* if every edge it traverses in both directions lies in such a set whose
edges it traverses either in both directions or in neither. Then a trip that leaves a vertex `u`
along darts it will traverse again returns to `u` before it continues along new edges.

## Main definitions

* `ClusterAlgebras.PlabicData.tripCycle`: the cycle `c_i` of the one-way trip from `i`.
* `ClusterAlgebras.PlabicData.IsTripWinding`: winding functions of the one-way trip from `i`.
* `ClusterAlgebras.PlabicData.IsPendantAt`: sets of darts pendant at a vertex.
* `ClusterAlgebras.PlabicData.HasPendantSelfCrossings`: one-way trips with pendant
  self-crossings.

## Main results

* `ClusterAlgebras.PlabicData.IsPlabicGraph.vertexOf_inv_eq_of_pendant`: a trip returns from a
  pendant excursion to where it left.

## Implementation notes

* **Labels.** As throughout the chapter, the label set `[1, b]` is `Fin b`, `0`-indexed: the
  element `i : Fin b` is FWZ's label `i + 1`, FWZ's `x + 1` modulo `b` is
  `finRotate b x`, and `β(x)` is `bvertex x`.
* **Darts of a one-way trip.** FWZ's `d ∈ darts(i)` is `d ∈ G.oneWayTrip i`, and FWZ's
  `n`-th dart `d_n` (`1 ≤ n ≤ m_i`) is `T^{n-1}(g_i)`, that is
  `G.tripMap^[n - 1] (G.leg i)`.
* **Hypotheses of the definitions.** FWZ define `c_i` and its winding functions for
  `b ≥ 2` and `π_G(i) ≠ i`. `tripCycle` and `IsTripWinding` are defined for every `G` and `i`,
  with `j = π_G(i)`; they are FWZ's objects under their hypotheses.
* **Functions on the faces.** A function on the set `Φ` of orbits of `φ` is a function on the
  subtype `G.faceOrbits`; the orbit `f(d)` of `d` is `⟨G.faceOf d, G.faceOf_mem_faceOrbits d⟩`.
  The condition `h(f_∞) = 0` is stated as `h f = 0` for the orbit `f` equal to `G.exterior`, so
  that `IsTripWinding` needs no proof that the exterior is an orbit.
* **Pendant sets** are `Set H`, and `IsPendantAt w D` makes sense for any `w : Finset H`; FWZ's
  `w` is a vertex, which `HasPendantSelfCrossings` requires (`w ∈ G.vertices`).
* **The return lemma** holds without FWZ's hypothesis `π_G(i) ≠ i`, which its proof does
  not use; it is stated without it.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-! ### The cycle and the winding functions of a trip -/

/-- The **cycle** `c_i : H → ℤ` of the one-way trip from `i` (the label `i : Fin b` is FWZ's
`i + 1`), with `j = π_G(i)`. For `d ∉ B` it is `[d ∈ darts(i)] - [d̄ ∈ darts(i)]`. For
`d ∈ B` it is `1` if `d ∈ f_∞` and `v(d) = β(x + 1)` for some `x ∈ [i, j)_b`; otherwise `-1` if
`d̄ ∈ f_∞` and `v(d̄) = β(x + 1)` for some `x ∈ [i, j)_b`; and `0` otherwise. FWZ assume
`b ≥ 2` and `j ≠ i`. -/
@[cluster_algebras "def_trip_cycle"]
noncomputable def tripCycle (i : Fin b) (d : H) : ℤ :=
  if d ∉ G.bdry then
    (if d ∈ G.oneWayTrip i then 1 else 0) - if G.inv d ∈ G.oneWayTrip i then 1 else 0
  else if d ∈ G.exterior ∧
      ∃ x ∈ cyclicIco i (G.tripPerm i), G.vertexOf d = G.bvertex (finRotate b x) then 1
  else if G.inv d ∈ G.exterior ∧
      ∃ x ∈ cyclicIco i (G.tripPerm i), G.vertexOf (G.inv d) = G.bvertex (finRotate b x) then -1
  else 0

/-- A **winding function** of the one-way trip from `i`: a function `h` on the orbits of `φ` with
`h(f_∞) = 0` and `h(f(d̄)) - h(f(d)) = c_i(d)` for every dart `d`, where `f(d)` is the orbit of
`φ` containing `d`. FWZ assume `b ≥ 2` and `π_G(i) ≠ i`. -/
@[cluster_algebras "def_trip_winding"]
structure IsTripWinding (i : Fin b) (h : G.faceOrbits → ℤ) : Prop where
  /-- `h(f_∞) = 0`. -/
  eq_zero_of_eq_exterior : ∀ f : G.faceOrbits, (f : Finset H) = G.exterior → h f = 0
  /-- `h(f(d̄)) - h(f(d)) = c_i(d)` for every dart `d`. -/
  sub_eq_tripCycle : ∀ d, h ⟨G.faceOf (G.inv d), G.faceOf_mem_faceOrbits _⟩ -
    h ⟨G.faceOf d, G.faceOf_mem_faceOrbits d⟩ = G.tripCycle i d

variable {G}

/-- Off `B`, `c_i(d) = [d ∈ darts(i)] - [d̄ ∈ darts(i)]`. -/
theorem tripCycle_of_notMem_bdry {i : Fin b} {d : H} (hd : d ∉ G.bdry) :
    G.tripCycle i d =
      (if d ∈ G.oneWayTrip i then 1 else 0) - if G.inv d ∈ G.oneWayTrip i then 1 else 0 := by
  rw [tripCycle, if_pos hd]

/-- On `B`, `c_i(d)` is `1` if `d ∈ f_∞` and `v(d) = β(x + 1)` for some `x ∈ [i, j)_b`, otherwise
`-1` if `d̄ ∈ f_∞` and `v(d̄) = β(x + 1)` for some `x ∈ [i, j)_b`, and `0` otherwise. -/
theorem tripCycle_of_mem_bdry {i : Fin b} {d : H} (hd : d ∈ G.bdry) :
    G.tripCycle i d =
      if d ∈ G.exterior ∧
          ∃ x ∈ cyclicIco i (G.tripPerm i), G.vertexOf d = G.bvertex (finRotate b x) then 1
      else if G.inv d ∈ G.exterior ∧
          ∃ x ∈ cyclicIco i (G.tripPerm i), G.vertexOf (G.inv d) = G.bvertex (finRotate b x)
        then -1
      else 0 := by
  rw [tripCycle, if_neg (not_not.2 hd)]

/-- Off `B`, a dart traversed by the trip and whose reverse is not has `c_i(d) = 1`. -/
theorem tripCycle_eq_one {i : Fin b} {d : H} (hd : d ∉ G.bdry) (h₁ : d ∈ G.oneWayTrip i)
    (h₂ : G.inv d ∉ G.oneWayTrip i) : G.tripCycle i d = 1 := by
  simp [tripCycle_of_notMem_bdry hd, h₁, h₂]

/-- Off `B`, a dart traversed by the trip in both directions has `c_i(d) = 0`. -/
theorem tripCycle_eq_zero_of_mem_of_inv_mem {i : Fin b} {d : H} (hd : d ∉ G.bdry)
    (h₁ : d ∈ G.oneWayTrip i) (h₂ : G.inv d ∈ G.oneWayTrip i) : G.tripCycle i d = 0 := by
  simp [tripCycle_of_notMem_bdry hd, h₁, h₂]

/-! ### Pendant sets and pendant self-crossings -/

variable (G)

/-- A set `D` of darts is **pendant at** `w`: `D ⊆ H \ B`, `d̄ ∈ D` for every `d ∈ D`, and every
`d ∈ D` with `v(d) ≠ w` lies at an internal vertex all of whose darts lie in `D`. FWZ
take `w` a vertex of `G`. -/
@[cluster_algebras "def_pendant_dart_set"]
structure IsPendantAt (w : Finset H) (D : Set H) : Prop where
  /-- `D ⊆ H \ B`. -/
  notMem_bdry : ∀ d ∈ D, d ∉ G.bdry
  /-- `D` is closed under reversal. -/
  inv_mem : ∀ d ∈ D, G.inv d ∈ D
  /-- A dart of `D` away from `w` lies at an internal vertex. -/
  vertexOf_mem_internalVertices : ∀ d ∈ D, G.vertexOf d ≠ w → G.vertexOf d ∈ G.internalVertices
  /-- All darts at the vertex of a dart of `D` away from `w` lie in `D`. -/
  mem_of_mem_vertexOf : ∀ d ∈ D, G.vertexOf d ≠ w → ∀ e ∈ G.vertexOf d, e ∈ D

/-- The one-way trip from `i` has **pendant self-crossings** (the label `i : Fin b` is FWZ's
`i + 1`): for every dart `x` with `x, x̄ ∈ darts(i)` there are a vertex `w` of `G` and a
set `D` pendant at `w` with `x ∈ D` such that `y ∈ darts(i)` if and only if `ȳ ∈ darts(i)`, for
every `y ∈ D`. -/
@[cluster_algebras "def_pendant_self_crossings"]
def HasPendantSelfCrossings (i : Fin b) : Prop :=
  ∀ x ∈ G.oneWayTrip i, G.inv x ∈ G.oneWayTrip i →
    ∃ w ∈ G.vertices, ∃ D : Set H, G.IsPendantAt w D ∧ x ∈ D ∧
      ∀ y ∈ D, (y ∈ G.oneWayTrip i ↔ G.inv y ∈ G.oneWayTrip i)

variable {G}

/-! ### Returning from a pendant excursion -/

/-- The dart `T^t(g_i)` is a dart of the one-way trip from `i` when `t < m_i`. -/
theorem iterate_mem_oneWayTrip {i : Fin b} {t : ℕ} (ht : t < G.tripLength i) :
    G.tripMap^[t] (G.leg i) ∈ G.oneWayTrip i :=
  mem_oneWayTrip.2 ⟨t, ht, rfl⟩

/-- The dart `T^{t+1}(g_i)` lies at the vertex `v(T^t(g_i)‾)`. -/
theorem iterate_succ_mem_vertexOf_inv (i : Fin b) (t : ℕ) :
    G.tripMap^[t + 1] (G.leg i) ∈ G.vertexOf (G.inv (G.tripMap^[t] (G.leg i))) := by
  rw [Function.iterate_succ_apply']
  exact turn_mem_vertexOf _

/-- **A trip returns from a pendant excursion to where it left.** Write `d_t = T^{t-1}(g_i)`, so
that `(d₁, …, d_m)` is the one-way trip from `i`, and suppose it has pendant self-crossings. Let
`1 ≤ k < n < m` with `d̄_k ∉ darts(i)`, `d̄_{n+1} ∉ darts(i)` and `d̄_t ∈ darts(i)` for
`t ∈ [k + 1, n]`. Then `v(d̄_n) = v(d̄_k)`. -/
@[cluster_algebras "lem_trip_run_return"]
theorem IsPlabicGraph.vertexOf_inv_eq_of_pendant (hG : G.IsPlabicGraph) {i : Fin b}
    (hP : G.HasPendantSelfCrossings i) {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (hnm : n < G.tripLength i)
    (hdk : G.inv (G.tripMap^[k - 1] (G.leg i)) ∉ G.oneWayTrip i)
    (hdn : G.inv (G.tripMap^[n] (G.leg i)) ∉ G.oneWayTrip i)
    (hrun : ∀ t, k < t → t ≤ n → G.inv (G.tripMap^[t - 1] (G.leg i)) ∈ G.oneWayTrip i) :
    G.vertexOf (G.inv (G.tripMap^[n - 1] (G.leg i))) =
      G.vertexOf (G.inv (G.tripMap^[k - 1] (G.leg i))) := by
  -- Work with `0`-indexed darts `e t = T^t(g_i)`, `k₀ = k - 1`, `n₀ = n - 1`.
  set e : ℕ → H := fun t => G.tripMap^[t] (G.leg i) with he
  obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
  obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hdk hdn hrun ⊢
  change G.inv (e k₀) ∉ G.oneWayTrip i at hdk
  change G.inv (e (n₀ + 1)) ∉ G.oneWayTrip i at hdn
  change G.vertexOf (G.inv (e n₀)) = G.vertexOf (G.inv (e k₀))
  have hrun' : ∀ t, k₀ < t → t ≤ n₀ → G.inv (e t) ∈ G.oneWayTrip i := by
    intro t h₁ h₂
    have := hrun (t + 1) (by omega) (by omega)
    simpa using this
  have hmem : ∀ t, t < G.tripLength i → e t ∈ G.oneWayTrip i := fun t ht =>
    iterate_mem_oneWayTrip ht
  have hstep : ∀ t, e (t + 1) ∈ G.vertexOf (G.inv (e t)) := fun t =>
    iterate_succ_mem_vertexOf_inv i t
  set u := G.vertexOf (G.inv (e k₀)) with hu
  -- `n₁` is the largest `t ∈ [k₀, n₀]` with `v(ē_t) = u`.
  let P : ℕ → Prop := fun t => k₀ ≤ t ∧ G.vertexOf (G.inv (e t)) = u
  set n₁ := Nat.findGreatest P n₀ with hn₁
  have hPn₁ : P n₁ := Nat.findGreatest_spec (P := P) (m := k₀) (by omega) ⟨le_rfl, rfl⟩
  have hn₁le : n₁ ≤ n₀ := Nat.findGreatest_le n₀
  have hgr : ∀ t, n₁ < t → t ≤ n₀ → G.vertexOf (G.inv (e t)) ≠ u := fun t h₁ h₂ hv =>
    Nat.findGreatest_is_greatest h₁ h₂ ⟨by omega, hv⟩
  rcases hn₁le.lt_or_eq with hlt | heq
  · exfalso
    -- The dart `e (n₁ + 1)` lies at `u` and is traversed in both directions.
    have hat : G.vertexOf (e (n₁ + 1)) = u := by
      rw [G.vertexOf_eq_of_mem (hstep n₁), hPn₁.2]
    obtain ⟨w, -, D, hD, hxD, hDiff⟩ := hP (e (n₁ + 1)) (hmem _ (by omega))
      (hrun' _ (by omega) (by omega))
    by_cases hw : G.vertexOf (e (n₁ + 1)) = w
    · -- `w = u`: the trip stays in `D` until `e (n₀ + 1)`.
      have hin : ∀ s, s ≤ n₀ - n₁ → e (n₁ + 1 + s) ∈ D := by
        intro s
        induction s with
        | zero => intro _; simpa using hxD
        | succ s ih =>
          intro hs
          have hD' := ih (by omega)
          have hz : G.vertexOf (G.inv (e (n₁ + 1 + s))) ≠ w := by
            rw [← hw, hat]
            exact hgr _ (by omega) (by omega)
          have := hD.mem_of_mem_vertexOf _ (hD.inv_mem _ hD') hz _ (hstep (n₁ + 1 + s))
          simpa [Nat.add_assoc] using this
      have hlast := hin (n₀ - n₁) le_rfl
      rw [show n₁ + 1 + (n₀ - n₁) = n₀ + 1 by omega] at hlast
      exact hdn ((hDiff _ hlast).1 (hmem _ hnm))
    · -- `w ≠ u`: all darts of `u` lie in `D`, among them `ē_{k₀}`.
      have hk : G.inv (e k₀) ∈ D :=
        hD.mem_of_mem_vertexOf _ hxD hw _ (by rw [hat]; exact G.self_mem_vertexOf _)
      have hk' : e k₀ ∈ D := by
        have := hD.inv_mem _ hk
        rwa [hG.inv_involutive] at this
      exact hdk ((hDiff _ hk').1 (hmem _ (by omega)))
  · rw [← heq]
    exact hPn₁.2

end PlabicData

end ClusterAlgebras

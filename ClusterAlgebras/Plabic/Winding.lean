/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CycleSpace

/-!
# Winding functions of simple closed walks

Let `M = (H, d ↦ d̄, σ, B)` be a disk map, with face permutation `φ = σ ∘ (d ↦ d̄)` and orbit
`f(d)` of `φ` through a dart `d`. For a function `c : H → ℤ`, a *winding function* is a function
`h` on the set `Φ` of orbits of `φ` with `h(f_∞) = 0` and `h(f(d̄)) - h(f(d)) = c(d)` for every
dart. Since `f(σ d) = f(d̄)`, such a function changes by `c(d)` when one turns from `d` to `σ d`
around a vertex (the *rotation rule*).

A *simple closed walk* is a cyclic sequence of darts `c₁, …, c_L` with `v(c̄ᵢ) = v(cᵢ₊₁)`,
`cᵢ₊₁ ≠ c̄ᵢ` and pairwise distinct vertices `v(cᵢ)`. Its cycle `c_C` is `1` on the darts `cᵢ`, `-1`
on their reverses and `0` elsewhere; it has exactly one winding function, which is constant, equal
to `λ`, on the orbits `f(cᵢ)` to the right of the walk, equal to `λ + 1` on the orbits `f(c̄ᵢ)` to
its left, and takes only the values `λ` and `λ + 1`. This is the combinatorial substitute for the
Jordan curve theorem in the parity arguments of Thurston's theory of triple diagrams: a strand
leaving the side of a closed walk on which the winding function is nonzero must come back to the
walk, and the nonzero side of a closed walk nested in another one is smaller.

## Main definitions

* `ClusterAlgebras.RotationSystem.IsSimpleClosedWalk`, `ClusterAlgebras.RotationSystem.walkCycle`,
  `ClusterAlgebras.DiskMap.IsWindingFunction`: simple closed walks, their cycles and winding
  functions.

## Main results

* `ClusterAlgebras.RotationSystem.apply_toFaceOrbit_rot`: the rotation rule.
* `ClusterAlgebras.RotationSystem.IsSimpleClosedWalk.walkCycle_apply_self`, `walkCycle_apply_inv`,
  `eq_of_vertexOf_eq`, `eq_of_vertexOf_inv_eq` and
  `ClusterAlgebras.RotationSystem.walkCycle_eq_zero`: the cycle of a simple closed walk.
* `ClusterAlgebras.DiskMap.IsDiskMap.existsUnique_isWindingFunction_walkCycle`: a simple closed
  walk has a unique winding function.
* `ClusterAlgebras.DiskMap.IsWindingFunction.walk_apply_eq`, `walk_apply_inv`: the two sides of a
  simple closed walk.
* `ClusterAlgebras.DiskMap.IsWindingFunction.walk_values`: a simple closed walk has two winding
  values.
* `ClusterAlgebras.DiskMap.IsWindingFunction.apply_eq_zero_of_isBoundaryVertex`: winding values at
  the endpoints.
* `ClusterAlgebras.DiskMap.IsWindingFunction.exists_walk_escape`: walking away from the inside of a
  closed walk.
* `ClusterAlgebras.DiskMap.IsWindingFunction.ssubset_of_nested`: nested closed walks.

## Implementation notes

* A walk `c₁, …, c_L` is a function `w : Fin L → H`, `0`-indexed: `w i` is FWZ's `c_{i+1}`,
  and the index `i + 1` modulo `L` is `finRotate L i`. Simple closed walks and their cycles are
  defined for rotation systems, of which disk maps are a special case.
* A winding function is a function `h : M.faceOrbits → ℤ` on the subtype `Φ` of orbits; the orbit
  `f(d)` is `M.toFaceOrbit d`. The normalisation `h(f_∞) = 0` is stated as `h f = 0` for the orbit
  `f` whose set of darts is the exterior, which needs no proof that the exterior is an orbit.
* The statements about the two sides and the two values of a winding function are stated relative
  to an arbitrary dart `cᵢ` of the walk rather than to `c₁`, and the hypothesis of the nesting
  lemma singles out an arbitrary vertex `v(c_{i₀})` instead of `v(c₁)`; these are FWZ's
  statements after a cyclic relabelling of the walk.
* The lemma on endpoints is proved for a disk map, its endpoints being the boundary vertices, and
  only needs the cycle to vanish at the darts of the endpoint considered. The escape lemma is
  stated for a disk map, its triple points being the internal vertices; FWZ's assumption
  that the value `ε` is one of `h(f(c₁))`, `h(f(c̄₁))` is not needed and is omitted. The darts
  `k₁, …, k_i` are `k 0, …, k n` for a sequence `k : ℕ → H` and `n = i - 1`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-- **Induction around a cycle**: a property of the indices `Fin L` that holds at `i₀` and passes
from `i` to `i + 1` (modulo `L`) whenever `i + 1 ≠ i₀` holds everywhere. -/
theorem finRotate_induction {L : ℕ} {P : Fin L → Prop} (i₀ : Fin L) (h0 : P i₀)
    (hstep : ∀ i, finRotate L i ≠ i₀ → P i → P (finRotate L i)) (i : Fin L) : P i := by
  open Fin.NatCast in
  cases L with
  | zero => exact i₀.elim0
  | succ n =>
    have key : ∀ k : ℕ, k ≤ n → P (i₀ + (k : Fin (n + 1))) := by
      intro k hk
      induction k with
      | zero => simpa using h0
      | succ k ih =>
        have h := hstep (i₀ + (k : Fin (n + 1))) ?_ (ih (by omega))
        · rwa [finRotate_apply, add_assoc, ← Nat.cast_add_one] at h
        · rw [finRotate_apply, add_assoc, ← Nat.cast_add_one]
          intro h
          have h' : ((k + 1 : ℕ) : Fin (n + 1)) = 0 := by simpa using congrArg (· - i₀) h
          rw [Fin.natCast_eq_zero] at h'
          have := Nat.le_of_dvd (by omega) h'
          omega
    simpa using key (i - i₀).val (by omega)

namespace RotationSystem

variable {H : Type*} [Fintype H] [DecidableEq H] (R : RotationSystem H)

/-! ### The rotation rule -/

/-- A dart `e` lies in the vertex `v(d)` if and only if `v(e) = v(d)`. -/
theorem mem_vertexOf_iff_vertexOf_eq {d e : H} :
    e ∈ R.vertexOf d ↔ R.vertexOf e = R.vertexOf d :=
  ⟨R.vertexOf_eq_of_mem, fun h => h ▸ R.self_mem_vertexOf e⟩

/-- For every `n`, the dart `σ^n d` lies in the vertex `v(d)`. -/
theorem rot_pow_apply_mem_vertexOf (n : ℕ) (d : H) : (R.rot ^ n) d ∈ R.vertexOf d :=
  R.mem_vertexOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))

/-- When `d ↦ d̄` is an involution, `f(σ d) = f(d̄)`, as `σ d = φ(d̄)`. -/
theorem toFaceOrbit_rot (hinv : Function.Involutive R.inv) (d : H) :
    R.toFaceOrbit (R.rot d) = R.toFaceOrbit (R.inv d) := by
  rw [← R.toFaceOrbit_facePerm (R.inv d), facePerm_apply, hinv d]

variable {R}

/-- **The rotation rule for winding functions**: if `h(f(d̄)) - h(f(d)) = c(d)` for every dart
`d`, then `h(f(σ d)) = h(f(d)) + c(d)` for every dart. Only the involutivity of `d ↦ d̄` is used,
and the values may lie in any additive group. -/
@[cluster_algebras "lem_winding_rotation_rule"]
theorem apply_toFaceOrbit_rot {G : Type*} [AddCommGroup G] (hinv : Function.Involutive R.inv)
    {c : H → G} {h : R.faceOrbits → G}
    (hh : ∀ d, h (R.toFaceOrbit (R.inv d)) - h (R.toFaceOrbit d) = c d) (d : H) :
    h (R.toFaceOrbit (R.rot d)) = h (R.toFaceOrbit d) + c d := by
  rw [R.toFaceOrbit_rot hinv, ← hh d]
  abel

/-- Iterating the rotation rule: if `c` vanishes at `σ^j x` for `j < n`, then `h(f(σ^n x)) =
h(f(x))`. -/
theorem apply_toFaceOrbit_rot_pow {G : Type*} [AddCommGroup G] (hinv : Function.Involutive R.inv)
    {c : H → G} {h : R.faceOrbits → G}
    (hh : ∀ d, h (R.toFaceOrbit (R.inv d)) - h (R.toFaceOrbit d) = c d) {x : H} {n : ℕ}
    (hc : ∀ j < n, c ((R.rot ^ j) x) = 0) :
    h (R.toFaceOrbit ((R.rot ^ n) x)) = h (R.toFaceOrbit x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, apply_toFaceOrbit_rot hinv hh, hc n (by omega), add_zero]
    exact ih fun j hj => hc j (by omega)

/-- If `c` vanishes at every dart of the vertex `v(x)`, then `h ∘ f` is constant on `v(x)`. -/
theorem apply_toFaceOrbit_eq_of_mem_vertexOf {G : Type*} [AddCommGroup G]
    (hinv : Function.Involutive R.inv) {c : H → G} {h : R.faceOrbits → G}
    (hh : ∀ d, h (R.toFaceOrbit (R.inv d)) - h (R.toFaceOrbit d) = c d) {x e : H}
    (hc : ∀ d ∈ R.vertexOf x, c d = 0) (he : e ∈ R.vertexOf x) :
    h (R.toFaceOrbit e) = h (R.toFaceOrbit x) := by
  obtain ⟨n, rfl⟩ := ((R.mem_vertexOf).1 he).exists_nat_pow_eq
  exact apply_toFaceOrbit_rot_pow hinv hh fun j _ => hc _ (R.rot_pow_apply_mem_vertexOf j x)

/-! ### Simple closed walks and their cycles -/

variable (R) in
/-- A **simple closed walk** `C = (c₁, …, c_L)`, `L ≥ 1`: with indices modulo `L`,
`v(c̄ᵢ) = v(cᵢ₊₁)` and `cᵢ₊₁ ≠ c̄ᵢ` for every `i`, and the vertices `v(c₁), …, v(c_L)` are pairwise
distinct. The walk is `w : Fin L → H`, `0`-indexed (`w i` is `c_{i+1}`), and `i + 1` modulo `L` is
`finRotate L i`. -/
@[cluster_algebras "def_closed_walk"]
structure IsSimpleClosedWalk {L : ℕ} (w : Fin L → H) : Prop where
  /-- The walk has at least one dart. -/
  pos : 0 < L
  /-- Consecutive darts are linked: `v(c̄ᵢ) = v(cᵢ₊₁)`. -/
  vertexOf_inv : ∀ i, R.vertexOf (R.inv (w i)) = R.vertexOf (w (finRotate L i))
  /-- The walk does not turn back: `cᵢ₊₁ ≠ c̄ᵢ`. -/
  ne_inv : ∀ i, w (finRotate L i) ≠ R.inv (w i)
  /-- The vertices `v(cᵢ)` are pairwise distinct. -/
  injective_vertexOf : Function.Injective fun i => R.vertexOf (w i)

omit [Fintype H] in
variable (R) in
/-- The **cycle** of a walk: `c_C(d) = |{i : cᵢ = d}| - |{i : cᵢ = d̄}|`. -/
@[cluster_algebras "def_closed_walk"]
def walkCycle {L : ℕ} (w : Fin L → H) (d : H) : ℤ :=
  (#{i | w i = d} : ℤ) - #{i | w i = R.inv d}

omit [Fintype H] in
/-- When `d ↦ d̄` is an involution, the cycle of a walk satisfies `c_C(d̄) = -c_C(d)`. -/
theorem walkCycle_inv (hinv : Function.Involutive R.inv) {L : ℕ} (w : Fin L → H) (d : H) :
    R.walkCycle w (R.inv d) = -R.walkCycle w d := by
  simp only [walkCycle, hinv d]
  ring

/-- The cycle of a closed walk sums to zero at every vertex. -/
theorem sum_walkCycle (hinv : Function.Involutive R.inv) {L : ℕ} {w : Fin L → H}
    (hw : ∀ i, R.vertexOf (R.inv (w i)) = R.vertexOf (w (finRotate L i))) (x : H) :
    ∑ d ∈ R.vertexOf x, R.walkCycle w d = 0 := by
  have key : ∀ d, R.walkCycle w d =
      ∑ i, ((if w i = d then (1 : ℤ) else 0) - if R.inv (w i) = d then 1 else 0) := by
    intro d
    have hiff : ∀ i, (R.inv (w i) = d ↔ w i = R.inv d) := fun i =>
      ⟨fun h => by rw [← h, hinv], fun h => by rw [h, hinv]⟩
    rw [sum_sub_distrib, walkCycle]
    simp only [hiff, card_filter]
    push_cast
    rfl
  simp only [key]
  rw [sum_comm]
  simp only [sum_sub_distrib, sum_ite_eq]
  have hmem : ∀ i, (R.inv (w i) ∈ R.vertexOf x ↔ w (finRotate L i) ∈ R.vertexOf x) := by
    intro i
    rw [mem_vertexOf_iff_vertexOf_eq, mem_vertexOf_iff_vertexOf_eq, hw]
  simp only [hmem]
  rw [Equiv.sum_comp (finRotate L) (fun i => if w i ∈ R.vertexOf x then (1 : ℤ) else 0), sub_self]

omit [Fintype H] in
/-- **The cycle of a simple closed walk**: `c_C` vanishes on the darts that are neither some `cᵢ`
nor some `c̄ᵢ`. -/
@[cluster_algebras "lem_walk_cycle_values"]
theorem walkCycle_eq_zero (hinv : Function.Involutive R.inv) {L : ℕ} {w : Fin L → H} {d : H}
    (h₁ : ∀ i, d ≠ w i) (h₂ : ∀ i, d ≠ R.inv (w i)) : R.walkCycle w d = 0 := by
  have e2 : ∀ k, w k ≠ R.inv d := fun k h => h₂ k (by rw [h, hinv])
  simp [walkCycle, fun k => (h₁ k).symm, e2]

omit [Fintype H] in
/-- A dart on which the cycle of a walk is nonzero is a dart of the walk or the reverse of
one. -/
theorem exists_of_walkCycle_ne_zero (hinv : Function.Involutive R.inv) {L : ℕ} {w : Fin L → H}
    {d : H} (hd : R.walkCycle w d ≠ 0) : ∃ i, d = w i ∨ d = R.inv (w i) := by
  by_contra hne
  push Not at hne
  exact hd (walkCycle_eq_zero hinv (fun i => (hne i).1) fun i => (hne i).2)

namespace IsSimpleClosedWalk

variable {L : ℕ} {w : Fin L → H} (hw : R.IsSimpleClosedWalk w)

include hw

/-- The darts of a simple closed walk are pairwise distinct. -/
theorem injective : Function.Injective w := fun i j h =>
  hw.injective_vertexOf (by simp only [h])

/-- No dart of a simple closed walk is the reverse of a dart of the walk. -/
theorem ne_inv_apply (i j : Fin L) : w i ≠ R.inv (w j) := by
  intro h
  have h1 : R.vertexOf (w i) = R.vertexOf (w (finRotate L j)) := by rw [h, hw.vertexOf_inv]
  have h2 : i = finRotate L j := hw.injective_vertexOf h1
  exact hw.ne_inv j (h2 ▸ h)

/-- **The cycle of a simple closed walk**: `c_C(cᵢ) = 1`. -/
@[cluster_algebras "lem_walk_cycle_values"]
theorem walkCycle_apply_self (i : Fin L) : R.walkCycle w (w i) = 1 := by
  have h1 : ({k | w k = w i} : Finset (Fin L)) = {i} := by
    ext k
    simp [hw.injective.eq_iff]
  have h2 : ({k | w k = R.inv (w i)} : Finset (Fin L)) = ∅ := by
    ext k
    simp [hw.ne_inv_apply k i]
  simp [walkCycle, h1, h2]

/-- **The cycle of a simple closed walk**: `c_C(c̄ᵢ) = -1`. -/
@[cluster_algebras "lem_walk_cycle_values"]
theorem walkCycle_apply_inv (hinv : Function.Involutive R.inv) (i : Fin L) :
    R.walkCycle w (R.inv (w i)) = -1 := by
  rw [walkCycle_inv hinv, hw.walkCycle_apply_self]

/-- **The cycle of a simple closed walk**: the only dart `cⱼ` at the vertex `v(cᵢ₊₁)` is
`cᵢ₊₁`. -/
@[cluster_algebras "lem_walk_cycle_values"]
theorem eq_of_vertexOf_eq {i j : Fin L} (h : R.vertexOf (w j) = R.vertexOf (w (finRotate L i))) :
    j = finRotate L i :=
  hw.injective_vertexOf h

/-- **The cycle of a simple closed walk**: the only dart `c̄ⱼ` at the vertex `v(cᵢ₊₁)` is
`c̄ᵢ`. -/
@[cluster_algebras "lem_walk_cycle_values"]
theorem eq_of_vertexOf_inv_eq {i j : Fin L}
    (h : R.vertexOf (R.inv (w j)) = R.vertexOf (w (finRotate L i))) : j = i :=
  (finRotate L).injective (hw.injective_vertexOf ((hw.vertexOf_inv j).symm.trans h))

/-- The cycle of a simple closed walk vanishes at every vertex that is not a vertex of the walk. -/
theorem walkCycle_eq_zero_of_vertexOf_ne (hinv : Function.Involutive R.inv) {d : H}
    (hd : ∀ i, R.vertexOf d ≠ R.vertexOf (w i)) : R.walkCycle w d = 0 := by
  refine walkCycle_eq_zero hinv (fun i h => hd i (by rw [h])) fun i h => ?_
  apply hd (finRotate L i)
  rw [h, hw.vertexOf_inv]

end IsSimpleClosedWalk

end RotationSystem

/-! ### Winding functions -/

namespace DiskMap

variable {H : Type*} [Fintype H] [DecidableEq H] (M : DiskMap H)

/-- A **winding function** of a function `c : H → ℤ` (in practice the cycle `c_C` of a simple
closed walk): a function `h : Φ → ℤ` on the orbits of `φ` with `h(f_∞) = 0` and
`h(f(d̄)) - h(f(d)) = c(d)` for every dart `d`. -/
@[cluster_algebras "def_closed_walk"]
structure IsWindingFunction (c : H → ℤ) (h : M.faceOrbits → ℤ) : Prop where
  /-- `h(f_∞) = 0`. -/
  apply_exterior : ∀ f : M.faceOrbits, (f : Finset H) = M.exterior → h f = 0
  /-- `h(f(d̄)) - h(f(d)) = c(d)`. -/
  sub_eq : ∀ d, h (M.toFaceOrbit (M.inv d)) - h (M.toFaceOrbit d) = c d

variable {M}

/-- In a disk map, the orbit of a dart of the exterior is the exterior. -/
theorem IsDiskMap.faceOf_eq_exterior (hM : M.IsDiskMap) {d : H}
    (hd : d ∈ M.exterior) : M.faceOf d = M.exterior := by
  obtain ⟨d₀, hd₀⟩ := M.mem_faceOrbits.1 hM.exterior_mem_faceOrbits
  rw [← hd₀] at hd ⊢
  exact M.faceOf_eq_of_mem hd

namespace IsWindingFunction

variable {c : H → ℤ} {h : M.faceOrbits → ℤ}

/-- A winding function vanishes on the orbit of every dart of the exterior. -/
theorem apply_toFaceOrbit_of_mem_exterior (hM : M.IsDiskMap) (hh : M.IsWindingFunction c h)
    {d : H} (hd : d ∈ M.exterior) : h (M.toFaceOrbit d) = 0 :=
  hh.apply_exterior _ (hM.faceOf_eq_exterior hd)

/-- A function `c` has at most one winding function. -/
theorem unique (hM : M.IsDiskMap) {h' : M.faceOrbits → ℤ} (hh : M.IsWindingFunction c h)
    (hh' : M.IsWindingFunction c h') : h = h' := by
  funext f
  have := hM.toIsConnected.eq_of_forall_inv (h := fun f => h f - h' f) (fun d => by
    linarith [hh.sub_eq d, hh'.sub_eq d]) f ⟨M.exterior, hM.exterior_mem_faceOrbits⟩
  simp only [hh.apply_exterior ⟨M.exterior, hM.exterior_mem_faceOrbits⟩ rfl,
    hh'.apply_exterior ⟨M.exterior, hM.exterior_mem_faceOrbits⟩ rfl] at this
  linarith

/-- The rotation rule for a winding function: `h(f(σ d)) = h(f(d)) + c(d)`. -/
theorem apply_rot (hinv : Function.Involutive M.inv) (hh : M.IsWindingFunction c h) (d : H) :
    h (M.toFaceOrbit (M.rot d)) = h (M.toFaceOrbit d) + c d :=
  RotationSystem.apply_toFaceOrbit_rot hinv hh.sub_eq d

end IsWindingFunction

/-- **A simple closed walk has a unique winding function**. Only the linking condition
`v(c̄ᵢ) = v(cᵢ₊₁)` of the walk is used. -/
@[cluster_algebras "lem_walk_winding_exists"]
theorem IsDiskMap.existsUnique_isWindingFunction_walkCycle (hM : M.IsDiskMap) {L : ℕ}
    {w : Fin L → H} (hw : M.IsSimpleClosedWalk w) :
    ∃! h : M.faceOrbits → ℤ, M.IsWindingFunction (M.walkCycle w) h := by
  obtain ⟨h, ⟨h0, hh⟩, -⟩ := hM.existsUnique_faceFunction (M.walkCycle w)
    (fun d => M.walkCycle_inv hM.inv_involutive w d) (fun v hv => by
      obtain ⟨x, rfl⟩ := M.mem_vertices.1 hv
      exact M.sum_walkCycle hM.inv_involutive hw.vertexOf_inv x)
  have hw' : M.IsWindingFunction (M.walkCycle w) h :=
    ⟨fun f hf => by rw [show f = ⟨M.exterior, hM.exterior_mem_faceOrbits⟩ from Subtype.ext hf, h0],
      hh⟩
  exact ⟨h, hw', fun h' hh' => hh'.unique hM hw'⟩

namespace IsWindingFunction

variable {L : ℕ} {w : Fin L → H} {h : M.faceOrbits → ℤ}

/-- **The two sides of a simple closed walk**, left side: `h(f(c̄ᵢ)) = h(f(cᵢ)) + 1`. -/
@[cluster_algebras "lem_walk_winding_sides"]
theorem walk_apply_inv (hw : M.IsSimpleClosedWalk w) (hh : M.IsWindingFunction (M.walkCycle w) h)
    (i : Fin L) : h (M.toFaceOrbit (M.inv (w i))) = h (M.toFaceOrbit (w i)) + 1 := by
  linarith [hh.sub_eq (w i), hw.walkCycle_apply_self i]

/-- A winding function of a simple closed walk takes the same value on the right of two
consecutive darts: `h(f(cᵢ₊₁)) = h(f(cᵢ))`. -/
theorem walk_apply_finRotate (hinv : Function.Involutive M.inv) (hw : M.IsSimpleClosedWalk w)
    (hh : M.IsWindingFunction (M.walkCycle w) h) (i : Fin L) :
    h (M.toFaceOrbit (w (finRotate L i))) = h (M.toFaceOrbit (w i)) := by
  classical
  have hex : ∃ k, (M.rot ^ k) (M.rot (M.inv (w i))) = M.inv (w i) ∨
      (M.rot ^ k) (M.rot (M.inv (w i))) = w (finRotate L i) := by
    obtain ⟨k, hk⟩ := (Equiv.Perm.sameCycle_apply_left.2
      (Equiv.Perm.SameCycle.refl M.rot (M.inv (w i)))).exists_nat_pow_eq
    exact ⟨k, Or.inl hk⟩
  have hzero : ∀ j < Nat.find hex, M.walkCycle w ((M.rot ^ j) (M.rot (M.inv (w i)))) = 0 := by
    intro j hj
    obtain ⟨hna, hnb⟩ := not_or.1 (Nat.find_min hex hj)
    have hmem :
        M.vertexOf ((M.rot ^ j) (M.rot (M.inv (w i)))) = M.vertexOf (w (finRotate L i)) := by
      have := M.rot_pow_apply_mem_vertexOf j (M.rot (M.inv (w i)))
      rw [RotationSystem.vertexOf_rot] at this
      rw [M.vertexOf_eq_of_mem this, hw.vertexOf_inv]
    refine RotationSystem.walkCycle_eq_zero hinv (fun k hk => ?_) fun k hk => ?_
    · rw [hk] at hmem hnb
      exact hnb (by rw [hw.eq_of_vertexOf_eq hmem])
    · rw [hk] at hmem hna
      exact hna (by rw [hw.eq_of_vertexOf_inv_eq hmem])
  have hrot := RotationSystem.apply_toFaceOrbit_rot_pow hinv hh.sub_eq hzero
  have h1 := hh.apply_rot hinv (M.inv (w i))
  rw [hw.walkCycle_apply_inv hinv] at h1
  have h2 := walk_apply_inv hw hh i
  rcases Nat.find_spec hex with he | he <;> rw [he] at hrot <;> linarith

/-- **The two sides of a simple closed walk**, right side: a winding function takes the same value
on the orbits `f(cᵢ)` of all the darts of the walk. -/
@[cluster_algebras "lem_walk_winding_sides"]
theorem walk_apply_eq (hinv : Function.Involutive M.inv) (hw : M.IsSimpleClosedWalk w)
    (hh : M.IsWindingFunction (M.walkCycle w) h) (i j : Fin L) :
    h (M.toFaceOrbit (w i)) = h (M.toFaceOrbit (w j)) :=
  finRotate_induction (P := fun i => h (M.toFaceOrbit (w i)) = h (M.toFaceOrbit (w j))) j rfl
    (fun k _ hk => by rw [hh.walk_apply_finRotate hinv hw k, hk]) i

/-- **A simple closed walk has two winding values**: with `λ = h(f(cᵢ))`, every value of the
winding function is `λ` or `λ + 1`. -/
@[cluster_algebras "lem_walk_winding_values"]
theorem walk_values (hM : M.IsDiskMap) (hw : M.IsSimpleClosedWalk w)
    (hh : M.IsWindingFunction (M.walkCycle w) h) (i : Fin L) (f : M.faceOrbits) :
    h f = h (M.toFaceOrbit (w i)) ∨ h f = h (M.toFaceOrbit (w i)) + 1 := by
  have hinv := hM.inv_involutive
  obtain ⟨e, rfl⟩ := M.toFaceOrbit_surjective f
  set lam := h (M.toFaceOrbit (w i))
  have step : ∀ y, (h (M.toFaceOrbit y) = lam ∨ h (M.toFaceOrbit y) = lam + 1) →
      (h (M.toFaceOrbit (M.inv y)) = lam ∨ h (M.toFaceOrbit (M.inv y)) = lam + 1) := by
    intro y hy
    by_cases hc : M.walkCycle w y = 0
    · have := hh.sub_eq y
      omega
    · obtain ⟨k, rfl | rfl⟩ := RotationSystem.exists_of_walkCycle_ne_zero hinv hc
      · right
        rw [hh.walk_apply_inv hw k, hh.walk_apply_eq hinv hw k i]
      · left
        rw [hinv, hh.walk_apply_eq hinv hw k i]
  induction hM.toIsConnected.reach (w i) e with
  | refl => exact Or.inl rfl
  | @rot y _ ih =>
    rw [M.toFaceOrbit_rot hinv]
    exact step y ih
  | @inv y _ ih => exact step y ih

/-- **Winding values at the endpoints**: if `h` is a winding function of `c` (`h(f_∞) = 0` and
`h(f(d̄)) - h(f(d)) = c(d)`) and `c` vanishes at every dart of the boundary vertex `v(d)` (for a
triple diagram, the endpoint of `d`), then `h(f(d)) = 0`. -/
@[cluster_algebras "lem_leg_winding_zero"]
theorem apply_eq_zero_of_isBoundaryVertex (hM : M.IsDiskMap) {c : H → ℤ}
    (hh : M.IsWindingFunction c h) {d : H} (hd : M.IsBoundaryVertex (M.vertexOf d))
    (hc : ∀ e ∈ M.vertexOf d, c e = 0) : h (M.toFaceOrbit d) = 0 := by
  have hdeg := hM.boundaryVertex_card
  obtain ⟨h3, h2⟩ := hdeg _ (M.vertexOf_mem_boundaryVertices.2 hd)
  have h1 : ((M.vertexOf d).filter (· ∉ M.bdry)).card = 1 := by
    have := card_filter_add_card_filter_not (s := M.vertexOf d) (· ∈ M.bdry)
    omega
  obtain ⟨g, hg⟩ := card_eq_one.1 h1
  obtain ⟨hgv, hgB⟩ := mem_filter.1 (hg ▸ mem_singleton_self g)
  have hvg : M.vertexOf g = M.vertexOf d := M.vertexOf_eq_of_mem hgv
  have hev : M.rot.symm g ∈ M.vertexOf d := by
    rw [← hvg]
    exact M.rot_symm_mem_vertexOf g
  have heB : M.rot.symm g ∈ M.bdry := by
    by_contra heB
    have h' := congrArg M.rot (eq_of_notMem_bdry hdeg hd hev hgv heB hgB)
    rw [Equiv.apply_symm_apply] at h'
    exact rot_ne_of_isBoundaryVertex hdeg (x := g) (by rwa [hvg]) h'.symm
  have hext : M.rot.symm g ∈ M.exterior :=
    M.mem_exterior.2 ⟨heB, by rwa [Equiv.apply_symm_apply]⟩
  rw [← RotationSystem.apply_toFaceOrbit_eq_of_mem_vertexOf hM.inv_involutive hh.sub_eq hc hev]
  exact hh.apply_toFaceOrbit_of_mem_exterior hM hext

/-- A winding function of a simple closed walk takes the same value on both sides of a dart that
is neither a dart of the walk nor the reverse of one. -/
theorem apply_inv_eq_of_forall_ne (hinv : Function.Involutive M.inv)
    (hh : M.IsWindingFunction (M.walkCycle w) h) {x : H} (hx : ∀ i, x ≠ w i ∧ x ≠ M.inv (w i)) :
    h (M.toFaceOrbit (M.inv x)) = h (M.toFaceOrbit x) := by
  linarith [hh.sub_eq x,
    RotationSystem.walkCycle_eq_zero hinv (fun i => (hx i).1) fun i => (hx i).2]

/-- If a dart `x` is off a simple closed walk and its reverse ends at a vertex not on the walk,
then every dart `y` at that vertex is off the walk and has the winding value of `x`. -/
theorem escape_step (hinv : Function.Involutive M.inv) (hw : M.IsSimpleClosedWalk w)
    (hh : M.IsWindingFunction (M.walkCycle w) h) {x y : H} (hx : ∀ i, x ≠ w i ∧ x ≠ M.inv (w i))
    (hnot : ∀ i, M.vertexOf (M.inv x) ≠ M.vertexOf (w i)) (hy : y ∈ M.vertexOf (M.inv x)) :
    (∀ i, y ≠ w i ∧ y ≠ M.inv (w i)) ∧ h (M.toFaceOrbit y) = h (M.toFaceOrbit x) := by
  have hv := M.vertexOf_eq_of_mem hy
  have hvert : ∀ e ∈ M.vertexOf (M.inv x), M.walkCycle w e = 0 := fun e he =>
    hw.walkCycle_eq_zero_of_vertexOf_ne hinv (by rwa [M.vertexOf_eq_of_mem he])
  refine ⟨fun i => ⟨fun heq => hnot i ?_, fun heq => hnot (finRotate L i) ?_⟩, ?_⟩
  · rw [← hv, heq]
  · rw [← hv, heq, hw.vertexOf_inv]
  · rw [RotationSystem.apply_toFaceOrbit_eq_of_mem_vertexOf hinv hh.sub_eq hvert hy,
      hh.apply_inv_eq_of_forall_ne hinv hx]

/-- **Walking away from the inside of a closed walk**. Let `C = (c₁, …, c_L)` be a simple closed
walk of a disk map all of whose vertices are internal (for a triple diagram: triple points), `h`
its winding function, `ε ≠ 0`, and `k₁` a dart at a vertex of `C` that is neither a dart of `C` nor
the reverse of one, with `h(f(k₁)) = ε`. Then there are darts `k₁, …, k_i` such that for `j < i`
the vertex `v(k̄ⱼ)` is internal and not a vertex of `C`, and `kⱼ₊₁ = σ³(k̄ⱼ)`, the vertex `v(k̄ᵢ)`
is a vertex of `C`, and every `kⱼ` is neither a dart of `C` nor the reverse of one and satisfies
`h(f(kⱼ)) = ε`. Here `k j` is `k_{j+1}` and `n = i - 1`. -/
@[cluster_algebras "lem_walk_escape"]
theorem exists_walk_escape (hM : M.IsDiskMap) (hw : M.IsSimpleClosedWalk w)
    (hint : ∀ i, ¬M.IsBoundaryVertex (M.vertexOf (w i)))
    (hh : M.IsWindingFunction (M.walkCycle w) h) {ε : ℤ} (hε : ε ≠ 0) {k₁ : H}
    (hk₁ : ∃ i, M.vertexOf k₁ = M.vertexOf (w i)) (hk₁C : ∀ i, k₁ ≠ w i ∧ k₁ ≠ M.inv (w i))
    (hk₁h : h (M.toFaceOrbit k₁) = ε) :
    ∃ (n : ℕ) (k : ℕ → H), k 0 = k₁ ∧
      (∀ j < n, ¬M.IsBoundaryVertex (M.vertexOf (M.inv (k j))) ∧
        (∀ i, M.vertexOf (M.inv (k j)) ≠ M.vertexOf (w i)) ∧
        k (j + 1) = (M.rot ^ 3) (M.inv (k j))) ∧
      (∃ i, M.vertexOf (M.inv (k n)) = M.vertexOf (w i)) ∧
      ∀ j ≤ n, (∀ i, k j ≠ w i ∧ k j ≠ M.inv (w i)) ∧ h (M.toFaceOrbit (k j)) = ε := by
  classical
  have hinv := hM.inv_involutive
  let T : Equiv.Perm H := M.rot ^ 3 * M.inv
  let k : ℕ → H := fun j => (T ^ j) k₁
  have hk0 : k 0 = k₁ := by simp [k]
  have hksucc : ∀ j, k (j + 1) = (M.rot ^ 3) (M.inv (k j)) := fun j => by
    simp only [k, pow_succ', Equiv.Perm.mul_apply, T]
  have hmem : ∀ j, k (j + 1) ∈ M.vertexOf (M.inv (k j)) := fun j => by
    rw [hksucc]
    exact M.rot_pow_apply_mem_vertexOf 3 _
  let Q : ℕ → Prop := fun j => ¬M.IsBoundaryVertex (M.vertexOf (M.inv (k j))) ∧
      ∀ i, M.vertexOf (M.inv (k j)) ≠ M.vertexOf (w i)
  have hex : ∃ j, ¬Q j := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨m, hm⟩ : ∃ m, orderOf T = m + 1 := ⟨orderOf T - 1, by have := orderOf_pos T; omega⟩
    have hkm : k (m + 1) = k₁ := by
      simp only [k]
      rw [← hm, pow_orderOf_eq_one, Equiv.Perm.one_apply]
    obtain ⟨i, hi⟩ := hk₁
    apply (hall m).2 i
    rw [← hi, ← hkm, M.vertexOf_eq_of_mem (hmem m)]
  have hQ : ∀ j < Nat.find hex, Q j := fun j hj => not_not.1 (Nat.find_min hex hj)
  have hprop : ∀ j ≤ Nat.find hex,
      (∀ i, k j ≠ w i ∧ k j ≠ M.inv (w i)) ∧ h (M.toFaceOrbit (k j)) = ε := by
    intro j hj
    induction j with
    | zero => exact hk0 ▸ ⟨hk₁C, hk₁h⟩
    | succ j ih =>
      obtain ⟨hC, hval⟩ := ih (by omega)
      obtain ⟨hC', hv⟩ := hh.escape_step hinv hw hC (hQ j (by omega)).2 (hmem j)
      exact ⟨hC', hv.trans hval⟩
  refine ⟨Nat.find hex, k, hk0, fun j hj => ⟨(hQ j hj).1, (hQ j hj).2, hksucc j⟩, ?_, hprop⟩
  have hn := Nat.find_spec hex
  obtain ⟨hC, hval⟩ := hprop _ le_rfl
  by_contra hno
  push Not at hno
  apply hn
  refine ⟨fun hb => hε ?_, hno⟩
  rw [← hval, ← hh.apply_inv_eq_of_forall_ne hinv hC]
  refine hh.apply_eq_zero_of_isBoundaryVertex hM hb fun e he =>
    hw.walkCycle_eq_zero_of_vertexOf_ne hinv fun i hi => hint i ?_
  rwa [← hi, M.vertexOf_eq_of_mem he]

/-- Replacing a winding function `h_N` of `N` by the constant `κ` on the zero set of `h_C`, where
`h_N` equals `κ` on both sides of every dart of `C`, and then subtracting `κ`, gives a winding
function of `N`. -/
private theorem ite_sub (hinv : Function.Involutive M.inv) {L' : ℕ} {C : Fin L → H}
    {N : Fin L' → H} {gC gN : M.faceOrbits → ℤ} (hgN : M.IsWindingFunction (M.walkCycle N) gN)
    (hgC : M.IsWindingFunction (M.walkCycle C) gC) {κ : ℤ}
    (hκC : ∀ i, gN (M.toFaceOrbit (C i)) = κ) (hκC' : ∀ i, gN (M.toFaceOrbit (M.inv (C i))) = κ)
    (hcN0 : ∀ d, (gC (M.toFaceOrbit d) = 0 ∨ gC (M.toFaceOrbit (M.inv d)) = 0) →
      M.walkCycle N d = 0) :
    M.IsWindingFunction (M.walkCycle N) (fun f => (if gC f = 0 then κ else gN f) - κ) := by
  refine ⟨fun f hf => by simp [hgC.apply_exterior f hf], fun d => ?_⟩
  by_cases hA : gC (M.toFaceOrbit d) = 0 <;> by_cases hB : gC (M.toFaceOrbit (M.inv d)) = 0
  · rw [if_pos hA, if_pos hB, hcN0 d (Or.inl hA)]
    ring
  · have hcC : M.walkCycle C d ≠ 0 := by
      rwa [← hgC.sub_eq d, hA, sub_zero]
    rw [if_pos hA, if_neg hB, hcN0 d (Or.inl hA)]
    obtain ⟨i, rfl | rfl⟩ := RotationSystem.exists_of_walkCycle_ne_zero hinv hcC
    · rw [hκC']
      ring
    · rw [hinv, hκC]
      ring
  · have hcC : M.walkCycle C d ≠ 0 := by
      rwa [← hgC.sub_eq d, hB, zero_sub, neg_ne_zero]
    rw [if_neg hA, if_pos hB, hcN0 d (Or.inr hB)]
    obtain ⟨i, rfl | rfl⟩ := RotationSystem.exists_of_walkCycle_ne_zero hinv hcC
    · rw [hκC]
      ring
    · rw [hκC']
      ring
  · rw [if_neg hA, if_neg hB, ← hgN.sub_eq d]
    ring

/-- **Nested closed walks**. Let `C = (c₁, …, c_L)` and `N` be simple closed walks of a disk map
with winding functions `h_C` and `h_N`. Suppose that `h_C(f(d)) ≠ 0` and `h_C(f(d̄)) ≠ 0` for every
dart `d` of `N`, and that no vertex of `C` other than `v(c_{i₀})` is a vertex of `N`. Then the set
of orbits on which `h_N` is nonzero is a proper subset of the set of orbits on which `h_C` is
nonzero. -/
@[cluster_algebras "lem_winding_nested"]
theorem ssubset_of_nested (hM : M.IsDiskMap) {L' : ℕ} {C : Fin L → H} {N : Fin L' → H}
    (hC : M.IsSimpleClosedWalk C) (hN : M.IsSimpleClosedWalk N) {gC gN : M.faceOrbits → ℤ}
    (hgC : M.IsWindingFunction (M.walkCycle C) gC) (hgN : M.IsWindingFunction (M.walkCycle N) gN)
    (hdarts : ∀ j, gC (M.toFaceOrbit (N j)) ≠ 0 ∧ gC (M.toFaceOrbit (M.inv (N j))) ≠ 0)
    (i₀ : Fin L) (hvert : ∀ i ≠ i₀, ∀ j, M.vertexOf (C i) ≠ M.vertexOf (N j)) :
    {f | gN f ≠ 0} ⊂ {f | gC f ≠ 0} := by
  have hinv := hM.inv_involutive
  set lam := gC (M.toFaceOrbit (C i₀))
  have hCi : ∀ i, gC (M.toFaceOrbit (C i)) = lam := fun i => hgC.walk_apply_eq hinv hC i i₀
  have hCi' : ∀ i, gC (M.toFaceOrbit (M.inv (C i))) = lam + 1 := fun i => by
    rw [hgC.walk_apply_inv hC i, hCi i]
  have h0 : 0 = lam ∨ 0 = lam + 1 := by
    have := hgC.walk_values hM hC i₀ ⟨M.exterior, hM.exterior_mem_faceOrbits⟩
    rwa [hgC.apply_exterior ⟨M.exterior, hM.exterior_mem_faceOrbits⟩ rfl] at this
  have hcN0 : ∀ d, (gC (M.toFaceOrbit d) = 0 ∨ gC (M.toFaceOrbit (M.inv d)) = 0) →
      M.walkCycle N d = 0 := by
    intro d hd
    by_contra hne
    obtain ⟨j, rfl | rfl⟩ := RotationSystem.exists_of_walkCycle_ne_zero hinv hne
    · exact hd.elim (hdarts j).1 (hdarts j).2
    · rw [hinv] at hd
      exact hd.elim (hdarts j).2 (hdarts j).1
  have hCN : ∀ i, M.walkCycle N (C i) = 0 := fun i =>
    hcN0 _ (by rw [hCi, hCi']; omega)
  have hstep1 : ∀ i, gN (M.toFaceOrbit (M.inv (C i))) = gN (M.toFaceOrbit (C i)) := fun i => by
    linarith [hgN.sub_eq (C i), hCN i]
  have hstep2 : ∀ i, finRotate L i ≠ i₀ →
      gN (M.toFaceOrbit (C (finRotate L i))) = gN (M.toFaceOrbit (M.inv (C i))) := by
    intro i hi
    refine RotationSystem.apply_toFaceOrbit_eq_of_mem_vertexOf hinv hgN.sub_eq (fun e he => ?_)
      ((M.mem_vertexOf_iff_vertexOf_eq).2 (hC.vertexOf_inv i).symm)
    refine hN.walkCycle_eq_zero_of_vertexOf_ne hinv fun j hj => hvert _ hi j ?_
    rw [← hj, M.vertexOf_eq_of_mem he, hC.vertexOf_inv]
  set κ := gN (M.toFaceOrbit (C i₀))
  have hκC : ∀ i, gN (M.toFaceOrbit (C i)) = κ := fun i =>
    finRotate_induction (P := fun i => gN (M.toFaceOrbit (C i)) = κ) i₀ rfl
      (fun i hi hP => by rw [hstep2 i hi, hstep1 i, hP]) i
  have hκC' : ∀ i, gN (M.toFaceOrbit (M.inv (C i))) = κ := fun i => by rw [hstep1, hκC]
  have huniq := (hgN.ite_sub hinv hgC hκC hκC' hcN0).unique hM hgN
  obtain ⟨f₁, hf₁C, hf₁N⟩ : ∃ f₁, gC f₁ ≠ 0 ∧ gN f₁ = κ := by
    rcases h0 with h0 | h0
    · exact ⟨_, by rw [hCi']; omega, hκC' i₀⟩
    · exact ⟨_, by rw [hCi]; omega, hκC i₀⟩
  have hκ0 : κ = 0 := by
    have := congrFun huniq f₁
    simp only [if_neg hf₁C] at this
    linarith
  have hZ : ∀ f, gC f = 0 → gN f = 0 := fun f hf => by
    have := congrFun huniq f
    simp only [if_pos hf] at this
    linarith
  have hsub : {f | gN f ≠ 0} ⊆ {f | gC f ≠ 0} := fun f hf hC0 => hf (hZ f hC0)
  rw [Set.ssubset_iff_of_subset hsub]
  exact ⟨f₁, hf₁C, fun h => h (hf₁N.trans hκ0)⟩

end IsWindingFunction

end DiskMap

end ClusterAlgebras

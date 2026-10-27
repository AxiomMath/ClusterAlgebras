/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CoreMoves
public import ClusterAlgebras.Plabic.FlipMoves

/-!
# Trivalent resolutions and flips

A *trivalent resolution* of a plabic graph `X` whose internal vertices have at least three darts is
a trivalent plabic graph reached from `X` by repeatedly undoing contractions of edges
(`ClusterAlgebras.PlabicGraph.IsResolution`). Each step of a resolution splits an internal vertex
`z` with `k` darts along a *diagonal*: the splitting from a dart `s` of `z` of size
`p ∈ [2, k - 2]` replaces `z` by two vertices with `p + 1` and `k - p + 1` darts.

Moves between plabic graphs lift to their resolutions. A flip at an edge of `X` commutes with the
splitting of a vertex with at least four darts away from the edge, so by induction on the excess
`∑_v (|v| - 3)` some resolutions of `X` and of its flip are joined by flips; the same holds for
square moves. Any two resolutions of `X` are joined by flips: two splittings of `X` at distinct
vertices commute, two splittings along nested arcs of one vertex have a common splitting, the
splitting from `s` of size `p` is the splitting from `σ^p(s)` of size `k - p`, and at a vertex with
four darts the two splittings are exchanged by a flip. Consequently trivalent plabic graphs that
are related by moves (M2) and (M3) are related by flips: project a move sequence onto resolutions.

A plabic graph without internal leaves can be made trivalent by moves (M2) and (M3) without
creating internal leaves: remove the bivalent vertices, then pass to a resolution. Finally, a
square move at a face whose four vertices lie in the core commutes with taking skeletons.

## Main results

* `ClusterAlgebras.PlabicGraph.exists_isResolution_flipMove`: a flip lifts to resolutions.
* `ClusterAlgebras.PlabicGraph.IsResolution.trivalentConnected`: any two resolutions are
  related by flips.
* `ClusterAlgebras.PlabicGraph.exists_trivalent_of_forall_not_isInternalLeaf`: a plabic graph
  without internal leaves can be made trivalent.
* `ClusterAlgebras.PlabicGraph.MoveEquivalent.trivalentConnected`: moves (M2) and (M3) between
  trivalent graphs are flips.
* `ClusterAlgebras.PlabicData.IsSquareMoveFace.skeleton`: a square move at core vertices commutes
  with the skeleton.
* `ClusterAlgebras.PlabicGraph.exists_isResolution_squareMove`: a square move lifts to
  resolutions.

## Implementation notes

* **Excess.** The inductions use the dart-weighted excess `∑_x (|v(x)| - 3)`, the sum over the
  darts `x` at internal vertices, in place of the excess `ex(X) = ∑_v (|v| - 3)` of [FWZ]. It also
  drops under every splitting along a diagonal, and the base cases are handled by trivalence
  directly.
* **Equality as isomorphism.** Two splittings of a graph live on `(H ⊕ Fin 2) ⊕ Fin 2`; the
  equalities of [FWZ] between them are isomorphisms exchanging the names of the new darts of the
  inner and of the outer splitting. The splitting from `s` of size `p` and the one from `σ^p(s)` of
  size `k - p` are isomorphic by exchanging the two new darts `n` and `n̄`.
* **Diagonals.** The case analysis of [FWZ] on pairs of diagonals of a vertex `z` (equal,
  non-crossing, crossing) is organised as follows: the splitting from `s` of size `p` and the one
  from `s` of size `2` have a common splitting (nested arcs with a common first dart); the
  splittings of size `2` from consecutive darts `s`, `σ(s)` are exchanged by a flip when `k = 4`,
  and for `k ≥ 5` are joined through the splittings from `s` of size `3` and from `σ^3(s)` of sizes
  `k - 3` and `k - 2`. These relations connect any two splittings of `z`.
* **Anchoring.** [FWZ] states `ClusterAlgebras.PlabicData.IsSquareMoveFace.skeleton` for anchored
  graphs, which makes the skeleton a plabic graph; the statement holds without that hypothesis,
  which is dropped.
* **Labels.** The labels `[1, b]` are `Fin b`, `0`-indexed.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm Function

/-! ### Orbits of permutations -/

section Orbits

variable {X : Type*}

/-- A set mapped into itself by a permutation of a finite set contains the cycles of its
elements. -/
private theorem mem_of_sameCycle_of_mapsTo [Finite X] {σ : Perm X} {A : Set X}
    (hA : ∀ a ∈ A, σ a ∈ A) {x y : X} (hx : x ∈ A) (h : σ.SameCycle x y) : y ∈ A := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact hA _ ih

section Period

variable [Fintype X] [DecidableEq X]

private theorem card_orbit_eq_minimalPeriod (σ : Perm X) (x : X) :
    ({y | σ.SameCycle x y} : Finset X).card = minimalPeriod σ x := by
  have h : ({y | σ.SameCycle x y} : Finset X) =
      (range (minimalPeriod σ x)).image fun i => (σ ^ i) x := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
    constructor
    · intro hy
      obtain ⟨n, rfl⟩ := hy.exists_nat_pow_eq
      refine ⟨n % minimalPeriod σ x,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (MulAction.minimalPeriod_pos σ x).out), ?_⟩
      rw [← Perm.iterate_eq_pow, ← Perm.iterate_eq_pow, iterate_mod_minimalPeriod_eq]
    · rintro ⟨i, -, rfl⟩
      exact sameCycle_pow_right.2 (SameCycle.refl _ _)
  rw [h, card_image_of_injOn, card_range]
  intro i hi j hj hij
  exact iterate_injOn_Iio_minimalPeriod (f := σ) (x := x) (by simpa using hi) (by simpa using hj)
    (by simpa [Perm.iterate_eq_pow] using hij)

/-- `σ^k(x) = x` for `k` the number of elements of the orbit of `x`. -/
private theorem pow_card_orbit_apply (σ : Perm X) (x : X) :
    (σ ^ ({y | σ.SameCycle x y} : Finset X).card) x = x := by
  rw [card_orbit_eq_minimalPeriod, ← Perm.iterate_eq_pow, iterate_minimalPeriod]

/-- The elements `σ^i(x)`, `i < k`, of the orbit of `x` are distinct. -/
private theorem eq_of_pow_apply_eq_of_lt (σ : Perm X) (x : X) {i j : ℕ}
    (hi : i < ({y | σ.SameCycle x y} : Finset X).card)
    (hj : j < ({y | σ.SameCycle x y} : Finset X).card) (h : (σ ^ i) x = (σ ^ j) x) : i = j := by
  rw [card_orbit_eq_minimalPeriod] at hi hj
  exact iterate_injOn_Iio_minimalPeriod (f := σ) (x := x) hi hj
    (by simpa [Perm.iterate_eq_pow] using h)

/-- Every element of the orbit of `x` is `σ^i(x)` for some `i` less than the size of the orbit. -/
private theorem exists_pow_lt_card_of_sameCycle (σ : Perm X) {x y : X} (h : σ.SameCycle x y) :
    ∃ i < ({y | σ.SameCycle x y} : Finset X).card, (σ ^ i) x = y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  refine ⟨n % minimalPeriod σ x, ?_, ?_⟩
  · rw [card_orbit_eq_minimalPeriod]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero (MulAction.minimalPeriod_pos σ x).out)
  · rw [← Perm.iterate_eq_pow, ← Perm.iterate_eq_pow, iterate_mod_minimalPeriod_eq]

/-- An orbit with three elements is the `3`-cycle `(x σx σ²x)`. -/
private theorem three_cycle_of_card {σ : Perm X} {x : X}
    (h : ({y | σ.SameCycle x y} : Finset X).card = 3) :
    σ (σ (σ x)) = x ∧ x ≠ σ x ∧ x ≠ σ (σ x) ∧ σ x ≠ σ (σ x) ∧
      ∀ y, σ.SameCycle x y → y = x ∨ y = σ x ∨ y = σ (σ x) := by
  have hp : ∀ i : ℕ, (σ ^ i) x = σ^[i] x := fun i => (congrFun (Perm.iterate_eq_pow σ i) x).symm
  have h3 := pow_card_orbit_apply σ x
  rw [h, hp] at h3
  have hne : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → σ^[i] x ≠ σ^[j] x := fun i j hi hj hij e =>
    hij (eq_of_pow_apply_eq_of_lt σ x (by omega) (by omega) (by rwa [hp, hp]))
  refine ⟨h3, hne 0 1 (by norm_num) (by norm_num) (by norm_num),
    hne 0 2 (by norm_num) (by norm_num) (by norm_num),
    hne 1 2 (by norm_num) (by norm_num) (by norm_num), fun y hy => ?_⟩
  obtain ⟨i, hi, rfl⟩ := exists_pow_lt_card_of_sameCycle σ hy
  rw [h] at hi
  rw [hp]
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end Period

end Orbits

/-- A finite set of darts containing `d`, mapped into itself by the rotation, and all of whose
darts lie in the orbit of `d`, is the vertex of `d`. -/
private theorem vertexOf_eq_of_closed {H : Type*} [Fintype H] [DecidableEq H]
    {R : RotationSystem H} {d : H} {A : Finset H} (hA : ∀ a ∈ A, R.rot a ∈ A) (hdA : d ∈ A)
    (hreach : ∀ a ∈ A, R.rot.SameCycle d a) : R.vertexOf d = A := by
  ext y
  rw [RotationSystem.mem_vertexOf]
  constructor
  · intro h
    exact mem_of_sameCycle_of_mapsTo (A := (A : Set H)) hA hdA h
  · exact hreach y

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

/-! ### The two new vertices of a splitting -/

section SplitVertices

variable (K : PlabicData H b) (s : H) (p : ℕ)

/-- The rotation of a splitting along the first new vertex `(n x_1 … x_p)`. -/
private theorem rot_vertexSplit_inl_pow_of_lt (hpk : p ≤ (K.vertexOf s).card) {j : ℕ}
    (hj : j < p) :
    (K.vertexSplit s p).rot (Sum.inl ((K.rot ^ j) s)) =
      if j + 1 = p then Sum.inr 0 else Sum.inl ((K.rot ^ (j + 1)) s) := by
  have hk : p ≤ ({y | K.rot.SameCycle s y} : Finset H).card := hpk
  rw [rot_vertexSplit, splitRot_inl_pow K.rot s p hk (by omega)]
  by_cases h : j + 1 = p
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg (by omega)]

/-- The rotation of a splitting along the second new vertex `(n̄ x_{p+1} … x_k)`. -/
private theorem rot_vertexSplit_inl_pow_of_le (hpk : p ≤ (K.vertexOf s).card) {j : ℕ}
    (hpj : p ≤ j) (hj : j < (K.vertexOf s).card) :
    (K.vertexSplit s p).rot (Sum.inl ((K.rot ^ j) s)) =
      if j + 1 = (K.vertexOf s).card then Sum.inr 1 else Sum.inl ((K.rot ^ (j + 1)) s) := by
  have hk : p ≤ ({y | K.rot.SameCycle s y} : Finset H).card := hpk
  rw [rot_vertexSplit, splitRot_inl_pow K.rot s p hk hj, if_neg (by omega)]
  rfl

/-- The first new vertex of a splitting from `s` of size `p ∈ [1, k]` is `(n x_1 … x_p)`, where
`x_{j+1} = σ^j(s)`. -/
private theorem vertexOf_vertexSplit_inr_zero (hp : 1 ≤ p) (hpk : p ≤ (K.vertexOf s).card) :
    (K.vertexSplit s p).vertexOf (Sum.inr 0) =
      insert (Sum.inr 0) ((range p).image fun j => Sum.inl ((K.rot ^ j) s)) := by
  have r0 : (K.vertexSplit s p).rot (Sum.inr 0) = Sum.inl ((K.rot ^ 0) s) := by
    rw [rot_vertexSplit, splitRot_inr_zero, if_neg (by omega), pow_zero, Perm.one_apply]
  have hreach : ∀ j < p, (K.vertexSplit s p).rot.SameCycle (Sum.inr 0)
      (Sum.inl ((K.rot ^ j) s)) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [← r0]
      exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    | succ j ih =>
      intro hj
      have h := K.rot_vertexSplit_inl_pow_of_lt s p hpk (j := j) (by omega)
      rw [if_neg (by omega)] at h
      rw [← h]
      exact sameCycle_apply_right.2 (ih (by omega))
  refine vertexOf_eq_of_closed ?_ (mem_insert_self _ _) ?_
  · intro a ha
    rcases mem_insert.1 ha with rfl | ha
    · rw [r0]
      exact mem_insert_of_mem (mem_image.2 ⟨0, mem_range.2 (by omega), rfl⟩)
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 ha
      rw [mem_range] at hj
      rw [K.rot_vertexSplit_inl_pow_of_lt s p hpk hj]
      split_ifs with h
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_image.2 ⟨j + 1, mem_range.2 (by omega), rfl⟩)
  · intro a ha
    rcases mem_insert.1 ha with rfl | ha
    · exact SameCycle.refl _ _
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 ha
      exact hreach j (mem_range.1 hj)

/-- The second new vertex of a splitting from `s` of size `p < k` is `(n̄ x_{p+1} … x_k)`,
where `x_{j+1} = σ^j(s)`. -/
private theorem vertexOf_vertexSplit_inr_one (hpk : p < (K.vertexOf s).card) :
    (K.vertexSplit s p).vertexOf (Sum.inr 1) =
      insert (Sum.inr 1) ((Ico p (K.vertexOf s).card).image
        fun j => Sum.inl ((K.rot ^ j) s)) := by
  set k := (K.vertexOf s).card with hkdef
  have hk : p ≤ ({y | K.rot.SameCycle s y} : Finset H).card := hpk.le
  have r1 : (K.vertexSplit s p).rot (Sum.inr 1) = Sum.inl ((K.rot ^ p) s) := by
    rw [rot_vertexSplit, splitRot_inr_one_of_le K.rot s p hk,
      if_neg (show p ≠ ({y | K.rot.SameCycle s y} : Finset H).card from Nat.ne_of_lt hpk)]
  have hreach : ∀ j, p ≤ j → j < k → (K.vertexSplit s p).rot.SameCycle (Sum.inr 1)
      (Sum.inl ((K.rot ^ j) s)) := by
    intro j hpj
    induction j, hpj using Nat.le_induction with
    | base =>
      intro _
      rw [← r1]
      exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    | succ j hj ih =>
      intro hjk
      have h := K.rot_vertexSplit_inl_pow_of_le s p hpk.le hj (by omega)
      rw [if_neg (by omega)] at h
      rw [← h]
      exact sameCycle_apply_right.2 (ih (by omega))
  refine vertexOf_eq_of_closed ?_ (mem_insert_self _ _) ?_
  · intro a ha
    rcases mem_insert.1 ha with rfl | ha
    · rw [r1]
      exact mem_insert_of_mem (mem_image.2 ⟨p, mem_Ico.2 ⟨le_rfl, hpk⟩, rfl⟩)
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 ha
      rw [mem_Ico] at hj
      rw [K.rot_vertexSplit_inl_pow_of_le s p hpk.le hj.1 hj.2]
      split_ifs with h
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_image.2 ⟨j + 1, mem_Ico.2 ⟨by omega, by omega⟩, rfl⟩)
  · intro a ha
    rcases mem_insert.1 ha with rfl | ha
    · exact SameCycle.refl _ _
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 ha
      exact hreach j (mem_Ico.1 hj).1 (mem_Ico.1 hj).2

private theorem injOn_pow_apply {S : Finset ℕ} (hS : ∀ j ∈ S, j < (K.vertexOf s).card) :
    Set.InjOn (fun j => (Sum.inl ((K.rot ^ j) s) : H ⊕ Fin 2)) S := by
  intro i hi j hj h
  exact eq_of_pow_apply_eq_of_lt K.rot s (hS i hi) (hS j hj) (Sum.inl.inj h)

/-- The first new vertex of a splitting from `s` of size `p ∈ [1, k]` has `p + 1` darts. -/
private theorem card_vertexOf_vertexSplit_inr_zero (hp : 1 ≤ p) (hpk : p ≤ (K.vertexOf s).card) :
    ((K.vertexSplit s p).vertexOf (Sum.inr 0)).card = p + 1 := by
  rw [K.vertexOf_vertexSplit_inr_zero s p hp hpk, card_insert_of_notMem (by simp),
    card_image_of_injOn (K.injOn_pow_apply s fun j hj => by
      have := mem_range.1 hj
      omega), card_range]

/-- The second new vertex of a splitting from `s` of size `p < k` has `k - p + 1` darts. -/
private theorem card_vertexOf_vertexSplit_inr_one (hpk : p < (K.vertexOf s).card) :
    ((K.vertexSplit s p).vertexOf (Sum.inr 1)).card = (K.vertexOf s).card - p + 1 := by
  rw [K.vertexOf_vertexSplit_inr_one s p hpk, card_insert_of_notMem (by simp),
    card_image_of_injOn (K.injOn_pow_apply s fun j hj => by
      exact (mem_Ico.1 hj).2), Nat.card_Ico]

/-- In a splitting from `s` of size `p ∈ [1, k)`, every dart of the split vertex lies at one of
the two new vertices. -/
private theorem vertexOf_vertexSplit_inl_of_sameCycle (hp : 1 ≤ p) (hpk : p < (K.vertexOf s).card)
    {x : H} (hx : K.rot.SameCycle s x) :
    (K.vertexSplit s p).vertexOf (Sum.inl x) = (K.vertexSplit s p).vertexOf (Sum.inr 0) ∨
      (K.vertexSplit s p).vertexOf (Sum.inl x) = (K.vertexSplit s p).vertexOf (Sum.inr 1) := by
  obtain ⟨j, hj, rfl⟩ := exists_pow_lt_card_of_sameCycle K.rot hx
  by_cases hjp : j < p
  · left
    refine (K.vertexSplit s p).vertexOf_eq_of_mem ?_
    rw [K.vertexOf_vertexSplit_inr_zero s p hp hpk.le]
    exact mem_insert_of_mem (mem_image.2 ⟨j, mem_range.2 hjp, rfl⟩)
  · right
    refine (K.vertexSplit s p).vertexOf_eq_of_mem ?_
    rw [K.vertexOf_vertexSplit_inr_one s p hpk]
    exact mem_insert_of_mem (mem_image.2 ⟨j, mem_Ico.2 ⟨by omega, hj⟩, rfl⟩)

/-- The new vertices of a splitting at an internal vertex are internal. -/
private theorem not_isBoundaryVertex_vertexSplit_inr (hz : ¬K.IsBoundaryVertex (K.vertexOf s))
    (hp : 1 ≤ p) (hpk : p < (K.vertexOf s).card) (i : Fin 2) :
    ¬(K.vertexSplit s p).IsBoundaryVertex ((K.vertexSplit s p).vertexOf (Sum.inr i)) := by
  have hmem : ∀ e ∈ (K.vertexSplit s p).vertexOf (Sum.inr i), e ∉ (K.vertexSplit s p).bdry := by
    intro e he heB
    rw [bdry_vertexSplit, mem_map] at heB
    obtain ⟨x, hx, rfl⟩ := heB
    have hs : K.rot.SameCycle s x := by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · rw [K.vertexOf_vertexSplit_inr_zero s p hp hpk.le] at he
        rcases mem_insert.1 he with h | h
        · simp at h
        · obtain ⟨j, -, hj⟩ := mem_image.1 h
          rw [Embedding.inl_apply, Sum.inl.injEq] at hj
          rw [← hj]
          exact sameCycle_pow_right.2 (SameCycle.refl _ _)
      · rw [K.vertexOf_vertexSplit_inr_one s p hpk] at he
        rcases mem_insert.1 he with h | h
        · simp at h
        · obtain ⟨j, -, hj⟩ := mem_image.1 h
          rw [Embedding.inl_apply, Sum.inl.injEq] at hj
          rw [← hj]
          exact sameCycle_pow_right.2 (SameCycle.refl _ _)
    exact hz ⟨x, K.mem_vertexOf.2 hs, hx⟩
  rintro ⟨e, he, heB⟩
  exact hmem e he heB

end SplitVertices

/-! ### Isomorphisms and vertex sizes -/

section IsoVertices

variable {H' : Type*} [Fintype H'] [DecidableEq H'] {G : PlabicData H b} {G' : PlabicData H' b}

/-- Isomorphic tuples have the same internal vertex sizes: a property of the sizes of the
internal vertices is transported along an isomorphism. -/
private theorem Iso.forall_card (θ : G.Iso G') {P : ℕ → Prop}
    (h : ∀ v ∈ G.internalVertices, P v.card) : ∀ v ∈ G'.internalVertices, P v.card := by
  intro v hv
  obtain ⟨hvV, hvB⟩ := (DiskMap.mem_internalVertices _).1 hv
  obtain ⟨y, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
  obtain ⟨x, rfl⟩ := θ.toEquiv.surjective y
  rw [θ.isBoundaryVertex_vertexOf_iff] at hvB
  rw [θ.card_vertexOf]
  exact h _ (G.vertexOf_mem_internalVertices.2 hvB)

/-- Trivalence is transported along an isomorphism. -/
private theorem Iso.isTrivalent (θ : G.Iso G') (h : G.IsTrivalent) : G'.IsTrivalent :=
  θ.forall_card (P := (· = 3)) h

end IsoVertices

/-! ### The excess -/

section Excess

/-- The excess `∑ (|v(x)| - 3)` over the darts `x` at internal vertices. It is the dart-weighted
form `∑_v |v| (|v| - 3)` of the excess `ex(X) = ∑_v (|v| - 3)` of a plabic graph. -/
private def excess (G : PlabicData H b) : ℕ :=
  ∑ x, if G.IsBoundaryVertex (G.vertexOf x) then 0 else (G.vertexOf x).card - 3

/-- **Splitting a vertex.** Let `K` be a tuple all of whose internal vertices have at least three
darts, and split an internal vertex `z = v(s)` with `k` darts from `s` with size `p ∈ [2, k - 2]`.
Then all internal vertices of the splitting have at least three darts, and the excess drops. -/
private theorem vertexSplit_thick_excess_lt (K : PlabicData H b) (s : H)
    (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) {p : ℕ} (hp : 2 ≤ p)
    (hpk : p + 2 ≤ (K.vertexOf s).card) (h3 : ∀ v ∈ K.internalVertices, 3 ≤ v.card) :
    (∀ v ∈ (K.vertexSplit s p).internalVertices, 3 ≤ v.card) ∧
      excess (K.vertexSplit s p) < excess K := by
  set S := K.vertexSplit s p with hS
  set k := (K.vertexOf s).card with hkdef
  have c0 := K.card_vertexOf_vertexSplit_inr_zero s p (by omega) (by omega)
  have c1 := K.card_vertexOf_vertexSplit_inr_one s p (by omega)
  have b0 := K.not_isBoundaryVertex_vertexSplit_inr s p hz (by omega) (by omega) 0
  have b1 := K.not_isBoundaryVertex_vertexSplit_inr s p hz (by omega) (by omega) 1
  rw [← hS] at c0 c1 b0 b1
  have hcases : ∀ x, K.rot.SameCycle s x →
      S.vertexOf (Sum.inl x) = S.vertexOf (Sum.inr 0) ∨
        S.vertexOf (Sum.inl x) = S.vertexOf (Sum.inr 1) :=
    fun x hx => K.vertexOf_vertexSplit_inl_of_sameCycle s p (by omega) (by omega) hx
  have hoff : ∀ x, ¬K.rot.SameCycle s x → S.vertexOf (Sum.inl x) =
      (K.vertexOf x).map Embedding.inl := fun x hx => K.vertexOf_vertexSplit_inl s p hx
  have hboff : ∀ t : Finset H, S.IsBoundaryVertex (t.map Embedding.inl) ↔ K.IsBoundaryVertex t :=
    fun t => K.isBoundaryVertex_map_inl_iff s p t
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨hvV, hvB⟩ := (DiskMap.mem_internalVertices _).1 hv
    obtain ⟨e, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
    rcases e with x | i
    · by_cases hx : K.rot.SameCycle s x
      · rcases hcases x hx with h | h <;> rw [h] <;> omega
      · rw [hoff x hx, card_map]
        rw [hoff x hx, hboff] at hvB
        exact h3 _ (K.vertexOf_mem_internalVertices.2 hvB)
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · omega
      · omega
  · set wK : H → ℕ := fun x =>
      if K.IsBoundaryVertex (K.vertexOf x) then 0 else (K.vertexOf x).card - 3 with hwK
    set wS : H ⊕ Fin 2 → ℕ := fun e =>
      if S.IsBoundaryVertex (S.vertexOf e) then 0 else (S.vertexOf e).card - 3 with hwS
    have hw0 : wS (Sum.inr 0) = p - 2 := by simp only [hwS, if_neg b0, c0]; omega
    have hw1 : wS (Sum.inr 1) = k - p - 2 := by simp only [hwS, if_neg b1, c1]; omega
    have hwK : ∀ x, K.rot.SameCycle s x → wK x = k - 3 := by
      intro x hx
      have hv : K.vertexOf x = K.vertexOf s := (K.vertexOf_eq_vertexOf_iff.2 hx).symm
      simp only [hwK, hv, if_neg hz]
      rfl
    have hle : ∀ x, wS (Sum.inl x) ≤ wK x := by
      intro x
      by_cases hx : K.rot.SameCycle s x
      · rw [hwK x hx]
        rcases hcases x hx with h | h
        · simp only [hwS, h, if_neg b0, c0]; omega
        · simp only [hwS, h, if_neg b1, c1]; omega
      · simp only [hwS, hoff x hx, hboff, card_map]
        exact le_rfl
    set sp := (K.rot ^ p) s with hsp
    have hsp_cyc : K.rot.SameCycle s sp := sameCycle_pow_right.2 (SameCycle.refl _ _)
    have hne : s ≠ sp := by
      intro h
      have := eq_of_pow_apply_eq_of_lt K.rot s (i := 0) (j := p) (by
        change 0 < (K.vertexOf s).card
        omega) (by change p < (K.vertexOf s).card; omega)
        (by rw [pow_zero, Perm.one_apply]; exact h)
      omega
    have hs0 : S.vertexOf (Sum.inl s) = S.vertexOf (Sum.inr 0) := by
      refine S.vertexOf_eq_of_mem ?_
      rw [hS, K.vertexOf_vertexSplit_inr_zero s p (by omega) (by omega)]
      exact mem_insert_of_mem (mem_image.2 ⟨0, mem_range.2 (by omega), by simp⟩)
    have hsp1 : S.vertexOf (Sum.inl sp) = S.vertexOf (Sum.inr 1) := by
      refine S.vertexOf_eq_of_mem ?_
      rw [hS, K.vertexOf_vertexSplit_inr_one s p (by omega)]
      exact mem_insert_of_mem (mem_image.2 ⟨p, mem_Ico.2 ⟨le_rfl, by omega⟩, rfl⟩)
    have hws : wS (Sum.inl s) = p - 2 := by simp only [hwS, hs0, if_neg b0, c0]; omega
    have hwsp : wS (Sum.inl sp) = k - p - 2 := by simp only [hwS, hsp1, if_neg b1, c1]; omega
    have hSsum : excess S = ∑ x, wS (Sum.inl x) + (wS (Sum.inr 0) + wS (Sum.inr 1)) := by
      rw [excess, Fintype.sum_sum_type, Fin.sum_univ_two]
    have hKsum : excess K = ∑ x, wK x := rfl
    have hsp_mem : sp ∈ univ.erase s := mem_erase.2 ⟨hne.symm, mem_univ _⟩
    rw [hSsum, hKsum, ← add_sum_erase _ _ (mem_univ s), ← add_sum_erase _ _ (mem_univ s),
      ← add_sum_erase _ _ hsp_mem, ← add_sum_erase _ _ hsp_mem, hws, hwsp, hw0, hw1,
      hwK s (SameCycle.refl _ _), hwK sp hsp_cyc]
    have : ∑ x ∈ (univ.erase s).erase sp, wS (Sum.inl x) ≤
        ∑ x ∈ (univ.erase s).erase sp, wK x := sum_le_sum fun x _ => hle x
    omega

end Excess

/-! ### Splittings along isomorphisms -/

section SplitNaturality

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
private theorem map_pow_apply_of_semiconj {σ : Perm α} {σ' : Perm β} {f : α → β} {s : α}
    (hf : ∀ y, σ.SameCycle s y → f (σ y) = σ' (f y)) (n : ℕ) :
    f ((σ ^ n) s) = (σ' ^ n) (f s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, hf _ (sameCycle_pow_right.2 (SameCycle.refl _ _)), ih,
      pow_succ', Perm.mul_apply]

/-- A map intertwining the rotations along the split vertex intertwines the rotations of the
splittings. -/
private theorem splitRot_map_inl {σ : Perm α} {σ' : Perm β} {f : α → β} (hfi : Injective f)
    {s : α} (hf : ∀ y, σ.SameCycle s y → f (σ y) = σ' (f y)) (p : ℕ) {x : α}
    (hx : f (σ x) = σ' (f x)) :
    splitRot σ' (f s) p (Sum.inl (f x)) = Sum.map f id (splitRot σ s p (Sum.inl x)) := by
  rw [splitRot_inl, splitRot_inl, ← hx, ← map_pow_apply_of_semiconj hf]
  simp only [hfi.eq_iff]
  split_ifs <;> rfl

private theorem splitRot_map_inr {σ : Perm α} {σ' : Perm β} {f : α → β} (hfi : Injective f)
    {s : α} (hf : ∀ y, σ.SameCycle s y → f (σ y) = σ' (f y)) (p : ℕ) (i : Fin 2) :
    splitRot σ' (f s) p (Sum.inr i) = Sum.map f id (splitRot σ s p (Sum.inr i)) := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · rw [splitRot_inr_zero, splitRot_inr_zero]
    split_ifs <;> rfl
  · rw [splitRot_inr_one, splitRot_inr_one, ← map_pow_apply_of_semiconj hf]
    simp only [hfi.eq_iff]
    split_ifs <;> rfl

end SplitNaturality

section IsoSplit

variable {H' : Type*} [Fintype H'] [DecidableEq H']

/-- An isomorphism `θ : K → K'` of plabic graphs induces an isomorphism of the splitting of `K`
at an internal vertex `v(s)` from `s` with the splitting of `K'` from `θ s` of the same size. -/
private noncomputable def Iso.vertexSplit {K : PlabicData H b} {K' : PlabicData H' b}
    (hK : K.IsPlabicGraph) (hK' : K'.IsPlabicGraph) (θ : K.Iso K') {s : H}
    (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) (p : ℕ) :
    (K.vertexSplit s p).Iso (K'.vertexSplit (θ.toEquiv s) p) :=
  Iso.ofEquivOfMapLeg (Equiv.sumCongr θ.toEquiv (Equiv.refl (Fin 2)))
    (by
      rintro (x | i)
      · simp [θ.map_inv]
      · fin_cases i <;> rfl)
    (by
      rintro (x | i)
      · have := splitRot_map_inl (σ := K.rot) (σ' := K'.rot) θ.toEquiv.injective
          (s := s) (fun y _ => θ.map_rot y) p (θ.map_rot x)
        simpa [rot_vertexSplit] using this.symm
      · have := splitRot_map_inr (σ := K.rot) (σ' := K'.rot) θ.toEquiv.injective
          (s := s) (fun y _ => θ.map_rot y) p i
        simpa [rot_vertexSplit] using this.symm)
    (by
      rintro (x | i)
      · simp [θ.mem_bdry_iff]
      · simp)
    (by
      rintro (x | i) hx
      · change K'.colour (θ.toEquiv x) = K.colour x
        by_cases hxb : K.IsBoundaryVertex (K.vertexOf x)
        · exfalso
          have hxs : ¬K.rot.SameCycle s x := fun h => hz (by
            rwa [(K.vertexOf_eq_vertexOf_iff).2 h])
          rw [K.vertexOf_vertexSplit_inl s p hxs, K.isBoundaryVertex_map_inl_iff] at hx
          exact hx hxb
        · exact θ.map_colour x hxb
      · exact θ.map_colour s hz)
    (fun i => by simp [θ.map_leg hK hK'])

end IsoSplit

/-! ### The first step of a resolution is a splitting -/

private theorem card_mergedVertex {G : PlabicData H b} {d : H} (he : G.IsContractibleEdge d) :
    (G.mergedVertex d).card + 2 = (G.vertexOf d).card + (G.vertexOf (G.inv d)).card := by
  have hdisj : Disjoint (G.vertexOf d) (G.vertexOf (G.inv d)) := by
    rw [disjoint_left]
    intro x h1 h2
    exact he.vertexOf_ne ((G.vertexOf_eq_of_mem h1).symm.trans (G.vertexOf_eq_of_mem h2))
  have hsub : ({d, G.inv d} : Finset H) ⊆ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact mem_union_left _ (G.self_mem_vertexOf _)
    · rw [mem_singleton.1 hx]
      exact mem_union_right _ (G.self_mem_vertexOf _)
  have hne : d ≠ G.inv d := fun h => he.vertexOf_ne (by rw [← h])
  rw [mergedVertex, card_sdiff_of_subset hsub, card_union_of_disjoint hdisj, card_pair hne]
  have := card_le_card hsub
  rw [card_pair hne, card_union_of_disjoint hdisj] at this
  omega

/-! ### The vertices of a flip -/

section FlipVertices

variable {G : PlabicData H b} {d : H}

private theorem notMem_vertexOf_union_of_pow {e : H}
    (he : e ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) (n : ℕ) :
    (G.rot ^ n) e ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  intro hn
  apply he
  have he' : e ∈ G.vertexOf ((G.rot ^ n) e) :=
    G.mem_vertexOf.2 (sameCycle_pow_left.2 (SameCycle.refl _ _))
  rcases mem_union.1 hn with h | h
  · exact mem_union_left _ (by rwa [← G.vertexOf_eq_of_mem h])
  · exact mem_union_right _ (by rwa [← G.vertexOf_eq_of_mem h])

/-- Off `v(d) ∪ v(d̄)`, the vertices of a flip are those of `G`. -/
private theorem vertexOf_flipMove_of_notMem (hf : G.IsFlipEdge d) {e : H}
    (he : e ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    (G.flipMove d).vertexOf e = G.vertexOf e := by
  have hpow : ∀ n : ℕ, (flipRot G.rot G.inv d ^ n) e = (G.rot ^ n) e := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hn := notMem_union.1 (notMem_vertexOf_union_of_pow he n)
      rw [pow_succ', Perm.mul_apply, ih, hf.flipRot_apply_of_notMem hn.1 hn.2, ← Perm.mul_apply,
        ← pow_succ']
  ext y
  rw [RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf]
  change (flipRot G.rot G.inv d).SameCycle e y ↔ G.rot.SameCycle e y
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [hpow]
    exact sameCycle_pow_right.2 (SameCycle.refl _ _)
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [← hpow]
    exact sameCycle_pow_right.2 (SameCycle.refl _ _)

private theorem ne_of_mem_of_mem_inv (hf : G.IsFlipEdge d) {x y : H} (hx : x ∈ G.vertexOf d)
    (hy : y ∈ G.vertexOf (G.inv d)) : x ≠ y := by
  rintro rfl
  exact hf.vertexOf_ne ((G.vertexOf_eq_of_mem hx).symm.trans (G.vertexOf_eq_of_mem hy))

/-- The vertex `(d a₂ b₁)` of a flip. -/
private theorem vertexOf_flipMove_self (hf : G.IsFlipEdge d) :
    (G.flipMove d).vertexOf d = {d, G.rot (G.rot d), G.rot (G.inv d)} := by
  have h1 : (G.flipMove d).rot d = G.rot (G.rot d) := hf.flipRot_apply_self
  have h2 : (G.flipMove d).rot (G.rot (G.rot d)) = G.rot (G.inv d) := hf.flipRot_apply_rot_rot
  have h3 : (G.flipMove d).rot (G.rot (G.inv d)) = d := hf.flipRot_apply_rot_inv
  refine vertexOf_eq_of_closed ?_ (mem_insert_self _ _) ?_
  · intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · rw [h1]
      simp
    · rw [h2]
      simp
    · rw [h3]
      simp
  · intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact SameCycle.refl _ _
    · rw [← h1]
      exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    · rw [← h2, ← h1]
      exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))

/-- The vertex `(d̄ b₂ a₁)` of a flip. -/
private theorem vertexOf_flipMove_inv (hf : G.IsFlipEdge d) :
    (G.flipMove d).vertexOf (G.inv d) = {G.inv d, G.rot (G.rot (G.inv d)), G.rot d} := by
  have h1 : (G.flipMove d).rot (G.inv d) = G.rot (G.rot (G.inv d)) := hf.flipRot_apply_inv
  have h2 : (G.flipMove d).rot (G.rot (G.rot (G.inv d))) = G.rot d :=
    hf.flipRot_apply_rot_rot_inv
  have h3 : (G.flipMove d).rot (G.rot d) = G.inv d := hf.flipRot_apply_rot
  refine vertexOf_eq_of_closed ?_ (mem_insert_self _ _) ?_
  · intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · rw [h1]
      simp
    · rw [h2]
      simp
    · rw [h3]
      simp
  · intro a ha
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact SameCycle.refl _ _
    · rw [← h1]
      exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    · rw [← h2, ← h1]
      exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))

/-- The darts of `v(d)` are `d`, `a₁ = σ d`, `a₂ = σ² d`. -/
private theorem eq_of_mem_vertexOf_of_card_three {e x : H} (h3 : (G.vertexOf x).card = 3)
    (he : e ∈ G.vertexOf x) : e = x ∨ e = G.rot x ∨ e = G.rot (G.rot x) :=
  (three_cycle_of_card h3).2.2.2.2 e (G.mem_vertexOf.1 he)

/-- The darts of `v(d) ∪ v(d̄)` lie at the two new vertices of the flip. -/
private theorem mem_vertexOf_flipMove_of_mem (hf : G.IsFlipEdge d) {e : H}
    (he : e ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    e ∈ (G.flipMove d).vertexOf d ∨ e ∈ (G.flipMove d).vertexOf (G.inv d) := by
  rw [vertexOf_flipMove_self hf, vertexOf_flipMove_inv hf]
  rcases mem_union.1 he with h | h
  · rcases eq_of_mem_vertexOf_of_card_three hf.card_vertexOf h with rfl | rfl | rfl <;> simp
  · rcases eq_of_mem_vertexOf_of_card_three hf.card_vertexOf_inv h with h | h | h <;>
      rw [h] <;> simp

private theorem card_vertexOf_flipMove_self (hf : G.IsFlipEdge d) :
    ((G.flipMove d).vertexOf d).card = 3 := by
  rw [vertexOf_flipMove_self hf]
  obtain ⟨-, -, n2, -, -⟩ := three_cycle_of_card hf.card_vertexOf
  refine card_eq_three.2 ⟨_, _, _, n2,
    ne_of_mem_of_mem_inv hf (G.self_mem_vertexOf d) (G.rot_mem_vertexOf _),
    ne_of_mem_of_mem_inv hf ?_ (G.rot_mem_vertexOf _), rfl⟩
  rw [← G.vertexOf_rot d, ← G.vertexOf_rot (G.rot d)]
  exact G.self_mem_vertexOf _

private theorem card_vertexOf_flipMove_inv (hf : G.IsFlipEdge d) :
    ((G.flipMove d).vertexOf (G.inv d)).card = 3 := by
  rw [vertexOf_flipMove_inv hf]
  obtain ⟨-, -, n2, -, -⟩ := three_cycle_of_card hf.card_vertexOf_inv
  refine card_eq_three.2 ⟨_, _, _, n2,
    (ne_of_mem_of_mem_inv hf (G.rot_mem_vertexOf _) (G.self_mem_vertexOf _)).symm,
    (ne_of_mem_of_mem_inv hf (G.rot_mem_vertexOf _) ?_).symm, rfl⟩
  rw [← G.vertexOf_rot (G.inv d), ← G.vertexOf_rot (G.rot (G.inv d))]
  exact G.self_mem_vertexOf _

/-- An internal vertex of a flip is an internal vertex of `G` or has three darts. -/
private theorem mem_internalVertices_or_card_eq_of_flipMove (hf : G.IsFlipEdge d) {v : Finset H}
    (hv : v ∈ (G.flipMove d).internalVertices) : v ∈ G.internalVertices ∨ v.card = 3 := by
  obtain ⟨hvV, hvB⟩ := (DiskMap.mem_internalVertices _).1 hv
  obtain ⟨e, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
  by_cases he : e ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
  · right
    rcases mem_vertexOf_flipMove_of_mem hf he with h | h
    · rw [(G.flipMove d).vertexOf_eq_of_mem h, card_vertexOf_flipMove_self hf]
    · rw [(G.flipMove d).vertexOf_eq_of_mem h, card_vertexOf_flipMove_inv hf]
  · left
    rw [vertexOf_flipMove_of_notMem hf he] at hvB ⊢
    exact G.vertexOf_mem_internalVertices.2 hvB

private theorem thick_flipMove (hf : G.IsFlipEdge d) (h3 : ∀ v ∈ G.internalVertices, 3 ≤ v.card) :
    ∀ v ∈ (G.flipMove d).internalVertices, 3 ≤ v.card := fun v hv =>
  (mem_internalVertices_or_card_eq_of_flipMove hf hv).elim (h3 v) fun h => h.ge

private theorem isTrivalent_flipMove (hf : G.IsFlipEdge d) (h : G.IsTrivalent) :
    (G.flipMove d).IsTrivalent := fun v hv =>
  (mem_internalVertices_or_card_eq_of_flipMove hf hv).elim (h v) id

/-- A flip edge away from the split vertex is a flip edge of the splitting. -/
private theorem IsFlipEdge.vertexSplit (hf : G.IsFlipEdge d) {s : H}
    (hs : ¬G.rot.SameCycle s d) (hs' : ¬G.rot.SameCycle s (G.inv d)) (p : ℕ) :
    (G.vertexSplit s p).IsFlipEdge (Sum.inl d) := by
  have hv := G.vertexOf_vertexSplit_inl s p hs
  have hv' := G.vertexOf_vertexSplit_inl s p hs'
  have hinv : (G.vertexSplit s p).inv (Sum.inl d) = Sum.inl (G.inv d) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hinv, hv, hv']
    exact (map_injective _).ne hf.vertexOf_ne
  · rw [hv, isBoundaryVertex_map_inl_iff]
    exact hf.not_isBoundaryVertex
  · rw [hinv, hv', isBoundaryVertex_map_inl_iff]
    exact hf.not_isBoundaryVertex_inv
  · exact hf.colour_inv
  · rw [hv, card_map]
    exact hf.card_vertexOf
  · rw [hinv, hv', card_map]
    exact hf.card_vertexOf_inv

/-- **A flip commutes with a splitting away from the flipped edge**: the flip at `{d, d̄}` of the
splitting of `G` at a vertex `w = v(s)` disjoint from `v(d) ∪ v(d̄)` is the splitting at `w` of the
flip of `G` at `{d, d̄}`. -/
private theorem flipRot_vertexSplit_apply (hf : G.IsFlipEdge d) {s : H}
    (hs : ¬G.rot.SameCycle s d) (hs' : ¬G.rot.SameCycle s (G.inv d)) (e : H ⊕ Fin 2) :
    flipRot (G.vertexSplit s 2).rot (G.vertexSplit s 2).inv (Sum.inl d) e =
      splitRot (flipRot G.rot G.inv d) s 2 e := by
  set X1 := G.vertexSplit s 2 with hX1
  have hf1 := hf.vertexSplit hs hs' 2
  have hU : ∀ y, y ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) → ¬G.rot.SameCycle s y := by
    intro y hy h
    rcases mem_union.1 hy with hy | hy
    · exact hs (h.trans (G.mem_vertexOf.1 hy).symm)
    · exact hs' (h.trans (G.mem_vertexOf.1 hy).symm)
  have hsU : s ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := fun h => hU s h (SameCycle.refl _ _)
  have hFw : ∀ y, G.rot.SameCycle s y → id (G.rot y) = flipRot G.rot G.inv d (id y) := by
    intro y hy
    have hyU : y ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := fun h => hU y h hy
    exact (hf.flipRot_apply_of_notMem (notMem_union.1 hyU).1 (notMem_union.1 hyU).2).symm
  have hv := G.vertexOf_vertexSplit_inl s 2 hs
  have hv' := G.vertexOf_vertexSplit_inl s 2 hs'
  have hinv : X1.inv (Sum.inl d) = Sum.inl (G.inv d) := rfl
  have hr : ∀ y, ¬G.rot.SameCycle s y → X1.rot (Sum.inl y) = Sum.inl (G.rot y) :=
    fun y hy => splitRot_inl_of_not_sameCycle _ _ _ hy
  have hFs : ∀ y, y ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) →
      ¬(flipRot G.rot G.inv d).SameCycle s y := by
    intro y hy h
    have : y ∈ (G.flipMove d).vertexOf s := (G.flipMove d).mem_vertexOf.2 h
    rw [vertexOf_flipMove_of_notMem hf hsU] at this
    exact hU y hy (G.mem_vertexOf.1 this)
  rcases e with y | i
  · by_cases hy : y ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
    · rw [splitRot_inl_of_not_sameCycle _ _ _ (hFs y hy)]
      have m0 : d ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) := mem_union_left _ (G.self_mem_vertexOf _)
      have m1 : G.rot d ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
        mem_union_left _ (G.rot_mem_vertexOf _)
      have m0' : G.inv d ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
        mem_union_right _ (G.self_mem_vertexOf _)
      have m1' : G.rot (G.inv d) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
        mem_union_right _ (G.rot_mem_vertexOf _)
      have r0 := hr d (hU _ m0)
      have r1 := hr _ (hU _ m1)
      have r0' := hr _ (hU _ m0')
      have r1' := hr _ (hU _ m1')
      rcases mem_union.1 hy with h | h
      · rcases eq_of_mem_vertexOf_of_card_three hf.card_vertexOf h with rfl | rfl | rfl
        · have := hf1.flipRot_apply_self
          rw [r0, r1] at this
          rw [this, hf.flipRot_apply_self]
        · have := hf1.flipRot_apply_rot
          rw [r0, hinv] at this
          rw [this, hf.flipRot_apply_rot]
        · have := hf1.flipRot_apply_rot_rot
          rw [r0, r1, hinv, r0'] at this
          rw [this, hf.flipRot_apply_rot_rot]
      · rcases eq_of_mem_vertexOf_of_card_three hf.card_vertexOf_inv h with h' | h' | h' <;>
          rw [h']
        · have := hf1.flipRot_apply_inv
          rw [hinv, r0', r1'] at this
          rw [this, hf.flipRot_apply_inv]
        · have := hf1.flipRot_apply_rot_inv
          rw [hinv, r0'] at this
          rw [this, hf.flipRot_apply_rot_inv]
        · have := hf1.flipRot_apply_rot_rot_inv
          rw [hinv, r0', r1', r0] at this
          rw [this, hf.flipRot_apply_rot_rot_inv]
    · have hyd : Sum.inl y ∉ X1.vertexOf (Sum.inl d) := by
        rw [hv]
        simpa using fun h => hy (mem_union_left _ h)
      have hyd' : Sum.inl y ∉ X1.vertexOf (X1.inv (Sum.inl d)) := by
        rw [hinv, hv']
        simpa using fun h => hy (mem_union_right _ h)
      rw [hf1.flipRot_apply_of_notMem hyd hyd']
      have hx : id (G.rot y) = flipRot G.rot G.inv d (id y) :=
        (hf.flipRot_apply_of_notMem (notMem_union.1 hy).1 (notMem_union.1 hy).2).symm
      have := splitRot_map_inl (f := id) injective_id hFw 2 hx
      simp only [id, Sum.map_id_id] at this
      rw [this]
      rfl
  · have hyd : Sum.inr i ∉ X1.vertexOf (Sum.inl d) := by
      rw [hv]
      simp
    have hyd' : Sum.inr i ∉ X1.vertexOf (X1.inv (Sum.inl d)) := by
      rw [hinv, hv']
      simp
    rw [hf1.flipRot_apply_of_notMem hyd hyd']
    have := splitRot_map_inr (f := id) injective_id hFw 2 i
    simp only [id, Sum.map_id_id] at this
    rw [this]
    rfl

/-- The isomorphism (the identity of darts) between the flip of a splitting and the splitting of
the flip, away from the flipped edge. -/
private noncomputable def flipMoveVertexSplitIso (hf : G.IsFlipEdge d) {s : H}
    (hs : ¬G.rot.SameCycle s d) (hs' : ¬G.rot.SameCycle s (G.inv d)) :
    ((G.vertexSplit s 2).flipMove (Sum.inl d)).Iso ((G.flipMove d).vertexSplit s 2) :=
  Iso.ofEquivOfMapLeg (Equiv.refl _) (fun _ => rfl)
    (fun e => flipRot_vertexSplit_apply hf hs hs' e)
    (fun _ => Iff.rfl)
    (fun e _ => by
      have hv := G.vertexOf_vertexSplit_inl s 2 hs
      have hv' := G.vertexOf_vertexSplit_inl s 2 hs'
      have hinv : (G.vertexSplit s 2).inv (Sum.inl d) = Sum.inl (G.inv d) := rfl
      have hsU : s ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
        rw [mem_union, not_or]
        exact ⟨fun h => hs (G.mem_vertexOf.1 h).symm, fun h => hs' (G.mem_vertexOf.1 h).symm⟩
      rw [Equiv.refl_apply, colour_flipMove, hinv, hv, hv']
      rcases e with y | i
      · simp [colour_flipMove]
      · simp [colour_flipMove, hsU])
    (fun _ => rfl)

end FlipVertices

/-! ### Square moves and splittings -/

section SquareSplit

variable {G : PlabicData H b} {c : H}

private theorem IsSquareMoveFace.facePerm_pow_eq (hq : G.IsSquareMoveFace c) (n : ℕ) :
    (G.facePerm ^ n) c = G.squareCorner c ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩ := by
  have h4 : ((G.facePerm ^ 4) ^ (n / 4)) c = c :=
    Perm.pow_apply_eq_self_of_apply_eq_self hq.facePerm_pow_four _
  conv_lhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, Perm.mul_apply, h4]
  rfl

private theorem IsSquareMoveFace.card_vertexOf_facePerm_pow (hq : G.IsSquareMoveFace c)
    (n : ℕ) : (G.vertexOf ((G.facePerm ^ n) c)).card = 3 := by
  rw [hq.facePerm_pow_eq n]
  exact hq.card_vertexOf _

private theorem vertexOf_inv_facePerm_pow (n : ℕ) :
    G.vertexOf (G.inv ((G.facePerm ^ n) c)) = G.vertexOf ((G.facePerm ^ (n + 1)) c) := by
  rw [pow_succ', Perm.mul_apply, RotationSystem.facePerm_apply, G.vertexOf_rot]

variable {s : H} (hs : ∀ n : ℕ, ¬G.rot.SameCycle s ((G.facePerm ^ n) c))

include hs

omit [Fintype H] [DecidableEq H] in
private theorem not_sameCycle_inv_facePerm_pow (n : ℕ) :
    ¬G.rot.SameCycle s (G.inv ((G.facePerm ^ n) c)) := fun h => hs (n + 1) (by
  rw [pow_succ', Perm.mul_apply, RotationSystem.facePerm_apply]
  exact sameCycle_apply_right.2 h)

omit [Fintype H] in
private theorem facePerm_pow_vertexSplit_inl (p n : ℕ) :
    ((G.vertexSplit s p).facePerm ^ n) (Sum.inl c) = Sum.inl ((G.facePerm ^ n) c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, RotationSystem.facePerm_apply, pow_succ', Perm.mul_apply,
      RotationSystem.facePerm_apply]
    exact splitRot_inl_of_not_sameCycle _ _ _ (not_sameCycle_inv_facePerm_pow hs n)

omit [Fintype H] in
private theorem squareCorner_vertexSplit_inl (p : ℕ) (k : Fin 4) :
    (G.vertexSplit s p).squareCorner (Sum.inl c) k = Sum.inl (G.squareCorner c k) :=
  facePerm_pow_vertexSplit_inl hs p k

private theorem vertexOf_squareCorner_vertexSplit (p : ℕ) (k : Fin 4) :
    (G.vertexSplit s p).vertexOf ((G.vertexSplit s p).squareCorner (Sum.inl c) k) =
      (G.vertexOf (G.squareCorner c k)).map Embedding.inl := by
  rw [squareCorner_vertexSplit_inl hs]
  exact G.vertexOf_vertexSplit_inl s p (hs k)

/-- A square-move face away from the split vertex is a square-move face of the splitting. -/
private theorem IsSquareMoveFace.vertexSplit (hq : G.IsSquareMoveFace c) (p : ℕ) :
    (G.vertexSplit s p).IsSquareMoveFace (Sum.inl c) := by
  set X1 := G.vertexSplit s p with hX1
  have hface : X1.faceOf (Sum.inl c) = (G.faceOf c).map Embedding.inl := by
    refine G.faceOf_vertexSplit_inl s p fun y hy => ?_
    obtain ⟨n, rfl⟩ := (G.mem_faceOf.1 hy).exists_nat_pow_eq
    exact not_sameCycle_inv_facePerm_pow hs n
  obtain ⟨hfaces, hdisj⟩ := (DiskMap.mem_internalFaces _).1 hq.faceOf_mem_internalFaces
  have hcB : c ∉ G.bdry := disjoint_left.1 hdisj (G.self_mem_faceOf c)
  refine ⟨?_, ?_, fun k => ?_, fun j k h => ?_, fun k => ?_, fun k => ?_⟩
  · refine (DiskMap.mem_internalFaces _).2 ⟨(DiskMap.mem_faces _).2 ⟨fun h => ?_,
      X1.faceOf_mem_faceOrbits _⟩, ?_⟩
    · have hm : Sum.inl c ∈ X1.exterior := h ▸ X1.self_mem_faceOf _
      have := X1.exterior_subset_bdry hm
      rw [hX1, bdry_vertexSplit] at this
      simp [hcB] at this
    · rw [hface, hX1, bdry_vertexSplit, disjoint_map]
      exact hdisj
  · rw [facePerm_pow_vertexSplit_inl hs, hq.facePerm_pow_four]
  · rw [vertexOf_squareCorner_vertexSplit hs]
    refine X1.mem_internalVertices.2 ⟨?_, ?_⟩
    · have hk : ¬G.rot.SameCycle s (G.squareCorner c k) := hs k
      rw [← G.vertexOf_vertexSplit_inl s p hk]
      exact X1.vertexOf_mem_vertices _
    · rw [isBoundaryVertex_map_inl_iff]
      exact (G.mem_internalVertices.1 (hq.vertexOf_mem_internalVertices k)).2
  · have h' : X1.vertexOf (X1.squareCorner (Sum.inl c) j) =
        X1.vertexOf (X1.squareCorner (Sum.inl c) k) := h
    rw [vertexOf_squareCorner_vertexSplit hs, vertexOf_squareCorner_vertexSplit hs] at h'
    exact hq.injective (map_injective _ h')
  · rw [vertexOf_squareCorner_vertexSplit hs, card_map]
    exact hq.card_vertexOf k
  · rw [squareCorner_vertexSplit_inl hs, squareCorner_vertexSplit_inl hs]
    exact hq.colour_ne k

omit hs in
private theorem vertexOf_mem_squareVertices_iff' {e : H} :
    G.vertexOf e ∈ G.squareVertices c ↔ ∃ k, e ∈ G.vertexOf (G.squareCorner c k) := by
  rw [mem_squareVertices]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, hk ▸ G.self_mem_vertexOf e⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (G.vertexOf_eq_of_mem hk).symm⟩

/-- The isomorphism (the identity of darts) between the square move of a splitting and the
splitting of the square move, away from the face. -/
private noncomputable def squareMoveVertexSplitIso (p : ℕ) :
    ((G.vertexSplit s p).squareMove (Sum.inl c)).Iso ((G.squareMove c).vertexSplit s p) :=
  Iso.ofEquivOfMapLeg (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl)
    (fun e _ => by
      have hsq : ∀ e : H ⊕ Fin 2, (G.vertexSplit s p).vertexOf e ∈
          (G.vertexSplit s p).squareVertices (Sum.inl c) ↔
          ∃ y, e = Sum.inl y ∧ G.vertexOf y ∈ G.squareVertices c := by
        intro e
        simp only [vertexOf_mem_squareVertices_iff', vertexOf_squareCorner_vertexSplit hs]
        constructor
        · rintro ⟨k, hk⟩
          obtain ⟨y, hy, rfl⟩ := mem_map.1 hk
          exact ⟨y, rfl, k, hy⟩
        · rintro ⟨y, rfl, k, hy⟩
          exact ⟨k, mem_map_of_mem _ hy⟩
      have hs' : G.vertexOf s ∉ G.squareVertices c := by
        rw [vertexOf_mem_squareVertices_iff']
        rintro ⟨k, hk⟩
        exact hs k (G.mem_vertexOf.1 hk).symm
      simp only [Equiv.refl_apply, colour_squareMove, hsq]
      rcases e with y | i
      · simp [colour_squareMove]
      · simp [colour_squareMove, hs'])
    (fun _ => rfl)

end SquareSplit

/-! ### Two splittings -/

section TwoSplits

variable {α : Type*} [DecidableEq α]

/-- The exchange of the new darts of the inner and the outer splitting of a twice split vertex
set: `inl (inl x) ↦ inl (inl x)`, `inl (inr i) ↦ inr i`, `inr i ↦ inl (inr i)`. -/
private def swapNew (α : Type*) : (α ⊕ Fin 2) ⊕ Fin 2 ≃ (α ⊕ Fin 2) ⊕ Fin 2 where
  toFun
    | .inl (.inl x) => .inl (.inl x)
    | .inl (.inr i) => .inr i
    | .inr i => .inl (.inr i)
  invFun
    | .inl (.inl x) => .inl (.inl x)
    | .inl (.inr i) => .inr i
    | .inr i => .inl (.inr i)
  left_inv := by rintro ((x | i) | i) <;> rfl
  right_inv := by rintro ((x | i) | i) <;> rfl

omit [DecidableEq α] in
private theorem swapNew_inl (w : α ⊕ Fin 2) : swapNew α (Sum.inl w) = Sum.map Sum.inl id w := by
  rcases w with x | i <;> rfl

omit [DecidableEq α] in
private theorem swapNew_map (w : α ⊕ Fin 2) : swapNew α (Sum.map Sum.inl id w) = Sum.inl w := by
  rcases w with x | i <;> rfl

omit [DecidableEq α] in
private theorem swapNew_inr (i : Fin 2) : swapNew α (Sum.inr i) = Sum.inl (Sum.inr i) := rfl

variable (σ : Perm α)

/-- Splitting at a second vertex `z'` does not change the rotation away from `z'`. -/
private theorem splitRot_splitRot_inl_of_not [Finite α] {s s' : α} (hss : ¬σ.SameCycle s s')
    (p p' : ℕ) {w : α ⊕ Fin 2} (hw : ∀ x, w = Sum.inl x → ¬σ.SameCycle s' x) :
    splitRot (splitRot σ s p) (Sum.inl s') p' (Sum.inl w) = Sum.inl (splitRot σ s p w) := by
  refine splitRot_inl_of_not_sameCycle _ _ _ fun h => ?_
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [splitRot_pow_inl_of_not_sameCycle _ _ _ hss] at hn
  exact hw _ hn.symm (sameCycle_pow_right.2 (SameCycle.refl _ _))

/-- Splitting at a second vertex `z'` acts on `z'` as on `σ`. -/
private theorem splitRot_splitRot_inl_inl {s s' : α} (hss : ¬σ.SameCycle s s') (p p' : ℕ) {x : α}
    (hx : σ.SameCycle s' x) :
    splitRot (splitRot σ s p) (Sum.inl s') p' (Sum.inl (Sum.inl x)) =
      Sum.map Sum.inl id (splitRot σ s' p' (Sum.inl x)) := by
  have hf : ∀ y, σ.SameCycle s' y → Sum.inl (σ y) = splitRot σ s p (Sum.inl y) := fun y hy =>
    (splitRot_inl_of_not_sameCycle _ _ _ fun h => hss (h.trans hy.symm)).symm
  exact splitRot_map_inl Sum.inl_injective hf p' (hf x hx)

private theorem splitRot_splitRot_inr {s s' : α} (hss : ¬σ.SameCycle s s') (p p' : ℕ)
    (i : Fin 2) :
    splitRot (splitRot σ s p) (Sum.inl s') p' (Sum.inr i) =
      Sum.map Sum.inl id (splitRot σ s' p' (Sum.inr i)) := by
  have hf : ∀ y, σ.SameCycle s' y → Sum.inl (σ y) = splitRot σ s p (Sum.inl y) := fun y hy =>
    (splitRot_inl_of_not_sameCycle _ _ _ fun h => hss (h.trans hy.symm)).symm
  exact splitRot_map_inr Sum.inl_injective hf p' i

/-- **Splittings at distinct vertices commute**, at the level of rotations. -/
private theorem swapNew_splitRot_comm [Finite α] {s s' : α} (hss : ¬σ.SameCycle s s') (p p' : ℕ)
    (y : (α ⊕ Fin 2) ⊕ Fin 2) :
    swapNew α (splitRot (splitRot σ s p) (Sum.inl s') p' y) =
      splitRot (splitRot σ s' p') (Sum.inl s) p (swapNew α y) := by
  have hss' : ¬σ.SameCycle s' s := fun h => hss h.symm
  rcases y with (x | i) | i
  · change _ = splitRot (splitRot σ s' p') (Sum.inl s) p (Sum.inl (Sum.inl x))
    by_cases hx : σ.SameCycle s x
    · rw [splitRot_splitRot_inl_of_not σ hss p p' (w := Sum.inl x) (fun x' h h' => by
          cases h; exact hss (hx.trans h'.symm)), swapNew_inl,
        splitRot_splitRot_inl_inl σ hss' p' p hx]
    · by_cases hx' : σ.SameCycle s' x
      · rw [splitRot_splitRot_inl_inl σ hss p p' hx', swapNew_map,
          splitRot_splitRot_inl_of_not σ hss' p' p (w := Sum.inl x) (fun x' h h' => by
            cases h; exact hx h')]
      · rw [splitRot_splitRot_inl_of_not σ hss p p' (w := Sum.inl x) (fun x' h h' => by
            cases h; exact hx' h'),
          splitRot_splitRot_inl_of_not σ hss' p' p (w := Sum.inl x) (fun x' h h' => by
            cases h; exact hx h'),
          splitRot_inl_of_not_sameCycle _ _ _ hx, splitRot_inl_of_not_sameCycle _ _ _ hx']
        rfl
  · rw [splitRot_splitRot_inl_of_not σ hss p p' (w := Sum.inr i) (fun _ h => by cases h),
      swapNew_inl]
    change _ = splitRot (splitRot σ s' p') (Sum.inl s) p (Sum.inr i)
    rw [splitRot_splitRot_inr σ hss' p' p]
  · rw [splitRot_splitRot_inr σ hss p p', swapNew_map, swapNew_inr,
      splitRot_splitRot_inl_of_not σ hss' p' p (w := Sum.inr i) (fun _ h => by cases h)]

/-- **Nested splittings at one vertex**, at the level of rotations. Splitting
`z = (x_1 … x_k)` from `x_1` with size `a` and then the second new vertex `(n̄ x_{a+1} … x_k)`
from `n̄` with size `a' - a + 1` gives the vertices `(n x_1 … x_a)`, `(m n̄ x_{a+1} … x_{a'})`,
`(m̄ x_{a'+1} … x_k)`; splitting `z` from `x_1` with size `a'` and then the first new vertex
`(n' x_1 … x_{a'})` from `x_1` with size `a` gives `(m' x_1 … x_a)`, `(m̄' x_{a+1} … x_{a'} n')`,
`(n̄' x_{a'+1} … x_k)`. The two agree once the names of the new darts are exchanged. -/
private theorem swapNew_splitRot_nested [Fintype α] (t : α) {a a' : ℕ} (ha : 1 ≤ a) (haa : a < a')
    (hak : a' < ({y | σ.SameCycle t y} : Finset α).card) (y : (α ⊕ Fin 2) ⊕ Fin 2) :
    swapNew α (splitRot (splitRot σ t a) (Sum.inr 1) (a' - a + 1) y) =
      splitRot (splitRot σ t a') (Sum.inl t) a (swapNew α y) := by
  set k := ({y | σ.SameCycle t y} : Finset α).card with hk
  set ρ1 := splitRot σ t a with hρ1
  set ρ2 := splitRot σ t a' with hρ2
  have inj : ∀ i j, i < k → j < k → (σ ^ i) t = (σ ^ j) t → i = j := fun i j hi hj h =>
    eq_of_pow_apply_eq_of_lt σ t hi hj h
  have h1 : ∀ j < k, ρ1 (Sum.inl ((σ ^ j) t)) = if j + 1 = a then Sum.inr 0
      else if j + 1 = k then Sum.inr 1 else Sum.inl ((σ ^ (j + 1)) t) := fun j hj =>
    splitRot_inl_pow σ t a (by omega) hj
  have h2 : ∀ j < k, ρ2 (Sum.inl ((σ ^ j) t)) = if j + 1 = a' then Sum.inr 0
      else if j + 1 = k then Sum.inr 1 else Sum.inl ((σ ^ (j + 1)) t) := fun j hj =>
    splitRot_inl_pow σ t a' (by omega) hj
  have r1_one : ρ1 (Sum.inr 1) = Sum.inl ((σ ^ a) t) := by
    rw [hρ1, splitRot_inr_one_of_le σ t a (by omega), if_neg (by omega)]
  have r1_zero : ρ1 (Sum.inr 0) = Sum.inl t := by
    rw [hρ1, splitRot_inr_zero, if_neg (by omega)]
  have r2_one : ρ2 (Sum.inr 1) = Sum.inl ((σ ^ a') t) := by
    rw [hρ2, splitRot_inr_one_of_le σ t a' (by omega), if_neg (by omega)]
  have r2_zero : ρ2 (Sum.inr 0) = Sum.inl t := by
    rw [hρ2, splitRot_inr_zero, if_neg (by omega)]
  have P1 : ∀ j, 1 ≤ j → a + j ≤ k → (ρ1 ^ j) (Sum.inr 1) = Sum.inl ((σ ^ (a + j - 1)) t) := by
    intro j hj1
    induction j, hj1 using Nat.le_induction with
    | base =>
      intro _
      rw [pow_one, r1_one, Nat.add_sub_cancel]
    | succ j hj ih =>
      intro hjk
      rw [pow_succ', Perm.mul_apply, ih (by omega), h1 _ (by omega), if_neg (by omega),
        if_neg (by omega), show a + j - 1 + 1 = a + (j + 1) - 1 by omega]
  have P3 : ∀ j ≤ a, (ρ2 ^ j) (Sum.inl t) = Sum.inl ((σ ^ j) t) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [pow_succ', Perm.mul_apply, ih (by omega), h2 _ (by omega), if_neg (by omega),
        if_neg (by omega)]
  have ht : (σ ^ 0) t = t := rfl
  rcases y with (h | i) | i
  · change _ = splitRot ρ2 (Sum.inl t) a (Sum.inl (Sum.inl h))
    have eL : splitRot ρ1 (Sum.inr 1) (a' - a + 1) (Sum.inl (Sum.inl h)) =
        if a' - a + 1 ≠ 0 ∧ (Sum.inl h : α ⊕ Fin 2) = Sum.inl ((σ ^ (a' - 1)) t) then Sum.inr 0
        else if ρ1 (Sum.inl h) = Sum.inr 1 then Sum.inr 1 else Sum.inl (ρ1 (Sum.inl h)) := by
      rw [splitRot_inl, Nat.add_sub_cancel, P1 (a' - a) (by omega) (by omega),
        show a + (a' - a) - 1 = a' - 1 by omega]
    have eR : splitRot ρ2 (Sum.inl t) a (Sum.inl (Sum.inl h)) =
        if a ≠ 0 ∧ (Sum.inl h : α ⊕ Fin 2) = Sum.inl ((σ ^ (a - 1)) t) then Sum.inr 0
        else if ρ2 (Sum.inl h) = Sum.inl t then Sum.inr 1 else Sum.inl (ρ2 (Sum.inl h)) := by
      rw [splitRot_inl, P3 (a - 1) (by omega)]
    rw [eL, eR]
    by_cases hA : h = (σ ^ (a' - 1)) t
    · have hne : (σ ^ (a' - 1)) t ≠ (σ ^ (a - 1)) t := fun e => by
        have := inj _ _ (by omega) (by omega) e
        omega
      have hr2 : ρ2 (Sum.inl h) = Sum.inr 0 := by
        rw [hA, h2 _ (by omega), if_pos (by omega)]
      rw [if_pos ⟨by omega, by rw [hA]⟩, if_neg (fun h' => hne (hA ▸ Sum.inl.inj h'.2)), hr2,
        if_neg (by simp)]
      rfl
    · by_cases hB : h = (σ ^ (a - 1)) t
      · have hr1 : ρ1 (Sum.inl ((σ ^ (a - 1)) t)) = Sum.inr 0 := by
          rw [h1 _ (by omega), if_pos (by omega)]
        have ha0 : a ≠ 0 := by omega
        subst hB
        simp [hA, hr1, ha0, swapNew_inl]
      · have e1 : ρ1 (Sum.inl h) = if σ h = t then Sum.inr 1 else Sum.inl (σ h) := by
          rw [hρ1, splitRot_inl, if_neg (fun h' => hB h'.2)]
        have e2 : ρ2 (Sum.inl h) = if σ h = t then Sum.inr 1 else Sum.inl (σ h) := by
          rw [hρ2, splitRot_inl, if_neg (fun h' => hA h'.2)]
        by_cases hC : σ h = t
        · simp [hA, hB, e1, e2, hC, swapNew_inr]
        · simp [hA, hB, e1, e2, hC, swapNew_inl]
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · change _ = splitRot ρ2 (Sum.inl t) a (Sum.inr 0)
      rw [splitRot_inl ρ1 (Sum.inr 1) (a' - a + 1) (Sum.inr 0), Nat.add_sub_cancel,
        P1 (a' - a) (by omega) (by omega), r1_zero, if_neg (by simp), if_neg (by simp),
        splitRot_inr_zero, if_neg (by omega)]
      rfl
    · change _ = splitRot ρ2 (Sum.inl t) a (Sum.inr 1)
      have hne : (σ ^ a) t ≠ t := fun e => by
        have := inj a 0 (by omega) (by omega) (by rw [e]; rfl)
        omega
      rw [splitRot_inl ρ1 (Sum.inr 1) (a' - a + 1) (Sum.inr 1), Nat.add_sub_cancel,
        P1 (a' - a) (by omega) (by omega), r1_one, if_neg (by simp), if_neg (by simp),
        splitRot_inr_one, P3 a le_rfl, if_neg (fun h => hne (Sum.inl.inj h.2))]
      rfl
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · change _ = splitRot ρ2 (Sum.inl t) a (Sum.inl (Sum.inr 0))
      rw [splitRot_inr_zero, if_neg (by omega), splitRot_inl ρ2 (Sum.inl t) a (Sum.inr 0),
        P3 (a - 1) (by omega), if_neg (by simp), r2_zero, if_pos rfl]
      rfl
    · change _ = splitRot ρ2 (Sum.inl t) a (Sum.inl (Sum.inr 1))
      have hne : (σ ^ a') t ≠ t := fun e => by
        have := inj a' 0 (by omega) (by omega) (by rw [e]; rfl)
        omega
      rw [splitRot_inr_one, P1 (a' - a + 1) (by omega) (by omega),
        show a + (a' - a + 1) - 1 = a' by omega, if_neg (by simp),
        splitRot_inl ρ2 (Sum.inl t) a (Sum.inr 1), P3 (a - 1) (by omega), if_neg (by simp), r2_one,
        if_neg (fun h => hne (Sum.inl.inj h))]
      rfl

/-- **Splitting from `s` with size `p` or from `σ^p(s)` with size `k - p`**, at the level of
rotations: the two splittings differ by the names of the new darts. -/
private theorem splitRot_sameDiag [Fintype α] (s : α) {p : ℕ} (hp : 1 ≤ p)
    (hpk : p < ({y | σ.SameCycle s y} : Finset α).card) (e : α ⊕ Fin 2) :
    Equiv.sumCongr (Equiv.refl α) (Equiv.swap 0 1) (splitRot σ s p e) =
      splitRot σ ((σ ^ p) s) (({y | σ.SameCycle s y} : Finset α).card - p)
        (Equiv.sumCongr (Equiv.refl α) (Equiv.swap 0 1) e) := by
  set k := ({y | σ.SameCycle s y} : Finset α).card with hk
  have inj : ∀ i j, i < k → j < k → (σ ^ i) s = (σ ^ j) s → i = j := fun i j hi hj h =>
    eq_of_pow_apply_eq_of_lt σ s hi hj h
  have hkpow : (σ ^ k) s = s := pow_card_orbit_apply σ s
  have hpow : ∀ i j, (σ ^ i) ((σ ^ j) s) = (σ ^ (i + j)) s := fun i j => by
    rw [← Perm.mul_apply, ← pow_add]
  have hσ1 : σ ((σ ^ (p - 1)) s) = (σ ^ p) s := by
    rw [← Perm.mul_apply, ← pow_succ', show p - 1 + 1 = p by omega]
  have hσk : σ ((σ ^ (k - 1)) s) = s := by
    rw [← Perm.mul_apply, ← pow_succ', show k - 1 + 1 = k by omega, hkpow]
  have hps : (σ ^ p) s ≠ s := fun e => by
    have := inj p 0 hpk (by omega) (by rw [e]; rfl)
    omega
  rcases e with x | i
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]
    rw [splitRot_inl, splitRot_inl, hpow, show k - p - 1 + p = k - 1 by omega]
    have hA : σ x = (σ ^ p) s ↔ x = (σ ^ (p - 1)) s := by
      rw [← hσ1, σ.injective.eq_iff]
    have hB : x = (σ ^ (k - 1)) s ↔ σ x = s :=
      ⟨fun h => by rw [h, hσk], fun h => σ.injective (by rw [h, hσk])⟩
    by_cases h1 : x = (σ ^ (p - 1)) s
    · have h2 : σ x ≠ s := by rwa [h1, hσ1]
      rw [if_pos ⟨by omega, h1⟩, if_neg (fun h => h2 (hB.1 h.2)), if_pos (hA.2 h1)]
      rfl
    · rw [if_neg (fun h => h1 h.2)]
      by_cases h2 : σ x = s
      · rw [if_pos h2, if_pos ⟨by omega, hB.2 h2⟩]
        rfl
      · rw [if_neg h2, if_neg (fun h => h2 (hB.1 h.2)), if_neg (fun h => h1 (hA.1 h))]
        rfl
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · simp only [Equiv.sumCongr_apply, Sum.map_inr, swap_apply_left]
      rw [splitRot_inr_zero, if_neg (by omega), splitRot_inr_one, hpow,
        show k - p + p = k by omega, hkpow, if_neg (fun h => hps h.2.symm)]
      rfl
    · simp only [Equiv.sumCongr_apply, Sum.map_inr, swap_apply_right]
      rw [splitRot_inr_one, if_neg (fun h => hps h.2), splitRot_inr_zero, if_neg (by omega)]
      rfl

end TwoSplits

/-! ### Isomorphisms between splittings -/

section SplitIsos

/-- In a splitting from `s` of size `p ≥ 1`, the dart `s` lies at the first new vertex. -/
private theorem vertexOf_vertexSplit_inl_self (K : PlabicData H b) (s : H) {p : ℕ} (hp : 1 ≤ p)
    (hpk : p ≤ (K.vertexOf s).card) :
    (K.vertexSplit s p).vertexOf (Sum.inl s) = (K.vertexSplit s p).vertexOf (Sum.inr 0) := by
  refine (K.vertexSplit s p).vertexOf_eq_of_mem ?_
  rw [K.vertexOf_vertexSplit_inr_zero s p hp hpk]
  exact mem_insert_of_mem (mem_image.2 ⟨0, mem_range.2 (by omega), rfl⟩)

/-- **A diagonal determines its splitting**: the splitting from `s` of size `p ∈ [1, k)` is
isomorphic to the splitting from `σ^p(s)` of size `k - p`, by exchanging the new darts. -/
private noncomputable def vertexSplitSameDiagIso {K : PlabicData H b} (hK : K.IsPlabicGraph)
    {s : H} (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) {p : ℕ} (hp : 1 ≤ p)
    (hpk : p < (K.vertexOf s).card) :
    (K.vertexSplit s p).Iso (K.vertexSplit ((K.rot ^ p) s) ((K.vertexOf s).card - p)) :=
  Iso.ofEquivOfMapLeg (Equiv.sumCongr (Equiv.refl H) (Equiv.swap 0 1))
    (by
      rintro (x | i)
      · rfl
      · fin_cases i <;> rfl)
    (fun e => splitRot_sameDiag K.rot s hp hpk e)
    (by
      rintro (x | i)
      · exact Iff.rfl
      · change Sum.inr _ ∈ K.bdry.map Embedding.inl ↔ Sum.inr i ∈ K.bdry.map Embedding.inl
        simp)
    (by
      rintro (x | i) _
      · rfl
      · exact colour_eq_of_sameCycle hK hz (sameCycle_pow_right.2 (SameCycle.refl _ _)))
    (fun _ => rfl)

/-- **Splittings at distinct vertices commute**: splitting `v(s)` and then `v(s')`, or `v(s')`
and then `v(s)`, gives isomorphic tuples. -/
private noncomputable def vertexSplitCommIso {K : PlabicData H b} {s s' : H}
    (hss : ¬K.rot.SameCycle s s') (p p' : ℕ) :
    ((K.vertexSplit s p).vertexSplit (Sum.inl s') p').Iso
      ((K.vertexSplit s' p').vertexSplit (Sum.inl s) p) :=
  Iso.ofEquivOfMapLeg (swapNew H)
    (by
      rintro ((x | i) | i)
      · rfl
      · fin_cases i <;> rfl
      · fin_cases i <;> rfl)
    (fun y => swapNew_splitRot_comm K.rot hss p p' y)
    (by
      rintro ((x | i) | i)
      · simp [swapNew_inl]
      · simp [swapNew_inl]
      · simp [swapNew_inr])
    (by
      rintro ((x | i) | i) _ <;> rfl)
    (fun _ => rfl)

/-- **Nested splittings commute**: splitting `z` from `x_1` with size `a` and then the second new
vertex from `n̄` with size `a' - a + 1`, or `z` from `x_1` with size `a'` and then the first new
vertex from `x_1` with size `a`, gives isomorphic tuples. -/
private noncomputable def vertexSplitNestedIso {K : PlabicData H b} {t : H} {a a' : ℕ}
    (ha : 1 ≤ a) (haa : a < a') (hak : a' < (K.vertexOf t).card) :
    ((K.vertexSplit t a).vertexSplit (Sum.inr 1) (a' - a + 1)).Iso
      ((K.vertexSplit t a').vertexSplit (Sum.inl t) a) :=
  Iso.ofEquivOfMapLeg (swapNew H)
    (by
      rintro ((x | i) | i)
      · rfl
      · fin_cases i <;> rfl
      · fin_cases i <;> rfl)
    (fun y => swapNew_splitRot_nested K.rot t ha haa hak y)
    (by
      rintro ((x | i) | i)
      · simp [swapNew_inl]
      · simp [swapNew_inl]
      · simp [swapNew_inr])
    (by
      rintro ((x | i) | i) _ <;> rfl)
    (fun _ => rfl)

/-- Splitting a vertex with four darts from `s` with size `2` gives two trivalent vertices joined
by a flip edge. -/
private theorem isFlipEdge_vertexSplit_two {K : PlabicData H b} {t : H}
    (hz : ¬K.IsBoundaryVertex (K.vertexOf t)) (hk : (K.vertexOf t).card = 4) :
    (K.vertexSplit t 2).IsFlipEdge (Sum.inr 0) := by
  have hinv : (K.vertexSplit t 2).inv (Sum.inr 0) = Sum.inr 1 := rfl
  refine ⟨?_, K.not_isBoundaryVertex_vertexSplit_inr t 2 hz (by omega) (by omega) 0, ?_, rfl,
    ?_, ?_⟩
  · rw [hinv]
    intro h
    have : Sum.inr 1 ∈ (K.vertexSplit t 2).vertexOf (Sum.inr 0) := by
      rw [h]
      exact (K.vertexSplit t 2).self_mem_vertexOf _
    rw [K.vertexOf_vertexSplit_inr_zero t 2 (by omega) (by omega)] at this
    simp at this
  · rw [hinv]
    exact K.not_isBoundaryVertex_vertexSplit_inr t 2 hz (by omega) (by omega) 1
  · rw [K.card_vertexOf_vertexSplit_inr_zero t 2 (by omega) (by omega)]
  · rw [hinv, K.card_vertexOf_vertexSplit_inr_one t 2 (by omega), hk]

/-- **The flip of a split four-dart vertex is the other splitting**: for a vertex
`z = (x_1 x_2 x_3 x_4)`, the flip of the splitting from `x_1` with size `2` at its new edge is the
splitting from `x_2` with size `2`. -/
private theorem isomorphic_flipMove_vertexSplit_two {K : PlabicData H b} (hK : K.IsPlabicGraph)
    {t : H} (hz : ¬K.IsBoundaryVertex (K.vertexOf t)) (hk : (K.vertexOf t).card = 4) :
    ((K.vertexSplit t 2).flipMove (Sum.inr 0)).Isomorphic (K.vertexSplit (K.rot t) 2) := by
  set Y := K.vertexSplit t 2 with hYdef
  have hY : Y.IsPlabicGraph := hK.vertexSplit hz 2
  have hf := isFlipEdge_vertexSplit_two hz hk
  have ha := hf.rot_rot_mem
  have h1 := isomorphic_flipMove_vertexSplit (hleg := vertexSplit_leg_mem) hY hf ha
  have hYc : (Y.contractEdge (Sum.inr 0) vertexSplit_leg_mem).IsPlabicGraph :=
    hY.contractEdge (K.isContractibleEdge_vertexSplit t 2 hz (by omega))
  set θ := contractEdgeVertexSplitIso K t 2 hK.inv_involutive
  have hzr : ¬K.IsBoundaryVertex (K.vertexOf (K.rot t)) := by rwa [K.vertexOf_rot]
  have hrt : K.rot t ≠ t := by
    intro h
    have := eq_of_pow_apply_eq_of_lt K.rot t (i := 1) (j := 0)
      (by change 1 < (K.vertexOf t).card; omega) (by change 0 < (K.vertexOf t).card; omega)
      (by rw [pow_one, pow_zero, Perm.one_apply, h])
    omega
  have e0 : Y.rot (Sum.inr 0) = Sum.inl t := by
    rw [hYdef, rot_vertexSplit, splitRot_inr_zero, if_neg (by norm_num)]
  have e1 : Y.rot (Sum.inl t) = Sum.inl (K.rot t) := by
    rw [hYdef, rot_vertexSplit, splitRot_inl, if_neg (fun h => hrt (by
      have := h.2
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at this
      exact this.symm)), if_neg hrt]
  have hval : θ.toEquiv (K.rot t) = ⟨Y.rot (Y.rot (Sum.inr 0)), ha⟩ := by
    apply Subtype.ext
    change (θ.toEquiv (K.rot t) : H ⊕ Fin 2) = Y.rot (Y.rot (Sum.inr 0))
    rw [e0, e1]
    rfl
  have I := Iso.vertexSplit hK hYc θ hzr 2
  rw [hval] at I
  exact PlabicData.Isomorphic.trans _ h1 ⟨I.symm⟩

end SplitIsos

/-! ### Square moves and skeletons -/

section SkeletonSquare

omit [Fintype H] [DecidableEq H] in
private theorem ext_of_toDiskMap {K K' : PlabicData H b} (h₁ : K.toDiskMap = K'.toDiskMap)
    (h₂ : K.colour = K'.colour) (h₃ : K.leg = K'.leg) : K = K' := by
  cases K
  cases K'
  simp only at h₁ h₂ h₃
  subst h₁ h₂ h₃
  rfl

/-- **A square move at core vertices commutes with the skeleton**.
Let `G` be a plabic graph and `q` the face through `c`, satisfying the conditions of the square
move, such that every dart of the four vertices `v(c₁), …, v(c₄)` lies in the core `K(G)`. Then
`q` is a face of the skeleton `Γ(G)` satisfying the conditions of the square move, and the square
move of `Γ(G)` at `q` is the skeleton of the square move of `G` at `q`. -/
@[cluster_algebras "lem_skeleton_square_move"]
theorem IsSquareMoveFace.skeleton {G : PlabicData H b} (hG : G.IsPlabicGraph) {c : H}
    (hq : G.IsSquareMoveFace c) (hK : ∀ k, G.vertexOf (G.squareCorner c k) ⊆ G.core) :
    ∃ hc : c ∈ G.skeletonDarts, (G.skeleton hG).IsSquareMoveFace ⟨c, hc⟩ ∧
      (G.skeleton hG).squareMove ⟨c, hc⟩ = (G.squareMove c).skeleton (hG.squareMove c) := by
  have hsub : ∀ n : ℕ, G.vertexOf ((G.facePerm ^ n) c) ⊆ G.skeletonDarts := by
    intro n y hy
    have hy' : y ∈ G.vertexOf (G.squareCorner c ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩) :=
      hq.facePerm_pow_eq n ▸ hy
    refine mem_filter.2 ⟨hK _ hy', Or.inr ?_⟩
    rw [G.vertexOf_eq_of_mem hy', inter_eq_left.2 (hK _), hq.card_vertexOf]
  have hmem : ∀ n : ℕ, (G.facePerm ^ n) c ∈ G.skeletonDarts := fun n =>
    hsub n (G.self_mem_vertexOf _)
  have hc : c ∈ G.skeletonDarts := hmem 0
  have hinvmem : ∀ n : ℕ, G.inv ((G.facePerm ^ n) c) ∈ G.skeletonDarts := fun n =>
    hsub (n + 1) (by rw [← vertexOf_inv_facePerm_pow]; exact G.self_mem_vertexOf _)
  have hstep : ∀ n : ℕ, ((G.skeleton hG).facePerm ⟨(G.facePerm ^ n) c, hmem n⟩ : H) =
      (G.facePerm ^ (n + 1)) c := by
    intro n
    have hinv : ((G.skeleton hG).inv ⟨(G.facePerm ^ n) c, hmem n⟩ : H) =
        G.inv ((G.facePerm ^ n) c) := by
      rw [coe_skeleton_inv, coe_skeletonInvFun_of_isLeast _ (n := 0)
        (by rw [skeletonWalk_zero]; exact hinvmem n)
        (fun j hj => absurd hj (Nat.not_lt_zero _)), skeletonWalk_zero]
    have hφ : G.rot (G.inv ((G.facePerm ^ n) c)) = (G.facePerm ^ (n + 1)) c := by
      rw [pow_succ', Perm.mul_apply, RotationSystem.facePerm_apply]
    rw [RotationSystem.facePerm_apply, skeleton_rot, coe_firstReturnPerm,
      coe_firstReturn_of_apply_mem (by rw [hinv, hφ]; exact hmem (n + 1)), hinv, hφ]
  have hpow : ∀ n : ℕ, (((G.skeleton hG).facePerm ^ n) ⟨c, hc⟩ : H) = (G.facePerm ^ n) c := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have : ((G.skeleton hG).facePerm ^ n) ⟨c, hc⟩ = ⟨(G.facePerm ^ n) c, hmem n⟩ :=
        Subtype.ext ih
      rw [pow_succ', Perm.mul_apply, this, hstep]
  have hcorner : ∀ k, ((G.skeleton hG).squareCorner ⟨c, hc⟩ k : H) = G.squareCorner c k :=
    fun k => hpow k
  have hvert : ∀ k, ((G.skeleton hG).vertexOf ((G.skeleton hG).squareCorner ⟨c, hc⟩ k)).map
      (Embedding.subtype _) = G.vertexOf (G.squareCorner c k) := by
    intro k
    rw [map_skeleton_vertexOf hG, hcorner]
    exact inter_eq_left.2 (hsub k)
  have hmemΓ : ∀ k (y : (G.skeletonDarts : Set H)),
      y ∈ (G.skeleton hG).vertexOf ((G.skeleton hG).squareCorner ⟨c, hc⟩ k) ↔
        (y : H) ∈ G.vertexOf (G.squareCorner c k) := by
    intro k y
    rw [← hvert k, ← mem_map' (Embedding.subtype (· ∈ (G.skeletonDarts : Set H)))]
    rfl
  obtain ⟨hfaces, hdisj⟩ := (DiskMap.mem_internalFaces _).1 hq.faceOf_mem_internalFaces
  have hcB : c ∉ G.bdry := disjoint_left.1 hdisj (G.self_mem_faceOf c)
  have hface : ∀ y ∈ (G.skeleton hG).faceOf ⟨c, hc⟩, (y : H) ∉ G.bdry := by
    intro y hy
    obtain ⟨n, rfl⟩ := ((G.skeleton hG).mem_faceOf.1 hy).exists_nat_pow_eq
    rw [hpow]
    exact disjoint_left.1 hdisj (G.mem_faceOf.2 (sameCycle_pow_right.2 (SameCycle.refl _ _)))
  refine ⟨hc, ⟨?_, ?_, fun k => ?_, fun j k h => ?_, fun k => ?_, fun k => ?_⟩, ?_⟩
  · refine (DiskMap.mem_internalFaces _).2 ⟨(DiskMap.mem_faces _).2 ⟨fun h => ?_,
      (G.skeleton hG).faceOf_mem_faceOrbits _⟩, disjoint_left.2 fun y hy hyB =>
        hface y hy ((mem_skeleton_bdry hG).1 hyB)⟩
    have hm : (⟨c, hc⟩ : (G.skeletonDarts : Set H)) ∈ (G.skeleton hG).exterior :=
      h ▸ (G.skeleton hG).self_mem_faceOf _
    exact hcB ((mem_skeleton_bdry hG).1 ((G.skeleton hG).exterior_subset_bdry hm))
  · exact Subtype.ext (by rw [hpow]; exact hq.facePerm_pow_four)
  · refine (G.skeleton hG).vertexOf_mem_internalVertices.2 ?_
    rintro ⟨y, hy, hyB⟩
    exact (G.mem_internalVertices.1 (hq.vertexOf_mem_internalVertices k)).2
      ⟨y, (hmemΓ k y).1 hy, (mem_skeleton_bdry hG).1 hyB⟩
  · have h' : (G.skeleton hG).vertexOf ((G.skeleton hG).squareCorner ⟨c, hc⟩ j) =
        (G.skeleton hG).vertexOf ((G.skeleton hG).squareCorner ⟨c, hc⟩ k) := h
    have := congrArg (Finset.map (Embedding.subtype (· ∈ (G.skeletonDarts : Set H)))) h'
    rw [hvert, hvert] at this
    exact hq.injective this
  · rw [← card_map (Embedding.subtype (· ∈ (G.skeletonDarts : Set H))), hvert]
    exact hq.card_vertexOf k
  · rw [skeleton_colour, skeleton_colour, hcorner, hcorner]
    exact hq.colour_ne k
  · have hiff : ∀ x : (G.skeletonDarts : Set H), (G.skeleton hG).vertexOf x ∈
        (G.skeleton hG).squareVertices ⟨c, hc⟩ ↔ G.vertexOf x ∈ G.squareVertices c := by
      intro x
      rw [vertexOf_mem_squareVertices_iff', vertexOf_mem_squareVertices_iff']
      exact exists_congr fun k => hmemΓ k x
    refine ext_of_toDiskMap rfl (funext fun x => ?_) rfl
    rw [colour_squareMove, skeleton_colour]
    change _ = (G.squareMove c).colour x
    rw [colour_squareMove]
    by_cases h : G.vertexOf x ∈ G.squareVertices c
    · rw [if_pos ((hiff x).2 h), if_pos h]
    · rw [if_neg (mt (hiff x).1 h), if_neg h]

end SkeletonSquare

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

/-- **The first step of a resolution is a splitting.** If `Y` has all internal vertices with at
least three darts and `X` is isomorphic to the contraction of `Y` along an edge, then `Y` is
isomorphic to the splitting of `X` at an internal vertex `z = v(s)` from `s` of some size
`p ∈ [2, k - 2]`, `k` being the number of darts of `z`. -/
private theorem ResolutionStep.exists_isomorphic_vertexSplit {X Y : PlabicGraph b}
    (h : ResolutionStep X Y) :
    ∃ (s : X.Dart) (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf s)) (p : ℕ),
      2 ≤ p ∧ p + 2 ≤ (X.data.vertexOf s).card ∧ Y.Isomorphic (X.vertexSplit hz p) := by
  obtain ⟨hY3, d, he, ⟨θ⟩⟩ := h
  set G := Y.data with hG
  have hGp : G.IsPlabicGraph := Y.isPlabicGraph
  have hleg := he.leg_mem hGp
  have hd3 : 3 ≤ (G.vertexOf d).card := hY3 _ he.mem_internalVertices
  have hd3' : 3 ≤ (G.vertexOf (G.inv d)).card := hY3 _ he.inv_mem_internalVertices
  obtain ⟨p, hp⟩ : ∃ p, (G.vertexOf d).card = p + 1 := ⟨(G.vertexOf d).card - 1, by omega⟩
  have hrd : G.rot d ≠ d := by
    intro h
    have : G.vertexOf d ⊆ {d} := by
      intro y hy
      obtain ⟨n, rfl⟩ := ((RotationSystem.mem_vertexOf _).1 hy).exists_nat_pow_eq
      have : ∀ m : ℕ, (G.rot ^ m) d = d := fun m => by
        induction m with
        | zero => rfl
        | succ m ih => rw [pow_succ', Perm.mul_apply, ih, h]
      rw [this, mem_singleton]
    have := card_le_card this
    rw [card_singleton] at this
    omega
  have hrd' : G.rot d ≠ G.inv d := fun h => he.vertexOf_ne (by rw [← h, G.vertexOf_rot])
  have ha : G.rot d ∈ (({d, G.inv d} : Set Y.Dart)ᶜ : Set Y.Dart) :=
    PlabicData.mem_compl_pair_iff.2 ⟨hrd, hrd'⟩
  set K := G.contractEdge d hleg with hK
  have hKp : K.IsPlabicGraph := hGp.contractEdge he
  have h1 : G.Isomorphic (K.vertexSplit ⟨G.rot d, ha⟩ p) :=
    PlabicData.isomorphic_vertexSplit_contractEdge hGp he hp ha
  have hzK : ¬K.IsBoundaryVertex (K.vertexOf ⟨G.rot d, ha⟩) := by
    rw [PlabicData.isBoundaryVertex_vertexOf_contractEdge_iff he, G.vertexOf_rot]
    exact he.not_isBoundaryVertex
  have hcardK : (K.vertexOf ⟨G.rot d, ha⟩).card + 2 =
      (G.vertexOf d).card + (G.vertexOf (G.inv d)).card := by
    have hm := PlabicData.map_vertexOf_contractEdge_of_mem (hleg := hleg)
      (x := ⟨G.rot d, ha⟩) he.not_sameCycle (mem_union_left _ (G.rot_mem_vertexOf d))
    rw [← PlabicData.card_mergedVertex he, ← hm, card_map]
  set s := θ.symm.toEquiv ⟨G.rot d, ha⟩ with hs
  have hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf s) := by
    rw [hs, θ.symm.isBoundaryVertex_vertexOf_iff]
    exact hzK
  have hcard : (X.data.vertexOf s).card = (K.vertexOf ⟨G.rot d, ha⟩).card :=
    θ.symm.card_vertexOf _
  refine ⟨s, hz, p, by omega, by omega, ?_⟩
  exact PlabicData.Isomorphic.trans _ h1
    ⟨PlabicData.Iso.vertexSplit hKp X.isPlabicGraph θ.symm hzK p⟩

/-! ### Resolutions -/

namespace IsResolution

variable {X X' Y T : PlabicGraph b}

private theorem thick (h : X.IsResolution T) : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card := h.1

private theorem isTrivalent (h : X.IsResolution T) : T.IsTrivalent := h.2.1

/-- A trivalent plabic graph is its own resolution. -/
private theorem self (hX : X.IsTrivalent) : X.IsResolution X :=
  ⟨fun v hv => (hX v hv).ge, hX, X, .refl, ⟨PlabicData.Iso.refl _⟩⟩

/-- The resolutions of `X` are resolutions of every graph isomorphic to `X`. -/
private theorem of_isomorphic (hXX' : X'.Isomorphic X) (h : X.IsResolution T) :
    X'.IsResolution T := by
  obtain ⟨h3, htri, Y, hXY, hTY⟩ := h
  obtain ⟨θ⟩ := hXX'
  refine ⟨θ.symm.forall_card h3, htri, ?_⟩
  rcases hXY.cases_head with rfl | ⟨Z, ⟨hZ3, d, he, hiso⟩, hZY⟩
  · exact ⟨X', .refl, PlabicData.Isomorphic.trans _ hTY ⟨θ.symm⟩⟩
  · exact ⟨Y, Relation.ReflTransGen.head ⟨hZ3, d, he, PlabicData.Isomorphic.trans _ ⟨θ⟩ hiso⟩
      hZY, hTY⟩

/-- If `X` is isomorphic to the contraction of `Y` along an edge, every resolution of `Y` is a
resolution of `X`. -/
private theorem head (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card) (hs : ResolutionStep X Y)
    (h : Y.IsResolution T) : X.IsResolution T :=
  let ⟨_, htri, Z, hYZ, hTZ⟩ := h
  ⟨hX, htri, Z, .head hs hYZ, hTZ⟩

/-- A resolution of `X` is `X` itself up to isomorphism, or a resolution of a graph of which `X`
is a contraction. -/
private theorem cases (h : X.IsResolution T) :
    T.Isomorphic X ∨ ∃ Y, ResolutionStep X Y ∧ Y.IsResolution T := by
  obtain ⟨h3, htri, Y, hXY, hTY⟩ := h
  rcases hXY.cases_head with rfl | ⟨Z, hXZ, hZY⟩
  · exact Or.inl hTY
  · exact Or.inr ⟨Z, hXZ, hXZ.1, htri, Y, hZY, hTY⟩

end IsResolution

/-- A splitting of size `p ∈ [2, k - 2]` of a vertex with `k` darts is a step of a resolution. -/
private theorem resolutionStep_vertexSplit {X : PlabicGraph b}
    (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card) {s : X.Dart}
    (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf s)) {p : ℕ} (hp : 2 ≤ p)
    (hpk : p + 2 ≤ (X.data.vertexOf s).card) : ResolutionStep X (X.vertexSplit hz p) :=
  ⟨(PlabicData.vertexSplit_thick_excess_lt X.data s hz hp hpk hX).1, Sum.inr 0,
    X.data.isContractibleEdge_vertexSplit s p hz (by omega),
    X.data.isomorphic_contractEdge_vertexSplit s p X.isPlabicGraph.inv_involutive⟩

/-- A plabic graph whose internal vertices have at least three darts, and which is not trivalent,
has an internal vertex with at least four darts. -/
private theorem exists_four_le_card {X : PlabicGraph b}
    (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card) (htri : ¬X.IsTrivalent) :
    ∃ s : X.Dart, ¬X.data.IsBoundaryVertex (X.data.vertexOf s) ∧
      4 ≤ (X.data.vertexOf s).card := by
  have : ∃ v ∈ X.data.internalVertices, v.card ≠ 3 := by
    by_contra hc
    push Not at hc
    exact htri hc
  obtain ⟨v, hv, hv3⟩ := this
  obtain ⟨hvV, hvB⟩ := (DiskMap.mem_internalVertices _).1 hv
  obtain ⟨s, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
  exact ⟨s, hvB, by have := hX _ hv; omega⟩

/-- **A flip lifts to resolutions**. Let `X` be a plabic graph in which
every internal vertex has at least three darts, and let `{d, d̄}` be an edge of `X` satisfying the
conditions of the flip move. Then some resolution `R` of `X` and some resolution `R'` of the flip
of `X` at `{d, d̄}` are `{M4}`-connected. -/
@[cluster_algebras "lem_resolution_flip"]
theorem exists_isResolution_flipMove (X : PlabicGraph b)
    (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card) {d : X.Dart} (hf : X.data.IsFlipEdge d) :
    ∃ R R', X.IsResolution R ∧ (X.flipMove hf).IsResolution R' ∧
      TrivalentConnected {TrivalentMoveType.m4} R R' := by
  suffices h : ∀ n, ∀ X : PlabicGraph b, PlabicData.excess X.data = n →
      (∀ v ∈ X.data.internalVertices, 3 ≤ v.card) → ∀ {d : X.Dart} (hf : X.data.IsFlipEdge d),
      ∃ R R', X.IsResolution R ∧ (X.flipMove hf).IsResolution R' ∧
        TrivalentConnected {TrivalentMoveType.m4} R R' from h _ X rfl hX hf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hX d hf
  have hY3 : ∀ v ∈ (X.flipMove hf).data.internalVertices, 3 ≤ v.card :=
    PlabicData.thick_flipMove hf hX
  by_cases htri : X.IsTrivalent
  · have hYtri : (X.flipMove hf).IsTrivalent := PlabicData.isTrivalent_flipMove hf htri
    exact ⟨X, X.flipMove hf, IsResolution.self htri, IsResolution.self hYtri,
      TrivalentConnected.of_isFlip (Set.mem_singleton _) htri hYtri
        ⟨d, hf, PlabicData.Isomorphic.refl _⟩⟩
  obtain ⟨s, hz, hk⟩ := exists_four_le_card hX htri
  have hs : ¬X.data.rot.SameCycle s d := fun h => by
    rw [(X.data.vertexOf_eq_vertexOf_iff).2 h, hf.card_vertexOf] at hk
    omega
  have hs' : ¬X.data.rot.SameCycle s (X.data.inv d) := fun h => by
    rw [(X.data.vertexOf_eq_vertexOf_iff).2 h, hf.card_vertexOf_inv] at hk
    omega
  have hsU : s ∉ X.data.vertexOf d ∪ X.data.vertexOf (X.data.inv d) := by
    rw [mem_union, not_or]
    exact ⟨fun h => hs (X.data.mem_vertexOf.1 h).symm,
      fun h => hs' (X.data.mem_vertexOf.1 h).symm⟩
  obtain ⟨hthick, hlt⟩ := PlabicData.vertexSplit_thick_excess_lt X.data s hz le_rfl (by omega) hX
  have hf1 := PlabicData.IsFlipEdge.vertexSplit hf hs hs' 2
  obtain ⟨R, R', hR, hR', hRR'⟩ := ih _ (hn ▸ hlt) (X.vertexSplit hz 2) rfl hthick hf1
  refine ⟨R, R', hR.head hX (resolutionStep_vertexSplit hX hz le_rfl (by omega)), ?_, hRR'⟩
  have hvY : (X.flipMove hf).data.vertexOf s = X.data.vertexOf s :=
    PlabicData.vertexOf_flipMove_of_notMem hf hsU
  have hzY : ¬(X.flipMove hf).data.IsBoundaryVertex ((X.flipMove hf).data.vertexOf s) := by
    rw [hvY]
    exact hz
  have hstep : ResolutionStep (X.flipMove hf) ((X.flipMove hf).vertexSplit hzY 2) :=
    resolutionStep_vertexSplit hY3 hzY le_rfl
      (by rw [hvY]; exact (show 2 + 2 ≤ (X.data.vertexOf s).card by omega))
  have hiso : ((X.flipMove hf).vertexSplit hzY 2).Isomorphic ((X.vertexSplit hz 2).flipMove hf1) :=
    ⟨(PlabicData.flipMoveVertexSplitIso hf hs hs').symm⟩
  exact (hR'.of_isomorphic hiso).head hY3 hstep

/-- **A square move lifts to resolutions**. Let `X` be a plabic
graph in which every internal vertex has at least three darts, and let `q` be the face through `c`
satisfying the conditions of the square move. Then some resolution `R` of `X` and some resolution
`R'` of the square move of `X` at `q` are `{M1}`-connected. -/
@[cluster_algebras "lem_resolution_square_move"]
theorem exists_isResolution_squareMove (X : PlabicGraph b)
    (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card) {c : X.Dart}
    (hq : X.data.IsSquareMoveFace c) :
    ∃ R R', X.IsResolution R ∧ (X.squareMove c).IsResolution R' ∧
      TrivalentConnected {TrivalentMoveType.m1} R R' := by
  suffices h : ∀ n, ∀ X : PlabicGraph b, PlabicData.excess X.data = n →
      (∀ v ∈ X.data.internalVertices, 3 ≤ v.card) → ∀ {c : X.Dart},
      X.data.IsSquareMoveFace c → ∃ R R', X.IsResolution R ∧ (X.squareMove c).IsResolution R' ∧
        TrivalentConnected {TrivalentMoveType.m1} R R' from h _ X rfl hX hq
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hX c hq
  have hY3 : ∀ v ∈ (X.squareMove c).data.internalVertices, 3 ≤ v.card := hX
  by_cases htri : X.IsTrivalent
  · have hYtri : (X.squareMove c).IsTrivalent := htri
    exact ⟨X, X.squareMove c, IsResolution.self htri, IsResolution.self hYtri,
      TrivalentConnected.of_isSquareMove (Set.mem_singleton _) htri hYtri
        ⟨c, hq, PlabicData.Isomorphic.refl _⟩⟩
  obtain ⟨s, hz, hk⟩ := exists_four_le_card hX htri
  have hs : ∀ n : ℕ, ¬X.data.rot.SameCycle s ((X.data.facePerm ^ n) c) := fun n h => by
    rw [(X.data.vertexOf_eq_vertexOf_iff).2 h, hq.card_vertexOf_facePerm_pow n] at hk
    omega
  obtain ⟨hthick, hlt⟩ := PlabicData.vertexSplit_thick_excess_lt X.data s hz le_rfl (by omega) hX
  have hq1 := PlabicData.IsSquareMoveFace.vertexSplit hs hq 2
  obtain ⟨R, R', hR, hR', hRR'⟩ := ih _ (hn ▸ hlt) (X.vertexSplit hz 2) rfl hthick hq1
  refine ⟨R, R', hR.head hX (resolutionStep_vertexSplit hX hz le_rfl (by omega)), ?_, hRR'⟩
  have hzY : ¬(X.squareMove c).data.IsBoundaryVertex ((X.squareMove c).data.vertexOf s) := hz
  have hstep : ResolutionStep (X.squareMove c) ((X.squareMove c).vertexSplit hzY 2) :=
    resolutionStep_vertexSplit hY3 hzY le_rfl hk
  have hiso : ((X.squareMove c).vertexSplit hzY 2).Isomorphic
      ((X.vertexSplit hz 2).squareMove (Sum.inl c)) :=
    ⟨(PlabicData.squareMoveVertexSplitIso hs 2).symm⟩
  exact (hR'.of_isomorphic hiso).head hY3 hstep

/-! ### Any two resolutions are related by flips -/

/-- `A` and `B` are *linked* if every resolution of `A` is `{M4}`-connected to every resolution of
`B`. -/
private def Linked (A B : PlabicGraph b) : Prop :=
  ∀ R R', A.IsResolution R → B.IsResolution R' → TrivalentConnected {TrivalentMoveType.m4} R R'

namespace Linked

variable {A B C : PlabicGraph b}

private theorem symm (h : Linked A B) : Linked B A := fun R R' hR hR' => (h R' R hR' hR).symm

private theorem trans (hB : ∀ v ∈ B.data.internalVertices, 3 ≤ v.card) (h : Linked A B)
    (h' : Linked B C) : Linked A C := fun R R'' hR hR'' => by
  obtain ⟨R', hR'⟩ := exists_isResolution B hB
  exact (h R R' hR hR').trans (h' R' R'' hR' hR'')

/-- Self-linked graphs with `{M4}`-connected resolutions are linked. -/
private theorem of_exists (hA : Linked A A) (hB : Linked B B) {R R' : PlabicGraph b}
    (hR : A.IsResolution R) (hR' : B.IsResolution R')
    (h : TrivalentConnected {TrivalentMoveType.m4} R R') : Linked A B :=
  fun R₁ R₁' h₁ h₁' => ((hA R₁ R h₁ hR).trans h).trans (hB R' R₁' hR' h₁')

/-- Self-linked graphs with a common splitting are linked. -/
private theorem of_common (hA : Linked A A) (hB : Linked B B)
    (hAt : ∀ v ∈ A.data.internalVertices, 3 ≤ v.card)
    (hBt : ∀ v ∈ B.data.internalVertices, 3 ≤ v.card) {U U' : PlabicGraph b}
    (hAU : ResolutionStep A U) (hBU : ResolutionStep B U') (hUU : U'.Isomorphic U) :
    Linked A B := by
  obtain ⟨R, hR⟩ := exists_isResolution U hAU.1
  exact of_exists hA hB (hR.head hAt hAU) ((hR.of_isomorphic hUU).head hBt hBU)
    (TrivalentConnected.refl hR.isTrivalent)

/-- Isomorphic self-linked graphs are linked. -/
private theorem of_isomorphic (hA : Linked A A) (hB : Linked B B)
    (hAt : ∀ v ∈ A.data.internalVertices, 3 ≤ v.card) (h : B.Isomorphic A) : Linked A B := by
  obtain ⟨R, hR⟩ := exists_isResolution A hAt
  exact of_exists hA hB hR (hR.of_isomorphic h) (TrivalentConnected.refl hR.isTrivalent)

end Linked

section SplitLinks

variable {X : PlabicGraph b}

private theorem thick_vertexSplit (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card) {s : X.Dart}
    (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf s)) {p : ℕ} (hp : 2 ≤ p)
    (hpk : p + 2 ≤ (X.data.vertexOf s).card) :
    ∀ v ∈ (X.vertexSplit hz p).data.internalVertices, 3 ≤ v.card :=
  (PlabicData.vertexSplit_thick_excess_lt X.data s hz hp hpk hX).1

private theorem vertexOf_eq_of_sameCycle {s u : X.Dart} (h : X.data.rot.SameCycle s u) :
    X.data.vertexOf u = X.data.vertexOf s :=
  (X.data.vertexOf_eq_vertexOf_iff.2 h).symm

/-- Every splitting of size `p ∈ [2, k - 2]` of a vertex of `X` with `k` darts is linked to
itself. -/
private def SplitsSelfLinked (X : PlabicGraph b) : Prop :=
  ∀ (s : X.Dart) (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf s)) (p : ℕ), 2 ≤ p →
    p + 2 ≤ (X.data.vertexOf s).card → Linked (X.vertexSplit hz p) (X.vertexSplit hz p)

/-- Nested arcs `A ⊊ A'` starting at the same dart: the two splittings have a common splitting. -/
private theorem linked_nested (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card)
    (hS : SplitsSelfLinked X) {t : X.Dart} (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf t))
    {a a' : ℕ} (ha : 2 ≤ a) (haa : a < a') (hak : a' + 2 ≤ (X.data.vertexOf t).card) :
    Linked (X.vertexSplit hz a) (X.vertexSplit hz a') := by
  have hA := thick_vertexSplit hX hz ha (by omega)
  have hB := thick_vertexSplit hX hz (by omega : 2 ≤ a') hak
  have hz1 : ¬(X.vertexSplit hz a).data.IsBoundaryVertex
      ((X.vertexSplit hz a).data.vertexOf (Sum.inr 1)) :=
    X.data.not_isBoundaryVertex_vertexSplit_inr t a hz (by omega) (by omega) 1
  have hc1 : ((X.vertexSplit hz a).data.vertexOf (Sum.inr 1)).card =
      (X.data.vertexOf t).card - a + 1 :=
    X.data.card_vertexOf_vertexSplit_inr_one t a (by omega)
  have hv2 : (X.vertexSplit hz a').data.vertexOf (Sum.inl t) =
      (X.vertexSplit hz a').data.vertexOf (Sum.inr 0) :=
    PlabicData.vertexOf_vertexSplit_inl_self X.data t (by omega) (by omega)
  have hz2 : ¬(X.vertexSplit hz a').data.IsBoundaryVertex
      ((X.vertexSplit hz a').data.vertexOf (Sum.inl t)) := by
    rw [hv2]
    exact X.data.not_isBoundaryVertex_vertexSplit_inr t a' hz (by omega) (by omega) 0
  have hc2 : ((X.vertexSplit hz a').data.vertexOf (Sum.inl t)).card = a' + 1 := by
    rw [hv2]
    exact X.data.card_vertexOf_vertexSplit_inr_zero t a' (by omega) (by omega)
  have s1 := resolutionStep_vertexSplit hA hz1 (p := a' - a + 1) (by omega) (by rw [hc1]; omega)
  have s2 := resolutionStep_vertexSplit hB hz2 (p := a) ha (by rw [hc2]; omega)
  exact Linked.of_common (hS t hz a ha (by omega)) (hS t hz a' (by omega) hak) hA hB s1 s2
    ⟨(PlabicData.vertexSplitNestedIso (K := X.data) (by omega) haa (by omega)).symm⟩

/-- A diagonal determines its splitting. -/
private theorem linked_sameDiag (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card)
    (hS : SplitsSelfLinked X) {t u : X.Dart} (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf t))
    (hzu : ¬X.data.IsBoundaryVertex (X.data.vertexOf u)) {p q : ℕ} (hp : 2 ≤ p)
    (hpk : p + 2 ≤ (X.data.vertexOf t).card) (hu : u = (X.data.rot ^ p) t)
    (hq : q = (X.data.vertexOf t).card - p) :
    Linked (X.vertexSplit hz p) (X.vertexSplit hzu q) := by
  subst hu hq
  have hvu := vertexOf_eq_of_sameCycle (s := t) (u := (X.data.rot ^ p) t)
    (sameCycle_pow_right.2 (SameCycle.refl _ _))
  exact Linked.of_isomorphic (hS t hz p hp hpk) (hS _ hzu _ (by omega) (by rw [hvu]; omega))
    (thick_vertexSplit hX hz hp hpk)
    ⟨(PlabicData.vertexSplitSameDiagIso X.isPlabicGraph hz (by omega) (by omega)).symm⟩

/-- At a vertex with four darts, the two splittings are related by a flip. -/
private theorem linked_four (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card)
    (hS : SplitsSelfLinked X) {t u : X.Dart} (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf t))
    (hzu : ¬X.data.IsBoundaryVertex (X.data.vertexOf u)) (hk : (X.data.vertexOf t).card = 4)
    (hu : u = X.data.rot t) : Linked (X.vertexSplit hz 2) (X.vertexSplit hzu 2) := by
  subst hu
  have hY := thick_vertexSplit hX hz le_rfl (by omega)
  have hf := PlabicData.isFlipEdge_vertexSplit_two hz hk
  obtain ⟨R, R', hR, hR', hRR'⟩ := exists_isResolution_flipMove (X.vertexSplit hz 2) hY hf
  have hiso : (X.vertexSplit hzu 2).Isomorphic ((X.vertexSplit hz 2).flipMove hf) :=
    PlabicData.Isomorphic.symm _
      (PlabicData.isomorphic_flipMove_vertexSplit_two X.isPlabicGraph hz hk)
  have hvu : X.data.vertexOf (X.data.rot t) = X.data.vertexOf t := X.data.vertexOf_rot t
  exact Linked.of_exists (hS t hz 2 le_rfl (by omega)) (hS _ hzu 2 le_rfl (by rw [hvu]; omega))
    hR (hR'.of_isomorphic hiso) hRR'

/-- Splittings at distinct vertices have a common splitting. -/
private theorem linked_comm (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card)
    (hS : SplitsSelfLinked X) {s s' : X.Dart} (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf s))
    (hz' : ¬X.data.IsBoundaryVertex (X.data.vertexOf s')) (hss : ¬X.data.rot.SameCycle s s')
    {p p' : ℕ} (hp : 2 ≤ p) (hpk : p + 2 ≤ (X.data.vertexOf s).card) (hp' : 2 ≤ p')
    (hpk' : p' + 2 ≤ (X.data.vertexOf s').card) :
    Linked (X.vertexSplit hz p) (X.vertexSplit hz' p') := by
  have hss' : ¬X.data.rot.SameCycle s' s := fun h => hss h.symm
  have hA := thick_vertexSplit hX hz hp hpk
  have hB := thick_vertexSplit hX hz' hp' hpk'
  have hv1 : (X.data.vertexSplit s p).vertexOf (Sum.inl s') =
      (X.data.vertexOf s').map Embedding.inl := X.data.vertexOf_vertexSplit_inl s p hss
  have hv2 : (X.data.vertexSplit s' p').vertexOf (Sum.inl s) =
      (X.data.vertexOf s).map Embedding.inl := X.data.vertexOf_vertexSplit_inl s' p' hss'
  have hz1 : ¬(X.data.vertexSplit s p).IsBoundaryVertex
      ((X.data.vertexSplit s p).vertexOf (Sum.inl s')) := by
    rw [hv1, PlabicData.isBoundaryVertex_map_inl_iff]
    exact hz'
  have hz2 : ¬(X.data.vertexSplit s' p').IsBoundaryVertex
      ((X.data.vertexSplit s' p').vertexOf (Sum.inl s)) := by
    rw [hv2, PlabicData.isBoundaryVertex_map_inl_iff]
    exact hz
  have s1 := resolutionStep_vertexSplit (X := X.vertexSplit hz p) hA hz1 hp' (by
    change p' + 2 ≤ ((X.data.vertexSplit s p).vertexOf (Sum.inl s')).card
    rw [hv1, card_map]
    exact hpk')
  have s2 := resolutionStep_vertexSplit (X := X.vertexSplit hz' p') hB hz2 hp (by
    change p + 2 ≤ ((X.data.vertexSplit s' p').vertexOf (Sum.inl s)).card
    rw [hv2, card_map]
    exact hpk)
  exact Linked.of_common (hS s hz p hp hpk) (hS s' hz' p' hp' hpk') hA hB s1 s2
    ⟨(PlabicData.vertexSplitCommIso hss p p').symm⟩

/-- The splittings of size `2` from consecutive darts of a vertex are linked. -/
private theorem linked_adjacent (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card)
    (hS : SplitsSelfLinked X) {t u : X.Dart} (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf t))
    (hzu : ¬X.data.IsBoundaryVertex (X.data.vertexOf u)) (hk : 4 ≤ (X.data.vertexOf t).card)
    (hu : u = X.data.rot t) : Linked (X.vertexSplit hz 2) (X.vertexSplit hzu 2) := by
  set k := (X.data.vertexOf t).card with hkdef
  rcases (show k = 4 ∨ 5 ≤ k by omega) with h4 | h5
  · exact linked_four hX hS hz hzu h4 hu
  have hv : ∀ n : ℕ, X.data.vertexOf ((X.data.rot ^ n) t) = X.data.vertexOf t := fun n =>
    vertexOf_eq_of_sameCycle (sameCycle_pow_right.2 (SameCycle.refl _ _))
  have hz3 : ¬X.data.IsBoundaryVertex (X.data.vertexOf ((X.data.rot ^ 3) t)) := by
    rw [hv]
    exact hz
  have hvu : X.data.vertexOf u = X.data.vertexOf t := by rw [hu, X.data.vertexOf_rot]
  have L1 := linked_nested hX hS hz (a := 2) (a' := 3) le_rfl (by norm_num) (by omega)
  have L2 := linked_sameDiag hX hS hz hz3 (p := 3) (q := k - 3) (by norm_num) (by omega) rfl rfl
  have L3 := linked_nested hX hS hz3 (a := k - 3) (a' := k - 2) (by omega) (by omega)
    (by rw [hv]; omega)
  have L4 := linked_sameDiag hX hS hzu hz3 (p := 2) (q := k - 2) le_rfl (by rw [hvu]; omega)
    (by rw [hu, ← Perm.mul_apply, ← pow_succ]) (by rw [hvu])
  have t3 : ∀ q, 2 ≤ q → q + 2 ≤ k → ∀ v ∈ (X.vertexSplit hz3 q).data.internalVertices,
      3 ≤ v.card := fun q hq hqk => thick_vertexSplit hX hz3 hq (by rw [hv]; omega)
  exact L1.trans (thick_vertexSplit hX hz (by norm_num) (by omega))
    (L2.trans (t3 _ (by omega) (by omega)) (L3.trans (t3 _ (by omega) (by omega)) L4.symm))

/-- The splittings of size `2` from any two darts of a vertex are linked. -/
private theorem linked_pow (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card)
    (hS : SplitsSelfLinked X) {t : X.Dart} (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf t))
    (hk : 4 ≤ (X.data.vertexOf t).card) (n : ℕ) :
    ∀ (u : X.Dart) (hzu : ¬X.data.IsBoundaryVertex (X.data.vertexOf u)),
      u = (X.data.rot ^ n) t → Linked (X.vertexSplit hz 2) (X.vertexSplit hzu 2) := by
  have hv : ∀ n : ℕ, X.data.vertexOf ((X.data.rot ^ n) t) = X.data.vertexOf t := fun n =>
    vertexOf_eq_of_sameCycle (sameCycle_pow_right.2 (SameCycle.refl _ _))
  induction n with
  | zero =>
    intro u hzu hu
    rw [pow_zero, Perm.one_apply] at hu
    subst hu
    exact hS u hz 2 le_rfl (by omega)
  | succ n ih =>
    intro u hzu hu
    have hzn : ¬X.data.IsBoundaryVertex (X.data.vertexOf ((X.data.rot ^ n) t)) := by
      rw [hv]
      exact hz
    exact (ih _ hzn rfl).trans (thick_vertexSplit hX hzn le_rfl (by rw [hv]; omega))
      (linked_adjacent hX hS hzn hzu (by rw [hv]; omega)
        (by rw [hu, pow_succ', Perm.mul_apply]))

/-- **Any two splittings of size `p ∈ [2, k - 2]` of the vertices of `X` are linked.** -/
private theorem linked_vertexSplit (hX : ∀ v ∈ X.data.internalVertices, 3 ≤ v.card)
    (hS : SplitsSelfLinked X) {s s' : X.Dart}
    (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf s))
    (hz' : ¬X.data.IsBoundaryVertex (X.data.vertexOf s')) {p p' : ℕ} (hp : 2 ≤ p)
    (hpk : p + 2 ≤ (X.data.vertexOf s).card) (hp' : 2 ≤ p')
    (hpk' : p' + 2 ≤ (X.data.vertexOf s').card) :
    Linked (X.vertexSplit hz p) (X.vertexSplit hz' p') := by
  by_cases hss : X.data.rot.SameCycle s s'
  · have hv := vertexOf_eq_of_sameCycle hss
    have L0 : Linked (X.vertexSplit hz p) (X.vertexSplit hz 2) := by
      rcases eq_or_lt_of_le hp with h2 | h2
      · subst h2
        exact hS s hz 2 le_rfl hpk
      · exact (linked_nested hX hS hz le_rfl h2 hpk).symm
    have L0' : Linked (X.vertexSplit hz' 2) (X.vertexSplit hz' p') := by
      rcases eq_or_lt_of_le hp' with h2 | h2
      · subst h2
        exact hS s' hz' 2 le_rfl hpk'
      · exact linked_nested hX hS hz' le_rfl h2 hpk'
    obtain ⟨n, hn⟩ := hss.exists_nat_pow_eq
    have L1 := linked_pow hX hS hz (by omega) n s' hz' hn.symm
    exact L0.trans (thick_vertexSplit hX hz le_rfl (by omega))
      (L1.trans (thick_vertexSplit hX hz' le_rfl (by omega)) L0')
  · exact linked_comm hX hS hz hz' hss hp hpk hp' hpk'

end SplitLinks

/-- **Any two resolutions are related by flips**. If `T` and
`T'` are resolutions of a plabic graph `X` (whose internal vertices then have at least three
darts), then `T` and `T'` are `{M4}`-connected. -/
@[cluster_algebras "lem_resolutions_flip_connected"]
theorem IsResolution.trivalentConnected {X T T' : PlabicGraph b} (hT : X.IsResolution T)
    (hT' : X.IsResolution T') : TrivalentConnected {TrivalentMoveType.m4} T T' := by
  suffices h : ∀ n, ∀ X : PlabicGraph b, PlabicData.excess X.data = n → Linked X X from
    h _ X rfl T T' hT hT'
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn T T' hT hT'
  have hX := hT.thick
  have hS : ∀ (s : X.Dart) (hz : ¬X.data.IsBoundaryVertex (X.data.vertexOf s)) (p : ℕ),
      2 ≤ p → p + 2 ≤ (X.data.vertexOf s).card →
        Linked (X.vertexSplit hz p) (X.vertexSplit hz p) := fun s hz p hp hpk =>
    ih _ (hn ▸ (PlabicData.vertexSplit_thick_excess_lt X.data s hz hp hpk hX).2) _ rfl
  have hnot : X.IsTrivalent → ∀ Y, ¬ResolutionStep X Y := fun htri Y hY => by
    obtain ⟨s, hz, p, hp, hpk, -⟩ := hY.exists_isomorphic_vertexSplit
    rw [htri.card_vertexOf hz] at hpk
    omega
  rcases hT.cases with hTX | ⟨Y, hXY, hYT⟩ <;> rcases hT'.cases with hTX' | ⟨Y', hXY', hYT'⟩
  · exact TrivalentConnected.of_isomorphic hT.isTrivalent hT'.isTrivalent
      (PlabicData.Isomorphic.trans _ hTX' (PlabicData.Isomorphic.symm _ hTX))
  · obtain ⟨θ⟩ := hTX
    exact absurd hXY' (hnot (θ.isTrivalent hT.isTrivalent) Y')
  · obtain ⟨θ⟩ := hTX'
    exact absurd hXY (hnot (θ.isTrivalent hT'.isTrivalent) Y)
  · obtain ⟨s, hz, p, hp, hpk, hY⟩ := hXY.exists_isomorphic_vertexSplit
    obtain ⟨s', hz', p', hp', hpk', hY'⟩ := hXY'.exists_isomorphic_vertexSplit
    exact linked_vertexSplit hX hS hz hz' hp hpk hp' hpk' T T'
      (hYT.of_isomorphic (PlabicData.Isomorphic.symm _ hY))
      (hYT'.of_isomorphic (PlabicData.Isomorphic.symm _ hY'))

/-! ### The results of the section -/

/-- **Moves (M2) and (M3) between trivalent graphs are flips**: trivalent
plabic graphs that are `{M2, M3}`-equivalent are `{M4}`-connected. -/
@[cluster_algebras "prop_flip_moves"]
theorem MoveEquivalent.trivalentConnected {G G' : PlabicGraph b} (hG : G.IsTrivalent)
    (hG' : G'.IsTrivalent) (h : MoveEquivalent {LocalMoveType.m2, LocalMoveType.m3} G G') :
    TrivalentConnected {TrivalentMoveType.m4} G G' := by
  have h3 : ∀ v ∈ G.data.internalVertices, 3 ≤ v.card := fun v hv => (hG v hv).ge
  have h3' : ∀ v ∈ G'.data.internalVertices, 3 ≤ v.card := fun v hv => (hG' v hv).ge
  have hchain := h.exists_chain_m3 h3 h3'
  suffices key : ∀ Y, Relation.ReflTransGen (fun X Y : PlabicGraph b =>
      (∀ v ∈ X.data.internalVertices, 3 ≤ v.card) ∧ (∀ v ∈ Y.data.internalVertices, 3 ≤ v.card) ∧
        MoveStep {LocalMoveType.m3} X Y) G Y →
      ∀ T, Y.IsResolution T → TrivalentConnected {TrivalentMoveType.m4} G T from
    key G' hchain G' (IsResolution.self hG')
  intro Y hY
  induction hY with
  | refl => exact fun T hT => (IsResolution.self hG).trivalentConnected hT
  | @tail Y Z _ hYZ ih =>
    obtain ⟨hY3, hZ3, hst⟩ := hYZ
    have hcommon : ∃ R, Y.IsResolution R ∧ Z.IsResolution R := by
      rcases hst with hiso | ⟨t, ht, hloc⟩
      · obtain ⟨R, hR⟩ := exists_isResolution Y hY3
        exact ⟨R, hR, hR.of_isomorphic hiso⟩
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        rcases hloc with ⟨d, hd⟩ | ⟨d, hd⟩
        · obtain ⟨R, hR⟩ := exists_isResolution Y hY3
          exact ⟨R, hR, hR.head hZ3 ⟨hY3, d, hd⟩⟩
        · obtain ⟨R, hR⟩ := exists_isResolution Z hZ3
          exact ⟨R, hR.head hY3 ⟨hZ3, d, hd⟩, hR⟩
    obtain ⟨R, hRY, hRZ⟩ := hcommon
    exact fun T hT => (ih R hRY).trans (hRZ.trivalentConnected hT)

/-- An internal vertex with exactly two darts can be removed: its darts `d₁`, `d₂ = σ d₁` satisfy
`d̄₁ ≠ d₂`, since otherwise `v` would be a connected component of the graph, which also has a
boundary vertex. -/
private theorem isBivalentRemovable_of_card_eq_two {H' : Type*} [Fintype H'] [DecidableEq H']
    {G : PlabicData H' b} (hG : G.IsPlabicGraph) {d : H'} (hdi : G.vertexOf d ∈ G.internalVertices)
    (hd2 : (G.vertexOf d).card = 2) : G.IsBivalentRemovable d := by
  refine ⟨G.vertexOf_mem_internalVertices.1 hdi, hd2, fun h => ?_⟩
  have hdr : G.rot d ≠ d := fun h' => hG.inv_ne d (h.trans h')
  have hS : ({d, G.rot d} : Finset H') = G.vertexOf d := by
    refine eq_of_subset_of_card_le (fun e he => ?_) (by rw [hd2, card_pair hdr.symm])
    rcases mem_insert.1 he with h' | h'
    · rw [h']
      exact G.self_mem_vertexOf _
    · rw [mem_singleton.1 h']
      exact G.rot_mem_vertexOf _
  have key : ∀ z, G.Reach d z → z ∈ G.vertexOf d := by
    intro z hz
    induction hz with
    | refl => exact G.self_mem_vertexOf _
    | @rot e _ ih' =>
      rw [← G.vertexOf_eq_of_mem ih']
      exact G.rot_mem_vertexOf _
    | @inv e _ ih' =>
      rw [← hS] at ih' ⊢
      rcases mem_insert.1 ih' with h' | h'
      · rw [h', h]
        exact mem_insert_of_mem (mem_singleton_self _)
      · rw [mem_singleton.1 h', ← h, hG.inv_involutive]
        exact mem_insert_self _ _
  obtain ⟨z, -, hzB⟩ := G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem ⟨0, hG.one_le⟩)
  have hz := key z (hG.reach d z)
  exact G.vertexOf_mem_internalVertices.1 hdi
    (G.vertexOf_eq_of_mem hz ▸ G.isBoundaryVertex_vertexOf_of_mem hzB)

/-- **A plabic graph without internal leaves can be made trivalent**:
if no internal vertex of the plabic graph `G` consists of exactly one dart, there is a sequence
`G = G₀, G₁, …, G_r` of plabic graphs without internal leaves, with `G_r` trivalent, in which each
`G_t` is isomorphic to `G_{t-1}` or obtained from it by a local move of type (M2) or (M3). -/
@[cluster_algebras "lem_trivalent_reduction"]
theorem exists_trivalent_of_forall_not_isInternalLeaf (G : PlabicGraph b)
    (hG : ∀ v, ¬G.data.IsInternalLeaf v) :
    ∃ G' : PlabicGraph b, G'.IsTrivalent ∧ Relation.ReflTransGen
      (fun X Y : PlabicGraph b => (∀ v, ¬Y.data.IsInternalLeaf v) ∧
        MoveStep {LocalMoveType.m2, LocalMoveType.m3} X Y) G G' := by
  suffices h : ∀ n, ∀ G : PlabicGraph b, Fintype.card G.Dart = n →
      (∀ v, ¬G.data.IsInternalLeaf v) → ∃ G' : PlabicGraph b, G'.IsTrivalent ∧
        Relation.ReflTransGen (fun X Y : PlabicGraph b => (∀ v, ¬Y.data.IsInternalLeaf v) ∧
          MoveStep {LocalMoveType.m2, LocalMoveType.m3} X Y) G G' from h _ G rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn hG
  by_cases h2 : ∃ d, G.data.vertexOf d ∈ G.data.internalVertices ∧ (G.data.vertexOf d).card = 2
  · obtain ⟨d, hdi, hd2⟩ := h2
    have hd := isBivalentRemovable_of_card_eq_two G.isPlabicGraph hdi hd2
    let G₁ : PlabicGraph b :=
      { Dart := ({d, G.data.rot d}ᶜ : Set G.Dart)
        data := G.data.bivalentRemoval G.isPlabicGraph hd
        isPlabicGraph := PlabicData.isPlabicGraph_bivalentRemoval G.isPlabicGraph hd }
    have hG₁ : ∀ v, ¬G₁.data.IsInternalLeaf v := by
      rintro v ⟨hv, hv1⟩
      obtain ⟨hvV, hvB⟩ := (DiskMap.mem_internalVertices _).1 hv
      obtain ⟨y, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
      have hmap := PlabicData.map_bivalentRemoval_vertexOf G.isPlabicGraph hd y
      have hb := PlabicData.isBoundaryVertex_bivalentRemoval_vertexOf_iff G.isPlabicGraph hd y
      refine hG _ ⟨G.data.vertexOf_mem_internalVertices.2 fun h => hvB (hb.2 h), ?_⟩
      rwa [← hmap, card_map]
    have hcard : Fintype.card G₁.Dart < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := d) (by simp)
    obtain ⟨G', hG', hseq⟩ := ih _ hcard G₁ rfl hG₁
    refine ⟨G', hG', Relation.ReflTransGen.head ⟨hG₁, Or.inr ⟨LocalMoveType.m2, by simp,
      Or.inl ⟨d, hd, PlabicData.Isomorphic.refl _⟩⟩⟩ hseq⟩
  · have h3 : ∀ v ∈ G.data.internalVertices, 3 ≤ v.card := by
      intro v hv
      obtain ⟨d, rfl⟩ := G.data.mem_vertices.1 (mem_filter.1 hv).1
      have h0 : 0 < (G.data.vertexOf d).card := card_pos.2 ⟨d, G.data.self_mem_vertexOf d⟩
      have hne1 : (G.data.vertexOf d).card ≠ 1 := fun h => hG _ ⟨hv, h⟩
      have hne2 : (G.data.vertexOf d).card ≠ 2 := fun h => h2 ⟨d, hv, h⟩
      omega
    obtain ⟨T, -, hT, Y, hGY, hTY⟩ := exists_isResolution G h3
    refine ⟨T, hT, Relation.ReflTransGen.tail (b := Y) ?_ ⟨?_, Or.inl hTY⟩⟩
    · refine Relation.ReflTransGen.mono (fun X Z hXZ => ⟨?_, ?_⟩) hGY
      · rintro v ⟨hv, hv1⟩
        have := hXZ.1 v hv
        omega
      · obtain ⟨-, d, hd⟩ := hXZ
        exact Or.inr ⟨LocalMoveType.m3, by simp, Or.inr ⟨d, hd⟩⟩
    · rintro v ⟨hv, hv1⟩
      rw [hT v hv] at hv1
      omega

end PlabicGraph

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

end PlabicData

end ClusterAlgebras

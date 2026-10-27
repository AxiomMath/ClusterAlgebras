/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.MinimalTriple
public import ClusterAlgebras.Plabic.Winding
public import ClusterAlgebras.Plabic.FirstReturn

/-!
# Closed strands, returning paths and the removal of hollow monogons

This file collects several steps of D. Thurston's theory of minimal triple diagrams.

*Closed strands.* The darts of a closed strand `C` of `out` darts in a triple diagram without
monogons form a simple closed walk, and its winding function `h` separates the two sides of `C`:
a strand path crossing `C` at a triple point changes the value of `h`, while a strand path that
does not meet `C` keeps it. Following an arc or a closed strand `T` that meets `C` therefore gives
a second crossing, hence a parallel digon whose paths run along `C` and along `T`. As a
consequence a triple diagram without badgons has no closed strands.

*Returning paths and side lists.* A parallel returning path of a simple strand path gives a
parallel digon; the entries of a side list come in pairs at the interior points; local
replacements of the rotation preserve the sets of darts reachable on one side of a strand path;
and a strand path with a returning path has one whose ends enclose no other returning path.

*Swivel moves.* Away from the four darts of the digon, a swivel move changes the strand map only
by inserting or deleting one of these darts.

*Hollow monogons.* If `{c}` is a hollow monogon at the triple point `x`, whose rotation is
`(c̄, c, a₁, a₂, a₃, a₄)`, its removal deletes `x` and joins the remaining ends of the edges at
`x` through the involution `μ` of `x` exchanging `c̄ ↔ c`, `a₂ ↔ a₃` and `a₁ ↔ a₄`, keeping the
part of the diagram reachable from the boundary. It is a triple diagram with the same strand
permutation and fewer triple points; so a triple diagram with a hollow monogon is not minimal.

## Main definitions

* `ClusterAlgebras.TripleData.hollowInv`, `ClusterAlgebras.TripleData.hollowRemoval`: the
  removal of a hollow monogon.

## Main results

* `ClusterAlgebras.TripleData.exists_isParallelDigon_of_isClosedStrand`: a closed strand is
  crossed twice.
* `ClusterAlgebras.TripleData.not_isClosedStrand_of_not_hasBadgon`: no badgons, no closed strands.
* `ClusterAlgebras.TripleData.IsReturningPath.hasParallelDigon`: a parallel returning path gives a
  parallel digon.
* `ClusterAlgebras.TripleData.exists_getElem?_sideList`,
  `ClusterAlgebras.TripleData.inv_rot_pow_two_getElem?_sideList`: consecutive entries of a side
  list.
* `ClusterAlgebras.TripleData.reach_of_local_replacement`: sides after a local replacement.
* `ClusterAlgebras.TripleData.exists_isReturningPath_minimal`: a minimal returning arc.
* `ClusterAlgebras.TripleData.exists_iterate_strandMap_swivelMove`: swivel moves preserve strands
  away from the digon.
* `ClusterAlgebras.TripleData.isTripleDiagram_hollowRemoval`,
  `ClusterAlgebras.TripleData.strandPerm_hollowRemoval'`,
  `ClusterAlgebras.TripleData.card_internalVertices_hollowRemoval_lt'`: removing a hollow monogon.
* `ClusterAlgebras.TripleDiagram.not_isMinimal_of_isHollowMonogon`: a hollow monogon is not
  minimal.

## Implementation notes

* Positions in lists are `0`-indexed, as in `ClusterAlgebras.Plabic.MinimalTriple`: the
  interior point `z_{l+1}` of a strand path `P` is `v(P[l]̄)`, and the `ζ` list
  `(λ₀, λ₁, …)` is `sideList ζ P`.
* A dart lies *strictly between* two darts `f, g` of a list `L` when its first position lies
  strictly between the first positions of `f` and `g` (`List.idxOf`), as in `hugDarts`.
* The darts of `x` are written `σᵏ c`, `k ∈ [0, 5]`, so that `a_k = σᵏ c` and `c̄ = σ⁵ c`.
* The involution `ι°` of `H° = H \ x` is the first-return map of `d ↦ μ(d)̄` to `H°`
  (`ClusterAlgebras.firstReturn`): the first dart outside `x` of the sequence
  `d̄, μ(d̄)̄, μ(μ(d̄)̄)̄, …` of FWZ. It is extended by the identity on `x`. The darts of
  the removal are those reachable from `B` under `σ` and `ι°`; since all of `B` is reachable from
  any of its darts, this is FWZ's orbit of `B`.
* Euler's relation for the removal is proved by counting orbits: the faces of `H°` are those of
  the first-return map `ψ` of `φ` to `H°`, up to one transposition `(ā₃ ā₁)` when no edge other
  than the loop has both ends at `x`, and equal to it otherwise; when the part of `H°` not
  reachable from `B` is nonempty, it is a connected rotation system, and Euler's bound applies to
  both parts.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)

/-! ### Side darts -/

omit [Fintype H] [DecidableEq H] in
/-- A side dart of a strand path at `v(ē)` is `σᵏ(ē)` for some `k ∈ {1, 2, 4, 5}`. -/
private theorem exists_eq_of_mem_sideDarts {ζ : StrandSide} {e f : H}
    (hf : f ∈ X.sideDarts ζ e) :
    ∃ k : ℕ, (k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 5) ∧ f = (X.rot ^ k) (X.inv e) := by
  cases ζ <;> simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hf <;>
    rcases hf with rfl | rfl
  · exact ⟨1, by simp, by rw [pow_one]⟩
  · exact ⟨2, by simp, rfl⟩
  · exact ⟨4, by simp, rfl⟩
  · exact ⟨5, by simp, rfl⟩

/-- A side dart of a strand path at `v(ē)` lies at `v(ē)`. -/
private theorem vertexOf_of_mem_sideDarts {ζ : StrandSide} {e f : H}
    (hf : f ∈ X.sideDarts ζ e) : X.vertexOf f = X.vertexOf (X.inv e) := by
  obtain ⟨k, -, rfl⟩ := X.exists_eq_of_mem_sideDarts hf
  exact X.vertexOf_rot_pow_apply k _

/-- At a triple point `v(ē)`, a side dart is neither `ē` nor `σ³ ē`. -/
private theorem ne_of_mem_sideDarts {X : TripleData H b} (hX : X.IsPreTripleDiagram)
    {ζ : StrandSide} {e f : H} (he : ¬X.IsBoundaryVertex (X.vertexOf (X.inv e)))
    (hf : f ∈ X.sideDarts ζ e) : f ≠ X.inv e ∧ f ≠ (X.rot ^ 3) (X.inv e) := by
  obtain ⟨k, hk, rfl⟩ := X.exists_eq_of_mem_sideDarts hf
  have h6 := (hX.rot_pow_six he).2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h6 k 0 (by omega) (by omega) (by simpa using h)
    omega
  · have := h6 k 3 (by omega) (by omega) h
    omega

omit [Fintype H] [DecidableEq H] in
/-- A dart of the `ζ` list of `P` is a side dart at `v(ē)` for a dart `e` of `P`. -/
private theorem exists_of_mem_sideList {ζ : StrandSide} {P : List H} {d : H}
    (hd : d ∈ X.sideList ζ P) : ∃ e ∈ P, d ∈ X.sideDarts ζ e := by
  cases ζ <;> simp only [sideList, List.mem_flatMap, List.mem_reverse] at hd <;>
    obtain ⟨e, he, hde⟩ := hd <;> exact ⟨e, List.dropLast_subset _ he, hde⟩

/-! ### A parallel returning path gives a parallel digon -/

/-- If `Q` is a returning path of the simple strand path `P = (e₁, …, e_m)` from `z_{a+1}` to
`z_{b+1}` with `a < b` (`0`-indexed), then `X` has a parallel digon, namely
`((e_{a+2}, …, e_{b+1}), Q)`. -/
@[cluster_algebras "lem_returning_parallel_digon"]
theorem IsReturningPath.hasParallelDigon {X : TripleData H b} (hX : X.IsPreTripleDiagram)
    {P Q : List H} {ζ : StrandSide} {a c : ℕ} (hQ : X.IsReturningPath P ζ Q a c) (hac : a < c) :
    X.HasParallelDigon := by
  have hPs := hQ.isSimpleStrandPath
  have hP := (X.isStrandPath_iff_getElem.1 hPs.isStrandPath)
  have hcl := hQ.lt_right
  have hal := hQ.lt_left
  -- the stretch `(e_{a+2}, …, e_{c+1})` of `P`
  set P' : List H := (P.drop (a + 1)).take (c - a) with hP'
  have hlen : P'.length = c - a := by simp [hP']; omega
  have hget : ∀ (t : ℕ) (ht : t < P'.length), P'[t] = P[a + 1 + t]'(by omega) := by
    intro t ht
    simp [hP']
  have hP'path : X.IsStrandPath P' := by
    rw [isStrandPath_iff_getElem]
    refine ⟨fun h => by simp [h] at hlen; omega, fun t ht => ?_, fun t ht => ?_⟩
    · rw [hget]
      exact hP.2.1 _ _
    · rw [hget, hget]
      exact hP.2.2 (a + 1 + t) (by omega)
  have hsa := hP.2.2 a (by omega)
  have hsc := hP.2.2 c (by omega)
  -- the corners
  set x := X.vertexOf (X.inv P[a]) with hx
  set y := X.vertexOf (X.inv P[c]) with hy
  have hxy : x ≠ y := by
    intro h
    have hnd := hPs.nodup
    have := (hnd.getElem_inj_iff (i := a) (j := c) (hi := by simp [interiorPoints]; omega)
      (hj := by simp [interiorPoints]; omega)).1 (by simpa [interiorPoints] using h)
    omega
  obtain ⟨e₁, he₁, f₁, hf₁, hf₁s⟩ := hQ.head?_mem
  obtain ⟨e₂, he₂, f₂, hf₂, hf₂s⟩ := hQ.getLast?_mem
  rw [List.getElem?_eq_getElem (by omega), Option.mem_def, Option.some_inj] at he₁ he₂
  subst he₁ he₂
  have hP'head : P'.head? = some P[a + 1] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega), hget]
  have hP'last : P'.getLast? = some P[c] := by
    rw [List.getLast?_eq_getElem?, hlen, List.getElem?_eq_getElem (by omega), hget]
    congr 2
    omega
  refine ⟨P', Q, x, y, ⟨hxy, ?_, ?_, hP'path, hQ.isStrandPath, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact X.vertexOf_mem_internalVertices.2 hsa.1
  · exact X.vertexOf_mem_internalVertices.2 hsc.1
  · rw [X.pathStart_of_head? hP'head, hsa.vertexOf_eq]
  · rw [X.pathEnd_of_getLast? hP'last]
  · rw [X.pathStart_of_head? hf₁, X.vertexOf_of_mem_sideDarts hf₁s]
  · rw [X.pathEnd_of_getLast? hf₂, X.vertexOf_of_mem_sideDarts hf₂s]
  · rw [hP'head, hf₁]
    intro h
    rw [Option.some_inj] at h
    exact (ne_of_mem_sideDarts hX hsa.1 hf₁s).2 (by rw [← h, hsa.2])
  · rw [hP'last, hf₂]
    intro h
    rw [Option.some_inj] at h
    exact (ne_of_mem_sideDarts hX hsc.1 hf₂s).1 (by rw [h])

/-! ### Consecutive entries of a side list -/

/-- Entries of a list built from blocks of length two. -/
private theorem getElem?_flatMap_of_length_eq_two {α β : Type*} (f : α → List β)
    (hf : ∀ x, (f x).length = 2) :
    ∀ (L : List α) (u j : ℕ), j < 2 → (L.flatMap f)[2 * u + j]? = L[u]?.bind fun x => (f x)[j]?
  | [], u, j, _ => by simp
  | x :: L, 0, j, hj => by
    rw [List.flatMap_cons, List.getElem?_append_left (by rw [hf]; omega)]
    simp
  | x :: L, u + 1, j, hj => by
    rw [List.flatMap_cons, List.getElem?_append_right (by rw [hf]; omega), hf,
      show 2 * (u + 1) + j - 2 = 2 * u + j by omega,
      getElem?_flatMap_of_length_eq_two f hf L u j hj]
    simp

omit [Fintype H] [DecidableEq H] in
private theorem sideList_right_getElem? (P : List H) (u j : ℕ) (hj : j < 2) :
    (X.sideList .right P)[2 * u + j]? = P.dropLast[u]?.bind fun e => (X.sideDarts .right e)[j]? :=
  getElem?_flatMap_of_length_eq_two _ (fun x => by simp [sideDarts]) _ u j hj

omit [Fintype H] [DecidableEq H] in
private theorem sideList_left_getElem? (P : List H) (u j : ℕ) (hj : j < 2) :
    (X.sideList .left P)[2 * u + j]? =
      P.dropLast.reverse[u]?.bind fun e => (X.sideDarts .left e)[j]? :=
  getElem?_flatMap_of_length_eq_two _ (fun x => by simp [sideDarts]) _ u j hj

omit [Fintype H] [DecidableEq H] in
private theorem getElem?_dropLast_of_lt (P : List H) {u : ℕ} (hu : u + 2 ≤ P.length) :
    P.dropLast[u]? = P[u]? := by
  rw [List.getElem?_eq_getElem (by simp; omega), List.getElem?_eq_getElem (by omega),
    List.getElem_dropLast]

omit [Fintype H] [DecidableEq H] in
private theorem getElem?_dropLast_reverse (P : List H) {u : ℕ} (hu : u + 2 ≤ P.length) :
    P.dropLast.reverse[u]? = P[P.length - 2 - u]? := by
  rw [List.getElem?_reverse (by simp; omega)]
  simp only [List.length_dropLast, List.getElem?_dropLast]
  rw [if_pos (by omega), show P.length - 1 - 1 - u = P.length - 2 - u by omega]

/-- Let `P = (e₁, …, e_m)` be a strand path and `(λ₀, λ₁, …)` its `ζ` list. For `u ∈ [0, m - 2]`
the darts `λ_{2u}` and `λ_{2u+1} = σ(λ_{2u})` lie at one interior point `z_{l+1} = v(P[l]̄)` of `P`
(`0`-indexed `l`), with `σ⁻¹(λ_{2u}) = P[l]̄ = ē_{l+1}` if `ζ` is right and
`σ⁻¹(λ_{2u}) = P[l+1] = e_{l+2}` if `ζ` is left. (FWZ assume `P` simple; this is not
needed.) -/
@[cluster_algebras "lem_list_steps"]
theorem exists_getElem?_sideList {X : TripleData H b} {P : List H}
    (hP : X.IsStrandPath P) (ζ : StrandSide) {u : ℕ} (hu : u + 2 ≤ P.length) :
    ∃ l, ∃ hl : l + 1 < P.length, ∃ lam : H,
      (X.sideList ζ P)[2 * u]? = some lam ∧ (X.sideList ζ P)[2 * u + 1]? = some (X.rot lam) ∧
      X.vertexOf lam = X.vertexOf (X.inv P[l]) ∧
      X.rot.symm lam = (match ζ with
        | .right => X.inv P[l]
        | .left => P[l + 1]) := by
  have hP' := (X.isStrandPath_iff_getElem.1 hP).2.2
  cases ζ with
  | right =>
    have h0 := X.sideList_right_getElem? P u 0 (by omega)
    have h1 := X.sideList_right_getElem? P u 1 (by omega)
    rw [add_zero] at h0
    rw [getElem?_dropLast_of_lt P hu, List.getElem?_eq_getElem (l := P) (by omega)] at h0 h1
    refine ⟨u, by omega, X.rot (X.inv P[u]), ?_, ?_, ?_, ?_⟩
    · simpa [sideDarts] using h0
    · simpa [sideDarts, pow_two] using h1
    · exact X.vertexOf_rot _
    · simp
  | left =>
    have h0 := X.sideList_left_getElem? P u 0 (by omega)
    have h1 := X.sideList_left_getElem? P u 1 (by omega)
    rw [add_zero] at h0
    rw [getElem?_dropLast_reverse P hu, List.getElem?_eq_getElem (l := P) (by omega)] at h0 h1
    have hs := hP' (P.length - 2 - u) (by omega)
    refine ⟨P.length - 2 - u, by omega, (X.rot ^ 4) (X.inv P[P.length - 2 - u]), ?_, ?_, ?_, ?_⟩
    · simpa [sideDarts] using h0
    · simp only [sideDarts] at h1
      rw [h1]
      simp [pow_succ']
    · exact X.vertexOf_rot_pow_apply 4 _
    · simp only
      rw [hs.2, show (4 : ℕ) = 1 + 3 by rfl, pow_add, Equiv.Perm.mul_apply, pow_one,
        Equiv.symm_apply_apply]

/-- Let `(λ₀, λ₁, …)` be the `ζ` list of a strand path `P = (e₁, …, e_m)`. For `u ∈ [0, m - 3]`,
`(σ²(λ_{2u}))̄ = σ⁻¹(λ_{2u+2})`. -/
@[cluster_algebras "lem_list_steps"]
theorem inv_rot_pow_two_getElem?_sideList {X : TripleData H b} (hX : X.IsPreTripleDiagram)
    {P : List H} (hP : X.IsStrandPath P) (ζ : StrandSide) {u : ℕ} (hu : u + 3 ≤ P.length) :
    ∃ lam lam' : H, (X.sideList ζ P)[2 * u]? = some lam ∧
      (X.sideList ζ P)[2 * u + 2]? = some lam' ∧ X.inv ((X.rot ^ 2) lam) = X.rot.symm lam' := by
  have hP' := (X.isStrandPath_iff_getElem.1 hP).2.2
  cases ζ with
  | right =>
    have h0 := X.sideList_right_getElem? P u 0 (by omega)
    have h2 := X.sideList_right_getElem? P (u + 1) 0 (by omega)
    rw [add_zero] at h0 h2
    rw [show 2 * (u + 1) = 2 * u + 2 by ring] at h2
    rw [getElem?_dropLast_of_lt P (by omega), List.getElem?_eq_getElem (l := P) (by omega)] at h0 h2
    have hs := hP' u (by omega)
    refine ⟨X.rot (X.inv P[u]), X.rot (X.inv P[u + 1]), by simpa [sideDarts] using h0,
      by simpa [sideDarts] using h2, ?_⟩
    rw [Equiv.symm_apply_apply,
      show (X.rot ^ 2) (X.rot (X.inv P[u])) = (X.rot ^ 3) (X.inv P[u]) from rfl, ← hs.2]
  | left =>
    have h0 := X.sideList_left_getElem? P u 0 (by omega)
    have h2 := X.sideList_left_getElem? P (u + 1) 0 (by omega)
    rw [add_zero] at h0 h2
    rw [show 2 * (u + 1) = 2 * u + 2 by ring] at h2
    rw [getElem?_dropLast_reverse P (by omega),
      List.getElem?_eq_getElem (l := P) (by omega)] at h0 h2
    have hs := hP' (P.length - 2 - u) (by omega)
    have hs' := hP' (P.length - 2 - (u + 1)) (by omega)
    have hidx : P.length - 2 - (u + 1) + 1 = P.length - 2 - u := by omega
    refine ⟨(X.rot ^ 4) (X.inv P[P.length - 2 - u]),
      (X.rot ^ 4) (X.inv P[P.length - 2 - (u + 1)]), by simpa [sideDarts] using h0,
      by simpa [sideDarts] using h2, ?_⟩
    have h24 : ∀ y, (X.rot ^ 2) ((X.rot ^ 4) y) = (X.rot ^ 6) y := fun y => by
      rw [← Equiv.Perm.mul_apply, ← pow_add]
    rw [h24, hX.rot_pow_six_apply hs.1, hX.inv_inv_apply, show (4 : ℕ) = 1 + 3 by rfl, pow_add,
      Equiv.Perm.mul_apply, pow_one,
      Equiv.symm_apply_apply, ← hs'.2]
    simp only [hidx]

/-! ### Sides after a local replacement -/

/-- Let `X` and `X'` have the same involution and the same `B`, with rotations `σ`, `σ'` agreeing
outside a set `D` of darts that is a union of vertices of `X`. Let `P`, `P'` be sequences of darts
and `ζ` a side. Let `K` be closed under the involution and under `σ^{±1}` at triple points of `X`
that are not vertices of darts of `P` or of their reverses, and let `L' ⊆ D ∩ K` be such that the
involution maps `(D ∩ K) \ L'` into itself. Suppose that `L'` is contained in the `ζ` list of `P'`,
and that every triple point of `X` disjoint from `D` that is the vertex of a dart of `P` or of the
reverse of one is the vertex of a dart of `P'` or of the reverse of one. Then `(K \ D) ∪ L'` is
closed under the involution and under `σ'^{±1}` at triple points of `X'` that are not vertices of
darts of `P'` or of their reverses.

FWZ also assume that `X`, `X'` are triple diagrams with the same `ε` and `o`, that `P`,
`P'` are simple strand paths, that `D` is also a union of vertices of `X'`, that `K` contains the
`ζ` list of `P` and that the `ζ` list of `P'` is contained in `(K \ D) ∪ L'`; these hypotheses
are not needed. -/
@[cluster_algebras "lem_local_replacement_reach"]
theorem reach_of_local_replacement {X X' : TripleData H b} (hinv : X'.inv = X.inv)
    (hbdry : X'.bdry = X.bdry) (hXinv : Function.Involutive X.inv) {D : Finset H}
    (hrot : ∀ d ∉ D, X'.rot d = X.rot d) (hD : ∀ d ∈ D, X.vertexOf d ⊆ D) {P P' : List H}
    {ζ : StrandSide} {K L' : Finset H}
    (hKinv : ∀ d ∈ K, X.inv d ∈ K)
    (hKrot : ∀ d ∈ K, ¬X.IsBoundaryVertex (X.vertexOf d) →
      (∀ e ∈ P, X.vertexOf d ≠ X.vertexOf e ∧ X.vertexOf d ≠ X.vertexOf (X.inv e)) →
      X.rot d ∈ K ∧ X.rot.symm d ∈ K)
    (hL' : L' ⊆ D ∩ K) (hL'inv : ∀ d ∈ (D ∩ K) \ L', X.inv d ∈ (D ∩ K) \ L')
    (hL'list : ∀ d ∈ L', d ∈ X'.sideList ζ P')
    (hpts : ∀ v ∈ X.internalVertices, Disjoint v D →
      (∃ e ∈ P, v = X.vertexOf e ∨ v = X.vertexOf (X.inv e)) →
      ∃ e ∈ P', v = X'.vertexOf e ∨ v = X'.vertexOf (X'.inv e)) :
    (∀ d ∈ (K \ D) ∪ L', X'.inv d ∈ (K \ D) ∪ L') ∧
      ∀ d ∈ (K \ D) ∪ L', ¬X'.IsBoundaryVertex (X'.vertexOf d) →
        (∀ e ∈ P', X'.vertexOf d ≠ X'.vertexOf e ∧ X'.vertexOf d ≠ X'.vertexOf (X'.inv e)) →
        X'.rot d ∈ (K \ D) ∪ L' ∧ X'.rot.symm d ∈ (K \ D) ∪ L' := by
  have hKstar : ∀ d ∈ (K \ D) ∪ L', d ∈ K := by
    intro d hd
    rcases mem_union.1 hd with hd | hd
    · exact (mem_sdiff.1 hd).1
    · exact (mem_inter.1 (hL' hd)).2
  refine ⟨fun d hd => ?_, fun d hd hb hP' => ?_⟩
  · rw [hinv]
    have hK := hKinv d (hKstar d hd)
    by_cases hD₁ : X.inv d ∈ D
    · by_cases hL₁ : X.inv d ∈ L'
      · exact mem_union_right _ hL₁
      · exfalso
        have := hL'inv _ (mem_sdiff.2 ⟨mem_inter.2 ⟨hD₁, hK⟩, hL₁⟩)
        rw [hXinv d] at this
        obtain ⟨hdDK, hdL⟩ := mem_sdiff.1 this
        rcases mem_union.1 hd with hd | hd
        · exact (mem_sdiff.1 hd).2 (mem_inter.1 hdDK).1
        · exact hdL hd
    · exact mem_union_left _ (mem_sdiff.2 ⟨hK, hD₁⟩)
  -- `d` is not a `ζ` list dart of `P'`, so it lies in `K \ D`
  have hdL : d ∉ L' := by
    intro hdL
    obtain ⟨e, he, hde⟩ := X'.exists_of_mem_sideList (hL'list d hdL)
    exact (hP' e he).2 (X'.vertexOf_of_mem_sideDarts hde)
  have hdKD : d ∈ K \ D := by
    rcases mem_union.1 hd with hd | hd
    · exact hd
    · exact absurd hd hdL
  obtain ⟨hdK, hdD⟩ := mem_sdiff.1 hdKD
  -- the rotations agree along the vertex of `d`, which avoids `D`
  have hstep : ∀ y, y ∉ D → X.rot y ∉ D := by
    intro y hy hy'
    exact hy (hD _ hy' (by
      rw [RotationSystem.mem_vertexOf]
      exact (Equiv.Perm.SameCycle.refl X.rot y).symm.trans
        (Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)) |>.symm))
  have hpow : ∀ n : ℕ, (X'.rot ^ n) d = (X.rot ^ n) d ∧ (X.rot ^ n) d ∉ D := by
    intro n
    induction n with
    | zero => exact ⟨rfl, hdD⟩
    | succ n ih =>
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih.1, hrot _ ih.2]
      exact ⟨rfl, hstep _ ih.2⟩
  have hvert : X'.vertexOf d = X.vertexOf d := by
    ext e
    rw [RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf]
    constructor
    · intro h
      obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
      rw [(hpow n).1]
      exact ⟨n, by simp⟩
    · intro h
      obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
      rw [← (hpow n).1]
      exact ⟨n, by simp⟩
  have hdisj : Disjoint (X.vertexOf d) D := by
    rw [Finset.disjoint_left]
    intro e he
    obtain ⟨n, rfl⟩ := (X.mem_vertexOf.1 he).exists_nat_pow_eq
    exact (hpow n).2
  have hb' : ¬X.IsBoundaryVertex (X.vertexOf d) := by
    rwa [← hvert, DiskMap.IsBoundaryVertex, ← hbdry]
  have hnP : ∀ e ∈ P, X.vertexOf d ≠ X.vertexOf e ∧ X.vertexOf d ≠ X.vertexOf (X.inv e) := by
    intro e he
    by_contra hne
    rw [not_and_or, not_not, not_not] at hne
    obtain ⟨e', he', h'⟩ := hpts _ (X.vertexOf_mem_internalVertices.2 hb') hdisj ⟨e, he, hne⟩
    rw [← hvert] at h'
    exact h'.elim (hP' e' he').1 (hP' e' he').2
  obtain ⟨hr, hr'⟩ := hKrot d hdK hb' hnP
  have hrmem : X.rot d ∈ X.vertexOf d := X.rot_mem_vertexOf d
  have hrsmem : X.rot.symm d ∈ X.vertexOf d := X.rot_symm_mem_vertexOf d
  have hrs : X'.rot.symm d = X.rot.symm d := by
    rw [Equiv.symm_apply_eq, hrot _ (Finset.disjoint_left.1 hdisj hrsmem),
      Equiv.apply_symm_apply]
  rw [hrot d hdD, hrs]
  exact ⟨mem_union_left _ (mem_sdiff.2 ⟨hr, Finset.disjoint_left.1 hdisj hrmem⟩),
    mem_union_left _ (mem_sdiff.2 ⟨hr', Finset.disjoint_left.1 hdisj hrsmem⟩)⟩

/-! ### A minimal returning arc -/

/-- If the sequence of darts `P` has a returning path on side `ζ`, then it has a returning path
`Q` on side `ζ` such that no returning path `Q'` of `P` on side `ζ` has both its first dart and the
reverse of its last dart strictly between the first dart of `Q` and the reverse of the last dart of
`Q` in the list `L = X.sideList ζ P` (a dart `z` lies strictly between `f` and `g` when its
position `L.idxOf z` lies strictly between `L.idxOf f` and `L.idxOf g`). -/
@[cluster_algebras "lem_minimal_returning_arc"]
theorem exists_isReturningPath_minimal {P : List H} {ζ : StrandSide}
    (h : ∃ Q a c, X.IsReturningPath P ζ Q a c) :
    ∃ Q a c, X.IsReturningPath P ζ Q a c ∧
      ∀ Q' a' c', X.IsReturningPath P ζ Q' a' c' →
        ∀ f ∈ Q.head?, ∀ g ∈ Q.getLast?, ∀ f' ∈ Q'.head?, ∀ g' ∈ Q'.getLast?,
          let L := X.sideList ζ P
          let i := L.idxOf f
          let j := L.idxOf (X.inv g)
          ¬((min i j < L.idxOf f' ∧ L.idxOf f' < max i j) ∧
            (min i j < L.idxOf (X.inv g') ∧ L.idxOf (X.inv g') < max i j)) := by
  classical
  have hex : ∃ n, ∃ Q a c f g, X.IsReturningPath P ζ Q a c ∧ Q.head? = some f ∧
      Q.getLast? = some g ∧ max ((X.sideList ζ P).idxOf f) ((X.sideList ζ P).idxOf (X.inv g)) -
        min ((X.sideList ζ P).idxOf f) ((X.sideList ζ P).idxOf (X.inv g)) = n := by
    obtain ⟨Q, a, c, hQ⟩ := h
    have hne := hQ.isStrandPath.ne_nil
    exact ⟨_, Q, a, c, Q.head hne, Q.getLast hne, hQ, List.head?_eq_some_head hne,
      List.getLast?_eq_some_getLast hne, rfl⟩
  obtain ⟨Q, a, c, f, g, hQ, hf, hg, hn⟩ := Nat.find_spec hex
  refine ⟨Q, a, c, hQ, fun Q' a' c' hQ' f₁ hf₁ g₁ hg₁ f' hf' g' hg' => ?_⟩
  rw [Option.mem_def] at hf₁ hg₁ hf' hg'
  rw [hf, Option.some_inj] at hf₁
  rw [hg, Option.some_inj] at hg₁
  subst hf₁ hg₁
  dsimp only
  rintro ⟨⟨h1, h2⟩, h3, h4⟩
  have hlt : max ((X.sideList ζ P).idxOf f') ((X.sideList ζ P).idxOf (X.inv g')) -
      min ((X.sideList ζ P).idxOf f') ((X.sideList ζ P).idxOf (X.inv g')) < Nat.find hex := by
    rw [← hn]
    omega
  exact Nat.find_min hex hlt ⟨Q', a', c', f', g', hQ', hf', hg', rfl⟩

/-! ### Closed strands -/

section ClosedStrands

variable {X}

/-- A step of the strand map at a dart not running to an endpoint is a strand step. -/
private theorem strandStep_strandMap {d : H} (hr : ¬X.RunsToEndpoint d) :
    X.StrandStep d (X.strandMap d) :=
  ⟨hr, by rw [X.strandMap_of_not_runsToEndpoint hr]; rfl⟩

/-- Along the strand map from a dart `d ∉ B`, as long as no endpoint is reached, the darts are not
in `B` and have the orientation of `d`. -/
private theorem iterate_notMem_bdry_isOut (hX : X.IsPreTripleDiagram) {d : H} (hd : d ∉ X.bdry)
    {n : ℕ} (hr : ∀ k < n, ¬X.RunsToEndpoint (X.strandMap^[k] d)) :
    ∀ k ≤ n, X.strandMap^[k] d ∉ X.bdry ∧ X.isOut (X.strandMap^[k] d) = X.isOut d := by
  intro k hk
  induction k with
  | zero => exact ⟨hd, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hs := strandStep_strandMap (hr k (by omega))
    rw [Function.iterate_succ_apply']
    exact ⟨hs.notMem_bdry, (hs.isOut_eq hX h1).trans h2⟩

/-- A stretch `(S^s d, …, S^{s+n-1} d)` of darts along the strand map is a strand path. -/
private theorem isStrandPath_map_iterate {d : H} {s n : ℕ} (hn : n ≠ 0)
    (hB : ∀ k, s ≤ k → k < s + n →
      X.strandMap^[k] d ∉ X.bdry ∧ X.isOut (X.strandMap^[k] d) = true)
    (hr : ∀ k, s ≤ k → k + 1 < s + n → ¬X.RunsToEndpoint (X.strandMap^[k] d)) :
    X.IsStrandPath ((List.range' s n).map fun k => X.strandMap^[k] d) := by
  rw [isStrandPath_iff_getElem]
  refine ⟨by simp [hn], fun t ht => ?_, fun t ht => ?_⟩
  · simp only [List.length_map, List.length_range'] at ht
    simp only [List.getElem_map, List.getElem_range', one_mul]
    exact hB _ (by omega) (by omega)
  · simp only [List.length_map, List.length_range'] at ht
    simp only [List.getElem_map, List.getElem_range', one_mul]
    rw [show s + (t + 1) = s + t + 1 by ring, Function.iterate_succ_apply']
    exact strandStep_strandMap (hr _ (by omega) (by omega))

private theorem head?_map_iterate {d : H} {s n : ℕ} (hn : n ≠ 0) :
    ((List.range' s n).map fun k => X.strandMap^[k] d).head? = some (X.strandMap^[s] d) := by
  simp [List.head?_range', hn]

private theorem getLast?_map_iterate {d : H} {s n : ℕ} (hn : n ≠ 0) :
    ((List.range' s n).map fun k => X.strandMap^[k] d).getLast? =
      some (X.strandMap^[s + n - 1] d) := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range', one_mul, List.length_map,
    List.length_range']
  congr 2
  omega

omit [Fintype H] [DecidableEq H] in
/-- Cancelling along an orbit on which `f` is injective. -/
private theorem eq_iterate_sub_of_eq {f : H → H} {d : H}
    (hinj : ∀ k l, f (f^[k] d) = f (f^[l] d) → f^[k] d = f^[l] d) :
    ∀ a c, f^[a] d = f^[c] d → a ≤ c → d = f^[c - a] d
  | 0, c, h, _ => by simpa using h
  | a + 1, 0, _, hac => absurd hac (by omega)
  | a + 1, c + 1, h, hac => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
    rw [show c + 1 - (a + 1) = c - a by omega]
    exact eq_iterate_sub_of_eq hinj a c (hinj a c h) (by omega)

/-- A dart all of whose iterates under the strand map avoid running to an endpoint is periodic. -/
private theorem minimalPeriod_strandMap {d : H}
    (hr : ∀ k, ¬X.RunsToEndpoint (X.strandMap^[k] d)) :
    0 < Function.minimalPeriod X.strandMap d ∧
      X.strandMap^[Function.minimalPeriod X.strandMap d] d = d ∧
      ∀ a c, a < Function.minimalPeriod X.strandMap d → c < Function.minimalPeriod X.strandMap d →
        X.strandMap^[a] d = X.strandMap^[c] d → a = c := by
  have hinj : ∀ k l, X.strandMap (X.strandMap^[k] d) = X.strandMap (X.strandMap^[l] d) →
      X.strandMap^[k] d = X.strandMap^[l] d := by
    intro k l h
    rw [X.strandMap_of_not_runsToEndpoint (hr k), X.strandMap_of_not_runsToEndpoint (hr l)] at h
    exact X.inv.injective (X.rot.injective (X.rot.injective (X.rot.injective h)))
  obtain ⟨a, c, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => X.strandMap^[n] d)
  have hper : ∃ p, 0 < p ∧ X.strandMap^[p] d = d := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨c - a, by omega, (eq_iterate_sub_of_eq hinj a c h hlt.le).symm⟩
    · exact ⟨a - c, by omega, (eq_iterate_sub_of_eq hinj c a h.symm hlt.le).symm⟩
  obtain ⟨p, hp, hpd⟩ := hper
  have hmem : d ∈ Function.periodicPts X.strandMap := Function.mk_mem_periodicPts hp hpd
  exact ⟨Function.minimalPeriod_pos_of_mem_periodicPts hmem, Function.iterate_minimalPeriod,
    fun a c ha hc h => Function.iterate_injOn_Iio_minimalPeriod ha hc h⟩

/-- No dart of the orbit of `d` under the strand map runs to an endpoint if the orbit contains no
dart at an endpoint. -/
private theorem not_runsToEndpoint_iterate {d : H}
    (hCb : ∀ e ∈ X.strandOrbit d, ¬X.IsBoundaryVertex (X.vertexOf e)) (k : ℕ) :
    ¬X.RunsToEndpoint (X.strandMap^[k] d) := by
  intro hr
  have hmem : X.strandMap^[k + 1] d ∈ X.strandOrbit d := X.mem_strandOrbit.2 ⟨k + 1, rfl⟩
  rw [Function.iterate_succ_apply', X.strandMap_of_runsToEndpoint hr] at hmem
  exact hCb _ hmem hr

omit [Fintype H] [DecidableEq H] in
/-- Along a periodic orbit of period `m`, the iterate at `i + 1` modulo `m`. -/
private theorem iterate_finRotate {f : H → H} {d : H} {m : ℕ} (hper : f^[m] d = d) (i : Fin m) :
    f^[(finRotate m i : ℕ)] d = f^[(i : ℕ) + 1] d := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := i.2; omega⟩
  rw [coe_finRotate]
  split_ifs with h
  · subst h
    simp only [Fin.val_last, Function.iterate_zero, id]
    exact hper.symm
  · rfl

/-- In a diagram without monogons, the darts `(d, S d, …, S^{m-1} d)` of a closed strand of `out`
darts of period `m` form a simple closed walk. -/
private theorem isSimpleClosedWalk_iterate (hX : X.IsPreTripleDiagram) (hmono : ¬X.HasMonogon)
    {d : H} (hd : d ∉ X.bdry) (hout : X.isOut d = true)
    (hr : ∀ k, ¬X.RunsToEndpoint (X.strandMap^[k] d)) {m : ℕ} (hm : 0 < m)
    (hper : X.strandMap^[m] d = d)
    (hinj : ∀ a c, a < m → c < m → X.strandMap^[a] d = X.strandMap^[c] d → a = c) :
    X.IsSimpleClosedWalk (fun i : Fin m => X.strandMap^[(i : ℕ)] d) := by
  have hBo : ∀ k, X.strandMap^[k] d ∉ X.bdry ∧ X.isOut (X.strandMap^[k] d) = true := fun k =>
    let h := iterate_notMem_bdry_isOut hX hd (n := k) (fun j _ => hr j) k le_rfl
    ⟨h.1, h.2.trans hout⟩
  have hadd : ∀ k, X.strandMap^[k + m] d = X.strandMap^[k] d := by
    intro k
    rw [Function.iterate_add_apply, hper]
  have hrot : ∀ k, X.strandMap^[k + 1] d = (X.rot ^ 3) (X.inv (X.strandMap^[k] d)) := by
    intro k
    rw [Function.iterate_succ_apply']
    exact (strandStep_strandMap (hr k)).2
  have htrip : ∀ k, ¬X.IsBoundaryVertex (X.vertexOf (X.strandMap^[k] d)) := by
    intro k
    have := (strandStep_strandMap (hr (k + m - 1))).not_isBoundaryVertex
    rwa [← Function.iterate_succ_apply' X.strandMap, Nat.succ_eq_add_one,
      show k + m - 1 + 1 = k + m by omega,
      hadd] at this
  have hfin : ∀ i : Fin m,
      X.strandMap^[(finRotate m i : ℕ)] d = X.strandMap^[(i : ℕ) + 1] d :=
    iterate_finRotate hper
  have key : ∀ a c, a < c → c < m →
      X.vertexOf (X.strandMap^[a] d) = X.vertexOf (X.strandMap^[c] d) → False := by
    intro a c hac hcm hv
    set U := (List.range' a (c - a)).map fun k => X.strandMap^[k] d with hU
    have hUp : X.IsStrandPath U :=
      isStrandPath_map_iterate (by omega) (fun k _ _ => hBo k) (fun k _ _ => hr k)
    have hUh := head?_map_iterate (X := X) (d := d) (s := a) (n := c - a) (by omega)
    have hUl := getLast?_map_iterate (X := X) (d := d) (s := a) (n := c - a) (by omega)
    rw [show a + (c - a) - 1 = c - 1 by omega] at hUl
    have hc1 : X.strandMap^[c] d = (X.rot ^ 3) (X.inv (X.strandMap^[c - 1] d)) := by
      rw [← hrot, show c - 1 + 1 = c by omega]
    by_cases heq : X.inv (X.strandMap^[c - 1] d) = (X.rot ^ 3) (X.strandMap^[a] d)
    · rw [heq, hX.rot_pow_three_rot_pow_three (htrip a)] at hc1
      have := hinj a c (by omega) hcm hc1.symm
      omega
    · apply hmono
      refine ⟨U, hUp, ?_, ?_, ?_⟩
      · rw [X.pathStart_of_head? hUh]
        exact X.vertexOf_mem_internalVertices.2 (htrip a)
      · rw [X.pathStart_of_head? hUh, X.pathEnd_of_getLast? hUl, hv, hc1,
          X.vertexOf_rot_pow_apply]
      · intro e₁ he₁ eₘ heₘ
        rw [hUh, Option.mem_def, Option.some_inj] at he₁
        rw [hUl, Option.mem_def, Option.some_inj] at heₘ
        rw [← he₁, ← heₘ]
        exact heq
  refine ⟨hm, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · simp only [hfin, hrot]
    exact (X.vertexOf_rot_pow_apply 3 _).symm
  · simp only [hfin, hrot]
    intro h
    have := (hX.rot_pow_six (hr i)).2 3 0 (by omega) (by omega) (by simpa using h)
    omega
  · simp only at hij
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact (key _ _ h j.2 hij).elim
    · exact Fin.ext h
    · exact (key _ _ h i.2 hij.symm).elim

/-- **Winding values across a closed walk.** Let `w` be a simple closed walk with
`w(i + 1) = σ³(w(i)̄)` at triple points, and `h` its winding function. At a vertex `v(w(i)̄)` of
the walk, a dart `u` that is neither a dart of the walk nor the reverse of one satisfies
`h(f(σ³ u)) ≠ h(f(u))`: the two darts lie on different sides of the walk. -/
private theorem winding_rot_pow_three_ne (hX : X.IsTripleDiagram) {m : ℕ} {w : Fin m → H}
    (hw : X.IsSimpleClosedWalk w) (hstep : ∀ i, w (finRotate m i) = (X.rot ^ 3) (X.inv (w i)))
    (htrip : ∀ i, ¬X.IsBoundaryVertex (X.vertexOf (X.inv (w i))))
    {h : X.faceOrbits → ℤ} (hh : X.IsWindingFunction (X.walkCycle w) h)
    {u : H} (hu₁ : ∀ i, u ≠ w i) (hu₂ : ∀ i, u ≠ X.inv (w i)) {i : Fin m}
    (hui : X.vertexOf u = X.vertexOf (X.inv (w i))) :
    h (X.toFaceOrbit ((X.rot ^ 3) u)) ≠ h (X.toFaceOrbit u) := by
  have hinv := hX.inv_involutive
  have hP := hX.toIsPreTripleDiagram
  set r := X.inv (w i) with hr
  have h6 := (hP.rot_pow_six (htrip i)).2
  obtain ⟨n, hn⟩ : ∃ n, (X.rot ^ n) r = u :=
    (X.mem_vertexOf.1 ((X.mem_vertexOf_iff_vertexOf_eq).2 hui)).exists_nat_pow_eq
  obtain ⟨k, hk6, hn⟩ : ∃ k < 6, (X.rot ^ k) r = u :=
    ⟨n % 6, Nat.mod_lt _ (by omega), by rw [← hP.rot_pow_mod_six (htrip i)]; exact hn⟩
  set V : ℕ → ℤ := fun j => h (X.toFaceOrbit ((X.rot ^ j) r)) with hV
  have hVs : ∀ j, V (j + 1) = V j + X.walkCycle w ((X.rot ^ j) r) := by
    intro j
    simp only [hV]
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hh.apply_rot hinv _
  have hvr : X.vertexOf r = X.vertexOf (w (finRotate m i)) := hw.vertexOf_inv i
  have hc0 : ∀ j, j < 6 → j ≠ 0 → j ≠ 3 → X.walkCycle w ((X.rot ^ j) r) = 0 := by
    intro j hj hj0 hj3
    refine RotationSystem.walkCycle_eq_zero hinv (fun l hl => ?_) fun l hl => ?_
    · have hv : X.vertexOf (w l) = X.vertexOf (w (finRotate m i)) := by
        rw [← hl, X.vertexOf_rot_pow_apply, hvr]
      have := hw.eq_of_vertexOf_eq hv
      rw [this, hstep] at hl
      exact hj3 (h6 j 3 hj (by omega) hl)
    · have hv : X.vertexOf (X.inv (w l)) = X.vertexOf (w (finRotate m i)) := by
        rw [← hl, X.vertexOf_rot_pow_apply, hvr]
      have := hw.eq_of_vertexOf_inv_eq hv
      rw [this] at hl
      exact hj0 (h6 j 0 hj (by omega) (by simpa using hl))
  have hcr : X.walkCycle w ((X.rot ^ 0) r) = -1 := by
    simpa using hw.walkCycle_apply_inv hinv i
  have hc3 : X.walkCycle w ((X.rot ^ 3) r) = 1 := by
    rw [← hstep]
    exact hw.walkCycle_apply_self _
  have e1 : V 1 = V 0 + X.walkCycle w ((X.rot ^ 0) r) := hVs 0
  have e2 : V 2 = V 1 + X.walkCycle w ((X.rot ^ 1) r) := hVs 1
  have e3 : V 3 = V 2 + X.walkCycle w ((X.rot ^ 2) r) := hVs 2
  have e4 : V 4 = V 3 + X.walkCycle w ((X.rot ^ 3) r) := hVs 3
  have e5 : V 5 = V 4 + X.walkCycle w ((X.rot ^ 4) r) := hVs 4
  rw [hcr] at e1
  rw [hc0 1 (by omega) (by omega) (by omega)] at e2
  rw [hc0 2 (by omega) (by omega) (by omega)] at e3
  rw [hc3] at e4
  rw [hc0 4 (by omega) (by omega) (by omega)] at e5
  have hrot3 : ∀ j, (X.rot ^ 3) ((X.rot ^ j) r) = (X.rot ^ (j + 3)) r := by
    intro j
    rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
  have hk0 : k ≠ 0 := by
    intro h0
    apply hu₂ i
    rw [← hn, h0, pow_zero, Equiv.Perm.one_apply]
  have hk3 : k ≠ 3 := by
    intro h3
    apply hu₁ (finRotate m i)
    rw [← hn, h3, hstep]
  rw [← hn, hrot3]
  change V (k + 3) ≠ V k
  have hV7 : V 7 = V 1 := by
    simp only [hV]
    rw [hP.rot_pow_mod_six (htrip i) 7]
  have hV8 : V 8 = V 2 := by
    simp only [hV]
    rw [hP.rot_pow_mod_six (htrip i) 8]
  interval_cases k
  · exact absurd rfl hk0
  · change V 4 ≠ V 1
    omega
  · change V 5 ≠ V 2
    omega
  · exact absurd rfl hk3
  · change V 7 ≠ V 4
    rw [hV7]
    omega
  · change V 8 ≠ V 5
    rw [hV8]
    omega

/-- Finding a change: if `μ a ≠ μ (a + n)`, some `p ∈ (a, a + n]` has `μ p ≠ μ (p - 1)`. -/
private theorem exists_ne_sub_one {μ : ℕ → ℤ} {a : ℕ} :
    ∀ n, μ a ≠ μ (a + n) → ∃ p, a < p ∧ p ≤ a + n ∧ μ p ≠ μ (p - 1)
  | 0, h => absurd rfl h
  | n + 1, h => by
    by_cases h' : μ (a + n + 1) = μ (a + n)
    · obtain ⟨p, hp1, hp2, hp3⟩ := exists_ne_sub_one (μ := μ) (a := a) n (by
        rw [← add_assoc, h'] at h
        exact h)
      exact ⟨p, hp1, by omega, hp3⟩
    · exact ⟨a + n + 1, by omega, by omega, by simpa using h'⟩

private theorem exists_ne_sub_one' {μ : ℕ → ℤ} {a c : ℕ} (hac : a ≤ c) (h : μ a ≠ μ c) :
    ∃ p, a < p ∧ p ≤ c ∧ μ p ≠ μ (p - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hac
  exact exists_ne_sub_one n h

/-- Let `X` be a triple diagram without monogons, `C` a closed strand of `X` consisting of `out`
darts, and `T` an arc of `X` or a closed strand of `X` consisting of `out` darts, containing a dart
`g` that is not a dart of `C` and lies at a triple point through which `C` passes. Then `X` has a
parallel digon `(P, Q)` such that the darts of `P` are darts of `C` and the darts of `Q` are darts
of `T`. (The darts of an arc are `out` darts, so `g` is an `out` dart.) -/
@[cluster_algebras "lem_closed_strand_crossed"]
theorem exists_isParallelDigon_of_isClosedStrand (hX : X.IsTripleDiagram)
    (hmono : ¬X.HasMonogon) {C : Finset H} (hC : X.IsClosedStrand C)
    (hCout : ∀ e ∈ C, X.isOut e = true) {T : Finset H}
    (hT : (∃ j, T = (X.arc j).toFinset) ∨ (X.IsClosedStrand T ∧ ∀ e ∈ T, X.isOut e = true))
    {g : H} (hgT : g ∈ T) (hgC : g ∉ C) (hg : X.PassesThrough C (X.vertexOf g)) :
    ∃ P Q x y, X.IsParallelDigon P Q x y ∧ (∀ e ∈ P, e ∈ C) ∧ ∀ e ∈ Q, e ∈ T := by
  have hP := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  obtain ⟨d, hdB, rfl, hCb⟩ := hC
  have hr := not_runsToEndpoint_iterate hCb
  obtain ⟨hm, hper, hinj⟩ := minimalPeriod_strandMap hr
  set m := Function.minimalPeriod X.strandMap d with hmdef
  have hdout : X.isOut d = true := hCout d (X.mem_strandOrbit.2 ⟨0, rfl⟩)
  have hw := isSimpleClosedWalk_iterate hP hmono hdB hdout hr hm hper hinj
  set w : Fin m → H := fun i => X.strandMap^[(i : ℕ)] d with hwdef
  obtain ⟨h, hh, -⟩ := hX.toIsDiskMap.existsUnique_isWindingFunction_walkCycle hw
  have hBo : ∀ k, X.strandMap^[k] d ∉ X.bdry ∧ X.isOut (X.strandMap^[k] d) = true := fun k =>
    let h := iterate_notMem_bdry_isOut hP hdB (n := k) (fun j _ => hr j) k le_rfl
    ⟨h.1, h.2.trans hdout⟩
  have hadd : ∀ k, X.strandMap^[k + m] d = X.strandMap^[k] d := by
    intro k
    rw [Function.iterate_add_apply, hper]
  have hrot : ∀ k, X.strandMap^[k + 1] d = (X.rot ^ 3) (X.inv (X.strandMap^[k] d)) := by
    intro k
    rw [Function.iterate_succ_apply']
    exact (strandStep_strandMap (hr k)).2
  have htripC : ∀ k, ¬X.IsBoundaryVertex (X.vertexOf (X.strandMap^[k] d)) := fun k =>
    hCb _ (X.mem_strandOrbit.2 ⟨k, rfl⟩)
  have hmod : ∀ k, X.strandMap^[k] d = w ⟨k % m, Nat.mod_lt _ hm⟩ := fun k =>
    (Function.iterate_mod_minimalPeriod_eq).symm
  have hmemC : ∀ u, u ∈ X.strandOrbit d ↔ ∃ i : Fin m, w i = u := by
    intro u
    rw [mem_strandOrbit]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, (hmod k).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  have hstepw : ∀ i, w (finRotate m i) = (X.rot ^ 3) (X.inv (w i)) := by
    intro i
    simp only [hwdef]
    rw [iterate_finRotate hper i, hrot]
  have htripw : ∀ i, ¬X.IsBoundaryVertex (X.vertexOf (X.inv (w i))) := fun i => hr i
  -- the winding function `μ`
  set μ : H → ℤ := fun u => h (X.toFaceOrbit u) with hμ
  have hinvC : ∀ i, X.isOut (X.inv (w i)) = false := by
    intro i
    rw [hP.isOut_inv_apply (hBo i).1, (hBo i).2]
    rfl
  have hμinv : ∀ u, (∀ i, u ≠ w i) → (∀ i, u ≠ X.inv (w i)) → μ (X.inv u) = μ u := by
    intro u h₁ h₂
    have := hh.sub_eq u
    rw [RotationSystem.walkCycle_eq_zero hinv h₁ h₂] at this
    simp only [hμ]
    linarith
  have hsame : ∀ u, ¬X.RunsToEndpoint u → (∀ i, u ≠ w i) → (∀ i, u ≠ X.inv (w i)) →
      (∀ i, X.vertexOf (X.strandMap u) ≠ X.vertexOf (w i)) → μ (X.strandMap u) = μ u := by
    intro u hu h₁ h₂ hv
    rw [← hμinv u h₁ h₂]
    have hS : X.strandMap u = (X.rot ^ 3) (X.inv u) := (strandStep_strandMap hu).2
    have hvS : X.vertexOf (X.strandMap u) = X.vertexOf (X.inv u) := by
      rw [hS, X.vertexOf_rot_pow_apply]
    rw [hS]
    refine RotationSystem.apply_toFaceOrbit_eq_of_mem_vertexOf hinv hh.sub_eq (fun e he => ?_)
      (X.rot_pow_apply_mem_vertexOf 3 _)
    refine hw.walkCycle_eq_zero_of_vertexOf_ne hinv fun i => ?_
    rw [X.vertexOf_eq_of_mem he, ← hvS]
    exact hv i
  have hdiff : ∀ u, ¬X.RunsToEndpoint u → (∀ i, u ≠ w i) → (∀ i, u ≠ X.inv (w i)) →
      (∃ i, X.vertexOf (X.strandMap u) = X.vertexOf (w i)) → μ (X.strandMap u) ≠ μ u := by
    intro u hu h₁ h₂ ⟨j, hj⟩
    rw [← hμinv u h₁ h₂]
    have hS : X.strandMap u = (X.rot ^ 3) (X.inv u) := (strandStep_strandMap hu).2
    rw [hS]
    refine winding_rot_pow_three_ne hX hw hstepw htripw hh (u := X.inv u)
      (i := (finRotate m).symm j)
      (fun i hi => h₂ i (by rw [← hi, hinv])) (fun i hi => h₁ i (by
        have := congrArg X.inv hi
        rwa [hinv, hinv] at this)) ?_
    rw [hw.vertexOf_inv, Equiv.apply_symm_apply, ← hj, hS, X.vertexOf_rot_pow_apply]
  have hzero : ∀ u, X.IsBoundaryVertex (X.vertexOf u) → μ u = 0 := by
    intro u hu
    refine hh.apply_eq_zero_of_isBoundaryVertex hX.toIsDiskMap hu fun e he => ?_
    have hve := X.vertexOf_eq_of_mem he
    refine RotationSystem.walkCycle_eq_zero hinv (fun i hi => ?_) fun i hi => ?_
    · exact htripC i (by rw [← hve] at hu; simpa [hi] using hu)
    · apply htripw i
      rw [← hve] at hu
      simpa [hi] using hu
  -- going back along the strand map into `C`
  have hback : ∀ u, ¬X.RunsToEndpoint u → X.strandMap u ∈ X.strandOrbit d →
      u ∈ X.strandOrbit d := by
    intro u hu hSu
    obtain ⟨k, hk⟩ := X.mem_strandOrbit.1 hSu
    have h1 : X.strandMap^[k] d = X.strandMap (X.strandMap^[k + m - 1] d) := by
      rw [← Function.iterate_succ_apply' X.strandMap, Nat.succ_eq_add_one,
        show k + m - 1 + 1 = k + m by omega, hadd]
    rw [h1, X.strandMap_of_not_runsToEndpoint hu,
      X.strandMap_of_not_runsToEndpoint (hr _)] at hk
    have := X.inv.injective (X.rot.injective (X.rot.injective (X.rot.injective hk)))
    rw [← this]
    exact X.mem_strandOrbit.2 ⟨_, rfl⟩
  have hnotinv : ∀ u, X.isOut u = true → ∀ i, u ≠ X.inv (w i) := by
    intro u hu i h
    rw [h, hinvC] at hu
    exact Bool.false_ne_true hu
  -- the conclusion from two points of `C` on `T`
  have hfinal : ∀ (t₀ : H) (p₁ p₂ : ℕ), p₁ < p₂ →
      (∀ k, p₁ ≤ k → k < p₂ → ¬X.RunsToEndpoint (X.strandMap^[k] t₀)) →
      (∀ k, p₁ ≤ k → k ≤ p₂ → X.strandMap^[k] t₀ ∉ X.bdry ∧
        X.isOut (X.strandMap^[k] t₀) = true ∧ X.strandMap^[k] t₀ ∉ X.strandOrbit d ∧
        X.strandMap^[k] t₀ ∈ T) →
      X.strandMap^[p₁] t₀ ≠ X.strandMap^[p₂] t₀ →
      (∃ i : Fin m, X.vertexOf (X.strandMap^[p₁] t₀) = X.vertexOf (w i)) →
      (∃ i : Fin m, X.vertexOf (X.strandMap^[p₂] t₀) = X.vertexOf (w i)) →
      ∃ P Q x y, X.IsParallelDigon P Q x y ∧ (∀ e ∈ P, e ∈ X.strandOrbit d) ∧
        ∀ e ∈ Q, e ∈ T := by
    intro t₀ p₁ p₂ hp hrt hBt hne ⟨a, ha⟩ ⟨c, hc⟩
    set Q := (List.range' p₁ (p₂ - p₁)).map fun k => X.strandMap^[k] t₀ with hQ
    have hQp : X.IsStrandPath Q := isStrandPath_map_iterate (by omega)
      (fun k hk1 hk2 => ⟨(hBt k hk1 (by omega)).1, (hBt k hk1 (by omega)).2.1⟩)
      (fun k hk1 hk2 => hrt k hk1 (by omega))
    have hQh := head?_map_iterate (X := X) (d := t₀) (s := p₁) (n := p₂ - p₁) (by omega)
    have hQl := getLast?_map_iterate (X := X) (d := t₀) (s := p₁) (n := p₂ - p₁) (by omega)
    rw [show p₁ + (p₂ - p₁) - 1 = p₂ - 1 by omega] at hQl
    have hp₂ : X.strandMap^[p₂] t₀ = (X.rot ^ 3) (X.inv (X.strandMap^[p₂ - 1] t₀)) := by
      rw [show p₂ = p₂ - 1 + 1 by omega, Function.iterate_succ_apply',
        show p₂ - 1 + 1 - 1 = p₂ - 1 by omega]
      exact (strandStep_strandMap (hrt _ (by omega) (by omega))).2
    have hQend : X.pathEnd Q = X.vertexOf (X.strandMap^[p₂] t₀) := by
      rw [X.pathEnd_of_getLast? hQl, hp₂, X.vertexOf_rot_pow_apply]
    have hQstart : X.pathStart Q = X.vertexOf (X.strandMap^[p₁] t₀) := X.pathStart_of_head? hQh
    have hx₁ : ¬X.IsBoundaryVertex (X.vertexOf (X.strandMap^[p₁] t₀)) := by
      rw [ha]
      exact htripC a
    have hx₂ : ¬X.IsBoundaryVertex (X.vertexOf (X.strandMap^[p₂] t₀)) := by
      rw [hc]
      exact htripC c
    by_cases hxy : X.vertexOf (X.strandMap^[p₁] t₀) = X.vertexOf (X.strandMap^[p₂] t₀)
    · -- a monogon
      exfalso
      apply hmono
      set u₁ := X.strandMap^[p₁] t₀
      set u₂ := X.strandMap^[p₂] t₀
      have hu₁o := (hBt p₁ le_rfl hp.le).2.1
      have hu₂o := (hBt p₂ hp.le le_rfl).2.1
      have hcc' : ({(X.rot ^ 3) u₁, (X.rot ^ 3) ((X.rot ^ 3) u₁)} : Finset H) ≠
          {(X.rot ^ 3) u₂, (X.rot ^ 3) ((X.rot ^ 3) u₂)} := by
        rw [hP.rot_pow_three_rot_pow_three hx₁, hP.rot_pow_three_rot_pow_three hx₂]
        intro heq
        have : u₂ ∈ ({(X.rot ^ 3) u₁, u₁} : Finset H) := by
          rw [heq]
          simp
        rcases mem_insert.1 this with h' | h'
        · have := hP.isOut_rot_pow_three_apply hx₁
          rw [← h', hu₂o, hu₁o] at this
          exact absurd this (by decide)
        · exact hne (mem_singleton.1 h').symm
      have hv₂ : (X.rot ^ 3) u₂ ∈ X.vertexOf u₁ := by
        rw [X.mem_vertexOf_iff_vertexOf_eq, X.vertexOf_rot_pow_apply, hxy]
      obtain ⟨hmon, -⟩ := X.isMonogon_of_two_passes hP
        (X.vertexOf_mem_internalVertices.2 hx₁) (X.rot_pow_apply_mem_vertexOf 3 u₁) hv₂ hcc'
        hQp (by rw [hQh, hP.rot_pow_three_rot_pow_three hx₁]) (fun e he => by
          rw [hQl, Option.mem_def, Option.some_inj] at he
          rw [← he]
          have hx' : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.strandMap^[p₂ - 1] t₀))) :=
            hrt _ (by omega) (by omega)
          rw [hp₂, hP.rot_pow_three_rot_pow_three hx'])
      exact ⟨Q, hmon⟩
    · -- a parallel digon
      have hac : a ≠ c := by
        rintro rfl
        exact hxy (ha.trans hc.symm)
      set c' : ℕ := if (a : ℕ) < c then c else c + m with hc'
      have hac' : (a : ℕ) < c' := by
        simp only [hc']
        split_ifs <;> omega
      have hc'm : (c' : ℕ) - 1 + 1 = c' := by omega
      have hwc' : X.strandMap^[c'] d = w c := by
        simp only [hc']
        split_ifs
        · rfl
        · exact hadd _
      set P := (List.range' a (c' - a)).map fun k => X.strandMap^[k] d with hPdef
      have hPp : X.IsStrandPath P := isStrandPath_map_iterate (by omega)
        (fun k _ _ => hBo k) (fun k _ _ => hr k)
      have hPh := head?_map_iterate (X := X) (d := d) (s := a) (n := c' - a) (by omega)
      have hPl := getLast?_map_iterate (X := X) (d := d) (s := a) (n := c' - a) (by omega)
      rw [show (a : ℕ) + (c' - a) - 1 = c' - 1 by omega] at hPl
      refine ⟨P, Q, _, _, ⟨hxy, X.vertexOf_mem_internalVertices.2 hx₁,
        X.vertexOf_mem_internalVertices.2 hx₂, hPp, hQp, ?_, ?_, hQstart, hQend, ?_, ?_⟩, ?_, ?_⟩
      · rw [X.pathStart_of_head? hPh, ha]
      · rw [X.pathEnd_of_getLast? hPl, hc, ← hwc', ← hc'm, hrot, X.vertexOf_rot_pow_apply,
          hc'm]
      · rw [hPh, hQh]
        intro h'
        rw [Option.some_inj] at h'
        exact (hBt p₁ le_rfl hp.le).2.2.1 (h' ▸ X.mem_strandOrbit.2 ⟨a, rfl⟩)
      · rw [hPl, hQl]
        intro h'
        rw [Option.some_inj] at h'
        exact (hBt (p₂ - 1) (by omega) (by omega)).2.2.1
          (h' ▸ X.mem_strandOrbit.2 ⟨c' - 1, rfl⟩)
      · intro e he
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 he
        exact X.mem_strandOrbit.2 ⟨k, rfl⟩
      · intro e he
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 he
        rw [List.mem_range'_1] at hk
        exact (hBt k hk.1 (by omega)).2.2.2
  -- the point of `C` at `g`
  obtain ⟨hgint, e₀, he₀C, he₀g⟩ := hg
  obtain ⟨i₀, hi₀⟩ := (hmemC e₀).1 he₀C
  have hgpt : X.vertexOf g = X.vertexOf (w i₀) := by rw [hi₀, he₀g]
  have hgb : ¬X.IsBoundaryVertex (X.vertexOf g) := (X.mem_internalVertices.1 hgint).2
  rcases hT with ⟨j, rfl⟩ | ⟨hTc, hTout⟩
  · -- `T` is an arc
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (hP.arcLength_ne_zero j)
    have hrA : ∀ k < n, ¬X.RunsToEndpoint (X.arcDart j k) :=
      (X.arcLength_eq_succ_iff.1 hn).2
    have hlastA : X.RunsToEndpoint (X.arcDart j n) := (X.arcLength_eq_succ_iff.1 hn).1
    have hBoA : ∀ k ≤ n, X.arcDart j k ∉ X.bdry ∧ X.isOut (X.arcDart j k) = true :=
      fun k hk => X.arcDart_notMem_bdry_isOut hP hn hk
    have hmemA : ∀ k ≤ n, X.arcDart j k ∈ (X.arc j).toFinset := by
      intro k hk
      rw [List.mem_toFinset, arc, List.mem_map]
      exact ⟨k, List.mem_range.2 (by rw [hn]; omega), rfl⟩
    have ht₀ : X.IsBoundaryVertex (X.vertexOf (X.arcDart j 0)) := by
      have := hP.endpoint_mem (sourceIndex j)
      exact (X.mem_boundaryVertices.1 this).2
    have hnotC : ∀ k ≤ n, X.arcDart j k ∉ X.strandOrbit d := by
      intro k hk
      induction k with
      | zero =>
        intro h0
        exact hCb _ h0 ht₀
      | succ k ih =>
        intro hk'
        rw [arcDart_succ] at hk'
        exact ih (by omega) (hback _ (hrA k (by omega)) hk')
    have hnc : ∀ k ≤ n, (∀ i, X.arcDart j k ≠ w i) ∧ (∀ i, X.arcDart j k ≠ X.inv (w i)) := by
      intro k hk
      refine ⟨fun i hi => hnotC k hk ((hmemC _).2 ⟨i, hi.symm⟩), ?_⟩
      exact hnotinv _ (hBoA k hk).2
    obtain ⟨p₀, hp₀, rfl⟩ : ∃ p₀ ≤ n, X.arcDart j p₀ = g := by
      rw [List.mem_toFinset, arc, List.mem_map] at hgT
      obtain ⟨k, hk, hkg⟩ := hgT
      rw [List.mem_range, hn] at hk
      exact ⟨k, by omega, hkg⟩
    have hp₀0 : p₀ ≠ 0 := by
      rintro rfl
      exact hgb ht₀
    -- the values of `μ` along the arc
    set ν : ℕ → ℤ := fun k => μ (X.arcDart j k) with hν
    have hν0 : ν 0 = 0 := hzero _ ht₀
    have hνn : ν n = 0 := by
      simp only [hν]
      rw [← hμinv _ (hnc n le_rfl).1 (hnc n le_rfl).2]
      exact hzero _ hlastA
    have hcross : ∀ p, 0 < p → p ≤ n → ν p ≠ ν (p - 1) →
        ∃ i, X.vertexOf (X.arcDart j p) = X.vertexOf (w i) := by
      intro p hp hpn hne
      by_contra hno
      push Not at hno
      apply hne
      have := hsame (X.arcDart j (p - 1)) (hrA _ (by omega)) (hnc _ (by omega)).1
        (hnc _ (by omega)).2 (by rw [← arcDart_succ, show p - 1 + 1 = p by omega]; exact hno)
      simp only [hν]
      rw [← this, ← arcDart_succ, show p - 1 + 1 = p by omega]
    have hνp₀ : ν p₀ ≠ ν (p₀ - 1) := by
      have := hdiff (X.arcDart j (p₀ - 1)) (hrA _ (by omega)) (hnc _ (by omega)).1
        (hnc _ (by omega)).2 ⟨i₀, by rw [← arcDart_succ, show p₀ - 1 + 1 = p₀ by omega, hgpt]⟩
      simp only [hν]
      rwa [← arcDart_succ, show p₀ - 1 + 1 = p₀ by omega] at this
    have hBt : ∀ k, k ≤ n → X.strandMap^[k] (X.endDart (sourceIndex j)) ∉ X.bdry ∧
        X.isOut (X.strandMap^[k] (X.endDart (sourceIndex j))) = true ∧
        X.strandMap^[k] (X.endDart (sourceIndex j)) ∉ X.strandOrbit d ∧
        X.strandMap^[k] (X.endDart (sourceIndex j)) ∈ (X.arc j).toFinset :=
      fun k hk => ⟨(hBoA k hk).1, (hBoA k hk).2, hnotC k hk, hmemA k hk⟩
    by_cases hν₁ : ν (p₀ - 1) = ν 0
    · -- a second crossing after `p₀`
      have hne : ν p₀ ≠ ν n := by rwa [hνn, ← hν0, ← hν₁]
      have hp₀n : p₀ ≤ n := hp₀
      obtain ⟨p, hp1, hp2, hp3⟩ := exists_ne_sub_one' hp₀n hne
      obtain ⟨i, hi⟩ := hcross p (by omega) hp2 hp3
      exact hfinal _ p₀ p hp1 (fun k _ hk => hrA k (by omega)) (fun k _ hk => hBt k (by omega))
        (X.arcDart_ne_of_lt hn hp1 hp2) ⟨i₀, hgpt⟩ ⟨i, hi⟩
    · -- a crossing before `p₀`
      obtain ⟨p, hp1, hp2, hp3⟩ := exists_ne_sub_one' (Nat.zero_le (p₀ - 1)) (Ne.symm hν₁)
      obtain ⟨i, hi⟩ := hcross p hp1 (by omega) hp3
      exact hfinal _ p p₀ (by omega) (fun k _ hk => hrA k (by omega))
        (fun k _ hk => hBt k (by omega)) (X.arcDart_ne_of_lt hn (by omega) hp₀) ⟨i, hi⟩
        ⟨i₀, hgpt⟩
  · -- `T` is a closed strand
    obtain ⟨g', hg'B, rfl, hTb⟩ := hTc
    have hSmem : ∀ k, X.strandMap^[k] g ∈ X.strandOrbit g' := by
      intro k
      obtain ⟨l, rfl⟩ := X.mem_strandOrbit.1 hgT
      rw [← Function.iterate_add_apply]
      exact X.mem_strandOrbit.2 ⟨_, rfl⟩
    have hrT : ∀ k, ¬X.RunsToEndpoint (X.strandMap^[k] g) := by
      intro k hk
      have := hSmem (k + 1)
      rw [Function.iterate_succ_apply', X.strandMap_of_runsToEndpoint hk] at this
      exact hTb _ this hk
    have hBoT : ∀ k, X.strandMap^[k] g ∉ X.bdry ∧ X.isOut (X.strandMap^[k] g) = true :=
      fun k => ⟨X.notMem_bdry_of_not_isBoundaryVertex (hTb _ (hSmem k)), hTout _ (hSmem k)⟩
    obtain ⟨hM, hperM, hinjM⟩ := minimalPeriod_strandMap hrT
    set M := Function.minimalPeriod X.strandMap g with hMdef
    have hnotC : ∀ k, X.strandMap^[k] g ∉ X.strandOrbit d := by
      intro k
      induction k with
      | zero => exact hgC
      | succ k ih =>
        intro hk'
        rw [Function.iterate_succ_apply'] at hk'
        exact ih (hback _ (hrT k) hk')
    have hnc : ∀ k, (∀ i, X.strandMap^[k] g ≠ w i) ∧ (∀ i, X.strandMap^[k] g ≠ X.inv (w i)) :=
      fun k => ⟨fun i hi => hnotC k ((hmemC _).2 ⟨i, hi.symm⟩), hnotinv _ (hBoT k).2⟩
    set ν : ℕ → ℤ := fun k => μ (X.strandMap^[k] g) with hν
    have hcross : ∀ p, 0 < p → ν p ≠ ν (p - 1) →
        ∃ i, X.vertexOf (X.strandMap^[p] g) = X.vertexOf (w i) := by
      intro p hp hne
      by_contra hno
      push Not at hno
      apply hne
      have := hsame (X.strandMap^[p - 1] g) (hrT _) (hnc _).1 (hnc _).2
        (by rw [← Function.iterate_succ_apply' X.strandMap, Nat.succ_eq_add_one,
            show p - 1 + 1 = p by omega]
            exact hno)
      simp only [hν]
      rw [← this, ← Function.iterate_succ_apply' X.strandMap, Nat.succ_eq_add_one,
        show p - 1 + 1 = p by omega]
    have hνM : ν M ≠ ν (M - 1) := by
      have := hdiff (X.strandMap^[M - 1] g) (hrT _) (hnc _).1 (hnc _).2
        ⟨i₀, by rw [← Function.iterate_succ_apply' X.strandMap, Nat.succ_eq_add_one,
          show M - 1 + 1 = M by omega, hperM, hgpt]⟩
      simp only [hν]
      rwa [← Function.iterate_succ_apply' X.strandMap, Nat.succ_eq_add_one,
        show M - 1 + 1 = M by omega] at this
    have hν0 : ν M = ν 0 := by
      simp only [hν]
      rw [hperM]
      rfl
    obtain ⟨p, hp1, hp2, hp3⟩ := exists_ne_sub_one' (Nat.zero_le (M - 1))
      (show ν 0 ≠ ν (M - 1) by rw [← hν0]; exact hνM)
    obtain ⟨i, hi⟩ := hcross p hp1 hp3
    exact hfinal g 0 p hp1 (fun k _ _ => hrT k)
      (fun k _ _ => ⟨(hBoT k).1, (hBoT k).2, hnotC k, hSmem k⟩)
      (fun h' => by have := hinjM 0 p hM (by omega) h'; omega) ⟨i₀, hgpt⟩ ⟨i, hi⟩

/-- A triple diagram without badgons has no closed strands. -/
@[cluster_algebras "lem_no_closed_strands"]
theorem not_isClosedStrand_of_not_hasBadgon (hX : X.IsTripleDiagram) (hbad : ¬X.HasBadgon)
    (C : Finset H) : ¬X.IsClosedStrand C := by
  intro hC
  have hP := hX.toIsPreTripleDiagram
  have hmono : ¬X.HasMonogon := fun h => hbad (Or.inl h)
  -- a closed strand consisting of `out` darts
  obtain ⟨C', hC', hC'out⟩ : ∃ C', X.IsClosedStrand C' ∧ ∀ e ∈ C', X.isOut e = true := by
    obtain ⟨d, hdB, hCd, hCb⟩ := hC
    subst hCd
    have hconst : ∀ e ∈ X.strandOrbit d, e ∉ X.bdry ∧ X.isOut e = X.isOut d := by
      intro e he
      obtain ⟨k, rfl⟩ := X.mem_strandOrbit.1 he
      exact iterate_notMem_bdry_isOut hP hdB (n := k)
        (fun j _ => not_runsToEndpoint_iterate hCb j) k le_rfl
    cases hd : X.isOut d
    · refine ⟨(X.strandOrbit d).image X.inv, IsClosedStrand.image_inv hP ⟨d, hdB, rfl, hCb⟩,
        fun e he => ?_⟩
      obtain ⟨e', he', rfl⟩ := mem_image.1 he
      rw [hP.isOut_inv_apply (hconst e' he').1, (hconst e' he').2, hd]
      rfl
    · exact ⟨_, ⟨d, hdB, rfl, hCb⟩, fun e he => (hconst e he).2.trans hd⟩
  obtain ⟨d, hdB, rfl, hCb⟩ := hC'
  have hr := not_runsToEndpoint_iterate hCb
  have hr0 : ¬X.RunsToEndpoint d := hr 0
  have hdout : X.isOut d = true := hC'out d (X.mem_strandOrbit.2 ⟨0, rfl⟩)
  set r₀ := X.inv d with hr₀
  set g := X.rot r₀ with hgdef
  have hgv : X.vertexOf g = X.vertexOf r₀ := X.vertexOf_rot r₀
  have hgb : ¬X.IsBoundaryVertex (X.vertexOf g) := by rwa [hgv]
  have hgB : g ∉ X.bdry := X.notMem_bdry_of_not_isBoundaryVertex hgb
  have hgout : X.isOut g = true := by
    rw [hgdef, hP.isOut_rot_apply hr0, hP.isOut_inv_apply hdB, hdout]
    rfl
  have h6 := (hP.rot_pow_six hr0).2
  -- `g` is not a dart of the closed strand, otherwise a monogon
  have h7 : (X.rot ^ 3) ((X.rot ^ 4) r₀) = g := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, hP.rot_pow_mod_six hr0]
    change (X.rot ^ 1) r₀ = X.rot r₀
    rw [pow_one]
  have hgC : g ∉ X.strandOrbit d := by
    intro hgC
    obtain ⟨hm, hper, -⟩ := minimalPeriod_strandMap hr
    obtain ⟨k, hk⟩ := X.mem_strandOrbit.1 hgC
    obtain ⟨N, hN⟩ : ∃ N, N = Function.minimalPeriod X.strandMap d * (k + 1) := ⟨_, rfl⟩
    have hNk : k + 1 ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ hm
    have hNd : X.strandMap^[N] d = d := by
      rw [hN, Function.iterate_mul]
      exact Function.iterate_fixed hper _
    have hiter : ∀ l, X.strandMap^[l] g = X.strandMap^[l + k] d := by
      intro l
      rw [← hk, ← Function.iterate_add_apply]
    set U := (List.range' 0 (N - k + 1)).map fun l => X.strandMap^[l] g with hU
    have hUp : X.IsStrandPath U := isStrandPath_map_iterate (by omega)
      (fun l _ _ => by
        rw [hiter]
        have := iterate_notMem_bdry_isOut hP hdB (n := l + k) (fun j _ => hr j) _ le_rfl
        exact ⟨this.1, this.2.trans hdout⟩)
      (fun l _ _ => by rw [hiter]; exact hr _)
    have hUh := head?_map_iterate (X := X) (d := g) (s := 0) (n := N - k + 1) (by omega)
    have hUl := getLast?_map_iterate (X := X) (d := g) (s := 0) (n := N - k + 1) (by omega)
    rw [hiter, show 0 + (N - k + 1) - 1 + k = N by omega, hNd] at hUl
    have hcc' : ({(X.rot ^ 4) r₀, (X.rot ^ 3) ((X.rot ^ 4) r₀)} : Finset H) ≠
        {r₀, (X.rot ^ 3) r₀} := by
      rw [h7]
      intro heq
      have : r₀ ∈ ({(X.rot ^ 4) r₀, g} : Finset H) := by
        rw [heq]
        simp
      rcases mem_insert.1 this with h' | h'
      · have := h6 4 0 (by omega) (by omega) (by simpa using h'.symm)
        omega
      · have := h6 1 0 (by omega) (by omega) (by simpa [hgdef] using (mem_singleton.1 h').symm)
        omega
    obtain ⟨hmon, -⟩ := X.isMonogon_of_two_passes hP (X.vertexOf_mem_internalVertices.2 hr0)
      (X.rot_pow_apply_mem_vertexOf 4 r₀) (X.self_mem_vertexOf r₀) hcc' hUp
      (by rw [hUh, h7]; rfl)
      (fun e he => by
        rw [hUl, Option.mem_def, Option.some_inj] at he
        rw [← he])
    exact hmono ⟨U, hmon⟩
  -- the strand through `g`
  obtain ⟨T, hT, hgT⟩ : ∃ T : Finset H, ((∃ j, T = (X.arc j).toFinset) ∨
      (X.IsClosedStrand T ∧ ∀ e ∈ T, X.isOut e = true)) ∧ g ∈ T := by
    rcases X.mem_arc_or_forall_strandOrbit hP hgB hgout with ⟨j, hj⟩ | h
    · exact ⟨_, Or.inl ⟨j, rfl⟩, List.mem_toFinset.2 hj⟩
    · exact ⟨_, Or.inr ⟨⟨g, hgB, rfl, fun e he => (h e he).1⟩, fun e he => (h e he).2⟩,
        X.mem_strandOrbit.2 ⟨0, rfl⟩⟩
  have hpass : X.PassesThrough (X.strandOrbit d) (X.vertexOf g) := by
    refine ⟨X.vertexOf_mem_internalVertices.2 hgb, X.strandMap d,
      X.mem_strandOrbit.2 ⟨1, rfl⟩, ?_⟩
    rw [hgv]
    exact (strandStep_strandMap hr0).vertexOf_eq
  obtain ⟨P, Q, x, y, hPQ, -, -⟩ := exists_isParallelDigon_of_isClosedStrand hX hmono
    ⟨d, hdB, rfl, hCb⟩ hC'out hT hgT hgC hpass
  exact hbad (Or.inr ⟨P, Q, x, y, hPQ⟩)

end ClosedStrands

/-! ### Strands across a swivel move -/

section Swivel

variable {X}

omit [Fintype H] [DecidableEq H] in
private theorem perm_pow_three_apply (f : Equiv.Perm H) (e : H) : (f ^ 3) e = f (f (f e)) := rfl

/-- Let `X'` be the swivel move of `X` at the digon `{d₁, d₂}`, `d₂ = φ(d₁)`, and
`L* = {d₁, d̄₁, d₂, d̄₂}`. For a dart `z ∉ L*` whose reverse lies at a triple point, the first dart
outside `L*` among `S(z), S²(z), …` equals the first dart outside `L*` among `S'(z), S'²(z), …`,
and in both sequences at most one dart of `L*` precedes it: it is `S^{k+1}(z) = S'^{k'+1}(z)` with
`k, k' ≤ 1` and `S^j(z), S'^{j'}(z) ∈ L*` for `1 ≤ j ≤ k`, `1 ≤ j' ≤ k'`. (FWZ also assume
`z ∉ B`, which follows.) -/
@[cluster_algebras "lem_swivel_reduced_strand"]
theorem exists_iterate_strandMap_swivelMove (hX : X.IsPreTripleDiagram) {d₁ : H}
    (hd : X.IsDigon (X.faceOf d₁)) {z : H}
    (hzL : z ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H))
    (hz : ¬X.RunsToEndpoint z) :
    ∃ w ∉ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H),
      (∃ k ≤ 1, X.strandMap^[k + 1] z = w ∧ ∀ j, 1 ≤ j → j ≤ k →
        X.strandMap^[j] z ∈ ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) ∧
      (∃ k ≤ 1, (X.swivelMove d₁).strandMap^[k + 1] z = w ∧ ∀ j, 1 ≤ j → j ≤ k →
        (X.swivelMove d₁).strandMap^[j] z ∈
          ({d₁, X.inv d₁, X.facePerm d₁, X.inv (X.facePerm d₁)} : Finset H)) := by
  have hinv := hX.inv_involutive
  -- the digon
  obtain ⟨hf, e, hfe, hve⟩ := hd
  have hd₁B : d₁ ∉ X.bdry :=
    disjoint_left.1 (X.mem_internalFaces.1 hf).2 (X.self_mem_faceOf d₁)
  have hd₂B : X.facePerm d₁ ∉ X.bdry :=
    disjoint_left.1 (X.mem_internalFaces.1 hf).2 (X.facePerm_mem_faceOf d₁)
  have hd₁ : d₁ ∈ ({e, X.facePerm e} : Finset H) := hfe ▸ X.self_mem_faceOf d₁
  have hφφ : X.facePerm (X.facePerm d₁) = d₁ := by
    have hne : X.facePerm e ≠ e := fun h => hve (by rw [h])
    have hφe : X.facePerm (X.facePerm e) = e := by
      have h1 : X.facePerm e ∈ X.faceOf d₁ := by rw [hfe]; simp
      have h2 : X.facePerm (X.facePerm e) ∈ X.faceOf d₁ := by
        rw [← X.faceOf_eq_of_mem h1]; exact X.facePerm_mem_faceOf _
      rw [hfe] at h2
      rcases mem_insert.1 h2 with h | h
      · exact h
      · exact absurd (X.facePerm.injective (mem_singleton.1 h)) hne
    rcases mem_insert.1 hd₁ with h | h
    · rw [h, hφe]
    · rw [mem_singleton.1 h, hφe]
  have hv : X.vertexOf d₁ ≠ X.vertexOf (X.facePerm d₁) := by
    rcases mem_insert.1 hd₁ with h | h
    · rwa [h]
    · have h' : d₁ = X.facePerm e := mem_singleton.1 h
      have hd' : X.facePerm d₁ = e := by
        rw [h'] at hφφ ⊢
        exact X.facePerm.injective hφφ
      rw [hd', h']
      exact Ne.symm hve
  set d₂ := X.facePerm d₁ with hd₂def
  set X' := X.swivelMove d₁ with hX'
  have hφφ' : X.rot (X.inv d₂) = d₁ := hφφ
  have hφ : X.rot (X.inv d₁) = d₂ := rfl
  have hint₁ : ¬X.IsBoundaryVertex (X.vertexOf d₁) := by
    intro hbv
    have hmem : X.inv d₂ ∈ X.vertexOf d₁ := by
      rw [← hφφ', X.vertexOf_rot]; exact X.self_mem_vertexOf _
    have heq := DiskMap.eq_of_notMem_bdry hX.boundaryVertex_card hbv hmem
      (X.self_mem_vertexOf d₁) (hX.inv_notMem_bdry hd₂B) hd₁B
    exact DiskMap.rot_ne_of_isBoundaryVertex hX.boundaryVertex_card hbv (by rwa [heq] at hφφ')
  have hint₂ : ¬X.IsBoundaryVertex (X.vertexOf d₂) := by
    intro hbv
    have hmem : X.inv d₁ ∈ X.vertexOf d₂ := by
      rw [← hφ, X.vertexOf_rot]; exact X.self_mem_vertexOf _
    have heq := DiskMap.eq_of_notMem_bdry hX.boundaryVertex_card hbv hmem
      (X.self_mem_vertexOf d₂) (hX.inv_notMem_bdry hd₁B) hd₂B
    exact DiskMap.rot_ne_of_isBoundaryVertex hX.boundaryVertex_card hbv (by rwa [heq] at hφ)
  obtain ⟨h6₁, hinj₁⟩ := hX.rot_pow_six hint₁
  obtain ⟨h6₂, hinj₂⟩ := hX.rot_pow_six hint₂
  have hs : ∀ (u : H) (k : ℕ), X.rot ((X.rot ^ k) u) = (X.rot ^ (k + 1)) u := fun u k => by
    rw [pow_succ', Equiv.Perm.mul_apply]
  have h5₁ : (X.rot ^ 5) d₁ = X.inv d₂ := X.rot.injective (by rw [hφφ', hs]; exact h6₁)
  have h5₂ : (X.rot ^ 5) d₂ = X.inv d₁ := X.rot.injective (by rw [hφ, hs]; exact h6₂)
  have hcross : ∀ i j : ℕ, (X.rot ^ i) d₁ ≠ (X.rot ^ j) d₂ := by
    intro i j h
    apply hv
    have h1 := X.vertexOf_rot_pow_apply i d₁
    have h2 := X.vertexOf_rot_pow_apply j d₂
    rw [← h1, ← h2, h]
  -- notation for the twelve darts
  set A : ℕ → H := fun k => (X.rot ^ k) d₁ with hA
  set B : ℕ → H := fun k => (X.rot ^ k) d₂ with hB
  have hA0 : A 0 = d₁ := by simp [hA]
  have hB0 : B 0 = d₂ := by simp [hB]
  have hA5 : A 5 = X.inv d₂ := h5₁
  have hB5 : B 5 = X.inv d₁ := h5₂
  have hAs : ∀ k, X.rot (A k) = A (k + 1) := fun k => hs d₁ k
  have hBs : ∀ k, X.rot (B k) = B (k + 1) := fun k => hs d₂ k
  have hA6 : ∀ k, A (k + 6) = A k := by
    intro k
    simp only [hA]
    rw [pow_add, Equiv.Perm.mul_apply, h6₁]
  have hB6 : ∀ k, B (k + 6) = B k := by
    intro k
    simp only [hB]
    rw [pow_add, Equiv.Perm.mul_apply, h6₂]
  have hA3 : ∀ k, (X.rot ^ 3) (A k) = A (k + 3) := by
    intro k
    simp only [hA]
    rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
  have hB3 : ∀ k, (X.rot ^ 3) (B k) = B (k + 3) := by
    intro k
    simp only [hB]
    rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
  have hAA : ∀ i j, i < 6 → j < 6 → A i = A j → i = j := hinj₁
  have hBB : ∀ i j, i < 6 → j < 6 → B i = B j → i = j := hinj₂
  have hAB : ∀ i j, A i ≠ B j := hcross
  have hiA0 : X.inv (A 0) = B 5 := by rw [hA0, hB5]
  have hiA5 : X.inv (A 5) = B 0 := by rw [hA5, hinv, hB0]
  have hiB0 : X.inv (B 0) = A 5 := by rw [hB0, hA5]
  have hiB5 : X.inv (B 5) = A 0 := by rw [hB5, hinv, hA0]
  have hL : ({d₁, X.inv d₁, d₂, X.inv d₂} : Finset H) = {A 0, B 5, B 0, A 5} := by
    rw [hA0, hB5, hB0, hA5]
  rw [hL] at hzL ⊢
  -- the swivel rotation on the twelve darts
  have hnd' : [A 0, A 2, A 4, B 0, B 2, B 4].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    refine ⟨⟨fun h => ?_, fun h => ?_, hAB _ _, hAB _ _, hAB _ _⟩, ⟨fun h => ?_, hAB _ _,
      hAB _ _, hAB _ _⟩, ⟨hAB _ _, hAB _ _, hAB _ _⟩, ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
    · have := hAA 0 2 (by omega) (by omega) h; omega
    · have := hAA 0 4 (by omega) (by omega) h; omega
    · have := hAA 2 4 (by omega) (by omega) h; omega
    · have := hBB 0 2 (by omega) (by omega) h; omega
    · have := hBB 0 4 (by omega) (by omega) h; omega
    · have := hBB 2 4 (by omega) (by omega) h; omega
  have hnd : [d₁, (X.rot ^ 2) d₁, (X.rot ^ 4) d₁, X.facePerm d₁, (X.rot ^ 2) (X.facePerm d₁),
      (X.rot ^ 4) (X.facePerm d₁)].Nodup := by
    simpa only [hA, hB, pow_zero, Equiv.Perm.one_apply] using hnd'
  obtain ⟨s0, s2, t4, s4, t0, t2⟩ := X.swivelRot_apply_six hnd
  have hX'rot : X'.rot = X.swivelRot d₁ := rfl
  -- `σ'` agrees with `σ` off the six darts `d₁, a₂, a₄, d₂, b₂, b₄`
  have hoff : ∀ u, u ≠ A 0 → u ≠ A 2 → u ≠ A 4 → u ≠ B 0 → u ≠ B 2 → u ≠ B 4 →
      X'.rot u = X.rot u := by
    intro u h1 h2 h3 h4 h5 h6
    rw [hA0] at h1
    rw [hB0] at h4
    exact X.swivelRot_apply_of_ne h1 h2 h3 h4 h5 h6
  have neAA : ∀ i j, i < 6 → j < 6 → i ≠ j → A i ≠ A j := fun i j hi hj hij h =>
    hij (hAA i j hi hj h)
  have neBB : ∀ i j, i < 6 → j < 6 → i ≠ j → B i ≠ B j := fun i j hi hj hij h =>
    hij (hBB i j hi hj h)
  have neBA : ∀ i j, B i ≠ A j := fun i j h => hAB j i h.symm
  have r'A0 : X'.rot (A 0) = A 3 := by
    change X.swivelRot d₁ d₁ = (X.rot ^ 3) d₁
    rw [s0, hs]
  have r'A1 : X'.rot (A 1) = A 2 := by
    rw [hoff _ (neAA 1 0 (by omega) (by omega) (by omega)) (neAA 1 2 (by omega) (by omega)
      (by omega)) (neAA 1 4 (by omega) (by omega) (by omega)) (hAB _ _) (hAB _ _) (hAB _ _),
      hAs]
  have r'A2 : X'.rot (A 2) = B 5 := by
    change X.swivelRot d₁ ((X.rot ^ 2) d₁) = (X.rot ^ 5) (X.facePerm d₁)
    rw [s2, hs]
  have r'A3 : X'.rot (A 3) = A 4 := by
    rw [hoff _ (neAA 3 0 (by omega) (by omega) (by omega)) (neAA 3 2 (by omega) (by omega)
      (by omega)) (neAA 3 4 (by omega) (by omega) (by omega)) (hAB _ _) (hAB _ _) (hAB _ _),
      hAs]
  have r'A4 : X'.rot (A 4) = B 1 := by
    change X.swivelRot d₁ ((X.rot ^ 4) d₁) = (X.rot ^ 1) (X.facePerm d₁)
    rw [s4, pow_one]
  have r'A5 : X'.rot (A 5) = A 0 := by
    rw [hoff _ (neAA 5 0 (by omega) (by omega) (by omega)) (neAA 5 2 (by omega) (by omega)
      (by omega)) (neAA 5 4 (by omega) (by omega) (by omega)) (hAB _ _) (hAB _ _) (hAB _ _),
      hAs, hA6 0]
  have r'B0 : X'.rot (B 0) = B 3 := by
    change X.swivelRot d₁ (X.facePerm d₁) = (X.rot ^ 3) (X.facePerm d₁)
    rw [t0, hs]
  have r'B1 : X'.rot (B 1) = B 2 := by
    rw [hoff _ (neBA _ _) (neBA _ _) (neBA _ _) (neBB 1 0 (by omega) (by omega) (by omega))
      (neBB 1 2 (by omega) (by omega) (by omega)) (neBB 1 4 (by omega) (by omega) (by omega)),
      hBs]
  have r'B2 : X'.rot (B 2) = A 5 := by
    change X.swivelRot d₁ ((X.rot ^ 2) (X.facePerm d₁)) = (X.rot ^ 5) d₁
    rw [t2, hs]
  have r'B3 : X'.rot (B 3) = B 4 := by
    rw [hoff _ (neBA _ _) (neBA _ _) (neBA _ _) (neBB 3 0 (by omega) (by omega) (by omega))
      (neBB 3 2 (by omega) (by omega) (by omega)) (neBB 3 4 (by omega) (by omega) (by omega)),
      hBs]
  have r'B4 : X'.rot (B 4) = A 1 := by
    change X.swivelRot d₁ ((X.rot ^ 4) (X.facePerm d₁)) = (X.rot ^ 1) d₁
    rw [t4, pow_one]
  have r'B5 : X'.rot (B 5) = B 0 := by
    rw [hoff _ (neBA _ _) (neBA _ _) (neBA _ _) (neBB 5 0 (by omega) (by omega) (by omega))
      (neBB 5 2 (by omega) (by omega) (by omega)) (neBB 5 4 (by omega) (by omega) (by omega)),
      hBs, hB6 0]
  -- the darts of `x ∪ y`
  set XY : Finset H := X.vertexOf d₁ ∪ X.vertexOf d₂ with hXY
  have hmemXY : ∀ u, u ∈ XY ↔ ∃ k < 6, u = A k ∨ u = B k := by
    intro u
    constructor
    · intro hu
      rcases mem_union.1 hu with hu | hu
      · obtain ⟨n, hn⟩ := (X.mem_vertexOf.1 hu).exists_nat_pow_eq
        rw [hX.rot_pow_mod_six hint₁] at hn
        exact ⟨n % 6, Nat.mod_lt _ (by omega), Or.inl hn.symm⟩
      · obtain ⟨n, hn⟩ := (X.mem_vertexOf.1 hu).exists_nat_pow_eq
        rw [hX.rot_pow_mod_six hint₂] at hn
        exact ⟨n % 6, Nat.mod_lt _ (by omega), Or.inr hn.symm⟩
    · rintro ⟨k, -, rfl | rfl⟩
      · exact mem_union_left _ (X.rot_pow_apply_mem_vertexOf k d₁)
      · exact mem_union_right _ (X.rot_pow_apply_mem_vertexOf k d₂)
  have hXYb : ∀ u ∈ XY, u ∉ X.bdry := by
    intro u hu hB'
    rcases mem_union.1 hu with hu | hu
    · exact hint₁ ⟨u, hu, hB'⟩
    · exact hint₂ ⟨u, hu, hB'⟩
  -- `σ'` preserves `x ∪ y`
  have hrXY : ∀ u ∈ XY, X'.rot u ∈ XY := by
    intro u hu
    obtain ⟨k, hk, rfl | rfl⟩ := (hmemXY u).1 hu <;> rw [hmemXY] <;> interval_cases k
    · exact ⟨3, by omega, Or.inl r'A0⟩
    · exact ⟨2, by omega, Or.inl r'A1⟩
    · exact ⟨5, by omega, Or.inr r'A2⟩
    · exact ⟨4, by omega, Or.inl r'A3⟩
    · exact ⟨1, by omega, Or.inr r'A4⟩
    · exact ⟨0, by omega, Or.inl r'A5⟩
    · exact ⟨3, by omega, Or.inr r'B0⟩
    · exact ⟨2, by omega, Or.inr r'B1⟩
    · exact ⟨5, by omega, Or.inl r'B2⟩
    · exact ⟨4, by omega, Or.inr r'B3⟩
    · exact ⟨1, by omega, Or.inl r'B4⟩
    · exact ⟨0, by omega, Or.inr r'B5⟩
  have hXY'b : ∀ u ∈ XY, ¬X'.IsBoundaryVertex (X'.vertexOf u) := by
    intro u hu ⟨e', he', heB⟩
    obtain ⟨n, rfl⟩ := (X'.mem_vertexOf.1 he').exists_nat_pow_eq
    have : ∀ n : ℕ, (X'.rot ^ n) u ∈ XY := by
      intro n
      induction n with
      | zero => simpa using hu
      | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hrXY _ ih
    exact hXYb _ (this n) heB
  have hXYt : ∀ u ∈ XY, ¬X.IsBoundaryVertex (X.vertexOf u) := by
    intro u hu
    rcases mem_union.1 hu with hu | hu
    · rw [X.vertexOf_eq_of_mem hu]; exact hint₁
    · rw [X.vertexOf_eq_of_mem hu]; exact hint₂
  have hAXY : ∀ k, A k ∈ XY := fun k => mem_union_left _ (X.rot_pow_apply_mem_vertexOf k d₁)
  have hBXY : ∀ k, B k ∈ XY := fun k => mem_union_right _ (X.rot_pow_apply_mem_vertexOf k d₂)
  -- the strand maps at darts whose reverse lies in `x ∪ y`
  have hS : ∀ u, X.inv u ∈ XY → X.strandMap u = (X.rot ^ 3) (X.inv u) := by
    intro u hu
    rw [X.strandMap_of_not_runsToEndpoint (hXYt _ hu)]
    rfl
  have hS' : ∀ u, X.inv u ∈ XY → X'.strandMap u = (X'.rot ^ 3) (X.inv u) := by
    intro u hu
    rw [X'.strandMap_of_not_runsToEndpoint (hXY'b _ hu)]
    rfl
  have hLA : ∀ k, k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 → A k ∉ ({A 0, B 5, B 0, A 5} : Finset H) := by
    intro k hk
    simp only [mem_insert, mem_singleton, not_or]
    refine ⟨neAA k 0 (by omega) (by omega) (by omega), hAB _ _, hAB _ _,
      neAA k 5 (by omega) (by omega) (by omega)⟩
  have hLB : ∀ k, k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 → B k ∉ ({A 0, B 5, B 0, A 5} : Finset H) := by
    intro k hk
    simp only [mem_insert, mem_singleton, not_or]
    refine ⟨neBA _ _, neBB k 5 (by omega) (by omega) (by omega),
      neBB k 0 (by omega) (by omega) (by omega), neBA _ _⟩
  have hmA0 : A 0 ∈ ({A 0, B 5, B 0, A 5} : Finset H) := by simp
  have hmB5 : B 5 ∈ ({A 0, B 5, B 0, A 5} : Finset H) := by simp
  have hmB0 : B 0 ∈ ({A 0, B 5, B 0, A 5} : Finset H) := by simp
  have hmA5 : A 5 ∈ ({A 0, B 5, B 0, A 5} : Finset H) := by simp
  have it1 : ∀ (f : H → H) (u : H), f^[0 + 1] u = f u := fun _ _ => rfl
  have it2 : ∀ (f : H → H) (u : H), f^[1 + 1] u = f (f u) := fun _ _ => rfl
  have one_le_one : ∀ j, 1 ≤ j → j ≤ 1 → j = 1 := fun j h1 h2 => by omega
  have no_j : ∀ j, 1 ≤ j → j ≤ 0 → False := fun j h1 h2 => by omega
  by_cases hzXY : X.inv z ∈ XY
  · obtain ⟨k, hk, hzk | hzk⟩ := (hmemXY _).1 hzXY
    · have hz' : z = X.inv (A k) := by rw [← hzk, hinv]
      interval_cases k
      · exact absurd (hz' ▸ hiA0 ▸ hmB5) hzL
      · -- `z̄ = a₁`
        refine ⟨A 4, hLA 4 (by omega), ⟨0, by omega, ?_, fun j h1 h2 => (no_j j h1 h2).elim⟩,
          ⟨1, le_rfl, ?_, fun j h1 h2 => ?_⟩⟩
        · rw [it1, hS _ hzXY, hzk, hA3]
        · rw [it2, hS' _ hzXY, hzk, perm_pow_three_apply, r'A1, r'A2, r'B5,
            hS' _ (by rw [hiB0]; exact hAXY 5), hiB0, perm_pow_three_apply, r'A5, r'A0, r'A3]
        · rw [one_le_one j h1 h2, Function.iterate_one, hS' _ hzXY, hzk, perm_pow_three_apply,
            r'A1, r'A2, r'B5]
          exact hmB0
      · -- `z̄ = a₂`
        refine ⟨B 3, hLB 3 (by omega), ⟨1, le_rfl, ?_, fun j h1 h2 => ?_⟩,
          ⟨0, by omega, ?_, fun j h1 h2 => (no_j j h1 h2).elim⟩⟩
        · rw [it2, hS _ hzXY, hzk, hA3, hS _ (by rw [hiA5]; exact hBXY 0), hiA5, hB3]
        · rw [one_le_one j h1 h2, Function.iterate_one, hS _ hzXY, hzk, hA3]
          exact hmA5
        · rw [it1, hS' _ hzXY, hzk, perm_pow_three_apply, r'A2, r'B5, r'B0]
      · -- `z̄ = a₃`
        refine ⟨B 2, hLB 2 (by omega), ⟨1, le_rfl, ?_, fun j h1 h2 => ?_⟩,
          ⟨0, by omega, ?_, fun j h1 h2 => (no_j j h1 h2).elim⟩⟩
        · rw [it2, hS _ hzXY, hzk, hA3, hA6 0, hS _ (by rw [hiA0]; exact hBXY 5), hiA0, hB3,
            show 5 + 3 = 2 + 6 by rfl, hB6]
        · rw [one_le_one j h1 h2, Function.iterate_one, hS _ hzXY, hzk, hA3, hA6 0]
          exact hmA0
        · rw [it1, hS' _ hzXY, hzk, perm_pow_three_apply, r'A3, r'A4, r'B1]
      · -- `z̄ = a₄`
        refine ⟨A 1, hLA 1 (by omega), ⟨0, by omega, ?_, fun j h1 h2 => (no_j j h1 h2).elim⟩,
          ⟨1, le_rfl, ?_, fun j h1 h2 => ?_⟩⟩
        · rw [it1, hS _ hzXY, hzk, hA3, show 4 + 3 = 1 + 6 by rfl, hA6]
        · rw [it2, hS' _ hzXY, hzk, perm_pow_three_apply, r'A4, r'B1, r'B2,
            hS' _ (by rw [hiA5]; exact hBXY 0), hiA5, perm_pow_three_apply, r'B0, r'B3, r'B4]
        · rw [one_le_one j h1 h2, Function.iterate_one, hS' _ hzXY, hzk, perm_pow_three_apply,
            r'A4, r'B1, r'B2]
          exact hmA5
      · exact absurd (hz' ▸ hiA5 ▸ hmB0) hzL
    · have hz' : z = X.inv (B k) := by rw [← hzk, hinv]
      interval_cases k
      · exact absurd (hz' ▸ hiB0 ▸ hmA5) hzL
      · -- `z̄ = b₁`
        refine ⟨B 4, hLB 4 (by omega), ⟨0, by omega, ?_, fun j h1 h2 => (no_j j h1 h2).elim⟩,
          ⟨1, le_rfl, ?_, fun j h1 h2 => ?_⟩⟩
        · rw [it1, hS _ hzXY, hzk, hB3]
        · rw [it2, hS' _ hzXY, hzk, perm_pow_three_apply, r'B1, r'B2, r'A5,
            hS' _ (by rw [hiA0]; exact hBXY 5), hiA0, perm_pow_three_apply, r'B5, r'B0, r'B3]
        · rw [one_le_one j h1 h2, Function.iterate_one, hS' _ hzXY, hzk, perm_pow_three_apply,
            r'B1, r'B2, r'A5]
          exact hmA0
      · -- `z̄ = b₂`
        refine ⟨A 3, hLA 3 (by omega), ⟨1, le_rfl, ?_, fun j h1 h2 => ?_⟩,
          ⟨0, by omega, ?_, fun j h1 h2 => (no_j j h1 h2).elim⟩⟩
        · rw [it2, hS _ hzXY, hzk, hB3, hS _ (by rw [hiB5]; exact hAXY 0), hiB5, hA3]
        · rw [one_le_one j h1 h2, Function.iterate_one, hS _ hzXY, hzk, hB3]
          exact hmB5
        · rw [it1, hS' _ hzXY, hzk, perm_pow_three_apply, r'B2, r'A5, r'A0]
      · -- `z̄ = b₃`
        refine ⟨A 2, hLA 2 (by omega), ⟨1, le_rfl, ?_, fun j h1 h2 => ?_⟩,
          ⟨0, by omega, ?_, fun j h1 h2 => (no_j j h1 h2).elim⟩⟩
        · rw [it2, hS _ hzXY, hzk, hB3, hB6 0, hS _ (by rw [hiB0]; exact hAXY 5), hiB0, hA3,
            show 5 + 3 = 2 + 6 by rfl, hA6]
        · rw [one_le_one j h1 h2, Function.iterate_one, hS _ hzXY, hzk, hB3, hB6 0]
          exact hmB0
        · rw [it1, hS' _ hzXY, hzk, perm_pow_three_apply, r'B3, r'B4, r'A1]
      · -- `z̄ = b₄`
        refine ⟨B 1, hLB 1 (by omega), ⟨0, by omega, ?_, fun j h1 h2 => (no_j j h1 h2).elim⟩,
          ⟨1, le_rfl, ?_, fun j h1 h2 => ?_⟩⟩
        · rw [it1, hS _ hzXY, hzk, hB3, show 4 + 3 = 1 + 6 by rfl, hB6]
        · rw [it2, hS' _ hzXY, hzk, perm_pow_three_apply, r'B4, r'A1, r'A2,
            hS' _ (by rw [hiB5]; exact hAXY 0), hiB5, perm_pow_three_apply, r'A0, r'A3, r'A4]
        · rw [one_le_one j h1 h2, Function.iterate_one, hS' _ hzXY, hzk, perm_pow_three_apply,
            r'B4, r'A1, r'A2]
          exact hmB5
      · exact absurd (hz' ▸ hiB5 ▸ hmA0) hzL
  · -- away from `x ∪ y` both strand maps take one step
    have hvz : ∀ u ∈ X.vertexOf (X.inv z), u ∉ XY := by
      intro u hu huXY
      apply hzXY
      have hvu : X.vertexOf u = X.vertexOf (X.inv z) := X.vertexOf_eq_of_mem hu
      rcases mem_union.1 huXY with h' | h'
      · exact mem_union_left _
          ((X.mem_vertexOf_iff_vertexOf_eq).2 (hvu.symm.trans (X.vertexOf_eq_of_mem h')))
      · exact mem_union_right _
          ((X.mem_vertexOf_iff_vertexOf_eq).2 (hvu.symm.trans (X.vertexOf_eq_of_mem h')))
    have hagree : ∀ u ∈ X.vertexOf (X.inv z), X'.rot u = X.rot u := by
      intro u hu
      have hu' := hvz u hu
      exact hoff u (fun h => hu' (h ▸ hAXY 0)) (fun h => hu' (h ▸ hAXY 2))
        (fun h => hu' (h ▸ hAXY 4)) (fun h => hu' (h ▸ hBXY 0)) (fun h => hu' (h ▸ hBXY 2))
        (fun h => hu' (h ▸ hBXY 4))
    have hpow : ∀ n : ℕ, (X'.rot ^ n) (X.inv z) = (X.rot ^ n) (X.inv z) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih,
          hagree _ (X.rot_pow_apply_mem_vertexOf n _)]
    have hvert : X'.vertexOf (X.inv z) = X.vertexOf (X.inv z) := by
      ext u
      rw [X'.mem_vertexOf, X.mem_vertexOf]
      constructor
      · intro h
        obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
        rw [hpow n]
        exact ⟨n, by simp⟩
      · intro h
        obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
        rw [← hpow n]
        exact ⟨n, by simp⟩
    have hz' : ¬X'.RunsToEndpoint z := by
      change ¬X'.IsBoundaryVertex (X'.vertexOf (X.inv z))
      rw [hvert]
      intro ⟨u, hu, huB⟩
      exact hz ⟨u, hu, huB⟩
    have hw : (X.rot ^ 3) (X.inv z) ∉ ({A 0, B 5, B 0, A 5} : Finset H) := by
      intro hmem
      apply hvz _ (X.rot_pow_apply_mem_vertexOf 3 _)
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with h | h | h | h <;> rw [h]
      · exact hAXY 0
      · exact hBXY 5
      · exact hBXY 0
      · exact hAXY 5
    refine ⟨(X.rot ^ 3) (X.inv z), hw, ⟨0, by omega, ?_, fun j h1 h2 => (no_j j h1 h2).elim⟩,
      ⟨0, by omega, ?_, fun j h1 h2 => (no_j j h1 h2).elim⟩⟩
    · rw [it1, X.strandMap_of_not_runsToEndpoint hz]
      rfl
    · rw [it1, X'.strandMap_of_not_runsToEndpoint hz']
      change (X'.rot ^ 3) (X.inv z) = _
      exact hpow 3

end Swivel

end TripleData

end ClusterAlgebras

/-! ## The removal of a hollow monogon -/

namespace ClusterAlgebras

open Finset Equiv

/-! ### Counting orbits on invariant sets -/

section OrbitsOn

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The orbits of `π` through the elements of `S`. -/
private def orbitsOn (π : Perm α) (S : Finset α) : Finset (Finset α) :=
  S.image fun d => ({e | π.SameCycle d e} : Finset α)

omit [Fintype α] [DecidableEq α] in
private theorem sameCycle_closed [Finite α] {π : Perm α} {p : α → Prop} (hp : ∀ d, p (π d) ↔ p d)
    {d e : α} (hd : p d) (h : π.SameCycle d e) : p e := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using hd
  | succ n ih => rw [pow_succ', Perm.mul_apply]; exact (hp _).2 ih

private theorem card_orbitsOn_union {π : Perm α} {S T : Finset α} (hT : ∀ d, π d ∈ T ↔ d ∈ T)
    (hST : Disjoint S T) :
    (orbitsOn π (S ∪ T)).card = (orbitsOn π S).card + (orbitsOn π T).card := by
  rw [orbitsOn, image_union, card_union_of_disjoint]
  · rfl
  rw [disjoint_left]
  intro o ho ho'
  obtain ⟨s, hs, rfl⟩ := mem_image.1 ho
  obtain ⟨t, ht, hts⟩ := mem_image.1 ho'
  have : s ∈ ({e | π.SameCycle t e} : Finset α) := by rw [hts]; simp [Perm.SameCycle.refl]
  simp only [mem_filter, mem_univ, true_and] at this
  exact disjoint_left.1 hST hs (sameCycle_closed (p := (· ∈ T)) hT ht this)

private theorem numOrbits_subtypePerm {π : Perm α} {p : α → Prop} [DecidablePred p]
    (h : ∀ d, p (π d) ↔ p d) :
    numOrbits (π.subtypePerm h) = (orbitsOn π (univ.filter p)).card := by
  rw [numOrbits_eq_card_image]
  have key : ∀ x : Subtype p,
      ({y | (π.subtypePerm h).SameCycle x y} : Finset (Subtype p)).map
        (Function.Embedding.subtype p) =
        ({e | π.SameCycle x e} : Finset α) := by
    intro x
    ext e
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
      Perm.sameCycle_subtypePerm]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro he
      exact ⟨⟨e, sameCycle_closed h x.2 he⟩, he, rfl⟩
  have himg : (univ.image fun x : Subtype p =>
      ({y | (π.subtypePerm h).SameCycle x y} : Finset (Subtype p))).image
        (Finset.map (Function.Embedding.subtype p)) = orbitsOn π (univ.filter p) := by
    ext o
    simp only [mem_image, mem_univ, true_and, orbitsOn, mem_filter]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, x.2, (key x).symm⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨_, ⟨⟨d, hd⟩, rfl⟩, key ⟨d, hd⟩⟩
  rw [← himg, card_image_of_injective _ (Finset.map_injective _)]

private theorem numOrbits_subtypePerm_finset {π : Perm α} {S : Finset α} (h : ∀ d,
    π d ∈ S ↔ d ∈ S) :
    numOrbits (π.subtypePerm h) = (orbitsOn π S).card := by
  rw [numOrbits_subtypePerm, filter_mem_eq_inter, univ_inter]

private theorem numOrbits_eq_card_orbitsOn (π : Perm α) : numOrbits π = (orbitsOn π univ).card :=
  numOrbits_eq_card_image π

omit [Fintype α] [DecidableEq α] in
private theorem sameCycle_iff_of_involutive [Finite α] {ι : Perm α} (hinv : Function.Involutive ι)
    {d e : α} : ι.SameCycle d e ↔ e = d ∨ e = ι d := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      rcases ih (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)) with h | h <;> rw [h]
      · exact Or.inr rfl
      · exact Or.inl (hinv d)
  · rintro (rfl | rfl)
    · exact Perm.SameCycle.refl _ _
    · exact Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)

private theorem two_mul_card_orbitsOn {ι : Perm α} (hinv : Function.Involutive ι) {S : Finset α}
    (hne : ∀ d ∈ S, ι d ≠ d) (hS : ∀ d, ι d ∈ S ↔ d ∈ S) : 2 * (orbitsOn ι S).card = S.card := by
  have horb : ∀ d, ({e | ι.SameCycle d e} : Finset α) = {d, ι d} := by
    intro d
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
      sameCycle_iff_of_involutive hinv]
  rw [card_eq_sum_card_image (fun d => ({e | ι.SameCycle d e} : Finset α)) S, orbitsOn,
    sum_const_nat (m := 2), mul_comm]
  intro o ho
  obtain ⟨d, hd, rfl⟩ := mem_image.1 ho
  have hfil : (S.filter fun a => ({e | ι.SameCycle a e} : Finset α) =
      ({e | ι.SameCycle d e} : Finset α)) = {d, ι d} := by
    ext a
    simp only [mem_filter, horb, mem_insert, mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      have := h ▸ (mem_insert_self a {ι a})
      simpa using this
    · rintro (rfl | rfl)
      · exact ⟨hd, rfl⟩
      · exact ⟨(hS _).2 hd, by rw [hinv d, pair_comm]⟩
  rw [hfil, card_pair (hne d hd).symm]

end OrbitsOn

/-! ### Rotation systems and orbits -/

namespace RotationSystem

variable {H : Type*} [Fintype H] [DecidableEq H] (R : RotationSystem H)

private theorem vertices_eq_orbitsOn : R.vertices = orbitsOn R.rot univ := rfl

private theorem faceOrbits_eq_orbitsOn : R.faceOrbits = orbitsOn R.facePerm univ := rfl

private theorem edges_eq_orbitsOn (hinv : Function.Involutive R.inv) :
    R.edges = orbitsOn R.inv univ := by
  simp only [edges, orbitsOn]
  congr 1
  funext d
  ext e
  simp [edgeOf, sameCycle_iff_of_involutive hinv]

end RotationSystem

end ClusterAlgebras

namespace ClusterAlgebras

open Finset Equiv

/-! ### First returns of inverses -/

section FirstReturnInv

variable {α : Type*} [Finite α]

/-- The first return of `π⁻¹` undoes the first return of `π`. -/
private theorem firstReturn_inv_firstReturn (π : Perm α) (Y : Set α) (y : Y) :
    firstReturn π⁻¹ Y (firstReturn π Y y) = y := by
  set m := firstReturnTime π Y y with hm
  have hpos : 0 < m := firstReturnTime_pos y
  have hback : ∀ j, j ≤ m → (π⁻¹ ^ j) ((π ^ m) y) = (π ^ (m - j)) y := by
    intro j hj
    conv_lhs => rw [show m = j + (m - j) by omega, pow_add, Perm.mul_apply, inv_pow]
    simp
  have hz : ((firstReturn π Y y : Y) : α) = (π ^ m) y := coe_firstReturn π Y y
  apply Subtype.ext
  rw [coe_firstReturn_of_pow (m := m) hpos]
  · rw [hz, hback m le_rfl, Nat.sub_self, pow_zero, Perm.one_apply]
  · rw [hz, hback m le_rfl, Nat.sub_self, pow_zero, Perm.one_apply]
    exact y.2
  · intro j hj hjm
    rw [hz, hback j hjm.le]
    exact pow_apply_notMem_of_lt_firstReturnTime (by omega) (by omega)

/-- Conjugating by a permutation `κ` that fixes `Y` pointwise and preserves it does not change the
first return to `Y`. -/
private theorem firstReturn_conj {π κ : Perm α} {Y : Set α} (hκ : ∀ x, κ x ∈ Y ↔ x ∈ Y)
    (hfix : ∀ y ∈ Y, κ y = y) (y : Y) :
    firstReturn (κ * π * κ⁻¹) Y y = firstReturn π Y y := by
  have hpow : ∀ n : ℕ, ((κ * π * κ⁻¹) ^ n) y = κ ((π ^ n) y) := by
    intro n
    rw [conj_pow, Perm.mul_apply, Perm.mul_apply]
    congr 2
    rw [Perm.inv_eq_iff_eq, hfix _ y.2]
  set m := firstReturnTime π Y y
  apply Subtype.ext
  rw [coe_firstReturn π Y y, coe_firstReturn_of_pow (m := m) (firstReturnTime_pos y)]
  · rw [hpow, hfix _ (pow_firstReturnTime_apply_mem y)]
  · rw [hpow, hκ]
    exact pow_firstReturnTime_apply_mem y
  · intro j hj hjm
    rw [hpow, hκ]
    exact pow_apply_notMem_of_lt_firstReturnTime hj hjm

end FirstReturnInv

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)

/-! ### Hollow monogons -/

/-- Basic facts about a hollow monogon `{c}` at the triple point `x = v(c)`: `c ∉ B`,
`σ(c̄) = c`, `x` is a triple point, and its rotation is `(c, σ c, …, σ⁵ c = c̄)`. -/
theorem hollowMonogon_facts {X : TripleData H b} (hX : X.IsPreTripleDiagram) {c : H}
    (hc : X.IsHollowMonogon {c}) :
    c ∉ X.bdry ∧ X.rot (X.inv c) = c ∧ ¬X.IsBoundaryVertex (X.vertexOf c) ∧
      (X.rot ^ 5) c = X.inv c ∧ (X.rot ^ 6) c = c ∧
      ∀ i j : ℕ, i < 6 → j < 6 → (X.rot ^ i) c = (X.rot ^ j) c → i = j := by
  obtain ⟨hcB, hφ⟩ := hc.facePerm_eq
  have hφ' : X.rot (X.inv c) = c := hφ
  have hx : ¬X.IsBoundaryVertex (X.vertexOf c) := by
    cases ho : X.isOut c
    · have h' : X.isOut (X.inv c) = true := by rw [hX.isOut_inv_apply hcB, ho]; rfl
      exact (X.isMonogon_of_isHollowMonogon hX hc (Or.inr rfl) h').2.1
    · exact (X.isMonogon_of_isHollowMonogon hX hc (Or.inl rfl) ho).2.1
  obtain ⟨h6, hinj⟩ := hX.rot_pow_six hx
  refine ⟨hcB, hφ', hx, X.rot.injective ?_, h6, hinj⟩
  rw [hφ', ← Equiv.Perm.mul_apply, ← pow_succ']
  exact h6

/-- The involution `μ` of the darts of the vertex `x = v(c)` of a hollow monogon `{c}`, whose
rotation is `(c̄, c, a₁, a₂, a₃, a₄)`, `aₖ = σᵏ c`: it exchanges `c̄ ↔ c`, `a₂ ↔ a₃` and
`a₁ ↔ a₄`, and fixes every other dart. -/
def hollowSwap (c : H) : Equiv.Perm H :=
  swap c (X.inv c) * swap (X.rot c) ((X.rot ^ 4) c) * swap ((X.rot ^ 2) c) ((X.rot ^ 3) c)

/-- The involution `ι°` of `H° = H \ x` of the removal of a hollow monogon `{c}` at `x = v(c)`:
`ι°(d)` is the first dart outside `x` among `d̄, μ(d̄)̄, …`, that is, the first return of
`d ↦ μ(d)̄` to `H°`. It is extended by the identity on `x`. -/
@[cluster_algebras "def_hollow_removal"]
noncomputable def hollowInv (c : H) : Equiv.Perm H :=
  Equiv.Perm.ofSubtype (firstReturnPerm (X.inv * X.hollowSwap c) {d | d ∉ X.vertexOf c})

/-- The rotation system `(H, ι°, σ)` of the removal of a hollow monogon, before restriction. -/
noncomputable def hollowRotationSystem (c : H) : RotationSystem H := ⟨X.hollowInv c, X.rot⟩

/-- The darts of the removal of a hollow monogon `{c}`: those reachable from `B` under `σ` and
`ι°`. -/
noncomputable def hollowDarts (c : H) : Finset H := by
  classical exact univ.filter fun d => ∃ e ∈ X.bdry, (X.hollowRotationSystem c).Reach e d

/-- A dart lies in `hollowDarts c` iff it is reachable from a dart of `B` under `σ` and `ι°`. -/
theorem mem_hollowDarts {c d : H} :
    d ∈ X.hollowDarts c ↔ ∃ e ∈ X.bdry, (X.hollowRotationSystem c).Reach e d := by
  unfold hollowDarts
  simp

/-- `hollowDarts c` is closed under `σ` and `σ⁻¹`. -/
theorem rot_mem_hollowDarts_iff (c d : H) : X.rot d ∈ X.hollowDarts c ↔ d ∈ X.hollowDarts c := by
  simp only [mem_hollowDarts]
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, h.trans ?_⟩
    exact (RotationSystem.Reach.refl d).rot.symm
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, h.rot⟩

/-- `hollowDarts c` is closed under `ι°`. -/
theorem hollowInv_mem_hollowDarts_iff (c d : H) :
    X.hollowInv c d ∈ X.hollowDarts c ↔ d ∈ X.hollowDarts c := by
  simp only [mem_hollowDarts]
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, h.trans ?_⟩
    exact (RotationSystem.Reach.refl (R := X.hollowRotationSystem c) d).inv.symm
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, h.inv⟩

/-- Every dart of `B` is a dart of the removal. -/
theorem mem_hollowDarts_of_mem_bdry {c d : H} (hd : d ∈ X.bdry) : d ∈ X.hollowDarts c :=
  (X.mem_hollowDarts).2 ⟨d, hd, RotationSystem.Reach.refl d⟩

/-- A dart at a boundary vertex is a dart of the removal. -/
theorem mem_hollowDarts_of_isBoundaryVertex {c d : H}
    (hd : X.IsBoundaryVertex (X.vertexOf d)) : d ∈ X.hollowDarts c := by
  obtain ⟨e, he, heB⟩ := hd
  obtain ⟨n, hn⟩ := ((X.mem_vertexOf.1 he).symm).exists_nat_pow_eq
  refine (X.mem_hollowDarts).2 ⟨e, heB, ?_⟩
  rw [← hn]
  exact (X.hollowRotationSystem c).reach_pow_apply (g := X.rot)
    (fun y => (RotationSystem.Reach.refl y).rot) n e

/-- The removal of a hollow monogon `{c}` of `X` at the triple point `x = v(c)`: the triple data
`(H°, ι°, σ|_{H°}, B, ε, o|_{H°})` restricted to the darts reachable from `B` under `σ` and `ι°`
(`hollowDarts`), where `ι° = hollowInv`. -/
@[cluster_algebras "def_hollow_removal"]
noncomputable def hollowRemoval (hX : X.IsPreTripleDiagram) (c : H) :
    TripleData (X.hollowDarts c) b where
  inv := (X.hollowInv c).subtypePerm (X.hollowInv_mem_hollowDarts_iff c)
  rot := X.rot.subtypePerm (X.rot_mem_hollowDarts_iff c)
  bdry := X.bdry.subtype (· ∈ X.hollowDarts c)
  endDart r := ⟨X.endDart r, X.mem_hollowDarts_of_isBoundaryVertex
    (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2⟩
  isOut d := X.isOut d

end TripleData

end ClusterAlgebras

namespace ClusterAlgebras

open Finset Equiv

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

/-! ### The involution `ι°` -/

/-- `ι°` fixes the darts of `x = v(c)`. -/
theorem hollowInv_apply_of_mem {c d : H} (hd : d ∈ X.vertexOf c) : X.hollowInv c d = d :=
  Perm.ofSubtype_apply_of_not_mem _ (by simpa using hd)

/-- Off `x = v(c)`, `ι°(d)` is the first return of `d` to `H \ x` under `ι ∘ μ`. -/
theorem hollowInv_apply_of_notMem {c d : H} (hd : d ∉ X.vertexOf c) :
    X.hollowInv c d =
      firstReturn (X.inv * X.hollowSwap c) {d | d ∉ X.vertexOf c} ⟨d, hd⟩ := by
  unfold hollowInv
  exact Perm.ofSubtype_apply_of_mem
    (firstReturnPerm (X.inv * X.hollowSwap c) {d | d ∉ X.vertexOf c}) hd

/-- `ι°` maps `H \ x` into itself. -/
theorem hollowInv_notMem {c d : H} (hd : d ∉ X.vertexOf c) : X.hollowInv c d ∉ X.vertexOf c := by
  rw [hollowInv_apply_of_notMem hd]
  exact (firstReturn (X.inv * X.hollowSwap c) {d | d ∉ X.vertexOf c} ⟨d, hd⟩).2

/-- `ι°(d)` lies at `x = v(c)` iff `d` does. -/
theorem hollowInv_mem_iff {c d : H} : X.hollowInv c d ∈ X.vertexOf c ↔ d ∈ X.vertexOf c := by
  constructor
  · intro h
    by_contra hd
    exact hollowInv_notMem hd h
  · intro hd
    rwa [hollowInv_apply_of_mem hd]

section Hollow

variable (hX : X.IsPreTripleDiagram) {c : H} (hc : X.IsHollowMonogon {c})

include hX hc

private theorem hollow_ne : ∀ i j : ℕ, i < 6 → j < 6 → i ≠ j → (X.rot ^ i) c ≠ (X.rot ^ j) c := by
  obtain ⟨-, -, -, -, -, hinj⟩ := hollowMonogon_facts hX hc
  exact fun i j hi hj hij h => hij (hinj i j hi hj h)

/-- The darts of `x = v(c)` are exactly `σᵏ c` for `k < 6`. -/
theorem hollow_mem_vertexOf_iff {d : H} :
    d ∈ X.vertexOf c ↔ ∃ k < 6, (X.rot ^ k) c = d := by
  obtain ⟨-, -, hx, -, -, -⟩ := hollowMonogon_facts hX hc
  constructor
  · intro hd
    obtain ⟨n, hn⟩ := (X.mem_vertexOf.1 hd).exists_nat_pow_eq
    rw [hX.rot_pow_mod_six hx] at hn
    exact ⟨n % 6, Nat.mod_lt _ (by omega), hn⟩
  · rintro ⟨k, -, rfl⟩
    exact X.rot_pow_apply_mem_vertexOf _ _

/-- `μ` is the product of the transpositions `(σ⁰c σ⁵c)`, `(σ¹c σ⁴c)` and `(σ²c σ³c)`. -/
theorem hollowSwap_eq : X.hollowSwap c = swap ((X.rot ^ 0) c) ((X.rot ^ 5) c) *
    swap ((X.rot ^ 1) c) ((X.rot ^ 4) c) * swap ((X.rot ^ 2) c) ((X.rot ^ 3) c) := by
  obtain ⟨-, -, -, h5, -, -⟩ := hollowMonogon_facts hX hc
  unfold hollowSwap
  rw [h5]
  simp only [pow_zero, pow_one, Perm.one_apply]

/-- `hollowSwap c` reverses the six darts `(rot ^ k) c` of a hollow monogon. -/
theorem hollowSwap_rot_pow_apply :
    X.hollowSwap c ((X.rot ^ 0) c) = (X.rot ^ 5) c ∧
    X.hollowSwap c ((X.rot ^ 1) c) = (X.rot ^ 4) c ∧
    X.hollowSwap c ((X.rot ^ 2) c) = (X.rot ^ 3) c ∧
    X.hollowSwap c ((X.rot ^ 3) c) = (X.rot ^ 2) c ∧
    X.hollowSwap c ((X.rot ^ 4) c) = (X.rot ^ 1) c ∧
    X.hollowSwap c ((X.rot ^ 5) c) = (X.rot ^ 0) c := by
  have hne := hollow_ne hX hc
  have n01 : (X.rot ^ 0) c ≠ (X.rot ^ 1) c := hne 0 1 (by decide) (by decide) (by decide)
  have n02 : (X.rot ^ 0) c ≠ (X.rot ^ 2) c := hne 0 2 (by decide) (by decide) (by decide)
  have n03 : (X.rot ^ 0) c ≠ (X.rot ^ 3) c := hne 0 3 (by decide) (by decide) (by decide)
  have n04 : (X.rot ^ 0) c ≠ (X.rot ^ 4) c := hne 0 4 (by decide) (by decide) (by decide)
  have n05 : (X.rot ^ 0) c ≠ (X.rot ^ 5) c := hne 0 5 (by decide) (by decide) (by decide)
  have n10 : (X.rot ^ 1) c ≠ (X.rot ^ 0) c := hne 1 0 (by decide) (by decide) (by decide)
  have n12 : (X.rot ^ 1) c ≠ (X.rot ^ 2) c := hne 1 2 (by decide) (by decide) (by decide)
  have n13 : (X.rot ^ 1) c ≠ (X.rot ^ 3) c := hne 1 3 (by decide) (by decide) (by decide)
  have n14 : (X.rot ^ 1) c ≠ (X.rot ^ 4) c := hne 1 4 (by decide) (by decide) (by decide)
  have n15 : (X.rot ^ 1) c ≠ (X.rot ^ 5) c := hne 1 5 (by decide) (by decide) (by decide)
  have n20 : (X.rot ^ 2) c ≠ (X.rot ^ 0) c := hne 2 0 (by decide) (by decide) (by decide)
  have n21 : (X.rot ^ 2) c ≠ (X.rot ^ 1) c := hne 2 1 (by decide) (by decide) (by decide)
  have n23 : (X.rot ^ 2) c ≠ (X.rot ^ 3) c := hne 2 3 (by decide) (by decide) (by decide)
  have n24 : (X.rot ^ 2) c ≠ (X.rot ^ 4) c := hne 2 4 (by decide) (by decide) (by decide)
  have n25 : (X.rot ^ 2) c ≠ (X.rot ^ 5) c := hne 2 5 (by decide) (by decide) (by decide)
  have n30 : (X.rot ^ 3) c ≠ (X.rot ^ 0) c := hne 3 0 (by decide) (by decide) (by decide)
  have n31 : (X.rot ^ 3) c ≠ (X.rot ^ 1) c := hne 3 1 (by decide) (by decide) (by decide)
  have n32 : (X.rot ^ 3) c ≠ (X.rot ^ 2) c := hne 3 2 (by decide) (by decide) (by decide)
  have n34 : (X.rot ^ 3) c ≠ (X.rot ^ 4) c := hne 3 4 (by decide) (by decide) (by decide)
  have n35 : (X.rot ^ 3) c ≠ (X.rot ^ 5) c := hne 3 5 (by decide) (by decide) (by decide)
  have n40 : (X.rot ^ 4) c ≠ (X.rot ^ 0) c := hne 4 0 (by decide) (by decide) (by decide)
  have n41 : (X.rot ^ 4) c ≠ (X.rot ^ 1) c := hne 4 1 (by decide) (by decide) (by decide)
  have n42 : (X.rot ^ 4) c ≠ (X.rot ^ 2) c := hne 4 2 (by decide) (by decide) (by decide)
  have n43 : (X.rot ^ 4) c ≠ (X.rot ^ 3) c := hne 4 3 (by decide) (by decide) (by decide)
  have n45 : (X.rot ^ 4) c ≠ (X.rot ^ 5) c := hne 4 5 (by decide) (by decide) (by decide)
  have n50 : (X.rot ^ 5) c ≠ (X.rot ^ 0) c := hne 5 0 (by decide) (by decide) (by decide)
  have n51 : (X.rot ^ 5) c ≠ (X.rot ^ 1) c := hne 5 1 (by decide) (by decide) (by decide)
  have n52 : (X.rot ^ 5) c ≠ (X.rot ^ 2) c := hne 5 2 (by decide) (by decide) (by decide)
  have n53 : (X.rot ^ 5) c ≠ (X.rot ^ 3) c := hne 5 3 (by decide) (by decide) (by decide)
  have n54 : (X.rot ^ 5) c ≠ (X.rot ^ 4) c := hne 5 4 (by decide) (by decide) (by decide)
  rw [hollowSwap_eq hX hc]
  simp only [Perm.mul_apply, swap_apply_left, swap_apply_right]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [swap_apply_of_ne_of_ne, swap_apply_left, swap_apply_right, n01, n02, n03, n04, n10,
      n12, n13, n15, n20, n21, n24, n25, n30, n31, n34, n35, n40, n41, n42, n43, n45, n50, n51,
      n52, n53, n54, ne_eq,
      not_false_eq_true]

/-- `μ` fixes every dart not at `x = v(c)`. -/
theorem hollowSwap_apply_of_notMem {d : H} (hd : d ∉ X.vertexOf c) : X.hollowSwap c d = d := by
  have hm : ∀ k < 6, d ≠ (X.rot ^ k) c := fun k hk h =>
    hd ((hollow_mem_vertexOf_iff hX hc).2 ⟨k, hk, h.symm⟩)
  rw [hollowSwap_eq hX hc, Perm.mul_apply, Perm.mul_apply,
    swap_apply_of_ne_of_ne (hm 2 (by omega)) (hm 3 (by omega)),
    swap_apply_of_ne_of_ne (hm 1 (by omega)) (hm 4 (by omega)),
    swap_apply_of_ne_of_ne (hm 0 (by omega)) (hm 5 (by omega))]

/-- `μ` is an involution. -/
theorem hollowSwap_hollowSwap (d : H) : X.hollowSwap c (X.hollowSwap c d) = d := by
  by_cases hd : d ∈ X.vertexOf c
  · obtain ⟨k, hk, rfl⟩ := (hollow_mem_vertexOf_iff hX hc).1 hd
    obtain ⟨v0, v1, v2, v3, v4, v5⟩ := hollowSwap_rot_pow_apply hX hc
    interval_cases k <;> simp only [v0, v1, v2, v3, v4, v5]
  · rw [hollowSwap_apply_of_notMem hX hc hd, hollowSwap_apply_of_notMem hX hc hd]

/-- `μ(d)` lies at `x = v(c)` iff `d` does. -/
theorem hollowSwap_mem_iff {d : H} : X.hollowSwap c d ∈ X.vertexOf c ↔ d ∈ X.vertexOf c := by
  constructor
  · intro h
    by_contra hd
    exact hd (by rwa [hollowSwap_apply_of_notMem hX hc hd] at h)
  · intro hd
    obtain ⟨k, hk, rfl⟩ := (hollow_mem_vertexOf_iff hX hc).1 hd
    obtain ⟨v0, v1, v2, v3, v4, v5⟩ := hollowSwap_rot_pow_apply hX hc
    interval_cases k <;> simp only [v0, v1, v2, v3, v4, v5] <;>
      exact X.rot_pow_apply_mem_vertexOf _ _

/-- On the darts of `x = v(c)`, `μ` reverses the orientation `o`. -/
theorem isOut_hollowSwap {d : H} (hd : d ∈ X.vertexOf c) :
    X.isOut (X.hollowSwap c d) = !X.isOut d := by
  obtain ⟨-, -, hx, -, -, -⟩ := hollowMonogon_facts hX hc
  obtain ⟨k, hk, rfl⟩ := (hollow_mem_vertexOf_iff hX hc).1 hd
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := hollowSwap_rot_pow_apply hX hc
  have ho := hX.isOut_rot_pow_apply hx
  interval_cases k
  · rw [v0, ho, ho]; simp [show ¬Even 5 by decide]
  · rw [v1, ho, ho]; simp [show ¬Even 1 by decide, show Even 4 by decide]
  · rw [v2, ho, ho]; simp [show ¬Even 3 by decide, show Even 2 by decide]
  · rw [v3, ho, ho]; simp [show ¬Even 3 by decide, show Even 2 by decide]
  · rw [v4, ho, ho]; simp [show ¬Even 1 by decide, show Even 4 by decide]
  · rw [v5, ho, ho]; simp [show ¬Even 5 by decide]

/-- No dart of `B` lies at `x`. -/
theorem notMem_vertexOf_of_mem_bdry {d : H} (hd : d ∈ X.bdry) : d ∉ X.vertexOf c := by
  obtain ⟨-, -, hx, -, -, -⟩ := hollowMonogon_facts hX hc
  intro h
  exact hx ⟨d, h, hd⟩

/-- `ι°(d) = d̄` when `d̄ ∉ x`. -/
theorem hollowInv_apply_of_inv_notMem {d : H} (hd : d ∉ X.vertexOf c)
    (hd' : X.inv d ∉ X.vertexOf c) : X.hollowInv c d = X.inv d := by
  rw [hollowInv_apply_of_notMem hd, coe_firstReturn_of_apply_mem]
  · simp only [Perm.mul_apply, hollowSwap_apply_of_notMem hX hc hd]
  · simpa only [Set.mem_setOf_eq, Perm.mul_apply, hollowSwap_apply_of_notMem hX hc hd] using hd'

/-- `ι°(d) = (μ(d̄))̄` when `d̄ ∈ x` and `(μ(d̄))̄ ∉ x`. -/
theorem hollowInv_apply_two {d : H} (hd : d ∉ X.vertexOf c) (h1 : X.inv d ∈ X.vertexOf c)
    (h2 : X.inv (X.hollowSwap c (X.inv d)) ∉ X.vertexOf c) :
    X.hollowInv c d = X.inv (X.hollowSwap c (X.inv d)) := by
  have hg1 : (X.inv * X.hollowSwap c) d = X.inv d := by
    rw [Perm.mul_apply, hollowSwap_apply_of_notMem hX hc hd]
  have hp2 : ((X.inv * X.hollowSwap c) ^ 2) d = X.inv (X.hollowSwap c (X.inv d)) := by
    rw [sq, Perm.mul_apply, hg1, Perm.mul_apply]
  rw [hollowInv_apply_of_notMem hd, coe_firstReturn_of_pow (m := 2) (by omega)]
  · exact hp2
  · rw [Set.mem_setOf_eq, hp2]
    exact h2
  · intro j hj hj2
    obtain rfl : j = 1 := by omega
    rw [pow_one, hg1, Set.mem_setOf_eq, not_not]
    exact h1

/-- `ι°(d) = ((μ((μ(d̄))̄))̄` when `d̄, (μ(d̄))̄ ∈ x` and the last dart is not in `x`. -/
theorem hollowInv_apply_three {d : H} (hd : d ∉ X.vertexOf c) (h1 : X.inv d ∈ X.vertexOf c)
    (h2 : X.inv (X.hollowSwap c (X.inv d)) ∈ X.vertexOf c)
    (h3 : X.inv (X.hollowSwap c (X.inv (X.hollowSwap c (X.inv d)))) ∉ X.vertexOf c) :
    X.hollowInv c d = X.inv (X.hollowSwap c (X.inv (X.hollowSwap c (X.inv d)))) := by
  have hg1 : (X.inv * X.hollowSwap c) d = X.inv d := by
    rw [Perm.mul_apply, hollowSwap_apply_of_notMem hX hc hd]
  have hp2 : ((X.inv * X.hollowSwap c) ^ 2) d = X.inv (X.hollowSwap c (X.inv d)) := by
    rw [sq, Perm.mul_apply, hg1, Perm.mul_apply]
  have hp3 : ((X.inv * X.hollowSwap c) ^ 3) d =
      X.inv (X.hollowSwap c (X.inv (X.hollowSwap c (X.inv d)))) := by
    rw [pow_succ', Perm.mul_apply, hp2, Perm.mul_apply]
  rw [hollowInv_apply_of_notMem hd, coe_firstReturn_of_pow (m := 3) (by omega)]
  · exact hp3
  · rw [Set.mem_setOf_eq, hp3]
    exact h3
  · intro j hj hj3
    rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
    · rw [pow_one, hg1, Set.mem_setOf_eq, not_not]
      exact h1
    · rw [hp2, Set.mem_setOf_eq, not_not]
      exact h2

/-- `ι°` is an involution. -/
theorem hollowInv_involutive : Function.Involutive (X.hollowInv c) := by
  intro d
  by_cases hd : d ∈ X.vertexOf c
  · rw [hollowInv_apply_of_mem hd, hollowInv_apply_of_mem hd]
  set g := X.inv * X.hollowSwap c with hg
  set Y : Set H := {d | d ∉ X.vertexOf c} with hY
  have hμμ : X.hollowSwap c * X.hollowSwap c = 1 := by
    ext e
    simp [hollowSwap_hollowSwap hX hc]
  have hconj : g⁻¹ = X.hollowSwap c * g * (X.hollowSwap c)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hμμ]
    refine inv_eq_of_mul_eq_one_right ?_
    ext e
    simp only [hg, Perm.mul_apply, Perm.one_apply, hollowSwap_hollowSwap hX hc,
      hX.inv_inv_apply]
  have hκ : ∀ y, X.hollowSwap c y ∈ Y ↔ y ∈ Y := fun y => by
    simp only [hY, Set.mem_setOf_eq, hollowSwap_mem_iff hX hc]
  have hfix : ∀ y ∈ Y, X.hollowSwap c y = y := fun y hy => hollowSwap_apply_of_notMem hX hc hy
  have h1 := hollowInv_apply_of_notMem (c := c) hd
  set y := firstReturn g Y ⟨d, hd⟩ with hy
  rw [h1, hollowInv_apply_of_notMem y.2]
  have := firstReturn_inv_firstReturn g Y ⟨d, hd⟩
  rw [hconj, firstReturn_conj hκ hfix] at this
  rw [← hy] at this
  exact congrArg Subtype.val this

/-- Along the sequence defining `ι°`, orientations are reversed once: `o(ι° d) ≠ o(d)` for
`d ∉ x ∪ B`. -/
theorem isOut_hollowInv {d : H} (hd : d ∉ X.vertexOf c) (hdB : d ∉ X.bdry) :
    X.isOut (X.hollowInv c d) = !X.isOut d := by
  obtain ⟨-, -, hx, -, -, -⟩ := hollowMonogon_facts hX hc
  set g := X.inv * X.hollowSwap c with hg
  set Y : Set H := {d | d ∉ X.vertexOf c} with hY
  set m := firstReturnTime g Y ⟨d, hd⟩
  have key : ∀ j, 1 ≤ j → j ≤ m → (g ^ j) d ∉ X.bdry ∧ X.isOut ((g ^ j) d) = !X.isOut d := by
    intro j hj hjm
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [zero_add, pow_one, hg, Perm.mul_apply, hollowSwap_apply_of_notMem hX hc hd]
        exact ⟨hX.inv_notMem_bdry hdB, hX.isOut_inv_apply hdB⟩
      · obtain ⟨ih1, ih2⟩ := ih hj0 (by omega)
        have hmem : (g ^ j) d ∈ X.vertexOf c := by
          have := pow_apply_notMem_of_lt_firstReturnTime (π := g) (Y := Y) (y := ⟨d, hd⟩) hj0
            (by omega)
          simpa [hY] using this
        have hμ : X.hollowSwap c ((g ^ j) d) ∈ X.vertexOf c := (hollowSwap_mem_iff hX hc).2 hmem
        have hμB : X.hollowSwap c ((g ^ j) d) ∉ X.bdry := fun h =>
          hx ⟨_, hμ, h⟩
        rw [pow_succ', Perm.mul_apply, hg, Perm.mul_apply]
        refine ⟨hX.inv_notMem_bdry hμB, ?_⟩
        rw [hX.isOut_inv_apply hμB, isOut_hollowSwap hX hc hmem, Bool.not_not, ih2]
  have hm : 1 ≤ m := firstReturnTime_pos _
  rw [hollowInv_apply_of_notMem hd, coe_firstReturn]
  exact (key m hm le_rfl).2

/-- `ι°` has no fixed point outside `x`. -/
theorem hollowInv_ne {d : H} (hd : d ∉ X.vertexOf c) : X.hollowInv c d ≠ d := by
  by_cases hdB : d ∈ X.bdry
  · have hd' : X.inv d ∉ X.vertexOf c :=
      notMem_vertexOf_of_mem_bdry hX hc (hX.inv_mem_bdry d hdB)
    rw [hollowInv_apply_of_inv_notMem hX hc hd hd']
    exact hX.inv_ne d
  · intro h
    have := isOut_hollowInv hX hc hd hdB
    rw [h] at this
    cases hb : X.isOut d <;> simp [hb] at this

/-- On `B`, `ι°` is `d ↦ d̄`. -/
theorem hollowInv_apply_of_mem_bdry {d : H} (hd : d ∈ X.bdry) : X.hollowInv c d = X.inv d :=
  hollowInv_apply_of_inv_notMem hX hc (notMem_vertexOf_of_mem_bdry hX hc hd)
    (notMem_vertexOf_of_mem_bdry hX hc (hX.inv_mem_bdry d hd))

/-- The darts of the removal avoid `x`. -/
theorem notMem_vertexOf_of_mem_hollowDarts {d : H} (hd : d ∈ X.hollowDarts c) :
    d ∉ X.vertexOf c := by
  obtain ⟨e, he, h⟩ := (X.mem_hollowDarts).1 hd
  clear hd
  induction h with
  | refl => exact notMem_vertexOf_of_mem_bdry hX hc he
  | @rot y _ ih =>
    intro hy
    apply ih
    rw [X.mem_vertexOf_iff_vertexOf_eq] at hy ⊢
    change X.vertexOf (X.rot y) = _ at hy
    rwa [X.vertexOf_rot] at hy
  | inv _ ih => exact hollowInv_notMem ih

end Hollow

end TripleData

end ClusterAlgebras

namespace ClusterAlgebras

open Finset Equiv

/-- Two permutations agreeing on a set closed under the first have the same orbits through its
points. -/
private theorem sameCycle_iff_of_eqOn' {α : Type*} [Finite α] {f g : Perm α} {S : Set α}
    (hS : ∀ z ∈ S, f z ∈ S) (hfg : ∀ z ∈ S, f z = g z) {x : α} (hx : x ∈ S) {y : α} :
    f.SameCycle x y ↔ g.SameCycle x y := by
  have key : ∀ n : ℕ, (f ^ n) x = (g ^ n) x ∧ (f ^ n) x ∈ S := by
    intro n
    induction n with
    | zero => exact ⟨rfl, hx⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply]
      exact ⟨by rw [hfg _ h2, h1], hS _ h2⟩
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← (key n).1, hn]⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, (key n).1, hn]⟩

namespace RotationSystem

variable {H : Type*} (R : RotationSystem H)

/-- The restriction of a rotation system to a set of darts closed under `σ` and `d ↦ d̄`. -/
private def restrict (p : H → Prop) (hinv : ∀ d, p (R.inv d) ↔ p d) (hrot : ∀ d,
    p (R.rot d) ↔ p d) :
    RotationSystem (Subtype p) :=
  ⟨R.inv.subtypePerm hinv, R.rot.subtypePerm hrot⟩

/-- Reachability in a closed set of darts is reachability in the restriction. -/
private theorem Reach.restrict {R : RotationSystem H} {p : H → Prop}
    {R' : RotationSystem (Subtype p)}
    (hinv : ∀ x : Subtype p, (R'.inv x : H) = R.inv x)
    (hrot : ∀ x : Subtype p, (R'.rot x : H) = R.rot x) {d e : H} (h : R.Reach d e)
    (hd : p d) : ∃ he : p e, R'.Reach ⟨d, hd⟩ ⟨e, he⟩ := by
  induction h with
  | refl => exact ⟨hd, Reach.refl _⟩
  | @rot y _ ih =>
    obtain ⟨hy, h'⟩ := ih
    have : (⟨R.rot y, by rw [← hrot ⟨y, hy⟩]; exact (R'.rot ⟨y, hy⟩).2⟩ : Subtype p) =
        R'.rot ⟨y, hy⟩ := Subtype.ext (hrot ⟨y, hy⟩).symm
    exact ⟨_, this ▸ h'.rot⟩
  | @inv y _ ih =>
    obtain ⟨hy, h'⟩ := ih
    have : (⟨R.inv y, by rw [← hinv ⟨y, hy⟩]; exact (R'.inv ⟨y, hy⟩).2⟩ : Subtype p) =
        R'.inv ⟨y, hy⟩ := Subtype.ext (hinv ⟨y, hy⟩).symm
    exact ⟨_, this ▸ h'.inv⟩

end RotationSystem

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

/-! ### The removal of a hollow monogon -/

section Removal

variable (hX : X.IsPreTripleDiagram) (c : H)

/-- The involution of the removal is `ι°`. -/
@[simp]
theorem coe_hollowRemoval_inv (d : X.hollowDarts c) :
    ((X.hollowRemoval hX c).inv d : H) = X.hollowInv c d := rfl

/-- The rotation of the removal is `σ`. -/
@[simp]
theorem coe_hollowRemoval_rot (d : X.hollowDarts c) :
    ((X.hollowRemoval hX c).rot d : H) = X.rot d := rfl

/-- The boundary darts of the removal are those of `B`. -/
@[simp]
theorem mem_hollowRemoval_bdry {d : X.hollowDarts c} :
    d ∈ (X.hollowRemoval hX c).bdry ↔ (d : H) ∈ X.bdry := mem_subtype

/-- The orientation of the removal is that of `X`. -/
@[simp]
theorem hollowRemoval_isOut (d : X.hollowDarts c) :
    (X.hollowRemoval hX c).isOut d = X.isOut d := rfl

/-- The end darts of the removal are those of `X`. -/
@[simp]
theorem coe_hollowRemoval_endDart (r : Fin (2 * b)) :
    ((X.hollowRemoval hX c).endDart r : H) = X.endDart r := rfl

/-- Powers of the rotation of the removal are powers of `σ`. -/
@[simp]
theorem coe_hollowRemoval_rot_pow (n : ℕ) (d : X.hollowDarts c) :
    (((X.hollowRemoval hX c).rot ^ n) d : H) = (X.rot ^ n) d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, coe_hollowRemoval_rot, ih, pow_succ',
      Perm.mul_apply]

/-- The rotation of the removal is the restriction of `σ` to `hollowDarts c`. -/
theorem hollowRemoval_rot_eq :
    (X.hollowRemoval hX c).rot = X.rot.subtypePerm (X.rot_mem_hollowDarts_iff c) := rfl

/-- The face permutation of the removal is the restriction of `σ ∘ ι°` to `hollowDarts c`. -/
theorem hollowRemoval_facePerm_eq :
    (X.hollowRemoval hX c).facePerm = (X.rot * X.hollowInv c).subtypePerm (fun d => by
      rw [Perm.mul_apply, X.rot_mem_hollowDarts_iff, X.hollowInv_mem_hollowDarts_iff]) := by
  ext d
  rfl

/-- The vertices of the removal are those of `X`. -/
theorem map_hollowRemoval_vertexOf (d : X.hollowDarts c) :
    ((X.hollowRemoval hX c).vertexOf d).map (Function.Embedding.subtype _) = X.vertexOf d := by
  ext e
  simp only [mem_map, RotationSystem.vertexOf, mem_filter, mem_univ, true_and,
    Function.Embedding.coe_subtype, hollowRemoval_rot_eq, Perm.sameCycle_subtypePerm]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro he
    exact ⟨⟨e, sameCycle_closed (p := (· ∈ X.hollowDarts c)) (X.rot_mem_hollowDarts_iff c)
      d.2 he⟩, he, rfl⟩

/-- A vertex of the removal is a boundary vertex iff it is one of `X`. -/
theorem isBoundaryVertex_hollowRemoval_iff (d : X.hollowDarts c) :
    (X.hollowRemoval hX c).IsBoundaryVertex ((X.hollowRemoval hX c).vertexOf d) ↔
      X.IsBoundaryVertex (X.vertexOf d) := by
  rw [← map_hollowRemoval_vertexOf hX c d]
  constructor
  · rintro ⟨e, he, heB⟩
    exact ⟨e, mem_map_of_mem _ he, (mem_hollowRemoval_bdry hX c).1 heB⟩
  · rintro ⟨e, he, heB⟩
    obtain ⟨e', he', rfl⟩ := mem_map.1 he
    exact ⟨e', he', (mem_hollowRemoval_bdry hX c).2 heB⟩

/-- A vertex of the removal has as many darts as the corresponding vertex of `X`. -/
theorem card_hollowRemoval_vertexOf (d : X.hollowDarts c) :
    ((X.hollowRemoval hX c).vertexOf d).card = (X.vertexOf d).card := by
  rw [← map_hollowRemoval_vertexOf hX c d, card_map]

/-- A vertex of the removal has as many boundary darts as the corresponding vertex of `X`. -/
theorem card_filter_hollowRemoval_vertexOf (d : X.hollowDarts c) :
    (((X.hollowRemoval hX c).vertexOf d).filter (· ∈ (X.hollowRemoval hX c).bdry)).card =
      ((X.vertexOf d).filter (· ∈ X.bdry)).card := by
  rw [← map_hollowRemoval_vertexOf hX c d, filter_map, card_map]
  congr 1
  apply filter_congr
  intro e _
  simp

/-- The endpoints of the removal are those of `X`. -/
theorem map_hollowRemoval_endpoint (r : Fin (2 * b)) :
    ((X.hollowRemoval hX c).endpoint r).map (Function.Embedding.subtype _) = X.endpoint r :=
  map_hollowRemoval_vertexOf hX c _

end Removal

section RemovalHollow

variable (hX : X.IsPreTripleDiagram) {c : H} (hc : X.IsHollowMonogon {c})

include hX hc

/-- The exterior orbit of `X` survives in the removal. -/
theorem hollowRemoval_exists_orbit :
    ∃ f ∈ (X.hollowRemoval hX c).faceOrbits, f ⊆ (X.hollowRemoval hX c).bdry ∧
      f ∪ f.map (X.hollowRemoval hX c).inv.toEmbedding = (X.hollowRemoval hX c).bdry ∧
      Disjoint f (f.map (X.hollowRemoval hX c).inv.toEmbedding) := by
  obtain ⟨f, hf, hfB, hfU, hfD⟩ := hX.exists_orbit
  obtain ⟨e₀, rfl⟩ := X.mem_faceOrbits.1 hf
  have he₀ : e₀ ∈ X.hollowDarts c :=
    X.mem_hollowDarts_of_mem_bdry (hfB (X.self_mem_faceOf e₀))
  -- on the exterior orbit, `σ ι° = φ`
  have hclosed : ∀ z ∈ (X.faceOf e₀ : Set H), X.facePerm z ∈ (X.faceOf e₀ : Set H) := by
    intro z hz
    simp only [Finset.mem_coe] at hz ⊢
    rw [← X.faceOf_eq_of_mem hz]
    exact X.facePerm_mem_faceOf z
  have heq : ∀ z ∈ (X.faceOf e₀ : Set H), X.facePerm z = (X.rot * X.hollowInv c) z := by
    intro z hz
    rw [Perm.mul_apply, hollowInv_apply_of_mem_bdry hX hc (hfB hz)]
    rfl
  have hiff : ∀ y : H, (X.rot * X.hollowInv c).SameCycle e₀ y ↔ y ∈ X.faceOf e₀ := by
    intro y
    rw [← sameCycle_iff_of_eqOn' hclosed heq (X.self_mem_faceOf e₀), X.mem_faceOf]
  have hmem : ∀ y : X.hollowDarts c,
      y ∈ (X.hollowRemoval hX c).faceOf ⟨e₀, he₀⟩ ↔ (y : H) ∈ X.faceOf e₀ := by
    intro y
    rw [RotationSystem.mem_faceOf, hollowRemoval_facePerm_eq, Perm.sameCycle_subtypePerm]
    exact hiff y
  have hmemB : ∀ y : X.hollowDarts c, y ∈ (X.hollowRemoval hX c).bdry ↔ (y : H) ∈ X.bdry :=
    fun y => mem_hollowRemoval_bdry hX c
  have hmemI : ∀ y : X.hollowDarts c,
      y ∈ ((X.hollowRemoval hX c).faceOf ⟨e₀, he₀⟩).map (X.hollowRemoval hX c).inv.toEmbedding ↔
        (y : H) ∈ (X.faceOf e₀).map X.inv.toEmbedding := by
    intro y
    simp only [mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z, (hmem z).1 hz, ?_⟩
      rw [coe_hollowRemoval_inv, hollowInv_apply_of_mem_bdry hX hc (hfB ((hmem z).1 hz))]
    · rintro ⟨z, hz, hzy⟩
      have hzO : z ∈ X.hollowDarts c := X.mem_hollowDarts_of_mem_bdry (hfB hz)
      refine ⟨⟨z, hzO⟩, (hmem _).2 hz, Subtype.ext ?_⟩
      rw [coe_hollowRemoval_inv, hollowInv_apply_of_mem_bdry hX hc (hfB hz)]
      exact hzy
  refine ⟨_, (X.hollowRemoval hX c).faceOf_mem_faceOrbits ⟨e₀, he₀⟩, fun y hy => ?_, ?_, ?_⟩
  · exact (hmemB y).2 (hfB ((hmem y).1 hy))
  · ext y
    rw [mem_union, hmem, hmemI, hmemB, ← hfU, mem_union]
  · rw [disjoint_left]
    intro y hy hy'
    exact disjoint_left.1 hfD ((hmem y).1 hy) ((hmemI y).1 hy')

/-- In the removal, every dart of `B` is reachable from every other. -/
theorem hollow_reach_bdry {e e' : H} (he : e ∈ X.bdry) (he' : e' ∈ X.bdry) :
    (X.hollowRotationSystem c).Reach e e' := by
  obtain ⟨f, hf, hfB, hfU, -⟩ := hX.exists_orbit
  obtain ⟨e₀, rfl⟩ := X.mem_faceOrbits.1 hf
  have hclosed : ∀ z ∈ (X.faceOf e₀ : Set H), X.facePerm z ∈ (X.faceOf e₀ : Set H) := by
    intro z hz
    simp only [Finset.mem_coe] at hz ⊢
    rw [← X.faceOf_eq_of_mem hz]
    exact X.facePerm_mem_faceOf z
  have heq : ∀ z ∈ (X.faceOf e₀ : Set H), X.facePerm z = (X.rot * X.hollowInv c) z := by
    intro z hz
    rw [Perm.mul_apply, hollowInv_apply_of_mem_bdry hX hc (hfB hz)]
    rfl
  have hstep : ∀ y, (X.hollowRotationSystem c).Reach y ((X.rot * X.hollowInv c) y) :=
    fun y => (RotationSystem.Reach.refl y).inv.rot
  have hfrom : ∀ y ∈ X.bdry, (X.hollowRotationSystem c).Reach e₀ y := by
    intro y hy
    rw [← hfU, mem_union] at hy
    rcases hy with hy | hy
    · have := (sameCycle_iff_of_eqOn' hclosed heq (X.self_mem_faceOf e₀)).1 (X.mem_faceOf.1 hy)
      obtain ⟨n, rfl⟩ := this.exists_nat_pow_eq
      exact RotationSystem.reach_pow_apply _ hstep n e₀
    · obtain ⟨z, hz, rfl⟩ := mem_map.1 hy
      have := (sameCycle_iff_of_eqOn' hclosed heq (X.self_mem_faceOf e₀)).1 (X.mem_faceOf.1 hz)
      obtain ⟨n, hn⟩ := this.exists_nat_pow_eq
      have h1 := RotationSystem.reach_pow_apply _ hstep n e₀
      rw [hn] at h1
      have h2 := h1.inv
      change (X.hollowRotationSystem c).Reach e₀ (X.hollowInv c z) at h2
      rwa [hollowInv_apply_of_mem_bdry hX hc (hfB hz)] at h2
  exact (hfrom e he).symm.trans (hfrom e' he')

/-- The removal is a pre-triple diagram. -/
theorem isPreTripleDiagram_hollowRemoval : (X.hollowRemoval hX c).IsPreTripleDiagram where
  one_le := hX.one_le
  nonempty := ⟨(X.hollowRemoval hX c).endDart ⟨0, by have := hX.one_le; omega⟩⟩
  inv_involutive d := Subtype.ext (hollowInv_involutive hX hc d)
  inv_ne d h := hollowInv_ne hX hc (notMem_vertexOf_of_mem_hollowDarts hX hc d.2)
    (congrArg Subtype.val h)
  inv_mem_bdry d hd := by
    rw [mem_hollowRemoval_bdry] at hd ⊢
    rw [coe_hollowRemoval_inv, hollowInv_apply_of_mem_bdry hX hc hd]
    exact hX.inv_mem_bdry _ hd
  boundaryVertex_card v hv := by
    obtain ⟨hvV, hvB⟩ := (X.hollowRemoval hX c).mem_boundaryVertices.1 hv
    obtain ⟨d, rfl⟩ := (X.hollowRemoval hX c).mem_vertices.1 hvV
    rw [isBoundaryVertex_hollowRemoval_iff] at hvB
    rw [card_hollowRemoval_vertexOf, card_filter_hollowRemoval_vertexOf]
    exact hX.boundaryVertex_card _ (X.vertexOf_mem_boundaryVertices.2 hvB)
  exists_orbit := hollowRemoval_exists_orbit hX hc
  internalVertex_card v hv := by
    obtain ⟨hvV, hvB⟩ := (X.hollowRemoval hX c).mem_internalVertices.1 hv
    obtain ⟨d, rfl⟩ := (X.hollowRemoval hX c).mem_vertices.1 hvV
    rw [isBoundaryVertex_hollowRemoval_iff] at hvB
    rw [card_hollowRemoval_vertexOf]
    exact hX.internalVertex_card _ (X.vertexOf_mem_internalVertices.2 hvB)
  endDart_notMem_bdry r := by
    rw [mem_hollowRemoval_bdry]
    exact hX.endDart_notMem_bdry r
  endpoint_mem r := by
    refine (X.hollowRemoval hX c).vertexOf_mem_boundaryVertices.2 ?_
    rw [isBoundaryVertex_hollowRemoval_iff]
    exact X.vertexOf_mem_boundaryVertices.1 (hX.endpoint_mem r)
  endpoint_injective r r' h := by
    apply hX.endpoint_injective
    rw [← map_hollowRemoval_endpoint hX c, ← map_hollowRemoval_endpoint hX c, h]
  exists_endpoint_eq v hv := by
    obtain ⟨hvV, hvB⟩ := (X.hollowRemoval hX c).mem_boundaryVertices.1 hv
    obtain ⟨d, rfl⟩ := (X.hollowRemoval hX c).mem_vertices.1 hvV
    rw [isBoundaryVertex_hollowRemoval_iff] at hvB
    obtain ⟨r, hr⟩ := hX.exists_endpoint_eq _ (X.vertexOf_mem_boundaryVertices.2 hvB)
    refine ⟨r, Finset.map_injective (Function.Embedding.subtype _) ?_⟩
    rw [map_hollowRemoval_endpoint, map_hollowRemoval_vertexOf, hr]
  exists_exterior r := by
    obtain ⟨e, he, he1, he2⟩ := hX.exists_exterior r
    have heB := X.exterior_subset_bdry he
    have heO : e ∈ X.hollowDarts c := X.mem_hollowDarts_of_mem_bdry heB
    refine ⟨⟨e, heO⟩, ?_, ?_, ?_⟩
    · rw [DiskMap.mem_exterior, mem_hollowRemoval_bdry, mem_hollowRemoval_bdry,
        coe_hollowRemoval_rot]
      exact X.mem_exterior.1 he
    · rw [← mem_map' (Function.Embedding.subtype _), map_hollowRemoval_endpoint]
      exact he1
    · rw [← mem_map' (Function.Embedding.subtype _), map_hollowRemoval_endpoint,
        Function.Embedding.coe_subtype, coe_hollowRemoval_inv,
        hollowInv_apply_of_mem_bdry hX hc heB]
      exact he2
  isOut_inv d hd := by
    rw [mem_hollowRemoval_bdry] at hd
    rw [hollowRemoval_isOut, hollowRemoval_isOut, coe_hollowRemoval_inv,
      isOut_hollowInv hX hc (notMem_vertexOf_of_mem_hollowDarts hX hc d.2) hd]
    cases X.isOut d <;> simp
  isOut_rot d hd := by
    rw [isBoundaryVertex_hollowRemoval_iff] at hd
    rw [hollowRemoval_isOut, hollowRemoval_isOut, coe_hollowRemoval_rot]
    exact hX.isOut_rot d hd
  isOut_source i := hX.isOut_source i
  isOut_target i := hX.isOut_target i

/-- The removal is a connected rotation system. -/
theorem isConnected_hollowRemoval :
    (X.hollowRemoval hX c).toRotationSystem.IsConnected := by
  have hP := isPreTripleDiagram_hollowRemoval hX hc
  refine RotationSystem.IsConnected.of_reach hP.nonempty hP.inv_involutive hP.inv_ne ?_
  intro d e
  obtain ⟨b₁, hb₁, h₁⟩ := (X.mem_hollowDarts).1 d.2
  obtain ⟨b₂, hb₂, h₂⟩ := (X.mem_hollowDarts).1 e.2
  have h : (X.hollowRotationSystem c).Reach d e :=
    h₁.symm.trans ((hollow_reach_bdry hX hc hb₁ hb₂).trans h₂)
  obtain ⟨he, h'⟩ := RotationSystem.Reach.restrict (R := X.hollowRotationSystem c)
    (R' := (X.hollowRemoval hX c).toRotationSystem) (fun x => rfl) (fun x => rfl) h d.2
  exact h'

end RemovalHollow

end TripleData

end ClusterAlgebras

namespace ClusterAlgebras

open Finset Equiv

section FirstReturnCount

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Images under two maps with the same fibres have the same cardinality. -/
private theorem card_image_eq_of_iff {ι β γ : Type*} [DecidableEq β] [DecidableEq γ] {s : Finset ι}
    {f : ι → β} {g : ι → γ} (h : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ g a = g b) :
    (s.image f).card = (s.image g).card := by
  have h1 : (s.image fun a => (f a, g a)).image Prod.fst = s.image f := by
    rw [image_image]; rfl
  have h2 : (s.image fun a => (f a, g a)).image Prod.snd = s.image g := by
    rw [image_image]; rfl
  have i1 : Set.InjOn Prod.fst (↑(s.image fun a => (f a, g a)) : Set (β × γ)) := by
    intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := mem_image.1 (mem_coe.1 hp)
    obtain ⟨a', ha', rfl⟩ := mem_image.1 (mem_coe.1 hq)
    exact Prod.ext hpq ((h a ha a' ha').1 hpq)
  have i2 : Set.InjOn Prod.snd (↑(s.image fun a => (f a, g a)) : Set (β × γ)) := by
    intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := mem_image.1 (mem_coe.1 hp)
    obtain ⟨a', ha', rfl⟩ := mem_image.1 (mem_coe.1 hq)
    exact Prod.ext ((h a ha a' ha').2 hpq) hpq
  rw [← h1, ← h2, card_image_of_injOn i1, card_image_of_injOn i2]

private theorem orbit_eq_iff {π : Perm α} {a b : α} :
    ({e | π.SameCycle a e} : Finset α) = ({e | π.SameCycle b e} : Finset α) ↔
      π.SameCycle a b := by
  constructor
  · intro h
    have : b ∈ ({e | π.SameCycle b e} : Finset α) := by simp [Perm.SameCycle.refl]
    rw [← h] at this
    simpa using this
  · intro h
    ext e
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨h.symm.trans, h.trans⟩

/-- The first-return map to `Y` has one orbit for each orbit of `π` meeting `Y`. -/
private theorem numOrbits_firstReturnPerm_eq (π : Perm α) (Y : Set α) [DecidablePred (· ∈ Y)] :
    numOrbits (firstReturnPerm π Y) = (orbitsOn π (univ.filter (· ∈ Y))).card := by
  rw [numOrbits_eq_card_image,
    card_image_eq_of_iff (g := fun y : Y => ({e | π.SameCycle (y : α) e} : Finset α))]
  · congr 1
    ext o
    simp only [mem_image, mem_univ, true_and, orbitsOn, mem_filter]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
  · intro a _ a' _
    rw [orbit_eq_iff, orbit_eq_iff, sameCycle_firstReturnPerm_iff]

end FirstReturnCount

section FirstReturnSteps

variable {α : Type*} [Finite α] {π : Perm α} {Y : Set α} {y : Y}

private theorem coe_firstReturn_two (h1 : π y ∉ Y) (h2 : π (π y) ∈ Y) :
    (firstReturn π Y y : α) = π (π y) := by
  have e2 : (π ^ 2) y = π (π y) := by rw [sq, Perm.mul_apply]
  rw [coe_firstReturn_of_pow (m := 2) (by omega) (by rw [e2]; exact h2), e2]
  intro j hj hj2
  obtain rfl : j = 1 := by omega
  rwa [pow_one]

private theorem coe_firstReturn_three (h1 : π y ∉ Y) (h2 : π (π y) ∉ Y) (h3 : π (π (π y)) ∈ Y) :
    (firstReturn π Y y : α) = π (π (π y)) := by
  have e2 : (π ^ 2) y = π (π y) := by rw [sq, Perm.mul_apply]
  have e3 : (π ^ 3) y = π (π (π y)) := by rw [pow_succ', Perm.mul_apply, e2]
  rw [coe_firstReturn_of_pow (m := 3) (by omega) (by rw [e3]; exact h3), e3]
  intro j hj hj3
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · rwa [pow_one]
  · rwa [e2]

private theorem coe_firstReturn_four (h1 : π y ∉ Y) (h2 : π (π y) ∉ Y) (h3 : π (π (π y)) ∉ Y)
    (h4 : π (π (π (π y))) ∈ Y) : (firstReturn π Y y : α) = π (π (π (π y))) := by
  have e2 : (π ^ 2) y = π (π y) := by rw [sq, Perm.mul_apply]
  have e3 : (π ^ 3) y = π (π (π y)) := by rw [pow_succ', Perm.mul_apply, e2]
  have e4 : (π ^ 4) y = π (π (π (π y))) := by rw [pow_succ', Perm.mul_apply, e3]
  rw [coe_firstReturn_of_pow (m := 4) (by omega) (by rw [e4]; exact h4), e4]
  intro j hj hj4
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl
  · rwa [pow_one]
  · rwa [e2]
  · rwa [e3]

end FirstReturnSteps

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

/-- The face permutation `σ ∘ ι°` of `H° = H \ x`. -/
noncomputable def hollowFacePerm (c : H) : Perm ({d | d ∉ X.vertexOf c} : Set H) :=
  (X.rot * X.hollowInv c).subtypePerm fun d => by
    simp only [Set.mem_setOf_eq, Perm.mul_apply, X.mem_vertexOf_iff_vertexOf_eq,
      RotationSystem.vertexOf_rot]
    rw [← X.mem_vertexOf_iff_vertexOf_eq, ← X.mem_vertexOf_iff_vertexOf_eq, hollowInv_mem_iff]

/-- `hollowFacePerm c` sends `y` to `σ(ι°(y))`. -/
@[simp]
theorem coe_hollowFacePerm (c : H) (y : ({d | d ∉ X.vertexOf c} : Set H)) :
    (X.hollowFacePerm c y : H) = X.rot (X.hollowInv c y) := rfl

private theorem bdry_nonempty_of_pre {X : TripleData H b} (hP : X.IsPreTripleDiagram) :
    X.bdry.Nonempty := by
  obtain ⟨f, hf, hfB, -, -⟩ := hP.exists_orbit
  obtain ⟨d, rfl⟩ := X.mem_faceOrbits.1 hf
  exact ⟨d, hfB (X.self_mem_faceOf d)⟩

section Euler

variable (hP : X.IsPreTripleDiagram) {c : H} (hc : X.IsHollowMonogon {c})

include hP hc

omit hc in
/-- The face permutation sends the reverse of `σᵏ c` to `σᵏ⁺¹ c`. -/
theorem facePerm_inv_rot_pow (k : ℕ) :
    X.facePerm (X.inv ((X.rot ^ k) c)) = (X.rot ^ (k + 1)) c := by
  rw [X.facePerm_apply, hP.inv_inv_apply, pow_succ', Perm.mul_apply]

/-- The face permutation sends `σ⁵ c` to `σ c`. -/
theorem facePerm_rot_pow_five : X.facePerm ((X.rot ^ 5) c) = (X.rot ^ 1) c := by
  obtain ⟨-, -, -, h5, -, -⟩ := hollowMonogon_facts hP hc
  rw [X.facePerm_apply, h5, hP.inv_inv_apply, pow_one]

omit hP hc in
/-- `σ(d)` lies at `v(c)` iff `d` does. -/
theorem rot_mem_vertexOf_iff {d : H} : X.rot d ∈ X.vertexOf c ↔ d ∈ X.vertexOf c := by
  rw [X.mem_vertexOf_iff_vertexOf_eq, X.mem_vertexOf_iff_vertexOf_eq, RotationSystem.vertexOf_rot]

/-- If `ā_k ∈ x` for `k ∈ [1, 4]`, then `ā_k = a_j` with `j ∈ [1, 4]` of the other parity. -/
theorem hollow_inv_rot_pow_eq {k j : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hj : j < 6)
    (h : X.inv ((X.rot ^ k) c) = (X.rot ^ j) c) : 1 ≤ j ∧ j ≤ 4 ∧ (k + j) % 2 = 1 := by
  obtain ⟨-, -, hx, h5, -, hinj⟩ := hollowMonogon_facts hP hc
  have hkB : (X.rot ^ k) c ∉ X.bdry := fun hB =>
    hx ⟨_, X.rot_pow_apply_mem_vertexOf k c, hB⟩
  have hpar : ∀ n, X.isOut ((X.rot ^ n) c) = xor (X.isOut c) (decide (n % 2 = 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply, hP.isOut_rot_apply (by rwa [X.vertexOf_rot_pow_apply]), ih]
      rcases Nat.mod_two_eq_zero_or_one n with h' | h'
      · have h'' : (n + 1) % 2 = 1 := by omega
        simp [h', h'']
      · have h'' : (n + 1) % 2 = 0 := by omega
        simp [h', h'']
  have ho := hP.isOut_inv_apply hkB
  rw [h, hpar, hpar] at ho
  have hj0 : j ≠ 0 := by
    rintro rfl
    have := congrArg X.inv h
    rw [hP.inv_inv_apply, pow_zero, Perm.one_apply, ← h5] at this
    have := hinj k 5 (by omega) (by omega) this
    omega
  have hj5 : j ≠ 5 := by
    rintro rfl
    have := congrArg X.inv h
    rw [hP.inv_inv_apply, h5, hP.inv_inv_apply] at this
    have := hinj k 0 (by omega) (by omega) (by simpa using this)
    omega
  refine ⟨by omega, by omega, ?_⟩
  by_contra hpj
  have hkj : decide (j % 2 = 1) = decide (k % 2 = 1) := decide_eq_decide.2 (by omega)
  rw [hkj] at ho
  cases X.isOut c <;> cases decide (k % 2 = 1) <;> simp at ho

/-- The four possible configurations of the edges at the vertex of a hollow monogon. -/
theorem hollow_cases (hX : X.IsTripleDiagram) :
    (X.inv ((X.rot ^ 1) c) ∉ X.vertexOf c ∧ X.inv ((X.rot ^ 2) c) ∉ X.vertexOf c ∧
      X.inv ((X.rot ^ 3) c) ∉ X.vertexOf c ∧ X.inv ((X.rot ^ 4) c) ∉ X.vertexOf c) ∨
    (X.inv ((X.rot ^ 1) c) = (X.rot ^ 2) c ∧ X.inv ((X.rot ^ 3) c) ∉ X.vertexOf c ∧
      X.inv ((X.rot ^ 4) c) ∉ X.vertexOf c) ∨
    (X.inv ((X.rot ^ 3) c) = (X.rot ^ 4) c ∧ X.inv ((X.rot ^ 1) c) ∉ X.vertexOf c ∧
      X.inv ((X.rot ^ 2) c) ∉ X.vertexOf c) ∨
    (X.inv ((X.rot ^ 1) c) = (X.rot ^ 4) c ∧ X.inv ((X.rot ^ 2) c) ∉ X.vertexOf c ∧
      X.inv ((X.rot ^ 3) c) ∉ X.vertexOf c) ∨
    (X.inv ((X.rot ^ 3) c) = (X.rot ^ 2) c ∧ X.inv ((X.rot ^ 1) c) ∉ X.vertexOf c ∧
      X.inv ((X.rot ^ 4) c) ∉ X.vertexOf c) := by
  obtain ⟨-, -, hx, h5, -, hinj⟩ := hollowMonogon_facts hP hc
  have hmem := fun d => hollow_mem_vertexOf_iff hP hc (d := d)
  have hne : ∀ i j : ℕ, i < 6 → j < 6 → i ≠ j → (X.rot ^ i) c ≠ (X.rot ^ j) c :=
    fun i j hi hj hij h => hij (hinj i j hi hj h)
  -- the possible partners
  have hp : ∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∈ X.vertexOf c →
      ∃ j, 1 ≤ j ∧ j ≤ 4 ∧ (k + j) % 2 = 1 ∧ X.inv ((X.rot ^ k) c) = (X.rot ^ j) c := by
    intro k hk1 hk4 h
    obtain ⟨j, hj, hjk⟩ := (hmem _).1 h
    obtain ⟨h1, h2, h3⟩ := hollow_inv_rot_pow_eq hP hc hk1 hk4 hj hjk.symm
    exact ⟨j, h1, h2, h3, hjk.symm⟩
  have hsym : ∀ k j, X.inv ((X.rot ^ k) c) = (X.rot ^ j) c →
      X.inv ((X.rot ^ j) c) = (X.rot ^ k) c := by
    intro k j h
    rw [← h, hP.inv_inv_apply]
  have hinvinj : ∀ k j, X.inv ((X.rot ^ k) c) = X.inv ((X.rot ^ j) c) →
      (X.rot ^ k) c = (X.rot ^ j) c := fun k j h => X.inv.injective h
  by_cases h1 : X.inv ((X.rot ^ 1) c) ∈ X.vertexOf c <;>
    by_cases h3 : X.inv ((X.rot ^ 3) c) ∈ X.vertexOf c
  · -- both: the vertex `x` would be closed
    exfalso
    obtain ⟨j₁, hj₁, hj₁', hp₁, he₁⟩ := hp 1 le_rfl (by omega) h1
    obtain ⟨j₃, hj₃, hj₃', hp₃, he₃⟩ := hp 3 (by omega) (by omega) h3
    have hj₁₃ : j₁ ≠ j₃ := by
      rintro rfl
      exact hne 1 3 (by omega) (by omega) (by omega) (hinvinj _ _ (he₁.trans he₃.symm))
    have hclosed : ∀ d ∈ X.vertexOf c, X.inv d ∈ X.vertexOf c := by
      intro d hd
      obtain ⟨k, hk, rfl⟩ := (hmem _).1 hd
      have hk' : k = 0 ∨ k = 5 ∨ k = 1 ∨ k = 3 ∨ k = j₁ ∨ k = j₃ := by omega
      rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [pow_zero, Perm.one_apply, ← h5]; exact X.rot_pow_apply_mem_vertexOf _ _
      · rw [h5, hP.inv_inv_apply]; exact X.self_mem_vertexOf c
      · exact h1
      · exact h3
      · rw [hsym _ _ he₁]; exact X.rot_pow_apply_mem_vertexOf _ _
      · rw [hsym _ _ he₃]; exact X.rot_pow_apply_mem_vertexOf _ _
    obtain ⟨e, he⟩ := bdry_nonempty_of_pre hX.toIsPreTripleDiagram
    have key : ∀ d, X.toRotationSystem.Reach c d → d ∈ X.vertexOf c := by
      intro d h
      induction h with
      | refl => exact X.self_mem_vertexOf c
      | rot _ ih => exact (rot_mem_vertexOf_iff (X := X) (c := c)).2 ih
      | inv _ ih => exact hclosed _ ih
    exact hx ⟨e, key e (hX.toIsDiskMap.toIsConnected.reach c e), he⟩
  · obtain ⟨j₁, hj₁, hj₁', hp₁, he₁⟩ := hp 1 le_rfl (by omega) h1
    have : j₁ = 2 ∨ j₁ = 4 := by omega
    rcases this with rfl | rfl
    · refine Or.inr (Or.inl ⟨he₁, h3, fun h4 => ?_⟩)
      obtain ⟨j₄, hj₄a, hj₄b, hp₄, he₄⟩ := hp 4 (by omega) le_rfl h4
      have : j₄ = 1 ∨ j₄ = 3 := by omega
      rcases this with rfl | rfl
      · exact hne 4 2 (by omega) (by omega) (by omega) ((hsym _ _ he₄).symm.trans he₁)
      · exact h3 (by rw [hsym _ _ he₄]; exact X.rot_pow_apply_mem_vertexOf _ _)
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨he₁, fun h2 => ?_, h3⟩)))
      obtain ⟨j₂, hj₂a, hj₂b, hp₂, he₂⟩ := hp 2 (by omega) (by omega) h2
      have : j₂ = 1 ∨ j₂ = 3 := by omega
      rcases this with rfl | rfl
      · exact hne 2 4 (by omega) (by omega) (by omega) ((hsym _ _ he₂).symm.trans he₁)
      · exact h3 (by rw [hsym _ _ he₂]; exact X.rot_pow_apply_mem_vertexOf _ _)
  · obtain ⟨j₃, hj₃, hj₃', hp₃, he₃⟩ := hp 3 (by omega) (by omega) h3
    have : j₃ = 2 ∨ j₃ = 4 := by omega
    rcases this with rfl | rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨he₃, h1, fun h4 => ?_⟩)))
      obtain ⟨j₄, hj₄a, hj₄b, hp₄, he₄⟩ := hp 4 (by omega) le_rfl h4
      have : j₄ = 1 ∨ j₄ = 3 := by omega
      rcases this with rfl | rfl
      · exact h1 (by rw [hsym _ _ he₄]; exact X.rot_pow_apply_mem_vertexOf _ _)
      · exact hne 4 2 (by omega) (by omega) (by omega) ((hsym _ _ he₄).symm.trans he₃)
    · refine Or.inr (Or.inr (Or.inl ⟨he₃, h1, fun h2 => ?_⟩))
      obtain ⟨j₂, hj₂a, hj₂b, hp₂, he₂⟩ := hp 2 (by omega) (by omega) h2
      have : j₂ = 1 ∨ j₂ = 3 := by omega
      rcases this with rfl | rfl
      · exact h1 (by rw [hsym _ _ he₂]; exact X.rot_pow_apply_mem_vertexOf _ _)
      · exact hne 2 4 (by omega) (by omega) (by omega) ((hsym _ _ he₂).symm.trans he₃)
  · refine Or.inl ⟨h1, fun h2 => ?_, h3, fun h4 => ?_⟩
    · obtain ⟨j₂, hj₂a, hj₂b, hp₂, he₂⟩ := hp 2 (by omega) (by omega) h2
      have : j₂ = 1 ∨ j₂ = 3 := by omega
      rcases this with rfl | rfl
      · exact h1 (by rw [hsym _ _ he₂]; exact X.rot_pow_apply_mem_vertexOf _ _)
      · exact h3 (by rw [hsym _ _ he₂]; exact X.rot_pow_apply_mem_vertexOf _ _)
    · obtain ⟨j₄, hj₄a, hj₄b, hp₄, he₄⟩ := hp 4 (by omega) le_rfl h4
      have : j₄ = 1 ∨ j₄ = 3 := by omega
      rcases this with rfl | rfl
      · exact h1 (by rw [hsym _ _ he₄]; exact X.rot_pow_apply_mem_vertexOf _ _)
      · exact h3 (by rw [hsym _ _ he₄]; exact X.rot_pow_apply_mem_vertexOf _ _)

/-- A dart outside `x` whose reverse is at `x` is some `ā_k`, `k ∈ [1, 4]`. -/
theorem eq_inv_of_inv_mem {y : H} (hy : y ∉ X.vertexOf c) (hiy : X.inv y ∈ X.vertexOf c) :
    ∃ k, 1 ≤ k ∧ k ≤ 4 ∧ y = X.inv ((X.rot ^ k) c) := by
  obtain ⟨-, -, -, h5, -, -⟩ := hollowMonogon_facts hP hc
  obtain ⟨k, hk, hk'⟩ := (hollow_mem_vertexOf_iff hP hc).1 hiy
  have hy' : y = X.inv ((X.rot ^ k) c) := by rw [hk', hP.inv_inv_apply]
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hy
    rw [hy', pow_zero, Perm.one_apply, ← h5]
    exact X.rot_pow_apply_mem_vertexOf _ _
  have hk5 : k ≠ 5 := by
    rintro rfl
    apply hy
    rw [hy', h5, hP.inv_inv_apply]
    exact X.self_mem_vertexOf c
  exact ⟨k, by omega, by omega, hy'⟩

/-- Every dart outside `x` reaches, in `(H, ι°, σ)`, some `ā_k ∉ x` with `k ∈ [1, 4]`. -/
theorem hollow_reach_bar (hX : X.IsTripleDiagram) {d : H} (hd : d ∉ X.vertexOf c) :
    ∃ k, 1 ≤ k ∧ k ≤ 4 ∧ X.inv ((X.rot ^ k) c) ∉ X.vertexOf c ∧
      (X.hollowRotationSystem c).Reach d (X.inv ((X.rot ^ k) c)) := by
  suffices H' : ∀ e, X.toRotationSystem.Reach d e →
      (e ∉ X.vertexOf c ∧ (X.hollowRotationSystem c).Reach d e) ∨
      ∃ k, 1 ≤ k ∧ k ≤ 4 ∧ X.inv ((X.rot ^ k) c) ∉ X.vertexOf c ∧
        (X.hollowRotationSystem c).Reach d (X.inv ((X.rot ^ k) c)) by
    exact (H' c (hX.toIsDiskMap.toIsConnected.reach d c)).resolve_left
      fun h => h.1 (X.self_mem_vertexOf c)
  intro e h
  induction h with
  | refl => exact Or.inl ⟨hd, RotationSystem.Reach.refl d⟩
  | @rot y _ ih =>
    rcases ih with ⟨hy, hr⟩ | h
    · exact Or.inl ⟨fun h' => hy ((rot_mem_vertexOf_iff (X := X) (c := c)).1 h'), hr.rot⟩
    · exact Or.inr h
  | @inv y _ ih =>
    rcases ih with ⟨hy, hr⟩ | h
    · by_cases hiy : X.inv y ∈ X.vertexOf c
      · obtain ⟨j, hj1, hj4, hy'⟩ := eq_inv_of_inv_mem hP hc hy hiy
        exact Or.inr ⟨j, hj1, hj4, hy' ▸ hy, hy' ▸ hr⟩
      · have := hr.inv
        change (X.hollowRotationSystem c).Reach d (X.hollowInv c y) at this
        rw [hollowInv_apply_of_inv_notMem hP hc hy hiy] at this
        exact Or.inl ⟨hiy, this⟩
    · exact Or.inr h

end Euler

end TripleData

end ClusterAlgebras

namespace ClusterAlgebras

open Finset Equiv

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

/-- The orbit of a dart `d` under `π` lies in `orbitsOn π S` when `d` is in the orbit of a point
of `S`. -/
private theorem orbit_mem_orbitsOn {π : Perm H} {S : Finset H} {d y : H} (hy : y ∈ S)
    (h : π.SameCycle d y) : ({e | π.SameCycle d e} : Finset H) ∈ orbitsOn π S :=
  mem_image.2 ⟨y, hy, orbit_eq_iff.2 h.symm⟩

section EulerCases

variable (hP : X.IsPreTripleDiagram) {c : H} (hc : X.IsHollowMonogon {c})

include hP hc

/-- Darts whose reverse is not at `x` are left alone by `ι°` and `ψ`. -/
theorem hollowFacePerm_apply_eq_firstReturn {y : ({d | d ∉ X.vertexOf c} : Set H)}
    (hy : X.inv y ∉ X.vertexOf c) :
    (X.hollowFacePerm c y : H) =
      (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} y : H) := by
  rw [coe_hollowFacePerm, hollowInv_apply_of_inv_notMem hP hc y.2 hy, coe_firstReturnPerm,
    coe_firstReturn_of_apply_mem]
  · rfl
  · change X.rot (X.inv y) ∉ X.vertexOf c
    rwa [rot_mem_vertexOf_iff (X := X) (c := c)]

/-- **The generic case.** If no edge at `x` other than the loop has both ends at `x`, then
`σ ι° = ψ ∘ (ā₃ ā₁)` on `H \ x`, where `ψ` is the first return of `φ`. -/
theorem hollowFacePerm_eq_generic
    (h1 : X.inv ((X.rot ^ 1) c) ∉ X.vertexOf c) (h2 : X.inv ((X.rot ^ 2) c) ∉ X.vertexOf c)
    (h3 : X.inv ((X.rot ^ 3) c) ∉ X.vertexOf c) (h4 : X.inv ((X.rot ^ 4) c) ∉ X.vertexOf c) :
    X.hollowFacePerm c = firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} *
      swap ⟨X.inv ((X.rot ^ 3) c), h3⟩ ⟨X.inv ((X.rot ^ 1) c), h1⟩ := by
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := hollowSwap_rot_pow_apply hP hc
  have hA : ∀ k, (X.rot ^ k) c ∈ X.vertexOf c := fun k => X.rot_pow_apply_mem_vertexOf k c
  have hr := fun d => rot_mem_vertexOf_iff (X := X) (c := c) (d := d)
  have ii : ∀ k, X.inv (X.inv ((X.rot ^ k) c)) = (X.rot ^ k) c := fun k => hP.inv_inv_apply _
  have φ1 : X.facePerm (X.inv ((X.rot ^ 1) c)) = (X.rot ^ 2) c := facePerm_inv_rot_pow hP (c := c) 1
  have φ2 : X.facePerm (X.inv ((X.rot ^ 2) c)) = (X.rot ^ 3) c := facePerm_inv_rot_pow hP (c := c) 2
  have φ3 : X.facePerm (X.inv ((X.rot ^ 3) c)) = (X.rot ^ 4) c := facePerm_inv_rot_pow hP (c := c) 3
  have φ4 : X.facePerm (X.inv ((X.rot ^ 4) c)) = (X.rot ^ 5) c := facePerm_inv_rot_pow hP (c := c) 4
  have φ5 := facePerm_rot_pow_five hP hc
  have φa : ∀ k, X.facePerm ((X.rot ^ k) c) = X.rot (X.inv ((X.rot ^ k) c)) := fun k => rfl
  have hn : ∀ k, X.rot (X.inv ((X.rot ^ k) c)) ∉ X.vertexOf c ↔
      X.inv ((X.rot ^ k) c) ∉ X.vertexOf c := fun k => by rw [hr]
  -- `ι°` on the four darts
  have ι1 : X.hollowInv c (X.inv ((X.rot ^ 1) c)) = X.inv ((X.rot ^ 4) c) := by
    rw [hollowInv_apply_two hP hc h1 (by rw [ii]; exact hA 1) (by rw [ii, v1]; exact h4), ii, v1]
  have ι2 : X.hollowInv c (X.inv ((X.rot ^ 2) c)) = X.inv ((X.rot ^ 3) c) := by
    rw [hollowInv_apply_two hP hc h2 (by rw [ii]; exact hA 2) (by rw [ii, v2]; exact h3), ii, v2]
  have ι3 : X.hollowInv c (X.inv ((X.rot ^ 3) c)) = X.inv ((X.rot ^ 2) c) := by
    rw [hollowInv_apply_two hP hc h3 (by rw [ii]; exact hA 3) (by rw [ii, v3]; exact h2), ii, v3]
  have ι4 : X.hollowInv c (X.inv ((X.rot ^ 4) c)) = X.inv ((X.rot ^ 1) c) := by
    rw [hollowInv_apply_two hP hc h4 (by rw [ii]; exact hA 4) (by rw [ii, v4]; exact h1), ii, v4]
  -- `ψ` on the four darts
  have ψ1 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h1⟩ : H) =
      X.rot (X.inv ((X.rot ^ 2) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_two]
    · change X.facePerm (X.facePerm (X.inv ((X.rot ^ 1) c))) = _
      rw [φ1]; exact φa _
    · change ¬(X.facePerm (X.inv ((X.rot ^ 1) c)) ∉ X.vertexOf c)
      rw [φ1, not_not]; exact hA 2
    · change X.facePerm (X.facePerm (X.inv ((X.rot ^ 1) c))) ∉ X.vertexOf c
      rw [φ1, φa, hn]; exact h2
  have ψ2 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h2⟩ : H) =
      X.rot (X.inv ((X.rot ^ 3) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_two]
    · change X.facePerm (X.facePerm (X.inv ((X.rot ^ 2) c))) = _
      rw [φ2]; exact φa _
    · change ¬(X.facePerm (X.inv ((X.rot ^ 2) c)) ∉ X.vertexOf c)
      rw [φ2, not_not]; exact hA 3
    · change X.facePerm (X.facePerm (X.inv ((X.rot ^ 2) c))) ∉ X.vertexOf c
      rw [φ2, φa, hn]; exact h3
  have ψ3 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h3⟩ : H) =
      X.rot (X.inv ((X.rot ^ 4) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_two]
    · change X.facePerm (X.facePerm (X.inv ((X.rot ^ 3) c))) = _
      rw [φ3]; exact φa _
    · change ¬(X.facePerm (X.inv ((X.rot ^ 3) c)) ∉ X.vertexOf c)
      rw [φ3, not_not]; exact hA 4
    · change X.facePerm (X.facePerm (X.inv ((X.rot ^ 3) c))) ∉ X.vertexOf c
      rw [φ3, φa, hn]; exact h4
  have ψ4 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h4⟩ : H) =
      X.rot (X.inv ((X.rot ^ 1) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_three]
    · change X.facePerm (X.facePerm (X.facePerm (X.inv ((X.rot ^ 4) c)))) = _
      rw [φ4, φ5]; exact φa _
    · change ¬(X.facePerm (X.inv ((X.rot ^ 4) c)) ∉ X.vertexOf c)
      rw [φ4, not_not]; exact hA 5
    · change ¬(X.facePerm (X.facePerm (X.inv ((X.rot ^ 4) c))) ∉ X.vertexOf c)
      rw [φ4, φ5, not_not]; exact hA 1
    · change X.facePerm (X.facePerm (X.facePerm (X.inv ((X.rot ^ 4) c)))) ∉ X.vertexOf c
      rw [φ4, φ5, φa, hn]; exact h1
  ext y : 1
  apply Subtype.ext
  rw [coe_hollowFacePerm, Perm.mul_apply]
  by_cases hy1 : (y : H) = X.inv ((X.rot ^ 1) c)
  · obtain rfl : y = ⟨_, h1⟩ := Subtype.ext hy1
    rw [swap_apply_right, ψ3]
    exact congrArg X.rot ι1
  by_cases hy3 : (y : H) = X.inv ((X.rot ^ 3) c)
  · obtain rfl : y = ⟨_, h3⟩ := Subtype.ext hy3
    rw [swap_apply_left, ψ1]
    exact congrArg X.rot ι3
  rw [swap_apply_of_ne_of_ne (fun h => hy3 (congrArg Subtype.val h))
    (fun h => hy1 (congrArg Subtype.val h))]
  by_cases hy2 : (y : H) = X.inv ((X.rot ^ 2) c)
  · obtain rfl : y = ⟨_, h2⟩ := Subtype.ext hy2
    rw [ψ2]
    exact congrArg X.rot ι2
  by_cases hy4 : (y : H) = X.inv ((X.rot ^ 4) c)
  · obtain rfl : y = ⟨_, h4⟩ := Subtype.ext hy4
    rw [ψ4]
    exact congrArg X.rot ι4
  have hiy : X.inv y ∉ X.vertexOf c := by
    intro hiy
    obtain ⟨k, hk1, hk4, hk⟩ := eq_inv_of_inv_mem hP hc y.2 hiy
    interval_cases k
    · exact hy1 hk
    · exact hy2 hk
    · exact hy3 hk
    · exact hy4 hk
  rw [← coe_hollowFacePerm]
  exact hollowFacePerm_apply_eq_firstReturn hP hc hiy

/-- In the generic case, the orbits of `φ` through `x` other than `{c}` meet `H \ x`. -/
private theorem orbitsOn_vertexOf_subset_generic
    (h1 : X.inv ((X.rot ^ 1) c) ∉ X.vertexOf c) (h2 : X.inv ((X.rot ^ 2) c) ∉ X.vertexOf c)
    (h3 : X.inv ((X.rot ^ 3) c) ∉ X.vertexOf c) (h4 : X.inv ((X.rot ^ 4) c) ∉ X.vertexOf c) :
    orbitsOn X.facePerm (X.vertexOf c) ⊆
      orbitsOn X.facePerm (univ.filter fun d => d ∉ X.vertexOf c) ∪
        {({e | X.facePerm.SameCycle c e} : Finset H)} := by
  have hr := fun d => rot_mem_vertexOf_iff (X := X) (c := c) (d := d)
  have hY : ∀ k, X.inv ((X.rot ^ k) c) ∉ X.vertexOf c →
      X.rot (X.inv ((X.rot ^ k) c)) ∈ univ.filter fun d => d ∉ X.vertexOf c := by
    intro k hk
    simp only [mem_filter, mem_univ, true_and]
    rwa [hr]
  have hstep : ∀ d, X.facePerm.SameCycle d (X.facePerm d) := fun d =>
    Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)
  intro o ho
  obtain ⟨d, hd, rfl⟩ := mem_image.1 ho
  obtain ⟨k, hk, rfl⟩ := (hollow_mem_vertexOf_iff hP hc).1 hd
  rw [mem_union]
  interval_cases k
  · right
    simp
  · exact Or.inl (orbit_mem_orbitsOn (hY 1 h1) (hstep _))
  · exact Or.inl (orbit_mem_orbitsOn (hY 2 h2) (hstep _))
  · exact Or.inl (orbit_mem_orbitsOn (hY 3 h3) (hstep _))
  · exact Or.inl (orbit_mem_orbitsOn (hY 4 h4) (hstep _))
  · left
    refine orbit_mem_orbitsOn (hY 1 h1) ?_
    have := (hstep ((X.rot ^ 5) c)).trans (hstep _)
    rwa [facePerm_rot_pow_five hP hc] at this

end EulerCases

end TripleData

end ClusterAlgebras

namespace ClusterAlgebras

open Finset Equiv

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

section EulerExceptional

variable (hP : X.IsPreTripleDiagram) {c : H} (hc : X.IsHollowMonogon {c})

include hP hc

/-- **The exceptional cases.** If exactly two of the darts `ā_k`, `k ∈ [1, 4]`, lie outside `x`,
namely `ā_p` and `ā_q`, with `ι°(ā_p) = ā_q`, `ι°(ā_q) = ā_p`, `ψ(ā_p) = σ(ā_q)` and
`ψ(ā_q) = σ(ā_p)`, then `σ ι° = ψ` on `H \ x`. -/
theorem hollowFacePerm_eq_firstReturn_of {p q : ℕ} (hp : X.inv ((X.rot ^ p) c) ∉ X.vertexOf c)
    (hq : X.inv ((X.rot ^ q) c) ∉ X.vertexOf c)
    (hothers : ∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∉ X.vertexOf c → k = p ∨ k = q)
    (ιp : X.hollowInv c (X.inv ((X.rot ^ p) c)) = X.inv ((X.rot ^ q) c))
    (ιq : X.hollowInv c (X.inv ((X.rot ^ q) c)) = X.inv ((X.rot ^ p) c))
    (ψp : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, hp⟩ : H) =
      X.rot (X.inv ((X.rot ^ q) c)))
    (ψq : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, hq⟩ : H) =
      X.rot (X.inv ((X.rot ^ p) c))) :
    X.hollowFacePerm c = firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} := by
  ext y : 1
  apply Subtype.ext
  by_cases hyp : (y : H) = X.inv ((X.rot ^ p) c)
  · obtain rfl : y = ⟨_, hp⟩ := Subtype.ext hyp
    rw [coe_hollowFacePerm, ψp]
    exact congrArg X.rot ιp
  by_cases hyq : (y : H) = X.inv ((X.rot ^ q) c)
  · obtain rfl : y = ⟨_, hq⟩ := Subtype.ext hyq
    rw [coe_hollowFacePerm, ψq]
    exact congrArg X.rot ιq
  have hiy : X.inv y ∉ X.vertexOf c := by
    intro hiy
    obtain ⟨k, hk1, hk4, hk⟩ := eq_inv_of_inv_mem hP hc y.2 hiy
    rcases hothers k hk1 hk4 (hk ▸ y.2) with rfl | rfl
    · exact hyp hk
    · exact hyq hk
  exact hollowFacePerm_apply_eq_firstReturn hP hc hiy

/-- In the exceptional cases, every dart outside `x` is a dart of the removal. -/
theorem mem_hollowDarts_of_exceptional (hX : X.IsTripleDiagram) {p q : ℕ}
    (hothers : ∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∉ X.vertexOf c → k = p ∨ k = q)
    (ιp : X.hollowInv c (X.inv ((X.rot ^ p) c)) = X.inv ((X.rot ^ q) c)) {d : H}
    (hd : d ∉ X.vertexOf c) : d ∈ X.hollowDarts c := by
  -- every dart outside `x` reaches `ā_q`
  have hreach : ∀ e, e ∉ X.vertexOf c →
      (X.hollowRotationSystem c).Reach e (X.inv ((X.rot ^ q) c)) := by
    intro e he
    obtain ⟨k, hk1, hk4, hk, hr⟩ := hollow_reach_bar hP hc hX he
    rcases hothers k hk1 hk4 hk with rfl | rfl
    · have := hr.inv
      change (X.hollowRotationSystem c).Reach e (X.hollowInv c _) at this
      rwa [ιp] at this
    · exact hr
  obtain ⟨e, he⟩ := bdry_nonempty_of_pre hX.toIsPreTripleDiagram
  have heY := notMem_vertexOf_of_mem_bdry hP hc he
  exact (X.mem_hollowDarts).2 ⟨e, he, (hreach e heY).trans (hreach d hd).symm⟩

omit hc in
private theorem hollow_aux_facts :
    (∀ k, (X.rot ^ k) c ∈ X.vertexOf c) ∧
    (∀ k, X.inv (X.inv ((X.rot ^ k) c)) = (X.rot ^ k) c) ∧
    (∀ k, X.facePerm (X.inv ((X.rot ^ k) c)) = (X.rot ^ (k + 1)) c) ∧
    (∀ k, X.facePerm ((X.rot ^ k) c) = X.rot (X.inv ((X.rot ^ k) c))) ∧
    (∀ k, X.rot ((X.rot ^ k) c) = (X.rot ^ (k + 1)) c) ∧
    (∀ d, X.rot d ∈ X.vertexOf c ↔ d ∈ X.vertexOf c) :=
  ⟨fun k => X.rot_pow_apply_mem_vertexOf k c, fun k => hP.inv_inv_apply _,
    facePerm_inv_rot_pow hP (c := c), fun _ => rfl,
    fun k => by rw [pow_succ', Perm.mul_apply], fun _ => rot_mem_vertexOf_iff (X := X) (c := c)⟩

/-- The case `ā₁ = a₂`. -/
private theorem hollowFacePerm_eq_firstReturn_e12 (e : X.inv ((X.rot ^ 1) c) = (X.rot ^ 2) c)
    (h3 : X.inv ((X.rot ^ 3) c) ∉ X.vertexOf c) (h4 : X.inv ((X.rot ^ 4) c) ∉ X.vertexOf c) :
    X.hollowFacePerm c = firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ∧
    (∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∉ X.vertexOf c → k = 3 ∨ k = 4) ∧
    X.hollowInv c (X.inv ((X.rot ^ 3) c)) = X.inv ((X.rot ^ 4) c) ∧
    orbitsOn X.facePerm (X.vertexOf c) ⊆
      orbitsOn X.facePerm (univ.filter fun d => d ∉ X.vertexOf c) ∪
        {({e | X.facePerm.SameCycle c e} : Finset H),
          ({e | X.facePerm.SameCycle ((X.rot ^ 2) c) e} : Finset H)} := by
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := hollowSwap_rot_pow_apply hP hc
  obtain ⟨hA, ii, φb, φa, hs, hr⟩ := hollow_aux_facts hP (c := c)
  have φ5 := facePerm_rot_pow_five hP hc
  have φ5' : X.rot (X.inv ((X.rot ^ 5) c)) = (X.rot ^ 1) c := φ5
  have φ3 : X.facePerm (X.inv ((X.rot ^ 3) c)) = (X.rot ^ 4) c := φb 3
  have φ4 : X.facePerm (X.inv ((X.rot ^ 4) c)) = (X.rot ^ 5) c := φb 4
  have s2 : X.rot ((X.rot ^ 2) c) = (X.rot ^ 3) c := hs 2
  have e' : X.inv ((X.rot ^ 2) c) = (X.rot ^ 1) c := by rw [← e, ii]
  have hothers : ∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∉ X.vertexOf c → k = 3 ∨ k = 4 := by
    intro k hk1 hk4 hk
    interval_cases k
    · exact absurd (e ▸ hA 2) hk
    · exact absurd (e' ▸ hA 1) hk
    · exact Or.inl rfl
    · exact Or.inr rfl
  have ι3 : X.hollowInv c (X.inv ((X.rot ^ 3) c)) = X.inv ((X.rot ^ 4) c) := by
    rw [hollowInv_apply_three hP hc h3 (by rw [ii]; exact hA 3) (by rw [ii, v3, e']; exact hA 1)
      (by rw [ii, v3, e', v1]; exact h4), ii, v3, e', v1]
  have ι4 : X.hollowInv c (X.inv ((X.rot ^ 4) c)) = X.inv ((X.rot ^ 3) c) := by
    rw [hollowInv_apply_three hP hc h4 (by rw [ii]; exact hA 4) (by rw [ii, v4, e]; exact hA 2)
      (by rw [ii, v4, e, v2]; exact h3), ii, v4, e, v2]
  have ψ3 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h3⟩ : H) =
      X.rot (X.inv ((X.rot ^ 4) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_two] <;>
      simp only [Set.mem_setOf_eq, not_not, not_false_eq_true, φ3, φa,
        hr, hA, h4]
  have ψ4 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h4⟩ : H) =
      X.rot (X.inv ((X.rot ^ 3) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_four] <;>
      simp only [Set.mem_setOf_eq, not_not, not_false_eq_true, φ4, φ5, φa, s2,
        e, hr, hA, h3]
  refine ⟨hollowFacePerm_eq_firstReturn_of hP hc h3 h4 hothers ι3 ι4 ψ3 ψ4, hothers, ι3, ?_⟩
  have hY : ∀ k, X.inv ((X.rot ^ k) c) ∉ X.vertexOf c →
      X.rot (X.inv ((X.rot ^ k) c)) ∈ univ.filter fun d => d ∉ X.vertexOf c := by
    intro k hk
    simp only [mem_filter, mem_univ, true_and]
    rwa [hr]
  have hstep : ∀ d, X.facePerm.SameCycle d (X.facePerm d) := fun d =>
    Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)
  intro o ho
  obtain ⟨d, hd, rfl⟩ := mem_image.1 ho
  obtain ⟨k, hk, rfl⟩ := (hollow_mem_vertexOf_iff hP hc).1 hd
  rw [mem_union, mem_insert, mem_singleton]
  interval_cases k
  · exact Or.inr (Or.inl (by simp))
  · -- `a₁ → a₃ → σ ā₃`
    refine Or.inl (orbit_mem_orbitsOn (hY 3 h3) ?_)
    have := (hstep ((X.rot ^ 1) c)).trans (hstep _)
    simp only [φa, e, s2] at this
    exact this
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl (orbit_mem_orbitsOn (hY 3 h3) (hstep _))
  · exact Or.inl (orbit_mem_orbitsOn (hY 4 h4) (hstep _))
  · refine Or.inl (orbit_mem_orbitsOn (hY 3 h3) ?_)
    have := ((hstep ((X.rot ^ 5) c)).trans (hstep _)).trans (hstep _)
    simp only [φa, φ5', e, s2] at this
    exact this

/-- The case `ā₃ = a₄`. -/
private theorem hollowFacePerm_eq_firstReturn_e34 (e : X.inv ((X.rot ^ 3) c) = (X.rot ^ 4) c)
    (h1 : X.inv ((X.rot ^ 1) c) ∉ X.vertexOf c) (h2 : X.inv ((X.rot ^ 2) c) ∉ X.vertexOf c) :
    X.hollowFacePerm c = firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ∧
    (∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∉ X.vertexOf c → k = 1 ∨ k = 2) ∧
    X.hollowInv c (X.inv ((X.rot ^ 1) c)) = X.inv ((X.rot ^ 2) c) ∧
    orbitsOn X.facePerm (X.vertexOf c) ⊆
      orbitsOn X.facePerm (univ.filter fun d => d ∉ X.vertexOf c) ∪
        {({e | X.facePerm.SameCycle c e} : Finset H),
          ({e | X.facePerm.SameCycle ((X.rot ^ 4) c) e} : Finset H)} := by
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := hollowSwap_rot_pow_apply hP hc
  obtain ⟨hA, ii, φb, φa, hs, hr⟩ := hollow_aux_facts hP (c := c)
  have φ5 := facePerm_rot_pow_five hP hc
  have φ5' : X.rot (X.inv ((X.rot ^ 5) c)) = (X.rot ^ 1) c := φ5
  have φ1 : X.facePerm (X.inv ((X.rot ^ 1) c)) = (X.rot ^ 2) c := φb 1
  have φ2 : X.facePerm (X.inv ((X.rot ^ 2) c)) = (X.rot ^ 3) c := φb 2
  have s4 : X.rot ((X.rot ^ 4) c) = (X.rot ^ 5) c := hs 4
  have e' : X.inv ((X.rot ^ 4) c) = (X.rot ^ 3) c := by rw [← e, ii]
  have hothers : ∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∉ X.vertexOf c → k = 1 ∨ k = 2 := by
    intro k hk1 hk4 hk
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (e ▸ hA 4) hk
    · exact absurd (e' ▸ hA 3) hk
  have ι1 : X.hollowInv c (X.inv ((X.rot ^ 1) c)) = X.inv ((X.rot ^ 2) c) := by
    rw [hollowInv_apply_three hP hc h1 (by rw [ii]; exact hA 1) (by rw [ii, v1, e']; exact hA 3)
      (by rw [ii, v1, e', v3]; exact h2), ii, v1, e', v3]
  have ι2 : X.hollowInv c (X.inv ((X.rot ^ 2) c)) = X.inv ((X.rot ^ 1) c) := by
    rw [hollowInv_apply_three hP hc h2 (by rw [ii]; exact hA 2) (by rw [ii, v2, e]; exact hA 4)
      (by rw [ii, v2, e, v4]; exact h1), ii, v2, e, v4]
  have ψ1 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h1⟩ : H) =
      X.rot (X.inv ((X.rot ^ 2) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_two] <;>
      simp only [Set.mem_setOf_eq, not_not, not_false_eq_true, φ1, φa,
        hr, hA, h2]
  have ψ2 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h2⟩ : H) =
      X.rot (X.inv ((X.rot ^ 1) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_four] <;>
      simp only [Set.mem_setOf_eq, not_not, not_false_eq_true, φ2, φ5, φa,
        s4, e, hr, hA, h1]
  refine ⟨hollowFacePerm_eq_firstReturn_of hP hc h1 h2 hothers ι1 ι2 ψ1 ψ2, hothers, ι1, ?_⟩
  have hY : ∀ k, X.inv ((X.rot ^ k) c) ∉ X.vertexOf c →
      X.rot (X.inv ((X.rot ^ k) c)) ∈ univ.filter fun d => d ∉ X.vertexOf c := by
    intro k hk
    simp only [mem_filter, mem_univ, true_and]
    rwa [hr]
  have hstep : ∀ d, X.facePerm.SameCycle d (X.facePerm d) := fun d =>
    Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)
  intro o ho
  obtain ⟨d, hd, rfl⟩ := mem_image.1 ho
  obtain ⟨k, hk, rfl⟩ := (hollow_mem_vertexOf_iff hP hc).1 hd
  rw [mem_union, mem_insert, mem_singleton]
  interval_cases k
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inl (orbit_mem_orbitsOn (hY 1 h1) (hstep _))
  · exact Or.inl (orbit_mem_orbitsOn (hY 2 h2) (hstep _))
  · refine Or.inl (orbit_mem_orbitsOn (hY 1 h1) ?_)
    have := ((hstep ((X.rot ^ 3) c)).trans (hstep _)).trans (hstep _)
    simp only [φa, φ5', e, s4] at this
    exact this
  · exact Or.inr (Or.inr rfl)
  · refine Or.inl (orbit_mem_orbitsOn (hY 1 h1) ?_)
    have := (hstep ((X.rot ^ 5) c)).trans (hstep _)
    simp only [φa, φ5'] at this
    exact this

/-- The case `ā₁ = a₄`. -/
private theorem hollowFacePerm_eq_firstReturn_e14 (e : X.inv ((X.rot ^ 1) c) = (X.rot ^ 4) c)
    (h2 : X.inv ((X.rot ^ 2) c) ∉ X.vertexOf c) (h3 : X.inv ((X.rot ^ 3) c) ∉ X.vertexOf c) :
    X.hollowFacePerm c = firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ∧
    (∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∉ X.vertexOf c → k = 2 ∨ k = 3) ∧
    X.hollowInv c (X.inv ((X.rot ^ 2) c)) = X.inv ((X.rot ^ 3) c) ∧
    orbitsOn X.facePerm (X.vertexOf c) ⊆
      orbitsOn X.facePerm (univ.filter fun d => d ∉ X.vertexOf c) ∪
        {({e | X.facePerm.SameCycle c e} : Finset H),
          ({e | X.facePerm.SameCycle ((X.rot ^ 1) c) e} : Finset H)} := by
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := hollowSwap_rot_pow_apply hP hc
  obtain ⟨hA, ii, φb, φa, hs, hr⟩ := hollow_aux_facts hP (c := c)
  have φ5 := facePerm_rot_pow_five hP hc
  have φ5' : X.rot (X.inv ((X.rot ^ 5) c)) = (X.rot ^ 1) c := φ5
  have φ2 : X.facePerm (X.inv ((X.rot ^ 2) c)) = (X.rot ^ 3) c := φb 2
  have φ3 : X.facePerm (X.inv ((X.rot ^ 3) c)) = (X.rot ^ 4) c := φb 3
  have s1 : X.rot ((X.rot ^ 1) c) = (X.rot ^ 2) c := hs 1
  have e' : X.inv ((X.rot ^ 4) c) = (X.rot ^ 1) c := by rw [← e, ii]
  have hothers : ∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∉ X.vertexOf c → k = 2 ∨ k = 3 := by
    intro k hk1 hk4 hk
    interval_cases k
    · exact absurd (e ▸ hA 4) hk
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (e' ▸ hA 1) hk
  have ι2 : X.hollowInv c (X.inv ((X.rot ^ 2) c)) = X.inv ((X.rot ^ 3) c) := by
    rw [hollowInv_apply_two hP hc h2 (by rw [ii]; exact hA 2) (by rw [ii, v2]; exact h3), ii, v2]
  have ι3 : X.hollowInv c (X.inv ((X.rot ^ 3) c)) = X.inv ((X.rot ^ 2) c) := by
    rw [hollowInv_apply_two hP hc h3 (by rw [ii]; exact hA 3) (by rw [ii, v3]; exact h2), ii, v3]
  have ψ2 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h2⟩ : H) =
      X.rot (X.inv ((X.rot ^ 3) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_two] <;>
      simp only [Set.mem_setOf_eq, not_not, not_false_eq_true, φ2, φa,
        hr, hA, h3]
  have ψ3 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h3⟩ : H) =
      X.rot (X.inv ((X.rot ^ 2) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_three] <;>
      simp only [Set.mem_setOf_eq, not_not, not_false_eq_true, φ3, φa, s1,
        e', hr, hA, h2]
  refine ⟨hollowFacePerm_eq_firstReturn_of hP hc h2 h3 hothers ι2 ι3 ψ2 ψ3, hothers, ι2, ?_⟩
  have hY : ∀ k, X.inv ((X.rot ^ k) c) ∉ X.vertexOf c →
      X.rot (X.inv ((X.rot ^ k) c)) ∈ univ.filter fun d => d ∉ X.vertexOf c := by
    intro k hk
    simp only [mem_filter, mem_univ, true_and]
    rwa [hr]
  have hstep : ∀ d, X.facePerm.SameCycle d (X.facePerm d) := fun d =>
    Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)
  intro o ho
  obtain ⟨d, hd, rfl⟩ := mem_image.1 ho
  obtain ⟨k, hk, rfl⟩ := (hollow_mem_vertexOf_iff hP hc).1 hd
  rw [mem_union, mem_insert, mem_singleton]
  interval_cases k
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl (orbit_mem_orbitsOn (hY 2 h2) (hstep _))
  · exact Or.inl (orbit_mem_orbitsOn (hY 3 h3) (hstep _))
  · refine Or.inl (orbit_mem_orbitsOn (hY 2 h2) ?_)
    have := (hstep ((X.rot ^ 4) c)).trans (hstep _)
    simp only [φa, e', s1] at this
    exact this
  · refine Or.inr (Or.inr ?_)
    rw [orbit_eq_iff]
    have := hstep ((X.rot ^ 5) c)
    simp only [φa, φ5'] at this
    exact this

/-- The case `ā₃ = a₂`. -/
private theorem hollowFacePerm_eq_firstReturn_e32 (e : X.inv ((X.rot ^ 3) c) = (X.rot ^ 2) c)
    (h1 : X.inv ((X.rot ^ 1) c) ∉ X.vertexOf c) (h4 : X.inv ((X.rot ^ 4) c) ∉ X.vertexOf c) :
    X.hollowFacePerm c = firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ∧
    (∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∉ X.vertexOf c → k = 1 ∨ k = 4) ∧
    X.hollowInv c (X.inv ((X.rot ^ 1) c)) = X.inv ((X.rot ^ 4) c) ∧
    orbitsOn X.facePerm (X.vertexOf c) ⊆
      orbitsOn X.facePerm (univ.filter fun d => d ∉ X.vertexOf c) ∪
        {({e | X.facePerm.SameCycle c e} : Finset H),
          ({e | X.facePerm.SameCycle ((X.rot ^ 3) c) e} : Finset H)} := by
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := hollowSwap_rot_pow_apply hP hc
  obtain ⟨hA, ii, φb, φa, hs, hr⟩ := hollow_aux_facts hP (c := c)
  have φ5 := facePerm_rot_pow_five hP hc
  have φ5' : X.rot (X.inv ((X.rot ^ 5) c)) = (X.rot ^ 1) c := φ5
  have φ1 : X.facePerm (X.inv ((X.rot ^ 1) c)) = (X.rot ^ 2) c := φb 1
  have φ4 : X.facePerm (X.inv ((X.rot ^ 4) c)) = (X.rot ^ 5) c := φb 4
  have s3 : X.rot ((X.rot ^ 3) c) = (X.rot ^ 4) c := hs 3
  have e' : X.inv ((X.rot ^ 2) c) = (X.rot ^ 3) c := by rw [← e, ii]
  have hothers : ∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∉ X.vertexOf c → k = 1 ∨ k = 4 := by
    intro k hk1 hk4 hk
    interval_cases k
    · exact Or.inl rfl
    · exact absurd (e' ▸ hA 3) hk
    · exact absurd (e ▸ hA 2) hk
    · exact Or.inr rfl
  have ι1 : X.hollowInv c (X.inv ((X.rot ^ 1) c)) = X.inv ((X.rot ^ 4) c) := by
    rw [hollowInv_apply_two hP hc h1 (by rw [ii]; exact hA 1) (by rw [ii, v1]; exact h4), ii, v1]
  have ι4 : X.hollowInv c (X.inv ((X.rot ^ 4) c)) = X.inv ((X.rot ^ 1) c) := by
    rw [hollowInv_apply_two hP hc h4 (by rw [ii]; exact hA 4) (by rw [ii, v4]; exact h1), ii, v4]
  have ψ1 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h1⟩ : H) =
      X.rot (X.inv ((X.rot ^ 4) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_three] <;>
      simp only [Set.mem_setOf_eq, not_not, not_false_eq_true, φ1, φa,
        s3, e', hr, hA, h4]
  have ψ4 : (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} ⟨_, h4⟩ : H) =
      X.rot (X.inv ((X.rot ^ 1) c)) := by
    rw [coe_firstReturnPerm, coe_firstReturn_three] <;>
      simp only [Set.mem_setOf_eq, not_not, not_false_eq_true, φ4, φ5, φa,
        hr, hA, h1]
  refine ⟨hollowFacePerm_eq_firstReturn_of hP hc h1 h4 hothers ι1 ι4 ψ1 ψ4, hothers, ι1, ?_⟩
  have hY : ∀ k, X.inv ((X.rot ^ k) c) ∉ X.vertexOf c →
      X.rot (X.inv ((X.rot ^ k) c)) ∈ univ.filter fun d => d ∉ X.vertexOf c := by
    intro k hk
    simp only [mem_filter, mem_univ, true_and]
    rwa [hr]
  have hstep : ∀ d, X.facePerm.SameCycle d (X.facePerm d) := fun d =>
    Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)
  intro o ho
  obtain ⟨d, hd, rfl⟩ := mem_image.1 ho
  obtain ⟨k, hk, rfl⟩ := (hollow_mem_vertexOf_iff hP hc).1 hd
  rw [mem_union, mem_insert, mem_singleton]
  interval_cases k
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inl (orbit_mem_orbitsOn (hY 1 h1) (hstep _))
  · refine Or.inl (orbit_mem_orbitsOn (hY 4 h4) ?_)
    have := (hstep ((X.rot ^ 2) c)).trans (hstep _)
    simp only [φa, e', s3] at this
    exact this
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl (orbit_mem_orbitsOn (hY 4 h4) (hstep _))
  · refine Or.inl (orbit_mem_orbitsOn (hY 1 h1) ?_)
    have := (hstep ((X.rot ^ 5) c)).trans (hstep _)
    simp only [φa, φ5'] at this
    exact this

end EulerExceptional

end TripleData

end ClusterAlgebras

namespace ClusterAlgebras

open Finset Equiv

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

section EulerMain

/-- In the generic case, `ι°(ā₂) = ā₃` and `ι°(ā₄) = ā₁`. -/
theorem hollowInv_generic (hP : X.IsPreTripleDiagram) {c : H} (hc : X.IsHollowMonogon {c})
    (h1 : X.inv ((X.rot ^ 1) c) ∉ X.vertexOf c) (h2 : X.inv ((X.rot ^ 2) c) ∉ X.vertexOf c)
    (h3 : X.inv ((X.rot ^ 3) c) ∉ X.vertexOf c) (h4 : X.inv ((X.rot ^ 4) c) ∉ X.vertexOf c) :
    X.hollowInv c (X.inv ((X.rot ^ 2) c)) = X.inv ((X.rot ^ 3) c) ∧
      X.hollowInv c (X.inv ((X.rot ^ 4) c)) = X.inv ((X.rot ^ 1) c) := by
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := hollowSwap_rot_pow_apply hP hc
  have hA : ∀ k, (X.rot ^ k) c ∈ X.vertexOf c := fun k => X.rot_pow_apply_mem_vertexOf k c
  have ii : ∀ k, X.inv (X.inv ((X.rot ^ k) c)) = (X.rot ^ k) c := fun k => hP.inv_inv_apply _
  constructor
  · rw [hollowInv_apply_two hP hc h2 (by rw [ii]; exact hA 2) (by rw [ii, v2]; exact h3), ii, v2]
  · rw [hollowInv_apply_two hP hc h4 (by rw [ii]; exact hA 4) (by rw [ii, v4]; exact h1), ii, v4]

/-- Reachability in `(H, ι°, σ)` preserves membership in the darts of the removal. -/
theorem mem_hollowDarts_iff_of_reach {c d e : H} (h : (X.hollowRotationSystem c).Reach d e) :
    d ∈ X.hollowDarts c ↔ e ∈ X.hollowDarts c := by
  simp only [mem_hollowDarts]
  exact ⟨fun ⟨b', hb, hb'⟩ => ⟨b', hb, hb'.trans h⟩,
    fun ⟨b', hb, hb'⟩ => ⟨b', hb, hb'.trans h.symm⟩⟩

/-- **Euler's relation for the removal of a hollow monogon.** -/
theorem euler_hollowRemoval (hX : X.IsTripleDiagram) {c : H} (hc : X.IsHollowMonogon {c}) :
    ((X.hollowRemoval hX.toIsPreTripleDiagram c).vertices.card : ℤ) -
      (X.hollowRemoval hX.toIsPreTripleDiagram c).edges.card +
      (X.hollowRemoval hX.toIsPreTripleDiagram c).faceOrbits.card = 2 := by
  have hP := hX.toIsPreTripleDiagram
  obtain ⟨-, -, hx, -, -, -⟩ := hollowMonogon_facts hP hc
  have hOx : ∀ d ∈ X.hollowDarts c, d ∉ X.vertexOf c := fun d hd =>
    notMem_vertexOf_of_mem_hollowDarts hP hc hd
  set Yf : Finset H := univ.filter (fun d => d ∉ X.vertexOf c) with hYf
  set Rf : Finset H := univ.filter (fun d => d ∉ X.vertexOf c ∧ d ∉ X.hollowDarts c) with hRf
  have hYOR : Yf = X.hollowDarts c ∪ Rf := by
    ext d
    simp only [hYf, hRf, mem_filter, mem_univ, true_and, mem_union]
    exact ⟨fun hd => (em (d ∈ X.hollowDarts c)).imp id fun hdO => ⟨hd, hdO⟩,
      fun h => h.elim (hOx d) And.left⟩
  have hOR : Disjoint (X.hollowDarts c) Rf :=
    disjoint_left.2 fun _ hd hd' => (mem_filter.1 hd').2.2 hd
  have hxY : Disjoint (X.vertexOf c) Yf :=
    disjoint_left.2 fun _ hd hd' => (mem_filter.1 hd').2 hd
  have huniv : (univ : Finset H) = X.vertexOf c ∪ Yf := by
    ext d
    simp only [mem_univ, mem_union, hYf, mem_filter, true_and, true_iff]
    exact em _
  -- closure properties
  have hrx : ∀ d, X.rot d ∈ X.vertexOf c ↔ d ∈ X.vertexOf c := fun d =>
    rot_mem_vertexOf_iff (X := X) (c := c)
  have hrY : ∀ d, X.rot d ∈ Yf ↔ d ∈ Yf := by
    intro d
    simp only [hYf, mem_filter, mem_univ, true_and, hrx]
  have hrO := X.rot_mem_hollowDarts_iff c
  have hrR : ∀ d, X.rot d ∈ Rf ↔ d ∈ Rf := by
    intro d
    simp only [hRf, mem_filter, mem_univ, true_and, hrx, hrO]
  have hιx : ∀ d, X.hollowInv c d ∈ X.vertexOf c ↔ d ∈ X.vertexOf c := fun d =>
    hollowInv_mem_iff
  have hιO := X.hollowInv_mem_hollowDarts_iff c
  have hιR : ∀ d, X.hollowInv c d ∈ Rf ↔ d ∈ Rf := by
    intro d
    simp only [hRf, mem_filter, mem_univ, true_and, hιx, hιO]
  have hφR : ∀ d, (X.rot * X.hollowInv c) d ∈ Rf ↔ d ∈ Rf := by
    intro d
    rw [Perm.mul_apply, hrR, hιR]
  have hιinv := hollowInv_involutive hP hc
  have hιne : ∀ d ∈ Yf, X.hollowInv c d ≠ d := fun d hd =>
    hollowInv_ne hP hc (mem_filter.1 hd).2
  -- the counts of the removal
  have hP' := isPreTripleDiagram_hollowRemoval hP hc
  have hV' : (X.hollowRemoval hP c).vertices.card = (orbitsOn X.rot (X.hollowDarts c)).card := by
    rw [RotationSystem.vertices_eq_orbitsOn, ← numOrbits_eq_card_orbitsOn]
    exact numOrbits_subtypePerm_finset (X.rot_mem_hollowDarts_iff c)
  have hE' : (X.hollowRemoval hP c).edges.card =
      (orbitsOn (X.hollowInv c) (X.hollowDarts c)).card := by
    rw [RotationSystem.edges_eq_orbitsOn _ hP'.inv_involutive, ← numOrbits_eq_card_orbitsOn]
    exact numOrbits_subtypePerm_finset (X.hollowInv_mem_hollowDarts_iff c)
  have hF' : (X.hollowRemoval hP c).faceOrbits.card =
      (orbitsOn (X.rot * X.hollowInv c) (X.hollowDarts c)).card := by
    rw [RotationSystem.faceOrbits_eq_orbitsOn, ← numOrbits_eq_card_orbitsOn,
      hollowRemoval_facePerm_eq]
    exact numOrbits_subtypePerm_finset _
  have hbound := (isConnected_hollowRemoval hP hc).euler_le
  rw [hV', hE', hF'] at hbound
  rw [hV', hE', hF']
  -- the counts of `X`
  have hVX : X.vertices.card =
      1 + (orbitsOn X.rot (X.hollowDarts c)).card + (orbitsOn X.rot Rf).card := by
    rw [RotationSystem.vertices_eq_orbitsOn, huniv, card_orbitsOn_union hrY hxY, hYOR,
      card_orbitsOn_union hrR hOR]
    have : orbitsOn X.rot (X.vertexOf c) = {X.vertexOf c} := by
      ext o
      simp only [orbitsOn, mem_image, mem_singleton]
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact X.vertexOf_eq_of_mem hd
      · rintro rfl
        exact ⟨c, X.self_mem_vertexOf c, rfl⟩
    rw [this, card_singleton]
    ring
  have hEX : X.edges.card =
      3 + (orbitsOn (X.hollowInv c) (X.hollowDarts c)).card +
        (orbitsOn (X.hollowInv c) Rf).card := by
    have h1 := two_mul_card_orbitsOn hP.inv_involutive (fun d _ => hP.inv_ne d) (S := univ)
      (fun d => by simp)
    have h2 := two_mul_card_orbitsOn hιinv
      (fun d hd => hιne d (by rw [hYOR]; exact mem_union_left _ hd)) hιO
    have h3 := two_mul_card_orbitsOn hιinv
      (fun d hd => hιne d (by rw [hYOR]; exact mem_union_right _ hd)) hιR
    have h6 : (X.vertexOf c).card = 6 :=
      hP.internalVertex_card _ (X.vertexOf_mem_internalVertices.2 hx)
    have hcard : (univ : Finset H).card = 6 + (X.hollowDarts c).card + Rf.card := by
      rw [huniv, card_union_of_disjoint hxY, hYOR, card_union_of_disjoint hOR, h6]
      ring
    rw [RotationSystem.edges_eq_orbitsOn _ hP.inv_involutive]
    omega
  -- faces
  have hYfilter : (univ.filter fun d => d ∈ ({d | d ∉ X.vertexOf c} : Set H)) = Yf := by
    ext d
    simp [hYf]
  have hPsi : numOrbits (firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c}) =
      (orbitsOn X.facePerm Yf).card := by
    rw [numOrbits_firstReturnPerm_eq, hYfilter]
  have hQ : numOrbits (X.hollowFacePerm c) =
      (orbitsOn (X.rot * X.hollowInv c) (X.hollowDarts c)).card +
        (orbitsOn (X.rot * X.hollowInv c) Rf).card := by
    rw [hollowFacePerm, numOrbits_subtypePerm, hYfilter, hYOR, card_orbitsOn_union hφR hOR]
  have hFbound : ∀ L : Finset (Finset H),
      orbitsOn X.facePerm (X.vertexOf c) ⊆ orbitsOn X.facePerm Yf ∪ L →
      X.faceOrbits.card ≤ (orbitsOn X.facePerm Yf).card + L.card := by
    intro L hL
    rw [RotationSystem.faceOrbits_eq_orbitsOn, huniv, orbitsOn, image_union, ← orbitsOn,
      ← orbitsOn]
    calc (orbitsOn X.facePerm (X.vertexOf c) ∪ orbitsOn X.facePerm Yf).card
        ≤ (orbitsOn X.facePerm Yf ∪ L).card := card_le_card (union_subset hL subset_union_left)
      _ ≤ _ := card_union_le _ _
  have hYf_hYset : ∀ d, d ∈ Yf ↔ d ∉ X.vertexOf c := fun d => by simp [hYf]
  -- the key estimates
  have key : (X.faceOrbits.card : ℤ) - 2 ≤ numOrbits (X.hollowFacePerm c) ∧
      (Rf.Nonempty → (X.faceOrbits.card : ℤ) ≤ numOrbits (X.hollowFacePerm c) ∧
        ((orbitsOn X.rot Rf).card : ℤ) - (orbitsOn (X.hollowInv c) Rf).card +
          (orbitsOn (X.rot * X.hollowInv c) Rf).card ≤ 2) := by
    have hRempty : ∀ {p q : ℕ},
        (∀ k, 1 ≤ k → k ≤ 4 → X.inv ((X.rot ^ k) c) ∉ X.vertexOf c → k = p ∨ k = q) →
        X.hollowInv c (X.inv ((X.rot ^ p) c)) = X.inv ((X.rot ^ q) c) → ¬Rf.Nonempty := by
      intro p q hothers hι ⟨d, hd⟩
      have hd' := mem_filter.1 hd
      exact hd'.2.2 (mem_hollowDarts_of_exceptional hP hc hX hothers hι hd'.2.1)
    have hcard2 : ∀ s t : Finset H, ({s, t} : Finset (Finset H)).card ≤ 2 := fun s t =>
      card_le_two
    rcases hollow_cases hP hc hX with ⟨h1, h2, h3, h4⟩ | ⟨e, h3, h4⟩ | ⟨e, h1, h2⟩ |
      ⟨e, h2, h3⟩ | ⟨e, h1, h4⟩
    · -- the generic case
      have heq := hollowFacePerm_eq_generic hP hc h1 h2 h3 h4
      have hFb := hFbound _ (orbitsOn_vertexOf_subset_generic hP hc h1 h2 h3 h4)
      rw [card_singleton] at hFb
      set ψ := firstReturnPerm X.facePerm {d | d ∉ X.vertexOf c} with hψ
      set p : ({d | d ∉ X.vertexOf c} : Set H) := ⟨_, h3⟩ with hp
      set q : ({d | d ∉ X.vertexOf c} : Set H) := ⟨_, h1⟩ with hq
      have hpq : p ≠ q := by
        intro h
        have := X.inv.injective (congrArg Subtype.val h)
        obtain ⟨-, -, -, -, -, hinj⟩ := hollowMonogon_facts hP hc
        have := hinj 3 1 (by omega) (by omega) this
        omega
      refine ⟨?_, fun hne => ?_⟩
      · rw [heq]
        by_cases hs : ψ.SameCycle p q
        · rw [numOrbits_mul_swap_of_sameCycle ψ hpq hs]
          push_cast
          omega
        · rw [numOrbits_mul_swap_of_not_sameCycle ψ hs]
          omega
      · obtain ⟨ι2, ι4⟩ := hollowInv_generic hP hc h1 h2 h3 h4
        -- every dart outside `x` reaches `ā₁` or `ā₃`
        have hreach : ∀ d, d ∉ X.vertexOf c →
            (X.hollowRotationSystem c).Reach d (X.inv ((X.rot ^ 1) c)) ∨
              (X.hollowRotationSystem c).Reach d (X.inv ((X.rot ^ 3) c)) := by
          intro d hd
          obtain ⟨k, hk1, hk4, -, hr⟩ := hollow_reach_bar hP hc hX hd
          interval_cases k
          · exact Or.inl hr
          · have := hr.inv
            change (X.hollowRotationSystem c).Reach d (X.hollowInv c _) at this
            rw [ι2] at this
            exact Or.inr this
          · exact Or.inr hr
          · have := hr.inv
            change (X.hollowRotationSystem c).Reach d (X.hollowInv c _) at this
            rw [ι4] at this
            exact Or.inl this
        obtain ⟨d, hd⟩ := hne
        obtain ⟨-, hdx, hdO⟩ := mem_filter.1 hd
        obtain ⟨e₀, he₀⟩ := bdry_nonempty_of_pre hX.toIsPreTripleDiagram
        have he₀O : e₀ ∈ X.hollowDarts c := X.mem_hollowDarts_of_mem_bdry he₀
        have he₀x := hOx e₀ he₀O
        -- exactly one of `ā₁`, `ā₃` is a dart of the removal
        have hsplit : (X.inv ((X.rot ^ 1) c) ∈ X.hollowDarts c ∧
              X.inv ((X.rot ^ 3) c) ∉ X.hollowDarts c) ∨
            (X.inv ((X.rot ^ 3) c) ∈ X.hollowDarts c ∧
              X.inv ((X.rot ^ 1) c) ∉ X.hollowDarts c) := by
          rcases hreach d hdx with hr | hr <;> rcases hreach e₀ he₀x with hr' | hr'
          · exact absurd ((mem_hollowDarts_iff_of_reach hr).2
              ((mem_hollowDarts_iff_of_reach hr').1 he₀O)) hdO
          · exact Or.inr ⟨(mem_hollowDarts_iff_of_reach hr').1 he₀O,
              fun h => hdO ((mem_hollowDarts_iff_of_reach hr).2 h)⟩
          · exact Or.inl ⟨(mem_hollowDarts_iff_of_reach hr').1 he₀O,
              fun h => hdO ((mem_hollowDarts_iff_of_reach hr).2 h)⟩
          · exact absurd ((mem_hollowDarts_iff_of_reach hr).2
              ((mem_hollowDarts_iff_of_reach hr').1 he₀O)) hdO
        -- `ā₃` and `ā₁` lie in different orbits of `σ ι°`
        have hns : ¬(X.hollowFacePerm c).SameCycle p q := by
          intro hs
          rw [hollowFacePerm, Perm.sameCycle_subtypePerm] at hs
          obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
          have hr := RotationSystem.reach_pow_apply (X.hollowRotationSystem c)
            (g := X.rot * X.hollowInv c) (fun y => (RotationSystem.Reach.refl y).inv.rot) n
            (X.inv ((X.rot ^ 3) c))
          rw [hn] at hr
          have := mem_hollowDarts_iff_of_reach hr
          rcases hsplit with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact hb (this.2 ha)
          · exact hb (this.1 ha)
        have hψeq : ψ = X.hollowFacePerm c * swap p q := by
          rw [heq, mul_assoc, swap_mul_self, mul_one]
        have hQpos : 0 < numOrbits (X.hollowFacePerm c) := by
          rw [numOrbits_eq_card_image]
          exact card_pos.2 ⟨_, mem_image_of_mem _ (mem_univ p)⟩
        have hnum : numOrbits ψ = numOrbits (X.hollowFacePerm c) - 1 := by
          rw [hψeq, numOrbits_mul_swap_of_not_sameCycle _ hns]
        refine ⟨by omega, ?_⟩
        -- the other component is a connected rotation system
        set a₀ : H := if X.inv ((X.rot ^ 1) c) ∈ X.hollowDarts c then X.inv ((X.rot ^ 3) c)
          else X.inv ((X.rot ^ 1) c) with ha₀
        have ha₀O : a₀ ∉ X.hollowDarts c := by
          rcases hsplit with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · rw [ha₀, if_pos ha]; exact hb
          · rw [ha₀, if_neg hb]; exact hb
        have hRreach : ∀ y ∈ Rf, (X.hollowRotationSystem c).Reach y a₀ := by
          intro y hy
          obtain ⟨-, hyx, hyO⟩ := mem_filter.1 hy
          rcases hsplit with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · rw [ha₀, if_pos ha]
            rcases hreach y hyx with hr | hr
            · exact absurd ((mem_hollowDarts_iff_of_reach hr).2 ha) hyO
            · exact hr
          · rw [ha₀, if_neg hb]
            rcases hreach y hyx with hr | hr
            · exact hr
            · exact absurd ((mem_hollowDarts_iff_of_reach hr).2 ha) hyO
        set R := (X.hollowRotationSystem c).restrict (· ∈ Rf) hιR hrR with hR
        have hRinv : Function.Involutive R.inv := fun y => Subtype.ext (hιinv y)
        have hRconn : R.IsConnected := by
          refine RotationSystem.IsConnected.of_reach ⟨⟨d, hd⟩⟩ hRinv
            (fun y h => hιne y (by rw [hYOR]; exact mem_union_right _ y.2)
              (congrArg Subtype.val h)) fun y z => ?_
          have hyz := (hRreach y y.2).trans (hRreach z z.2).symm
          obtain ⟨_, h'⟩ := RotationSystem.Reach.restrict (R := X.hollowRotationSystem c)
            (R' := R) (fun x => rfl) (fun x => rfl) hyz y.2
          exact h'
        have hRV : R.vertices.card = (orbitsOn X.rot Rf).card := by
          rw [RotationSystem.vertices_eq_orbitsOn, ← numOrbits_eq_card_orbitsOn]
          exact numOrbits_subtypePerm_finset hrR
        have hRE : R.edges.card = (orbitsOn (X.hollowInv c) Rf).card := by
          rw [RotationSystem.edges_eq_orbitsOn _ hRinv, ← numOrbits_eq_card_orbitsOn]
          exact numOrbits_subtypePerm_finset hιR
        have hRF : R.faceOrbits.card = (orbitsOn (X.rot * X.hollowInv c) Rf).card := by
          rw [RotationSystem.faceOrbits_eq_orbitsOn, ← numOrbits_eq_card_orbitsOn]
          have : R.facePerm = (X.rot * X.hollowInv c).subtypePerm hφR := by
            ext y
            rfl
          rw [this]
          exact numOrbits_subtypePerm_finset hφR
        have := hRconn.euler_le
        rwa [hRV, hRE, hRF] at this
    · obtain ⟨heq, hothers, hι, hsub⟩ := hollowFacePerm_eq_firstReturn_e12 hP hc e h3 h4
      have hFb := hFbound _ hsub
      have := hcard2 ({e | X.facePerm.SameCycle c e} : Finset H)
        ({e | X.facePerm.SameCycle ((X.rot ^ 2) c) e} : Finset H)
      refine ⟨?_, fun hne => absurd hne (hRempty hothers hι)⟩
      rw [heq, hPsi]
      omega
    · obtain ⟨heq, hothers, hι, hsub⟩ := hollowFacePerm_eq_firstReturn_e34 hP hc e h1 h2
      have hFb := hFbound _ hsub
      have := hcard2 ({e | X.facePerm.SameCycle c e} : Finset H)
        ({e | X.facePerm.SameCycle ((X.rot ^ 4) c) e} : Finset H)
      refine ⟨?_, fun hne => absurd hne (hRempty hothers hι)⟩
      rw [heq, hPsi]
      omega
    · obtain ⟨heq, hothers, hι, hsub⟩ := hollowFacePerm_eq_firstReturn_e14 hP hc e h2 h3
      have hFb := hFbound _ hsub
      have := hcard2 ({e | X.facePerm.SameCycle c e} : Finset H)
        ({e | X.facePerm.SameCycle ((X.rot ^ 1) c) e} : Finset H)
      refine ⟨?_, fun hne => absurd hne (hRempty hothers hι)⟩
      rw [heq, hPsi]
      omega
    · obtain ⟨heq, hothers, hι, hsub⟩ := hollowFacePerm_eq_firstReturn_e32 hP hc e h1 h4
      have hFb := hFbound _ hsub
      have := hcard2 ({e | X.facePerm.SameCycle c e} : Finset H)
        ({e | X.facePerm.SameCycle ((X.rot ^ 3) c) e} : Finset H)
      refine ⟨?_, fun hne => absurd hne (hRempty hothers hι)⟩
      rw [heq, hPsi]
      omega
  -- conclusion
  obtain ⟨k1, k2⟩ := key
  have heuler := hX.euler
  rw [hVX, hEX] at heuler
  rw [hQ] at k1
  push_cast at heuler hbound k1 ⊢
  by_cases hRne : Rf.Nonempty
  · obtain ⟨k3, k4⟩ := k2 hRne
    rw [hQ] at k3
    push_cast at k3
    linarith
  · have hR0 : Rf = ∅ := not_nonempty_iff_eq_empty.1 hRne
    have h0 : ∀ π : Perm H, (orbitsOn π Rf).card = 0 := fun π => by simp [orbitsOn, hR0]
    simp only [h0, Nat.cast_zero, add_zero] at heuler k1
    linarith

end EulerMain

end TripleData

end ClusterAlgebras

namespace ClusterAlgebras

open Finset Equiv

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

section Strands

variable (hP : X.IsPreTripleDiagram) {c : H} (hc : X.IsHollowMonogon {c})

include hP hc

/-- **One passage through `x`.** A strand arriving at `x` along the reverse of a dart
`s ∈ x \ {c, c̄}` leaves `x` along `μ(s)` after one or two steps, all at `x`. -/
theorem hollow_passage {u : H} (hu : X.inv u ∈ X.vertexOf c) (hu0 : X.inv u ≠ c)
    (hu5 : X.inv u ≠ X.inv c) :
    ∃ j, 1 ≤ j ∧ X.strandMap^[j] u = X.hollowSwap c (X.inv u) ∧
      ∀ l, 1 ≤ l → l ≤ j → X.strandMap^[l] u ∈ X.vertexOf c := by
  obtain ⟨-, -, hx, h5, h6, -⟩ := hollowMonogon_facts hP hc
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := hollowSwap_rot_pow_apply hP hc
  obtain ⟨k, hk, hk'⟩ := (hollow_mem_vertexOf_iff hP hc).1 hu
  have hA : ∀ k, (X.rot ^ k) c ∈ X.vertexOf c := fun k => X.rot_pow_apply_mem_vertexOf k c
  have hS : ∀ w, X.inv w ∈ X.vertexOf c → X.strandMap w = (X.rot ^ 3) (X.inv w) := by
    intro w hw
    have : ¬X.RunsToEndpoint w := by
      change ¬X.IsBoundaryVertex (X.vertexOf (X.inv w))
      rw [X.vertexOf_eq_of_mem hw]
      exact hx
    rw [X.strandMap_of_not_runsToEndpoint this]
    rfl
  have h33 : ∀ k, (X.rot ^ 3) ((X.rot ^ k) c) = (X.rot ^ (k + 3)) c := fun k => by
    rw [← Perm.mul_apply, ← pow_add, add_comm]
  have hmod := hP.rot_pow_mod_six hx
  have t0 : (X.rot ^ 3) ((X.rot ^ 0) c) = (X.rot ^ 3) c := h33 0
  have t1 : (X.rot ^ 3) ((X.rot ^ 1) c) = (X.rot ^ 4) c := h33 1
  have t2 : (X.rot ^ 3) ((X.rot ^ 2) c) = (X.rot ^ 5) c := h33 2
  have t3 : (X.rot ^ 3) ((X.rot ^ 3) c) = (X.rot ^ 0) c := by rw [h33]; exact hmod 6
  have t4 : (X.rot ^ 3) ((X.rot ^ 4) c) = (X.rot ^ 1) c := by rw [h33]; exact hmod 7
  have t5 : (X.rot ^ 3) ((X.rot ^ 5) c) = (X.rot ^ 2) c := by rw [h33]; exact hmod 8
  have i5 : X.inv ((X.rot ^ 5) c) = (X.rot ^ 0) c := by
    rw [h5, hP.inv_inv_apply, pow_zero, Perm.one_apply]
  have i0 : X.inv ((X.rot ^ 0) c) = (X.rot ^ 5) c := by rw [pow_zero, Perm.one_apply, h5]
  interval_cases k
  · exact absurd (by rw [← hk', pow_zero, Perm.one_apply]) hu0
  · refine ⟨1, le_rfl, ?_, fun l hl1 hl2 => ?_⟩
    · rw [Function.iterate_one, hS u hu, ← hk', t1, v1]
    · obtain rfl : l = 1 := by omega
      rw [Function.iterate_one, hS u hu, ← hk', t1]
      exact hA 4
  · refine ⟨2, by omega, ?_, fun l hl1 hl2 => ?_⟩
    · rw [Function.iterate_succ_apply', Function.iterate_one, hS u hu, ← hk', t2,
        hS _ (by rw [i5]; exact hA 0), i5, t0, v2]
    · rcases (show l = 1 ∨ l = 2 by omega) with rfl | rfl
      · rw [Function.iterate_one, hS u hu, ← hk', t2]
        exact hA 5
      · rw [Function.iterate_succ_apply', Function.iterate_one, hS u hu, ← hk', t2,
          hS _ (by rw [i5]; exact hA 0), i5, t0]
        exact hA 3
  · refine ⟨2, by omega, ?_, fun l hl1 hl2 => ?_⟩
    · rw [Function.iterate_succ_apply', Function.iterate_one, hS u hu, ← hk', t3,
        hS _ (by rw [i0]; exact hA 5), i0, t5, v3]
    · rcases (show l = 1 ∨ l = 2 by omega) with rfl | rfl
      · rw [Function.iterate_one, hS u hu, ← hk', t3]
        exact hA 0
      · rw [Function.iterate_succ_apply', Function.iterate_one, hS u hu, ← hk', t3,
          hS _ (by rw [i0]; exact hA 5), i0, t5]
        exact hA 2
  · refine ⟨1, le_rfl, ?_, fun l hl1 hl2 => ?_⟩
    · rw [Function.iterate_one, hS u hu, ← hk', t4, v4]
    · obtain rfl : l = 1 := by omega
      rw [Function.iterate_one, hS u hu, ← hk', t4]
      exact hA 1
  · exact absurd (by rw [← hk', h5]) hu5

/-- **Skipping `x` along a strand.** If `d ∉ x` and `d̄ ∈ x`, the strand from `d` runs through
darts of `x` until a dart `o` with `ō = ι°(d)`. -/
theorem hollow_strand_skip {d : H} (hd : d ∉ X.vertexOf c) (hr : X.inv d ∈ X.vertexOf c) :
    ∃ j, 1 ≤ j ∧ (∀ l, 1 ≤ l → l ≤ j → X.strandMap^[l] d ∈ X.vertexOf c) ∧
      X.inv (X.strandMap^[j] d) = X.hollowInv c d := by
  obtain ⟨-, -, -, h5, -, -⟩ := hollowMonogon_facts hP hc
  obtain ⟨v0, -, -, -, -, v5⟩ := hollowSwap_rot_pow_apply hP hc
  have hμc : X.hollowSwap c c = X.inv c := by simpa [h5] using v0
  have hμc' : X.hollowSwap c (X.inv c) = c := by simpa [h5] using v5
  set g := X.inv * X.hollowSwap c with hg
  set Y : Set H := {d | d ∉ X.vertexOf c} with hY
  set m := firstReturnTime g Y ⟨d, hd⟩ with hm
  have hgd : g d = X.inv d := by
    rw [hg, Perm.mul_apply, hollowSwap_apply_of_notMem hP hc hd]
  have hgs : ∀ s, g s = X.inv (X.hollowSwap c s) := fun s => rfl
  have hι : X.hollowInv c d = (g ^ m) d := by
    rw [hollowInv_apply_of_notMem hd, coe_firstReturn]
  have hm2 : 2 ≤ m := by
    have h1 := firstReturnTime_pos (π := g) (Y := Y) ⟨d, hd⟩
    by_contra hlt
    have hm1 : m = 1 := by omega
    have := pow_firstReturnTime_apply_mem (π := g) (Y := Y) ⟨d, hd⟩
    rw [← hm, hm1, pow_one, hgd] at this
    exact this hr
  have hin : ∀ i, 0 < i → i < m → (g ^ i) d ∈ X.vertexOf c := by
    intro i hi him
    have := pow_apply_notMem_of_lt_firstReturnTime (π := g) (Y := Y) (y := ⟨d, hd⟩) hi him
    simpa [hY] using this
  have key : ∀ i, 1 ≤ i → i ≤ m - 1 → (g ^ i) d ≠ c ∧ (g ^ i) d ≠ X.inv c ∧
      ∃ j, 1 ≤ j ∧ X.strandMap^[j] d = X.hollowSwap c ((g ^ i) d) ∧
        ∀ l, 1 ≤ l → l ≤ j → X.strandMap^[l] d ∈ X.vertexOf c := by
    intro i hi1 him
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [zero_add, pow_one, hgd]
        have hr0 : X.inv d ≠ c := fun h => hd (by
          rw [← hP.inv_inv_apply d, h, ← h5]; exact X.rot_pow_apply_mem_vertexOf _ _)
        have hr5 : X.inv d ≠ X.inv c := fun h => hd (by
          rw [X.inv.injective h]; exact X.self_mem_vertexOf c)
        exact ⟨hr0, hr5, hollow_passage hP hc hr hr0 hr5⟩
      · obtain ⟨hc0, hc5, j, hj, hjS, hjx⟩ := ih hi0 (by omega)
        have hsucc : (g ^ (i + 1)) d = X.inv (X.hollowSwap c ((g ^ i) d)) := by
          rw [pow_succ', Perm.mul_apply, hgs]
        have hmem : (g ^ (i + 1)) d ∈ X.vertexOf c := hin _ (by omega) (by omega)
        have hn0 : (g ^ (i + 1)) d ≠ c := by
          intro h
          rw [hsucc] at h
          have h' : X.hollowSwap c ((g ^ i) d) = X.inv c := by
            have := congrArg X.inv h
            rwa [hP.inv_inv_apply] at this
          apply hc0
          rw [← hollowSwap_hollowSwap hP hc ((g ^ i) d), h', hμc']
        have hn5 : (g ^ (i + 1)) d ≠ X.inv c := by
          intro h
          rw [hsucc] at h
          have h' : X.hollowSwap c ((g ^ i) d) = c := X.inv.injective h
          apply hc5
          rw [← hollowSwap_hollowSwap hP hc ((g ^ i) d), h', hμc]
        obtain ⟨j', hj', hj'S, hj'x⟩ := hollow_passage hP hc
          (u := X.hollowSwap c ((g ^ i) d)) (by rw [← hsucc]; exact hmem)
          (by rw [← hsucc]; exact hn0) (by rw [← hsucc]; exact hn5)
        rw [← hsucc] at hj'S
        refine ⟨hn0, hn5, j' + j, by omega, ?_, fun l hl1 hl2 => ?_⟩
        · rw [Function.iterate_add_apply, hjS, hj'S]
        · rcases le_or_gt l j with h | h
          · exact hjx l hl1 h
          · have := hj'x (l - j) (by omega) (by omega)
            rwa [← hjS, ← Function.iterate_add_apply, show l - j + j = l by omega] at this
  obtain ⟨-, -, j, hj, hjS, hjx⟩ := key (m - 1) (by omega) le_rfl
  refine ⟨j, hj, hjx, ?_⟩
  have hgm : (g ^ m) d = X.inv (X.hollowSwap c ((g ^ (m - 1)) d)) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ', Perm.mul_apply, hgs]
  rw [hι, hgm, hjS]

/-- **The strand map of the removal** skips the darts of `x`: `S°(d) = S^J(d)` for some `J ≥ 1`
with `S^l(d) ∈ x` for `0 < l < J`. -/
theorem coe_strandMap_hollowRemoval (d : X.hollowDarts c) :
    ∃ J, 1 ≤ J ∧ ((X.hollowRemoval hP c).strandMap d : H) = X.strandMap^[J] d ∧
      ∀ l, 1 ≤ l → l < J → X.strandMap^[l] d ∈ X.vertexOf c := by
  have hd := notMem_vertexOf_of_mem_hollowDarts hP hc d.2
  -- both strand maps are `T` applied to the reverse
  set T : H → H := fun e => if X.IsBoundaryVertex (X.vertexOf e) then e else (X.rot ^ 3) e
    with hT
  have hS : ∀ w, X.strandMap w = T (X.inv w) := fun w => rfl
  have hS' : ((X.hollowRemoval hP c).strandMap d : H) = T (X.hollowInv c d) := by
    have hiff := isBoundaryVertex_hollowRemoval_iff hP c ((X.hollowRemoval hP c).inv d)
    simp only [strandMap, RunsToEndpoint, hT]
    by_cases hb : X.IsBoundaryVertex (X.vertexOf (X.hollowInv c d))
    · rw [if_pos (hiff.2 hb), if_pos hb]
      rfl
    · rw [if_neg (fun h => hb (hiff.1 h)), if_neg hb]
      rfl
  by_cases hr : X.inv d ∈ X.vertexOf c
  · obtain ⟨j, hj, hjx, hjι⟩ := hollow_strand_skip hP hc hd hr
    refine ⟨j + 1, by omega, ?_, fun l hl1 hl2 => hjx l hl1 (by omega)⟩
    rw [hS', Function.iterate_succ_apply', hS, hjι]
  · refine ⟨1, le_rfl, ?_, fun l hl1 hl2 => by omega⟩
    rw [hS', Function.iterate_one, hS, hollowInv_apply_of_inv_notMem hP hc hd hr]

/-- The last dart of the arc of the removal from `s_i` runs to the endpoint at which the arc of `X`
from `s_i` ends. -/
theorem hollowInv_last_hollowRemoval (i : Fin b) {n n' : ℕ} (hn : X.arcLength i = n + 1)
    (hn' : (X.hollowRemoval hP c).arcLength i = n' + 1) :
    X.hollowInv c ((X.hollowRemoval hP c).arcDart i n' : H) = X.inv (X.arcDart i n) := by
  obtain ⟨hlast, hnot⟩ := X.arcLength_eq_succ_iff.1 hn
  obtain ⟨hlast', hnot'⟩ := (X.hollowRemoval hP c).arcLength_eq_succ_iff.1 hn'
  have hxb : ∀ w ∈ X.vertexOf c, ¬X.IsBoundaryVertex (X.vertexOf w) := by
    obtain ⟨-, -, hx, -, -, -⟩ := hollowMonogon_facts hP hc
    intro w hw
    rw [X.vertexOf_eq_of_mem hw]
    exact hx
  -- the darts of the arc of `X`
  have hend : ∀ j, j ≤ n + 1 → X.strandMap^[n + 1 - j] (X.arcDart i j) =
      X.inv (X.arcDart i n) := by
    intro j hj
    have : X.strandMap^[n + 1 - j] (X.arcDart i j) = X.strandMap (X.arcDart i n) := by
      rw [arcDart, arcDart, ← Function.iterate_add_apply,
        ← Function.iterate_succ_apply' X.strandMap]
      congr 1
      omega
    rw [this]
    exact X.strandMap_of_runsToEndpoint hlast
  have hendB : X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart i n))) := hlast
  have htrip : ∀ k, 1 ≤ k → k ≤ n → ¬X.IsBoundaryVertex (X.vertexOf (X.arcDart i k)) := by
    intro k hk1 hkn
    have := X.strandStep_arcDart hn (k := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at this
    exact this.not_isBoundaryVertex
  have hiter : ∀ j l, X.strandMap^[l] (X.arcDart i j) = X.arcDart i (l + j) := fun j l => by
    rw [arcDart, arcDart, Function.iterate_add_apply]
  -- the step of the removal
  have hstep : ∀ k, k < n' → ∀ j, j ≤ n →
      (((X.hollowRemoval hP c).arcDart i k : X.hollowDarts c) : H) = X.arcDart i j →
      ∃ j', j' ≤ n ∧ (((X.hollowRemoval hP c).arcDart i (k + 1) : X.hollowDarts c) : H) =
        X.arcDart i j' := by
    intro k hk j hj hkj
    obtain ⟨J, hJ, hJeq, hJx⟩ := coe_strandMap_hollowRemoval hP hc
      ((X.hollowRemoval hP c).arcDart i k)
    rw [hkj] at hJeq hJx
    have hnr := hnot' k hk
    -- the next dart of the removal is at a triple point
    have htr : ¬X.IsBoundaryVertex (X.vertexOf (X.strandMap^[J] (X.arcDart i j))) := by
      rw [← hJeq, (X.hollowRemoval hP c).strandMap_of_not_runsToEndpoint hnr,
        coe_hollowRemoval_rot, coe_hollowRemoval_rot, coe_hollowRemoval_rot, coe_hollowRemoval_inv,
        RotationSystem.vertexOf_rot, RotationSystem.vertexOf_rot, RotationSystem.vertexOf_rot]
      exact fun h => hnr ((isBoundaryVertex_hollowRemoval_iff hP c _).2 h)
    refine ⟨J + j, ?_, by rw [(X.hollowRemoval hP c).arcDart_succ, hJeq, hiter]⟩
    by_contra hgt
    rcases (show n + 1 - j < J ∨ n + 1 - j = J by omega) with hlt | heq
    · have := hJx (n + 1 - j) (by omega) hlt
      rw [hend j (by omega)] at this
      exact hxb _ this hendB
    · rw [← heq, hend j (by omega)] at htr
      exact htr hendB
  have hcorr : ∀ k, k ≤ n' → ∃ j, j ≤ n ∧
      (((X.hollowRemoval hP c).arcDart i k : X.hollowDarts c) : H) = X.arcDart i j := by
    intro k hk
    induction k with
    | zero => exact ⟨0, by omega, rfl⟩
    | succ k ih =>
      obtain ⟨j, hj, hkj⟩ := ih (by omega)
      exact hstep k (by omega) j hj hkj
  obtain ⟨j, hj, hkj⟩ := hcorr n' le_rfl
  obtain ⟨J, hJ, hJeq, hJx⟩ := coe_strandMap_hollowRemoval hP hc
    ((X.hollowRemoval hP c).arcDart i n')
  rw [hkj] at hJeq hJx
  have hval : (((X.hollowRemoval hP c).strandMap ((X.hollowRemoval hP c).arcDart i n') :
      X.hollowDarts c) : H) = X.hollowInv c ((X.hollowRemoval hP c).arcDart i n') := by
    rw [(X.hollowRemoval hP c).strandMap_of_runsToEndpoint hlast', coe_hollowRemoval_inv]
  have hbd : X.IsBoundaryVertex (X.vertexOf (X.hollowInv c
      ((X.hollowRemoval hP c).arcDart i n'))) :=
    (isBoundaryVertex_hollowRemoval_iff hP c _).1 hlast'
  rw [← hval, hJeq] at hbd ⊢
  -- `J + j = n + 1`
  rcases lt_trichotomy (J + j) (n + 1) with hlt | heq | hgt
  · rw [hiter] at hbd
    exact absurd hbd (htrip _ (by omega) (by omega))
  · have := hend j (by omega)
    rwa [show n + 1 - j = J by omega] at this
  · have := hJx (n + 1 - j) (by omega) (by omega)
    rw [hend j (by omega)] at this
    exact absurd hendB (hxb _ this)

/-- **The removal has the strand permutation of `X`**. -/
theorem strandPerm_hollowRemoval : (X.hollowRemoval hP c).strandPerm = X.strandPerm := by
  set X' := X.hollowRemoval hP c with hX'
  have hP' : X'.IsPreTripleDiagram := isPreTripleDiagram_hollowRemoval hP hc
  funext i
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (hP.arcLength_ne_zero i)
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (hP'.arcLength_ne_zero i)
  have h1 : X.arcLastIndex i = some n := X.arcLastIndex_eq_some_iff.2 (X.arcLength_eq_succ_iff.1 hn)
  have h2 : X'.arcLastIndex i = some n' :=
    X'.arcLastIndex_eq_some_iff.2 (X'.arcLength_eq_succ_iff.1 hn')
  have hlast := hollowInv_last_hollowRemoval hP hc i hn hn'
  simp only [strandPerm, h1, h2]
  congr 1
  unfold findTarget
  congr 1
  funext j
  apply decide_eq_decide.2
  rw [← (Finset.map_injective (Function.Embedding.subtype (· ∈ X.hollowDarts c))).eq_iff]
  rw [target, map_hollowRemoval_endpoint, map_hollowRemoval_vertexOf, coe_hollowRemoval_inv,
    hlast]
  rfl

/-- **The removal has fewer triple points than `X`.** -/
theorem card_internalVertices_hollowRemoval_lt :
    (X.hollowRemoval hP c).internalVertices.card < X.internalVertices.card := by
  obtain ⟨-, -, hx, -, -, -⟩ := hollowMonogon_facts hP hc
  have hxmem : X.vertexOf c ∈ X.internalVertices := X.vertexOf_mem_internalVertices.2 hx
  calc (X.hollowRemoval hP c).internalVertices.card
      ≤ (X.internalVertices.erase (X.vertexOf c)).card := by
        refine card_le_card_of_injOn (Finset.map (Function.Embedding.subtype _)) ?_ ?_
        · intro v hv
          rw [Finset.mem_coe] at hv ⊢
          obtain ⟨hvV, hvB⟩ := (X.hollowRemoval hP c).mem_internalVertices.1 hv
          obtain ⟨d, rfl⟩ := (X.hollowRemoval hP c).mem_vertices.1 hvV
          rw [isBoundaryVertex_hollowRemoval_iff] at hvB
          rw [map_hollowRemoval_vertexOf]
          exact mem_erase.2 ⟨fun h => notMem_vertexOf_of_mem_hollowDarts hP hc d.2
            ((X.mem_vertexOf_iff_vertexOf_eq).2 h), X.vertexOf_mem_internalVertices.2 hvB⟩
        · exact fun v _ w _ h => Finset.map_injective _ h
    _ < X.internalVertices.card := card_erase_lt_of_mem hxmem

end Strands

/-- The removal of a hollow monogon of a triple diagram is a triple diagram. -/
@[cluster_algebras "lem_hollow_removal"]
theorem isTripleDiagram_hollowRemoval (hX : X.IsTripleDiagram) {c : H}
    (hc : X.IsHollowMonogon {c}) :
    (X.hollowRemoval hX.toIsPreTripleDiagram c).IsTripleDiagram :=
  (isPreTripleDiagram_hollowRemoval hX.toIsPreTripleDiagram hc).isTripleDiagram
    (isConnected_hollowRemoval hX.toIsPreTripleDiagram hc).transitive
    (euler_hollowRemoval hX hc)

/-- The removal of a hollow monogon of a triple diagram `X` has the strand permutation of `X`. -/
@[cluster_algebras "lem_hollow_removal"]
theorem strandPerm_hollowRemoval' (hX : X.IsTripleDiagram) {c : H}
    (hc : X.IsHollowMonogon {c}) :
    (X.hollowRemoval hX.toIsPreTripleDiagram c).strandPerm = X.strandPerm :=
  strandPerm_hollowRemoval hX.toIsPreTripleDiagram hc

/-- The removal of a hollow monogon of a triple diagram `X` has fewer triple points than `X`. -/
@[cluster_algebras "lem_hollow_removal"]
theorem card_internalVertices_hollowRemoval_lt' (hX : X.IsTripleDiagram) {c : H}
    (hc : X.IsHollowMonogon {c}) :
    (X.hollowRemoval hX.toIsPreTripleDiagram c).internalVertices.card <
      X.internalVertices.card :=
  card_internalVertices_hollowRemoval_lt hX.toIsPreTripleDiagram hc

end TripleData

namespace TripleDiagram

variable {b : ℕ}

/-- A triple diagram with a hollow monogon is not minimal. -/
@[cluster_algebras "lem_hollow_not_minimal"]
theorem not_isMinimal_of_isHollowMonogon (X : TripleDiagram b) {c : X.Dart}
    (hc : X.data.IsHollowMonogon {c}) : ¬X.IsMinimal := by
  intro hmin
  let X' : TripleDiagram b :=
    ⟨X.data.hollowDarts c, X.data.hollowRemoval X.isTripleDiagram.toIsPreTripleDiagram c,
      TripleData.isTripleDiagram_hollowRemoval X.isTripleDiagram hc⟩
  have h := hmin X' (TripleData.strandPerm_hollowRemoval' X.isTripleDiagram hc)
  have h' := TripleData.card_internalVertices_hollowRemoval_lt' X.isTripleDiagram hc
  exact absurd h (not_le.2 h')

end TripleDiagram

end ClusterAlgebras

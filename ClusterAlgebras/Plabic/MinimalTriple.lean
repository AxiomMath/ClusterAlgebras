/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.TripleDiagram

/-!
# Minimal triple diagrams: strand paths and bad features

A triple diagram `X` with `b` arcs is *minimal* if no triple diagram with `b` arcs and the same
strand permutation has fewer triple points. D. Thurston's theory of minimal triple diagrams
detects non-minimality through *bad features*, which are described here through *strand paths*:
a strand path `(e₁, …, e_m)` is a stretch of consecutive `out` darts of one strand, traversed in
its direction, with `e_{j+1} = σ³(ē_j)` at the triple point `v(ē_j)`.

* A *monogon* is a strand path running from a triple point `x` back to `x` along a different pass;
  a *hollow monogon* is an internal face of one dart.
* A *parallel digon* is a pair of strand paths running from `x` to `y ≠ x` with different first
  and different last darts; an *anti-parallel digon* is a pair of dart-disjoint strand paths, one
  from `x` to `y` and one from `y` to `x`. A *badgon* is a monogon or a parallel digon.
* A strand path is *simple* if its interior points are distinct from each other and from its two
  ends; its *right* and *left lists* record the darts on either side of it. A *returning path*
  leaves a simple strand path on one side and comes back to it on the same side, and it *hugs* it
  if the strands leaving the path between them run directly to the returning path.
* A triple diagram is *monogon-stable* if no triple diagram move-equivalent to it has a monogon.

## Main definitions

* `ClusterAlgebras.TripleDiagram.IsMinimal`: minimal triple diagrams.
* `ClusterAlgebras.TripleData.IsStrandPath`, `TripleData.pathStart`, `TripleData.pathEnd`,
  `TripleData.interiorPoints`: strand paths.
* `ClusterAlgebras.TripleData.IsMonogon`: monogons.
* `ClusterAlgebras.TripleData.IsParallelDigon`, `TripleData.IsAntiParallelDigon`: parallel and
  anti-parallel digons.
* `ClusterAlgebras.TripleData.HasBadgon`: having a badgon.
* `ClusterAlgebras.DiskMap.IsHollowMonogon`: hollow monogons.
* `ClusterAlgebras.TripleData.IsSimpleStrandPath`, `TripleData.sideDarts`,
  `TripleData.sideList`: simple strand paths and their sides.
* `ClusterAlgebras.TripleData.IsReturningPath`: returning paths.
* `ClusterAlgebras.TripleData.Hugs`: hugging.
* `ClusterAlgebras.TripleDiagram.IsMonogonStable`: monogon-stable triple diagrams.

## Main results

* `ClusterAlgebras.TripleData.isMonogon_of_two_passes`: two passes of one strand give a monogon.
* `ClusterAlgebras.TripleData.isMonogon_of_isHollowMonogon`: a hollow monogon is a monogon.
* `ClusterAlgebras.TripleData.isStrandPath_of_isChain`,
  `ClusterAlgebras.TripleData.isStrandPath_reverse_map_inv_of_isChain`: walks along strands.
* `ClusterAlgebras.TripleData.nodup_interiorPoints_arc`: the triple points of an arc of a
  monogon-free diagram are distinct.
* `ClusterAlgebras.TripleData.isHollowMonogon_of_isMonogon_singleton`: a monogon of length one is
  hollow.
* `ClusterAlgebras.TripleData.mem_arc_or_forall_strandOrbit`: every `out` dart lies on an arc or on
  a closed strand of `out` darts.
* `ClusterAlgebras.TripleData.IsClosedStrand.image_inv`: reversing a closed strand.

## Implementation notes

* **Sequences.** Strand paths are lists of darts. The vertex a path runs from, `v(e₁)`, and the
  vertex it runs to, `v(ē_m)`, are `pathStart` and `pathEnd`; their value on the empty list, `∅`,
  is irrelevant since strand paths are nonempty. The first and last darts are read through
  `List.head?` and `List.getLast?`.
* **Indices.** Positions in lists are `0`-indexed. The interior points `z₁, …, z_{m-1}` of a
  strand path `P` are the list `interiorPoints P`, so that FWZ's `z_l` is
  `(interiorPoints P)[l - 1] = v(P[l - 1]̄)`. Accordingly, a returning path *from `z_{a+1}` to
  `z_{b+1}`* is `IsReturningPath P ζ Q a b` with `0`-indexed `a, b`; it is parallel if `a < b` and
  anti-parallel if `b < a`, as in FWZ.
* **Sides.** The two sides `right` and `left` form the type `StrandSide`, with the sign
  `StrandSide.sign` (`1` for right, `-1` for left) of the definition of hugging.
* **Hypotheses.** The lemmas are stated for pre-triple diagrams: none of them uses connectedness
  or Euler's relation.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Sides -/

/-- The two **sides** `ζ ∈ {right, left}` of a strand path. -/
@[cluster_algebras "def_simple_strand_path"]
inductive StrandSide : Type
  /-- The right side. -/
  | right
  /-- The left side. -/
  | left
  deriving DecidableEq, Fintype, Inhabited

namespace StrandSide

/-- The **sign** `s` of a side: `1` for the right side and `-1` for the left side. -/
@[cluster_algebras "def_hugging"]
def sign : StrandSide → ℤ
  | right => 1
  | left => -1

/-- The right side has sign `1`. -/
@[simp]
theorem sign_right : right.sign = 1 := rfl

/-- The left side has sign `-1`. -/
@[simp]
theorem sign_left : left.sign = -1 := rfl

end StrandSide

/-! ### Minimal triple diagrams -/

namespace TripleDiagram

variable {b : ℕ}

/-- A triple diagram `X` with `b` arcs is **minimal** if every triple diagram `X'` with `b`
arcs and `π_{X'} = π_X` has at least as many triple points as `X`. -/
@[cluster_algebras "def_minimal_triple_diagram"]
def IsMinimal (X : TripleDiagram b) : Prop :=
  ∀ X' : TripleDiagram b, X'.data.strandPerm = X.data.strandPerm →
    X.data.internalVertices.card ≤ X'.data.internalVertices.card

end TripleDiagram

/-! ### Hollow monogons -/

namespace DiskMap

variable {H : Type*} [Fintype H] [DecidableEq H] (M : DiskMap H)

/-- A **hollow monogon**: an internal face consisting of exactly one dart. -/
@[cluster_algebras "def_hollow_monogon"]
def IsHollowMonogon (f : Finset H) : Prop := f ∈ M.internalFaces ∧ f.card = 1

/-- Being a hollow monogon is decidable. -/
instance : DecidablePred M.IsHollowMonogon := fun _ => by
  unfold IsHollowMonogon
  infer_instance

/-- A dart `d ∉ B` fixed by `φ` is a hollow monogon `{d}`. -/
theorem isHollowMonogon_singleton {d : H} (hd : d ∉ M.bdry) (hφ : M.facePerm d = d) :
    M.IsHollowMonogon {d} := by
  have hf : M.faceOf d = {d} := by
    ext x
    simp only [mem_singleton]
    exact ⟨fun hx => ((M.mem_faceOf.1 hx).eq_of_left hφ).symm, fun hx => hx ▸ M.self_mem_faceOf d⟩
  refine ⟨M.mem_internalFaces.2 ⟨hf ▸ M.faceOf_mem_faces hd, disjoint_singleton_left.2 hd⟩,
    card_singleton d⟩

variable {M} in
/-- A hollow monogon `{c}` consists of a dart `c ∉ B` fixed by `φ`. -/
theorem IsHollowMonogon.facePerm_eq {c : H} (hc : M.IsHollowMonogon {c}) :
    c ∉ M.bdry ∧ M.facePerm c = c := by
  obtain ⟨hf, hB⟩ := M.mem_internalFaces.1 hc.1
  refine ⟨disjoint_singleton_left.1 hB, ?_⟩
  obtain ⟨d, hd⟩ := M.mem_faceOrbits.1 (M.mem_faces.1 hf).2
  have hcd : M.faceOf c = {c} := by
    rw [← hd]
    exact M.faceOf_eq_of_mem (hd ▸ mem_singleton_self c)
  have := M.facePerm_mem_faceOf c
  rwa [hcd, mem_singleton] at this

end DiskMap

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)

/-! ### Triple points -/

omit [Fintype H] [DecidableEq H] in
/-- `σ³ d = σ (σ (σ d))`. -/
theorem rot_pow_three_apply (d : H) : (X.rot ^ 3) d = X.rot (X.rot (X.rot d)) := rfl

/-- The darts `σⁿ(d)` lie at the vertex of `d`. -/
theorem vertexOf_rot_pow_apply (n : ℕ) (d : H) : X.vertexOf ((X.rot ^ n) d) = X.vertexOf d :=
  X.vertexOf_eq_of_mem (X.mem_vertexOf.2 (Equiv.Perm.sameCycle_pow_right.2
    (Equiv.Perm.SameCycle.refl _ _)))

/-- A dart at a triple point is not in `B`. -/
theorem notMem_bdry_of_not_isBoundaryVertex {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) :
    d ∉ X.bdry := fun h => hd (X.isBoundaryVertex_vertexOf_of_mem h)

namespace IsPreTripleDiagram

variable {X} (hX : X.IsPreTripleDiagram)

include hX

/-- The map `d ↦ d̄` is an involution. -/
theorem inv_inv_apply (d : H) : X.inv (X.inv d) = d := hX.inv_involutive d

/-- The reverse of a dart not in `B` is not in `B`. -/
theorem inv_notMem_bdry {d : H} (hd : d ∉ X.bdry) : X.inv d ∉ X.bdry := fun h =>
  hd (by simpa [hX.inv_inv_apply d] using hX.inv_mem_bdry _ h)

/-- At a triple point, `σ⁶ d = d` and `d, σ d, …, σ⁵ d` are distinct. -/
theorem rot_pow_six {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) :
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

/-- At a triple point, `σ⁶ d = d`. -/
theorem rot_pow_six_apply {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) :
    (X.rot ^ 6) d = d :=
  (hX.rot_pow_six hd).1

/-- At a triple point, `σⁿ d = σ^(n % 6) d`. -/
theorem rot_pow_mod_six {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) (n : ℕ) :
    (X.rot ^ n) d = (X.rot ^ (n % 6)) d := by
  conv_lhs => rw [← Nat.mod_add_div n 6, pow_add, pow_mul, Equiv.Perm.mul_apply,
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (hX.rot_pow_six_apply hd) (n / 6)]

/-- `σ³ σ³ d = d` at a triple point. -/
theorem rot_pow_three_rot_pow_three {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) :
    (X.rot ^ 3) ((X.rot ^ 3) d) = d := by
  rw [← Equiv.Perm.mul_apply, ← pow_add]
  exact hX.rot_pow_six_apply hd

/-- The orientation alternates around a triple point. -/
theorem isOut_rot_apply {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) :
    X.isOut (X.rot d) = !X.isOut d := by
  have := hX.isOut_rot d hd
  revert this
  cases X.isOut (X.rot d) <;> cases X.isOut d <;> simp

/-- The orientation is reversed by `d ↦ d̄` off `B`. -/
theorem isOut_inv_apply {d : H} (hd : d ∉ X.bdry) : X.isOut (X.inv d) = !X.isOut d := by
  have := hX.isOut_inv d hd
  revert this
  cases X.isOut (X.inv d) <;> cases X.isOut d <;> simp

/-- At a triple point, `σⁿ` preserves the orientation for even `n` and reverses it for odd `n`. -/
theorem isOut_rot_pow_apply {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) (n : ℕ) :
    X.isOut ((X.rot ^ n) d) = if Even n then X.isOut d else !X.isOut d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply,
      hX.isOut_rot_apply (by rwa [X.vertexOf_rot_pow_apply]), ih]
    by_cases h : Even n <;> simp [h, Nat.even_add_one]

/-- At a triple point, `σ³` reverses the orientation. -/
theorem isOut_rot_pow_three_apply {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) :
    X.isOut ((X.rot ^ 3) d) = !X.isOut d := by
  rw [hX.isOut_rot_pow_apply hd, if_neg (by decide)]

end IsPreTripleDiagram

/-! ### Strand paths -/

/-- Two consecutive darts `e, e'` of a strand path: `v(ē)` is a triple point and `e' = σ³(ē)`. -/
@[cluster_algebras "def_strand_path"]
def StrandStep (e e' : H) : Prop := ¬X.RunsToEndpoint e ∧ e' = (X.rot ^ 3) (X.inv e)

/-- Being a step of a strand path is decidable. -/
instance : DecidableRel X.StrandStep := fun _ _ => by
  unfold StrandStep
  infer_instance

/-- A **strand path**: a nonempty sequence `(e₁, …, e_m)` of darts not in `B` with `o(e_j) = out`
for all `j`, such that `v(ē_j)` is a triple point and `e_{j+1} = σ³(ē_j)` for every
`j ∈ [1, m - 1]`. It runs from `pathStart P = v(e₁)` to `pathEnd P = v(ē_m)`, leaves along `e₁`,
arrives along `e_m`, and its interior points are `interiorPoints P`. -/
@[cluster_algebras "def_strand_path"]
structure IsStrandPath (P : List H) : Prop where
  /-- A strand path has at least one dart. -/
  ne_nil : P ≠ []
  /-- No dart of a strand path is in `B`. -/
  notMem_bdry : ∀ e ∈ P, e ∉ X.bdry
  /-- Every dart of a strand path is `out`. -/
  isOut_eq_true : ∀ e ∈ P, X.isOut e = true
  /-- Consecutive darts `e_j, e_{j+1}` satisfy `e_{j+1} = σ³(ē_j)` at the triple point `v(ē_j)`. -/
  isChain : P.IsChain X.StrandStep

/-- The vertex `v(e₁)` a strand path `(e₁, …, e_m)` **runs from**; `∅` for the empty sequence. -/
@[cluster_algebras "def_strand_path"]
def pathStart (P : List H) : Finset H := (P.head?.map X.vertexOf).getD ∅

/-- The vertex `v(ē_m)` a strand path `(e₁, …, e_m)` **runs to**; `∅` for the empty sequence. -/
@[cluster_algebras "def_strand_path"]
def pathEnd (P : List H) : Finset H := (P.getLast?.map fun e => X.vertexOf (X.inv e)).getD ∅

/-- The **interior points** `z_l = v(ē_l)`, `l ∈ [1, m - 1]`, of a strand path `(e₁, …, e_m)`,
as a list: `z_l` is the entry of index `l - 1`. -/
@[cluster_algebras "def_strand_path"]
def interiorPoints (P : List H) : List (Finset H) := P.dropLast.map fun e => X.vertexOf (X.inv e)

/-- The conditions defining a strand path. -/
theorem isStrandPath_iff {P : List H} :
    X.IsStrandPath P ↔ P ≠ [] ∧ (∀ e ∈ P, e ∉ X.bdry) ∧ (∀ e ∈ P, X.isOut e = true) ∧
      P.IsChain X.StrandStep :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

/-- Being a strand path is decidable. -/
instance : DecidablePred X.IsStrandPath := fun _ => decidable_of_iff _ X.isStrandPath_iff.symm

/-- The conditions of a strand path, read position by position. -/
theorem isStrandPath_iff_getElem {P : List H} :
    X.IsStrandPath P ↔ P ≠ [] ∧
      (∀ (t : ℕ) (ht : t < P.length), P[t] ∉ X.bdry ∧ X.isOut P[t] = true) ∧
      ∀ (t : ℕ) (ht : t + 1 < P.length), X.StrandStep P[t] P[t + 1] := by
  rw [isStrandPath_iff, List.isChain_iff_getElem]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, fun t ht => ⟨h₂ _ (List.getElem_mem ht), h₃ _ (List.getElem_mem ht)⟩, h₄⟩
  · rintro ⟨h₁, h₂, h₄⟩
    refine ⟨h₁, fun e he => ?_, fun e he => ?_, h₄⟩ <;>
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
    exacts [(h₂ t ht).1, (h₂ t ht).2]

/-- The sequence `(e, …)` runs from `v(e)`. -/
@[simp]
theorem pathStart_cons (e : H) (P : List H) : X.pathStart (e :: P) = X.vertexOf e := rfl

/-- A sequence with first dart `e` runs from `v(e)`. -/
theorem pathStart_of_head? {P : List H} {e : H} (h : P.head? = some e) :
    X.pathStart P = X.vertexOf e := by
  simp [pathStart, h]

/-- A sequence with last dart `e` runs to `v(ē)`. -/
theorem pathEnd_of_getLast? {P : List H} {e : H} (h : P.getLast? = some e) :
    X.pathEnd P = X.vertexOf (X.inv e) := by
  simp [pathEnd, h]

/-- The sequence `(e)` runs to `v(ē)`. -/
@[simp]
theorem pathEnd_singleton (e : H) : X.pathEnd [e] = X.vertexOf (X.inv e) := rfl

/-- The vertex of the dart after a step is the vertex of the reverse of the dart before it. -/
theorem StrandStep.vertexOf_eq {X : TripleData H b} {e e' : H} (h : X.StrandStep e e') :
    X.vertexOf e' = X.vertexOf (X.inv e) := by
  rw [h.2, X.vertexOf_rot_pow_apply]

/-- The dart after a step lies at a triple point. -/
theorem StrandStep.not_isBoundaryVertex {X : TripleData H b} {e e' : H} (h : X.StrandStep e e') :
    ¬X.IsBoundaryVertex (X.vertexOf e') := by
  rw [h.vertexOf_eq]
  exact h.1

/-- The dart after a step is not in `B`. -/
theorem StrandStep.notMem_bdry {X : TripleData H b} {e e' : H} (h : X.StrandStep e e') :
    e' ∉ X.bdry :=
  X.notMem_bdry_of_not_isBoundaryVertex h.not_isBoundaryVertex

/-- A step of a strand path is a step of the strand map. -/
theorem StrandStep.strandMap_eq {X : TripleData H b} {e e' : H} (h : X.StrandStep e e') :
    X.strandMap e = e' := by
  rw [X.strandMap_of_not_runsToEndpoint h.1, h.2]
  rfl

/-- A step of a strand path preserves the orientation. -/
theorem StrandStep.isOut_eq {X : TripleData H b} (hX : X.IsPreTripleDiagram) {e e' : H}
    (h : X.StrandStep e e') (he : e ∉ X.bdry) : X.isOut e' = X.isOut e := by
  rw [h.2, hX.isOut_rot_pow_three_apply h.1, hX.isOut_inv_apply he, Bool.not_not]

/-! ### Monogons, digons and badgons -/

/-- A **monogon**: a strand path `(e₁, …, e_m)` running from a triple point `x` to the same triple
point `x` with `ē_m ≠ σ³(e₁)`; its vertex is `pathStart P = x`. -/
@[cluster_algebras "def_monogon"]
structure IsMonogon (P : List H) : Prop where
  /-- A monogon is a strand path. -/
  isStrandPath : X.IsStrandPath P
  /-- It runs from a triple point. -/
  pathStart_mem : X.pathStart P ∈ X.internalVertices
  /-- It runs back to the same triple point. -/
  pathEnd_eq : X.pathEnd P = X.pathStart P
  /-- It comes back along a different pass: `ē_m ≠ σ³(e₁)`. -/
  inv_ne : ∀ e₁ ∈ P.head?, ∀ eₘ ∈ P.getLast?, X.inv eₘ ≠ (X.rot ^ 3) e₁

/-- The conditions defining a monogon. -/
theorem isMonogon_iff {P : List H} :
    X.IsMonogon P ↔ X.IsStrandPath P ∧ X.pathStart P ∈ X.internalVertices ∧
      X.pathEnd P = X.pathStart P ∧
      ∀ e₁ ∈ P.head?, ∀ eₘ ∈ P.getLast?, X.inv eₘ ≠ (X.rot ^ 3) e₁ :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

/-- Being a monogon is decidable. -/
instance : DecidablePred X.IsMonogon := fun _ => decidable_of_iff _ X.isMonogon_iff.symm

/-- The triple diagram **has a monogon**. -/
@[cluster_algebras "def_badgon"]
def HasMonogon : Prop := ∃ P, X.IsMonogon P

/-- A **parallel digon** with corners `x ≠ y`: strand paths `P = (e₁, …, e_m)` and
`Q = (f₁, …, f_n)` both running from the triple point `x` to the triple point `y`, with `e₁ ≠ f₁`
and `e_m ≠ f_n`. -/
@[cluster_algebras "def_parallel_digon"]
structure IsParallelDigon (P Q : List H) (x y : Finset H) : Prop where
  /-- The corners are distinct. -/
  ne : x ≠ y
  /-- The corner `x` is a triple point. -/
  mem_left : x ∈ X.internalVertices
  /-- The corner `y` is a triple point. -/
  mem_right : y ∈ X.internalVertices
  /-- `P` is a strand path. -/
  isStrandPath_fst : X.IsStrandPath P
  /-- `Q` is a strand path. -/
  isStrandPath_snd : X.IsStrandPath Q
  /-- `P` runs from `x`. -/
  pathStart_fst : X.pathStart P = x
  /-- `P` runs to `y`. -/
  pathEnd_fst : X.pathEnd P = y
  /-- `Q` runs from `x`. -/
  pathStart_snd : X.pathStart Q = x
  /-- `Q` runs to `y`. -/
  pathEnd_snd : X.pathEnd Q = y
  /-- `e₁ ≠ f₁`. -/
  head?_ne : P.head? ≠ Q.head?
  /-- `e_m ≠ f_n`. -/
  getLast?_ne : P.getLast? ≠ Q.getLast?

/-- An **anti-parallel digon** with corners `x ≠ y`: strand paths `P` running from the triple
point `x` to the triple point `y` and `Q` running from `y` to `x`, with no dart in common. -/
@[cluster_algebras "def_parallel_digon"]
structure IsAntiParallelDigon (P Q : List H) (x y : Finset H) : Prop where
  /-- The corners are distinct. -/
  ne : x ≠ y
  /-- The corner `x` is a triple point. -/
  mem_left : x ∈ X.internalVertices
  /-- The corner `y` is a triple point. -/
  mem_right : y ∈ X.internalVertices
  /-- `P` is a strand path. -/
  isStrandPath_fst : X.IsStrandPath P
  /-- `Q` is a strand path. -/
  isStrandPath_snd : X.IsStrandPath Q
  /-- `P` runs from `x`. -/
  pathStart_fst : X.pathStart P = x
  /-- `P` runs to `y`. -/
  pathEnd_fst : X.pathEnd P = y
  /-- `Q` runs from `y`. -/
  pathStart_snd : X.pathStart Q = y
  /-- `Q` runs to `x`. -/
  pathEnd_snd : X.pathEnd Q = x
  /-- No dart of `P` is a dart of `Q`. -/
  disjoint : P.Disjoint Q

/-- The triple diagram **has a parallel digon**. -/
@[cluster_algebras "def_badgon"]
def HasParallelDigon : Prop := ∃ P Q x y, X.IsParallelDigon P Q x y

/-- A triple diagram **has a badgon**, a badgon being a monogon or a parallel digon. -/
@[cluster_algebras "def_badgon"]
def HasBadgon : Prop := X.HasMonogon ∨ X.HasParallelDigon

/-! ### Simple strand paths, returning paths and hugging -/

/-- A strand path `(e₁, …, e_m)` is **simple** if its interior points `z_l = v(ē_l)`,
`l ∈ [1, m - 1]`, are pairwise distinct and differ from `v(e₁)` and `v(ē_m)`. -/
@[cluster_algebras "def_simple_strand_path"]
structure IsSimpleStrandPath (P : List H) : Prop where
  /-- A simple strand path is a strand path. -/
  isStrandPath : X.IsStrandPath P
  /-- The interior points are pairwise distinct. -/
  nodup : (X.interiorPoints P).Nodup
  /-- `v(e₁)` is not an interior point. -/
  pathStart_notMem : X.pathStart P ∉ X.interiorPoints P
  /-- `v(ē_m)` is not an interior point. -/
  pathEnd_notMem : X.pathEnd P ∉ X.interiorPoints P

/-- The conditions defining a simple strand path. -/
theorem isSimpleStrandPath_iff {P : List H} :
    X.IsSimpleStrandPath P ↔ X.IsStrandPath P ∧ (X.interiorPoints P).Nodup ∧
      X.pathStart P ∉ X.interiorPoints P ∧ X.pathEnd P ∉ X.interiorPoints P :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

/-- Being a simple strand path is decidable. -/
instance : DecidablePred X.IsSimpleStrandPath := fun _ =>
  decidable_of_iff _ X.isSimpleStrandPath_iff.symm

/-- The darts on side `ζ` of a strand path at the interior point `v(ē)`, where `e` is a dart of the
path other than the last: the **right darts** `σ ē, σ² ē` and the **left darts** `σ⁴ ē, σ⁵ ē`,
in this order. -/
@[cluster_algebras "def_simple_strand_path"]
def sideDarts : StrandSide → H → List H
  | .right, e => [X.rot (X.inv e), (X.rot ^ 2) (X.inv e)]
  | .left, e => [(X.rot ^ 4) (X.inv e), (X.rot ^ 5) (X.inv e)]

/-- The **`ζ` list** of a strand path `(e₁, …, e_m)`: the right list
`(σ ē₁, σ² ē₁, …, σ ē_{m-1}, σ² ē_{m-1})` and the left list
`(σ⁴ ē_{m-1}, σ⁵ ē_{m-1}, …, σ⁴ ē₁, σ⁵ ē₁)`. -/
@[cluster_algebras "def_simple_strand_path"]
def sideList : StrandSide → List H → List H
  | .right, P => P.dropLast.flatMap (X.sideDarts .right)
  | .left, P => P.dropLast.reverse.flatMap (X.sideDarts .left)

/-- A **returning path** of the simple strand path `P` on side `ζ` from `z_{a+1}` to `z_{b+1}`
(`a, b` are `0`-indexed, see the implementation notes): a strand path `Q = (f₁, …, f_n)` such
that `f₁` is a `ζ` dart of `P` at `z_{a+1}`, `f̄_n` is a `ζ` dart of `P` at `z_{b+1}`, and no
interior point of `Q` is the vertex of a dart of `P` or of the reverse of one. It is *parallel* if
`a < b` and *anti-parallel* if `b < a`. -/
@[cluster_algebras "def_returning_path"]
structure IsReturningPath (P : List H) (ζ : StrandSide) (Q : List H) (a b : ℕ) : Prop where
  /-- `P` is a simple strand path. -/
  isSimpleStrandPath : X.IsSimpleStrandPath P
  /-- `Q` is a strand path. -/
  isStrandPath : X.IsStrandPath Q
  /-- `z_{a+1}` is an interior point of `P`. -/
  lt_left : a + 1 < P.length
  /-- `z_{b+1}` is an interior point of `P`. -/
  lt_right : b + 1 < P.length
  /-- `f₁` is a `ζ` dart of `P` at `z_{a+1} = v(ē_{a+1})`. -/
  head?_mem : ∃ e ∈ P[a]?, ∃ f ∈ Q.head?, f ∈ X.sideDarts ζ e
  /-- `f̄_n` is a `ζ` dart of `P` at `z_{b+1} = v(ē_{b+1})`. -/
  getLast?_mem : ∃ e ∈ P[b]?, ∃ f ∈ Q.getLast?, X.inv f ∈ X.sideDarts ζ e
  /-- No interior point of `Q` is the vertex of a dart of `P` or of its reverse. -/
  interiorPoints_ne : ∀ z ∈ X.interiorPoints Q, ∀ e ∈ P,
    z ≠ X.vertexOf e ∧ z ≠ X.vertexOf (X.inv e)

/-- The conditions defining a returning path. -/
theorem isReturningPath_iff {P : List H} {ζ : StrandSide} {Q : List H} {a b : ℕ} :
    X.IsReturningPath P ζ Q a b ↔ X.IsSimpleStrandPath P ∧ X.IsStrandPath Q ∧
      a + 1 < P.length ∧ b + 1 < P.length ∧
      (∃ e ∈ P[a]?, ∃ f ∈ Q.head?, f ∈ X.sideDarts ζ e) ∧
      (∃ e ∈ P[b]?, ∃ f ∈ Q.getLast?, X.inv f ∈ X.sideDarts ζ e) ∧
      ∀ z ∈ X.interiorPoints Q, ∀ e ∈ P, z ≠ X.vertexOf e ∧ z ≠ X.vertexOf (X.inv e) :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩⟩

/-- Being a returning path is decidable. -/
instance (P : List H) (ζ : StrandSide) (Q : List H) (a b : ℕ) :
    Decidable (X.IsReturningPath P ζ Q a b) :=
  decidable_of_iff _ X.isReturningPath_iff.symm

/-- The darts `d₁, d₂, …` of the `ζ` list of `P` lying strictly between `f₁` and `f̄_n`, where
`Q = (f₁, …, f_n)`, numbered from the one nearest to `f₁` (the set `J` of `Hugs`). -/
@[cluster_algebras "def_hugging"]
def hugDarts (P : List H) (ζ : StrandSide) (Q : List H) : List H :=
  match Q.head?, Q.getLast? with
  | some f, some f' =>
    let L := X.sideList ζ P
    let i := L.idxOf f
    let j := L.idxOf (X.inv f')
    if i < j then (L.drop (i + 1)).take (j - i - 1) else ((L.take i).drop (j + 1)).reverse
  | _, _ => []

/-- The exponent `ν s` of `Hugs`: `s = 1` on the right and `s = -1` on the left, and
`ν = 1` if `a > b` and `ν = -1` otherwise. -/
@[cluster_algebras "def_hugging"]
def hugExponent (ζ : StrandSide) (a b : ℕ) : ℤ := (if b < a then 1 else -1) * ζ.sign

/-- A returning path `Q = (f₁, …, f_n)` of `P` on side `ζ` from `z_{a+1}` to `z_{b+1}`, whose
interior points are pairwise distinct, **hugs** `P` if the set `J = (d₁, d₂, …)` of darts of the
`ζ` list of `P` strictly between `f₁` and `f̄_n` (`hugDarts`) has `2(n - 1)` elements and
`d̄_{2j-1} = σ^{νs}(f̄_j)` and `d̄_{2j} = σ^{2νs}(f̄_j)` for every `j ∈ [1, n - 1]`, with
`νs = hugExponent ζ a b`. Lists are `0`-indexed: `d_{2j-1}`, `d_{2j}` and `f_j` are the entries of
index `2(j - 1)`, `2(j - 1) + 1` and `j - 1`. -/
@[cluster_algebras "def_hugging"]
structure Hugs (P : List H) (ζ : StrandSide) (Q : List H) (a b : ℕ) : Prop where
  /-- `Q` is a returning path of `P` on side `ζ` from `z_{a+1}` to `z_{b+1}`. -/
  isReturningPath : X.IsReturningPath P ζ Q a b
  /-- The interior points of `Q` are pairwise distinct. -/
  nodup : (X.interiorPoints Q).Nodup
  /-- `|J| = 2(n - 1)`. -/
  length_hugDarts : (X.hugDarts P ζ Q).length = 2 * (Q.length - 1)
  /-- `d̄_{2j-1} = σ^{νs}(f̄_j)` and `d̄_{2j} = σ^{2νs}(f̄_j)`. -/
  inv_hugDarts : ∀ j < Q.length - 1,
    (X.hugDarts P ζ Q)[2 * j]?.map X.inv =
        Q[j]?.map (fun f => (X.rot ^ hugExponent ζ a b) (X.inv f)) ∧
      (X.hugDarts P ζ Q)[2 * j + 1]?.map X.inv =
        Q[j]?.map (fun f => (X.rot ^ (2 * hugExponent ζ a b)) (X.inv f))

/-- The conditions defining hugging. -/
theorem hugs_iff {P : List H} {ζ : StrandSide} {Q : List H} {a b : ℕ} :
    X.Hugs P ζ Q a b ↔ X.IsReturningPath P ζ Q a b ∧ (X.interiorPoints Q).Nodup ∧
      (X.hugDarts P ζ Q).length = 2 * (Q.length - 1) ∧
      ∀ j < Q.length - 1,
        (X.hugDarts P ζ Q)[2 * j]?.map X.inv =
            Q[j]?.map (fun f => (X.rot ^ hugExponent ζ a b) (X.inv f)) ∧
          (X.hugDarts P ζ Q)[2 * j + 1]?.map X.inv =
            Q[j]?.map (fun f => (X.rot ^ (2 * hugExponent ζ a b)) (X.inv f)) :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

/-- Hugging is decidable. -/
instance (P : List H) (ζ : StrandSide) (Q : List H) (a b : ℕ) :
    Decidable (X.Hugs P ζ Q a b) :=
  decidable_of_iff _ X.hugs_iff.symm


/-! ### Monogons from two passes and from hollow monogons -/

/-- A dart of a triple point `v` has vertex `v`, a triple point. -/
theorem vertexOf_eq_of_mem_internalVertices {v : Finset H} (hv : v ∈ X.internalVertices) {c : H}
    (hc : c ∈ v) : X.vertexOf c = v ∧ ¬X.IsBoundaryVertex (X.vertexOf c) := by
  obtain ⟨hvV, hvb⟩ := X.mem_internalVertices.1 hv
  obtain ⟨d, rfl⟩ := X.mem_vertices.1 hvV
  have := X.vertexOf_eq_of_mem hc
  exact ⟨this, this ▸ hvb⟩

/-- **Two passes of one strand give a monogon.** Let `v` be a triple point with two distinct
passes `{c, σ³ c}` and `{c', σ³ c'}`, and `U = (u₁, …, u_k)` a strand path with `u₁ = σ³ c` and
`ū_k = c'`. Then `U` is a monogon with vertex `v`. The darts `c, c'` need not be `in` darts. -/
@[cluster_algebras "lem_two_passes_monogon"]
theorem isMonogon_of_two_passes (hX : X.IsPreTripleDiagram) {v : Finset H}
    (hv : v ∈ X.internalVertices) {c c' : H} (hc : c ∈ v) (hc' : c' ∈ v)
    (hcc' : ({c, (X.rot ^ 3) c} : Finset H) ≠ {c', (X.rot ^ 3) c'}) {U : List H}
    (hU : X.IsStrandPath U) (h₁ : U.head? = some ((X.rot ^ 3) c))
    (hₖ : ∀ u ∈ U.getLast?, X.inv u = c') :
    X.IsMonogon U ∧ X.pathStart U = v := by
  obtain ⟨hcv, hcb⟩ := X.vertexOf_eq_of_mem_internalVertices hv hc
  obtain ⟨hc'v, -⟩ := X.vertexOf_eq_of_mem_internalVertices hv hc'
  have hu := List.getLast?_eq_some_getLast hU.ne_nil
  have hu' := hₖ _ hu
  have hs : X.pathStart U = v := by rw [X.pathStart_of_head? h₁, X.vertexOf_rot_pow_apply, hcv]
  refine ⟨⟨hU, hs ▸ hv, ?_, ?_⟩, hs⟩
  · rw [X.pathEnd_of_getLast? hu, hu', hc'v, hs]
  · intro e₁ he₁ eₘ heₘ
    have h1 : e₁ = (X.rot ^ 3) c := Option.some_injective _ ((Option.mem_def.1 he₁).symm.trans h₁)
    have h2 : eₘ = U.getLast hU.ne_nil :=
      Option.some_injective _ ((Option.mem_def.1 heₘ).symm.trans hu)
    rw [h1, h2, hu', hX.rot_pow_three_rot_pow_three hcb]
    rintro rfl
    exact hcc' rfl

/-- **A hollow monogon is a monogon.** Let `{c}` be a hollow monogon and `e` the one of `c, c̄`
with `o(e) = out`. Then `v(c) = v(c̄)` is a triple point and `(e)` is a monogon. -/
@[cluster_algebras "lem_hollow_monogon_is_monogon"]
theorem isMonogon_of_isHollowMonogon (hX : X.IsPreTripleDiagram) {c : H}
    (hc : X.IsHollowMonogon {c}) {e : H} (he : e = c ∨ e = X.inv c) (hout : X.isOut e = true) :
    X.vertexOf c = X.vertexOf (X.inv c) ∧ ¬X.IsBoundaryVertex (X.vertexOf c) ∧
      X.IsMonogon [e] := by
  obtain ⟨hcB, hφ⟩ := hc.facePerm_eq
  have hφ' : X.rot (X.inv c) = c := hφ
  have hvc : X.vertexOf c = X.vertexOf (X.inv c) := by
    conv_lhs => rw [← hφ']
    exact X.vertexOf_rot _
  have hicB := hX.inv_notMem_bdry hcB
  have hcb : ¬X.IsBoundaryVertex (X.vertexOf c) := by
    intro hb
    refine hX.inv_ne c (DiskMap.eq_of_notMem_bdry hX.boundaryVertex_card hb ?_
      (X.self_mem_vertexOf c) hicB hcB)
    rw [hvc]
    exact X.self_mem_vertexOf _
  have hicb : ¬X.IsBoundaryVertex (X.vertexOf (X.inv c)) := hvc ▸ hcb
  refine ⟨hvc, hcb, ?_⟩
  rcases he with rfl | rfl
  · refine ⟨⟨by simp, by simpa using hcB, by simpa using hout, List.isChain_singleton _⟩,
      X.vertexOf_mem_internalVertices.2 hcb, hvc.symm, ?_⟩
    intro e₁ he₁ eₘ heₘ
    simp only [List.head?_cons, List.getLast?_singleton, Option.mem_def,
      Option.some.injEq] at he₁ heₘ
    subst he₁ heₘ
    intro h
    have h4 : (X.rot ^ 4) e = (X.rot ^ 0) e := by
      rw [pow_succ', Equiv.Perm.mul_apply, ← h, hφ', pow_zero, Equiv.Perm.one_apply]
    exact absurd ((hX.rot_pow_six hcb).2 4 0 (by norm_num) (by norm_num) h4) (by norm_num)
  · refine ⟨⟨by simp, by simpa using hicB, by simpa using hout, List.isChain_singleton _⟩,
      X.vertexOf_mem_internalVertices.2 hicb, ?_, ?_⟩
    · rw [pathEnd_singleton, pathStart_cons, hX.inv_inv_apply, hvc]
    intro e₁ he₁ eₘ heₘ
    simp only [List.head?_cons, List.getLast?_singleton, Option.mem_def,
      Option.some.injEq] at he₁ heₘ
    subst he₁ heₘ
    rw [hX.inv_inv_apply]
    intro h
    have h3 : (X.rot ^ 3) (X.inv c) = (X.rot ^ 1) (X.inv c) := by
      rw [← h, pow_one, hφ']
    exact absurd ((hX.rot_pow_six hicb).2 3 1 (by norm_num) (by norm_num) h3) (by norm_num)

/-- **A monogon of length one is hollow**: if `(e)` is a monogon, then `{e}` or `{ē}` is a hollow
monogon. -/
@[cluster_algebras "lem_short_monogon_hollow"]
theorem isHollowMonogon_of_isMonogon_singleton (hX : X.IsPreTripleDiagram) {e : H}
    (h : X.IsMonogon [e]) : X.IsHollowMonogon {e} ∨ X.IsHollowMonogon {X.inv e} := by
  have heB : e ∉ X.bdry := h.isStrandPath.notMem_bdry e (by simp)
  have hout : X.isOut e = true := h.isStrandPath.isOut_eq_true e (by simp)
  have hstart := h.pathStart_mem
  have hend := h.pathEnd_eq
  simp only [pathStart_cons, pathEnd_singleton] at hstart hend
  have hb : ¬X.IsBoundaryVertex (X.vertexOf e) := X.vertexOf_mem_internalVertices.1 hstart
  have hmem : X.inv e ∈ X.vertexOf e := by
    rw [← hend]
    exact X.self_mem_vertexOf _
  obtain ⟨n, hn⟩ := (X.mem_vertexOf.1 hmem).exists_nat_pow_eq
  rw [hX.rot_pow_mod_six hb] at hn
  have h3 : X.inv e ≠ (X.rot ^ 3) e := h.inv_ne e (by simp) e (by simp)
  have hinvout : X.isOut (X.inv e) = false := by
    rw [hX.isOut_inv_apply heB, hout]
    rfl
  have hj : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize n % 6 = j at hn hj
  interval_cases j
  · rw [pow_zero, Equiv.Perm.one_apply] at hn
    exact absurd hn.symm (hX.inv_ne e)
  · right
    refine X.isHollowMonogon_singleton (hX.inv_notMem_bdry heB) ?_
    change X.rot (X.inv (X.inv e)) = X.inv e
    rw [hX.inv_inv_apply, ← hn, pow_one]
  · have := hX.isOut_rot_pow_apply hb 2
    rw [hn, hinvout, hout] at this
    simp at this
  · exact absurd hn.symm h3
  · have := hX.isOut_rot_pow_apply hb 4
    rw [hn, hinvout, hout] at this
    simp [Nat.even_iff] at this
  · left
    refine X.isHollowMonogon_singleton heB ?_
    change X.rot (X.inv e) = e
    rw [← hn, ← Equiv.Perm.mul_apply, ← pow_succ']
    exact hX.rot_pow_six_apply hb

/-! ### Walks along strands -/

/-- Along a chain of strand steps of darts not in `B`, the orientation is constant. -/
theorem isOut_eq_of_isChain (hX : X.IsPreTripleDiagram) :
    ∀ {K : List H} {k : H}, (∀ x ∈ k :: K, x ∉ X.bdry) → (k :: K).IsChain X.StrandStep →
      ∀ x ∈ k :: K, X.isOut x = X.isOut k
  | [], k, _, _, x, hx => by
    rw [List.mem_singleton] at hx
    rw [hx]
  | k' :: K, k, hB, hK, x, hx => by
    rw [List.isChain_cons_cons] at hK
    have hstep := hK.1.isOut_eq hX (hB k (by simp))
    rcases List.mem_cons.1 hx with rfl | hx
    · rfl
    · rw [isOut_eq_of_isChain hX (fun y hy => hB y (List.mem_cons_of_mem _ hy)) hK.2 x hx, hstep]

/-- A strand step read backwards along the reverses: if `e' = σ³(ē)` at the triple point `v(ē)`,
then `ē = σ³(ē'̄)` at the triple point `v(e')`. -/
theorem StrandStep.inv_inv {X : TripleData H b} (hX : X.IsPreTripleDiagram) {e e' : H}
    (h : X.StrandStep e e') : X.StrandStep (X.inv e') (X.inv e) := by
  refine ⟨?_, ?_⟩
  · change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.inv e')))
    rw [hX.inv_inv_apply, h.vertexOf_eq]
    exact h.1
  · rw [hX.inv_inv_apply, h.2, hX.rot_pow_three_rot_pow_three h.1]

/-- **Walks along strands**, first part: if `k₁, …, k_n` are darts not in `B` with `v(k̄_j)` a
triple point and `k_{j+1} = σ³(k̄_j)` for `j ∈ [1, n - 1]`, and `o(k₁) = out`, then
`(k₁, …, k_n)` is a strand path. -/
@[cluster_algebras "lem_walk_strand_path"]
theorem isStrandPath_of_isChain (hX : X.IsPreTripleDiagram) {K : List H} (hne : K ≠ [])
    (hB : ∀ k ∈ K, k ∉ X.bdry) (hK : K.IsChain X.StrandStep)
    (hout : X.isOut (K.head hne) = true) : X.IsStrandPath K := by
  obtain ⟨k, K, rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨hne, hB, fun x hx => ?_, hK⟩
  rw [X.isOut_eq_of_isChain hX hB hK x hx]
  exact hout

/-- **Walks along strands**, second part: under the same conditions with `o(k₁) = in`, the
sequence `(k̄_n, …, k̄₁)` is a strand path. -/
@[cluster_algebras "lem_walk_strand_path"]
theorem isStrandPath_reverse_map_inv_of_isChain (hX : X.IsPreTripleDiagram) {K : List H}
    (hne : K ≠ []) (hB : ∀ k ∈ K, k ∉ X.bdry) (hK : K.IsChain X.StrandStep)
    (hin : X.isOut (K.head hne) = false) : X.IsStrandPath (K.reverse.map X.inv) := by
  obtain ⟨k, K', rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨by simp, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hX.inv_notMem_bdry (hB y (List.mem_reverse.1 hy))
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hy' := List.mem_reverse.1 hy
    rw [hX.isOut_inv_apply (hB y hy'), X.isOut_eq_of_isChain hX hB hK y hy']
    simp only [List.head_cons] at hin
    simp [hin]
  · rw [List.isChain_map, List.isChain_reverse]
    exact hK.imp fun _ _ h => h.inv_inv hX

/-! ### Arcs -/

/-- Consecutive darts `S^k(a_i)` and `S^{k+1}(a_i)`, `k < m`, of an arc of length `m + 1` form a
step of a strand path. -/
theorem strandStep_arcDart {i : Fin b} {m : ℕ} (h : X.arcLength i = m + 1) {k : ℕ} (hk : k < m) :
    X.StrandStep (X.arcDart i k) (X.arcDart i (k + 1)) := by
  have hr := (X.arcLength_eq_succ_iff.1 h).2 k hk
  refine ⟨hr, ?_⟩
  rw [arcDart_succ, X.strandMap_of_not_runsToEndpoint hr]
  rfl

/-- The darts of an arc are `out` darts not in `B`. -/
theorem arcDart_notMem_bdry_isOut (hX : X.IsPreTripleDiagram) {i : Fin b} {m : ℕ}
    (h : X.arcLength i = m + 1) {k : ℕ} (hk : k ≤ m) :
    X.arcDart i k ∉ X.bdry ∧ X.isOut (X.arcDart i k) = true := by
  induction k with
  | zero => exact ⟨hX.endDart_notMem_bdry _, hX.isOut_source i⟩
  | succ k ih =>
    have ih := ih (by omega)
    have hs := X.strandStep_arcDart h (k := k) (by omega)
    exact ⟨hs.notMem_bdry, (hs.isOut_eq hX ih.1).trans ih.2⟩

/-- A stretch `(S^s(a_i), …, S^{s+n-1}(a_i))` of an arc is a strand path. -/
theorem isStrandPath_map_arcDart (hX : X.IsPreTripleDiagram) {i : Fin b} {m : ℕ}
    (h : X.arcLength i = m + 1) {s n : ℕ} (hn : n ≠ 0) (hsn : s + n ≤ m + 1) :
    X.IsStrandPath ((List.range' s n).map (X.arcDart i)) := by
  rw [isStrandPath_iff_getElem]
  refine ⟨by simp [hn], fun t ht => ?_, fun t ht => ?_⟩
  · simp only [List.length_map, List.length_range'] at ht
    simp only [List.getElem_map, List.getElem_range', one_mul]
    exact X.arcDart_notMem_bdry_isOut hX h (by omega)
  · simp only [List.length_map, List.length_range'] at ht
    simp only [List.getElem_map, List.getElem_range', one_mul]
    rw [← add_assoc]
    exact X.strandStep_arcDart h (by omega)

/-- The arc from `s_i` is the list of darts `S^k(a_i)` for `k < arcLength i`. -/
theorem arc_eq_map_range' (i : Fin b) :
    X.arc i = (List.range' 0 (X.arcLength i)).map (X.arcDart i) := by
  rw [arc, List.range_eq_range']

/-- An arc of positive length is a strand path. -/
theorem isStrandPath_arc (hX : X.IsPreTripleDiagram) {i : Fin b} (h : X.arcLength i ≠ 0) :
    X.IsStrandPath (X.arc i) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h
  rw [arc_eq_map_range']
  exact X.isStrandPath_map_arcDart hX hm h (by omega)

/-- The darts of an arc are pairwise distinct. -/
theorem arcDart_ne_of_lt {i : Fin b} {m : ℕ} (h : X.arcLength i = m + 1) {a c : ℕ} (hac : a < c)
    (hc : c ≤ m) : X.arcDart i a ≠ X.arcDart i c := by
  intro heq
  have key : X.arcDart i (m - c + a) = X.arcDart i (m - c + c) := by
    simp only [arcDart, Function.iterate_add_apply] at heq ⊢
    rw [heq]
  rw [show m - c + c = m by omega] at key
  have hr := X.arcLength_eq_succ_iff.1 h
  exact hr.2 (m - c + a) (by omega) (key ▸ hr.1)

private theorem not_hasMonogon_aux (hX : X.IsPreTripleDiagram) (hmono : ¬X.HasMonogon) {i : Fin b}
    {m : ℕ} (hm : X.arcLength i = m + 1) {a c : ℕ} (hac : a < c) (hc : c < m)
    (heq : X.vertexOf (X.inv (X.arcDart i a)) = X.vertexOf (X.inv (X.arcDart i c))) : False := by
  have hPs : X.IsStrandPath ((List.range' (a + 1) (c - a)).map (X.arcDart i)) :=
    X.isStrandPath_map_arcDart hX hm (by omega) (by omega)
  have hhead : ((List.range' (a + 1) (c - a)).map (X.arcDart i)).head? =
      some (X.arcDart i (a + 1)) := by
    simp [List.head?_range', show c - a ≠ 0 by omega]
  have hlast : ((List.range' (a + 1) (c - a)).map (X.arcDart i)).getLast? =
      some (X.arcDart i c) := by
    rw [List.getLast?_eq_getElem?]
    simp [show c - a - 1 < c - a by omega, show a + 1 + (c - a - 1) = c by omega]
  have hstep : X.StrandStep (X.arcDart i a) (X.arcDart i (a + 1)) :=
    X.strandStep_arcDart hm (by omega)
  have hstart : X.pathStart ((List.range' (a + 1) (c - a)).map (X.arcDart i)) =
      X.vertexOf (X.inv (X.arcDart i a)) := by
    rw [X.pathStart_of_head? hhead, hstep.vertexOf_eq]
  have hinv : X.inv (X.arcDart i c) = (X.rot ^ 3) (X.arcDart i (a + 1)) := by
    by_contra hne
    refine hmono ⟨_, hPs, ?_, ?_, ?_⟩
    · rw [hstart]
      exact X.vertexOf_mem_internalVertices.2 hstep.1
    · rw [X.pathEnd_of_getLast? hlast, hstart, heq]
    · intro e₁ he₁ eₘ heₘ
      rw [Option.some_injective _ ((Option.mem_def.1 he₁).symm.trans hhead),
        Option.some_injective _ ((Option.mem_def.1 heₘ).symm.trans hlast)]
      exact hne
  rw [hstep.2, hX.rot_pow_three_rot_pow_three hstep.1] at hinv
  exact X.arcDart_ne_of_lt hm hac (by omega) (X.inv.injective hinv).symm

/-- **Arcs of a monogon-free diagram**: if `X` has no monogon, the triple points
`v(ē₁), …, v(ē_{m-1})` of an arc `(e₁, …, e_m)` are pairwise distinct. -/
@[cluster_algebras "lem_arc_no_repeat"]
theorem nodup_interiorPoints_arc (hX : X.IsPreTripleDiagram) (hmono : ¬X.HasMonogon)
    (i : Fin b) : (X.interiorPoints (X.arc i)).Nodup := by
  rcases Nat.eq_zero_or_pos (X.arcLength i) with h0 | hpos
  · simp [interiorPoints, arc, h0]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have heq : X.interiorPoints (X.arc i) =
      (List.range m).map fun k => X.vertexOf (X.inv (X.arcDart i k)) := by
    rw [interiorPoints, arc, ← List.map_dropLast, List.dropLast_eq_take, List.length_range,
      List.take_range, List.map_map, hm]
    simp
  rw [heq]
  refine List.Nodup.map_on (fun a ha c hc hac => ?_) List.nodup_range
  rw [List.mem_range] at ha hc
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact X.not_hasMonogon_aux hX hmono hm hlt hc hac
  · exact X.not_hasMonogon_aux hX hmono hm hlt ha hac.symm

/-! ### Out-darts and closed strands -/

/-- If `f` is injective along the forward orbit of `x` and `f^[a] x = f^[c] x` with `a ≤ c`, then
`x = f^[c - a] x`. -/
private theorem eq_iterate_sub_of_iterate_eq {α : Type*} {f : α → α} {x : α}
    (hinj : ∀ k l, f (f^[k] x) = f (f^[l] x) → f^[k] x = f^[l] x) :
    ∀ a c, f^[a] x = f^[c] x → a ≤ c → x = f^[c - a] x
  | 0, c, h, _ => by simpa using h
  | a + 1, 0, _, hac => absurd hac (by omega)
  | a + 1, c + 1, h, hac => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
    rw [show c + 1 - (a + 1) = c - a by omega]
    exact eq_iterate_sub_of_iterate_eq hinj a c (hinj a c h) (by omega)

/-- On a finite type, a map injective along the forward orbit of `x` returns to `x`. -/
private theorem exists_iterate_eq_self {α : Type*} [Finite α] {f : α → α} {x : α}
    (hinj : ∀ k l, f (f^[k] x) = f (f^[l] x) → f^[k] x = f^[l] x) :
    ∃ p, 0 < p ∧ f^[p] x = x := by
  obtain ⟨a, c, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] x)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨c - a, by omega, (eq_iterate_sub_of_iterate_eq hinj a c h hlt.le).symm⟩
  · exact ⟨a - c, by omega, (eq_iterate_sub_of_iterate_eq hinj c a h.symm hlt.le).symm⟩

/-- In a pre-triple diagram every arc reaches an endpoint: its length is positive. -/
theorem IsPreTripleDiagram.arcLength_ne_zero {X : TripleData H b} (hX : X.IsPreTripleDiagram)
    (i : Fin b) : X.arcLength i ≠ 0 := by
  intro h0
  have hr := X.arcLength_eq_zero_iff.1 h0
  have hS : ∀ k, X.strandMap (X.arcDart i k) = (X.rot ^ 3) (X.inv (X.arcDart i k)) := fun k => by
    rw [X.strandMap_of_not_runsToEndpoint (hr k), rot_pow_three_apply]
  obtain ⟨p, hp, hpx⟩ := exists_iterate_eq_self (f := X.strandMap)
    (x := X.endDart (sourceIndex i)) (fun k l hkl => by
      have h1 := hS k
      have h2 := hS l
      simp only [arcDart] at h1 h2
      rw [h1, h2] at hkl
      exact X.inv.injective ((X.rot ^ 3).injective hkl))
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hv : X.vertexOf (X.endDart (sourceIndex i)) = X.vertexOf (X.inv (X.arcDart i q)) := by
    have : X.strandMap^[q + 1] (X.endDart (sourceIndex i)) =
        (X.rot ^ 3) (X.inv (X.arcDart i q)) := by
      rw [Function.iterate_succ_apply']
      exact hS q
    rw [← X.vertexOf_rot_pow_apply 3 (X.inv (X.arcDart i q)), ← this, hpx]
  apply hr q
  change X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart i q)))
  rw [← hv]
  exact (X.mem_boundaryVertices.1 (hX.endpoint_mem _)).2

/-- The **predecessor** `(σ³ e)̄` of a dart `e` along its strand: for `e` at a triple point,
`S((σ³ e)̄) = e` (`strandMap_strandPred`). -/
def strandPred (e : H) : H := X.inv ((X.rot ^ 3) e)

/-- For a dart `e` at a triple point, `S((σ³ e)̄) = e`. -/
theorem strandMap_strandPred (hX : X.IsPreTripleDiagram) {e : H}
    (he : ¬X.IsBoundaryVertex (X.vertexOf e)) : X.strandMap (X.strandPred e) = e := by
  have hr : ¬X.RunsToEndpoint (X.strandPred e) := by
    change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.inv ((X.rot ^ 3) e))))
    rwa [hX.inv_inv_apply, X.vertexOf_rot_pow_apply]
  rw [X.strandMap_of_not_runsToEndpoint hr, ← rot_pow_three_apply, strandPred, hX.inv_inv_apply,
    hX.rot_pow_three_rot_pow_three he]

/-- The predecessor of an `out` dart at a triple point is an `out` dart not in `B`. -/
theorem strandPred_notMem_bdry_isOut (hX : X.IsPreTripleDiagram) {e : H}
    (he : ¬X.IsBoundaryVertex (X.vertexOf e)) (hout : X.isOut e = true) :
    X.strandPred e ∉ X.bdry ∧ X.isOut (X.strandPred e) = true := by
  have h3 : (X.rot ^ 3) e ∉ X.bdry :=
    X.notMem_bdry_of_not_isBoundaryVertex (by rwa [X.vertexOf_rot_pow_apply])
  refine ⟨hX.inv_notMem_bdry h3, ?_⟩
  rw [strandPred, hX.isOut_inv_apply h3, hX.isOut_rot_pow_three_apply he, hout]
  rfl

/-- **Every out-dart lies on an arc or on a closed strand of out-darts**: a dart `d ∉ B` with
`o(d) = out` is a dart of the arc from some `s_j`, or the orbit of the strand map containing `d`
contains no dart at an endpoint and consists of `out` darts. -/
@[cluster_algebras "lem_out_dart_strand"]
theorem mem_arc_or_forall_strandOrbit (hX : X.IsPreTripleDiagram) {d : H} (hd : d ∉ X.bdry)
    (hout : X.isOut d = true) :
    (∃ j, d ∈ X.arc j) ∨
      ∀ e ∈ X.strandOrbit d, ¬X.IsBoundaryVertex (X.vertexOf e) ∧ X.isOut e = true := by
  set D : ℕ → H := fun q => X.strandPred^[q] d with hD
  have hDsucc : ∀ q, D (q + 1) = X.strandPred (D q) := fun q =>
    Function.iterate_succ_apply' _ _ _
  have hG : ∀ q, (∀ p < q, ¬X.IsBoundaryVertex (X.vertexOf (D p))) →
      D q ∉ X.bdry ∧ X.isOut (D q) = true := by
    intro q
    induction q with
    | zero => exact fun _ => ⟨hd, hout⟩
    | succ q ih =>
      intro hT
      rw [hDsucc]
      exact X.strandPred_notMem_bdry_isOut hX (hT q (by omega))
        (ih (fun p hp => hT p (by omega))).2
  have hSD : ∀ k r, (∀ p < k + r, ¬X.IsBoundaryVertex (X.vertexOf (D p))) →
      X.strandMap^[k] (D (k + r)) = D r := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro r hT
      rw [Function.iterate_succ_apply, show k + 1 + r = (k + r) + 1 by omega, hDsucc,
        X.strandMap_strandPred hX (hT (k + r) (by omega))]
      exact ih r (fun p hp => hT p (by omega))
  by_cases hall : ∀ q, ¬X.IsBoundaryVertex (X.vertexOf (D q))
  · right
    have hper : ∃ p, 0 < p ∧ D p = d := by
      obtain ⟨a, c, hne, hac⟩ := Finite.exists_ne_map_eq_of_infinite D
      have key : ∀ a c, a < c → D a = D c → D (c - a) = d := by
        intro a c hlt hac
        have h1 := hSD a 0 (fun p _ => hall p)
        have h2 := hSD a (c - a) (fun p _ => hall p)
        rw [show a + (c - a) = c by omega, ← hac] at h2
        rw [add_zero] at h1
        rw [← h2, h1]
        rfl
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact ⟨c - a, by omega, key a c hlt hac⟩
      · exact ⟨a - c, by omega, key c a hlt hac.symm⟩
    obtain ⟨p, hp, hDp⟩ := hper
    have hreach : ∀ k, ∃ r, X.strandMap^[k] d = D r := by
      intro k
      induction k with
      | zero => exact ⟨0, rfl⟩
      | succ k ih =>
        obtain ⟨r, hr⟩ := ih
        rw [Function.iterate_succ_apply', hr]
        rcases r with _ | r
        · refine ⟨p - 1, ?_⟩
          have := hSD 1 (p - 1) (fun q _ => hall q)
          rw [show 1 + (p - 1) = p by omega, hDp] at this
          exact this
        · refine ⟨r, ?_⟩
          have := hSD 1 r (fun q _ => hall q)
          rw [add_comm] at this
          exact this
    intro e he
    obtain ⟨k, rfl⟩ := X.mem_strandOrbit.1 he
    obtain ⟨r, hr⟩ := hreach k
    rw [hr]
    exact ⟨hall r, (hG r (fun q _ => hall q)).2⟩
  · left
    simp only [not_forall, not_not] at hall
    classical
    have hq : X.IsBoundaryVertex (X.vertexOf (D (Nat.find hall))) := Nat.find_spec hall
    have hlt : ∀ p < Nat.find hall, ¬X.IsBoundaryVertex (X.vertexOf (D p)) :=
      fun p hp => Nat.find_min hall hp
    generalize Nat.find hall = q at hq hlt
    obtain ⟨hqB, hqout⟩ := hG q hlt
    obtain ⟨r, hr⟩ := hX.exists_endpoint_eq _ (X.vertexOf_mem_boundaryVertices.2 hq)
    have hDq : D q = X.endDart r := by
      refine DiskMap.eq_of_notMem_bdry hX.boundaryVertex_card hq (X.self_mem_vertexOf _) ?_ hqB
        (hX.endDart_notMem_bdry r)
      rw [← hr]
      exact X.self_mem_vertexOf _
    rcases exists_sourceIndex_or_targetIndex r with ⟨j, rfl⟩ | ⟨j, rfl⟩
    swap
    · rw [hDq, hX.isOut_target j] at hqout
      exact absurd hqout (by simp)
    refine ⟨j, ?_⟩
    have hdq : X.arcDart j q = d := by
      have := hSD q 0 hlt
      rw [add_zero, hDq] at this
      exact this
    have hrun : ∀ k < q, ¬X.RunsToEndpoint (X.arcDart j k) := by
      intro k hk
      have h1 := hSD k (q - k) (fun p hp => hlt p (by omega))
      rw [show k + (q - k) = q by omega, hDq] at h1
      change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart j k)))
      rw [show X.arcDart j k = D (q - k) from h1, show q - k = (q - k - 1) + 1 by omega, hDsucc,
        strandPred, hX.inv_inv_apply, X.vertexOf_rot_pow_apply]
      exact hlt _ (by omega)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (hX.arcLength_ne_zero j)
    have hqm : q ≤ m := by
      by_contra hqm
      exact hrun m (by omega) (X.arcLength_eq_succ_iff.1 hm).1
    rw [arc, List.mem_map]
    exact ⟨q, List.mem_range.2 (by omega), hdq⟩

/-- **Reversing a closed strand**: if `C` is a closed strand, then `{d̄ : d ∈ C}` is a closed
strand. -/
@[cluster_algebras "lem_closed_strand_reverse"]
theorem IsClosedStrand.image_inv {X : TripleData H b} (hX : X.IsPreTripleDiagram)
    {C : Finset H} (hC : X.IsClosedStrand C) : X.IsClosedStrand (C.image X.inv) := by
  obtain ⟨d, hdB, rfl, hCb⟩ := hC
  have hmem : ∀ k, X.strandMap^[k] d ∈ X.strandOrbit d := fun k => X.mem_strandOrbit.2 ⟨k, rfl⟩
  have hSmem : ∀ e ∈ X.strandOrbit d, X.strandMap e ∈ X.strandOrbit d := by
    intro e he
    obtain ⟨k, rfl⟩ := X.mem_strandOrbit.1 he
    rw [← Function.iterate_succ_apply' X.strandMap]
    exact hmem _
  have hnr : ∀ e ∈ X.strandOrbit d, ¬X.RunsToEndpoint e := by
    intro e he hr
    have := hCb _ (hSmem e he)
    rw [X.strandMap_of_runsToEndpoint hr] at this
    exact this hr
  have hSe : ∀ e ∈ X.strandOrbit d, X.strandMap e = (X.rot ^ 3) (X.inv e) := fun e he => by
    rw [X.strandMap_of_not_runsToEndpoint (hnr e he), rot_pow_three_apply]
  have hrev : ∀ e ∈ X.strandOrbit d, X.strandMap (X.inv (X.strandMap e)) = X.inv e := by
    intro e he
    have hb : ¬X.IsBoundaryVertex (X.vertexOf (X.strandMap e)) := hCb _ (hSmem e he)
    have hb' : ¬X.IsBoundaryVertex (X.vertexOf (X.inv e)) := by
      rwa [hSe e he, X.vertexOf_rot_pow_apply] at hb
    have hr : ¬X.RunsToEndpoint (X.inv (X.strandMap e)) := by
      change ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.inv (X.strandMap e))))
      rwa [hX.inv_inv_apply]
    rw [X.strandMap_of_not_runsToEndpoint hr, ← rot_pow_three_apply, hX.inv_inv_apply, hSe e he,
      hX.rot_pow_three_rot_pow_three hb']
  obtain ⟨p, hp, hpd⟩ := exists_iterate_eq_self (f := X.strandMap) (x := d) (fun k l hkl => by
    rw [hSe _ (hmem k), hSe _ (hmem l)] at hkl
    exact X.inv.injective ((X.rot ^ 3).injective hkl))
  have hback : ∀ k r, X.strandMap^[k] (X.inv (X.strandMap^[k + r] d)) =
      X.inv (X.strandMap^[r] d) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro r
      rw [Function.iterate_succ_apply, show k + 1 + r = (k + r) + 1 by omega,
        Function.iterate_succ_apply', hrev _ (hmem _)]
      exact ih r
  have hmul : ∀ t, X.strandMap^[p * t] d = d := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [Nat.mul_succ, Function.iterate_add_apply, hpd, ih]
  have hinv_eq : X.strandOrbit (X.inv d) = (X.strandOrbit d).image X.inv := by
    ext e
    rw [X.mem_strandOrbit, mem_image]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨X.strandMap^[p * k - k] d, hmem _, ?_⟩
      have := hback k (p * k - k)
      rw [Nat.add_sub_cancel' (Nat.le_mul_of_pos_left k hp), hmul] at this
      exact this.symm
    · rintro ⟨e', he', rfl⟩
      obtain ⟨r, rfl⟩ := X.mem_strandOrbit.1 he'
      refine ⟨p * r - r, ?_⟩
      have := hback (p * r - r) r
      rwa [Nat.sub_add_cancel (Nat.le_mul_of_pos_left r hp), hmul] at this
  refine ⟨X.inv d, hX.inv_notMem_bdry hdB, hinv_eq.symm, ?_⟩
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_image.1 he
  have hb := hCb _ (hSmem e' he')
  rwa [hSe e' he', X.vertexOf_rot_pow_apply] at hb

end TripleData

/-! ### Monogon-stable triple diagrams -/

namespace TripleDiagram

variable {b : ℕ}

/-- A triple diagram is **monogon-stable** if no triple diagram move-equivalent to it has a
monogon. -/
@[cluster_algebras "def_monogon_stable"]
def IsMonogonStable (X : TripleDiagram b) : Prop :=
  ∀ X' : TripleDiagram b, X.MoveEquivalent X' → ¬X'.data.HasMonogon

end TripleDiagram

end ClusterAlgebras

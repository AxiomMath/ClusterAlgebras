/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.SimpleArc
public import ClusterAlgebras.Plabic.MinimalTriple
public import ClusterAlgebras.Plabic.Swivel
public import ClusterAlgebras.Plabic.CycleSpace
public import ClusterAlgebras.Plabic.TripleMoves

/-!
# Cutting a triple diagram along a simple arc

Let `X` be a triple diagram and `S` a simple arc of `X`. Thurston's induction views the part of
`X` on one side `ζ` of `S` as a smaller triple diagram `X|_{S,ζ}`, the *cut* of `X` along `S`: its
darts are the darts `H_ζ(S)` on that side together with `2N` new boundary darts `α_k, ᾱ_k`, where
`N` is the length of the `ζ` cut list `(g₀, …, g_{N-1})`, and the rotation closes each `g_k` into
the `3`-cycle `(g_k ᾱ_k α_{k-1})` of a new endpoint. The cut is a triple diagram whose triple
points are the triple points of `X` on that side, its strand paths are strand paths of `X`, and
swivel moves of the cut are swivel moves of `X`. We also show that chords of a triple diagram
without triple points do not cross, and define boundary-parallel arcs.

## Main definitions

* `ClusterAlgebras.TripleData.cut`: the cut along a set `K` of darts and a list `L` of its darts.
* `ClusterAlgebras.TripleData.arcCut`: the cut `X|_{S,ζ}` of a triple diagram along a simple arc.
* `ClusterAlgebras.TripleData.IsBoundaryParallel`: an arc that is boundary-parallel along an
  interval.

## Main results

* `ClusterAlgebras.TripleData.IsSimpleArc.isTripleDiagram_arcCut`,
  `ClusterAlgebras.TripleData.two_mul_length_arcCutList_div_two`,
  `ClusterAlgebras.TripleData.IsSimpleArc.internalVertices_arcCut`: the cut is a triple diagram
  with `N_ζ / 2` arcs, whose triple points are those of `X` on the side `ζ` avoided by `S`.
* `ClusterAlgebras.TripleData.IsSimpleArc.card_internalVertices_arcCut_le`: the cut has fewer
  triple points.
* `ClusterAlgebras.TripleData.IsSimpleArc.exists_isStrandPath_of_isStrandPath_arcCut`,
  `ClusterAlgebras.TripleData.IsSimpleArc.isMonogon_of_isMonogon_arcCut`,
  `ClusterAlgebras.TripleData.IsSimpleArc.mem_arcCutList_of_eq_arc_arcCut`: strand paths, monogons
  and arcs of the cut.
* `ClusterAlgebras.TripleData.IsSimpleArc.arcCut_swivelMove`: swivel moves of the cut are swivel
  moves of `X`.
* `ClusterAlgebras.TripleData.inv_endDart_ne_endDart_of_cyclic`: chords of a triple diagram without
  triple points do not cross.

## Implementation notes

The new darts of the cut are `Sum.inr (k, true) = α_k` and `Sum.inr (k, false) = ᾱ_k`, so that the
cut of a swivel move of `X` away from `S` is the swivel move of the cut on the nose; the two cuts
then live on the same type of darts, and the equality is stated as `HEq` since that type is built
from `H_ζ(S)` and the cut list. Labels are `0`-indexed: the endpoint `ε'(r)` of the cut is the
cycle of `g_r` on the right and of `g_{r+1}` on the left, for `r : Fin (2 * (N / 2))`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-- The permutation given by a map `f`, if `f` is bijective, and the identity otherwise. -/
noncomputable def permOfBijectiveOrOne {α : Type*} (f : α → α) : Equiv.Perm α :=
  open scoped Classical in
  if h : Function.Bijective f then Equiv.ofBijective f h else 1

/-- For a bijective map `f`, the permutation `permOfBijectiveOrOne f` agrees with `f`. -/
theorem permOfBijectiveOrOne_apply {α : Type*} {f : α → α} (hf : Function.Bijective f) (x : α) :
    permOfBijectiveOrOne f x = f x := by
  unfold permOfBijectiveOrOne
  rw [dif_pos hf]
  rfl

namespace TripleData

/-- The darts `H_K ⊔ {α_k, ᾱ_k : k ∈ ℤ/N}` of a cut: the darts of a set `K` (`Sum.inl`) and `2N`
new symbols, `α_k = Sum.inr (k, true)` and `ᾱ_k = Sum.inr (k, false)`. -/
abbrev CutDart {H : Type*} (K : Finset H) (N : ℕ) : Type _ := {d // d ∈ K} ⊕ (Fin N × Bool)

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)

/-- The dart `g_k = L[k]` of the list `L`, as a dart of the cut (if it lies in `K`). -/
def cutListDart (K : Finset H) (L : List H) (k : Fin L.length) : CutDart K L.length :=
  if h : L[(k : ℕ)] ∈ K then .inl ⟨L[(k : ℕ)], h⟩ else .inr (k, true)

/-- The rotation of the cut along `(K, L)`, as a map: `σ` on the darts of `K` outside `L`, and the
`3`-cycles `g_k ↦ ᾱ_k ↦ α_{k-1} ↦ g_k`, `g_k = L[k]`. -/
def cutRotFun (K : Finset H) (L : List H) : CutDart K L.length → CutDart K L.length
  | .inl d =>
    if h : d.1 ∈ L then .inr (⟨L.idxOf d.1, List.idxOf_lt_length_of_mem h⟩, false)
    else if h' : X.rot d.1 ∈ K then .inl ⟨X.rot d.1, h'⟩ else .inl d
  | .inr (k, false) => .inr ((finRotate _).symm k, true)
  | .inr (k, true) => cutListDart K L (finRotate _ k)

/-- The involution of the cut along `K`, as a map: `d ↦ d̄` on `K` and `α_k ↔ ᾱ_k`. -/
def cutInvFun (K : Finset H) (N : ℕ) : CutDart K N → CutDart K N
  | .inl d => if h : X.inv d.1 ∈ K then .inl ⟨X.inv d.1, h⟩ else .inl d
  | .inr (k, β) => .inr (k, !β)

/-- The **cut** of `X` along a set `K` of darts and a list `L = (g₀, …, g_{N-1})` of darts of `K`,
with shift `s`: the darts are `K ⊔ {α_k, ᾱ_k : k ∈ ℤ/N}`; the involution is `d ↦ d̄` on `K` and
exchanges `α_k` and `ᾱ_k`; the rotation is `σ` on `K` outside `L` and consists of the `3`-cycles
`(g_k ᾱ_k α_{k-1})` on the remaining darts; `B' = {α_k, ᾱ_k}`; the orientation is that of `X`; and
the endpoint `ε'(r)` is the cycle of `g_{r+s}` (labels `0`-indexed, indices modulo `N`). It has
`N / 2` arcs. The rotation and the involution are defined by these formulas when they are
bijective, which is the case under `IsCutData`, and are the identity otherwise. -/
noncomputable def cut (K : Finset H) (L : List H) (s : ℕ) :
    TripleData (CutDart K L.length) (L.length / 2) where
  inv := permOfBijectiveOrOne (X.cutInvFun K L.length)
  rot := permOfBijectiveOrOne (X.cutRotFun K L)
  bdry := univ.filter fun x => x.isRight
  endDart r := cutListDart K L ⟨((r : ℕ) + s) % L.length, Nat.mod_lt _ (by have := r.isLt; omega)⟩
  isOut := Sum.elim (fun d => X.isOut d.1) fun _ => false

/-- The conditions on a set `K` of darts and a list `L` under which the cut along `(K, L)` is
well behaved: `L` has no repetition and its darts lie in `K`, `K` is closed under `d ↦ d̄` and
contains no dart of `B`, and the darts of `K` outside `L` fill triple points of `X` whose darts all
lie in `K` outside `L`. -/
structure IsCutData (K : Finset H) (L : List H) : Prop where
  /-- `L` has no repetition. -/
  nodup : L.Nodup
  /-- The darts of `L` lie in `K`. -/
  mem_of_mem_list : ∀ d ∈ L, d ∈ K
  /-- `K` is closed under `d ↦ d̄`. -/
  inv_mem : ∀ d ∈ K, X.inv d ∈ K
  /-- `K` contains no dart of `B`. -/
  notMem_bdry : ∀ d ∈ K, d ∉ X.bdry
  /-- A dart of `K` outside `L` lies at a triple point. -/
  not_isBoundaryVertex : ∀ d ∈ K, d ∉ L → ¬X.IsBoundaryVertex (X.vertexOf d)
  /-- The darts at the vertex of a dart of `K` outside `L` lie in `K` outside `L`. -/
  mem_of_mem_vertexOf : ∀ d ∈ K, d ∉ L → ∀ e ∈ X.vertexOf d, e ∈ K ∧ e ∉ L

namespace IsCutData

variable {X} {K : Finset H} {L : List H} (hc : X.IsCutData K L)

include hc

/-- The dart `g_k = L[k]` lies in `K`. -/
theorem getElem_mem (k : Fin L.length) : L[(k : ℕ)] ∈ K :=
  hc.mem_of_mem_list _ (List.getElem_mem _)

/-- The dart `g_k` of the cut is the dart `L[k]` of `K`. -/
theorem cutListDart_eq (k : Fin L.length) :
    cutListDart K L k = .inl ⟨L[(k : ℕ)], hc.getElem_mem k⟩ := by
  unfold cutListDart
  rw [dif_pos (hc.getElem_mem k)]

/-- The rotation `σ(d)` of a dart `d` of `K` outside `L` lies in `K`. -/
theorem rot_mem {d : H} (hd : d ∈ K) (hL : d ∉ L) : X.rot d ∈ K :=
  (hc.mem_of_mem_vertexOf d hd hL _ (X.rot_mem_vertexOf d)).1

/-- The rotation `σ(d)` of a dart `d` of `K` outside `L` does not lie in `L`. -/
theorem rot_notMem {d : H} (hd : d ∈ K) (hL : d ∉ L) : X.rot d ∉ L :=
  (hc.mem_of_mem_vertexOf d hd hL _ (X.rot_mem_vertexOf d)).2

/-- The index of `L[k]` in `L` is `k`. -/
theorem idxOf_getElem (k : Fin L.length) : L.idxOf L[(k : ℕ)] = k :=
  hc.nodup.idxOf_getElem _ _

/-- The involution of the cut sends a dart `d` of `K` to `d̄`. -/
theorem cutInvFun_inl (d : {d // d ∈ K}) :
    X.cutInvFun K L.length (.inl d) = .inl ⟨X.inv d.1, hc.inv_mem _ d.2⟩ := by
  simp only [cutInvFun, dif_pos (hc.inv_mem _ d.2)]

omit [Fintype H] hc in
/-- The involution of the cut exchanges `α_k` and `ᾱ_k`. -/
theorem cutInvFun_inr (k : Fin L.length) (β : Bool) :
    X.cutInvFun K L.length (.inr (k, β)) = .inr (k, !β) := rfl

/-- If `d ↦ d̄` is an involution of `X`, then the involution map of the cut is involutive. -/
theorem cutInvFun_involutive (hinv : Function.Involutive X.inv) :
    Function.Involutive (X.cutInvFun K L.length) := by
  rintro (d | ⟨k, β⟩)
  · rw [hc.cutInvFun_inl, hc.cutInvFun_inl]
    congr 1
    exact Subtype.ext (hinv _)
  · rw [cutInvFun_inr, cutInvFun_inr, Bool.not_not]

/-- The rotation map of the cut is `σ` on a dart of `K` outside `L`. -/
theorem cutRotFun_inl_of_notMem (d : {d // d ∈ K}) (hd : d.1 ∉ L) :
    X.cutRotFun K L (.inl d) = .inl ⟨X.rot d.1, hc.rot_mem d.2 hd⟩ := by
  simp only [cutRotFun, dif_neg hd, dif_pos (hc.rot_mem d.2 hd)]

/-- The rotation map of the cut sends `g_k` to `ᾱ_k`. -/
theorem cutRotFun_inl_getElem (k : Fin L.length) :
    X.cutRotFun K L (.inl ⟨L[(k : ℕ)], hc.getElem_mem k⟩) = .inr (k, false) := by
  simp only [cutRotFun, dif_pos (List.getElem_mem _)]
  congr
  exact hc.idxOf_getElem k

omit [Fintype H] hc in
/-- The rotation map of the cut sends `ᾱ_k` to `α_{k-1}`. -/
theorem cutRotFun_inr_false (k : Fin L.length) :
    X.cutRotFun K L (.inr (k, false)) = .inr ((finRotate _).symm k, true) := rfl

/-- The rotation map of the cut sends `α_k` to `g_{k+1}`. -/
theorem cutRotFun_inr_true (k : Fin L.length) :
    X.cutRotFun K L (.inr (k, true)) =
      .inl ⟨L[((finRotate _ k : Fin L.length) : ℕ)], hc.getElem_mem _⟩ := by
  simp only [cutRotFun]
  exact hc.cutListDart_eq _

/-- The rotation map of the cut is injective. -/
theorem cutRotFun_injective : Function.Injective (X.cutRotFun K L) := by
  have key : ∀ x : CutDart K L.length, (∃ d : {d // d ∈ K}, ∃ hd : d.1 ∉ L,
      x = .inl d ∧ X.cutRotFun K L x = .inl ⟨X.rot d.1, hc.rot_mem d.2 hd⟩) ∨
      (∃ k : Fin L.length, x = .inl ⟨L[(k : ℕ)], hc.getElem_mem k⟩ ∧
        X.cutRotFun K L x = .inr (k, false)) ∨
      (∃ k : Fin L.length, x = .inr (k, false) ∧
        X.cutRotFun K L x = .inr ((finRotate _).symm k, true)) ∨
      (∃ k : Fin L.length, x = .inr (k, true) ∧
        X.cutRotFun K L x = .inl ⟨L[((finRotate _ k : Fin L.length) : ℕ)], hc.getElem_mem _⟩) := by
    rintro (d | ⟨k, _ | _⟩)
    · by_cases hd : d.1 ∈ L
      · obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hd
        refine Or.inr (Or.inl ⟨⟨k, hk⟩, ?_, ?_⟩)
        · exact congrArg Sum.inl (Subtype.ext hkd.symm)
        · have : d = ⟨L[k], hc.getElem_mem ⟨k, hk⟩⟩ := Subtype.ext hkd.symm
          subst this
          exact hc.cutRotFun_inl_getElem ⟨k, hk⟩
      · exact Or.inl ⟨d, hd, rfl, hc.cutRotFun_inl_of_notMem d hd⟩
    · exact Or.inr (Or.inr (Or.inl ⟨k, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨k, rfl, hc.cutRotFun_inr_true k⟩))
  intro x y hxy
  rcases key x with ⟨d, hd, rfl, hx⟩ | ⟨k, rfl, hx⟩ | ⟨k, rfl, hx⟩ | ⟨k, rfl, hx⟩ <;>
  rcases key y with ⟨d', hd', rfl, hy⟩ | ⟨k', rfl, hy⟩ | ⟨k', rfl, hy⟩ | ⟨k', rfl, hy⟩ <;>
  rw [hx, hy] at hxy <;> simp only [Sum.inl.injEq, Sum.inr.injEq, Subtype.mk.injEq,
    Prod.mk.injEq, reduceCtorEq, and_false, and_true, Bool.false_eq_true] at hxy
  all_goals first
    | exact congrArg Sum.inl (Subtype.ext (X.rot.injective hxy))
    | exact absurd (show X.rot d.1 ∈ L from hxy ▸ List.getElem_mem _) (hc.rot_notMem d.2 hd)
    | exact absurd (show X.rot d'.1 ∈ L from hxy ▸ List.getElem_mem _) (hc.rot_notMem d'.2 hd')
    | exact absurd (show X.rot d.1 ∈ L from hxy.symm ▸ List.getElem_mem _) (hc.rot_notMem d.2 hd)
    | exact absurd (show X.rot d'.1 ∈ L from hxy.symm ▸ List.getElem_mem _)
        (hc.rot_notMem d'.2 hd')
    | (subst hxy; rfl)
    | exact congrArg (fun k => Sum.inr (k, false)) ((finRotate _).symm.injective hxy)
    | (have := (hc.nodup.getElem_inj_iff).1 hxy
       rw [(finRotate _).injective (Fin.ext this)])

end IsCutData

/-! ### The cut along a set of darts and a list -/

section Cut

variable {X} {K : Finset H} {L : List H} {s : ℕ}

/-- The darts of the cut lying over a set `v` of darts of `X`: the darts `Sum.inl d`,
`d ∈ v ∩ K`. -/
def liftVertex (K : Finset H) (N : ℕ) (v : Finset H) : Finset (CutDart K N) :=
  (v.subtype (· ∈ K)).map Function.Embedding.inl

omit [Fintype H] in
/-- A dart of the cut lies over `v` if and only if it is `Sum.inl d` for a dart `d ∈ v ∩ K`. -/
theorem mem_liftVertex {N : ℕ} {v : Finset H} {x : CutDart K N} :
    x ∈ liftVertex K N v ↔ ∃ d : {d // d ∈ K}, d.1 ∈ v ∧ x = .inl d := by
  simp only [liftVertex, mem_map, mem_subtype, Function.Embedding.inl_apply]
  exact ⟨fun ⟨d, hd, e⟩ => ⟨d, hd, e.symm⟩, fun ⟨d, hd, e⟩ => ⟨d, hd, e.symm⟩⟩

omit [Fintype H] in
/-- For `v ⊆ K`, the set of darts of the cut over `v` has as many elements as `v`. -/
theorem card_liftVertex {N : ℕ} {v : Finset H} (hv : v ⊆ K) :
    (liftVertex K N v).card = v.card := by
  rw [liftVertex, card_map, card_subtype, filter_true_of_mem fun d hd => hv hd]

/-- The three darts `g_k, ᾱ_k, α_{k-1}` of the endpoint of the cut at `g_k`. -/
def cutTriple (K : Finset H) (L : List H) (k : Fin L.length) : Finset (CutDart K L.length) :=
  {cutListDart K L k, .inr (k, false), .inr ((finRotate _).symm k, true)}

namespace IsCutData

variable (hc : X.IsCutData K L)

include hc

/-- The rotation map of the cut is bijective. -/
theorem cutRotFun_bijective : Function.Bijective (X.cutRotFun K L) :=
  Finite.injective_iff_bijective.1 hc.cutRotFun_injective

/-- The rotation of the cut is given by `cutRotFun`. -/
theorem cut_rot_apply (x : CutDart K L.length) : (X.cut K L s).rot x = X.cutRotFun K L x :=
  permOfBijectiveOrOne_apply hc.cutRotFun_bijective x

/-- The rotation of the cut is `σ` on a dart of `K` outside `L`. -/
theorem cut_rot_inl_of_notMem (d : {d // d ∈ K}) (hd : d.1 ∉ L) :
    (X.cut K L s).rot (.inl d) = .inl ⟨X.rot d.1, hc.rot_mem d.2 hd⟩ := by
  rw [hc.cut_rot_apply, hc.cutRotFun_inl_of_notMem d hd]

/-- The rotation of the cut sends `g_k` to `ᾱ_k`. -/
theorem cut_rot_cutListDart (k : Fin L.length) :
    (X.cut K L s).rot (cutListDart K L k) = .inr (k, false) := by
  rw [hc.cut_rot_apply, hc.cutListDart_eq, hc.cutRotFun_inl_getElem]

/-- The rotation of the cut sends `ᾱ_k` to `α_{k-1}`. -/
theorem cut_rot_inr_false (k : Fin L.length) :
    (X.cut K L s).rot (.inr (k, false)) = .inr ((finRotate _).symm k, true) := by
  rw [hc.cut_rot_apply]
  rfl

/-- The rotation of the cut sends `α_k` to `g_{k+1}`. -/
theorem cut_rot_inr_true (k : Fin L.length) :
    (X.cut K L s).rot (.inr (k, true)) = cutListDart K L (finRotate _ k) := by
  rw [hc.cut_rot_apply]
  rfl

section Inv

variable (hinv : Function.Involutive X.inv)

include hinv

/-- The involution of the cut is given by `cutInvFun`. -/
theorem cut_inv_apply (x : CutDart K L.length) :
    (X.cut K L s).inv x = X.cutInvFun K L.length x :=
  permOfBijectiveOrOne_apply (hc.cutInvFun_involutive hinv).bijective x

/-- The involution of the cut sends a dart `d` of `K` to `d̄`. -/
theorem cut_inv_inl (d : {d // d ∈ K}) :
    (X.cut K L s).inv (.inl d) = .inl ⟨X.inv d.1, hc.inv_mem _ d.2⟩ := by
  rw [hc.cut_inv_apply hinv, hc.cutInvFun_inl]

/-- The involution of the cut exchanges `α_k` and `ᾱ_k`. -/
theorem cut_inv_inr (k : Fin L.length) (β : Bool) :
    (X.cut K L s).inv (.inr (k, β)) = .inr (k, !β) := by
  rw [hc.cut_inv_apply hinv]
  rfl

/-- The involution of the cut is involutive. -/
theorem cut_inv_involutive : Function.Involutive (X.cut K L s).inv := by
  intro x
  rw [hc.cut_inv_apply hinv, hc.cut_inv_apply hinv]
  exact hc.cutInvFun_involutive hinv x

end Inv

/-- For a dart `d` of `K` outside `L`, every `σ^n(d)` is a dart of `K` outside `L`, and the
`n`-th power of the rotation of the cut sends `d` to `σ^n(d)`. -/
theorem cut_rot_pow_inl_of_notMem (d : {d // d ∈ K}) (hd : d.1 ∉ L) (n : ℕ) :
    ∃ h : (X.rot ^ n) d.1 ∈ K, (X.rot ^ n) d.1 ∉ L ∧
      ((X.cut K L s).rot ^ n) (.inl d) = .inl ⟨(X.rot ^ n) d.1, h⟩ := by
  induction n with
  | zero => exact ⟨d.2, hd, rfl⟩
  | succ n ih =>
    obtain ⟨h, hL, e⟩ := ih
    have e1 : (X.rot ^ (n + 1)) d.1 = X.rot ((X.rot ^ n) d.1) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [e1]
    refine ⟨hc.rot_mem h hL, hc.rot_notMem h hL, ?_⟩
    rw [pow_succ', Equiv.Perm.mul_apply, e, hc.cut_rot_inl_of_notMem ⟨_, h⟩ hL]

/-- The vertex of the cut at a dart `d` of `K` outside `L` consists of the darts over the vertex
of `X` at `d`. -/
theorem cut_vertexOf_inl_of_notMem (d : {d // d ∈ K}) (hd : d.1 ∉ L) :
    (X.cut K L s).vertexOf (.inl d) = liftVertex K L.length (X.vertexOf d.1) := by
  ext x
  rw [RotationSystem.mem_vertexOf, mem_liftVertex]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    obtain ⟨h1, -, e⟩ := hc.cut_rot_pow_inl_of_notMem (s := s) d hd n
    exact ⟨⟨_, h1⟩, RotationSystem.rot_pow_apply_mem_vertexOf _ n _, e⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨n, hn⟩ := (X.mem_vertexOf.1 he).exists_nat_pow_eq
    obtain ⟨h1, -, e'⟩ := hc.cut_rot_pow_inl_of_notMem (s := s) d hd n
    have : e = ⟨_, h1⟩ := Subtype.ext hn.symm
    rw [this, ← e']
    exact Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)

/-- The rotation of the cut preserves the triple `{g_k, ᾱ_k, α_{k-1}}`. -/
theorem cut_rot_mem_cutTriple {k : Fin L.length} {x : CutDart K L.length}
    (hx : x ∈ cutTriple K L k) : (X.cut K L s).rot x ∈ cutTriple K L k := by
  simp only [cutTriple, mem_insert, mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl
  · rw [hc.cut_rot_cutListDart]
    exact Or.inr (Or.inl rfl)
  · rw [hc.cut_rot_inr_false]
    exact Or.inr (Or.inr rfl)
  · rw [hc.cut_rot_inr_true, Equiv.apply_symm_apply]
    exact Or.inl rfl

/-- The vertex of the cut at `g_k` is the triple `{g_k, ᾱ_k, α_{k-1}}`. -/
theorem cut_vertexOf_cutListDart (k : Fin L.length) :
    (X.cut K L s).vertexOf (cutListDart K L k) = cutTriple K L k := by
  ext x
  rw [RotationSystem.mem_vertexOf]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => simp [cutTriple]
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hc.cut_rot_mem_cutTriple ih
  · intro hx
    simp only [cutTriple, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.refl _ _
    · rw [← hc.cut_rot_cutListDart (s := s) k]
      exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
    · rw [← hc.cut_rot_inr_false (s := s) k, ← hc.cut_rot_cutListDart (s := s) k]
      exact Equiv.Perm.sameCycle_apply_right.2
        (Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _))

/-- Every dart of the cut is a dart of `K` outside `L`, or lies in one of the triples
`{g_k, ᾱ_k, α_{k-1}}`. -/
theorem cutDart_cases (x : CutDart K L.length) :
    (∃ d : {d // d ∈ K}, d.1 ∉ L ∧ x = .inl d) ∨ ∃ k, x ∈ cutTriple K L k := by
  rcases x with d | ⟨k, _ | _⟩
  · by_cases hd : d.1 ∈ L
    · obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hd
      refine Or.inr ⟨⟨k, hk⟩, ?_⟩
      have : (Sum.inl d : CutDart K L.length) = cutListDart K L ⟨k, hk⟩ := by
        rw [hc.cutListDart_eq]
        exact congrArg Sum.inl (Subtype.ext hkd.symm)
      rw [this]
      simp [cutTriple]
    · exact Or.inl ⟨d, hd, rfl⟩
  · exact Or.inr ⟨k, by simp [cutTriple]⟩
  · refine Or.inr ⟨finRotate _ k, ?_⟩
    simp only [cutTriple, mem_insert, mem_singleton, Equiv.symm_apply_apply, or_true]

/-- The vertex of the cut at a dart of the triple `{g_k, ᾱ_k, α_{k-1}}` is that triple. -/
theorem cut_vertexOf_of_mem_cutTriple {k : Fin L.length} {x : CutDart K L.length}
    (hx : x ∈ cutTriple K L k) : (X.cut K L s).vertexOf x = cutTriple K L k := by
  rw [← hc.cut_vertexOf_cutListDart (s := s) k]
  apply RotationSystem.vertexOf_eq_of_mem
  rwa [hc.cut_vertexOf_cutListDart]

omit [Fintype H] hc in
/-- The boundary darts of the cut are the new darts `α_k, ᾱ_k`. -/
theorem mem_cut_bdry {x : CutDart K L.length} : x ∈ (X.cut K L s).bdry ↔ x.isRight := by
  simp [cut]

/-- The vertex of the cut at a dart of `K` outside `L` is not a boundary vertex. -/
theorem cut_not_isBoundaryVertex_vertexOf_inl {d : {d // d ∈ K}} (hd : d.1 ∉ L) :
    ¬(X.cut K L s).IsBoundaryVertex ((X.cut K L s).vertexOf (.inl d)) := by
  rintro ⟨y, hy, hyB⟩
  rw [hc.cut_vertexOf_inl_of_notMem d hd, mem_liftVertex] at hy
  obtain ⟨e, -, rfl⟩ := hy
  simp [mem_cut_bdry] at hyB

/-- The vertex of the cut at a dart of the triple `{g_k, ᾱ_k, α_{k-1}}` is a boundary vertex. -/
theorem cut_isBoundaryVertex_vertexOf_of_mem_cutTriple {k : Fin L.length}
    {x : CutDart K L.length} (hx : x ∈ cutTriple K L k) :
    (X.cut K L s).IsBoundaryVertex ((X.cut K L s).vertexOf x) := by
  rw [hc.cut_vertexOf_of_mem_cutTriple hx]
  exact ⟨.inr (k, false), by simp [cutTriple], by simp [mem_cut_bdry]⟩

/-- A dart of the cut lies at a triple point exactly when it is a dart of `K` outside `L`. -/
theorem cut_not_isBoundaryVertex_iff {x : CutDart K L.length} :
    ¬(X.cut K L s).IsBoundaryVertex ((X.cut K L s).vertexOf x) ↔
      ∃ d : {d // d ∈ K}, d.1 ∉ L ∧ x = .inl d := by
  constructor
  · intro h
    rcases hc.cutDart_cases x with h' | ⟨k, hk⟩
    · exact h'
    · exact absurd (hc.cut_isBoundaryVertex_vertexOf_of_mem_cutTriple hk) h
  · rintro ⟨d, hd, rfl⟩
    exact hc.cut_not_isBoundaryVertex_vertexOf_inl hd

/-- The triple `{g_k, ᾱ_k, α_{k-1}}` has three elements. -/
theorem card_cutTriple (k : Fin L.length) : (cutTriple K L k).card = 3 := by
  rw [cutTriple, hc.cutListDart_eq]
  rw [card_insert_of_notMem (by simp), card_pair (by simp)]

end IsCutData

end Cut

/-! ### The cut is a pre-triple diagram -/

section CutPreTriple

private theorem val_finRotate_eq {n : ℕ} (j : Fin n) : (finRotate n j : ℕ) = ((j : ℕ) + 1) % n := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : j = Fin.last n
    · subst h
      simp
    · have : (j : ℕ) < n := Fin.val_lt_last h
      rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

private theorem val_finRotate_symm_succ {n k : ℕ} (hk : k + 1 < n) :
    (finRotate n).symm ⟨k + 1, hk⟩ = ⟨k, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [val_finRotate_eq, Nat.mod_eq_of_lt hk]

private theorem even_mod_add_iff {N x y : ℕ} (hN : Even N) : Even (x % N + y) ↔ Even (x + y) := by
  have h := Nat.mod_add_div x N
  have he : Even (N * (x / N)) := hN.mul_right _
  conv_rhs => rw [← h]
  rw [show x % N + N * (x / N) + y = (x % N + y) + N * (x / N) by ring,
    Nat.even_add (m := x % N + y) (n := N * (x / N)), iff_true_intro he, iff_true]

private theorem eq_of_add_mod_eq {N r r' s : ℕ} (hr : r < N) (hr' : r' < N)
    (h : (r + s) % N = (r' + s) % N) : r = r' := by
  have : r ≡ r' [MOD N] := Nat.ModEq.add_right_cancel' s h
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at this

variable {X} {K : Finset H} {L : List H} {s : ℕ}

/-- The index `k = r + s` modulo `N` of the dart `g_k` at the endpoint `ε'(r)` of the cut. -/
def cutEndIndex (L : List H) (s : ℕ) (r : Fin (2 * (L.length / 2))) : Fin L.length :=
  ⟨((r : ℕ) + s) % L.length, Nat.mod_lt _ (by have := r.isLt; omega)⟩

omit [Fintype H] [DecidableEq H] in
/-- The map `r ↦ r + s` modulo `N` is injective. -/
theorem cutEndIndex_injective : Function.Injective (cutEndIndex (H := H) L s) := by
  intro r r' h
  have h' := congrArg Fin.val h
  simp only [cutEndIndex] at h'
  exact Fin.ext (eq_of_add_mod_eq (by have := r.isLt; omega) (by have := r'.isLt; omega) h')

omit [Fintype H] [DecidableEq H] in
/-- For `N` even, the map `r ↦ r + s` modulo `N` is surjective. -/
theorem cutEndIndex_surjective (hev : Even L.length) :
    Function.Surjective (cutEndIndex (H := H) L s) := by
  have hcard : Fintype.card (Fin (2 * (L.length / 2))) = Fintype.card (Fin L.length) := by
    obtain ⟨t, ht⟩ := hev
    simp only [Fintype.card_fin]
    omega
  exact ((Fintype.bijective_iff_injective_and_card _).2 ⟨cutEndIndex_injective, hcard⟩).2

omit [Fintype H] [DecidableEq H] in
/-- For `N` even, the map `r ↦ r + s` modulo `N` commutes with `r ↦ r + 1`. -/
theorem cutEndIndex_finRotate (hev : Even L.length) (r : Fin (2 * (L.length / 2))) :
    cutEndIndex (H := H) L s (finRotate _ r) = finRotate _ (cutEndIndex L s r) := by
  have h2 : 2 * (L.length / 2) = L.length := by obtain ⟨t, ht⟩ := hev; omega
  apply Fin.ext
  rcases r with ⟨r, hr⟩
  simp only [cutEndIndex, val_finRotate_eq]
  rw [h2, Nat.mod_add_mod, Nat.mod_add_mod, show r + 1 + s = r + s + 1 by ring]

omit [Fintype H] in
/-- The end dart `ε'(r)` of the cut is `g_{r+s}`. -/
theorem cut_endDart (r : Fin (2 * (L.length / 2))) :
    (X.cut K L s).endDart r = cutListDart K L (cutEndIndex L s r) := rfl

namespace IsCutData

variable (hc : X.IsCutData K L)

include hc

/-- The endpoint `ε'(r)` of the cut is the triple `{g_k, ᾱ_k, α_{k-1}}` for `k = r + s`. -/
theorem cut_endpoint (r : Fin (2 * (L.length / 2))) :
    (X.cut K L s).endpoint r = cutTriple K L (cutEndIndex L s r) := by
  rw [endpoint, cut_endDart, hc.cut_vertexOf_cutListDart]

/-- The triples `{g_k, ᾱ_k, α_{k-1}}` are pairwise distinct. -/
theorem cutTriple_injective : Function.Injective (cutTriple K L) := by
  intro k k' h
  have hmem : cutListDart K L k ∈ cutTriple K L k' := by
    rw [← h]
    simp [cutTriple]
  simp only [cutTriple, mem_insert, mem_singleton, hc.cutListDart_eq, reduceCtorEq, or_false,
    Sum.inl.injEq, Subtype.mk.injEq] at hmem
  exact Fin.ext ((hc.nodup.getElem_inj_iff).1 hmem)

/-- Exactly two darts of the triple `{g_k, ᾱ_k, α_{k-1}}` are boundary darts of the cut. -/
theorem filter_cutTriple_mem_bdry (k : Fin L.length) :
    ((cutTriple K L k).filter (· ∈ (X.cut K L s).bdry)).card = 2 := by
  have : (cutTriple K L k).filter (· ∈ (X.cut K L s).bdry) =
      {.inr (k, false), .inr ((finRotate _).symm k, true)} := by
    ext x
    simp only [cutTriple, mem_filter, mem_insert, mem_singleton, mem_cut_bdry, hc.cutListDart_eq]
    constructor
    · rintro ⟨rfl | rfl | rfl, h⟩
      · simp at h
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨Or.inr (Or.inr rfl), rfl⟩
  rw [this, card_pair (by simp)]

/-- The exterior of the cut: the darts `α_k`. -/
theorem cut_faceOf_inr_true (hinv : Function.Involutive X.inv) (hN : 0 < L.length)
    (k : Fin L.length) :
    (X.cut K L s).faceOf (.inr (k, true)) = univ.image fun j => .inr (j, true) := by
  have hφ : ∀ j : Fin L.length, (X.cut K L s).facePerm (.inr (j, true)) =
      .inr ((finRotate _).symm j, true) := fun j => by
    rw [RotationSystem.facePerm_apply, hc.cut_inv_inr hinv, Bool.not_true,
      hc.cut_rot_inr_false]
  -- every `α_j` reaches `α_0`
  have h0 : ∀ n (hn : n < L.length),
      ((X.cut K L s).facePerm ^ n) (.inr (⟨n, hn⟩, true)) = .inr (⟨0, hN⟩, true) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [pow_succ, Equiv.Perm.mul_apply, hφ, val_finRotate_symm_succ hn]
      exact ih (by omega)
  have hsame : ∀ j : Fin L.length, (X.cut K L s).facePerm.SameCycle (.inr (j, true))
      (.inr (⟨0, hN⟩, true)) := fun j =>
    ⟨(j : ℕ), by rw [zpow_natCast]; exact h0 j j.isLt⟩
  ext x
  rw [RotationSystem.mem_faceOf, mem_image]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact ⟨k, mem_univ _, rfl⟩
    | succ n ih =>
      obtain ⟨j, -, hj⟩ := ih
      rw [pow_succ', Equiv.Perm.mul_apply, ← hj, hφ]
      exact ⟨_, mem_univ _, rfl⟩
  · rintro ⟨j, -, rfl⟩
    exact (hsame k).trans (hsame j).symm

end IsCutData

/-- **The cut is a pre-triple diagram**: if `X` is a pre-triple diagram, `(K, L)` satisfy
`IsCutData`, `L` has an even length `N ≥ 2` and the orientations along `L` alternate, with
`o(g_k) = out` exactly when `k + s` is even, then the cut along `(K, L)` with shift `s` is a
pre-triple diagram. -/
theorem IsCutData.isPreTripleDiagram_cut (hc : X.IsCutData K L) (hX : X.IsPreTripleDiagram)
    (hN : 2 ≤ L.length) (hev : Even L.length)
    (hO : ∀ k : Fin L.length, X.isOut L[(k : ℕ)] = decide (Even ((k : ℕ) + s))) :
    (X.cut K L s).IsPreTripleDiagram where
  one_le := by omega
  nonempty := ⟨.inr (⟨0, by omega⟩, true)⟩
  inv_involutive := hc.cut_inv_involutive hX.inv_involutive
  inv_ne := by
    rintro (d | ⟨k, β⟩)
    · rw [hc.cut_inv_inl hX.inv_involutive]
      intro h
      exact hX.inv_ne d.1 (congrArg Subtype.val (Sum.inl_injective h))
    · rw [hc.cut_inv_inr hX.inv_involutive]
      cases β <;> simp
  inv_mem_bdry := by
    intro x hx
    rw [mem_cut_bdry] at hx ⊢
    rcases x with d | ⟨k, β⟩
    · simp at hx
    · rw [hc.cut_inv_inr hX.inv_involutive]
      rfl
  boundaryVertex_card := by
    intro v hv
    obtain ⟨hvV, hbv⟩ := (X.cut K L s).mem_boundaryVertices.1 hv
    obtain ⟨x, rfl⟩ := (X.cut K L s).mem_vertices.1 hvV
    rcases hc.cutDart_cases x with ⟨d, hd, rfl⟩ | ⟨k, hk⟩
    · exact absurd hbv (hc.cut_not_isBoundaryVertex_vertexOf_inl hd)
    · rw [hc.cut_vertexOf_of_mem_cutTriple hk]
      exact ⟨hc.card_cutTriple k, hc.filter_cutTriple_mem_bdry k⟩
  exists_orbit := by
    have hN0 : 0 < L.length := by omega
    refine ⟨_, (X.cut K L s).faceOf_mem_faceOrbits (.inr (⟨0, hN0⟩, true)), ?_, ?_, ?_⟩
    · rw [hc.cut_faceOf_inr_true hX.inv_involutive hN0]
      intro x hx
      obtain ⟨j, -, rfl⟩ := mem_image.1 hx
      simp [mem_cut_bdry]
    · rw [hc.cut_faceOf_inr_true hX.inv_involutive hN0]
      ext x
      rw [mem_union, mem_map_equiv, mem_cut_bdry, mem_image, mem_image]
      rcases x with d | ⟨k, _ | _⟩
      · have : (X.cut K L s).inv.symm (.inl d) = .inl ⟨X.inv d.1, hc.inv_mem _ d.2⟩ := by
          rw [Equiv.symm_apply_eq, hc.cut_inv_inl hX.inv_involutive]
          congr 1
          exact Subtype.ext (hX.inv_involutive _).symm
        simp [this]
      · have : (X.cut K L s).inv.symm (.inr (k, false)) = .inr (k, true) := by
          rw [Equiv.symm_apply_eq, hc.cut_inv_inr hX.inv_involutive]
          rfl
        simp only [this, Sum.isRight_inr, iff_true]
        exact Or.inr ⟨k, mem_univ _, rfl⟩
      · simp only [Sum.isRight_inr, iff_true]
        exact Or.inl ⟨k, mem_univ _, rfl⟩
    · rw [hc.cut_faceOf_inr_true hX.inv_involutive hN0, disjoint_left]
      intro x hx hx'
      obtain ⟨j, -, rfl⟩ := mem_image.1 hx
      rw [mem_map_equiv] at hx'
      have : (X.cut K L s).inv.symm (.inr (j, true)) = .inr (j, false) := by
        rw [Equiv.symm_apply_eq, hc.cut_inv_inr hX.inv_involutive]
        rfl
      rw [this] at hx'
      obtain ⟨i, -, hi⟩ := mem_image.1 hx'
      simp at hi
  internalVertex_card := by
    intro v hv
    obtain ⟨hvV, hbv⟩ := (X.cut K L s).mem_internalVertices.1 hv
    obtain ⟨x, rfl⟩ := (X.cut K L s).mem_vertices.1 hvV
    obtain ⟨d, hd, rfl⟩ := hc.cut_not_isBoundaryVertex_iff.1 hbv
    rw [hc.cut_vertexOf_inl_of_notMem d hd,
      card_liftVertex fun e he => (hc.mem_of_mem_vertexOf d.1 d.2 hd e he).1]
    exact hX.internalVertex_card _
      (X.vertexOf_mem_internalVertices.2 (hc.not_isBoundaryVertex d.1 d.2 hd))
  endDart_notMem_bdry := by
    intro r
    rw [cut_endDart, hc.cutListDart_eq, mem_cut_bdry]
    simp
  endpoint_mem := by
    intro r
    refine (X.cut K L s).mem_boundaryVertices.2 ⟨(X.cut K L s).vertexOf_mem_vertices _, ?_⟩
    exact hc.cut_isBoundaryVertex_vertexOf_of_mem_cutTriple (k := cutEndIndex L s r)
      (by rw [cut_endDart]; simp [cutTriple])
  endpoint_injective := by
    intro r r' h
    rw [hc.cut_endpoint, hc.cut_endpoint] at h
    exact cutEndIndex_injective (hc.cutTriple_injective h)
  exists_endpoint_eq := by
    intro v hv
    obtain ⟨hvV, hbv⟩ := (X.cut K L s).mem_boundaryVertices.1 hv
    obtain ⟨x, rfl⟩ := (X.cut K L s).mem_vertices.1 hvV
    rcases hc.cutDart_cases x with ⟨d, hd, rfl⟩ | ⟨k, hk⟩
    · exact absurd hbv (hc.cut_not_isBoundaryVertex_vertexOf_inl hd)
    · obtain ⟨r, hr⟩ := cutEndIndex_surjective (s := s) hev k
      refine ⟨r, ?_⟩
      rw [hc.cut_endpoint, hr, hc.cut_vertexOf_of_mem_cutTriple hk]
  exists_exterior := by
    intro r
    refine ⟨.inr (cutEndIndex L s r, true), ?_, ?_, ?_⟩
    · rw [DiskMap.mem_exterior, mem_cut_bdry, mem_cut_bdry, hc.cut_rot_inr_true,
        hc.cutListDart_eq]
      simp
    · rw [hc.cut_endpoint, cutEndIndex_finRotate hev]
      simp only [cutTriple, mem_insert, mem_singleton, Equiv.symm_apply_apply, or_true]
    · rw [hc.cut_endpoint, hc.cut_inv_inr hX.inv_involutive]
      simp [cutTriple]
  isOut_inv := by
    intro x hx
    rcases x with d | ⟨k, β⟩
    · rw [hc.cut_inv_inl hX.inv_involutive]
      exact hX.isOut_inv d.1 (hc.notMem_bdry d.1 d.2)
    · simp [mem_cut_bdry] at hx
  isOut_rot := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := hc.cut_not_isBoundaryVertex_iff.1 hx
    rw [hc.cut_rot_inl_of_notMem d hd]
    exact hX.isOut_rot d.1 (hc.not_isBoundaryVertex d.1 d.2 hd)
  isOut_source := by
    intro j
    rw [cut_endDart, hc.cutListDart_eq]
    change X.isOut _ = true
    rw [hO, decide_eq_true_iff]
    simp only [cutEndIndex, sourceIndex_val]
    rw [even_mod_add_iff hev, show 2 * (j : ℕ) + s + s = 2 * ((j : ℕ) + s) by ring]
    exact even_two_mul _
  isOut_target := by
    intro j
    rw [cut_endDart, hc.cutListDart_eq]
    change X.isOut _ = false
    rw [hO, decide_eq_false_iff_not]
    simp only [cutEndIndex, targetIndex_val]
    rw [even_mod_add_iff hev, show 2 * (j : ℕ) + 1 + s + s = 2 * ((j : ℕ) + s) + 1 by ring,
      Nat.not_even_iff_odd]
    exact odd_two_mul_add_one _

end CutPreTriple

/-! ### Transitivity and faces of the cut -/

section CutGlobal

variable {X} {K : Finset H} {L : List H} {s : ℕ}

/-- The darts of the cut over `K`. -/
private def leftSet (K : Finset H) (N : ℕ) : Set (CutDart K N) := {x | x.isLeft}

/-- The correspondence between `K` and the darts of the cut over `K`. -/
private def toLeft (K : Finset H) (N : ℕ) (y : (K : Set H)) : leftSet K N :=
  ⟨.inl ⟨y.1, y.2⟩, rfl⟩

omit [Fintype H] [DecidableEq H] in
private theorem toLeft_injective (N : ℕ) : Function.Injective (toLeft K N) := by
  intro y y' h
  have := congrArg (fun z : leftSet K N => (z : CutDart K N)) h
  simp only [toLeft, Sum.inl.injEq, Subtype.mk.injEq] at this
  exact Subtype.ext this

namespace IsCutData

variable (hc : X.IsCutData K L)

include hc

/-- **Transitivity of the cut**: if `K` is the smallest set of darts containing `L` and closed
under `d ↦ d̄` and under `σ` at the darts of `K` outside `L`, then every dart of the cut reaches
every other. -/
theorem reach_cut (hinv : Function.Involutive X.inv) (hN : 0 < L.length)
    (hK : ∀ C : Set H, (∀ d ∈ L, d ∈ C) → (∀ d ∈ C, d ∈ K → X.inv d ∈ C) →
      (∀ d ∈ C, d ∈ K → d ∉ L → X.rot d ∈ C) → ∀ d ∈ K, d ∈ C)
    (x y : CutDart K L.length) : (X.cut K L s).Reach x y := by
  let α₀ : CutDart K L.length := .inr (⟨0, hN⟩, true)
  have hα : ∀ n (hn : n < L.length), (X.cut K L s).Reach α₀ (.inr (⟨n, hn⟩, true)) := by
    intro n
    induction n with
    | zero => intro _; exact .refl _
    | succ n ih =>
      intro hn
      have h3 := ((ih (by omega)).rot.rot).inv
      have e : (X.cut K L s).inv ((X.cut K L s).rot ((X.cut K L s).rot
          (.inr (⟨n, by omega⟩, true)))) = (.inr (⟨n + 1, hn⟩, true) : CutDart K L.length) := by
        rw [hc.cut_rot_inr_true, hc.cut_rot_cutListDart, hc.cut_inv_inr hinv]
        congr
        apply Fin.ext
        rw [val_finRotate_eq, Nat.mod_eq_of_lt hn]
      rw [e] at h3
      exact h3
  have hα' : ∀ k : Fin L.length, (X.cut K L s).Reach α₀ (.inr (k, true)) := fun k => hα k k.isLt
  have hg : ∀ k : Fin L.length, (X.cut K L s).Reach α₀ (cutListDart K L k) := fun k => by
    have := (hα' ((finRotate _).symm k)).rot
    rwa [hc.cut_rot_inr_true, Equiv.apply_symm_apply] at this
  have hα'' : ∀ k : Fin L.length, (X.cut K L s).Reach α₀ (.inr (k, false)) := fun k => by
    have := (hα' k).inv
    rwa [hc.cut_inv_inr hinv] at this
  have hKC := hK {d | ∃ h : d ∈ K, (X.cut K L s).Reach α₀ (.inl ⟨d, h⟩)}
    (fun d hd => by
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
      refine ⟨hc.getElem_mem ⟨k, hk⟩, ?_⟩
      have := hg ⟨k, hk⟩
      rwa [hc.cutListDart_eq] at this)
    (fun d ⟨h, hr⟩ _ => ⟨hc.inv_mem d h, by
      have := hr.inv
      rwa [hc.cut_inv_inl hinv] at this⟩)
    (fun d ⟨h, hr⟩ _ hL => ⟨hc.rot_mem h hL, by
      have := hr.rot
      rwa [hc.cut_rot_inl_of_notMem ⟨d, h⟩ hL] at this⟩)
  have hall : ∀ z, (X.cut K L s).Reach α₀ z := by
    rintro (d | ⟨k, _ | _⟩)
    · exact (hKC d.1 d.2).2
    · exact hα'' k
    · exact hα' k
  exact (hall x).symm.trans (hall y)

/-- **The cut is connected** under the hypotheses of `reach_cut`. -/
theorem isConnected_cut (hX : X.IsPreTripleDiagram) (hN : 0 < L.length)
    (hK : ∀ C : Set H, (∀ d ∈ L, d ∈ C) → (∀ d ∈ C, d ∈ K → X.inv d ∈ C) →
      (∀ d ∈ C, d ∈ K → d ∉ L → X.rot d ∈ C) → ∀ d ∈ K, d ∈ C) :
    (X.cut K L s).IsConnected := by
  refine RotationSystem.IsConnected.of_reach ⟨.inr (⟨0, hN⟩, true)⟩
    (hc.cut_inv_involutive hX.inv_involutive) ?_ (hc.reach_cut hX.inv_involutive hN hK)
  rintro (d | ⟨k, β⟩)
  · rw [hc.cut_inv_inl hX.inv_involutive]
    intro h
    exact hX.inv_ne d.1 (congrArg Subtype.val (Sum.inl_injective h))
  · rw [hc.cut_inv_inr hX.inv_involutive]
    cases β <;> simp

section Faces

variable (hinv : Function.Involutive X.inv)

include hinv

/-- The face permutation of the cut is `φ` on a dart `d` of `K` with `d̄ ∉ L`. -/
theorem cut_facePerm_inl_of_notMem (d : {d // d ∈ K}) (hd : X.inv d.1 ∉ L) :
    (X.cut K L s).facePerm (.inl d) =
      .inl ⟨X.facePerm d.1, hc.rot_mem (hc.inv_mem _ d.2) hd⟩ := by
  rw [RotationSystem.facePerm_apply, hc.cut_inv_inl hinv,
    hc.cut_rot_inl_of_notMem ⟨_, hc.inv_mem _ d.2⟩ hd]
  rfl

/-- The face permutation of the cut sends a dart `d` of `K` with `d̄ = g_k` to `ᾱ_k`. -/
theorem cut_facePerm_inl_of_eq (d : {d // d ∈ K}) (k : Fin L.length)
    (hd : X.inv d.1 = L[(k : ℕ)]) : (X.cut K L s).facePerm (.inl d) = .inr (k, false) := by
  rw [RotationSystem.facePerm_apply, hc.cut_inv_inl hinv]
  have : (⟨X.inv d.1, hc.inv_mem _ d.2⟩ : {d // d ∈ K}) = ⟨L[(k : ℕ)], hc.getElem_mem k⟩ :=
    Subtype.ext hd
  rw [this, ← hc.cutListDart_eq, hc.cut_rot_cutListDart]

/-- The face permutation of the cut sends `ᾱ_k` to `g_{k+1}`. -/
theorem cut_facePerm_inr_false (k : Fin L.length) :
    (X.cut K L s).facePerm (.inr (k, false)) = cutListDart K L (finRotate _ k) := by
  rw [RotationSystem.facePerm_apply, hc.cut_inv_inr hinv, Bool.not_false, hc.cut_rot_inr_true]

/-- Along the cut, the first return of `φ'` to the darts over `K` is the first return of `φ` to
`K`, provided that from `σ(g_k)` the orbit of `φ` runs outside `K` to `g_{k+1}`. -/
private theorem firstReturn_toLeft
    (hF : ∀ k : Fin L.length, ∃ t, (X.facePerm ^ (t + 1)) (X.inv L[(k : ℕ)]) =
      L[((finRotate _ k : Fin L.length) : ℕ)] ∧
      ∀ j, 0 < j → j ≤ t → (X.facePerm ^ j) (X.inv L[(k : ℕ)]) ∉ K)
    (y : (K : Set H)) :
    firstReturn (X.cut K L s).facePerm (leftSet K L.length) (toLeft K L.length y) =
      toLeft K L.length (firstReturn X.facePerm (K : Set H) y) := by
  obtain ⟨y, hy⟩ := y
  have hyK : y ∈ K := hy
  apply Subtype.ext
  by_cases hL : X.inv y ∈ L
  · obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hL
    obtain ⟨t, ht, hmin⟩ := hF ⟨k, hk⟩
    have hyk : X.inv L[k] = y := by rw [hkd, hinv]
    simp only at ht hmin
    rw [hyk] at ht hmin
    have h1 : (firstReturn X.facePerm (K : Set H) ⟨y, hy⟩ : H) = (X.facePerm ^ (t + 1)) y := by
      apply coe_firstReturn_of_pow (by omega)
      · rw [ht]
        exact hc.getElem_mem _
      · intro j hj hjt
        exact hmin j hj (by omega)
    have hφ1 : (X.cut K L s).facePerm (.inl ⟨y, hyK⟩) = .inr (⟨k, hk⟩, false) :=
      hc.cut_facePerm_inl_of_eq hinv ⟨y, hyK⟩ ⟨k, hk⟩ hkd.symm
    have hφ2 : ((X.cut K L s).facePerm ^ 2) (.inl ⟨y, hyK⟩) =
        .inl ⟨L[((finRotate _ ⟨k, hk⟩ : Fin L.length) : ℕ)], hc.getElem_mem _⟩ := by
      rw [pow_two, Equiv.Perm.mul_apply, hφ1, hc.cut_facePerm_inr_false hinv, hc.cutListDart_eq]
    have h2 : (firstReturn (X.cut K L s).facePerm (leftSet K L.length)
        (toLeft K L.length ⟨y, hy⟩) : CutDart K L.length) =
        ((X.cut K L s).facePerm ^ 2) (.inl ⟨y, hyK⟩) := by
      apply coe_firstReturn_of_pow (by omega)
      · change ((X.cut K L s).facePerm ^ 2) (Sum.inl ⟨y, hyK⟩) ∈ leftSet K L.length
        rw [hφ2]
        rfl
      · intro j hj hj2
        obtain rfl : j = 1 := by omega
        rw [pow_one]
        change ((X.cut K L s).facePerm (.inl ⟨y, hyK⟩)).isLeft ≠ true
        rw [hφ1]
        simp
    rw [h2, hφ2]
    simp only [toLeft, h1, ht]
  · have hmem : X.facePerm y ∈ (K : Set H) := hc.rot_mem (hc.inv_mem _ hyK) hL
    have h1 := coe_firstReturn_of_apply_mem (π := X.facePerm) (Y := (K : Set H))
      (y := ⟨y, hy⟩) hmem
    have hφ := hc.cut_facePerm_inl_of_notMem (s := s) hinv ⟨y, hyK⟩ hL
    have h2 := coe_firstReturn_of_apply_mem (π := (X.cut K L s).facePerm)
      (Y := leftSet K L.length) (y := toLeft K L.length ⟨y, hy⟩)
      (by change ((X.cut K L s).facePerm (.inl ⟨y, hyK⟩)).isLeft = true; rw [hφ]; rfl)
    rw [h2]
    change (X.cut K L s).facePerm (.inl ⟨y, hyK⟩) = _
    rw [hφ]
    simp only [toLeft, h1]

private theorem iterate_firstReturn_toLeft
    (hF : ∀ k : Fin L.length, ∃ t, (X.facePerm ^ (t + 1)) (X.inv L[(k : ℕ)]) =
      L[((finRotate _ k : Fin L.length) : ℕ)] ∧
      ∀ j, 0 < j → j ≤ t → (X.facePerm ^ j) (X.inv L[(k : ℕ)]) ∉ K)
    (n : ℕ) (y : (K : Set H)) :
    (firstReturn (X.cut K L s).facePerm (leftSet K L.length))^[n] (toLeft K L.length y) =
      toLeft K L.length ((firstReturn X.facePerm (K : Set H))^[n] y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      hc.firstReturn_toLeft hinv hF, ih]

/-- Two darts of `K` lie in one orbit of `φ'` exactly when they lie in one orbit of `φ`. -/
theorem cut_sameCycle_facePerm_inl_iff
    (hF : ∀ k : Fin L.length, ∃ t, (X.facePerm ^ (t + 1)) (X.inv L[(k : ℕ)]) =
      L[((finRotate _ k : Fin L.length) : ℕ)] ∧
      ∀ j, 0 < j → j ≤ t → (X.facePerm ^ j) (X.inv L[(k : ℕ)]) ∉ K)
    (y y' : {d // d ∈ K}) :
    (X.cut K L s).facePerm.SameCycle (.inl y) (.inl y') ↔ X.facePerm.SameCycle y.1 y'.1 := by
  have key : ∀ {α : Type _} [Finite α] (f : Equiv.Perm α) (a a' : α),
      f.SameCycle a a' ↔ ∃ n : ℕ, a' = (f ^ n) a := fun f a a' =>
    ⟨fun h => let ⟨n, hn⟩ := h.exists_nat_pow_eq; ⟨n, hn.symm⟩,
      fun ⟨n, hn⟩ => ⟨n, by rw [zpow_natCast, hn]⟩⟩
  rw [key, key]
  have e1 := exists_iterate_firstReturn_eq_iff (X.cut K L s).facePerm (leftSet K L.length)
    (y := toLeft K L.length ⟨y.1, y.2⟩) (y' := toLeft K L.length ⟨y'.1, y'.2⟩)
  have e2 := exists_iterate_firstReturn_eq_iff X.facePerm (K : Set H)
    (y := ⟨y.1, y.2⟩) (y' := ⟨y'.1, y'.2⟩)
  change (∃ n : ℕ, (toLeft K L.length ⟨y'.1, y'.2⟩ : CutDart K L.length) =
    ((X.cut K L s).facePerm ^ n) (toLeft K L.length ⟨y.1, y.2⟩)) ↔ _
  rw [← e1, ← e2]
  simp only [hc.iterate_firstReturn_toLeft hinv hF]
  exact exists_congr fun n => (toLeft_injective L.length).eq_iff

end Faces

end IsCutData

end CutGlobal

/-! ### Counting the vertices, edges and faces of the cut -/

section Counting

/-- Two maps that identify the same pairs of points of `s` have images of the same size. -/
private theorem card_image_eq_of_iff {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    {s : Finset α} {f : α → β} {g : α → γ} (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    (s.image f).card = (s.image g).card := by
  refine Finset.card_bij (fun c hc => g (mem_image.1 hc).choose) (fun c hc => ?_)
    (fun c₁ hc₁ c₂ hc₂ heq => ?_) (fun c hc => ?_)
  · exact mem_image_of_mem _ (mem_image.1 hc).choose_spec.1
  · have e₁ := (mem_image.1 hc₁).choose_spec
    have e₂ := (mem_image.1 hc₂).choose_spec
    rw [← e₁.2, ← e₂.2]
    exact (h _ e₁.1 _ e₂.1).2 heq
  · obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
    refine ⟨f x, mem_image_of_mem _ hx, ?_⟩
    have e := (mem_image.1 (mem_image_of_mem f hx)).choose_spec
    exact (h _ e.1 _ hx).1 e.2

/-- A rotation system whose involution is fixed-point-free has half as many edges as darts. -/
private theorem two_mul_card_edges' (R : RotationSystem H)
    (hinv : Function.Involutive R.inv) (hfix : ∀ d, R.inv d ≠ d) :
    2 * R.edges.card = Fintype.card H := by
  have hfib : ∀ s ∈ univ.image R.edgeOf,
      ({a ∈ univ | R.edgeOf a = s} : Finset H).card = 2 := by
    intro s hs
    obtain ⟨d, -, rfl⟩ := mem_image.1 hs
    have : ({a ∈ univ | R.edgeOf a = R.edgeOf d} : Finset H) = R.edgeOf d := by
      ext a
      simp only [mem_filter, mem_univ, true_and, RotationSystem.mem_edgeOf]
      constructor
      · exact fun h => R.mem_edgeOf.1 (h ▸ R.mem_edgeOf.2 (Or.inl rfl))
      · rintro (rfl | rfl)
        · rfl
        · ext x
          simp only [RotationSystem.mem_edgeOf, hinv d]
          tauto
    rw [this, RotationSystem.edgeOf, card_pair (hfix d).symm]
  rw [← card_univ, card_eq_sum_card_image R.edgeOf univ, sum_const_nat hfib,
    RotationSystem.edges, mul_comm]

/-- If a set `D` of darts is a union of vertices of `c` darts each, then `D` has `c` times as many
darts as vertices. -/
private theorem mul_card_image_vertexOf (R : RotationSystem H) {D : Finset H} {c : ℕ}
    (hD : ∀ d ∈ D, ∀ e ∈ R.vertexOf d, e ∈ D)
    (hc : ∀ d ∈ D, (R.vertexOf d).card = c) : c * (D.image R.vertexOf).card = D.card := by
  have hfib : ∀ v ∈ D.image R.vertexOf, ({a ∈ D | R.vertexOf a = v} : Finset H).card = c := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hv
    have : ({a ∈ D | R.vertexOf a = R.vertexOf d} : Finset H) = R.vertexOf d := by
      ext a
      simp only [mem_filter]
      exact ⟨fun ⟨_, h⟩ => h ▸ R.self_mem_vertexOf a,
        fun h => ⟨hD d hd a h, R.vertexOf_eq_of_mem h⟩⟩
    rw [this, hc d hd]
  rw [card_eq_sum_card_image R.vertexOf D, sum_const_nat hfib, mul_comm]

variable {X}

/-- In a pre-triple diagram with `b` arcs, `6 |V| = |H| + 6b`: the `2b` endpoints have three
darts each and the triple points six. -/
private theorem IsPreTripleDiagram.six_mul_card_vertices (hX : X.IsPreTripleDiagram) :
    6 * X.vertices.card = Fintype.card H + 6 * b := by
  set Db : Finset H := univ.filter fun d => X.IsBoundaryVertex (X.vertexOf d) with hDb
  set Di : Finset H := univ.filter fun d => ¬X.IsBoundaryVertex (X.vertexOf d) with hDi
  have hsplit : Db.card + Di.card = Fintype.card H := by
    rw [hDb, hDi, card_filter_add_card_filter_not, card_univ]
  have hVb : Db.image X.vertexOf = X.boundaryVertices := by
    ext v
    simp only [hDb, mem_image, mem_filter, mem_univ, true_and, DiskMap.mem_boundaryVertices,
      RotationSystem.mem_vertices]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, rfl⟩, hd⟩
    · rintro ⟨⟨d, rfl⟩, hd⟩
      exact ⟨d, hd, rfl⟩
  have hVi : Di.image X.vertexOf = X.internalVertices := by
    ext v
    simp only [hDi, mem_image, mem_filter, mem_univ, true_and, DiskMap.mem_internalVertices,
      RotationSystem.mem_vertices]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, rfl⟩, hd⟩
    · rintro ⟨⟨d, rfl⟩, hd⟩
      exact ⟨d, hd, rfl⟩
  have h3 := mul_card_image_vertexOf X.toRotationSystem (D := Db) (c := 3)
    (fun d hd e he => by
      simp only [hDb, mem_filter, mem_univ, true_and] at hd ⊢
      rwa [X.vertexOf_eq_of_mem he])
    (fun d hd => (hX.boundaryVertex_card _ (X.vertexOf_mem_boundaryVertices.2
      (mem_filter.1 hd).2)).1)
  have h6 := mul_card_image_vertexOf X.toRotationSystem (D := Di) (c := 6)
    (fun d hd e he => by
      simp only [hDi, mem_filter, mem_univ, true_and] at hd ⊢
      rwa [X.vertexOf_eq_of_mem he])
    (fun d hd => hX.internalVertex_card _ (X.vertexOf_mem_internalVertices.2
      (mem_filter.1 hd).2))
  have hb : X.boundaryVertices.card = 2 * b := by
    have : X.boundaryVertices = univ.image X.endpoint := by
      ext v
      simp only [mem_image, mem_univ, true_and]
      constructor
      · intro hv
        exact hX.exists_endpoint_eq v hv
      · rintro ⟨r, rfl⟩
        exact hX.endpoint_mem r
    rw [this, card_image_of_injective _ hX.endpoint_injective, card_univ, Fintype.card_fin]
  have hV : X.vertices.card = X.boundaryVertices.card + X.internalVertices.card := by
    rw [DiskMap.boundaryVertices, DiskMap.internalVertices, card_filter_add_card_filter_not]
  rw [hVb] at h3
  rw [hVi] at h6
  omega

end Counting

section CutCount

variable {X} {K : Finset H} {L : List H} {s : ℕ}

namespace IsCutData

variable (hc : X.IsCutData K L)

include hc

/-- **The faces of the cut**: if from `σ(g_k)` the orbit of `φ` runs outside `K` to `g_{k+1}`,
then the orbits of `φ'` are the exterior `{α_k}` and one orbit for each orbit of `φ` meeting
`K`. -/
theorem card_faceOrbits_cut (hinv : Function.Involutive X.inv) (hN : 0 < L.length)
    (hF : ∀ k : Fin L.length, ∃ t, (X.facePerm ^ (t + 1)) (X.inv L[(k : ℕ)]) =
      L[((finRotate _ k : Fin L.length) : ℕ)] ∧
      ∀ j, 0 < j → j ≤ t → (X.facePerm ^ j) (X.inv L[(k : ℕ)]) ∉ K) :
    (X.cut K L s).faceOrbits.card = (K.image X.faceOf).card + 1 := by
  have hfo : (X.cut K L s).faceOrbits = insert ((X.cut K L s).faceOf (.inr (⟨0, hN⟩, true)))
      ((univ : Finset {d // d ∈ K}).image fun y => (X.cut K L s).faceOf (.inl y)) := by
    ext f
    simp only [RotationSystem.mem_faceOrbits, mem_insert, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      rcases x with y | ⟨k, _ | _⟩
      · exact Or.inr ⟨y, rfl⟩
      · refine Or.inr ⟨⟨L[((finRotate _ k : Fin L.length) : ℕ)], hc.getElem_mem _⟩, ?_⟩
        rw [← (X.cut K L s).faceOf_facePerm (.inr (k, false)), hc.cut_facePerm_inr_false hinv,
          hc.cutListDart_eq]
      · left
        rw [hc.cut_faceOf_inr_true hinv hN, hc.cut_faceOf_inr_true hinv hN]
    · rintro (h | ⟨y, h⟩)
      · exact ⟨_, h.symm⟩
      · exact ⟨_, h⟩
  rw [hfo, card_insert_of_notMem]
  · congr 1
    have hK : K.image X.faceOf = (univ : Finset {d // d ∈ K}).image fun y => X.faceOf y.1 := by
      ext f
      simp only [mem_image, mem_univ, true_and, Subtype.exists]
      exact ⟨fun ⟨d, hd, e⟩ => ⟨d, hd, e⟩, fun ⟨d, hd, e⟩ => ⟨d, hd, e⟩⟩
    rw [hK]
    apply card_image_eq_of_iff
    intro y _ y' _
    rw [RotationSystem.faceOf_eq_faceOf_iff, RotationSystem.faceOf_eq_faceOf_iff]
    exact hc.cut_sameCycle_facePerm_inl_iff hinv hF y y'
  · intro hmem
    obtain ⟨y, -, hy⟩ := mem_image.1 hmem
    have : (.inl y : CutDart K L.length) ∈ (X.cut K L s).faceOf (.inr (⟨0, hN⟩, true)) :=
      hy ▸ (X.cut K L s).self_mem_faceOf _
    rw [hc.cut_faceOf_inr_true hinv hN] at this
    obtain ⟨j, -, hj⟩ := mem_image.1 this
    simp at hj

omit [Fintype H] [DecidableEq H] hc in
/-- The number of darts of the cut. -/
theorem card_cutDart : Fintype.card (CutDart K L.length) = K.card + 2 * L.length := by
  simp only [Fintype.card_sum, Fintype.card_coe, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  ring

end IsCutData

end CutCount

end TripleData

/-! ### The cut along a simple arc -/

namespace StrandSide

/-- The value of the winding function of a simple arc on the side `ζ`: `-1` on the right and `0`
on the left. -/
def arcValue : StrandSide → ℤ
  | right => -1
  | left => 0

/-- The shift of the labels of the endpoints of a cut on the side `ζ`: the endpoint `ε'(r)` of the
cut is the cycle of `g_{r+s}` (labels `0`-indexed), with `s = 0` on the right and `s = 1` on the
left. -/
def cutShift : StrandSide → ℕ
  | right => 0
  | left => 1

end StrandSide

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)

/-- The darts `H_ζ(S)` on the side `ζ` of the simple arc `S` from `s_i`: `H_right(S)` or
`H_left(S)`. -/
noncomputable abbrev arcSideDarts (i : Fin b) (ζ : StrandSide) : Finset H :=
  X.arcSide i ζ.arcValue

/-- The `ζ` cut list `Λ_ζ` of the simple arc from `s_i`. -/
def arcCutList (i : Fin b) : StrandSide → List H
  | .right => X.rightCutList i
  | .left => X.leftCutList i

/-- **The cut of a triple diagram along a simple arc**. Let `S` be the simple arc
from `s_i`, `ζ` a side and `Λ_ζ = (g₀, …, g_{N-1})` its `ζ` cut list. The cut `X|_{S,ζ}` has the
darts `H_ζ(S) ⊔ {α_k, ᾱ_k : k ∈ ℤ/N}`; its involution is `d ↦ d̄` on `H_ζ(S)` and exchanges `α_k`
and `ᾱ_k`; its rotation is `σ` on `H_ζ(S)` outside the cut list and consists of the `3`-cycles
`(g_k ᾱ_k α_{k-1})` on the remaining darts; `B' = {α_k, ᾱ_k}`; `o' = o`; and its endpoint
`ε'(r)` is the cycle of `g_{r-1}` on the right and of `g_r` on the left (labels `1`-indexed; with
the `0`-indexed labels `r : Fin (2 * (N / 2))` of the formalization, `g_r` and `g_{r+1}`). It has
`N / 2` arcs. -/
@[cluster_algebras "def_arc_cut"]
noncomputable def arcCut (i : Fin b) (ζ : StrandSide) :
    TripleData (CutDart (X.arcSideDarts i ζ) (X.arcCutList i ζ).length)
      ((X.arcCutList i ζ).length / 2) :=
  X.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift

/-! ### Clockwise distances -/

section CyclicDistance

variable {n : ℕ}

private theorem fin_val_sub (a c : Fin n) :
    ((a - c : Fin n) : ℕ) = if (c : ℕ) ≤ a then (a : ℕ) - c else n + (a : ℕ) - c := by
  split_ifs with h
  · exact Fin.coe_sub_iff_le.2 h
  · exact Fin.coe_sub_iff_lt.2 (not_le.1 h)

private theorem val_finRotate_pow (q : Fin n) (s : ℕ) :
    ((finRotate n ^ s) q : ℕ) = ((q : ℕ) + s) % n := by
  induction s with
  | zero => simp [Nat.mod_eq_of_lt q.isLt]
  | succ s ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, val_finRotate_eq, ih, Nat.mod_add_mod, add_assoc]

private theorem val_finRotate_pow_sub (q : Fin n) {s : ℕ} (hs : s < n) :
    (((finRotate n ^ s) q - q : Fin n) : ℕ) = s := by
  rw [fin_val_sub, val_finRotate_pow]
  have := q.isLt
  by_cases h : (q : ℕ) + s < n
  · rw [Nat.mod_eq_of_lt h]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega

private theorem finRotate_pow_val_sub (r q : Fin n) :
    (finRotate n ^ ((r - q : Fin n) : ℕ)) q = r := by
  apply Fin.ext
  rw [val_finRotate_pow, fin_val_sub]
  have := q.isLt
  have := r.isLt
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

private theorem val_sub_add_val_sub {p q : Fin n} (h : p ≠ q) :
    ((p - q : Fin n) : ℕ) + ((q - p : Fin n) : ℕ) = n := by
  have h' : (p : ℕ) ≠ q := fun e => h (Fin.ext e)
  rw [fin_val_sub, fin_val_sub]
  have := q.isLt
  have := p.isLt
  split_ifs <;> omega

private theorem finRotate_pow_succ (q : Fin n) (s : ℕ) :
    (finRotate n ^ (s + 1)) q = finRotate n ((finRotate n ^ s) q) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

private theorem finRotate_pow_injective (q : Fin n) {s t : ℕ} (hs : s < n) (ht : t < n)
    (h : (finRotate n ^ s) q = (finRotate n ^ t) q) : s = t := by
  have := congrArg (fun r : Fin n => ((r - q : Fin n) : ℕ)) h
  simpa only [val_finRotate_pow_sub q hs, val_finRotate_pow_sub q ht] using this

end CyclicDistance

/-! ### Facts on simple arcs -/

section ArcFacts

variable {X} {i : Fin b}

/-- The clockwise distance `q - p` from the start `ε(p)` of the arc from `s_i` to its end `ε(q)`,
the number of positions in its left run `p, p + 1, …, q - 1`. -/
private def leftRunLength (X : TripleData H b) (i : Fin b) : ℕ :=
  ((X.arcEndIndex i - sourceIndex i : Fin (2 * b)) : ℕ)

private theorem arcEndIndex_ne : X.arcEndIndex i ≠ sourceIndex i :=
  (sourceIndex_ne_targetIndex _ _).symm

private theorem rightRunLength_add_leftRunLength :
    X.rightRunLength i + X.leftRunLength i = 2 * b :=
  val_sub_add_val_sub arcEndIndex_ne.symm

private theorem rightRunLength_odd : Odd (X.rightRunLength i) := by
  rw [rightRunLength, fin_val_sub, arcEndIndex, sourceIndex_val, targetIndex_val]
  split_ifs with h
  · exact ⟨i - X.strandPerm i - 1, by omega⟩
  · exact ⟨b + i - X.strandPerm i - 1, by have := (X.strandPerm i).isLt; omega⟩

private theorem leftRunLength_odd : Odd (X.leftRunLength i) := by
  have h1 := rightRunLength_add_leftRunLength (X := X) (i := i)
  have h2 := rightRunLength_odd (X := X) (i := i)
  obtain ⟨t, ht⟩ := h2
  exact ⟨b - t - 1, by omega⟩

private theorem rightRunLength_pos : 0 < X.rightRunLength i := by
  obtain ⟨t, ht⟩ := rightRunLength_odd (X := X) (i := i)
  omega

private theorem leftRunLength_pos : 0 < X.leftRunLength i := by
  obtain ⟨t, ht⟩ := leftRunLength_odd (X := X) (i := i)
  omega

private theorem finRotate_pow_rightRunLength :
    (finRotate (2 * b) ^ X.rightRunLength i) (X.arcEndIndex i) = sourceIndex i :=
  finRotate_pow_val_sub _ _

private theorem finRotate_pow_leftRunLength :
    (finRotate (2 * b) ^ X.leftRunLength i) (sourceIndex i) = X.arcEndIndex i :=
  finRotate_pow_val_sub _ _

omit [Fintype H] [DecidableEq H] in
private theorem two_le_two_mul_b (i : Fin b) : 2 ≤ 2 * b := by
  have := i.isLt
  omega

/-- The leg `n_r` is `out` exactly when `r` (`0`-indexed) is even. -/
private theorem isOut_endDart (hX : X.IsTripleDiagram) (r : Fin (2 * b)) :
    X.isOut (X.endDart r) = decide (Even (r : ℕ)) := by
  rcases exists_sourceIndex_or_targetIndex r with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [hX.isOut_source]
    simp
  · rw [hX.isOut_target]
    simp

private theorem not_runsToEndpoint_arcDart (hX : X.IsTripleDiagram) {k : ℕ}
    (hk : k + 1 < X.arcLength i) : ¬X.RunsToEndpoint (X.arcDart i k) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (hX.toIsPreTripleDiagram.arcLength_ne_zero i)
  exact (X.arcLength_eq_succ_iff.1 hm).2 k (by omega)

private theorem arcLength_pos (hX : X.IsTripleDiagram) : 0 < X.arcLength i :=
  Nat.pos_of_ne_zero (hX.toIsPreTripleDiagram.arcLength_ne_zero i)

private theorem rot_endDart (hX : X.IsTripleDiagram) (r : Fin (2 * b)) :
    X.rot (X.endDart r) = X.inv (X.exteriorDart r) := by
  rw [exteriorDart, hX.inv_involutive]

private theorem facePerm_inv_exteriorDart (hX : X.IsTripleDiagram) (r : Fin (2 * b)) :
    X.facePerm (X.inv (X.exteriorDart r)) = X.endDart (finRotate _ r) := by
  rw [RotationSystem.facePerm_apply, hX.inv_involutive, rot_exteriorDart hX]

private theorem inv_exteriorDart_mem_bdry (hX : X.IsTripleDiagram) (r : Fin (2 * b)) :
    X.inv (X.exteriorDart r) ∈ X.bdry :=
  hX.inv_mem_bdry _ (X.exterior_subset_bdry (exteriorDart_mem_exterior hX r))

omit [Fintype H] [DecidableEq H] in
private theorem facePerm_eq (d : H) : X.facePerm d = X.rot (X.inv d) := rfl

private theorem notMem_arcSide_of_mem_bdry {d : H} {v : ℤ} (h : d ∈ X.bdry) :
    d ∉ X.arcSide i v := fun h' => (mem_arcSide.1 h').1 h

private theorem notMem_arcSide_of_mem_arcDarts {d : H} {v : ℤ} (h : d ∈ X.arcDarts i) :
    d ∉ X.arcSide i v := fun h' => (mem_arcSide.1 h').2.1 h

/-- The last dart `e_m` of the arc runs to `ε(q)`: `ē_m = n_q`. -/
private theorem inv_arcDart_last (hX : X.IsTripleDiagram) :
    X.inv (X.arcDart i (X.arcLength i - 1)) = X.endDart (X.arcEndIndex i) :=
  (endDart_arcEndIndex hX i).symm

/-! #### The cut lists, position by position -/

private theorem flatMap_pair {α : Type*} (f g : ℕ → α) (n : ℕ) :
    ((List.range n).flatMap fun k => [f k, g k]).length = 2 * n ∧
    ∀ j < 2 * n, ((List.range n).flatMap fun k => [f k, g k])[j]? =
      some (if j % 2 = 0 then f (j / 2) else g (j / 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hl, hg⟩ := ih
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    refine ⟨by simp only [List.length_append, hl, List.length_cons, List.length_nil]; ring,
      fun j hj => ?_⟩
    by_cases hj' : j < 2 * n
    · rw [List.getElem?_append_left (by rw [hl]; exact hj'), hg j hj']
    · rw [List.getElem?_append_right (by rw [hl]; omega), hl]
      obtain h | h : j = 2 * n ∨ j = 2 * n + 1 := by omega
      · subst h
        have h1 : 2 * n % 2 = 0 := by omega
        have h2 : 2 * n / 2 = n := by omega
        simp [h1, h2]
      · subst h
        have h1 : (2 * n + 1) % 2 = 1 := by omega
        have h2 : (2 * n + 1) / 2 = n := by omega
        simp [h1, h2]

private theorem flatMap_pair_reverse {α : Type*} (f g : ℕ → α) (n : ℕ) :
    ((List.range n).reverse.flatMap fun k => [f k, g k]).length = 2 * n ∧
    ∀ j < 2 * n, ((List.range n).reverse.flatMap fun k => [f k, g k])[j]? =
      some (if j % 2 = 0 then f (n - 1 - j / 2) else g (n - 1 - j / 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hl, hg⟩ := ih
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatMap_cons, List.cons_append]
    refine ⟨by simp only [List.length_cons, hl]; ring, fun j hj => ?_⟩
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j <;> simp
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      simp only [List.getElem?_cons_succ]
      rw [hg j' (by omega)]
      have e1 : (j' + 2) % 2 = j' % 2 := by omega
      have e2 : n + 1 - 1 - (j' + 2) / 2 = n - 1 - j' / 2 := by omega
      rw [e1, e2]

/-- The darts of the right cut list, position by position. -/
private def rightCutFun (X : TripleData H b) (i : Fin b) (j : ℕ) : H :=
  if j < X.rightRunLength i - 1 then X.endDart ((finRotate (2 * b) ^ (j + 1)) (X.arcEndIndex i))
  else (X.rot ^ ((j - (X.rightRunLength i - 1)) % 2 + 1))
    (X.inv (X.arcDart i ((j - (X.rightRunLength i - 1)) / 2)))

/-- The darts of the left cut list, position by position. -/
private def leftCutFun (X : TripleData H b) (i : Fin b) (j : ℕ) : H :=
  if j < X.leftRunLength i - 1 then X.endDart ((finRotate (2 * b) ^ (j + 1)) (sourceIndex i))
  else (X.rot ^ ((j - (X.leftRunLength i - 1)) % 2 + 4))
    (X.inv (X.arcDart i (X.arcLength i - 1 - 1 - (j - (X.leftRunLength i - 1)) / 2)))

private theorem leftCutList_eq : X.leftCutList i =
    (List.range (X.leftRunLength i - 1)).map
      (fun t => X.endDart ((finRotate (2 * b) ^ (t + 1)) (sourceIndex i))) ++
    (List.range (X.arcLength i - 1)).reverse.flatMap fun k =>
      [(X.rot ^ 4) (X.inv (X.arcDart i k)), (X.rot ^ 5) (X.inv (X.arcDart i k))] := rfl

private theorem length_rightCutList :
    (X.rightCutList i).length = X.rightRunLength i - 1 + 2 * (X.arcLength i - 1) := by
  rw [rightCutList, List.length_append, List.length_map, List.length_range,
    (flatMap_pair _ _ _).1]

private theorem length_leftCutList :
    (X.leftCutList i).length = X.leftRunLength i - 1 + 2 * (X.arcLength i - 1) := by
  rw [leftCutList_eq, List.length_append, List.length_map, List.length_range,
    (flatMap_pair_reverse _ _ _).1]

private theorem getElem?_rightCutList {j : ℕ} (hj : j < (X.rightCutList i).length) :
    (X.rightCutList i)[j]? = some (X.rightCutFun i j) := by
  have hl := length_rightCutList (X := X) (i := i)
  rw [rightCutList, rightCutFun]
  split_ifs with h1
  · rw [List.getElem?_append_left (by simpa using h1)]
    simp [h1]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map, List.length_range]
    rw [(flatMap_pair _ _ _).2 _ (by omega)]
    split_ifs with h2
    · rw [h2, zero_add, pow_one]
    · rw [show (j - (X.rightRunLength i - 1)) % 2 = 1 by omega]

private theorem getElem?_leftCutList {j : ℕ} (hj : j < (X.leftCutList i).length) :
    (X.leftCutList i)[j]? = some (X.leftCutFun i j) := by
  have hl := length_leftCutList (X := X) (i := i)
  rw [leftCutList_eq, leftCutFun]
  split_ifs with h1
  · rw [List.getElem?_append_left (by simpa using h1)]
    simp [h1]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map, List.length_range]
    rw [(flatMap_pair_reverse _ _ _).2 _ (by omega)]
    split_ifs with h2
    · rw [h2]
    · rw [show (j - (X.leftRunLength i - 1)) % 2 = 1 by omega]

private theorem getElem_rightCutList {j : ℕ} (hj : j < (X.rightCutList i).length) :
    (X.rightCutList i)[j] = X.rightCutFun i j := by
  have := getElem?_rightCutList hj
  rw [List.getElem?_eq_getElem hj] at this
  exact Option.some_injective _ this

private theorem getElem_leftCutList {j : ℕ} (hj : j < (X.leftCutList i).length) :
    (X.leftCutList i)[j] = X.leftCutFun i j := by
  have := getElem?_leftCutList hj
  rw [List.getElem?_eq_getElem hj] at this
  exact Option.some_injective _ this

end ArcFacts

/-! ### The cut lists satisfy the conditions of a cut -/

section ArcCutData

variable {X} {i : Fin b}

private theorem even_mod_iff {N x : ℕ} (hN : Even N) : Even (x % N) ↔ Even x := by
  simpa using even_mod_add_iff (y := 0) hN

private theorem passesThrough_rot_pow_inv_arcDart (hX : X.IsTripleDiagram) {k : ℕ}
    (hk : k + 1 < X.arcLength i) (j : ℕ) :
    X.PassesThrough (X.arc i).toFinset (X.vertexOf ((X.rot ^ j) (X.inv (X.arcDart i k)))) := by
  rw [X.vertexOf_rot_pow_apply]
  refine ⟨X.vertexOf_mem_internalVertices.2 (not_runsToEndpoint_arcDart hX hk), _,
    mem_arc_toFinset.2 ⟨k + 1, hk, rfl⟩, ?_⟩
  rw [arcDart_succ_eq hX hk, X.vertexOf_rot_pow_apply]

/-- A dart of the right cut list lies at an endpoint or at a triple point of the arc. -/
private theorem isBoundaryVertex_or_passesThrough_of_mem_rightCutList (hX : X.IsTripleDiagram)
    {d : H} (hd : d ∈ X.rightCutList i) :
    X.IsBoundaryVertex (X.vertexOf d) ∨ X.PassesThrough (X.arc i).toFinset (X.vertexOf d) := by
  rcases mem_rightCutList.1 hd with ⟨r, -, rfl⟩ | ⟨k, hk, rfl | rfl⟩
  · exact Or.inl (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2
  · right
    have := passesThrough_rot_pow_inv_arcDart hX hk 1
    rwa [pow_one] at this
  · exact Or.inr (passesThrough_rot_pow_inv_arcDart hX hk 2)

/-- A dart of the left cut list lies at an endpoint or at a triple point of the arc. -/
private theorem isBoundaryVertex_or_passesThrough_of_mem_leftCutList (hX : X.IsTripleDiagram)
    {d : H} (hd : d ∈ X.leftCutList i) :
    X.IsBoundaryVertex (X.vertexOf d) ∨ X.PassesThrough (X.arc i).toFinset (X.vertexOf d) := by
  rcases mem_leftCutList.1 hd with ⟨r, -, rfl⟩ | ⟨k, hk, rfl | rfl⟩
  · exact Or.inl (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2
  · exact Or.inr (passesThrough_rot_pow_inv_arcDart hX hk 4)
  · exact Or.inr (passesThrough_rot_pow_inv_arcDart hX hk 5)

/-- The darts `σʲ ē_l` at the triple points of a simple arc determine `l` and `j`. -/
private theorem rot_pow_inv_arcDart_inj (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {k k' a a' : ℕ} (hk : k + 1 < X.arcLength i) (hk' : k' + 1 < X.arcLength i) (ha : a < 6)
    (ha' : a' < 6)
    (h : (X.rot ^ a) (X.inv (X.arcDart i k)) = (X.rot ^ a') (X.inv (X.arcDart i k'))) :
    k = k' ∧ a = a' := by
  have hv := congrArg X.vertexOf h
  rw [X.vertexOf_rot_pow_apply, X.vertexOf_rot_pow_apply] at hv
  obtain rfl := hS k k' hk hk' hv
  exact ⟨rfl, (hX.toIsPreTripleDiagram.rot_pow_six (not_runsToEndpoint_arcDart hX hk)).2 a a'
    ha ha' h⟩

private theorem endDart_finRotate_pow_inj (hX : X.IsTripleDiagram) (q : Fin (2 * b)) {s t : ℕ}
    (hs : s < 2 * b) (ht : t < 2 * b)
    (h : X.endDart ((finRotate (2 * b) ^ s) q) = X.endDart ((finRotate (2 * b) ^ t) q)) :
    s = t := by
  have := hX.endpoint_injective (show X.endpoint ((finRotate (2 * b) ^ s) q) =
    X.endpoint ((finRotate (2 * b) ^ t) q) from congrArg X.vertexOf h)
  exact finRotate_pow_injective q hs ht this

private theorem endDart_ne_rot_pow_inv_arcDart (hX : X.IsTripleDiagram) {k : ℕ}
    (hk : k + 1 < X.arcLength i) (r : Fin (2 * b)) (a : ℕ) :
    X.endDart r ≠ (X.rot ^ a) (X.inv (X.arcDart i k)) := by
  intro h
  have hb : X.IsBoundaryVertex (X.vertexOf (X.endDart r)) :=
    (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2
  rw [h, X.vertexOf_rot_pow_apply] at hb
  exact not_runsToEndpoint_arcDart hX hk hb

private theorem nodup_rightCutList (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) :
    (X.rightCutList i).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨j, hj⟩ ⟨j', hj'⟩ h
  simp only [List.get_eq_getElem, getElem_rightCutList] at h
  have hl := length_rightCutList (X := X) (i := i)
  have hP := rightRunLength_add_leftRunLength (X := X) (i := i)
  have hP0 := leftRunLength_pos (X := X) (i := i)
  apply Fin.ext
  simp only
  unfold rightCutFun at h
  split_ifs at h
  · have := endDart_finRotate_pow_inj hX _ (by omega) (by omega) h
    omega
  · exact absurd h (endDart_ne_rot_pow_inv_arcDart hX (by omega) _ _)
  · exact absurd h.symm (endDart_ne_rot_pow_inv_arcDart hX (by omega) _ _)
  · have := rot_pow_inv_arcDart_inj hX hS (by omega) (by omega) (by omega) (by omega) h
    omega

private theorem nodup_leftCutList (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) :
    (X.leftCutList i).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨j, hj⟩ ⟨j', hj'⟩ h
  simp only [List.get_eq_getElem, getElem_leftCutList] at h
  have hl := length_leftCutList (X := X) (i := i)
  have hP := rightRunLength_add_leftRunLength (X := X) (i := i)
  have hP0 := rightRunLength_pos (X := X) (i := i)
  apply Fin.ext
  simp only
  unfold leftCutFun at h
  split_ifs at h
  · have := endDart_finRotate_pow_inj hX _ (by omega) (by omega) h
    omega
  · exact absurd h (endDart_ne_rot_pow_inv_arcDart hX (by omega) _ _)
  · exact absurd h.symm (endDart_ne_rot_pow_inv_arcDart hX (by omega) _ _)
  · have := rot_pow_inv_arcDart_inj hX hS (by omega) (by omega) (by omega) (by omega) h
    omega

/-- The right cut list satisfies the conditions of a cut. -/
private theorem isCutData_right (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) :
    X.IsCutData (X.rightSide i) (X.rightCutList i) where
  nodup := nodup_rightCutList hX hS
  mem_of_mem_list _ hd := hS.mem_rightSide_of_mem_rightCutList hX hd
  inv_mem _ hd := hS.inv_mem_arcSide hX hd
  notMem_bdry _ hd := (mem_arcSide.1 hd).1
  not_isBoundaryVertex d hd hL :=
    (X.mem_internalVertices.1
      ((hS.mem_rightCutList_or_of_mem_rightSide hX hd).resolve_left hL).1).2
  mem_of_mem_vertexOf d hd hL e he := by
    rcases hS.mem_rightCutList_or_of_mem_rightSide hX hd with h | ⟨hint, hpass⟩
    · exact absurd h hL
    have hv := X.vertexOf_eq_of_mem he
    refine ⟨?_, fun heL => ?_⟩
    · rcases hS.forall_mem_rightSide_or_forall_mem_leftSide hX hint hpass with h | h
      · exact h e he
      · exact absurd (h d (X.self_mem_vertexOf d))
          (disjoint_left.1 disjoint_rightSide_leftSide hd)
    · rcases isBoundaryVertex_or_passesThrough_of_mem_rightCutList hX heL with hb | hp
      · exact (X.mem_internalVertices.1 hint).2 (hv ▸ hb)
      · exact hpass (hv ▸ hp)

/-- The left cut list satisfies the conditions of a cut. -/
private theorem isCutData_left (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) :
    X.IsCutData (X.leftSide i) (X.leftCutList i) where
  nodup := nodup_leftCutList hX hS
  mem_of_mem_list _ hd := hS.mem_leftSide_of_mem_leftCutList hX hd
  inv_mem _ hd := hS.inv_mem_arcSide hX hd
  notMem_bdry _ hd := (mem_arcSide.1 hd).1
  not_isBoundaryVertex d hd hL :=
    (X.mem_internalVertices.1
      ((hS.mem_leftCutList_or_of_mem_leftSide hX hd).resolve_left hL).1).2
  mem_of_mem_vertexOf d hd hL e he := by
    rcases hS.mem_leftCutList_or_of_mem_leftSide hX hd with h | ⟨hint, hpass⟩
    · exact absurd h hL
    have hv := X.vertexOf_eq_of_mem he
    refine ⟨?_, fun heL => ?_⟩
    · rcases hS.forall_mem_rightSide_or_forall_mem_leftSide hX hint hpass with h | h
      · exact absurd (h d (X.self_mem_vertexOf d))
          (disjoint_right.1 disjoint_rightSide_leftSide hd)
      · exact h e he
    · rcases isBoundaryVertex_or_passesThrough_of_mem_leftCutList hX heL with hb | hp
      · exact (X.mem_internalVertices.1 hint).2 (hv ▸ hb)
      · exact hpass (hv ▸ hp)

/-- The cut list on the side `ζ` satisfies the conditions of a cut. -/
theorem IsSimpleArc.isCutData_arcCutList (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) : X.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ) := by
  cases ζ
  · exact isCutData_right hX hS
  · exact isCutData_left hX hS

/-- The orientations along the right cut list: `g_k` is `out` exactly when `k` is even. -/
private theorem isOut_rightCutList (hX : X.IsTripleDiagram) (k : Fin (X.rightCutList i).length) :
    X.isOut (X.rightCutList i)[(k : ℕ)] = decide (Even ((k : ℕ) + 0)) := by
  have hl := length_rightCutList (X := X) (i := i)
  have hk := k.isLt
  obtain ⟨t, ht⟩ := rightRunLength_odd (X := X) (i := i)
  rw [getElem_rightCutList, rightCutFun, add_zero]
  split_ifs with h1
  · rw [isOut_endDart hX]
    congr 1
    apply propext
    rw [val_finRotate_pow, even_mod_iff ⟨b, by ring⟩, arcEndIndex, targetIndex_val,
      Nat.even_iff, Nat.even_iff]
    omega
  · rw [isOut_rot_pow_inv_arcDart hX (by omega)]
    congr 1
    apply propext
    rw [Nat.even_iff, Nat.odd_iff]
    omega

/-- The orientations along the left cut list: `g_k` is `out` exactly when `k` is odd. -/
private theorem isOut_leftCutList (hX : X.IsTripleDiagram) (k : Fin (X.leftCutList i).length) :
    X.isOut (X.leftCutList i)[(k : ℕ)] = decide (Even ((k : ℕ) + 1)) := by
  have hl := length_leftCutList (X := X) (i := i)
  have hk := k.isLt
  obtain ⟨t, ht⟩ := leftRunLength_odd (X := X) (i := i)
  rw [getElem_leftCutList, leftCutFun]
  split_ifs with h1
  · rw [isOut_endDart hX]
    congr 1
    apply propext
    rw [val_finRotate_pow, even_mod_iff ⟨b, by ring⟩, sourceIndex_val, Nat.even_iff,
      Nat.even_iff]
    omega
  · rw [isOut_rot_pow_inv_arcDart hX (by omega)]
    congr 1
    apply propext
    rw [Nat.even_iff, Nat.odd_iff]
    omega

private theorem even_length_rightCutList : Even (X.rightCutList i).length := by
  rw [length_rightCutList]
  obtain ⟨t, ht⟩ := rightRunLength_odd (X := X) (i := i)
  exact ⟨t + (X.arcLength i - 1), by omega⟩

private theorem even_length_leftCutList : Even (X.leftCutList i).length := by
  rw [length_leftCutList]
  obtain ⟨t, ht⟩ := leftRunLength_odd (X := X) (i := i)
  exact ⟨t + (X.arcLength i - 1), by omega⟩

/-- The cut lists have even length. -/
theorem even_length_arcCutList (ζ : StrandSide) : Even (X.arcCutList i ζ).length := by
  cases ζ
  · exact even_length_rightCutList
  · exact even_length_leftCutList

/-- The orientations along a cut list alternate. -/
private theorem isOut_arcCutList (hX : X.IsTripleDiagram) (ζ : StrandSide)
    (k : Fin (X.arcCutList i ζ).length) :
    X.isOut (X.arcCutList i ζ)[(k : ℕ)] = decide (Even ((k : ℕ) + ζ.cutShift)) := by
  cases ζ
  · exact isOut_rightCutList hX k
  · exact isOut_leftCutList hX k

/-- The side `H_ζ(S)` is reached from its cut list without crossing `S`. -/
private theorem forall_mem_of_closed (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) (C : Set H) (h₁ : ∀ d ∈ X.arcCutList i ζ, d ∈ C)
    (h₂ : ∀ d ∈ C, d ∈ X.arcSideDarts i ζ → X.inv d ∈ C)
    (h₃ : ∀ d ∈ C, d ∈ X.arcSideDarts i ζ → d ∉ X.arcCutList i ζ → X.rot d ∈ C) :
    ∀ d ∈ X.arcSideDarts i ζ, d ∈ C := by
  have hc := hS.isCutData_arcCutList hX ζ
  -- the darts of `C ∩ H_ζ(S)` at a triple point avoided by `S`
  have hpow : ∀ d ∈ C, d ∈ X.arcSideDarts i ζ → d ∉ X.arcCutList i ζ → ∀ n,
      (X.rot ^ n) d ∈ C ∧ (X.rot ^ n) d ∈ X.arcSideDarts i ζ ∧
        (X.rot ^ n) d ∉ X.arcCutList i ζ := by
    intro d hdC hdK hdL n
    induction n with
    | zero => exact ⟨hdC, hdK, hdL⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨h₃ _ h1 h2 h3, hc.rot_mem h2 h3, hc.rot_notMem h2 h3⟩
  have hnotL : ∀ d, X.vertexOf d ∈ X.internalVertices →
      ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d) → d ∉ X.arcCutList i ζ := by
    intro d hint hpass hL
    have := (match ζ, hL with
      | .right, hL => isBoundaryVertex_or_passesThrough_of_mem_rightCutList hX hL
      | .left, hL => isBoundaryVertex_or_passesThrough_of_mem_leftCutList hX hL)
    exact this.elim (X.mem_internalVertices.1 hint).2 hpass
  have hmem : (C ∩ (X.arcSideDarts i ζ : Set H)) ∈ {K : Set H | (∀ d ∈ X.arcCutList i ζ, d ∈ K) ∧
      (∀ d ∈ K, X.inv d ∈ K) ∧ ∀ d ∈ K, X.vertexOf d ∈ X.internalVertices →
        ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d) →
          X.rot d ∈ K ∧ X.rot.symm d ∈ K} := by
    refine ⟨fun d hd => ⟨h₁ d hd, hc.mem_of_mem_list d hd⟩,
      fun d ⟨hdC, hdK⟩ => ⟨h₂ d hdC hdK, hc.inv_mem d hdK⟩,
      fun d ⟨hdC, hdK⟩ hint hpass => ?_⟩
    have hdL := hnotL d hint hpass
    obtain ⟨a1, a2, -⟩ := hpow d hdC hdK hdL 1
    obtain ⟨b1, b2, -⟩ := hpow d hdC hdK hdL 5
    rw [pow_one] at a1 a2
    have hsymm : X.rot.symm d = (X.rot ^ 5) d := by
      rw [Equiv.symm_apply_eq, ← Equiv.Perm.mul_apply, ← pow_succ',
        hX.toIsPreTripleDiagram.rot_pow_six_apply (X.mem_internalVertices.1 hint).2]
    rw [hsymm]
    exact ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
  have hle : (X.arcSideDarts i ζ : Set H) ⊆ C ∩ (X.arcSideDarts i ζ : Set H) := by
    cases ζ
    · exact (hS.isLeast_rightSide hX).2 hmem
    · exact (hS.isLeast_leftSide hX).2 hmem
  exact fun d hd => (hle hd).1

end ArcCutData

/-! ### The faces along the cut lists -/

section ArcChains

variable {X} {i : Fin b}

private theorem rightCutFun_leg (j : ℕ) (h : j < X.rightRunLength i - 1) :
    X.rightCutFun i j = X.endDart ((finRotate (2 * b) ^ (j + 1)) (X.arcEndIndex i)) :=
  if_pos h

private theorem rightCutFun_arc (j l a : ℕ) (h : j = X.rightRunLength i - 1 + 2 * l + a)
    (ha : a < 2) : X.rightCutFun i j = (X.rot ^ (a + 1)) (X.inv (X.arcDart i l)) := by
  rw [rightCutFun, if_neg (by omega), show (j - (X.rightRunLength i - 1)) % 2 = a by omega,
    show (j - (X.rightRunLength i - 1)) / 2 = l by omega]

private theorem leftCutFun_leg (j : ℕ) (h : j < X.leftRunLength i - 1) :
    X.leftCutFun i j = X.endDart ((finRotate (2 * b) ^ (j + 1)) (sourceIndex i)) :=
  if_pos h

private theorem leftCutFun_arc (j l a : ℕ) (h : j = X.leftRunLength i - 1 + 2 * l + a)
    (ha : a < 2) :
    X.leftCutFun i j = (X.rot ^ (a + 4)) (X.inv (X.arcDart i (X.arcLength i - 1 - 1 - l))) := by
  rw [leftCutFun, if_neg (by omega), show (j - (X.leftRunLength i - 1)) % 2 = a by omega,
    show (j - (X.leftRunLength i - 1)) / 2 = l by omega]

omit [Fintype H] [DecidableEq H] in
private theorem facePerm_pow_succ_apply (n : ℕ) (x : H) :
    (X.facePerm ^ (n + 1)) x = (X.facePerm ^ n) (X.facePerm x) := by
  rw [pow_succ, Equiv.Perm.mul_apply]

omit [Fintype H] [DecidableEq H] in
private theorem rot_rot_pow (a : ℕ) (x : H) : X.rot ((X.rot ^ a) x) = (X.rot ^ (a + 1)) x := by
  rw [pow_succ', Equiv.Perm.mul_apply]

private theorem val_finRotate_of_lt {N : ℕ} (k : Fin N) (h : (k : ℕ) + 1 < N) :
    ((finRotate N k : Fin N) : ℕ) = (k : ℕ) + 1 := by
  rw [val_finRotate_eq, Nat.mod_eq_of_lt h]

private theorem val_finRotate_of_eq {N : ℕ} (k : Fin N) (h : (k : ℕ) + 1 = N) :
    ((finRotate N k : Fin N) : ℕ) = 0 := by
  rw [val_finRotate_eq, h, Nat.mod_self]

/-- **The faces along the right cut list**: from `σ(g_k)` the orbit of `φ` runs outside
`H_right(S)` to `g_{k+1}`. -/
private theorem chain_rightCutList (hX : X.IsTripleDiagram) (k : Fin (X.rightCutList i).length) :
    ∃ t, (X.facePerm ^ (t + 1)) (X.inv (X.rightCutList i)[(k : ℕ)]) =
      (X.rightCutList i)[((finRotate _ k : Fin (X.rightCutList i).length) : ℕ)] ∧
      ∀ j, 0 < j → j ≤ t → (X.facePerm ^ j) (X.inv (X.rightCutList i)[(k : ℕ)]) ∉
        X.rightSide i := by
  have hinv := hX.inv_involutive
  have hl := length_rightCutList (X := X) (i := i)
  have hk := k.isLt
  have hP0 := rightRunLength_pos (X := X) (i := i)
  have hm := arcLength_pos hX (i := i)
  have hφ : ∀ g, X.facePerm (X.inv g) = X.rot g := fun g => by rw [facePerm_eq, hinv]
  have hB : ∀ r, X.inv (X.exteriorDart r) ∉ X.rightSide i := fun r =>
    notMem_arcSide_of_mem_bdry (inv_exteriorDart_mem_bdry hX r)
  have hA : ∀ t < X.arcLength i, X.arcDart i t ∉ X.rightSide i := fun t ht =>
    notMem_arcSide_of_mem_arcDarts (arcDart_mem_arcDarts ht)
  have hlast := inv_arcDart_last hX (i := i)
  have hfirst : X.endDart ((finRotate (2 * b) ^ X.rightRunLength i) (X.arcEndIndex i)) =
      X.arcDart i 0 := by
    rw [finRotate_pow_rightRunLength, arcDart_zero]
  -- `φ(e_m) = β̄_q` and `φ(β̄_q) = n_{q+1}`
  have hem : X.facePerm (X.arcDart i (X.arcLength i - 1)) =
      X.inv (X.exteriorDart (X.arcEndIndex i)) := by
    rw [facePerm_eq, hlast, rot_endDart hX]
  have hp1 : X.rightRunLength i = 1 →
      X.endDart (finRotate (2 * b) (X.arcEndIndex i)) = X.arcDart i 0 := fun h => by
    rw [← hfirst, h, pow_one]
  have hm1 : X.arcLength i = 1 → X.facePerm (X.arcDart i 0) =
      X.inv (X.exteriorDart (X.arcEndIndex i)) := fun h => by
    rw [← hem, h]
  rw [getElem_rightCutList hk, getElem_rightCutList (finRotate _ k).isLt]
  by_cases h1 : (k : ℕ) + 1 < X.rightRunLength i - 1
  · -- a leg followed by a leg
    rw [val_finRotate_of_lt k (by omega), rightCutFun_leg (k : ℕ) (by omega),
      rightCutFun_leg ((k : ℕ) + 1) h1]
    refine ⟨1, ?_, fun j hj hj1 => ?_⟩
    · rw [facePerm_pow_succ_apply, pow_one, hφ, rot_endDart hX, facePerm_inv_exteriorDart hX,
        ← finRotate_pow_succ]
    · obtain rfl : j = 1 := by omega
      rw [pow_one, hφ, rot_endDart hX]
      exact hB _
  -- the last leg is followed by `n_p = e₁`
  have hlegs : (k : ℕ) + 1 = X.rightRunLength i - 1 → X.facePerm (X.facePerm (X.inv
      (X.endDart ((finRotate (2 * b) ^ ((k : ℕ) + 1)) (X.arcEndIndex i))))) = X.arcDart i 0 :=
    fun h => by
      rw [hφ, rot_endDart hX, facePerm_inv_exteriorDart hX, ← finRotate_pow_succ,
        show (k : ℕ) + 1 + 1 = X.rightRunLength i by omega, hfirst]
  by_cases h2 : (k : ℕ) + 1 = X.rightRunLength i - 1
  · rw [rightCutFun_leg (k : ℕ) (by omega)]
    by_cases hm1' : X.arcLength i = 1
    · -- `m = 1`: followed by the first leg
      rw [val_finRotate_of_eq k (by omega), rightCutFun_leg 0 (by omega)]
      refine ⟨3, ?_, fun j hj hj3 => ?_⟩
      · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, facePerm_pow_succ_apply, pow_one,
          hlegs h2, hm1 hm1', facePerm_inv_exteriorDart hX, zero_add, pow_one]
      · interval_cases j
        · rw [pow_one, hφ, rot_endDart hX]
          exact hB _
        · rw [facePerm_pow_succ_apply, pow_one, hlegs h2]
          exact hA 0 hm
        · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, pow_one, hlegs h2, hm1 hm1']
          exact hB _
    · rw [val_finRotate_of_lt k (by omega), rightCutFun_arc ((k : ℕ) + 1) 0 0 (by omega) (by omega)]
      refine ⟨2, ?_, fun j hj hj2 => ?_⟩
      · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, pow_one, hlegs h2,
          facePerm_eq (X.arcDart i 0), zero_add, pow_one]
      · interval_cases j
        · rw [pow_one, hφ, rot_endDart hX]
          exact hB _
        · rw [facePerm_pow_succ_apply, pow_one, hlegs h2]
          exact hA 0 hm
  -- a dart at a triple point of the arc
  obtain ⟨l, a, hkl, ha⟩ : ∃ l a, (k : ℕ) = X.rightRunLength i - 1 + 2 * l + a ∧ a < 2 :=
    ⟨((k : ℕ) - (X.rightRunLength i - 1)) / 2, ((k : ℕ) - (X.rightRunLength i - 1)) % 2,
      by omega, by omega⟩
  rw [rightCutFun_arc _ l a hkl ha]
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · -- `σ ē_l`, followed by `σ² ē_l`
    rw [val_finRotate_of_lt k (by omega), rightCutFun_arc ((k : ℕ) + 1) l 1 (by omega) (by omega)]
    refine ⟨0, ?_, fun j hj hj0 => by omega⟩
    rw [facePerm_pow_succ_apply, pow_zero, Equiv.Perm.one_apply, hφ, rot_rot_pow]
  · have hsucc : l + 1 < X.arcLength i := by omega
    have he : X.facePerm (X.inv ((X.rot ^ (1 + 1)) (X.inv (X.arcDart i l)))) =
        X.arcDart i (l + 1) := by
      rw [hφ, rot_rot_pow, arcDart_succ_eq hX hsucc]
    by_cases hl1 : l + 2 < X.arcLength i
    · -- `σ² ē_l`, followed by `σ ē_{l+1}`
      rw [val_finRotate_of_lt k (by omega),
        rightCutFun_arc ((k : ℕ) + 1) (l + 1) 0 (by omega) (by omega)]
      refine ⟨1, ?_, fun j hj hj1 => ?_⟩
      · rw [facePerm_pow_succ_apply, pow_one, he, facePerm_eq, zero_add, pow_one]
      · obtain rfl : j = 1 := by omega
        rw [pow_one, he]
        exact hA _ hsucc
    · -- `σ² ē_{m-1}`, the last dart of the list
      have hlm : l + 1 = X.arcLength i - 1 := by omega
      rw [hlm] at he
      rw [val_finRotate_of_eq k (by omega)]
      by_cases hP1 : X.rightRunLength i = 1
      · rw [rightCutFun_arc 0 0 0 (by omega) (by omega)]
        refine ⟨3, ?_, fun j hj hj3 => ?_⟩
        · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, facePerm_pow_succ_apply,
            pow_one, he, hem, facePerm_inv_exteriorDart hX, hp1 hP1, facePerm_eq, zero_add,
            pow_one]
        · interval_cases j
          · rw [pow_one, he]
            exact hA _ (by omega)
          · rw [facePerm_pow_succ_apply, pow_one, he, hem]
            exact hB _
          · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, pow_one, he, hem,
              facePerm_inv_exteriorDart hX, hp1 hP1]
            exact hA 0 hm
      · rw [rightCutFun_leg 0 (by omega)]
        refine ⟨2, ?_, fun j hj hj2 => ?_⟩
        · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, pow_one, he, hem,
            facePerm_inv_exteriorDart hX, zero_add, pow_one]
        · interval_cases j
          · rw [pow_one, he]
            exact hA _ (by omega)
          · rw [facePerm_pow_succ_apply, pow_one, he, hem]
            exact hB _

/-- **The faces along the left cut list**: from `σ(g_k)` the orbit of `φ` runs outside
`H_left(S)` to `g_{k+1}`. -/
private theorem chain_leftCutList (hX : X.IsTripleDiagram) (k : Fin (X.leftCutList i).length) :
    ∃ t, (X.facePerm ^ (t + 1)) (X.inv (X.leftCutList i)[(k : ℕ)]) =
      (X.leftCutList i)[((finRotate _ k : Fin (X.leftCutList i).length) : ℕ)] ∧
      ∀ j, 0 < j → j ≤ t → (X.facePerm ^ j) (X.inv (X.leftCutList i)[(k : ℕ)]) ∉
        X.leftSide i := by
  have hinv := hX.inv_involutive
  have hl := length_leftCutList (X := X) (i := i)
  have hk := k.isLt
  have hQ0 := leftRunLength_pos (X := X) (i := i)
  have hm := arcLength_pos hX (i := i)
  have hφ : ∀ g, X.facePerm (X.inv g) = X.rot g := fun g => by rw [facePerm_eq, hinv]
  have hB : ∀ r, X.inv (X.exteriorDart r) ∉ X.leftSide i := fun r =>
    notMem_arcSide_of_mem_bdry (inv_exteriorDart_mem_bdry hX r)
  have hA : ∀ t < X.arcLength i, X.inv (X.arcDart i t) ∉ X.leftSide i := fun t ht =>
    notMem_arcSide_of_mem_arcDarts (inv_arcDart_mem_arcDarts ht)
  have hlast := inv_arcDart_last hX (i := i)
  have hq : X.endDart ((finRotate (2 * b) ^ X.leftRunLength i) (sourceIndex i)) =
      X.inv (X.arcDart i (X.arcLength i - 1)) := by
    rw [finRotate_pow_leftRunLength, hlast]
  -- `φ(ē₁) = β̄_p`
  have hp : X.facePerm (X.inv (X.arcDart i 0)) = X.inv (X.exteriorDart (sourceIndex i)) := by
    rw [hφ, arcDart_zero, rot_endDart hX]
  have hq1 : X.leftRunLength i = 1 →
      X.endDart (finRotate (2 * b) (sourceIndex i)) = X.inv (X.arcDart i (X.arcLength i - 1)) :=
    fun h => by rw [← hq, h, pow_one]
  -- `φ(ē_m) = σ⁴ ē_{m-1}` when `m ≥ 2`, and `φ(ē_m) = β̄_p` when `m = 1`
  have hem : 2 ≤ X.arcLength i → X.facePerm (X.inv (X.arcDart i (X.arcLength i - 1))) =
      (X.rot ^ (0 + 4)) (X.inv (X.arcDart i (X.arcLength i - 1 - 1 - 0))) := fun h2 => by
    have h3 := arcDart_succ_eq hX (i := i) (k := X.arcLength i - 1 - 1) (by omega)
    rw [show X.arcLength i - 1 - 1 + 1 = X.arcLength i - 1 by omega] at h3
    rw [hφ, h3, rot_rot_pow, Nat.sub_zero]
  have hm1 : X.arcLength i = 1 → X.facePerm (X.inv (X.arcDart i (X.arcLength i - 1))) =
      X.inv (X.exteriorDart (sourceIndex i)) := fun h => by
    rw [← hp, h]
  rw [getElem_leftCutList hk, getElem_leftCutList (finRotate _ k).isLt]
  by_cases h1 : (k : ℕ) + 1 < X.leftRunLength i - 1
  · rw [val_finRotate_of_lt k (by omega), leftCutFun_leg (k : ℕ) (by omega),
      leftCutFun_leg ((k : ℕ) + 1) h1]
    refine ⟨1, ?_, fun j hj hj1 => ?_⟩
    · rw [facePerm_pow_succ_apply, pow_one, hφ, rot_endDart hX, facePerm_inv_exteriorDart hX,
        ← finRotate_pow_succ]
    · obtain rfl : j = 1 := by omega
      rw [pow_one, hφ, rot_endDart hX]
      exact hB _
  have hlegs : (k : ℕ) + 1 = X.leftRunLength i - 1 → X.facePerm (X.facePerm (X.inv
      (X.endDart ((finRotate (2 * b) ^ ((k : ℕ) + 1)) (sourceIndex i))))) =
      X.inv (X.arcDart i (X.arcLength i - 1)) :=
    fun h => by
      rw [hφ, rot_endDart hX, facePerm_inv_exteriorDart hX, ← finRotate_pow_succ,
        show (k : ℕ) + 1 + 1 = X.leftRunLength i by omega, hq]
  by_cases h2 : (k : ℕ) + 1 = X.leftRunLength i - 1
  · rw [leftCutFun_leg (k : ℕ) (by omega)]
    by_cases hm1' : X.arcLength i = 1
    · rw [val_finRotate_of_eq k (by omega), leftCutFun_leg 0 (by omega)]
      refine ⟨3, ?_, fun j hj hj3 => ?_⟩
      · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, facePerm_pow_succ_apply, pow_one,
          hlegs h2, hm1 hm1', facePerm_inv_exteriorDart hX, zero_add, pow_one]
      · interval_cases j
        · rw [pow_one, hφ, rot_endDart hX]
          exact hB _
        · rw [facePerm_pow_succ_apply, pow_one, hlegs h2]
          exact hA _ (by omega)
        · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, pow_one, hlegs h2, hm1 hm1']
          exact hB _
    · rw [val_finRotate_of_lt k (by omega), leftCutFun_arc ((k : ℕ) + 1) 0 0 (by omega) (by omega)]
      refine ⟨2, ?_, fun j hj hj2 => ?_⟩
      · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, pow_one, hlegs h2, hem (by omega)]
      · interval_cases j
        · rw [pow_one, hφ, rot_endDart hX]
          exact hB _
        · rw [facePerm_pow_succ_apply, pow_one, hlegs h2]
          exact hA _ (by omega)
  obtain ⟨l, a, hkl, ha⟩ : ∃ l a, (k : ℕ) = X.leftRunLength i - 1 + 2 * l + a ∧ a < 2 :=
    ⟨((k : ℕ) - (X.leftRunLength i - 1)) / 2, ((k : ℕ) - (X.leftRunLength i - 1)) % 2,
      by omega, by omega⟩
  rw [leftCutFun_arc _ l a hkl ha]
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · rw [val_finRotate_of_lt k (by omega), leftCutFun_arc ((k : ℕ) + 1) l 1 (by omega) (by omega)]
    refine ⟨0, ?_, fun j hj hj0 => by omega⟩
    rw [facePerm_pow_succ_apply, pow_zero, Equiv.Perm.one_apply, hφ, rot_rot_pow]
  · -- `σ⁵ ē_j` with `j = m - 1 - l`: `φ` sends `(σ⁵ ē_j)̄` to `σ⁶ ē_j = ē_j`
    have hsix : X.facePerm (X.inv ((X.rot ^ (1 + 4))
        (X.inv (X.arcDart i (X.arcLength i - 1 - 1 - l))))) =
        X.inv (X.arcDart i (X.arcLength i - 1 - 1 - l)) := by
      rw [hφ, rot_rot_pow]
      exact hX.toIsPreTripleDiagram.rot_pow_six_apply (not_runsToEndpoint_arcDart hX (by omega))
    by_cases hl1 : l + 2 < X.arcLength i
    · rw [val_finRotate_of_lt k (by omega),
        leftCutFun_arc ((k : ℕ) + 1) (l + 1) 0 (by omega) (by omega)]
      have hj : X.facePerm (X.inv (X.arcDart i (X.arcLength i - 1 - 1 - l))) =
          (X.rot ^ (0 + 4)) (X.inv (X.arcDart i (X.arcLength i - 1 - 1 - (l + 1)))) := by
        rw [hφ, show X.arcLength i - 1 - 1 - l = X.arcLength i - 1 - 1 - (l + 1) + 1 by omega,
          arcDart_succ_eq hX (k := X.arcLength i - 1 - 1 - (l + 1)) (by omega), rot_rot_pow]
      refine ⟨1, ?_, fun j hj' hj1 => ?_⟩
      · rw [facePerm_pow_succ_apply, pow_one, hsix, hj]
      · obtain rfl : j = 1 := by omega
        rw [pow_one, hsix]
        exact hA _ (by omega)
    · have hl0 : X.arcLength i - 1 - 1 - l = 0 := by omega
      rw [hl0] at hsix
      rw [hl0, val_finRotate_of_eq k (by omega)]
      by_cases hQ1 : X.leftRunLength i = 1
      · rw [leftCutFun_arc 0 0 0 (by omega) (by omega)]
        refine ⟨3, ?_, fun j hj hj3 => ?_⟩
        · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, facePerm_pow_succ_apply,
            pow_one, hsix, hp, facePerm_inv_exteriorDart hX, hq1 hQ1, hem (by omega)]
        · interval_cases j
          · rw [pow_one, hsix]
            exact hA 0 hm
          · rw [facePerm_pow_succ_apply, pow_one, hsix, hp]
            exact hB _
          · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, pow_one, hsix, hp,
              facePerm_inv_exteriorDart hX, hq1 hQ1]
            exact hA _ (by omega)
      · rw [leftCutFun_leg 0 (by omega)]
        refine ⟨2, ?_, fun j hj hj2 => ?_⟩
        · rw [facePerm_pow_succ_apply, facePerm_pow_succ_apply, pow_one, hsix, hp,
            facePerm_inv_exteriorDart hX, zero_add, pow_one]
        · interval_cases j
          · rw [pow_one, hsix]
            exact hA 0 hm
          · rw [facePerm_pow_succ_apply, pow_one, hsix, hp]
            exact hB _

/-- From `σ(g_k)` the orbit of `φ` runs outside `H_ζ(S)` to `g_{k+1}`. -/
private theorem chain_arcCutList (hX : X.IsTripleDiagram) (ζ : StrandSide)
    (k : Fin (X.arcCutList i ζ).length) :
    ∃ t, (X.facePerm ^ (t + 1)) (X.inv (X.arcCutList i ζ)[(k : ℕ)]) =
      (X.arcCutList i ζ)[((finRotate _ k : Fin (X.arcCutList i ζ).length) : ℕ)] ∧
      ∀ j, 0 < j → j ≤ t → (X.facePerm ^ j) (X.inv (X.arcCutList i ζ)[(k : ℕ)]) ∉
        X.arcSideDarts i ζ := by
  cases ζ
  · exact chain_rightCutList hX k
  · exact chain_leftCutList hX k

end ArcChains

/-! ### The cut is a triple diagram -/

section ArcCutTriple

variable {X} {i : Fin b}

/-- The darts at the endpoints of a pre-triple diagram with `b` arcs: `6b` of them. -/
private theorem card_boundaryDarts (hX : X.IsPreTripleDiagram) :
    (univ.filter fun d => X.IsBoundaryVertex (X.vertexOf d)).card = 6 * b := by
  have hVb : (univ.filter fun d => X.IsBoundaryVertex (X.vertexOf d)).image X.vertexOf =
      X.boundaryVertices := by
    ext v
    simp only [mem_image, mem_filter, mem_univ, true_and, DiskMap.mem_boundaryVertices,
      RotationSystem.mem_vertices]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, rfl⟩, hd⟩
    · rintro ⟨⟨d, rfl⟩, hd⟩
      exact ⟨d, hd, rfl⟩
  have h3 := mul_card_image_vertexOf X.toRotationSystem
    (D := univ.filter fun d => X.IsBoundaryVertex (X.vertexOf d)) (c := 3)
    (fun d hd e he => by
      simp only [mem_filter, mem_univ, true_and] at hd ⊢
      rwa [X.vertexOf_eq_of_mem he])
    (fun d hd => (hX.boundaryVertex_card _ (X.vertexOf_mem_boundaryVertices.2
      (mem_filter.1 hd).2)).1)
  have hb : X.boundaryVertices.card = 2 * b := by
    have : X.boundaryVertices = univ.image X.endpoint := by
      ext v
      simp only [mem_image, mem_univ, true_and]
      exact ⟨fun hv => hX.exists_endpoint_eq v hv, fun ⟨r, hr⟩ => hr ▸ hX.endpoint_mem r⟩
    rw [this, card_image_of_injective _ hX.endpoint_injective, card_univ, Fintype.card_fin]
  rw [hVb, hb] at h3
  omega

/-- A triple diagram with `b` arcs has `4b` darts in `B`. -/
private theorem card_bdry (hX : X.IsTripleDiagram) : X.bdry.card = 4 * b := by
  have hDb := card_boundaryDarts hX.toIsPreTripleDiagram
  have hsplit : (univ.filter fun d => X.IsBoundaryVertex (X.vertexOf d)) =
      X.bdry ∪ univ.image X.endDart := by
    ext d
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image]
    constructor
    · intro hd
      by_cases hB : d ∈ X.bdry
      · exact Or.inl hB
      · right
        obtain ⟨r, hr⟩ := hX.exists_endpoint_eq _ (X.vertexOf_mem_boundaryVertices.2 hd)
        refine ⟨r, (DiskMap.eq_of_notMem_bdry hX.boundaryVertex_card hd
          (show d ∈ X.vertexOf d from X.self_mem_vertexOf d) ?_ hB
          (hX.endDart_notMem_bdry r)).symm⟩
        rw [← hr]
        exact X.self_mem_vertexOf _
    · rintro (h | ⟨r, -, rfl⟩)
      · exact X.isBoundaryVertex_vertexOf_of_mem h
      · exact (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2
  have hdisj : Disjoint X.bdry (univ.image X.endDart) := by
    rw [disjoint_left]
    rintro d hd hd'
    obtain ⟨r, -, rfl⟩ := mem_image.1 hd'
    exact hX.endDart_notMem_bdry r hd
  have himg : (univ.image X.endDart).card = 2 * b := by
    rw [card_image_of_injective _ (fun r s h => hX.endpoint_injective
      (show X.endpoint r = X.endpoint s from congrArg X.vertexOf h)), card_univ,
      Fintype.card_fin]
  rw [hsplit, card_union_of_disjoint hdisj, himg] at hDb
  omega

/-- The arc from `s_i` has `2m` darts `e_l, ē_l`. -/
private theorem card_arcDarts (hX : X.IsTripleDiagram) :
    (X.arcDarts i).card = 2 * X.arcLength i := by
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero (hX.toIsPreTripleDiagram.arcLength_ne_zero i)
  have hnd : (X.arc i).Nodup := by
    rw [arc_eq_map_range']
    refine List.Nodup.map_on (fun a ha c hc hac => ?_) List.nodup_range'
    simp only [List.mem_range'_1, hM] at ha hc
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact X.arcDart_ne_of_lt hM h (by omega) hac
    · exact X.arcDart_ne_of_lt hM h (by omega) hac.symm
  have h1 : (X.arc i).toFinset.card = X.arcLength i := by
    rw [List.toFinset_card_of_nodup hnd, length_arc]
  have h2 : ((X.arc i).toFinset.image X.inv).card = X.arcLength i := by
    rw [card_image_of_injective _ X.inv.injective, h1]
  have hdisj : Disjoint (X.arc i).toFinset ((X.arc i).toFinset.image X.inv) := by
    rw [disjoint_left]
    intro d hd hd'
    obtain ⟨t, ht, rfl⟩ := mem_arc_toFinset.1 hd
    obtain ⟨e, he, heq⟩ := mem_image.1 hd'
    obtain ⟨t', ht', rfl⟩ := mem_arc_toFinset.1 he
    have o1 := (X.arcDart_notMem_bdry_isOut hX.toIsPreTripleDiagram hM (k := t) (by omega)).2
    have o2 := X.arcDart_notMem_bdry_isOut hX.toIsPreTripleDiagram hM (k := t') (by omega)
    have o3 := hX.toIsPreTripleDiagram.isOut_inv_apply o2.1
    rw [← heq, o3, o2.2] at o1
    simp at o1
  rw [arcDarts, card_union_of_disjoint hdisj, h1, h2]
  ring

/-- The darts of `X`: `B`, the darts of the arc and the two sides. -/
private theorem card_sides (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) :
    (X.rightSide i).card + (X.leftSide i).card + 2 * X.arcLength i + 4 * b =
      Fintype.card H := by
  have hu := hS.arcDarts_union_rightSide_union_leftSide hX
  have hd1 : Disjoint (X.arcDarts i) (X.rightSide i) := disjoint_arcDarts_arcSide _
  have hd2 : Disjoint (X.arcDarts i ∪ X.rightSide i) (X.leftSide i) :=
    disjoint_union_left.2 ⟨disjoint_arcDarts_arcSide _, disjoint_rightSide_leftSide⟩
  have hc := congrArg Finset.card hu
  rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1, card_arcDarts hX, card_compl,
    card_bdry hX] at hc
  have := X.bdry.card_le_univ
  rw [card_bdry hX] at this
  omega

/-- A side whose cut list is empty has no darts. -/
private theorem arcSideDarts_eq_empty (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) (h : X.arcCutList i ζ = []) : X.arcSideDarts i ζ = ∅ :=
  eq_empty_of_forall_notMem (forall_mem_of_closed hX hS ζ ∅ (by simp [h])
    (fun d hd => absurd hd id) (fun d hd => absurd hd id))

private theorem length_arcCutList_right :
    (X.arcCutList i .right).length = X.rightRunLength i - 1 + 2 * (X.arcLength i - 1) :=
  length_rightCutList

private theorem length_arcCutList_left :
    (X.arcCutList i .left).length = X.leftRunLength i - 1 + 2 * (X.arcLength i - 1) :=
  length_leftCutList

private theorem finRotate_ne_self (h2b : 2 ≤ 2 * b) (r : Fin (2 * b)) : finRotate _ r ≠ r :=
  fun h => by
    have := finRotate_pow_injective r (s := 1) (t := 0) (by omega) (by omega)
      (by rw [pow_one, pow_zero, Equiv.Perm.one_apply, h])
    omega

private theorem finRotate_arcEndIndex_eq_sourceIndex_iff :
    finRotate _ (X.arcEndIndex i) = sourceIndex i ↔ X.rightRunLength i = 1 := by
  have h2b := two_le_two_mul_b i
  constructor
  · intro h
    have := val_finRotate_pow_sub (X.arcEndIndex i) (s := 1) (by omega)
    rwa [pow_one, h] at this
  · intro h
    rw [← pow_one (finRotate (2 * b)), ← h, finRotate_pow_rightRunLength]

private theorem finRotate_sourceIndex_eq_arcEndIndex_iff :
    finRotate _ (sourceIndex i) = X.arcEndIndex i ↔ X.leftRunLength i = 1 := by
  have h2b := two_le_two_mul_b i
  constructor
  · intro h
    have := val_finRotate_pow_sub (sourceIndex i) (s := 1) (by omega)
    rwa [pow_one, h] at this
  · intro h
    rw [← pow_one (finRotate (2 * b)), ← h, finRotate_pow_leftRunLength]

/-- The orbit of `φ` through a leg at a position other than `p` and `q` meets one of the sides. -/
private theorem exists_side_faceOf_endDart (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {r : Fin (2 * b)} (hp : r ≠ sourceIndex i) (hq : r ≠ X.arcEndIndex i) :
    ∃ e ∈ X.rightSide i ∪ X.leftSide i, X.faceOf e = X.faceOf (X.endDart r) := by
  rcases isRightPosition_or_isLeftPosition hp hq with h | h
  · exact ⟨_, mem_union_left _ (hS.endDart_mem_rightSide hX h), rfl⟩
  · exact ⟨_, mem_union_right _ (hS.endDart_mem_leftSide hX h), rfl⟩

/-- The orbit of `φ` through a dart `e_t` with `t + 1 < m` meets one of the sides. -/
private theorem exists_side_faceOf_arcDart (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {t : ℕ} (ht : t + 1 < X.arcLength i) :
    ∃ e ∈ X.rightSide i ∪ X.leftSide i, X.faceOf e = X.faceOf (X.arcDart i t) :=
  ⟨X.facePerm (X.arcDart i t), mem_union_left _ (by
    rw [facePerm_eq]
    exact (hS.rot_pow_inv_arcDart_mem_rightSide hX ht).1), X.faceOf_facePerm _⟩

/-- The orbit of `φ` through a dart `ē_t` with `t ≥ 1` meets one of the sides. -/
private theorem exists_side_faceOf_inv_arcDart (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {t : ℕ} (h1 : 1 ≤ t) (ht : t < X.arcLength i) :
    ∃ e ∈ X.rightSide i ∪ X.leftSide i, X.faceOf e = X.faceOf (X.inv (X.arcDart i t)) :=
  ⟨X.facePerm (X.inv (X.arcDart i t)), mem_union_right _ (by
    rw [facePerm_eq, hX.inv_involutive, show t = t - 1 + 1 by omega,
      arcDart_succ_eq hX (by omega), rot_rot_pow]
    exact (hS.rot_pow_inv_arcDart_mem_leftSide hX (by omega)).1), X.faceOf_facePerm _⟩

/-- The orbit of `φ` through the last dart `e_m` meets one of the sides, unless `N_R = m = 1`. -/
private theorem exists_side_faceOf_arcDart_last (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) :
    (∃ e ∈ X.rightSide i ∪ X.leftSide i,
        X.faceOf e = X.faceOf (X.arcDart i (X.arcLength i - 1))) ∨
      (X.rightRunLength i = 1 ∧ X.arcLength i = 1) := by
  have hm := arcLength_pos hX (i := i)
  set G : H → Prop := fun x => ∃ e ∈ X.rightSide i ∪ X.leftSide i, X.faceOf e = X.faceOf x
  have hGφ : ∀ x, G (X.facePerm x) → G x := fun x ⟨e, he, hex⟩ =>
    ⟨e, he, hex.trans (X.faceOf_facePerm x)⟩
  change G _ ∨ _
  have h1 : X.facePerm (X.facePerm (X.arcDart i (X.arcLength i - 1))) =
      X.endDart (finRotate _ (X.arcEndIndex i)) := by
    rw [facePerm_eq (X.arcDart i _), inv_arcDart_last hX, rot_endDart hX,
      facePerm_inv_exteriorDart hX]
  by_cases hP : X.rightRunLength i = 1
  · rw [finRotate_arcEndIndex_eq_sourceIndex_iff.2 hP] at h1
    by_cases hm1 : X.arcLength i = 1
    · exact Or.inr ⟨hP, hm1⟩
    · left
      refine hGφ _ (hGφ _ ?_)
      rw [h1, ← arcDart_zero]
      exact exists_side_faceOf_arcDart hX hS (t := 0) (by omega)
  · left
    refine hGφ _ (hGφ _ ?_)
    rw [h1]
    exact exists_side_faceOf_endDart hX hS
      (fun h => hP (finRotate_arcEndIndex_eq_sourceIndex_iff.1 h))
      (finRotate_ne_self (two_le_two_mul_b i) _)

/-- The orbit of `φ` through the reverse `ē₁` of the first dart meets one of the sides, unless
`N_L = m = 1`. -/
private theorem exists_side_faceOf_inv_arcDart_zero (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) :
    (∃ e ∈ X.rightSide i ∪ X.leftSide i, X.faceOf e = X.faceOf (X.inv (X.arcDart i 0))) ∨
      (X.leftRunLength i = 1 ∧ X.arcLength i = 1) := by
  have hm := arcLength_pos hX (i := i)
  set G : H → Prop := fun x => ∃ e ∈ X.rightSide i ∪ X.leftSide i, X.faceOf e = X.faceOf x
  have hGφ : ∀ x, G (X.facePerm x) → G x := fun x ⟨e, he, hex⟩ =>
    ⟨e, he, hex.trans (X.faceOf_facePerm x)⟩
  change G _ ∨ _
  have h1 : X.facePerm (X.facePerm (X.inv (X.arcDart i 0))) =
      X.endDart (finRotate _ (sourceIndex i)) := by
    rw [facePerm_eq (X.inv _), hX.inv_involutive, arcDart_zero, rot_endDart hX,
      facePerm_inv_exteriorDart hX]
  by_cases hQ : X.leftRunLength i = 1
  · rw [finRotate_sourceIndex_eq_arcEndIndex_iff.2 hQ, endDart_arcEndIndex hX] at h1
    by_cases hm1 : X.arcLength i = 1
    · exact Or.inr ⟨hQ, hm1⟩
    · left
      refine hGφ _ (hGφ _ ?_)
      rw [h1]
      exact exists_side_faceOf_inv_arcDart hX hS (by omega) (by omega)
  · left
    refine hGφ _ (hGφ _ ?_)
    rw [h1]
    exact exists_side_faceOf_endDart hX hS (finRotate_ne_self (two_le_two_mul_b i) _)
      (fun h => hQ (finRotate_sourceIndex_eq_arcEndIndex_iff.1 h))

/-- The orbit of `φ` through a dart of the arc meets one of the sides, unless it is the orbit of
`e₁` (when `N_R = m = 1`) or of `ē₁` (when `N_L = m = 1`). -/
private theorem faceOf_cases_of_mem_arcDarts (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {x : H} (hx : x ∈ X.arcDarts i) :
    (∃ e ∈ X.rightSide i ∪ X.leftSide i, X.faceOf e = X.faceOf x) ∨
      (X.rightRunLength i = 1 ∧ X.arcLength i = 1 ∧ X.faceOf x = X.faceOf (X.arcDart i 0)) ∨
      (X.leftRunLength i = 1 ∧ X.arcLength i = 1 ∧
        X.faceOf x = X.faceOf (X.inv (X.arcDart i 0))) := by
  obtain ⟨t, ht, rfl | rfl⟩ := mem_arcDarts.1 hx
  · by_cases ht' : t + 1 < X.arcLength i
    · exact Or.inl (exists_side_faceOf_arcDart hX hS ht')
    · obtain rfl : t = X.arcLength i - 1 := by omega
      rcases exists_side_faceOf_arcDart_last hX hS with h | ⟨hP, hm1⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨hP, hm1, by rw [hm1]⟩)
  · by_cases ht' : 1 ≤ t
    · exact Or.inl (exists_side_faceOf_inv_arcDart hX hS ht' ht)
    · obtain rfl : t = 0 := by omega
      rcases exists_side_faceOf_inv_arcDart_zero hX hS with h | ⟨hQ, hm1⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨hQ, hm1, rfl⟩)

/-- The orbit of `φ` through a dart meets one of the sides, unless it is the exterior or, when one
of the cut lists is empty, the orbit of `e₁` or of `ē₁`. -/
private theorem faceOf_cases (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) (d : H) :
    X.faceOf d = X.exterior ∨
      (∃ e ∈ X.rightSide i ∪ X.leftSide i, X.faceOf e = X.faceOf d) ∨
      (X.rightRunLength i = 1 ∧ X.arcLength i = 1 ∧ X.faceOf d = X.faceOf (X.arcDart i 0)) ∨
      (X.leftRunLength i = 1 ∧ X.arcLength i = 1 ∧
        X.faceOf d = X.faceOf (X.inv (X.arcDart i 0))) := by
  have hinv := hX.inv_involutive
  set G : H → Prop := fun x => ∃ e ∈ X.rightSide i ∪ X.leftSide i, X.faceOf e = X.faceOf x
  have hGφ : ∀ x, G (X.facePerm x) → G x := fun x ⟨e, he, hex⟩ =>
    ⟨e, he, hex.trans (X.faceOf_facePerm x)⟩
  have hGmem : ∀ x, x ∈ X.rightSide i ∪ X.leftSide i → G x := fun x hx => ⟨x, hx, rfl⟩
  by_cases hB : d ∈ X.bdry
  · by_cases hext : d ∈ X.exterior
    · left
      obtain ⟨f, hf⟩ := X.mem_faceOrbits.1 hX.toIsDiskMap.exterior_mem_faceOrbits
      rw [← hf, X.faceOf_eq_of_mem (hf ▸ hext)]
    · have hdi : X.inv d ∈ X.exterior := by
        have hu := hX.toIsDiskMap.exterior_union_map_inv
        rw [← hu, mem_union, mem_map_equiv] at hB
        rcases hB with h | h
        · exact absurd h hext
        · have : X.inv.symm d = X.inv d := by
            rw [Equiv.symm_apply_eq, hinv]
          rwa [this] at h
      have hφB : X.facePerm d ∉ X.bdry := (X.mem_exterior.1 hdi).2
      have hφf : X.faceOf (X.facePerm d) = X.faceOf d := X.faceOf_facePerm d
      by_cases hA : X.facePerm d ∈ X.arcDarts i
      · rcases faceOf_cases_of_mem_arcDarts hX hS hA with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact Or.inr (Or.inl (hGφ _ h))
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, hφf ▸ h3⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, hφf ▸ h3⟩))
      · have hu := hS.arcDarts_union_rightSide_union_leftSide hX
        have : X.facePerm d ∈ X.bdryᶜ := mem_compl.2 hφB
        rw [← hu, mem_union, mem_union] at this
        rcases this with (h | h) | h
        · exact absurd h hA
        · exact Or.inr (Or.inl (hGφ _ (hGmem _ (mem_union_left _ h))))
        · exact Or.inr (Or.inl (hGφ _ (hGmem _ (mem_union_right _ h))))
  · by_cases hA : d ∈ X.arcDarts i
    · rcases faceOf_cases_of_mem_arcDarts hX hS hA with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · have hu := hS.arcDarts_union_rightSide_union_leftSide hX
      have : d ∈ X.bdryᶜ := mem_compl.2 hB
      rw [← hu, mem_union, mem_union] at this
      rcases this with (h | h) | h
      · exact absurd h hA
      · exact Or.inr (Or.inl (hGmem _ (mem_union_left _ h)))
      · exact Or.inr (Or.inl (hGmem _ (mem_union_right _ h)))

omit [Fintype H] in
/-- The Euler characteristic of a cut, times `6`, in terms of its darts and faces. -/
private theorem six_mul_euler_cut {K : Finset H} {L : List H} {s : ℕ}
    (hpre : (X.cut K L s).IsPreTripleDiagram)
    (hev : Even L.length) :
    6 * ((X.cut K L s).vertices.card - (X.cut K L s).edges.card +
      (X.cut K L s).faceOrbits.card : ℤ) =
      6 * (X.cut K L s).faceOrbits.card - 2 * K.card - L.length := by
  have hV := IsPreTripleDiagram.six_mul_card_vertices hpre
  have hE := two_mul_card_edges' (X.cut K L s).toRotationSystem hpre.inv_involutive hpre.inv_ne
  rw [IsCutData.card_cutDart] at hV hE
  obtain ⟨t, ht⟩ := hev
  omega

/-- The Euler characteristic of `X`, times `6`, in terms of its darts and faces. -/
private theorem six_mul_euler (hX : X.IsTripleDiagram) :
    6 * b - 2 * (Fintype.card H : ℤ) + 6 * X.faceOrbits.card = 12 := by
  have hV := IsPreTripleDiagram.six_mul_card_vertices hX.toIsPreTripleDiagram
  have hE := two_mul_card_edges' X.toRotationSystem hX.inv_involutive hX.inv_ne
  have he := hX.euler
  omega

/-- The cut of a triple diagram along a simple arc on a side `ζ` with `N_ζ ≥ 2` is a pre-triple
diagram. -/
private theorem isPreTripleDiagram_arcCut (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) (hN : 2 ≤ (X.arcCutList i ζ).length) :
    (X.arcCut i ζ).IsPreTripleDiagram :=
  (hS.isCutData_arcCutList hX ζ).isPreTripleDiagram_cut hX.toIsPreTripleDiagram hN
    (even_length_arcCutList ζ) (isOut_arcCutList hX ζ)

/-- The cut of a triple diagram along a simple arc on a side `ζ` with `N_ζ ≥ 1` is connected. -/
private theorem isConnected_arcCut (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) (hN : 0 < (X.arcCutList i ζ).length) :
    (X.arcCut i ζ).IsConnected :=
  (hS.isCutData_arcCutList hX ζ).isConnected_cut hX.toIsPreTripleDiagram hN
    (forall_mem_of_closed hX hS ζ)

/-- The faces of the cut of a triple diagram along a simple arc. -/
private theorem card_faceOrbits_arcCut (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) (hN : 0 < (X.arcCutList i ζ).length) :
    (X.arcCut i ζ).faceOrbits.card = ((X.arcSideDarts i ζ).image X.faceOf).card + 1 :=
  (hS.isCutData_arcCutList hX ζ).card_faceOrbits_cut hX.inv_involutive hN
    (chain_arcCutList hX ζ)

/-- Euler's relation for the cut of a triple diagram along a simple arc. -/
private theorem euler_arcCut (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) (ζ : StrandSide)
    (hN : 2 ≤ (X.arcCutList i ζ).length) :
    ((X.arcCut i ζ).vertices.card : ℤ) - (X.arcCut i ζ).edges.card +
      (X.arcCut i ζ).faceOrbits.card = 2 := by
  have hχ := fun ζ' (hN' : 2 ≤ (X.arcCutList i ζ').length) =>
    six_mul_euler_cut (s := ζ'.cutShift)
      (isPreTripleDiagram_arcCut hX hS ζ' hN') (even_length_arcCutList ζ')
  have hle := fun ζ' (hN' : 2 ≤ (X.arcCutList i ζ').length) =>
    (isConnected_arcCut hX hS ζ' (by omega)).euler_le
  have hF := fun ζ' (hN' : 2 ≤ (X.arcCutList i ζ').length) =>
    card_faceOrbits_arcCut hX hS ζ' (by omega)
  have h6 := six_mul_euler hX
  have hsides := card_sides hX hS
  have hlr := rightRunLength_add_leftRunLength (X := X) (i := i)
  have hm := arcLength_pos hX (i := i)
  have hNr := length_arcCutList_right (X := X) (i := i)
  have hNl := length_arcCutList_left (X := X) (i := i)
  have hP0 := rightRunLength_pos (X := X) (i := i)
  have hQ0 := leftRunLength_pos (X := X) (i := i)
  -- the faces of `X` are the exterior, the orbits meeting the two sides, and the exceptions
  have hfacesE : ∀ E : Finset (Finset H),
      (X.rightRunLength i = 1 → X.arcLength i = 1 → X.faceOf (X.arcDart i 0) ∈ E) →
      (X.leftRunLength i = 1 → X.arcLength i = 1 → X.faceOf (X.inv (X.arcDart i 0)) ∈ E) →
      X.faceOrbits.card ≤ E.card + ((X.rightSide i).image X.faceOf).card +
        ((X.leftSide i).image X.faceOf).card + 1 := by
    intro E h3 h4
    have hsub : X.faceOrbits ⊆ insert X.exterior
        (E ∪ ((X.rightSide i).image X.faceOf ∪ (X.leftSide i).image X.faceOf)) := by
      intro f hf
      obtain ⟨d, rfl⟩ := X.mem_faceOrbits.1 hf
      rw [mem_insert, mem_union, mem_union, mem_image, mem_image]
      rcases faceOf_cases hX hS d with h | ⟨e, he, hed⟩ | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩
      · exact Or.inl h
      · rcases mem_union.1 he with he | he
        · exact Or.inr (Or.inr (Or.inl ⟨e, he, hed⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨e, he, hed⟩))
      · exact Or.inr (Or.inl (by rw [h]; exact h3 h1 h2))
      · exact Or.inr (Or.inl (by rw [h]; exact h4 h1 h2))
    have := card_le_card hsub
    have h1 := card_insert_le X.exterior
      (E ∪ ((X.rightSide i).image X.faceOf ∪ (X.leftSide i).image X.faceOf))
    have h2 := card_union_le E ((X.rightSide i).image X.faceOf ∪ (X.leftSide i).image X.faceOf)
    have h3 := card_union_le ((X.rightSide i).image X.faceOf) ((X.leftSide i).image X.faceOf)
    omega
  simp only [rightSide, leftSide] at hsides hfacesE
  -- both cut lists are nonempty, or the other one is empty
  have hcases : (2 ≤ (X.arcCutList i .right).length ∧ 2 ≤ (X.arcCutList i .left).length) ∨
      (X.arcCutList i .right = [] ∨ X.arcCutList i .left = []) := by
    obtain ⟨a, ha⟩ := even_length_arcCutList (X := X) (i := i) .right
    obtain ⟨c, hc⟩ := even_length_arcCutList (X := X) (i := i) .left
    by_cases h1 : (X.arcCutList i .right).length = 0
    · exact Or.inr (Or.inl (List.eq_nil_of_length_eq_zero h1))
    by_cases h2 : (X.arcCutList i .left).length = 0
    · exact Or.inr (Or.inr (List.eq_nil_of_length_eq_zero h2))
    exact Or.inl ⟨by omega, by omega⟩
  rcases hcases with ⟨hr, hl⟩ | hemp
  · -- both cuts are connected rotation systems: their Euler characteristics add up to `4`
    have hF0 := hfacesE ∅ (fun h1 h2 => (by omega : False).elim)
      (fun h1 h2 => (by omega : False).elim)
    have er := hχ .right hr
    have el := hχ .left hl
    have fr := hF .right hr
    have fl := hF .left hl
    have br := hle .right hr
    have bl := hle .left hl
    simp only [arcSideDarts, StrandSide.arcValue, arcCut] at er el fr fl br bl
    rw [card_empty] at hF0
    cases ζ <;> simp only [arcSideDarts, StrandSide.arcValue, arcCut] <;> omega
  · -- the other cut list is empty: then `m = 1` and the other side has no darts
    cases ζ
    · rcases hemp with he | he
      · simp [he] at hN
      have hK := arcSideDarts_eq_empty hX hS .left he
      have hl0 : (X.arcCutList i .left).length = 0 := by rw [he]; rfl
      have hF1 := hfacesE {X.faceOf (X.inv (X.arcDart i 0))} (fun h1 h2 => (by omega : False).elim)
        (fun _ _ => mem_singleton_self _)
      have er := hχ .right hN
      have fr := hF .right hN
      have br := hle .right hN
      simp only [arcSideDarts, StrandSide.arcValue, arcCut] at hK er fr br
      simp only [arcSideDarts, StrandSide.arcValue, arcCut]
      rw [hK, image_empty, card_empty, card_singleton] at hF1
      rw [hK, card_empty] at hsides
      omega
    · rcases hemp with he | he
      · have hK := arcSideDarts_eq_empty hX hS .right he
        have hr0 : (X.arcCutList i .right).length = 0 := by rw [he]; rfl
        have hF1 := hfacesE {X.faceOf (X.arcDart i 0)} (fun _ _ => mem_singleton_self _)
          (fun h1 h2 => (by omega : False).elim)
        have el := hχ .left hN
        have fl := hF .left hN
        have bl := hle .left hN
        simp only [arcSideDarts, StrandSide.arcValue, arcCut] at hK el fl bl
        simp only [arcSideDarts, StrandSide.arcValue, arcCut]
        rw [hK, image_empty, card_empty, card_singleton] at hF1
        rw [hK, card_empty] at hsides
        omega
      · simp [he] at hN

end ArcCutTriple

/-! ### Triple points and strand paths of a cut -/

section CutStrands

variable {X} {K : Finset H} {L : List H} {s : ℕ}

namespace IsCutData

variable (hc : X.IsCutData K L)

include hc

/-- The triple points of the cut are the vertices of `X` at the darts of `K` outside `L`. -/
theorem internalVertices_cut :
    (X.cut K L s).internalVertices =
      ((K.filter (· ∉ L)).image X.vertexOf).image (liftVertex K L.length) := by
  ext v
  rw [DiskMap.mem_internalVertices, RotationSystem.mem_vertices, mem_image]
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    obtain ⟨d, hd, rfl⟩ := hc.cut_not_isBoundaryVertex_iff.1 hx
    exact ⟨X.vertexOf d.1, mem_image.2 ⟨d.1, mem_filter.2 ⟨d.2, hd⟩, rfl⟩,
      (hc.cut_vertexOf_inl_of_notMem d hd).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hw
    obtain ⟨hdK, hdL⟩ := mem_filter.1 hd
    rw [← hc.cut_vertexOf_inl_of_notMem (s := s) ⟨d, hdK⟩ hdL]
    exact ⟨⟨_, rfl⟩, hc.cut_not_isBoundaryVertex_vertexOf_inl hdL⟩

/-- A step of a strand path of the cut between darts over `K` is a step of `X`. -/
theorem strandStep_of_cut (hinv : Function.Involutive X.inv) {a a' : {d // d ∈ K}}
    (h : (X.cut K L s).StrandStep (.inl a) (.inl a')) : X.StrandStep a.1 a'.1 := by
  obtain ⟨h1, h2⟩ := h
  have h1' : ¬(X.cut K L s).IsBoundaryVertex ((X.cut K L s).vertexOf
      (.inl ⟨X.inv a.1, hc.inv_mem _ a.2⟩)) := by
    have := h1
    unfold RunsToEndpoint at this
    rwa [hc.cut_inv_inl hinv] at this
  rw [hc.cut_inv_inl hinv] at h2
  obtain ⟨c, hcL, hc'⟩ := hc.cut_not_isBoundaryVertex_iff.1 h1'
  have hcv : c = ⟨X.inv a.1, hc.inv_mem _ a.2⟩ := (Sum.inl_injective hc').symm
  subst hcv
  obtain ⟨hm, -, he⟩ := hc.cut_rot_pow_inl_of_notMem (s := s) _ hcL 3
  rw [he] at h2
  exact ⟨hc.not_isBoundaryVertex _ (hc.inv_mem _ a.2) hcL,
    congrArg Subtype.val (Sum.inl_injective h2)⟩

omit [Fintype H] [DecidableEq H] hc in
private theorem exists_eq_map_inl {N : ℕ} :
    ∀ P : List (CutDart K N), (∀ e ∈ P, e.isLeft) →
      ∃ Q : List {d // d ∈ K}, P = Q.map Sum.inl
  | [], _ => ⟨[], rfl⟩
  | e :: P, h => by
    obtain ⟨Q, hQ⟩ := exists_eq_map_inl P fun x hx => h x (List.mem_cons_of_mem _ hx)
    rcases e with d | e
    · exact ⟨d :: Q, by rw [hQ]; rfl⟩
    · have := h _ List.mem_cons_self
      simp at this

/-- **Strand paths of the cut are strand paths of `X`**: a strand path of the cut consists of
darts over `K`, and these form a strand path of `X`. -/
theorem exists_isStrandPath_of_isStrandPath_cut (hX : X.IsPreTripleDiagram)
    {P : List (CutDart K L.length)} (hP : (X.cut K L s).IsStrandPath P) :
    ∃ Q : List {d // d ∈ K}, P = Q.map Sum.inl ∧ X.IsStrandPath (Q.map Subtype.val) := by
  obtain ⟨Q, rfl⟩ := exists_eq_map_inl P fun e he => by
    have := hP.notMem_bdry e he
    rw [mem_cut_bdry] at this
    cases e <;> simp_all
  refine ⟨Q, rfl, ?_⟩
  obtain ⟨hne, -, hout, hchain⟩ := hP
  refine ⟨fun h => hne (List.map_eq_nil_iff.2 (List.map_eq_nil_iff.1 h)), fun e he => ?_,
    fun e he => ?_, ?_⟩
  · obtain ⟨d, -, rfl⟩ := List.mem_map.1 he
    exact hc.notMem_bdry _ d.2
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
    exact hout (.inl d) (List.mem_map_of_mem hd)
  · rw [List.isChain_map] at hchain ⊢
    exact hchain.imp fun a a' h => hc.strandStep_of_cut hX.inv_involutive h

/-- A monogon of the cut is a monogon of `X`. -/
theorem isMonogon_of_isMonogon_cut (hX : X.IsPreTripleDiagram) {Q : List {d // d ∈ K}}
    (hP : (X.cut K L s).IsMonogon (Q.map Sum.inl)) : X.IsMonogon (Q.map Subtype.val) := by
  obtain ⟨Q', hQ', hpath⟩ := hc.exists_isStrandPath_of_isStrandPath_cut hX hP.isStrandPath
  obtain rfl : Q = Q' := (List.map_injective_iff.2 Sum.inl_injective) hQ'
  obtain ⟨-, hstart, hend, hinvne⟩ := hP
  cases Q with
  | nil => exact absurd rfl hpath.ne_nil
  | cons e₁ Q =>
    obtain ⟨eₘ, hlast⟩ :=
      Option.isSome_iff_exists.1 (List.getLast?_isSome.2 (List.cons_ne_nil e₁ Q))
    have hstart' : (X.cut K L s).pathStart ((e₁ :: Q).map Sum.inl) =
        (X.cut K L s).vertexOf (.inl e₁) := rfl
    have hend' : (X.cut K L s).pathEnd ((e₁ :: Q).map Sum.inl) =
        (X.cut K L s).vertexOf ((X.cut K L s).inv (.inl eₘ)) := by
      apply pathEnd_of_getLast?
      rw [List.getLast?_map, hlast]
      rfl
    rw [hstart'] at hstart hend
    rw [hend'] at hend
    have h₁ : e₁.1 ∉ L := by
      obtain ⟨d, hd, he⟩ := hc.cut_not_isBoundaryVertex_iff.1
        ((X.cut K L s).mem_internalVertices.1 hstart).2
      rw [Sum.inl_injective he]
      exact hd
    refine ⟨hpath, X.vertexOf_mem_internalVertices.2 (hc.not_isBoundaryVertex _ e₁.2 h₁),
      ?_, ?_⟩
    · rw [hc.cut_inv_inl hX.inv_involutive] at hend
      have hmem : (Sum.inl ⟨X.inv eₘ.1, hc.inv_mem _ eₘ.2⟩ : CutDart K L.length) ∈
          (X.cut K L s).vertexOf (.inl e₁) := hend ▸ (X.cut K L s).self_mem_vertexOf _
      rw [hc.cut_vertexOf_inl_of_notMem e₁ h₁, mem_liftVertex] at hmem
      obtain ⟨c, hcv, hc'⟩ := hmem
      rw [show c.1 = X.inv eₘ.1 from
        congrArg Subtype.val (Sum.inl_injective hc').symm] at hcv
      have e1 : X.pathEnd ((e₁ :: Q).map Subtype.val) = X.vertexOf (X.inv eₘ.1) := by
        apply pathEnd_of_getLast?
        rw [List.getLast?_map, hlast]
        rfl
      rw [e1, X.vertexOf_eq_of_mem hcv]
      rfl
    · intro a ha c hc'
      simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      rw [List.getLast?_map, hlast] at hc'
      simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hc'
      subst ha hc'
      intro heq
      apply hinvne (.inl e₁) rfl (.inl eₘ) (by rw [List.getLast?_map, hlast]; rfl)
      rw [hc.cut_inv_inl hX.inv_involutive]
      obtain ⟨hm, -, he⟩ := hc.cut_rot_pow_inl_of_notMem (s := s) e₁ h₁ 3
      rw [he]
      exact congrArg Sum.inl (Subtype.ext heq)

/-- An arc of the cut starts at a dart of `L` and ends at the reverse of a dart of `L`. -/
theorem mem_list_of_eq_arc_cut (hX : X.IsPreTripleDiagram) {Q : List {d // d ∈ K}}
    (hne : Q ≠ []) {j : Fin (L.length / 2)} (hQ : Q.map Sum.inl = (X.cut K L s).arc j) :
    (∀ a ∈ (Q.map Subtype.val).head?, a ∈ L) ∧
      ∀ a ∈ (Q.map Subtype.val).getLast?, X.inv a ∈ L := by
  have hlen : (X.cut K L s).arcLength j = Q.length := by
    rw [← length_arc, ← hQ, List.length_map]
  obtain ⟨M, hM⟩ : ∃ M, Q.length = M + 1 := ⟨Q.length - 1, by
    have := List.length_pos_of_ne_nil hne
    omega⟩
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- the first dart is the dart `g_k` of the endpoint `ε'(j)`
    obtain ⟨d, Q', rfl⟩ := List.exists_cons_of_ne_nil hne
    have h0 : ((d :: Q').map Sum.inl)[0]? = some ((X.cut K L s).arcDart j 0) := by
      rw [hQ, arc, List.getElem?_map, List.getElem?_range (by omega)]
      rfl
    simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at ha
    subst ha
    simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq, arcDart_zero,
      cut_endDart, hc.cutListDart_eq] at h0
    rw [Sum.inl_injective h0]
    exact List.getElem_mem _
  · -- the last dart runs to an endpoint of the cut
    have hlast : (Q.map Sum.inl)[M]? = some ((X.cut K L s).arcDart j M) := by
      rw [hQ, arc, List.getElem?_map, List.getElem?_range (by omega)]
      rfl
    have hr := ((X.cut K L s).arcLength_eq_succ_iff.1 (hlen.trans hM)).1
    rw [List.getLast?_map, Option.mem_def, Option.map_eq_some_iff] at ha
    obtain ⟨d, hd, rfl⟩ := ha
    rw [List.getLast?_eq_getElem?, hM, Nat.add_sub_cancel] at hd
    rw [List.getElem?_map, hd, Option.map_some, Option.some.injEq] at hlast
    rw [← hlast] at hr
    change (X.cut K L s).IsBoundaryVertex ((X.cut K L s).vertexOf
      ((X.cut K L s).inv (.inl d))) at hr
    rw [hc.cut_inv_inl hX.inv_involutive] at hr
    rcases hc.cutDart_cases (.inl ⟨X.inv d.1, hc.inv_mem _ d.2⟩) with ⟨c, hcL, hc'⟩ | ⟨k, hk⟩
    · rw [hc'] at hr
      exact absurd hr (hc.cut_not_isBoundaryVertex_vertexOf_inl hcL)
    · simp only [cutTriple, hc.cutListDart_eq, mem_insert, mem_singleton, reduceCtorEq,
        or_false, Sum.inl.injEq, Subtype.mk.injEq] at hk
      rw [hk]
      exact List.getElem_mem _

end IsCutData

end CutStrands

/-! ### The main results on cuts along simple arcs -/

section ArcCutMain

variable {X} {i : Fin b}

/-- A dart of `H_ζ(S)` outside the cut list lies at a triple point avoided by `S`. -/
private theorem avoided_of_mem_arcSideDarts (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) {d : H} (hd : d ∈ X.arcSideDarts i ζ) (hL : d ∉ X.arcCutList i ζ) :
    X.vertexOf d ∈ X.internalVertices ∧ ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d) := by
  cases ζ
  · exact (hS.mem_rightCutList_or_of_mem_rightSide hX hd).resolve_left hL
  · exact (hS.mem_leftCutList_or_of_mem_leftSide hX hd).resolve_left hL

/-- A dart at a triple point avoided by `S` is not in a cut list. -/
private theorem notMem_arcCutList_of_avoided (hX : X.IsTripleDiagram) (ζ : StrandSide) {d : H}
    (hint : X.vertexOf d ∈ X.internalVertices)
    (hpass : ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) : d ∉ X.arcCutList i ζ := by
  intro hL
  have := (match ζ, hL with
    | .right, hL => isBoundaryVertex_or_passesThrough_of_mem_rightCutList hX hL
    | .left, hL => isBoundaryVertex_or_passesThrough_of_mem_leftCutList hX hL)
  exact this.elim (X.mem_internalVertices.1 hint).2 hpass

/-- **The cut is a triple diagram**: the cut of a triple diagram along a simple arc on a side `ζ`
with `N_ζ ≥ 2` is a triple diagram (with `N_ζ / 2` arcs, see
`two_mul_length_arcCutList_div_two`). -/
@[cluster_algebras "lem_arc_cut_triple"]
theorem IsSimpleArc.isTripleDiagram_arcCut (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) (hN : 2 ≤ (X.arcCutList i ζ).length) : (X.arcCut i ζ).IsTripleDiagram :=
  (isPreTripleDiagram_arcCut hX hS ζ hN).isTripleDiagram
    (isConnected_arcCut hX hS ζ (by omega)).transitive (euler_arcCut hX hS ζ hN)

/-- **The cut is a triple diagram**: the cut list has even length `N_ζ`, so the cut has `N_ζ / 2`
arcs and `2 (N_ζ / 2) = N_ζ` endpoints. -/
@[cluster_algebras "lem_arc_cut_triple"]
theorem two_mul_length_arcCutList_div_two (ζ : StrandSide) :
    2 * ((X.arcCutList i ζ).length / 2) = (X.arcCutList i ζ).length := by
  obtain ⟨t, ht⟩ := even_length_arcCutList (X := X) (i := i) ζ
  omega

open scoped Classical in
/-- **The cut is a triple diagram**: the triple points of the cut are exactly the triple points of
`X` avoided by `S` whose darts lie in `H_ζ(S)`, each carried by the darts over it. -/
@[cluster_algebras "lem_arc_cut_triple"]
theorem IsSimpleArc.internalVertices_arcCut (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) :
    (X.arcCut i ζ).internalVertices =
      (X.internalVertices.filter fun v =>
        ¬X.PassesThrough (X.arc i).toFinset v ∧ v ⊆ X.arcSideDarts i ζ).image
        (liftVertex (X.arcSideDarts i ζ) (X.arcCutList i ζ).length) := by
  have hc := hS.isCutData_arcCutList hX ζ
  rw [arcCut, hc.internalVertices_cut]
  congr 1
  ext v
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨d, ⟨hdK, hdL⟩, rfl⟩
    obtain ⟨hint, hpass⟩ := avoided_of_mem_arcSideDarts hX hS ζ hdK hdL
    exact ⟨hint, hpass, fun e he => (hc.mem_of_mem_vertexOf d hdK hdL e he).1⟩
  · rintro ⟨hint, hpass, hsub⟩
    obtain ⟨x, rfl⟩ := X.mem_vertices.1 (X.mem_internalVertices.1 hint).1
    exact ⟨x, ⟨hsub (X.self_mem_vertexOf x), notMem_arcCutList_of_avoided hX ζ hint hpass⟩,
      rfl⟩

open scoped Classical in
/-- **The cut has fewer triple points**: if the simple arc `S` has `m - 1` triple points, the cut
along `S` has at most `T - (m - 1)` triple points, where `T` is the number of triple points of
`X`. -/
@[cluster_algebras "lem_arc_cut_fewer"]
theorem IsSimpleArc.card_internalVertices_arcCut_le (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) (ζ : StrandSide) :
    (X.arcCut i ζ).internalVertices.card ≤ X.internalVertices.card - (X.arcLength i - 1) := by
  set Z : Finset (Finset H) :=
    (range (X.arcLength i - 1)).image fun k => X.vertexOf (X.inv (X.arcDart i k)) with hZ
  have hZcard : Z.card = X.arcLength i - 1 := by
    rw [hZ, card_image_of_injOn, card_range]
    intro k hk l hl h
    simp only [coe_range, Set.mem_Iio] at hk hl
    exact hS k l (by omega) (by omega) h
  have hZsub : Z ⊆ X.internalVertices := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hv
    exact X.vertexOf_mem_internalVertices.2
      (not_runsToEndpoint_arcDart hX (by simp at hk; omega))
  have hsub : (X.internalVertices.filter fun v =>
      ¬X.PassesThrough (X.arc i).toFinset v ∧ v ⊆ X.arcSideDarts i ζ) ⊆
      X.internalVertices \ Z := by
    intro v hv
    obtain ⟨hint, hpass, -⟩ := mem_filter.1 hv
    refine mem_sdiff.2 ⟨hint, fun hvZ => hpass ?_⟩
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hvZ
    have := passesThrough_rot_pow_inv_arcDart hX (i := i) (k := k) (by simp at hk; omega) 0
    rwa [pow_zero, Equiv.Perm.one_apply] at this
  rw [hS.internalVertices_arcCut hX ζ]
  calc _ ≤ _ := card_image_le
    _ ≤ (X.internalVertices \ Z).card := card_le_card hsub
    _ = _ := by rw [card_sdiff_of_subset hZsub, hZcard]

/-- **Strand paths of the cut are strand paths of `X`**: a strand path `P` of `X|_{S,ζ}` consists
of darts `Sum.inl d` with `d ∈ H_ζ(S)`, and these darts form a strand path of `X`. -/
@[cluster_algebras "lem_arc_cut_strand_paths"]
theorem IsSimpleArc.exists_isStrandPath_of_isStrandPath_arcCut (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) (ζ : StrandSide) {P : List (CutDart (X.arcSideDarts i ζ)
      (X.arcCutList i ζ).length)} (hP : (X.arcCut i ζ).IsStrandPath P) :
    ∃ Q : List {d // d ∈ X.arcSideDarts i ζ}, P = Q.map Sum.inl ∧
      X.IsStrandPath (Q.map Subtype.val) :=
  (hS.isCutData_arcCutList hX ζ).exists_isStrandPath_of_isStrandPath_cut hX.toIsPreTripleDiagram
    hP

/-- **Strand paths of the cut are strand paths of `X`**: a monogon of `X|_{S,ζ}` is a monogon of
`X`. -/
@[cluster_algebras "lem_arc_cut_strand_paths"]
theorem IsSimpleArc.isMonogon_of_isMonogon_arcCut (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) (ζ : StrandSide) {Q : List {d // d ∈ X.arcSideDarts i ζ}}
    (hP : (X.arcCut i ζ).IsMonogon (Q.map Sum.inl)) : X.IsMonogon (Q.map Subtype.val) :=
  (hS.isCutData_arcCutList hX ζ).isMonogon_of_isMonogon_cut hX.toIsPreTripleDiagram hP

/-- **Strand paths of the cut are strand paths of `X`**: if a strand path `(a₁, …, a_k)` of
`X|_{S,ζ}` is an arc of `X|_{S,ζ}`, then `a₁` and `ā_k` belong to the `ζ` cut list. -/
@[cluster_algebras "lem_arc_cut_strand_paths"]
theorem IsSimpleArc.mem_arcCutList_of_eq_arc_arcCut (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) (ζ : StrandSide) {Q : List {d // d ∈ X.arcSideDarts i ζ}}
    (hP : (X.arcCut i ζ).IsStrandPath (Q.map Sum.inl))
    {j : Fin ((X.arcCutList i ζ).length / 2)} (hQ : Q.map Sum.inl = (X.arcCut i ζ).arc j) :
    (∀ a ∈ (Q.map Subtype.val).head?, a ∈ X.arcCutList i ζ) ∧
      ∀ a ∈ (Q.map Subtype.val).getLast?, X.inv a ∈ X.arcCutList i ζ :=
  (hS.isCutData_arcCutList hX ζ).mem_list_of_eq_arc_cut hX.toIsPreTripleDiagram
    (fun h => hP.ne_nil (by rw [h]; rfl)) hQ

end ArcCutMain

/-! ### Swivel moves of a cut -/

section CutSwivel

/-- A face orbit through a dart `d` with `φ(φ(d)) = d` is `{d, φ(d)}`. -/
private theorem faceOf_eq_pair_of_facePerm_facePerm {α : Type*} [Fintype α] [DecidableEq α]
    {R : RotationSystem α} {d : α} (h : R.facePerm (R.facePerm d) = d) :
    R.faceOf d = {d, R.facePerm d} := by
  ext e
  rw [RotationSystem.mem_faceOf, mem_insert, mem_singleton]
  constructor
  · intro he
    obtain ⟨n, rfl⟩ := he.exists_nat_pow_eq
    clear he
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h' | h' <;> rw [h']
      · exact Or.inr rfl
      · exact Or.inl h
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)

omit [Fintype H] in
/-- A swap of two darts over `K`, applied to a dart over `K`, as a dart over `K`. -/
private theorem swap_inl_inl {K : Finset H} {N : ℕ} (a c w : {d // d ∈ K}) :
    Equiv.swap (Sum.inl a : CutDart K N) (.inl c) (.inl w) =
      .inl ⟨Equiv.swap a.1 c.1 w.1, by
        rw [Equiv.swap_apply_def]; split_ifs <;> simp [a.2, c.2, w.2]⟩ := by
  rw [Sum.inl_injective.swap_apply]
  congr 1
  exact Subtype.ext (Subtype.val_injective.swap_apply _ _ _).symm

omit [Fintype H] in
/-- A swap of two darts over `K` fixes the new symbols. -/
private theorem swap_inl_inr {K : Finset H} {N : ℕ} (a c : {d // d ∈ K}) (p : Fin N × Bool) :
    Equiv.swap (Sum.inl a : CutDart K N) (.inl c) (.inr p) = .inr p :=
  Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)

variable {X} {K : Finset H} {L : List H} {s : ℕ}

namespace IsCutData

variable (hc : X.IsCutData K L)

include hc

/-- A dart over `K` on a face of the cut containing no new symbol is not in `L`, and neither is its
reverse. -/
private theorem notMem_of_mem_faceOf_cut (hinv : Function.Involutive X.inv)
    {x : CutDart K L.length} (hx : Disjoint ((X.cut K L s).faceOf x) (X.cut K L s).bdry)
    {e : {d // d ∈ K}} (he : .inl e ∈ (X.cut K L s).faceOf x) : e.1 ∉ L ∧ X.inv e.1 ∉ L := by
  have hface := (X.cut K L s).faceOf_eq_of_mem he
  have hB : ∀ p : Fin L.length × Bool, (Sum.inr p : CutDart K L.length) ∉ (X.cut K L s).faceOf x :=
    fun p hp => disjoint_left.1 hx hp (mem_cut_bdry.2 rfl)
  constructor
  · intro heL
    obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 heL
    have h1 := hc.cut_facePerm_inr_false hinv (s := s) ((finRotate _).symm ⟨k, hk⟩)
    rw [Equiv.apply_symm_apply, hc.cutListDart_eq] at h1
    obtain rfl : (⟨L[k], hc.getElem_mem ⟨k, hk⟩⟩ : {d // d ∈ K}) = e := Subtype.ext hke
    apply hB (((finRotate _).symm ⟨k, hk⟩), false)
    rw [← hface, RotationSystem.mem_faceOf]
    have h2 := Equiv.Perm.sameCycle_apply_right.2
      (Equiv.Perm.SameCycle.refl (X.cut K L s).facePerm
        (Sum.inr ((finRotate _).symm ⟨k, hk⟩, false)))
    rw [h1] at h2
    exact h2.symm
  · intro heL
    obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 heL
    have h1 := hc.cut_facePerm_inl_of_eq hinv (s := s) e ⟨k, hk⟩ hke.symm
    apply hB (⟨k, hk⟩, false)
    rw [← hface, ← h1]
    exact RotationSystem.facePerm_mem_faceOf _ _

/-- **A digon of the cut is a digon of `X`.** If the face of the cut through `e` is a digon, then
`e` and `φ(e)` are darts of `K` outside `L`, the face permutation of the cut sends `e` to `φ(e)`,
and the face of `X` through `e` is a digon. -/
theorem isDigon_of_isDigon_cut (hX : X.IsPreTripleDiagram) {e : {d // d ∈ K}}
    (hD : (X.cut K L s).IsDigon ((X.cut K L s).faceOf (.inl e))) :
    ∃ h₂ : X.facePerm e.1 ∈ K, (X.cut K L s).facePerm (.inl e) = .inl ⟨X.facePerm e.1, h₂⟩ ∧
      e.1 ∉ L ∧ X.facePerm e.1 ∉ L ∧ X.facePerm (X.facePerm e.1) = e.1 ∧
      X.IsDigon (X.faceOf e.1) := by
  have hinv := hX.inv_involutive
  have hdisj := ((X.cut K L s).mem_internalFaces.1 hD.1).2
  obtain ⟨he1, hinv1⟩ := hc.notMem_of_mem_faceOf_cut hinv hdisj
    ((X.cut K L s).self_mem_faceOf _)
  have hφ1 := hc.cut_facePerm_inl_of_notMem hinv (s := s) e hinv1
  set e₂ : {d // d ∈ K} := ⟨X.facePerm e.1, hc.rot_mem (hc.inv_mem _ e.2) hinv1⟩ with he₂
  have hmem2 : (.inl e₂ : CutDart K L.length) ∈ (X.cut K L s).faceOf (.inl e) := by
    rw [← hφ1]
    exact (X.cut K L s).facePerm_mem_faceOf _
  obtain ⟨he2, hinv2⟩ := hc.notMem_of_mem_faceOf_cut hinv hdisj hmem2
  have hφ2 := hc.cut_facePerm_inl_of_notMem hinv (s := s) e₂ hinv2
  have hφφ := hD.facePerm_facePerm
  rw [hφ1, hφ2] at hφφ
  have hφφX : X.facePerm (X.facePerm e.1) = e.1 :=
    congrArg Subtype.val (Sum.inl_injective hφφ)
  have hface := faceOf_eq_pair_of_facePerm_facePerm (R := X.toRotationSystem) hφφX
  refine ⟨e₂.2, hφ1, he1, he2, hφφX, ?_, e.1, hface, ?_⟩
  · refine X.mem_internalFaces.2 ⟨X.mem_faces.2 ⟨fun h => ?_, X.faceOf_mem_faceOrbits _⟩, ?_⟩
    · have : e.1 ∈ X.exterior := h ▸ X.self_mem_faceOf _
      exact hc.notMem_bdry _ e.2 (mem_filter.1 this).1
    · rw [hface]
      refine disjoint_left.2 fun z hz => ?_
      rcases mem_insert.1 hz with rfl | hz
      · exact hc.notMem_bdry _ e.2
      · rw [mem_singleton.1 hz]
        exact hc.notMem_bdry _ e₂.2
  · intro h
    apply hD.vertexOf_ne
    rw [hφ1, hc.cut_vertexOf_inl_of_notMem e he1, hc.cut_vertexOf_inl_of_notMem e₂ he2]
    exact congrArg _ h

/-- **The cut commutes with a swivel move.** If the face of the cut through `e` is a digon, then
cutting the swivel move of `X` at `e` along `(K, L)` gives the swivel move of the cut at `e`. -/
theorem swivelMove_cut (hX : X.IsPreTripleDiagram) {e : {d // d ∈ K}}
    (hD : (X.cut K L s).IsDigon ((X.cut K L s).faceOf (.inl e))) :
    (X.swivelMove e.1).cut K L s = (X.cut K L s).swivelMove (.inl e) := by
  obtain ⟨h₂, hφ, he1, he2, -, hDX⟩ := hc.isDigon_of_isDigon_cut hX hD
  -- the darts of `x ∪ y` lie over `K` outside `L`
  have hUK : ∀ z ∈ X.vertexOf e.1 ∪ X.vertexOf (X.facePerm e.1), z ∈ K ∧ z ∉ L := by
    intro z hz
    rcases mem_union.1 hz with hz | hz
    · exact hc.mem_of_mem_vertexOf _ e.2 he1 z hz
    · exact hc.mem_of_mem_vertexOf _ h₂ he2 z hz
  -- the swivel rotation is `σ ∘ τ`
  set τ : Equiv.Perm H :=
    (Equiv.swap e.1 ((X.rot ^ 4) (X.facePerm e.1)) * Equiv.swap e.1 ((X.rot ^ 2) e.1)) *
      (Equiv.swap ((X.rot ^ 4) e.1) ((X.rot ^ 2) (X.facePerm e.1)) *
        Equiv.swap ((X.rot ^ 4) e.1) (X.facePerm e.1)) with hτ
  have hsw : ∀ z, X.swivelRot e.1 z = X.rot (τ z) := fun z => rfl
  have hτU : ∀ z, z ∉ X.vertexOf e.1 ∪ X.vertexOf (X.facePerm e.1) → τ z = z := fun z hz =>
    X.rot.injective ((hsw z).symm.trans (swivelRot_apply_of_notMem hz))
  have hτU' : ∀ z, z ∈ X.vertexOf e.1 ∪ X.vertexOf (X.facePerm e.1) →
      τ z ∈ X.vertexOf e.1 ∪ X.vertexOf (X.facePerm e.1) := by
    intro z hz
    have h1 := (hDX.vertexOf_swivelMove_of_mem hX hz).1
      ((X.swivelMove e.1).rot_mem_vertexOf z)
    rw [swivelMove_rot, hsw] at h1
    exact rot_mem_union_vertexOf_iff.1 h1
  have hτL : ∀ z, z ∉ L → τ z ∉ L := by
    intro z hz
    by_cases hzU : z ∈ X.vertexOf e.1 ∪ X.vertexOf (X.facePerm e.1)
    · exact (hUK _ (hτU' z hzU)).2
    · rw [hτU z hzU]; exact hz
  have key : ∀ w w' : {d // d ∈ K}, w'.1 = τ w.1 →
      (X.swivelMove e.1).cutRotFun K L (.inl w) = X.cutRotFun K L (.inl w') := by
    intro w w' hw'
    by_cases hwL : w.1 ∈ L
    · have hwU : w.1 ∉ X.vertexOf e.1 ∪ X.vertexOf (X.facePerm e.1) :=
        fun h => (hUK _ h).2 hwL
      have : w' = w := Subtype.ext (hw'.trans (hτU _ hwU))
      subst this
      simp only [cutRotFun, dif_pos hwL]
    · have hw'L : w'.1 ∉ L := hw' ▸ hτL _ hwL
      rw [hc.cutRotFun_inl_of_notMem w' hw'L]
      have hK : (X.swivelMove e.1).rot w.1 ∈ K := by
        rw [swivelMove_rot, hsw, ← hw']; exact hc.rot_mem w'.2 hw'L
      simp only [cutRotFun, dif_neg hwL, dif_pos hK, Sum.inl.injEq, Subtype.mk.injEq]
      rw [swivelMove_rot, hsw, ← hw']
  -- the darts `σ^k(d₁)`, `σ^k(d₂)` of the cut
  obtain ⟨m2, -, e2⟩ := hc.cut_rot_pow_inl_of_notMem (s := s) e he1 2
  obtain ⟨m4, -, e4⟩ := hc.cut_rot_pow_inl_of_notMem (s := s) e he1 4
  obtain ⟨n2, -, f2⟩ := hc.cut_rot_pow_inl_of_notMem (s := s) ⟨_, h₂⟩ he2 2
  obtain ⟨n4, -, f4⟩ := hc.cut_rot_pow_inl_of_notMem (s := s) ⟨_, h₂⟩ he2 4
  have hfun : (X.swivelMove e.1).cutRotFun K L = ⇑((X.cut K L s).swivelRot (.inl e)) := by
    funext z
    simp only [swivelRot, Equiv.Perm.mul_apply, hφ, e2, e4, f2, f4]
    rcases z with w | p
    · simp only [swap_inl_inl]
      rw [hc.cut_rot_apply]
      refine key w _ ?_
      rfl
    · simp only [swap_inl_inr]
      rw [hc.cut_rot_apply]
      rcases p with ⟨k, _ | _⟩ <;> rfl
  have hbij : Function.Bijective ((X.swivelMove e.1).cutRotFun K L) := by
    rw [hfun]; exact Equiv.bijective _
  have hrot : permOfBijectiveOrOne ((X.swivelMove e.1).cutRotFun K L) =
      (X.cut K L s).swivelRot (.inl e) :=
    Equiv.ext fun z => by rw [permOfBijectiveOrOne_apply hbij, hfun]
  change ({ (X.cut K L s) with
      rot := permOfBijectiveOrOne ((X.swivelMove e.1).cutRotFun K L) } : TripleData _ _) =
    { (X.cut K L s) with rot := (X.cut K L s).swivelRot (.inl e) }
  rw [hrot]

end IsCutData

end CutSwivel

/-! ### Swivel moves of a cut along a simple arc -/

section ArcCutSwivel

variable {X} {i : Fin b} {d₁ : H}

/-- The sets of darts containing `Λ` and closed under `d ↦ d̄` and under `d ↦ σ^{±1}(d)` at triple
points avoided by the arc from `s_i`. -/
private def sideClosed (Y : TripleData H b) (j : Fin b) (Λ : List H) : Set (Set H) :=
  {A | (∀ d ∈ Λ, d ∈ A) ∧ (∀ d ∈ A, Y.inv d ∈ A) ∧
      ∀ d ∈ A, Y.vertexOf d ∈ Y.internalVertices →
        ¬Y.PassesThrough (Y.arc j).toFinset (Y.vertexOf d) → Y.rot d ∈ A ∧ Y.rot.symm d ∈ A}

/-- Off the two triple points `x ∪ y` of the digon `f(d₁)`, the powers of the swivel rotation are
those of `σ`. -/
private theorem swivelRot_pow_apply_of_notMem {z : H}
    (hz : z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) (n : ℕ) :
    (X.swivelRot d₁ ^ n) z = (X.rot ^ n) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : (X.rot ^ n) z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) :=
      notMem_of_mem_vertexOf hz ((RotationSystem.mem_vertexOf _).2
        (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)))
    rw [pow_succ', Equiv.Perm.mul_apply, ih, swivelRot_apply_of_notMem hn, pow_succ',
      Equiv.Perm.mul_apply]

/-- Off `x ∪ y`, the inverse of the swivel rotation is that of `σ`. -/
private theorem swivelRot_symm_apply_of_notMem {z : H}
    (hz : z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) :
    (X.swivelRot d₁).symm z = X.rot.symm z := by
  rw [Equiv.symm_apply_eq, swivelRot_apply_of_notMem
    (notMem_of_mem_vertexOf hz (X.rot_symm_mem_vertexOf z)), Equiv.apply_symm_apply]

/-- The strand map of the swivel move agrees with that of `X` at darts whose reverse is not in
`x ∪ y`. -/
private theorem strandMap_swivelMove_of_notMem (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) {z : H}
    (hz : X.inv z ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)) :
    (X.swivelMove d₁).strandMap z = X.strandMap z := by
  have hE : (X.swivelMove d₁).RunsToEndpoint z ↔ X.RunsToEndpoint z :=
    hd.isBoundaryVertex_swivelMove_iff hX (X.inv z)
  by_cases h : X.RunsToEndpoint z
  · rw [(X.swivelMove d₁).strandMap_of_runsToEndpoint (hE.2 h), X.strandMap_of_runsToEndpoint h]
    rfl
  · rw [strandMap, if_neg (mt hE.1 h), strandMap, if_neg h]
    exact swivelRot_pow_apply_of_notMem hz 3

variable (hX : X.IsTripleDiagram) (hd : X.IsDigon (X.faceOf d₁))
  (hU : ∀ e ∈ X.arcDarts i, e ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁))

include hX hd hU

private theorem arcDart_swivelMove {k : ℕ} (hk : k < X.arcLength i) :
    (X.swivelMove d₁).arcDart i k = X.arcDart i k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [arcDart_succ, arcDart_succ, ih (by omega)]
    exact strandMap_swivelMove_of_notMem hX.toIsPreTripleDiagram hd
      (hU _ (inv_arcDart_mem_arcDarts (by omega)))

private theorem arcLength_swivelMove : (X.swivelMove d₁).arcLength i = X.arcLength i := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero
    (hX.toIsPreTripleDiagram.arcLength_ne_zero i)
  have hE : ∀ z, (X.swivelMove d₁).RunsToEndpoint z ↔ X.RunsToEndpoint z := fun z =>
    hd.isBoundaryVertex_swivelMove_iff hX.toIsPreTripleDiagram (X.inv z)
  obtain ⟨h1, h2⟩ := X.arcLength_eq_succ_iff.1 hn
  rw [hn, arcLength_eq_succ_iff]
  refine ⟨?_, fun k hk => ?_⟩
  · rw [hE, arcDart_swivelMove hX hd hU (by omega)]
    exact h1
  · rw [hE, arcDart_swivelMove hX hd hU (by omega)]
    exact h2 k hk

private theorem arc_swivelMove : (X.swivelMove d₁).arc i = X.arc i := by
  unfold arc
  rw [arcLength_swivelMove hX hd hU]
  exact List.map_congr_left fun k hk =>
    arcDart_swivelMove hX hd hU (List.mem_range.1 hk)

private theorem arcDarts_swivelMove : (X.swivelMove d₁).arcDarts i = X.arcDarts i := by
  unfold arcDarts
  rw [arc_swivelMove hX hd hU]
  rfl

private theorem isSimpleArc_swivelMove (hS : X.IsSimpleArc i) :
    (X.swivelMove d₁).IsSimpleArc i := by
  intro k l hk hl h
  rw [arcLength_swivelMove hX hd hU] at hk hl
  rw [arcDart_swivelMove hX hd hU (by omega), arcDart_swivelMove hX hd hU (by omega),
    swivelMove_inv, vertexOf_swivelMove_of_notMem (hU _ (inv_arcDart_mem_arcDarts (by omega))),
    vertexOf_swivelMove_of_notMem (hU _ (inv_arcDart_mem_arcDarts (by omega)))] at h
  exact hS k l hk hl h

omit hU in
private theorem arcEndIndex_swivelMove :
    (X.swivelMove d₁).arcEndIndex i = X.arcEndIndex i := by
  unfold arcEndIndex
  rw [hd.strandPerm_swivelMove hX.toIsPreTripleDiagram]

private theorem rightCutList_swivelMove :
    (X.swivelMove d₁).rightCutList i = X.rightCutList i := by
  unfold rightCutList rightRunLength
  rw [arcEndIndex_swivelMove hX hd, arcLength_swivelMove hX hd hU]
  congr 1
  refine List.flatMap_congr fun k hk => ?_
  have hk' := List.mem_range.1 hk
  have h := hU _ (inv_arcDart_mem_arcDarts (i := i) (t := k) (by omega))
  rw [arcDart_swivelMove hX hd hU (by omega), swivelMove_rot, swivelMove_inv,
    swivelRot_apply_of_notMem h, swivelRot_pow_apply_of_notMem h]

private theorem leftCutList_swivelMove :
    (X.swivelMove d₁).leftCutList i = X.leftCutList i := by
  unfold leftCutList
  rw [arcEndIndex_swivelMove hX hd, arcLength_swivelMove hX hd hU]
  congr 1
  refine List.flatMap_congr fun k hk => ?_
  have hk' := List.mem_range.1 (List.mem_reverse.1 hk)
  have h := hU _ (inv_arcDart_mem_arcDarts (i := i) (t := k) (by omega))
  rw [arcDart_swivelMove hX hd hU (by omega), swivelMove_rot, swivelMove_inv,
    swivelRot_pow_apply_of_notMem h, swivelRot_pow_apply_of_notMem h]

private theorem arcCutList_swivelMove (ζ : StrandSide) :
    (X.swivelMove d₁).arcCutList i ζ = X.arcCutList i ζ := by
  cases ζ
  · exact rightCutList_swivelMove hX hd hU
  · exact leftCutList_swivelMove hX hd hU

private theorem mem_sideClosed_swivelMove {Λ : List H} {A : Set H}
    (hA : A ∈ sideClosed X i Λ)
    (hUA : ∀ d ∈ A, d ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) →
      ∀ z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁), z ∈ A) :
    A ∈ sideClosed (X.swivelMove d₁) i Λ := by
  have hP := hX.toIsPreTripleDiagram
  obtain ⟨h1, h2, h3⟩ := hA
  refine ⟨h1, h2, fun d hdA hint hpass => ?_⟩
  by_cases hdU : d ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁)
  · have hsub := (hd.vertexOf_swivelMove_of_mem hP hdU).1
    exact ⟨hUA d hdA hdU _ (hsub ((X.swivelMove d₁).rot_mem_vertexOf d)),
      hUA d hdA hdU _ (hsub ((X.swivelMove d₁).rot_symm_mem_vertexOf d))⟩
  · have hv := vertexOf_swivelMove_of_notMem hdU
    have hint' : X.vertexOf d ∈ X.internalVertices := by
      rw [X.vertexOf_mem_internalVertices]
      rw [(X.swivelMove d₁).vertexOf_mem_internalVertices,
        hd.isBoundaryVertex_swivelMove_iff hP] at hint
      exact hint
    have hpass' : ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d) := by
      rintro ⟨-, e, he, hev⟩
      refine hpass ⟨hint, e, by rwa [arc_swivelMove hX hd hU], ?_⟩
      rw [vertexOf_swivelMove_of_notMem (hU e (mem_union_left _ he)), hv, hev]
    obtain ⟨hr, hr'⟩ := h3 d hdA hint' hpass'
    refine ⟨?_, ?_⟩
    · rw [swivelMove_rot, swivelRot_apply_of_notMem hdU]; exact hr
    · rw [swivelMove_rot, swivelRot_symm_apply_of_notMem hdU]; exact hr'

private theorem arcSideDarts_swivelMove_subset (hS : X.IsSimpleArc i) (ζ : StrandSide)
    (hUA : ∀ d ∈ X.arcSideDarts i ζ, d ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) →
      ∀ z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁), z ∈ X.arcSideDarts i ζ) :
    (X.swivelMove d₁).arcSideDarts i ζ ⊆ X.arcSideDarts i ζ := by
  have hX₁ := hd.isTripleDiagram_swivelMove hX
  have hS₁ := isSimpleArc_swivelMove hX hd hU hS
  cases ζ
  · have hl := hS₁.isLeast_rightSide hX₁
    have hmem : (X.rightSide i : Set H) ∈
        sideClosed (X.swivelMove d₁) i ((X.swivelMove d₁).rightCutList i) := by
      rw [rightCutList_swivelMove hX hd hU]
      exact mem_sideClosed_swivelMove hX hd hU (hS.isLeast_rightSide hX).1
        fun d hd' hdU z hz => mem_coe.2 (hUA d (mem_coe.1 hd') hdU z hz)
    exact coe_subset.1 (hl.2 hmem)
  · have hl := hS₁.isLeast_leftSide hX₁
    have hmem : (X.leftSide i : Set H) ∈
        sideClosed (X.swivelMove d₁) i ((X.swivelMove d₁).leftCutList i) := by
      rw [leftCutList_swivelMove hX hd hU]
      exact mem_sideClosed_swivelMove hX hd hU (hS.isLeast_leftSide hX).1
        fun d hd' hdU z hz => mem_coe.2 (hUA d (mem_coe.1 hd') hdU z hz)
    exact coe_subset.1 (hl.2 hmem)

private theorem arcSideDarts_swivelMove (hS : X.IsSimpleArc i) {ζ : StrandSide}
    (hUK : ∀ z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁), z ∈ X.arcSideDarts i ζ)
    (ζ' : StrandSide) :
    (X.swivelMove d₁).arcSideDarts i ζ' = X.arcSideDarts i ζ' := by
  have hX₁ := hd.isTripleDiagram_swivelMove hX
  have hS₁ := isSimpleArc_swivelMove hX hd hU hS
  have hRL := disjoint_left.1 (disjoint_rightSide_leftSide (X := X) (i := i))
  have hUA : ∀ ζ'', ∀ d ∈ X.arcSideDarts i ζ'', d ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) →
      ∀ z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁), z ∈ X.arcSideDarts i ζ'' := by
    intro ζ'' d hdA hdU z hz
    have h1 := hUK d hdU
    have h2 := hUK z hz
    cases ζ <;> cases ζ''
    · exact h2
    · exact absurd hdA (hRL h1)
    · exact absurd h1 (hRL hdA)
    · exact h2
  have hsub := fun ζ'' => arcSideDarts_swivelMove_subset hX hd hU hS ζ'' (hUA ζ'')
  refine Subset.antisymm (hsub ζ') fun d hd' => ?_
  have hB : d ∉ X.bdry := (mem_arcSide.1 hd').1
  have hA : d ∉ X.arcDarts i := (mem_arcSide.1 hd').2.1
  have hcov := hS₁.arcDarts_union_rightSide_union_leftSide hX₁
  have hmem : d ∈ (X.swivelMove d₁).bdryᶜ := mem_compl.2 hB
  rw [← hcov, arcDarts_swivelMove hX hd hU, mem_union, mem_union] at hmem
  rcases hmem with (h | h) | h
  · exact absurd h hA
  · cases ζ'
    · exact h
    · exact absurd hd' (hRL (hsub .right h))
  · cases ζ'
    · exact absurd (hsub .left h) (hRL hd')
    · exact h

end ArcCutSwivel

section ArcCutSwivelMain

variable {X} {i : Fin b}

/-- **Swivel moves of the cut are swivel moves of `X`**. Let `S` be the
simple arc from `s_i` of a triple diagram `X`, `ζ` a side, and `D = f'(d₁)` a digon of `X|_{S,ζ}`
through a dart `d₁` of `H_ζ(S)`. Then `D` consists of the darts of the face `f(d₁)` of `X`, and
`f(d₁)` is a digon of `X`; `S` is a simple arc of the swivel move `X₁` of `X` at `D`, with the same
darts; the sets `H_ζ(S)` and the `ζ` cut lists of `S` in `X₁` and in `X` coincide; and
`X₁|_{S,ζ}` is the swivel move of `X|_{S,ζ}` at `D` (an equality of triple data over the same
darts, stated as `HEq` since the dart type of a cut is built from `H_ζ(S)` and the cut list). -/
@[cluster_algebras "lem_arc_cut_swivel"]
theorem IsSimpleArc.arcCut_swivelMove (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) {d₁ : H} (hd₁ : d₁ ∈ X.arcSideDarts i ζ)
    (hD : (X.arcCut i ζ).IsDigon ((X.arcCut i ζ).faceOf (.inl ⟨d₁, hd₁⟩))) :
    X.IsDigon (X.faceOf d₁) ∧
      (X.arcCut i ζ).faceOf (.inl ⟨d₁, hd₁⟩) =
        ((X.faceOf d₁).subtype (· ∈ X.arcSideDarts i ζ)).map Function.Embedding.inl ∧
      (X.swivelMove d₁).IsSimpleArc i ∧ (X.swivelMove d₁).arc i = X.arc i ∧
      (X.swivelMove d₁).arcSideDarts i ζ = X.arcSideDarts i ζ ∧
      (X.swivelMove d₁).arcCutList i ζ = X.arcCutList i ζ ∧
      HEq ((X.swivelMove d₁).arcCut i ζ) ((X.arcCut i ζ).swivelMove (.inl ⟨d₁, hd₁⟩)) := by
  have hc := hS.isCutData_arcCutList hX ζ
  obtain ⟨h₂, hφ, he1, he2, hφφ, hDX⟩ := hc.isDigon_of_isDigon_cut hX.toIsPreTripleDiagram hD
  have hUK : ∀ z ∈ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁), z ∈ X.arcSideDarts i ζ := by
    intro z hz
    rcases mem_union.1 hz with hz | hz
    · exact (hc.mem_of_mem_vertexOf _ hd₁ he1 z hz).1
    · exact (hc.mem_of_mem_vertexOf _ h₂ he2 z hz).1
  have hU : ∀ e ∈ X.arcDarts i, e ∉ X.vertexOf d₁ ∪ X.vertexOf (X.facePerm d₁) :=
    fun e he heU => disjoint_left.1 (disjoint_arcDarts_arcSide _) he (hUK e heU)
  have hK := arcSideDarts_swivelMove hX hDX hU hS hUK ζ
  have hL := arcCutList_swivelMove hX hDX hU ζ
  refine ⟨hDX, ?_, isSimpleArc_swivelMove hX hDX hU hS, arc_swivelMove hX hDX hU, hK, hL, ?_⟩
  · have hφ' : (X.arcCut i ζ).facePerm (.inl ⟨d₁, hd₁⟩) = .inl ⟨X.facePerm d₁, h₂⟩ := hφ
    rw [faceOf_eq_pair_of_facePerm_facePerm (R := (X.arcCut i ζ).toRotationSystem)
      hD.facePerm_facePerm, faceOf_eq_pair_of_facePerm_facePerm (R := X.toRotationSystem) hφφ, hφ']
    ext z
    rcases z with z | p
    · simp only [mem_insert, mem_singleton, mem_map, mem_subtype, Function.Embedding.inl_apply,
        Sum.inl.injEq]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨_, Or.inl rfl, rfl⟩
        · exact ⟨_, Or.inr rfl, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        rcases ha with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
    · constructor
      · intro h
        simp only [mem_insert, mem_singleton, reduceCtorEq, or_self] at h
      · intro h
        obtain ⟨a, -, ha⟩ := mem_map.1 h
        exact absurd ha (by simp)
  · have hD' : (X.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift).IsDigon
        ((X.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift).faceOf
          (.inl ⟨d₁, hd₁⟩)) := hD
    have key := hc.swivelMove_cut hX.toIsPreTripleDiagram hD'
    change HEq ((X.swivelMove d₁).cut ((X.swivelMove d₁).arcSideDarts i ζ)
      ((X.swivelMove d₁).arcCutList i ζ) ζ.cutShift)
      ((X.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift).swivelMove (.inl ⟨d₁, hd₁⟩))
    rw [hK, hL]
    exact heq_of_eq key

end ArcCutSwivelMain

/-! ### Chords of a triple diagram without triple points -/

section Chords

/-- An arc consisting of a single dart `n_a` from the source `ε(a)` to the endpoint `ε(c)` is
simple and ends at `ε(c)`. -/
private theorem isSimpleArc_and_arcEndIndex_of_chord {n : ℕ} {Y : TripleData H n}
    (hY : Y.IsTripleDiagram) (j : Fin n) {c : Fin (2 * n)}
    (h : Y.inv (Y.endDart (sourceIndex j)) = Y.endDart c) :
    Y.IsSimpleArc j ∧ Y.arcEndIndex j = c := by
  have hlen : Y.arcLength j = 0 + 1 := by
    rw [Y.arcLength_eq_succ_iff]
    refine ⟨?_, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    change Y.IsBoundaryVertex (Y.vertexOf (Y.inv (Y.endDart (sourceIndex j))))
    rw [h]
    exact (Y.mem_boundaryVertices.1 (hY.endpoint_mem c)).2
  refine ⟨fun k l hk _ _ => by omega, ?_⟩
  apply hY.endpoint_injective
  change Y.vertexOf (Y.endDart (Y.arcEndIndex j)) = Y.vertexOf (Y.endDart c)
  rw [endDart_arcEndIndex hY, hlen, Nat.add_sub_cancel, arcDart_zero, h]

/-- **Chords of a triple diagram without triple points do not cross**: if `a, b, c, d` are
positions of a triple diagram `Y` in this clockwise cyclic order (that is,
`0 < b - a < c - a < d - a` for the clockwise distances in `Fin (2n)`) and `n̄_a = n_c`, then
`n̄_b ≠ n_d`. Positions are `0`-indexed. -/
@[cluster_algebras "lem_chord_noncrossing"]
theorem inv_endDart_ne_endDart_of_cyclic {n : ℕ} {Y : TripleData H n} (hY : Y.IsTripleDiagram)
    {a b c d : Fin (2 * n)} (hab : 0 < ((b - a : Fin (2 * n)) : ℕ))
    (hbc : ((b - a : Fin (2 * n)) : ℕ) < ((c - a : Fin (2 * n)) : ℕ))
    (hcd : ((c - a : Fin (2 * n)) : ℕ) < ((d - a : Fin (2 * n)) : ℕ))
    (hac : Y.inv (Y.endDart a) = Y.endDart c) : Y.inv (Y.endDart b) ≠ Y.endDart d := by
  have hinv := hY.inv_involutive
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  simp only [fin_val_sub] at hab hbc hcd
  intro hbd
  by_cases hout : Y.isOut (Y.endDart a) = true
  · -- `n_a` is `out`: the chord `(n_a)` is the arc from `ε(a)`; `b` is on its left, `d` on its
    -- right
    obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := exists_sourceIndex_or_targetIndex a
    swap
    · rw [hY.isOut_target] at hout
      exact absurd hout (by decide)
    obtain ⟨hS, hq⟩ := isSimpleArc_and_arcEndIndex_of_chord hY j hac
    have hbl : Y.IsLeftPosition j b := by
      refine ⟨fun h => ?_, ?_⟩
      · subst h
        simp at hab
      · rw [hq, fin_val_sub, fin_val_sub]
        split_ifs at hab hbc hcd ⊢ <;> omega
    have hdr : Y.IsRightPosition j d := by
      refine ⟨fun h => ?_, ?_⟩
      · rw [hq] at h
        subst h
        simp at hcd
      · simp only [rightRun, mem_filter, mem_univ, true_and, rightRunLength, hq]
        rw [fin_val_sub, fin_val_sub]
        split_ifs at hab hbc hcd ⊢ <;> omega
    have h1 := hS.inv_mem_arcSide hY (hS.endDart_mem_leftSide hY hbl)
    have h2 := hS.endDart_mem_rightSide hY hdr
    rw [hbd] at h1
    exact disjoint_left.1 disjoint_rightSide_leftSide h2 h1
  · -- `n_c` is `out`: the chord `(n_c)` is the arc from `ε(c)`; `b` is on its right, `d` on its
    -- left
    have hcout : Y.isOut (Y.endDart c) = true := by
      rw [← hac, hY.toIsPreTripleDiagram.isOut_inv_apply (hY.endDart_notMem_bdry a)]
      simpa using hout
    have hca : Y.inv (Y.endDart c) = Y.endDart a := by rw [← hac, hinv]
    obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := exists_sourceIndex_or_targetIndex c
    swap
    · rw [hY.isOut_target] at hcout
      exact absurd hcout (by decide)
    obtain ⟨hS, hq⟩ := isSimpleArc_and_arcEndIndex_of_chord hY j hca
    have hbr : Y.IsRightPosition j b := by
      refine ⟨fun h => ?_, ?_⟩
      · rw [hq] at h
        subst h
        simp at hab
      · simp only [rightRun, mem_filter, mem_univ, true_and, rightRunLength, hq]
        rw [fin_val_sub, fin_val_sub]
        split_ifs at hab hbc hcd ⊢ <;> omega
    have hdl : Y.IsLeftPosition j d := by
      refine ⟨fun h => ?_, ?_⟩
      · subst h
        simp at hcd
      · rw [hq, fin_val_sub, fin_val_sub]
        split_ifs at hab hbc hcd ⊢ <;> omega
    have h1 := hS.inv_mem_arcSide hY (hS.endDart_mem_rightSide hY hbr)
    have h2 := hS.endDart_mem_leftSide hY hdl
    rw [hbd] at h1
    exact disjoint_left.1 disjoint_rightSide_leftSide h1 h2

end Chords

/-! ### Boundary-parallel arcs -/

/-- The arc `X.arc i` is boundary-parallel along `I`: `I` is an interval of `i` for the strand
permutation `X.strandPerm` with `2k` interior positions, the arc is simple and passes through
exactly `k` triple points, and for every interior position `r` of `I` the vertex
`X.vertexOf (X.inv (X.endDart r))` is a triple point through which the arc passes. -/
@[cluster_algebras "def_boundary_parallel"]
def IsBoundaryParallel (i : Fin b) (I : Finset (Fin (2 * b))) : Prop :=
  IsIntervalOf X.strandPerm i I ∧ X.IsSimpleArc i ∧
    2 * {v | X.PassesThrough (X.arc i).toFinset v}.ncard =
      (intervalInterior X.strandPerm i I).card ∧
    ∀ r ∈ intervalInterior X.strandPerm i I,
      X.PassesThrough (X.arc i).toFinset (X.vertexOf (X.inv (X.endDart r)))

section BoundaryParallel

variable {X} {i : Fin b}

/-- A simple arc `S = (e₁, …, e_m)` passes through exactly `m - 1` triple points, its points
`z_l = v(ē_l)`, `l ∈ [1, m - 1]`. -/
theorem IsSimpleArc.ncard_passesThrough (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) :
    {v | X.PassesThrough (X.arc i).toFinset v}.ncard = X.arcLength i - 1 := by
  have hset : {v | X.PassesThrough (X.arc i).toFinset v} =
      ↑((range (X.arcLength i - 1)).image fun k => X.vertexOf (X.inv (X.arcDart i k))) := by
    ext v
    simp only [Set.mem_setOf_eq, coe_image, coe_range, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨hint, d, hd, rfl⟩
      obtain ⟨t, ht, rfl⟩ := mem_arc_toFinset.1 hd
      rcases t with _ | k
      · exact ((X.mem_internalVertices.1 hint).2
          (X.mem_boundaryVertices.1 (hX.endpoint_mem (sourceIndex i))).2).elim
      · refine ⟨k, by omega, ?_⟩
        rw [arcDart_succ_eq hX ht, X.vertexOf_rot_pow_apply]
    · rintro ⟨k, hk, rfl⟩
      have := passesThrough_rot_pow_inv_arcDart hX (i := i) (k := k) (by omega) 0
      rwa [pow_zero, Equiv.Perm.one_apply] at this
  rw [hset, Set.ncard_coe_finset, card_image_of_injOn, card_range]
  intro k hk l hl h
  simp only [coe_range, Set.mem_Iio] at hk hl
  exact hS k l (by omega) (by omega) h

/-- A boundary-parallel arc `S = (e₁, …, e_m)` along an interval with `2k` interior positions has
`m - 1 = k`. -/
theorem IsBoundaryParallel.two_mul_arcLength_sub_one (hX : X.IsTripleDiagram)
    {I : Finset (Fin (2 * b))} (h : X.IsBoundaryParallel i I) :
    2 * (X.arcLength i - 1) = (intervalInterior X.strandPerm i I).card := by
  rw [← h.2.1.ncard_passesThrough hX]
  exact h.2.2.1

end BoundaryParallel

end TripleData

end ClusterAlgebras

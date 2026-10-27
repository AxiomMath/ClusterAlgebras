/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.Trips
public import ClusterAlgebras.Plabic.CornerTriangulation
public import ClusterAlgebras.Plabic.TripleDiagram

/-!
# Chains of the trip map and the strand diagram

For an arbitrary plabic graph `G`, [FWZ] draw a strand along each side of every edge, turning
sharply right at black vertices and sharply left at white ones, making a U-turn at white leaves,
going straight through bivalent white vertices, and replacing a white vertex of degree at least
four by a trivalent white tree. Here the tree is replaced by a corner triangulation of the vertex,
whose triangles become the triple points.

A dart `d ∉ B` is *initial* if `v(d)` is a crossing or `d` is a leg, and *terminal* if `v(d̄)` is a
crossing or a boundary vertex. Following the trip map from an initial dart to the first terminal
dart gives a bijection `end` from the initial onto the terminal darts. Given a *white datum* `D`,
a corner triangulation `D_w` of each crossing `w`, the *strand diagram* `X°(G, D)` has as darts the
symbols `x⁺_d`, `x⁻_t` (the two ends of a chain), `y^±_{s,τ}` (the strands across the diagonals `s`
of the `D_w`) and the boundary symbols `∂_r`, `∂'_r`. It is a pre-triple diagram whose triple
points are the triangles of the `D_w`. A *generalized triple diagram* of `G` is a pre-triple
diagram isomorphic to some `X°(G, D)`, provided every trip of `G` contains an initial dart; this
notion is invariant under isomorphisms of plabic graphs.

## Main definitions

* `ClusterAlgebras.PlabicData.IsInitial`, `ClusterAlgebras.PlabicData.IsTerminal`,
  `ClusterAlgebras.PlabicData.chainEnd`: initial and terminal darts and the end of the chain
  from a dart.
* `ClusterAlgebras.PlabicData.IsWhiteDatum`: white data.
* `ClusterAlgebras.RotationSystem.cornerNext`: the clockwise successor of a dart in a triangle of
  corners.
* `ClusterAlgebras.StrandSymbol`, `ClusterAlgebras.PlabicData.StrandDart`,
  `ClusterAlgebras.PlabicData.strandDiagram`: the strand diagram.
* `ClusterAlgebras.PlabicData.IsGeneralizedTripleDiagram`: generalized triple diagrams.

## Main results

* `ClusterAlgebras.PlabicData.IsPlabicGraph.chainEnd_bijOn`: `end` is a bijection from the
  initial onto the terminal darts.
* `ClusterAlgebras.PlabicData.isPreTripleDiagram_strandDiagram`,
  `ClusterAlgebras.PlabicData.bijOn_strandTriplePoint`: the strand diagram is a pre-triple
  diagram whose triple points are the triangles of the white datum.
* `ClusterAlgebras.PlabicData.Iso.isGeneralizedTripleDiagram_iff`: generalized triple diagrams
  of isomorphic plabic graphs.

## Implementation notes

* **Symbols.** The pairwise distinct symbols of [FWZ] are the constructors of an inductive type
  `StrandSymbol H b`, and the darts of `X°(G, D)` are the symbols cut out by `IsStrandSymbol`:
  `x⁺_d` for initial `d`, `x⁻_t` for terminal `t`, `y^±_{s,τ}` for `s ∈ D_w` and a triangle `τ ∋ s`
  of `D_w`, and every `∂_r`, `∂'_r`. The involution and the rotation are total functions on
  symbols (`strandInvSym`, `strandRotSym`), with arbitrary values on symbols that are not darts,
  restricted to the darts.
* **Clockwise listings.** For a triangle `τ` of `D_w` and `p ∈ τ`, `cornerNext τ p` is the first
  element of `τ \ {p}` in `σ⁻¹ p, σ⁻² p, …`, so
  `(p, cornerNext τ p, cornerNext τ (cornerNext τ p))` is the clockwise listing of `τ` starting at
  `p`. The pair `P_τ(p, cornerNext τ p)` consists of `pairOut τ p` and `pairIn τ p`, and the
  triangle cycle `(P_τ(x,y), P_τ(z,x), P_τ(y,z))` of [FWZ] sends `pairOut τ p` to `pairIn τ p`
  and `pairIn τ p` to `pairOut τ (cornerNext τ (cornerNext τ p))`.
* **White data.** A white datum is a function `D : Finset H → Finset (Sym2 H)` whose value at
  every crossing is a corner triangulation of it; its other values are irrelevant.
* **Labels.** Endpoint labels `r : Fin (2 * b)` and arc labels `i : Fin b` are `0`-indexed: they
  are the labels `r + 1` and `i + 1` of [FWZ]. So the endpoint cycles of [FWZ]
  `(∂'_{2i}, ∂_{2i-1}, x⁺_{g_i})` and `(∂'_{2i+1}, ∂_{2i}, x⁻_{ḡ_i})` read
  `(∂'_{2i+1}, ∂_{2i}, x⁺_{g_i})` and `(∂'_{2i+2}, ∂_{2i+1}, x⁻_{ḡ_i})` in Lean labels, and the
  endpoint `ε°(r)` is recorded by its dart `endSymbol r` outside `B°`.
* The strand diagram takes the facts that `G` is a plabic graph and `D` a white datum as
  arguments: its involution and rotation are permutations only then. Accordingly a generalized
  triple diagram of `G` is defined for a plabic graph `G`.
* That the strand diagram is a pre-triple diagram whose triple points are the triangles of the
  white datum is stated in two parts, the pre-triple diagram property
  (`isPreTripleDiagram_strandDiagram`) and the bijection between the triangles of the white
  datum and the triple points (`bijOn_strandTriplePoint`).

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-- Being a crossing is decidable. -/
instance : DecidablePred G.IsCrossing := fun _ => by unfold IsCrossing; infer_instance

/-! ### Chains of the trip map -/

/-- An **initial** dart: a dart `d ∉ B` such that `v(d)` is a crossing or `d` is a leg. -/
@[cluster_algebras "def_trip_chains"]
def IsInitial (d : H) : Prop := d ∉ G.bdry ∧ (G.IsCrossing (G.vertexOf d) ∨ G.IsLeg d)

/-- A **terminal** dart: a dart `t ∉ B` such that `v(t̄)` is a crossing or a boundary vertex. -/
@[cluster_algebras "def_trip_chains"]
def IsTerminal (t : H) : Prop :=
  t ∉ G.bdry ∧ (G.IsCrossing (G.vertexOf (G.inv t)) ∨ G.IsBoundaryVertex (G.vertexOf (G.inv t)))

/-- Being an initial dart is decidable. -/
instance : DecidablePred G.IsInitial := fun _ => by unfold IsInitial; infer_instance

/-- Being a terminal dart is decidable. -/
instance : DecidablePred G.IsTerminal := fun _ => by unfold IsTerminal; infer_instance

/-- The length of the chain from `d`: the least `m ≥ 0` such that `Tᵐ(d)` is terminal, and `0` if
there is none. -/
noncomputable def chainLength (d : H) : ℕ :=
  open Classical in
  if h : ∃ m, G.IsTerminal (G.tripMap^[m] d) then Nat.find h else 0

/-- The **end** of the chain from a dart `d`: `end(d) = Tᵐ(d)` for the least `m ≥ 0` such that
`Tᵐ(d)` is terminal, and `end(d) = d` if there is no such `m`. -/
@[cluster_algebras "def_trip_chains"]
noncomputable def chainEnd (d : H) : H := G.tripMap^[G.chainLength d] d

variable {G}

/-- `end(d) = Tᵐ(d)` for `m` the length of the chain from `d`. -/
theorem chainEnd_def (d : H) : G.chainEnd d = G.tripMap^[G.chainLength d] d := rfl

/-- If some `Tᵐ(d)` is terminal, then `T^ℓ(d)` is terminal for `ℓ` the length of the chain
from `d`. -/
theorem chainLength_spec {d : H} (h : ∃ m, G.IsTerminal (G.tripMap^[m] d)) :
    G.IsTerminal (G.tripMap^[G.chainLength d] d) := by
  rw [chainLength, dif_pos h]
  exact Nat.find_spec h

/-- `Tʲ(d)` is not terminal for `j` less than the length of the chain from `d`. -/
theorem not_isTerminal_of_lt_chainLength {d : H} {j : ℕ} (hj : j < G.chainLength d) :
    ¬G.IsTerminal (G.tripMap^[j] d) := by
  intro ht
  have h : ∃ m, G.IsTerminal (G.tripMap^[m] d) := ⟨j, ht⟩
  rw [chainLength, dif_pos h] at hj
  exact Nat.find_min h hj ht

/-- If `Tʲ(d)` is terminal, then the length of the chain from `d` is at most `j`. -/
theorem chainLength_le {d : H} {j : ℕ} (hj : G.IsTerminal (G.tripMap^[j] d)) :
    G.chainLength d ≤ j := by
  have h : ∃ m, G.IsTerminal (G.tripMap^[m] d) := ⟨j, hj⟩
  rw [chainLength, dif_pos h]
  exact Nat.find_min' h hj

/-- An initial dart is not in `B`. -/
theorem IsInitial.notMem_bdry {d : H} (h : G.IsInitial d) : d ∉ G.bdry := h.1

/-- A terminal dart is not in `B`. -/
theorem IsTerminal.notMem_bdry {t : H} (h : G.IsTerminal t) : t ∉ G.bdry := h.1

/-- A crossing is an internal vertex. -/
theorem IsCrossing.not_isBoundaryVertex {w : Finset H} (h : G.IsCrossing w) :
    ¬G.IsBoundaryVertex w :=
  (G.mem_internalVertices.1 h.1).2

section IsPlabicGraph

variable (hG : G.IsPlabicGraph)

include hG

/-- In a plabic graph, a dart outside `B` at a boundary vertex is a leg. -/
theorem IsPlabicGraph.isLeg_of_isBoundaryVertex {d : H} (hd : d ∉ G.bdry)
    (hv : G.IsBoundaryVertex (G.vertexOf d)) : G.IsLeg d := by
  obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hv)
  have hmem : d ∈ (G.bvertex i).filter (· ∉ G.bdry) := by
    rw [mem_filter, hi]
    exact ⟨G.self_mem_vertexOf d, hd⟩
  rw [hG.filter_bvertex_notMem_bdry, mem_singleton] at hmem
  exact ⟨i, hmem.symm⟩

/-- In a plabic graph, a leg lies at a boundary vertex. -/
theorem IsPlabicGraph.isBoundaryVertex_of_isLeg {d : H} (hd : G.IsLeg d) :
    G.IsBoundaryVertex (G.vertexOf d) := by
  obtain ⟨i, rfl⟩ := hd
  exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)

/-- (a) If `t` is terminal, then `T(t)` is initial. -/
theorem IsTerminal.isInitial_tripMap {t : H} (ht : G.IsTerminal t) :
    G.IsInitial (G.tripMap t) := by
  have hv : G.vertexOf (G.tripMap t) = G.vertexOf (G.inv t) := vertexOf_turn _
  rcases ht.2 with hc | hb
  · refine ⟨fun hB => hc.not_isBoundaryVertex ⟨_, ?_, hB⟩, Or.inl (hv ▸ hc)⟩
    exact turn_mem_vertexOf _
  · have hT : G.tripMap t = G.inv t := turn_of_isBoundaryVertex hb
    have hnB : G.inv t ∉ G.bdry := fun h => ht.1 (hG.inv_mem_bdry_iff.1 h)
    rw [hT]
    exact ⟨hnB, Or.inr (hG.isLeg_of_isBoundaryVertex hnB hb)⟩

/-- (b) If `T(z)` is initial, then `z` is terminal. -/
theorem isTerminal_of_isInitial_tripMap {z : H} (hz : G.IsInitial (G.tripMap z)) :
    G.IsTerminal z := by
  have hv : G.vertexOf (G.tripMap z) = G.vertexOf (G.inv z) := vertexOf_turn _
  refine ⟨fun hB => hz.1 ((tripMap_mem_bdry_iff hG z).2 hB), ?_⟩
  rcases hz.2 with hc | hl
  · exact Or.inl (hv ▸ hc)
  · exact Or.inr (hv ▸ hG.isBoundaryVertex_of_isLeg hl)

/-- In a plabic graph, `Tⁿ(d)` is the `n`-th power of the trip permutation applied to `d`. -/
theorem tripMap_iterate_eq (n : ℕ) (d : H) : G.tripMap^[n] d = (hG.tripEquiv ^ n) d :=
  (hG.tripEquiv_pow_apply n d).symm

/-- `T^{p-1}(d) = T⁻¹(d)` for `p` the order of `T`. -/
theorem tripMap_iterate_orderOf_pred (d : H) :
    G.tripMap (G.tripMap^[orderOf hG.tripEquiv - 1] d) = d := by
  have hpos := (isOfFinOrder_of_finite hG.tripEquiv).orderOf_pos
  rw [← Function.iterate_succ_apply' G.tripMap, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos,
    tripMap_iterate_eq hG, pow_orderOf_eq_one, Equiv.Perm.one_apply]

/-- (c) For an initial dart `d` some `Tᵐ(d)` is terminal. -/
theorem IsInitial.exists_isTerminal {d : H} (hd : G.IsInitial d) :
    ∃ m, G.IsTerminal (G.tripMap^[m] d) :=
  ⟨_, isTerminal_of_isInitial_tripMap hG (by rwa [tripMap_iterate_orderOf_pred hG])⟩

/-- (c) The end of the chain from an initial dart is terminal. -/
theorem IsInitial.isTerminal_chainEnd {d : H} (hd : G.IsInitial d) :
    G.IsTerminal (G.chainEnd d) :=
  chainLength_spec (hd.exists_isTerminal hG)

/-- (c) No `Tʲ(d)` with `0 < j ≤ m` is initial, for `d` initial and `end(d) = Tᵐ(d)`. -/
theorem not_isInitial_of_le_chainLength {d : H} {j : ℕ} (hj0 : 0 < j)
    (hj : j ≤ G.chainLength d) : ¬G.IsInitial (G.tripMap^[j] d) := by
  intro hi
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Function.iterate_succ_apply'] at hi
  exact not_isTerminal_of_lt_chainLength (by omega) (isTerminal_of_isInitial_tripMap hG hi)

private theorem eq_of_chainEnd_eq_of_le {d d' : H} (hd : G.IsInitial d)
    (h : G.chainEnd d = G.chainEnd d') (hle : G.chainLength d ≤ G.chainLength d') : d = d' := by
  obtain ⟨k, hk⟩ : ∃ k, G.chainLength d' = G.chainLength d + k := ⟨_, (Nat.add_sub_of_le hle).symm⟩
  rw [chainEnd_def, chainEnd_def, hk, Function.iterate_add_apply] at h
  have h' : d = G.tripMap^[k] d' :=
    ((tripMap_bijective hG).injective.iterate _) h
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact h'
  · exact absurd (h' ▸ hd) (not_isInitial_of_le_chainLength hG hk0 (by omega))

/-- (d) `end` is injective on initial darts. -/
theorem chainEnd_injOn : Set.InjOn G.chainEnd {d | G.IsInitial d} := by
  intro d hd d' hd' h
  rcases le_total (G.chainLength d) (G.chainLength d') with hle | hle
  · exact eq_of_chainEnd_eq_of_le hG hd h hle
  · exact (eq_of_chainEnd_eq_of_le hG hd' h.symm hle).symm

/-- (e) Every terminal dart is the end of the chain from an initial dart. -/
theorem IsTerminal.exists_chainEnd_eq {t : H} (ht : G.IsTerminal t) :
    ∃ d, G.IsInitial d ∧ G.chainEnd d = t := by
  set e := hG.tripEquiv
  have hpow : ∀ j k : ℕ, j ≤ k →
      G.tripMap^[j] ((e ^ (-(k : ℤ))) t) = (e ^ (-((k - j : ℕ) : ℤ))) t := by
    intro j k hj
    rw [tripMap_iterate_eq hG, ← zpow_natCast, ← Equiv.Perm.mul_apply, ← zpow_add]
    congr 2
    push_cast [hj]
    ring
  have hex : ∃ k : ℕ, G.IsInitial ((e ^ (-(k : ℤ))) t) := by
    refine ⟨orderOf e - 1, ?_⟩
    have hpos := (isOfFinOrder_of_finite e).orderOf_pos
    have h1 : e ^ (-((orderOf e - 1 : ℕ) : ℤ)) = e := by
      rw [show (-((orderOf e - 1 : ℕ) : ℤ)) = 1 - (orderOf e : ℤ) by
        push_cast [Nat.cast_sub (show 1 ≤ orderOf e from hpos)]; ring,
        zpow_sub, zpow_one, zpow_natCast, pow_orderOf_eq_one, inv_one, mul_one]
    rw [h1]
    exact ht.isInitial_tripMap hG
  classical
  set k := Nat.find hex with hk
  have hdk : G.IsInitial ((e ^ (-(k : ℤ))) t) := Nat.find_spec hex
  have hTk : G.tripMap^[k] ((e ^ (-(k : ℤ))) t) = t := by
    rw [hpow k k le_rfl, Nat.sub_self, Nat.cast_zero, neg_zero, zpow_zero, Equiv.Perm.one_apply]
  refine ⟨_, hdk, ?_⟩
  have hlen : G.chainLength ((e ^ (-(k : ℤ))) t) = k := by
    refine le_antisymm (chainLength_le (by rwa [hTk])) ?_
    by_contra hlt
    push Not at hlt
    have hterm := chainLength_spec ⟨k, by rwa [hTk]⟩
    have hinit := hterm.isInitial_tripMap hG
    rw [← Function.iterate_succ_apply' G.tripMap, hpow _ _ hlt] at hinit
    exact Nat.find_min hex (by omega) hinit
  rw [chainEnd_def, hlen, hTk]

/-- **Chains pair initial and terminal darts**: in a plabic graph, `end` is a bijection from the
set of initial darts onto the set of terminal darts. -/
@[cluster_algebras "lem_trip_chain_bijection"]
theorem IsPlabicGraph.chainEnd_bijOn :
    Set.BijOn G.chainEnd {d | G.IsInitial d} {t | G.IsTerminal t} :=
  ⟨fun _ hd => IsInitial.isTerminal_chainEnd hG hd, chainEnd_injOn hG,
    fun _ ht => let ⟨d, hd, h⟩ := IsTerminal.exists_chainEnd_eq hG ht; ⟨d, hd, h⟩⟩

end IsPlabicGraph

end PlabicData

/-! ### The clockwise successor in a triangle of corners -/

section CyclicOrder

variable {m : ℕ} [NeZero m]

/-- Three distinct elements of `ZMod m` are listed clockwise in one of the two orders starting at
the first. -/
theorem sbtw_or_sbtw_of_ne {i j k : ZMod m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    sbtw i j k ∨ sbtw i k j := by
  rw [TypeA.sbtw_iff_sbtw_basePos i, TypeA.sbtw_iff_sbtw_basePos i i k j, Int.sbtw_iff,
    Int.sbtw_iff, TypeA.basePos_self]
  have hinj := TypeA.basePos_injective i
  have h1 := TypeA.basePos_nonneg i j
  have h2 := TypeA.basePos_nonneg i k
  have h3 : TypeA.basePos i j ≠ 0 := fun h =>
    hij (hinj (h.trans (TypeA.basePos_self i).symm)).symm
  have h4 : TypeA.basePos i k ≠ 0 := fun h =>
    hik (hinj (h.trans (TypeA.basePos_self i).symm)).symm
  have h5 : TypeA.basePos i j ≠ TypeA.basePos i k := fun h => hjk (hinj h)
  omega

/-- If `j` lies strictly between `i` and `k`, then `j` is fewer steps from `i` than `k`. -/
theorem val_sub_lt_val_sub_of_sbtw {i j k : ZMod m} (h : sbtw i j k) :
    (j - i).val < (k - i).val := by
  rw [TypeA.sbtw_iff_sbtw_basePos i, Int.sbtw_iff, TypeA.basePos_self] at h
  have h1 := TypeA.basePos_nonneg i j
  have h2 := TypeA.basePos_nonneg i k
  have : TypeA.basePos i j < TypeA.basePos i k := by omega
  unfold TypeA.basePos at this
  exact_mod_cast this

end CyclicOrder

namespace RotationSystem

variable {H : Type*} [DecidableEq H] (R : RotationSystem H)

/-- The **clockwise successor** of a dart `p` in a set `τ` of darts: the first element of
`τ \ {p}` in the sequence `σ⁻¹ p, σ⁻² p, …`, and `p` itself if there is none. For a triangle `τ`
of a corner triangulation and `p ∈ τ`, `(p, cornerNext τ p, cornerNext τ (cornerNext τ p))` is the
clockwise listing of `τ` starting at `p`. -/
noncomputable def cornerNext (τ : Finset H) (p : H) : H :=
  open Classical in
  if h : ∃ k : ℕ, 0 < k ∧ (R.rot.symm ^ k) p ∈ τ ∧ (R.rot.symm ^ k) p ≠ p then
    (R.rot.symm ^ Nat.find h) p
  else p

variable {R}

namespace IsCornerLabelling

variable {m : ℕ} [NeZero m] {w : Finset H} {l : ZMod m → H}

/-- The clockwise successor of `λ i` in `λ(τ')` is `λ j` for the element `j ≠ i` of `τ'` with the
least number of steps from `i`. -/
theorem cornerNext_image_eq (hl : R.IsCornerLabelling w l) {τ' : Finset (ZMod m)} {i j : ZMod m}
    (hj : j ∈ τ') (hji : j ≠ i) (hmin : ∀ k ∈ τ', k ≠ i → (j - i).val ≤ (k - i).val) :
    R.cornerNext (τ'.image l) (l i) = l j := by
  classical
  have key : ∀ n : ℕ, (R.rot.symm ^ n) (l i) = l (i + n) := fun n => (hl.apply_add_nat i n).symm
  have hjv : (R.rot.symm ^ (j - i).val) (l i) = l j := by
    rw [key, ZMod.natCast_zmod_val, add_sub_cancel]
  have hpos : 0 < (j - i).val := by
    rw [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]
    exact sub_ne_zero.2 hji
  have hex : ∃ k : ℕ, 0 < k ∧ (R.rot.symm ^ k) (l i) ∈ τ'.image l ∧
      (R.rot.symm ^ k) (l i) ≠ l i :=
    ⟨_, hpos, hjv ▸ mem_image_of_mem l hj, hjv ▸ hl.injective.ne hji⟩
  rw [cornerNext, dif_pos hex]
  have : Nat.find hex = (j - i).val := by
    rw [Nat.find_eq_iff]
    refine ⟨⟨hpos, hjv ▸ mem_image_of_mem l hj, hjv ▸ hl.injective.ne hji⟩, ?_⟩
    rintro n hn ⟨hn0, hmem, hne⟩
    rw [key] at hmem hne
    obtain ⟨k, hk, hkl⟩ := mem_image.1 hmem
    have hk' : k = i + n := hl.injective hkl
    have hki : k ≠ i := fun h => hne (by rw [← hk', h])
    have := hmin k hk hki
    rw [hk', add_sub_cancel_left, ZMod.val_natCast,
      Nat.mod_eq_of_lt (lt_trans hn (ZMod.val_lt _))] at this
    omega
  rw [this, hjv]

/-- If `(i, j, k)` is clockwise, the clockwise successor of `λ i` in `{λ i, λ j, λ k}` is
`λ j`. -/
theorem cornerNext_of_sbtw (hl : R.IsCornerLabelling w l) {i j k : ZMod m} (h : sbtw i j k) :
    R.cornerNext {l i, l j, l k} (l i) = l j := by
  have himg : ({l i, l j, l k} : Finset H) = ({i, j, k} : Finset (ZMod m)).image l := by
    simp [Finset.image_insert]
  rw [himg]
  refine hl.cornerNext_image_eq (by simp) (fun hji => sbtw_irrefl_left (hji ▸ h)) ?_
  intro x hx hxi
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact absurd rfl hxi
  · exact le_rfl
  · exact (val_sub_lt_val_sub_of_sbtw h).le

/-- The facts on one clockwise listing `(λ i, λ j, λ k)` used for the clockwise successor. -/
private theorem spec_of_sbtw (hl : R.IsCornerLabelling w l) {i j k : ZMod m} (h : sbtw i j k) :
    R.cornerNext {l i, l j, l k} (l i) = l j ∧ R.rot.symm (l j) ≠ l i ∧
      R.rot.symm (l i) ≠ l k := by
  refine ⟨hl.cornerNext_of_sbtw h, fun he => ?_, fun he => ?_⟩
  · rw [← hl.2] at he
    obtain rfl := hl.injective he
    exact not_sbtw_self_add_one j k (sbtw_cyclic_left h)
  · rw [← hl.2] at he
    obtain rfl := hl.injective he
    exact not_sbtw_self_add_one i j h

omit [DecidableEq H] [NeZero m] in
/-- On a corner labelling of at least two corners, `σ⁻¹` fixes no labelled corner. -/
theorem rot_symm_ne_self (hl : R.IsCornerLabelling w l) (hm : 1 < m) (a : ZMod m) :
    R.rot.symm (l a) ≠ l a := by
  intro he
  rw [← hl.2] at he
  have h2 : ((1 : ℕ) : ZMod m) = 0 := by
    rw [Nat.cast_one]
    linear_combination hl.injective he
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact absurd (Nat.le_of_dvd one_pos h2) (by omega)

/-- **The clockwise successor in a triangle.** Let `w` have a corner labelling and let `τ ⊆ w`
have three elements. For `x ∈ τ` the clockwise successor `q` of `x` and the successor `r` of `q`
list `τ = {x, q, r}`, the successor of `r` is `x`, `σ⁻¹ x ≠ x`, `σ⁻¹ q ≠ x`, `σ⁻¹ x ≠ r`, and
`(x, q, r)` is a clockwise listing. -/
theorem cornerNext_spec (hl : R.IsCornerLabelling w l) {τ : Finset H} (hτw : τ ⊆ w)
    (hτ : τ.card = 3) {x : H} (hx : x ∈ τ) :
    ∃ q r, τ = {x, q, r} ∧ x ≠ q ∧ x ≠ r ∧ q ≠ r ∧ R.cornerNext τ x = q ∧
      R.cornerNext τ q = r ∧ R.cornerNext τ r = x ∧ R.rot.symm x ≠ x ∧
      R.rot.symm q ≠ x ∧ R.rot.symm x ≠ r ∧ R.IsCornerClockwise x q r := by
  have h3m : 3 ≤ m := by
    rw [← hl.card_eq]
    exact hτ ▸ card_le_card hτw
  obtain ⟨y, z, hyz, hyzτ⟩ := card_eq_two.1 (by rw [card_erase_of_mem hx, hτ] :
    (τ.erase x).card = 2)
  have hτeq : τ = {x, y, z} := by rw [← hyzτ, insert_erase hx]
  have hy : y ∈ τ.erase x := by simp [hyzτ]
  have hz : z ∈ τ.erase x := by simp [hyzτ]
  have hxy : x ≠ y := fun h => (mem_erase.1 hy).1 h.symm
  have hxz : x ≠ z := fun h => (mem_erase.1 hz).1 h.symm
  obtain ⟨i, rfl⟩ := hl.exists_eq (hτw hx)
  obtain ⟨j, rfl⟩ := hl.exists_eq (hτw (mem_of_mem_erase hy))
  obtain ⟨k, rfl⟩ := hl.exists_eq (hτw (mem_of_mem_erase hz))
  have hfix := hl.rot_symm_ne_self (by omega)
  have hij : i ≠ j := fun h => hxy (h ▸ rfl)
  have hik : i ≠ k := fun h => hxz (h ▸ rfl)
  have hjk : j ≠ k := fun h => hyz (h ▸ rfl)
  rcases sbtw_or_sbtw_of_ne hij hik hjk with h | h
  · have e1 : ({l j, l k, l i} : Finset H) = {l i, l j, l k} := by
      ext; simp only [mem_insert, mem_singleton]; tauto
    have e2 : ({l k, l i, l j} : Finset H) = {l i, l j, l k} := by
      ext; simp only [mem_insert, mem_singleton]; tauto
    obtain ⟨a1, a2, a3⟩ := spec_of_sbtw hl h
    obtain ⟨b1, b2, b3⟩ := spec_of_sbtw hl (sbtw_cyclic_left h)
    obtain ⟨c1, c2, c3⟩ := spec_of_sbtw hl (sbtw_cyclic_left (sbtw_cyclic_left h))
    rw [e1] at b1
    rw [e2] at c1
    subst hτeq
    exact ⟨l j, l k, rfl, hxy, hxz, hyz, a1, b1, c1, hfix i, a2, a3, hl.isCornerClockwise h⟩
  · have e1 : ({l k, l j, l i} : Finset H) = {l i, l j, l k} := by
      ext; simp only [mem_insert, mem_singleton]; tauto
    have e2 : ({l j, l i, l k} : Finset H) = {l i, l j, l k} := by
      ext; simp only [mem_insert, mem_singleton]; tauto
    have e0 : ({l i, l k, l j} : Finset H) = {l i, l j, l k} := by
      ext; simp only [mem_insert, mem_singleton]; tauto
    obtain ⟨a1, a2, a3⟩ := spec_of_sbtw hl h
    obtain ⟨b1, b2, b3⟩ := spec_of_sbtw hl (sbtw_cyclic_left h)
    obtain ⟨c1, c2, c3⟩ := spec_of_sbtw hl (sbtw_cyclic_left (sbtw_cyclic_left h))
    rw [e0] at a1
    rw [e1] at b1
    rw [e2] at c1
    subst hτeq
    refine ⟨l k, l j, ?_, hxz, hxy, hyz.symm, a1, b1, c1, hfix i, a2, a3,
      hl.isCornerClockwise h⟩
    ext; simp only [mem_insert, mem_singleton]; tauto

end IsCornerLabelling

end RotationSystem

/-! ### White data -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)
  (D : Finset H → Finset (Sym2 H))

/-- A **white datum** of a plabic graph: a family `D = (D_w)` of corner triangulations, one of
each crossing `w`. The family is indexed by all sets of darts; its values away from the crossings
are irrelevant. -/
@[cluster_algebras "def_strand_diagram"]
def IsWhiteDatum : Prop := ∀ w, G.IsCrossing w → G.IsCornerTriangulation w (D w)

/-- A **triangle of a white datum**: a triangle of `D_w` for some crossing `w`. -/
def IsDatumTriangle (τ : Finset H) : Prop :=
  ∃ w, G.IsCrossing w ∧ G.IsCornerTriangle w (D w) τ

/-- A pair `(s, τ)` indexing the symbols `y^±_{s,τ}` of the strand diagram: `s ∈ D_w` and `τ` a
triangle of `D_w` with `s ⊆ τ`, for some crossing `w`. -/
def IsDatumSegment (s : Sym2 H) (τ : Finset H) : Prop :=
  ∃ w, G.IsCrossing w ∧ s ∈ D w ∧ G.IsCornerTriangle w (D w) τ ∧ s ∈ τ.sym2

/-- Being a triangle of the white datum is decidable. -/
instance : DecidablePred (G.IsDatumTriangle D) := fun _ => by
  unfold IsDatumTriangle; infer_instance

/-- Being a pair `(s, τ)` indexing the symbols `y^±_{s,τ}` is decidable. -/
instance (s : Sym2 H) : DecidablePred (G.IsDatumSegment D s) := fun _ => by
  unfold IsDatumSegment; infer_instance

/-- The triangle of the white datum containing the side `{p, σ⁻¹ p}` of `p` (unique when `v(p)` is
a crossing), and `∅` if there is none. -/
noncomputable def sideTriangle (p : H) : Finset H :=
  open Classical in
  if h : ∃ τ, G.IsDatumTriangle D τ ∧ G.cornerSide p ∈ τ.sym2 then h.choose else ∅

/-- The triangle of the white datum other than `τ` containing `s` (unique when `s ∈ D_w`), and `τ`
if there is none. -/
noncomputable def otherTriangle (s : Sym2 H) (τ : Finset H) : Finset H :=
  open Classical in
  if h : ∃ τ', G.IsDatumTriangle D τ' ∧ s ∈ τ'.sym2 ∧ τ' ≠ τ then h.choose else τ

variable {G D}

/-- A crossing is the vertex of each of its darts. -/
theorem IsCrossing.eq_vertexOf {w : Finset H} (hw : G.IsCrossing w) {p : H} (hp : p ∈ w) :
    w = G.vertexOf p := by
  obtain ⟨d, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hw.1).1
  exact (G.vertexOf_eq_of_mem hp).symm

/-- If `(s, τ)` indexes the symbols `y^±_{s,τ}`, then `τ` is a triangle of the white datum. -/
theorem IsDatumTriangle.of_isDatumSegment {s : Sym2 H} {τ : Finset H}
    (h : G.IsDatumSegment D s τ) : G.IsDatumTriangle D τ :=
  let ⟨w, hw, _, hτ, _⟩ := h
  ⟨w, hw, hτ⟩

/-- A triangle of the white datum through `p` is a triangle of `D_{v(p)}`. -/
theorem IsDatumTriangle.vertexOf {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H}
    (hp : p ∈ τ) : G.IsCrossing (G.vertexOf p) ∧
      G.IsCornerTriangle (G.vertexOf p) (D (G.vertexOf p)) τ := by
  obtain ⟨w, hw, ht⟩ := hτ
  rw [← hw.eq_vertexOf (ht.1 hp)]
  exact ⟨hw, ht⟩

/-- A triangle of the white datum has three elements. -/
theorem IsDatumTriangle.card_eq {τ : Finset H} (hτ : G.IsDatumTriangle D τ) : τ.card = 3 :=
  let ⟨_, _, ht⟩ := hτ
  ht.2.1

omit [Fintype H] in
/-- The sides of a crossing are not elements of a corner triangulation of it. -/
theorem cornerSide_notMem_of_isCornerTriangulation {w : Finset H} {E : Finset (Sym2 H)}
    (hE : G.IsCornerTriangulation w E) {a : H} (ha : a ∈ w) : G.cornerSide a ∉ E := by
  obtain ⟨-, m, _, l, hl, hT⟩ := hE
  obtain ⟨k, rfl⟩ := hl.exists_eq ha
  rw [hl.cornerSide_apply]
  intro h
  exact (hT.isDiagonal _ (RotationSystem.mem_cornerPullback.2 h)).2 ⟨k, rfl⟩

section WhiteDatum

variable (hD : G.IsWhiteDatum D)

include hD

/-- **The clockwise successor in a triangle of a white datum.** -/
theorem IsWhiteDatum.cornerNext_spec {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {x : H}
    (hx : x ∈ τ) :
    ∃ q r, τ = {x, q, r} ∧ x ≠ q ∧ x ≠ r ∧ q ≠ r ∧ G.cornerNext τ x = q ∧
      G.cornerNext τ q = r ∧ G.cornerNext τ r = x ∧ G.rot.symm x ≠ x ∧
      G.rot.symm q ≠ x ∧ G.rot.symm x ≠ r ∧ G.IsCornerClockwise x q r := by
  obtain ⟨w, hw, ht⟩ := hτ
  obtain ⟨-, m, _, l, hl, -⟩ := hD w hw
  exact hl.cornerNext_spec ht.1 ht.2.1 hx

variable {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {x : H} (hx : x ∈ τ)

include hτ hx

/-- The clockwise successor of `x` in `τ` lies in `τ`. -/
theorem IsWhiteDatum.cornerNext_mem : G.cornerNext τ x ∈ τ := by
  obtain ⟨q, r, he, -, -, -, h1, -⟩ := hD.cornerNext_spec hτ hx
  rw [h1, he]; simp

/-- The clockwise successor of `x` in `τ` is not `x`. -/
theorem IsWhiteDatum.cornerNext_ne : G.cornerNext τ x ≠ x := by
  obtain ⟨q, r, -, hxq, -, -, h1, -⟩ := hD.cornerNext_spec hτ hx
  rw [h1]; exact hxq.symm

/-- The second clockwise successor of `x` in `τ` is not `x`. -/
theorem IsWhiteDatum.cornerNext_cornerNext_ne : G.cornerNext τ (G.cornerNext τ x) ≠ x := by
  obtain ⟨q, r, -, -, hxr, -, h1, h2, -⟩ := hD.cornerNext_spec hτ hx
  rw [h1, h2]; exact hxr.symm

/-- The second clockwise successor of `x` in `τ` is not the first. -/
theorem IsWhiteDatum.cornerNext_cornerNext_ne_cornerNext :
    G.cornerNext τ (G.cornerNext τ x) ≠ G.cornerNext τ x := by
  obtain ⟨q, r, -, -, -, hqr, h1, h2, -⟩ := hD.cornerNext_spec hτ hx
  rw [h1, h2]; exact hqr.symm

/-- The third clockwise successor of `x` in `τ` is `x`. -/
theorem IsWhiteDatum.cornerNext_three :
    G.cornerNext τ (G.cornerNext τ (G.cornerNext τ x)) = x := by
  obtain ⟨q, r, -, -, -, -, h1, h2, h3, -⟩ := hD.cornerNext_spec hτ hx
  rw [h1, h2, h3]

/-- `τ` consists of `x` and its first and second clockwise successors in `τ`. -/
theorem IsWhiteDatum.eq_insert_cornerNext :
    τ = {x, G.cornerNext τ x, G.cornerNext τ (G.cornerNext τ x)} := by
  obtain ⟨q, r, he, -, -, -, h1, h2, -⟩ := hD.cornerNext_spec hτ hx
  rwa [h1, h2]

/-- `(x, cornerNext τ x, cornerNext τ (cornerNext τ x))` is a clockwise listing of `τ`. -/
theorem IsWhiteDatum.isCornerClockwise_cornerNext :
    G.IsCornerClockwise x (G.cornerNext τ x) (G.cornerNext τ (G.cornerNext τ x)) := by
  obtain ⟨q, r, -, -, -, -, h1, h2, -, -, -, -, h⟩ := hD.cornerNext_spec hτ hx
  rwa [h1, h2]

/-- `σ⁻¹` of the clockwise successor of `x` in `τ` is not `x`. -/
theorem IsWhiteDatum.rot_symm_cornerNext_ne : G.rot.symm (G.cornerNext τ x) ≠ x := by
  obtain ⟨q, r, -, -, -, -, h1, -, -, -, h, -⟩ := hD.cornerNext_spec hτ hx
  rwa [h1]

/-- If `σ⁻¹ x ∈ τ`, the clockwise successor of `x` in `τ` is `σ⁻¹ x`. -/
theorem IsWhiteDatum.cornerNext_eq_rot_symm (h : G.rot.symm x ∈ τ) :
    G.cornerNext τ x = G.rot.symm x := by
  obtain ⟨q, r, he, -, -, -, h1, -, -, hx', -, hxr, -⟩ := hD.cornerNext_spec hτ hx
  rw [he] at h
  simp only [mem_insert, mem_singleton] at h
  rcases h with h | h | h
  · exact absurd h hx'
  · rw [h1, h]
  · exact absurd h hxr

/-- The element of `τ` outside `{x, cornerNext τ x}` is `cornerNext τ (cornerNext τ x)`. -/
theorem IsWhiteDatum.eq_cornerNext_cornerNext {y : H} (hy : y ∈ τ)
    (hys : y ∉ s(x, G.cornerNext τ x)) : y = G.cornerNext τ (G.cornerNext τ x) := by
  rw [hD.eq_insert_cornerNext hτ hx] at hy
  simp only [mem_insert, mem_singleton] at hy
  simp only [Sym2.mem_iff, not_or] at hys
  tauto

/-- The pair `{x, cornerNext τ x}` is an element of `D_{v(x)}` unless it is the side of `x`. -/
theorem IsWhiteDatum.mk_cornerNext_mem (h : G.cornerNext τ x ≠ G.rot.symm x) :
    s(x, G.cornerNext τ x) ∈ D (G.vertexOf x) := by
  obtain ⟨hw, ht⟩ := hτ.vertexOf hx
  have hseg := ht.2.2 x hx _ (hD.cornerNext_mem hτ hx) (hD.cornerNext_ne hτ hx).symm
  rcases RotationSystem.mem_cornerSegments.1 hseg with h' | ⟨a, -, ha⟩
  · exact h'
  · exfalso
    rw [RotationSystem.cornerSide, Sym2.eq_iff] at ha
    rcases ha with ⟨rfl, h2⟩ | ⟨h1, h2⟩
    · exact h h2.symm
    · exact hD.rot_symm_cornerNext_ne hτ hx (h1 ▸ h2)

/-- If `cornerNext τ x ≠ σ⁻¹ x`, the pair `{x, cornerNext τ x}` is not a corner side at the
vertex of `x`. -/
theorem IsWhiteDatum.mk_cornerNext_ne_cornerSide (h : G.cornerNext τ x ≠ G.rot.symm x) (a : H)
    (ha : a ∈ G.vertexOf x) : s(x, G.cornerNext τ x) ≠ G.cornerSide a := by
  intro he
  obtain ⟨hw, -⟩ := hτ.vertexOf hx
  exact cornerSide_notMem_of_isCornerTriangulation (hD _ hw) ha
    (he ▸ hD.mk_cornerNext_mem hτ hx h)

omit hτ hx in
/-- The triangle `sideTriangle D p` is a triangle of the white datum containing the side of `p`,
for `p` at a crossing. -/
theorem IsWhiteDatum.sideTriangle_spec {p : H} (hp : G.IsCrossing (G.vertexOf p)) :
    G.IsDatumTriangle D (G.sideTriangle D p) ∧ G.cornerSide p ∈ (G.sideTriangle D p).sym2 := by
  have hex : ∃ τ, G.IsDatumTriangle D τ ∧ G.cornerSide p ∈ τ.sym2 := by
    have h1 := (hD _ hp).card_filter_cornerSide hp.three_le_card (G.self_mem_vertexOf p)
    obtain ⟨τ, hτ⟩ := card_eq_one.1 h1
    have hmem : τ ∈ (G.cornerTriangles (G.vertexOf p) (D (G.vertexOf p))).filter
        fun t => G.cornerSide p ∈ t.sym2 := by rw [hτ]; exact mem_singleton_self τ
    rw [mem_filter, RotationSystem.mem_cornerTriangles] at hmem
    exact ⟨τ, ⟨_, hp, hmem.1⟩, hmem.2⟩
  rw [sideTriangle, dif_pos hex]
  exact hex.choose_spec

omit hτ hx in
/-- A triangle of the white datum containing the side of `p` is `sideTriangle D p`. -/
theorem IsWhiteDatum.eq_sideTriangle {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H}
    (hs : G.cornerSide p ∈ τ.sym2) : τ = G.sideTriangle D p := by
  have hp : p ∈ τ := mem_sym2_iff.1 hs p (Sym2.mem_mk_left _ _)
  obtain ⟨hw, ht⟩ := hτ.vertexOf hp
  obtain ⟨hτ₀, hs₀⟩ := hD.sideTriangle_spec hw
  have hp₀ : p ∈ G.sideTriangle D p := mem_sym2_iff.1 hs₀ p (Sym2.mem_mk_left _ _)
  obtain ⟨-, ht₀⟩ := hτ₀.vertexOf hp₀
  have h1 := (hD _ hw).card_filter_cornerSide hw.three_le_card (G.self_mem_vertexOf p)
  refine card_le_one.1 h1.le _ ?_ _ ?_ <;>
    simp only [mem_filter, RotationSystem.mem_cornerTriangles]
  exacts [⟨ht, hs⟩, ⟨ht₀, hs₀⟩]

omit hτ hx in
/-- For `s ∈ D_w` and a triangle `τ ∋ s` of `D_w`, `otherTriangle D s τ` is the other triangle of
`D_w` containing `s`, and the other triangle of that one is `τ`. -/
theorem IsWhiteDatum.otherTriangle_spec {s : Sym2 H} {τ : Finset H}
    (h : G.IsDatumSegment D s τ) :
    G.IsDatumSegment D s (G.otherTriangle D s τ) ∧ G.otherTriangle D s τ ≠ τ ∧
      G.otherTriangle D s (G.otherTriangle D s τ) = τ := by
  obtain ⟨w, hw, hs, ht, hsτ⟩ := h
  have h2 := (hD w hw).card_filter_mem hw.three_le_card hs
  set F := (G.cornerTriangles w (D w)).filter fun t => s ∈ t.sym2 with hF
  -- a triangle of the datum containing `s` lies in `F`
  have hmemF : ∀ τ', G.IsDatumTriangle D τ' → s ∈ τ'.sym2 → τ' ∈ F := by
    intro τ' hτ' hsτ'
    obtain ⟨u, hu⟩ : ∃ u, u ∈ s := ⟨_, Sym2.out_fst_mem s⟩
    have huw : u ∈ w := ((hD w hw).1 s hs).2 u hu
    have huτ' : u ∈ τ' := mem_sym2_iff.1 hsτ' u hu
    obtain ⟨-, ht'⟩ := hτ'.vertexOf huτ'
    rw [← hw.eq_vertexOf huw] at ht'
    rw [hF, mem_filter, RotationSystem.mem_cornerTriangles]
    exact ⟨ht', hsτ'⟩
  have hτF : τ ∈ F := hmemF τ ⟨w, hw, ht⟩ hsτ
  obtain ⟨α, β, hαβ, hFeq⟩ := card_eq_two.1 h2
  have hex : ∀ τ₀ ∈ F, ∃ τ', G.IsDatumTriangle D τ' ∧ s ∈ τ'.sym2 ∧ τ' ≠ τ₀ := by
    intro τ₀ hτ₀
    rw [hFeq, mem_insert, mem_singleton] at hτ₀
    have hα : α ∈ F := by simp [hFeq]
    have hβ : β ∈ F := by simp [hFeq]
    rw [hF, mem_filter, RotationSystem.mem_cornerTriangles] at hα hβ
    rcases hτ₀ with rfl | rfl
    · exact ⟨β, ⟨w, hw, hβ.1⟩, hβ.2, hαβ.symm⟩
    · exact ⟨α, ⟨w, hw, hα.1⟩, hα.2, hαβ⟩
  have hspec : ∀ τ₀ ∈ F, G.otherTriangle D s τ₀ ∈ F ∧ G.otherTriangle D s τ₀ ≠ τ₀ := by
    intro τ₀ hτ₀
    rw [otherTriangle, dif_pos (hex τ₀ hτ₀)]
    obtain ⟨h1, h2, h3⟩ := (hex τ₀ hτ₀).choose_spec
    exact ⟨hmemF _ h1 h2, h3⟩
  obtain ⟨hoF, hoτ⟩ := hspec τ hτF
  obtain ⟨hooF, hooτ⟩ := hspec _ hoF
  have hoo : G.otherTriangle D s (G.otherTriangle D s τ) = τ := by
    rw [hFeq, mem_insert, mem_singleton] at hτF hoF hooF
    rcases hτF with h1 | h1 <;> rcases hoF with h2 | h2 <;> rcases hooF with h3 | h3 <;>
      first
      | exact (hoτ (h2.trans h1.symm)).elim
      | exact (hooτ (h3.trans h2.symm)).elim
      | exact h3.trans h1.symm
  have hoF' := hoF
  rw [hF, mem_filter, RotationSystem.mem_cornerTriangles] at hoF'
  exact ⟨⟨w, hw, hs, hoF'.1, hoF'.2⟩, hoτ, hoo⟩

omit hτ hx in
/-- A triangle of the white datum containing an element `s` of `D_w` is a triangle of `D_w`. -/
theorem IsWhiteDatum.isCornerTriangle_of_mem {w : Finset H} (hw : G.IsCrossing w) {s : Sym2 H}
    (hs : s ∈ D w) {τ' : Finset H} (hτ' : G.IsDatumTriangle D τ') (hsτ' : s ∈ τ'.sym2) :
    G.IsCornerTriangle w (D w) τ' := by
  have hu : (Quot.out s).1 ∈ s := Sym2.out_fst_mem s
  have huw : (Quot.out s).1 ∈ w := ((hD w hw).1 s hs).2 _ hu
  have huτ' : (Quot.out s).1 ∈ τ' := mem_sym2_iff.1 hsτ' _ hu
  obtain ⟨-, ht'⟩ := hτ'.vertexOf huτ'
  rwa [← hw.eq_vertexOf huw] at ht'

omit hτ hx in
/-- The triangle of the white datum containing `s ∈ D_w` other than `τ` is
`otherTriangle D s τ`. -/
theorem IsWhiteDatum.eq_otherTriangle {s : Sym2 H} {τ τ' : Finset H}
    (h : G.IsDatumSegment D s τ) (hτ' : G.IsDatumTriangle D τ') (hs : s ∈ τ'.sym2)
    (hne : τ' ≠ τ) : τ' = G.otherTriangle D s τ := by
  obtain ⟨ho, hoτ, -⟩ := hD.otherTriangle_spec h
  obtain ⟨w, hw, hsw, ht, hsτ⟩ := h
  have hc2 := (hD w hw).card_filter_mem hw.three_le_card hsw
  have hF : ∀ x, G.IsDatumTriangle D x → s ∈ x.sym2 →
      x ∈ (G.cornerTriangles w (D w)).filter fun t => s ∈ t.sym2 := fun x hx hsx =>
    mem_filter.2 ⟨RotationSystem.mem_cornerTriangles.2
      (hD.isCornerTriangle_of_mem hw hsw hx hsx), hsx⟩
  obtain ⟨α, β, -, hFeq⟩ := card_eq_two.1 hc2
  have m1 := hF τ ⟨w, hw, ht⟩ hsτ
  have m2 := hF τ' hτ' hs
  have m3 := hF _ (.of_isDatumSegment ho) (let ⟨_, _, _, _, h⟩ := ho; h)
  rw [hFeq, mem_insert, mem_singleton] at m1 m2 m3
  rcases m1 with h1 | h1 <;> rcases m2 with h2 | h2 <;> rcases m3 with h3 | h3 <;>
    first
    | exact (hne (h2.trans h1.symm)).elim
    | exact (hoτ (h3.trans h1.symm)).elim
    | exact h2.trans h3.symm

end WhiteDatum

end PlabicData

/-! ### Endpoint labels -/

/-- The value of `finRotate n r`: `r + 1`, or `0` when `r` is the last element. -/
theorem val_finRotate {n : ℕ} (r : Fin n) :
    ((finRotate n r : Fin n) : ℕ) = if (r : ℕ) + 1 = n then (0 : ℕ) else (r : ℕ) + 1 := by
  cases n with
  | zero => exact r.elim0
  | succ n =>
    rw [coe_finRotate]
    simp only [Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega

/-- The arc label `⌊r/2⌋ : Fin b` next to the endpoint label `r : Fin (2 * b)`: `r` is
`sourceIndex (halfIndex r)` or `targetIndex (halfIndex r)` according to its parity. -/
def halfIndex {b : ℕ} (r : Fin (2 * b)) : Fin b := ⟨r / 2, by omega⟩

/-- The value of `halfIndex r` is `r / 2`. -/
@[simp]
theorem halfIndex_val {b : ℕ} (r : Fin (2 * b)) : (halfIndex r : ℕ) = r / 2 := rfl

/-- The arc label next to the endpoint label `2i` is `i`. -/
@[simp]
theorem halfIndex_sourceIndex {b : ℕ} (i : Fin b) : halfIndex (sourceIndex i) = i :=
  Fin.ext (by simp)

/-- The arc label next to the endpoint label `2i + 1` is `i`. -/
@[simp]
theorem halfIndex_targetIndex {b : ℕ} (i : Fin b) : halfIndex (targetIndex i) = i :=
  Fin.ext (by simp; omega)

/-- `2i + 1` follows `2i`. -/
theorem finRotate_sourceIndex {b : ℕ} (i : Fin b) :
    finRotate (2 * b) (sourceIndex i) = targetIndex i :=
  Fin.ext (by rw [val_finRotate]; simp only [sourceIndex_val, targetIndex_val]; split_ifs <;> omega)

/-! ### The symbols of the strand diagram -/

/-- The **symbols** from which the darts of the strand diagram are drawn: `x⁺_d` and `x⁻_t` for
darts `d` and `t`, `y⁺_{s,τ}` and `y⁻_{s,τ}` for a pair `s` and a set `τ` of darts, and `∂_r`,
`∂'_r` for endpoint labels `r : Fin (2 * b)` (`0`-indexed: `r` is the label `r + 1` of [FWZ]).
Distinct constructors give distinct symbols. -/
@[cluster_algebras "def_strand_diagram"]
inductive StrandSymbol (H : Type*) (b : ℕ) where
  /-- The symbol `x⁺_d`. -/
  | xPlus : H → StrandSymbol H b
  /-- The symbol `x⁻_t`. -/
  | xMinus : H → StrandSymbol H b
  /-- The symbol `y⁺_{s,τ}`. -/
  | yPlus : Sym2 H → Finset H → StrandSymbol H b
  /-- The symbol `y⁻_{s,τ}`. -/
  | yMinus : Sym2 H → Finset H → StrandSymbol H b
  /-- The symbol `∂_r`. -/
  | bd : Fin (2 * b) → StrandSymbol H b
  /-- The symbol `∂'_r`. -/
  | bd' : Fin (2 * b) → StrandSymbol H b
  deriving DecidableEq, Fintype

namespace StrandSymbol

variable {H : Type*} {b : ℕ}

/-- The orientation `o°`: `out` (`true`) on the symbols `x⁺`, `y⁺`, and `in` (`false`) on the
others. -/
def isOut : StrandSymbol H b → Bool
  | xPlus _ => true
  | yPlus _ _ => true
  | _ => false

/-- The symbols `∂_r` and `∂'_r`, which make up `B°`. -/
def IsBoundary : StrandSymbol H b → Prop
  | bd _ => True
  | bd' _ => True
  | _ => False

/-- Being a symbol of `B°` is decidable. -/
instance : DecidablePred (IsBoundary (H := H) (b := b)) := fun a => by
  cases a <;> unfold IsBoundary <;> infer_instance

end StrandSymbol

namespace PlabicData

open StrandSymbol

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)
  (D : Finset H → Finset (Sym2 H))

/-- The symbol of the endpoint `ε°(r)` outside `B°`: `x⁺_{g_i}` at the source `r = 2i` and
`x⁻_{ḡ_i}` at the target `r = 2i + 1` (`0`-indexed). -/
def endSymbol (r : Fin (2 * b)) : StrandSymbol H b :=
  if (r : ℕ) % 2 = 0 then xPlus (G.leg (halfIndex r)) else xMinus (G.inv (G.leg (halfIndex r)))

/-- The first symbol of the pair `P_τ(p, p')` for `p' = cornerNext τ p`: `x⁺_p` if `p' = σ⁻¹ p`,
and `y⁺_{{p,p'},τ}` otherwise. -/
noncomputable def pairOut (τ : Finset H) (p : H) : StrandSymbol H b :=
  if G.cornerNext τ p = G.rot.symm p then xPlus p else yPlus s(p, G.cornerNext τ p) τ

/-- The second symbol of the pair `P_τ(p, p')` for `p' = cornerNext τ p`: `x⁻_{p̄}` if
`p' = σ⁻¹ p`, and `y⁻_{{p,p'},τ}` otherwise. -/
noncomputable def pairIn (τ : Finset H) (p : H) : StrandSymbol H b :=
  if G.cornerNext τ p = G.rot.symm p then xMinus (G.inv p) else yMinus s(p, G.cornerNext τ p) τ

/-- The rotation `σ°` of the strand diagram on symbols. On the triangle cycle
`(P_τ(x,y), P_τ(z,x), P_τ(y,z))` of a clockwise listing `(x, y, z)` it sends the first symbol of
each pair to the second, and the second symbol of the pair at `p` to the first symbol of the pair
at the third dart of `τ`; on the endpoint cycles `(∂'_{2i}, ∂_{2i-1}, x⁺_{g_i})` and
`(∂'_{2i+1}, ∂_{2i}, x⁻_{ḡ_i})` it is the cycle (labels as in [FWZ]). -/
noncomputable def strandRotSym : StrandSymbol H b → StrandSymbol H b
  | xPlus d => if h : G.IsLeg d then bd' (targetIndex h.choose) else xMinus (G.inv d)
  | xMinus t =>
    if h : G.IsLeg (G.inv t) then bd' (finRotate _ (targetIndex h.choose))
    else
      G.pairOut (G.sideTriangle D (G.inv t))
        (G.cornerNext (G.sideTriangle D (G.inv t))
          (G.cornerNext (G.sideTriangle D (G.inv t)) (G.inv t)))
  | yPlus s τ => yMinus s τ
  | yMinus s τ => if h : ∃ r ∈ τ, r ∉ s then G.pairOut τ h.choose else yMinus s τ
  | bd r => G.endSymbol r
  | bd' r => bd ((finRotate _).symm r)

/-- The start of the chain ending at `t`: the initial dart `d` with `end(d) = t`, and `t` itself if
there is none. -/
noncomputable def chainStart (t : H) : H :=
  open Classical in
  if h : ∃ d, G.IsInitial d ∧ G.chainEnd d = t then h.choose else t

/-- The involution of the strand diagram on symbols: the pairs `{x⁺_d, x⁻_{end(d)}}`,
`{y⁺_{s,τ}, y⁻_{s,τ'}}` for the two triangles `τ ≠ τ'` containing `s`, and `{∂_r, ∂'_r}`. -/
noncomputable def strandInvSym : StrandSymbol H b → StrandSymbol H b
  | xPlus d => xMinus (G.chainEnd d)
  | xMinus t => xPlus (G.chainStart t)
  | yPlus s τ => yMinus s (G.otherTriangle D s τ)
  | yMinus s τ => yPlus s (G.otherTriangle D s τ)
  | bd r => bd' r
  | bd' r => bd r

/-- The symbols that are darts of the strand diagram: `x⁺_d` for initial `d`, `x⁻_t` for terminal
`t`, `y^±_{s,τ}` for `s ∈ D_w` and a triangle `τ ∋ s` of `D_w` (`w` a crossing), and all `∂_r`,
`∂'_r`. -/
def IsStrandSymbol : StrandSymbol H b → Prop
  | xPlus d => G.IsInitial d
  | xMinus t => G.IsTerminal t
  | yPlus s τ => G.IsDatumSegment D s τ
  | yMinus s τ => G.IsDatumSegment D s τ
  | bd _ => True
  | bd' _ => True

/-- Being a dart of the strand diagram is decidable. -/
instance : DecidablePred (G.IsStrandSymbol D) := fun a => by
  cases a <;> unfold IsStrandSymbol <;> infer_instance

/-- The darts `H°` of the strand diagram `X°(G, D)`. -/
abbrev StrandDart : Type _ := {a : StrandSymbol H b // G.IsStrandSymbol D a}

variable {G D}

omit [Fintype H] [DecidableEq H] in
/-- The symbol of the endpoint `ε°(2i)` is `x⁺_{g_i}`. -/
theorem endSymbol_sourceIndex (i : Fin b) : G.endSymbol (sourceIndex i) = xPlus (G.leg i) := by
  simp [endSymbol]

omit [Fintype H] [DecidableEq H] in
/-- The symbol of the endpoint `ε°(2i + 1)` is `x⁻_{ḡ_i}`. -/
theorem endSymbol_targetIndex (i : Fin b) :
    G.endSymbol (targetIndex i) = xMinus (G.inv (G.leg i)) := by
  rw [endSymbol, if_neg (by simp), halfIndex_targetIndex]

/-- An element of a triangle of the white datum is not in `B`. -/
theorem IsDatumTriangle.notMem_bdry {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H}
    (hp : p ∈ τ) : p ∉ G.bdry := fun h =>
  (hτ.vertexOf hp).1.not_isBoundaryVertex ⟨p, G.self_mem_vertexOf p, h⟩

/-- `σ°` sends `∂_r` to the symbol of the endpoint `ε°(r)`. -/
theorem strandRotSym_bd (r : Fin (2 * b)) : G.strandRotSym D (bd r) = G.endSymbol r := rfl

/-- `σ°` sends `∂'_r` to `∂_{r-1}`. -/
theorem strandRotSym_bd' (r : Fin (2 * b)) :
    G.strandRotSym D (bd' r) = bd ((finRotate _).symm r) := rfl

section IsPlabicGraph

variable (hG : G.IsPlabicGraph)

include hG

/-- In a plabic graph, the chosen label of a leg `d = g_i` is `i`. -/
theorem IsPlabicGraph.isLeg_choose_eq {d : H} (h : G.IsLeg d) {i : Fin b} (hi : G.leg i = d) :
    h.choose = i :=
  hG.leg_injective (h.choose_spec.trans hi.symm)

/-- In a plabic graph, a dart at a crossing is not a leg. -/
theorem IsPlabicGraph.not_isLeg_of_isCrossing {p : H} (hp : G.IsCrossing (G.vertexOf p)) :
    ¬G.IsLeg p := fun h => hp.not_isBoundaryVertex (hG.isBoundaryVertex_of_isLeg h)

/-- The symbol of each endpoint `ε°(r)` is a dart of the strand diagram. -/
theorem isStrandSymbol_endSymbol (r : Fin (2 * b)) : G.IsStrandSymbol D (G.endSymbol r) := by
  unfold endSymbol
  split_ifs
  · exact (show G.IsInitial _ from ⟨hG.leg_notMem_bdry _, Or.inr ⟨_, rfl⟩⟩)
  · refine (show G.IsTerminal _ from
      ⟨fun h => hG.leg_notMem_bdry _ (hG.inv_mem_bdry_iff.1 h), Or.inr ?_⟩)
    rw [hG.inv_involutive]
    exact hG.isBoundaryVertex_of_isLeg ⟨_, rfl⟩

/-- `σ°` sends the symbol of the endpoint `ε°(r)` to `∂'_{r+1}`. -/
theorem strandRotSym_endSymbol (r : Fin (2 * b)) :
    G.strandRotSym D (G.endSymbol r) = bd' (finRotate _ r) := by
  rcases exists_sourceIndex_or_targetIndex r with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hl : G.IsLeg (G.leg i) := ⟨i, rfl⟩
    rw [endSymbol_sourceIndex, strandRotSym, dif_pos hl, hG.isLeg_choose_eq hl rfl,
      finRotate_sourceIndex]
  · rw [endSymbol_targetIndex]
    have hl : G.IsLeg (G.inv (G.inv (G.leg i))) := ⟨i, (hG.inv_involutive _).symm⟩
    rw [strandRotSym, dif_pos hl, hG.isLeg_choose_eq hl (hG.inv_involutive _).symm]

/-- The start of the chain ending at a terminal dart `t` is an initial dart `d` with
`end(d) = t`. -/
theorem IsTerminal.chainStart_spec {t : H} (ht : G.IsTerminal t) :
    G.IsInitial (G.chainStart t) ∧ G.chainEnd (G.chainStart t) = t := by
  have hex := ht.exists_chainEnd_eq hG
  rw [chainStart, dif_pos hex]
  exact hex.choose_spec

/-- The start of the chain ending at `end(d)`, for `d` initial, is `d`. -/
theorem IsInitial.chainStart_chainEnd {d : H} (hd : G.IsInitial d) :
    G.chainStart (G.chainEnd d) = d := by
  obtain ⟨h1, h2⟩ := (hd.isTerminal_chainEnd hG).chainStart_spec hG
  exact chainEnd_injOn hG h1 hd h2

section WhiteDatum

variable (hD : G.IsWhiteDatum D)

include hD

omit hG in
/-- The first symbol of the pair `P_τ(p, cornerNext τ p)` is a dart of the strand diagram. -/
theorem isStrandSymbol_pairOut {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H}
    (hp : p ∈ τ) : G.IsStrandSymbol D (G.pairOut τ p) := by
  unfold pairOut
  split_ifs with h
  · exact (show G.IsInitial p from ⟨hτ.notMem_bdry hp, Or.inl (hτ.vertexOf hp).1⟩)
  · exact (show G.IsDatumSegment D _ τ from ⟨_, (hτ.vertexOf hp).1,
      hD.mk_cornerNext_mem hτ hp h, (hτ.vertexOf hp).2,
      mk_mem_sym2_iff.2 ⟨hp, hD.cornerNext_mem hτ hp⟩⟩)

/-- The second symbol of the pair `P_τ(p, cornerNext τ p)` is a dart of the strand diagram. -/
theorem isStrandSymbol_pairIn {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H}
    (hp : p ∈ τ) : G.IsStrandSymbol D (G.pairIn τ p) := by
  unfold pairIn
  split_ifs with h
  · refine (show G.IsTerminal (G.inv p) from
      ⟨fun h' => hτ.notMem_bdry hp (hG.inv_mem_bdry_iff.1 h'), Or.inl ?_⟩)
    rw [hG.inv_involutive]
    exact (hτ.vertexOf hp).1
  · exact (show G.IsDatumSegment D _ τ from ⟨_, (hτ.vertexOf hp).1,
      hD.mk_cornerNext_mem hτ hp h, (hτ.vertexOf hp).2,
      mk_mem_sym2_iff.2 ⟨hp, hD.cornerNext_mem hτ hp⟩⟩)

omit hG in
/-- A pair `(s, τ)` indexing `y^±_{s,τ}` is `s = {p, cornerNext τ p}` for a dart `p ∈ τ` whose
pair `{p, cornerNext τ p}` is not its side. -/
theorem IsWhiteDatum.exists_eq_mk_cornerNext {s : Sym2 H} {τ : Finset H}
    (h : G.IsDatumSegment D s τ) :
    ∃ p ∈ τ, s = s(p, G.cornerNext τ p) ∧ G.cornerNext τ p ≠ G.rot.symm p := by
  obtain ⟨w, hw, hs, ht, hsτ⟩ := h
  have hτ : G.IsDatumTriangle D τ := ⟨w, hw, ht⟩
  have hnotside : ∀ p ∈ τ, s = s(p, G.cornerNext τ p) → G.cornerNext τ p ≠ G.rot.symm p := by
    intro p hp he hn
    rw [hn] at he
    refine cornerSide_notMem_of_isCornerTriangulation (hD w hw) (ht.1 hp) ?_
    rw [RotationSystem.cornerSide, ← he]
    exact hs
  induction s using Sym2.ind with | _ x y => ?_
  rw [mk_mem_sym2_iff] at hsτ
  have hxy : x ≠ y := fun e => ((hD w hw).1 _ hs).1 (by rw [e]; exact Sym2.mk_isDiag_iff.2 rfl)
  have hy := hsτ.2
  rw [hD.eq_insert_cornerNext hτ hsτ.1] at hy
  simp only [mem_insert, mem_singleton] at hy
  rcases hy with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact ⟨x, hsτ.1, rfl, hnotside x hsτ.1 rfl⟩
  · have hp := hD.cornerNext_mem hτ (hD.cornerNext_mem hτ hsτ.1)
    have he : s(x, G.cornerNext τ (G.cornerNext τ x)) = s(G.cornerNext τ (G.cornerNext τ x),
        G.cornerNext τ (G.cornerNext τ (G.cornerNext τ x))) := by
      rw [hD.cornerNext_three hτ hsτ.1, Sym2.eq_swap]
    exact ⟨_, hp, he, hnotside _ hp he⟩

/-- **Classification of the darts of the strand diagram.** Every dart is a `∂_r`, a `∂'_r`, the
endpoint symbol `x⁺_{g_i}` or `x⁻_{ḡ_i}` of an endpoint, or one of the two symbols of a pair
`P_τ(p, cornerNext τ p)` of a triangle `τ` of the white datum. -/
theorem IsStrandSymbol.cases {a : StrandSymbol H b} (ha : G.IsStrandSymbol D a) :
    (∃ r, a = bd r) ∨ (∃ r, a = bd' r) ∨ (∃ r, a = G.endSymbol r) ∨
      (∃ τ p, G.IsDatumTriangle D τ ∧ p ∈ τ ∧ a = G.pairOut τ p) ∨
      (∃ τ p, G.IsDatumTriangle D τ ∧ p ∈ τ ∧ a = G.pairIn τ p) := by
  cases a with
  | xPlus d =>
    obtain ⟨-, hc | ⟨i, rfl⟩⟩ := (ha : G.IsInitial d)
    · obtain ⟨hτ, hs⟩ := hD.sideTriangle_spec hc
      have hd : d ∈ G.sideTriangle D d := mem_sym2_iff.1 hs d (Sym2.mem_mk_left _ _)
      have hd' : G.rot.symm d ∈ G.sideTriangle D d :=
        mem_sym2_iff.1 hs _ (Sym2.mem_mk_right _ _)
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨_, d, hτ, hd, ?_⟩)))
      rw [pairOut, if_pos (hD.cornerNext_eq_rot_symm hτ hd hd')]
    · exact Or.inr (Or.inr (Or.inl ⟨sourceIndex i, (endSymbol_sourceIndex i).symm⟩))
  | xMinus t =>
    obtain ⟨htB, hc | hb⟩ := (ha : G.IsTerminal t)
    · obtain ⟨hτ, hs⟩ := hD.sideTriangle_spec hc
      have hd : G.inv t ∈ G.sideTriangle D (G.inv t) := mem_sym2_iff.1 hs _ (Sym2.mem_mk_left _ _)
      have hd' : G.rot.symm (G.inv t) ∈ G.sideTriangle D (G.inv t) :=
        mem_sym2_iff.1 hs _ (Sym2.mem_mk_right _ _)
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, G.inv t, hτ, hd, ?_⟩)))
      rw [pairIn, if_pos (hD.cornerNext_eq_rot_symm hτ hd hd'), hG.inv_involutive]
    · obtain ⟨i, hi⟩ := hG.isLeg_of_isBoundaryVertex (fun h => htB (hG.inv_mem_bdry_iff.1 h)) hb
      refine Or.inr (Or.inr (Or.inl ⟨targetIndex i, ?_⟩))
      rw [endSymbol_targetIndex, hi, hG.inv_involutive]
  | yPlus s τ =>
    have hτ : G.IsDatumTriangle D τ := .of_isDatumSegment (ha : G.IsDatumSegment D s τ)
    obtain ⟨p, hp, rfl, hn⟩ := hD.exists_eq_mk_cornerNext (ha : G.IsDatumSegment D s τ)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨τ, p, hτ, hp, by rw [pairOut, if_neg hn]⟩)))
  | yMinus s τ =>
    have hτ : G.IsDatumTriangle D τ := .of_isDatumSegment (ha : G.IsDatumSegment D s τ)
    obtain ⟨p, hp, rfl, hn⟩ := hD.exists_eq_mk_cornerNext (ha : G.IsDatumSegment D s τ)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨τ, p, hτ, hp, by rw [pairIn, if_neg hn]⟩)))
  | bd r => exact Or.inl ⟨r, rfl⟩
  | bd' r => exact Or.inr (Or.inl ⟨r, rfl⟩)

omit hD in
/-- `σ°` sends the first symbol of the pair at `p` to the second. -/
theorem strandRotSym_pairOut {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H} (hp : p ∈ τ) :
    G.strandRotSym D (G.pairOut τ p) = G.pairIn τ p := by
  unfold pairOut pairIn
  split_ifs with h
  · rw [strandRotSym, dif_neg (hG.not_isLeg_of_isCrossing (hτ.vertexOf hp).1)]
  · rfl

/-- `σ°` sends the second symbol of the pair at `p` to the first symbol of the pair at the third
dart `cornerNext τ (cornerNext τ p)` of `τ`. -/
theorem strandRotSym_pairIn {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H} (hp : p ∈ τ) :
    G.strandRotSym D (G.pairIn τ p) = G.pairOut τ (G.cornerNext τ (G.cornerNext τ p)) := by
  unfold pairIn
  split_ifs with h
  · have hnl : ¬G.IsLeg (G.inv (G.inv p)) := by
      rw [hG.inv_involutive]
      exact hG.not_isLeg_of_isCrossing (hτ.vertexOf hp).1
    have hside : G.cornerSide p ∈ τ.sym2 := by
      rw [RotationSystem.cornerSide, ← h]
      exact mk_mem_sym2_iff.2 ⟨hp, hD.cornerNext_mem hτ hp⟩
    rw [strandRotSym, dif_neg hnl, hG.inv_involutive, ← hD.eq_sideTriangle hτ hside]
  · have hex : ∃ r ∈ τ, r ∉ s(p, G.cornerNext τ p) :=
      ⟨_, hD.cornerNext_mem hτ (hD.cornerNext_mem hτ hp), by
        simp only [Sym2.mem_iff, not_or]
        exact ⟨hD.cornerNext_cornerNext_ne hτ hp,
          hD.cornerNext_cornerNext_ne_cornerNext hτ hp⟩⟩
    rw [strandRotSym, dif_pos hex]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    rw [← hD.eq_cornerNext_cornerNext hτ hp h1 h2]

/-- The involution on symbols sends darts of the strand diagram to darts. -/
theorem isStrandSymbol_strandInvSym {a : StrandSymbol H b} (ha : G.IsStrandSymbol D a) :
    G.IsStrandSymbol D (G.strandInvSym D a) := by
  cases a with
  | xPlus d => exact (ha : G.IsInitial d).isTerminal_chainEnd hG
  | xMinus t => exact ((ha : G.IsTerminal t).chainStart_spec hG).1
  | yPlus s τ => exact (hD.otherTriangle_spec (ha : G.IsDatumSegment D s τ)).1
  | yMinus s τ => exact (hD.otherTriangle_spec (ha : G.IsDatumSegment D s τ)).1
  | bd r => trivial
  | bd' r => trivial

/-- The involution on symbols is an involution on the darts of the strand diagram. -/
theorem strandInvSym_strandInvSym {a : StrandSymbol H b} (ha : G.IsStrandSymbol D a) :
    G.strandInvSym D (G.strandInvSym D a) = a := by
  cases a with
  | xPlus d =>
    change xPlus (G.chainStart (G.chainEnd d)) = xPlus d
    rw [(ha : G.IsInitial d).chainStart_chainEnd hG]
  | xMinus t =>
    change xMinus (G.chainEnd (G.chainStart t)) = xMinus t
    rw [((ha : G.IsTerminal t).chainStart_spec hG).2]
  | yPlus s τ =>
    change yPlus s (G.otherTriangle D s (G.otherTriangle D s τ)) = yPlus s τ
    rw [(hD.otherTriangle_spec (ha : G.IsDatumSegment D s τ)).2.2]
  | yMinus s τ =>
    change yMinus s (G.otherTriangle D s (G.otherTriangle D s τ)) = yMinus s τ
    rw [(hD.otherTriangle_spec (ha : G.IsDatumSegment D s τ)).2.2]
  | bd r => rfl
  | bd' r => rfl

/-- The rotation `σ°` on symbols sends darts of the strand diagram to darts. -/
theorem isStrandSymbol_strandRotSym {a : StrandSymbol H b} (ha : G.IsStrandSymbol D a) :
    G.IsStrandSymbol D (G.strandRotSym D a) := by
  rcases IsStrandSymbol.cases hG hD ha with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ |
    ⟨τ, p, hτ, hp, rfl⟩ | ⟨τ, p, hτ, hp, rfl⟩
  · exact isStrandSymbol_endSymbol hG r
  · trivial
  · rw [strandRotSym_endSymbol hG]; trivial
  · rw [strandRotSym_pairOut hG hτ hp]; exact isStrandSymbol_pairIn hG hD hτ hp
  · rw [strandRotSym_pairIn hG hD hτ hp]
    exact isStrandSymbol_pairOut hD hτ (hD.cornerNext_mem hτ (hD.cornerNext_mem hτ hp))

/-- Every dart of the strand diagram is the image under `σ°` of a dart. -/
theorem exists_strandRotSym_eq {a : StrandSymbol H b} (ha : G.IsStrandSymbol D a) :
    ∃ a', G.IsStrandSymbol D a' ∧ G.strandRotSym D a' = a := by
  rcases IsStrandSymbol.cases hG hD ha with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ |
    ⟨τ, p, hτ, hp, rfl⟩ | ⟨τ, p, hτ, hp, rfl⟩
  · exact ⟨bd' (finRotate _ r), trivial, by rw [strandRotSym_bd', Equiv.symm_apply_apply]⟩
  · exact ⟨G.endSymbol ((finRotate _).symm r), isStrandSymbol_endSymbol hG _, by
      rw [strandRotSym_endSymbol hG, Equiv.apply_symm_apply]⟩
  · exact ⟨bd r, trivial, rfl⟩
  · have hq := hD.cornerNext_mem hτ hp
    exact ⟨G.pairIn τ (G.cornerNext τ p), isStrandSymbol_pairIn hG hD hτ hq, by
      rw [strandRotSym_pairIn hG hD hτ hq, hD.cornerNext_three hτ hp]⟩
  · exact ⟨G.pairOut τ p, isStrandSymbol_pairOut hD hτ hp, strandRotSym_pairOut hG hτ hp⟩

end WhiteDatum

end IsPlabicGraph

/-! ### The strand diagram -/

section Diagram

variable (G) (hG : G.IsPlabicGraph) (hD : G.IsWhiteDatum D)

/-- The involution `d ↦ d̄` of the strand diagram. -/
noncomputable def strandInv : Equiv.Perm (G.StrandDart D) :=
  Function.Involutive.toPerm
    (fun a => ⟨G.strandInvSym D a.1, isStrandSymbol_strandInvSym hG hD a.2⟩)
    fun a => Subtype.ext (strandInvSym_strandInvSym hG hD a.2)

/-- The rotation `σ°` of the strand diagram. -/
noncomputable def strandRot : Equiv.Perm (G.StrandDart D) :=
  Equiv.ofBijective (fun a => ⟨G.strandRotSym D a.1, isStrandSymbol_strandRotSym hG hD a.2⟩)
    (Finite.surjective_iff_bijective.1 fun a =>
      let ⟨a', ha', h⟩ := exists_strandRotSym_eq hG hD a.2
      ⟨⟨a', ha'⟩, Subtype.ext h⟩)

/-- **The strand diagram** `X°(G, D) = (H°, d ↦ d̄, σ°, B°, ε°, o°)` of a plabic graph `G` with a
white datum `D`. Its darts are the symbols `x⁺_d` (`d` initial), `x⁻_t` (`t` terminal),
`y^±_{s,τ}` (`s ∈ D_w`, `τ ∋ s` a triangle of `D_w`) and `∂_r`, `∂'_r`; the involution pairs
`x⁺_d` with `x⁻_{end(d)}`, `y⁺_{s,τ}` with `y⁻_{s,τ'}` for the other triangle `τ'` containing `s`,
and `∂_r` with `∂'_r`; the rotation is given by the triangle cycles
`(P_τ(x,y), P_τ(z,x), P_τ(y,z))` and the endpoint cycles; `B° = {∂_r, ∂'_r}`; the endpoints
`ε°(2i - 1)`, `ε°(2i)` are the cycles of `x⁺_{g_i}`, `x⁻_{ḡ_i}` (recorded by these darts,
`0`-indexed); and `o°` is `out` on `x⁺`, `y⁺` and `in` on `x⁻`, `y⁻`. -/
@[cluster_algebras "def_strand_diagram"]
noncomputable def strandDiagram : TripleData (G.StrandDart D) b where
  inv := G.strandInv hG hD
  rot := G.strandRot hG hD
  bdry := univ.filter fun a => a.1.IsBoundary
  endDart r := ⟨G.endSymbol r, isStrandSymbol_endSymbol hG r⟩
  isOut a := a.1.isOut

variable {G}

/-- The involution of the strand diagram is the involution on symbols. -/
@[simp]
theorem strandDiagram_inv_apply (a : G.StrandDart D) :
    ((G.strandDiagram hG hD).inv a).1 = G.strandInvSym D a.1 := rfl

/-- The rotation of the strand diagram is the rotation `σ°` on symbols. -/
@[simp]
theorem strandDiagram_rot_apply (a : G.StrandDart D) :
    ((G.strandDiagram hG hD).rot a).1 = G.strandRotSym D a.1 := rfl

/-- A dart of the strand diagram is in `B°` if and only if it is some `∂_r` or `∂'_r`. -/
theorem mem_strandDiagram_bdry {a : G.StrandDart D} :
    a ∈ (G.strandDiagram hG hD).bdry ↔ a.1.IsBoundary := by
  simp [strandDiagram]

/-- The dart recording the endpoint `ε°(r)` of the strand diagram is `endSymbol r`. -/
@[simp]
theorem strandDiagram_endDart (r : Fin (2 * b)) :
    ((G.strandDiagram hG hD).endDart r).1 = G.endSymbol r := rfl

/-- The orientation of the strand diagram is the orientation `o°` on symbols. -/
@[simp]
theorem strandDiagram_isOut (a : G.StrandDart D) :
    (G.strandDiagram hG hD).isOut a = a.1.isOut := rfl

variable (G D) in
/-- The triple point of `X°(G, D)` of a triangle `τ` of the white datum: the six symbols of the
pairs `P_τ(p, cornerNext τ p)`, `p ∈ τ`. -/
noncomputable def strandTriplePoint (τ : Finset H) : Finset (G.StrandDart D) :=
  univ.filter fun a => ∃ x ∈ τ, a.1 = G.pairOut τ x ∨ a.1 = G.pairIn τ x

end Diagram

end PlabicData

/-! ### Orbits of a permutation -/

/-- The orbit of `a` under a permutation of a finite type is any set containing `a`, closed under
the permutation, all of whose elements lie in the orbit of `a`. -/
theorem filter_sameCycle_eq {α : Type*} [Fintype α] [DecidableEq α] {f : Equiv.Perm α} {a : α}
    {S : Finset α} (ha : a ∈ S) (hS : ∀ y ∈ S, f y ∈ S) (hreach : ∀ y ∈ S, f.SameCycle a y) :
    ({e ∈ univ | f.SameCycle a e} : Finset α) = S := by
  ext y
  simp only [mem_filter, mem_univ, true_and]
  refine ⟨fun h => ?_, hreach y⟩
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using ha
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hS _ ih

/-- If `f a = b`, then `a` and `b` lie in the same cycle of `f`. -/
theorem sameCycle_of_apply_eq {α : Type*} {f : Equiv.Perm α} {a b : α} (h : f a = b) :
    f.SameCycle a b :=
  ⟨1, by rw [zpow_one, h]⟩

namespace PlabicData

open StrandSymbol

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  {D : Finset H → Finset (Sym2 H)}

/-! ### The symbols of the pairs -/

omit [Fintype H] in
/-- A first symbol of a pair is never a second symbol of a pair. -/
theorem pairOut_ne_pairIn (τ τ' : Finset H) (x y : H) : G.pairOut τ x ≠ G.pairIn τ' y := by
  unfold pairOut pairIn; split_ifs <;> simp

omit [Fintype H] [DecidableEq H] in
/-- The symbol of an endpoint is never `∂_{r'}`. -/
theorem endSymbol_ne_bd (r r' : Fin (2 * b)) : G.endSymbol r ≠ bd r' := by
  unfold endSymbol; split_ifs <;> simp

omit [Fintype H] [DecidableEq H] in
/-- The symbol of an endpoint is never `∂'_{r'}`. -/
theorem endSymbol_ne_bd' (r r' : Fin (2 * b)) : G.endSymbol r ≠ bd' r' := by
  unfold endSymbol; split_ifs <;> simp

omit [Fintype H] [DecidableEq H] in
/-- The symbol of an endpoint is not in `B°`. -/
theorem not_isBoundary_endSymbol (r : Fin (2 * b)) : ¬(G.endSymbol r).IsBoundary := by
  unfold endSymbol; split_ifs <;> simp [IsBoundary]

omit [Fintype H] in
/-- The first symbol of a pair is not in `B°`. -/
theorem not_isBoundary_pairOut (τ : Finset H) (p : H) : ¬(G.pairOut τ p).IsBoundary := by
  unfold pairOut; split_ifs <;> simp [IsBoundary]

omit [Fintype H] in
/-- The second symbol of a pair is not in `B°`. -/
theorem not_isBoundary_pairIn (τ : Finset H) (p : H) : ¬(G.pairIn τ p).IsBoundary := by
  unfold pairIn; split_ifs <;> simp [IsBoundary]

omit [Fintype H] in
/-- The first symbol of a pair is oriented `out`. -/
@[simp]
theorem isOut_pairOut (τ : Finset H) (p : H) : (G.pairOut τ p).isOut = true := by
  unfold pairOut; split_ifs <;> rfl

omit [Fintype H] in
/-- The second symbol of a pair is oriented `in`. -/
@[simp]
theorem isOut_pairIn (τ : Finset H) (p : H) : (G.pairIn τ p).isOut = false := by
  unfold pairIn; split_ifs <;> rfl

/-- On a triangle `τ` of the white datum, `p ↦ pairOut τ p` is injective. -/
theorem IsWhiteDatum.pairOut_injOn (hD : G.IsWhiteDatum D) {τ : Finset H}
    (hτ : G.IsDatumTriangle D τ) : Set.InjOn (G.pairOut τ) τ := by
  intro x hx y hy h
  unfold pairOut at h
  split_ifs at h with h1 h2 h2
  all_goals first
    | exact xPlus.inj h
    | contradiction
    | skip
  · obtain ⟨he, -⟩ := yPlus.inj h
    rcases Sym2.eq_iff.1 he with ⟨h3, -⟩ | ⟨h3, h4⟩
    · exact h3
    · rw [h3] at h4
      exact absurd h4 (hD.cornerNext_cornerNext_ne hτ hy)

/-- On a triangle `τ` of the white datum, `p ↦ pairIn τ p` is injective. -/
theorem IsWhiteDatum.pairIn_injOn (hD : G.IsWhiteDatum D) {τ : Finset H}
    (hτ : G.IsDatumTriangle D τ) : Set.InjOn (G.pairIn τ) τ := by
  intro x hx y hy h
  unfold pairIn at h
  split_ifs at h with h1 h2 h2
  all_goals first
    | exact G.inv.injective (xMinus.inj h)
    | contradiction
    | skip
  · obtain ⟨he, -⟩ := yMinus.inj h
    rcases Sym2.eq_iff.1 he with ⟨h3, -⟩ | ⟨h3, h4⟩
    · exact h3
    · rw [h3] at h4
      exact absurd h4 (hD.cornerNext_cornerNext_ne hτ hy)

/-! ### The strand diagram is a pre-triple diagram -/

section PreTriple

variable (hG : G.IsPlabicGraph) (hD : G.IsWhiteDatum D)

include hG hD

/-- **Classification of the darts of the strand diagram**, on darts. -/
theorem strandDart_cases (a : G.StrandDart D) :
    (∃ r, a = ⟨bd r, trivial⟩) ∨ (∃ r, a = ⟨bd' r, trivial⟩) ∨
      (∃ r, a = ⟨G.endSymbol r, isStrandSymbol_endSymbol hG r⟩) ∨
      (∃ τ p, ∃ (hτ : G.IsDatumTriangle D τ) (hp : p ∈ τ),
        a = ⟨G.pairOut τ p, isStrandSymbol_pairOut hD hτ hp⟩) ∨
      (∃ τ p, ∃ (hτ : G.IsDatumTriangle D τ) (hp : p ∈ τ),
        a = ⟨G.pairIn τ p, isStrandSymbol_pairIn hG hD hτ hp⟩) := by
  obtain ⟨a, ha⟩ := a
  rcases IsStrandSymbol.cases hG hD ha with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ |
    ⟨τ, p, hτ, hp, rfl⟩ | ⟨τ, p, hτ, hp, rfl⟩
  · exact Or.inl ⟨r, rfl⟩
  · exact Or.inr (Or.inl ⟨r, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨r, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨τ, p, hτ, hp, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨τ, p, hτ, hp, rfl⟩)))

/-- The rotation of the strand diagram sends `∂_r` to the dart of the endpoint `ε°(r)`. -/
theorem strandDiagram_rot_bd (r : Fin (2 * b)) :
    (G.strandDiagram hG hD).rot ⟨bd r, trivial⟩ =
      ⟨G.endSymbol r, isStrandSymbol_endSymbol hG r⟩ := Subtype.ext rfl

/-- The rotation of the strand diagram sends the dart of the endpoint `ε°(r)` to `∂'_{r+1}`. -/
theorem strandDiagram_rot_endSymbol (r : Fin (2 * b)) (h : G.IsStrandSymbol D (G.endSymbol r)) :
    (G.strandDiagram hG hD).rot ⟨G.endSymbol r, h⟩ = ⟨bd' (finRotate _ r), trivial⟩ :=
  Subtype.ext (strandRotSym_endSymbol hG r)

/-- The rotation of the strand diagram sends `∂'_r` to `∂_{r-1}`. -/
theorem strandDiagram_rot_bd' (r : Fin (2 * b)) :
    (G.strandDiagram hG hD).rot ⟨bd' r, trivial⟩ = ⟨bd ((finRotate _).symm r), trivial⟩ :=
  Subtype.ext rfl

/-- The rotation of the strand diagram sends `pairOut τ p` to `pairIn τ p`. -/
theorem strandDiagram_rot_pairOut {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H}
    (hp : p ∈ τ) (h : G.IsStrandSymbol D (G.pairOut τ p)) :
    (G.strandDiagram hG hD).rot ⟨G.pairOut τ p, h⟩ =
      ⟨G.pairIn τ p, isStrandSymbol_pairIn hG hD hτ hp⟩ :=
  Subtype.ext (strandRotSym_pairOut hG hτ hp)

/-- The rotation of the strand diagram sends `pairIn τ p` to `pairOut τ r`, for `r` the second
clockwise successor of `p` in `τ`. -/
theorem strandDiagram_rot_pairIn {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H}
    (hp : p ∈ τ) (h : G.IsStrandSymbol D (G.pairIn τ p)) :
    (G.strandDiagram hG hD).rot ⟨G.pairIn τ p, h⟩ =
      ⟨G.pairOut τ (G.cornerNext τ (G.cornerNext τ p)), isStrandSymbol_pairOut hD hτ
        (hD.cornerNext_mem hτ (hD.cornerNext_mem hτ hp))⟩ :=
  Subtype.ext (strandRotSym_pairIn hG hD hτ hp)

/-- The endpoint cycle of `∂_r`: `{∂_r, x, ∂'_{r+1}}` for the endpoint symbol `x` of `r`. -/
theorem strandDiagram_vertexOf_bd (r : Fin (2 * b)) :
    (G.strandDiagram hG hD).vertexOf ⟨bd r, trivial⟩ =
      {⟨bd r, trivial⟩, ⟨G.endSymbol r, isStrandSymbol_endSymbol hG r⟩,
        ⟨bd' (finRotate _ r), trivial⟩} := by
  have h1 := strandDiagram_rot_bd hG hD r
  have h2 := strandDiagram_rot_endSymbol hG hD r (isStrandSymbol_endSymbol hG r)
  have h3 : (G.strandDiagram hG hD).rot ⟨bd' (finRotate _ r), trivial⟩ = ⟨bd r, trivial⟩ := by
    rw [strandDiagram_rot_bd', Equiv.symm_apply_apply]
  refine filter_sameCycle_eq (by simp) ?_ ?_
  · intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · simp [h1]
    · simp [h2]
    · rw [h3]
      simp
  · intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact sameCycle_of_apply_eq h1
    · exact (sameCycle_of_apply_eq h1).trans (sameCycle_of_apply_eq h2)

/-- The cycle of the first symbol of a pair of a triangle `τ` is the triple point of `τ`. -/
theorem strandDiagram_vertexOf_pairOut {τ : Finset H} (hτ : G.IsDatumTriangle D τ) {p : H}
    (hp : p ∈ τ) :
    (G.strandDiagram hG hD).vertexOf ⟨G.pairOut τ p, isStrandSymbol_pairOut hD hτ hp⟩ =
      G.strandTriplePoint D τ := by
  set X := G.strandDiagram hG hD
  have step : ∀ x (hx : x ∈ τ) (a : G.StrandDart D),
      a.1 = G.pairOut τ (G.cornerNext τ (G.cornerNext τ x)) →
        X.rot.SameCycle ⟨G.pairOut τ x, isStrandSymbol_pairOut hD hτ hx⟩ a := by
    intro x hx a ha
    have e : a = ⟨G.pairOut τ (G.cornerNext τ (G.cornerNext τ x)), isStrandSymbol_pairOut hD hτ
        (hD.cornerNext_mem hτ (hD.cornerNext_mem hτ hx))⟩ := Subtype.ext ha
    rw [e]
    exact (sameCycle_of_apply_eq (strandDiagram_rot_pairOut hG hD hτ hx _)).trans
      (sameCycle_of_apply_eq (strandDiagram_rot_pairIn hG hD hτ hx _))
  have hout : ∀ x (hx : x ∈ τ),
      X.rot.SameCycle ⟨G.pairOut τ p, isStrandSymbol_pairOut hD hτ hp⟩
        ⟨G.pairOut τ x, isStrandSymbol_pairOut hD hτ hx⟩ := by
    intro x hx
    have hq := hD.cornerNext_mem hτ hp
    have hr := hD.cornerNext_mem hτ hq
    have hx' := hx
    rw [hD.eq_insert_cornerNext hτ hp] at hx'
    simp only [mem_insert, mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.refl _ _
    · refine (step p hp ⟨_, isStrandSymbol_pairOut hD hτ hr⟩ rfl).trans
        (step _ hr _ ?_)
      change G.pairOut τ (G.cornerNext τ p) = _
      rw [hD.cornerNext_three hτ hp]
    · exact step p hp _ rfl
  refine filter_sameCycle_eq ?_ ?_ ?_
  · simp only [strandTriplePoint, mem_filter, mem_univ, true_and]
    exact ⟨p, hp, Or.inl rfl⟩
  · rintro ⟨y, hy⟩ hyS
    simp only [strandTriplePoint, mem_filter, mem_univ, true_and] at hyS ⊢
    obtain ⟨x, hx, rfl | rfl⟩ := hyS
    · exact ⟨x, hx, Or.inr (strandRotSym_pairOut hG hτ hx)⟩
    · exact ⟨_, hD.cornerNext_mem hτ (hD.cornerNext_mem hτ hx),
        Or.inl (strandRotSym_pairIn hG hD hτ hx)⟩
  · rintro ⟨y, hy⟩ hyS
    simp only [strandTriplePoint, mem_filter, mem_univ, true_and] at hyS
    obtain ⟨x, hx, rfl | rfl⟩ := hyS
    · exact hout x hx
    · exact (hout x hx).trans (sameCycle_of_apply_eq (strandDiagram_rot_pairOut hG hD hτ hx _))

/-- A triple point of the strand diagram has six darts. -/
theorem card_strandTriplePoint {τ : Finset H} (hτ : G.IsDatumTriangle D τ) :
    (G.strandTriplePoint D τ).card = 6 := by
  have hmap : (G.strandTriplePoint D τ).map (Function.Embedding.subtype _) =
      τ.image (G.pairOut τ) ∪ τ.image (G.pairIn τ) := by
    ext a
    simp only [mem_map, strandTriplePoint, mem_filter, mem_univ, true_and,
      Function.Embedding.coe_subtype, mem_union, mem_image]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨x, hx, h | h⟩, rfl⟩
      · exact Or.inl ⟨x, hx, h.symm⟩
      · exact Or.inr ⟨x, hx, h.symm⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨⟨_, isStrandSymbol_pairOut hD hτ hx⟩, ⟨x, hx, Or.inl rfl⟩, rfl⟩
      · exact ⟨⟨_, isStrandSymbol_pairIn hG hD hτ hx⟩, ⟨x, hx, Or.inr rfl⟩, rfl⟩
  have hdisj : Disjoint (τ.image (G.pairOut τ)) (τ.image (G.pairIn τ)) := by
    rw [disjoint_left]
    intro a ha ha'
    obtain ⟨x, -, rfl⟩ := mem_image.1 ha
    obtain ⟨y, -, h⟩ := mem_image.1 ha'
    exact pairOut_ne_pairIn τ τ x y h.symm
  rw [← card_map, hmap, card_union_of_disjoint hdisj, card_image_of_injOn (hD.pairOut_injOn hτ),
    card_image_of_injOn (hD.pairIn_injOn hτ), hτ.card_eq]

/-- The face permutation sends `∂_r` to `∂_{r-1}`. -/
theorem strandDiagram_facePerm_bd (r : Fin (2 * b)) :
    (G.strandDiagram hG hD).facePerm ⟨bd r, trivial⟩ = ⟨bd ((finRotate _).symm r), trivial⟩ :=
  Subtype.ext rfl

/-- The involution of the strand diagram sends `∂_r` to `∂'_r`. -/
theorem strandDiagram_inv_bd (r : Fin (2 * b)) :
    (G.strandDiagram hG hD).inv ⟨bd r, trivial⟩ = ⟨bd' r, trivial⟩ :=
  Subtype.ext rfl

/-- The endpoint `ε°(r)` is the cycle of `∂_r`. -/
theorem strandDiagram_endpoint (r : Fin (2 * b)) :
    (G.strandDiagram hG hD).endpoint r = (G.strandDiagram hG hD).vertexOf ⟨bd r, trivial⟩ := by
  rw [TripleData.endpoint, ← (G.strandDiagram hG hD).vertexOf_rot ⟨bd r, trivial⟩,
    strandDiagram_rot_bd]
  rfl

/-- Every boundary vertex of the strand diagram is the cycle of some `∂_r`. -/
theorem strandDiagram_exists_eq_vertexOf_bd {v : Finset (G.StrandDart D)}
    (hv : v ∈ (G.strandDiagram hG hD).boundaryVertices) :
    ∃ r, v = (G.strandDiagram hG hD).vertexOf ⟨bd r, trivial⟩ := by
  set X := G.strandDiagram hG hD
  obtain ⟨hvV, e, he, heB⟩ := X.mem_boundaryVertices.1 hv
  obtain ⟨d, rfl⟩ := X.mem_vertices.1 hvV
  rw [← X.vertexOf_eq_of_mem he]
  rw [mem_strandDiagram_bdry] at heB
  obtain ⟨e, he'⟩ := e
  cases e with
  | bd r => exact ⟨r, rfl⟩
  | bd' r =>
    refine ⟨(finRotate _).symm r, ?_⟩
    rw [← X.vertexOf_rot, strandDiagram_rot_bd']
  | xPlus _ => exact (heB : False).elim
  | xMinus _ => exact (heB : False).elim
  | yPlus _ _ => exact (heB : False).elim
  | yMinus _ _ => exact (heB : False).elim

/-- The internal vertices of the strand diagram are its triple points. -/
theorem mem_strandDiagram_internalVertices {v : Finset (G.StrandDart D)} :
    v ∈ (G.strandDiagram hG hD).internalVertices ↔
      ∃ τ, G.IsDatumTriangle D τ ∧ v = G.strandTriplePoint D τ := by
  set X := G.strandDiagram hG hD
  constructor
  · intro hv
    obtain ⟨hvV, hnb⟩ := X.mem_internalVertices.1 hv
    obtain ⟨a, rfl⟩ := X.mem_vertices.1 hvV
    rcases strandDart_cases hG hD a with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ |
      ⟨τ, p, hτ, hp, rfl⟩ | ⟨τ, p, hτ, hp, rfl⟩
    · exact (hnb ⟨_, X.self_mem_vertexOf _, (mem_strandDiagram_bdry hG hD).2 trivial⟩).elim
    · exact (hnb ⟨_, X.self_mem_vertexOf _, (mem_strandDiagram_bdry hG hD).2 trivial⟩).elim
    · refine (hnb ⟨_, X.rot_mem_vertexOf _, ?_⟩).elim
      rw [strandDiagram_rot_endSymbol, mem_strandDiagram_bdry]
      trivial
    · exact ⟨τ, hτ, strandDiagram_vertexOf_pairOut hG hD hτ hp⟩
    · refine ⟨τ, hτ, ?_⟩
      rw [← strandDiagram_rot_pairOut hG hD hτ hp (isStrandSymbol_pairOut hD hτ hp),
        X.vertexOf_rot, strandDiagram_vertexOf_pairOut hG hD hτ hp]
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨p, hp⟩ : τ.Nonempty := card_pos.1 (by rw [hτ.card_eq]; norm_num)
    rw [← strandDiagram_vertexOf_pairOut hG hD hτ hp]
    refine X.mem_internalVertices.2 ⟨X.vertexOf_mem_vertices _, ?_⟩
    rintro ⟨e, he, heB⟩
    rw [strandDiagram_vertexOf_pairOut hG hD hτ hp] at he
    simp only [strandTriplePoint, mem_filter, mem_univ, true_and] at he
    rw [mem_strandDiagram_bdry] at heB
    obtain ⟨x, -, h | h⟩ := he
    · exact not_isBoundary_pairOut τ x (h ▸ heB)
    · exact not_isBoundary_pairIn τ x (h ▸ heB)

/-- The face permutation of `X°(G, D)` connects `bd 0` to every `bd k`. -/
theorem strandDiagram_sameCycle_bd {k : ℕ} (hk : k < 2 * b) :
    (G.strandDiagram hG hD).facePerm.SameCycle ⟨bd ⟨0, by omega⟩, trivial⟩
      ⟨bd ⟨k, hk⟩, trivial⟩ := by
  induction k with
  | zero => exact .refl _ _
  | succ k ih =>
    refine (ih (by omega)).trans (sameCycle_of_apply_eq ?_).symm
    have hrot : (finRotate (2 * b)).symm ⟨k + 1, hk⟩ = ⟨k, by omega⟩ := by
      rw [Equiv.symm_apply_eq]
      exact Fin.ext (by rw [val_finRotate, if_neg (by simp; omega)])
    rw [strandDiagram_facePerm_bd, hrot]

omit hD in
/-- A dart `bd r` of the strand diagram is never an endpoint-symbol dart. -/
theorem strandDart_bd_ne_endSymbol (r r' : Fin (2 * b)) : (⟨bd r, trivial⟩ : G.StrandDart D) ≠
    ⟨G.endSymbol r', isStrandSymbol_endSymbol hG r'⟩ := fun h =>
  endSymbol_ne_bd r' r (congrArg Subtype.val h).symm

omit hG hD in
/-- The darts `bd r` and `bd' r'` of the strand diagram are distinct. -/
theorem strandDart_bd_ne_bd' (r r' : Fin (2 * b)) :
    (⟨bd r, trivial⟩ : G.StrandDart D) ≠ ⟨bd' r', trivial⟩ := fun h => by
  simpa using congrArg Subtype.val h

omit hD in
/-- An endpoint-symbol dart of the strand diagram is never a dart `bd' r`. -/
theorem strandDart_endSymbol_ne_bd' (r r' : Fin (2 * b)) :
    (⟨G.endSymbol r', isStrandSymbol_endSymbol hG r'⟩ : G.StrandDart D) ≠ ⟨bd' r, trivial⟩ :=
  fun h => endSymbol_ne_bd' r' r (congrArg Subtype.val h)

/-- Every endpoint of `X°(G, D)` has three darts, two of them in the boundary. -/
theorem card_of_mem_strandDiagram_boundaryVertices {v : Finset (G.StrandDart D)}
    (hv : v ∈ (G.strandDiagram hG hD).boundaryVertices) :
    v.card = 3 ∧ (v.filter (· ∈ (G.strandDiagram hG hD).bdry)).card = 2 := by
  obtain ⟨r, rfl⟩ := strandDiagram_exists_eq_vertexOf_bd hG hD hv
  rw [strandDiagram_vertexOf_bd hG hD r]
  refine ⟨?_, ?_⟩
  · rw [card_insert_of_notMem, card_pair (strandDart_endSymbol_ne_bd' hG _ _)]
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨strandDart_bd_ne_endSymbol hG _ _, strandDart_bd_ne_bd' _ _⟩
  · rw [filter_insert,
      if_pos ((mem_strandDiagram_bdry hG hD (a := ⟨bd r, trivial⟩)).2 trivial), filter_insert,
      if_neg (fun h => not_isBoundary_endSymbol r ((mem_strandDiagram_bdry hG hD).1 h)),
      filter_singleton,
      if_pos ((mem_strandDiagram_bdry hG hD (a := ⟨bd' (finRotate _ r), trivial⟩)).2 trivial),
      card_pair (strandDart_bd_ne_bd' _ _)]

/-- The darts `bd r` form a face orbit of `X°(G, D)` that is half of its boundary. -/
theorem exists_faceOrbit_strandDiagram :
    ∃ f ∈ (G.strandDiagram hG hD).faceOrbits, f ⊆ (G.strandDiagram hG hD).bdry ∧
      f ∪ f.map (G.strandDiagram hG hD).inv.toEmbedding = (G.strandDiagram hG hD).bdry ∧
      Disjoint f (f.map (G.strandDiagram hG hD).inv.toEmbedding) := by
  have hb := hG.one_le
  refine ⟨univ.image fun r => (⟨bd r, trivial⟩ : G.StrandDart D), ?_, ?_, ?_, ?_⟩
  · rw [(G.strandDiagram hG hD).mem_faceOrbits]
    refine ⟨⟨bd ⟨0, by omega⟩, trivial⟩, filter_sameCycle_eq (by simp) ?_ ?_⟩
    · intro y hy
      obtain ⟨r, -, rfl⟩ := mem_image.1 hy
      rw [strandDiagram_facePerm_bd]
      exact mem_image_of_mem _ (mem_univ _)
    · intro y hy
      obtain ⟨r, -, rfl⟩ := mem_image.1 hy
      exact strandDiagram_sameCycle_bd hG hD r.isLt
  · intro a ha
    obtain ⟨r, -, rfl⟩ := mem_image.1 ha
    exact (mem_strandDiagram_bdry hG hD).2 trivial
  · ext ⟨a, ha⟩
    rw [mem_union, mem_strandDiagram_bdry, mem_map, mem_image]
    constructor
    · rintro (⟨r, -, h⟩ | ⟨x, hx, h⟩)
      · exact h ▸ trivial
      · obtain ⟨r, -, rfl⟩ := mem_image.1 hx
        rw [← h]
        simp only [Equiv.toEmbedding_apply, strandDiagram_inv_bd]
        trivial
    · intro h
      cases a with
      | bd r => exact Or.inl ⟨r, mem_univ _, rfl⟩
      | bd' r =>
        exact Or.inr ⟨⟨bd r, trivial⟩, mem_image_of_mem _ (mem_univ _),
          strandDiagram_inv_bd hG hD r⟩
      | xPlus _ => exact (h : False).elim
      | xMinus _ => exact (h : False).elim
      | yPlus _ _ => exact (h : False).elim
      | yMinus _ _ => exact (h : False).elim
  · rw [disjoint_left]
    intro a ha ha'
    obtain ⟨r, -, rfl⟩ := mem_image.1 ha
    obtain ⟨x, hx, h⟩ := mem_map.1 ha'
    obtain ⟨r', -, rfl⟩ := mem_image.1 hx
    simp only [Equiv.toEmbedding_apply, strandDiagram_inv_bd] at h
    exact strandDart_bd_ne_bd' _ _ h.symm

/-- The endpoint labelling of `X°(G, D)` is injective. -/
theorem strandDiagram_endpoint_injective :
    Function.Injective (G.strandDiagram hG hD).endpoint := by
  intro r r' h
  rw [strandDiagram_endpoint, strandDiagram_endpoint] at h
  have hm : (⟨bd r, trivial⟩ : G.StrandDart D) ∈
      (G.strandDiagram hG hD).vertexOf ⟨bd r', trivial⟩ :=
    h ▸ (G.strandDiagram hG hD).self_mem_vertexOf _
  rw [strandDiagram_vertexOf_bd hG hD r'] at hm
  simp only [mem_insert, mem_singleton] at hm
  rcases hm with h1 | h1 | h1
  · simpa using congrArg Subtype.val h1
  · exact (strandDart_bd_ne_endSymbol hG _ _ h1).elim
  · exact (strandDart_bd_ne_bd' _ _ h1).elim

/-- Some exterior dart at `ε(r + 1)` of `X°(G, D)` runs to `ε(r)`. -/
theorem exists_exterior_strandDiagram (r : Fin (2 * b)) :
    ∃ d ∈ (G.strandDiagram hG hD).exterior,
      d ∈ (G.strandDiagram hG hD).endpoint (finRotate (2 * b) r) ∧
      (G.strandDiagram hG hD).inv d ∈ (G.strandDiagram hG hD).endpoint r := by
  refine ⟨⟨bd (finRotate _ r), trivial⟩, ?_, ?_, ?_⟩
  · rw [(G.strandDiagram hG hD).mem_exterior, mem_strandDiagram_bdry, mem_strandDiagram_bdry,
      strandDiagram_rot_bd]
    exact ⟨trivial, not_isBoundary_endSymbol _⟩
  · rw [strandDiagram_endpoint]
    exact (G.strandDiagram hG hD).self_mem_vertexOf _
  · rw [strandDiagram_endpoint, strandDiagram_inv_bd, strandDiagram_vertexOf_bd hG hD r]
    simp

/-- The orientation of `X°(G, D)` alternates around each triple point. -/
theorem strandDiagram_isOut_rot (a : G.StrandDart D)
    (ha : ¬(G.strandDiagram hG hD).IsBoundaryVertex ((G.strandDiagram hG hD).vertexOf a)) :
    (G.strandDiagram hG hD).isOut ((G.strandDiagram hG hD).rot a) ≠
      (G.strandDiagram hG hD).isOut a := by
  rcases strandDart_cases hG hD a with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ |
    ⟨τ, p, hτ, hp, rfl⟩ | ⟨τ, p, hτ, hp, rfl⟩
  · exact (ha ⟨_, (G.strandDiagram hG hD).self_mem_vertexOf _,
      (mem_strandDiagram_bdry hG hD).2 trivial⟩).elim
  · exact (ha ⟨_, (G.strandDiagram hG hD).self_mem_vertexOf _,
      (mem_strandDiagram_bdry hG hD).2 trivial⟩).elim
  · refine (ha ⟨_, (G.strandDiagram hG hD).rot_mem_vertexOf _, ?_⟩).elim
    rw [strandDiagram_rot_endSymbol, mem_strandDiagram_bdry]
    trivial
  · rw [strandDiagram_rot_pairOut hG hD hτ hp, strandDiagram_isOut, strandDiagram_isOut]
    simp
  · rw [strandDiagram_rot_pairIn hG hD hτ hp, strandDiagram_isOut, strandDiagram_isOut]
    simp

/-- **The strand diagram is a pre-triple diagram**: for a plabic graph `G` with `b` boundary
vertices and a white datum `D`, `X°(G, D)` is a pre-triple diagram with `b` arcs. -/
@[cluster_algebras "lem_strand_diagram_pre"]
theorem isPreTripleDiagram_strandDiagram : (G.strandDiagram hG hD).IsPreTripleDiagram := by
  have hb := hG.one_le
  refine
    { one_le := hb
      nonempty := ⟨⟨bd ⟨0, by omega⟩, trivial⟩⟩
      inv_involutive := fun a => Subtype.ext (strandInvSym_strandInvSym hG hD a.2)
      inv_ne := ?_
      inv_mem_bdry := ?_
      boundaryVertex_card := fun _ => card_of_mem_strandDiagram_boundaryVertices hG hD
      exists_orbit := exists_faceOrbit_strandDiagram hG hD
      internalVertex_card := ?_
      endDart_notMem_bdry := ?_
      endpoint_mem := ?_
      endpoint_injective := strandDiagram_endpoint_injective hG hD
      exists_endpoint_eq := ?_
      exists_exterior := exists_exterior_strandDiagram hG hD
      isOut_inv := ?_
      isOut_rot := strandDiagram_isOut_rot hG hD
      isOut_source := ?_
      isOut_target := ?_ }
  · rintro ⟨a, ha⟩ h
    have h' := congrArg Subtype.val h
    rw [strandDiagram_inv_apply] at h'
    cases a <;> simp [strandInvSym] at h'
  · rintro ⟨a, ha⟩ h
    rw [mem_strandDiagram_bdry] at h ⊢
    rw [strandDiagram_inv_apply]
    cases a <;> simp_all [strandInvSym, IsBoundary]
  · intro v hv
    obtain ⟨τ, hτ, rfl⟩ := (mem_strandDiagram_internalVertices hG hD).1 hv
    exact card_strandTriplePoint hG hD hτ
  · intro r h
    exact not_isBoundary_endSymbol r ((mem_strandDiagram_bdry hG hD).1 h)
  · intro r
    rw [strandDiagram_endpoint]
    exact (G.strandDiagram hG hD).mem_boundaryVertices.2
      ⟨(G.strandDiagram hG hD).vertexOf_mem_vertices _,
        ⟨_, (G.strandDiagram hG hD).self_mem_vertexOf _, (mem_strandDiagram_bdry hG hD).2 trivial⟩⟩
  · intro v hv
    obtain ⟨r, rfl⟩ := strandDiagram_exists_eq_vertexOf_bd hG hD hv
    exact ⟨r, strandDiagram_endpoint hG hD r⟩
  · rintro ⟨a, ha⟩ h
    rw [mem_strandDiagram_bdry] at h
    rw [strandDiagram_isOut, strandDiagram_isOut, strandDiagram_inv_apply]
    cases a <;> simp_all [strandInvSym, isOut, IsBoundary]
  · intro i
    rw [strandDiagram_isOut, strandDiagram_endDart, endSymbol_sourceIndex]
    rfl
  · intro i
    rw [strandDiagram_isOut, strandDiagram_endDart, endSymbol_targetIndex]
    rfl

/-- **The triple points of the strand diagram are the triangles of the white datum**:
`τ ↦ strandTriplePoint D τ` is a bijection from the triangles of the `D_w` onto the internal
vertices of `X°(G, D)`. -/
@[cluster_algebras "lem_strand_diagram_pre"]
theorem bijOn_strandTriplePoint :
    Set.BijOn (G.strandTriplePoint D) {τ | G.IsDatumTriangle D τ}
      ((G.strandDiagram hG hD).internalVertices : Set (Finset (G.StrandDart D))) := by
  refine ⟨fun τ hτ => (mem_strandDiagram_internalVertices hG hD).2 ⟨τ, hτ, rfl⟩, ?_,
    fun v hv => ?_⟩
  · intro τ hτ τ' hτ' h
    obtain ⟨p, hp⟩ : τ.Nonempty := card_pos.1 (by rw [hτ.card_eq]; norm_num)
    have hm : (⟨G.pairOut τ p, isStrandSymbol_pairOut hD hτ hp⟩ : G.StrandDart D) ∈
        G.strandTriplePoint D τ' := by
      rw [← h]
      simp only [strandTriplePoint, mem_filter, mem_univ, true_and]
      exact ⟨p, hp, Or.inl rfl⟩
    simp only [strandTriplePoint, mem_filter, mem_univ, true_and] at hm
    obtain ⟨x, hx, he | he⟩ := hm
    · unfold pairOut at he
      split_ifs at he with h1 h2 h2
      · obtain rfl := xPlus.inj he
        have hs : G.cornerSide p ∈ τ.sym2 := by
          rw [RotationSystem.cornerSide, ← h1]
          exact mk_mem_sym2_iff.2 ⟨hp, hD.cornerNext_mem hτ hp⟩
        have hs' : G.cornerSide p ∈ τ'.sym2 := by
          rw [RotationSystem.cornerSide, ← h2]
          exact mk_mem_sym2_iff.2 ⟨hx, hD.cornerNext_mem hτ' hx⟩
        exact (hD.eq_sideTriangle hτ hs).trans (hD.eq_sideTriangle hτ' hs').symm
      · exact (yPlus.inj he).2
    · exact (pairOut_ne_pairIn τ τ' p x he).elim
  · obtain ⟨τ, hτ, rfl⟩ := (mem_strandDiagram_internalVertices hG hD).1 hv
    exact ⟨τ, hτ, rfl⟩

end PreTriple

/-! ### Generalized triple diagrams -/

variable (G) in
/-- A **generalized triple diagram** of a plabic graph `G`: a pre-triple diagram `X` such that
every orbit of the trip map of `G` (on `H \ B`) contains an initial dart, and `X` is isomorphic to
the strand diagram `X°(G, D)` of some white datum `D`. -/
@[cluster_algebras "def_generalized_triple_diagram"]
def IsGeneralizedTripleDiagram (hG : G.IsPlabicGraph) {H'' : Type*} [Fintype H'']
    [DecidableEq H''] (X : TripleData H'' b) : Prop :=
  X.IsPreTripleDiagram ∧ (∀ d ∉ G.bdry, ∃ e ∈ G.trip d, G.IsInitial e) ∧
    ∃ D, ∃ hD : G.IsWhiteDatum D, X.Isomorphic (G.strandDiagram hG hD)

end PlabicData

/-! ### Transport along a bijection of darts -/

namespace StrandSymbol

variable {H H' : Type*} {b : ℕ}

/-- The image of a symbol under an embedding of darts. -/
def map (f : H ↪ H') : StrandSymbol H b → StrandSymbol H' b
  | xPlus d => xPlus (f d)
  | xMinus t => xMinus (f t)
  | yPlus s τ => yPlus (s.map f) (τ.map f)
  | yMinus s τ => yMinus (s.map f) (τ.map f)
  | bd r => bd r
  | bd' r => bd' r

/-- Mapping a symbol along `θ` and then along `θ⁻¹` gives it back. -/
theorem map_symm_map (θ : H ≃ H') (a : StrandSymbol H b) :
    (a.map θ.toEmbedding).map θ.symm.toEmbedding = a := by
  have hτ : ∀ τ : Finset H, (τ.map θ.toEmbedding).map θ.symm.toEmbedding = τ := fun τ => by
    ext; simp [Finset.mem_map_equiv]
  cases a <;> simp [map, Sym2.map_map, hτ]

/-- The bijection of symbols induced by a bijection of darts. -/
def mapEquiv (θ : H ≃ H') : StrandSymbol H b ≃ StrandSymbol H' b where
  toFun := map θ.toEmbedding
  invFun := map θ.symm.toEmbedding
  left_inv := map_symm_map θ
  right_inv a := map_symm_map θ.symm a

/-- The bijection `mapEquiv θ` sends a symbol to its image under `θ`. -/
@[simp]
theorem mapEquiv_apply (θ : H ≃ H') (a : StrandSymbol H b) :
    mapEquiv θ a = a.map θ.toEmbedding := rfl

/-- The inverse of `mapEquiv θ` sends a symbol to its image under `θ⁻¹`. -/
@[simp]
theorem mapEquiv_symm_apply (θ : H ≃ H') (a : StrandSymbol H' b) :
    (mapEquiv θ).symm a = a.map θ.symm.toEmbedding := rfl

/-- Mapping a symbol along an embedding preserves its orientation. -/
@[simp]
theorem isOut_map (f : H ↪ H') (a : StrandSymbol H b) : (a.map f).isOut = a.isOut := by
  cases a <;> rfl

/-- A symbol mapped along an embedding is in `B°` if and only if the symbol is. -/
@[simp]
theorem isBoundary_map (f : H ↪ H') (a : StrandSymbol H b) :
    (a.map f).IsBoundary ↔ a.IsBoundary := by
  cases a <;> rfl

end StrandSymbol

namespace PlabicData

open StrandSymbol

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  {D : Finset H → Finset (Sym2 H)}

/-- The white datum `θ(D) = (θ(D_w))_{θ(w)}` transported along a bijection `θ` of darts. -/
def mapDatum {H' : Type*} (θ : H ≃ H') (D : Finset H → Finset (Sym2 H)) :
    Finset H' → Finset (Sym2 H') :=
  fun w' => (D (w'.map θ.symm.toEmbedding)).map θ.toEmbedding.sym2Map

omit [Fintype H] [DecidableEq H] in
/-- The transported white datum at `θ(w)` is `θ(D_w)`. -/
theorem mapDatum_map {H' : Type*} (θ : H ≃ H') (D : Finset H → Finset (Sym2 H)) (w : Finset H) :
    mapDatum θ D (w.map θ.toEmbedding) = (D w).map θ.toEmbedding.sym2Map := by
  have e : (w.map θ.toEmbedding).map θ.symm.toEmbedding = w := by ext; simp [mem_map_equiv]
  rw [mapDatum, e]

omit [Fintype H] [DecidableEq H] in
/-- Transporting a white datum along `θ` and then along `θ⁻¹` gives it back. -/
theorem mapDatum_symm_mapDatum {H' : Type*} (θ : H ≃ H') (D : Finset H → Finset (Sym2 H)) :
    mapDatum θ.symm (mapDatum θ D) = D := by
  funext w
  have e : (w.map θ.symm.symm.toEmbedding).map θ.symm.toEmbedding = w := by
    ext; simp [mem_map_equiv]
  simp only [mapDatum, e]
  ext x
  simp only [mem_map, Function.Embedding.sym2Map_apply, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa [Sym2.map_map] using hz
  · intro hx
    exact ⟨x.map θ, ⟨x, hx, rfl⟩, by simp [Sym2.map_map]⟩

omit [Fintype H] [DecidableEq H] in
/-- `θ(s) ∈ θ(E)` if and only if `s ∈ E`. -/
theorem sym2Map_mem_map_iff {H' : Type*} (θ : H ≃ H') {E : Finset (Sym2 H)} {s : Sym2 H} :
    s.map θ ∈ E.map θ.toEmbedding.sym2Map ↔ s ∈ E := by
  have := Finset.mem_map' (f := θ.toEmbedding.sym2Map) (a := s) (s := E)
  simpa using this

omit [Fintype H] [DecidableEq H] in
/-- `θ(s)` is a pair of elements of `θ(τ)` if and only if `s` is a pair of elements of `τ`. -/
theorem sym2Map_mem_sym2_iff {H' : Type*} (θ : H ≃ H') {τ : Finset H} {s : Sym2 H} :
    s.map θ ∈ (τ.map θ.toEmbedding).sym2 ↔ s ∈ τ.sym2 := by
  induction s using Sym2.ind with
  | _ x y => simp

namespace Iso

variable {H' : Type*} [Fintype H'] [DecidableEq H'] {G' : PlabicData H' b} (θ : G.Iso G')

/-- An isomorphism commutes with `σ⁻¹`. -/
theorem map_rot_symm (d : H) : θ.toEquiv (G.rot.symm d) = G'.rot.symm (θ.toEquiv d) := by
  apply G'.rot.injective
  rw [← θ.map_rot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- An isomorphism commutes with `σ⁻ⁿ`. -/
theorem map_rot_symm_pow (n : ℕ) (d : H) :
    θ.toEquiv ((G.rot.symm ^ n) d) = (G'.rot.symm ^ n) (θ.toEquiv d) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, θ.map_rot_symm, ih, pow_succ',
      Equiv.Perm.mul_apply]

/-- An isomorphism commutes with `Tⁿ`. -/
theorem map_tripMap_iterate (n : ℕ) (d : H) :
    θ.toEquiv (G.tripMap^[n] d) = G'.tripMap^[n] (θ.toEquiv d) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', θ.map_tripMap, ih,
      Function.iterate_succ_apply']

/-- An isomorphism carries clockwise successors to clockwise successors. -/
theorem map_cornerNext (τ : Finset H) (p : H) :
    θ.toEquiv (G.cornerNext τ p) = G'.cornerNext (τ.map θ.toEquiv.toEmbedding) (θ.toEquiv p) := by
  have hP : ∀ k : ℕ, (0 < k ∧ (G'.rot.symm ^ k) (θ.toEquiv p) ∈ τ.map θ.toEquiv.toEmbedding ∧
      (G'.rot.symm ^ k) (θ.toEquiv p) ≠ θ.toEquiv p) ↔
      (0 < k ∧ (G.rot.symm ^ k) p ∈ τ ∧ (G.rot.symm ^ k) p ≠ p) := by
    intro k
    rw [← θ.map_rot_symm_pow, mem_map_equiv, Equiv.symm_apply_apply,
      θ.toEquiv.injective.ne_iff]
  unfold RotationSystem.cornerNext
  by_cases h : ∃ k : ℕ, 0 < k ∧ (G.rot.symm ^ k) p ∈ τ ∧ (G.rot.symm ^ k) p ≠ p
  · have h' : ∃ k : ℕ, 0 < k ∧ (G'.rot.symm ^ k) (θ.toEquiv p) ∈ τ.map θ.toEquiv.toEmbedding ∧
        (G'.rot.symm ^ k) (θ.toEquiv p) ≠ θ.toEquiv p :=
      let ⟨k, hk⟩ := h
      ⟨k, (hP k).2 hk⟩
    rw [dif_pos h, dif_pos h', θ.map_rot_symm_pow]
    congr 2
    exact le_antisymm (Nat.find_min' h ((hP _).1 (Nat.find_spec h')))
      (Nat.find_min' h' ((hP _).2 (Nat.find_spec h)))
  · have h' : ¬∃ k : ℕ, 0 < k ∧ (G'.rot.symm ^ k) (θ.toEquiv p) ∈ τ.map θ.toEquiv.toEmbedding ∧
        (G'.rot.symm ^ k) (θ.toEquiv p) ≠ θ.toEquiv p :=
      fun ⟨k, hk⟩ => h ⟨k, (hP k).1 hk⟩
    rw [dif_neg h, dif_neg h']

/-- An isomorphism carries the side `{p, σ⁻¹ p}` to the side of `θ p`. -/
theorem map_cornerSide (p : H) :
    (G.cornerSide p).map θ.toEquiv = G'.cornerSide (θ.toEquiv p) := by
  simp [RotationSystem.cornerSide, θ.map_rot_symm]

/-- An isomorphism carries crossings to crossings. -/
theorem isCrossing_map {w : Finset H} (hw : G.IsCrossing w) :
    G'.IsCrossing (w.map θ.toEquiv.toEmbedding) := by
  obtain ⟨hint, hcol, hcard⟩ := hw
  obtain ⟨hV, hnb⟩ := G.mem_internalVertices.1 hint
  obtain ⟨d, rfl⟩ := G.mem_vertices.1 hV
  refine ⟨?_, ?_, by rwa [card_map]⟩
  · rw [θ.map_vertexOf]
    exact G'.mem_internalVertices.2 ⟨G'.vertexOf_mem_vertices _,
      (θ.isBoundaryVertex_vertexOf_iff d).not.2 hnb⟩
  · intro e he
    rw [mem_map_equiv] at he
    have hnb' : ¬G.IsBoundaryVertex (G.vertexOf (θ.toEquiv.symm e)) := by
      rwa [G.vertexOf_eq_of_mem he]
    have := θ.map_colour _ hnb'
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact hcol _ he

section IsPlabicGraph

variable (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)

include hG hG'

/-- An isomorphism of plabic graphs carries initial darts to initial darts. -/
theorem isInitial_map {d : H} (hd : G.IsInitial d) : G'.IsInitial (θ.toEquiv d) := by
  refine ⟨fun h => hd.1 ((θ.mem_bdry_iff d).1 h), ?_⟩
  rcases hd.2 with hc | ⟨i, rfl⟩
  · left
    rw [← θ.map_vertexOf]
    exact θ.isCrossing_map hc
  · exact Or.inr ⟨i, (Iso.map_leg hG hG' θ i).symm⟩

omit hG hG' in
/-- An isomorphism carries terminal darts to terminal darts. -/
theorem isTerminal_map {t : H} (ht : G.IsTerminal t) : G'.IsTerminal (θ.toEquiv t) := by
  refine ⟨fun h => ht.1 ((θ.mem_bdry_iff t).1 h), ?_⟩
  rw [← θ.map_inv]
  rcases ht.2 with hc | hb
  · left
    rw [← θ.map_vertexOf]
    exact θ.isCrossing_map hc
  · exact Or.inr ((θ.isBoundaryVertex_vertexOf_iff _).2 hb)

/-- For an isomorphism of plabic graphs, `θ d` is initial if and only if `d` is. -/
theorem isInitial_map_iff {d : H} : G'.IsInitial (θ.toEquiv d) ↔ G.IsInitial d := by
  refine ⟨fun h => ?_, θ.isInitial_map hG hG'⟩
  have := θ.symm.isInitial_map hG' hG h
  rwa [show θ.symm.toEquiv (θ.toEquiv d) = d from θ.toEquiv.symm_apply_apply d] at this

omit hG hG' in
/-- For an isomorphism, `θ t` is terminal if and only if `t` is. -/
theorem isTerminal_map_iff {t : H} : G'.IsTerminal (θ.toEquiv t) ↔ G.IsTerminal t := by
  refine ⟨fun h => ?_, θ.isTerminal_map⟩
  have := θ.symm.isTerminal_map h
  rwa [show θ.symm.toEquiv (θ.toEquiv t) = t from θ.toEquiv.symm_apply_apply t] at this

omit hG hG' in
/-- An isomorphism preserves the length of the chain from a dart. -/
theorem chainLength_map (d : H) : G'.chainLength (θ.toEquiv d) = G.chainLength d := by
  have hT : ∀ m, G'.IsTerminal (G'.tripMap^[m] (θ.toEquiv d)) ↔
      G.IsTerminal (G.tripMap^[m] d) := fun m => by
    rw [← θ.map_tripMap_iterate]
    exact θ.isTerminal_map_iff
  by_cases h : ∃ m, G.IsTerminal (G.tripMap^[m] d)
  · have h' : ∃ m, G'.IsTerminal (G'.tripMap^[m] (θ.toEquiv d)) :=
      let ⟨m, hm⟩ := h
      ⟨m, (hT m).2 hm⟩
    exact le_antisymm (chainLength_le ((hT _).2 (chainLength_spec h)))
      (chainLength_le ((hT _).1 (chainLength_spec h')))
  · have h' : ¬∃ m, G'.IsTerminal (G'.tripMap^[m] (θ.toEquiv d)) :=
      fun ⟨m, hm⟩ => h ⟨m, (hT m).1 hm⟩
    rw [chainLength, dif_neg h', chainLength, dif_neg h]

omit hG hG' in
/-- An isomorphism commutes with `end`. -/
theorem map_chainEnd (d : H) : θ.toEquiv (G.chainEnd d) = G'.chainEnd (θ.toEquiv d) := by
  rw [chainEnd_def, chainEnd_def, θ.chainLength_map, θ.map_tripMap_iterate]

/-- An isomorphism of plabic graphs commutes with the start of the chain ending at a terminal
dart. -/
theorem map_chainStart {t : H} (ht : G.IsTerminal t) :
    θ.toEquiv (G.chainStart t) = G'.chainStart (θ.toEquiv t) := by
  obtain ⟨h1, h2⟩ := ht.chainStart_spec hG
  obtain ⟨h1', h2'⟩ := (θ.isTerminal_map ht).chainStart_spec hG'
  refine chainEnd_injOn hG' (θ.isInitial_map hG hG' h1) h1' ?_
  rw [← θ.map_chainEnd, h2, h2']

end IsPlabicGraph

/-- An isomorphism carries a triangle of `E` at `w` to a triangle of `θ(E)` at `θ(w)`. -/
theorem isCornerTriangle_map {w : Finset H} {E : Finset (Sym2 H)} {τ : Finset H}
    (h : G.IsCornerTriangle w E τ) :
    G'.IsCornerTriangle (w.map θ.toEquiv.toEmbedding) (E.map θ.toEquiv.toEmbedding.sym2Map)
      (τ.map θ.toEquiv.toEmbedding) := by
  obtain ⟨hsub, hcard, hseg⟩ := h
  refine ⟨map_subset_map.2 hsub, by rw [card_map, hcard], ?_⟩
  intro u hu v hv huv
  rw [mem_map_equiv] at hu hv
  have hne : θ.toEquiv.symm u ≠ θ.toEquiv.symm v := θ.toEquiv.symm.injective.ne huv
  have huv' : s(u, v) = s(θ.toEquiv.symm u, θ.toEquiv.symm v).map θ.toEquiv := by simp
  rcases RotationSystem.mem_cornerSegments.1 (hseg _ hu _ hv hne) with hE | ⟨a, ha, he⟩
  · refine RotationSystem.mem_cornerSegments.2 (Or.inl ?_)
    rw [huv']
    exact (sym2Map_mem_map_iff θ.toEquiv).2 hE
  · refine RotationSystem.mem_cornerSegments.2 (Or.inr ⟨θ.toEquiv a, mem_map_of_mem _ ha, ?_⟩)
    rw [← θ.map_cornerSide, he, huv']

/-- An isomorphism carries a corner triangulation `E` of `w` to a corner triangulation `θ(E)` of
`θ(w)`. -/
theorem isCornerTriangulation_map {w : Finset H} {E : Finset (Sym2 H)}
    (h : G.IsCornerTriangulation w E) :
    G'.IsCornerTriangulation (w.map θ.toEquiv.toEmbedding)
      (E.map θ.toEquiv.toEmbedding.sym2Map) := by
  obtain ⟨hE, m, hm, l, hl, hT⟩ := h
  refine ⟨?_, m, hm, θ.toEquiv ∘ l, ⟨?_, fun i => ?_⟩, ?_⟩
  · intro e he
    obtain ⟨e₀, he₀, rfl⟩ := mem_map.1 he
    refine ⟨?_, fun x hx => ?_⟩
    · rw [Function.Embedding.sym2Map_apply, Sym2.isDiag_map θ.toEquiv.toEmbedding.injective]
      exact (hE e₀ he₀).1
    · rw [Function.Embedding.sym2Map_apply, Sym2.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact mem_map_of_mem _ ((hE e₀ he₀).2 y hy)
  · rw [coe_map, Equiv.coe_toEmbedding]
    exact (θ.toEquiv.injective.injOn.bijOn_image).comp hl.1
  · simp only [Function.comp_apply, hl.2 i, θ.map_rot_symm]
  · convert hT using 1
    ext e
    rw [RotationSystem.mem_cornerPullback, RotationSystem.mem_cornerPullback, ← Sym2.map_map]
    exact sym2Map_mem_map_iff θ.toEquiv

/-- An isomorphism carries white data to white data. -/
theorem isWhiteDatum_mapDatum (hD : G.IsWhiteDatum D) :
    G'.IsWhiteDatum (mapDatum θ.toEquiv D) := by
  intro w' hw'
  have hw : G.IsCrossing (w'.map θ.toEquiv.symm.toEmbedding) := θ.symm.isCrossing_map hw'
  have h := θ.isCornerTriangulation_map (hD _ hw)
  have e : (w'.map θ.toEquiv.symm.toEmbedding).map θ.toEquiv.toEmbedding = w' := by
    ext; simp [mem_map_equiv]
  rw [e] at h
  exact h

/-- An isomorphism carries triangles of `D` to triangles of the transported white datum. -/
theorem isDatumTriangle_map {τ : Finset H} (hτ : G.IsDatumTriangle D τ) :
    G'.IsDatumTriangle (mapDatum θ.toEquiv D) (τ.map θ.toEquiv.toEmbedding) := by
  obtain ⟨w, hw, ht⟩ := hτ
  exact ⟨_, θ.isCrossing_map hw, by rw [mapDatum_map]; exact θ.isCornerTriangle_map ht⟩

/-- An isomorphism carries a pair `(s, τ)` indexing `y^±_{s,τ}` for `D` to the pair
`(θ(s), θ(τ))` for the transported white datum. -/
theorem isDatumSegment_map {s : Sym2 H} {τ : Finset H} (h : G.IsDatumSegment D s τ) :
    G'.IsDatumSegment (mapDatum θ.toEquiv D) (s.map θ.toEquiv) (τ.map θ.toEquiv.toEmbedding) := by
  obtain ⟨w, hw, hs, ht, hsτ⟩ := h
  refine ⟨_, θ.isCrossing_map hw, ?_, ?_, (sym2Map_mem_sym2_iff θ.toEquiv).2 hsτ⟩
  · rw [mapDatum_map]; exact (sym2Map_mem_map_iff θ.toEquiv).2 hs
  · rw [mapDatum_map]; exact θ.isCornerTriangle_map ht

/-- An isomorphism carries `pairOut τ p` to `pairOut θ(τ) (θ p)`. -/
theorem map_pairOut (τ : Finset H) (p : H) :
    (G.pairOut τ p).map θ.toEquiv.toEmbedding =
      G'.pairOut (τ.map θ.toEquiv.toEmbedding) (θ.toEquiv p) := by
  have hc : G'.cornerNext (τ.map θ.toEquiv.toEmbedding) (θ.toEquiv p) =
      G'.rot.symm (θ.toEquiv p) ↔ G.cornerNext τ p = G.rot.symm p := by
    rw [← θ.map_cornerNext, ← θ.map_rot_symm, θ.toEquiv.injective.eq_iff]
  unfold pairOut
  by_cases h : G.cornerNext τ p = G.rot.symm p
  · rw [if_pos h, if_pos (hc.2 h)]
    rfl
  · rw [if_neg h, if_neg (hc.not.2 h)]
    simp only [StrandSymbol.map, Sym2.map_mk, Equiv.coe_toEmbedding, θ.map_cornerNext]

/-- An isomorphism carries `pairIn τ p` to `pairIn θ(τ) (θ p)`. -/
theorem map_pairIn (τ : Finset H) (p : H) :
    (G.pairIn τ p).map θ.toEquiv.toEmbedding =
      G'.pairIn (τ.map θ.toEquiv.toEmbedding) (θ.toEquiv p) := by
  have hc : G'.cornerNext (τ.map θ.toEquiv.toEmbedding) (θ.toEquiv p) =
      G'.rot.symm (θ.toEquiv p) ↔ G.cornerNext τ p = G.rot.symm p := by
    rw [← θ.map_cornerNext, ← θ.map_rot_symm, θ.toEquiv.injective.eq_iff]
  unfold pairIn
  by_cases h : G.cornerNext τ p = G.rot.symm p
  · rw [if_pos h, if_pos (hc.2 h)]
    simp only [StrandSymbol.map, Equiv.coe_toEmbedding, θ.map_inv]
  · rw [if_neg h, if_neg (hc.not.2 h)]
    simp only [StrandSymbol.map, Sym2.map_mk, Equiv.coe_toEmbedding, θ.map_cornerNext]

/-- An isomorphism of plabic graphs carries the symbol of the endpoint `ε°(r)` to that of `G'`. -/
theorem map_endSymbol (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (r : Fin (2 * b)) :
    (G.endSymbol r).map θ.toEquiv.toEmbedding = G'.endSymbol r := by
  unfold endSymbol
  split_ifs <;> simp [StrandSymbol.map, Iso.map_leg hG hG' θ, θ.map_inv]

section StrandDiagram

variable (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (hD : G.IsWhiteDatum D)

/-- If `p ∈ τ`, then `θ p ∈ θ(τ)`. -/
theorem mem_map_toEmbedding {τ : Finset H} {p : H} (hp : p ∈ τ) :
    θ.toEquiv p ∈ τ.map θ.toEquiv.toEmbedding :=
  mem_map_equiv.2 (by simpa using hp)

include hD in
/-- For `p` at a crossing, an isomorphism carries the triangle of `D` containing the side of `p`
to the triangle of the transported white datum containing the side of `θ p`. -/
theorem map_sideTriangle {p : H} (hp : G.IsCrossing (G.vertexOf p)) :
    (G.sideTriangle D p).map θ.toEquiv.toEmbedding =
      G'.sideTriangle (mapDatum θ.toEquiv D) (θ.toEquiv p) := by
  obtain ⟨hτ, hs⟩ := hD.sideTriangle_spec hp
  refine (θ.isWhiteDatum_mapDatum hD).eq_sideTriangle (θ.isDatumTriangle_map hτ) ?_
  rw [← θ.map_cornerSide]
  exact (sym2Map_mem_sym2_iff θ.toEquiv).2 hs

include hD in
/-- An isomorphism carries the triangle of `D` other than `τ` containing `s` to the triangle of
the transported white datum other than `θ(τ)` containing `θ(s)`. -/
theorem map_otherTriangle {s : Sym2 H} {τ : Finset H} (h : G.IsDatumSegment D s τ) :
    (G.otherTriangle D s τ).map θ.toEquiv.toEmbedding =
      G'.otherTriangle (mapDatum θ.toEquiv D) (s.map θ.toEquiv) (τ.map θ.toEquiv.toEmbedding) := by
  obtain ⟨ho, hoτ, -⟩ := hD.otherTriangle_spec h
  refine (θ.isWhiteDatum_mapDatum hD).eq_otherTriangle (θ.isDatumSegment_map h)
    (θ.isDatumTriangle_map (.of_isDatumSegment ho)) ?_ fun e => hoτ (Finset.map_injective _ e)
  obtain ⟨-, -, -, -, hso⟩ := ho
  exact (sym2Map_mem_sym2_iff θ.toEquiv).2 hso

include hG hG' in
/-- An isomorphism of plabic graphs carries darts of `X°(G, D)` to darts of `X°(G', θ(D))`. -/
theorem isStrandSymbol_map {a : StrandSymbol H b} (ha : G.IsStrandSymbol D a) :
    G'.IsStrandSymbol (mapDatum θ.toEquiv D) (a.map θ.toEquiv.toEmbedding) := by
  cases a with
  | xPlus d => exact θ.isInitial_map hG hG' (ha : G.IsInitial d)
  | xMinus t => exact θ.isTerminal_map (ha : G.IsTerminal t)
  | yPlus s τ => exact θ.isDatumSegment_map (ha : G.IsDatumSegment D s τ)
  | yMinus s τ => exact θ.isDatumSegment_map (ha : G.IsDatumSegment D s τ)
  | bd r => trivial
  | bd' r => trivial

include hG hG' in
/-- For an isomorphism of plabic graphs, the image of a symbol is a dart of `X°(G', θ(D))` if and
only if the symbol is a dart of `X°(G, D)`. -/
theorem isStrandSymbol_map_iff {a : StrandSymbol H b} :
    G'.IsStrandSymbol (mapDatum θ.toEquiv D) (a.map θ.toEquiv.toEmbedding) ↔
      G.IsStrandSymbol D a := by
  refine ⟨fun h => ?_, θ.isStrandSymbol_map hG hG'⟩
  have := θ.symm.isStrandSymbol_map hG' hG h
  rwa [show θ.symm.toEquiv = θ.toEquiv.symm from rfl, mapDatum_symm_mapDatum,
    StrandSymbol.map_symm_map] at this

/-- The bijection `x^±_d ↦ x^±_{θ d}`, `y^±_{s,τ} ↦ y^±_{θ s, θ τ}`, `∂_r ↦ ∂_r`,
`∂'_r ↦ ∂'_r` of the darts of the strand diagrams of `G` and `G'`. -/
def strandDartEquiv : G.StrandDart D ≃ G'.StrandDart (mapDatum θ.toEquiv D) :=
  (StrandSymbol.mapEquiv θ.toEquiv).subtypeEquiv fun _ => (θ.isStrandSymbol_map_iff hG hG').symm

/-- The bijection of darts of the strand diagrams maps each symbol along `θ`. -/
@[simp]
theorem strandDartEquiv_apply (a : G.StrandDart D) :
    (θ.strandDartEquiv hG hG' a).1 = a.1.map θ.toEquiv.toEmbedding := rfl

include hG hG' hD in
/-- An isomorphism of plabic graphs commutes with the involutions of the strand diagrams on
darts. -/
theorem map_strandInvSym {a : StrandSymbol H b} (ha : G.IsStrandSymbol D a) :
    (G.strandInvSym D a).map θ.toEquiv.toEmbedding =
      G'.strandInvSym (mapDatum θ.toEquiv D) (a.map θ.toEquiv.toEmbedding) := by
  cases a with
  | xPlus d =>
    simp only [strandInvSym, StrandSymbol.map, Equiv.coe_toEmbedding, θ.map_chainEnd]
  | xMinus t =>
    simp only [strandInvSym, StrandSymbol.map, Equiv.coe_toEmbedding,
      θ.map_chainStart hG hG' (ha : G.IsTerminal t)]
  | yPlus s τ =>
    simp only [strandInvSym, StrandSymbol.map, Equiv.coe_toEmbedding,
      θ.map_otherTriangle hD (ha : G.IsDatumSegment D s τ)]
  | yMinus s τ =>
    simp only [strandInvSym, StrandSymbol.map, Equiv.coe_toEmbedding,
      θ.map_otherTriangle hD (ha : G.IsDatumSegment D s τ)]
  | bd r => rfl
  | bd' r => rfl

include hG hG' hD in
/-- An isomorphism of plabic graphs commutes with the rotations of the strand diagrams on
darts. -/
theorem map_strandRotSym {a : StrandSymbol H b} (ha : G.IsStrandSymbol D a) :
    (G.strandRotSym D a).map θ.toEquiv.toEmbedding =
      G'.strandRotSym (mapDatum θ.toEquiv D) (a.map θ.toEquiv.toEmbedding) := by
  have hD' := θ.isWhiteDatum_mapDatum hD
  rcases IsStrandSymbol.cases hG hD ha with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ |
    ⟨τ, p, hτ, hp, rfl⟩ | ⟨τ, p, hτ, hp, rfl⟩
  · rw [strandRotSym_bd, θ.map_endSymbol hG hG']
    rfl
  · rfl
  · rw [strandRotSym_endSymbol hG, θ.map_endSymbol hG hG', strandRotSym_endSymbol hG']
    rfl
  · rw [strandRotSym_pairOut hG hτ hp, θ.map_pairIn, θ.map_pairOut,
      strandRotSym_pairOut hG' (θ.isDatumTriangle_map hτ) (θ.mem_map_toEmbedding hp)]
  · rw [strandRotSym_pairIn hG hD hτ hp, θ.map_pairOut, θ.map_cornerNext, θ.map_cornerNext,
      θ.map_pairIn,
      strandRotSym_pairIn hG' hD' (θ.isDatumTriangle_map hτ) (θ.mem_map_toEmbedding hp)]

/-- **An isomorphism of plabic graphs induces an isomorphism of strand diagrams**
`X°(G, D) → X°(G', θ(D))`. -/
noncomputable def strandDiagramIso :
    (G.strandDiagram hG hD).Iso (G'.strandDiagram hG' (θ.isWhiteDatum_mapDatum hD)) where
  toEquiv := θ.strandDartEquiv hG hG'
  map_inv d := Subtype.ext (θ.map_strandInvSym hG hG' hD d.2)
  map_rot d := Subtype.ext (θ.map_strandRotSym hG hG' hD d.2)
  mem_bdry_iff d := by
    rw [mem_strandDiagram_bdry, mem_strandDiagram_bdry, strandDartEquiv_apply]
    exact StrandSymbol.isBoundary_map _ _
  map_isOut d _ := by
    rw [strandDiagram_isOut, strandDiagram_isOut, strandDartEquiv_apply]
    exact StrandSymbol.isOut_map _ _
  map_endpoint r := by
    rw [strandDiagram_endpoint hG hD, strandDiagram_endpoint hG' (θ.isWhiteDatum_mapDatum hD),
      strandDiagram_vertexOf_bd hG hD, strandDiagram_vertexOf_bd hG' (θ.isWhiteDatum_mapDatum hD)]
    have e1 : θ.strandDartEquiv (D := D) hG hG' ⟨bd r, trivial⟩ = ⟨bd r, trivial⟩ :=
      Subtype.ext rfl
    have e2 : θ.strandDartEquiv (D := D) hG hG' ⟨G.endSymbol r, isStrandSymbol_endSymbol hG r⟩ =
        ⟨G'.endSymbol r, isStrandSymbol_endSymbol hG' r⟩ :=
      Subtype.ext (θ.map_endSymbol hG hG' r)
    have e3 : θ.strandDartEquiv (D := D) hG hG' ⟨bd' (finRotate _ r), trivial⟩ =
        ⟨bd' (finRotate _ r), trivial⟩ := Subtype.ext rfl
    simp only [map_insert, map_singleton, Equiv.coe_toEmbedding, e1, e2, e3]

end StrandDiagram

end Iso

/-- Generalized triple diagrams of `G` are generalized triple diagrams of any graph isomorphic to
`G`. -/
theorem IsGeneralizedTripleDiagram.of_iso {H' : Type*} [Fintype H'] [DecidableEq H']
    {G' : PlabicData H' b} (θ : G.Iso G') (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    {H'' : Type*} [Fintype H''] [DecidableEq H''] {X : TripleData H'' b}
    (h : G.IsGeneralizedTripleDiagram hG X) : G'.IsGeneralizedTripleDiagram hG' X := by
  obtain ⟨hX, horb, D, hD, hiso⟩ := h
  refine ⟨hX, ?_, mapDatum θ.toEquiv D, θ.isWhiteDatum_mapDatum hD,
    hiso.elim fun φ => ⟨φ.trans (θ.strandDiagramIso hG hG' hD)⟩⟩
  intro d' hd'
  have hd : θ.toEquiv.symm d' ∉ G.bdry := by rwa [← θ.mem_bdry_iff, Equiv.apply_symm_apply]
  obtain ⟨e, ⟨n, rfl⟩, he⟩ := horb _ hd
  refine ⟨θ.toEquiv (G.tripMap^[n] (θ.toEquiv.symm d')), ⟨n, ?_⟩, θ.isInitial_map hG hG' he⟩
  rw [θ.map_tripMap_iterate, Equiv.apply_symm_apply]

/-- **Generalized triple diagrams of isomorphic graphs**: if `θ : G → G'` is an isomorphism of
plabic graphs, then `X` is a generalized triple diagram of `G` if and only if it is one of `G'`. -/
@[cluster_algebras "lem_generalized_isomorphism"]
theorem Iso.isGeneralizedTripleDiagram_iff {H' : Type*} [Fintype H'] [DecidableEq H']
    {G' : PlabicData H' b} (θ : G.Iso G') (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    {H'' : Type*} [Fintype H''] [DecidableEq H''] (X : TripleData H'' b) :
    G.IsGeneralizedTripleDiagram hG X ↔ G'.IsGeneralizedTripleDiagram hG' X :=
  ⟨IsGeneralizedTripleDiagram.of_iso θ hG hG', IsGeneralizedTripleDiagram.of_iso θ.symm hG' hG⟩

end PlabicData

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap

/-!
# The bridge graph of a sequence of pairs

Let `b ≥ 1`, let `s = ((i₁, j₁), …, (i_r, j_r))` be a finite sequence of pairs of integers with
`1 ≤ i_t < j_t ≤ b`, and let `γ : [1, b] → {white, black}`. The *bridge graph* `G(s, γ)` is the
plabic graph drawn as follows: the boundary vertices `1, …, b` lie on the top side of the disk from
left to right; for every `x ∈ [1, b]` a vertical *line* hangs down from the boundary vertex `x`;
the `t`-th pair gives a horizontal *bridge*, below those of the earlier pairs, joining a white
vertex on the line of `i_t` (its left end) to a black vertex on the line of `j_t` (its right end);
a line ends at its lowest bridge, and a boundary vertex lying in no pair carries a lollipop of
colour `γ(x)`.

For `x ∈ [1, b]` let `P_x = {t ∈ [1, r] : x ∈ {i_t, j_t}}`, the heights of the bridges ending on
the line of `x`; `x` is a *lollipop position* if `P_x = ∅` and a *line position* otherwise. For a
line position, `m_x = max P_x` is the height of the lowest vertex of the line, and `nx_x(u)` is
the least element of `P_x` greater than `u`. The darts are the boundary arcs `e_x`, `ē_x`, the legs
`g_x` and lollipop darts `λ_x`, the bridge darts `c_t`, `c̄_t`, and the segments `dn_{x,u}`,
`up_{x,u}` of the lines leaving the vertex at height `u` downwards and upwards; the involution
pairs `dn_{x,u}` with `up_{x, nx_x(u)}`.

This file constructs `G(s, γ)` as an explicit `PlabicData` on an explicit finite type of darts,
computably, so that small cases can be evaluated by `decide`, together with the formulas for its
rotation, involution and colouring, the keys of its darts, and the darts arriving at a crossing.

## Main definitions

* `ClusterAlgebras.BridgeSymbol`: the symbols naming the darts of a bridge graph.
* `ClusterAlgebras.BridgeGraph.heights`, `BridgeGraph.top`, `BridgeGraph.next`,
  `BridgeGraph.prev`: the sets `P_x`, the heights `m_x`, the maps `nx_x` and their inverses `pv_x`.
* `ClusterAlgebras.BridgeDart`: the darts of `G(s, γ)`, the symbols satisfying
  `BridgeSymbol.IsDart`.
* `ClusterAlgebras.bridgeGraph`: the bridge graph `G(s, γ)`.
* `ClusterAlgebras.BridgeDart.key`: the key of a dart.

## Main results

* `ClusterAlgebras.bridgeGraph_inv_mem_crossing_iff`: the darts whose reverses lie at the white
  end of a bridge that is not the lowest one on its line.

## Implementation notes

* **Labels and heights.** Boundary labels are `Fin b`, `0`-indexed: `x : Fin b` is FWZ's
  label `x + 1`, so `x` is an end of the `t`-th pair when `(x : ℤ) + 1 ∈ {i_t, j_t}`, and
  FWZ's `x + 1` modulo `b` is `finRotate b x`. Heights and indices of pairs are natural numbers,
  `1`-indexed as in FWZ: the `t`-th pair `BridgeGraph.pair s t` is `s[t - 1]`, and the
  height `0` is that of the boundary vertices.
* **Darts.** A dart is a `BridgeSymbol b` satisfying `BridgeSymbol.IsDart s`: `e_x` is `bdry x`,
  `ē_x` is `bdryRev x`, `λ_x` is `lam x`, `dn_{x,u}` is `dn x u`, `up_{x,u}` is `up x u`, `c_t`
  is `bridge t` and `c̄_t` is `bridgeRev t`. The leg `g_x` is `dn x 0` for every `x`, as FWZ
  put `g_x = dn_{x,0}` at a line position; at a lollipop position `dn x 0` is FWZ's `g_x`.
* **No hypotheses on the pairs.** FWZ assume `1 ≤ i_t < j_t ≤ b`. The construction is made
  total: the rotation sends `c_t` to `up_{x,t}` for the label `x` with `x + 1 = i_t` if there is
  one, and `c̄_t` to the dart below or above the vertex at height `t` on the line of the label `y`
  with `y + 1 = j_t ≠ i_t` if there is one, fixing the bridge dart otherwise. Under FWZ's
  hypotheses these are FWZ's rules, and in all cases the rotation and the involution are
  permutations of the darts, so `bridgeGraph b s γ` is defined for every list `s`. The colour of a
  dart at a boundary vertex, which is irrelevant, is white.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160, Section 7.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Symbols and the lines of a bridge graph -/

/-- The symbols naming the darts of a bridge graph with `b` boundary vertices: `bdry x` is the
boundary arc `e_x`, `bdryRev x` is `ē_x`, `lam x` is the lollipop dart `λ_x`, `dn x u` and `up x u`
are the segments `dn_{x,u}`, `up_{x,u}` of the line of `x` leaving the vertex at height `u`
downwards and upwards (`dn x 0` is the leg `g_x`), and `bridge t`, `bridgeRev t` are the darts
`c_t`, `c̄_t` of the `t`-th bridge. Labels are `0`-indexed: `x : Fin b` is the label `x + 1`. -/
inductive BridgeSymbol (b : ℕ) : Type
  /-- The boundary arc `e_x`, from the boundary vertex `x` to `x - 1`. -/
  | bdry (x : Fin b)
  /-- The boundary arc `ē_x`, the reverse of `e_x`. -/
  | bdryRev (x : Fin b)
  /-- The dart `λ_x` of the lollipop at `x`. -/
  | lam (x : Fin b)
  /-- The segment `dn_{x,u}` of the line of `x`, leaving the vertex at height `u` downwards. -/
  | dn (x : Fin b) (u : ℕ)
  /-- The segment `up_{x,u}` of the line of `x`, leaving the vertex at height `u` upwards. -/
  | up (x : Fin b) (u : ℕ)
  /-- The bridge `c_t`, from its white end to its black end. -/
  | bridge (t : ℕ)
  /-- The bridge `c̄_t`, from its black end to its white end. -/
  | bridgeRev (t : ℕ)
  deriving DecidableEq

namespace BridgeGraph

variable {b : ℕ} (s : List (ℤ × ℤ))

/-- The `t`-th pair `(i_t, j_t)` of `s`, `1`-indexed: `s[t - 1]` for `t ∈ [1, r]`. -/
def pair (t : ℕ) : ℤ × ℤ := s.getD (t - 1) (0, 0)

/-- The set `P_x` of the indices `t ∈ [1, r]` whose pair contains the label `x + 1` of `x`: the
heights of the bridge ends on the line of `x`. -/
def heights (x : Fin b) : Finset ℕ :=
  (Icc 1 s.length).filter fun t => (x : ℤ) + 1 = (pair s t).1 ∨ (x : ℤ) + 1 = (pair s t).2

/-- The height `m_x = max P_x` of the lowest vertex on the line of `x`; it is `0` at a lollipop
position. -/
def top (x : Fin b) : ℕ := (heights s x).sup id

/-- `nx_x(u)`: the least element of `P_x` greater than `u` (`0` if there is none). -/
def next (x : Fin b) (u : ℕ) : ℕ :=
  if h : ((heights s x).filter (u < ·)).Nonempty then ((heights s x).filter (u < ·)).min' h
  else 0

/-- `pv_x(u)`: the greatest element of `{0} ∪ P_x` less than `u`; for `u ∈ P_x` this is the
inverse of `nx_x`. -/
def prev (x : Fin b) (u : ℕ) : ℕ := ((heights s x).filter (· < u)).sup id

/-- The label `x : Fin b` with `x + 1 = i`, if `i ∈ [1, b]`. -/
def label? (b : ℕ) (i : ℤ) : Option (Fin b) :=
  if h : 1 ≤ i ∧ i ≤ b then some ⟨(i - 1).toNat, by omega⟩ else none

/-- The label of the left end `i_t` of the `t`-th pair, if it is one. -/
def leftEnd (b : ℕ) (t : ℕ) : Option (Fin b) := label? b (pair s t).1

/-- The label of the right end `j_t` of the `t`-th pair, if it is one and differs from `i_t`. -/
def rightEnd (b : ℕ) (t : ℕ) : Option (Fin b) :=
  if (pair s t).1 = (pair s t).2 then none else label? b (pair s t).2

variable {s}

/-- `t ∈ P_x` if and only if `t ∈ [1, r]` and the label `x + 1` is one of the ends of the `t`-th
pair. -/
theorem mem_heights {x : Fin b} {t : ℕ} :
    t ∈ heights s x ↔ 1 ≤ t ∧ t ≤ s.length ∧
      ((x : ℤ) + 1 = (pair s t).1 ∨ (x : ℤ) + 1 = (pair s t).2) := by
  simp [heights, and_assoc]

/-- Every element of `P_x` is positive. -/
theorem pos_of_mem_heights {x : Fin b} {t : ℕ} (h : t ∈ heights s x) : 0 < t :=
  (mem_heights.1 h).1

/-- Every element of `P_x` is at most the length `r` of `s`. -/
theorem le_length_of_mem_heights {x : Fin b} {t : ℕ} (h : t ∈ heights s x) : t ≤ s.length :=
  (mem_heights.1 h).2.1

/-- Every element of `P_x` is at most `m_x`. -/
theorem le_top {x : Fin b} {t : ℕ} (h : t ∈ heights s x) : t ≤ top s x :=
  le_sup (f := id) h

/-- At a line position `x`, the height `m_x` lies in `P_x`. -/
theorem top_mem {x : Fin b} (h : (heights s x).Nonempty) : top s x ∈ heights s x := by
  obtain ⟨t, ht, he⟩ := exists_mem_eq_sup _ h id
  rw [top, he]
  exact ht

/-- `u < m_x` if and only if some element of `P_x` is greater than `u`. -/
theorem lt_top_iff {x : Fin b} {u : ℕ} : u < top s x ↔ ∃ t ∈ heights s x, u < t := by
  simp [top]

/-- `m_x = 0` if and only if `x` is a lollipop position, that is, `P_x = ∅`. -/
theorem top_eq_zero_iff {x : Fin b} : top s x = 0 ↔ heights s x = ∅ := by
  refine ⟨fun h => eq_empty_iff_forall_notMem.2 fun t ht => ?_, fun h => by simp [top, h]⟩
  have := le_top ht
  have := pos_of_mem_heights ht
  omega

/-- `m_x > 0` if and only if `x` is a line position, that is, `P_x` is nonempty. -/
theorem top_pos_iff {x : Fin b} : 0 < top s x ↔ (heights s x).Nonempty := by
  rw [Nat.pos_iff_ne_zero, Ne, top_eq_zero_iff, ← ne_eq, nonempty_iff_ne_empty]

/-- For `u < m_x`, `nx_x(u)` is an element of `P_x` greater than `u`. -/
theorem next_spec {x : Fin b} {u : ℕ} (h : u < top s x) :
    next s x u ∈ heights s x ∧ u < next s x u := by
  have hne : ((heights s x).filter (u < ·)).Nonempty := by
    obtain ⟨t, ht, hut⟩ := lt_top_iff.1 h
    exact ⟨t, mem_filter.2 ⟨ht, hut⟩⟩
  rw [next, dif_pos hne]
  exact mem_filter.1 (min'_mem _ hne)

/-- For `u < m_x`, `nx_x(u)` lies in `P_x`. -/
theorem next_mem {x : Fin b} {u : ℕ} (h : u < top s x) : next s x u ∈ heights s x :=
  (next_spec h).1

/-- For `u < m_x`, `u < nx_x(u)`. -/
theorem lt_next {x : Fin b} {u : ℕ} (h : u < top s x) : u < next s x u :=
  (next_spec h).2

/-- `nx_x(u)` is at most every element of `P_x` greater than `u`. -/
theorem next_le {x : Fin b} {u t : ℕ} (ht : t ∈ heights s x) (hut : u < t) : next s x u ≤ t := by
  have hne : ((heights s x).filter (u < ·)).Nonempty := ⟨t, mem_filter.2 ⟨ht, hut⟩⟩
  rw [next, dif_pos hne]
  exact min'_le _ _ (mem_filter.2 ⟨ht, hut⟩)

/-- `pv_x(u)` lies in `{0} ∪ P_x`. -/
theorem prev_eq_zero_or_mem (x : Fin b) (u : ℕ) : prev s x u = 0 ∨ prev s x u ∈ heights s x := by
  rcases ((heights s x).filter (· < u)).eq_empty_or_nonempty with h | h
  · left
    simp [prev, h]
  · right
    obtain ⟨t, ht, he⟩ := exists_mem_eq_sup _ h id
    rw [prev, he]
    exact (mem_filter.1 ht).1

/-- For `u > 0`, `pv_x(u) < u`. -/
theorem prev_lt {x : Fin b} {u : ℕ} (hu : 0 < u) : prev s x u < u := by
  rw [prev, Finset.sup_lt_iff hu]
  intro t ht
  exact (mem_filter.1 ht).2

/-- Every element of `P_x` less than `u` is at most `pv_x(u)`. -/
theorem le_prev {x : Fin b} {u t : ℕ} (ht : t ∈ heights s x) (htu : t < u) : t ≤ prev s x u :=
  le_sup (f := id) (mem_filter.2 ⟨ht, htu⟩)

/-- For `u ∈ P_x`, `pv_x(u) < m_x`. -/
theorem prev_lt_top {x : Fin b} {u : ℕ} (hu : u ∈ heights s x) : prev s x u < top s x :=
  (prev_lt (pos_of_mem_heights hu)).trans_le (le_top hu)

/-- `pv_x ∘ nx_x` is the identity on `({0} ∪ P_x) \ {m_x}`. -/
theorem prev_next {x : Fin b} {u : ℕ} (hu : u = 0 ∨ u ∈ heights s x) (h : u < top s x) :
    prev s x (next s x u) = u := by
  obtain ⟨hm, hlt⟩ := next_spec h
  apply le_antisymm
  · rw [prev, Finset.sup_le_iff]
    intro t ht
    obtain ⟨ht, htn⟩ := mem_filter.1 ht
    by_contra hut
    have := next_le ht (by simpa using hut)
    omega
  · rcases hu with rfl | hu
    · exact Nat.zero_le _
    · exact le_prev hu hlt

/-- `nx_x ∘ pv_x` is the identity on `P_x`. -/
theorem next_prev {x : Fin b} {u : ℕ} (hu : u ∈ heights s x) : next s x (prev s x u) = u := by
  obtain ⟨hm, hlt⟩ := next_spec (prev_lt_top hu)
  apply le_antisymm (next_le hu (prev_lt (pos_of_mem_heights hu)))
  by_contra h
  have := le_prev (u := u) hm (by omega)
  omega

/-- `label? b i = some x` if and only if `x + 1 = i`. -/
theorem label?_eq_some {i : ℤ} {x : Fin b} : label? b i = some x ↔ (x : ℤ) + 1 = i := by
  unfold label?
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff]
    omega
  · simp only [false_iff]
    intro hx
    have := x.isLt
    omega

/-- The left end of the `t`-th pair is the label of `x` if and only if `x + 1 = i_t`. -/
theorem leftEnd_eq_some {t : ℕ} {x : Fin b} :
    leftEnd s b t = some x ↔ (x : ℤ) + 1 = (pair s t).1 :=
  label?_eq_some

/-- The right end of the `t`-th pair is the label of `x` if and only if `x + 1 = j_t` and
`x + 1 ≠ i_t`. -/
theorem rightEnd_eq_some {t : ℕ} {x : Fin b} :
    rightEnd s b t = some x ↔ (x : ℤ) + 1 = (pair s t).2 ∧ (x : ℤ) + 1 ≠ (pair s t).1 := by
  unfold rightEnd
  split_ifs with h
  · simp only [false_iff, not_and, not_not]
    intro hx
    rw [hx, h]
  · rw [label?_eq_some]
    exact ⟨fun hx => ⟨hx, fun h' => h (h'.symm.trans hx)⟩, And.left⟩

/-- If `t ∈ P_x` and `x + 1 ≠ i_t`, then `x` is the right end of the `t`-th pair. -/
theorem rightEnd_eq_some_of_mem_heights {t : ℕ} {x : Fin b} (ht : t ∈ heights s x)
    (hx : (x : ℤ) + 1 ≠ (pair s t).1) : rightEnd s b t = some x :=
  rightEnd_eq_some.2 ⟨(mem_heights.1 ht).2.2.resolve_left hx, hx⟩

/-- For `t ∈ [1, r]`, the `t`-th pair is `s[t - 1]`. -/
theorem pair_eq_getElem {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ s.length) :
    pair s t = s[t - 1] := by
  rw [pair, List.getD_eq_getElem _ _ (by omega)]

/-- Every integer of `[1, b]` is the label `x + 1` of some `x : Fin b`. -/
theorem exists_label_eq {i : ℤ} (h : 1 ≤ i ∧ i ≤ b) : ∃ x : Fin b, (x : ℤ) + 1 = i := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (show (label? b i).isSome by simp [label?, h])
  exact ⟨x, label?_eq_some.1 hx⟩

/-- If every pair `(i_t, j_t)` of `s` satisfies `1 ≤ i_t < j_t ≤ b`, then the ends of the `t`-th
pair are labels, the left one is less than the right one, and `t` lies in `P_{i_t}` and in
`P_{j_t}`. -/
theorem exists_ends (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) {t : ℕ} (h1 : 1 ≤ t)
    (h2 : t ≤ s.length) :
    ∃ x y : Fin b, (x : ℤ) + 1 = (pair s t).1 ∧ (y : ℤ) + 1 = (pair s t).2 ∧ x < y ∧
      t ∈ heights s x ∧ t ∈ heights s y := by
  have hp := hs _ (pair_eq_getElem h1 h2 ▸ List.getElem_mem (by omega))
  obtain ⟨x, hx⟩ := exists_label_eq (b := b) ⟨hp.1, by omega⟩
  obtain ⟨y, hy⟩ := exists_label_eq (b := b) ⟨by omega, hp.2.2⟩
  refine ⟨x, y, hx, hy, ?_, mem_heights.2 ⟨h1, h2, Or.inl hx⟩, mem_heights.2 ⟨h1, h2, Or.inr hy⟩⟩
  rw [Fin.lt_def]
  omega

end BridgeGraph

/-! ### The rotation, the involution and the colouring on symbols -/

namespace BridgeSymbol

open BridgeGraph

variable {b : ℕ} (s : List (ℤ × ℤ))

/-- The symbols that are darts of the bridge graph of `s`: all boundary arcs `e_x`, `ē_x`; `λ_x`
for a lollipop position `x`; `dn_{x,u}` for `u ∈ ({0} ∪ P_x) \ {m_x}` (with `dn_{x,0} = g_x` at
every `x`); `up_{x,u}` for `u ∈ P_x`; and `c_t`, `c̄_t` for `t ∈ [1, r]`. -/
def IsDart : BridgeSymbol b → Prop
  | .bdry _ => True
  | .bdryRev _ => True
  | .lam x => heights s x = ∅
  | .dn x u => u = 0 ∨ (u ∈ heights s x ∧ u < top s x)
  | .up x u => u ∈ heights s x
  | .bridge t => 1 ≤ t ∧ t ≤ s.length
  | .bridgeRev t => 1 ≤ t ∧ t ≤ s.length

/-- Being a dart of the bridge graph of `s` is decidable. -/
instance : DecidablePred (IsDart (b := b) s) := fun d => by
  cases d <;> unfold IsDart <;> infer_instance

/-- The rotation `σ` of the bridge graph on symbols: `g_x ↦ ē_{x+1} ↦ e_x ↦ g_x`; `λ_x ↦ λ_x`;
at the white end of the `t`-th bridge (on the line of `i_t`)
`up_{i_t,t} ↦ dn_{i_t,t} ↦ c_t ↦ up_{i_t,t}`, or `up_{i_t,t} ↦ c_t ↦ up_{i_t,t}` if `t = m_{i_t}`;
at its black end (on the line of `j_t`) `up_{j_t,t} ↦ c̄_t ↦ dn_{j_t,t} ↦ up_{j_t,t}`, or
`up_{j_t,t} ↦ c̄_t ↦ up_{j_t,t}` if `t = m_{j_t}`. -/
def rotate : BridgeSymbol b → BridgeSymbol b
  | .bdry x => .dn x 0
  | .bdryRev y => .bdry ((finRotate b).symm y)
  | .lam x => .lam x
  | .dn x 0 => .bdryRev (finRotate b x)
  | .dn x (u + 1) =>
    if (x : ℤ) + 1 = (pair s (u + 1)).1 then .bridge (u + 1) else .up x (u + 1)
  | .up x u =>
    if (x : ℤ) + 1 = (pair s u).1 then (if u < top s x then .dn x u else .bridge u)
    else .bridgeRev u
  | .bridge t =>
    match leftEnd s b t with
    | some x => .up x t
    | none => .bridge t
  | .bridgeRev t =>
    match rightEnd s b t with
    | some y => if t < top s y then .dn y t else .up y t
    | none => .bridgeRev t

/-- The inverse `σ⁻¹` of the rotation of the bridge graph on symbols. -/
def rotateInv : BridgeSymbol b → BridgeSymbol b
  | .bdry x => .bdryRev (finRotate b x)
  | .bdryRev y => .dn ((finRotate b).symm y) 0
  | .lam x => .lam x
  | .dn x 0 => .bdry x
  | .dn x (u + 1) =>
    if (x : ℤ) + 1 = (pair s (u + 1)).1 then .up x (u + 1) else .bridgeRev (u + 1)
  | .up x u =>
    if (x : ℤ) + 1 = (pair s u).1 then .bridge u
    else if u < top s x then .dn x u else .bridgeRev u
  | .bridge t =>
    match leftEnd s b t with
    | some x => if t < top s x then .dn x t else .up x t
    | none => .bridge t
  | .bridgeRev t =>
    match rightEnd s b t with
    | some y => .up y t
    | none => .bridgeRev t

/-- The involution `d ↦ d̄` of the bridge graph on symbols: `e_x ↔ ē_x`, `g_x ↔ λ_x` at a
lollipop position, `c_t ↔ c̄_t`, and `dn_{x,u} ↔ up_{x, nx_x(u)}`. -/
def reverse : BridgeSymbol b → BridgeSymbol b
  | .bdry x => .bdryRev x
  | .bdryRev x => .bdry x
  | .lam x => .dn x 0
  | .dn x u => if u < top s x then .up x (next s x u) else .lam x
  | .up x u => .dn x (prev s x u)
  | .bridge t => .bridgeRev t
  | .bridgeRev t => .bridge t

/-- The colour of the vertex of a symbol: white at the white end of a bridge, black at its black
end, `γ(x)` at the lollipop of `x`, and (irrelevantly) white at the boundary vertices. -/
def colour (γ : Fin b → Shade) : BridgeSymbol b → Shade
  | .lam x => γ x
  | .dn x u => if u ≠ 0 ∧ (x : ℤ) + 1 ≠ (pair s u).1 then .black else .white
  | .up x u => if (x : ℤ) + 1 = (pair s u).1 then .white else .black
  | .bridgeRev _ => .black
  | _ => .white

/-- A symbol is a **boundary arc** if it is some `e_x` or `ē_x`. -/
def IsBoundaryArc : BridgeSymbol b → Prop
  | .bdry _ => True
  | .bdryRev _ => True
  | _ => False

/-- Being a boundary arc is decidable. -/
instance : DecidablePred (IsBoundaryArc (b := b)) := fun d => by
  cases d <;> unfold IsBoundaryArc <;> infer_instance

variable {s}

/-- `σ(e_x) = g_x`. -/
@[simp] theorem rotate_bdry (x : Fin b) : rotate s (.bdry x) = .dn x 0 := rfl
/-- `σ(ē_y) = e_{y-1}`. -/
@[simp] theorem rotate_bdryRev (y : Fin b) :
    rotate s (.bdryRev y) = .bdry ((finRotate b).symm y) := rfl
/-- `σ(λ_x) = λ_x`. -/
@[simp] theorem rotate_lam (x : Fin b) : rotate s (.lam x) = .lam x := rfl
/-- `σ(g_x) = ē_{x+1}`. -/
@[simp] theorem rotate_dn_zero (x : Fin b) : rotate s (.dn x 0) = .bdryRev (finRotate b x) := rfl

/-- For `u ≠ 0`, `σ(dn_{x,u})` is `c_u` if `x + 1 = i_u` and `up_{x,u}` otherwise. -/
theorem rotate_dn_of_ne_zero {x : Fin b} {u : ℕ} (hu : u ≠ 0) :
    rotate s (.dn x u) = if (x : ℤ) + 1 = (pair s u).1 then .bridge u else .up x u := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu
  rfl

/-- `σ(up_{x,u})` is `dn_{x,u}` if `x + 1 = i_u` and `u < m_x`, `c_u` if `x + 1 = i_u` and
`u = m_x`, and `c̄_u` otherwise. -/
theorem rotate_up (x : Fin b) (u : ℕ) : rotate s (.up x u) =
    if (x : ℤ) + 1 = (pair s u).1 then (if u < top s x then .dn x u else .bridge u)
    else .bridgeRev u := rfl

/-- If `x + 1 = i_t`, then `σ(c_t) = up_{x,t}`. -/
theorem rotate_bridge_of_eq {t : ℕ} {x : Fin b} (hx : (x : ℤ) + 1 = (pair s t).1) :
    rotate s (.bridge t) = .up x t := by
  simp only [rotate, leftEnd_eq_some.2 hx]

/-- If `y + 1 = j_t ≠ i_t`, then `σ(c̄_t)` is `dn_{y,t}` if `t < m_y` and `up_{y,t}` otherwise. -/
theorem rotate_bridgeRev_of_eq {t : ℕ} {y : Fin b} (hy : (y : ℤ) + 1 = (pair s t).2)
    (hne : (pair s t).1 ≠ (pair s t).2) :
    rotate s (.bridgeRev t) = if t < top s y then .dn y t else .up y t := by
  simp only [rotate, rightEnd_eq_some.2 ⟨hy, fun h => hne (h.symm.trans hy)⟩]

/-- `σ⁻¹(e_x) = ē_{x+1}`. -/
@[simp] theorem rotateInv_bdry (x : Fin b) : rotateInv s (.bdry x) = .bdryRev (finRotate b x) :=
  rfl
/-- `σ⁻¹(ē_y) = g_{y-1}`. -/
@[simp] theorem rotateInv_bdryRev (y : Fin b) :
    rotateInv s (.bdryRev y) = .dn ((finRotate b).symm y) 0 := rfl
/-- `σ⁻¹(λ_x) = λ_x`. -/
@[simp] theorem rotateInv_lam (x : Fin b) : rotateInv s (.lam x) = .lam x := rfl
/-- `σ⁻¹(g_x) = e_x`. -/
@[simp] theorem rotateInv_dn_zero (x : Fin b) : rotateInv s (.dn x 0) = .bdry x := rfl

/-- For `u ≠ 0`, `σ⁻¹(dn_{x,u})` is `up_{x,u}` if `x + 1 = i_u` and `c̄_u` otherwise. -/
theorem rotateInv_dn_of_ne_zero {x : Fin b} {u : ℕ} (hu : u ≠ 0) :
    rotateInv s (.dn x u) = if (x : ℤ) + 1 = (pair s u).1 then .up x u else .bridgeRev u := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu
  rfl

/-- `σ⁻¹(up_{x,u})` is `c_u` if `x + 1 = i_u`, and otherwise `dn_{x,u}` if `u < m_x` and `c̄_u`
if not. -/
theorem rotateInv_up (x : Fin b) (u : ℕ) : rotateInv s (.up x u) =
    if (x : ℤ) + 1 = (pair s u).1 then .bridge u
    else if u < top s x then .dn x u else .bridgeRev u := rfl

/-- If `x + 1 = i_t`, then `σ⁻¹(c_t)` is `dn_{x,t}` if `t < m_x` and `up_{x,t}` otherwise. -/
theorem rotateInv_bridge_of_eq {t : ℕ} {x : Fin b} (hx : (x : ℤ) + 1 = (pair s t).1) :
    rotateInv s (.bridge t) = if t < top s x then .dn x t else .up x t := by
  simp only [rotateInv, leftEnd_eq_some.2 hx]

/-- If `y + 1 = j_t ≠ i_t`, then `σ⁻¹(c̄_t) = up_{y,t}`. -/
theorem rotateInv_bridgeRev_of_eq {t : ℕ} {y : Fin b} (hy : (y : ℤ) + 1 = (pair s t).2)
    (hne : (pair s t).1 ≠ (pair s t).2) : rotateInv s (.bridgeRev t) = .up y t := by
  simp only [rotateInv, rightEnd_eq_some.2 ⟨hy, fun h => hne (h.symm.trans hy)⟩]

/-- The reverse of `e_x` is `ē_x`. -/
@[simp] theorem reverse_bdry (x : Fin b) : reverse s (.bdry x) = .bdryRev x := rfl
/-- The reverse of `ē_x` is `e_x`. -/
@[simp] theorem reverse_bdryRev (x : Fin b) : reverse s (.bdryRev x) = .bdry x := rfl
/-- The reverse of `λ_x` is `g_x`. -/
@[simp] theorem reverse_lam (x : Fin b) : reverse s (.lam x) = .dn x 0 := rfl
/-- The reverse of `dn_{x,u}` is `up_{x, nx_x(u)}` if `u < m_x` and `λ_x` otherwise. -/
theorem reverse_dn (x : Fin b) (u : ℕ) :
    reverse s (.dn x u) = if u < top s x then .up x (next s x u) else .lam x := rfl
/-- The reverse of `up_{x,u}` is `dn_{x, pv_x(u)}`. -/
@[simp] theorem reverse_up (x : Fin b) (u : ℕ) : reverse s (.up x u) = .dn x (prev s x u) := rfl
/-- The reverse of `c_t` is `c̄_t`. -/
@[simp] theorem reverse_bridge (t : ℕ) : reverse (b := b) s (.bridge t) = .bridgeRev t := rfl
/-- The reverse of `c̄_t` is `c_t`. -/
@[simp] theorem reverse_bridgeRev (t : ℕ) : reverse (b := b) s (.bridgeRev t) = .bridge t := rfl

/-- For `u < m_x`, the reverse of `dn_{x,u}` is `up_{x, nx_x(u)}`. -/
theorem reverse_dn_of_lt_top {x : Fin b} {u : ℕ} (h : u < top s x) :
    reverse s (.dn x u) = .up x (next s x u) := if_pos h

/-- Every `e_x` is a dart. -/
@[simp] theorem isDart_bdry (x : Fin b) : IsDart s (.bdry x) := trivial
/-- Every `ē_x` is a dart. -/
@[simp] theorem isDart_bdryRev (x : Fin b) : IsDart s (.bdryRev x) := trivial
/-- `λ_x` is a dart if and only if `x` is a lollipop position. -/
@[simp] theorem isDart_lam {x : Fin b} : IsDart s (.lam x) ↔ heights s x = ∅ := Iff.rfl
/-- `dn_{x,u}` is a dart if and only if `u = 0` or `u ∈ P_x` with `u < m_x`. -/
@[simp] theorem isDart_dn {x : Fin b} {u : ℕ} :
    IsDart s (.dn x u) ↔ u = 0 ∨ (u ∈ heights s x ∧ u < top s x) := Iff.rfl
/-- `up_{x,u}` is a dart if and only if `u ∈ P_x`. -/
@[simp] theorem isDart_up {x : Fin b} {u : ℕ} : IsDart s (.up x u) ↔ u ∈ heights s x := Iff.rfl
/-- `c_t` is a dart if and only if `t ∈ [1, r]`. -/
@[simp] theorem isDart_bridge {t : ℕ} :
    IsDart (b := b) s (.bridge t) ↔ 1 ≤ t ∧ t ≤ s.length := Iff.rfl
/-- `c̄_t` is a dart if and only if `t ∈ [1, r]`. -/
@[simp] theorem isDart_bridgeRev {t : ℕ} :
    IsDart (b := b) s (.bridgeRev t) ↔ 1 ≤ t ∧ t ≤ s.length := Iff.rfl

/-- `e_x` is a boundary arc. -/
@[simp] theorem isBoundaryArc_bdry (x : Fin b) : IsBoundaryArc (.bdry x) := trivial
/-- `ē_x` is a boundary arc. -/
@[simp] theorem isBoundaryArc_bdryRev (x : Fin b) : IsBoundaryArc (.bdryRev x) := trivial
/-- `λ_x` is not a boundary arc. -/
@[simp] theorem not_isBoundaryArc_lam (x : Fin b) : ¬IsBoundaryArc (.lam x) := id
/-- `dn_{x,u}` is not a boundary arc. -/
@[simp] theorem not_isBoundaryArc_dn (x : Fin b) (u : ℕ) : ¬IsBoundaryArc (.dn x u) := id
/-- `up_{x,u}` is not a boundary arc. -/
@[simp] theorem not_isBoundaryArc_up (x : Fin b) (u : ℕ) : ¬IsBoundaryArc (.up x u) := id
/-- `c_t` is not a boundary arc. -/
@[simp] theorem not_isBoundaryArc_bridge (t : ℕ) : ¬IsBoundaryArc (b := b) (.bridge t) := id
/-- `c̄_t` is not a boundary arc. -/
@[simp] theorem not_isBoundaryArc_bridgeRev (t : ℕ) : ¬IsBoundaryArc (b := b) (.bridgeRev t) :=
  id

/-- The colour of `λ_x` is `γ(x)`. -/
@[simp] theorem colour_lam (γ : Fin b → Shade) (x : Fin b) : colour s γ (.lam x) = γ x := rfl
/-- The colour of `c_t` is white. -/
@[simp] theorem colour_bridge (γ : Fin b → Shade) (t : ℕ) :
    colour (b := b) s γ (.bridge t) = .white := rfl
/-- The colour of `c̄_t` is black. -/
@[simp] theorem colour_bridgeRev (γ : Fin b → Shade) (t : ℕ) :
    colour (b := b) s γ (.bridgeRev t) = .black := rfl
/-- The colour of `up_{x,u}` is white if `x + 1 = i_u` and black otherwise. -/
theorem colour_up (γ : Fin b → Shade) (x : Fin b) (u : ℕ) : colour s γ (.up x u) =
    if (x : ℤ) + 1 = (pair s u).1 then .white else .black := rfl
/-- For `u ≠ 0`, the colour of `dn_{x,u}` is white if `x + 1 = i_u` and black otherwise. -/
theorem colour_dn_of_ne_zero (γ : Fin b → Shade) {x : Fin b} {u : ℕ} (hu : u ≠ 0) :
    colour s γ (.dn x u) = if (x : ℤ) + 1 = (pair s u).1 then .white else .black := by
  simp only [colour, ne_eq, hu, not_false_eq_true, true_and, ite_not]

/-- The rotation sends darts to darts. -/
theorem isDart_rotate {d : BridgeSymbol b} (hd : IsDart s d) : IsDart s (rotate s d) := by
  cases d with
  | bdry x => exact Or.inl rfl
  | bdryRev y => trivial
  | lam x => exact hd
  | dn x u =>
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · trivial
    · have hd' : u ∈ heights s x ∧ u < top s x := hd.resolve_left hu.ne'
      rw [rotate_dn_of_ne_zero hu.ne']
      split_ifs
      · exact ⟨hu, le_length_of_mem_heights hd'.1⟩
      · exact hd'.1
  | up x u =>
    rw [rotate_up]
    split_ifs with h1 h2
    · exact Or.inr ⟨hd, h2⟩
    · exact ⟨pos_of_mem_heights hd, le_length_of_mem_heights hd⟩
    · exact ⟨pos_of_mem_heights hd, le_length_of_mem_heights hd⟩
  | bridge t =>
    simp only [rotate]
    split
    · next x hx =>
      exact mem_heights.2 ⟨hd.1, hd.2, Or.inl (leftEnd_eq_some.1 hx)⟩
    · exact hd
  | bridgeRev t =>
    simp only [rotate]
    split
    · next y hy =>
      have hm : t ∈ heights s y := mem_heights.2 ⟨hd.1, hd.2, Or.inr (rightEnd_eq_some.1 hy).1⟩
      split_ifs with h
      · exact Or.inr ⟨hm, h⟩
      · exact hm
    · exact hd

/-- The inverse rotation sends darts to darts. -/
theorem isDart_rotateInv {d : BridgeSymbol b} (hd : IsDart s d) : IsDart s (rotateInv s d) := by
  cases d with
  | bdry x => trivial
  | bdryRev y => exact Or.inl rfl
  | lam x => exact hd
  | dn x u =>
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · trivial
    · have hd' : u ∈ heights s x ∧ u < top s x := hd.resolve_left hu.ne'
      rw [rotateInv_dn_of_ne_zero hu.ne']
      split_ifs
      · exact hd'.1
      · exact ⟨hu, le_length_of_mem_heights hd'.1⟩
  | up x u =>
    rw [rotateInv_up]
    split_ifs with h1 h2
    · exact ⟨pos_of_mem_heights hd, le_length_of_mem_heights hd⟩
    · exact Or.inr ⟨hd, h2⟩
    · exact ⟨pos_of_mem_heights hd, le_length_of_mem_heights hd⟩
  | bridge t =>
    simp only [rotateInv]
    split
    · next x hx =>
      have hm : t ∈ heights s x := mem_heights.2 ⟨hd.1, hd.2, Or.inl (leftEnd_eq_some.1 hx)⟩
      split_ifs with h
      · exact Or.inr ⟨hm, h⟩
      · exact hm
    · exact hd
  | bridgeRev t =>
    simp only [rotateInv]
    split
    · next y hy =>
      exact mem_heights.2 ⟨hd.1, hd.2, Or.inr (rightEnd_eq_some.1 hy).1⟩
    · exact hd

/-- `σ⁻¹ ∘ σ` is the identity on darts. -/
theorem rotateInv_rotate {d : BridgeSymbol b} (hd : IsDart s d) :
    rotateInv s (rotate s d) = d := by
  cases d with
  | bdry x => rfl
  | bdryRev y =>
    change BridgeSymbol.bdryRev (finRotate b ((finRotate b).symm y)) = _
    rw [Equiv.apply_symm_apply]
  | lam x => rfl
  | dn x u =>
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · change BridgeSymbol.dn ((finRotate b).symm (finRotate b x)) 0 = _
      rw [Equiv.symm_apply_apply]
    · have hd' : u ∈ heights s x ∧ u < top s x := hd.resolve_left hu.ne'
      rw [rotate_dn_of_ne_zero hu.ne']
      split_ifs with h
      · rw [rotateInv_bridge_of_eq h, if_pos hd'.2]
      · rw [rotateInv_up, if_neg h, if_pos hd'.2]
  | up x u =>
    have hu := pos_of_mem_heights hd
    rw [rotate_up]
    split_ifs with h1 h2
    · rw [rotateInv_dn_of_ne_zero hu.ne', if_pos h1]
    · rw [rotateInv_bridge_of_eq h1, if_neg h2]
    · have := rightEnd_eq_some_of_mem_heights hd h1
      simp only [rotateInv, this]
  | bridge t =>
    simp only [rotate]
    split
    · next x hx =>
      rw [rotateInv_up, if_pos (leftEnd_eq_some.1 hx)]
    · next hx => simp only [rotateInv, hx]
  | bridgeRev t =>
    simp only [rotate]
    split
    · next y hy =>
      obtain ⟨hy1, hy2⟩ := rightEnd_eq_some.1 hy
      split_ifs with h
      · rw [rotateInv_dn_of_ne_zero (by have := hd.1; omega), if_neg hy2]
      · rw [rotateInv_up, if_neg hy2, if_neg h]
    · next hy => simp only [rotateInv, hy]

/-- `σ ∘ σ⁻¹` is the identity on darts. -/
theorem rotate_rotateInv {d : BridgeSymbol b} (hd : IsDart s d) :
    rotate s (rotateInv s d) = d := by
  cases d with
  | bdry x =>
    change BridgeSymbol.bdry ((finRotate b).symm (finRotate b x)) = _
    rw [Equiv.symm_apply_apply]
  | bdryRev y =>
    change BridgeSymbol.bdryRev (finRotate b ((finRotate b).symm y)) = _
    rw [Equiv.apply_symm_apply]
  | lam x => rfl
  | dn x u =>
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · rfl
    · have hd' : u ∈ heights s x ∧ u < top s x := hd.resolve_left hu.ne'
      rw [rotateInv_dn_of_ne_zero hu.ne']
      split_ifs with h
      · rw [rotate_up, if_pos h, if_pos hd'.2]
      · have := rightEnd_eq_some_of_mem_heights hd'.1 h
        simp only [rotate, this, if_pos hd'.2]
  | up x u =>
    have hu := pos_of_mem_heights hd
    rw [rotateInv_up]
    split_ifs with h1 h2
    · rw [rotate_bridge_of_eq h1]
    · rw [rotate_dn_of_ne_zero hu.ne', if_neg h1]
    · have := rightEnd_eq_some_of_mem_heights hd h1
      simp only [rotate, this, if_neg h2]
  | bridge t =>
    simp only [rotateInv]
    split
    · next x hx =>
      have hx' := leftEnd_eq_some.1 hx
      split_ifs with h
      · rw [rotate_dn_of_ne_zero (by have := hd.1; omega), if_pos hx']
      · rw [rotate_up, if_pos hx', if_neg h]
    · next hx => simp only [rotate, hx]
  | bridgeRev t =>
    simp only [rotateInv]
    split
    · next y hy =>
      rw [rotate_up, if_neg (rightEnd_eq_some.1 hy).2]
    · next hy => simp only [rotate, hy]

/-- The involution sends darts to darts. -/
theorem isDart_reverse {d : BridgeSymbol b} (hd : IsDart s d) : IsDart s (reverse s d) := by
  cases d with
  | bdry x => trivial
  | bdryRev x => trivial
  | lam x => exact Or.inl rfl
  | dn x u =>
    rw [reverse_dn]
    split_ifs with h
    · exact next_mem h
    · have hu : u = 0 := hd.resolve_right fun h' => h h'.2
      subst hu
      exact top_eq_zero_iff.1 (by omega)
  | up x u =>
    rcases prev_eq_zero_or_mem x u (s := s) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, prev_lt_top hd⟩
  | bridge t => exact hd
  | bridgeRev t => exact hd

/-- The involution `d ↦ d̄` is an involution on darts. -/
theorem reverse_reverse {d : BridgeSymbol b} (hd : IsDart s d) :
    reverse s (reverse s d) = d := by
  cases d with
  | bdry x => rfl
  | bdryRev x => rfl
  | lam x =>
    have : top s x = 0 := top_eq_zero_iff.2 hd
    simp [reverse_dn, this]
  | dn x u =>
    rw [reverse_dn]
    split_ifs with h
    · rw [reverse_up, prev_next (hd.imp_right And.left) h]
    · have hu : u = 0 := hd.resolve_right fun h' => h h'.2
      subst hu
      rfl
  | up x u =>
    rw [reverse_up, reverse_dn_of_lt_top (prev_lt_top hd), next_prev hd]
  | bridge t => rfl
  | bridgeRev t => rfl

/-- The **key** of a symbol, for `r` the length of `s`:
`key(dn_{x,u}) = 2u + 1` (so `key(g_x) = 1`), `key(c_t) = key(c̄_t) = 2t`,
`key(up_{x,u}) = 4r + 4 - 2u`, `key(λ_x) = 2`; the boundary arcs, which have no key in FWZ,
get `0`. -/
def key (s : List (ℤ × ℤ)) : BridgeSymbol b → ℤ
  | .dn _ u => 2 * u + 1
  | .bridge t => 2 * t
  | .bridgeRev t => 2 * t
  | .up _ u => 4 * s.length + 4 - 2 * u
  | .lam _ => 2
  | .bdry _ => 0
  | .bdryRev _ => 0

end BridgeSymbol

/-! ### The darts and the bridge graph -/

/-- The finite set of the darts of the bridge graph of `s`, as symbols. -/
def BridgeSymbol.darts (b : ℕ) (s : List (ℤ × ℤ)) : Finset (BridgeSymbol b) :=
  (univ.image BridgeSymbol.bdry ∪ univ.image BridgeSymbol.bdryRev ∪ univ.image BridgeSymbol.lam ∪
    (univ ×ˢ range (s.length + 1)).image (fun p => BridgeSymbol.dn p.1 p.2) ∪
    (univ ×ˢ range (s.length + 1)).image (fun p => BridgeSymbol.up p.1 p.2) ∪
    (range (s.length + 1)).image BridgeSymbol.bridge ∪
    (range (s.length + 1)).image BridgeSymbol.bridgeRev).filter (BridgeSymbol.IsDart s)

/-- A symbol lies in `BridgeSymbol.darts b s` if and only if it is a dart. -/
theorem BridgeSymbol.mem_darts {b : ℕ} {s : List (ℤ × ℤ)} {d : BridgeSymbol b} :
    d ∈ BridgeSymbol.darts b s ↔ d.IsDart s := by
  rw [BridgeSymbol.darts, mem_filter, and_iff_right_iff_imp]
  intro hd
  cases d with
  | dn x u =>
    have : u < s.length + 1 := by
      rcases hd with rfl | ⟨h, -⟩
      · omega
      · have := BridgeGraph.le_length_of_mem_heights h
        omega
    simp
    omega
  | up x u => simpa using BridgeGraph.le_length_of_mem_heights (s := s) hd
  | bridge t => simpa using hd.2
  | bridgeRev t => simpa using hd.2
  | _ => simp

/-- The darts of the bridge graph of `s` with `b` boundary vertices: the symbols satisfying
`BridgeSymbol.IsDart s`. -/
abbrev BridgeDart (b : ℕ) (s : List (ℤ × ℤ)) : Type := {d : BridgeSymbol b // d.IsDart s}

/-- The darts of a bridge graph form a finite type. -/
instance (b : ℕ) (s : List (ℤ × ℤ)) : Fintype (BridgeDart b s) :=
  Fintype.subtype (BridgeSymbol.darts b s) fun _ => BridgeSymbol.mem_darts

namespace BridgeDart

variable {b : ℕ} {s : List (ℤ × ℤ)}

/-- The rotation of the bridge graph, as a permutation of its darts. -/
def rotPerm (b : ℕ) (s : List (ℤ × ℤ)) : Equiv.Perm (BridgeDart b s) where
  toFun d := ⟨d.1.rotate s, BridgeSymbol.isDart_rotate d.2⟩
  invFun d := ⟨d.1.rotateInv s, BridgeSymbol.isDart_rotateInv d.2⟩
  left_inv d := Subtype.ext (BridgeSymbol.rotateInv_rotate d.2)
  right_inv d := Subtype.ext (BridgeSymbol.rotate_rotateInv d.2)

/-- The involution of the bridge graph, as a permutation of its darts. -/
def revPerm (b : ℕ) (s : List (ℤ × ℤ)) : Equiv.Perm (BridgeDart b s) :=
  Function.Involutive.toPerm (fun d => ⟨d.1.reverse s, BridgeSymbol.isDart_reverse d.2⟩)
    fun d => Subtype.ext (BridgeSymbol.reverse_reverse d.2)

/-- The **key** of a dart of the bridge graph `G(s, γ)`, for `r` the length of `s`:
`key(dn_{x,u}) = 2u + 1` (so `key(g_x) = 1` for every `x`), `key(c_t) = key(c̄_t) = 2t`,
`key(up_{x,u}) = 4r + 4 - 2u`, and `key(λ_x) = 2` at a lollipop position `x`. FWZ define
it on the darts off the boundary circle; the boundary arcs get the value `0`. -/
@[cluster_algebras "def_bridge_dart_key"]
def key (d : BridgeDart b s) : ℤ := d.1.key s

end BridgeDart

/-- The **bridge graph** `G(s, γ)` of a finite sequence of pairs `s = ((i₁, j₁), …, (i_r, j_r))`
with `1 ≤ i_t < j_t ≤ b` and a colouring `γ : [1, b] → Shade` (with `0`-indexed labels: `γ x` is
the colour at the label `x + 1`). Its darts are the
`BridgeDart b s`; the involution is `BridgeSymbol.reverse`, the rotation `BridgeSymbol.rotate`,
the boundary arcs are the `e_x` and `ē_x`, the colours are `BridgeSymbol.colour` (white at the
white end `{up_{i_t,t}, dn_{i_t,t}, c_t}` of a bridge, black at its black end, `γ(x)` at the
lollipop `{λ_x}`), and the vertex labelled `x` is that of the leg `g_x = dn_{x,0}`.
The definition makes sense for every list `s`; see the implementation notes of the file. -/
@[cluster_algebras "def_bridge_graph"]
def bridgeGraph (b : ℕ) (s : List (ℤ × ℤ)) (γ : Fin b → Shade) :
    PlabicData (BridgeDart b s) b where
  inv := BridgeDart.revPerm b s
  rot := BridgeDart.rotPerm b s
  bdry := univ.filter fun d => d.1.IsBoundaryArc
  colour d := d.1.colour s γ
  leg x := ⟨.dn x 0, Or.inl rfl⟩

namespace bridgeGraph

variable {b : ℕ} {s : List (ℤ × ℤ)} {γ : Fin b → Shade}

/-- The rotation of `G(s, γ)` is `BridgeSymbol.rotate` on symbols. -/
@[simp]
theorem rot_val (d : BridgeDart b s) :
    ((bridgeGraph b s γ).rot d).1 = d.1.rotate s := rfl

/-- The inverse rotation of `G(s, γ)` is `BridgeSymbol.rotateInv` on symbols. -/
@[simp]
theorem rot_symm_val (d : BridgeDart b s) :
    ((bridgeGraph b s γ).rot.symm d).1 = d.1.rotateInv s := rfl

/-- The involution of `G(s, γ)` is `BridgeSymbol.reverse` on symbols. -/
@[simp]
theorem inv_val (d : BridgeDart b s) :
    ((bridgeGraph b s γ).inv d).1 = d.1.reverse s := rfl

/-- The boundary arcs of `G(s, γ)` are the darts `e_x` and `ē_x`. -/
@[simp]
theorem mem_bdry {d : BridgeDart b s} :
    d ∈ (bridgeGraph b s γ).bdry ↔ d.1.IsBoundaryArc := by
  simp [bridgeGraph]

/-- The colouring of `G(s, γ)` is `BridgeSymbol.colour` on symbols. -/
@[simp]
theorem colour_apply (d : BridgeDart b s) :
    (bridgeGraph b s γ).colour d = d.1.colour s γ := rfl

/-- The leg of `G(s, γ)` at `x` is `g_x = dn_{x,0}`. -/
@[simp]
theorem leg_val (x : Fin b) : ((bridgeGraph b s γ).leg x).1 = .dn x 0 := rfl

/-- The involution of `G(s, γ)` is involutive. -/
theorem inv_involutive : Function.Involutive (bridgeGraph b s γ).inv :=
  fun d => Subtype.ext (BridgeSymbol.reverse_reverse d.2)

end bridgeGraph

open BridgeGraph BridgeSymbol in
/-- **The darts arriving at a crossing of the bridge graph.** Let `t ∈ [1, r]`, let `x` be the
left end of the `t`-th pair (`x + 1 = i_t`, in `0`-indexed labels), with `t ≠ m_x`, and let
`u ∈ {0} ∪ P_x` with `u < t` be such that no element of `P_x` lies in `[u + 1, t - 1]`. Then
`dn_{x,u}`, `up_{x, nx_x(t)}` and `c̄_t` are darts of `G(s, γ)`, and they are exactly the darts
`z` with `z̄ ∈ {up_{x,t}, dn_{x,t}, c_t}`, the white end of the `t`-th bridge. FWZ assume
`s` nested with `1 ≤ i_t < j_t ≤ b`; neither is needed. -/
@[cluster_algebras "lem_bridge_crossing_arrivals"]
theorem bridgeGraph_inv_mem_crossing_iff {b : ℕ} {s : List (ℤ × ℤ)} (γ : Fin b → Shade)
    {t : ℕ} (ht : 1 ≤ t ∧ t ≤ s.length) {x : Fin b} (hx : (x : ℤ) + 1 = (pair s t).1)
    (htm : t ≠ top s x) {u : ℕ} (hu : u = 0 ∨ u ∈ heights s x) (hut : u < t)
    (hgap : ∀ v ∈ heights s x, v ∉ Icc (u + 1) (t - 1)) :
    IsDart s (.dn x u) ∧ IsDart s (.up x (next s x t)) ∧ IsDart (b := b) s (.bridgeRev t) ∧
      ∀ z : BridgeDart b s,
        ((bridgeGraph b s γ).inv z).1 ∈ ({.up x t, .dn x t, .bridge t} : Finset (BridgeSymbol b)) ↔
          z.1 ∈ ({.dn x u, .up x (next s x t), .bridgeRev t} : Finset (BridgeSymbol b)) := by
  have htP : t ∈ heights s x := mem_heights.2 ⟨ht.1, ht.2, Or.inl hx⟩
  have htT : t < top s x := lt_of_le_of_ne (le_top htP) htm
  have huT : u < top s x := hut.trans htT
  have hnu : next s x u = t := by
    obtain ⟨hm, hlt⟩ := next_spec huT
    refine le_antisymm (next_le htP hut) ?_
    by_contra h
    exact hgap _ hm (mem_Icc.2 ⟨hlt, by omega⟩)
  have hpt : prev s x (next s x t) = t := prev_next (Or.inr htP) htT
  have hpu : prev s x t = u := by
    rw [← hnu]
    exact prev_next hu huT
  refine ⟨hu.imp_right fun h => ⟨h, huT⟩, next_mem htT, ht, fun z => ?_⟩
  rw [bridgeGraph.inv_val]
  simp only [mem_insert, mem_singleton]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← reverse_reverse z.2]
    rcases h with h | h | h <;> rw [h]
    · left
      rw [reverse_up, hpu]
    · refine Or.inr (Or.inl ?_)
      rw [reverse_dn_of_lt_top htT]
    · exact Or.inr (Or.inr rfl)
  · rcases h with h | h | h <;> rw [h]
    · left
      rw [reverse_dn_of_lt_top huT, hnu]
    · refine Or.inr (Or.inl ?_)
      rw [reverse_up, hpt]
    · exact Or.inr (Or.inr rfl)

end ClusterAlgebras

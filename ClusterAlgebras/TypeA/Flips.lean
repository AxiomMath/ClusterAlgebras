/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeA.Polygon

/-!
# The fan, flip-connectivity, and counting triangulations

Facts about triangulations of a convex polygon used in the classification of seed patterns of
type `A_n`. The fan is a triangulation; any two triangulations are joined by flips; every
triangulation of the `m`-gon has `m - 3` diagonals; non-crossing sets of diagonals extend to
triangulations; two crossing diagonals are related by a flip; there are `c_{m-2}`
triangulations, `m` sides and `m(m-3)/2` diagonals; and every orientation of a path is the
quiver of some triangulation.

## Main definitions

* `ClusterAlgebras.TypeA.fanTriangulation m`: the fan `T∘` at the vertex `0`.
* `ClusterAlgebras.TypeA.IsFlip T T'`: `T'` is obtained from `T` by one flip.
* `ClusterAlgebras.TypeA.IsPathListing d ε`: `d₁, …, dₙ` list a triangulation of the
  `(n+3)`-gon whose quiver is the path with orientation `ε`.

## Main statements

* `ClusterAlgebras.TypeA.isTriangulation_fanTriangulation`: the fan is a triangulation.
* `ClusterAlgebras.TypeA.IsTriangulation.reflTransGen_isFlip`: flip-connectivity.
* `ClusterAlgebras.TypeA.IsTriangulation.card_eq`: `|T| = m - 3`.
* `ClusterAlgebras.TypeA.encard_setOf_isTriangulation`: there are `c_{m-2}` triangulations.
* `ClusterAlgebras.TypeA.exists_isPathListing`: a triangulation for every orientation of a path.

## Implementation notes

* **Vertex convention.** The vertices of the `m`-gon are the elements of `ZMod m`, so the vertex
  `v : ZMod m` is the vertex `v + 1` when the vertices are labelled `1, …, m` (see
  `ClusterAlgebras.TypeA.Polygon`). The fan `{{1, j} : j ∈ [3, m-1]}` is therefore
  `{s(0, j) : j ∈ [2, m-2]}` here, and its segments `{1, j}` (`j ∈ [2, m]`) and `{ℓ, ℓ+1}`
  (`ℓ ∈ [2, m-1]`) are `s(0, j)` (`j ∈ [1, m-1]`) and `s(ℓ, ℓ+1)` (`ℓ ∈ [1, m-2]`). For `m = 6`
  it is `ClusterAlgebras.hexagonFan`.
* A sequence of flips `T = U₀, …, U_r = T'` is `Relation.ReflTransGen IsFlip T T'`.
* In `IsPathListing` the diagonals `d₁, …, dₙ` are indexed by `Fin n`, `d_{p+1}` being `d p`,
  and so are the signs, `ε_{p+1}` being `ε p`; only `ε p` with `p + 1 < n` enters, as the
  signs `ε₁, …, ε_{n-1}`.
-/

@[expose] public section

namespace ClusterAlgebras

namespace TypeA

/-! ### The fan -/

/-- The **fan triangulation** `T∘` of the convex `m`-gon: the segments `s(0, j)` with
`j ∈ [2, m-2]`. -/
@[cluster_algebras "lem_fan_triangulation"]
def fanTriangulation (m : ℕ) : Finset (Sym2 (ZMod m)) :=
  (Finset.Icc 2 (m - 2)).image fun j : ℕ => s(0, (j : ZMod m))

variable {m : ℕ} [NeZero m]

/-! ### Vertices as natural numbers

Continuing `ClusterAlgebras.TypeA.sbtw_natCast_iff` and its companions: on residues of natural
numbers below `m`, sides, diagonals and crossing are statements about natural numbers. -/

private theorem isSide_natCast_iff_flips (hm : 3 ≤ m) {a b : ℕ} (hab : a < b) (hb : b < m) :
    IsSide s((a : ZMod m), (b : ZMod m)) ↔ b = a + 1 ∨ (a = 0 ∧ b = m - 1) := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨k, hk, rfl⟩ := exists_natCast_eq i
    by_cases hk1 : k + 1 < m
    · rw [show (k : ZMod m) + 1 = ((k + 1 : ℕ) : ZMod m) by push_cast; rfl,
        sym2_natCast_eq_iff (by omega) hb hk hk1] at hi
      omega
    · have hkm : k + 1 = m := by omega
      rw [show (k : ZMod m) + 1 = ((0 : ℕ) : ZMod m) by
          rw [← Nat.cast_add_one, hkm, ZMod.natCast_self, Nat.cast_zero],
        sym2_natCast_eq_iff (by omega) hb hk (by omega)] at hi
      omega
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact ⟨a, by push_cast; rfl⟩
    · refine ⟨((m - 1 : ℕ) : ZMod m), ?_⟩
      rw [show ((m - 1 : ℕ) : ZMod m) + 1 = 0 by
        rw [← Nat.cast_add_one, Nat.sub_add_cancel (by omega), ZMod.natCast_self]]
      simp [Sym2.eq_swap]

omit [NeZero m] in
private theorem isSegment_natCast_iff_flips {a b : ℕ} (ha : a < m) (hb : b < m) :
    IsSegment s((a : ZMod m), (b : ZMod m)) ↔ a ≠ b := by
  rw [IsSegment, Sym2.mk_isDiag_iff, natCast_inj_of_lt ha hb]

private theorem exists_natCast_lt_of_isSegment_flips {e : Sym2 (ZMod m)} (he : IsSegment e) :
    ∃ a b : ℕ, a < b ∧ b < m ∧ e = s((a : ZMod m), (b : ZMod m)) := by
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨a, ha, rfl⟩ := exists_natCast_eq x
    obtain ⟨b, hb, rfl⟩ := exists_natCast_eq y
    rw [isSegment_natCast_iff_flips ha hb] at he
    rcases Nat.lt_or_gt_of_ne he with h | h
    exacts [⟨a, b, h, hb, rfl⟩, ⟨b, a, h, ha, Sym2.eq_swap⟩]

private theorem cross_natCast_iff_flips {a b c d : ℕ} (hab : a < b) (hb : b < m) (hcd : c < d)
    (hd : d < m) :
    Cross s((a : ZMod m), (b : ZMod m)) s((c : ZMod m), (d : ZMod m)) ↔
      (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b) := by
  constructor
  · rintro ⟨x, y, z, w, h1, h2, h3, h4⟩
    obtain ⟨x, hx, rfl⟩ := exists_natCast_eq x
    obtain ⟨y, hy, rfl⟩ := exists_natCast_eq y
    obtain ⟨z, hz, rfl⟩ := exists_natCast_eq z
    obtain ⟨w, hw, rfl⟩ := exists_natCast_eq w
    rw [sym2_natCast_eq_iff (by omega) hb hx hy] at h1
    rw [sym2_natCast_eq_iff (by omega) hd hz hw] at h2
    rw [sbtw_natCast_iff hx hz hy] at h3
    rw [sbtw_natCast_iff hy hw hx] at h4
    omega
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · refine ⟨a, b, c, d, rfl, rfl, ?_, ?_⟩
      · rw [sbtw_natCast_iff (by omega) (by omega) hb]
        omega
      · rw [sbtw_natCast_iff hb hd (by omega)]
        omega
    · refine ⟨a, b, d, c, rfl, Sym2.eq_swap, ?_, ?_⟩
      · rw [sbtw_natCast_iff (by omega) hd hb]
        omega
      · rw [sbtw_natCast_iff hb (by omega) (by omega)]
        omega

private theorem isDiagonal_natCast_iff_flips (hm : 3 ≤ m) {a b : ℕ} (hab : a < b) (hb : b < m) :
    IsDiagonal s((a : ZMod m), (b : ZMod m)) ↔ a + 2 ≤ b ∧ ¬(a = 0 ∧ b = m - 1) := by
  rw [IsDiagonal, isSegment_natCast_iff_flips (by omega) hb, isSide_natCast_iff_flips hm hab hb]
  omega

omit [NeZero m] in
private theorem mem_fanTriangulation_natCast_iff_flips {a b : ℕ} (hab : a < b) (hb : b < m) :
    s((a : ZMod m), (b : ZMod m)) ∈ fanTriangulation m ↔ a = 0 ∧ 2 ≤ b ∧ b ≤ m - 2 := by
  simp only [fanTriangulation, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [← Nat.cast_zero, sym2_natCast_eq_iff (by omega) (by omega) (by omega) hb] at h
    omega
  · rintro ⟨rfl, h⟩
    exact ⟨b, h, by rw [Nat.cast_zero]⟩

omit [NeZero m] in
private theorem natCast_add_one_eq_zero_flips {k : ℕ} (hk : k + 1 = m) :
    (k : ZMod m) + 1 = 0 := by
  rw [← Nat.cast_add_one, hk, ZMod.natCast_self]

/-- **The fan is a triangulation.** -/
@[cluster_algebras "lem_fan_triangulation"]
theorem isTriangulation_fanTriangulation (hm : 4 ≤ m) : IsTriangulation (fanTriangulation m) where
  isDiagonal e he := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he
    rw [Finset.mem_Icc] at hj
    rw [← Nat.cast_zero, isDiagonal_natCast_iff_flips (by omega) (by omega) (by omega)]
    omega
  noncrossing e he f hf := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hf
    rw [Finset.mem_Icc] at hj hk
    rw [← Nat.cast_zero, cross_natCast_iff_flips (by omega) (by omega) (by omega) (by omega)]
    omega
  maximal e he hne := by
    obtain ⟨a, b, hab, hb, rfl⟩ := exists_natCast_lt_of_isSegment_flips he.isSegment
    rw [isDiagonal_natCast_iff_flips (by omega) hab hb] at he
    rw [mem_fanTriangulation_natCast_iff_flips hab hb] at hne
    refine ⟨s(((0 : ℕ) : ZMod m), ((a + 1 : ℕ) : ZMod m)), ?_, ?_⟩
    · rw [mem_fanTriangulation_natCast_iff_flips (by omega) (by omega)]
      omega
    · rw [cross_natCast_iff_flips hab hb (by omega) (by omega)]
      omega

omit [NeZero m] in
/-- **The fan has `m - 3` elements.** -/
@[cluster_algebras "lem_fan_triangulation"]
theorem card_fanTriangulation (hm : 4 ≤ m) : (fanTriangulation m).card = m - 3 := by
  rw [fanTriangulation, Finset.card_image_of_injOn, Nat.card_Icc]
  · omega
  intro j hj k hk h
  simp only [Finset.coe_Icc, Set.mem_Icc] at hj hk
  simp only at h
  rw [← Nat.cast_zero, sym2_natCast_eq_iff (by omega) (by omega) (by omega) (by omega)] at h
  omega

/-- **The segments of the fan** are the sets `s(0, j)`, `j ∈ [1, m-1]`, and `s(ℓ, ℓ+1)`,
`ℓ ∈ [1, m-2]`. -/
@[cluster_algebras "lem_fan_triangulation"]
theorem segments_fanTriangulation (hm : 4 ≤ m) :
    segments (fanTriangulation m) =
      (Finset.Icc 1 (m - 1)).image (fun j : ℕ => s(0, (j : ZMod m))) ∪
        (Finset.Icc 1 (m - 2)).image fun l : ℕ => s((l : ZMod m), (l : ZMod m) + 1) := by
  ext e
  rw [mem_segments, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (he | ⟨i, rfl⟩)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he
      rw [Finset.mem_Icc] at hj
      exact Or.inl ⟨j, Finset.mem_Icc.2 (by omega), rfl⟩
    · obtain ⟨k, hk, rfl⟩ := exists_natCast_eq i
      by_cases h0 : k = 0
      · subst h0
        exact Or.inl ⟨1, Finset.mem_Icc.2 (by omega), by simp⟩
      by_cases hl : k + 1 < m
      · exact Or.inr ⟨k, Finset.mem_Icc.2 (by omega), rfl⟩
      · refine Or.inl ⟨k, Finset.mem_Icc.2 (by omega), ?_⟩
        rw [natCast_add_one_eq_zero_flips (by omega), Sym2.eq_swap]
  · rintro (⟨j, hj, rfl⟩ | ⟨l, hl, rfl⟩)
    · rw [Finset.mem_Icc] at hj
      by_cases h1 : j = 1
      · subst h1
        exact Or.inr ⟨0, by simp⟩
      by_cases h2 : j = m - 1
      · refine Or.inr ⟨(j : ZMod m), ?_⟩
        rw [natCast_add_one_eq_zero_flips (by omega), Sym2.eq_swap]
      · exact Or.inl (Finset.mem_image.2 ⟨j, Finset.mem_Icc.2 (by omega), rfl⟩)
    · exact Or.inr ⟨l, rfl⟩

/-- **The fan has `2m - 3` segments.** -/
@[cluster_algebras "lem_fan_triangulation"]
theorem card_segments_fanTriangulation (hm : 4 ≤ m) :
    (segments (fanTriangulation m)).card = 2 * m - 3 := by
  rw [segments_fanTriangulation hm, Finset.card_union_of_disjoint, Finset.card_image_of_injOn,
    Finset.card_image_of_injOn, Nat.card_Icc, Nat.card_Icc]
  · omega
  · intro j hj k hk h
    simp only [Finset.coe_Icc, Set.mem_Icc] at hj hk
    simp only at h
    rw [← Nat.cast_add_one, ← Nat.cast_add_one,
      sym2_natCast_eq_iff (by omega) (by omega) (by omega) (by omega)] at h
    omega
  · intro j hj k hk h
    simp only [Finset.coe_Icc, Set.mem_Icc] at hj hk
    simp only at h
    rw [← Nat.cast_zero, sym2_natCast_eq_iff (by omega) (by omega) (by omega)
      (by omega)] at h
    omega
  · rw [Finset.disjoint_left]
    rintro e he₁ he₂
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he₁
    obtain ⟨l, hl, h⟩ := Finset.mem_image.1 he₂
    rw [Finset.mem_Icc] at hj hl
    rw [← Nat.cast_add_one, ← Nat.cast_zero,
      sym2_natCast_eq_iff (by omega) (by omega) (by omega) (by omega)] at h
    omega

/-! ### Flip-connectivity and the number of diagonals -/

/-- `T'` is obtained from `T` by **one flip**: `T' = (T \ {γ}) ∪ {γ'}` with `γ'` the replacement
of some `γ ∈ T`. -/
def IsFlip (T T' : Finset (Sym2 (ZMod m))) : Prop :=
  ∃ γ γ', IsFlipReplacement T γ γ' ∧ T' = flipTriangulation T γ γ'

omit [NeZero m] in
/-- Undoing a flip: flipping `(T \ {γ}) ∪ {γ'}` back at `γ'` with replacement `γ` gives `T`. -/
private theorem flipTriangulation_flipTriangulation_flips {T : Finset (Sym2 (ZMod m))}
    {γ γ' : Sym2 (ZMod m)} (hγ : γ ∈ T) (hγ' : γ' ∉ T) :
    flipTriangulation (flipTriangulation T γ γ') γ' γ = T := by
  rw [flipTriangulation, flipTriangulation, Finset.erase_insert
    (fun h => hγ' (Finset.mem_of_mem_erase h)), Finset.insert_erase hγ]

omit [NeZero m] in
/-- **Flips can be reversed**: if `T'` is a flip of `T`, then `T` is a flip of `T'`. -/
theorem IsFlip.symm {T T' : Finset (Sym2 (ZMod m))} (h : IsFlip T T') :
    IsFlip T' T := by
  obtain ⟨γ, γ', ⟨hT, hγ, -, hγ'T, hT'⟩, rfl⟩ := h
  have hback := flipTriangulation_flipTriangulation_flips hγ hγ'T
  refine ⟨γ', γ, ⟨hT', Finset.mem_insert_self _ _, hT.isDiagonal γ hγ, ?_, by rwa [hback]⟩,
    hback.symm⟩
  rw [flipTriangulation, Finset.mem_insert, Finset.mem_erase]
  rintro (h | ⟨h, -⟩)
  exacts [hγ'T (h ▸ hγ), h rfl]

/-- A diagonal that is a segment of `T` lies in `T`. -/
private theorem mem_of_mem_segments_flips {T : Finset (Sym2 (ZMod m))} {e : Sym2 (ZMod m)}
    (he : e ∈ segments T) (hd : IsDiagonal e) : e ∈ T :=
  (mem_segments.1 he).resolve_right hd.2

/-- The number of diagonals of `T` through the vertex `0`. -/
private def fanDegree (T : Finset (Sym2 (ZMod m))) : ℕ :=
  ((Finset.Icc 2 (m - 2)).filter fun k : ℕ => s((0 : ZMod m), (k : ZMod m)) ∈ T).card

/-- A triangulation all of whose `m - 3` possible diagonals through `0` are present is the
fan. -/
private theorem eq_fanTriangulation_of_fanDegree (hm : 4 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) (hdeg : fanDegree T = m - 3) : T = fanTriangulation m := by
  unfold fanDegree at hdeg
  have hall := Finset.filter_card_eq (s := Finset.Icc 2 (m - 2))
    (p := fun k : ℕ => s((0 : ZMod m), (k : ZMod m)) ∈ T) (by rw [Nat.card_Icc]; omega)
  have hsub : fanTriangulation m ⊆ T := fun e he => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he
    exact hall j hj
  refine Finset.Subset.antisymm (fun e he => ?_) hsub
  by_contra hne
  obtain ⟨f, hf, hcr⟩ :=
    (isTriangulation_fanTriangulation hm).maximal e (hT.isDiagonal e he) hne
  exact hT.noncrossing e he f (hsub hf) hcr

omit [NeZero m] in
/-- If `P 1` and `P (m - 1)` hold and `P k` fails for some `k ∈ [1, m-2]`, there are `u < k < w`
with `P u` and `P w` and `P` failing strictly between `u` and `w`. -/
private theorem exists_gap_flips {P : ℕ → Prop} {k : ℕ} (h₁ : P 1) (hm : P (m - 1)) (hk : ¬P k)
    (hk1 : 1 ≤ k) (hkm : k < m - 1) :
    ∃ u w, 1 ≤ u ∧ u < k ∧ k < w ∧ w < m ∧ P u ∧ P w ∧ ∀ j, u < j → j < w → ¬P j := by
  classical
  have hex : ∃ j, k < j ∧ j < m ∧ P j := ⟨m - 1, by omega, by omega, hm⟩
  obtain ⟨hkw, hwm, hPw⟩ := Nat.find_spec hex
  have hPu : P (Nat.findGreatest P k) := Nat.findGreatest_spec hk1 h₁
  refine ⟨Nat.findGreatest P k, Nat.find hex, Nat.le_findGreatest hk1 h₁,
    lt_of_le_of_ne (Nat.findGreatest_le k) fun h => hk (h ▸ hPu), hkw, hwm, hPu, hPw,
    fun j huj hjw hPj => ?_⟩
  rcases le_or_gt j k with hjk | hjk
  · exact Nat.findGreatest_is_greatest huj hjk hPj
  · exact Nat.find_min hex hjw ⟨hjk, by omega, hPj⟩

/-- If `s(0, u)` and `s(0, w)` are segments of `T` but no `s(0, j)` with `u < j < w` is, then
`s(u, w)` lies in `T`: `u` is the apex over `s(0, w)`. -/
private theorem mem_of_fan_gap_flips (hm : 4 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) {u w : ℕ} (hu1 : 1 ≤ u) (huw : u + 2 ≤ w) (hwm : w < m)
    (hPu : s((0 : ZMod m), (u : ZMod m)) ∈ segments T)
    (hPw : s((0 : ZMod m), (w : ZMod m)) ∈ segments T)
    (hgap : ∀ j, u < j → j < w → s((0 : ZMod m), (j : ZMod m)) ∉ segments T) :
    s((u : ZMod m), (w : ZMod m)) ∈ T := by
  have h0 : ((0 : ℕ) : ZMod m) = 0 := Nat.cast_zero
  obtain ⟨B, ⟨hB, hB0, hBw⟩, -⟩ := IsTriangulation.existsUnique_apex (by omega) hT hPw
    ⟨((1 : ℕ) : ZMod m), by rw [← h0, sbtw_natCast_iff (by omega) (by omega) hwm]; omega⟩
  obtain ⟨Bn, hBn, rfl⟩ := exists_natCast_eq B
  rw [← h0, sbtw_natCast_iff (by omega) hBn hwm] at hB
  obtain rfl : Bn = u := by
    by_contra hne
    have hBu : Bn < u := (lt_or_gt_of_ne hne).resolve_right fun h => hgap Bn h (by omega) hB0
    have hd₁ : s((0 : ZMod m), (u : ZMod m)) ∈ T := mem_of_mem_segments_flips hPu (by
      rw [← h0, isDiagonal_natCast_iff_flips (by omega) (by omega) (by omega)]; omega)
    have hd₂ : s((Bn : ZMod m), (w : ZMod m)) ∈ T := mem_of_mem_segments_flips hBw (by
      rw [isDiagonal_natCast_iff_flips (by omega) (by omega) hwm]; omega)
    refine hT.noncrossing _ hd₁ _ hd₂ ?_
    rw [← h0, cross_natCast_iff_flips (by omega) (by omega) (by omega) hwm]
    omega
  exact mem_of_mem_segments_flips hBw (by
    rw [isDiagonal_natCast_iff_flips (by omega) (by omega) hwm]; omega)

omit [NeZero m] in
/-- Flipping `s(u, w)` to `s(b, 0)` adds exactly `b` to the fan diagonals through `0`. -/
private theorem filter_mem_flipTriangulation_fan {T : Finset (Sym2 (ZMod m))} {u bn w : ℕ}
    (hu1 : 1 ≤ u) (hub : u < bn) (hbw : bn < w) (hwm : w < m) :
    ((Finset.Icc 2 (m - 2)).filter fun j : ℕ => s((0 : ZMod m), (j : ZMod m)) ∈
      flipTriangulation T s((u : ZMod m), (w : ZMod m)) s((bn : ZMod m), 0)) =
    insert bn ((Finset.Icc 2 (m - 2)).filter fun j : ℕ => s((0 : ZMod m), (j : ZMod m)) ∈ T) := by
  have h0 : ((0 : ℕ) : ZMod m) = 0 := Nat.cast_zero
  have hbn : bn < m := by omega
  ext j
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_Icc, flipTriangulation,
    Finset.mem_erase]
  constructor
  · rintro ⟨hj, h | ⟨-, h⟩⟩
    · left
      rw [← h0, sym2_natCast_eq_iff (by omega) (by omega) hbn (by omega)] at h
      omega
    · exact Or.inr ⟨hj, h⟩
  · rintro (rfl | ⟨hj, h⟩)
    · exact ⟨by omega, Or.inl Sym2.eq_swap⟩
    · refine ⟨hj, Or.inr ⟨?_, h⟩⟩
      rw [← h0, Ne, sym2_natCast_eq_iff (by omega) (by omega) (by omega : u < m) hwm]
      omega

/-- The inductive step of flip-connectivity: a triangulation other than the fan has a flip
raising the number of diagonals through `0`. -/
private theorem exists_isFlip_fanDegree (hm : 4 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) (hdeg : fanDegree T < m - 3) :
    ∃ T', IsFlip T T' ∧ IsTriangulation T' ∧ fanDegree T' = fanDegree T + 1 := by
  have h0 : ((0 : ℕ) : ZMod m) = 0 := Nat.cast_zero
  obtain ⟨k, hk, hkT⟩ : ∃ k ∈ Finset.Icc 2 (m - 2), s((0 : ZMod m), (k : ZMod m)) ∉ T := by
    by_contra! h
    unfold fanDegree at hdeg
    rw [Finset.filter_true_of_mem h, Nat.card_Icc] at hdeg
    omega
  rw [Finset.mem_Icc] at hk
  have hside : ∀ j, j < m → (j = 1 ∨ j = m - 1) → s((0 : ZMod m), (j : ZMod m)) ∈ segments T :=
    fun j hj h => mem_segments.2 (Or.inr (by
      rw [← h0, isSide_natCast_iff_flips (by omega) (by omega) hj]; omega))
  obtain ⟨u, w, hu1, huk, hkw, hwm, hPu, hPw, hgap⟩ :=
    exists_gap_flips (P := fun j => s((0 : ZMod m), (j : ZMod m)) ∈ segments T)
      (hside 1 (by omega) (by simp)) (hside (m - 1) (by omega) (by simp))
      (fun h => hkT (mem_of_mem_segments_flips h (by
        rw [← h0, isDiagonal_natCast_iff_flips (by omega) (by omega) (by omega)]; omega)))
      (by omega) (by omega)
  have hγ := mem_of_fan_gap_flips hm hT hu1 (by omega) hwm hPu hPw hgap
  obtain ⟨⟨b, ⟨hb, hub, hbw⟩, -⟩, -⟩ := IsTriangulation.existsUnique_apex_of_mem hm hT hγ
  have hq : IsFlipQuadrilateral T (u : ZMod m) b (w : ZMod m) 0 := by
    refine ⟨hb, ?_, hub, hbw, by rw [Sym2.eq_swap]; exact hPw, hPu⟩
    rw [← h0, sbtw_natCast_iff hwm (by omega) (by omega : u < m)]
    omega
  have hflip := hq.isFlipReplacement hT hγ
  obtain ⟨bn, hbn, rfl⟩ := exists_natCast_eq b
  rw [sbtw_natCast_iff (by omega : u < m) hbn hwm] at hb
  refine ⟨_, ⟨_, _, hflip, rfl⟩, hflip.2.2.2.2, ?_⟩
  unfold fanDegree
  rw [filter_mem_flipTriangulation_fan hu1 (by omega) (by omega) hwm, Finset.card_insert_of_notMem]
  simp only [Finset.mem_filter, not_and]
  exact fun _ h => hgap bn (by omega) (by omega) (mem_segments.2 (Or.inl h))

/-- Every triangulation is joined to the fan by flips. -/
private theorem reflTransGen_isFlip_fanTriangulation (hm : 4 ≤ m) :
    ∀ n : ℕ, ∀ T : Finset (Sym2 (ZMod m)), IsTriangulation T → fanDegree T + n = m - 3 →
      Relation.ReflTransGen IsFlip T (fanTriangulation m) := by
  intro n
  induction n with
  | zero =>
    intro T hT hdeg
    rw [eq_fanTriangulation_of_fanDegree hm hT hdeg]
  | succ n ih =>
    intro T hT hdeg
    obtain ⟨T', hflip, hT', hdeg'⟩ := exists_isFlip_fanDegree hm hT (by omega)
    exact Relation.ReflTransGen.head hflip (ih T' hT' (by omega))

omit [NeZero m] in
/-- The number of diagonals through `0` is at most `m - 3`. -/
private theorem fanDegree_le (T : Finset (Sym2 (ZMod m))) : fanDegree T ≤ m - 3 := by
  unfold fanDegree
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Nat.card_Icc]
  omega

/-- **Any two triangulations are joined by flips**: there are triangulations
`T = U₀, U₁, …, U_r = T'` with `U_s` obtained from `U_{s-1}` by the flip at some diagonal of
`U_{s-1}`. -/
@[cluster_algebras "lem_flip_connected"]
theorem IsTriangulation.reflTransGen_isFlip (hm : 4 ≤ m) {T T' : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) (hT' : IsTriangulation T') : Relation.ReflTransGen IsFlip T T' :=
  (reflTransGen_isFlip_fanTriangulation hm _ T hT (Nat.add_sub_cancel' (fanDegree_le T))).trans
    ((reflTransGen_isFlip_fanTriangulation hm _ T' hT'
      (Nat.add_sub_cancel' (fanDegree_le T'))).swap.mono fun _ _ h => h.symm)

/-- **A triangulation of the `m`-gon has `m - 3` diagonals.** -/
@[cluster_algebras "lem_triangulation_card"]
theorem IsTriangulation.card_eq (hm : 4 ≤ m) {T : Finset (Sym2 (ZMod m))}
    (hT : IsTriangulation T) : T.card = m - 3 := by
  have h := IsTriangulation.reflTransGen_isFlip hm hT (isTriangulation_fanTriangulation hm)
  rw [← card_fanTriangulation hm]
  generalize fanTriangulation m = F at h ⊢
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    obtain ⟨γ, γ', ⟨-, hγ, -, hγ', -⟩, rfl⟩ := hbc
    rw [ih, flipTriangulation, Finset.card_insert_of_notMem
      (fun h => hγ' (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hγ,
      Nat.sub_add_cancel (Finset.card_pos.2 ⟨γ, hγ⟩)]

/-- **Non-crossing sets of diagonals extend to triangulations, (a).** -/
@[cluster_algebras "lem_noncrossing_extends"]
theorem exists_isTriangulation_superset {S : Finset (Sym2 (ZMod m))}
    (hS : ∀ e ∈ S, IsDiagonal e) (hnc : ∀ e ∈ S, ∀ f ∈ S, ¬Cross e f) :
    ∃ T, IsTriangulation T ∧ S ⊆ T := by
  classical
  set F := (Finset.univ.filter fun e : Sym2 (ZMod m) => IsDiagonal e).powerset.filter
    fun U => S ⊆ U ∧ ∀ e ∈ U, ∀ f ∈ U, ¬Cross e f with hF
  have hmem : ∀ U, U ∈ F ↔ (∀ e ∈ U, IsDiagonal e) ∧ S ⊆ U ∧ ∀ e ∈ U, ∀ f ∈ U, ¬Cross e f := by
    intro U
    simp only [hF, Finset.mem_filter, Finset.mem_powerset]
    exact and_congr_left' ⟨fun h e he => (Finset.mem_filter.1 (h he)).2,
      fun h e he => Finset.mem_filter.2 ⟨Finset.mem_univ _, h e he⟩⟩
  obtain ⟨T, hTF, hmax⟩ := F.exists_max_image Finset.card ⟨S, (hmem S).2 ⟨hS, subset_rfl, hnc⟩⟩
  obtain ⟨hTd, hST, hTnc⟩ := (hmem T).1 hTF
  refine ⟨T, ⟨hTd, hTnc, fun e he heT => ?_⟩, hST⟩
  by_contra! hcr
  have hins : insert e T ∈ F := by
    refine (hmem _).2 ⟨?_, hST.trans (Finset.subset_insert _ _), ?_⟩
    · intro f hf
      rcases Finset.mem_insert.1 hf with rfl | hf
      exacts [he, hTd f hf]
    · intro f hf g hg
      rw [Finset.mem_insert] at hf hg
      rcases hf with rfl | hf <;> rcases hg with rfl | hg
      exacts [not_cross_self _, hcr _ hg, fun h => hcr _ hf h.symm, hTnc _ hf _ hg]
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem heT] at this
  omega

/-- **Non-crossing sets of diagonals extend to triangulations, (b).** A pairwise non-crossing set
of `m - 3` diagonals is a triangulation. -/
@[cluster_algebras "lem_noncrossing_extends"]
theorem isTriangulation_of_card_eq (hm : 4 ≤ m) {S : Finset (Sym2 (ZMod m))}
    (hS : ∀ e ∈ S, IsDiagonal e) (hnc : ∀ e ∈ S, ∀ f ∈ S, ¬Cross e f) (hcard : S.card = m - 3) :
    IsTriangulation S := by
  obtain ⟨T, hT, hST⟩ := exists_isTriangulation_superset hS hnc
  rwa [Finset.eq_of_subset_of_card_le hST (by rw [IsTriangulation.card_eq hm hT, hcard])]

/-- **Two crossing diagonals are related by a flip**: there is a triangulation `T ∋ δ` in which
the replacement of `δ` is `δ'`. -/
@[cluster_algebras "lem_crossing_pair_flip"]
theorem exists_isFlipReplacement_of_cross {δ δ' : Sym2 (ZMod m)}
    (hδ : IsDiagonal δ) (hδ' : IsDiagonal δ') (h : Cross δ δ') :
    ∃ T, IsFlipReplacement T δ δ' := by
  classical
  obtain ⟨a, c, b, d, rfl, rfl, hb, hd⟩ := h
  obtain ⟨⟨hab, hac, had, hbc, hbd, hcd⟩, -, -, -⟩ := quadrilateral_cross hb hd
  set R : Finset (Sym2 (ZMod m)) := {s(a, b), s(b, c), s(c, d), s(d, a)} with hR
  set S := insert s(a, c) (R.filter IsDiagonal) with hSdef
  have hS6 : ∀ e ∈ S, e ∈ ({s(a, b), s(b, c), s(c, d), s(d, a), s(a, c), s(b, d)} :
      Finset (Sym2 (ZMod m))) := by
    intro e he
    simp only [hSdef, hR, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton] at he ⊢
    tauto
  have hbdS : s(b, d) ∉ S := by
    simp only [hSdef, hR, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton, Sym2.eq_iff]
    tauto
  obtain ⟨T, hT, hST⟩ := exists_isTriangulation_superset (S := S)
    (fun e he => by
      simp only [hSdef, Finset.mem_insert, Finset.mem_filter] at he
      rcases he with rfl | ⟨-, he⟩
      exacts [hδ, he])
    (fun e he f hf hcr => by
      rcases quadrilateral_eq_of_cross hb hd e (hS6 e he) f (hS6 f hf) hcr with
        ⟨-, rfl⟩ | ⟨rfl, -⟩
      exacts [hbdS hf, hbdS he])
  have hrim : ∀ e ∈ R, e ∈ segments T := by
    intro e he
    by_cases hdiag : IsDiagonal e
    · exact mem_segments.2 (Or.inl (hST (Finset.mem_insert_of_mem
        (Finset.mem_filter.2 ⟨he, hdiag⟩))))
    · refine mem_segments.2 (Or.inr (not_not.1 fun hside => hdiag ⟨?_, hside⟩))
      simp only [hR, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp only [IsSegment, Sym2.mk_isDiag_iff] <;> tauto
  have hq : IsFlipQuadrilateral T a b c d :=
    ⟨hb, hd, hrim _ (by simp [hR]), hrim _ (by simp [hR]), hrim _ (by simp [hR]),
      hrim _ (by simp [hR])⟩
  exact ⟨T, hq.isFlipReplacement hT (hST (Finset.mem_insert_self _ _))⟩

/-! ### Counting -/

/-- **The number of triangulations**: for `m ≥ 3` the convex `m`-gon has exactly `c_{m-2}`
triangulations. -/
@[cluster_algebras "lem_triangulation_count"]
theorem encard_setOf_isTriangulation (hm : 3 ≤ m) :
    {T : Finset (Sym2 (ZMod m)) | IsTriangulation T}.encard = catalanNumber (m - 2) := by
  have hbij := bijOn_basePosTri (0 : ZMod m)
  have hset : {S | IsIntervalTriangulation 0 ((m : ℤ) - 1) S} =
      ↑(intervalTriangulations 0 ((m : ℤ) - 1)) := by
    ext S
    simp [mem_intervalTriangulations]
  rw [← hbij.injOn.encard_image, hbij.image_eq, hset, Set.encard_coe_eq_coe_finsetCard,
    ← intervalTriangulationCount, intervalTriangulationCount_eq_catalanNumber (by omega)]
  congr
  omega

omit [NeZero m] in
private theorem one_ne_zero_flips (hm : 2 ≤ m) : (1 : ZMod m) ≠ 0 := by
  intro h
  have h₁ : ((1 : ℕ) : ZMod m) = ((0 : ℕ) : ZMod m) := by rw [Nat.cast_one, Nat.cast_zero, h]
  rw [natCast_inj_of_lt (by omega) (by omega)] at h₁
  omega

omit [NeZero m] in
/-- **The sides of the `m`-gon**: `ℓ ↦ {ℓ, ℓ+1}` is a bijection from `ZMod m` onto the sides. -/
@[cluster_algebras "lem_diagonal_count"]
theorem bijective_side (hm : 3 ≤ m) :
    Function.Bijective fun l : ZMod m =>
      (⟨s(l, l + 1), l, rfl⟩ : {σ : Sym2 (ZMod m) // IsSide σ}) := by
  refine ⟨fun l l' h => ?_, fun ⟨_, l, rfl⟩ => ⟨l, rfl⟩⟩
  simp only [Subtype.mk.injEq, Sym2.eq_iff] at h
  rcases h with ⟨h, -⟩ | ⟨h₁, h₂⟩
  · exact h
  · have h₃ : (2 : ZMod m) = ((0 : ℕ) : ZMod m) := by
      rw [Nat.cast_zero]
      linear_combination h₂ - h₁
    rw [← Nat.cast_ofNat, natCast_inj_of_lt (by omega) (by omega)] at h₃
    omega

/-- **The number of sides**: the `m`-gon has `m` sides. -/
@[cluster_algebras "lem_diagonal_count"]
theorem card_filter_isSide (hm : 3 ≤ m) :
    (Finset.univ.filter fun σ : Sym2 (ZMod m) => IsSide σ).card = m := by
  rw [← Fintype.card_subtype, ← Fintype.card_of_bijective (bijective_side hm), ZMod.card]

/-- **The number of diagonals**: the `m`-gon has `m(m-3)/2` diagonals. -/
@[cluster_algebras "lem_diagonal_count"]
theorem card_filter_isDiagonal (hm : 3 ≤ m) :
    (Finset.univ.filter fun σ : Sym2 (ZMod m) => IsDiagonal σ).card = m * (m - 3) / 2 := by
  have hside : ∀ σ : Sym2 (ZMod m), IsSide σ → IsSegment σ := by
    rintro σ ⟨i, rfl⟩
    rw [IsSegment, Sym2.mk_isDiag_iff]
    exact fun h => one_ne_zero_flips (m := m) (by omega) (by linear_combination -h)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun σ : Sym2 (ZMod m) => IsSegment σ) IsSide
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have h₁ : (Finset.univ.filter fun σ : Sym2 (ZMod m) => IsSegment σ ∧ IsSide σ) =
      Finset.univ.filter fun σ => IsSide σ :=
    Finset.filter_congr fun σ _ => ⟨fun h => h.2, fun h => ⟨hside σ h, h⟩⟩
  have h₂ : (Finset.univ.filter fun σ : Sym2 (ZMod m) => IsSegment σ ∧ ¬IsSide σ) =
      Finset.univ.filter fun σ => IsDiagonal σ :=
    Finset.filter_congr fun σ _ => Iff.rfl
  have h₃ : (Finset.univ.filter fun σ : Sym2 (ZMod m) => IsSegment σ).card = m.choose 2 := by
    rw [← Fintype.card_subtype]
    have := Sym2.card_subtype_not_diag (α := ZMod m)
    rwa [ZMod.card] at this
  rw [h₁, h₂, h₃, card_filter_isSide hm, Nat.choose_two_right] at hsplit
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have h₄ : (k + 3) * (k + 3 - 1) = (k + 3) * (k + 3 - 3) + (k + 3) * 2 := by
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 3 = k by omega]
    ring
  rw [h₄, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)] at hsplit
  omega

/-! ### A triangulation for every orientation of a path -/

/-- `d₁, …, dₙ` (here `d 0, …, d (n-1)`) are pairwise distinct and form a triangulation `T` of the
`(n+3)`-gon whose quiver restricted to the diagonals is the path `d₁ — d₂ — ⋯ — dₙ` oriented by
`ε`: `β_T(d_p, d_{p+1}) = ε_p`, `β_T(d_{p+1}, d_p) = -ε_p`, and `β_T(d_p, d_q) = 0` for
`|p - q| ≠ 1`, where `β_T` is the signed count of the arrows of `Q(T)`. -/
def IsPathListing {n : ℕ} (d : Fin n → Sym2 (ZMod (n + 3))) (ε : Fin n → ℤ) : Prop :=
  Function.Injective d ∧ IsTriangulation (Finset.univ.image d) ∧
    ∀ p q : Fin n, signedCount (polygonArrows (Finset.univ.image d)) (d p) (d q) =
      if (q : ℕ) = p + 1 then ε p else if (p : ℕ) = q + 1 then -ε q else 0

/-- Sides between residues of natural numbers, in either order. -/
private theorem isSide_natCast_iff'_flips (hm : 3 ≤ m) {x y : ℕ} (hx : x < m) (hy : y < m) :
    IsSide s((x : ZMod m), (y : ZMod m)) ↔
      y = x + 1 ∨ x = y + 1 ∨ (x = 0 ∧ y = m - 1) ∨ (y = 0 ∧ x = m - 1) := by
  rcases lt_trichotomy x y with h | rfl | h
  · rw [isSide_natCast_iff_flips hm h hy]
    omega
  · refine ⟨fun h => absurd ?_ (one_ne_zero_flips (m := m) (by omega)), fun h => by omega⟩
    obtain ⟨i, hi⟩ := h
    rcases Sym2.eq_iff.1 hi with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · linear_combination h₁ - h₂
    · linear_combination h₂ - h₁
  · rw [Sym2.eq_swap, isSide_natCast_iff_flips hm h hx]
    omega

/-- With no side among `σ`, the arrow count `a(σ, σ')` is the number of arrow triangles. -/
private theorem polygonArrows_eq_card_flips {T : Finset (Sym2 (ZMod m))} {σ σ' : Sym2 (ZMod m)}
    (hσ : ¬IsSide σ) : polygonArrows T σ σ' = (arrowTriangles T σ σ').card :=
  polygonArrows_eq_card_arrowTriangles T fun h => hσ h.1

/-- No arrow triangle from `σ` to `σ'`. -/
private theorem arrowTriangles_eq_empty_flips {T : Finset (Sym2 (ZMod m))}
    {σ σ' : Sym2 (ZMod m)}
    (h : ∀ a b c : ZMod m, sbtw a b c → σ = s(a, b) → σ' = s(b, c) → s(c, a) ∈ segments T →
      False) : arrowTriangles T σ σ' = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun t ht => ?_
  obtain ⟨⟨-, htri⟩, a, b, c, hcw, hσ, hσ', ha, -, hc⟩ := mem_arrowTriangles.1 ht
  refine h a b c hcw hσ hσ' (htri c hc a ha fun hca => ?_)
  subst hca
  exact sbtw_irrefl_left_right hcw

/-- A triangle carrying a clockwise listing `(a, b, c)` is the only arrow triangle from
`s(a, b)` to `s(b, c)`. -/
private theorem arrowTriangles_eq_singleton_flips {T : Finset (Sym2 (ZMod m))}
    {t₀ : Finset (ZMod m)} {a b c : ZMod m} (ht₀ : IsTriangle T t₀) (hcw : sbtw a b c)
    (ha : a ∈ t₀) (hb : b ∈ t₀) (hc : c ∈ t₀) : arrowTriangles T s(a, b) s(b, c) = {t₀} := by
  have hab : a ≠ b := fun h => by subst h; exact sbtw_irrefl_left hcw
  have hbc : b ≠ c := fun h => by subst h; exact sbtw_irrefl_right hcw
  have hac : a ≠ c := fun h => by subst h; exact sbtw_irrefl_left_right hcw
  have hne : s(a, b) ≠ s(b, c) := by
    rw [Ne, Sym2.eq_iff]
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    exacts [hab h, hac h]
  ext t
  rw [mem_arrowTriangles, Finset.mem_singleton]
  constructor
  · rintro ⟨htri, a', b', c', -, h₁, h₂, ha', hb', hc'⟩
    refine IsTriangle.eq_of_mem_sym2 (σ := s(a, b)) (σ' := s(b, c))
      (by rwa [Sym2.mk_isDiag_iff]) (by rwa [Sym2.mk_isDiag_iff]) hne htri ht₀ ?_ ?_
      (Finset.mk_mem_sym2_iff.2 ⟨ha, hb⟩) (Finset.mk_mem_sym2_iff.2 ⟨hb, hc⟩)
    · exact h₁ ▸ Finset.mk_mem_sym2_iff.2 ⟨ha', hb'⟩
    · exact h₂ ▸ Finset.mk_mem_sym2_iff.2 ⟨hb', hc'⟩
  · rintro rfl
    exact ⟨ht₀, a, b, c, hcw, rfl, rfl, ha, hb, hc⟩

/-- Three distinct vertices pairwise joined by segments of `T` form a triangle of `T`. -/
private theorem isTriangle_of_segments_flips {T : Finset (Sym2 (ZMod m))} {x y z : ZMod m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (h₁ : s(x, y) ∈ segments T)
    (h₂ : s(y, z) ∈ segments T) (h₃ : s(x, z) ∈ segments T) : IsTriangle T {x, y, z} := by
  refine ⟨Finset.card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩, fun u hu v hv huv => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first
    | exact absurd rfl huv
    | assumption
    | (rw [Sym2.eq_swap]; assumption)

/-- The diagonal `s(l p, l p + p + 2)` of the `(n+3)`-gon whose left end is at position `l p`. -/
private def posDiag {n : ℕ} (l : ℕ → ℕ) (p : Fin n) : Sym2 (ZMod (n + 3)) :=
  s(((l p : ℕ) : ZMod (n + 3)), ((l p + p + 2 : ℕ) : ZMod (n + 3)))

private theorem posDiag_eq_iff {n : ℕ} {l : ℕ → ℕ} {p : Fin n} (hp : l p + p + 2 ≤ n + 1)
    {x y : ℕ} (hx : x < n + 3) (hy : y < n + 3) :
    posDiag l p = s((x : ZMod (n + 3)), (y : ZMod (n + 3))) ↔
      (l p = x ∧ l p + p + 2 = y) ∨ (l p = y ∧ l p + p + 2 = x) :=
  sym2_natCast_eq_iff (by omega) (by omega) hx hy

private theorem isDiagonal_posDiag {n : ℕ} {l : ℕ → ℕ} {p : Fin n} (hp : l p + p + 2 ≤ n + 1) :
    IsDiagonal (posDiag l p) := by
  unfold posDiag
  rw [isDiagonal_natCast_iff_flips (by omega) (by omega) (by omega)]
  omega

/-- Diagonals `s(l p, l p + p + 2)` nested as `p` grows are pairwise distinct and form a
triangulation of the `(n+3)`-gon. -/
private theorem isTriangulation_image_posDiag {n : ℕ} (hn : 1 ≤ n) {l : ℕ → ℕ}
    (hr : ∀ p, p < n → l p + p + 2 ≤ n + 1)
    (hmono : ∀ p q, p ≤ q → q < n → l q ≤ l p ∧ l p + p ≤ l q + q) :
    Function.Injective (posDiag (n := n) l) ∧
      IsTriangulation (Finset.univ.image (posDiag (n := n) l)) := by
  have hinj : Function.Injective (posDiag (n := n) l) := by
    intro p q h
    have := hr p p.2
    have := hr q q.2
    unfold posDiag at h
    rw [sym2_natCast_eq_iff (a := l p) (b := l p + p + 2) (c := l q) (d := l q + q + 2)
      (by omega) (by omega) (by omega) (by omega)] at h
    exact Fin.ext (by omega)
  refine ⟨hinj, isTriangulation_of_card_eq (by omega) ?_ ?_ ?_⟩
  · intro e he
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 he
    exact isDiagonal_posDiag (hr p p.2)
  · intro e he f hf
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hf
    have := hr p p.2
    have := hr q q.2
    unfold posDiag
    rw [cross_natCast_iff_flips (by omega) (by omega) (by omega) (by omega)]
    rcases le_total (p : ℕ) q with h | h
    · have := hmono p q h q.2
      omega
    · have := hmono q p h p.2
      omega
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    omega

/-- There is no arrow from `d p` to `d q` in the triangulation of the `d k = s(l k, l k + k + 2)`
when no triangle `{a, b, c}` listed clockwise has `d p = {a, b}`, `d q = {b, c}` and `{c, a}` a
segment. -/
private theorem polygonArrows_posDiag_eq_zero {n : ℕ} {l : ℕ → ℕ}
    (hr : ∀ p, p < n → l p + p + 2 ≤ n + 1) (p q : Fin n)
    (H : ∀ a b c k : ℕ, a < n + 3 → b < n + 3 → c < n + 3 → k < n →
      ((a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)) →
      ((l p = a ∧ l p + p + 2 = b) ∨ (l p = b ∧ l p + p + 2 = a)) →
      ((l q = b ∧ l q + q + 2 = c) ∨ (l q = c ∧ l q + q + 2 = b)) →
      (((l k = c ∧ l k + k + 2 = a) ∨ (l k = a ∧ l k + k + 2 = c)) ∨
        (a = c + 1 ∨ c = a + 1 ∨ (c = 0 ∧ a = n + 2) ∨ (a = 0 ∧ c = n + 2))) → False) :
    polygonArrows (Finset.univ.image (posDiag l)) (posDiag l p) (posDiag l q) = 0 := by
  rw [polygonArrows_eq_card_flips (isDiagonal_posDiag (hr p p.2)).2, Finset.card_eq_zero]
  refine arrowTriangles_eq_empty_flips fun a b c hcw h₁ h₂ h₃ => ?_
  obtain ⟨a, ha, rfl⟩ := exists_natCast_eq a
  obtain ⟨b, hb, rfl⟩ := exists_natCast_eq b
  obtain ⟨c, hc, rfl⟩ := exists_natCast_eq c
  rw [sbtw_natCast_iff ha hb hc] at hcw
  rw [posDiag_eq_iff (hr p p.2) ha hb] at h₁
  rw [posDiag_eq_iff (hr q q.2) hb hc] at h₂
  rcases mem_segments.1 h₃ with hk | hside
  · obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hk
    rw [posDiag_eq_iff (hr k k.2) hc ha] at hk
    exact H a b c k ha hb hc k.2 hcw h₁ h₂ (Or.inl hk)
  · rw [isSide_natCast_iff'_flips (by omega) hc ha] at hside
    exact H a b c 0 ha hb hc p.pos hcw h₁ h₂ (Or.inr (by omega))

/-- There is exactly one arrow from `d p = {x, y}` to `d q = {y, z}` in the triangulation of the
`d k = s(l k, l k + k + 2)` when `(x, y, z)` is clockwise and `{z, x}` is a side. -/
private theorem polygonArrows_posDiag_eq_one {n : ℕ} {l : ℕ → ℕ}
    (hr : ∀ p, p < n → l p + p + 2 ≤ n + 1) (p q : Fin n) (x y z : ℕ) (hx : x < n + 3)
    (hy : y < n + 3) (hz : z < n + 3) (hcw : (x < y ∧ y < z) ∨ (y < z ∧ z < x) ∨ (z < x ∧ x < y))
    (h₁ : (l p = x ∧ l p + p + 2 = y) ∨ (l p = y ∧ l p + p + 2 = x))
    (h₂ : (l q = y ∧ l q + q + 2 = z) ∨ (l q = z ∧ l q + q + 2 = y))
    (hxz : z = x + 1 ∨ x = z + 1) :
    polygonArrows (Finset.univ.image (posDiag l)) (posDiag l p) (posDiag l q) = 1 := by
  have e₁ := (posDiag_eq_iff (hr p p.2) hx hy).2 h₁
  have e₂ := (posDiag_eq_iff (hr q q.2) hy hz).2 h₂
  have hxy' : (x : ZMod (n + 3)) ≠ y := by rw [Ne, natCast_inj_of_lt hx hy]; omega
  have hxz' : (x : ZMod (n + 3)) ≠ z := by rw [Ne, natCast_inj_of_lt hx hz]; omega
  have hyz' : (y : ZMod (n + 3)) ≠ z := by rw [Ne, natCast_inj_of_lt hy hz]; omega
  have hdT : ∀ p, posDiag l p ∈ segments (Finset.univ.image (posDiag (n := n) l)) := fun p =>
    mem_segments.2 (Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ p)))
  have htri : IsTriangle (Finset.univ.image (posDiag l))
      {(x : ZMod (n + 3)), (y : ZMod (n + 3)), (z : ZMod (n + 3))} :=
    isTriangle_of_segments_flips hxy' hxz' hyz' (e₁ ▸ hdT p) (e₂ ▸ hdT q)
      (mem_segments.2 (Or.inr ((isSide_natCast_iff'_flips (by omega) hx hz).2 (by omega))))
  rw [polygonArrows_eq_card_flips (isDiagonal_posDiag (hr p p.2)).2, e₁, e₂,
    arrowTriangles_eq_singleton_flips htri ((sbtw_natCast_iff hx hy hz).2 hcw)
      (by simp) (by simp) (by simp), Finset.card_singleton]

/-- The combinatorial core of `exists_isPathListing`: positions `l p` of the left ends, with
`d p = s(l p, l p + p + 2)`, nested as prescribed by `ε`, give a path listing. -/
private theorem isPathListing_of_positions_flips {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → ℤ)
    (hε : ∀ p : Fin n, (p : ℕ) + 1 < n → ε p = 1 ∨ ε p = -1) (l : ℕ → ℕ)
    (hr : ∀ p, p < n → l p + p + 2 ≤ n + 1)
    (hmono : ∀ p q, p ≤ q → q < n → l q ≤ l p ∧ l p + p ≤ l q + q)
    (hstep : ∀ p : Fin n, (p : ℕ) + 1 < n →
      (ε p = 1 → l p = l (p + 1) + 1) ∧ (ε p ≠ 1 → l p = l (p + 1))) :
    IsPathListing (posDiag l) ε := by
  have facts : ∀ k, k < n → l k + k + 2 ≤ n + 1 ∧ l k ≤ l 0 ∧ l 0 ≤ l k + k := fun k hk =>
    ⟨hr k hk, (hmono 0 k (Nat.zero_le _) hk).1, by simpa using (hmono 0 k (Nat.zero_le _) hk).2⟩
  have hL : ∀ p : Fin n, l p < n + 3 := fun p => by have := hr p p.2; omega
  have hR : ∀ p : Fin n, l p + p + 2 < n + 3 := fun p => by have := hr p p.2; omega
  have hadj : ∀ p q : Fin n, (q : ℕ) = p + 1 →
      signedCount (polygonArrows (Finset.univ.image (posDiag l))) (posDiag l p) (posDiag l q) =
        ε p := by
    intro p q hpq
    have hp1 : (p : ℕ) + 1 < n := hpq ▸ q.2
    obtain ⟨hs₁, hs₂⟩ := hstep p hp1
    rw [← hpq] at hs₁ hs₂
    have fp := facts p p.2
    have fq := facts q q.2
    unfold signedCount
    rcases hε p hp1 with he | he
    · have hl := hs₁ he
      rw [polygonArrows_posDiag_eq_one hr p q (l p) (l p + p + 2) (l q) (hL p) (hR p) (hL q)
        (by omega) (by omega) (by omega) (by omega), polygonArrows_posDiag_eq_zero hr q p
        (fun a b c k _ _ _ hk h₀ h₁ h₂ h₃ => by have := facts k hk; omega), he]
      norm_num
    · have hl := hs₂ (by rw [he]; norm_num)
      rw [polygonArrows_posDiag_eq_one hr q p (l q + q + 2) (l q) (l p + p + 2) (hR q) (hL q)
        (hR p) (by omega) (by omega) (by omega) (by omega), polygonArrows_posDiag_eq_zero hr p q
        (fun a b c k _ _ _ hk h₀ h₁ h₂ h₃ => by have := facts k hk; omega), he]
      norm_num
  obtain ⟨hinj, hTri⟩ := isTriangulation_image_posDiag hn hr hmono
  refine ⟨hinj, hTri, fun p q => ?_⟩
  split_ifs with h₁ h₂
  · exact hadj p q h₁
  · rw [show signedCount (polygonArrows (Finset.univ.image (posDiag l))) (posDiag l p)
        (posDiag l q) = -signedCount (polygonArrows (Finset.univ.image (posDiag l)))
        (posDiag l q) (posDiag l p) by unfold signedCount; ring, hadj q p h₂]
  · have fp := facts p p.2
    have fq := facts q q.2
    unfold signedCount
    rw [polygonArrows_posDiag_eq_zero hr p q
        (fun a b c k _ _ _ hk h₀ h₃ h₄ h₅ => by have := facts k hk; omega),
      polygonArrows_posDiag_eq_zero hr q p
        (fun a b c k _ _ _ hk h₀ h₃ h₄ h₅ => by have := facts k hk; omega)]
    simp

/-- **A triangulation for every orientation of a path.** For `n ≥ 1` and signs
`ε₁, …, ε_{n-1} ∈ {1, -1}` there are pairwise distinct diagonals `d₁, …, dₙ` of the
`(n+3)`-gon forming a triangulation `T` with `β_T(d_p, d_q) = ε_p` if `q = p + 1`, `-ε_q` if
`p = q + 1`, and `0` otherwise. -/
@[cluster_algebras "lem_path_triangulation"]
theorem exists_isPathListing {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → ℤ)
    (hε : ∀ p : Fin n, (p : ℕ) + 1 < n → ε p = 1 ∨ ε p = -1) :
    ∃ d : Fin n → Sym2 (ZMod (n + 3)), IsPathListing d ε := by
  set e : ℕ → ℕ := fun i => if h : i < n then (if ε ⟨i, h⟩ = 1 then 1 else 0) else 0 with he
  have he₁ : ∀ i, e i ≤ 1 := fun i => by
    simp only [he]
    split_ifs <;> omega
  set l : ℕ → ℕ := fun p => ∑ i ∈ Finset.Ico p (n - 1), e i with hl
  have hsum : ∀ p q, ∑ i ∈ Finset.Ico p q, e i ≤ q - p := fun p q => by
    refine (Finset.sum_le_card_nsmul _ _ 1 fun i _ => he₁ i).trans ?_
    simp
  have hsplit : ∀ p q, p ≤ q → q ≤ n - 1 → l p = ∑ i ∈ Finset.Ico p q, e i + l q :=
    fun p q hpq hq => (Finset.sum_Ico_consecutive _ hpq hq).symm
  refine ⟨_, isPathListing_of_positions_flips hn ε hε l ?_ ?_ ?_⟩
  · intro p hp
    have := hsum p (n - 1)
    simp only [hl]
    omega
  · intro p q hpq hq
    have h₁ := hsplit p q hpq (by omega)
    have h₂ := hsum p q
    omega
  · intro p hp
    have h₁ := hsplit p (p + 1) (by omega) (by omega)
    rw [Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self, Finset.sum_empty, zero_add] at h₁
    have h₂ : e p = if ε p = 1 then 1 else 0 := by simp [he, p.2]
    rw [h₂] at h₁
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [if_pos h] at h₁
      omega
    · rw [if_neg h] at h₁
      omega

end TypeA

end ClusterAlgebras

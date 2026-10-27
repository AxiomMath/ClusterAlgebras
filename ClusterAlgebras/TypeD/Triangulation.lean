/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeD.Arcs
public import ClusterAlgebras.TypeD.Run

/-!
# Tagged triangulations of a once-punctured polygon

The radii of a tagged triangulation cut the punctured polygon into *sectors*, each sector run
carries a triangulation of an integer run, and a tagged triangulation is of one of three kinds,
`P_+`, `P_-` (all radii of one tag, at least two positions) or the digon kind (the two radii at
one position). From this, every tagged triangulation has `n` arcs and every arc of it has
exactly one replacement.

## Main definitions

* `ClusterAlgebras.TypeD.gap`, `succ`, `pred`, `sector`, `outerArc`: successors, gaps, sectors
  and outer arcs of a set `R` of positions.
* `ClusterAlgebras.TypeD.radiusSet`, `sectorChords`: the positions of the radii of `T` and the
  chords `T_R(a)` of a sector run whose segments lie in `T`.
* `ClusterAlgebras.TypeD.IsKindP`, `IsDigonKind`: the three kinds.
* `ClusterAlgebras.TypeD.dFlip`, `IsDFlipReplacement`: flips of tagged triangulations.

## Main results

* `ClusterAlgebras.TypeD.isTaggedTriangulation_iff_kind`: the three kinds.
* `ClusterAlgebras.TypeD.IsTaggedTriangulation.card_eq`: a tagged triangulation has `n` arcs.
* `ClusterAlgebras.TypeD.IsTaggedTriangulation.existsUnique_isDFlipReplacement`: every arc has
  exactly one replacement, described explicitly in five cases.

## Implementation notes

* Indices start at `0` (see `ClusterAlgebras.TypeD.Arcs`). A position `a : Fin n` is used as
  the integer `(a : ℤ) ∈ [0, n - 1]`, so the sector run of `a` is `[a, a + g_R(a)]`.
* The gap `g_R(a)` is the least `t ∈ [1, n]` with `a + t ∈ R` (mod `n`), and `n` if there is
  none; for `a ∈ R` this is `r_{s+1} - r_s` for consecutive elements `r_s < r_{s+1}` of `R`
  (`gap_spec`). The predecessor is defined symmetrically, and is the element whose successor
  is `a` (`succ_pred`).
* The set `T_R(a)` is `sectorChords T R a`; the segment `s(c)` of a chord `c` is the ordinary
  arc `ordArc c.1 c.2`.
* `IsKindP T τ R` takes the tag `τ` and the radius set `R`; `IsDigonKind T a` takes the
  doubled position `a`.
* `IsDFlipReplacement T γ γ'` says that `γ ∈ T`, `γ' ∉ T` and `(T \ {γ}) ∪ {γ'}` is a tagged
  triangulation, so `IsTaggedTriangulation.existsUnique_isDFlipReplacement` is its unique
  existence.
-/

@[expose] public section

namespace ClusterAlgebras.TypeD

variable {n : ℕ} [NeZero n]

/-! ### Segments inside a lifted run -/

private theorem npos : (0 : ℤ) < n := Int.natCast_pos.2 (NeZero.pos n)

private theorem vtx_add_coe (x t : ℤ) : (vtx ((vtx x : Fin n) + t) : Fin n) = vtx (x + t) := by
  rw [vtx_eq_vtx_iff, vtx_val, Int.emod_add_emod]

private theorem vtx_sub_coe (x t : ℤ) : (vtx ((vtx x : Fin n) - t) : Fin n) = vtx (x - t) := by
  rw [vtx_eq_vtx_iff, vtx_val, Int.emod_sub_emod]

private theorem exists_eq_add_mul_of_vtx_eq {u v : ℤ} (h : (vtx u : Fin n) = vtx v) :
    ∃ k : ℤ, v = u + k * n := by
  rw [vtx_eq_vtx_iff] at h
  obtain ⟨k, hk⟩ := (Int.ModEq.dvd h : (n : ℤ) ∣ v - u)
  exact ⟨k, by linarith⟩

private theorem eq_of_vtx_eq {u v : ℤ} (h₁ : u ≤ v) (h₂ : v < u + n)
    (h : (vtx u : Fin n) = vtx v) : u = v := by
  obtain ⟨k, rfl⟩ := exists_eq_add_mul_of_vtx_eq h
  have hn := npos (n := n)
  have h1 : k < 1 := lt_of_mul_lt_mul_right (by linarith : k * n < 1 * n) hn.le
  have h2 : 0 ≤ k := le_of_mul_le_mul_right (by linarith : 0 * n ≤ k * n) hn
  obtain rfl : k = 0 := by omega
  simp

private theorem eq_of_vtx_eq' {u v : ℤ} (h₁ : u < v + n) (h₂ : v < u + n)
    (h : (vtx u : Fin n) = vtx v) : u = v := by
  rcases le_total u v with h' | h'
  · exact eq_of_vtx_eq h' h₂ h
  · exact (eq_of_vtx_eq h' h₁ h.symm).symm

private theorem coe_vtx_eq (u : ℤ) : ∃ k : ℤ, ((vtx u : Fin n) : ℤ) = u + k * n :=
  exists_eq_add_mul_of_vtx_eq (vtx_coe _).symm

private theorem cdist_vtx {x y : ℤ} (h₁ : x < y) (h₂ : y < x + n) :
    (cdist (vtx x : Fin n) (vtx y) : ℤ) = y - x :=
  (cdist_vtx_kappa_eq_cut h₁ h₂).1

/-- The shadow of `α(x̄, ȳ)` for `x < y < x + n`. -/
private theorem shadow_eq_image {x y : ℤ} (h₁ : x < y) (h₂ : y < x + n) :
    shadow (vtx x : Fin n) (vtx y) = (intRange x (y - 1)).image vtx := by
  ext b
  have hc := cdist_vtx (n := n) h₁ h₂
  simp only [shadow, Finset.mem_image, Finset.mem_range, mem_intRange, vtx_add_coe]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨x + t, by omega, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨(m - x).toNat, by omega, by congr 1; omega⟩

private theorem interiorVertices_eq_image {x y : ℤ} (h₁ : x < y) (h₂ : y < x + n) :
    interiorVertices (vtx x : Fin n) (vtx y) = (intRange (x + 1) (y - 1)).image vtx := by
  ext b
  have hc := cdist_vtx (n := n) h₁ h₂
  simp only [interiorVertices, Finset.mem_image, Finset.mem_Ioo, mem_intRange, vtx_add_coe]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨x + t, by omega, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨(m - x).toNat, by omega, by congr 1; omega⟩

private theorem ordArc_eq_ordinary {x y : ℤ} (h₁ : 2 ≤ y - x) (h₂ : y - x ≤ n - 1) :
    ∃ h, (ordArc x y : TaggedArc n) = .ordinary (vtx x) (vtx y) h :=
  (seg_eq_arc h₁ h₂).2

private theorem ordArc_congr {x y x' y' : ℤ} (hx : (vtx x : Fin n) = vtx x')
    (hy : (vtx y : Fin n) = vtx y') : (ordArc x y : TaggedArc n) = ordArc x' y' := by
  simp only [ordArc, hx, hy]

private theorem vtx_eq_of_ordArc_eq {x y x' y' : ℤ}
    (h : (ordArc x y : TaggedArc n) = ordArc x' y') : (vtx x : Fin n) = vtx x' := by
  unfold ordArc at h
  split_ifs at h <;> simp_all

private theorem intRange_subset {x y x' y' : ℤ} (h₁ : x' ≤ x) (h₂ : y ≤ y') :
    intRange x y ⊆ intRange x' y' := fun m hm => by
  rw [mem_intRange] at hm ⊢
  omega

/-- Under the injectivity of `vtx` on `[u, v - 1]`, inclusion of images of intervals is inclusion
of the intervals. -/
private theorem image_subset_image_iff {u v x y x' y' : ℤ} (hvu : v - u ≤ n) (hx : u ≤ x)
    (hxy : x ≤ y) (hy : y ≤ v - 1) (hx' : u ≤ x') (hy' : y' ≤ v - 1) :
    (intRange x y).image (vtx : ℤ → Fin n) ⊆ (intRange x' y').image vtx ↔ x' ≤ x ∧ y ≤ y' := by
  constructor
  · intro h
    have key : ∀ m, x ≤ m → m ≤ y → x' ≤ m ∧ m ≤ y' := by
      intro m hm1 hm2
      obtain ⟨m', hm', he⟩ := Finset.mem_image.1
        (h (Finset.mem_image_of_mem vtx (mem_intRange.2 ⟨hm1, hm2⟩)))
      rw [mem_intRange] at hm'
      obtain rfl := eq_of_vtx_eq' (by omega) (by omega) he
      exact hm'
    exact ⟨(key x le_rfl hxy).1, (key y hxy le_rfl).2⟩
  · rintro ⟨h1, h2⟩
    exact Finset.image_subset_image (intRange_subset h1 h2)

private theorem disjoint_image_iff {u v x y x' y' : ℤ} (hvu : v - u ≤ n) (hx : u ≤ x)
    (hxy : x ≤ y) (hy : y ≤ v - 1) (hx' : u ≤ x') (hxy' : x' ≤ y') (hy' : y' ≤ v - 1) :
    Disjoint ((intRange x y).image (vtx : ℤ → Fin n)) ((intRange x' y').image vtx) ↔
      y < x' ∨ y' < x := by
  rw [Finset.disjoint_left]
  constructor
  · intro h
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    exact h (Finset.mem_image_of_mem vtx (mem_intRange.2 ⟨by omega, by omega⟩ :
      max x x' ∈ intRange x y)) (Finset.mem_image_of_mem vtx (mem_intRange.2
        ⟨by omega, by omega⟩))
  · intro h b hb hb'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨m', hm', he⟩ := Finset.mem_image.1 hb'
    rw [mem_intRange] at hm hm'
    have := eq_of_vtx_eq' (by omega) (by omega) he
    omega

private theorem compat_ordArc_of_le {u v : ℤ} (hvu : v - u ≤ n) {c c' : ℤ × ℤ} (h1 : u ≤ c.1)
    (h2 : c.2 ≤ v) (h3 : 2 ≤ c.2 - c.1) (hl : c.2 - c.1 ≤ n - 1) (h1' : u ≤ c'.1)
    (h2' : c'.2 ≤ v) (h3' : 2 ≤ c'.2 - c'.1) (hl' : c'.2 - c'.1 ≤ n - 1) :
    (ordArc c.1 c.2 : TaggedArc n).Compatible (ordArc c'.1 c'.2) ↔ ¬RunCross c c' := by
  obtain ⟨h, e⟩ := ordArc_eq_ordinary (n := n) h3 hl
  obtain ⟨h', e'⟩ := ordArc_eq_ordinary (n := n) h3' hl'
  rw [e, e']
  simp only [TaggedArc.Compatible]
  rw [shadow_eq_image (by omega) (by omega), shadow_eq_image (by omega) (by omega),
    image_subset_image_iff hvu (by omega) (by omega) (by omega) (by omega) (by omega),
    image_subset_image_iff hvu (by omega) (by omega) (by omega) (by omega) (by omega),
    disjoint_image_iff hvu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    RunCross]
  omega

/-- For integers `x < y` with `y - x ≤ n - 1`, the shadow of `s(x, y)` is `{β_m̄ : x ≤ m < y}`. -/
@[cluster_algebras "lem_D_lift_segments"]
theorem shadow_seg {x y : ℤ} (hxy : x < y) (hyx : y - x ≤ n - 1) :
    (seg x y : DSeg n).shadow = (intRange x (y - 1)).image vtx := by
  by_cases h1 : y - x = 1
  · obtain rfl : y = x + 1 := by omega
    rw [seg_eq_boundary]
    ext b
    simp only [DSeg.shadow, Finset.mem_singleton, Finset.mem_image, mem_intRange]
    constructor
    · rintro rfl
      exact ⟨x, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      obtain rfl : m = x := by omega
      rfl
  · obtain ⟨hs, hh, ho⟩ := seg_eq_arc (n := n) (by omega : 2 ≤ y - x) hyx
    rw [hs, ho]
    exact shadow_eq_image hxy (by omega)

/-- **Segments inside a lifted run** (a): `m ↦ m̄` is injective on `[u, v - 1]` when
`v - u ≤ n`. -/
@[cluster_algebras "lem_D_lift_segments"]
theorem injOn_vtx {u v : ℤ} (hvu : v - u ≤ n) :
    Set.InjOn (vtx : ℤ → Fin n) (Set.Icc u (v - 1)) := by
  intro m hm m' hm' h
  simp only [Set.mem_Icc] at hm hm'
  exact eq_of_vtx_eq' (by omega) (by omega) h

/-- **Segments inside a lifted run** (a): `(x, y) ↦ s(x, y)` is injective on the pairs
`u ≤ x < y ≤ v` with `y - x ≤ n - 1`, when `v - u ≤ n`. -/
@[cluster_algebras "lem_D_lift_segments"]
theorem injOn_seg {u v : ℤ} (hvu : v - u ≤ n) :
    Set.InjOn (fun c : ℤ × ℤ => (seg c.1 c.2 : DSeg n))
      {c | u ≤ c.1 ∧ c.1 < c.2 ∧ c.2 ≤ v ∧ c.2 - c.1 ≤ n - 1} := by
  rintro ⟨x, y⟩ ⟨h1, h2, h3, h4⟩ ⟨x', y'⟩ ⟨h1', h2', h3', h4'⟩ h
  simp only at h h1 h2 h3 h4 h1' h2' h3' h4'
  have hs := congrArg DSeg.shadow h
  rw [shadow_seg h2 h4, shadow_seg h2' h4'] at hs
  have a1 := (image_subset_image_iff hvu h1 (by omega) (by omega) h1' (by omega)).1 hs.le
  have a2 := (image_subset_image_iff hvu h1' (by omega) (by omega) h1 (by omega)).1 hs.ge
  simp only [Prod.mk.injEq]
  omega

private theorem isRunChord_iff' {u v : ℤ} {c : ℤ × ℤ} :
    IsRunChord u v c ↔ u ≤ c.1 ∧ c.1 < c.2 ∧ c.2 ≤ v ∧ 2 ≤ c.2 - c.1 ∧ (c.1 ≠ u ∨ c.2 ≠ v) := by
  rw [IsRunChord, Ne, Prod.ext_iff, not_and_or]

omit [NeZero n] in
private theorem IsRunChord.len_le {u v : ℤ} {c : ℤ × ℤ} (hc : IsRunChord u v c)
    (hvu : v - u ≤ n) : c.2 - c.1 ≤ n - 1 := by
  rw [isRunChord_iff'] at hc
  omega

/-- **Segments inside a lifted run** (b): for chords `c, c'` of a run `[u, v]` with
`v - u ≤ n`, the ordinary arcs `s(c)` and `s(c')` are compatible if and only if `c` and `c'` do
not cross. -/
@[cluster_algebras "lem_D_lift_segments"]
theorem compatible_ordArc_iff {u v : ℤ} (hvu : v - u ≤ n) {c c' : ℤ × ℤ}
    (hc : IsRunChord u v c) (hc' : IsRunChord u v c') :
    (ordArc c.1 c.2 : TaggedArc n).Compatible (ordArc c'.1 c'.2) ↔ ¬RunCross c c' := by
  have l1 := hc.len_le hvu
  have l2 := hc'.len_le hvu
  rw [isRunChord_iff'] at hc hc'
  exact compat_ordArc_of_le hvu hc.1 hc.2.2.1 hc.2.2.2.1 l1 hc'.1 hc'.2.2.1 hc'.2.2.2.1 l2

/-- **Segments inside a lifted run** (c): for `2 ≤ y - x ≤ n - 1` (in particular for a chord
`(x, y)` of a run of length at most `n`), the interior vertices of the run of `s(x, y)` are the
`m̄` with `x < m < y`. -/
@[cluster_algebras "lem_D_lift_segments"]
theorem interiorVertices_vtx {x y : ℤ} (h₁ : 2 ≤ y - x) (h₂ : y - x ≤ n - 1) :
    interiorVertices (vtx x : Fin n) (vtx y) = (intRange (x + 1) (y - 1)).image vtx :=
  interiorVertices_eq_image (by omega) (by omega)

/-! ### Successors, gaps and sectors -/

/-- The `t ∈ [0, n - 1]` with `a + t + 1 ∈ R` (mod `n`). -/
def gapCandidates (R : Finset (Fin n)) (a : Fin n) : Finset ℕ :=
  (Finset.range n).filter fun t => (vtx ((a : ℤ) + ((t + 1 : ℕ) : ℤ)) : Fin n) ∈ R

/-- The **gap** `g_R(a)`: the least `t ∈ [1, n]` with `a + t ∈ R` (mod `n`), and `n` if there is
none. For `a ∈ R` with `R = {r₁ < ⋯ < r_k}` and `a = r_s` it is `r_{s+1} - r_s`, where
`r_{k+1} = r₁ + n` (`gap_spec`). -/
@[cluster_algebras "def_D_sectors"]
def gap (R : Finset (Fin n)) (a : Fin n) : ℕ :=
  if h : (gapCandidates R a).Nonempty then (gapCandidates R a).min' h + 1 else n

/-- The **successor** `a⁺ = a + g_R(a)` (mod `n`). -/
@[cluster_algebras "def_D_sectors"]
def succ (R : Finset (Fin n)) (a : Fin n) : Fin n :=
  vtx ((a : ℤ) + (gap R a : ℤ))

/-- The `t ∈ [0, n - 1]` with `a - t - 1 ∈ R` (mod `n`). -/
def predGapCandidates (R : Finset (Fin n)) (a : Fin n) : Finset ℕ :=
  (Finset.range n).filter fun t => (vtx ((a : ℤ) - ((t + 1 : ℕ) : ℤ)) : Fin n) ∈ R

/-- The least `t ∈ [1, n]` with `a - t ∈ R` (mod `n`), and `n` if there is none. -/
def predGap (R : Finset (Fin n)) (a : Fin n) : ℕ :=
  if h : (predGapCandidates R a).Nonempty then (predGapCandidates R a).min' h + 1 else n

/-- The **predecessor** `a⁻` of `a`: the element of `R` whose successor is `a`
(`succ_pred`). -/
@[cluster_algebras "def_D_sectors"]
def pred (R : Finset (Fin n)) (a : Fin n) : Fin n :=
  vtx ((a : ℤ) - (predGap R a : ℤ))

/-- The **sector** `S_R(a) = {β_m̄ : a ≤ m < a + g_R(a)}`, as a set of indices of boundary
segments. The *sector run* of `a` is the integer run `[a, a + g_R(a)]`. -/
@[cluster_algebras "def_D_sectors"]
def sector (R : Finset (Fin n)) (a : Fin n) : Finset (Fin n) :=
  (Finset.range (gap R a)).image fun t : ℕ => vtx ((a : ℤ) + (t : ℤ))

/-- The **outer arc** `α_R(a) = s(a, a + g_R(a))`, used when `|R| ≥ 2` and `g_R(a) ≥ 2`. -/
@[cluster_algebras "def_D_sectors"]
def outerArc (R : Finset (Fin n)) (a : Fin n) : TaggedArc n :=
  ordArc (a : ℤ) ((a : ℤ) + (gap R a : ℤ))

/-- The gap of `a ∈ R` is the least `t ∈ [1, n]` with `a + t ∈ R` (mod `n`). -/
@[cluster_algebras "def_D_sectors"]
theorem gap_spec {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) :
    1 ≤ gap R a ∧ gap R a ≤ n ∧ (vtx ((a : ℤ) + (gap R a : ℤ)) : Fin n) ∈ R ∧
      ∀ t : ℕ, 0 < t → t < gap R a → (vtx ((a : ℤ) + (t : ℤ)) : Fin n) ∉ R := by
  have hn := NeZero.pos n
  have hne : (gapCandidates R a).Nonempty := ⟨n - 1, by
    simp only [gapCandidates, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rwa [Nat.sub_add_cancel hn, vtx_add_n, vtx_coe]⟩
  have hg : gap R a = (gapCandidates R a).min' hne + 1 := dif_pos hne
  have hmem := Finset.mem_filter.1 (show (gapCandidates R a).min' hne ∈ (Finset.range n).filter
    (fun t => (vtx ((a : ℤ) + ((t + 1 : ℕ) : ℤ)) : Fin n) ∈ R) from
      (gapCandidates R a).min'_mem hne)
  rw [Finset.mem_range] at hmem
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hg]; exact hmem.2
  · intro t ht0 htg hmemt
    have h' : t - 1 ∈ gapCandidates R a := by
      simp only [gapCandidates, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rwa [Nat.sub_add_cancel ht0]
    have := (gapCandidates R a).min'_le _ h'
    omega

private theorem predGap_spec {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) :
    1 ≤ predGap R a ∧ predGap R a ≤ n ∧ (vtx ((a : ℤ) - (predGap R a : ℤ)) : Fin n) ∈ R ∧
      ∀ t : ℕ, 0 < t → t < predGap R a → (vtx ((a : ℤ) - (t : ℤ)) : Fin n) ∉ R := by
  have hn := NeZero.pos n
  have hne : (predGapCandidates R a).Nonempty := ⟨n - 1, by
    simp only [predGapCandidates, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rwa [Nat.sub_add_cancel hn, vtx_sub_n, vtx_coe]⟩
  have hg : predGap R a = (predGapCandidates R a).min' hne + 1 := dif_pos hne
  have hmem := Finset.mem_filter.1 (show (predGapCandidates R a).min' hne ∈ (Finset.range n).filter
    (fun t => (vtx ((a : ℤ) - ((t + 1 : ℕ) : ℤ)) : Fin n) ∈ R) from
      (predGapCandidates R a).min'_mem hne)
  rw [Finset.mem_range] at hmem
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hg]; exact hmem.2
  · intro t ht0 htg hmemt
    have h' : t - 1 ∈ predGapCandidates R a := by
      simp only [predGapCandidates, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rwa [Nat.sub_add_cancel ht0]
    have := (predGapCandidates R a).min'_le _ h'
    omega

private theorem notMem_of_lt_gap {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) {m : ℤ}
    (h₁ : (a : ℤ) < m) (h₂ : m < a + gap R a) : (vtx m : Fin n) ∉ R := by
  have := (gap_spec ha).2.2.2 (m - a).toNat (by omega) (by omega)
  rwa [show (a : ℤ) + ((m - a).toNat : ℤ) = m by omega] at this

private theorem gap_eq_of {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) {g : ℕ} (h₁ : 1 ≤ g)
    (h₃ : (vtx ((a : ℤ) + (g : ℤ)) : Fin n) ∈ R)
    (h₄ : ∀ m : ℤ, (a : ℤ) < m → m < a + g → (vtx m : Fin n) ∉ R) : gap R a = g := by
  obtain ⟨g1, g2, g3, g4⟩ := gap_spec ha
  rcases lt_trichotomy (gap R a) g with h | h | h
  · exact absurd g3 (h₄ _ (by omega) (by omega))
  · exact h
  · exact absurd h₃ (g4 g (by omega) h)

private theorem predGap_eq_of {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) {g : ℕ}
    (h₁ : 1 ≤ g) (h₃ : (vtx ((a : ℤ) - (g : ℤ)) : Fin n) ∈ R)
    (h₄ : ∀ t : ℕ, 0 < t → t < g → (vtx ((a : ℤ) - t) : Fin n) ∉ R) : predGap R a = g := by
  obtain ⟨g1, g2, g3, g4⟩ := predGap_spec ha
  rcases lt_trichotomy (predGap R a) g with h | h | h
  · exact absurd g3 (h₄ _ (by omega) h)
  · exact h
  · exact absurd h₃ (g4 g (by omega) h)

/-- For `R = {a}`, `a⁺ = a⁻ = a` and `g_R(a) = n`. -/
@[cluster_algebras "def_D_sectors"]
theorem gap_singleton (a : Fin n) :
    gap {a} a = n ∧ succ {a} a = a ∧ pred {a} a = a := by
  have hn := NeZero.pos n
  have hg : gap {a} a = n := by
    refine gap_eq_of (Finset.mem_singleton_self a) hn ?_ ?_
    · rw [vtx_add_n, vtx_coe]; exact Finset.mem_singleton_self a
    · intro m h1 h2 hm
      have hm' : (vtx m : Fin n) = vtx (a : ℤ) := by rw [vtx_coe]; exact Finset.mem_singleton.1 hm
      have := eq_of_vtx_eq (n := n) h1.le (by omega) hm'.symm
      omega
  have hp : predGap {a} a = n := by
    refine predGap_eq_of (Finset.mem_singleton_self a) hn ?_ ?_
    · rw [vtx_sub_n, vtx_coe]; exact Finset.mem_singleton_self a
    · intro t h1 h2 hm
      have hm' : (vtx ((a : ℤ) - t) : Fin n) = vtx (a : ℤ) := by
        rw [vtx_coe]; exact Finset.mem_singleton.1 hm
      have := eq_of_vtx_eq (n := n) (u := (a : ℤ) - t) (v := a) (by omega) (by omega) hm'
      omega
  refine ⟨hg, ?_, ?_⟩
  · rw [succ, hg, vtx_add_n, vtx_coe]
  · rw [pred, hp, vtx_sub_n, vtx_coe]

/-- The predecessor of `a ∈ R` lies in `R` and has successor `a`. -/
@[cluster_algebras "def_D_sectors"]
theorem succ_pred {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) :
    pred R a ∈ R ∧ succ R (pred R a) = a := by
  obtain ⟨p1, p2, p3, p4⟩ := predGap_spec ha
  have hp : pred R a ∈ R := p3
  refine ⟨hp, ?_⟩
  obtain ⟨k, hk⟩ := coe_vtx_eq (n := n) ((a : ℤ) - predGap R a)
  have hpc : ((pred R a : Fin n) : ℤ) = (a : ℤ) - predGap R a + k * n := hk
  have hg : gap R (pred R a) = predGap R a := by
    refine gap_eq_of hp p1 ?_ ?_
    · rw [hpc, show (a : ℤ) - predGap R a + k * n + predGap R a = a + k * n by ring,
        vtx_add_mul, vtx_coe]; exact ha
    · intro m h1 h2 hm
      refine p4 (predGap R a - (m - pred R a).toNat) (by omega) (by omega) ?_
      rw [← vtx_add_mul _ k]
      convert hm using 2
      push_cast [Nat.cast_sub (show (m - pred R a).toNat ≤ predGap R a by omega)]
      omega
  rw [succ, hg, hpc, show (a : ℤ) - predGap R a + k * n + predGap R a = a + k * n by ring,
    vtx_add_mul, vtx_coe]

/-! ### Sectors partition the boundary -/

/-- Two representations `m̄ = m̄'` with `a ≤ m < a + g(a)`, `a' ≤ m' < a' + g(a')`, one way. -/
private theorem sector_repr_unique_aux {R : Finset (Fin n)} {a a' : Fin n} (ha : a ∈ R)
    (ha' : a' ∈ R) {m m' : ℤ} (h2 : m < a + gap R a) (h1' : (a' : ℤ) ≤ m')
    (hle : m' - a' ≤ m - a) (h : (vtx m : Fin n) = vtx m') : a = a' ∧ m = m' := by
  have hv : (vtx ((a : ℤ) + (m - a - (m' - a'))) : Fin n) = vtx (a' : ℤ) := by
    rw [vtx_eq_vtx_iff]
    have := ((show Int.ModEq n m m' from vtx_eq_vtx_iff.1 h).sub_right m').add_right (a' : ℤ)
    rw [sub_self, zero_add] at this
    rw [show (a : ℤ) + (m - a - (m' - a')) = m - m' + a' by ring]
    exact this
  rw [vtx_coe] at hv
  by_cases hd : m - a - (m' - a') = 0
  · rw [hd, add_zero, vtx_coe] at hv
    subst hv
    exact ⟨rfl, by omega⟩
  · have hm : (vtx ((a : ℤ) + (m - a - (m' - a'))) : Fin n) ∈ R := by rwa [hv]
    exact absurd hm (notMem_of_lt_gap ha (by omega) (by omega))

private theorem sector_repr_unique {R : Finset (Fin n)} {a a' : Fin n} (ha : a ∈ R)
    (ha' : a' ∈ R) {m m' : ℤ} (h1 : (a : ℤ) ≤ m) (h2 : m < a + gap R a) (h1' : (a' : ℤ) ≤ m')
    (h2' : m' < a' + gap R a') (h : (vtx m : Fin n) = vtx m') : a = a' ∧ m = m' := by
  rcases le_total (m' - a') (m - a) with hle | hle
  · exact sector_repr_unique_aux ha ha' h2 h1' hle h
  · obtain ⟨e1, e2⟩ := sector_repr_unique_aux ha' ha h2' h1 hle h.symm
    exact ⟨e1.symm, e2.symm⟩

private theorem exists_sector_repr {R : Finset (Fin n)} (hR : R.Nonempty) (i : Fin n) :
    ∃ a ∈ R, ∃ m : ℤ, (a : ℤ) ≤ m ∧ m < a + gap R a ∧ (vtx m : Fin n) = i := by
  classical
  obtain ⟨r, hr⟩ := hR
  have hex : ∃ s : ℕ, (vtx ((i : ℤ) - s) : Fin n) ∈ R := ⟨cdist r i, by
    have e := vtx_add_cdist r i
    set c := cdist r i
    rwa [← e, vtx_sub_coe, add_sub_cancel_right, vtx_coe]⟩
  set s := Nat.find hex with hs
  have hsR : (vtx ((i : ℤ) - s) : Fin n) ∈ R := Nat.find_spec hex
  refine ⟨_, hsR, ((vtx ((i : ℤ) - s) : Fin n) : ℤ) + s, le_add_of_nonneg_right (by positivity),
    ?_, by rw [vtx_add_coe, sub_add_cancel, vtx_coe]⟩
  by_contra hcon
  have g := gap_spec hsR
  have hlt : s - gap R (vtx ((i : ℤ) - s)) < s := by omega
  refine Nat.find_min hex hlt ?_
  have := g.2.2.1
  rw [vtx_add_coe] at this
  convert this using 2
  push_cast [Nat.cast_sub (show gap R (vtx ((i : ℤ) - s)) ≤ s by omega)]
  ring

/-- **Sectors partition the boundary** (a): the gaps of a nonempty `R` sum to `n`. -/
@[cluster_algebras "lem_D_sectors"]
theorem sum_gap {R : Finset (Fin n)} (hR : R.Nonempty) : ∑ a ∈ R, gap R a = n := by
  have h := Finset.card_sigma R (fun a => Finset.range (gap R a))
  simp only [Finset.card_range] at h
  rw [← h]
  calc _ = (Finset.univ : Finset (Fin n)).card := by
        refine Finset.card_bij (fun p _ => (vtx ((p.1 : ℤ) + (p.2 : ℤ)) : Fin n))
          (fun _ _ => Finset.mem_univ _) ?_ ?_
        · rintro ⟨a, t⟩ hp ⟨a', t'⟩ hp' he
          simp only [Finset.mem_sigma, Finset.mem_range] at hp hp'
          obtain ⟨e1, e2⟩ := sector_repr_unique hp.1 hp'.1 (m := a + t) (m' := a' + t')
            (by omega) (by omega) (by omega) (by omega) he
          subst e1
          obtain rfl : t = t' := by omega
          rfl
        · intro i _
          obtain ⟨a, ha, m, h1, h2, h3⟩ := exists_sector_repr hR i
          refine ⟨⟨a, (m - a).toNat⟩, ?_, ?_⟩
          · simp only [Finset.mem_sigma, Finset.mem_range]; exact ⟨ha, by omega⟩
          · change (vtx ((a : ℤ) + ((m - a).toNat : ℤ)) : Fin n) = i
            rw [← h3]; congr 1; omega
    _ = n := by simp

private theorem mem_sector_iff {R : Finset (Fin n)} {a i : Fin n} :
    i ∈ sector R a ↔ ∃ m : ℤ, (a : ℤ) ≤ m ∧ m < a + gap R a ∧ (vtx m : Fin n) = i := by
  simp only [sector, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨a + t, by omega, by omega, rfl⟩
  · rintro ⟨m, h1, h2, rfl⟩; exact ⟨(m - a).toNat, by omega, by congr 1; omega⟩

/-- **Sectors partition the boundary** (a): every boundary segment lies in exactly one sector. -/
@[cluster_algebras "lem_D_sectors"]
theorem existsUnique_mem_sector {R : Finset (Fin n)} (hR : R.Nonempty) (i : Fin n) :
    ∃! a, a ∈ R ∧ i ∈ sector R a := by
  obtain ⟨a, ha, m, h1, h2, h3⟩ := exists_sector_repr hR i
  refine ⟨a, ⟨ha, mem_sector_iff.2 ⟨m, h1, h2, h3⟩⟩, ?_⟩
  rintro a' ⟨ha', hi⟩
  obtain ⟨m', h1', h2', h3'⟩ := mem_sector_iff.1 hi
  exact (sector_repr_unique ha ha' h1 h2 h1' h2' (h3.trans h3'.symm)).1.symm

/-- **Sectors partition the boundary** (a): the only integers `m` of the sector run
`[a, a + g_R(a)]` with `m̄ ∈ R` are its two ends. -/
@[cluster_algebras "lem_D_sectors"]
theorem vtx_mem_iff_of_mem_sectorRun {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) {m : ℤ}
    (h₁ : (a : ℤ) ≤ m) (h₂ : m ≤ a + gap R a) :
    (vtx m : Fin n) ∈ R ↔ m = a ∨ m = a + gap R a := by
  constructor
  · intro hm
    by_contra hc
    rw [not_or] at hc
    exact notMem_of_lt_gap ha (by omega) (by omega) hm
  · rintro (rfl | rfl)
    · rwa [vtx_coe]
    · exact (gap_spec ha).2.2.1

/-- **Sectors partition the boundary** (a): every vertex is `m̄` for exactly one pair `(a, m)`
with `a ∈ R` and `a ≤ m < a + g_R(a)`. -/
@[cluster_algebras "lem_D_sectors"]
theorem existsUnique_vtx_eq {R : Finset (Fin n)} (hR : R.Nonempty) (i : Fin n) :
    ∃! p : Fin n × ℤ, p.1 ∈ R ∧ (p.1 : ℤ) ≤ p.2 ∧ p.2 < p.1 + gap R p.1 ∧ vtx p.2 = i := by
  obtain ⟨a, ha, m, h1, h2, h3⟩ := exists_sector_repr hR i
  refine ⟨(a, m), ⟨ha, h1, h2, h3⟩, ?_⟩
  rintro ⟨a', m'⟩ ⟨ha', h1', h2', h3'⟩
  obtain ⟨e1, e2⟩ := sector_repr_unique ha' ha h1' h2' h1 h2 (h3'.trans h3.symm)
  exact Prod.ext e1 e2

private theorem gap_lt_of_two_le_card {R : Finset (Fin n)} (hR : 2 ≤ R.card) {a : Fin n}
    (ha : a ∈ R) : gap R a < n := by
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < R.card) a
  have e := vtx_add_cdist a b
  have hc := cdist_lt a b
  by_contra hcon
  have hpos : 0 < cdist a b := by
    by_contra h0
    rw [Nat.not_lt, Nat.le_zero] at h0
    rw [h0, Nat.cast_zero, add_zero, vtx_coe] at e
    exact hba e.symm
  exact (gap_spec ha).2.2.2 _ hpos (by omega) (by rwa [e])

omit [NeZero n] in
private theorem eq_singleton_of_card_le_one {R : Finset (Fin n)} (hR : R.card ≤ 1) {a : Fin n}
    (ha : a ∈ R) : R = {a} :=
  Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun b hb => Finset.card_le_one.1 hR b hb a ha⟩

private theorem notMem_interiorVertices_of_sector {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R)
    {x y : ℤ} (h1 : (a : ℤ) ≤ x) (h2 : x < y) (h3 : y ≤ a + gap R a) (h4 : y < x + n) :
    ∀ r ∈ R, r ∉ interiorVertices (vtx x : Fin n) (vtx y) := by
  intro r hr hi
  rw [interiorVertices_eq_image h2 h4, Finset.mem_image] at hi
  obtain ⟨m, hm, rfl⟩ := hi
  rw [mem_intRange] at hm
  exact notMem_of_lt_gap ha (by omega) (by omega) hr

/-- **Sectors partition the boundary** (b): an ordinary arc has no interior vertex in `R` if and
only if it is `s(c)` for a chord `c` of some sector run, or (when `|R| ≥ 2`) it is some outer
arc. -/
@[cluster_algebras "lem_D_sectors"]
theorem forall_notMem_interiorVertices_iff {R : Finset (Fin n)} (hR : R.Nonempty) {i j : Fin n}
    (h : 2 ≤ cdist i j) :
    (∀ r ∈ R, r ∉ interiorVertices i j) ↔
      (∃ a ∈ R, ∃ c, IsRunChord a (a + gap R a) c ∧ ordArc c.1 c.2 = .ordinary i j h) ∨
        (2 ≤ R.card ∧ ∃ a ∈ R, 2 ≤ gap R a ∧ outerArc R a = .ordinary i j h) := by
  have hcl := cdist_lt i j
  constructor
  · intro hR'
    obtain ⟨a, ha, x, h1, h2, rfl⟩ := exists_sector_repr hR i
    obtain ⟨d, hd⟩ : ∃ d : ℕ, cdist (vtx x : Fin n) j = d := ⟨_, rfl⟩
    have hj : (vtx (x + d) : Fin n) = j := by rw [← hd, ← vtx_add_coe, vtx_add_cdist]
    rw [hd] at hcl
    have hd2 : 2 ≤ d := hd ▸ h
    obtain ⟨g1, g2, g3, g4⟩ := gap_spec ha
    have hy : x + d ≤ a + gap R a := by
      by_contra hc
      apply hR' _ g3
      rw [← hj, interiorVertices_eq_image (by omega) (by omega)]
      exact Finset.mem_image_of_mem _ (mem_intRange.2 ⟨by omega, by omega⟩)
    subst hj
    obtain ⟨h', e⟩ := ordArc_eq_ordinary (n := n) (x := x) (y := x + d) (by omega) (by omega)
    by_cases hout : x = a ∧ d = gap R a
    · right
      obtain ⟨rfl, rfl⟩ := hout
      refine ⟨?_, a, ha, hd2, ?_⟩
      · by_contra hc
        have := (gap_singleton a).1
        rw [← eq_singleton_of_card_le_one (by omega) ha] at this
        omega
      · exact e
    · left
      refine ⟨a, ha, (x, x + d), ?_, e⟩
      rw [isRunChord_iff']
      dsimp only
      omega
  · rintro (⟨a, ha, c, hc, e⟩ | ⟨hR2, a, ha, hg, e⟩)
    · have hl := hc.len_le (n := n) (by have := (gap_spec ha).2.1; omega)
      rw [isRunChord_iff'] at hc
      obtain ⟨h', e'⟩ := ordArc_eq_ordinary (n := n) hc.2.2.2.1 hl
      rw [e', TaggedArc.ordinary.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact notMem_interiorVertices_of_sector ha hc.1 hc.2.1 hc.2.2.1 (by omega)
    · have hlt := gap_lt_of_two_le_card hR2 ha
      obtain ⟨h', e'⟩ := ordArc_eq_ordinary (n := n) (x := a) (y := a + gap R a) (by omega)
        (by omega)
      rw [outerArc, e', TaggedArc.ordinary.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact notMem_interiorVertices_of_sector ha le_rfl (by omega) le_rfl (by omega)

private theorem sectorPair_eq_of_ordArc_eq {R : Finset (Fin n)} {a a' : Fin n} (ha : a ∈ R)
    (ha' : a' ∈ R) {c c' : ℤ × ℤ} (h1 : (a : ℤ) ≤ c.1) (h2 : 2 ≤ c.2 - c.1)
    (h3 : c.2 ≤ a + gap R a) (h4 : c.2 - c.1 ≤ n - 1) (h1' : (a' : ℤ) ≤ c'.1)
    (h2' : 2 ≤ c'.2 - c'.1) (h3' : c'.2 ≤ a' + gap R a') (h4' : c'.2 - c'.1 ≤ n - 1)
    (h : (ordArc c.1 c.2 : TaggedArc n) = ordArc c'.1 c'.2) : a = a' ∧ c = c' := by
  obtain ⟨_, e⟩ := ordArc_eq_ordinary (n := n) h2 h4
  obtain ⟨_, e'⟩ := ordArc_eq_ordinary (n := n) h2' h4'
  rw [e, e', TaggedArc.ordinary.injEq] at h
  obtain ⟨r1, r2⟩ := sector_repr_unique ha ha' h1 (by omega) h1' (by omega) h.1
  subst r1
  exact ⟨rfl, Prod.ext r2 (eq_of_vtx_eq' (by omega) (by omega) h.2)⟩

/-- **Sectors partition the boundary** (b): the pair `(a, c)` of a sector-run chord with a given
segment is unique. -/
@[cluster_algebras "lem_D_sectors"]
theorem eq_of_ordArc_eq {R : Finset (Fin n)} {a a' : Fin n} (ha : a ∈ R) (ha' : a' ∈ R)
    {c c' : ℤ × ℤ} (hc : IsRunChord a (a + gap R a) c) (hc' : IsRunChord a' (a' + gap R a') c')
    (h : (ordArc c.1 c.2 : TaggedArc n) = ordArc c'.1 c'.2) : a = a' ∧ c = c' := by
  have l := hc.len_le (n := n) (by have := (gap_spec ha).2.1; omega)
  have l' := hc'.len_le (n := n) (by have := (gap_spec ha').2.1; omega)
  rw [isRunChord_iff'] at hc hc'
  exact sectorPair_eq_of_ordArc_eq ha ha' hc.1 hc.2.2.2.1 hc.2.2.1 l hc'.1 hc'.2.2.2.1
    hc'.2.2.1 l' h

/-- **Sectors partition the boundary** (b): the position `a` of an outer arc is unique. -/
@[cluster_algebras "lem_D_sectors"]
theorem eq_of_outerArc_eq {R : Finset (Fin n)} {a a' : Fin n}
    (h : outerArc R a = outerArc R a') : a = a' := by
  simpa only [vtx_coe] using vtx_eq_of_ordArc_eq h

private theorem sector_eq_image (R : Finset (Fin n)) (a : Fin n) :
    sector R a = (intRange (a : ℤ) (a + gap R a - 1)).image vtx := by
  ext i
  simp only [mem_sector_iff, Finset.mem_image, mem_intRange]
  constructor
  · rintro ⟨m, h1, h2, h3⟩
    exact ⟨m, ⟨h1, by omega⟩, h3⟩
  · rintro ⟨m, ⟨h1, h2⟩, h3⟩
    exact ⟨m, h1, by omega, h3⟩

/-- **Sectors partition the boundary** (b): the shadow of the segment of a chord of the sector
run of `a` is properly contained in the sector of `a`. -/
@[cluster_algebras "lem_D_sectors"]
theorem shadow_seg_ssubset_sector {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) {c : ℤ × ℤ}
    (hc : IsRunChord a (a + gap R a) c) : (seg c.1 c.2 : DSeg n).shadow ⊂ sector R a := by
  have g := gap_spec ha
  have hl := hc.len_le (n := n) (by omega)
  rw [isRunChord_iff'] at hc
  rw [shadow_seg (by omega) hl, sector_eq_image]
  refine HasSubset.Subset.ssubset_of_not_subset ?_ ?_
  · exact (image_subset_image_iff (u := a) (v := a + gap R a) (by omega) (by omega) (by omega)
      (by omega) le_rfl le_rfl).2 ⟨by omega, by omega⟩
  · rw [image_subset_image_iff (u := a) (v := a + gap R a) (by omega) le_rfl (by omega) le_rfl
      (by omega) (by omega)]
    omega

/-- **Sectors partition the boundary** (b): for `|R| ≥ 2`, the shadow of the outer arc of `a`
is the sector of `a`. -/
@[cluster_algebras "lem_D_sectors"]
theorem shadow_seg_outer_eq_sector {R : Finset (Fin n)} (hR : 2 ≤ R.card) {a : Fin n}
    (ha : a ∈ R) : (seg (a : ℤ) (a + gap R a) : DSeg n).shadow = sector R a := by
  have g := gap_spec ha
  have hlt := gap_lt_of_two_le_card hR ha
  rw [shadow_seg (by omega) (by omega), sector_eq_image]

/-- **Sectors partition the boundary** (c): ordinary arcs whose shadows lie in different sectors
are compatible. -/
@[cluster_algebras "lem_D_sectors"]
theorem compatible_of_subset_sector {R : Finset (Fin n)} {a a' : Fin n} (ha : a ∈ R)
    (ha' : a' ∈ R) (haa' : a ≠ a') {i j k l : Fin n} (h : 2 ≤ cdist i j) (h' : 2 ≤ cdist k l)
    (hs : shadow i j ⊆ sector R a) (hs' : shadow k l ⊆ sector R a') :
    (TaggedArc.ordinary i j h).Compatible (.ordinary k l h') := by
  simp only [TaggedArc.Compatible]
  refine Or.inr <| Or.inr <| Finset.disjoint_of_subset_left hs <|
    Finset.disjoint_of_subset_right hs' <| Finset.disjoint_left.2 fun b hb hb' => ?_
  exact haa' ((existsUnique_mem_sector ⟨a, ha⟩ b).unique ⟨ha, hb⟩ ⟨ha', hb'⟩)

/-- **Sectors partition the boundary** (c): the outer arc of `a` is compatible with the segment
of every chord of the sector run of `a`. -/
@[cluster_algebras "lem_D_sectors"]
theorem compatible_outerArc_ordArc {R : Finset (Fin n)} (hR : 2 ≤ R.card) {a : Fin n}
    (ha : a ∈ R) (hg : 2 ≤ gap R a) {c : ℤ × ℤ} (hc : IsRunChord a (a + gap R a) c) :
    (outerArc R a).Compatible (ordArc c.1 c.2) := by
  have hlt := gap_lt_of_two_le_card hR ha
  have hl := hc.len_le (n := n) (by omega)
  rw [isRunChord_iff'] at hc
  obtain ⟨_, e⟩ := ordArc_eq_ordinary (n := n) (x := a) (y := a + gap R a) (by omega) (by omega)
  obtain ⟨_, e'⟩ := ordArc_eq_ordinary (n := n) hc.2.2.2.1 hl
  rw [outerArc, e, e']
  simp only [TaggedArc.Compatible]
  refine Or.inr <| Or.inl ?_
  rw [shadow_eq_image (by omega) (by omega), shadow_eq_image (by omega) (by omega)]
  exact Finset.image_subset_image (intRange_subset (by omega) (by omega))

/-! ### The three kinds of tagged triangulations -/

/-- The **radius set** of `T`: the positions of the radii in `T`. -/
@[cluster_algebras "lem_D_structure"]
def radiusSet (T : Finset (TaggedArc n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => TaggedArc.radius .plain i ∈ T ∨ TaggedArc.radius .notched i ∈ T

/-- The set `T_R(a)` of chords `c` of the sector run `[a, a + g_R(a)]` with `s(c) ∈ T`. -/
@[cluster_algebras "lem_D_structure"]
def sectorChords (T : Finset (TaggedArc n)) (R : Finset (Fin n)) (a : Fin n) :
    Finset (ℤ × ℤ) :=
  (intRange a (a + gap R a) ×ˢ intRange a (a + gap R a)).filter fun c =>
    IsRunChord a (a + gap R a) c ∧ ordArc c.1 c.2 ∈ T

/-- `T` is **of kind `P_τ` with radius set `R`**: `|R| ≥ 2`, the radii in `T` are exactly the
`ρ^τ_a`, `a ∈ R`; every `T_R(a)` is a triangulation of the sector run of `a`; `α_R(a) ∈ T`
whenever `g_R(a) ≥ 2`; and every ordinary arc of `T` is an outer arc or the segment of an
element of some `T_R(a)`. -/
@[cluster_algebras "lem_D_structure"]
def IsKindP (T : Finset (TaggedArc n)) (τ : Tag) (R : Finset (Fin n)) : Prop :=
  2 ≤ R.card ∧ (∀ σ b, TaggedArc.radius σ b ∈ T ↔ σ = τ ∧ b ∈ R) ∧
    (∀ a ∈ R, IsRunTriangulation a (a + gap R a) (sectorChords T R a)) ∧
    (∀ a ∈ R, 2 ≤ gap R a → outerArc R a ∈ T) ∧
    ∀ γ ∈ T, γ.IsOrdinary → ∃ a ∈ R, (2 ≤ gap R a ∧ γ = outerArc R a) ∨
      ∃ c ∈ sectorChords T R a, ordArc c.1 c.2 = γ

/-- `T` is **of digon kind with doubled position `a`**: the radii in `T` are exactly `ρ^+_a` and
`ρ^-_a`; with `R = {a}`, `T_R(a)` is a triangulation of `[a, a + n]`; and every ordinary arc of
`T` is the segment of an element of `T_R(a)`. -/
@[cluster_algebras "lem_D_structure"]
def IsDigonKind (T : Finset (TaggedArc n)) (a : Fin n) : Prop :=
  (∀ σ b, TaggedArc.radius σ b ∈ T ↔ b = a) ∧
    IsRunTriangulation a (a + gap {a} a) (sectorChords T {a} a) ∧
    ∀ γ ∈ T, γ.IsOrdinary → ∃ c ∈ sectorChords T {a} a, ordArc c.1 c.2 = γ

omit [NeZero n] in
/-- A position lies in `radiusSet T` exactly when `T` has a radius at it. -/
theorem mem_radiusSet {T : Finset (TaggedArc n)} {r : Fin n} :
    r ∈ radiusSet T ↔ ∃ σ, TaggedArc.radius σ r ∈ T := by
  simp only [radiusSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | h) <;> exact ⟨_, h⟩
  · rintro ⟨⟨⟩, h⟩
    exacts [Or.inl h, Or.inr h]

/-- A chord lies in `sectorChords T R a` exactly when it is a chord of the sector run of `a`
whose segment lies in `T`. -/
theorem mem_sectorChords {T : Finset (TaggedArc n)} {R : Finset (Fin n)} {a : Fin n}
    {c : ℤ × ℤ} :
    c ∈ sectorChords T R a ↔ IsRunChord a (a + gap R a) c ∧ ordArc c.1 c.2 ∈ T := by
  rw [sectorChords, Finset.mem_filter, Finset.mem_product, mem_intRange, mem_intRange]
  refine ⟨And.right, fun h => ?_⟩
  have := isRunChord_iff'.1 h.1
  exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, h⟩

/-- A pair `c` lying in the sector run of `a` whose segment is an ordinary arc. -/
private def IsSectorPair (R : Finset (Fin n)) (a : Fin n) (c : ℤ × ℤ) : Prop :=
  (a : ℤ) ≤ c.1 ∧ c.2 ≤ a + gap R a ∧ 2 ≤ c.2 - c.1 ∧ c.2 - c.1 ≤ n - 1

private theorem IsRunChord.isSectorPair {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R)
    {c : ℤ × ℤ} (hc : IsRunChord a (a + gap R a) c) : IsSectorPair R a c := by
  have l := hc.len_le (n := n) (by have := (gap_spec ha).2.1; omega)
  rw [isRunChord_iff'] at hc
  exact ⟨hc.1, hc.2.2.1, hc.2.2.2.1, l⟩

private theorem isSectorPair_outer {R : Finset (Fin n)} (hR : 2 ≤ R.card) {a : Fin n}
    (ha : a ∈ R) (hg : 2 ≤ gap R a) : IsSectorPair R a ((a : ℤ), (a : ℤ) + gap R a) := by
  have := gap_lt_of_two_le_card hR ha
  refine ⟨le_rfl, le_rfl, ?_, ?_⟩ <;> dsimp only <;> omega

private theorem IsSectorPair.ordArc_eq {R : Finset (Fin n)} {a : Fin n} {c : ℤ × ℤ}
    (h : IsSectorPair R a c) :
    ∃ hh, (ordArc c.1 c.2 : TaggedArc n) = .ordinary (vtx c.1) (vtx c.2) hh :=
  ordArc_eq_ordinary h.2.2.1 h.2.2.2

private theorem IsSectorPair.isOrdinary {R : Finset (Fin n)} {a : Fin n} {c : ℤ × ℤ}
    (h : IsSectorPair R a c) : (ordArc c.1 c.2 : TaggedArc n).IsOrdinary := by
  obtain ⟨_, e⟩ := h.ordArc_eq
  rw [e]
  trivial

private theorem IsSectorPair.eq {R : Finset (Fin n)} {a a' : Fin n} (ha : a ∈ R) (ha' : a' ∈ R)
    {c c' : ℤ × ℤ} (h : IsSectorPair R a c) (h' : IsSectorPair R a' c')
    (e : (ordArc c.1 c.2 : TaggedArc n) = ordArc c'.1 c'.2) : a = a' ∧ c = c' :=
  sectorPair_eq_of_ordArc_eq ha ha' h.1 h.2.2.1 h.2.1 h.2.2.2 h'.1 h'.2.2.1 h'.2.1 h'.2.2.2 e

private theorem IsSectorPair.compat_radius {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R)
    {c : ℤ × ℤ} (h : IsSectorPair R a c) {r : Fin n} (hr : r ∈ R) (σ : Tag) :
    (ordArc c.1 c.2 : TaggedArc n).Compatible (.radius σ r) := by
  obtain ⟨_, e⟩ := h.ordArc_eq
  rw [e]
  exact notMem_interiorVertices_of_sector ha h.1 (by have := h.2.2.1; omega) h.2.1
    (by have := h.2.2.2; omega) r hr

private theorem IsSectorPair.shadow_subset {R : Finset (Fin n)} {a : Fin n} {c : ℤ × ℤ}
    (h : IsSectorPair R a c) : shadow (vtx c.1 : Fin n) (vtx c.2) ⊆ sector R a := by
  rw [shadow_eq_image (by have := h.2.2.1; omega) (by have := h.2.2.2; omega), sector_eq_image]
  exact Finset.image_subset_image (intRange_subset h.1 (by have := h.2.1; omega))

private theorem IsSectorPair.compat {R : Finset (Fin n)} {a b : Fin n} (ha : a ∈ R) (hb : b ∈ R)
    {c c' : ℤ × ℤ} (h : IsSectorPair R a c) (h' : IsSectorPair R b c')
    (hx : a = b → ¬RunCross c c') :
    (ordArc c.1 c.2 : TaggedArc n).Compatible (ordArc c'.1 c'.2) := by
  by_cases hab : a = b
  · subst hab
    exact (compat_ordArc_of_le (u := a) (v := a + gap R a)
      (by have := (gap_spec ha).2.1; omega) h.1 h.2.1 h.2.2.1 h.2.2.2 h'.1 h'.2.1 h'.2.2.1
      h'.2.2.2).2 (hx rfl)
  · obtain ⟨_, e⟩ := h.ordArc_eq
    obtain ⟨_, e'⟩ := h'.ordArc_eq
    rw [e, e']
    exact compatible_of_subset_sector ha hb hab _ _ h.shadow_subset h'.shadow_subset

private theorem not_runCross_outer {u v : ℤ} {c : ℤ × ℤ} (h1 : u ≤ c.1) (h2 : c.2 ≤ v) :
    ¬RunCross c (u, v) ∧ ¬RunCross (u, v) c := by
  simp only [RunCross]
  omega

/-- The common data of the kinds: sector-run triangulations, outer arcs, and the description of
the ordinary arcs. -/
private def SectorData (T : Finset (TaggedArc n)) (R : Finset (Fin n)) : Prop :=
  (∀ a ∈ R, IsRunTriangulation a (a + gap R a) (sectorChords T R a)) ∧
    (2 ≤ R.card → ∀ a ∈ R, 2 ≤ gap R a → outerArc R a ∈ T) ∧
    ∀ γ ∈ T, γ.IsOrdinary → ∃ a ∈ R, (2 ≤ R.card ∧ 2 ≤ gap R a ∧ γ = outerArc R a) ∨
      ∃ c ∈ sectorChords T R a, ordArc c.1 c.2 = γ

private theorem SectorData.rep {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    (hS : SectorData T R) {γ : TaggedArc n} (hγ : γ ∈ T) (ho : γ.IsOrdinary) :
    ∃ a ∈ R, ∃ c, IsSectorPair R a c ∧ ordArc c.1 c.2 = γ ∧
      (c = ((a : ℤ), (a : ℤ) + gap R a) ∨ c ∈ sectorChords T R a) := by
  obtain ⟨a, ha, ⟨hR, hg, rfl⟩ | ⟨c, hc, rfl⟩⟩ := hS.2.2 γ hγ ho
  · exact ⟨a, ha, _, isSectorPair_outer hR ha hg, rfl, Or.inl rfl⟩
  · exact ⟨a, ha, c, (mem_sectorChords.1 hc).1.isSectorPair ha, rfl, Or.inr hc⟩

private theorem SectorData.compat_ord {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    (hS : SectorData T R) {γ δ : TaggedArc n} (hγ : γ ∈ T) (hγo : γ.IsOrdinary) (hδ : δ ∈ T)
    (hδo : δ.IsOrdinary) : γ.Compatible δ := by
  obtain ⟨a, ha, c, hc, rfl, hc'⟩ := hS.rep hγ hγo
  obtain ⟨b, hb, d, hd, rfl, hd'⟩ := hS.rep hδ hδo
  refine hc.compat ha hb hd ?_
  rintro rfl
  rcases hc' with rfl | hc'
  · exact (not_runCross_outer hd.1 hd.2.1).2
  rcases hd' with rfl | hd'
  · exact (not_runCross_outer hc.1 hc.2.1).1
  exact (isRunTriangulation_iff.1 (hS.1 a ha)).2.1 c hc' d hd'

/-- The segment of a chord of a sector run which is compatible with the segments of all the
chords of `T_R(b)` lies in `T`. -/
private theorem SectorData.ordArc_mem_of_compat {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    (hS : SectorData T R) {b : Fin n} (hb : b ∈ R) {c : ℤ × ℤ} (hc : IsRunChord b (b + gap R b) c)
    (hcomp : ∀ d ∈ sectorChords T R b, (ordArc c.1 c.2 : TaggedArc n).Compatible (ordArc d.1 d.2)) :
    ordArc c.1 c.2 ∈ T := by
  by_contra hm
  obtain ⟨d, hd, hx⟩ := (isRunTriangulation_iff.1 (hS.1 b hb)).2.2 c hc
    fun h => hm (mem_sectorChords.1 h).2
  exact (compatible_ordArc_iff (by have := (gap_spec hb).2.1; omega) hc
    (mem_sectorChords.1 hd).1).1 (hcomp d hd) hx

private theorem SectorData.mem_of_compat {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    (hR : R.Nonempty) (hS : SectorData T R) {i j : Fin n} (h : 2 ≤ cdist i j)
    (hrad : ∀ r ∈ R, r ∉ interiorVertices i j)
    (hcomp : ∀ δ ∈ T, δ.IsOrdinary → (TaggedArc.ordinary i j h).Compatible δ) :
    TaggedArc.ordinary i j h ∈ T := by
  rcases (forall_notMem_interiorVertices_iff hR h).1 hrad with ⟨a, ha, c, hc, e⟩ |
    ⟨hR2, a, ha, hg, e⟩
  · rw [← e]
    refine hS.ordArc_mem_of_compat ha hc fun d hd => ?_
    have hdT := mem_sectorChords.1 hd
    rw [e]
    exact hcomp _ hdT.2 (hdT.1.isSectorPair ha).isOrdinary
  · rw [← e]
    exact hS.2.1 hR2 a ha hg

private theorem SectorData.isTaggedTriangulation {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    (hR : R.Nonempty) (hS : SectorData T R)
    (hrR : ∀ σ b, TaggedArc.radius σ b ∈ T → b ∈ R)
    (hRr : ∀ r ∈ R, ∃ σ, TaggedArc.radius σ r ∈ T)
    (hrr : ∀ σ b σ' b', TaggedArc.radius σ b ∈ T → TaggedArc.radius σ' b' ∈ T → b = b' ∨ σ = σ')
    (hmax : ∀ σ b, (∀ δ ∈ T, (TaggedArc.radius σ b).Compatible δ) → TaggedArc.radius σ b ∈ T) :
    IsTaggedTriangulation T := by
  have hord_rad : ∀ γ ∈ T, γ.IsOrdinary → ∀ σ b, b ∈ R →
      γ.Compatible (TaggedArc.radius σ b) := by
    intro γ hγ ho σ b hb
    obtain ⟨a, ha, c, hc, rfl, -⟩ := hS.rep hγ ho
    exact hc.compat_radius ha hb σ
  refine ⟨?_, ?_⟩
  · intro γ hγ δ hδ
    cases γ with
    | radius σ b =>
      cases δ with
      | radius σ' b' => exact hrr σ b σ' b' hγ hδ
      | ordinary k l h => exact (hord_rad _ hδ trivial σ b (hrR σ b hγ)).symm
    | ordinary i j h =>
      cases δ with
      | radius σ' b' => exact hord_rad _ hγ trivial σ' b' (hrR _ _ hδ)
      | ordinary k l h' => exact hS.compat_ord hγ trivial hδ trivial
  · intro γ hγ
    cases γ with
    | radius σ b => exact hmax σ b hγ
    | ordinary i j h =>
      refine hS.mem_of_compat hR h ?_ (fun δ hδ _ => hγ δ hδ)
      intro r hr
      obtain ⟨σ, hσ⟩ := hRr r hr
      exact hγ _ hσ

private theorem IsKindP.sectorData {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (h : IsKindP T τ R) : SectorData T R := by
  refine ⟨h.2.2.1, fun _ => h.2.2.2.1, fun γ hγ ho => ?_⟩
  obtain ⟨a, ha, ⟨hg, e⟩ | hc⟩ := h.2.2.2.2 γ hγ ho
  exacts [⟨a, ha, Or.inl ⟨h.1, hg, e⟩⟩, ⟨a, ha, Or.inr hc⟩]

private theorem IsKindP.nonempty {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (h : IsKindP T τ R) : R.Nonempty :=
  Finset.card_pos.1 (by have := h.1; omega)

private theorem tag_eq_of_compat {σ τ : Tag} {x r r' : Fin n} (hrr' : r ≠ r')
    (h1 : (TaggedArc.radius σ x).Compatible (.radius τ r))
    (h2 : (TaggedArc.radius σ x).Compatible (.radius τ r')) : σ = τ := by
  simp only [TaggedArc.Compatible] at h1 h2
  rcases h1 with rfl | h1
  · exact h2.resolve_left hrr'
  · exact h1

private theorem eq_of_compat_radius {σ : Tag} {x a : Fin n}
    (h₁ : (TaggedArc.radius σ x).Compatible (.radius .plain a))
    (h₂ : (TaggedArc.radius σ x).Compatible (.radius .notched a)) : x = a := by
  simp only [TaggedArc.Compatible] at h₁ h₂
  rcases h₁ with h₁ | rfl
  · exact h₁
  · exact h₂.resolve_right (by decide)

private theorem coe_lt_of_vtx_notMem {R : Finset (Fin n)} {b : Fin n} (hb : b ∈ R) {m : ℤ}
    (h : (b : ℤ) ≤ m) (hm : (vtx m : Fin n) ∉ R) : (b : ℤ) < m := by
  rcases h.lt_or_eq with h | rfl
  · exact h
  · rw [vtx_coe] at hm
    exact absurd hb hm

private theorem IsSectorPair.not_compat_radius {R : Finset (Fin n)} {a : Fin n} {d : ℤ × ℤ}
    (h : IsSectorPair R a d) {m : ℤ} (h1 : d.1 < m) (h2 : m < d.2) (σ : Tag) :
    ¬(TaggedArc.radius σ (vtx m : Fin n)).Compatible (ordArc d.1 d.2) := by
  obtain ⟨_, e⟩ := h.ordArc_eq
  rw [e]
  intro hc
  apply hc
  rw [interiorVertices_eq_image (by omega) (by have := h.2.2.2; omega)]
  exact Finset.mem_image_of_mem _ (mem_intRange.2 ⟨by omega, by omega⟩)

private theorem IsKindP.not_compat_radius {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) {x : Fin n} (hx : x ∉ R) (σ : Tag) :
    ∃ b ∈ R, 2 ≤ gap R b ∧ ¬(TaggedArc.radius σ x).Compatible (outerArc R b) := by
  obtain ⟨b, hb, m, h1, h2, rfl⟩ := exists_sector_repr hT.nonempty x
  have hmb := coe_lt_of_vtx_notMem hb h1 hx
  have hg : 2 ≤ gap R b := by omega
  refine ⟨b, hb, hg, ?_⟩
  rw [outerArc]
  exact (isSectorPair_outer hT.1 hb hg).not_compat_radius hmb h2 σ

private theorem IsKindP.isTaggedTriangulation {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (h : IsKindP T τ R) : IsTaggedTriangulation T := by
  refine h.sectorData.isTaggedTriangulation h.nonempty (fun σ b hb => ((h.2.1 σ b).1 hb).2)
    (fun r hr => ⟨τ, (h.2.1 τ r).2 ⟨rfl, hr⟩⟩) ?_ ?_
  · intro σ b σ' b' hb hb'
    right
    rw [((h.2.1 σ b).1 hb).1, ((h.2.1 σ' b').1 hb').1]
  · intro σ b hc
    obtain ⟨r, hr, r', hr', hrr'⟩ := Finset.one_lt_card.1 (by have := h.1; omega : 1 < R.card)
    obtain rfl := tag_eq_of_compat hrr' (hc _ ((h.2.1 τ r).2 ⟨rfl, hr⟩))
      (hc _ ((h.2.1 τ r').2 ⟨rfl, hr'⟩))
    by_contra hb
    obtain ⟨a, ha, hg, hnc⟩ := h.not_compat_radius (fun hb' => hb ((h.2.1 σ b).2 ⟨rfl, hb'⟩)) σ
    exact hnc (hc _ (h.2.2.2.1 a ha hg))

private theorem IsDigonKind.sectorData {T : Finset (TaggedArc n)} {a : Fin n}
    (h : IsDigonKind T a) : SectorData T {a} := by
  refine ⟨fun b hb => ?_, fun hc => by simp at hc, fun γ hγ ho =>
    ⟨a, Finset.mem_singleton_self a, Or.inr (h.2.2 γ hγ ho)⟩⟩
  rw [Finset.mem_singleton] at hb
  subst hb
  exact h.2.1

private theorem IsDigonKind.isTaggedTriangulation {T : Finset (TaggedArc n)} {a : Fin n}
    (h : IsDigonKind T a) : IsTaggedTriangulation T := by
  refine h.sectorData.isTaggedTriangulation ⟨a, Finset.mem_singleton_self a⟩
    (fun σ b hb => Finset.mem_singleton.2 ((h.1 σ b).1 hb))
    (fun r hr => ⟨.plain, (h.1 _ _).2 (Finset.mem_singleton.1 hr)⟩) ?_ ?_
  · intro σ b σ' b' hb hb'
    left
    rw [(h.1 σ b).1 hb, (h.1 σ' b').1 hb']
  · intro σ b hc
    exact (h.1 σ b).2 (eq_of_compat_radius (hc _ ((h.1 .plain a).2 rfl))
      (hc _ ((h.1 .notched a).2 rfl)))

/-- An ordinary arc of a tagged triangulation whose shadow has maximal size among the ordinary
arcs of `T` has its first endpoint outside the interior of every ordinary arc of `T`. -/
private theorem IsTaggedTriangulation.notMem_interiorVertices_of_max {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {i j : Fin n} {h : 2 ≤ cdist i j} (hγ : .ordinary i j h ∈ T)
    (hmax : ∀ δ ∈ T.filter TaggedArc.IsOrdinary, (DSeg.arc δ : DSeg n).shadow.card ≤
      (DSeg.arc (.ordinary i j h) : DSeg n).shadow.card)
    {k l : Fin n} {h' : 2 ≤ cdist k l} (hδ : .ordinary k l h' ∈ T) :
    i ∉ interiorVertices k l := by
  intro hi
  have hc := hT.1 _ hγ _ hδ
  simp only [TaggedArc.Compatible] at hc
  obtain ⟨t, ht, hti⟩ := Finset.mem_image.1 hi
  rw [Finset.mem_Ioo] at ht
  have hcl := cdist_lt i j
  have hi1 : i ∈ shadow i j :=
    Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), by simp [vtx_coe]⟩
  have hi2 : i ∈ shadow k l := Finset.mem_image.2 ⟨t, Finset.mem_range.2 ht.2, hti⟩
  have hm1 : (vtx ((i : ℤ) - 1) : Fin n) ∈ shadow k l := by
    refine Finset.mem_image.2 ⟨t - 1, Finset.mem_range.2 (by omega), ?_⟩
    rw [← hti, vtx_sub_coe]
    congr 1
    push_cast [Nat.cast_sub (by omega : 1 ≤ t)]
    ring
  have hm2 : (vtx ((i : ℤ) - 1) : Fin n) ∉ shadow i j := by
    intro hm
    obtain ⟨s, hs, hse⟩ := Finset.mem_image.1 hm
    rw [Finset.mem_range] at hs
    have := eq_of_vtx_eq (n := n) (u := (i : ℤ) - 1) (v := i + s) (by omega) (by omega)
      hse.symm
    omega
  have hle := hmax _ (Finset.mem_filter.2 ⟨hδ, trivial⟩)
  simp only [DSeg.shadow] at hle
  rcases hc with hc | hc | hc
  · have := Finset.card_lt_card (⟨hc, fun h => hm2 (h hm1)⟩ : shadow i j ⊂ shadow k l)
    omega
  · exact hm2 (hc hm1)
  · exact Finset.disjoint_left.1 hc hi1 hi2

private theorem IsTaggedTriangulation.radiusSet_nonempty {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) : (radiusSet T).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hnr : ∀ σ r, TaggedArc.radius σ r ∉ T := fun σ r h => by
    simpa [hne] using mem_radiusSet.2 ⟨σ, h⟩
  by_cases hord : (T.filter TaggedArc.IsOrdinary).Nonempty
  · obtain ⟨γ, hγ, hmax⟩ :=
      Finset.exists_max_image _ (fun γ => (DSeg.arc γ : DSeg n).shadow.card) hord
    rw [Finset.mem_filter] at hγ
    cases γ with
    | radius σ r => exact hγ.2
    | ordinary i j h =>
      refine hnr .plain i (hT.2 _ fun δ hδ => ?_)
      cases δ with
      | radius σ r => exact absurd hδ (hnr σ r)
      | ordinary k l h' => exact hT.notMem_interiorVertices_of_max hγ.1 hmax hδ
  · refine hnr .plain ⟨0, NeZero.pos n⟩ (hT.2 _ fun δ hδ => ?_)
    cases δ with
    | radius σ r => exact absurd hδ (hnr σ r)
    | ordinary k l h' => exact absurd ⟨_, Finset.mem_filter.2 ⟨hδ, trivial⟩⟩ hord

private theorem IsTaggedTriangulation.ord_rep {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {γ : TaggedArc n} (hγ : γ ∈ T) (ho : γ.IsOrdinary) :
    ∃ a ∈ radiusSet T,
      (2 ≤ (radiusSet T).card ∧ 2 ≤ gap (radiusSet T) a ∧ γ = outerArc (radiusSet T) a) ∨
      ∃ c ∈ sectorChords T (radiusSet T) a, ordArc c.1 c.2 = γ := by
  cases γ with
  | radius => exact absurd ho id
  | ordinary i j h =>
    rcases (forall_notMem_interiorVertices_iff hT.radiusSet_nonempty h).1
        (fun r hr => (mem_radiusSet.1 hr).elim fun _ hσ => hT.1 _ hγ _ hσ) with
      ⟨a, ha, c, hc, e⟩ | ⟨hR2, a, ha, hg, e⟩
    · exact ⟨a, ha, Or.inr ⟨c, mem_sectorChords.2 ⟨hc, e ▸ hγ⟩, e⟩⟩
    · exact ⟨a, ha, Or.inl ⟨hR2, hg, e.symm⟩⟩

private theorem IsTaggedTriangulation.ordArc_mem {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {a : Fin n} (ha : a ∈ radiusSet T) {c : ℤ × ℤ}
    (hc : IsSectorPair (radiusSet T) a c)
    (hx : ∀ c' ∈ sectorChords T (radiusSet T) a, ¬RunCross c c') : ordArc c.1 c.2 ∈ T := by
  refine hT.2 _ fun δ hδ => ?_
  cases δ with
  | radius σ r => exact hc.compat_radius ha (mem_radiusSet.2 ⟨σ, hδ⟩) σ
  | ordinary k l h' =>
    obtain ⟨b, hb, ⟨hR2, hg, e⟩ | ⟨d, hd, e⟩⟩ := hT.ord_rep hδ trivial
    · rw [e, outerArc]
      refine hc.compat (c' := ((b : ℤ), (b : ℤ) + gap _ b)) ha hb
        (isSectorPair_outer hR2 hb hg) ?_
      rintro rfl
      exact (not_runCross_outer hc.1 hc.2.1).1
    · rw [← e]
      refine hc.compat ha hb ((mem_sectorChords.1 hd).1.isSectorPair hb) ?_
      rintro rfl
      exact hx d hd

private theorem IsTaggedTriangulation.sectorData {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) : SectorData T (radiusSet T) := by
  refine ⟨fun a ha => ?_, fun hR2 a ha hg => ?_, fun γ hγ ho => hT.ord_rep hγ ho⟩
  · refine isRunTriangulation_iff.2 ⟨fun c hc => (mem_sectorChords.1 hc).1, ?_, ?_⟩
    · intro c hc c' hc'
      have h1 := mem_sectorChords.1 hc
      have h2 := mem_sectorChords.1 hc'
      exact (compatible_ordArc_iff (by have := (gap_spec ha).2.1; omega) h1.1 h2.1).1
        (hT.1 _ h1.2 _ h2.2)
    · intro c hc hcT
      by_contra hcon
      push Not at hcon
      exact hcT (mem_sectorChords.2 ⟨hc, hT.ordArc_mem ha (hc.isSectorPair ha) hcon⟩)
  · rw [outerArc]
    refine hT.ordArc_mem (c := ((a : ℤ), (a : ℤ) + gap _ a)) ha (isSectorPair_outer hR2 ha hg)
      fun c' hc' => ?_
    have := isRunChord_iff'.1 (mem_sectorChords.1 hc').1
    exact (not_runCross_outer this.1 this.2.2.1).2

private theorem IsKindP.of_sectorData {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (hR : 2 ≤ R.card) (hrad : ∀ σ b, TaggedArc.radius σ b ∈ T ↔ σ = τ ∧ b ∈ R)
    (hS : SectorData T R) : IsKindP T τ R := by
  refine ⟨hR, hrad, hS.1, hS.2.1 hR, fun γ hγ ho => ?_⟩
  obtain ⟨a, ha, ⟨-, hg, e⟩ | h⟩ := hS.2.2 γ hγ ho
  exacts [⟨a, ha, Or.inl ⟨hg, e⟩⟩, ⟨a, ha, Or.inr h⟩]

private theorem IsDigonKind.of_sectorData {T : Finset (TaggedArc n)} {a : Fin n}
    (hrad : ∀ σ b, TaggedArc.radius σ b ∈ T ↔ b = a) (hS : SectorData T {a}) :
    IsDigonKind T a := by
  refine ⟨hrad, hS.1 a (Finset.mem_singleton_self a), fun γ hγ ho => ?_⟩
  obtain ⟨b, hb, ⟨hc, -⟩ | h⟩ := hS.2.2 γ hγ ho
  · simp at hc
  · rwa [Finset.mem_singleton.1 hb] at h

private theorem IsTaggedTriangulation.isDigonKind {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {a : Fin n} (ha : TaggedArc.radius .plain a ∈ T)
    (hb : TaggedArc.radius .notched a ∈ T) : IsDigonKind T a := by
  have hrad : ∀ σ c, TaggedArc.radius σ c ∈ T ↔ c = a := fun σ c =>
    ⟨fun hc => eq_of_compat_radius (hT.1 _ hc _ ha) (hT.1 _ hc _ hb), by
      rintro rfl
      cases σ
      exacts [ha, hb]⟩
  have hRa : radiusSet T = {a} := by
    ext c
    rw [mem_radiusSet, Finset.mem_singleton]
    exact ⟨fun ⟨σ, h⟩ => (hrad σ c).1 h, fun h => ⟨.plain, (hrad _ _).2 h⟩⟩
  have hS := hT.sectorData
  rw [hRa] at hS
  exact IsDigonKind.of_sectorData hrad hS

private theorem IsTaggedTriangulation.exists_isKindP {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T)
    (hmix : ∀ a b, TaggedArc.radius .plain a ∈ T → TaggedArc.radius .notched b ∉ T) :
    ∃ τ R, IsKindP T τ R := by
  obtain ⟨r, hr⟩ := hT.radiusSet_nonempty
  obtain ⟨τ, hτ⟩ := mem_radiusSet.1 hr
  have hsame : ∀ σ σ' b b', TaggedArc.radius σ b ∈ T → TaggedArc.radius σ' b' ∈ T → σ = σ' := by
    intro σ σ' b b' h h'
    cases σ <;> cases σ'
    exacts [rfl, absurd h' (hmix _ _ h), absurd h (hmix _ _ h'), rfl]
  have hrad : ∀ σ b, TaggedArc.radius σ b ∈ T ↔ σ = τ ∧ b ∈ radiusSet T := fun σ b =>
    ⟨fun h => ⟨hsame _ _ _ _ h hτ, mem_radiusSet.2 ⟨σ, h⟩⟩, by
      rintro ⟨rfl, hb⟩
      obtain ⟨σ', h'⟩ := mem_radiusSet.1 hb
      rwa [hsame _ _ _ _ hτ h']⟩
  have hcard : 2 ≤ (radiusSet T).card := by
    by_contra hc
    have hRr := eq_singleton_of_card_le_one (by omega) hr
    have hin : TaggedArc.radius (-τ) r ∈ T := by
      refine hT.2 _ fun δ hδ => ?_
      cases δ with
      | radius σ b =>
        have := ((hrad σ b).1 hδ).2
        rw [hRr, Finset.mem_singleton] at this
        exact Or.inl this.symm
      | ordinary k l h' => exact hT.1 _ hτ _ hδ
    have := ((hrad _ _).1 hin).1
    cases τ <;> exact absurd this (by decide)
  exact ⟨τ, _, IsKindP.of_sectorData hcard hrad hT.sectorData⟩

/-- **The three kinds of tagged triangulations**: `T` is a tagged triangulation if and only if it
is of kind `P_+` or `P_-` with some radius set, or of digon kind. -/
@[cluster_algebras "lem_D_structure"]
theorem isTaggedTriangulation_iff_kind {T : Finset (TaggedArc n)} :
    IsTaggedTriangulation T ↔ (∃ τ R, IsKindP T τ R) ∨ ∃ a, IsDigonKind T a := by
  refine ⟨fun hT => ?_, ?_⟩
  · by_cases hmix : ∃ a b, TaggedArc.radius .plain a ∈ T ∧ TaggedArc.radius .notched b ∈ T
    · obtain ⟨a, b, ha, hb⟩ := hmix
      obtain rfl : a = b := Or.resolve_right (hT.1 _ ha _ hb) (by decide)
      exact Or.inr ⟨a, hT.isDigonKind ha hb⟩
    · push Not at hmix
      exact Or.inl (hT.exists_isKindP hmix)
  · rintro (⟨τ, R, hT⟩ | ⟨a, hT⟩)
    exacts [hT.isTaggedTriangulation, hT.isTaggedTriangulation]

/-- **The three kinds of tagged triangulations** are mutually exclusive, and the tag, the radius
set and the doubled position are determined by `T`. -/
@[cluster_algebras "lem_D_structure"]
theorem kind_unique {T : Finset (TaggedArc n)} :
    (∀ τ τ' R R', IsKindP T τ R → IsKindP T τ' R' → τ = τ' ∧ R = R') ∧
      (∀ τ R a, IsKindP T τ R → ¬IsDigonKind T a) ∧
      ∀ a b, IsDigonKind T a → IsDigonKind T b → a = b := by
  refine ⟨?_, ?_, ?_⟩
  · intro τ τ' R R' h h'
    obtain ⟨r, hr⟩ := h.nonempty
    refine ⟨((h'.2.1 τ r).1 ((h.2.1 τ r).2 ⟨rfl, hr⟩)).1, Finset.ext fun b =>
      ⟨fun hb => ((h'.2.1 τ b).1 ((h.2.1 τ b).2 ⟨rfl, hb⟩)).2,
        fun hb => ((h.2.1 τ' b).1 ((h'.2.1 τ' b).2 ⟨rfl, hb⟩)).2⟩⟩
  · intro τ R a h hd
    have h2 := (h.2.1 (-τ) a).1 ((hd.1 (-τ) a).2 rfl)
    cases τ <;> exact absurd h2.1 (by decide)
  · intro a b ha hb
    exact (hb.1 .plain a).1 ((ha.1 .plain a).2 rfl)

private theorem IsSectorPair.ne_radius {R : Finset (Fin n)} {a : Fin n} {c : ℤ × ℤ}
    (h : IsSectorPair R a c) (σ : Tag) (b : Fin n) :
    (ordArc c.1 c.2 : TaggedArc n) ≠ .radius σ b := by
  intro e
  have := h.isOrdinary
  rw [e] at this
  exact this

private theorem outerArc_ne_radius {R : Finset (Fin n)} (hR : 2 ≤ R.card) {a : Fin n}
    (ha : a ∈ R) (hg : 2 ≤ gap R a) (σ : Tag) (b : Fin n) : outerArc R a ≠ .radius σ b :=
  (isSectorPair_outer hR ha hg).ne_radius σ b

/-- The tagged triangulation of kind `P_τ` with radius set `R` and sector data `Ta`. -/
private def kindPSet (τ : Tag) (R : Finset (Fin n)) (Ta : Fin n → Finset (ℤ × ℤ)) :
    Finset (TaggedArc n) :=
  R.image (TaggedArc.radius τ) ∪ (R.filter fun a => 2 ≤ gap R a).image (outerArc R) ∪
    R.biUnion fun a => (Ta a).image fun c => ordArc c.1 c.2

private theorem mem_kindPSet {τ : Tag} {R : Finset (Fin n)} {Ta : Fin n → Finset (ℤ × ℤ)}
    {γ : TaggedArc n} :
    γ ∈ kindPSet τ R Ta ↔ (∃ b ∈ R, TaggedArc.radius τ b = γ) ∨
      (∃ b ∈ R, 2 ≤ gap R b ∧ outerArc R b = γ) ∨ ∃ b ∈ R, ∃ c ∈ Ta b, ordArc c.1 c.2 = γ := by
  simp only [kindPSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_biUnion, or_assoc, and_assoc]

private theorem kindPSet_spec (τ : Tag) {R : Finset (Fin n)} (hR : 2 ≤ R.card)
    {Ta : Fin n → Finset (ℤ × ℤ)} (hTa : ∀ a ∈ R, IsRunTriangulation a (a + gap R a) (Ta a)) :
    IsKindP (kindPSet τ R Ta) τ R ∧ ∀ a ∈ R, sectorChords (kindPSet τ R Ta) R a = Ta a := by
  have hch : ∀ b ∈ R, ∀ c ∈ Ta b, IsSectorPair R b c := fun b hb c hc =>
    ((hTa b hb).1 c hc).isSectorPair hb
  have hsc : ∀ a ∈ R, sectorChords (kindPSet τ R Ta) R a = Ta a := by
    intro a ha
    ext c
    rw [mem_sectorChords, mem_kindPSet]
    constructor
    · rintro ⟨hc, ⟨b, hb, e⟩ | ⟨b, hb, hg, e⟩ | ⟨b, hb, c', hc', e⟩⟩
      · exact absurd e.symm ((hc.isSectorPair ha).ne_radius _ _)
      · rw [outerArc] at e
        obtain ⟨rfl, rfl⟩ := (isSectorPair_outer hR hb hg).eq hb ha (hc.isSectorPair ha) e
        exact absurd rfl hc.2.2.2.2
      · obtain ⟨rfl, rfl⟩ := (hch b hb c' hc').eq hb ha (hc.isSectorPair ha) e
        exact hc'
    · intro hc
      exact ⟨(hTa a ha).1 c hc, Or.inr (Or.inr ⟨a, ha, c, hc, rfl⟩)⟩
  refine ⟨⟨hR, ?_, fun a ha => (hsc a ha).symm ▸ hTa a ha, fun a ha hg =>
    mem_kindPSet.2 (Or.inr (Or.inl ⟨a, ha, hg, rfl⟩)), ?_⟩, hsc⟩
  · intro σ b
    rw [mem_kindPSet]
    constructor
    · rintro (⟨b', hb', e⟩ | ⟨b', hb', hg, e⟩ | ⟨b', hb', c, hc, e⟩)
      · rw [TaggedArc.radius.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact ⟨rfl, hb'⟩
      · exact absurd e (outerArc_ne_radius hR hb' hg _ _)
      · exact absurd e ((hch b' hb' c hc).ne_radius _ _)
    · rintro ⟨rfl, hb⟩
      exact Or.inl ⟨b, hb, rfl⟩
  · intro γ hγ ho
    rcases mem_kindPSet.1 hγ with ⟨b, hb, rfl⟩ | ⟨b, hb, hg, rfl⟩ | ⟨b, hb, c, hc, rfl⟩
    · exact absurd ho id
    · exact ⟨b, hb, Or.inl ⟨hg, rfl⟩⟩
    · exact ⟨b, hb, Or.inr ⟨c, (hsc b hb).symm ▸ hc, rfl⟩⟩

private theorem IsKindP.eq_kindPSet {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (h : IsKindP T τ R) : T = kindPSet τ R (sectorChords T R) := by
  ext γ
  rw [mem_kindPSet]
  constructor
  · intro hγ
    cases γ with
    | radius σ b =>
      obtain ⟨rfl, hb⟩ := (h.2.1 σ b).1 hγ
      exact Or.inl ⟨b, hb, rfl⟩
    | ordinary i j hij =>
      obtain ⟨b, hb, ⟨hg, e⟩ | ⟨c, hc, e⟩⟩ := h.2.2.2.2 _ hγ trivial
      · exact Or.inr (Or.inl ⟨b, hb, hg, e.symm⟩)
      · exact Or.inr (Or.inr ⟨b, hb, c, hc, e⟩)
  · rintro (⟨b, hb, rfl⟩ | ⟨b, hb, hg, rfl⟩ | ⟨b, hb, c, hc, rfl⟩)
    · exact (h.2.1 τ b).2 ⟨rfl, hb⟩
    · exact h.2.2.2.1 b hb hg
    · exact (mem_sectorChords.1 hc).2

/-- **The three kinds of tagged triangulations**: for `|R| ≥ 2` and a choice of triangulations
`T_a` of the sector runs of `a ∈ R`, exactly one tagged triangulation of kind `P_τ` with radius
set `R` has `T_R(a) = T_a` for all `a ∈ R`. -/
@[cluster_algebras "lem_D_structure"]
theorem existsUnique_isKindP (τ : Tag) {R : Finset (Fin n)} (hR : 2 ≤ R.card)
    (Ta : Fin n → Finset (ℤ × ℤ)) (hTa : ∀ a ∈ R, IsRunTriangulation a (a + gap R a) (Ta a)) :
    ∃! T : Finset (TaggedArc n), IsKindP T τ R ∧ ∀ a ∈ R, sectorChords T R a = Ta a := by
  refine ⟨kindPSet τ R Ta, kindPSet_spec τ hR hTa, ?_⟩
  rintro T ⟨h, hsc⟩
  rw [h.eq_kindPSet, kindPSet, kindPSet]
  congr 1
  exact Finset.biUnion_congr rfl fun b hb => by rw [hsc b hb]

/-- The tagged triangulation of digon kind at `a` with sector data `Ta`. -/
private def digonSet (a : Fin n) (Ta : Finset (ℤ × ℤ)) : Finset (TaggedArc n) :=
  {TaggedArc.radius .plain a, TaggedArc.radius .notched a} ∪ Ta.image fun c => ordArc c.1 c.2

private theorem mem_digonSet {a : Fin n} {Ta : Finset (ℤ × ℤ)} {γ : TaggedArc n} :
    γ ∈ digonSet a Ta ↔ (∃ σ, TaggedArc.radius σ a = γ) ∨ ∃ c ∈ Ta, ordArc c.1 c.2 = γ := by
  simp only [digonSet, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image]
  constructor
  · rintro ((rfl | rfl) | h)
    exacts [Or.inl ⟨_, rfl⟩, Or.inl ⟨_, rfl⟩, Or.inr h]
  · rintro (⟨⟨⟩, rfl⟩ | h)
    exacts [Or.inl (Or.inl rfl), Or.inl (Or.inr rfl), Or.inr h]

private theorem digonSet_spec (a : Fin n) {Ta : Finset (ℤ × ℤ)}
    (hTa : IsRunTriangulation a (a + gap {a} a) Ta) :
    IsDigonKind (digonSet a Ta) a ∧ sectorChords (digonSet a Ta) {a} a = Ta := by
  have ha := Finset.mem_singleton_self a
  have hch : ∀ c ∈ Ta, IsSectorPair {a} a c := fun c hc => (hTa.1 c hc).isSectorPair ha
  have hsc : sectorChords (digonSet a Ta) {a} a = Ta := by
    ext c
    rw [mem_sectorChords, mem_digonSet]
    constructor
    · rintro ⟨hc, ⟨σ, e⟩ | ⟨c', hc', e⟩⟩
      · exact absurd e.symm ((hc.isSectorPair ha).ne_radius _ _)
      · obtain ⟨-, rfl⟩ := (hch c' hc').eq ha ha (hc.isSectorPair ha) e
        exact hc'
    · intro hc
      exact ⟨hTa.1 c hc, Or.inr ⟨c, hc, rfl⟩⟩
  refine ⟨⟨?_, hsc.symm ▸ hTa, ?_⟩, hsc⟩
  · intro σ b
    rw [mem_digonSet]
    constructor
    · rintro (⟨σ', e⟩ | ⟨c, hc, e⟩)
      · rw [TaggedArc.radius.injEq] at e
        exact e.2.symm
      · exact absurd e ((hch c hc).ne_radius _ _)
    · rintro rfl
      exact Or.inl ⟨σ, rfl⟩
  · intro γ hγ ho
    rcases mem_digonSet.1 hγ with ⟨σ, rfl⟩ | ⟨c, hc, rfl⟩
    · exact absurd ho id
    · exact ⟨c, hsc.symm ▸ hc, rfl⟩

private theorem IsDigonKind.eq_digonSet {T : Finset (TaggedArc n)} {a : Fin n}
    (h : IsDigonKind T a) : T = digonSet a (sectorChords T {a} a) := by
  ext γ
  rw [mem_digonSet]
  constructor
  · intro hγ
    cases γ with
    | radius σ b =>
      obtain rfl := (h.1 σ b).1 hγ
      exact Or.inl ⟨σ, rfl⟩
    | ordinary i j hij => exact Or.inr (h.2.2 _ hγ trivial)
  · rintro (⟨σ, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact (h.1 σ a).2 rfl
    · exact (mem_sectorChords.1 hc).2

/-- **The three kinds of tagged triangulations**: for a position `a` and a triangulation `T_a`
of `[a, a + n]`, exactly one tagged triangulation of digon kind at `a` has `T_R(a) = T_a`. -/
@[cluster_algebras "lem_D_structure"]
theorem existsUnique_isDigonKind (a : Fin n) {Ta : Finset (ℤ × ℤ)}
    (hTa : IsRunTriangulation a (a + gap {a} a) Ta) :
    ∃! T : Finset (TaggedArc n), IsDigonKind T a ∧ sectorChords T {a} a = Ta := by
  refine ⟨digonSet a Ta, digonSet_spec a hTa, ?_⟩
  rintro T ⟨h, hsc⟩
  rw [h.eq_digonSet, hsc]

private theorem IsKindP.card_eq {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (h : IsKindP T τ R) : T.card = n := by
  classical
  have hR := h.nonempty
  have hch : ∀ b ∈ R, ∀ c ∈ sectorChords T R b, IsSectorPair R b c := fun b hb c hc =>
    (mem_sectorChords.1 hc).1.isSectorPair hb
  rw [h.eq_kindPSet, kindPSet, Finset.card_union_eq_card_add_card.2,
    Finset.card_union_eq_card_add_card.2,
    Finset.card_image_of_injective _ (fun b b' e => by injection e),
    Finset.card_image_of_injOn, Finset.card_biUnion, Finset.card_filter]
  · have hs : ∀ a ∈ R, ((sectorChords T R a).image
        fun c => (ordArc c.1 c.2 : TaggedArc n)).card = (sectorChords T R a).card :=
      fun a ha => Finset.card_image_of_injOn (fun c hc c' hc' e =>
        ((hch a ha c hc).eq ha ha (hch a ha c' hc') e).2)
    rw [Finset.sum_congr rfl hs, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    conv_rhs => rw [← sum_gap hR]
    refine Finset.sum_congr rfl fun a ha => ?_
    have := (h.2.2.1 a ha).card (by have := (gap_spec ha).1; omega)
    simp only [add_sub_cancel_left] at this
    split_ifs at this ⊢ <;> omega
  · intro a ha a' ha' haa'
    rw [Function.onFun, Finset.disjoint_left]
    intro γ hγ hγ'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨c', hc', e⟩ := Finset.mem_image.1 hγ'
    exact haa' ((hch a' ha' c' hc').eq ha' ha (hch a ha c hc) e).1.symm
  · exact fun _ _ _ _ e => eq_of_outerArc_eq e
  · rw [Finset.disjoint_left]
    intro γ hγ hγ'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨b', hb', e⟩ := Finset.mem_image.1 hγ'
    rw [Finset.mem_filter] at hb'
    exact outerArc_ne_radius h.1 hb'.1 hb'.2 _ _ e
  · rw [Finset.disjoint_left]
    intro γ hγ hγ'
    obtain ⟨a, ha, hγa⟩ := Finset.mem_biUnion.1 hγ'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγa
    rcases Finset.mem_union.1 hγ with hγ | hγ
    · obtain ⟨b, hb, e⟩ := Finset.mem_image.1 hγ
      exact (hch a ha c hc).ne_radius _ _ e.symm
    · obtain ⟨b', hb', e⟩ := Finset.mem_image.1 hγ
      rw [Finset.mem_filter] at hb'
      rw [outerArc] at e
      obtain ⟨rfl, rfl⟩ := (isSectorPair_outer h.1 hb'.1 hb'.2).eq hb'.1 ha (hch a ha c hc) e
      exact (mem_sectorChords.1 hc).1.2.2.2.2 rfl

private theorem IsDigonKind.card_eq (hn : 3 ≤ n) {T : Finset (TaggedArc n)} {a : Fin n}
    (h : IsDigonKind T a) : T.card = n := by
  classical
  have ha := Finset.mem_singleton_self a
  have hch : ∀ c ∈ sectorChords T {a} a, IsSectorPair {a} a c := fun c hc =>
    (mem_sectorChords.1 hc).1.isSectorPair ha
  have hc := h.2.1.card (by have := (gap_singleton a).1; omega)
  rw [(gap_singleton a).1, add_sub_cancel_left, if_pos (by omega)] at hc
  rw [h.eq_digonSet, digonSet, Finset.card_union_eq_card_add_card.2,
    Finset.card_image_of_injOn (fun c hc c' hc' e => ((hch c hc).eq ha ha (hch c' hc') e).2)]
  · rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    omega
  · rw [Finset.disjoint_left]
    intro γ hγ hγ'
    obtain ⟨c, hc, e⟩ := Finset.mem_image.1 hγ'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
    rcases hγ with rfl | rfl <;> exact (hch c hc).ne_radius _ _ e

/-- **A tagged triangulation has `n` tagged arcs.** -/
@[cluster_algebras "lem_D_size"]
theorem IsTaggedTriangulation.card_eq (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) : T.card = n := by
  rcases isTaggedTriangulation_iff_kind.1 hT with ⟨τ, R, h⟩ | ⟨a, h⟩
  · exact h.card_eq
  · exact h.card_eq hn

/-! ### Flips -/

/-- The **flip** `(T \ {γ}) ∪ {γ'}` of `T` at `γ` with replacement `γ'`. -/
@[cluster_algebras "def_D_flip"]
def dFlip (T : Finset (TaggedArc n)) (γ γ' : TaggedArc n) : Finset (TaggedArc n) :=
  insert γ' (T.erase γ)

/-- `γ'` is the **replacement** of `γ` in a flip of the tagged triangulation `T`: `γ ∈ T`,
`γ' ∉ T`, and `(T \ {γ}) ∪ {γ'}` is a tagged triangulation. The passage from `T` to
`dFlip T γ γ'` is then the *flip of `T` at `γ`*; by
`IsTaggedTriangulation.existsUnique_isDFlipReplacement` the replacement exists and is unique. -/
@[cluster_algebras "def_D_flip"]
def IsDFlipReplacement (T : Finset (TaggedArc n)) (γ γ' : TaggedArc n) : Prop :=
  IsTaggedTriangulation T ∧ γ ∈ T ∧ γ' ∉ T ∧ IsTaggedTriangulation (dFlip T γ γ')

/-- Being a replacement is decidable. -/
instance instDecidableIsDFlipReplacement (T : Finset (TaggedArc n)) (γ γ' : TaggedArc n) :
    Decidable (IsDFlipReplacement T γ γ') := by
  unfold IsDFlipReplacement; infer_instance

/-- Flipping back: if `γ'` replaces `γ` in `T`, then `γ` replaces `γ'` in the flip, and flipping
it gives back `T`. -/
@[cluster_algebras "def_D_flip"]
theorem IsDFlipReplacement.symm {T : Finset (TaggedArc n)} {γ γ' : TaggedArc n}
    (h : IsDFlipReplacement T γ γ') :
    IsDFlipReplacement (dFlip T γ γ') γ' γ ∧ dFlip (dFlip T γ γ') γ' γ = T := by
  obtain ⟨hT, hγ, hγ', hT'⟩ := h
  have hne : γ ≠ γ' := fun e => hγ' (e ▸ hγ)
  have hback : dFlip (dFlip T γ γ') γ' γ = T := by
    rw [dFlip, dFlip, Finset.erase_insert (fun hm => hγ' (Finset.mem_of_mem_erase hm)),
      Finset.insert_erase hγ]
  refine ⟨⟨hT', Finset.mem_insert_self _ _, ?_, by rwa [hback]⟩, hback⟩
  rw [dFlip, Finset.mem_insert, not_or]
  exact ⟨hne, fun hm => (Finset.mem_erase.1 hm).1 rfl⟩

omit [NeZero n] in
/-- Membership in the flip `dFlip T γ γ'`. -/
theorem mem_dFlip {T : Finset (TaggedArc n)} {γ γ' δ : TaggedArc n} :
    δ ∈ dFlip T γ γ' ↔ δ = γ' ∨ (δ ≠ γ ∧ δ ∈ T) := by
  rw [dFlip, Finset.mem_insert, Finset.mem_erase]

omit [NeZero n] in
private theorem mem_dFlip_of_ne {T : Finset (TaggedArc n)} {γ γ' δ : TaggedArc n} (h : δ ≠ γ)
    (h' : δ ≠ γ') : δ ∈ dFlip T γ γ' ↔ δ ∈ T := by
  simp [mem_dFlip, h, h']

private theorem sectorChords_dFlip_self {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    {a : Fin n} (ha : a ∈ R) {c c' : ℤ × ℤ} (hc : c ∈ sectorChords T R a)
    (hc' : IsRunChord a (a + gap R a) c') :
    sectorChords (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) R a =
      insert c' ((sectorChords T R a).erase c) := by
  have hcp := (mem_sectorChords.1 hc).1.isSectorPair ha
  have hc'p := hc'.isSectorPair ha
  ext d
  rw [mem_sectorChords, mem_dFlip, Finset.mem_insert, Finset.mem_erase, mem_sectorChords]
  constructor
  · rintro ⟨hd, e | ⟨hne, hdT⟩⟩
    · exact Or.inl ((hd.isSectorPair ha).eq ha ha hc'p e).2
    · exact Or.inr ⟨fun h => hne (by rw [h]), hd, hdT⟩
  · rintro (rfl | ⟨hne, hd, hdT⟩)
    · exact ⟨hc', Or.inl rfl⟩
    · exact ⟨hd, Or.inr ⟨fun e => hne ((hd.isSectorPair ha).eq ha ha hcp e).2, hdT⟩⟩

private theorem SectorData.dFlip_ord {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    (hS : SectorData T R) {a : Fin n} (ha : a ∈ R) {c c' : ℤ × ℤ}
    (hf : IsRunFlip a (a + gap R a) (sectorChords T R a) c c') :
    SectorData (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) R ∧
      sectorChords (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) R a =
        insert c' ((sectorChords T R a).erase c) ∧
      (∀ b ∈ R, b ≠ a → sectorChords (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) R b =
        sectorChords T R b) ∧
      ∀ σ x, TaggedArc.radius σ x ∈ dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2) ↔
        TaggedArc.radius σ x ∈ T := by
  obtain ⟨-, hcT, hc'ch, -, htri⟩ := hf
  have hcch := (mem_sectorChords.1 hcT).1
  have hcp := hcch.isSectorPair ha
  have hc'p := hc'ch.isSectorPair ha
  have hsa := sectorChords_dFlip_self ha hcT hc'ch
  have hsb : ∀ b ∈ R, b ≠ a →
      sectorChords (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) R b = sectorChords T R b := by
    intro b hb hba
    ext d
    rw [mem_sectorChords, mem_sectorChords]
    exact and_congr_right fun hd =>
      mem_dFlip_of_ne (fun e => hba ((hd.isSectorPair hb).eq hb ha hcp e).1)
        (fun e => hba ((hd.isSectorPair hb).eq hb ha hc'p e).1)
  refine ⟨⟨fun b hb => ?_, ?_, ?_⟩, hsa, hsb, fun σ x => mem_dFlip_of_ne
    (fun e => hcp.ne_radius _ _ e.symm) (fun e => hc'p.ne_radius _ _ e.symm)⟩
  · by_cases hba : b = a
    · subst hba
      rwa [hsa]
    · rw [hsb b hb hba]
      exact hS.1 b hb
  · intro hR2 b hb hg
    refine mem_dFlip.2 (Or.inr ⟨fun e => ?_, hS.2.1 hR2 b hb hg⟩)
    rw [outerArc] at e
    obtain ⟨rfl, h⟩ := (isSectorPair_outer hR2 hb hg).eq hb ha hcp e
    exact hcch.2.2.2.2 h.symm
  · intro δ hδ ho
    rcases mem_dFlip.1 hδ with rfl | ⟨hne, hδT⟩
    · exact ⟨a, ha, Or.inr ⟨c', by rw [hsa]; exact Finset.mem_insert_self _ _, rfl⟩⟩
    · obtain ⟨b, hb, ⟨hR2, hg, e⟩ | ⟨d, hd, rfl⟩⟩ := hS.2.2 δ hδT ho
      · exact ⟨b, hb, Or.inl ⟨hR2, hg, e⟩⟩
      · refine ⟨b, hb, Or.inr ⟨d, ?_, rfl⟩⟩
        by_cases hba : b = a
        · subst hba
          rw [hsa]
          exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h => hne (by rw [h]), hd⟩)
        · rwa [hsb b hb hba]

private theorem IsKindP.isDFlipReplacement_ordArc' {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) {c c' : ℤ × ℤ}
    (hc : IsRunFlip a (a + gap R a) (sectorChords T R a) c c') :
    IsDFlipReplacement T (ordArc c.1 c.2) (ordArc c'.1 c'.2) ∧
      IsKindP (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) τ R ∧
      sectorChords (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) R a =
        insert c' ((sectorChords T R a).erase c) ∧
      ∀ b ∈ R, b ≠ a →
        sectorChords (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) R b = sectorChords T R b := by
  obtain ⟨hS', hsa, hsb, hrad⟩ := hT.sectorData.dFlip_ord ha hc
  have hK : IsKindP (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) τ R :=
    IsKindP.of_sectorData hT.1 (fun σ x => (hrad σ x).trans (hT.2.1 σ x)) hS'
  exact ⟨⟨hT.isTaggedTriangulation, (mem_sectorChords.1 hc.2.1).2,
    fun h => hc.2.2.2.1 (mem_sectorChords.2 ⟨hc.2.2.1, h⟩), hK.isTaggedTriangulation⟩,
    hK, hsa, hsb⟩

private theorem IsDigonKind.isDFlipReplacement_ordArc' {T : Finset (TaggedArc n)}
    {a : Fin n} (hT : IsDigonKind T a) {c c' : ℤ × ℤ}
    (hc : IsRunFlip a (a + gap {a} a) (sectorChords T {a} a) c c') :
    IsDFlipReplacement T (ordArc c.1 c.2) (ordArc c'.1 c'.2) ∧
      IsDigonKind (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) a ∧
      sectorChords (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) {a} a =
        insert c' ((sectorChords T {a} a).erase c) := by
  obtain ⟨hS', hsa, -, hrad⟩ := hT.sectorData.dFlip_ord (Finset.mem_singleton_self a) hc
  have hK : IsDigonKind (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) a :=
    IsDigonKind.of_sectorData (fun σ x => (hrad σ x).trans (hT.1 σ x)) hS'
  exact ⟨⟨hT.isTaggedTriangulation, (mem_sectorChords.1 hc.2.1).2,
    fun h => hc.2.2.2.1 (mem_sectorChords.2 ⟨hc.2.2.1, h⟩), hK.isTaggedTriangulation⟩, hK, hsa⟩

omit [NeZero n] in
private theorem ne_pair_iff {d : ℤ × ℤ} {x y : ℤ} : d ≠ (x, y) ↔ d.1 ≠ x ∨ d.2 ≠ y := by
  rw [Ne, Prod.ext_iff, not_and_or]

private theorem gap_insert_left {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) {y : ℤ}
    (h1 : (a : ℤ) < y) (h2 : y < a + gap R a) : (gap (insert (vtx y) R) a : ℤ) = y - a := by
  have g := gap_spec ha
  have := gap_eq_of (R := insert (vtx y) R) (Finset.mem_insert_of_mem ha) (g := (y - a).toNat)
    (by omega) ?_ ?_
  · rw [this]; omega
  · rw [show (a : ℤ) + ((y - a).toNat : ℤ) = y by omega]
    exact Finset.mem_insert_self _ _
  · intro m hm1 hm2 hm
    rcases Finset.mem_insert.1 hm with hm | hm
    · have := eq_of_vtx_eq (n := n) (u := m) (v := y) (by omega) (by omega) hm
      omega
    · exact notMem_of_lt_gap ha hm1 (by omega) hm

private theorem gap_insert_right {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) {y : ℤ}
    (h1 : (a : ℤ) < y) (h2 : y < a + gap R a) :
    (gap (insert (vtx y) R) (vtx y) : ℤ) = a + gap R a - y := by
  have g := gap_spec ha
  obtain ⟨k, hk⟩ := coe_vtx_eq (n := n) y
  have := gap_eq_of (R := insert (vtx y) R) (Finset.mem_insert_self _ _)
    (g := ((a : ℤ) + gap R a - y).toNat) (by omega) ?_ ?_
  · rw [this]; omega
  · rw [hk, show y + k * n + (((a : ℤ) + gap R a - y).toNat : ℤ) = (a + gap R a) + k * n by
      omega, vtx_add_mul]
    exact Finset.mem_insert_of_mem g.2.2.1
  · intro m hm1 hm2 hm
    rw [hk] at hm1 hm2
    rw [← vtx_sub_mul m k, Finset.mem_insert] at hm
    rcases hm with hm | hm
    · have := eq_of_vtx_eq (n := n) (u := y) (v := m - k * n) (by omega) (by omega) hm.symm
      omega
    · exact notMem_of_lt_gap ha (by omega) (by omega) hm

private theorem gap_insert_other {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) {y : ℤ}
    (h1 : (a : ℤ) < y) (h2 : y < a + gap R a) {b : Fin n} (hb : b ∈ R) (hba : b ≠ a) :
    gap (insert (vtx y) R) b = gap R b := by
  have g := gap_spec hb
  refine gap_eq_of (Finset.mem_insert_of_mem hb) g.1 (Finset.mem_insert_of_mem g.2.2.1) ?_
  intro m hm1 hm2 hm
  rcases Finset.mem_insert.1 hm with hm | hm
  · exact hba (sector_repr_unique hb ha hm1.le hm2 h1.le h2 hm).1
  · exact notMem_of_lt_gap hb hm1 hm2 hm

private theorem outerArc_singleton_not_ordinary (a : Fin n) : ¬(outerArc {a} a).IsOrdinary := by
  rw [outerArc, (gap_singleton a).1, ordArc, dif_neg]
  · exact id
  · rw [vtx_add_n, vtx_coe]
    simp [cdist]

private theorem IsRunTriangle.mem_left {u v y : ℤ} {T : Finset (ℤ × ℤ)}
    (hy : IsRunTriangle u v T u y v) (h : 2 ≤ y - u) : (u, y) ∈ T := by
  have := hy.2.1
  rcases hy.2.2.1 with h' | h' | h'
  · exact h'
  · dsimp only at h'; omega
  · rw [Prod.ext_iff] at h'; dsimp only at h'; omega

private theorem IsRunTriangle.mem_right {u v y : ℤ} {T : Finset (ℤ × ℤ)}
    (hy : IsRunTriangle u v T u y v) (h : 2 ≤ v - y) : (y, v) ∈ T := by
  have := hy.1
  rcases hy.2.2.2.1 with h' | h' | h'
  · exact h'
  · dsimp only at h'; omega
  · rw [Prod.ext_iff] at h'; dsimp only at h'; omega

/-- The chords of the lower part `[a, y]` of a split sector run. -/
private theorem sectorChords_insert_low {T T' : Finset (TaggedArc n)} {R : Finset (Fin n)}
    {a : Fin n} (ha : a ∈ R) {y : ℤ} (h1 : (a : ℤ) < y) (h2 : y < a + gap R a)
    (hT' : ∀ d, IsSectorPair R a d → d ≠ ((a : ℤ), (a : ℤ) + gap R a) →
      (ordArc d.1 d.2 ∈ T' ↔ ordArc d.1 d.2 ∈ T)) :
    sectorChords T' (insert (vtx y) R) a =
      (sectorChords T R a).filter (fun c => c.2 ≤ y ∧ c ≠ ((a : ℤ), y)) := by
  have g := gap_spec ha
  have el : (a : ℤ) + gap (insert (vtx y) R) a = y := by rw [gap_insert_left ha h1 h2]; ring
  ext d
  rw [mem_sectorChords, Finset.mem_filter, mem_sectorChords, el]
  constructor
  · rintro ⟨hd, hdT'⟩
    have hd' := isRunChord_iff'.1 hd
    have hp : IsSectorPair R a d := ⟨hd'.1, by omega, hd'.2.2.2.1, by omega⟩
    have hT := (hT' d hp (ne_pair_iff.2 (Or.inr (by omega)))).1 hdT'
    refine ⟨⟨isRunChord_iff'.2 ⟨hd'.1, hd'.2.1, by omega, hd'.2.2.2.1, Or.inr (by omega)⟩, hT⟩,
      hd'.2.2.1, ne_pair_iff.2 hd'.2.2.2.2⟩
  · rintro ⟨⟨hd, hdT⟩, hdy, hne⟩
    have hd' := isRunChord_iff'.1 hd
    refine ⟨isRunChord_iff'.2 ⟨hd'.1, hd'.2.1, hdy, hd'.2.2.2.1, ne_pair_iff.1 hne⟩, ?_⟩
    exact (hT' d (hd.isSectorPair ha) (ne_pair_iff.2 (Or.inr (by omega)))).2 hdT

/-- The chords of the upper part `[y, a + g_R(a)]` of a split sector run, shifted to the sector
run of `ȳ`. -/
private theorem sectorChords_insert_up {T T' : Finset (TaggedArc n)} {R : Finset (Fin n)}
    {a : Fin n} (ha : a ∈ R) {y : ℤ} (h1 : (a : ℤ) < y) (h2 : y < a + gap R a) {k : ℤ}
    (hk : ((vtx y : Fin n) : ℤ) = y + k * n)
    (hT' : ∀ d, IsSectorPair R a d → d ≠ ((a : ℤ), (a : ℤ) + gap R a) →
      (ordArc d.1 d.2 ∈ T' ↔ ordArc d.1 d.2 ∈ T)) :
    sectorChords T' (insert (vtx y) R) (vtx y) =
      ((sectorChords T R a).filter (fun c => y ≤ c.1 ∧ c ≠ (y, (a : ℤ) + gap R a))).image
        (shiftPair (k * n)) := by
  have g := gap_spec ha
  have e2 : ((vtx y : Fin n) : ℤ) + gap (insert (vtx y) R) (vtx y) = a + gap R a + k * n := by
    rw [gap_insert_right ha h1 h2, hk]; ring
  ext d
  rw [mem_sectorChords, Finset.mem_image, e2, hk]
  constructor
  · rintro ⟨hd, hdT'⟩
    have hd' := isRunChord_iff'.1 hd
    have hp : IsSectorPair R a (d.1 - k * n, d.2 - k * n) :=
      ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega⟩
    have hoe : (ordArc d.1 d.2 : TaggedArc n) = ordArc (d.1 - k * n) (d.2 - k * n) :=
      ordArc_congr (vtx_sub_mul _ _).symm (vtx_sub_mul _ _).symm
    have hT := (hT' _ hp (ne_pair_iff.2 (Or.inl (by dsimp only; omega)))).1 (hoe ▸ hdT')
    refine ⟨(d.1 - k * n, d.2 - k * n), Finset.mem_filter.2 ⟨mem_sectorChords.2
      ⟨isRunChord_iff'.2 ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega, Or.inl (by dsimp only; omega)⟩, hT⟩, by dsimp only; omega,
        ne_pair_iff.2 (by dsimp only; omega)⟩, ?_⟩
    simp only [shiftPair, sub_add_cancel]
  · rintro ⟨e, he, rfl⟩
    rw [Finset.mem_filter, mem_sectorChords] at he
    obtain ⟨⟨hech, heT⟩, hey, hne⟩ := he
    have he' := isRunChord_iff'.1 hech
    have hne' := ne_pair_iff.1 hne
    refine ⟨isRunChord_iff'.2 ⟨by simp only [shiftPair]; omega, by simp only [shiftPair]; omega,
      by simp only [shiftPair]; omega, by simp only [shiftPair]; omega,
      by simp only [shiftPair]; omega⟩, ?_⟩
    have hoe : (ordArc (shiftPair (k * n) e).1 (shiftPair (k * n) e).2 : TaggedArc n) =
        ordArc e.1 e.2 := ordArc_congr (vtx_add_mul _ _) (vtx_add_mul _ _)
    rw [hoe]
    exact (hT' e (hech.isSectorPair ha) (ne_pair_iff.2 (Or.inl (by omega)))).2 heT

/-- After splitting the sector of `a` at the apex `y` of its outer side, an ordinary arc of `T`
other than the outer arc of `a` is an outer arc or a segment of a sector-run chord. -/
private theorem SectorData.split_ord {T T' : Finset (TaggedArc n)} {R : Finset (Fin n)}
    (hS : SectorData T R) {a : Fin n} (ha : a ∈ R) {y : ℤ}
    (hy : IsRunTriangle a (a + gap R a) (sectorChords T R a) a y (a + gap R a))
    (hT' : ∀ d, IsSectorPair R a d → d ≠ ((a : ℤ), (a : ℤ) + gap R a) →
      (ordArc d.1 d.2 ∈ T' ↔ ordArc d.1 d.2 ∈ T))
    (hother : ∀ b ∈ R, b ≠ a → ∀ d, IsSectorPair R b d →
      (ordArc d.1 d.2 ∈ T' ↔ ordArc d.1 d.2 ∈ T))
    {δ : TaggedArc n} (hδT : δ ∈ T) (ho : δ.IsOrdinary) (hne : δ ≠ outerArc R a) :
    ∃ b ∈ insert (vtx y) R, (2 ≤ (insert (vtx y) R).card ∧ 2 ≤ gap (insert (vtx y) R) b ∧
      δ = outerArc (insert (vtx y) R) b) ∨
      ∃ c ∈ sectorChords T' (insert (vtx y) R) b, ordArc c.1 c.2 = δ := by
  have y1 := hy.1
  have y2 := hy.2.1
  have hgl := gap_insert_left ha y1 y2
  have hgr := gap_insert_right ha y1 y2
  have hgo := fun b (hb : b ∈ R) (hba : b ≠ a) => gap_insert_other ha y1 y2 hb hba
  obtain ⟨k, hk⟩ := coe_vtx_eq (n := n) y
  have e2 : ((vtx y : Fin n) : ℤ) + gap (insert (vtx y) R) (vtx y) = a + gap R a + k * n := by
    rw [hgr, hk]; ring
  have hcard : 2 ≤ (insert (vtx y) R).card := by
    rw [Finset.card_insert_of_notMem (notMem_of_lt_gap ha y1 y2)]
    have := Finset.card_pos.2 ⟨a, ha⟩
    omega
  obtain ⟨b, hb, ⟨hR2, hg, e⟩ | ⟨d, hd, e⟩⟩ := hS.2.2 δ hδT ho
  · have hba : b ≠ a := by rintro rfl; exact hne e
    refine ⟨b, Finset.mem_insert_of_mem hb, Or.inl ⟨hcard, by rwa [hgo b hb hba], ?_⟩⟩
    rw [e, outerArc, outerArc, hgo b hb hba]
  by_cases hba : b = a
  · subst hba
    have hd' := isRunChord_iff'.1 (mem_sectorChords.1 hd).1
    rcases ((hS.1 b ha).eq_runGlue_of_isRunTriangle hy).1 d hd with h2 | h1
    · by_cases hdy : d = ((b : ℤ), y)
      · subst hdy
        refine ⟨b, Finset.mem_insert_of_mem ha, Or.inl ⟨hcard, by dsimp only at hd'; omega, ?_⟩⟩
        rw [outerArc, ← e, show (b : ℤ) + gap (insert (vtx y) R) b = y by rw [hgl]; ring]
      · refine ⟨b, Finset.mem_insert_of_mem ha, Or.inr ⟨d, ?_, e⟩⟩
        rw [sectorChords_insert_low ha y1 y2 hT']
        exact Finset.mem_filter.2 ⟨hd, h2, hdy⟩
    · by_cases hdy : d = (y, (b : ℤ) + gap R b)
      · subst hdy
        refine ⟨vtx y, Finset.mem_insert_self _ _, Or.inl ⟨hcard, by
          dsimp only at hd'; omega, ?_⟩⟩
        rw [← e, outerArc, e2]
        exact (ordArc_congr (vtx_coe _) (vtx_add_mul _ _)).symm
      · refine ⟨vtx y, Finset.mem_insert_self _ _, Or.inr ⟨shiftPair (k * n) d, ?_, ?_⟩⟩
        · rw [sectorChords_insert_up ha y1 y2 hk hT']
          exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hd, h1, hdy⟩)
        · rw [← e]
          exact ordArc_congr (vtx_add_mul _ _) (vtx_add_mul _ _)
  · have hd' := mem_sectorChords.1 hd
    refine ⟨b, Finset.mem_insert_of_mem hb, Or.inr ⟨d, ?_, e⟩⟩
    rw [mem_sectorChords, hgo b hb hba]
    exact ⟨hd'.1, (hother b hb hba d (hd'.1.isSectorPair hb)).2 hd'.2⟩

/-- Splitting the sector of `a` at the apex `y` of its outer side. -/
private theorem SectorData.split {T T' : Finset (TaggedArc n)} {R : Finset (Fin n)}
    (hS : SectorData T R) {a : Fin n} (ha : a ∈ R) {y : ℤ}
    (hy : IsRunTriangle a (a + gap R a) (sectorChords T R a) a y (a + gap R a))
    (hT' : ∀ d, IsSectorPair R a d → d ≠ ((a : ℤ), (a : ℤ) + gap R a) →
      (ordArc d.1 d.2 ∈ T' ↔ ordArc d.1 d.2 ∈ T))
    (hother : ∀ b ∈ R, b ≠ a → ∀ d, IsSectorPair R b d →
      (ordArc d.1 d.2 ∈ T' ↔ ordArc d.1 d.2 ∈ T))
    (hord : ∀ δ ∈ T', δ.IsOrdinary → δ ∈ T ∧ δ ≠ outerArc R a) :
    SectorData T' (insert (vtx y) R) := by
  have y1 := hy.1
  have y2 := hy.2.1
  have hgl := gap_insert_left ha y1 y2
  have hgr := gap_insert_right ha y1 y2
  have hgo := fun b (hb : b ∈ R) (hba : b ≠ a) => gap_insert_other ha y1 y2 hb hba
  obtain ⟨k, hk⟩ := coe_vtx_eq (n := n) y
  have hsplit := (hS.1 a ha).eq_runGlue_of_isRunTriangle hy
  have el : (a : ℤ) + gap (insert (vtx y) R) a = y := by rw [hgl]; ring
  have e2 : ((vtx y : Fin n) : ℤ) + gap (insert (vtx y) R) (vtx y) = a + gap R a + k * n := by
    rw [hgr, hk]; ring
  have hsegA : ∀ d ∈ sectorChords T R a, ordArc d.1 d.2 ∈ T' := fun d hdT =>
    (hT' d ((mem_sectorChords.1 hdT).1.isSectorPair ha) (mem_sectorChords.1 hdT).1.2.2.2.2).2
      (mem_sectorChords.1 hdT).2
  refine ⟨fun b hb => ?_, fun _ b hb hg => ?_, fun δ hδ ho =>
    hS.split_ord ha hy hT' hother (hord δ hδ ho).1 ho (hord δ hδ ho).2⟩
  · rcases Finset.mem_insert.1 hb with rfl | hb
    · rw [sectorChords_insert_up ha y1 y2 hk hT', e2, hk]
      exact isRunTriangulation_image_shiftPair_iff.2 hsplit.2.2.1
    · by_cases hba : b = a
      · subst hba
        rw [sectorChords_insert_low ha y1 y2 hT', el]
        exact hsplit.2.1
      · have hoth : sectorChords T' (insert (vtx y) R) b = sectorChords T R b := by
          ext d
          rw [mem_sectorChords, mem_sectorChords, hgo b hb hba]
          exact and_congr_right fun hd => hother b hb hba d (hd.isSectorPair hb)
        rw [hoth, hgo b hb hba]
        exact hS.1 b hb
  · rcases Finset.mem_insert.1 hb with rfl | hb
    · have houtY : outerArc (insert (vtx y) R) (vtx y) = ordArc y (a + gap R a) := by
        rw [outerArc, e2]
        exact ordArc_congr (vtx_coe _) (vtx_add_mul _ _)
      rw [houtY]
      exact hsegA (y, (a : ℤ) + gap R a) (hy.mem_right (by omega))
    · by_cases hba : b = a
      · subst hba
        rw [outerArc, el]
        exact hsegA ((b : ℤ), y) (hy.mem_left (by omega))
      · have hR2 : 2 ≤ R.card := by
          have := Finset.one_lt_card.2 ⟨a, ha, b, hb, fun h => hba h.symm⟩
          omega
        rw [hgo b hb hba] at hg
        rw [show outerArc (insert (vtx y) R) b = outerArc R b by
          rw [outerArc, outerArc, hgo b hb hba]]
        exact (hother b hb hba _ (isSectorPair_outer hR2 hb hg)).2 (hS.2.1 hR2 b hb hg)

private theorem IsKindP.isDFlipReplacement_outerArc' {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) (hg : 2 ≤ gap R a)
    {y : ℤ} (hy : IsRunTriangle a (a + gap R a) (sectorChords T R a) a y (a + gap R a)) :
    IsDFlipReplacement T (outerArc R a) (.radius τ (vtx y)) ∧
      IsKindP (dFlip T (outerArc R a) (.radius τ (vtx y))) τ (insert (vtx y) R) := by
  have hS := hT.sectorData
  have hyR := notMem_of_lt_gap ha hy.1 hy.2.1
  have hout := isSectorPair_outer hT.1 ha hg
  have hS' : SectorData (dFlip T (outerArc R a) (.radius τ (vtx y))) (insert (vtx y) R) := by
    refine hS.split ha hy (fun d hd hne => mem_dFlip_of_ne (fun e => hne ?_) (hd.ne_radius _ _))
      (fun b hb hba d hd => mem_dFlip_of_ne (fun e => hba ?_) (hd.ne_radius _ _)) ?_
    · rw [outerArc] at e
      exact (hd.eq ha ha hout e).2
    · rw [outerArc] at e
      exact (hd.eq hb ha hout e).1
    · intro δ hδ ho
      rcases mem_dFlip.1 hδ with rfl | ⟨hne, h⟩
      · exact absurd ho id
      · exact ⟨h, hne⟩
  have hrad : ∀ σ x, TaggedArc.radius σ x ∈ dFlip T (outerArc R a) (.radius τ (vtx y)) ↔
      σ = τ ∧ x ∈ insert (vtx y) R := by
    intro σ x
    rw [mem_dFlip, Finset.mem_insert, TaggedArc.radius.injEq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨-, h⟩)
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨((hT.2.1 σ x).1 h).1, Or.inr ((hT.2.1 σ x).1 h).2⟩
    · rintro ⟨rfl, h | h⟩
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr ⟨(outerArc_ne_radius hT.1 ha hg _ _).symm, (hT.2.1 σ x).2 ⟨rfl, h⟩⟩
  have hcard : 2 ≤ (insert (vtx y) R).card := by
    rw [Finset.card_insert_of_notMem hyR]
    have := hT.1
    omega
  have hK := IsKindP.of_sectorData hcard hrad hS'
  exact ⟨⟨hT.isTaggedTriangulation, hT.2.2.2.1 a ha hg,
    fun h => hyR ((hT.2.1 τ _).1 h).2, hK.isTaggedTriangulation⟩, hK⟩

private theorem IsDigonKind.isDFlipReplacement_radius' {T : Finset (TaggedArc n)}
    {a : Fin n} (hT : IsDigonKind T a) (τ : Tag) {y : ℤ}
    (hy : IsRunTriangle a (a + gap {a} a) (sectorChords T {a} a) a y (a + gap {a} a)) :
    IsDFlipReplacement T (.radius τ a) (.radius (-τ) (vtx y)) ∧
      IsKindP (dFlip T (.radius τ a) (.radius (-τ) (vtx y))) (-τ) {a, vtx y} := by
  have ha := Finset.mem_singleton_self a
  have hS := hT.sectorData
  have hyR := notMem_of_lt_gap ha hy.1 hy.2.1
  have hS' : SectorData (dFlip T (.radius τ a) (.radius (-τ) (vtx y))) (insert (vtx y) {a}) := by
    refine hS.split ha hy (fun d hd _ => mem_dFlip_of_ne (hd.ne_radius _ _) (hd.ne_radius _ _))
      (fun b hb hba => absurd (Finset.mem_singleton.1 hb) hba) ?_
    intro δ hδ ho
    rcases mem_dFlip.1 hδ with rfl | ⟨-, h⟩
    · exact absurd ho id
    · exact ⟨h, fun e => outerArc_singleton_not_ordinary a (e ▸ ho)⟩
  have hrad : ∀ σ x, TaggedArc.radius σ x ∈ dFlip T (.radius τ a) (.radius (-τ) (vtx y)) ↔
      σ = -τ ∧ x ∈ (insert (vtx y) {a} : Finset (Fin n)) := by
    intro σ x
    rw [mem_dFlip, Finset.mem_insert, Finset.mem_singleton, TaggedArc.radius.injEq, hT.1, Ne,
      TaggedArc.radius.injEq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, Or.inl h2⟩
      · refine ⟨?_, Or.inr h2⟩
        cases σ <;> cases τ <;> first | rfl | exact absurd ⟨rfl, h2⟩ h1
    · rintro ⟨rfl, h | h⟩
      · exact Or.inl ⟨rfl, h⟩
      · refine Or.inr ⟨fun h' => ?_, h⟩
        cases τ <;> exact absurd h'.1 (by decide)
  have hK := IsKindP.of_sectorData (by rw [Finset.card_insert_of_notMem hyR,
    Finset.card_singleton]) hrad hS'
  rw [Finset.pair_comm]
  exact ⟨⟨hT.isTaggedTriangulation, (hT.1 τ a).2 rfl,
    fun h => hyR (Finset.mem_singleton.2 ((hT.1 _ _).1 h)), hK.isTaggedTriangulation⟩, hK⟩

private theorem mem_runGlue {u w v : ℤ} {T₁ T₂ : Finset (ℤ × ℤ)} {d : ℤ × ℤ} :
    d ∈ runGlue u w v T₁ T₂ ↔
      d ∈ T₁ ∨ d ∈ T₂ ∨ (2 ≤ w - u ∧ d = (u, w)) ∨ (2 ≤ v - w ∧ d = (w, v)) := by
  unfold runGlue
  split_ifs with h1 h2 <;>
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, or_false] <;> tauto

private theorem pred_ne {R : Finset (Fin n)} (hR : 2 ≤ R.card) {a : Fin n} (ha : a ∈ R) :
    pred R a ≠ a := by
  intro h
  have hs := (succ_pred ha).2
  rw [h, succ] at hs
  have hlt := gap_lt_of_two_le_card hR ha
  have g := gap_spec ha
  have := eq_of_vtx_eq (n := n) (u := a) (v := a + gap R a) (by omega) (by omega)
    (by rw [vtx_coe]; exact hs.symm)
  omega

private theorem gap_add_gap_le {R : Finset (Fin n)} {a b : Fin n} (ha : a ∈ R) (hb : b ∈ R)
    (hab : a ≠ b) : gap R a + gap R b ≤ n := by
  calc gap R a + gap R b = ∑ x ∈ {a, b}, gap R x := (Finset.sum_pair hab).symm
    _ ≤ ∑ x ∈ R, gap R x := Finset.sum_le_sum_of_subset
      (Finset.insert_subset_iff.2 ⟨ha, Finset.singleton_subset_iff.2 hb⟩)
    _ = n := sum_gap ⟨a, ha⟩

private theorem eq_pred_of_succ_eq {R : Finset (Fin n)} {a b : Fin n} (ha : a ∈ R) (hb : b ∈ R)
    (h : succ R b = a) : b = pred R a := by
  obtain ⟨hp, hsp⟩ := succ_pred ha
  have gb := gap_spec hb
  have gp := gap_spec hp
  refine (sector_repr_unique hb hp (m := (b : ℤ) + gap R b - 1) (m' := (pred R a : ℤ) +
    gap R (pred R a) - 1) (by omega) (by omega) (by omega) (by omega) ?_).1
  rw [← vtx_sub_coe, ← vtx_sub_coe ((pred R a : ℤ) + _)]
  change vtx (((succ R b : Fin n) : ℤ) - 1) = vtx (((succ R (pred R a) : Fin n) : ℤ) - 1)
  rw [h, hsp]

/-- The shift `k` with `a = a⁻ + g(a⁻) + k n`. -/
private theorem exists_coe_eq_pred_add {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) :
    ∃ k : ℤ, (a : ℤ) = (pred R a : ℤ) + gap R (pred R a) + k * n := by
  have hs := (succ_pred ha).2
  rw [succ] at hs
  exact exists_eq_add_mul_of_vtx_eq (u := (pred R a : ℤ) + gap R (pred R a)) (v := a)
    (by rw [hs, vtx_coe])

private theorem gap_erase_pred {R : Finset (Fin n)} (hR : 2 ≤ R.card) {a : Fin n} (ha : a ∈ R) :
    gap (R.erase a) (pred R a) = gap R (pred R a) + gap R a := by
  obtain ⟨hp, -⟩ := succ_pred ha
  have hpa := pred_ne hR ha
  obtain ⟨k, hk⟩ := exists_coe_eq_pred_add ha
  have ga := gap_spec ha
  have gp := gap_spec hp
  have hlt := gap_lt_of_two_le_card hR ha
  refine gap_eq_of (Finset.mem_erase.2 ⟨hpa, hp⟩) (by omega) ?_ ?_
  · rw [Finset.mem_erase]
    have e : (vtx ((pred R a : ℤ) + ((gap R (pred R a) + gap R a : ℕ) : ℤ)) : Fin n) =
        vtx ((a : ℤ) + gap R a) := by
      rw [← vtx_sub_mul ((a : ℤ) + gap R a) k]
      congr 1
      push_cast
      omega
    rw [e]
    refine ⟨fun h => ?_, ga.2.2.1⟩
    have := eq_of_vtx_eq (n := n) (u := a) (v := a + gap R a) (by omega) (by omega)
      (by rw [vtx_coe]; exact h.symm)
    omega
  · intro m hm1 hm2 hm
    rw [Finset.mem_erase] at hm
    push_cast at hm2
    rcases lt_trichotomy m ((pred R a : ℤ) + gap R (pred R a)) with h | h | h
    · exact notMem_of_lt_gap hp hm1 h hm.2
    · subst h
      exact hm.1 (succ_pred ha).2
    · rw [← vtx_add_mul m k] at hm
      exact notMem_of_lt_gap ha (by omega) (by omega) hm.2

private theorem gap_erase_other {R : Finset (Fin n)} {a b : Fin n} (ha : a ∈ R) (hb : b ∈ R)
    (hba : b ≠ a) (hbp : b ≠ pred R a) : gap (R.erase a) b = gap R b := by
  have g := gap_spec hb
  refine gap_eq_of (Finset.mem_erase.2 ⟨hba, hb⟩) g.1 (Finset.mem_erase.2 ⟨fun h => hbp
    (eq_pred_of_succ_eq ha hb h), g.2.2.1⟩) ?_
  intro m hm1 hm2 hm
  exact notMem_of_lt_gap hb hm1 hm2 (Finset.mem_of_mem_erase hm)

/-- A chord of the merged sector run `[a⁻, a⁻ + g(a⁻) + g(a)]` whose segment lies in `T` does
not cross the radius position `a⁻ + g(a⁻)`. -/
private theorem IsKindP.chord_side {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) {d : ℤ × ℤ}
    (hd : IsRunChord (pred R a) ((pred R a : ℤ) + gap R (pred R a) + gap R a) d)
    (hdT : ordArc d.1 d.2 ∈ T) :
    d.2 ≤ (pred R a : ℤ) + gap R (pred R a) ∨ (pred R a : ℤ) + gap R (pred R a) ≤ d.1 := by
  obtain ⟨hp, -⟩ := succ_pred ha
  have hG := gap_add_gap_le hp ha (pred_ne hT.1 ha)
  have ga := gap_spec ha
  have gp := gap_spec hp
  have hlen := hd.len_le (n := n) (by omega)
  have hd' := isRunChord_iff'.1 hd
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  obtain ⟨_, e⟩ := ordArc_eq_ordinary (n := n) hd'.2.2.2.1 hlen
  have hc' := hT.isTaggedTriangulation.1 _ hdT _ ((hT.2.1 τ a).2 ⟨rfl, ha⟩)
  rw [e] at hc'
  apply hc'
  rw [interiorVertices_eq_image (by omega) (by omega)]
  exact Finset.mem_image.2 ⟨(pred R a : ℤ) + gap R (pred R a),
    mem_intRange.2 ⟨by omega, by omega⟩, (succ_pred ha).2⟩

/-- The ordinary arcs of `T` in the merged sector run `[a⁻, a⁻ + g(a⁻) + g(a)]`. -/
private theorem IsKindP.mem_merge {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) {k : ℤ}
    (hk : (a : ℤ) = (pred R a : ℤ) + gap R (pred R a) + k * n) {d : ℤ × ℤ}
    (hd : IsRunChord (pred R a) ((pred R a : ℤ) + gap R (pred R a) + gap R a) d) :
    ordArc d.1 d.2 ∈ T ↔ d ∈ runGlue (pred R a) ((pred R a : ℤ) + gap R (pred R a))
      ((pred R a : ℤ) + gap R (pred R a) + gap R a) (sectorChords T R (pred R a))
      ((sectorChords T R a).image (shiftPair ((-k) * n))) := by
  obtain ⟨hp, -⟩ := succ_pred ha
  have hG := gap_add_gap_le hp ha (pred_ne hT.1 ha)
  have ga := gap_spec ha
  have gp := gap_spec hp
  have hd' := isRunChord_iff'.1 hd
  rw [mem_runGlue]
  constructor
  · intro hdT
    rcases hT.chord_side ha hd hdT with h | h
    · by_cases hdo : d = ((pred R a : ℤ), (pred R a : ℤ) + gap R (pred R a))
      · subst hdo
        exact Or.inr <| Or.inr <| Or.inl ⟨by dsimp only at hd'; omega, rfl⟩
      · exact Or.inl <| mem_sectorChords.2 ⟨isRunChord_iff'.2 ⟨hd'.1, hd'.2.1, h, hd'.2.2.2.1,
          ne_pair_iff.1 hdo⟩, hdT⟩
    · have hoe : (ordArc d.1 d.2 : TaggedArc n) = ordArc (d.1 + k * n) (d.2 + k * n) :=
        ordArc_congr (vtx_add_mul _ _).symm (vtx_add_mul _ _).symm
      by_cases hdo : d = ((pred R a : ℤ) + gap R (pred R a),
          (pred R a : ℤ) + gap R (pred R a) + gap R a)
      · subst hdo
        exact Or.inr <| Or.inr <| Or.inr ⟨by omega, rfl⟩
      · have := ne_pair_iff.1 hdo
        refine Or.inr <| Or.inl <| Finset.mem_image.2 ⟨(d.1 + k * n, d.2 + k * n),
          mem_sectorChords.2 ⟨isRunChord_iff'.2 ⟨by dsimp only; omega, by dsimp only; omega,
            by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩, hoe ▸ hdT⟩, ?_⟩
        simp only [shiftPair]
        ext <;> dsimp only <;> ring
  · rintro (h | h | ⟨hg, rfl⟩ | ⟨hg, rfl⟩)
    · exact (mem_sectorChords.1 h).2
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      have hoe : (ordArc (shiftPair ((-k) * n) e).1 (shiftPair ((-k) * n) e).2 : TaggedArc n) =
          ordArc e.1 e.2 := ordArc_congr (vtx_add_mul _ _) (vtx_add_mul _ _)
      rw [hoe]
      exact (mem_sectorChords.1 he).2
    · exact hT.2.2.2.1 _ hp (by omega)
    · have := hT.2.2.2.1 a ha (by omega)
      rw [outerArc] at this
      convert this using 1
      apply ordArc_congr
      · rw [← vtx_add_mul _ k, ← hk, vtx_coe]
      · rw [← vtx_add_mul _ k]
        congr 1
        omega

private theorem IsKindP.isRunTriangulation_merge {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) {k : ℤ}
    (hk : (a : ℤ) = (pred R a : ℤ) + gap R (pred R a) + k * n) :
    IsRunTriangulation (pred R a) ((pred R a : ℤ) + gap R (pred R a) + gap R a)
      (runGlue (pred R a) ((pred R a : ℤ) + gap R (pred R a))
      ((pred R a : ℤ) + gap R (pred R a) + gap R a) (sectorChords T R (pred R a))
      ((sectorChords T R a).image (shiftPair ((-k) * n)))) := by
  obtain ⟨hp, -⟩ := succ_pred ha
  have ga := gap_spec ha
  have gp := gap_spec hp
  have h2 := isRunTriangulation_image_shiftPair_iff (t := (-k) * n) |>.2 (hT.2.2.1 a ha)
  rw [show (a : ℤ) + gap R a + (-k) * n = (pred R a : ℤ) + gap R (pred R a) + gap R a by
    rw [hk]; ring, show (a : ℤ) + (-k) * n = (pred R a : ℤ) + gap R (pred R a) by
    rw [hk]; ring] at h2
  exact (isRunTriangulation_runGlue (by omega) (by omega) (hT.2.2.1 _ hp) h2).1

/-- The chords of the merged sector run of `a⁻` after removing the radius at `a`. -/
private theorem IsKindP.sectorChords_merge {T T' : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) {k : ℤ}
    (hk : (a : ℤ) = (pred R a : ℤ) + gap R (pred R a) + k * n)
    (hT'p : ∀ d, IsRunChord (pred R a) (pred R a + gap (R.erase a) (pred R a)) d →
      (ordArc d.1 d.2 ∈ T' ↔ ordArc d.1 d.2 ∈ T)) :
    sectorChords T' (R.erase a) (pred R a) =
      runGlue (pred R a) ((pred R a : ℤ) + gap R (pred R a))
      ((pred R a : ℤ) + gap R (pred R a) + gap R a) (sectorChords T R (pred R a))
      ((sectorChords T R a).image (shiftPair ((-k) * n))) := by
  have ev : (pred R a : ℤ) + gap (R.erase a) (pred R a) =
      (pred R a : ℤ) + gap R (pred R a) + gap R a := by
    rw [gap_erase_pred hT.1 ha]; push_cast; ring
  ext d
  rw [mem_sectorChords]
  constructor
  · rintro ⟨hd, hdT'⟩
    exact (hT.mem_merge ha hk (ev ▸ hd)).1 ((hT'p d hd).1 hdT')
  · intro hd
    have hd2 := (hT.isRunTriangulation_merge ha hk).1 d hd
    have hd1 : IsRunChord (pred R a) (pred R a + gap (R.erase a) (pred R a)) d := ev ▸ hd2
    exact ⟨hd1, (hT'p d hd1).2 ((hT.mem_merge ha hk hd2).2 hd)⟩

/-- After removing the radius at `a`, an ordinary arc of `T` is an outer arc or a segment of a
sector-run chord for `R \ {a}`. -/
private theorem IsKindP.merge_ord {T T' : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R)
    (hT'p : ∀ d, IsRunChord (pred R a) (pred R a + gap (R.erase a) (pred R a)) d →
      (ordArc d.1 d.2 ∈ T' ↔ ordArc d.1 d.2 ∈ T))
    (hT'o : ∀ b ∈ R, b ≠ a → b ≠ pred R a → ∀ d, IsSectorPair R b d →
      (ordArc d.1 d.2 ∈ T' ↔ ordArc d.1 d.2 ∈ T))
    {δ : TaggedArc n} (hδT : δ ∈ T) (ho : δ.IsOrdinary) :
    ∃ b ∈ R.erase a, (2 ≤ (R.erase a).card ∧ 2 ≤ gap (R.erase a) b ∧
      δ = outerArc (R.erase a) b) ∨ ∃ c ∈ sectorChords T' (R.erase a) b, ordArc c.1 c.2 = δ := by
  obtain ⟨hp, -⟩ := succ_pred ha
  have hpR : pred R a ∈ R.erase a := Finset.mem_erase.2 ⟨pred_ne hT.1 ha, hp⟩
  obtain ⟨k, hk⟩ := exists_coe_eq_pred_add ha
  have ga := gap_spec ha
  have gp := gap_spec hp
  have hscp := hT.sectorChords_merge ha hk hT'p
  obtain ⟨b, hb, ⟨hg, e⟩ | ⟨c, hc, e⟩⟩ := hT.2.2.2.2 δ hδT ho
  · by_cases hbp : b = pred R a
    · subst hbp
      refine ⟨pred R a, hpR, Or.inr ⟨((pred R a : ℤ), (pred R a : ℤ) + gap R (pred R a)),
        ?_, e.symm⟩⟩
      rw [hscp]
      exact mem_runGlue.2 (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩)))
    by_cases hba : b = a
    · subst hba
      refine ⟨pred R b, hpR, Or.inr ⟨((pred R b : ℤ) + gap R (pred R b),
        (pred R b : ℤ) + gap R (pred R b) + gap R b), ?_, ?_⟩⟩
      · rw [hscp]
        exact mem_runGlue.2 (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩)))
      · rw [e, outerArc]
        apply ordArc_congr
        · rw [← vtx_add_mul _ k, ← hk, vtx_coe]
        · rw [← vtx_add_mul _ k]
          congr 1
          omega
    have hbR : b ∈ R.erase a := Finset.mem_erase.2 ⟨hba, hb⟩
    have hgo := gap_erase_other ha hb hba hbp
    refine ⟨b, hbR, Or.inl ⟨?_, by rwa [hgo], by rw [e, outerArc, outerArc, hgo]⟩⟩
    have := Finset.one_lt_card.2 ⟨b, hbR, pred R a, hpR, hbp⟩
    omega
  · by_cases hbp : b = pred R a
    · subst hbp
      exact ⟨pred R a, hpR, Or.inr ⟨c, by rw [hscp]; exact mem_runGlue.2 (Or.inl hc), e⟩⟩
    by_cases hba : b = a
    · subst hba
      refine ⟨pred R b, hpR, Or.inr ⟨shiftPair ((-k) * n) c, ?_, ?_⟩⟩
      · rw [hscp]
        exact mem_runGlue.2 (Or.inr (Or.inl (Finset.mem_image_of_mem _ hc)))
      · rw [← e]
        exact ordArc_congr (vtx_add_mul _ _) (vtx_add_mul _ _)
    have hc' := mem_sectorChords.1 hc
    refine ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, Or.inr ⟨c, mem_sectorChords.2 ⟨?_,
      (hT'o b hb hba hbp c (hc'.1.isSectorPair hb)).2 hc'.2⟩, e⟩⟩
    rw [gap_erase_other ha hb hba hbp]
    exact hc'.1

/-- Merging the sectors of `a⁻` and `a` after removing the radius at `a`. -/
private theorem IsKindP.merge {T T' : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R)
    (hT'p : ∀ d, IsRunChord (pred R a) (pred R a + gap (R.erase a) (pred R a)) d →
      (ordArc d.1 d.2 ∈ T' ↔ ordArc d.1 d.2 ∈ T))
    (hT'o : ∀ b ∈ R, b ≠ a → b ≠ pred R a → ∀ d, IsSectorPair R b d →
      (ordArc d.1 d.2 ∈ T' ↔ ordArc d.1 d.2 ∈ T))
    (hout : 2 ≤ (R.erase a).card → outerArc (R.erase a) (pred R a) ∈ T')
    (hord : ∀ δ ∈ T', δ.IsOrdinary →
      δ ∈ T ∨ (2 ≤ (R.erase a).card ∧ δ = outerArc (R.erase a) (pred R a))) :
    SectorData T' (R.erase a) := by
  obtain ⟨hp, -⟩ := succ_pred ha
  have hpR : pred R a ∈ R.erase a := Finset.mem_erase.2 ⟨pred_ne hT.1 ha, hp⟩
  obtain ⟨k, hk⟩ := exists_coe_eq_pred_add ha
  have ga := gap_spec ha
  have gp := gap_spec hp
  have hgo := fun b (hb : b ∈ R.erase a) (hbp : b ≠ pred R a) =>
    gap_erase_other ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb) hbp
  have ev : (pred R a : ℤ) + gap (R.erase a) (pred R a) =
      (pred R a : ℤ) + gap R (pred R a) + gap R a := by
    rw [gap_erase_pred hT.1 ha]; push_cast; ring
  refine ⟨fun b hb => ?_, fun hR2 b hb hg => ?_, fun δ hδ ho => ?_⟩
  · by_cases hbp : b = pred R a
    · subst hbp
      rw [hT.sectorChords_merge ha hk hT'p, ev]
      exact hT.isRunTriangulation_merge ha hk
    · have hsco : sectorChords T' (R.erase a) b = sectorChords T R b := by
        ext d
        rw [mem_sectorChords, mem_sectorChords, hgo b hb hbp]
        exact and_congr_right fun hd => hT'o b (Finset.mem_of_mem_erase hb)
          (Finset.ne_of_mem_erase hb) hbp d (hd.isSectorPair (Finset.mem_of_mem_erase hb))
      rw [hsco, hgo b hb hbp]
      exact hT.2.2.1 b (Finset.mem_of_mem_erase hb)
  · by_cases hbp : b = pred R a
    · subst hbp
      exact hout hR2
    · have hb' := Finset.mem_of_mem_erase hb
      rw [hgo b hb hbp] at hg
      rw [show outerArc (R.erase a) b = outerArc R b by rw [outerArc, outerArc, hgo b hb hbp]]
      exact (hT'o b hb' (Finset.ne_of_mem_erase hb) hbp _
        (isSectorPair_outer hT.1 hb' hg)).2 (hT.2.2.2.1 b hb' hg)
  · rcases hord δ hδ ho with hδT | ⟨hR2, rfl⟩
    · exact hT.merge_ord ha hT'p hT'o hδT ho
    · exact ⟨pred R a, hpR, Or.inl ⟨hR2, by omega, rfl⟩⟩

private theorem ordArc_pred_succ {R : Finset (Fin n)} (hR : 2 ≤ R.card) {a : Fin n}
    (ha : a ∈ R) :
    (ordArc (pred R a : ℤ) (succ R a : ℤ) : TaggedArc n) = outerArc (R.erase a) (pred R a) := by
  obtain ⟨k, hk⟩ := exists_coe_eq_pred_add ha
  have hgp := gap_erase_pred hR ha
  rw [outerArc]
  apply ordArc_congr rfl
  rw [vtx_coe, succ, ← vtx_sub_mul _ k]
  congr 1
  rw [hgp]
  push_cast
  omega

/-- After flipping the radius at `a`, the radii are exactly those of tag `τ` at `R.erase a`. -/
private theorem IsKindP.radius_mem_dFlip_iff {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R)
    (hcard : 2 ≤ (R.erase a).card) (hpR : pred R a ∈ R.erase a)
    (hgp2 : 2 ≤ gap (R.erase a) (pred R a)) (σ : Tag) (x : Fin n) :
    TaggedArc.radius σ x ∈ dFlip T (.radius τ a) (ordArc (pred R a : ℤ) (succ R a : ℤ)) ↔
      σ = τ ∧ x ∈ R.erase a := by
  rw [mem_dFlip, ordArc_pred_succ hT.1 ha, Finset.mem_erase, hT.2.1, Ne,
    TaggedArc.radius.injEq]
  constructor
  · rintro (e | ⟨h1, h2, h3⟩)
    · exact absurd e.symm (outerArc_ne_radius hcard hpR hgp2 _ _)
    · exact ⟨h2, fun h => h1 ⟨h2, h⟩, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact Or.inr ⟨fun h => h2 h.2, h1, h3⟩

private theorem IsKindP.isDFlipReplacement_radius_of_three_le' {T : Finset (TaggedArc n)}
    {τ : Tag} {R : Finset (Fin n)} (hT : IsKindP T τ R) (hR : 3 ≤ R.card) {a : Fin n}
    (ha : a ∈ R) :
    IsDFlipReplacement T (.radius τ a) (ordArc (pred R a : ℤ) (succ R a : ℤ)) ∧
      IsKindP (dFlip T (.radius τ a) (ordArc (pred R a : ℤ) (succ R a : ℤ))) τ (R.erase a) := by
  obtain ⟨hp, -⟩ := succ_pred ha
  have hpR : pred R a ∈ R.erase a := Finset.mem_erase.2 ⟨pred_ne hT.1 ha, hp⟩
  have ga := gap_spec ha
  have gp := gap_spec hp
  have hgp := gap_erase_pred hT.1 ha
  have hcard : 2 ≤ (R.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  have hlt := gap_lt_of_two_le_card hcard hpR
  have hgp2 : 2 ≤ gap (R.erase a) (pred R a) := by omega
  have hout := isSectorPair_outer hcard hpR hgp2
  have hγ' := ordArc_pred_succ hT.1 ha
  have hT'p : ∀ d, IsRunChord (pred R a) (pred R a + gap (R.erase a) (pred R a)) d →
      (ordArc d.1 d.2 ∈ dFlip T (.radius τ a) (ordArc (pred R a : ℤ) (succ R a : ℤ)) ↔
        ordArc d.1 d.2 ∈ T) := fun d hd =>
    mem_dFlip_of_ne ((hd.isSectorPair hpR).ne_radius _ _) fun e => hd.2.2.2.2
      ((hd.isSectorPair hpR).eq hpR hpR hout (by rwa [hγ', outerArc] at e)).2
  have hT'o : ∀ b ∈ R, b ≠ a → b ≠ pred R a → ∀ d, IsSectorPair R b d →
      (ordArc d.1 d.2 ∈ dFlip T (.radius τ a) (ordArc (pred R a : ℤ) (succ R a : ℤ)) ↔
        ordArc d.1 d.2 ∈ T) := by
    intro b hb hba hbp d hd
    have hd' : IsSectorPair (R.erase a) b d :=
      ⟨hd.1, by rw [gap_erase_other ha hb hba hbp]; exact hd.2.1, hd.2.2.1, hd.2.2.2⟩
    exact mem_dFlip_of_ne (hd.ne_radius _ _) fun e => hbp
      (hd'.eq (Finset.mem_erase.2 ⟨hba, hb⟩) hpR hout (by rwa [hγ', outerArc] at e)).1
  have hS' := hT.merge ha hT'p hT'o (fun _ => mem_dFlip.2 (Or.inl hγ'.symm))
    fun δ hδ _ => (mem_dFlip.1 hδ).elim (fun e => Or.inr ⟨hcard, e.trans hγ'⟩) fun h => Or.inl h.2
  have hK := IsKindP.of_sectorData hcard (hT.radius_mem_dFlip_iff ha hcard hpR hgp2) hS'
  refine ⟨⟨hT.isTaggedTriangulation, (hT.2.1 τ a).2 ⟨rfl, ha⟩, fun h => ?_,
    hK.isTaggedTriangulation⟩, hK⟩
  have hc := hT.isTaggedTriangulation.1 _ h _ ((hT.2.1 τ a).2 ⟨rfl, ha⟩)
  rw [hγ', outerArc] at hc
  obtain ⟨_, e⟩ := hout.ordArc_eq
  dsimp only at e
  rw [e] at hc
  apply hc
  rw [interiorVertices_eq_image (by omega) (by omega)]
  refine Finset.mem_image.2 ⟨(pred R a : ℤ) + gap R (pred R a), mem_intRange.2
    ⟨by omega, by rw [hgp]; push_cast; omega⟩, ?_⟩
  exact (succ_pred ha).2

private theorem IsKindP.ne_of_pair {T : Finset (TaggedArc n)} {τ : Tag} {a b : Fin n}
    (hT : IsKindP T τ {a, b}) : a ≠ b := by
  rintro rfl
  simpa using hT.1

private theorem tag_eq_neg_of_ne : ∀ σ τ : Tag, σ ≠ τ → σ = -τ := by decide

private theorem neg_tag_ne : ∀ τ : Tag, -τ ≠ τ := by decide

private theorem IsKindP.isDFlipReplacement_radius_of_pair' {T : Finset (TaggedArc n)}
    {τ : Tag} {a b : Fin n} (hT : IsKindP T τ {a, b}) :
    IsDFlipReplacement T (.radius τ a) (.radius (-τ) b) ∧
      IsDigonKind (dFlip T (.radius τ a) (.radius (-τ) b)) b := by
  have hab := hT.ne_of_pair
  have ha : a ∈ ({a, b} : Finset (Fin n)) := Finset.mem_insert_self _ _
  have hpb : pred {a, b} a = b := by
    obtain ⟨hp, -⟩ := succ_pred ha
    rcases Finset.mem_insert.1 hp with h | h
    · exact absurd h (pred_ne hT.1 ha)
    · exact Finset.mem_singleton.1 h
  have herase : ({a, b} : Finset (Fin n)).erase a = {b} := Finset.erase_insert (by simpa using hab)
  have hiff : ∀ d : ℤ × ℤ, 2 ≤ d.2 - d.1 → d.2 - d.1 ≤ n - 1 →
      (ordArc d.1 d.2 ∈ dFlip T (.radius τ a) (.radius (-τ) b) ↔ ordArc d.1 d.2 ∈ T) := by
    intro d h1 h2
    obtain ⟨_, e⟩ := ordArc_eq_ordinary (n := n) h1 h2
    rw [mem_dFlip, e]
    simp
  have hpR : pred {a, b} a ∈ ({a, b} : Finset (Fin n)).erase a :=
    Finset.mem_erase.2 ⟨pred_ne hT.1 ha, (succ_pred ha).1⟩
  have hS' := hT.merge ha (fun d hd => hiff d (isRunChord_iff'.1 hd).2.2.2.1
      (hd.len_le (n := n) (by have := (gap_spec hpR).2.1; omega)))
    (fun c hc hca hcp => absurd ((Finset.mem_insert.1 hc).resolve_left hca) fun h =>
      hcp ((Finset.mem_singleton.1 h).trans hpb.symm))
    (fun h => by rw [herase] at h; simp at h)
    (fun δ hδ ho => by
      rcases mem_dFlip.1 hδ with rfl | ⟨-, h⟩
      exacts [absurd ho id, Or.inl h])
  rw [herase] at hS'
  have hrad : ∀ σ x, TaggedArc.radius σ x ∈ dFlip T (.radius τ a) (.radius (-τ) b) ↔ x = b := by
    intro σ x
    rw [mem_dFlip, hT.2.1, Ne, TaggedArc.radius.injEq, TaggedArc.radius.injEq,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨-, h⟩ | ⟨h1, h2, h3 | h3⟩)
      exacts [h, absurd ⟨h2, h3⟩ h1, h3]
    · rintro rfl
      by_cases hσ : σ = τ
      · exact Or.inr ⟨fun h => hab h.2.symm, hσ, Or.inr rfl⟩
      · exact Or.inl ⟨tag_eq_neg_of_ne σ τ hσ, rfl⟩
  have hK := IsDigonKind.of_sectorData hrad hS'
  refine ⟨⟨hT.isTaggedTriangulation, (hT.2.1 τ a).2 ⟨rfl, ha⟩, fun h => ?_,
    hK.isTaggedTriangulation⟩, hK⟩
  exact neg_tag_ne τ ((hT.2.1 _ _).1 h).1

private theorem IsDFlipReplacement.compat {T : Finset (TaggedArc n)} {γ δ : TaggedArc n}
    (h : IsDFlipReplacement T γ δ) {ε : TaggedArc n} (hε : ε ∈ T) (hne : ε ≠ γ) :
    δ.Compatible ε :=
  h.2.2.2.1 δ (mem_dFlip.2 (Or.inl rfl)) ε (mem_dFlip.2 (Or.inr ⟨hne, hε⟩))

private theorem IsRunTriangulation.exists_flip {u v : ℤ} {T : Finset (ℤ × ℤ)}
    (hT : IsRunTriangulation u v T) {c : ℤ × ℤ} (hc : c ∈ T) :
    ∃ c', IsRunFlip u v T c c' ∧ ∀ c'', IsRunFlip u v T c c'' → c'' = c' := by
  obtain ⟨x, z⟩ := c
  have hch := isRunChord_iff'.1 (hT.1 _ hc)
  dsimp only at hch
  obtain ⟨y, hy, -⟩ := hT.existsUnique_apex (by omega) (Or.inl hc)
  obtain ⟨⟨t1, t2, t3⟩, ⟨ht, hpar⟩, -⟩ := hT.existsUnique_parent hc
  dsimp only at ht hpar
  rcases hpar with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, hT.isRunFlip_right hc hy ht⟩
  · exact ⟨_, hT.isRunFlip_left hc hy ht⟩

private theorem apex_cover {T : Finset (TaggedArc n)} {R : Finset (Fin n)} {a : Fin n} {y : ℤ}
    (hy : IsRunTriangle a (a + gap R a) (sectorChords T R a) a y (a + gap R a)) {m : ℤ}
    (h1 : (a : ℤ) < m) (h2 : m < a + gap R a) (hmy : m ≠ y) :
    ∃ d ∈ sectorChords T R a, d.1 < m ∧ m < d.2 := by
  rcases lt_or_gt_of_ne hmy with h | h
  · exact ⟨_, hy.mem_left (by omega), h1, h⟩
  · exact ⟨_, hy.mem_right (by omega), h, h2⟩

private theorem IsKindP.radiusSet_eq {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (hT : IsKindP T τ R) : radiusSet T = R := by
  ext x
  rw [mem_radiusSet]
  exact ⟨fun ⟨σ, h⟩ => ((hT.2.1 σ x).1 h).2, fun hx => ⟨τ, (hT.2.1 τ x).2 ⟨rfl, hx⟩⟩⟩

private theorem IsDigonKind.radiusSet_eq {T : Finset (TaggedArc n)} {a : Fin n}
    (hT : IsDigonKind T a) : radiusSet T = {a} := by
  ext x
  rw [mem_radiusSet, Finset.mem_singleton]
  exact ⟨fun ⟨σ, h⟩ => (hT.1 σ x).1 h, fun h => ⟨.plain, (hT.1 _ _).2 h⟩⟩

/-- Uniqueness in case (i), once the replacement is known to be ordinary. -/
private theorem uniq_ordArc_core {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    (hT : IsTaggedTriangulation T) (hRs : radiusSet T = R) {a : Fin n} (ha : a ∈ R)
    {c c' : ℤ × ℤ} (hc : c ∈ sectorChords T R a)
    (huniq : ∀ c'', IsRunFlip a (a + gap R a) (sectorChords T R a) c c'' → c'' = c')
    {δ : TaggedArc n} (hδ : IsDFlipReplacement T (ordArc c.1 c.2) δ) (hδo : δ.IsOrdinary) :
    δ = ordArc c'.1 c'.2 := by
  have hS := hT.sectorData
  rw [hRs] at hS
  have hcp := (mem_sectorChords.1 hc).1.isSectorPair ha
  cases δ with
  | radius σ x => exact absurd hδo id
  | ordinary i j h =>
    have hint : ∀ r ∈ R, r ∉ interiorVertices i j := by
      intro r hr
      obtain ⟨σ, hσ⟩ := mem_radiusSet.1 (hRs ▸ hr)
      exact hδ.compat hσ (fun e => hcp.ne_radius _ _ e.symm)
    rcases (forall_notMem_interiorVertices_iff ⟨a, ha⟩ h).1 hint with
      ⟨b, hb, c'', hc'', e⟩ | ⟨hR2, b, hb, hg, e⟩
    · by_cases hba : b = a
      · subst hba
        have hnot : c'' ∉ sectorChords T R b := fun hm =>
          hδ.2.2.1 (e ▸ (mem_sectorChords.1 hm).2)
        have hRs'' : radiusSet (dFlip T (ordArc c.1 c.2) (.ordinary i j h)) = R := by
          rw [← hRs]
          ext x
          rw [mem_radiusSet, mem_radiusSet]
          exact exists_congr fun σ =>
            mem_dFlip_of_ne (fun e' => hcp.ne_radius _ _ e'.symm) (by simp)
        have hS'' := hδ.2.2.2.sectorData
        rw [hRs''] at hS''
        have hsc := sectorChords_dFlip_self (T := T) hb hc hc''
        rw [e] at hsc
        rw [← e, huniq c'' ⟨hS.1 b hb, hc, hc'', hnot, hsc ▸ hS''.1 b hb⟩]
      · refine absurd ?_ hδ.2.2.1
        rw [← e]
        refine hS.ordArc_mem_of_compat hb hc'' fun d hd => ?_
        have hdT := mem_sectorChords.1 hd
        rw [e]
        exact hδ.compat hdT.2 fun e' => hba ((hdT.1.isSectorPair hb).eq hb ha hcp e').1
    · exact absurd (e ▸ hS.2.1 hR2 b hb hg) hδ.2.2.1

private theorem IsKindP.uniq_ordArc {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) {c c' : ℤ × ℤ}
    (hc : c ∈ sectorChords T R a)
    (huniq : ∀ c'', IsRunFlip a (a + gap R a) (sectorChords T R a) c c'' → c'' = c')
    {δ : TaggedArc n} (hδ : IsDFlipReplacement T (ordArc c.1 c.2) δ) :
    δ = ordArc c'.1 c'.2 := by
  have hcp := (mem_sectorChords.1 hc).1.isSectorPair ha
  refine uniq_ordArc_core hT.isTaggedTriangulation hT.radiusSet_eq ha hc huniq hδ ?_
  cases δ with
  | ordinary => trivial
  | radius σ x =>
    exfalso
    obtain ⟨r, hr, r', hr', hrr'⟩ := Finset.one_lt_card.1 (by have := hT.1; omega : 1 < R.card)
    obtain rfl : σ = τ := tag_eq_of_compat hrr'
      (hδ.compat ((hT.2.1 τ r).2 ⟨rfl, hr⟩) (fun e => hcp.ne_radius _ _ e.symm))
      (hδ.compat ((hT.2.1 τ r').2 ⟨rfl, hr'⟩) (fun e => hcp.ne_radius _ _ e.symm))
    by_cases hx : x ∈ R
    · exact hδ.2.2.1 ((hT.2.1 σ x).2 ⟨rfl, hx⟩)
    · obtain ⟨b, hb, hg, hnc⟩ := hT.not_compat_radius hx σ
      refine hnc (hδ.compat (hT.2.2.2.1 b hb hg) fun e => ?_)
      rw [outerArc] at e
      obtain ⟨rfl, h⟩ := (isSectorPair_outer hT.1 hb hg).eq hb ha hcp e
      exact (mem_sectorChords.1 hc).1.2.2.2.2 h.symm

private theorem IsDigonKind.uniq_ordArc {T : Finset (TaggedArc n)} {a : Fin n}
    (hT : IsDigonKind T a) {c c' : ℤ × ℤ} (hc : c ∈ sectorChords T {a} a)
    (huniq : ∀ c'', IsRunFlip a (a + gap {a} a) (sectorChords T {a} a) c c'' → c'' = c')
    {δ : TaggedArc n} (hδ : IsDFlipReplacement T (ordArc c.1 c.2) δ) :
    δ = ordArc c'.1 c'.2 := by
  have ha := Finset.mem_singleton_self a
  have hcp := (mem_sectorChords.1 hc).1.isSectorPair ha
  refine uniq_ordArc_core hT.isTaggedTriangulation hT.radiusSet_eq ha hc huniq hδ ?_
  cases δ with
  | ordinary => trivial
  | radius σ x =>
    exact hδ.2.2.1 ((hT.1 σ x).2 (eq_of_compat_radius
      (hδ.compat ((hT.1 .plain a).2 rfl) (fun e => hcp.ne_radius _ _ e.symm))
      (hδ.compat ((hT.1 .notched a).2 rfl) (fun e => hcp.ne_radius _ _ e.symm))))

private theorem IsKindP.uniq_outerArc {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) (hg : 2 ≤ gap R a) {y : ℤ}
    (hy : IsRunTriangle a (a + gap R a) (sectorChords T R a) a y (a + gap R a))
    {δ : TaggedArc n} (hδ : IsDFlipReplacement T (outerArc R a) δ) :
    δ = .radius τ (vtx y) := by
  have hS := hT.sectorData
  have hout := isSectorPair_outer hT.1 ha hg
  have hne_seg : ∀ b ∈ R, ∀ d ∈ sectorChords T R b, ordArc d.1 d.2 ≠ outerArc R a := by
    intro b hb d hd e
    rw [outerArc] at e
    obtain ⟨rfl, h⟩ := ((mem_sectorChords.1 hd).1.isSectorPair hb).eq hb ha hout e
    exact (mem_sectorChords.1 hd).1.2.2.2.2 h
  cases δ with
  | ordinary i j h =>
    exfalso
    have hint : ∀ r ∈ R, r ∉ interiorVertices i j := fun r hr =>
      hδ.compat ((hT.2.1 τ r).2 ⟨rfl, hr⟩) (fun e => outerArc_ne_radius hT.1 ha hg _ _ e.symm)
    apply hδ.2.2.1
    rcases (forall_notMem_interiorVertices_iff hT.nonempty h).1 hint with
      ⟨b, hb, c'', hc'', e⟩ | ⟨hR2, b, hb, hg', e⟩
    · rw [← e]
      refine hS.ordArc_mem_of_compat hb hc'' fun d hd => ?_
      rw [e]
      exact hδ.compat (mem_sectorChords.1 hd).2 (hne_seg b hb d hd)
    · rw [← e]
      exact hT.2.2.2.1 b hb hg'
  | radius σ x =>
    obtain ⟨r, hr, r', hr', hrr'⟩ := Finset.one_lt_card.1 (by have := hT.1; omega : 1 < R.card)
    obtain rfl : σ = τ := tag_eq_of_compat hrr'
      (hδ.compat ((hT.2.1 τ r).2 ⟨rfl, hr⟩) (fun e => outerArc_ne_radius hT.1 ha hg _ _ e.symm))
      (hδ.compat ((hT.2.1 τ r').2 ⟨rfl, hr'⟩)
        (fun e => outerArc_ne_radius hT.1 ha hg _ _ e.symm))
    have hx : x ∉ R := fun hx => hδ.2.2.1 ((hT.2.1 σ x).2 ⟨rfl, hx⟩)
    obtain ⟨b, hb, m, h1, h2, rfl⟩ := exists_sector_repr hT.nonempty x
    have hmb := coe_lt_of_vtx_notMem hb h1 hx
    by_cases hba : b = a
    · subst hba
      by_cases hmy : m = y
      · rw [hmy]
      · exfalso
        obtain ⟨d, hd, hd1, hd2⟩ := apex_cover hy hmb h2 hmy
        have hdT := mem_sectorChords.1 hd
        exact (hdT.1.isSectorPair hb).not_compat_radius hd1 hd2 σ
          (hδ.compat hdT.2 (hne_seg b hb d hd))
    · exfalso
      have hg' : 2 ≤ gap R b := by omega
      have := hδ.compat (hT.2.2.2.1 b hb hg') fun e => hba (eq_of_outerArc_eq e)
      rw [outerArc] at this
      exact (isSectorPair_outer hT.1 hb hg').not_compat_radius (m := m) hmb h2 σ this

private theorem IsKindP.uniq_radius_of_three_le {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) (hR : 3 ≤ R.card) {a : Fin n} (ha : a ∈ R)
    {δ : TaggedArc n} (hδ : IsDFlipReplacement T (.radius τ a) δ) :
    δ = ordArc (pred R a : ℤ) (succ R a : ℤ) := by
  have hcard : 2 ≤ (R.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  cases δ with
  | radius σ x =>
    exfalso
    obtain ⟨r, hr, r', hr', hrr'⟩ := Finset.one_lt_card.1 (by omega : 1 < (R.erase a).card)
    obtain rfl : σ = τ := tag_eq_of_compat hrr'
      (hδ.compat ((hT.2.1 τ r).2 ⟨rfl, Finset.mem_of_mem_erase hr⟩)
        (by simpa using Finset.ne_of_mem_erase hr))
      (hδ.compat ((hT.2.1 τ r').2 ⟨rfl, Finset.mem_of_mem_erase hr'⟩)
        (by simpa using Finset.ne_of_mem_erase hr'))
    by_cases hx : x ∈ R
    · exact hδ.2.2.1 ((hT.2.1 σ x).2 ⟨rfl, hx⟩)
    · obtain ⟨b, hb, hg, hnc⟩ := hT.not_compat_radius hx σ
      exact hnc (hδ.compat (hT.2.2.2.1 b hb hg) (outerArc_ne_radius hT.1 hb hg _ _))
  | ordinary i j h =>
    have hRs : radiusSet (dFlip T (.radius τ a) (.ordinary i j h)) = R.erase a := by
      ext x
      rw [mem_radiusSet, Finset.mem_erase]
      constructor
      · rintro ⟨σ, hσ⟩
        rcases mem_dFlip.1 hσ with e | ⟨hne, h'⟩
        · exact absurd e (by simp)
        · obtain ⟨rfl, hx⟩ := (hT.2.1 σ x).1 h'
          exact ⟨fun e => hne (by rw [e]), hx⟩
      · rintro ⟨hxa, hx⟩
        exact ⟨τ, mem_dFlip.2 (Or.inr ⟨by simpa using hxa, (hT.2.1 τ x).2 ⟨rfl, hx⟩⟩)⟩
    have hS'' := hδ.2.2.2.sectorData
    rw [hRs] at hS''
    have hpR : pred R a ∈ R.erase a := Finset.mem_erase.2 ⟨pred_ne hT.1 ha, (succ_pred ha).1⟩
    have hgp := gap_erase_pred hT.1 ha
    have hg1 := (gap_spec (succ_pred ha).1).1
    have hg2 := (gap_spec ha).1
    have hmem := hS''.2.1 hcard _ hpR (by omega)
    rw [← ordArc_pred_succ hT.1 ha] at hmem
    have hnot := (hT.isDFlipReplacement_radius_of_three_le' hR ha).1.2.2.1
    rcases mem_dFlip.1 hmem with e | ⟨-, h'⟩
    · exact e.symm
    · exact absurd h' hnot

/-- In a tagged triangulation, the radii do not all have the same tag and position. -/
private theorem IsTaggedTriangulation.not_forall_radius {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {τ : Tag} {b : Fin n}
    (hrad : ∀ σ x, TaggedArc.radius σ x ∈ T → σ = τ ∧ x = b) : False := by
  rcases isTaggedTriangulation_iff_kind.1 hT with ⟨τ', R', hK⟩ | ⟨c, hK⟩
  · obtain ⟨r, hr, r', hr', hrr'⟩ := Finset.one_lt_card.1 (by have := hK.1; omega : 1 < R'.card)
    exact hrr' ((hrad _ _ ((hK.2.1 τ' r).2 ⟨rfl, hr⟩)).2.trans
      (hrad _ _ ((hK.2.1 τ' r').2 ⟨rfl, hr'⟩)).2.symm)
  · exact absurd ((hrad _ _ ((hK.1 .plain c).2 rfl)).1.trans
      (hrad _ _ ((hK.1 .notched c).2 rfl)).1.symm) (by decide)

private theorem IsKindP.uniq_radius_of_pair {T : Finset (TaggedArc n)} {τ : Tag}
    {a b : Fin n} (hT : IsKindP T τ {a, b}) {δ : TaggedArc n}
    (hδ : IsDFlipReplacement T (.radius τ a) δ) : δ = .radius (-τ) b := by
  have hab := hT.ne_of_pair
  have hbT : TaggedArc.radius τ b ∈ T := (hT.2.1 τ b).2 ⟨rfl, by simp⟩
  cases δ with
  | ordinary i j h =>
    refine (hδ.2.2.2.not_forall_radius (τ := τ) (b := b) fun σ x hσ => ?_).elim
    rcases mem_dFlip.1 hσ with e | ⟨hne, h'⟩
    · exact absurd e (by simp)
    · obtain ⟨rfl, hx⟩ := (hT.2.1 σ x).1 h'
      refine ⟨rfl, ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact absurd rfl hne
      · exact Finset.mem_singleton.1 hx
  | radius σ x =>
    by_cases hσ : σ = τ
    · exfalso
      subst hσ
      by_cases hx : x ∈ ({a, b} : Finset (Fin n))
      · rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hδ.2.2.1 hδ.2.1
        · rw [Finset.mem_singleton] at hx
          subst hx
          exact hδ.2.2.1 hbT
      · obtain ⟨c, hc, hg, hnc⟩ := hT.not_compat_radius hx σ
        exact hnc (hδ.compat (hT.2.2.2.1 c hc hg) (outerArc_ne_radius hT.1 hc hg _ _))
    · have c1 := hδ.compat hbT (by simpa using hab.symm)
      simp only [TaggedArc.Compatible] at c1
      rcases c1 with rfl | c1
      · rw [tag_eq_neg_of_ne σ τ hσ]
      · exact absurd c1 hσ

private theorem IsDigonKind.uniq_radius {T : Finset (TaggedArc n)} {a : Fin n}
    (hT : IsDigonKind T a) (τ : Tag) {y : ℤ}
    (hy : IsRunTriangle a (a + gap {a} a) (sectorChords T {a} a) a y (a + gap {a} a))
    {δ : TaggedArc n} (hδ : IsDFlipReplacement T (.radius τ a) δ) :
    δ = .radius (-τ) (vtx y) := by
  have ha := Finset.mem_singleton_self a
  cases δ with
  | ordinary i j h =>
    refine (hδ.2.2.2.not_forall_radius (τ := -τ) (b := a) fun σ x hσ => ?_).elim
    rcases mem_dFlip.1 hσ with e | ⟨hne, h'⟩
    · exact absurd e (by simp)
    · obtain rfl := (hT.1 σ x).1 h'
      exact ⟨tag_eq_neg_of_ne σ τ fun h => hne (by rw [h]), rfl⟩
  | radius σ x =>
    have hxa : x ≠ a := fun hx => hδ.2.2.1 ((hT.1 σ x).2 hx)
    have c1 := hδ.compat ((hT.1 _ _).2 rfl : TaggedArc.radius (-τ) a ∈ T)
      (by simpa using neg_tag_ne τ)
    simp only [TaggedArc.Compatible] at c1
    obtain rfl := c1.resolve_left hxa
    obtain ⟨b, hb, m, h1, h2, rfl⟩ := exists_sector_repr ⟨a, ha⟩ x
    rw [Finset.mem_singleton] at hb
    subst hb
    have hmb := coe_lt_of_vtx_notMem ha h1 (by simpa using hxa)
    by_cases hmy : m = y
    · rw [hmy]
    · exfalso
      obtain ⟨d, hd, hd1, hd2⟩ := apex_cover hy hmb h2 hmy
      have hdT := mem_sectorChords.1 hd
      have hdp := hdT.1.isSectorPair ha
      exact hdp.not_compat_radius hd1 hd2 _ (hδ.compat hdT.2 (hdp.ne_radius _ _))

/-- **Flips of tagged triangulations**: every arc `γ` of a tagged triangulation `T` has exactly
one replacement `γ'`. -/
@[cluster_algebras "lem_D_flip"]
theorem IsTaggedTriangulation.existsUnique_isDFlipReplacement (hn : 3 ≤ n)
    {T : Finset (TaggedArc n)} (hT : IsTaggedTriangulation T) {γ : TaggedArc n} (hγ : γ ∈ T) :
    ∃! γ', IsDFlipReplacement T γ γ' := by
  rcases isTaggedTriangulation_iff_kind.1 hT with ⟨τ, R, hK⟩ | ⟨a, hK⟩
  · cases γ with
    | radius σ a =>
      obtain ⟨rfl, ha⟩ := (hK.2.1 σ a).1 hγ
      by_cases h3 : 3 ≤ R.card
      · exact ⟨_, (hK.isDFlipReplacement_radius_of_three_le' h3 ha).1,
          fun δ hδ => hK.uniq_radius_of_three_le h3 ha hδ⟩
      · have h2 : R.card = 2 := by have := hK.1; omega
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h2
        obtain ⟨b, hR⟩ : ∃ b, ({x, y} : Finset (Fin n)) = {a, b} := by
          rcases Finset.mem_insert.1 ha with rfl | h
          · exact ⟨y, rfl⟩
          · rw [Finset.mem_singleton] at h
            subst h
            exact ⟨x, Finset.pair_comm _ _⟩
        rw [hR] at hK
        exact ⟨_, hK.isDFlipReplacement_radius_of_pair'.1,
          fun δ hδ => hK.uniq_radius_of_pair hδ⟩
    | ordinary i j h =>
      obtain ⟨a, ha, ⟨hg, e⟩ | ⟨c, hc, e⟩⟩ := hK.2.2.2.2 _ hγ trivial
      · obtain ⟨y, hy, -⟩ := (hK.2.2.1 a ha).existsUnique_apex (by omega) (Or.inr rfl)
        rw [e]
        exact ⟨_, (hK.isDFlipReplacement_outerArc' ha hg hy).1,
          fun δ hδ => hK.uniq_outerArc ha hg hy hδ⟩
      · obtain ⟨c', hc', huniq⟩ := (hK.2.2.1 a ha).exists_flip hc
        rw [← e]
        exact ⟨_, (hK.isDFlipReplacement_ordArc' ha hc').1,
          fun δ hδ => hK.uniq_ordArc ha hc huniq hδ⟩
  · cases γ with
    | radius σ b =>
      obtain rfl := (hK.1 σ b).1 hγ
      have hg : 2 ≤ gap {b} b := by rw [(gap_singleton b).1]; omega
      obtain ⟨y, hy, -⟩ := hK.2.1.existsUnique_apex (by omega) (Or.inr rfl)
      exact ⟨_, (hK.isDFlipReplacement_radius' σ hy).1, fun δ hδ => hK.uniq_radius σ hy hδ⟩
    | ordinary i j h =>
      obtain ⟨c, hc, e⟩ := hK.2.2 _ hγ trivial
      obtain ⟨c', hc', huniq⟩ := hK.2.1.exists_flip hc
      rw [← e]
      exact ⟨_, (hK.isDFlipReplacement_ordArc' hc').1, fun δ hδ => hK.uniq_ordArc hc huniq hδ⟩

/-- **Flips of tagged triangulations**, case (i) in kind `P_τ`: the replacement of the segment
`s(c)` of `c ∈ T_R(a)` is `s(c')` for the replacement `c'` of `c` in the run triangulation
`T_R(a)`; the flip is of the same kind with the same radius set, with
`T'_R(a) = (T_R(a) \ {c}) ∪ {c'}` and the other `T_R(b)` unchanged. -/
@[cluster_algebras "lem_D_flip"]
theorem IsKindP.isDFlipReplacement_ordArc {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) {c c' : ℤ × ℤ}
    (hc : IsRunFlip a (a + gap R a) (sectorChords T R a) c c') :
    IsDFlipReplacement T (ordArc c.1 c.2) (ordArc c'.1 c'.2) ∧
      IsKindP (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) τ R ∧
      sectorChords (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) R a =
        insert c' ((sectorChords T R a).erase c) ∧
      ∀ b ∈ R, b ≠ a →
        sectorChords (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) R b = sectorChords T R b :=
  hT.isDFlipReplacement_ordArc' ha hc

/-- **Flips of tagged triangulations**, case (i) in the digon kind: the replacement of the
segment `s(c)` of `c ∈ T_R(a)` is `s(c')` for the replacement `c'` of `c` in `T_R(a)`; the flip
is of digon kind at `a`, with `T'_R(a) = (T_R(a) \ {c}) ∪ {c'}`. -/
@[cluster_algebras "lem_D_flip"]
theorem IsDigonKind.isDFlipReplacement_ordArc {T : Finset (TaggedArc n)}
    {a : Fin n} (hT : IsDigonKind T a) {c c' : ℤ × ℤ}
    (hc : IsRunFlip a (a + gap {a} a) (sectorChords T {a} a) c c') :
    IsDFlipReplacement T (ordArc c.1 c.2) (ordArc c'.1 c'.2) ∧
      IsDigonKind (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) a ∧
      sectorChords (dFlip T (ordArc c.1 c.2) (ordArc c'.1 c'.2)) {a} a =
        insert c' ((sectorChords T {a} a).erase c) :=
  hT.isDFlipReplacement_ordArc' hc

/-- **Flips of tagged triangulations**, case (ii): in kind `P_τ`, the replacement of the outer arc
`α_R(a)` is `ρ^τ_ȳ`, where `y` is the apex of the outer side of the sector run of `a` in
`T_R(a)`; the flip is of kind `P_τ` with radius set `R ∪ {ȳ}`. -/
@[cluster_algebras "lem_D_flip"]
theorem IsKindP.isDFlipReplacement_outerArc {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) (hg : 2 ≤ gap R a)
    {y : ℤ} (hy : IsRunTriangle a (a + gap R a) (sectorChords T R a) a y (a + gap R a)) :
    IsDFlipReplacement T (outerArc R a) (.radius τ (vtx y)) ∧
      IsKindP (dFlip T (outerArc R a) (.radius τ (vtx y))) τ (insert (vtx y) R) :=
  hT.isDFlipReplacement_outerArc' ha hg hy

/-- **Flips of tagged triangulations**, case (iii): in kind `P_τ` with `|R| ≥ 3`, the replacement
of the radius `ρ^τ_a` is `α(a⁻, a⁺)`; the flip is of kind `P_τ` with radius set `R \ {a}`. -/
@[cluster_algebras "lem_D_flip"]
theorem IsKindP.isDFlipReplacement_radius_of_three_le {T : Finset (TaggedArc n)}
    {τ : Tag} {R : Finset (Fin n)} (hT : IsKindP T τ R) (hR : 3 ≤ R.card) {a : Fin n}
    (ha : a ∈ R) :
    IsDFlipReplacement T (.radius τ a) (ordArc (pred R a : ℤ) (succ R a : ℤ)) ∧
      IsKindP (dFlip T (.radius τ a) (ordArc (pred R a : ℤ) (succ R a : ℤ))) τ (R.erase a) :=
  hT.isDFlipReplacement_radius_of_three_le' hR ha

/-- **Flips of tagged triangulations**, case (iv): in kind `P_τ` with `R = {a, b}`, the
replacement of the radius `ρ^τ_a` is `ρ^{-τ}_b`; the flip is of digon kind with doubled position
`b`. -/
@[cluster_algebras "lem_D_flip"]
theorem IsKindP.isDFlipReplacement_radius_of_pair {T : Finset (TaggedArc n)}
    {τ : Tag} {a b : Fin n} (hT : IsKindP T τ {a, b}) :
    IsDFlipReplacement T (.radius τ a) (.radius (-τ) b) ∧
      IsDigonKind (dFlip T (.radius τ a) (.radius (-τ) b)) b :=
  hT.isDFlipReplacement_radius_of_pair'

/-- **Flips of tagged triangulations**, case (v): in the digon kind at `a`, the replacement of the
radius `ρ^τ_a` is `ρ^{-τ}_ȳ`, where `y` is the apex of `(a, a + n)` in `T_R(a)`; the flip is of
kind `P_{-τ}` with radius set `{a, ȳ}`. -/
@[cluster_algebras "lem_D_flip"]
theorem IsDigonKind.isDFlipReplacement_radius {T : Finset (TaggedArc n)}
    {a : Fin n} (hT : IsDigonKind T a) (τ : Tag) {y : ℤ}
    (hy : IsRunTriangle a (a + gap {a} a) (sectorChords T {a} a) a y (a + gap {a} a)) :
    IsDFlipReplacement T (.radius τ a) (.radius (-τ) (vtx y)) ∧
      IsKindP (dFlip T (.radius τ a) (.radius (-τ) (vtx y))) (-τ) {a, vtx y} :=
  hT.isDFlipReplacement_radius' τ hy

end ClusterAlgebras.TypeD

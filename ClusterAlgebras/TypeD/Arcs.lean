/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Tagged arcs of a once-punctured polygon

A combinatorial model of the tagged arcs of a once-punctured polygon, following the first part of
Section 5.4 of [FWZ]. The vertices of the once-punctured `n`-gon are the elements of `Fin n`, the
puncture enters only through the radii, and curves up to isotopy are replaced by symbols: the
ordinary arcs `α(i, j)` with `2 ≤ d(i, j) ≤ n - 1`, the radii `ρ^τ_i`, the boundary segments
`β_i`, and the loops `L_i`. Integers are used as lifts of vertices to the universal cover of the
boundary: the vertex of `u ∈ ℤ` is its residue `ū` and its *sheet* is `η(u) = ⌊u / n⌋`.

## Main definitions

* `ClusterAlgebras.TypeD.cdist`, `vtx`, `sheet`, `kappa`, `cut`, `interiorVertices`: the
  clockwise distance `d(i, j)`, residue `ū`, sheet `η(u)`, `κ(u, v)`, cut indicator `χ(i, j)` and
  interior vertices.
* `ClusterAlgebras.TypeD.Tag`, `ClusterAlgebras.TypeD.TaggedArc`: tags and tagged arcs.
* `ClusterAlgebras.TypeD.DSeg`, `ClusterAlgebras.TypeD.seg`: the symbols of segments and the
  segment `s(u, v)` of a pair of integers.
* `ClusterAlgebras.TypeD.TaggedArc.Compatible`, `ClusterAlgebras.TypeD.IsTaggedTriangulation`,
  `ClusterAlgebras.TypeD.radiusTriangulation`: compatibility, tagged triangulations and `T∘`.

## Main statements

* `ClusterAlgebras.TypeD.kappa_add`, …: the properties of the sheet function.
* `ClusterAlgebras.TypeD.card_taggedArc`: there are `n²` tagged arcs.

## Implementation notes

* Indices start at `0`: the vertex `i ∈ [1, n]` of [FWZ] is `i - 1 : Fin n` here, and an integer
  `u` is the integer `u - 1` here. Under this shift the residue, the sheet `η(u) = (u - ū) / n`
  (which becomes `⌊u / n⌋` with `ū ∈ [0, n - 1]`), the cut indicator (`χ(i, j) = 1` iff `j < i`)
  and all differences of integers are unchanged; the cut ends on the side `{n - 1, 0}` here.
* The tag `+` (plain) is `Tag.plain` and `-` (notched) is `Tag.notched`.
* `TaggedArc.ordinary i j h` carries the proof `h : 2 ≤ d(i, j)`; the other bound
  `d(i, j) ≤ n - 1` holds for every pair (`cdist_lt`), so it is not a field.
* A symbol `DSeg` is a tagged arc, a boundary segment or a loop. The segment `s(u, v)` is a total
  function `seg u v` of two integers; it is the segment of the model for `u < v ≤ u + n`
  (`seg_eq_boundary`, `seg_eq_arc`, `seg_eq_loop`), and is junk otherwise. Likewise `ordArc u v`
  is the ordinary arc `α(ū, v̄)` when `2 ≤ d(ū, v̄)` and the junk value `ρ^+_ū` otherwise.
* Shadows are meaningful for ordinary arcs and boundary segments only. `DSeg.shadow` is `∅` on
  radii and all of `Fin n` on loops (junk values that no statement reads).

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*
* A tagged triangulation is defined as a pairwise compatible set containing every arc compatible
  with all of its elements. Since every tagged arc is compatible with itself, this is maximality
  among pairwise compatible sets (`isTaggedTriangulation_iff_maximal`); the explicit form is
  decidable, so small cases can be evaluated.
-/

@[expose] public section

namespace ClusterAlgebras.TypeD

variable {n : ℕ}

/-! ### Cyclic notation -/

/-- The **clockwise distance** `d(i, j) ∈ [0, n - 1]`: the residue of `j - i` modulo `n`. -/
@[cluster_algebras "def_D_notation"]
def cdist (i j : Fin n) : ℕ :=
  ((j : ℕ) + n - i) % n

/-- The clockwise distance is below `n`. -/
theorem cdist_lt (i j : Fin n) : cdist i j < n :=
  Nat.mod_lt _ i.pos

/-- The **residue** `ū ∈ Fin n` of an integer `u`: its remainder modulo `n`, in `[0, n - 1]`. -/
@[cluster_algebras "def_D_notation"]
def vtx [NeZero n] (u : ℤ) : Fin n :=
  ⟨(u % n).toNat, by
    have h1 := Int.emod_nonneg u (Int.natCast_ne_zero.2 (NeZero.ne n))
    have h2 := Int.emod_lt_of_pos u (Int.natCast_pos.2 (NeZero.pos n))
    omega⟩

/-- The value of the residue of `u` is `u mod n`. -/
theorem vtx_val [NeZero n] (u : ℤ) : ((vtx u : Fin n) : ℤ) = u % n := by
  have h1 := Int.emod_nonneg u (Int.natCast_ne_zero.2 (NeZero.ne n))
  simp only [vtx]
  omega

/-- Two residues agree exactly when the integers agree modulo `n`. -/
theorem vtx_eq_vtx_iff [NeZero n] {u v : ℤ} : (vtx u : Fin n) = vtx v ↔ u % n = v % n := by
  rw [Fin.ext_iff, ← Nat.cast_inj (R := ℤ), vtx_val, vtx_val]

/-- The residue of an element of `Fin n`, read as an integer, is itself. -/
theorem vtx_coe [NeZero n] (i : Fin n) : (vtx (i : ℤ) : Fin n) = i := by
  apply Fin.ext
  have h := vtx_val (n := n) (i : ℤ)
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.isLt)] at h
  exact_mod_cast h

/-- The residue is `n`-periodic: `u + k n` and `u` have the same residue. -/
theorem vtx_add_mul [NeZero n] (u k : ℤ) : (vtx (u + k * n) : Fin n) = vtx u := by
  rw [vtx_eq_vtx_iff, Int.add_mul_emod_self_right]

/-- `u - k n` and `u` have the same residue. -/
theorem vtx_sub_mul [NeZero n] (u k : ℤ) : (vtx (u - k * n) : Fin n) = vtx u := by
  rw [← vtx_add_mul (u - k * n) k, sub_add_cancel]

/-- `u + n` and `u` have the same residue. -/
theorem vtx_add_n [NeZero n] (u : ℤ) : (vtx (u + n) : Fin n) = vtx u := by
  simpa using vtx_add_mul (n := n) u 1

/-- `u - n` and `u` have the same residue. -/
theorem vtx_sub_n [NeZero n] (u : ℤ) : (vtx (u - n) : Fin n) = vtx u := by
  simpa using vtx_sub_mul (n := n) u 1

/-- The residues of `u + d` and `u` differ for `0 < d < n`. -/
theorem vtx_add_ne_self [NeZero n] {u d : ℤ} (h₁ : 0 < d) (h₂ : d < n) :
    (vtx (u + d) : Fin n) ≠ vtx u := by
  intro h
  rw [vtx_eq_vtx_iff, Int.emod_eq_emod_iff_emod_sub_eq_zero, add_sub_cancel_left] at h
  have := Int.le_of_dvd h₁ (Int.dvd_of_emod_eq_zero h)
  omega

/-- The clockwise distance as an integer residue. -/
private theorem cdist_cast (i j : Fin n) : (cdist i j : ℤ) = ((j : ℤ) + n - i) % n := by
  unfold cdist
  rw [Int.natCast_mod, Nat.cast_sub (by omega)]
  push_cast
  rfl

/-- The residue of `i + d(i, j)` is `j`. -/
theorem vtx_add_cdist [NeZero n] (i j : Fin n) :
    (vtx ((i : ℤ) + (cdist i j : ℤ)) : Fin n) = j := by
  suffices h : (vtx ((i : ℤ) + (cdist i j : ℤ)) : Fin n) = vtx (j : ℤ) by rw [h, vtx_coe]
  rw [vtx_eq_vtx_iff, cdist_cast, Int.add_emod_emod,
    show (i : ℤ) + ((j : ℤ) + n - i) = j + 1 * n by ring, Int.add_mul_emod_self_right]

/-- The **sheet** `η(u) = ⌊u / n⌋` of an integer `u`, equal to `(u - ū) / n`. -/
@[cluster_algebras "def_D_notation"]
def sheet (n : ℕ) (u : ℤ) : ℤ :=
  u / n

/-- The sheet difference `κ(u, v) = η(v) - η(u)` of two integers `u` and `v`. -/
@[cluster_algebras "def_D_notation"]
def kappa (n : ℕ) (u v : ℤ) : ℤ :=
  sheet n v - sheet n u

/-- The **cut indicator** `χ(i, j)`: `1` if `j < i` and `0` otherwise. For `i ≠ j` it
indicates that the run from `i` to `j` passes along the side `{n - 1, 0}`. -/
@[cluster_algebras "def_D_notation"]
def cut (i j : Fin n) : ℤ :=
  if j < i then 1 else 0

/-- The **interior vertices** of the run from `i` to `j`: the vertices `i + t` with
`0 < t < d(i, j)`. -/
@[cluster_algebras "def_D_notation"]
def interiorVertices [NeZero n] (i j : Fin n) : Finset (Fin n) :=
  (Finset.Ioo 0 (cdist i j)).image fun t : ℕ => vtx ((i : ℤ) + (t : ℤ))

/-! ### Properties of the sheet function -/

/-- **Properties of the sheet function**: additivity, `κ(u, w) = κ(u, v) + κ(v, w)` for all
integers `u`, `v`, `w`. -/
@[cluster_algebras "lem_D_kappa"]
theorem kappa_add (u v w : ℤ) : kappa n u w = kappa n u v + kappa n v w := by
  unfold kappa
  ring

/-- The sheet of `u + n` is one more than that of `u`. -/
private theorem sheet_add_n [NeZero n] (u : ℤ) : sheet n (u + n) = sheet n u + 1 := by
  simpa [sheet] using Int.add_mul_ediv_right u 1 (Int.natCast_ne_zero.2 (NeZero.ne n))

/-- **Properties of the sheet function**: shift invariance, `κ(u + n, v + n) = κ(u, v)`. -/
@[cluster_algebras "lem_D_kappa"]
theorem kappa_add_n [NeZero n] (u v : ℤ) : kappa n (u + n) (v + n) = kappa n u v := by
  simp [kappa, sheet_add_n]

/-- **Properties of the sheet function**: `κ(u, v) ∈ {0, 1}` for `u ≤ v ≤ u + n`. -/
@[cluster_algebras "lem_D_kappa"]
theorem kappa_eq_zero_or_one [NeZero n] {u v : ℤ} (huv : u ≤ v) (hvu : v - u ≤ n) :
    kappa n u v = 0 ∨ kappa n u v = 1 := by
  have hn : (0 : ℤ) < n := Int.natCast_pos.2 (NeZero.pos n)
  have h1 : u / n ≤ v / n := Int.ediv_le_ediv hn huv
  have h2 : v / n ≤ (u + n) / n := Int.ediv_le_ediv hn (by omega)
  have h3 := sheet_add_n (n := n) u
  unfold kappa sheet at *
  rw [h3] at h2
  omega

/-- **Properties of the sheet function**: `κ(u, u + n) = 1`. -/
@[cluster_algebras "lem_D_kappa"]
theorem kappa_self_add_n [NeZero n] (u : ℤ) : kappa n u (u + n) = 1 := by
  simp [kappa, sheet_add_n]

/-- **Properties of the sheet function**: for `u < v < u + n`, `d(ū, v̄) = v - u`,
`κ(u, v) = χ(ū, v̄)` and `κ(u, v) + κ(v, u + n) = 1`. -/
@[cluster_algebras "lem_D_kappa"]
theorem cdist_vtx_kappa_eq_cut [NeZero n] {u v : ℤ} (huv : u < v) (hvu : v < u + n) :
    (cdist (vtx u : Fin n) (vtx v) : ℤ) = v - u ∧ kappa n u v = cut (vtx u : Fin n) (vtx v) ∧
      kappa n u v + kappa n v (u + n) = 1 := by
  have hn : (0 : ℤ) < n := Int.natCast_pos.2 (NeZero.pos n)
  have hk := kappa_eq_zero_or_one (n := n) huv.le (by omega)
  have hsu := sheet_add_n (n := n) u
  have eu := Int.emod_add_mul_ediv u n
  have ev := Int.emod_add_mul_ediv v n
  have hu0 := Int.emod_nonneg u hn.ne'
  have hu1 := Int.emod_lt_of_pos u hn
  have hv0 := Int.emod_nonneg v hn.ne'
  have hv1 := Int.emod_lt_of_pos v hn
  have hlt : (vtx v : Fin n) < vtx u ↔ v % n < u % n := by
    rw [Fin.lt_def, ← vtx_val v, ← vtx_val u]
    exact Nat.cast_lt.symm
  rw [cdist_cast, vtx_val, vtx_val]
  simp only [cut, hlt]
  unfold kappa sheet at *
  rcases hk with hk | hk
  · have hq : v / n = u / n := by linarith
    rw [hq] at ev
    refine ⟨?_, ?_, by linarith⟩
    · rw [show v % n + n - u % n = (v - u) + n * 1 by linarith, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by linarith) (by linarith)]
    · rw [if_neg (by linarith)]
      linarith
  · have hq : v / n = u / n + 1 := by linarith
    rw [hq, mul_add, mul_one] at ev
    refine ⟨?_, ?_, by linarith⟩
    · rw [show v % n + n - u % n = v - u by linarith,
        Int.emod_eq_of_lt (by linarith) (by linarith)]
    · rw [if_pos (by linarith)]
      linarith

/-- **Properties of the sheet function**: `χ(i, j) + χ(j, i) = 1` for `i ≠ j`. -/
@[cluster_algebras "lem_D_kappa"]
theorem cut_add_cut {i j : Fin n} (hij : i ≠ j) : cut i j + cut j i = 1 := by
  have := Fin.val_ne_of_ne hij
  simp only [cut, Fin.lt_def]
  split_ifs <;> omega

/-! ### Tagged arcs -/

/-- A **tag**: plain (`+`) or notched (`-`). -/
@[cluster_algebras "def_D_tagged_arcs"]
inductive Tag where
  /-- The plain tag `+`. -/
  | plain
  /-- The notched tag `-`. -/
  | notched
  deriving DecidableEq, Fintype, Repr

/-- The other tag `-τ`. -/
@[cluster_algebras "def_D_tagged_arcs"]
def Tag.neg : Tag → Tag
  | plain => notched
  | notched => plain

/-- Negation on tags swaps `+` and `-` (`Tag.neg`). -/
instance Tag.instNeg : Neg Tag :=
  ⟨Tag.neg⟩

/-- `-(+) = -`. -/
@[simp]
theorem Tag.neg_plain : -Tag.plain = Tag.notched :=
  rfl

/-- `-(-) = +`. -/
@[simp]
theorem Tag.neg_notched : -Tag.notched = Tag.plain :=
  rfl

/-- A **tagged arc** of the once-punctured `n`-gon: an *ordinary arc* `α(i, j)` with
`2 ≤ d(i, j)` (and `d(i, j) ≤ n - 1`, which always holds), or a *radius* `ρ^τ_i` with tag `τ`
and *position* `i`. -/
@[cluster_algebras "def_D_tagged_arcs"]
inductive TaggedArc (n : ℕ) where
  /-- The ordinary arc `α(i, j)`. -/
  | ordinary (i j : Fin n) (h : 2 ≤ cdist i j)
  /-- The radius `ρ^τ_i`. -/
  | radius (τ : Tag) (i : Fin n)
  deriving DecidableEq, Fintype

namespace TaggedArc

/-- A tagged arc is **ordinary** when it is not a radius. -/
def IsOrdinary : TaggedArc n → Prop
  | ordinary .. => True
  | radius .. => False

/-- Being ordinary is decidable. -/
instance instDecidablePredIsOrdinary : DecidablePred (IsOrdinary (n := n)) := fun γ => by
  cases γ <;> unfold IsOrdinary <;> infer_instance

/-- The ordinary arc `α(i, j)` is ordinary. -/
@[simp]
theorem isOrdinary_ordinary (i j : Fin n) (h : 2 ≤ cdist i j) : (ordinary i j h).IsOrdinary :=
  trivial

/-- A radius `ρ^τ_i` is not ordinary. -/
@[simp]
theorem not_isOrdinary_radius (τ : Tag) (i : Fin n) : ¬(radius τ i).IsOrdinary :=
  id

end TaggedArc

/-- The **shadow** `S(α(i, j)) = {β_{i + t} : 0 ≤ t < d(i, j)}` of an ordinary arc, as the set of
indices of its boundary segments. -/
@[cluster_algebras "def_D_tagged_arcs"]
def shadow [NeZero n] (i j : Fin n) : Finset (Fin n) :=
  (Finset.range (cdist i j)).image fun t : ℕ => vtx ((i : ℤ) + (t : ℤ))

/-- The symbols of **segments**: a tagged arc, a boundary segment `β_i`, or the loop `L_i`. -/
@[cluster_algebras "def_D_tagged_arcs"]
inductive DSeg (n : ℕ) where
  /-- A tagged arc. -/
  | arc (γ : TaggedArc n)
  /-- The boundary segment `β_i`. -/
  | boundary (i : Fin n)
  /-- The loop `L_i`. -/
  | loop (i : Fin n)
  deriving DecidableEq

/-- The shadow of a symbol: `S(α(i, j))` for an ordinary arc and `{β_i}` for `β_i`; the junk
values `∅` on radii and `Fin n` on loops are never used. -/
@[cluster_algebras "def_D_tagged_arcs"]
def DSeg.shadow [NeZero n] : DSeg n → Finset (Fin n)
  | arc (.ordinary i j _) => TypeD.shadow i j
  | arc (.radius ..) => ∅
  | boundary i => {i}
  | loop _ => Finset.univ

section

variable [NeZero n]

/-- The ordinary arc `α(ū, v̄)` of two integers, when `2 ≤ d(ū, v̄)`; the junk value `ρ^+_ū`
otherwise. -/
@[cluster_algebras "def_D_tagged_arcs"]
def ordArc (u v : ℤ) : TaggedArc n :=
  if h : 2 ≤ cdist (vtx u : Fin n) (vtx v) then .ordinary (vtx u) (vtx v) h
  else .radius .plain (vtx u)

/-- The **segment** `s(u, v)` of integers `u < v ≤ u + n`: `β_ū` if `v = u + 1`, the loop `L_ū`
if `v = u + n`, and the ordinary arc `α(ū, v̄)` otherwise. Total, with junk values outside
`u < v ≤ u + n`. -/
@[cluster_algebras "def_D_tagged_arcs"]
def seg (u v : ℤ) : DSeg n :=
  if v - u = 1 then .boundary (vtx u)
  else if v - u = n then .loop (vtx u)
  else .arc (ordArc u v)

/-- `s(u, u + 1) = β_ū`. -/
@[cluster_algebras "def_D_tagged_arcs"]
theorem seg_eq_boundary (u : ℤ) : (seg u (u + 1) : DSeg n) = .boundary (vtx u) := by
  simp [seg]

/-- `s(u, u + n) = L_ū` for `n ≥ 2`. -/
@[cluster_algebras "def_D_tagged_arcs"]
theorem seg_eq_loop (hn : 2 ≤ n) (u : ℤ) : (seg u (u + n) : DSeg n) = .loop (vtx u) := by
  unfold seg
  rw [if_neg (by omega), if_pos (by ring)]

/-- For `2 ≤ v - u ≤ n - 1`, `s(u, v)` is the ordinary arc `α(ū, v̄)`, which is one: the
segment is well defined. -/
@[cluster_algebras "def_D_tagged_arcs"]
theorem seg_eq_arc {u v : ℤ} (h₁ : 2 ≤ v - u) (h₂ : v - u ≤ n - 1) :
    (seg u v : DSeg n) = .arc (ordArc u v) ∧
      ∃ h, (ordArc u v : TaggedArc n) = .ordinary (vtx u) (vtx v) h := by
  have hc := (cdist_vtx_kappa_eq_cut (n := n) (by omega : u < v) (by omega : v < u + n)).1
  have h2 : 2 ≤ cdist (vtx u : Fin n) (vtx v) := by omega
  refine ⟨?_, h2, by simp [ordArc, h2]⟩
  unfold seg
  rw [if_neg (by omega), if_neg (by omega)]

/-- Segments are invariant under translation by `n`: `s(u + n, v + n) = s(u, v)`. -/
@[cluster_algebras "def_D_tagged_arcs"]
theorem seg_add_n (u v : ℤ) : (seg (u + n) (v + n) : DSeg n) = seg u v := by
  simp only [seg, ordArc, vtx_add_n, add_sub_add_right_eq_sub]

/-! ### Compatibility and tagged triangulations -/

namespace TaggedArc

/-- Two tagged arcs are **compatible** when (a) both are ordinary and their shadows are nested
or disjoint, (b) one is an ordinary arc `α(i, j)` and the other a radius whose position is not an
interior vertex of the run from `i` to `j`, or (c) both are radii with the same position or the
same tag. -/
@[cluster_algebras "def_D_compatible"]
def Compatible : TaggedArc n → TaggedArc n → Prop
  | ordinary i j _, ordinary k l _ =>
      shadow i j ⊆ shadow k l ∨ shadow k l ⊆ shadow i j ∨ Disjoint (shadow i j) (shadow k l)
  | ordinary i j _, radius _ a => a ∉ interiorVertices i j
  | radius _ a, ordinary i j _ => a ∉ interiorVertices i j
  | radius τ a, radius σ b => a = b ∨ τ = σ

/-- Compatibility is decidable. -/
instance instDecidableRelCompatible : DecidableRel (Compatible (n := n)) := fun γ δ => by
  cases γ <;> cases δ <;> unfold Compatible <;> infer_instance

/-- Every tagged arc is compatible with itself. -/
@[simp, cluster_algebras "def_D_compatible"]
theorem compatible_refl (γ : TaggedArc n) : γ.Compatible γ := by
  cases γ <;> simp [Compatible]

end TaggedArc

/-- A **tagged triangulation**: a set `T` of pairwise compatible tagged arcs that contains every
tagged arc compatible with all of its elements, that is, a maximal pairwise compatible set
(`isTaggedTriangulation_iff_maximal`). -/
@[cluster_algebras "def_D_compatible"]
def IsTaggedTriangulation (T : Finset (TaggedArc n)) : Prop :=
  (∀ γ ∈ T, ∀ δ ∈ T, γ.Compatible δ) ∧ ∀ γ, (∀ δ ∈ T, γ.Compatible δ) → γ ∈ T

/-- Being a tagged triangulation is decidable. -/
instance instDecidablePredIsTaggedTriangulation :
    DecidablePred (IsTaggedTriangulation (n := n)) := fun T => by
  unfold IsTaggedTriangulation
  infer_instance

/-- Compatibility of tagged arcs is symmetric. -/
theorem TaggedArc.Compatible.symm {γ δ : TaggedArc n} (h : γ.Compatible δ) :
    δ.Compatible γ := by
  cases γ <;> cases δ <;> simp only [TaggedArc.Compatible] at h ⊢ <;> tauto

/-- A tagged triangulation is exactly a set of pairwise compatible tagged arcs which is maximal
for inclusion among such sets. -/
@[cluster_algebras "def_D_compatible"]
theorem isTaggedTriangulation_iff_maximal (T : Finset (TaggedArc n)) :
    IsTaggedTriangulation T ↔
      Maximal (fun S : Set (TaggedArc n) => S.Pairwise TaggedArc.Compatible) (T : Set _) := by
  have : Std.Refl (TaggedArc.Compatible (n := n)) := ⟨TaggedArc.compatible_refl⟩
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a ha b hb _ => h1 a ha b hb, fun S hS hTS x hx =>
      h2 x fun δ hδ => Set.pairwise_iff_of_refl.1 hS hx (hTS hδ)⟩
  · rintro ⟨hP, hmax⟩
    refine ⟨fun γ hγ δ hδ => Set.pairwise_iff_of_refl.1 hP hγ hδ, fun γ hγ => hmax ?_
      (Set.subset_insert _ _) (Set.mem_insert _ _)⟩
    exact hP.insert fun δ hδ _ => ⟨hγ δ hδ, (hγ δ hδ).symm⟩

/-- The **radius triangulation** `T∘ = {ρ^+_1, …, ρ^+_n}`. -/
@[cluster_algebras "def_D_compatible"]
def radiusTriangulation (n : ℕ) : Finset (TaggedArc n) :=
  Finset.univ.image (TaggedArc.radius .plain)

end

/-! ### Counting tagged arcs -/

/-- The clockwise distance without residues. -/
private theorem cdist_eq_ite (i j : Fin n) :
    cdist i j = if (i : ℕ) ≤ j then (j : ℕ) - i else (j : ℕ) + n - i := by
  unfold cdist
  have := i.isLt
  have := j.isLt
  split_ifs with h
  · rw [show (j : ℕ) + n - i = (j - i) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- For a fixed `i`, exactly `n - 2` vertices `j` have `d(i, j) ≥ 2`. -/
private theorem card_filter_two_le_cdist (i : Fin n) :
    (Finset.univ.filter fun j : Fin n => 2 ≤ cdist i j).card = n - 2 := by
  rw [← Nat.card_Ico 2 n]
  have hi := i.isLt
  refine Finset.card_bij (fun j _ => cdist i j) (fun j hj => ?_) (fun j₁ _ j₂ _ h => ?_)
    (fun t ht => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_Ico.2 ⟨hj, cdist_lt i j⟩
  · have := j₁.isLt
    have := j₂.isLt
    simp only [cdist_eq_ite] at h
    apply Fin.ext
    split_ifs at h <;> omega
  · rw [Finset.mem_Ico] at ht
    refine ⟨⟨if (i : ℕ) + t < n then i + t else i + t - n, by split_ifs <;> omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, cdist_eq_ite]
      split_ifs <;> omega
    · simp only [cdist_eq_ite]
      split_ifs <;> omega

/-- Ordinary arcs are the pairs `(i, j)` with `d(i, j) ≥ 2`. -/
private def ordinaryEquiv :
    {γ : TaggedArc n // γ.IsOrdinary} ≃ Σ i : Fin n, {j : Fin n // 2 ≤ cdist i j} where
  toFun γ := match γ with
    | ⟨.ordinary i j h, _⟩ => ⟨i, j, h⟩
    | ⟨.radius _ _, h⟩ => False.elim h
  invFun p := ⟨.ordinary p.1 p.2.1 p.2.2, trivial⟩
  left_inv := by
    rintro ⟨⟨⟩ | ⟨⟩, h⟩
    · rfl
    · exact False.elim h
  right_inv := by
    rintro ⟨i, j, h⟩
    rfl

/-- Radii are the pairs of a tag and a position. -/
private def radiusEquiv : {γ : TaggedArc n // ¬γ.IsOrdinary} ≃ Tag × Fin n where
  toFun γ := match γ with
    | ⟨.ordinary .., h⟩ => False.elim (h trivial)
    | ⟨.radius τ i, _⟩ => (τ, i)
  invFun p := ⟨.radius p.1 p.2, id⟩
  left_inv := by
    rintro ⟨⟨⟩ | ⟨⟩, h⟩
    · exact False.elim (h trivial)
    · rfl
  right_inv := by
    rintro ⟨τ, i⟩
    rfl

/-- **Counting tagged arcs by kind**: there are `n (n - 2)` ordinary arcs and `2 n` radii. -/
@[cluster_algebras "lem_D_arc_count"]
theorem card_ordinary_and_radius :
    (Finset.univ.filter fun γ : TaggedArc n => γ.IsOrdinary).card = n * (n - 2) ∧
      (Finset.univ.filter fun γ : TaggedArc n => ¬γ.IsOrdinary).card = 2 * n := by
  constructor
  · rw [← Fintype.card_subtype, Fintype.card_congr ordinaryEquiv, Fintype.card_sigma]
    simp only [Fintype.card_subtype, card_filter_two_le_cdist, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  · rw [← Fintype.card_subtype, Fintype.card_congr radiusEquiv, Fintype.card_prod,
      Fintype.card_fin]
    rfl

/-- **There are `n²` tagged arcs.** -/
@[cluster_algebras "lem_D_arc_count"]
theorem card_taggedArc (hn : 3 ≤ n) : Fintype.card (TaggedArc n) = n ^ 2 := by
  obtain ⟨h1, h2⟩ := card_ordinary_and_radius (n := n)
  rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not
    (fun γ : TaggedArc n => γ.IsOrdinary), h1, h2]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

end ClusterAlgebras.TypeD

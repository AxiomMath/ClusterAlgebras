/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeD.Triangulation
public import Mathlib.Data.Matrix.Basic

/-!
# The extended exchange matrix of a tagged triangulation

The explicit extended exchange matrix `B̃•(T)` of a tagged triangulation `T` of the punctured
`n`-gon. Its rows are indexed by the arcs of `T`, the boundary segments `β_1, …, β_n` and two
symbols `λ`, `λ̄`, and its columns by the arcs of `T`. The mutable and boundary rows are the
quiver of the ideal triangulation underlying `T` (clockwise `3`-cycles in its triangles, the two
radii of a punctured digon behaving as one arc); the rows `λ`, `λ̄` are given as sums of
contributions of the triangles.

## Main definitions

* `ClusterAlgebras.TypeD.DRow`: the row symbols; `DSeg.rows` is the set `E(s)` of rows of a
  segment `s`.
* `ClusterAlgebras.TypeD.arrowMatrix`, `lamMatrix`, `cycMatrix`: `Ar_{s,s'}`, `U_{μ,s}` and
  `Cyc(s₁, s₂, s₃)`.
* `ClusterAlgebras.TypeD.outerTriangles`, `punctureTriangles`: the triangles of `T`.
* `ClusterAlgebras.TypeD.dMatrix`: the matrix `B̃•(T)`.
* `ClusterAlgebras.TypeD.IsLabelling`, `extLabel`, `labelledMatrix`: labellings, the extended
  labelling `ℓ̂` and the `(2n + 2) × n` matrix `B̃•(T, ℓ)`.

## Main results

* `ClusterAlgebras.TypeD.dMatrix_arc_arc`: the principal part is skew-symmetric.
* `ClusterAlgebras.TypeD.dMatrix_col_ordArc_right`, `dMatrix_col_ordArc_left`,
  `dMatrix_col_outerArc`, `dMatrix_col_radius_of_isKindP`, `dMatrix_col_radius_of_isDigonKind`:
  the columns of `B̃•(T)`.

## Implementation notes

* `dMatrix T` is a matrix indexed by all row symbols and all tagged arcs; its entries outside
  the index set `ℛ(T) × T = (T ⊔ {β_i} ⊔ {λ, λ̄}) × T` are zero, since every symbol of a
  triangle of `T` is an arc of `T`, a boundary segment or the loop of the doubled radius.
* `λ_+ = λ` is `DRow.lam .plain` and `λ_- = λ̄` is `DRow.lam .notched`.
* Puncture triangles exist when `T` is of kind `P_τ`. The definition detects the kind from the
  radii (`IsPunctureKind`: at least two positions and no radius of tag `-τ`) and the digon kind
  from a position carrying both radii; on tagged triangulations these are the kinds of
  `isTaggedTriangulation_iff_kind`. The radius set and the sector runs are those of
  `radiusSet T`.
* A labelling, a bijection `[1, n] → T`, is an injective map `ℓ : Fin n → TaggedArc n` with
  range `T` (`IsLabelling`). With indices from `0`, the extended labelling sends `n + i` to
  `β_i`, `2n` to `λ` and `2n + 1` to `λ̄`.
-/

@[expose] public section

namespace ClusterAlgebras.TypeD

variable {n : ℕ} [NeZero n]

/-! ### Row symbols and the elementary matrices -/

/-- The symbols indexing the rows of `B̃•(T)`: tagged arcs, boundary segments `β_i`, and `λ_τ`
(`λ_+ = λ`, `λ_- = λ̄`). -/
@[cluster_algebras "def_D_matrix"]
inductive DRow (n : ℕ) where
  /-- The row of a tagged arc. -/
  | arc (γ : TaggedArc n)
  /-- The row of the boundary segment `β_i`. -/
  | boundary (i : Fin n)
  /-- The row `λ_τ`. -/
  | lam (τ : Tag)
  deriving DecidableEq, Fintype

/-- The set `E(s)` of rows of a segment `s`: `{s}` for a tagged arc or a boundary segment, and
`{ρ^+_a, ρ^-_a}` for the loop `L_a`. -/
@[cluster_algebras "def_D_matrix"]
def DSeg.rows : DSeg n → Finset (DRow n)
  | arc γ => {.arc γ}
  | boundary i => {.boundary i}
  | loop a => {.arc (.radius .plain a), .arc (.radius .notched a)}

/-- `Ar_{s,s'}(δ, ε) = [δ ∈ E(s)][ε ∈ E(s')] - [ε ∈ E(s)][δ ∈ E(s')]`: an arrow `s → s'`. -/
@[cluster_algebras "def_D_matrix"]
def arrowMatrix (s s' : DSeg n) : Matrix (DRow n) (TaggedArc n) ℤ :=
  Matrix.of fun δ ε =>
    (if δ ∈ s.rows ∧ DRow.arc ε ∈ s'.rows then 1 else 0) -
      (if DRow.arc ε ∈ s.rows ∧ δ ∈ s'.rows then 1 else 0)

/-- `U_{λ_τ,s}(δ, ε) = [δ = λ_τ][ε ∈ E(s)]`. -/
@[cluster_algebras "def_D_matrix"]
def lamMatrix (τ : Tag) (s : DSeg n) : Matrix (DRow n) (TaggedArc n) ℤ :=
  Matrix.of fun δ ε => if δ = .lam τ ∧ DRow.arc ε ∈ s.rows then 1 else 0

/-- `Cyc(s₁, s₂, s₃) = Ar_{s₁,s₂} + Ar_{s₂,s₃} + Ar_{s₃,s₁}`: the oriented `3`-cycle
`s₁ → s₂ → s₃ → s₁`. -/
@[cluster_algebras "def_D_matrix"]
def cycMatrix (s₁ s₂ s₃ : DSeg n) : Matrix (DRow n) (TaggedArc n) ℤ :=
  arrowMatrix s₁ s₂ + arrowMatrix s₂ s₃ + arrowMatrix s₃ s₁

/-! ### Triangles -/

/-- The **outer triangles** of `T`: the pairs `(a, (x, y, z))` with `a` in the radius set `R` of
`T` and `(x, y, z)` a triangle of `T_R(a)` in the sector run `[a, a + g_R(a)]`. Their *sides* are
the segments `s(x, y)`, `s(y, z)`, `s(x, z)`; the last is the loop `L_a` exactly when `T` is of
digon kind and `(x, z) = (a, a + n)`. -/
@[cluster_algebras "def_D_triangles"]
def outerTriangles (T : Finset (TaggedArc n)) : Finset (Fin n × ℤ × ℤ × ℤ) :=
  (radiusSet T).biUnion fun a =>
    (runTriangles a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a)).image
      fun t => (a, t)

/-- `T` has the radii of kind `P_τ`: at least two positions and no radius of tag `-τ`. On tagged
triangulations this is being of kind `P_τ`. -/
@[cluster_algebras "def_D_triangles"]
def IsPunctureKind (T : Finset (TaggedArc n)) (τ : Tag) : Prop :=
  2 ≤ (radiusSet T).card ∧ ∀ i, TaggedArc.radius (-τ) i ∉ T

/-- Having the radii of kind `P_τ` is decidable. -/
instance instDecidableIsPunctureKind (T : Finset (TaggedArc n)) (τ : Tag) :
    Decidable (IsPunctureKind T τ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The **puncture triangles** of `T` of kind `P_τ`: the pairs `(a, a⁺)`, `a ∈ R`, recorded as
`(τ, a)`; the *outer side* of `(a, a⁺)` is `s(a, a + g_R(a))`, the outer arc `α_R(a)` or `β_a`
when `g_R(a) = 1`. -/
@[cluster_algebras "def_D_triangles"]
def punctureTriangles (T : Finset (TaggedArc n)) : Finset (Tag × Fin n) :=
  (Finset.univ ×ˢ radiusSet T).filter fun p => IsPunctureKind T p.1

/-! ### The matrix `B̃•(T)` -/

/-- The contribution of the outer triangle `(a, (x, y, z))`, with `k = κ(y, z)`:
`Cyc(s(x,y), s(y,z), s(x,z)) + k (U_{λ,s(y,z)} + U_{λ̄,s(y,z)} - U_{λ,s(x,z)} - U_{λ̄,s(x,z)})`. -/
@[cluster_algebras "def_D_matrix"]
def outerContribution (p : Fin n × ℤ × ℤ × ℤ) : Matrix (DRow n) (TaggedArc n) ℤ :=
  cycMatrix (seg p.2.1 p.2.2.1) (seg p.2.2.1 p.2.2.2) (seg p.2.1 p.2.2.2) +
    kappa n p.2.2.1 p.2.2.2 •
      (lamMatrix .plain (seg p.2.2.1 p.2.2.2) + lamMatrix .notched (seg p.2.2.1 p.2.2.2) -
        lamMatrix .plain (seg p.2.1 p.2.2.2) - lamMatrix .notched (seg p.2.1 p.2.2.2))

/-- The contribution of the puncture triangle `(a, a⁺)` of kind `P_τ`, with outer side `s` and
`k = χ(a, a⁺)`: `Cyc(s, ρ^τ_{a⁺}, ρ^τ_a) + k (U_{λ_τ,s} - U_{λ_τ,ρ^τ_{a⁺}} + U_{λ_{-τ},ρ^τ_a})`. -/
@[cluster_algebras "def_D_matrix"]
def punctureContribution (T : Finset (TaggedArc n)) (τ : Tag) (a : Fin n) :
    Matrix (DRow n) (TaggedArc n) ℤ :=
  cycMatrix (seg (a : ℤ) (a + gap (radiusSet T) a)) (.arc (.radius τ (succ (radiusSet T) a)))
      (.arc (.radius τ a)) +
    cut a (succ (radiusSet T) a) •
      (lamMatrix τ (seg (a : ℤ) (a + gap (radiusSet T) a)) -
        lamMatrix τ (.arc (.radius τ (succ (radiusSet T) a))) +
        lamMatrix (-τ) (.arc (.radius τ a)))

/-- The contribution `U_{λ̄,ρ^+_a} + U_{λ,ρ^-_a}` of a position `a` carrying both radii (the
doubled position of the digon kind), and `0` otherwise. -/
@[cluster_algebras "def_D_matrix"]
def digonContribution (T : Finset (TaggedArc n)) (a : Fin n) : Matrix (DRow n) (TaggedArc n) ℤ :=
  if TaggedArc.radius .plain a ∈ T ∧ TaggedArc.radius .notched a ∈ T then
    lamMatrix .notched (.arc (.radius .plain a)) + lamMatrix .plain (.arc (.radius .notched a))
  else 0

/-- The **matrix `B̃•(T)`** of a tagged triangulation `T`: the sum of the contributions of its
outer triangles, of its puncture triangles (kind `P_τ`), and of its doubled position (digon
kind). Rows are indexed by `DRow n`, columns by tagged arcs; the entries outside
`ℛ(T) × T` vanish. -/
@[cluster_algebras "def_D_matrix"]
def dMatrix (T : Finset (TaggedArc n)) : Matrix (DRow n) (TaggedArc n) ℤ :=
  (∑ p ∈ outerTriangles T, outerContribution p) +
    (∑ p ∈ punctureTriangles T, punctureContribution T p.1 p.2) +
    ∑ a, digonContribution T a

omit [NeZero n] in
/-- `Ar_{s,s'}` is skew-symmetric on arc rows and arc columns. -/
private theorem arrowMatrix_arc_arc (s s' : DSeg n) (δ ε : TaggedArc n) :
    arrowMatrix s s' (.arc δ) ε = -arrowMatrix s s' (.arc ε) δ := by
  simp only [arrowMatrix, Matrix.of_apply]
  ring

omit [NeZero n] in
/-- `U_{λ_τ,s}` vanishes on arc rows. -/
private theorem lamMatrix_arc (τ : Tag) (s : DSeg n) (δ ε : TaggedArc n) :
    lamMatrix τ s (.arc δ) ε = 0 := by
  simp [lamMatrix]

/-- The contribution of an outer triangle is skew-symmetric on arcs. -/
private theorem outerContribution_arc_arc (p : Fin n × ℤ × ℤ × ℤ) (δ ε : TaggedArc n) :
    outerContribution p (.arc δ) ε = -outerContribution p (.arc ε) δ := by
  simp only [outerContribution, cycMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    lamMatrix_arc, arrowMatrix_arc_arc _ _ δ ε, sub_zero, add_zero, smul_zero]
  ring

/-- The contribution of a puncture triangle is skew-symmetric on arcs. -/
private theorem punctureContribution_arc_arc (T : Finset (TaggedArc n)) (τ : Tag) (a : Fin n)
    (δ ε : TaggedArc n) :
    punctureContribution T τ a (.arc δ) ε = -punctureContribution T τ a (.arc ε) δ := by
  simp only [punctureContribution, cycMatrix, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, lamMatrix_arc, arrowMatrix_arc_arc _ _ δ ε, sub_zero, add_zero, smul_zero]
  ring

omit [NeZero n] in
/-- The contribution of a doubled position vanishes on arc rows. -/
private theorem digonContribution_arc (T : Finset (TaggedArc n)) (a : Fin n) (δ ε : TaggedArc n) :
    digonContribution T a (.arc δ) ε = 0 := by
  unfold digonContribution
  split_ifs <;> simp [lamMatrix_arc]

/-- **The principal part of `B̃•(T)` is skew-symmetric**: `b_{δε} = -b_{εδ}` for tagged arcs
`δ, ε`, for every finite set `T` of tagged arcs. -/
@[cluster_algebras "lem_D_matrix_skew"]
theorem dMatrix_arc_arc (T : Finset (TaggedArc n)) (δ ε : TaggedArc n) :
    dMatrix T (.arc δ) ε = -dMatrix T (.arc ε) δ := by
  simp only [dMatrix, Matrix.add_apply, Matrix.sum_apply, outerContribution_arc_arc _ δ ε,
    punctureContribution_arc_arc _ _ _ δ ε, digonContribution_arc, Finset.sum_neg_distrib,
    Finset.sum_const_zero, add_zero]
  ring

/-! ### The columns of `B̃•(T)` -/

/-- The column `e_s` of a symbol: `e_δ` for a tagged arc or a boundary segment, and
`e_{L_a} = e_{ρ^+_a} + e_{ρ^-_a}` for a loop. -/
@[cluster_algebras "lem_D_columns"]
def segVec (s : DSeg n) : DRow n → ℤ :=
  fun δ => if δ ∈ s.rows then 1 else 0

/-- The unit column `e_δ`. -/
@[cluster_algebras "lem_D_columns"]
def rowVec (δ₀ : DRow n) : DRow n → ℤ :=
  fun δ => if δ = δ₀ then 1 else 0

/-! ### Computing the columns -/

omit [NeZero n] in
/-- The column of a tagged arc is its unit column. -/
private theorem segVec_arc (γ : TaggedArc n) : segVec (DSeg.arc γ) = rowVec (.arc γ) := by
  funext δ
  simp [segVec, rowVec, DSeg.rows]

omit [NeZero n] in
/-- The column `ε` of `Ar_{s,s'}` is `[ε ∈ E(s')] e_s - [ε ∈ E(s)] e_{s'}`. -/
private theorem arrowMatrix_apply (s s' : DSeg n) (δ : DRow n) (γ : TaggedArc n) :
    arrowMatrix s s' δ γ = segVec s δ * segVec s' (.arc γ) - segVec s (.arc γ) * segVec s' δ := by
  simp only [arrowMatrix, Matrix.of_apply, segVec]
  by_cases h1 : δ ∈ s.rows <;> by_cases h2 : DRow.arc γ ∈ s'.rows <;>
    by_cases h3 : DRow.arc γ ∈ s.rows <;> by_cases h4 : δ ∈ s'.rows <;> simp [h1, h2, h3, h4]

omit [NeZero n] in
/-- The column `ε` of `U_{λ_τ,s}` is `[ε ∈ E(s)] e_{λ_τ}`. -/
private theorem lamMatrix_apply (τ : Tag) (s : DSeg n) (δ : DRow n) (γ : TaggedArc n) :
    lamMatrix τ s δ γ = rowVec (.lam τ) δ * segVec s (.arc γ) := by
  simp only [lamMatrix, Matrix.of_apply, segVec, rowVec]
  by_cases h1 : δ = .lam τ <;> by_cases h2 : DRow.arc γ ∈ s.rows <;> simp [h1, h2]

/-- The column `γ` of the contribution of the outer triangle `(x, y, z)`: `e_{s(x,z)} - e_{s(y,z)}`
from the first short side, `e_{s(x,y)} - e_{s(x,z)} + κ(y,z)(e_λ + e_λ̄)` from the second and
`e_{s(y,z)} - e_{s(x,y)} - κ(y,z)(e_λ + e_λ̄)` from the base, each weighted by `[γ ∈ E(side)]`. -/
private theorem outerContribution_apply (p : Fin n × ℤ × ℤ × ℤ) (δ : DRow n) (γ : TaggedArc n) :
    outerContribution p δ γ =
      segVec (seg p.2.1 p.2.2.1) (.arc γ) *
          (segVec (seg p.2.1 p.2.2.2) δ - segVec (seg p.2.2.1 p.2.2.2) δ) +
        segVec (seg p.2.2.1 p.2.2.2) (.arc γ) *
          (segVec (seg p.2.1 p.2.2.1) δ - segVec (seg p.2.1 p.2.2.2) δ +
            kappa n p.2.2.1 p.2.2.2 * (rowVec (.lam .plain) δ + rowVec (.lam .notched) δ)) +
        segVec (seg p.2.1 p.2.2.2) (.arc γ) *
          (segVec (seg p.2.2.1 p.2.2.2) δ - segVec (seg p.2.1 p.2.2.1) δ -
            kappa n p.2.2.1 p.2.2.2 * (rowVec (.lam .plain) δ + rowVec (.lam .notched) δ)) := by
  simp only [outerContribution, cycMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, arrowMatrix_apply, lamMatrix_apply]
  ring

/-- The column `γ` of the contribution of the puncture triangle `(b, b⁺)`. -/
private theorem punctureContribution_apply (T : Finset (TaggedArc n)) (τ : Tag) (b : Fin n)
    (δ : DRow n) (γ : TaggedArc n) :
    punctureContribution T τ b δ γ =
      segVec (seg (b : ℤ) (b + gap (radiusSet T) b)) (.arc γ) *
          (rowVec (.arc (.radius τ b)) δ - rowVec (.arc (.radius τ (succ (radiusSet T) b))) δ +
            cut b (succ (radiusSet T) b) * rowVec (.lam τ) δ) +
        segVec (.arc (.radius τ (succ (radiusSet T) b))) (.arc γ) *
          (segVec (seg (b : ℤ) (b + gap (radiusSet T) b)) δ - rowVec (.arc (.radius τ b)) δ -
            cut b (succ (radiusSet T) b) * rowVec (.lam τ) δ) +
        segVec (.arc (.radius τ b)) (.arc γ) *
          (rowVec (.arc (.radius τ (succ (radiusSet T) b))) δ -
            segVec (seg (b : ℤ) (b + gap (radiusSet T) b)) δ +
            cut b (succ (radiusSet T) b) * rowVec (.lam (-τ)) δ) := by
  simp only [punctureContribution, cycMatrix, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, arrowMatrix_apply, lamMatrix_apply, segVec_arc]
  ring

/-- An entry of `B̃•(T)` is the sum of the entries of the contributions. -/
private theorem dMatrix_apply (T : Finset (TaggedArc n)) (δ : DRow n) (γ : TaggedArc n) :
    dMatrix T δ γ = ∑ p ∈ outerTriangles T, outerContribution p δ γ +
      ∑ p ∈ punctureTriangles T, punctureContribution T p.1 p.2 δ γ +
      ∑ b, digonContribution T b δ γ := by
  simp only [dMatrix, Matrix.add_apply, Matrix.sum_apply]

omit [NeZero n] in
/-- The entry of the column of a tagged arc `ρ` in the row of a tagged arc `γ`. -/
private theorem segVec_arc_arc (ρ γ : TaggedArc n) :
    segVec (DSeg.arc ρ) (.arc γ) = if γ = ρ then 1 else 0 := by
  simp [segVec, DSeg.rows]

/-- Residues are compatible with translation. -/
private theorem vtx_add_congr {u u' : ℤ} (h : (vtx u : Fin n) = vtx u') (d : ℤ) :
    (vtx (u + d) : Fin n) = vtx (u' + d) := by
  have h3 : u % n = u' % n := by rw [← vtx_val (n := n), ← vtx_val (n := n), h]
  have : ((vtx (u + d) : Fin n) : ℤ) = ((vtx (u' + d) : Fin n) : ℤ) := by
    rw [vtx_val, vtx_val, Int.add_emod, h3, ← Int.add_emod]
  exact Fin.ext (mod_cast this)

/-- The segment `s(u, v)` depends only on `ū` and `v - u`. -/
private theorem seg_congr {u u' v v' : ℤ} (h : (vtx u : Fin n) = vtx u') (hd : v - u = v' - u') :
    (seg u v : DSeg n) = seg u' v' := by
  have hv : (vtx v : Fin n) = vtx v' := by
    have := vtx_add_congr h (v - u)
    rwa [show u + (v - u) = v by ring, hd, show u' + (v' - u') = v' by ring] at this
  simp only [seg, ordArc, h, hv, hd]

/-- Membership in the outer triangles. -/
private theorem mem_outerTriangles {T : Finset (TaggedArc n)} {p : Fin n × ℤ × ℤ × ℤ} :
    p ∈ outerTriangles T ↔ p.1 ∈ radiusSet T ∧
      IsRunTriangle p.1 (p.1 + gap (radiusSet T) p.1) (sectorChords T (radiusSet T) p.1)
        p.2.1 p.2.2.1 p.2.2.2 := by
  obtain ⟨b, x, y, z⟩ := p
  simp only [outerTriangles, Finset.mem_biUnion, Finset.mem_image, runTriangles,
    Finset.mem_filter, Finset.mem_product, mem_intRange, Prod.mk.injEq]
  constructor
  · rintro ⟨b', hb', t, ⟨_, ht⟩, rfl, rfl⟩
    exact ⟨hb', ht⟩
  · rintro ⟨hb, ht⟩
    refine ⟨b, hb, (x, y, z), ⟨?_, ht⟩, rfl, rfl⟩
    dsimp only
    obtain ⟨hxy, hyz, -, -, hxz⟩ := ht
    have : (b : ℤ) ≤ x ∧ z ≤ b + gap (radiusSet T) b := by
      rcases hxz with h | h | h
      · obtain ⟨⟨h1, -, h3, -⟩, -⟩ := mem_sectorChords.1 h
        exact ⟨h1, h3⟩
      · exact ⟨h.1, h.2.2⟩
      · simp only [Prod.mk.injEq] at h
        omega
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩

omit [NeZero n] in
/-- Membership in the puncture triangles. -/
private theorem mem_punctureTriangles {T : Finset (TaggedArc n)} {p : Tag × Fin n} :
    p ∈ punctureTriangles T ↔ p.2 ∈ radiusSet T ∧ IsPunctureKind T p.1 := by
  simp [punctureTriangles]

/-- An ordinary arc of a pair at distance in `[2, n - 1]` is not a radius. -/
private theorem ordArc_ne_radius {u v : ℤ} (h₁ : 2 ≤ v - u) (h₂ : v - u ≤ n - 1) (σ : Tag)
    (b : Fin n) :
    (ordArc u v : TaggedArc n) ≠ .radius σ b := by
  obtain ⟨-, _, he⟩ := seg_eq_arc (n := n) h₁ h₂
  rw [he]
  rintro ⟨⟩

/-- The rows of a segment of a sector run: the segment of a chord, the outer arc, or the loop. -/
private theorem rows_seg_of_isRunSegment (hn : 2 ≤ n) {T : Finset (TaggedArc n)}
    {R : Finset (Fin n)}
    {b : Fin n} (hb : b ∈ R) {p q : ℤ}
    (hs : IsRunSegment b (b + gap R b) (sectorChords T R b) (p, q)) {γ : TaggedArc n}
    (hγ : DRow.arc γ ∈ (seg p q : DSeg n).rows) :
    ((p, q) ∈ sectorChords T R b ∧ 2 ≤ q - p ∧ q - p ≤ n - 1 ∧ γ = ordArc p q) ∨
      ((p, q) = ((b : ℤ), (b : ℤ) + (gap R b : ℤ)) ∧ 2 ≤ gap R b ∧ gap R b ≤ n - 1 ∧
        γ = outerArc R b) ∨
      ((p, q) = ((b : ℤ), (b : ℤ) + (gap R b : ℤ)) ∧ gap R b = n ∧ ∃ σ, γ = .radius σ b) := by
  obtain ⟨hg1, hgn, -, -⟩ := gap_spec hb
  rcases hs with hc | ⟨-, hq, -⟩ | h
  · obtain ⟨⟨h1, -, h3, h4, h5⟩, -⟩ := mem_sectorChords.1 hc
    have h6 : q - p ≤ (n : ℤ) - 1 := by
      by_contra hcon
      exact h5 (Prod.ext (by simp only; omega) (by simp only; omega))
    rw [(seg_eq_arc (n := n) h4 h6).1] at hγ
    simp only [DSeg.rows, Finset.mem_singleton, DRow.arc.injEq] at hγ
    exact Or.inl ⟨hc, h4, h6, hγ⟩
  · simp only at hq
    subst hq
    rw [seg_eq_boundary] at hγ
    simp [DSeg.rows] at hγ
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    right
    by_cases h1 : gap R b = 1
    · rw [h1, Nat.cast_one, seg_eq_boundary] at hγ
      simp [DSeg.rows] at hγ
    by_cases h2 : gap R b = n
    · rw [h2, seg_eq_loop hn, vtx_coe] at hγ
      simp only [DSeg.rows, Finset.mem_insert, Finset.mem_singleton, DRow.arc.injEq] at hγ
      exact Or.inr ⟨rfl, h2, hγ.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)⟩
    · have h3 : (2 : ℤ) ≤ (b + gap R b : ℤ) - b := by omega
      have h4 : (b + gap R b : ℤ) - b ≤ n - 1 := by omega
      rw [(seg_eq_arc (n := n) h3 h4).1] at hγ
      simp only [DSeg.rows, Finset.mem_singleton, DRow.arc.injEq] at hγ
      exact Or.inl ⟨rfl, by omega, by omega, hγ⟩

/-- A chord of a sector run has length in `[2, n - 1]`. -/
private theorem isRunChord_length_bounds {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) {c : ℤ × ℤ}
    (hc : IsRunChord a (a + gap R a) c) : 2 ≤ c.2 - c.1 ∧ c.2 - c.1 ≤ n - 1 := by
  obtain ⟨x, z⟩ := c
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  simp only at h1 h2 h3 h4 h5 ⊢
  obtain ⟨-, hgn, -, -⟩ := gap_spec ha
  refine ⟨h4, ?_⟩
  by_contra hcon
  exact h5 (Prod.ext (by simp only; omega) (by simp only; omega))

/-- The segment of a chord of a sector run is not an outer arc. -/
private theorem ordArc_ne_outerArc {R : Finset (Fin n)} {a b : Fin n} (ha : a ∈ R) (hb : b ∈ R)
    {c : ℤ × ℤ} (hc : IsRunChord a (a + gap R a) c) (hg : 2 ≤ gap R b) (hg' : gap R b ≤ n - 1) :
    (ordArc c.1 c.2 : TaggedArc n) ≠ outerArc R b := by
  obtain ⟨h4, h6⟩ := isRunChord_length_bounds ha hc
  obtain ⟨x, z⟩ := c
  obtain ⟨h1, h2, h3, -, h5⟩ := hc
  simp only at h1 h2 h3 h4 h5 h6
  obtain ⟨-, hh1, e1⟩ := seg_eq_arc (n := n) h4 h6
  obtain ⟨-, hh2, e2⟩ := seg_eq_arc (n := n) (u := b) (v := b + gap R b) (by omega) (by omega)
  intro h
  simp only at h
  rw [e1, outerArc, e2] at h
  simp only [TaggedArc.ordinary.injEq] at h
  obtain ⟨hx, hz⟩ := h
  rw [vtx_coe] at hx
  have hxR : (vtx x : Fin n) ∈ R := hx ▸ hb
  have hzR : (vtx z : Fin n) ∈ R := hz ▸ (gap_spec hb).2.2.1
  have := (vtx_mem_iff_of_mem_sectorRun ha h1 (by omega)).1 hxR
  have := (vtx_mem_iff_of_mem_sectorRun ha (by omega) h3).1 hzR
  exact h5 (Prod.ext (by simp only; omega) (by simp only; omega))

/-- The only segment of a sector run whose rows contain `s(c)`, for a chord `c` of the sector
run of `a`, is `c` itself. -/
private theorem eq_of_ordArc_mem_rows (hn : 2 ≤ n) {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    {a b : Fin n} (ha : a ∈ R) (hb : b ∈ R) {x z : ℤ} (hxz : (x, z) ∈ sectorChords T R a)
    {p q : ℤ} (hs : IsRunSegment b (b + gap R b) (sectorChords T R b) (p, q))
    (hγ : DRow.arc (ordArc x z) ∈ (seg p q : DSeg n).rows) : b = a ∧ (p, q) = (x, z) := by
  have hc := (mem_sectorChords.1 hxz).1
  obtain ⟨h4, h6⟩ := isRunChord_length_bounds ha hc
  rcases rows_seg_of_isRunSegment hn hb hs hγ with ⟨hpq, -, -, h⟩ | ⟨-, hg, hg', h⟩ |
      ⟨-, -, σ, h⟩
  · exact eq_of_ordArc_eq hb ha (mem_sectorChords.1 hpq).1 hc h.symm
  · exact absurd h (ordArc_ne_outerArc ha hb hc hg hg')
  · exact absurd h (ordArc_ne_radius h4 h6 σ b)

/-- The only segment of a sector run whose rows contain the outer arc `α_R(a)` is the outer side of
the sector run of `a`. -/
private theorem eq_of_outerArc_mem_rows (hn : 2 ≤ n) {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    {a b : Fin n} (ha : a ∈ R) (hb : b ∈ R) (hg : 2 ≤ gap R a)
    (hg' : gap R a ≤ n - 1) {p q : ℤ}
    (hs : IsRunSegment b (b + gap R b) (sectorChords T R b) (p, q))
    (hγ : DRow.arc (outerArc R a) ∈ (seg p q : DSeg n).rows) :
    b = a ∧ (p, q) = ((b : ℤ), (b : ℤ) + (gap R b : ℤ)) := by
  rcases rows_seg_of_isRunSegment hn hb hs hγ with ⟨hpq, -, -, h⟩ | ⟨hpq, -, -, h⟩ |
      ⟨-, -, σ, h⟩
  · exact absurd h.symm (ordArc_ne_outerArc hb ha (mem_sectorChords.1 hpq).1 hg hg')
  · exact ⟨eq_of_outerArc_eq h.symm, hpq⟩
  · exact absurd h (ordArc_ne_radius (by omega) (by omega) σ b)

/-- The only segment of a sector run whose rows contain a radius `ρ^τ_a` is the loop `L_a`, the
outer side of a sector run of length `n`. -/
private theorem eq_of_radius_mem_rows (hn : 2 ≤ n) {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    {b : Fin n} (hb : b ∈ R) {p q : ℤ}
    (hs : IsRunSegment b (b + gap R b) (sectorChords T R b) (p, q)) {τ : Tag} {a : Fin n}
    (hγ : DRow.arc (.radius τ a) ∈ (seg p q : DSeg n).rows) :
    b = a ∧ gap R b = n ∧ (p, q) = ((b : ℤ), (b : ℤ) + (gap R b : ℤ)) := by
  rcases rows_seg_of_isRunSegment hn hb hs hγ with ⟨-, h4, h6, h⟩ | ⟨-, hgb, hgb', h⟩ |
      ⟨hpq, hgn, σ, h⟩
  · exact absurd h.symm (ordArc_ne_radius h4 h6 τ a)
  · exact absurd h.symm (ordArc_ne_radius (by omega) (by omega) τ a)
  · simp only [TaggedArc.radius.injEq] at h
    exact ⟨h.2.symm, hgn, hpq⟩

/-- The radius set of a tagged triangulation of kind `P_τ` with radius set `R` is `R`. -/
private theorem radiusSet_eq_of_isKindP {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (hT : IsKindP T τ R) : radiusSet T = R := by
  ext b
  simp only [radiusSet, Finset.mem_filter, Finset.mem_univ, true_and, hT.2.1]
  cases τ <;> simp

/-- The radius set of a tagged triangulation of digon kind at `a` is `{a}`. -/
private theorem radiusSet_eq_of_isDigonKind {T : Finset (TaggedArc n)} {a : Fin n}
    (hT : IsDigonKind T a) : radiusSet T = {a} := by
  ext b
  simp [radiusSet, hT.1]

/-- For `|R| ≥ 2` every gap is at most `n - 1`. -/
private theorem gap_le_sub_one {R : Finset (Fin n)} (hR : 2 ≤ R.card) {b : Fin n} (hb : b ∈ R) :
    gap R b ≤ n - 1 := by
  obtain ⟨c, hc, hcb⟩ := Finset.exists_mem_ne hR b
  have hsum := sum_gap ⟨b, hb⟩
  have hsub : ({b, c} : Finset (Fin n)) ⊆ R :=
    Finset.insert_subset_iff.2 ⟨hb, Finset.singleton_subset_iff.2 hc⟩
  have hle := Finset.sum_le_sum_of_subset (f := gap R) hsub
  rw [Finset.sum_pair hcb.symm, hsum] at hle
  have := (gap_spec hc).1
  omega

/-- A tagged triangulation of kind `P_τ` has the radii of kind `P_σ` exactly for `σ = τ`. -/
private theorem isPunctureKind_iff_of_isKindP {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) (σ : Tag) : IsPunctureKind T σ ↔ σ = τ := by
  rw [IsPunctureKind, radiusSet_eq_of_isKindP hT]
  constructor
  · rintro ⟨hR, h⟩
    obtain ⟨b, hb⟩ := Finset.card_pos.1 (by omega : 0 < R.card)
    have := h b
    rw [hT.2.1] at this
    cases σ <;> cases τ <;> simp_all [Neg.neg, Tag.neg]
  · rintro rfl
    refine ⟨hT.1, fun i h => ?_⟩
    rw [hT.2.1] at h
    cases σ <;> simp [Neg.neg, Tag.neg] at h

/-- In kind `P_τ` no position carries both radii. -/
private theorem not_both_radii_of_isKindP {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (hT : IsKindP T τ R) (b : Fin n) :
    ¬(TaggedArc.radius .plain b ∈ T ∧ TaggedArc.radius .notched b ∈ T) := by
  rw [hT.2.1, hT.2.1]
  cases τ <;> simp

/-- The chords `T_R(a)` of a tagged triangulation triangulate the sector run of `a`. -/
private theorem isRunTriangulation_of_isTaggedTriangulation {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {a : Fin n} (ha : a ∈ radiusSet T) :
    IsRunTriangulation a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a) := by
  rcases isTaggedTriangulation_iff_kind.1 hT with ⟨τ, R, hK⟩ | ⟨b, hD⟩
  · rw [radiusSet_eq_of_isKindP hK] at ha ⊢
    exact hK.2.2.1 a ha
  · rw [radiusSet_eq_of_isDigonKind hD] at ha ⊢
    obtain rfl := Finset.mem_singleton.1 ha
    exact hD.2.1

omit [NeZero n] in
/-- `[γ ∈ E(s)] = 0` for `γ ∉ E(s)`. -/
private theorem segVec_eq_zero {s : DSeg n} {γ : TaggedArc n} (h : DRow.arc γ ∉ s.rows) :
    segVec s (.arc γ) = 0 := by
  simp [segVec, h]

omit [NeZero n] in
/-- `[γ ∈ E(s)] = 1` for `γ ∈ E(s)`. -/
private theorem segVec_eq_one {s : DSeg n} {γ : TaggedArc n} (h : DRow.arc γ ∈ s.rows) :
    segVec s (.arc γ) = 1 := by
  simp [segVec, h]

/-- An outer triangle none of whose sides has `γ` among its rows contributes nothing to
column `γ`. -/
private theorem outerContribution_eq_zero {p : Fin n × ℤ × ℤ × ℤ} {γ : TaggedArc n}
    (h₁ : DRow.arc γ ∉ (seg p.2.1 p.2.2.1 : DSeg n).rows)
    (h₂ : DRow.arc γ ∉ (seg p.2.2.1 p.2.2.2 : DSeg n).rows)
    (h₃ : DRow.arc γ ∉ (seg p.2.1 p.2.2.2 : DSeg n).rows) (δ : DRow n) :
    outerContribution p δ γ = 0 := by
  rw [outerContribution_apply, segVec_eq_zero h₁, segVec_eq_zero h₂, segVec_eq_zero h₃]
  ring

omit [NeZero n] in
/-- The contribution of a doubled position `b` vanishes on the columns of the arcs other than the
radii at `b`. -/
private theorem digonContribution_eq_zero (T : Finset (TaggedArc n)) {b : Fin n} {γ : TaggedArc n}
    (h : ∀ σ, γ ≠ .radius σ b) (δ : DRow n) : digonContribution T b δ γ = 0 := by
  unfold digonContribution
  split_ifs
  · simp only [Matrix.add_apply, lamMatrix_apply, segVec_arc_arc, if_neg (h _)]
    ring
  · rfl

/-- The column of the segment of a chord of a sector run only receives contributions from outer
triangles. -/
private theorem dMatrix_ordArc_eq_outer (hn : 3 ≤ n) {T : Finset (TaggedArc n)} {a : Fin n}
    (ha : a ∈ radiusSet T) {x z : ℤ} (hxz : (x, z) ∈ sectorChords T (radiusSet T) a)
    (δ : DRow n) :
    dMatrix T δ (ordArc x z) = ∑ p ∈ outerTriangles T, outerContribution p δ (ordArc x z) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨h4, h6⟩ := isRunChord_length_bounds ha (mem_sectorChords.1 hxz).1
  rw [dMatrix_apply]
  have hP : ∑ p ∈ punctureTriangles T, punctureContribution T p.1 p.2 δ (ordArc x z) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨hb, -⟩ := mem_punctureTriangles.1 hp
    have h1 : DRow.arc (ordArc x z) ∉
        (seg (p.2 : ℤ) (p.2 + gap (radiusSet T) p.2) : DSeg n).rows := by
      intro h
      obtain ⟨hba, he⟩ := eq_of_ordArc_mem_rows hn2 ha hb hxz (Or.inr (Or.inr rfl)) h
      obtain ⟨-, -, -, -, h5⟩ := (mem_sectorChords.1 hxz).1
      rw [hba] at he
      exact h5 he.symm
    rw [punctureContribution_apply, segVec_eq_zero h1, segVec_arc_arc, segVec_arc_arc,
      if_neg (ordArc_ne_radius h4 h6 _ _), if_neg (ordArc_ne_radius h4 h6 _ _)]
    ring
  have hD : ∑ b, digonContribution T b δ (ordArc x z) = 0 :=
    Finset.sum_eq_zero fun b _ => digonContribution_eq_zero T (ordArc_ne_radius h4 h6 · b) δ
  rw [hP, hD]
  ring

/-- `-(+) = -`. -/
private theorem tag_neg_plain : -Tag.plain = Tag.notched := rfl

/-- `-(-) = +`. -/
private theorem tag_neg_notched : -Tag.notched = Tag.plain := rfl

/-- For `0 < d < n`, `κ(u, u + d) = χ(ū, \overline{u + d})`. -/
private theorem kappa_add_eq_cut {u d : ℤ} (h₁ : 0 < d) (h₂ : d < n) :
    kappa n u (u + d) = cut (vtx u : Fin n) (vtx (u + d)) :=
  (cdist_vtx_kappa_eq_cut (n := n) (by omega) (by omega)).2.1

/-- For `|R| ≥ 2`, `a⁺ ≠ a`. -/
private theorem succ_ne_self {R : Finset (Fin n)} (hR : 2 ≤ R.card) {a : Fin n} (ha : a ∈ R) :
    succ R a ≠ a := by
  have h1 := (gap_spec ha).1
  have h2 := gap_le_sub_one hR ha
  have := vtx_add_ne_self (n := n) (u := a) (d := gap R a) (by omega) (by omega)
  rwa [vtx_coe] at this

/-- For `|R| ≥ 2`, `a⁻ ≠ a`. -/
private theorem pred_ne_self {R : Finset (Fin n)} (hR : 2 ≤ R.card) {a : Fin n} (ha : a ∈ R) :
    pred R a ≠ a := by
  intro h
  have := (succ_pred ha).2
  rw [h] at this
  exact succ_ne_self hR ha this

/-- The predecessor of `a ∈ R` is the only element of `R` with successor `a`. -/
private theorem eq_pred_of_succ_eq {R : Finset (Fin n)} {a b : Fin n} (ha : a ∈ R) (hb : b ∈ R)
    (h : succ R b = a) : b = pred R a := by
  obtain ⟨hc, hsc⟩ := succ_pred ha
  have hb1 := (gap_spec hb).1
  have hc1 := (gap_spec hc).1
  have hv : (vtx ((b : ℤ) + (gap R b : ℤ) + -1) : Fin n) =
      vtx ((pred R a : ℤ) + (gap R (pred R a) : ℤ) + -1) :=
    vtx_add_congr (h.trans hsc.symm) _
  have := (existsUnique_vtx_eq ⟨a, ha⟩ (vtx ((b : ℤ) + (gap R b : ℤ) + -1))).unique
    (y₁ := (b, (b : ℤ) + (gap R b : ℤ) + -1))
    (y₂ := (pred R a, (pred R a : ℤ) + (gap R (pred R a) : ℤ) + -1))
    ⟨hb, by simp only; omega, by simp only; omega, rfl⟩
    ⟨hc, by simp only; omega, by simp only; omega, hv.symm⟩
  exact congrArg Prod.fst this

omit [NeZero n] in
/-- A position not carrying both radii contributes nothing. -/
private theorem digonContribution_eq_zero_of_not {T : Finset (TaggedArc n)} {b : Fin n}
    (h : ¬(TaggedArc.radius .plain b ∈ T ∧ TaggedArc.radius .notched b ∈ T)) (δ : DRow n)
    (γ : TaggedArc n) : digonContribution T b δ γ = 0 := by
  simp [digonContribution, if_neg h]

/-- The segment of a chord `(x, z)` of a sector run lies in the rows of no other segment of that
sector run. -/
private theorem ordArc_notMem_rows (hn : 2 ≤ n) {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    {a : Fin n} (ha : a ∈ R) {x z : ℤ} (hxz : (x, z) ∈ sectorChords T R a) {p q : ℤ}
    (hs : IsRunSegment a (a + gap R a) (sectorChords T R a) (p, q)) (hne : (p, q) ≠ (x, z)) :
    DRow.arc (ordArc x z) ∉ (seg p q : DSeg n).rows :=
  fun h => hne (eq_of_ordArc_mem_rows hn ha ha hxz hs h).2

/-- In the column of the segment of a chord `(x, z)` of a sector run, the outer triangles other
than the triangle with base `(x, z)` and the parent of `(x, z)` contribute nothing. -/
private theorem outerContribution_ordArc_eq_zero (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {a : Fin n} (ha : a ∈ radiusSet T) {x y z : ℤ}
    (hxz : (x, z) ∈ sectorChords T (radiusSet T) a)
    (hy : IsRunTriangle a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a) x y z)
    {t : ℤ × ℤ × ℤ}
    (ht : IsRunTriangle a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a) t.1 t.2.1
      t.2.2 ∧ ((t.1 = x ∧ t.2.1 = z) ∨ (t.2.1 = x ∧ t.2.2 = z)))
    {p : Fin n × ℤ × ℤ × ℤ} (hp : p ∈ outerTriangles T) (hp₁ : p ≠ (a, x, y, z))
    (hp₂ : p ≠ (a, t)) (δ : DRow n) : outerContribution p δ (ordArc x z) = 0 := by
  have hn2 : 2 ≤ n := by omega
  have hR := isRunTriangulation_of_isTaggedTriangulation hT ha
  have huv : 2 ≤ ((a : ℤ) + (gap (radiusSet T) a : ℤ)) - a := by
    obtain ⟨h1, -, h3, h4, -⟩ := (mem_sectorChords.1 hxz).1
    simp only at h1 h3 h4
    omega
  obtain ⟨b, x1, y1, z1⟩ := p
  obtain ⟨hb, ht1⟩ := mem_outerTriangles.1 hp
  simp only at hb ht1 ⊢
  apply outerContribution_eq_zero <;> intro h
  · obtain ⟨rfl, he⟩ := eq_of_ordArc_mem_rows hn2 ha hb hxz ht1.2.2.1 h
    simp only [Prod.mk.injEq] at he
    rw [he.1, he.2] at ht1
    exact hp₂ (by rw [he.1, he.2, (hR.existsUnique_parent hxz).unique (y₁ := (x, z, z1))
      ⟨ht1, Or.inl ⟨rfl, rfl⟩⟩ ht])
  · obtain ⟨rfl, he⟩ := eq_of_ordArc_mem_rows hn2 ha hb hxz ht1.2.2.2.1 h
    simp only [Prod.mk.injEq] at he
    rw [he.1, he.2] at ht1
    exact hp₂ (by rw [he.1, he.2, (hR.existsUnique_parent hxz).unique (y₁ := (x1, x, z))
      ⟨ht1, Or.inr ⟨rfl, rfl⟩⟩ ht])
  · obtain ⟨rfl, he⟩ := eq_of_ordArc_mem_rows hn2 ha hb hxz ht1.2.2.2.2 h
    simp only [Prod.mk.injEq] at he
    rw [he.1, he.2] at ht1
    exact hp₁ (by rw [he.1, he.2, (hR.existsUnique_apex huv (Or.inl hxz)).unique ht1 hy])

/-- An ordinary arc `(u, v)` with `2 ≤ v - u ≤ n - 1` is a row of the segment `s(u, v)`. -/
theorem ordArc_mem_rows_seg {u v : ℤ} (h₁ : 2 ≤ v - u) (h₂ : v - u ≤ n - 1) :
    DRow.arc (ordArc u v) ∈ (seg u v : DSeg n).rows := by
  rw [(seg_eq_arc (n := n) h₁ h₂).1]
  simp [DSeg.rows]

/-- **The columns of `B̃•(T)`**, case (1) with parent `(x, z, w)`: for `(x, z) ∈ T_R(a)` with
apex `y`, the column of `s(x, z)` is
`e_{s(y,z)} + e_{s(x,w)} - e_{s(x,y)} - e_{s(z,w)} - κ(y, z)(e_λ + e_λ̄)`. -/
@[cluster_algebras "lem_D_columns"]
theorem dMatrix_col_ordArc_right (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {a : Fin n} (ha : a ∈ radiusSet T) {x y z w : ℤ}
    (hxz : (x, z) ∈ sectorChords T (radiusSet T) a)
    (hy : IsRunTriangle a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a) x y z)
    (hw : IsRunTriangle a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a) x z w) :
    (fun δ => dMatrix T δ (ordArc x z)) =
      segVec (seg y z) + segVec (seg x w) - segVec (seg x y) - segVec (seg z w) -
        kappa n y z • (rowVec (.lam .plain) + rowVec (.lam .notched)) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨h4, h6⟩ := isRunChord_length_bounds ha (mem_sectorChords.1 hxz).1
  have hmem := ordArc_mem_rows_seg (n := n) h4 h6
  have hp1 : ((a, x, y, z) : Fin n × ℤ × ℤ × ℤ) ∈ outerTriangles T :=
    mem_outerTriangles.2 ⟨ha, hy⟩
  have hp2 : ((a, x, z, w) : Fin n × ℤ × ℤ × ℤ) ∈ outerTriangles T :=
    mem_outerTriangles.2 ⟨ha, hw⟩
  have hne : ((a, x, y, z) : Fin n × ℤ × ℤ × ℤ) ≠ (a, x, z, w) := by
    have := hy.2.1
    simp only [ne_eq, Prod.mk.injEq, not_and]
    omega
  have n1 := ordArc_notMem_rows hn2 ha hxz hy.2.2.1
    (by have := hy.2.1; simp only [ne_eq, Prod.mk.injEq]; omega)
  have n2 := ordArc_notMem_rows hn2 ha hxz hy.2.2.2.1
    (by have := hy.1; simp only [ne_eq, Prod.mk.injEq]; omega)
  have n3 := ordArc_notMem_rows hn2 ha hxz hw.2.2.2.1
    (by have := hw.1; simp only [ne_eq, Prod.mk.injEq]; omega)
  have n4 := ordArc_notMem_rows hn2 ha hxz hw.2.2.2.2
    (by have := hw.2.1; simp only [ne_eq, Prod.mk.injEq]; omega)
  funext δ
  rw [dMatrix_ordArc_eq_outer hn ha hxz δ, Finset.sum_eq_add_of_mem _ _ hp1 hp2 hne
      fun p hp hp' => outerContribution_ordArc_eq_zero hn hT ha hxz hy (t := (x, z, w))
        ⟨hw, Or.inl ⟨rfl, rfl⟩⟩ hp hp'.1 hp'.2 δ,
    outerContribution_apply, outerContribution_apply]
  simp only [segVec_eq_one hmem, segVec_eq_zero n1, segVec_eq_zero n2, segVec_eq_zero n3,
    segVec_eq_zero n4, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The columns of `B̃•(T)`**, case (1) with parent `(x', x, z)`: for `(x, z) ∈ T_R(a)` with
apex `y`, the column of `s(x, z)` is
`e_{s(y,z)} + e_{s(x',x)} - e_{s(x,y)} - e_{s(x',z)} + κ(x, y)(e_λ + e_λ̄)`. -/
@[cluster_algebras "lem_D_columns"]
theorem dMatrix_col_ordArc_left (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {a : Fin n} (ha : a ∈ radiusSet T) {x' x y z : ℤ}
    (hxz : (x, z) ∈ sectorChords T (radiusSet T) a)
    (hy : IsRunTriangle a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a) x y z)
    (hx' : IsRunTriangle a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a) x' x z) :
    (fun δ => dMatrix T δ (ordArc x z)) =
      segVec (seg y z) + segVec (seg x' x) - segVec (seg x y) - segVec (seg x' z) +
        kappa n x y • (rowVec (.lam .plain) + rowVec (.lam .notched)) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨h4, h6⟩ := isRunChord_length_bounds ha (mem_sectorChords.1 hxz).1
  have hmem := ordArc_mem_rows_seg (n := n) h4 h6
  have hp1 : ((a, x, y, z) : Fin n × ℤ × ℤ × ℤ) ∈ outerTriangles T :=
    mem_outerTriangles.2 ⟨ha, hy⟩
  have hp2 : ((a, x', x, z) : Fin n × ℤ × ℤ × ℤ) ∈ outerTriangles T :=
    mem_outerTriangles.2 ⟨ha, hx'⟩
  have hne : ((a, x, y, z) : Fin n × ℤ × ℤ × ℤ) ≠ (a, x', x, z) := by
    have := hx'.1
    simp only [ne_eq, Prod.mk.injEq, not_and]
    omega
  have n1 := ordArc_notMem_rows hn2 ha hxz hy.2.2.1
    (by have := hy.2.1; simp only [ne_eq, Prod.mk.injEq]; omega)
  have n2 := ordArc_notMem_rows hn2 ha hxz hy.2.2.2.1
    (by have := hy.1; simp only [ne_eq, Prod.mk.injEq]; omega)
  have n3 := ordArc_notMem_rows hn2 ha hxz hx'.2.2.1
    (by have := hx'.1; simp only [ne_eq, Prod.mk.injEq]; omega)
  have n4 := ordArc_notMem_rows hn2 ha hxz hx'.2.2.2.2
    (by have := hx'.1; simp only [ne_eq, Prod.mk.injEq]; omega)
  funext δ
  rw [dMatrix_ordArc_eq_outer hn ha hxz δ, Finset.sum_eq_add_of_mem _ _ hp1 hp2 hne
      fun p hp hp' => outerContribution_ordArc_eq_zero hn hT ha hxz hy (t := (x', x, z))
        ⟨hx', Or.inr ⟨rfl, rfl⟩⟩ hp hp'.1 hp'.2 δ,
    outerContribution_apply, outerContribution_apply]
  simp only [segVec_eq_one hmem, segVec_eq_zero n1, segVec_eq_zero n2, segVec_eq_zero n3,
    segVec_eq_zero n4, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    kappa_add (n := n) x y z]
  ring

/-- In kind `P_τ`, in the column of the outer arc `α_R(a)` the outer triangles other than the
triangle on the outer side of the sector run of `a` contribute nothing. -/
private theorem outerContribution_outerArc_eq_zero (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    {τ : Tag} {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R)
    (hg : 2 ≤ gap R a) {y : ℤ}
    (hy : IsRunTriangle a (a + gap R a) (sectorChords T R a) a y (a + gap R a))
    {p : Fin n × ℤ × ℤ × ℤ} (hp : p ∈ outerTriangles T)
    (hne : p ≠ ((a, a, y, a + gap R a) : Fin n × ℤ × ℤ × ℤ)) (δ : DRow n) :
    outerContribution p δ (outerArc R a) = 0 := by
  have hn2 : 2 ≤ n := by omega
  have hg' := gap_le_sub_one hT.1 ha
  have hRT := hT.2.2.1 a ha
  have huv : 2 ≤ ((a : ℤ) + (gap R a : ℤ)) - a := by omega
  obtain ⟨b, x1, y1, z1⟩ := p
  obtain ⟨hb, ht⟩ := mem_outerTriangles.1 hp
  simp only at hb ht ⊢
  rw [radiusSet_eq_of_isKindP hT] at hb ht
  apply outerContribution_eq_zero <;> intro h
  · obtain ⟨rfl, he⟩ := eq_of_outerArc_mem_rows hn2 ha hb hg hg' ht.2.2.1 h
    exact (hRT.short_sides_ne_outer ht).1 he
  · obtain ⟨rfl, he⟩ := eq_of_outerArc_mem_rows hn2 ha hb hg hg' ht.2.2.2.1 h
    exact (hRT.short_sides_ne_outer ht).2.1 he
  · obtain ⟨rfl, he⟩ := eq_of_outerArc_mem_rows hn2 ha hb hg hg' ht.2.2.2.2 h
    simp only [Prod.mk.injEq] at he
    rw [he.1, he.2] at ht
    exact hne (by rw [he.1, he.2, (hRT.existsUnique_apex huv (Or.inr rfl)).unique ht hy])

/-- In kind `P_τ`, in the column of the outer arc `α_R(a)` the puncture triangles other than
`(τ, a)` contribute nothing. -/
private theorem punctureContribution_outerArc_eq_zero (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    {τ : Tag} {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R)
    (hg : 2 ≤ gap R a) {p : Tag × Fin n} (hp : p ∈ punctureTriangles T) (hne : p ≠ (τ, a))
    (δ : DRow n) : punctureContribution T p.1 p.2 δ (outerArc R a) = 0 := by
  have hRS := radiusSet_eq_of_isKindP hT
  have hg' := gap_le_sub_one hT.1 ha
  have hord : ∀ σ b, outerArc R a ≠ .radius σ b := ordArc_ne_radius (by omega) (by omega)
  obtain ⟨σ, b⟩ := p
  obtain ⟨hb, hσ⟩ := mem_punctureTriangles.1 hp
  simp only at hb hσ
  rw [hRS] at hb
  rw [isPunctureKind_iff_of_isKindP hT] at hσ
  subst hσ
  have n1 : DRow.arc (outerArc R a) ∉ (seg (b : ℤ) (b + gap R b) : DSeg n).rows := fun h =>
    hne (by rw [(eq_of_outerArc_mem_rows (T := T) (by omega) ha hb hg hg'
      (Or.inr (Or.inr rfl)) h).1])
  rw [punctureContribution_apply]
  simp only [hRS, segVec_eq_zero n1, segVec_arc_arc, if_neg (hord _ _)]
  ring

/-- **The columns of `B̃•(T)`**, case (2): in kind `P_τ`, for `u = a`, `v = a + g_R(a)` and the
apex `y` of `(u, v)`, the column of the outer arc `α_R(a)` is
`e_{s(y,v)} + e_{ρ^τ_a} - e_{s(u,y)} - e_{ρ^τ_{a⁺}} + κ(u, y) e_{λ_τ} - κ(y, v) e_{λ_{-τ}}`. -/
@[cluster_algebras "lem_D_columns"]
theorem dMatrix_col_outerArc (hn : 3 ≤ n) {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) (hg : 2 ≤ gap R a)
    {y : ℤ} (hy : IsRunTriangle a (a + gap R a) (sectorChords T R a) a y (a + gap R a)) :
    (fun δ => dMatrix T δ (outerArc R a)) =
      segVec (seg y (a + gap R a)) + rowVec (.arc (.radius τ a)) - segVec (seg (a : ℤ) y) -
        rowVec (.arc (.radius τ (succ R a))) + kappa n a y • rowVec (.lam τ) -
        kappa n y (a + gap R a) • rowVec (.lam (-τ)) := by
  have hn2 : 2 ≤ n := by omega
  have hRS := radiusSet_eq_of_isKindP hT
  have hg' := gap_le_sub_one hT.1 ha
  have hord : ∀ σ b, outerArc R a ≠ .radius σ b := ordArc_ne_radius (by omega) (by omega)
  have key : ∀ b ∈ R, ∀ p q : ℤ, IsRunSegment b (b + gap R b) (sectorChords T R b) (p, q) →
      DRow.arc (outerArc R a) ∈ (seg p q : DSeg n).rows →
      b = a ∧ (p, q) = ((b : ℤ), (b : ℤ) + (gap R b : ℤ)) :=
    fun b hb p q hs h => eq_of_outerArc_mem_rows hn2 ha hb hg hg' hs h
  have hmem : DRow.arc (outerArc R a) ∈ (seg (a : ℤ) (a + gap R a) : DSeg n).rows := by
    rw [(seg_eq_arc (n := n) (by omega) (by omega)).1]
    simp [DSeg.rows, outerArc]
  have hcut : cut a (succ R a) = kappa n a y + kappa n y (a + gap R a) := by
    rw [← kappa_add]
    obtain ⟨-, h, -⟩ := cdist_vtx_kappa_eq_cut (n := n) (u := a) (v := a + gap R a)
      (by omega) (by omega)
    rw [h, vtx_coe]
    rfl
  have hp1 : ((a, a, y, a + gap R a) : Fin n × ℤ × ℤ × ℤ) ∈ outerTriangles T :=
    mem_outerTriangles.2 ⟨hRS ▸ ha, hRS ▸ hy⟩
  have hq1 : ((τ, a) : Tag × Fin n) ∈ punctureTriangles T :=
    mem_punctureTriangles.2 ⟨hRS ▸ ha, (isPunctureKind_iff_of_isKindP hT τ).2 rfl⟩
  have n1 : DRow.arc (outerArc R a) ∉ (seg (a : ℤ) y : DSeg n).rows := fun h => by
    have := hy.2.1
    have := (Prod.mk.inj (key a ha _ _ hy.2.2.1 h).2).2
    omega
  have n2 : DRow.arc (outerArc R a) ∉ (seg y (a + gap R a) : DSeg n).rows := fun h => by
    have := hy.1
    have := (Prod.mk.inj (key a ha _ _ hy.2.2.2.1 h).2).1
    omega
  funext δ
  rw [dMatrix_apply, Finset.sum_eq_single_of_mem _ hp1
      fun p hp hne => outerContribution_outerArc_eq_zero hn hT ha hg hy hp hne δ,
    Finset.sum_eq_single_of_mem _ hq1
      fun p hp hne => punctureContribution_outerArc_eq_zero hn hT ha hg hp hne δ,
    Finset.sum_eq_zero fun b _ => digonContribution_eq_zero T (hord · b) δ,
    outerContribution_apply, punctureContribution_apply]
  simp only [hRS, segVec_eq_one hmem, segVec_eq_zero n1, segVec_eq_zero n2, segVec_arc_arc,
    if_neg (hord _ _), Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hcut]
  cases τ <;> simp only [tag_neg_plain, tag_neg_notched] <;> ring

/-- In kind `P_τ`, no segment of a sector run has the radius `ρ^τ_a` among its rows. -/
private theorem radius_notMem_rows_of_isKindP (hn : 2 ≤ n) {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) {a b : Fin n} (hb : b ∈ R) {p q : ℤ}
    (hs : IsRunSegment b (b + gap R b) (sectorChords T R b) (p, q)) :
    DRow.arc (.radius τ a) ∉ (seg p q : DSeg n).rows := fun h => by
  have := (eq_of_radius_mem_rows hn hb hs h).2.1
  have := gap_le_sub_one hT.1 hb
  omega

/-- In kind `P_τ`, the outer triangles contribute nothing to the column of a radius. -/
private theorem outerContribution_radius_eq_zero_of_isKindP (hn : 2 ≤ n)
    {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)} (hT : IsKindP T τ R) (a : Fin n)
    {p : Fin n × ℤ × ℤ × ℤ} (hp : p ∈ outerTriangles T) (δ : DRow n) :
    outerContribution p δ (.radius τ a) = 0 := by
  obtain ⟨b, x1, y1, z1⟩ := p
  obtain ⟨hb, ht⟩ := mem_outerTriangles.1 hp
  simp only at hb ht
  rw [radiusSet_eq_of_isKindP hT] at hb ht
  exact outerContribution_eq_zero (radius_notMem_rows_of_isKindP hn hT hb ht.2.2.1)
    (radius_notMem_rows_of_isKindP hn hT hb ht.2.2.2.1)
    (radius_notMem_rows_of_isKindP hn hT hb ht.2.2.2.2) δ

/-- In kind `P_τ`, in the column of the radius `ρ^τ_a` the puncture triangles other than `(τ, a)`
and `(τ, a⁻)` contribute nothing. -/
private theorem punctureContribution_radius_eq_zero_of_isKindP (hn : 2 ≤ n)
    {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n}
    (ha : a ∈ R) {p : Tag × Fin n} (hp : p ∈ punctureTriangles T)
    (hne : p ≠ (τ, a) ∧ p ≠ (τ, pred R a)) (δ : DRow n) :
    punctureContribution T p.1 p.2 δ (.radius τ a) = 0 := by
  have hRS := radiusSet_eq_of_isKindP hT
  obtain ⟨σ, b⟩ := p
  obtain ⟨hb, hσ⟩ := mem_punctureTriangles.1 hp
  simp only at hb hσ
  rw [hRS] at hb
  rw [isPunctureKind_iff_of_isKindP hT] at hσ
  subst hσ
  have hba : ¬a = b := fun h => hne.1 (by rw [h])
  have hsb : ¬a = succ R b := fun h => hne.2 (by rw [eq_pred_of_succ_eq ha hb h.symm])
  rw [punctureContribution_apply]
  simp only [hRS,
    segVec_eq_zero (radius_notMem_rows_of_isKindP hn hT (a := a) hb (Or.inr (Or.inr rfl))),
    segVec_arc_arc, TaggedArc.radius.injEq, true_and, if_neg hba, if_neg hsb]
  ring

/-- **The columns of `B̃•(T)`**, case (3): in kind `P_τ`, with `x = a⁻`, `y = x + g_R(a⁻)` and
`z = y + g_R(a)`, the column of the radius `ρ^τ_a` is
`e_{s(x,y)} + e_{ρ^τ_{a⁺}} - e_{ρ^τ_{a⁻}} - e_{s(y,z)} - κ(x, y) e_{λ_τ} + κ(y, z) e_{λ_{-τ}}`;
when `|R| = 2` the two radius terms cancel. -/
@[cluster_algebras "lem_D_columns"]
theorem dMatrix_col_radius_of_isKindP (hn : 3 ≤ n) {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hT : IsKindP T τ R) {a : Fin n} (ha : a ∈ R) :
    (fun δ => dMatrix T δ (.radius τ a)) =
      segVec (seg (pred R a : ℤ) ((pred R a : ℤ) + gap R (pred R a))) +
        rowVec (.arc (.radius τ (succ R a))) - rowVec (.arc (.radius τ (pred R a))) -
        segVec (seg ((pred R a : ℤ) + gap R (pred R a))
          ((pred R a : ℤ) + gap R (pred R a) + gap R a)) -
        kappa n (pred R a) ((pred R a : ℤ) + gap R (pred R a)) • rowVec (.lam τ) +
        kappa n ((pred R a : ℤ) + gap R (pred R a))
          ((pred R a : ℤ) + gap R (pred R a) + gap R a) • rowVec (.lam (-τ)) := by
  have hn2 : 2 ≤ n := by omega
  have hRS := radiusSet_eq_of_isKindP hT
  obtain ⟨hc, hsc⟩ := succ_pred ha
  have hac : a ≠ pred R a := fun h => pred_ne_self hT.1 ha h.symm
  have hsa : a ≠ succ R a := fun h => succ_ne_self hT.1 ha h.symm
  have hga := (gap_spec ha).1
  have hga' := gap_le_sub_one hT.1 ha
  have hgc := (gap_spec hc).1
  have hgc' := gap_le_sub_one hT.1 hc
  have hvy : (vtx ((pred R a : ℤ) + (gap R (pred R a) : ℤ)) : Fin n) = vtx (a : ℤ) :=
    hsc.trans (vtx_coe a).symm
  have hseg : (seg ((pred R a : ℤ) + gap R (pred R a))
      ((pred R a : ℤ) + gap R (pred R a) + gap R a) : DSeg n) = seg (a : ℤ) (a + gap R a) :=
    seg_congr hvy (by ring)
  have hk1 : kappa n (pred R a) ((pred R a : ℤ) + gap R (pred R a)) = cut (pred R a) a := by
    rw [kappa_add_eq_cut (by omega) (by omega), vtx_coe, hvy, vtx_coe]
  have hk2 : kappa n ((pred R a : ℤ) + gap R (pred R a))
      ((pred R a : ℤ) + gap R (pred R a) + gap R a) = cut a (succ R a) := by
    rw [kappa_add_eq_cut (by omega) (by omega), hvy, vtx_coe, vtx_add_congr hvy]
    rfl
  have hq1 : ((τ, a) : Tag × Fin n) ∈ punctureTriangles T :=
    mem_punctureTriangles.2 ⟨hRS ▸ ha, (isPunctureKind_iff_of_isKindP hT τ).2 rfl⟩
  have hq2 : ((τ, pred R a) : Tag × Fin n) ∈ punctureTriangles T :=
    mem_punctureTriangles.2 ⟨hRS ▸ hc, (isPunctureKind_iff_of_isKindP hT τ).2 rfl⟩
  have hne : ((τ, a) : Tag × Fin n) ≠ (τ, pred R a) := fun h => hac (congrArg Prod.snd h)
  have n1 := radius_notMem_rows_of_isKindP hn2 hT (a := a) ha (Or.inr (Or.inr rfl))
  have n2 := radius_notMem_rows_of_isKindP hn2 hT (a := a) hc (Or.inr (Or.inr rfl))
  funext δ
  rw [dMatrix_apply,
    Finset.sum_eq_zero fun p hp => outerContribution_radius_eq_zero_of_isKindP hn2 hT a hp δ,
    Finset.sum_eq_add_of_mem _ _ hq1 hq2 hne
      fun p hp hne' => punctureContribution_radius_eq_zero_of_isKindP hn2 hT ha hp hne' δ,
    Finset.sum_eq_zero fun b _ =>
      digonContribution_eq_zero_of_not (not_both_radii_of_isKindP hT b) δ _,
    punctureContribution_apply, punctureContribution_apply]
  simp only [hRS, hsc, segVec_eq_zero n1, segVec_eq_zero n2, segVec_arc_arc,
    TaggedArc.radius.injEq, true_and, if_true, if_neg hac, if_neg hsa, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hseg, hk1, hk2]
  ring

/-- In the digon kind at `a`, in the column of a radius `ρ^τ_a` the outer triangles other than
the triangle on the loop `L_a` contribute nothing. -/
private theorem outerContribution_radius_eq_zero_of_isDigonKind (hn : 3 ≤ n)
    {T : Finset (TaggedArc n)} {a : Fin n} (hT : IsDigonKind T a) (τ : Tag) {y : ℤ}
    (hy : IsRunTriangle a (a + gap {a} a) (sectorChords T {a} a) a y (a + gap {a} a))
    {p : Fin n × ℤ × ℤ × ℤ} (hp : p ∈ outerTriangles T)
    (hne : p ≠ ((a, a, y, a + gap {a} a) : Fin n × ℤ × ℤ × ℤ)) (δ : DRow n) :
    outerContribution p δ (.radius τ a) = 0 := by
  have hn2 : 2 ≤ n := by omega
  have hRT := hT.2.1
  have huv : 2 ≤ ((a : ℤ) + (gap {a} a : ℤ)) - a := by
    rw [(gap_singleton a).1]
    omega
  obtain ⟨b, x1, y1, z1⟩ := p
  obtain ⟨hb, ht⟩ := mem_outerTriangles.1 hp
  simp only at hb ht ⊢
  rw [radiusSet_eq_of_isDigonKind hT] at hb ht
  obtain rfl : b = a := Finset.mem_singleton.1 hb
  apply outerContribution_eq_zero <;> intro h
  · exact (hRT.short_sides_ne_outer ht).1 (eq_of_radius_mem_rows hn2 hb ht.2.2.1 h).2.2
  · exact (hRT.short_sides_ne_outer ht).2.1 (eq_of_radius_mem_rows hn2 hb ht.2.2.2.1 h).2.2
  · have he := (eq_of_radius_mem_rows hn2 hb ht.2.2.2.2 h).2.2
    simp only [Prod.mk.injEq] at he
    rw [he.1, he.2] at ht
    exact hne (by rw [he.1, he.2, (hRT.existsUnique_apex huv (Or.inr rfl)).unique ht hy])

/-- **The columns of `B̃•(T)`**, case (4): in the digon kind at `a`, with `u = a` and `y` the apex
of `(u, u + n)`, the column of the radius `ρ^τ_a` is
`e_{s(y,u+n)} - e_{s(u,y)} - κ(y, u + n) e_{λ_τ} + κ(u, y) e_{λ_{-τ}}`. -/
@[cluster_algebras "lem_D_columns"]
theorem dMatrix_col_radius_of_isDigonKind (hn : 3 ≤ n) {T : Finset (TaggedArc n)} {a : Fin n}
    (hT : IsDigonKind T a) (τ : Tag) {y : ℤ}
    (hy : IsRunTriangle a (a + gap {a} a) (sectorChords T {a} a) a y (a + gap {a} a)) :
    (fun δ => dMatrix T δ (.radius τ a)) =
      segVec (seg y ((a : ℤ) + n)) - segVec (seg (a : ℤ) y) -
        kappa n y ((a : ℤ) + n) • rowVec (.lam τ) + kappa n a y • rowVec (.lam (-τ)) := by
  have hn2 : 2 ≤ n := by omega
  have hRS := radiusSet_eq_of_isDigonKind hT
  obtain ⟨hgn, -, -⟩ := gap_singleton a
  have hmem : DRow.arc (.radius τ a) ∈ (seg (a : ℤ) (a + gap {a} a) : DSeg n).rows := by
    rw [hgn, seg_eq_loop hn2, vtx_coe]
    cases τ <;> simp [DSeg.rows]
  have hp1 : ((a, a, y, a + gap {a} a) : Fin n × ℤ × ℤ × ℤ) ∈ outerTriangles T :=
    mem_outerTriangles.2 ⟨by simp [hRS], hRS ▸ hy⟩
  have hP : punctureTriangles T = ∅ := by
    ext p
    simp [mem_punctureTriangles, IsPunctureKind, hRS]
  have hka : kappa n a y = 1 - kappa n y ((a : ℤ) + n) := by
    have := kappa_add (n := n) a y (a + n)
    rw [kappa_self_add_n] at this
    omega
  have n1 : DRow.arc (.radius τ a) ∉ (seg (a : ℤ) y : DSeg n).rows := fun h => by
    have := hy.2.1
    have := (Prod.mk.inj (eq_of_radius_mem_rows hn2 (Finset.mem_singleton_self a)
      hy.2.2.1 h).2.2).2
    omega
  have n2 : DRow.arc (.radius τ a) ∉ (seg y (a + gap {a} a) : DSeg n).rows := fun h => by
    have := hy.1
    have := (Prod.mk.inj (eq_of_radius_mem_rows hn2 (Finset.mem_singleton_self a)
      hy.2.2.2.1 h).2.2).1
    omega
  funext δ
  rw [dMatrix_apply, Finset.sum_eq_single_of_mem _ hp1 fun p hp hne =>
      outerContribution_radius_eq_zero_of_isDigonKind hn hT τ hy hp hne δ,
    hP, Finset.sum_empty, Finset.sum_eq_single a (fun b _ hb =>
      digonContribution_eq_zero_of_not (fun h => hb ((hT.1 _ _).1 h.1)) δ _) (by simp),
    outerContribution_apply, digonContribution, if_pos ⟨(hT.1 _ _).2 rfl, (hT.1 _ _).2 rfl⟩]
  simp only [segVec_eq_one hmem, segVec_eq_zero n1, segVec_eq_zero n2, Matrix.add_apply,
    lamMatrix_apply, segVec_arc_arc, TaggedArc.radius.injEq, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hka]
  rw [hgn]
  cases τ <;> simp only [tag_neg_plain, tag_neg_notched, reduceCtorEq, and_true, and_self,
    if_true, if_false] <;> ring

/-! ### Labellings -/

/-- A **labelling** of `T`: a bijection `ℓ : [1, n] → T`, here an injective map
`Fin n → TaggedArc n` with range `T`. -/
@[cluster_algebras "def_D_labelled_matrix"]
def IsLabelling (T : Finset (TaggedArc n)) (ℓ : Fin n → TaggedArc n) : Prop :=
  Function.Injective ℓ ∧ Set.range ℓ = (T : Set (TaggedArc n))

/-- The **extended labelling** `ℓ̂ : [1, 2n + 2] → ℛ(T)`: `ℓ̂(i) = ℓ(i)` for `i < n`,
`ℓ̂(n + i) = β_i`, `ℓ̂(2n) = λ` and `ℓ̂(2n + 1) = λ̄` (indices from `0`). -/
@[cluster_algebras "def_D_labelled_matrix"]
def extLabel (ℓ : Fin n → TaggedArc n) (i : Fin (2 * n + 2)) : DRow n :=
  if h : (i : ℕ) < n then .arc (ℓ ⟨i, h⟩)
  else if h' : (i : ℕ) < 2 * n then .boundary ⟨i - n, by omega⟩
  else if (i : ℕ) = 2 * n then .lam .plain
  else .lam .notched

/-- `n ≤ 2n + 2`: the mutable indices of the labelled matrix. -/
theorem le_two_mul_add_two (n : ℕ) : n ≤ 2 * n + 2 := by
  omega

/-- The **labelled matrix** `B̃•(T, ℓ)`: the `(2n + 2) × n` matrix with entries
`b_{ℓ̂(i) ℓ(j)}`. -/
@[cluster_algebras "def_D_labelled_matrix"]
def labelledMatrix (T : Finset (TaggedArc n)) (ℓ : Fin n → TaggedArc n) :
    Matrix (Fin (2 * n + 2)) (Fin n) ℤ :=
  Matrix.of fun i j => dMatrix T (extLabel ℓ i) (ℓ j)

/-- The **flipped labelling** `ℓ'` of the flip at `ℓ(k)` with replacement `γ'`: `ℓ` with
`ℓ'(k) = γ'`. -/
@[cluster_algebras "def_D_labelled_matrix"]
def flipLabelling (ℓ : Fin n → TaggedArc n) (k : Fin n) (γ' : TaggedArc n) :
    Fin n → TaggedArc n :=
  Function.update ℓ k γ'

end ClusterAlgebras.TypeD

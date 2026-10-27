/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.ExchangeMatrix
public import ClusterAlgebras.SeedPattern
public import ClusterAlgebras.TreeOrientation
public import ClusterAlgebras.Cartan.Counterpart
public import ClusterAlgebras.FiniteType.Basic
public import ClusterAlgebras.TypeD.External
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# An explicit seed pattern of type `D_n`

The seed pattern `Σ•_n` of [FWZ, Section 5.4], in the specialization `a = (0, 1)`, `ā = (1, 0)`
of its construction. The field is `F_n = 𝕜(p₁, q₁, …, p_n, q_n, λ, λ̄)`; a tagged arc `γ` carries
an element `P_γ`, a `2 × 2` determinant of lifted vectors `w_u`. The seed `Σ(T, ℓ)` of a labelled
tagged triangulation has extended cluster `(P_γ)_{γ ∈ T}`, the boundary values `P_{β_i}` and
`λ, λ̄`, and extended exchange matrix `B̃•(T, ℓ)`; flips are mutations, and the pattern through
the seed of the radius triangulation is of finite type, has a full-rank initial extended exchange
matrix, and has a seed whose exchange matrix is an orientation of the tree `D_n`.

## Main definitions

* `ClusterAlgebras.TypeD.DVar`, `ClusterAlgebras.TypeD.DField`: the indeterminates and the
  field `F_n = FractionRing (MvPolynomial (DVar n) 𝕜)`.
* `ClusterAlgebras.TypeD.liftVec`, `bracket`, `tagVec`: the vectors `w_u`, `e^τ` and the bracket
  `⟨X, Y⟩ = X₁ Y₂ - X₂ Y₁`.
* `ClusterAlgebras.TypeD.arcValue`, `rowValue`, `segValue`: the elements `P_γ`, `P_δ`, `P_s`.
* `ClusterAlgebras.TypeD.dSeed`, `initialLabelling`, `dPattern`: `Σ(T, ℓ)`, `ℓ∘` and `Σ•_n`.
* `ClusterAlgebras.TypeD.dynkinWordD`, `dynkinExchangeD`: the vertex `t_D` and the matrix `B_D`.

## Main statements

* `ClusterAlgebras.TypeD.bracket_liftVec`, `bracket_liftVec_tagVec`: lifted brackets.
* `ClusterAlgebras.TypeD.segValue_mul_segValue`, …: the three exchange identities.
* `ClusterAlgebras.TypeD.IsDFlipReplacement.arcValue_mul_arcValue`: exchange relations of flips.
* `ClusterAlgebras.TypeD.seedMutation_dSeed`: seed mutation is the flip.
* `ClusterAlgebras.TypeD.isLabeledSeed_dSeed_radiusTriangulation`: the initial seed.
* `ClusterAlgebras.TypeD.isFiniteType_dPattern`, `span_labelledMatrix_initial`,
  `isPatternOfType_dPattern`.
* `ClusterAlgebras.TypeD.exists_dPattern_eq_dSeed`,
  `IsTaggedTriangulation.exists_dPattern_eq_dSeed`: the seeds of `Σ•_n` are the `Σ(T, ℓ)`.
* `ClusterAlgebras.TypeD.principalPart_dPattern_dynkinWordD`,
  `exists_orientation_dynkinExchangeD`: `Σ•_n(t_D)` has exchange matrix `B_D`, an orientation
  of `D_n`.

## Implementation notes

* Indices start at `0` (see `ClusterAlgebras.TypeD.Arcs`): the vertex `i` is the vertex `i + 1`
  of [FWZ], and the integer lift `u` is the lift `u + 1` of [FWZ], so `w_u` has sheet
  `η(u) = ⌊u / n⌋` and `w_{u + n} = A w_u` with `A = diag(λ̄, λ)`.
* The indeterminate `λ_τ` is `DVar.lam τ`: `λ_+ = λ` and `λ_- = λ̄`.
* Exponents `κ(u, v)` and `η(u)` are integers and enter through `zpow`; the exchange monomials
  are products of `zpow`s, as in the library's `exchangeMonomialPos`.
* The initial labelling `ℓ∘` is that of [FWZ], shifted: `ℓ∘(k) = ρ^+_{k+1}` for `k ≤ n - 3`,
  `ℓ∘(n - 2) = ρ^+_0` and `ℓ∘(n - 1) = ρ^+_{n-1}`; the vertex `t_D` is the word
  `(0, 1, …, n - 3, n - 1)`.
* `Σ•_n` is defined as the pattern `t ↦ μ_t(Σ(T∘, ℓ∘))`, which is the pattern of
  `ClusterAlgebras.exists_isSeedPattern` through `Σ(T∘, ℓ∘)` at the root; that it is a seed
  pattern is `isSeedPattern_dPattern`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 5][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras.TypeD

open MvPolynomial

variable (K : Type*) [Field K] {n : ℕ} [NeZero n]

/-! ### The field and the elements `P_γ` -/

/-- The indeterminates `p_i`, `q_i` (`i ∈ Fin n`) and `λ_τ` (`λ_+ = λ`, `λ_- = λ̄`) of `F_n`. -/
@[cluster_algebras "def_D_field"]
inductive DVar (n : ℕ) where
  /-- The indeterminate `p_i`. -/
  | p (i : Fin n)
  /-- The indeterminate `q_i`. -/
  | q (i : Fin n)
  /-- The indeterminate `λ_τ`. -/
  | lam (τ : Tag)

/-- The field `F_n = 𝕜(p₁, q₁, …, p_n, q_n, λ, λ̄)` of rational functions in `2n + 2`
indeterminates. -/
@[cluster_algebras "def_D_field"]
abbrev DField (K : Type*) [Field K] (n : ℕ) : Type _ :=
  FractionRing (MvPolynomial (DVar n) K)

/-- An indeterminate of `F_n`. -/
@[cluster_algebras "def_D_field"]
noncomputable def var (v : DVar n) : DField K n :=
  algebraMap (MvPolynomial (DVar n) K) (DField K n) (X v)

/-- The bracket `⟨X, Y⟩ = X₁ Y₂ - X₂ Y₁` of two vectors of `F_n²`. -/
@[cluster_algebras "def_D_field"]
def bracket {F : Type*} [CommRing F] (X Y : F × F) : F :=
  X.1 * Y.2 - X.2 * Y.1

/-- The lifted vector `w_u = (λ̄^{η(u)} p_ū, λ^{η(u)} q_ū)` of an integer `u`. -/
@[cluster_algebras "def_D_field"]
noncomputable def liftVec (u : ℤ) : DField K n × DField K n :=
  (var K (.lam .notched) ^ sheet n u * var K (.p (vtx u)),
    var K (.lam .plain) ^ sheet n u * var K (.q (vtx u)))

/-- The vectors `e^+ = (0, 1)` and `e^- = (λ̄ - λ, 0)`. -/
@[cluster_algebras "def_D_field"]
noncomputable def tagVec : Tag → DField K n × DField K n
  | .plain => (0, 1)
  | .notched => (var K (.lam .notched) - var K (.lam .plain), 0)

/-- The element `P_γ` of a tagged arc: `P_{α(i,j)} = ⟨w_i, w_{i + d(i,j)}⟩`, `P_{ρ^+_i} = p_i` and
`P_{ρ^-_i} = (λ - λ̄) q_i`. -/
@[cluster_algebras "def_D_field"]
noncomputable def arcValue : TaggedArc n → DField K n
  | .ordinary i j _ => bracket (liftVec K (i : ℤ)) (liftVec K ((i : ℤ) + cdist i j))
  | .radius .plain i => var K (.p i)
  | .radius .notched i => (var K (.lam .plain) - var K (.lam .notched)) * var K (.q i)

/-- The element `P_δ` of a row symbol: `P_γ` for a tagged arc, `P_{β_i} = ⟨w_i, w_{i+1}⟩`, and
`P_λ = λ`, `P_λ̄ = λ̄`. -/
@[cluster_algebras "def_D_field"]
noncomputable def rowValue : DRow n → DField K n
  | .arc γ => arcValue K γ
  | .boundary i => bracket (liftVec K (i : ℤ)) (liftVec K ((i : ℤ) + 1))
  | .lam τ => var K (.lam τ)

/-- The element `P_s` of a symbol: `P_γ`, `P_{β_i}`, and `P_{L_i} = P_{ρ^+_i} P_{ρ^-_i}`; for
integers `u < v ≤ u + n`, `P[u, v] = P_{s(u,v)}` is `segValue K (seg u v)`. -/
@[cluster_algebras "def_D_field"]
noncomputable def segValue : DSeg n → DField K n
  | .arc γ => arcValue K γ
  | .boundary i => rowValue K (.boundary i)
  | .loop i => arcValue K (.radius .plain i) * arcValue K (.radius .notched i)

/-! ### Elementary facts on indeterminates, residues and lifted vectors -/

omit [NeZero n] in
/-- An indeterminate of `F_n` is nonzero. -/
private theorem var_ne_zero (v : DVar n) : var K v ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (DVar n) K) (DField K n))).2
    (X_ne_zero v)

/-- The sheet of `u + m n` is `η(u) + m`. -/
private theorem sheet_add_mul (u m : ℤ) : sheet n (u + m * n) = sheet n u + m :=
  Int.add_mul_ediv_right u m (Int.natCast_ne_zero.2 (NeZero.ne n))

omit [NeZero n] in
/-- The sheet of a vertex is `0`. -/
private theorem sheet_fin (i : Fin n) : sheet n (i : ℤ) = 0 :=
  Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast i.isLt)

/-- `u = ū + η(u) n`. -/
private theorem vtx_add_sheet (u : ℤ) : ((vtx u : Fin n) : ℤ) + sheet n u * n = u := by
  rw [vtx_val]
  unfold sheet
  have := Int.emod_add_mul_ediv u n
  linarith

/-- `w_{u + m n} = A^m w_u`. -/
private theorem liftVec_add_mul (u m : ℤ) :
    liftVec K (n := n) (u + m * n) =
      (var K (.lam .notched) ^ m * (liftVec K u).1, var K (.lam .plain) ^ m * (liftVec K u).2) := by
  simp only [liftVec, sheet_add_mul, vtx_add_mul, zpow_add₀ (var_ne_zero K _)]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> ring

/-- `w_i = (p_i, q_i)` for a vertex `i`. -/
private theorem liftVec_fin (i : Fin n) :
    liftVec K (n := n) (i : ℤ) = (var K (.p i), var K (.q i)) := by
  simp [liftVec, sheet_fin, vtx_coe]

/-- `⟨w_{a + m n}, w_{b + m n}⟩ = (λ λ̄)^m ⟨w_a, w_b⟩`. -/
private theorem bracket_liftVec_add_mul (a b m : ℤ) :
    bracket (liftVec K (n := n) (a + m * n)) (liftVec K (b + m * n)) =
      (var K (.lam .plain) * var K (.lam .notched)) ^ m * bracket (liftVec K a) (liftVec K b) := by
  rw [liftVec_add_mul, liftVec_add_mul]
  unfold bracket
  rw [mul_zpow]
  ring

/-- The bracket of `w_ū` and `w_{ū + (v - u)}` is `P[u, v]`. -/
private theorem bracket_liftVec_vtx (hn : 3 ≤ n) {u v : ℤ} (huv : u < v) (hvu : v ≤ u + n) :
    bracket (liftVec K (n := n) ((vtx u : Fin n) : ℤ))
        (liftVec K (((vtx u : Fin n) : ℤ) + (v - u))) = segValue K (seg u v) := by
  rcases (show v - u = 1 ∨ v - u = n ∨ (2 ≤ v - u ∧ v - u ≤ n - 1) by omega) with
    h | h | ⟨h1, h2⟩
  · obtain rfl : v = u + 1 := by omega
    rw [seg_eq_boundary, add_sub_cancel_left]
    rfl
  · obtain rfl : v = u + n := by omega
    rw [seg_eq_loop (by omega), add_sub_cancel_left,
      show ((vtx u : Fin n) : ℤ) + n = (vtx u : ℤ) + 1 * n by ring, liftVec_add_mul,
      liftVec_fin]
    simp only [segValue, arcValue, bracket, zpow_one]
    ring
  · obtain ⟨hs, h', ho⟩ := seg_eq_arc (n := n) h1 h2
    rw [hs, ho]
    simp only [segValue, arcValue]
    rw [(cdist_vtx_kappa_eq_cut (n := n) huv (by omega)).1]

omit [NeZero n] in
/-- A point of `𝕜^{DVar n}` at which to evaluate. -/
private def evalPt (a b : Fin n) : DVar n → K
  | .p c => if c = a then 1 else 0
  | .q c => if c = b then 1 else 0
  | .lam τ => if τ = .plain then 1 else 0

omit [NeZero n] in
/-- The image of a polynomial with a nonzero value is nonzero. -/
private theorem algebraMap_ne_zero_of_eval {f : MvPolynomial (DVar n) K} (x : DVar n → K)
    (h : eval x f ≠ 0) : algebraMap (MvPolynomial (DVar n) K) (DField K n) f ≠ 0 := by
  intro h0
  apply h
  rw [(map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h0, map_zero]

omit [NeZero n] in
/-- `p_a q_b - q_a p_b ≠ 0` for `a ≠ b`. -/
private theorem pq_sub_ne_zero {a b : Fin n} (hab : a ≠ b) :
    var K (.p a) * var K (.q b) - var K (.q a) * var K (.p b) ≠ 0 := by
  simp only [var, ← map_mul, ← map_sub]
  refine algebraMap_ne_zero_of_eval K (evalPt K a b) ?_
  simp [evalPt, hab, Ne.symm hab]

omit [NeZero n] in
/-- `λ p_a q_b - λ̄ q_a p_b ≠ 0` for `a ≠ b`. -/
private theorem lam_pq_sub_ne_zero {a b : Fin n} (hab : a ≠ b) :
    var K (.lam .plain) * var K (.p a) * var K (.q b) -
      var K (.lam .notched) * var K (.q a) * var K (.p b) ≠ 0 := by
  simp only [var, ← map_mul, ← map_sub]
  refine algebraMap_ne_zero_of_eval K (evalPt K a b) ?_
  simp [evalPt, hab, Ne.symm hab]

omit [NeZero n] in
/-- `(λ - λ̄) q_a ≠ 0`. -/
private theorem lam_sub_mul_q_ne_zero (a : Fin n) :
    (var K (.lam .plain) - var K (.lam .notched)) * var K (.q a) ≠ 0 := by
  simp only [var, ← map_mul, ← map_sub]
  refine algebraMap_ne_zero_of_eval K (evalPt K a a) ?_
  simp [evalPt]

/-- `⟨w_i, w_v⟩ ≠ 0` for a vertex `i` and `i < v < i + n`. -/
private theorem bracket_liftVec_ne_zero (i : Fin n) {v : ℤ} (h1 : (i : ℤ) < v)
    (h2 : v < i + n) : bracket (liftVec K (n := n) (i : ℤ)) (liftVec K v) ≠ 0 := by
  have hd := vtx_add_sheet (n := n) v
  have hv0 := vtx_val (n := n) v
  have hs : sheet n v = 0 ∨ sheet n v = 1 := by
    have hi := i.isLt
    unfold sheet
    have h3 : 0 ≤ v / n := Int.ediv_nonneg (by omega) (by omega)
    have h4 : v / n < 2 := Int.ediv_lt_of_lt_mul (by omega) (by omega)
    omega
  have hne : (vtx v : Fin n) ≠ i := by
    intro he
    rw [he] at hd
    rcases hs with hs | hs <;> rw [hs] at hd <;> omega
  rw [← hd, liftVec_add_mul, liftVec_fin, liftVec_fin]
  rcases hs with hs | hs <;> rw [hs] <;> simp only [bracket, zpow_zero, zpow_one, one_mul]
  · exact pq_sub_ne_zero K (Ne.symm hne)
  · have := lam_pq_sub_ne_zero K (Ne.symm hne)
    contrapose! this
    linear_combination this

/-! ### Lifted brackets and the exchange identities -/

/-- **Lifted brackets**: for `u < v ≤ u + n`, `⟨w_u, w_v⟩ = (λ λ̄)^{η(u)} P[u, v]`. -/
@[cluster_algebras "lem_D_lift"]
theorem bracket_liftVec (hn : 3 ≤ n) {u v : ℤ} (huv : u < v) (hvu : v ≤ u + n) :
    bracket (liftVec K (n := n) u) (liftVec K v) =
      (var K (.lam .plain) * var K (.lam .notched)) ^ sheet n u * segValue K (seg u v) := by
  have hd := vtx_add_sheet (n := n) u
  have e1 : liftVec K (n := n) u = liftVec K (((vtx u : Fin n) : ℤ) + sheet n u * n) := by
    rw [hd]
  have e2 : liftVec K (n := n) v =
      liftVec K ((((vtx u : Fin n) : ℤ) + (v - u)) + sheet n u * n) := by
    congr 1
    linarith
  rw [e1, e2, bracket_liftVec_add_mul, bracket_liftVec_vtx K hn huv hvu]

/-- **Lifted brackets**: `⟨w_u, e^τ⟩ = λ_{-τ}^{η(u)} P_{ρ^τ_ū}`. -/
@[cluster_algebras "lem_D_lift"]
theorem bracket_liftVec_tagVec (u : ℤ) (τ : Tag) :
    bracket (liftVec K (n := n) u) (tagVec K τ) =
      var K (.lam (-τ)) ^ sheet n u * arcValue K (.radius τ (vtx u)) := by
  cases τ <;> simp only [bracket, liftVec, tagVec, arcValue, Tag.neg_plain, Tag.neg_notched] <;>
    ring

/-- **Lifted brackets**: `P[u + n, v + n] = P[u, v]`. -/
@[cluster_algebras "lem_D_lift"]
theorem segValue_seg_add_n (u v : ℤ) :
    segValue K (seg (u + n) (v + n) : DSeg n) = segValue K (seg u v) := by
  rw [seg_add_n]

/-- **Lifted brackets**: the elements `P_δ` of all row symbols (tagged arcs, boundary segments,
`λ`, `λ̄`) are nonzero. -/
@[cluster_algebras "lem_D_lift"]
theorem rowValue_ne_zero (hn : 3 ≤ n) (δ : DRow n) : rowValue K δ ≠ 0 := by
  rcases δ with (⟨i, j, h⟩ | ⟨_ | _, i⟩) | i | τ
  · have := cdist_lt i j
    exact bracket_liftVec_ne_zero K i (by omega) (by omega)
  · exact var_ne_zero K _
  · exact lam_sub_mul_q_ne_zero K i
  · exact bracket_liftVec_ne_zero K i (by omega) (by omega)
  · exact var_ne_zero K _

/-- **Lifted brackets**: the elements `P_s` of all symbols are nonzero. -/
@[cluster_algebras "lem_D_lift"]
theorem segValue_ne_zero (hn : 3 ≤ n) (s : DSeg n) : segValue K s ≠ 0 := by
  rcases s with γ | i | i
  · exact rowValue_ne_zero K hn (.arc γ)
  · exact rowValue_ne_zero K hn (.boundary i)
  · exact mul_ne_zero (rowValue_ne_zero K hn (.arc (.radius .plain i)))
      (rowValue_ne_zero K hn (.arc (.radius .notched i)))

/-- `P[u, v] = λ^{κ(u,v)} p_ū q_v̄ - λ̄^{κ(u,v)} q_ū p_v̄` for `u < v ≤ u + n`. -/
private theorem segValue_seg_eq (hn : 3 ≤ n) {u v : ℤ} (huv : u < v) (hvu : v ≤ u + n) :
    segValue K (seg u v : DSeg n) =
      var K (.lam .plain) ^ kappa n u v * var K (.p (vtx u)) * var K (.q (vtx v)) -
        var K (.lam .notched) ^ kappa n u v * var K (.q (vtx u)) * var K (.p (vtx v)) := by
  have hb := bracket_liftVec K hn huv hvu
  have hl := var_ne_zero K (n := n) (.lam .plain)
  have hl' := var_ne_zero K (n := n) (.lam .notched)
  have hs : sheet n v = sheet n u + kappa n u v := by unfold kappa; ring
  simp only [bracket, liftVec, hs, zpow_add₀ hl, zpow_add₀ hl'] at hb
  refine mul_left_cancel₀ (zpow_ne_zero (sheet n u) (mul_ne_zero hl hl')) ?_
  rw [← hb, mul_zpow]
  ring

/-- **The exchange identities** (a): for integers `x < y < z < w` with `w - x ≤ n`,
`P[x,z] P[y,w] = (λ λ̄)^{κ(y,z)} P[x,y] P[z,w] + P[x,w] P[y,z]`. -/
@[cluster_algebras "lem_D_identities"]
theorem segValue_mul_segValue (hn : 3 ≤ n) {x y z w : ℤ} (hxy : x < y) (hyz : y < z)
    (hzw : z < w) (hwx : w - x ≤ n) :
    segValue K (seg x z : DSeg n) * segValue K (seg y w) =
      (var K (.lam .plain) * var K (.lam .notched)) ^ kappa n y z * segValue K (seg x y) *
          segValue K (seg z w) +
        segValue K (seg x w) * segValue K (seg y z) := by
  have hl := var_ne_zero K (n := n) (.lam .plain)
  have hl' := var_ne_zero K (n := n) (.lam .notched)
  rw [segValue_seg_eq K hn hxy (by omega), segValue_seg_eq K hn hyz (by omega),
    segValue_seg_eq K hn hzw (by omega), segValue_seg_eq K hn (hxy.trans hyz) (by omega),
    segValue_seg_eq K hn (hyz.trans hzw) (by omega),
    segValue_seg_eq K hn ((hxy.trans hyz).trans hzw) (by omega),
    kappa_add (n := n) x y w, kappa_add (n := n) y z w, kappa_add (n := n) x y z]
  simp only [zpow_add₀ hl, zpow_add₀ hl', mul_zpow]
  ring

/-- **The exchange identities** (b): for integers `x < y < z` with `z - x ≤ n - 1` and
`P^τ_u = P_{ρ^τ_ū}`, `P[x,z] P^τ_y = λ_{-τ}^{κ(y,z)} P[x,y] P^τ_z + λ_τ^{κ(x,y)} P^τ_x P[y,z]`. -/
@[cluster_algebras "lem_D_identities"]
theorem segValue_mul_arcValue_radius (hn : 3 ≤ n) (τ : Tag) {x y z : ℤ} (hxy : x < y)
    (hyz : y < z) (hzx : z - x ≤ n - 1) :
    segValue K (seg x z : DSeg n) * arcValue K (.radius τ (vtx y)) =
      var K (.lam (-τ)) ^ kappa n y z * segValue K (seg x y) * arcValue K (.radius τ (vtx z)) +
        var K (.lam τ) ^ kappa n x y * arcValue K (.radius τ (vtx x)) *
          segValue K (seg y z) := by
  have hl := var_ne_zero K (n := n) (.lam .plain)
  have hl' := var_ne_zero K (n := n) (.lam .notched)
  rw [segValue_seg_eq K hn hxy (by omega), segValue_seg_eq K hn hyz (by omega),
    segValue_seg_eq K hn (hxy.trans hyz) (by omega), kappa_add (n := n) x y z]
  cases τ <;> simp only [arcValue, Tag.neg_plain, Tag.neg_notched, zpow_add₀ hl,
    zpow_add₀ hl'] <;> ring

/-- **The exchange identities** (c): for integers `u < v < u + n`,
`P^τ_u P^{-τ}_v = λ_τ^{κ(v,u+n)} P[u,v] + λ_{-τ}^{κ(u,v)} P[v,u+n]`. -/
@[cluster_algebras "lem_D_identities"]
theorem arcValue_radius_mul_arcValue_radius (hn : 3 ≤ n) (τ : Tag) {u v : ℤ} (huv : u < v)
    (hvu : v < u + n) :
    arcValue K (n := n) (.radius τ (vtx u)) * arcValue K (.radius (-τ) (vtx v)) =
      var K (.lam τ) ^ kappa n v (u + n) * segValue K (seg u v) +
        var K (.lam (-τ)) ^ kappa n u v * segValue K (seg v (u + n)) := by
  obtain ⟨-, -, hk⟩ := cdist_vtx_kappa_eq_cut (n := n) huv hvu
  have hv := vtx_add_mul (n := n) u 1
  rw [one_mul] at hv
  rw [segValue_seg_eq K hn huv hvu.le, segValue_seg_eq K hn hvu (by omega), hv,
    show kappa n v (u + n) = 1 - kappa n u v by omega]
  rcases kappa_eq_zero_or_one (n := n) huv.le (by omega) with h | h <;> rw [h] <;>
    cases τ <;> simp only [arcValue, Tag.neg_plain, Tag.neg_notched, zpow_zero, zpow_one,
      sub_zero, sub_self] <;> ring

/-- The residue of an integer of `[0, n)` is itself. -/
private theorem vtx_val_of_lt {u : ℤ} (h0 : 0 ≤ u) (h1 : u < n) : ((vtx u : Fin n) : ℤ) = u := by
  rw [vtx_val, Int.emod_eq_of_lt h0 h1]

/-- The residue of `u` is `u - m n` when that lies in `[0, n)`. -/
private theorem vtx_val_eq {u : ℤ} (m : ℤ) (h0 : 0 ≤ u - m * n) (h1 : u - m * n < n) :
    ((vtx u : Fin n) : ℤ) = u - m * n := by
  rw [show u = (u - m * n) + m * n by ring, vtx_add_mul, vtx_val_of_lt h0 h1]
  ring

/-- The sheet of `u ∈ [0, 2n)`. -/
private theorem sheet_eq {u : ℤ} (h0 : 0 ≤ u) (h1 : u < 2 * n) :
    sheet n u = if u < n then 0 else 1 := by
  unfold sheet
  split_ifs with h
  · exact Int.ediv_eq_zero_of_lt h0 h
  · rw [show u = (u - n) + 1 * n by ring, Int.add_mul_ediv_right _ _
      (Int.natCast_ne_zero.2 (NeZero.ne n)), Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    rfl

/-- Residues are compatible with translation. -/
private theorem vtx_vtx_add (u m : ℤ) :
    (vtx (((vtx u : Fin n) : ℤ) + m) : Fin n) = vtx (u + m) := by
  have := vtx_add_sheet (n := n) u
  rw [show ((vtx u : Fin n) : ℤ) + m = (u + m) + (-sheet n u) * n by linarith, vtx_add_mul]

/-- The gap of an element of `R`: `1 ≤ g_R(a) ≤ n`, `a + g_R(a) ∈ R` and no `a + t` with
`0 < t < g_R(a)` lies in `R`. -/
private theorem gap_spec' {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) :
    1 ≤ gap R a ∧ gap R a ≤ n ∧ (vtx ((a : ℤ) + (gap R a : ℤ)) : Fin n) ∈ R ∧
      ∀ t : ℕ, 0 < t → t < gap R a → (vtx ((a : ℤ) + (t : ℤ)) : Fin n) ∉ R := by
  have hpos := NeZero.pos n
  have hmem : n - 1 ∈ gapCandidates R a := by
    simp only [gapCandidates, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [show ((a : ℤ) + ((n - 1 + 1 : ℕ) : ℤ)) = a + 1 * n by
      rw [Nat.sub_add_cancel hpos]; ring, vtx_add_mul, vtx_coe]
    exact ha
  have hne : (gapCandidates R a).Nonempty := ⟨_, hmem⟩
  rw [gap, dif_pos hne]
  have hle : ∀ t ∈ gapCandidates R a, (gapCandidates R a).min' hne ≤ t :=
    fun t ht => Finset.min'_le _ _ ht
  set m := (gapCandidates R a).min' hne with hmdef
  have hm : m ∈ gapCandidates R a := Finset.min'_mem _ hne
  simp only [gapCandidates, Finset.mem_filter, Finset.mem_range] at hm
  refine ⟨by omega, by omega, hm.2, fun t ht0 ht hR => ?_⟩
  have : t - 1 ∈ gapCandidates R a := by
    simp only [gapCandidates, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rwa [Nat.sub_add_cancel ht0]
  have := hle _ this
  omega

/-- Distinct vertices are joined by a run of length in `(0, n)`. -/
private theorem exists_vtx_eq_of_ne {a b : Fin n} (h : a ≠ b) :
    ∃ t : ℕ, 0 < t ∧ t < n ∧ (vtx ((a : ℤ) + t) : Fin n) = b := by
  have hv := Fin.val_ne_of_ne h
  have := a.isLt
  have := b.isLt
  by_cases hab : (a : ℕ) ≤ b
  · refine ⟨b - a, by omega, by omega, Fin.ext ?_⟩
    have := vtx_val_eq (n := n) (u := (a : ℤ) + ((b - a : ℕ) : ℤ)) 0 (by omega) (by omega)
    omega
  · refine ⟨b + n - a, by omega, by omega, Fin.ext ?_⟩
    have := vtx_val_eq (n := n) (u := (a : ℤ) + ((b + n - a : ℕ) : ℤ)) 1 (by omega) (by omega)
    omega

private theorem radiusSet_of_isKindP {T : Finset (TaggedArc n)} {τ : Tag} {R : Finset (Fin n)}
    (h : IsKindP T τ R) : radiusSet T = R := by
  ext b
  simp only [radiusSet, Finset.mem_filter, Finset.mem_univ, true_and, h.2.1]
  cases τ <;> simp

private theorem radiusSet_of_isDigonKind {T : Finset (TaggedArc n)} {a : Fin n}
    (h : IsDigonKind T a) : radiusSet T = {a} := by
  ext b
  simp [radiusSet, h.1]

/-! ### Monomials in the elements `P_δ` -/

/-- The monomial `∏_δ P_δ^{f(δ)}` of an exponent vector `f`. -/
private noncomputable def rowProd (f : DRow n → ℤ) : DField K n :=
  ∏ δ, rowValue K δ ^ f δ

private theorem rowProd_add (hn : 3 ≤ n) (f g : DRow n → ℤ) :
    rowProd K (f + g) = rowProd K f * rowProd K g := by
  simp only [rowProd, Pi.add_apply, zpow_add₀ (rowValue_ne_zero K hn _),
    Finset.prod_mul_distrib]

private theorem rowProd_smul (c : ℤ) (f : DRow n → ℤ) :
    rowProd K (c • f) = rowProd K f ^ c := by
  simp only [rowProd, Pi.smul_apply, smul_eq_mul, mul_comm c, zpow_mul, Finset.prod_zpow]

private theorem rowProd_rowVec (δ₀ : DRow n) : rowProd K (rowVec δ₀) = rowValue K δ₀ := by
  simp only [rowProd, rowVec]
  simp

private theorem rowProd_segVec (s : DSeg n) : rowProd K (segVec s) = segValue K s := by
  have e : ∀ δ, rowValue K δ ^ (if δ ∈ s.rows then (1 : ℤ) else 0) =
      if δ ∈ s.rows then rowValue K δ else 1 := fun δ => by
    split_ifs <;> simp
  simp only [rowProd, segVec, e]
  rw [Finset.prod_ite_mem, Finset.univ_inter]
  rcases s with γ | i | i
  · simp [DSeg.rows, rowValue, segValue]
  · simp [DSeg.rows, segValue]
  · rw [DSeg.rows, Finset.prod_pair (by simp)]
    rfl

/-- If `v = u₁ - u₂` with `u₁, u₂ ≥ 0` of disjoint supports, the two exchange monomials of `v` are
the monomials of `u₁` and `u₂`. -/
private theorem prod_filter_eq_rowProd {v u₁ u₂ : DRow n → ℤ} (hv : ∀ δ, v δ = u₁ δ - u₂ δ)
    (h₁ : ∀ δ, 0 ≤ u₁ δ) (h₂ : ∀ δ, 0 ≤ u₂ δ) (hd : ∀ δ, u₁ δ = 0 ∨ u₂ δ = 0) :
    (∏ δ ∈ Finset.univ.filter (fun δ => 0 < v δ), rowValue K δ ^ v δ) = rowProd K u₁ ∧
      (∏ δ ∈ Finset.univ.filter (fun δ => v δ < 0), rowValue K δ ^ (-v δ)) = rowProd K u₂ := by
  constructor
  · rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun δ _ => ?_
    have := h₁ δ
    have := h₂ δ
    rcases hd δ with h | h
    · rw [if_neg (by rw [hv, h]; omega), h, zpow_zero]
    · rw [hv, h, sub_zero]
      split_ifs with hp
      · rfl
      · rw [show u₁ δ = 0 by omega, zpow_zero]
  · rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun δ _ => ?_
    have := h₁ δ
    have := h₂ δ
    rcases hd δ with h | h
    · rw [hv, h, zero_sub, neg_neg]
      split_ifs with hp
      · rfl
      · rw [show u₂ δ = 0 by omega, zpow_zero]
    · rw [if_neg (by rw [hv, h]; omega), h, zpow_zero]

omit [NeZero n] in
private theorem segVec_nonneg (s : DSeg n) (δ : DRow n) : 0 ≤ segVec s δ := by
  unfold segVec
  split_ifs <;> omega

omit [NeZero n] in
private theorem rowVec_nonneg (δ₀ δ : DRow n) : 0 ≤ rowVec δ₀ δ := by
  unfold rowVec
  split_ifs <;> omega

omit [NeZero n] in
private theorem segVec_eq_zero {s : DSeg n} {δ : DRow n} (h : δ ∉ s.rows) : segVec s δ = 0 := by
  simp [segVec, h]

omit [NeZero n] in
private theorem rowVec_eq_zero {δ₀ δ : DRow n} (h : δ ≠ δ₀) : rowVec δ₀ δ = 0 := by
  simp [rowVec, h]

omit [NeZero n] in
private theorem lam_notMem_rows (τ : Tag) (s : DSeg n) : DRow.lam τ ∉ s.rows := by
  rcases s with _ | _ | _ <;> simp [DSeg.rows]

/-- Distinct lifts of a residue are at distance at least `n`. -/
private theorem vtx_ne_of_lt {p q : ℤ} (h1 : p < q) (h2 : q < p + n) :
    (vtx p : Fin n) ≠ vtx q := by
  intro h
  have hp := vtx_add_sheet (n := n) p
  have hq := vtx_add_sheet (n := n) q
  rw [h] at hp
  have : (sheet n q - sheet n p) * n = q - p := by linarith
  rcases le_or_gt (sheet n q - sheet n p) 0 with h3 | h3 <;> nlinarith

/-- The rows of `s(u, v)` for `u < v < u + n`: `β_ū` or the ordinary arc `α(ū, v̄)`. -/
private theorem rows_seg_of_lt {u v : ℤ} (h1 : u < v) (h2 : v < u + n) {δ : DRow n}
    (h : δ ∈ (seg u v : DSeg n).rows) :
    (v = u + 1 ∧ δ = .boundary (vtx u)) ∨ ∃ hc, δ = .arc (.ordinary (vtx u) (vtx v) hc) := by
  by_cases h3 : v = u + 1
  · subst h3
    rw [seg_eq_boundary] at h
    simp only [DSeg.rows, Finset.mem_singleton] at h
    exact Or.inl ⟨rfl, h⟩
  · obtain ⟨hs, hc, ho⟩ := seg_eq_arc (n := n) (u := u) (v := v) (by omega) (by omega)
    rw [hs, ho] at h
    simp only [DSeg.rows, Finset.mem_singleton] at h
    exact Or.inr ⟨hc, h⟩

/-- The rows of `s(u, u + n)`: the two radii at `ū`. -/
private theorem rows_seg_loop (hn : 3 ≤ n) {u v : ℤ} (h : v = u + n) {δ : DRow n}
    (hδ : δ ∈ (seg u v : DSeg n).rows) : ∃ τ, δ = .arc (.radius τ (vtx u)) := by
  subst h
  rw [seg_eq_loop (by omega)] at hδ
  simp only [DSeg.rows, Finset.mem_insert, Finset.mem_singleton] at hδ
  rcases hδ with h | h <;> exact ⟨_, h⟩

/-- A radius is not a row of a segment `s(u, v)` with `u < v < u + n`. -/
private theorem radius_notMem_rows_seg {u v : ℤ} (h1 : u < v) (h2 : v < u + n) (τ : Tag)
    (b : Fin n) : DRow.arc (.radius τ b) ∉ (seg u v : DSeg n).rows := by
  intro h
  rcases rows_seg_of_lt h1 h2 h with ⟨-, h⟩ | ⟨_, h⟩ <;> cases h

/-- **Rows of different segments are different**: segments `s(u, v)`, `s(u', v')` of integers
`u < v ≤ u + n`, `u' < v' ≤ u' + n` whose ends have different residues share no row. -/
private theorem rows_seg_disjoint (hn : 3 ≤ n) {u v u' v' : ℤ} (h1 : u < v) (h2 : v ≤ u + n)
    (h1' : u' < v') (h2' : v' ≤ u' + n)
    (hne : (vtx u : Fin n) ≠ vtx u' ∨ (vtx v : Fin n) ≠ vtx v') {δ : DRow n}
    (h : δ ∈ (seg u v : DSeg n).rows) : δ ∉ (seg u' v' : DSeg n).rows := by
  intro h'
  rcases lt_or_eq_of_le h2 with h2 | h2 <;> rcases lt_or_eq_of_le h2' with h2' | h2'
  · rcases rows_seg_of_lt h1 h2 h with ⟨e1, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases rows_seg_of_lt h1' h2' h' with ⟨e2, e3⟩ | ⟨_, e3⟩
    · simp only [DRow.boundary.injEq] at e3
      rcases hne with hne | hne
      · exact hne e3
      · apply hne
        rw [e1, e2, ← vtx_vtx_add, e3, vtx_vtx_add]
    · simp only [reduceCtorEq] at e3
    · simp only [reduceCtorEq] at e3
    · simp only [DRow.arc.injEq, TaggedArc.ordinary.injEq] at e3
      rcases hne with hne | hne
      · exact hne e3.1
      · exact hne e3.2
  · obtain ⟨τ, rfl⟩ := rows_seg_loop hn h2' h'
    exact radius_notMem_rows_seg h1 h2 _ _ h
  · obtain ⟨τ, rfl⟩ := rows_seg_loop hn h2 h
    exact radius_notMem_rows_seg h1' h2' _ _ h'
  · obtain ⟨τ, rfl⟩ := rows_seg_loop hn h2 h
    obtain ⟨σ, e⟩ := rows_seg_loop hn h2' h'
    simp only [DRow.arc.injEq, TaggedArc.radius.injEq] at e
    rcases hne with hne | hne
    · exact hne e.2
    · apply hne
      rw [h2, h2', show u + (n : ℤ) = u + 1 * n by ring, show u' + (n : ℤ) = u' + 1 * n by ring,
        vtx_add_mul, vtx_add_mul]
      exact e.2

/-- `P_{s(u,v)} = P_{α(ū, v̄)}` for `2 ≤ v - u ≤ n - 1`. -/
private theorem arcValue_ordArc {u v : ℤ} (h₁ : 2 ≤ v - u) (h₂ : v - u ≤ n - 1) :
    arcValue K (ordArc u v : TaggedArc n) = segValue K (seg u v) := by
  rw [(seg_eq_arc (n := n) h₁ h₂).1]
  rfl

/-- `κ(u, v) ≥ 0` for `u ≤ v ≤ u + n`. -/
private theorem kappa_nonneg {u v : ℤ} (h1 : u ≤ v) (h2 : v - u ≤ n) : 0 ≤ kappa n u v := by
  rcases kappa_eq_zero_or_one (n := n) h1 h2 with h | h <;> omega

/-! ### The exchange relations of the five kinds of flips -/

/-- The rows of `s(y, z)`, `s(x, w)` are not rows of `s(x, y)`, `s(z, w)`, `λ`, `λ̄`: the two
halves of the column of the flip of a chord with parent `(x, z, w)` have disjoint supports. -/
private theorem disjoint_supports_col_right (hn : 3 ≤ n) {x y z w : ℤ} (hxy : x < y) (hyz : y < z)
    (hzw : z < w) (hwx : w - x ≤ n) (δ : DRow n) :
    ((segVec (seg y z : DSeg n) + segVec (seg x w)) : DRow n → ℤ) δ = 0 ∨
      ((segVec (seg x y : DSeg n) + segVec (seg z w) +
        kappa n y z • (rowVec (.lam .plain) + rowVec (.lam .notched))) : DRow n → ℤ) δ = 0 := by
  refine or_iff_not_imp_left.2 fun h0 => ?_
  have hmem : δ ∈ (seg y z : DSeg n).rows ∨ δ ∈ (seg x w : DSeg n).rows := by
    by_contra hc
    push Not at hc
    exact h0 (by simp only [Pi.add_apply, segVec_eq_zero hc.1, segVec_eq_zero hc.2, add_zero])
  have hl : ∀ τ, δ ≠ .lam τ := fun τ he => by
    subst he
    rcases hmem with h | h <;> exact lam_notMem_rows τ _ h
  have e1 : δ ∉ (seg x y : DSeg n).rows := by
    rcases hmem with h | h
    · exact rows_seg_disjoint hn hyz (by omega) hxy (by omega)
        (Or.inl (vtx_ne_of_lt hxy (by omega)).symm) h
    · exact rows_seg_disjoint hn (by omega) (by omega) hxy (by omega)
        (Or.inr (vtx_ne_of_lt (by omega) (by omega)).symm) h
  have e2 : δ ∉ (seg z w : DSeg n).rows := by
    rcases hmem with h | h
    · exact rows_seg_disjoint hn hyz (by omega) hzw (by omega)
        (Or.inl (vtx_ne_of_lt hyz (by omega))) h
    · exact rows_seg_disjoint hn (by omega) (by omega) hzw (by omega)
        (Or.inl (vtx_ne_of_lt (by omega) (by omega))) h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, segVec_eq_zero e1,
    segVec_eq_zero e2, rowVec_eq_zero (hl _), add_zero, mul_zero]

/-- The exchange relation of a flip of a chord `(x, z)` of a sector run, with parent `(x, z, w)`
and apex `y`. -/
private theorem exchange_of_col_right (hn : 3 ≤ n) {T : Finset (TaggedArc n)} {x y z w : ℤ}
    (hxy : x < y) (hyz : y < z) (hzw : z < w) (hwx : w - x ≤ n) (h2xz : 2 ≤ z - x)
    (hxzn : z - x ≤ n - 1) (h2yw : 2 ≤ w - y) (hywn : w - y ≤ n - 1)
    (hcol : (fun δ => dMatrix T δ (ordArc x z)) =
      segVec (seg y z) + segVec (seg x w) - segVec (seg x y) - segVec (seg z w) -
        kappa n y z • (rowVec (.lam .plain) + rowVec (.lam .notched))) :
    arcValue K (ordArc x z) * arcValue K (ordArc y w) =
      (∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ (ordArc x z)),
          rowValue K δ ^ dMatrix T δ (ordArc x z)) +
        ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ (ordArc x z) < 0),
          rowValue K δ ^ (-dMatrix T δ (ordArc x z)) := by
  have hk := kappa_nonneg (n := n) hyz.le (by omega : z - y ≤ n)
  set u₁ : DRow n → ℤ := segVec (seg y z) + segVec (seg x w)
  set u₂ : DRow n → ℤ := segVec (seg x y) + segVec (seg z w) +
    kappa n y z • (rowVec (.lam .plain) + rowVec (.lam .notched))
  have hv : ∀ δ, dMatrix T δ (ordArc x z) = u₁ δ - u₂ δ := fun δ => by
    have := congrFun hcol δ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [u₁, u₂, Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
    ring
  have h₁ : ∀ δ, 0 ≤ u₁ δ := fun δ => add_nonneg (segVec_nonneg _ _) (segVec_nonneg _ _)
  have h₂ : ∀ δ, 0 ≤ u₂ δ := fun δ => add_nonneg (add_nonneg (segVec_nonneg _ _)
    (segVec_nonneg _ _)) (mul_nonneg hk (add_nonneg (rowVec_nonneg _ _) (rowVec_nonneg _ _)))
  have hd : ∀ δ, u₁ δ = 0 ∨ u₂ δ = 0 := disjoint_supports_col_right hn hxy hyz hzw hwx
  obtain ⟨hpos, hneg⟩ := prod_filter_eq_rowProd K hv h₁ h₂ hd
  rw [hpos, hneg]
  simp only [u₁, u₂, rowProd_add K hn, rowProd_smul, rowProd_segVec, rowProd_rowVec]
  rw [arcValue_ordArc K h2xz hxzn, arcValue_ordArc K h2yw hywn,
    segValue_mul_segValue K hn hxy hyz hzw hwx]
  simp only [rowValue]
  ring

/-- The rows of `s(x, y)`, `s(x', z)` are not rows of `s(y, z)`, `s(x', x)`, `λ`, `λ̄`: the two
halves of the column of the flip of a chord with parent `(x', x, z)` have disjoint supports. -/
private theorem disjoint_supports_col_left (hn : 3 ≤ n) {x' x y z : ℤ} (hx'x : x' < x)
    (hxy : x < y) (hyz : y < z) (hzx : z - x' ≤ n) (δ : DRow n) :
    ((segVec (seg y z : DSeg n) + segVec (seg x' x) +
        kappa n x y • (rowVec (.lam .plain) + rowVec (.lam .notched))) : DRow n → ℤ) δ = 0 ∨
      ((segVec (seg x y : DSeg n) + segVec (seg x' z)) : DRow n → ℤ) δ = 0 := by
  refine or_iff_not_imp_right.2 fun h0 => ?_
  have hmem : δ ∈ (seg x y : DSeg n).rows ∨ δ ∈ (seg x' z : DSeg n).rows := by
    by_contra hc
    push Not at hc
    exact h0 (by simp only [Pi.add_apply, segVec_eq_zero hc.1, segVec_eq_zero hc.2, add_zero])
  have hl : ∀ τ, δ ≠ .lam τ := fun τ he => by
    subst he
    rcases hmem with h | h <;> exact lam_notMem_rows τ _ h
  have e1 : δ ∉ (seg y z : DSeg n).rows := by
    rcases hmem with h | h
    · exact rows_seg_disjoint hn hxy (by omega) hyz (by omega)
        (Or.inl (vtx_ne_of_lt hxy (by omega))) h
    · exact rows_seg_disjoint hn (by omega) (by omega) hyz (by omega)
        (Or.inl (vtx_ne_of_lt (by omega) (by omega))) h
  have e2 : δ ∉ (seg x' x : DSeg n).rows := by
    rcases hmem with h | h
    · exact rows_seg_disjoint hn hxy (by omega) hx'x (by omega)
        (Or.inl (vtx_ne_of_lt hx'x (by omega)).symm) h
    · exact rows_seg_disjoint hn (by omega) (by omega) hx'x (by omega)
        (Or.inr (vtx_ne_of_lt (by omega) (by omega)).symm) h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, segVec_eq_zero e1,
    segVec_eq_zero e2, rowVec_eq_zero (hl _), add_zero, mul_zero]

/-- The exchange relation of a flip of a chord `(x, z)` of a sector run, with parent `(x', x, z)`
and apex `y`. -/
private theorem exchange_of_col_left (hn : 3 ≤ n) {T : Finset (TaggedArc n)} {x' x y z : ℤ}
    (hx'x : x' < x) (hxy : x < y) (hyz : y < z) (hzx : z - x' ≤ n) (h2xz : 2 ≤ z - x)
    (hxzn : z - x ≤ n - 1) (h2x'y : 2 ≤ y - x') (hx'yn : y - x' ≤ n - 1)
    (hcol : (fun δ => dMatrix T δ (ordArc x z)) =
      segVec (seg y z) + segVec (seg x' x) - segVec (seg x y) - segVec (seg x' z) +
        kappa n x y • (rowVec (.lam .plain) + rowVec (.lam .notched))) :
    arcValue K (ordArc x z) * arcValue K (ordArc x' y) =
      (∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ (ordArc x z)),
          rowValue K δ ^ dMatrix T δ (ordArc x z)) +
        ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ (ordArc x z) < 0),
          rowValue K δ ^ (-dMatrix T δ (ordArc x z)) := by
  have hk := kappa_nonneg (n := n) hxy.le (by omega : y - x ≤ n)
  set u₁ : DRow n → ℤ := segVec (seg y z) + segVec (seg x' x) +
    kappa n x y • (rowVec (.lam .plain) + rowVec (.lam .notched))
  set u₂ : DRow n → ℤ := segVec (seg x y) + segVec (seg x' z)
  have hv : ∀ δ, dMatrix T δ (ordArc x z) = u₁ δ - u₂ δ := fun δ => by
    have := congrFun hcol δ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [u₁, u₂, Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
    ring
  have h₁ : ∀ δ, 0 ≤ u₁ δ := fun δ => add_nonneg (add_nonneg (segVec_nonneg _ _)
    (segVec_nonneg _ _)) (mul_nonneg hk (add_nonneg (rowVec_nonneg _ _) (rowVec_nonneg _ _)))
  have h₂ : ∀ δ, 0 ≤ u₂ δ := fun δ => add_nonneg (segVec_nonneg _ _) (segVec_nonneg _ _)
  have hd : ∀ δ, u₁ δ = 0 ∨ u₂ δ = 0 := disjoint_supports_col_left hn hx'x hxy hyz hzx
  obtain ⟨hpos, hneg⟩ := prod_filter_eq_rowProd K hv h₁ h₂ hd
  rw [hpos, hneg]
  simp only [u₁, u₂, rowProd_add K hn, rowProd_smul, rowProd_segVec, rowProd_rowVec]
  rw [arcValue_ordArc K h2xz hxzn, arcValue_ordArc K h2x'y hx'yn, mul_comm,
    segValue_mul_segValue K hn hx'x hxy hyz hzx]
  simp only [rowValue]
  ring

/-- The rows `s(y, z)`, `ρ^τ_x̄`, `λ_τ` are not rows of `s(x, y)`, `ρ^τ_z̄`, `λ_{-τ}`: the two
halves of the column of the flip of an outer arc have disjoint supports. -/
private theorem disjoint_supports_col_outer (hn : 3 ≤ n) (τ : Tag) {x y z : ℤ} (hxy : x < y)
    (hyz : y < z) (h2xz : 2 ≤ z - x) (hxzn : z - x ≤ n - 1) {bx bz : Fin n} (hbx : vtx x = bx)
    (hbz : vtx z = bz) (δ : DRow n) :
    ((segVec (seg y z : DSeg n) + rowVec (.arc (.radius τ bx)) +
        kappa n x y • rowVec (.lam τ)) : DRow n → ℤ) δ = 0 ∨
      ((segVec (seg x y : DSeg n) + rowVec (.arc (.radius τ bz)) +
        kappa n y z • rowVec (.lam (-τ))) : DRow n → ℤ) δ = 0 := by
  have hτ : ∀ σ : Tag, σ ≠ -σ := by rintro (_ | _) <;> simp [Tag.neg_plain, Tag.neg_notched]
  have hxz : bx ≠ bz := hbx ▸ hbz ▸ vtx_ne_of_lt (by omega) (by omega)
  refine or_iff_not_imp_left.2 fun h0 => ?_
  have hmem : δ ∈ (seg y z : DSeg n).rows ∨ δ = .arc (.radius τ bx) ∨ δ = .lam τ := by
    by_contra hc
    push Not at hc
    exact h0 (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      segVec_eq_zero hc.1, rowVec_eq_zero hc.2.1, rowVec_eq_zero hc.2.2, add_zero, mul_zero])
  have e1 : δ ∉ (seg x y : DSeg n).rows := by
    rcases hmem with h | rfl | rfl
    · exact rows_seg_disjoint hn hyz (by omega) hxy (by omega)
        (Or.inl (vtx_ne_of_lt hxy (by omega)).symm) h
    · exact radius_notMem_rows_seg hxy (by omega) _ _
    · exact lam_notMem_rows _ _
  have e2 : δ ≠ .arc (.radius τ bz) := by
    rcases hmem with h | rfl | rfl
    · rintro rfl
      exact radius_notMem_rows_seg hyz (by omega) _ _ h
    · simpa using hxz
    · simp
  have e3 : δ ≠ .lam (-τ) := by
    rcases hmem with h | rfl | rfl
    · rintro rfl
      exact lam_notMem_rows _ _ h
    · simp
    · simpa using hτ τ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, segVec_eq_zero e1,
    rowVec_eq_zero e2, rowVec_eq_zero e3, add_zero, mul_zero]

/-- The exchange relation of the flip of an outer arc `α_R(a) = s(x, z)` with apex `y`, whose
replacement is the radius `ρ^τ_ȳ`. -/
private theorem exchange_of_col_outer (hn : 3 ≤ n) {T : Finset (TaggedArc n)} (τ : Tag)
    {x y z : ℤ} (hxy : x < y) (hyz : y < z) (h2xz : 2 ≤ z - x) (hxzn : z - x ≤ n - 1)
    {bx bz : Fin n} (hbx : vtx x = bx) (hbz : vtx z = bz)
    (hcol : (fun δ => dMatrix T δ (ordArc x z)) =
      segVec (seg y z) + rowVec (.arc (.radius τ bx)) - segVec (seg x y) -
        rowVec (.arc (.radius τ bz)) + kappa n x y • rowVec (.lam τ) -
        kappa n y z • rowVec (.lam (-τ))) :
    arcValue K (ordArc x z) * arcValue K (.radius τ (vtx y)) =
      (∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ (ordArc x z)),
          rowValue K δ ^ dMatrix T δ (ordArc x z)) +
        ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ (ordArc x z) < 0),
          rowValue K δ ^ (-dMatrix T δ (ordArc x z)) := by
  have hk1 := kappa_nonneg (n := n) hxy.le (by omega : y - x ≤ n)
  have hk2 := kappa_nonneg (n := n) hyz.le (by omega : z - y ≤ n)
  set u₁ : DRow n → ℤ := segVec (seg y z) + rowVec (.arc (.radius τ bx)) +
    kappa n x y • rowVec (.lam τ)
  set u₂ : DRow n → ℤ := segVec (seg x y) + rowVec (.arc (.radius τ bz)) +
    kappa n y z • rowVec (.lam (-τ))
  have hv : ∀ δ, dMatrix T δ (ordArc x z) = u₁ δ - u₂ δ := fun δ => by
    have := congrFun hcol δ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [u₁, u₂, Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
    ring
  have h₁ : ∀ δ, 0 ≤ u₁ δ := fun δ => add_nonneg (add_nonneg (segVec_nonneg _ _)
    (rowVec_nonneg _ _)) (mul_nonneg hk1 (rowVec_nonneg _ _))
  have h₂ : ∀ δ, 0 ≤ u₂ δ := fun δ => add_nonneg (add_nonneg (segVec_nonneg _ _)
    (rowVec_nonneg _ _)) (mul_nonneg hk2 (rowVec_nonneg _ _))
  have hd : ∀ δ, u₁ δ = 0 ∨ u₂ δ = 0 :=
    disjoint_supports_col_outer hn τ hxy hyz h2xz hxzn hbx hbz
  obtain ⟨hpos, hneg⟩ := prod_filter_eq_rowProd K hv h₁ h₂ hd
  rw [hpos, hneg]
  simp only [u₁, u₂, rowProd_add K hn, rowProd_smul, rowProd_segVec, rowProd_rowVec]
  rw [arcValue_ordArc K h2xz hxzn, segValue_mul_arcValue_radius K hn τ hxy hyz hxzn, hbx, hbz]
  simp only [rowValue]
  ring

/-- The rows `s(x, y)`, `ρ^τ_z̄`, `λ_{-τ}` are not rows of `s(y, z)`, `ρ^τ_x̄`, `λ_τ`: the two
halves of the column of the flip of a radius with neighbours `x̄`, `z̄` have disjoint supports. -/
private theorem disjoint_supports_col_radius (hn : 3 ≤ n) (τ : Tag) {x y z : ℤ} (hxy : x < y)
    (hyz : y < z) (h2xz : 2 ≤ z - x) (hxzn : z - x ≤ n - 1) {bx bz : Fin n} (hbx : vtx x = bx)
    (hbz : vtx z = bz) (δ : DRow n) :
    ((segVec (seg x y : DSeg n) + rowVec (.arc (.radius τ bz)) +
        kappa n y z • rowVec (.lam (-τ))) : DRow n → ℤ) δ = 0 ∨
      ((segVec (seg y z : DSeg n) + rowVec (.arc (.radius τ bx)) +
        kappa n x y • rowVec (.lam τ)) : DRow n → ℤ) δ = 0 := by
  have hτ : ∀ σ : Tag, σ ≠ -σ := by rintro (_ | _) <;> simp [Tag.neg_plain, Tag.neg_notched]
  have hxz : bx ≠ bz := hbx ▸ hbz ▸ vtx_ne_of_lt (by omega) (by omega)
  refine or_iff_not_imp_left.2 fun h0 => ?_
  have hmem : δ ∈ (seg x y : DSeg n).rows ∨ δ = .arc (.radius τ bz) ∨ δ = .lam (-τ) := by
    by_contra hc
    push Not at hc
    exact h0 (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      segVec_eq_zero hc.1, rowVec_eq_zero hc.2.1, rowVec_eq_zero hc.2.2, add_zero, mul_zero])
  have e1 : δ ∉ (seg y z : DSeg n).rows := by
    rcases hmem with h | rfl | rfl
    · exact rows_seg_disjoint hn hxy (by omega) hyz (by omega)
        (Or.inl (vtx_ne_of_lt hxy (by omega))) h
    · exact radius_notMem_rows_seg hyz (by omega) _ _
    · exact lam_notMem_rows _ _
  have e2 : δ ≠ .arc (.radius τ bx) := by
    rcases hmem with h | rfl | rfl
    · rintro rfl
      exact radius_notMem_rows_seg hxy (by omega) _ _ h
    · simpa using hxz.symm
    · simp
  have e3 : δ ≠ .lam τ := by
    rcases hmem with h | rfl | rfl
    · rintro rfl
      exact lam_notMem_rows _ _ h
    · simp
    · simpa using (hτ τ).symm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, segVec_eq_zero e1,
    rowVec_eq_zero e2, rowVec_eq_zero e3, add_zero, mul_zero]

/-- The exchange relation of the flip of a radius `ρ^τ_ȳ` with neighbours `x̄`, `z̄` in a radius
set of at least three positions, whose replacement is `s(x, z)`. -/
private theorem exchange_of_col_radius (hn : 3 ≤ n) {T : Finset (TaggedArc n)} (τ : Tag)
    {x y z : ℤ} (hxy : x < y) (hyz : y < z) (h2xz : 2 ≤ z - x) (hxzn : z - x ≤ n - 1)
    {bx by' bz : Fin n} (hbx : vtx x = bx) (hby : vtx y = by') (hbz : vtx z = bz)
    (hcol : (fun δ => dMatrix T δ (.radius τ by')) =
      segVec (seg x y) + rowVec (.arc (.radius τ bz)) - rowVec (.arc (.radius τ bx)) -
        segVec (seg y z) - kappa n x y • rowVec (.lam τ) +
        kappa n y z • rowVec (.lam (-τ))) :
    arcValue K (.radius τ by') * arcValue K (ordArc x z) =
      (∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ (.radius τ by')),
          rowValue K δ ^ dMatrix T δ (.radius τ by')) +
        ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ (.radius τ by') < 0),
          rowValue K δ ^ (-dMatrix T δ (.radius τ by')) := by
  have hk1 := kappa_nonneg (n := n) hxy.le (by omega : y - x ≤ n)
  have hk2 := kappa_nonneg (n := n) hyz.le (by omega : z - y ≤ n)
  set u₁ : DRow n → ℤ := segVec (seg x y) + rowVec (.arc (.radius τ bz)) +
    kappa n y z • rowVec (.lam (-τ))
  set u₂ : DRow n → ℤ := segVec (seg y z) + rowVec (.arc (.radius τ bx)) +
    kappa n x y • rowVec (.lam τ)
  have hv : ∀ δ, dMatrix T δ (.radius τ by') = u₁ δ - u₂ δ := fun δ => by
    have := congrFun hcol δ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [u₁, u₂, Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
    ring
  have h₁ : ∀ δ, 0 ≤ u₁ δ := fun δ => add_nonneg (add_nonneg (segVec_nonneg _ _)
    (rowVec_nonneg _ _)) (mul_nonneg hk2 (rowVec_nonneg _ _))
  have h₂ : ∀ δ, 0 ≤ u₂ δ := fun δ => add_nonneg (add_nonneg (segVec_nonneg _ _)
    (rowVec_nonneg _ _)) (mul_nonneg hk1 (rowVec_nonneg _ _))
  have hd : ∀ δ, u₁ δ = 0 ∨ u₂ δ = 0 :=
    disjoint_supports_col_radius hn τ hxy hyz h2xz hxzn hbx hbz
  obtain ⟨hpos, hneg⟩ := prod_filter_eq_rowProd K hv h₁ h₂ hd
  rw [hpos, hneg]
  simp only [u₁, u₂, rowProd_add K hn, rowProd_smul, rowProd_segVec, rowProd_rowVec]
  rw [arcValue_ordArc K h2xz hxzn, mul_comm, ← hby,
    segValue_mul_arcValue_radius K hn τ hxy hyz hxzn, hbx, hbz]
  simp only [rowValue]
  ring

/-- The rows `s(v, u + n)`, `λ_{-τ}` are not rows of `s(u, v)`, `λ_τ`: the two halves of the column
of the flip of a radius `ρ^τ_ū` into `ρ^{-τ}_v̄` have disjoint supports. -/
private theorem disjoint_supports_col_radius_radius (hn : 3 ≤ n) (τ : Tag) {u v : ℤ} (huv : u < v)
    (hvu : v < u + n) (δ : DRow n) :
    ((segVec (seg v (u + n) : DSeg n) + kappa n u v • rowVec (.lam (-τ))) : DRow n → ℤ) δ = 0 ∨
      ((segVec (seg u v : DSeg n) + kappa n v (u + n) • rowVec (.lam τ)) : DRow n → ℤ) δ = 0 := by
  have hτ : ∀ σ : Tag, σ ≠ -σ := by rintro (_ | _) <;> simp [Tag.neg_plain, Tag.neg_notched]
  refine or_iff_not_imp_left.2 fun h0 => ?_
  have hmem : δ ∈ (seg v (u + n) : DSeg n).rows ∨ δ = .lam (-τ) := by
    by_contra hc
    push Not at hc
    exact h0 (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      segVec_eq_zero hc.1, rowVec_eq_zero hc.2, add_zero, mul_zero])
  have e1 : δ ∉ (seg u v : DSeg n).rows := by
    rcases hmem with h | rfl
    · exact rows_seg_disjoint hn hvu (by omega) huv (by omega)
        (Or.inl (vtx_ne_of_lt huv hvu).symm) h
    · exact lam_notMem_rows _ _
  have e2 : δ ≠ .lam τ := by
    rcases hmem with h | rfl
    · rintro rfl
      exact lam_notMem_rows _ _ h
    · simpa using (hτ τ).symm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, segVec_eq_zero e1,
    rowVec_eq_zero e2, add_zero, mul_zero]

/-- The exchange relation of the flip of a radius `ρ^τ_ū` whose replacement is the radius
`ρ^{-τ}_v̄`, for `u < v < u + n`. -/
private theorem exchange_of_col_radius_radius (hn : 3 ≤ n) {T : Finset (TaggedArc n)} (τ : Tag)
    {u v : ℤ} (huv : u < v) (hvu : v < u + n) {bu bv : Fin n} (hbu : vtx u = bu)
    (hbv : vtx v = bv)
    (hcol : ∀ δ, dMatrix T δ (.radius τ bu) =
      segVec (seg v (u + n)) δ - segVec (seg u v) δ - kappa n v (u + n) * rowVec (.lam τ) δ +
        kappa n u v * rowVec (.lam (-τ)) δ) :
    arcValue K (.radius τ bu) * arcValue K (.radius (-τ) bv) =
      (∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ (.radius τ bu)),
          rowValue K δ ^ dMatrix T δ (.radius τ bu)) +
        ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ (.radius τ bu) < 0),
          rowValue K δ ^ (-dMatrix T δ (.radius τ bu)) := by
  have hk1 := kappa_nonneg (n := n) huv.le (by omega : v - u ≤ n)
  have hk2 := kappa_nonneg (n := n) (by omega : v ≤ u + n) (by omega : u + n - v ≤ n)
  set u₁ : DRow n → ℤ := segVec (seg v (u + n)) + kappa n u v • rowVec (.lam (-τ))
  set u₂ : DRow n → ℤ := segVec (seg u v) + kappa n v (u + n) • rowVec (.lam τ)
  have hv : ∀ δ, dMatrix T δ (.radius τ bu) = u₁ δ - u₂ δ := fun δ => by
    simp only [u₁, u₂, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcol δ]
    ring
  have h₁ : ∀ δ, 0 ≤ u₁ δ := fun δ => add_nonneg (segVec_nonneg _ _)
    (mul_nonneg hk1 (rowVec_nonneg _ _))
  have h₂ : ∀ δ, 0 ≤ u₂ δ := fun δ => add_nonneg (segVec_nonneg _ _)
    (mul_nonneg hk2 (rowVec_nonneg _ _))
  have hd : ∀ δ, u₁ δ = 0 ∨ u₂ δ = 0 := disjoint_supports_col_radius_radius hn τ huv hvu
  obtain ⟨hpos, hneg⟩ := prod_filter_eq_rowProd K hv h₁ h₂ hd
  rw [hpos, hneg]
  simp only [u₁, u₂, rowProd_add K hn, rowProd_smul, rowProd_segVec, rowProd_rowVec]
  rw [← hbu, ← hbv, arcValue_radius_mul_arcValue_radius K hn τ huv hvu]
  simp only [rowValue]
  ring

/-- The bounds of a segment of a triangulation of a run. -/
private theorem isRunSegment_bounds {u v : ℤ} {Tc : Finset (ℤ × ℤ)} (huv : u < v)
    (hTc : ∀ c ∈ Tc, IsRunChord u v c) {p q : ℤ} (h : IsRunSegment u v Tc (p, q)) :
    u ≤ p ∧ p < q ∧ q ≤ v := by
  rcases h with h | ⟨h1, h2, h3⟩ | h
  · obtain ⟨h1, h2, h3, -⟩ := hTc _ h
    exact ⟨h1, h2, h3⟩
  · simp only at h1 h2 h3
    omega
  · simp only [Prod.mk.injEq] at h
    omega

omit [NeZero n] in
/-- A chord `(x, z)` of a run `[u, v]` with `v - u ≤ n` has `z - x ≤ n - 1`. -/
private theorem isRunChord_le {u v : ℤ} (hvu : v - u ≤ n) {c : ℤ × ℤ} (hc : IsRunChord u v c) :
    2 ≤ c.2 - c.1 ∧ c.2 - c.1 ≤ n - 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  have h6 : ¬(c.1 = u ∧ c.2 = v) := fun ⟨e1, e2⟩ => h5 (Prod.ext e1 e2)
  omega

/-- `α(ū, v̄)` only depends on the residues of `u` and `v`. -/
private theorem ordArc_congr {u v u' v' : ℤ} (hu : (vtx u : Fin n) = vtx u')
    (hv : (vtx v : Fin n) = vtx v') : (ordArc u v : TaggedArc n) = ordArc u' v' := by
  unfold ordArc
  simp only [hu, hv]

/-- The gap of an element of a radius set of at least two positions is at most `n - 1`. -/
private theorem gap_le_of_two_le_card {R : Finset (Fin n)} (hR : 2 ≤ R.card) {a : Fin n}
    (ha : a ∈ R) : gap R a ≤ n - 1 := by
  obtain ⟨g1, g2, g3, g4⟩ := gap_spec' ha
  by_contra hg
  have hgn : gap R a = n := by omega
  have : ∃ b ∈ R, b ≠ a := by
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card (show R ⊆ {a} from fun b hb => Finset.mem_singleton.2 (hcon b hb))
    simp at this
    omega
  obtain ⟨b, hb, hba⟩ := this
  obtain ⟨t, ht0, htn, hvt⟩ := exists_vtx_eq_of_ne (Ne.symm hba)
  exact g4 t ht0 (by omega) (hvt ▸ hb)

/-- The common exchange relation of the flips of chords of sector runs. -/
private theorem exchange_chord (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {a : Fin n} (ha : a ∈ radiusSet T)
    (hg : gap (radiusSet T) a ≤ n)
    (hRT : IsRunTriangulation a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a))
    (hflip : ∀ c c', IsRunFlip a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a) c c' →
      IsDFlipReplacement T (ordArc c.1 c.2) (ordArc c'.1 c'.2))
    {c : ℤ × ℤ} (hc : c ∈ sectorChords T (radiusSet T) a) {γ' : TaggedArc n}
    (h : IsDFlipReplacement T (ordArc c.1 c.2) γ') :
    arcValue K (ordArc c.1 c.2) * arcValue K γ' =
      (∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ (ordArc c.1 c.2)),
          rowValue K δ ^ dMatrix T δ (ordArc c.1 c.2)) +
        ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ (ordArc c.1 c.2) < 0),
          rowValue K δ ^ (-dMatrix T δ (ordArc c.1 c.2)) := by
  obtain ⟨x, z⟩ := c
  simp only at h ⊢
  have huniq : ∀ γ'', IsDFlipReplacement T (ordArc x z) γ'' → γ' = γ'' := fun γ'' h'' =>
    (hT.existsUnique_isDFlipReplacement hn h.2.1).unique h h''
  have hch := hRT.1 _ hc
  obtain ⟨hxz2, hxzn⟩ := isRunChord_le (n := n) (u := (a : ℤ)) (v := a + gap (radiusSet T) a)
    (by omega) hch
  obtain ⟨h1, -, h3, -, -⟩ := hch
  simp only at hxz2 hxzn h1 h3
  have h2 : 2 ≤ ((a : ℤ) + gap (radiusSet T) a) - a := by omega
  obtain ⟨y, hy, -⟩ := hRT.existsUnique_apex h2 (Or.inl hc)
  obtain ⟨⟨t1, t2, t3⟩, ⟨ht, hpar⟩, -⟩ := hRT.existsUnique_parent hc
  have hb := fun {p q : ℤ} => isRunSegment_bounds (u := (a : ℤ)) (by omega) hRT.1 (p := p) (q := q)
  have hxy := hy.1
  have hyz := hy.2.1
  simp only at hpar
  rcases hpar with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hf := (hRT.isRunFlip_right hc hy ht).1
    have hzw := ht.2.1
    have s3 := ht.2.2.2.2
    have b3 := hb s3
    obtain ⟨hyw2, hywn⟩ := isRunChord_le (n := n) (u := (a : ℤ)) (v := a + gap (radiusSet T) a)
      (by omega) hf.2.2.1
    simp only at hyw2 hywn
    rw [huniq _ (hflip _ _ hf)]
    exact exchange_of_col_right K hn hxy hyz hzw (by omega) hxz2 hxzn hyw2 hywn
      (dMatrix_col_ordArc_right hn hT ha hc hy ht)
  · have hf := (hRT.isRunFlip_left hc hy ht).1
    have hx'x := ht.1
    have s3 := ht.2.2.2.2
    have b3 := hb s3
    obtain ⟨hx'y2, hx'yn⟩ := isRunChord_le (n := n) (u := (a : ℤ)) (v := a + gap (radiusSet T) a)
      (by omega) hf.2.2.1
    simp only at hx'y2 hx'yn
    rw [huniq _ (hflip _ _ hf)]
    exact exchange_of_col_left K hn hx'x hxy hyz (by omega) hxz2 hxzn hx'y2 hx'yn
      (dMatrix_col_ordArc_left hn hT ha hc hy ht)

/-- In a radius set `{b, b'}` of two positions, `b'` is both the successor and the predecessor of
`b`, `b` is the successor of `b'`, and the gaps of `b'` and `b` add up to `n`. -/
private theorem succ_pred_gap_of_pair {b b' : Fin n} (hb'b : b' ≠ b) :
    succ {b, b'} b = b' ∧ pred {b, b'} b = b' ∧ succ {b, b'} b' = b ∧
      gap {b, b'} b' + gap {b, b'} b = n := by
  have hb : b ∈ ({b, b'} : Finset (Fin n)) := by simp
  have hb'R : b' ∈ ({b, b'} : Finset (Fin n)) := by simp
  obtain ⟨g1, g2, g3, g4⟩ := gap_spec' hb
  obtain ⟨p1, p2⟩ := succ_pred hb
  have hsb : succ {b, b'} b = b' := by
    have : succ {b, b'} b ∈ ({b, b'} : Finset (Fin n)) := g3
    rcases Finset.mem_insert.1 this with h1 | h1
    · exfalso
      obtain ⟨t, ht0, htn, hvt⟩ := exists_vtx_eq_of_ne hb'b.symm
      have hg : gap {b, b'} b = n := by
        by_contra hgn
        exact vtx_ne_of_lt (n := n) (p := b) (q := b + gap {b, b'} b) (by omega)
          (by omega) (by rw [vtx_coe]; exact h1.symm)
      exact g4 t ht0 (by omega) (hvt ▸ hb'R)
    · exact Finset.mem_singleton.1 h1
  have hpb : pred {b, b'} b = b' := by
    rcases Finset.mem_insert.1 p1 with h1 | h1
    · rw [h1] at p2
      rw [p2] at hsb
      exact absurd hsb hb'b.symm
    · exact Finset.mem_singleton.1 h1
  rw [hpb] at p2
  obtain ⟨q1, q2, q3, q4⟩ := gap_spec' hb'R
  have hgb : gap {b, b'} b < n := by
    by_contra hgn
    have : (vtx ((b : ℤ) + gap {b, b'} b) : Fin n) = b := by
      rw [show (b : ℤ) + gap {b, b'} b = b + 1 * n by omega, vtx_add_mul, vtx_coe]
    rw [← succ, hsb] at this
    exact hb'b this
  refine ⟨hsb, hpb, p2, ?_⟩
  have e1 : (vtx ((b' : ℤ) + gap {b, b'} b' + gap {b, b'} b) : Fin n) = b' := by
    rw [← vtx_vtx_add]
    change (vtx ((succ {b, b'} b' : ℤ) + gap {b, b'} b) : Fin n) = b'
    rw [p2]
    exact hsb
  by_contra hne
  rcases (show gap {b, b'} b' + gap {b, b'} b < n ∨ n < gap {b, b'} b' + gap {b, b'} b
    by omega) with hl | hl
  · exact vtx_ne_of_lt (n := n) (p := b') (q := b' + gap {b, b'} b' + gap {b, b'} b)
      (by omega) (by omega) (by rw [vtx_coe, e1])
  · apply vtx_ne_of_lt (n := n) (p := b' + n) (q := b' + gap {b, b'} b' + gap {b, b'} b)
      (by omega) (by omega)
    rw [e1, show (b' : ℤ) + n = b' + 1 * n by ring, vtx_add_mul, vtx_coe]

/-- The exchange relation of the flip of the radius `ρ^τ_b` of a radius set `{b, b'}` of two
positions, whose replacement is the radius `ρ^{-τ}_{b'}`. -/
private theorem exchange_radius_of_pair (hn : 3 ≤ n) {T : Finset (TaggedArc n)} {τ : Tag}
    {b b' : Fin n} (hK : IsKindP T τ {b, b'}) (hb'b : b' ≠ b) :
    arcValue K (.radius τ b) * arcValue K (.radius (-τ) b') =
      (∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ (.radius τ b)),
          rowValue K δ ^ dMatrix T δ (.radius τ b)) +
        ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ (.radius τ b) < 0),
          rowValue K δ ^ (-dMatrix T δ (.radius τ b)) := by
  have hb : b ∈ ({b, b'} : Finset (Fin n)) := by simp
  obtain ⟨hsb, hpb, p2, hsum⟩ := succ_pred_gap_of_pair hb'b
  obtain ⟨g1, -⟩ := gap_spec' hb
  obtain ⟨q1, -⟩ := gap_spec' (show b' ∈ ({b, b'} : Finset (Fin n)) by simp)
  have hcol := dMatrix_col_radius_of_isKindP hn hK hb
  rw [hpb, hsb] at hcol
  set x : ℤ := ((b' : Fin n) : ℤ)
  set y : ℤ := x + gap {b, b'} b'
  set z : ℤ := y + gap {b, b'} b
  have hz : z = x + n := by simp only [z, y]; omega
  have hy : (vtx y : Fin n) = b := p2
  have hzv : (vtx z : Fin n) = b' := by
    rw [hz, show x + n = x + 1 * n by ring, vtx_add_mul, vtx_coe]
  refine exchange_of_col_radius_radius K hn τ (u := y) (v := z) (by simp only [z]; omega)
    (by rw [hz]; simp only [y]; omega) hy hzv fun δ => ?_
  have := congrFun hcol δ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [this, hz, seg_add_n, kappa_add_n]
  ring

/-- The exchange relation of the flip of the radius `ρ^τ_b` of a radius set `R` of at least three
positions, whose replacement is the ordinary arc joining the neighbours of `b` in `R`. -/
private theorem exchange_radius_of_three_le (hn : 3 ≤ n) {T : Finset (TaggedArc n)} {τ : Tag}
    {R : Finset (Fin n)} (hK : IsKindP T τ R) (hR3 : 3 ≤ R.card) {b : Fin n} (hb : b ∈ R) :
    arcValue K (.radius τ b) * arcValue K (ordArc (pred R b : ℤ) (succ R b : ℤ)) =
      (∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ (.radius τ b)),
          rowValue K δ ^ dMatrix T δ (.radius τ b)) +
        ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ (.radius τ b) < 0),
          rowValue K δ ^ (-dMatrix T δ (.radius τ b)) := by
  obtain ⟨p1, p2⟩ := succ_pred hb
  obtain ⟨g1, g2, g3, g4⟩ := gap_spec' p1
  obtain ⟨g1', g2', g3', g4'⟩ := gap_spec' hb
  set x : ℤ := ((pred R b : Fin n) : ℤ)
  set y : ℤ := x + gap R (pred R b)
  set z : ℤ := y + gap R b
  have hy : (vtx y : Fin n) = b := p2
  have hz : (vtx z : Fin n) = succ R b := by
    simp only [z]
    rw [← vtx_vtx_add, hy]
    rfl
  have hzn : gap R (pred R b) + gap R b ≤ n - 1 := by
    by_contra hcon
    have hsub : R ⊆ {pred R b, b} := by
      intro c hc
      by_cases hcp : c = pred R b
      · exact hcp ▸ Finset.mem_insert_self _ _
      obtain ⟨t, ht0, htn, hvt⟩ := exists_vtx_eq_of_ne (Ne.symm hcp)
      rcases lt_trichotomy t (gap R (pred R b)) with ht | ht | ht
      · exact absurd (hvt ▸ hc) (g4 t ht0 ht)
      · subst ht
        have hcb : c = b := hvt.symm.trans hy
        rw [hcb]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exfalso
        apply g4' (t - gap R (pred R b)) (by omega) (by omega)
        have e : (vtx ((b : ℤ) + ((t - gap R (pred R b) : ℕ) : ℤ)) : Fin n) = c := by
          rw [← hvt]
          generalize hs : ((t - gap R (pred R b) : ℕ) : ℤ) = s
          have e2 : (vtx (y + s) : Fin n) = vtx (((b : Fin n) : ℤ) + s) := by
            rw [← vtx_vtx_add, hy]
          rw [← e2]
          congr 1
          simp only [y]
          rw [← hs]
          push_cast [Nat.cast_sub ht.le]
          ring
        rw [e]
        exact hc
    have := Finset.card_le_card hsub
    have := Finset.card_insert_le (pred R b) ({b} : Finset (Fin n))
    simp at this
    omega
  have hcol := dMatrix_col_radius_of_isKindP hn hK hb
  rw [ordArc_congr (u := x) (v := ((succ R b : Fin n) : ℤ)) (u' := x) (v' := z) rfl
    (by rw [vtx_coe, hz])]
  exact exchange_of_col_radius K hn τ (by simp only [y]; omega) (by simp only [z]; omega)
    (by simp only [z, y]; omega) (by simp only [z, y]; omega)
    (vtx_coe _) hy hz hcol

/-- The exchange relations of the flips of a tagged triangulation of kind `P_τ`. -/
private theorem arcValue_mul_arcValue_of_isKindP (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    {τ : Tag} {R : Finset (Fin n)} (hK : IsKindP T τ R) {γ γ' : TaggedArc n}
    (h : IsDFlipReplacement T γ γ') :
    arcValue K γ * arcValue K γ' =
      (∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ γ), rowValue K δ ^ dMatrix T δ γ) +
        ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ γ < 0),
          rowValue K δ ^ (-dMatrix T δ γ) := by
  have hT := h.1
  have hγ := h.2.1
  have huniq : ∀ γ'', IsDFlipReplacement T γ γ'' → γ' = γ'' := fun γ'' h'' =>
    (hT.existsUnique_isDFlipReplacement hn hγ).unique h h''
  have hR := radiusSet_of_isKindP hK
  rcases γ with ⟨i, j, hij⟩ | ⟨σ, b⟩
  · obtain ⟨a, ha, hcase⟩ := hK.2.2.2.2 _ hγ trivial
    rcases hcase with ⟨hg, hout⟩ | ⟨c, hc, hcγ⟩
    · rw [hout] at h huniq ⊢
      have hgn := gap_le_of_two_le_card hK.1 ha
      obtain ⟨y, hy, -⟩ := (hK.2.2.1 a ha).existsUnique_apex (by omega) (Or.inr rfl)
      rw [huniq _ (hK.isDFlipReplacement_outerArc ha hg hy).1]
      exact exchange_of_col_outer K hn τ hy.1 hy.2.1 (by omega) (by omega) (vtx_coe a) rfl
        (dMatrix_col_outerArc hn hK ha hg hy)
    · rw [← hcγ] at h ⊢
      rw [← hR] at ha hc
      exact exchange_chord K hn hT ha (gap_spec' ha).2.1 (hR ▸ hK.2.2.1 a (hR ▸ ha))
        (fun c c' hf => (hK.isDFlipReplacement_ordArc (hR ▸ ha) (hR ▸ hf)).1) hc h
  · obtain ⟨rfl, hb⟩ := (hK.2.1 σ b).1 hγ
    rcases (show R.card = 2 ∨ 3 ≤ R.card by have := hK.1; omega) with hR2 | hR3
    · obtain ⟨b', hb'b, rfl⟩ : ∃ b', b' ≠ b ∧ R = {b, b'} := by
        obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.1 hR2
        rcases Finset.mem_insert.1 hb with rfl | hb
        · exact ⟨d, hcd.symm, rfl⟩
        · rw [Finset.mem_singleton] at hb
          subst hb
          exact ⟨c, hcd, Finset.pair_comm _ _⟩
      rw [huniq _ (hK.isDFlipReplacement_radius_of_pair).1]
      exact exchange_radius_of_pair K hn hK hb'b
    · rw [huniq _ (hK.isDFlipReplacement_radius_of_three_le hR3 hb).1]
      exact exchange_radius_of_three_le K hn hK hR3 hb

/-- The exchange relations of the flips of a tagged triangulation of digon kind. -/
private theorem arcValue_mul_arcValue_of_isDigonKind (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    {a : Fin n} (hD : IsDigonKind T a) {γ γ' : TaggedArc n} (h : IsDFlipReplacement T γ γ') :
    arcValue K γ * arcValue K γ' =
      (∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ γ), rowValue K δ ^ dMatrix T δ γ) +
        ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ γ < 0),
          rowValue K δ ^ (-dMatrix T δ γ) := by
  have hT := h.1
  have hγ := h.2.1
  have huniq : ∀ γ'', IsDFlipReplacement T γ γ'' → γ' = γ'' := fun γ'' h'' =>
    (hT.existsUnique_isDFlipReplacement hn hγ).unique h h''
  have hR := radiusSet_of_isDigonKind hD
  have ha : a ∈ radiusSet T := by rw [hR]; exact Finset.mem_singleton_self a
  have hga : gap {a} a = n := by
    obtain ⟨g1, g2, g3, -⟩ := gap_spec' (Finset.mem_singleton_self a)
    by_contra hgn
    exact vtx_ne_of_lt (n := n) (p := a) (q := a + gap {a} a) (by omega) (by omega)
      (by rw [vtx_coe]; exact (Finset.mem_singleton.1 g3).symm)
  rcases γ with ⟨i, j, hij⟩ | ⟨σ, b⟩
  · obtain ⟨c, hc, hcγ⟩ := hD.2.2 _ hγ trivial
    rw [← hcγ] at h ⊢
    rw [← hR] at hc
    exact exchange_chord K hn hT ha (by rw [hR, hga]) (hR ▸ hD.2.1)
      (fun c c' hf => (hD.isDFlipReplacement_ordArc (hR ▸ hf)).1) hc h
  · have hb : b = a := (hD.1 σ b).1 hγ
    subst hb
    obtain ⟨y, hy, -⟩ := hD.2.1.existsUnique_apex (by omega) (Or.inr rfl)
    rw [huniq _ (hD.isDFlipReplacement_radius σ hy).1]
    have hcol := dMatrix_col_radius_of_isDigonKind hn hD σ hy
    have hy1 := hy.1
    have hy2 := hy.2.1
    rw [hga] at hy2
    refine exchange_of_col_radius_radius K hn σ (u := b) (v := y) hy1 hy2 (vtx_coe b) rfl
      fun δ => ?_
    have := congrFun hcol δ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this]

/-- **Exchange relations of flips**: if `γ'` replaces `γ` in the tagged triangulation `T`, then
`P_γ P_γ' = ∏_{b_{δγ} > 0} P_δ^{b_{δγ}} + ∏_{b_{δγ} < 0} P_δ^{-b_{δγ}}`, the products over the
rows `δ` of `B̃•(T) = (b_{δε})`. -/
@[cluster_algebras "lem_D_exchange"]
theorem IsDFlipReplacement.arcValue_mul_arcValue (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    {γ γ' : TaggedArc n} (h : IsDFlipReplacement T γ γ') :
    arcValue K γ * arcValue K γ' =
      (∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ γ), rowValue K δ ^ dMatrix T δ γ) +
        ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ γ < 0),
          rowValue K δ ^ (-dMatrix T δ γ) := by
  rcases isTaggedTriangulation_iff_kind.1 h.1 with ⟨τ, R, hK⟩ | ⟨a, hD⟩
  · exact arcValue_mul_arcValue_of_isKindP K hn hK h
  · exact arcValue_mul_arcValue_of_isDigonKind K hn hD h

/-! ### The seeds of labelled tagged triangulations -/

/-- The extended cluster `x̃(T, ℓ) = (P_{ℓ̂(1)}, …, P_{ℓ̂(2n+2)})`. -/
@[cluster_algebras "def_D_seed"]
noncomputable def dCluster (ℓ : Fin n → TaggedArc n) : Fin (2 * n + 2) → DField K n :=
  fun i => rowValue K (extLabel ℓ i)

/-- The **seed** `Σ(T, ℓ) = (x̃(T, ℓ), B̃•(T, ℓ))` of a labelled tagged triangulation. -/
@[cluster_algebras "def_D_seed"]
noncomputable def dSeed (T : Finset (TaggedArc n)) (ℓ : Fin n → TaggedArc n) :
    SeedData (DField K n) (2 * n + 2) n where
  extCluster := dCluster K ℓ
  extExchangeMatrix := labelledMatrix T ℓ

variable (n) in
/-- The **initial labelling** `ℓ∘` of `T∘`: `ℓ∘(k) = ρ^+_{k+1}` for `k ≤ n - 3`,
`ℓ∘(n - 2) = ρ^+_0` and `ℓ∘(n - 1) = ρ^+_{n-1}` (in `1`-based numbering, `ℓ∘(k) = ρ^+_{k+1}` for
`k ∈ [1, n - 2]`, `ℓ∘(n - 1) = ρ^+_1`, `ℓ∘(n) = ρ^+_n`). -/
@[cluster_algebras "def_D_seed"]
def initialLabelling : Fin n → TaggedArc n := fun k =>
  .radius .plain
    (if (k : ℕ) + 2 < n then vtx ((k : ℤ) + 1) else if (k : ℕ) + 2 = n then vtx 0
      else vtx ((n : ℤ) - 1))

/-- The position `ℓ∘(k)` of the radius `ℓ∘(k)`. -/
private def initialPos (k : Fin n) : Fin n :=
  if (k : ℕ) + 2 < n then vtx ((k : ℤ) + 1) else if (k : ℕ) + 2 = n then vtx 0
    else vtx ((n : ℤ) - 1)

private theorem initialLabelling_eq (k : Fin n) :
    initialLabelling n k = .radius .plain (initialPos k) := rfl

private theorem initialPos_val (k : Fin n) :
    ((initialPos k : Fin n) : ℤ) =
      if (k : ℕ) + 2 < n then (k : ℤ) + 1 else if (k : ℕ) + 2 = n then 0 else (n : ℤ) - 1 := by
  have hk := k.isLt
  unfold initialPos
  split_ifs with h1 h2
  · exact vtx_val_of_lt (by omega) (by omega)
  · exact vtx_val_of_lt le_rfl (by omega)
  · exact vtx_val_of_lt (by omega) (by omega)

private theorem initialPos_injective : Function.Injective (initialPos (n := n)) := by
  intro a b h
  have ha := initialPos_val a
  have hb := initialPos_val b
  rw [h] at ha
  have := a.isLt
  have := b.isLt
  apply Fin.ext
  split_ifs at ha hb <;> omega

/-- `ℓ∘` is a labelling of `T∘`. -/
private theorem isLabelling_initialLabelling :
    IsLabelling (radiusTriangulation n) (initialLabelling n) := by
  refine ⟨fun a b h => initialPos_injective (by simpa [initialLabelling_eq] using h), ?_⟩
  ext γ
  simp only [Set.mem_range, radiusTriangulation, Finset.coe_image, Finset.coe_univ,
    Set.image_univ, initialLabelling_eq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨k, rfl⟩ := (Finite.injective_iff_surjective.1 initialPos_injective) a
    exact ⟨k, rfl⟩

/-- `T∘` is a tagged triangulation. -/
private theorem isTaggedTriangulation_radiusTriangulation (hn : 3 ≤ n) :
    IsTaggedTriangulation (radiusTriangulation n) := by
  simp only [IsTaggedTriangulation, radiusTriangulation, Finset.mem_image, Finset.mem_univ,
    true_and, forall_exists_index, forall_apply_eq_imp_iff]
  refine ⟨fun a b => Or.inr rfl, fun γ hγ => ?_⟩
  rcases γ with ⟨i, j, h⟩ | ⟨_ | _, a⟩
  · exfalso
    apply hγ (vtx ((i : ℤ) + 1))
    exact Finset.mem_image.2 ⟨1, Finset.mem_Ioo.2 ⟨by omega, by omega⟩, by simp⟩
  · exact ⟨a, rfl⟩
  · exfalso
    let b : Fin n := ⟨if (a : ℕ) = 0 then 1 else 0, by split_ifs <;> omega⟩
    rcases hγ b with h | h
    · have := congrArg Fin.val h
      simp only [b] at this
      split_ifs at this <;> omega
    · cases h

/-- The flipped labelling is a labelling of the flip. -/
private theorem isLabelling_flipLabelling {T : Finset (TaggedArc n)} {ℓ : Fin n → TaggedArc n}
    (hℓ : IsLabelling T ℓ) {k : Fin n} {γ' : TaggedArc n} (h : IsDFlipReplacement T (ℓ k) γ') :
    IsLabelling (dFlip T (ℓ k) γ') (flipLabelling ℓ k γ') := by
  have hmem : ∀ i, ℓ i ∈ T := fun i => by
    have : ℓ i ∈ Set.range ℓ := ⟨i, rfl⟩
    rwa [hℓ.2] at this
  have hγ' : ∀ i, ℓ i ≠ γ' := fun i hi => h.2.2.1 (hi ▸ hmem i)
  refine ⟨fun i j hij => ?_, ?_⟩
  · simp only [flipLabelling] at hij
    by_cases hi : i = k <;> by_cases hj : j = k
    · rw [hi, hj]
    · subst hi
      rw [Function.update_self, Function.update_of_ne hj] at hij
      exact absurd hij.symm (hγ' j)
    · subst hj
      rw [Function.update_self, Function.update_of_ne hi] at hij
      exact absurd hij (hγ' i)
    · rw [Function.update_of_ne hi, Function.update_of_ne hj] at hij
      exact hℓ.1 hij
  · ext x
    simp only [Set.mem_range, flipLabelling, dFlip, Finset.coe_insert, Finset.coe_erase,
      Set.mem_insert_iff, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi : i = k
      · subst hi
        exact Or.inl (Function.update_self _ _ _)
      · rw [Function.update_of_ne hi]
        exact Or.inr ⟨hmem i, fun he => hi (hℓ.1 he)⟩
    · rintro (rfl | ⟨hx, hxk⟩)
      · exact ⟨k, Function.update_self _ _ _⟩
      · obtain ⟨i, rfl⟩ : x ∈ Set.range ℓ := by rwa [hℓ.2]
        have hi : i ≠ k := fun he => hxk (he ▸ rfl)
        exact ⟨i, by rw [Function.update_of_ne hi]⟩

/-! ### The matrix of the radius triangulation -/

private theorem gap_univ (a : Fin n) : gap (Finset.univ : Finset (Fin n)) a = 1 := by
  have h0 : 0 ∈ gapCandidates Finset.univ a := by
    simp [gapCandidates, NeZero.pos n]
  rw [gap, dif_pos ⟨0, h0⟩, Nat.add_eq_right]
  exact Nat.eq_zero_of_le_zero (Finset.min'_le _ _ h0)

private theorem predGap_univ (a : Fin n) : predGap (Finset.univ : Finset (Fin n)) a = 1 := by
  have h0 : 0 ∈ predGapCandidates Finset.univ a := by
    simp [predGapCandidates, NeZero.pos n]
  rw [predGap, dif_pos ⟨0, h0⟩, Nat.add_eq_right]
  exact Nat.eq_zero_of_le_zero (Finset.min'_le _ _ h0)

private theorem succ_univ (a : Fin n) :
    succ (Finset.univ : Finset (Fin n)) a = vtx ((a : ℤ) + 1) := by
  rw [succ, gap_univ, Nat.cast_one]

private theorem pred_univ (a : Fin n) :
    pred (Finset.univ : Finset (Fin n)) a = vtx ((a : ℤ) - 1) := by
  rw [pred, predGap_univ, Nat.cast_one]

/-- `T∘` is of kind `P_+` with radius set `[1, n]`. -/
private theorem isKindP_radiusTriangulation (hn : 3 ≤ n) :
    IsKindP (radiusTriangulation n) .plain Finset.univ := by
  refine ⟨by rw [Finset.card_univ, Fintype.card_fin]; omega, fun σ b => ?_, fun a _ => ?_,
    fun a _ h => ?_, fun γ hγ ho => ?_⟩
  · simp only [radiusTriangulation, Finset.mem_image, Finset.mem_univ, true_and, and_true]
    exact ⟨fun ⟨_, h⟩ => by cases h; rfl, fun h => h ▸ ⟨b, rfl⟩⟩
  · rw [gap_univ]
    refine ⟨fun c hc => ?_, fun h => ?_⟩
    · simpa [gap_univ] using (Finset.mem_filter.1 hc).2.1
    · push_cast at h
      omega
  · rw [gap_univ] at h
    omega
  · simp only [radiusTriangulation, Finset.mem_image, Finset.mem_univ, true_and] at hγ
    obtain ⟨a, rfl⟩ := hγ
    exact absurd ho id

/-- `(b - 1) mod n` followed by `+ 1` is `b`. -/
private theorem vtx_vtx_sub_one_add_one (b : Fin n) :
    (vtx (((vtx ((b : ℤ) - 1) : Fin n) : ℤ) + 1) : Fin n) = b := by
  rw [vtx_vtx_add, sub_add_cancel, vtx_coe]

/-- `(c + 1) mod n` followed by `- 1` is `c`. -/
private theorem vtx_vtx_add_one_sub_one (c : Fin n) :
    (vtx (((vtx ((c : ℤ) + 1) : Fin n) : ℤ) - 1) : Fin n) = c := by
  rw [sub_eq_add_neg, vtx_vtx_add, add_neg_cancel_right, vtx_coe]

omit [NeZero n] in
private theorem extLabel_castLE (ℓ : Fin n → TaggedArc n) (i : Fin n) :
    extLabel ℓ (Fin.castLE (le_two_mul_add_two n) i) = .arc (ℓ i) := by
  simp [extLabel]

omit [NeZero n] in
private theorem extLabel_boundary (ℓ : Fin n → TaggedArc n) (c : Fin n) :
    extLabel ℓ ⟨n + c, by omega⟩ = .boundary c := by
  have := c.isLt
  rw [extLabel, dif_neg (by simp), dif_pos (by simp; omega)]
  congr 1
  ext
  simp

omit [NeZero n] in
private theorem extLabel_lam_plain (ℓ : Fin n → TaggedArc n) :
    extLabel ℓ ⟨2 * n, by omega⟩ = .lam .plain := by
  rw [extLabel, dif_neg (by simp; omega), dif_neg (by simp), if_pos rfl]

omit [NeZero n] in
private theorem extLabel_lam_notched (ℓ : Fin n → TaggedArc n) :
    extLabel ℓ ⟨2 * n + 1, by omega⟩ = .lam .notched := by
  rw [extLabel, dif_neg (by simp; omega), dif_neg (by simp), if_neg (by simp)]

/-- The columns of `B̃•(T∘)`. -/
private theorem dMatrix_radiusTriangulation (hn : 3 ≤ n) (b : Fin n) (δ : DRow n) :
    dMatrix (radiusTriangulation n) δ (.radius .plain b) =
      (if δ = .boundary (vtx ((b : ℤ) - 1)) then 1 else 0) +
        (if δ = .arc (.radius .plain (vtx ((b : ℤ) + 1))) then 1 else 0) -
        (if δ = .arc (.radius .plain (vtx ((b : ℤ) - 1))) then 1 else 0) -
        (if δ = .boundary b then 1 else 0) -
        (if (b : ℕ) = 0 ∧ δ = .lam .plain then 1 else 0) +
        (if (b : ℕ) + 1 = n ∧ δ = .lam .notched then 1 else 0) := by
  have h := congrFun (dMatrix_col_radius_of_isKindP hn (isKindP_radiusTriangulation hn)
    (Finset.mem_univ b)) δ
  have hb := b.isLt
  have hp : (((vtx ((b : ℤ) - 1) : Fin n) : ℤ)) = if (b : ℕ) = 0 then (n : ℤ) - 1 else b - 1 := by
    split_ifs with h0
    · rw [vtx_val_eq (-1) (by omega) (by omega)]
      omega
    · rw [vtx_val_eq 0 (by omega) (by omega)]
      ring
  have hs := vtx_vtx_sub_one_add_one b
  rw [pred_univ, gap_univ, gap_univ, succ_univ, Nat.cast_one, seg_eq_boundary, seg_eq_boundary,
    vtx_coe, hs] at h
  rw [h]
  have k1 : kappa n ((vtx ((b : ℤ) - 1) : Fin n) : ℤ) (((vtx ((b : ℤ) - 1) : Fin n) : ℤ) + 1) =
      if (b : ℕ) = 0 then 1 else 0 := by
    unfold kappa
    rw [sheet_eq (by omega) (by omega), sheet_eq (by omega) (by omega)]
    split_ifs <;> omega
  have k2 : kappa n (((vtx ((b : ℤ) - 1) : Fin n) : ℤ) + 1)
      (((vtx ((b : ℤ) - 1) : Fin n) : ℤ) + 1 + 1) = if (b : ℕ) + 1 = n then 1 else 0 := by
    unfold kappa
    rw [sheet_eq (by omega) (by omega), sheet_eq (by omega) (by omega)]
    split_ifs <;> omega
  simp only [segVec, rowVec, DSeg.rows, Finset.mem_singleton, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [k1, k2]
  have h2 : ¬(1 = n) := by omega
  by_cases h0 : (b : ℕ) = 0
  · simp [h0, h2, Tag.neg_plain]
  · by_cases h1 : (b : ℕ) + 1 = n <;> simp [h0, h1, Tag.neg_plain]

omit [NeZero n] in
/-- Case analysis on the indices of the extended cluster. -/
private theorem fin_two_mul_add_two_cases {P : Fin (2 * n + 2) → Prop}
    (h1 : ∀ i : Fin n, P (Fin.castLE (le_two_mul_add_two n) i))
    (h2 : ∀ c : Fin n, P ⟨n + c, by omega⟩) (h3 : P ⟨2 * n, by omega⟩)
    (h4 : P ⟨2 * n + 1, by omega⟩) (i : Fin (2 * n + 2)) : P i := by
  obtain ⟨i, hi⟩ := i
  by_cases a : i < n
  · exact h1 ⟨i, a⟩
  · by_cases b : i < 2 * n
    · have := h2 ⟨i - n, by omega⟩
      simp only [show n + (i - n) = i by omega] at this
      exact this
    · by_cases c : i = 2 * n
      · subst c
        exact h3
      · obtain rfl : i = 2 * n + 1 := by omega
        exact h4

/-! ### The rows outside `ℛ(T)` vanish -/

/-- The rows of the outer side of a sector run are rows of `ℛ(T)`. -/
private theorem mem_of_arc_mem_rows_outer (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {a : Fin n} (ha : a ∈ radiusSet T) {γ : TaggedArc n}
    (h : DRow.arc γ ∈ (seg (a : ℤ) (a + gap (radiusSet T) a) : DSeg n).rows) : γ ∈ T := by
  obtain ⟨g1, g2, g3, g4⟩ := gap_spec' ha
  rcases (show gap (radiusSet T) a = 1 ∨ gap (radiusSet T) a = n ∨
      (2 ≤ gap (radiusSet T) a ∧ gap (radiusSet T) a ≤ n - 1) by omega) with hg | hg | ⟨hg1, hg2⟩
  · rw [hg, Nat.cast_one, seg_eq_boundary] at h
    simp [DSeg.rows] at h
  · rw [hg, seg_eq_loop (by omega)] at h
    simp only [DSeg.rows, Finset.mem_insert, Finset.mem_singleton, DRow.arc.injEq] at h
    rcases isTaggedTriangulation_iff_kind.1 hT with ⟨τ, R', hK⟩ | ⟨b, hD⟩
    · exfalso
      have hR := radiusSet_of_isKindP hK
      have hc : 2 ≤ (radiusSet T).card := hR ▸ hK.1
      have : ∃ b ∈ radiusSet T, b ≠ a := by
        by_contra hcon
        push Not at hcon
        have := Finset.card_le_card (show radiusSet T ⊆ {a} from
          fun b hb => Finset.mem_singleton.2 (hcon b hb))
        simp at this
        omega
      obtain ⟨b, hb, hba⟩ := this
      obtain ⟨t, ht0, htn, hvt⟩ := exists_vtx_eq_of_ne (Ne.symm hba)
      exact g4 t ht0 (by omega) (hvt ▸ hb)
    · have hab : a = b := by
        rw [radiusSet_of_isDigonKind hD] at ha
        simpa using ha
      rcases h with rfl | rfl <;> exact (hD.1 _ _).2 (by rw [vtx_coe]; exact hab)
  · obtain ⟨hs, -, -⟩ := seg_eq_arc (n := n) (u := a) (v := a + gap (radiusSet T) a)
      (by omega) (by omega)
    rw [hs] at h
    simp only [DSeg.rows, Finset.mem_singleton, DRow.arc.injEq] at h
    subst h
    rcases isTaggedTriangulation_iff_kind.1 hT with ⟨τ, R', hK⟩ | ⟨b, hD⟩
    · have hR := radiusSet_of_isKindP hK
      have := hK.2.2.2.1 a (hR ▸ ha) (hR ▸ hg1)
      rw [← hR] at this
      exact this
    · exfalso
      have hR := radiusSet_of_isDigonKind hD
      rw [hR] at ha g3 hg1 hg2
      rw [Finset.mem_singleton] at ha g3
      subst ha
      have h1 := congrArg (fun i : Fin n => (i : ℤ)) g3
      by_cases hlt : (a : ℤ) + (gap {a} a : ℤ) < n
      · rw [vtx_val_eq 0 (by omega) (by omega)] at h1
        omega
      · rw [vtx_val_eq 1 (by omega) (by omega)] at h1
        omega

/-- The rows of a chord of a sector run are rows of `ℛ(T)`. -/
private theorem mem_of_arc_mem_rows_chord {T : Finset (TaggedArc n)} {R : Finset (Fin n)}
    {a : Fin n} (hg : gap R a ≤ n) {c : ℤ × ℤ} (hc : c ∈ sectorChords T R a) {γ : TaggedArc n}
    (h : DRow.arc γ ∈ (seg c.1 c.2 : DSeg n).rows) : γ ∈ T := by
  simp only [sectorChords, Finset.mem_filter] at hc
  obtain ⟨-, ⟨h1, h2, h3, h4, h5⟩, hT⟩ := hc
  have h6 : ¬(c.1 = a ∧ c.2 = a + gap R a) := fun ⟨e1, e2⟩ => h5 (Prod.ext e1 e2)
  obtain ⟨hs, -, -⟩ := seg_eq_arc (n := n) (u := c.1) (v := c.2) h4 (by omega)
  rw [hs] at h
  simp only [DSeg.rows, Finset.mem_singleton, DRow.arc.injEq] at h
  exact h ▸ hT

/-- The rows of a side of a triangle of a sector run are rows of `ℛ(T)`. -/
private theorem mem_of_arc_mem_rows_runSegment (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {a : Fin n} (ha : a ∈ radiusSet T) {c : ℤ × ℤ}
    (hc : IsRunSegment a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a) c)
    {γ : TaggedArc n} (h : DRow.arc γ ∈ (seg c.1 c.2 : DSeg n).rows) : γ ∈ T := by
  rcases hc with hc | ⟨-, h2, -⟩ | rfl
  · exact mem_of_arc_mem_rows_chord (gap_spec' ha).2.1 hc h
  · rw [h2, seg_eq_boundary] at h
    simp [DSeg.rows] at h
  · exact mem_of_arc_mem_rows_outer hn hT ha h

omit [NeZero n] in
/-- A radius of a puncture triangle lies in `T`. -/
private theorem radius_mem_of_isPunctureKind {T : Finset (TaggedArc n)} {τ : Tag}
    (hP : IsPunctureKind T τ) {b : Fin n} (hb : b ∈ radiusSet T) : TaggedArc.radius τ b ∈ T := by
  simp only [radiusSet, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have := hP.2 b
  cases τ <;> rcases hb with hb | hb <;> first | exact hb | exact absurd hb this

/-- **The rows of `B̃•(T)` outside `ℛ(T)` vanish**: `b_{γ ε} = 0` for a tagged arc `γ ∉ T`. -/
private theorem dMatrix_arc_eq_zero (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) {γ : TaggedArc n} (hγ : γ ∉ T) (ε : TaggedArc n) :
    dMatrix T (.arc γ) ε = 0 := by
  have harrow : ∀ s s' : DSeg n, DRow.arc γ ∉ s.rows → DRow.arc γ ∉ s'.rows →
      arrowMatrix s s' (.arc γ) ε = 0 := by
    intro s s' h h'
    simp [arrowMatrix, h, h']
  have hlam : ∀ τ (s : DSeg n), lamMatrix τ s (.arc γ) ε = 0 := by
    intro τ s
    simp [lamMatrix]
  have hcyc : ∀ s₁ s₂ s₃ : DSeg n, DRow.arc γ ∉ s₁.rows → DRow.arc γ ∉ s₂.rows →
      DRow.arc γ ∉ s₃.rows → cycMatrix s₁ s₂ s₃ (.arc γ) ε = 0 := by
    intro s₁ s₂ s₃ h₁ h₂ h₃
    simp only [cycMatrix, Matrix.add_apply, harrow _ _ h₁ h₂, harrow _ _ h₂ h₃,
      harrow _ _ h₃ h₁, add_zero]
  have h1 : ∀ p ∈ outerTriangles T, outerContribution p (.arc γ) ε = 0 := by
    intro p hp
    simp only [outerTriangles, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨a, ha, t, ht, rfl⟩ := hp
    simp only [runTriangles, Finset.mem_filter] at ht
    obtain ⟨-, -, s1, s2, s3⟩ := ht.2
    simp only [outerContribution, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, hlam,
      sub_zero, add_zero, smul_zero]
    exact hcyc _ _ _ (fun h => hγ (mem_of_arc_mem_rows_runSegment hn hT ha s1 h))
      (fun h => hγ (mem_of_arc_mem_rows_runSegment hn hT ha s2 h))
      (fun h => hγ (mem_of_arc_mem_rows_runSegment hn hT ha s3 h))
  have h2 : ∀ p ∈ punctureTriangles T, punctureContribution T p.1 p.2 (.arc γ) ε = 0 := by
    intro p hp
    simp only [punctureTriangles, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at hp
    obtain ⟨ha, hP⟩ := hp
    have hs := (gap_spec' ha).2.2.1
    simp only [punctureContribution, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      hlam, sub_zero, add_zero, smul_zero]
    refine hcyc _ _ _ (fun h => hγ (mem_of_arc_mem_rows_outer hn hT ha h)) (fun h => ?_)
      (fun h => ?_)
    · simp only [DSeg.rows, Finset.mem_singleton, DRow.arc.injEq] at h
      exact hγ (h ▸ radius_mem_of_isPunctureKind hP hs)
    · simp only [DSeg.rows, Finset.mem_singleton, DRow.arc.injEq] at h
      exact hγ (h ▸ radius_mem_of_isPunctureKind hP ha)
  have h3 : ∀ a, digonContribution T a (.arc γ) ε = 0 := by
    intro a
    simp only [digonContribution]
    split_ifs
    · simp [Matrix.add_apply, hlam]
    · rfl
  simp only [dMatrix, Matrix.add_apply, Matrix.sum_apply, Finset.sum_eq_zero h1,
    Finset.sum_eq_zero h2, Finset.sum_eq_zero fun a _ => h3 a, add_zero]

omit [NeZero n] in
/-- The extended labelling of an injective labelling is injective. -/
private theorem extLabel_injective {ℓ : Fin n → TaggedArc n} (hℓ : Function.Injective ℓ) :
    Function.Injective (extLabel ℓ) := by
  intro i j h
  induction i using fin_two_mul_add_two_cases <;> induction j using fin_two_mul_add_two_cases <;>
    simp only [extLabel_castLE, extLabel_boundary, extLabel_lam_plain, extLabel_lam_notched,
      reduceCtorEq, DRow.arc.injEq, DRow.boundary.injEq, DRow.lam.injEq] at h
  all_goals first | rfl | rw [hℓ h] | (subst h; rfl)

/-- A row with a nonzero entry in `B̃•(T)` is a row of `ℛ(T)`, hence a label of the extended
labelling. -/
private theorem exists_extLabel_eq (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    {ℓ : Fin n → TaggedArc n} (hℓ : IsLabelling T ℓ) (hT : IsTaggedTriangulation T)
    {ε : TaggedArc n} {δ : DRow n} (hδ : dMatrix T δ ε ≠ 0) : ∃ i, extLabel ℓ i = δ := by
  rcases δ with γ | c | (_ | _)
  · by_cases hγ : γ ∈ T
    · obtain ⟨j, rfl⟩ : γ ∈ Set.range ℓ := by rwa [hℓ.2]
      exact ⟨_, extLabel_castLE ℓ j⟩
    · exact absurd (dMatrix_arc_eq_zero hn hT hγ _) hδ
  · exact ⟨_, extLabel_boundary ℓ c⟩
  · exact ⟨_, extLabel_lam_plain ℓ⟩
  · exact ⟨_, extLabel_lam_notched ℓ⟩

/-- **Seed mutation is the flip**: `μ_k(Σ(T, ℓ)) = Σ(T', ℓ')` for the flip `T'` of `T` at `ℓ(k)`
and the flipped labelling `ℓ'`. -/
@[cluster_algebras "lem_D_seed_mutation"]
theorem seedMutation_dSeed (hn : 3 ≤ n) {T : Finset (TaggedArc n)} {ℓ : Fin n → TaggedArc n}
    (hℓ : IsLabelling T ℓ) {k : Fin n} {γ' : TaggedArc n} (h : IsDFlipReplacement T (ℓ k) γ') :
    seedMutation (le_two_mul_add_two n) (dSeed K T ℓ) k =
      dSeed K (dFlip T (ℓ k) γ') (flipLabelling ℓ k γ') := by
  have hT := h.1
  have hinj := extLabel_injective hℓ.1
  have hpos : exchangeMonomialPos (dCluster K ℓ) (labelledMatrix T ℓ) k =
      ∏ δ ∈ Finset.univ.filter (fun δ => 0 < dMatrix T δ (ℓ k)),
        rowValue K δ ^ dMatrix T δ (ℓ k) := by
    unfold exchangeMonomialPos
    refine Finset.prod_bij (fun i _ => extLabel ℓ i)
      (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩)
      (fun a _ b _ hab => hinj hab) (fun δ hδ => ?_) (fun i _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ
    obtain ⟨i, rfl⟩ := exists_extLabel_eq hn hℓ hT hδ.ne'
    exact ⟨i, by simpa [labelledMatrix] using hδ, rfl⟩
  have hneg : exchangeMonomialNeg (dCluster K ℓ) (labelledMatrix T ℓ) k =
      ∏ δ ∈ Finset.univ.filter (fun δ => dMatrix T δ (ℓ k) < 0),
        rowValue K δ ^ (-dMatrix T δ (ℓ k)) := by
    unfold exchangeMonomialNeg
    refine Finset.prod_bij (fun i _ => extLabel ℓ i)
      (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩)
      (fun a _ b _ hab => hinj hab) (fun δ hδ => ?_) (fun i _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ
    obtain ⟨i, rfl⟩ := exists_extLabel_eq hn hℓ hT hδ.ne
    exact ⟨i, by simpa [labelledMatrix] using hδ, rfl⟩
  have hoff : ∀ i, i ≠ Fin.castLE (le_two_mul_add_two n) k →
      extLabel ℓ i = extLabel (flipLabelling ℓ k γ') i := by
    intro i
    induction i using fin_two_mul_add_two_cases with
    | h1 j =>
      intro hj
      have hjk : j ≠ k := fun e => hj (e ▸ rfl)
      rw [extLabel_castLE, extLabel_castLE, flipLabelling, Function.update_of_ne hjk]
    | h2 c => intro _; rw [extLabel_boundary, extLabel_boundary]
    | h3 => intro _; rw [extLabel_lam_plain, extLabel_lam_plain]
    | h4 => intro _; rw [extLabel_lam_notched, extLabel_lam_notched]
  refine SeedData.ext ?_ (labelledMatrix_dFlip hn hℓ h).symm
  simp only [seedMutation, dSeed]
  funext i
  by_cases hi : i = Fin.castLE (le_two_mul_add_two n) k
  · subst hi
    rw [Function.update_self, hpos, hneg, ← IsDFlipReplacement.arcValue_mul_arcValue K hn h]
    simp only [dCluster, extLabel_castLE, flipLabelling, Function.update_self, rowValue]
    exact mul_div_cancel_left₀ _ (rowValue_ne_zero K hn (.arc (ℓ k)))
  · rw [Function.update_of_ne hi]
    simp only [dCluster, hoff i hi]

/-! ### The initial seed -/

/-- A polynomial representative of `P_δ`, for the rows of `B̃•(T∘)`. -/
private noncomputable def rowPoly : DRow n → MvPolynomial (DVar n) K
  | .arc (.radius .plain a) => X (.p a)
  | .boundary c =>
      X (.lam .plain) ^ (kappa n c (c + 1)).toNat * X (.p c) * X (.q (vtx ((c : ℤ) + 1))) -
        X (.lam .notched) ^ (kappa n c (c + 1)).toNat * X (.q c) * X (.p (vtx ((c : ℤ) + 1)))
  | .lam τ => X (.lam τ)
  | _ => 0

/-- `P_{β_c} = λ^{κ} p_c q_{c+1} - λ̄^{κ} q_c p_{c+1}`, `κ = κ(c, c + 1)`. -/
private theorem rowValue_boundary (hn : 3 ≤ n) (c : Fin n) :
    rowValue K (.boundary c) =
      var K (.lam .plain) ^ kappa n c (c + 1) * var K (.p c) * var K (.q (vtx ((c : ℤ) + 1))) -
        var K (.lam .notched) ^ kappa n c (c + 1) * var K (.q c) *
          var K (.p (vtx ((c : ℤ) + 1))) := by
  have h := segValue_seg_eq K hn (u := (c : ℤ)) (v := (c : ℤ) + 1) (by omega) (by omega)
  rw [seg_eq_boundary, vtx_coe] at h
  exact h

private theorem algebraMap_rowPoly_boundary (hn : 3 ≤ n) (c : Fin n) :
    algebraMap (MvPolynomial (DVar n) K) (DField K n) (rowPoly K (.boundary c)) =
      rowValue K (.boundary c) := by
  have hk := kappa_eq_zero_or_one (n := n) (u := (c : ℤ)) (v := (c : ℤ) + 1) (by omega)
    (by omega)
  rw [rowValue_boundary K hn, rowPoly]
  simp only [map_sub, map_mul, map_pow]
  rw [← Int.toNat_of_nonneg (show 0 ≤ kappa n c (c + 1) by omega), zpow_natCast, zpow_natCast,
    Int.toNat_natCast]
  rfl

/-- `p_ū`. -/
private noncomputable def pz (u : ℤ) : DField K n := var K (.p (vtx u))

/-- `q_ū`. -/
private noncomputable def qz (u : ℤ) : DField K n := var K (.q (vtx u))

/-- `P_{β_ū}`. -/
private noncomputable def bz (u : ℤ) : DField K n := rowValue K (.boundary (vtx u))

private theorem pz_ne_zero (u : ℤ) : pz K (n := n) u ≠ 0 := var_ne_zero K _

/-- The boundary relations `P_{β_c} = p_c q_{c+1} - q_c p_{c+1}` for `c + 1 < n`. -/
private theorem bz_eq (hn : 3 ≤ n) {c : ℕ} (hc : c + 1 < n) :
    bz K (n := n) c = pz K c * qz K ((c : ℤ) + 1) - qz K c * pz K ((c : ℤ) + 1) := by
  have h := segValue_seg_eq K hn (u := (c : ℤ)) (v := (c : ℤ) + 1) (by omega) (by omega)
  rw [seg_eq_boundary] at h
  have hk : kappa n c (c + 1) = 0 := by
    unfold kappa
    rw [sheet_eq (by omega) (by omega), sheet_eq (by omega) (by omega)]
    split_ifs <;> omega
  rw [hk, zpow_zero, zpow_zero, one_mul, one_mul] at h
  exact h

/-- The boundary relation `P_{β_{n-1}} = λ p_{n-1} q_0 - λ̄ q_{n-1} p_0`. -/
private theorem bz_last (hn : 3 ≤ n) :
    bz K (n := n) ((n - 1 : ℕ) : ℤ) = var K (.lam .plain) * pz K ((n - 1 : ℕ) : ℤ) * qz K 0 -
      var K (.lam .notched) * qz K ((n - 1 : ℕ) : ℤ) * pz K 0 := by
  have h := segValue_seg_eq K hn (u := ((n - 1 : ℕ) : ℤ)) (v := ((n - 1 : ℕ) : ℤ) + 1)
    (by omega) (by omega)
  rw [seg_eq_boundary, show ((n - 1 : ℕ) : ℤ) + 1 = 0 + 1 * n by omega, vtx_add_mul] at h
  have hk : kappa n ((n - 1 : ℕ) : ℤ) (0 + 1 * n) = 1 := by
    unfold kappa
    rw [sheet_eq (by omega) (by omega), sheet_eq (by omega) (by omega)]
    split_ifs <;> omega
  rw [hk, zpow_one, zpow_one] at h
  exact h

/-- The entries of the extended cluster `x̃(T∘, ℓ∘)`: `p_{ℓ∘(k)}`, `P_{β_c}`, `λ` and `λ̄`. -/
private theorem dCluster_initial :
    (∀ k : Fin n, dCluster K (initialLabelling n) (Fin.castLE (le_two_mul_add_two n) k) =
      var K (.p (initialPos k))) ∧
    (∀ c : Fin n, dCluster K (initialLabelling n) ⟨n + c, by omega⟩ = rowValue K (.boundary c)) ∧
    dCluster K (initialLabelling n) ⟨2 * n, by omega⟩ = var K (.lam .plain) ∧
    dCluster K (initialLabelling n) ⟨2 * n + 1, by omega⟩ = var K (.lam .notched) := by
  refine ⟨fun k => ?_, fun c => ?_, ?_, ?_⟩
  · simp only [dCluster, extLabel_castLE, initialLabelling_eq]
    rfl
  · simp only [dCluster, extLabel_boundary]
  · simp only [dCluster, extLabel_lam_plain]
    rfl
  · simp only [dCluster, extLabel_lam_notched]
    rfl

/-- The extended cluster `x̃(T∘, ℓ∘)` is algebraically independent over `𝕜`: it is the image of
the algebraically independent `X_i` under the substitution `Ψ`. -/
private theorem algebraicIndependent_dCluster_initial (hn : 3 ≤ n) :
    AlgebraicIndependent K (dCluster K (initialLabelling n)) := by
  classical
  obtain ⟨hxp, hxb, hxl, hxl'⟩ := dCluster_initial K (n := n)
  set x := dCluster K (initialLabelling n)
  have hsurj := Finite.injective_iff_surjective.1 (initialPos_injective (n := n))
  set y : Fin (2 * n + 2) → MvPolynomial (DVar n) K :=
    fun i => rowPoly K (extLabel (initialLabelling n) i)
  have hxy : x = IsScalarTower.toAlgHom K (MvPolynomial (DVar n) K) (DField K n) ∘ y := by
    funext i
    induction i using fin_two_mul_add_two_cases with
    | h1 k =>
      simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', y, extLabel_castLE,
        initialLabelling_eq, rowPoly, hxp]
      rfl
    | h2 c =>
      simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', y, extLabel_boundary,
        hxb, algebraMap_rowPoly_boundary K hn]
    | h3 =>
      simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', y, extLabel_lam_plain,
        hxl, rowPoly]
      rfl
    | h4 =>
      simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', y, extLabel_lam_notched,
        hxl', rowPoly]
      rfl
  rw [hxy]
  refine AlgebraicIndependent.map' ?_ (IsFractionRing.injective _ _)
  let L := FractionRing (MvPolynomial (Fin (2 * n + 2)) K)
  let Y : Fin (2 * n + 2) → L := fun i => algebraMap (MvPolynomial (Fin (2 * n + 2)) K) L (X i)
  have hY : ∀ i, Y i ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (X_ne_zero i)
  let e : Fin n ≃ Fin n := Equiv.ofBijective _ ⟨initialPos_injective, hsurj⟩
  let XP : ℤ → L := fun u => Y (Fin.castLE (le_two_mul_add_two n) (e.symm (vtx u)))
  let C : ℤ → L := fun u => Y ⟨n + (vtx u : Fin n), by omega⟩
  have hXP : ∀ u, XP u ≠ 0 := fun u => hY _
  have XP_vtx : ∀ u, XP ((vtx u : Fin n) : ℤ) = XP u := fun u => by simp only [XP, vtx_coe]
  let Λ := Y ⟨2 * n, by omega⟩
  let Λ' := Y ⟨2 * n + 1, by omega⟩
  have hΛ : Λ - Λ' ≠ 0 := by
    refine sub_ne_zero.2 fun h => ?_
    have := X_injective (σ := Fin (2 * n + 2)) (R := K)
      (IsFractionRing.injective (MvPolynomial (Fin (2 * n + 2)) K) L h)
    simp [Fin.ext_iff] at this
  let S : L := ∑ d ∈ Finset.range (n - 1), C d / (XP d * XP ((d : ℤ) + 1))
  let Q0 : L := (C ((n : ℤ) - 1) / (XP ((n : ℤ) - 1) * XP 0) + Λ' * S) / (Λ - Λ')
  let Qψ : Fin n → L := fun a =>
    Q0 + ∑ d ∈ Finset.range a, C d / (XP d * XP ((d : ℤ) + 1))
  let g : DVar n → L
    | .p a => XP a
    | .q a => XP a * Qψ a
    | .lam .plain => Λ
    | .lam .notched => Λ'
  refine AlgebraicIndependent.of_comp (aeval g) ?_
  have hcomp : (aeval g : MvPolynomial (DVar n) K →ₐ[K] L) ∘ y =
      IsScalarTower.toAlgHom K (MvPolynomial (Fin (2 * n + 2)) K) L ∘ X := by
    funext i
    induction i using fin_two_mul_add_two_cases with
    | h1 k =>
      simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', y, extLabel_castLE,
        initialLabelling_eq, rowPoly, aeval_X, g, XP, vtx_coe]
      simp only [Y, e]
      congr 3
      exact e.symm_apply_apply k
    | h2 c =>
      simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', y, extLabel_boundary,
        rowPoly, map_sub, map_mul, map_pow, aeval_X, g]
      have hc := c.isLt
      change _ = Y ⟨n + c, _⟩
      have hC : Y ⟨n + c, by omega⟩ = C c := by simp only [C, vtx_coe]
      rw [hC]
      set c' : Fin n := vtx ((c : ℤ) + 1) with hc'def
      by_cases hc1 : (c : ℕ) + 1 < n
      · have hk : kappa n c (c + 1) = 0 := by
          unfold kappa
          rw [sheet_eq (by omega) (by omega), sheet_eq (by omega) (by omega)]
          split_ifs <;> omega
        have hv : c' = ⟨c + 1, hc1⟩ := by
          apply Fin.ext
          have := vtx_val_of_lt (n := n) (u := (c : ℤ) + 1) (by omega) (by omega)
          simp only [c']
          omega
        have hQ : Qψ c' = Qψ c + C c / (XP c * XP c') := by
          simp only [Qψ, hv, Finset.sum_range_succ]
          push_cast
          ring
        rw [hk, hQ]
        simp only [Int.toNat_zero, pow_zero, one_mul]
        calc _ = (XP c * XP c') * (C c / (XP c * XP c')) := by ring
          _ = C c := mul_div_cancel₀ _ (mul_ne_zero (hXP _) (hXP _))
      · have hcn : (c : ℕ) = n - 1 := by omega
        have hk : kappa n c (c + 1) = 1 := by
          unfold kappa
          rw [sheet_eq (by omega) (by omega), sheet_eq (by omega) (by omega)]
          split_ifs <;> omega
        have hv : c' = vtx 0 := by
          rw [hc'def, show (c : ℤ) + 1 = 0 + 1 * n by omega, vtx_add_mul]
        have hv0 : (c' : ℕ) = 0 := by
          rw [hv]
          exact_mod_cast vtx_val_of_lt (n := n) (u := 0) le_rfl (by omega)
        have hQ0 : Qψ c' = Q0 := by
          simp only [Qψ, hv0, Finset.range_zero, Finset.sum_empty, add_zero]
        have hQc : Qψ c = Q0 + S := by
          simp only [Qψ, S, hcn]
        have hc' : (c : ℤ) = (n : ℤ) - 1 := by omega
        have hQ0' : (Λ - Λ') * Q0 = C ((n : ℤ) - 1) / (XP ((n : ℤ) - 1) * XP 0) + Λ' * S :=
          mul_div_cancel₀ _ hΛ
        have e1 : XP (c' : ℤ) = XP 0 := by rw [hv, XP_vtx]
        have e2 : XP c = XP ((n : ℤ) - 1) := by rw [hc']
        have e3 : C c = C ((n : ℤ) - 1) := by rw [hc']
        rw [hk, hQ0, hQc, e1, e2, e3]
        simp only [Int.toNat_one, pow_one]
        calc _ = XP ((n : ℤ) - 1) * XP 0 * ((Λ - Λ') * Q0 - Λ' * S) := by ring
          _ = XP ((n : ℤ) - 1) * XP 0 * (C ((n : ℤ) - 1) / (XP ((n : ℤ) - 1) * XP 0)) := by
            rw [hQ0']
            ring
          _ = C ((n : ℤ) - 1) := mul_div_cancel₀ _ (mul_ne_zero (hXP _) (hXP _))
    | h3 =>
      simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', y, extLabel_lam_plain,
        rowPoly, aeval_X, g]
      rfl
    | h4 =>
      simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', y, extLabel_lam_notched,
        rowPoly, aeval_X, g]
      rfl
  rw [hcomp]
  exact (MvPolynomial.algebraicIndependent_X _ _).map' (IsFractionRing.injective _ _)

/-- `q_k / p_k = q_0 / p_0 + ∑_{d < k} P_{β_d} / (p_d p_{d+1})` for `k < n`. -/
private theorem qz_div_pz_eq (hn : 3 ≤ n) {k : ℕ} (hk : k < n) :
    qz K (n := n) k / pz K k =
      qz K 0 / pz K 0 + ∑ d ∈ Finset.range k, bz K d / (pz K d * pz K ((d : ℤ) + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih (by omega), bz_eq K hn hk]
    have h1 := pz_ne_zero K (n := n) k
    have h2 := pz_ne_zero K (n := n) ((k : ℤ) + 1)
    push_cast
    field_simp
    ring

/-- `q_0 / p_0` in terms of `λ`, `λ̄`, the `p_d` and the `P_{β_d}`. -/
private theorem qz_zero_div_pz_zero (hn : 3 ≤ n) :
    qz K (n := n) 0 / pz K 0 =
      (bz K ((n - 1 : ℕ) : ℤ) / (pz K ((n - 1 : ℕ) : ℤ) * pz K 0) +
        var K (.lam .notched) * ∑ d ∈ Finset.range (n - 1),
          bz K d / (pz K d * pz K ((d : ℤ) + 1))) /
        (var K (.lam .plain) - var K (.lam .notched)) := by
  have hlam : var K (n := n) (.lam .plain) - var K (.lam .notched) ≠ 0 := by
    simp only [var, ← map_sub]
    refine algebraMap_ne_zero_of_eval K (evalPt K 0 0) ?_
    simp [evalPt]
  have hS : ∑ d ∈ Finset.range (n - 1), bz K d / (pz K d * pz K ((d : ℤ) + 1)) =
      qz K (n := n) ((n - 1 : ℕ) : ℤ) / pz K ((n - 1 : ℕ) : ℤ) - qz K 0 / pz K 0 := by
    rw [qz_div_pz_eq K hn (by omega : n - 1 < n)]
    ring
  rw [eq_div_iff hlam, hS, bz_last K hn]
  have h1 := pz_ne_zero K (n := n) ((n - 1 : ℕ) : ℤ)
  have h2 := pz_ne_zero K (n := n) 0
  field_simp
  ring

/-- The extended cluster `x̃(T∘, ℓ∘)` generates `F_n` over `𝕜`. -/
private theorem adjoin_range_dCluster_initial (hn : 3 ≤ n) :
    IntermediateField.adjoin K (Set.range (dCluster K (initialLabelling n))) = ⊤ := by
  obtain ⟨hxp, hxb, hxl, hxl'⟩ := dCluster_initial K (n := n)
  set x := dCluster K (initialLabelling n)
  have hsurj := Finite.injective_iff_surjective.1 (initialPos_injective (n := n))
  set A := IntermediateField.adjoin K (Set.range x)
  have hx : ∀ i, x i ∈ A := fun i => IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  have hp : ∀ u : ℤ, pz K (n := n) u ∈ A := fun u => by
    obtain ⟨k, hk⟩ := hsurj (vtx u)
    rw [pz, ← hk, ← hxp]
    exact hx _
  have hb : ∀ u : ℤ, bz K (n := n) u ∈ A := fun u => by
    rw [bz, ← hxb]
    exact hx _
  have hl : var K (n := n) (.lam .plain) ∈ A := hxl ▸ hx _
  have hl' : var K (n := n) (.lam .notched) ∈ A := hxl' ▸ hx _
  have hq0 : qz K (n := n) 0 / pz K 0 ∈ A := by
    rw [qz_zero_div_pz_zero K hn]
    exact div_mem (add_mem (div_mem (hb _) (mul_mem (hp _) (hp _)))
      (mul_mem hl' (sum_mem fun d _ => div_mem (hb _) (mul_mem (hp _) (hp _)))))
      (sub_mem hl hl')
  have hq : ∀ k : ℕ, k < n → qz K (n := n) k ∈ A := fun k hk => by
    have h := pz_ne_zero K (n := n) k
    have hmem : qz K (n := n) k / pz K k ∈ A := by
      rw [qz_div_pz_eq K hn hk]
      exact add_mem hq0 (sum_mem fun d _ => div_mem (hb _) (mul_mem (hp _) (hp _)))
    have : qz K (n := n) k = qz K k / pz K k * pz K k := by field_simp
    rw [this]
    exact mul_mem hmem (hp _)
  have hvar : ∀ v : DVar n, var K v ∈ A := by
    rintro (a | a | _ | _)
    · have := hp a
      rwa [pz, vtx_coe] at this
    · have := hq a a.isLt
      rwa [qz, vtx_coe] at this
    · exact hl
    · exact hl'
  have hpoly : ∀ f : MvPolynomial (DVar n) K,
      algebraMap (MvPolynomial (DVar n) K) (DField K n) f ∈ A := fun f => by
    induction f using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact A.algebraMap_mem c
    | add f g hf hg =>
      rw [map_add]
      exact add_mem hf hg
    | mul_X f v hf =>
      rw [map_mul]
      exact mul_mem hf (hvar v)
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (DVar n) K) z
  exact div_mem (hpoly a) (hpoly b)

/-- **The seed of the radius triangulation is a labeled seed**: `Σ(T∘, ℓ∘)` is a labeled seed in
`F_n` over `𝕜`. -/
@[cluster_algebras "lem_D_initial_seed"]
theorem isLabeledSeed_dSeed_radiusTriangulation (hn : 3 ≤ n) :
    IsLabeledSeed K (le_two_mul_add_two n)
      (dSeed K (radiusTriangulation n) (initialLabelling n)) := by
  refine ⟨⟨algebraicIndependent_dCluster_initial K hn, adjoin_range_dCluster_initial K hn⟩,
    fun _ => 1, fun _ => one_pos, fun i j => ?_⟩
  simp only [Matrix.submatrix_apply, id, dSeed, labelledMatrix, Matrix.of_apply,
    extLabel_castLE, Int.cast_one, one_mul]
  exact dMatrix_arc_arc _ _ _

/-! ### The pattern `Σ•_n` -/

variable (n) in
/-- The **explicit pattern** `Σ•_n`: the seed pattern of rank `n` in `F_n` over `𝕜` whose seed at
the root `t∘` is `Σ(T∘, ℓ∘)`, namely `t ↦ μ_t(Σ(T∘, ℓ∘))` (`isSeedPattern_dPattern`). -/
@[cluster_algebras "def_D_pattern"]
noncomputable def dPattern : RegularTree n → SeedData (DField K n) (2 * n + 2) n := fun t =>
  seedMutationSeq (le_two_mul_add_two n) (dSeed K (radiusTriangulation n) (initialLabelling n))
    t.word

variable (n) in
/-- The seed of `Σ•_n` at the root `t∘` is `Σ(T∘, ℓ∘)`. -/
@[simp]
theorem dPattern_root :
    dPattern K n .root = dSeed K (radiusTriangulation n) (initialLabelling n) :=
  rfl

/-- `Σ•_n` is a seed pattern, with `Σ•_n(t∘) = Σ(T∘, ℓ∘)`. -/
@[cluster_algebras "def_D_pattern"]
theorem isSeedPattern_dPattern [CharZero K] (hn : 3 ≤ n) :
    IsSeedPattern K (le_two_mul_add_two n) (dPattern K n) ∧
      dPattern K n .root = dSeed K (radiusTriangulation n) (initialLabelling n) := by
  have hS := isLabeledSeed_dSeed_radiusTriangulation K hn
  refine ⟨⟨fun t => hS.seedMutationSeq _ _, ?_⟩, rfl⟩
  rintro k t t' (h | h)
  · simp [dPattern, h]
  · simp only [dPattern, h, seedMutationSeq_append, seedMutationSeq_cons, seedMutationSeq_nil]
    exact (seedMutation_seedMutation _ (hS.seedMutationSeq _ _) k).symm

/-- **The seeds of `Σ•_n` are the seeds of tagged triangulations** (a): every seed of `Σ•_n` is
`Σ(T, ℓ)` for a tagged triangulation `T` with a labelling `ℓ`. -/
@[cluster_algebras "lem_D_pattern_seeds"]
theorem exists_dPattern_eq_dSeed [CharZero K] (hn : 3 ≤ n) (t : RegularTree n) :
    ∃ T ℓ, IsTaggedTriangulation T ∧ IsLabelling T ℓ ∧ dPattern K n t = dSeed K T ℓ := by
  suffices ∀ w : List (Fin n), ∃ T ℓ, IsTaggedTriangulation T ∧ IsLabelling T ℓ ∧
      seedMutationSeq (le_two_mul_add_two n)
        (dSeed K (radiusTriangulation n) (initialLabelling n)) w = dSeed K T ℓ from this t.word
  intro w
  induction w using List.reverseRecOn with
  | nil => exact ⟨_, _, isTaggedTriangulation_radiusTriangulation hn,
      isLabelling_initialLabelling, rfl⟩
  | append_singleton w k ih =>
    obtain ⟨T, ℓ, hT, hℓ, h⟩ := ih
    have hk : ℓ k ∈ T := by
      have : ℓ k ∈ Set.range ℓ := ⟨k, rfl⟩
      rwa [hℓ.2] at this
    obtain ⟨γ', hγ', -⟩ := hT.existsUnique_isDFlipReplacement hn hk
    refine ⟨_, _, hγ'.2.2.2, isLabelling_flipLabelling hℓ hγ', ?_⟩
    rw [seedMutationSeq_append, h, seedMutationSeq_cons, seedMutationSeq_nil,
      seedMutation_dSeed K hn hℓ hγ']

/-- **The seeds of `Σ•_n` are the seeds of tagged triangulations** (b): every tagged
triangulation `T` occurs, with some labelling, as a seed of `Σ•_n`. -/
@[cluster_algebras "lem_D_pattern_seeds"]
theorem IsTaggedTriangulation.exists_dPattern_eq_dSeed [CharZero K] (hn : 3 ≤ n)
    {T : Finset (TaggedArc n)} (hT : IsTaggedTriangulation T) :
    ∃ t ℓ, IsLabelling T ℓ ∧ dPattern K n t = dSeed K T ℓ := by
  have hP := (isSeedPattern_dPattern K hn).1
  have hr := reflTransGen_dFlip_radiusTriangulation hn hT
  clear hT
  induction hr with
  | refl => exact ⟨.root, initialLabelling n, isLabelling_initialLabelling, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨γ, γ', hγ, rfl⟩ := hstep
    obtain ⟨t, ℓ, hℓ, ht⟩ := ih
    have : γ ∈ Set.range ℓ := by rw [hℓ.2]; exact hγ.2.1
    obtain ⟨k, rfl⟩ := this
    obtain ⟨t', ht'⟩ := hP.seedMutationSeq_mem_range (le_two_mul_add_two n) t [k]
    refine ⟨t', _, isLabelling_flipLabelling hℓ hγ, ?_⟩
    rw [ht', seedMutationSeq_cons, seedMutationSeq_nil, ht, seedMutation_dSeed K hn hℓ hγ]

/-- **`Σ•_n` is of finite type.** -/
@[cluster_algebras "lem_D_pattern_finite"]
theorem isFiniteType_dPattern [CharZero K] (hn : 3 ≤ n) : IsFiniteType (dPattern K n) := by
  refine (Set.finite_range fun p : Finset (TaggedArc n) × (Fin n → TaggedArc n) =>
    dSeed K p.1 p.2).subset ?_
  rintro _ ⟨t, rfl⟩
  obtain ⟨T, ℓ, -, -, h⟩ := exists_dPattern_eq_dSeed K hn t
  exact ⟨(T, ℓ), h.symm⟩

/-- The indicator vector of the label `j` with `ℓ∘(j) = ρ^+_a`. -/
private def initialIndicator (a : Fin n) : Fin n → ℤ :=
  fun j => if initialPos j = a then 1 else 0

/-- The row of `λ` in `B̃•(T∘, ℓ∘)` is `-e_0`. -/
private theorem initialIndicator_zero (hn : 3 ≤ n) :
    initialIndicator (0 : Fin n) =
      -labelledMatrix (radiusTriangulation n) (initialLabelling n) ⟨2 * n, by omega⟩ := by
  ext j
  simp only [labelledMatrix, Matrix.of_apply, extLabel_lam_plain, initialLabelling_eq,
    dMatrix_radiusTriangulation hn, initialIndicator, Pi.neg_apply, reduceCtorEq, if_false,
    and_true, and_false, DRow.lam.injEq]
  by_cases h : initialPos j = 0
  · simp [h]
  · have h' : (initialPos j : ℕ) ≠ 0 := fun h' => h (Fin.ext h')
    simp [h, h']

/-- The row of `β_c` in `B̃•(T∘, ℓ∘)` is `e_{c+1} - e_c`. -/
private theorem initialIndicator_add_one_sub (hn : 3 ≤ n) (c : Fin n) :
    initialIndicator (vtx ((c : ℤ) + 1)) - initialIndicator c =
      labelledMatrix (radiusTriangulation n) (initialLabelling n) ⟨n + c, by omega⟩ := by
  ext j
  simp only [labelledMatrix, Matrix.of_apply, extLabel_boundary, initialLabelling_eq,
    dMatrix_radiusTriangulation hn, initialIndicator, Pi.sub_apply]
  have h1 : (initialPos j = vtx ((c : ℤ) + 1)) ↔ c = vtx ((initialPos j : ℤ) - 1) :=
    ⟨fun h => by rw [h, vtx_vtx_add_one_sub_one], fun h => by rw [h, vtx_vtx_sub_one_add_one]⟩
  simp [h1, eq_comm, -add_lt_iff_neg_left]

/-- **The initial matrix has full `ℤ`-rank**: the rows of `B̃•(T∘, ℓ∘)` span `ℤⁿ` as an abelian
group. -/
@[cluster_algebras "lem_D_full_rank"]
theorem span_labelledMatrix_initial (hn : 3 ≤ n) :
    Submodule.span ℤ
      (Set.range (labelledMatrix (radiusTriangulation n) (initialLabelling n))) = ⊤ := by
  set V := Submodule.span ℤ
    (Set.range (labelledMatrix (radiusTriangulation n) (initialLabelling n)))
  have hrow : ∀ r, labelledMatrix (radiusTriangulation n) (initialLabelling n) r ∈ V :=
    fun r => Submodule.subset_span ⟨r, rfl⟩
  have hall : ∀ k : ℕ, k < n → initialIndicator (vtx (k : ℤ) : Fin n) ∈ V := by
    intro k
    induction k with
    | zero =>
      intro _
      have : (vtx ((0 : ℕ) : ℤ) : Fin n) = 0 := by
        apply Fin.ext
        have h := vtx_val_of_lt (n := n) (u := 0) le_rfl (by omega)
        rw [Fin.val_zero]
        exact_mod_cast h
      rw [this, initialIndicator_zero hn]
      exact V.neg_mem (hrow _)
    | succ k ih =>
      intro hk
      have h := initialIndicator_add_one_sub hn (vtx k)
      rw [sub_eq_iff_eq_add] at h
      have hv : (vtx (((vtx (k : ℤ) : Fin n) : ℤ) + 1) : Fin n) = vtx ((k + 1 : ℕ) : ℤ) := by
        rw [vtx_val_of_lt (by omega) (by omega)]
        push_cast
        rfl
      rw [← hv, h]
      exact V.add_mem (hrow _) (ih (by omega))
  have hsingle : ∀ j : Fin n, (fun j' => if j = j' then (1 : ℤ) else 0) ∈ V := by
    intro j
    have : (fun j' => if j = j' then (1 : ℤ) else 0) = initialIndicator (initialPos j) := by
      ext j'
      simp only [initialIndicator]
      congr 1
      exact propext ⟨fun h => h ▸ rfl, fun h => initialPos_injective h.symm⟩
    rw [this, ← vtx_coe (initialPos j)]
    exact hall _ (initialPos j).isLt
  refine eq_top_iff.2 fun v _ => ?_
  rw [pi_eq_sum_univ v]
  exact V.sum_mem fun j _ => V.smul_mem _ (hsingle j)

/-! ### A seed of type `D_n` -/

variable (n) in
/-- The vertex `t_D = (0, 1, …, n - 3, n - 1)` of `𝕋_n` (in `1`-based numbering,
`(1, 2, …, n - 2, n)`). -/
@[cluster_algebras "lem_D_dynkin_seed"]
def dynkinWordD : RegularTree n :=
  ⟨(List.finRange n).filter fun k => (k : ℕ) + 2 ≠ n,
    (((List.pairwise_lt_finRange n).filter _).imp ne_of_lt).isChain⟩

variable (n) in
/-- The matrix `B_D`: `b_{ij} = 1` if there is an arrow `i → j` in the orientation
`k + 1 → k` (`k ≤ n - 3`), `n - 1 → n - 3` of `D_n`, `b_{ij} = -1` for the reversed pairs,
and `0` otherwise; that is, `b_{ij} = 1` exactly when `dynkinTreeDRel n j i`. In `1`-based
numbering, `b_{k+1,k} = 1 = -b_{k,k+1}` for `k ∈ [1, n - 3]` and `b_{n-1,n-2} = b_{n,n-2} = 1`. -/
@[cluster_algebras "lem_D_dynkin_seed"]
def dynkinExchangeD : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if dynkinTreeDRel n j i then 1 else if dynkinTreeDRel n i j then -1 else 0

/-! #### Mutations of matrices of quivers without multiple arrows -/

omit [NeZero n] in
/-- The matrix `[A a b] - [A b a]` of a relation (the arrows of a quiver). -/
private def relMatrix (A : Fin n → Fin n → Prop) [DecidableRel A] : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a b => (if A a b then 1 else 0) - (if A b a then 1 else 0)

omit [NeZero n] in
/-- The mutation of the relation `A` at `k`. -/
private def mutRel (A : Fin n → Fin n → Prop) (k : Fin n) (a b : Fin n) : Prop :=
  if a = k ∨ b = k then A b a else (A a b ∧ ¬(A b k ∧ A k a)) ∨ (A a k ∧ A k b ∧ ¬A b a)

omit [NeZero n] in
private instance (A : Fin n → Fin n → Prop) [DecidableRel A] (k : Fin n) :
    DecidableRel (mutRel A k) := fun a b => by
  unfold mutRel
  infer_instance

omit [NeZero n] in
private theorem relMatrix_congr {A A' : Fin n → Fin n → Prop} [DecidableRel A] [DecidableRel A']
    (h : ∀ a b, A a b ↔ A' a b) : relMatrix A = relMatrix A' := by
  ext a b
  simp only [relMatrix, Matrix.of_apply, h]

omit [NeZero n] in
/-- Mutation of the matrix of an asymmetric relation in which no arrow `a → b` accompanies a
path `a → k → b` is the matrix of the mutated relation. -/
private theorem matrixMutation_relMatrix (A : Fin n → Fin n → Prop) [DecidableRel A] (k : Fin n)
    (hasym : ∀ a b, A a b → ¬A b a) (hsh : ∀ a b, A a k → A k b → ¬A a b) :
    matrixMutation le_rfl (relMatrix A) k = relMatrix (mutRel A k) := by
  ext a b
  by_cases hab : a = k ∨ b = k
  · rw [matrixMutation_apply_of_eq le_rfl _ k (by simpa only [castLE_self] using hab)]
    simp only [relMatrix, Matrix.of_apply, mutRel, if_pos hab, if_pos hab.symm]
    ring
  · push Not at hab
    rw [matrixMutation_apply_of_ne_eq_max le_rfl _ k (by simpa only [castLE_self] using hab.1)
      hab.2]
    simp only [relMatrix, Matrix.of_apply, mutRel, castLE_self, if_neg (not_or.2 hab),
      if_neg (not_or.2 hab.symm)]
    have e1 := hasym a k
    have e2 := hasym k b
    have e3 := hasym a b
    have e4 := hsh a b
    have e5 := hsh b a
    by_cases h1 : A a k <;> by_cases h2 : A k a <;> by_cases h3 : A k b <;>
      by_cases h4 : A b k <;> by_cases h5 : A a b <;> by_cases h6 : A b a <;>
      simp_all

/-! #### The quivers along `t_D` -/

/-- The initial quiver: the cycle `n - 2 → n - 1 → n - 3 → n - 4 → ⋯ → 0 → n - 2`. -/
private def arrInit (n : ℕ) (a b : Fin n) : Prop :=
  ((a : ℕ) = b + 1 ∧ (b : ℕ) + 4 ≤ n) ∨ ((a : ℕ) + 1 = n ∧ (b : ℕ) + 3 = n) ∨
    ((a : ℕ) = 0 ∧ (b : ℕ) + 2 = n) ∨ ((a : ℕ) + 2 = n ∧ (b : ℕ) + 1 = n)

/-- The quiver after mutating at `0, …, j - 1`, for `1 ≤ j ≤ n - 3`. -/
private def arrStep (n j : ℕ) (a b : Fin n) : Prop :=
  ((a : ℕ) = b + 1 ∧ 1 ≤ (a : ℕ) ∧ (a : ℕ) + 1 ≤ j) ∨ ((a : ℕ) + 1 = j ∧ (b : ℕ) = j) ∨
    ((a : ℕ) + 2 = n ∧ (b : ℕ) + 1 = j) ∨ ((a : ℕ) = j ∧ (b : ℕ) + 2 = n) ∨
    ((a : ℕ) + 2 = n ∧ (b : ℕ) + 1 = n) ∨ ((a : ℕ) + 1 = n ∧ (b : ℕ) + 3 = n) ∨
    ((a : ℕ) = b + 1 ∧ j + 1 ≤ (a : ℕ) ∧ (a : ℕ) + 3 ≤ n)

/-- The quiver after mutating at `0, …, n - 3`. -/
private def arrLast (n : ℕ) (a b : Fin n) : Prop :=
  ((a : ℕ) = b + 1 ∧ (a : ℕ) + 2 ≤ n) ∨ ((a : ℕ) + 3 = n ∧ (b : ℕ) + 1 = n)

private instance (n : ℕ) : DecidableRel (arrInit n) := fun _ _ => by
  unfold arrInit; infer_instance

private instance (n j : ℕ) : DecidableRel (arrStep n j) := fun _ _ => by
  unfold arrStep; infer_instance

private instance (n : ℕ) : DecidableRel (arrLast n) := fun _ _ => by
  unfold arrLast; infer_instance

omit [NeZero n] in
private theorem relMatrix_arrInit_mutation (hn : 4 ≤ n) :
    matrixMutation le_rfl (relMatrix (arrInit n)) ⟨0, by omega⟩ = relMatrix (arrStep n 1) := by
  have hak : ∀ x : Fin n, arrInit n x ⟨0, by omega⟩ ↔ (x : ℕ) = 1 := fun x => by
    simp only [arrInit]
    constructor <;> intro h <;> omega
  have hka : ∀ x : Fin n, arrInit n ⟨0, by omega⟩ x ↔ (x : ℕ) + 2 = n := fun x => by
    simp only [arrInit, true_and]
    constructor <;> intro h <;> omega
  rw [matrixMutation_relMatrix _ _ (fun a b h h' => by unfold arrInit at h h'; omega)
    (fun a b h h' => by rw [hak] at h; rw [hka] at h'; unfold arrInit; omega)]
  refine relMatrix_congr fun a b => ?_
  have := a.isLt
  have := b.isLt
  unfold mutRel
  rw [hak a, hka a, hak b, hka b]
  simp only [Fin.ext_iff]
  split_ifs with hab
  · constructor
    · intro h
      unfold arrInit at h
      unfold arrStep
      omega
    · intro h
      unfold arrStep at h
      unfold arrInit
      rcases h with h | h | h | h | h | h | h <;> omega
  · constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
      · unfold arrInit at h1
        unfold arrStep
        omega
      · clear h3
        unfold arrStep
        omega
    · intro h
      unfold arrStep at h
      rcases h with h | h | h | h | h | h | h <;>
        first
          | (exfalso; omega)
          | (left; exact ⟨by unfold arrInit; omega, by omega⟩)
          | (right; exact ⟨by omega, by omega, by unfold arrInit; omega⟩)

omit [NeZero n] in
private theorem relMatrix_arrStep_mutation (hn : 4 ≤ n) {j : ℕ} (hj : 1 ≤ j) (hjn : j + 4 ≤ n) :
    matrixMutation le_rfl (relMatrix (arrStep n j)) ⟨j, by omega⟩ =
      relMatrix (arrStep n (j + 1)) := by
  have hak : ∀ x : Fin n, arrStep n j x ⟨j, by omega⟩ ↔ ((x : ℕ) + 1 = j ∨ (x : ℕ) = j + 1) :=
    fun x => by
      simp only [arrStep, and_true]
      constructor <;> intro h <;> omega
  have hka : ∀ x : Fin n, arrStep n j ⟨j, by omega⟩ x ↔ (x : ℕ) + 2 = n := fun x => by
    simp only [arrStep, true_and]
    constructor <;> intro h <;> omega
  rw [matrixMutation_relMatrix _ _ (fun a b h h' => by unfold arrStep at h h'; omega)
    (fun a b h h' => by rw [hak] at h; rw [hka] at h'; unfold arrStep; omega)]
  refine relMatrix_congr fun a b => ?_
  have := a.isLt
  have := b.isLt
  unfold mutRel
  rw [hak a, hka a, hak b, hka b]
  simp only [Fin.ext_iff]
  split_ifs with hab
  · constructor
    · intro h
      unfold arrStep at h ⊢
      rcases h with h | h | h | h | h | h | h <;> omega
    · intro h
      unfold arrStep at h ⊢
      rcases h with h | h | h | h | h | h | h <;> omega
  · constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
      · unfold arrStep at h1 ⊢
        rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> omega
      · rcases h1 with h1 | h1 <;>
        first
          | (clear h3; unfold arrStep; omega)
          | (exfalso; apply h3; unfold arrStep; omega)
    · intro h
      unfold arrStep at h
      rcases h with h | h | h | h | h | h | h <;>
        first
          | (exfalso; omega)
          | (left; exact ⟨by unfold arrStep; omega, by omega⟩)
          | (right; exact ⟨by omega, by omega, by unfold arrStep; omega⟩)

omit [NeZero n] in
private theorem relMatrix_arrStep_last_mutation (hn : 4 ≤ n) :
    matrixMutation le_rfl (relMatrix (arrStep n (n - 3))) ⟨n - 3, by omega⟩ =
      relMatrix (arrLast n) := by
  have hak : ∀ x : Fin n, arrStep n (n - 3) x ⟨n - 3, by omega⟩ ↔
      ((x : ℕ) + 4 = n ∨ (x : ℕ) + 1 = n) := fun x => by
    simp only [arrStep, and_true]
    constructor <;> intro h <;> omega
  have hka : ∀ x : Fin n, arrStep n (n - 3) ⟨n - 3, by omega⟩ x ↔ (x : ℕ) + 2 = n := fun x => by
    simp only [arrStep, true_and]
    constructor <;> intro h <;> omega
  rw [matrixMutation_relMatrix _ _ (fun a b h h' => by unfold arrStep at h h'; omega)
    (fun a b h h' => by rw [hak] at h; rw [hka] at h'; unfold arrStep; omega)]
  refine relMatrix_congr fun a b => ?_
  have := a.isLt
  have := b.isLt
  unfold mutRel
  rw [hak a, hka a, hak b, hka b]
  simp only [Fin.ext_iff]
  split_ifs with hab
  · constructor
    · intro h
      unfold arrStep at h
      unfold arrLast
      rcases h with h | h | h | h | h | h | h <;> omega
    · intro h
      unfold arrLast at h
      unfold arrStep
      rcases h with h | h <;> omega
  · constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
      · unfold arrStep at h1
        unfold arrLast
        rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> omega
      · rcases h1 with h1 | h1 <;>
        first
          | (clear h3; unfold arrLast; omega)
          | (exfalso; apply h3; unfold arrStep; omega)
    · intro h
      unfold arrLast at h
      rcases h with h | h <;>
        first
          | (exfalso; omega)
          | (left; exact ⟨by unfold arrStep; omega, by omega⟩)

omit [NeZero n] in
private theorem relMatrix_arrLast_mutation (hn : 4 ≤ n) :
    matrixMutation le_rfl (relMatrix (arrLast n)) ⟨n - 1, by omega⟩ = dynkinExchangeD n := by
  have hak : ∀ x : Fin n, arrLast n x ⟨n - 1, by omega⟩ ↔ (x : ℕ) + 3 = n := fun x => by
    simp only [arrLast]
    constructor <;> intro h <;> omega
  have hka : ∀ x : Fin n, ¬arrLast n ⟨n - 1, by omega⟩ x := fun x => by
    simp only [arrLast]
    omega
  rw [matrixMutation_relMatrix _ _ (fun a b h h' => by unfold arrLast at h h'; omega)
    (fun a b h h' => absurd h' (hka b))]
  ext a b
  have := a.isLt
  have := b.isLt
  have hR : ¬(dynkinTreeDRel n a b ∧ dynkinTreeDRel n b a) := by
    simp only [dynkinTreeDRel]
    omega
  have key : ∀ x y : Fin n, mutRel (arrLast n) ⟨n - 1, by omega⟩ x y ↔ dynkinTreeDRel n y x := by
    intro x y
    have := x.isLt
    have := y.isLt
    unfold mutRel
    simp only [hka, false_and, and_false, not_false_eq_true, and_true, or_false, Fin.ext_iff]
    split_ifs <;> unfold arrLast dynkinTreeDRel <;> constructor <;> intro h <;> omega
  simp only [relMatrix, dynkinExchangeD, Matrix.of_apply, key]
  by_cases e1 : dynkinTreeDRel n b a
  · simp only [e1, if_true, if_neg fun h => hR ⟨h, e1⟩]
    rfl
  · simp only [e1, if_false, zero_sub]
    split_ifs <;> rfl

/-- The principal part of the matrix of `T∘` is the matrix of the initial quiver. -/
private theorem principalPart_labelledMatrix_initial (hn : 4 ≤ n) :
    principalPart (le_two_mul_add_two n)
        (labelledMatrix (radiusTriangulation n) (initialLabelling n)) =
      relMatrix (arrInit n) := by
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [principalPart, Matrix.submatrix_apply, id, labelledMatrix, Matrix.of_apply,
    extLabel_castLE, initialLabelling_eq, dMatrix_radiusTriangulation (by omega : 3 ≤ n),
    reduceCtorEq, if_false, and_false, sub_zero, add_zero, DRow.arc.injEq,
    TaggedArc.radius.injEq, true_and, relMatrix]
  have hpa := initialPos_val a
  have hpb := initialPos_val b
  have e1 : initialPos a = vtx ((initialPos b : ℤ) + 1) ↔ arrInit n a b := by
    rw [Fin.ext_iff, ← Int.natCast_inj]
    by_cases h : (initialPos b : ℤ) + 1 < n
    · rw [vtx_val_eq 0 (by omega) (by omega)]
      simp only [arrInit]
      split_ifs at hpa hpb <;> omega
    · rw [vtx_val_eq 1 (by omega) (by omega)]
      simp only [arrInit]
      split_ifs at hpa hpb <;> omega
  have e2 : initialPos a = vtx ((initialPos b : ℤ) - 1) ↔ arrInit n b a := by
    rw [Fin.ext_iff, ← Int.natCast_inj]
    by_cases h : 0 ≤ (initialPos b : ℤ) - 1
    · rw [vtx_val_eq 0 (by omega) (by omega)]
      simp only [arrInit]
      split_ifs at hpa hpb <;> omega
    · rw [vtx_val_eq (-1) (by omega) (by omega)]
      simp only [arrInit]
      split_ifs at hpa hpb <;> omega
  simp only [e1, e2, zero_add]

omit [NeZero n] in
/-- The principal part of a mutation sequence is the corresponding sequence of mutations of the
principal part. -/
private theorem principalPart_seedMutationSeq {F : Type*} [Field F] {m : ℕ} (hmn : n ≤ m)
    (S : SeedData F m n) (w : List (Fin n)) :
    principalPart hmn (seedMutationSeq hmn S w).extExchangeMatrix =
      w.foldl (fun B k => matrixMutation le_rfl B k) (principalPart hmn S.extExchangeMatrix) := by
  induction w generalizing S with
  | nil => rfl
  | cons k w ih =>
    rw [seedMutationSeq_cons, ih, List.foldl_cons]
    congr 1
    exact principalPart_matrixMutation hmn _ k

/-- **A seed of `Σ•_n` with exchange matrix of type `D_n`**: for `n ≥ 4` the exchange matrix of
`Σ•_n(t_D)` is `B_D`. -/
@[cluster_algebras "lem_D_dynkin_seed"]
theorem principalPart_dPattern_dynkinWordD (hn : 4 ≤ n) :
    principalPart (le_two_mul_add_two n) (dPattern K n (dynkinWordD n)).extExchangeMatrix =
      dynkinExchangeD n := by
  let g : ℕ → Fin n := fun j => if h : j < n then ⟨j, h⟩ else ⟨0, by omega⟩
  have hg : ∀ j (h : j < n), g j = ⟨j, h⟩ := fun j h => by simp only [g, dif_pos h]
  have hword : (dynkinWordD n).word = (List.range (n - 2) ++ [n - 1]).map g := by
    have h1 : (dynkinWordD n).word = ((dynkinWordD n).word.map Fin.val).map g := by
      rw [List.map_map]
      conv_lhs => rw [← List.map_id (dynkinWordD n).word]
      refine List.map_congr_left fun k _ => ?_
      simp only [Function.comp_apply, id, hg k k.isLt]
    have h2 : (dynkinWordD n).word.map Fin.val = List.range (n - 2) ++ [n - 1] := by
      simp only [dynkinWordD]
      rw [show (fun k : Fin n => decide ((k : ℕ) + 2 ≠ n)) =
          (fun j : ℕ => decide (j + 2 ≠ n)) ∘ Fin.val from rfl, ← List.filter_map,
        List.map_coe_finRange_eq_range,
        show n = n - 2 + 1 + 1 by omega, List.range_succ, List.range_succ, List.filter_append,
        List.filter_append, List.filter_eq_self.2 (fun j hj => by
          simp only [List.mem_range] at hj
          simp only [decide_eq_true_eq]
          omega)]
      simp only [List.filter_cons, List.filter_nil]
      simp
    rw [h1, h2]
  have hsteps : ∀ j, 1 ≤ j → j ≤ n - 3 →
      (List.range j).foldl (fun B k => matrixMutation le_rfl B (g k))
        (relMatrix (arrInit n)) = relMatrix (arrStep n j) := by
    intro j hj1 hj2
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_cons,
          List.foldl_nil, hg 0 (by omega)]
        exact relMatrix_arrInit_mutation hn
      · rw [List.range_succ, List.foldl_append, ih hj (by omega), List.foldl_cons,
          List.foldl_nil, hg j (by omega)]
        exact relMatrix_arrStep_mutation hn hj (by omega)
  simp only [dPattern]
  rw [principalPart_seedMutationSeq, hword, List.foldl_map]
  simp only [dSeed]
  rw [principalPart_labelledMatrix_initial hn, List.foldl_append,
    show n - 2 = n - 3 + 1 by omega, List.range_succ, List.foldl_append,
    hsteps (n - 3) (by omega) le_rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hg (n - 3) (by omega), relMatrix_arrStep_last_mutation hn, hg (n - 1) (by omega),
    relMatrix_arrLast_mutation hn]

omit [NeZero n] in
/-- **A seed of `Σ•_n` with exchange matrix of type `D_n`**: the Cartan counterpart of `B_D` is
`C(D_n)`. -/
@[cluster_algebras "lem_D_dynkin_seed"]
theorem cartanCounterpart_dynkinExchangeD (hn : 4 ≤ n) :
    cartanCounterpart (dynkinExchangeD n) = cartanD n := by
  have := hn
  ext i j
  simp only [cartanCounterpart, cartanD, cartanOfGraph, dynkinExchangeD, Matrix.of_apply,
    dynkinTreeD, SimpleGraph.fromRel_adj, dynkinTreeDRel]
  by_cases hij : i = j
  · simp [hij]
  have hv : (i : ℕ) ≠ j := Fin.val_ne_of_ne hij
  have := i.isLt
  have := j.isLt
  simp only [ne_eq, hij, not_false_eq_true, true_and]
  split_ifs <;> first | omega | norm_num

/-- **A seed of `Σ•_n` with exchange matrix of type `D_n`**: `Σ•_n` is of type `D_n`. -/
@[cluster_algebras "lem_D_dynkin_seed"]
theorem isPatternOfType_dPattern (hn : 4 ≤ n) :
    IsPatternOfType (le_two_mul_add_two n) (dPattern K n) [.D n hn] := by
  refine ⟨dynkinWordD n, ?_⟩
  rw [principalPart_dPattern_dynkinWordD K hn, cartanCounterpart_dynkinExchangeD hn]
  refine ⟨Equiv.refl _, fun i j => ?_⟩
  have h : ∀ i : Fin n, (finSumFinEquiv (m := n) (n := 0)).symm i = Sum.inl i :=
    fun i => finSumFinEquiv_symm_apply_castAdd (n := 0) i
  change cartanD n i j =
    Matrix.fromBlocks (cartanD n) (0 : Matrix (Fin n) (Fin 0) ℤ) 0 0
      ((finSumFinEquiv (m := n) (n := 0)).symm (i : Fin (n + 0)))
      ((finSumFinEquiv (m := n) (n := 0)).symm (j : Fin (n + 0)))
  rw [h, h, Matrix.fromBlocks_apply₁₁]

omit [NeZero n] in
/-- **A seed of `Σ•_n` with exchange matrix of type `D_n`**: `B_D = B(Q_D, id)` for the
orientation `Q_D` of the tree `D_n` with an arrow `i → j` exactly when `b_{ij} = 1`, that is,
the arrows `k + 1 → k` (`k ≤ n - 3`) and `n - 1 → n - 3`. -/
@[cluster_algebras "lem_D_dynkin_seed"]
theorem exists_orientation_dynkinExchangeD (hn : 4 ≤ n) :
    ∃ (Q : Quiver (Fin n)) (L : Labelling Q n n), Q.IsTreeOrientation (dynkinTreeD n) ∧
      L.equiv = Equiv.refl _ ∧ exchangeMatrix Q L = dynkinExchangeD n ∧
      ∀ i j, Q.arrows i j = if dynkinTreeDRel n j i then 1 else 0 := by
  have := hn
  have hR : ∀ i j : Fin n, dynkinTreeDRel n i j → ¬dynkinTreeDRel n j i := fun i j h h' => by
    have := i.isLt
    have := j.isLt
    simp only [dynkinTreeDRel] at h h'
    omega
  obtain ⟨Q, hQa, hQf, hQ⟩ := orientation_of_arrow_counts (dynkinTreeD n)
    (fun i j => if dynkinTreeDRel n j i then 1 else 0)
    (fun v => if_neg fun h => by simp only [dynkinTreeDRel] at h; omega)
    (fun u v huv => by
      rw [dynkinTreeD, SimpleGraph.fromRel_adj] at huv
      rcases huv.2 with h | h
      · rw [if_neg (hR u v h), if_pos h]
      · rw [if_pos h, if_neg (hR v u h)])
    (fun u v huv hadj => if_neg fun h => hadj (by
      rw [dynkinTreeD, SimpleGraph.fromRel_adj]
      exact ⟨huv, Or.inr h⟩))
  let L : Labelling Q n n := ⟨Equiv.refl _, le_rfl, fun i => by simp [hQf, i.isLt]⟩
  refine ⟨Q, L, hQ, rfl, ?_, fun i j => by rw [hQa]⟩
  ext i j
  simp only [exchangeMatrix, extExchangeMatrix, Matrix.of_apply, signedCount, hQa, L,
    Equiv.refl_apply, dynkinExchangeD, castLE_self]
  by_cases h1 : dynkinTreeDRel n j i
  · rw [if_pos h1, if_neg (hR j i h1), if_pos h1]
    simp
  · by_cases h2 : dynkinTreeDRel n i j
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
      simp
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
      simp

end ClusterAlgebras.TypeD

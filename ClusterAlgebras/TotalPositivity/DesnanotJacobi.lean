/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.SchurComplement
public import ClusterAlgebras.External
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.LinearCombination

/-!
# The two exchange relations among minors

Two three-term identities among minors drive the exchange relations of double wiring diagrams
[FWZ, Chapter 1].

The first is the **Desnanot–Jacobi identity** (the "Lewis Carroll identity") in general
position: for the generic matrix `z`, sets `I'`, `S` of equal size, rows `x < y` outside `I'` and
columns `a < b` outside `S`,
`Δ_{I'y, Sb} Δ_{I'x, Sa} = Δ_{I'y, Sa} Δ_{I'x, Sb} + Δ_{I',S} Δ_{I'xy, Sab}`.
It is proved through the Schur complement `T = z/(I', S)` over the field of fractions of
`ℤ[z]`: each of the five minors bordering `Δ_{I',S}` is, up to a sign `(-1)^ν`, the product of
`Δ_{I',S}` with a `1 × 1` or `2 × 2` minor of `T`, and the identity reduces to the expansion of a
`2 × 2` determinant.

The second is the **three-term relation for nested row sets**: for any square matrix over a
commutative ring, columns `α < β < γ` outside `S` and row sets `I ⊆ I⁺` of sizes `|S| + 1` and
`|S| + 2`,
`Δ_{I, Sβ} Δ_{I⁺, Sαγ} = Δ_{I, Sα} Δ_{I⁺, Sβγ} + Δ_{I, Sγ} Δ_{I⁺, Sαβ}`.
It is the three-term relation for flag minors applied to the matrix whose first rows are the
rows of `I`, in increasing order, followed by the row of `I⁺ \ I`: the flag minors of that
matrix are the minors on `I`, and, up to one common sign, the minors on `I⁺`.

## Main results

* `ClusterAlgebras.minor_desnanot_jacobi`: the Desnanot–Jacobi identity in general position.
* `ClusterAlgebras.minor_nested_three_term`: the three-term relation for nested row sets.

Along the way: `minor_singleton` and `minor_pair` (the `1 × 1` and `2 × 2` minors written out)
and `shuffleCount_union` (additivity of the shuffle count).

## Implementation notes

* The Desnanot–Jacobi identity is stated for any linearly ordered row and column types, not only
  `[1, n]`, and without assuming `I'` and `S` nonempty: for `I' = S = ∅` the minor `Δ_{∅,∅}` is
  `1` and the identity is the expansion of a `2 × 2` determinant, which the same proof covers.
* The common sign in the nested relation is the sign of the permutation that sorts the rows
  `i₁ < ⋯ < i_k, i*` into increasing order. It is not computed as `(-1)^q`: the proof only uses
  that it is a unit squaring to `1`.
* The three-term relation for flag minors (`flagMinor_three_term`), an exercise in
  [FWZ, Chapter 1], is assumed rather than proved; the nested relation depends on it.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 1.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

section Small

variable {R : Type*} [CommRing R] {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]

/-- A `1 × 1` minor is the corresponding entry. -/
theorem minor_singleton (M : Matrix ι κ R) (i : ι) (j : κ) : minor M {i} {j} = M i j := by
  rw [minor_of_card_eq M (card_singleton i) (card_singleton j), Matrix.det_unique]
  simp [orderEmbOfFin_singleton]

/-- The increasing enumeration of a pair `{a, b}` with `a < b` is `![a, b]`. -/
theorem orderEmbOfFin_pair {α : Type*} [LinearOrder α] {a b : α} (hab : a < b)
    (h : ({a, b} : Finset α).card = 2) :
    ⇑(({a, b} : Finset α).orderEmbOfFin h) = ![a, b] :=
  (orderEmbOfFin_unique h (f := ![a, b]) (fun x => by fin_cases x <;> simp)
    (fun x y hxy => by fin_cases x <;> fin_cases y <;> simp_all)).symm

/-- A `2 × 2` minor, written out: for `x < y` and `a < b`,
`Δ_{xy, ab}(M) = M_{xa} M_{yb} - M_{xb} M_{ya}`. -/
theorem minor_pair (M : Matrix ι κ R) {x y : ι} (hxy : x < y) {a b : κ} (hab : a < b) :
    minor M {x, y} {a, b} = M x a * M y b - M x b * M y a := by
  rw [minor_of_card_eq M (card_pair hxy.ne) (card_pair hab.ne), Matrix.det_fin_two,
    Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
    Matrix.submatrix_apply, orderEmbOfFin_pair hxy, orderEmbOfFin_pair hab]
  simp

/-- The shuffle count is additive in its first argument over disjoint unions. -/
theorem shuffleCount_union {A B C : Finset ι} (h : Disjoint A B) :
    shuffleCount (A ∪ B) C = shuffleCount A C + shuffleCount B C := by
  unfold shuffleCount
  rw [union_product, filter_union, card_union_of_disjoint]
  exact disjoint_filter_filter (disjoint_product.mpr (Or.inl h))

end Small

/-- **The Desnanot–Jacobi identity in general position.** For the generic matrix `z`, sets `I'`,
`S` with `|I'| = |S|`, rows `x < y` outside `I'` and columns `a < b` outside `S`,
`Δ_{I'y, Sb} Δ_{I'x, Sa} = Δ_{I'y, Sa} Δ_{I'x, Sb} + Δ_{I',S} Δ_{I'xy, Sab}`. -/
@[cluster_algebras "lem_desnanot_jacobi"]
theorem minor_desnanot_jacobi {ι κ : Type*} [LinearOrder ι] [LinearOrder κ] {I' : Finset ι}
    {S : Finset κ} (hcard : S.card = I'.card) {x y : ι} (hx : x ∉ I') (hy : y ∉ I') (hxy : x < y)
    {a b : κ} (ha : a ∉ S) (hb : b ∉ S) (hab : a < b) :
    minor (genericMatrix ι κ) (I' ∪ {y}) (S ∪ {b}) *
        minor (genericMatrix ι κ) (I' ∪ {x}) (S ∪ {a}) =
      minor (genericMatrix ι κ) (I' ∪ {y}) (S ∪ {a}) *
          minor (genericMatrix ι κ) (I' ∪ {x}) (S ∪ {b}) +
        minor (genericMatrix ι κ) I' S * minor (genericMatrix ι κ) (I' ∪ {x, y}) (S ∪ {a, b}) := by
  classical
  set P := MvPolynomial (ι × κ) ℤ
  set K := FractionRing P
  apply IsFractionRing.injective P K
  simp only [map_add, map_mul, RingHom.map_minor (algebraMap P K)]
  set X := (genericMatrix ι κ).map (algebraMap P K)
  have hd : minor X I' S ≠ 0 := by
    rw [← RingHom.map_minor]
    exact (map_ne_zero_iff _ (IsFractionRing.injective P K)).mpr
      (minor_genericMatrix_ne_zero hcard.symm)
  set T := schurComplement X I' S
  have h1 : ∀ e f, e ∉ I' → f ∉ S → minor X (I' ∪ {e}) (S ∪ {f}) =
      (-1) ^ (shuffleCount {e} I' + shuffleCount {f} S) * minor X I' S * T e f := by
    intro e f he hf
    rw [union_comm I', union_comm S, minor_union_eq_schurComplement X hcard hd
      (disjoint_singleton_left.mpr he) (disjoint_singleton_left.mpr hf) (by simp),
      minor_singleton]
  have hνI : shuffleCount {x, y} I' = shuffleCount {x} I' + shuffleCount {y} I' := by
    rw [insert_eq, shuffleCount_union (disjoint_singleton.mpr hxy.ne)]
  have hνS : shuffleCount {a, b} S = shuffleCount {a} S + shuffleCount {b} S := by
    rw [insert_eq, shuffleCount_union (disjoint_singleton.mpr hab.ne)]
  have h2 : minor X (I' ∪ {x, y}) (S ∪ {a, b}) =
      (-1) ^ (shuffleCount {x} I' + shuffleCount {y} I' +
        (shuffleCount {a} S + shuffleCount {b} S)) * minor X I' S *
        (T x a * T y b - T x b * T y a) := by
    rw [union_comm I', union_comm S, minor_union_eq_schurComplement X hcard hd
      (disjoint_insert_left.mpr ⟨hx, disjoint_singleton_left.mpr hy⟩)
      (disjoint_insert_left.mpr ⟨ha, disjoint_singleton_left.mpr hb⟩)
      (by rw [card_pair hab.ne, card_pair hxy.ne]), minor_pair T hxy hab, hνI, hνS]
  rw [h1 y b hy hb, h1 x a hx ha, h1 y a hy ha, h1 x b hx hb, h2]
  ring

section Nested

variable {R : Type*} [CommRing R] {κ : Type*} [LinearOrder κ]

/-- The increasing enumeration of the first `m` rows of `Fin n` is the inclusion
`Fin.castLE`. -/
theorem orderEmbOfFin_initialRows {n m : ℕ} (hm : m ≤ n) (h : (initialRows n m).card = m)
    (l : Fin m) : (initialRows n m).orderEmbOfFin h l = Fin.castLE hm l :=
  (congrFun (orderEmbOfFin_unique h (f := Fin.castLE hm) (fun l => by simp [initialRows])
    (Fin.castLEOrderEmb hm).strictMono) l).symm

/-- If the first `m` rows of `y` are the rows `g 0, …, g (m-1)` of `z`, in this order, then a
minor of `y` on the first `m` rows is the determinant of `z` on the rows `g` and the columns of
`X`, listed increasingly. -/
theorem minor_initialRows_eq_det {ι : Type*} {n m : ℕ} (hm : m ≤ n) (y : Matrix (Fin n) κ R)
    (z : Matrix ι κ R) (g : Fin m → ι) (hy : ∀ l, y (Fin.castLE hm l) = z (g l))
    {X : Finset κ} (hX : X.card = m) :
    minor y (initialRows n m) X = (z.submatrix g (X.orderEmbOfFin hX)).det := by
  rw [minor_of_card_eq y (card_initialRows hm) hX]
  congr 1
  ext l j
  simp [orderEmbOfFin_initialRows hm, hy]

end Nested

/-- **The three-term relation for nested row sets.** For an `n × n` matrix over a commutative ring,
a set `S` of columns, columns `α < β < γ` outside `S`, and row sets `I ⊆ I⁺` with `|I| = |S| + 1`
and `|I⁺| = |S| + 2`,
`Δ_{I, Sβ} Δ_{I⁺, Sαγ} = Δ_{I, Sα} Δ_{I⁺, Sβγ} + Δ_{I, Sγ} Δ_{I⁺, Sαβ}`. -/
@[cluster_algebras "lem_nested_three_term"]
theorem minor_nested_three_term {R : Type*} [CommRing R] {n : ℕ} (hn : 3 ≤ n)
    (z : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)) {α β γ : Fin n} (hα : α ∉ S)
    (hβ : β ∉ S) (hγ : γ ∉ S) (hαβ : α < β) (hβγ : β < γ) {I Iplus : Finset (Fin n)}
    (hsub : I ⊆ Iplus) (hI : I.card = S.card + 1) (hIplus : Iplus.card = S.card + 2) :
    minor z I (S ∪ {β}) * minor z Iplus (S ∪ {α, γ}) =
      minor z I (S ∪ {α}) * minor z Iplus (S ∪ {β, γ}) +
        minor z I (S ∪ {γ}) * minor z Iplus (S ∪ {α, β}) := by
  classical
  set k := S.card + 1 with hk
  have hk1 : k + 1 ≤ n := by
    have := card_le_univ Iplus
    rw [Fintype.card_fin] at this
    omega
  have hk0 : k ≤ n := by omega
  obtain ⟨istar, hstar⟩ : ∃ i, Iplus \ I = {i} :=
    card_eq_one.mp (by rw [card_sdiff_of_subset hsub, hI, hIplus]; omega)
  have hstar_mem : istar ∈ Iplus ∧ istar ∉ I := mem_sdiff.mp (hstar ▸ mem_singleton_self istar)
  set eI := I.orderEmbOfFin hI
  let g : Fin (k + 1) → Fin n := Fin.lastCases istar eI
  have hg_cast : ∀ l : Fin k, g (Fin.castSucc l) = eI l := fun l => by simp [g]
  have hg_last : g (Fin.last k) = istar := by simp [g]
  let y : Matrix (Fin n) (Fin n) R := fun r =>
    if h : (r : ℕ) < k + 1 then z (g ⟨r, h⟩) else 0
  have hy_big : ∀ l : Fin (k + 1), y (Fin.castLE hk1 l) = z (g l) := fun l => by
    simp only [y, Fin.val_castLE, dif_pos l.isLt]
  have hy_small : ∀ l : Fin k, y (Fin.castLE hk0 l) = z (eI l) := fun l => by
    rw [← hg_cast]
    simp only [y, Fin.val_castLE, dif_pos (Nat.lt_succ_of_lt l.isLt)]
    rfl
  have hsmall : ∀ X : Finset (Fin n), X.card = k → flagMinor y X = minor z I X := by
    intro X hX
    rw [flagMinor, hX, minor_initialRows_eq_det hk0 y z eI hy_small hX,
      minor_of_card_eq z hI hX]
  have hg_mem : ∀ l, g l ∈ Iplus := by
    intro l
    induction l using Fin.lastCases with
    | last => rw [hg_last]; exact hstar_mem.1
    | cast l => rw [hg_cast]; exact hsub (I.orderEmbOfFin_mem hI l)
  have hg_inj : Function.Injective g := by
    intro l l' h
    induction l using Fin.lastCases with
    | last =>
      induction l' using Fin.lastCases with
      | last => rfl
      | cast l' =>
        rw [hg_last, hg_cast] at h
        exact absurd (h ▸ I.orderEmbOfFin_mem hI l') hstar_mem.2
    | cast l =>
      induction l' using Fin.lastCases with
      | last =>
        rw [hg_last, hg_cast] at h
        exact absurd (h ▸ I.orderEmbOfFin_mem hI l) hstar_mem.2
      | cast l' =>
        rw [hg_cast, hg_cast] at h
        rw [eI.injective h]
  set ePlus := Iplus.orderIsoOfFin hIplus
  let τ : Fin (k + 1) → Fin (k + 1) := fun l => ePlus.symm ⟨g l, hg_mem l⟩
  have hτ : Function.Injective τ := fun l l' h => hg_inj (by
    simpa using congrArg Subtype.val (ePlus.symm.injective h))
  let σ : Equiv.Perm (Fin (k + 1)) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτ)
  have hσ : ∀ l, Iplus.orderEmbOfFin hIplus (σ l) = g l := fun l => by
    rw [← coe_orderIsoOfFin_apply]
    simp [σ, τ, ePlus]
  set ε : R := ((Equiv.Perm.sign σ : ℤ) : R)
  have hε : ε * ε = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hbig : ∀ X : Finset (Fin n), X.card = k + 1 → flagMinor y X = ε * minor z Iplus X := by
    intro X hX
    rw [flagMinor, hX, minor_initialRows_eq_det hk1 y z g hy_big hX,
      minor_of_card_eq z hIplus hX, ← Matrix.det_permute]
    congr 1
    ext l j
    simp [hσ]
  have hc1 : ∀ c, c ∉ S → (S ∪ {c}).card = k := fun c hc => by
    rw [card_union_of_disjoint (disjoint_singleton_right.mpr hc), card_singleton]
  have hc2 : ∀ c d, c ∉ S → d ∉ S → c < d → (S ∪ {c, d}).card = k + 1 := fun c d hc hd hcd => by
    rw [card_union_of_disjoint
      (disjoint_insert_right.mpr ⟨hc, disjoint_singleton_right.mpr hd⟩), card_pair hcd.ne]
  have key := flagMinor_three_term hn y S hα hβ hγ hαβ hβγ
  rw [hsmall _ (hc1 β hβ), hsmall _ (hc1 α hα), hsmall _ (hc1 γ hγ),
    hbig _ (hc2 α γ hα hγ (hαβ.trans hβγ)), hbig _ (hc2 β γ hβ hγ hβγ),
    hbig _ (hc2 α β hα hβ hαβ)] at key
  linear_combination ε * key -
    (minor z I (S ∪ {β}) * minor z Iplus (S ∪ {α, γ}) -
      minor z I (S ∪ {α}) * minor z Iplus (S ∪ {β, γ}) -
        minor z I (S ∪ {γ}) * minor z Iplus (S ∪ {α, β})) * hε

end ClusterAlgebras

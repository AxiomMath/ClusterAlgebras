/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.Defs
public import ClusterAlgebras.TotalPositivity.Muir

/-!
# Plücker coordinates specialize to minors

Let `z` be the generic `k × 2k` matrix and `y` the generic `k × k` matrix over `ℂ`. The
specialization `φ : ℂ[z] → ℂ[y]` substitutes `[y | W]` for `z`, where `W` is the antidiagonal
matrix whose column `j` is `(-1)^{j-1}` times the unit vector `e_{k+1-j}`. For a `k`-element set
`J` of columns, `φ` sends the Plücker coordinate `P_J(z)` to the minor `Δ_{K(J), L(J)}(y)`, where
`L(J) = J ∩ [1, k]` and `K(J) = [1, k] ∖ {k + 1 - j : k + j ∈ J}`; the choice of signs in `W`
makes every sign in the Laplace expansion along the columns of `W` cancel.

## Main results

* `ClusterAlgebras.minor_eq_mul_minor_erase`: Laplace expansion of a minor along a column that
  vanishes on all but one of its rows.
* `ClusterAlgebras.card_matRowSet_eq_card_matColSet`: `|K(J)| = |L(J)|` for `|J| = k`.
* `ClusterAlgebras.matSpecialization_pluckerCoord`: `φ(P_J(z)) = Δ_{K(J), L(J)}(y)` for `|J| = k`.
* `ClusterAlgebras.matSpecialization_pluckerCoord_of_nonempty`,
  `ClusterAlgebras.matSpecialization_pluckerCoord_topHalf`: the two cases
  `φ(P_J(z)) = Δ_{K(J), L(J)}(y)` when `L(J) ≠ ∅` and `φ(P_{[k+1, 2k]}(z)) = 1`.
* `ClusterAlgebras.existsUnique_matRowSet_matColSet`: every pair `(K, L)` of subsets of `[1, k]`
  with `|K| = |L|` and `L ≠ ∅` is `(K(J), L(J))` for exactly one `k`-element `J ≠ [k+1, 2k]`.

## Implementation notes

* Indices are 0-based: column `c ≥ k` of `z` is sent to `(-1)^{c-k}` times the unit vector of row
  `2k - 1 - c`, and the top half `[k+1, 2k]` is `{c | k ≤ c}`.
* Neither the hypothesis `k ≥ 2` nor a split into two cases is needed: since the minor on two
  empty sets is `1`, the single statement `φ(P_J(z)) = Δ_{K(J), L(J)}(y)` holds for every `k` and
  every `k`-element `J`, and specializes to both cases.
* The sign computation is an induction on the number of columns of `J` in the top half: the
  largest such column `c` is expanded first, along the row `r = 2k - 1 - c`. The rows already
  removed are all smaller than `r`, so `r` is in position `r - (k - |I|)` among the remaining rows
  `I`, and `c` in position `|J| - 1` among the columns; with the sign `(-1)^{c-k}` of the entry the
  exponent is `2|J| - 2`, so every step of the expansion contributes the sign `+1`.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix Finset MvPolynomial

/-! ### Laplace expansion of a minor along a sparse column -/

section Laplace

variable {R : Type*} [CommRing R] {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]

/-- The element in position `p` of the increasing enumeration of `I` has exactly `p` elements of
`I` below it. -/
theorem card_filter_lt_orderEmbOfFin (I : Finset ι) {n : ℕ} (h : I.card = n) (p : Fin n) :
    #{i ∈ I | i < I.orderEmbOfFin h p} = p := by
  have : I.filter (· < I.orderEmbOfFin h p) =
      (univ.filter (· < p)).map (I.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [mem_filter, mem_map, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨q, rfl⟩ : x ∈ Set.range (I.orderEmbOfFin h) := by rwa [range_orderEmbOfFin]
      exact ⟨q, (OrderEmbedding.lt_iff_lt _).1 hlt, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨orderEmbOfFin_mem _ _ _, (OrderEmbedding.lt_iff_lt _).2 hq⟩
  rw [this, card_map, filter_gt_eq_Iio, Fin.card_Iio]

/-- Removing the element in position `p` from `I`: the increasing enumeration of the rest is that
of `I` composed with `p.succAbove`. -/
theorem orderEmbOfFin_erase (I : Finset ι) {n : ℕ} (h : I.card = n + 1) (p : Fin (n + 1))
    (h' : (I.erase (I.orderEmbOfFin h p)).card = n) (x : Fin n) :
    (I.erase (I.orderEmbOfFin h p)).orderEmbOfFin h' x = I.orderEmbOfFin h (p.succAbove x) :=
  (congrFun (orderEmbOfFin_unique h' (f := fun x => I.orderEmbOfFin h (p.succAbove x))
    (fun x => mem_erase.2 ⟨fun he => Fin.succAbove_ne p x ((I.orderEmbOfFin h).injective he),
      orderEmbOfFin_mem _ _ _⟩)
    ((I.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove p))) x).symm

/-- **Laplace expansion of a minor along a sparse column.** If the column `c ∈ J` of `Z` vanishes
on every row of `I` other than `r ∈ I`, then
`Δ_{I,J}(Z) = (-1)^{a + b} Z_{rc} Δ_{I ∖ {r}, J ∖ {c}}(Z)`, where `a` and `b` are the numbers of
elements of `I` below `r` and of `J` below `c` (the 0-based positions of `r` and `c`). -/
theorem minor_eq_mul_minor_erase (Z : Matrix ι κ R) {I : Finset ι} {J : Finset κ}
    (hIJ : I.card = J.card) {r : ι} {c : κ} (hr : r ∈ I) (hc : c ∈ J)
    (hcol : ∀ i ∈ I, i ≠ r → Z i c = 0) :
    minor Z I J = (-1) ^ (#{i ∈ I | i < r} + #{j ∈ J | j < c}) * Z r c *
      minor Z (I.erase r) (J.erase c) := by
  obtain ⟨n, hn⟩ : ∃ n, I.card = n + 1 := ⟨I.card - 1, by
    have := card_pos.2 ⟨r, hr⟩
    omega⟩
  have hJn : J.card = n + 1 := hIJ ▸ hn
  obtain ⟨p, rfl⟩ : r ∈ Set.range (I.orderEmbOfFin hn) := by rwa [range_orderEmbOfFin]
  obtain ⟨q, rfl⟩ : c ∈ Set.range (J.orderEmbOfFin hJn) := by rwa [range_orderEmbOfFin]
  have hIe : (I.erase (I.orderEmbOfFin hn p)).card = n := by
    rw [card_erase_of_mem hr, hn]
    rfl
  have hJe : (J.erase (J.orderEmbOfFin hJn q)).card = n := by
    rw [card_erase_of_mem hc, hJn]
    rfl
  rw [minor_of_card_eq Z hn hJn, minor_of_card_eq Z hIe hJe, card_filter_lt_orderEmbOfFin,
    card_filter_lt_orderEmbOfFin, det_succ_column _ q, Fintype.sum_eq_single p]
  · simp only [submatrix_apply]
    congr 2
    ext x y
    simp only [submatrix_apply, orderEmbOfFin_erase]
  · intro i hi
    simp only [submatrix_apply]
    rw [hcol _ (orderEmbOfFin_mem _ _ _) (fun he => hi ((I.orderEmbOfFin hn).injective he))]
    simp

end Laplace

/-! ### The sets `K(J)` and `L(J)` -/

section Sets

variable {k : ℕ}

/-- The row `2k - 1 - c` of `y` assigned to a column `c ≥ k` of `z`, 0-based. -/
private def rowOf (c : Fin (2 * k)) (hc : k ≤ (c : ℕ)) : Fin k :=
  ⟨2 * k - 1 - c, by have := c.isLt; omega⟩

/-- The column `2k - 1 - r` of `z` assigned to a row `r` of `y`, 0-based. -/
private def colOf (r : Fin k) : Fin (2 * k) :=
  ⟨2 * k - 1 - r, by have := r.isLt; omega⟩

private theorem rowOf_colOf (r : Fin k) (h : k ≤ (colOf r : ℕ)) : rowOf (colOf r) h = r := by
  ext
  simp only [rowOf, colOf]
  have := r.isLt
  omega

private theorem colOf_rowOf (c : Fin (2 * k)) (hc : k ≤ (c : ℕ)) : colOf (rowOf c hc) = c := by
  ext
  simp only [rowOf, colOf]
  have := c.isLt
  omega

/-- Membership in `L(J)`: the column `j` of `y` is in `L(J)` iff the column `j` of `z` is in
`J`. -/
theorem mem_matColSet {J : Finset (Fin (2 * k))} {j : Fin k} :
    j ∈ matColSet k J ↔ Fin.castLE (by omega) j ∈ J := by
  simp [matColSet, Fin.castLE]

/-- Erasing a column `c ≥ k` of `J` does not change `L(J)`. -/
theorem matColSet_erase_of_le {J : Finset (Fin (2 * k))} {c : Fin (2 * k)}
    (hc : k ≤ (c : ℕ)) : matColSet k (J.erase c) = matColSet k J := by
  ext j
  simp only [mem_matColSet, mem_erase, Fin.castLE, ne_eq, and_iff_right_iff_imp]
  intro _ h
  rw [← h] at hc
  simp only at hc
  omega

/-- Membership in `K(J)`: the row `r` is in `K(J)` iff the column `2k - 1 - r` is not in `J`. -/
theorem mem_matRowSet {J : Finset (Fin (2 * k))} {r : Fin k} :
    r ∈ matRowSet k J ↔ (⟨2 * k - 1 - r, by have := r.isLt; omega⟩ : Fin (2 * k)) ∉ J := by
  simp [matRowSet]

/-- `L(J)`, read as columns of `z`, is the part of `J` in the first `k` columns. -/
theorem map_matColSet (J : Finset (Fin (2 * k))) :
    (matColSet k J).map (Fin.castLEEmb (by omega)) =
      J.filter fun c : Fin (2 * k) => (c : ℕ) < k := by
  ext c
  simp only [mem_map, mem_filter, Fin.castLEEmb_apply, mem_matColSet]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨hj, j.isLt⟩
  · rintro ⟨hc, hlt⟩
    exact ⟨⟨c, hlt⟩, hc, rfl⟩

/-- `|K(J)| + |J| = k + |L(J)|` for every set `J` of columns. -/
theorem card_matRowSet_add_card (J : Finset (Fin (2 * k))) :
    (matRowSet k J).card + J.card = k + (matColSet k J).card := by
  have hJ := card_filter_add_card_filter_not (s := J) (fun c : Fin (2 * k) => (c : ℕ) < k)
  have hL : (matColSet k J).card = #(J.filter fun c : Fin (2 * k) => (c : ℕ) < k) := by
    rw [← map_matColSet, card_map]
  have hK := card_filter_add_card_filter_not (s := (univ : Finset (Fin k)))
    (fun r : Fin k => (⟨2 * k - 1 - r, by have := r.isLt; omega⟩ : Fin (2 * k)) ∉ J)
  have hbij : #{r : Fin k | ¬ (⟨2 * k - 1 - r, by have := r.isLt; omega⟩ : Fin (2 * k)) ∉ J} =
      #(J.filter fun c : Fin (2 * k) => ¬ (c : ℕ) < k) := by
    refine card_bij' (fun r _ => colOf r) (fun c hc => rowOf c (by simp at hc; omega)) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [mem_filter, mem_univ, true_and, not_not] at hr
      simp only [mem_filter, colOf, not_lt]
      exact ⟨hr, by have := r.isLt; omega⟩
    · intro c hc
      simp only [mem_filter, mem_univ, true_and, not_not, not_lt] at hc ⊢
      convert hc.1 using 1
      ext
      simp only [rowOf]
      have := c.isLt
      omega
    · exact fun r _ => rowOf_colOf r _
    · exact fun c _ => colOf_rowOf c _
  rw [card_univ, Fintype.card_fin] at hK
  have hRow : (matRowSet k J).card = #{r : Fin k |
      (⟨2 * k - 1 - r, by have := r.isLt; omega⟩ : Fin (2 * k)) ∉ J} := rfl
  omega

/-- **`|K(J)| = |L(J)|`** for a `k`-element set `J` of columns. -/
@[cluster_algebras "lem_mat_specialization_minors"]
theorem card_matRowSet_eq_card_matColSet {J : Finset (Fin (2 * k))} (hJ : J.card = k) :
    (matRowSet k J).card = (matColSet k J).card := by
  have := card_matRowSet_add_card J
  omega

/-- The pair `(K(J), L(J))` determines `J`. -/
theorem eq_of_matRowSet_eq_of_matColSet_eq {J J' : Finset (Fin (2 * k))}
    (hK : matRowSet k J = matRowSet k J') (hL : matColSet k J = matColSet k J') : J = J' := by
  ext c
  by_cases hc : (c : ℕ) < k
  · simpa [mem_matColSet, Fin.castLE] using congrArg (fun L => (⟨c, hc⟩ : Fin k) ∈ L) hL
  · have := congrArg (fun K => rowOf c (by omega) ∈ K) hK
    simp only [mem_matRowSet, eq_iff_iff] at this
    have hcc : (⟨2 * k - 1 - (rowOf c (by omega) : ℕ), by omega⟩ : Fin (2 * k)) = c := by
      ext
      simp only [rowOf]
      have := c.isLt
      omega
    rw [hcc] at this
    exact not_iff_not.1 this

/-- **The converse.** Every pair `(K, L)` of subsets of `[1, k]` with `|K| = |L|` and `L ≠ ∅` is
`(K(J), L(J))` for exactly one `k`-element set `J ≠ [k+1, 2k]`, namely
`J = L ∪ {k + j : j ∈ [1, k], k + 1 - j ∉ K}` (1-based). -/
theorem existsUnique_matRowSet_matColSet {K L : Finset (Fin k)} (hKL : K.card = L.card)
    (hL : L.Nonempty) :
    ∃! J : Finset (Fin (2 * k)), J.card = k ∧
      J ≠ univ.filter (fun c : Fin (2 * k) => k ≤ (c : ℕ)) ∧
      matRowSet k J = K ∧ matColSet k J = L := by
  let J : Finset (Fin (2 * k)) := univ.filter fun c : Fin (2 * k) =>
    if h : (c : ℕ) < k then (⟨c, h⟩ : Fin k) ∈ L else rowOf c (by omega) ∉ K
  have hK' : matRowSet k J = K := by
    ext r
    simp only [mem_matRowSet, J, mem_filter, mem_univ, true_and]
    rw [dif_neg (by have := r.isLt; omega), not_not]
    have : rowOf (k := k) ⟨2 * k - 1 - r, by have := r.isLt; omega⟩
      (by have := r.isLt; simp; omega) = r := by
      ext
      simp only [rowOf]
      have := r.isLt
      omega
    rw [this]
  have hL' : matColSet k J = L := by
    ext j
    simp only [mem_matColSet, J, mem_filter, mem_univ, true_and, Fin.castLE]
    rw [dif_pos j.isLt]
  refine ⟨J, ⟨?_, ?_, hK', hL'⟩, ?_⟩
  · have := card_matRowSet_add_card J
    rw [hK', hL', hKL] at this
    omega
  · intro h
    obtain ⟨j, hj⟩ := hL
    have : Fin.castLE (by omega) j ∈ J := by rwa [← mem_matColSet, hL']
    rw [h] at this
    simp [Fin.castLE] at this
    omega
  · rintro J' ⟨_, _, hK'', hL''⟩
    exact eq_of_matRowSet_eq_of_matColSet_eq (hK''.trans hK'.symm) (hL''.trans hL'.symm)

end Sets

/-! ### The specialization of a Plücker coordinate -/

section Specialization

variable {k : ℕ}

/-- `φ(z_{rc})`: the entry of `y` for `c < k`, and otherwise `(-1)^{c-k}` in row `2k - 1 - c` and
`0` elsewhere (0-based). -/
theorem matSpecialization_X (r : Fin k) (c : Fin (2 * k)) :
    matSpecialization k (X (r, c)) = if h : (c : ℕ) < k then X (r, ⟨c, h⟩)
      else if (r : ℕ) + c = 2 * k - 1 then C ((-1) ^ ((c : ℕ) - k)) else 0 := by
  simp [matSpecialization]

/-- On columns of the first `k` only, `φ` turns a minor of `z` into the minor of `y` on the same
rows and the same columns. -/
private theorem minor_map_matSpecialization_of_lt (I : Finset (Fin k)) {J : Finset (Fin (2 * k))}
    (hJ : ∀ c ∈ J, (c : ℕ) < k) :
    minor ((complexGenericMatrix k (2 * k)).map (matSpecialization k)) I J =
      minor (complexGenericMatrix k k) I (matColSet k J) := by
  have hsub : ((complexGenericMatrix k (2 * k)).map (matSpecialization k)).submatrix
      (OrderIso.refl (Fin k)).toOrderEmbedding (Fin.castLEOrderEmb (by omega)) =
      complexGenericMatrix k k := by
    ext r j
    simp [matSpecialization_X, Fin.castLE]
  have hJ' : (matColSet k J).map (Fin.castLEOrderEmb (n := k) (m := 2 * k) (by omega)).toEmbedding
      = J := by
    have := map_matColSet J
    rwa [filter_true_of_mem hJ] at this
  rw [← hsub, minor_submatrix_orderEmbedding, hJ']
  congr 1
  ext
  simp

/-- If `c ∈ J` is the largest element of `J`, the other elements of `J` all lie below it. -/
private theorem card_filter_lt_of_forall_le {α : Type*} [LinearOrder α] {J : Finset α} {c : α}
    (hcJ : c ∈ J) (hc : ∀ c' ∈ J, c' ≤ c) : #{j ∈ J | j < c} = J.card - 1 := by
  rw [← card_erase_of_mem hcJ]
  congr 1
  ext j
  simp only [mem_filter, mem_erase]
  exact ⟨fun ⟨hj, hjc⟩ => ⟨hjc.ne, hj⟩, fun ⟨hjc, hj⟩ => ⟨hj, (hc j hj).lt_of_ne hjc⟩⟩

/-- If every row outside `I` lies below `r`, then `r` is the number of rows of `I` below it plus
the number of rows outside `I`. -/
private theorem card_filter_lt_add_card_compl {I : Finset (Fin k)} {r : Fin k}
    (h : ∀ i ∉ I, i < r) : #{i ∈ I | i < r} + (k - I.card) = r := by
  have hc : #(Iᶜ) = k - I.card := by rw [card_compl, Fintype.card_fin]
  have h1 : Iᶜ.filter (· < r) = Iᶜ := filter_true_of_mem fun i hi => h i (mem_compl.1 hi)
  have h2 := card_union_of_disjoint (disjoint_filter_filter (p := fun i : Fin k => i < r)
    (q := fun i : Fin k => i < r) (disjoint_compl_right : Disjoint I Iᶜ))
  rw [← filter_union, union_compl, filter_gt_eq_Iio, Fin.card_Iio, h1, hc] at h2
  omega

/-- **One step of the sign computation.** If `c ≥ k` is the largest column of `J` and the row
`r = 2k - 1 - c` lies in `I` above every row outside `I`, the expansion of `Δ_{I,J}(φ(z))` along
`c` has the sign `+1`: `Δ_{I,J}(φ(z)) = Δ_{I ∖ {r}, J ∖ {c}}(φ(z))`. -/
private theorem minor_map_matSpecialization_eq_erase {I : Finset (Fin k)}
    {J : Finset (Fin (2 * k))} (hcard : I.card = J.card) {c : Fin (2 * k)} (hcJ : c ∈ J)
    (hc : ∀ c' ∈ J, c' ≤ c) (hck : k ≤ (c : ℕ)) {r : Fin k} (hrI : r ∈ I)
    (hrc : (r : ℕ) + c = 2 * k - 1) (hout : ∀ i ∉ I, i < r) :
    minor ((complexGenericMatrix k (2 * k)).map (matSpecialization k)) I J =
      minor ((complexGenericMatrix k (2 * k)).map (matSpecialization k)) (I.erase r)
        (J.erase c) := by
  have hIr := card_filter_lt_add_card_compl hout
  have hJc := card_filter_lt_of_forall_le hcJ hc
  have hIk : I.card ≤ k := by
    have := card_le_univ I
    rwa [Fintype.card_fin] at this
  have hJpos : 0 < J.card := card_pos.2 ⟨c, hcJ⟩
  have hsign : ((-1 : ComplexPoly k k) ^ (#{i ∈ I | i < r} + #{j ∈ J | j < c})) *
      ((complexGenericMatrix k (2 * k)).map (matSpecialization k)) r c = 1 := by
    rw [Matrix.map_apply, complexGenericMatrix_apply, matSpecialization_X, dif_neg (by omega),
      if_pos hrc, map_pow, map_neg, map_one, ← pow_add]
    exact Even.neg_one_pow ⟨J.card - 1, by omega⟩
  rw [minor_eq_mul_minor_erase _ hcard hrI hcJ, hsign, one_mul]
  intro i _ hi
  rw [Matrix.map_apply, complexGenericMatrix_apply, matSpecialization_X, dif_neg (by omega),
    if_neg fun h => hi (Fin.ext (by omega))]

/-- Removing the row `r` and the column `c = 2k - 1 - r ∈ J` does not change the set of rows
`r' ∈ I` whose column `2k - 1 - r'` lies outside `J`. -/
private theorem filter_erase_eq_filter {I : Finset (Fin k)} {J : Finset (Fin (2 * k))}
    {r : Fin k} {c : Fin (2 * k)} (hcJ : c ∈ J) (hrc : (r : ℕ) + c = 2 * k - 1) :
    ((I.erase r).filter fun r' : Fin k =>
        (⟨2 * k - 1 - r', by have := r'.isLt; omega⟩ : Fin (2 * k)) ∉ J.erase c) =
      I.filter fun r' : Fin k =>
        (⟨2 * k - 1 - r', by have := r'.isLt; omega⟩ : Fin (2 * k)) ∉ J := by
  ext r'
  simp only [mem_filter, mem_erase, ne_eq]
  have : (⟨2 * k - 1 - r', by have := r'.isLt; omega⟩ : Fin (2 * k)) = c ↔ r' = r := by
    rw [Fin.ext_iff, Fin.ext_iff]
    simp only
    have := r'.isLt
    omega
  exact ⟨fun ⟨⟨hr', hI⟩, hJ⟩ => ⟨hI, fun h => hJ ⟨mt this.1 hr', h⟩⟩,
    fun ⟨hI, hJ⟩ => ⟨⟨fun h => hJ (by rw [this.2 h]; exact hcJ), hI⟩, fun h => hJ h.2⟩⟩

/-- The induction behind `matSpecialization_pluckerCoord`, on the number `n` of columns of `J` in
the top half: the rows outside `I` lie above every row `2k - 1 - c`, `c ∈ J`, `c ≥ k`, which lie in
`I`. -/
private theorem minor_map_matSpecialization_aux (n : ℕ) :
    ∀ (I : Finset (Fin k)) (J : Finset (Fin (2 * k))),
      #(J.filter fun c : Fin (2 * k) => k ≤ (c : ℕ)) = n →
      I.card = J.card → (∀ i ∉ I, ∀ c ∈ J, k ≤ (c : ℕ) → (i : ℕ) + c < 2 * k - 1) →
      (∀ c ∈ J, k ≤ (c : ℕ) → ∃ i ∈ I, (i : ℕ) + c = 2 * k - 1) →
      minor ((complexGenericMatrix k (2 * k)).map (matSpecialization k)) I J =
        minor (complexGenericMatrix k k)
          (I.filter fun r => (⟨2 * k - 1 - r, by have := r.isLt; omega⟩ : Fin (2 * k)) ∉ J)
          (matColSet k J) := by
  induction n with
  | zero =>
    intro I J hn _ _ _
    have hJ : ∀ c ∈ J, (c : ℕ) < k := fun c hc =>
      not_le.1 (filter_eq_empty_iff.1 (card_eq_zero.1 hn) hc)
    rw [minor_map_matSpecialization_of_lt I hJ, filter_true_of_mem]
    intro r _ hr
    have := hJ _ hr
    simp only at this
    omega
  | succ n ih =>
    intro I J hn hcard hout hin
    obtain ⟨c₀, hc₀⟩ : (J.filter fun c : Fin (2 * k) => k ≤ (c : ℕ)).Nonempty := by
      rw [← card_pos, hn]
      omega
    have hne : J.Nonempty := ⟨c₀, (mem_filter.1 hc₀).1⟩
    set c := J.max' hne
    have hcJ : c ∈ J := max'_mem J hne
    have hck : k ≤ (c : ℕ) := le_trans (mem_filter.1 hc₀).2 (le_max' J c₀ (mem_filter.1 hc₀).1)
    obtain ⟨r, hrI, hrc⟩ := hin c hcJ hck
    rw [minor_map_matSpecialization_eq_erase hcard hcJ (fun c' hc' => le_max' J c' hc') hck hrI
      hrc fun i hi => by have := hout i hi c hcJ hck; rw [Fin.lt_def]; omega,
      ih (I.erase r) (J.erase c)]
    · congr 1
      · exact filter_erase_eq_filter hcJ hrc
      · exact matColSet_erase_of_le hck
    · rw [filter_erase, card_erase_of_mem (mem_filter.2 ⟨hcJ, hck⟩), hn]
      rfl
    · rw [card_erase_of_mem hrI, card_erase_of_mem hcJ, hcard]
    · intro i hi c' hc' hc'k
      rw [mem_erase] at hc'
      have := lt_of_le_of_ne (le_max' J c' hc'.2) hc'.1
      rw [Fin.lt_def] at this
      by_cases hir : i = r
      · subst hir
        omega
      · exact hout i (fun h => hi (mem_erase.2 ⟨hir, h⟩)) c' hc'.2 hc'k
    · intro c' hc' hc'k
      rw [mem_erase] at hc'
      obtain ⟨i, hiI, hic⟩ := hin c' hc'.2 hc'k
      refine ⟨i, mem_erase.2 ⟨fun h => hc'.1 ?_, hiI⟩, hic⟩
      subst h
      ext
      omega

/-- **Plücker coordinates specialize to minors.** For every `k`-element set `J` of columns,
`φ(P_J(z)) = Δ_{K(J), L(J)}(y)`. For `J = [k+1, 2k]` both `K(J)` and `L(J)` are empty and the
minor is `1`. -/
@[cluster_algebras "lem_mat_specialization_minors"]
theorem matSpecialization_pluckerCoord {J : Finset (Fin (2 * k))} (hJ : J.card = k) :
    matSpecialization k (pluckerCoord (complexGenericMatrix k (2 * k)) J) =
      minor (complexGenericMatrix k k) (matRowSet k J) (matColSet k J) := by
  rw [← AlgHom.coe_toRingHom, RingHom.map_pluckerCoord, pluckerCoord]
  refine minor_map_matSpecialization_aux _ univ J rfl ?_ (fun i hi => absurd (mem_univ i) hi) ?_
  · rw [card_univ, Fintype.card_fin, hJ]
  · intro c _ hc
    refine ⟨rowOf c hc, mem_univ _, ?_⟩
    simp only [rowOf]
    have := c.isLt
    omega

/-- **Plücker coordinates specialize to minors**, the case `L(J) ≠ ∅`:
`φ(P_J(z)) = Δ_{K(J), L(J)}(y)`. -/
@[cluster_algebras "lem_mat_specialization_minors"]
theorem matSpecialization_pluckerCoord_of_nonempty {J : Finset (Fin (2 * k))} (hJ : J.card = k)
    (_hL : (matColSet k J).Nonempty) :
    matSpecialization k (pluckerCoord (complexGenericMatrix k (2 * k)) J) =
      minor (complexGenericMatrix k k) (matRowSet k J) (matColSet k J) :=
  matSpecialization_pluckerCoord hJ

/-- The top half `[k+1, 2k]` of the columns has `k` elements. -/
theorem card_topHalf : #{c : Fin (2 * k) | k ≤ (c : ℕ)} = k := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * k))))
    (fun c : Fin (2 * k) => (c : ℕ) < k)
  rw [Fin.card_filter_val_lt, card_univ, Fintype.card_fin] at h
  simp only [not_lt] at h
  omega

/-- **Plücker coordinates specialize to minors**, the case `J = [k+1, 2k]`: `φ(P_J(z)) = 1`. -/
@[cluster_algebras "lem_mat_specialization_minors"]
theorem matSpecialization_pluckerCoord_topHalf :
    matSpecialization k (pluckerCoord (complexGenericMatrix k (2 * k))
      {c : Fin (2 * k) | k ≤ (c : ℕ)}) = 1 := by
  rw [matSpecialization_pluckerCoord card_topHalf]
  have hK : matRowSet k {c : Fin (2 * k) | k ≤ (c : ℕ)} = ∅ := by
    ext r
    simp [mem_matRowSet]
    omega
  have hL : matColSet k {c : Fin (2 * k) | k ≤ (c : ℕ)} = ∅ := by
    ext j
    simp [mem_matColSet, Fin.castLE]
  rw [hK, hL, minor_of_card_eq _ card_empty card_empty, det_isEmpty]

/-- The bottom half `[1, k]` of the columns: `φ(P_{[1,k]}(z)) = det y`. -/
theorem matSpecialization_pluckerCoord_bottomHalf :
    matSpecialization k (pluckerCoord (complexGenericMatrix k (2 * k))
      {c : Fin (2 * k) | (c : ℕ) < k}) = (complexGenericMatrix k k).det := by
  have hcard : #{c : Fin (2 * k) | (c : ℕ) < k} = k := by
    rw [Fin.card_filter_val_lt]
    omega
  rw [matSpecialization_pluckerCoord hcard]
  have hK : matRowSet k {c : Fin (2 * k) | (c : ℕ) < k} = univ := by
    ext r
    simp [mem_matRowSet]
    omega
  have hL : matColSet k {c : Fin (2 * k) | (c : ℕ) < k} = univ := by
    ext j
    simp [mem_matColSet, Fin.castLE]
  rw [hK, hL, minor_of_card_eq _ (card_fin k) (card_fin k)]
  congr 1
  ext i j
  simp [orderEmbOfFin_univ_fin]

end Specialization

end ClusterAlgebras

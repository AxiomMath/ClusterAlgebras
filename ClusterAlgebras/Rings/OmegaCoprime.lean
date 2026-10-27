/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.Omega
public import ClusterAlgebras.Rings.MinorIrreducible
public import ClusterAlgebras.Rings.MatSpecialization
public import ClusterAlgebras.TotalPositivity.DesnanotJacobi

/-!
# The flag minor `P_{Jbc}` does not divide `Ω`

For the generic `k × k` matrix `z` over `ℂ`, write `P_X` for the flag minor `P_X(z)`. For
`2 ≤ b < c ≤ k - 1` put `a = b - 1`, `d = c + 1` and `J = [b + 1, c - 1]`, and write `Ja` for
`J ∪ {a}`, `Jbcd` for `J ∪ {b, c, d}`, and so on. Put `Ω = P_{Jb} P_{Jacd} - P_{Ja} P_{Jbcd}`.
The main result is that `P_{Jbc}` does not divide `Ω` in `ℂ[z]` [FWZ].

The proof follows [FWZ]. Let `g = |Jbc|` and let `f` be the substitution setting `z_{ia} = 0` for
the first `g` rows `i`. It fixes the minors whose columns avoid `a`, among them `P_{Jbc}`; it
kills `P_{Ja}`, whose column `a` lies in its first `g - 1` rows; and in `P_{Jacd}` it leaves a
column `a` whose only nonzero entry is `z_{g+1,a}`, so that `f(P_{Jacd}) = ± z_{g+1,a} M` for a
minor `M` on the columns `Jcd`. A divisibility `P_{Jbc} ∣ Ω` would then give
`P_{Jbc} ∣ ± P_{Jb} z_{g+1,a} M`. Since `P_{Jbc}` is irreducible, hence prime in the factorial
ring `ℂ[z]`, it would divide `P_{Jb}`, `z_{g+1,a}` or `M`, all minors whose column sets miss `b`
or `c`.

## Main results

* `ClusterAlgebras.minor_congr`: a minor depends only on the entries in its rows and columns.
* `ClusterAlgebras.minor_eq_zero_of_forall_eq_zero`: a minor with a column vanishing on its rows
  is zero.
* `ClusterAlgebras.not_flagMinor_mvPolynomialX_dvd_omega`: `P_{Jbc} ∤ Ω` for the matrix of
  indeterminates over any field.
* `ClusterAlgebras.not_flagMinor_complexGenericMatrix_dvd_omega`: `P_{Jbc} ∤ Ω` in `ℂ[z]`.

## Implementation notes

* Indices are 0-based, as in `ClusterAlgebras.flagMinor_complexGenericMatrix_omega`: the
  1-based `2 ≤ b < c ≤ k - 1`, `a = b - 1`, `d = c + 1` of [FWZ] become columns `a b c d : Fin k`
  with `a + 1 = b`, `b < c` and `c + 1 = d`, and `J = [b + 1, c - 1]` becomes `Finset.Ioo b c`.
  The hypothesis `k ≥ 4` of [FWZ] follows from the existence of four distinct columns.
* [FWZ] rules out `P_{Jbc} ∣ z_{g+1,a}` by degree. Here `z_{g+1,a}` is read as the `1 × 1`
  minor on the column set `{a}`, and all three cases are handled alike: a minor does not divide a
  minor whose column set fails to contain its own (`not_minor_mvPolynomialX_dvd_of_not_subset`).
  Neither the sign of the Laplace expansion nor the row set of `M` needs to be identified.
* The result is proved for the matrix of indeterminates over any field `K`, where the polynomial
  ring is factorial, and then read off for `ℂ`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapter 6*.
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial Matrix Finset

section Minor

variable {R : Type*} [CommRing R] {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]

/-- A minor depends only on the entries in its rows and columns: if `M` and `N` agree on `I × J`,
then `Δ_{I,J}(M) = Δ_{I,J}(N)`. -/
theorem minor_congr {M N : Matrix ι κ R} {I : Finset ι} {J : Finset κ}
    (h : ∀ i ∈ I, ∀ j ∈ J, M i j = N i j) : minor M I J = minor N I J := by
  unfold minor
  split_ifs with hc
  · congr 1
    ext s t
    exact h _ (orderEmbOfFin_mem _ _ _) _ (orderEmbOfFin_mem _ _ _)
  · rfl

/-- A minor vanishes when one of its columns vanishes on all of its rows. -/
theorem minor_eq_zero_of_forall_eq_zero {M : Matrix ι κ R} {I : Finset ι} {J : Finset κ}
    {c : κ} (hc : c ∈ J) (h : ∀ i ∈ I, M i c = 0) : minor M I J = 0 := by
  unfold minor
  split_ifs with hcard
  · obtain ⟨t, rfl⟩ : c ∈ Set.range (J.orderEmbOfFin hcard) := by
      rwa [range_orderEmbOfFin]
    exact det_eq_zero_of_column_eq_zero t fun s => h _ (orderEmbOfFin_mem _ _ _)
  · rfl

end Minor

section ZeroColumn

variable {K : Type*} [CommRing K] {n : ℕ} (a : Fin n) (g : ℕ)

/-- The substitution of `K[z]` setting `z_{ia} = 0` for the rows `i < g`. -/
private noncomputable def zeroColumn :
    MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K :=
  eval₂Hom C fun p => if p.2 = a ∧ (p.1 : ℕ) < g then 0 else X p

private theorem map_zeroColumn_apply (i j : Fin n) :
    (mvPolynomialX (Fin n) (Fin n) K).map (zeroColumn a g) i j =
      if j = a ∧ (i : ℕ) < g then 0 else mvPolynomialX (Fin n) (Fin n) K i j := by
  simp [zeroColumn, mvPolynomialX_apply]

/-- `zeroColumn a g` fixes the flag minors whose columns avoid `a`. -/
private theorem zeroColumn_flagMinor_of_notMem {S : Finset (Fin n)} (hS : a ∉ S) :
    zeroColumn a g (flagMinor (mvPolynomialX (Fin n) (Fin n) K) S) =
      flagMinor (mvPolynomialX (Fin n) (Fin n) K) S := by
  rw [RingHom.map_flagMinor, flagMinor, flagMinor]
  exact minor_congr fun i _ j hj => by
    rw [map_zeroColumn_apply, if_neg (by rintro ⟨rfl, -⟩; exact hS hj)]

/-- `zeroColumn a g` kills the flag minors on at most `g` rows whose columns contain `a`. -/
private theorem zeroColumn_flagMinor_eq_zero {S : Finset (Fin n)} (ha : a ∈ S)
    (hS : S.card ≤ g) : zeroColumn a g (flagMinor (mvPolynomialX (Fin n) (Fin n) K) S) = 0 := by
  rw [RingHom.map_flagMinor, flagMinor]
  refine minor_eq_zero_of_forall_eq_zero ha fun i hi => ?_
  rw [map_zeroColumn_apply, if_pos]
  refine ⟨rfl, ?_⟩
  simp only [initialRows, mem_filter, mem_univ, true_and] at hi
  omega

/-- On a flag minor on `g + 1` rows whose columns contain `a`, `zeroColumn a g` leaves a column
`a` whose only nonzero entry is `z_{ga}`: the Laplace expansion along it is a single term. -/
private theorem zeroColumn_flagMinor_eq_mul {S : Finset (Fin n)} (ha : a ∈ S)
    (hS : S.card = g + 1) (hg : g < n) :
    zeroColumn a g (flagMinor (mvPolynomialX (Fin n) (Fin n) K) S) =
      (-1) ^ (#{i ∈ initialRows n S.card | i < ⟨g, hg⟩} + #{j ∈ S | j < a}) *
          minor (mvPolynomialX (Fin n) (Fin n) K) {⟨g, hg⟩} {a} *
        minor (mvPolynomialX (Fin n) (Fin n) K) ((initialRows n S.card).erase ⟨g, hg⟩)
          (S.erase a) := by
  have hr : (⟨g, hg⟩ : Fin n) ∈ initialRows n S.card := by simp [initialRows, hS]
  rw [RingHom.map_flagMinor, flagMinor,
    minor_eq_mul_minor_erase _ (card_initialRows (by omega)) hr ha, minor_singleton]
  · rw [map_zeroColumn_apply, if_neg (by simp), minor_congr]
    intro i _ j hj
    rw [map_zeroColumn_apply, if_neg fun h => (mem_erase.1 (h.1 ▸ hj)).1 rfl]
  · intro i hi hir
    rw [map_zeroColumn_apply, if_pos]
    refine ⟨rfl, ?_⟩
    simp only [initialRows, mem_filter, mem_univ, true_and, hS] at hi
    have : (i : ℕ) ≠ g := fun h => hir (Fin.ext h)
    omega

end ZeroColumn

/-- Let `z` be the matrix of indeterminates over a field. For columns `a, b, c, d` with
`a + 1 = b < c` and `c + 1 = d`, and `J = (b, c)`, `P_{Jbc}(z)` does not divide
`P_{Jb}(z) P_{Jacd}(z) - P_{Ja}(z) P_{Jbcd}(z)`. -/
theorem not_flagMinor_mvPolynomialX_dvd_omega {K : Type*} [Field K] {n : ℕ} {a b c d : Fin n}
    (hab : (a : ℕ) + 1 = b) (hbc : b < c) (hcd : (c : ℕ) + 1 = d) :
    ¬flagMinor (mvPolynomialX (Fin n) (Fin n) K) (Ioo b c ∪ {b, c}) ∣
      flagMinor (mvPolynomialX (Fin n) (Fin n) K) (Ioo b c ∪ {b}) *
          flagMinor (mvPolynomialX (Fin n) (Fin n) K) (Ioo b c ∪ {a, c, d}) -
        flagMinor (mvPolynomialX (Fin n) (Fin n) K) (Ioo b c ∪ {a}) *
          flagMinor (mvPolynomialX (Fin n) (Fin n) K) (Ioo b c ∪ {b, c, d}) := by
  classical
  set J := Ioo b c with hJ
  have hbc' : (b : ℕ) < c := hbc
  have hd := d.isLt
  have haJ : a ∉ J := by
    simp only [J, mem_Ioo]
    omega
  have hbJ : b ∉ J := by simp [J]
  have hcJ : c ∉ J := by simp [J]
  have hdJ : d ∉ J := by
    simp only [J, mem_Ioo]
    omega
  obtain ⟨hab', hac, had, hbd, hcd'⟩ : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have hJcard : J.card + 3 ≤ n := by rw [hJ, Fin.card_Ioo]; omega
  have cJbc : (J ∪ {b, c}).card = J.card + 2 := by
    rw [card_union_of_disjoint (by simp [hbJ, hcJ]), card_pair hbc.ne]
  have cJb : (J ∪ {b}).card = J.card + 1 := by
    rw [card_union_of_disjoint (by simp [hbJ]), card_singleton]
  have cJa : (J ∪ {a}).card = J.card + 1 := by
    rw [card_union_of_disjoint (by simp [haJ]), card_singleton]
  have cJacd : (J ∪ {a, c, d}).card = J.card + 3 := by
    rw [card_union_of_disjoint (by simp [haJ, hcJ, hdJ]),
      card_insert_of_notMem (by simp [hac, had]), card_pair hcd']
  have hI : (initialRows n (J ∪ {b, c}).card).Nonempty := by
    rw [← card_pos, card_initialRows (by omega)]; omega
  have hP : Prime (flagMinor (mvPolynomialX (Fin n) (Fin n) K) (J ∪ {b, c})) :=
    (irreducible_minor_mvPolynomialX hI (card_initialRows (by omega))).prime
  intro hdvd
  have h := map_dvd (zeroColumn (K := K) a (J.card + 2)) hdvd
  rw [map_sub, map_mul, map_mul, zeroColumn_flagMinor_eq_zero a _ (S := J ∪ {a}) (by simp)
    (by omega), zero_mul, sub_zero,
    zeroColumn_flagMinor_of_notMem a _ (S := J ∪ {b, c}) (by simp [haJ, hab', hac]),
    zeroColumn_flagMinor_of_notMem a _ (S := J ∪ {b}) (by simp [haJ, hab']),
    zeroColumn_flagMinor_eq_mul a _ (S := J ∪ {a, c, d}) (by simp) (by omega) (by omega)] at h
  rcases hP.dvd_or_dvd h with h | h
  · refine not_minor_mvPolynomialX_dvd_of_not_subset (card_initialRows (by omega))
      (Or.inr fun hs => ?_) h
    simpa [hcJ, hbc.ne'] using hs (by simp : c ∈ J ∪ {b, c})
  rcases hP.dvd_or_dvd h with h | h
  · rcases hP.dvd_or_dvd h with h | h
    · exact hP.not_unit (isUnit_of_dvd_unit h (isUnit_neg_one.pow _))
    · refine not_minor_mvPolynomialX_dvd_of_not_subset ?_ (Or.inr fun hs => ?_) h
      · simp
      · simpa [hab'.symm] using hs (by simp : b ∈ J ∪ {b, c})
  · refine not_minor_mvPolynomialX_dvd_of_not_subset ?_ (Or.inr fun hs => ?_) h
    · rw [card_erase_of_mem (by rw [initialRows, mem_filter, cJacd]; exact ⟨mem_univ _, by simp⟩),
        card_erase_of_mem (by simp), card_initialRows (by omega)]
    · simpa [hbJ, hab'.symm, hbc.ne, hbd] using hs (by simp : b ∈ J ∪ {b, c})

/-- Let `z` be the generic `k × k` matrix over `ℂ` and `P_X = P_X(z)`. For columns `a, b, c, d`
with `a + 1 = b < c` and `c + 1 = d`, and `J = (b, c)` the columns strictly between `b` and `c`,
`P_{Jbc}` does not divide `P_{Jb} P_{Jacd} - P_{Ja} P_{Jbcd}` in `ℂ[z]`. -/
@[cluster_algebras "lem_omega_coprime"]
theorem not_flagMinor_complexGenericMatrix_dvd_omega {k : ℕ} {a b c d : Fin k}
    (hab : (a : ℕ) + 1 = b) (hbc : b < c) (hcd : (c : ℕ) + 1 = d) :
    ¬flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {b, c}) ∣
      flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {b}) *
          flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {a, c, d}) -
        flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {a}) *
          flagMinor (complexGenericMatrix k k) (Finset.Ioo b c ∪ {b, c, d}) := by
  rw [complexGenericMatrix_eq_mvPolynomialX]
  exact not_flagMinor_mvPolynomialX_dvd_omega hab hbc hcd

end ClusterAlgebras

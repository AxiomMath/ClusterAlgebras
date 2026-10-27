/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.LaurentPhenomenon.Trivialization
public import ClusterAlgebras.Folding.EntryIndependent
public import ClusterAlgebras.Folding.SetMutationSeed

/-!
# Folding: the exchange relation of an orbit mutation

Given folding data, let `(x̃, B̃)` be a `(G, ψ)`-admissible seed, `r` a mutable label and
`K = θ(r)`. Mutating `(x̃, B̃)` along the increasing sequence `s_K` gives an extended cluster
`(x'₁, …, x'_m)` whose entries lie in `P = ℚ_sf(w̃)`, and for every `k ∈ K`
`ψ(x'_k) = (M⁺_r(x̃ᴳ, B̃ᴳ) + M⁻_r(x̃ᴳ, B̃ᴳ)) / x^G_r`: `ψ` sends the exchange relation at `k` in
the seed to the exchange relation at `r` in the folded seed.

Since `b_{kk'} = 0` for `k, k' ∈ K` (`ClusterAlgebras.IsGroupAdmissible.eq_zero`),
`x'_k = (M⁺_k + M⁻_k) / x_k` with `M^±_k = M^±_k(x̃, B̃)`. The map `ψ` is multiplicative and
`ψ(x_i) = x^G_p` for `i ∈ θ(p)`, so `ψ(M⁺_k) = ∏_p (x^G_p)^{e_p}` with
`e_p = ∑_{i ∈ θ(p)} max(0, b_{ik})`. The entries `b_{ik}`, `i ∈ θ(p)`, have one weak sign
(`ClusterAlgebras.IsGroupAdmissible.mul_nonneg`), so `e_p = max(0, ∑_{i ∈ θ(p)} b_{ik})`, which
is `max(0, b^G_{pr})` because `k ∈ θ(r)`. Hence `ψ(M⁺_k) = M⁺_r(x̃ᴳ, B̃ᴳ)`, and likewise
`ψ(M⁻_k) = M⁻_r(x̃ᴳ, B̃ᴳ)`; finally `ψ` preserves sums and quotients, and `ψ(x_k) = x^G_r`.

## Main results

* `ClusterAlgebras.IsFoldAdmissibleSeed.seedMutationSeq_extCluster_mem_universalSemifield`:
  mutation keeps the entries of the extended cluster of an admissible seed in `P`.
* `ClusterAlgebras.IsFoldAdmissibleSeed.foldValue_seedMutationSeq_increasingSeq_extCluster`:
  `ψ(x'_k) = (M⁺_r(x̃ᴳ, B̃ᴳ) + M⁻_r(x̃ᴳ, B̃ᴳ)) / x^G_r` for `k ∈ θ(r)`.

## Implementation notes

* The membership `x'_k ∈ P` is stated at every position after mutation along any sequence,
  not only for `k ∈ θ(r)` after `μ_{s_K}`, since `P` is closed under products, sums and
  quotients.

* The map `ψ` is applied through `ClusterAlgebras.foldValue`, its extension by `0` to `F`.
  On `P` it is multiplicative and additive (`ClusterAlgebras.foldValue_mul`,
  `ClusterAlgebras.foldValue_add`, …), which is all the proof uses. The exchange monomials are
  handled in the form `∏ᵢ xᵢ ^ max(0, b_{ik})` of `ClusterAlgebras.exchangeMonomialPos_eq_prod`,
  with `max(0, ·)` written `Int.toNat`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Section 4.4.
-/

@[expose] public section

namespace ClusterAlgebras

open MulAction

variable {G : Type*} [Group G] {m n mG nG : ℕ} [MulAction G (Fin m)] {hmn : n ≤ m}

/-! ### Positive parts of sums of one weak sign -/

/-- If the integers `f i`, `i ∈ s`, have one weak sign, then the positive part of their sum is
the sum of their positive parts. -/
theorem sum_toNat_eq_toNat_sum_of_mul_nonneg {ι : Type*} {s : Finset ι} {f : ι → ℤ}
    (hf : ∀ i ∈ s, ∀ i' ∈ s, 0 ≤ f i * f i') :
    ∑ i ∈ s, (f i).toNat = (∑ i ∈ s, f i).toNat := by
  by_cases h : ∀ i ∈ s, 0 ≤ f i
  · apply @Nat.cast_injective ℤ
    rw [Nat.cast_sum, Int.toNat_of_nonneg (Finset.sum_nonneg h)]
    exact Finset.sum_congr rfl fun i hi => Int.toNat_of_nonneg (h i hi)
  · push Not at h
    obtain ⟨i₀, hi₀, hneg⟩ := h
    have hle : ∀ i ∈ s, f i ≤ 0 := fun i hi => by nlinarith [hf i₀ hi₀ i hi]
    rw [Finset.sum_eq_zero fun i hi => Int.toNat_eq_zero.2 (hle i hi),
      Int.toNat_eq_zero.2 (Finset.sum_nonpos hle)]

/-- Regrouping a product over the indices along the orbits of `θ`: if the exponents `f i` have
one weak sign over each orbit, then
`∏ᵢ (y_{θ.label i}) ^ max(0, f i) = ∏_p (y_p) ^ max(0, ∑_{i ∈ θ(p)} f i)`. -/
theorem OrbitLabelling.prod_pow_toNat_label {M : Type*} [CommMonoid M]
    (θ : OrbitLabelling G m n mG nG) {f : Fin m → ℤ}
    (hf : ∀ p, ∀ i ∈ θ.orbit p, ∀ i' ∈ θ.orbit p, 0 ≤ f i * f i') (y : Fin mG → M) :
    ∏ i, y (θ.label i) ^ (f i).toNat = ∏ p, y p ^ (∑ i ∈ θ.orbit p, f i).toNat := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ θ.label]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hs : (Finset.univ.filter fun i => θ.label i = p) = θ.orbit p := by
    ext i
    simp [θ.mem_orbit_iff_label_eq]
  rw [hs, Finset.prod_congr rfl (g := fun i => y p ^ (f i).toNat) fun i hi => by
      rw [(θ.mem_orbit_iff_label_eq).1 hi],
    Finset.prod_pow_eq_pow_sum, sum_toNat_eq_toNat_sum_of_mul_nonneg (hf p)]

/-! ### `ψ` on `P` -/

section Seeds

variable {F : Type*} [Field F] [CharZero F] {w : Fin m → F} [Fact (AlgebraicIndependent ℚ w)]
  {FG : Type*} [Field FG] [CharZero FG] {z : Fin mG → FG} [Fact (AlgebraicIndependent ℚ z)]
  (ψ : FZSemifieldHom (universalSemifield w) (universalSemifield z))

/-- `ψ(1) = 1`. -/
theorem foldValue_one : foldValue ψ (1 : F) = 1 := by
  rw [foldValue_of_mem ψ one_mem_universalSemifield]
  exact congrArg Subtype.val (map_one ψ)

/-- `ψ(xy) = ψ(x) ψ(y)` for `x, y ∈ P`. -/
theorem foldValue_mul {x y : F} (hx : x ∈ universalSemifield w) (hy : y ∈ universalSemifield w) :
    foldValue ψ (x * y) = foldValue ψ x * foldValue ψ y := by
  rw [foldValue_of_mem ψ hx, foldValue_of_mem ψ hy,
    foldValue_of_mem ψ (mul_mem_universalSemifield hx hy), ← universalSemifield.coe_mul,
    ← map_mul, universalSemifield.mk_mul_mk]

/-- `ψ(x ⊕ y) = ψ(x) ⊕ ψ(y)` for `x, y ∈ P`. -/
theorem foldValue_add {x y : F} (hx : x ∈ universalSemifield w) (hy : y ∈ universalSemifield w) :
    foldValue ψ (x + y) = foldValue ψ x + foldValue ψ y := by
  rw [foldValue_of_mem ψ hx, foldValue_of_mem ψ hy,
    foldValue_of_mem ψ (add_mem_universalSemifield hx hy), ← universalSemifield.coe_add,
    ← map_add, universalSemifield.mk_add_mk]

/-- `ψ(x / y) = ψ(x) / ψ(y)` for `x, y ∈ P`. -/
theorem foldValue_div {x y : F} (hx : x ∈ universalSemifield w) (hy : y ∈ universalSemifield w) :
    foldValue ψ (x / y) = foldValue ψ x / foldValue ψ y := by
  rw [foldValue_of_mem ψ hx, foldValue_of_mem ψ hy,
    foldValue_of_mem ψ (div_mem_universalSemifield hx hy), ← universalSemifield.coe_div,
    ← map_div, universalSemifield.mk_div_mk]

/-- `ψ(x ^ e) = ψ(x) ^ e` for `x ∈ P` and `e ∈ ℕ`. -/
theorem foldValue_pow {x : F} (hx : x ∈ universalSemifield w) (e : ℕ) :
    foldValue ψ (x ^ e) = foldValue ψ x ^ e := by
  rw [foldValue_of_mem ψ hx, foldValue_of_mem ψ (pow_mem_universalSemifield hx e),
    ← universalSemifield.coe_pow, ← map_pow]
  rfl

/-- `ψ` sends a finite product of elements of `P` to the product of their images. -/
theorem foldValue_prod {ι : Type*} (s : Finset ι) {f : ι → F}
    (hf : ∀ i ∈ s, f i ∈ universalSemifield w) :
    foldValue ψ (∏ i ∈ s, f i) = ∏ i ∈ s, foldValue ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using foldValue_one ψ
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, f i ∈ universalSemifield w := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      foldValue_mul ψ (hf a (Finset.mem_insert_self a s)) (prod_mem_universalSemifield hs),
      ih hs]

/-- `ψ` sends the positive exchange monomial of a tuple of elements of `P` to
`∏ᵢ ψ(xᵢ) ^ max(0, b_{ik})`. -/
theorem foldValue_exchangeMonomialPos {m' n' : ℕ} {x : Fin m' → F}
    (hx : ∀ i, x i ∈ universalSemifield w) (B : Matrix (Fin m') (Fin n') ℤ) (k : Fin n') :
    foldValue ψ (exchangeMonomialPos x B k) = ∏ i, foldValue ψ (x i) ^ (B i k).toNat := by
  rw [exchangeMonomialPos_eq_prod,
    foldValue_prod ψ _ fun i _ => pow_mem_universalSemifield (hx i) _]
  exact Finset.prod_congr rfl fun i _ => foldValue_pow ψ (hx i) _

/-- `ψ` sends the negative exchange monomial of a tuple of elements of `P` to
`∏ᵢ ψ(xᵢ) ^ max(0, -b_{ik})`. -/
theorem foldValue_exchangeMonomialNeg {m' n' : ℕ} {x : Fin m' → F}
    (hx : ∀ i, x i ∈ universalSemifield w) (B : Matrix (Fin m') (Fin n') ℤ) (k : Fin n') :
    foldValue ψ (exchangeMonomialNeg x B k) = ∏ i, foldValue ψ (x i) ^ (-B i k).toNat := by
  rw [exchangeMonomialNeg_eq_prod,
    foldValue_prod ψ _ fun i _ => pow_mem_universalSemifield (hx i) _]
  exact Finset.prod_congr rfl fun i _ => foldValue_pow ψ (hx i) _

/-! ### The exchange relation of an orbit mutation -/

variable {ψ}

/-- **Folded exchange relation, membership.** Mutation of a `(G, ψ)`-admissible seed along any
sequence keeps the entries of the extended cluster in `P = ℚ_sf(w̃)`. -/
@[cluster_algebras "lem_folded_exchange"]
theorem IsFoldAdmissibleSeed.seedMutationSeq_extCluster_mem_universalSemifield
    {S : SeedData F m n} (hS : IsFoldAdmissibleSeed G hmn ψ S) (s : List (Fin n)) (i : Fin m) :
    (seedMutationSeq hmn S s).extCluster i ∈ universalSemifield w :=
  ClusterAlgebras.seedMutationSeq_extCluster_mem_universalSemifield hmn hS.mem s i

/-- **Folded exchange relation.** Let `(x̃, B̃)` be `(G, ψ)`-admissible, `r` a mutable label and
`(x'₁, …, x'_m)` the extended cluster of `μ_{s_{θ(r)}}(x̃, B̃)`. Then for every `k ∈ θ(r)`,
`ψ(x'_k) = (M⁺_r(x̃ᴳ, B̃ᴳ) + M⁻_r(x̃ᴳ, B̃ᴳ)) / x^G_r`. -/
@[cluster_algebras "lem_folded_exchange"]
theorem IsFoldAdmissibleSeed.foldValue_seedMutationSeq_increasingSeq_extCluster
    (θ : OrbitLabelling G m n mG nG) {S : SeedData F m n} (hS : IsFoldAdmissibleSeed G hmn ψ S)
    (r : Fin nG) {k : Fin n} (hk : k ∈ θ.cols hmn r) :
    foldValue ψ
        ((seedMutationSeq hmn S (increasingSeq (θ.cols hmn r))).extCluster (Fin.castLE hmn k)) =
      (exchangeMonomialPos (foldedSeed θ ψ S).extCluster (foldedSeed θ ψ S).extExchangeMatrix r +
          exchangeMonomialNeg (foldedSeed θ ψ S).extCluster
            (foldedSeed θ ψ S).extExchangeMatrix r) /
        (foldedSeed θ ψ S).extCluster (Fin.castLE θ.le r) := by
  have hK : ∀ k ∈ θ.cols hmn r, ∀ k' ∈ θ.cols hmn r,
      S.extExchangeMatrix (Fin.castLE hmn k) k' = 0 := fun k hk k' hk' =>
    hS.admissible.eq_zero k k' (θ.mem_orbit_of_mem (θ.mem_cols.1 hk) (θ.mem_cols.1 hk'))
  have hx : ∀ i, foldValue ψ (S.extCluster i) = (foldedSeed θ ψ S).extCluster (θ.label i) :=
    fun i => hS.foldValue_eq _ _ (θ.mem_orbit_of_mem (θ.mem_orbit_label i) (θ.rep_mem _))
  have hsign : ∀ p, ∀ i ∈ θ.orbit p, ∀ i' ∈ θ.orbit p,
      0 ≤ S.extExchangeMatrix i k * S.extExchangeMatrix i' k := fun p i hi i' hi' =>
    hS.admissible.mul_nonneg i i' (θ.mem_orbit_of_mem hi hi') k
  have hsign' : ∀ p, ∀ i ∈ θ.orbit p, ∀ i' ∈ θ.orbit p,
      0 ≤ -S.extExchangeMatrix i k * -S.extExchangeMatrix i' k := fun p i hi i' hi' => by
    rw [neg_mul_neg]
    exact hsign p i hi i' hi'
  have hentry : ∀ p, (foldedSeed θ ψ S).extExchangeMatrix p r =
      ∑ i ∈ θ.orbit p, S.extExchangeMatrix i k := fun p =>
    foldedMatrix_apply_eq_sum_of_mem_cols hS.admissible θ p r hk
  have hlabel : θ.label (Fin.castLE hmn k) = Fin.castLE θ.le r :=
    (θ.mem_orbit_iff_label_eq).1 (θ.mem_cols.1 hk)
  have hpos := exchangeMonomialPos_mem_universalSemifield hS.mem S.extExchangeMatrix k
  have hneg := exchangeMonomialNeg_mem_universalSemifield hS.mem S.extExchangeMatrix k
  rw [seedMutationSeq_increasingSeq_extCluster_of_mem S hK hk,
    foldValue_div ψ (add_mem_universalSemifield hpos hneg) (hS.mem _), foldValue_add ψ hpos hneg,
    foldValue_exchangeMonomialPos ψ hS.mem, foldValue_exchangeMonomialNeg ψ hS.mem,
    exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod, hx, hlabel]
  simp only [hx]
  rw [θ.prod_pow_toNat_label hsign, θ.prod_pow_toNat_label hsign']
  simp only [hentry, Finset.sum_neg_distrib]

end Seeds

end ClusterAlgebras

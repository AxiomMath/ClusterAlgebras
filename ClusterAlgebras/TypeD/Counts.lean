/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Semifield.Universal
public import ClusterAlgebras.Coefficients.Trivialization
public import ClusterAlgebras.TypeD.Count
public import ClusterAlgebras.TypeD.Reduction

/-!
# Cluster variables and clusters in type `D_n`

A seed pattern of type `D_n` has `n²` cluster variables and `(3n - 2)/n · binom(2n - 2, n - 1)`
clusters. For `Σ•_n`, the elements `P_γ` are written as subtraction-free expressions in the
initial extended cluster; trivialising the coefficients gives `n²` visibly distinct Laurent
polynomials, and `ClusterAlgebras.IsSeedPattern.exists_rescaling_of_zSpanCondition` transports
the counts to every pattern of type `D_n`.

## Main definitions

* `ClusterAlgebras.TypeD.laurentWeight`: the weights `μ_m` of the expansion of `P[u, v]`.
* `ClusterAlgebras.TypeD.laurentE0`: the coefficient-free expressions `E⁰_γ`.

## Main statements

* `ClusterAlgebras.TypeD.segValue_seg_eq_sum`, `arcValue_mem_universalSemifield`: the elements
  `P_γ` in the initial extended cluster.
* `ClusterAlgebras.TypeD.laurentE0_injective`: the `E⁰_γ` are distinct.
* `ClusterAlgebras.TypeD.arcValue_injective_and_range`, `bijOn_image_arcValue_patternClusters`,
  `encard_dPattern`: cluster variables and clusters of `Σ•_n`.
* `ClusterAlgebras.IsSeedPattern.encard_of_isPatternOfType_D`: the counts in type `D_n`.

## Implementation notes

* Indices start at `0`. The one-based `u ∈ [1, n]`, `u < v ≤ u + n` and weights
  `μ_m = 1` (`v ≤ n`), resp. `μ_m = λ̄` (`m ≤ n - 1`), `μ_n = 1`, `μ_m = λ` (`m ≥ n + 1`) for
  `v > n` become `u ∈ [0, n - 1]`, `u < v ≤ u + n` and `μ_m = 1` (`v < n`), resp. `μ_m = λ̄`
  (`m < n - 1`), `μ_{n-1} = 1`, `μ_m = λ` (`m ≥ n`) for `v ≥ n`.
* "Built with sums, products and quotients only" is membership in the universal semifield
  `ℚ_sf(x̃(T∘, ℓ∘))`.
* The number of clusters `(3n - 2)/n · binom(2n - 2, n - 1)` is stated through a natural number
  `N` with `n N = (3n - 2) binom(2n - 2, n - 1)`, which determines it; counts are `Set.encard`,
  which records finiteness too.
* The distinctness of the `E⁰_γ` is proved by clearing denominators: `E⁰_γ · ∏ₖ zₖ` is the value
  at `z` of a polynomial with rational coefficients, so by algebraic independence two equal
  `E⁰_γ(z)` give equal values `E⁰_γ(w)` at every point `w` with positive rational entries. The
  points `w = (1, …, 1)` and `w` with one entry `s ∈ {2, n}` and the others `1` then separate
  the kinds of arcs, the positions of radii, and the ordinary arcs, in place of a comparison of
  sets of Laurent monomials.
* In the transfer of the counts, instead of trivializing the coefficients of `Σ̄` and rescaling
  `Σ•_n` to the trivialized pattern, the rescaling `ψ : ℚ_sf(x̃(t∘)) → ℚ_sf(x̃̄(t∘))` given by
  `IsSeedPattern.exists_rescaling_of_zSpanCondition` is composed with the specialization
  `ℚ_sf(x̃̄(t∘)) → ℚ_sf(y)` sending the frozen variables to `1` and the cluster variables to
  indeterminates `y`; it sends the monomial factors `ε̄(φ(x_{i;t}))` to `1`, which is what the
  trivialization achieves.
-/

@[expose] public section

namespace ClusterAlgebras

namespace TypeD

variable (K : Type*) [Field K] {n : ℕ} [NeZero n]

/-! ### Elementary facts on residues, sheets and the elements `P[u, v]` -/

omit [NeZero n] in
/-- An indeterminate of `F_n` is nonzero. -/
private theorem cnt_var_ne_zero (v : DVar n) : var K v ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (DVar n) K) (DField K n))).2
    (MvPolynomial.X_ne_zero v)

/-- The sheet of `u ∈ [0, 2n)`. -/
private theorem cnt_sheet_eq {u : ℤ} (h0 : 0 ≤ u) (h1 : u < 2 * n) :
    sheet n u = if u < n then 0 else 1 := by
  unfold sheet
  split_ifs with h
  · exact Int.ediv_eq_zero_of_lt h0 h
  · rw [show u = (u - n) + 1 * n by ring, Int.add_mul_ediv_right _ _
      (Int.natCast_ne_zero.2 (NeZero.ne n)), Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    rfl

/-- `κ(u, v)` for `0 ≤ u ≤ v < 2n`. -/
private theorem cnt_kappa_eq {u v : ℤ} (h0 : 0 ≤ u) (huv : u ≤ v) (h1 : v < 2 * n) :
    kappa n u v = (if v < n then 0 else 1) - (if u < n then 0 else 1) := by
  unfold kappa
  rw [cnt_sheet_eq h0 (by omega), cnt_sheet_eq (by omega) h1]

/-- `P[u, v] = λ^{κ(u,v)} p_ū q_v̄ - λ̄^{κ(u,v)} q_ū p_v̄` for `u < v ≤ u + n`. -/
private theorem cnt_segValue_seg_eq (hn : 3 ≤ n) {u v : ℤ} (huv : u < v) (hvu : v ≤ u + n) :
    segValue K (seg u v : DSeg n) =
      var K (.lam .plain) ^ kappa n u v * var K (.p (vtx u)) * var K (.q (vtx v)) -
        var K (.lam .notched) ^ kappa n u v * var K (.q (vtx u)) * var K (.p (vtx v)) := by
  have hb := bracket_liftVec K hn huv hvu
  have hl := cnt_var_ne_zero K (n := n) (.lam .plain)
  have hl' := cnt_var_ne_zero K (n := n) (.lam .notched)
  have hs : sheet n v = sheet n u + kappa n u v := by unfold kappa; ring
  simp only [bracket, liftVec, hs, zpow_add₀ hl, zpow_add₀ hl'] at hb
  refine mul_left_cancel₀ (zpow_ne_zero (sheet n u) (mul_ne_zero hl hl')) ?_
  rw [← hb, mul_zpow]
  ring

variable (n) in
/-- The ratio `Q_m = q_m̄ / p_m̄`. -/
private noncomputable def cntQ (m : ℤ) : DField K n :=
  var K (.q (vtx m)) / var K (.p (vtx m))

/-- `P_{β_m̄} / (p_m p_{m+1}) = λ^{κ} Q_{m+1} - λ̄^{κ} Q_m`, `κ = κ(m, m + 1)`. -/
private theorem cnt_boundary_div (hn : 3 ≤ n) (m : ℤ) :
    rowValue K (.boundary (vtx m : Fin n)) / (var K (.p (vtx m)) * var K (.p (vtx (m + 1)))) =
      var K (.lam .plain) ^ kappa n m (m + 1) * cntQ K n (m + 1) -
        var K (.lam .notched) ^ kappa n m (m + 1) * cntQ K n m := by
  have h := cnt_segValue_seg_eq K hn (u := m) (v := m + 1) (by omega) (by omega)
  rw [seg_eq_boundary] at h
  have h1 := cnt_var_ne_zero K (.p (vtx m : Fin n))
  have h2 := cnt_var_ne_zero K (.p (vtx (m + 1) : Fin n))
  change segValue K (.boundary (vtx m)) / _ = _
  rw [h, cntQ, cntQ]
  field_simp

/-- Telescoping sums over integer intervals. -/
private theorem cnt_sum_Ico_telescope {M : Type*} [AddCommGroup M] (f : ℤ → M) {a b : ℤ}
    (hab : a ≤ b) : ∑ m ∈ Finset.Ico a b, (f (m + 1) - f m) = f b - f a := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hb ih =>
    rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one hb, ih]
    abel

/-- Sums over consecutive integer intervals. -/
private theorem cnt_sum_Ico_consecutive {M : Type*} [AddCommMonoid M] (f : ℤ → M) {a b c : ℤ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ m ∈ Finset.Ico a c, f m = ∑ m ∈ Finset.Ico a b, f m + ∑ m ∈ Finset.Ico b c, f m := by
  rw [← Finset.Ico_union_Ico_eq_Ico hab hbc,
    Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a b c)]

/-- The weight `μ_m` in the expansion of `P[u, v]`: `1` if `v < n`; for `v ≥ n`, `λ̄` if
`m < n - 1`, `1` if `m = n - 1`, and `λ` if `m ≥ n`. -/
@[cluster_algebras "lem_D_laurent"]
noncomputable def laurentWeight (v m : ℤ) : DField K n :=
  if v < n then 1
  else if m < (n : ℤ) - 1 then var K (.lam .notched)
  else if m = (n : ℤ) - 1 then 1
  else var K (.lam .plain)

variable (n) in
/-- The term `μ_m (λ^κ Q_{m+1} - λ̄^κ Q_m)`, `κ = κ(m, m + 1)`, of the expansion of `P[u, v]`. -/
private noncomputable def cntTerm (v m : ℤ) : DField K n :=
  laurentWeight K v m * (var K (.lam .plain) ^ kappa n m (m + 1) * cntQ K n (m + 1) -
    var K (.lam .notched) ^ kappa n m (m + 1) * cntQ K n m)

/-- The term of `m ∈ [0, n - 1)`, where `κ(m, m + 1) = 0`. -/
private theorem cntTerm_of_lt {v m : ℤ} (hm₀ : 0 ≤ m) (hm : m + 1 < n) :
    cntTerm K n v m = laurentWeight K v m * (cntQ K n (m + 1) - cntQ K n m) := by
  rw [cntTerm, cnt_kappa_eq hm₀ (by omega) (by omega), if_pos hm, if_pos (by omega)]
  simp

/-- The term of `m = n - 1` for `v ≥ n`. -/
private theorem cntTerm_sub_one (hn : 3 ≤ n) {v : ℤ} (hv : n ≤ v) :
    cntTerm K n v ((n : ℤ) - 1) =
      var K (.lam .plain) * cntQ K n n - var K (.lam .notched) * cntQ K n ((n : ℤ) - 1) := by
  rw [cntTerm, sub_add_cancel, cnt_kappa_eq (by omega) (by omega) (by omega), laurentWeight,
    if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos (by omega)]
  simp

/-- The term of `m ∈ [n, 2n - 1)` for `v ≥ n`, where `κ(m, m + 1) = 0`. -/
private theorem cntTerm_of_le {v m : ℤ} (hm : n ≤ m) (hm' : m + 1 < 2 * n) (hv : n ≤ v) :
    cntTerm K n v m = var K (.lam .plain) * (cntQ K n (m + 1) - cntQ K n m) := by
  rw [cntTerm, cnt_kappa_eq (by omega) (by omega) hm', laurentWeight, if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

/-- **The elements `P_γ` in the initial extended cluster**: with `c_m = P_{β_m̄}` and
`p_m = p_m̄`, for `u ∈ [0, n - 1]` and `u < v ≤ u + n`,
`P[u, v] = p_u p_v ∑_{m = u}^{v - 1} μ_m c_m / (p_m p_{m+1})`. -/
@[cluster_algebras "lem_D_laurent"]
theorem segValue_seg_eq_sum (hn : 3 ≤ n) {u v : ℤ} (hu₀ : 0 ≤ u) (hun : u < n) (huv : u < v)
    (hvu : v ≤ u + n) :
    segValue K (seg u v : DSeg n) =
      var K (.p (vtx u)) * var K (.p (vtx v)) *
        ∑ m ∈ Finset.Ico u v, laurentWeight K v m * rowValue K (.boundary (vtx m)) /
          (var K (.p (vtx m)) * var K (.p (vtx (m + 1)))) := by
  have hpu := cnt_var_ne_zero K (.p (vtx u : Fin n))
  have hpv := cnt_var_ne_zero K (.p (vtx v : Fin n))
  have hterm : ∀ m : ℤ, laurentWeight K v m * rowValue K (.boundary (vtx m)) /
      (var K (.p (vtx m)) * var K (.p (vtx (m + 1)))) = cntTerm K n v m := fun m => by
    rw [mul_div_assoc, cnt_boundary_div K hn, cntTerm]
  simp_rw [hterm]
  rw [cnt_segValue_seg_eq K hn huv hvu]
  by_cases hv : v < n
  · have hS : ∀ m ∈ Finset.Ico u v, cntTerm K n v m = cntQ K n (m + 1) - cntQ K n m :=
      fun m hm => by
        rw [Finset.mem_Ico] at hm
        rw [cntTerm_of_lt K (by omega) (by omega), laurentWeight, if_pos hv, one_mul]
    rw [Finset.sum_congr rfl hS, cnt_sum_Ico_telescope _ huv.le,
      cnt_kappa_eq hu₀ huv.le (by omega), if_pos hv, if_pos hun, cntQ, cntQ]
    simp only [sub_zero, zpow_zero, one_mul]
    field_simp
  · push Not at hv
    have h1 : ∀ m ∈ Finset.Ico u ((n : ℤ) - 1),
        cntTerm K n v m = var K (.lam .notched) * (cntQ K n (m + 1) - cntQ K n m) :=
      fun m hm => by
        rw [Finset.mem_Ico] at hm
        rw [cntTerm_of_lt K (by omega) (by omega), laurentWeight, if_neg (by omega), if_pos hm.2]
    have h3 : ∀ m ∈ Finset.Ico (n : ℤ) v,
        cntTerm K n v m = var K (.lam .plain) * (cntQ K n (m + 1) - cntQ K n m) :=
      fun m hm => by
        rw [Finset.mem_Ico] at hm
        exact cntTerm_of_le K hm.1 (by omega) hv
    have hI : Finset.Ico ((n : ℤ) - 1) n = {(n : ℤ) - 1} := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [cnt_sum_Ico_consecutive _ (show u ≤ (n : ℤ) - 1 by omega) (show (n : ℤ) - 1 ≤ v by omega),
      cnt_sum_Ico_consecutive _ (show (n : ℤ) - 1 ≤ n by omega) hv, Finset.sum_congr rfl h1,
      Finset.sum_congr rfl h3, hI, Finset.sum_singleton, cntTerm_sub_one K hn hv,
      ← Finset.mul_sum, ← Finset.mul_sum, cnt_sum_Ico_telescope _ (show u ≤ (n : ℤ) - 1 by omega),
      cnt_sum_Ico_telescope _ hv, cnt_kappa_eq hu₀ huv.le (by omega), if_neg (by omega),
      if_pos hun]
    simp only [sub_zero, zpow_one, cntQ]
    field_simp
    ring

/-- **The elements `P_γ` in the initial extended cluster**: `P_{ρ^-_u} = P[u, u + n] / p_u`. -/
@[cluster_algebras "lem_D_laurent"]
theorem arcValue_radius_notched_eq (hn : 3 ≤ n) (u : Fin n) :
    arcValue K (.radius .notched u) = segValue K (seg (u : ℤ) (u + n)) / var K (.p u) := by
  rw [seg_eq_loop (by omega), vtx_coe]
  simp only [segValue, arcValue]
  rw [mul_div_cancel_left₀ _ (cnt_var_ne_zero K _)]

/-! ### The initial extended cluster -/

variable (n) in
/-- The label `k` with `ℓ∘(k) = ρ^+_a`. -/
private def cntInitialIdx (a : Fin n) : Fin n :=
  if (a : ℕ) = 0 then ⟨n - 2, by have := a.isLt; omega⟩
  else if (a : ℕ) + 1 = n then ⟨n - 1, by have := a.isLt; omega⟩
  else ⟨a - 1, by have := a.isLt; omega⟩

/-- `ℓ∘(k) = ρ^+_a` for `k = cntInitialIdx n a`. -/
private theorem cnt_initialLabelling_idx (hn : 3 ≤ n) (a : Fin n) :
    initialLabelling n (cntInitialIdx n a) = .radius .plain a := by
  have ha := a.isLt
  have hv : ∀ x : ℤ, 0 ≤ x → x < n → ((vtx x : Fin n) : ℤ) = x := fun x h0 h1 => by
    rw [vtx_val, Int.emod_eq_of_lt h0 h1]
  simp only [initialLabelling, TaggedArc.radius.injEq, true_and]
  unfold cntInitialIdx
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [Fin.ext_iff] at * <;> try omega
  all_goals first
    | (have := hv 0 le_rfl (by omega); omega)
    | (have := hv ((n : ℤ) - 1) (by omega) (by omega); omega)
    | (have := hv (((a : ℕ) - 1 : ℕ) + 1 : ℤ) (by omega) (by omega); omega)

/-- `ℓ∘ ∘ cntInitialIdx` is injective. -/
private theorem cnt_initialIdx_injective (hn : 3 ≤ n) :
    Function.Injective (cntInitialIdx n) := fun a b h => by
  have := cnt_initialLabelling_idx hn a
  rw [h, cnt_initialLabelling_idx hn b, TaggedArc.radius.injEq] at this
  exact this.2.symm

omit [NeZero n] in
/-- `ℓ̂(i) = ℓ(i)` for `i < n`. -/
private theorem cnt_extLabel_castLE (ℓ : Fin n → TaggedArc n) (i : Fin n) :
    extLabel ℓ (Fin.castLE (le_two_mul_add_two n) i) = .arc (ℓ i) := by
  simp [extLabel]

omit [NeZero n] in
/-- `ℓ̂(n + c) = β_c`. -/
private theorem cnt_extLabel_boundary (ℓ : Fin n → TaggedArc n) (c : Fin n) :
    extLabel ℓ ⟨n + c, by omega⟩ = .boundary c := by
  have := c.isLt
  rw [extLabel, dif_neg (by simp), dif_pos (by simp; omega)]
  congr 1
  ext
  simp

omit [NeZero n] in
/-- `ℓ̂(2n) = λ`. -/
private theorem cnt_extLabel_lam_plain (ℓ : Fin n → TaggedArc n) :
    extLabel ℓ ⟨2 * n, by omega⟩ = .lam .plain := by
  rw [extLabel, dif_neg (by simp; omega), dif_neg (by simp), if_pos rfl]

omit [NeZero n] in
/-- `ℓ̂(2n + 1) = λ̄`. -/
private theorem cnt_extLabel_lam_notched (ℓ : Fin n → TaggedArc n) :
    extLabel ℓ ⟨2 * n + 1, by omega⟩ = .lam .notched := by
  rw [extLabel, dif_neg (by simp; omega), dif_neg (by simp), if_neg (by simp)]

/-- The entries `p_a` of `x̃(T∘, ℓ∘)`. -/
private theorem cnt_extCluster_p (hn : 3 ≤ n) (a : Fin n) :
    (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster
      (Fin.castLE (le_two_mul_add_two n) (cntInitialIdx n a)) = var K (.p a) := by
  change rowValue K (extLabel _ _) = _
  rw [cnt_extLabel_castLE, cnt_initialLabelling_idx hn a]
  rfl

/-- The entries `P_{β_c}` of `x̃(T∘, ℓ∘)`. -/
private theorem cnt_extCluster_boundary (c : Fin n) :
    (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster ⟨n + c, by omega⟩ =
      rowValue K (.boundary c) := by
  change rowValue K (extLabel _ _) = _
  rw [cnt_extLabel_boundary]

/-- The entry `λ` of `x̃(T∘, ℓ∘)`. -/
private theorem cnt_extCluster_lam_plain :
    (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster ⟨2 * n, by omega⟩ =
      var K (.lam .plain) := by
  change rowValue K (extLabel _ _) = _
  rw [cnt_extLabel_lam_plain]
  rfl

/-- The entry `λ̄` of `x̃(T∘, ℓ∘)`. -/
private theorem cnt_extCluster_lam_notched :
    (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster ⟨2 * n + 1, by omega⟩ =
      var K (.lam .notched) := by
  change rowValue K (extLabel _ _) = _
  rw [cnt_extLabel_lam_notched]
  rfl

/-- A sum over a nonempty finset of elements of `ℚ_sf(y)` lies in `ℚ_sf(y)`. -/
private theorem cnt_sum_mem_universalSemifield {ι α F : Type*} [Field F] {y : ι → F}
    {s : Finset α} (hs : s.Nonempty) {f : α → F} (hf : ∀ a ∈ s, f a ∈ universalSemifield y) :
    ∑ a ∈ s, f a ∈ universalSemifield y := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hf a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    rw [Finset.sum_cons]
    exact add_mem_universalSemifield (hf a (Finset.mem_cons_self a s))
      (ih fun b hb => hf b (Finset.mem_cons_of_mem hb))

/-- `p_a ∈ ℚ_sf(x̃(T∘, ℓ∘))`. -/
private theorem cnt_mem_p (hn : 3 ≤ n) (a : Fin n) :
    var K (.p a) ∈
      universalSemifield (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster := by
  rw [← cnt_extCluster_p K hn a]
  exact mem_universalSemifield_self _ _

/-- `P_{β_c} ∈ ℚ_sf(x̃(T∘, ℓ∘))`. -/
private theorem cnt_mem_boundary (c : Fin n) :
    rowValue K (.boundary c) ∈
      universalSemifield (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster := by
  rw [← cnt_extCluster_boundary K c]
  exact mem_universalSemifield_self _ _

/-- `λ_τ ∈ ℚ_sf(x̃(T∘, ℓ∘))`. -/
private theorem cnt_mem_lam (τ : Tag) :
    var K (.lam τ) ∈
      universalSemifield (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster := by
  cases τ
  · rw [← cnt_extCluster_lam_plain K]
    exact mem_universalSemifield_self _ _
  · rw [← cnt_extCluster_lam_notched K]
    exact mem_universalSemifield_self _ _

/-- `μ_m ∈ ℚ_sf(x̃(T∘, ℓ∘))`. -/
private theorem cnt_mem_weight (v m : ℤ) :
    laurentWeight K (n := n) v m ∈
      universalSemifield (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster := by
  unfold laurentWeight
  split_ifs <;> first | exact one_mem_universalSemifield | exact cnt_mem_lam K _

/-- The terms `μ_m P_{β_m} / (p_m p_{m+1})` lie in `ℚ_sf(x̃(T∘, ℓ∘))`. -/
private theorem cnt_mem_term (hn : 3 ≤ n) (v m : ℤ) :
    laurentWeight K v m * rowValue K (.boundary (vtx m)) /
        (var K (.p (vtx m)) * var K (.p (vtx (m + 1)))) ∈
      universalSemifield (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster :=
  div_mem_universalSemifield (mul_mem_universalSemifield (cnt_mem_weight K v m)
    (cnt_mem_boundary K _)) (mul_mem_universalSemifield (cnt_mem_p K hn _) (cnt_mem_p K hn _))

/-- `P[u, v] ∈ ℚ_sf(x̃(T∘, ℓ∘))`. -/
private theorem cnt_mem_segValue (hn : 3 ≤ n) {u v : ℤ} (hu₀ : 0 ≤ u) (hun : u < n)
    (huv : u < v) (hvu : v ≤ u + n) :
    segValue K (seg u v : DSeg n) ∈
      universalSemifield (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster := by
  rw [segValue_seg_eq_sum K hn hu₀ hun huv hvu]
  exact mul_mem_universalSemifield (mul_mem_universalSemifield (cnt_mem_p K hn _)
    (cnt_mem_p K hn _)) (cnt_sum_mem_universalSemifield ⟨u, Finset.mem_Ico.2 ⟨le_rfl, huv⟩⟩
      fun m _ => cnt_mem_term K hn v m)

/-- `P_{α(i,j)} = P[i, i + d(i, j)]`. -/
private theorem cnt_arcValue_ordinary (hn : 3 ≤ n) (i j : Fin n) (h : 2 ≤ cdist i j) :
    arcValue K (.ordinary i j h) = segValue K (seg (i : ℤ) (i + cdist i j)) := by
  have hc := cdist_lt i j
  have hs : sheet n (i : ℤ) = 0 := by
    unfold sheet
    exact Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast i.isLt)
  simp only [arcValue]
  rw [bracket_liftVec K hn (by omega) (by omega), hs, zpow_zero, one_mul]

/-- **The elements `P_γ` in the initial extended cluster**: every `P_γ` is given by an expression
in the entries of `x̃(T∘, ℓ∘)` built with sums, products and quotients only, that is, it lies in
the universal semifield of `x̃(T∘, ℓ∘)`. -/
@[cluster_algebras "lem_D_laurent"]
theorem arcValue_mem_universalSemifield (hn : 3 ≤ n) (γ : TaggedArc n) :
    arcValue K γ ∈
      universalSemifield (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster := by
  rcases γ with ⟨i, j, h⟩ | ⟨_ | _, i⟩
  · have hc := cdist_lt i j
    rw [cnt_arcValue_ordinary K hn]
    exact cnt_mem_segValue K hn (by omega) (by exact_mod_cast i.isLt) (by omega) (by omega)
  · exact cnt_mem_p K hn i
  · rw [arcValue_radius_notched_eq K hn]
    exact div_mem_universalSemifield (cnt_mem_segValue K hn (by omega)
      (by exact_mod_cast i.isLt) (by omega) le_rfl) (cnt_mem_p K hn i)

variable {K}

/-- The coefficient-free expression `E⁰_γ` of a tagged arc in `z₁, …, z_n` (indices modulo `n`):
`E⁰_{α(i,j)} = ∑_{t=0}^{d(i,j)-1} z_i z_j / (z_{i+t} z_{i+t+1})`, `E⁰_{ρ^+_i} = z_i` and
`E⁰_{ρ^-_i} = ∑_{t=0}^{n-1} z_i / (z_{i+t} z_{i+t+1})`. -/
@[cluster_algebras "lem_D_laurent_distinct"]
def laurentE0 {F : Type*} [Field F] (z : Fin n → F) : TaggedArc n → F
  | .ordinary i j _ => ∑ t ∈ Finset.range (cdist i j),
      z i * z j / (z (vtx ((i : ℤ) + t)) * z (vtx ((i : ℤ) + t + 1)))
  | .radius .plain i => z i
  | .radius .notched i => ∑ t ∈ Finset.range n,
      z i / (z (vtx ((i : ℤ) + t)) * z (vtx ((i : ℤ) + t + 1)))

/-! ### Distinctness of the coefficient-free expressions -/

/-- `∏_{k ∉ {a, b}} X_k`. -/
private noncomputable def cntPair (a b : Fin n) : MvPolynomial (Fin n) ℚ :=
  ∏ k ∈ (Finset.univ.erase a).erase b, MvPolynomial.X k

/-- The numerator `E⁰_γ · ∏_k z_k` of `E⁰_γ`, a polynomial. -/
private noncomputable def cntNum : TaggedArc n → MvPolynomial (Fin n) ℚ
  | .ordinary i j _ => ∑ t ∈ Finset.range (cdist i j),
      MvPolynomial.X i * MvPolynomial.X j * cntPair (vtx ((i : ℤ) + t)) (vtx ((i : ℤ) + t + 1))
  | .radius .plain i => MvPolynomial.X i * ∏ k, MvPolynomial.X k
  | .radius .notched i => ∑ t ∈ Finset.range n,
      MvPolynomial.X i * cntPair (vtx ((i : ℤ) + t)) (vtx ((i : ℤ) + t + 1))

omit [NeZero n] in
/-- `c / (w_a w_b) · ∏_k w_k = c · ∏_{k ∉ {a, b}} w_k` for `a ≠ b`. -/
private theorem cnt_term_mul_prod {F : Type*} [Field F] (w : Fin n → F) (hw : ∀ k, w k ≠ 0)
    {a b : Fin n} (hab : a ≠ b) (c : F) :
    c / (w a * w b) * ∏ k, w k = c * ∏ k ∈ (Finset.univ.erase a).erase b, w k := by
  rw [← Finset.mul_prod_erase Finset.univ w (Finset.mem_univ a),
    ← Finset.mul_prod_erase (Finset.univ.erase a) w
      (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩)]
  have := hw a
  have := hw b
  field_simp

/-- Consecutive residues differ for `n ≥ 2`. -/
private theorem cnt_vtx_succ_ne (hn : 2 ≤ n) (x : ℤ) : (vtx x : Fin n) ≠ vtx (x + 1) :=
  fun h => vtx_add_ne_self (u := x) (d := 1) one_pos (by omega) h.symm

/-- `cntNum γ` evaluates to `E⁰_γ(w) · ∏_k w_k` at every `w` with nonzero entries. -/
private theorem cnt_aeval_cntNum {F : Type*} [Field F] [Algebra ℚ F] (hn : 2 ≤ n)
    (w : Fin n → F) (hw : ∀ k, w k ≠ 0) (γ : TaggedArc n) :
    MvPolynomial.aeval w (cntNum γ) = laurentE0 w γ * ∏ k, w k := by
  rcases γ with ⟨i, j, h⟩ | ⟨_ | _, i⟩
  · simp only [cntNum, laurentE0, map_sum, map_mul, MvPolynomial.aeval_X, cntPair, map_prod,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [cnt_term_mul_prod w hw (cnt_vtx_succ_ne hn _)]
  · simp [cntNum, laurentE0, map_prod]
  · simp only [cntNum, laurentE0, map_sum, map_mul, MvPolynomial.aeval_X, cntPair, map_prod,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [cnt_term_mul_prod w hw (cnt_vtx_succ_ne hn _)]

/-- Equal values of `E⁰` at algebraically independent `z` give equal values at every positive
rational point. -/
private theorem cnt_laurentE0_eq_at {F : Type*} [Field F] [CharZero F] (hn : 2 ≤ n)
    {z : Fin n → F} (hz : AlgebraicIndependent ℚ z) {γ γ' : TaggedArc n}
    (h : laurentE0 z γ = laurentE0 z γ') (w : Fin n → ℚ) (hw : ∀ k, 0 < w k) :
    laurentE0 w γ = laurentE0 w γ' := by
  have hz0 : ∀ k, z k ≠ 0 := hz.ne_zero
  have hN : cntNum γ = cntNum γ' := by
    apply algebraicIndependent_iff_injective_aeval.1 hz
    rw [cnt_aeval_cntNum hn z hz0, cnt_aeval_cntNum hn z hz0, h]
  have hw0 : ∀ k, w k ≠ 0 := fun k => (hw k).ne'
  have := congrArg (MvPolynomial.aeval w) hN
  rw [cnt_aeval_cntNum hn w hw0, cnt_aeval_cntNum hn w hw0] at this
  exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun k _ => hw0 k) this

/-- The point `w` with `w_a = s` and `w_k = 1` otherwise. -/
private def cntPt (a : Fin n) (s : ℚ) : Fin n → ℚ := fun k => if k = a then s else 1

omit [NeZero n] in
/-- The entries of `cntPt a s` are at least `1` for `s ≥ 1`. -/
private theorem cnt_one_le_cntPt {a : Fin n} {s : ℚ} (hs : 1 ≤ s) (k : Fin n) :
    1 ≤ cntPt a s k := by
  unfold cntPt
  split_ifs <;> linarith

omit [NeZero n] in
/-- `(cntPt a s)_k = 1` for `k ≠ a`. -/
private theorem cnt_cntPt_of_ne {a k : Fin n} (s : ℚ) (h : k ≠ a) : cntPt a s k = 1 :=
  if_neg h

omit [NeZero n] in
/-- `(cntPt a s)_a = s`. -/
private theorem cnt_cntPt_self (a : Fin n) (s : ℚ) : cntPt a s a = s :=
  if_pos rfl

omit [NeZero n] in
/-- `1 / (x y) ≤ 1` for `x, y ≥ 1`. -/
private theorem cnt_div_le_one {x y : ℚ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 * 1 / (x * y) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith

/-- `j ≠ i` for an ordinary arc `α(i, j)`. -/
private theorem cnt_ne_of_ordinary {i j : Fin n} (h : 2 ≤ cdist i j) : j ≠ i := by
  intro e
  have := vtx_add_ne_self (u := (i : ℤ)) (d := cdist i j) (by omega)
    (by exact_mod_cast cdist_lt i j)
  rw [vtx_add_cdist, vtx_coe] at this
  exact this e

/-- Away from the endpoints, `E⁰_{α(i,j)}(w) ≤ d(i, j)`. -/
private theorem cnt_le_of_ne {i j a : Fin n} (h : 2 ≤ cdist i j) (hai : a ≠ i) (haj : a ≠ j)
    {s : ℚ} (hs : 1 ≤ s) : laurentE0 (cntPt a s) (.ordinary i j h) ≤ cdist i j := by
  simp only [laurentE0]
  calc _ ≤ ∑ _t ∈ Finset.range (cdist i j), (1 : ℚ) := Finset.sum_le_sum fun t _ => by
          rw [cnt_cntPt_of_ne s (Ne.symm hai), cnt_cntPt_of_ne s (Ne.symm haj)]
          exact cnt_div_le_one (cnt_one_le_cntPt hs _) (cnt_one_le_cntPt hs _)
    _ = cdist i j := by simp

/-- At the left endpoint, `E⁰_{α(i,j)}(w) ≥ s`. -/
private theorem cnt_le_at_left (hn : 3 ≤ n) {i j : Fin n} (h : 2 ≤ cdist i j) {s : ℚ}
    (hs : 1 ≤ s) : s ≤ laurentE0 (cntPt i s) (.ordinary i j h) := by
  simp only [laurentE0]
  have hpos : ∀ k, 0 < cntPt i s k := fun k => by linarith [cnt_one_le_cntPt hs (a := i) k]
  have h1 : (vtx ((i : ℤ) + ((1 : ℕ) : ℤ)) : Fin n) ≠ i := by
    have := vtx_add_ne_self (n := n) (u := (i : ℤ)) (d := 1) one_pos (by omega)
    rwa [vtx_coe] at this
  have h2 : (vtx ((i : ℤ) + ((1 : ℕ) : ℤ) + 1) : Fin n) ≠ i := by
    have := vtx_add_ne_self (n := n) (u := (i : ℤ)) (d := 2) two_pos (by omega)
    rwa [vtx_coe, show (i : ℤ) + 2 = (i : ℤ) + ((1 : ℕ) : ℤ) + 1 by push_cast; ring] at this
  calc s = cntPt i s i * cntPt i s j / (cntPt i s (vtx ((i : ℤ) + ((1 : ℕ) : ℤ))) *
        cntPt i s (vtx ((i : ℤ) + ((1 : ℕ) : ℤ) + 1))) := by
          rw [cnt_cntPt_self, cnt_cntPt_of_ne s (cnt_ne_of_ordinary h), cnt_cntPt_of_ne s h1,
            cnt_cntPt_of_ne s h2]
          ring
    _ ≤ _ := Finset.single_le_sum (f := fun t : ℕ => cntPt i s i * cntPt i s j /
        (cntPt i s (vtx ((i : ℤ) + t)) * cntPt i s (vtx ((i : ℤ) + t + 1))))
          (fun t _ => div_nonneg (mul_nonneg (hpos i).le (hpos j).le)
            (mul_nonneg (hpos _).le (hpos _).le))
          (Finset.mem_range.2 (by omega))

/-- At the first interior vertex, `E⁰_{α(i,j)}(w) < d(i, j)`. -/
private theorem cnt_lt_at_interior (hn : 3 ≤ n) {i j : Fin n} (h : 2 ≤ cdist i j) {s : ℚ}
    (hs : 1 < s) :
    laurentE0 (cntPt (vtx ((i : ℤ) + 1)) s) (.ordinary i j h) < cdist i j := by
  simp only [laurentE0]
  have hc := cdist_lt i j
  have hi : i ≠ vtx ((i : ℤ) + 1) := by
    have := vtx_add_ne_self (n := n) (u := (i : ℤ)) (d := 1) one_pos (by omega)
    rw [vtx_coe] at this
    exact Ne.symm this
  have hj : j ≠ vtx ((i : ℤ) + 1) := by
    have := vtx_add_ne_self (n := n) (u := (i : ℤ) + 1) (d := (cdist i j : ℤ) - 1) (by omega)
      (by omega)
    rwa [show (i : ℤ) + 1 + ((cdist i j : ℤ) - 1) = (i : ℤ) + cdist i j by ring,
      vtx_add_cdist] at this
  calc _ < ∑ _t ∈ Finset.range (cdist i j), (1 : ℚ) := by
        refine Finset.sum_lt_sum (fun t _ => ?_) ⟨0, Finset.mem_range.2 (by omega), ?_⟩
        · rw [cnt_cntPt_of_ne s hi, cnt_cntPt_of_ne s hj]
          exact cnt_div_le_one (cnt_one_le_cntPt hs.le _) (cnt_one_le_cntPt hs.le _)
        · rw [cnt_cntPt_of_ne s hi, cnt_cntPt_of_ne s hj]
          simp only [Nat.cast_zero, add_zero, vtx_coe]
          rw [cnt_cntPt_of_ne s hi, cnt_cntPt_self, div_lt_one (by positivity)]
          linarith
    _ = cdist i j := by simp

/-- Off the run from `i` to `j`, `E⁰_{α(i,j)}(w) = d(i, j)`. -/
private theorem cnt_eq_of_notMem_run {i j a : Fin n} (h : 2 ≤ cdist i j)
    (hrun : ∀ u : ℕ, u ≤ cdist i j → (vtx ((i : ℤ) + u) : Fin n) ≠ a) (s : ℚ) :
    laurentE0 (cntPt a s) (.ordinary i j h) = cdist i j := by
  simp only [laurentE0]
  have hi : i ≠ a := by simpa [vtx_coe] using hrun 0 (Nat.zero_le _)
  have hj : j ≠ a := by simpa [vtx_add_cdist] using hrun _ le_rfl
  calc _ = ∑ _t ∈ Finset.range (cdist i j), (1 : ℚ) := Finset.sum_congr rfl fun t ht => by
          rw [Finset.mem_range] at ht
          have h2 := hrun (t + 1) ht
          push_cast at h2
          rw [cnt_cntPt_of_ne s hi, cnt_cntPt_of_ne s hj, cnt_cntPt_of_ne s (hrun t ht.le),
            cnt_cntPt_of_ne s (by rwa [add_assoc])]
          norm_num
    _ = cdist i j := by simp

/-- `E⁰_{ρ^-_i}(w) = w_i ∑_{t < n} 1 / (w_t w_{t+1})`. -/
private theorem cnt_laurentE0_notched (w : Fin n → ℚ) (i : Fin n) :
    laurentE0 w (.radius .notched i) =
      w i * ∑ t ∈ Finset.range n, 1 / (w (vtx (t : ℤ)) * w (vtx ((t : ℤ) + 1))) := by
  simp only [laurentE0]
  set g : ℤ → ℚ := fun x => 1 / (w (vtx x) * w (vtx (x + 1))) with hg
  have hper : ∀ x, g (x + n) = g x := fun x => by
    simp only [hg]
    rw [show x + n + 1 = (x + 1) + 1 * n by ring, show x + n = x + 1 * n by ring,
      vtx_add_mul, vtx_add_mul]
  have hshift : ∀ c : ℕ, ∑ t ∈ Finset.range n, g ((c : ℤ) + t) =
      ∑ t ∈ Finset.range n, g t := by
    intro c
    induction c with
    | zero => simp
    | succ c ih =>
      have e1 := Finset.sum_range_succ (fun t : ℕ => g ((c : ℤ) + t)) n
      have e2 := Finset.sum_range_succ' (fun t : ℕ => g ((c : ℤ) + t)) n
      rw [← ih, show ∑ t ∈ Finset.range n, g (((c + 1 : ℕ) : ℤ) + t) =
          ∑ t ∈ Finset.range n, g ((c : ℤ) + ((t + 1 : ℕ) : ℤ)) from
            Finset.sum_congr rfl fun t _ => by push_cast; ring_nf]
      have e3 : g ((c : ℤ) + ((n : ℕ) : ℤ)) = g ((c : ℤ) + ((0 : ℕ) : ℤ)) := by
        simp only [Nat.cast_zero, add_zero]
        exact hper _
      linarith
  have := hshift (i : ℕ)
  simp only [hg] at this
  rw [← this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_one_div]

/-- An ordinary arc and its reverse are separated by a positive point. -/
private theorem cnt_laurentE0_ne_reverse (hn : 3 ≤ n) {i j : Fin n} (hij : 2 ≤ cdist i j)
    (hji : 2 ≤ cdist j i) (hd : cdist i j = cdist j i) :
    laurentE0 (cntPt (vtx ((i : ℤ) + 1)) 2) (.ordinary i j hij) ≠
      laurentE0 (cntPt (vtx ((i : ℤ) + 1)) 2) (.ordinary j i hji) := by
  intro heq
  have e1 := cnt_lt_at_interior hn hij (s := 2) one_lt_two
  have hc := cdist_lt i j
  have hN : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hdvd : ∀ {x y : ℤ}, (vtx x : Fin n) = vtx y → (n : ℤ) ∣ y - x := fun h =>
    Int.ModEq.dvd (vtx_eq_vtx_iff.1 h)
  have d1 : (n : ℤ) ∣ (j : ℤ) - ((i : ℤ) + cdist i j) :=
    hdvd (by rw [vtx_add_cdist, vtx_coe])
  have d2 : (n : ℤ) ∣ (i : ℤ) - ((j : ℤ) + cdist i j) :=
    hdvd (by rw [hd, vtx_add_cdist, vtx_coe])
  have d3 : (n : ℤ) ∣ 2 * (cdist i j : ℤ) := by
    have := dvd_add d1 d2
    rw [show (j : ℤ) - ((i : ℤ) + cdist i j) + ((i : ℤ) - ((j : ℤ) + cdist i j)) =
      -(2 * (cdist i j : ℤ)) by ring] at this
    exact dvd_neg.1 this
  have h2d : 2 * (cdist i j : ℤ) = n := by
    obtain ⟨k, hk⟩ := d3
    have hk0 : 0 < k := by nlinarith
    have hk2 : k < 2 := by nlinarith
    obtain rfl : k = 1 := by omega
    rw [hk, mul_one]
  have hrun : ∀ u : ℕ, u ≤ cdist j i → (vtx ((j : ℤ) + u) : Fin n) ≠ vtx ((i : ℤ) + 1) := by
    intro u hu e
    have := dvd_add (hdvd e) d1
    rw [show (i : ℤ) + 1 - ((j : ℤ) + u) + ((j : ℤ) - ((i : ℤ) + cdist i j)) =
      -((cdist i j : ℤ) + u - 1) by ring, dvd_neg] at this
    have := Int.le_of_dvd (by omega) this
    omega
  rw [heq, cnt_eq_of_notMem_run hji hrun 2, ← hd] at e1
  exact lt_irrefl _ e1

/-- Positive points separate ordinary arcs. -/
private theorem cnt_ordinary_eq_of_forall_laurentE0_eq (hn : 3 ≤ n) {i j i' j' : Fin n}
    (hij : 2 ≤ cdist i j) (hij' : 2 ≤ cdist i' j')
    (h : ∀ w : Fin n → ℚ, (∀ k, 0 < w k) →
      laurentE0 w (.ordinary i j hij) = laurentE0 w (.ordinary i' j' hij')) :
    TaggedArc.ordinary i j hij = .ordinary i' j' hij' := by
  have h1 := h (fun _ => 1) (fun _ => one_pos)
  simp only [laurentE0, mul_one, div_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    at h1
  have hpt : ∀ a s, 1 ≤ s → laurentE0 (cntPt a s) (.ordinary i j hij) =
      laurentE0 (cntPt a s) (.ordinary i' j' hij') :=
    fun a s hs => h _ fun k => by linarith [cnt_one_le_cntPt hs (a := a) k]
  have hd : cdist i j = cdist i' j' := by exact_mod_cast h1
  have hn' : (3 : ℚ) ≤ n := by exact_mod_cast hn
  have hcq : (cdist i j : ℚ) < n := by exact_mod_cast cdist_lt i j
  have hcq' : (cdist i' j' : ℚ) < n := by exact_mod_cast cdist_lt i' j'
  have key1 : i = i' ∨ i = j' := by
    by_contra hcon
    push Not at hcon
    have e1 := cnt_le_of_ne hij' hcon.1 hcon.2 (s := n) (by linarith)
    have e2 := cnt_le_at_left hn hij (s := n) (by linarith)
    rw [hpt _ _ (by linarith)] at e2
    rw [← hd] at e1
    linarith
  have key2 : i' = i ∨ i' = j := by
    by_contra hcon
    push Not at hcon
    have e1 := cnt_le_of_ne hij hcon.1 hcon.2 (s := n) (by linarith)
    have e2 := cnt_le_at_left hn hij' (s := n) (by linarith)
    rw [← hpt _ _ (by linarith)] at e2
    rw [hd] at e1
    linarith
  by_cases hii : i = i'
  · subst hii
    obtain rfl : j = j' := by rw [← vtx_add_cdist i j, ← vtx_add_cdist i j', hd]
    rfl
  · obtain rfl : i = j' := key1.resolve_left hii
    obtain rfl : i' = j := key2.resolve_left (Ne.symm hii)
    exact absurd (hpt _ 2 one_le_two) (cnt_laurentE0_ne_reverse hn hij hij' hd)

/-- Positive points separate tagged arcs. -/
private theorem cnt_eq_of_forall_laurentE0_eq (hn : 3 ≤ n) {γ γ' : TaggedArc n}
    (h : ∀ w : Fin n → ℚ, (∀ k, 0 < w k) → laurentE0 w γ = laurentE0 w γ') : γ = γ' := by
  have h1 := h (fun _ => 1) (fun _ => one_pos)
  have hpt : ∀ a s, 1 ≤ s → laurentE0 (cntPt a s) γ = laurentE0 (cntPt a s) γ' :=
    fun a s hs => h _ fun k => by linarith [cnt_one_le_cntPt hs (a := a) k]
  have hS : ∀ w : Fin n → ℚ, (∀ k, 0 < w k) →
      0 < ∑ t ∈ Finset.range n, 1 / (w (vtx (t : ℤ)) * w (vtx ((t : ℤ) + 1))) := fun w hw =>
    Finset.sum_pos (fun _ _ => one_div_pos.2 (mul_pos (hw _) (hw _)))
      ⟨0, Finset.mem_range.2 (NeZero.pos n)⟩
  have hn' : (3 : ℚ) ≤ n := by exact_mod_cast hn
  rcases γ with ⟨i, j, hij⟩ | ⟨_ | _, i⟩ <;> rcases γ' with ⟨i', j', hij'⟩ | ⟨_ | _, i'⟩
  · exact cnt_ordinary_eq_of_forall_laurentE0_eq hn hij hij' h
  all_goals simp only [laurentE0, mul_one, div_one, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at h1
  · have := cdist_lt i j
    have : cdist i j = 1 := by exact_mod_cast h1
    omega
  · have := cdist_lt i j
    have : cdist i j = n := by exact_mod_cast h1
    omega
  · have : cdist i' j' = 1 := by exact_mod_cast h1.symm
    omega
  · have := hpt i 2 one_le_two
    simp only [laurentE0, cnt_cntPt_self] at this
    by_contra hne
    rw [cnt_cntPt_of_ne _ (fun e => hne (by rw [e]))] at this
    norm_num at this
  · linarith
  · have := cdist_lt i' j'
    have : cdist i' j' = n := by exact_mod_cast h1.symm
    omega
  · linarith
  · have := hpt i 2 one_le_two
    rw [cnt_laurentE0_notched, cnt_laurentE0_notched, cnt_cntPt_self] at this
    have hs := hS (cntPt i 2) fun k => by linarith [cnt_one_le_cntPt one_le_two (a := i) k]
    by_contra hne
    rw [cnt_cntPt_of_ne _ (fun e => hne (by rw [e]))] at this
    have : (2 : ℚ) = 1 := mul_right_cancel₀ hs.ne' this
    norm_num at this

/-- **The coefficient-free expressions are distinct**: for `n ≥ 3` and `z₁, …, z_n` algebraically
independent over `ℚ` in a field of characteristic zero, `γ ↦ E⁰_γ` is injective. -/
@[cluster_algebras "lem_D_laurent_distinct"]
theorem laurentE0_injective {F : Type*} [Field F] [CharZero F] (hn : 3 ≤ n) {z : Fin n → F}
    (hz : AlgebraicIndependent ℚ z) : Function.Injective (laurentE0 z) := fun γ γ' h =>
  cnt_eq_of_forall_laurentE0_eq hn fun w hw => cnt_laurentE0_eq_at (by omega) hz h w hw

variable (K)

/-! ### Semifield homomorphisms at the elements `P_γ` -/

section Hom

variable {F₀ L ι₀ ι : Type*} [Field F₀] [CharZero F₀] [Field L] [CharZero L] {y₀ : ι₀ → F₀}
  {y : ι → L} [Fact (AlgebraicIndependent ℚ y₀)] [Fact (AlgebraicIndependent ℚ y)]

open Classical in
/-- The value in `L` of a semifield homomorphism `θ : ℚ_sf(y₀) → ℚ_sf(y)` at an element of `F₀`,
and `0` outside `ℚ_sf(y₀)`. -/
private noncomputable def cntHomVal
    (θ : FZSemifieldHom (universalSemifield y₀) (universalSemifield y)) (z : F₀) : L :=
  if h : z ∈ universalSemifield y₀ then (θ ⟨z, h⟩ : L) else 0

variable (θ : FZSemifieldHom (universalSemifield y₀) (universalSemifield y))

/-- `cntHomVal θ` agrees with `θ` on `ℚ_sf(y₀)`. -/
private theorem cntHomVal_mk {z : F₀} (h : z ∈ universalSemifield y₀) :
    cntHomVal θ z = θ ⟨z, h⟩ := by
  unfold cntHomVal
  rw [dif_pos h]

/-- `cntHomVal θ` is additive on `ℚ_sf(y₀)`. -/
private theorem cntHomVal_add {a b : F₀} (ha : a ∈ universalSemifield y₀)
    (hb : b ∈ universalSemifield y₀) : cntHomVal θ (a + b) = cntHomVal θ a + cntHomVal θ b := by
  rw [cntHomVal_mk θ (add_mem_universalSemifield ha hb), cntHomVal_mk θ ha, cntHomVal_mk θ hb,
    ← universalSemifield.mk_add_mk ha hb, map_add, universalSemifield.coe_add]

/-- `cntHomVal θ` is multiplicative on `ℚ_sf(y₀)`. -/
private theorem cntHomVal_mul {a b : F₀} (ha : a ∈ universalSemifield y₀)
    (hb : b ∈ universalSemifield y₀) : cntHomVal θ (a * b) = cntHomVal θ a * cntHomVal θ b := by
  rw [cntHomVal_mk θ (mul_mem_universalSemifield ha hb), cntHomVal_mk θ ha, cntHomVal_mk θ hb,
    ← universalSemifield.mk_mul_mk ha hb, map_mul, universalSemifield.coe_mul]

/-- `cntHomVal θ` respects quotients on `ℚ_sf(y₀)`. -/
private theorem cntHomVal_div {a b : F₀} (ha : a ∈ universalSemifield y₀)
    (hb : b ∈ universalSemifield y₀) : cntHomVal θ (a / b) = cntHomVal θ a / cntHomVal θ b := by
  rw [cntHomVal_mk θ (div_mem_universalSemifield ha hb), cntHomVal_mk θ ha, cntHomVal_mk θ hb,
    ← universalSemifield.mk_div_mk ha hb, map_div, universalSemifield.coe_div]

/-- `cntHomVal θ 1 = 1`. -/
private theorem cntHomVal_one : cntHomVal θ (1 : F₀) = 1 := by
  rw [cntHomVal_mk θ one_mem_universalSemifield]
  exact congrArg Subtype.val (map_one θ)

/-- `cntHomVal θ` respects nonempty sums of elements of `ℚ_sf(y₀)`. -/
private theorem cntHomVal_sum {α : Type*} {s : Finset α} (hs : s.Nonempty) {f : α → F₀}
    (hf : ∀ a ∈ s, f a ∈ universalSemifield y₀) :
    cntHomVal θ (∑ a ∈ s, f a) = ∑ a ∈ s, cntHomVal θ (f a) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    have hf' : ∀ b ∈ s, f b ∈ universalSemifield y₀ := fun b hb =>
      hf b (Finset.mem_cons_of_mem hb)
    rw [Finset.sum_cons, Finset.sum_cons, cntHomVal_add θ (hf a (Finset.mem_cons_self a s))
      (cnt_sum_mem_universalSemifield hs hf'), ih hf']

/-- `cntHomVal θ` is nonzero on `ℚ_sf(y₀)`. -/
private theorem cntHomVal_ne_zero (z : F₀) (h : z ∈ universalSemifield y₀) :
    cntHomVal θ z ≠ 0 := by
  rw [cntHomVal_mk θ h]
  exact universalSemifield.coe_ne_zero Fact.out _

end Hom

/-- Integer intervals as ranges. -/
private theorem cnt_sum_Ico_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (a : ℤ)
    (k : ℕ) : ∑ m ∈ Finset.Ico a (a + k), f m = ∑ t ∈ Finset.range k, f (a + t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, Nat.cast_succ, ← add_assoc,
      ← Finset.sum_Ico_add_eq_sum_Ico_add_one (by omega)]

section HomArc

variable [CharZero K] {L ι : Type*} [Field L] [CharZero L] {y : ι → L}
  [Fact (AlgebraicIndependent ℚ y)] {x₀ : Fin (2 * n + 2) → DField K n}
  (hx₀ : x₀ = (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster)
  [Fact (AlgebraicIndependent ℚ x₀)]
  (θ : FZSemifieldHom (universalSemifield x₀) (universalSemifield y))

include hx₀

/-- **A semifield homomorphism at the elements `P_γ`**: if `θ : ℚ_sf(x̃(T∘, ℓ∘)) → ℚ_sf(y)` sends
the frozen variables `P_{β_c}`, `λ`, `λ̄` to `1`, then `θ(P_γ) = E⁰_γ(θ(p_1), …, θ(p_n))`. -/
private theorem cnt_homVal_arcValue (hn : 3 ≤ n)
    (hθ : ∀ i : Fin (2 * n + 2), n ≤ (i : ℕ) → θ ⟨x₀ i, mem_universalSemifield_self _ i⟩ = 1)
    (γ : TaggedArc n) :
    cntHomVal θ (arcValue K γ) = laurentE0 (fun a => cntHomVal θ (var K (.p a))) γ := by
  subst hx₀
  set z : Fin n → L := fun a => cntHomVal θ (var K (.p a)) with hz
  have hc : ∀ c : Fin n, cntHomVal θ (rowValue K (.boundary c)) = 1 := fun c => by
    rw [← cnt_extCluster_boundary K c, cntHomVal_mk θ (mem_universalSemifield_self _ _),
      hθ _ (by simp), universalSemifield.coe_one]
  have hl : ∀ τ : Tag, cntHomVal θ (var K (n := n) (.lam τ)) = 1 := fun τ => by
    cases τ <;> [rw [← cnt_extCluster_lam_plain K]; rw [← cnt_extCluster_lam_notched K]] <;>
      rw [cntHomVal_mk θ (mem_universalSemifield_self _ _), hθ _ (by simp; omega),
        universalSemifield.coe_one]
  have hw : ∀ v m : ℤ, cntHomVal θ (laurentWeight K (n := n) v m) = 1 := fun v m => by
    unfold laurentWeight
    split_ifs <;> first | exact cntHomVal_one θ | exact hl _
  have hseg : ∀ {u v : ℤ}, 0 ≤ u → u < n → u < v → v ≤ u + n →
      cntHomVal θ (segValue K (seg u v : DSeg n)) = z (vtx u) * z (vtx v) *
        ∑ m ∈ Finset.Ico u v, 1 / (z (vtx m) * z (vtx (m + 1))) := by
    intro u v hu₀ hun huv hvu
    rw [segValue_seg_eq_sum K hn hu₀ hun huv hvu,
      cntHomVal_mul θ (mul_mem_universalSemifield (cnt_mem_p K hn _) (cnt_mem_p K hn _))
        (cnt_sum_mem_universalSemifield ⟨u, Finset.mem_Ico.2 ⟨le_rfl, huv⟩⟩
          fun m _ => cnt_mem_term K hn v m),
      cntHomVal_mul θ (cnt_mem_p K hn _) (cnt_mem_p K hn _),
      cntHomVal_sum θ ⟨u, Finset.mem_Ico.2 ⟨le_rfl, huv⟩⟩ fun m _ => cnt_mem_term K hn v m]
    refine congrArg _ (Finset.sum_congr rfl fun m _ => ?_)
    rw [cntHomVal_div θ (mul_mem_universalSemifield (cnt_mem_weight K v m)
        (cnt_mem_boundary K _)) (mul_mem_universalSemifield (cnt_mem_p K hn _)
          (cnt_mem_p K hn _)),
      cntHomVal_mul θ (cnt_mem_weight K v m) (cnt_mem_boundary K _),
      cntHomVal_mul θ (cnt_mem_p K hn _) (cnt_mem_p K hn _), hw, hc, mul_one]
  rcases γ with ⟨i, j, h⟩ | ⟨_ | _, i⟩
  · have hcd := cdist_lt i j
    rw [cnt_arcValue_ordinary K hn, hseg (by omega) (by exact_mod_cast i.isLt) (by omega)
      (by omega), cnt_sum_Ico_eq_sum_range, vtx_coe, vtx_add_cdist, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => mul_one_div _ _
  · rfl
  · rw [arcValue_radius_notched_eq K hn,
      cntHomVal_div θ (cnt_mem_segValue K hn (by omega) (by exact_mod_cast i.isLt) (by omega)
        le_rfl) (cnt_mem_p K hn i),
      hseg (by omega) (by exact_mod_cast i.isLt) (by omega) le_rfl,
      show (i : ℤ) + n = (i : ℤ) + 1 * n by ring, vtx_add_mul, vtx_coe,
      show (i : ℤ) + 1 * n = (i : ℤ) + ((n : ℕ) : ℤ) by ring, cnt_sum_Ico_eq_sum_range]
    have hzi : z i ≠ 0 := cntHomVal_ne_zero θ _ (cnt_mem_p K hn i)
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    change _ / z i = _
    field_simp

end HomArc

/-! ### Cluster variables and clusters of `Σ•_n` -/

/-- The cluster of `Σ(T, ℓ)` is `(P_{ℓ(1)}, …, P_{ℓ(n)})`. -/
private theorem cnt_cluster_dSeed (T : Finset (TaggedArc n)) (ℓ : Fin n → TaggedArc n)
    (i : Fin n) : cluster (le_two_mul_add_two n) (dSeed K T ℓ) i = arcValue K (ℓ i) := by
  change rowValue K (extLabel ℓ _) = _
  rw [cnt_extLabel_castLE]
  rfl

/-- The cluster variables of `Σ(T, ℓ)` are the `P_γ`, `γ ∈ T`. -/
private theorem cnt_clusterVariables_dSeed {T : Finset (TaggedArc n)} {ℓ : Fin n → TaggedArc n}
    (hℓ : IsLabelling T ℓ) :
    clusterVariables (le_two_mul_add_two n) (dSeed K T ℓ) = arcValue K '' (T : Set _) := by
  rw [← hℓ.2, ← Set.range_comp]
  exact congrArg Set.range (funext fun i => cnt_cluster_dSeed K T ℓ i)

omit [NeZero n] in
/-- Every tagged arc lies in a tagged triangulation. -/
private theorem cnt_exists_isTaggedTriangulation_mem [NeZero n] (γ : TaggedArc n) :
    ∃ T : Finset (TaggedArc n), IsTaggedTriangulation T ∧ γ ∈ T := by
  classical
  obtain ⟨S, hγS, hS⟩ := (Set.toFinite
    {S : Set (TaggedArc n) | S.Pairwise TaggedArc.Compatible}).exists_le_maximal
      (a := {γ}) (Set.pairwise_singleton _ _)
  refine ⟨S.toFinite.toFinset, ?_, ?_⟩
  · rw [isTaggedTriangulation_iff_maximal, Set.Finite.coe_toFinset]
    exact hS
  · simpa using hγS (Set.mem_singleton γ)

/-- The indeterminates `Y_1, …, Y_k` of `ℚ(Y_1, …, Y_k)`. -/
private noncomputable def cntY (k : ℕ) : Fin k → FractionRing (MvPolynomial (Fin k) ℚ) :=
  fun i => algebraMap (MvPolynomial (Fin k) ℚ) _ (MvPolynomial.X i)

private theorem cnt_algebraicIndependent_cntY (k : ℕ) : AlgebraicIndependent ℚ (cntY k) := by
  -- Instance search with pending depth above 1 misses this scalar tower.
  set_option maxSynthPendingDepth 1 in
  exact (MvPolynomial.algebraicIndependent_X (Fin k) ℚ).map'
    (f := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin k) ℚ) (FractionRing (MvPolynomial (Fin k) ℚ)))
    (IsFractionRing.injective _ _)

/-- A semifield homomorphism `ℚ_sf(x) → ℚ_sf(y)` sending the cluster variables `x_i`, `i < n₀`,
to `y_i` and the frozen variables to `1`. -/
private theorem cnt_exists_hom {F₀ L : Type*} [Field F₀] [CharZero F₀] [Field L] [CharZero L]
    {m₀ n₀ : ℕ} (h : n₀ ≤ m₀) {x : Fin m₀ → F₀} [Fact (AlgebraicIndependent ℚ x)]
    {y : Fin n₀ → L} [Fact (AlgebraicIndependent ℚ y)] :
    ∃ χ : FZSemifieldHom (universalSemifield x) (universalSemifield y),
      (∀ i : Fin n₀, (χ ⟨x (Fin.castLE h i), mem_universalSemifield_self x _⟩ : L) = y i) ∧
      ∀ i : Fin m₀, n₀ ≤ (i : ℕ) → χ ⟨x i, mem_universalSemifield_self x i⟩ = 1 := by
  refine ⟨universalSemifieldLift x fun i =>
      if hi : (i : ℕ) < n₀ then ⟨y ⟨i, hi⟩, mem_universalSemifield_self y _⟩ else 1,
    fun i => ?_, fun i hi => ?_⟩ <;> rw [universalSemifieldLift_apply_self]
  · simp only [Fin.val_castLE, Fin.is_lt, dif_pos]
  · simp only [dif_neg (not_lt.2 hi)]

/-- The elements `P_γ` are distinct. -/
private theorem cnt_arcValue_injective [CharZero K] (hn : 3 ≤ n) :
    Function.Injective (arcValue K (n := n)) := by
  set x₀ := (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster
  haveI : Fact (AlgebraicIndependent ℚ x₀) :=
    ⟨(isLabeledSeed_dSeed_radiusTriangulation K hn).1.algebraicIndependent_rat⟩
  haveI := Fact.mk (cnt_algebraicIndependent_cntY n)
  obtain ⟨θ, hθY, hθ⟩ := cnt_exists_hom (le_two_mul_add_two n) (x := x₀) (y := cntY n)
  have hz : ∀ a, cntHomVal θ (var K (.p a)) = cntY n (cntInitialIdx n a) := fun a => by
    rw [cntHomVal_mk θ (cnt_mem_p K hn a), show (⟨var K (.p a), cnt_mem_p K hn a⟩ :
        universalSemifield x₀) = ⟨x₀ (Fin.castLE (le_two_mul_add_two n) (cntInitialIdx n a)),
          mem_universalSemifield_self _ _⟩ from Subtype.ext (cnt_extCluster_p K hn a).symm]
    exact hθY _
  have hzi : AlgebraicIndependent ℚ fun a => cntHomVal θ (var K (.p a)) := by
    rw [funext hz]
    exact (cnt_algebraicIndependent_cntY n).comp _ (cnt_initialIdx_injective hn)
  intro γ γ' h
  apply laurentE0_injective hn hzi
  rw [← cnt_homVal_arcValue K rfl θ hn hθ γ, ← cnt_homVal_arcValue K rfl θ hn hθ γ', h]

/-- A semifield homomorphism from `ℚ_sf(x̃(T∘, ℓ∘))` that is `1` on the frozen variables and
sends `p_1, …, p_n` to algebraically independent elements separates the cluster variables of
`Σ•_n`. -/
private theorem cnt_cluster_eq_of_homVal_eq [CharZero K] (hn : 3 ≤ n) {L ι : Type*} [Field L]
    [CharZero L] {y : ι → L} [Fact (AlgebraicIndependent ℚ y)]
    [Fact (AlgebraicIndependent ℚ (dPattern K n .root).extCluster)]
    (θ : FZSemifieldHom (universalSemifield (dPattern K n .root).extCluster) (universalSemifield y))
    (hθ : ∀ i : Fin (2 * n + 2), n ≤ (i : ℕ) →
      θ ⟨(dPattern K n .root).extCluster i, mem_universalSemifield_self _ i⟩ = 1)
    (hzi : AlgebraicIndependent ℚ fun a => cntHomVal θ (var K (.p a))) {t t' : RegularTree n}
    {i j : Fin n} (h : cntHomVal θ (cluster (le_two_mul_add_two n) (dPattern K n t) i) =
      cntHomVal θ (cluster (le_two_mul_add_two n) (dPattern K n t') j)) :
    cluster (le_two_mul_add_two n) (dPattern K n t) i =
      cluster (le_two_mul_add_two n) (dPattern K n t') j := by
  have hx0 : (dPattern K n .root).extCluster =
      (dSeed K (radiusTriangulation n) (initialLabelling n)).extCluster := by
    rw [(isSeedPattern_dPattern K hn).2]
  obtain ⟨T, ℓ, -, -, hT⟩ := exists_dPattern_eq_dSeed K hn t
  obtain ⟨T', ℓ', -, -, hT'⟩ := exists_dPattern_eq_dSeed K hn t'
  rw [hT, hT', cnt_cluster_dSeed, cnt_cluster_dSeed] at h ⊢
  refine congrArg (arcValue K) (laurentE0_injective hn hzi ?_)
  rw [← cnt_homVal_arcValue K hx0 θ hn hθ, ← cnt_homVal_arcValue K hx0 θ hn hθ, h]

/-- **Cluster variables and clusters of `Σ•_n`**: `γ ↦ P_γ` is a bijection from the tagged arcs
onto the cluster variables of `Σ•_n`. -/
@[cluster_algebras "lem_D_pattern_counts"]
theorem arcValue_injective_and_range [CharZero K] (hn : 3 ≤ n) :
    Function.Injective (arcValue K (n := n)) ∧
      Set.range (arcValue K (n := n)) =
        patternClusterVariables (le_two_mul_add_two n) (dPattern K n) := by
  refine ⟨cnt_arcValue_injective K hn, Set.ext fun x => ⟨?_, fun hx => ?_⟩⟩
  · rintro ⟨γ, rfl⟩
    obtain ⟨T, hT, hγ⟩ := cnt_exists_isTaggedTriangulation_mem γ
    obtain ⟨t, ℓ, hℓ, ht⟩ := IsTaggedTriangulation.exists_dPattern_eq_dSeed K hn hT
    obtain ⟨k, hk⟩ : γ ∈ Set.range ℓ := by rwa [hℓ.2]
    exact Set.mem_iUnion.2 ⟨t, ⟨k, by rw [ht, cnt_cluster_dSeed, hk]⟩⟩
  · obtain ⟨t, k, rfl⟩ := Set.mem_iUnion.1 hx
    obtain ⟨T, ℓ, -, -, h⟩ := exists_dPattern_eq_dSeed K hn t
    exact ⟨ℓ k, by rw [h, cnt_cluster_dSeed]⟩

/-- **Cluster variables and clusters of `Σ•_n`**: `T ↦ {P_γ : γ ∈ T}` is a bijection from the
tagged triangulations onto the clusters of `Σ•_n`. -/
@[cluster_algebras "lem_D_pattern_counts"]
theorem bijOn_image_arcValue_patternClusters [CharZero K] (hn : 3 ≤ n) :
    Set.BijOn (fun T : Finset (TaggedArc n) => arcValue K '' (T : Set (TaggedArc n)))
      {T | IsTaggedTriangulation T}
      (patternClusters (le_two_mul_add_two n) (dPattern K n)) := by
  refine ⟨fun T hT => ?_, fun T _ T' _ h => ?_, fun S hS => ?_⟩
  · obtain ⟨t, ℓ, hℓ, ht⟩ := IsTaggedTriangulation.exists_dPattern_eq_dSeed K hn hT
    exact ⟨t, by beta_reduce; rw [ht, cnt_clusterVariables_dSeed K hℓ]⟩
  · exact Finset.coe_injective (Set.image_injective.2 (cnt_arcValue_injective K hn) h)
  · obtain ⟨t, rfl⟩ := hS
    obtain ⟨T, ℓ, hT, hℓ, h⟩ := exists_dPattern_eq_dSeed K hn t
    exact ⟨T, hT, by beta_reduce; rw [h, cnt_clusterVariables_dSeed K hℓ]⟩

/-- **Cluster variables and clusters of `Σ•_n`**: `Σ•_n` has `n²` cluster variables and
`N = (3n - 2)/n · binom(2n - 2, n - 1)` clusters. -/
@[cluster_algebras "lem_D_pattern_counts"]
theorem encard_dPattern [CharZero K] (hn : 3 ≤ n) :
    (patternClusterVariables (le_two_mul_add_two n) (dPattern K n)).encard = (n ^ 2 : ℕ) ∧
      ∃ N : ℕ, (patternClusters (le_two_mul_add_two n) (dPattern K n)).encard = N ∧
        n * N = (3 * n - 2) * (2 * n - 2).choose (n - 1) := by
  obtain ⟨hinj, hrange⟩ := arcValue_injective_and_range K hn
  have hbij := bijOn_image_arcValue_patternClusters K hn
  refine ⟨?_, {T : Finset (TaggedArc n) | IsTaggedTriangulation T}.ncard, ?_,
    mul_ncard_isTaggedTriangulation hn⟩
  · rw [← hrange, ← Set.image_univ, hinj.injOn.encard_image, Set.encard_univ,
      ENat.card_eq_coe_fintype_card, card_taggedArc hn]
  · rw [← hbij.image_eq, hbij.injOn.encard_image, (Set.toFinite _).cast_ncard_eq]

end TypeD

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ}

/-! ### Transfer of the counts -/

/-- A semifield homomorphism `ℚ_sf(x) → ℚ_sf(y)` that is `1` on the frozen variables `x_i`,
`i ≥ n`, is `1` on every tropical evaluation at them. -/
private theorem cnt_hom_tropicalEval {F₀ L ι : Type*} [Field F₀] [CharZero F₀] [Field L]
    [CharZero L] {m₀ n₀ : ℕ} {x : Fin m₀ → F₀} [Fact (AlgebraicIndependent ℚ x)] {y : ι → L}
    [Fact (AlgebraicIndependent ℚ y)]
    (χ : FZSemifieldHom (universalSemifield x) (universalSemifield y))
    (hχ : ∀ i : Fin m₀, n₀ ≤ (i : ℕ) → χ ⟨x i, mem_universalSemifield_self x i⟩ = 1)
    (e : TropicalSemifield (FrozenIndex m₀ n₀))
    (h : tropicalEval (fun a : FrozenIndex m₀ n₀ => x a) e ∈ universalSemifield x) :
    χ ⟨tropicalEval (fun a : FrozenIndex m₀ n₀ => x a) e, h⟩ = 1 := by
  classical
  unfold tropicalEval at h ⊢
  suffices ∀ (s : Finset (FrozenIndex m₀ n₀))
      (h : ∏ a ∈ s, x a ^ TropicalSemifield.exponent e a ∈ universalSemifield x),
      χ ⟨∏ a ∈ s, x a ^ TropicalSemifield.exponent e a, h⟩ = 1 from this _ h
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro h
    exact (congrArg χ (Subtype.ext (by simp))).trans (map_one χ)
  | insert a s ha ih =>
    intro h
    have hs : ∏ b ∈ s, x b ^ TropicalSemifield.exponent e b ∈ universalSemifield x :=
      prod_mem_universalSemifield fun b _ =>
        zpow_mem_universalSemifield (mem_universalSemifield_self _ _) _
    have hx : (⟨∏ b ∈ insert a s, x b ^ TropicalSemifield.exponent e b, h⟩ :
        universalSemifield x) = (⟨x a, mem_universalSemifield_self x a⟩ :
          universalSemifield x) ^ TropicalSemifield.exponent e a * ⟨_, hs⟩ :=
      Subtype.ext (by
        change ∏ b ∈ insert a s, x b ^ TropicalSemifield.exponent e b =
          x a ^ TropicalSemifield.exponent e a * ∏ b ∈ s, x b ^ TropicalSemifield.exponent e b
        exact Finset.prod_insert ha)
    rw [hx, map_mul, map_zpow, hχ a a.2, one_zpow, one_mul, ih hs]

/-- If `a = b ε` with `ε` a tropical evaluation at the frozen variables, a semifield homomorphism
that is `1` on the frozen variables takes the same value at `a` and `b`. -/
private theorem cnt_hom_eq_of_eq_mul {F₀ L ι : Type*} [Field F₀] [CharZero F₀] [Field L]
    [CharZero L] {m₀ n₀ : ℕ} {x : Fin m₀ → F₀} [Fact (AlgebraicIndependent ℚ x)] {y : ι → L}
    [Fact (AlgebraicIndependent ℚ y)]
    (χ : FZSemifieldHom (universalSemifield x) (universalSemifield y))
    (hχ : ∀ i : Fin m₀, n₀ ≤ (i : ℕ) → χ ⟨x i, mem_universalSemifield_self x i⟩ = 1)
    {a : universalSemifield x} {b : F₀} (hb : b ∈ universalSemifield x)
    {e : TropicalSemifield (FrozenIndex m₀ n₀)}
    (h : (a : F₀) = b * tropicalEval (fun k : FrozenIndex m₀ n₀ => x k) e) : χ a = χ ⟨b, hb⟩ := by
  have he : tropicalEval (fun k : FrozenIndex m₀ n₀ => x k) e ∈ universalSemifield x :=
    prod_mem_universalSemifield fun k _ =>
      zpow_mem_universalSemifield (mem_universalSemifield_self _ _) _
  rw [show a = ⟨b, hb⟩ * ⟨_, he⟩ from Subtype.ext h, map_mul, cnt_hom_tropicalEval χ hχ, mul_one]

/-- A semifield homomorphism that is `1` on the frozen variables is `1` on every tropical
evaluation at them. -/
private theorem cnt_hom_eq_one {F₀ L ι : Type*} [Field F₀] [CharZero F₀] [Field L]
    [CharZero L] {m₀ n₀ : ℕ} {x : Fin m₀ → F₀} [Fact (AlgebraicIndependent ℚ x)] {y : ι → L}
    [Fact (AlgebraicIndependent ℚ y)]
    (χ : FZSemifieldHom (universalSemifield x) (universalSemifield y))
    (hχ : ∀ i : Fin m₀, n₀ ≤ (i : ℕ) → χ ⟨x i, mem_universalSemifield_self x i⟩ = 1)
    {a : universalSemifield x} {e : TropicalSemifield (FrozenIndex m₀ n₀)}
    (h : (a : F₀) = tropicalEval (fun k : FrozenIndex m₀ n₀ => x k) e) : χ a = 1 :=
  (cnt_hom_eq_of_eq_mul χ hχ one_mem_universalSemifield (by rw [h, one_mul])).trans (map_one χ)

/-- Two assignments of seed data with the same coincidences among cluster variables have the
same numbers of cluster variables and of clusters. -/
private theorem cnt_encard_eq_of_cluster_iff {F₀ F₁ : Type*} [Nonempty F₁] {m₀ m₁ n₀ : ℕ}
    (h₀ : n₀ ≤ m₀) (h₁ : n₀ ≤ m₁) {P₀ : RegularTree n₀ → SeedData F₀ m₀ n₀}
    {P₁ : RegularTree n₀ → SeedData F₁ m₁ n₀}
    (h : ∀ (t t' : RegularTree n₀) (i j : Fin n₀),
      cluster h₀ (P₀ t) i = cluster h₀ (P₀ t') j ↔ cluster h₁ (P₁ t) i = cluster h₁ (P₁ t') j) :
    (patternClusterVariables h₁ P₁).encard = (patternClusterVariables h₀ P₀).encard ∧
      (patternClusters h₁ P₁).encard = (patternClusters h₀ P₀).encard := by
  classical
  let f : F₀ → F₁ := fun x =>
    if hx : ∃ p : RegularTree n₀ × Fin n₀, cluster h₀ (P₀ p.1) p.2 = x then
      cluster h₁ (P₁ hx.choose.1) hx.choose.2
    else Classical.arbitrary F₁
  have hf : ∀ t i, f (cluster h₀ (P₀ t) i) = cluster h₁ (P₁ t) i := fun t i => by
    have hx : ∃ p : RegularTree n₀ × Fin n₀, cluster h₀ (P₀ p.1) p.2 = cluster h₀ (P₀ t) i :=
      ⟨(t, i), rfl⟩
    simp only [f, dif_pos hx]
    exact (h _ _ _ _).1 hx.choose_spec
  have hcl : ∀ t, clusterVariables h₁ (P₁ t) = f '' clusterVariables h₀ (P₀ t) := fun t => by
    rw [clusterVariables, clusterVariables, ← Set.range_comp]
    exact congrArg Set.range (funext fun i => (hf t i).symm)
  have hinj : Set.InjOn f (patternClusterVariables h₀ P₀) := by
    intro x hx x' hx' hxx
    obtain ⟨t, i, rfl⟩ := Set.mem_iUnion.1 hx
    obtain ⟨t', j, rfl⟩ := Set.mem_iUnion.1 hx'
    rw [hf, hf] at hxx
    exact (h _ _ _ _).2 hxx
  have hsub : ∀ t, clusterVariables h₀ (P₀ t) ⊆ patternClusterVariables h₀ P₀ := fun t =>
    Set.subset_iUnion (fun t => clusterVariables h₀ (P₀ t)) t
  refine ⟨?_, ?_⟩
  · have : patternClusterVariables h₁ P₁ = f '' patternClusterVariables h₀ P₀ := by
      rw [patternClusterVariables, patternClusterVariables, Set.image_iUnion]
      exact congrArg Set.iUnion (funext hcl)
    rw [this, hinj.encard_image]
  · have : patternClusters h₁ P₁ = (fun S => f '' S) '' patternClusters h₀ P₀ := by
      rw [patternClusters, patternClusters, ← Set.range_comp]
      exact congrArg Set.range (funext hcl)
    rw [this, Set.InjOn.encard_image]
    rintro _ ⟨t, rfl⟩ _ ⟨t', rfl⟩ hSS
    exact (hinj.image_eq_image_iff (hsub t) (hsub t')).1 hSS

/-- In the transfer of the counts, equal cluster variables of a pattern `P'` with the exchange
matrices of `Σ•_n` come from equal cluster variables of `Σ•_n`. -/
private theorem cnt_cluster_dPattern_eq_of_eq [CharZero K] {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (hmn : n ≤ m) {P' : RegularTree n → SeedData F m n} (hP' : IsSeedPattern K hmn P')
    (hB : principalPart (TypeD.le_two_mul_add_two n)
      (TypeD.dPattern K n .root).extExchangeMatrix = principalPart hmn (P' .root).extExchangeMatrix)
    (hZ : ZSpanCondition (P' .root).extExchangeMatrix (TypeD.dPattern K n .root).extExchangeMatrix)
    {t t' : RegularTree n} {i j : Fin n} (h : cluster hmn (P' t) i = cluster hmn (P' t') j) :
    cluster (TypeD.le_two_mul_add_two n) (TypeD.dPattern K n t) i =
      cluster (TypeD.le_two_mul_add_two n) (TypeD.dPattern K n t') j := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hD := (TypeD.isSeedPattern_dPattern K hn).1
  have hx0 : (TypeD.dPattern K n .root).extCluster =
      (TypeD.dSeed K (TypeD.radiusTriangulation n) (TypeD.initialLabelling n)).extCluster := by
    rw [(TypeD.isSeedPattern_dPattern K hn).2]
  haveI : Fact (AlgebraicIndependent ℚ (TypeD.dPattern K n .root).extCluster) :=
    ⟨(hD.1 .root).1.algebraicIndependent_rat⟩
  haveI : Fact (AlgebraicIndependent ℚ (P' .root).extCluster) :=
    ⟨(hP'.1 .root).1.algebraicIndependent_rat⟩
  haveI := Fact.mk (TypeD.cnt_algebraicIndependent_cntY n)
  obtain ⟨φ, ψ, hψ₁, hψ₂, hx, -⟩ := hD.exists_rescaling_of_zSpanCondition _ hmn hP' .root hB hZ
  obtain ⟨χ, hχY, hχ⟩ := TypeD.cnt_exists_hom hmn (x := (P' .root).extCluster) (y := TypeD.cntY n)
  set θ := χ.comp ψ with hθdef
  have hθ : ∀ i : Fin (2 * n + 2), n ≤ (i : ℕ) →
      θ ⟨(TypeD.dPattern K n .root).extCluster i, mem_universalSemifield_self _ i⟩ = 1 :=
    fun i hi => by
      rw [hθdef, FZSemifieldHom.coe_comp, Function.comp_apply]
      exact cnt_hom_eq_one χ hχ (hψ₂ i hi)
  have hpv : ∀ a, TypeD.cntHomVal θ (TypeD.var K (.p a)) = TypeD.cntY n (TypeD.cntInitialIdx n a) :=
    fun a => by
      rw [TypeD.cntHomVal_mk θ (hx0 ▸ TypeD.cnt_mem_p K hn a),
        show (⟨TypeD.var K (.p a), hx0 ▸ TypeD.cnt_mem_p K hn a⟩ :
          universalSemifield (TypeD.dPattern K n .root).extCluster) =
          ⟨(TypeD.dPattern K n .root).extCluster
            (Fin.castLE (TypeD.le_two_mul_add_two n) (TypeD.cntInitialIdx n a)),
            mem_universalSemifield_self _ _⟩ from Subtype.ext (by
          change TypeD.var K (.p a) = (TypeD.dPattern K n .root).extCluster _
          rw [hx0, TypeD.cnt_extCluster_p K hn a]),
        hθdef, FZSemifieldHom.coe_comp, Function.comp_apply,
        cnt_hom_eq_of_eq_mul χ hχ (mem_universalSemifield_self _ _)
          (hψ₁ (Fin.castLE (TypeD.le_two_mul_add_two n) (TypeD.cntInitialIdx n a))
            (TypeD.cntInitialIdx n a).isLt)]
      exact hχY _
  have hzi : AlgebraicIndependent ℚ fun a => TypeD.cntHomVal θ (TypeD.var K (.p a)) := by
    rw [funext hpv]
    exact (TypeD.cnt_algebraicIndependent_cntY n).comp _ (TypeD.cnt_initialIdx_injective hn)
  have hval : ∀ (t : RegularTree n) (i : Fin n),
      TypeD.cntHomVal θ (cluster (TypeD.le_two_mul_add_two n) (TypeD.dPattern K n t) i) =
        (χ ⟨cluster hmn (P' t) i, hP'.extCluster_mem_universalSemifield hmn .root t _⟩).1 := by
    intro t i
    change TypeD.cntHomVal θ
      ((TypeD.dPattern K n t).extCluster (Fin.castLE (TypeD.le_two_mul_add_two n) i)) = _
    rw [TypeD.cntHomVal_mk θ (hD.extCluster_mem_universalSemifield _ .root t _), hθdef,
      FZSemifieldHom.coe_comp, Function.comp_apply]
    exact congrArg Subtype.val (cnt_hom_eq_of_eq_mul χ hχ _ (hx t i))
  refine TypeD.cnt_cluster_eq_of_homVal_eq K hn θ hθ hzi ?_
  rw [hval, hval]
  exact congrArg (fun z => (χ z).1) (Subtype.ext h)

/-- **Cluster variables and clusters in type `D_n`**: for `n ≥ 4`, a seed pattern of type `D_n`
has `n²` cluster variables and `N = (3n - 2)/n · binom(2n - 2, n - 1)` clusters. -/
@[cluster_algebras "prop_type_D_counts"]
theorem IsSeedPattern.encard_of_isPatternOfType_D [CharZero K] {n : ℕ} (hn : 4 ≤ n)
    (hmn : n ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hX : IsPatternOfType hmn P [.D n hn]) :
    (patternClusterVariables hmn P).encard = (n ^ 2 : ℕ) ∧
      ∃ N : ℕ, (patternClusters hmn P).encard = N ∧
        n * N = (3 * n - 2) * (2 * n - 2).choose (n - 1) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hn3 : 3 ≤ n := by omega
  obtain ⟨-, P', hP', -, hpp, hcv, hcl, -⟩ :=
    hP.exists_reindex_principalPart_eq_dPattern hn hmn hX
  rw [← hcv, ← hcl]
  have hD := (TypeD.isSeedPattern_dPattern K hn3).1
  have hB : principalPart (TypeD.le_two_mul_add_two n)
      (TypeD.dPattern K n .root).extExchangeMatrix =
      principalPart hmn (P' .root).extExchangeMatrix := (hpp _).symm
  have hZ : ZSpanCondition (P' .root).extExchangeMatrix
      (TypeD.dPattern K n .root).extExchangeMatrix := by
    refine zSpanCondition_of_span_eq_top ?_ _
    rw [(TypeD.isSeedPattern_dPattern K hn3).2]
    exact TypeD.span_labelledMatrix_initial hn3
  obtain ⟨h₁, h₂⟩ := cnt_encard_eq_of_cluster_iff (TypeD.le_two_mul_add_two n) hmn
    fun t t' i j => ⟨fun h => hD.cluster_eq_of_zSpanCondition _ hmn hP' hB hZ h,
      cnt_cluster_dPattern_eq_of_eq hn3 hmn hP' hB hZ⟩
  obtain ⟨e₁, N, e₂, e₃⟩ := TypeD.encard_dPattern K hn3
  exact ⟨h₁.trans e₁, N, h₂.trans e₂, e₃⟩

end ClusterAlgebras

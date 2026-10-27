/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.TypeD.Triangulation
public import Mathlib.Data.Finset.Powerset

/-!
# The number of tagged triangulations

The once-punctured `n`-gon has `(3n - 2)/n · binom(2n - 2, n - 1)` tagged triangulations. They
are counted directly through the three kinds, weighting a radius set `R` by the number
`∏_{a ∈ R} C_{g_R(a) - 1}` of choices of triangulations of its sector runs.

## Main statements

* `ClusterAlgebras.TypeD.sum_prod_catalan_consecutivePairs`: weighted subsets of an interval.
* `ClusterAlgebras.TypeD.two_mul_sum_prod_catalan_gap`: the weight of all radius sets.
* `ClusterAlgebras.TypeD.mul_ncard_isTaggedTriangulation`: the number of tagged
  triangulations.

## Implementation notes

* The counts are stated without division: `2 N = (n + 1) C_n` for the weight sum and
  `n d_n = (3n - 2) binom(2n - 2, n - 1)` for the number `d_n` of tagged triangulations, which
  determine `N` and `d_n`.
* The consecutive pairs `a < a'` of a finite set `A ⊆ ℕ` are the pairs of elements with no
  element of `A` strictly between them (`consecutivePairs`).
-/

@[expose] public section

namespace ClusterAlgebras.TypeD

/-- The pairs `a < a'` of consecutive elements of a finite set `A` of natural numbers. -/
@[cluster_algebras "lem_catalan_subsets"]
def consecutivePairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun p => p.1 < p.2 ∧ ∀ b ∈ A, ¬(p.1 < b ∧ b < p.2)

/-- A pair `p` is a consecutive pair of `A` iff both entries lie in `A`, `p.1 < p.2`, and no
element of `A` lies strictly between them. -/
@[simp]
theorem mem_consecutivePairs {A : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ consecutivePairs A ↔
      (p.1 ∈ A ∧ p.2 ∈ A) ∧ p.1 < p.2 ∧ ∀ b ∈ A, ¬(p.1 < b ∧ b < p.2) := by
  simp only [consecutivePairs, Finset.mem_filter, Finset.mem_product]

/-- The weight `∏ C_{a' - a - 1}` of a finite set of naturals. -/
private def cpWeight (A : Finset ℕ) : ℕ :=
  ∏ p ∈ consecutivePairs A, catalanNumber (p.2 - p.1 - 1)

/-- A singleton has no consecutive pairs. -/
private theorem consecutivePairs_singleton (m : ℕ) : consecutivePairs {m} = ∅ := by
  ext p
  simp only [mem_consecutivePairs, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2 h3
  omega

/-- Adding an element `L` above the maximum `b` of `B` adds the single consecutive pair
`(b, L)`. -/
private theorem consecutivePairs_insert {B : Finset ℕ} {b L : ℕ} (hb : b ∈ B)
    (hB : ∀ x ∈ B, x ≤ b) (hbL : b < L) :
    consecutivePairs (insert L B) = insert (b, L) (consecutivePairs B) := by
  ext ⟨x, y⟩
  simp only [mem_consecutivePairs, Finset.mem_insert, Prod.mk.injEq, forall_eq_or_imp]
  grind

/-- Adding an element `L` above the maximum `b` multiplies the weight by `C_{L - b - 1}`. -/
private theorem cpWeight_insert {B : Finset ℕ} {b L : ℕ} (hb : b ∈ B)
    (hB : ∀ x ∈ B, x ≤ b) (hbL : b < L) :
    cpWeight (insert L B) = catalanNumber (L - b - 1) * cpWeight B := by
  have hL : L ∉ B := fun h => absurd (hB L h) (by omega)
  rw [cpWeight, consecutivePairs_insert hb hB hbL,
    Finset.prod_insert (by simp [hL]), cpWeight]

/-- The sets `A ⊆ [m, M]` containing `m` and `M`. -/
private def endSets (m M : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc m M).powerset.filter fun A => m ∈ A ∧ M ∈ A

/-- Membership in `endSets m M`. -/
private theorem mem_endSets {m M : ℕ} {A : Finset ℕ} :
    A ∈ endSets m M ↔ (∀ x ∈ A, m ≤ x ∧ x ≤ M) ∧ m ∈ A ∧ M ∈ A := by
  simp only [endSets, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_Icc]

private theorem endSets_self (m : ℕ) : endSets m m = {{m}} := by
  ext A
  rw [mem_endSets, Finset.mem_singleton]
  constructor
  · rintro ⟨h, hm, -⟩
    exact Finset.eq_singleton_iff_unique_mem.2 ⟨hm, fun x hx => le_antisymm (h x hx).2 (h x hx).1⟩
  · rintro rfl
    simp

/-- Removing the largest element `M` from the sets in `endSets m M` sorts them by their second
largest element `b`. -/
private theorem sum_sigma_endSets {m M : ℕ} (hlt : m < M) :
    ∑ x ∈ (Finset.Ico m M).sigma fun b => endSets m b,
      catalanNumber (M - x.1 - 1) * cpWeight x.2 = ∑ A ∈ endSets m M, cpWeight A := by
  refine Finset.sum_nbij' (fun x => insert M x.2) (fun A => ⟨(A.erase M).sup id, A.erase M⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨b, B⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Ico, mem_endSets] at hx ⊢
    obtain ⟨⟨hb1, hb2⟩, hB, hmB, hbB⟩ := hx
    refine ⟨fun x hx => ?_, Finset.mem_insert_of_mem hmB, Finset.mem_insert_self _ _⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · omega
    · grind
  · intro A hA
    simp only [mem_endSets] at hA
    obtain ⟨hA, hmA, hMA⟩ := hA
    have hmA' : m ∈ A.erase M := Finset.mem_erase.2 ⟨hlt.ne, hmA⟩
    obtain ⟨b, hb, hbsup⟩ := Finset.exists_mem_eq_sup _ ⟨m, hmA'⟩ id
    have hbsup' : (A.erase M).sup id = b := hbsup
    have hle : ∀ x ∈ A.erase M, x ≤ b := fun x hx => hbsup' ▸ Finset.le_sup (f := id) hx
    have hbM : b < M :=
      lt_of_le_of_ne (hA b (Finset.mem_of_mem_erase hb)).2 (Finset.ne_of_mem_erase hb)
    simp only [Finset.mem_sigma, Finset.mem_Ico, mem_endSets]
    rw [hbsup']
    exact ⟨⟨hle m hmA', hbM⟩, fun x hx => ⟨(hA x (Finset.mem_of_mem_erase hx)).1, hle x hx⟩,
      hmA', hb⟩
  · rintro ⟨b, B⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Ico, mem_endSets] at hx
    obtain ⟨⟨hb1, hb2⟩, hB, hmB, hbB⟩ := hx
    have hMB : M ∉ B := fun h => absurd (hB M h).2 (by omega)
    simp only [Finset.erase_insert hMB]
    congr 1
    exact le_antisymm (Finset.sup_le fun x hx => (hB x hx).2) (Finset.le_sup (f := id) hbB)
  · intro A hA
    simp only [mem_endSets] at hA
    exact Finset.insert_erase hA.2.2
  · rintro ⟨b, B⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Ico, mem_endSets] at hx
    obtain ⟨⟨hb1, hb2⟩, hB, hmB, hbB⟩ := hx
    exact (cpWeight_insert hbB (fun x hx => (hB x hx).2) hb2).symm

/-- **Weighted subsets of an interval**, for the interval `[m, M]`. -/
private theorem sum_cpWeight_endSets (m M : ℕ) (hmM : m ≤ M) :
    ∑ A ∈ endSets m M, cpWeight A = catalanNumber (M - m) := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  rcases hmM.eq_or_lt with rfl | hlt
  · rw [endSets_self, Finset.sum_singleton, cpWeight, consecutivePairs_singleton]
    simp
  rw [← sum_sigma_endSets hlt, Finset.sum_sigma]
  have : ∀ b ∈ Finset.Ico m M, ∑ B ∈ endSets m b, catalanNumber (M - b - 1) * cpWeight B =
      catalanNumber (M - b - 1) * catalanNumber (b - m) := by
    intro b hb
    rw [Finset.mem_Ico] at hb
    rw [← Finset.mul_sum, ih b hb.2 hb.1]
  rw [Finset.sum_congr rfl this, Finset.sum_Ico_eq_sum_range]
  obtain ⟨k, hk⟩ : ∃ k, M - m = k + 1 := ⟨M - m - 1, by omega⟩
  rw [hk, catalanNumber_succ]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [mul_comm]
  congr 2 <;> omega

/-- **Weighted subsets of an interval**: the sum over the sets `A ⊆ [0, L]`
containing `0` and `L` of `∏ C_{a' - a - 1}`, the product over the pairs `a < a'` of consecutive
elements of `A`, is `C_L`. -/
@[cluster_algebras "lem_catalan_subsets"]
theorem sum_prod_catalan_consecutivePairs (L : ℕ) :
    ∑ A ∈ (Finset.range (L + 1)).powerset.filter (fun A => 0 ∈ A ∧ L ∈ A),
      ∏ p ∈ consecutivePairs A, catalanNumber (p.2 - p.1 - 1) = catalanNumber L := by
  have h : (Finset.range (L + 1)).powerset.filter (fun A => 0 ∈ A ∧ L ∈ A) = endSets 0 L := by
    rw [endSets, show Finset.Icc 0 L = Finset.range (L + 1) by
      ext x
      simp only [Finset.mem_range, Finset.mem_Icc]
      omega]
  rw [h]
  simpa [cpWeight] using sum_cpWeight_endSets 0 L (Nat.zero_le L)

/-- `∑_{M < N} ∑_{k ≤ M} h(k) = ∑_{k < N} (N - k) h(k)`. -/
private theorem sum_range_sum_range_succ (h : ℕ → ℕ) (N : ℕ) :
    ∑ M ∈ Finset.range N, ∑ k ∈ Finset.range (M + 1), h k =
      ∑ k ∈ Finset.range N, (N - k) * h k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (N + 1 - k) * h k),
      Finset.sum_range_succ h, show N + 1 - N = 1 by omega, one_mul, ← add_assoc,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show N + 1 - k = (N - k) + 1 by omega]
    ring

/-- `2 ∑_{k < N} (N - k) C_{N-1-k} C_k = (N + 1) C_N` for `N ≥ 1`. -/
private theorem two_mul_sum_sub_mul_catalan {N : ℕ} (hN : 0 < N) :
    2 * ∑ k ∈ Finset.range N, (N - k) * (catalanNumber (N - 1 - k) * catalanNumber k) =
      (N + 1) * catalanNumber N := by
  have hrefl : ∑ k ∈ Finset.range N, (N - k) * (catalanNumber (N - 1 - k) * catalanNumber k) =
      ∑ k ∈ Finset.range N, (k + 1) * (catalanNumber (N - 1 - k) * catalanNumber k) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show N - (N - 1 - k) = k + 1 by omega, show N - 1 - (N - 1 - k) = k by omega,
      mul_comm (catalanNumber k)]
  rw [two_mul]
  nth_rw 2 [hrefl]
  rw [← Finset.sum_add_distrib]
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [catalanNumber_succ N', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show N' + 1 - 1 - k = N' - k by omega, ← add_mul,
    show N' + 1 - k + (k + 1) = N' + 1 + 1 by omega]
  ring

/-- The positions whose values lie in a set of naturals. -/
private def toFin {n : ℕ} (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun a => (a : ℕ) ∈ A

/-- The values of `toFin A` are `A`, when `A ⊆ [0, n - 1]`. -/
private theorem map_toFin {n : ℕ} {A : Finset ℕ} (hA : ∀ x ∈ A, x < n) :
    (toFin A : Finset (Fin n)).map Fin.valEmbedding = A := by
  ext x
  simp only [toFin, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  exact ⟨fun ⟨a, ha, e⟩ => e ▸ ha, fun hx => ⟨⟨x, hA x hx⟩, hx, rfl⟩⟩

/-- `toFin` recovers a set of positions from its values. -/
private theorem toFin_map {n : ℕ} (R : Finset (Fin n)) : toFin (R.map Fin.valEmbedding) = R := by
  ext a
  simp [toFin, Fin.val_inj]

open Classical in
/-- The triangulations of the run `[u, v]`, as a finset. -/
private noncomputable def runTriangulations (u v : ℤ) : Finset (Finset (ℤ × ℤ)) :=
  (intRange u v ×ˢ intRange u v).powerset.filter (IsRunTriangulation u v)

/-- Membership in `runTriangulations u v`. -/
private theorem mem_runTriangulations {u v : ℤ} {T : Finset (ℤ × ℤ)} :
    T ∈ runTriangulations u v ↔ IsRunTriangulation u v T := by
  simp only [runTriangulations, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨And.right, fun h => ⟨fun c hc => ?_, h⟩⟩
  obtain ⟨h1, h2, h3, -⟩ := h.1 c hc
  simp only [Finset.mem_product, mem_intRange]
  omega

/-- The run `[u, v]` has `C_{v - u - 1}` triangulations. -/
private theorem card_runTriangulations {u v : ℤ} (huv : u < v) :
    (runTriangulations u v).card = catalanNumber (v - u - 1).toNat := by
  have h := encard_setOf_isRunTriangulation huv
  have : {T | IsRunTriangulation u v T} = ↑(runTriangulations u v) := by
    ext T
    simp [mem_runTriangulations]
  rw [this, Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

variable {n : ℕ} [NeZero n]

/-- The residue of `x < n` is `x`. -/
private theorem vtx_natCast_of_lt {x : ℕ} (hx : x < n) :
    (vtx (x : ℤ) : Fin n) = ⟨x, hx⟩ := by
  apply Fin.ext
  have h := vtx_val (n := n) (x : ℤ)
  rw [Int.emod_eq_of_lt (by omega) (by omega)] at h
  exact_mod_cast h

/-- The gap of `a ∈ R` is the least `t ≥ 1` with `a + t ∈ R` (mod `n`). -/
private theorem gap_eq_of {R : Finset (Fin n)} {a : Fin n} (ha : a ∈ R) {t : ℕ} (ht : 0 < t)
    (hmem : (vtx ((a : ℤ) + (t : ℤ)) : Fin n) ∈ R)
    (hnot : ∀ s : ℕ, 0 < s → s < t → (vtx ((a : ℤ) + (s : ℤ)) : Fin n) ∉ R) :
    gap R a = t := by
  obtain ⟨h1, -, h3, h4⟩ := gap_spec ha
  rcases lt_trichotomy (gap R a) t with h | h | h
  · exact absurd h3 (hnot _ (by omega) h)
  · exact h
  · exact absurd hmem (h4 t ht h)

omit [NeZero n] in
private theorem mem_map_val_iff {R : Finset (Fin n)} {x : ℕ} (hx : x < n) :
    x ∈ R.map Fin.valEmbedding ↔ (⟨x, hx⟩ : Fin n) ∈ R := by
  simp only [Finset.mem_map, Fin.valEmbedding_apply]
  exact ⟨fun ⟨a, ha, e⟩ => e ▸ ha, fun h => ⟨_, h, rfl⟩⟩

omit [NeZero n] in
private theorem lt_of_mem_map_val {R : Finset (Fin n)} {x : ℕ}
    (hx : x ∈ R.map Fin.valEmbedding) : x < n := by
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
  exact a.isLt

/-- The gap of the greatest element `M` of `R` wraps around to the least element `m`. -/
private theorem gap_max_eq {R : Finset (Fin n)} {mF MF : Fin n} (hm : mF ∈ R) (hM : MF ∈ R)
    (hR : ∀ a ∈ R, mF ≤ a ∧ a ≤ MF) : gap R MF = n - ((MF : ℕ) - mF) := by
  have hmM : (mF : ℕ) ≤ MF := (hR mF hm).2
  have hlt := MF.isLt
  refine gap_eq_of hM (by omega) ?_ ?_
  · rw [show ((MF : ℕ) : ℤ) + ((n - ((MF : ℕ) - mF) : ℕ) : ℤ) = ((mF : ℕ) : ℤ) + n by omega,
      vtx_add_n, vtx_coe]
    exact hm
  · intro s hs hst hmem
    by_cases hsn : (MF : ℕ) + s < n
    · rw [show ((MF : ℕ) : ℤ) + (s : ℤ) = ((MF + s : ℕ) : ℤ) by omega,
        vtx_natCast_of_lt hsn] at hmem
      have := Fin.le_def.1 (hR _ hmem).2
      simp only at this
      omega
    · rw [show ((MF : ℕ) : ℤ) + (s : ℤ) = ((MF + s - n : ℕ) : ℤ) + n by omega,
        vtx_add_n, vtx_natCast_of_lt (show MF + s - n < n by omega)] at hmem
      have := Fin.le_def.1 (hR _ hmem).1
      simp only at this
      omega

/-- The gap of the first entry of a consecutive pair of `R` is the difference of the pair. -/
private theorem gap_vtx_eq_of_mem_consecutivePairs {R : Finset (Fin n)} {p : ℕ × ℕ}
    (hp : p ∈ consecutivePairs (R.map Fin.valEmbedding)) :
    gap R (vtx (p.1 : ℤ)) = p.2 - p.1 := by
  simp only [mem_consecutivePairs] at hp
  obtain ⟨⟨hp1, hp2⟩, hp12, hpb⟩ := hp
  have hn1 := lt_of_mem_map_val hp1
  have hn2 := lt_of_mem_map_val hp2
  rw [vtx_natCast_of_lt hn1]
  refine gap_eq_of ((mem_map_val_iff _).1 hp1) (by omega) ?_ ?_
  · rw [show ((p.1 : ℕ) : ℤ) + ((p.2 - p.1 : ℕ) : ℤ) = ((p.2 : ℕ) : ℤ) by omega,
      vtx_natCast_of_lt hn2]
    exact (mem_map_val_iff _).1 hp2
  · intro s hs hst hmem
    rw [show ((p.1 : ℕ) : ℤ) + (s : ℤ) = ((p.1 + s : ℕ) : ℤ) by omega,
      vtx_natCast_of_lt (by omega)] at hmem
    exact hpb (p.1 + s) ((mem_map_val_iff _).2 hmem) ⟨by omega, by omega⟩

/-- Away from the greatest element `M` of `R`, the gaps of `R` are the differences of its
consecutive pairs. -/
private theorem prod_erase_catalan_gap {R : Finset (Fin n)} {mF MF : Fin n} (hM : MF ∈ R)
    (hR : ∀ a ∈ R, mF ≤ a ∧ a ≤ MF) :
    ∏ a ∈ R.erase MF, catalanNumber (gap R a - 1) = cpWeight (R.map Fin.valEmbedding) := by
  symm
  refine Finset.prod_nbij (fun p => (vtx (p.1 : ℤ) : Fin n)) ?_ ?_ ?_
    fun p hp => by rw [gap_vtx_eq_of_mem_consecutivePairs hp]
  · intro p hp
    simp only [mem_consecutivePairs] at hp
    obtain ⟨⟨h1, h2⟩, h12, -⟩ := hp
    rw [vtx_natCast_of_lt (lt_of_mem_map_val h1), Finset.mem_erase]
    refine ⟨fun h => ?_, (mem_map_val_iff _).1 h1⟩
    have : p.2 ≤ MF := by
      obtain ⟨a, ha, e⟩ := Finset.mem_map.1 h2
      rw [← e]
      exact (hR a ha).2
    rw [Fin.ext_iff] at h
    simp only at h
    omega
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, mem_consecutivePairs] at hp hq
    obtain ⟨⟨hp1, hp2⟩, hp12, hpb⟩ := hp
    obtain ⟨⟨hq1, hq2⟩, hq12, hqb⟩ := hq
    simp only at hpq
    rw [vtx_natCast_of_lt (lt_of_mem_map_val hp1), vtx_natCast_of_lt (lt_of_mem_map_val hq1),
      Fin.mk.injEq] at hpq
    refine Prod.ext hpq ?_
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hqb p.2 hp2 ⟨by omega, h⟩
    · exact hpb q.2 hq2 ⟨by omega, h⟩
  · intro a ha
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at ha
    have haM : (a : ℕ) < MF := lt_of_le_of_ne (hR a ha.1).2 (Fin.val_ne_of_ne ha.2)
    have hS : ((R.map Fin.valEmbedding).filter fun x => (a : ℕ) < x).Nonempty :=
      ⟨MF, Finset.mem_filter.2 ⟨(mem_map_val_iff MF.isLt).2 hM, haM⟩⟩
    have hmin := Finset.min'_mem _ hS
    rw [Finset.mem_filter] at hmin
    refine ⟨((a : ℕ), ((R.map Fin.valEmbedding).filter fun x => (a : ℕ) < x).min' hS), ?_,
      vtx_coe a⟩
    simp only [Finset.mem_coe, mem_consecutivePairs]
    refine ⟨⟨(mem_map_val_iff a.isLt).2 ha.1, hmin.1⟩, hmin.2, fun b hb hab => ?_⟩
    exact (not_le.2 hab.2) (Finset.min'_le _ b (Finset.mem_filter.2 ⟨hb, hab.1⟩))

/-- For `R` with least element `m` and greatest element `M`, the weight
`∏_{a ∈ R} C_{g_R(a) - 1}` is `C_{n - 1 - (M - m)}` times the weight of the consecutive pairs
of `R` inside `[m, M]`. -/
private theorem prod_catalan_gap_eq {R : Finset (Fin n)} {mF MF : Fin n} (hm : mF ∈ R)
    (hM : MF ∈ R) (hR : ∀ a ∈ R, mF ≤ a ∧ a ≤ MF) :
    ∏ a ∈ R, catalanNumber (gap R a - 1) =
      catalanNumber (n - 1 - ((MF : ℕ) - mF)) * cpWeight (R.map Fin.valEmbedding) := by
  rw [← Finset.mul_prod_erase R _ hM, gap_max_eq hm hM hR, prod_erase_catalan_gap hM hR]
  congr 2
  omega

/-- A nonempty `R ⊆ [0, n - 1]` is a set of naturals with least element `m` and greatest
element `M` for exactly one pair `m ≤ M < n`. -/
private theorem sum_prod_catalan_gap_eq_sum_biUnion :
    ∑ R ∈ (Finset.univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
      ∏ a ∈ R, catalanNumber (gap R a - 1) =
      ∑ A ∈ ((Finset.range n).sigma fun M => Finset.range (M + 1)).biUnion
          (fun x => endSets x.2 x.1),
        ∏ a ∈ toFin (n := n) A, catalanNumber (gap (toFin A) a - 1) := by
  refine Finset.sum_nbij' (fun R => R.map Fin.valEmbedding) (toFin (n := n)) ?_ ?_
    (fun R _ => toFin_map R) ?_ (fun R _ => by rw [toFin_map])
  · intro R hR
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and] at hR
    simp only [Finset.mem_biUnion, Finset.mem_sigma, Finset.mem_range]
    refine ⟨⟨R.max' hR, R.min' hR⟩, ⟨(R.max' hR).isLt,
      Nat.lt_succ_of_le (Fin.le_def.1 (R.min'_le_max' hR))⟩, ?_⟩
    rw [mem_endSets]
    refine ⟨fun x hx => ?_, Finset.mem_map_of_mem _ (R.min'_mem hR),
      Finset.mem_map_of_mem _ (R.max'_mem hR)⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
    exact ⟨Fin.le_def.1 (R.min'_le a ha), Fin.le_def.1 (R.le_max' a ha)⟩
  · intro A hA
    simp only [Finset.mem_biUnion, Finset.mem_sigma, Finset.mem_range] at hA
    obtain ⟨⟨M, m⟩, ⟨hM, hm⟩, hA⟩ := hA
    dsimp only at hM hm hA
    rw [mem_endSets] at hA
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    exact ⟨⟨m, by omega⟩, by simp [toFin, hA.2.1]⟩
  · intro A hA
    simp only [Finset.mem_biUnion, Finset.mem_sigma, Finset.mem_range] at hA
    obtain ⟨⟨M, m⟩, ⟨hM, hm⟩, hA⟩ := hA
    dsimp only at hM hm hA
    rw [mem_endSets] at hA
    exact map_toFin fun x hx => by have := (hA.1 x hx).2; omega

private theorem pairwiseDisjoint_endSets (I : Finset ((_ : ℕ) × ℕ)) :
    (I : Set ((_ : ℕ) × ℕ)).PairwiseDisjoint fun x => endSets x.2 x.1 := by
  rintro ⟨M, m⟩ - ⟨M', m'⟩ - hne
  rw [Function.onFun, Finset.disjoint_left]
  intro A hA hA'
  rw [mem_endSets] at hA hA'
  apply hne
  have h1 := hA.1 _ hA'.2.1
  have h2 := hA'.1 _ hA.2.1
  have h3 := hA.1 _ hA'.2.2
  have h4 := hA'.1 _ hA.2.2
  simp only at h1 h2 h3 h4
  obtain rfl : M = M' := by omega
  obtain rfl : m = m' := by omega
  rfl

/-- The weight of the radius sets with greatest element `M`, summed over their least
element. -/
private theorem sum_sum_endSets_prod_catalan_gap {M : ℕ} (hM : M < n) :
    ∑ m ∈ Finset.range (M + 1), ∑ A ∈ endSets m M,
        ∏ a ∈ toFin (n := n) A, catalanNumber (gap (toFin A) a - 1) =
      ∑ k ∈ Finset.range (M + 1), catalanNumber (n - 1 - k) * catalanNumber k := by
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show catalanNumber k = catalanNumber (M - (M + 1 - 1 - k)) from congrArg _ (by omega),
    ← sum_cpWeight_endSets (M + 1 - 1 - k) M (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [mem_endSets] at hA
  have hAn : ∀ x ∈ A, x < n := fun x hx => by have := (hA.1 x hx).2; omega
  have key := prod_catalan_gap_eq (R := toFin A) (mF := ⟨M + 1 - 1 - k, by omega⟩)
    (MF := ⟨M, hM⟩)
    (by simpa [toFin] using hA.2.1)
    (by simpa [toFin] using hA.2.2)
    (fun a ha => by
      simp only [toFin, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact ⟨Fin.le_def.2 (hA.1 _ ha).1, Fin.le_def.2 (hA.1 _ ha).2⟩)
  rw [key, map_toFin hAn]
  congr 3
  dsimp only
  omega

/-- **The weight of all radius sets**: `∑_{∅ ≠ R ⊆ [1, n]} ∏_{a ∈ R} C_{g_R(a) - 1} =
(n + 1) C_n / 2`, stated as `2 ∑ = (n + 1) C_n`. -/
@[cluster_algebras "lem_D_weight_sum"]
theorem two_mul_sum_prod_catalan_gap :
    2 * ∑ R ∈ (Finset.univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
      ∏ a ∈ R, catalanNumber (gap R a - 1) = (n + 1) * catalanNumber n := by
  rw [sum_prod_catalan_gap_eq_sum_biUnion, Finset.sum_biUnion (pairwiseDisjoint_endSets _),
    Finset.sum_sigma, Finset.sum_congr rfl fun M hM =>
      sum_sum_endSets_prod_catalan_gap (Finset.mem_range.1 hM), sum_range_sum_range_succ]
  convert two_mul_sum_sub_mul_catalan (N := n) (NeZero.pos n) using 4

open Classical in
/-- There are `∏_{a ∈ R} C_{g_R(a) - 1}` tagged triangulations of kind `P_τ` with radius set
`R`. -/
private theorem card_filter_isKindP (τ : Tag) {R : Finset (Fin n)} (hR : 2 ≤ R.card) :
    (Finset.univ.filter fun T : Finset (TaggedArc n) => IsKindP T τ R).card =
      ∏ a ∈ R, catalanNumber (gap R a - 1) := by
  rw [show ∏ a ∈ R, catalanNumber (gap R a - 1) =
      ∏ a ∈ R, (runTriangulations (a : ℤ) (a + gap R a)).card from
    Finset.prod_congr rfl fun a ha => by
      have := (gap_spec ha).1
      rw [card_runTriangulations (by omega)]
      congr 1
      omega, ← Finset.card_pi]
  refine Finset.card_bij (fun T _ => fun a _ => sectorChords T R a) ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter] at hT
    rw [Finset.mem_pi]
    intro a ha
    exact mem_runTriangulations.2 (hT.2.2.2.1 a ha)
  · intro T₁ h₁ T₂ h₂ h
    rw [Finset.mem_filter] at h₁ h₂
    exact (existsUnique_isKindP τ hR (fun a => sectorChords T₁ R a) h₁.2.2.2.1).unique
      ⟨h₁.2, fun a _ => rfl⟩ ⟨h₂.2, fun a ha => (congrFun (congrFun h a) ha).symm⟩
  · intro f hf
    rw [Finset.mem_pi] at hf
    obtain ⟨T, ⟨hT, hTa⟩, -⟩ := existsUnique_isKindP τ hR
      (fun a => if h : a ∈ R then f a h else ∅) (fun a ha => by
        rw [dif_pos ha]
        exact mem_runTriangulations.1 (hf a ha))
    refine ⟨T, Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩, ?_⟩
    funext a ha
    rw [hTa a ha, dif_pos ha]

open Classical in
/-- There are `C_{n - 1}` tagged triangulations of digon kind at `a`. -/
private theorem card_filter_isDigonKind (a : Fin n) :
    (Finset.univ.filter fun T : Finset (TaggedArc n) => IsDigonKind T a).card =
      catalanNumber (n - 1) := by
  have hg := (gap_singleton a).1
  have hpos := NeZero.pos n
  rw [show catalanNumber (n - 1) = (runTriangulations (a : ℤ) (a + gap {a} a)).card by
    rw [card_runTriangulations (by omega)]
    congr 1
    omega]
  refine Finset.card_bij (fun T _ => sectorChords T {a} a) ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter] at hT
    exact mem_runTriangulations.2 hT.2.2.1
  · intro T₁ h₁ T₂ h₂ h
    rw [Finset.mem_filter] at h₁ h₂
    exact (existsUnique_isDigonKind a h₁.2.2.1).unique ⟨h₁.2, rfl⟩ ⟨h₂.2, h.symm⟩
  · intro Ta hTa
    obtain ⟨T, ⟨hT, hTa'⟩, -⟩ := existsUnique_isDigonKind a (mem_runTriangulations.1 hTa)
    exact ⟨T, Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩, hTa'⟩

open Classical in
/-- The tagged triangulations, sorted by kind. -/
private theorem setOf_isTaggedTriangulation_eq :
    {T : Finset (TaggedArc n) | IsTaggedTriangulation T} =
      ↑(((Finset.univ : Finset Tag) ×ˢ
          (Finset.univ : Finset (Fin n)).powerset.filter fun R => 2 ≤ R.card).biUnion
          (fun x => Finset.univ.filter fun T => IsKindP T x.1 x.2) ∪
        (Finset.univ : Finset (Fin n)).biUnion
          (fun a => Finset.univ.filter fun T => IsDigonKind T a)) := by
  ext T
  simp only [Set.mem_setOf_eq, Finset.coe_union, Finset.coe_biUnion, Finset.coe_filter,
    Finset.mem_univ, true_and, Finset.mem_coe, Finset.mem_product, Set.mem_union,
    Set.mem_iUnion, exists_prop, isTaggedTriangulation_iff_kind, Finset.mem_filter,
    Finset.mem_powerset, Finset.subset_univ]
  constructor
  · rintro (⟨τ, R, h⟩ | ⟨a, h⟩)
    · exact Or.inl ⟨(τ, R), h.1, h⟩
    · exact Or.inr ⟨a, h⟩
  · rintro (⟨x, -, h⟩ | ⟨a, h⟩)
    · exact Or.inl ⟨x.1, x.2, h⟩
    · exact Or.inr ⟨a, h⟩

/-- The number of tagged triangulations, counted by kind. -/
private theorem ncard_isTaggedTriangulation_eq :
    {T : Finset (TaggedArc n) | IsTaggedTriangulation T}.ncard =
      2 * ∑ R ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun R => 2 ≤ R.card),
        ∏ a ∈ R, catalanNumber (gap R a - 1) + n * catalanNumber (n - 1) := by
  classical
  have hdisjP : ((Finset.univ ×ˢ (Finset.univ : Finset (Fin n)).powerset.filter
      (fun R => 2 ≤ R.card) : Finset (Tag × Finset (Fin n))) :
        Set (Tag × Finset (Fin n))).PairwiseDisjoint
        (fun x : Tag × Finset (Fin n) => Finset.univ.filter fun T => IsKindP T x.1 x.2) := by
    intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro T h₁ h₂
    rw [Finset.mem_filter] at h₁ h₂
    obtain ⟨e1, e2⟩ := kind_unique.1 _ _ _ _ h₁.2 h₂.2
    exact hxy (Prod.ext e1 e2)
  have hdisjD : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun a => Finset.univ.filter fun T => IsDigonKind T a) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro T h₁ h₂
    rw [Finset.mem_filter] at h₁ h₂
    exact hab (kind_unique.2.2 a b h₁.2 h₂.2)
  rw [setOf_isTaggedTriangulation_eq, Set.ncard_coe_finset,
    Finset.card_union_of_disjoint, Finset.card_biUnion hdisjP, Finset.card_biUnion hdisjD,
    Finset.sum_congr rfl fun x hx => card_filter_isKindP x.1
      (Finset.mem_filter.1 (Finset.mem_product.1 hx).2).2,
    Finset.sum_congr rfl fun a _ => card_filter_isDigonKind a, Finset.sum_product]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rfl
  · rw [Finset.disjoint_left]
    intro T h₁ h₂
    simp only [Finset.mem_biUnion, Finset.mem_filter] at h₁ h₂
    obtain ⟨x, -, -, hx⟩ := h₁
    obtain ⟨a, -, -, ha⟩ := h₂
    exact kind_unique.2.1 _ _ a hx ha

/-- The weight of all radius sets, split by the size of `R`. -/
private theorem sum_prod_catalan_gap_nonempty :
    ∑ R ∈ (Finset.univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
      ∏ a ∈ R, catalanNumber (gap R a - 1) =
      ∑ R ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun R => 2 ≤ R.card),
        ∏ a ∈ R, catalanNumber (gap R a - 1) + n * catalanNumber (n - 1) := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun R => 2 ≤ R.card), Finset.filter_filter,
    Finset.filter_filter]
  congr 1
  · exact Finset.sum_congr (Finset.filter_congr fun R _ =>
      ⟨And.right, fun h => ⟨Finset.card_pos.1 (lt_of_lt_of_le two_pos h), h⟩⟩) fun _ _ => rfl
  · have hsing : ((Finset.univ : Finset (Fin n)).powerset.filter
        fun R => R.Nonempty ∧ ¬2 ≤ R.card) =
        (Finset.univ : Finset (Fin n)).map ⟨fun a => {a}, Finset.singleton_injective⟩ := by
      ext R
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
        Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk]
      grind [Finset.card_eq_one, Finset.card_pos]
    rw [hsing, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, Finset.prod_singleton, (gap_singleton _).1,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The number of tagged triangulations**: the once-punctured `n`-gon has exactly
`(3n - 2)/n · binom(2n - 2, n - 1)` tagged triangulations, stated as
`n d_n = (3n - 2) binom(2n - 2, n - 1)`. -/
@[cluster_algebras "lem_D_count_triangulations"]
theorem mul_ncard_isTaggedTriangulation (hn : 3 ≤ n) :
    n * {T : Finset (TaggedArc n) | IsTaggedTriangulation T}.ncard =
      (3 * n - 2) * (2 * n - 2).choose (n - 1) := by
  have hN := two_mul_sum_prod_catalan_gap (n := n)
  rw [sum_prod_catalan_gap_nonempty] at hN
  rw [ncard_isTaggedTriangulation_eq]
  set S := ∑ R ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun R => 2 ≤ R.card),
    ∏ a ∈ R, catalanNumber (gap R a - 1)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have e1 : (k + 1) * catalanNumber k = Nat.centralBinom k := succ_mul_catalanNumber k
  have e2 : (k + 1 + 1) * catalanNumber (k + 1) = Nat.centralBinom (k + 1) :=
    succ_mul_catalanNumber (k + 1)
  have e3 := Nat.succ_mul_centralBinom_succ k
  have e4 : (2 * (k + 1) - 2).choose (k + 1 - 1) = Nat.centralBinom k := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    congr 1
  rw [e4]
  simp only [Nat.add_sub_cancel] at hN ⊢
  rw [e1] at hN ⊢
  rw [e2] at hN
  zify [show 2 ≤ 3 * (k + 1) by omega] at hN e3 ⊢
  linear_combination (k + 1 : ℤ) * hN + e3

end ClusterAlgebras.TypeD

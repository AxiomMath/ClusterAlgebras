/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.QuasiCartan.Defs
public import ClusterAlgebras.SkewSymmetrization

/-!
# Quasi-Cartan matrices, companions, edges and sign changes

Elementary properties of quasi-Cartan matrices and their companions, of the edges of a
skew-symmetrizable matrix and of its chordless cycles, and of simultaneous sign changes.

## Main results

* `ClusterAlgebras.IsSymmetrizer.sign_eq`: for a symmetrizer of `A`, the entries `aᵢⱼ` and `aⱼᵢ`
  have the same sign.
* `ClusterAlgebras.IsSymmetrizer.sq_eq`: `(dᵢ aᵢⱼ)² = dᵢ dⱼ aᵢⱼ aⱼᵢ`, and `1 ≤ aᵢⱼ aⱼᵢ` when
  `aᵢⱼ ≠ 0`.
* `ClusterAlgebras.IsPositiveQuasiCartan.mul_le_three`: a positive quasi-Cartan matrix has
  `0 ≤ aᵢⱼ aⱼᵢ ≤ 3` for `i ≠ j`.
* `ClusterAlgebras.SkewSymmetrizable.isQuasiCartanCompanion_cartanCounterpart`: the Cartan
  counterpart is a quasi-Cartan companion, positive exactly when it is of finite type.
* `ClusterAlgebras.SkewSymmetrizable.isQCEdge_iff`: for `i ≠ j`, `{i, j}` is an edge exactly when
  `bᵢⱼ ≠ 0`, exactly when `aᵢⱼ ≠ 0` for any quasi-Cartan companion `A`.
* `ClusterAlgebras.IsQCCyclicEnumeration.card_eq`: a chordless cycle with a cyclic enumeration
  by `ℤ/p` has `p` elements.
* `ClusterAlgebras.IsQCCyclicEnumeration.bijOn_edges`: `s ↦ {v(s), v(s + 1)}` is a bijection from
  `ℤ/p` onto the edges of the cycle.
* `ClusterAlgebras.IsQuasiCartanCompanion.isQuasiCartanCompanion_qcSignChange`: sign changes
  preserve quasi-Cartan companions and their symmetrizers, and are involutions.

## References

* S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.11.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

/-! ### Quasi-Cartan matrices -/

/-- **Entries in symmetric positions have the same sign**: for a symmetrizer `d` of `A`, the
entries `aᵢⱼ` and `aⱼᵢ` are both positive, both zero, or both negative. -/
@[cluster_algebras "lem_qc_same_sign"]
theorem IsSymmetrizer.sign_eq {A : Matrix (Fin n) (Fin n) ℤ} {d : Fin n → ℤ}
    (hd : IsSymmetrizer A d) (i j : Fin n) :
    (0 < A i j ↔ 0 < A j i) ∧ (A i j = 0 ↔ A j i = 0) ∧ (A i j < 0 ↔ A j i < 0) := by
  have hi := hd.1 i
  have hj := hd.1 j
  have h := hd.2 i j
  have hpos : ∀ {a b : ℤ}, 0 < a → 0 < b → ∀ {x y : ℤ}, a * x = b * y → (0 < x ↔ 0 < y) :=
    fun ha hb x y hxy => by
      rw [← mul_pos_iff_of_pos_left ha, hxy, mul_pos_iff_of_pos_left hb]
  refine ⟨hpos hi hj h, ?_, ?_⟩
  · rw [← mul_eq_zero_iff_left hi.ne', h, mul_eq_zero_iff_left hj.ne']
  · simpa using hpos hi hj (x := -A i j) (y := -A j i) (by rw [mul_neg, mul_neg, h])

/-- **`(dᵢ aᵢⱼ)² = dᵢ dⱼ aᵢⱼ aⱼᵢ`**, and `1 ≤ aᵢⱼ aⱼᵢ` when `aᵢⱼ ≠ 0`. -/
@[cluster_algebras "lem_qc_same_sign"]
theorem IsSymmetrizer.sq_eq {A : Matrix (Fin n) (Fin n) ℤ} {d : Fin n → ℤ}
    (hd : IsSymmetrizer A d) (i j : Fin n) :
    (d i * A i j) ^ 2 = d i * d j * (A i j * A j i) ∧ (A i j ≠ 0 → 1 ≤ A i j * A j i) := by
  refine ⟨by linear_combination d i * A i j * hd.2 i j, fun hij => ?_⟩
  obtain ⟨hp, -, hn⟩ := hd.sign_eq i j
  rcases hij.lt_or_gt with h | h
  · nlinarith [hn.1 h]
  · nlinarith [hp.1 h]

/-- **A positive quasi-Cartan matrix has `0 ≤ aᵢⱼ aⱼᵢ ≤ 3`** for `i ≠ j`. -/
@[cluster_algebras "lem_qc_bound_three"]
theorem IsPositiveQuasiCartan.mul_le_three {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : IsPositiveQuasiCartan A) {i j : Fin n} (hij : i ≠ j) :
    0 ≤ A i j * A j i ∧ A i j * A j i ≤ 3 := by
  obtain ⟨⟨hdiag, -⟩, d, hd, hpos⟩ := hA
  obtain ⟨hsq, hge⟩ := hd.sq_eq i j
  have hdi := hd.1 i
  have hdj := hd.1 j
  refine ⟨?_, ?_⟩
  · by_cases h : A i j = 0
    · simp [h]
    · linarith [hge h]
  set M := diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)
  set w : Fin n → ℝ := Pi.single i ((d i : ℝ) * A i j) + Pi.single j (-(2 * d i))
  have hw : w ≠ 0 := by
    intro h
    have := congrFun h j
    simp [w, hij.symm, hdi.ne'] at this
  have hquad := hpos w hw
  have hcomp : w ⬝ᵥ (M *ᵥ w) =
      ((2 * d i * (4 * d i * d j - (d i * A i j) ^ 2) : ℤ) : ℝ) := by
    have hM : ∀ a b, M a b = d a * A a b := fun a b => by simp [M, diagonal_mul]
    simp only [w, dotProduct_add, add_dotProduct, mulVec_add, mulVec_single, single_dotProduct,
      Pi.smul_apply, op_smul_eq_mul, col_apply, hM, hdiag i, hdiag j]
    have h' : ((d i : ℝ) * A i j) = d j * A j i := by exact_mod_cast hd.2 i j
    push_cast
    linear_combination (2 * (d i : ℝ) ^ 2 * A i j) * h'
  rw [hcomp] at hquad
  have h1 : (0 : ℤ) < 2 * d i * (d i * d j) * (4 - A i j * A j i) := by
    have : (0 : ℤ) < 2 * d i * (4 * d i * d j - (d i * A i j) ^ 2) := by exact_mod_cast hquad
    rw [hsq] at this
    linarith
  have h2 : 0 < 4 - A i j * A j i := pos_of_mul_pos_right h1 (by positivity)
  linarith

/-- **The Cartan counterpart is a quasi-Cartan companion**, and it is positive exactly when it
is a Cartan matrix of finite type. -/
@[cluster_algebras "lem_qc_cartan_counterpart_companion"]
theorem SkewSymmetrizable.isQuasiCartanCompanion_cartanCounterpart
    {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B) :
    IsQuasiCartanCompanion B (cartanCounterpart B) ∧
      (IsPositiveQuasiCartan (cartanCounterpart B) ↔ IsCartanFiniteType (cartanCounterpart B)) := by
  obtain ⟨d, hd⟩ := hB
  obtain ⟨hgc, hsym⟩ := hd.isGeneralizedCartan_cartanCounterpart
  have hqc : IsQuasiCartan (cartanCounterpart B) := ⟨hgc.1, d, hsym⟩
  refine ⟨⟨hqc, fun i j hij => by simp [cartanCounterpart, hij]⟩,
    fun h => ⟨hgc, h.2⟩, fun h => ⟨hqc, h.2⟩⟩

/-! ### Edges -/

/-- **Edges and nonzero entries.** For a skew-symmetrizable `B`, `bᵢᵢ = 0` and `bᵢⱼ > 0` exactly
when `bⱼᵢ < 0`; for `i ≠ j`, `{i, j}` is an edge exactly when `bᵢⱼ ≠ 0`, exactly when
`bⱼᵢ ≠ 0`, exactly when `aᵢⱼ ≠ 0` for any quasi-Cartan companion `A`. -/
@[cluster_algebras "lem_qc_edge_entries"]
theorem SkewSymmetrizable.isQCEdge_iff {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B)
    (i j : Fin n) :
    B i i = 0 ∧ (0 < B i j ↔ B j i < 0) ∧
      (i ≠ j → (IsQCEdge B s(i, j) ↔ B i j ≠ 0) ∧ (B i j ≠ 0 ↔ B j i ≠ 0) ∧
        ∀ A, IsQuasiCartanCompanion B A → (A i j ≠ 0 ↔ B i j ≠ 0)) := by
  obtain ⟨d, hd⟩ := hB
  have hcomm : B i j ≠ 0 ↔ B j i ≠ 0 := (hd.apply_eq_zero_comm i j).not
  refine ⟨hd.apply_self_eq_zero i, hd.pos_iff_neg i j, fun hij => ⟨⟨?_, fun h => ?_⟩, hcomm,
    fun A hA => ?_⟩⟩
  · rintro ⟨a, b, hab, -, hprod⟩
    rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact left_ne_zero_of_mul hprod
    · exact right_ne_zero_of_mul hprod
  · exact ⟨i, j, rfl, hij, mul_ne_zero h (hcomm.1 h)⟩
  · rw [← abs_ne_zero, hA.2 i j hij, abs_ne_zero]

/-! ### Cyclic enumerations -/

/-- In `ℤ/p` with `3 ≤ p`, as for a cyclic enumeration, `s + 1 ≠ s`. -/
theorem IsQCCyclicEnumeration.add_one_ne_self {B : Matrix (Fin n) (Fin n) ℤ}
    {Z : Finset (Fin n)} {p : ℕ} {v : ZMod p → Fin n} (hv : IsQCCyclicEnumeration B Z v)
    (s : ZMod p) : s + 1 ≠ s := by
  intro h
  have h1 : ((1 : ℕ) : ZMod p) = 0 := by simpa using h
  have := Nat.le_of_dvd one_pos ((ZMod.natCast_eq_zero_iff 1 p).1 h1)
  have := hv.1
  omega

/-- In `ℤ/p` with `3 ≤ p`, as for a cyclic enumeration, `s + 1 + 1 ≠ s`. -/
theorem IsQCCyclicEnumeration.add_one_add_one_ne_self {B : Matrix (Fin n) (Fin n) ℤ}
    {Z : Finset (Fin n)} {p : ℕ} {v : ZMod p → Fin n} (hv : IsQCCyclicEnumeration B Z v)
    (s : ZMod p) : s + 1 + 1 ≠ s := by
  intro h
  have h1 : ((2 : ℕ) : ZMod p) = 0 := by linear_combination h
  have := Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff 2 p).1 h1)
  have := hv.1
  omega

/-- **A chordless cycle with a cyclic enumeration by `ℤ/p` has `p` elements.** -/
@[cluster_algebras "lem_qc_cycle_edges"]
theorem IsQCCyclicEnumeration.card_eq {B : Matrix (Fin n) (Fin n) ℤ} {Z : Finset (Fin n)}
    {p : ℕ} {v : ZMod p → Fin n} (hv : IsQCCyclicEnumeration B Z v) : Z.card = p := by
  obtain ⟨hp, hinj, hrange, -⟩ := hv
  have : NeZero p := ⟨by omega⟩
  have hZ : Z = Finset.univ.image v := by
    apply Finset.coe_injective
    rw [← hrange, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hZ, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]

/-- **The edges of a chordless cycle**: `s ↦ {v(s), v(s + 1)}` is a bijection from `ℤ/p` onto
the edges of `Z`. -/
@[cluster_algebras "lem_qc_cycle_edges"]
theorem IsQCCyclicEnumeration.bijOn_edges {B : Matrix (Fin n) (Fin n) ℤ} {Z : Finset (Fin n)}
    {p : ℕ} {v : ZMod p → Fin n} (hv : IsQCCyclicEnumeration B Z v) :
    Set.BijOn (fun s => s(v s, v (s + 1))) Set.univ (qcEdgesOf B Z) := by
  have hadd1 := hv.add_one_ne_self
  have hadd2 := hv.add_one_add_one_ne_self
  obtain ⟨-, hinj, hrange, hedge⟩ := hv
  have hmem : ∀ s, v s ∈ Z := fun s => Finset.mem_coe.1 (hrange ▸ Set.mem_range_self s)
  refine ⟨fun s _ => ⟨(hedge s (s + 1) (hadd1 s).symm).2 (Or.inl rfl), ?_⟩,
    fun s _ t _ hst => ?_, fun e he => ?_⟩
  · intro i hi
    rcases Sym2.mem_iff.1 hi with rfl | rfl <;> exact hmem _
  · rcases Sym2.eq_iff.1 hst with ⟨h, -⟩ | ⟨h1, h2⟩
    · exact hinj h
    · obtain rfl := hinj h1
      exact absurd (hinj h2) (hadd2 t)
  · obtain ⟨⟨a, b, rfl, hab, hprod⟩, hZ⟩ := he
    obtain ⟨s, rfl⟩ : a ∈ Set.range v := hrange ▸ hZ a (Sym2.mem_mk_left a b)
    obtain ⟨t, rfl⟩ : b ∈ Set.range v := hrange ▸ hZ b (Sym2.mem_mk_right _ b)
    have hst : s ≠ t := fun h => hab (congrArg v h)
    rcases (hedge s t hst).1 ⟨v s, v t, rfl, hab, hprod⟩ with rfl | rfl
    · exact ⟨s, Set.mem_univ _, rfl⟩
    · exact ⟨s - 1, Set.mem_univ _, by simp [Sym2.eq_swap]⟩

/-- On a cyclic enumeration `v` of a chordless cycle, the number of edges `{i, j}` with
`0 < aᵢⱼ` equals the number of `s : ZMod p` with `0 < a_{v(s) v(s+1)}`, for any `A` with a
symmetrizer. -/
theorem IsQCCyclicEnumeration.ncard_posEdges_eq {B A : Matrix (Fin n) (Fin n) ℤ}
    {Z : Finset (Fin n)} {p : ℕ} [NeZero p] {v : ZMod p → Fin n}
    (hv : IsQCCyclicEnumeration B Z v) {d : Fin n → ℤ} (hd : IsSymmetrizer A d) :
    {e | e ∈ qcEdgesOf B Z ∧ ∃ i j, e = s(i, j) ∧ 0 < A i j}.ncard =
      (Finset.univ.filter fun s => 0 < A (v s) (v (s + 1))).card := by
  have hbij := hv.bijOn_edges
  have hinj : Function.Injective (fun s => s(v s, v (s + 1))) := Set.injOn_univ.1 hbij.injOn
  have hset : {e | e ∈ qcEdgesOf B Z ∧ ∃ i j, e = s(i, j) ∧ 0 < A i j} =
      (fun s => s(v s, v (s + 1))) ''
        ↑(Finset.univ.filter fun s => 0 < A (v s) (v (s + 1))) := by
    ext e
    constructor
    · rintro ⟨he, i, j, rfl, hpos⟩
      obtain ⟨s, -, hs⟩ := hbij.surjOn he
      refine ⟨s, ?_, hs⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rcases Sym2.eq_iff.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rwa [h1, h2]
      · rw [h1, h2]
        exact (hd.sign_eq i j).1.1 hpos
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hbij.mapsTo (Set.mem_univ s), v s, v (s + 1), rfl, by simpa using hs⟩
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]

/-! ### Simultaneous sign changes -/

/-- A simultaneous sign change is an involution. -/
@[simp]
theorem qcSignChange_qcSignChange (ε : Fin n → ℤˣ) (A : Matrix (Fin n) (Fin n) ℤ) :
    qcSignChange ε (qcSignChange ε A) = A := by
  ext i j
  simp only [qcSignChange, of_apply]
  linear_combination ((ε j : ℤ) * ε j * A i j) * Int.units_coe_mul_self (ε i) +
    A i j * Int.units_coe_mul_self (ε j)

/-- A symmetrizer of `A` is a symmetrizer of `ε · A`. -/
theorem IsSymmetrizer.qcSignChange {A : Matrix (Fin n) (Fin n) ℤ} {d : Fin n → ℤ}
    (hd : IsSymmetrizer A d) (ε : Fin n → ℤˣ) : IsSymmetrizer (qcSignChange ε A) d := by
  refine ⟨hd.1, fun i j => ?_⟩
  simp only [ClusterAlgebras.qcSignChange, of_apply]
  linear_combination ((ε i : ℤ) * ε j) * hd.2 i j

/-- A simultaneous sign change of a positive quasi-Cartan matrix is positive. -/
theorem IsPositiveQuasiCartan.qcSignChange {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : IsPositiveQuasiCartan A) (ε : Fin n → ℤˣ) :
    IsPositiveQuasiCartan (qcSignChange ε A) := by
  obtain ⟨⟨hdiag, d₀, hd₀⟩, d, hd, hpos⟩ := hA
  refine ⟨⟨fun i => ?_, d₀, hd₀.qcSignChange ε⟩, d, hd.qcSignChange ε, fun w hw => ?_⟩
  · simp [ClusterAlgebras.qcSignChange, hdiag i, Int.units_coe_mul_self]
  have hw' : (fun i => ((ε i : ℤ) : ℝ) * w i) ≠ 0 := fun h => hw <| funext fun i => by
    simpa only [Pi.zero_apply, mul_eq_zero, Int.cast_eq_zero, Units.ne_zero, false_or] using
      congrFun h i
  convert hpos _ hw' using 1
  simp only [dotProduct, mulVec, diagonal_mul, Matrix.map_apply, ClusterAlgebras.qcSignChange,
    of_apply, Int.cast_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `(-1)` to the number of positive values of `x` is the product of `-1` over the positive
values and `1` over the others. -/
private theorem neg_one_pow_card_filter {ι : Type*} [Fintype ι] (x : ι → ℤ) :
    (-1 : ℤ) ^ (Finset.univ.filter fun s => 0 < x s).card =
      ∏ s, if 0 < x s then -1 else 1 := by
  rw [Finset.prod_ite]
  simp

/-- Multiplying a nonzero integer by a sign `ab` multiplies `-1` or `1`, according as it is
positive or not, by `ab`. -/
private theorem posSign_units_mul (a b : ℤˣ) {x : ℤ} (hx : x ≠ 0) :
    (if 0 < (a : ℤ) * b * x then (-1 : ℤ) else 1) = a * b * (if 0 < x then -1 else 1) := by
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
    rcases hx.lt_or_gt with h | h <;> simp [h, h.not_gt]

/-- **Sign changes preserve companions and their symmetrizers, and are involutions.** -/
@[cluster_algebras "lem_qc_sign_change"]
theorem IsQuasiCartanCompanion.isQuasiCartanCompanion_qcSignChange {B A : Matrix (Fin n) (Fin n) ℤ}
    (hA : IsQuasiCartanCompanion B A) (ε : Fin n → ℤˣ) :
    IsQuasiCartanCompanion B (qcSignChange ε A) ∧
      (∀ d, IsSymmetrizer (qcSignChange ε A) d ↔ IsSymmetrizer A d) ∧
      qcSignChange ε (qcSignChange ε A) = A := by
  refine ⟨⟨⟨fun i => ?_, ?_⟩, fun i j hij => ?_⟩, fun d => ⟨fun h => ?_, fun h => ?_⟩,
    qcSignChange_qcSignChange ε A⟩
  · simp [qcSignChange, hA.1.1 i, Int.units_coe_mul_self]
  · obtain ⟨d, hd⟩ := hA.1.2
    exact ⟨d, hd.qcSignChange ε⟩
  · have habs : ∀ u : ℤˣ, |(u : ℤ)| = 1 := fun u => by
      rcases Int.units_eq_one_or u with rfl | rfl <;> simp
    simp [qcSignChange, abs_mul, hA.2 i j hij, habs]
  · simpa using h.qcSignChange ε
  · exact h.qcSignChange ε

/-- **Sign changes preserve positivity.** -/
@[cluster_algebras "lem_qc_sign_change", simp]
theorem isPositiveQuasiCartan_qcSignChange_iff {A : Matrix (Fin n) (Fin n) ℤ} (ε : Fin n → ℤˣ) :
    IsPositiveQuasiCartan (qcSignChange ε A) ↔ IsPositiveQuasiCartan A :=
  ⟨fun h => by simpa using h.qcSignChange ε, fun h => h.qcSignChange ε⟩

/-- **Sign changes preserve the sign condition** on every chordless cycle. -/
@[cluster_algebras "lem_qc_sign_change"]
theorem IsQuasiCartanCompanion.satisfiesQCSignCondition_qcSignChange_iff
    {B A : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B) (hA : IsQuasiCartanCompanion B A)
    (ε : Fin n → ℤˣ) {Z : Finset (Fin n)} (hZ : IsQCChordlessCycle B Z) :
    SatisfiesQCSignCondition B (qcSignChange ε A) Z ↔ SatisfiesQCSignCondition B A Z := by
  obtain ⟨p, v, hv⟩ := hZ
  have hp := hv.1
  have : NeZero p := ⟨by omega⟩
  obtain ⟨d, hd⟩ := hA.1.2
  unfold SatisfiesQCSignCondition
  rw [hv.ncard_posEdges_eq (hd.qcSignChange ε), hv.ncard_posEdges_eq hd]
  have hne : ∀ s, A (v s) (v (s + 1)) ≠ 0 := fun s => by
    have hvne : v s ≠ v (s + 1) := fun h => hv.add_one_ne_self s (hv.2.1 h).symm
    obtain ⟨-, -, hedge⟩ := hB.isQCEdge_iff (v s) (v (s + 1))
    obtain ⟨hedge, -, hcomp⟩ := hedge hvne
    exact (hcomp A hA).2 (hedge.1 (hv.bijOn_edges.mapsTo (Set.mem_univ s)).1)
  have key : (-1 : ℤ) ^ (Finset.univ.filter fun s => 0 < qcSignChange ε A (v s) (v (s + 1))).card
      = (-1) ^ (Finset.univ.filter fun s => 0 < A (v s) (v (s + 1))).card := by
    rw [neg_one_pow_card_filter, neg_one_pow_card_filter,
      show (∏ s, if 0 < qcSignChange ε A (v s) (v (s + 1)) then (-1 : ℤ) else 1) =
        ∏ s, ((ε (v s) : ℤ) * ε (v (s + 1)) * if 0 < A (v s) (v (s + 1)) then -1 else 1) from
        Finset.prod_congr rfl fun s _ => posSign_units_mul _ _ (hne s),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hshift : ∏ s, (ε (v (s + 1)) : ℤ) = ∏ s, (ε (v s) : ℤ) :=
      Equiv.prod_comp (Equiv.addRight (1 : ZMod p)) (fun s => (ε (v s) : ℤ))
    rw [hshift, ← Finset.prod_mul_distrib]
    simp only [Int.units_coe_mul_self, Finset.prod_const_one, one_mul]
  constructor <;> intro h' <;> by_contra h <;> rw [Nat.not_odd_iff_even] at h <;>
    rw [h'.neg_one_pow, h.neg_one_pow] at key <;> norm_num at key

end ClusterAlgebras

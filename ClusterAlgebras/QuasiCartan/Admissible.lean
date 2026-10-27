/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.QuasiCartan.Criterion

/-!
# Admissible companions are unique up to sign changes

A sign function on the edges of a skew-symmetrizable matrix `B` that is trivial on every
chordless cycle is a coboundary. Hence two admissible companions of `B` differ by a simultaneous
sign change, and once an admissible companion is at hand, the conditions of the
Barot–Geiss–Zelevinsky criterion reduce to its positivity.

## Main results

* `ClusterAlgebras.exists_signVector_of_prod_eq_one`: a sign function on the edges whose product
  over every chordless cycle is `1` has the form `δ({i, j}) = εᵢ εⱼ` for a sign vector `ε`.
* `ClusterAlgebras.IsAdmissibleCompanion.isAdmissibleCompanion_iff`: given an admissible
  companion `A`, a companion `A'` is admissible exactly when `A' = ε · A` for a sign vector `ε`.
* `ClusterAlgebras.IsAdmissibleCompanion.satisfiesBGZ_iff_isPositiveQuasiCartan`: if every
  chordless cycle is cyclically oriented, `B` satisfies the criterion exactly when an admissible
  companion is positive.

## References

* M. Barot, C. Geiss, A. Zelevinsky, *Cluster algebras of finite type and positive
  symmetrizable matrices*, J. London Math. Soc. 73 (2006), Propositions 1.4–1.5.
* S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.11.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

/-! ### Closed walks and their values -/

section Walks

variable {V : Type*} {G : SimpleGraph V} {δ : Sym2 V → ℤˣ}

/-- A product over `ℤ/(N + 1)` of a function of `s` and `s + 1`, as a product over `[0, N]`. -/
private lemma prod_zmod_succ_eq {M : Type*} [CommMonoid M] (N : ℕ) (f : ℕ → ℕ → M) :
    ∏ i : ZMod (N + 1), f i.val (i + 1).val =
      (∏ j ∈ Finset.range N, f j (j + 1)) * f N 0 := by
  change ∏ i : Fin (N + 1), f i.val (i + 1).val = _
  rw [Fin.prod_univ_castSucc, ← Fin.prod_univ_eq_prod_range]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fin.val_add_one, if_neg (Fin.castSucc_lt_last j).ne]
    simp
  · simp

/-- In `Fin (N + 1)`, `t = s + 1` in terms of the representatives in `[0, N]`. -/
private lemma fin_eq_add_one_iff {N : ℕ} (s t : Fin (N + 1)) :
    t = s + 1 ↔ t.val = s.val + 1 ∨ (s.val = N ∧ t.val = 0) := by
  rw [Fin.ext_iff, Fin.val_add_one]
  split_ifs with h
  · rw [h, Fin.val_last]
    have := t.isLt
    omega
  · have : s.val ≠ N := fun h' => h (Fin.ext (by simpa using h'))
    omega

/-- In `ℤ/(N + 1)`, `t = s + 1` in terms of the representatives in `[0, N]`. -/
private lemma zmod_eq_add_one_iff {N : ℕ} (s t : ZMod (N + 1)) :
    t = s + 1 ↔ t.val = s.val + 1 ∨ (s.val = N ∧ t.val = 0) :=
  fin_eq_add_one_iff s t

/-- Splitting a product over `[0, m)` at `a ≤ b ≤ m`. -/
private lemma prod_range_split {M : Type*} [CommMonoid M] (F : ℕ → M) {a b m : ℕ} (hab : a ≤ b)
    (hbm : b ≤ m) : ∏ j ∈ Finset.range m, F j = (∏ j ∈ Finset.range a, F j) *
      ((∏ j ∈ Finset.range (b - a), F (a + j)) * ∏ j ∈ Finset.range (m - b), F (b + j)) := by
  conv_lhs => rw [show m = a + ((b - a) + (m - b)) by omega]
  rw [Finset.prod_range_add, Finset.prod_range_add]
  refine congrArg₂ _ rfl (congrArg₂ _ rfl (Finset.prod_congr rfl fun j _ => ?_))
  rw [show a + (b - a + j) = b + j by omega]

/-- A closed walk `g` of length `m` through a vertex twice, at `a < b < m`, splits into two
shorter closed walks; so it has value `1` when shorter closed walks do. -/
private lemma prod_closed_of_eq {g : ℕ → V} {m a b : ℕ}
    (ih : ∀ k < m, ∀ g : ℕ → V, (∀ j < k, G.Adj (g j) (g (j + 1))) → g k = g 0 →
      ∏ j ∈ Finset.range k, δ s(g j, g (j + 1)) = 1)
    (hadj : ∀ j < m, G.Adj (g j) (g (j + 1))) (hclosed : g m = g 0) (hab : a < b) (hbm : b < m)
    (heq : g a = g b) : ∏ j ∈ Finset.range m, δ s(g j, g (j + 1)) = 1 := by
  set F : ℕ → ℤˣ := fun j => δ s(g j, g (j + 1)) with hF
  have h1 := ih (b - a) (by omega) (fun j => g (a + j))
    (fun j hj => hadj (a + j) (by omega))
    (by
      simp only [add_zero]
      rw [show a + (b - a) = b by omega, heq])
  have h2 := ih (a + (m - b)) (by omega) (fun j => if j ≤ a then g j else g (j - a + b))
    (fun j hj => by
      rcases lt_trichotomy j a with h | rfl | h
      · rw [if_pos h.le, if_pos (by omega : j + 1 ≤ a)]
        exact hadj j (by omega)
      · rw [if_pos le_rfl, if_neg (by omega), show j + 1 - j + b = b + 1 by omega, heq]
        exact hadj b hbm
      · rw [if_neg (by omega), if_neg (by omega), show j + 1 - a + b = j - a + b + 1 by omega]
        exact hadj _ (by omega))
    (by
      rw [if_neg (by omega), if_pos (Nat.zero_le _), show a + (m - b) - a + b = m by omega,
        hclosed])
  rw [Finset.prod_range_add] at h2
  rw [prod_range_split F hab.le hbm.le, show (∏ j ∈ Finset.range (b - a), F (a + j)) = 1 from h1,
    one_mul, ← h2]
  refine congrArg₂ _ (Finset.prod_congr rfl fun j hj => ?_)
    (Finset.prod_congr rfl fun j hj => ?_)
  · rw [Finset.mem_range] at hj
    simp only [hF, if_pos hj.le, if_pos (show j + 1 ≤ a by omega)]
  · rw [Finset.mem_range] at hj
    have e1 : (if a + j ≤ a then g (a + j) else g (a + j - a + b)) = g (b + j) := by
      split_ifs with h
      · rw [show j = 0 by omega, add_zero, add_zero, heq]
      · rw [show a + j - a + b = b + j by omega]
    have e2 : (if a + j + 1 ≤ a then g (a + j + 1) else g (a + j + 1 - a + b)) =
        g (b + j + 1) := by
      rw [if_neg (by omega), show a + j + 1 - a + b = b + j + 1 by omega]
    simp only [hF, e1, e2]

/-- The closed walk `g a, …, g b, g a` closing a chord `{g a, g b}` of a walk `g` has value `1`
when closed walks of its length do. -/
private lemma prod_chord_short {g : ℕ → V} {F : ℕ → ℤˣ} (hF : ∀ j, F j = δ s(g j, g (j + 1)))
    {m a b : ℕ} (hadj : ∀ j < m, G.Adj (g j) (g (j + 1))) (hab : a < b) (hbm : b < m)
    (hadjab : G.Adj (g a) (g b))
    (hP : ∀ g : ℕ → V, (∀ j < b - a + 1, G.Adj (g j) (g (j + 1))) → g (b - a + 1) = g 0 →
      ∏ j ∈ Finset.range (b - a + 1), δ s(g j, g (j + 1)) = 1) :
    (∏ j ∈ Finset.range (b - a), F (a + j)) * δ s(g a, g b) = 1 := by
  have h1 := hP (fun j => if j ≤ b - a then g (a + j) else g a)
    (fun j hj => by
      rcases (by omega : j < b - a ∨ j = b - a) with h | rfl
      · rw [if_pos h.le, if_pos (by omega : j + 1 ≤ b - a)]
        exact hadj (a + j) (by omega)
      · rw [if_pos le_rfl, if_neg (by omega), show a + (b - a) = b by omega]
        exact hadjab.symm)
    (by rw [if_neg (by omega), if_pos (Nat.zero_le _), add_zero])
  have e1 : ∏ j ∈ Finset.range (b - a),
      δ s((if j ≤ b - a then g (a + j) else g a),
        (if j + 1 ≤ b - a then g (a + (j + 1)) else g a)) =
      ∏ j ∈ Finset.range (b - a), F (a + j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [if_pos hj.le, if_pos (by omega), ← add_assoc, hF]
  rwa [Finset.prod_range_succ, e1, if_pos le_rfl, if_neg (by omega),
    show a + (b - a) = b by omega, Sym2.eq_swap] at h1

/-- The closed walk `g 0, …, g a, g b, …, g m` shortcutting a closed walk `g` along a chord
`{g a, g b}` has value `1` when closed walks of its length do. -/
private lemma prod_chord_long {g : ℕ → V} {F : ℕ → ℤˣ} (hF : ∀ j, F j = δ s(g j, g (j + 1)))
    {m a b : ℕ} (hadj : ∀ j < m, G.Adj (g j) (g (j + 1))) (hclosed : g m = g 0) (hab : a < b)
    (hbm : b < m) (hadjab : G.Adj (g a) (g b))
    (hP : ∀ g : ℕ → V, (∀ j < a + 1 + (m - b), G.Adj (g j) (g (j + 1))) →
      g (a + 1 + (m - b)) = g 0 → ∏ j ∈ Finset.range (a + 1 + (m - b)), δ s(g j, g (j + 1)) = 1) :
    (∏ j ∈ Finset.range a, F j) * δ s(g a, g b) * ∏ j ∈ Finset.range (m - b), F (b + j) = 1 := by
  have h2 := hP (fun j => if j ≤ a then g j else g (j - a - 1 + b))
    (fun j hj => by
      rcases lt_trichotomy j a with h | rfl | h
      · rw [if_pos h.le, if_pos (by omega : j + 1 ≤ a)]
        exact hadj j (by omega)
      · rw [if_pos le_rfl, if_neg (by omega), show j + 1 - j - 1 + b = b by omega]
        exact hadjab
      · rw [if_neg (by omega), if_neg (by omega),
          show j + 1 - a - 1 + b = j - a - 1 + b + 1 by omega]
        exact hadj _ (by omega))
    (by
      rw [if_neg (by omega), if_pos (Nat.zero_le _),
        show a + 1 + (m - b) - a - 1 + b = m by omega, hclosed])
  have e2 : ∏ j ∈ Finset.range a,
      δ s((if j ≤ a then g j else g (j - a - 1 + b)),
        (if j + 1 ≤ a then g (j + 1) else g (j + 1 - a - 1 + b))) =
      ∏ j ∈ Finset.range a, F j := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [if_pos hj.le, if_pos (by omega), hF]
  have e3 : ∏ j ∈ Finset.range (m - b),
      δ s((if a + 1 + j ≤ a then g (a + 1 + j) else g (a + 1 + j - a - 1 + b)),
        (if a + 1 + j + 1 ≤ a then g (a + 1 + j + 1) else g (a + 1 + j + 1 - a - 1 + b))) =
      ∏ j ∈ Finset.range (m - b), F (b + j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [if_neg (by omega), if_neg (by omega), show a + 1 + j - a - 1 + b = b + j by omega,
      show a + 1 + j + 1 - a - 1 + b = b + j + 1 by omega, hF]
  rwa [Finset.prod_range_add, Finset.prod_range_succ, e2, e3, if_pos le_rfl, if_neg (by omega),
    show a + 1 - a - 1 + b = b by omega] at h2

/-- A closed walk `g` of length `N + 1 ≥ 3` without repeated vertices or chords is a chordless
cycle, so it has value `1` when every chordless cycle does. -/
private lemma prod_closed_of_chordless
    (hcyc : ∀ (N : ℕ) (u : ZMod (N + 1) → V), 2 ≤ N → Function.Injective u →
      (∀ s t, s ≠ t → (G.Adj (u s) (u t) ↔ t = s + 1 ∨ t = s - 1)) →
      ∏ s, δ s(u s, u (s + 1)) = 1)
    {g : ℕ → V} {N : ℕ} (hN : 2 ≤ N) (hadj : ∀ j < N + 1, G.Adj (g j) (g (j + 1)))
    (hclosed : g (N + 1) = g 0) (hinj : ∀ a b, a < N + 1 → b < N + 1 → g a = g b → a = b)
    (hchord : ∀ a b, a < b → b < N + 1 → G.Adj (g a) (g b) → 2 ≤ b - a →
      a = 0 ∧ b = N + 1 - 1) :
    ∏ j ∈ Finset.range (N + 1), δ s(g j, g (j + 1)) = 1 := by
  have key := hcyc N (fun s => g s.val) hN
    (fun s t h => ZMod.val_injective _ (hinj _ _ (ZMod.val_lt s) (ZMod.val_lt t) h))
    (fun s t hst => by
      have hst' : s.val ≠ t.val := fun h => hst (ZMod.val_injective _ h)
      have hs := ZMod.val_lt s
      have ht := ZMod.val_lt t
      rw [eq_sub_iff_add_eq, eq_comm (a := t + 1), zmod_eq_add_one_iff, zmod_eq_add_one_iff]
      generalize s.val = a at *
      generalize t.val = b at *
      constructor
      · intro h
        rcases lt_or_gt_of_ne hst' with hlt | hlt
        · have := hchord a b hlt ht h
          omega
        · have := hchord b a hlt hs h.symm
          omega
      · rintro ((h | ⟨h1, h2⟩) | (h | ⟨h1, h2⟩))
        · rw [h]
          exact hadj a hs
        · rw [h1, h2, ← hclosed]
          exact hadj N (by omega)
        · rw [h]
          exact (hadj b ht).symm
        · rw [h1, h2, ← hclosed]
          exact (hadj N (by omega)).symm)
  rw [Finset.prod_range_succ, hclosed]
  rwa [prod_zmod_succ_eq N (fun i j => δ s(g i, g j))] at key

/-- **Every closed walk has value `1`** when every chordless cycle does: if
`(g 0, …, g m)` is a closed walk of `G`, then `∏ δ({g j, g (j + 1)}) = 1`, provided the same
holds for every cyclic enumeration `u : ℤ/(N + 1) → V`, `N ≥ 2`, of an induced cycle. -/
private lemma prod_range_eq_one_of_closed
    (hcyc : ∀ (N : ℕ) (u : ZMod (N + 1) → V), 2 ≤ N → Function.Injective u →
      (∀ s t, s ≠ t → (G.Adj (u s) (u t) ↔ t = s + 1 ∨ t = s - 1)) →
      ∏ s, δ s(u s, u (s + 1)) = 1) :
    ∀ (m : ℕ) (g : ℕ → V), (∀ j < m, G.Adj (g j) (g (j + 1))) → g m = g 0 →
      ∏ j ∈ Finset.range m, δ s(g j, g (j + 1)) = 1 := by
  intro m
  induction m using Nat.strong_induction_on with | _ m ih => ?_
  intro g hadj hclosed
  by_cases hrep : ∃ a b, a < b ∧ b < m ∧ g a = g b
  · obtain ⟨a, b, hab, hbm, heq⟩ := hrep
    exact prod_closed_of_eq ih hadj hclosed hab hbm heq
  push Not at hrep
  have hinj : ∀ a b, a < m → b < m → g a = g b → a = b := by
    intro a b ha hb h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hrep a b hlt hb h
    · exact hrep b a hlt ha h.symm
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m) with rfl | rfl | rfl | hm
  · simp
  · simpa [hclosed] using hadj 0 one_pos
  · rw [Finset.prod_range_succ, Finset.prod_range_one, zero_add,
      show g (1 + 1) = g 0 from hclosed, Sym2.eq_swap (a := g 1), Int.units_mul_self]
  by_cases hchord : ∃ a b, a < b ∧ b < m ∧ G.Adj (g a) (g b) ∧ 2 ≤ b - a ∧ ¬(a = 0 ∧ b = m - 1)
  · obtain ⟨a, b, hab, hbm, hadjab, hba, hnot⟩ := hchord
    set F : ℕ → ℤˣ := fun j => δ s(g j, g (j + 1))
    have h1 := prod_chord_short (F := F) (fun _ => rfl) hadj hab hbm hadjab (ih _ (by omega))
    have h2 := prod_chord_long (F := F) (fun _ => rfl) hadj hclosed hab hbm hadjab
      (ih _ (by omega))
    rw [prod_range_split F hab.le hbm.le]
    set X := ∏ j ∈ Finset.range a, F j
    set Y := ∏ j ∈ Finset.range (b - a), F (a + j)
    set W := ∏ j ∈ Finset.range (m - b), F (b + j)
    calc X * (Y * W) = X * (Y * W) * (δ s(g a, g b) * δ s(g a, g b)) := by
          rw [Int.units_mul_self, mul_one]
      _ = (Y * δ s(g a, g b)) * (X * δ s(g a, g b) * W) := by ac_rfl
      _ = 1 := by rw [h1, h2, one_mul]
  · push Not at hchord
    obtain ⟨N, rfl⟩ : ∃ N, m = N + 1 := ⟨m - 1, by omega⟩
    exact prod_closed_of_chordless hcyc (by omega) hadj hclosed hinj hchord

/-- The value of a walk, the product of `δ` over its edges, read off its vertices. -/
private lemma prod_map_edges_eq {x y : V} (p : G.Walk x y) :
    (p.edges.map δ).prod =
      ∏ j ∈ Finset.range p.length, δ s(p.getVert j, p.getVert (j + 1)) := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rw [SimpleGraph.Walk.edges_cons, List.map_cons, List.prod_cons, ih,
      SimpleGraph.Walk.length_cons, Finset.prod_range_succ', mul_comm]
    simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero]

end Walks

/-- **A sign function trivial on chordless cycles is a coboundary.** If `δ` assigns a sign to
every edge of `B` and the product of `δ` over the edges of every chordless cycle is `1`, then
`δ({i, j}) = εᵢ εⱼ` on every edge `{i, j}` for some sign vector `ε`. -/
@[cluster_algebras "lem_qc_cycle_potential"]
theorem exists_signVector_of_prod_eq_one {B : Matrix (Fin n) (Fin n) ℤ}
    (δ : Sym2 (Fin n) → ℤˣ)
    (hδ : ∀ Z, IsQCChordlessCycle B Z → ∏ᶠ e ∈ qcEdgesOf B Z, δ e = 1) :
    ∃ ε : Fin n → ℤˣ, ∀ i j, IsQCEdge B s(i, j) → δ s(i, j) = ε i * ε j := by
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => IsQCEdge B s(i, j)
      symm := ⟨fun i j h => by rwa [Sym2.eq_swap]⟩
      loopless := ⟨fun i ⟨a, b, h, hab, _⟩ => by
        obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := Sym2.eq_iff.1 h <;> exact hab rfl⟩ }
  have hcyc : ∀ (N : ℕ) (u : ZMod (N + 1) → Fin n), 2 ≤ N → Function.Injective u →
      (∀ s t, s ≠ t → (G.Adj (u s) (u t) ↔ t = s + 1 ∨ t = s - 1)) →
      ∏ s, δ s(u s, u (s + 1)) = 1 := by
    intro N u hN hu hedge
    have hv : IsQCCyclicEnumeration B (Finset.univ.image u) u :=
      ⟨by omega, hu, by simp, hedge⟩
    have h := hδ _ ⟨N + 1, u, hv⟩
    rwa [← finprod_mem_eq_of_bijOn (f := fun s => δ s(u s, u (s + 1))) _ hv.bijOn_edges
      (fun _ _ => rfl), finprod_mem_univ, finprod_eq_prod_of_fintype] at h
  have hclosed : ∀ {x : Fin n} (p : G.Walk x x), (p.edges.map δ).prod = 1 := fun p => by
    rw [prod_map_edges_eq]
    exact prod_range_eq_one_of_closed hcyc p.length p.getVert
      (fun j hj => p.adj_getVert_succ hj) (by simp)
  let r : Fin n → Fin n := fun i => Quot.out (G.connectedComponentMk i)
  have hr : ∀ i, G.Reachable (r i) i := fun i => SimpleGraph.ConnectedComponent.exact
    (Quot.out_eq (G.connectedComponentMk i))
  let W : ∀ i, G.Walk (r i) i := fun i => (hr i).some
  refine ⟨fun i => ((W i).edges.map δ).prod, fun i j hij => ?_⟩
  have hij' : G.Adj i j := hij
  have hrij : r i = r j :=
    congrArg Quot.out (SimpleGraph.ConnectedComponent.eq.2 hij'.reachable)
  have h := hclosed ((W i).append ((SimpleGraph.Walk.cons hij' (W j).reverse).copy rfl hrij.symm))
  simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy,
    SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_reverse, List.map_append, List.map_cons,
    List.map_reverse, List.prod_append, List.prod_cons, List.prod_reverse] at h
  set a := ((W i).edges.map δ).prod
  set b := ((W j).edges.map δ).prod
  have h' := congrArg (· * (a * b)) h
  simp only [one_mul] at h'
  rw [← h']
  calc δ s(i, j) = δ s(i, j) * (a * a) * (b * b) := by
        rw [Int.units_mul_self, Int.units_mul_self, mul_one, mul_one]
    _ = a * (δ s(i, j) * b) * (a * b) := by ac_rfl

/-- Two companions `A`, `A'` of a skew-symmetrizable `B` with `εᵢ εⱼ = 1` exactly on the edges
`{i, j}` where `aᵢⱼ` and `a'ᵢⱼ` have the same sign satisfy `A' = ε · A`. -/
private lemma eq_qcSignChange_of_units_mul_eq {B A A' : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hA : IsQuasiCartanCompanion B A)
    (hA' : IsQuasiCartanCompanion B A') {ε : Fin n → ℤˣ}
    (hε : ∀ i j, IsQCEdge B s(i, j) →
      (ε i : ℤ) * ε j = if (0 < A i j ↔ 0 < A' i j) then 1 else -1) :
    A' = qcSignChange ε A := by
  refine Matrix.ext fun i j => ?_
  simp only [qcSignChange, of_apply]
  by_cases hij : i = j
  · subst hij
    rw [hA'.1.1 i, hA.1.1 i, Int.units_coe_mul_self, one_mul]
  obtain ⟨-, -, hedge⟩ := hB.isQCEdge_iff i j
  obtain ⟨hedge, -, hcomp⟩ := hedge hij
  have habs : |A' i j| = |A i j| := by rw [hA'.2 i j hij, hA.2 i j hij]
  by_cases hB0 : B i j = 0
  · have h1 : A i j = 0 := by rw [← abs_eq_zero, hA.2 i j hij, hB0, abs_zero]
    have h2 : A' i j = 0 := by rw [← abs_eq_zero, habs, h1, abs_zero]
    rw [h1, h2, mul_zero]
  have hx : A i j ≠ 0 := (hcomp A hA).2 hB0
  rw [hε i j (hedge.2 hB0)]
  rcases abs_eq_abs.1 habs with h | h <;> split_ifs with hc <;> rw [h] at hc ⊢
  · rw [one_mul]
  · exact absurd Iff.rfl hc
  · rcases hx.lt_or_gt with hlt | hlt
    · exact absurd (hc.2 (by omega)) (by omega)
    · exact absurd (hc.1 hlt) (by omega)
  · rw [neg_one_mul]

/-- **Admissible companions are unique up to sign changes**: if `A` is an admissible
companion of `B`, a companion `A'` of `B` is admissible exactly when `A' = ε · A` for a sign
vector `ε`. -/
@[cluster_algebras "prop_qc_admissible_companion_unique"]
theorem IsAdmissibleCompanion.isAdmissibleCompanion_iff {B A A' : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hA : IsAdmissibleCompanion B A)
    (hA' : IsQuasiCartanCompanion B A') :
    IsAdmissibleCompanion B A' ↔ ∃ ε : Fin n → ℤˣ, A' = qcSignChange ε A := by
  refine ⟨fun hA'adm => ?_, ?_⟩
  swap
  · rintro ⟨ε, rfl⟩
    exact ⟨(hA.1.isQuasiCartanCompanion_qcSignChange ε).1,
      fun Z hZ => (hA.1.satisfiesQCSignCondition_qcSignChange_iff hB ε hZ).2 (hA.2 Z hZ)⟩
  obtain ⟨d, hd⟩ := hA.1.1.2
  obtain ⟨d', hd'⟩ := hA'.1.2
  let δ : Sym2 (Fin n) → ℤˣ := Sym2.lift
    ⟨fun i j => if (0 < A i j ↔ 0 < A' i j) then 1 else -1, fun i j => by
      simp only [(hd.sign_eq i j).1, (hd'.sign_eq i j).1]⟩
  have hδ : ∀ i j, δ s(i, j) = if (0 < A i j ↔ 0 < A' i j) then 1 else -1 := fun i j => rfl
  have hσ : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
      (if (P ↔ Q) then (1 : ℤˣ) else -1) = (if P then -1 else 1) * (if Q then -1 else 1) := by
    intro P Q _ _
    by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
  have hodd : ∀ {A₀ : Matrix (Fin n) (Fin n) ℤ} {d₀ : Fin n → ℤ}, IsSymmetrizer A₀ d₀ →
      ∀ {Z : Finset (Fin n)} {p : ℕ} [NeZero p] {v : ZMod p → Fin n},
      IsQCCyclicEnumeration B Z v → SatisfiesQCSignCondition B A₀ Z →
      ∏ s, (if 0 < A₀ (v s) (v (s + 1)) then (-1 : ℤˣ) else 1) = -1 := by
    intro A₀ d₀ hd₀ Z p _ v hv hsc
    unfold SatisfiesQCSignCondition at hsc
    rw [hv.ncard_posEdges_eq hd₀] at hsc
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, hsc.neg_one_pow]
  have hprod : ∀ Z, IsQCChordlessCycle B Z → ∏ᶠ e ∈ qcEdgesOf B Z, δ e = 1 := by
    rintro Z ⟨p, v, hv⟩
    have : NeZero p := ⟨by have := hv.1; omega⟩
    rw [← finprod_mem_eq_of_bijOn (f := fun s => δ s(v s, v (s + 1))) _ hv.bijOn_edges
      (fun _ _ => rfl), finprod_mem_univ, finprod_eq_prod_of_fintype]
    simp only [hδ, hσ, Finset.prod_mul_distrib]
    rw [hodd hd hv (hA.2 Z ⟨p, v, hv⟩), hodd hd' hv (hA'adm.2 Z ⟨p, v, hv⟩)]
    rfl
  obtain ⟨ε, hε⟩ := exists_signVector_of_prod_eq_one δ hprod
  refine ⟨ε, eq_qcSignChange_of_units_mul_eq hB hA.1 hA' fun i j hij => ?_⟩
  rw [← Units.val_mul, ← hε i j hij, hδ]
  split_ifs <;> rfl

/-- **The criterion reduces to the positivity of one admissible companion**: if every
chordless cycle of `B` is cyclically oriented and `A` is an admissible companion of `B`, then
`B` satisfies the equivalent conditions of the Barot–Geiss–Zelevinsky criterion, here condition
(4) and condition (3), exactly when `A` is positive. -/
@[cluster_algebras "prop_qc_admissible_companion_unique"]
theorem IsAdmissibleCompanion.satisfiesBGZ_iff_isPositiveQuasiCartan
    {B A : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B) (hA : IsAdmissibleCompanion B A)
    (hcyc : ∀ Z, IsQCChordlessCycle B Z → IsQCCyclicallyOriented B Z) :
    (SatisfiesBGZ B ↔ IsPositiveQuasiCartan A) ∧ (IsTwoFinite B ↔ IsPositiveQuasiCartan A) := by
  have h : SatisfiesBGZ B ↔ IsPositiveQuasiCartan A := by
    refine ⟨fun ⟨_, A', hA', hpos⟩ => ?_, fun hpos => ⟨hcyc, A, hA.1, hpos⟩⟩
    obtain ⟨ε, rfl⟩ := (hA.isAdmissibleCompanion_iff hB hA').1
      ⟨hA', fun Z hZ => hpos.satisfiesQCSignCondition hB hA' hZ⟩
    exact (isPositiveQuasiCartan_qcSignChange_iff ε).1 hpos
  exact ⟨h, (hB.tfae_satisfiesBGZ.out 2 3).trans h⟩

end ClusterAlgebras

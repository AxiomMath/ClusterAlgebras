/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.ReturningPaths
public import ClusterAlgebras.Plabic.ReturningArcHug
public import ClusterAlgebras.Plabic.HugMonogon

/-!
# Thurston's straightening

D. Thurston's straightening lemma [FWZ] states that every monogon-stable triple diagram `X` has
the *straightening property*: no triple diagram move-equivalent to `X` has a parallel digon, and
for every minimal interval `I` of `X`, of `i` say, some triple diagram move-equivalent to `X` has
its arc from `s_i` boundary-parallel along `I`.

The proof is by strong induction on the number of triple points. Assuming that every
monogon-stable triple diagram with fewer triple points has the straightening property,

* (part (i)) no diagram move-equivalent to `X` has a parallel digon: otherwise some simple arc `S`
  of a diagram `X' ∼ X` has a parallel returning path; choosing `S` with the fewest triple points,
  a returning path of least run is made to hug `S` by moves of the cut along `S`; it is
  anti-parallel, and pushing `S` off the resulting closed aligned rail gives a shorter simple arc
  that still has a parallel returning path;
* (Step 1) the arc `S` from `s_i` can be made to have no returning path on a given side `ζ`, by
  repeatedly making a minimal returning path hug `S` and pushing `S` off the resulting rail;
* (Step 2) once `S` has no returning path on the side `ζ` of a minimal interval `I`, the legs
  `g₀, …, g_{2k-1}` at the interior positions of `I` are combed onto `S` one at a time: for the
  first leg `g_t` whose reverse is not a dart of the `ζ` list, the arc through `g_t` of the cut
  `X|_{S,ζ}` (for `t = 0`), or of its cut along the single-dart arc through `g_{t-1}` (for
  `t ≥ 1`), is straightened by the induction hypothesis, the moves are lifted to `X`, and the
  aligned or staggered combing along the resulting rail makes `ḡ_t` a dart of the `ζ` list.

## Main results

* `ClusterAlgebras.TripleDiagram.IsMonogonStable.not_hasParallelDigon`: Straightening, part (i):
  no parallel digons.
* `ClusterAlgebras.TripleDiagram.IsMonogonStable.exists_moveEquivalent_forall_not_isReturningPath`:
  Straightening, Step 1: removing returning paths.
* `ClusterAlgebras.TripleDiagram.IsMonogonStable.exists_moveEquivalent_isBoundaryParallel`:
  Straightening, Step 2: combing.
* `ClusterAlgebras.TripleDiagram.IsMonogonStable.hasStraighteningProperty`: every monogon-stable
  triple diagram has the straightening property.

## Implementation notes

* Labels are `0`-indexed: the arc label `i : Fin b` is FWZ's `i + 1`, a returning path from
  `z_{a+1}` to `z_{c+1}` is `X.IsReturningPath (X.arc i) ζ Q a c`, and the entries of cut lists and
  side lists are numbered from `0`.
* The induction hypothesis "every monogon-stable triple diagram with fewer triple points than `X`
  has the straightening property" quantifies over triple diagrams with any number of arcs, as the
  cuts it is applied to have fewer arcs than `X`.
* Step 1 is stated for any side `ζ`: the interval `I` of FWZ only serves to name its side.
* In Step 2 the swivel moves straightening a (nested) cut are lifted one at a time, so that the cut
  of the lifted diagram is the diagram reached by these moves itself, and not only isomorphic to
  it; the arcs, intervals and legs of the cut are then read off the cut list.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset RailLabel

namespace TripleData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}

section Helpers

variable {X : TripleData H b}

private theorem rot_pow_rot_pow' (hX : X.IsPreTripleDiagram) {d : H}
    (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) (m n : ℕ) :
    (X.rot ^ m) ((X.rot ^ n) d) = (X.rot ^ ((m + n) % 6)) d := by
  rw [← Equiv.Perm.mul_apply, ← pow_add, hX.rot_pow_mod_six hd]

/-- A returning path from a point `z_{a+1}` to itself is a monogon. -/
private theorem hasMonogon_of_isReturningPath_self (hX : X.IsPreTripleDiagram) {P Q : List H}
    {ζ : StrandSide} {a : ℕ} (hQ : X.IsReturningPath P ζ Q a a) : X.HasMonogon := by
  obtain ⟨e, he, f, hf, hfe⟩ := hQ.head?_mem
  obtain ⟨e', he', g, hg, hge⟩ := hQ.getLast?_mem
  obtain rfl : e' = e := Option.mem_unique he' he
  have hPs := hQ.isSimpleStrandPath.isStrandPath
  have ha := hQ.lt_left
  rw [List.getElem?_eq_getElem (by omega), Option.mem_def, Option.some_inj] at he
  subst he
  have hz : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[a])) :=
    ((X.isStrandPath_iff_getElem.1 hPs).2.2 a ha).1
  have hPa := (X.isStrandPath_iff_getElem.1 hPs).2.1 a (by omega)
  have hc₀out : X.isOut (X.inv P[a]) = false := by
    rw [hX.isOut_inv_apply hPa.1, hPa.2]; rfl
  set c₀ := X.inv P[a] with hc₀
  have hfQ : f ∈ Q := List.mem_of_mem_head? hf
  have hgQ : g ∈ Q := List.mem_of_mem_getLast? hg
  have hfout : X.isOut f = true := hQ.isStrandPath.isOut_eq_true f hfQ
  have hgout : X.isOut (X.inv g) = false := by
    rw [hX.isOut_inv_apply (hQ.isStrandPath.notMem_bdry g hgQ),
      hQ.isStrandPath.isOut_eq_true g hgQ]; rfl
  have hout : ∀ n, X.isOut ((X.rot ^ n) c₀) = decide ¬Even n := by
    intro n
    rw [hX.isOut_rot_pow_apply hz, hc₀out]
    by_cases h : Even n <;> simp [h]
  have hv : X.vertexOf c₀ ∈ X.internalVertices := X.vertexOf_mem_internalVertices.2 hz
  have hmem : ∀ n, (X.rot ^ n) c₀ ∈ X.vertexOf c₀ := fun n => by
    rw [← X.vertexOf_rot_pow_apply n c₀]; exact X.self_mem_vertexOf _
  have hne := (hX.rot_pow_six hz).2
  have hrr := rot_pow_rot_pow' hX hz
  have hU : Q.head? = some f := hf
  have hrot1 : X.rot c₀ = (X.rot ^ 1) c₀ := by rw [pow_one]
  cases ζ
  · simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hfe hge
    have hf1 : f = (X.rot ^ 1) c₀ := by
      rcases hfe with h | h
      · rw [h, hrot1]
      · rw [h, hout 2] at hfout
        exact absurd hfout (by decide)
    have hg2 : X.inv g = (X.rot ^ 2) c₀ := by
      rcases hge with h | h
      · rw [h, hrot1, hout 1] at hgout
        exact absurd hgout (by decide)
      · exact h
    refine ⟨Q, (X.isMonogon_of_two_passes hX hv (hmem 4) (hmem 2) ?_ hQ.isStrandPath ?_ ?_).1⟩
    · intro h
      have h4 : (X.rot ^ 4) c₀ ∈ ({(X.rot ^ 2) c₀, (X.rot ^ 3) ((X.rot ^ 2) c₀)} : Finset H) := by
        rw [← h]; exact mem_insert_self _ _
      rw [hrr] at h4
      simp only [mem_insert, mem_singleton] at h4
      rcases h4 with h' | h'
      · exact absurd (hne 4 2 (by norm_num) (by norm_num) h') (by norm_num)
      · exact absurd (hne 4 5 (by norm_num) (by norm_num) h') (by norm_num)
    · rw [hU, hrr, hf1]
    · intro u hu
      rw [Option.mem_unique hu hg, hg2]
  · simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hfe hge
    have hf5 : f = (X.rot ^ 5) c₀ := by
      rcases hfe with h | h
      · rw [h, hout 4] at hfout
        exact absurd hfout (by decide)
      · exact h
    have hg4 : X.inv g = (X.rot ^ 4) c₀ := by
      rcases hge with h | h
      · exact h
      · rw [h, hout 5] at hgout
        exact absurd hgout (by decide)
    refine ⟨Q, (X.isMonogon_of_two_passes hX hv (hmem 2) (hmem 4) ?_ hQ.isStrandPath ?_ ?_).1⟩
    · intro h
      have h2 : (X.rot ^ 2) c₀ ∈ ({(X.rot ^ 4) c₀, (X.rot ^ 3) ((X.rot ^ 4) c₀)} : Finset H) := by
        rw [← h]; exact mem_insert_self _ _
      rw [hrr] at h2
      simp only [mem_insert, mem_singleton] at h2
      rcases h2 with h' | h'
      · exact absurd (hne 2 4 (by norm_num) (by norm_num) h') (by norm_num)
      · exact absurd (hne 2 1 (by norm_num) (by norm_num) h') (by norm_num)
    · rw [hU, hrr, hf5]
    · intro u hu
      rw [Option.mem_unique hu hg, hg4]

/-- A returning path of the arc from `s_i` on side `ζ` forces `N_ζ ≥ 2`. -/
private theorem two_le_length_arcCutList_of_isReturningPath {i : Fin b} {ζ : StrandSide}
    {Q : List H} {a c : ℕ} (hQ : X.IsReturningPath (X.arc i) ζ Q a c) :
    2 ≤ (X.arcCutList i ζ).length := by
  obtain ⟨e, he, f, -, hfe⟩ := hQ.head?_mem
  have ha := hQ.lt_left
  rw [List.getElem?_eq_getElem (by omega), getElem_arc, Option.mem_def, Option.some_inj] at he
  subst he
  rw [length_arc] at ha
  have hmem := mem_arcCutList_of_mem_sideList (mem_sideList_arc.2 ⟨a, ha, hfe⟩)
  have hpos := List.length_pos_of_mem hmem
  obtain ⟨t, ht⟩ := even_length_arcCutList (X := X) (i := i) ζ
  omega

/-- The arc from `s_i` is simple as soon as its interior points are pairwise distinct. -/
private theorem isSimpleArc_of_nodup {i : Fin b}
    (h : (X.interiorPoints (X.arc i)).Nodup) : X.IsSimpleArc i := by
  intro k l hk hl hv
  rw [← X.length_arc] at hk hl
  have hk' : k < (X.interiorPoints (X.arc i)).length := by
    simp only [interiorPoints, List.length_map, List.length_dropLast]; omega
  have hl' : l < (X.interiorPoints (X.arc i)).length := by
    simp only [interiorPoints, List.length_map, List.length_dropLast]; omega
  refine (h.getElem_inj_iff (hi := hk') (hj := hl')).1 ?_
  simp only [interiorPoints, List.getElem_map, List.getElem_dropLast, getElem_arc]
  exact hv

/-- The arc from `s_i` is simple as soon as it is a simple strand path. -/
private theorem isSimpleArc_of_isSimpleStrandPath' {i : Fin b}
    (h : X.IsSimpleStrandPath (X.arc i)) : X.IsSimpleArc i :=
  isSimpleArc_of_nodup h.nodup

/-- A dart of the `ζ` list of the arc from `s_i` lies at a triple point through which the arc
passes. -/
private theorem passesThrough_of_mem_sideList_arc (hX : X.IsTripleDiagram) {i : Fin b}
    {ζ : StrandSide} {d : H} (hd : d ∈ X.sideList ζ (X.arc i)) :
    X.PassesThrough (X.arc i).toFinset (X.vertexOf d) := by
  obtain ⟨k, hk, h⟩ := mem_sideList_arc.1 hd
  have hv : X.vertexOf d = X.vertexOf (X.inv (X.arcDart i k)) := by
    cases ζ <;> simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at h <;>
      rcases h with rfl | rfl <;> simp [X.vertexOf_rot_pow_apply, X.vertexOf_rot]
  obtain ⟨m, hm⟩ : ∃ m, X.arcLength i = m + 1 := ⟨X.arcLength i - 1, by omega⟩
  refine ⟨?_, X.arcDart i (k + 1), mem_arc_toFinset.2 ⟨k + 1, hk, rfl⟩, ?_⟩
  · rw [hv]
    exact X.vertexOf_mem_internalVertices.2 ((X.arcLength_eq_succ_iff.1 hm).2 k (by omega))
  · rw [hv, arcDart_succ_eq hX hk, X.vertexOf_rot_pow_apply]

/-- The `ζ` list of a simple arc has no repeated dart. -/
private theorem nodup_sideList_arc (hX : X.IsTripleDiagram) {i : Fin b} (hS : X.IsSimpleArc i)
    (ζ : StrandSide) : (X.sideList ζ (X.arc i)).Nodup := by
  have h := (hS.isCutData_arcCutList hX ζ).nodup
  rw [arcCutList_eq_append] at h
  exact h.sublist (List.sublist_append_right _ _)

omit [Fintype H] in
/-- The entries of an infix `F` of a list `L` without repeated entries sit at consecutive
positions of `L`. -/
private theorem exists_idxOf_of_isInfix {L F : List H} (hnd : L.Nodup) (hF : F <:+: L) :
    ∃ p, ∀ k (hk : k < F.length), L.idxOf F[k] = p + k := by
  obtain ⟨s, t, rfl⟩ := hF
  refine ⟨s.length, fun k hk => ?_⟩
  have hlt : s.length + k < (s ++ F ++ t).length := by simp; omega
  have h : (s ++ F ++ t)[s.length + k]'hlt = F[k] := by
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
    simp
  rw [← h, hnd.idxOf_getElem]

/-! ### Local replacements of the rotation -/

section LocalReplacement

variable {X' : TripleData H b} {D : Finset H}

omit [Fintype H] [DecidableEq H] in
private theorem rot_pow_apply_of_notMem' (hrot : ∀ d ∉ D, X'.rot d = X.rot d)
    (hD : ∀ d, X.rot d ∈ D ↔ d ∈ D) {d : H} (hd : d ∉ D) (k : ℕ) :
    (X'.rot ^ k) d = (X.rot ^ k) d ∧ (X.rot ^ k) d ∉ D := by
  induction k with
  | zero => exact ⟨rfl, hd⟩
  | succ k ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih.1, hrot _ ih.2]
    exact ⟨rfl, fun h => ih.2 ((hD _).1 h)⟩

private theorem vertexOf_eq_of_notMem' (hrot : ∀ d ∉ D, X'.rot d = X.rot d)
    (hD : ∀ d, X.rot d ∈ D ↔ d ∈ D) {d : H} (hd : d ∉ D) :
    X'.vertexOf d = X.vertexOf d := by
  ext e
  rw [RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf]
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    rw [(rot_pow_apply_of_notMem' hrot hD hd k).1]
    exact ⟨k, by simp⟩
  · intro h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    rw [← (rot_pow_apply_of_notMem' hrot hD hd k).1]
    exact ⟨k, by simp⟩

/-- An arc ends at an endpoint. -/
private theorem isBoundaryVertex_pathEnd_arc' (hX : X.IsPreTripleDiagram) (i : Fin b) :
    X.IsBoundaryVertex (X.pathEnd (X.arc i)) := by
  have h0 := hX.arcLength_ne_zero i
  obtain ⟨m, hm⟩ : ∃ m, X.arcLength i = m + 1 := ⟨X.arcLength i - 1, by omega⟩
  have hend := (X.arcLength_eq_succ_iff.1 hm).1
  have hlast : (X.arc i).getLast? = some (X.arcDart i m) := by
    rw [List.getLast?_eq_getElem?, X.length_arc, hm, show m + 1 - 1 = m by omega,
      List.getElem?_eq_getElem (by rw [X.length_arc]; omega), X.getElem_arc]
  rw [X.pathEnd_of_getLast? hlast]
  exact hend

/-- After a local replacement of the rotation on a set of darts at triple points, a strand path
with the first and last darts of the arc from `s_i` is the arc from `s_i`. -/
private theorem eq_arc_of_local' (hX : X.IsPreTripleDiagram)
    (hinv : X'.inv = X.inv) (hbdry : X'.bdry = X.bdry) (hend : X'.endDart = X.endDart)
    (hDrot : ∀ d, X.rot d ∈ D ↔ d ∈ D) (hrot : ∀ d ∉ D, X'.rot d = X.rot d)
    (hDint : ∀ d ∈ D, ¬X.IsBoundaryVertex (X.vertexOf d)) {i : Fin b} {P' : List H}
    (hP' : X'.IsStrandPath P') (hhead : P'.head? = (X.arc i).head?)
    (hlast : P'.getLast? = (X.arc i).getLast?) : P' = X'.arc i := by
  have hS0 : 0 < (X.arc i).length := by
    rw [X.length_arc]
    exact Nat.pos_of_ne_zero (hX.arcLength_ne_zero i)
  have hShead : (X.arc i).head? = some (X'.endDart (sourceIndex i)) := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hS0, X.getElem_arc, hend]
    rfl
  refine eq_arc_of_isStrandPath hP' (hhead.trans hShead) ?_
  intro e he
  rw [hlast] at he
  have hend' : X.IsBoundaryVertex (X.vertexOf (X.inv e)) := by
    have := isBoundaryVertex_pathEnd_arc' hX i
    rwa [X.pathEnd_of_getLast? he] at this
  have heD : X.inv e ∉ D := fun h => hDint _ h hend'
  change X'.IsBoundaryVertex (X'.vertexOf (X'.inv e))
  rw [hinv, vertexOf_eq_of_notMem' hrot hDrot heD]
  unfold DiskMap.IsBoundaryVertex
  rw [show X'.toDiskMap.bdry = X.toDiskMap.bdry from hbdry]
  exact hend'

end LocalReplacement

/-! ### Diagrams agreeing at the points of an arc -/

section AgreeOnArc

/-- If `σ'` agrees with `σ` on the vertex of `d`, then `σ'^k(d) = σ^k(d)`. -/
private theorem rot_pow_eq_of_forall_mem_vertexOf' {X X' : TripleData H b} {d : H}
    (h : ∀ e ∈ X.vertexOf d, X'.rot e = X.rot e) (k : ℕ) : (X'.rot ^ k) d = (X.rot ^ k) d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
    apply h
    rw [← X.vertexOf_rot_pow_apply k d]
    exact X.self_mem_vertexOf _

/-- If `σ'` agrees with `σ` at every dart not lying at a triple point avoided by the arc `S` from
`s_i`, then `σ'` and `σ` give the same `ζ` list along `S`. -/
private theorem sideList_arc_eq' {X X' : TripleData H b} {i : Fin b} (hX : X.IsTripleDiagram)
    (hinv : X'.inv = X.inv)
    (hrot : ∀ d, ¬(X.vertexOf d ∈ X.internalVertices ∧
      ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) → X'.rot d = X.rot d)
    (ζ : StrandSide) : X'.sideList ζ (X.arc i) = X.sideList ζ (X.arc i) := by
  have hpt : ∀ e ∈ (X.arc i).dropLast, ∀ d ∈ X.vertexOf (X.inv e), X'.rot d = X.rot d := by
    intro e he d hd
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 he
    simp only [List.length_dropLast, length_arc] at hk
    simp only [List.getElem_dropLast, getElem_arc] at hd
    apply hrot
    rintro ⟨hint, hpass⟩
    apply hpass
    refine ⟨hint, X.arcDart i (k + 1), mem_arc_toFinset.2 ⟨k + 1, by omega, rfl⟩, ?_⟩
    rw [arcDart_succ_eq hX (by omega), X.vertexOf_rot_pow_apply, X.vertexOf_eq_of_mem hd]
  have h : ∀ ζ', ∀ e ∈ (X.arc i).dropLast, X'.sideDarts ζ' e = X.sideDarts ζ' e := by
    intro ζ' e he
    have hp := rot_pow_eq_of_forall_mem_vertexOf' (hpt e he)
    have h1 := hpt e he _ (X.self_mem_vertexOf (X.inv e))
    cases ζ' <;> simp only [sideDarts, hinv, hp, h1]
  cases ζ
  · exact List.flatMap_congr (h _)
  · exact List.flatMap_congr fun e he => h _ e (List.mem_reverse.1 he)

end AgreeOnArc

/-! ### The arc after a push-off -/

/-- After the push-off of a closed aligned rail along the simple arc from `s_i`, the arc from `s_i`
is simple and has one dart less. -/
private theorem pushOff_arc (hX : X.IsPreTripleDiagram) {n : ℕ} (R : X.ClosedAlignedRail n)
    {i : Fin b} {ζ : StrandSide} (hS : X.IsSimpleStrandPath (X.arc i))
    (hR : R.IsAlong (X.arc i) ζ) :
    R.pushOff.IsSimpleArc i ∧ R.pushOff.arcLength i + 1 = X.arcLength i := by
  obtain ⟨P', hP's, hlen, hhead, hlast, -⟩ :=
    ClosedAlignedRail.exists_isSimpleStrandPath_pushOff hX R hS hR
  have hDint : ∀ d ∈ R.railPoints.darts, ¬X.IsBoundaryVertex (X.vertexOf d) := by
    intro d hd
    obtain ⟨a', ha', hda⟩ := R.railPoints.mem_darts.1 hd
    rw [X.vertexOf_eq_of_mem hda]
    exact (X.mem_internalVertices.1 (R.railPoints.vertexOf_mem a' ha')).2
  obtain rfl : P' = R.pushOff.arc i := eq_arc_of_local' (X' := R.pushOff) hX rfl rfl rfl
    R.railPoints.rot_mem_darts_iff (fun d hd => R.pushOff_rot_of_notMem hd) hDint
    hP's.isStrandPath hhead hlast
  refine ⟨isSimpleArc_of_isSimpleStrandPath' hP's, ?_⟩
  rw [← length_arc, ← length_arc]
  exact hlen

/-- The darts `ρ_{0,2}`, `ρ_{n,1}`, `ρ_{j,1}`, `ρ_{j,2}` (`j ∈ [1, n - 1]`) of a rail whose facing
darts sit at the consecutive positions `p, p + 1, …` of a list `L` sit at the positions
`p + 1, …, p + 2n`; a dart at another position is none of them. -/
private theorem ne_rail_darts {n q : ℕ} (hn : 1 ≤ n) (R : X.RailPoints n q) {L : List H} {p : ℕ}
    (hpos : ∀ k (hk : k < R.facingDarts.length), L.idxOf R.facingDarts[k] = p + k) {f : H}
    (hf : L.idxOf f < p + 1 ∨ p + 2 * n < L.idxOf f) :
    f ≠ R.dart (rho 0 2) ∧ f ≠ R.dart (rho n 1) ∧ ∀ j, 1 ≤ j → j ≤ n - 1 →
      f ≠ R.dart (rho j 1) ∧ f ≠ R.dart (rho j 2) := by
  have hl := R.length_facingDarts
  refine ⟨?_, ?_, fun j hj1 hj2 => ⟨?_, ?_⟩⟩ <;> rintro rfl
  · have h := hpos (2 * 0 + 1) (by omega)
    rw [R.getElem_facingDarts_two_mul_add_one (by omega)] at h
    omega
  · have h := hpos (2 * n) (by omega)
    rw [R.getElem_facingDarts_two_mul le_rfl] at h
    omega
  · have h := hpos (2 * j) (by omega)
    rw [R.getElem_facingDarts_two_mul (by omega)] at h
    omega
  · have h := hpos (2 * j + 1) (by omega)
    rw [R.getElem_facingDarts_two_mul_add_one (by omega)] at h
    omega

/-! ### Strand permutations and arcs of cuts -/

/-- The strand map of a diagram is injective. -/
private theorem strandMap_injective₃ : Function.Injective X.strandMap := by
  have hv : ∀ d d', X.RunsToEndpoint d → ¬X.RunsToEndpoint d' →
      X.inv d ≠ X.rot (X.rot (X.rot (X.inv d'))) := by
    intro d d' hd hd' h
    apply hd'
    change X.IsBoundaryVertex (X.vertexOf (X.inv d'))
    have := congrArg X.vertexOf h
    rw [X.vertexOf_rot, X.vertexOf_rot, X.vertexOf_rot] at this
    rw [← this]
    exact hd
  intro d d' h
  by_cases hd : X.RunsToEndpoint d <;> by_cases hd' : X.RunsToEndpoint d'
  · rw [X.strandMap_of_runsToEndpoint hd, X.strandMap_of_runsToEndpoint hd'] at h
    exact X.inv.injective h
  · rw [X.strandMap_of_runsToEndpoint hd, X.strandMap_of_not_runsToEndpoint hd'] at h
    exact absurd h (hv d d' hd hd')
  · rw [X.strandMap_of_not_runsToEndpoint hd, X.strandMap_of_runsToEndpoint hd'] at h
    exact absurd h.symm (hv d' d hd' hd)
  · rw [X.strandMap_of_not_runsToEndpoint hd, X.strandMap_of_not_runsToEndpoint hd'] at h
    exact X.inv.injective (X.rot.injective (X.rot.injective (X.rot.injective h)))

/-- Two arcs, the second at least as long as the first, with the same last dart are equal. -/
private theorem eq_of_arcDart_last_eq₃ (hX : X.IsPreTripleDiagram)
    {j j' : Fin b} (hle : X.arcLength j ≤ X.arcLength j')
    (h : X.arcDart j (X.arcLength j - 1) = X.arcDart j' (X.arcLength j' - 1)) : j = j' := by
  have hm := hX.arcLength_ne_zero j
  have hm' := hX.arcLength_ne_zero j'
  have h' : X.strandMap^[X.arcLength j - 1] (X.endDart (sourceIndex j)) =
      X.strandMap^[X.arcLength j - 1]
        (X.arcDart j' (X.arcLength j' - X.arcLength j)) := by
    change X.arcDart j _ = _
    rw [h, arcDart, arcDart, ← Function.iterate_add_apply]
    congr 1
    omega
  have h0 := strandMap_injective₃.iterate _ h'
  rcases Nat.eq_zero_or_pos (X.arcLength j' - X.arcLength j) with h1 | h1
  · rw [h1, arcDart_zero] at h0
    exact sourceIndex_injective (hX.endpoint_injective (by
      rw [endpoint, endpoint, h0]))
  · exfalso
    obtain ⟨t, ht⟩ : ∃ t, X.arcLength j' - X.arcLength j = t + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
    rw [ht] at h0
    obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hm'
    have hs := X.strandStep_arcDart hM (k := t) (by omega)
    have hb := (X.mem_boundaryVertices.1 (hX.endpoint_mem (sourceIndex j))).2
    change X.IsBoundaryVertex (X.vertexOf (X.endDart (sourceIndex j))) at hb
    rw [h0, hs.vertexOf_eq] at hb
    exact hs.1 hb

/-- The strand permutation of a triple diagram is injective. -/
private theorem strandPerm_injective₃ (hX : X.IsTripleDiagram) :
    Function.Injective X.strandPerm := by
  intro j j' h
  have h1 := endDart_arcEndIndex hX j
  have h2 := endDart_arcEndIndex hX j'
  have : X.arcEndIndex j = X.arcEndIndex j' := by
    simp only [arcEndIndex, h]
  rw [this, h2] at h1
  have h3 := (X.inv.injective h1).symm
  rcases le_total (X.arcLength j) (X.arcLength j') with hle | hle
  · exact eq_of_arcDart_last_eq₃ hX.toIsPreTripleDiagram hle h3
  · exact (eq_of_arcDart_last_eq₃ hX.toIsPreTripleDiagram hle h3.symm).symm

/-- Every position of a triple diagram is the start or the end of an arc. -/
private theorem exists_eq_sourceIndex_or_arcEndIndex (hX : X.IsTripleDiagram) (r : Fin (2 * b)) :
    ∃ j, r = sourceIndex j ∨ r = X.arcEndIndex j := by
  rcases exists_sourceIndex_or_targetIndex r with ⟨j, rfl⟩ | ⟨j', rfl⟩
  · exact ⟨j, Or.inl rfl⟩
  · obtain ⟨j, rfl⟩ := (Finite.injective_iff_surjective.1 (strandPerm_injective₃ hX)) j'
    exact ⟨j, Or.inr rfl⟩

/-- The arc from `s_j` of a cut along `(K, L)` with shift `s` consists of darts over `K` forming a
strand path of `X`; its first dart is the entry of `L` at the position of `s_j`, and the reverse of
its last dart the entry of `L` at the position of `t_{π(j)}`. -/
private theorem arc_cut_ends₃ {K : Finset H} {L : List H} {s : ℕ}
    (hX : X.IsPreTripleDiagram) (hc : X.IsCutData K L) (hY : (X.cut K L s).IsTripleDiagram)
    (j : Fin (L.length / 2)) :
    ∃ Q : List {d // d ∈ K}, Q.map Sum.inl = (X.cut K L s).arc j ∧
      X.IsStrandPath (Q.map Subtype.val) ∧
      (Q.map Subtype.val).head? = some L[(cutEndIndex L s (sourceIndex j) : ℕ)] ∧
      (Q.map Subtype.val).getLast?.map X.inv =
        some L[(cutEndIndex L s (targetIndex ((X.cut K L s).strandPerm j)) : ℕ)] := by
  have hinv := hX.inv_involutive
  have hYp := hY.toIsPreTripleDiagram
  have hm := hYp.arcLength_ne_zero j
  have hYP : (X.cut K L s).IsStrandPath ((X.cut K L s).arc j) :=
    (X.cut K L s).isStrandPath_arc hYp hm
  obtain ⟨Q, hQ, hP⟩ := hc.exists_isStrandPath_of_isStrandPath_cut hX hYP
  refine ⟨Q, hQ.symm, hP, ?_, ?_⟩
  · have h0 : ((X.cut K L s).arc j).head? = some ((X.cut K L s).endDart (sourceIndex j)) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [length_arc]; omega),
        getElem_arc, arcDart_zero]
    rw [hQ, List.head?_map, cut_endDart, hc.cutListDart_eq] at h0
    rw [List.head?_map]
    obtain ⟨q, hq, hq'⟩ := Option.map_eq_some_iff.1 h0
    rw [hq, Option.map_some, congrArg Subtype.val (Sum.inl_injective hq')]
  · have h0 : ((X.cut K L s).arc j).getLast? =
        some ((X.cut K L s).arcDart j ((X.cut K L s).arcLength j - 1)) := by
      rw [List.getLast?_eq_getElem?, length_arc,
        List.getElem?_eq_getElem (by rw [length_arc]; omega), getElem_arc]
    have h1 := endDart_arcEndIndex hY j
    rw [hQ, List.getLast?_map] at h0
    obtain ⟨q, hq, hq'⟩ := Option.map_eq_some_iff.1 h0
    rw [← hq', hc.cut_inv_inl hinv] at h1
    rw [List.getLast?_map, hq, Option.map_some, Option.map_some]
    change (X.cut K L s).endDart (targetIndex ((X.cut K L s).strandPerm j)) = _ at h1
    rw [cut_endDart, hc.cutListDart_eq] at h1
    exact congrArg some (congrArg Subtype.val (Sum.inl_injective h1)).symm

/-- A strand path of a triple diagram leaving along the leg at a position `ρ` and arriving at an
endpoint is the arc from `s_j`, where `ρ` is the position of `s_j`. -/
private theorem exists_eq_arc_of_isStrandPath (hX : X.IsTripleDiagram) {P : List H}
    (hP : X.IsStrandPath P) {ρ : Fin (2 * b)} (hhead : P.head? = some (X.endDart ρ))
    (hlast : ∀ e ∈ P.getLast?, X.RunsToEndpoint e) :
    ∃ j, ρ = sourceIndex j ∧ P = X.arc j := by
  rcases exists_sourceIndex_or_targetIndex ρ with ⟨j, rfl⟩ | ⟨j', rfl⟩
  · exact ⟨j, rfl, eq_arc_of_isStrandPath hP hhead hlast⟩
  · exfalso
    have h1 := hP.isOut_eq_true _ (List.mem_of_mem_head? hhead)
    rw [hX.isOut_target] at h1
    exact Bool.false_ne_true h1

/-! ### Intervals of a cut read on its cut list -/

/-- The value of a difference in `Fin n`. -/
private theorem val_sub_ite₃ {n : ℕ} (p a : Fin n) :
    ((p - a : Fin n) : ℕ) = if (a : ℕ) ≤ p then (p : ℕ) - a else n - a + p := by
  rw [Fin.val_sub]
  have := a.isLt
  have := p.isLt
  split_ifs with h
  · rw [show n - (a : ℕ) + p = (p - a) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

private theorem add_mod_ite₃ {x s n : ℕ} (hx : x < n) (hs : s ≤ n) :
    (x + s) % n = if x + s < n then x + s else x + s - n := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- After a shift by `s ≤ 1` of the circle `ℤ/n`, the positions strictly inside the cyclic
interval from `a` to `c`, when the shift of `c` is the smaller one, are those whose shifts are
larger than the shift of `a` or smaller than the shift of `c`. -/
private theorem mem_cyclicIcc_sdiff_iff_shift_compl {n s : ℕ} (hs : s ≤ 1) (a c r : Fin n)
    (hac : ((c : ℕ) + s) % n < ((a : ℕ) + s) % n) :
    r ∈ cyclicIcc a c \ {a, c} ↔
      ((a : ℕ) + s) % n < ((r : ℕ) + s) % n ∨ ((r : ℕ) + s) % n < ((c : ℕ) + s) % n := by
  have ha := a.isLt
  have hc := c.isLt
  have hr := r.isLt
  rw [mem_sdiff, mem_cyclicIcc, Fin.le_def, val_sub_ite₃, val_sub_ite₃, mem_insert,
    mem_singleton, Fin.ext_iff, Fin.ext_iff]
  rw [add_mod_ite₃ ha (by omega), add_mod_ite₃ hc (by omega)] at hac ⊢
  rw [add_mod_ite₃ hr (by omega)]
  split_ifs at hac ⊢ <;> omega

omit [Fintype H] [DecidableEq H] in
/-- An interval of `j` for a map `π` of the arcs of a cut along a list `L` with shift `s ≤ 1`,
described on the cut list: its interior positions are those whose cut list index lies outside
the closed range between the indices of the two ends `s_j` and `t_{π(j)}`. -/
private theorem exists_isIntervalOf_cut_compl {L : List H} {s : ℕ} (hs : s ≤ 1)
    (hev : Even L.length) (π : Fin (L.length / 2) → Fin (L.length / 2)) (j : Fin (L.length / 2)) :
    ∃ I, IsIntervalOf π j I ∧ ∀ r, r ∈ intervalInterior π j I ↔
      (cutEndIndex L s r : ℕ) <
          min (cutEndIndex L s (sourceIndex j) : ℕ) (cutEndIndex L s (targetIndex (π j))) ∨
        max (cutEndIndex L s (sourceIndex j) : ℕ) (cutEndIndex L s (targetIndex (π j))) <
          (cutEndIndex L s r : ℕ) := by
  have hne : (cutEndIndex L s (sourceIndex j) : ℕ) ≠ cutEndIndex L s (targetIndex (π j)) :=
    fun h => sourceIndex_ne_targetIndex j (π j) (cutEndIndex_injective (Fin.ext h))
  have h2 : 2 * (L.length / 2) = L.length := by obtain ⟨t, ht⟩ := hev; omega
  have hval : ∀ r : Fin (2 * (L.length / 2)),
      (cutEndIndex L s r : ℕ) = ((r : ℕ) + s) % (2 * (L.length / 2)) := by
    intro r
    simp only [cutEndIndex]
    exact congrArg (((r : ℕ) + s) % ·) h2.symm
  simp only [hval] at hne ⊢
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨cyclicIcc (targetIndex (π j)) (sourceIndex j), Or.inr rfl, fun r => ?_⟩
    rw [intervalInterior, pair_comm, mem_cyclicIcc_sdiff_iff_shift_compl hs _ _ r h,
      min_eq_left h.le, max_eq_right h.le, or_comm]
  · refine ⟨cyclicIcc (sourceIndex j) (targetIndex (π j)), Or.inl rfl, fun r => ?_⟩
    rw [intervalInterior, mem_cyclicIcc_sdiff_iff_shift_compl hs _ _ r h, min_eq_right h.le,
      max_eq_left h.le, or_comm]

/-! ### Isomorphisms preserve boundary-parallel arcs -/

/-- If `θ : X → X'` is an isomorphism of triple diagrams and the arc from `s'_j` of `X'` is
boundary-parallel along `I`, so is the arc from `s_j` of `X`. -/
private theorem isBoundaryParallel_of_iso₃ {H' : Type*} [Fintype H'] [DecidableEq H']
    {X' : TripleData H' b} (θ : X.Iso X') (hX : X.IsTripleDiagram)
    (hX' : X'.IsTripleDiagram) {j : Fin b} {I : Finset (Fin (2 * b))}
    (h : X'.IsBoundaryParallel j I) : X.IsBoundaryParallel j I := by
  have hp := hX.toIsPreTripleDiagram
  have hp' := hX'.toIsPreTripleDiagram
  have hπ : X'.strandPerm = X.strandPerm := θ.strandPerm_eq hp hp'
  have hlen : X'.arcLength j = X.arcLength j := by
    simp only [arcLength, θ.arcLastIndex_eq hp hp']
  obtain ⟨hI, hS', hcard, hpass⟩ := h
  rw [hπ] at hI hcard hpass
  have hS : X.IsSimpleArc j := by
    intro k l hk hl hv
    apply hS' k l (by rwa [hlen]) (by rwa [hlen])
    rw [← θ.map_arcDart hp hp', ← θ.map_arcDart hp hp', ← θ.map_inv, ← θ.map_inv,
      ← θ.map_vertexOf, ← θ.map_vertexOf, hv]
  refine ⟨hI, hS, ?_, fun r hr => ?_⟩
  · rw [← hcard, hS.ncard_passesThrough hX, hS'.ncard_passesThrough hX', hlen]
  · obtain ⟨hint, d, hd, hdv⟩ := hpass r hr
    rw [← θ.map_endDart hp hp', ← θ.map_inv] at hint hdv
    refine ⟨X.vertexOf_mem_internalVertices.2
      ((θ.isBoundaryVertex_vertexOf_iff _).not.1 (X'.vertexOf_mem_internalVertices.1 hint)), ?_⟩
    obtain ⟨t, ht, rfl⟩ := mem_arc_toFinset.1 hd
    refine ⟨X.arcDart j t, mem_arc_toFinset.2 ⟨t, by rw [← hlen]; exact ht, rfl⟩, ?_⟩
    rw [← θ.map_arcDart hp hp', ← θ.map_vertexOf, ← θ.map_vertexOf] at hdv
    exact map_injective _ hdv

/-! ### Lifting swivel moves of a cut on the nose -/

omit [Fintype H] in
private theorem isDigon_cut_congr₃ {Y : TripleData H b} {K K' : Finset H} {L L' : List H}
    {s : ℕ} (hK : K' = K) (hL : L' = L) {d : H} (hd : d ∈ K) (hd' : d ∈ K')
    (h : (Y.cut K L s).IsDigon ((Y.cut K L s).faceOf (.inl ⟨d, hd⟩))) :
    (Y.cut K' L' s).IsDigon ((Y.cut K' L' s).faceOf (.inl ⟨d, hd'⟩)) := by
  subst hK hL
  exact h

/-- The invariant of a lift of swivel moves of the cut along `S`: `X'` is reached from `X` by
swivel moves, has the data of `X` except for the rotation, which agrees with `σ` off `H_ζ(S)` minus
the cut list, has the simple arc `S` with the same side and cut list, and its cut along `S` is
`W`. -/
private def LiftInv (X : TripleData H b) (i : Fin b) (ζ : StrandSide)
    (W : TripleData (CutDart (X.arcSideDarts i ζ) (X.arcCutList i ζ).length)
      ((X.arcCutList i ζ).length / 2)) (X' : TripleData H b) : Prop :=
  Relation.ReflTransGen SwivelStep X X' ∧ X'.inv = X.inv ∧ X'.bdry = X.bdry ∧
    X'.endDart = X.endDart ∧ X'.isOut = X.isOut ∧
    (∀ d, (d ∉ X.arcSideDarts i ζ ∨ d ∈ X.arcCutList i ζ) → X'.rot d = X.rot d) ∧
    X'.IsSimpleArc i ∧ X'.arc i = X.arc i ∧ X'.arcSideDarts i ζ = X.arcSideDarts i ζ ∧
    X'.arcCutList i ζ = X.arcCutList i ζ ∧
    W = X'.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift

/-- One swivel move of the cut lifts. -/
private theorem LiftInv.step {i : Fin b} (hX : X.IsTripleDiagram) {ζ : StrandSide}
    {W W' : TripleData (CutDart (X.arcSideDarts i ζ) (X.arcCutList i ζ).length)
      ((X.arcCutList i ζ).length / 2)} {X₁ : TripleData H b} (h : X.LiftInv i ζ W X₁)
    (hst : W.SwivelStep W') : ∃ X₂, X.LiftInv i ζ W' X₂ := by
  obtain ⟨hch, hinv, hbdry, hend, hout, hrot, hS₁, harc, hK, hL, rfl⟩ := h
  set K := X.arcSideDarts i ζ with hKdef
  set L := X.arcCutList i ζ with hLdef
  have hX₁ : X₁.IsTripleDiagram := isTripleDiagram_of_reflTransGen_swivelStep hch hX
  have hc : X₁.IsCutData K L := by
    have := hS₁.isCutData_arcCutList hX₁ ζ
    rwa [hK, hL] at this
  obtain ⟨e, hD, rfl⟩ := hst
  rcases e with e | p
  swap
  · exfalso
    have hdisj := ((X₁.cut K L ζ.cutShift).mem_internalFaces.1 hD.1).2
    exact disjoint_left.1 hdisj ((X₁.cut K L ζ.cutShift).self_mem_faceOf _)
      (IsCutData.mem_cut_bdry.2 rfl)
  obtain ⟨h₂, -, he1, he2, -, hDX⟩ := hc.isDigon_of_isDigon_cut hX₁.toIsPreTripleDiagram hD
  have hcut := hc.swivelMove_cut hX₁.toIsPreTripleDiagram hD
  have hd₁ : e.1 ∈ X₁.arcSideDarts i ζ := hK ▸ e.2
  have hD' := isDigon_cut_congr₃ (Y := X₁) (s := ζ.cutShift) hK hL e.2 hd₁ hD
  obtain ⟨-, -, hS₂, harc₂, hK₂, hL₂, -⟩ := hS₁.arcCut_swivelMove hX₁ ζ hd₁ hD'
  have hUK : ∀ z ∈ X₁.vertexOf e.1 ∪ X₁.vertexOf (X₁.facePerm e.1), z ∈ K ∧ z ∉ L := by
    intro z hz
    rcases mem_union.1 hz with hz | hz
    · exact hc.mem_of_mem_vertexOf _ e.2 he1 z hz
    · exact hc.mem_of_mem_vertexOf _ h₂ he2 z hz
  refine ⟨X₁.swivelMove e.1, hch.tail ⟨e.1, hDX, rfl⟩, hinv, hbdry, hend, hout,
    fun d hd => ?_, hS₂, harc₂.trans harc, hK₂.trans hK, hL₂.trans hL, hcut.symm⟩
  have hdU : d ∉ X₁.vertexOf e.1 ∪ X₁.vertexOf (X₁.facePerm e.1) := by
    intro hdU
    obtain ⟨h1, h2⟩ := hUK d hdU
    rcases hd with hd | hd
    · exact hd h1
    · exact h2 hd
  rw [swivelMove_rot, swivelRot_apply_of_notMem hdU]
  exact hrot d hd

/-- Swivel moves of the cut along a simple arc lift, on the nose, to swivel moves of the
diagram. -/
private theorem exists_liftInv {i : Fin b} (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {ζ : StrandSide} {W : TripleData (CutDart (X.arcSideDarts i ζ) (X.arcCutList i ζ).length)
      ((X.arcCutList i ζ).length / 2)}
    (hW : Relation.ReflTransGen SwivelStep (X.arcCut i ζ) W) : ∃ X', X.LiftInv i ζ W X' := by
  induction hW with
  | refl =>
    exact ⟨X, Relation.ReflTransGen.refl, rfl, rfl, rfl, rfl, fun _ _ => rfl, hS, rfl, rfl,
      rfl, rfl⟩
  | tail _ hst ih =>
    obtain ⟨X₁, h₁⟩ := ih
    exact h₁.step hX hst

/-! ### Single-dart arcs of a cut -/

/-- An arc through a dart `d` that lies at an endpoint and whose reverse lies at an endpoint is
the single dart `d` or `d̄`. -/
private theorem arc_eq_single₃ (hX : X.IsPreTripleDiagram) {j : Fin b} {d : H}
    (hd : d ∈ X.arcDarts j) (hb : X.IsBoundaryVertex (X.vertexOf d))
    (hb' : X.IsBoundaryVertex (X.vertexOf (X.inv d))) :
    X.arcLength j = 1 ∧ (X.endDart (sourceIndex j) = d ∨ X.endDart (sourceIndex j) = X.inv d) := by
  have hinv := hX.inv_involutive
  have key : ∀ e, e ∈ X.arc j → X.IsBoundaryVertex (X.vertexOf e) →
      X.IsBoundaryVertex (X.vertexOf (X.inv e)) →
        X.arcLength j = 1 ∧ X.endDart (sourceIndex j) = e := by
    intro e he hbe hbe'
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (hX.arcLength_ne_zero j)
    obtain ⟨k, hk, rfl⟩ := mem_arc_toFinset.1 (List.mem_toFinset.2 he)
    rcases k with _ | k
    · refine ⟨(X.arcLength_eq_succ_iff (m := 0)).2 ⟨hbe', fun k hk => absurd hk
        (Nat.not_lt_zero _)⟩, rfl⟩
    · exact absurd hbe (X.strandStep_arcDart hm (k := k) (by omega)).not_isBoundaryVertex
  rcases mem_union.1 hd with h | h
  · obtain ⟨h1, h2⟩ := key d (List.mem_toFinset.1 h) hb hb'
    exact ⟨h1, Or.inl h2⟩
  · obtain ⟨e, he, rfl⟩ := mem_image.1 h
    rw [hinv] at hb'
    obtain ⟨h1, h2⟩ := key e (List.mem_toFinset.1 he) hb' hb
    exact ⟨h1, Or.inr (by rwa [hinv])⟩

private theorem val_finRotate_pow₃ {n : ℕ} (a : Fin n) (k : ℕ) :
    ((finRotate n ^ k) a : ℕ) = ((a : ℕ) + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt a.isLt]
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    have hn : 0 < n := Fin.pos a
    haveI : NeZero n := ⟨by omega⟩
    rw [finRotate_apply, Fin.val_add, ih, Fin.val_one', Nat.add_mod_mod, Nat.mod_add_mod,
      add_assoc]

private theorem finRotate_pow_val_sub₃ {n : ℕ} (a c : Fin n) :
    (finRotate n ^ ((c - a : Fin n) : ℕ)) a = c := by
  apply Fin.ext
  rw [val_finRotate_pow₃, Fin.sub_def]
  simp only
  have ha := a.isLt
  have hc := c.isLt
  rw [Nat.add_mod_mod, show (a : ℕ) + (n - a + c) = n + c by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt hc]

omit [Fintype H] [DecidableEq H] in
/-- The index in the cut list of the leg at the position `t` steps clockwise from `r`. -/
private theorem val_cutEndIndex_finRotate_pow₃ {L : List H} {s : ℕ} (hev : Even L.length)
    (r : Fin (2 * (L.length / 2))) (t : ℕ) :
    (cutEndIndex L s ((finRotate _ ^ t) r) : ℕ) = ((cutEndIndex L s r : ℕ) + t) % L.length := by
  have h2 : 2 * (L.length / 2) = L.length := by obtain ⟨u, hu⟩ := hev; omega
  simp only [cutEndIndex]
  have e : ∀ m, m = L.length → ((r : ℕ) + t) % m = ((r : ℕ) + t) % L.length := by
    rintro m rfl; rfl
  rw [val_finRotate_pow₃, e _ h2, Nat.mod_add_mod, Nat.mod_add_mod, add_right_comm]

/-- The two sides of a simple arc are disjoint. -/
private theorem disjoint_arcSideDarts_opposite₃ {i : Fin b} (ζ : StrandSide) :
    Disjoint (X.arcSideDarts i ζ) (X.arcSideDarts i ζ.opposite) := by
  cases ζ
  · exact disjoint_rightSide_leftSide
  · exact disjoint_rightSide_leftSide.symm

/-- The cut list of a single-dart arc of a cut: let `A` be an arc of `Y = X.cut K L s` consisting
of one dart, with its two ends at the legs `g_{t-1}` and `g_c` of `Y` (`t - 1 < t < c` indices of
`L`), and let `θ` be the side of `A` containing the leg `g_t`. Then the `θ` cut list of `A` is
`(g_t, …, g_{c-1})`. -/
private theorem arcCutList_of_single₃ {K : Finset H} {L : List H} {s : ℕ} (hc : X.IsCutData K L)
    (hev : Even L.length) (hY : (X.cut K L s).IsTripleDiagram) {j₀ : Fin (L.length / 2)}
    (hlen : (X.cut K L s).arcLength j₀ = 1) {t c : ℕ} (ht : 1 ≤ t) (htc : t < c)
    (hcN : c < L.length)
    (hends : ((cutEndIndex L s (sourceIndex j₀) : ℕ) = t - 1 ∧
        (cutEndIndex L s ((X.cut K L s).arcEndIndex j₀) : ℕ) = c) ∨
      ((cutEndIndex L s (sourceIndex j₀) : ℕ) = c ∧
        (cutEndIndex L s ((X.cut K L s).arcEndIndex j₀) : ℕ) = t - 1))
    {θ : StrandSide}
    (hθ : (Sum.inl ⟨L[t]'(by omega), hc.getElem_mem ⟨t, by omega⟩⟩ : CutDart K L.length) ∈
      (X.cut K L s).arcSideDarts j₀ θ) :
    ((X.cut K L s).arcCutList j₀ θ).length = c - t ∧
      ∀ u (hu : u < c - t), ((X.cut K L s).arcCutList j₀ θ)[u]? =
        some (Sum.inl ⟨L[t + u]'(by omega), hc.getElem_mem ⟨t + u, by omega⟩⟩) := by
  set Y := X.cut K L s with hYdef
  have hS₀ : Y.IsSimpleArc j₀ := fun k l hk hl _ => by omega
  have hleg : ∀ r, Y.endDart r = .inl ⟨L[(cutEndIndex L s r : ℕ)], hc.getElem_mem _⟩ := by
    intro r
    rw [hYdef, cut_endDart, hc.cutListDart_eq]
  have hpos := fun r m => val_cutEndIndex_finRotate_pow₃ (H := H) (s := s) hev r m
  obtain ⟨rt, hrt⟩ := cutEndIndex_surjective (H := H) (L := L) (s := s) hev ⟨t, by omega⟩
  have hrtv : (cutEndIndex L s rt : ℕ) = t := by rw [hrt]
  have hp : rt ≠ sourceIndex j₀ := by
    rintro rfl
    rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hq : rt ≠ Y.arcEndIndex j₀ := by
    rintro rfl
    rcases hends with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega
  have hrun : ∃ u, u + 1 < ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ) ∧
      rt = (finRotate _ ^ (u + 1)) (Y.arcSideStart j₀ θ) := by
    rcases exists_eq_finRotate_pow_arcSideStart (X := Y) hp hq θ with h | ⟨u, hu, hru⟩
    · exact h
    · exfalso
      have hmem := getElem?_arcCutList_of_lt (X := Y) (i := j₀) θ.opposite hu
      have hK := (hS₀.isCutData_arcCutList hY θ.opposite).mem_of_mem_list _
        (List.mem_of_getElem? hmem)
      rw [← hru, hleg, show (⟨L[(cutEndIndex L s rt : ℕ)], hc.getElem_mem _⟩ : {d // d ∈ K}) =
        ⟨L[t]'(by omega), hc.getElem_mem ⟨t, by omega⟩⟩ from Subtype.ext (by simp only [hrt])]
        at hK
      exact disjoint_left.1 (disjoint_arcSideDarts_opposite₃ (X := Y) (i := j₀) θ) hθ hK
  obtain ⟨ut, hut, hrt'⟩ := hrun
  have hAE : (cutEndIndex L s (Y.arcSideStart j₀ θ) : ℕ) = t - 1 ∧
      (cutEndIndex L s (Y.arcSideEnd j₀ θ) : ℕ) = c := by
    have hd := (Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _).isLt
    have hE := hpos (Y.arcSideStart j₀ θ) ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ)
    rw [finRotate_pow_val_sub₃] at hE
    have hR := hpos (Y.arcSideStart j₀ θ) (ut + 1)
    rw [← hrt', hrtv] at hR
    have hcases : ((cutEndIndex L s (Y.arcSideStart j₀ θ) : ℕ) = t - 1 ∧
        (cutEndIndex L s (Y.arcSideEnd j₀ θ) : ℕ) = c) ∨
        ((cutEndIndex L s (Y.arcSideStart j₀ θ) : ℕ) = c ∧
        (cutEndIndex L s (Y.arcSideEnd j₀ θ) : ℕ) = t - 1) := by
      cases θ <;> simp only [arcSideStart, arcSideEnd, arcEndIndex] at hends ⊢ <;> tauto
    rcases hcases with h | ⟨h1, h2⟩
    · exact h
    · exfalso
      rw [h1] at hE hR
      rw [h2] at hE
      rcases Nat.lt_or_ge (c + ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ))
        L.length with h3 | h3
      · rw [Nat.mod_eq_of_lt h3] at hE; omega
      · rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)] at hE
        rcases Nat.lt_or_ge (c + (ut + 1)) L.length with h4 | h4
        · rw [Nat.mod_eq_of_lt h4] at hR; omega
        · rw [Nat.mod_eq_sub_mod h4, Nat.mod_eq_of_lt (by omega)] at hR; omega
  have hd₀ : ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ) = c - t + 1 := by
    have hd := (Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _).isLt
    have hE := hpos (Y.arcSideStart j₀ θ) ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ)
    rw [finRotate_pow_val_sub₃, hAE.1, hAE.2] at hE
    rcases Nat.lt_or_ge (t - 1 + ((Y.arcSideEnd j₀ θ - Y.arcSideStart j₀ θ : Fin _) : ℕ))
      L.length with h3 | h3
    · rw [Nat.mod_eq_of_lt h3] at hE; omega
    · rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)] at hE; omega
  have hsl : Y.sideList θ (Y.arc j₀) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [length_sideList_arc, hlen]
  refine ⟨?_, fun u hu => ?_⟩
  · rw [arcCutList_eq_append, hsl, List.append_nil, List.length_map, List.length_range, hd₀]
    omega
  · rw [arcCutList_eq_append, hsl, List.append_nil, List.getElem?_map,
      List.getElem?_range (by omega), Option.map_some, hleg]
    congr 3
    have := hpos (Y.arcSideStart j₀ θ) (u + 1)
    rw [hAE.1, Nat.mod_eq_of_lt (by omega)] at this
    simp only [this]
    congr 1
    omega

/-- The common setting of Step 2: for a simple arc with `k` triple points whose side `ζ` has `2k`
positions, the `ζ` list has `2k` entries and the `ζ` cut list is `(g₀, …, g_{2k-1}, λ₀, …,
λ_{2k-1})`. -/
private theorem stepTwo_lists₃ {i : Fin b} (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hI : IsIntervalOf X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ}
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k) (hS : X.IsSimpleArc i)
    (hSk : {v | X.PassesThrough (X.arc i).toFinset v}.ncard = k) :
    (X.sideList ζ (X.arc i)).length = 2 * k ∧ (X.arcCutList i ζ).length = 4 * k ∧
      ∀ v, (X.arcCutList i ζ)[2 * k + v]? = (X.sideList ζ (X.arc i))[v]? := by
  have hm1 := hX.toIsPreTripleDiagram.arcLength_ne_zero i
  have hm : X.arcLength i = k + 1 := by have := hS.ncard_passesThrough hX; omega
  have hΛ : (X.sideList ζ (X.arc i)).length = 2 * k := by rw [length_sideList_arc]; omega
  have hcard := hI.card_intervalInterior_eq (X := X)
  rw [hζ] at hcard
  have hlegs : ((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1 = 2 * k := by
    omega
  refine ⟨hΛ, ?_, fun v => ?_⟩
  · rw [arcCutList_eq_append, List.length_append, List.length_map, List.length_range, hΛ]
    omega
  · rw [← hlegs]
    exact getElem?_arcCutList_add ζ v

/-! ### Rails from straightened cuts, for cuts along given sets and lists -/

/-- `IsSimpleArc.exists_rail_of_isBoundaryParallel_arcCut` (the case `t = 0`), with the side
`H_ζ(S)` and the cut list given as `K`, `L`. -/
private theorem rail_of_cut {i : Fin b} (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hI : IsIntervalOf X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k) (hS : X.IsSimpleArc i)
    (hSk : {v | X.PassesThrough (X.arc i).toFinset v}.ncard = k)
    {K : Finset H} {L : List H} (hK : X.arcSideDarts i ζ = K) (hL : X.arcCutList i ζ = L)
    (hg0 : ∀ g ∈ L[0]?, X.inv g ∉ X.sideList ζ (X.arc i))
    {j₂ : Fin (L.length / 2)} {Q : List {d // d ∈ K}}
    (hQ : Q.map Sum.inl = (X.cut K L ζ.cutShift).arc j₂) {w : ℕ} (hw : w < 2 * k)
    (hends : ((Q.map Subtype.val).head? = L[0]? ∧
        (Q.map Subtype.val).getLast?.map X.inv = (X.sideList ζ (X.arc i))[w]?) ∨
      ((Q.map Subtype.val).head? = (X.sideList ζ (X.arc i))[w]? ∧
        (Q.map Subtype.val).getLast?.map X.inv = L[0]?))
    {I₂ : Finset (Fin (2 * (L.length / 2)))}
    (hB₂ : (X.cut K L ζ.cutShift).IsBoundaryParallel j₂ I₂)
    (hI₂ : ∀ r, r ∈ intervalInterior (X.cut K L ζ.cutShift).strandPerm j₂ I₂ ↔
      ∃ v, w < v ∧ v < 2 * k ∧ ∃ d ∈ (X.sideList ζ (X.arc i))[v]?,
        ∃ hd : d ∈ K, (X.cut K L ζ.cutShift).endDart r = .inl ⟨d, hd⟩) :
    (∃ r, 1 ≤ r ∧ ∃ R : X.AlignedRail r, R.IsAlong (X.arc i) ζ ∧
      L[0]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3))) ∨
    (∃ r, 1 ≤ r ∧ ∃ R : X.StaggeredRail r, R.IsAlong (X.arc i) ζ ∧
      L[0]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3))) := by
  subst hK hL
  exact IsSimpleArc.exists_rail_of_isBoundaryParallel_arcCut hX hI hζ hk1 hk hS hSk hg0 hQ hw
    hends hB₂ hI₂

/-- `IsSimpleArc.exists_rail_of_isBoundaryParallel_arcCut_arcCut` (the case `t ≥ 1`), with the
side `H_ζ(S)` and the cut list given as `K`, `L`, and the side and the cut list of `A` given as
`KA`, `LA`. -/
private theorem rail_of_cut_cut {i : Fin b} (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hI : IsIntervalOf X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ}
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k) (hS : X.IsSimpleArc i)
    (hSk : {v | X.PassesThrough (X.arc i).toFinset v}.ncard = k) {t : ℕ} (ht0 : 0 < t)
    (ht : t < 2 * k) {K : Finset H} {L : List H} (hK : X.arcSideDarts i ζ = K)
    (hL : X.arcCutList i ζ = L)
    (ht' : ∀ t' < t, ∀ g ∈ L[t']?, X.inv g ∈ X.sideList ζ (X.arc i))
    (hgt : ∀ g ∈ L[t]?, X.inv g ∉ X.sideList ζ (X.arc i)) {a : ℕ}
    (ha : L[t - 1]?.map X.inv = (X.sideList ζ (X.arc i))[a]?)
    {j₀ : Fin (L.length / 2)}
    (hA : ∃ g ∈ L[t - 1]?, ∃ hg : g ∈ K,
      (Sum.inl ⟨g, hg⟩ : CutDart _ _) ∈ (X.cut K L ζ.cutShift).arcDarts j₀)
    {θ : StrandSide}
    (hθ : ∃ g ∈ L[t]?, ∃ hg : g ∈ K,
      (Sum.inl ⟨g, hg⟩ : CutDart _ _) ∈ (X.cut K L ζ.cutShift).arcSideDarts j₀ θ)
    {KA : Finset (CutDart K L.length)} {LA : List (CutDart K L.length)}
    (hKA : (X.cut K L ζ.cutShift).arcSideDarts j₀ θ = KA)
    (hLA : (X.cut K L ζ.cutShift).arcCutList j₀ θ = LA)
    {j₂ : Fin (LA.length / 2)} {Q₂ : List {d // d ∈ KA}}
    (hQ₂ : Q₂.map Sum.inl = ((X.cut K L ζ.cutShift).cut KA LA θ.cutShift).arc j₂)
    {Q : List {d // d ∈ K}} (hQQ : Q₂.map Subtype.val = Q.map Sum.inl)
    {w : ℕ} (hw : w < a)
    (hends : ((Q.map Subtype.val).head? = L[t]? ∧
        (Q.map Subtype.val).getLast?.map X.inv = (X.sideList ζ (X.arc i))[w]?) ∨
      ((Q.map Subtype.val).head? = (X.sideList ζ (X.arc i))[w]? ∧
        (Q.map Subtype.val).getLast?.map X.inv = L[t]?))
    {I₂ : Finset (Fin (2 * (LA.length / 2)))}
    (hB₂ : ((X.cut K L ζ.cutShift).cut KA LA θ.cutShift).IsBoundaryParallel j₂ I₂)
    (hI₂ : ∀ r, r ∈ intervalInterior ((X.cut K L ζ.cutShift).cut KA LA θ.cutShift).strandPerm
        j₂ I₂ ↔
      ∃ v, w < v ∧ v < a ∧ ∃ d ∈ (X.sideList ζ (X.arc i))[v]?, ∃ (hd : d ∈ K)
        (hd' : (Sum.inl ⟨d, hd⟩ : CutDart _ _) ∈ KA),
        ((X.cut K L ζ.cutShift).cut KA LA θ.cutShift).endDart r = .inl ⟨.inl ⟨d, hd⟩, hd'⟩) :
    (∃ r, 1 ≤ r ∧ ∃ R : X.AlignedRail r, R.IsAlong (X.arc i) ζ ∧
      L[t]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3)) ∧
      ∀ t' < t, ∀ g ∈ L[t']?, X.inv g ∉ R.facingDarts) ∨
    (∃ r, 1 ≤ r ∧ ∃ R : X.StaggeredRail r, R.IsAlong (X.arc i) ζ ∧
      L[t]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3)) ∧
      ∀ t' < t, ∀ g ∈ L[t']?, X.inv g ∈ R.facingDarts →
        X.inv g = X.railDart R.rho R.eta (RailLabel.rho r 2)) := by
  subst hK hL
  subst hKA hLA
  exact IsSimpleArc.exists_rail_of_isBoundaryParallel_arcCut_arcCut hX hI hζ hk hS hSk ht0 ht
    ht' hgt ha hA hθ hQ₂ hQQ hw hends hB₂ hI₂

/-! ### Combing -/

/-- The legs of the cut lists of two diagrams with the same strand permutation and the same legs
agree. -/
private theorem getElem?_arcCutList_congr {X' : TripleData H b} {i : Fin b}
    (hπ : X'.strandPerm = X.strandPerm) (hend : X'.endDart = X.endDart)
    {I : Finset (Fin (2 * b))} (hI : IsIntervalOf X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {t : ℕ}
    (ht : t < (intervalInterior X.strandPerm i I).card) :
    (X'.arcCutList i ζ)[t]? = (X.arcCutList i ζ)[t]? := by
  have hS : X'.arcSideStart i ζ = X.arcSideStart i ζ := by
    cases ζ <;> simp [arcSideStart, arcEndIndex, hπ]
  have hE : X'.arcSideEnd i ζ = X.arcSideEnd i ζ := by
    cases ζ <;> simp [arcSideEnd, arcEndIndex, hπ]
  have hcard := hI.card_intervalInterior_eq (X := X)
  rw [hζ] at hcard
  rw [getElem?_arcCutList_of_lt (X := X) ζ (by omega),
    getElem?_arcCutList_of_lt (X := X') ζ (by rw [hS, hE]; omega), hS, hend]

/-- **Combing** (the end of Step 2): combing along a rail produced from a straightened cut gives a
diagram whose arc from `s_i` is simple, has no returning path on side `ζ`, and whose legs
`g₀, …, g_t` all have their reverses in the `ζ` list. -/
private theorem exists_comb {i : Fin b} (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {I : Finset (Fin (2 * b))} (hI : IsIntervalOf X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ}
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k)
    (hret : ∀ Q a c, ¬X.IsReturningPath (X.arc i) ζ Q a c) {t : ℕ} (ht : t < 2 * k)
    (ht' : ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∈ X.sideList ζ (X.arc i))
    (hrail : (∃ r, 1 ≤ r ∧ ∃ R : X.AlignedRail r, R.IsAlong (X.arc i) ζ ∧
      (X.arcCutList i ζ)[t]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3)) ∧
      ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∉ R.facingDarts) ∨
    (∃ r, 1 ≤ r ∧ ∃ R : X.StaggeredRail r, R.IsAlong (X.arc i) ζ ∧
      (X.arcCutList i ζ)[t]?.map X.inv = some (X.railDart R.rho R.eta (RailLabel.eta r 3)) ∧
      ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∈ R.facingDarts →
        X.inv g = X.railDart R.rho R.eta (RailLabel.rho r 2))) :
    ∃ (X' : TripleData H b) (hX' : X'.IsTripleDiagram),
      TripleDiagram.MoveEquivalent ⟨H, X, hX⟩ ⟨H, X', hX'⟩ ∧ X'.IsSimpleArc i ∧
      (∀ Q a c, ¬X'.IsReturningPath (X'.arc i) ζ Q a c) ∧
      ∀ t' < t + 1, ∀ g ∈ (X'.arcCutList i ζ)[t']?, X'.inv g ∈ X'.sideList ζ (X'.arc i) := by
  have hp := hX.toIsPreTripleDiagram
  have hSs := hS.isSimpleStrandPath hX
  -- the darts of the old legs `ḡ_{t'}`, `t' ≤ t`
  have hold : ∀ t' < t + 1, ∀ g ∈ (X.arcCutList i ζ)[t']?,
      t' < t ∧ X.inv g ∈ X.sideList ζ (X.arc i) ∨ t' = t := by
    intro t' ht'' g hg
    rcases Nat.lt_or_ge t' t with h | h
    · exact Or.inl ⟨h, ht' t' h g hg⟩
    · exact Or.inr (by omega)
  rcases hrail with ⟨r, hr, R, hR, hη, hout⟩ | ⟨r, hr, R, hR, hη, hout⟩
  · obtain ⟨hX', hmove⟩ := TripleDiagram.exists_moveEquivalent_alignedComb ⟨H, X, hX⟩ hr R
    obtain ⟨P', hP's, -, hhead, hlast, -, L₁, L₂, hsl, hsl'⟩ :=
      AlignedRail.exists_isSimpleStrandPath_alignedComb hp hr R hSs hR
    have hDint : ∀ d ∈ R.darts, ¬X.IsBoundaryVertex (X.vertexOf d) := by
      intro d hd
      obtain ⟨a', ha', hda⟩ := R.mem_darts.1 hd
      rw [X.vertexOf_eq_of_mem hda]
      exact (X.mem_internalVertices.1 (R.vertexOf_mem a' ha')).2
    obtain rfl : P' = R.alignedComb.arc i := eq_arc_of_local' (X' := R.alignedComb) hp rfl rfl rfl
      R.rot_mem_darts_iff (fun d hd => R.alignedComb_rot_of_notMem hd) hDint
      hP's.isStrandPath hhead hlast
    have hπ : R.alignedComb.strandPerm = X.strandPerm := hmove.strandPerm_eq
    refine ⟨R.alignedComb, hX', hmove, isSimpleArc_of_isSimpleStrandPath' hP's,
      AlignedRail.forall_not_isReturningPath_alignedComb hX hS hr R hR hret, ?_⟩
    intro t' ht'' g hg
    rw [getElem?_arcCutList_congr hπ rfl hI hζ (by omega)] at hg
    change X.inv g ∈ R.alignedComb.sideList ζ (R.alignedComb.arc i)
    rw [hsl']
    rcases hold t' ht'' g hg with ⟨h1, h2⟩ | rfl
    · have h3 := hout t' h1 g hg
      rw [hsl] at h2
      simp only [List.mem_append] at h2 ⊢
      tauto
    · rw [Option.mem_def.1 hg, Option.map_some, Option.some_inj] at hη
      rw [hη]
      change R.dart (eta r 3) ∈ _
      simp
  · obtain ⟨hX', hmove⟩ := TripleDiagram.exists_moveEquivalent_staggeredComb ⟨H, X, hX⟩ R
    obtain ⟨P', hP's, -, hhead, hlast, -, L₁, L₂, hsl, hsl'⟩ :=
      StaggeredRail.exists_isSimpleStrandPath_staggeredComb hp R hSs hR
    have hDint : ∀ d ∈ R.darts, ¬X.IsBoundaryVertex (X.vertexOf d) := by
      intro d hd
      obtain ⟨a', ha', hda⟩ := R.mem_darts.1 hd
      rw [X.vertexOf_eq_of_mem hda]
      exact (X.mem_internalVertices.1 (R.vertexOf_mem a' ha')).2
    obtain rfl : P' = R.staggeredComb.arc i := eq_arc_of_local' (X' := R.staggeredComb) hp rfl
      rfl rfl R.rot_mem_darts_iff (fun d hd => R.staggeredComb_rot_of_notMem hd) hDint
      hP's.isStrandPath hhead hlast
    have hπ : R.staggeredComb.strandPerm = X.strandPerm := hmove.strandPerm_eq
    refine ⟨R.staggeredComb, hX', hmove, isSimpleArc_of_isSimpleStrandPath' hP's,
      StaggeredRail.forall_not_isReturningPath_staggeredComb hX hS R hR hret, ?_⟩
    intro t' ht'' g hg
    rw [getElem?_arcCutList_congr hπ rfl hI hζ (by omega)] at hg
    change X.inv g ∈ R.staggeredComb.sideList ζ (R.staggeredComb.arc i)
    rw [hsl']
    rcases hold t' ht'' g hg with ⟨h1, h2⟩ | rfl
    · by_cases h3 : X.inv g ∈ R.facingDarts
      · rw [hout t' h1 g hg h3]
        change R.dart (rho r 2) ∈ _
        simp
      · rw [hsl] at h2
        simp only [List.mem_append] at h2 ⊢
        tauto
    · rw [Option.mem_def.1 hg, Option.map_some, Option.some_inj] at hη
      rw [hη]
      change R.dart (eta r 3) ∈ _
      simp

/-! ### The cut along a minimal interval -/

/-- A dart of the `ζ` list of the arc from `s_i` lies at a triple point. -/
private theorem not_isBoundaryVertex_of_mem_sideList_arc {i : Fin b} {ζ : StrandSide} {d : H}
    (hd : d ∈ X.sideList ζ (X.arc i)) : ¬X.IsBoundaryVertex (X.vertexOf d) := by
  obtain ⟨k, hk, h⟩ := mem_sideList_arc.1 hd
  have hv : X.vertexOf d = X.vertexOf (X.inv (X.arcDart i k)) := by
    cases ζ <;> simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at h <;>
      rcases h with rfl | rfl <;> simp [X.vertexOf_rot_pow_apply, X.vertexOf_rot]
  rw [hv]
  obtain ⟨m, hm⟩ : ∃ m, X.arcLength i = m + 1 := ⟨X.arcLength i - 1, by omega⟩
  exact (X.arcLength_eq_succ_iff.1 hm).2 k (by omega)

/-- In the setting of Step 2, the entry `x` of the `ζ` cut list `(g₀, …, g_{2k-1}, λ₀, …,
λ_{2k-1})` lies in the `ζ` list exactly when `x ≥ 2k`. -/
private theorem getElem_arcCutList_mem_sideList_iff {i : Fin b} (hX : X.IsTripleDiagram)
    {I : Finset (Fin (2 * b))} (hI : IsIntervalOf X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ}
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k) (hS : X.IsSimpleArc i)
    (hSk : {v | X.PassesThrough (X.arc i).toFinset v}.ncard = k) {x : ℕ}
    (hx : x < (X.arcCutList i ζ).length) :
    (X.arcCutList i ζ)[x] ∈ X.sideList ζ (X.arc i) ↔ 2 * k ≤ x := by
  obtain ⟨hΛ, hL, hLΛ⟩ := stepTwo_lists₃ hX hI hζ hk hS hSk
  have hcard := hI.card_intervalInterior_eq (X := X)
  rw [hζ] at hcard
  constructor
  · intro h
    by_contra hlt
    have h1 := getElem?_arcCutList_of_lt (X := X) (i := i) ζ (t := x) (by omega)
    rw [List.getElem?_eq_getElem hx, Option.some_inj] at h1
    rw [h1] at h
    exact not_isBoundaryVertex_of_mem_sideList_arc h
      (X.mem_boundaryVertices.1 (hX.endpoint_mem _)).2
  · intro h
    have h1 := hLΛ (x - 2 * k)
    rw [show 2 * k + (x - 2 * k) = x by omega, List.getElem?_eq_getElem hx] at h1
    exact List.mem_of_getElem? h1.symm

/-- **The arcs of the cut along a minimal interval**: in the setting of Step 2, every arc of the
cut joins a leg `g_x` (`x < 2k`) to a dart `λ_{x - 2k}` of the `ζ` list (`x ≥ 2k`), read on the
indices of the cut list of its two ends. -/
private theorem arcCut_ends_split {i : Fin b} (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {I : Finset (Fin (2 * b))} (hI : IsMinimalInterval X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ}
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k)
    (hN : 2 ≤ (X.arcCutList i ζ).length)
    (hret : ∀ Q a c, ¬X.IsReturningPath (X.arc i) ζ Q a c)
    (j : Fin ((X.arcCutList i ζ).length / 2)) :
    ((cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ) < 2 * k ∧
      2 * k ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
        (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ)) ∨
    (2 * k ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ) ∧
      (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
        (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ) < 2 * k) := by
  have hc := hS.isCutData_arcCutList hX ζ
  have hY := hS.isTripleDiagram_arcCut hX ζ hN
  have hSk : {v | X.PassesThrough (X.arc i).toFinset v}.ncard = k := by
    have := hS.two_mul_ncard_passesThrough_of_isMinimalInterval hX hI hζ hN hret
    omega
  have hmem := fun x hx => getElem_arcCutList_mem_sideList_iff hX hI.1 hζ hk hS hSk (x := x) hx
  obtain ⟨Q₀, hQ₀, -, hh, hl⟩ := arc_cut_ends₃ (s := ζ.cutShift) hX.toIsPreTripleDiagram hc hY j
  obtain ⟨Q, hQ, f, f', hf, hf', hcase⟩ :=
    hS.exists_arc_arcCut_of_isMinimalInterval hX hI hζ hN hret j
  obtain rfl : Q = Q₀ := List.map_injective_iff.2 Sum.inl_injective (hQ.trans hQ₀.symm)
  rw [hf, Option.some_inj] at hh
  rw [hf', Option.map_some, Option.some_inj] at hl
  have hbd : ∀ r, ¬X.endDart r ∈ X.sideList ζ (X.arc i) := fun r h =>
    not_isBoundaryVertex_of_mem_sideList_arc h (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2
  have hx₁ := (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j)).isLt
  have hx₂ := (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
    (targetIndex ((X.arcCut i ζ).strandPerm j))).isLt
  have hl' : X.inv f' = (X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ) ζ.cutShift
      (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ)] := hl
  rcases hcase with ⟨⟨r, -, hr⟩, h2⟩ | ⟨h1, r, -, hr⟩
  · refine .inl ⟨?_, ?_⟩
    · by_contra h
      have := (hmem _ hx₁).2 (by omega)
      rw [← hh, hr] at this
      exact hbd r this
    · rwa [← hmem _ hx₂, ← hl']
  · refine .inr ⟨?_, ?_⟩
    · rwa [← hmem _ hx₁, ← hh]
    · by_contra h
      have := (hmem _ hx₂).2 (by omega)
      rw [← hl', hr] at this
      exact hbd r this

/-- Two diagrams with the same strand permutation and the same `ζ` cut list of the arc from `s_i`
have the same `ζ` list along it. -/
private theorem sideList_eq_of_arcCutList_eq {X' : TripleData H b} {i : Fin b}
    (hπ : X'.strandPerm = X.strandPerm) {ζ : StrandSide}
    (h : X'.arcCutList i ζ = X.arcCutList i ζ) :
    X'.sideList ζ (X'.arc i) = X.sideList ζ (X.arc i) := by
  have e1 := arcCutList_eq_append (X := X') (i := i) ζ
  have hS : X'.arcSideStart i ζ = X.arcSideStart i ζ := by
    cases ζ <;> simp [arcSideStart, arcEndIndex, hπ]
  have hE : X'.arcSideEnd i ζ = X.arcSideEnd i ζ := by
    cases ζ <;> simp [arcSideEnd, arcEndIndex, hπ]
  rw [h, arcCutList_eq_append (X := X) (i := i) ζ, hS, hE] at e1
  exact (List.append_inj e1 (by simp)).2.symm

/-- If no arc of the cut along `(K, L)` (the side and the cut list of the arc from `s_i`) has
both of its ends in the `ζ` list, then the arc from `s_i` has no returning path on side `ζ`. -/
private theorem forall_not_isReturningPath_of_ends {i : Fin b} (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) {ζ : StrandSide} {K : Finset H} {L : List H}
    (hK : X.arcSideDarts i ζ = K) (hL : X.arcCutList i ζ = L) (hN : 2 ≤ L.length) {k : ℕ}
    (hΛ : ∀ x (hx : x < L.length), L[x] ∈ X.sideList ζ (X.arc i) ↔ 2 * k ≤ x)
    (hsplit : ∀ j : Fin (L.length / 2),
      ¬(2 * k ≤ (cutEndIndex L ζ.cutShift (sourceIndex j) : ℕ) ∧
        2 * k ≤ (cutEndIndex L ζ.cutShift
          (targetIndex ((X.cut K L ζ.cutShift).strandPerm j)) : ℕ))) :
    ∀ Q a c, ¬X.IsReturningPath (X.arc i) ζ Q a c := by
  subst hK hL
  intro Q a c hQ
  have hc := hS.isCutData_arcCutList hX ζ
  have hY := hS.isTripleDiagram_arcCut hX ζ hN
  obtain ⟨⟨Q', j, rfl, hQ'⟩, hh, hl⟩ := (hS.exists_isReturningPath_iff hX ζ hN _).1 ⟨a, c, hQ⟩
  obtain ⟨Q₁, h1, -, h2, h3⟩ := arc_cut_ends₃ (s := ζ.cutShift) hX.toIsPreTripleDiagram hc hY j
  obtain rfl : Q₁ = Q' := List.map_injective_iff.2 Sum.inl_injective (h1.trans hQ'.symm)
  obtain ⟨g, hg, hgx⟩ := Option.map_eq_some_iff.1 h3
  refine hsplit j ⟨(hΛ _ (Fin.isLt _)).1 (hh _ h2), ?_⟩
  rw [← hΛ _ (Fin.isLt _), ← hgx]
  exact hl _ hg

omit [Fintype H] [DecidableEq H] in
private theorem eq_of_getElem?_eq₃ {α : Type*} {L : List α} (hL : L.Nodup) {x y : ℕ} {d : α}
    (hx : L[x]? = some d) (hy : L[y]? = some d) : x = y := by
  obtain ⟨hx', rfl⟩ := List.getElem?_eq_some_iff.1 hx
  obtain ⟨hy', h⟩ := List.getElem?_eq_some_iff.1 hy
  exact hL.getElem_inj_iff.1 h.symm

/-! ### Darts of cuts -/

omit [Fintype H] [DecidableEq H] in
/-- The first dart of a list of darts of a cut over `K`, read in `X`. -/
private theorem head?_map_val_of_map_inl {K : Finset H} {n : ℕ} {Q : List {d // d ∈ K}}
    {d : {d // d ∈ K}} (h : (Q.map (Sum.inl : _ → CutDart K n)).head? = some (.inl d)) :
    (Q.map Subtype.val).head? = some d.1 := by
  cases Q with
  | nil => simp at h
  | cons q Q =>
    simp only [List.map_cons, List.head?_cons, Option.some_inj, Sum.inl.injEq] at h ⊢
    rw [h]

/-- The reverse of the last dart of a list of darts of a cut over `K`, read in `X`. -/
private theorem getLast?_map_val_of_map_inl {K : Finset H} {L : List H} {s : ℕ}
    (hc : X.IsCutData K L) (hinv : Function.Involutive X.inv) {Q : List {d // d ∈ K}}
    {d : {d // d ∈ K}}
    (h : (Q.map Sum.inl).getLast?.map (X.cut K L s).inv = some (.inl d)) :
    (Q.map Subtype.val).getLast?.map X.inv = some d.1 := by
  rw [List.getLast?_map, Option.map_map] at h
  rw [List.getLast?_map, Option.map_map]
  obtain ⟨q, hq, hqd⟩ := Option.map_eq_some_iff.1 h
  rw [hq, Option.map_some]
  simp only [Function.comp_apply, hc.cut_inv_inl hinv, Sum.inl.injEq] at hqd
  rw [Function.comp_apply, ← hqd]

/-- The leg of a cut at the endpoint `ε'(r)` is the dart of the cut list of index
`cutEndIndex L s r`. -/
private theorem cut_endDart_eq {K : Finset H} {L : List H} {s : ℕ} (hc : X.IsCutData K L)
    (r : Fin (2 * (L.length / 2))) :
    (X.cut K L s).endDart r = .inl ⟨L[(cutEndIndex L s r : ℕ)], hc.getElem_mem _⟩ := by
  rw [cut_endDart, hc.cutListDart_eq]

/-- A dart of the cut list lies at an endpoint of the cut. -/
private theorem cut_isBoundaryVertex_getElem {K : Finset H} {L : List H} {s : ℕ}
    (hc : X.IsCutData K L) {x : ℕ} (hx : x < L.length) :
    (X.cut K L s).IsBoundaryVertex
      ((X.cut K L s).vertexOf (.inl ⟨L[x], hc.getElem_mem ⟨x, hx⟩⟩)) := by
  have h : (Sum.inl ⟨L[x], hc.getElem_mem ⟨x, hx⟩⟩ : CutDart K L.length) =
      cutListDart K L ⟨x, hx⟩ := (hc.cutListDart_eq ⟨x, hx⟩).symm
  rw [h]
  exact hc.cut_isBoundaryVertex_vertexOf_of_mem_cutTriple (k := ⟨x, hx⟩) (by simp [cutTriple])

/-- **The arcs of the nested cut** (Step 2, `t ≥ 1`): if every arc of `Y = X|_{S,ζ}` joins a leg
`g_x` (`x < 2k`) to a dart `λ_{x-2k}` (`x ≥ 2k`), and the cut list of the arc `A` of `Y` is
`(g_t, g_{t+1}, …)`, then every arc of `Y|_{A,θ}` joins entries `g_{t+z}` of the two kinds. -/
private theorem nested_ends_split {i : Fin b} (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {ζ : StrandSide} (hN : 2 ≤ (X.arcCutList i ζ).length) {k t : ℕ}
    (hsplit : ∀ j : Fin ((X.arcCutList i ζ).length / 2),
      ((cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ) < 2 * k ∧
        2 * k ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
          (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ)) ∨
      (2 * k ≤ (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ) ∧
        (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
          (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ) < 2 * k))
    {j₀ : Fin ((X.arcCutList i ζ).length / 2)} {θ : StrandSide}
    (hS₀ : (X.arcCut i ζ).IsSimpleArc j₀)
    (hNA : 2 ≤ ((X.arcCut i ζ).arcCutList j₀ θ).length)
    (hLA : ∀ u (hu : u < ((X.arcCut i ζ).arcCutList j₀ θ).length),
      ∃ hx : t + u < (X.arcCutList i ζ).length, ((X.arcCut i ζ).arcCutList j₀ θ)[u] =
        .inl ⟨(X.arcCutList i ζ)[t + u], (hS.isCutData_arcCutList hX ζ).getElem_mem ⟨t + u, hx⟩⟩)
    (j : Fin (((X.arcCut i ζ).arcCutList j₀ θ).length / 2)) :
    (t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift (sourceIndex j) : ℕ) <
        2 * k ∧
      2 * k ≤ t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
        (targetIndex (((X.arcCut i ζ).arcCut j₀ θ).strandPerm j)) : ℕ)) ∨
    (2 * k ≤ t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift (sourceIndex j) : ℕ) ∧
      t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
        (targetIndex (((X.arcCut i ζ).arcCut j₀ θ).strandPerm j)) : ℕ) < 2 * k) := by
  have hc := hS.isCutData_arcCutList hX ζ
  have hY := hS.isTripleDiagram_arcCut hX ζ hN
  have hinvY := hY.toIsPreTripleDiagram.inv_involutive
  have hinv := hX.toIsPreTripleDiagram.inv_involutive
  have hcA := hS₀.isCutData_arcCutList hY θ
  have hY₂ := hS₀.isTripleDiagram_arcCut hY θ hNA
  have hev : Even (X.arcCutList i ζ).length := even_length_arcCutList ζ
  obtain ⟨Q₂, hQ₂, hQ₂s, hQ₂h, hQ₂l⟩ :=
    arc_cut_ends₃ (s := θ.cutShift) hY.toIsPreTripleDiagram hcA hY₂ j
  replace hQ₂l : (Q₂.map Subtype.val).getLast?.map (X.arcCut i ζ).inv =
      some ((X.arcCut i ζ).arcCutList j₀ θ)[(cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ)
        θ.cutShift (targetIndex (((X.arcCut i ζ).arcCut j₀ θ).strandPerm j)) : ℕ)] := hQ₂l
  have hz₁ := (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift (sourceIndex j)).isLt
  have hz₂ := (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
    (targetIndex (((X.arcCut i ζ).arcCut j₀ θ).strandPerm j))).isLt
  obtain ⟨hx₁, hLA₁⟩ := hLA _ hz₁
  obtain ⟨hx₂, hLA₂⟩ := hLA _ hz₂
  obtain ⟨ρ', hρ'⟩ := cutEndIndex_surjective (H := H) (L := X.arcCutList i ζ)
    (s := ζ.cutShift) hev ⟨_, hx₁⟩
  have hhead : (Q₂.map Subtype.val).head? = some ((X.arcCut i ζ).endDart ρ') := by
    rw [hQ₂h, hLA₁]
    change _ = some ((X.cut _ _ _).endDart ρ')
    rw [cut_endDart_eq hc]
    simp only [hρ']
  have hlast : ∀ e ∈ (Q₂.map Subtype.val).getLast?, (X.arcCut i ζ).RunsToEndpoint e := by
    intro e he
    have h := hQ₂l
    rw [Option.mem_def.1 he, Option.map_some, Option.some_inj, hLA₂] at h
    change (X.arcCut i ζ).IsBoundaryVertex ((X.arcCut i ζ).vertexOf ((X.arcCut i ζ).inv e))
    rw [h]
    exact cut_isBoundaryVertex_getElem hc hx₂
  obtain ⟨j', hρj', hQ₂arc⟩ := exists_eq_arc_of_isStrandPath hY hQ₂s hhead hlast
  obtain ⟨Q', hQ', -, -, hQ'l⟩ := arc_cut_ends₃ (s := ζ.cutShift) hX.toIsPreTripleDiagram hc hY j'
  have hQQ : Q'.map Sum.inl = Q₂.map Subtype.val := hQ'.trans hQ₂arc.symm
  have e1 : (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j') : ℕ) =
      t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift (sourceIndex j) : ℕ) := by
    rw [← hρj', hρ']
  have e2 : (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
        (targetIndex ((X.arcCut i ζ).strandPerm j')) : ℕ) =
      t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
        (targetIndex (((X.arcCut i ζ).arcCut j₀ θ).strandPerm j)) : ℕ) := by
    rw [← hQQ, hLA₂] at hQ₂l
    have h := getLast?_map_val_of_map_inl (s := ζ.cutShift) hc hinv hQ₂l
    rw [hQ'l, Option.some_inj] at h
    exact hc.nodup.getElem_inj_iff.1 h
  have := hsplit j'
  rwa [e1, e2] at this

omit [Fintype H] [DecidableEq H] in
/-- Two darts `Sum.inl L[x]`, `Sum.inl L[y]` of a cut are equal only if `x = y`. -/
private theorem idx_eq_of_inl_eq {K : Finset H} {L : List H} (hnd : L.Nodup) {x y : ℕ}
    {hx : x < L.length} {hy : y < L.length} {h1 : L[x] ∈ K} {h2 : L[y] ∈ K}
    (h : (Sum.inl ⟨L[x], h1⟩ : CutDart K L.length) = .inl ⟨L[y], h2⟩) : x = y :=
  hnd.getElem_inj_iff.1 (congrArg Subtype.val (Sum.inl_injective h))

/-- The index in the cut list of the leg of a cut at a given endpoint. -/
private theorem cutEndIndex_eq_of_endDart_eq {K : Finset H} {L : List H} {s : ℕ}
    (hc : X.IsCutData K L) {r : Fin (2 * (L.length / 2))} {x : ℕ} {hx : x < L.length}
    (h : (X.cut K L s).endDart r = .inl ⟨L[x], hc.getElem_mem ⟨x, hx⟩⟩) :
    (cutEndIndex L s r : ℕ) = x := by
  rw [cut_endDart_eq hc] at h
  exact idx_eq_of_inl_eq hc.nodup h

end Helpers

/-! ### Step 2 -/

section StepTwo

variable {X : TripleData H b}

/-- **Step 2 for `t = 0`**: if `ḡ₀` is not a dart of the `ζ` list, straightening the cut along
`S` and combing produces a diagram in which it is. -/
private theorem step_two_zero {i : Fin b} (hX : X.IsTripleDiagram)
    (hXs : TripleDiagram.IsMonogonStable ⟨H, X, hX⟩)
    (ih : ∀ (b' : ℕ) (Y : TripleDiagram b'), Y.IsMonogonStable →
      Y.data.internalVertices.card < X.internalVertices.card → Y.HasStraighteningProperty)
    {I : Finset (Fin (2 * b))} (hI : IsMinimalInterval X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k)
    (hS : X.IsSimpleArc i) (hret : ∀ Q a c, ¬X.IsReturningPath (X.arc i) ζ Q a c)
    (hg0 : ∀ g ∈ (X.arcCutList i ζ)[0]?, X.inv g ∉ X.sideList ζ (X.arc i)) :
    ∃ (X' : TripleData H b) (hX' : X'.IsTripleDiagram),
      TripleDiagram.MoveEquivalent ⟨H, X, hX⟩ ⟨H, X', hX'⟩ ∧ X'.IsSimpleArc i ∧
      (∀ Q a c, ¬X'.IsReturningPath (X'.arc i) ζ Q a c) ∧
      ∀ t' < 0 + 1, ∀ g ∈ (X'.arcCutList i ζ)[t']?, X'.inv g ∈ X'.sideList ζ (X'.arc i) := by
  have hp := hX.toIsPreTripleDiagram
  have hcard := hI.1.card_intervalInterior_eq (X := X)
  rw [hζ] at hcard
  have hNe : 2 ≤ (X.arcCutList i ζ).length := by
    rw [arcCutList_eq_append, List.length_append, List.length_map, List.length_range]; omega
  have hSk : {v | X.PassesThrough (X.arc i).toFinset v}.ncard = k := by
    have := hS.two_mul_ncard_passesThrough_of_isMinimalInterval hX hI hζ hNe hret; omega
  have hm : X.arcLength i = k + 1 := by
    have := hS.ncard_passesThrough hX
    have := hp.arcLength_ne_zero i
    omega
  obtain ⟨hΛlen, hLlen, hLΛ⟩ := stepTwo_lists₃ hX hI.1 hζ hk hS hSk
  have hmem := fun x hx => getElem_arcCutList_mem_sideList_iff hX hI.1 hζ hk hS hSk (x := x) hx
  have hc := hS.isCutData_arcCutList hX ζ
  have hY : (X.arcCut i ζ).IsTripleDiagram := hS.isTripleDiagram_arcCut hX ζ hNe
  have hev : Even (X.arcCutList i ζ).length := even_length_arcCutList ζ
  have hs : ζ.cutShift ≤ 1 := by cases ζ <;> simp [StrandSide.cutShift]
  have hsplit := arcCut_ends_split hX hS hI hζ hk hNe hret
  have hnd := hc.nodup
  -- the arc `j₂` of the cut through `g₀`
  obtain ⟨ρ, hρ⟩ := cutEndIndex_surjective (H := H) (L := X.arcCutList i ζ) (s := ζ.cutShift) hev
    ⟨0, by omega⟩
  obtain ⟨j₂, hj₂⟩ := exists_eq_sourceIndex_or_arcEndIndex hY ρ
  have hx0 : (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₂) : ℕ) = 0 ∨
      (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
        (targetIndex ((X.arcCut i ζ).strandPerm j₂)) : ℕ) = 0 := by
    rcases hj₂ with rfl | rfl
    · exact Or.inl (congrArg Fin.val hρ)
    · exact Or.inr (congrArg Fin.val hρ)
  have hsp := hsplit j₂
  have hx₁ := (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₂)).isLt
  have hx₂ := (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
    (targetIndex ((X.arcCut i ζ).strandPerm j₂))).isLt
  obtain ⟨w, hw⟩ : ∃ w, w = max (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₂) : ℕ)
      (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
        (targetIndex ((X.arcCut i ζ).strandPerm j₂)) : ℕ) - 2 * k := ⟨_, rfl⟩
  -- the interval `I₂` of `j₂` whose interior positions carry `λ_{w+1}, …, λ_{2k-1}`
  obtain ⟨I₂, hI₂int, hI₂mem⟩ :=
    exists_isIntervalOf_cut_compl hs hev (X.arcCut i ζ).strandPerm j₂
  have hImin : IsMinimalInterval (X.arcCut i ζ).strandPerm j₂ I₂ := by
    refine ⟨hI₂int, fun j' hj' ⟨h1, h2⟩ => ?_⟩
    have hr1 : sourceIndex j' ∈ intervalInterior (X.arcCut i ζ).strandPerm j₂ I₂ := by
      rw [intervalInterior, mem_sdiff, mem_insert, mem_singleton]
      exact ⟨h1, fun h => h.elim (fun h => hj' (sourceIndex_injective h))
        (sourceIndex_ne_targetIndex _ _)⟩
    have hr2 : targetIndex ((X.arcCut i ζ).strandPerm j') ∈
        intervalInterior (X.arcCut i ζ).strandPerm j₂ I₂ := by
      rw [intervalInterior, mem_sdiff, mem_insert, mem_singleton]
      exact ⟨h2, fun h => h.elim (fun h => sourceIndex_ne_targetIndex _ _ h.symm)
        (fun h => hj' (strandPerm_injective₃ hY (targetIndex_injective h)))⟩
    have e1 := (hI₂mem _).1 hr1
    have e2 := (hI₂mem _).1 hr2
    rcases hsplit j' with h | h <;> omega
  -- straightening the cut
  have hlt : (X.arcCut i ζ).internalVertices.card < X.internalVertices.card := by
    have h1 := hS.card_internalVertices_arcCut_le hX ζ
    have h3 : 0 < X.internalVertices.card := by
      have h0 := (X.arcLength_eq_succ_iff.1 hm).2 0 (by omega)
      exact Finset.card_pos.2 ⟨_, X.vertexOf_mem_internalVertices.2 h0⟩
    omega
  have hst := ih _ ⟨_, X.arcCut i ζ, hY⟩ (hS.isMonogonStable_arcCut hX hXs ζ hNe) hlt
  obtain ⟨Y', hYY', hbp⟩ := hst.2 j₂ I₂ hImin
  obtain ⟨W, hW, ⟨θ⟩⟩ := hYY'.exists_swivelSteps
  have hWt : W.IsTripleDiagram := isTripleDiagram_of_reflTransGen_swivelStep hW hY
  have hπW : W.strandPerm = (X.arcCut i ζ).strandPerm :=
    (TripleDiagram.MoveEquivalent.of_reflTransGen_swivelStep (X := ⟨_, X.arcCut i ζ, hY⟩)
      (X' := ⟨_, W, hWt⟩) hW (Isomorphic.refl _)).strandPerm_eq
  have hbpW : W.IsBoundaryParallel j₂ I₂ := isBoundaryParallel_of_iso₃ θ hWt Y'.isTripleDiagram hbp
  -- lifting the moves
  obtain ⟨X', hch, hinv, -, hend, -, -, hS', harc, hK, hL, rfl⟩ := exists_liftInv hX hS hW
  have hX' : X'.IsTripleDiagram := isTripleDiagram_of_reflTransGen_swivelStep hch hX
  have hmove : TripleDiagram.MoveEquivalent ⟨H, X, hX⟩ ⟨H, X', hX'⟩ :=
    TripleDiagram.MoveEquivalent.of_reflTransGen_swivelStep hch (Isomorphic.refl _)
  have hπ : X'.strandPerm = X.strandPerm := hmove.strandPerm_eq
  have hc' : X'.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ) := by
    have := hS'.isCutData_arcCutList hX' ζ
    rwa [hK, hL] at this
  obtain ⟨Q, hQ, -, hQh, hQl⟩ := arc_cut_ends₃ hX'.toIsPreTripleDiagram hc' hWt j₂
  rw [← List.getElem?_eq_getElem] at hQh hQl
  rw [hπW] at hQl
  have hΛ' : X'.sideList ζ (X'.arc i) = X.sideList ζ (X.arc i) :=
    sideList_eq_of_arcCutList_eq hπ hL
  have hI' : IsIntervalOf X'.strandPerm i I := hπ ▸ hI.1
  have hζ' : intervalSide X'.strandPerm i I = ζ := by rwa [hπ]
  have hk' : (intervalInterior X'.strandPerm i I).card = 2 * k := by rwa [hπ]
  have hlen' : X'.arcLength i = X.arcLength i := by
    have := congrArg List.length harc
    rwa [length_arc, length_arc] at this
  have hSk' : {v | X'.PassesThrough (X'.arc i).toFinset v}.ncard = k := by
    rw [hS'.ncard_passesThrough hX', hlen', hm]
    rfl
  have hg0' : ∀ g ∈ (X.arcCutList i ζ)[0]?, X'.inv g ∉ X'.sideList ζ (X'.arc i) := by
    rwa [hinv, hΛ']
  have hwk : w < 2 * k := by omega
  have hends : ((Q.map Subtype.val).head? = (X.arcCutList i ζ)[0]? ∧
        (Q.map Subtype.val).getLast?.map X'.inv = (X'.sideList ζ (X'.arc i))[w]?) ∨
      ((Q.map Subtype.val).head? = (X'.sideList ζ (X'.arc i))[w]? ∧
        (Q.map Subtype.val).getLast?.map X'.inv = (X.arcCutList i ζ)[0]?) := by
    rw [hΛ', ← hLΛ w, hQh, hQl]
    rcases hx0 with h0 | h0
    · left
      exact ⟨by rw [h0], by congr 1; omega⟩
    · right
      exact ⟨by congr 1; omega, by rw [h0]⟩
  have hI₂' : ∀ r, r ∈ intervalInterior
      (X'.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift).strandPerm j₂ I₂ ↔
      ∃ v, w < v ∧ v < 2 * k ∧ ∃ d ∈ (X'.sideList ζ (X'.arc i))[v]?,
        ∃ hd : d ∈ X.arcSideDarts i ζ,
          (X'.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift).endDart r =
            .inl ⟨d, hd⟩ := by
    intro r
    have hy := (cutEndIndex (X.arcCutList i ζ) ζ.cutShift r).isLt
    rw [hπW, hI₂mem r, cut_endDart, hc'.cutListDart_eq, hΛ']
    constructor
    · intro h
      refine ⟨(cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ) - 2 * k, by omega, by omega,
        _, ?_, hc'.getElem_mem _, rfl⟩
      rw [← hLΛ, show 2 * k + ((cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ) - 2 * k) =
        (cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ) by omega]
      exact List.getElem?_eq_getElem hy
    · rintro ⟨v, hv1, hv2, d, hd, hdK, he⟩
      have hde := congrArg Subtype.val (Sum.inl_injective he)
      simp only at hde
      rw [← hLΛ, ← hde] at hd
      have := eq_of_getElem?_eq₃ hnd hd (List.getElem?_eq_getElem hy)
      omega
  have hrail := rail_of_cut hX' hI' hζ' hk1 hk' hS' hSk' hK hL hg0' hQ hwk hends hbpW hI₂'
  have hret' : ∀ Q a c, ¬X'.IsReturningPath (X'.arc i) ζ Q a c := by
    refine forall_not_isReturningPath_of_ends hX' hS' hK hL hNe (k := k) (fun x hx => ?_)
      (fun j h => ?_)
    · rw [hΛ']
      exact hmem x hx
    · rw [hπW] at h
      rcases hsplit j with h' | h' <;> omega
  obtain ⟨X'', hX'', hmv, hS'', hret'', hlegs⟩ := exists_comb hX' hS' hI' hζ' hk' hret'
    (t := 0) (by omega) (fun t' h => absurd h (Nat.not_lt_zero _)) (by
      rw [hL]
      rcases hrail with ⟨r, hr, R, hR, hη⟩ | ⟨r, hr, R, hR, hη⟩
      · exact Or.inl ⟨r, hr, R, hR, hη, fun t' h => absurd h (Nat.not_lt_zero _)⟩
      · exact Or.inr ⟨r, hr, R, hR, hη, fun t' h => absurd h (Nat.not_lt_zero _)⟩)
  exact ⟨X'', hX'', hmove.trans hmv, hS'', hret'', hlegs⟩

/-- **Step 2 for `t ≥ 1`**: if `ḡ₀, …, ḡ_{t-1}` are darts of the `ζ` list and `ḡ_t` is not,
straightening the cut of `X|_{S,ζ}` along the arc `A` through `g_{t-1}` and combing produces a
diagram in which `ḡ₀, …, ḡ_t` are darts of the `ζ` list. -/
private theorem step_two_succ {i : Fin b} (hX : X.IsTripleDiagram)
    (hXs : TripleDiagram.IsMonogonStable ⟨H, X, hX⟩)
    (ih : ∀ (b' : ℕ) (Y : TripleDiagram b'), Y.IsMonogonStable →
      Y.data.internalVertices.card < X.internalVertices.card → Y.HasStraighteningProperty)
    {I : Finset (Fin (2 * b))} (hI : IsMinimalInterval X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {k : ℕ}
    (hk : (intervalInterior X.strandPerm i I).card = 2 * k)
    (hS : X.IsSimpleArc i) (hret : ∀ Q a c, ¬X.IsReturningPath (X.arc i) ζ Q a c)
    {t : ℕ} (ht0 : 0 < t) (ht : t < 2 * k)
    (ht' : ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X.inv g ∈ X.sideList ζ (X.arc i))
    (hgt : ∀ g ∈ (X.arcCutList i ζ)[t]?, X.inv g ∉ X.sideList ζ (X.arc i)) :
    ∃ (X' : TripleData H b) (hX' : X'.IsTripleDiagram),
      TripleDiagram.MoveEquivalent ⟨H, X, hX⟩ ⟨H, X', hX'⟩ ∧ X'.IsSimpleArc i ∧
      (∀ Q a c, ¬X'.IsReturningPath (X'.arc i) ζ Q a c) ∧
      ∀ t' < t + 1, ∀ g ∈ (X'.arcCutList i ζ)[t']?, X'.inv g ∈ X'.sideList ζ (X'.arc i) := by
  have hp := hX.toIsPreTripleDiagram
  have hinv := hp.inv_involutive
  have hcard := hI.1.card_intervalInterior_eq (X := X)
  rw [hζ] at hcard
  have hNe : 2 ≤ (X.arcCutList i ζ).length := by
    rw [arcCutList_eq_append, List.length_append, List.length_map, List.length_range]; omega
  have hSk : {v | X.PassesThrough (X.arc i).toFinset v}.ncard = k := by
    have := hS.two_mul_ncard_passesThrough_of_isMinimalInterval hX hI hζ hNe hret; omega
  have hm : X.arcLength i = k + 1 := by
    have := hS.ncard_passesThrough hX
    have := hp.arcLength_ne_zero i
    omega
  obtain ⟨hΛlen, hLlen, hLΛ⟩ := stepTwo_lists₃ hX hI.1 hζ hk hS hSk
  have hmem := fun x hx => getElem_arcCutList_mem_sideList_iff hX hI.1 hζ hk hS hSk (x := x) hx
  have hc := hS.isCutData_arcCutList hX ζ
  have hY : (X.arcCut i ζ).IsTripleDiagram := hS.isTripleDiagram_arcCut hX ζ hNe
  have hYp := hY.toIsPreTripleDiagram
  have hinvY := hYp.inv_involutive
  have hev : Even (X.arcCutList i ζ).length := even_length_arcCutList ζ
  have hsplit := arcCut_ends_split hX hS hI hζ hk hNe hret
  have hnd := hc.nodup
  have hYms := hS.isMonogonStable_arcCut hX hXs ζ hNe
  -- the index `a` of `ḡ_{t-1}` in the `ζ` list
  obtain ⟨a, haΛ, hΛa⟩ := List.getElem_of_mem (ht' (t - 1) (by omega) _
    (Option.mem_def.2 (List.getElem?_eq_getElem (l := X.arcCutList i ζ) (i := t - 1)
      (by omega))))
  have ha2k : a < 2 * k := by omega
  have hLa : (X.arcCutList i ζ)[2 * k + a]'(by omega) =
      X.inv ((X.arcCutList i ζ)[t - 1]'(by omega)) := by
    have h := hLΛ a
    rwa [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem haΛ, Option.some_inj,
      hΛa] at h
  have ha' : (X.arcCutList i ζ)[t - 1]?.map X.inv = (X.sideList ζ (X.arc i))[a]? := by
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem haΛ, Option.map_some, hΛa]
  -- the single-dart arc `A = j₀` of the cut through `g_{t-1}`
  obtain ⟨ρ₀, hρ₀⟩ := cutEndIndex_surjective (H := H) (L := X.arcCutList i ζ)
    (s := ζ.cutShift) hev ⟨t - 1, by omega⟩
  obtain ⟨j₀, hj₀⟩ := exists_eq_sourceIndex_or_arcEndIndex hY ρ₀
  have hgAρ : (X.arcCut i ζ).endDart ρ₀ =
      .inl ⟨(X.arcCutList i ζ)[t - 1]'(by omega), hc.getElem_mem ⟨t - 1, by omega⟩⟩ := by
    change (X.cut _ _ _).endDart ρ₀ = _
    rw [cut_endDart_eq hc]
    simp only [hρ₀]
  have hgAmem : (.inl ⟨(X.arcCutList i ζ)[t - 1]'(by omega), hc.getElem_mem ⟨t - 1, by omega⟩⟩ :
      CutDart _ _) ∈ (X.arcCut i ζ).arcDarts j₀ := by
    rw [mem_arcDarts]
    rcases hj₀ with rfl | rfl
    · exact ⟨0, Nat.pos_of_ne_zero (hYp.arcLength_ne_zero _), Or.inl (by rw [arcDart_zero, hgAρ])⟩
    · exact ⟨_, Nat.sub_lt (Nat.pos_of_ne_zero (hYp.arcLength_ne_zero _)) one_pos,
        Or.inr (by rw [← endDart_arcEndIndex hY, hgAρ])⟩
  have hinvgA : (X.arcCut i ζ).inv (.inl ⟨(X.arcCutList i ζ)[t - 1]'(by omega),
      hc.getElem_mem ⟨t - 1, by omega⟩⟩) =
      .inl ⟨(X.arcCutList i ζ)[2 * k + a]'(by omega), hc.getElem_mem ⟨_, by omega⟩⟩ := by
    change (X.cut _ _ _).inv _ = _
    rw [hc.cut_inv_inl hinv]
    congr 2
    exact hLa.symm
  have hbA := cut_isBoundaryVertex_getElem (s := ζ.cutShift) hc (x := t - 1) (by omega)
  have hbA' : (X.arcCut i ζ).IsBoundaryVertex ((X.arcCut i ζ).vertexOf ((X.arcCut i ζ).inv
      (.inl ⟨(X.arcCutList i ζ)[t - 1]'(by omega), hc.getElem_mem ⟨t - 1, by omega⟩⟩))) := by
    rw [hinvgA]
    exact cut_isBoundaryVertex_getElem hc (by omega)
  obtain ⟨hlen1, hsrc⟩ := arc_eq_single₃ hYp hgAmem hbA hbA'
  have hendA : (X.arcCut i ζ).endDart ((X.arcCut i ζ).arcEndIndex j₀) =
      (X.arcCut i ζ).inv ((X.arcCut i ζ).endDart (sourceIndex j₀)) := by
    rw [endDart_arcEndIndex hY, hlen1]
    rfl
  have hendsA : ((cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₀) : ℕ) = t - 1 ∧
        (cutEndIndex (X.arcCutList i ζ) ζ.cutShift ((X.arcCut i ζ).arcEndIndex j₀) : ℕ) =
          2 * k + a) ∨
      ((cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j₀) : ℕ) = 2 * k + a ∧
        (cutEndIndex (X.arcCutList i ζ) ζ.cutShift ((X.arcCut i ζ).arcEndIndex j₀) : ℕ) =
          t - 1) := by
    rcases hsrc with h | h
    · left
      rw [h, hinvgA] at hendA
      exact ⟨cutEndIndex_eq_of_endDart_eq hc h, cutEndIndex_eq_of_endDart_eq hc hendA⟩
    · right
      rw [h, hinvY] at hendA
      rw [hinvgA] at h
      exact ⟨cutEndIndex_eq_of_endDart_eq hc h, cutEndIndex_eq_of_endDart_eq hc hendA⟩
  -- the side `θ` of `A` containing `g_t`
  have hS₀ : (X.arcCut i ζ).IsSimpleArc j₀ := fun k l hk hl _ => by omega
  have htL : t < (X.arcCutList i ζ).length := by omega
  have hgtA : (.inl ⟨(X.arcCutList i ζ)[t], hc.getElem_mem ⟨t, htL⟩⟩ : CutDart _ _) ∉
      (X.arcCut i ζ).arcDarts j₀ := by
    rw [mem_arcDarts]
    rintro ⟨t₀, ht₀, h⟩
    obtain rfl : t₀ = 0 := by omega
    rw [arcDart_zero] at h
    rcases hsrc with h' | h' <;> rw [h'] at h
    · rcases h with h | h
      · have := idx_eq_of_inl_eq hnd h; omega
      · rw [hinvgA] at h
        have := idx_eq_of_inl_eq hnd h
        omega
    · rcases h with h | h
      · rw [hinvgA] at h
        have := idx_eq_of_inl_eq hnd h
        omega
      · rw [hinvY] at h
        have := idx_eq_of_inl_eq hnd h
        omega
  have hgtB : (.inl ⟨(X.arcCutList i ζ)[t], hc.getElem_mem ⟨t, htL⟩⟩ : CutDart _ _) ∈
      (X.arcCut i ζ).bdryᶜ := by
    rw [mem_compl]
    change _ ∉ (X.cut _ _ _).bdry
    rw [IsCutData.mem_cut_bdry]
    simp
  rw [← hS₀.arcDarts_union_rightSide_union_leftSide hY] at hgtB
  obtain ⟨θ, hθ⟩ : ∃ θ, (.inl ⟨(X.arcCutList i ζ)[t], hc.getElem_mem ⟨t, htL⟩⟩ : CutDart _ _) ∈
      (X.arcCut i ζ).arcSideDarts j₀ θ := by
    rcases mem_union.1 hgtB with h | h
    · rcases mem_union.1 h with h | h
      · exact absurd h hgtA
      · exact ⟨.right, h⟩
    · exact ⟨.left, h⟩
  -- the cut list of `A` on side `θ` is `(g_t, …, g_{2k-1}, λ₀, …, λ_{a-1})`
  obtain ⟨hLAlen, hLAget⟩ := arcCutList_of_single₃ hc hev hY hlen1 (t := t) (c := 2 * k + a)
    (by omega) (by omega) (by omega) hendsA hθ
  replace hLAlen : ((X.arcCut i ζ).arcCutList j₀ θ).length = 2 * k + a - t := hLAlen
  replace hLAget : ∀ u (hu : u < 2 * k + a - t), ((X.arcCut i ζ).arcCutList j₀ θ)[u]? =
      some (.inl ⟨(X.arcCutList i ζ)[t + u]'(by omega),
        hc.getElem_mem ⟨t + u, by omega⟩⟩) := hLAget
  have hNA : 2 ≤ ((X.arcCut i ζ).arcCutList j₀ θ).length := by
    obtain ⟨u, hu⟩ := even_length_arcCutList (X := X.arcCut i ζ) (i := j₀) θ
    omega
  have hLA' : ∀ u (hu : u < ((X.arcCut i ζ).arcCutList j₀ θ).length),
      ∃ hx : t + u < (X.arcCutList i ζ).length, ((X.arcCut i ζ).arcCutList j₀ θ)[u] =
        .inl ⟨(X.arcCutList i ζ)[t + u], hc.getElem_mem ⟨t + u, hx⟩⟩ := by
    intro u hu
    refine ⟨by omega, ?_⟩
    have h := hLAget u (by omega)
    rwa [List.getElem?_eq_getElem hu, Option.some_inj] at h
  have hsplit₂ := nested_ends_split hX hS hNe hsplit hS₀ hNA hLA'
  have hcA := hS₀.isCutData_arcCutList hY θ
  have hY₂ := hS₀.isTripleDiagram_arcCut hY θ hNA
  have hevA : Even ((X.arcCut i ζ).arcCutList j₀ θ).length := even_length_arcCutList θ
  have hsθ : θ.cutShift ≤ 1 := by cases θ <;> simp [StrandSide.cutShift]
  have hndA := hcA.nodup
  -- the arc `j₂` of the nested cut through `g_t`
  obtain ⟨ρ₂, hρ₂⟩ := cutEndIndex_surjective (L := (X.arcCut i ζ).arcCutList j₀ θ)
    (s := θ.cutShift) hevA ⟨0, by omega⟩
  obtain ⟨j₂, hj₂⟩ := exists_eq_sourceIndex_or_arcEndIndex hY₂ ρ₂
  have hz0 : (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift (sourceIndex j₂) : ℕ) = 0 ∨
      (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
        (targetIndex (((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂)) : ℕ) = 0 := by
    rcases hj₂ with rfl | rfl
    · exact Or.inl (congrArg Fin.val hρ₂)
    · exact Or.inr (congrArg Fin.val hρ₂)
  have hsp := hsplit₂ j₂
  have hz₁ := (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift (sourceIndex j₂)).isLt
  have hz₂ := (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
    (targetIndex (((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂))).isLt
  obtain ⟨w, hw⟩ : ∃ w, w = max
      (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift (sourceIndex j₂) : ℕ)
      (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
        (targetIndex (((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂)) : ℕ) - (2 * k - t) :=
    ⟨_, rfl⟩
  have hwa : w < a := by omega
  -- the interval `I₂` of `j₂` whose interior positions carry `λ_{w+1}, …, λ_{a-1}`
  obtain ⟨I₂, hI₂int, hI₂mem⟩ :=
    exists_isIntervalOf_cut_compl hsθ hevA ((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂
  have hImin : IsMinimalInterval ((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂ I₂ := by
    refine ⟨hI₂int, fun j' hj' ⟨h1, h2⟩ => ?_⟩
    have hr1 : sourceIndex j' ∈ intervalInterior ((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂ I₂ := by
      rw [intervalInterior, mem_sdiff, mem_insert, mem_singleton]
      exact ⟨h1, fun h => h.elim (fun h => hj' (sourceIndex_injective h))
        (sourceIndex_ne_targetIndex _ _)⟩
    have hr2 : targetIndex (((X.arcCut i ζ).arcCut j₀ θ).strandPerm j') ∈
        intervalInterior ((X.arcCut i ζ).arcCut j₀ θ).strandPerm j₂ I₂ := by
      rw [intervalInterior, mem_sdiff, mem_insert, mem_singleton]
      exact ⟨h2, fun h => h.elim (fun h => sourceIndex_ne_targetIndex _ _ h.symm)
        (fun h => hj' (strandPerm_injective₃ hY₂ (targetIndex_injective h)))⟩
    have e1 := (hI₂mem _).1 hr1
    have e2 := (hI₂mem _).1 hr2
    rcases hsplit₂ j' with h | h <;> omega
  -- straightening the nested cut
  have hlt : ((X.arcCut i ζ).arcCut j₀ θ).internalVertices.card < X.internalVertices.card := by
    have h1 := hS.card_internalVertices_arcCut_le hX ζ
    have h2 := hS₀.card_internalVertices_arcCut_le hY θ
    have h3 : 0 < X.internalVertices.card := by
      have h0 := (X.arcLength_eq_succ_iff.1 hm).2 0 (by omega)
      exact Finset.card_pos.2 ⟨_, X.vertexOf_mem_internalVertices.2 h0⟩
    omega
  have hst := ih _ ⟨_, (X.arcCut i ζ).arcCut j₀ θ, hY₂⟩
    (hS₀.isMonogonStable_arcCut hY hYms θ hNA) hlt
  obtain ⟨Y', hYY', hbp⟩ := hst.2 j₂ I₂ hImin
  obtain ⟨W, hW, ⟨θ'⟩⟩ := hYY'.exists_swivelSteps
  have hWt : W.IsTripleDiagram := isTripleDiagram_of_reflTransGen_swivelStep hW hY₂
  have hπW : W.strandPerm = ((X.arcCut i ζ).arcCut j₀ θ).strandPerm :=
    (TripleDiagram.MoveEquivalent.of_reflTransGen_swivelStep
      (X := ⟨_, (X.arcCut i ζ).arcCut j₀ θ, hY₂⟩) (X' := ⟨_, W, hWt⟩) hW
      (Isomorphic.refl _)).strandPerm_eq
  have hbpW : W.IsBoundaryParallel j₂ I₂ := isBoundaryParallel_of_iso₃ θ' hWt Y'.isTripleDiagram hbp
  -- lifting the moves to `X|_{S,ζ}`, then to `X`
  obtain ⟨Y₁, hchY, hinvY₁, -, -, -, -, hS₁, harcY₁, hKA, hLA, rfl⟩ := exists_liftInv hY hS₀ hW
  have hY₁t : Y₁.IsTripleDiagram := isTripleDiagram_of_reflTransGen_swivelStep hchY hY
  have hπY₁ : Y₁.strandPerm = (X.arcCut i ζ).strandPerm :=
    (TripleDiagram.MoveEquivalent.of_reflTransGen_swivelStep
      (X := ⟨_, X.arcCut i ζ, hY⟩) (X' := ⟨_, Y₁, hY₁t⟩) hchY (Isomorphic.refl _)).strandPerm_eq
  have hcA' : Y₁.IsCutData ((X.arcCut i ζ).arcSideDarts j₀ θ) ((X.arcCut i ζ).arcCutList j₀ θ) := by
    have := hS₁.isCutData_arcCutList hY₁t θ
    rwa [hKA, hLA] at this
  have hA : ∃ g ∈ (X.arcCutList i ζ)[t - 1]?, ∃ hg : g ∈ X.arcSideDarts i ζ,
      (Sum.inl ⟨g, hg⟩ : CutDart _ _) ∈ Y₁.arcDarts j₀ := by
    refine ⟨_, List.getElem?_eq_getElem (by omega), hc.getElem_mem ⟨t - 1, by omega⟩, ?_⟩
    unfold arcDarts
    rw [harcY₁, hinvY₁]
    exact hgAmem
  have hθ' : ∃ g ∈ (X.arcCutList i ζ)[t]?, ∃ hg : g ∈ X.arcSideDarts i ζ,
      (Sum.inl ⟨g, hg⟩ : CutDart _ _) ∈ Y₁.arcSideDarts j₀ θ := by
    rw [hKA]
    exact ⟨_, List.getElem?_eq_getElem htL, _, hθ⟩
  obtain ⟨Q₂, hQ₂, hQ₂s, hQ₂h, hQ₂l⟩ := arc_cut_ends₃ hY₁t.toIsPreTripleDiagram hcA' hWt j₂
  rw [← List.getElem?_eq_getElem] at hQ₂h hQ₂l
  rw [hπW] at hQ₂l
  obtain ⟨X', hch, hinv', -, -, -, -, hS', harc, hK, hL, rfl⟩ := exists_liftInv hX hS hchY
  have hX' : X'.IsTripleDiagram := isTripleDiagram_of_reflTransGen_swivelStep hch hX
  have hp' := hX'.toIsPreTripleDiagram
  have hmove : TripleDiagram.MoveEquivalent ⟨H, X, hX⟩ ⟨H, X', hX'⟩ :=
    TripleDiagram.MoveEquivalent.of_reflTransGen_swivelStep hch (Isomorphic.refl _)
  have hπ : X'.strandPerm = X.strandPerm := hmove.strandPerm_eq
  have hc' : X'.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ) := by
    have := hS'.isCutData_arcCutList hX' ζ
    rwa [hK, hL] at this
  obtain ⟨Q, hQQ, -⟩ := hc'.exists_isStrandPath_of_isStrandPath_cut hp' hQ₂s
  have hΛ' : X'.sideList ζ (X'.arc i) = X.sideList ζ (X.arc i) :=
    sideList_eq_of_arcCutList_eq hπ hL
  have hI' : IsIntervalOf X'.strandPerm i I := hπ ▸ hI.1
  have hζ' : intervalSide X'.strandPerm i I = ζ := by rwa [hπ]
  have hk' : (intervalInterior X'.strandPerm i I).card = 2 * k := by rwa [hπ]
  have hlen' : X'.arcLength i = X.arcLength i := by
    have := congrArg List.length harc
    rwa [length_arc, length_arc] at this
  have hSk' : {v | X'.PassesThrough (X'.arc i).toFinset v}.ncard = k := by
    rw [hS'.ncard_passesThrough hX', hlen', hm]
    rfl
  -- the ends of `Q`
  have hends : ((Q.map Subtype.val).head? = (X.arcCutList i ζ)[t]? ∧
        (Q.map Subtype.val).getLast?.map X'.inv = (X'.sideList ζ (X'.arc i))[w]?) ∨
      ((Q.map Subtype.val).head? = (X'.sideList ζ (X'.arc i))[w]? ∧
        (Q.map Subtype.val).getLast?.map X'.inv = (X.arcCutList i ζ)[t]?) := by
    rw [hQQ] at hQ₂h hQ₂l
    rw [List.getElem?_eq_getElem hz₁] at hQ₂h
    rw [List.getElem?_eq_getElem hz₂] at hQ₂l
    obtain ⟨hx₁', hu₁⟩ := hLA' _ hz₁
    obtain ⟨hx₂', hu₂⟩ := hLA' _ hz₂
    rw [hu₁] at hQ₂h
    rw [hu₂] at hQ₂l
    have hh := head?_map_val_of_map_inl hQ₂h
    have hl := getLast?_map_val_of_map_inl hc' hp'.inv_involutive hQ₂l
    rw [hh, hl, hΛ', ← hLΛ w]
    simp only
    rcases hz0 with h0 | h0
    · left
      rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem]
      exact ⟨by congr 1; omega, by congr 1; omega⟩
    · right
      rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem]
      exact ⟨by congr 1; omega, by congr 1; omega⟩
  -- the interior positions of `I₂`
  have hI₂' : ∀ r, r ∈ intervalInterior ((X'.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ)
      ζ.cutShift).cut ((X.arcCut i ζ).arcSideDarts j₀ θ) ((X.arcCut i ζ).arcCutList j₀ θ)
        θ.cutShift).strandPerm j₂ I₂ ↔
      ∃ v, w < v ∧ v < a ∧ ∃ d ∈ (X'.sideList ζ (X'.arc i))[v]?,
        ∃ (hd : d ∈ X.arcSideDarts i ζ)
          (hd' : (Sum.inl ⟨d, hd⟩ : CutDart _ _) ∈ (X.arcCut i ζ).arcSideDarts j₀ θ),
          ((X'.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift).cut
            ((X.arcCut i ζ).arcSideDarts j₀ θ) ((X.arcCut i ζ).arcCutList j₀ θ)
              θ.cutShift).endDart r = .inl ⟨.inl ⟨d, hd⟩, hd'⟩ := by
    intro r
    have hu := (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift r).isLt
    obtain ⟨hx, hLAu⟩ := hLA' _ hu
    rw [hπW, hI₂mem r, cut_endDart_eq hcA', hΛ']
    constructor
    · intro h
      refine ⟨t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift r : ℕ) - 2 * k,
        by omega, by omega, _, ?_, hc.getElem_mem ⟨_, hx⟩, ?_, ?_⟩
      · rw [← hLΛ, show 2 * k + (t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift
          r : ℕ) - 2 * k) = t + (cutEndIndex ((X.arcCut i ζ).arcCutList j₀ θ) θ.cutShift r : ℕ)
          by omega]
        exact List.getElem?_eq_getElem hx
      · rw [← hLAu]
        exact hcA'.getElem_mem _
      · congr 1
        exact Subtype.ext hLAu
    · rintro ⟨v, hv1, hv2, d, hd, hdK, hdA, he⟩
      have hde := congrArg Subtype.val (Sum.inl_injective he)
      simp only at hde
      rw [hLAu] at hde
      have hde' := congrArg Subtype.val (Sum.inl_injective hde)
      simp only at hde'
      rw [← hLΛ, ← hde'] at hd
      have := eq_of_getElem?_eq₃ hnd hd (List.getElem?_eq_getElem hx)
      omega
  have ht'' : ∀ t' < t, ∀ g ∈ (X.arcCutList i ζ)[t']?, X'.inv g ∈ X'.sideList ζ (X'.arc i) := by
    rwa [hinv', hΛ']
  have hgt'' : ∀ g ∈ (X.arcCutList i ζ)[t]?, X'.inv g ∉ X'.sideList ζ (X'.arc i) := by
    rwa [hinv', hΛ']
  have ha'' : (X.arcCutList i ζ)[t - 1]?.map X'.inv = (X'.sideList ζ (X'.arc i))[a]? := by
    rwa [hinv', hΛ']
  have hrail := rail_of_cut_cut hX' hI' hζ' hk' hS' hSk' ht0 ht hK hL ht'' hgt'' ha'' hA hθ'
    hKA hLA hQ₂ hQQ hwa hends hbpW hI₂'
  have hret' : ∀ Q a c, ¬X'.IsReturningPath (X'.arc i) ζ Q a c := by
    refine forall_not_isReturningPath_of_ends hX' hS' hK hL hNe (k := k) (fun x hx => ?_)
      (fun j h => ?_)
    · rw [hΛ']
      exact hmem x hx
    · rw [hπY₁] at h
      rcases hsplit j with h' | h' <;> omega
  obtain ⟨X'', hX'', hmv, hS'', hret'', hlegs⟩ := exists_comb hX' hS' hI' hζ' hk' hret' ht
    (by rwa [hL]) (by rwa [hL])
  exact ⟨X'', hX'', hmove.trans hmv, hS'', hret'', hlegs⟩

end StepTwo

end TripleData

namespace TripleDiagram

variable {b : ℕ}

open TripleData

/-- Under the induction hypothesis of the straightening lemma, the cut of a monogon-stable
diagram along a simple arc with a triple point has the straightening property. -/
private theorem hasStraighteningProperty_arcCut {X : TripleDiagram b} (hX : X.IsMonogonStable)
    (ih : ∀ (b' : ℕ) (Y : TripleDiagram b'), Y.IsMonogonStable →
      Y.data.internalVertices.card < X.data.internalVertices.card → Y.HasStraighteningProperty)
    {Y : TripleDiagram b} (hXY : X.MoveEquivalent Y) {i : Fin b} (hS : Y.data.IsSimpleArc i)
    (ζ : StrandSide) (hN : 2 ≤ (Y.data.arcCutList i ζ).length) (hm : 2 ≤ Y.data.arcLength i) :
    HasStraighteningProperty
      ⟨_, Y.data.arcCut i ζ, hS.isTripleDiagram_arcCut Y.isTripleDiagram ζ hN⟩ := by
  apply ih
  · exact hS.isMonogonStable_arcCut Y.isTripleDiagram (fun W hW => hX W (hXY.trans hW)) ζ hN
  · have h1 := hS.card_internalVertices_arcCut_le Y.isTripleDiagram ζ
    have h2 := hXY.card_internalVertices_eq
    have h3 : 0 < Y.data.internalVertices.card := by
      obtain ⟨m, hm'⟩ : ∃ m, Y.data.arcLength i = m + 1 := ⟨Y.data.arcLength i - 1, by omega⟩
      have h0 := (Y.data.arcLength_eq_succ_iff.1 hm').2 0 (by omega)
      exact Finset.card_pos.2 ⟨_, Y.data.vertexOf_mem_internalVertices.2 h0⟩
    change (Y.data.arcCut i ζ).internalVertices.card < X.data.internalVertices.card
    omega

/-- The core of part (i) of the straightening lemma: a simple arc of a diagram `Y ∼ X` with a
parallel returning path on side `ζ` gives a diagram `Y' ∼ X` whose arc from the same source is
simple, shorter, and has a parallel returning path on side `ζ`. -/
private theorem exists_shorter_parallel {X : TripleDiagram b} (hX : X.IsMonogonStable)
    (ih : ∀ (b' : ℕ) (Y : TripleDiagram b'), Y.IsMonogonStable →
      Y.data.internalVertices.card < X.data.internalVertices.card → Y.HasStraighteningProperty)
    {Y : TripleDiagram b} (hXY : X.MoveEquivalent Y) {i : Fin b} {ζ : StrandSide}
    (hS : Y.data.IsSimpleArc i) {U : List Y.Dart} {aU cU : ℕ} (hacU : aU < cU)
    (hU : Y.data.IsReturningPath (Y.data.arc i) ζ U aU cU) :
    ∃ Y' : TripleDiagram b, X.MoveEquivalent Y' ∧ Y'.data.IsSimpleArc i ∧
      (∃ U' a' c', a' < c' ∧ Y'.data.IsReturningPath (Y'.data.arc i) ζ U' a' c') ∧
      Y'.data.arcLength i < Y.data.arcLength i := by
  classical
  have hZ := Y.isTripleDiagram
  set L := Y.data.sideList ζ (Y.data.arc i) with hL
  have hLnd : L.Nodup := nodup_sideList_arc hZ hS ζ
  have hN := two_le_length_arcCutList_of_isReturningPath hU
  have hm : 2 ≤ Y.data.arcLength i := by have := hU.lt_left; rw [length_arc] at this; omega
  have hst := hasStraighteningProperty_arcCut hX ih hXY hS ζ hN hm
  -- a parallel returning path `U₀` with least span
  have hex : ∃ n, ∃ U a c f g, a < c ∧ Y.data.IsReturningPath (Y.data.arc i) ζ U a c ∧
      U.head? = some f ∧ U.getLast? = some g ∧
      max (L.idxOf f) (L.idxOf (Y.data.inv g)) - min (L.idxOf f) (L.idxOf (Y.data.inv g)) =
        n := by
    have hne := hU.isStrandPath.ne_nil
    exact ⟨_, U, aU, cU, U.head hne, U.getLast hne, hacU, hU, List.head?_eq_some_head hne,
      List.getLast?_eq_some_getLast hne, rfl⟩
  obtain ⟨U₀, a₀, c₀, f₀, g₀, hac₀, hU₀, hf₀, hg₀, -⟩ := Nat.find_spec hex
  set lo := min (L.idxOf f₀) (L.idxOf (Y.data.inv g₀)) with hlo
  set hi := max (L.idxOf f₀) (L.idxOf (Y.data.inv g₀)) with hhi
  -- among `U₀` and the returning paths with both ends in its run, one `Q` with least span
  have hex2 : ∃ n, ∃ Q a c f g, Y.data.IsReturningPath (Y.data.arc i) ζ Q a c ∧
      Q.head? = some f ∧ Q.getLast? = some g ∧
      ((Q = U₀ ∧ a = a₀ ∧ c = c₀) ∨ (lo < L.idxOf f ∧ L.idxOf f < hi ∧
        lo < L.idxOf (Y.data.inv g) ∧ L.idxOf (Y.data.inv g) < hi)) ∧
      max (L.idxOf f) (L.idxOf (Y.data.inv g)) - min (L.idxOf f) (L.idxOf (Y.data.inv g)) = n :=
    ⟨_, U₀, a₀, c₀, f₀, g₀, hU₀, hf₀, hg₀, Or.inl ⟨rfl, rfl, rfl⟩, rfl⟩
  obtain ⟨Q, a, c, fQ, gQ, hQ, hfQ, hgQ, hQin, hQn⟩ := Nat.find_spec hex2
  have hQin₀ : (Q = U₀ ∧ a = a₀ ∧ c = c₀) → L.idxOf fQ = L.idxOf f₀ ∧
      L.idxOf (Y.data.inv gQ) = L.idxOf (Y.data.inv g₀) := by
    rintro ⟨rfl, -, -⟩
    rw [Option.some_injective _ (hfQ.symm.trans hf₀), Option.some_injective _ (hgQ.symm.trans hg₀)]
    exact ⟨rfl, rfl⟩
  have hmin : ∀ Q' a' c', Y.data.IsReturningPath (Y.data.arc i) ζ Q' a' c' →
      ∀ f ∈ Q.head?, ∀ g ∈ Q.getLast?, ∀ f' ∈ Q'.head?, ∀ g' ∈ Q'.getLast?,
        let L := Y.data.sideList ζ (Y.data.arc i)
        let k := L.idxOf f
        let l := L.idxOf (Y.data.inv g)
        ¬((min k l < L.idxOf f' ∧ L.idxOf f' < max k l) ∧
          (min k l < L.idxOf (Y.data.inv g') ∧ L.idxOf (Y.data.inv g') < max k l)) := by
    intro Q' a' c' hQ' f hf g hg f' hf' g' hg'
    obtain rfl : fQ = f := Option.mem_unique hfQ hf
    obtain rfl : gQ = g := Option.mem_unique hgQ hg
    dsimp only
    rw [← hL]
    rintro ⟨⟨h1, h2⟩, h3, h4⟩
    have hlt : max (L.idxOf f') (L.idxOf (Y.data.inv g')) -
        min (L.idxOf f') (L.idxOf (Y.data.inv g')) < Nat.find hex2 := by
      rw [← hQn]; omega
    refine Nat.find_min hex2 hlt ⟨Q', a', c', f', g', hQ', Option.mem_def.1 hf',
      Option.mem_def.1 hg', Or.inr ?_, rfl⟩
    rcases hQin with hQ₀ | ⟨h5, h6, h7, h8⟩
    · obtain ⟨e1, e2⟩ := hQin₀ hQ₀
      omega
    · omega
  -- making `Q` hug `S`
  obtain ⟨Z, hZ', hmove, hinv, -, -, -, hrot, hSZ, harc, hUZ, Q'', hhug, hQh, hQl⟩ :=
    hS.exists_moveEquivalent_hugs hZ ζ hN hst hQ hmin
  have hXZ : X.MoveEquivalent ⟨Y.Dart, Z, hZ'⟩ := hXY.trans hmove
  have hhug' : Z.Hugs (Z.arc i) ζ Q'' a c := by rwa [harc]
  rcases lt_trichotomy a c with hac | rfl | hca
  · -- a parallel hugging returning path gives a hollow monogon
    exfalso
    obtain ⟨σ', -, h, hmv, e, he⟩ := exists_hollowMonogon_of_hugs ⟨Y.Dart, Z, hZ'⟩ hac hhug'
    apply hX _ (hXZ.trans hmv)
    have hp := h.toIsPreTripleDiagram
    obtain ⟨heB, -⟩ := he.facePerm_eq
    by_cases ho : ({ Z with rot := σ' } : TripleData Y.Dart b).isOut e = true
    · exact ⟨_, (TripleData.isMonogon_of_isHollowMonogon _ hp he (Or.inl rfl) ho).2.2⟩
    · refine ⟨_, (TripleData.isMonogon_of_isHollowMonogon _ hp he (Or.inr rfl) ?_).2.2⟩
      rw [hp.isOut_inv_apply heB]
      simpa using ho
  · -- a returning path from a point to itself is a monogon
    exact absurd (hasMonogon_of_isReturningPath_self hZ'.toIsPreTripleDiagram
      hhug'.isReturningPath) (hX _ hXZ)
  -- `Q` is anti-parallel, hence not `U₀`, so its ends lie in the run of `U₀`
  have hQin' : lo < L.idxOf fQ ∧ L.idxOf fQ < hi ∧ lo < L.idxOf (Y.data.inv gQ) ∧
      L.idxOf (Y.data.inv gQ) < hi := by
    rcases hQin with ⟨-, rfl, rfl⟩ | h
    · omega
    · exact h
  -- the closed aligned rail and its push-off
  obtain ⟨R, hR, -, hends⟩ := hhug'.exists_closedAlignedRail hZ'.toIsPreTripleDiagram hca
  obtain ⟨hW, hmvW⟩ := TripleDiagram.exists_moveEquivalent_pushOff ⟨Y.Dart, Z, hZ'⟩ R
  have hXW : X.MoveEquivalent ⟨Y.Dart, R.pushOff, hW⟩ := hXZ.trans hmvW
  obtain ⟨hSW, hlenW⟩ := pushOff_arc hZ'.toIsPreTripleDiagram R (hSZ.isSimpleStrandPath hZ') hR
  have hlenZ : Z.arcLength i = Y.data.arcLength i := by
    have := congrArg List.length harc
    rwa [length_arc, length_arc] at this
  -- positions in the `ζ` list
  have hLZ : Z.sideList ζ (Z.arc i) = L := by rw [harc]; exact sideList_arc_eq' hZ hinv hrot ζ
  obtain ⟨p, hpos⟩ := exists_idxOf_of_isInfix (F := R.railPoints.facingDarts) hLnd
    (by rw [← hLZ]; exact hR.1)
  have hfQ'' : Q''.head? = some fQ := hQh.trans hfQ
  obtain ⟨gQ'', hgQ'', hgg⟩ : ∃ g, Q''.getLast? = some g ∧ Y.data.inv g = Y.data.inv gQ := by
    have := hQl
    rw [hgQ, Option.map_some] at this
    exact Option.map_eq_some_iff.1 this
  have hn1 : 1 ≤ Q''.length := List.length_pos_iff.2 hhug.isReturningPath.isStrandPath.ne_nil
  have hρ := hends fQ hfQ'' gQ'' hgQ''
  have hlenF := R.railPoints.length_facingDarts
  have h02 := hpos (2 * 0 + 1) (by omega)
  rw [R.railPoints.getElem_facingDarts_two_mul_add_one (by omega)] at h02
  have hn1' := hpos (2 * Q''.length) (by omega)
  rw [R.railPoints.getElem_facingDarts_two_mul le_rfl] at hn1'
  rw [hinv, hgg] at hρ
  have hQpos : (L.idxOf fQ = p + 1 ∧ L.idxOf (Y.data.inv gQ) = p + 2 * Q''.length) ∨
      (L.idxOf fQ = p + 2 * Q''.length ∧ L.idxOf (Y.data.inv gQ) = p + 1) := by
    rcases hρ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [← h1, ← h2]; exact ⟨h02, hn1'⟩
    · right; rw [← h1, ← h2]; exact ⟨hn1', h02⟩
  -- the parallel returning path `U₀` survives the push-off
  obtain ⟨U'', hU'', hUh, hUl⟩ := hUZ U₀ a₀ c₀ hU₀
  have hU''' : Z.IsReturningPath (Z.arc i) ζ U'' a₀ c₀ := by rwa [harc]
  have hfirst := fun f (hf : f ∈ U''.head?) =>
    ne_rail_darts hn1 R.railPoints hpos (f := f) (by
      obtain rfl : f = f₀ := Option.some_injective _ ((Option.mem_def.1 hf).symm.trans
        (hUh.trans hf₀))
      omega)
  have hlast := fun g (hg : g ∈ U''.getLast?) =>
    ne_rail_darts hn1 R.railPoints hpos (f := Z.inv g) (by
      have h1 : Y.data.inv g = Y.data.inv g₀ := by
        have := hUl
        rw [Option.mem_def.1 hg, hg₀, Option.map_some, Option.map_some] at this
        exact Option.some_injective _ this
      rw [hinv, h1]
      omega)
  rcases ClosedAlignedRail.hasMonogon_or_isReturningPath_pushOff hZ'.toIsPreTripleDiagram R hR
      hU''' hac₀ hfirst hlast with hmonoW | ⟨a', c', hac', hUW⟩
  · exact absurd hmonoW (hX _ hXW)
  · refine ⟨⟨Y.Dart, R.pushOff, hW⟩, hXW, hSW, ⟨U'', a', c', hac', hUW⟩, ?_⟩
    change R.pushOff.arcLength i < Y.data.arcLength i
    omega

/-- **Straightening, part (i): no parallel digons**. Let `X` be monogon-stable, and suppose that
every monogon-stable triple diagram with fewer triple points than `X` has the straightening
property. Then no triple diagram move-equivalent to `X` has a parallel digon. -/
@[cluster_algebras "lem_straighten_no_parallel_digon"]
theorem IsMonogonStable.not_hasParallelDigon {X : TripleDiagram b} (hX : X.IsMonogonStable)
    (ih : ∀ (b' : ℕ) (Y : TripleDiagram b'), Y.IsMonogonStable →
      Y.data.internalVertices.card < X.data.internalVertices.card → Y.HasStraighteningProperty)
    {X' : TripleDiagram b} (hXX' : X.MoveEquivalent X') : ¬X'.data.HasParallelDigon := by
  classical
  intro hdig
  have hex : ∃ n, ∃ (Y : TripleDiagram b) (i : Fin b) (ζ : StrandSide), X.MoveEquivalent Y ∧
      Y.data.IsSimpleArc i ∧ (∃ U a c, a < c ∧ Y.data.IsReturningPath (Y.data.arc i) ζ U a c) ∧
      Y.data.arcLength i = n := by
    obtain ⟨i, ζ, hS, -, U, a, c, hac, hU⟩ :=
      exists_isReturningPath_of_hasParallelDigon X'.isTripleDiagram (hX X' hXX') hdig
    exact ⟨_, X', i, ζ, hXX', hS, ⟨U, a, c, hac, hU⟩, rfl⟩
  obtain ⟨Y, i, ζ, hXY, hS, ⟨U, a, c, hac, hU⟩, hn⟩ := Nat.find_spec hex
  obtain ⟨Y', hXY', hS', hU', hlt⟩ := exists_shorter_parallel hX ih hXY hS hac hU
  exact Nat.find_min hex (hn ▸ hlt) ⟨Y', i, ζ, hXY', hS', hU', rfl⟩

/-- **Straightening, Step 1: removing returning paths**. Let `X` be monogon-stable, and suppose
that every monogon-stable triple diagram with fewer triple points than `X` has the straightening
property. Let `ζ` be a side, and let the arc `S` from `s_i` be simple. Then there is `X' ∼ X` whose
arc from `s_i` is simple and has no returning path on side `ζ`. -/
@[cluster_algebras "lem_straighten_step_one"]
theorem IsMonogonStable.exists_moveEquivalent_forall_not_isReturningPath {X : TripleDiagram b}
    (hX : X.IsMonogonStable)
    (ih : ∀ (b' : ℕ) (Y : TripleDiagram b'), Y.IsMonogonStable →
      Y.data.internalVertices.card < X.data.internalVertices.card → Y.HasStraighteningProperty)
    {i : Fin b} (ζ : StrandSide) (hS : X.data.IsSimpleArc i) :
    ∃ X' : TripleDiagram b, X.MoveEquivalent X' ∧ X'.data.IsSimpleArc i ∧
      ∀ Q a c, ¬X'.data.IsReturningPath (X'.data.arc i) ζ Q a c := by
  classical
  suffices h : ∀ n (Y : TripleDiagram b), X.MoveEquivalent Y → Y.data.IsSimpleArc i →
      Y.data.arcLength i = n → ∃ X' : TripleDiagram b, X.MoveEquivalent X' ∧
        X'.data.IsSimpleArc i ∧ ∀ Q a c, ¬X'.data.IsReturningPath (X'.data.arc i) ζ Q a c from
    h _ X (MoveEquivalent.refl X) hS rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro Y hXY hSY hn
  by_cases hret : ∃ Q a c, Y.data.IsReturningPath (Y.data.arc i) ζ Q a c
  swap
  · exact ⟨Y, hXY, hSY, fun Q a c h => hret ⟨Q, a, c, h⟩⟩
  obtain ⟨Q, a, c, hQ, hmin⟩ := Y.data.exists_isReturningPath_minimal hret
  have hZ := Y.isTripleDiagram
  have hN := two_le_length_arcCutList_of_isReturningPath hQ
  have hm : 2 ≤ Y.data.arcLength i := by have := hQ.lt_left; rw [length_arc] at this; omega
  have hst := hasStraighteningProperty_arcCut hX ih hXY hSY ζ hN hm
  obtain ⟨Z, hZ', hmove, -, -, -, -, -, hSZ, harc, -, Q'', hhug, -, -⟩ :=
    hSY.exists_moveEquivalent_hugs hZ ζ hN hst hQ hmin
  have hXZ : X.MoveEquivalent ⟨Y.Dart, Z, hZ'⟩ := hXY.trans hmove
  have hhug' : Z.Hugs (Z.arc i) ζ Q'' a c := by rwa [harc]
  rcases lt_trichotomy a c with hac | rfl | hca
  · exact absurd (hhug'.isReturningPath.hasParallelDigon hZ'.toIsPreTripleDiagram hac)
      (hX.not_hasParallelDigon ih hXZ)
  · exact absurd (hasMonogon_of_isReturningPath_self hZ'.toIsPreTripleDiagram
      hhug'.isReturningPath) (hX _ hXZ)
  · obtain ⟨R, hR, -⟩ := hhug'.exists_closedAlignedRail hZ'.toIsPreTripleDiagram hca
    obtain ⟨hW, hmvW⟩ := TripleDiagram.exists_moveEquivalent_pushOff ⟨Y.Dart, Z, hZ'⟩ R
    obtain ⟨hSW, hlenW⟩ :=
      pushOff_arc hZ'.toIsPreTripleDiagram R (hSZ.isSimpleStrandPath hZ') hR
    have hlenZ : Z.arcLength i = Y.data.arcLength i := by
      have := congrArg List.length harc
      rwa [length_arc, length_arc] at this
    exact ihn (R.pushOff.arcLength i) (by omega) ⟨Y.Dart, R.pushOff, hW⟩ (hXZ.trans hmvW) hSW
      rfl

/-- **Straightening, Step 2: combing**. Let `X` be monogon-stable, and suppose that every
monogon-stable triple diagram with fewer triple points than `X` has the straightening property.
Let `I` be a minimal interval of `i` with side `ζ`, and suppose the arc `S` from `s_i` is simple
and has no returning path on side `ζ`. Then some `X' ∼ X` has its arc from `s_i` boundary-parallel
along `I`. -/
@[cluster_algebras "lem_straighten_step_two"]
theorem IsMonogonStable.exists_moveEquivalent_isBoundaryParallel {X : TripleDiagram b}
    (hX : X.IsMonogonStable)
    (ih : ∀ (b' : ℕ) (Y : TripleDiagram b'), Y.IsMonogonStable →
      Y.data.internalVertices.card < X.data.internalVertices.card → Y.HasStraighteningProperty)
    {i : Fin b} {I : Finset (Fin (2 * b))} (hI : X.IsMinimalInterval i I) {ζ : StrandSide}
    (hζ : intervalSide X.data.strandPerm i I = ζ) (hS : X.data.IsSimpleArc i)
    (hret : ∀ Q a c, ¬X.data.IsReturningPath (X.data.arc i) ζ Q a c) :
    ∃ X' : TripleDiagram b, X.MoveEquivalent X' ∧ X'.data.IsBoundaryParallel i I := by
  classical
  have hp := X.isTripleDiagram.toIsPreTripleDiagram
  obtain ⟨k, hk⟩ : ∃ k, (intervalInterior X.data.strandPerm i I).card = 2 * k := by
    obtain ⟨r, hr⟩ := hI.1.even_card_intervalInterior
    exact ⟨r, by omega⟩
  have hcard := hI.1.card_intervalInterior_eq (X := X.data)
  rw [hζ] at hcard
  have hNlen : (X.data.arcCutList i ζ).length = 2 * k + 2 * (X.data.arcLength i - 1) := by
    rw [arcCutList_eq_append, List.length_append, List.length_map, List.length_range,
      length_sideList_arc]
    omega
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- no interior position: the arc has no triple point
    have hm : X.data.arcLength i - 1 = 0 := by
      by_contra hm
      have hN : 2 ≤ (X.data.arcCutList i ζ).length := by omega
      have := hS.two_mul_ncard_passesThrough_of_isMinimalInterval X.isTripleDiagram hI hζ hN hret
      rw [hS.ncard_passesThrough X.isTripleDiagram] at this
      omega
    refine ⟨X, MoveEquivalent.refl X, hI.1, hS, ?_, fun r hr => ?_⟩
    · rw [hS.ncard_passesThrough X.isTripleDiagram, hm, hk]
    · rw [Finset.card_eq_zero.1 (by omega : (intervalInterior X.data.strandPerm i I).card = 0)]
        at hr
      exact absurd hr (Finset.notMem_empty r)
  -- the legs `g₀, …, g_{t-1}` already run to `S`, with `t` maximal
  let P : ℕ → Prop := fun t => ∃ Y : TripleDiagram b, X.MoveEquivalent Y ∧
    Y.data.IsSimpleArc i ∧ (∀ Q a c, ¬Y.data.IsReturningPath (Y.data.arc i) ζ Q a c) ∧
    ∀ t' < t, ∀ g ∈ (Y.data.arcCutList i ζ)[t']?, Y.data.inv g ∈ Y.data.sideList ζ (Y.data.arc i)
  have hP0 : P 0 := ⟨X, MoveEquivalent.refl X, hS, hret, fun t' h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨tm, htm⟩ : ∃ tm, tm = Nat.findGreatest P (2 * k) := ⟨_, rfl⟩
  have hPt : P tm := htm ▸ Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hle : tm ≤ 2 * k := htm ▸ Nat.findGreatest_le _
  have hmax : ∀ t, tm < t → t ≤ 2 * k → ¬P t := fun t h1 h2 =>
    Nat.findGreatest_is_greatest (htm ▸ h1) h2
  obtain ⟨Y, hXY, hSY, hretY, hlegs⟩ := hPt
  have hY := Y.isTripleDiagram
  have hπ : Y.data.strandPerm = X.data.strandPerm := hXY.strandPerm_eq
  have hIY : ClusterAlgebras.IsMinimalInterval Y.data.strandPerm i I := by rwa [hπ]
  have hζY : intervalSide Y.data.strandPerm i I = ζ := by rwa [hπ]
  have hkY : (intervalInterior Y.data.strandPerm i I).card = 2 * k := by rwa [hπ]
  have hYms : TripleDiagram.IsMonogonStable ⟨Y.Dart, Y.data, hY⟩ :=
    fun W hW => hX W (hXY.trans hW)
  rcases Nat.lt_or_ge tm (2 * k) with htk | htk
  · -- a further leg can be combed onto `S`: contradiction with the maximality of `tm`
    exfalso
    have hgt : ∀ g ∈ (Y.data.arcCutList i ζ)[tm]?,
        Y.data.inv g ∉ Y.data.sideList ζ (Y.data.arc i) := by
      intro g hg hmem
      refine hmax (tm + 1) (by omega) (by omega) ⟨Y, hXY, hSY, hretY, fun t' ht' g' hg' => ?_⟩
      obtain h | rfl : t' < tm ∨ t' = tm := by omega
      · exact hlegs t' h g' hg'
      · rwa [Option.mem_unique hg' hg]
    have ihY : ∀ (b' : ℕ) (W : TripleDiagram b'), W.IsMonogonStable →
        W.data.internalVertices.card < Y.data.internalVertices.card →
          W.HasStraighteningProperty := fun b' W hW hlt =>
      ih b' W hW (hXY.card_internalVertices_eq ▸ hlt)
    obtain ⟨X'', hX'', hmv, hS'', hret'', hlegs''⟩ :
        ∃ (X'' : TripleData Y.Dart b) (hX'' : X''.IsTripleDiagram),
          TripleDiagram.MoveEquivalent ⟨Y.Dart, Y.data, hY⟩ ⟨Y.Dart, X'', hX''⟩ ∧
          X''.IsSimpleArc i ∧ (∀ Q a c, ¬X''.IsReturningPath (X''.arc i) ζ Q a c) ∧
          ∀ t' < tm + 1, ∀ g ∈ (X''.arcCutList i ζ)[t']?,
            X''.inv g ∈ X''.sideList ζ (X''.arc i) := by
      rcases Nat.eq_zero_or_pos tm with rfl | h0
      · exact step_two_zero hY hYms ihY hIY hζY hk1 hkY hSY hretY hgt
      · exact step_two_succ hY hYms ihY hIY hζY hkY hSY hretY h0 htk hlegs hgt
    exact hmax (tm + 1) (by omega) (by omega)
      ⟨⟨Y.Dart, X'', hX''⟩, hXY.trans hmv, hS'', hret'', hlegs''⟩
  · -- every leg runs to `S`: the arc from `s_i` is boundary-parallel along `I`
    have hm : 2 ≤ (Y.data.arcCutList i ζ).length := by
      rw [arcCutList_eq_append, List.length_append, List.length_map, List.length_range]
      have := hIY.1.card_intervalInterior_eq (X := Y.data)
      rw [hζY] at this
      omega
    refine ⟨Y, hXY, hIY.1, hSY,
      hSY.two_mul_ncard_passesThrough_of_isMinimalInterval hY hIY hζY hm hretY, fun r hr => ?_⟩
    have hcardY := hIY.1.card_intervalInterior_eq (X := Y.data)
    rw [hζY] at hcardY
    have hr' := (hIY.1.mem_intervalInterior_iff (X := Y.data)).1 hr
    rw [hζY] at hr'
    obtain ⟨t₀, ht₀, rfl⟩ := hr'
    have hg := getElem?_arcCutList_of_lt (X := Y.data) (i := i) ζ ht₀
    exact passesThrough_of_mem_sideList_arc hY (hlegs t₀ (by omega) _ hg)

/-- **Straightening**. Every monogon-stable triple diagram has the straightening property. -/
@[cluster_algebras "lem_straighten"]
theorem IsMonogonStable.hasStraighteningProperty {X : TripleDiagram b}
    (hX : X.IsMonogonStable) : X.HasStraighteningProperty := by
  suffices h : ∀ n (b : ℕ) (X : TripleDiagram b), X.data.internalVertices.card = n →
      X.IsMonogonStable → X.HasStraighteningProperty from h _ b X rfl hX
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro b X hn hX
  have ih : ∀ (b' : ℕ) (Y : TripleDiagram b'), Y.IsMonogonStable →
      Y.data.internalVertices.card < X.data.internalVertices.card →
        Y.HasStraighteningProperty := fun b' Y hY hlt => ihn _ (hn ▸ hlt) b' Y rfl hY
  refine ⟨fun X' h => hX.not_hasParallelDigon ih h, fun i I hI => ?_⟩
  have hS : X.data.IsSimpleArc i := isSimpleArc_of_nodup
    (X.data.nodup_interiorPoints_arc X.isTripleDiagram.toIsPreTripleDiagram
      (hX X (MoveEquivalent.refl X)) i)
  obtain ⟨X', hXX', hS', hret'⟩ :=
    hX.exists_moveEquivalent_forall_not_isReturningPath ih (intervalSide X.data.strandPerm i I) hS
  have hπ : X'.data.strandPerm = X.data.strandPerm := hXX'.strandPerm_eq
  have hX' : X'.IsMonogonStable := fun W hW => hX W (hXX'.trans hW)
  have ih' : ∀ (b' : ℕ) (Y : TripleDiagram b'), Y.IsMonogonStable →
      Y.data.internalVertices.card < X'.data.internalVertices.card →
        Y.HasStraighteningProperty := fun b' Y hY hlt =>
    ih b' Y hY (hXX'.card_internalVertices_eq ▸ hlt)
  obtain ⟨X'', h, hbp⟩ := hX'.exists_moveEquivalent_isBoundaryParallel ih'
    (hXX'.isMinimalInterval_iff.2 hI) (by rw [hπ]) hS' hret'
  exact ⟨X'', hXX'.trans h, hbp⟩

end TripleDiagram

end ClusterAlgebras

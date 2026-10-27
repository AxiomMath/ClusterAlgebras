/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.RailPaths

/-!
# A hugging parallel returning path gives a staggered rail

Let `P = (e₁, …, e_m)` be a simple strand path of a triple diagram and `Q = (f₁, …, f_n)` a
parallel returning path of `P` on the side `ζ`, from the interior point `z_{a+1}` to the interior
point `z_{c+1}` with `a < c`, that hugs `P`. Then `n = c - a + 1`, and the points
`z_{a+1}, …, z_{c+1}` of `P` together with the interior points of `Q` are the points of a staggered
rail of length `n - 1`. On the right side its named darts are `ρ_{j,0} = ē_{a+j+1}` and
`η_{j,0} = f̄_j`; on the left side the points are read backwards, with `ρ_{j,0} = e_{c-j+2}` and
`η_{j,0} = f_{n-j+1}`. In both cases the rail closes up with `η̄_{n-1,3} = ρ_{n-1,2}`.

## Main results

* `ClusterAlgebras.TripleData.Hugs.exists_staggeredRail`: a hugging parallel returning path gives
  a staggered rail.

## Implementation notes

* Positions in lists are `0`-indexed, as in `ClusterAlgebras.Plabic.MinimalTriple`: the
  interior point `z_{l+1}` of a strand path `P` is `v(P[l]̄)`, and `Q[j]` is `f_{j+1}`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset RailLabel

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

/-! ### Entries of the side lists -/

/-- Entries of a list built from blocks of length two. -/
private theorem getElem?_flatMap_two {α β : Type*} (f : α → List β)
    (hf : ∀ x, (f x).length = 2) :
    ∀ (L : List α) (u j : ℕ), j < 2 → (L.flatMap f)[2 * u + j]? = L[u]?.bind fun x => (f x)[j]?
  | [], u, j, _ => by simp
  | x :: L, 0, j, hj => by
    rw [List.flatMap_cons, List.getElem?_append_left (by rw [hf]; omega)]
    simp
  | x :: L, u + 1, j, hj => by
    rw [List.flatMap_cons, List.getElem?_append_right (by rw [hf]; omega), hf,
      show 2 * (u + 1) + j - 2 = 2 * u + j by omega, getElem?_flatMap_two f hf L u j hj]
    simp

omit [Fintype H] [DecidableEq H] in
private theorem length_flatMap_two {α β : Type*} (f : α → List β) (hf : ∀ x, (f x).length = 2) :
    ∀ L : List α, (L.flatMap f).length = 2 * L.length
  | [] => by simp
  | x :: L => by
    rw [List.flatMap_cons, List.length_append, hf, length_flatMap_two f hf L, List.length_cons]
    ring

omit [Fintype H] [DecidableEq H] in
/-- The `ζ` list of `(e₁, …, e_m)` has `2(m - 1)` entries. -/
private theorem length_sideList (ζ : StrandSide) (P : List H) :
    (X.sideList ζ P).length = 2 * (P.length - 1) := by
  cases ζ <;>
  · simp only [sideList]
    rw [length_flatMap_two _ (fun x => by simp [sideDarts])]
    simp

omit [Fintype H] [DecidableEq H] in
/-- The entries of the right list: `λ_{2u+k} = σ^{k+1}(ē_{u+1})` (`0`-indexed `P[u]`). -/
private theorem getElem?_sideList_right {P : List H} {u k : ℕ} (hk : k < 2)
    (hu : u + 2 ≤ P.length) :
    (X.sideList .right P)[2 * u + k]? = some ((X.rot ^ (k + 1)) (X.inv (P[u]'(by omega)))) := by
  simp only [sideList]
  rw [getElem?_flatMap_two _ (fun x => by simp [sideDarts]) _ u k hk,
    List.getElem?_eq_getElem (by simp; omega), List.getElem_dropLast]
  interval_cases k <;> simp [sideDarts, pow_two]

omit [Fintype H] [DecidableEq H] in
/-- The entries of the left list: `λ_{2u+k} = σ^{k+4}(ē_{m-1-u})` (`0`-indexed
`P[m - 2 - u]`). -/
private theorem getElem?_sideList_left {P : List H} {u k : ℕ} (hk : k < 2) (hu : u + 2 ≤ P.length) :
    (X.sideList .left P)[2 * u + k]? =
      some ((X.rot ^ (k + 4)) (X.inv (P[P.length - 2 - u]'(by omega)))) := by
  simp only [sideList]
  have e : P.dropLast.reverse[u]? = some (P[P.length - 2 - u]'(by omega)) := by
    rw [List.getElem?_reverse (by simp; omega)]
    simp only [List.length_dropLast, List.getElem?_dropLast]
    rw [if_pos (by omega), show P.length - 1 - 1 - u = P.length - 2 - u by omega,
      List.getElem?_eq_getElem (by omega)]
  rw [getElem?_flatMap_two _ (fun x => by simp [sideDarts]) _ u k hk, e]
  interval_cases k <;> simp [sideDarts]

/-! ### Strand paths -/

/-- In a strand path, `σ³(ē_l) = e_{l+1}` (`0`-indexed). -/
private theorem rot_pow_three_inv_getElem {P : List H} (hP : X.IsStrandPath P) {l : ℕ}
    (hl : l + 1 < P.length) : (X.rot ^ 3) (X.inv P[l]) = P[l + 1] :=
  (((X.isStrandPath_iff_getElem.1 hP).2.2 l hl).2).symm

/-! ### Lists -/

omit [Fintype H] [DecidableEq H] in
private theorem getElem_idx {α : Type*} (l : List α) {i j : ℕ} (h : i = j) (hi : i < l.length) :
    l[i] = l[j]'(h ▸ hi) := by
  subst h
  rfl

omit [Fintype H] [DecidableEq H] in
private theorem getElem_mem_dropLast {α : Type*} {l : List α} {i : ℕ} (hi : i + 1 < l.length) :
    l[i] ∈ l.dropLast := by
  rw [← List.getElem_dropLast (by simp; omega)]
  exact List.getElem_mem _

omit [Fintype H] in
private theorem idxOf_eq_of_getElem?_eq_some {l : List H} (hl : l.Nodup) {i : ℕ} {x : H}
    (h : l[i]? = some x) : l.idxOf x = i := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact hl.idxOf_getElem i hi

/-! ### Interior points, side lists and rail points -/

/-- Two interior points of a strand path with pairwise distinct interior points coincide only
at the same index. -/
private theorem eq_of_nodup_interiorPoints {P : List H} (hnd : (X.interiorPoints P).Nodup)
    {l l' : ℕ} (hl : l + 1 < P.length) (hl' : l' + 1 < P.length)
    (h : X.vertexOf (X.inv P[l]) = X.vertexOf (X.inv P[l'])) : l = l' := by
  simp only [interiorPoints] at hnd
  have e1 : (P.dropLast.map fun e => X.vertexOf (X.inv e))[l]'(by simp; omega) =
      X.vertexOf (X.inv P[l]) := by simp
  have e2 : (P.dropLast.map fun e => X.vertexOf (X.inv e))[l']'(by simp; omega) =
      X.vertexOf (X.inv P[l']) := by simp
  exact (hnd.getElem_inj_iff).1 (by rw [e1, e2, h])

private theorem vertexOf_inv_getElem_mem_interiorPoints {P : List H} {k : ℕ}
    (hk : k + 1 < P.length) : X.vertexOf (X.inv P[k]) ∈ X.interiorPoints P :=
  List.mem_map.2 ⟨P[k], getElem_mem_dropLast hk, rfl⟩

/-- The reverse of a dart of a strand path points inwards. -/
private theorem isOut_inv_getElem (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsStrandPath P) (k : ℕ) (hk : k < P.length) : X.isOut (X.inv P[k]) = false := by
  have hPg := X.isStrandPath_iff_getElem.1 hP
  rw [hX.isOut_inv_apply (hPg.2.1 k hk).1, (hPg.2.1 k hk).2]
  rfl

/-- The `ζ` list of a simple strand path has no repeated entry. -/
private theorem nodup_sideList (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsSimpleStrandPath P) (ζ : StrandSide) : (X.sideList ζ P).Nodup := by
  have hPg := X.isStrandPath_iff_getElem.1 hP.isStrandPath
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hj
  rw [length_sideList] at hj
  have key : ∀ (e : ℕ) (u u' k k' : ℕ) (hk : k < 2) (hk' : k' < 2) (pos : ℕ → ℕ)
      (hpos : ∀ u, u + 2 ≤ P.length → pos u + 1 < P.length)
      (hposinj : ∀ u u', u + 2 ≤ P.length → u' + 2 ≤ P.length → pos u = pos u' → u = u')
      (he : e + 1 < 6) (hu : u + 2 ≤ P.length) (hu' : u' + 2 ≤ P.length),
      (X.rot ^ (k + e)) (X.inv (P[pos u]'(by have := hpos u hu; omega))) =
        (X.rot ^ (k' + e)) (X.inv (P[pos u']'(by have := hpos u' hu'; omega))) →
        u = u' ∧ k = k' := by
    intro e u u' k k' hk hk' pos hpos hposinj he hu hu' h
    have hv := congrArg X.vertexOf h
    rw [X.vertexOf_rot_pow_apply, X.vertexOf_rot_pow_apply] at hv
    obtain rfl :=
      hposinj u u' hu hu' (eq_of_nodup_interiorPoints hP.nodup (hpos u hu) (hpos u' hu') hv)
    refine ⟨rfl, ?_⟩
    have := (hX.rot_pow_six (hPg.2.2 (pos u) (hpos u hu)).1).2 _ _ (by omega) (by omega) h
    omega
  obtain ⟨u, k, hk, rfl⟩ : ∃ u k, k < 2 ∧ i = 2 * u + k := ⟨i / 2, i % 2, by omega, by omega⟩
  obtain ⟨u', k', hk', rfl⟩ : ∃ u k, k < 2 ∧ j = 2 * u + k := ⟨j / 2, j % 2, by omega, by omega⟩
  cases ζ with
  | right =>
    rw [getElem?_sideList_right hk (by omega), getElem?_sideList_right hk' (by omega), ne_eq,
      Option.some_inj]
    intro h
    have := key 1 u u' k k' hk hk' id (fun u hu => by simp; omega) (fun u u' _ _ h => h)
      (by norm_num) (by omega) (by omega) h
    omega
  | left =>
    rw [getElem?_sideList_left hk (by omega), getElem?_sideList_left hk' (by omega), ne_eq,
      Option.some_inj]
    intro h
    have := key 4 u u' k k' hk hk' (fun u => P.length - 2 - u) (fun u hu => by omega)
      (fun u u' hu hu' h => by omega) (by norm_num) (by omega) (by omega) h
    omega

omit [Fintype H] [DecidableEq H] in
private theorem railDart_rho (rho eta : ℕ → H) (j k : ℕ) :
    X.railDart rho eta (RailLabel.rho j k) = (X.rot ^ k) (rho j) :=
  rfl

omit [Fintype H] [DecidableEq H] in
private theorem railDart_eta (rho eta : ℕ → H) (j k : ℕ) :
    X.railDart rho eta (RailLabel.eta j k) = (X.rot ^ k) (eta j) :=
  rfl

omit [Fintype H] [DecidableEq H] in
private theorem rot_zpow_neg_one_eq {d : H} (h : (X.rot ^ 6) d = d) :
    (X.rot ^ (-1 : ℤ)) d = (X.rot ^ 5) d := by
  rw [zpow_neg_one, Equiv.Perm.inv_eq_iff_eq, ← Equiv.Perm.mul_apply, ← pow_succ']
  exact h.symm

omit [Fintype H] [DecidableEq H] in
private theorem rot_zpow_neg_two_eq {d : H} (h : (X.rot ^ 6) d = d) :
    (X.rot ^ (2 * -1 : ℤ)) d = (X.rot ^ 4) d := by
  rw [show (2 * -1 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
    Equiv.Perm.inv_eq_iff_eq, ← Equiv.Perm.mul_apply, ← pow_add]
  exact h.symm

/-- Rail points from interior points of a strand path and of a returning path of it. -/
private theorem railPoints_of_returning {P Q : List H} {ζ : StrandSide} {a b : ℕ}
    (hQ : X.IsReturningPath P ζ Q a b) (hQnd : (X.interiorPoints Q).Nodup) {N M : ℕ}
    {rho eta : ℕ → H} {px py : ℕ → ℕ}
    (hpx : ∀ j ≤ N, ∃ h : px j + 1 < P.length,
      X.vertexOf (rho j) = X.vertexOf (X.inv P[px j]))
    (hpxinj : ∀ j ≤ N, ∀ j' ≤ N, px j = px j' → j = j')
    (hpy : ∀ i, 1 ≤ i → i ≤ M → ∃ h : py i + 1 < Q.length,
      X.vertexOf (eta i) = X.vertexOf (X.inv Q[py i]))
    (hpyinj : ∀ i i', 1 ≤ i → i ≤ M → 1 ≤ i' → i' ≤ M → py i = py i' → i = i') :
    (∀ c ∈ pointSet N M, X.vertexOf (Sum.elim rho eta c) ∈ X.internalVertices) ∧
      Set.InjOn (fun c => X.vertexOf (Sum.elim rho eta c)) (pointSet N M) ∧
      ∀ i, 1 ≤ i → i ≤ M → ∀ e ∈ P,
        X.vertexOf (eta i) ≠ X.vertexOf e ∧ X.vertexOf (eta i) ≠ X.vertexOf (X.inv e) := by
  have hPg := X.isStrandPath_iff_getElem.1 hQ.isSimpleStrandPath.isStrandPath
  have hQg := X.isStrandPath_iff_getElem.1 hQ.isStrandPath
  have hy : ∀ i, 1 ≤ i → i ≤ M → ∀ e ∈ P,
      X.vertexOf (eta i) ≠ X.vertexOf e ∧ X.vertexOf (eta i) ≠ X.vertexOf (X.inv e) := by
    intro i h1 h2 e he
    obtain ⟨hk, hv⟩ := hpy i h1 h2
    rw [hv]
    exact hQ.interiorPoints_ne _ (vertexOf_inv_getElem_mem_interiorPoints hk) e he
  refine ⟨?_, ?_, hy⟩
  · rintro (j | i) hc
    · obtain ⟨hk, hv⟩ := hpx j (by simpa [pointSet] using hc)
      simp only [Sum.elim_inl, hv]
      exact X.vertexOf_mem_internalVertices.2 (hPg.2.2 _ hk).1
    · obtain ⟨h1, h2⟩ : 1 ≤ i ∧ i ≤ M := by simpa [pointSet] using hc
      obtain ⟨hk, hv⟩ := hpy i h1 h2
      simp only [Sum.elim_inr, hv]
      exact X.vertexOf_mem_internalVertices.2 (hQg.2.2 _ hk).1
  · rintro (j | i) hc (j' | i') hc' h
    · obtain ⟨hk, hv⟩ := hpx j (by simpa [pointSet] using hc)
      obtain ⟨hk', hv'⟩ := hpx j' (by simpa [pointSet] using hc')
      simp only [Sum.elim_inl, hv, hv'] at h
      rw [hpxinj j (by simpa [pointSet] using hc) j' (by simpa [pointSet] using hc')
        (eq_of_nodup_interiorPoints hQ.isSimpleStrandPath.nodup hk hk' h)]
    · obtain ⟨hk, hv⟩ := hpx j (by simpa [pointSet] using hc)
      obtain ⟨h1, h2⟩ : 1 ≤ i' ∧ i' ≤ M := by simpa [pointSet] using hc'
      simp only [Sum.elim_inl, Sum.elim_inr] at h
      exact absurd (h.symm.trans hv) (hy i' h1 h2 _ (List.getElem_mem _)).2
    · obtain ⟨hk, hv⟩ := hpx j' (by simpa [pointSet] using hc')
      obtain ⟨h1, h2⟩ : 1 ≤ i ∧ i ≤ M := by simpa [pointSet] using hc
      simp only [Sum.elim_inl, Sum.elim_inr] at h
      exact absurd (h.trans hv) (hy i h1 h2 _ (List.getElem_mem _)).2
    · obtain ⟨h1, h2⟩ : 1 ≤ i ∧ i ≤ M := by simpa [pointSet] using hc
      obtain ⟨h1', h2'⟩ : 1 ≤ i' ∧ i' ≤ M := by simpa [pointSet] using hc'
      obtain ⟨hk, hv⟩ := hpy i h1 h2
      obtain ⟨hk', hv'⟩ := hpy i' h1' h2'
      simp only [Sum.elim_inr, hv, hv'] at h
      rw [hpyinj i i' h1 h2 h1' h2' (eq_of_nodup_interiorPoints hQnd hk hk' h)]

/-! ### A hugging parallel returning path gives a staggered rail -/

/-- The first dart `f₁` of a returning path `Q` of `P` from `z_{a+1}` to `z_{c+1}` is an outgoing
`ζ` dart of `P` at `z_{a+1}`, and `f̄_n` is an incoming `ζ` dart of `P` at `z_{c+1}`. -/
private theorem IsReturningPath.exists_endpoints (hX : X.IsPreTripleDiagram) {P Q : List H}
    {ζ : StrandSide} {a c : ℕ} (hR : X.IsReturningPath P ζ Q a c) :
    ∃ (hn : 0 < Q.length) (f₁ fₙ : H), Q.head? = some f₁ ∧ Q.getLast? = some fₙ ∧
      f₁ = Q[0] ∧ fₙ = Q[Q.length - 1] ∧
      f₁ ∈ X.sideDarts ζ (P[a]'(by have := hR.lt_left; omega)) ∧
      X.inv fₙ ∈ X.sideDarts ζ (P[c]'(by have := hR.lt_right; omega)) ∧
      X.isOut f₁ = true ∧ X.isOut (X.inv fₙ) = false := by
  have hQne := hR.isStrandPath.ne_nil
  have hn : 0 < Q.length := List.length_pos_iff.2 hQne
  have ha := hR.lt_left
  have hc := hR.lt_right
  obtain ⟨f₁, hf₁⟩ : ∃ f, Q.head? = some f := ⟨_, List.head?_eq_some_head hQne⟩
  obtain ⟨fₙ, hfₙ⟩ : ∃ f, Q.getLast? = some f := ⟨_, List.getLast?_eq_some_getLast hQne⟩
  have hf₁0 : f₁ = Q[0] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hn] at hf₁
    exact (Option.some_inj.1 hf₁).symm
  have hfₙ0 : fₙ = Q[Q.length - 1] := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hfₙ
    exact (Option.some_inj.1 hfₙ).symm
  obtain ⟨e, he, f, hf, hfe⟩ := hR.head?_mem
  obtain ⟨e', he', f', hf', hfe'⟩ := hR.getLast?_mem
  rw [List.getElem?_eq_getElem (by omega), Option.mem_def, Option.some_inj] at he he'
  rw [Option.mem_def, hf₁, Option.some_inj] at hf
  rw [Option.mem_def, hfₙ, Option.some_inj] at hf'
  subst he he' hf hf'
  refine ⟨hn, f₁, fₙ, hf₁, hfₙ, hf₁0, hfₙ0, hfe, hfe', ?_, ?_⟩
  · rw [hf₁0]
    exact ((X.isStrandPath_iff_getElem.1 hR.isStrandPath).2.1 0 hn).2
  · rw [hfₙ0]
    exact isOut_inv_getElem hX hR.isStrandPath _ (by omega)

/-- A right side dart `f` at `e_{k+1}` is `σ ē_{k+1}` if it points outwards and `σ² ē_{k+1}` if
it points inwards. -/
private theorem eq_of_mem_sideDarts_right (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsStrandPath P) {k : ℕ} (hk : k + 1 < P.length) {f : H}
    (hf : f ∈ X.sideDarts .right P[k]) :
    (X.isOut f = true → f = X.rot (X.inv P[k])) ∧
      (X.isOut f = false → f = (X.rot ^ 2) (X.inv P[k])) := by
  have hb := ((X.isStrandPath_iff_getElem.1 hP).2.2 k hk).1
  have hin := isOut_inv_getElem hX hP k (by omega)
  simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · refine ⟨fun _ => rfl, fun h => ?_⟩
    rw [hX.isOut_rot_apply hb, hin] at h
    simp at h
  · refine ⟨fun h => ?_, fun _ => rfl⟩
    rw [hX.isOut_rot_pow_apply hb, hin] at h
    simp at h

/-- A left side dart `f` at `e_{k+1}` is `σ⁵ ē_{k+1}` if it points outwards and `σ⁴ ē_{k+1}` if
it points inwards. -/
private theorem eq_of_mem_sideDarts_left (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsStrandPath P) {k : ℕ} (hk : k + 1 < P.length) {f : H}
    (hf : f ∈ X.sideDarts .left P[k]) :
    (X.isOut f = true → f = (X.rot ^ 5) (X.inv P[k])) ∧
      (X.isOut f = false → f = (X.rot ^ 4) (X.inv P[k])) := by
  have hb := ((X.isStrandPath_iff_getElem.1 hP).2.2 k hk).1
  have hin := isOut_inv_getElem hX hP k (by omega)
  simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · refine ⟨fun h => ?_, fun _ => rfl⟩
    rw [hX.isOut_rot_pow_apply hb, hin] at h
    simp [show Even 4 by decide] at h
  · refine ⟨fun _ => rfl, fun h => ?_⟩
    rw [hX.isOut_rot_pow_apply hb, hin] at h
    simp [show ¬Even 5 by decide] at h

/-- A path `Q` hugging `P` on the right from `z_{a+1}` to `z_{c+1}` has length `c - a + 1`, runs
from `σ ē_{a+1}` to the reverse of `σ² ē_{c+1}`, and is glued to `P` through `σ⁵` and `σ⁴`. -/
private theorem Hugs.hug_right (hX : X.IsPreTripleDiagram) {P Q : List H} {a c : ℕ}
    (hQ : X.Hugs P .right Q a c) (hac : a < c) :
    ∃ (hn : Q.length = c - a + 1) (hc : c + 1 < P.length),
      Q[0] = X.rot (X.inv P[a]) ∧ X.inv Q[Q.length - 1] = (X.rot ^ 2) (X.inv P[c]) ∧
      (∀ t (ht : t < Q.length - 1),
        X.inv ((X.rot ^ 2) (X.inv P[a + t])) = (X.rot ^ 5) (X.inv Q[t])) ∧
      ∀ t (ht : t < Q.length - 1),
        X.inv (X.rot (X.inv P[a + t + 1])) = (X.rot ^ 4) (X.inv Q[t]) := by
  have hR := hQ.isReturningPath
  have hP := hR.isSimpleStrandPath
  have hQg := X.isStrandPath_iff_getElem.1 hR.isStrandPath
  have ha := hR.lt_left
  have hc := hR.lt_right
  obtain ⟨_, f₁, fₙ, hf₁, hfₙ, hf₁0, hfₙ0, hfe, hfe', hf₁out, hfₙin⟩ := hR.exists_endpoints hX
  have hf₁e := (eq_of_mem_sideDarts_right hX hP.isStrandPath ha hfe).1 hf₁out
  have hfₙe := (eq_of_mem_sideDarts_right hX hP.isStrandPath hc hfe').2 hfₙin
  have hhug := hQ.inv_hugDarts
  have hLl := length_sideList (X := X) .right P
  have hLnd := nodup_sideList hX hP .right
  have hLa : (X.sideList .right P)[2 * a]? = some f₁ := by
    rw [show 2 * a = 2 * a + 0 from rfl, getElem?_sideList_right (by norm_num) (by omega), hf₁e,
      zero_add, pow_one]
  have hLc : (X.sideList .right P)[2 * c + 1]? = some (X.inv fₙ) := by
    rw [getElem?_sideList_right (by norm_num) (by omega), hfₙe]
  have hJ : X.hugDarts P .right Q =
      ((X.sideList .right P).drop (2 * a + 1)).take (2 * c + 1 - 2 * a - 1) := by
    simp only [hugDarts, hf₁, hfₙ, idxOf_eq_of_getElem?_eq_some hLnd hLa,
      idxOf_eq_of_getElem?_eq_some hLnd hLc]
    rw [if_pos (by omega)]
  have hna : Q.length = c - a + 1 := by
    have hlen := hQ.length_hugDarts
    rw [hJ] at hlen
    simp only [List.length_drop, List.length_take, hLl] at hlen
    omega
  have hJk : ∀ k, k < 2 * (Q.length - 1) → (X.hugDarts P .right Q)[k]? =
      (X.sideList .right P)[2 * a + 1 + k]? := by
    intro k hk
    rw [hJ, List.getElem?_take, if_pos (by omega), List.getElem?_drop]
  have hexp : hugExponent .right a c = -1 := by
    simp [hugExponent, not_lt.2 hac.le]
  refine ⟨hna, hc, hf₁0.symm.trans hf₁e, (congrArg X.inv hfₙ0).symm.trans hfₙe,
    fun t ht => ?_, fun t ht => ?_⟩
  · have h := (hhug t ht).1
    rw [hJk _ (by omega), show 2 * a + 1 + 2 * t = 2 * (a + t) + 1 by omega,
      getElem?_sideList_right (by norm_num) (by omega), List.getElem?_eq_getElem (by omega),
      hexp] at h
    simp only [Option.map_some, Option.some_inj] at h
    rw [← rot_zpow_neg_one_eq (hX.rot_pow_six_apply (hQg.2.2 t (by omega)).1), ← h]
  · have h := (hhug t ht).2
    rw [hJk _ (by omega), show 2 * a + 1 + (2 * t + 1) = 2 * (a + t + 1) + 0 by omega,
      getElem?_sideList_right (by norm_num) (by omega), List.getElem?_eq_getElem (by omega),
      hexp] at h
    simp only [Option.map_some, Option.some_inj, zero_add, pow_one] at h
    rw [← rot_zpow_neg_two_eq (hX.rot_pow_six_apply (hQg.2.2 t (by omega)).1), ← h]

/-- A path `Q` hugging `P` on the right from `z_{a+1}` to `z_{c+1}` gives a staggered rail with
`ρ_{j,0} = ē_{a+j+1}` and `η_{i,0} = f̄_i`. -/
private theorem Hugs.exists_staggeredRail_right_darts (hX : X.IsPreTripleDiagram) {P Q : List H}
    {a c : ℕ} (hQ : X.Hugs P .right Q a c) (hac : a < c) :
    ∃ (hn : Q.length = c - a + 1) (hc : c + 1 < P.length) (R : X.StaggeredRail (Q.length - 1)),
      (∀ k (hk : k ≤ Q.length - 1), R.rho k = X.inv (P[a + k]'(by omega))) ∧
      ∀ i (h1 : 1 ≤ i) (h2 : i ≤ Q.length - 1), R.eta i = X.inv (Q[i - 1]'(by omega)) := by
  have hR := hQ.isReturningPath
  have hP := hR.isSimpleStrandPath
  obtain ⟨hna, hc, hQ0, _, hug1, hug2⟩ := hQ.hug_right hX hac
  obtain ⟨rho, hrho⟩ : ∃ rho : ℕ → H, ∀ k (hk : k ≤ Q.length - 1),
      rho k = X.inv (P[a + k]'(by omega)) :=
    ⟨fun k => X.inv ((P[a + k]?).getD Q[0]), fun k hk => by
      simp [List.getElem?_eq_getElem (show a + k < P.length by omega)]⟩
  obtain ⟨eta, heta⟩ : ∃ eta : ℕ → H, ∀ i (h1 : 1 ≤ i) (h2 : i ≤ Q.length - 1),
      eta i = X.inv (Q[i - 1]'(by omega)) :=
    ⟨fun i => X.inv ((Q[i - 1]?).getD Q[0]), fun i h1 h2 => by
      simp [List.getElem?_eq_getElem (show i - 1 < Q.length by omega)]⟩
  have hfacts := railPoints_of_returning hR hQ.nodup (N := Q.length - 1) (M := Q.length - 1)
    (rho := rho) (eta := eta) (px := fun j => a + j) (py := fun i => i - 1)
    (fun j hj => ⟨by omega, by rw [hrho j hj]⟩) (fun j _ j' _ h => by omega)
    (fun i h1 h2 => ⟨by omega, by rw [heta i h1 h2]⟩)
    (fun i i' _ _ _ _ h => by omega)
  refine ⟨hna, hc,
    { rho := rho
      eta := eta
      vertexOf_mem := hfacts.1
      injOn_vertexOf := hfacts.2.1
      one_le := by omega
      inv_rho_three := fun j hj => by
        rw [railDart_rho, railDart_rho, hrho j (by omega), hrho (j + 1) (by omega), pow_zero,
          Equiv.Perm.one_apply, rot_pow_three_inv_getElem hP.isStrandPath (l := a + j) (by omega)]
        rfl
      inv_rho_zero_one := by
        rw [railDart_rho, railDart_eta, hrho 0 (by omega), heta 1 le_rfl (by omega), pow_zero,
          Equiv.Perm.one_apply, pow_one, getElem_idx P (Nat.add_zero a), ← hQ0]
      inv_eta_three := fun j hj1 hj2 => by
        rw [railDart_eta, railDart_eta, heta j hj1 (by omega),
          heta (j + 1) (by omega) (by omega), pow_zero, Equiv.Perm.one_apply,
          rot_pow_three_inv_getElem hR.isStrandPath (by omega)]
        congr 1
        exact getElem_idx Q (by omega) _
      inv_rho_two := fun j hj1 hj2 => by
        rw [railDart_rho, railDart_eta, hrho (j - 1) (by omega), heta j hj1 hj2]
        exact hug1 (j - 1) (by omega)
      inv_rho_one := fun j hj1 hj2 => by
        rw [railDart_rho, railDart_eta, hrho j (by omega), heta j hj1 hj2, pow_one]
        have := hug2 (j - 1) (by omega)
        rw [getElem_idx P (show a + (j - 1) + 1 = a + j by omega)] at this
        exact this }, hrho, heta⟩

/-- `Hugs.exists_staggeredRail` on the right side. -/
private theorem Hugs.exists_staggeredRail_right (hX : X.IsPreTripleDiagram) {P Q : List H}
    {a c : ℕ} (hQ : X.Hugs P .right Q a c) (hac : a < c) :
    ∃ R : X.StaggeredRail (Q.length - 1),
      X.inv (R.dart (RailLabel.eta (Q.length - 1) 3)) = R.dart (RailLabel.rho (Q.length - 1) 2) ∧
      ∀ d ∈ R.darts, (∃ l, a ≤ l ∧ l ≤ c ∧ (X.interiorPoints P)[l]? = some (X.vertexOf d)) ∨
        X.vertexOf d ∈ X.interiorPoints Q := by
  have hR := hQ.isReturningPath
  obtain ⟨hna, hc, R, hrho, heta⟩ := hQ.exists_staggeredRail_right_darts hX hac
  obtain ⟨_, _, _, hQl, _, _⟩ := hQ.hug_right hX hac
  refine ⟨R, ?_, fun d hd => ?_⟩
  · change X.inv ((X.rot ^ 3) (R.eta (Q.length - 1))) = (X.rot ^ 2) (R.rho (Q.length - 1))
    rw [heta _ (by omega) le_rfl, hrho _ le_rfl,
      rot_pow_three_inv_getElem hR.isStrandPath (by omega),
      getElem_idx Q (show Q.length - 1 - 1 + 1 = Q.length - 1 by omega), hQl,
      getElem_idx P (show c = a + (Q.length - 1) by omega)]
  obtain ⟨j | i, hpt, hdm⟩ := R.toRailPoints.mem_darts.1 hd <;> rw [X.vertexOf_eq_of_mem hdm]
  · have hj : j ≤ Q.length - 1 := by simpa [pointSet] using hpt
    refine Or.inl ⟨a + j, by omega, by omega, ?_⟩
    rw [getElem?_interiorPoints (by omega)]
    simp only [Sum.elim_inl, hrho j hj]
  · obtain ⟨h1, h2⟩ : 1 ≤ i ∧ i ≤ Q.length - 1 := by simpa [pointSet] using hpt
    refine Or.inr ?_
    simp only [Sum.elim_inr, heta i h1 h2]
    exact vertexOf_inv_getElem_mem_interiorPoints (by omega)

/-- A path `Q` hugging `P` on the left from `z_{a+1}` to `z_{c+1}` has length `c - a + 1`, runs
from `σ⁵ ē_{a+1}` to the reverse of `σ⁴ ē_{c+1}`, and is glued to `P` through `σ` and `σ²`. -/
private theorem Hugs.hug_left (hX : X.IsPreTripleDiagram) {P Q : List H} {a c : ℕ}
    (hQ : X.Hugs P .left Q a c) (hac : a < c) :
    ∃ (hn : Q.length = c - a + 1) (hc : c + 1 < P.length),
      Q[0] = (X.rot ^ 5) (X.inv P[a]) ∧ X.inv Q[Q.length - 1] = (X.rot ^ 4) (X.inv P[c]) ∧
      (∀ t (ht : t < Q.length - 1),
        X.inv ((X.rot ^ 4) (X.inv P[a + t])) = X.rot (X.inv Q[t])) ∧
      ∀ t (ht : t < Q.length - 1),
        X.inv ((X.rot ^ 5) (X.inv P[a + t + 1])) = (X.rot ^ 2) (X.inv Q[t]) := by
  have hR := hQ.isReturningPath
  have hP := hR.isSimpleStrandPath
  have ha := hR.lt_left
  have hc := hR.lt_right
  obtain ⟨_, f₁, fₙ, hf₁, hfₙ, hf₁0, hfₙ0, hfe, hfe', hf₁out, hfₙin⟩ := hR.exists_endpoints hX
  have hf₁e := (eq_of_mem_sideDarts_left hX hP.isStrandPath ha hfe).1 hf₁out
  have hfₙe := (eq_of_mem_sideDarts_left hX hP.isStrandPath hc hfe').2 hfₙin
  have hhug := hQ.inv_hugDarts
  have hLl := length_sideList (X := X) .left P
  have hLnd := nodup_sideList hX hP .left
  have hLa : (X.sideList .left P)[2 * (P.length - 2 - a) + 1]? = some f₁ := by
    rw [getElem?_sideList_left (by norm_num) (by omega), hf₁e]
    congr 3
    exact getElem_idx P (by omega) _
  have hLc : (X.sideList .left P)[2 * (P.length - 2 - c)]? = some (X.inv fₙ) := by
    rw [show 2 * (P.length - 2 - c) = 2 * (P.length - 2 - c) + 0 from rfl,
      getElem?_sideList_left (by norm_num) (by omega), hfₙe]
    congr 3
    exact getElem_idx P (by omega) _
  have hJ : X.hugDarts P .left Q = (((X.sideList .left P).take
      (2 * (P.length - 2 - a) + 1)).drop (2 * (P.length - 2 - c) + 1)).reverse := by
    simp only [hugDarts, hf₁, hfₙ, idxOf_eq_of_getElem?_eq_some hLnd hLa,
      idxOf_eq_of_getElem?_eq_some hLnd hLc]
    rw [if_neg (by omega)]
  have hna : Q.length = c - a + 1 := by
    have hlen := hQ.length_hugDarts
    rw [hJ] at hlen
    simp only [List.length_reverse, List.length_drop, List.length_take, hLl] at hlen
    omega
  have hJk : ∀ k, k < 2 * (Q.length - 1) → (X.hugDarts P .left Q)[k]? =
      (X.sideList .left P)[2 * (P.length - 2 - a) - k]? := by
    intro k hk
    rw [hJ, List.getElem?_reverse (by simp [hLl]; omega)]
    simp only [List.length_drop, List.length_take, hLl, List.getElem?_drop, List.getElem?_take]
    rw [if_pos (by omega)]
    congr 1
    omega
  have hexp : hugExponent .left a c = 1 := by
    simp [hugExponent, not_lt.2 hac.le]
  refine ⟨hna, hc, hf₁0.symm.trans hf₁e, (congrArg X.inv hfₙ0).symm.trans hfₙe,
    fun t ht => ?_, fun t ht => ?_⟩
  · have h := (hhug t ht).1
    rw [hJk _ (by omega), show 2 * (P.length - 2 - a) - 2 * t =
        2 * (P.length - 2 - a - t) + 0 by omega,
      getElem?_sideList_left (by norm_num) (by omega), List.getElem?_eq_getElem (by omega),
      hexp] at h
    simp only [Option.map_some, Option.some_inj, zero_add, zpow_one] at h
    rw [← h]
    congr 3
    exact getElem_idx P (by omega) _
  · have h := (hhug t ht).2
    rw [hJk _ (by omega), show 2 * (P.length - 2 - a) - (2 * t + 1) =
        2 * (P.length - 2 - a - t - 1) + 1 by omega,
      getElem?_sideList_left (by norm_num) (by omega), List.getElem?_eq_getElem (by omega),
      hexp, show (2 : ℤ) * 1 = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
    simp only [Option.map_some, Option.some_inj] at h
    rw [← h]
    congr 3
    exact getElem_idx P (by omega) _

/-- At an interior vertex, powers of the rotation compose with exponents taken modulo `6`. -/
private theorem rot_pow_rot_pow_apply_mod_six (hX : X.IsPreTripleDiagram) {d : H}
    (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) (k k' : ℕ) :
    (X.rot ^ k) ((X.rot ^ k') d) = (X.rot ^ ((k + k') % 6)) d := by
  rw [← Equiv.Perm.mul_apply, ← pow_add, hX.rot_pow_mod_six hd]

/-- A path `Q` hugging `P` on the left from `z_{a+1}` to `z_{c+1}` gives a staggered rail with
`ρ_{j,0} = σ³ ē_{c-j+1}` and `η_{i,0} = σ³ f̄_{n-i}`. -/
private theorem Hugs.exists_staggeredRail_left_darts (hX : X.IsPreTripleDiagram) {P Q : List H}
    {a c : ℕ} (hQ : X.Hugs P .left Q a c) (hac : a < c) :
    ∃ (hn : Q.length = c - a + 1) (hc : c + 1 < P.length) (R : X.StaggeredRail (Q.length - 1)),
      (∀ k (hk : k ≤ Q.length - 1), R.rho k = (X.rot ^ 3) (X.inv (P[c - k]'(by omega)))) ∧
      ∀ i (h1 : 1 ≤ i) (h2 : i ≤ Q.length - 1),
        R.eta i = (X.rot ^ 3) (X.inv (Q[Q.length - 1 - i]'(by omega))) := by
  have hR := hQ.isReturningPath
  have hP := hR.isSimpleStrandPath
  obtain ⟨hna, hc, _, hQl, hug1, hug2⟩ := hQ.hug_left hX hac
  have hQtp : ∀ k (hk : k + 1 < Q.length), ¬X.IsBoundaryVertex (X.vertexOf (X.inv Q[k])) :=
    fun k hk => ((X.isStrandPath_iff_getElem.1 hR.isStrandPath).2.2 k hk).1
  have hPtp : ∀ k (hk : k + 1 < P.length), ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[k])) :=
    fun k hk => ((X.isStrandPath_iff_getElem.1 hP.isStrandPath).2.2 k hk).1
  obtain ⟨rho, hrho⟩ : ∃ rho : ℕ → H, ∀ k (hk : k ≤ Q.length - 1),
      rho k = P[c - k + 1]'(by omega) :=
    ⟨fun k => (P[c - k + 1]?).getD Q[0], fun k hk => by
      simp [List.getElem?_eq_getElem (show c - k + 1 < P.length by omega)]⟩
  have hrho3 : ∀ k (hk : k ≤ Q.length - 1),
      rho k = (X.rot ^ 3) (X.inv (P[c - k]'(by omega))) := fun k hk => by
    rw [hrho k hk, rot_pow_three_inv_getElem hP.isStrandPath (by omega)]
  obtain ⟨eta, heta⟩ : ∃ eta : ℕ → H, ∀ i (h1 : 1 ≤ i) (h2 : i ≤ Q.length - 1),
      eta i = Q[Q.length - i]'(by omega) :=
    ⟨fun i => (Q[Q.length - i]?).getD Q[0], fun i h1 h2 => by
      simp [List.getElem?_eq_getElem (show Q.length - i < Q.length by omega)]⟩
  have heta3 : ∀ i (h1 : 1 ≤ i) (h2 : i ≤ Q.length - 1),
      eta i = (X.rot ^ 3) (X.inv (Q[Q.length - 1 - i]'(by omega))) := fun i h1 h2 => by
    rw [heta i h1 h2, rot_pow_three_inv_getElem hR.isStrandPath (by omega)]
    exact getElem_idx Q (by omega) _
  have hfacts := railPoints_of_returning hR hQ.nodup (N := Q.length - 1) (M := Q.length - 1)
    (rho := rho) (eta := eta) (px := fun j => c - j) (py := fun i => Q.length - 1 - i)
    (fun j hj => ⟨by omega, by rw [hrho3 j hj, X.vertexOf_rot_pow_apply]⟩)
    (fun j _ j' _ h => by omega)
    (fun i h1 h2 => ⟨by omega, by rw [heta3 i h1 h2, X.vertexOf_rot_pow_apply]⟩)
    (fun i i' _ _ _ _ h => by omega)
  refine ⟨hna, hc,
    { rho := rho
      eta := eta
      vertexOf_mem := hfacts.1
      injOn_vertexOf := hfacts.2.1
      one_le := by omega
      inv_rho_three := fun j hj => by
        rw [railDart_rho, railDart_rho, hrho3 j (by omega),
          hX.rot_pow_three_rot_pow_three (hPtp _ (by omega)), hX.inv_inv_apply, pow_zero,
          Equiv.Perm.one_apply, hrho (j + 1) (by omega)]
        exact getElem_idx P (by omega) _
      inv_rho_zero_one := by
        rw [railDart_rho, railDart_eta, hrho3 0 (by omega),
          rot_pow_rot_pow_apply_mod_six hX (hPtp _ (by omega)), heta 1 le_rfl (by omega),
          pow_zero, Equiv.Perm.one_apply, show (1 + 3) % 6 = 4 from rfl,
          getElem_idx P (Nat.sub_zero c), ← hQl, hX.inv_inv_apply]
      inv_eta_three := fun j hj1 hj2 => by
        rw [railDart_eta, railDart_eta, heta3 j hj1 (by omega),
          hX.rot_pow_three_rot_pow_three (hQtp _ (by omega)), hX.inv_inv_apply,
          heta (j + 1) (by omega) (by omega), pow_zero, Equiv.Perm.one_apply]
        exact getElem_idx Q (by omega) _
      inv_rho_two := fun j hj1 hj2 => by
        rw [railDart_rho, railDart_eta, hrho3 (j - 1) (by omega), heta3 j hj1 hj2,
          rot_pow_rot_pow_apply_mod_six hX (hPtp _ (by omega)),
          rot_pow_rot_pow_apply_mod_six hX (hQtp _ (by omega)), show (2 + 3) % 6 = 5 from rfl,
          show (5 + 3) % 6 = 2 from rfl]
        have := hug2 (Q.length - 1 - j) (by omega)
        rw [getElem_idx P (show a + (Q.length - 1 - j) + 1 = c - (j - 1) by omega)] at this
        exact this
      inv_rho_one := fun j hj1 hj2 => by
        rw [railDart_rho, railDart_eta, hrho3 j (by omega), heta3 j hj1 hj2,
          rot_pow_rot_pow_apply_mod_six hX (hPtp _ (by omega)),
          rot_pow_rot_pow_apply_mod_six hX (hQtp _ (by omega)), show (1 + 3) % 6 = 4 from rfl,
          show (4 + 3) % 6 = 1 from rfl, pow_one]
        have := hug1 (Q.length - 1 - j) (by omega)
        rw [getElem_idx P (show a + (Q.length - 1 - j) = c - j by omega)] at this
        exact this }, hrho3, heta3⟩

/-- `Hugs.exists_staggeredRail` on the left side. -/
private theorem Hugs.exists_staggeredRail_left (hX : X.IsPreTripleDiagram) {P Q : List H}
    {a c : ℕ} (hQ : X.Hugs P .left Q a c) (hac : a < c) :
    ∃ R : X.StaggeredRail (Q.length - 1),
      X.inv (R.dart (RailLabel.eta (Q.length - 1) 3)) = R.dart (RailLabel.rho (Q.length - 1) 2) ∧
      ∀ d ∈ R.darts, (∃ l, a ≤ l ∧ l ≤ c ∧ (X.interiorPoints P)[l]? = some (X.vertexOf d)) ∨
        X.vertexOf d ∈ X.interiorPoints Q := by
  have hR := hQ.isReturningPath
  obtain ⟨hna, hc, R, hrho3, heta3⟩ := hQ.exists_staggeredRail_left_darts hX hac
  obtain ⟨_, _, hQ0, _, _, _⟩ := hQ.hug_left hX hac
  have hQtp : ∀ k (hk : k + 1 < Q.length), ¬X.IsBoundaryVertex (X.vertexOf (X.inv Q[k])) :=
    fun k hk => ((X.isStrandPath_iff_getElem.1 hR.isStrandPath).2.2 k hk).1
  have hPtp : ∀ k (hk : k + 1 < P.length), ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[k])) :=
    fun k hk => ((X.isStrandPath_iff_getElem.1 hR.isSimpleStrandPath.isStrandPath).2.2 k hk).1
  refine ⟨R, ?_, fun d hd => ?_⟩
  · change X.inv ((X.rot ^ 3) (R.eta (Q.length - 1))) = (X.rot ^ 2) (R.rho (Q.length - 1))
    rw [heta3 _ (by omega) le_rfl, hX.rot_pow_three_rot_pow_three (hQtp _ (by omega)),
      hX.inv_inv_apply, hrho3 _ le_rfl, rot_pow_rot_pow_apply_mod_six hX (hPtp _ (by omega)),
      show (2 + 3) % 6 = 5 from rfl,
      ← getElem_idx P (show a = c - (Q.length - 1) by omega) (by omega), ← hQ0]
    exact getElem_idx Q (by omega) _
  obtain ⟨j | i, hpt, hdm⟩ := R.toRailPoints.mem_darts.1 hd <;> rw [X.vertexOf_eq_of_mem hdm]
  · have hj : j ≤ Q.length - 1 := by simpa [pointSet] using hpt
    refine Or.inl ⟨c - j, by omega, by omega, ?_⟩
    rw [getElem?_interiorPoints (by omega)]
    simp only [Sum.elim_inl, hrho3 j hj, X.vertexOf_rot_pow_apply]
  · obtain ⟨h1, h2⟩ : 1 ≤ i ∧ i ≤ Q.length - 1 := by simpa [pointSet] using hpt
    refine Or.inr ?_
    simp only [Sum.elim_inr, heta3 i h1 h2, X.vertexOf_rot_pow_apply]
    exact vertexOf_inv_getElem_mem_interiorPoints (by omega)

/-- **A hugging parallel returning path gives a staggered rail.** Let `P` be a simple strand path
and `Q = (f₁, …, f_n)` a parallel returning path of `P` on side `ζ` from `z_{a+1}` to `z_{c+1}`
(`0`-indexed, `a < c`) that hugs `P`. Then `X` has a staggered rail of length `n - 1` whose
points are `z_{a+1}, …, z_{c+1}` and the interior points of `Q`, with `η̄_{n-1,3} = ρ_{n-1,2}`. -/
theorem Hugs.exists_staggeredRail (hX : X.IsPreTripleDiagram) {P Q : List H} {ζ : StrandSide}
    {a c : ℕ} (hQ : X.Hugs P ζ Q a c) (hac : a < c) :
    ∃ R : X.StaggeredRail (Q.length - 1),
      X.inv (R.dart (RailLabel.eta (Q.length - 1) 3)) = R.dart (RailLabel.rho (Q.length - 1) 2) ∧
      ∀ d ∈ R.darts, (∃ l, a ≤ l ∧ l ≤ c ∧ (X.interiorPoints P)[l]? = some (X.vertexOf d)) ∨
        X.vertexOf d ∈ X.interiorPoints Q := by
  cases ζ with
  | right => exact hQ.exists_staggeredRail_right hX hac
  | left => exact hQ.exists_staggeredRail_left hX hac

end TripleData

end ClusterAlgebras

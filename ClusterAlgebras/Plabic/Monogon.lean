/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.MinimalTriple
public import ClusterAlgebras.Plabic.Winding

/-!
# Convex monogons of triple diagrams

Let `X` be a triple diagram and `M = (e₁, …, e_m)` a monogon of `X` with vertex `x` that is a
simple strand path, with interior points `z_l = v(ē_l)`. Its *cycle* `c_M` is `1` on the darts
`e_l`, `-1` on their reverses and `0` elsewhere, and a *winding function* of `M` is a function `h`
on the orbits of `φ` with `h(f_∞) = 0` and `h(f(d̄)) - h(f(d)) = c_M(d)`. The monogon is a simple
closed walk, so it has exactly one winding function; it is constant, equal to `w`, to the right of
`M` and equal to `w + 1` to its left.

The monogon is *convex with inside right* if `σ(ē_m) = e₁` and `h(f(e₁)) ≠ 0`, and *convex with
inside left* if `σ(e₁) = ē_m` and `h(f(ē₁)) ≠ 0`: the corner at `x` contains no other dart on the
inside, and the inside is the side on which the winding function is nonzero. The *inside darts* are
the darts off `B` and off `M` on which `h` takes the inside value; at the triple points of `M` they
are the darts of the inside list, and globally they are everything reachable from the inside list
without crossing `M`. Conversely this reachability criterion detects convexity.

Every triple diagram with a monogon has a convex monogon: a monogon that is a simple strand path
and on which the set of orbits with nonzero winding value is smallest is convex, since otherwise
the strand leaving its corner on the inside gives a smaller one.

## Main definitions

* `ClusterAlgebras.TripleData.monogonCycle`, `ClusterAlgebras.TripleData.IsMonogonWindingFunction`:
  the cycle and the winding functions of a simple monogon.
* `ClusterAlgebras.TripleData.IsConvexMonogon`: convex monogons with inside `ζ`.
* `ClusterAlgebras.TripleData.insideDarts`, `ClusterAlgebras.TripleData.insideList`: the inside
  darts and the inside list of a convex monogon.
* `ClusterAlgebras.TripleData.avoidingClosure`: the smallest set of darts containing a given set
  and closed under the involution and under `σ^{±1}` at triple points off a strand path.

## Main results

* `ClusterAlgebras.TripleData.existsUnique_isMonogonWindingFunction` and
  `ClusterAlgebras.TripleData.IsMonogonWindingFunction.apply_getElem`,
  `ClusterAlgebras.TripleData.IsMonogonWindingFunction.apply_rot_pow_inv_getElem`: a simple monogon
  has a unique winding function, and its values near `M`.
* `ClusterAlgebras.TripleData.IsConvexMonogon.notMem_insideDarts_of_isBoundaryVertex` and the
  following lemmas: the local description of the inside.
* `ClusterAlgebras.TripleData.IsConvexMonogon.insideDarts_eq_avoidingClosure`: the inside by
  reachability.
* `ClusterAlgebras.TripleData.isConvexMonogon_of_avoidingClosure`: convexity by reachability.
* `ClusterAlgebras.TripleData.ssubset_of_split`: cutting a monogon along a strand inside it.
* `ClusterAlgebras.TripleData.exists_isConvexMonogon`: convex monogons exist.

## Implementation notes

* **Indices.** A monogon is a list `P` of darts, `0`-indexed: FWZ's `e_l` is `P[l - 1]`, its
  interior point `z_l` is `v(P[l - 1]̄)` for `l ∈ [1, m - 1]`, and `e₁ = P[0]`.
* **The cycle.** `monogonCycle P` is `1` on the darts of `P`, `-1` on their reverses and `0`
  elsewhere; for a simple monogon these sets are disjoint and it is the cycle of `P` read as a
  closed walk (`monogonCycle_eq_walkCycle`), so that the results on winding functions of simple
  closed walks apply. The closed walk of a list `L` is `L.get`.
* **The inside value.** The inside darts are defined relative to a winding function `h`, which is
  unique; the inside value `ω` is `h(f(e₁))` (inside right) or `h(f(ē₁))` (inside left), the value
  of `h` at `sideOrbit ζ e₁`.
* **Reachability.** The smallest set containing a set `S` of darts and closed under the involution
  and under `σ^{±1}` at triple points that are not vertices of darts of `M` is
  `avoidingClosure M S`, the intersection of all such sets (`isLeast_avoidingClosure`).
* **Cutting.** In the cutting lemma the strand `G = (g₀, …, g_j)` is a list, and FWZ's index
  `l ∈ [1, m - 1]` is kept: `z_l = v(P[l - 1]̄)` and `M' = (e_{l+1}, …, e_m, g₀, …, g_j)` is
  `P.drop l ++ G`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)

/-! ### Winding functions and convexity -/

/-- The **cycle** `c_M : H → ℤ` of a monogon `M = (e₁, …, e_m)`: `c_M(e_l) = 1`, `c_M(ē_l) = -1`
and `c_M = 0` elsewhere. -/
@[cluster_algebras "def_monogon_winding"]
def monogonCycle (P : List H) (d : H) : ℤ :=
  if d ∈ P then 1 else if X.inv d ∈ P then -1 else 0

/-- A **winding function** of a monogon `M`: a function `h : Φ → ℤ` with `h(f_∞) = 0` and
`h(f(d̄)) - h(f(d)) = c_M(d)` for every dart `d`. -/
@[cluster_algebras "def_monogon_winding"]
abbrev IsMonogonWindingFunction (P : List H) (h : X.faceOrbits → ℤ) : Prop :=
  X.IsWindingFunction (X.monogonCycle P) h

/-- The orbit on side `ζ` of a dart `e`: `f(e)` on the right and `f(ē)` on the left. -/
def sideOrbit : StrandSide → H → X.faceOrbits
  | .right, e => X.toFaceOrbit e
  | .left, e => X.toFaceOrbit (X.inv e)

/-- On the right, the side orbit of `e` is `f(e)`. -/
@[simp] theorem sideOrbit_right (e : H) : X.sideOrbit .right e = X.toFaceOrbit e := rfl

/-- On the left, the side orbit of `e` is `f(ē)`. -/
@[simp] theorem sideOrbit_left (e : H) : X.sideOrbit .left e = X.toFaceOrbit (X.inv e) := rfl

/-- The **corner condition** of a monogon with first dart `e₁` and last dart `e_m` and inside `ζ`:
`σ(ē_m) = e₁` on the right and `σ(e₁) = ē_m` on the left. -/
def IsInsideCorner : StrandSide → H → H → Prop
  | .right, e₁, eₘ => X.rot (X.inv eₘ) = e₁
  | .left, e₁, eₘ => X.rot e₁ = X.inv eₘ

omit [Fintype H] [DecidableEq H] in
/-- The corner condition with inside right is `σ(ē_m) = e₁`. -/
theorem isInsideCorner_right_iff {e₁ eₘ : H} :
    X.IsInsideCorner .right e₁ eₘ ↔ X.rot (X.inv eₘ) = e₁ := Iff.rfl

omit [Fintype H] [DecidableEq H] in
/-- The corner condition with inside left is `σ(e₁) = ē_m`. -/
theorem isInsideCorner_left_iff {e₁ eₘ : H} :
    X.IsInsideCorner .left e₁ eₘ ↔ X.rot e₁ = X.inv eₘ := Iff.rfl

/-- A monogon `M = (e₁, …, e_m)` is **convex with inside `ζ`**: it is a simple strand path,
`σ(ē_m) = e₁` (inside right) or `σ(e₁) = ē_m` (inside left), and some winding function `h` of `M`
has `h(f(e₁)) ≠ 0` (inside right) or `h(f(ē₁)) ≠ 0` (inside left). A monogon is *convex* if it is
convex with inside right or left. -/
@[cluster_algebras "def_convex_monogon"]
structure IsConvexMonogon (P : List H) (ζ : StrandSide) : Prop where
  /-- `M` is a monogon. -/
  isMonogon : X.IsMonogon P
  /-- `M` is a simple strand path. -/
  isSimpleStrandPath : X.IsSimpleStrandPath P
  /-- The corner condition at the vertex of `M`. -/
  isInsideCorner : ∀ e₁ ∈ P.head?, ∀ eₘ ∈ P.getLast?, X.IsInsideCorner ζ e₁ eₘ
  /-- Some winding function is nonzero on the inside of the first dart. -/
  exists_windingFunction : ∃ h, X.IsMonogonWindingFunction P h ∧
    ∀ e₁ ∈ P.head?, h (X.sideOrbit ζ e₁) ≠ 0

/-- The **inside darts** `H_in(M)` of a convex monogon `M = (e₁, …, e_m)` with inside `ζ` and
winding function `h`: the darts `d ∉ B` that are not `e_l` or `ē_l` and satisfy `h(f(d)) = ω`,
where `ω = h(f(e₁))` if `ζ` is right and `ω = h(f(ē₁))` if `ζ` is left. -/
@[cluster_algebras "def_monogon_inside"]
def insideDarts (P : List H) (ζ : StrandSide) (h : X.faceOrbits → ℤ) : Finset H :=
  {d | d ∉ X.bdry ∧ d ∉ P ∧ X.inv d ∉ P ∧
    ∀ e₁ ∈ P.head?, h (X.toFaceOrbit d) = h (X.sideOrbit ζ e₁)}

/-- The **inside list** of a convex monogon with inside `ζ`: its `ζ` list `(g₀, …, g_{N-1})`,
`N = 2(m - 1)`. -/
@[cluster_algebras "def_monogon_inside"]
abbrev insideList (ζ : StrandSide) (P : List H) : List H := X.sideList ζ P

/-- A set `S` of darts is **closed off `P`** if it is closed under the involution and under
`σ^{±1}` at triple points that are not vertices of darts of `P`. -/
def IsClosedOff (P : List H) (S : Set H) : Prop :=
  (∀ d ∈ S, X.inv d ∈ S) ∧ ∀ d ∈ S, ¬X.IsBoundaryVertex (X.vertexOf d) →
    (∀ e ∈ P, X.vertexOf d ≠ X.vertexOf e) → X.rot d ∈ S ∧ X.rot.symm d ∈ S

/-- The smallest set of darts containing `S` and closed under the involution and under `σ^{±1}` at
triple points that are not vertices of darts of `P`. -/
def avoidingClosure (P : List H) (S : Set H) : Set H :=
  ⋂₀ {T | S ⊆ T ∧ X.IsClosedOff P T}

/-- `avoidingClosure P S` is the least set of darts containing `S` and closed off `P`. -/
theorem isLeast_avoidingClosure (P : List H) (S : Set H) :
    IsLeast {T | S ⊆ T ∧ X.IsClosedOff P T} (X.avoidingClosure P S) := by
  refine ⟨⟨Set.subset_sInter fun T hT => hT.1, fun d hd => ?_, fun d hd hb hP => ?_⟩,
    fun T hT => Set.sInter_subset_of_mem hT⟩
  · exact Set.mem_sInter.2 fun T hT => hT.2.1 d (Set.mem_sInter.1 hd T hT)
  · exact ⟨Set.mem_sInter.2 fun T hT => (hT.2.2 d (Set.mem_sInter.1 hd T hT) hb hP).1,
      Set.mem_sInter.2 fun T hT => (hT.2.2 d (Set.mem_sInter.1 hd T hT) hb hP).2⟩

/-- A set of darts is contained in its closure avoiding `P`. -/
theorem subset_avoidingClosure (P : List H) (S : Set H) : S ⊆ X.avoidingClosure P S :=
  (X.isLeast_avoidingClosure P S).1.1

/-- The closure of a set of darts avoiding `P` is closed off `P`. -/
theorem isClosedOff_avoidingClosure (P : List H) (S : Set H) :
    X.IsClosedOff P (X.avoidingClosure P S) :=
  (X.isLeast_avoidingClosure P S).1.2

/-- The closure of `S` avoiding `P` is contained in every set closed off `P` containing `S`. -/
theorem avoidingClosure_subset {P : List H} {S T : Set H} (hST : S ⊆ T)
    (hT : X.IsClosedOff P T) : X.avoidingClosure P S ⊆ T :=
  (X.isLeast_avoidingClosure P S).2 ⟨hST, hT⟩

/-! ### Closed walks from lists -/

private theorem val_finRotate {n : ℕ} (j : Fin n) :
    (finRotate n j : ℕ) = if (j : ℕ) + 1 < n then (j : ℕ) + 1 else 0 := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : j = Fin.last n
    · subst h; simp
    · have : (j : ℕ) < n := Fin.val_lt_last h
      simp only [h, if_false, show (j : ℕ) + 1 < n + 1 by omega, if_true]

omit [Fintype H] [DecidableEq H] in
private theorem get_eq_getLast {L : List H} (hne : L ≠ []) (i : Fin L.length)
    (hi : ¬(i : ℕ) + 1 < L.length) : L.get i = L.getLast hne := by
  rw [List.getLast_eq_getElem, List.get_eq_getElem]
  congr 1
  omega

/-- A nonempty list of darts, consecutive darts of which are linked without turning back, whose
last dart is linked to its first, and whose darts have pairwise distinct vertices, is a simple
closed walk. -/
private theorem isSimpleClosedWalk_get {R : RotationSystem H} {L : List H} (hne : L ≠ [])
    (hchain : L.IsChain fun d d' => R.vertexOf (R.inv d) = R.vertexOf d' ∧ d' ≠ R.inv d)
    (hlast : R.vertexOf (R.inv (L.getLast hne)) = R.vertexOf (L.head hne))
    (hlast' : L.head hne ≠ R.inv (L.getLast hne))
    (hnodup : (L.map R.vertexOf).Nodup) : R.IsSimpleClosedWalk L.get := by
  have hc := List.isChain_iff_getElem.1 hchain
  have hrot : ∀ (i : Fin L.length) (hi : (i : ℕ) + 1 < L.length),
      L.get (finRotate L.length i) = L[(i : ℕ) + 1]'hi := fun i hi => by
    have := val_finRotate i
    rw [if_pos hi] at this
    rw [show finRotate L.length i = ⟨i + 1, hi⟩ from Fin.ext this]
    rfl
  have hrot' : ∀ i : Fin L.length, ¬(i : ℕ) + 1 < L.length →
      L.get (finRotate L.length i) = L.head hne := fun i hi => by
    have := val_finRotate i
    rw [if_neg hi] at this
    rw [List.head_eq_getElem, List.get_eq_getElem]
    congr 1
  refine ⟨List.length_pos_iff.2 hne, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · by_cases hi : (i : ℕ) + 1 < L.length
    · rw [hrot i hi]
      exact (hc i hi).1
    · rw [hrot' i hi, get_eq_getLast hne i hi]
      exact hlast
  · by_cases hi : (i : ℕ) + 1 < L.length
    · rw [hrot i hi]
      exact (hc i hi).2
    · rw [hrot' i hi, get_eq_getLast hne i hi]
      exact hlast'
  · have := (hnodup.getElem_inj_iff (i := i) (j := j) (hi := by simp)
      (hj := by simp)).1 (by simpa [List.getElem_map] using hij)
    exact Fin.ext this

/-- The cycle of a simple closed walk given by a list is `1` on its darts, `-1` on their reverses
and `0` elsewhere. -/
theorem walkCycle_get_eq_monogonCycle (hinv : Function.Involutive X.inv) {L : List H}
    (hw : X.IsSimpleClosedWalk L.get) : X.walkCycle L.get = X.monogonCycle L := by
  funext d
  unfold monogonCycle
  by_cases hd : d ∈ L
  · rw [if_pos hd]
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hd
    exact hw.walkCycle_apply_self i
  · rw [if_neg hd]
    by_cases hd' : X.inv d ∈ L
    · rw [if_pos hd']
      obtain ⟨i, hi⟩ := List.mem_iff_get.1 hd'
      have : d = X.inv (L.get i) := by rw [hi, hinv]
      rw [this]
      exact hw.walkCycle_apply_inv hinv i
    · rw [if_neg hd']
      refine RotationSystem.walkCycle_eq_zero hinv (fun i h => hd ?_) fun i h => hd' ?_
      · rw [h]
        exact List.get_mem _ _
      · rw [h, hinv]
        exact List.get_mem _ _

/-! ### Simple strand paths as closed walks -/

/-- The vertices of the darts of a strand path `(e₁, …, e_m)` are `v(e₁)` followed by its interior
points. -/
theorem map_vertexOf_eq_cons_interiorPoints :
    ∀ {e : H} {Q : List H}, (e :: Q).IsChain X.StrandStep →
      (e :: Q).map X.vertexOf = X.vertexOf e :: X.interiorPoints (e :: Q)
  | e, [], _ => by simp [interiorPoints]
  | e, e' :: Q, h => by
    rw [List.isChain_cons_cons] at h
    have ih := map_vertexOf_eq_cons_interiorPoints h.2
    have hip : X.interiorPoints (e :: e' :: Q) =
        X.vertexOf (X.inv e) :: X.interiorPoints (e' :: Q) := by
      simp [interiorPoints]
    rw [List.map_cons, ih, hip, h.1.vertexOf_eq]

variable {X} in
/-- A strand step is a link of a closed walk. -/
theorem StrandStep.link (hX : X.IsPreTripleDiagram) {e e' : H}
    (h : X.StrandStep e e') : X.vertexOf (X.inv e) = X.vertexOf e' ∧ e' ≠ X.inv e := by
  refine ⟨h.vertexOf_eq.symm, fun he => ?_⟩
  have h3 : (X.rot ^ 3) (X.inv e) = (X.rot ^ 0) (X.inv e) := by rw [← h.2, he, pow_zero]; rfl
  exact absurd ((hX.rot_pow_six h.1).2 3 0 (by norm_num) (by norm_num) h3) (by norm_num)

variable {X} in
/-- A monogon that is a simple strand path is a simple closed walk. -/
theorem IsMonogon.isSimpleClosedWalk (hX : X.IsPreTripleDiagram)
    {P : List H} (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) :
    X.IsSimpleClosedWalk P.get := by
  have hne := hP.isStrandPath.ne_nil
  refine isSimpleClosedWalk_get hne (hP.isStrandPath.isChain.imp fun _ _ h => h.link hX) ?_ ?_ ?_
  · have h1 := hP.pathEnd_eq
    rw [X.pathEnd_of_getLast? (List.getLast?_eq_some_getLast hne),
      X.pathStart_of_head? (List.head?_eq_some_head hne)] at h1
    exact h1
  · intro h
    have h1 := hP.isStrandPath.isOut_eq_true _ (List.head_mem hne)
    have h2 := hP.isStrandPath.isOut_eq_true _ (List.getLast_mem hne)
    rw [h, hX.isOut_inv_apply (hP.isStrandPath.notMem_bdry _ (List.getLast_mem hne)), h2] at h1
    exact absurd h1 (by simp)
  · obtain ⟨e, Q, rfl⟩ := List.exists_cons_of_ne_nil hne
    rw [X.map_vertexOf_eq_cons_interiorPoints hP.isStrandPath.isChain]
    exact List.nodup_cons.2 ⟨hs.pathStart_notMem, hs.nodup⟩

variable {X} in
/-- The cycle of a simple monogon is the cycle of the closed walk it forms. -/
theorem monogonCycle_eq_walkCycle (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) :
    X.monogonCycle P = X.walkCycle P.get :=
  (X.walkCycle_get_eq_monogonCycle hX.inv_involutive (hP.isSimpleClosedWalk hX hs)).symm

/-! ### The winding function of a simple monogon -/

section Winding

variable {X}

private theorem rot_pow_inj (hX : X.IsPreTripleDiagram) {d : H}
    (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) {i j : ℕ} (hi : i < 6) (hj : j < 6)
    (h : (X.rot ^ i) d = (X.rot ^ j) d) : i = j :=
  (hX.rot_pow_six hd).2 i j hi hj h

private theorem exists_rot_pow_eq (hX : X.IsPreTripleDiagram) {d e : H}
    (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) (he : e ∈ X.vertexOf d) :
    ∃ k < 6, e = (X.rot ^ k) d := by
  obtain ⟨n, hn⟩ := (X.mem_vertexOf.1 he).exists_nat_pow_eq
  exact ⟨n % 6, Nat.mod_lt _ (by norm_num), by rw [← hn, hX.rot_pow_mod_six hd]⟩

/-- At the vertex `v(c_{i+1})` of a simple closed walk, the only dart of the walk is `c_{i+1}` and
the only reverse of a dart of the walk is `c̄_i`. -/
private theorem eq_of_vertexOf_eq_finRotate {L : ℕ} {w : Fin L → H}
    (hw : X.IsSimpleClosedWalk w) (i : Fin L) {d : H}
    (hd : X.vertexOf d = X.vertexOf (w (finRotate L i))) :
    (∀ j, d = w j → d = w (finRotate L i)) ∧ ∀ j, d = X.inv (w j) → d = X.inv (w i) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [hj, hw.eq_of_vertexOf_eq (i := i) (j := j) (by rw [← hj, hd])]
  · rw [hj, hw.eq_of_vertexOf_inv_eq (i := i) (j := j) (by rw [← hj, hd])]

/-- The values of the winding function of a simple closed walk around the vertex `v(c_{i+1})`,
where the walk enters along `c̄_i` and leaves along `c_{i+1} = σ^t(c̄_i)`: with `μ = h(f(c_i))`,
`h(f(σ^k c̄_i))` is `μ` for `1 ≤ k ≤ t` and `μ + 1` otherwise. -/
private theorem walk_apply_rot_pow (hX : X.IsTripleDiagram) {L : ℕ} {w : Fin L → H}
    (hw : X.IsSimpleClosedWalk w) {h : X.faceOrbits → ℤ}
    (hh : X.IsWindingFunction (X.walkCycle w) h) (i : Fin L)
    (htrip : ¬X.IsBoundaryVertex (X.vertexOf (X.inv (w i)))) {t : ℕ} (ht6 : t < 6)
    (ht : w (finRotate L i) = (X.rot ^ t) (X.inv (w i))) :
    ∀ k < 6, h (X.toFaceOrbit ((X.rot ^ k) (X.inv (w i)))) =
      h (X.toFaceOrbit (w i)) + if 1 ≤ k ∧ k ≤ t then 0 else 1 := by
  have hinv := hX.inv_involutive
  have hpre := hX.toIsPreTripleDiagram
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hw.ne_inv i (by rw [ht, pow_zero, Equiv.Perm.one_apply])
  have hv : ∀ k, X.vertexOf ((X.rot ^ k) (X.inv (w i))) = X.vertexOf (w (finRotate L i)) :=
    fun k => by rw [X.vertexOf_rot_pow_apply, hw.vertexOf_inv]
  have hc : ∀ k < 6, X.walkCycle w ((X.rot ^ k) (X.inv (w i))) =
      if k = 0 then -1 else if k = t then 1 else 0 := by
    intro k hk
    obtain ⟨hA, hB⟩ := eq_of_vertexOf_eq_finRotate hw i (hv k)
    split_ifs with h0 h1
    · subst h0
      rw [pow_zero, Equiv.Perm.one_apply]
      exact hw.walkCycle_apply_inv hinv i
    · subst h1
      rw [← ht]
      exact hw.walkCycle_apply_self _
    · refine RotationSystem.walkCycle_eq_zero hinv (fun j hj => h1 ?_) fun j hj => h0 ?_
      · have := hA j hj
        rw [ht] at this
        exact rot_pow_inj hpre htrip hk ht6 this
      · have := hB j hj
        exact rot_pow_inj hpre htrip hk (by norm_num)
          (by rw [this, pow_zero, Equiv.Perm.one_apply])
  intro k hk
  induction k with
  | zero =>
    rw [pow_zero, Equiv.Perm.one_apply, hh.walk_apply_inv hw i]
    simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, hh.apply_rot hinv, ih (by omega), hc k (by omega)]
    split_ifs <;> omega

private theorem strandStep_getElem {P : List H} (hP : X.IsStrandPath P) {l : ℕ}
    (hl : l + 1 < P.length) : X.StrandStep P[l] P[l + 1] :=
  List.isChain_iff_getElem.1 hP.isChain l hl

private theorem finRotate_eq_succ {L : ℕ} (i : Fin L) (hi : (i : ℕ) + 1 < L) :
    finRotate L i = ⟨i + 1, hi⟩ :=
  Fin.ext (by rw [val_finRotate, if_pos hi])

private theorem finRotate_eq_zero {L : ℕ} (i : Fin L) (hi : ¬(i : ℕ) + 1 < L) :
    finRotate L i = ⟨0, i.pos⟩ :=
  Fin.ext (by rw [val_finRotate, if_neg hi])

omit [Fintype H] [DecidableEq H] in
private theorem getElem_zero_mem_head? {P : List H} (h0 : 0 < P.length) : P[0] ∈ P.head? := by
  cases P with
  | nil => simp at h0
  | cons e Q => simp

omit [Fintype H] [DecidableEq H] in
private theorem getElem_last_mem_getLast? {P : List H} (h0 : 0 < P.length) :
    P[P.length - 1] ∈ P.getLast? := by
  rw [List.getLast?_eq_getElem?]
  simp

/-- The vertex of a monogon: its last dart returns to `v(e₁)`, a triple point. -/
private theorem IsMonogon.vertexOf_inv_last {P : List H} (hP : X.IsMonogon P)
    (h0 : 0 < P.length) :
    X.vertexOf (X.inv P[P.length - 1]) = X.vertexOf P[0] ∧
      ¬X.IsBoundaryVertex (X.vertexOf P[0]) := by
  have hne := hP.isStrandPath.ne_nil
  have h1 := hP.pathEnd_eq
  rw [X.pathEnd_of_getLast? (List.getLast?_eq_some_getLast hne),
    X.pathStart_of_head? (List.head?_eq_some_head hne), List.getLast_eq_getElem,
    List.head_eq_getElem] at h1
  have h2 := hP.pathStart_mem
  rw [X.pathStart_of_head? (List.head?_eq_some_head hne), List.head_eq_getElem] at h2
  exact ⟨h1, X.vertexOf_mem_internalVertices.1 h2⟩

private theorem IsMonogon.not_isBoundaryVertex_vertexOf_inv_last {P : List H}
    (hP : X.IsMonogon P) (h0 : 0 < P.length) :
    ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[P.length - 1])) := by
  rw [(hP.vertexOf_inv_last h0).1]
  exact (hP.vertexOf_inv_last h0).2

/-- The darts of a monogon and their reverses lie at triple points. -/
private theorem IsMonogon.not_isBoundaryVertex {P : List H} (hP : X.IsMonogon P) {e : H}
    (he : e ∈ P) :
    ¬X.IsBoundaryVertex (X.vertexOf e) ∧ ¬X.IsBoundaryVertex (X.vertexOf (X.inv e)) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  have hx := hP.vertexOf_inv_last (by omega)
  refine ⟨?_, ?_⟩
  · rcases j with _ | j
    · exact hx.2
    · rw [(strandStep_getElem hP.isStrandPath hj).vertexOf_eq]
      exact (strandStep_getElem hP.isStrandPath hj).1
  · by_cases hj' : j + 1 < P.length
    · exact (strandStep_getElem hP.isStrandPath hj').1
    · have : j = P.length - 1 := by omega
      subst this
      exact hP.not_isBoundaryVertex_vertexOf_inv_last (by omega)

/-- The reverse of a dart of a monogon lies at the vertex of a dart of the monogon. -/
private theorem IsMonogon.exists_vertexOf_inv_eq {P : List H} (hP : X.IsMonogon P) {e : H}
    (he : e ∈ P) : ∃ e' ∈ P, X.vertexOf (X.inv e) = X.vertexOf e' := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  by_cases hj' : j + 1 < P.length
  · exact ⟨_, List.getElem_mem hj', (strandStep_getElem hP.isStrandPath hj').vertexOf_eq.symm⟩
  · have : j = P.length - 1 := by omega
    subst this
    exact ⟨_, List.getElem_mem (by omega), (hP.vertexOf_inv_last (by omega)).1⟩

/-- A dart at a vertex not on a monogon is neither a dart of the monogon nor the reverse of
one. -/
private theorem IsMonogon.notMem_of_forall_ne (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) {d : H} (hd : ∀ e ∈ P, X.vertexOf d ≠ X.vertexOf e) :
    d ∉ P ∧ X.inv d ∉ P := by
  refine ⟨fun h => hd d h rfl, fun h => ?_⟩
  obtain ⟨e', he', hv⟩ := hP.exists_vertexOf_inv_eq h
  rw [hX.inv_inv_apply] at hv
  exact hd e' he' hv

omit [Fintype H] in
/-- The monogon cycle of `P` vanishes on a dart `d` such that neither `d` nor its reverse is a dart
of `P`. -/
theorem monogonCycle_eq_zero_of_notMem {P : List H} {d : H} (hd : d ∉ P) (hd' : X.inv d ∉ P) :
    X.monogonCycle P d = 0 := by
  simp [monogonCycle, hd, hd']

omit [Fintype H] in
/-- The monogon cycle of `P` is `1` on a dart of `P`. -/
theorem monogonCycle_eq_one_of_mem {P : List H} {d : H} (hd : d ∈ P) :
    X.monogonCycle P d = 1 := by
  simp [monogonCycle, hd]

omit [Fintype H] in
/-- The monogon cycle of `P` is `-1` on the reverse of a dart of `P` that is not itself in `P`. -/
theorem monogonCycle_eq_neg_one_of_inv_mem {P : List H} {d : H} (hd : d ∉ P)
    (hd' : X.inv d ∈ P) : X.monogonCycle P d = -1 := by
  simp [monogonCycle, hd, hd']

/-- **A simple monogon has a unique winding function.** -/
@[cluster_algebras "lem_monogon_winding_exists"]
theorem existsUnique_isMonogonWindingFunction (hX : X.IsTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) :
    ∃! h, X.IsMonogonWindingFunction P h := by
  change ∃! h, X.IsWindingFunction (X.monogonCycle P) h
  rw [monogonCycle_eq_walkCycle hX.toIsPreTripleDiagram hP hs]
  exact hX.toIsDiskMap.existsUnique_isWindingFunction_walkCycle
    (hP.isSimpleClosedWalk hX.toIsPreTripleDiagram hs)

/-- A winding function of a simple monogon is a winding function of the closed walk it forms. -/
theorem IsMonogonWindingFunction.isWindingFunction_walkCycle (hX : X.IsPreTripleDiagram)
    {P : List H} (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) : X.IsWindingFunction (X.walkCycle P.get) h := by
  rw [← monogonCycle_eq_walkCycle hX hP hs]
  exact hh

/-- **The values of the winding function along a simple monogon**: `h(f(e_l)) = h(f(e₁))` and
`h(f(ē_l)) = h(f(e₁)) + 1`. -/
@[cluster_algebras "lem_monogon_winding_exists"]
theorem IsMonogonWindingFunction.apply_getElem (hX : X.IsTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) {l : ℕ} (hl : l < P.length) :
    h (X.toFaceOrbit P[l]) = h (X.toFaceOrbit (P[0]'(by omega))) ∧
      h (X.toFaceOrbit (X.inv P[l])) = h (X.toFaceOrbit (P[0]'(by omega))) + 1 := by
  have hw := hP.isSimpleClosedWalk hX.toIsPreTripleDiagram hs
  have hh' := hh.isWindingFunction_walkCycle hX.toIsPreTripleDiagram hP hs
  have e := hh'.walk_apply_eq hX.inv_involutive hw ⟨l, hl⟩ ⟨0, by omega⟩
  have e' := hh'.walk_apply_inv hw ⟨l, hl⟩
  simp only [List.get_eq_getElem] at e e'
  exact ⟨e, by rw [e', e]⟩

private theorem IsMonogonWindingFunction.apply_rot_pow_inv' (hX : X.IsTripleDiagram)
    {P : List H} (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) {l : ℕ} (hl : l + 1 < P.length) :
    ∀ k < 6, h (X.toFaceOrbit ((X.rot ^ k) (X.inv P[l]))) =
      h (X.toFaceOrbit (P[0]'(by omega))) + if 1 ≤ k ∧ k ≤ 3 then 0 else 1 := by
  have hw := hP.isSimpleClosedWalk hX.toIsPreTripleDiagram hs
  have hh' := hh.isWindingFunction_walkCycle hX.toIsPreTripleDiagram hP hs
  have hstep := strandStep_getElem hP.isStrandPath hl
  have key := walk_apply_rot_pow hX hw hh' ⟨l, by omega⟩ hstep.1 (t := 3) (by norm_num)
    (by rw [finRotate_eq_succ _ hl]; exact hstep.2)
  intro k hk
  rw [← (hh.apply_getElem hX hP hs (by omega : l < P.length)).1]
  exact key k hk

/-- **The values of the winding function around a simple monogon**: at
`z_l = v(ē_l)`, `l ∈ [1, m - 1]`, `h(f(σ^k ē_l)) = h(f(e₁))` for `k ∈ {1, 2, 3}` and
`h(f(σ^k ē_l)) = h(f(e₁)) + 1` for `k ∈ {0, 4, 5}`. Here `ē_l` is `X.inv P[l]` with `0`-indexed
`l`, so the condition `l ∈ [1, m - 1]` reads `l + 1 < m`. -/
@[cluster_algebras "lem_monogon_winding_exists"]
theorem IsMonogonWindingFunction.apply_rot_pow_inv_getElem (hX : X.IsTripleDiagram)
    {P : List H} (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) {l : ℕ} (hl : l + 1 < P.length) :
    (∀ k ∈ ({1, 2, 3} : Finset ℕ), h (X.toFaceOrbit ((X.rot ^ k) (X.inv P[l]))) =
        h (X.toFaceOrbit (P[0]'(by omega)))) ∧
      ∀ k ∈ ({0, 4, 5} : Finset ℕ), h (X.toFaceOrbit ((X.rot ^ k) (X.inv P[l]))) =
        h (X.toFaceOrbit (P[0]'(by omega))) + 1 := by
  have key := hh.apply_rot_pow_inv' hX hP hs hl
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;>
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [key k (by omega)]
    rcases hk with rfl | rfl | rfl <;> simp

end Winding

/-! ### Darts at the vertices of a simple monogon -/

section Local

variable {X}

/-- The exponent `t` with `e₁ = σ^t(ē_m)` at the corner of a monogon with inside `ζ`. -/
private def cornerExp : StrandSide → ℕ
  | .right => 1
  | .left => 5

private theorem cornerExp_lt (ζ : StrandSide) : cornerExp ζ < 6 := by
  cases ζ <;> decide

private theorem IsMonogon.getElem_zero_eq_rot_pow (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (h0 : 0 < P.length) {ζ : StrandSide}
    (hc : X.IsInsideCorner ζ P[0] P[P.length - 1]) :
    P[0] = (X.rot ^ cornerExp ζ) (X.inv P[P.length - 1]) := by
  cases ζ with
  | right =>
    simp only [cornerExp, pow_one]
    exact hc.symm
  | left =>
    simp only [cornerExp]
    have hx := (hP.vertexOf_inv_last h0).2
    change X.rot P[0] = X.inv P[P.length - 1] at hc
    rw [← hc, ← Equiv.Perm.mul_apply, ← pow_succ]
    exact (hX.rot_pow_six_apply hx).symm

private theorem IsMonogonWindingFunction.apply_rot_pow_inv_last (hX : X.IsTripleDiagram)
    {P : List H} (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) (h0 : 0 < P.length) {ζ : StrandSide}
    (hc : X.IsInsideCorner ζ P[0] P[P.length - 1]) :
    ∀ k < 6, h (X.toFaceOrbit ((X.rot ^ k) (X.inv P[P.length - 1]))) =
      h (X.toFaceOrbit P[0]) + if 1 ≤ k ∧ k ≤ cornerExp ζ then 0 else 1 := by
  have hpre := hX.toIsPreTripleDiagram
  have hw := hP.isSimpleClosedWalk hpre hs
  have hh' := hh.isWindingFunction_walkCycle hpre hP hs
  have key := walk_apply_rot_pow hX hw hh' ⟨P.length - 1, by omega⟩
    (hP.not_isBoundaryVertex_vertexOf_inv_last h0) (cornerExp_lt ζ)
    (by
      rw [finRotate_eq_zero _ (by change ¬(P.length - 1 + 1 < P.length); omega)]
      exact hP.getElem_zero_eq_rot_pow hpre h0 hc)
  intro k hk
  rw [← (hh.apply_getElem hX hP hs (by omega : P.length - 1 < P.length)).1]
  exact key k hk

private theorem vertexOf_getElem_inj {P : List H} (hw : X.IsSimpleClosedWalk P.get) {i j : ℕ}
    (hi : i < P.length) (hj : j < P.length) (h : X.vertexOf P[i] = X.vertexOf P[j]) : i = j :=
  congrArg Fin.val (hw.injective_vertexOf (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h)

/-- The darts at an interior point `z_l = v(ē_l)` of a simple monogon: `σ^k ē_l` is a dart of
the monogon only for `k = 3` and the reverse of one only for `k = 0`. -/
private theorem rot_pow_inv_getElem_mem (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {l : ℕ} (hl : l + 1 < P.length) {k : ℕ}
    (hk : k < 6) :
    ((X.rot ^ k) (X.inv P[l]) ∈ P ↔ k = 3) ∧ (X.inv ((X.rot ^ k) (X.inv P[l])) ∈ P ↔ k = 0) ∧
      (X.rot ^ k) (X.inv P[l]) ∉ X.bdry := by
  have hw := hP.isSimpleClosedWalk hX hs
  have hstep := strandStep_getElem hP.isStrandPath hl
  have htrip : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[l])) := hstep.1
  have hv : X.vertexOf ((X.rot ^ k) (X.inv P[l])) =
      X.vertexOf (P.get (finRotate P.length ⟨l, by omega⟩)) := by
    rw [X.vertexOf_rot_pow_apply, finRotate_eq_succ _ hl]
    exact hstep.vertexOf_eq.symm
  obtain ⟨hA, hB⟩ := eq_of_vertexOf_eq_finRotate hw ⟨l, by omega⟩ hv
  rw [finRotate_eq_succ _ hl] at hA
  refine ⟨⟨fun hd => ?_, fun hk3 => ?_⟩, ⟨fun hd => ?_, fun hk0 => ?_⟩, ?_⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_get.1 hd
    exact rot_pow_inj hX htrip hk (by norm_num) ((hA j hj.symm).trans hstep.2)
  · rw [hk3, ← hstep.2]
    exact List.getElem_mem _
  · obtain ⟨j, hj⟩ := List.mem_iff_get.1 hd
    have := hB j (by rw [hj, hX.inv_inv_apply])
    exact rot_pow_inj hX htrip hk (by norm_num) (by rw [this, pow_zero, Equiv.Perm.one_apply]; rfl)
  · rw [hk0, pow_zero, Equiv.Perm.one_apply, hX.inv_inv_apply]
    exact List.getElem_mem _
  · exact X.notMem_bdry_of_not_isBoundaryVertex (by rwa [X.vertexOf_rot_pow_apply])

/-- The darts at the vertex `x` of a simple monogon with corner condition `ζ`: `σ^k ē_m` is a dart
of the monogon only for `k = t` (`e₁ = σ^t ē_m`) and the reverse of one only for `k = 0`. -/
private theorem rot_pow_inv_last_mem (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) (h0 : 0 < P.length) {ζ : StrandSide}
    (hc : X.IsInsideCorner ζ P[0] P[P.length - 1]) {k : ℕ} (hk : k < 6) :
    ((X.rot ^ k) (X.inv P[P.length - 1]) ∈ P ↔ k = cornerExp ζ) ∧
      (X.inv ((X.rot ^ k) (X.inv P[P.length - 1])) ∈ P ↔ k = 0) ∧
      (X.rot ^ k) (X.inv P[P.length - 1]) ∉ X.bdry := by
  have htrip := hP.not_isBoundaryVertex_vertexOf_inv_last h0
  have hlast : ¬(P.length - 1 + 1 < P.length) := by omega
  have hv : X.vertexOf ((X.rot ^ k) (X.inv P[P.length - 1])) =
      X.vertexOf (P.get (finRotate P.length ⟨P.length - 1, by omega⟩)) := by
    rw [X.vertexOf_rot_pow_apply, finRotate_eq_zero _ hlast]
    exact (hP.vertexOf_inv_last h0).1
  have he1 := hP.getElem_zero_eq_rot_pow hX h0 hc
  obtain ⟨hA, hB⟩ :=
    eq_of_vertexOf_eq_finRotate (hP.isSimpleClosedWalk hX hs) ⟨P.length - 1, by omega⟩ hv
  rw [finRotate_eq_zero _ hlast] at hA
  refine ⟨⟨fun hd => ?_, fun hkt => ?_⟩, ⟨fun hd => ?_, fun hk0 => ?_⟩, ?_⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_get.1 hd
    exact rot_pow_inj hX htrip hk (cornerExp_lt ζ) ((hA j hj.symm).trans he1)
  · rw [hkt, ← he1]
    exact List.getElem_mem _
  · obtain ⟨j, hj⟩ := List.mem_iff_get.1 hd
    have := hB j (by rw [hj, hX.inv_inv_apply])
    exact rot_pow_inj hX htrip hk (by norm_num) (by rw [this, pow_zero, Equiv.Perm.one_apply]; rfl)
  · rw [hk0, pow_zero, Equiv.Perm.one_apply, hX.inv_inv_apply]
    exact List.getElem_mem _
  · exact X.notMem_bdry_of_not_isBoundaryVertex (by rwa [X.vertexOf_rot_pow_apply])

private theorem rot_pow_mem_sideDarts (hX : X.IsPreTripleDiagram) {e : H}
    (htrip : ¬X.IsBoundaryVertex (X.vertexOf (X.inv e))) {k : ℕ} (hk : k < 6) :
    ((X.rot ^ k) (X.inv e) ∈ X.sideDarts .right e ↔ k = 1 ∨ k = 2) ∧
      ((X.rot ^ k) (X.inv e) ∈ X.sideDarts .left e ↔ k = 4 ∨ k = 5) := by
  have key : ∀ j < 6, (X.rot ^ k) (X.inv e) = (X.rot ^ j) (X.inv e) ↔ k = j := fun j hj =>
    ⟨rot_pow_inj hX htrip hk hj, fun h => h ▸ rfl⟩
  simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false]
  rw [show X.rot (X.inv e) = (X.rot ^ 1) (X.inv e) by rw [pow_one], key 1 (by norm_num),
    key 2 (by norm_num), key 4 (by norm_num), key 5 (by norm_num)]
  exact ⟨Iff.rfl, Iff.rfl⟩

private theorem vertexOf_of_mem_sideDarts {ζ : StrandSide} {e d : H}
    (hd : d ∈ X.sideDarts ζ e) : X.vertexOf d = X.vertexOf (X.inv e) := by
  cases ζ <;>
  · simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · first
      | exact X.vertexOf_rot _
      | exact X.vertexOf_rot_pow_apply _ _
    · exact X.vertexOf_rot_pow_apply _ _

omit [Fintype H] [DecidableEq H] in
private theorem mem_sideList {ζ : StrandSide} {P : List H} {d : H} :
    d ∈ X.sideList ζ P ↔ ∃ l, ∃ hl : l + 1 < P.length, d ∈ X.sideDarts ζ P[l] := by
  have key : ∀ e, e ∈ P.dropLast ↔ ∃ l, ∃ hl : l + 1 < P.length, P[l] = e := by
    intro e
    rw [List.mem_iff_getElem]
    simp only [List.length_dropLast, List.getElem_dropLast]
    constructor <;> rintro ⟨l, hl, rfl⟩ <;> exact ⟨l, by omega, rfl⟩
  cases ζ <;>
  · simp only [sideList, List.mem_flatMap, List.mem_reverse, key]
    constructor
    · rintro ⟨e, ⟨l, hl, rfl⟩, hd⟩
      exact ⟨l, hl, hd⟩
    · rintro ⟨l, hl, hd⟩
      exact ⟨_, ⟨l, hl, rfl⟩, hd⟩

private theorem mem_sideList_iff_of_vertexOf (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {ζ : StrandSide} {d : H} {l : ℕ}
    (hl : l + 1 < P.length) (hd : X.vertexOf d = X.vertexOf (X.inv P[l])) :
    d ∈ X.sideList ζ P ↔ d ∈ X.sideDarts ζ P[l] := by
  have hw := hP.isSimpleClosedWalk hX hs
  refine ⟨fun h => ?_, fun h => mem_sideList.2 ⟨l, hl, h⟩⟩
  obtain ⟨l', hl', hd'⟩ := mem_sideList.1 h
  have h1 := (vertexOf_of_mem_sideDarts hd').symm.trans hd
  rw [← (strandStep_getElem hP.isStrandPath hl').vertexOf_eq,
    ← (strandStep_getElem hP.isStrandPath hl).vertexOf_eq] at h1
  obtain rfl : l' = l := by have := vertexOf_getElem_inj hw hl' hl h1; omega
  exact hd'

private theorem notMem_sideList_of_vertexOf (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) (h0 : 0 < P.length) {ζ : StrandSide}
    {d : H} (hd : X.vertexOf d = X.vertexOf P[0]) : d ∉ X.sideList ζ P := by
  have hw := hP.isSimpleClosedWalk hX hs
  intro h
  obtain ⟨l, hl, hd'⟩ := mem_sideList.1 h
  have h1 := (vertexOf_of_mem_sideDarts hd').symm.trans hd
  rw [← (strandStep_getElem hP.isStrandPath hl).vertexOf_eq] at h1
  have := vertexOf_getElem_inj hw hl h0 h1
  omega

/-- A winding function of a monogon vanishes at the darts of the endpoints. -/
private theorem IsMonogonWindingFunction.apply_eq_zero_of_isBoundaryVertex'
    (hX : X.IsTripleDiagram) {P : List H} (hP : X.IsMonogon P) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) {d : H} (hd : X.IsBoundaryVertex (X.vertexOf d)) :
    h (X.toFaceOrbit d) = 0 := by
  refine hh.apply_eq_zero_of_isBoundaryVertex hX.toIsDiskMap hd fun e he => ?_
  have hv : X.vertexOf e = X.vertexOf d := X.vertexOf_eq_of_mem he
  refine X.monogonCycle_eq_zero_of_notMem (fun heP => ?_) fun heP => ?_
  · exact (hP.not_isBoundaryVertex heP).1 (hv ▸ hd)
  · have := (hP.not_isBoundaryVertex heP).2
    rw [hX.inv_involutive e, hv] at this
    exact this hd

end Local

/-! ### The inside of a convex monogon -/

section Inside

variable {X}

/-- For nonempty `P`, a dart lies in `insideDarts P ζ h` iff it is not a boundary dart, neither it
nor its reverse is a dart of `P`, and `h` takes the same value on its face orbit as on the `ζ`-side
orbit of the first dart of `P`. -/
theorem mem_insideDarts {P : List H} {ζ : StrandSide} {h : X.faceOrbits → ℤ}
    (h0 : 0 < P.length) {d : H} :
    d ∈ X.insideDarts P ζ h ↔ d ∉ X.bdry ∧ d ∉ P ∧ X.inv d ∉ P ∧
      h (X.toFaceOrbit d) = h (X.sideOrbit ζ P[0]) := by
  cases P with
  | nil => simp at h0
  | cons e Q => simp [insideDarts]

namespace IsConvexMonogon

variable {P : List H} {ζ : StrandSide}

/-- A convex monogon is a nonempty list of darts. -/
theorem length_pos (hM : X.IsConvexMonogon P ζ) : 0 < P.length :=
  List.length_pos_iff.2 hM.isMonogon.isStrandPath.ne_nil

/-- The first and last darts of a convex monogon with inside `ζ` form an inside corner on side
`ζ`. -/
theorem isInsideCorner_getElem (hM : X.IsConvexMonogon P ζ) :
    X.IsInsideCorner ζ (P[0]'hM.length_pos)
      (P[P.length - 1]'(by have := hM.length_pos; omega)) :=
  hM.isInsideCorner _ (getElem_zero_mem_head? hM.length_pos) _
    (getElem_last_mem_getLast? hM.length_pos)

/-- The inside value `ω` of a convex monogon is nonzero, for every winding function. -/
theorem apply_sideOrbit_ne_zero (hX : X.IsTripleDiagram) (hM : X.IsConvexMonogon P ζ)
    {h : X.faceOrbits → ℤ} (hh : X.IsMonogonWindingFunction P h) :
    h (X.sideOrbit ζ (P[0]'hM.length_pos)) ≠ 0 := by
  obtain ⟨h', hh', hne⟩ := hM.exists_windingFunction
  rw [DiskMap.IsWindingFunction.unique hX.toIsDiskMap hh hh']
  exact hne _ (getElem_zero_mem_head? hM.length_pos)

/-- **Local description of the inside**: no dart at an endpoint (in particular no dart of `B` and
no leg) is inside. -/
@[cluster_algebras "lem_monogon_inside_local"]
theorem notMem_insideDarts_of_isBoundaryVertex (hX : X.IsTripleDiagram)
    (hM : X.IsConvexMonogon P ζ) {h : X.faceOrbits → ℤ} (hh : X.IsMonogonWindingFunction P h)
    {d : H} (hd : X.IsBoundaryVertex (X.vertexOf d)) : d ∉ X.insideDarts P ζ h := fun hK =>
  hM.apply_sideOrbit_ne_zero hX hh <| ((mem_insideDarts hM.length_pos).1 hK).2.2.2.symm.trans
    (hh.apply_eq_zero_of_isBoundaryVertex' hX hM.isMonogon hd)

end IsConvexMonogon

/-- **Local description of the inside**: for every dart `d`, `d` and `d̄` are both inside or both
not. -/
@[cluster_algebras "lem_monogon_inside_local"]
theorem inv_mem_insideDarts_iff (hX : X.IsPreTripleDiagram) {P : List H} {ζ : StrandSide}
    {h : X.faceOrbits → ℤ} (hh : X.IsMonogonWindingFunction P h) (h0 : 0 < P.length) (d : H) :
    X.inv d ∈ X.insideDarts P ζ h ↔ d ∈ X.insideDarts P ζ h := by
  rw [mem_insideDarts h0, mem_insideDarts h0, hX.inv_inv_apply]
  by_cases hd : d ∈ P
  · simp [hd]
  by_cases hd' : X.inv d ∈ P
  · simp [hd']
  have hval : h (X.toFaceOrbit (X.inv d)) = h (X.toFaceOrbit d) := by
    have := hh.sub_eq d
    rw [X.monogonCycle_eq_zero_of_notMem hd hd'] at this
    linarith
  have hB : X.inv d ∈ X.bdry ↔ d ∈ X.bdry :=
    ⟨fun h' => by simpa [hX.inv_inv_apply] using hX.inv_mem_bdry _ h', hX.inv_mem_bdry d⟩
  rw [hval, hB]
  tauto

/-- **Local description of the inside**: at a triple point avoided by `M`, all or none of the
darts are inside. -/
@[cluster_algebras "lem_monogon_inside_local"]
theorem mem_insideDarts_iff_of_forall_ne (hX : X.IsTripleDiagram) {P : List H}
    {ζ : StrandSide} {h : X.faceOrbits → ℤ} (hP : X.IsMonogon P)
    (hh : X.IsMonogonWindingFunction P h) {d : H} (hd : ¬X.IsBoundaryVertex (X.vertexOf d))
    (havoid : ∀ e ∈ P, X.vertexOf d ≠ X.vertexOf e) {e : H} (he : e ∈ X.vertexOf d) :
    e ∈ X.insideDarts P ζ h ↔ d ∈ X.insideDarts P ζ h := by
  have h0 : 0 < P.length := List.length_pos_iff.2 hP.isStrandPath.ne_nil
  have hpre := hX.toIsPreTripleDiagram
  have hv : X.vertexOf e = X.vertexOf d := X.vertexOf_eq_of_mem he
  obtain ⟨he1, he2⟩ := hP.notMem_of_forall_ne hpre fun e' he' => by rw [hv]; exact havoid e' he'
  obtain ⟨hd1, hd2⟩ := hP.notMem_of_forall_ne hpre havoid
  have hc : ∀ e' ∈ X.vertexOf d, X.monogonCycle P e' = 0 := fun e' he' => by
    have hv' := X.vertexOf_eq_of_mem he'
    obtain ⟨h1, h2⟩ := hP.notMem_of_forall_ne hpre fun e'' he'' => by
      rw [hv']; exact havoid e'' he''
    exact X.monogonCycle_eq_zero_of_notMem h1 h2
  have hval := RotationSystem.apply_toFaceOrbit_eq_of_mem_vertexOf hX.inv_involutive hh.sub_eq hc he
  rw [mem_insideDarts h0, mem_insideDarts h0, hval]
  have hdB := X.notMem_bdry_of_not_isBoundaryVertex hd
  have heB := X.notMem_bdry_of_not_isBoundaryVertex (hv ▸ hd)
  simp [hdB, heB, he1, he2, hd1, hd2]

namespace IsConvexMonogon

variable {P : List H} {ζ : StrandSide}

/-- **Local description of the inside**: at an interior point `z_l = v(ē_l)` exactly the two `ζ`
darts are inside. -/
@[cluster_algebras "lem_monogon_inside_local"]
theorem mem_insideDarts_iff_mem_sideDarts (hX : X.IsTripleDiagram) (hM : X.IsConvexMonogon P ζ)
    {h : X.faceOrbits → ℤ} (hh : X.IsMonogonWindingFunction P h) {l : ℕ}
    (hl : l + 1 < P.length) {e : H} (he : e ∈ X.vertexOf (X.inv P[l])) :
    e ∈ X.insideDarts P ζ h ↔ e ∈ X.sideDarts ζ P[l] := by
  have hpre := hX.toIsPreTripleDiagram
  have hstep := strandStep_getElem hM.isMonogon.isStrandPath hl
  have htrip : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[l])) := hstep.1
  obtain ⟨k, hk, rfl⟩ := exists_rot_pow_eq hpre htrip he
  obtain ⟨h1, h2, h3⟩ := rot_pow_inv_getElem_mem hpre hM.isMonogon hM.isSimpleStrandPath hl hk
  have hval := hh.apply_rot_pow_inv' hX hM.isMonogon hM.isSimpleStrandPath hl k hk
  have hside := rot_pow_mem_sideDarts hpre htrip hk
  have h00 := hh.apply_getElem hX hM.isMonogon hM.isSimpleStrandPath hM.length_pos
  rw [mem_insideDarts hM.length_pos, h1, h2, hval]
  cases ζ with
  | right =>
    rw [hside.1]
    simp only [sideOrbit]
    constructor
    · rintro ⟨-, h3', h0', hv⟩
      split_ifs at hv with hc <;> omega
    · intro hk'
      refine ⟨h3, by omega, by omega, ?_⟩
      rw [if_pos (by omega)]
      simp
  | left =>
    rw [hside.2]
    simp only [sideOrbit]
    rw [h00.2]
    constructor
    · rintro ⟨-, h3', h0', hv⟩
      split_ifs at hv with hc <;> omega
    · intro hk'
      refine ⟨h3, by omega, by omega, ?_⟩
      rw [if_neg (by omega)]

/-- **Local description of the inside**: no dart of the vertex `x` of `M` is inside. -/
@[cluster_algebras "lem_monogon_inside_local"]
theorem notMem_insideDarts_of_mem_pathStart (hX : X.IsTripleDiagram)
    (hM : X.IsConvexMonogon P ζ) {h : X.faceOrbits → ℤ} (hh : X.IsMonogonWindingFunction P h)
    {e : H} (he : e ∈ X.pathStart P) : e ∉ X.insideDarts P ζ h := by
  have hpre := hX.toIsPreTripleDiagram
  have h0 := hM.length_pos
  have hx := hM.isMonogon.vertexOf_inv_last h0
  have hc := hM.isInsideCorner_getElem
  rw [X.pathStart_of_head? (List.head?_eq_some_head hM.isMonogon.isStrandPath.ne_nil),
    List.head_eq_getElem, ← hx.1] at he
  have htrip := hM.isMonogon.not_isBoundaryVertex_vertexOf_inv_last h0
  obtain ⟨k, hk, rfl⟩ := exists_rot_pow_eq hpre htrip he
  obtain ⟨h1, h2, -⟩ := rot_pow_inv_last_mem hpre hM.isMonogon hM.isSimpleStrandPath h0 hc hk
  have hval := hh.apply_rot_pow_inv_last hX hM.isMonogon hM.isSimpleStrandPath h0 hc k hk
  have h00 := hh.apply_getElem hX hM.isMonogon hM.isSimpleStrandPath h0
  rw [mem_insideDarts h0, h1, h2, hval]
  rintro ⟨-, hn1, hn0, hv⟩
  cases ζ with
  | right =>
    simp only [sideOrbit, cornerExp] at hv hn1
    split_ifs at hv <;> omega
  | left =>
    simp only [sideOrbit, cornerExp] at hv hn1
    rw [h00.2] at hv
    split_ifs at hv <;> omega

/-- **Local description of the inside**: the inside darts at the triple points of `M` are exactly
the darts of the inside list. -/
@[cluster_algebras "lem_monogon_inside_local"]
theorem mem_insideDarts_iff_mem_insideList (hX : X.IsTripleDiagram)
    (hM : X.IsConvexMonogon P ζ) {h : X.faceOrbits → ℤ} (hh : X.IsMonogonWindingFunction P h)
    {d : H} (hd : ∃ e ∈ P, X.vertexOf d = X.vertexOf e) :
    d ∈ X.insideDarts P ζ h ↔ d ∈ X.insideList ζ P := by
  have hpre := hX.toIsPreTripleDiagram
  obtain ⟨e, he, hde⟩ := hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  rcases j with _ | j
  · have hn := notMem_sideList_of_vertexOf hpre hM.isMonogon hM.isSimpleStrandPath hj
      (ζ := ζ) hde
    refine ⟨fun hK => absurd hK (hM.notMem_insideDarts_of_mem_pathStart hX hh ?_),
      fun hL => absurd hL hn⟩
    rw [X.pathStart_of_head? (List.head?_eq_some_head hM.isMonogon.isStrandPath.ne_nil),
      List.head_eq_getElem, ← hde]
    exact X.self_mem_vertexOf d
  · have hstep := strandStep_getElem hM.isMonogon.isStrandPath hj
    have hde' : X.vertexOf d = X.vertexOf (X.inv P[j]) := hde.trans hstep.vertexOf_eq
    rw [hM.mem_insideDarts_iff_mem_sideDarts hX hh hj (by rw [← hde']; exact X.self_mem_vertexOf d),
      insideList, mem_sideList_iff_of_vertexOf hpre hM.isMonogon hM.isSimpleStrandPath hj hde']

end IsConvexMonogon

end Inside

/-! ### The inside by reachability -/

section Reach

variable {X}

omit [Fintype H] [DecidableEq H] in
/-- A set closed under `σ` and the involution contains everything reachable from its darts. -/
private theorem mem_of_reach {T : Set H} (hrot : ∀ x ∈ T, X.rot x ∈ T)
    (hinv : ∀ x ∈ T, X.inv x ∈ T) {d e : H} (h : X.Reach d e) : d ∈ T → e ∈ T := by
  induction h with
  | refl => exact id
  | rot _ ih => exact fun hd => hrot _ (ih hd)
  | inv _ ih => exact fun hd => hinv _ (ih hd)

/-- The darts of a side list lie at vertices of darts of the strand path. -/
private theorem exists_mem_vertexOf_of_mem_sideList {P : List H} (hP : X.IsStrandPath P)
    {ζ : StrandSide} {d : H} (hd : d ∈ X.sideList ζ P) :
    ∃ e ∈ P, X.vertexOf d = X.vertexOf e := by
  obtain ⟨l, hl, hd⟩ := mem_sideList.1 hd
  exact ⟨_, List.getElem_mem hl,
    (vertexOf_of_mem_sideDarts hd).trans (strandStep_getElem hP hl).vertexOf_eq.symm⟩

/-- **The inside by reachability**: the inside darts of a convex monogon `M` form the smallest set
of darts containing the inside list and closed under the involution and under `σ^{±1}` at triple
points that are not vertices of darts of `M`. -/
@[cluster_algebras "lem_monogon_inside_reach"]
theorem IsConvexMonogon.insideDarts_eq_avoidingClosure (hX : X.IsTripleDiagram) {P : List H}
    {ζ : StrandSide} (hM : X.IsConvexMonogon P ζ) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) :
    (X.insideDarts P ζ h : Set H) = X.avoidingClosure P {d | d ∈ X.insideList ζ P} := by
  have hpre := hX.toIsPreTripleDiagram
  have h0 := hM.length_pos
  have hsub : {d | d ∈ X.insideList ζ P} ⊆ (X.insideDarts P ζ h : Set H) := fun d hd =>
    (hM.mem_insideDarts_iff_mem_insideList hX hh
      (exists_mem_vertexOf_of_mem_sideList hM.isMonogon.isStrandPath hd)).2 hd
  have hclosed : X.IsClosedOff P (X.insideDarts P ζ h : Set H) := by
    refine ⟨fun d hd => (inv_mem_insideDarts_iff hpre hh h0 d).2 hd,
      fun d hd hb havoid => ⟨?_, ?_⟩⟩
    · exact (mem_insideDarts_iff_of_forall_ne hX hM.isMonogon hh hb havoid
        (X.rot_mem_vertexOf d)).2 hd
    · exact (mem_insideDarts_iff_of_forall_ne hX hM.isMonogon hh hb havoid
        (X.rot_symm_mem_vertexOf d)).2 hd
  refine Set.Subset.antisymm (fun d hd => ?_) (X.avoidingClosure_subset hsub hclosed)
  by_contra hdS
  have hS := X.isClosedOff_avoidingClosure P {d | d ∈ X.insideList ζ P}
  have key : ∀ e, e ∈ X.insideDarts P ζ h → e ∉ X.avoidingClosure P {d | d ∈ X.insideList ζ P} →
      ¬X.IsBoundaryVertex (X.vertexOf e) ∧ ∀ e' ∈ P, X.vertexOf e ≠ X.vertexOf e' := by
    intro e heK heS
    refine ⟨fun hb => hM.notMem_insideDarts_of_isBoundaryVertex hX hh hb heK,
      fun e' he' hv => heS ?_⟩
    exact X.subset_avoidingClosure P _
      ((hM.mem_insideDarts_iff_mem_insideList hX hh ⟨e', he', hv⟩).1 heK)
  have hrot : ∀ e ∈ {e | e ∈ X.insideDarts P ζ h ∧
      e ∉ X.avoidingClosure P {d | d ∈ X.insideList ζ P}},
      X.rot e ∈ {e | e ∈ X.insideDarts P ζ h ∧
        e ∉ X.avoidingClosure P {d | d ∈ X.insideList ζ P}} := by
    rintro e ⟨heK, heS⟩
    obtain ⟨hb, havoid⟩ := key e heK heS
    refine ⟨(mem_insideDarts_iff_of_forall_ne hX hM.isMonogon hh hb havoid
      (X.rot_mem_vertexOf e)).2 heK, fun hS' => heS ?_⟩
    have := (hS.2 _ hS' (by rwa [X.vertexOf_rot]) (by rwa [X.vertexOf_rot])).2
    rwa [Equiv.symm_apply_apply] at this
  have hinv : ∀ e ∈ {e | e ∈ X.insideDarts P ζ h ∧
      e ∉ X.avoidingClosure P {d | d ∈ X.insideList ζ P}},
      X.inv e ∈ {e | e ∈ X.insideDarts P ζ h ∧
        e ∉ X.avoidingClosure P {d | d ∈ X.insideList ζ P}} := by
    rintro e ⟨heK, heS⟩
    refine ⟨(inv_mem_insideDarts_iff hpre hh h0 e).2 heK, fun hS' => heS ?_⟩
    have := hS.1 _ hS'
    rwa [hpre.inv_inv_apply] at this
  have hT := mem_of_reach hrot hinv (hX.toIsDiskMap.toIsConnected.reach d (P[0]'h0)) ⟨hd, hdS⟩
  exact ((mem_insideDarts h0).1 hT.1).2.1 (List.getElem_mem h0)

/-- At the vertices of a monogon `M`, the darts off `M` and off the `ζ` list of `M` take the
value of the other side of `M`. -/
private theorem subset_setOf_eq_otherSide (hX : X.IsTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {ζ : StrandSide} (h0 : 0 < P.length)
    (hc' : X.IsInsideCorner ζ P[0] P[P.length - 1]) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) {ω' : ℤ}
    (hω'def : ω' = h (X.toFaceOrbit P[0]) + if ζ = .right then 1 else 0) :
    {d | (∃ e ∈ P, X.vertexOf d = X.vertexOf e) ∧ d ∉ P ∧ X.inv d ∉ P ∧
      d ∉ X.sideList ζ P} ⊆ {d | d ∉ P ∧ X.inv d ∉ P ∧ h (X.toFaceOrbit d) = ω'} := by
  have hpre := hX.toIsPreTripleDiagram
  have hx := hP.vertexOf_inv_last h0
  rintro d ⟨⟨e, he, hde⟩, hd1, hd2, hd3⟩
  refine ⟨hd1, hd2, ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  rcases j with _ | j
  · have htrip := hP.not_isBoundaryVertex_vertexOf_inv_last h0
    have hdx : d ∈ X.vertexOf (X.inv P[P.length - 1]) := by
      rw [hx.1, ← hde]
      exact X.self_mem_vertexOf d
    obtain ⟨k, hk, rfl⟩ := exists_rot_pow_eq hpre htrip hdx
    obtain ⟨h1, h2, -⟩ := rot_pow_inv_last_mem hpre hP hs h0 hc' hk
    rw [h1] at hd1
    rw [h2] at hd2
    rw [hh.apply_rot_pow_inv_last hX hP hs h0 hc' k hk, hω'def]
    cases ζ with
    | right =>
      simp only [cornerExp] at hd1 ⊢
      rw [if_neg (by omega)]
      simp
    | left =>
      simp only [cornerExp] at hd1 ⊢
      rw [if_pos (by omega)]
      simp
  · have hstep := strandStep_getElem hP.isStrandPath hj
    have hde' : X.vertexOf d = X.vertexOf (X.inv P[j]) := hde.trans hstep.vertexOf_eq
    have htrip : ¬X.IsBoundaryVertex (X.vertexOf (X.inv P[j])) := hstep.1
    have hdz : d ∈ X.vertexOf (X.inv P[j]) := by
      rw [← hde']
      exact X.self_mem_vertexOf d
    rw [mem_sideList_iff_of_vertexOf hpre hP hs hj hde'] at hd3
    obtain ⟨k, hk, rfl⟩ := exists_rot_pow_eq hpre htrip hdz
    obtain ⟨h1, h2, -⟩ := rot_pow_inv_getElem_mem hpre hP hs hj hk
    have hsd := rot_pow_mem_sideDarts hpre htrip hk
    rw [h1] at hd1
    rw [h2] at hd2
    rw [hh.apply_rot_pow_inv' hX hP hs hj k hk, hω'def]
    cases ζ with
    | right =>
      rw [hsd.1] at hd3
      rw [if_neg (by omega), if_pos rfl]
    | left =>
      rw [hsd.2] at hd3
      rw [if_pos (by omega), if_neg (by decide)]

/-- The darts off a monogon `M` of a given value of the winding function form a set closed
off `M`. -/
private theorem isClosedOff_setOf_eq (hX : X.IsTripleDiagram) {P : List H} (hP : X.IsMonogon P)
    {h : X.faceOrbits → ℤ} (hh : X.IsMonogonWindingFunction P h) (ω' : ℤ) :
    X.IsClosedOff P {d | d ∉ P ∧ X.inv d ∉ P ∧ h (X.toFaceOrbit d) = ω'} := by
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  refine ⟨fun d hd => ⟨hd.2.1, by rw [hpre.inv_inv_apply]; exact hd.1, ?_⟩,
    fun d hd hb havoid => ⟨?_, ?_⟩⟩
  · have := hh.sub_eq d
    rw [X.monogonCycle_eq_zero_of_notMem hd.1 hd.2.1] at this
    rw [← hd.2.2]
    linarith
  · obtain ⟨h1, h2⟩ := hP.notMem_of_forall_ne hpre fun e he => by
      rw [X.vertexOf_rot]; exact havoid e he
    refine ⟨h1, h2, ?_⟩
    rw [hh.apply_rot hinv, X.monogonCycle_eq_zero_of_notMem hd.1 hd.2.1, add_zero]
    exact hd.2.2
  · have hv : X.vertexOf (X.rot.symm d) = X.vertexOf d :=
      X.vertexOf_eq_of_mem (X.rot_symm_mem_vertexOf d)
    obtain ⟨h1, h2⟩ := hP.notMem_of_forall_ne hpre fun e he => by
      rw [hv]; exact havoid e he
    refine ⟨h1, h2, ?_⟩
    have := hh.apply_rot hinv (X.rot.symm d)
    rw [Equiv.apply_symm_apply, X.monogonCycle_eq_zero_of_notMem h1 h2, add_zero] at this
    rw [← this]
    exact hd.2.2

/-- Two sets closed off a monogon `M`, avoiding the endpoints and together covering the darts at
the vertices of `M` off `M`, cannot exist: the endpoint `0` is reached from `M`. -/
private theorem false_of_isClosedOff_cover (hX : X.IsTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) {S A B : Set H} (hSA : S ⊆ A)
    (hB : {d | (∃ e ∈ P, X.vertexOf d = X.vertexOf e) ∧ d ∉ P ∧ X.inv d ∉ P ∧ d ∉ S} ⊆ B)
    (hAc : X.IsClosedOff P A) (hBc : X.IsClosedOff P B)
    (hAb : ∀ d ∈ A, ¬X.IsBoundaryVertex (X.vertexOf d))
    (hBb : ∀ d ∈ B, ¬X.IsBoundaryVertex (X.vertexOf d)) : False := by
  have hpre := hX.toIsPreTripleDiagram
  have h0 : 0 < P.length := List.length_pos_iff.2 hP.isStrandPath.ne_nil
  have hatM : ∀ d, (∃ e ∈ P, X.vertexOf d = X.vertexOf e) →
      d ∈ P ∨ X.inv d ∈ P ∨ d ∈ A ∨ d ∈ B := by
    intro d hd
    by_cases h1 : d ∈ P
    · exact Or.inl h1
    by_cases h2 : X.inv d ∈ P
    · exact Or.inr (Or.inl h2)
    by_cases h3 : d ∈ S
    · exact Or.inr (Or.inr (Or.inl (hSA h3)))
    · exact Or.inr (Or.inr (Or.inr (hB ⟨hd, h1, h2, h3⟩)))
  have hPatM : ∀ d, d ∈ P ∨ X.inv d ∈ P → ∃ e ∈ P, X.vertexOf d = X.vertexOf e := by
    rintro d (hd | hd)
    · exact ⟨d, hd, rfl⟩
    · obtain ⟨e', he', hv⟩ := hP.exists_vertexOf_inv_eq hd
      rw [hpre.inv_inv_apply] at hv
      exact ⟨e', he', hv⟩
  have hrotS : ∀ d ∈ {d | (∃ e ∈ P, X.vertexOf d = X.vertexOf e) ∨ d ∈ A ∨ d ∈ B},
      X.rot d ∈ {d | (∃ e ∈ P, X.vertexOf d = X.vertexOf e) ∨ d ∈ A ∨ d ∈ B} := by
    intro d hd
    by_cases hm : ∃ e ∈ P, X.vertexOf d = X.vertexOf e
    · obtain ⟨e, he, hv⟩ := hm
      exact Or.inl ⟨e, he, by rw [X.vertexOf_rot]; exact hv⟩
    have hm' : ∀ e ∈ P, X.vertexOf d ≠ X.vertexOf e := fun e he hv => hm ⟨e, he, hv⟩
    rcases hd with hd | hd | hd
    · exact absurd hd hm
    · exact Or.inr (Or.inl (hAc.2 d hd (hAb d hd) hm').1)
    · exact Or.inr (Or.inr (hBc.2 d hd (hBb d hd) hm').1)
  have hinvS : ∀ d ∈ {d | (∃ e ∈ P, X.vertexOf d = X.vertexOf e) ∨ d ∈ A ∨ d ∈ B},
      X.inv d ∈ {d | (∃ e ∈ P, X.vertexOf d = X.vertexOf e) ∨ d ∈ A ∨ d ∈ B} := by
    rintro d (hd | hd | hd)
    · rcases hatM d hd with h1 | h1 | h1 | h1
      · exact Or.inl (hPatM _ (Or.inr (by rwa [hpre.inv_inv_apply])))
      · exact Or.inl (hPatM _ (Or.inl h1))
      · exact Or.inr (Or.inl (hAc.1 d h1))
      · exact Or.inr (Or.inr (hBc.1 d h1))
    · exact Or.inr (Or.inl (hAc.1 d hd))
    · exact Or.inr (Or.inr (hBc.1 d hd))
  have hb1 := hX.one_le
  have hbd : X.IsBoundaryVertex (X.vertexOf (X.endDart ⟨0, by omega⟩)) :=
    (X.mem_boundaryVertices.1 (hX.endpoint_mem _)).2
  rcases mem_of_reach hrotS hinvS
      (hX.toIsDiskMap.toIsConnected.reach (P[0]'h0) (X.endDart ⟨0, by omega⟩))
      (Or.inl ⟨P[0], List.getElem_mem h0, rfl⟩) with ⟨e, he, hv⟩ | hd | hd
  · exact (hP.not_isBoundaryVertex he).1 (hv ▸ hbd)
  · exact hAb _ hd hbd
  · exact hBb _ hd hbd

/-- **Convexity by reachability**. Let `M = (e₁, …, e_m)` be a monogon that is a simple strand path
and `ζ` a side such that `σ(ē_m) = e₁` if `ζ` is right and `σ(e₁) = ē_m` if `ζ` is left. If no
dart of the smallest set containing the `ζ` list of `M` and closed under the involution and under
`σ^{±1}` at triple points that are not vertices of darts of `M` lies at an endpoint, then `M` is
convex with inside `ζ`. -/
@[cluster_algebras "lem_monogon_convex_criterion"]
theorem isConvexMonogon_of_avoidingClosure (hX : X.IsTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {ζ : StrandSide}
    (hc : ∀ e₁ ∈ P.head?, ∀ eₘ ∈ P.getLast?, X.IsInsideCorner ζ e₁ eₘ)
    (hK : ∀ d ∈ X.avoidingClosure P {d | d ∈ X.sideList ζ P},
      ¬X.IsBoundaryVertex (X.vertexOf d)) :
    X.IsConvexMonogon P ζ := by
  have h0 : 0 < P.length := List.length_pos_iff.2 hP.isStrandPath.ne_nil
  have hc' : X.IsInsideCorner ζ P[0] P[P.length - 1] :=
    hc _ (getElem_zero_mem_head? h0) _ (getElem_last_mem_getLast? h0)
  obtain ⟨h, hh, -⟩ := existsUnique_isMonogonWindingFunction hX hP hs
  have h00 := hh.apply_getElem hX hP hs h0
  refine ⟨hP, hs, hc, h, hh, fun e₁ he₁ => ?_⟩
  obtain rfl : e₁ = P[0] := by
    have := getElem_zero_mem_head? h0
    rw [Option.mem_def] at this he₁
    exact Option.some_injective _ (he₁.symm.trans this)
  intro hω
  -- the value `ω'` of the other side
  obtain ⟨ω', hω'def⟩ : ∃ ω' : ℤ, ω' = h (X.toFaceOrbit P[0]) + if ζ = .right then 1 else 0 :=
    ⟨_, rfl⟩
  have hω' : ω' ≠ 0 := by
    cases ζ
    · simp only [sideOrbit] at hω
      simp [hω'def, hω]
    · simp only [sideOrbit] at hω
      rw [h00.2] at hω
      simp only [hω'def, reduceCtorEq, if_false, add_zero]
      omega
  have hK'U := X.avoidingClosure_subset
    (subset_setOf_eq_otherSide hX hP hs h0 hc' hh hω'def) (isClosedOff_setOf_eq hX hP hh ω')
  exact false_of_isClosedOff_cover hX hP (S := {d | d ∈ X.sideList ζ P})
    (X.subset_avoidingClosure P _) (X.subset_avoidingClosure P _)
    (X.isClosedOff_avoidingClosure P _) (X.isClosedOff_avoidingClosure P _) hK
    fun d hd hb => hω' (by
      rw [← (hK'U hd).2.2]
      exact hh.apply_eq_zero_of_isBoundaryVertex' hX hP hb)

end Reach

/-! ### Cutting a monogon along a strand inside it -/

section Split

variable {X}

/-- A nonempty list of darts whose consecutive darts are linked, whose last dart is linked to its
first and whose darts have pairwise distinct vertices is a simple closed walk. -/
private theorem isSimpleClosedWalk_of_isChain {L : List H} (hne : L ≠ [])
    (hchain : L.IsChain fun d d' => X.vertexOf (X.inv d) = X.vertexOf d' ∧ d' ≠ X.inv d)
    (hlast : ∀ a ∈ L.getLast?, ∀ c ∈ L.head?,
      X.vertexOf (X.inv a) = X.vertexOf c ∧ c ≠ X.inv a)
    (hnodup : (L.map X.vertexOf).Nodup) : X.IsSimpleClosedWalk L.get := by
  have := hlast _ (List.getLast?_eq_some_getLast hne) _ (List.head?_eq_some_head hne)
  exact isSimpleClosedWalk_get hne hchain this.1 this.2 hnodup

/-- The vertices of the darts of a simple closed walk are pairwise distinct. -/
private theorem nodup_map_vertexOf {L : List H} (hw : X.IsSimpleClosedWalk L.get) :
    (L.map X.vertexOf).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  simp only [List.getElem_map] at hij
  have := hw.injective_vertexOf (a₁ := ⟨i, by simpa using i.2⟩) (a₂ := ⟨j, by simpa using j.2⟩) hij
  exact Fin.ext (by simpa using congrArg Fin.val this)

/-- A simple strand path has darts with pairwise distinct vertices. -/
theorem IsSimpleStrandPath.nodup_map_vertexOf {P : List H} (hs : X.IsSimpleStrandPath P) :
    (P.map X.vertexOf).Nodup := by
  obtain ⟨e, Q, rfl⟩ := List.exists_cons_of_ne_nil hs.isStrandPath.ne_nil
  rw [X.map_vertexOf_eq_cons_interiorPoints hs.isStrandPath.isChain]
  exact List.nodup_cons.2 ⟨hs.pathStart_notMem, hs.nodup⟩

/-- A monogon whose darts have pairwise distinct vertices is a simple strand path. -/
private theorem IsMonogon.isSimpleStrandPath_of_nodup {P : List H} (hP : X.IsMonogon P)
    (hn : (P.map X.vertexOf).Nodup) : X.IsSimpleStrandPath P := by
  obtain ⟨e, Q, rfl⟩ := List.exists_cons_of_ne_nil hP.isStrandPath.ne_nil
  rw [X.map_vertexOf_eq_cons_interiorPoints hP.isStrandPath.isChain] at hn
  refine ⟨hP.isStrandPath, (List.nodup_cons.1 hn).2, (List.nodup_cons.1 hn).1, ?_⟩
  rw [hP.pathEnd_eq]
  exact (List.nodup_cons.1 hn).1

private theorem inv_notMem_of_mem {L : List H} (hw : X.IsSimpleClosedWalk L.get) {d : H}
    (hd : d ∈ L) : X.inv d ∉ L := by
  intro h
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hd
  obtain ⟨j, hj⟩ := List.mem_iff_get.1 h
  exact hw.ne_inv_apply j i hj

private theorem walk_values_of_mem (hM : X.toDiskMap.IsDiskMap) {L : List H}
    (hw : X.IsSimpleClosedWalk L.get) {h : X.faceOrbits → ℤ}
    (hh : X.IsWindingFunction (X.walkCycle L.get) h) {d : H} (hd : d ∈ L) :
    h (X.toFaceOrbit (X.inv d)) = h (X.toFaceOrbit d) + 1 ∧
      (∀ f, h f = h (X.toFaceOrbit d) ∨ h f = h (X.toFaceOrbit d) + 1) ∧
      (0 = h (X.toFaceOrbit d) ∨ 0 = h (X.toFaceOrbit d) + 1) := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hd
  refine ⟨hh.walk_apply_inv hw i, hh.walk_values hM hw i, ?_⟩
  have := hh.walk_values hM hw i ⟨X.exterior, hM.exterior_mem_faceOrbits⟩
  rwa [hh.apply_exterior ⟨X.exterior, hM.exterior_mem_faceOrbits⟩ rfl] at this

private theorem walk_apply_eq_of_mem (hinv : Function.Involutive X.inv) {L : List H}
    (hw : X.IsSimpleClosedWalk L.get) {h : X.faceOrbits → ℤ}
    (hh : X.IsWindingFunction (X.walkCycle L.get) h) {d d' : H} (hd : d ∈ L) (hd' : d' ∈ L) :
    h (X.toFaceOrbit d) = h (X.toFaceOrbit d') := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hd
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hd'
  exact hh.walk_apply_eq hinv hw i j

omit [Fintype H] in
private theorem monogonCycle_eq_sub {L : List H} {d : H} (h : ¬(d ∈ L ∧ X.inv d ∈ L)) :
    X.monogonCycle L d = (if d ∈ L then 1 else 0) - if X.inv d ∈ L then 1 else 0 := by
  unfold monogonCycle
  by_cases h1 : d ∈ L <;> by_cases h2 : X.inv d ∈ L <;> simp_all

private theorem cycle_add_aux {a₁ a₂ a₃ b₁ b₂ b₃ : Prop} [Decidable a₁] [Decidable a₂]
    [Decidable a₃] [Decidable b₁] [Decidable b₂] [Decidable b₃] (h₁₂ : ¬(a₁ ∧ a₂))
    (h₁₂' : ¬(b₁ ∧ b₂)) (h₃ : a₃ → ¬a₁ ∧ ¬a₂ ∧ ¬b₁ ∧ ¬b₂)
    (h₃' : b₃ → ¬a₁ ∧ ¬a₂ ∧ ¬b₁ ∧ ¬b₂) (h₃₃ : ¬(a₃ ∧ b₃)) :
    ((if a₁ ∨ a₂ then (1 : ℤ) else 0) - if b₁ ∨ b₂ then 1 else 0) =
      ((if a₂ ∨ a₃ then 1 else 0) - if b₂ ∨ b₃ then 1 else 0) +
        ((if a₁ ∨ b₃ then 1 else 0) - if b₁ ∨ a₃ then 1 else 0) := by
  by_cases ha₁ : a₁ <;> by_cases ha₂ : a₂ <;> by_cases ha₃ : a₃ <;> by_cases hb₁ : b₁ <;>
    by_cases hb₂ : b₂ <;> by_cases hb₃ : b₃ <;> simp_all

/-- The walk `M'` obtained by cutting a monogon along a strand inside it is simple. -/
private theorem isSimpleClosedWalk_drop_append_of_split (hpre : X.IsPreTripleDiagram)
    {P : List H} (hP : X.IsStrandPath P) (hw : X.IsSimpleClosedWalk P.get) {g₀ : H}
    {G' : List H} (hG : X.IsStrandPath (g₀ :: G')) {l : ℕ} (hl : l + 1 < P.length)
    (hstepx : X.StrandStep (P[P.length - 1]'(by omega)) g₀)
    (hvg₀ : X.vertexOf g₀ = X.vertexOf (P[0]'(by omega)))
    (hgjv : X.vertexOf (X.inv ((g₀ :: G').getLast (List.cons_ne_nil _ _))) = X.vertexOf P[l + 1])
    (hGn : (X.interiorPoints (g₀ :: G')).Nodup)
    (hGv : ∀ z ∈ X.interiorPoints (g₀ :: G'), ∀ e ∈ P, z ≠ X.vertexOf e)
    (hGP : ∀ g ∈ g₀ :: G', g ∉ P ∧ X.inv g ∉ P) :
    X.IsSimpleClosedWalk (P.drop (l + 1) ++ g₀ :: G').get := by
  have h0 : 0 < P.length := by omega
  have hGne : (g₀ :: G') ≠ [] := List.cons_ne_nil _ _
  have hPchain := hP.isChain.imp fun _ _ h => h.link hpre
  have hdropne : P.drop (l + 1) ≠ [] := by
    simp only [ne_eq, List.drop_eq_nil_iff, not_le]
    omega
  refine isSimpleClosedWalk_of_isChain (by simp) ?_ ?_ ?_
  · rw [List.isChain_append]
    refine ⟨hPchain.drop _, hG.isChain.imp fun _ _ h => h.link hpre, fun x hx' y hy => ?_⟩
    rw [List.getLast?_drop, if_neg (by omega), List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega), Option.mem_def, Option.some_inj] at hx'
    rw [List.head?_cons, Option.mem_def, Option.some_inj] at hy
    subst hx' hy
    exact hstepx.link hpre
  · intro a ha c hc
    rw [List.getLast?_append_of_ne_nil _ hGne, List.getLast?_eq_some_getLast hGne,
      Option.mem_def, Option.some_inj] at ha
    rw [List.head?_append_of_ne_nil _ hdropne, List.head?_drop,
      List.getElem?_eq_getElem (by omega), Option.mem_def, Option.some_inj] at hc
    subst ha hc
    refine ⟨hgjv, fun he => (hGP _ (List.getLast_mem hGne)).2 ?_⟩
    rw [← he]
    exact List.getElem_mem _
  · rw [List.map_append, X.map_vertexOf_eq_cons_interiorPoints hG.isChain, List.nodup_append]
    refine ⟨?_, List.nodup_cons.2 ⟨fun hmem => hGv _ hmem _ (List.getElem_mem h0) hvg₀, hGn⟩,
      ?_⟩
    · rw [List.map_drop]
      exact (nodup_map_vertexOf hw).sublist (List.drop_sublist _ _)
    · intro a ha c hc hac
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
      rw [List.getElem_drop] at hac
      rw [List.length_drop] at hi
      rcases List.mem_cons.1 hc with hc | hc
      · subst hc
        have := vertexOf_getElem_inj hw (by omega) h0 (hac.trans hvg₀)
        omega
      · subst hac
        exact hGv _ hc _ (List.getElem_mem _) rfl

/-- The vertices of the walk `C` obtained by cutting a monogon along a strand are distinct. -/
private theorem nodup_vertexOf_take_append_reverse_of_split {P : List H}
    (hw : X.IsSimpleClosedWalk P.get) {g₀ : H} {G' : List H} {l : ℕ} (hl : l + 1 < P.length)
    (hgjv : X.vertexOf (X.inv ((g₀ :: G').getLast (List.cons_ne_nil _ _))) = X.vertexOf P[l + 1])
    (hGn : (X.interiorPoints (g₀ :: G')).Nodup)
    (hGv : ∀ z ∈ X.interiorPoints (g₀ :: G'), ∀ e ∈ P, z ≠ X.vertexOf e) :
    ((P.take (l + 1) ++ (g₀ :: G').reverse.map X.inv).map X.vertexOf).Nodup := by
  have hGne : (g₀ :: G') ≠ [] := List.cons_ne_nil _ _
  have hPv := nodup_map_vertexOf hw
  have hGinv : (g₀ :: G').map (fun g => X.vertexOf (X.inv g)) =
      X.interiorPoints (g₀ :: G') ++ [X.vertexOf (X.inv ((g₀ :: G').getLast hGne))] := by
    conv_lhs => rw [← List.dropLast_append_getLast hGne]
    rw [List.map_append]
    rfl
  simp only [List.map_append, List.map_reverse, List.map_map]
  rw [List.nodup_append, List.nodup_reverse]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_take]
    exact hPv.sublist (List.take_sublist _ _)
  · rw [show X.vertexOf ∘ ⇑X.inv = fun g => X.vertexOf (X.inv g) from rfl, hGinv,
      List.nodup_append]
    refine ⟨hGn, List.nodup_singleton _, fun a ha c hc hac => ?_⟩
    rw [List.mem_singleton] at hc
    exact hGv _ ha _ (List.getElem_mem (show l + 1 < P.length by omega))
      (hac.trans (hc.trans hgjv))
  · intro a ha c hc hac
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
    rw [List.getElem_take] at hac
    rw [List.length_take] at hi
    rw [List.mem_reverse, show X.vertexOf ∘ ⇑X.inv = fun g => X.vertexOf (X.inv g) from rfl,
      hGinv, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | hc
    · subst hac
      exact hGv _ hc _ (List.getElem_mem _) rfl
    · subst hc
      have := vertexOf_getElem_inj hw (by omega) (show l + 1 < P.length by omega)
        (hac.trans hgjv)
      omega

/-- The walk `C` obtained by cutting a monogon along a strand inside it is simple. -/
private theorem isSimpleClosedWalk_take_append_reverse_of_split (hpre : X.IsPreTripleDiagram)
    {P : List H} (hP : X.IsStrandPath P) (hw : X.IsSimpleClosedWalk P.get) {g₀ : H}
    {G' : List H} (hG : X.IsStrandPath (g₀ :: G')) {l : ℕ} (hl : l + 1 < P.length)
    (hvg₀ : X.vertexOf g₀ = X.vertexOf (P[0]'(by omega)))
    (hgl : X.vertexOf (X.inv ((g₀ :: G').getLast (List.cons_ne_nil _ _))) =
      X.vertexOf (X.inv (P[l]'(by omega))))
    (hgjv : X.vertexOf (X.inv ((g₀ :: G').getLast (List.cons_ne_nil _ _))) = X.vertexOf P[l + 1])
    (hGn : (X.interiorPoints (g₀ :: G')).Nodup)
    (hGv : ∀ z ∈ X.interiorPoints (g₀ :: G'), ∀ e ∈ P, z ≠ X.vertexOf e)
    (hGP : ∀ g ∈ g₀ :: G', g ∉ P ∧ X.inv g ∉ P) :
    X.IsSimpleClosedWalk (P.take (l + 1) ++ (g₀ :: G').reverse.map X.inv).get := by
  have h0 : 0 < P.length := by omega
  have hGne : (g₀ :: G') ≠ [] := List.cons_ne_nil _ _
  have htakene : P.take (l + 1) ≠ [] := fun h => by
    rw [List.take_eq_nil_iff] at h
    rcases h with h | h
    · omega
    · simp [h] at h0
  refine isSimpleClosedWalk_of_isChain (by simp) ?_ ?_ ?_
  · rw [List.isChain_append, List.isChain_map, List.isChain_reverse]
    refine ⟨(hP.isChain.imp fun _ _ h => h.link hpre).take _, hG.isChain.imp fun a c hac => ?_,
      fun x hx' y hy => ?_⟩
    · refine ⟨by rw [hpre.inv_inv_apply]; exact hac.vertexOf_eq, fun he => (hac.link hpre).2 ?_⟩
      rw [hpre.inv_inv_apply] at he
      exact he.symm
    · rw [List.getLast?_take, if_neg (by omega), Nat.add_sub_cancel,
        List.getElem?_eq_getElem (by omega), Option.some_or, Option.mem_def,
        Option.some_inj] at hx'
      rw [List.head?_map, List.head?_reverse, List.getLast?_eq_some_getLast hGne,
        Option.map_some, Option.mem_def, Option.some_inj] at hy
      subst hx' hy
      refine ⟨hgl.symm, fun he => (hGP _ (List.getLast_mem hGne)).1 ?_⟩
      rw [X.inv.injective he]
      exact List.getElem_mem _
  · intro a ha c hc
    rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_map, List.getLast?_reverse,
      List.head?_cons, Option.map_some, Option.mem_def, Option.some_inj] at ha
    rw [List.head?_append_of_ne_nil _ htakene, List.head?_take, if_neg (by omega),
      List.head?_eq_getElem?, List.getElem?_eq_getElem h0, Option.mem_def,
      Option.some_inj] at hc
    subst ha hc
    refine ⟨by rw [hpre.inv_inv_apply]; exact hvg₀, fun he => (hGP _ List.mem_cons_self).1 ?_⟩
    rw [← hpre.inv_inv_apply g₀, ← he]
    exact List.getElem_mem _
  · exact nodup_vertexOf_take_append_reverse_of_split hw hl hgjv hGn hGv

/-- Cutting a monogon along a strand splits its cycle into the cycles of the two pieces. -/
private theorem monogonCycle_eq_add_of_split (hpre : X.IsPreTripleDiagram) {P G : List H}
    (k : ℕ) (hw : X.IsSimpleClosedWalk P.get) (hwM : X.IsSimpleClosedWalk (P.drop k ++ G).get)
    (hwC : X.IsSimpleClosedWalk (P.take k ++ G.reverse.map X.inv).get)
    (hGP : ∀ g ∈ G, g ∉ P ∧ X.inv g ∉ P) (d : H) :
    X.monogonCycle P d = X.monogonCycle (P.drop k ++ G) d +
      X.monogonCycle (P.take k ++ G.reverse.map X.inv) d := by
  have hPn : P.Nodup := List.nodup_iff_injective_get.2 hw.injective
  have hnot : ∀ {L : List H}, X.IsSimpleClosedWalk L.get → ∀ d, ¬(d ∈ L ∧ X.inv d ∈ L) :=
    fun hL d hd => inv_notMem_of_mem hL hd.1 hd.2
  have hmemR : ∀ e, e ∈ G.reverse.map X.inv ↔ X.inv e ∈ G := fun e => by
    rw [List.mem_map]
    refine ⟨?_, fun he => ⟨X.inv e, List.mem_reverse.2 he, hpre.inv_inv_apply e⟩⟩
    rintro ⟨a, ha, rfl⟩
    rw [hpre.inv_inv_apply]
    exact List.mem_reverse.1 ha
  have hmemP : ∀ e, e ∈ P ↔ e ∈ P.take k ∨ e ∈ P.drop k := fun e => by
    conv_lhs => rw [← List.take_append_drop k P]
    exact List.mem_append
  have htd : ∀ e, ¬(e ∈ P.take k ∧ e ∈ P.drop k) := by
    rintro e ⟨h1, h2⟩
    have := (List.take_append_drop k P).symm ▸ hPn
    exact (List.nodup_append.1 this).2.2 e h1 e h2 rfl
  rw [monogonCycle_eq_sub (hnot hw d), monogonCycle_eq_sub (hnot hwM d),
    monogonCycle_eq_sub (hnot hwC d)]
  simp only [List.mem_append, hmemP, hmemR, hpre.inv_inv_apply]
  refine cycle_add_aux (htd d) (htd (X.inv d)) (fun h3 => ?_) (fun h3 => ?_) ?_
  · obtain ⟨h1, h2⟩ := hGP _ h3
    exact ⟨fun h => h1 (List.mem_of_mem_take h), fun h => h1 (List.mem_of_mem_drop h),
      fun h => h2 (List.mem_of_mem_take h), fun h => h2 (List.mem_of_mem_drop h)⟩
  · obtain ⟨h1, h2⟩ := hGP _ h3
    rw [hpre.inv_inv_apply] at h2
    exact ⟨fun h => h2 (List.mem_of_mem_take h), fun h => h2 (List.mem_of_mem_drop h),
      fun h => h1 (List.mem_of_mem_take h), fun h => h1 (List.mem_of_mem_drop h)⟩
  · rintro ⟨h1, h2⟩
    exact hnot hwM d ⟨List.mem_append_right _ h1, List.mem_append_right _ h2⟩

private theorem ssubset_of_eq_sub (hX : X.IsTripleDiagram) {P C M : List H}
    (hw : X.IsSimpleClosedWalk P.get) {h : X.faceOrbits → ℤ}
    (hh : X.IsWindingFunction (X.walkCycle P.get) h)
    (hwC : X.IsSimpleClosedWalk C.get) {hC : X.faceOrbits → ℤ}
    (hhC : X.IsWindingFunction (X.walkCycle C.get) hC)
    (hwM : X.IsSimpleClosedWalk M.get) {h' : X.faceOrbits → ℤ}
    (hh' : X.IsWindingFunction (X.walkCycle M.get) h') (hh'f : ∀ f, h' f = h f - hC f)
    {e g : H} (he : e ∈ P) (heC : e ∈ C) (hgC : X.inv g ∈ C) (hgM : g ∈ M) {ω : ℤ}
    (hω : ω = h (X.toFaceOrbit e) ∨ ω = h (X.toFaceOrbit (X.inv e))) (hω0 : ω ≠ 0)
    (hg : h (X.toFaceOrbit g) = ω) :
    {f | h' f ≠ 0} ⊂ {f | h f ≠ 0} := by
  have hMd := hX.toIsDiskMap
  obtain ⟨hPinv, hPvals, hPzero⟩ := walk_values_of_mem hMd hw hh he
  obtain ⟨hCinv, hCvals, hCzero⟩ := walk_values_of_mem hMd hwC hhC heC
  have hCg := walk_apply_eq_of_mem hX.inv_involutive hwC hhC hgC heC
  have hCinvg := (walk_values_of_mem hMd hwC hhC hgC).1
  rw [hX.toIsPreTripleDiagram.inv_inv_apply] at hCinvg
  obtain ⟨-, hM'vals, hM'zero⟩ := walk_values_of_mem hMd hwM hh' hgM
  have hωw : ω = h (X.toFaceOrbit e) ∨ ω = h (X.toFaceOrbit e) + 1 :=
    hω.imp id fun hω => hω.trans hPinv
  have hμ := hh'f (X.toFaceOrbit g)
  have hsub : {f | h' f ≠ 0} ⊆ {f | h f ≠ 0} := by
    intro f hf hf0
    apply hf
    have := hPvals f
    have := hCvals f
    have := hM'vals f
    have := hh'f f
    omega
  rw [Set.ssubset_iff_of_subset hsub]
  have hP0inv := hh'f (X.toFaceOrbit (X.inv e))
  have hP0' := hh'f (X.toFaceOrbit e)
  rcases hPzero with hw0 | hw0
  · refine ⟨X.toFaceOrbit (X.inv e), ?_, ?_⟩
    · change h _ ≠ 0
      omega
    · change ¬(h' _ ≠ 0)
      omega
  · refine ⟨X.toFaceOrbit e, ?_, ?_⟩
    · change h _ ≠ 0
      omega
    · change ¬(h' _ ≠ 0)
      omega

/-- **Cutting a monogon along a strand inside it**. Let `M = (e₁, …, e_m)` be a monogon with vertex
`x` that is a simple strand path, with winding function `h`, and `ω` the nonzero one of
`h(f(e₁))`, `h(f(ē₁))`. Let `l ∈ [1, m - 1]` and
`G = (g₀, …, g_j)` a strand path with `g₀ = σ³(ē_m)` and `v(ḡ_j) = z_l`, whose interior points
are pairwise distinct and are not vertices of `M`, whose darts are neither darts of `M` nor
reverses of darts of `M`, and with `h(f(g_p)) = ω` for every `p`. Then
`M' = (e_{l+1}, …, e_m, g₀, …, g_j)` is a simple closed walk, and for its winding function `h'` the
set of orbits on which `h'` is nonzero is a proper subset of the set of orbits on which `h` is
nonzero. -/
@[cluster_algebras "lem_monogon_split_smaller"]
theorem ssubset_of_split (hX : X.IsTripleDiagram) {P : List H} (hP : X.IsMonogon P)
    (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ} (hh : X.IsMonogonWindingFunction P h)
    {l : ℕ} (hl1 : 1 ≤ l) (hl : l < P.length) {ω : ℤ}
    (hω : ω = h (X.toFaceOrbit (P[0]'(by omega))) ∨
      ω = h (X.toFaceOrbit (X.inv (P[0]'(by omega)))))
    (hω0 : ω ≠ 0) {G : List H} (hG : X.IsStrandPath G)
    (hG0 : G.head? = some ((X.rot ^ 3) (X.inv (P[P.length - 1]'(by omega)))))
    (hGl : X.pathEnd G = X.vertexOf (X.inv (P[l - 1]'(by omega))))
    (hGn : (X.interiorPoints G).Nodup)
    (hGv : ∀ z ∈ X.interiorPoints G, ∀ e ∈ P, z ≠ X.vertexOf e)
    (hGP : ∀ g ∈ G, g ∉ P ∧ X.inv g ∉ P) (hGh : ∀ g ∈ G, h (X.toFaceOrbit g) = ω) :
    X.IsSimpleClosedWalk (P.drop l ++ G).get ∧
      ∀ h' : X.faceOrbits → ℤ, X.IsWindingFunction (X.walkCycle (P.drop l ++ G).get) h' →
        {f | h' f ≠ 0} ⊂ {f | h f ≠ 0} := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hGl
  have hpre := hX.toIsPreTripleDiagram
  have hinv := hX.inv_involutive
  have hMd := hX.toIsDiskMap
  have h0 : 0 < P.length := by omega
  have hw := hP.isSimpleClosedWalk hpre hs
  have hhw := hh.isWindingFunction_walkCycle hpre hP hs
  have hx := hP.vertexOf_inv_last h0
  obtain ⟨g₀, G', rfl⟩ := List.exists_cons_of_ne_nil hG.ne_nil
  have hGne : (g₀ :: G') ≠ [] := List.cons_ne_nil _ _
  have hg₀ : g₀ = (X.rot ^ 3) (X.inv P[P.length - 1]) := by simpa using hG0
  have hstepx : X.StrandStep P[P.length - 1] g₀ :=
    ⟨hP.not_isBoundaryVertex_vertexOf_inv_last h0, hg₀⟩
  have hvg₀ : X.vertexOf g₀ = X.vertexOf P[0] := by rw [hstepx.vertexOf_eq, hx.1]
  have hg₀mem : g₀ ∈ g₀ :: G' := by simp
  have hpe : X.pathEnd (g₀ :: G') = X.vertexOf (X.inv ((g₀ :: G').getLast hGne)) :=
    X.pathEnd_of_getLast? (List.getLast?_eq_some_getLast hGne)
  have hstepl := strandStep_getElem hP.isStrandPath (show l + 1 < P.length by omega)
  have hgjv : X.vertexOf (X.inv ((g₀ :: G').getLast hGne)) = X.vertexOf P[l + 1] := by
    rw [← hpe, hGl, hstepl.vertexOf_eq]
  have hwM' := isSimpleClosedWalk_drop_append_of_split hpre hP.isStrandPath hw hG
    (by omega) hstepx hvg₀ hgjv hGn hGv hGP
  have hwC := isSimpleClosedWalk_take_append_reverse_of_split hpre hP.isStrandPath hw hG
    (by omega) hvg₀ (hpe.symm.trans hGl) hgjv hGn hGv hGP
  have hcyc := monogonCycle_eq_add_of_split hpre (l + 1) hw hwM' hwC hGP
  obtain ⟨hC, hhC, -⟩ := hMd.existsUnique_isWindingFunction_walkCycle hwC
  refine ⟨hwM', fun h' hh' => ?_⟩
  have hcM' := X.walkCycle_get_eq_monogonCycle hinv hwM'
  have hcC := X.walkCycle_get_eq_monogonCycle hinv hwC
  have hdiff : X.IsWindingFunction (X.walkCycle (P.drop (l + 1) ++ g₀ :: G').get)
      (fun f => h f - hC f) := by
    refine ⟨fun f hf => by simp only [hh.apply_exterior f hf, hhC.apply_exterior f hf, sub_zero],
      fun d => ?_⟩
    have a := hh.sub_eq d
    have c := hhC.sub_eq d
    rw [hcC] at c
    rw [hcM']
    have := hcyc d
    linarith
  have hh'f : ∀ f, h' f = h f - hC f := fun f => by rw [hh'.unique hMd hdiff]
  have hP0C : P[0] ∈ P.take (l + 1) ++ (g₀ :: G').reverse.map X.inv := by
    apply List.mem_append_left
    rw [List.mem_iff_getElem]
    exact ⟨0, by simp only [List.length_take]; omega, by simp⟩
  exact ssubset_of_eq_sub hX hw hhw hwC hhC hwM' hh' hh'f (List.getElem_mem h0) hP0C
    (List.mem_append_right _ (List.mem_map.2 ⟨g₀, List.mem_reverse.2 hg₀mem, rfl⟩))
    (List.mem_append_right _ hg₀mem) hω hω0 (hGh g₀ hg₀mem)

end Split

/-! ### Convex monogons exist -/

section Exists

variable {X}

omit [Fintype H] [DecidableEq H] in
private theorem getElem_of_eq_idx {L : List H} {a c : ℕ} (h : a = c) (ha : a < L.length) :
    L[a] = L[c]'(h ▸ ha) := by
  subst h
  rfl

omit [Fintype H] [DecidableEq H] in
private theorem eq_getElem_zero_of_mem_head? {P : List H} (h0 : 0 < P.length) {e : H}
    (he : e ∈ P.head?) : e = P[0] := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0, Option.mem_def,
    Option.some_inj] at he
  exact he.symm

omit [Fintype H] [DecidableEq H] in
private theorem eq_getElem_last_of_mem_getLast? {P : List H} (h0 : 0 < P.length) {e : H}
    (he : e ∈ P.getLast?) : e = P[P.length - 1] := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), Option.mem_def,
    Option.some_inj] at he
  exact he.symm

/-- Reading a strand path backwards: `e_s = (σ³ e_{s+1})̄`. -/
private theorem getElem_eq_inv_rot_pow_three (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsStrandPath P) {s : ℕ} (hs : s + 1 < P.length) :
    P[s] = X.inv ((X.rot ^ 3) P[s + 1]) := by
  have hstep := strandStep_getElem hP hs
  rw [hstep.2, hX.rot_pow_three_rot_pow_three hstep.1, hX.inv_inv_apply]

/-- If two darts of a strand path coincide, its first dart recurs. -/
private theorem getElem_zero_eq_of_getElem_eq (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsStrandPath P) {a c : ℕ} (hac : a < c) (hc : c < P.length) (heq : P[a] = P[c]) :
    P[0] = P[c - a] := by
  have key : ∀ t, t ≤ a → P[a - t]'(by omega) = P[c - t]'(by omega) := by
    intro t
    induction t with
    | zero =>
      intro _
      simpa using heq
    | succ t ih =>
      intro ht
      rw [getElem_eq_inv_rot_pow_three hX hP (s := a - (t + 1)) (by omega),
        getElem_eq_inv_rot_pow_three hX hP (s := c - (t + 1)) (by omega),
        ← getElem_of_eq_idx (show a - t = a - (t + 1) + 1 by omega) (by omega),
        ← getElem_of_eq_idx (show c - t = c - (t + 1) + 1 by omega) (by omega), ih (by omega)]
  simpa using key a le_rfl

/-- A monogon whose first dart recurs at position `δ` gives the shorter monogon `P.drop δ`. -/
private theorem IsMonogon.drop_of_getElem_eq {P : List H} (hP : X.IsMonogon P) {δ : ℕ}
    (hδ : δ < P.length) (heq : P[0] = P[δ]) : X.IsMonogon (P.drop δ) := by
  have h0 : 0 < P.length := by omega
  have hhead : (P.drop δ).head? = P.head? := by
    rw [List.head?_drop, List.getElem?_eq_getElem hδ, ← heq, List.head?_eq_getElem?,
      List.getElem?_eq_getElem h0]
  have hlast : (P.drop δ).getLast? = P.getLast? := by
    rw [List.getLast?_drop, if_neg (by omega)]
  have hS : X.pathStart (P.drop δ) = X.pathStart P := by simp only [pathStart, hhead]
  have hE : X.pathEnd (P.drop δ) = X.pathEnd P := by simp only [pathEnd, hlast]
  refine ⟨⟨by rw [Ne, List.drop_eq_nil_iff]; omega,
    fun e he => hP.isStrandPath.notMem_bdry e (List.mem_of_mem_drop he),
    fun e he => hP.isStrandPath.isOut_eq_true e (List.mem_of_mem_drop he),
    hP.isStrandPath.isChain.drop δ⟩, hS ▸ hP.pathStart_mem, by rw [hS, hE]; exact hP.pathEnd_eq,
    ?_⟩
  rw [hhead, hlast]
  exact hP.inv_ne

/-- A stretch `(e_{s+1}, …, e_{s+t})` of a strand path running from a triple point back to it
along a different pass is a monogon. -/
private theorem isMonogon_drop_take {P : List H} (hP : X.IsStrandPath P) {s t : ℕ} (ht : 1 ≤ t)
    (hst : s + t ≤ P.length) (htrip : ¬X.IsBoundaryVertex (X.vertexOf (P[s]'(by omega))))
    (hv : X.vertexOf (X.inv (P[s + t - 1]'(by omega))) = X.vertexOf (P[s]'(by omega)))
    (hne : X.inv (P[s + t - 1]'(by omega)) ≠ (X.rot ^ 3) (P[s]'(by omega))) :
    X.IsMonogon ((P.drop s).take t) ∧ ((P.drop s).take t).length = t := by
  have hhead : ((P.drop s).take t).head? = some (P[s]'(by omega)) := by
    rw [List.head?_take, if_neg (by omega), List.head?_drop, List.getElem?_eq_getElem]
  have hlast : ((P.drop s).take t).getLast? = some (P[s + t - 1]'(by omega)) := by
    rw [List.getLast?_take, if_neg (by omega), List.getElem?_drop,
      show s + (t - 1) = s + t - 1 by omega, List.getElem?_eq_getElem (by omega), Option.some_or]
  refine ⟨⟨⟨fun h => by simp [h] at hhead,
    fun e he => hP.notMem_bdry e (List.mem_of_mem_drop (List.mem_of_mem_take he)),
    fun e he => hP.isOut_eq_true e (List.mem_of_mem_drop (List.mem_of_mem_take he)),
    (hP.isChain.drop s).take t⟩, ?_, ?_, ?_⟩,
    by simp only [List.length_take, List.length_drop]; omega⟩
  · rw [X.pathStart_of_head? hhead]
    exact X.vertexOf_mem_internalVertices.2 htrip
  · rw [X.pathStart_of_head? hhead, X.pathEnd_of_getLast? hlast, hv]
  · intro e₁ he₁ eₘ heₘ
    rw [hhead, Option.mem_def, Option.some_inj] at he₁
    rw [hlast, Option.mem_def, Option.some_inj] at heₘ
    subst he₁ heₘ
    exact hne

/-- In a monogon of minimal length, the first dart does not recur. -/
private theorem IsMonogon.getElem_zero_ne_of_minimal {P : List H} (hP : X.IsMonogon P)
    (hmin : ∀ Q, X.IsMonogon Q → P.length ≤ Q.length) {δ : ℕ} (hδ0 : 0 < δ)
    (hδ : δ < P.length) : P[0]'(by omega) ≠ P[δ] := by
  intro heq
  have := hmin _ (hP.drop_of_getElem_eq hδ heq)
  simp only [List.length_drop] at this
  omega

/-- In a monogon of minimal length, no two interior points coincide. -/
private theorem IsMonogon.vertexOf_inv_getElem_ne_of_minimal (hX : X.IsPreTripleDiagram)
    {P : List H} (hP : X.IsMonogon P) (hmin : ∀ Q, X.IsMonogon Q → P.length ≤ Q.length)
    {a c : ℕ} (hac : a < c) (hc : c + 1 < P.length) :
    X.vertexOf (X.inv (P[a]'(by omega))) ≠ X.vertexOf (X.inv P[c]) := by
  intro hv
  by_cases heq : P[a] = P[c]
  · exact hP.getElem_zero_ne_of_minimal hmin (δ := c - a) (by omega) (by omega)
      (getElem_zero_eq_of_getElem_eq hX hP.isStrandPath hac (by omega) heq)
  · have hstep := strandStep_getElem hP.isStrandPath (show a + 1 < P.length by omega)
    have hQ := isMonogon_drop_take hP.isStrandPath (s := a + 1) (t := c - a) (by omega)
      (by omega) (by rw [hstep.vertexOf_eq]; exact hstep.1)
      (by
        rw [← getElem_of_eq_idx (show c = a + 1 + (c - a) - 1 by omega) (by omega),
          hstep.vertexOf_eq]
        exact hv.symm)
      (by
        rw [← getElem_of_eq_idx (show c = a + 1 + (c - a) - 1 by omega) (by omega)]
        intro h
        apply heq
        rw [getElem_eq_inv_rot_pow_three hX hP.isStrandPath (s := a) (by omega), ← h,
          hX.inv_inv_apply])
    have := hmin _ hQ.1
    rw [hQ.2] at this
    omega

/-- In a monogon of minimal length, no interior point is the starting vertex. -/
private theorem IsMonogon.vertexOf_inv_getElem_ne_start_of_minimal (hX : X.IsPreTripleDiagram)
    {P : List H} (hP : X.IsMonogon P) (hmin : ∀ Q, X.IsMonogon Q → P.length ≤ Q.length)
    {a : ℕ} (ha : a + 1 < P.length) :
    X.vertexOf (X.inv P[a]) ≠ X.vertexOf (P[0]'(by omega)) := by
  have hx := hP.vertexOf_inv_last (show 0 < P.length by omega)
  intro hv
  by_cases heq : P[0] = P[a + 1]
  · exact hP.getElem_zero_ne_of_minimal hmin (by omega) ha heq
  · have hQ := isMonogon_drop_take hP.isStrandPath (s := 0) (t := a + 1) (by omega) (by omega)
      hx.2
      (by
        rw [← getElem_of_eq_idx (show a = 0 + (a + 1) - 1 by omega) (by omega)]
        exact hv)
      (by
        rw [← getElem_of_eq_idx (show a = 0 + (a + 1) - 1 by omega) (by omega)]
        intro h
        apply heq
        have hstep := strandStep_getElem hP.isStrandPath ha
        rw [hstep.2, h, hX.rot_pow_three_rot_pow_three hx.2])
    have := hmin _ hQ.1
    rw [hQ.2] at this
    omega

/-- **A shortest monogon is simple**: a triple diagram with a monogon has a monogon that is a
simple strand path. -/
private theorem exists_isMonogon_isSimpleStrandPath (hX : X.IsPreTripleDiagram)
    (hmono : X.HasMonogon) : ∃ P, X.IsMonogon P ∧ X.IsSimpleStrandPath P := by
  classical
  have hex : ∃ n, ∃ P, X.IsMonogon P ∧ P.length = n := by
    obtain ⟨P, hP⟩ := hmono
    exact ⟨_, P, hP, rfl⟩
  obtain ⟨P, hP, hPn⟩ := Nat.find_spec hex
  have hmin : ∀ Q, X.IsMonogon Q → P.length ≤ Q.length := fun Q hQ =>
    hPn ▸ Nat.find_min' hex ⟨Q, hQ, rfl⟩
  have h0 : 0 < P.length := List.length_pos_iff.2 hP.isStrandPath.ne_nil
  have hmem : X.vertexOf P[0] ∉ X.interiorPoints P := by
    intro hm
    obtain ⟨e, he, hv⟩ := List.mem_map.1 hm
    obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 he
    rw [List.getElem_dropLast] at hv
    rw [List.length_dropLast] at ha
    exact hP.vertexOf_inv_getElem_ne_start_of_minimal hX hmin (a := a) (by omega) hv
  have hS : X.pathStart P = X.vertexOf P[0] := by
    rw [X.pathStart_of_head? (List.head?_eq_some_head hP.isStrandPath.ne_nil),
      List.head_eq_getElem]
  refine ⟨P, hP, hP.isStrandPath, ?_, by rw [hS]; exact hmem,
    by rw [hP.pathEnd_eq, hS]; exact hmem⟩
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  have hi := i.2
  have hj := j.2
  simp only [interiorPoints, List.length_map, List.length_dropLast] at hi hj
  simp only [interiorPoints, List.getElem_map, List.getElem_dropLast] at hij
  by_contra hne
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact hP.vertexOf_inv_getElem_ne_of_minimal hX hmin hlt (by omega) hij
  · exact hP.vertexOf_inv_getElem_ne_of_minimal hX hmin hlt (by omega) hij.symm

/-- The corner of a monogon: `ē_m = σ^{±1}(e₁)`, so the corner condition holds on one side. -/
private theorem IsMonogon.exists_isInsideCorner (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (h0 : 0 < P.length) :
    ∃ ζ, X.IsInsideCorner ζ P[0] P[P.length - 1] := by
  have hx := hP.vertexOf_inv_last h0
  have hmem : X.inv P[P.length - 1] ∈ X.vertexOf P[0] := by
    rw [← hx.1]
    exact X.self_mem_vertexOf _
  obtain ⟨j, hj, hjeq⟩ := exists_rot_pow_eq hX hx.2 hmem
  have hout0 := hP.isStrandPath.isOut_eq_true _ (List.getElem_mem h0)
  have hlB := hP.isStrandPath.notMem_bdry _
    (List.getElem_mem (show P.length - 1 < P.length by omega))
  have houtl := hP.isStrandPath.isOut_eq_true _
    (List.getElem_mem (show P.length - 1 < P.length by omega))
  have hinvout : X.isOut (X.inv P[P.length - 1]) = false := by
    rw [hX.isOut_inv_apply hlB, houtl]
    rfl
  have hpar := hX.isOut_rot_pow_apply hx.2 j
  rw [← hjeq, hinvout, hout0] at hpar
  have h3 : j ≠ 3 := by
    rintro rfl
    exact hP.inv_ne _ (getElem_zero_mem_head? h0) _ (getElem_last_mem_getLast? h0) hjeq
  have hodd : ¬Even j := by
    intro he
    rw [if_pos he] at hpar
    exact absurd hpar (by simp)
  interval_cases j
  · exact absurd (by decide) hodd
  · refine ⟨.left, ?_⟩
    change X.rot P[0] = X.inv P[P.length - 1]
    rw [hjeq, pow_one]
  · exact absurd (by decide) hodd
  · exact absurd rfl h3
  · exact absurd (by decide) hodd
  · refine ⟨.right, ?_⟩
    change X.rot (X.inv P[P.length - 1]) = P[0]
    rw [hjeq, ← Equiv.Perm.mul_apply, ← pow_succ']
    exact hX.rot_pow_six_apply hx.2

omit [Fintype H] [DecidableEq H] in
private theorem head?_map_range' (k : ℕ → H) (s : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    ((List.range' s t).map k).head? = some (k s) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp [List.range'_succ]

omit [Fintype H] [DecidableEq H] in
private theorem getLast?_map_range' (k : ℕ → H) (s : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    ((List.range' s t).map k).getLast? = some (k (s + (t - 1))) := by
  rw [List.getLast?_eq_getElem?]
  simp [show t - 1 < t by omega]

omit [Fintype H] [DecidableEq H] in
private theorem forall_mem_map_range' {k : ℕ → H} {p : H → Prop} {n s t : ℕ}
    (hk : ∀ j ≤ n, p (k j)) (hst : s + t ≤ n + 1) : ∀ g ∈ (List.range' s t).map k, p g := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
  rw [List.mem_range'_1] at hj
  exact hk j (by omega)

private theorem getElem_interiorPoints_map_range' {k : ℕ → H} {s t q : ℕ}
    (hq : q < (X.interiorPoints ((List.range' s t).map k)).length) :
    (X.interiorPoints ((List.range' s t).map k))[q] = X.vertexOf (X.inv (k (s + q))) := by
  simp [interiorPoints, List.getElem_dropLast]

private theorem length_interiorPoints_map_range' (k : ℕ → H) (s t : ℕ) :
    (X.interiorPoints ((List.range' s t).map k)).length = t - 1 := by
  simp [interiorPoints]

private theorem nodup_interiorPoints_map_range' {k : ℕ → H} {s t : ℕ}
    (hk : ∀ p q, p < q → q + 1 < t →
      X.vertexOf (X.inv (k (s + p))) ≠ X.vertexOf (X.inv (k (s + q)))) :
    (X.interiorPoints ((List.range' s t).map k)).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro p q hpq
  have e1 := getElem_interiorPoints_map_range' p.2
  have e2 := getElem_interiorPoints_map_range' q.2
  have hp := p.2.trans_eq (length_interiorPoints_map_range' k s t)
  have hq := q.2.trans_eq (length_interiorPoints_map_range' k s t)
  simp only at hpq
  rw [e1, e2] at hpq
  by_contra hne
  have hne' : (p : ℕ) ≠ q := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact hk p q hlt (by omega) hpq
  · exact hk q p hlt (by omega) hpq.symm

private theorem ne_vertexOf_of_mem_interiorPoints_map_range' {P : List H} {n : ℕ} {k : ℕ → H}
    (hk : ∀ j < n, ∀ i, X.vertexOf (X.inv (k j)) ≠ X.vertexOf (P.get i)) :
    ∀ z ∈ X.interiorPoints ((List.range' 0 (n + 1)).map k), ∀ e ∈ P, z ≠ X.vertexOf e := by
  intro z hz e he
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.1 hz
  have e1 := getElem_interiorPoints_map_range' hq
  rw [length_interiorPoints_map_range'] at hq
  rw [e1, zero_add]
  obtain ⟨i', rfl⟩ := List.mem_iff_get.1 he
  exact hk q (by omega) i'

private theorem isStrandPath_map_range' {n : ℕ} {k : ℕ → H}
    (hkB : ∀ j ≤ n, k j ∉ X.bdry ∧ X.isOut (k j) = true)
    (hkstep : ∀ j < n, X.StrandStep (k j) (k (j + 1))) {s t : ℕ} (ht : 1 ≤ t)
    (hst : s + t ≤ n + 1) : X.IsStrandPath ((List.range' s t).map k) := by
  rw [isStrandPath_iff_getElem]
  refine ⟨by simp; omega, fun q hq => ?_, fun q hq => ?_⟩
  · simp only [List.length_map, List.length_range'] at hq
    simp only [List.getElem_map, List.getElem_range', one_mul]
    exact hkB _ (by omega)
  · simp only [List.length_map, List.length_range'] at hq
    simp only [List.getElem_map, List.getElem_range', one_mul]
    rw [← add_assoc]
    exact hkstep _ (by omega)

private theorem escape_injective (hpre : X.IsPreTripleDiagram) {n : ℕ} {k : ℕ → H} {x : H}
    (hkstep : ∀ j < n, X.StrandStep (k j) (k (j + 1)))
    (hk0 : k 0 = (X.rot ^ 3) (X.inv x)) (hx : ∀ j ≤ n, k j ≠ x) {a c : ℕ} (hac : a < c)
    (hc : c ≤ n) : k a ≠ k c := by
  intro heq
  have hkback : ∀ j < n, k j = X.inv ((X.rot ^ 3) (k (j + 1))) := fun j hj => by
    rw [(hkstep j hj).2, hpre.rot_pow_three_rot_pow_three (hkstep j hj).1, hpre.inv_inv_apply]
  have key : ∀ t ≤ a, k (a - t) = k (c - t) := by
    intro t ht
    induction t with
    | zero => simpa using heq
    | succ t ih =>
      rw [hkback (a - (t + 1)) (by omega), hkback (c - (t + 1)) (by omega),
        show a - (t + 1) + 1 = a - t by omega, show c - (t + 1) + 1 = c - t by omega,
        ih (by omega)]
  have h0c := key a le_rfl
  obtain ⟨r, hr⟩ : ∃ r, c - a = r + 1 := ⟨c - a - 1, by omega⟩
  rw [Nat.sub_self, hk0, hr, (hkstep r (by omega)).2] at h0c
  exact hx r (by omega) (X.inv.injective ((X.rot ^ 3).injective h0c)).symm

private theorem escape_notMem_bdry (hpre : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (h0 : 0 < P.length) {n : ℕ} {k : ℕ → H}
    (hk0 : k 0 = (X.rot ^ 3) (X.inv P[P.length - 1]))
    (hkstep : ∀ j < n, X.StrandStep (k j) (k (j + 1))) :
    ∀ j ≤ n, k j ∉ X.bdry ∧ X.isOut (k j) = true := by
  intro j hj
  induction j with
  | zero =>
    have hb : ¬X.IsBoundaryVertex (X.vertexOf (k 0)) := by
      rw [hk0, X.vertexOf_rot_pow_apply, (hP.vertexOf_inv_last h0).1]
      exact (hP.vertexOf_inv_last h0).2
    refine ⟨X.notMem_bdry_of_not_isBoundaryVertex hb, ?_⟩
    rw [hk0, hpre.isOut_rot_pow_three_apply (hP.not_isBoundaryVertex_vertexOf_inv_last h0),
      hpre.isOut_inv_apply (hP.isStrandPath.notMem_bdry _ (List.getElem_mem _)),
      hP.isStrandPath.isOut_eq_true _ (List.getElem_mem _)]
    rfl
  | succ j ih =>
    obtain ⟨hB, hout⟩ := ih (by omega)
    have hstep := hkstep j (by omega)
    exact ⟨hstep.notMem_bdry, (hstep.isOut_eq hpre hB).trans hout⟩

private theorem exists_escape_value (hX : X.IsTripleDiagram) {P : List H} (hP : X.IsMonogon P)
    (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ} (hh : X.IsMonogonWindingFunction P h)
    (h0 : 0 < P.length) {ζ : StrandSide} (hc : X.IsInsideCorner ζ P[0] P[P.length - 1])
    (hconv : h (X.sideOrbit ζ P[0]) = 0) :
    ∃ ω : ℤ, ω ≠ 0 ∧ (ω = h (X.toFaceOrbit P[0]) ∨ ω = h (X.toFaceOrbit (X.inv P[0]))) ∧
      h (X.toFaceOrbit ((X.rot ^ 3) (X.inv P[P.length - 1]))) = ω := by
  have h00 := hh.apply_getElem hX hP hs h0
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℤ, ω = h (X.toFaceOrbit P[0]) + if ζ = .right then 1 else 0 :=
    ⟨_, rfl⟩
  refine ⟨ω, ?_, ?_, ?_⟩
  · cases ζ
    · simp only [sideOrbit] at hconv
      simp [hωdef, hconv]
    · simp only [sideOrbit] at hconv
      rw [h00.2] at hconv
      simp only [hωdef, reduceCtorEq, if_false, add_zero]
      omega
  · cases ζ
    · right
      rw [h00.2, hωdef]
      simp
    · left
      rw [hωdef]
      simp
  · rw [hh.apply_rot_pow_inv_last hX hP hs h0 hc 3 (by norm_num), hωdef]
    cases ζ <;> simp [cornerExp]

private theorem rot_pow_three_inv_last_notMem (hX : X.IsPreTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) (h0 : 0 < P.length) {ζ : StrandSide}
    (hc : X.IsInsideCorner ζ P[0] P[P.length - 1]) :
    (X.rot ^ 3) (X.inv P[P.length - 1]) ∉ P ∧
      X.inv ((X.rot ^ 3) (X.inv P[P.length - 1])) ∉ P := by
  obtain ⟨h₁, h₂, -⟩ := rot_pow_inv_last_mem hX hP hs h0 hc (k := 3) (by norm_num)
  refine ⟨fun hm => ?_, fun hm => absurd (h₂.1 hm) (by norm_num)⟩
  have := h₁.1 hm
  cases ζ <;> simp [cornerExp] at this

/-- A monogon nested in `P`, meeting it only at its starting vertex and with darts on orbits
where `h` is nonzero, has a winding function with strictly smaller support. -/
private theorem exists_smaller_of_nested (hX : X.IsTripleDiagram) {P Q : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) (hQm : X.IsMonogon Q) (hQs : X.IsSimpleStrandPath Q)
    (hdarts : ∀ g ∈ Q, h (X.toFaceOrbit g) ≠ 0 ∧ h (X.toFaceOrbit (X.inv g)) ≠ 0)
    (h0 : 0 < P.length) (hvert : ∀ i : Fin P.length, i ≠ ⟨0, h0⟩ → ∀ j : Fin Q.length,
      X.vertexOf (P.get i) ≠ X.vertexOf (Q.get j)) :
    ∃ Q, X.IsMonogon Q ∧ X.IsSimpleStrandPath Q ∧ ∃ h' : X.faceOrbits → ℤ,
      X.IsMonogonWindingFunction Q h' ∧ {f | h' f ≠ 0} ⊂ {f | h f ≠ 0} := by
  have hpre := hX.toIsPreTripleDiagram
  obtain ⟨h'', hh'', -⟩ := existsUnique_isMonogonWindingFunction hX hQm hQs
  exact ⟨Q, hQm, hQs, h'', hh'', DiskMap.IsWindingFunction.ssubset_of_nested
    hX.toIsDiskMap (hP.isSimpleClosedWalk hpre hs) (hQm.isSimpleClosedWalk hpre hQs)
    (hh.isWindingFunction_walkCycle hpre hP hs)
    (hh''.isWindingFunction_walkCycle hpre hQm hQs)
    (fun j => hdarts _ (List.mem_iff_get.2 ⟨j, rfl⟩)) ⟨0, h0⟩ hvert⟩

private theorem exists_smaller_of_strand_meets_itself (hX : X.IsTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) {n : ℕ} {k : ℕ → H}
    (hsteps : ∀ j < n, ¬X.IsBoundaryVertex (X.vertexOf (X.inv (k j))) ∧
      (∀ i, X.vertexOf (X.inv (k j)) ≠ X.vertexOf (P.get i)) ∧
        k (j + 1) = (X.rot ^ 3) (X.inv (k j)))
    (hkstep : ∀ j < n, X.StrandStep (k j) (k (j + 1)))
    (hkv : ∀ j < n, ∀ i, X.vertexOf (k (j + 1)) ≠ X.vertexOf (P.get i))
    (hkB : ∀ j ≤ n, k j ∉ X.bdry ∧ X.isOut (k j) = true)
    (hkh : ∀ j ≤ n, h (X.toFaceOrbit (k j)) ≠ 0 ∧ h (X.toFaceOrbit (X.inv (k j))) ≠ 0)
    (hkinj : ∀ a c, a < c → c ≤ n → k a ≠ k c)
    (hrep : ∃ a c, a < c ∧ c < n ∧ X.vertexOf (X.inv (k a)) = X.vertexOf (X.inv (k c))) :
    ∃ Q, X.IsMonogon Q ∧ X.IsSimpleStrandPath Q ∧ ∃ h' : X.faceOrbits → ℤ,
      X.IsMonogonWindingFunction Q h' ∧ {f | h' f ≠ 0} ⊂ {f | h f ≠ 0} := by
  classical
  have hpre := hX.toIsPreTripleDiagram
  have h0 : 0 < P.length := List.length_pos_iff.2 hP.isStrandPath.ne_nil
  have hexb : ∃ c, ∃ a < c, c < n ∧ X.vertexOf (X.inv (k a)) = X.vertexOf (X.inv (k c)) :=
    let ⟨a, c, h⟩ := hrep; ⟨c, a, h⟩
  obtain ⟨a, hac, hcn, hv⟩ := Nat.find_spec hexb
  have hmin : ∀ c' < Nat.find hexb, ∀ a' < c', c' < n →
      X.vertexOf (X.inv (k a')) ≠ X.vertexOf (X.inv (k c')) :=
    fun c' hc' a' ha' hcn' hv' => Nat.find_min hexb hc' ⟨a', ha', hcn', hv'⟩
  generalize Nat.find hexb = c at hac hcn hv hmin
  have hQs := isStrandPath_map_range' hkB hkstep (s := a + 1) (t := c - a) (by omega) (by omega)
  have hQh := head?_map_range' k (a + 1) (t := c - a) (by omega)
  have hQl := getLast?_map_range' k (a + 1) (t := c - a) (by omega)
  rw [show a + 1 + (c - a - 1) = c by omega] at hQl
  have hstepa := hkstep a (by omega)
  have hQm : X.IsMonogon ((List.range' (a + 1) (c - a)).map k) := by
    refine ⟨hQs, ?_, ?_, ?_⟩
    · rw [X.pathStart_of_head? hQh, hstepa.vertexOf_eq]
      exact X.vertexOf_mem_internalVertices.2 (hsteps a (by omega)).1
    · rw [X.pathStart_of_head? hQh, X.pathEnd_of_getLast? hQl, hstepa.vertexOf_eq, hv]
    · intro e₁ he₁ eₘ heₘ
      rw [hQh, Option.mem_def, Option.some_inj] at he₁
      rw [hQl, Option.mem_def, Option.some_inj] at heₘ
      subst he₁ heₘ
      rw [hstepa.2, hpre.rot_pow_three_rot_pow_three (hsteps a (by omega)).1]
      exact fun he => hkinj a c hac (by omega) (X.inv.injective he).symm
  have hnot : X.vertexOf (X.inv (k a)) ∉
      X.interiorPoints ((List.range' (a + 1) (c - a)).map k) := by
    intro hm
    obtain ⟨q, hq, hqv⟩ := List.mem_iff_getElem.1 hm
    have e := getElem_interiorPoints_map_range' hq
    rw [length_interiorPoints_map_range'] at hq
    rw [e] at hqv
    exact hmin (a + 1 + q) (by omega) a (by omega) (by omega) hqv.symm
  have hQsimple : X.IsSimpleStrandPath ((List.range' (a + 1) (c - a)).map k) := by
    refine ⟨hQs, nodup_interiorPoints_map_range' fun p q hpq hq =>
      hmin (a + 1 + q) (by omega) (a + 1 + p) (by omega) (by omega), ?_, ?_⟩
    · rw [X.pathStart_of_head? hQh, hstepa.vertexOf_eq]
      exact hnot
    · rw [hQm.pathEnd_eq, X.pathStart_of_head? hQh, hstepa.vertexOf_eq]
      exact hnot
  refine exists_smaller_of_nested hX hP hs hh hQm hQsimple
    (forall_mem_map_range' (p := fun g => h (X.toFaceOrbit g) ≠ 0 ∧
      h (X.toFaceOrbit (X.inv g)) ≠ 0) hkh (by omega)) h0 fun i' _ j => ?_
  have hj := j.2
  simp only [List.length_map, List.length_range'] at hj
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range', one_mul]
  rw [show a + 1 + (j : ℕ) = (a + j) + 1 by omega]
  exact (hkv (a + j) (by omega) i').symm

private theorem exists_smaller_of_strand_returns_to_start (hX : X.IsTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) (h0 : 0 < P.length) {n : ℕ} {k : ℕ → H}
    (hk0 : k 0 = (X.rot ^ 3) (X.inv P[P.length - 1]))
    (hsteps : ∀ j < n, ¬X.IsBoundaryVertex (X.vertexOf (X.inv (k j))) ∧
      (∀ i, X.vertexOf (X.inv (k j)) ≠ X.vertexOf (P.get i)) ∧
        k (j + 1) = (X.rot ^ 3) (X.inv (k j)))
    (hkstep : ∀ j < n, X.StrandStep (k j) (k (j + 1)))
    (hkv : ∀ j < n, ∀ i, X.vertexOf (k (j + 1)) ≠ X.vertexOf (P.get i))
    (hkB : ∀ j ≤ n, k j ∉ X.bdry ∧ X.isOut (k j) = true)
    (hkP : ∀ j ≤ n, k j ∉ P ∧ X.inv (k j) ∉ P)
    (hkh : ∀ j ≤ n, h (X.toFaceOrbit (k j)) ≠ 0 ∧ h (X.toFaceOrbit (X.inv (k j))) ≠ 0)
    (hrep : ∀ a c, a < c → c < n → X.vertexOf (X.inv (k a)) ≠ X.vertexOf (X.inv (k c)))
    (hi : X.vertexOf (X.inv (k n)) = X.vertexOf (P.get ⟨0, h0⟩)) :
    ∃ Q, X.IsMonogon Q ∧ X.IsSimpleStrandPath Q ∧ ∃ h' : X.faceOrbits → ℤ,
      X.IsMonogonWindingFunction Q h' ∧ {f | h' f ≠ 0} ⊂ {f | h f ≠ 0} := by
  have hpre := hX.toIsPreTripleDiagram
  have hw := hP.isSimpleClosedWalk hpre hs
  have hx := hP.vertexOf_inv_last h0
  have htrip := hP.not_isBoundaryVertex_vertexOf_inv_last h0
  have hvg₀ : X.vertexOf (k 0) = X.vertexOf P[0] := by
    rw [hk0, X.vertexOf_rot_pow_apply, hx.1]
  have hGs := isStrandPath_map_range' hkB hkstep (s := 0) (t := n + 1) (by omega) (by omega)
  have hGh := head?_map_range' k 0 (t := n + 1) (by omega)
  have hGl := getLast?_map_range' k 0 (t := n + 1) (by omega)
  rw [show 0 + (n + 1 - 1) = n by omega] at hGl
  have hGn : (X.interiorPoints ((List.range' 0 (n + 1)).map k)).Nodup :=
    nodup_interiorPoints_map_range' fun p q hpq _ => by
      simpa only [zero_add] using hrep p q hpq (by omega)
  have hGv := ne_vertexOf_of_mem_interiorPoints_map_range' fun j hj => (hsteps j hj).2.1
  have hGm : X.IsMonogon ((List.range' 0 (n + 1)).map k) := by
    refine ⟨hGs, ?_, ?_, ?_⟩
    · rw [X.pathStart_of_head? hGh, hvg₀]
      exact X.vertexOf_mem_internalVertices.2 hx.2
    · rw [X.pathEnd_of_getLast? hGl, hi, X.pathStart_of_head? hGh, hvg₀]
      rfl
    · intro e₁ he₁ eₘ heₘ
      rw [hGh, Option.mem_def, Option.some_inj] at he₁
      rw [hGl, Option.mem_def, Option.some_inj] at heₘ
      subst he₁ heₘ
      rw [hk0, hpre.rot_pow_three_rot_pow_three htrip]
      exact fun he => (hkP n le_rfl).1 (by rw [X.inv.injective he]; exact List.getElem_mem _)
  have hGsimple : X.IsSimpleStrandPath ((List.range' 0 (n + 1)).map k) := by
    refine ⟨hGs, hGn, ?_, ?_⟩
    · rw [X.pathStart_of_head? hGh, hvg₀]
      exact fun hm => hGv _ hm _ (List.getElem_mem h0) rfl
    · rw [hGm.pathEnd_eq, X.pathStart_of_head? hGh, hvg₀]
      exact fun hm => hGv _ hm _ (List.getElem_mem h0) rfl
  refine exists_smaller_of_nested hX hP hs hh hGm hGsimple
    (forall_mem_map_range' (p := fun g => h (X.toFaceOrbit g) ≠ 0 ∧
      h (X.toFaceOrbit (X.inv g)) ≠ 0) hkh (by omega)) h0 fun i' hi'0 j => ?_
  have hj := j.2
  simp only [List.length_map, List.length_range'] at hj
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range', one_mul, zero_add]
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj0
  · rw [hj0, hvg₀]
    intro hv
    exact hi'0 (Fin.ext (vertexOf_getElem_inj hw i'.2 h0 hv))
  · obtain ⟨j', hj'⟩ : ∃ j', (j : ℕ) = j' + 1 := ⟨j - 1, by omega⟩
    rw [hj']
    exact (hkv j' (by omega) i').symm

/-- Following `P` from `e_i` and then a strand path `G` from `σ³ ē_m` back to `v(e_i)` is a
monogon. -/
private theorem isMonogon_drop_append_of_returns_inside (hX : X.IsTripleDiagram) {P G : List H}
    (hP : X.IsMonogon P) (h0 : 0 < P.length) {i : Fin P.length} (hi0 : (i : ℕ) ≠ 0)
    (hGs : X.IsStrandPath G) {g₀ gₙ : H} (hGh : G.head? = some g₀) (hGl : G.getLast? = some gₙ)
    (hg₀ : g₀ = (X.rot ^ 3) (X.inv P[P.length - 1]))
    (hi : X.vertexOf (X.inv gₙ) = X.vertexOf (P.get i)) (hgₙ : gₙ ∉ P) :
    X.IsMonogon (P.drop i ++ G) := by
  have hpre := hX.toIsPreTripleDiagram
  have htrip := hP.not_isBoundaryVertex_vertexOf_inv_last h0
  have hil := i.2
  have hstep := strandStep_getElem hP.isStrandPath (show (i : ℕ) - 1 + 1 < P.length by omega)
  have hdne : P.drop i ≠ [] := by rw [Ne, List.drop_eq_nil_iff]; omega
  have hGne := hGs.ne_nil
  have hhM' : (P.drop i ++ G).head? = some (P[(i : ℕ)]'hil) := by
    rw [List.head?_append_of_ne_nil _ hdne, List.head?_drop, List.getElem?_eq_getElem hil]
  have hlM' : (P.drop i ++ G).getLast? = some gₙ := by
    rw [List.getLast?_append_of_ne_nil _ hGne, hGl]
  refine ⟨⟨by simp [hGne], fun e he => ?_, fun e he => ?_, ?_⟩, ?_, ?_, ?_⟩
  · rcases List.mem_append.1 he with he | he
    · exact hP.isStrandPath.notMem_bdry e (List.mem_of_mem_drop he)
    · exact hGs.notMem_bdry e he
  · rcases List.mem_append.1 he with he | he
    · exact hP.isStrandPath.isOut_eq_true e (List.mem_of_mem_drop he)
    · exact hGs.isOut_eq_true e he
  · rw [List.isChain_append]
    refine ⟨hP.isStrandPath.isChain.drop _, hGs.isChain, fun x hx' y hy => ?_⟩
    rw [List.getLast?_drop, if_neg (by omega), List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega), Option.mem_def, Option.some_inj] at hx'
    rw [hGh, Option.mem_def, Option.some_inj] at hy
    subst hx' hy
    exact ⟨htrip, hg₀⟩
  · rw [X.pathStart_of_head? hhM']
    exact X.vertexOf_mem_internalVertices.2
      (hP.not_isBoundaryVertex (List.mem_iff_get.2 ⟨i, rfl⟩)).1
  · rwa [X.pathStart_of_head? hhM', X.pathEnd_of_getLast? hlM']
  · intro e₁ he₁ eₘ heₘ
    rw [hhM', Option.mem_def, Option.some_inj] at he₁
    rw [hlM', Option.mem_def, Option.some_inj] at heₘ
    subst he₁ heₘ
    rw [getElem_of_eq_idx (show (i : ℕ) = (i : ℕ) - 1 + 1 by omega) hil, hstep.2,
      hpre.rot_pow_three_rot_pow_three hstep.1]
    exact fun he => hgₙ (by rw [X.inv.injective he]; exact List.getElem_mem _)

private theorem exists_smaller_of_strand_returns_inside (hX : X.IsTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) (h0 : 0 < P.length) {ω : ℤ}
    (hωP : ω = h (X.toFaceOrbit P[0]) ∨ ω = h (X.toFaceOrbit (X.inv P[0]))) (hω0 : ω ≠ 0)
    {n : ℕ} {k : ℕ → H} (hk0 : k 0 = (X.rot ^ 3) (X.inv P[P.length - 1]))
    (hsteps : ∀ j < n, ¬X.IsBoundaryVertex (X.vertexOf (X.inv (k j))) ∧
      (∀ i, X.vertexOf (X.inv (k j)) ≠ X.vertexOf (P.get i)) ∧
        k (j + 1) = (X.rot ^ 3) (X.inv (k j)))
    (hkstep : ∀ j < n, X.StrandStep (k j) (k (j + 1)))
    (hkB : ∀ j ≤ n, k j ∉ X.bdry ∧ X.isOut (k j) = true)
    (hkP : ∀ j ≤ n, k j ∉ P ∧ X.inv (k j) ∉ P) (hkval : ∀ j ≤ n, h (X.toFaceOrbit (k j)) = ω)
    (hrep : ∀ a c, a < c → c < n → X.vertexOf (X.inv (k a)) ≠ X.vertexOf (X.inv (k c)))
    {i : Fin P.length} (hi : X.vertexOf (X.inv (k n)) = X.vertexOf (P.get i))
    (hi0 : (i : ℕ) ≠ 0) :
    ∃ Q, X.IsMonogon Q ∧ X.IsSimpleStrandPath Q ∧ ∃ h' : X.faceOrbits → ℤ,
      X.IsMonogonWindingFunction Q h' ∧ {f | h' f ≠ 0} ⊂ {f | h f ≠ 0} := by
  have hpre := hX.toIsPreTripleDiagram
  have hGs := isStrandPath_map_range' hkB hkstep (s := 0) (t := n + 1) (by omega) (by omega)
  have hGh := head?_map_range' k 0 (t := n + 1) (by omega)
  have hGl := getLast?_map_range' k 0 (t := n + 1) (by omega)
  rw [show 0 + (n + 1 - 1) = n by omega] at hGl
  have hGn : (X.interiorPoints ((List.range' 0 (n + 1)).map k)).Nodup :=
    nodup_interiorPoints_map_range' fun p q hpq _ => by
      simpa only [zero_add] using hrep p q hpq (by omega)
  have hGv := ne_vertexOf_of_mem_interiorPoints_map_range' fun j hj => (hsteps j hj).2.1
  have hGP : ∀ g ∈ (List.range' 0 (n + 1)).map k, g ∉ P ∧ X.inv g ∉ P :=
    forall_mem_map_range' (p := fun g => g ∉ P ∧ X.inv g ∉ P) hkP (by omega)
  have hGval : ∀ g ∈ (List.range' 0 (n + 1)).map k, h (X.toFaceOrbit g) = ω :=
    forall_mem_map_range' (p := fun g => h (X.toFaceOrbit g) = ω) hkval (by omega)
  have hil := i.2
  have hstep := strandStep_getElem hP.isStrandPath (show (i : ℕ) - 1 + 1 < P.length by omega)
  have hGl' : X.pathEnd ((List.range' 0 (n + 1)).map k) =
      X.vertexOf (X.inv (P[(i : ℕ) - 1]'(by omega))) := by
    rw [X.pathEnd_of_getLast? hGl, hi, show P.get i = P[(i : ℕ) - 1 + 1]'(by omega) from
      getElem_of_eq_idx (by omega) i.2, hstep.vertexOf_eq]
  obtain ⟨hwM', hss⟩ := ssubset_of_split hX hP hs hh (l := i) (by omega) hil hωP hω0 hGs
    (by rw [hGh, hk0]) hGl' hGn hGv hGP hGval
  have hM'm := isMonogon_drop_append_of_returns_inside hX hP h0 hi0 hGs hGh hGl hk0 hi
    (hkP n le_rfl).1
  have hM's := hM'm.isSimpleStrandPath_of_nodup (nodup_map_vertexOf hwM')
  obtain ⟨h'', hh'', -⟩ := existsUnique_isMonogonWindingFunction hX hM'm hM's
  exact ⟨_, hM'm, hM's, h'', hh'', hss h'' (hh''.isWindingFunction_walkCycle hpre hM'm hM's)⟩

private theorem exists_smaller_of_not_convex (hX : X.IsTripleDiagram) {P : List H}
    (hP : X.IsMonogon P) (hs : X.IsSimpleStrandPath P) {h : X.faceOrbits → ℤ}
    (hh : X.IsMonogonWindingFunction P h) (h0 : 0 < P.length) {ζ : StrandSide}
    (hc : X.IsInsideCorner ζ P[0] P[P.length - 1]) (hconv : h (X.sideOrbit ζ P[0]) = 0) :
    ∃ Q, X.IsMonogon Q ∧ X.IsSimpleStrandPath Q ∧ ∃ h' : X.faceOrbits → ℤ,
      X.IsMonogonWindingFunction Q h' ∧ {f | h' f ≠ 0} ⊂ {f | h f ≠ 0} := by
  have hpre := hX.toIsPreTripleDiagram
  have hx := hP.vertexOf_inv_last h0
  obtain ⟨ω, hω0, hωP, hg₀val⟩ := exists_escape_value hX hP hs hh h0 hc hconv
  have hg₀P := rot_pow_three_inv_last_notMem hpre hP hs h0 hc
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ = (X.rot ^ 3) (X.inv P[P.length - 1]) := ⟨_, rfl⟩
  rw [← hg₀] at hg₀val hg₀P
  have hvg₀ : X.vertexOf g₀ = X.vertexOf P[0] := by rw [hg₀, X.vertexOf_rot_pow_apply, hx.1]
  have hk₁C : ∀ i, g₀ ≠ P.get i ∧ g₀ ≠ X.inv (P.get i) := fun i =>
    ⟨fun he => hg₀P.1 (he ▸ List.mem_iff_get.2 ⟨i, rfl⟩),
      fun he => hg₀P.2 (by rw [he, hpre.inv_inv_apply]; exact List.mem_iff_get.2 ⟨i, rfl⟩)⟩
  obtain ⟨n, k, hk0, hsteps, ⟨i, hi⟩, hprops⟩ :=
    DiskMap.IsWindingFunction.exists_walk_escape hX.toIsDiskMap (hP.isSimpleClosedWalk hpre hs)
      (fun i => (hP.not_isBoundaryVertex (List.mem_iff_get.2 ⟨i, rfl⟩)).1)
      (hh.isWindingFunction_walkCycle hpre hP hs) hω0 ⟨⟨0, h0⟩, hvg₀⟩ hk₁C hg₀val
  rw [hg₀] at hk0
  have hkP : ∀ j ≤ n, k j ∉ P ∧ X.inv (k j) ∉ P := fun j hj => by
    obtain ⟨hC, -⟩ := hprops j hj
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · obtain ⟨i', hi'⟩ := List.mem_iff_get.1 hm
      exact (hC i').1 hi'.symm
    · obtain ⟨i', hi'⟩ := List.mem_iff_get.1 hm
      exact (hC i').2 (by rw [hi', hpre.inv_inv_apply])
  have hkval : ∀ j ≤ n, h (X.toFaceOrbit (k j)) = ω := fun j hj => (hprops j hj).2
  have hkh : ∀ j ≤ n, h (X.toFaceOrbit (k j)) ≠ 0 ∧ h (X.toFaceOrbit (X.inv (k j))) ≠ 0 :=
    fun j hj => by
      have := hh.sub_eq (k j)
      rw [X.monogonCycle_eq_zero_of_notMem (hkP j hj).1 (hkP j hj).2] at this
      have := hkval j hj
      exact ⟨by omega, by omega⟩
  have hkstep : ∀ j < n, X.StrandStep (k j) (k (j + 1)) := fun j hj =>
    ⟨(hsteps j hj).1, (hsteps j hj).2.2⟩
  have hkB := escape_notMem_bdry hpre hP h0 hk0 hkstep
  have hkv : ∀ j < n, ∀ i, X.vertexOf (k (j + 1)) ≠ X.vertexOf (P.get i) := fun j hj i => by
    rw [(hkstep j hj).vertexOf_eq]
    exact (hsteps j hj).2.1 i
  by_cases hrep : ∃ a c, a < c ∧ c < n ∧ X.vertexOf (X.inv (k a)) = X.vertexOf (X.inv (k c))
  · exact exists_smaller_of_strand_meets_itself hX hP hs hh hsteps hkstep hkv hkB hkh
      (fun a c hac hc => escape_injective hpre hkstep hk0
        (fun j hj he => (hkP j hj).1 (by rw [he]; exact List.getElem_mem _)) hac hc) hrep
  push Not at hrep
  by_cases hi0 : (i : ℕ) = 0
  · obtain rfl : i = ⟨0, h0⟩ := Fin.ext hi0
    exact exists_smaller_of_strand_returns_to_start hX hP hs hh h0 hk0 hsteps hkstep hkv hkB hkP
      hkh hrep hi
  · exact exists_smaller_of_strand_returns_inside hX hP hs hh h0 hωP hω0 hk0 hsteps hkstep hkB
      hkP hkval hrep hi hi0

/-- **Convex monogons exist**: a triple diagram with a monogon has a convex monogon. -/
@[cluster_algebras "lem_monogon_convex_exists"]
theorem exists_isConvexMonogon (hX : X.IsTripleDiagram) (hmono : X.HasMonogon) :
    ∃ P ζ, X.IsConvexMonogon P ζ := by
  classical
  have hpre := hX.toIsPreTripleDiagram
  obtain ⟨P₀, hP₀, hs₀⟩ := exists_isMonogon_isSimpleStrandPath hpre hmono
  obtain ⟨h₀, hh₀, -⟩ := existsUnique_isMonogonWindingFunction hX hP₀ hs₀
  suffices key : ∀ n, ∀ P, X.IsMonogon P → X.IsSimpleStrandPath P → ∀ h : X.faceOrbits → ℤ,
      X.IsMonogonWindingFunction P h → (univ.filter fun f => h f ≠ 0).card = n →
      ∃ P ζ, X.IsConvexMonogon P ζ from key _ P₀ hP₀ hs₀ h₀ hh₀ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hP hs h hh hn
  have h0 : 0 < P.length := List.length_pos_iff.2 hP.isStrandPath.ne_nil
  obtain ⟨ζ, hc⟩ := hP.exists_isInsideCorner hpre h0
  by_cases hconv : h (X.sideOrbit ζ P[0]) ≠ 0
  · refine ⟨P, ζ, hP, hs, fun e₁ he₁ eₘ heₘ => ?_, h, hh, fun e₁ he₁ => ?_⟩
    · rw [eq_getElem_zero_of_mem_head? h0 he₁, eq_getElem_last_of_mem_getLast? h0 heₘ]
      exact hc
    · rw [eq_getElem_zero_of_mem_head? h0 he₁]
      exact hconv
  push Not at hconv
  obtain ⟨Q, hQ, hsQ, h', hh', hss⟩ := exists_smaller_of_not_convex hX hP hs hh h0 hc hconv
  refine ih _ ?_ Q hQ hsQ h' hh' rfl
  rw [← hn]
  apply Finset.card_lt_card
  rw [← Finset.coe_ssubset]
  simpa using hss

end Exists

end TripleData

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.NormalTriple
public import ClusterAlgebras.Plabic.MinimalTriple

/-!
# The normal plabic graph of a triple diagram

Let `X` be a (pre-)triple diagram with `b` arcs and let `I` be the set of its in-darts outside `B`.
For `y ∈ I` put `ψ(y) = \overline{σ⁻¹(y)}` if `y` lies at a triple point, and
`ψ(n_{2i}) = \overline{n_{2i-1}}` for the dart `n_{2i}` of the target `t_i`; then `ψ` is a
permutation of `I`. The *normal plabic graph* `G(X)` has the darts `c_y`, `c*_y` (`y ∈ I`) and
`h_i`, `h*_i` (`i ∈ [1, b]`); its involution pairs `c_y` with `c*_y` and `h_i` with `h*_i`, its
rotation sends `c_y ↦ c_{ψ(y)}` and `c*_y ↦ c*_{σ²(y)}` at triple points and consists of the
cycles `(h*_{i+1}, h_i, c*_{n_{2i}})` at the boundary. The black vertices of `G(X)` are the orbits
of `ψ`, i.e. the faces of `X` whose darts outside `B` are in-darts, and the white vertices are the
triple points of `X`.

`G(X)` is a normal plabic pregraph, and `X(G(X)) ≅ X`; hence `G(X)` is a normal plabic graph when
`X` is a triple diagram. Conversely `G(X(G)) ≅ G` for a normal plabic graph `G`, and both
constructions respect isomorphisms. Finally, the strands of `X(G)` follow the trips of `G`: the
strand through `x⁺_k` turns at the white vertex of `\overline{σ k}` exactly as the trip through
`σ k` does. Consequently `π_G = π_{X(G)}`, and `G` has a roundtrip if and only if `X(G)` has a
closed strand.

## Main definitions

* `ClusterAlgebras.NormalOfTripleDart`, `ClusterAlgebras.TripleData.NormalDart`: the darts `c_y`,
  `c*_y`, `h_i`, `h*_i`.
* `ClusterAlgebras.TripleData.inDarts`, `ClusterAlgebras.TripleData.psiFun`,
  `ClusterAlgebras.TripleData.IsPreTripleDiagram.psi`: the set `I` and the permutation `ψ`.
* `ClusterAlgebras.TripleData.normalOfTriple`: the normal plabic graph `G(X)`.

## Main results

* `ClusterAlgebras.TripleData.IsPreTripleDiagram.bijOn_psiFun`,
  `ClusterAlgebras.TripleData.IsPreTripleDiagram.isNormalPlabicPregraph_normalOfTriple`: `ψ` is a
  permutation of `I` and `G(X)` is a normal plabic pregraph.
* `ClusterAlgebras.TripleData.IsPreTripleDiagram.tripleOfNormalIso`: `X(G(X)) ≅ X`.
* `ClusterAlgebras.TripleData.IsTripleDiagram.isNormalPlabicGraph_normalOfTriple`: `G(X)` is a
  normal plabic graph.
* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.normalOfTripleIso`: `G ≅ G(X(G))`.
* `ClusterAlgebras.TripleData.Iso.normalOfTriple`: `G(X)` depends on `X` only up to isomorphism.
* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.strandMap_plus_of_internal`,
  `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.strandMap_plus_of_eq_inv_leg`: strands of
  `X(G)` follow trips of `G`.
* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.tripPerm_eq_strandPerm`: `π_G = π_{X(G)}`.
* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.hasRoundtrip_iff_exists_isClosedStrand`: `G` has
  a roundtrip if and only if `X(G)` has a closed strand.

## Implementation notes

* **Darts.** `I` is the `Finset` `TripleData.inDarts`, and the darts of `G(X)` are the inductive
  type `NormalOfTripleDart X.InDart b`, with constructors `c`, `cStar`, `h`, `hStar`. The darts
  `h_i`, `h*_i` are those of the boundary circle, and the leg at `i` is `c*_{n_{2i}}`.
* **Labels.** Labels are `0`-indexed: `i : Fin b` stands for the `1`-indexed label `i + 1`, the
  dart `n_{2i}` of the target `t_{i+1}` is `X.endDart (targetIndex i)`, and the dart `h_{i+1}` is
  `h (finRotate b i)`. The case `y = n_{2i}` of `ψ` is decided by `TripleData.targetLabel y`, the
  first label `i` with `n_{2i} = y`.
* **Colours.** Colours are recorded on darts: `c_y` is black and every other dart white; the
  colours of the darts at boundary vertices are irrelevant.
* **The construction takes the pre-triple hypothesis.** The rotation of `G(X)` is a permutation
  only because `ψ` and `σ²` preserve `I`, which uses the conditions of a pre-triple diagram; so
  `normalOfTriple` takes the proof `hX` as an argument.
* **Exterior darts.** The darts `p_r` of the exterior at the endpoints of `X` and `h_i` at the
  boundary vertices of `G` are chosen (`DiskMap.exteriorDartAt`); a boundary vertex carries only
  one dart of the exterior (`DiskMap.eq_of_mem_exterior_of_mem_vertexOf`).
* **Isomorphisms.** The isomorphism `G → G(X(G))` is built as the inverse of the explicit
  bijection `G(X(G)) → G`, `c_{x⁻_k} ↦ k`, `c*_{x⁻_k} ↦ k̄`, `h_i ↦ h_i`, `h*_i ↦ h̄_i`. The
  isomorphism `X(G(X)) → X` is indexed by `y ∈ I` through the bijection `y ↦ c_y` onto the darts
  at black vertices of `G(X)`.
* **Roundtrips.** A closed strand through darts `x⁻_k` is handled directly rather than by
  reversing it: such a strand follows a trip of `G` backwards, and is periodic, so the trip
  through `k` returns to `k` without meeting a leg.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Orbits through closed sets -/

/-- A predicate preserved by `f` is preserved along the orbits of `f`. -/
private theorem mem_of_sameCycle_of_closed' {α : Type*} [Finite α] {f : Equiv.Perm α}
    {P : α → Prop} (hP : ∀ x, P x → P (f x)) {x y : α} (hx : P x) (h : f.SameCycle x y) :
    P y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hP _ ih

/-- A vertex on which the rotation is a `3`-cycle. -/
private theorem vertexOf_eq_three' {H : Type*} [Fintype H] [DecidableEq H] (R : RotationSystem H)
    {a₁ a₂ a₃ : H} (h₁ : R.rot a₁ = a₂) (h₂ : R.rot a₂ = a₃) (h₃ : R.rot a₃ = a₁) :
    R.vertexOf a₁ = {a₁, a₂, a₃} := by
  ext e
  rw [RotationSystem.mem_vertexOf]
  constructor
  · intro h
    refine mem_of_sameCycle_of_closed' (P := fun x => x ∈ ({a₁, a₂, a₃} : Finset H)) ?_
      (by simp) h
    intro x hx
    simp only [mem_insert, mem_singleton] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · exact Or.inr (Or.inl h₁)
    · exact Or.inr (Or.inr h₂)
    · exact Or.inl h₃
  · intro he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.refl _ _
    · rw [← h₁]
      exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
    · rw [← h₂, ← h₁]
      exact Equiv.Perm.sameCycle_apply_right.2
        (Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _))

private theorem val_finRotate' {n : ℕ} (r : Fin n) : (finRotate n r : ℕ) = (r + 1) % n := by
  cases n with
  | zero => exact r.elim0
  | succ n =>
    rw [finRotate_apply, Fin.val_add, Fin.val_one']
    simp [Nat.add_mod]

/-! ### The darts of the normal plabic graph -/

/-- The darts of the normal plabic graph of a triple diagram: pairwise distinct symbols `c_y`
(`c y`) and `c*_y` (`cStar y`) for `y` in a set `I`, and `h_i` (`h i`), `h*_i` (`hStar i`) for
`i` in `Fin n` (in practice `n = b`, and `i : Fin b` stands for the `1`-indexed label `i + 1`).
-/
inductive NormalOfTripleDart (I : Type*) (n : ℕ) : Type _
  /-- The dart `c_y`. -/
  | c (y : I)
  /-- The dart `c*_y`. -/
  | cStar (y : I)
  /-- The dart `h_i` of the boundary circle. -/
  | h (i : Fin n)
  /-- The dart `h*_i` of the boundary circle. -/
  | hStar (i : Fin n)
  deriving DecidableEq

namespace NormalOfTripleDart

variable {I : Type*} {n : ℕ}

/-- The darts of `NormalOfTripleDart I n` as a sum type. -/
def equivSum : NormalOfTripleDart I n ≃ (I ⊕ I) ⊕ (Fin n ⊕ Fin n) where
  toFun
    | c y => .inl (.inl y)
    | cStar y => .inl (.inr y)
    | h i => .inr (.inl i)
    | hStar i => .inr (.inr i)
  invFun
    | .inl (.inl y) => c y
    | .inl (.inr y) => cStar y
    | .inr (.inl i) => h i
    | .inr (.inr i) => hStar i
  left_inv := by rintro (_ | _ | _ | _) <;> rfl
  right_inv := by rintro ((_ | _) | (_ | _)) <;> rfl

/-- The darts `NormalOfTripleDart I n` form a finite type when `I` does. -/
instance [Fintype I] : Fintype (NormalOfTripleDart I n) := Fintype.ofEquiv _ equivSum.symm

/-- Whether a dart is one of the darts `h_i`, `h*_i` of the boundary circle. -/
def isH : NormalOfTripleDart I n → Bool
  | h _ => true
  | hStar _ => true
  | _ => false

/-- The dart `c_y` is not a dart of the boundary circle. -/
@[simp] theorem isH_c (y : I) : (c y : NormalOfTripleDart I n).isH = false := rfl
/-- The dart `c*_y` is not a dart of the boundary circle. -/
@[simp] theorem isH_cStar (y : I) : (cStar y : NormalOfTripleDart I n).isH = false := rfl
/-- The dart `h_i` is a dart of the boundary circle. -/
@[simp] theorem isH_h (i : Fin n) : (h i : NormalOfTripleDart I n).isH = true := rfl
/-- The dart `h*_i` is a dart of the boundary circle. -/
@[simp] theorem isH_hStar (i : Fin n) : (hStar i : NormalOfTripleDart I n).isH = true := rfl

/-- The involution `c_y ↔ c*_y`, `h_i ↔ h*_i`. -/
def star : Equiv.Perm (NormalOfTripleDart I n) where
  toFun
    | c y => cStar y
    | cStar y => c y
    | h i => hStar i
    | hStar i => h i
  invFun
    | c y => cStar y
    | cStar y => c y
    | h i => hStar i
    | hStar i => h i
  left_inv := by rintro (_ | _ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _ | _) <;> rfl

/-- The involution sends `c_y` to `c*_y`. -/
@[simp] theorem star_c (y : I) : star (c y : NormalOfTripleDart I n) = cStar y := rfl
/-- The involution sends `c*_y` to `c_y`. -/
@[simp] theorem star_cStar (y : I) : star (cStar y : NormalOfTripleDart I n) = c y := rfl
/-- The involution sends `h_i` to `h*_i`. -/
@[simp] theorem star_h (i : Fin n) : star (h i : NormalOfTripleDart I n) = hStar i := rfl
/-- The involution sends `h*_i` to `h_i`. -/
@[simp] theorem star_hStar (i : Fin n) : star (hStar i : NormalOfTripleDart I n) = h i := rfl

/-- The involution `star` is its own inverse. -/
@[simp] theorem star_symm_apply (d : NormalOfTripleDart I n) : star.symm d = star d := by
  rcases d with _ | _ | _ | _ <;> rfl

/-- The colouring: the darts `c_y` are black, all others white. -/
def colour : NormalOfTripleDart I n → Shade
  | c _ => .black
  | _ => .white

/-- The dart `c_y` is black. -/
@[simp] theorem colour_c (y : I) : colour (c y : NormalOfTripleDart I n) = .black := rfl
/-- The dart `c*_y` is white. -/
@[simp] theorem colour_cStar (y : I) : colour (cStar y : NormalOfTripleDart I n) = .white := rfl
/-- The dart `h_i` is white. -/
@[simp] theorem colour_h (i : Fin n) : colour (h i : NormalOfTripleDart I n) = .white := rfl
/-- The dart `h*_i` is white. -/
@[simp] theorem colour_hStar (i : Fin n) : colour (hStar i : NormalOfTripleDart I n) = .white :=
  rfl

/-- A bijection `I ≃ I'` induces a bijection of darts, `c_y ↦ c_{e y}`, `c*_y ↦ c*_{e y}`,
`h_i ↦ h_i`, `h*_i ↦ h*_i`. -/
def mapEquiv {I' : Type*} (e : I ≃ I') : NormalOfTripleDart I n ≃ NormalOfTripleDart I' n where
  toFun
    | c y => c (e y)
    | cStar y => cStar (e y)
    | h i => h i
    | hStar i => hStar i
  invFun
    | c y => c (e.symm y)
    | cStar y => cStar (e.symm y)
    | h i => h i
    | hStar i => hStar i
  left_inv := by rintro (_ | _ | _ | _) <;> simp
  right_inv := by rintro (_ | _ | _ | _) <;> simp

section MapEquiv

variable {I' : Type*} (e : I ≃ I')

/-- `mapEquiv e` sends `c_y` to `c_{e y}`. -/
@[simp] theorem mapEquiv_c (y : I) : mapEquiv (n := n) e (c y) = c (e y) := rfl
/-- `mapEquiv e` sends `c*_y` to `c*_{e y}`. -/
@[simp] theorem mapEquiv_cStar (y : I) : mapEquiv (n := n) e (cStar y) = cStar (e y) := rfl
/-- `mapEquiv e` fixes `h_i`. -/
@[simp] theorem mapEquiv_h (i : Fin n) : mapEquiv (I := I) e (h i) = h i := rfl
/-- `mapEquiv e` fixes `h*_i`. -/
@[simp] theorem mapEquiv_hStar (i : Fin n) : mapEquiv (I := I) e (hStar i) = hStar i := rfl

end MapEquiv

end NormalOfTripleDart

/-! ### The darts of the exterior at labelled boundary vertices -/

namespace DiskMap

variable {H : Type*} [Fintype H] [DecidableEq H] {M : DiskMap H} {n : ℕ}
  {ν : Fin n → Finset H}

/-- Given boundary vertices `ν(1), …, ν(n)` labelled so that for every `r` some dart of the
exterior at `ν(r + 1)` runs to `ν(r)`, a dart of the exterior at `ν(r)` whose reverse lies at
`ν(r - 1)`. In a disk map it is the unique dart of the exterior at `ν(r)`
(`DiskMap.eq_of_mem_exterior_of_mem_vertexOf`). -/
noncomputable def exteriorDartAt
    (hν : ∀ r, ∃ d ∈ M.exterior, d ∈ ν (finRotate n r) ∧ M.inv d ∈ ν r) (r : Fin n) : H :=
  (hν ((finRotate n).symm r)).choose

omit [Fintype H] in
/-- The dart `exteriorDartAt hν r` lies in the exterior and at `ν(r)`, and its reverse lies at
`ν(r - 1)`. -/
theorem exteriorDartAt_spec (hν : ∀ r, ∃ d ∈ M.exterior, d ∈ ν (finRotate n r) ∧ M.inv d ∈ ν r)
    (r : Fin n) :
    exteriorDartAt hν r ∈ M.exterior ∧ exteriorDartAt hν r ∈ ν r ∧
      M.inv (exteriorDartAt hν r) ∈ ν ((finRotate n).symm r) := by
  obtain ⟨h1, h2, h3⟩ := (hν ((finRotate n).symm r)).choose_spec
  refine ⟨h1, ?_, h3⟩
  have e : ν (finRotate n ((finRotate n).symm r)) = ν r := by rw [Equiv.apply_symm_apply]
  exact (congrArg (fun S => exteriorDartAt hν r ∈ S) e).mp h2

/-- If every boundary vertex has three darts, two of them in `B`, then a boundary vertex carries at
most one dart of the exterior. -/
theorem eq_of_mem_exterior_of_mem_vertexOf
    (hdeg : ∀ v ∈ M.boundaryVertices, v.card = 3 ∧ (v.filter (· ∈ M.bdry)).card = 2)
    {p p' : H} (hp : p ∈ M.exterior) (hp' : p' ∈ M.exterior) (h : p' ∈ M.vertexOf p) :
    p' = p := by
  have hv := M.isBoundaryVertex_vertexOf_of_mem (M.exterior_subset_bdry hp)
  have h' : M.rot p' ∈ M.vertexOf p := by
    rw [← M.vertexOf_eq_of_mem h]
    exact M.rot_mem_vertexOf p'
  exact M.rot.injective (eq_of_notMem_bdry hdeg hv h' (M.rot_mem_vertexOf p)
    (M.mem_exterior.1 hp').2 (M.mem_exterior.1 hp).2)

/-- The rotation at a labelled boundary vertex `ν(r)` in terms of the chosen darts `p_r` of the
exterior: it is the cycle `(p̄_{r+1}, p_r, g)`, with `g` the dart of `ν(r)` outside `B`. -/
theorem rot_cycle_exteriorDartAt (hinv : Function.Involutive M.inv)
    (hbdry : ∀ d ∈ M.bdry, M.inv d ∈ M.bdry)
    (hdeg : ∀ v ∈ M.boundaryVertices, v.card = 3 ∧ (v.filter (· ∈ M.bdry)).card = 2)
    (horb : ∃ f ∈ M.faceOrbits, f ⊆ M.bdry ∧ f ∪ f.map M.inv.toEmbedding = M.bdry ∧
      Disjoint f (f.map M.inv.toEmbedding))
    (hν : ∀ r, ∃ d ∈ M.exterior, d ∈ ν (finRotate n r) ∧ M.inv d ∈ ν r) {r : Fin n}
    (hv : ν r ∈ M.boundaryVertices) {g : H} (hg : g ∈ ν r) (hgB : g ∉ M.bdry) :
    ν r = {M.inv (exteriorDartAt hν (finRotate n r)), exteriorDartAt hν r, g} ∧
      M.rot (M.inv (exteriorDartAt hν (finRotate n r))) = exteriorDartAt hν r ∧
      M.rot (exteriorDartAt hν r) = g ∧
      M.rot g = M.inv (exteriorDartAt hν (finRotate n r)) := by
  obtain ⟨hp, hpv, -⟩ := exteriorDartAt_spec hν r
  obtain ⟨hq, -, hqv⟩ := exteriorDartAt_spec hν (finRotate n r)
  rw [Equiv.symm_apply_apply] at hqv
  exact rot_cycle_of_mem_boundaryVertices hinv hbdry hdeg horb hv hp hpv hq hqv hg hgB

end DiskMap

/-! ### In-darts, sources and targets of a triple diagram -/

namespace TripleData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)

/-- The set `I` of **in-darts** outside `B`: the darts `z ∉ B` with `o(z) = in`. -/
def inDarts : Finset H := {y | y ∉ X.bdry ∧ X.isOut y = false}

/-- The in-darts outside `B`, as a type. -/
abbrev InDart : Type _ := {y // y ∈ X.inDarts}

/-- The darts `c_y`, `c*_y`, `h_i`, `h*_i` of the normal plabic graph `G(X)`. -/
abbrev NormalDart : Type _ := NormalOfTripleDart X.InDart b

/-- The label `i` (if any) of the target `t_i` whose dart outside `B` is `y`, found by searching
the labels in order. -/
def targetLabel (y : H) : Option (Fin b) :=
  (List.finRange b).find? fun i => X.endDart (targetIndex i) = y

/-- The label `i` (if any) of the source `s_i` whose dart outside `B` is `z`, found by searching
the labels in order. -/
def sourceLabel (z : H) : Option (Fin b) :=
  (List.finRange b).find? fun i => X.endDart (sourceIndex i) = z

/-- The map `ψ` on darts: `ψ(y) = \overline{σ⁻¹(y)}` unless `y = n_{2i}` is the dart of a target
`t_i` outside `B`, in which case `ψ(y) = \overline{n_{2i-1}}`. -/
def psiFun (y : H) : H :=
  match X.targetLabel y with
  | some i => X.inv (X.endDart (sourceIndex i))
  | none => X.inv (X.rot.symm y)

/-- The inverse `χ` of `ψ`: `χ(y') = σ(\bar y')` unless `\bar y' = n_{2i-1}` is the dart of a
source `s_i` outside `B`, in which case `χ(y') = n_{2i}`. -/
def chiFun (y : H) : H :=
  match X.sourceLabel (X.inv y) with
  | some i => X.endDart (targetIndex i)
  | none => X.rot (X.inv y)

variable {X}

/-- A dart lies in `I` if and only if it is outside `B` and is an in-dart. -/
theorem mem_inDarts {y : H} : y ∈ X.inDarts ↔ y ∉ X.bdry ∧ X.isOut y = false := by
  simp [inDarts]

omit [Fintype H] in
/-- If `y` has target label `i`, then `y` is the dart `n_{2i}` of the target `t_i`. -/
theorem endDart_of_targetLabel_eq_some {y : H} {i : Fin b} (h : X.targetLabel y = some i) :
    X.endDart (targetIndex i) = y := by
  simpa using List.find?_some h

omit [Fintype H] in
/-- A dart has no target label if and only if it is the dart of no target. -/
theorem targetLabel_eq_none_iff {y : H} :
    X.targetLabel y = none ↔ ∀ i, X.endDart (targetIndex i) ≠ y := by
  simp [targetLabel, List.find?_eq_none]

omit [Fintype H] in
/-- If `z` has source label `i`, then `z` is the dart `n_{2i-1}` of the source `s_i`. -/
theorem endDart_of_sourceLabel_eq_some {z : H} {i : Fin b} (h : X.sourceLabel z = some i) :
    X.endDart (sourceIndex i) = z := by
  simpa using List.find?_some h

omit [Fintype H] in
/-- A dart has no source label if and only if it is the dart of no source. -/
theorem sourceLabel_eq_none_iff {z : H} :
    X.sourceLabel z = none ↔ ∀ i, X.endDart (sourceIndex i) ≠ z := by
  simp [sourceLabel, List.find?_eq_none]

omit [Fintype H] in
/-- If `y` has target label `i`, then `ψ(y) = \overline{n_{2i-1}}`. -/
theorem psiFun_of_some {y : H} {i : Fin b} (h : X.targetLabel y = some i) :
    X.psiFun y = X.inv (X.endDart (sourceIndex i)) := by
  simp [psiFun, h]

omit [Fintype H] in
/-- If `y` has no target label, then `ψ(y) = \overline{σ⁻¹(y)}`. -/
theorem psiFun_of_none {y : H} (h : X.targetLabel y = none) :
    X.psiFun y = X.inv (X.rot.symm y) := by
  simp [psiFun, h]

omit [Fintype H] in
/-- If `\bar y` has source label `i`, then `χ(y) = n_{2i}`. -/
theorem chiFun_of_some {y : H} {i : Fin b} (h : X.sourceLabel (X.inv y) = some i) :
    X.chiFun y = X.endDart (targetIndex i) := by
  simp [chiFun, h]

omit [Fintype H] in
/-- If `\bar y` has no source label, then `χ(y) = σ(\bar y)`. -/
theorem chiFun_of_none {y : H} (h : X.sourceLabel (X.inv y) = none) :
    X.chiFun y = X.rot (X.inv y) := by
  simp [chiFun, h]

namespace IsPreTripleDiagram

variable (hX : X.IsPreTripleDiagram)

include hX

/-- The darts `n_r` outside `B` at the endpoints are pairwise distinct. -/
theorem endDart_injective : Function.Injective X.endDart := fun r s h =>
  hX.endpoint_injective (by simp only [endpoint, h])

/-- The target label of the dart `n_{2i}` of the target `t_i` is `i`. -/
theorem targetLabel_endDart (i : Fin b) : X.targetLabel (X.endDart (targetIndex i)) = some i := by
  have hs : (X.targetLabel (X.endDart (targetIndex i))).isSome := by
    unfold targetLabel
    exact List.find?_isSome.2 ⟨i, List.mem_finRange i, by simp⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hs
  rw [hj, targetIndex_injective (hX.endDart_injective (endDart_of_targetLabel_eq_some hj))]

/-- The source label of the dart `n_{2i-1}` of the source `s_i` is `i`. -/
theorem sourceLabel_endDart (i : Fin b) : X.sourceLabel (X.endDart (sourceIndex i)) = some i := by
  have hs : (X.sourceLabel (X.endDart (sourceIndex i))).isSome := by
    unfold sourceLabel
    exact List.find?_isSome.2 ⟨i, List.mem_finRange i, by simp⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hs
  rw [hj, sourceIndex_injective (hX.endDart_injective (endDart_of_sourceLabel_eq_some hj))]

/-- The dart `n_r` lies at a boundary vertex. -/
theorem isBoundaryVertex_endDart (r : Fin (2 * b)) :
    X.IsBoundaryVertex (X.vertexOf (X.endDart r)) :=
  X.vertexOf_mem_boundaryVertices.1 (hX.endpoint_mem r)

/-- The dart outside `B` at an endpoint `ε(r)` is `n_r`. -/
theorem eq_endDart_of_mem_endpoint {z : H} {r : Fin (2 * b)} (hz : z ∈ X.endpoint r)
    (hzB : z ∉ X.bdry) : z = X.endDart r :=
  DiskMap.eq_of_notMem_bdry hX.boundaryVertex_card (hX.isBoundaryVertex_endDart r) hz
    (X.self_mem_vertexOf _) hzB (hX.endDart_notMem_bdry r)

/-- A dart outside `B` at an endpoint is some `n_r`. -/
theorem exists_endDart_eq {z : H} (hz : X.IsBoundaryVertex (X.vertexOf z)) (hzB : z ∉ X.bdry) :
    ∃ r, X.endDart r = z := by
  obtain ⟨r, hr⟩ := hX.exists_endpoint_eq _ (X.vertexOf_mem_boundaryVertices.2 hz)
  refine ⟨r, (hX.eq_endDart_of_mem_endpoint ?_ hzB).symm⟩
  rw [hr]
  exact X.self_mem_vertexOf z

/-- A dart at an internal vertex has no target label. -/
theorem targetLabel_eq_none_of_internal {y : H} (hy : ¬X.IsBoundaryVertex (X.vertexOf y)) :
    X.targetLabel y = none :=
  targetLabel_eq_none_iff.2 fun _ hi => hy (hi ▸ hX.isBoundaryVertex_endDart _)

/-- A dart at an internal vertex has no source label. -/
theorem sourceLabel_eq_none_of_internal {y : H} (hy : ¬X.IsBoundaryVertex (X.vertexOf y)) :
    X.sourceLabel y = none :=
  sourceLabel_eq_none_iff.2 fun _ hi => hy (hi ▸ hX.isBoundaryVertex_endDart _)

/-- An in-dart outside `B` that is not the dart of a target lies at a triple point. -/
theorem not_isBoundaryVertex_of_targetLabel_eq_none {y : H} (hy : y ∈ X.inDarts)
    (h : X.targetLabel y = none) : ¬X.IsBoundaryVertex (X.vertexOf y) := by
  intro hb
  obtain ⟨hyB, hyo⟩ := mem_inDarts.1 hy
  obtain ⟨r, rfl⟩ := hX.exists_endDart_eq hb hyB
  rcases exists_sourceIndex_or_targetIndex r with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · rw [hX.isOut_source] at hyo
    exact Bool.noConfusion hyo
  · rw [hX.targetLabel_endDart] at h
    simp at h

/-- An out-dart outside `B` that is not the dart of a source lies at a triple point. -/
theorem not_isBoundaryVertex_of_sourceLabel_eq_none {z : H} (hzB : z ∉ X.bdry)
    (hzo : X.isOut z = true) (h : X.sourceLabel z = none) :
    ¬X.IsBoundaryVertex (X.vertexOf z) := by
  intro hb
  obtain ⟨r, rfl⟩ := hX.exists_endDart_eq hb hzB
  rcases exists_sourceIndex_or_targetIndex r with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · rw [hX.sourceLabel_endDart] at h
    simp at h
  · rw [hX.isOut_target] at hzo
    exact Bool.noConfusion hzo

/-- The dart `n_{2i}` of the target `t_i` lies in `I`. -/
theorem endDart_targetIndex_mem_inDarts (i : Fin b) : X.endDart (targetIndex i) ∈ X.inDarts :=
  mem_inDarts.2 ⟨hX.endDart_notMem_bdry _, hX.isOut_target i⟩

/-- `ψ` maps `I` to `I`. -/
theorem psiFun_mem {y : H} (hy : y ∈ X.inDarts) : X.psiFun y ∈ X.inDarts := by
  rcases h : X.targetLabel y with _ | i
  · rw [psiFun_of_none h]
    have hi := hX.not_isBoundaryVertex_of_targetLabel_eq_none hy h
    have hi' : ¬X.IsBoundaryVertex (X.vertexOf (X.rot.symm y)) := by
      rwa [X.vertexOf_eq_of_mem (X.rot_symm_mem_vertexOf y)]
    have hB := X.notMem_bdry_of_not_isBoundaryVertex hi'
    refine mem_inDarts.2 ⟨hX.inv_notMem_bdry hB, ?_⟩
    rw [hX.isOut_inv_apply hB]
    have := hX.isOut_rot_apply hi'
    rw [Equiv.apply_symm_apply, (mem_inDarts.1 hy).2] at this
    cases h' : X.isOut (X.rot.symm y) <;> simp_all
  · rw [psiFun_of_some h]
    have hB := hX.endDart_notMem_bdry (sourceIndex i)
    refine mem_inDarts.2 ⟨hX.inv_notMem_bdry hB, ?_⟩
    rw [hX.isOut_inv_apply hB, hX.isOut_source]
    rfl

/-- `χ` maps `I` to `I`. -/
theorem chiFun_mem {y : H} (hy : y ∈ X.inDarts) : X.chiFun y ∈ X.inDarts := by
  obtain ⟨hyB, hyo⟩ := mem_inDarts.1 hy
  have hiB := hX.inv_notMem_bdry hyB
  have hio : X.isOut (X.inv y) = true := by rw [hX.isOut_inv_apply hyB, hyo]; rfl
  rcases h : X.sourceLabel (X.inv y) with _ | i
  · rw [chiFun_of_none h]
    have hi := hX.not_isBoundaryVertex_of_sourceLabel_eq_none hiB hio h
    have hi' : ¬X.IsBoundaryVertex (X.vertexOf (X.rot (X.inv y))) := by rwa [X.vertexOf_rot]
    refine mem_inDarts.2 ⟨X.notMem_bdry_of_not_isBoundaryVertex hi', ?_⟩
    rw [hX.isOut_rot_apply hi, hio]
    rfl
  · rw [chiFun_of_some h]
    exact hX.endDart_targetIndex_mem_inDarts i

/-- `χ(ψ(y)) = y` for `y ∈ I`. -/
theorem chiFun_psiFun {y : H} (hy : y ∈ X.inDarts) : X.chiFun (X.psiFun y) = y := by
  rcases h : X.targetLabel y with _ | i
  · rw [psiFun_of_none h]
    have hi := hX.not_isBoundaryVertex_of_targetLabel_eq_none hy h
    have hi' : ¬X.IsBoundaryVertex (X.vertexOf (X.rot.symm y)) := by
      rwa [X.vertexOf_eq_of_mem (X.rot_symm_mem_vertexOf y)]
    have hs : X.sourceLabel (X.inv (X.inv (X.rot.symm y))) = none := by
      rw [hX.inv_inv_apply]
      exact hX.sourceLabel_eq_none_of_internal hi'
    rw [chiFun_of_none hs, hX.inv_inv_apply, Equiv.apply_symm_apply]
  · rw [psiFun_of_some h]
    have hs : X.sourceLabel (X.inv (X.inv (X.endDart (sourceIndex i)))) = some i := by
      rw [hX.inv_inv_apply]
      exact hX.sourceLabel_endDart i
    rw [chiFun_of_some hs, endDart_of_targetLabel_eq_some h]

/-- `ψ(χ(y)) = y` for `y ∈ I`. -/
theorem psiFun_chiFun {y : H} (hy : y ∈ X.inDarts) : X.psiFun (X.chiFun y) = y := by
  obtain ⟨hyB, hyo⟩ := mem_inDarts.1 hy
  have hiB := hX.inv_notMem_bdry hyB
  have hio : X.isOut (X.inv y) = true := by rw [hX.isOut_inv_apply hyB, hyo]; rfl
  rcases h : X.sourceLabel (X.inv y) with _ | i
  · rw [chiFun_of_none h]
    have hi := hX.not_isBoundaryVertex_of_sourceLabel_eq_none hiB hio h
    have hi' : ¬X.IsBoundaryVertex (X.vertexOf (X.rot (X.inv y))) := by rwa [X.vertexOf_rot]
    rw [psiFun_of_none (hX.targetLabel_eq_none_of_internal hi'), Equiv.symm_apply_apply,
      hX.inv_inv_apply]
  · rw [chiFun_of_some h, psiFun_of_some (hX.targetLabel_endDart i),
      endDart_of_sourceLabel_eq_some h, hX.inv_inv_apply]

/-- The permutation `ψ` of `I`. -/
def psi : Equiv.Perm X.InDart where
  toFun y := ⟨X.psiFun y, hX.psiFun_mem y.2⟩
  invFun y := ⟨X.chiFun y, hX.chiFun_mem y.2⟩
  left_inv y := Subtype.ext (hX.chiFun_psiFun y.2)
  right_inv y := Subtype.ext (hX.psiFun_chiFun y.2)

/-- The permutation `ψ` of `I` is given by `psiFun`. -/
@[simp]
theorem coe_psi (y : X.InDart) : (hX.psi y : H) = X.psiFun y := rfl

/-- The inverse of `ψ` is given by `chiFun`. -/
@[simp]
theorem coe_psi_symm (y : X.InDart) : (hX.psi.symm y : H) = X.chiFun y := rfl

/-- At a triple point, `σ²` maps an in-dart to an in-dart again at a triple point. -/
theorem rot_rot_mem {y : H} (hy : y ∈ X.inDarts) (h : X.targetLabel y = none) :
    X.rot (X.rot y) ∈ X.inDarts ∧ X.targetLabel (X.rot (X.rot y)) = none := by
  have hi := hX.not_isBoundaryVertex_of_targetLabel_eq_none hy h
  have hi1 : ¬X.IsBoundaryVertex (X.vertexOf (X.rot y)) := by rwa [X.vertexOf_rot]
  have hi2 : ¬X.IsBoundaryVertex (X.vertexOf (X.rot (X.rot y))) := by rwa [X.vertexOf_rot]
  refine ⟨mem_inDarts.2 ⟨X.notMem_bdry_of_not_isBoundaryVertex hi2, ?_⟩,
    hX.targetLabel_eq_none_of_internal hi2⟩
  rw [hX.isOut_rot_apply hi1, hX.isOut_rot_apply hi, (mem_inDarts.1 hy).2]
  rfl

/-- At a triple point, `σ⁻²` maps an in-dart to an in-dart again at a triple point. -/
theorem rot_symm_rot_symm_mem {y : H} (hy : y ∈ X.inDarts) (h : X.targetLabel y = none) :
    X.rot.symm (X.rot.symm y) ∈ X.inDarts ∧
      X.targetLabel (X.rot.symm (X.rot.symm y)) = none := by
  have hi := hX.not_isBoundaryVertex_of_targetLabel_eq_none hy h
  have hi1 : ¬X.IsBoundaryVertex (X.vertexOf (X.rot.symm y)) := by
    rwa [X.vertexOf_eq_of_mem (X.rot_symm_mem_vertexOf y)]
  have hi2 : ¬X.IsBoundaryVertex (X.vertexOf (X.rot.symm (X.rot.symm y))) := by
    rwa [X.vertexOf_eq_of_mem (X.rot_symm_mem_vertexOf _)]
  refine ⟨mem_inDarts.2 ⟨X.notMem_bdry_of_not_isBoundaryVertex hi2, ?_⟩,
    hX.targetLabel_eq_none_of_internal hi2⟩
  have e1 := hX.isOut_rot_apply hi1
  have e2 := hX.isOut_rot_apply hi2
  rw [Equiv.apply_symm_apply] at e1 e2
  rw [(mem_inDarts.1 hy).2, e2] at e1
  simpa using e1.symm

/-! ### The data of `G(X)` -/

/-- The dart `n_{2i}` of the target `t_i` outside `B`, as an element of `I`. -/
def targetDart (i : Fin b) : X.InDart :=
  ⟨X.endDart (targetIndex i), hX.endDart_targetIndex_mem_inDarts i⟩

/-- The underlying dart of `targetDart i` is `n_{2i}`. -/
@[simp]
theorem coe_targetDart (i : Fin b) : (hX.targetDart i : H) = X.endDart (targetIndex i) := rfl

/-- An in-dart with target label `i` is `targetDart i`. -/
theorem eq_targetDart_of_targetLabel {y : X.InDart} {i : Fin b} (h : X.targetLabel y = some i) :
    y = hX.targetDart i :=
  Subtype.ext (endDart_of_targetLabel_eq_some h).symm

/-- The image of `c*_y` under the rotation of `G(X)`. -/
def rotStar (y : X.InDart) : X.NormalDart :=
  match h : X.targetLabel y with
  | some i => .hStar (finRotate b i)
  | none => .cStar ⟨X.rot (X.rot y), (hX.rot_rot_mem y.2 h).1⟩

/-- The image of `c*_y` under the inverse rotation of `G(X)`. -/
def rotInvStar (y : X.InDart) : X.NormalDart :=
  match h : X.targetLabel y with
  | some i => .h i
  | none => .cStar ⟨X.rot.symm (X.rot.symm y), (hX.rot_symm_rot_symm_mem y.2 h).1⟩

/-- If `y` has target label `i`, the rotation of `G(X)` sends `c*_y` to `h*_{i+1}`. -/
theorem rotStar_of_some {y : X.InDart} {i : Fin b} (h : X.targetLabel y = some i) :
    hX.rotStar y = .hStar (finRotate b i) := by
  simp only [rotStar]
  split
  · simp_all
  · simp_all

/-- If `y` has no target label, the rotation of `G(X)` sends `c*_y` to `c*_{σ²(y)}`. -/
theorem rotStar_of_none {y : X.InDart} (h : X.targetLabel y = none) :
    hX.rotStar y = .cStar ⟨X.rot (X.rot y), (hX.rot_rot_mem y.2 h).1⟩ := by
  simp only [rotStar]
  split
  · simp_all
  · rfl

/-- If `y` has target label `i`, the inverse rotation of `G(X)` sends `c*_y` to `h_i`. -/
theorem rotInvStar_of_some {y : X.InDart} {i : Fin b} (h : X.targetLabel y = some i) :
    hX.rotInvStar y = .h i := by
  simp only [rotInvStar]
  split
  · simp_all
  · simp_all

/-- If `y` has no target label, the inverse rotation of `G(X)` sends `c*_y` to `c*_{σ⁻²(y)}`. -/
theorem rotInvStar_of_none {y : X.InDart} (h : X.targetLabel y = none) :
    hX.rotInvStar y =
      .cStar ⟨X.rot.symm (X.rot.symm y), (hX.rot_symm_rot_symm_mem y.2 h).1⟩ := by
  simp only [rotInvStar]
  split
  · simp_all
  · rfl

/-- The rotation of `G(X)` as a function. -/
def normalRotFun : X.NormalDart → X.NormalDart
  | .c y => .c (hX.psi y)
  | .cStar y => hX.rotStar y
  | .h i => .cStar (hX.targetDart i)
  | .hStar i => .h ((finRotate b).symm i)

/-- The inverse rotation of `G(X)` as a function. -/
def normalRotInvFun : X.NormalDart → X.NormalDart
  | .c y => .c (hX.psi.symm y)
  | .cStar y => hX.rotInvStar y
  | .h i => .hStar (finRotate b i)
  | .hStar i => .cStar (hX.targetDart ((finRotate b).symm i))

/-- The rotation `σ_G` of `G(X)`: `c_y ↦ c_{ψ(y)}`, `c*_y ↦ c*_{σ²(y)}` for `y` at a triple point,
and the cycles `(h*_{i+1}, h_i, c*_{n_{2i}})`. -/
def normalRot : Equiv.Perm X.NormalDart where
  toFun := hX.normalRotFun
  invFun := hX.normalRotInvFun
  left_inv := by
    rintro (y | y | i | i)
    · simp [normalRotFun, normalRotInvFun]
    · rcases h : X.targetLabel y with _ | i
      · simp only [normalRotFun, hX.rotStar_of_none h, normalRotInvFun]
        rw [hX.rotInvStar_of_none (hX.rot_rot_mem y.2 h).2]
        congr 1
        exact Subtype.ext (by simp)
      · simp only [normalRotFun, hX.rotStar_of_some h, normalRotInvFun, Equiv.symm_apply_apply]
        rw [hX.eq_targetDart_of_targetLabel h]
    · simp only [normalRotFun, normalRotInvFun]
      rw [hX.rotInvStar_of_some (y := hX.targetDart _) (hX.targetLabel_endDart _)]
    · simp only [normalRotFun, normalRotInvFun, Equiv.apply_symm_apply]
  right_inv := by
    rintro (y | y | i | i)
    · simp [normalRotFun, normalRotInvFun]
    · rcases h : X.targetLabel y with _ | i
      · simp only [normalRotInvFun, hX.rotInvStar_of_none h, normalRotFun]
        rw [hX.rotStar_of_none (hX.rot_symm_rot_symm_mem y.2 h).2]
        congr 1
        exact Subtype.ext (by simp)
      · simp only [normalRotInvFun, hX.rotInvStar_of_some h, normalRotFun]
        rw [hX.eq_targetDart_of_targetLabel h]
    · simp only [normalRotInvFun, normalRotFun, Equiv.symm_apply_apply]
    · simp only [normalRotInvFun, normalRotFun]
      rw [hX.rotStar_of_some (y := hX.targetDart _) (hX.targetLabel_endDart _),
        Equiv.apply_symm_apply]

end IsPreTripleDiagram

/-! ### The normal plabic graph `G(X)` -/

variable (X) in
/-- **The normal plabic graph `G(X)` of a pre-triple diagram.** Let `I` be the set of in-darts
outside `B` (`TripleData.inDarts`), and `ψ(y) = \overline{σ⁻¹(y)}` for `y ∈ I` at a triple point,
`ψ(n_{2i}) = \overline{n_{2i-1}}` (`TripleData.psiFun`). The darts of `G(X)` are the symbols
`c_y`, `c*_y` for `y ∈ I` and `h_i`, `h*_i` for `i ∈ [1, b]` (`X.NormalDart`); the involution
pairs `c_y` with `c*_y` and `h_i` with `h*_i`; the rotation sends `c_y ↦ c_{ψ(y)}`,
`c*_y ↦ c*_{σ²(y)}` for `y` at a triple point, and consists of the cycles
`(h*_{i+1}, h_i, c*_{n_{2i}})`; `B_G = {h_i, h*_i}`; the leg at `i` is `c*_{n_{2i}}`, so that
`β_G(i)` is its orbit; the darts `c_y` are black and the darts `c*_y` at triple points white.

Labels are `0`-indexed: `i : Fin b` stands for the `1`-indexed `i + 1`, `n_{2i}` is
`X.endDart (targetIndex i)` and `h_{i+1}` is `h (finRotate b i)`. The colours of `h_i`, `h*_i`
and `c*_{n_{2i}}`, which lie at boundary vertices, are irrelevant and set to white. The rotation
needs `ψ` and `σ²` to preserve `I`, so the construction takes the hypothesis that `X` is a
pre-triple diagram. -/
@[cluster_algebras "def_normal_of_triple"]
def normalOfTriple (hX : X.IsPreTripleDiagram) : PlabicData X.NormalDart b where
  inv := NormalOfTripleDart.star
  rot := hX.normalRot
  bdry := univ.filter fun d => d.isH
  colour := NormalOfTripleDart.colour
  leg i := .cStar (hX.targetDart i)

namespace IsPreTripleDiagram

variable (hX : X.IsPreTripleDiagram)

/-- The involution of `G(X)` is `c_y ↔ c*_y`, `h_i ↔ h*_i`. -/
@[simp] theorem normalOfTriple_inv : (X.normalOfTriple hX).inv = NormalOfTripleDart.star := rfl
/-- The rotation of `G(X)` is `normalRot`. -/
@[simp] theorem normalOfTriple_rot : (X.normalOfTriple hX).rot = hX.normalRot := rfl
/-- The colouring of `G(X)`: the darts `c_y` are black, all others white. -/
@[simp] theorem normalOfTriple_colour :
    (X.normalOfTriple hX).colour = NormalOfTripleDart.colour := rfl
/-- The leg of `G(X)` at `i` is `c*_{n_{2i}}`. -/
@[simp, cluster_algebras "lem_normal_of_triple_pregraph"]
theorem normalOfTriple_leg (i : Fin b) :
    (X.normalOfTriple hX).leg i = .cStar (hX.targetDart i) := rfl

/-- The darts of `B_G` are the darts `h_i`, `h*_i`. -/
@[simp]
theorem mem_normalOfTriple_bdry {d : X.NormalDart} :
    d ∈ (X.normalOfTriple hX).bdry ↔ d.isH = true := by
  simp [normalOfTriple]

/-- The rotation of `G(X)` sends `c_y` to `c_{ψ(y)}`. -/
@[simp] theorem normalRot_c (y : X.InDart) : hX.normalRot (.c y) = .c (hX.psi y) := rfl
/-- The rotation of `G(X)` sends `h_i` to `c*_{n_{2i}}`. -/
@[simp] theorem normalRot_h (i : Fin b) : hX.normalRot (.h i) = .cStar (hX.targetDart i) := rfl
/-- The rotation of `G(X)` sends `h*_{i+1}` to `h_i`. -/
@[simp] theorem normalRot_hStar (i : Fin b) :
    hX.normalRot (.hStar i) = .h ((finRotate b).symm i) := rfl

/-- If `y` has target label `i`, the rotation of `G(X)` sends `c*_y` to `h*_{i+1}`. -/
theorem normalRot_cStar_of_some {y : X.InDart} {i : Fin b} (h : X.targetLabel y = some i) :
    hX.normalRot (.cStar y) = .hStar (finRotate b i) :=
  hX.rotStar_of_some h

/-- If `y` has no target label, the rotation of `G(X)` sends `c*_y` to `c*_{σ²(y)}`. -/
theorem normalRot_cStar_of_none {y : X.InDart} (h : X.targetLabel y = none) :
    hX.normalRot (.cStar y) = .cStar ⟨X.rot (X.rot y), (hX.rot_rot_mem y.2 h).1⟩ :=
  hX.rotStar_of_none h

/-- The rotation of `G(X)` sends `c*_{n_{2i}}` to `h*_{i+1}`. -/
theorem normalRot_cStar_targetDart (i : Fin b) :
    hX.normalRot (.cStar (hX.targetDart i)) = .hStar (finRotate b i) :=
  hX.normalRot_cStar_of_some (hX.targetLabel_endDart i)

/-! ### The vertices of `G(X)` -/

/-- The boundary vertex of `G(X)` through `h_i` is `{h_i, c*_{n_{2i}}, h*_{i+1}}`. -/
theorem vertexOf_normalOfTriple_h (i : Fin b) :
    (X.normalOfTriple hX).vertexOf (.h i) =
      {.h i, .cStar (hX.targetDart i), .hStar (finRotate b i)} :=
  vertexOf_eq_three' _ rfl (hX.normalRot_cStar_targetDart i)
    (congrArg NormalOfTripleDart.h ((finRotate b).symm_apply_apply i))

/-- The darts `c*_{n_{2i}}` and `h_i` lie at the same vertex of `G(X)`. -/
theorem vertexOf_normalOfTriple_cStar_targetDart (i : Fin b) :
    (X.normalOfTriple hX).vertexOf (.cStar (hX.targetDart i)) =
      (X.normalOfTriple hX).vertexOf (.h i) := by
  rw [← RotationSystem.vertexOf_rot _ (NormalOfTripleDart.h i)]
  rfl

/-- The darts `h*_{i+1}` and `h_i` lie at the same vertex of `G(X)`. -/
theorem vertexOf_normalOfTriple_hStar (i : Fin b) :
    (X.normalOfTriple hX).vertexOf (.hStar i) =
      (X.normalOfTriple hX).vertexOf (.h ((finRotate b).symm i)) := by
  rw [← RotationSystem.vertexOf_rot _ (NormalOfTripleDart.hStar i)]
  rfl

/-- The vertex of `h_i` is a boundary vertex of `G(X)`. -/
theorem isBoundaryVertex_normalOfTriple_h (i : Fin b) :
    (X.normalOfTriple hX).IsBoundaryVertex ((X.normalOfTriple hX).vertexOf (.h i)) :=
  ⟨.h i, RotationSystem.self_mem_vertexOf _ _, by simp⟩

/-- If `y` has a target label, the vertex of `c*_y` is a boundary vertex of `G(X)`. -/
theorem isBoundaryVertex_normalOfTriple_cStar_of_some {y : X.InDart} {i : Fin b}
    (h : X.targetLabel y = some i) :
    (X.normalOfTriple hX).IsBoundaryVertex ((X.normalOfTriple hX).vertexOf (.cStar y)) := by
  rw [hX.eq_targetDart_of_targetLabel h, vertexOf_normalOfTriple_cStar_targetDart]
  exact hX.isBoundaryVertex_normalOfTriple_h i

/-- The vertex of `c_y` in `G(X)` is not a boundary vertex. -/
theorem not_isBoundaryVertex_normalOfTriple_c (y : X.InDart) :
    ¬(X.normalOfTriple hX).IsBoundaryVertex ((X.normalOfTriple hX).vertexOf (.c y)) := by
  rintro ⟨e, he, heB⟩
  obtain ⟨y', rfl⟩ := mem_of_sameCycle_of_closed' (f := (X.normalOfTriple hX).rot)
    (P := fun d => ∃ y', d = NormalOfTripleDart.c y') (by rintro _ ⟨y', rfl⟩; exact ⟨_, rfl⟩)
    ⟨y, rfl⟩ ((RotationSystem.mem_vertexOf _).1 he)
  simp at heB

/-- For `y` at a triple point, the vertex of `c*_y` in `G(X)` is not a boundary vertex. -/
theorem not_isBoundaryVertex_normalOfTriple_cStar {y : X.InDart} (h : X.targetLabel y = none) :
    ¬(X.normalOfTriple hX).IsBoundaryVertex ((X.normalOfTriple hX).vertexOf (.cStar y)) := by
  rintro ⟨e, he, heB⟩
  obtain ⟨y', -, rfl⟩ := mem_of_sameCycle_of_closed' (f := (X.normalOfTriple hX).rot)
    (P := fun d => ∃ y' : X.InDart, X.targetLabel y' = none ∧ d = NormalOfTripleDart.cStar y')
    (by
      rintro _ ⟨y', hy', rfl⟩
      exact ⟨_, (hX.rot_rot_mem y'.2 hy').2, hX.normalRot_cStar_of_none hy'⟩)
    ⟨y, h, rfl⟩ ((RotationSystem.mem_vertexOf _).1 he)
  simp at heB

/-- A dart of `G(X)` at an internal vertex is some `c_y`, or some `c*_y` with `y` at a triple
point. -/
theorem internal_cases_normalOfTriple {d : X.NormalDart}
    (hd : ¬(X.normalOfTriple hX).IsBoundaryVertex ((X.normalOfTriple hX).vertexOf d)) :
    (∃ y, d = .c y) ∨ ∃ y : X.InDart, X.targetLabel y = none ∧ d = .cStar y := by
  rcases d with y | y | i | i
  · exact Or.inl ⟨y, rfl⟩
  · rcases h : X.targetLabel y with _ | i
    · exact Or.inr ⟨y, h, rfl⟩
    · exact absurd (hX.isBoundaryVertex_normalOfTriple_cStar_of_some h) hd
  · exact absurd ⟨.h i, RotationSystem.self_mem_vertexOf _ _, by simp⟩ hd
  · exact absurd ⟨.hStar i, RotationSystem.self_mem_vertexOf _ _, by simp⟩ hd

/-- Every boundary vertex of `G(X)` is the vertex of some `h_i`. -/
theorem exists_vertexOf_normalOfTriple_eq_h {d : X.NormalDart}
    (hd : (X.normalOfTriple hX).IsBoundaryVertex ((X.normalOfTriple hX).vertexOf d)) :
    ∃ i, (X.normalOfTriple hX).vertexOf d = (X.normalOfTriple hX).vertexOf (.h i) := by
  obtain ⟨e, he, heB⟩ := hd
  rw [← RotationSystem.vertexOf_eq_of_mem _ he]
  rcases e with y | y | i | i
  · simp at heB
  · simp at heB
  · exact ⟨i, rfl⟩
  · exact ⟨_, hX.vertexOf_normalOfTriple_hStar i⟩

/-- The white vertex of `G(X)` at a triple point consists of three darts. -/
theorem card_vertexOf_normalOfTriple_cStar {y : X.InDart} (h : X.targetLabel y = none) :
    ((X.normalOfTriple hX).vertexOf (.cStar y)).card = 3 := by
  have h1 := hX.rot_rot_mem y.2 h
  have h2 := hX.rot_rot_mem h1.1 h1.2
  have hi := hX.not_isBoundaryVertex_of_targetLabel_eq_none y.2 h
  obtain ⟨h6, hdist⟩ := hX.rot_pow_six hi
  have e3 : (X.normalOfTriple hX).rot (.cStar ⟨_, h2.1⟩) = .cStar y := by
    rw [normalOfTriple_rot, hX.normalRot_cStar_of_none h2.2]
    congr 1
    exact Subtype.ext h6
  rw [vertexOf_eq_three' _ (hX.normalRot_cStar_of_none h) (hX.normalRot_cStar_of_none h1.2) e3,
    card_eq_three]
  refine ⟨_, _, _, fun he => ?_, fun he => ?_, fun he => ?_, rfl⟩
  · have := hdist 0 2 (by norm_num) (by norm_num)
      (congrArg Subtype.val (NormalOfTripleDart.cStar.inj he))
    omega
  · have := hdist 0 4 (by norm_num) (by norm_num)
      (congrArg Subtype.val (NormalOfTripleDart.cStar.inj he))
    omega
  · have := hdist 2 4 (by norm_num) (by norm_num)
      (congrArg Subtype.val (NormalOfTripleDart.cStar.inj he))
    omega

/-- The orbit of `φ_G` through `h_i` is `{h_j : j ∈ [1, b]}`. -/
theorem faceOf_normalOfTriple_h (i : Fin b) :
    (X.normalOfTriple hX).faceOf (.h i) = univ.image NormalOfTripleDart.h := by
  have hb := hX.one_le
  have key : ∀ (n : ℕ) (hn : n < b), (X.normalOfTriple hX).facePerm.SameCycle
      (.h ⟨n, hn⟩) (.h ⟨0, by omega⟩) := by
    intro n
    induction n with
    | zero => exact fun _ => .refl _ _
    | succ n ih =>
      intro hn
      have h1 : (X.normalOfTriple hX).facePerm (.h ⟨n + 1, hn⟩) = .h ⟨n, by omega⟩ := by
        change NormalOfTripleDart.h _ = _
        congr 1
        rw [Equiv.symm_apply_eq]
        apply Fin.ext
        rw [val_finRotate']
        exact (Nat.mod_eq_of_lt hn).symm
      have h2 : (X.normalOfTriple hX).facePerm.SameCycle (.h ⟨n + 1, hn⟩)
          ((X.normalOfTriple hX).facePerm (.h ⟨n + 1, hn⟩)) :=
        Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
      rw [h1] at h2
      exact h2.trans (ih (by omega))
  ext e
  rw [RotationSystem.mem_faceOf]
  constructor
  · intro he
    refine mem_of_sameCycle_of_closed' (f := (X.normalOfTriple hX).facePerm)
      (P := fun d => d ∈ univ.image NormalOfTripleDart.h) ?_ (by simp) he
    intro x hx
    obtain ⟨s, -, rfl⟩ := mem_image.1 hx
    exact mem_image_of_mem _ (mem_univ _)
  · intro he
    obtain ⟨s, -, rfl⟩ := mem_image.1 he
    exact (key i i.2).trans (key s s.2).symm

/-- The darts of `G(X)` at the boundary vertex `β_G(i)` outside `B_G`: the leg `c*_{n_{2i}}`. -/
theorem filter_bvertex_normalOfTriple (i : Fin b) :
    ((X.normalOfTriple hX).bvertex i).filter (· ∉ (X.normalOfTriple hX).bdry) =
      {.cStar (hX.targetDart i)} := by
  rw [PlabicData.bvertex, normalOfTriple_leg, vertexOf_normalOfTriple_cStar_targetDart,
    vertexOf_normalOfTriple_h]
  ext z
  simp only [mem_filter, mem_insert, mem_singleton, mem_normalOfTriple_bdry]
  constructor
  · rintro ⟨rfl | rfl | rfl, hz⟩ <;> simp_all
  · rintro rfl
    simp

include hX in
/-- **`G(X)` is a normal plabic pregraph**, first part: `ψ` is a permutation of the set `I` of
in-darts outside `B`. -/
@[cluster_algebras "lem_normal_of_triple_pregraph"]
theorem bijOn_psiFun : Set.BijOn X.psiFun (X.inDarts : Set H) (X.inDarts : Set H) := by
  refine ⟨fun y hy => hX.psiFun_mem hy, fun y hy y' hy' he => ?_, fun y hy => ?_⟩
  · rw [← hX.chiFun_psiFun hy, he, hX.chiFun_psiFun hy']
  · exact ⟨X.chiFun y, hX.chiFun_mem hy, hX.psiFun_chiFun hy⟩

/-- **`G(X)` is a normal plabic pregraph**, second part: for a pre-triple diagram `X` with `b`
arcs, `G(X)` is a normal plabic pregraph with `b` boundary vertices; its leg at `i` is
`c*_{n_{2i}}` (`normalOfTriple_leg`). -/
@[cluster_algebras "lem_normal_of_triple_pregraph"]
theorem isNormalPlabicPregraph_normalOfTriple :
    (X.normalOfTriple hX).IsNormalPlabicPregraph where
  colour_inv_ne d hd _ := by
    rcases hX.internal_cases_normalOfTriple hd with ⟨y, rfl⟩ | ⟨y, -, rfl⟩ <;> simp
  card_vertexOf_of_white d hd hc := by
    rcases hX.internal_cases_normalOfTriple hd with ⟨y, rfl⟩ | ⟨y, hy, rfl⟩
    · simp at hc
    · exact hX.card_vertexOf_normalOfTriple_cStar hy
  not_isBoundaryVertex_inv_leg i := hX.not_isBoundaryVertex_normalOfTriple_c _
  colour_inv_leg _ := rfl
  one_le := hX.one_le
  nonempty := ⟨.h ⟨0, by have := hX.one_le; omega⟩⟩
  inv_involutive := by rintro (_ | _ | _ | _) <;> rfl
  inv_ne := by rintro (_ | _ | _ | _) <;> simp
  inv_mem_bdry := by rintro (_ | _ | _ | _) <;> simp
  boundaryVertex_card v hv := by
    obtain ⟨hvV, hvB⟩ := DiskMap.mem_boundaryVertices _ |>.1 hv
    obtain ⟨d, rfl⟩ := RotationSystem.mem_vertices _ |>.1 hvV
    obtain ⟨i, hi⟩ := hX.exists_vertexOf_normalOfTriple_eq_h hvB
    rw [hi, vertexOf_normalOfTriple_h]
    refine ⟨by rw [card_eq_three]; exact ⟨_, _, _, by simp, by simp, by simp, rfl⟩, ?_⟩
    have : ({.h i, .cStar (hX.targetDart i), .hStar (finRotate b i)} : Finset X.NormalDart).filter
        (· ∈ (X.normalOfTriple hX).bdry) = {.h i, .hStar (finRotate b i)} := by
      ext z
      simp only [mem_filter, mem_insert, mem_singleton, mem_normalOfTriple_bdry]
      constructor
      · rintro ⟨rfl | rfl | rfl, hz⟩ <;> simp_all
      · rintro (rfl | rfl) <;> simp
    rw [this, card_pair (by simp)]
  exists_orbit := by
    have hb := hX.one_le
    refine ⟨univ.image NormalOfTripleDart.h, ?_, ?_, ?_, ?_⟩
    · rw [← hX.faceOf_normalOfTriple_h ⟨0, by omega⟩]
      exact RotationSystem.faceOf_mem_faceOrbits _ _
    · intro z hz
      obtain ⟨s, -, rfl⟩ := mem_image.1 hz
      simp
    · ext z
      rcases z with y | y | i | i <;> simp [mem_map_equiv]
    · rw [disjoint_left]
      intro z hz hz'
      obtain ⟨s, -, rfl⟩ := mem_image.1 hz
      simp [mem_map_equiv] at hz'
  colour_rot d _ := by
    rcases d with y | y | i | i
    · rfl
    · rcases h : X.targetLabel y with _ | i
      · rw [normalOfTriple_rot, hX.normalRot_cStar_of_none h]
        rfl
      · rw [normalOfTriple_rot, hX.normalRot_cStar_of_some h]
        rfl
    · rfl
    · rfl
  leg_notMem_bdry i := by simp
  bvertex_mem i := by
    rw [PlabicData.bvertex, normalOfTriple_leg, vertexOf_normalOfTriple_cStar_targetDart]
    exact (X.normalOfTriple hX).vertexOf_mem_boundaryVertices.2
      (hX.isBoundaryVertex_normalOfTriple_h i)
  bvertex_injective i j hij := by
    simp only [PlabicData.bvertex, normalOfTriple_leg,
      vertexOf_normalOfTriple_cStar_targetDart] at hij
    have : (NormalOfTripleDart.h i : X.NormalDart) ∈ (X.normalOfTriple hX).vertexOf (.h j) :=
      hij ▸ RotationSystem.self_mem_vertexOf _ _
    rw [vertexOf_normalOfTriple_h] at this
    simpa using this
  exists_bvertex_eq v hv := by
    obtain ⟨hvV, hvB⟩ := DiskMap.mem_boundaryVertices _ |>.1 hv
    obtain ⟨d, rfl⟩ := RotationSystem.mem_vertices _ |>.1 hvV
    obtain ⟨i, hi⟩ := hX.exists_vertexOf_normalOfTriple_eq_h hvB
    refine ⟨i, ?_⟩
    rw [hi, PlabicData.bvertex, normalOfTriple_leg, vertexOf_normalOfTriple_cStar_targetDart]
  exists_exterior i := by
    refine ⟨.h (finRotate b i), ?_, ?_, ?_⟩
    · rw [DiskMap.mem_exterior]
      simp
    · rw [PlabicData.bvertex, normalOfTriple_leg, vertexOf_normalOfTriple_cStar_targetDart]
      exact RotationSystem.self_mem_vertexOf _ _
    · rw [PlabicData.bvertex, normalOfTriple_leg, vertexOf_normalOfTriple_cStar_targetDart,
        vertexOf_normalOfTriple_h]
      simp

/-! ### The exterior of a pre-triple diagram -/

include hX in
/-- The involution of a pre-triple diagram is its own inverse. -/
theorem inv_symm_apply (d : H) : X.inv.symm d = X.inv d := by
  rw [Equiv.symm_apply_eq, hX.inv_inv_apply]

include hX in
/-- The exterior and its reverse partition `B`. -/
theorem exterior_union_disjoint :
    X.exterior ∪ X.exterior.map X.inv.toEmbedding = X.bdry ∧
      Disjoint X.exterior (X.exterior.map X.inv.toEmbedding) := by
  obtain ⟨f, hf, hfB, hu, hd⟩ := hX.exists_orbit
  have := X.eq_exterior_of_mem_faceOrbits hX.inv_involutive hX.inv_mem_bdry
    hX.boundaryVertex_card hf hfB hu hd
  subst this
  exact ⟨hu, hd⟩

include hX in
/-- The reverse of a dart of the exterior is not in the exterior. -/
theorem inv_notMem_exterior {d : H} (hd : d ∈ X.exterior) : X.inv d ∉ X.exterior := by
  intro h
  refine disjoint_left.1 hX.exterior_union_disjoint.2 hd (mem_map_equiv.2 ?_)
  rwa [hX.inv_symm_apply]

/-- The dart `p_r` of the exterior at the endpoint `ε(r)`. -/
noncomputable def extDart (r : Fin (2 * b)) : H := DiskMap.exteriorDartAt hX.exists_exterior r

/-- The dart `p_r` lies in the exterior. -/
theorem extDart_mem_exterior (r : Fin (2 * b)) : hX.extDart r ∈ X.exterior :=
  (DiskMap.exteriorDartAt_spec hX.exists_exterior r).1

/-- The dart `p_r` lies at the endpoint `ε(r)`. -/
theorem extDart_mem_endpoint (r : Fin (2 * b)) : hX.extDart r ∈ X.endpoint r :=
  (DiskMap.exteriorDartAt_spec hX.exists_exterior r).2.1

/-- The dart `p_r` lies in `B`. -/
theorem extDart_mem_bdry (r : Fin (2 * b)) : hX.extDart r ∈ X.bdry :=
  X.exterior_subset_bdry (hX.extDart_mem_exterior r)

/-- The rotation at the endpoint `ε(r)` is `(p̄_{r+1}, p_r, n_r)`. -/
theorem rot_cycle_extDart (r : Fin (2 * b)) :
    X.endpoint r = {X.inv (hX.extDart (finRotate _ r)), hX.extDart r, X.endDart r} ∧
      X.rot (X.inv (hX.extDart (finRotate _ r))) = hX.extDart r ∧
      X.rot (hX.extDart r) = X.endDart r ∧
      X.rot (X.endDart r) = X.inv (hX.extDart (finRotate _ r)) :=
  DiskMap.rot_cycle_exteriorDartAt hX.inv_involutive hX.inv_mem_bdry hX.boundaryVertex_card
    hX.exists_orbit hX.exists_exterior (hX.endpoint_mem r) (X.self_mem_vertexOf _)
    (hX.endDart_notMem_bdry r)

/-- The darts `p_r` are pairwise distinct. -/
theorem extDart_injective : Function.Injective hX.extDart := by
  intro r s h
  apply hX.endpoint_injective
  have hr := X.vertexOf_eq_of_mem (hX.extDart_mem_endpoint r)
  have hs := X.vertexOf_eq_of_mem (hX.extDart_mem_endpoint s)
  rw [h] at hr
  exact hr.symm.trans hs

/-- Every dart of the exterior is some `p_r`. -/
theorem exists_extDart_eq {d : H} (hd : d ∈ X.exterior) : ∃ r, hX.extDart r = d := by
  have hv := X.isBoundaryVertex_vertexOf_of_mem (X.exterior_subset_bdry hd)
  obtain ⟨r, hr⟩ := hX.exists_endpoint_eq _ (X.vertexOf_mem_boundaryVertices.2 hv)
  refine ⟨r, DiskMap.eq_of_mem_exterior_of_mem_vertexOf hX.boundaryVertex_card hd
    (hX.extDart_mem_exterior r) ?_⟩
  rw [← hr]
  exact hX.extDart_mem_endpoint r

/-! ### The darts at black vertices of `G(X)` -/

/-- The darts at black vertices of `G(X)` are the darts `c_y`. -/
theorem mem_blackDarts_normalOfTriple {d : X.NormalDart} :
    d ∈ (X.normalOfTriple hX).blackDarts ↔ ∃ y, d = .c y := by
  rw [PlabicData.mem_blackDarts]
  constructor
  · rintro ⟨hd, hc⟩
    rcases hX.internal_cases_normalOfTriple hd with h | ⟨y, -, rfl⟩
    · exact h
    · simp at hc
  · rintro ⟨y, rfl⟩
    exact ⟨hX.not_isBoundaryVertex_normalOfTriple_c y, rfl⟩

/-- The symbol `y` of a dart `c_y` at a black vertex of `G(X)`. -/
def cOfBlack : (X.normalOfTriple hX).BlackDart → X.InDart
  | ⟨.c y, _⟩ => y
  | ⟨.cStar y, _⟩ => y
  | ⟨.h i, _⟩ => hX.targetDart i
  | ⟨.hStar i, _⟩ => hX.targetDart i

/-- The bijection `y ↦ c_y` from `I` onto the darts at black vertices of `G(X)`. -/
def cEquiv : X.InDart ≃ (X.normalOfTriple hX).BlackDart where
  toFun y := ⟨.c y, hX.mem_blackDarts_normalOfTriple.2 ⟨y, rfl⟩⟩
  invFun := hX.cOfBlack
  left_inv _ := rfl
  right_inv := by
    rintro ⟨d, hd⟩
    obtain ⟨y, rfl⟩ := hX.mem_blackDarts_normalOfTriple.1 hd
    rfl

/-- The underlying dart of `cEquiv y` is `c_y`. -/
@[simp]
theorem coe_cEquiv (y : X.InDart) : (hX.cEquiv y : X.NormalDart) = .c y := rfl

/-- The dart `c_y` is the reverse of the leg at `i` exactly when `y` has target label `i`. -/
theorem legIndex_cEquiv (y : X.InDart) :
    (X.normalOfTriple hX).legIndex (hX.cEquiv y) = X.targetLabel y := by
  simp only [PlabicData.legIndex, targetLabel, coe_cEquiv, normalOfTriple_inv, normalOfTriple_leg,
    NormalOfTripleDart.star_cStar, NormalOfTripleDart.c.injEq, Subtype.ext_iff, coe_targetDart]

/-- The reverse of the leg of `G(X)` at `i` is `c_{n_{2i}}`. -/
theorem invLeg_normalOfTriple (i : Fin b) :
    hX.isNormalPlabicPregraph_normalOfTriple.invLeg i = hX.cEquiv (hX.targetDart i) := rfl

/-- In `X(G(X))` the involution sends `x⁺_{c_y}` to `x⁻_{c_{ψ(y)}}`. -/
theorem tripleInv_plus_cEquiv (y : X.InDart) :
    hX.isNormalPlabicPregraph_normalOfTriple.tripleInv (.plus (hX.cEquiv y)) =
      .minus (hX.cEquiv (hX.psi y)) := rfl

/-- In `X(G(X))` the involution sends `x⁻_{c_y}` to `x⁺_{c_{ψ⁻¹(y)}}`. -/
theorem tripleInv_minus_cEquiv (y : X.InDart) :
    hX.isNormalPlabicPregraph_normalOfTriple.tripleInv (.minus (hX.cEquiv y)) =
      .plus (hX.cEquiv (hX.psi.symm y)) := rfl

/-- If `y` has no target label, the rotation of `X(G(X))` sends `x⁺_{c_y}` to `x⁻_{c_y}`. -/
theorem tripleRot_plus_cEquiv_of_none {y : X.InDart} (h : X.targetLabel y = none) :
    hX.isNormalPlabicPregraph_normalOfTriple.tripleRot (.plus (hX.cEquiv y)) =
      .minus (hX.cEquiv y) :=
  PlabicData.IsNormalPlabicPregraph.tripleRot_plus_of_none _ ((hX.legIndex_cEquiv y).trans h)

/-- If `y` has target label `i`, the rotation of `X(G(X))` sends `x⁺_{c_y}` to the symbol `∂'`
indexed by the successor of the source index of `i`. -/
theorem tripleRot_plus_cEquiv_of_some {y : X.InDart} {i : Fin b} (h : X.targetLabel y = some i) :
    hX.isNormalPlabicPregraph_normalOfTriple.tripleRot (.plus (hX.cEquiv y)) =
      .del' (finRotate _ (sourceIndex i)) :=
  PlabicData.IsNormalPlabicPregraph.tripleRot_plus_of_some _ ((hX.legIndex_cEquiv y).trans h)

/-- If `y` has no target label, the rotation of `X(G(X))` sends `x⁻_{c_y}` to
`x⁺_{c_{σ²(y)}}`. -/
theorem tripleRot_minus_cEquiv_of_none {y : X.InDart} (h : X.targetLabel y = none) :
    hX.isNormalPlabicPregraph_normalOfTriple.tripleRot (.minus (hX.cEquiv y)) =
      .plus (hX.cEquiv ⟨X.rot (X.rot y), (hX.rot_rot_mem y.2 h).1⟩) := by
  rw [PlabicData.IsNormalPlabicPregraph.tripleRot_minus_of_none _
    ((hX.legIndex_cEquiv y).trans h)]
  congr 1
  apply Subtype.ext
  rw [PlabicData.IsNormalPlabicPregraph.coe_psi, coe_cEquiv, normalOfTriple_inv,
    NormalOfTripleDart.star_c, normalOfTriple_rot, hX.normalRot_cStar_of_none h]
  rfl

/-- If `y` has target label `i`, the rotation of `X(G(X))` sends `x⁻_{c_y}` to the symbol `∂'`
indexed by the successor of the target index of `i`. -/
theorem tripleRot_minus_cEquiv_of_some {y : X.InDart} {i : Fin b}
    (h : X.targetLabel y = some i) :
    hX.isNormalPlabicPregraph_normalOfTriple.tripleRot (.minus (hX.cEquiv y)) =
      .del' (finRotate _ (targetIndex i)) :=
  PlabicData.IsNormalPlabicPregraph.tripleRot_minus_of_some _ ((hX.legIndex_cEquiv y).trans h)

/-! ### `X(G(X))` is isomorphic to `X` -/

/-- The map `x⁺_y ↦ \overline{ψ(y)}`, `x⁻_y ↦ y`, `∂_r ↦ p_r`, `∂'_r ↦ p̄_r` on the symbols of
`X(G(X))`, indexed by `y ∈ I` rather than by `c_y`. -/
noncomputable def tripleDartToDart : TripleOfNormalDart X.InDart (2 * b) → H
  | .plus y => X.inv (X.psiFun y)
  | .minus y => y
  | .del r => hX.extDart r
  | .del' r => X.inv (hX.extDart r)

/-- The kind of a symbol: `0` for `x⁺`, `1` for `x⁻`, `2` for `∂`, `3` for `∂'`. -/
private def symbolKind {K : Type*} {n : ℕ} : TripleOfNormalDart K n → ℕ
  | .plus _ => 0
  | .minus _ => 1
  | .del _ => 2
  | .del' _ => 3

private theorem kind_tripleDartToDart (z : TripleOfNormalDart X.InDart (2 * b)) :
    (if hX.tripleDartToDart z ∈ X.exterior then 2 else if hX.tripleDartToDart z ∈ X.bdry then 3
      else if X.isOut (hX.tripleDartToDart z) then 0 else 1) = symbolKind z := by
  rcases z with y | y | r | r
  · have hB := hX.inv_notMem_bdry (mem_inDarts.1 (hX.psiFun_mem y.2)).1
    have ho : X.isOut (X.inv (X.psiFun y)) = true := by
      rw [hX.isOut_inv_apply (mem_inDarts.1 (hX.psiFun_mem y.2)).1,
        (mem_inDarts.1 (hX.psiFun_mem y.2)).2]
      rfl
    simp only [tripleDartToDart, symbolKind]
    rw [if_neg (fun h => hB (X.exterior_subset_bdry h)), if_neg hB, if_pos ho]
  · have hB := (mem_inDarts.1 y.2).1
    simp only [tripleDartToDart, symbolKind]
    rw [if_neg (fun h => hB (X.exterior_subset_bdry h)), if_neg hB, if_neg (by
      rw [(mem_inDarts.1 y.2).2]; decide)]
  · simp only [tripleDartToDart, symbolKind]
    rw [if_pos (hX.extDart_mem_exterior r)]
  · simp only [tripleDartToDart, symbolKind]
    rw [if_neg (hX.inv_notMem_exterior (hX.extDart_mem_exterior r)),
      if_pos (hX.inv_mem_bdry _ (hX.extDart_mem_bdry r))]

/-- The map `tripleDartToDart` is injective. -/
theorem tripleDartToDart_injective : Function.Injective hX.tripleDartToDart := by
  intro z₁ z₂ h
  have hk := hX.kind_tripleDartToDart z₁
  rw [h, hX.kind_tripleDartToDart z₂] at hk
  rcases z₁ with y₁ | y₁ | r₁ | r₁ <;> rcases z₂ with y₂ | y₂ | r₂ | r₂ <;>
    simp only [symbolKind] at hk <;> (try omega) <;> simp only [tripleDartToDart] at h
  · congr 1
    apply Subtype.ext
    rw [← hX.chiFun_psiFun y₁.2, X.inv.injective h, hX.chiFun_psiFun y₂.2]
  · rw [Subtype.ext h]
  · rw [hX.extDart_injective h]
  · rw [hX.extDart_injective (X.inv.injective h)]

/-- The map `tripleDartToDart` is surjective. -/
theorem tripleDartToDart_surjective : Function.Surjective hX.tripleDartToDart := by
  intro z
  by_cases hzB : z ∈ X.bdry
  · by_cases hze : z ∈ X.exterior
    · obtain ⟨r, rfl⟩ := hX.exists_extDart_eq hze
      exact ⟨.del r, rfl⟩
    · rw [← hX.exterior_union_disjoint.1] at hzB
      rcases mem_union.1 hzB with h | h
      · exact absurd h hze
      · rw [mem_map_equiv, hX.inv_symm_apply] at h
        obtain ⟨r, hr⟩ := hX.exists_extDart_eq h
        refine ⟨.del' r, ?_⟩
        simp only [tripleDartToDart]
        rw [hr, hX.inv_inv_apply]
  · cases ho : X.isOut z
    · exact ⟨.minus ⟨z, mem_inDarts.2 ⟨hzB, ho⟩⟩, rfl⟩
    · have hy : X.inv z ∈ X.inDarts := by
        refine mem_inDarts.2 ⟨hX.inv_notMem_bdry hzB, ?_⟩
        rw [hX.isOut_inv_apply hzB, ho]
        rfl
      refine ⟨.plus ⟨X.chiFun (X.inv z), hX.chiFun_mem hy⟩, ?_⟩
      simp only [tripleDartToDart]
      rw [hX.psiFun_chiFun hy, hX.inv_inv_apply]

/-- The map `tripleDartToDart` is a bijection. -/
theorem tripleDartToDart_bijective : Function.Bijective hX.tripleDartToDart :=
  ⟨hX.tripleDartToDart_injective, hX.tripleDartToDart_surjective⟩

/-- The bijection `θ` from the darts of `X(G(X))` to the darts of `X`. -/
noncomputable def tripleOfNormalEquiv :
    (X.normalOfTriple hX).TripleDart ≃ H :=
  (TripleOfNormalDart.mapEquiv hX.cEquiv.symm).trans
    (Equiv.ofBijective _ hX.tripleDartToDart_bijective)

/-- `θ(x⁺_{c_y}) = \overline{ψ(y)}`. -/
@[simp]
theorem tripleOfNormalEquiv_plus (y : X.InDart) :
    hX.tripleOfNormalEquiv (.plus (hX.cEquiv y)) = X.inv (X.psiFun y) := by
  simp [tripleOfNormalEquiv, tripleDartToDart]

/-- `θ(x⁻_{c_y}) = y`. -/
@[simp]
theorem tripleOfNormalEquiv_minus (y : X.InDart) :
    hX.tripleOfNormalEquiv (.minus (hX.cEquiv y)) = y := by
  simp [tripleOfNormalEquiv, tripleDartToDart]

/-- `θ(∂_r) = p_r`. -/
@[simp]
theorem tripleOfNormalEquiv_del (r : Fin (2 * b)) :
    hX.tripleOfNormalEquiv (.del r) = hX.extDart r := rfl

/-- `θ(∂'_r) = p̄_r`. -/
@[simp]
theorem tripleOfNormalEquiv_del' (r : Fin (2 * b)) :
    hX.tripleOfNormalEquiv (.del' r) = X.inv (hX.extDart r) := rfl

/-- `θ` sends the dart of `X(G(X))` outside `B` at the endpoint `ε(r)` to `n_r`. -/
theorem tripleOfNormalEquiv_endDart (r : Fin (2 * b)) :
    hX.tripleOfNormalEquiv (hX.isNormalPlabicPregraph_normalOfTriple.endDart r) = X.endDart r := by
  rcases exists_sourceIndex_or_targetIndex r with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [PlabicData.IsNormalPlabicPregraph.endDart_sourceIndex, invLeg_normalOfTriple,
      tripleOfNormalEquiv_plus, coe_targetDart, psiFun_of_some (hX.targetLabel_endDart i),
      hX.inv_inv_apply]
  · rw [PlabicData.IsNormalPlabicPregraph.endDart_targetIndex, invLeg_normalOfTriple,
      tripleOfNormalEquiv_minus, coe_targetDart]

/-- **`X(G(X))` is isomorphic to `X`**: for a pre-triple diagram `X` with `b` arcs, with `p_r`
the dart of the exterior at `ε(r)`, the map `θ` with `θ(x⁻_{c_y}) = y`,
`θ(x⁺_{c_y}) = \overline{ψ(y)}` for `y ∈ I`, `θ(∂_r) = p_r` and `θ(∂'_r) = p̄_r` is an isomorphism
of pre-triple diagrams `X(G(X)) → X` (`tripleOfNormalIso_apply_plus`,
`tripleOfNormalIso_apply_minus`, `tripleOfNormalIso_apply_del`, `tripleOfNormalIso_apply_del'`). -/
@[cluster_algebras "lem_normal_triple_inverse_right"]
noncomputable def tripleOfNormalIso :
    ((X.normalOfTriple hX).tripleOfNormal hX.isNormalPlabicPregraph_normalOfTriple).Iso X where
  toEquiv := hX.tripleOfNormalEquiv
  map_inv := by
    rintro (k | k | r | r)
    · obtain ⟨y, rfl⟩ := hX.cEquiv.surjective k
      rw [PlabicData.IsNormalPlabicPregraph.tripleOfNormal_inv, tripleInv_plus_cEquiv,
        tripleOfNormalEquiv_minus, tripleOfNormalEquiv_plus, hX.inv_inv_apply]
      rfl
    · obtain ⟨y, rfl⟩ := hX.cEquiv.surjective k
      rw [PlabicData.IsNormalPlabicPregraph.tripleOfNormal_inv, tripleInv_minus_cEquiv,
        tripleOfNormalEquiv_minus, tripleOfNormalEquiv_plus, coe_psi_symm,
        hX.psiFun_chiFun y.2]
    · simp only [PlabicData.IsNormalPlabicPregraph.tripleOfNormal_inv,
        PlabicData.IsNormalPlabicPregraph.tripleInv_del, tripleOfNormalEquiv_del,
        tripleOfNormalEquiv_del']
    · simp only [PlabicData.IsNormalPlabicPregraph.tripleOfNormal_inv,
        PlabicData.IsNormalPlabicPregraph.tripleInv_del', tripleOfNormalEquiv_del,
        tripleOfNormalEquiv_del', hX.inv_inv_apply]
  map_rot := by
    rintro (k | k | r | r)
    · obtain ⟨y, rfl⟩ := hX.cEquiv.surjective k
      rw [PlabicData.IsNormalPlabicPregraph.tripleOfNormal_rot, tripleOfNormalEquiv_plus]
      rcases h : X.targetLabel y with _ | i
      · rw [hX.tripleRot_plus_cEquiv_of_none h, tripleOfNormalEquiv_minus, psiFun_of_none h,
          hX.inv_inv_apply, Equiv.apply_symm_apply]
      · rw [hX.tripleRot_plus_cEquiv_of_some h, tripleOfNormalEquiv_del', psiFun_of_some h,
          hX.inv_inv_apply, (hX.rot_cycle_extDart _).2.2.2]
    · obtain ⟨y, rfl⟩ := hX.cEquiv.surjective k
      rw [PlabicData.IsNormalPlabicPregraph.tripleOfNormal_rot, tripleOfNormalEquiv_minus]
      rcases h : X.targetLabel y with _ | i
      · rw [hX.tripleRot_minus_cEquiv_of_none h, tripleOfNormalEquiv_plus,
          psiFun_of_none (hX.rot_rot_mem y.2 h).2, hX.inv_inv_apply]
        simp
      · rw [hX.tripleRot_minus_cEquiv_of_some h, tripleOfNormalEquiv_del',
          ← endDart_of_targetLabel_eq_some h, (hX.rot_cycle_extDart _).2.2.2]
    · rw [PlabicData.IsNormalPlabicPregraph.tripleOfNormal_rot,
        PlabicData.IsNormalPlabicPregraph.tripleRot_del, tripleOfNormalEquiv_endDart,
        tripleOfNormalEquiv_del, (hX.rot_cycle_extDart r).2.2.1]
    · rw [PlabicData.IsNormalPlabicPregraph.tripleOfNormal_rot,
        PlabicData.IsNormalPlabicPregraph.tripleRot_del', tripleOfNormalEquiv_del,
        tripleOfNormalEquiv_del']
      have := (hX.rot_cycle_extDart ((finRotate _).symm r)).2.1
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
  mem_bdry_iff := by
    rintro (k | k | r | r)
    · obtain ⟨y, rfl⟩ := hX.cEquiv.surjective k
      rw [tripleOfNormalEquiv_plus, PlabicData.IsNormalPlabicPregraph.mem_tripleOfNormal_bdry]
      simpa using hX.inv_notMem_bdry (mem_inDarts.1 (hX.psiFun_mem y.2)).1
    · obtain ⟨y, rfl⟩ := hX.cEquiv.surjective k
      rw [tripleOfNormalEquiv_minus, PlabicData.IsNormalPlabicPregraph.mem_tripleOfNormal_bdry]
      simpa using (mem_inDarts.1 y.2).1
    · rw [tripleOfNormalEquiv_del, PlabicData.IsNormalPlabicPregraph.mem_tripleOfNormal_bdry]
      simpa using hX.extDart_mem_bdry r
    · rw [tripleOfNormalEquiv_del', PlabicData.IsNormalPlabicPregraph.mem_tripleOfNormal_bdry]
      simpa using hX.inv_mem_bdry _ (hX.extDart_mem_bdry r)
  map_isOut := by
    rintro (k | k | r | r) hz
    · obtain ⟨y, rfl⟩ := hX.cEquiv.surjective k
      rw [tripleOfNormalEquiv_plus, hX.isOut_inv_apply (mem_inDarts.1 (hX.psiFun_mem y.2)).1,
        (mem_inDarts.1 (hX.psiFun_mem y.2)).2]
      rfl
    · obtain ⟨y, rfl⟩ := hX.cEquiv.surjective k
      rw [tripleOfNormalEquiv_minus, (mem_inDarts.1 y.2).2]
      rfl
    · simp at hz
    · simp at hz
  map_endpoint r := by
    rw [TripleData.endpoint, PlabicData.IsNormalPlabicPregraph.tripleOfNormal_endDart,
      PlabicData.IsNormalPlabicPregraph.vertexOf_tripleOfNormal_endDart,
      PlabicData.IsNormalPlabicPregraph.vertexOf_tripleOfNormal_del, (hX.rot_cycle_extDart r).1]
    simp only [map_insert, map_singleton, Equiv.coe_toEmbedding, tripleOfNormalEquiv_del,
      tripleOfNormalEquiv_endDart, tripleOfNormalEquiv_del']
    ext z
    simp only [mem_insert, mem_singleton]
    tauto

/-- The isomorphism `X(G(X)) → X` sends `x⁻_{c_y}` to `y`. -/
@[simp, cluster_algebras "lem_normal_triple_inverse_right"]
theorem tripleOfNormalIso_apply_minus (y : X.InDart) :
    hX.tripleOfNormalIso.toEquiv (.minus (hX.cEquiv y)) = y :=
  hX.tripleOfNormalEquiv_minus y

/-- The isomorphism `X(G(X)) → X` sends `x⁺_{c_y}` to `\overline{ψ(y)}`. -/
@[simp, cluster_algebras "lem_normal_triple_inverse_right"]
theorem tripleOfNormalIso_apply_plus (y : X.InDart) :
    hX.tripleOfNormalIso.toEquiv (.plus (hX.cEquiv y)) = X.inv (X.psiFun y) :=
  hX.tripleOfNormalEquiv_plus y

/-- The isomorphism `X(G(X)) → X` sends `∂_r` to `p_r`. -/
@[simp, cluster_algebras "lem_normal_triple_inverse_right"]
theorem tripleOfNormalIso_apply_del (r : Fin (2 * b)) :
    hX.tripleOfNormalIso.toEquiv (.del r) = hX.extDart r := rfl

/-- The isomorphism `X(G(X)) → X` sends `∂'_r` to `p̄_r`. -/
@[simp, cluster_algebras "lem_normal_triple_inverse_right"]
theorem tripleOfNormalIso_apply_del' (r : Fin (2 * b)) :
    hX.tripleOfNormalIso.toEquiv (.del' r) = X.inv (hX.extDart r) := rfl

end IsPreTripleDiagram

/-! ### `G(X)` is a normal plabic graph -/

private theorem pow_apply_of_semiconj' {α β : Type*} (θ : α ≃ β) {f : Equiv.Perm α}
    {g : Equiv.Perm β} (h : ∀ x, θ (f x) = g (θ x)) (n : ℕ) (x : α) :
    θ ((f ^ n) x) = (g ^ n) (θ x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, h, ih, pow_succ', Equiv.Perm.mul_apply]

private theorem sameCycle_map' {α β : Type*} [Finite α] (θ : α ≃ β) {f : Equiv.Perm α}
    {g : Equiv.Perm β} (h : ∀ x, θ (f x) = g (θ x)) {x y : α} (hxy : f.SameCycle x y) :
    g.SameCycle (θ x) (θ y) := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  exact ⟨n, by rw [zpow_natCast, ← pow_apply_of_semiconj' θ h]⟩

private theorem map_filter_sameCycle {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (θ : α ≃ β) {f : Equiv.Perm α} {g : Equiv.Perm β}
    (h : ∀ x, θ (f x) = g (θ x)) (x : α) (z : β) :
    θ.symm z ∈ ({y | f.SameCycle x y} : Finset α) ↔ z ∈ ({y | g.SameCycle (θ x) y} : Finset β) := by
  have h' : ∀ y, θ.symm (g y) = f (θ.symm y) := fun y => by
    apply θ.injective
    rw [Equiv.apply_symm_apply, h, Equiv.apply_symm_apply]
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hz
    simpa using sameCycle_map' θ h hz
  · intro hz
    simpa using sameCycle_map' θ.symm h' hz

private theorem card_image_univ_of_map {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (θ : α ≃ β) (F : α → Finset α) (G : β → Finset β)
    (h : ∀ a, (F a).map θ.toEmbedding = G (θ a)) :
    (univ.image G).card = (univ.image F).card := by
  have : univ.image G = (univ.image F).map ⟨fun s => s.map θ.toEmbedding, map_injective _⟩ := by
    ext s
    simp only [mem_image, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨F (θ.symm y), ⟨_, rfl⟩, by rw [h, Equiv.apply_symm_apply]⟩
    · rintro ⟨s, ⟨a, rfl⟩, rfl⟩
      exact ⟨θ a, (h a).symm⟩
  rw [this, card_map]

/-- A pre-triple diagram isomorphic to a triple diagram is a triple diagram. -/
private theorem isTripleDiagram_of_iso {H' : Type} [Fintype H'] [DecidableEq H']
    {Y : TripleData H b} {X' : TripleData H' b} (θ : Y.Iso X') (hY : Y.IsPreTripleDiagram)
    (hX' : X'.IsTripleDiagram) : Y.IsTripleDiagram := by
  have hv : ∀ d, (Y.vertexOf d).map θ.toEquiv.toEmbedding = X'.vertexOf (θ.toEquiv d) := by
    intro d
    ext z
    rw [mem_map_equiv]
    exact map_filter_sameCycle θ.toEquiv θ.map_rot d z
  have hf : ∀ d, (Y.faceOf d).map θ.toEquiv.toEmbedding = X'.faceOf (θ.toEquiv d) := by
    intro d
    ext z
    rw [mem_map_equiv]
    exact map_filter_sameCycle θ.toEquiv θ.map_facePerm d z
  have he : ∀ d, (Y.edgeOf d).map θ.toEquiv.toEmbedding = X'.edgeOf (θ.toEquiv d) := by
    intro d
    simp [RotationSystem.edgeOf, θ.map_inv]
  refine hY.isTripleDiagram (fun d e => ?_) ?_
  · refine (RotationSystem.reach_iff_exists_mem_closure _).1 ?_
    have key : ∀ a c, X'.Reach a c → Y.Reach (θ.toEquiv.symm a) (θ.toEquiv.symm c) := by
      intro a c h
      induction h with
      | refl => exact .refl _
      | rot _ ih =>
        rw [θ.symm_map_rot]
        exact ih.rot
      | inv _ ih =>
        rw [θ.symm_map_inv]
        exact ih.inv
    simpa using key _ _ (hX'.toIsDiskMap.toIsConnected.reach (θ.toEquiv d) (θ.toEquiv e))
  · have h1 : Y.vertices.card = X'.vertices.card :=
      (card_image_univ_of_map θ.toEquiv _ _ hv).symm
    have h2 : Y.edges.card = X'.edges.card := (card_image_univ_of_map θ.toEquiv _ _ he).symm
    have h3 : Y.faceOrbits.card = X'.faceOrbits.card :=
      (card_image_univ_of_map θ.toEquiv _ _ hf).symm
    rw [h1, h2, h3]
    exact hX'.euler

/-- **`G(X)` is a normal plabic graph**: if `X` is a triple diagram, then `G(X)` is a normal
plabic graph. -/
@[cluster_algebras "lem_normal_of_triple"]
theorem IsTripleDiagram.isNormalPlabicGraph_normalOfTriple (hX : X.IsTripleDiagram) :
    (X.normalOfTriple hX.toIsPreTripleDiagram).IsNormalPlabicGraph := by
  have hP := hX.toIsPreTripleDiagram
  have hG := hP.isNormalPlabicPregraph_normalOfTriple
  exact hG.isNormalPlabicGraph_of_isTripleDiagram
    (isTripleDiagram_of_iso hP.tripleOfNormalIso hG.isPreTripleDiagram_tripleOfNormal hX)

/-! ### `G(X)` depends on `X` only up to isomorphism -/

namespace Iso

variable {H' : Type} [Fintype H'] [DecidableEq H'] {X' : TripleData H' b}

private theorem map_rot_symm' (θ : X.Iso X') (d : H) :
    θ.toEquiv (X.rot.symm d) = X'.rot.symm (θ.toEquiv d) := by
  rw [Equiv.eq_symm_apply, ← θ.map_rot, Equiv.apply_symm_apply]

private theorem map_endDart' (θ : X.Iso X') (hX : X.IsPreTripleDiagram)
    (hX' : X'.IsPreTripleDiagram) (r : Fin (2 * b)) : θ.toEquiv (X.endDart r) = X'.endDart r := by
  have hmem : θ.toEquiv (X.endDart r) ∈ X'.endpoint r := by
    rw [← θ.map_endpoint r, mem_map_equiv, Equiv.symm_apply_apply]
    exact X.self_mem_vertexOf _
  exact hX'.eq_endDart_of_mem_endpoint hmem (by rw [θ.mem_bdry_iff]; exact hX.endDart_notMem_bdry r)

/-- An isomorphism of triple data maps `I` onto `I'`. -/
theorem mem_inDarts_iff (θ : X.Iso X') (y : H) : θ.toEquiv y ∈ X'.inDarts ↔ y ∈ X.inDarts := by
  rw [mem_inDarts, mem_inDarts, θ.mem_bdry_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [θ.map_isOut y h1] at h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [θ.map_isOut y h1]; exact h2⟩

/-- The bijection `I ≃ I'` of in-darts induced by an isomorphism. -/
def inDartEquiv (θ : X.Iso X') : X.InDart ≃ X'.InDart :=
  θ.toEquiv.subtypeEquiv fun y => (θ.mem_inDarts_iff y).symm

/-- The bijection `inDartEquiv θ` is the restriction of `θ`. -/
@[simp]
theorem coe_inDartEquiv (θ : X.Iso X') (y : X.InDart) : (θ.inDartEquiv y : H') = θ.toEquiv y :=
  rfl

/-- An isomorphism of pre-triple diagrams preserves target labels. -/
theorem targetLabel_toEquiv_apply (θ : X.Iso X') (hX : X.IsPreTripleDiagram)
    (hX' : X'.IsPreTripleDiagram) (y : H) : X'.targetLabel (θ.toEquiv y) = X.targetLabel y := by
  have key : ∀ i, (X'.endDart (targetIndex i) = θ.toEquiv y) ↔ (X.endDart (targetIndex i) = y) := by
    intro i
    rw [← θ.map_endDart' hX hX', θ.toEquiv.apply_eq_iff_eq]
  simp only [targetLabel, key]

/-- An isomorphism of pre-triple diagrams intertwines the maps `ψ`. -/
theorem map_psiFun (θ : X.Iso X') (hX : X.IsPreTripleDiagram) (hX' : X'.IsPreTripleDiagram)
    (y : H) : θ.toEquiv (X.psiFun y) = X'.psiFun (θ.toEquiv y) := by
  rcases h : X.targetLabel y with _ | i
  · rw [psiFun_of_none h, psiFun_of_none ((θ.targetLabel_toEquiv_apply hX hX' y).trans h),
      θ.map_inv, θ.map_rot_symm']
  · rw [psiFun_of_some h, psiFun_of_some ((θ.targetLabel_toEquiv_apply hX hX' y).trans h),
      θ.map_inv, θ.map_endDart' hX hX']

/-- **`G(X)` depends on `X` only up to isomorphism**: an isomorphism `θ : X → X'` of
(pre-)triple diagrams induces the isomorphism `G(X) → G(X')`, `c_y ↦ c_{θ y}`,
`c*_y ↦ c*_{θ y}`, `h_i ↦ h_i`, `h*_i ↦ h*_i` (`Iso.normalOfTriple_apply_c`,
`Iso.normalOfTriple_apply_cStar`, `Iso.normalOfTriple_apply_h`, `Iso.normalOfTriple_apply_hStar`).
For triple diagrams both are normal plabic graphs
(`IsTripleDiagram.isNormalPlabicGraph_normalOfTriple`). -/
@[cluster_algebras "lem_normal_of_triple_isomorphism"]
def normalOfTriple (θ : X.Iso X') (hX : X.IsPreTripleDiagram) (hX' : X'.IsPreTripleDiagram) :
    (X.normalOfTriple hX).Iso (X'.normalOfTriple hX') where
  toEquiv := NormalOfTripleDart.mapEquiv θ.inDartEquiv
  map_inv := by rintro (_ | _ | _ | _) <;> rfl
  map_rot := by
    rintro (y | y | i | i)
    · change NormalOfTripleDart.c _ = NormalOfTripleDart.c _
      congr 1
      exact Subtype.ext (θ.map_psiFun hX hX' y)
    · have hy := θ.targetLabel_toEquiv_apply hX hX' y
      rcases h : X.targetLabel y with _ | i
      · rw [IsPreTripleDiagram.normalOfTriple_rot, hX.normalRot_cStar_of_none h,
          NormalOfTripleDart.mapEquiv_cStar, NormalOfTripleDart.mapEquiv_cStar,
          IsPreTripleDiagram.normalOfTriple_rot, hX'.normalRot_cStar_of_none (hy.trans h)]
        congr 1
        apply Subtype.ext
        simp [θ.map_rot]
      · rw [IsPreTripleDiagram.normalOfTriple_rot, hX.normalRot_cStar_of_some h,
          NormalOfTripleDart.mapEquiv_cStar, IsPreTripleDiagram.normalOfTriple_rot,
          hX'.normalRot_cStar_of_some (hy.trans h)]
        rfl
    · change NormalOfTripleDart.cStar _ = NormalOfTripleDart.cStar _
      congr 1
      exact Subtype.ext (θ.map_endDart' hX hX' _)
    · rfl
  mem_bdry_iff := by rintro (_ | _ | _ | _) <;> simp
  map_colour := by rintro (_ | _ | _ | _) _ <;> rfl
  map_bvertex i := by
    rw [hX.filter_bvertex_normalOfTriple, hX'.filter_bvertex_normalOfTriple, map_singleton,
      Equiv.coe_toEmbedding, NormalOfTripleDart.mapEquiv_cStar]
    congr 2
    exact Subtype.ext (θ.map_endDart' hX hX' _)

/-- The isomorphism `G(X) → G(X')` induced by `θ` sends `c_y` to `c_{θ y}`. -/
@[simp, cluster_algebras "lem_normal_of_triple_isomorphism"]
theorem normalOfTriple_apply_c (θ : X.Iso X') (hX : X.IsPreTripleDiagram)
    (hX' : X'.IsPreTripleDiagram) (y : X.InDart) :
    (θ.normalOfTriple hX hX').toEquiv (.c y) = .c (θ.inDartEquiv y) := rfl

/-- The isomorphism `G(X) → G(X')` induced by `θ` sends `c*_y` to `c*_{θ y}`. -/
@[simp, cluster_algebras "lem_normal_of_triple_isomorphism"]
theorem normalOfTriple_apply_cStar (θ : X.Iso X') (hX : X.IsPreTripleDiagram)
    (hX' : X'.IsPreTripleDiagram) (y : X.InDart) :
    (θ.normalOfTriple hX hX').toEquiv (.cStar y) = .cStar (θ.inDartEquiv y) := rfl

/-- The isomorphism `G(X) → G(X')` induced by `θ` fixes `h_i`. -/
@[simp, cluster_algebras "lem_normal_of_triple_isomorphism"]
theorem normalOfTriple_apply_h (θ : X.Iso X') (hX : X.IsPreTripleDiagram)
    (hX' : X'.IsPreTripleDiagram) (i : Fin b) :
    (θ.normalOfTriple hX hX').toEquiv (.h i) = .h i := rfl

/-- The isomorphism `G(X) → G(X')` induced by `θ` fixes `h*_i`. -/
@[simp, cluster_algebras "lem_normal_of_triple_isomorphism"]
theorem normalOfTriple_apply_hStar (θ : X.Iso X') (hX : X.IsPreTripleDiagram)
    (hX' : X'.IsPreTripleDiagram) (i : Fin b) :
    (θ.normalOfTriple hX hX').toEquiv (.hStar i) = .hStar i := rfl

end Iso

end TripleData

/-! ### `G(X(G))` is isomorphic to `G` -/

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

namespace IsNormalPlabicPregraph

variable (hP : G.IsNormalPlabicPregraph)

/-- The dart `x⁻_k` of `X(G)` is an in-dart outside `B`. -/
theorem minus_mem_inDarts (k : G.BlackDart) :
    (.minus k : G.TripleDart) ∈ (G.tripleOfNormal hP).inDarts :=
  TripleData.mem_inDarts.2 ⟨by simp, rfl⟩

/-- The in-darts of `X(G)` outside `B` are the darts `x⁻_k`. -/
theorem exists_minus_of_mem_inDarts {z : G.TripleDart}
    (hz : z ∈ (G.tripleOfNormal hP).inDarts) : ∃ k, z = .minus k := by
  rcases z with k | k | r | r
  · simp [TripleData.mem_inDarts] at hz
  · exact ⟨k, rfl⟩
  · simp [TripleData.mem_inDarts] at hz
  · simp [TripleData.mem_inDarts] at hz

/-- The dart `k` of an in-dart `x⁻_k` of `X(G)`. -/
def blackOfIn : (G.tripleOfNormal hP).InDart → G.BlackDart
  | ⟨.plus k, _⟩ => k
  | ⟨.minus k, _⟩ => k
  | ⟨.del r, _⟩ => hP.invLeg (halfIndex r)
  | ⟨.del' r, _⟩ => hP.invLeg (halfIndex r)

/-- The bijection `k ↦ x⁻_k` from the darts at black vertices of `G` onto the in-darts of `X(G)`
outside `B`. -/
def minusEquiv : G.BlackDart ≃ (G.tripleOfNormal hP).InDart where
  toFun k := ⟨.minus k, hP.minus_mem_inDarts k⟩
  invFun := hP.blackOfIn
  left_inv _ := rfl
  right_inv := by
    rintro ⟨z, hz⟩
    obtain ⟨k, rfl⟩ := hP.exists_minus_of_mem_inDarts hz
    rfl

/-- The underlying dart of `minusEquiv k` is `x⁻_k`. -/
@[simp]
theorem coe_minusEquiv (k : G.BlackDart) : (hP.minusEquiv k : G.TripleDart) = .minus k := rfl

/-- The target label of `x⁻_k` in `X(G)` is the index of the leg whose reverse is `k`. -/
theorem targetLabel_minus (k : G.BlackDart) :
    (G.tripleOfNormal hP).targetLabel (.minus k) = G.legIndex k := by
  simp only [TripleData.targetLabel, PlabicData.legIndex, tripleOfNormal_endDart,
    endDart_targetIndex, TripleOfNormalDart.minus.injEq, Subtype.ext_iff]
  rfl

/-- The map `ψ` of `X(G)` sends `x⁻_k` to `x⁻_{σ(k)}`. -/
theorem psiFun_minus (k : G.BlackDart) :
    (G.tripleOfNormal hP).psiFun (.minus k) = .minus ⟨G.rot k, hP.rot_mem_blackDarts k.2⟩ := by
  rcases h : G.legIndex k with _ | i
  · rw [TripleData.psiFun_of_none ((hP.targetLabel_minus k).trans h)]
    have : (G.tripleOfNormal hP).rot.symm (.minus k) = .plus k := by
      rw [Equiv.symm_apply_eq, tripleOfNormal_rot, hP.tripleRot_plus_of_none h]
    rw [this]
    rfl
  · rw [TripleData.psiFun_of_some ((hP.targetLabel_minus k).trans h), tripleOfNormal_endDart,
      endDart_sourceIndex, tripleOfNormal_inv, tripleInv_plus]
    congr 1
    exact Subtype.ext (congrArg G.rot (inv_leg_of_legIndex_eq_some h))

/-- If `k` is not the reverse of a leg, the rotation of `X(G)` applied twice sends `x⁻_k` to
`x⁻_{ψ(k)}`, where `ψ(k) = \overline{σ(k̄)}`. -/
theorem rot_rot_minus_of_none {k : G.BlackDart} (h : G.legIndex k = none) :
    (G.tripleOfNormal hP).rot ((G.tripleOfNormal hP).rot (.minus k)) = .minus (hP.psi k h) := by
  rw [tripleOfNormal_rot, hP.tripleRot_minus_of_none h,
    hP.tripleRot_plus_of_none (hP.legIndex_psi k h)]

/-- The permutation `ψ` of `X(G)` sends `x⁻_k` to `x⁻_{σ(k)}`. -/
theorem psi_minusEquiv (k : G.BlackDart) :
    hP.isPreTripleDiagram_tripleOfNormal.psi (hP.minusEquiv k) =
      hP.minusEquiv ⟨G.rot k, hP.rot_mem_blackDarts k.2⟩ :=
  Subtype.ext (hP.psiFun_minus k)

/-- If `k` is not the reverse of a leg, the rotation of `G(X(G))` sends `c*_{x⁻_k}` to
`c*_{x⁻_{ψ(k)}}`, where `ψ(k) = \overline{σ(k̄)}`. -/
theorem normalRot_cStar_minusEquiv_of_none {k : G.BlackDart} (h : G.legIndex k = none) :
    hP.isPreTripleDiagram_tripleOfNormal.normalRot (.cStar (hP.minusEquiv k)) =
      .cStar (hP.minusEquiv (hP.psi k h)) := by
  rw [hP.isPreTripleDiagram_tripleOfNormal.normalRot_cStar_of_none
    ((hP.targetLabel_minus k).trans h)]
  congr 1
  exact Subtype.ext (hP.rot_rot_minus_of_none h)

/-- If `k` is the reverse of the leg at `i`, the rotation of `G(X(G))` sends `c*_{x⁻_k}` to
`h*_{i+1}`. -/
theorem normalRot_cStar_minusEquiv_of_some {k : G.BlackDart} {i : Fin b}
    (h : G.legIndex k = some i) :
    hP.isPreTripleDiagram_tripleOfNormal.normalRot (.cStar (hP.minusEquiv k)) =
      .hStar (finRotate b i) :=
  hP.isPreTripleDiagram_tripleOfNormal.normalRot_cStar_of_some ((hP.targetLabel_minus k).trans h)

/-- The dart of the target `t_i` of `X(G)` outside `B` is `x⁻_k` for `k` the reverse of the leg
at `i`. -/
theorem targetDart_tripleOfNormal (i : Fin b) :
    hP.isPreTripleDiagram_tripleOfNormal.targetDart i = hP.minusEquiv (hP.invLeg i) :=
  Subtype.ext (hP.endDart_targetIndex i)

/-- The vertex of `x⁺_k`, for `k` not the reverse of a leg, is a triple point. -/
theorem not_isBoundaryVertex_tripleOfNormal_plus {k : G.BlackDart} (h : G.legIndex k = none) :
    ¬(G.tripleOfNormal hP).IsBoundaryVertex ((G.tripleOfNormal hP).vertexOf (.plus k)) := by
  rw [hP.vertexOf_tripleOfNormal_plus_of_none h]
  rintro ⟨e, he, heB⟩
  simp only [mem_insert, mem_singleton] at he
  rw [mem_tripleOfNormal_bdry] at heB
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at heB

/-- The vertex of `x⁻_k`, for `k` not the reverse of a leg, is a triple point. -/
theorem not_isBoundaryVertex_tripleOfNormal_minus {k : G.BlackDart} (h : G.legIndex k = none) :
    ¬(G.tripleOfNormal hP).IsBoundaryVertex ((G.tripleOfNormal hP).vertexOf (.minus k)) := by
  have : (G.tripleOfNormal hP).vertexOf (.minus k) = (G.tripleOfNormal hP).vertexOf (.plus k) := by
    rw [← RotationSystem.vertexOf_rot _ (TripleOfNormalDart.plus k), tripleOfNormal_rot,
      hP.tripleRot_plus_of_none h]
  rw [this]
  exact hP.not_isBoundaryVertex_tripleOfNormal_plus h

/-- `x⁺_k` runs to an endpoint exactly when `σ(k)` is the reverse of a leg. -/
theorem runsToEndpoint_plus_iff (k : G.BlackDart) :
    (G.tripleOfNormal hP).RunsToEndpoint (.plus k) ↔ G.legIndex (G.rot k) ≠ none := by
  unfold TripleData.RunsToEndpoint
  rw [tripleOfNormal_inv, tripleInv_plus]
  rcases h : G.legIndex (G.rot k) with _ | i
  · exact iff_of_false (hP.not_isBoundaryVertex_tripleOfNormal_minus (k := ⟨_, _⟩) h)
      (fun h' => h' rfl)
  · exact iff_of_true (hP.isBoundaryVertex_tripleOfNormal_minus_of_some (k := ⟨_, _⟩) h)
      (Option.some_ne_none i)

/-- `x⁻_k` runs to an endpoint exactly when `σ⁻¹(k)` is the reverse of a leg. -/
theorem runsToEndpoint_minus_iff (k : G.BlackDart) :
    (G.tripleOfNormal hP).RunsToEndpoint (.minus k) ↔ G.legIndex (G.rot.symm k) ≠ none := by
  unfold TripleData.RunsToEndpoint
  rw [tripleOfNormal_inv, tripleInv_minus]
  rcases h : G.legIndex (G.rot.symm k) with _ | i
  · exact iff_of_false (hP.not_isBoundaryVertex_tripleOfNormal_plus (k := ⟨_, _⟩) h)
      (fun h' => h' rfl)
  · exact iff_of_true (hP.isBoundaryVertex_tripleOfNormal_plus_of_some (k := ⟨_, _⟩) h)
      (Option.some_ne_none i)

end IsNormalPlabicPregraph

namespace IsNormalPlabicGraph

variable (hG : G.IsNormalPlabicGraph)

/-- The dart `h_i` of the exterior at the boundary vertex `β(i)`. -/
noncomputable def extDart (i : Fin b) : H := DiskMap.exteriorDartAt hG.exists_exterior i

/-- The dart `h_i` lies in the exterior. -/
theorem extDart_mem_exterior (i : Fin b) : hG.extDart i ∈ G.exterior :=
  (DiskMap.exteriorDartAt_spec hG.exists_exterior i).1

/-- The dart `h_i` lies at the boundary vertex `β(i)`. -/
theorem extDart_mem_bvertex (i : Fin b) : hG.extDart i ∈ G.bvertex i :=
  (DiskMap.exteriorDartAt_spec hG.exists_exterior i).2.1

/-- The dart `h_i` lies in `B`. -/
theorem extDart_mem_bdry (i : Fin b) : hG.extDart i ∈ G.bdry :=
  G.exterior_subset_bdry (hG.extDart_mem_exterior i)

/-- The rotation at `β(i)` is `(h̄_{i+1}, h_i, g_i)`. -/
theorem rot_cycle_extDart (i : Fin b) :
    G.bvertex i = {G.inv (hG.extDart (finRotate b i)), hG.extDart i, G.leg i} ∧
      G.rot (G.inv (hG.extDart (finRotate b i))) = hG.extDart i ∧
      G.rot (hG.extDart i) = G.leg i ∧
      G.rot (G.leg i) = G.inv (hG.extDart (finRotate b i)) :=
  DiskMap.rot_cycle_exteriorDartAt hG.inv_involutive hG.inv_mem_bdry hG.boundaryVertex_card
    hG.exists_orbit hG.exists_exterior (hG.bvertex_mem i) (G.leg_mem_bvertex i)
    (hG.leg_notMem_bdry i)

/-- The darts `h_i` are pairwise distinct. -/
theorem extDart_injective : Function.Injective hG.extDart := by
  intro i j h
  apply hG.bvertex_injective
  have hi := G.vertexOf_eq_of_mem (hG.extDart_mem_bvertex i)
  have hj := G.vertexOf_eq_of_mem (hG.extDart_mem_bvertex j)
  rw [h] at hi
  exact hi.symm.trans hj

/-- Every dart of the exterior is some `h_i`. -/
theorem exists_extDart_eq {d : H} (hd : d ∈ G.exterior) : ∃ i, hG.extDart i = d := by
  have hv := G.isBoundaryVertex_vertexOf_of_mem (G.exterior_subset_bdry hd)
  obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hv)
  refine ⟨i, DiskMap.eq_of_mem_exterior_of_mem_vertexOf hG.boundaryVertex_card hd
    (hG.extDart_mem_exterior i) ?_⟩
  rw [← hi]
  exact hG.extDart_mem_bvertex i

/-- The map `c_k ↦ k`, `c*_k ↦ k̄`, `h_i ↦ h_i`, `h*_i ↦ h̄_i` on the symbols indexed by the darts
at black vertices of `G`. -/
noncomputable def normalDartToDart : NormalOfTripleDart G.BlackDart b → H
  | .c k => k
  | .cStar k => G.inv k
  | .h i => hG.extDart i
  | .hStar i => G.inv (hG.extDart i)

/-- The kind of a symbol: `0` for `c`, `1` for `c*`, `2` for `h`, `3` for `h*`. -/
private def normalSymbolKind {K : Type*} {n : ℕ} : NormalOfTripleDart K n → ℕ
  | .c _ => 0
  | .cStar _ => 1
  | .h _ => 2
  | .hStar _ => 3

private theorem kind_normalDartToDart (z : NormalOfTripleDart G.BlackDart b) :
    (if hG.normalDartToDart z ∈ G.exterior then 2 else if hG.normalDartToDart z ∈ G.bdry then 3
      else if hG.normalDartToDart z ∈ G.blackDarts then 0 else 1) = normalSymbolKind z := by
  rcases z with k | k | i | i
  · have hB := notMem_bdry_of_mem_blackDarts k.2
    simp only [normalDartToDart, normalSymbolKind]
    rw [if_neg (fun h => hB (G.exterior_subset_bdry h)), if_neg hB, if_pos k.2]
  · have hB : G.inv (k : H) ∉ G.bdry := fun h =>
      notMem_bdry_of_mem_blackDarts k.2 (hG.inv_mem_bdry_iff.1 h)
    have hK : G.inv (k : H) ∉ G.blackDarts := by
      intro h
      have := hG.colour_inv_ne k (mem_blackDarts.1 k.2).1 (mem_blackDarts.1 h).1
      rw [(mem_blackDarts.1 h).2, (mem_blackDarts.1 k.2).2] at this
      exact this rfl
    simp only [normalDartToDart, normalSymbolKind]
    rw [if_neg (fun h => hB (G.exterior_subset_bdry h)), if_neg hB, if_neg hK]
  · simp only [normalDartToDart, normalSymbolKind]
    rw [if_pos (hG.extDart_mem_exterior i)]
  · have hne : G.inv (hG.extDart i) ∉ G.exterior := by
      intro h
      refine disjoint_left.1 hG.disjoint_exterior_map_inv (hG.extDart_mem_exterior i)
        (mem_map_equiv.2 ?_)
      rwa [show G.inv.symm (hG.extDart i) = G.inv (hG.extDart i) by
        rw [Equiv.symm_apply_eq, hG.inv_involutive]]
    simp only [normalDartToDart, normalSymbolKind]
    rw [if_neg hne, if_pos (hG.inv_mem_bdry _ (hG.extDart_mem_bdry i))]

/-- The map `normalDartToDart` is injective. -/
theorem normalDartToDart_injective : Function.Injective hG.normalDartToDart := by
  intro z₁ z₂ h
  have hk := hG.kind_normalDartToDart z₁
  rw [h, hG.kind_normalDartToDart z₂] at hk
  rcases z₁ with k₁ | k₁ | i₁ | i₁ <;> rcases z₂ with k₂ | k₂ | i₂ | i₂ <;>
    simp only [normalSymbolKind] at hk <;> (try omega) <;> simp only [normalDartToDart] at h
  · rw [Subtype.ext h]
  · rw [Subtype.ext (G.inv.injective h)]
  · rw [hG.extDart_injective h]
  · rw [hG.extDart_injective (G.inv.injective h)]

/-- The map `normalDartToDart` is surjective. -/
theorem normalDartToDart_surjective : Function.Surjective hG.normalDartToDart := by
  intro d
  by_cases hdB : d ∈ G.bdry
  · by_cases hde : d ∈ G.exterior
    · obtain ⟨i, rfl⟩ := hG.exists_extDart_eq hde
      exact ⟨.h i, rfl⟩
    · rw [← hG.exterior_union_map_inv] at hdB
      rcases mem_union.1 hdB with h | h
      · exact absurd h hde
      · rw [mem_map_equiv, show G.inv.symm d = G.inv d by
          rw [Equiv.symm_apply_eq, hG.inv_involutive]] at h
        obtain ⟨i, hi⟩ := hG.exists_extDart_eq h
        refine ⟨.hStar i, ?_⟩
        simp only [normalDartToDart]
        rw [hi, hG.inv_involutive]
  · by_cases hdK : d ∈ G.blackDarts
    · exact ⟨.c ⟨d, hdK⟩, rfl⟩
    · have hiK : G.inv d ∈ G.blackDarts := by
        by_cases hv : G.IsBoundaryVertex (G.vertexOf d)
        · obtain ⟨i, rfl⟩ := hG.isNormalPlabicPregraph.exists_leg_eq hv hdB
          exact hG.isNormalPlabicPregraph.inv_leg_mem_blackDarts i
        · have hc : G.colour d = .white := by
            cases hc : G.colour d
            · rfl
            · exact absurd (mem_blackDarts.2 ⟨hv, hc⟩) hdK
          exact mem_blackDarts.2 (hG.inv_internal_black_of_white hv hc)
      refine ⟨.cStar ⟨G.inv d, hiK⟩, ?_⟩
      simp only [normalDartToDart]
      rw [hG.inv_involutive]

/-- The map `normalDartToDart` is a bijection. -/
theorem normalDartToDart_bijective : Function.Bijective hG.normalDartToDart :=
  ⟨hG.normalDartToDart_injective, hG.normalDartToDart_surjective⟩

/-- The bijection from the darts of `G(X(G))` to the darts of `G`:
`c_{x⁻_k} ↦ k`, `c*_{x⁻_k} ↦ k̄`, `h_i ↦ h_i`, `h*_i ↦ h̄_i`. -/
noncomputable def normalOfTripleEquiv :
    (G.tripleOfNormal hG.isNormalPlabicPregraph).NormalDart ≃ H :=
  (NormalOfTripleDart.mapEquiv hG.isNormalPlabicPregraph.minusEquiv.symm).trans
    (Equiv.ofBijective _ hG.normalDartToDart_bijective)

/-- The bijection `G(X(G)) → G` sends `c_{x⁻_k}` to `k`. -/
@[simp]
theorem normalOfTripleEquiv_c (k : G.BlackDart) :
    hG.normalOfTripleEquiv (.c (hG.isNormalPlabicPregraph.minusEquiv k)) = k := by
  simp [normalOfTripleEquiv, normalDartToDart]

/-- The bijection `G(X(G)) → G` sends `c*_{x⁻_k}` to `k̄`. -/
@[simp]
theorem normalOfTripleEquiv_cStar (k : G.BlackDart) :
    hG.normalOfTripleEquiv (.cStar (hG.isNormalPlabicPregraph.minusEquiv k)) = G.inv k := by
  simp [normalOfTripleEquiv, normalDartToDart]

/-- The bijection `G(X(G)) → G` sends the symbol `h_i` to the dart `h_i` of `G`. -/
@[simp]
theorem normalOfTripleEquiv_h (i : Fin b) : hG.normalOfTripleEquiv (.h i) = hG.extDart i := rfl

/-- The bijection `G(X(G)) → G` sends the symbol `h*_i` to `h̄_i`. -/
@[simp]
theorem normalOfTripleEquiv_hStar (i : Fin b) :
    hG.normalOfTripleEquiv (.hStar i) = G.inv (hG.extDart i) := rfl

/-- The isomorphism `G(X(G)) → G` inverse to `normalOfTripleIso`. -/
noncomputable def normalOfTripleIsoSymm :
    ((G.tripleOfNormal hG.isNormalPlabicPregraph).normalOfTriple
      hG.isNormalPlabicPregraph.isPreTripleDiagram_tripleOfNormal).Iso G where
  toEquiv := hG.normalOfTripleEquiv
  map_inv := by
    have hP := hG.isNormalPlabicPregraph
    rintro (y | y | i | i)
    · obtain ⟨k, rfl⟩ := hP.minusEquiv.surjective y
      rw [TripleData.IsPreTripleDiagram.normalOfTriple_inv, NormalOfTripleDart.star_c,
        normalOfTripleEquiv_cStar, normalOfTripleEquiv_c]
    · obtain ⟨k, rfl⟩ := hP.minusEquiv.surjective y
      rw [TripleData.IsPreTripleDiagram.normalOfTriple_inv, NormalOfTripleDart.star_cStar,
        normalOfTripleEquiv_cStar, normalOfTripleEquiv_c, hG.inv_involutive]
    · rfl
    · rw [TripleData.IsPreTripleDiagram.normalOfTriple_inv, NormalOfTripleDart.star_hStar,
        normalOfTripleEquiv_hStar, normalOfTripleEquiv_h, hG.inv_involutive]
  map_rot := by
    have hP := hG.isNormalPlabicPregraph
    rintro (y | y | i | i)
    · obtain ⟨k, rfl⟩ := hP.minusEquiv.surjective y
      rw [TripleData.IsPreTripleDiagram.normalOfTriple_rot,
        TripleData.IsPreTripleDiagram.normalRot_c, hP.psi_minusEquiv, normalOfTripleEquiv_c,
        normalOfTripleEquiv_c]
    · obtain ⟨k, rfl⟩ := hP.minusEquiv.surjective y
      rw [TripleData.IsPreTripleDiagram.normalOfTriple_rot, normalOfTripleEquiv_cStar]
      rcases h : G.legIndex k with _ | i
      · rw [hP.normalRot_cStar_minusEquiv_of_none h, normalOfTripleEquiv_cStar,
          IsNormalPlabicPregraph.coe_psi, hG.inv_involutive]
      · rw [hP.normalRot_cStar_minusEquiv_of_some h, normalOfTripleEquiv_hStar,
          ← inv_leg_of_legIndex_eq_some h, hG.inv_involutive, (hG.rot_cycle_extDart i).2.2.2]
    · rw [TripleData.IsPreTripleDiagram.normalOfTriple_rot,
        TripleData.IsPreTripleDiagram.normalRot_h, hP.targetDart_tripleOfNormal,
        normalOfTripleEquiv_cStar, normalOfTripleEquiv_h, (hG.rot_cycle_extDart i).2.2.1]
      exact hG.inv_involutive _
    · rw [TripleData.IsPreTripleDiagram.normalOfTriple_rot,
        TripleData.IsPreTripleDiagram.normalRot_hStar, normalOfTripleEquiv_h,
        normalOfTripleEquiv_hStar]
      have := (hG.rot_cycle_extDart ((finRotate b).symm i)).2.1
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
  mem_bdry_iff := by
    have hP := hG.isNormalPlabicPregraph
    rintro (y | y | i | i)
    · obtain ⟨k, rfl⟩ := hP.minusEquiv.surjective y
      rw [normalOfTripleEquiv_c, TripleData.IsPreTripleDiagram.mem_normalOfTriple_bdry]
      simpa using notMem_bdry_of_mem_blackDarts k.2
    · obtain ⟨k, rfl⟩ := hP.minusEquiv.surjective y
      rw [normalOfTripleEquiv_cStar, TripleData.IsPreTripleDiagram.mem_normalOfTriple_bdry,
        hG.inv_mem_bdry_iff]
      simpa using notMem_bdry_of_mem_blackDarts k.2
    · rw [normalOfTripleEquiv_h, TripleData.IsPreTripleDiagram.mem_normalOfTriple_bdry]
      simpa using hG.extDart_mem_bdry i
    · rw [normalOfTripleEquiv_hStar, TripleData.IsPreTripleDiagram.mem_normalOfTriple_bdry]
      simpa using hG.inv_mem_bdry _ (hG.extDart_mem_bdry i)
  map_colour d hd := by
    have hP := hG.isNormalPlabicPregraph
    rcases hP.isPreTripleDiagram_tripleOfNormal.internal_cases_normalOfTriple hd with
      ⟨y, rfl⟩ | ⟨y, hy, rfl⟩
    · obtain ⟨k, rfl⟩ := hP.minusEquiv.surjective y
      rw [normalOfTripleEquiv_c, (mem_blackDarts.1 k.2).2]
      rfl
    · obtain ⟨k, rfl⟩ := hP.minusEquiv.surjective y
      rw [normalOfTripleEquiv_cStar, hP.colour_inv k.2 ((hP.targetLabel_minus k).symm.trans hy)]
      rfl
  map_bvertex i := by
    have hP := hG.isNormalPlabicPregraph
    rw [hP.isPreTripleDiagram_tripleOfNormal.filter_bvertex_normalOfTriple,
      hG.filter_bvertex_notMem_bdry, map_singleton, Equiv.coe_toEmbedding,
      hP.targetDart_tripleOfNormal, normalOfTripleEquiv_cStar]
    congr 1
    exact hG.inv_involutive _

/-- **`G(X(G))` is isomorphic to `G`**: for a normal plabic graph `G` with exterior darts `h_i`
(`IsNormalPlabicGraph.extDart`) and set `K` of darts at black vertices, the map `θ` with
`θ(k) = c_{x⁻_k}` and `θ(k̄) = c*_{x⁻_k}` for `k ∈ K`, `θ(h_i) = h_i` and `θ(h̄_i) = h*_i` is an
isomorphism of plabic graphs `G → G(X(G))`
(`normalOfTripleIso_apply_black`, `normalOfTripleIso_apply_inv_black`,
`normalOfTripleIso_apply_extDart`, `normalOfTripleIso_apply_inv_extDart`); `G(X(G))` is a normal
plabic graph (`isNormalPlabicGraph_normalOfTriple_tripleOfNormal`). -/
@[cluster_algebras "lem_normal_triple_inverse_left"]
noncomputable def normalOfTripleIso :
    G.Iso ((G.tripleOfNormal hG.isNormalPlabicPregraph).normalOfTriple
      hG.isNormalPlabicPregraph.isPreTripleDiagram_tripleOfNormal) :=
  hG.normalOfTripleIsoSymm.symm

/-- The isomorphism `G → G(X(G))` sends `k ∈ K` to `c_{x⁻_k}`. -/
@[cluster_algebras "lem_normal_triple_inverse_left"]
theorem normalOfTripleIso_apply_black (k : G.BlackDart) :
    hG.normalOfTripleIso.toEquiv k = .c (hG.isNormalPlabicPregraph.minusEquiv k) :=
  Equiv.symm_apply_eq _ |>.2 (hG.normalOfTripleEquiv_c k).symm

/-- The isomorphism `G → G(X(G))` sends `k̄` to `c*_{x⁻_k}` for `k ∈ K`. -/
@[cluster_algebras "lem_normal_triple_inverse_left"]
theorem normalOfTripleIso_apply_inv_black (k : G.BlackDart) :
    hG.normalOfTripleIso.toEquiv (G.inv k) = .cStar (hG.isNormalPlabicPregraph.minusEquiv k) :=
  Equiv.symm_apply_eq _ |>.2 (hG.normalOfTripleEquiv_cStar k).symm

/-- The isomorphism `G → G(X(G))` sends the dart `h_i` of `G` to the symbol `h_i`. -/
@[cluster_algebras "lem_normal_triple_inverse_left"]
theorem normalOfTripleIso_apply_extDart (i : Fin b) :
    hG.normalOfTripleIso.toEquiv (hG.extDart i) = .h i :=
  Equiv.symm_apply_eq _ |>.2 (hG.normalOfTripleEquiv_h i).symm

/-- The isomorphism `G → G(X(G))` sends `h̄_i` to `h*_i`. -/
@[cluster_algebras "lem_normal_triple_inverse_left"]
theorem normalOfTripleIso_apply_inv_extDart (i : Fin b) :
    hG.normalOfTripleIso.toEquiv (G.inv (hG.extDart i)) = .hStar i :=
  Equiv.symm_apply_eq _ |>.2 (hG.normalOfTripleEquiv_hStar i).symm

/-- For a normal plabic graph `G`, `G(X(G))` is a normal plabic graph. -/
@[cluster_algebras "lem_normal_triple_inverse_left"]
theorem isNormalPlabicGraph_normalOfTriple_tripleOfNormal :
    ((G.tripleOfNormal hG.isNormalPlabicPregraph).normalOfTriple
      hG.isNormalPlabicPregraph.isPreTripleDiagram_tripleOfNormal).IsNormalPlabicGraph :=
  hG.isTripleDiagram_tripleOfNormal.isNormalPlabicGraph_normalOfTriple

/-! ### Trips and strands -/

include hG in
/-- A dart at an internal vertex is not a leg. -/
theorem not_isLeg_of_internal {d : H} (hd : ¬G.IsBoundaryVertex (G.vertexOf d)) :
    ¬G.IsLeg d := by
  rintro ⟨j, rfl⟩
  exact hd (hG.isNormalPlabicPregraph.isBoundaryVertex_leg j)

include hG in
/-- A dart at a black vertex is not a leg. -/
theorem not_isLeg_of_mem_blackDarts {k : H} (hk : k ∈ G.blackDarts) : ¬G.IsLeg k :=
  hG.not_isLeg_of_internal (mem_blackDarts.1 hk).1

/-- **Strands of `X(G)` follow trips of `G`**, first part: let `T` be the trip map of `G` and `S`
the strand map of `X(G)`; for `k ∈ K` with `v(\overline{σ k})` internal, `T(σ k)` is not a leg
and `S(x⁺_k) = x⁺_{σ⁻¹(T²(σ k))}`. -/
@[cluster_algebras "lem_strand_follows_trip"]
theorem strandMap_plus_of_internal (k : G.BlackDart)
    (hk : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.rot k)))) :
    ¬G.IsLeg (G.tripMap (G.rot k)) ∧ ∃ k' : G.BlackDart,
      (k' : H) = G.rot.symm (G.tripMap (G.tripMap (G.rot k))) ∧
      (G.tripleOfNormal hG.isNormalPlabicPregraph).strandMap (.plus k) = .plus k' := by
  have hP := hG.isNormalPlabicPregraph
  have hm : G.rot (k : H) ∈ G.blackDarts := hP.rot_mem_blackDarts k.2
  have hl : G.legIndex (G.rot (k : H)) = none := hP.legIndex_eq_none_of_internal hk
  have hw : G.colour (G.inv (G.rot (k : H))) = .white := hP.colour_inv hm hl
  have hT1 : G.tripMap (G.rot k) = G.rot.symm (G.inv (G.rot k)) := by
    rw [tripMap_apply, turn_of_white hk hw]
  have ha₃ : ¬G.IsBoundaryVertex (G.vertexOf (G.rot.symm (G.inv (G.rot k)))) := by
    rwa [G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf _)]
  have hw₃ : G.colour (G.rot.symm (G.inv (G.rot k))) = .white := by
    rw [hP.colour_rot_symm hk, hw]
  obtain ⟨hb₃, hc₃⟩ := hP.inv_black_of_white ha₃ hw₃
  have hT2 : G.tripMap (G.tripMap (G.rot k)) =
      G.rot (G.inv (G.rot.symm (G.inv (G.rot k)))) := by
    rw [hT1, tripMap_apply, turn_of_black hb₃ hc₃]
  refine ⟨by rw [hT1]; exact hG.not_isLeg_of_internal ha₃, ?_⟩
  have hl' := hP.legIndex_psi ⟨_, hm⟩ hl
  refine ⟨hP.psi (hP.psi ⟨_, hm⟩ hl) hl', ?_, ?_⟩
  · rw [hT2, Equiv.symm_apply_apply]
    have h3 := congrArg Subtype.val (hP.psi_psi_psi (k := ⟨_, hm⟩) hl).1
    rw [IsNormalPlabicPregraph.coe_psi] at h3
    have h4 : G.rot (G.inv (hP.psi (hP.psi ⟨_, hm⟩ hl) hl' : H)) = G.inv (G.rot k) := by
      have := congrArg G.inv h3
      rwa [hP.inv_inv] at this
    have h5 : G.inv (hP.psi (hP.psi ⟨_, hm⟩ hl) hl' : H) = G.rot.symm (G.inv (G.rot k)) := by
      rw [← h4, Equiv.symm_apply_apply]
    rw [← h5, hP.inv_inv]
  · have hnr : ¬(G.tripleOfNormal hP).RunsToEndpoint (.plus k) := by
      rw [hP.runsToEndpoint_plus_iff]
      exact fun h => h hl
    rw [TripleData.strandMap_of_not_runsToEndpoint _ hnr, IsNormalPlabicPregraph.tripleOfNormal_inv,
      IsNormalPlabicPregraph.tripleInv_plus, IsNormalPlabicPregraph.tripleOfNormal_rot,
      hP.tripleRot_minus_of_none (k := ⟨_, hm⟩) hl, hP.tripleRot_plus_of_none hl',
      hP.tripleRot_minus_of_none hl']

/-- **Strands of `X(G)` follow trips of `G`**, second part: for `k ∈ K` with `σ k = ḡ_j`,
`T(σ k) = g_j`, and the reverse of `x⁺_k` is the dart `n_{2j}` of the target `t_j` outside
`B`. -/
@[cluster_algebras "lem_strand_follows_trip"]
theorem strandMap_plus_of_eq_inv_leg (k : G.BlackDart) {j : Fin b}
    (hkj : G.rot (k : H) = G.inv (G.leg j)) :
    G.tripMap (G.rot k) = G.leg j ∧
      (G.tripleOfNormal hG.isNormalPlabicPregraph).inv (.plus k) =
        hG.isNormalPlabicPregraph.endDart (targetIndex j) := by
  have hP := hG.isNormalPlabicPregraph
  refine ⟨?_, ?_⟩
  · rw [tripMap_apply, hkj, hP.inv_inv, turn_of_isBoundaryVertex (hP.isBoundaryVertex_leg j)]
  · rw [IsNormalPlabicPregraph.tripleOfNormal_inv, IsNormalPlabicPregraph.tripleInv_plus,
      IsNormalPlabicPregraph.endDart_targetIndex]
    congr 1
    exact Subtype.ext hkj

/-- Until the arc of `X(G)` from the `i`-th endpoint runs to an endpoint, its `j`-th dart is
`x⁺_k` with `σ k = T^{2j+1}(g_i)`, and the trip from `g_i` meets no leg before that step. -/
theorem arcDart_eq_plus_of_forall_not_runsToEndpoint (i : Fin b) (j : ℕ)
    (hlt : ∀ j' < j, ¬(G.tripleOfNormal hG.isNormalPlabicPregraph).RunsToEndpoint
      ((G.tripleOfNormal hG.isNormalPlabicPregraph).arcDart i j')) :
    ∃ k : G.BlackDart, (G.tripleOfNormal hG.isNormalPlabicPregraph).arcDart i j = .plus k ∧
      G.rot (k : H) = G.tripMap^[2 * j + 1] (G.leg i) ∧
      ∀ n, 0 < n → n ≤ 2 * j + 1 → ¬G.IsLeg (G.tripMap^[n] (G.leg i)) := by
  have hP := hG.isNormalPlabicPregraph
  induction j with
  | zero =>
    have hT : G.tripMap (G.leg i) = G.rot (G.inv (G.leg i)) := by
      rw [tripMap_apply,
        turn_of_black (hP.not_isBoundaryVertex_inv_leg i) (hP.colour_inv_leg i)]
    refine ⟨hP.invLeg i, by
      rw [TripleData.arcDart_zero, IsNormalPlabicPregraph.tripleOfNormal_endDart,
        IsNormalPlabicPregraph.endDart_sourceIndex], ?_, ?_⟩
    · rw [Function.iterate_one, hT]
      rfl
    · intro n hn hn1
      obtain rfl : n = 1 := by omega
      rw [Function.iterate_one, hT]
      exact hG.not_isLeg_of_mem_blackDarts
        (hP.rot_mem_blackDarts (hP.inv_leg_mem_blackDarts i))
  | succ j ih =>
    obtain ⟨k, hk, hrk, hnl⟩ := ih (fun j' hj' => hlt j' (by omega))
    have hnr := hlt j (by omega)
    rw [hk, hP.runsToEndpoint_plus_iff, not_not] at hnr
    have hint := hP.not_isBoundaryVertex_inv (hP.rot_mem_blackDarts k.2) hnr
    obtain ⟨hnl', k', hk', hS⟩ := hG.strandMap_plus_of_internal k hint
    have hrk' : G.rot (k' : H) = G.tripMap^[2 * (j + 1) + 1] (G.leg i) := by
      rw [hk', Equiv.apply_symm_apply, show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by ring,
        Function.iterate_succ_apply', Function.iterate_succ_apply', hrk]
    refine ⟨k', by rw [TripleData.arcDart_succ, hk, hS], hrk', fun n hn hn' => ?_⟩
    rcases Nat.lt_or_ge n (2 * j + 2) with h | h
    · exact hnl n hn (by omega)
    · rcases Nat.lt_or_ge n (2 * j + 3) with h' | h'
      · obtain rfl : n = 2 * j + 1 + 1 := by omega
        rw [Function.iterate_succ_apply', ← hrk]
        exact hnl'
      · obtain rfl : n = 2 * (j + 1) + 1 := by omega
        rw [← hrk']
        exact hG.not_isLeg_of_mem_blackDarts (hP.rot_mem_blackDarts k'.2)

/-- **Trip permutation equals strand permutation**: for a normal plabic graph `G`,
`π_G = π_{X(G)}`. -/
@[cluster_algebras "lem_trip_strand_permutation"]
theorem tripPerm_eq_strandPerm :
    G.tripPerm = (G.tripleOfNormal hG.isNormalPlabicPregraph).strandPerm := by
  have hP := hG.isNormalPlabicPregraph
  funext i
  have hex : ∃ m, (G.tripleOfNormal hP).RunsToEndpoint ((G.tripleOfNormal hP).arcDart i m) := by
    by_contra hne
    push Not at hne
    obtain ⟨n, hn, hleg⟩ := hG.toIsPlabicGraph.exists_isLeg_iterate_tripMap i
    obtain ⟨-, -, -, hnl⟩ :=
      hG.arcDart_eq_plus_of_forall_not_runsToEndpoint i n fun j' _ => hne j'
    exact hnl n hn (by omega) hleg
  classical
  have hm := Nat.find_spec hex
  have hlt : ∀ j' < Nat.find hex,
      ¬(G.tripleOfNormal hP).RunsToEndpoint ((G.tripleOfNormal hP).arcDart i j') :=
    fun _ => Nat.find_min hex
  generalize Nat.find hex = m at hm hlt
  obtain ⟨k, hk, hrk, hnl⟩ := hG.arcDart_eq_plus_of_forall_not_runsToEndpoint i m hlt
  have hm' := hm
  rw [hk, hP.runsToEndpoint_plus_iff] at hm'
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, G.legIndex (G.rot (k : H)) = some ℓ := by
    rcases h : G.legIndex (G.rot (k : H)) with _ | ℓ
    · exact absurd h hm'
    · exact ⟨ℓ, rfl⟩
  have hkℓ : G.rot (k : H) = G.inv (G.leg ℓ) := (inv_leg_of_legIndex_eq_some hℓ).symm
  obtain ⟨hT, hinv⟩ := hG.strandMap_plus_of_eq_inv_leg k hkℓ
  have hT' : G.tripMap^[2 * m + 2] (G.leg i) = G.leg ℓ := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, Function.iterate_succ_apply', ← hrk, hT]
  have hlen : G.tripLength i = 2 * m + 2 := by
    refine le_antisymm (tripLength_le (by omega) ⟨ℓ, hT'.symm⟩) ?_
    by_contra hlt'
    push Not at hlt'
    obtain ⟨hpos, hleg⟩ := tripLength_spec (hG.toIsPlabicGraph.exists_isLeg_iterate_tripMap i)
    exact hnl _ hpos (by omega) hleg
  have h1 : G.tripPerm i = ℓ := by
    rw [hG.toIsPlabicGraph.tripPerm_eq_iff, hlen, hT']
  have hlenX : (G.tripleOfNormal hP).arcLength i = m + 1 :=
    (G.tripleOfNormal hP).arcLength_eq_succ_iff.2 ⟨hm, hlt⟩
  have htgt : (G.tripleOfNormal hP).target ℓ = (G.tripleOfNormal hP).vertexOf
      ((G.tripleOfNormal hP).inv ((G.tripleOfNormal hP).arcDart i m)) := by
    rw [hk, hinv]
    rfl
  have h2 := (G.tripleOfNormal hP).target_strandPerm hlenX ⟨ℓ, htgt⟩
  rw [← htgt] at h2
  have h3 : (G.tripleOfNormal hP).strandPerm i = ℓ :=
    targetIndex_injective (hP.isPreTripleDiagram_tripleOfNormal.endpoint_injective h2)
  rw [h1, h3]

/-- Iterating the trip map a further `ord(T)` times changes nothing. -/
private theorem iterate_add_orderOf_tripEquiv (n : ℕ) (x : H) :
    G.tripMap^[n + orderOf hG.toIsPlabicGraph.tripEquiv] x = G.tripMap^[n] x := by
  rw [Function.iterate_add_apply, ← hG.toIsPlabicGraph.tripEquiv_pow_apply (orderOf _) x,
    pow_orderOf_eq_one]
  rfl

/-- Along a trip of `G` that meets no leg, the strand of `X(G)` through `x⁺_k` follows the
trip two steps at a time. -/
theorem strandMap_iterate_plus_of_forall_not_isLeg {d : H} (hd : ∀ n, ¬G.IsLeg (G.tripMap^[n] d))
    {N : ℕ} (hk₀ : G.rot.symm (G.tripMap^[N] d) ∈ G.blackDarts) (j : ℕ) :
    ∃ k : G.BlackDart,
      (G.tripleOfNormal hG.isNormalPlabicPregraph).strandMap^[j] (.plus ⟨_, hk₀⟩) = .plus k ∧
      G.rot (k : H) = G.tripMap^[2 * j + N] d := by
  have hP := hG.isNormalPlabicPregraph
  induction j with
  | zero => exact ⟨⟨_, hk₀⟩, rfl, by simp⟩
  | succ j ih =>
    obtain ⟨k, hk, hrk⟩ := ih
    have hl : G.legIndex (G.rot (k : H)) = none := by
      rcases h : G.legIndex (G.rot (k : H)) with _ | ℓ
      · rfl
      · exfalso
        have := (hG.strandMap_plus_of_eq_inv_leg k
          (inv_leg_of_legIndex_eq_some h).symm).1
        rw [hrk, ← Function.iterate_succ_apply' (f := G.tripMap)] at this
        exact hd _ ⟨ℓ, this.symm⟩
    have hint := hP.not_isBoundaryVertex_inv (hP.rot_mem_blackDarts k.2) hl
    obtain ⟨-, k', hk', hS⟩ := hG.strandMap_plus_of_internal k hint
    refine ⟨k', by rw [Function.iterate_succ_apply', hk, hS], ?_⟩
    rw [hk', Equiv.apply_symm_apply, hrk,
      show 2 * (j + 1) + N = (2 * j + N) + 1 + 1 by ring, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

/-- A normal plabic graph with a roundtrip has a closed strand in `X(G)`. -/
theorem exists_isClosedStrand_of_hasRoundtrip (hrt : G.HasRoundtrip) :
    ∃ C, (G.tripleOfNormal hG.isNormalPlabicPregraph).IsClosedStrand C := by
  have hP := hG.isNormalPlabicPregraph
  obtain ⟨d, hdB, hd⟩ := hasRoundtrip_iff.1 hrt
  have hdi : ¬G.IsBoundaryVertex (G.vertexOf d) := by
    intro hb
    obtain ⟨j, hj⟩ := hP.exists_leg_eq hb hdB
    exact hd 0 ⟨j, hj⟩
  obtain ⟨N, hN⟩ : ∃ N, G.tripMap^[N] d ∈ G.blackDarts := by
    cases hc : G.colour d
    · obtain ⟨h1, h2⟩ := hP.inv_black_of_white hdi hc
      refine ⟨1, ?_⟩
      rw [Function.iterate_one, tripMap_apply, turn_of_black h1 h2]
      exact hP.rot_mem_blackDarts (mem_blackDarts.2 ⟨h1, h2⟩)
    · exact ⟨0, mem_blackDarts.2 ⟨hdi, hc⟩⟩
  have hk₀ : G.rot.symm (G.tripMap^[N] d) ∈ G.blackDarts := hP.rot_symm_mem_blackDarts hN
  refine ⟨(G.tripleOfNormal hP).strandOrbit (.plus ⟨_, hk₀⟩), .plus ⟨_, hk₀⟩, by simp, rfl,
    fun e he => ?_⟩
  obtain ⟨j, rfl⟩ := (G.tripleOfNormal hP).mem_strandOrbit.1 he
  obtain ⟨k, hk, hrk⟩ := hG.strandMap_iterate_plus_of_forall_not_isLeg hd hk₀ j
  rw [hk]
  rcases h : G.legIndex (k : H) with _ | ℓ
  · exact hP.not_isBoundaryVertex_tripleOfNormal_plus h
  · exfalso
    have hT : G.tripMap (G.leg ℓ) = G.tripMap^[2 * j + N] d := by
      rw [tripMap_apply,
        turn_of_black (hP.not_isBoundaryVertex_inv_leg ℓ) (hP.colour_inv_leg ℓ),
        inv_leg_of_legIndex_eq_some h, hrk]
    have hpos : 0 < orderOf hG.toIsPlabicGraph.tripEquiv :=
      (isOfFinOrder_of_finite _).orderOf_pos
    have hT' : G.tripMap (G.leg ℓ) = G.tripMap
        (G.tripMap^[2 * j + N + orderOf hG.toIsPlabicGraph.tripEquiv - 1] d) := by
      rw [hT, ← Function.iterate_succ_apply' (f := G.tripMap),
        show (2 * j + N + orderOf hG.toIsPlabicGraph.tripEquiv - 1).succ =
          2 * j + N + orderOf hG.toIsPlabicGraph.tripEquiv by omega,
        hG.iterate_add_orderOf_tripEquiv]
    exact hd _ ⟨ℓ, (tripMap_bijective hG.toIsPlabicGraph).1 hT'⟩

/-- A strand of `X(G)` through `x⁺_{k₀}` that never runs to an endpoint follows the trip of `G`
through `σ(k₀)`, which is then a roundtrip. -/
theorem hasRoundtrip_of_forall_not_runsToEndpoint_plus (k₀ : G.BlackDart)
    (hnot : ∀ j, ¬(G.tripleOfNormal hG.isNormalPlabicPregraph).RunsToEndpoint
      ((G.tripleOfNormal hG.isNormalPlabicPregraph).strandMap^[j] (.plus k₀))) :
    G.HasRoundtrip := by
  have hP := hG.isNormalPlabicPregraph
  have claim : ∀ j, ∃ k : G.BlackDart,
      (G.tripleOfNormal hP).strandMap^[j] (.plus k₀) = .plus k ∧
      G.rot (k : H) = G.tripMap^[2 * j] (G.rot k₀) ∧
      ¬G.IsLeg (G.tripMap^[2 * j + 1] (G.rot k₀)) := by
    intro j
    induction j with
    | zero =>
      have h0 := hnot 0
      rw [Function.iterate_zero_apply, hP.runsToEndpoint_plus_iff, not_not] at h0
      have hint := hP.not_isBoundaryVertex_inv (hP.rot_mem_blackDarts k₀.2) h0
      exact ⟨k₀, rfl, rfl, (hG.strandMap_plus_of_internal k₀ hint).1⟩
    | succ j ih =>
      obtain ⟨k, hk, hrk, -⟩ := ih
      have h0 := hnot j
      rw [hk, hP.runsToEndpoint_plus_iff, not_not] at h0
      have hint := hP.not_isBoundaryVertex_inv (hP.rot_mem_blackDarts k.2) h0
      obtain ⟨-, k', hk', hS⟩ := hG.strandMap_plus_of_internal k hint
      have hS' : (G.tripleOfNormal hP).strandMap^[j + 1] (.plus k₀) = .plus k' := by
        rw [Function.iterate_succ_apply', hk, hS]
      have hrk' : G.rot (k' : H) = G.tripMap^[2 * (j + 1)] (G.rot k₀) := by
        rw [hk', Equiv.apply_symm_apply, hrk, show 2 * (j + 1) = 2 * j + 1 + 1 by ring,
          Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine ⟨k', hS', hrk', ?_⟩
      have h1 := hnot (j + 1)
      rw [hS', hP.runsToEndpoint_plus_iff, not_not] at h1
      have hint' := hP.not_isBoundaryVertex_inv (hP.rot_mem_blackDarts k'.2) h1
      rw [Function.iterate_succ_apply', ← hrk']
      exact (hG.strandMap_plus_of_internal k' hint').1
  refine hasRoundtrip_iff.2 ⟨G.rot k₀,
    notMem_bdry_of_mem_blackDarts (hP.rot_mem_blackDarts k₀.2), fun n => ?_⟩
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨k, -, hrk, -⟩ := claim j
    rw [← hrk]
    exact hG.not_isLeg_of_mem_blackDarts (hP.rot_mem_blackDarts k.2)
  · exact (claim j).choose_spec.2.2

/-- A strand of `X(G)` through `x⁻_{k₀}` that never runs to an endpoint follows the trip of `G`
through `k₀` backwards, two steps at a time, meeting no leg. -/
theorem strandMap_iterate_minus_of_forall_not_runsToEndpoint (k₀ : G.BlackDart)
    (hnot : ∀ j, ¬(G.tripleOfNormal hG.isNormalPlabicPregraph).RunsToEndpoint
      ((G.tripleOfNormal hG.isNormalPlabicPregraph).strandMap^[j] (.minus k₀))) :
    ∀ j, ∃ k : G.BlackDart,
      (G.tripleOfNormal hG.isNormalPlabicPregraph).strandMap^[j] (.minus k₀) = .minus k ∧
      G.tripMap^[2 * j] k = k₀ ∧ ∀ t ≤ 2 * j, ¬G.IsLeg (G.tripMap^[t] k) := by
  have hP := hG.isNormalPlabicPregraph
  intro j
  induction j with
  | zero =>
    refine ⟨k₀, rfl, rfl, fun t ht => ?_⟩
    obtain rfl : t = 0 := by omega
    exact hG.not_isLeg_of_mem_blackDarts k₀.2
  | succ j ih =>
    obtain ⟨k, hk, hTk, hnl⟩ := ih
    have h0 := hnot j
    rw [hk, hP.runsToEndpoint_minus_iff, not_not] at h0
    have hk' : G.rot.symm (k : H) ∈ G.blackDarts := hP.rot_symm_mem_blackDarts k.2
    have hl' := hP.legIndex_psi ⟨_, hk'⟩ h0
    have hS : (G.tripleOfNormal hP).strandMap^[j + 1] (.minus k₀) =
        .minus (hP.psi ⟨_, hk'⟩ h0) := by
      have hnr := hnot j
      rw [hk] at hnr
      rw [Function.iterate_succ_apply', hk,
        TripleData.strandMap_of_not_runsToEndpoint _ hnr,
        IsNormalPlabicPregraph.tripleOfNormal_inv, IsNormalPlabicPregraph.tripleInv_minus,
        IsNormalPlabicPregraph.tripleOfNormal_rot,
        hP.tripleRot_plus_of_none (k := ⟨_, hk'⟩) h0,
        hP.tripleRot_minus_of_none h0, hP.tripleRot_plus_of_none hl']
    have hi := hP.not_isBoundaryVertex_inv hk' h0
    have hw := hP.colour_inv hk' h0
    have hi' : ¬G.IsBoundaryVertex (G.vertexOf (G.rot (G.inv (G.rot.symm (k : H))))) := by
      rwa [G.vertexOf_rot]
    have hT1 : G.tripMap (hP.psi ⟨_, hk'⟩ h0) = G.inv (G.rot.symm (k : H)) := by
      rw [IsNormalPlabicPregraph.coe_psi, tripMap_apply, hP.inv_inv,
        turn_of_white hi' (by rw [hG.colour_rot _ hi, hw]), Equiv.symm_apply_apply]
    have hT2 : G.tripMap (G.inv (G.rot.symm (k : H))) = k := by
      rw [tripMap_apply, hP.inv_inv, turn_of_black (mem_blackDarts.1 hk').1
        (mem_blackDarts.1 hk').2, Equiv.apply_symm_apply]
    have hTT : G.tripMap^[2] (hP.psi ⟨_, hk'⟩ h0 : H) = k := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one,
        hT1, hT2]
    refine ⟨hP.psi ⟨_, hk'⟩ h0, hS, ?_, fun t ht => ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring, Function.iterate_add_apply, hTT, hTk]
    · rcases Nat.lt_or_ge t 2 with h2 | h2
      · rcases Nat.lt_or_ge t 1 with h1 | h1
        · obtain rfl : t = 0 := by omega
          exact hG.not_isLeg_of_mem_blackDarts (hP.psi ⟨_, hk'⟩ h0).2
        · obtain rfl : t = 1 := by omega
          rw [Function.iterate_one, hT1]
          exact hG.not_isLeg_of_internal hi
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
        rw [Function.iterate_add_apply, hTT]
        exact hnl t' (by omega)

/-- A strand of `X(G)` through `x⁻_{k₀}` that never runs to an endpoint yields a roundtrip of
`G` through `k₀`. -/
theorem hasRoundtrip_of_forall_not_runsToEndpoint_minus (k₀ : G.BlackDart)
    (hnot : ∀ j, ¬(G.tripleOfNormal hG.isNormalPlabicPregraph).RunsToEndpoint
      ((G.tripleOfNormal hG.isNormalPlabicPregraph).strandMap^[j] (.minus k₀))) :
    G.HasRoundtrip := by
  have hP := hG.isNormalPlabicPregraph
  have hper : ∀ j, (G.tripleOfNormal hP).strandMap^[j] (.minus k₀) =
      ((((G.tripleOfNormal hP).rot ^ 3) * (G.tripleOfNormal hP).inv) ^ j) (.minus k₀) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', TripleData.strandMap_of_not_runsToEndpoint _ (hnot j),
        ih, pow_succ' _ j, Equiv.Perm.mul_apply]
      rfl
  set Q := orderOf (((G.tripleOfNormal hP).rot ^ 3) * (G.tripleOfNormal hP).inv) with hQ
  have hQpos : 0 < Q := (isOfFinOrder_of_finite _).orderOf_pos
  obtain ⟨k, hk, hTk, hnl⟩ := hG.strandMap_iterate_minus_of_forall_not_runsToEndpoint k₀ hnot Q
  have hkk : k = k₀ := by
    rw [hper, hQ, pow_orderOf_eq_one, Equiv.Perm.one_apply] at hk
    exact (TripleOfNormalDart.minus.inj hk).symm
  subst hkk
  have hperT : Function.IsPeriodicPt G.tripMap (2 * Q) (k : H) := hTk
  refine hasRoundtrip_iff.2 ⟨k, notMem_bdry_of_mem_blackDarts k.2, fun n => ?_⟩
  rw [← hperT.iterate_mod_apply]
  exact hnl _ (Nat.mod_lt _ (by omega)).le

/-- **Roundtrips and closed strands**: a normal plabic graph `G` has a roundtrip if and only if
`X(G)` has a closed strand. -/
@[cluster_algebras "lem_roundtrip_closed_strand"]
theorem hasRoundtrip_iff_exists_isClosedStrand :
    G.HasRoundtrip ↔ ∃ C, (G.tripleOfNormal hG.isNormalPlabicPregraph).IsClosedStrand C := by
  have hP := hG.isNormalPlabicPregraph
  refine ⟨hG.exists_isClosedStrand_of_hasRoundtrip, ?_⟩
  rintro ⟨C, z, hzB, rfl, hC⟩
  have hmem : ∀ j, (G.tripleOfNormal hP).strandMap^[j] z ∈
      (G.tripleOfNormal hP).strandOrbit z :=
    fun j => (G.tripleOfNormal hP).mem_strandOrbit.2 ⟨j, rfl⟩
  have hnot : ∀ j, ¬(G.tripleOfNormal hP).RunsToEndpoint
      ((G.tripleOfNormal hP).strandMap^[j] z) := by
    intro j hr
    have := hC _ (hmem (j + 1))
    rw [Function.iterate_succ_apply',
      (G.tripleOfNormal hP).strandMap_of_runsToEndpoint hr] at this
    exact this hr
  rcases z with k₀ | k₀ | r | r
  · exact hG.hasRoundtrip_of_forall_not_runsToEndpoint_plus k₀ hnot
  · exact hG.hasRoundtrip_of_forall_not_runsToEndpoint_minus k₀ hnot
  · simp at hzB
  · simp at hzB

end IsNormalPlabicGraph

end PlabicData

end ClusterAlgebras

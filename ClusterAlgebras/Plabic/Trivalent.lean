/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap
public import ClusterAlgebras.Plabic.FirstReturn

/-!
# Trivalent plabic graphs, splitting a vertex, and the flip move

A plabic graph is *trivalent* if every internal vertex consists of exactly three darts.

Let `K` be a plabic graph, `z` an internal vertex of `K` consisting of `k` darts, `s ∈ z` and
`p ∈ [0, k]`, and write `x_j = σ^{j-1}(s)`, so that `z = (x_1 x_2 … x_k)` as a cycle of the
rotation `σ`. The *splitting* of `K` at `z` from `s` of size `p` adds two new darts `n`, `n̄`
forming a new edge, and replaces the vertex `z` by the two vertices `(n x_1 … x_p)` and
`(n̄ x_{p+1} … x_k)`, both coloured as `z`. Contracting the new edge gives back the rotation `σ`:
the rotation induced on the old darts by the new rotation and the dart `n` is `σ`. Using this and
the count of faces under contraction, the splitting of a plabic graph is again a plabic graph,
with the same boundary vertices and legs.

The *flip move* (M4) applies to an edge `{d, d̄}` whose endpoints `x = (d a₁ a₂)` and
`y = (d̄ b₁ b₂)` are distinct trivalent internal vertices of the same colour, and replaces them by
the vertices `(d a₂ b₁)` and `(d̄ b₂ a₁)`.

## Main definitions

* `ClusterAlgebras.PlabicData.IsTrivalent`, `ClusterAlgebras.PlabicGraph.IsTrivalent`: trivalent
  plabic graphs.
* `ClusterAlgebras.splitInv`, `ClusterAlgebras.splitRot`: the involution and the rotation of a
  splitting, on the darts `H ⊕ Fin 2`.
* `ClusterAlgebras.PlabicData.vertexSplit`: the splitting of a vertex.
* `ClusterAlgebras.PlabicData.IsFlipEdge`, `ClusterAlgebras.PlabicData.flipMove`: the flip move,
  with its rotation `ClusterAlgebras.flipRot`.

## Main results

* `ClusterAlgebras.coe_inducedRotation_splitRot`, `ClusterAlgebras.inducedRotationPerm_splitRot`:
  contracting the new edge of a splitting restores the rotation.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.vertexSplit`,
  `ClusterAlgebras.PlabicData.bvertex_vertexSplit`, `ClusterAlgebras.PlabicData.leg_vertexSplit`:
  a splitting of a plabic graph is a plabic graph with the same boundary vertices and legs.

## Implementation notes

* **New darts.** The splitting lives on the dart type `H ⊕ Fin 2`: the old dart `x` is
  `Sum.inl x`, and the new darts are `n = Sum.inr 0` and `n̄ = Sum.inr 1`.
* **The rotation of a splitting** is built as a product of transpositions, which makes it a
  permutation by construction: `σ̂ ∘ (x_k n̄)` inserts `n̄` before `x_1` in the cycle `z` (where
  `σ̂` is `σ` fixing the new darts), then `∘ (y n)` inserts `n` after `y`, where `y = x_p` if
  `p ≥ 1` and `y = n̄` if `p = 0`, giving the cycle `(n̄ x_1 … x_p n x_{p+1} … x_k)`, and finally
  `∘ (n n̄)` cuts this cycle into `(n x_1 … x_p)` and `(n̄ x_{p+1} … x_k)`. The values are
  `ClusterAlgebras.splitRot_inl`, `splitRot_inr_zero`, `splitRot_inr_one`; on the cycle `z` they
  are FWZ's cycles when `p ≤ k` (`splitRot_inl_pow`, `splitRot_inr_one_of_le`). The
  definition makes sense for every `p`, and the splitting of a plabic graph at an internal vertex
  is a plabic graph for every `p`; the bound `p ≤ k` is only needed to read off the two cycles.
* **Colours** are a function on darts: the splitting gives the new darts the colour of `s`, and
  every old dart keeps its colour. For a plabic graph the colour is constant on the internal vertex
  `z`, so both new vertices have the colour `κ(z)`.
* **The rotation of a flip** is `σ ∘ (d a₁ b₂)(a₂ d̄ b₁)`, written as a product of four
  transpositions; its values on `x ∪ y` are the two new cycles when the endpoints are distinct
  trivalent vertices (`ClusterAlgebras.PlabicData.IsFlipEdge.flipRot_apply_self` and its
  companions). The colouring of a flip gives every dart of `x ∪ y` the colour of `d`.
* **Labels.** The labels `[1, b]` are `Fin b`, `0`-indexed, as in the rest of the chapter.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Equiv Equiv.Perm Function Finset

/-! ### Trivalent plabic graphs -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-- A plabic graph is **trivalent** if every internal vertex consists of exactly three darts. -/
@[cluster_algebras "def_trivalent_plabic_graph"]
def IsTrivalent : Prop := ∀ v ∈ G.internalVertices, v.card = 3

variable {G}

/-- In a trivalent graph, the vertex of a dart at an internal vertex has three darts. -/
theorem IsTrivalent.card_vertexOf (h : G.IsTrivalent) {d : H}
    (hd : ¬G.IsBoundaryVertex (G.vertexOf d)) : (G.vertexOf d).card = 3 :=
  h _ (G.vertexOf_mem_internalVertices.2 hd)

end PlabicData

/-- A bundled plabic graph is **trivalent** if its underlying tuple is trivalent. -/
def PlabicGraph.IsTrivalent {b : ℕ} (G : PlabicGraph b) : Prop := G.data.IsTrivalent

/-! ### Auxiliary facts on orbits of permutations -/

section Orbits

variable {X : Type*}

private theorem zpow_sumCongr {α β : Type*} (f : Perm α) (g : Perm β) (n : ℤ) :
    Perm.sumCongr f g ^ n = Perm.sumCongr (f ^ n) (g ^ n) :=
  (map_zpow (sumCongrHom α β) (f, g) n).symm

private theorem sameCycle_sumCongr_inl {α β : Type*} (f : Perm α) (g : Perm β) {x y : α} :
    (Perm.sumCongr f g).SameCycle (Sum.inl x) (Sum.inl y) ↔ f.SameCycle x y := by
  simp [SameCycle, zpow_sumCongr]

private theorem sameCycle_sumCongr_inr {α β : Type*} (f : Perm α) (g : Perm β) {x y : β} :
    (Perm.sumCongr f g).SameCycle (Sum.inr x) (Sum.inr y) ↔ g.SameCycle x y := by
  simp [SameCycle, zpow_sumCongr]

private theorem not_sameCycle_sumCongr_inl_inr {α β : Type*} (f : Perm α) (g : Perm β) {x : α}
    {y : β} : ¬(Perm.sumCongr f g).SameCycle (Sum.inl x) (Sum.inr y) := by
  simp [SameCycle, zpow_sumCongr]

private theorem numOrbits_sumCongr {α β : Type*} [Finite α] [Finite β] (f : Perm α)
    (g : Perm β) : numOrbits (Perm.sumCongr f g) = numOrbits f + numOrbits g := by
  let F : Quotient (SameCycle.setoid f) ⊕ Quotient (SameCycle.setoid g) →
      Quotient (SameCycle.setoid (Perm.sumCongr f g)) :=
    Sum.elim (Quotient.map Sum.inl fun _ _ h => (sameCycle_sumCongr_inl f g).2 h)
      (Quotient.map Sum.inr fun _ _ h => (sameCycle_sumCongr_inr f g).2 h)
  have hF : Bijective F := by
    refine ⟨?_, ?_⟩
    · rintro (u | u) (v | v) huv <;>
        induction u using Quotient.inductionOn <;> induction v using Quotient.inductionOn
      · exact congrArg Sum.inl
          (Quotient.sound ((sameCycle_sumCongr_inl f g).1 (Quotient.exact huv)))
      · exact absurd (Quotient.exact huv) (not_sameCycle_sumCongr_inl_inr f g)
      · exact absurd (Quotient.exact huv).symm (not_sameCycle_sumCongr_inl_inr f g)
      · exact congrArg Sum.inr
          (Quotient.sound ((sameCycle_sumCongr_inr f g).1 (Quotient.exact huv)))
    · intro c
      induction c using Quotient.inductionOn with | h z => ?_
      rcases z with x | y
      · exact ⟨Sum.inl ⟦x⟧, rfl⟩
      · exact ⟨Sum.inr ⟦y⟧, rfl⟩
  rw [numOrbits, numOrbits, numOrbits, ← Nat.card_sum]
  exact (Nat.card_congr (Equiv.ofBijective F hF)).symm

private theorem numOrbits_one : numOrbits (1 : Perm X) = Nat.card X := by
  refine Nat.card_congr (Equiv.ofBijective (Quotient.lift id fun x y h => sameCycle_one.1 h)
    ⟨?_, fun x => ⟨⟦x⟧, rfl⟩⟩)
  intro u v huv
  induction u using Quotient.inductionOn
  induction v using Quotient.inductionOn
  exact Quotient.sound (sameCycle_one.2 huv)

private theorem numOrbits_swap_fin_two : numOrbits (Equiv.swap (0 : Fin 2) 1) = 1 := by
  have h := numOrbits_mul_swap_of_not_sameCycle (1 : Perm (Fin 2)) (p := 0) (q := 1)
    (by simp [sameCycle_one])
  rwa [one_mul, numOrbits_one, Nat.card_eq_fintype_card, Fintype.card_fin] at h

private theorem sameCycle_of_semiconj {α β : Type*} {f : Perm α} {g : Perm β} (e : α ≃ β)
    (h : ∀ x, e (f x) = g (e x)) {x y : α} : g.SameCycle (e x) (e y) ↔ f.SameCycle x y := by
  have hc : e.permCongr f = g := by
    ext x
    simpa [Equiv.permCongr_apply] using h (e.symm x)
  have hpow : ∀ n : ℤ, ∀ x, e ((f ^ n) x) = (g ^ n) (e x) := by
    intro n x
    rw [← hc]
    have : (e.permCongr f) ^ n = e.permCongr (f ^ n) := by
      simpa using (map_zpow (Equiv.permCongrHom e).toMonoidHom f n).symm
    rw [this, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, e.injective (by rw [hpow, hn])⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hpow, hn]⟩

private theorem numOrbits_of_semiconj {α β : Type*} {f : Perm α} {g : Perm β} (e : α ≃ β)
    (h : ∀ x, e (f x) = g (e x)) : numOrbits f = numOrbits g :=
  Nat.card_congr (Quotient.congr e fun _ _ => (sameCycle_of_semiconj e h).symm)

private theorem sameCycle_iff_of_involutive [Finite X] {ι : Perm X} (h : Involutive ι)
    {x y : X} : ι.SameCycle x y ↔ y = x ∨ y = ι x := by
  constructor
  · intro hxy
    obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      rcases ih (sameCycle_pow_right.2 (SameCycle.refl _ _)) with h' | h'
      · exact Or.inr (by rw [h'])
      · exact Or.inl (by rw [h', h x])
  · rintro (rfl | rfl)
    · exact SameCycle.refl _ _
    · exact sameCycle_apply_right.2 (SameCycle.refl _ _)

private theorem minimalPeriod_perm_pos [Finite X] (σ : Perm X) (x : X) :
    0 < minimalPeriod σ x := by
  refine IsPeriodicPt.minimalPeriod_pos (n := orderOf σ)
    (isOfFinOrder_of_finite σ).orderOf_pos ?_
  change (⇑σ)^[orderOf σ] x = x
  rw [Perm.iterate_eq_pow, pow_orderOf_eq_one, Perm.one_apply]

section Period

variable [Fintype X] [DecidableEq X]

private theorem card_sameCycle_eq_minimalPeriod (σ : Perm X) (x : X) :
    ({y | σ.SameCycle x y} : Finset X).card = minimalPeriod σ x := by
  have h : ({y | σ.SameCycle x y} : Finset X) =
      (range (minimalPeriod σ x)).image fun i => (σ ^ i) x := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
    constructor
    · intro hy
      obtain ⟨n, rfl⟩ := hy.exists_nat_pow_eq
      refine ⟨n % minimalPeriod σ x, Nat.mod_lt _ (minimalPeriod_perm_pos σ x), ?_⟩
      rw [← Perm.iterate_eq_pow, ← Perm.iterate_eq_pow, iterate_mod_minimalPeriod_eq]
    · rintro ⟨i, -, rfl⟩
      exact sameCycle_pow_right.2 (SameCycle.refl _ _)
  rw [h, card_image_of_injOn, card_range]
  intro i hi j hj hij
  exact iterate_injOn_Iio_minimalPeriod (f := σ) (x := x) (by simpa using hi) (by simpa using hj)
    (by simpa [Perm.iterate_eq_pow] using hij)

/-- `σ^k(x) = x` for `k` the number of elements of the orbit of `x`. -/
private theorem pow_card_sameCycle_apply (σ : Perm X) (x : X) :
    (σ ^ ({y | σ.SameCycle x y} : Finset X).card) x = x := by
  rw [card_sameCycle_eq_minimalPeriod, ← Perm.iterate_eq_pow, iterate_minimalPeriod]

/-- The elements `σ^i(x)`, `i < k`, of the orbit of `x` are distinct. -/
private theorem eq_of_pow_apply_eq (σ : Perm X) (x : X) {i j : ℕ}
    (hi : i < ({y | σ.SameCycle x y} : Finset X).card)
    (hj : j < ({y | σ.SameCycle x y} : Finset X).card) (h : (σ ^ i) x = (σ ^ j) x) : i = j := by
  rw [card_sameCycle_eq_minimalPeriod] at hi hj
  exact iterate_injOn_Iio_minimalPeriod (f := σ) (x := x) hi hj
    (by simpa [Perm.iterate_eq_pow] using h)

private theorem one_le_card_sameCycle (σ : Perm X) (x : X) :
    1 ≤ ({y | σ.SameCycle x y} : Finset X).card :=
  card_pos.2 ⟨x, by simp [SameCycle.refl]⟩

end Period

/-- A first return after two steps. -/
private theorem coe_firstReturn_two [Finite X] {π : Perm X} {Y : Set X} {y : Y}
    (h1 : π y ∉ Y) (h2 : π (π y) ∈ Y) : (firstReturn π Y y : X) = π (π y) := by
  have hp : (π ^ 2) y = π (π y) := by rw [pow_two, Perm.mul_apply]
  rw [coe_firstReturn_of_pow (m := 2) two_pos (by rwa [hp]) fun j hj hj2 => ?_, hp]
  obtain rfl : j = 1 := by omega
  rwa [pow_one]

/-- A first return after three steps. -/
private theorem coe_firstReturn_three [Finite X] {π : Perm X} {Y : Set X} {y : Y}
    (h1 : π y ∉ Y) (h2 : π (π y) ∉ Y) (h3 : π (π (π y)) ∈ Y) :
    (firstReturn π Y y : X) = π (π (π y)) := by
  have hp2 : (π ^ 2) y = π (π y) := by rw [pow_two, Perm.mul_apply]
  have hp3 : (π ^ 3) y = π (π (π y)) := by rw [pow_succ', Perm.mul_apply, hp2]
  rw [coe_firstReturn_of_pow (m := 3) (by norm_num) (by rwa [hp3]) fun j hj hj3 => ?_, hp3]
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · rwa [pow_one]
  · rwa [hp2]

end Orbits

/-! ### Counting vertices, edges and orbits of `φ` -/

namespace RotationSystem

variable {H : Type*} [Fintype H] [DecidableEq H] (R : RotationSystem H)

private theorem card_vertices_eq_numOrbits : R.vertices.card = numOrbits R.rot := by
  rw [numOrbits_eq_card_image]
  rfl

private theorem card_faceOrbits_eq_numOrbits : R.faceOrbits.card = numOrbits R.facePerm := by
  rw [numOrbits_eq_card_image]
  rfl

private theorem card_edges_eq_numOrbits (h : Involutive R.inv) :
    R.edges.card = numOrbits R.inv := by
  rw [numOrbits_eq_card_image, edges]
  refine congrArg card (congrArg (fun f => image f univ) (funext fun d => ?_))
  ext e
  simp [edgeOf, sameCycle_iff_of_involutive h]

end RotationSystem

/-! ### The rotation and involution of a splitting -/

section Split

variable {H : Type*}

/-- The **involution of a splitting**: on the darts `H ⊕ Fin 2` it is `ι` on the old darts
`Sum.inl x` and exchanges the two new darts `n = Sum.inr 0` and `n̄ = Sum.inr 1`. -/
def splitInv (ι : Perm H) : Perm (H ⊕ Fin 2) := Perm.sumCongr ι (Equiv.swap 0 1)

section Inv

variable (ι : Perm H)

/-- On an old dart `Sum.inl x`, the involution of a splitting is `ι`. -/
@[simp]
theorem splitInv_inl (x : H) : splitInv ι (Sum.inl x) = Sum.inl (ι x) := rfl

/-- The involution of a splitting sends `n = Sum.inr 0` to `n̄ = Sum.inr 1`. -/
@[simp]
theorem splitInv_inr_zero : splitInv ι (Sum.inr 0) = Sum.inr 1 := rfl

/-- The involution of a splitting sends `n̄ = Sum.inr 1` to `n = Sum.inr 0`. -/
@[simp]
theorem splitInv_inr_one : splitInv ι (Sum.inr 1) = Sum.inr 0 := rfl

variable {ι} in
/-- If `ι` is an involution, so is the involution `splitInv ι` of a splitting. -/
theorem splitInv_involutive (h : Involutive ι) : Involutive (splitInv ι) := by
  rintro (x | i)
  · simp [h x]
  · fin_cases i <;> rfl

/-- If `ι` has no fixed points, neither has the involution `splitInv ι` of a splitting. -/
theorem splitInv_ne (h : ∀ x, ι x ≠ x) (d : H ⊕ Fin 2) : splitInv ι d ≠ d := by
  rcases d with x | i
  · simpa using h x
  · fin_cases i <;> simp

/-- The old darts `H`, as the complement `(H ⊕ Fin 2) \ {n, n̄}` of the new edge of a
splitting. -/
noncomputable def splitComplEquiv :
    H ≃ ((({Sum.inr 0, splitInv ι (Sum.inr 0)} : Set (H ⊕ Fin 2))ᶜ : Set (H ⊕ Fin 2))) :=
  Equiv.ofBijective (fun x => ⟨Sum.inl x, by simp⟩) <| by
    refine ⟨fun x y h => by simpa using h, ?_⟩
    rintro ⟨x | i, hi⟩
    · exact ⟨x, rfl⟩
    · exfalso
      fin_cases i <;> simp at hi

/-- The equivalence `splitComplEquiv ι` sends `x` to the old dart `Sum.inl x`. -/
@[simp]
theorem coe_splitComplEquiv (x : H) : (splitComplEquiv ι x : H ⊕ Fin 2) = Sum.inl x := rfl

end Inv

variable [DecidableEq H]

/-- The rotation `σ` with the new dart `n̄ = Sum.inr 1` inserted before `s`, that is, after
`σ⁻¹(s)`; the new dart `n = Sum.inr 0` is fixed. -/
def splitRotAux (σ : Perm H) (s : H) : Perm (H ⊕ Fin 2) :=
  Perm.sumCongr σ 1 * Equiv.swap (Sum.inl (σ.symm s)) (Sum.inr 1)

/-- The dart after which the new dart `n` is inserted in a splitting of size `p` from `s`: the dart
`x_p = σ^{p-1}(s)` if `p ≥ 1`, and the new dart `n̄` if `p = 0`. -/
def splitAnchor (σ : Perm H) (s : H) (p : ℕ) : H ⊕ Fin 2 :=
  if p = 0 then Sum.inr 1 else Sum.inl ((σ ^ (p - 1)) s)

/-- The **rotation of a splitting** of the vertex `z` of `s` from `s` of size `p`, with new darts
`n = Sum.inr 0` and `n̄ = Sum.inr 1`: it agrees with `σ` off `z`, and on `z ⊔ {n, n̄}`, where
`z = (x_1 … x_k)` with `x_j = σ^{j-1}(s)`, it consists of the two cycles `(n x_1 … x_p)` and
`(n̄ x_{p+1} … x_k)` when `p ≤ k` (`splitRot_inl_pow`, `splitRot_inr_zero`,
`splitRot_inr_one_of_le`). It is the cycle `(n̄ x_1 … x_p n x_{p+1} … x_k)` cut by the
transposition `(n n̄)`. -/
def splitRot (σ : Perm H) (s : H) (p : ℕ) : Perm (H ⊕ Fin 2) :=
  splitRotAux σ s * Equiv.swap (splitAnchor σ s p) (Sum.inr 0) * Equiv.swap (Sum.inr 0) (Sum.inr 1)

variable (ι σ : Perm H) (s : H) (p : ℕ)

private theorem splitRotAux_inl (x : H) :
    splitRotAux σ s (Sum.inl x) = if σ x = s then Sum.inr 1 else Sum.inl (σ x) := by
  unfold splitRotAux
  rw [Perm.mul_apply]
  by_cases hx : σ x = s
  · obtain rfl : x = σ.symm s := by rw [← hx, Equiv.symm_apply_apply]
    simp
  · have hne : (Sum.inl x : H ⊕ Fin 2) ≠ Sum.inl (σ.symm s) := by
      intro h
      apply hx
      rw [Sum.inl.inj h, Equiv.apply_symm_apply]
    rw [swap_apply_of_ne_of_ne hne Sum.inl_ne_inr, if_neg hx]
    simp

private theorem splitRotAux_inr_zero : splitRotAux σ s (Sum.inr 0) = Sum.inr 0 := by
  simp [splitRotAux, swap_apply_of_ne_of_ne]

private theorem splitRotAux_inr_one : splitRotAux σ s (Sum.inr 1) = Sum.inl s := by
  simp [splitRotAux]

omit [DecidableEq H] in
private theorem splitAnchor_ne_inr_zero : splitAnchor σ s p ≠ Sum.inr 0 := by
  unfold splitAnchor
  split_ifs <;> simp

omit [DecidableEq H] in
private theorem splitAnchor_eq_inr_one_iff : splitAnchor σ s p = Sum.inr 1 ↔ p = 0 := by
  unfold splitAnchor
  split_ifs with h <;> simp [h]

omit [DecidableEq H] in
private theorem splitAnchor_eq_inl_iff (x : H) :
    splitAnchor σ s p = Sum.inl x ↔ p ≠ 0 ∧ x = (σ ^ (p - 1)) s := by
  unfold splitAnchor
  split_ifs with h <;> simp [h, eq_comm]

/-- The rotation of a splitting at an old dart. -/
theorem splitRot_inl (x : H) :
    splitRot σ s p (Sum.inl x) = if p ≠ 0 ∧ x = (σ ^ (p - 1)) s then Sum.inr 0
      else if σ x = s then Sum.inr 1 else Sum.inl (σ x) := by
  unfold splitRot
  rw [Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne Sum.inl_ne_inr Sum.inl_ne_inr]
  by_cases h : p ≠ 0 ∧ x = (σ ^ (p - 1)) s
  · rw [if_pos h, ← (splitAnchor_eq_inl_iff σ s p x).2 h, swap_apply_left,
      splitRotAux_inr_zero]
  · have hne : (Sum.inl x : H ⊕ Fin 2) ≠ splitAnchor σ s p := fun h' =>
      h ((splitAnchor_eq_inl_iff σ s p x).1 h'.symm)
    rw [if_neg h, swap_apply_of_ne_of_ne hne Sum.inl_ne_inr, splitRotAux_inl]

/-- The rotation of a splitting at the new dart `n`: it is the start of the cycle
`(n x_1 … x_p)`. -/
theorem splitRot_inr_zero :
    splitRot σ s p (Sum.inr 0) = if p = 0 then Sum.inr 0 else Sum.inl s := by
  unfold splitRot
  rw [Perm.mul_apply, Perm.mul_apply, swap_apply_left]
  by_cases hp : p = 0
  · rw [if_pos hp, ← (splitAnchor_eq_inr_one_iff σ s p).2 hp, swap_apply_left,
      splitRotAux_inr_zero]
  · have hne : (Sum.inr 1 : H ⊕ Fin 2) ≠ splitAnchor σ s p := fun h =>
      hp ((splitAnchor_eq_inr_one_iff σ s p).1 h.symm)
    rw [if_neg hp, swap_apply_of_ne_of_ne hne (by simp), splitRotAux_inr_one]

/-- The rotation of a splitting at the new dart `n̄`: it is the start of the cycle
`(n̄ x_{p+1} … x_k)`. -/
theorem splitRot_inr_one :
    splitRot σ s p (Sum.inr 1) = if p ≠ 0 ∧ (σ ^ p) s = s then Sum.inr 1
      else Sum.inl ((σ ^ p) s) := by
  unfold splitRot
  rw [Perm.mul_apply, Perm.mul_apply, swap_apply_right, swap_apply_right]
  by_cases hp : p = 0
  · subst hp
    simp [splitAnchor, splitRotAux_inr_one]
  · have hσ : σ ((σ ^ (p - 1)) s) = (σ ^ p) s := by
      rw [← Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    rw [splitAnchor, if_neg hp, splitRotAux_inl, hσ]
    simp [hp]

/-- Off the vertex `z` of `s`, the rotation of a splitting is `σ`. -/
theorem splitRot_inl_of_not_sameCycle {x : H} (hx : ¬σ.SameCycle s x) :
    splitRot σ s p (Sum.inl x) = Sum.inl (σ x) := by
  rw [splitRot_inl, if_neg, if_neg]
  · rintro rfl
    exact hx (sameCycle_apply_left.2 (SameCycle.refl _ _))
  · rintro ⟨-, rfl⟩
    exact hx (sameCycle_pow_right.2 (SameCycle.refl _ _))

/-- Off the vertex `z` of `s`, every power of the rotation of a splitting is the same power of
`σ`. -/
theorem splitRot_pow_inl_of_not_sameCycle {x : H} (hx : ¬σ.SameCycle s x) (n : ℕ) :
    (splitRot σ s p ^ n) (Sum.inl x) = Sum.inl ((σ ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, splitRot_inl_of_not_sameCycle, ← Perm.mul_apply,
      ← pow_succ']
    exact fun h => hx (h.trans (sameCycle_pow_right.2 (SameCycle.refl _ _)).symm)

section Cycles

variable [Fintype H]

/-- **The rotation of a splitting on the vertex `z`.** Write `k` for the number of darts of
`z`, the orbit of `s`, and `x_{j+1} = σ^j(s)`. For `p ≤ k` the rotation of the splitting maps
`x_{j+1}` to `n` if `j + 1 = p`, to `n̄` if `j + 1 = k ≠ p`, and to `x_{j+2}` otherwise: on the old
darts of `z` it consists of the cycles `(n x_1 … x_p)` and `(n̄ x_{p+1} … x_k)`. -/
theorem splitRot_inl_pow (hp : p ≤ ({y | σ.SameCycle s y} : Finset H).card) {j : ℕ}
    (hj : j < ({y | σ.SameCycle s y} : Finset H).card) :
    splitRot σ s p (Sum.inl ((σ ^ j) s)) =
      if j + 1 = p then Sum.inr 0
      else if j + 1 = ({y | σ.SameCycle s y} : Finset H).card then Sum.inr 1
      else Sum.inl ((σ ^ (j + 1)) s) := by
  set k := ({y | σ.SameCycle s y} : Finset H).card with hk
  have hσ : σ ((σ ^ j) s) = (σ ^ (j + 1)) s := by rw [← Perm.mul_apply, ← pow_succ']
  have h1 : (p ≠ 0 ∧ (σ ^ j) s = (σ ^ (p - 1)) s) ↔ j + 1 = p := by
    constructor
    · rintro ⟨hp0, h⟩
      have := eq_of_pow_apply_eq σ s hj (by omega) h
      omega
    · intro h
      exact ⟨by omega, by rw [show p - 1 = j by omega]⟩
  have h2 : (σ ^ (j + 1)) s = s ↔ j + 1 = k := by
    constructor
    · intro h
      by_contra hne
      have := eq_of_pow_apply_eq σ s (i := j + 1) (j := 0) (by omega)
        (by have := one_le_card_sameCycle σ s; omega) (by rw [h, pow_zero, Perm.one_apply])
      omega
    · intro h
      rw [h]
      exact pow_card_sameCycle_apply σ s
  rw [splitRot_inl, hσ]
  simp only [h1, h2]

/-- The rotation of a splitting at the new dart `n̄`, for `p ≤ k`: `n̄` is fixed when `p = k`, and
otherwise it is followed by `x_{p+1} = σ^p(s)`. -/
theorem splitRot_inr_one_of_le (hp : p ≤ ({y | σ.SameCycle s y} : Finset H).card) :
    splitRot σ s p (Sum.inr 1) = if p = ({y | σ.SameCycle s y} : Finset H).card then Sum.inr 1
      else Sum.inl ((σ ^ p) s) := by
  have h : (p ≠ 0 ∧ (σ ^ p) s = s) ↔ p = ({y | σ.SameCycle s y} : Finset H).card := by
    have h1 := one_le_card_sameCycle σ s
    constructor
    · rintro ⟨hp0, h⟩
      by_contra hne
      have := eq_of_pow_apply_eq σ s (i := p) (j := 0) (by omega) (by omega)
        (by rw [h, pow_zero, Perm.one_apply])
      omega
    · intro h
      refine ⟨by omega, ?_⟩
      rw [h]
      exact pow_card_sameCycle_apply σ s
  rw [splitRot_inr_one]
  simp only [h]

end Cycles

/-! ### Contracting the new edge restores the rotation -/

private theorem coe_inducedRotation_splitRot_aux [Finite H]
    (z : (({Sum.inr 0, splitInv ι (Sum.inr 0)} : Set (H ⊕ Fin 2))ᶜ : Set (H ⊕ Fin 2))) {x : H}
    (hz : (z : H ⊕ Fin 2) = Sum.inl x) :
    (inducedRotation (splitInv ι) (splitRot σ s p) (Sum.inr 0) z : H ⊕ Fin 2) =
      Sum.inl (σ x) := by
  set Y : Set (H ⊕ Fin 2) := ({Sum.inr 0, splitInv ι (Sum.inr 0)} : Set (H ⊕ Fin 2))ᶜ
  have hYl : ∀ y : H, Sum.inl y ∈ Y := fun y => by simp [Y]
  have hY0 : (Sum.inr 0 : H ⊕ Fin 2) ∉ Y := by simp [Y]
  have hY1 : (Sum.inr 1 : H ⊕ Fin 2) ∉ Y := by simp [Y]
  set τ := splitRot σ s p * Equiv.swap (Sum.inr 0) (splitInv ι (Sum.inr 0)) with hτ
  have hτl : ∀ y : H, τ (Sum.inl y) = splitRot σ s p (Sum.inl y) := fun y => by
    simp [hτ, swap_apply_of_ne_of_ne]
  have hτ0 : τ (Sum.inr 0) = splitRot σ s p (Sum.inr 1) := by simp [hτ]
  have hτ1 : τ (Sum.inr 1) = splitRot σ s p (Sum.inr 0) := by simp [hτ]
  clear_value τ
  unfold inducedRotation
  rw [← hτ]
  by_cases h1 : p ≠ 0 ∧ x = (σ ^ (p - 1)) s
  · have e1 : τ (Sum.inl x) = Sum.inr 0 := by rw [hτl, splitRot_inl, if_pos h1]
    have hσx : (σ ^ p) s = σ x := by
      obtain ⟨hp, rfl⟩ := h1
      rw [← Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    by_cases h2 : σ x = s
    · have e2 : τ (Sum.inr 0) = Sum.inr 1 := by
        rw [hτ0, splitRot_inr_one, if_pos ⟨h1.1, hσx.trans h2⟩]
      have e3 : τ (Sum.inr 1) = Sum.inl s := by rw [hτ1, splitRot_inr_zero, if_neg h1.1]
      rw [coe_firstReturn_three] <;> simp only [hz, e1, e2, e3, h2]
      exacts [hY0, hY1, hYl s]
    · have e2 : τ (Sum.inr 0) = Sum.inl (σ x) := by
        rw [hτ0, splitRot_inr_one, if_neg (fun h => h2 (hσx ▸ h.2)), hσx]
      rw [coe_firstReturn_two] <;> simp only [hz, e1, e2]
      exacts [hY0, hYl _]
  · by_cases h2 : σ x = s
    · have e1 : τ (Sum.inl x) = Sum.inr 1 := by rw [hτl, splitRot_inl, if_neg h1, if_pos h2]
      by_cases hp : p = 0
      · have e2 : τ (Sum.inr 1) = Sum.inr 0 := by rw [hτ1, splitRot_inr_zero, if_pos hp]
        have e3 : τ (Sum.inr 0) = Sum.inl s := by
          rw [hτ0, splitRot_inr_one, hp]
          simp
        rw [coe_firstReturn_three] <;> simp only [hz, e1, e2, e3, h2]
        exacts [hY1, hY0, hYl s]
      · have e2 : τ (Sum.inr 1) = Sum.inl s := by rw [hτ1, splitRot_inr_zero, if_neg hp]
        rw [coe_firstReturn_two] <;> simp only [hz, e1, e2, h2]
        exacts [hY1, hYl s]
    · have e1 : τ (Sum.inl x) = Sum.inl (σ x) := by rw [hτl, splitRot_inl, if_neg h1, if_neg h2]
      rw [coe_firstReturn_of_apply_mem] <;> simp only [hz, e1]
      exact hYl _

/-- **Contracting the new edge of a splitting restores the rotation**: the rotation induced on the
old darts `H = (H ⊔ {n, n̄}) \ {n, n̄}` by the involution `ι` of the splitting, its rotation, and
the new dart `n` maps each old dart `x` to `σ(x)`. -/
@[cluster_algebras "lem_vertex_split_induced"]
theorem coe_inducedRotation_splitRot [Finite H] (x : H)
    (hx : Sum.inl x ∈ (({Sum.inr 0, splitInv ι (Sum.inr 0)} : Set (H ⊕ Fin 2))ᶜ)) :
    (inducedRotation (splitInv ι) (splitRot σ s p) (Sum.inr 0) ⟨Sum.inl x, hx⟩ : H ⊕ Fin 2) =
      Sum.inl (σ x) :=
  coe_inducedRotation_splitRot_aux ι σ s p _ rfl

/-- **Contracting the new edge of a splitting restores the rotation**, as permutations: under the
identification of the old darts `H` with `(H ⊔ {n, n̄}) \ {n, n̄}`, the induced rotation is `σ`. -/
@[cluster_algebras "lem_vertex_split_induced"]
theorem inducedRotationPerm_splitRot [Finite H] :
    inducedRotationPerm (splitInv ι) (splitRot σ s p) (Sum.inr 0) =
      (splitComplEquiv ι).permCongr σ := by
  ext z
  obtain ⟨x, rfl⟩ := (splitComplEquiv ι).surjective z
  rw [coe_inducedRotationPerm, coe_inducedRotation_splitRot_aux ι σ s p _ rfl,
    Equiv.permCongr_apply, Equiv.symm_apply_apply, coe_splitComplEquiv]

end Split

/-! ### Counting the orbits of a splitting -/

section SplitCount

variable {H : Type*} [DecidableEq H] [Finite H]

/-- A splitting has one vertex more: the rotation of a splitting has one orbit more than `σ`. -/
theorem numOrbits_splitRot (σ : Perm H) (s : H) (p : ℕ) :
    numOrbits (splitRot σ s p) = numOrbits σ + 1 := by
  have hAdef : splitRotAux σ s =
      Perm.sumCongr σ 1 * Equiv.swap (Sum.inl (σ.symm s)) (Sum.inr 1) := rfl
  have h0 : numOrbits (Perm.sumCongr σ (1 : Perm (Fin 2))) = numOrbits σ + 2 := by
    rw [numOrbits_sumCongr, numOrbits_one, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hn1 : ¬(Perm.sumCongr σ (1 : Perm (Fin 2))).SameCycle (Sum.inl (σ.symm s)) (Sum.inr 1) :=
    not_sameCycle_sumCongr_inl_inr _ _
  have h1 : numOrbits (splitRotAux σ s) = numOrbits σ + 1 := by
    rw [hAdef, numOrbits_mul_swap_of_not_sameCycle _ hn1, h0]
    omega
  have hn2 : ¬(splitRotAux σ s).SameCycle (splitAnchor σ s p) (Sum.inr 0) := fun h =>
    splitAnchor_ne_inr_zero σ s p (h.symm.eq_of_left (splitRotAux_inr_zero σ s)).symm
  have h2 : numOrbits (splitRotAux σ s * Equiv.swap (splitAnchor σ s p) (Sum.inr 0)) =
      numOrbits σ := by
    rw [numOrbits_mul_swap_of_not_sameCycle _ hn2, h1, Nat.add_sub_cancel]
  have hn3 : (splitRotAux σ s * Equiv.swap (splitAnchor σ s p) (Sum.inr 0)).SameCycle
      (Sum.inr 0) (Sum.inr 1) := by
    rw [sameCycle_mul_swap_iff _ hn2]
    refine Or.inr (Or.inr ⟨SameCycle.refl _ _, ?_⟩)
    unfold splitAnchor
    split_ifs with hp
    · exact SameCycle.refl _ _
    · have h : (splitRotAux σ s).SameCycle (Sum.inr 1) (Sum.inl s) := by
        rw [← splitRotAux_inr_one σ s]
        exact sameCycle_apply_right.2 (SameCycle.refl _ _)
      refine h.trans ?_
      rw [hAdef, sameCycle_mul_swap_iff _ hn1]
      exact Or.inl ((sameCycle_sumCongr_inl _ _).2 (sameCycle_pow_right.2 (SameCycle.refl _ _)))
  rw [splitRot, numOrbits_mul_swap_of_sameCycle _ (by simp) hn3, h2]

omit [DecidableEq H] in
/-- A splitting has one edge more: the involution of a splitting has one orbit more than `ι`. -/
theorem numOrbits_splitInv (ι : Perm H) : numOrbits (splitInv ι) = numOrbits ι + 1 := by
  rw [splitInv, numOrbits_sumCongr, numOrbits_swap_fin_two]

/-- A splitting has as many orbits of `φ` as the original: the face permutation of a splitting
has as many orbits as `σ ∘ ι`. -/
theorem numOrbits_splitRot_mul_splitInv {ι : Perm H} (hι : Involutive ι) (σ : Perm H) (s : H)
    (p : ℕ) : numOrbits (splitRot σ s p * splitInv ι) = numOrbits (σ * ι) := by
  set φ := splitRot σ s p * splitInv ι with hφdef
  have hφ : ∀ z, φ.SameCycle z (φ z) := fun z => sameCycle_apply_right.2 (SameCycle.refl _ _)
  have hφ0 : φ (Sum.inr 0) = splitRot σ s p (Sum.inr 1) := rfl
  have hφ1 : φ (Sum.inr 1) = splitRot σ s p (Sum.inr 0) := rfl
  have hY : ∀ x : H,
      Sum.inl x ∈ (({Sum.inr 0, splitInv ι (Sum.inr 0)} : Set (H ⊕ Fin 2))ᶜ) := fun x => by simp
  have two : ∀ {a b c : H ⊕ Fin 2}, φ a = b → φ b = c → φ.SameCycle a c := by
    rintro a _ _ rfl rfl
    exact (hφ a).trans (hφ _)
  have h : ∀ z, ∃ y ∈ (({Sum.inr 0, splitInv ι (Sum.inr 0)} : Set (H ⊕ Fin 2))ᶜ),
      φ.SameCycle z y := by
    rintro (x | i)
    · exact ⟨Sum.inl x, hY x, SameCycle.refl _ _⟩
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · by_cases hc : p ≠ 0 ∧ (σ ^ p) s = s
        · refine ⟨Sum.inl s, hY s, two (b := Sum.inr 1) ?_ ?_⟩
          · rw [hφ0, splitRot_inr_one, if_pos hc]
          · rw [hφ1, splitRot_inr_zero, if_neg hc.1]
        · refine ⟨Sum.inl ((σ ^ p) s), hY _, ?_⟩
          have h1 := hφ (Sum.inr 0)
          rwa [hφ0, splitRot_inr_one, if_neg hc] at h1
      · by_cases hp : p = 0
        · refine ⟨Sum.inl s, hY s, two (b := Sum.inr 0) ?_ ?_⟩
          · rw [hφ1, splitRot_inr_zero, if_pos hp]
          · rw [hφ0, splitRot_inr_one]
            simp [hp]
        · refine ⟨Sum.inl s, hY s, ?_⟩
          have h1 := hφ (Sum.inr 1)
          rwa [hφ1, splitRot_inr_zero, if_neg hp] at h1
  rw [hφdef, ← numOrbits_inducedRotationPerm_mul (splitInv_involutive hι) _ _ h]
  refine (numOrbits_of_semiconj (splitComplEquiv ι) fun x => ?_).symm
  have hsub : (splitInv ι).subtypePerm (apply_mem_compl_pair_iff (splitInv_involutive hι)
      (Sum.inr 0)) (splitComplEquiv ι x) = splitComplEquiv ι (ι x) := Subtype.ext rfl
  rw [Perm.mul_apply, Perm.mul_apply, hsub, inducedRotationPerm_splitRot, Equiv.permCongr_apply,
    Equiv.symm_apply_apply]

end SplitCount

/-! ### Splitting a vertex of a plabic graph -/

namespace PlabicData

variable {H : Type*} [DecidableEq H] {b : ℕ} (K : PlabicData H b) (s : H) (p : ℕ)

/-- The **splitting** of `K` at the vertex `z = v(s)` from `s` of size `p`, with new darts
`n = Sum.inr 0` and `n̄ = Sum.inr 1`: the dart set is `H ⊕ Fin 2`, the involution agrees with
`d ↦ d̄` on `H` and exchanges `n` and `n̄` (`splitInv`), the rotation agrees with `σ` off `z` and
consists of the cycles `(n x_1 … x_p)` and `(n̄ x_{p+1} … x_k)` on `z ⊔ {n, n̄}`, where
`x_j = σ^{j-1}(s)` and `k` is the number of darts of `z` (`splitRot`), the boundary arcs and the
legs are those of `K`, the new darts get the colour of `s`, and the old darts keep their colour.
In FWZ `z` is internal and `p ∈ [0, k]`. -/
@[cluster_algebras "def_vertex_split"]
def vertexSplit : PlabicData (H ⊕ Fin 2) b where
  inv := splitInv K.inv
  rot := splitRot K.rot s p
  bdry := K.bdry.map Embedding.inl
  colour := Sum.elim K.colour fun _ => K.colour s
  leg i := Sum.inl (K.leg i)

/-- The involution of a splitting is `splitInv` of the involution of `K`. -/
@[simp]
theorem inv_vertexSplit : (K.vertexSplit s p).inv = splitInv K.inv := rfl

/-- The rotation of a splitting is `splitRot` of the rotation of `K`. -/
@[simp]
theorem rot_vertexSplit : (K.vertexSplit s p).rot = splitRot K.rot s p := rfl

/-- The boundary arcs of a splitting are those of `K`, as old darts. -/
@[simp]
theorem bdry_vertexSplit : (K.vertexSplit s p).bdry = K.bdry.map Embedding.inl := rfl

/-- **A splitting has the same legs**: the leg `g_i` of the splitting is the leg `g_i` of `K`. -/
@[cluster_algebras "lem_vertex_split_plabic", simp]
theorem leg_vertexSplit (i : Fin b) : (K.vertexSplit s p).leg i = Sum.inl (K.leg i) := rfl

/-- In a splitting, an old dart keeps its colour. -/
@[simp]
theorem colour_vertexSplit_inl (x : H) :
    (K.vertexSplit s p).colour (Sum.inl x) = K.colour x := rfl

/-- In a splitting, the new darts have the colour of `s`. -/
@[simp]
theorem colour_vertexSplit_inr (i : Fin 2) :
    (K.vertexSplit s p).colour (Sum.inr i) = K.colour s := rfl

section Fintype

variable [Fintype H]

/-- Off the split vertex, the vertices of a splitting are those of `K`. -/
theorem vertexOf_vertexSplit_inl {x : H} (hx : ¬K.rot.SameCycle s x) :
    (K.vertexSplit s p).vertexOf (Sum.inl x) = (K.vertexOf x).map Embedding.inl := by
  ext e
  simp only [RotationSystem.mem_vertexOf, mem_map, Embedding.inl_apply, rot_vertexSplit]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [splitRot_pow_inl_of_not_sameCycle _ _ _ hx]
    exact ⟨_, sameCycle_pow_right.2 (SameCycle.refl _ _), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, rfl⟩ := hy.exists_nat_pow_eq
    rw [← splitRot_pow_inl_of_not_sameCycle _ _ p hx]
    exact sameCycle_pow_right.2 (SameCycle.refl _ _)

/-- An orbit of `φ` all of whose darts `y` have `ȳ` off the split vertex is an orbit of `φ` of the
splitting. -/
theorem faceOf_vertexSplit_inl {x : H}
    (h : ∀ y ∈ K.faceOf x, ¬K.rot.SameCycle s (K.inv y)) :
    (K.vertexSplit s p).faceOf (Sum.inl x) = (K.faceOf x).map Embedding.inl := by
  have hpow : ∀ n : ℕ, ((K.vertexSplit s p).facePerm ^ n) (Sum.inl x) =
      Sum.inl ((K.facePerm ^ n) x) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply, ih, pow_succ' K.facePerm, Perm.mul_apply,
        RotationSystem.facePerm_apply, RotationSystem.facePerm_apply, inv_vertexSplit,
        splitInv_inl, rot_vertexSplit, splitRot_inl_of_not_sameCycle]
      exact h _ (K.mem_faceOf.2 (sameCycle_pow_right.2 (SameCycle.refl _ _)))
  ext e
  simp only [RotationSystem.mem_faceOf, mem_map, Embedding.inl_apply]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [hpow]
    exact ⟨_, sameCycle_pow_right.2 (SameCycle.refl _ _), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, rfl⟩ := hy.exists_nat_pow_eq
    rw [← hpow]
    exact sameCycle_pow_right.2 (SameCycle.refl _ _)

omit [Fintype H] in
/-- A set of old darts is a boundary vertex of a splitting if and only if it is a boundary vertex
of `K`. -/
theorem isBoundaryVertex_map_inl_iff (t : Finset H) :
    (K.vertexSplit s p).IsBoundaryVertex (t.map Embedding.inl) ↔ K.IsBoundaryVertex t := by
  simp [DiskMap.IsBoundaryVertex]

omit [Fintype H] in
/-- If the split vertex is not a boundary vertex, the exterior of a splitting is that of `K`. -/
theorem exterior_vertexSplit (hzB : ∀ x ∈ K.bdry, ¬K.rot.SameCycle s x) :
    (K.vertexSplit s p).exterior = K.exterior.map Embedding.inl := by
  ext d
  rcases d with x | i
  · by_cases hx : x ∈ K.bdry
    · have : splitRot K.rot s p (Sum.inl x) = Sum.inl (K.rot x) :=
        splitRot_inl_of_not_sameCycle _ _ _ (hzB x hx)
      simp [DiskMap.mem_exterior, this, hx]
    · simp [DiskMap.mem_exterior, hx]
  · simp [DiskMap.mem_exterior]

private theorem exists_of_isBoundaryVertex_vertexSplit
    (hzB : ∀ x ∈ K.bdry, ¬K.rot.SameCycle s x) {d : H ⊕ Fin 2}
    (hd : (K.vertexSplit s p).IsBoundaryVertex ((K.vertexSplit s p).vertexOf d)) :
    ∃ x ∈ K.bdry, (K.vertexSplit s p).vertexOf d = (K.vertexOf x).map Embedding.inl := by
  obtain ⟨e, he, heB⟩ := hd
  rw [bdry_vertexSplit, mem_map] at heB
  obtain ⟨x, hx, rfl⟩ := heB
  refine ⟨x, hx, ?_⟩
  rw [← (K.vertexSplit s p).vertexOf_eq_of_mem he]
  exact vertexOf_vertexSplit_inl K s p (hzB x hx)

private theorem colour_of_sameCycle (hK : K.IsPlabicGraph)
    (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) {x : H} (hx : K.rot.SameCycle s x) :
    K.colour x = K.colour s := by
  obtain ⟨n, rfl⟩ := hx.exists_nat_pow_eq
  clear hx
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, hK.colour_rot _ ?_, ih]
    rwa [K.vertexOf_eq_of_mem ((K.mem_vertexOf).2 (sameCycle_pow_right.2 (SameCycle.refl _ _)))]

omit [Fintype H] [DecidableEq H] in
private theorem map_inl_map_splitInv (ι : Perm H) (t : Finset H) :
    (t.map Embedding.inl).map (splitInv ι).toEmbedding =
      (t.map ι.toEmbedding).map Embedding.inl := by
  rw [map_map, map_map]
  congr 1

omit [Fintype H] in
private theorem reach_inl_rot_vertexSplit [Finite H] (x : H) :
    (K.vertexSplit s p).Reach (Sum.inl x) (Sum.inl (K.rot x)) := by
  have h := coe_inducedRotation_splitRot K.inv K.rot s p x (by simp)
  rw [inducedRotation, coe_firstReturn] at h
  rw [← h]
  refine RotationSystem.reach_pow_apply _ (fun y => ?_) _ _
  rw [Perm.mul_apply]
  refine RotationSystem.Reach.rot (R := (K.vertexSplit s p).toRotationSystem) ?_
  rcases y with y | i
  · rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)]
    exact .refl _
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · rw [splitInv_inr_zero, Equiv.swap_apply_left]
      exact (RotationSystem.Reach.refl _).inv
    · rw [splitInv_inr_zero, Equiv.swap_apply_right]
      exact (RotationSystem.Reach.refl _).inv

omit [Fintype H] in
/-- If `K` is connected, so is every splitting of `K`. -/
theorem reach_vertexSplit [Finite H] (hK : K.IsConnected) (d e : H ⊕ Fin 2) :
    (K.vertexSplit s p).Reach d e := by
  have hH : ∀ x y : H, K.Reach x y → (K.vertexSplit s p).Reach (Sum.inl x) (Sum.inl y) := by
    intro x y h
    induction h with
    | refl => exact .refl _
    | rot _ ih => exact ih.trans (reach_inl_rot_vertexSplit K s p _)
    | inv _ ih => exact ih.inv
  have hs : ∀ d, (K.vertexSplit s p).Reach d (Sum.inl s) := by
    rintro (x | i)
    · exact hH x s (hK.reach x s)
    · have h01 : (K.vertexSplit s p).Reach (Sum.inr 0) (Sum.inr 1) :=
        (RotationSystem.Reach.refl _).inv
      have h10 : (K.vertexSplit s p).Reach (Sum.inr 1) (Sum.inr 0) :=
        (RotationSystem.Reach.refl _).inv
      have hr0 : (K.vertexSplit s p).Reach (Sum.inr 0)
          ((K.vertexSplit s p).rot (Sum.inr 0)) := (RotationSystem.Reach.refl _).rot
      have hr1 : (K.vertexSplit s p).Reach (Sum.inr 1)
          ((K.vertexSplit s p).rot (Sum.inr 1)) := (RotationSystem.Reach.refl _).rot
      rw [rot_vertexSplit, splitRot_inr_zero] at hr0
      rw [rot_vertexSplit, splitRot_inr_one] at hr1
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · by_cases hp : p = 0
        · subst hp
          simp only [ne_eq, not_true_eq_false, false_and, if_false, pow_zero,
            Perm.one_apply] at hr1
          exact h01.trans hr1
        · rwa [if_neg hp] at hr0
      · by_cases hp : p = 0
        · subst hp
          simpa using hr1
        · rw [if_neg hp] at hr0
          exact h10.trans hr0
  exact (hs d).trans (hs e).symm

omit [Fintype H] in
/-- If `K` is a connected rotation system, so is every splitting of `K`. -/
theorem isConnected_vertexSplit [Finite H] (hK : K.IsConnected) :
    (K.vertexSplit s p).IsConnected :=
  RotationSystem.IsConnected.of_reach ⟨Sum.inr 0⟩ (splitInv_involutive hK.inv_involutive)
    (splitInv_ne _ hK.inv_ne) (K.reach_vertexSplit s p hK)

/-- A splitting has one more vertex than `K`. -/
theorem card_vertices_vertexSplit :
    (K.vertexSplit s p).vertices.card = K.vertices.card + 1 := by
  rw [RotationSystem.card_vertices_eq_numOrbits, RotationSystem.card_vertices_eq_numOrbits]
  exact numOrbits_splitRot K.rot s p

/-- If the involution of `K` is an involution, a splitting has one more edge than `K`. -/
theorem card_edges_vertexSplit (hι : Involutive K.inv) :
    (K.vertexSplit s p).edges.card = K.edges.card + 1 := by
  rw [RotationSystem.card_edges_eq_numOrbits _ (splitInv_involutive hι),
    RotationSystem.card_edges_eq_numOrbits _ hι]
  exact numOrbits_splitInv K.inv

/-- If the involution of `K` is an involution, a splitting has as many faces as `K`. -/
theorem card_faceOrbits_vertexSplit (hι : Involutive K.inv) :
    (K.vertexSplit s p).faceOrbits.card = K.faceOrbits.card := by
  rw [RotationSystem.card_faceOrbits_eq_numOrbits, RotationSystem.card_faceOrbits_eq_numOrbits]
  exact numOrbits_splitRot_mul_splitInv hι K.rot s p

/-- **A splitting has the same boundary vertices**: if the split vertex is internal and `K` is a
plabic graph, the boundary vertex `β(i)` of the splitting consists of the darts of the boundary
vertex `β(i)` of `K`. -/
@[cluster_algebras "lem_vertex_split_plabic"]
theorem bvertex_vertexSplit (hK : K.IsPlabicGraph) (hz : ¬K.IsBoundaryVertex (K.vertexOf s))
    (i : Fin b) : (K.vertexSplit s p).bvertex i = (K.bvertex i).map Embedding.inl := by
  refine vertexOf_vertexSplit_inl K s p fun h => hz ?_
  rw [(K.vertexOf_eq_vertexOf_iff).2 h]
  exact (K.mem_boundaryVertices.1 (hK.bvertex_mem i)).2

/-- If `K` is a plabic graph and the split vertex is not a boundary vertex, the exterior of a
splitting is a face orbit splitting its boundary darts into two halves exchanged by the
involution. -/
theorem exists_orbit_vertexSplit (hK : K.IsPlabicGraph)
    (hzB : ∀ x ∈ K.bdry, ¬K.rot.SameCycle s x) :
    ∃ f ∈ (K.vertexSplit s p).faceOrbits, f ⊆ (K.vertexSplit s p).bdry ∧
      f ∪ f.map (K.vertexSplit s p).inv.toEmbedding = (K.vertexSplit s p).bdry ∧
      Disjoint f (f.map (K.vertexSplit s p).inv.toEmbedding) := by
  obtain ⟨hextO, hsub, hun, hdis⟩ := hK.exterior_spec
  obtain ⟨e0, he0, -⟩ := hK.exists_exterior ⟨0, hK.one_le⟩
  have hface : K.faceOf e0 = K.exterior := by
    obtain ⟨d0, hd0⟩ := K.mem_faceOrbits.1 hextO
    rw [← hd0] at he0 ⊢
    exact K.faceOf_eq_of_mem he0
  refine ⟨K.exterior.map Embedding.inl, ?_, map_subset_map.2 hsub, ?_, ?_⟩
  · rw [← hface, ← faceOf_vertexSplit_inl K s p]
    · exact (K.vertexSplit s p).faceOf_mem_faceOrbits _
    · intro y hy
      rw [hface] at hy
      exact hzB _ (hK.inv_mem_bdry _ (K.exterior_subset_bdry hy))
  · rw [inv_vertexSplit, map_inl_map_splitInv, ← map_union, hun, bdry_vertexSplit]
  · rw [inv_vertexSplit, map_inl_map_splitInv]
    exact (disjoint_map _).2 hdis

/-- If `K` is a plabic graph and the split vertex is internal, the colour of a splitting is
constant on its internal vertices. -/
theorem colour_rot_vertexSplit (hK : K.IsPlabicGraph) (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) :
    ∀ d, ¬(K.vertexSplit s p).IsBoundaryVertex ((K.vertexSplit s p).vertexOf d) →
      (K.vertexSplit s p).colour ((K.vertexSplit s p).rot d) = (K.vertexSplit s p).colour d := by
  intro d hd
  have hcz : ∀ x, K.rot.SameCycle s x → K.colour x = K.colour s := fun x hx =>
    colour_of_sameCycle K s hK hz hx
  rcases d with x | i
  · by_cases hx : K.rot.SameCycle s x
    · rw [colour_vertexSplit_inl, hcz x hx, rot_vertexSplit, splitRot_inl]
      split_ifs
      · rfl
      · rfl
      · exact hcz _ (hx.trans (sameCycle_apply_right.2 (SameCycle.refl _ _)))
    · have hint : ¬K.IsBoundaryVertex (K.vertexOf x) := fun hb => hd (by
        rwa [vertexOf_vertexSplit_inl K s p hx, isBoundaryVertex_map_inl_iff])
      rw [rot_vertexSplit, splitRot_inl_of_not_sameCycle _ _ _ hx, colour_vertexSplit_inl,
        colour_vertexSplit_inl, hK.colour_rot x hint]
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · rw [rot_vertexSplit, splitRot_inr_zero]
      split_ifs <;> rfl
    · rw [rot_vertexSplit, splitRot_inr_one]
      split_ifs
      · rfl
      · exact hcz _ (sameCycle_pow_right.2 (SameCycle.refl _ _))

/-- If `K` is a plabic graph and the split vertex is internal, every boundary vertex of a
splitting has three darts, two of them boundary darts. -/
theorem boundaryVertex_card_vertexSplit (hK : K.IsPlabicGraph)
    (hzB : ∀ x ∈ K.bdry, ¬K.rot.SameCycle s x) :
    ∀ v ∈ (K.vertexSplit s p).boundaryVertices,
      v.card = 3 ∧ (v.filter (· ∈ (K.vertexSplit s p).bdry)).card = 2 := by
  intro v hv
  obtain ⟨hvV, hvB⟩ := (K.vertexSplit s p).mem_boundaryVertices.1 hv
  obtain ⟨d, rfl⟩ := (K.vertexSplit s p).mem_vertices.1 hvV
  obtain ⟨x, hx, hxv⟩ := exists_of_isBoundaryVertex_vertexSplit K s p hzB hvB
  rw [hxv]
  obtain ⟨h3, h2⟩ := hK.boundaryVertex_card _
    (K.vertexOf_mem_boundaryVertices.2 (K.isBoundaryVertex_vertexOf_of_mem hx))
  refine ⟨by rw [card_map, h3], ?_⟩
  rw [filter_map, card_map]
  refine Eq.trans ?_ h2
  congr 1
  ext y
  simp

/-- **A splitting is a plabic graph**: the splitting of a plabic graph `K` at an internal vertex
`z = v(s)` from `s`, of any size `p`, is a plabic graph. Its boundary vertices and legs are those
of `K` (`bvertex_vertexSplit`, `leg_vertexSplit`). -/
@[cluster_algebras "lem_vertex_split_plabic"]
theorem IsPlabicGraph.vertexSplit {K : PlabicData H b} (hK : K.IsPlabicGraph) {s : H}
    (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) (p : ℕ) : (K.vertexSplit s p).IsPlabicGraph := by
  have hzB : ∀ x ∈ K.bdry, ¬K.rot.SameCycle s x := fun x hx h =>
    hz ⟨x, K.mem_vertexOf.2 h, hx⟩
  have hbv := bvertex_vertexSplit K s p hK hz
  refine
    { toIsDiskMap :=
        { toIsConnected := isConnected_vertexSplit K s p hK.toIsConnected
          inv_mem_bdry := ?_
          euler := ?_
          boundaryVertex_card := boundaryVertex_card_vertexSplit K s p hK hzB
          exists_orbit := exists_orbit_vertexSplit K s p hK hzB }
      one_le := hK.one_le
      colour_rot := colour_rot_vertexSplit K s p hK hz
      leg_notMem_bdry := fun i => by simpa using hK.leg_notMem_bdry i
      bvertex_mem := ?_
      bvertex_injective := ?_
      exists_bvertex_eq := ?_
      exists_exterior := ?_ }
  · intro d hd
    rw [bdry_vertexSplit, mem_map] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact mem_map_of_mem _ (hK.inv_mem_bdry x hx)
  · rw [card_vertices_vertexSplit, card_edges_vertexSplit _ _ _ hK.inv_involutive,
      card_faceOrbits_vertexSplit _ _ _ hK.inv_involutive]
    push_cast
    linarith [hK.euler]
  · intro i
    refine (K.vertexSplit s p).mem_boundaryVertices.2
      ⟨(K.vertexSplit s p).vertexOf_mem_vertices _, ?_⟩
    rw [hbv, isBoundaryVertex_map_inl_iff]
    exact (K.mem_boundaryVertices.1 (hK.bvertex_mem i)).2
  · intro i j h
    rw [hbv, hbv] at h
    exact hK.bvertex_injective (map_injective _ h)
  · intro v hv
    obtain ⟨hvV, hvB⟩ := (K.vertexSplit s p).mem_boundaryVertices.1 hv
    obtain ⟨d, rfl⟩ := (K.vertexSplit s p).mem_vertices.1 hvV
    obtain ⟨x, hx, hxv⟩ := exists_of_isBoundaryVertex_vertexSplit K s p hzB hvB
    obtain ⟨i, hi⟩ := hK.exists_bvertex_eq _
      (K.vertexOf_mem_boundaryVertices.2 (K.isBoundaryVertex_vertexOf_of_mem hx))
    exact ⟨i, by rw [hbv, hi, hxv]⟩
  · intro i
    obtain ⟨d, hd, h1, h2⟩ := hK.exists_exterior i
    refine ⟨Sum.inl d, ?_, ?_, ?_⟩
    · rw [exterior_vertexSplit K s p hzB]
      exact mem_map_of_mem _ hd
    · rw [hbv]
      exact mem_map_of_mem _ h1
    · rw [hbv]
      exact mem_map_of_mem _ h2

end Fintype

end PlabicData

/-! ### The flip move -/

section Flip

variable {H : Type*} [DecidableEq H]

/-- The **rotation of a flip** at the dart `d`: writing `d̄ = ι d`, `a₁ = σ d`, `a₂ = σ² d`,
`b₁ = σ d̄` and `b₂ = σ² d̄`, it is `σ ∘ (d a₁ b₂)(a₂ d̄ b₁)`. When the vertices `x = (d a₁ a₂)`
and `y = (d̄ b₁ b₂)` are distinct and trivalent, it agrees with `σ` off `x ∪ y` and consists of
the cycles `(d a₂ b₁)` and `(d̄ b₂ a₁)` on `x ∪ y` (`PlabicData.IsFlipEdge.flipRot_apply_self` and
its companions). -/
def flipRot (σ ι : Perm H) (d : H) : Perm H :=
  σ * (Equiv.swap d (σ d) * Equiv.swap (σ d) ((σ ^ 2) (ι d)) *
    (Equiv.swap ((σ ^ 2) d) (ι d) * Equiv.swap (ι d) (σ (ι d))))

/-- The values of the rotation of a flip, given that the six darts are distinct and the two
vertices are `3`-cycles. -/
private theorem flipRot_spec {σ ι : Perm H} {d : H} (h3 : σ (σ (σ d)) = d)
    (h3' : σ (σ (σ (ι d))) = ι d)
    (n1 : d ≠ σ d) (n2 : d ≠ σ (σ d)) (n3 : σ d ≠ σ (σ d))
    (m1 : ι d ≠ σ (ι d)) (m2 : ι d ≠ σ (σ (ι d))) (m3 : σ (ι d) ≠ σ (σ (ι d)))
    (c00 : d ≠ ι d) (c01 : d ≠ σ (ι d)) (c02 : d ≠ σ (σ (ι d)))
    (c10 : σ d ≠ ι d) (c11 : σ d ≠ σ (ι d)) (c12 : σ d ≠ σ (σ (ι d)))
    (c20 : σ (σ d) ≠ ι d) (c21 : σ (σ d) ≠ σ (ι d)) (c22 : σ (σ d) ≠ σ (σ (ι d))) :
    flipRot σ ι d d = σ (σ d) ∧ flipRot σ ι d (σ (σ d)) = σ (ι d) ∧
      flipRot σ ι d (σ (ι d)) = d ∧ flipRot σ ι d (ι d) = σ (σ (ι d)) ∧
      flipRot σ ι d (σ (σ (ι d))) = σ d ∧ flipRot σ ι d (σ d) = ι d ∧
      ∀ e, e ≠ d → e ≠ σ d → e ≠ σ (σ d) → e ≠ ι d → e ≠ σ (ι d) → e ≠ σ (σ (ι d)) →
        flipRot σ ι d e = σ e := by
  simp only [flipRot, pow_two, Perm.mul_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun e e1 e2 e3 e4 e5 e6 => ?_⟩ <;>
    simp [Equiv.swap_apply_def, n2.symm, n3.symm, m1.symm, m2.symm, m3.symm, c00.symm, c01.symm,
      c02.symm, c10.symm, c11.symm, c12.symm, c21.symm, c22.symm, *]

end Flip

section ThreeCycle

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- An orbit with three elements is a `3`-cycle `(x σx σ²x)`. -/
private theorem three_cycle {σ : Perm H} {x : H}
    (h : ({y | σ.SameCycle x y} : Finset H).card = 3) :
    σ (σ (σ x)) = x ∧ x ≠ σ x ∧ x ≠ σ (σ x) ∧ σ x ≠ σ (σ x) := by
  have hp : ∀ i : ℕ, (σ ^ i) x = σ^[i] x := fun i => (congrFun (Perm.iterate_eq_pow σ i) x).symm
  have h3 := pow_card_sameCycle_apply σ x
  rw [h, hp] at h3
  have hne : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → σ^[i] x ≠ σ^[j] x := fun i j hi hj hij e =>
    hij (eq_of_pow_apply_eq σ x (by omega) (by omega) (by rwa [hp, hp]))
  exact ⟨h3, hne 0 1 (by norm_num) (by norm_num) (by norm_num),
    hne 0 2 (by norm_num) (by norm_num) (by norm_num),
    hne 1 2 (by norm_num) (by norm_num) (by norm_num)⟩

end ThreeCycle

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b) (d : H)

/-- The conditions of the **flip move** (M4) at the edge `{d, d̄}`: its endpoints `x = v(d)` and
`y = v(d̄)` are distinct internal vertices of the same colour, each consisting of exactly three
darts. -/
@[cluster_algebras "def_flip_move"]
structure IsFlipEdge : Prop where
  /-- The endpoints are distinct. -/
  vertexOf_ne : G.vertexOf d ≠ G.vertexOf (G.inv d)
  /-- `x = v(d)` is internal. -/
  not_isBoundaryVertex : ¬G.IsBoundaryVertex (G.vertexOf d)
  /-- `y = v(d̄)` is internal. -/
  not_isBoundaryVertex_inv : ¬G.IsBoundaryVertex (G.vertexOf (G.inv d))
  /-- The endpoints have the same colour. -/
  colour_inv : G.colour (G.inv d) = G.colour d
  /-- `x` has three darts. -/
  card_vertexOf : (G.vertexOf d).card = 3
  /-- `y` has three darts. -/
  card_vertexOf_inv : (G.vertexOf (G.inv d)).card = 3

/-- The **flip** of `G` at the edge `{d, d̄}`: with `a₁ = σ d`, `a₂ = σ² d`, `b₁ = σ d̄`,
`b₂ = σ² d̄`, the rotation agrees with `σ` outside `x ∪ y` and consists of the cycles `(d a₂ b₁)`
and `(d̄ b₂ a₁)` on `x ∪ y` (`flipRot`); the darts of `x ∪ y` get the colour of `d`, the common
colour of `x` and `y`, and the involution, the boundary arcs, the other colours and the legs are
those of `G`. The conditions on the edge are `IsFlipEdge`. -/
@[cluster_algebras "def_flip_move"]
def flipMove : PlabicData H b where
  inv := G.inv
  rot := flipRot G.rot G.inv d
  bdry := G.bdry
  colour e := if e ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) then G.colour d else G.colour e
  leg := G.leg

/-- The involution of a flip is that of `G`. -/
@[simp]
theorem inv_flipMove : (G.flipMove d).inv = G.inv := rfl

/-- The rotation of a flip is `flipRot`. -/
@[simp]
theorem rot_flipMove : (G.flipMove d).rot = flipRot G.rot G.inv d := rfl

/-- The boundary arcs of a flip are those of `G`. -/
@[simp]
theorem bdry_flipMove : (G.flipMove d).bdry = G.bdry := rfl

/-- The legs of a flip are those of `G`. -/
@[simp]
theorem leg_flipMove : (G.flipMove d).leg = G.leg := rfl

/-- In a flip, the darts of `x ∪ y` get the colour of `d` and the other darts keep their
colour. -/
theorem colour_flipMove (e : H) : (G.flipMove d).colour e =
    if e ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) then G.colour d else G.colour e := rfl

namespace IsFlipEdge

variable {G d} (hf : G.IsFlipEdge d)

include hf

private theorem spec :
    flipRot G.rot G.inv d d = G.rot (G.rot d) ∧
      flipRot G.rot G.inv d (G.rot (G.rot d)) = G.rot (G.inv d) ∧
      flipRot G.rot G.inv d (G.rot (G.inv d)) = d ∧
      flipRot G.rot G.inv d (G.inv d) = G.rot (G.rot (G.inv d)) ∧
      flipRot G.rot G.inv d (G.rot (G.rot (G.inv d))) = G.rot d ∧
      flipRot G.rot G.inv d (G.rot d) = G.inv d ∧
      ∀ e, e ∉ G.vertexOf d → e ∉ G.vertexOf (G.inv d) →
        flipRot G.rot G.inv d e = G.rot e := by
  obtain ⟨h3, n1, n2, n3⟩ := three_cycle hf.card_vertexOf
  obtain ⟨h3', m1, m2, m3⟩ := three_cycle hf.card_vertexOf_inv
  have hx : ∀ i : ℕ, G.rot.SameCycle d (G.rot^[i] d) := fun i => by
    rw [Perm.iterate_eq_pow]
    exact sameCycle_pow_right.2 (SameCycle.refl _ _)
  have hy : ∀ i : ℕ, G.rot.SameCycle (G.inv d) (G.rot^[i] (G.inv d)) := fun i => by
    rw [Perm.iterate_eq_pow]
    exact sameCycle_pow_right.2 (SameCycle.refl _ _)
  have hc : ∀ i j : ℕ, G.rot^[i] d ≠ G.rot^[j] (G.inv d) := fun i j e =>
    hf.vertexOf_ne ((G.vertexOf_eq_vertexOf_iff).2 ((hx i).trans (e ▸ (hy j).symm)))
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := flipRot_spec (ι := G.inv) h3 h3' n1 n2 n3 m1 m2 m3
    (hc 0 0) (hc 0 1) (hc 0 2) (hc 1 0) (hc 1 1) (hc 1 2) (hc 2 0) (hc 2 1) (hc 2 2)
  refine ⟨r1, r2, r3, r4, r5, r6, fun e hex hey => r7 e ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
    rintro rfl
  · exact hex (G.self_mem_vertexOf _)
  · exact hex (G.rot_mem_vertexOf _)
  · exact hex (G.mem_vertexOf.2 (hx 2))
  · exact hey (G.self_mem_vertexOf _)
  · exact hey (G.rot_mem_vertexOf _)
  · exact hey (G.mem_vertexOf.2 (hy 2))

/-- The flip maps `d` to `a₂ = σ² d`. -/
theorem flipRot_apply_self : flipRot G.rot G.inv d d = G.rot (G.rot d) := hf.spec.1

/-- The flip maps `a₂ = σ² d` to `b₁ = σ d̄`. -/
theorem flipRot_apply_rot_rot : flipRot G.rot G.inv d (G.rot (G.rot d)) = G.rot (G.inv d) :=
  hf.spec.2.1

/-- The flip maps `b₁ = σ d̄` to `d`. -/
theorem flipRot_apply_rot_inv : flipRot G.rot G.inv d (G.rot (G.inv d)) = d := hf.spec.2.2.1

/-- The flip maps `d̄` to `b₂ = σ² d̄`. -/
theorem flipRot_apply_inv : flipRot G.rot G.inv d (G.inv d) = G.rot (G.rot (G.inv d)) :=
  hf.spec.2.2.2.1

/-- The flip maps `b₂ = σ² d̄` to `a₁ = σ d`. -/
theorem flipRot_apply_rot_rot_inv :
    flipRot G.rot G.inv d (G.rot (G.rot (G.inv d))) = G.rot d := hf.spec.2.2.2.2.1

/-- The flip maps `a₁ = σ d` to `d̄`. -/
theorem flipRot_apply_rot : flipRot G.rot G.inv d (G.rot d) = G.inv d := hf.spec.2.2.2.2.2.1

/-- The flip agrees with `σ` outside `x ∪ y`. -/
theorem flipRot_apply_of_notMem {e : H} (hex : e ∉ G.vertexOf d)
    (hey : e ∉ G.vertexOf (G.inv d)) : flipRot G.rot G.inv d e = G.rot e :=
  hf.spec.2.2.2.2.2.2 e hex hey

end IsFlipEdge

end PlabicData

end ClusterAlgebras

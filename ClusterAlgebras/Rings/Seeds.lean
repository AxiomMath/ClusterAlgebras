/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.Defs
public import ClusterAlgebras.Seed
public import ClusterAlgebras.ExchangeMatrix
public import ClusterAlgebras.WiringDiagram.Chamber

/-!
# Seeds of wiring diagrams and rectangles seeds

This file defines the seed `Σ(D, λ)` of a wiring diagram, whose entries are the chamber minors, its
image `Σ_SL(D, λ)` in `ℂ[SL_k]`, the rectangles quiver `Q_{a,b}`, the labels `J(v)` of its
vertices, and the rectangles seed `Σ_{a,b}(λ)` with its cyclic shifts `Σ^i_{a,b}(λ)`.

## Main definitions

* `ClusterAlgebras.wiringSeed`: the seed `Σ(D, λ)` of a wiring diagram with a chamber labelling.
* `ClusterAlgebras.slWiringSeed`: the seed `Σ_SL(D, λ)` in `ℂ[SL_k]`.
* `ClusterAlgebras.rectArrows`: the arrow function of the rectangles quiver `Q_{a,b}`.
* `ClusterAlgebras.rectLabel`: the label `J(v)` of a vertex of `Q_{a,b}`.
* `ClusterAlgebras.RectangleLabelling`: a labelling of the vertices of `Q_{a,b}`.
* `ClusterAlgebras.rectanglesSeedShift`: the cyclic shift `Σ^i_{a,b}(λ)` of the rectangles seed.
* `ClusterAlgebras.rectanglesSeed`: the rectangles seed `Σ_{a,b}(λ)`.

## Implementation notes

* **Seeds whose entries lie in a polynomial ring are read in its fraction field.** The seeds
  `Σ(D, λ)` and `Σ^i_{a,b}(λ)` are tuples of elements of `ℂ[z]`; here they are tuples of elements
  of `ℂ(z) = FractionRing ℂ[z]` (the images of those polynomials), so that seed mutation, which
  divides, applies to them. That they are labeled seeds in the subfield their entries generate is
  `IsLabeledSeed ℂ hmn (S.adjoinSelf ℂ)` (`ClusterAlgebras.Rings.Basic`). The seed `Σ_SL(D, λ)` is
  a tuple of elements of the ring `ℂ[SL_k]`; its fraction field only exists once `ℂ[SL_k]` is
  known to be a domain.
* A wiring diagram of `WiringDiagram n'` has `n' + 2` strands, so the generic matrix is
  `(n' + 2) × (n' + 2)`. A **chamber labelling** is a `Labelling` of the quiver `Q(D)`: its frozen
  vertices are the unbounded chambers, so the two notions coincide.
* The rectangles quiver has vertex type `Option (Fin a × Fin (b - a))`: `some (p, q)` is the
  `(p + 1) × (q + 1)` rectangle and `none` the empty one. A **rectangle labelling** is defined
  directly from the frozen set and not from the bundled `Quiver`, whose axioms are
  `ClusterAlgebras.isArrowSystem_rectArrows` and `ClusterAlgebras.twoCycleFree_rectArrows`.
* The sizes `m` and `n` of a labelling are parameters, as for `Labelling`; a bijection
  `Fin m ≃ V_{a,b}` under which exactly the first `n` indices are mutable forces
  `m = a(b - a) + 1` and `n = (a - 1)(b - a - 1)`.
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### The seed of a wiring diagram -/

section Wiring

variable {n' m n : ℕ}

/-- The **seed of a wiring diagram** `Σ(D, λ) = (x̃(D, λ), B̃(D, λ))` for a chamber labelling `λ`:
the entry in position `i` is the chamber minor `P_{J(λ(i))}(z)` of the generic `(n'+2) × (n'+2)`
matrix over `ℂ`, read in `ℂ(z)`, and the matrix is `B̃(Q(D), λ)`, with entries the signed counts
`β(λ(i), λ(j))` of the arrows of `Q(D)`. -/
@[cluster_algebras "def_wiring_seed"]
noncomputable def wiringSeed (D : WiringDiagram n') (L : Labelling D.wiringQuiver m n) :
    SeedData (FractionRing (ComplexPoly (n' + 2) (n' + 2))) m n where
  extCluster i := algebraMap _ _
    (flagMinor (complexGenericMatrix (n' + 2) (n' + 2)) (L.equiv i).chamberSet)
  extExchangeMatrix := extExchangeMatrix D.wiringQuiver L

/-- The **seed of a wiring diagram on `SL_k`**: the tuple of the images `π(P_{J(λ(i))}(z))` of the
chamber minors in `ℂ[SL_k]`, `k = n' + 2`, and the matrix `B̃(D, λ)`. -/
@[cluster_algebras "def_sl_wiring_seed"]
noncomputable def slWiringSeed (D : WiringDiagram n') (L : Labelling D.wiringQuiver m n) :
    SeedData (SLCoord (n' + 2)) m n where
  extCluster i := slQuot (n' + 2)
    (flagMinor (complexGenericMatrix (n' + 2) (n' + 2)) (L.equiv i).chamberSet)
  extExchangeMatrix := extExchangeMatrix D.wiringQuiver L

end Wiring

/-! ### The rectangles quiver -/

section Rectangles

/-- The vertex set `V_{a,b}` of the rectangles quiver: `some (p, q)` is the `(p + 1) × (q + 1)`
rectangle, `p < a`, `q < b - a`, and `none` is the empty rectangle `∅`. -/
@[cluster_algebras "def_rectangles_quiver"]
abbrev RectVertex (a b : ℕ) : Type := Option (Fin a × Fin (b - a))

/-- The frozen set `F_{a,b}`: the empty rectangle and the rectangles of full height `a` or full
width `b - a`. -/
@[cluster_algebras "def_rectangles_quiver"]
def RectFrozen (a b : ℕ) : RectVertex a b → Prop
  | none => True
  | some (p, q) => (p : ℕ) + 1 = a ∨ (q : ℕ) + 1 = b - a

/-- Membership in the frozen set `F_{a,b}` is decidable. -/
instance (a b : ℕ) : DecidablePred (RectFrozen a b) := by
  rintro (_ | ⟨p, q⟩) <;> unfold RectFrozen <;> infer_instance

/-- The steps of the rectangles quiver, before arrows between two frozen vertices are removed:
`(p, q) → (p, q + 1)`, `(p, q) → (p + 1, q)`, `(p, q) → (p - 1, q - 1)`, and `∅ → (1, 1)`
(1-based; `some (0, 0)` here). -/
@[cluster_algebras "def_rectangles_quiver"]
def RectStep (a b : ℕ) : RectVertex a b → RectVertex a b → Prop
  | some (p, q), some (p', q') => ((p' : ℕ) = p ∧ (q' : ℕ) = q + 1) ∨
      ((p' : ℕ) = p + 1 ∧ (q' : ℕ) = q) ∨ ((p' : ℕ) + 1 = p ∧ (q' : ℕ) + 1 = q)
  | none, some (p', q') => (p' : ℕ) = 0 ∧ (q' : ℕ) = 0
  | _, none => False

/-- Whether `v → w` is a step of the rectangles quiver is decidable. -/
instance (a b : ℕ) (v w : RectVertex a b) : Decidable (RectStep a b v w) := by
  rcases v with _ | ⟨p, q⟩ <;> rcases w with _ | ⟨p', q'⟩ <;> unfold RectStep <;> infer_instance

/-- The arrow function `α` of the **rectangles quiver** `Q_{a,b}`: `α(v, w) = 1` exactly when `v`
and `w` are not both frozen and `v → w` is a step, and `0` otherwise. -/
@[cluster_algebras "def_rectangles_quiver"]
def rectArrows (a b : ℕ) (v w : RectVertex a b) : ℕ :=
  if ¬(RectFrozen a b v ∧ RectFrozen a b w) ∧ RectStep a b v w then 1 else 0

/-- The **label** `J(v) ⊆ [1, b]` of a vertex of `Q_{a,b}`, with `c = b - a`:
`J(p, q) = [c - q + 1, c - q + p] ∪ [c + p + 1, b]` and `J(∅) = [c + 1, b]` (1-based). With the
0-based columns and rectangles used here, column `x` lies in the label of `some (p, q)` when
`c ≤ x + q + 1 ≤ c + p` or `c + p + 1 ≤ x`, and in that of `none` when `c ≤ x`. -/
@[cluster_algebras "def_rectangle_label"]
def rectLabel (a b : ℕ) : RectVertex a b → Finset (Fin b)
  | none => Finset.univ.filter fun x => b - a ≤ (x : ℕ)
  | some (p, q) => Finset.univ.filter fun x =>
      (b - a ≤ (x : ℕ) + q + 1 ∧ (x : ℕ) + q + 1 ≤ b - a + p) ∨ b - a + p + 1 ≤ (x : ℕ)

/-- A **rectangle labelling**: a bijection `λ : [1, m] → V_{a,b}` under which `λ(i)` is mutable
exactly when `i ∈ [1, n]`. -/
@[cluster_algebras "def_rectangles_seed"]
structure RectangleLabelling (a b m n : ℕ) where
  /-- The bijection `λ`. -/
  equiv : Fin m ≃ RectVertex a b
  /-- The mutable indices form an initial segment. -/
  le : n ≤ m
  /-- A vertex is frozen exactly when its index is at least `n`. -/
  frozen_iff : ∀ i : Fin m, RectFrozen a b (equiv i) ↔ n ≤ (i : ℕ)

/-- The **cyclic shift** `Σ^i_{a,b}(λ)` of the rectangles seed: the entry in position `ℓ` is the
Plücker coordinate `P_{(J(λ(ℓ)) + i) mod b}` of the generic `a × b` matrix over `ℂ`, read in
`ℂ(z)`, and the matrix has `(ℓ, ℓ')` entry `β(λ(ℓ), λ(ℓ'))`, the signed count of `α`. -/
@[cluster_algebras "def_rectangles_seed"]
noncomputable def rectanglesSeedShift {a b m n : ℕ} (L : RectangleLabelling a b m n) (i : ℤ) :
    SeedData (FractionRing (ComplexPoly a b)) m n where
  extCluster ℓ := algebraMap _ _
    (pluckerCoord (complexGenericMatrix a b) (cyclicShift i (rectLabel a b (L.equiv ℓ))))
  extExchangeMatrix := Matrix.of fun ℓ ℓ' =>
    signedCount (rectArrows a b) (L.equiv ℓ) (L.equiv (Fin.castLE L.le ℓ'))

/-- The **rectangles seed** `Σ_{a,b}(λ) = Σ^0_{a,b}(λ)`. -/
@[cluster_algebras "def_rectangles_seed"]
noncomputable def rectanglesSeed {a b m n : ℕ} (L : RectangleLabelling a b m n) :
    SeedData (FractionRing (ComplexPoly a b)) m n :=
  rectanglesSeedShift L 0

/-- The order of the mutable vertices in the cyclic shift mutation sequence: `p` decreasing from
`a - 1` to `1` and, for each `p`, `q` increasing from `1` to `b - a - 1` (1-based; `some (p, q)`
with `p` from `a - 2` down to `0` and `q` from `0` up to `b - a - 2` here). -/
@[cluster_algebras "lem_cyclic_shift_mutation"]
def cyclicShiftOrder (a b : ℕ) : List (RectVertex a b) :=
  ((List.finRange a).reverse.filter fun p : Fin a => (p : ℕ) + 1 < a).flatMap fun p =>
    ((List.finRange (b - a)).filter fun q : Fin (b - a) => (q : ℕ) + 1 < b - a).map fun q =>
      some (p, q)

end Rectangles

end ClusterAlgebras

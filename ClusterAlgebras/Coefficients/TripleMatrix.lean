/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Tropical.TriplePattern

/-!
# The seed of a triple, and mutation of labeled seed triples

A labeled seed triple `(x, y, B)` of rank `n`, with frozen variables `x_{n+1}, …, x_m`, comes
from a labeled seed. Its *extended matrix* `B̃(y, B)` is the `m × n` integer matrix whose first
`n` rows are those of `B` and whose `(i, j)` entry for `i > n` is the exponent of `qᵢ` in `yⱼ`.
The principal part of `B̃(y, B)` is `B` and its coefficient tuple is `y`, so the seed
`(x̃, B̃(y, B))`, with `x̃ = (x₁, …, xₙ, x_{n+1}, …, x_m)`, is a labeled seed whose triple is
`(x, y, B)`. Since seed mutation and mutation of triples agree, and seed mutation preserves
labeled seeds and frozen variables, the mutation of a labeled seed triple is a labeled seed
triple with the same frozen variables.

The file also records the *monomial evaluation* `ε_e : Trop(qᵢ) → Eˣ`,
`∏ᵢ qᵢ ^ aᵢ ↦ ∏ᵢ eᵢ ^ aᵢ`, at nonzero elements `eᵢ` of a field `E`. The map `ε` of mutation of
triples is the monomial evaluation at the frozen variables (`coe_monomialEvaluation`).
Finally, a pattern of triples is determined by its triple at one vertex, and a seed by its
triple and its frozen variables.

## Main definitions

* `ClusterAlgebras.TropicalSemifield.lift`: the group homomorphism out of `Trop(qᵢ : i ∈ ι)`
  sending `qᵢ` to a prescribed element `uᵢ` of a commutative group.
* `ClusterAlgebras.monomialEvaluation`: the monomial evaluation `ε_e`.
* `ClusterAlgebras.tripleExtendedMatrix`: the extended matrix `B̃(y, B)` of a triple.
* `ClusterAlgebras.SeedTriple.toSeedData`: the seed `(x̃, B̃(y, B))` of a triple.

## Main results

* `ClusterAlgebras.coe_monomialEvaluation`: `ε_e` is `tropicalEval e`, followed by the
  inclusion `Eˣ → E`.
* `ClusterAlgebras.principalPart_tripleExtendedMatrix`,
  `ClusterAlgebras.coefficientTuple_tripleExtendedMatrix`: the principal part of `B̃(y, B)` is
  `B` and its coefficient tuple is `y`.
* `ClusterAlgebras.SeedTriple.toSeedTriple_toSeedData`: the triple of the seed of a triple is
  the triple itself.
* `ClusterAlgebras.IsSeedTriple.mutation`: the mutation of a labeled seed triple is a labeled
  seed triple with the same frozen variables.
* `ClusterAlgebras.IsTriplePattern.eq_of_apply_eq`: a pattern of triples is determined by its
  triple at one vertex.
* `ClusterAlgebras.SeedData.eq_of_toSeedTriple_eq` (proved in the library, tagged here): a seed
  is determined by its triple and its frozen variables.

## Implementation notes

* FWZ index the variables of the tropical semifield of `monomialEvaluation` by
  `[n+1, ℓ]`. The definition is made for any finite index type `ι`, which covers
  `FrozenIndex ℓ n`; it is the field case of `TropicalSemifield.lift`, the universal property
  of `Trop(qᵢ : i ∈ ι)` as the free abelian group on the `qᵢ`.
* FWZ require `m ≥ n ≥ 1` for `B̃(y, B)`. The matrix is defined for all `m` and `n`;
  `n ≤ m` enters only where its principal part is taken.
* A pattern of triples is determined by one triple using only that mutation of triples with
  given frozen variables is a function of the triple; the hypothesis that the triples are
  labeled seed triples is not used. `IsTriplePattern.eq_of_apply_eq` is stated in FWZ's
  form and is the case of `RegularTree.eq_of_apply_eq_of_adj`, which assumes only the edge
  condition for an arbitrary rule `f k` on an arbitrary type.
* Fomin–Williams–Zelevinsky's statement that a labeled seed is determined by its triple, for
  labeled seeds with the same frozen variables, is the library's
  `SeedData.eq_of_toSeedTriple_eq`, which holds for all seed data: it is tagged, not restated.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras, Chapter 4*,
  Section 4.3.
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### Monomial evaluation -/

namespace TropicalSemifield

variable {ι G : Type*} [Fintype ι] [CommGroup G]

/-- The group homomorphism `Trop(qᵢ : i ∈ ι) → G`, `∏ᵢ qᵢ ^ aᵢ ↦ ∏ᵢ uᵢ ^ aᵢ`, into a commutative
group `G`: the unique one sending each generator `qᵢ` to `uᵢ`. -/
def lift (u : ι → G) : TropicalSemifield ι →* G where
  toFun y := ∏ i, u i ^ exponent y i
  map_one' := by simp
  map_mul' y y' := by simp [zpow_add, Finset.prod_mul_distrib]

/-- The value of `lift u` at `∏ᵢ qᵢ ^ aᵢ` is `∏ᵢ uᵢ ^ aᵢ`. -/
theorem lift_apply (u : ι → G) (y : TropicalSemifield ι) :
    lift u y = ∏ i, u i ^ exponent y i :=
  rfl

/-- The value of `lift u` at the monomial with exponent vector `a` is `∏ᵢ uᵢ ^ aᵢ`. -/
@[simp]
theorem lift_monomial (u : ι → G) (a : ι → ℤ) : lift u (monomial a) = ∏ i, u i ^ a i :=
  rfl

/-- `lift u` sends the generator `qᵢ` to `uᵢ`. -/
@[simp]
theorem lift_q [DecidableEq ι] (u : ι → G) (i : ι) : lift u (q i) = u i := by
  rw [lift_apply, Finset.prod_eq_single i (fun j _ hj => by simp [hj])
    (by simp)]
  simp

omit [Fintype ι] in
/-- Two group homomorphisms out of `Trop(qᵢ : i ∈ ι)`, for a finite index type `ι`, that agree
on every generator `qᵢ` are equal. -/
theorem hom_ext [Finite ι] [DecidableEq ι] {f g : TropicalSemifield ι →* G}
    (h : ∀ i, f (q i) = g (q i)) : f = g := by
  have := Fintype.ofFinite ι
  ext y
  rw [← prod_q_zpow y]
  simp [map_prod, map_zpow, h]

/-- Every group homomorphism out of `Trop(qᵢ : i ∈ ι)` is the lift of its values on the
generators. -/
theorem lift_comp_q [DecidableEq ι] (f : TropicalSemifield ι →* G) : lift (fun i => f (q i)) = f :=
  hom_ext fun i => lift_q _ i

end TropicalSemifield

variable {E : Type*} [Field E] {ι : Type*} [Fintype ι]

/-- The **monomial evaluation** at nonzero elements `eᵢ` of a field `E`: the group homomorphism
`ε_e : Trop(qᵢ : i ∈ ι) → Eˣ` with `ε_e(∏ᵢ qᵢ ^ aᵢ) = ∏ᵢ eᵢ ^ aᵢ`. FWZ take
`ι = [n+1, ℓ]`; any finite index type is allowed. -/
@[cluster_algebras "def_monomial_evaluation"]
def monomialEvaluation (e : ι → E) (he : ∀ i, e i ≠ 0) : TropicalSemifield ι →* Eˣ :=
  TropicalSemifield.lift fun i => Units.mk0 (e i) (he i)

/-- The monomial evaluation, followed by the inclusion `Eˣ → E`, is `tropicalEval e`. In
particular the map `ε` of mutation of triples is the monomial evaluation at the frozen
variables. -/
@[simp]
theorem coe_monomialEvaluation (e : ι → E) (he : ∀ i, e i ≠ 0) (y : TropicalSemifield ι) :
    (monomialEvaluation e he y : E) = tropicalEval e y := by
  simp [monomialEvaluation, TropicalSemifield.lift_apply, tropicalEval]

/-- The value of `ε_e(∏ᵢ qᵢ ^ aᵢ)` in `E` is `∏ᵢ eᵢ ^ aᵢ`. -/
@[simp]
theorem coe_monomialEvaluation_monomial (e : ι → E) (he : ∀ i, e i ≠ 0) (a : ι → ℤ) :
    (monomialEvaluation e he (TropicalSemifield.monomial a) : E) = ∏ i, e i ^ a i := by
  simp [tropicalEval]

/-- `ε_e(qᵢ) = eᵢ`, as a unit. -/
@[simp]
theorem monomialEvaluation_q [DecidableEq ι] (e : ι → E) (he : ∀ i, e i ≠ 0) (i : ι) :
    monomialEvaluation e he (TropicalSemifield.q i) = Units.mk0 (e i) (he i) :=
  TropicalSemifield.lift_q _ i

/-! ### The extended matrix of a triple -/

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- The **extended matrix** `B̃(y, B)` of a tuple `y = (y₁, …, yₙ)` in `Trop(q_{n+1}, …, q_m)`
and an `n × n` integer matrix `B`: the `m × n` integer matrix whose first `n` rows are those of
`B` and whose `(i, j)` entry for `i > n` is the exponent of `qᵢ` in `yⱼ`. -/
@[cluster_algebras "def_triple_extended_matrix"]
def tripleExtendedMatrix (y : Fin n → TropicalSemifield (FrozenIndex m n))
    (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin m) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if h : (i : ℕ) < n then B ⟨i, h⟩ j else TropicalSemifield.exponent (y j) ⟨i, not_lt.1 h⟩

section TripleExtendedMatrix

variable (y : Fin n → TropicalSemifield (FrozenIndex m n)) (B : Matrix (Fin n) (Fin n) ℤ)

/-- For `i < n`, row `i` of `B̃(y, B)` is row `i` of `B`. -/
theorem tripleExtendedMatrix_apply_of_lt {i : Fin m} (hi : (i : ℕ) < n) (j : Fin n) :
    tripleExtendedMatrix y B i j = B ⟨i, hi⟩ j := by
  simp [tripleExtendedMatrix, hi]

/-- The first `n` rows of `B̃(y, B)` are those of `B`. -/
@[simp]
theorem tripleExtendedMatrix_apply_castLE (hmn : n ≤ m) (i j : Fin n) :
    tripleExtendedMatrix y B (Fin.castLE hmn i) j = B i j :=
  tripleExtendedMatrix_apply_of_lt y B i.2 j

/-- For a frozen position `i`, the `(i, j)` entry of `B̃(y, B)` is the exponent of `qᵢ` in
`yⱼ`. -/
@[simp]
theorem tripleExtendedMatrix_apply_frozenIndex (i : FrozenIndex m n) (j : Fin n) :
    tripleExtendedMatrix y B i.1 j = TropicalSemifield.exponent (y j) i := by
  simp [tripleExtendedMatrix, not_lt.2 i.2]

/-- The principal part of `B̃(y, B)` is `B`. -/
@[simp]
theorem principalPart_tripleExtendedMatrix (hmn : n ≤ m) :
    principalPart hmn (tripleExtendedMatrix y B) = B := by
  ext i j
  exact tripleExtendedMatrix_apply_castLE y B hmn i j

/-- The coefficient tuple of `B̃(y, B)` is `y`. -/
@[simp]
theorem coefficientTuple_tripleExtendedMatrix :
    coefficientTuple (tripleExtendedMatrix y B) = y := by
  funext j
  ext i
  simp

end TripleExtendedMatrix

/-! ### The seed of a triple -/

/-- The **seed of a triple** `(x, y, B)` with frozen variables `x_{n+1}, …, x_m`: the extended
cluster `(x₁, …, xₙ, x_{n+1}, …, x_m)` together with the extended matrix `B̃(y, B)`. -/
def SeedTriple.toSeedData (frozen : FrozenIndex m n → F) (T : SeedTriple F m n) :
    SeedData F m n where
  extCluster := T.extCluster frozen
  extExchangeMatrix := tripleExtendedMatrix T.coeff T.exchangeMatrix

section ToSeedData

variable (frozen : FrozenIndex m n → F) (T : SeedTriple F m n)

omit [Field F] in
/-- The extended cluster of the seed of a triple is the extended cluster of the triple. -/
@[simp]
theorem SeedTriple.extCluster_toSeedData :
    (T.toSeedData frozen).extCluster = T.extCluster frozen :=
  rfl

omit [Field F] in
/-- The extended exchange matrix of the seed of a triple `(x, y, B)` is `B̃(y, B)`. -/
@[simp]
theorem SeedTriple.extExchangeMatrix_toSeedData :
    (T.toSeedData frozen).extExchangeMatrix = tripleExtendedMatrix T.coeff T.exchangeMatrix :=
  rfl

omit [Field F] in
/-- The frozen variables of the seed of a triple are the given frozen variables. -/
@[simp]
theorem SeedTriple.frozenTuple_toSeedData :
    (T.toSeedData frozen).frozenTuple = frozen := by
  funext i
  simp [SeedData.frozenTuple, SeedTriple.extCluster, not_lt.2 i.2]

omit [Field F] in
/-- The triple of the seed of a triple `(x, y, B)` is `(x, y, B)`. -/
@[simp]
theorem SeedTriple.toSeedTriple_toSeedData (hmn : n ≤ m) :
    (T.toSeedData frozen).toSeedTriple hmn = T := by
  obtain ⟨x, y, B⟩ := T
  simp only [SeedData.toSeedTriple, extExchangeMatrix_toSeedData,
    coefficientTuple_tripleExtendedMatrix, principalPart_tripleExtendedMatrix,
    SeedTriple.mk.injEq, and_true]
  funext j
  exact dif_pos j.2

/-- The seed of a triple is a labeled seed exactly when the triple is a labeled seed
triple. -/
theorem SeedTriple.isLabeledSeed_toSeedData_iff (hmn : n ≤ m) :
    IsLabeledSeed K hmn (T.toSeedData frozen) ↔ IsSeedTriple K frozen T := by
  change _ ∧ SkewSymmetrizable (principalPart hmn _) ↔ _
  rw [extExchangeMatrix_toSeedData, principalPart_tripleExtendedMatrix]
  rfl

end ToSeedData

/-! ### Mutation of labeled seed triples -/

/-- **The mutation of a labeled seed triple is a labeled seed triple**, with the same frozen
variables. -/
@[cluster_algebras "lem_triple_mutation_is_triple"]
theorem IsSeedTriple.mutation [CharZero K] (hmn : n ≤ m) {frozen : FrozenIndex m n → F}
    {T : SeedTriple F m n} (hT : IsSeedTriple K frozen T) (k : Fin n) :
    IsSeedTriple K frozen (T.mutation frozen k) := by
  have hS := ((T.isLabeledSeed_toSeedData_iff frozen hmn).2 hT).seedMutation hmn k
  have h := hS.isSeedTriple_toSeedTriple hmn
  rwa [SeedData.frozenTuple_seedMutation, SeedData.toSeedTriple_seedMutation,
    SeedTriple.frozenTuple_toSeedData, SeedTriple.toSeedTriple_toSeedData] at h

/-! ### Uniqueness -/

/-- Two maps on the vertices of `𝕋ₙ` that follow the same rule `f k` along every edge labelled
`k`, and agree at one vertex, are equal. -/
theorem RegularTree.eq_of_apply_eq_of_adj {α : Type*} (f : Fin n → α → α)
    {P P' : RegularTree n → α} (hP : ∀ k t t', RegularTree.Adj k t t' → P t' = f k (P t))
    (hP' : ∀ k t t', RegularTree.Adj k t t' → P' t' = f k (P' t)) {t₀ : RegularTree n}
    (h : P t₀ = P' t₀) : P = P' := by
  funext t
  obtain ⟨d, s, κ, h0, hl, hs⟩ := RegularTree.exists_walk t₀ t
  have key : ∀ e : Fin (d + 1), P (s e) = P' (s e) := by
    intro e
    induction e using Fin.induction with
    | zero => rwa [h0]
    | succ e ih => rw [hP _ _ _ (hs e), hP' _ _ _ (hs e), ih]
  rw [← hl]
  exact key _

/-- **A pattern of triples is determined by one triple**: two labeled seed patterns of triples
with the same frozen variables that agree at one vertex agree everywhere. Only the edge
conditions are used; see `RegularTree.eq_of_apply_eq_of_adj`. -/
@[cluster_algebras "lem_triple_pattern_unique"]
theorem IsTriplePattern.eq_of_apply_eq {frozen : FrozenIndex m n → F}
    {P P' : RegularTree n → SeedTriple F m n} (hP : IsTriplePattern K frozen P)
    (hP' : IsTriplePattern K frozen P') {t₀ : RegularTree n} (h : P t₀ = P' t₀) : P = P' :=
  RegularTree.eq_of_apply_eq_of_adj (fun k T => T.mutation frozen k) hP.2 hP'.2 h

attribute [cluster_algebras "lem_seed_determined_by_triple"] SeedData.eq_of_toSeedTriple_eq

end ClusterAlgebras

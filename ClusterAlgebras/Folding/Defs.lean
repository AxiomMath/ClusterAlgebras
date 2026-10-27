/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Defs.MatrixMutationEquiv
public import ClusterAlgebras.Seed
public import ClusterAlgebras.Semifield.Universal

/-!
# Folding: the definitions

Section 4.4 of [FWZ] folds a matrix, and a seed, along the action of a group `G` on its row
indices. This file sets up every definition of that section; the results are in the other
files of `ClusterAlgebras/Folding/`.

## Main definitions

* `ClusterAlgebras.IsGroupAdmissible`: conditions (2)–(4) of Definition 4.4.1 of [FWZ] on an
  `m × n` integer matrix, for an action `MulAction G (Fin m)`.
* `ClusterAlgebras.OrbitLabelling`: a numbering `θ` of the `G`-orbits by `Fin mG`, the
  mutable orbits first.
* `ClusterAlgebras.foldedMatrix`: the folded matrix `B̃ᴳ`, `b^G_{pq} = ∑_{i ∈ θ(p)} b_{i j_q}`.
* `ClusterAlgebras.increasingSeq`: the increasing sequence `s_K` of a set of columns.
* `ClusterAlgebras.mutationCorrection`: the correction `c(x, y)` of a mutated entry.
* `ClusterAlgebras.orbitSeq`: the orbit sequence `θ(ρ)*`.
* `ClusterAlgebras.IsGloballyFoldable`: Definition 4.4.8 of [FWZ].
* `ClusterAlgebras.IsFoldAdmissibleSeed`: a `(G, ψ)`-admissible seed.
* `ClusterAlgebras.foldedSeed`: the folded seed `(x̃, B̃)ᴳ`.

## Implementation notes

* Indices are `Fin m`, so `0, …, m - 1` where [FWZ] writes `1, …, m`, and the mutable
  indices are those of value below `n`; a column `j : Fin n` is the row `Fin.castLE hmn j`.
  This is the convention of `ClusterAlgebras.matrixMutation`.

* The group acts by a `MulAction G (Fin m)`, and the orbits, the relation `i ∼ i'` and the
  quotient are Mathlib's `MulAction.orbit`, `MulAction.orbitRel` and
  `MulAction.orbitRel.Quotient`. An orbit is *mutable* (`ClusterAlgebras.IsMutableOrbit`)
  when it lies in `[0, n)`. The standing assumption of [FWZ] that every `g` maps `[0, n)` into
  itself is not assumed: an orbit labelling already sends exactly the orbits contained in
  `[0, n)` to `[0, nG)`, so dropping it is a generalisation.

* Condition (2), `b_{g(i) g(j)} = b_{ij}`, is stated as: whenever the row `g • j` is the column
  `j'`, `b_{g • i, j'} = b_{ij}`. Read for a `g` preserving `[0, n)` this is the condition of
  [FWZ], and it avoids building the column `g • j` with a proof that it is mutable.

* An orbit labelling is a structure holding the bijection `Fin mG ≃ orbitRel.Quotient G (Fin m)`,
  the inequality `nG ≤ mG` and the condition that `θ p` is mutable iff `p < nG`. Together these
  force `mG` to be the number of orbits and `nG` the number of mutable ones, as in [FWZ]. The orbit
  `θ(p)` as a set of indices is `OrbitLabelling.orbit`, a `Finset`.

* The folded matrix reads column `j_q`, the least element of the mutable orbit `θ(q)`, as
  `OrbitLabelling.colRep`; `ClusterAlgebras.foldedMatrix_apply_eq_sum_of_mem_cols` shows any
  element would do.

* Folding data. The reference seed fixes `P = ℚ_sf(w̃)`, a subset of `F`, and `P^G = ℚ_sf(z̃)`;
  `ψ : P → P^G` is an `FZSemifieldHom`. The semifield structure on `ℚ_sf(·)` needs the field to
  have characteristic zero and the generators to be algebraically independent over `ℚ`, the
  latter as a `Fact` instance; nothing else about the folding data enters the definitions,
  so the conditions on the reference seed (a labeled seed) and on `z̃` (a free generating
  tuple) are hypotheses of the results that use them.

* A folded seed applies `ψ` to entries of a tuple of elements of `F` that [FWZ] takes in
  `P`. To keep `ClusterAlgebras.foldedSeed` a function of a `SeedData`, `ψ` is extended to
  all of `F` by `0` off `P` (`ClusterAlgebras.foldValue`), the way division is total in Lean;
  on an admissible seed every entry is in `P` and the extension is never read.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Section 4.4.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix MulAction

variable {G : Type*} [Group G] {m n mG nG : ℕ} [MulAction G (Fin m)]

/-! ### Admissible matrices and orbit labellings -/

variable (n) in
/-- An orbit `ω` of the action of `G` on `Fin m` is **mutable** when all its elements are
mutable indices, that is, of value below `n`. -/
def IsMutableOrbit (ω : orbitRel.Quotient G (Fin m)) : Prop :=
  ∀ i ∈ ω.orbit, (i : ℕ) < n

variable (G) in
/-- An `m × n` integer matrix `B` is **`G`-admissible** for an action of `G` on `Fin m` when
* (2) `b_{g(i) g(j)} = b_{ij}` for every row `i`, column `j` and `g ∈ G`;
* (3) `b_{i i'} = 0` for mutable `i ∼ i'`;
* (4) `b_{ij} b_{i'j} ≥ 0` for all `i ∼ i'` and every column `j`.
Here `i ∼ i'` means `i' ∈ orbit G i`. -/
@[cluster_algebras "def_group_admissible"]
structure IsGroupAdmissible (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ) : Prop where
  /-- Condition (2): `b_{g(i) g(j)} = b_{ij}`, where the row `g • j` is the column `j'`. -/
  smul_eq : ∀ (g : G) (i : Fin m) (j j' : Fin n), Fin.castLE hmn j' = g • Fin.castLE hmn j →
    B (g • i) j' = B i j
  /-- Condition (3): `b_{i i'} = 0` for mutable `i ∼ i'`. -/
  eq_zero : ∀ i i' : Fin n, Fin.castLE hmn i' ∈ orbit G (Fin.castLE hmn i) →
    B (Fin.castLE hmn i) i' = 0
  /-- Condition (4): `b_{ij} b_{i'j} ≥ 0` for `i ∼ i'`. -/
  mul_nonneg : ∀ i i' : Fin m, i' ∈ orbit G i → ∀ j : Fin n, 0 ≤ B i j * B i' j

variable (G m n mG nG) in
/-- An **orbit labelling** of the action of `G` on `Fin m`: a bijection `θ` from `Fin mG` to the
set of `G`-orbits with `nG ≤ mG`, such that `θ p` is a mutable orbit if and only if `p < nG`.
So `mG` is the number of orbits and `nG` the number of mutable ones. -/
@[cluster_algebras "def_orbit_labelling"]
structure OrbitLabelling where
  /-- The bijection `θ` from labels to orbits. -/
  equiv : Fin mG ≃ orbitRel.Quotient G (Fin m)
  /-- There are at most as many mutable orbits as orbits. -/
  le : nG ≤ mG
  /-- The mutable orbits are those with labels below `nG`. -/
  lt_iff : ∀ p : Fin mG, (p : ℕ) < nG ↔ IsMutableOrbit n (equiv p)

namespace OrbitLabelling

variable (θ : OrbitLabelling G m n mG nG)

open Classical in
/-- The orbit `θ(p)` as a finite set of indices. -/
noncomputable def orbit (p : Fin mG) : Finset (Fin m) :=
  Finset.univ.filter fun i => (Quotient.mk'' i : orbitRel.Quotient G (Fin m)) = θ.equiv p

/-- The label of the orbit of an index. -/
noncomputable def label (i : Fin m) : Fin mG :=
  θ.equiv.symm (Quotient.mk'' i)

/-- An index lies in `θ(p)` exactly when its `G`-orbit is the orbit labelled `p`. -/
theorem mem_orbit_iff {p : Fin mG} {i : Fin m} :
    i ∈ θ.orbit p ↔ (Quotient.mk'' i : orbitRel.Quotient G (Fin m)) = θ.equiv p := by
  classical
  simp [orbit]

/-- An index lies in `θ(p)` exactly when the label of its orbit is `p`. -/
theorem mem_orbit_iff_label_eq {p : Fin mG} {i : Fin m} : i ∈ θ.orbit p ↔ θ.label i = p := by
  rw [mem_orbit_iff, label, Equiv.symm_apply_eq, eq_comm]

/-- Every index lies in the orbit of its own label. -/
theorem mem_orbit_label (i : Fin m) : i ∈ θ.orbit (θ.label i) :=
  (θ.mem_orbit_iff_label_eq).2 rfl

/-- As a set, `θ(p)` is the `G`-orbit labelled `p`. -/
theorem coe_orbit (p : Fin mG) : (θ.orbit p : Set (Fin m)) = (θ.equiv p).orbit := by
  ext i
  simp [mem_orbit_iff, orbitRel.Quotient.mem_orbit]

/-- Two indices in `θ(p)` are in the same `G`-orbit. -/
theorem mem_orbit_of_mem {p : Fin mG} {i i' : Fin m} (hi : i ∈ θ.orbit p) (hi' : i' ∈ θ.orbit p) :
    i' ∈ MulAction.orbit G i := by
  rw [mem_orbit_iff] at hi hi'
  rw [← orbitRel_apply]
  exact Quotient.exact' (hi'.trans hi.symm)

/-- An index in the `G`-orbit of an index of `θ(p)` is in `θ(p)`. -/
theorem mem_of_mem_orbit {p : Fin mG} {i i' : Fin m} (hi : i ∈ θ.orbit p)
    (hi' : i' ∈ MulAction.orbit G i) : i' ∈ θ.orbit p := by
  rw [mem_orbit_iff] at hi ⊢
  rw [← hi]
  exact Quotient.sound' (orbitRel_apply.2 hi')

/-- Each orbit `θ(p)` is stable under the action of `G`. -/
theorem smul_mem_orbit {p : Fin mG} {i : Fin m} (hi : i ∈ θ.orbit p) (g : G) :
    g • i ∈ θ.orbit p :=
  θ.mem_of_mem_orbit hi (mem_orbit i g)

/-- Every orbit `θ(p)` is nonempty. -/
theorem orbit_nonempty (p : Fin mG) : (θ.orbit p).Nonempty := by
  obtain ⟨i, hi⟩ := Quotient.exists_rep (θ.equiv p)
  exact ⟨i, (θ.mem_orbit_iff).2 hi⟩

/-- Distinct labels have disjoint orbits. -/
theorem disjoint_orbit {p p' : Fin mG} (h : p ≠ p') : Disjoint (θ.orbit p) (θ.orbit p') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [mem_orbit_iff_label_eq] at hi hi'
  exact h (hi.symm.trans hi')

/-- The least element `i_p` of the orbit `θ(p)`. -/
noncomputable def rep (p : Fin mG) : Fin m :=
  (θ.orbit p).min' (θ.orbit_nonempty p)

/-- The least element `i_p` lies in `θ(p)`. -/
theorem rep_mem (p : Fin mG) : θ.rep p ∈ θ.orbit p :=
  Finset.min'_mem _ _

/-- The least element `i_p` is at most every element of `θ(p)`. -/
theorem rep_le {p : Fin mG} {i : Fin m} (hi : i ∈ θ.orbit p) : θ.rep p ≤ i :=
  Finset.min'_le _ _ hi

/-- Every element of a mutable orbit `θ(q)`, `q < nG`, is a mutable index. -/
theorem val_lt_of_mem {p : Fin mG} (hp : (p : ℕ) < nG) {i : Fin m} (hi : i ∈ θ.orbit p) :
    (i : ℕ) < n :=
  (θ.lt_iff p).1 hp i (by rwa [← SetLike.mem_coe, coe_orbit] at hi)

/-- The label `castLE θ.le q : Fin mG` of a mutable orbit `q : Fin nG`. -/
theorem val_castLE_lt (q : Fin nG) : ((Fin.castLE θ.le q : Fin mG) : ℕ) < nG := by
  simp

open Classical in
/-- The mutable orbit `θ(q)`, `q < nG`, as a finite set of columns. -/
noncomputable def cols (hmn : n ≤ m) (q : Fin nG) : Finset (Fin n) :=
  Finset.univ.filter fun j => Fin.castLE hmn j ∈ θ.orbit (Fin.castLE θ.le q)

/-- A column `j` lies in the columns of `θ(q)` exactly when the row `j` lies in `θ(q)`. -/
theorem mem_cols {hmn : n ≤ m} {q : Fin nG} {j : Fin n} :
    j ∈ θ.cols hmn q ↔ Fin.castLE hmn j ∈ θ.orbit (Fin.castLE θ.le q) := by
  classical
  simp [cols]

/-- The least element `j_q` of a mutable orbit `θ(q)`, as a column. -/
noncomputable def colRep (q : Fin nG) : Fin n :=
  ⟨θ.rep (Fin.castLE θ.le q), θ.val_lt_of_mem (θ.val_castLE_lt q) (θ.rep_mem _)⟩

/-- Read as a row, the column `j_q` is the least element `i_q` of `θ(q)`. -/
@[simp]
theorem castLE_colRep (hmn : n ≤ m) (q : Fin nG) :
    Fin.castLE hmn (θ.colRep q) = θ.rep (Fin.castLE θ.le q) :=
  rfl

/-- The column `j_q` is a column of `θ(q)`. -/
theorem colRep_mem_cols (hmn : n ≤ m) (q : Fin nG) : θ.colRep q ∈ θ.cols hmn q := by
  rw [mem_cols, θ.castLE_colRep hmn]
  exact θ.rep_mem _

/-- The columns of a mutable orbit `θ(q)`, read as rows, are exactly the elements of `θ(q)`. -/
theorem map_cols_eq_orbit (hmn : n ≤ m) (q : Fin nG) :
    (θ.cols hmn q).map (Fin.castLEEmb hmn) = θ.orbit (Fin.castLE θ.le q) := by
  ext i
  simp only [Finset.mem_map, mem_cols, Fin.castLEEmb_apply]
  refine ⟨fun ⟨j, hj, hji⟩ => hji ▸ hj, fun hi => ?_⟩
  exact ⟨⟨i, θ.val_lt_of_mem (θ.val_castLE_lt q) hi⟩, by simpa using hi, by ext; simp⟩

/-- A sum over a mutable orbit `θ(q)` is a sum over its columns. -/
theorem sum_orbit_eq_sum_cols {M : Type*} [AddCommMonoid M] (hmn : n ≤ m) (q : Fin nG)
    (f : Fin m → M) :
    ∑ i ∈ θ.orbit (Fin.castLE θ.le q), f i = ∑ j ∈ θ.cols hmn q, f (Fin.castLE hmn j) := by
  rw [← θ.map_cols_eq_orbit hmn, Finset.sum_map]
  rfl

/-- A mutable orbit has at least one column. -/
theorem card_cols_pos (hmn : n ≤ m) (q : Fin nG) : 0 < (θ.cols hmn q).card :=
  Finset.card_pos.2 ⟨_, θ.colRep_mem_cols hmn q⟩

end OrbitLabelling

/-- The **folded matrix** `B̃ᴳ`: the `mG × nG` matrix with
`b^G_{pq} = ∑_{i ∈ θ(p)} b_{i j_q}`, where `j_q` is the least element of `θ(q)`. -/
@[cluster_algebras "def_folded_matrix"]
noncomputable def foldedMatrix (θ : OrbitLabelling G m n mG nG)
    (B : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin mG) (Fin nG) ℤ :=
  Matrix.of fun p q => ∑ i ∈ θ.orbit p, B i (θ.colRep q)

/-- The entries of the folded matrix: `b^G_{pq} = ∑_{i ∈ θ(p)} b_{i j_q}`. -/
theorem foldedMatrix_apply (θ : OrbitLabelling G m n mG nG)
    (B : Matrix (Fin m) (Fin n) ℤ) (p : Fin mG) (q : Fin nG) :
    foldedMatrix θ B p q = ∑ i ∈ θ.orbit p, B i (θ.colRep q) :=
  rfl

/-! ### Mutation at a set of indices -/

/-- The **increasing sequence** `s_K = (k₁, …, k_s)` of a set `K` of columns,
`k₁ < ⋯ < k_s`. -/
@[cluster_algebras "def_increasing_sequence"]
def increasingSeq (K : Finset (Fin n)) : List (Fin n) :=
  K.sort (· ≤ ·)

/-- The **mutation correction** `c(x, y)`: `xy` if `x, y > 0`, `-xy` if `x, y < 0`, and `0`
otherwise. Off row and column `k`, `μ_k(B)_{ij} = b_{ij} + c(b_{ik}, b_{kj})`. -/
@[cluster_algebras "def_mutation_correction"]
def mutationCorrection (x y : ℤ) : ℤ :=
  if 0 < x ∧ 0 < y then x * y else if x < 0 ∧ y < 0 then -(x * y) else 0

/-- The **orbit sequence** `θ(ρ)*` of a sequence `ρ = (r₁, …, r_d)` of mutable labels: the
concatenation of `s_{θ(r₁)}, …, s_{θ(r_d)}`. -/
@[cluster_algebras "def_orbit_sequence"]
noncomputable def orbitSeq (θ : OrbitLabelling G m n mG nG) (hmn : n ≤ m) (ρ : List (Fin nG)) :
    List (Fin n) :=
  ρ.flatMap fun r => increasingSeq (θ.cols hmn r)

/-- An `m × n` integer matrix `B` is **globally foldable** for an orbit labelling `θ` when it is
`G`-admissible and so is `μ_{θ(ρ)*}(B)` for every finite sequence `ρ` of mutable labels. -/
@[cluster_algebras "def_globally_foldable"]
def IsGloballyFoldable (θ : OrbitLabelling G m n mG nG) (hmn : n ≤ m)
    (B : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  IsGroupAdmissible G hmn B ∧
    ∀ ρ : List (Fin nG), IsGroupAdmissible G hmn (matrixMutationList hmn B (orbitSeq θ hmn ρ))

/-! ### Admissible and folded seeds -/

section Seeds

variable {F : Type*} [Field F] [CharZero F] {w : Fin m → F} [Fact (AlgebraicIndependent ℚ w)]
  {FG : Type*} [Field FG] [CharZero FG] {z : Fin mG → FG} [Fact (AlgebraicIndependent ℚ z)]

open Classical in
/-- The semifield homomorphism `ψ : ℚ_sf(w̃) → ℚ_sf(z̃)`, read as a function `F → F^G`: `ψ(x)`
on `ℚ_sf(w̃)`, and `0` elsewhere. -/
noncomputable def foldValue (ψ : FZSemifieldHom (universalSemifield w) (universalSemifield z))
    (x : F) : FG :=
  if h : x ∈ universalSemifield w then (ψ ⟨x, h⟩ : FG) else 0

/-- On `ℚ_sf(w̃)`, `foldValue ψ` is `ψ`. -/
theorem foldValue_of_mem (ψ : FZSemifieldHom (universalSemifield w) (universalSemifield z))
    {x : F} (hx : x ∈ universalSemifield w) : foldValue ψ x = (ψ ⟨x, hx⟩ : FG) := by
  classical
  simp [foldValue, hx]

variable (G) in
/-- Given folding data, with `ψ : ℚ_sf(w̃) → ℚ_sf(z̃)`, a pair `S = (x̃, B̃)` is
**`(G, ψ)`-admissible** when the entries of `x̃` lie in `P = ℚ_sf(w̃)`, `B̃` is `G`-admissible,
`b_{ij} = -b_{ji}` for mutable `i, j`, and `ψ(x_i) = ψ(x_{i'})` whenever `i ∼ i'`. -/
@[cluster_algebras "def_admissible_seed"]
structure IsFoldAdmissibleSeed (hmn : n ≤ m)
    (ψ : FZSemifieldHom (universalSemifield w) (universalSemifield z)) (S : SeedData F m n) :
    Prop where
  /-- The entries of the extended cluster lie in `P`. -/
  mem : ∀ i, S.extCluster i ∈ universalSemifield w
  /-- The extended exchange matrix is `G`-admissible. -/
  admissible : IsGroupAdmissible G hmn S.extExchangeMatrix
  /-- The principal part is skew-symmetric. -/
  skew : ∀ i j : Fin n,
    S.extExchangeMatrix (Fin.castLE hmn i) j = -S.extExchangeMatrix (Fin.castLE hmn j) i
  /-- `ψ` is constant on the entries over an orbit. -/
  foldValue_eq : ∀ i i' : Fin m, i' ∈ orbit G i →
    foldValue ψ (S.extCluster i) = foldValue ψ (S.extCluster i')

/-- The **folded seed** `(x̃, B̃)ᴳ = (x̃ᴳ, B̃ᴳ)`, with `x^G_p = ψ(x_{i_p})` for `i_p` the least
element of `θ(p)`. -/
@[cluster_algebras "def_folded_seed"]
noncomputable def foldedSeed (θ : OrbitLabelling G m n mG nG)
    (ψ : FZSemifieldHom (universalSemifield w) (universalSemifield z)) (S : SeedData F m n) :
    SeedData FG mG nG where
  extCluster p := foldValue ψ (S.extCluster (θ.rep p))
  extExchangeMatrix := foldedMatrix θ S.extExchangeMatrix

end Seeds

end ClusterAlgebras

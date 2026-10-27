/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Cartan.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The Cartan matrices of the Dynkin diagrams

The second part of FWZ's Section 5.2. A *Dynkin symbol* is one of `A_n` (`n ≥ 1`), `B_n`
(`n ≥ 2`), `C_n` (`n ≥ 3`), `D_n` (`n ≥ 4`), `E_6`, `E_7`, `E_8`, `F_4`, `G_2`, and `C(X)` is its
Cartan matrix in the conventions of Kac that FWZ use. For a list of symbols `C(X)` is
block-diagonal, and a matrix is *of type `X`* when it is a simultaneous permutation of `C(X)`.
The determinants of the `C(X)` are computed, and every `C(X)` is a Cartan matrix of finite
type, by Sylvester's criterion.

## Main definitions

* `ClusterAlgebras.dynkinTreeD m`: the tree `D_m`.
* `ClusterAlgebras.dynkinGraphE n`: the graph `E_n`.
* `ClusterAlgebras.cartanOfGraph G`: the simply-laced Cartan matrix of a graph `G`.
* `ClusterAlgebras.cartanA`, `cartanB`, `cartanC`, `cartanD`, `cartanE`, `cartanF₄`,
  `cartanG₂`: the Cartan matrices, defined for every size where the rule makes sense.
* `ClusterAlgebras.DynkinSymbol`: the Dynkin symbols, with `DynkinSymbol.rank` and
  `DynkinSymbol.cartan`.
* `ClusterAlgebras.DynkinSymbol.listRank`, `DynkinSymbol.listCartan`: the total rank and the
  block-diagonal Cartan matrix of a list of symbols.
* `ClusterAlgebras.IsOfDynkinType A X`: `A` is of type `X`.

## Main results

* `ClusterAlgebras.det_cartanA`, `det_cartanB`, `det_cartanC`, `det_cartanD`, `det_cartanE`,
  `det_cartanF₄`, `det_cartanG₂`: the determinants of the Dynkin Cartan matrices.
* `ClusterAlgebras.isCartanFiniteType_listCartan`: `C(X)` is a Cartan matrix of finite type.
* `ClusterAlgebras.IsOfDynkinType.isCartanFiniteType`: every matrix of type `X` is of finite
  type.

## Implementation notes

* Indices are `Fin n`, so FWZ's vertex `i` is `i - 1` here. In particular `C(B_n)` has
  the entry `-2` in position `(0, 1)`, `C(C_n)` in position `(1, 0)`, `C(F_4)` in position
  `(2, 1)`, and `C(G_2)` has `-3` in position `(0, 1)`.
* The type `E_n` is one constructor with `n ∈ [6, 8]`, as FWZ treat the three uniformly.
* Being of type `X` packages FWZ's two conditions, `n = n₁ + ⋯ + n_r` and having the
  same type as `C(X)`, into one bijection `Fin n ≃ Fin (n₁ + ⋯ + n_r)`.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

/-! ### The tree `D_m` -/

/-- The edge relation of the tree `D_m`: in `1`-based numbering `{i, i+1}` for `1 ≤ i ≤ m - 2`
and `{m - 2, m}`, so on `Fin m` the edges `{i, i + 1}` with `i + 1 ≤ m - 2` and
`{m - 3, m - 1}`. -/
def dynkinTreeDRel (m : ℕ) (i j : Fin m) : Prop :=
  ((i : ℕ) + 1 = j ∧ (j : ℕ) + 2 ≤ m) ∨ ((i : ℕ) + 3 = m ∧ (j : ℕ) + 1 = m)

/-- The edge relation of `D_m` is decidable. -/
instance instDecidableRelDynkinTreeDRel (m : ℕ) : DecidableRel (dynkinTreeDRel m) :=
  fun _ _ => by unfold dynkinTreeDRel; infer_instance

/-- The **tree `D_m`**: vertex set `[1, m]` and edges `{i, i+1}` for `1 ≤ i ≤ m - 2` together
with `{m - 2, m}`. It is defined for every `m`; it is the Dynkin tree `D_m` for `m ≥ 4`. -/
@[cluster_algebras "def_dynkin_tree_D"]
def dynkinTreeD (m : ℕ) : FiniteSimpleGraph (Fin m) :=
  SimpleGraph.fromRel (dynkinTreeDRel m)

/-- Adjacency in `D_m` is decidable. -/
instance instDecidableRelDynkinTreeDAdj (m : ℕ) : DecidableRel (dynkinTreeD m).Adj :=
  fun _ _ => decidable_of_iff _ (SimpleGraph.fromRel_adj _ _ _).symm

/-- Adjacency in `D_m` unfolded to its edge relation. -/
theorem dynkinTreeD_adj {m : ℕ} {i j : Fin m} :
    (dynkinTreeD m).Adj i j ↔ i ≠ j ∧ (dynkinTreeDRel m i j ∨ dynkinTreeDRel m j i) :=
  SimpleGraph.fromRel_adj ..

/-! ### The Cartan matrices -/

/-- The simply-laced Cartan matrix of a graph `G`: `2` on the diagonal, `-1` at the edges of `G`,
and `0` elsewhere. -/
def cartanOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if i = j then 2 else if G.Adj i j then -1 else 0

/-- The entries of the simply-laced Cartan matrix of a graph. -/
theorem cartanOfGraph_apply {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    cartanOfGraph G i j = if i = j then 2 else if G.Adj i j then -1 else 0 :=
  rfl

/-- `C(A_n)`: edges `{i, i+1}`. Defined for every `n`. -/
@[cluster_algebras "def_dynkin_cartan"]
def cartanA (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if i = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0

/-- `C(B_n)`: the matrix `C(A_n)` with its `1`-based entry `(1, 2)` replaced by `-2`. Defined
for every `n`; `C(B_1) = (2)`. -/
@[cluster_algebras "def_dynkin_cartan"]
def cartanB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then -2 else cartanA n i j

/-- `C(C_n)`: the matrix `C(A_n)` with its `1`-based entry `(2, 1)` replaced by `-2`. Defined
for every `n`; `C(C_1) = (2)` and `C(C_2)` is the transpose of `C(B_2)`. -/
@[cluster_algebras "def_dynkin_cartan"]
def cartanC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then -2 else cartanA n i j

/-- `C(D_n)`: the simply-laced Cartan matrix of the tree `D_n`. -/
@[cluster_algebras "def_dynkin_cartan"]
def cartanD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  cartanOfGraph (dynkinTreeD n)

/-- The edge relation of `E_n`: in `1`-based numbering `{i, i+1}` for `1 ≤ i ≤ n - 2` and
`{3, n}`, so on `Fin n` the edges `{i, i + 1}` with `i + 1 ≤ n - 2` and `{2, n - 1}`. -/
def dynkinERel (n : ℕ) (i j : Fin n) : Prop :=
  ((i : ℕ) + 1 = j ∧ (j : ℕ) + 2 ≤ n) ∨ ((i : ℕ) = 2 ∧ (j : ℕ) + 1 = n)

/-- The edge relation of `E_n` is decidable. -/
instance instDecidableRelDynkinERel (n : ℕ) : DecidableRel (dynkinERel n) :=
  fun _ _ => by unfold dynkinERel; infer_instance

/-- The graph `E_n`: the path `1 — ⋯ — (n - 1)` with the vertex `n` attached to `3`. -/
def dynkinGraphE (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (dynkinERel n)

/-- Adjacency in `E_n` is decidable. -/
instance instDecidableRelDynkinGraphEAdj (n : ℕ) : DecidableRel (dynkinGraphE n).Adj :=
  fun _ _ => decidable_of_iff _ (SimpleGraph.fromRel_adj _ _ _).symm

/-- Adjacency in `E_n` unfolded to its edge relation. -/
theorem dynkinGraphE_adj {n : ℕ} {i j : Fin n} :
    (dynkinGraphE n).Adj i j ↔ i ≠ j ∧ (dynkinERel n i j ∨ dynkinERel n j i) :=
  SimpleGraph.fromRel_adj ..

/-- `C(E_n)`: the simply-laced Cartan matrix of `E_n`. Defined for every `n`; the Dynkin symbols
use `n ∈ {6, 7, 8}`. -/
@[cluster_algebras "def_dynkin_cartan"]
def cartanE (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  cartanOfGraph (dynkinGraphE n)

/-- `C(F_4)`: the matrix `C(A_4)` with its `1`-based entry `(3, 2)` replaced by `-2`. -/
@[cluster_algebras "def_dynkin_cartan"]
def cartanF₄ : Matrix (Fin 4) (Fin 4) ℤ :=
  of fun i j => if (i : ℕ) = 2 ∧ (j : ℕ) = 1 then -2 else cartanA 4 i j

/-- `C(G_2)`: the matrix `C(A_2)` with its `1`-based entry `(1, 2)` replaced by `-3`. -/
@[cluster_algebras "def_dynkin_cartan"]
def cartanG₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then -3 else cartanA 2 i j

/-! ### Dynkin symbols -/

/-- A **Dynkin symbol**: one of `A_n` (`n ≥ 1`), `B_n` (`n ≥ 2`), `C_n` (`n ≥ 3`), `D_n`
(`n ≥ 4`), `E_n` (`n ∈ {6, 7, 8}`), `F_4`, `G_2`. -/
@[cluster_algebras "def_dynkin_cartan"]
inductive DynkinSymbol where
  /-- The symbol `A_n`, `n ≥ 1`. -/
  | A (n : ℕ) (hn : 1 ≤ n)
  /-- The symbol `B_n`, `n ≥ 2`. -/
  | B (n : ℕ) (hn : 2 ≤ n)
  /-- The symbol `C_n`, `n ≥ 3`. -/
  | C (n : ℕ) (hn : 3 ≤ n)
  /-- The symbol `D_n`, `n ≥ 4`. -/
  | D (n : ℕ) (hn : 4 ≤ n)
  /-- The symbol `E_n`, `n ∈ {6, 7, 8}`. -/
  | E (n : ℕ) (hn : 6 ≤ n ∧ n ≤ 8)
  /-- The symbol `F_4`. -/
  | F₄
  /-- The symbol `G_2`. -/
  | G₂
  deriving DecidableEq

namespace DynkinSymbol

/-- The **rank** of a Dynkin symbol: its subscript. -/
@[cluster_algebras "def_dynkin_cartan"]
def rank : DynkinSymbol → ℕ
  | A n _ => n
  | B n _ => n
  | C n _ => n
  | D n _ => n
  | E n _ => n
  | F₄ => 4
  | G₂ => 2

/-- The **Cartan matrix** `C(X)` of a Dynkin symbol `X`. -/
@[cluster_algebras "def_dynkin_cartan"]
def cartan : (X : DynkinSymbol) → Matrix (Fin X.rank) (Fin X.rank) ℤ
  | A n _ => cartanA n
  | B n _ => cartanB n
  | C n _ => cartanC n
  | D n _ => cartanD n
  | E n _ => cartanE n
  | F₄ => cartanF₄
  | G₂ => cartanG₂

/-- The total rank `n₁ + ⋯ + n_r` of a list of Dynkin symbols. -/
@[cluster_algebras "def_dynkin_cartan"]
def listRank : List DynkinSymbol → ℕ
  | [] => 0
  | X :: Xs => X.rank + listRank Xs

/-- The Cartan matrix `C(X)` of a list `X = (X¹, …, X^r)` of Dynkin symbols: the block-diagonal
matrix with diagonal blocks `C(X¹), …, C(X^r)` in this order. -/
@[cluster_algebras "def_dynkin_cartan"]
def listCartan : (Xs : List DynkinSymbol) → Matrix (Fin (listRank Xs)) (Fin (listRank Xs)) ℤ
  | [] => 0
  | X :: Xs => reindex finSumFinEquiv finSumFinEquiv (fromBlocks X.cartan 0 0 (listCartan Xs))

end DynkinSymbol

/-- An `n × n` matrix `A` is **of type `X`**, for a list `X` of Dynkin symbols, when
`n = n₁ + ⋯ + n_r` and `A` has the same type as `C(X)`: `aᵢⱼ = C(X)_{σ(i)σ(j)}` for a bijection
`σ` from the indices of `A` to those of `C(X)`. For a single symbol `X` the list is `[X]`. -/
@[cluster_algebras "def_dynkin_cartan"]
def IsOfDynkinType {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (Xs : List DynkinSymbol) : Prop :=
  ∃ σ : Fin n ≃ Fin (DynkinSymbol.listRank Xs), ∀ i j,
    A i j = DynkinSymbol.listCartan Xs (σ i) (σ j)

/-- Being of type `X` is having the same type as `C(X)` once the sizes agree. -/
theorem isOfDynkinType_iff_sameCartanType {Xs : List DynkinSymbol}
    (A : Matrix (Fin (DynkinSymbol.listRank Xs)) (Fin (DynkinSymbol.listRank Xs)) ℤ) :
    IsOfDynkinType A Xs ↔ SameCartanType (DynkinSymbol.listCartan Xs) A :=
  Iff.rfl

/-- `C(X)` is of type `X`. -/
theorem isOfDynkinType_listCartan (Xs : List DynkinSymbol) :
    IsOfDynkinType (DynkinSymbol.listCartan Xs) Xs :=
  ⟨Equiv.refl _, fun _ _ => rfl⟩

/-! ### Determinants -/

/-- **Expansion at a leaf in position `0`.** If the first row and the first column of `M` vanish
outside the positions `0` and `1`, then
`det M = M₀₀ det M_{0̂} - M₀₁ M₁₀ det M_{0̂ 1̂}`, where hats denote deleted indices. -/
theorem det_eq_of_leaf_zero {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (hrow : ∀ j : Fin n, M 0 j.succ.succ = 0) (hcol : ∀ i : Fin n, M i.succ.succ 0 = 0) :
    M.det = M 0 0 * (M.submatrix Fin.succ Fin.succ).det -
      M 0 1 * M 1 0 * ((M.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [hrow, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [det_succ_column_zero (M.submatrix Fin.succ (Fin.succ 0).succAbove), Fin.sum_univ_succ]
  simp only [submatrix_apply, Fin.succ_succAbove_zero, hcol, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, submatrix_submatrix, Fin.succAbove_zero]
  have : ((Fin.succ (0 : Fin (n + 1))).succAbove ∘ Fin.succ) = Fin.succ ∘ Fin.succ := by
    funext j; simp
  rw [this]
  simp
  ring

/-- The entries of `C(A_n)` in terms of the values of the indices. -/
theorem cartanA_apply {n : ℕ} (i j : Fin n) : cartanA n i j =
    if (i : ℕ) = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0 := by
  simp [cartanA, Fin.val_inj]

/-- The entries of `C(D_n)` in terms of the values of the indices. -/
theorem cartanD_apply {n : ℕ} (i j : Fin n) : cartanD n i j =
    if (i : ℕ) = j then 2 else
      if ((i : ℕ) + 1 = j ∧ (j : ℕ) + 2 ≤ n) ∨ ((i : ℕ) + 3 = n ∧ (j : ℕ) + 1 = n) ∨
        ((j : ℕ) + 1 = i ∧ (i : ℕ) + 2 ≤ n) ∨ ((j : ℕ) + 3 = n ∧ (i : ℕ) + 1 = n) then -1
      else 0 := by
  simp only [cartanD, cartanOfGraph, dynkinTreeD, of_apply, SimpleGraph.fromRel_adj,
    dynkinTreeDRel, Fin.val_inj, ne_eq]
  by_cases h : i = j
  · simp [h]
  · simp only [h, if_false, not_false_eq_true, true_and, or_assoc]

/-- Deleting the vertex `0` from `C(A_{n+1})` gives `C(A_n)`. -/
theorem cartanA_submatrix_succ (n : ℕ) :
    (cartanA (n + 1)).submatrix Fin.succ Fin.succ = cartanA n := by
  ext i j; simp [cartanA, Fin.succ_inj]

/-- Deleting the vertex `0` from `C(B_{n+2})` gives `C(A_{n+1})`. -/
theorem cartanB_submatrix_succ (n : ℕ) :
    (cartanB (n + 2)).submatrix Fin.succ Fin.succ = cartanA (n + 1) := by
  ext i j; simp [cartanB, ← cartanA_submatrix_succ (n + 1)]

/-- Deleting the vertex `0` from `C(C_{n+2})` gives `C(A_{n+1})`. -/
theorem cartanC_submatrix_succ (n : ℕ) :
    (cartanC (n + 2)).submatrix Fin.succ Fin.succ = cartanA (n + 1) := by
  ext i j; simp [cartanC, ← cartanA_submatrix_succ (n + 1)]

/-- Deleting the vertex `0` from `C(D_{n+1})` gives `C(D_n)`. -/
theorem cartanD_submatrix_succ (n : ℕ) :
    (cartanD (n + 1)).submatrix Fin.succ Fin.succ = cartanD n := by
  ext i j
  simp only [cartanD, cartanOfGraph, dynkinTreeD, submatrix_apply, of_apply, Fin.succ_inj,
    SimpleGraph.fromRel_adj, dynkinTreeDRel, ne_eq, Fin.val_succ]
  congr 2
  apply propext
  omega

/-- The determinants `det C(A_n) = n + 1` and `det C(A_{n+1}) = n + 2`. -/
theorem det_cartanA_and_succ (n : ℕ) :
    (cartanA n).det = n + 1 ∧ (cartanA (n + 1)).det = n + 2 := by
  induction n with
  | zero => exact ⟨by simp, by rw [det_fin_one]; simp [cartanA]⟩
  | succ n ih =>
    refine ⟨by exact_mod_cast ih.2, ?_⟩
    rw [det_eq_of_leaf_zero _ (fun j => ?_) (fun i => ?_), cartanA_submatrix_succ,
      cartanA_submatrix_succ, ih.1, ih.2]
    · simp [cartanA]
      ring
    all_goals
      simp only [cartanA_apply, Fin.val_succ, Fin.val_zero]
      split_ifs <;> simp_all

/-- **Determinants of the Dynkin Cartan matrices**: `det C(A_n) = n + 1`. -/
@[cluster_algebras "lem_dynkin_det"]
theorem det_cartanA (n : ℕ) : (cartanA n).det = n + 1 :=
  (det_cartanA_and_succ n).1

/-- **Determinants of the Dynkin Cartan matrices**: `det C(B_n) = 2` for `n ≥ 1`. -/
@[cluster_algebras "lem_dynkin_det"]
theorem det_cartanB {n : ℕ} (hn : 1 ≤ n) : (cartanB n).det = 2 := by
  obtain _ | _ | n := n
  · omega
  · rw [det_fin_one]; simp [cartanB, cartanA]
  · rw [det_eq_of_leaf_zero _ (fun j => ?_) (fun i => ?_), cartanB_submatrix_succ,
      cartanA_submatrix_succ, det_cartanA, det_cartanA]
    · simp [cartanB, cartanA]
      ring
    all_goals
      simp only [cartanB, of_apply, cartanA_apply, Fin.val_succ, Fin.val_zero]
      split_ifs <;> simp_all

/-- **Determinants of the Dynkin Cartan matrices**: `det C(C_n) = 2` for `n ≥ 1`. -/
@[cluster_algebras "lem_dynkin_det"]
theorem det_cartanC {n : ℕ} (hn : 1 ≤ n) : (cartanC n).det = 2 := by
  obtain _ | _ | n := n
  · omega
  · rw [det_fin_one]; simp [cartanC, cartanA]
  · rw [det_eq_of_leaf_zero _ (fun j => ?_) (fun i => ?_), cartanC_submatrix_succ,
      cartanA_submatrix_succ, det_cartanA, det_cartanA]
    · simp [cartanC, cartanA]
      ring
    all_goals
      simp only [cartanC, of_apply, cartanA_apply, Fin.val_succ, Fin.val_zero]
      split_ifs <;> simp_all

/-- The determinants `det C(D_{n+2}) = det C(D_{n+3}) = 4`. -/
theorem det_cartanD_add_two_and_succ (n : ℕ) :
    (cartanD (n + 2)).det = 4 ∧ (cartanD (n + 3)).det = 4 := by
  induction n with
  | zero => exact ⟨by rw [det_fin_two]; decide, by rw [det_fin_three]; decide⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [det_eq_of_leaf_zero _ (fun j => ?_) (fun i => ?_), cartanD_submatrix_succ,
      cartanD_submatrix_succ, ih.1, ih.2]
    · simp only [cartanD_apply, Fin.val_one, Fin.val_zero]
      norm_num
    · simp only [cartanD_apply, Fin.val_succ, Fin.val_zero]
      split_ifs <;> simp_all
    · simp only [cartanD_apply, Fin.val_succ, Fin.val_zero]
      split_ifs <;> simp_all

/-- **Determinants of the Dynkin Cartan matrices**: `det C(D_n) = 4` for `n ≥ 4`. -/
@[cluster_algebras "lem_dynkin_det"]
theorem det_cartanD {n : ℕ} (hn : 4 ≤ n) : (cartanD n).det = 4 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ n by omega)
  exact (det_cartanD_add_two_and_succ m).1

/-- **Determinants of the Dynkin Cartan matrices**: `det C(E_n) = 9 - n` for `n ∈ {6, 7, 8}`. -/
@[cluster_algebras "lem_dynkin_det"]
theorem det_cartanE {n : ℕ} (hn : 6 ≤ n ∧ n ≤ 8) : (cartanE n).det = 9 - n := by
  obtain ⟨h₁, h₂⟩ := hn
  interval_cases n
  · have h₁ : (cartanE 6).submatrix Fin.succ Fin.succ = (cartanD 5).submatrix
        (Equiv.swap (0 : Fin 5) 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 5))
        (Equiv.swap (0 : Fin 5) 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 5)) := by
      ext i j; revert i j; decide
    have h₂ : (cartanE 6).submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ) =
        (cartanA 4).submatrix (Equiv.swap (0 : Fin 4) 2 : Equiv.Perm (Fin 4))
          (Equiv.swap (0 : Fin 4) 2 : Equiv.Perm (Fin 4)) := by
      ext i j; revert i j; decide
    rw [det_eq_of_leaf_zero _ (by decide) (by decide), submatrix_submatrix, h₂, h₁,
      det_submatrix_equiv_self, det_submatrix_equiv_self, det_cartanD (by norm_num), det_cartanA]
    decide
  · have h₁ : (cartanE 7).submatrix Fin.succ Fin.succ = (cartanD 6).submatrix
        (Equiv.swap (0 : Fin 6) 4 * Equiv.swap 1 3 : Equiv.Perm (Fin 6))
        (Equiv.swap (0 : Fin 6) 4 * Equiv.swap 1 3 : Equiv.Perm (Fin 6)) := by
      ext i j; revert i j; decide
    have h₂ : (cartanE 7).submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ) =
        (cartanA 5).submatrix (Equiv.swap (0 : Fin 5) 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 5))
          (Equiv.swap (0 : Fin 5) 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 5)) := by
      ext i j; revert i j; decide
    rw [det_eq_of_leaf_zero _ (by decide) (by decide), submatrix_submatrix, h₂, h₁,
      det_submatrix_equiv_self, det_submatrix_equiv_self, det_cartanD (by norm_num), det_cartanA]
    decide
  · have h₁ : (cartanE 8).submatrix Fin.succ Fin.succ = (cartanD 7).submatrix
        (Equiv.swap (0 : Fin 7) 5 * Equiv.swap 1 4 * Equiv.swap 2 3 : Equiv.Perm (Fin 7))
        (Equiv.swap (0 : Fin 7) 5 * Equiv.swap 1 4 * Equiv.swap 2 3 : Equiv.Perm (Fin 7)) := by
      ext i j; revert i j; decide
    have h₂ : (cartanE 8).submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ) =
        (cartanA 6).submatrix (Equiv.swap (0 : Fin 6) 4 * Equiv.swap 1 3 : Equiv.Perm (Fin 6))
          (Equiv.swap (0 : Fin 6) 4 * Equiv.swap 1 3 : Equiv.Perm (Fin 6)) := by
      ext i j; revert i j; decide
    rw [det_eq_of_leaf_zero _ (by decide) (by decide), submatrix_submatrix, h₂, h₁,
      det_submatrix_equiv_self, det_submatrix_equiv_self, det_cartanD (by norm_num), det_cartanA]
    decide

/-- **Determinants of the Dynkin Cartan matrices**: `det C(F_4) = 1`. -/
@[cluster_algebras "lem_dynkin_det"]
theorem det_cartanF₄ : cartanF₄.det = 1 := by
  rw [det_succ_row_zero]
  simp only [Fin.sum_univ_succ, det_fin_three, Finset.univ_unique, Finset.sum_singleton]
  decide

/-- **Determinants of the Dynkin Cartan matrices**: `det C(G_2) = 1`. -/
@[cluster_algebras "lem_dynkin_det"]
theorem det_cartanG₂ : cartanG₂.det = 1 := by
  rw [det_fin_two]
  decide

/-! ### Finite type -/

/-- The quadratic form of `D A` written as a double sum. -/
theorem dotProduct_diagonal_mul_map_mulVec_eq_sum {n : ℕ} (d : Fin n → ℤ)
    (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℝ) :
    v ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ v) =
      ∑ i, ∑ j, v i * ((d i : ℝ) * A i j) * v j := by
  simp only [dotProduct, mulVec, diagonal_mul, map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Sylvester's criterion for Cartan matrices.** A matrix with diagonal entries `2`,
nonpositive entries off the diagonal and a symmetrizer, whose leading principal minors are all
positive, is a Cartan matrix of finite type. -/
theorem isCartanFiniteType_of_leadingMinors_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0) {d : Fin n → ℤ}
    (hd : IsSymmetrizer A d)
    (hmin : ∀ (k : ℕ) (hk : k ≤ n), 1 ≤ k →
      0 < (A.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    IsCartanFiniteType A := by
  refine ⟨⟨hdiag, hoff, d, hd⟩, d, hd, posDef_of_leadingMinors_pos ?_ ?_⟩
  · ext i j
    simp only [transpose_apply, diagonal_mul, map_apply]
    exact_mod_cast hd.2 j i
  · intro k hk hk1
    have h : (diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)).submatrix
        (Fin.castLE hk) (Fin.castLE hk) = diagonal (fun i => (d (Fin.castLE hk i) : ℝ)) *
          (A.submatrix (Fin.castLE hk) (Fin.castLE hk)).map (Int.cast : ℤ → ℝ) := by
      ext i j; simp [diagonal_mul]
    rw [h, det_mul, det_diagonal, ← Int.cast_det]
    exact mul_pos (Finset.prod_pos fun i _ => by exact_mod_cast hd.1 _)
      (by exact_mod_cast hmin k hk hk1)

/-- Gluing symmetrizers of `A` and `B` gives a symmetrizer of the block-diagonal matrix. -/
theorem IsSymmetrizer.reindex_fromBlocks {a b : ℕ} {A : Matrix (Fin a) (Fin a) ℤ}
    {B : Matrix (Fin b) (Fin b) ℤ} {dA : Fin a → ℤ} {dB : Fin b → ℤ} (hA : IsSymmetrizer A dA)
    (hB : IsSymmetrizer B dB) :
    IsSymmetrizer (reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B))
      (fun i => Sum.elim dA dB (finSumFinEquiv.symm i)) := by
  set e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  set N := reindex e e (fromBlocks A 0 0 B) with hN
  have hentry : ∀ p q, N (e p) (e q) = fromBlocks A 0 0 B p q := by simp [hN]
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · obtain ⟨p, rfl⟩ := e.surjective i
    rcases p with p | p <;> simp [hA.1, hB.1]
  · obtain ⟨p, rfl⟩ := e.surjective i
    obtain ⟨q, rfl⟩ := e.surjective j
    rcases p with p | p <;> rcases q with q | q <;> simp [hentry, hA.2, hB.2]

private theorem dotProduct_diagonal_mul_map_mulVec_nonneg {m : ℕ} {D : Fin m → ℤ}
    {M : Matrix (Fin m) (Fin m) ℤ}
    (h : ∀ w : Fin m → ℝ, w ≠ 0 →
      0 < w ⬝ᵥ ((diagonal (fun i => (D i : ℝ)) * M.map (Int.cast : ℤ → ℝ)) *ᵥ w))
    (w : Fin m → ℝ) :
    0 ≤ w ⬝ᵥ ((diagonal (fun i => (D i : ℝ)) * M.map (Int.cast : ℤ → ℝ)) *ᵥ w) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · exact (h w hw).le

/-- **A block-diagonal matrix with diagonal blocks of finite type is of finite type.** -/
theorem IsCartanFiniteType.reindex_fromBlocks {a b : ℕ} {A : Matrix (Fin a) (Fin a) ℤ}
    {B : Matrix (Fin b) (Fin b) ℤ} (hA : IsCartanFiniteType A) (hB : IsCartanFiniteType B) :
    IsCartanFiniteType (reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B)) := by
  obtain ⟨⟨hAd, hAo, -⟩, dA, hdA, hpA⟩ := hA
  obtain ⟨⟨hBd, hBo, -⟩, dB, hdB, hpB⟩ := hB
  have hsym := hdA.reindex_fromBlocks hdB
  set e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  set N := reindex e e (fromBlocks A 0 0 B) with hN
  have hentry : ∀ p q, N (e p) (e q) = fromBlocks A 0 0 B p q := by simp [hN]
  set d : Fin (a + b) → ℤ := fun i => Sum.elim dA dB (e.symm i) with hd
  have hde : ∀ p, d (e p) = Sum.elim dA dB p := by simp [hd]
  refine ⟨⟨?_, ?_, d, hsym⟩, d, hsym, ?_⟩
  · intro i
    obtain ⟨p, rfl⟩ := e.surjective i
    rcases p with p | p <;> simp [hentry, hAd, hBd]
  · intro i j hij
    obtain ⟨p, rfl⟩ := e.surjective i
    obtain ⟨q, rfl⟩ := e.surjective j
    rcases p with p | p <;> rcases q with q | q <;> simp only [hentry, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, le_refl]
    · exact hAo p q fun h => hij (by rw [h])
    · exact hBo p q fun h => hij (by rw [h])
  · intro v hv
    have hsplit : v ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * N.map (Int.cast : ℤ → ℝ)) *ᵥ v) =
        (v ∘ e ∘ Sum.inl) ⬝ᵥ ((diagonal (fun i => (dA i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ
          (v ∘ e ∘ Sum.inl)) +
        (v ∘ e ∘ Sum.inr) ⬝ᵥ ((diagonal (fun i => (dB i : ℝ)) * B.map (Int.cast : ℤ → ℝ)) *ᵥ
          (v ∘ e ∘ Sum.inr)) := by
      simp only [dotProduct_diagonal_mul_map_mulVec_eq_sum]
      rw [← e.sum_comp]
      simp only [← e.sum_comp (fun j => v _ * _ * v j), hentry, hde, Fintype.sum_sum_type,
        fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        Matrix.zero_apply, Int.cast_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
        zero_add, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    rw [hsplit]
    by_cases hl : v ∘ e ∘ Sum.inl = 0
    · have hr : v ∘ e ∘ Sum.inr ≠ 0 := fun hr =>
        hv (funext (e.surjective.forall.2 (Sum.forall.2 ⟨congrFun hl, congrFun hr⟩)))
      exact add_pos_of_nonneg_of_pos (dotProduct_diagonal_mul_map_mulVec_nonneg hpA _) (hpB _ hr)
    · exact add_pos_of_pos_of_nonneg (hpA _ hl) (dotProduct_diagonal_mul_map_mulVec_nonneg hpB _)

/-- The diagonal entries of a simply-laced Cartan matrix are `2`. -/
theorem cartanOfGraph_apply_self {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i : Fin n) : cartanOfGraph G i i = 2 := by
  simp [cartanOfGraph]

/-- The off-diagonal entries of a simply-laced Cartan matrix are nonpositive. -/
theorem cartanOfGraph_apply_nonpos {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {i j : Fin n} (hij : i ≠ j) : cartanOfGraph G i j ≤ 0 := by
  simp only [cartanOfGraph, of_apply, hij, if_false]
  split_ifs <;> norm_num

/-- The constant vector `1` is a symmetrizer of a simply-laced Cartan matrix. -/
theorem isSymmetrizer_cartanOfGraph_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    IsSymmetrizer (cartanOfGraph G) 1 := by
  refine ⟨fun _ => one_pos, fun i j => ?_⟩
  simp only [cartanOfGraph, of_apply, Pi.one_apply, one_mul, eq_comm (a := i), G.adj_comm]

/-- The entries of `C(E_n)` in terms of the values of the indices. -/
theorem cartanE_apply {n : ℕ} (i j : Fin n) : cartanE n i j =
    if (i : ℕ) = j then 2 else
      if ((i : ℕ) + 1 = j ∧ (j : ℕ) + 2 ≤ n) ∨ ((i : ℕ) = 2 ∧ (j : ℕ) + 1 = n) ∨
        ((j : ℕ) + 1 = i ∧ (i : ℕ) + 2 ≤ n) ∨ ((j : ℕ) = 2 ∧ (i : ℕ) + 1 = n) then -1
      else 0 := by
  simp only [cartanE, cartanOfGraph, dynkinGraphE, of_apply, SimpleGraph.fromRel_adj,
    dynkinERel, Fin.val_inj, ne_eq]
  by_cases h : i = j
  · simp [h]
  · simp only [h, if_false, not_false_eq_true, true_and, or_assoc]

/-- The leading principal submatrices of `C(A_n)` are the `C(A_k)`. -/
theorem cartanA_submatrix_castLE {k n : ℕ} (hk : k ≤ n) :
    (cartanA n).submatrix (Fin.castLE hk) (Fin.castLE hk) = cartanA k := by
  ext i j
  simp only [submatrix_apply, cartanA_apply, Fin.val_castLE]
  split_ifs <;> omega

/-- The leading principal submatrices of `C(B_n)` are the `C(B_k)`. -/
theorem cartanB_submatrix_castLE {k n : ℕ} (hk : k ≤ n) :
    (cartanB n).submatrix (Fin.castLE hk) (Fin.castLE hk) = cartanB k := by
  ext i j
  simp only [cartanB, of_apply, submatrix_apply, cartanA_apply, Fin.val_castLE]
  split_ifs <;> omega

/-- The leading principal submatrices of `C(C_n)` are the `C(C_k)`. -/
theorem cartanC_submatrix_castLE {k n : ℕ} (hk : k ≤ n) :
    (cartanC n).submatrix (Fin.castLE hk) (Fin.castLE hk) = cartanC k := by
  ext i j
  simp only [cartanC, of_apply, submatrix_apply, cartanA_apply, Fin.val_castLE]
  split_ifs <;> omega

/-- The proper leading principal submatrices of `C(D_n)` are the `C(A_k)`. -/
theorem cartanD_submatrix_castLE {k n : ℕ} (hkn : k < n) :
    (cartanD n).submatrix (Fin.castLE hkn.le) (Fin.castLE hkn.le) = cartanA k := by
  ext i j
  simp only [submatrix_apply, cartanD_apply, cartanA_apply, Fin.val_castLE]
  have := i.isLt
  have := j.isLt
  split_ifs <;> omega

/-- The proper leading principal submatrices of `C(E_n)` are the `C(A_k)`. -/
theorem cartanE_submatrix_castLE {k n : ℕ} (hkn : k < n) :
    (cartanE n).submatrix (Fin.castLE hkn.le) (Fin.castLE hkn.le) = cartanA k := by
  ext i j
  simp only [submatrix_apply, cartanE_apply, cartanA_apply, Fin.val_castLE]
  have := i.isLt
  have := j.isLt
  split_ifs <;> omega

/-- The Cartan matrix `cartanA n` is of finite type. -/
theorem isCartanFiniteType_cartanA (n : ℕ) : IsCartanFiniteType (cartanA n) := by
  refine isCartanFiniteType_of_leadingMinors_pos (d := 1) (fun i => by simp [cartanA])
    (fun i j hij => ?_) ⟨fun _ => one_pos, fun i j => ?_⟩ fun k hk hk1 => ?_
  · simp only [cartanA_apply]
    split_ifs <;> simp_all [Fin.val_inj]
  · simp only [cartanA_apply, Pi.one_apply, one_mul]
    split_ifs <;> omega
  · rw [cartanA_submatrix_castLE, det_cartanA]
    positivity

/-- The Cartan matrix `cartanB n` is of finite type. -/
theorem isCartanFiniteType_cartanB (n : ℕ) : IsCartanFiniteType (cartanB n) := by
  refine isCartanFiniteType_of_leadingMinors_pos (d := fun i => if (i : ℕ) = 0 then 1 else 2)
    (fun i => by simp [cartanB, cartanA_apply]; omega) (fun i j hij => ?_)
    ⟨fun i => by dsimp only; split_ifs <;> norm_num, fun i j => ?_⟩ fun k hk hk1 => ?_
  · simp only [cartanB, of_apply, cartanA_apply]
    split_ifs <;> simp_all [Fin.val_inj]
  · simp only [cartanB, of_apply, cartanA_apply]
    split_ifs <;> omega
  · rw [cartanB_submatrix_castLE, det_cartanB hk1]
    norm_num

/-- The Cartan matrix `cartanC n` is of finite type. -/
theorem isCartanFiniteType_cartanC (n : ℕ) : IsCartanFiniteType (cartanC n) := by
  refine isCartanFiniteType_of_leadingMinors_pos (d := fun i => if (i : ℕ) = 0 then 2 else 1)
    (fun i => by simp [cartanC, cartanA_apply]; omega) (fun i j hij => ?_)
    ⟨fun i => by dsimp only; split_ifs <;> norm_num, fun i j => ?_⟩ fun k hk hk1 => ?_
  · simp only [cartanC, of_apply, cartanA_apply]
    split_ifs <;> simp_all [Fin.val_inj]
  · simp only [cartanC, of_apply, cartanA_apply]
    split_ifs <;> omega
  · rw [cartanC_submatrix_castLE, det_cartanC hk1]
    norm_num

/-- The Cartan matrix `cartanD n`, `n ≥ 4`, is of finite type. -/
theorem isCartanFiniteType_cartanD {n : ℕ} (hn : 4 ≤ n) : IsCartanFiniteType (cartanD n) := by
  refine isCartanFiniteType_of_leadingMinors_pos (cartanOfGraph_apply_self _)
    (fun i j hij => cartanOfGraph_apply_nonpos _ hij) (isSymmetrizer_cartanOfGraph_one _)
    fun k hk hk1 => ?_
  rcases hk.lt_or_eq with hkn | rfl
  · rw [cartanD_submatrix_castLE hkn, det_cartanA]
    positivity
  · simp only [Fin.castLE_rfl, submatrix_id_id, det_cartanD hn]
    norm_num

/-- The Cartan matrix `cartanE n`, `6 ≤ n ≤ 8`, is of finite type. -/
theorem isCartanFiniteType_cartanE {n : ℕ} (hn : 6 ≤ n ∧ n ≤ 8) :
    IsCartanFiniteType (cartanE n) := by
  refine isCartanFiniteType_of_leadingMinors_pos (cartanOfGraph_apply_self _)
    (fun i j hij => cartanOfGraph_apply_nonpos _ hij) (isSymmetrizer_cartanOfGraph_one _)
    fun k hk hk1 => ?_
  rcases hk.lt_or_eq with hkn | rfl
  · rw [cartanE_submatrix_castLE hkn, det_cartanA]
    positivity
  · simp only [Fin.castLE_rfl, submatrix_id_id, det_cartanE hn]
    omega

/-- The Cartan matrix `cartanF₄` is of finite type. -/
theorem isCartanFiniteType_cartanF₄ : IsCartanFiniteType cartanF₄ := by
  refine isCartanFiniteType_of_leadingMinors_pos (d := ![2, 2, 1, 1]) (by decide) (by decide)
    (by unfold IsSymmetrizer; decide) fun k hk hk1 => ?_
  interval_cases k
  · rw [det_fin_one]; revert hk; decide
  · rw [det_fin_two]; revert hk; decide
  · rw [det_fin_three]; revert hk; decide
  · simp only [Fin.castLE_rfl, submatrix_id_id, det_cartanF₄]
    norm_num

/-- The Cartan matrix `cartanG₂` is of finite type. -/
theorem isCartanFiniteType_cartanG₂ : IsCartanFiniteType cartanG₂ := by
  refine isCartanFiniteType_of_leadingMinors_pos (d := ![1, 3]) (by decide) (by decide)
    (by unfold IsSymmetrizer; decide) fun k hk hk1 => ?_
  interval_cases k
  · rw [det_fin_one]; revert hk; decide
  · simp only [Fin.castLE_rfl, submatrix_id_id, det_cartanG₂]
    norm_num

/-- **The Cartan matrix of a Dynkin symbol is of finite type.** -/
theorem DynkinSymbol.isCartanFiniteType_cartan : (X : DynkinSymbol) → IsCartanFiniteType X.cartan
  | .A n _ => isCartanFiniteType_cartanA n
  | .B n _ => isCartanFiniteType_cartanB n
  | .C n _ => isCartanFiniteType_cartanC n
  | .D _ hn => isCartanFiniteType_cartanD hn
  | .E _ hn => isCartanFiniteType_cartanE hn
  | .F₄ => isCartanFiniteType_cartanF₄
  | .G₂ => isCartanFiniteType_cartanG₂

/-- **The Dynkin Cartan matrices are of finite type**: for every list `X` of Dynkin symbols,
`C(X)` is a Cartan matrix of finite type. -/
@[cluster_algebras "lem_dynkin_finite_type"]
theorem isCartanFiniteType_listCartan (Xs : List DynkinSymbol) :
    IsCartanFiniteType (DynkinSymbol.listCartan Xs) := by
  induction Xs with
  | nil =>
    refine ⟨⟨fun i => i.elim0, fun i => i.elim0, 1, fun i => i.elim0, fun i => i.elim0⟩, 1,
      ⟨fun i => i.elim0, fun i => i.elim0⟩, fun v hv => absurd (funext fun i => i.elim0) hv⟩
  | cons X Xs ih => exact X.isCartanFiniteType_cartan.reindex_fromBlocks ih

/-- **The Dynkin Cartan matrices are of finite type**: every matrix of type `X` is a Cartan
matrix of finite type. -/
@[cluster_algebras "lem_dynkin_finite_type"]
theorem IsOfDynkinType.isCartanFiniteType {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {Xs : List DynkinSymbol} (hA : IsOfDynkinType A Xs) : IsCartanFiniteType A := by
  obtain ⟨σ, hσ⟩ := hA
  have h : A = (DynkinSymbol.listCartan Xs).submatrix σ σ := by
    ext i j; exact hσ i j
  rw [h]
  exact (isCartanFiniteType_listCartan Xs).submatrix σ.injective

end ClusterAlgebras

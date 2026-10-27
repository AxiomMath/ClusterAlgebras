/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Tropical.Triple
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Finite subtrees of the regular tree and their exchange ideals

Let `Σ` be a seed pattern of rank `n` in `F` over a field `K`, with `m × n` matrices. A *finite
subtree* `T` of `𝕋ₙ` is a nonempty finite set of vertices any two of which are joined by a walk
inside `T`. Removing the edges labelled `i` cuts `T` into the forest `T[i]`, whose connected
component through `t` is written `C_i(t)`; along such a component the cluster variable in
position `i` does not change. The *formal variables* of `T` are one variable `z_r` for each frozen
position `r` and one variable `z_{i,C}` for each `i < n` and each component `C` of `T[i]`, and
`ζ(t)` is the tuple of formal variables `(z_{1,C_1(t)}, …, z_{n,C_n(t)}, z_{n+1}, …, z_m)`.

The *evaluation* `ev_T : K[z_T] → F` sends `z_r` to the frozen variable `x_r` and `z_{i,C}` to the
cluster variable `x_{i;t_C}` for a chosen vertex `t_C ∈ C`. The *exchange polynomials*
`E_{t,t'} = z_{k,C_k(t)} z_{k,C_k(t')} - M⁺ₖ(ζ(t), B̃(t)) - M⁻ₖ(ζ(t), B̃(t))` of the edges of `T`
generate the *exchange ideal* `I_T`, and `J_T` is its saturation with respect to the product `M_T`
of the mutable formal variables. The *depth* of a formal variable is measured from a vertex
`t₀ ∈ T`.

## Main definitions

* `ClusterAlgebras.RegularTree.subtreeGraph T`, `ClusterAlgebras.RegularTree.IsFiniteSubtree T`:
  the edges of `T` and the condition that `T` is a finite subtree.
* `ClusterAlgebras.RegularTree.subtreeForest T i`, `ClusterAlgebras.RegularTree.subtreeComponent`:
  the forest `T[i]` and its component `C_i(t)`.
* `ClusterAlgebras.RegularTree.FormalVar m T`, `ClusterAlgebras.formalCluster K T t`: the formal
  variables `z_T` and the tuple `ζ(t)`.
* `ClusterAlgebras.subtreeEval K hmn P T`: the evaluation `ev_T`.
* `ClusterAlgebras.subtreeAlgebra K P T`: the subalgebra `𝒜_T`.
* `ClusterAlgebras.exchangePolynomial K P T t t' k`, `ClusterAlgebras.exchangeIdeal K P T`: the
  exchange polynomials and the exchange ideal `I_T`.
* `ClusterAlgebras.mutableVarProd K m T`, `ClusterAlgebras.saturatedExchangeIdeal K P T`: the
  product `M_T` and the saturation `J_T`.
* `ClusterAlgebras.RegularTree.formalVarDepth T t₀`: the depth of a formal variable.

## Implementation notes

* A finite subtree is a `Finset` of vertices. Its edges form the graph `subtreeGraph T` on the
  vertices of `T`, and the condition that any two elements of `T` are joined by a walk inside `T`
  is that this graph is connected; connectedness includes nonemptiness. The forests `T[i]` are
  graphs on the same vertex type, and their components are Mathlib's connected components.
* Indices are `0`-based: the mutable positions are `i : Fin n`, sitting in position
  `Fin.castLE hmn i` of an extended cluster, and the frozen positions are `FrozenIndex m n`.
* The evaluation chooses the vertex `t_C` as the representative `Quot.out C` of the component. It
  sends `z_r` to the entry in position `r` of the seed at the root of `𝕋ₙ`, the frozen variables
  being the same at every vertex.
* The exchange monomials of `ζ(t)` have nonnegative exponents, so they are defined in `K[z_T]`
  itself as products of natural powers; `map_exchangePolynomial` shows that any ring map to a
  field, in particular the one to the fraction field, takes them to the exchange monomials
  `exchangeMonomialPos` and `exchangeMonomialNeg` computed there.
* The definitions need neither that `Σ` is a seed pattern nor that `K` has characteristic zero,
  and assume neither.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapter 6*,
  Section 6.8.
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial

namespace RegularTree

variable {n : ℕ}

/-- An edge labelled `k` can be traversed in either direction. -/
theorem Adj.symm {k : Fin n} {t t' : RegularTree n} (h : RegularTree.Adj k t t') :
    RegularTree.Adj k t' t :=
  Or.symm h

/-- The two ends of an edge are distinct. -/
theorem Adj.ne {k : Fin n} {t t' : RegularTree n} (h : RegularTree.Adj k t t') : t ≠ t' := by
  rintro rfl
  rcases h with h | h <;> simpa using congrArg List.length h

/-- The graph on the vertices of `𝕋ₙ` whose edges are the edges of `𝕋ₙ` with a label in `L`. For
`L = univ` it is `𝕋ₙ` itself. -/
def labelGraph (L : Set (Fin n)) : SimpleGraph (RegularTree n) where
  Adj t t' := ∃ k ∈ L, RegularTree.Adj k t t'
  symm := ⟨by
    rintro t t' ⟨k, hk, h⟩
    exact ⟨k, hk, h.symm⟩⟩
  loopless := ⟨by
    rintro t ⟨k, -, h⟩
    exact h.ne rfl⟩

/-- `t` and `t'` are adjacent in `labelGraph L` iff they are joined by an edge of `𝕋ₙ` with label
in `L`. -/
@[simp]
theorem labelGraph_adj {L : Set (Fin n)} {t t' : RegularTree n} :
    (labelGraph L).Adj t t' ↔ ∃ k ∈ L, RegularTree.Adj k t t' :=
  Iff.rfl

/-- The **edges of a set `T` of vertices** of `𝕋ₙ`: the graph on `T` whose edges are the edges of
`𝕋ₙ` between elements of `T`. -/
@[cluster_algebras "def_finite_subtree"]
def subtreeGraph (T : Finset (RegularTree n)) : SimpleGraph T :=
  (labelGraph Set.univ).comap ((↑) : T → RegularTree n)

/-- Two elements of `T` are adjacent in `subtreeGraph T` iff they are adjacent in `𝕋ₙ`. -/
@[simp]
theorem subtreeGraph_adj {T : Finset (RegularTree n)} {t t' : T} :
    (subtreeGraph T).Adj t t' ↔ ∃ k, RegularTree.Adj k (t : RegularTree n) t' := by
  simp [subtreeGraph]

/-- `T` is a **finite subtree** of `𝕋ₙ`: a nonempty finite set of vertices any two of which are
joined by a walk in `𝕋ₙ` all of whose vertices lie in `T`, that is, the graph of the edges of `T`
is connected. -/
@[cluster_algebras "def_finite_subtree"]
def IsFiniteSubtree (T : Finset (RegularTree n)) : Prop :=
  (subtreeGraph T).Connected

/-- A finite subtree is nonempty. -/
theorem IsFiniteSubtree.nonempty {T : Finset (RegularTree n)} (hT : IsFiniteSubtree T) :
    T.Nonempty :=
  let ⟨t⟩ := SimpleGraph.Connected.nonempty hT
  ⟨t, t.2⟩

/-- The **forest `T[i]`**: the graph on `T` whose edges are the edges of `T` not labelled `i`. -/
@[cluster_algebras "def_subtree_components"]
def subtreeForest (T : Finset (RegularTree n)) (i : Fin n) : SimpleGraph T :=
  (labelGraph {i}ᶜ).comap ((↑) : T → RegularTree n)

/-- Two elements of `T` are adjacent in `T[i]` iff they are joined by an edge of `𝕋ₙ` with a label
`k ≠ i`. -/
@[simp]
theorem subtreeForest_adj {T : Finset (RegularTree n)} {i : Fin n} {t t' : T} :
    (subtreeForest T i).Adj t t' ↔ ∃ k, k ≠ i ∧ RegularTree.Adj k (t : RegularTree n) t' := by
  simp [subtreeForest]

/-- The **component `C_i(t)`**: the connected component of the forest `T[i]` containing `t`. -/
@[cluster_algebras "def_subtree_components"]
abbrev subtreeComponent (T : Finset (RegularTree n)) (i : Fin n) (t : T) :
    (subtreeForest T i).ConnectedComponent :=
  (subtreeForest T i).connectedComponentMk t

variable (m : ℕ) in
/-- The **formal variables** `z_T` of a set `T` of vertices of `𝕋ₙ`: a variable `z_r` for each
frozen position `r`, and a *mutable* formal variable `z_{i,C}` for each `i < n` and each connected
component `C` of `T[i]`. -/
@[cluster_algebras "def_tree_formal_variables"]
abbrev FormalVar (T : Finset (RegularTree n)) : Type :=
  FrozenIndex m n ⊕ Σ i : Fin n, (subtreeForest T i).ConnectedComponent

variable {m : ℕ}

/-- The formal variable in position `r` of `ζ(t)`: `z_{r,C_r(t)}` for a mutable position `r`, and
`z_r` for a frozen one. -/
def formalVarOf (T : Finset (RegularTree n)) (t : T) (r : Fin m) : FormalVar m T :=
  if h : (r : ℕ) < n then .inr ⟨⟨r, h⟩, subtreeComponent T ⟨r, h⟩ t⟩
  else .inl ⟨r, not_lt.1 h⟩

/-- The formal variable in a mutable position `i` of `ζ(t)` is `z_{i,C_i(t)}`. -/
theorem formalVarOf_castLE (hmn : n ≤ m) (T : Finset (RegularTree n)) (t : T) (i : Fin n) :
    formalVarOf T t (Fin.castLE hmn i) = .inr ⟨i, subtreeComponent T i t⟩ := by
  simp [formalVarOf]

/-- The formal variable in a frozen position `r` of `ζ(t)` is `z_r`. -/
theorem formalVarOf_of_le (T : Finset (RegularTree n)) (t : T) {r : Fin m} (hr : n ≤ (r : ℕ)) :
    formalVarOf (m := m) T t r = .inl ⟨r, hr⟩ := by
  simp [formalVarOf, not_lt.2 hr]

/-- The entries of `ζ(t)` are pairwise distinct. -/
theorem formalVarOf_injective (T : Finset (RegularTree n)) (t : T) :
    Function.Injective (formalVarOf (m := m) T t) := by
  intro r r' h
  unfold formalVarOf at h
  split_ifs at h <;> simp_all [Fin.ext_iff]

/-- The **depth** of a formal variable, measured from a vertex `t₀ ∈ T`: `0` for the `z_r`, and for
`z_{i,C}` the least distance `d(s)` from `t₀` to a vertex `s ∈ C` along walks inside `T`. -/
@[cluster_algebras "def_formal_variable_depth"]
noncomputable def formalVarDepth (T : Finset (RegularTree n)) (t₀ : T) : FormalVar m T → ℕ :=
  Sum.elim (fun _ => 0) fun v => sInf ((subtreeGraph T).dist t₀ '' v.2.supp)

/-- The variables `z_r` have depth `0`. -/
@[simp]
theorem formalVarDepth_inl (T : Finset (RegularTree n)) (t₀ : T) (r : FrozenIndex m n) :
    formalVarDepth T t₀ (.inl r) = 0 :=
  rfl

/-- The depth of `z_{i,C}` is at most the distance from `t₀` to any vertex of `C`. -/
theorem formalVarDepth_inr_le (T : Finset (RegularTree n)) (t₀ : T) {i : Fin n}
    {C : (subtreeForest T i).ConnectedComponent} {s : T} (hs : s ∈ C.supp) :
    formalVarDepth T t₀ (Sum.inr ⟨i, C⟩ : FormalVar m T) ≤ (subtreeGraph T).dist t₀ s :=
  Nat.sInf_le ⟨s, hs, rfl⟩

/-- The depth of `z_{i,C}` is the distance from `t₀` to some vertex of `C`. -/
theorem exists_mem_supp_dist_eq_formalVarDepth (T : Finset (RegularTree n)) (t₀ : T) {i : Fin n}
    (C : (subtreeForest T i).ConnectedComponent) :
    ∃ s ∈ C.supp,
      (subtreeGraph T).dist t₀ s = formalVarDepth T t₀ (Sum.inr ⟨i, C⟩ : FormalVar m T) := by
  obtain ⟨s, hs⟩ := C.exists_rep
  exact Nat.sInf_mem (s := (subtreeGraph T).dist t₀ '' C.supp) ⟨_, s, (C.mem_supp_iff s).2 hs, rfl⟩

/-- Every entry of `ζ(s)` has depth at most the distance from `t₀` to `s`. -/
theorem formalVarDepth_formalVarOf_le (T : Finset (RegularTree n)) (t₀ s : T) (r : Fin m) :
    formalVarDepth T t₀ (formalVarOf T s r) ≤ (subtreeGraph T).dist t₀ s := by
  unfold formalVarOf
  split_ifs
  exacts [formalVarDepth_inr_le T t₀ rfl, Nat.zero_le _]

end RegularTree

open RegularTree

variable (K : Type*) {F : Type*} [Field K] {m n : ℕ}

/-- The tuple **`ζ(t)`** of formal variables of a vertex `t ∈ T`: its entry in a mutable position
`i` is `z_{i,C_i(t)}`, and in a frozen position `r` it is `z_r`. -/
@[cluster_algebras "def_tree_formal_variables"]
noncomputable def formalCluster (T : Finset (RegularTree n)) (t : T) :
    Fin m → MvPolynomial (FormalVar m T) K :=
  fun r => X (formalVarOf T t r)

/-- The entry of `ζ(t)` in position `r` is the variable `X (formalVarOf T t r)`. -/
theorem formalCluster_apply (T : Finset (RegularTree n)) (t : T) (r : Fin m) :
    formalCluster K T t r = X (formalVarOf T t r) :=
  rfl

/-- The **evaluation** `ev_T : K[z_T] → F` of the formal variables of `T`: the `K`-algebra map
sending `z_r` to the frozen variable `x_r` and `z_{i,C}` to the cluster variable `x_{i;t_C}`, for
the vertex `t_C ∈ C` chosen as the representative of `C`. -/
@[cluster_algebras "def_tree_evaluation"]
noncomputable def subtreeEval [Field F] [Algebra K F] (hmn : n ≤ m)
    (P : RegularTree n → SeedData F m n) (T : Finset (RegularTree n)) :
    MvPolynomial (FormalVar m T) K →ₐ[K] F :=
  aeval <| Sum.elim (fun r => (P .root).extCluster r.1)
    fun v => (P (Quot.out v.2 : T)).extCluster (Fin.castLE hmn v.1)

/-- The **subalgebra `𝒜_T`** of a set `T` of vertices: the `K`-subalgebra of `F` generated by the
entries `x_{i;t}` of the extended clusters of the seeds at the vertices `t ∈ T`. -/
@[cluster_algebras "def_tree_subalgebra"]
def subtreeAlgebra [Field F] [Algebra K F] (P : RegularTree n → SeedData F m n)
    (T : Finset (RegularTree n)) : Subalgebra K F :=
  Algebra.adjoin K (⋃ t ∈ T, Set.range (P t).extCluster)

/-- The **exchange polynomial** `E_{t,t'} = z_{k,C_k(t)} z_{k,C_k(t')} - M⁺ₖ(ζ(t), B̃(t)) -
M⁻ₖ(ζ(t), B̃(t))` of vertices `t, t' ∈ T` and a direction `k`; it is used when `t` and `t'` are
joined by an edge labelled `k`. The exchange monomials have nonnegative exponents, so they are
written as products of natural powers (`map_exchangePolynomial`). -/
@[cluster_algebras "def_exchange_ideal"]
noncomputable def exchangePolynomial (P : RegularTree n → SeedData F m n)
    (T : Finset (RegularTree n)) (t t' : T) (k : Fin n) : MvPolynomial (FormalVar m T) K :=
  X (.inr ⟨k, subtreeComponent T k t⟩) * X (.inr ⟨k, subtreeComponent T k t'⟩) -
    ∏ i, formalCluster K T t i ^ ((P t).extExchangeMatrix i k).toNat -
    ∏ i, formalCluster K T t i ^ (-(P t).extExchangeMatrix i k).toNat

/-- The **exchange ideal** `I_T`: the ideal of `K[z_T]` generated by the exchange polynomials
`E_{t,t'}` of the ordered pairs of elements of `T` joined by an edge. -/
@[cluster_algebras "def_exchange_ideal"]
noncomputable def exchangeIdeal (P : RegularTree n → SeedData F m n)
    (T : Finset (RegularTree n)) : Ideal (MvPolynomial (FormalVar m T) K) :=
  Ideal.span {f | ∃ (t t' : T) (k : Fin n), RegularTree.Adj k t t' ∧
    exchangePolynomial K P T t t' k = f}

variable {K}

/-- The exchange polynomial is, in any field receiving `K[z_T]`, in particular in its fraction
field, `z_{k,C_k(t)} z_{k,C_k(t')} - M⁺ₖ(ζ(t), B̃(t)) - M⁻ₖ(ζ(t), B̃(t))` with the exchange
monomials of `ζ(t)` computed there. -/
@[cluster_algebras "def_exchange_ideal"]
theorem map_exchangePolynomial (P : RegularTree n → SeedData F m n)
    (T : Finset (RegularTree n)) (t t' : T) (k : Fin n) {L : Type*} [Field L]
    (φ : MvPolynomial (FormalVar m T) K →+* L) :
    φ (exchangePolynomial K P T t t' k) =
      φ (X (.inr ⟨k, subtreeComponent T k t⟩)) * φ (X (.inr ⟨k, subtreeComponent T k t'⟩)) -
        exchangeMonomialPos (φ ∘ formalCluster K T t) (P t).extExchangeMatrix k -
        exchangeMonomialNeg (φ ∘ formalCluster K T t) (P t).extExchangeMatrix k := by
  simp [exchangePolynomial, exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod, map_prod]

/-- The exchange polynomial of an edge of `T` lies in the exchange ideal. -/
theorem mem_exchangeIdeal_of_adj (P : RegularTree n → SeedData F m n)
    (T : Finset (RegularTree n)) {t t' : T} {k : Fin n} (h : RegularTree.Adj k t t') :
    exchangePolynomial K P T t t' k ∈ exchangeIdeal K P T :=
  Ideal.subset_span ⟨t, t', k, h, rfl⟩

variable (K m) in
/-- The product **`M_T`** of the mutable formal variables `z_{i,C}` of `T`. -/
@[cluster_algebras "def_saturated_exchange_ideal"]
noncomputable def mutableVarProd (T : Finset (RegularTree n)) : MvPolynomial (FormalVar m T) K :=
  haveI := Fintype.ofFinite (Σ i : Fin n, (subtreeForest T i).ConnectedComponent)
  ∏ v : Σ i : Fin n, (subtreeForest T i).ConnectedComponent, X (.inr v)

variable (K) in
/-- The **saturated exchange ideal** `J_T = {f : M_T ^ e f ∈ I_T for some e ≥ 0}`: the saturation
of the exchange ideal with respect to the product of the mutable formal variables. -/
@[cluster_algebras "def_saturated_exchange_ideal"]
noncomputable def saturatedExchangeIdeal (P : RegularTree n → SeedData F m n)
    (T : Finset (RegularTree n)) : Ideal (MvPolynomial (FormalVar m T) K) where
  carrier := {f | ∃ e : ℕ, mutableVarProd K m T ^ e * f ∈ exchangeIdeal K P T}
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [mul_add, pow_add]
    refine add_mem ?_ ?_
    · rw [mul_right_comm]
      exact Ideal.mul_mem_right _ _ ha
    · rw [mul_assoc]
      exact Ideal.mul_mem_left _ _ hb
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c f ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ he

/-- `f` lies in the saturation iff some power of the product of the mutable variables times `f`
lies in the exchange ideal. -/
theorem mem_saturatedExchangeIdeal {P : RegularTree n → SeedData F m n}
    {T : Finset (RegularTree n)} {f : MvPolynomial (FormalVar m T) K} :
    f ∈ saturatedExchangeIdeal K P T ↔
      ∃ e : ℕ, mutableVarProd K m T ^ e * f ∈ exchangeIdeal K P T :=
  Iff.rfl

/-- The exchange ideal is contained in its saturation. -/
theorem exchangeIdeal_le_saturatedExchangeIdeal (P : RegularTree n → SeedData F m n)
    (T : Finset (RegularTree n)) : exchangeIdeal K P T ≤ saturatedExchangeIdeal K P T :=
  fun f hf => ⟨0, by simpa using hf⟩

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.SeedPattern
public import ClusterAlgebras.Cartan.External

/-!
# Types of Cartan matrices and of seed patterns

The end of FWZ's Section 5.2. Every Cartan matrix of finite type has a type, a list of Dynkin
symbols, by the Cartan–Killing classification applied to the components of its Coxeter graph.
The *Cartan counterpart* `A(B)` of a skew-symmetrizable matrix `B` has diagonal entries `2` and
`aᵢⱼ = -|bᵢⱼ|` off the diagonal, and a seed pattern is *of type `X`* when the Cartan counterpart
of one of its exchange matrices is of type `X`.

## Main definitions

* `ClusterAlgebras.cartanCounterpart B`: the Cartan counterpart `A(B)`.
* `ClusterAlgebras.IsPatternOfType hmn P X`: the seed pattern `P` is of type `X`.

## Main statements

* `ClusterAlgebras.isOfDynkinType_of_isCartanFiniteType`: every Cartan matrix of finite type
  has a type.
* `ClusterAlgebras.isOfDynkinType_ofFn_of_blocks`: the type of a matrix split into blocks is
  the list of the types of the blocks.
* `ClusterAlgebras.IsSkewSymmetrizingVector.isGeneralizedCartan_cartanCounterpart`: the Cartan
  counterpart is a symmetrizable generalized Cartan matrix.

## Implementation notes

* FWZ's "more precisely" clause takes the vertex sets of the connected components of the
  Coxeter graph. It is stated here for any partition of the indices into blocks with no nonzero
  entry joining two different blocks, which the components are; the block `I_s` is listed in
  increasing order by `Finset.orderEmbOfFin`.
* As FWZ remark, the type of a seed pattern imposes no condition on the frozen rows of its
  extended exchange matrices.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

/-- The entries of `C(X :: Xs)` in the block of `X`. -/
private theorem listCartan_cons_apply_inl_inl (X : DynkinSymbol) (Xs : List DynkinSymbol)
    (a b : Fin X.rank) :
    DynkinSymbol.listCartan (X :: Xs) (finSumFinEquiv (Sum.inl a))
      (finSumFinEquiv (Sum.inl b)) = X.cartan a b := by
  simp [DynkinSymbol.listCartan, reindex_apply]

/-- The entries of `C(X :: Xs)` joining the block of `X` to the rest vanish. -/
private theorem listCartan_cons_apply_inl_inr (X : DynkinSymbol) (Xs : List DynkinSymbol)
    (a : Fin X.rank) (b : Fin (DynkinSymbol.listRank Xs)) :
    DynkinSymbol.listCartan (X :: Xs) (finSumFinEquiv (Sum.inl a))
      (finSumFinEquiv (Sum.inr b)) = 0 := by
  simp [DynkinSymbol.listCartan, reindex_apply]

/-- The entries of `C(X :: Xs)` joining the rest to the block of `X` vanish. -/
private theorem listCartan_cons_apply_inr_inl (X : DynkinSymbol) (Xs : List DynkinSymbol)
    (a : Fin (DynkinSymbol.listRank Xs)) (b : Fin X.rank) :
    DynkinSymbol.listCartan (X :: Xs) (finSumFinEquiv (Sum.inr a))
      (finSumFinEquiv (Sum.inl b)) = 0 := by
  simp [DynkinSymbol.listCartan, reindex_apply]

/-- The entries of `C(X :: Xs)` outside the block of `X` are those of `C(Xs)`. -/
private theorem listCartan_cons_apply_inr_inr (X : DynkinSymbol) (Xs : List DynkinSymbol)
    (a b : Fin (DynkinSymbol.listRank Xs)) :
    DynkinSymbol.listCartan (X :: Xs) (finSumFinEquiv (Sum.inr a))
      (finSumFinEquiv (Sum.inr b)) = DynkinSymbol.listCartan Xs a b := by
  simp [DynkinSymbol.listCartan, reindex_apply]

/-- `C([X])` is `C(X)`. -/
private theorem listCartan_singleton_apply (X : DynkinSymbol) (a b : Fin X.rank) :
    DynkinSymbol.listCartan [X] a b = X.cartan a b :=
  listCartan_cons_apply_inl_inl X [] a b

/-- Being of type `[X]` is being a simultaneous permutation of `C(X)`. -/
private theorem isOfDynkinType_singleton_iff {A : Matrix (Fin n) (Fin n) ℤ} {X : DynkinSymbol} :
    IsOfDynkinType A [X] ↔ ∃ σ : Fin n ≃ Fin X.rank, ∀ i j, A i j = X.cartan (σ i) (σ j) :=
  ⟨fun ⟨σ, h⟩ => ⟨σ, fun i j => (h i j).trans (listCartan_singleton_apply X _ _)⟩,
    fun ⟨σ, h⟩ => ⟨σ, fun i j => (h i j).trans (listCartan_singleton_apply X _ _).symm⟩⟩

/-- A matrix on any index type whose indices are split into blocks `s ∈ [1, r]`, with no
nonzero entry joining two blocks and the block `s` a simultaneous permutation of `C(X s)`, is a
simultaneous permutation of `C(X 1, …, X r)`. -/
private theorem exists_equiv_listCartan_ofFn_aux {ι : Type*} {r : ℕ} (A : ι → ι → ℤ)
    (b : ι → Fin r) (hsep : ∀ i j, b i ≠ b j → A i j = 0) (X : Fin r → DynkinSymbol)
    (e : ∀ s, {i // b i = s} ≃ Fin (X s).rank)
    (he : ∀ s (i j : {i // b i = s}), A i j = (X s).cartan (e s i) (e s j)) :
    ∃ σ : ι ≃ Fin (DynkinSymbol.listRank (List.ofFn X)),
      ∀ i j, A i j = DynkinSymbol.listCartan (List.ofFn X) (σ i) (σ j) := by
  induction r generalizing ι with
  | zero =>
    have : IsEmpty ι := ⟨fun i => (b i).elim0⟩
    rw [List.ofFn_zero]
    exact ⟨Equiv.equivOfIsEmpty ι (Fin 0), isEmptyElim⟩
  | succ r ih =>
    classical
    let b' : {i // b i ≠ 0} → Fin r := fun i => (b i).pred i.2
    have hb' : ∀ i, (b' i).succ = b i := fun i => Fin.succ_pred _ _
    let e' : ∀ s, {i // b' i = s} ≃ Fin (X s.succ).rank := fun s =>
      (show {i // b' i = s} ≃ {i // b i = s.succ} from
        { toFun := fun i => ⟨i.1.1, by rw [← hb', i.2]⟩
          invFun := fun i => ⟨⟨i.1, by simp [i.2]⟩, by simp [b', i.2]⟩
          left_inv := fun i => rfl
          right_inv := fun i => rfl }).trans (e s.succ)
    obtain ⟨σ', hσ'⟩ := ih (fun i j : {i // b i ≠ 0} => A i j) b'
      (fun i j h => hsep i j fun h' => h (Fin.succ_injective _ (by rw [hb', hb', h'])))
      (fun s => X s.succ) e'
      (fun s i j => he s.succ ⟨i.1.1, by rw [← hb', i.2]⟩ ⟨j.1.1, by rw [← hb', j.2]⟩)
    rw [List.ofFn_succ]
    let σ : ι ≃ Fin (DynkinSymbol.listRank (X 0 :: List.ofFn fun s => X s.succ)) :=
      (Equiv.sumCompl fun i => b i = 0).symm.trans
        ((Equiv.sumCongr (e 0) σ').trans finSumFinEquiv)
    have hσl : ∀ i (hi : b i = 0), σ i = finSumFinEquiv (Sum.inl (e 0 ⟨i, hi⟩)) := by
      intro i hi
      simp only [σ, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun i => b i = 0) hi,
        Equiv.sumCongr_apply, Sum.map_inl]
      rfl
    have hσr : ∀ i (hi : ¬b i = 0), σ i = finSumFinEquiv (Sum.inr (σ' ⟨i, hi⟩)) := by
      intro i hi
      simp only [σ, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun i => b i = 0) hi,
        Equiv.sumCongr_apply, Sum.map_inr]
      rfl
    refine ⟨σ, fun i j => ?_⟩
    by_cases hi : b i = 0 <;> by_cases hj : b j = 0
    · rw [hσl i hi, hσl j hj]
      exact (he 0 ⟨i, hi⟩ ⟨j, hj⟩).trans (listCartan_cons_apply_inl_inl _ _ _ _).symm
    · rw [hσl i hi, hσr j hj]
      exact (hsep i j (by omega)).trans (listCartan_cons_apply_inl_inr _ _ _ _).symm
    · rw [hσr i hi, hσl j hj]
      exact (hsep i j (by omega)).trans (listCartan_cons_apply_inr_inl _ _ _ _).symm
    · rw [hσr i hi, hσr j hj]
      exact (hσ' ⟨i, hi⟩ ⟨j, hj⟩).trans (listCartan_cons_apply_inr_inr _ _ _ _).symm

/-- **Every Cartan matrix of finite type has a type**, the precise form: if the indices of `A`
are partitioned into blocks `I₁, …, I_r`, no nonzero entry of `A` joins two different blocks,
and the principal submatrix `A_{I_s}` (indices in increasing order) is of type `X^s` for each
`s`, then `A` is of type `(X¹, …, X^r)`. The vertex sets of the connected components of the
Coxeter graph are such a partition. -/
@[cluster_algebras "lem_cartan_type_exists"]
theorem isOfDynkinType_ofFn_of_blocks {A : Matrix (Fin n) (Fin n) ℤ} {r : ℕ}
    (I : Fin r → Finset (Fin n)) (hcover : ∀ i, ∃! s, i ∈ I s)
    (hsep : ∀ s s', s ≠ s' → ∀ i ∈ I s, ∀ j ∈ I s', A i j = 0) (X : Fin r → DynkinSymbol)
    (hX : ∀ s, IsOfDynkinType (A.submatrix ((I s).orderEmbOfFin rfl) ((I s).orderEmbOfFin rfl))
      [X s]) :
    IsOfDynkinType A (List.ofFn X) := by
  classical
  let b : Fin n → Fin r := fun i => (hcover i).exists.choose
  have hb : ∀ i, i ∈ I (b i) := fun i => (hcover i).exists.choose_spec
  have hbI : ∀ i s, b i = s ↔ i ∈ I s := fun i s =>
    ⟨fun h => h ▸ hb i, fun h => (hcover i).unique (hb i) h⟩
  choose σ hσ using fun s => isOfDynkinType_singleton_iff.mp (hX s)
  let e : ∀ s, {i // b i = s} ≃ Fin (X s).rank := fun s =>
    ((Equiv.subtypeEquivRight fun i => hbI i s).trans
      ((I s).orderIsoOfFin rfl).symm.toEquiv).trans (σ s)
  refine exists_equiv_listCartan_ofFn_aux A b (fun i j h => hsep _ _ h i (hb i) j (hb j)) X e ?_
  intro s i j
  have key : ∀ x : {i // b i = s}, (x : Fin n) =
      (I s).orderEmbOfFin rfl (((I s).orderIsoOfFin rfl).symm ⟨x, (hbI x s).1 x.2⟩) := by
    intro x
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  exact (congrArg₂ A (key i) (key j)).trans (hσ s _ _)

/-- **Every Cartan matrix of finite type has a type**: some list `X` of Dynkin symbols with `A`
of type `X`. -/
@[cluster_algebras "lem_cartan_type_exists"]
theorem isOfDynkinType_of_isCartanFiniteType {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : IsCartanFiniteType A) : ∃ Xs : List DynkinSymbol, IsOfDynkinType A Xs := by
  classical
  let c := Fintype.equivFin (coxeterGraph A).ConnectedComponent
  let I : Fin _ → Finset (Fin n) := fun s =>
    Finset.univ.filter fun i => c ((coxeterGraph A).connectedComponentMk i) = s
  have hI : ∀ s i, i ∈ I s ↔ c ((coxeterGraph A).connectedComponentMk i) = s := by simp [I]
  have hX : ∀ s, ∃ X, IsOfDynkinType
      (A.submatrix ((I s).orderEmbOfFin rfl) ((I s).orderEmbOfFin rfl)) [X] := by
    intro s
    refine cartan_killing (hA.submatrix ((I s).orderEmbOfFin rfl).injective) ?_
    have hmem : ∀ i, i ∈ I s ↔ i ∈ (c.symm s).supp := fun i => by
      rw [hI, SimpleGraph.ConnectedComponent.mem_supp_iff, Equiv.eq_symm_apply]
    let φ : coxeterGraph (A.submatrix ((I s).orderEmbOfFin rfl) ((I s).orderEmbOfFin rfl)) ≃g
        (c.symm s).toSimpleGraph :=
      { toEquiv := ((I s).orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight hmem)
        map_rel_iff' := by
          intro a b
          change (coxeterGraph A).Adj ((I s).orderIsoOfFin rfl a) ((I s).orderIsoOfFin rfl b) ↔ _
          rw [coxeterGraph_adj, coxeterGraph_adj, Finset.coe_orderIsoOfFin_apply,
            Finset.coe_orderIsoOfFin_apply, ((I s).orderEmbOfFin rfl).injective.ne_iff]
          rfl }
    exact φ.connected_iff.mpr (c.symm s).connected_toSimpleGraph
  choose X hX using hX
  refine ⟨_, isOfDynkinType_ofFn_of_blocks I
    (fun i => ⟨c ((coxeterGraph A).connectedComponentMk i), (hI _ _).2 rfl,
      fun s hs => ((hI _ _).1 hs).symm⟩) ?_ X hX⟩
  intro s s' hss' i hi j hj
  by_contra h
  apply hss'
  rw [← (hI s i).1 hi, ← (hI s' j).1 hj]
  obtain rfl | hij := eq_or_ne i j
  · rfl
  · rw [SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (coxeterGraph_adj.2 ⟨hij, Or.inl h⟩)]

/-- The **Cartan counterpart** of an `n × n` integer matrix `B`: the matrix `A(B)` with
`aᵢᵢ = 2` and `aᵢⱼ = -|bᵢⱼ|` for `i ≠ j`. FWZ define it for skew-symmetrizable `B`;
the formula makes sense for every matrix. -/
@[cluster_algebras "def_cartan_counterpart"]
def cartanCounterpart (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if i = j then 2 else -|B i j|

/-- The entries of the Cartan counterpart `A(B)`. -/
theorem cartanCounterpart_apply (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    cartanCounterpart B i j = if i = j then 2 else -|B i j| := rfl

/-- The diagonal entries of the Cartan counterpart are `2`. -/
@[simp]
theorem cartanCounterpart_apply_self (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    cartanCounterpart B i i = 2 := by
  simp [cartanCounterpart_apply]

/-- The off-diagonal entries of the Cartan counterpart are `aᵢⱼ = -|bᵢⱼ|`. -/
@[simp]
theorem cartanCounterpart_apply_of_ne (B : Matrix (Fin n) (Fin n) ℤ) {i j : Fin n}
    (hij : i ≠ j) : cartanCounterpart B i j = -|B i j| := by
  simp [cartanCounterpart_apply, hij]

/-- `diag(d₁, …, dₙ)` symmetrizes the Cartan counterpart of `B` for any skew-symmetrizing
vector `d` of `B`. -/
theorem IsSkewSymmetrizingVector.isSymmetrizer_cartanCounterpart
    {B : Matrix (Fin n) (Fin n) ℤ} {d : Fin n → ℤ} (hd : IsSkewSymmetrizingVector B d) :
    IsSymmetrizer (cartanCounterpart B) d := by
  refine ⟨hd.1, fun i j => ?_⟩
  obtain rfl | hij := eq_or_ne i j
  · rfl
  · have h := congrArg abs (hd.2 i j)
    simp only [Int.cast_id, abs_mul, abs_neg, abs_of_pos (hd.1 i), abs_of_pos (hd.1 j)] at h
    simp only [cartanCounterpart, of_apply, if_neg hij, if_neg (Ne.symm hij), mul_neg, h]

/-- **The Cartan counterpart is a symmetrizable generalized Cartan matrix**, with symmetrizer
`diag(d₁, …, dₙ)` for any skew-symmetrizing vector `d` of `B`. -/
@[cluster_algebras "lem_cartan_counterpart_generalized"]
theorem IsSkewSymmetrizingVector.isGeneralizedCartan_cartanCounterpart
    {B : Matrix (Fin n) (Fin n) ℤ} {d : Fin n → ℤ} (hd : IsSkewSymmetrizingVector B d) :
    IsGeneralizedCartan (cartanCounterpart B) ∧ IsSymmetrizer (cartanCounterpart B) d :=
  ⟨⟨cartanCounterpart_apply_self B, fun _ _ hij => by simp [hij], d,
    hd.isSymmetrizer_cartanCounterpart⟩, hd.isSymmetrizer_cartanCounterpart⟩

variable {F : Type*} [Field F] {m : ℕ}

/-- A seed pattern `P` of rank `n` is **of type `X`**, for a list `X` of Dynkin symbols of total
rank `n`, when for some vertex `t` the Cartan counterpart of the exchange matrix of `P t` is of
type `X`. For a single symbol the list is `[X]`. This imposes no condition on the frozen rows. -/
@[cluster_algebras "def_pattern_type"]
def IsPatternOfType (hmn : n ≤ m) (P : RegularTree n → SeedData F m n)
    (Xs : List DynkinSymbol) : Prop :=
  ∃ t, IsOfDynkinType (cartanCounterpart (principalPart hmn (P t).extExchangeMatrix)) Xs

end ClusterAlgebras

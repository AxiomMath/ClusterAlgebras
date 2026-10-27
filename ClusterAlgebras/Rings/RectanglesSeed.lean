/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.RectanglesQuiver
public import ClusterAlgebras.Rings.FreeTuple
public import ClusterAlgebras.Rings.Basic
public import ClusterAlgebras.Rings.Rotation
public import ClusterAlgebras.Rings.MinorIrreducible

/-!
# The rectangles seed is a labeled seed

Let `1 ≤ a ≤ b`, `c = b - a`, and let `z` be the generic `a × b` matrix over `ℂ`. The Plücker
coordinates `P_{J(v)}(z)` of the labels of the rectangles `v ∈ V_{a,b}` are algebraically
independent over `ℂ`. The proof is by induction on `a`, with `c` fixed. For `a = 1` the family is
the family of indeterminates `z_{11}, …, z_{1b}`. For the step from `(a, b)` to `(a + 1, b + 1)`,
the specialization `θ` sending the last column of `z` to the last unit vector maps `P_{J(v)}`, for
`v` a rectangle of height at most `a`, to the Plücker coordinate `P_{J'(v)}(z')` of the top-left
`a × b` block `z'` (expansion along the last column), and fixes the `c` coordinates `P_{J(a+1,q)}`
of the rectangles of full height, whose labels are the windows `[j, j + a]` of consecutive columns,
`j < c`. By expansion along the last row, `P_{[j, j+a]} = u_j z_{a+1, j+a+1} + h_j` with
`u_j = P_{[j, j+a-1]}(z') ≠ 0` and `u_j`, `h_j` involving only the entries of `z'` and the entries
`z_{a+1, i}` with `i ≤ j + a`. Adjoining such elements one at a time preserves algebraic
independence: an element `u X_s + h` with `u ≠ 0` and `u`, `h` free of the variable `X_s` is
transcendental over any algebra of polynomials free of `X_s`.

Consequently every cyclic shift `Σ^i_{a,b}(λ)` of the rectangles seed, the image of `Σ_{a,b}(λ)`
under the automorphism `ρ^{-i}` of `ℂ[z]`, has algebraically independent entries; its matrix is the
extended exchange matrix of the rectangles quiver, whose principal part is skew-symmetric. So
`Σ_{a,b}(λ)` is a labeled seed over `ℂ` in the field its entries generate, and a rectangle
labelling has `m = a(b - a) + 1` and `n = (a - 1)(b - a - 1)`, which is at least `1` when
`2 ≤ a ≤ b - 2`.

## Main results

* `ClusterAlgebras.algebraicIndependent_optionElim_mul_X_add`,
  `ClusterAlgebras.algebraicIndependent_sumElim_mul_X_add`: adjoining polynomials `u X_s + h`,
  triangular in fresh variables, to an algebraically independent family.
* `ClusterAlgebras.algebraicIndependent_pluckerCoord_rectLabel`: the Plücker coordinates of the
  rectangles labels are algebraically independent.
* `ClusterAlgebras.extSkewSymmetrizable_extExchangeMatrix`: the extended exchange matrix of a
  labelled quiver is extended skew-symmetrizable.
* `ClusterAlgebras.isLabeledSeed_rectanglesSeedShift`: every cyclic shift `Σ^i_{a,b}(λ)` is a
  labeled seed in the field its entries generate.
* `ClusterAlgebras.isLabeledSeed_rectanglesSeed`, `ClusterAlgebras.RectangleLabelling.one_le_n`:
  the rectangles seed is a labeled seed, with `n ≥ 1`.
* `ClusterAlgebras.RectangleLabelling.m_eq`, `ClusterAlgebras.RectangleLabelling.n_eq`: the sizes
  `m = a(b - a) + 1` and `n = (a - 1)(b - a - 1)` of a rectangle labelling.

## Implementation notes

* FWZ state the algebraic independence of the Plücker coordinates for `1 ≤ a < b`; it
  holds, with the same proof, for `1 ≤ a ≤ b`, which is how it is stated. For `a = b` the only
  rectangle is `∅`, with `P_{J(∅)} = det z`.
* FWZ state that the rectangles seed is a labeled seed for `2 ≤ a ≤ b - 2`. That
  `Σ_{a,b}(λ)` is a labeled seed holds for `1 ≤ a ≤ b`, and is stated so; the hypothesis
  `2 ≤ a ≤ b - 2` is what gives `n ≥ 1`, which is `RectangleLabelling.one_le_n`.
* FWZ prove the triangularity of the full-height coordinates by a transcendence-degree
  count over `L = ℂ(z')`. Here it is the one-variable statement
  `algebraicIndependent_optionElim_mul_X_add`, applied `c` times along the windows in increasing
  order; "free of the variable `X_s`" is membership in `MvPolynomial.supported` of a set of
  variables not containing `s`.
* With the 0-based indices used here, the window of the rectangle `some (a, q)` of
  `V_{a+1,b+1}` is `[j, j + a]` with `j = c - 1 - q`, and the specialization `θ` sends the
  column `b` (the last of `b + 1`) to the unit vector of the row `a` (the last of `a + 1`).

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6.
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial

/-! ### Adjoining polynomials linear in a fresh variable -/

section Adjoin

variable {k σ ι : Type*} [CommRing k]

/-- The ring homomorphism `k[X_σ] → k[X_σ][Y]` sending `X_s` to `Y` and every other variable to
the constant `X_t` restricts to the constant embedding on the polynomials free of `X_s`. -/
private theorem eval₂Hom_eq_C_of_mem_supported [DecidableEq σ] {T : Set σ} {s : σ} (hs : s ∉ T)
    {p : MvPolynomial σ k} (hp : p ∈ supported k T) :
    eval₂Hom (Polynomial.C.comp C)
      (fun t => if t = s then Polynomial.X else Polynomial.C (X t)) p = Polynomial.C p := by
  refine hom_congr_vars (by ext; simp) (fun i hi _ => ?_) rfl
  simp [show i ≠ s from fun h => hs (h ▸ (mem_supported.1 hp) hi)]

/-- **Adjoining an element linear in a fresh variable.** If the family `x` is algebraically
independent and its members involve only the variables of `T`, and `s ∉ T`, then for `u ≠ 0`
and `h` involving only the variables of `T`, the family `x` together with `u X_s + h` is
algebraically independent: `u X_s + h` is transcendental over the polynomials free of `X_s`. -/
theorem algebraicIndependent_optionElim_mul_X_add [IsDomain k] {x : ι → MvPolynomial σ k}
    (hx : AlgebraicIndependent k x) {T : Set σ} (hxT : ∀ i, x i ∈ supported k T) {s : σ}
    (hs : s ∉ T) {u h : MvPolynomial σ k} (hu : u ∈ supported k T) (hu0 : u ≠ 0)
    (hh : h ∈ supported k T) :
    AlgebraicIndependent k fun o : Option ι => o.elim (u * X s + h) x := by
  classical
  refine AlgebraicIndependent.option_iff.2 ⟨hx, ?_⟩
  have hA : Algebra.adjoin k (Set.range x) ≤ supported k T :=
    Algebra.adjoin_le (Set.range_subset_iff.2 hxT)
  set ε : MvPolynomial σ k →+* Polynomial (MvPolynomial σ k) := eval₂Hom (Polynomial.C.comp C)
      (fun t => if t = s then Polynomial.X else Polynomial.C (X t)) with hε
  have hεC : ε.comp (algebraMap (Algebra.adjoin k (Set.range x)) (MvPolynomial σ k)) =
      Polynomial.C.comp (Algebra.adjoin k (Set.range x)).val.toRingHom :=
    RingHom.ext fun a => eval₂Hom_eq_C_of_mem_supported hs (hA a.2)
  have hεg : ε (u * X s + h) = Polynomial.C u * Polynomial.X + Polynomial.C h := by
    simp only [map_add, map_mul, hε, eval₂Hom_eq_C_of_mem_supported hs hu,
      eval₂Hom_eq_C_of_mem_supported hs hh]
    simp
  rw [transcendental_iff_injective, injective_iff_map_eq_zero]
  intro q hq
  have h1 := congrArg ε hq
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hεC, hεg, map_zero,
    ← Polynomial.eval₂_map, ← Polynomial.comp, Polynomial.comp_eq_zero_iff] at h1
  rcases h1 with h1 | ⟨-, h1⟩
  · exact Polynomial.map_injective _ Subtype.val_injective (by simpa using h1)
  · have h2 := congrArg (Polynomial.coeff · 1) h1
    simp only [Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_C_zero,
      Polynomial.coeff_C_succ, add_zero, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero,
      mul_zero, zero_add] at h2
    exact absurd h2 hu0

/-- `Option (ι ⊕ Fin r) ≃ ι ⊕ Fin (r + 1)`, with `none ↦ inr r`. -/
private def optionSumFinSuccEquiv (ι : Type*) (r : ℕ) : Option (ι ⊕ Fin r) ≃ ι ⊕ Fin (r + 1) where
  toFun o := o.elim (Sum.inr (Fin.last r)) (Sum.map id Fin.castSucc)
  invFun := Sum.elim (fun i => some (Sum.inl i))
    (fun j => Fin.lastCases none (fun i => some (Sum.inr i)) j)
  left_inv o := by rcases o with _ | i | i <;> simp
  right_inv o := by
    rcases o with i | j
    · simp
    · induction j using Fin.lastCases <;> simp

/-- **Adjoining a triangular family.** Let `x` be algebraically independent with members
involving only the variables of `T 0`, where `T` is an increasing sequence of sets of variables.
If for each `j < r` the variable `s_j` lies in `T (j + 1)` but not in `T j`, and `u_j ≠ 0` and
`h_j` involve only the variables of `T j`, then `x` together with the `u_j X_{s_j} + h_j` is
algebraically independent. -/
theorem algebraicIndependent_sumElim_mul_X_add [IsDomain k] {x : ι → MvPolynomial σ k}
    (hx : AlgebraicIndependent k x) {T : ℕ → Set σ} (hT : Monotone T)
    (hxT : ∀ i, x i ∈ supported k (T 0)) {r : ℕ} {s : Fin r → σ}
    {u h : Fin r → MvPolynomial σ k} (hs : ∀ j : Fin r, s j ∉ T j)
    (hsT : ∀ j : Fin r, s j ∈ T (j + 1)) (hu : ∀ j : Fin r, u j ∈ supported k (T j))
    (hu0 : ∀ j, u j ≠ 0) (hh : ∀ j : Fin r, h j ∈ supported k (T j)) :
    AlgebraicIndependent k (Sum.elim x fun j => u j * X (s j) + h j) := by
  induction r with
  | zero =>
    rw [← algebraicIndependent_equiv (Equiv.sumEmpty ι (Fin 0)).symm]
    exact hx
  | succ r ih =>
    have hS : ∀ {j : ℕ}, j ≤ r → supported k (T j) ≤ supported k (T r) :=
      fun hj => supported_mono (hT hj)
    have h1 := ih (s := s ∘ Fin.castSucc) (u := u ∘ Fin.castSucc) (h := h ∘ Fin.castSucc)
      (fun j => hs (Fin.castSucc j)) (fun j => hsT (Fin.castSucc j))
      (fun j => hu (Fin.castSucc j)) (fun j => hu0 (Fin.castSucc j))
      (fun j => hh (Fin.castSucc j))
    have h2 := algebraicIndependent_optionElim_mul_X_add h1 ?_ (hs (Fin.last r))
      (hu (Fin.last r)) (hu0 (Fin.last r)) (hh (Fin.last r))
    · rw [← algebraicIndependent_equiv (optionSumFinSuccEquiv ι r)]
      convert h2 using 1
      ext (_ | i | i) <;> rfl
    · rintro (i | j)
      · exact hS (Nat.zero_le _) (hxT i)
      · have hj : (j : ℕ) + 1 ≤ r := j.isLt
        refine add_mem (mul_mem (hS (Nat.le_of_succ_le hj) (hu (Fin.castSucc j))) ?_)
          (hS (Nat.le_of_succ_le hj) (hh (Fin.castSucc j)))
        exact (X_mem_supported).2 (hT hj (hsT (Fin.castSucc j)))

end Adjoin

/-! ### Minors along order embeddings -/

section Minors

variable {R : Type*} [CommRing R]

/-- The minor on the images of two order embeddings `f`, `g` of `Fin k` is the determinant of
the submatrix they cut out. -/
theorem minor_map_orderEmbedding {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (z : Matrix ι κ R) {k : ℕ} (f : Fin k ↪o ι) (g : Fin k ↪o κ) :
    minor z (Finset.univ.map f.toEmbedding) (Finset.univ.map g.toEmbedding) =
      (z.submatrix f g).det := by
  have hf : (Finset.univ.map f.toEmbedding).card = k := by simp
  have hg : (Finset.univ.map g.toEmbedding).card = k := by simp
  rw [minor_of_card_eq z hf hg, ← Finset.orderEmbOfFin_unique' hf (f := f) (by simp),
    ← Finset.orderEmbOfFin_unique' hg (f := g) (by simp)]

/-- The Plücker coordinate on the image of an order embedding `g` of `Fin k` is the determinant
of the columns `g`. -/
theorem pluckerCoord_map_orderEmbedding {κ : Type*} [LinearOrder κ] {k : ℕ}
    (z : Matrix (Fin k) κ R) (g : Fin k ↪o κ) :
    pluckerCoord z (Finset.univ.map g.toEmbedding) = (z.submatrix id g).det := by
  have hg : (Finset.univ.map g.toEmbedding).card = k := by simp
  rw [pluckerCoord_eq_det z hg, ← Finset.orderEmbOfFin_unique' hg (f := g) (by simp)]

/-- A determinant whose entries lie in a subring lies in it. -/
theorem det_mem_of_forall_mem {S : Type*} [SetLike S R] [SubringClass S R] {s : S}
    {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n R} (hM : ∀ i j, M i j ∈ s) :
    M.det ∈ s := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => hM _ _) _

end Minors

/-! ### Specializing the last column -/

section Specialization

variable {a b : ℕ}

/-- The order embedding `Fin (a + 1) ↪o Fin (b + 1)` extending `f : Fin a ↪o Fin b` by
`a ↦ b`. -/
private def snocLastOrderEmb (f : Fin a ↪o Fin b) : Fin (a + 1) ↪o Fin (b + 1) :=
  OrderEmbedding.ofStrictMono
    (fun k => if h : (k : ℕ) < a then (f ⟨k, h⟩).castSucc else Fin.last b) (by
      intro i j hij
      have hj := j.isLt
      by_cases hja : (j : ℕ) < a
      · have hia : (i : ℕ) < a := lt_trans hij hja
        simp only [hia, hja, dite_true, Fin.castSucc_lt_castSucc_iff]
        exact f.strictMono (Fin.mk_lt_mk.2 hij)
      · have hia : (i : ℕ) < a := by omega
        simp only [hia, hja, dite_true, dite_false]
        exact Fin.castSucc_lt_last _)

@[simp] private theorem snocLastOrderEmb_castSucc (f : Fin a ↪o Fin b) (i : Fin a) :
    snocLastOrderEmb f i.castSucc = (f i).castSucc := by
  simp [snocLastOrderEmb]

@[simp] private theorem snocLastOrderEmb_last (f : Fin a ↪o Fin b) :
    snocLastOrderEmb f (Fin.last a) = Fin.last b := by
  simp [snocLastOrderEmb]

variable (a b) in
/-- The specialization `θ` of `ℂ[z]`, `z` the generic `(a + 1) × (b + 1)` matrix, sending the
last column of `z` to the last unit vector and fixing the other entries. -/
private noncomputable def lastColumnSpecialization :
    ComplexPoly (a + 1) (b + 1) →ₐ[ℂ] ComplexPoly (a + 1) (b + 1) :=
  aeval fun t => if t.2 = Fin.last b then (if t.1 = Fin.last a then 1 else 0) else X t

private theorem lastColumnSpecialization_X_of_ne {t : Fin (a + 1) × Fin (b + 1)}
    (ht : t.2 ≠ Fin.last b) : lastColumnSpecialization a b (X t) = X t := by
  simp [lastColumnSpecialization, ht]

private theorem lastColumnSpecialization_X_last (i : Fin (a + 1)) :
    lastColumnSpecialization a b (X (i, Fin.last b)) = if i = Fin.last a then 1 else 0 := by
  simp [lastColumnSpecialization]

/-- `θ(P_{J ∪ {b}}(z)) = P_J(z')`, `z'` the top-left `a × b` block of `z`: expansion along the
last column. -/
private theorem lastColumnSpecialization_pluckerCoord (J : Finset (Fin b)) :
    lastColumnSpecialization a b (pluckerCoord (complexGenericMatrix (a + 1) (b + 1))
      (J.map Fin.castSuccEmb ∪ {Fin.last b})) =
      rename (Prod.map Fin.castSucc Fin.castSucc) (pluckerCoord (complexGenericMatrix a b) J) := by
  by_cases hJ : J.card = a
  · set f := J.orderEmbOfFin hJ
    have hJF : J.map Fin.castSuccEmb ∪ {Fin.last b} =
        Finset.univ.map (snocLastOrderEmb f).toEmbedding := by
      symm
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hx
        induction k using Fin.lastCases with
        | last => simp
        | cast i => simp [f, Finset.orderEmbOfFin_mem]
      · refine (Finset.card_union_le _ _).trans ?_
        simp [hJ]
    rw [hJF, pluckerCoord_map_orderEmbedding, pluckerCoord_eq_det _ hJ, AlgHom.map_det,
      AlgHom.map_det, Matrix.det_succ_column _ (Fin.last a),
      Fintype.sum_eq_single (Fin.last a)]
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
        snocLastOrderEmb_last, complexGenericMatrix_apply, lastColumnSpecialization_X_last,
        if_true, Fin.succAbove_last, mul_one]
      rw [Even.neg_one_pow ⟨_, rfl⟩, one_mul]
      congr 1
      ext r k
      simp [lastColumnSpecialization_X_of_ne, Fin.castSucc_ne_last, f]
    · intro i hi
      simp [lastColumnSpecialization_X_last, hi]
  · simp [pluckerCoord, minor, hJ]

variable (a b) in
/-- The window `[j, j + a]` of `a + 1` consecutive columns among `b + 1`, for `j < b - a`. -/
private def windowOrderEmb (j : Fin (b - a)) : Fin (a + 1) ↪o Fin (b + 1) :=
  OrderEmbedding.ofStrictMono (fun k => ⟨j + k, by omega⟩) fun _ _ h =>
    Fin.mk_lt_mk.2 (by omega)

@[simp] private theorem val_windowOrderEmb (j : Fin (b - a)) (k : Fin (a + 1)) :
    (windowOrderEmb a b j k : ℕ) = j + k := rfl

variable (a b) in
/-- The square submatrix of `z` on the columns of the window `[j, j + a]`. -/
private noncomputable def windowMatrix (j : Fin (b - a)) :
    Matrix (Fin (a + 1)) (Fin (a + 1)) (ComplexPoly (a + 1) (b + 1)) :=
  (complexGenericMatrix (a + 1) (b + 1)).submatrix id (windowOrderEmb a b j)

private theorem windowMatrix_apply (j : Fin (b - a)) (r k : Fin (a + 1)) :
    windowMatrix a b j r k = X (r, windowOrderEmb a b j k) := by
  simp [windowMatrix]

/-- `θ` fixes the window coordinate `P_{[j, j+a]}`, and expanding it along the last row writes it
as `u_j z_{a, j+a} + h_j`. -/
private theorem lastColumnSpecialization_pluckerCoord_window (j : Fin (b - a)) :
    lastColumnSpecialization a b (pluckerCoord (complexGenericMatrix (a + 1) (b + 1))
      (Finset.univ.map (windowOrderEmb a b j).toEmbedding)) =
      ((windowMatrix a b j).submatrix Fin.castSucc Fin.castSucc).det *
        X (Fin.last a, ⟨a + j, by omega⟩) +
      ∑ k : Fin a, (-1) ^ (a + (k : ℕ)) * windowMatrix a b j (Fin.last a) k.castSucc *
        ((windowMatrix a b j).submatrix Fin.castSucc k.castSucc.succAbove).det := by
  have hM : (lastColumnSpecialization a b).mapMatrix (windowMatrix a b j) =
      windowMatrix a b j := by
    refine Matrix.ext fun r k => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, windowMatrix, Matrix.submatrix_apply,
      id, complexGenericMatrix_apply]
    refine lastColumnSpecialization_X_of_ne fun h => ?_
    have := congrArg Fin.val h
    simp only [val_windowOrderEmb, Fin.val_last] at this
    omega
  have hlast : windowMatrix a b j (Fin.last a) (Fin.last a) =
      X (Fin.last a, ⟨a + j, by omega⟩) := by
    simp only [windowMatrix, Matrix.submatrix_apply, id, complexGenericMatrix_apply]
    congr 2
    ext
    simp [add_comm]
  have hsign : (-1 : ComplexPoly (a + 1) (b + 1)) ^ ((Fin.last a : ℕ) + (Fin.last a : ℕ)) = 1 :=
    Even.neg_one_pow ⟨a, rfl⟩
  rw [pluckerCoord_map_orderEmbedding, AlgHom.map_det, ← windowMatrix, hM,
    Matrix.det_succ_row _ (Fin.last a), Fin.sum_univ_castSucc, hsign, hlast]
  simp only [Fin.succAbove_last, Fin.val_last, Fin.val_castSucc, one_mul]
  ring

/-- The leading coefficient `u_j = P_{[j, j+a-1]}(z')` is nonzero, a minor of the generic
matrix. -/
private theorem det_windowMatrix_ne_zero (ha : 1 ≤ a) (j : Fin (b - a)) :
    ((windowMatrix a b j).submatrix Fin.castSucc Fin.castSucc).det ≠ 0 := by
  have h : (windowMatrix a b j).submatrix Fin.castSucc Fin.castSucc =
      (complexGenericMatrix (a + 1) (b + 1)).submatrix Fin.castSuccOrderEmb
        (Fin.castSuccOrderEmb.trans (windowOrderEmb a b j)) := rfl
  rw [h, ← minor_map_orderEmbedding]
  have : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  exact (irreducible_minor_complexGenericMatrix (Finset.map_nonempty.2 Finset.univ_nonempty)
    (by simp)).ne_zero

variable (a b) in
/-- The variables allowed at the `i`-th adjunction: the entries of the top-left `a × b` block `z'`
and the entries `z_{a, k}` of the last row with `k < a + i`. -/
private def lastRowVars (i : ℕ) : Set (Fin (a + 1) × Fin (b + 1)) :=
  {t | (t.1 : ℕ) < a ∧ (t.2 : ℕ) < b ∨ (t.1 : ℕ) = a ∧ (t.2 : ℕ) < a + i}

private theorem monotone_lastRowVars : Monotone (lastRowVars a b) := by
  intro i i' hii t ht
  rcases ht with ht | ht
  · exact Or.inl ht
  · exact Or.inr ⟨ht.1, by omega⟩

/-- The polynomials in the entries of `z'` lie in `supported ℂ (lastRowVars a b 0)`. -/
private theorem rename_castSucc_mem_supported (p : MvPolynomial (Fin a × Fin b) ℂ) :
    rename (Prod.map Fin.castSucc Fin.castSucc) p ∈ supported ℂ (lastRowVars a b 0) := by
  classical
  refine mem_supported.2 fun t ht => ?_
  obtain ⟨t', -, rfl⟩ := Finset.mem_image.1 (vars_rename _ _ ht)
  exact Or.inl ⟨t'.1.isLt, t'.2.isLt⟩

/-- The leading coefficient `u_j` lies in `supported ℂ (lastRowVars a b j)`. -/
private theorem det_windowMatrix_mem_supported (j : Fin (b - a)) :
    ((windowMatrix a b j).submatrix Fin.castSucc Fin.castSucc).det ∈
      supported ℂ (lastRowVars a b j) :=
  det_mem_of_forall_mem fun r k => by
    rw [Matrix.submatrix_apply, windowMatrix_apply]
    refine X_mem_supported.2 (Or.inl ⟨by simp, ?_⟩)
    have := j.isLt
    have := k.isLt
    simp only [val_windowOrderEmb, Fin.val_castSucc]
    omega

/-- The remainder `h_j` lies in `supported ℂ (lastRowVars a b j)`. -/
private theorem sum_windowMatrix_mem_supported (j : Fin (b - a)) :
    ∑ k : Fin a, (-1) ^ (a + (k : ℕ)) * windowMatrix a b j (Fin.last a) k.castSucc *
        ((windowMatrix a b j).submatrix Fin.castSucc k.castSucc.succAbove).det ∈
      supported ℂ (lastRowVars a b j) := by
  refine Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) ?_)
    (det_mem_of_forall_mem fun r l => ?_)
  · rw [windowMatrix_apply]
    refine X_mem_supported.2 (Or.inr ⟨by simp, ?_⟩)
    have := k.isLt
    simp only [val_windowOrderEmb, Fin.val_castSucc]
    omega
  · rw [Matrix.submatrix_apply, windowMatrix_apply]
    refine X_mem_supported.2 (Or.inl ⟨by simp, ?_⟩)
    have := j.isLt
    have := l.isLt
    have := (k.castSucc.succAbove l).isLt
    simp only [val_windowOrderEmb]
    omega

end Specialization

/-! ### The rectangles coordinates are algebraically independent -/

section Independent

/-- The column of the one-element label of a rectangle of `V_{1,b+1}`. -/
private def rectColumnOne (b : ℕ) : RectVertex 1 (b + 1) → Fin (b + 1)
  | none => Fin.last b
  | some (_, q) => ⟨b - 1 - q, by omega⟩

private theorem rectLabel_one (b : ℕ) (v : RectVertex 1 (b + 1)) :
    rectLabel 1 (b + 1) v = {rectColumnOne b v} := by
  rcases v with _ | ⟨p, q⟩
  · ext x
    have := x.isLt
    simp [rectLabel, rectColumnOne, Fin.ext_iff]
    omega
  · ext x
    have := x.isLt
    have := q.isLt
    have := p.isLt
    simp [rectLabel, rectColumnOne, Fin.ext_iff]
    omega

private theorem rectColumnOne_injective (b : ℕ) : Function.Injective (rectColumnOne b) := by
  rintro (_ | ⟨p, q⟩) (_ | ⟨p', q'⟩) h
  · rfl
  · have := q'.isLt
    simp [rectColumnOne, Fin.ext_iff] at h
    omega
  · have := q.isLt
    simp [rectColumnOne, Fin.ext_iff] at h
    omega
  · have := q.isLt
    have := q'.isLt
    obtain rfl : p = p' := Subsingleton.elim _ _
    simp [rectColumnOne, Fin.ext_iff] at h
    congr
    ext
    omega

/-- The base case `a = 1`: the family is the family of indeterminates `z_{1j}`. -/
private theorem algebraicIndependent_rect_one (b : ℕ) :
    AlgebraicIndependent ℂ fun v : RectVertex 1 (b + 1) =>
      pluckerCoord (complexGenericMatrix 1 (b + 1)) (rectLabel 1 (b + 1) v) := by
  have := (algebraicIndependent_X (Fin 1 × Fin (b + 1)) ℂ).comp
    (fun v => ((0 : Fin 1), rectColumnOne b v))
    fun v w h => rectColumnOne_injective b (Prod.ext_iff.1 h).2
  convert this using 1
  funext v
  rw [rectLabel_one, pluckerCoord_eq_det _ (Finset.card_singleton _), Matrix.det_unique]
  simp

/-- The labels of `V_{a,b}` inside `V_{a+1,b+1}`: `J_{a+1,b+1}(v) = J_{a,b}(v) ∪ {b + 1}`. -/
private theorem rectLabel_rectVertexEmbedding_succ (a b : ℕ) (v : RectVertex a b) :
    rectLabel (a + 1) (b + 1) (rectVertexEmbedding (a + 1) (b + 1) v) =
      (rectLabel a b v).map Fin.castSuccEmb ∪ {Fin.last b} := by
  rw [rectLabel_rectVertexEmbedding (by omega) (by omega)]
  rfl

/-- The label of the full-height rectangle `(a + 1, c - j)` is the window `[j, j + a]`. -/
private theorem rectLabel_last_row (a b : ℕ) (j : Fin (b - a)) :
    rectLabel (a + 1) (b + 1) (some (Fin.last a, ⟨b - a - 1 - j, by omega⟩)) =
      Finset.univ.map (windowOrderEmb a b j).toEmbedding := by
  ext x
  have := x.isLt
  have := j.isLt
  simp only [rectLabel, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    RelEmbedding.coe_toEmbedding, Fin.val_last]
  constructor
  · intro h
    exact ⟨⟨x - j, by omega⟩, Fin.ext (by simp; omega)⟩
  · rintro ⟨k, rfl⟩
    have := k.isLt
    simp only [val_windowOrderEmb]
    omega

private theorem rectVertexEmbedding_ne_last (a b : ℕ) (v : RectVertex a b)
    (q : Fin (b + 1 - (a + 1))) : rectVertexEmbedding (a + 1) (b + 1) v ≠ some (Fin.last a, q) := by
  rcases v with _ | ⟨p, q'⟩
  · intro h
    have h' : (none : RectVertex (a + 1) (b + 1)) = some (Fin.last a, q) := h
    simp at h'
  · intro h
    have h' : (some (Fin.castLE (Nat.sub_le (a + 1) 1) p, Fin.castLE (by omega) q') :
        RectVertex (a + 1) (b + 1)) = some (Fin.last a, q) := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    have h1 := congrArg Fin.val h'.1
    have := p.isLt
    simp only [Fin.val_castLE, Fin.val_last] at h1
    omega

/-- `V_{a+1,b+1}` is `V_{a,b}` together with the `b - a` full-height rectangles. -/
private def rectVertexSum (a b : ℕ) : RectVertex a b ⊕ Fin (b - a) → RectVertex (a + 1) (b + 1) :=
  Sum.elim (rectVertexEmbedding (a + 1) (b + 1)) fun j =>
    some (Fin.last a, ⟨b - a - 1 - j, by omega⟩)

private theorem rectVertexSum_bijective (a b : ℕ) : Function.Bijective (rectVertexSum a b) := by
  constructor
  · rintro (v | j) (w | j') h
    · exact congrArg Sum.inl ((rectVertexEmbedding (a + 1) (b + 1)).injective h)
    · exact absurd h (rectVertexEmbedding_ne_last a b v _)
    · exact absurd h.symm (rectVertexEmbedding_ne_last a b w _)
    · have := j.isLt
      have := j'.isLt
      simp only [rectVertexSum, Sum.elim_inr, Option.some.injEq, Prod.mk.injEq, true_and,
        Fin.ext_iff] at h
      exact congrArg Sum.inr (Fin.ext (by omega))
  · rintro (_ | ⟨p, q⟩)
    · exact ⟨Sum.inl none, rfl⟩
    · have := p.isLt
      have := q.isLt
      by_cases hp : (p : ℕ) = a
      · refine ⟨Sum.inr ⟨b - a - 1 - q, by omega⟩, ?_⟩
        simp only [rectVertexSum, Sum.elim_inr, Option.some.injEq, Prod.mk.injEq]
        exact ⟨Fin.ext hp.symm, Fin.ext (by simp; omega)⟩
      · exact ⟨Sum.inl (some (⟨p, by omega⟩, ⟨q, by omega⟩)), rfl⟩

/-- The induction step, from `(a, b)` to `(a + 1, b + 1)`. -/
private theorem algebraicIndependent_rect_succ (a b : ℕ) (ha : 1 ≤ a)
    (ih : AlgebraicIndependent ℂ fun v : RectVertex a b =>
      pluckerCoord (complexGenericMatrix a b) (rectLabel a b v)) :
    AlgebraicIndependent ℂ fun v : RectVertex (a + 1) (b + 1) =>
      pluckerCoord (complexGenericMatrix (a + 1) (b + 1)) (rectLabel (a + 1) (b + 1) v) := by
  rw [← algebraicIndependent_equiv (Equiv.ofBijective _ (rectVertexSum_bijective a b))]
  refine AlgebraicIndependent.of_comp (lastColumnSpecialization a b) ?_
  have hx := ih.map' (f := rename (Prod.map Fin.castSucc Fin.castSucc))
    (rename_injective _ ((Fin.castSucc_injective _).prodMap (Fin.castSucc_injective _)))
  have key := algebraicIndependent_sumElim_mul_X_add hx monotone_lastRowVars
    (fun _ => rename_castSucc_mem_supported _)
    (s := fun j : Fin (b - a) => (Fin.last a, ⟨a + j, by omega⟩))
    (u := fun j => ((windowMatrix a b j).submatrix Fin.castSucc Fin.castSucc).det)
    (h := fun j => ∑ k : Fin a, (-1) ^ (a + (k : ℕ)) *
      windowMatrix a b j (Fin.last a) k.castSucc *
        ((windowMatrix a b j).submatrix Fin.castSucc k.castSucc.succAbove).det)
    (fun j h => by rcases h with h | h <;> simp at h)
    (fun j => Or.inr ⟨by simp, by simp⟩)
    det_windowMatrix_mem_supported (det_windowMatrix_ne_zero ha) sum_windowMatrix_mem_supported
  convert key using 1
  funext v
  rcases v with v | j
  · simp only [Function.comp_apply, Equiv.ofBijective_apply, rectVertexSum, Sum.elim_inl]
    rw [rectLabel_rectVertexEmbedding_succ, lastColumnSpecialization_pluckerCoord]
  · simp only [Function.comp_apply, Equiv.ofBijective_apply, rectVertexSum, Sum.elim_inr]
    rw [rectLabel_last_row, lastColumnSpecialization_pluckerCoord_window]

/-- **The rectangles coordinates are algebraically independent.** For `1 ≤ a ≤ b`, the Plücker
coordinates `P_{J(v)}(z)`, `v ∈ V_{a,b}`, of the generic `a × b` matrix over `ℂ` are
algebraically independent over `ℂ`. FWZ assume `a < b`. -/
@[cluster_algebras "lem_rectangles_independent"]
theorem algebraicIndependent_pluckerCoord_rectLabel {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    AlgebraicIndependent ℂ fun v : RectVertex a b =>
      pluckerCoord (complexGenericMatrix a b) (rectLabel a b v) := by
  induction a, ha using Nat.le_induction generalizing b with
  | base =>
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact algebraicIndependent_rect_one b
  | succ a ha ih =>
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact algebraicIndependent_rect_succ a b ha (ih (by omega))

end Independent

/-! ### The rectangles seed and its cyclic shifts are labeled seeds -/

section Seed

/-- **The extended exchange matrix of a labelled quiver is extended skew-symmetrizable**: its
principal part is the exchange matrix, which is skew-symmetric, so `d = (1, …, 1)` is a
skew-symmetrizing vector. -/
theorem extSkewSymmetrizable_extExchangeMatrix {V : Type*} [Fintype V] {m n : ℕ}
    {Q : Quiver V} (L : Labelling Q m n) : ExtSkewSymmetrizable L.le (extExchangeMatrix Q L) := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun i j => ?_⟩
  have h := congrFun (congrFun (exchangeMatrix_transpose Q L) j) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply, exchangeMatrix, Matrix.of_apply] at h
  simp only [Int.cast_one, one_mul, Matrix.submatrix_apply, id, h]

variable {a b m n : ℕ}

/-- The entries of every cyclic shift `Σ^i_{a,b}(λ)` are algebraically independent over `ℂ`:
they are the images of the rectangles coordinates under the automorphism `ρ^{-i}` of `ℂ[z]`,
read in `ℂ(z)`. -/
theorem algebraicIndependent_rectanglesSeedShift (ha : 1 ≤ a) (hab : a ≤ b)
    (L : RectangleLabelling a b m n) (i : ℤ) :
    AlgebraicIndependent ℂ (rectanglesSeedShift L i).extCluster := by
  have h1 := ((algebraicIndependent_equiv L.equiv).2
    (algebraicIndependent_pluckerCoord_rectLabel ha hab)).map'
      (f := ((rotationEquiv a b ^ (-i) : ComplexPoly a b ≃ₐ[ℂ] ComplexPoly a b) :
        ComplexPoly a b →ₐ[ℂ] ComplexPoly a b)) (AlgEquiv.injective _)
  have h2 := h1.map' (f := IsScalarTower.toAlgHom ℂ (ComplexPoly a b)
    (FractionRing (ComplexPoly a b))) (IsFractionRing.injective _ _)
  convert h2 using 1
  funext ℓ
  simp only [Function.comp_apply, AlgEquiv.coe_algHom, IsScalarTower.coe_toAlgHom',
    rotationEquiv_zpow_pluckerCoord, neg_neg]
  rfl

/-- **Every cyclic shift `Σ^i_{a,b}(λ)` is a labeled seed** over `ℂ` in the subfield of `ℂ(z)`
generated by its entries, for `1 ≤ a ≤ b`. -/
theorem isLabeledSeed_rectanglesSeedShift (ha : 1 ≤ a) (hab : a ≤ b)
    (L : RectangleLabelling a b m n) (i : ℤ) :
    IsLabeledSeed ℂ L.le ((rectanglesSeedShift L i).adjoinSelf ℂ) :=
  (isLabeledSeed_adjoinSelf_iff ℂ L.le _).2 ⟨algebraicIndependent_rectanglesSeedShift ha hab L i,
    extSkewSymmetrizable_extExchangeMatrix L.toLabelling⟩

/-- **The rectangles seed is a labeled seed**: `Σ_{a,b}(λ)` is a labeled seed over `ℂ` in the
subfield of `ℂ(z)` generated by its entries. FWZ assume `2 ≤ a ≤ b - 2`, which is used
only for `n ≥ 1` (`RectangleLabelling.one_le_n`); the seed property holds for `1 ≤ a ≤ b`. -/
@[cluster_algebras "lem_rectangles_seed_is_seed"]
theorem isLabeledSeed_rectanglesSeed (ha : 1 ≤ a) (hab : a ≤ b)
    (L : RectangleLabelling a b m n) :
    IsLabeledSeed ℂ L.le ((rectanglesSeed L).adjoinSelf ℂ) :=
  isLabeledSeed_rectanglesSeedShift ha hab L 0

/-- A rectangle labelling numbers the `m = a(b - a) + 1` rectangles of `V_{a,b}`. -/
theorem RectangleLabelling.m_eq (L : RectangleLabelling a b m n) : m = a * (b - a) + 1 := by
  simpa using Fintype.card_congr L.equiv

/-- A rectangle labelling has `n = (a - 1)(b - a - 1)` mutable indices, the number of rectangles
of height less than `a` and width less than `b - a`. -/
theorem RectangleLabelling.n_eq (L : RectangleLabelling a b m n) :
    n = (a - 1) * (b - a - 1) := by
  have e1 : Fin n ≃ {v : RectVertex a b // ¬RectFrozen a b v} :=
    { toFun := fun j => ⟨L.equiv (Fin.castLE L.le j), fun h => by
        have := (L.frozen_iff _).1 h
        simp only [Fin.val_castLE] at this
        omega⟩
      invFun := fun v => ⟨L.equiv.symm v, by
        by_contra h
        exact v.2 (by simpa using (L.frozen_iff (L.equiv.symm v)).2 (not_lt.1 h))⟩
      left_inv := fun j => by ext; simp
      right_inv := fun v => by ext; simp }
  let f : Fin (a - 1) × Fin (b - a - 1) → {v : RectVertex a b // ¬RectFrozen a b v} :=
    fun pq => ⟨some (Fin.castLE (by omega) pq.1, Fin.castLE (by omega) pq.2), by
      have := pq.1.isLt
      have := pq.2.isLt
      simp only [RectFrozen, Fin.val_castLE, not_or]
      omega⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨p, q⟩ ⟨p', q'⟩ h
      simp only [f, Subtype.mk.injEq, Option.some.injEq, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castLE] at h
      exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
    · rintro ⟨_ | ⟨p, q⟩, h⟩
      · exact absurd trivial h
      · simp only [RectFrozen, not_or] at h
        exact ⟨(⟨p, by omega⟩, ⟨q, by omega⟩), rfl⟩
  rw [← Fintype.card_fin n, Fintype.card_congr (e1.trans (Equiv.ofBijective f hf).symm)]
  simp

/-- For `2 ≤ a ≤ b - 2` a rectangle labelling has at least one mutable index. -/
@[cluster_algebras "lem_rectangles_seed_is_seed"]
theorem RectangleLabelling.one_le_n (L : RectangleLabelling a b m n) (ha : 2 ≤ a)
    (hab : a + 2 ≤ b) : 1 ≤ n := by
  rw [L.n_eq]
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))

end Seed

end ClusterAlgebras

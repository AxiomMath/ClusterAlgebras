/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.Defs
public import ClusterAlgebras.External
public import ClusterAlgebras.TotalPositivity.Muir

/-!
# Three-term Plücker relations and the rotation of the columns

Two facts about the Plücker coordinates `P_J(z)` of an `a × b` matrix `z`, from the cluster
structure on the Plücker ring `R_{a,b}` [FWZ, Chapter 6].

The **three-term Grassmann–Plücker relations**: over any commutative ring, for a set `S` of
`a - 2` columns and columns `α < β < γ < δ` outside `S`,
`P_{S∪{α,γ}} P_{S∪{β,δ}} = P_{S∪{α,β}} P_{S∪{γ,δ}} + P_{S∪{α,δ}} P_{S∪{β,γ}}`.
The case `a = 2`, `S = ∅` is the relation for `2 × b` matrices; Muir's law for flag minors adjoins
the columns `S` to every coordinate of the generic matrix, and a specialization of the generic
matrix gives the relation for every `z`.

The **rotation** `ρ` of the columns of the generic `a × b` matrix, `z_{rj} ↦ z_{r,j-1}` and
`z_{r1} ↦ (-1)^{a-1} z_{rb}`, is a `ℂ`-algebra automorphism of `ℂ[z]` with
`ρ(P_J) = P_{(J-1) mod b}`: the sign `(-1)^{a-1}` that the first column picks up is cancelled by
moving that column past the other `a - 1`.

## Main results

* `ClusterAlgebras.pluckerCoord_union_mul_pluckerCoord_union`: the three-term Grassmann–Plücker
  relations.
* `ClusterAlgebras.rotationEquiv`: the rotation as a `ℂ`-algebra automorphism of `ℂ[z]`, with
  `ClusterAlgebras.coe_rotationEquiv : ⇑(rotationEquiv a b) = rotation a b`.
* `ClusterAlgebras.rotation_pluckerCoord`: `ρ(P_J) = P_{(J-1) mod b}`, and
  `ClusterAlgebras.rotationEquiv_zpow_pluckerCoord`: `ρ^i(P_J) = P_{(J-i) mod b}`.
* `ClusterAlgebras.pluckerCoord_rotateColumns`: for a matrix over any commutative ring, rotating
  the columns and multiplying the new last column by `(-1)^{a-1}` shifts the Plücker coordinates.

## Implementation notes

* Indices are `0`-based, so the column `1` of [FWZ] is column `0` and its column `b` is column
  `b - 1`. The set `(J - i) mod b` is `cyclicShift (-i) J`, the image of `J` under the `(-i)`-th
  power of `finRotate b`.
* [FWZ] assumes `a ≥ 2` and `|S| = a - 2` for the three-term relations, and `1 ≤ a ≤ b` and
  `|J| = a` for the rotation. None of these is needed: when the sizes do not match, every Plücker
  coordinate involved is the junk value `0` of `minor`, and both identities hold trivially.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset MvPolynomial

variable {R : Type*} [CommRing R]

/-! ### The three-term Grassmann–Plücker relations -/

/-- The Plücker coordinates of the first `k` rows of a matrix with rows indexed by `ℕ` are its
minors on the rows `range k`. -/
theorem pluckerCoord_submatrix_val {κ : Type*} [LinearOrder κ] {k : ℕ} (z : Matrix ℕ κ R)
    (J : Finset κ) :
    pluckerCoord (z.submatrix (Fin.val : Fin k → ℕ) id) J = minor z (range k) J := by
  refine (minor_submatrix_orderEmbedding z (Fin.valOrderEmb k)
    (OrderIso.refl κ).toOrderEmbedding univ J).trans ?_
  congr 1
  · ext j
    simp only [mem_range, mem_map, mem_univ, true_and]
    exact ⟨by rintro ⟨i, rfl⟩; exact i.isLt, fun h => ⟨⟨j, h⟩, rfl⟩⟩
  · ext j; simp

/-- Adjoining two distinct columns outside `S` adds two to its cardinality. -/
private theorem card_union_pair {b : ℕ} {S : Finset (Fin b)} {x y : Fin b} (hx : x ∉ S)
    (hy : y ∉ S) (hxy : x ≠ y) : (S ∪ {x, y}).card = S.card + 2 := by
  rw [card_union_of_disjoint (by simp [hx, hy]), card_pair hxy]

/-- The three-term Grassmann–Plücker relations for a matrix with exactly `S.card + 2` rows. -/
private theorem pluckerCoord_three_term_of_card {b : ℕ} (S : Finset (Fin b))
    (z : Matrix (Fin (S.card + 2)) (Fin b) R) {α β γ δ : Fin b} (hα : α ∉ S) (hβ : β ∉ S)
    (hγ : γ ∉ S) (hδ : δ ∉ S) (hαβ : α < β) (hβγ : β < γ) (hγδ : γ < δ) :
    pluckerCoord z (S ∪ {α, γ}) * pluckerCoord z (S ∪ {β, δ}) -
      pluckerCoord z (S ∪ {α, β}) * pluckerCoord z (S ∪ {γ, δ}) -
      pluckerCoord z (S ∪ {α, δ}) * pluckerCoord z (S ∪ {β, γ}) = 0 := by
  have hαγ := hαβ.trans hβγ
  have hβδ := hβγ.trans hγδ
  have hαδ := hαβ.trans hβδ
  set w := genericMatrix ℕ (Fin b)
  let B : Fin 6 → Finset (Fin b) := ![{α, γ}, {β, δ}, {α, β}, {γ, δ}, {α, δ}, {β, γ}]
  let F : MvPolynomial (Fin 6) ℤ := X 0 * X 1 - X 2 * X 3 - X 4 * X 5
  have hF : F.IsHomogeneous 2 :=
    ((IsHomogeneous.mul (isHomogeneous_X _ _) (isHomogeneous_X _ _)).sub
      (IsHomogeneous.mul (isHomogeneous_X _ _) (isHomogeneous_X _ _))).sub
      (IsHomogeneous.mul (isHomogeneous_X _ _) (isHomogeneous_X _ _))
  have h2 := pluckerCoord_three_term (by have := δ.isLt; omega)
    (w.submatrix (Fin.val : Fin 2 → ℕ) id) hαβ hβγ hγδ
  simp only [pluckerCoord_submatrix_val] at h2
  have h0 : aeval (fun s => minor w (range (B s).card) (B s)) F = 0 := by
    simp [F, B, card_pair hαβ.ne, card_pair hβγ.ne, card_pair hγδ.ne, card_pair hαγ.ne,
      card_pair hβδ.ne, card_pair hαδ.ne, h2]
  have h1 := muir_law_flag B hF h0 S (by intro s; fin_cases s <;> simp [B, hα, hβ, hγ, hδ])
  let z' : Matrix ℕ (Fin b) R := fun i j => if h : i < S.card + 2 then z ⟨i, h⟩ j else 0
  have hz : ∀ s, minor z' (range (B s ∪ S).card) (B s ∪ S) = pluckerCoord z (S ∪ B s) := by
    intro s
    have : (S ∪ B s).card = S.card + 2 := by
      fin_cases s
      exacts [card_union_pair hα hγ hαγ.ne, card_union_pair hβ hδ hβδ.ne,
        card_union_pair hα hβ hαβ.ne, card_union_pair hγ hδ hγδ.ne,
        card_union_pair hα hδ hαδ.ne, card_union_pair hβ hγ hβγ.ne]
    rw [union_comm, this, ← pluckerCoord_submatrix_val]
    congr 1
    ext i j
    simp [z']
  have h3 := congrArg (eval₂Hom (Int.castRingHom R) fun p : ℕ × Fin b => z' p.1 p.2) h1
  rw [map_aeval_int, map_zero] at h3
  simp only [RingHom.map_minor, genericMatrix_map_eval₂Hom, hz, F, map_sub, map_mul,
    aeval_X] at h3
  exact h3

/-- **The three-term Grassmann–Plücker relations.** For a matrix `z` with `a` rows and `b`
columns over a commutative ring, a set `S` of columns and columns `α < β < γ < δ` outside `S`,
`P_{S∪{α,γ}} P_{S∪{β,δ}} = P_{S∪{α,β}} P_{S∪{γ,δ}} + P_{S∪{α,δ}} P_{S∪{β,γ}}`.

No hypothesis on `a` or `|S|` is needed: unless `|S| + 2 = a`, all six coordinates are `0`. -/
@[cluster_algebras "lem_plucker_three_term"]
theorem pluckerCoord_union_mul_pluckerCoord_union {a b : ℕ} (z : Matrix (Fin a) (Fin b) R)
    (S : Finset (Fin b)) {α β γ δ : Fin b} (hα : α ∉ S) (hβ : β ∉ S) (hγ : γ ∉ S) (hδ : δ ∉ S)
    (hαβ : α < β) (hβγ : β < γ) (hγδ : γ < δ) :
    pluckerCoord z (S ∪ {α, γ}) * pluckerCoord z (S ∪ {β, δ}) =
      pluckerCoord z (S ∪ {α, β}) * pluckerCoord z (S ∪ {γ, δ}) +
        pluckerCoord z (S ∪ {α, δ}) * pluckerCoord z (S ∪ {β, γ}) := by
  by_cases ha : S.card + 2 = a
  · subst ha
    linear_combination pluckerCoord_three_term_of_card S z hα hβ hγ hδ hαβ hβγ hγδ
  have h0 : ∀ x y : Fin b, x ∉ S → y ∉ S → x < y → pluckerCoord z (S ∪ {x, y}) = 0 :=
    fun x y hx hy hxy => by
      rw [pluckerCoord, minor, dif_neg]
      rwa [card_union_pair hx hy hxy.ne, card_univ, Fintype.card_fin]
  rw [h0 α γ hα hγ (hαβ.trans hβγ), h0 β δ hβ hδ (hβγ.trans hγδ), h0 α β hα hβ hαβ,
    h0 γ δ hγ hδ hγδ, h0 α δ hα hδ (hαβ.trans (hβγ.trans hγδ)), h0 β γ hβ hγ hβγ]
  ring

/-! ### Rotating the columns of a matrix -/

/-- The cyclic permutation `j ↦ j + 1 mod b` of the columns, in values. -/
theorem val_finRotate {b : ℕ} (j : Fin b) :
    ((finRotate b j : Fin b) : ℕ) = if (j : ℕ) + 1 = b then (0 : ℕ) else (j : ℕ) + 1 := by
  obtain _ | n := b
  · exact j.elim0
  rw [coe_finRotate]
  simp [Fin.ext_iff]

/-- The cyclic permutation `j ↦ j - 1 mod b` of the columns, in values. -/
theorem val_finRotate_symm {b : ℕ} (j : Fin b) :
    (((finRotate b).symm j : Fin b) : ℕ) = if (j : ℕ) = 0 then b - 1 else (j : ℕ) - 1 := by
  obtain _ | n := b
  · exact j.elim0
  set k := (finRotate (n + 1)).symm j with hk
  have hj : finRotate (n + 1) k = j := by simp [hk]
  rw [← hj, coe_finRotate]
  by_cases h : k = Fin.last n
  · simp [h]
  · have := Fin.val_lt_last h
    simp [h]

/-- The square of `(-1)^k` is `1`. -/
private theorem neg_one_pow_mul_self {S : Type*} [Ring S] (k : ℕ) :
    ((-1) ^ k * (-1) ^ k : S) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-- Every column of `J` but the first is nonzero. -/
private theorem orderEmbOfFin_ne_zero {b n : ℕ} {J : Finset (Fin b)} (hJ : J.card = n + 1)
    {k : Fin (n + 1)} (hk : k ≠ 0) : (J.orderEmbOfFin hJ k : ℕ) ≠ 0 := by
  have := (J.orderEmbOfFin hJ).strictMono (Fin.pos_iff_ne_zero.mpr hk)
  rw [Fin.lt_def] at this
  omega

/-- If the first column of `J` is `0`, then listing the columns `(J - 1) mod b` in increasing
order moves it from the first place to the last. -/
private theorem finRotate_symm_comp_orderEmbOfFin {b n : ℕ} {J : Finset (Fin b)}
    (hJ : J.card = n + 1) (hJ' : (J.map (finRotate b).symm.toEmbedding).card = n + 1)
    (he0 : (J.orderEmbOfFin hJ 0 : ℕ) = 0) :
    (finRotate b).symm ∘ J.orderEmbOfFin hJ ∘ finRotate (n + 1) =
      (J.map (finRotate b).symm.toEmbedding).orderEmbOfFin hJ' := by
  set e := J.orderEmbOfFin hJ
  set σ := (finRotate b).symm
  set τ := finRotate (n + 1)
  have hτ : ∀ k : Fin (n + 1),
      (τ k : ℕ) = if k = Fin.last n then (0 : ℕ) else (k : ℕ) + 1 := coe_finRotate
  have hτlast : τ (Fin.last n) = 0 := by ext; rw [hτ]; simp
  have hτne : ∀ k, k ≠ Fin.last n → (e (τ k) : ℕ) ≠ 0 := by
    intro k hk
    refine orderEmbOfFin_ne_zero hJ fun h => ?_
    have := hτ k
    rw [h, if_neg hk] at this
    simp at this
  have hf : ∀ k : Fin (n + 1), (σ (e (τ k)) : ℕ) =
      if k = Fin.last n then b - 1 else e (τ k) - 1 := by
    intro k
    rw [val_finRotate_symm]
    by_cases hk : k = Fin.last n
    · simp [hk, hτlast, he0]
    · rw [if_neg (hτne k hk), if_neg hk]
  refine Finset.orderEmbOfFin_unique hJ' (fun k => mem_map_of_mem _ (J.orderEmbOfFin_mem hJ _))
    fun k l hkl => ?_
  have hk : k ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hkl (Fin.le_last l))
  rw [Fin.lt_def]
  change (σ (e (τ k)) : ℕ) < σ (e (τ l))
  rw [hf, hf, if_neg hk]
  have hk0 := hτne k hk
  by_cases hl : l = Fin.last n
  · rw [if_pos hl]
    have := (e (τ k)).isLt
    omega
  · rw [if_neg hl]
    have h1 : τ k < τ l := by
      rw [Fin.lt_def, hτ, hτ, if_neg hk, if_neg hl]
      have := Fin.lt_def.mp hkl
      omega
    have h2 := Fin.lt_def.mp (e.strictMono h1)
    omega

/-- **Rotating the columns shifts the Plücker coordinates.** Let `Z` be a matrix with `a` rows
and `b` columns over a commutative ring, and let `Z'` have column `j` equal to column `j - 1` of
`Z` for `j ≥ 1` and column `0` equal to `(-1)^{a-1}` times column `b - 1` of `Z`. Then
`P_J(Z') = P_{(J-1) mod b}(Z)` for every set `J` of columns. -/
theorem pluckerCoord_rotateColumns {a b : ℕ} (Z : Matrix (Fin a) (Fin b) R)
    (J : Finset (Fin b)) :
    pluckerCoord (Matrix.of fun r (j : Fin b) =>
        (if (j : ℕ) = 0 then (-1) ^ (a - 1) else 1) * Z r ((finRotate b).symm j)) J =
      pluckerCoord Z (J.map (finRotate b).symm.toEmbedding) := by
  by_cases hJ : J.card = a
  swap
  · simp [pluckerCoord, minor, hJ]
  have hJ' : (J.map (finRotate b).symm.toEmbedding).card = a := by rw [card_map, hJ]
  rw [pluckerCoord_eq_det _ hJ, pluckerCoord_eq_det _ hJ']
  set e := J.orderEmbOfFin hJ
  set e' := (J.map (finRotate b).symm.toEmbedding).orderEmbOfFin hJ'
  set σ := (finRotate b).symm
  set v : Fin a → R := fun k => if (e k : ℕ) = 0 then (-1) ^ (a - 1) else 1
  have h1 : (Matrix.of fun r (j : Fin b) =>
        (if (j : ℕ) = 0 then (-1) ^ (a - 1) else 1) * Z r (σ j)).submatrix id e =
      Matrix.of fun r k => v k * (Z.submatrix id (σ ∘ e)) r k := rfl
  rw [h1, Matrix.det_mul_row]
  by_cases h0 : ∃ j ∈ J, (j : ℕ) = 0
  · obtain ⟨j0, hj0, hj0'⟩ := h0
    obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 :=
      ⟨a - 1, by have := card_pos.mpr ⟨j0, hj0⟩; omega⟩
    have he0 : (e 0 : ℕ) = 0 := by
      have : e 0 ≤ j0 := by
        rw [show (0 : Fin (n + 1)) = ⟨0, n.succ_pos⟩ from rfl, Finset.orderEmbOfFin_zero]
        exact J.min'_le _ hj0
      rw [Fin.le_def] at this
      omega
    have hepos : ∀ k : Fin (n + 1), k ≠ 0 → (e k : ℕ) ≠ 0 := fun _ => orderEmbOfFin_ne_zero hJ
    have hprod : ∏ k, v k = (-1) ^ n := by
      rw [Fin.prod_univ_succ,
        Finset.prod_eq_one fun k _ => by simp [v, hepos k.succ (Fin.succ_ne_zero k)]]
      simp [v, he0]
    set τ := finRotate (n + 1)
    have he : σ ∘ e ∘ τ = e' := finRotate_symm_comp_orderEmbOfFin hJ hJ' he0
    have he2 : σ ∘ e = e' ∘ τ.symm := by
      rw [← he]; ext k; simp
    rw [hprod, he2, show Z.submatrix id (e' ∘ τ.symm) = (Z.submatrix id e').submatrix id τ.symm
      from rfl, Matrix.det_permute', Equiv.Perm.sign_symm, sign_finRotate, Nat.add_sub_cancel,
      ← mul_assoc]
    push_cast
    rw [neg_one_pow_mul_self, one_mul]
  · push Not at h0
    have hv : ∀ k, (e k : ℕ) ≠ 0 := fun k => h0 _ (J.orderEmbOfFin_mem hJ k)
    have he : σ ∘ e = e' := by
      refine Finset.orderEmbOfFin_unique hJ'
        (fun k => mem_map_of_mem _ (J.orderEmbOfFin_mem hJ k)) fun k l hkl => ?_
      have := e.strictMono hkl
      rw [Fin.lt_def] at this ⊢
      simp only [Function.comp_apply, σ, val_finRotate_symm, hv k, hv l, if_false]
      have := hv k
      omega
    rw [Finset.prod_eq_one fun k _ => by simp [v, hv k], one_mul, he]

/-! ### Cyclic shifts -/

/-- The cyclic shift by `0` is the identity. -/
@[simp]
theorem cyclicShift_zero {b : ℕ} (J : Finset (Fin b)) : cyclicShift 0 J = J := by
  rw [cyclicShift, zpow_zero]
  exact map_refl

/-- Cyclic shifts compose: `((J + j) + i) mod b = (J + (i + j)) mod b`. -/
@[simp]
theorem cyclicShift_cyclicShift {b : ℕ} (i j : ℤ) (J : Finset (Fin b)) :
    cyclicShift i (cyclicShift j J) = cyclicShift (i + j) J := by
  simp only [cyclicShift, map_map]
  congr 1
  ext x
  simp [zpow_add, Equiv.Perm.mul_apply]

/-- A cyclic shift preserves the number of columns. -/
@[simp]
theorem card_cyclicShift {b : ℕ} (i : ℤ) (J : Finset (Fin b)) :
    (cyclicShift i J).card = J.card :=
  card_map _

/-- `(J - 1) mod b` is the image of `J` under `j ↦ j - 1 mod b`. -/
theorem cyclicShift_neg_one {b : ℕ} (J : Finset (Fin b)) :
    cyclicShift (-1) J = J.map (finRotate b).symm.toEmbedding := by
  simp only [cyclicShift, zpow_neg, zpow_one]
  rfl

/-! ### The rotation of the columns of the generic matrix -/

/-- `ρ(z_{rj}) = z_{r,j-1}`, the column index taken mod `b`, times `(-1)^{a-1}` when `j` is the
first column. -/
theorem rotation_X {a b : ℕ} (r : Fin a) (j : Fin b) :
    rotation a b (X (r, j)) =
      (if (j : ℕ) = 0 then (-1) ^ (a - 1) else 1) * X (r, (finRotate b).symm j) := by
  simp only [rotation, aeval_X]
  split_ifs with h
  · simp only [map_pow, map_neg, map_one]
    congr 3
    rw [Fin.ext_iff, val_finRotate_symm, if_pos h]
  · rw [one_mul]
    congr 2
    rw [Fin.ext_iff, val_finRotate_symm, if_neg h]

/-- The inverse of the rotation: `z_{rj} ↦ z_{r,j+1}` for `j` not the last column, and
`z_{rb} ↦ (-1)^{a-1} z_{r1}`. -/
noncomputable def rotationInv (a b : ℕ) : ComplexPoly a b →ₐ[ℂ] ComplexPoly a b :=
  aeval fun rj => (if (rj.2 : ℕ) + 1 = b then (-1) ^ (a - 1) else 1) * X (rj.1, finRotate b rj.2)

/-- The defining property of `rotationInv` on the indeterminates. -/
theorem rotationInv_X {a b : ℕ} (r : Fin a) (j : Fin b) :
    rotationInv a b (X (r, j)) =
      (if (j : ℕ) + 1 = b then (-1) ^ (a - 1) else 1) * X (r, finRotate b j) := by
  simp [rotationInv]

/-- The rotation `ρ` composed with `rotationInv` is the identity. -/
theorem rotation_comp_rotationInv (a b : ℕ) :
    (rotation a b).comp (rotationInv a b) = AlgHom.id ℂ _ := by
  refine algHom_ext fun ⟨r, j⟩ => ?_
  rw [AlgHom.comp_apply, rotationInv_X, map_mul, rotation_X, AlgHom.id_apply]
  simp only [Equiv.symm_apply_apply, val_finRotate, apply_ite (rotation a b), map_pow, map_neg,
    map_one]
  split_ifs <;> first
    | omega
    | rw [← mul_assoc, neg_one_pow_mul_self, one_mul]
    | simp_all

/-- `rotationInv` composed with the rotation `ρ` is the identity. -/
theorem rotationInv_comp_rotation (a b : ℕ) :
    (rotationInv a b).comp (rotation a b) = AlgHom.id ℂ _ := by
  refine algHom_ext fun ⟨r, j⟩ => ?_
  rw [AlgHom.comp_apply, rotation_X, map_mul, rotationInv_X, AlgHom.id_apply]
  simp only [Equiv.apply_symm_apply, val_finRotate_symm, apply_ite (rotationInv a b), map_pow,
    map_neg, map_one]
  have := j.isLt
  split_ifs <;> first
    | omega
    | rw [← mul_assoc, neg_one_pow_mul_self, one_mul]
    | simp_all

/-- **The rotation is an automorphism**: `ρ` as a `ℂ`-algebra automorphism of `ℂ[z]`, with
inverse `z_{rj} ↦ z_{r,j+1}`, `z_{rb} ↦ (-1)^{a-1} z_{r1}`. -/
@[cluster_algebras "lem_rotation_plucker"]
noncomputable def rotationEquiv (a b : ℕ) : ComplexPoly a b ≃ₐ[ℂ] ComplexPoly a b :=
  AlgEquiv.ofAlgHom (rotation a b) (rotationInv a b) (rotation_comp_rotationInv a b)
    (rotationInv_comp_rotation a b)

/-- The automorphism `rotationEquiv a b` is the rotation `ρ`. -/
@[cluster_algebras "lem_rotation_plucker", simp]
theorem coe_rotationEquiv (a b : ℕ) : ⇑(rotationEquiv a b) = rotation a b :=
  rfl

/-- The inverse of `rotationEquiv a b` is `rotationInv a b`. -/
@[simp]
theorem coe_rotationEquiv_symm (a b : ℕ) : ⇑(rotationEquiv a b).symm = rotationInv a b :=
  rfl

/-- The rotation applied to the generic matrix entrywise: column `j` of the image is column `j - 1`
of `z`, and column `0` is `(-1)^{a-1}` times column `b - 1`. -/
theorem map_rotation_complexGenericMatrix (a b : ℕ) :
    (complexGenericMatrix a b).map (rotation a b) = Matrix.of fun r (j : Fin b) =>
      (if (j : ℕ) = 0 then (-1) ^ (a - 1) else 1) *
        complexGenericMatrix a b r ((finRotate b).symm j) := by
  ext r j
  simp [rotation_X]

/-- **Rotation shifts the Plücker coordinates**: `ρ(P_J) = P_{(J-1) mod b}` for every set `J` of
columns, with no hypothesis on `a`, `b` or `|J|`. -/
@[cluster_algebras "lem_rotation_plucker"]
theorem rotation_pluckerCoord (a b : ℕ) (J : Finset (Fin b)) :
    rotation a b (pluckerCoord (complexGenericMatrix a b) J) =
      pluckerCoord (complexGenericMatrix a b) (cyclicShift (-1) J) := by
  rw [← AlgHom.coe_toRingHom, RingHom.map_pluckerCoord, AlgHom.coe_toRingHom,
    map_rotation_complexGenericMatrix, pluckerCoord_rotateColumns, cyclicShift_neg_one]

/-- The inverse rotation shifts the Plücker coordinates the other way:
`ρ⁻¹(P_J) = P_{(J+1) mod b}`. -/
theorem rotationInv_pluckerCoord (a b : ℕ) (J : Finset (Fin b)) :
    rotationInv a b (pluckerCoord (complexGenericMatrix a b) J) =
      pluckerCoord (complexGenericMatrix a b) (cyclicShift 1 J) := by
  rw [← coe_rotationEquiv_symm, AlgEquiv.symm_apply_eq, coe_rotationEquiv,
    rotation_pluckerCoord, cyclicShift_cyclicShift]
  simp

/-- **Powers of the rotation shift the Plücker coordinates**: `ρ^i(P_J) = P_{(J-i) mod b}` for
every `i ∈ ℤ`. -/
theorem rotationEquiv_zpow_pluckerCoord (a b : ℕ) (i : ℤ) (J : Finset (Fin b)) :
    (rotationEquiv a b ^ i) (pluckerCoord (complexGenericMatrix a b) J) =
      pluckerCoord (complexGenericMatrix a b) (cyclicShift (-i) J) := by
  induction i using Int.induction_on generalizing J with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, AlgEquiv.mul_apply, coe_rotationEquiv, rotation_pluckerCoord, ih,
      cyclicShift_cyclicShift]
    congr 2
    ring
  | pred i ih =>
    rw [zpow_sub_one, AlgEquiv.mul_apply, AlgEquiv.aut_inv, coe_rotationEquiv_symm,
      rotationInv_pluckerCoord, ih, cyclicShift_cyclicShift]
    congr 2
    ring

/-- `ρ^i(P_J) = P_{(J-i) mod b}` for every `i ∈ ℕ`. -/
theorem rotationEquiv_pow_pluckerCoord (a b : ℕ) (i : ℕ) (J : Finset (Fin b)) :
    (rotationEquiv a b ^ i) (pluckerCoord (complexGenericMatrix a b) J) =
      pluckerCoord (complexGenericMatrix a b) (cyclicShift (-i) J) := by
  rw [← zpow_natCast, rotationEquiv_zpow_pluckerCoord]

end ClusterAlgebras

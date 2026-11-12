/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
/-! # Results of Fomin–Williams–Zelevinsky, *Introduction to Cluster Algebras* (FWZ) -/
@[expose] public section
namespace ClusterAlgebras
/-! ## Arrow systems -/
def IsArrowSystem {V : Type*} (a : V → V → ℕ) : Prop := ∀ v, a v v = 0
def signedCount {V : Type*} (a : V → V → ℕ) (i j : V) : ℤ := (a i j : ℤ) - (a j i : ℤ)
/-- An arrow system is **two-cycle-free** when no two vertices carry arrows in both directions. -/
def TwoCycleFree {V : Type*} (a : V → V → ℕ) : Prop := ∀ i j, a i j = 0 ∨ a j i = 0
def cancellation {V : Type*} (a : V → V → ℕ) (i j : V) : ℕ := a i j - min (a i j) (a j i)
def reversal {V : Type*} [DecidableEq V] (c : V → V → ℕ) (k i j : V) : ℕ :=
  if i = k ∨ j = k then c j i else c i j
/-! ## Quivers and quiver mutation -/
structure Quiver.{u_2} (V : Type u_2) [Fintype V] where
  frozen : Finset V
  arrows : V → V → ℕ
  isArrowSystem : IsArrowSystem arrows
  twoCycleFree : TwoCycleFree arrows
  frozen_eq_zero : ∀ u ∈ frozen, ∀ v ∈ frozen, arrows u v = 0
def Quiver.stepOne {V : Type*} [Fintype V] [DecidableEq V] (Q : Quiver V) (k i j : V) : ℕ :=
  if i ∈ Q.frozen ∧ j ∈ Q.frozen then Q.arrows i j else Q.arrows i j + Q.arrows i k * Q.arrows k j
def Quiver.mutationArrows {V : Type*} [Fintype V] [DecidableEq V] (Q : Quiver V) (k : V) :
    V → V → ℕ := cancellation (reversal (Q.stepOne k) k)
/-- The **mutation** of `Q` at the mutable vertex `k`. -/
def Quiver.mutate {V : Type*} [Fintype V] [DecidableEq V] (Q : Quiver V) {k : V}
    (hk : k ∉ Q.frozen) : Quiver V where
  frozen := Q.frozen
  arrows := Q.mutationArrows k
  isArrowSystem v := Nat.sub_eq_zero_of_le (min_self _).ge
  twoCycleFree i j := (le_total (reversal (Q.stepOne k) k i j) (reversal (Q.stepOne k) k j i)).imp
      (fun h => Nat.sub_eq_zero_of_le (le_min le_rfl h))
      (fun h => Nat.sub_eq_zero_of_le (le_min le_rfl h))
  frozen_eq_zero u hu v hv := by
    have hne : ∀ x y : V, x ∈ Q.frozen → y ∈ Q.frozen → reversal (Q.stepOne k) k x y = 0 := by
      intro x y hx hy
      have : ¬(x = k ∨ y = k) := by
        rintro (rfl | rfl)
        exacts [hk hx, hk hy]
      rw [reversal, ite_eq_right this, Quiver.stepOne, ite_eq_left ⟨hx, hy⟩]
      exact Q.frozen_eq_zero x hx y hy
    rw [Quiver.mutationArrows, cancellation, hne u v hu hv]
    exact Nat.zero_sub _
/-- A vertex of `Q` with no arrow into it. -/
def Quiver.IsSource {V : Type*} [Fintype V] (Q : Quiver V) (k : V) : Prop := ∀ v, Q.arrows v k = 0
/-- A vertex of `Q` with no arrow out of it. -/
def Quiver.IsSink {V : Type*} [Fintype V] (Q : Quiver V) (k : V) : Prop := ∀ v, Q.arrows k v = 0
structure Quiver.Iso {V : Type*} [Fintype V] {V' : Type*} [Fintype V'] (Q : Quiver V)
    (Q' : Quiver V') where
  equiv : V ≃ V'
  mem_frozen_iff : ∀ v, equiv v ∈ Q'.frozen ↔ v ∈ Q.frozen
  arrows_eq : ∀ u v, Q'.arrows (equiv u) (equiv v) = Q.arrows u v
/-! ## Exchange matrices -/
structure Labelling {V : Type*} [Fintype V] (Q : Quiver V) (m n : ℕ) where
  equiv : Fin m ≃ V
  le : n ≤ m
  mem_frozen_iff : ∀ i : Fin m, equiv i ∈ Q.frozen ↔ n ≤ (i : ℕ)
/-- The same numbering, read as a labelling of a mutation of `Q`. -/
def Labelling.mutate {V : Type*} {m n : ℕ} [Fintype V] [DecidableEq V] {Q : Quiver V}
    (L : Labelling Q m n) {k : V} (hk : k ∉ Q.frozen) : Labelling (Q.mutate hk) m n where
  equiv := L.equiv
  le := L.le
  mem_frozen_iff := L.mem_frozen_iff
def extExchangeMatrix {V : Type*} {m n : ℕ} [Fintype V] (Q : Quiver V) (L : Labelling Q m n) :
    Matrix (Fin m) (Fin n) ℤ :=
  Matrix.of fun i j => signedCount Q.arrows (L.equiv i) (L.equiv (Fin.castLE L.le j))
/-! ## Matrix mutation -/
/-- The **mutation of `B` in direction `k`**. -/
def matrixMutation {R : Type*} [CommRing R] [LinearOrder R] {m n : ℕ} (hmn : n ≤ m)
    (B : Matrix (Fin m) (Fin n) R) (k : Fin n) : Matrix (Fin m) (Fin n) R := Matrix.of fun i j =>
    if i = Fin.castLE hmn k ∨ j = k then -B i j else if 0 < B i k ∧ 0 < B (Fin.castLE hmn k) j then
      B i j + B i k * B (Fin.castLE hmn k) j else if B i k < 0 ∧ B (Fin.castLE hmn k) j < 0 then
      B i j - B i k * B (Fin.castLE hmn k) j else B i j
/-! ## Skew-symmetrizable matrices and their diagrams -/
def IsSkewSymmetrizingVector {R : Type*} [CommRing R] {n : ℕ} (B : Matrix (Fin n) (Fin n) R)
    (d : Fin n → ℤ) : Prop := (∀ i, 0 < d i) ∧ ∀ i j, (d i : R) * B i j = -((d j : R) * B j i)
/-- `B` is **skew-symmetrizable** when it admits a skew-symmetrizing vector. -/
def SkewSymmetrizable {R : Type*} [CommRing R] {n : ℕ} (B : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ d : Fin n → ℤ, IsSkewSymmetrizingVector B d
structure Diagram.{u_2} (ι : Type u_2) where
  edges : Set (ι × ι)
  weight : ι × ι → ℝ
  weight_eq_zero_of_notMem : ∀ p ∉ edges, weight p = 0
noncomputable def diagram {ι : Type*} (B : Matrix ι ι ℝ) : Diagram ι where
  edges := {p | 0 < B p.1 p.2}
  weight p := if 0 < B p.1 p.2 then |B p.1 p.2 * B p.2 p.1| else 0
  weight_eq_zero_of_notMem _ hp := ite_eq_right hp
def Diagram.Connected {ι : Type*} (Γ : Diagram ι) : Prop :=
  ∀ P : Set ι, P.Nonempty → Pᶜ.Nonempty → ∃ i ∈ P, ∃ j ∈ Pᶜ, (i, j) ∈ Γ.edges ∨ (j, i) ∈ Γ.edges
/-! ## Graphs, trees, and acyclicity -/
/-- A finite simple graph is a simple graph on a finite vertex type. -/
@[nolint unusedArguments]
abbrev FiniteSimpleGraph (V : Type*) [Fintype V] := SimpleGraph V
def Quiver.IsOrientation {V : Type*} [Fintype V] (Q : Quiver V) (G : FiniteSimpleGraph V) : Prop :=
  Q.frozen = ∅ ∧ ∀ u v : V, u ≠ v → (G.Adj u v → Q.arrows u v + Q.arrows v u = 1) ∧
      (¬G.Adj u v → Q.arrows u v = 0 ∧ Q.arrows v u = 0)
/-- A **finite tree**: a finite simple graph that is connected and acyclic. -/
abbrev IsFiniteTree {V : Type*} [Fintype V] (T : FiniteSimpleGraph V) : Prop := T.IsTree
/-- An **orientation of a finite tree**: an orientation of it as a finite simple graph. -/
abbrev Quiver.IsTreeOrientation {V : Type*} [Fintype V] (Q : Quiver V)
    (T : FiniteSimpleGraph V) : Prop := Q.IsOrientation T
def IsOrientedCycle {V : Type*} [Fintype V] (Q : Quiver V) (r : ℕ) (v : ℕ → V) : Prop :=
  1 ≤ r ∧ v r = v 0 ∧ Set.InjOn v (Set.Iio r) ∧ ∀ t < r, 0 < Q.arrows (v t) (v (t + 1))
/-- A quiver is **acyclic** when it contains no oriented cycle. -/
def Acyclic {V : Type*} [Fintype V] (Q : Quiver V) : Prop :=
  ∀ (r : ℕ) (v : ℕ → V), ¬IsOrientedCycle Q r v
/-! ## Mutation paths and mutation equivalence -/
inductive Quiver.MutationPath.{u} {V : Type u} [Fintype V] [DecidableEq V] : Quiver V → Type u
  | nil (Q : Quiver V) : Quiver.MutationPath Q
  | cons {Q : Quiver V} {k : V} (hk : k ∉ Q.frozen) (p : Quiver.MutationPath (Q.mutate hk)) :
      Quiver.MutationPath Q
/-- The **result** of a mutation path: the last quiver of its chain. -/
def Quiver.MutationPath.result.{u} {V : Type u} [Fintype V] [DecidableEq V] :
    {Q : Quiver V} → Q.MutationPath → Quiver V
  | _, .nil Q => Q
  | _, .cons _ p => p.result
def Quiver.MutationPath.AtSourceOrSink.{u} {V : Type u} [Fintype V] [DecidableEq V] :
    {Q : Quiver V} → Q.MutationPath → Prop
  | _, .nil _ => True
  | Q, .cons (k := k) _ p => (Q.IsSource k ∨ Q.IsSink k) ∧ p.AtSourceOrSink
def Quiver.MutationEquivalent.{u, u_1} {V : Type u} [Fintype V] [DecidableEq V]
    {V' : Type u_1} [Fintype V'] (Q : Quiver V) (Q' : Quiver V') : Prop :=
  ∃ p : Q.MutationPath, Nonempty (p.result.Iso Q')
/-! ## The Markov quiver -/
def markovQuiver : Quiver (Fin 3) where
  frozen := ∅
  arrows u v := if u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 2 ∨ u = 2 ∧ v = 0 then 2 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; fin_cases i <;> fin_cases j <;> decide
  frozen_eq_zero := by decide
/-! ## Words, spans, and crossings -/
/-- The transposition of the two levels either side of the gap `g`. -/
def gapSwap {n : ℕ} (g : Fin (n + 1)) : Equiv.Perm (Fin (n + 2)) := Equiv.swap g.castSucc g.succ
/-- The first position preceded by exactly `j` occurrences of `g` in `l`. -/
def spanStart {α : Type*} [DecidableEq α] (g : α) : ℕ → List α → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | j + 1, a :: l => (if a = g then spanStart g j l else spanStart g (j + 1) l) + 1
/-- The list with the stretch of length `new.length` starting at `p` replaced by `new`. -/
def spliceWord {α : Type*} (l : List α) (p : ℕ) (new : List α) : List α :=
  l.take p ++ new ++ l.drop (p + new.length)
/-! ## Wiring diagrams -/
structure WiringDiagram (n : ℕ) where
  word : List (Fin (n + 1))
  length_eq : word.length = (n + 2).choose 2
  prod_eq : (word.map gapSwap).prod = Fin.revPerm
namespace WiringDiagram
variable {n : ℕ} (D : WiringDiagram n)
/-- The **level of the crossing at position `t`**, or `0` past the end of the word. -/
def levelAt (t : ℕ) : Fin (n + 1) := D.word.getD t 0
/-- The **multiplicity of the gap `g`**: the number of crossings at that level. -/
def multiplicity (g : Fin (n + 1)) : ℕ := D.word.count g
/-- How many crossings of `g` lie before position `t`. -/
def countUpTo (g : Fin (n + 1)) (t : ℕ) : ℕ := (D.word.take t).count g
/-- The permutation `u_t` reached after the first `t` crossings. -/
def wire (t : ℕ) : Equiv.Perm (Fin (n + 2)) := ((D.word.map gapSwap).take t).prod
/-- The **level of the wire `v`** after `t` crossings, the inverse reading of `wire`. -/
def levelOf (t : ℕ) (v : Fin (n + 2)) : Fin (n + 2) := (D.wire t).symm v
/-- The set `{u_t(1), …, u_t(g)}` of wires lying at or below the gap `g` after `t` crossings. -/
def belowSet (t : ℕ) (g : Fin (n + 1)) : Finset (Fin (n + 2)) :=
  {v ∈ Finset.univ | D.levelOf t v ≤ g.castSucc}
structure Chamber where
  gap : Fin (n + 1)
  idx : ℕ
  idx_le : idx ≤ D.multiplicity gap
namespace Chamber
variable {D} (c : D.Chamber)
/-- The **left position** of the chamber, with `0` standing for `-∞`. -/
def left : ℕ := spanStart c.gap c.idx D.word
/-- The **right position** of the chamber, with `word.length + 1` standing for `+∞`. -/
def right : ℕ := if c.idx = D.multiplicity c.gap then D.word.length + 1
  else spanStart c.gap (c.idx + 1) D.word
/-- A chamber **has a left end** when its left position is a genuine position. -/
def HasLeftEnd : Prop := c.left ≠ 0
/-- A chamber **has a right end** when its right position is a genuine position. -/
def HasRightEnd : Prop := c.right ≠ D.word.length + 1
/-- A chamber is **bounded** when it has both ends, and **unbounded** otherwise. -/
def Bounded : Prop := c.HasLeftEnd ∧ c.HasRightEnd
instance instDecidableHasLeftEnd : Decidable c.HasLeftEnd :=
  inferInstanceAs (Decidable (c.left ≠ 0))
instance instDecidableHasRightEnd : Decidable c.HasRightEnd :=
  inferInstanceAs (Decidable (c.right ≠ D.word.length + 1))
instance instDecidableBounded : Decidable c.Bounded :=
  inferInstanceAs (Decidable (c.HasLeftEnd ∧ c.HasRightEnd))
def chamberSet : Finset (Fin (n + 2)) := D.belowSet c.left c.gap
end Chamber
/-- Chambers correspond to a gap together with an index into that gap's crossings. -/
def chamberEquiv : D.Chamber ≃ ((g : Fin (n + 1)) × Fin (D.multiplicity g + 1)) where
  toFun c := ⟨c.gap, ⟨c.idx, Nat.lt_succ_of_le c.idx_le⟩⟩
  invFun p := ⟨p.1, p.2, Nat.le_of_lt_succ p.2.isLt⟩
  left_inv c := by cases c; rfl
  right_inv p := by cases p; rfl
instance instFintypeChamber : Fintype D.Chamber := Fintype.ofEquiv _ D.chamberEquiv.symm
instance instDecidableEqChamber : DecidableEq D.Chamber := fun c c' =>
  decidable_of_iff (D.chamberEquiv c = D.chamberEquiv c') D.chamberEquiv.apply_eq_iff_eq
def Arrow (c c' : D.Chamber) : Prop := (c.Bounded ∨ c'.Bounded) ∧
    ((c.gap = c'.gap ∧ c.right = c'.left) ∨
      (((c'.gap : ℕ) + 1 = (c.gap : ℕ) ∨ (c.gap : ℕ) + 1 = (c'.gap : ℕ)) ∧
        c'.left < c.left ∧ c.left < c'.right ∧ c'.right < c.right))
instance instDecidableArrow (c c' : D.Chamber) : Decidable (D.Arrow c c') := by
  unfold Arrow; infer_instance
/-- The arrow multiplicities of `Q(D)`: at most one arrow per ordered pair. -/
def wiringArrows (c c' : D.Chamber) : ℕ := if D.Arrow c c' then 1 else 0
end WiringDiagram
/-! ## Double wiring diagrams -/
/-- The two families of curves of a double wiring diagram. -/
inductive Colour
  | thick : Colour
  | thin : Colour deriving DecidableEq
/-- The **subword of one colour**: the levels of that colour's crossings, in order. -/
def subword {n : ℕ} (w : List (Fin (n + 1) × Colour)) (e : Colour) : List (Fin (n + 1)) :=
  (w.filter fun x => x.2 = e).map Prod.fst
structure DoubleWiringDiagram (n : ℕ) where
  word : List (Fin (n + 1) × Colour)
  length_subword : ∀ e, (subword word e).length = (n + 2).choose 2
  prod_subword : ∀ e, ((subword word e).map gapSwap).prod = Fin.revPerm
namespace DoubleWiringDiagram
variable {n : ℕ} (D : DoubleWiringDiagram n)
/-- The gaps cut by the crossings, in order. -/
def levels : List (Fin (n + 2)) := D.word.map fun x => x.1.castSucc
/-- The **multiplicity of a gap**: how many crossings cut it, of either colour. -/
def multiplicity (g : Fin (n + 2)) : ℕ := D.levels.count g
def countUpTo (g : Fin (n + 2)) (t : ℕ) : ℕ := (D.levels.take t).count g
structure Chamber where
  gap : Fin (n + 2)
  idx : ℕ
  idx_le : idx ≤ D.multiplicity gap
namespace Chamber
variable {D : DoubleWiringDiagram n} (c : D.Chamber)
/-- The **left position**, with `0` for `-∞`. -/
def left : ℕ := spanStart c.gap c.idx D.levels
/-- The **right position**, with `word.length + 1` for `+∞`. -/
def right : ℕ := if c.idx = D.multiplicity c.gap then D.word.length + 1
  else spanStart c.gap (c.idx + 1) D.levels
/-- A chamber **has a left end** when its left position is a genuine position. -/
def HasLeftEnd : Prop := c.left ≠ 0
/-- A chamber **has a right end** when its right position is a genuine position. -/
def HasRightEnd : Prop := c.right ≠ D.word.length + 1
/-- A chamber is **bounded** when it has both ends. -/
def Bounded : Prop := c.HasLeftEnd ∧ c.HasRightEnd
instance instDecidableHasLeftEnd : Decidable c.HasLeftEnd :=
  inferInstanceAs (Decidable (c.left ≠ 0))
instance instDecidableHasRightEnd : Decidable c.HasRightEnd :=
  inferInstanceAs (Decidable (c.right ≠ D.word.length + 1))
instance instDecidableBounded : Decidable c.Bounded :=
  inferInstanceAs (Decidable (c.HasLeftEnd ∧ c.HasRightEnd))
end Chamber
/-- Chambers correspond to a gap together with an index into that gap's crossings. -/
def chamberEquiv : D.Chamber ≃ ((g : Fin (n + 2)) × Fin (D.multiplicity g + 1)) where
  toFun c := ⟨c.gap, ⟨c.idx, Nat.lt_succ_of_le c.idx_le⟩⟩
  invFun p := ⟨p.1, p.2, Nat.le_of_lt_succ p.2.isLt⟩
  left_inv c := by cases c; rfl
  right_inv p := by cases p; rfl
instance instFintypeChamber : Fintype D.Chamber := Fintype.ofEquiv _ D.chamberEquiv.symm
end DoubleWiringDiagram
/-! ## Caldero–Keller as hypothesis
P. Caldero and B. Keller, Ann. Sci. ENS 39 (2006): mutation equivalent acyclic quivers are joined
by mutations at sources and sinks. FWZ cite it without proof. -/
def CalderoKeller.{u} : Prop :=
  ∀ {V V' : Type u} [Fintype V] [Fintype V'] [DecidableEq V] {Q : Quiver V} {Q' : Quiver V'},
    Acyclic Q → Acyclic Q' → Q.frozen = ∅ → Q'.frozen = ∅ → Q.MutationEquivalent Q' →
      ∃ p : Q.MutationPath, p.AtSourceOrSink ∧ Nonempty (p.result.Iso Q')
/-! ## Extended skew-symmetrizability -/
section
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}
def ExtSkewSymmetrizable (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) : Prop :=
  SkewSymmetrizable (B.submatrix (Fin.castLE hmn) id)
end
/-! ## Skew-symmetrization -/
section
variable {ι : Type*}
noncomputable def skewSymmetrization (B : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  .of fun i j => Real.sign (B i j) * √|B i j * B j i|
end
/-! ## Minors and Plücker coordinates -/
section
open Matrix
variable {R S : Type*} [CommRing R] [CommRing S] {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
def minor (z : Matrix ι κ R) (I : Finset ι) (J : Finset κ) : R :=
  if h : J.card = I.card then (z.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h)).det else 0
def pluckerCoord {k : ℕ} (z : Matrix (Fin k) κ R) (J : Finset κ) : R := minor z Finset.univ J
end
/-! ## Mutation identities and the Grassmann–Plücker relation as hypotheses
Exercises of FWZ Chapters 1–2 (arXiv:1608.05735). -/
section
universe u
def PluckerCoordThreeTerm : Prop :=
  ∀ {R : Type u} [CommRing R] {m : ℕ} (_ : 4 ≤ m) (z : Matrix (Fin 2) (Fin m) R) {i j k l : Fin m}
      (_ : i < j) (_ : j < k) (_ : k < l), pluckerCoord z {i, k} * pluckerCoord z {j, l} =
      pluckerCoord z {i, j} * pluckerCoord z {k, l} + pluckerCoord z {i, l} * pluckerCoord z {j, k}
variable {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}
/-- **Matrix mutation is an involution**, `μ_k(μ_k(B)) = B`. -/
def MatrixMutationMatrixMutation : Prop :=
  ∀ {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ} (hmn : n ≤ m)
      (B : Matrix (Fin m) (Fin n) R) (k : Fin n), matrixMutation hmn (matrixMutation hmn B k) k = B
def IsSkewSymmetrizingVector.SubmatrixMatrixMutation : Prop :=
  ∀ {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ} (hmn : n ≤ m)
      {C : Matrix (Fin m) (Fin n) R} {d : Fin n → ℤ}
      (_ : IsSkewSymmetrizingVector (C.submatrix (Fin.castLE hmn) id) d) (k : Fin n),
    IsSkewSymmetrizingVector ((matrixMutation hmn C k).submatrix (Fin.castLE hmn) id) d
/-- **Skew-symmetrization commutes with mutation**, `S(μ_k(B)) = μ_k(S(B))`. -/
def SkewSymmetrizable.SkewSymmetrizationMatrixMutation : Prop :=
  ∀ {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (_ : SkewSymmetrizable B) (hnn : n ≤ n) (k : Fin n),
    skewSymmetrization (ClusterAlgebras.matrixMutation hnn B k) =
      ClusterAlgebras.matrixMutation hnn (skewSymmetrization B) k
end
/-! ## Cartan matrices -/
section
open Matrix
variable {n : ℕ}
def IsSymmetrizer (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ) : Prop :=
  (∀ i, 0 < d i) ∧ ∀ i j, d i * A i j = d j * A j i
def IsGeneralizedCartan (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i, A i i = 2) ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧ ∃ d, IsSymmetrizer A d
def IsCartanFiniteType (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsGeneralizedCartan A ∧ ∃ d, IsSymmetrizer A d ∧ ∀ v : Fin n → ℝ, v ≠ 0 →
      0 < v ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ v)
def coxeterGraph (A : Matrix (Fin n) (Fin n) ℤ) : FiniteSimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => A i j ≠ 0
/-- A matrix is **indecomposable** when its Coxeter graph is connected. -/
def IsIndecomposable (A : Matrix (Fin n) (Fin n) ℤ) : Prop := (coxeterGraph A).Connected
end
/-! ## Seeds and seed mutation -/
section
variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ}
def IsFreeGeneratingTuple (x : Fin m → F) : Prop :=
  AlgebraicIndependent K x ∧ IntermediateField.adjoin K (Set.range x) = ⊤
variable {α : Type*} {n : ℕ}
def principalPart (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) α) : Matrix (Fin n) (Fin n) α :=
  B.submatrix (Fin.castLE hmn) id
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
@[ext]
structure SeedData (F : Type*) (m n : ℕ) where
  extCluster : Fin m → F
  extExchangeMatrix : Matrix (Fin m) (Fin n) ℤ
def IsLabeledSeed (hmn : n ≤ m) (S : SeedData F m n) : Prop :=
  IsFreeGeneratingTuple K S.extCluster ∧ ExtSkewSymmetrizable hmn S.extExchangeMatrix
variable {K}
def exchangeMonomialPos (x : Fin m → F) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) : F :=
  ∏ i ∈ Finset.univ.filter (fun i => 0 < B i k), x i ^ B i k
def exchangeMonomialNeg (x : Fin m → F) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) : F :=
  ∏ i ∈ Finset.univ.filter (fun i => B i k < 0), x i ^ (-B i k)
def seedMutation (hmn : n ≤ m) (S : SeedData F m n) (k : Fin n) : SeedData F m n where
  extCluster := Function.update S.extCluster (Fin.castLE hmn k)
    ((exchangeMonomialPos S.extCluster S.extExchangeMatrix k +
        exchangeMonomialNeg S.extCluster S.extExchangeMatrix k) / S.extCluster (Fin.castLE hmn k))
  extExchangeMatrix := matrixMutation hmn S.extExchangeMatrix k
end
/-! ## Seed patterns -/
section
variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}
structure RegularTree (n : ℕ) where
  word : List (Fin n)
  isChain_ne : word.IsChain (· ≠ ·)
def RegularTree.Adj (k : Fin n) (t t' : RegularTree n) : Prop :=
  t'.word = t.word ++ [k] ∨ t.word = t'.word ++ [k]
variable (K) in
def IsSeedPattern (hmn : n ≤ m) (P : RegularTree n → SeedData F m n) : Prop :=
  (∀ t, IsLabeledSeed K hmn (P t)) ∧
    ∀ (k : Fin n) (t t' : RegularTree n), RegularTree.Adj k t t' → P t' = seedMutation hmn (P t) k
end
/-! ## Dynkin types -/
section
open Matrix
def dynkinTreeDRel (m : ℕ) (i j : Fin m) : Prop :=
  ((i : ℕ) + 1 = j ∧ (j : ℕ) + 2 ≤ m) ∨ ((i : ℕ) + 3 = m ∧ (j : ℕ) + 1 = m)
instance instDecidableRelDynkinTreeDRel (m : ℕ) : DecidableRel (dynkinTreeDRel m) :=
  fun _ _ => by unfold dynkinTreeDRel; infer_instance
def dynkinTreeD (m : ℕ) : FiniteSimpleGraph (Fin m) := SimpleGraph.fromRel (dynkinTreeDRel m)
instance instDecidableRelDynkinTreeDAdj (m : ℕ) : DecidableRel (dynkinTreeD m).Adj :=
  fun _ _ => decidable_of_iff _ (SimpleGraph.fromRel_adj _ _ _).symm
def cartanOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Fin n) (Fin n) ℤ := of fun i j => if i = j then 2 else if G.Adj i j then -1 else 0
/-- `C(A_n)`: edges `{i, i+1}`. -/
def cartanA (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if i = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0
/-- `C(B_n)`: the matrix `C(A_n)` with its `1`-based entry `(1, 2)` replaced by `-2`. -/
def cartanB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then -2 else cartanA n i j
/-- `C(C_n)`: the matrix `C(A_n)` with its `1`-based entry `(2, 1)` replaced by `-2`. -/
def cartanC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then -2 else cartanA n i j
/-- `C(D_n)`: the simply-laced Cartan matrix of the tree `D_n`. -/
def cartanD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := cartanOfGraph (dynkinTreeD n)
def dynkinERel (n : ℕ) (i j : Fin n) : Prop :=
  ((i : ℕ) + 1 = j ∧ (j : ℕ) + 2 ≤ n) ∨ ((i : ℕ) = 2 ∧ (j : ℕ) + 1 = n)
instance instDecidableRelDynkinERel (n : ℕ) : DecidableRel (dynkinERel n) :=
  fun _ _ => by unfold dynkinERel; infer_instance
/-- The graph `E_n`: the path `1 — ⋯ — (n - 1)` with the vertex `n` attached to `3`. -/
def dynkinGraphE (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.fromRel (dynkinERel n)
instance instDecidableRelDynkinGraphEAdj (n : ℕ) : DecidableRel (dynkinGraphE n).Adj :=
  fun _ _ => decidable_of_iff _ (SimpleGraph.fromRel_adj _ _ _).symm
/-- `C(E_n)`: the simply-laced Cartan matrix of `E_n`. -/
def cartanE (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := cartanOfGraph (dynkinGraphE n)
/-- `C(F_4)`: the matrix `C(A_4)` with its `1`-based entry `(3, 2)` replaced by `-2`. -/
def cartanF₄ : Matrix (Fin 4) (Fin 4) ℤ :=
  of fun i j => if (i : ℕ) = 2 ∧ (j : ℕ) = 1 then -2 else cartanA 4 i j
/-- `C(G_2)`: the matrix `C(A_2)` with its `1`-based entry `(1, 2)` replaced by `-3`. -/
def cartanG₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then -3 else cartanA 2 i j
inductive DynkinSymbol where
  | A (n : ℕ) (hn : 1 ≤ n)
  | B (n : ℕ) (hn : 2 ≤ n)
  | C (n : ℕ) (hn : 3 ≤ n)
  | D (n : ℕ) (hn : 4 ≤ n)
  | E (n : ℕ) (hn : 6 ≤ n ∧ n ≤ 8)
  | F₄
  | G₂
  deriving DecidableEq
namespace DynkinSymbol
/-- The **rank** of a Dynkin symbol: its subscript. -/
def rank : DynkinSymbol → ℕ
  | A n _ => n
  | B n _ => n
  | C n _ => n
  | D n _ => n
  | E n _ => n
  | F₄ => 4
  | G₂ => 2
/-- The **Cartan matrix** `C(X)` of a Dynkin symbol `X`. -/
def cartan : (X : DynkinSymbol) → Matrix (Fin X.rank) (Fin X.rank) ℤ
  | A n _ => cartanA n
  | B n _ => cartanB n
  | C n _ => cartanC n
  | D n _ => cartanD n
  | E n _ => cartanE n
  | F₄ => cartanF₄
  | G₂ => cartanG₂
/-- The total rank `n₁ + ⋯ + n_r` of a list of Dynkin symbols. -/
def listRank : List DynkinSymbol → ℕ
  | [] => 0
  | X :: Xs => X.rank + listRank Xs
def listCartan : (Xs : List DynkinSymbol) → Matrix (Fin (listRank Xs)) (Fin (listRank Xs)) ℤ
  | [] => 0
  | X :: Xs => reindex finSumFinEquiv finSumFinEquiv (fromBlocks X.cartan 0 0 (listCartan Xs))
end DynkinSymbol
def IsOfDynkinType {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (Xs : List DynkinSymbol) : Prop :=
  ∃ σ : Fin n ≃ Fin (DynkinSymbol.listRank Xs), ∀ i j,
    A i j = DynkinSymbol.listCartan Xs (σ i) (σ j)
end
/-! ## The Cartan–Killing classification as hypothesis
Kac, *Infinite-dimensional Lie algebras*, Ch. 4: an indecomposable Cartan matrix of finite type
is of a single Dynkin type. FWZ cite it. -/
section
def CartanKilling : Prop :=
  ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (_ : IsCartanFiniteType A) (_ : IsIndecomposable A),
      ∃ X : DynkinSymbol, IsOfDynkinType A [X]
end
/-! ## The Cartan counterpart -/
section
open Matrix
variable {n : ℕ}
def cartanCounterpart (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if i = j then 2 else -|B i j|
end
/-! ## Mutation equivalence of matrices -/
section
open Matrix
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}
def matrixMutationList (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (ks : List (Fin n)) :
    Matrix (Fin m) (Fin n) R := ks.foldl (matrixMutation hmn) B
def MutationEquiv (B B' : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ (ks : List (Fin n)) (π : Equiv.Perm (Fin n)),
    B' = (matrixMutationList le_rfl B ks).submatrix π π
end
/-! ## Seed patterns of finite type -/
section
variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}
def IsFiniteType (P : RegularTree n → SeedData F m n) : Prop := (Set.range P).Finite
end
/-! ## `2`-finite matrices -/
section
variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}
def IsTwoFinite (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  SkewSymmetrizable B ∧ ∀ B' : Matrix (Fin n) (Fin n) ℤ, MutationEquiv B B' →
    ∀ i j, |B' i j * B' j i| ≤ 3
end
/-! ## Triangulations of a polygon and their quivers -/
section
variable {m : ℕ} [NeZero m]
instance instDecidableSbtwZMod (a b c : ZMod m) : Decidable (sbtw a b c) := by
  match m, ‹NeZero m›, a, b, c with
  | (n + 1), _, a, b, c => exact decidable_of_iff _ Fin.sbtw_iff.symm
def IsSegment (e : Sym2 (ZMod m)) : Prop := ¬e.IsDiag
def IsSide (e : Sym2 (ZMod m)) : Prop := ∃ i : ZMod m, e = s(i, i + 1)
/-- A segment is a **diagonal** when it is not a side. -/
def IsDiagonal (e : Sym2 (ZMod m)) : Prop := IsSegment e ∧ ¬IsSide e
instance instDecidablePredIsSide : DecidablePred (IsSide (m := m)) := fun _ => by
  unfold IsSide; infer_instance
def Cross (e f : Sym2 (ZMod m)) : Prop :=
  ∃ a b c d : ZMod m, e = s(a, b) ∧ f = s(c, d) ∧ sbtw a c b ∧ sbtw b d a
abbrev IsClockwise (a b c : ZMod m) : Prop := sbtw a b c
structure IsTriangulation (T : Finset (Sym2 (ZMod m))) : Prop where
  isDiagonal : ∀ e ∈ T, IsDiagonal e
  noncrossing : ∀ e ∈ T, ∀ f ∈ T, ¬Cross e f
  maximal : ∀ e, IsDiagonal e → e ∉ T → ∃ f ∈ T, Cross e f
/-- The **segments of `T`**: its diagonals together with all the sides of the `m`-gon. -/
def segments (T : Finset (Sym2 (ZMod m))) : Finset (Sym2 (ZMod m)) := T ∪ Finset.univ.filter IsSide
def IsTriangle (T : Finset (Sym2 (ZMod m))) (t : Finset (ZMod m)) : Prop :=
  t.card = 3 ∧ ∀ u ∈ t, ∀ v ∈ t, u ≠ v → s(u, v) ∈ segments T
instance instDecidablePredIsTriangle (T : Finset (Sym2 (ZMod m))) :
    DecidablePred (IsTriangle T) := fun _ => by unfold IsTriangle; infer_instance
def arrowTriangles (T : Finset (Sym2 (ZMod m))) (σ σ' : Sym2 (ZMod m)) : Finset (Finset (ZMod m)) :=
  {t ∈ Finset.univ | IsTriangle T t ∧
    ∃ a b c : ZMod m, IsClockwise a b c ∧ σ = s(a, b) ∧ σ' = s(b, c) ∧ a ∈ t ∧ b ∈ t ∧ c ∈ t}
def polygonArrows (T : Finset (Sym2 (ZMod m))) (σ σ' : Sym2 (ZMod m)) : ℕ :=
  if IsSide σ ∧ IsSide σ' then 0 else (arrowTriangles T σ σ').card
/-- The vertices of the quiver of `T`: the segments of `T`. -/
def SegmentType (T : Finset (Sym2 (ZMod m))) : Type := {e : Sym2 (ZMod m) // e ∈ segments T}
instance instDecidableEqSegmentType (T : Finset (Sym2 (ZMod m))) : DecidableEq (SegmentType T) :=
  fun _ _ => decidable_of_iff _ Subtype.ext_iff.symm
instance instFintypeSegmentType (T : Finset (Sym2 (ZMod m))) : Fintype (SegmentType T) :=
  Subtype.fintype _
def polygonQuiver (T : Finset (Sym2 (ZMod m))) : Quiver (SegmentType T) where
  frozen := {σ ∈ Finset.univ | IsSide σ.1}
  arrows σ σ' := polygonArrows T σ.1 σ'.1
  isArrowSystem σ := by
    change polygonArrows T σ.1 σ.1 = 0
    unfold polygonArrows
    split
    · rfl
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro t ht
      obtain ⟨-, a, b, c, hcw, hσ, hσ', -⟩ := (Finset.mem_filter.1 ht).2
      rw [hσ, Sym2.eq_iff] at hσ'
      rcases hσ' with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
      · exact sbtw_irrefl_left hcw
      · exact sbtw_irrefl_left_right hcw
  twoCycleFree σ σ' := by
    change polygonArrows T σ.1 σ'.1 = 0 ∨ polygonArrows T σ'.1 σ.1 = 0
    by_cases hside : IsSide σ.1 ∧ IsSide σ'.1
    · exact Or.inl (ite_eq_left hside)
    by_contra hc
    obtain ⟨hz1, hz2⟩ := not_or.1 hc
    have e1 : polygonArrows T σ.1 σ'.1 = (arrowTriangles T σ.1 σ'.1).card := ite_eq_right hside
    have e2 : polygonArrows T σ'.1 σ.1 = (arrowTriangles T σ'.1 σ.1).card :=
      ite_eq_right fun h => hside ⟨h.2, h.1⟩
    obtain ⟨t, ht⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero fun h => hz1 (e1.trans h))
    obtain ⟨t', ht'⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero fun h => hz2 (e2.trans h))
    obtain ⟨-, a, b, c, hcw, hσ, hσ', -⟩ := (Finset.mem_filter.1 ht).2
    obtain ⟨-, a', b', c', hcw', hτ, hτ', -⟩ := (Finset.mem_filter.1 ht').2
    have hab : a ≠ b := by rintro rfl; exact sbtw_irrefl_left hcw
    have hbc : b ≠ c := by rintro rfl; exact sbtw_irrefl_right hcw
    have hac : a ≠ c := by rintro rfl; exact sbtw_irrefl_left_right hcw
    have e4 : (s(b, c) : Sym2 (ZMod m)) = s(a', b') := hσ'.symm.trans hτ
    rcases Sym2.eq_iff.1 (hσ.symm.trans hτ') with ⟨hA1, hA2⟩ | ⟨hB1, hB2⟩
    · rcases Sym2.eq_iff.1 e4 with ⟨-, hC2⟩ | ⟨hD1, -⟩
      · exact hac (hC2.trans hA1.symm).symm
      · exact hab (hD1.trans hA1.symm).symm
    · rcases Sym2.eq_iff.1 e4 with ⟨-, hC2⟩ | ⟨-, hD2⟩
      · exact hbc (hC2.trans hB2.symm).symm
      · subst hD2 hB2 hB1
        exact sbtw_asymm hcw hcw'
  frozen_eq_zero σ hσ σ' hσ' :=
    ite_eq_left (show IsSide σ.1 ∧ IsSide σ'.1 from ⟨by simpa using hσ, by simpa using hσ'⟩)
end
/-! ## Flips and tree orientations as hypotheses
Exercises of FWZ Chapter 5 (arXiv:1707.07190). -/
section
section Flip
variable {m : ℕ} [NeZero m]
/-- The result `(T \ {γ}) ∪ {γ'}` of the flip of `T` at `γ` with replacement `γ'`. -/
def flipTriangulation (T : Finset (Sym2 (ZMod m))) (γ γ' : Sym2 (ZMod m)) :
    Finset (Sym2 (ZMod m)) := insert γ' (T.erase γ)
def IsFlipReplacement (T : Finset (Sym2 (ZMod m))) (γ γ' : Sym2 (ZMod m)) : Prop :=
  IsTriangulation T ∧ γ ∈ T ∧ IsDiagonal γ' ∧ γ' ∉ T ∧ IsTriangulation (flipTriangulation T γ γ')
def PolygonQuiverMutateIsoFlip : Prop :=
  ∀ {m : ℕ} [NeZero m] {T : Finset (Sym2 (ZMod m))} {γ γ' : Sym2 (ZMod m)}
      (h : IsFlipReplacement T γ γ')
      (hk : (⟨γ, Finset.mem_union_left _ h.2.1⟩ : SegmentType T) ∉ (polygonQuiver T).frozen),
    ∃ e : ((polygonQuiver T).mutate hk).Iso (polygonQuiver (flipTriangulation T γ γ')),
      ∀ σ : SegmentType T, (e.equiv σ).1 = if σ.1 = γ then γ' else σ.1
end Flip
universe u
def Quiver.ExistsMutationPathOfIsTreeOrientation : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] {T : FiniteSimpleGraph V} (_ : IsFiniteTree T)
      {Q Q' : Quiver V} (_ : Q.IsTreeOrientation T) (_ : Q'.IsTreeOrientation T),
    ∃ p : Q.MutationPath, p.AtSourceOrSink ∧ p.result = Q'
end
/-! ## Folding -/
section
open Matrix MulAction
variable {G : Type*} [Group G] {m n mG nG : ℕ} [MulAction G (Fin m)]
variable (n) in
def IsMutableOrbit (ω : orbitRel.Quotient G (Fin m)) : Prop := ∀ i ∈ ω.orbit, (i : ℕ) < n
variable (G) in
structure IsGroupAdmissible (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ) : Prop where
  smul_eq : ∀ (g : G) (i : Fin m) (j j' : Fin n), Fin.castLE hmn j' = g • Fin.castLE hmn j →
    B (g • i) j' = B i j
  eq_zero : ∀ i i' : Fin n, Fin.castLE hmn i' ∈ orbit G (Fin.castLE hmn i) →
    B (Fin.castLE hmn i) i' = 0
  mul_nonneg : ∀ i i' : Fin m, i' ∈ orbit G i → ∀ j : Fin n, 0 ≤ B i j * B i' j
variable (G m n mG nG) in
structure OrbitLabelling where
  equiv : Fin mG ≃ orbitRel.Quotient G (Fin m)
  le : nG ≤ mG
  lt_iff : ∀ p : Fin mG, (p : ℕ) < nG ↔ IsMutableOrbit n (equiv p)
namespace OrbitLabelling
variable (θ : OrbitLabelling G m n mG nG)
open Classical in
/-- The orbit `θ(p)` as a finite set of indices. -/
noncomputable def orbit (p : Fin mG) : Finset (Fin m) :=
  Finset.univ.filter fun i => (Quotient.mk'' i : orbitRel.Quotient G (Fin m)) = θ.equiv p
open Classical in
/-- The mutable orbit `θ(q)`, `q < nG`, as a finite set of columns. -/
noncomputable def cols (hmn : n ≤ m) (q : Fin nG) : Finset (Fin n) :=
  Finset.univ.filter fun j => Fin.castLE hmn j ∈ θ.orbit (Fin.castLE θ.le q)
end OrbitLabelling
/-- The **increasing sequence** `s_K = (k₁, …, k_s)` of a set `K` of columns, `k₁ < ⋯ < k_s`. -/
def increasingSeq (K : Finset (Fin n)) : List (Fin n) := K.sort (· ≤ ·)
noncomputable def orbitSeq (θ : OrbitLabelling G m n mG nG) (hmn : n ≤ m) (ρ : List (Fin nG)) :
    List (Fin n) := ρ.flatMap fun r => increasingSeq (θ.cols hmn r)
def IsGloballyFoldable (θ : OrbitLabelling G m n mG nG) (hmn : n ≤ m)
    (B : Matrix (Fin m) (Fin n) ℤ) : Prop := IsGroupAdmissible G hmn B ∧
    ∀ ρ : List (Fin nG), IsGroupAdmissible G hmn (matrixMutationList hmn B (orbitSeq θ hmn ρ))
end
/-! ## Orbit labellings by representatives -/
namespace TypeBC
open Matrix MulAction
universe u
section Reps
variable {G : Type*} [Group G] {N NG : ℕ} [MulAction G (Fin N)]
noncomputable def orbitLabellingOfReps (r : Fin NG → Fin N)
    (hinj : ∀ p q, r q ∈ orbit G (r p) → p = q) (hsurj : ∀ i, ∃ p, i ∈ orbit G (r p)) :
    OrbitLabelling G N N NG NG where
  equiv := Equiv.ofBijective (fun p => (Quotient.mk'' (r p) : orbitRel.Quotient G (Fin N)))
    ⟨fun p q h => (hinj q p (orbitRel_apply.1 (Quotient.exact' h))).symm, fun ω => by
      induction ω using Quotient.inductionOn' with
      | h i =>
        obtain ⟨p, hp⟩ := hsurj i
        exact ⟨p, Quotient.sound' (orbitRel_apply.2 (mem_orbit_symm.1 hp))⟩⟩
  le := le_rfl
  lt_iff p := ⟨fun _ i _ => i.isLt, fun _ => p.isLt⟩
end Reps
end TypeBC
/-! ## Tagged arcs of a once-punctured polygon -/
namespace TypeD
variable {n : ℕ}
/-- The **clockwise distance** `d(i, j) ∈ [0, n - 1]`: the residue of `j - i` modulo `n`. -/
def cdist (i j : Fin n) : ℕ := ((j : ℕ) + n - i) % n
/-- The **residue** `ū ∈ Fin n` of an integer `u`: its remainder modulo `n`, in `[0, n - 1]`. -/
def vtx [NeZero n] (u : ℤ) : Fin n :=
  ⟨(u % n).toNat, (Int.toNat_lt (Int.emod_nonneg u (Int.natCast_ne_zero.2 (NeZero.ne n)))).2
    (Int.emod_lt_of_pos u (Int.natCast_pos.2 (NeZero.pos n)))⟩
/-- The **sheet** `η(u) = ⌊u / n⌋` of an integer `u`, equal to `(u - ū) / n`. -/
def sheet (n : ℕ) (u : ℤ) : ℤ := u / n
/-- The sheet difference `κ(u, v) = η(v) - η(u)` of two integers `u` and `v`. -/
def kappa (n : ℕ) (u v : ℤ) : ℤ := sheet n v - sheet n u
/-- The **cut indicator** `χ(i, j)`: `1` if `j < i` and `0` otherwise. -/
def cut (i j : Fin n) : ℤ := if j < i then 1 else 0
def interiorVertices [NeZero n] (i j : Fin n) : Finset (Fin n) :=
  (Finset.Ioo 0 (cdist i j)).image fun t : ℕ => vtx ((i : ℤ) + (t : ℤ))
/-- A **tag**: plain (`+`) or notched (`-`). -/
inductive Tag where
  | plain
  | notched
  deriving DecidableEq, Repr
instance : Fintype Tag := derive_fintype% Tag
/-- The other tag `-τ`. -/
def Tag.neg : Tag → Tag
  | plain => notched
  | notched => plain
instance Tag.instNeg : Neg Tag := ⟨Tag.neg⟩
inductive TaggedArc (n : ℕ) where
  | ordinary (i j : Fin n) (h : 2 ≤ cdist i j)
  | radius (τ : Tag) (i : Fin n)
  deriving DecidableEq, Fintype
def shadow [NeZero n] (i j : Fin n) : Finset (Fin n) :=
  (Finset.range (cdist i j)).image fun t : ℕ => vtx ((i : ℤ) + (t : ℤ))
/-- The symbols of **segments**: a tagged arc, a boundary segment `β_i`, or the loop `L_i`. -/
inductive DSeg (n : ℕ) where
  | arc (γ : TaggedArc n)
  | boundary (i : Fin n)
  | loop (i : Fin n)
  deriving DecidableEq
section
variable [NeZero n]
def ordArc (u v : ℤ) : TaggedArc n :=
  if h : 2 ≤ cdist (vtx u : Fin n) (vtx v) then .ordinary (vtx u) (vtx v) h
  else .radius .plain (vtx u)
def seg (u v : ℤ) : DSeg n := if v - u = 1 then .boundary (vtx u)
  else if v - u = n then .loop (vtx u) else .arc (ordArc u v)
namespace TaggedArc
def Compatible : TaggedArc n → TaggedArc n → Prop
  | ordinary i j _, ordinary k l _ =>
      shadow i j ⊆ shadow k l ∨ shadow k l ⊆ shadow i j ∨ Disjoint (shadow i j) (shadow k l)
  | ordinary i j _, radius _ a => a ∉ interiorVertices i j
  | radius _ a, ordinary i j _ => a ∉ interiorVertices i j
  | radius τ a, radius σ b => a = b ∨ τ = σ
end TaggedArc
def IsTaggedTriangulation (T : Finset (TaggedArc n)) : Prop :=
  (∀ γ ∈ T, ∀ δ ∈ T, γ.Compatible δ) ∧ ∀ γ, (∀ δ ∈ T, γ.Compatible δ) → γ ∈ T
end
end TypeD
/-! ## Triangulations of a run of integers -/
namespace TypeD
def IsRunChord (u v : ℤ) (c : ℤ × ℤ) : Prop :=
  u ≤ c.1 ∧ c.1 < c.2 ∧ c.2 ≤ v ∧ 2 ≤ c.2 - c.1 ∧ c ≠ (u, v)
instance instDecidablePredIsRunChord (u v : ℤ) : DecidablePred (IsRunChord u v) := fun _ => by
  unfold IsRunChord; infer_instance
def IsRunSegment (u v : ℤ) (T : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : Prop :=
  c ∈ T ∨ (u ≤ c.1 ∧ c.2 = c.1 + 1 ∧ c.2 ≤ v) ∨ c = (u, v)
instance instDecidablePredIsRunSegment (u v : ℤ) (T : Finset (ℤ × ℤ)) :
    DecidablePred (IsRunSegment u v T) := fun _ => by
  unfold IsRunSegment; infer_instance
def IsRunTriangle (u v : ℤ) (T : Finset (ℤ × ℤ)) (x y z : ℤ) : Prop :=
  x < y ∧ y < z ∧ IsRunSegment u v T (x, y) ∧ IsRunSegment u v T (y, z) ∧ IsRunSegment u v T (x, z)
instance instDecidableIsRunTriangle (u v : ℤ) (T : Finset (ℤ × ℤ)) (x y z : ℤ) :
    Decidable (IsRunTriangle u v T x y z) := by
  unfold IsRunTriangle; infer_instance
def intRange (u v : ℤ) : Finset ℤ := (Finset.range (v + 1 - u).toNat).image fun t : ℕ => u + t
/-- The finite set of triangles `(x, y, z)` of `T` with vertices in `[u, v]`. -/
def runTriangles (u v : ℤ) (T : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ × ℤ) :=
  (intRange u v ×ˢ intRange u v ×ˢ intRange u v).filter fun t =>
    IsRunTriangle u v T t.1 t.2.1 t.2.2
end TypeD
/-! ## Sectors and flips of tagged triangulations -/
namespace TypeD
variable {n : ℕ} [NeZero n]
/-- The `t ∈ [0, n - 1]` with `a + t + 1 ∈ R` (mod `n`). -/
def gapCandidates (R : Finset (Fin n)) (a : Fin n) : Finset ℕ :=
  (Finset.range n).filter fun t => (vtx ((a : ℤ) + ((t + 1 : ℕ) : ℤ)) : Fin n) ∈ R
def gap (R : Finset (Fin n)) (a : Fin n) : ℕ :=
  if h : (gapCandidates R a).Nonempty then (gapCandidates R a).min' h + 1 else n
/-- The **successor** `a⁺ = a + g_R(a)` (mod `n`). -/
def succ (R : Finset (Fin n)) (a : Fin n) : Fin n := vtx ((a : ℤ) + (gap R a : ℤ))
/-- The **radius set** of `T`: the positions of the radii in `T`. -/
def radiusSet (T : Finset (TaggedArc n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => TaggedArc.radius .plain i ∈ T ∨ TaggedArc.radius .notched i ∈ T
/-- The set `T_R(a)` of chords `c` of the sector run `[a, a + g_R(a)]` with `s(c) ∈ T`. -/
def sectorChords (T : Finset (TaggedArc n)) (R : Finset (Fin n)) (a : Fin n) : Finset (ℤ × ℤ) :=
  (intRange a (a + gap R a) ×ˢ intRange a (a + gap R a)).filter fun c =>
    IsRunChord a (a + gap R a) c ∧ ordArc c.1 c.2 ∈ T
/-- The **flip** `(T \ {γ}) ∪ {γ'}` of `T` at `γ` with replacement `γ'`. -/
def dFlip (T : Finset (TaggedArc n)) (γ γ' : TaggedArc n) : Finset (TaggedArc n) :=
  insert γ' (T.erase γ)
def IsDFlipReplacement (T : Finset (TaggedArc n)) (γ γ' : TaggedArc n) : Prop :=
  IsTaggedTriangulation T ∧ γ ∈ T ∧ γ' ∉ T ∧ IsTaggedTriangulation (dFlip T γ γ')
end TypeD
/-! ## The exchange matrix of a tagged triangulation -/
namespace TypeD
variable {n : ℕ} [NeZero n]
inductive DRow (n : ℕ) where
  | arc (γ : TaggedArc n)
  | boundary (i : Fin n)
  | lam (τ : Tag)
  deriving DecidableEq, Fintype
def DSeg.rows : DSeg n → Finset (DRow n)
  | arc γ => {.arc γ}
  | boundary i => {.boundary i}
  | loop a => {.arc (.radius .plain a), .arc (.radius .notched a)}
/-- `Ar_{s,s'}(δ, ε) = [δ ∈ E(s)][ε ∈ E(s')] - [ε ∈ E(s)][δ ∈ E(s')]`: an arrow `s → s'`. -/
def arrowMatrix (s s' : DSeg n) : Matrix (DRow n) (TaggedArc n) ℤ := Matrix.of fun δ ε =>
    (if δ ∈ s.rows ∧ DRow.arc ε ∈ s'.rows then 1 else 0) -
      (if DRow.arc ε ∈ s.rows ∧ δ ∈ s'.rows then 1 else 0)
/-- `U_{λ_τ,s}(δ, ε) = [δ = λ_τ][ε ∈ E(s)]`. -/
def lamMatrix (τ : Tag) (s : DSeg n) : Matrix (DRow n) (TaggedArc n) ℤ :=
  Matrix.of fun δ ε => if δ = .lam τ ∧ DRow.arc ε ∈ s.rows then 1 else 0
def cycMatrix (s₁ s₂ s₃ : DSeg n) : Matrix (DRow n) (TaggedArc n) ℤ :=
  arrowMatrix s₁ s₂ + arrowMatrix s₂ s₃ + arrowMatrix s₃ s₁
def outerTriangles (T : Finset (TaggedArc n)) : Finset (Fin n × ℤ × ℤ × ℤ) :=
  (radiusSet T).biUnion fun a =>
    (runTriangles a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a)).image
      fun t => (a, t)
/-- `T` has the radii of kind `P_τ`: at least two positions and no radius of tag `-τ`. -/
def IsPunctureKind (T : Finset (TaggedArc n)) (τ : Tag) : Prop :=
  2 ≤ (radiusSet T).card ∧ ∀ i, TaggedArc.radius (-τ) i ∉ T
instance instDecidableIsPunctureKind (T : Finset (TaggedArc n)) (τ : Tag) :
    Decidable (IsPunctureKind T τ) := inferInstanceAs (Decidable (_ ∧ _))
def punctureTriangles (T : Finset (TaggedArc n)) : Finset (Tag × Fin n) :=
  (Finset.univ ×ˢ radiusSet T).filter fun p => IsPunctureKind T p.1
def outerContribution (p : Fin n × ℤ × ℤ × ℤ) : Matrix (DRow n) (TaggedArc n) ℤ :=
  cycMatrix (seg p.2.1 p.2.2.1) (seg p.2.2.1 p.2.2.2) (seg p.2.1 p.2.2.2) +
    kappa n p.2.2.1 p.2.2.2 •
      (lamMatrix .plain (seg p.2.2.1 p.2.2.2) + lamMatrix .notched (seg p.2.2.1 p.2.2.2) -
        lamMatrix .plain (seg p.2.1 p.2.2.2) - lamMatrix .notched (seg p.2.1 p.2.2.2))
def punctureContribution (T : Finset (TaggedArc n)) (τ : Tag) (a : Fin n) :
    Matrix (DRow n) (TaggedArc n) ℤ :=
  cycMatrix (seg (a : ℤ) (a + gap (radiusSet T) a)) (.arc (.radius τ (succ (radiusSet T) a)))
      (.arc (.radius τ a)) + cut a (succ (radiusSet T) a) •
      (lamMatrix τ (seg (a : ℤ) (a + gap (radiusSet T) a)) -
        lamMatrix τ (.arc (.radius τ (succ (radiusSet T) a))) + lamMatrix (-τ) (.arc (.radius τ a)))
def digonContribution (T : Finset (TaggedArc n)) (a : Fin n) : Matrix (DRow n) (TaggedArc n) ℤ :=
  if TaggedArc.radius .plain a ∈ T ∧ TaggedArc.radius .notched a ∈ T then
    lamMatrix .notched (.arc (.radius .plain a)) + lamMatrix .plain (.arc (.radius .notched a))
  else 0
def dMatrix (T : Finset (TaggedArc n)) : Matrix (DRow n) (TaggedArc n) ℤ :=
  (∑ p ∈ outerTriangles T, outerContribution p) +
    (∑ p ∈ punctureTriangles T, punctureContribution T p.1 p.2) + ∑ a, digonContribution T a
def IsLabelling (T : Finset (TaggedArc n)) (ℓ : Fin n → TaggedArc n) : Prop :=
  Function.Injective ℓ ∧ Set.range ℓ = (T : Set (TaggedArc n))
def extLabel (ℓ : Fin n → TaggedArc n) (i : Fin (2 * n + 2)) : DRow n :=
  if h : (i : ℕ) < n then .arc (ℓ ⟨i, h⟩) else if h' : (i : ℕ) < 2 * n then
    .boundary ⟨i - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) (two_mul n ▸ h')⟩
  else if (i : ℕ) = 2 * n then .lam .plain else .lam .notched
/-- The **labelled matrix** `B̃•(T, ℓ)`: the `(2n + 2) × n` matrix with entries `b_{ℓ̂(i) ℓ(j)}`. -/
def labelledMatrix (T : Finset (TaggedArc n)) (ℓ : Fin n → TaggedArc n) :
    Matrix (Fin (2 * n + 2)) (Fin n) ℤ := Matrix.of fun i j => dMatrix T (extLabel ℓ i) (ℓ j)
def flipLabelling (ℓ : Fin n → TaggedArc n) (k : Fin n) (γ' : TaggedArc n) : Fin n → TaggedArc n :=
  Function.update ℓ k γ'
end TypeD
/-! ## Flips of tagged triangulations as hypothesis
An exercise of FWZ Section 5.4 (arXiv:1707.07190). -/
namespace TypeD
variable {n : ℕ} [NeZero n]
def LabelledMatrixDFlip : Prop :=
  ∀ {n : ℕ} [NeZero n] (_ : 3 ≤ n) {T : Finset (TaggedArc n)} {ℓ : Fin n → TaggedArc n}
      (_ : IsLabelling T ℓ) {k : Fin n} {γ' : TaggedArc n} (_ : IsDFlipReplacement T (ℓ k) γ'),
    labelledMatrix (dFlip T (ℓ k) γ') (flipLabelling ℓ k γ') =
      matrixMutation (Nat.le_add_right_of_le (Nat.le_mul_of_pos_left n Nat.two_pos))
        (labelledMatrix T ℓ) k
end TypeD
/-! ## The `E₆` lifts -/
section
open Matrix MulAction
universe u
namespace TypeFG
def e₆Involution : Fin 6 → Fin 6 := ![4, 3, 2, 1, 0, 5]
def E₆FoldGroup : Type := Multiplicative (ZMod 2)
instance instGroupE₆FoldGroup : Group E₆FoldGroup :=
  inferInstanceAs (Group (Multiplicative (ZMod 2)))
instance instFintypeE₆FoldGroup : Fintype E₆FoldGroup :=
  inferInstanceAs (Fintype (Multiplicative (ZMod 2)))
instance instMulActionE₆FoldGroup : MulAction E₆FoldGroup (Fin 6) where
  smul g i := if Multiplicative.toAdd (g : Multiplicative (ZMod 2)) = 0 then i else e₆Involution i
  one_smul := by decide
  mul_smul := by decide
instance instDecidableMemOrbitE₆FoldGroup (i i' : Fin 6) : Decidable (i' ∈ orbit E₆FoldGroup i) :=
  decidable_of_iff (i' = i ∨ i' = e₆Involution i) (by
    rw [mem_orbit_iff]
    revert i i'
    decide)
noncomputable def e₆OrbitLabelling : OrbitLabelling E₆FoldGroup 6 6 4 4 :=
  TypeBC.orbitLabellingOfReps ![5, 2, 1, 0] (by decide) (by decide)
def matrixE₆Lift (ε : Fin 3 → ℤˣ) : Matrix (Fin 6) (Fin 6) ℤ := !![0, -(ε 2 : ℤ), 0, 0, 0, 0;
    (ε 2 : ℤ), 0, -(ε 1 : ℤ), 0, 0, 0; 0, (ε 1 : ℤ), 0, (ε 1 : ℤ), 0, -(ε 0 : ℤ);
    0, 0, -(ε 1 : ℤ), 0, (ε 2 : ℤ), 0; 0, 0, 0, -(ε 2 : ℤ), 0, 0; 0, 0, (ε 0 : ℤ), 0, 0, 0]
end TypeFG
end
/-! ## Foldability of the `E₆` lifts as hypothesis
An exercise of FWZ Chapter 5 (arXiv:1707.07190). -/
namespace TypeFG
def IsGloballyFoldableMatrixE₆Lift : Prop := ∀ (ε : Fin 3 → ℤˣ),
    IsGloballyFoldable e₆OrbitLabelling le_rfl (matrixE₆Lift ε)
end TypeFG
/-! ## Diagrams, cycles and shapes -/
section
open Matrix
variable {n m N : ℕ}
/-- The **weight** of the indices `i, j` of an integer matrix `B`: `w_B(i, j) = |bᵢⱼ bⱼᵢ|`. -/
def diagramWeight (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℕ := (B i j * B j i).natAbs
def diagramGraph (B : Matrix (Fin n) (Fin n) ℤ) : FiniteSimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ 0 < diagramWeight B i j
  symm := ⟨fun i j h => ⟨h.1.symm, by
    have h2 := h.2
    unfold diagramWeight at h2 ⊢
    rwa [mul_comm]⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩
def IsInducedPath (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin m → Fin n) : Prop :=
  1 ≤ m ∧ Function.Injective v ∧ ∀ p q : Fin m, p ≠ q →
    ((diagramGraph B).Adj (v p) (v q) ↔ (p : ℕ) + 1 = q ∨ (q : ℕ) + 1 = p)
def IsChordlessCycle (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin m → Fin n) : Prop :=
  3 ≤ m ∧ Function.Injective v ∧ ∀ p q : Fin m, p ≠ q →
    ((diagramGraph B).Adj (v p) (v q) ↔ q = finRotate m p ∨ p = finRotate m q)
def cycleWeights (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin m → Fin n) : Fin m → ℕ :=
  fun p => diagramWeight B (v p) (v (finRotate m p))
def IsCyclicallyOriented (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin m → Fin n) : Prop :=
  (∀ p, 0 < B (v p) (v (finRotate m p))) ∨ ∀ p, 0 < B (v (finRotate m p)) (v p)
def orderedModel (f : ℕ → ℕ → ℕ) {M : ℕ} (p q : Fin M) : ℕ := if (p : ℕ) < q then f p q else f q p
def IsShapeOf (ω : Fin N → Fin N → ℕ) (M : ℕ) (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ e : Fin M ≃ Fin N, ∀ p q : Fin M, p ≠ q → ω (e p) (e q) = orderedModel f p q
def tShapeModel (a b c : ℕ) (p q : ℕ) : ℕ := if (p + 1 = q ∧ q ≤ a) ∨
      (p = 0 ∧ q = a + 1 ∧ 1 ≤ b) ∨ (a + 1 ≤ p ∧ p + 1 = q ∧ q ≤ a + b) ∨
      (p = 0 ∧ q = a + b + 1 ∧ 1 ≤ c) ∨ (a + b + 1 ≤ p ∧ p + 1 = q ∧ q ≤ a + b + c) then 1 else 0
def IsTShape (ω : Fin N → Fin N → ℕ) (a b c : ℕ) : Prop :=
  IsShapeOf ω (a + b + c + 1) (tShapeModel a b c)
def crownModel (s p q r : ℕ) (i j : ℕ) : ℕ :=
  let X := s + 3
  let Y := s + 3 + (p - 1)
  let Z := s + 3 + (p - 1) + (q - 1)
  if (i + 1 = j ∧ j ≤ s + 2) ∨ (i = 0 ∧ j = s + 2) ∨
      (i = 0 ∧ j = X ∧ 2 ≤ p) ∨ (X ≤ i ∧ i + 1 = j ∧ j < Y) ∨
      (i = 1 ∧ j = Y ∧ 2 ≤ q) ∨ (Y ≤ i ∧ i + 1 = j ∧ j < Z) ∨
      (i = 2 ∧ j = Z ∧ 2 ≤ r) ∨ (Z ≤ i ∧ i + 1 = j ∧ j < Z + (r - 1)) then 1 else 0
def IsCrownShape (B : Matrix (Fin N) (Fin N) ℤ) (s p q r : ℕ) : Prop :=
  1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ ∃ e : Fin (p + q + r + s) ≃ Fin N, (∀ i j : Fin (p + q + r + s), i ≠ j →
      diagramWeight B (e i) (e j) = orderedModel (crownModel s p q r) i j) ∧
    ∀ i j : Fin (p + q + r + s),
      ((i : ℕ) + 1 = j ∧ (j : ℕ) ≤ s + 2) ∨ ((i : ℕ) = s + 2 ∧ (j : ℕ) = 0) → 0 < B (e i) (e j)
def IsAdmissibleCycleWeights (w : Fin m → ℕ) : Prop := (∀ p, w p = 1) ∨
    (∃ h : m = 3, w ∘ Fin.cast h.symm ∈ ({![2, 2, 1], ![2, 1, 2], ![1, 2, 2]} : Set (Fin 3 → ℕ))) ∨
    ∃ h : m = 4, w ∘ Fin.cast h.symm ∈ ({![2, 1, 2, 1], ![1, 2, 1, 2]} : Set (Fin 4 → ℕ))
end
/-! ## Exercises on `2`-finite diagrams as hypotheses
Three exercises of FWZ Section 5.10 (arXiv:1707.07190). -/
section
def ExistsIsTShapeMatrixMutationListOfIsCrownShape : Prop :=
  ∀ {N : ℕ} {B : Matrix (Fin N) (Fin N) ℤ} (_ : SkewSymmetrizable B) {s p q r : ℕ}
      (_ : IsCrownShape B s p q r),
    ∃ t : List (Fin N), IsTShape (diagramWeight (matrixMutationList le_rfl B t)) (p + r - 1) q s
def IsChordlessCycle.IsCyclicallyOrientedOfIsTwoFinite : Prop :=
  ∀ {m : ℕ} {B : Matrix (Fin m) (Fin m) ℤ} {v : Fin m ≃ Fin m} (_ : IsChordlessCycle B v)
      (_ : IsTwoFinite B), IsCyclicallyOriented B v ∧ IsAdmissibleCycleWeights (cycleWeights B v)
def IsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne : Prop :=
  ∀ {B : Matrix (Fin 4) (Fin 4) ℤ} (_ : SkewSymmetrizable B) {v : Fin 4 ≃ Fin 4}
      (_ : IsChordlessCycle B v) (_ : ∀ p, 0 < B (v p) (v (finRotate 4 p)))
      (_ : cycleWeights B v = ![2, 1, 2, 1]),
    IsInducedPath (matrixMutationList le_rfl B [v 0, v 1, v 0]) ![v 2, v 1, v 0, v 3] ∧
      diagramWeight (matrixMutationList le_rfl B [v 0, v 1, v 0]) (v 2) (v 1) = 1 ∧
      diagramWeight (matrixMutationList le_rfl B [v 0, v 1, v 0]) (v 1) (v 0) = 2 ∧
      diagramWeight (matrixMutationList le_rfl B [v 0, v 1, v 0]) (v 0) (v 3) = 1
end
namespace Challenge
/-- **Quiver mutation is matrix mutation**. -/
theorem extExchangeMatrix_mutate_eq_matrixMutation {V : Type*} [Fintype V] [DecidableEq V]
    {m n : ℕ} (Q : Quiver V)
    (L : Labelling Q m n) (k : Fin n) (hk : L.equiv (Fin.castLE L.le k) ∉ Q.frozen) :
    extExchangeMatrix (Q.mutate hk) (L.mutate hk) = matrixMutation L.le (extExchangeMatrix Q L) k :=
  sorry
/-- **Mutation preserves the determinant**, when the mutated diagonal entry vanishes. -/
theorem det_matrixMutation_eq {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {n : ℕ} (hnn : n ≤ n) (B : Matrix (Fin n) (Fin n) R) (k : Fin n) (hk : B k k = 0) :
    (matrixMutation hnn B k).det = B.det := sorry
/-- **Mutation preserves the rank**, when the mutated diagonal entry vanishes. -/
theorem rank_matrixMutation_eq {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {m n : ℕ} (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n)
    (hk : B (Fin.castLE hmn k) k = 0) : (matrixMutation hmn B k).rank = B.rank := sorry
/-- **Mutation preserves the gcd of the entries**, granted that mutating twice at `k` is `B`. -/
theorem gcd_matrixMutation_eq_of_involutive {m n : ℕ} (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ)
    (k : Fin n) (hinv : matrixMutation hmn (matrixMutation hmn B k) k = B) :
    (Finset.univ.gcd fun p : Fin m × Fin n => matrixMutation hmn B k p.1 p.2) =
      Finset.univ.gcd fun p : Fin m × Fin n => B p.1 p.2 := sorry
/-- **Skew-symmetrizing vectors are unique up to a scalar**. -/
theorem div_eq_div_of_isSkewSymmetrizingVector {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {d d' : Fin n → ℤ} (hΓ : (diagram B).Connected) (hd : IsSkewSymmetrizingVector B d)
    (hd' : IsSkewSymmetrizingVector B d') (i j : Fin n) :
    (d i : ℚ) / (d' i : ℚ) = (d j : ℚ) / (d' j : ℚ) := sorry
/-- **The Markov quiver is self-similar**. -/
theorem nonempty_iso_markovQuiver_mutate {k : Fin 3} (hk : k ∉ markovQuiver.frozen) :
    Nonempty ((markovQuiver.mutate hk).Iso markovQuiver) := sorry
/-- **The arrows of a wiring diagram form a quiver**. -/
theorem isArrowSystem_and_twoCycleFree_wiringArrows {n : ℕ} (D : WiringDiagram n) :
    IsArrowSystem D.wiringArrows ∧ TwoCycleFree D.wiringArrows ∧
      ∀ c c' : D.Chamber, ¬c.Bounded → ¬c'.Bounded → D.wiringArrows c c' = 0 := sorry
/-- **A braid move is a mutation**. -/
theorem existsUnique_iso_mutate_of_braidMove {n : ℕ} (D D' : WiringDiagram n) (p : ℕ)
    (hp : p + 3 ≤ D.word.length) (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p)
    (hD' : D'.word = spliceWord D.word p [D.levelAt (p + 1), D.levelAt p, D.levelAt (p + 1)])
    (Q : Quiver D.Chamber) (hQa : Q.arrows = D.wiringArrows)
    (hQf : ∀ c : D.Chamber, c ∈ Q.frozen ↔ ¬c.Bounded)
    (Q' : Quiver D'.Chamber) (hQ'a : Q'.arrows = D'.wiringArrows)
    (hQ'f : ∀ c : D'.Chamber, c ∈ Q'.frozen ↔ ¬c.Bounded)
    (Y : D.Chamber) (hYgap : Y.gap = D.levelAt p)
    (hYidx : Y.idx = D.countUpTo (D.levelAt p) (p + 1)) (hY : Y ∉ Q.frozen)
    (Z : D'.Chamber) (hZgap : Z.gap = D'.levelAt p)
    (hZidx : Z.idx = D'.countUpTo (D'.levelAt p) (p + 1)) : (∃! ψ : D.Chamber ≃ D'.Chamber,
        ψ Y = Z ∧ ∀ c, c ≠ Y → (ψ c).chamberSet = c.chamberSet) ∧
      ∀ ψ : D.Chamber ≃ D'.Chamber, ψ Y = Z → (∀ c, c ≠ Y → (ψ c).chamberSet = c.chamberSet) →
        ∃ i : (Q.mutate hY).Iso Q', i.equiv = ψ := sorry
/-- **The chambers of a double wiring diagram**. -/
theorem card_chamber_and_card_bounded {n : ℕ} (D : DoubleWiringDiagram n) :
    Fintype.card D.Chamber = (n + 2) ^ 2 ∧
      (Finset.univ.filter fun c : D.Chamber => c.Bounded).card = (n + 1) ^ 2 := sorry
/-- **Tree orientations are mutation inequivalent**, granted the Caldero–Keller theorem. -/
theorem exists_isTreeOrientation_of_mutationEquivalent.{u} (hCK : CalderoKeller.{u})
    {V V' : Type u} [Fintype V]
    [Fintype V'] [DecidableEq V] {T : FiniteSimpleGraph V} {Q : Quiver V} {Q' : Quiver V'}
    (hT : IsFiniteTree T) (hQ : Q.IsTreeOrientation T) (hQ' : Acyclic Q')
    (hfQ' : Q'.frozen = ∅) (h : Q.MutationEquivalent Q') : ∃ T' : FiniteSimpleGraph V',
      IsFiniteTree T' ∧ Q'.IsTreeOrientation T' ∧ Nonempty (T ≃g T') := sorry
/-- **The finite type classification**, granted Cartan–Killing and the exercises above. -/
theorem isFiniteType_iff_exists_isCartanFiniteType.{u} {K : Type u} {F : Type*} [Field K]
    [Field F] [Algebra K F] {m n : ℕ} [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hCartanKilling : CartanKilling) (hExistsIsTShapeMatrixMutationListOfIsCrownShape :
      ExistsIsTShapeMatrixMutationListOfIsCrownShape)
    (hIsCyclicallyOrientedOfIsTwoFinite : IsChordlessCycle.IsCyclicallyOrientedOfIsTwoFinite)
    (hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne :
      IsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne)
    (hSubmatrixMatrixMutation : IsSkewSymmetrizingVector.SubmatrixMatrixMutation.{0})
    (hMatrixMutationMatrixMutation : MatrixMutationMatrixMutation.{0})
    (hPluckerCoordThreeTerm₀ : PluckerCoordThreeTerm.{0})
    (hPluckerCoordThreeTerm : PluckerCoordThreeTerm.{u})
    (hPolygonQuiverMutateIsoFlip : PolygonQuiverMutateIsoFlip)
    (hExistsMutationPathOfIsTreeOrientation : Quiver.ExistsMutationPathOfIsTreeOrientation.{0})
    (hSkewSymmetrizationMatrixMutation : SkewSymmetrizable.SkewSymmetrizationMatrixMutation)
    (hLabelledMatrixDFlip : TypeD.LabelledMatrixDFlip)
    (hIsGloballyFoldableMatrixE₆Lift : TypeFG.IsGloballyFoldableMatrixE₆Lift) : IsFiniteType P ↔
      ∃ t, IsCartanFiniteType (cartanCounterpart (principalPart hmn (P t).extExchangeMatrix)) :=
  sorry
end Challenge
end ClusterAlgebras

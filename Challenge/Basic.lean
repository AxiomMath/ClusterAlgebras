/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib

/-!
# The formal challenge

Results of S. Fomin, L. Williams and A. Zelevinsky, *Introduction to Cluster Algebras* (FWZ),
stated over Mathlib alone and left open.
-/

@[expose] public section

namespace ClusterAlgebras

/-! ## Arrow systems -/

/-- An **arrow system** on `V` assigns to each ordered pair of vertices the number of arrows
running from the first to the second, with no vertex joined to itself. -/
def IsArrowSystem {V : Type*} (a : V → V → ℕ) : Prop := ∀ v, a v v = 0

/-- The **signed count** of `a` at `(i, j)`: the excess of the arrows running from `i` to `j`
over those running back. -/
def signedCount {V : Type*} (a : V → V → ℕ) (i j : V) : ℤ := (a i j : ℤ) - (a j i : ℤ)

/-- An arrow system is **two-cycle-free** when no two vertices carry arrows in both
directions. -/
def TwoCycleFree {V : Type*} (a : V → V → ℕ) : Prop := ∀ i j, a i j = 0 ∨ a j i = 0

/-- The **cancellation** of `a`, which deletes as many opposed pairs of arrows between each
two vertices as it can. -/
def cancellation {V : Type*} (a : V → V → ℕ) (i j : V) : ℕ := a i j - min (a i j) (a j i)

/-- The **reversal** of `c` at `k`, which reverses every arrow with an end at `k` and leaves
the others alone. -/
def reversal {V : Type*} [DecidableEq V] (c : V → V → ℕ) (k i j : V) : ℕ :=
  if i = k ∨ j = k then c j i else c i j

/-! ## Quivers and quiver mutation -/

/-- A **quiver**: a finite vertex set, a subset of *frozen* vertices, and a two-cycle-free
arrow system carrying no arrow between two frozen vertices. The vertices outside `frozen`
are the *mutable* ones. -/
structure Quiver.{u_2} (V : Type u_2) [Fintype V] where
  /-- The frozen vertices. -/
  frozen : Finset V
  /-- The arrow multiplicities. -/
  arrows : V → V → ℕ
  /-- No vertex carries an arrow to itself. -/
  isArrowSystem : IsArrowSystem arrows
  /-- No two vertices carry arrows in both directions. -/
  twoCycleFree : TwoCycleFree arrows
  /-- No arrow joins two frozen vertices. -/
  frozen_eq_zero : ∀ u ∈ frozen, ∀ v ∈ frozen, arrows u v = 0

/-- The **first-step system** of `Q` at `k`, which adds to each pair not joining two frozen
vertices the number of paths through `k`. -/
def Quiver.stepOne {V : Type*} [Fintype V] [DecidableEq V] (Q : Quiver V) (k i j : V) : ℕ :=
  if i ∈ Q.frozen ∧ j ∈ Q.frozen then Q.arrows i j
  else Q.arrows i j + Q.arrows i k * Q.arrows k j

/-- The arrow system underlying the mutation of `Q` at `k`: adding the composite arrows
through `k`, reversing the arrows at `k`, then cancelling 2-cycles. -/
def Quiver.mutationArrows {V : Type*} [Fintype V] [DecidableEq V] (Q : Quiver V) (k : V) :
    V → V → ℕ :=
  cancellation (reversal (Q.stepOne k) k)

/-- The **mutation** of `Q` at the mutable vertex `k`. -/
def Quiver.mutate {V : Type*} [Fintype V] [DecidableEq V] (Q : Quiver V) {k : V}
    (hk : k ∉ Q.frozen) : Quiver V where
  frozen := Q.frozen
  arrows := Q.mutationArrows k
  isArrowSystem v := Nat.sub_eq_zero_of_le (min_self _).ge
  twoCycleFree i j :=
    (le_total (reversal (Q.stepOne k) k i j) (reversal (Q.stepOne k) k j i)).imp
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

/-- An **isomorphism** of quivers: a bijection of the vertices matching the frozen sets and
preserving every arrow count. -/
structure Quiver.Iso {V : Type*} [Fintype V] {V' : Type*} [Fintype V'] (Q : Quiver V)
    (Q' : Quiver V') where
  /-- The bijection on vertices. -/
  equiv : V ≃ V'
  /-- It matches the frozen sets. -/
  mem_frozen_iff : ∀ v, equiv v ∈ Q'.frozen ↔ v ∈ Q.frozen
  /-- It preserves every arrow count. -/
  arrows_eq : ∀ u v, Q'.arrows (equiv u) (equiv v) = Q.arrows u v

/-! ## Exchange matrices -/

/-- A **labelling** of the vertices of `Q` by `1, …, m` under which the mutable vertices are
exactly those numbered below `n`. -/
structure Labelling {V : Type*} [Fintype V] (Q : Quiver V) (m n : ℕ) where
  /-- The numbering of the vertices. -/
  equiv : Fin m ≃ V
  /-- The mutable indices form an initial segment, so there are at most `m` of them. -/
  le : n ≤ m
  /-- A vertex is frozen exactly when its index is at least `n`. -/
  mem_frozen_iff : ∀ i : Fin m, equiv i ∈ Q.frozen ↔ n ≤ (i : ℕ)

/-- The same numbering, read as a labelling of a mutation of `Q`. -/
def Labelling.mutate {V : Type*} {m n : ℕ} [Fintype V] [DecidableEq V] {Q : Quiver V}
    (L : Labelling Q m n) {k : V} (hk : k ∉ Q.frozen) :
    Labelling (Q.mutate hk) m n where
  equiv := L.equiv
  le := L.le
  mem_frozen_iff := L.mem_frozen_iff

/-- The **extended exchange matrix** of `Q` in the numbering `L`: rows run over all the
vertices, columns over the mutable ones, and the entry is the signed count. -/
def extExchangeMatrix {V : Type*} {m n : ℕ} [Fintype V] (Q : Quiver V) (L : Labelling Q m n) :
    Matrix (Fin m) (Fin n) ℤ :=
  Matrix.of fun i j => signedCount Q.arrows (L.equiv i) (L.equiv (Fin.castLE L.le j))

/-! ## Matrix mutation -/

/-- The **mutation of `B` in direction `k`**. The first clause negates row and column `k`;
the two middle clauses add `b i k * b k j` when those two entries share a sign, the sign of
the correction matching theirs; every other entry is unchanged. -/
def matrixMutation {R : Type*} [CommRing R] [LinearOrder R] {m n : ℕ} (hmn : n ≤ m)
    (B : Matrix (Fin m) (Fin n) R) (k : Fin n) : Matrix (Fin m) (Fin n) R :=
  Matrix.of fun i j =>
    if i = Fin.castLE hmn k ∨ j = k then -B i j
    else if 0 < B i k ∧ 0 < B (Fin.castLE hmn k) j then
      B i j + B i k * B (Fin.castLE hmn k) j
    else if B i k < 0 ∧ B (Fin.castLE hmn k) j < 0 then
      B i j - B i k * B (Fin.castLE hmn k) j
    else B i j

/-! ## Skew-symmetrizable matrices and their diagrams -/

/-- `d` is a **skew-symmetrizing vector** for `B` when its entries are positive and
rescaling the rows of `B` by them gives a skew-symmetric matrix. -/
def IsSkewSymmetrizingVector {R : Type*} [CommRing R] {n : ℕ} (B : Matrix (Fin n) (Fin n) R)
    (d : Fin n → ℤ) : Prop :=
  (∀ i, 0 < d i) ∧ ∀ i j, (d i : R) * B i j = -((d j : R) * B j i)

/-- `B` is **skew-symmetrizable** when it admits a skew-symmetrizing vector. -/
def SkewSymmetrizable {R : Type*} [CommRing R] {n : ℕ} (B : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ d : Fin n → ℤ, IsSkewSymmetrizingVector B d

/-- A **diagram** on `ι`: a set of directed edges between elements of `ι`, each carrying a
real weight. Weights are recorded as `0` off the edge set, so that two diagrams are equal
exactly when they have the same edges and agree on them. -/
structure Diagram.{u_2} (ι : Type u_2) where
  /-- The directed edges of the diagram. -/
  edges : Set (ι × ι)
  /-- The weight carried by each edge, and `0` off the edges. -/
  weight : ι × ι → ℝ
  /-- Only edges carry a weight. -/
  weight_eq_zero_of_notMem : ∀ p ∉ edges, weight p = 0

/-- The **diagram** `Γ(B)` of a real matrix `B`: its edges are the pairs `(i, j)` with
`b i j > 0`, and the edge `(i, j)` carries the weight `|b i j * b j i|`. -/
noncomputable def diagram {ι : Type*} (B : Matrix ι ι ℝ) : Diagram ι where
  edges := {p | 0 < B p.1 p.2}
  weight p := if 0 < B p.1 p.2 then |B p.1 p.2 * B p.2 p.1| else 0
  weight_eq_zero_of_notMem _ hp := ite_eq_right hp

/-- A diagram is **connected** when no splitting of the index type into two nonempty
complementary parts separates it: some edge of the diagram, in one direction or the other,
joins the two parts. -/
def Diagram.Connected {ι : Type*} (Γ : Diagram ι) : Prop :=
  ∀ P : Set ι, P.Nonempty → Pᶜ.Nonempty → ∃ i ∈ P, ∃ j ∈ Pᶜ, (i, j) ∈ Γ.edges ∨ (j, i) ∈ Γ.edges

/-! ## Graphs, trees, and acyclicity -/

/-- A finite simple graph is a simple graph on a finite vertex type. -/
@[nolint unusedArguments]
abbrev FiniteSimpleGraph (V : Type*) [Fintype V] := SimpleGraph V

/-- A quiver is an **orientation** of `G` when it has no frozen vertices, carries exactly one
arrow across each edge of `G` in one of the two directions, and carries no arrow between
non-adjacent vertices. -/
def Quiver.IsOrientation {V : Type*} [Fintype V] (Q : Quiver V) (G : FiniteSimpleGraph V) : Prop :=
  Q.frozen = ∅ ∧
    ∀ u v : V, u ≠ v →
      (G.Adj u v → Q.arrows u v + Q.arrows v u = 1) ∧
      (¬G.Adj u v → Q.arrows u v = 0 ∧ Q.arrows v u = 0)

/-- A **finite tree**: a finite simple graph that is connected and acyclic. -/
abbrev IsFiniteTree {V : Type*} [Fintype V] (T : FiniteSimpleGraph V) : Prop := T.IsTree

/-- An **orientation of a finite tree**: an orientation of it as a finite simple graph. -/
abbrev Quiver.IsTreeOrientation {V : Type*} [Fintype V] (Q : Quiver V)
    (T : FiniteSimpleGraph V) : Prop :=
  Q.IsOrientation T

/-- An **oriented cycle** of length `r` in `Q`, presented as a sequence `v` of vertices: `v`
closes up after `r` steps, its first `r` entries are pairwise distinct, and each of the `r`
steps carries at least one arrow. -/
def IsOrientedCycle {V : Type*} [Fintype V] (Q : Quiver V) (r : ℕ) (v : ℕ → V) : Prop :=
  1 ≤ r ∧ v r = v 0 ∧ Set.InjOn v (Set.Iio r) ∧ ∀ t < r, 0 < Q.arrows (v t) (v (t + 1))

/-- A quiver is **acyclic** when it contains no oriented cycle. -/
def Acyclic {V : Type*} [Fintype V] (Q : Quiver V) : Prop :=
  ∀ (r : ℕ) (v : ℕ → V), ¬IsOrientedCycle Q r v

/-! ## Mutation paths and mutation equivalence -/

/-- A **mutation path** from `Q`: a finite chain of mutations, each performed at a vertex
mutable in the quiver the chain has reached so far. -/
inductive Quiver.MutationPath.{u} {V : Type u} [Fintype V] [DecidableEq V] : Quiver V → Type u
  /-- The empty path from `Q`, whose result is `Q` itself. -/
  | nil (Q : Quiver V) : Quiver.MutationPath Q
  /-- Prefixing a path from `μ_k(Q)` with a mutation of `Q` at the mutable vertex `k` gives a
  path from `Q`. -/
  | cons {Q : Quiver V} {k : V} (hk : k ∉ Q.frozen) (p : Quiver.MutationPath (Q.mutate hk)) :
      Quiver.MutationPath Q

/-- The **result** of a mutation path: the last quiver of its chain. -/
def Quiver.MutationPath.result.{u} {V : Type u} [Fintype V] [DecidableEq V] :
    {Q : Quiver V} → Q.MutationPath → Quiver V
  | _, .nil Q => Q
  | _, .cons _ p => p.result

/-- A mutation path each of whose steps is performed at a vertex that is a source or a sink
of the quiver the path has reached. -/
def Quiver.MutationPath.AtSourceOrSink.{u} {V : Type u} [Fintype V] [DecidableEq V] :
    {Q : Quiver V} → Q.MutationPath → Prop
  | _, .nil _ => True
  | Q, .cons (k := k) _ p => (Q.IsSource k ∨ Q.IsSink k) ∧ p.AtSourceOrSink

/-- Two quivers are **mutation equivalent** when some mutation path from the first has a
result isomorphic to the second. -/
def Quiver.MutationEquivalent.{u, u_1} {V : Type u} [Fintype V] [DecidableEq V]
    {V' : Type u_1} [Fintype V']
    (Q : Quiver V) (Q' : Quiver V') : Prop :=
  ∃ p : Q.MutationPath, Nonempty (p.result.Iso Q')

/-! ## The Markov quiver -/

/-- The **Markov quiver**: three vertices, no frozen vertices, and a doubled arrow round the
cycle `0 → 1 → 2 → 0`. FWZ index the vertices `1, 2, 3`; here they are `0, 1, 2`. -/
def markovQuiver : Quiver (Fin 3) where
  frozen := ∅
  arrows u v := if u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 2 ∨ u = 2 ∧ v = 0 then 2 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; fin_cases i <;> fin_cases j <;> decide
  frozen_eq_zero := by decide

/-! ## Words, spans and crossings

The machinery both wiring-diagram sections run on. A crossing at level `g` exchanges the two
strands either side of the gap `g`, so it acts on levels as one adjacent transposition; a *span*
locates the stretch of a word between two consecutive crossings of one gap. -/

/-- The transposition of the two levels either side of the gap `g`. -/
def gapSwap {n : ℕ} (g : Fin (n + 1)) : Equiv.Perm (Fin (n + 2)) := Equiv.swap g.castSucc g.succ

/-- The first position preceded by exactly `j` occurrences of `g` in `l`. The value when `l` holds
fewer than `j` occurrences is junk; every use below supplies `j ≤ l.count g`. -/
def spanStart {α : Type*} [DecidableEq α] (g : α) : ℕ → List α → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | j + 1, a :: l => (if a = g then spanStart g j l else spanStart g (j + 1) l) + 1

/-- The list with the stretch of length `new.length` starting at `p` replaced by `new`. -/
def spliceWord {α : Type*} (l : List α) (p : ℕ) (new : List α) : List α :=
  l.take p ++ new ++ l.drop (p + new.length)

/-! ## Wiring diagrams -/

/-- A **wiring diagram** on `n + 2` strands: a word in the adjacent transpositions whose length
is the number of pairs of strands and whose product is the longest permutation. Being of that
length forces the word to be reduced. -/
structure WiringDiagram (n : ℕ) where
  /-- The levels of the crossings, left to right. -/
  word : List (Fin (n + 1))
  /-- There are as many crossings as pairs of strands. -/
  length_eq : word.length = (n + 2).choose 2
  /-- The crossings compose to the longest permutation. -/
  prod_eq : (word.map gapSwap).prod = Fin.revPerm

namespace WiringDiagram

variable {n : ℕ} (D : WiringDiagram n)

/-- The **level of the crossing at position `t`**, or `0` past the end of the word. -/
def levelAt (t : ℕ) : Fin (n + 1) := D.word.getD t 0

/-- The **multiplicity of the gap `g`**: the number of crossings at that level. -/
def multiplicity (g : Fin (n + 1)) : ℕ := D.word.count g

/-- How many crossings of `g` lie before position `t`. -/
def countUpTo (g : Fin (n + 1)) (t : ℕ) : ℕ := (D.word.take t).count g

/-- The permutation `u_t` reached after the first `t` crossings. The wire occupying level `ℓ`
after `t` crossings is `D.wire t ℓ`. -/
def wire (t : ℕ) : Equiv.Perm (Fin (n + 2)) := ((D.word.map gapSwap).take t).prod

/-- The **level of the wire `v`** after `t` crossings, the inverse reading of `wire`. -/
def levelOf (t : ℕ) (v : Fin (n + 2)) : Fin (n + 2) := (D.wire t).symm v

/-- The set `{u_t(1), …, u_t(g)}` of wires lying at or below the gap `g` after `t`
crossings. -/
def belowSet (t : ℕ) (g : Fin (n + 1)) : Finset (Fin (n + 2)) :=
  {v ∈ Finset.univ | D.levelOf t v ≤ g.castSucc}

/-- A **chamber** of `D`: a gap, together with an index counting how many crossings of that gap
lie to its left, written as the pair `(g, j)`. -/
structure Chamber where
  /-- The gap the chamber lies in. -/
  gap : Fin (n + 1)
  /-- How many crossings of `gap` lie to the left of the chamber. -/
  idx : ℕ
  /-- There are at most that many crossings of the gap in total. -/
  idx_le : idx ≤ D.multiplicity gap

namespace Chamber

variable {D} (c : D.Chamber)

/-- The **left position** of the chamber, with `0` standing for `-∞`. -/
def left : ℕ := spanStart c.gap c.idx D.word

/-- The **right position** of the chamber, with `word.length + 1` standing for `+∞`. -/
def right : ℕ :=
  if c.idx = D.multiplicity c.gap then D.word.length + 1
  else spanStart c.gap (c.idx + 1) D.word

/-- A chamber **has a left end** when its left position is a genuine position. -/
def HasLeftEnd : Prop := c.left ≠ 0

/-- A chamber **has a right end** when its right position is a genuine position. -/
def HasRightEnd : Prop := c.right ≠ D.word.length + 1

/-- A chamber is **bounded** when it has both ends, and **unbounded** otherwise. -/
def Bounded : Prop := c.HasLeftEnd ∧ c.HasRightEnd

/-- Having a left end is decidable, being an inequality between naturals. -/
instance instDecidableHasLeftEnd : Decidable c.HasLeftEnd :=
  inferInstanceAs (Decidable (c.left ≠ 0))

/-- Having a right end is decidable. -/
instance instDecidableHasRightEnd : Decidable c.HasRightEnd :=
  inferInstanceAs (Decidable (c.right ≠ D.word.length + 1))

/-- Boundedness is decidable. -/
instance instDecidableBounded : Decidable c.Bounded :=
  inferInstanceAs (Decidable (c.HasLeftEnd ∧ c.HasRightEnd))

/-- The **chamber set** `J(c)`: the wires lying below the chamber's gap, read anywhere in its
span. Read here at the left end; every position of the span gives the same set. -/
def chamberSet : Finset (Fin (n + 2)) := D.belowSet c.left c.gap

end Chamber

/-- Chambers correspond to a gap together with an index into that gap's crossings. -/
def chamberEquiv : D.Chamber ≃ ((g : Fin (n + 1)) × Fin (D.multiplicity g + 1)) where
  toFun c := ⟨c.gap, ⟨c.idx, Nat.lt_succ_of_le c.idx_le⟩⟩
  invFun p := ⟨p.1, p.2, Nat.le_of_lt_succ p.2.isLt⟩
  left_inv c := by cases c; rfl
  right_inv p := by cases p; rfl

/-- There are finitely many chambers. -/
instance instFintypeChamber : Fintype D.Chamber := Fintype.ofEquiv _ D.chamberEquiv.symm

/-- Equality of chambers is decidable. -/
instance instDecidableEqChamber : DecidableEq D.Chamber := fun c c' =>
  decidable_of_iff (D.chamberEquiv c = D.chamberEquiv c') D.chamberEquiv.apply_eq_iff_eq

/-- **The arrows of `Q(D)`.** There is an arrow from `c` to `c'` when at least one of the two
chambers is bounded, and either they lie in one gap and `c` ends where `c'` begins, or they lie
in adjacent gaps and their spans interleave strictly. -/
def Arrow (c c' : D.Chamber) : Prop :=
  (c.Bounded ∨ c'.Bounded) ∧
    ((c.gap = c'.gap ∧ c.right = c'.left) ∨
      (((c'.gap : ℕ) + 1 = (c.gap : ℕ) ∨ (c.gap : ℕ) + 1 = (c'.gap : ℕ)) ∧
        c'.left < c.left ∧ c.left < c'.right ∧ c'.right < c.right))

/-- Whether there is an arrow between two chambers is decidable. -/
instance instDecidableArrow (c c' : D.Chamber) : Decidable (D.Arrow c c') := by
  unfold Arrow; infer_instance

/-- The arrow multiplicities of `Q(D)`: at most one arrow per ordered pair. -/
def wiringArrows (c c' : D.Chamber) : ℕ := if D.Arrow c c' then 1 else 0

end WiringDiagram

/-! ## Double wiring diagrams -/

/-- The two families of curves of a double wiring diagram. -/
inductive Colour
  /-- The thick family. -/
  | thick : Colour
  /-- The thin family. -/
  | thin : Colour
  deriving DecidableEq

/-- The **subword of one colour**: the levels of that colour's crossings, in order. -/
def subword {n : ℕ} (w : List (Fin (n + 1) × Colour)) (e : Colour) : List (Fin (n + 1)) :=
  (w.filter fun x => x.2 = e).map Prod.fst

/-- A **double wiring diagram** on `n + 2` strands: an interleaved word whose letters carry a
colour, each colour's subword being a wiring diagram on the same strands. -/
structure DoubleWiringDiagram (n : ℕ) where
  /-- The levels and colours of the crossings, left to right. -/
  word : List (Fin (n + 1) × Colour)
  /-- Each colour crosses each pair of strands once. -/
  length_subword : ∀ e, (subword word e).length = (n + 2).choose 2
  /-- Each colour's crossings compose to the longest permutation. -/
  prod_subword : ∀ e, ((subword word e).map gapSwap).prod = Fin.revPerm

namespace DoubleWiringDiagram

variable {n : ℕ} (D : DoubleWiringDiagram n)

/-- The gaps cut by the crossings, in order. A crossing of level `g` cuts the gap `g.castSucc`. -/
def levels : List (Fin (n + 2)) := D.word.map fun x => x.1.castSucc

/-- The **multiplicity of a gap**: how many crossings cut it, of either colour. -/
def multiplicity (g : Fin (n + 2)) : ℕ := D.levels.count g

/-- How many crossings of `g` lie before position `t`. -/
def countUpTo (g : Fin (n + 2)) (t : ℕ) : ℕ := (D.levels.take t).count g

/-- A **chamber** of `D`: a gap, together with an index counting how many crossings of that gap —
of either colour — lie to its left. -/
structure Chamber where
  /-- The gap the chamber sits in. -/
  gap : Fin (n + 2)
  /-- How many crossings of that gap lie to its left. -/
  idx : ℕ
  /-- There are no more of them than the gap has crossings. -/
  idx_le : idx ≤ D.multiplicity gap

namespace Chamber

variable {D : DoubleWiringDiagram n} (c : D.Chamber)

/-- The **left position**, with `0` for `-∞`. -/
def left : ℕ := spanStart c.gap c.idx D.levels

/-- The **right position**, with `word.length + 1` for `+∞`. -/
def right : ℕ :=
  if c.idx = D.multiplicity c.gap then D.word.length + 1
  else spanStart c.gap (c.idx + 1) D.levels

/-- A chamber **has a left end** when its left position is a genuine position. -/
def HasLeftEnd : Prop := c.left ≠ 0

/-- A chamber **has a right end** when its right position is a genuine position. -/
def HasRightEnd : Prop := c.right ≠ D.word.length + 1

/-- A chamber is **bounded** when it has both ends. -/
def Bounded : Prop := c.HasLeftEnd ∧ c.HasRightEnd

/-- Having a left end is decidable, being an inequality between naturals. -/
instance instDecidableHasLeftEnd : Decidable c.HasLeftEnd :=
  inferInstanceAs (Decidable (c.left ≠ 0))

/-- Having a right end is decidable. -/
instance instDecidableHasRightEnd : Decidable c.HasRightEnd :=
  inferInstanceAs (Decidable (c.right ≠ D.word.length + 1))

/-- Boundedness is decidable. -/
instance instDecidableBounded : Decidable c.Bounded :=
  inferInstanceAs (Decidable (c.HasLeftEnd ∧ c.HasRightEnd))

end Chamber

/-- Chambers correspond to a gap together with an index into that gap's crossings. -/
def chamberEquiv : D.Chamber ≃ ((g : Fin (n + 2)) × Fin (D.multiplicity g + 1)) where
  toFun c := ⟨c.gap, ⟨c.idx, Nat.lt_succ_of_le c.idx_le⟩⟩
  invFun p := ⟨p.1, p.2, Nat.le_of_lt_succ p.2.isLt⟩
  left_inv c := by cases c; rfl
  right_inv p := by cases p; rfl

/-- There are finitely many chambers. -/
instance instFintypeChamber : Fintype D.Chamber := Fintype.ofEquiv _ D.chamberEquiv.symm

end DoubleWiringDiagram

/-! ## Caldero–Keller as hypothesis

P. Caldero and B. Keller, *From triangulated categories to cluster algebras II*,
Ann. Sci. École Norm. Sup. (4) **39** (2006), no. 6, 983–1009: mutation equivalent acyclic
quivers are joined by mutations at sources and sinks alone. FWZ state this without
proof, its published proof running through cluster categories; it enters
`exists_isTreeOrientation_of_mutationEquivalent` as a hypothesis. -/

/-- **Caldero–Keller.** Two acyclic quivers without frozen vertices that are mutation
equivalent are joined by a sequence of mutations performed only at sources and sinks. -/
def CalderoKeller.{u} : Prop :=
  ∀ {V V' : Type u} [Fintype V] [Fintype V'] [DecidableEq V] {Q : Quiver V} {Q' : Quiver V'},
    Acyclic Q → Acyclic Q' → Q.frozen = ∅ → Q'.frozen = ∅ → Q.MutationEquivalent Q' →
      ∃ p : Q.MutationPath, p.AtSourceOrSink ∧ Nonempty (p.result.Iso Q')

/-! ## Extended skew-symmetrizability -/

section

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}

/-- `B` is **extended skew-symmetrizable** when its top `n × n` submatrix — the first
`n` rows — is skew-symmetrizable. -/
def ExtSkewSymmetrizable (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) : Prop :=
  SkewSymmetrizable (B.submatrix (Fin.castLE hmn) id)

end

/-! ## Skew-symmetrization -/

section

variable {ι : Type*}

/-- The **skew-symmetrization** `S(B)` of a real matrix `B`: the matrix with entries
`s i j = sgn (b i j) * √|b i j * b j i|`.

For a skew-symmetrizable `B` this is the skew-symmetric matrix obtained from `B` by the
diagonal conjugation `b i j ↦ √(d i / d j) * b i j` of any skew-symmetrizing vector `d`. -/
noncomputable def skewSymmetrization (B : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  .of fun i j => Real.sign (B i j) * √|B i j * B j i|

end

/-! ## Minors and Plücker coordinates -/

section

open Matrix

variable {R S : Type*} [CommRing R] [CommRing S] {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]

/-- The **minor** `Δ_{I,J}(z)`: for finite sets `I` of rows and `J` of columns with
`|I| = |J| = k`, listed increasingly as `i₁ < ⋯ < i_k` and `j₁ < ⋯ < j_k`, the determinant of the
`k × k` matrix `(z_{i_s j_t})`. When `|I| ≠ |J|` it is `0`, a junk value no statement relies on. -/
def minor (z : Matrix ι κ R) (I : Finset ι) (J : Finset κ) : R :=
  if h : J.card = I.card then (z.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h)).det else 0

/-- The **Plücker coordinate** `P_J(z) = Δ_{[1,k],J}(z)` of a `k × m` matrix `z`, for a set `J` of
`k` columns: the minor on all the rows and the columns `J`. -/
def pluckerCoord {k : ℕ} (z : Matrix (Fin k) κ R) (J : Finset κ) : R :=
  minor z Finset.univ J

end

/-! ## Mutation identities and the Grassmann–Plücker relation as hypotheses

S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras. Chapters 1–3*,
arXiv:1608.05735: exercises of Chapters 1 and 2, which enter
`isFiniteType_iff_exists_isCartanFiniteType` as hypotheses. -/

section

universe u

/-- **The three-term Grassmann–Plücker relation.** For a `2 × m` matrix and columns
`i < j < k < l`, `P_{ik} P_{jl} = P_{ij} P_{kl} + P_{il} P_{jk}`.

An unlabelled exercise in FWZ, Section 1.2. -/
def PluckerCoordThreeTerm : Prop :=
  ∀ {R : Type u} [CommRing R] {m : ℕ} (_ : 4 ≤ m) (z : Matrix (Fin 2) (Fin m) R) {i j k l : Fin m}
      (_ : i < j) (_ : j < k) (_ : k < l),
    pluckerCoord z {i, k} * pluckerCoord z {j, l} =
      pluckerCoord z {i, j} * pluckerCoord z {k, l} + pluckerCoord z {i, l} * pluckerCoord z {j, k}

variable {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}

/-- **Matrix mutation is an involution**, `μ_k(μ_k(B)) = B`.

An exercise in FWZ on matrix mutation. -/
def MatrixMutationMatrixMutation : Prop :=
  ∀ {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ} (hmn : n ≤ m)
      (B : Matrix (Fin m) (Fin n) R) (k : Fin n),
    matrixMutation hmn (matrixMutation hmn B k) k = B

/-- **Mutation preserves a skew-symmetrizing vector of the top submatrix.** If `d`
skew-symmetrizes the top `n × n` submatrix of `C`, then it skew-symmetrizes the top `n × n`
submatrix of `μ_k(C)`.

An exercise in FWZ on matrix mutation, which asks for the mutated matrix to be extended
skew-symmetrizable *with the same* `d`. -/
def IsSkewSymmetrizingVector.SubmatrixMatrixMutation : Prop :=
  ∀ {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ} (hmn : n ≤ m)
      {C : Matrix (Fin m) (Fin n) R} {d : Fin n → ℤ}
      (_ : IsSkewSymmetrizingVector (C.submatrix (Fin.castLE hmn) id) d) (k : Fin n),
    IsSkewSymmetrizingVector ((matrixMutation hmn C k).submatrix (Fin.castLE hmn) id) d

/-- **Skew-symmetrization commutes with mutation**, `S(μ_k(B)) = μ_k(S(B))`.

An exercise in FWZ. -/
def SkewSymmetrizable.SkewSymmetrizationMatrixMutation : Prop :=
  ∀ {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (_ : SkewSymmetrizable B) (hnn : n ≤ n) (k : Fin n),
    skewSymmetrization (ClusterAlgebras.matrixMutation hnn B k) =
      ClusterAlgebras.matrixMutation hnn (skewSymmetrization B) k

end

/-! ## Cartan matrices -/

section

open Matrix

variable {n : ℕ}

/-- `d` is a **symmetrizer** of `A`: its entries are positive integers and `DA` is symmetric
for `D = diag(d)`, that is `dᵢ aᵢⱼ = dⱼ aⱼᵢ` for all `i, j`. -/
def IsSymmetrizer (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ) : Prop :=
  (∀ i, 0 < d i) ∧ ∀ i j, d i * A i j = d j * A j i

/-- A **symmetrizable generalized Cartan matrix**: an integer matrix with diagonal entries `2`,
nonpositive entries off the diagonal, and a symmetrizer. -/
def IsGeneralizedCartan (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i, A i i = 2) ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧ ∃ d, IsSymmetrizer A d

/-- A symmetrizable generalized Cartan matrix `A` is **of finite type**, or a *Cartan matrix of
finite type*, when for some symmetrizer `D = diag(d)` the symmetric matrix `DA` is positive
definite: `vᵀ D A v > 0` for every nonzero `v ∈ ℝⁿ`. -/
def IsCartanFiniteType (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsGeneralizedCartan A ∧ ∃ d, IsSymmetrizer A d ∧
    ∀ v : Fin n → ℝ, v ≠ 0 →
      0 < v ⬝ᵥ ((diagonal (fun i => (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ)) *ᵥ v)

/-- The **Coxeter graph** of an `n × n` matrix `A`: the finite simple graph on `[1, n]` in which
`i ≠ j` are adjacent when `aᵢⱼ ≠ 0 ∨ aⱼᵢ ≠ 0`. For a symmetrizable generalized Cartan matrix
this is equivalent to `aᵢⱼ ≠ 0`. -/
def coxeterGraph (A : Matrix (Fin n) (Fin n) ℤ) : FiniteSimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => A i j ≠ 0

/-- A matrix is **indecomposable** when its Coxeter graph is connected. Connectedness includes
nonemptiness, so the `0 × 0` matrix is not indecomposable. -/
def IsIndecomposable (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (coxeterGraph A).Connected

end

/-! ## Seeds and seed mutation -/

section

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ}

/-- `x` is a **free generating tuple** of `F` over `K` when its entries are algebraically
independent over `K` and generate `F` as a field over `K`, that is, `F = K(x₁, …, xₘ)`. -/
def IsFreeGeneratingTuple (x : Fin m → F) : Prop :=
  AlgebraicIndependent K x ∧ IntermediateField.adjoin K (Set.range x) = ⊤

variable {α : Type*} {n : ℕ}

/-- The **principal part** of an `m × n` matrix `B`, for `n ≤ m`: the `n × n` matrix formed
by its first `n` rows. It is the submatrix that `ExtSkewSymmetrizable` asks to be
skew-symmetrizable. -/
def principalPart (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) α) : Matrix (Fin n) (Fin n) α :=
  B.submatrix (Fin.castLE hmn) id

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The data of a labeled seed with none of its conditions: an *extended cluster*, an
`m`-tuple of elements of `F`, and an *extended exchange matrix*, an `m × n` integer matrix.
Seed mutation acts on this data, and `IsLabeledSeed` says when it is a labeled seed. -/
@[ext]
structure SeedData (F : Type*) (m n : ℕ) where
  /-- The extended cluster `x̃ = (x₁, …, xₘ)`. -/
  extCluster : Fin m → F
  /-- The extended exchange matrix `B̃`. -/
  extExchangeMatrix : Matrix (Fin m) (Fin n) ℤ

/-- `S` is a **labeled seed** in `F` over `K` when its extended cluster is a free generating
tuple of `F` over `K` and its extended exchange matrix is extended skew-symmetrizable. -/
def IsLabeledSeed (hmn : n ≤ m) (S : SeedData F m n) : Prop :=
  IsFreeGeneratingTuple K S.extCluster ∧ ExtSkewSymmetrizable hmn S.extExchangeMatrix

variable {K}

/-- The **positive exchange monomial** `M⁺ₖ(x̃, B̃)`: the product of `xᵢ ^ bᵢₖ` over the rows
`i` with `bᵢₖ > 0`. -/
def exchangeMonomialPos (x : Fin m → F) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) : F :=
  ∏ i ∈ Finset.univ.filter (fun i => 0 < B i k), x i ^ B i k

/-- The **negative exchange monomial** `M⁻ₖ(x̃, B̃)`: the product of `xᵢ ^ (-bᵢₖ)` over the
rows `i` with `bᵢₖ < 0`. -/
def exchangeMonomialNeg (x : Fin m → F) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) : F :=
  ∏ i ∈ Finset.univ.filter (fun i => B i k < 0), x i ^ (-B i k)

/-- **Seed mutation** in direction `k`: the entry of the extended cluster in position `k` is
replaced by `(M⁺ₖ + M⁻ₖ) / xₖ`, every other entry is kept, and the extended exchange matrix
is mutated in direction `k`. When `xₖ ≠ 0` the new entry `x'ₖ` satisfies the *exchange
relation* `xₖ x'ₖ = M⁺ₖ + M⁻ₖ`; when `xₖ = 0` it is `0`. -/
def seedMutation (hmn : n ≤ m) (S : SeedData F m n) (k : Fin n) : SeedData F m n where
  extCluster := Function.update S.extCluster (Fin.castLE hmn k)
    ((exchangeMonomialPos S.extCluster S.extExchangeMatrix k +
        exchangeMonomialNeg S.extCluster S.extExchangeMatrix k) /
      S.extCluster (Fin.castLE hmn k))
  extExchangeMatrix := matrixMutation hmn S.extExchangeMatrix k

end

/-! ## Seed patterns -/

section

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- A vertex of the **`n`-regular tree** `𝕋ₙ`: a finite sequence of elements of `[1, n]` in
which no two consecutive entries are equal. FWZ take `n ≥ 1`; nothing here uses
it. -/
structure RegularTree (n : ℕ) where
  /-- The sequence `(k₁, …, k_r)`. -/
  word : List (Fin n)
  /-- No two consecutive entries are equal. -/
  isChain_ne : word.IsChain (· ≠ ·)

/-- Two vertices of `𝕋ₙ` are joined by an **edge labelled `k`**, written `t —k— t'`, when
one is obtained from the other by appending `k` at the end. -/
def RegularTree.Adj (k : Fin n) (t t' : RegularTree n) : Prop :=
  t'.word = t.word ++ [k] ∨ t.word = t'.word ++ [k]

variable (K) in
/-- `P` is a **seed pattern** of rank `n` in `F` over `K` when it assigns a labeled seed to
every vertex of `𝕋ₙ` and the seeds at the two ends of an edge labelled `k` are related by
seed mutation in direction `k`. FWZ take `K` of characteristic zero and `n ≥ 1`;
the definition uses neither, so neither is assumed here. -/
def IsSeedPattern (hmn : n ≤ m) (P : RegularTree n → SeedData F m n) : Prop :=
  (∀ t, IsLabeledSeed K hmn (P t)) ∧
    ∀ (k : Fin n) (t t' : RegularTree n), RegularTree.Adj k t t' → P t' = seedMutation hmn (P t) k

end

/-! ## Dynkin types -/

section

open Matrix

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
def dynkinTreeD (m : ℕ) : FiniteSimpleGraph (Fin m) :=
  SimpleGraph.fromRel (dynkinTreeDRel m)

/-- Adjacency in `D_m` is decidable. -/
instance instDecidableRelDynkinTreeDAdj (m : ℕ) : DecidableRel (dynkinTreeD m).Adj :=
  fun _ _ => decidable_of_iff _ (SimpleGraph.fromRel_adj _ _ _).symm

/-- The simply-laced Cartan matrix of a graph `G`: `2` on the diagonal, `-1` at the edges of `G`,
and `0` elsewhere. -/
def cartanOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if i = j then 2 else if G.Adj i j then -1 else 0

/-- `C(A_n)`: edges `{i, i+1}`. Defined for every `n`. -/
def cartanA (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if i = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0

/-- `C(B_n)`: the matrix `C(A_n)` with its `1`-based entry `(1, 2)` replaced by `-2`. Defined
for every `n`; `C(B_1) = (2)`. -/
def cartanB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then -2 else cartanA n i j

/-- `C(C_n)`: the matrix `C(A_n)` with its `1`-based entry `(2, 1)` replaced by `-2`. Defined
for every `n`; `C(C_1) = (2)` and `C(C_2)` is the transpose of `C(B_2)`. -/
def cartanC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then -2 else cartanA n i j

/-- `C(D_n)`: the simply-laced Cartan matrix of the tree `D_n`. -/
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

/-- `C(E_n)`: the simply-laced Cartan matrix of `E_n`. Defined for every `n`; the Dynkin symbols
use `n ∈ {6, 7, 8}`. -/
def cartanE (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  cartanOfGraph (dynkinGraphE n)

/-- `C(F_4)`: the matrix `C(A_4)` with its `1`-based entry `(3, 2)` replaced by `-2`. -/
def cartanF₄ : Matrix (Fin 4) (Fin 4) ℤ :=
  of fun i j => if (i : ℕ) = 2 ∧ (j : ℕ) = 1 then -2 else cartanA 4 i j

/-- `C(G_2)`: the matrix `C(A_2)` with its `1`-based entry `(1, 2)` replaced by `-3`. -/
def cartanG₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then -3 else cartanA 2 i j

/-- A **Dynkin symbol**: one of `A_n` (`n ≥ 1`), `B_n` (`n ≥ 2`), `C_n` (`n ≥ 3`), `D_n`
(`n ≥ 4`), `E_n` (`n ∈ {6, 7, 8}`), `F_4`, `G_2`. -/
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

/-- The Cartan matrix `C(X)` of a list `X = (X¹, …, X^r)` of Dynkin symbols: the block-diagonal
matrix with diagonal blocks `C(X¹), …, C(X^r)` in this order. -/
def listCartan : (Xs : List DynkinSymbol) → Matrix (Fin (listRank Xs)) (Fin (listRank Xs)) ℤ
  | [] => 0
  | X :: Xs => reindex finSumFinEquiv finSumFinEquiv (fromBlocks X.cartan 0 0 (listCartan Xs))

end DynkinSymbol

/-- An `n × n` matrix `A` is **of type `X`**, for a list `X` of Dynkin symbols, when
`n = n₁ + ⋯ + n_r` and `A` has the same type as `C(X)`: `aᵢⱼ = C(X)_{σ(i)σ(j)}` for a bijection
`σ` from the indices of `A` to those of `C(X)`. For a single symbol `X` the list is `[X]`. -/
def IsOfDynkinType {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (Xs : List DynkinSymbol) : Prop :=
  ∃ σ : Fin n ≃ Fin (DynkinSymbol.listRank Xs), ∀ i j,
    A i j = DynkinSymbol.listCartan Xs (σ i) (σ j)

end

/-! ## The Cartan–Killing classification as hypothesis

V. G. Kac, *Infinite-dimensional Lie algebras*, 3rd ed., Cambridge University Press, 1990,
Chapter 4: every indecomposable Cartan matrix of finite type is of a single Dynkin type. It
enters `isFiniteType_iff_exists_isCartanFiniteType` as a hypothesis. -/

section

/-- **The Cartan–Killing classification.** An indecomposable Cartan matrix of finite type is of
type `X` for a single Dynkin symbol `X`. -/
def CartanKilling : Prop :=
  ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (_ : IsCartanFiniteType A) (_ : IsIndecomposable A),
      ∃ X : DynkinSymbol, IsOfDynkinType A [X]

end

/-! ## The Cartan counterpart -/

section

open Matrix

variable {n : ℕ}

/-- The **Cartan counterpart** of an `n × n` integer matrix `B`: the matrix `A(B)` with
`aᵢᵢ = 2` and `aᵢⱼ = -|bᵢⱼ|` for `i ≠ j`. FWZ define it for skew-symmetrizable `B`;
the formula makes sense for every matrix. -/
def cartanCounterpart (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => if i = j then 2 else -|B i j|

end

/-! ## Mutation equivalence of matrices -/

section

open Matrix

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}

/-- Mutation along a finite sequence of directions:
`matrixMutationList hmn B [k₁, …, k_r]` is `μ_{k_r} ⋯ μ_{k₁}(B)`, the list being
read left to right. -/
def matrixMutationList (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (ks : List (Fin n)) :
    Matrix (Fin m) (Fin n) R :=
  ks.foldl (matrixMutation hmn) B

/-- `B` and `B'` are **mutation equivalent** if some finite sequence of
mutations `k₁, …, k_r` and some permutation `π` of the indices satisfy
`B' = μ_{k_r} ⋯ μ_{k₁}(B) ∘ (π, π)`, that is
`B'ᵢⱼ = (μ_{k_r} ⋯ μ_{k₁}(B))_{π(i)π(j)}` for all `i, j`. -/
def MutationEquiv (B B' : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ (ks : List (Fin n)) (π : Equiv.Perm (Fin n)),
    B' = (matrixMutationList le_rfl B ks).submatrix π π

end

/-! ## Seed patterns of finite type -/

section

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- A seed pattern `P` is **of finite type** when the set `{P t : t ∈ 𝕋ₙ}` of its labeled seeds
is finite. -/
def IsFiniteType (P : RegularTree n → SeedData F m n) : Prop :=
  (Set.range P).Finite

end

/-! ## `2`-finite matrices -/

section

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- A skew-symmetrizable `n × n` integer matrix `B` is **`2`-finite** when
`|b'ᵢⱼ b'ⱼᵢ| ≤ 3` for every matrix `B'` mutation equivalent to `B` and all `i, j`. -/
def IsTwoFinite (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  SkewSymmetrizable B ∧ ∀ B' : Matrix (Fin n) (Fin n) ℤ, MutationEquiv B B' →
    ∀ i j, |B' i j * B' j i| ≤ 3

end

/-! ## Triangulations of a polygon and their quivers -/

section

variable {m : ℕ} [NeZero m]

/-- Circular betweenness `sbtw` on `ZMod m` is decidable (Mathlib provides no such instance). -/
instance instDecidableSbtwZMod (a b c : ZMod m) : Decidable (sbtw a b c) := by
  match m, ‹NeZero m›, a, b, c with
  | (n + 1), _, a, b, c => exact decidable_of_iff _ Fin.sbtw_iff.symm

/-- A **segment** of the convex `m`-gon: a two-element subset of `ZMod m`, presented as an
unordered pair of distinct vertices. -/
def IsSegment (e : Sym2 (ZMod m)) : Prop := ¬e.IsDiag

/-- A segment is a **side** of the `m`-gon when its endpoints are cyclically consecutive,
that is, when it is `s(i, i + 1)` for some vertex `i`. -/
def IsSide (e : Sym2 (ZMod m)) : Prop := ∃ i : ZMod m, e = s(i, i + 1)

/-- A segment is a **diagonal** when it is not a side. -/
def IsDiagonal (e : Sym2 (ZMod m)) : Prop := IsSegment e ∧ ¬IsSide e

/-- Being a side is decidable: the witness `i` ranges over the finite type `ZMod m`. -/
instance instDecidablePredIsSide : DecidablePred (IsSide (m := m)) := fun _ => by
  unfold IsSide; infer_instance

/-- Two segments **cross** when, naming their endpoints suitably, each of the two arcs that
`{a, b}` cuts `ZMod m` into contains one endpoint of `{c, d}`: `sbtw a c b` and `sbtw b d a`. -/
def Cross (e f : Sym2 (ZMod m)) : Prop :=
  ∃ a b c d : ZMod m, e = s(a, b) ∧ f = s(c, d) ∧ sbtw a c b ∧ sbtw b d a

/-- A listing `(a, b, c)` of a three-element subset of `ZMod m` is **clockwise** when,
starting at `a` and increasing the index by one at each step, one meets `b` strictly before
`c`, that is, `sbtw a b c` for the cyclic order on `ZMod m`. -/
abbrev IsClockwise (a b c : ZMod m) : Prop := sbtw a b c

/-- A **triangulation** of the convex `m`-gon: a set of pairwise non-crossing diagonals,
maximal with that property. Maximality says every diagonal outside `T` crosses some element
of `T`. -/
structure IsTriangulation (T : Finset (Sym2 (ZMod m))) : Prop where
  /-- Every element of `T` is a diagonal. -/
  isDiagonal : ∀ e ∈ T, IsDiagonal e
  /-- No two elements of `T` cross. -/
  noncrossing : ∀ e ∈ T, ∀ f ∈ T, ¬Cross e f
  /-- `T` is maximal: any diagonal outside it crosses something in it. -/
  maximal : ∀ e, IsDiagonal e → e ∉ T → ∃ f ∈ T, Cross e f

/-- The **segments of `T`**: its diagonals together with all the sides of the `m`-gon. -/
def segments (T : Finset (Sym2 (ZMod m))) : Finset (Sym2 (ZMod m)) :=
  T ∪ Finset.univ.filter IsSide

/-- A **triangle of `T`**: a three-element subset of `ZMod m` all three of whose pairs are
segments of `T`. -/
def IsTriangle (T : Finset (Sym2 (ZMod m))) (t : Finset (ZMod m)) : Prop :=
  t.card = 3 ∧ ∀ u ∈ t, ∀ v ∈ t, u ≠ v → s(u, v) ∈ segments T

/-- Being a triangle of `T` is decidable: a cardinality and a bounded quantification. -/
instance instDecidablePredIsTriangle (T : Finset (Sym2 (ZMod m))) :
    DecidablePred (IsTriangle T) := fun _ => by unfold IsTriangle; infer_instance

/-- The triangles of `T` that contribute an arrow from `σ` to `σ'`: those admitting a
clockwise listing `(a, b, c)` with `σ = s(a,b)` and `σ' = s(b,c)`. -/
def arrowTriangles (T : Finset (Sym2 (ZMod m))) (σ σ' : Sym2 (ZMod m)) :
    Finset (Finset (ZMod m)) :=
  {t ∈ Finset.univ | IsTriangle T t ∧
    ∃ a b c : ZMod m, IsClockwise a b c ∧ σ = s(a, b) ∧ σ' = s(b, c) ∧ a ∈ t ∧ b ∈ t ∧ c ∈ t}

/-- The **arrow multiplicities of the quiver of `T`**: `a(σ, σ')` counts the triangles of `T`
carrying a clockwise listing that runs along `σ` and then along `σ'`, except that a pair of
sides carries no arrow. -/
def polygonArrows (T : Finset (Sym2 (ZMod m))) (σ σ' : Sym2 (ZMod m)) : ℕ :=
  if IsSide σ ∧ IsSide σ' then 0 else (arrowTriangles T σ σ').card

/-- The vertices of the quiver of `T`: the segments of `T`. -/
def SegmentType (T : Finset (Sym2 (ZMod m))) : Type := {e : Sym2 (ZMod m) // e ∈ segments T}

/-- Segments of `T` have decidable equality, inherited from `Sym2 (ZMod m)`. -/
instance instDecidableEqSegmentType (T : Finset (Sym2 (ZMod m))) : DecidableEq (SegmentType T) :=
  fun _ _ => decidable_of_iff _ Subtype.ext_iff.symm

/-- There are finitely many segments of `T`. -/
instance instFintypeSegmentType (T : Finset (Sym2 (ZMod m))) : Fintype (SegmentType T) :=
  Subtype.fintype _

/-- The **quiver of the triangulation `T`**: its vertices are the segments of `T`, its frozen
vertices the sides of the `m`-gon, and its arrows are `polygonArrows`. -/
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

S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras. Chapters 4–5*,
arXiv:1707.07190: exercises of Chapter 5, which enter
`isFiniteType_iff_exists_isCartanFiniteType` as hypotheses. -/

section

section Flip

variable {m : ℕ} [NeZero m]

/-- The result `(T \ {γ}) ∪ {γ'}` of the flip of `T` at `γ` with replacement `γ'`. -/
def flipTriangulation (T : Finset (Sym2 (ZMod m))) (γ γ' : Sym2 (ZMod m)) :
    Finset (Sym2 (ZMod m)) :=
  insert γ' (T.erase γ)

/-- `γ'` is the **replacement** of `γ` in a flip of the triangulation `T`: `γ ∈ T`, `γ'` is a
diagonal not in `T`, and `(T \ {γ}) ∪ {γ'}` is a triangulation. The passage from `T` to
`flipTriangulation T γ γ'` is then the *flip of `T` at `γ`*. -/
def IsFlipReplacement (T : Finset (Sym2 (ZMod m))) (γ γ' : Sym2 (ZMod m)) : Prop :=
  IsTriangulation T ∧ γ ∈ T ∧ IsDiagonal γ' ∧ γ' ∉ T ∧
    IsTriangulation (flipTriangulation T γ γ')

/-- **A flip is a mutation.** If `γ'` replaces `γ` in a flip of the triangulation `T`, the
bijection from the segments of `T` to those of `(T \ {γ}) ∪ {γ'}` sending `γ` to `γ'` and fixing
every other segment is an isomorphism from `μ_γ(Q(T))` to `Q((T \ {γ}) ∪ {γ'})`. The
mutability of the vertex `γ` of `Q(T)` is the hypothesis `hk`. -/
def PolygonQuiverMutateIsoFlip : Prop :=
  ∀ {m : ℕ} [NeZero m] {T : Finset (Sym2 (ZMod m))} {γ γ' : Sym2 (ZMod m)}
      (h : IsFlipReplacement T γ γ')
      (hk : (⟨γ, Finset.mem_union_left _ h.2.1⟩ : SegmentType T) ∉ (polygonQuiver T).frozen),
    ∃ e : ((polygonQuiver T).mutate hk).Iso (polygonQuiver (flipTriangulation T γ γ')),
      ∀ σ : SegmentType T, (e.equiv σ).1 = if σ.1 = γ then γ' else σ.1

end Flip

universe u

/-- **Orientations of a tree are mutation equivalent.** Any two orientations `Q`, `Q'` of a
finite tree on the same vertex set are joined by a mutation path each of whose mutations is
performed at a source or a sink of the quiver it is applied to. -/
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

open Classical in
/-- The mutable orbit `θ(q)`, `q < nG`, as a finite set of columns. -/
noncomputable def cols (hmn : n ≤ m) (q : Fin nG) : Finset (Fin n) :=
  Finset.univ.filter fun j => Fin.castLE hmn j ∈ θ.orbit (Fin.castLE θ.le q)

end OrbitLabelling

/-- The **increasing sequence** `s_K = (k₁, …, k_s)` of a set `K` of columns,
`k₁ < ⋯ < k_s`. -/
def increasingSeq (K : Finset (Fin n)) : List (Fin n) :=
  K.sort (· ≤ ·)

/-- The **orbit sequence** `θ(ρ)*` of a sequence `ρ = (r₁, …, r_d)` of mutable labels: the
concatenation of `s_{θ(r₁)}, …, s_{θ(r_d)}`. -/
noncomputable def orbitSeq (θ : OrbitLabelling G m n mG nG) (hmn : n ≤ m) (ρ : List (Fin nG)) :
    List (Fin n) :=
  ρ.flatMap fun r => increasingSeq (θ.cols hmn r)

/-- An `m × n` integer matrix `B` is **globally foldable** for an orbit labelling `θ` when it is
`G`-admissible and so is `μ_{θ(ρ)*}(B)` for every finite sequence `ρ` of mutable labels. -/
def IsGloballyFoldable (θ : OrbitLabelling G m n mG nG) (hmn : n ≤ m)
    (B : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  IsGroupAdmissible G hmn B ∧
    ∀ ρ : List (Fin nG), IsGroupAdmissible G hmn (matrixMutationList hmn B (orbitSeq θ hmn ρ))

end

/-! ## Orbit labellings by representatives -/

namespace TypeBC

open Matrix MulAction

universe u

section Reps

variable {G : Type*} [Group G] {N NG : ℕ} [MulAction G (Fin N)]

/-- The **orbit labelling given by representatives**, for an action on `Fin N` with all indices
mutable: `θ(p)` is the orbit of `r p`, where `r` meets every orbit exactly once. -/
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
def cdist (i j : Fin n) : ℕ :=
  ((j : ℕ) + n - i) % n

/-- The **residue** `ū ∈ Fin n` of an integer `u`: its remainder modulo `n`, in `[0, n - 1]`. -/
def vtx [NeZero n] (u : ℤ) : Fin n :=
  ⟨(u % n).toNat, (Int.toNat_lt (Int.emod_nonneg u (Int.natCast_ne_zero.2 (NeZero.ne n)))).2
    (Int.emod_lt_of_pos u (Int.natCast_pos.2 (NeZero.pos n)))⟩

/-- The **sheet** `η(u) = ⌊u / n⌋` of an integer `u`, equal to `(u - ū) / n`. -/
def sheet (n : ℕ) (u : ℤ) : ℤ :=
  u / n

/-- The sheet difference `κ(u, v) = η(v) - η(u)` of two integers `u` and `v`. -/
def kappa (n : ℕ) (u v : ℤ) : ℤ :=
  sheet n v - sheet n u

/-- The **cut indicator** `χ(i, j)`: `1` if `j < i` and `0` otherwise. For `i ≠ j` it
indicates that the run from `i` to `j` passes along the side `{n - 1, 0}`. -/
def cut (i j : Fin n) : ℤ :=
  if j < i then 1 else 0

/-- The **interior vertices** of the run from `i` to `j`: the vertices `i + t` with
`0 < t < d(i, j)`. -/
def interiorVertices [NeZero n] (i j : Fin n) : Finset (Fin n) :=
  (Finset.Ioo 0 (cdist i j)).image fun t : ℕ => vtx ((i : ℤ) + (t : ℤ))

/-- A **tag**: plain (`+`) or notched (`-`). -/
inductive Tag where
  /-- The plain tag `+`. -/
  | plain
  /-- The notched tag `-`. -/
  | notched
  deriving DecidableEq, Repr

/-- The two tags form a finite type. -/
instance : Fintype Tag := derive_fintype% Tag

/-- The other tag `-τ`. -/
def Tag.neg : Tag → Tag
  | plain => notched
  | notched => plain

/-- Negation on tags swaps `+` and `-` (`Tag.neg`). -/
instance Tag.instNeg : Neg Tag :=
  ⟨Tag.neg⟩

/-- A **tagged arc** of the once-punctured `n`-gon: an *ordinary arc* `α(i, j)` with
`2 ≤ d(i, j)` (and `d(i, j) ≤ n - 1`, which always holds), or a *radius* `ρ^τ_i` with tag `τ`
and *position* `i`. -/
inductive TaggedArc (n : ℕ) where
  /-- The ordinary arc `α(i, j)`. -/
  | ordinary (i j : Fin n) (h : 2 ≤ cdist i j)
  /-- The radius `ρ^τ_i`. -/
  | radius (τ : Tag) (i : Fin n)
  deriving DecidableEq, Fintype

/-- The **shadow** `S(α(i, j)) = {β_{i + t} : 0 ≤ t < d(i, j)}` of an ordinary arc, as the set of
indices of its boundary segments. -/
def shadow [NeZero n] (i j : Fin n) : Finset (Fin n) :=
  (Finset.range (cdist i j)).image fun t : ℕ => vtx ((i : ℤ) + (t : ℤ))

/-- The symbols of **segments**: a tagged arc, a boundary segment `β_i`, or the loop `L_i`. -/
inductive DSeg (n : ℕ) where
  /-- A tagged arc. -/
  | arc (γ : TaggedArc n)
  /-- The boundary segment `β_i`. -/
  | boundary (i : Fin n)
  /-- The loop `L_i`. -/
  | loop (i : Fin n)
  deriving DecidableEq

section

variable [NeZero n]

/-- The ordinary arc `α(ū, v̄)` of two integers, when `2 ≤ d(ū, v̄)`; the junk value `ρ^+_ū`
otherwise. -/
def ordArc (u v : ℤ) : TaggedArc n :=
  if h : 2 ≤ cdist (vtx u : Fin n) (vtx v) then .ordinary (vtx u) (vtx v) h
  else .radius .plain (vtx u)

/-- The **segment** `s(u, v)` of integers `u < v ≤ u + n`: `β_ū` if `v = u + 1`, the loop `L_ū`
if `v = u + n`, and the ordinary arc `α(ū, v̄)` otherwise. Total, with junk values outside
`u < v ≤ u + n`. -/
def seg (u v : ℤ) : DSeg n :=
  if v - u = 1 then .boundary (vtx u)
  else if v - u = n then .loop (vtx u)
  else .arc (ordArc u v)

namespace TaggedArc

/-- Two tagged arcs are **compatible** when (a) both are ordinary and their shadows are nested
or disjoint, (b) one is an ordinary arc `α(i, j)` and the other a radius whose position is not an
interior vertex of the run from `i` to `j`, or (c) both are radii with the same position or the
same tag. -/
def Compatible : TaggedArc n → TaggedArc n → Prop
  | ordinary i j _, ordinary k l _ =>
      shadow i j ⊆ shadow k l ∨ shadow k l ⊆ shadow i j ∨ Disjoint (shadow i j) (shadow k l)
  | ordinary i j _, radius _ a => a ∉ interiorVertices i j
  | radius _ a, ordinary i j _ => a ∉ interiorVertices i j
  | radius τ a, radius σ b => a = b ∨ τ = σ

end TaggedArc

/-- A **tagged triangulation**: a set `T` of pairwise compatible tagged arcs that contains every
tagged arc compatible with all of its elements, that is, a maximal pairwise compatible set. -/
def IsTaggedTriangulation (T : Finset (TaggedArc n)) : Prop :=
  (∀ γ ∈ T, ∀ δ ∈ T, γ.Compatible δ) ∧ ∀ γ, (∀ δ ∈ T, γ.Compatible δ) → γ ∈ T

end

end TypeD

/-! ## Triangulations of a run of integers -/

namespace TypeD

/-- A **chord** of the run `[u, v]`: a pair `(x, y)` of integers with `u ≤ x < y ≤ v`,
`y - x ≥ 2` and `(x, y) ≠ (u, v)`. -/
def IsRunChord (u v : ℤ) (c : ℤ × ℤ) : Prop :=
  u ≤ c.1 ∧ c.1 < c.2 ∧ c.2 ≤ v ∧ 2 ≤ c.2 - c.1 ∧ c ≠ (u, v)

/-- Being a chord is decidable. -/
instance instDecidablePredIsRunChord (u v : ℤ) : DecidablePred (IsRunChord u v) := fun _ => by
  unfold IsRunChord; infer_instance

/-- A **segment** of a triangulation `T` of `[u, v]`: a chord in `T`, a side `(x, x + 1)` with
`u ≤ x < v`, or the outer side `(u, v)`. -/
def IsRunSegment (u v : ℤ) (T : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : Prop :=
  c ∈ T ∨ (u ≤ c.1 ∧ c.2 = c.1 + 1 ∧ c.2 ≤ v) ∨ c = (u, v)

/-- Being a segment is decidable. -/
instance instDecidablePredIsRunSegment (u v : ℤ) (T : Finset (ℤ × ℤ)) :
    DecidablePred (IsRunSegment u v T) := fun _ => by
  unfold IsRunSegment; infer_instance

/-- A **triangle** `(x, y, z)` of `T`: integers `x < y < z` such that `(x, y)`, `(y, z)` and
`(x, z)` are segments of `T`. Its base is `(x, z)`, its apex `y`, its first short side `(x, y)`
and its second short side `(y, z)`. -/
def IsRunTriangle (u v : ℤ) (T : Finset (ℤ × ℤ)) (x y z : ℤ) : Prop :=
  x < y ∧ y < z ∧ IsRunSegment u v T (x, y) ∧ IsRunSegment u v T (y, z) ∧
    IsRunSegment u v T (x, z)

/-- Being a triangle is decidable. -/
instance instDecidableIsRunTriangle (u v : ℤ) (T : Finset (ℤ × ℤ)) (x y z : ℤ) :
    Decidable (IsRunTriangle u v T x y z) := by
  unfold IsRunTriangle; infer_instance

/-- The integers `u, u + 1, …, v` as a finset, the image of `Finset.range` under `t ↦ u + t`; it
equals `Finset.Icc u v`. -/
def intRange (u v : ℤ) : Finset ℤ :=
  (Finset.range (v + 1 - u).toNat).image fun t : ℕ => u + t

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

/-- The **gap** `g_R(a)`: the least `t ∈ [1, n]` with `a + t ∈ R` (mod `n`), and `n` if there is
none. For `a ∈ R` with `R = {r₁ < ⋯ < r_k}` and `a = r_s` it is `r_{s+1} - r_s`, where
`r_{k+1} = r₁ + n`. -/
def gap (R : Finset (Fin n)) (a : Fin n) : ℕ :=
  if h : (gapCandidates R a).Nonempty then (gapCandidates R a).min' h + 1 else n

/-- The **successor** `a⁺ = a + g_R(a)` (mod `n`). -/
def succ (R : Finset (Fin n)) (a : Fin n) : Fin n :=
  vtx ((a : ℤ) + (gap R a : ℤ))

/-- The **radius set** of `T`: the positions of the radii in `T`. -/
def radiusSet (T : Finset (TaggedArc n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => TaggedArc.radius .plain i ∈ T ∨ TaggedArc.radius .notched i ∈ T

/-- The set `T_R(a)` of chords `c` of the sector run `[a, a + g_R(a)]` with `s(c) ∈ T`. -/
def sectorChords (T : Finset (TaggedArc n)) (R : Finset (Fin n)) (a : Fin n) :
    Finset (ℤ × ℤ) :=
  (intRange a (a + gap R a) ×ˢ intRange a (a + gap R a)).filter fun c =>
    IsRunChord a (a + gap R a) c ∧ ordArc c.1 c.2 ∈ T

/-- The **flip** `(T \ {γ}) ∪ {γ'}` of `T` at `γ` with replacement `γ'`. -/
def dFlip (T : Finset (TaggedArc n)) (γ γ' : TaggedArc n) : Finset (TaggedArc n) :=
  insert γ' (T.erase γ)

/-- `γ'` is the **replacement** of `γ` in a flip of the tagged triangulation `T`: `γ ∈ T`,
`γ' ∉ T`, and `(T \ {γ}) ∪ {γ'}` is a tagged triangulation. The passage from `T` to
`dFlip T γ γ'` is then the *flip of `T` at `γ`*; the replacement exists and is unique. -/
def IsDFlipReplacement (T : Finset (TaggedArc n)) (γ γ' : TaggedArc n) : Prop :=
  IsTaggedTriangulation T ∧ γ ∈ T ∧ γ' ∉ T ∧ IsTaggedTriangulation (dFlip T γ γ')

end TypeD

/-! ## The exchange matrix of a tagged triangulation -/

namespace TypeD

variable {n : ℕ} [NeZero n]

/-- The symbols indexing the rows of `B̃•(T)`: tagged arcs, boundary segments `β_i`, and `λ_τ`
(`λ_+ = λ`, `λ_- = λ̄`). -/
inductive DRow (n : ℕ) where
  /-- The row of a tagged arc. -/
  | arc (γ : TaggedArc n)
  /-- The row of the boundary segment `β_i`. -/
  | boundary (i : Fin n)
  /-- The row `λ_τ`. -/
  | lam (τ : Tag)
  deriving DecidableEq, Fintype

/-- The set `E(s)` of rows of a segment `s`: `{s}` for a tagged arc or a boundary segment, and
`{ρ^+_a, ρ^-_a}` for the loop `L_a`. -/
def DSeg.rows : DSeg n → Finset (DRow n)
  | arc γ => {.arc γ}
  | boundary i => {.boundary i}
  | loop a => {.arc (.radius .plain a), .arc (.radius .notched a)}

/-- `Ar_{s,s'}(δ, ε) = [δ ∈ E(s)][ε ∈ E(s')] - [ε ∈ E(s)][δ ∈ E(s')]`: an arrow `s → s'`. -/
def arrowMatrix (s s' : DSeg n) : Matrix (DRow n) (TaggedArc n) ℤ :=
  Matrix.of fun δ ε =>
    (if δ ∈ s.rows ∧ DRow.arc ε ∈ s'.rows then 1 else 0) -
      (if DRow.arc ε ∈ s.rows ∧ δ ∈ s'.rows then 1 else 0)

/-- `U_{λ_τ,s}(δ, ε) = [δ = λ_τ][ε ∈ E(s)]`. -/
def lamMatrix (τ : Tag) (s : DSeg n) : Matrix (DRow n) (TaggedArc n) ℤ :=
  Matrix.of fun δ ε => if δ = .lam τ ∧ DRow.arc ε ∈ s.rows then 1 else 0

/-- `Cyc(s₁, s₂, s₃) = Ar_{s₁,s₂} + Ar_{s₂,s₃} + Ar_{s₃,s₁}`: the oriented `3`-cycle
`s₁ → s₂ → s₃ → s₁`. -/
def cycMatrix (s₁ s₂ s₃ : DSeg n) : Matrix (DRow n) (TaggedArc n) ℤ :=
  arrowMatrix s₁ s₂ + arrowMatrix s₂ s₃ + arrowMatrix s₃ s₁

/-- The **outer triangles** of `T`: the pairs `(a, (x, y, z))` with `a` in the radius set `R` of
`T` and `(x, y, z)` a triangle of `T_R(a)` in the sector run `[a, a + g_R(a)]`. Their *sides* are
the segments `s(x, y)`, `s(y, z)`, `s(x, z)`; the last is the loop `L_a` exactly when `T` is of
digon kind and `(x, z) = (a, a + n)`. -/
def outerTriangles (T : Finset (TaggedArc n)) : Finset (Fin n × ℤ × ℤ × ℤ) :=
  (radiusSet T).biUnion fun a =>
    (runTriangles a (a + gap (radiusSet T) a) (sectorChords T (radiusSet T) a)).image
      fun t => (a, t)

/-- `T` has the radii of kind `P_τ`: at least two positions and no radius of tag `-τ`. On tagged
triangulations this is being of kind `P_τ`. -/
def IsPunctureKind (T : Finset (TaggedArc n)) (τ : Tag) : Prop :=
  2 ≤ (radiusSet T).card ∧ ∀ i, TaggedArc.radius (-τ) i ∉ T

/-- Having the radii of kind `P_τ` is decidable. -/
instance instDecidableIsPunctureKind (T : Finset (TaggedArc n)) (τ : Tag) :
    Decidable (IsPunctureKind T τ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The **puncture triangles** of `T` of kind `P_τ`: the pairs `(a, a⁺)`, `a ∈ R`, recorded as
`(τ, a)`; the *outer side* of `(a, a⁺)` is `s(a, a + g_R(a))`, the outer arc `α_R(a)` or `β_a`
when `g_R(a) = 1`. -/
def punctureTriangles (T : Finset (TaggedArc n)) : Finset (Tag × Fin n) :=
  (Finset.univ ×ˢ radiusSet T).filter fun p => IsPunctureKind T p.1

/-- The contribution of the outer triangle `(a, (x, y, z))`, with `k = κ(y, z)`:
`Cyc(s(x,y), s(y,z), s(x,z)) + k (U_{λ,s(y,z)} + U_{λ̄,s(y,z)} - U_{λ,s(x,z)} - U_{λ̄,s(x,z)})`. -/
def outerContribution (p : Fin n × ℤ × ℤ × ℤ) : Matrix (DRow n) (TaggedArc n) ℤ :=
  cycMatrix (seg p.2.1 p.2.2.1) (seg p.2.2.1 p.2.2.2) (seg p.2.1 p.2.2.2) +
    kappa n p.2.2.1 p.2.2.2 •
      (lamMatrix .plain (seg p.2.2.1 p.2.2.2) + lamMatrix .notched (seg p.2.2.1 p.2.2.2) -
        lamMatrix .plain (seg p.2.1 p.2.2.2) - lamMatrix .notched (seg p.2.1 p.2.2.2))

/-- The contribution of the puncture triangle `(a, a⁺)` of kind `P_τ`, with outer side `s` and
`k = χ(a, a⁺)`: `Cyc(s, ρ^τ_{a⁺}, ρ^τ_a) + k (U_{λ_τ,s} - U_{λ_τ,ρ^τ_{a⁺}} + U_{λ_{-τ},ρ^τ_a})`. -/
def punctureContribution (T : Finset (TaggedArc n)) (τ : Tag) (a : Fin n) :
    Matrix (DRow n) (TaggedArc n) ℤ :=
  cycMatrix (seg (a : ℤ) (a + gap (radiusSet T) a)) (.arc (.radius τ (succ (radiusSet T) a)))
      (.arc (.radius τ a)) +
    cut a (succ (radiusSet T) a) •
      (lamMatrix τ (seg (a : ℤ) (a + gap (radiusSet T) a)) -
        lamMatrix τ (.arc (.radius τ (succ (radiusSet T) a))) +
        lamMatrix (-τ) (.arc (.radius τ a)))

/-- The contribution `U_{λ̄,ρ^+_a} + U_{λ,ρ^-_a}` of a position `a` carrying both radii (the
doubled position of the digon kind), and `0` otherwise. -/
def digonContribution (T : Finset (TaggedArc n)) (a : Fin n) : Matrix (DRow n) (TaggedArc n) ℤ :=
  if TaggedArc.radius .plain a ∈ T ∧ TaggedArc.radius .notched a ∈ T then
    lamMatrix .notched (.arc (.radius .plain a)) + lamMatrix .plain (.arc (.radius .notched a))
  else 0

/-- The **matrix `B̃•(T)`** of a tagged triangulation `T`: the sum of the contributions of its
outer triangles, of its puncture triangles (kind `P_τ`), and of its doubled position (digon
kind). Rows are indexed by `DRow n`, columns by tagged arcs; the entries outside
`ℛ(T) × T` vanish. -/
def dMatrix (T : Finset (TaggedArc n)) : Matrix (DRow n) (TaggedArc n) ℤ :=
  (∑ p ∈ outerTriangles T, outerContribution p) +
    (∑ p ∈ punctureTriangles T, punctureContribution T p.1 p.2) +
    ∑ a, digonContribution T a

/-- A **labelling** of `T`: a bijection `ℓ : [1, n] → T`, here an injective map
`Fin n → TaggedArc n` with range `T`. -/
def IsLabelling (T : Finset (TaggedArc n)) (ℓ : Fin n → TaggedArc n) : Prop :=
  Function.Injective ℓ ∧ Set.range ℓ = (T : Set (TaggedArc n))

/-- The **extended labelling** `ℓ̂ : [1, 2n + 2] → ℛ(T)`: `ℓ̂(i) = ℓ(i)` for `i < n`,
`ℓ̂(n + i) = β_i`, `ℓ̂(2n) = λ` and `ℓ̂(2n + 1) = λ̄` (indices from `0`). -/
def extLabel (ℓ : Fin n → TaggedArc n) (i : Fin (2 * n + 2)) : DRow n :=
  if h : (i : ℕ) < n then .arc (ℓ ⟨i, h⟩)
  else if h' : (i : ℕ) < 2 * n then
    .boundary ⟨i - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) (two_mul n ▸ h')⟩
  else if (i : ℕ) = 2 * n then .lam .plain
  else .lam .notched

/-- The **labelled matrix** `B̃•(T, ℓ)`: the `(2n + 2) × n` matrix with entries
`b_{ℓ̂(i) ℓ(j)}`. -/
def labelledMatrix (T : Finset (TaggedArc n)) (ℓ : Fin n → TaggedArc n) :
    Matrix (Fin (2 * n + 2)) (Fin n) ℤ :=
  Matrix.of fun i j => dMatrix T (extLabel ℓ i) (ℓ j)

/-- The **flipped labelling** `ℓ'` of the flip at `ℓ(k)` with replacement `γ'`: `ℓ` with
`ℓ'(k) = γ'`. -/
def flipLabelling (ℓ : Fin n → TaggedArc n) (k : Fin n) (γ' : TaggedArc n) :
    Fin n → TaggedArc n :=
  Function.update ℓ k γ'

end TypeD

/-! ## Flips of tagged triangulations as hypothesis

S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras. Chapters 4–5*,
arXiv:1707.07190, Section 5.4: an exercise, which enters
`isFiniteType_iff_exists_isCartanFiniteType` as a hypothesis. -/

namespace TypeD

variable {n : ℕ} [NeZero n]

/-- **A flip is a mutation of `B̃•`.** Let `T` be a tagged triangulation with labelling `ℓ`, let
`k : Fin n`, and let `γ'` be the replacement of `ℓ k`. Then the labelled matrix of the flip with
the flipped labelling is the mutation in direction `k` of the labelled matrix of `T`:
`B̃•(T', ℓ') = μ_k(B̃•(T, ℓ))`, the rows `λ, λ̄` included. -/
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

/-- The involution `g` of `Fin 6` exchanging the two long arms `2 — 1 — 0` and `2 — 3 — 4` of the
`E₆` tree and fixing `2` and `5`. -/
def e₆Involution : Fin 6 → Fin 6 :=
  ![4, 3, 2, 1, 0, 5]

/-- The group `ℤ/2ℤ`, written multiplicatively, acting on `Fin 6` through the involution `g`
(`ClusterAlgebras.TypeFG.instMulActionE₆FoldGroup`). -/
def E₆FoldGroup : Type :=
  Multiplicative (ZMod 2)

/-- `E₆FoldGroup` is the group `Multiplicative (ZMod 2)`. -/
instance instGroupE₆FoldGroup : Group E₆FoldGroup :=
  inferInstanceAs (Group (Multiplicative (ZMod 2)))

/-- `E₆FoldGroup` is finite, with two elements. -/
instance instFintypeE₆FoldGroup : Fintype E₆FoldGroup :=
  inferInstanceAs (Fintype (Multiplicative (ZMod 2)))

/-- The action of `ℤ/2ℤ` on `Fin 6`: the identity fixes every index, the generator acts by the
involution `g`. All indices are mutable (`m = n = 6`). -/
instance instMulActionE₆FoldGroup : MulAction E₆FoldGroup (Fin 6) where
  smul g i := if Multiplicative.toAdd (g : Multiplicative (ZMod 2)) = 0 then i else e₆Involution i
  one_smul := by decide
  mul_smul := by decide

/-- Membership in an orbit of `E₆FoldGroup` is decidable. -/
instance instDecidableMemOrbitE₆FoldGroup (i i' : Fin 6) :
    Decidable (i' ∈ orbit E₆FoldGroup i) :=
  decidable_of_iff (i' = i ∨ i' = e₆Involution i) (by
    rw [mem_orbit_iff]
    revert i i'
    decide)

/-- The orbit labelling `θ` of the `E₆` folding: `θ(0) = {5}`, `θ(1) = {2}`, `θ(2) = {1, 3}`,
`θ(3) = {0, 4}`, all four orbits being mutable. -/
noncomputable def e₆OrbitLabelling : OrbitLabelling E₆FoldGroup 6 6 4 4 :=
  TypeBC.orbitLabellingOfReps ![5, 2, 1, 0] (by decide) (by decide)

/-- **The `E₆` lifts.** For `ε ∈ {1, -1}³`, the `6 × 6` integer matrix `Q_ε` with
`q₅₂ = ε₁`, `q₂₅ = -ε₁`, `q₂₁ = q₂₃ = ε₂`, `q₁₂ = q₃₂ = -ε₂`, `q₁₀ = q₃₄ = ε₃`,
`q₀₁ = q₄₃ = -ε₃` and all other entries `0`, indices running over `Fin 6`. -/
def matrixE₆Lift (ε : Fin 3 → ℤˣ) : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, -(ε 2 : ℤ), 0, 0, 0, 0;
    (ε 2 : ℤ), 0, -(ε 1 : ℤ), 0, 0, 0;
    0, (ε 1 : ℤ), 0, (ε 1 : ℤ), 0, -(ε 0 : ℤ);
    0, 0, -(ε 1 : ℤ), 0, (ε 2 : ℤ), 0;
    0, 0, 0, -(ε 2 : ℤ), 0, 0;
    0, 0, (ε 0 : ℤ), 0, 0, 0]

end TypeFG

end

/-! ## Foldability of the `E₆` lifts as hypothesis

S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras. Chapters 4–5*,
arXiv:1707.07190, Chapter 5: an exercise, which enters
`isFiniteType_iff_exists_isCartanFiniteType` as a hypothesis. -/

namespace TypeFG

/-- For every `ε ∈ {1, -1}³`, the matrix `Q_ε` is globally foldable for the action of `ℤ/2ℤ`
on `Fin 6` and the orbit labelling `θ` of the `E₆` folding. -/
def IsGloballyFoldableMatrixE₆Lift : Prop :=
  ∀ (ε : Fin 3 → ℤˣ),
    IsGloballyFoldable e₆OrbitLabelling le_rfl (matrixE₆Lift ε)

end TypeFG

/-! ## Diagrams, cycles and shapes -/

section

open Matrix

variable {n m N : ℕ}

/-- The **weight** of the indices `i, j` of an integer matrix `B`: `w_B(i, j) = |bᵢⱼ bⱼᵢ|`.
There is an *arrow* `i → j` in `B` when `0 < bᵢⱼ`. -/
def diagramWeight (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℕ :=
  (B i j * B j i).natAbs

/-- The **graph** `G_B` of `B`: the finite simple graph on `[1, n]` in which `i ≠ j` are
*adjacent* when their weight is positive. -/
def diagramGraph (B : Matrix (Fin n) (Fin n) ℤ) : FiniteSimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ 0 < diagramWeight B i j
  symm := ⟨fun i j h => ⟨h.1.symm, by
    have h2 := h.2
    unfold diagramWeight at h2 ⊢
    rwa [mul_comm]⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- A sequence `(v₁, …, v_m)` of pairwise distinct indices, `m ≥ 1`, is an **induced path**
of `B` when, for `p ≠ q`, the indices `v_p` and `v_q` are adjacent exactly when
`|p - q| = 1`. Its weights are the `w_B(v_p, v_{p+1})`. -/
def IsInducedPath (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin m → Fin n) : Prop :=
  1 ≤ m ∧ Function.Injective v ∧ ∀ p q : Fin m, p ≠ q →
    ((diagramGraph B).Adj (v p) (v q) ↔ (p : ℕ) + 1 = q ∨ (q : ℕ) + 1 = p)

/-- A sequence `(v₁, …, v_m)` of pairwise distinct indices, `m ≥ 3`, is a **chordless cycle**
of `B` when, reading indices modulo `m`, the indices `v_p` and `v_q` (`p ≠ q`) are adjacent
exactly when `p - q ≡ ±1`. Here `finRotate m` is `p ↦ p + 1` modulo `m`. -/
def IsChordlessCycle (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin m → Fin n) : Prop :=
  3 ≤ m ∧ Function.Injective v ∧ ∀ p q : Fin m, p ≠ q →
    ((diagramGraph B).Adj (v p) (v q) ↔ q = finRotate m p ∨ p = finRotate m q)

/-- The **weights** `w_p = w_B(v_p, v_{p+1})`, `p ∈ [1, m]`, of a cycle `(v₁, …, v_m)`, indices
read modulo `m`. -/
def cycleWeights (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin m → Fin n) : Fin m → ℕ :=
  fun p => diagramWeight B (v p) (v (finRotate m p))

/-- A cycle `(v₁, …, v_m)` is **cyclically oriented** when either `v_p → v_{p+1}` for all `p`,
or `v_{p+1} → v_p` for all `p`. -/
def IsCyclicallyOriented (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin m → Fin n) : Prop :=
  (∀ p, 0 < B (v p) (v (finRotate m p))) ∨ ∀ p, 0 < B (v (finRotate m p)) (v p)

/-- The weight of the pair at the positions `p ≠ q` of a model with weights `f`, the model
recording `f p q` for `p < q` only. -/
def orderedModel (f : ℕ → ℕ → ℕ) {M : ℕ} (p q : Fin M) : ℕ :=
  if (p : ℕ) < q then f p q else f q p

/-- A weighted graph `ω` on `[1, N]` **has the model `f` on `M` positions** when `[1, N]` has an
enumeration `e : [0, M) ≃ [1, N]` with `ω(e(p), e(q)) = f(p, q)` for all positions `p < q`,
that is, `ω` has the weights `f` on the listed pairs and `0` on all other pairs of distinct
indices. -/
def IsShapeOf (ω : Fin N → Fin N → ℕ) (M : ℕ) (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ e : Fin M ≃ Fin N, ∀ p q : Fin M, p ≠ q → ω (e p) (e q) = orderedModel f p q

/-- The model of `T_{a,b,c}`: the positions are `o = 0`, `x_t = t` (`t ∈ [1, a]`),
`y_t = a + t` (`t ∈ [1, b]`), `z_t = a + b + t` (`t ∈ [1, c]`), and the weight is `1` on the
pairs `{o, x₁}`, `{x_t, x_{t+1}}`, `{o, y₁}`, `{y_t, y_{t+1}}`, `{o, z₁}`, `{z_t, z_{t+1}}`. -/
def tShapeModel (a b c : ℕ) (p q : ℕ) : ℕ :=
  if (p + 1 = q ∧ q ≤ a) ∨
      (p = 0 ∧ q = a + 1 ∧ 1 ≤ b) ∨ (a + 1 ≤ p ∧ p + 1 = q ∧ q ≤ a + b) ∨
      (p = 0 ∧ q = a + b + 1 ∧ 1 ≤ c) ∨ (a + b + 1 ≤ p ∧ p + 1 = q ∧ q ≤ a + b + c)
  then 1 else 0

/-- `ω` is **of shape `T_{a,b,c}`** (`N = a + b + c + 1`): `[1, N]` has an enumeration
`o, x₁, …, x_a, y₁, …, y_b, z₁, …, z_c` with `ω = 1` on `{o, x₁}`, `{xᵢ, xᵢ₊₁}`, `{o, y₁}`,
`{yᵢ, yᵢ₊₁}`, `{o, z₁}`, `{zᵢ, zᵢ₊₁}` (pairs involving an empty arm omitted) and `ω = 0` on all
other pairs of distinct indices. -/
def IsTShape (ω : Fin N → Fin N → ℕ) (a b c : ℕ) : Prop :=
  IsShapeOf ω (a + b + c + 1) (tShapeModel a b c)

/-- The model of the crown `S^s_{p,q,r}`: positions `c_i = i - 1` (`i ∈ [1, s + 3]`),
`x_t = s + 2 + t` (`t ∈ [1, p - 1]`), `y_t = s + 2 + (p - 1) + t` (`t ∈ [1, q - 1]`),
`z_t = s + 2 + (p - 1) + (q - 1) + t` (`t ∈ [1, r - 1]`); weight `1` on the cycle pairs
`{cᵢ, cᵢ₊₁}` (indices modulo `s + 3`), on `{c₁, x₁}`, `{xᵢ, xᵢ₊₁}`, `{c₂, y₁}`, `{yᵢ, yᵢ₊₁}`,
`{c₃, z₁}`, `{zᵢ, zᵢ₊₁}`. -/
def crownModel (s p q r : ℕ) (i j : ℕ) : ℕ :=
  let X := s + 3
  let Y := s + 3 + (p - 1)
  let Z := s + 3 + (p - 1) + (q - 1)
  if (i + 1 = j ∧ j ≤ s + 2) ∨ (i = 0 ∧ j = s + 2) ∨
      (i = 0 ∧ j = X ∧ 2 ≤ p) ∨ (X ≤ i ∧ i + 1 = j ∧ j < Y) ∨
      (i = 1 ∧ j = Y ∧ 2 ≤ q) ∨ (Y ≤ i ∧ i + 1 = j ∧ j < Z) ∨
      (i = 2 ∧ j = Z ∧ 2 ≤ r) ∨ (Z ≤ i ∧ i + 1 = j ∧ j < Z + (r - 1))
  then 1 else 0

/-- An `N × N` matrix `B` is **of crown shape `S^s_{p,q,r}`** (`s ≥ 0`, `p, q, r ≥ 1`,
`N = p + q + r + s`): `[1, N]` has an enumeration `c₁, …, c_{s+3}, x₁, …, x_{p-1}, y₁, …,
y_{q-1}, z₁, …, z_{r-1}` (the positions of `crownModel`) with `cᵢ → cᵢ₊₁` for all `i` (indices
modulo `s + 3`), `w_B = 1` on the pairs of `crownModel` and `w_B = 0` on all other pairs of
distinct indices. The arrows on the branch pairs are arbitrary. -/
def IsCrownShape (B : Matrix (Fin N) (Fin N) ℤ) (s p q r : ℕ) : Prop :=
  1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ ∃ e : Fin (p + q + r + s) ≃ Fin N,
    (∀ i j : Fin (p + q + r + s), i ≠ j →
      diagramWeight B (e i) (e j) = orderedModel (crownModel s p q r) i j) ∧
    ∀ i j : Fin (p + q + r + s),
      ((i : ℕ) + 1 = j ∧ (j : ℕ) ≤ s + 2) ∨ ((i : ℕ) = s + 2 ∧ (j : ℕ) = 0) →
        0 < B (e i) (e j)

/-- The set `L_m` of weight sequences of `2`-finite chordless `m`-cycles: the constant
sequence `(1, …, 1)`, together with the three cyclic rotations of `(2, 2, 1)` if `m = 3`, and
with `(2, 1, 2, 1)` and `(1, 2, 1, 2)` if `m = 4`. -/
def IsAdmissibleCycleWeights (w : Fin m → ℕ) : Prop :=
  (∀ p, w p = 1) ∨
    (∃ h : m = 3, w ∘ Fin.cast h.symm ∈ ({![2, 2, 1], ![2, 1, 2], ![1, 2, 2]} : Set (Fin 3 → ℕ))) ∨
    ∃ h : m = 4, w ∘ Fin.cast h.symm ∈ ({![2, 1, 2, 1], ![1, 2, 1, 2]} : Set (Fin 4 → ℕ))

end

/-! ## Exercises on `2`-finite diagrams as hypotheses

S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras. Chapters 4–5*,
arXiv:1707.07190, Section 5.10: three exercises, which enter
`isFiniteType_iff_exists_isCartanFiniteType` as hypotheses. -/

section

/-- **The crown `S^s_{p,q,r}` is mutation equivalent to the tree `T_{p+r-1,q,s}`.** If the
skew-symmetrizable `N × N` integer matrix `B` is of crown shape `S^s_{p,q,r}`, then some
mutation `μ_t(B)` is of shape `T_{p+r-1,q,s}`.

This is an exercise of [FWZ, Section 5.10]. -/
def ExistsIsTShapeMatrixMutationListOfIsCrownShape : Prop :=
  ∀ {N : ℕ} {B : Matrix (Fin N) (Fin N) ℤ} (_ : SkewSymmetrizable B) {s p q r : ℕ}
      (_ : IsCrownShape B s p q r),
    ∃ t : List (Fin N), IsTShape (diagramWeight (matrixMutationList le_rfl B t)) (p + r - 1) q s

/-- **A chordless cycle of a `2`-finite cycle diagram is cyclically oriented, with weights in
`L_m`.** If `m ≥ 3`, `B` is a skew-symmetrizable `m × m` integer matrix, and the enumeration
`(v₁, …, v_m)` of `[1, m]` is a chordless cycle of `B`, then `B` `2`-finite implies that the
cycle is cyclically oriented and that its weights `(w₁, …, w_m)` lie in `L_m`.

This is part (a) of an exercise of [FWZ, Section 5.10]. -/
def IsChordlessCycle.IsCyclicallyOrientedOfIsTwoFinite : Prop :=
  ∀ {m : ℕ} {B : Matrix (Fin m) (Fin m) ℤ} {v : Fin m ≃ Fin m} (_ : IsChordlessCycle B v)
      (_ : IsTwoFinite B),
    IsCyclicallyOriented B v ∧ IsAdmissibleCycleWeights (cycleWeights B v)

/-- **The square with weights `(2, 1, 2, 1)` mutates to a path of type `F₄`.** If
`(v₁, v₂, v₃, v₄)` is an enumeration of `[1, 4]` which is a chordless cycle of the
skew-symmetrizable `4 × 4` integer matrix `B`, with `v_p → v_{p+1}` for all `p` and weights
`(2, 1, 2, 1)`, then `(v₃, v₂, v₁, v₄)` is an induced path of `μ_{(v₁, v₂, v₁)}(B)` with weights
`(1, 2, 1)`. -/
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

/-- **Quiver mutation is matrix mutation**. Mutating a quiver and then taking its extended exchange
matrix agrees with taking the matrix and then mutating it. -/
theorem extExchangeMatrix_mutate_eq_matrixMutation {V : Type*} [Fintype V] [DecidableEq V]
    {m n : ℕ} (Q : Quiver V)
    (L : Labelling Q m n) (k : Fin n) (hk : L.equiv (Fin.castLE L.le k) ∉ Q.frozen) :
    extExchangeMatrix (Q.mutate hk) (L.mutate hk)
      = matrixMutation L.le (extExchangeMatrix Q L) k :=
  sorry

/-- **Mutation preserves the determinant**, when the mutated diagonal entry vanishes. -/
theorem det_matrixMutation_eq {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {n : ℕ} (hnn : n ≤ n) (B : Matrix (Fin n) (Fin n) R) (k : Fin n) (hk : B k k = 0) :
    (matrixMutation hnn B k).det = B.det :=
  sorry

/-- **Mutation preserves the rank**, when the mutated diagonal entry vanishes. -/
theorem rank_matrixMutation_eq {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {m n : ℕ} (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n)
    (hk : B (Fin.castLE hmn k) k = 0) :
    (matrixMutation hmn B k).rank = B.rank :=
  sorry

/-- **Mutation preserves the greatest common divisor of the entries**, granted that mutating twice
at `k` returns `B`. FWZ leave that involutivity as an exercise, so it is a hypothesis here. -/
theorem gcd_matrixMutation_eq_of_involutive {m n : ℕ} (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ)
    (k : Fin n)
    (hinv : matrixMutation hmn (matrixMutation hmn B k) k = B) :
    (Finset.univ.gcd fun p : Fin m × Fin n => matrixMutation hmn B k p.1 p.2) =
      Finset.univ.gcd fun p : Fin m × Fin n => B p.1 p.2 :=
  sorry

/-- **Skew-symmetrizing vectors are unique up to a scalar**. For a matrix with connected diagram,
the ratio of two skew-symmetrizing vectors does not depend on the index. -/
theorem div_eq_div_of_isSkewSymmetrizingVector {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {d d' : Fin n → ℤ} (hΓ : (diagram B).Connected) (hd : IsSkewSymmetrizingVector B d)
    (hd' : IsSkewSymmetrizingVector B d') (i j : Fin n) :
    (d i : ℚ) / (d' i : ℚ) = (d j : ℚ) / (d' j : ℚ) :=
  sorry

/-- **The Markov quiver is self-similar**. Its mutation at each vertex is isomorphic to it. -/
theorem nonempty_iso_markovQuiver_mutate {k : Fin 3} (hk : k ∉ markovQuiver.frozen) :
    Nonempty ((markovQuiver.mutate hk).Iso markovQuiver) :=
  sorry

/-- **The arrows of a wiring diagram form a quiver**. No chamber carries an arrow to itself, no two
chambers carry arrows in both directions, and no arrow joins two unbounded chambers: the three
conditions `Quiver` asks of its arrow function. -/
theorem isArrowSystem_and_twoCycleFree_wiringArrows {n : ℕ} (D : WiringDiagram n) :
    IsArrowSystem D.wiringArrows ∧ TwoCycleFree D.wiringArrows ∧
      ∀ c c' : D.Chamber, ¬c.Bounded → ¬c'.Bounded → D.wiringArrows c c' = 0 :=
  sorry

/-- **A braid move is a mutation**. For wiring diagrams `D` and `D'` related by a braid move with
site `Y` and replacement `Z`, there is exactly one bijection of the chambers sending `Y` to `Z` and
preserving the chamber set of every other chamber, and that bijection is an isomorphism from
`μ_Y(Q(D))` to `Q(D')`. The two quivers are given by their arrow counts and frozen sets;
`isArrowSystem_and_twoCycleFree_wiringArrows` says such quivers exist. -/
theorem existsUnique_iso_mutate_of_braidMove {n : ℕ} (D D' : WiringDiagram n) (p : ℕ)
    (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p)
    (hD' : D'.word = spliceWord D.word p [D.levelAt (p + 1), D.levelAt p, D.levelAt (p + 1)])
    (Q : Quiver D.Chamber) (hQa : Q.arrows = D.wiringArrows)
    (hQf : ∀ c : D.Chamber, c ∈ Q.frozen ↔ ¬c.Bounded)
    (Q' : Quiver D'.Chamber) (hQ'a : Q'.arrows = D'.wiringArrows)
    (hQ'f : ∀ c : D'.Chamber, c ∈ Q'.frozen ↔ ¬c.Bounded)
    (Y : D.Chamber) (hYgap : Y.gap = D.levelAt p)
    (hYidx : Y.idx = D.countUpTo (D.levelAt p) (p + 1)) (hY : Y ∉ Q.frozen)
    (Z : D'.Chamber) (hZgap : Z.gap = D'.levelAt p)
    (hZidx : Z.idx = D'.countUpTo (D'.levelAt p) (p + 1)) :
    (∃! ψ : D.Chamber ≃ D'.Chamber,
        ψ Y = Z ∧ ∀ c, c ≠ Y → (ψ c).chamberSet = c.chamberSet) ∧
      ∀ ψ : D.Chamber ≃ D'.Chamber, ψ Y = Z →
        (∀ c, c ≠ Y → (ψ c).chamberSet = c.chamberSet) →
        ∃ i : (Q.mutate hY).Iso Q', i.equiv = ψ :=
  sorry

/-- **The chambers of a double wiring diagram**. A double wiring diagram on `n + 2` strands has `(n
+ 2) ^ 2` chambers, of which `(n + 1) ^ 2` are bounded, whatever its word. -/
theorem card_chamber_and_card_bounded {n : ℕ} (D : DoubleWiringDiagram n) :
    Fintype.card D.Chamber = (n + 2) ^ 2 ∧
      (Finset.univ.filter fun c : D.Chamber => c.Bounded).card = (n + 1) ^ 2 :=
  sorry

/-- **Tree orientations are mutation inequivalent**, granted the Caldero–Keller theorem. An acyclic
quiver mutation equivalent to an orientation of a finite tree orients a finite tree isomorphic to
it, so orientations of non-isomorphic trees are never mutation equivalent. -/
theorem exists_isTreeOrientation_of_mutationEquivalent.{u} (hCK : CalderoKeller.{u})
    {V V' : Type u} [Fintype V]
    [Fintype V'] [DecidableEq V] {T : FiniteSimpleGraph V} {Q : Quiver V} {Q' : Quiver V'}
    (hT : IsFiniteTree T) (hQ : Q.IsTreeOrientation T) (hQ' : Acyclic Q')
    (hfQ' : Q'.frozen = ∅) (h : Q.MutationEquivalent Q') :
    ∃ T' : FiniteSimpleGraph V',
      IsFiniteTree T' ∧ Q'.IsTreeOrientation T' ∧ Nonempty (T ≃g T') :=
  sorry

/-- **The finite type classification**, granted the Cartan–Killing classification and the
exercises stated above as hypotheses. A seed pattern is of finite type if and only if, for some
vertex `t`, the Cartan counterpart of the exchange matrix of `P t` is a Cartan matrix of finite
type. -/
theorem isFiniteType_iff_exists_isCartanFiniteType.{u} {K : Type u} {F : Type*} [Field K]
    [Field F] [Algebra K F] {m n : ℕ} [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hCartanKilling : CartanKilling)
    (hExistsIsTShapeMatrixMutationListOfIsCrownShape :
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
    (hIsGloballyFoldableMatrixE₆Lift : TypeFG.IsGloballyFoldableMatrixE₆Lift) :
    IsFiniteType P ↔
      ∃ t, IsCartanFiniteType (cartanCounterpart (principalPart hmn (P t).extExchangeMatrix)) :=
  sorry

end Challenge

end ClusterAlgebras

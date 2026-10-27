/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
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
  isArrowSystem _ := Nat.sub_eq_zero_of_le (le_min le_rfl le_rfl)
  twoCycleFree i j :=
    (le_total (reversal (Q.stepOne k) k i j) (reversal (Q.stepOne k) k j i)).imp
      (fun h => Nat.sub_eq_zero_of_le (le_min le_rfl h))
      (fun h => Nat.sub_eq_zero_of_le (le_min le_rfl h))
  frozen_eq_zero u hu v hv :=
    have hne : ¬(u = k ∨ v = k) := fun h => h.elim (fun e => hk (e ▸ hu)) (fun e => hk (e ▸ hv))
    Nat.sub_eq_zero_of_le
      (((if_neg hne).trans ((if_pos ⟨hu, hv⟩).trans (Q.frozen_eq_zero u hu v hv))).le.trans
        (Nat.zero_le _))

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
  weight_eq_zero_of_notMem _ hp := if_neg hp

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
  isArrowSystem v := by revert v; decide
  twoCycleFree i j := by revert i j; decide
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
instance instDecidableArrow (c c' : D.Chamber) : Decidable (D.Arrow c c') :=
  inferInstanceAs (Decidable ((c.Bounded ∨ c'.Bounded) ∧
    ((c.gap = c'.gap ∧ c.right = c'.left) ∨
      (((c'.gap : ℕ) + 1 = (c.gap : ℕ) ∨ (c.gap : ℕ) + 1 = (c'.gap : ℕ)) ∧
        c'.left < c.left ∧ c.left < c'.right ∧ c'.right < c.right))))

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
`prop_trees_inequivalent` as a hypothesis. -/

/-- **Caldero–Keller.** Two acyclic quivers without frozen vertices that are mutation
equivalent are joined by a sequence of mutations performed only at sources and sinks. -/
def CalderoKeller.{u} : Prop :=
  ∀ {V V' : Type u} [Fintype V] [Fintype V'] [DecidableEq V] {Q : Quiver V} {Q' : Quiver V'},
    Acyclic Q → Acyclic Q' → Q.frozen = ∅ → Q'.frozen = ∅ → Q.MutationEquivalent Q' →
      ∃ p : Q.MutationPath, p.AtSourceOrSink ∧ Nonempty (p.result.Iso Q')

namespace Challenge

/-- **`lem_adjmatrix` — quiver mutation is matrix mutation.** Mutating a quiver and then
taking its extended exchange matrix agrees with taking the matrix and then mutating it. -/
theorem lem_adjmatrix {V : Type*} [Fintype V] [DecidableEq V] {m n : ℕ} (Q : Quiver V)
    (L : Labelling Q m n) (k : Fin n) (hk : L.equiv (Fin.castLE L.le k) ∉ Q.frozen) :
    extExchangeMatrix (Q.mutate hk) (L.mutate hk)
      = matrixMutation L.le (extExchangeMatrix Q L) k :=
  sorry

/-- **`thm_det_invariant` — mutation preserves the determinant.** -/
theorem thm_det_invariant {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {n : ℕ} (hnn : n ≤ n) (B : Matrix (Fin n) (Fin n) R) (k : Fin n) (hk : B k k = 0) :
    (matrixMutation hnn B k).det = B.det :=
  sorry

/-- **`thm_rank_invariant` — mutation preserves the rank.** -/
theorem thm_rank_invariant {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {m n : ℕ} (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n)
    (hk : B (Fin.castLE hmn k) k = 0) :
    (matrixMutation hmn B k).rank = B.rank :=
  sorry

/-- **`lem_gcd_invariant` — mutation preserves the greatest common divisor of the entries**,
granted that mutating twice at `k` returns `B`. That involutivity is the one assumption here:
FWZ leave it as an exercise, so it is a hypothesis rather than something proved. -/
theorem lem_gcd_invariant {m n : ℕ} (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n)
    (hinv : matrixMutation hmn (matrixMutation hmn B k) k = B) :
    (Finset.univ.gcd fun p : Fin m × Fin n => matrixMutation hmn B k p.1 p.2) =
      Finset.univ.gcd fun p : Fin m × Fin n => B p.1 p.2 :=
  sorry

/-- **`lem_skew_symmetrizing_vector_unique` — a skew-symmetrizing vector of a matrix with
connected diagram is unique up to a scalar.** The ratio of two of them does not depend on the
index. -/
theorem lem_skew_symmetrizing_vector_unique {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {d d' : Fin n → ℤ} (hΓ : (diagram B).Connected) (hd : IsSkewSymmetrizingVector B d)
    (hd' : IsSkewSymmetrizingVector B d') (i j : Fin n) :
    (d i : ℚ) / (d' i : ℚ) = (d j : ℚ) / (d' j : ℚ) :=
  sorry

/-- **`lem_markov_self_similar` — the Markov quiver is fixed by mutation up to
isomorphism.** -/
theorem lem_markov_self_similar {k : Fin 3} (hk : k ∉ markovQuiver.frozen) :
    Nonempty ((markovQuiver.mutate hk).Iso markovQuiver) :=
  sorry

/-- **`lem_wiring_quiver_is_quiver` — the arrow counts of a wiring diagram form a quiver.**
No chamber carries an arrow to itself, no two chambers carry arrows in both directions, and no
arrow joins two unbounded chambers. These are exactly the three conditions `Quiver` asks of its
arrow function, so this says that `Q(D)` exists. -/
theorem lem_wiring_quiver_is_quiver {n : ℕ} (D : WiringDiagram n) :
    IsArrowSystem D.wiringArrows ∧ TwoCycleFree D.wiringArrows ∧
      ∀ c c' : D.Chamber, ¬c.Bounded → ¬c'.Bounded → D.wiringArrows c c' = 0 :=
  sorry

/-- **`prop_braid_is_mutation` — a braid move mutates the quiver of a wiring diagram.**
For wiring diagrams `D` and `D'` related by a braid move with site `Y` and replacement `Z`,
there is exactly one bijection of the chambers sending `Y` to `Z` and preserving the chamber set
of every other chamber, and that bijection is an isomorphism from `μ_Y(Q(D))` to `Q(D')`. The
two quivers are given by their arrow counts and frozen sets rather than constructed, so the
statement is conditional; `lem_wiring_quiver_is_quiver` is what says such quivers exist. -/
theorem prop_braid_is_mutation {n : ℕ} (D D' : WiringDiagram n) (p : ℕ)
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

/-- **`lem_double_chamber_count` — a double wiring diagram has `(n + 2) ^ 2` chambers, of which
`(n + 1) ^ 2` are bounded.** Neither count depends on the word. -/
theorem lem_double_chamber_count {n : ℕ} (D : DoubleWiringDiagram n) :
    Fintype.card D.Chamber = (n + 2) ^ 2 ∧
      (Finset.univ.filter fun c : D.Chamber => c.Bounded).card = (n + 1) ^ 2 :=
  sorry

/-- **`prop_trees_inequivalent` — an acyclic quiver mutation equivalent to an orientation of
a finite tree orients a finite tree isomorphic to it.** Hence orientations of non-isomorphic
trees are never mutation equivalent. The tree is determined only up to isomorphism, mutation
equivalence being insensitive to relabelling the vertices. -/
theorem prop_trees_inequivalent.{u} (hCK : CalderoKeller.{u}) {V V' : Type u} [Fintype V]
    [Fintype V'] [DecidableEq V] {T : FiniteSimpleGraph V} {Q : Quiver V} {Q' : Quiver V'}
    (hT : IsFiniteTree T) (hQ : Q.IsTreeOrientation T) (hQ' : Acyclic Q')
    (hfQ' : Q'.frozen = ∅) (h : Q.MutationEquivalent Q') :
    ∃ T' : FiniteSimpleGraph V',
      IsFiniteTree T' ∧ Q'.IsTreeOrientation T' ∧ Nonempty (T ≃g T') :=
  sorry

end Challenge

end ClusterAlgebras

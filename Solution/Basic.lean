/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ClusterAlgebras

/-! # Satisfying the formal challenge -/

@[expose] public section

namespace ClusterAlgebras.Challenge

/-- **Quiver mutation is matrix mutation**. Mutating a quiver and then taking its extended exchange
matrix agrees with taking the matrix and then mutating it. -/
theorem extExchangeMatrix_mutate_eq_matrixMutation {V : Type*} [Fintype V] [DecidableEq V]
    {m n : ℕ} (Q : Quiver V)
    (L : Labelling Q m n) (k : Fin n) (hk : L.equiv (Fin.castLE L.le k) ∉ Q.frozen) :
    extExchangeMatrix (Q.mutate hk) (L.mutate hk)
      = matrixMutation L.le (extExchangeMatrix Q L) k :=
  extExchangeMatrix_mutate Q L k

/-- **Mutation preserves the determinant**, when the mutated diagonal entry vanishes. -/
theorem det_matrixMutation_eq {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {n : ℕ} (hnn : n ≤ n) (B : Matrix (Fin n) (Fin n) R) (k : Fin n) (hk : B k k = 0) :
    (matrixMutation hnn B k).det = B.det :=
  det_matrixMutation hnn B k hk

/-- **Mutation preserves the rank**, when the mutated diagonal entry vanishes. -/
theorem rank_matrixMutation_eq {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {m n : ℕ} (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n)
    (hk : B (Fin.castLE hmn k) k = 0) :
    (matrixMutation hmn B k).rank = B.rank :=
  rank_matrixMutation hmn B k hk

/-- **Mutation preserves the greatest common divisor of the entries**, granted that mutating twice
at `k` returns `B`. FWZ leave that involutivity as an exercise, so it is a hypothesis here. -/
theorem gcd_matrixMutation_eq_of_involutive {m n : ℕ} (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ)
    (k : Fin n)
    (hinv : matrixMutation hmn (matrixMutation hmn B k) k = B) :
    (Finset.univ.gcd fun p : Fin m × Fin n => matrixMutation hmn B k p.1 p.2) =
      Finset.univ.gcd fun p : Fin m × Fin n => B p.1 p.2 :=
  gcd_matrixMutation_of_involutive hmn B k hinv

/-- **Skew-symmetrizing vectors are unique up to a scalar**. For a matrix with connected diagram,
the ratio of two skew-symmetrizing vectors does not depend on the index. -/
theorem div_eq_div_of_isSkewSymmetrizingVector {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {d d' : Fin n → ℤ} (hΓ : (diagram B).Connected) (hd : IsSkewSymmetrizingVector B d)
    (hd' : IsSkewSymmetrizingVector B d') (i j : Fin n) :
    (d i : ℚ) / (d' i : ℚ) = (d j : ℚ) / (d' j : ℚ) :=
  hd.div_eq_div_of_connected hΓ hd' i j

/-- **The Markov quiver is self-similar**. Its mutation at each vertex is isomorphic to it. -/
theorem nonempty_iso_markovQuiver_mutate {k : Fin 3} (hk : k ∉ markovQuiver.frozen) :
    Nonempty ((markovQuiver.mutate hk).Iso markovQuiver) :=
  markovQuiver_iso_mutate hk

/-- **The arrows of a wiring diagram form a quiver**. No chamber carries an arrow to itself, no two
chambers carry arrows in both directions, and no arrow joins two unbounded chambers: the three
conditions `Quiver` asks of its arrow function. -/
theorem isArrowSystem_and_twoCycleFree_wiringArrows {n : ℕ} (D : WiringDiagram n) :
    IsArrowSystem D.wiringArrows ∧ TwoCycleFree D.wiringArrows ∧
      ∀ c c' : D.Chamber, ¬c.Bounded → ¬c'.Bounded → D.wiringArrows c c' = 0 :=
  ⟨D.isArrowSystem_wiringArrows, D.twoCycleFree_wiringArrows,
    fun _ _ hc hc' => D.wiringArrows_eq_zero_of_not_bounded hc hc'⟩

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
        ∃ i : (Q.mutate hY).Iso Q', i.equiv = ψ := by
  have hDD' : D' = D.braidMove p hp hgh hgg := WiringDiagram.ext' (by rw [hD']; rfl)
  subst hDD'
  have hQQ : Q = D.wiringQuiver :=
    Quiver.ext' (by ext c; rw [hQf, D.mem_frozen_wiringQuiver]) hQa
  subst hQQ
  have hQQ' : Q' = (D.braidMove p hp hgh hgg).wiringQuiver :=
    Quiver.ext' (by ext c; rw [hQ'f, (D.braidMove p hp hgh hgg).mem_frozen_wiringQuiver]) hQ'a
  subst hQQ'
  have hYY : Y = D.braidSite hp := WiringDiagram.Chamber.ext' hYgap hYidx
  subst hYY
  have hZZ : Z = D.braidReplacement hp hgh hgg := WiringDiagram.Chamber.ext' hZgap hZidx
  subst hZZ
  have key : ∀ ψ : D.Chamber ≃ (D.braidMove p hp hgh hgg).Chamber,
      ψ (D.braidSite hp) = D.braidReplacement hp hgh hgg →
      (∀ c, c ≠ D.braidSite hp → (ψ c).chamberSet = c.chamberSet) →
      ψ = D.braidEquiv hp hgh hgg := fun ψ h1 h2 =>
    Equiv.ext fun c => by
      rw [D.braidEquiv_apply hp hgh hgg]
      exact D.eq_braidChamber_of_chamberSet hp hgh hgg h1 h2 c
  refine ⟨⟨D.braidEquiv hp hgh hgg, ⟨by simp, fun c hc => ?_⟩, ?_⟩, fun ψ h1 h2 => ?_⟩
  · rw [D.braidEquiv_apply hp hgh hgg]
    exact D.chamberSet_braidChamber_of_ne hp hgh hgg hc
  · rintro ψ ⟨h1, h2⟩
    exact key ψ h1 h2
  · exact ⟨D.braidIso hp hgh hgg, (key ψ h1 h2).symm⟩

/-- **The chambers of a double wiring diagram**. A double wiring diagram on `n + 2` strands has `(n
+ 2) ^ 2` chambers, of which `(n + 1) ^ 2` are bounded, whatever its word. -/
theorem card_chamber_and_card_bounded {n : ℕ} (D : DoubleWiringDiagram n) :
    Fintype.card D.Chamber = (n + 2) ^ 2 ∧
      (Finset.univ.filter fun c : D.Chamber => c.Bounded).card = (n + 1) ^ 2 :=
  ⟨D.card_chamber, D.card_bounded_chamber⟩

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
  exists_isTreeOrientation_of_calderoKeller hCK hT hQ hQ' hfQ' h

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
  IsSeedPattern.isFiniteType_iff_exists_isCartanFiniteType hmn hP hCartanKilling
    hExistsIsTShapeMatrixMutationListOfIsCrownShape hIsCyclicallyOrientedOfIsTwoFinite
    hIsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne hSubmatrixMatrixMutation
    hMatrixMutationMatrixMutation hPluckerCoordThreeTerm₀ hPluckerCoordThreeTerm
    hPolygonQuiverMutateIsoFlip hExistsMutationPathOfIsTreeOrientation
    hSkewSymmetrizationMatrixMutation hLabelledMatrixDFlip hIsGloballyFoldableMatrixE₆Lift

end ClusterAlgebras.Challenge

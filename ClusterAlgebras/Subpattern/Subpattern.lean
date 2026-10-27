/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.ClusterAlgebra
public import ClusterAlgebras.Subpattern.Freezing
public import ClusterAlgebras.Subpattern.RestrictedSeed

/-!
# Seed subpatterns and cluster subalgebras

A seed pattern `Π` of rank `n'` is a *seed subpattern* of a seed pattern `Σ` of rank `n` when
one of its seeds is obtained from a seed `Σ(t)` by freezing a set `S` of mutable indices,
restricting to a set `I` of indices for which the enumeration `ι_I` is closed for the frozen
matrix, and relabelling by a bijective restriction map `π`: `Π(t') = ((Fr_S(Σ(t)))_I)^π`
(`ClusterAlgebras.IsSeedSubpattern`). The cluster algebra of a seed subpattern is a *cluster
subalgebra* (`ClusterAlgebras.IsClusterSubalgebra`).

Writing `r = φ_S ∘ ι_I ∘ π`, the seed `((Fr_S(Σ(t)))_I)^π` is the reindexing `Σ(t)^r`
(`ClusterAlgebras.SeedData.reindex_restrict_freeze`), and `r` is closed for the matrix of
`Σ(t)`. Since reindexing along a closed map commutes with mutation, every seed of `Π` is a
reindexing `Σ(u)^r` along the same map `r`
(`ClusterAlgebras.IsSeedSubpattern.exists_map_eq_reindex`). Consequently every cluster
variable of `Π` is a cluster variable of `Σ`, and a seed subpattern of a pattern with finitely
many cluster variables has finitely many cluster variables
(`ClusterAlgebras.IsSeedSubpattern.finite_iUnion_clusterVariables`).

## Main definitions

* `ClusterAlgebras.IsSeedSubpattern`: `Π` is a seed subpattern of `Σ`, along a `K`-algebra
  embedding `ι` of the field of `Π` into that of `Σ`.
* `ClusterAlgebras.IsClusterSubalgebra`: a subring of `F` is a cluster subalgebra of the
  cluster algebra of `Σ`.

## Main results

* `ClusterAlgebras.SeedData.reindex_restrict_freeze`: `((Fr_S(x̃, B̃))_I)^π` is the reindexing
  of `(x̃, B̃)` along `φ_S ∘ ι_I ∘ π`.
* `ClusterAlgebras.IsSeedSubpattern.exists_map_eq_reindex`: the seeds of a subpattern are
  reindexed seeds of the pattern, along a single reindexing map closed for their matrices.
* `ClusterAlgebras.IsSeedSubpattern.finite_iUnion_clusterVariables`: a seed subpattern of a
  pattern with finitely many cluster variables has finitely many cluster variables.

## Implementation notes

* In [FWZ17], `Π` is a seed pattern in a subfield `F' ⊆ F` containing `K`. Here `Π` is a seed
  pattern in any field `E` over `K`, together with a `K`-algebra homomorphism `ι : E →ₐ[K] F`,
  injective because `E` is a field; the seeds of `Π` are compared with those of `Σ` after
  applying `ι` to their entries. A subfield is the case `E = F'` an intermediate field and
  `ι = F'.val`, and every injective `ι` is that case for `F' = ι(E)` up to isomorphism, so this
  is a generalisation. It is what makes a subpattern of a subpattern typecheck: the field `F''`
  of the inner subpattern embeds in `F` along the composite embedding, whereas a subfield of
  `F'` is not literally a subfield of `F`.

* The relabelling `π` is a bijective restriction map from `(m', n')` to `(|I|, n_I)`, where
  `n_I = mutableCard (n - |S|) I` counts the indices of `I` below `n_S = n - |S|`. The
  definition also asks `|I| = m'` and `n_I = n'`, so this is a bijective restriction map from
  `(m', n')` to itself, as in [FWZ17]; typing it with target `(|I|, n_I)` lets it be composed
  with `ι_I` without a cast along these equations.

* In [FWZ17], `Σ` is presupposed to be a seed pattern; `IsSeedSubpattern` does not ask for it,
  and the results that walk in `Σ` take `IsSeedPattern K hmn P` as a hypothesis. That `Π` is a
  seed pattern is part of the definition.

* Only the mutation relations of the two patterns are used: `seedMutation_reindex` and
  `seedMutation_map` hold without the nonvanishing of the exchanged variable, so the seeds of
  `Π` are reached by the mutation sequence from `t'` to `u'`
  (`IsSeedPattern.apply_eq_seedMutationSeq`), carried over to `Σ` along `r`.

* A cluster subalgebra is a subring of `F`: the image under the inclusion of an intermediate
  field `E` of the cluster algebra of a seed subpattern in `E`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 4–5*][FWZ17]
-/

@[expose] public section

namespace ClusterAlgebras

variable {m n m' n' : ℕ}

/-! ### The seed of a subpattern as a reindexed seed -/

section Reindex

variable {F : Type*}

/-- **Freezing, restricting and relabelling is reindexing along the composite**:
`((Fr_S(x̃, B̃))_I)^π = (x̃, B̃)^{φ_S ∘ ι_I ∘ π}`. -/
theorem SeedData.reindex_restrict_freeze (hmn : n ≤ m) (h' : n' ≤ m') (Sd : SeedData F m n)
    (S : Finset (Fin n)) (I : Finset (Fin m))
    (π : ReindexingMap m' n' I.card (mutableCard (n - S.card) I)) :
    ((Sd.freeze hmn S).restrict I).reindex h' π
      = Sd.reindex h' ((freezingMap hmn S).comp ((enumerationMap (n - S.card) I).comp π)) :=
  rfl

end Reindex

/-! ### Seed subpatterns -/

section Subpattern

variable {K F E : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]

/-- `P'` is a **seed subpattern** of `P` along the `K`-algebra embedding `ι : E →ₐ[K] F` when
`P'` is a seed pattern in `E` over `K` and there are vertices `t ∈ 𝕋ₙ`, `t' ∈ 𝕋_{n'}`, a set
`S` of mutable indices and a set `I` of indices with `|I| = m'` and `n_I = n'` (the indices of
`I` below `n - |S|`), and a bijective restriction map `π`, such that the enumeration `ι_I` is
closed for `Fr_S(B̃(t))` and `P'(t')`, read in `F` along `ι`, is `((Fr_S(P(t)))_I)^π`.

A subpattern in a subfield `F' ⊆ F` containing `K` is the case `ι = F'.val`. -/
@[cluster_algebras "def_seed_subpattern"]
def IsSeedSubpattern (hmn : n ≤ m) (h' : n' ≤ m') (ι : E →ₐ[K] F)
    (P : RegularTree n → SeedData F m n) (P' : RegularTree n' → SeedData E m' n') : Prop :=
  IsSeedPattern K h' P' ∧ ∃ (t : RegularTree n) (t' : RegularTree n') (S : Finset (Fin n))
    (I : Finset (Fin m)), I.card = m' ∧ mutableCard (n - S.card) I = n' ∧
    ∃ π : ReindexingMap m' n' I.card (mutableCard (n - S.card) I), π.IsRestriction ∧
      Function.Bijective π ∧
      (enumerationMap (n - S.card) I).IsClosedFor (mutableCard_le_card _ I)
        (matrixFreeze hmn S (P t).extExchangeMatrix) ∧
      (P' t').map ι = (((P t).freeze hmn S).restrict I).reindex h' π

variable {hmn : n ≤ m} {h' : n' ≤ m'} {ι : E →ₐ[K] F} {P : RegularTree n → SeedData F m n}
  {P' : RegularTree n' → SeedData E m' n'}

/-- A seed subpattern is a seed pattern. -/
theorem IsSeedSubpattern.isSeedPattern (hsub : IsSeedSubpattern hmn h' ι P P') :
    IsSeedPattern K h' P' :=
  hsub.1

/-- A seed subpattern from a seed of `P` reindexed along `φ_S ∘ ι_I ∘ π`: the condition
`P'(t') = ((Fr_S(P(t)))_I)^π` of `IsSeedSubpattern`, in the form given by
`SeedData.reindex_restrict_freeze`. -/
theorem isSeedSubpattern_of_map_eq_reindex (hP' : IsSeedPattern K h' P') (t : RegularTree n)
    (t' : RegularTree n') (S : Finset (Fin n)) (I : Finset (Fin m)) (hI : I.card = m')
    (hIn : mutableCard (n - S.card) I = n')
    (π : ReindexingMap m' n' I.card (mutableCard (n - S.card) I)) (hπ : π.IsRestriction)
    (hπb : Function.Bijective π)
    (hcl : (enumerationMap (n - S.card) I).IsClosedFor (mutableCard_le_card _ I)
      (matrixFreeze hmn S (P t).extExchangeMatrix))
    (heq : (P' t').map ι
      = (P t).reindex h' ((freezingMap hmn S).comp ((enumerationMap (n - S.card) I).comp π))) :
    IsSeedSubpattern hmn h' ι P P' :=
  ⟨hP', t, t', S, I, hI, hIn, π, hπ, hπb, hcl,
    heq.trans (SeedData.reindex_restrict_freeze hmn h' _ S I π).symm⟩

/-- **The seeds of a subpattern are reindexed seeds of the pattern**: if `P'` is a seed
subpattern of the seed pattern `P` along `ι`, there is a reindexing map `r` from `(m', n')` to
`(m, n)` such that every seed `P'(u')`, read in `F` along `ι`, is `P(u)^r` for some vertex `u`
with `r` closed for `B̃(u)`.

The map is `r = φ_S ∘ ι_I ∘ π`. -/
@[cluster_algebras "lem_subpattern_seeds"]
theorem IsSeedSubpattern.exists_map_eq_reindex (hP : IsSeedPattern K hmn P)
    (hsub : IsSeedSubpattern hmn h' ι P P') :
    ∃ r : ReindexingMap m' n' m n, ∀ u' : RegularTree n', ∃ u : RegularTree n,
      r.IsClosedFor h' (P u).extExchangeMatrix ∧ (P' u').map ι = (P u).reindex h' r := by
  obtain ⟨hP', t, t', S, I, -, -, π, -, hπb, hcl, heq⟩ := hsub
  set r := (freezingMap hmn S).comp ((enumerationMap (n - S.card) I).comp π)
  have hr : r.IsClosedFor h' (P t).extExchangeMatrix :=
    (freezingMap_isClosedFor hmn S (sub_card_le_of_le hmn S) _).comp
      (hcl.comp (ReindexingMap.isClosedFor_of_surjective hπb.2 h' _))
  refine ⟨r, fun u' => ?_⟩
  set s := t'.word.reverse ++ u'.word
  obtain ⟨u, hu⟩ := hP.seedMutationSeq_mem_range hmn t (s.map (r.col h'))
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    exact hr.seedMutationSeq hmn s
  · rw [hP'.apply_eq_seedMutationSeq h' t' u', seedMutationSeq_map, heq,
      SeedData.reindex_restrict_freeze, seedMutationSeq_reindex hmn h' _ hr, ← hu]

/-- **A seed subpattern of a pattern with finitely many cluster variables has finitely many
cluster variables**: if `P` is a seed pattern whose seeds have finitely many cluster variables
in all, and `P'` is a seed subpattern of `P`, then the seeds of `P'` have finitely many cluster
variables in all. -/
@[cluster_algebras "lem_subalgebra_finite"]
theorem IsSeedSubpattern.finite_iUnion_clusterVariables (hP : IsSeedPattern K hmn P)
    (hsub : IsSeedSubpattern hmn h' ι P P')
    (hfin : (⋃ t, clusterVariables hmn (P t)).Finite) :
    (⋃ t', clusterVariables h' (P' t')).Finite := by
  obtain ⟨r, hr⟩ := hsub.exists_map_eq_reindex hP
  refine (hfin.preimage (RingHom.injective (ι : E →+* F)).injOn).subset ?_
  rintro _ ⟨_, ⟨u', rfl⟩, ⟨p, rfl⟩⟩
  obtain ⟨u, -, hu⟩ := hr u'
  refine Set.mem_iUnion.2 ⟨u, r.col h' p, ?_⟩
  have := congrArg (fun Sd : SeedData F m' n' => Sd.extCluster (Fin.castLE h' p)) hu
  exact this.symm

end Subpattern

/-! ### Cluster subalgebras -/

section Subalgebra

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]

/-- A subring `A'` of `F` is a **cluster subalgebra** of the cluster algebra of `P` when it is
the cluster algebra of a seed subpattern of `P` in an intermediate field `E` of `F / K`, read
in `F` along the inclusion `E → F`. -/
@[cluster_algebras "def_cluster_subalgebra"]
def IsClusterSubalgebra (hmn : n ≤ m) (P : RegularTree n → SeedData F m n) (A' : Subring F) :
    Prop :=
  ∃ (m' n' : ℕ) (h' : n' ≤ m') (E : IntermediateField K F)
    (P' : RegularTree n' → SeedData E m' n'),
    IsSeedSubpattern hmn h' E.val P P' ∧ A' = ((clusterAlgebra K h' P').map E.val).toSubring

variable {K}

/-- The cluster algebra of a seed subpattern in an intermediate field is a cluster
subalgebra. -/
theorem IsSeedSubpattern.isClusterSubalgebra {hmn : n ≤ m} {h' : n' ≤ m'}
    {P : RegularTree n → SeedData F m n} {E : IntermediateField K F}
    {P' : RegularTree n' → SeedData E m' n'} (hsub : IsSeedSubpattern hmn h' E.val P P') :
    IsClusterSubalgebra K hmn P ((clusterAlgebra K h' P').map E.val).toSubring :=
  ⟨m', n', h', E, P', hsub, rfl⟩

end Subalgebra

end ClusterAlgebras

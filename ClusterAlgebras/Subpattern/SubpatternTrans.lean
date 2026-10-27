/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Subpattern.Factorization
public import ClusterAlgebras.Subpattern.Subpattern

/-!
# A subpattern of a subpattern is a subpattern

If `Π` is a seed subpattern of a seed pattern `Σ` and `Π'` is a seed subpattern of `Π`, then `Π'`
is a seed subpattern of `Σ` [FWZ17, Lemma 4.2.7].

The seeds of a subpattern are reindexed seeds of the pattern along a single closed reindexing
map. So a seed of `Π'` is `Π(u')^{r'}` and `Π(u')` is `Σ(u)^r`, whence the seed of `Π'` is
`Σ(u)^{r ∘ r'}`, with `r ∘ r'` closed for the matrix of `Σ(u)`. A closed reindexing map
factors as a freezing, a restriction and a relabelling, which is exactly the data of a seed
subpattern.

## Main results

* `ClusterAlgebras.IsSeedSubpattern.trans`: a seed subpattern of a seed subpattern of a seed
  pattern `Σ` is a seed subpattern of `Σ`, along the composite embedding of fields.

## Implementation notes

* FWZ take subfields `F'' ⊆ F' ⊆ F`. Here, as in `IsSeedSubpattern`, the fields of the
  subpatterns are arbitrary fields `E'` and `E` over `K` with `K`-algebra embeddings
  `ι' : E' →ₐ[K] E` and `ι : E →ₐ[K] F`; the inclusion `F'' ⊆ F` is the composite `ι.comp ι'`.
  Subfields with their inclusions are a special case.

* Repeated freezing and restriction is a single freezing followed by a single restriction only
  up to a relabelling of the indices, since freezing renumbers the newly frozen indices in front
  of the old frozen ones. The relabelling `π` in the definition of a seed subpattern absorbs
  this, and the factorization `ReindexingMap.exists_freeze_restrict_factorization` produces it.

* That `Π` is a seed pattern, needed to see the seeds of `Π'` as reindexed seeds of `Π`, is part
  of the definition of a seed subpattern.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 4–5*][FWZ17]
-/

@[expose] public section

namespace ClusterAlgebras

variable {m n m' n' m'' n'' : ℕ} {K F E E' : Type*} [Field K] [Field F] [Field E] [Field E']
  [Algebra K F] [Algebra K E] [Algebra K E']

/-- If `P` is a seed pattern in `F`, `P'` is a seed subpattern of `P` along `ι : E →ₐ[K] F` and
`P''` is a seed subpattern of `P'` along `ι' : E' →ₐ[K] E`, then `P''` is a seed subpattern of `P`
along the composite `ι.comp ι'`. -/
@[cluster_algebras "lem_subpattern_trans"]
theorem IsSeedSubpattern.trans {hmn : n ≤ m} {h' : n' ≤ m'} {h'' : n'' ≤ m''}
    {ι : E →ₐ[K] F} {ι' : E' →ₐ[K] E} {P : RegularTree n → SeedData F m n}
    {P' : RegularTree n' → SeedData E m' n'} {P'' : RegularTree n'' → SeedData E' m'' n''}
    (hP : IsSeedPattern K hmn P) (hsub : IsSeedSubpattern hmn h' ι P P')
    (hsub' : IsSeedSubpattern h' h'' ι' P' P'') :
    IsSeedSubpattern hmn h'' (ι.comp ι') P P'' := by
  obtain ⟨r', hr'⟩ := hsub'.exists_map_eq_reindex hsub.isSeedPattern
  obtain ⟨r, hr⟩ := hsub.exists_map_eq_reindex hP
  obtain ⟨hP'', -, u'', -⟩ := hsub'
  obtain ⟨u', hcl', hu'⟩ := hr' u''
  obtain ⟨u, hcl, hu⟩ := hr u'
  have hB : (P' u').extExchangeMatrix = matrixReindex h' (P u).extExchangeMatrix r :=
    congrArg SeedData.extExchangeMatrix hu
  obtain ⟨S, I, hI, hIn, π, hπ, hπb, hclI, hrr⟩ :=
    ReindexingMap.exists_freeze_restrict_factorization hmn h'' (hcl.comp (hB ▸ hcl'))
  refine isSeedSubpattern_of_map_eq_reindex hP'' u u'' S I hI hIn π hπ hπb hclI ?_
  rw [← hrr, ← SeedData.reindex_reindex h' h'', ← hu, ← SeedData.map_reindex, ← hu']
  rfl

end ClusterAlgebras

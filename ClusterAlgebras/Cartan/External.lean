/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Cartan.Dynkin

/-!
# The Cartan–Killing classification

Every indecomposable Cartan matrix of finite type is of type `X` for a single Dynkin symbol `X`.
The converse, that every `C(X)` is of finite type, is `isCartanFiniteType_listCartan`.

## Main results

* `cartan_killing`: an indecomposable Cartan matrix of finite type is of Dynkin type `[X]` for
  some Dynkin symbol `X`.

## Implementation notes

The classification is not developed here: `cartan_killing` is stated as an `axiom`, so
`#print axioms` on any result reports whether it rests on it.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, 3rd ed., Cambridge University Press, 1990,
  Chapter 4.
* W. Fulton and J. Harris, *Representation theory*, Springer, 1991, Section 21.
-/

@[expose] public section

namespace ClusterAlgebras

/-- **The Cartan–Killing classification.** An indecomposable Cartan matrix of finite type is of
type `X` for a single Dynkin symbol `X`. -/
@[cluster_algebras "ext_cartan_killing"]
axiom cartan_killing {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : IsCartanFiniteType A)
    (hind : IsIndecomposable A) : ∃ X : DynkinSymbol, IsOfDynkinType A [X]

end ClusterAlgebras

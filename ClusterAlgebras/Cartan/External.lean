/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ClusterAlgebras.Definitions
public import ClusterAlgebras.Cartan.Dynkin

/-!
# The Cartan–Killing classification

Every indecomposable Cartan matrix of finite type is of type `X` for a single Dynkin symbol `X`.
The converse, that every `C(X)` is of finite type, is `isCartanFiniteType_listCartan`.

## Main results

* `CartanKilling`: an indecomposable Cartan matrix of finite type is of Dynkin type `[X]` for
  some Dynkin symbol `X`.

## Implementation notes

The classification is not developed here: it is the hypothesis `CartanKilling`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, 3rd ed., Cambridge University Press, 1990,
  Chapter 4.
* W. Fulton and J. Harris, *Representation theory*, Springer, 1991, Section 21.
-/

@[expose] public section

namespace ClusterAlgebras

attribute [cluster_algebras "ext_cartan_killing"] ClusterAlgebras.CartanKilling

end ClusterAlgebras

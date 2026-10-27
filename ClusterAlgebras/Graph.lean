/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Quiver
public import ClusterAlgebras.Definitions

/-!
# Finite simple graphs, and orienting one into a quiver

A finite simple graph is a `SimpleGraph` on a finite vertex type;
`ClusterAlgebras.FiniteSimpleGraph` is a reducible abbreviation for it. Its edge set of
two-element subsets is `G.edgeSet` and its adjacency relation is `G.Adj`, related by
`SimpleGraph.mem_edgeSet`.

An orientation of such a graph, `ClusterAlgebras.Quiver.IsOrientation`, is a quiver with no
frozen vertices obtained by choosing a direction for each edge.
-/

@[expose] public section

namespace ClusterAlgebras

attribute [cluster_algebras "def_finite_simple_graph"] FiniteSimpleGraph

variable {V : Type*} [Fintype V]

attribute [cluster_algebras "def_graph_orientation"] Quiver.IsOrientation

end ClusterAlgebras

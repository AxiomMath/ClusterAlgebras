/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.DoubleWiring.Label
public import ClusterAlgebras.WiringDiagram.Chamber
public import ClusterAlgebras.TotalPositivity.Minor

/-!
# The extended clusters of wiring and double wiring diagrams

The chamber minors of FWZ's Sections 1.3 and 1.4, as families in the ring `ℤ[z]` of the generic
`n × n` matrix, indexed by the chambers. Wiring diagrams have `n + 2` strands here, as in
`ClusterAlgebras.WiringDiagram.Basic`, so the generic matrix is `(n + 2) × (n + 2)`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {n : ℕ}

/-- The **extended cluster** of a wiring diagram `D`: the chamber minors `P_{J(c)}(z)`, flag minors
of the generic matrix labelled by the chamber sets, indexed by the chambers `c` of `D`. -/
@[cluster_algebras "def_wiring_extended_cluster"]
noncomputable def wiringExtendedCluster (D : WiringDiagram n) :
    D.Chamber → MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℤ :=
  fun c => flagMinor (genericMatrix (Fin (n + 2)) (Fin (n + 2))) c.chamberSet

/-- The **extended cluster** of a double wiring diagram `D`: the chamber minors
`Δ_{I(c),J(c)}(z)` of the generic matrix, `I(c)` the thin and `J(c)` the thick part of the label,
indexed by the chambers `c` of `D`. -/
@[cluster_algebras "def_double_extended_cluster"]
noncomputable def doubleExtendedCluster (D : DoubleWiringDiagram n) :
    D.Chamber → MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℤ :=
  fun c => minor (genericMatrix (Fin (n + 2)) (Fin (n + 2))) (D.label c .thin) (D.label c .thick)

end ClusterAlgebras

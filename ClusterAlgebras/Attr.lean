module

public meta import Lean

/-!
# The `cluster_algebras` attribute

This file declares the attribute `cluster_algebras`, which takes a string literal and attaches it
to a declaration as a reference label. The attribute has no effect on elaboration.
-/

public meta section

open Lean

/-- The attribute `cluster_algebras`, taking a string literal as the reference label of the
declaration it is applied to. -/
syntax (name := cluster_algebras) "cluster_algebras " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `cluster_algebras
  descr := "attaches a reference label to a declaration"
  add   := fun _ _ _ => pure ()
}

end

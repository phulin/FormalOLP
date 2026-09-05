import TauCeti.Algebra.Algebra.Hom
import FormalOLP

/-!
# FormalOLP dependency compatibility

This smoke test imports a concrete Tau Ceti module and the public FormalOLP root
together.  Tau Ceti's package root is intentionally empty; importing a
concrete `TauCeti.*` module exercises the actual dependency code.  Keeping this
file outside the
`FormalOLP` library prevents the compatibility check from becoming part of the
textbook-facing module tree while still exercising the shared dependency graph.
-/

#check AlgHom.algebraMap_toAlgebra_apply
#check FormalOLP.FirstOrderLogic.SemanticNotions.semantic_consequence_iff_unsatisfiable_negation
#check FormalOLP.FirstOrderLogic.SemanticNotions.semantic_deduction_theorem

example {α : Type*} (s t : Set α) : s ∩ (s ∪ t) = s := by
  exact FormalOLP.SetsFunctionsRelations.intersection_union_absorption s t

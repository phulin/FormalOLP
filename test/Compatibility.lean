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
#check FormalOLP.Computability.turingReducible
#check FormalOLP.Computability.turingEquivalent
#check FormalOLP.Computability.turingEquivalent_equivalence
#check FormalOLP.Computability.setTuringReducible
#check FormalOLP.Computability.setTuringEquivalent_equivalence
#check FormalOLP.SetTheory.membershipFormula
#check FormalOLP.SetTheory.realize_membership
#check FormalOLP.SetTheory.ModelExtensionality.emptyset_unique
#check FormalOLP.SetTheory.ModelExtensionality.emptyset_exists_unique
#check FormalOLP.SetTheory.ModelExtensionality.pair_unique
#check FormalOLP.SetTheory.ModelExtensionality.pair_exists_unique
#check FormalOLP.SetTheory.ModelExtensionality.singleton_exists_unique

example (f g h : ℕ →. ℕ)
    (hfg : FormalOLP.Computability.turingReducible f g)
    (hgh : FormalOLP.Computability.turingReducible g h) :
    FormalOLP.Computability.turingReducible f h := by
  exact FormalOLP.Computability.turingReducible_trans hfg hgh

example (f g : ℕ →. ℕ) :
    FormalOLP.Computability.turingEquivalent f g →
      FormalOLP.Computability.turingEquivalent g f := by
  exact FormalOLP.Computability.turingEquivalent_symm

example (A B C : Set ℕ)
    (hAB : FormalOLP.Computability.setTuringReducible A B)
    (hBC : FormalOLP.Computability.setTuringReducible B C) :
    FormalOLP.Computability.setTuringReducible A C := by
  exact FormalOLP.Computability.setTuringReducible_trans hAB hBC

example (A B : Set ℕ) :
    FormalOLP.Computability.setTuringEquivalent A B →
      FormalOLP.Computability.setTuringEquivalent B A := by
  exact FormalOLP.Computability.setTuringEquivalent_symm

example {α : Type*} (s t : Set α) : s ∩ (s ∪ t) = s := by
  exact FormalOLP.SetsFunctionsRelations.intersection_union_absorption s t

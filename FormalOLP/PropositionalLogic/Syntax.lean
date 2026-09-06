/-!
# Native propositional syntax

This formula language is shared by the classical and intuitionistic OLP
topics.  It uses falsum, conjunction, disjunction, and implication as the
primitive constructors, with negation and verum defined below.

The declarations correspond to `LO.IntProp.Formula`,
`LO.IntProp.Formula.neg`, and `LO.IntProp.Formula.verum` in
`LeanPool/Incompleteness/Foundation/IntProp/Formula.lean` at Pool revision
`c8ddda0a64f21cb019720cdda48c94354d4091e7`.  They are re-declared natively;
no LeanPool source is imported.
-/

namespace FormalOLP.PropositionalLogic

universe u

/-- Propositional formulas over a type of atoms. -/
inductive Formula (Atom : Type u) : Type u where
  | atom : Atom → Formula Atom
  | falsum : Formula Atom
  | and : Formula Atom → Formula Atom → Formula Atom
  | or : Formula Atom → Formula Atom → Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  deriving DecidableEq

namespace Formula

variable {Atom : Type u}

/-- Intuitionistic negation, defined using implication and falsum. -/
def neg (φ : Formula Atom) : Formula Atom := .imp φ .falsum

/-- Verum, defined as falsum implying falsum. -/
def verum : Formula Atom := .imp .falsum .falsum

@[simp] theorem neg_eq (φ : Formula Atom) : neg φ = .imp φ .falsum := rfl

@[simp] theorem verum_eq : (verum : Formula Atom) = .imp .falsum .falsum := rfl

end Formula

end FormalOLP.PropositionalLogic

/-!
# Syntax for normal modal logic

This is the formula language used by the native FormalOLP relational-model
development.  It follows the OLP convention of taking falsum and implication
as primitive and defining the remaining connectives.

The inductive shape and connective definitions correspond to
`LO.Modal.Formula`, `LO.Modal.Formula.neg`, `LO.Modal.Formula.or`,
`LO.Modal.Formula.and`, and `LO.Modal.Formula.dia` in
`LeanPool/Incompleteness/Foundation/Modal/Formula.lean` at Pool revision
`c8ddda0a64f21cb019720cdda48c94354d4091e7`.  They are re-declared natively;
no Pool source is imported by this module.
-/

namespace FormalOLP.NormalModalLogic

universe u

/-- Propositional modal formulas over a type of atoms. -/
inductive Formula (Atom : Type u) : Type u where
  | atom : Atom → Formula Atom
  | falsum : Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  | box : Formula Atom → Formula Atom
  deriving DecidableEq

namespace Formula

variable {Atom : Type u}

/-- Negation, defined from implication and falsum. -/
def neg (φ : Formula Atom) : Formula Atom := .imp φ .falsum

/-- The truth constant, defined from implication and falsum. -/
def verum : Formula Atom := .imp .falsum .falsum

/-- Disjunction, defined in the usual implication basis. -/
def or (φ ψ : Formula Atom) : Formula Atom := .imp (neg φ) ψ

/-- Conjunction, defined in the usual implication basis. -/
def and (φ ψ : Formula Atom) : Formula Atom := neg (.imp φ (neg ψ))

/-- Possibility, defined as the dual of necessity. -/
def diamond (φ : Formula Atom) : Formula Atom := neg (.box (neg φ))

@[simp] theorem neg_eq (φ : Formula Atom) : neg φ = .imp φ .falsum := rfl

@[simp] theorem verum_eq : (verum : Formula Atom) = .imp .falsum .falsum := rfl

@[simp] theorem or_eq (φ ψ : Formula Atom) : or φ ψ = .imp (neg φ) ψ := rfl

@[simp] theorem and_eq (φ ψ : Formula Atom) : and φ ψ = neg (.imp φ (neg ψ)) := rfl

@[simp] theorem diamond_eq (φ : Formula Atom) : diamond φ = neg (.box (neg φ)) := rfl

end Formula

end FormalOLP.NormalModalLogic

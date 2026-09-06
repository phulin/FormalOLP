import FormalOLP.PropositionalLogic.Syntax
import Mathlib.Data.Set.Lattice.Bounded

/-!
# Classical propositional semantics

This module follows the Open Logic Text's valuation, satisfaction, and
semantic-entailment definitions in
`OpenLogic/content/propositional-logic/syntax-and-semantics/valuations-sat.tex`
and `semantic-notions.tex`.  A valuation assigns a proposition to each atom;
the recursive `Evaluate` function gives the corresponding truth conditions.
Contexts are sets of formulas, so `Entails` has exactly the textbook
all-valuations scope.

The definitions are native and do not import Lean Pool.  The natural
deduction soundness theorem is in `FormalOLP.ProofTheory.NaturalDeduction`.
-/

namespace FormalOLP.PropositionalLogic

universe u

/-- A classical valuation assigns a truth proposition to each atom. -/
abbrev Valuation (Atom : Type u) := Atom → Prop

/-- Truth-functional evaluation of a formula under a valuation. -/
def Evaluate (v : Valuation Atom) : Formula Atom → Prop
  | .atom a => v a
  | .falsum => False
  | .and φ ψ => Evaluate v φ ∧ Evaluate v ψ
  | .or φ ψ => Evaluate v φ ∨ Evaluate v ψ
  | .imp φ ψ => Evaluate v φ → Evaluate v ψ

namespace Evaluate

variable {Atom : Type u} (v : Valuation Atom)

@[simp] theorem atom (a : Atom) : Evaluate v (.atom a) ↔ v a := Iff.rfl

@[simp] theorem falsum : ¬Evaluate v (.falsum : Formula Atom) := by
  simp [Evaluate]

@[simp] theorem and (φ ψ : Formula Atom) :
    Evaluate v (.and φ ψ) ↔ Evaluate v φ ∧ Evaluate v ψ := Iff.rfl

@[simp] theorem or (φ ψ : Formula Atom) :
    Evaluate v (.or φ ψ) ↔ Evaluate v φ ∨ Evaluate v ψ := Iff.rfl

@[simp] theorem imp (φ ψ : Formula Atom) :
    Evaluate v (.imp φ ψ) ↔ (Evaluate v φ → Evaluate v ψ) := Iff.rfl

theorem neg (φ : Formula Atom) :
    Evaluate v (Formula.neg φ) ↔ ¬Evaluate v φ := by
  rfl

@[simp] theorem verum : Evaluate v (Formula.verum : Formula Atom) := by
  simp [Formula.verum, Evaluate]

end Evaluate

/-- Satisfaction of one formula by a valuation. -/
abbrev Satisfies (v : Valuation Atom) (φ : Formula Atom) : Prop := Evaluate v φ

/-- Satisfaction of every formula in a context. -/
def SatisfiesContext (v : Valuation Atom) (Γ : Set (Formula Atom)) : Prop :=
  ∀ ⦃φ⦄, φ ∈ Γ → Satisfies v φ

/-- Semantic entailment of a formula by a context. -/
def Entails (Γ : Set (Formula Atom)) (φ : Formula Atom) : Prop :=
  ∀ v, SatisfiesContext v Γ → Satisfies v φ

/-- Satisfiability of a context. -/
def Satisfiable (Γ : Set (Formula Atom)) : Prop :=
  ∃ v, SatisfiesContext v Γ

/-- A formula is a tautology when the empty context entails it. -/
def Tautology (φ : Formula Atom) : Prop := Entails (∅ : Set (Formula Atom)) φ

theorem satisfiesContext_insert_iff {v : Valuation Atom} {Γ : Set (Formula Atom)}
    {φ : Formula Atom} :
    SatisfiesContext v (insert φ Γ) ↔ Satisfies v φ ∧ SatisfiesContext v Γ := by
  constructor
  · intro h
    exact ⟨h (by simp), fun ψ hψ => h (by simp [hψ])⟩
  · rintro ⟨hφ, hΓ⟩ ψ hψ
    have hψ' : ψ = φ ∨ ψ ∈ Γ := by simpa using hψ
    rcases hψ' with rfl | hψ
    · exact hφ
    · exact hΓ hψ

theorem satisfiesContext_union_iff {v : Valuation Atom}
    {Γ Δ : Set (Formula Atom)} :
    SatisfiesContext v (Γ ∪ Δ) ↔ SatisfiesContext v Γ ∧ SatisfiesContext v Δ := by
  constructor
  · intro h
    exact ⟨fun ψ hψ => h (Set.mem_union_left Δ hψ),
      fun ψ hψ => h (Set.mem_union_right Γ hψ)⟩
  · rintro ⟨hΓ, hΔ⟩ ψ hψ
    change ψ ∈ Γ ∨ ψ ∈ Δ at hψ
    rcases hψ with hψ | hψ
    · exact hΓ hψ
    · exact hΔ hψ

theorem satisfiesContext_mono {v : Valuation Atom} {Γ Δ : Set (Formula Atom)}
    (hΓΔ : Γ ⊆ Δ) (hΔ : SatisfiesContext v Δ) :
    SatisfiesContext v Γ := by
  intro φ hφ
  exact hΔ (hΓΔ hφ)

theorem entails_of_mem {Γ : Set (Formula Atom)} {φ : Formula Atom}
    (hφ : φ ∈ Γ) : Entails Γ φ := by
  intro v hΓ
  exact hΓ hφ

theorem entails_mono {Γ Δ : Set (Formula Atom)} {φ : Formula Atom}
    (hΓΔ : Γ ⊆ Δ) (hΓ : Entails Γ φ) : Entails Δ φ := by
  intro v hΔ
  exact hΓ v (satisfiesContext_mono hΓΔ hΔ)

theorem entails_empty_iff_tautology {φ : Formula Atom} :
    Entails (∅ : Set (Formula Atom)) φ ↔ Tautology φ := Iff.rfl

theorem entails_modus_ponens {Γ : Set (Formula Atom)} {φ ψ : Formula Atom}
    (hφ : Entails Γ φ) (hImp : Entails Γ (.imp φ ψ)) :
    Entails Γ ψ := by
  intro v hΓ
  exact hImp v hΓ (hφ v hΓ)

theorem entails_deduction {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
    Entails (insert φ Γ) ψ ↔ Entails Γ (.imp φ ψ) := by
  constructor
  · intro h v hΓ hφ
    exact h v (satisfiesContext_insert_iff.mpr ⟨hφ, hΓ⟩)
  · intro h v hInsert
    have hφ : Satisfies v φ := hInsert (Set.mem_insert φ Γ)
    have hΓ : SatisfiesContext v Γ :=
      satisfiesContext_mono (Set.subset_insert φ Γ) hInsert
    exact h v hΓ hφ

end FormalOLP.PropositionalLogic

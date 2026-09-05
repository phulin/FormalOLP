import Mathlib.ModelTheory.Satisfiability

/-!
# Semantic notions for first-order logic

This file records the first semantic API for the Open Logic Text's
first-order logic chapter.  The definitions are deliberately thin wrappers
around Mathlib's first-order syntax and semantics: a theory entails a sentence
when every nonempty model of the theory realizes that sentence.

The OLP source for this chain is
`OpenLogic/content/first-order-logic/syntax-and-semantics/semantic-notions.tex`.
The source develops validity, entailment, satisfiability, entailment by an
unsatisfiable negation, monotonicity, and the semantic deduction theorem.
This module formalizes the latter three links and the basic membership link;
proof systems and completeness remain separate future interfaces.
-/

namespace FormalOLP.FirstOrderLogic

open FirstOrder

namespace SemanticNotions

universe u v w

variable {L : Language.{u, v}}

/-- Semantic consequence of a sentence from a first-order theory.

The superscript-free definition follows the OLP convention that models are
nonempty.  Mathlib's `ModelsBoundedFormula` quantifies over its bundled
nonempty model type, while retaining the formula-level API for later work.
-/
abbrev SemanticallyEntails (T : L.Theory) (φ : L.Sentence) : Prop :=
  T ⊨ᵇ φ

/-- Satisfiability of a first-order theory by a nonempty structure. -/
abbrev Satisfiable (T : L.Theory) : Prop :=
  T.IsSatisfiable

theorem semantic_consequence_of_mem {T : L.Theory} {φ : L.Sentence} (hφ : φ ∈ T) :
    SemanticallyEntails T φ := by
  exact Language.Theory.models_sentence_of_mem hφ

theorem semantic_consequence_mono {T T' : L.Theory} {φ : L.Sentence}
    (hTT' : T ⊆ T') (hT : SemanticallyEntails T φ) :
    SemanticallyEntails T' φ := by
  change T ⊨ᵇ φ at hT
  change T' ⊨ᵇ φ
  rw [Language.Theory.models_sentence_iff] at hT ⊢
  intro M
  exact hT (M.subtheoryModel hTT')

/-- A theory entails a sentence exactly when adjoining its negation is unsatisfiable.

This is the OLP proposition `prop:entails-unsat`, and uses no completeness
assumption: it is a direct semantic equivalence.
-/
theorem semantic_consequence_iff_unsatisfiable_negation {T : L.Theory} {φ : L.Sentence} :
    SemanticallyEntails T φ ↔ ¬Satisfiable (T ∪ {φ.not}) := by
  exact Language.Theory.models_iff_not_satisfiable φ

/-- The semantic deduction theorem for adding one sentence to a theory. -/
theorem semantic_deduction_theorem {T : L.Theory} {φ ψ : L.Sentence} :
    SemanticallyEntails (T ∪ {φ}) ψ ↔ SemanticallyEntails T (φ.imp ψ) := by
  constructor
  · intro h
    change (T ∪ {φ}) ⊨ᵇ ψ at h
    change T ⊨ᵇ (φ.imp ψ)
    rw [Language.Theory.models_sentence_iff] at h ⊢
    intro M
    rw [Language.Sentence.realize_imp]
    intro hφ
    let _ : M ⊨ T ∪ {φ} := by
      exact Language.Theory.Model.union M.is_model ⟨fun χ hχ => by
        rw [Set.mem_singleton_iff.mp hχ]
        exact hφ⟩
    let M' : Language.Theory.ModelType (T ∪ {φ}) :=
      Language.Theory.ModelType.of _ M
    change (M : Type _) ⊨ ψ
    exact h M'
  · intro h
    change T ⊨ᵇ (φ.imp ψ) at h
    change (T ∪ {φ}) ⊨ᵇ ψ
    rw [Language.Theory.models_sentence_iff] at h ⊢
    intro M
    have hφ : M ⊨ φ := by
      exact Language.Theory.realize_sentence_of_mem (T ∪ {φ})
        (Set.mem_union_right T (Set.mem_singleton φ))
    have hImp : M ⊨ φ.imp ψ := h (M.subtheoryModel Set.subset_union_left)
    exact (Language.Sentence.realize_imp (M : Type _)).mp hImp hφ

end SemanticNotions

end FormalOLP.FirstOrderLogic

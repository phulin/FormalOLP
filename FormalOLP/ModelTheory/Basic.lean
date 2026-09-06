import FormalOLP.FirstOrderLogic

/-!
# Basic model-theory bridges

This file records the first native model-theory chain used by FormalOLP:
first-order isomorphisms preserve sentence truth, hence elementary
equivalence and theory models, and Mathlib's compactness theorem gives the
finite satisfiability criterion.  The declarations deliberately expose the
Mathlib notions rather than introducing a second semantics.
-/

namespace FormalOLP.ModelTheory

open FirstOrder

universe u v w w'

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- An isomorphism of two first-order structures, with its witness hidden. -/
abbrev Isomorphic : Prop := Nonempty (M ≃[L] N)

/-- The native Mathlib notion of agreement on all first-order sentences. -/
abbrev ElementarilyEquivalent : Prop := M ≅[L] N

theorem isomorphism_preserves_sentence (e : M ≃[L] N) (φ : L.Sentence) :
    M ⊨ φ ↔ N ⊨ φ := by
  exact FirstOrder.Language.StrongHomClass.realize_sentence e φ

theorem isomorphic_implies_elementarilyEquivalent (h : Isomorphic (L := L) (M := M)
    (N := N)) : ElementarilyEquivalent (L := L) (M := M) (N := N) := by
  exact FirstOrder.Language.StrongHomClass.elementarilyEquivalent h.some

theorem isomorphic_preserves_theory {T : L.Theory} (h : Isomorphic (L := L) (M := M)
    (N := N)) : M ⊨ T ↔ N ⊨ T := by
  exact (FirstOrder.Language.StrongHomClass.elementarilyEquivalent h.some).theory_model_iff

theorem elementary_equivalence_preserves_sentence
    (h : ElementarilyEquivalent (L := L) (M := M) (N := N)) (φ : L.Sentence) :
    M ⊨ φ ↔ N ⊨ φ := by
  exact h.realize_sentence φ

theorem elementary_equivalence_preserves_theory {T : L.Theory}
    (h : ElementarilyEquivalent (L := L) (M := M) (N := N)) :
    M ⊨ T ↔ N ⊨ T := by
  exact h.theory_model_iff

/-! ## Compactness -/

theorem compactness (T : L.Theory) :
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable := by
  exact Language.Theory.isSatisfiable_iff_isFinitelySatisfiable

theorem compactness_of_finite_satisfiability (T : L.Theory)
    (hT : T.IsFinitelySatisfiable) : T.IsSatisfiable := by
  exact compactness T |>.2 hT

end FormalOLP.ModelTheory

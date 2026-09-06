import FormalOLP.IntuitionisticLogic.Kripke

/-!
# Basic intuitionistic semantic soundness

This module proves the elementary intuitionistic axiom and rule instances
needed before a full derivation system is introduced.  The OLP source is the
relational-model definition and theorem `thm:soundness` in
`OpenLogic/content/intuitionistic-logic/soundness-completeness/soundness-nd.tex`;
the proofs below are new native proofs.

The proof targets correspond mathematically to Pool's
`LO.IntProp.Formula.Kripke.ValidOnModel.andElim₁`, `andElim₂`, `andInst₃`,
`orInst₁`, `orInst₂`, `orElim`, `imply₁`, `imply₂`, `mdp`, and `efq` in
`LeanPool/Incompleteness/Foundation/IntProp/Kripke/Basic.lean`.  No Pool
declaration is imported.
-/

namespace FormalOLP.IntuitionisticLogic

open FormalOLP.PropositionalLogic

universe u v

def axiomImply₁ (φ ψ : Formula Atom) : Formula Atom := .imp φ (.imp ψ φ)

def axiomImply₂ (φ ψ χ : Formula Atom) : Formula Atom :=
  .imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ))

def axiomAndElimLeft (φ ψ : Formula Atom) : Formula Atom := .imp (.and φ ψ) φ

def axiomAndElimRight (φ ψ : Formula Atom) : Formula Atom := .imp (.and φ ψ) ψ

def axiomAndIntro (φ ψ : Formula Atom) : Formula Atom := .imp φ (.imp ψ (.and φ ψ))

def axiomOrIntroLeft (φ ψ : Formula Atom) : Formula Atom := .imp φ (.or φ ψ)

def axiomOrIntroRight (φ ψ : Formula Atom) : Formula Atom := .imp ψ (.or φ ψ)

def axiomEfq (φ : Formula Atom) : Formula Atom := .imp .falsum φ

theorem model_valid_axiomImply₁ (M : Model Atom) (φ ψ : Formula Atom) :
    Model.Valid M (axiomImply₁ φ ψ) := by
  intro x y _ hφ z hyz _
  exact forces_hereditary hyz hφ

theorem model_valid_axiomImply₂ (M : Model Atom) (φ ψ χ : Formula Atom) :
    Model.Valid M (axiomImply₂ φ ψ χ) := by
  intro x y _ hφψ z hyz hφψ' w hzw hφ
  exact hφψ (M.rel_trans hyz hzw) hφ (M.rel_refl w) (hφψ' hzw hφ)

theorem model_valid_axiomAndElimLeft (M : Model Atom) (φ ψ : Formula Atom) :
    Model.Valid M (axiomAndElimLeft φ ψ) := by
  intro x y _ hAnd
  exact hAnd.1

theorem model_valid_axiomAndElimRight (M : Model Atom) (φ ψ : Formula Atom) :
    Model.Valid M (axiomAndElimRight φ ψ) := by
  intro x y _ hAnd
  exact hAnd.2

theorem model_valid_axiomAndIntro (M : Model Atom) (φ ψ : Formula Atom) :
    Model.Valid M (axiomAndIntro φ ψ) := by
  intro x y _ hφ z hyz hψ
  exact ⟨forces_hereditary hyz hφ, hψ⟩

theorem model_valid_axiomOrIntroLeft (M : Model Atom) (φ ψ : Formula Atom) :
    Model.Valid M (axiomOrIntroLeft φ ψ) := by
  intro x y _ hφ
  exact Or.inl hφ

theorem model_valid_axiomOrIntroRight (M : Model Atom) (φ ψ : Formula Atom) :
    Model.Valid M (axiomOrIntroRight φ ψ) := by
  intro x y _ hψ
  exact Or.inr hψ

theorem model_valid_axiomEfq (M : Model Atom) (φ : Formula Atom) :
    Model.Valid M (axiomEfq φ) := by
  intro x _ _ hFalse
  exact False.elim hFalse

theorem model_valid_orElim (M : Model Atom) (φ ψ χ : Formula Atom) :
    Model.Valid M (.imp (.imp φ χ) (.imp (.imp ψ χ) (.imp (.or φ ψ) χ))) := by
  intro x y _ hφχ z hyz hψχ w hzw hOr
  cases hOr with
  | inl hφ => exact hφχ (M.rel_trans hyz hzw) hφ
  | inr hψ => exact hψχ hzw hψ

theorem model_valid_mdp {φ ψ : Formula Atom}
    (hImp : Model.Valid M (.imp φ ψ)) (hφ : Model.Valid M φ) :
    Model.Valid M ψ := by
  intro x
  exact hImp x (M.rel_refl x) (hφ x)

theorem frame_valid_of_model_valid {F : Frame} {φ : Formula Atom}
    (h : ∀ V : Valuation F Atom, Model.Valid (Model.fromFrame F V) φ) :
    Frame.Valid F φ := h

theorem frame_valid_axiomImply₁ (F : Frame) (φ ψ : Formula Atom) :
    Frame.Valid F (axiomImply₁ φ ψ) := by
  intro V
  exact model_valid_axiomImply₁ (Model.fromFrame F V) φ ψ

theorem frame_valid_axiomImply₂ (F : Frame) (φ ψ χ : Formula Atom) :
    Frame.Valid F (axiomImply₂ φ ψ χ) := by
  intro V
  exact model_valid_axiomImply₂ (Model.fromFrame F V) φ ψ χ

theorem frame_valid_axiomAndElimLeft (F : Frame) (φ ψ : Formula Atom) :
    Frame.Valid F (axiomAndElimLeft φ ψ) := by
  intro V
  exact model_valid_axiomAndElimLeft (Model.fromFrame F V) φ ψ

theorem frame_valid_axiomAndElimRight (F : Frame) (φ ψ : Formula Atom) :
    Frame.Valid F (axiomAndElimRight φ ψ) := by
  intro V
  exact model_valid_axiomAndElimRight (Model.fromFrame F V) φ ψ

theorem frame_valid_axiomAndIntro (F : Frame) (φ ψ : Formula Atom) :
    Frame.Valid F (axiomAndIntro φ ψ) := by
  intro V
  exact model_valid_axiomAndIntro (Model.fromFrame F V) φ ψ

theorem frame_valid_axiomOrIntroLeft (F : Frame) (φ ψ : Formula Atom) :
    Frame.Valid F (axiomOrIntroLeft φ ψ) := by
  intro V
  exact model_valid_axiomOrIntroLeft (Model.fromFrame F V) φ ψ

theorem frame_valid_axiomOrIntroRight (F : Frame) (φ ψ : Formula Atom) :
    Frame.Valid F (axiomOrIntroRight φ ψ) := by
  intro V
  exact model_valid_axiomOrIntroRight (Model.fromFrame F V) φ ψ

theorem frame_valid_axiomEfq (F : Frame) (φ : Formula Atom) :
    Frame.Valid F (axiomEfq φ) := by
  intro V
  exact model_valid_axiomEfq (Model.fromFrame F V) φ

theorem frame_valid_orElim (F : Frame) (φ ψ χ : Formula Atom) :
    Frame.Valid F (.imp (.imp φ χ) (.imp (.imp ψ χ) (.imp (.or φ ψ) χ))) := by
  intro V
  exact model_valid_orElim (Model.fromFrame F V) φ ψ χ

theorem frame_valid_mdp {F : Frame} {φ ψ : Formula Atom}
    (hImp : Frame.Valid F (.imp φ ψ)) (hφ : Frame.Valid F φ) :
    Frame.Valid F ψ := by
  intro V
  exact model_valid_mdp (hImp V) (hφ V)

end FormalOLP.IntuitionisticLogic

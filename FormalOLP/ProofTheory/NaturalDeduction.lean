import FormalOLP.PropositionalLogic.Semantics
import Mathlib.Data.Set.Finite.Basic

/-!
# Propositional natural deduction

This module formalizes the sequent-style propositional natural deduction
rules `N2c` from
`OpenLogic/content/proof-theory/natural-deduction/rules-N2.tex` and
`sequent-natural-deduction.tex`.  A derivation is indexed by its set of open
assumptions and its conclusion.  Implication introduction and classical
reductio therefore discharge exactly the assumptions shown in the source
calculus; the other rules combine the premise contexts by union.

The constructors through explosion are the shared intuitionistic core.
`raa` is the explicit classical absurdity rule from `N2c`; omitting that
constructor gives the corresponding intuitionistic rule fragment.  The
soundness proof instantiates the classical valuation semantics rather than
assuming validity of any rule.
-/

namespace FormalOLP.ProofTheory

open FormalOLP.PropositionalLogic

universe u

variable {Atom : Type u}

/-- A propositional natural-deduction derivation with open assumptions `Γ`. -/
inductive Derivation : Set (Formula Atom) → Formula Atom → Prop where
  | assumption {Γ : Set (Formula Atom)} {φ : Formula Atom} :
      φ ∈ Γ → Derivation Γ φ
  | impIntro {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      Derivation (insert φ Γ) ψ → Derivation Γ (.imp φ ψ)
  | impElim {Γ Δ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      Derivation Γ (.imp φ ψ) → Derivation Δ φ → Derivation (Γ ∪ Δ) ψ
  | andIntro {Γ Δ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      Derivation Γ φ → Derivation Δ ψ → Derivation (Γ ∪ Δ) (.and φ ψ)
  | andElimLeft {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      Derivation Γ (.and φ ψ) → Derivation Γ φ
  | andElimRight {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      Derivation Γ (.and φ ψ) → Derivation Γ ψ
  | orIntroLeft {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      Derivation Γ φ → Derivation Γ (.or φ ψ)
  | orIntroRight {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      Derivation Γ ψ → Derivation Γ (.or φ ψ)
  | orElim {Γ Δ Θ : Set (Formula Atom)} {φ ψ χ : Formula Atom} :
      Derivation Γ (.or φ ψ) →
      Derivation (insert φ Δ) χ →
      Derivation (insert ψ Θ) χ →
      Derivation (Γ ∪ Δ ∪ Θ) χ
  | falseElim {Γ : Set (Formula Atom)} {φ : Formula Atom} :
      Derivation Γ .falsum → Derivation Γ φ
  | raa {Γ : Set (Formula Atom)} {φ : Formula Atom} :
      Derivation (insert (Formula.neg φ) Γ) .falsum → Derivation Γ φ

namespace Derivation

theorem subset_insert_mono {Γ Δ : Set (Formula Atom)} {φ : Formula Atom}
    (hΓΔ : Γ ⊆ Δ) : insert φ Γ ⊆ insert φ Δ := by
  intro ψ hψ
  have hψ' : ψ = φ ∨ ψ ∈ Γ := by simpa using hψ
  rcases hψ' with rfl | hψ
  · simp
  · exact Set.mem_insert_of_mem φ (hΓΔ hψ)

theorem subset_union_left {Γ Δ Θ : Set (Formula Atom)}
    (h : Γ ⊆ Δ) : Γ ⊆ Δ ∪ Θ := by
  intro φ hφ
  exact Set.mem_union_left Θ (h hφ)

theorem subset_union_right {Γ Δ Θ : Set (Formula Atom)}
    (h : Γ ⊆ Θ) : Γ ⊆ Δ ∪ Θ := by
  intro φ hφ
  exact Set.mem_union_right Δ (h hφ)

theorem weakening {Γ Δ : Set (Formula Atom)} {φ : Formula Atom}
    (hΓΔ : Γ ⊆ Δ) (d : Derivation Γ φ) : Derivation Δ φ := by
  induction d generalizing Δ with
  | assumption hmem =>
      exact .assumption (hΓΔ hmem)
  | impIntro d ih =>
      apply Derivation.impIntro
      exact ih (subset_insert_mono hΓΔ)
  | @impElim Γ₁ Δ₁ φ ψ dImp dArg ihImp ihArg =>
      have hImp : Γ₁ ⊆ Δ := by
        intro ψ hψ
        exact hΓΔ (Set.mem_union_left _ hψ)
      have hArg : Δ₁ ⊆ Δ := by
        intro ψ hψ
        exact hΓΔ (Set.mem_union_right _ hψ)
      simpa only [Set.union_self] using
        (Derivation.impElim (ihImp hImp) (ihArg hArg))
  | @andIntro Γ₁ Δ₁ φ ψ dLeft dRight ihLeft ihRight =>
      have hLeft : Γ₁ ⊆ Δ := by
        intro ψ hψ
        exact hΓΔ (Set.mem_union_left _ hψ)
      have hRight : Δ₁ ⊆ Δ := by
        intro ψ hψ
        exact hΓΔ (Set.mem_union_right _ hψ)
      simpa only [Set.union_self] using
        (Derivation.andIntro (ihLeft hLeft) (ihRight hRight))
  | andElimLeft d ih =>
      exact .andElimLeft (ih hΓΔ)
  | andElimRight d ih =>
      exact .andElimRight (ih hΓΔ)
  | orIntroLeft d ih =>
      exact .orIntroLeft (ih hΓΔ)
  | orIntroRight d ih =>
      exact .orIntroRight (ih hΓΔ)
  | @orElim Γ₁ Δ₁ Θ₁ φ ψ χ dOr dLeft dRight ihOr ihLeft ihRight =>
      have hOr : Γ₁ ⊆ Δ := by
        intro ψ hψ
        exact hΓΔ (Set.mem_union_left Θ₁ (Set.mem_union_left Δ₁ hψ))
      have hLeft : insert φ Δ₁ ⊆ insert φ Δ := by
        exact subset_insert_mono (φ := φ) (by
          intro ψ hψ
          exact hΓΔ (Set.mem_union_left Θ₁ (Set.mem_union_right Γ₁ hψ)))
      have hRight : insert ψ Θ₁ ⊆ insert ψ Δ := by
        exact subset_insert_mono (φ := ψ) (by
          intro ψ hψ
          exact hΓΔ (Set.mem_union_right (Γ₁ ∪ Δ₁) hψ))
      simpa only [Set.union_self] using
        (Derivation.orElim (ihOr hOr) (ihLeft hLeft) (ihRight hRight))
  | falseElim d ih =>
      exact .falseElim (ih hΓΔ)
  | raa d ih =>
      exact .raa (ih (subset_insert_mono hΓΔ))

theorem weakening_of_subset {Γ Δ : Set (Formula Atom)} {φ : Formula Atom}
    (d : Derivation Γ φ) (hΓΔ : Γ ⊆ Δ) : Derivation Δ φ :=
  weakening hΓΔ d

/-- Remove a discharged formula from a finite support of a premise. -/
theorem remove_discharged_support {Γ Δ : Set (Formula Atom)}
    {φ ψ : Formula Atom} (hΔfin : Δ.Finite) (hΔ : Δ ⊆ insert φ Γ)
    (d : Derivation Δ ψ) :
    ∃ Δ' : Set (Formula Atom), Δ'.Finite ∧ Δ' ⊆ Γ ∧
      Derivation (insert φ Δ') ψ := by
  let Δ' : Set (Formula Atom) := Δ \ {φ}
  have hΔ'fin : Δ'.Finite := by
    exact hΔfin.sdiff
  have hΔ'sub : Δ' ⊆ Γ := by
    intro χ hχ
    have hχ' : χ ∈ Δ ∧ χ ∉ ({φ} : Set (Formula Atom)) := by
      simpa [Δ'] using hχ
    have hχinsert : χ = φ ∨ χ ∈ Γ := by
      simpa using hΔ hχ'.1
    rcases hχinsert with rfl | hχΓ
    · exact (hχ'.2 (by simp)).elim
    · exact hχΓ
  have hΔsub : Δ ⊆ insert φ Δ' := by
    intro χ hχ
    by_cases hχφ : χ = φ
    · subst χ
      exact Set.mem_insert φ Δ'
    · apply Set.mem_insert_of_mem φ
      change χ ∈ Δ \ {φ}
      exact ⟨hχ, by simpa using hχφ⟩
  exact ⟨Δ', hΔ'fin, hΔ'sub, weakening hΔsub d⟩

/-- Every derivation has a finite set of open assumptions as a support. -/
theorem finite_support {Γ : Set (Formula Atom)} {φ : Formula Atom}
    (d : Derivation Γ φ) :
    ∃ Δ : Set (Formula Atom), Δ.Finite ∧ Δ ⊆ Γ ∧ Derivation Δ φ := by
  induction d with
  | @assumption Γ₁ φ₁ hmem =>
      have hsingle : ({φ₁} : Set (Formula Atom)) ⊆ Γ₁ := by
        intro ψ hψ
        have hψ' : ψ = φ₁ := by simpa using hψ
        simpa [hψ'] using hmem
      exact ⟨{φ₁}, Set.finite_singleton φ₁, hsingle,
        Derivation.assumption (by simp)⟩
  | @impIntro Γ₁ φ₁ ψ₁ d ih =>
      rcases ih with ⟨Δ, hΔfin, hΔ, dΔ⟩
      rcases remove_discharged_support hΔfin hΔ dΔ with
        ⟨Δ', hΔ'fin, hΔ'sub, dΔ'⟩
      exact ⟨Δ', hΔ'fin, hΔ'sub, Derivation.impIntro dΔ'⟩
  | @impElim Γ₁ Δ₁ φ₁ ψ₁ dImp dArg ihImp ihArg =>
      rcases ihImp with ⟨Γ', hΓ'fin, hΓ', dImp'⟩
      rcases ihArg with ⟨Δ', hΔ'fin, hΔ', dArg'⟩
      have hfin : (Γ' ∪ Δ').Finite := hΓ'fin.union hΔ'fin
      have hsub : Γ' ∪ Δ' ⊆ Γ₁ ∪ Δ₁ := by
        intro χ hχ
        change χ ∈ Γ' ∨ χ ∈ Δ' at hχ
        change χ ∈ Γ₁ ∨ χ ∈ Δ₁
        rcases hχ with hχ | hχ
        · exact Or.inl (hΓ' hχ)
        · exact Or.inr (hΔ' hχ)
      exact ⟨Γ' ∪ Δ', hfin, hsub, Derivation.impElim dImp' dArg'⟩
  | @andIntro Γ₁ Δ₁ φ₁ ψ₁ dLeft dRight ihLeft ihRight =>
      rcases ihLeft with ⟨Γ', hΓ'fin, hΓ', dLeft'⟩
      rcases ihRight with ⟨Δ', hΔ'fin, hΔ', dRight'⟩
      have hfin : (Γ' ∪ Δ').Finite := hΓ'fin.union hΔ'fin
      have hsub : Γ' ∪ Δ' ⊆ Γ₁ ∪ Δ₁ := by
        intro χ hχ
        change χ ∈ Γ' ∨ χ ∈ Δ' at hχ
        change χ ∈ Γ₁ ∨ χ ∈ Δ₁
        rcases hχ with hχ | hχ
        · exact Or.inl (hΓ' hχ)
        · exact Or.inr (hΔ' hχ)
      exact ⟨Γ' ∪ Δ', hfin, hsub, Derivation.andIntro dLeft' dRight'⟩
  | @andElimLeft Γ₁ φ₁ ψ₁ d ih =>
      rcases ih with ⟨Δ, hΔfin, hΔ, dΔ⟩
      exact ⟨Δ, hΔfin, hΔ, Derivation.andElimLeft dΔ⟩
  | @andElimRight Γ₁ φ₁ ψ₁ d ih =>
      rcases ih with ⟨Δ, hΔfin, hΔ, dΔ⟩
      exact ⟨Δ, hΔfin, hΔ, Derivation.andElimRight dΔ⟩
  | @orIntroLeft Γ₁ φ₁ ψ₁ d ih =>
      rcases ih with ⟨Δ, hΔfin, hΔ, dΔ⟩
      exact ⟨Δ, hΔfin, hΔ, Derivation.orIntroLeft dΔ⟩
  | @orIntroRight Γ₁ φ₁ ψ₁ d ih =>
      rcases ih with ⟨Δ, hΔfin, hΔ, dΔ⟩
      exact ⟨Δ, hΔfin, hΔ, Derivation.orIntroRight dΔ⟩
  | @orElim Γ₁ Δ₁ Θ₁ φ₁ ψ₁ χ dOr dLeft dRight ihOr ihLeft ihRight =>
      rcases ihOr with ⟨Γ', hΓ'fin, hΓ', dOr'⟩
      rcases ihLeft with ⟨Δ', hΔ'fin, hΔ', dLeft'⟩
      rcases ihRight with ⟨Θ', hΘ'fin, hΘ', dRight'⟩
      rcases remove_discharged_support hΔ'fin hΔ' dLeft' with
        ⟨Δ'', hΔ''fin, hΔ''sub, dLeft''⟩
      rcases remove_discharged_support hΘ'fin hΘ' dRight' with
        ⟨Θ'', hΘ''fin, hΘ''sub, dRight''⟩
      have hfin : (Γ' ∪ Δ'' ∪ Θ'').Finite :=
        (hΓ'fin.union hΔ''fin).union hΘ''fin
      have hsub : Γ' ∪ Δ'' ∪ Θ'' ⊆ Γ₁ ∪ Δ₁ ∪ Θ₁ := by
        intro ξ hξ
        change (ξ ∈ Γ' ∨ ξ ∈ Δ'') ∨ ξ ∈ Θ'' at hξ
        change (ξ ∈ Γ₁ ∨ ξ ∈ Δ₁) ∨ ξ ∈ Θ₁
        rcases hξ with hξ | hξ
        · rcases hξ with hξ | hξ
          · exact Or.inl (Or.inl (hΓ' hξ))
          · exact Or.inl (Or.inr (hΔ''sub hξ))
        · exact Or.inr (hΘ''sub hξ)
      exact ⟨Γ' ∪ Δ'' ∪ Θ'', hfin, hsub,
        Derivation.orElim dOr' dLeft'' dRight''⟩
  | @falseElim Γ₁ φ₁ d ih =>
      rcases ih with ⟨Δ, hΔfin, hΔ, dΔ⟩
      exact ⟨Δ, hΔfin, hΔ, Derivation.falseElim dΔ⟩
  | @raa Γ₁ φ₁ d ih =>
      rcases ih with ⟨Δ, hΔfin, hΔ, dΔ⟩
      rcases remove_discharged_support hΔfin hΔ dΔ with
        ⟨Δ', hΔ'fin, hΔ'sub, dΔ'⟩
      exact ⟨Δ', hΔ'fin, hΔ'sub, Derivation.raa dΔ'⟩

/-! ## Semantic soundness -/

theorem soundness {Γ : Set (Formula Atom)} {φ : Formula Atom}
    (d : Derivation Γ φ) : Entails Γ φ := by
  induction d with
  | assumption hmem =>
      exact entails_of_mem hmem
  | impIntro d ih =>
      intro v hΓ hφ
      exact ih v (satisfiesContext_insert_iff.mpr ⟨hφ, hΓ⟩)
  | impElim dImp dArg ihImp ihArg =>
      intro v hUnion
      have hContexts := satisfiesContext_union_iff.mp hUnion
      exact ihImp v hContexts.1 (ihArg v hContexts.2)
  | andIntro dLeft dRight ihLeft ihRight =>
      intro v hUnion
      have hContexts := satisfiesContext_union_iff.mp hUnion
      exact ⟨ihLeft v hContexts.1, ihRight v hContexts.2⟩
  | andElimLeft d ih =>
      intro v hΓ
      exact (ih v hΓ).1
  | andElimRight d ih =>
      intro v hΓ
      exact (ih v hΓ).2
  | orIntroLeft d ih =>
      intro v hΓ
      exact Or.inl (ih v hΓ)
  | orIntroRight d ih =>
      intro v hΓ
      exact Or.inr (ih v hΓ)
  | orElim dOr dLeft dRight ihOr ihLeft ihRight =>
      intro v hUnion
      have hOuter := satisfiesContext_union_iff.mp hUnion
      have hBranches := satisfiesContext_union_iff.mp hOuter.1
      have hOr := ihOr v hBranches.1
      cases hOr with
      | inl hφ =>
          exact ihLeft v (satisfiesContext_insert_iff.mpr ⟨hφ, hBranches.2⟩)
      | inr hψ =>
          exact ihRight v (satisfiesContext_insert_iff.mpr ⟨hψ, hOuter.2⟩)
  | falseElim d ih =>
      intro v hΓ
      exact False.elim (ih v hΓ)
  | @raa Γ₁ φ₁ d ih =>
      intro v hΓ
      by_cases hφ : Satisfies v φ₁
      · exact hφ
      · have hNeg : Satisfies v (Formula.neg φ₁) :=
          (Evaluate.neg v φ₁).mpr hφ
        exact False.elim (ih v (satisfiesContext_insert_iff.mpr ⟨hNeg, hΓ⟩))

theorem theorem_soundness {φ : Formula Atom}
    (d : Derivation (∅ : Set (Formula Atom)) φ) : Tautology φ :=
  soundness d

end Derivation

end FormalOLP.ProofTheory

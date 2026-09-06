import FormalOLP.IntuitionisticLogic.Kripke
import FormalOLP.ProofTheory.NaturalDeduction

/-!
# Intuitionistic natural deduction and Kripke soundness

The shared natural-deduction object is
`FormalOLP.ProofTheory.Derivation`.  Its contexts are sets of formulas and
its premise contexts are combined by union, as in the OLP sequent-style
natural-deduction rules.  The shared object also has the classical `raa`
constructor for the classical propositional development.  The separate
`IntuitionisticDerivation` below is a Type-valued proof tree containing
exactly the OLP intuitionistic rules and has an explicit `toDerivation`
embedding into that shared object;
there is no classical rule in this native calculus.

The soundness theorem is the theorem `thm:soundness` in
`OpenLogic/content/intuitionistic-logic/soundness-completeness/soundness-nd.tex`.
Its proof explicitly uses persistence of both assumptions and forced
formulas, including the discharged assumptions in implication introduction
and the two branches of disjunction elimination.
-/

namespace FormalOLP.IntuitionisticLogic

open FormalOLP.PropositionalLogic

universe u v

variable {Atom : Type u}

/-- The shared propositional derivation type used by this intuitionistic topic. -/
abbrev Derivation (Atom : Type u) := FormalOLP.ProofTheory.Derivation (Atom := Atom)

/-! The intuitionistic derivation object. -/
inductive IntuitionisticDerivation : Set (Formula Atom) → Formula Atom → Type u where
  | assumption {Γ : Set (Formula Atom)} {φ : Formula Atom} (h : φ ∈ Γ) :
      IntuitionisticDerivation Γ φ
  | impIntro {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      IntuitionisticDerivation (insert φ Γ) ψ →
        IntuitionisticDerivation Γ (.imp φ ψ)
  | impElim {Γ Δ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      IntuitionisticDerivation Γ (.imp φ ψ) →
      IntuitionisticDerivation Δ φ → IntuitionisticDerivation (Γ ∪ Δ) ψ
  | andIntro {Γ Δ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      IntuitionisticDerivation Γ φ → IntuitionisticDerivation Δ ψ →
        IntuitionisticDerivation (Γ ∪ Δ) (.and φ ψ)
  | andElimLeft {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      IntuitionisticDerivation Γ (.and φ ψ) → IntuitionisticDerivation Γ φ
  | andElimRight {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      IntuitionisticDerivation Γ (.and φ ψ) → IntuitionisticDerivation Γ ψ
  | orIntroLeft {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      IntuitionisticDerivation Γ φ → IntuitionisticDerivation Γ (.or φ ψ)
  | orIntroRight {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      IntuitionisticDerivation Γ ψ → IntuitionisticDerivation Γ (.or φ ψ)
  | orElim {Γ Δ Θ : Set (Formula Atom)} {φ ψ χ : Formula Atom} :
      IntuitionisticDerivation Γ (.or φ ψ) →
      IntuitionisticDerivation (insert φ Δ) χ →
      IntuitionisticDerivation (insert ψ Θ) χ →
        IntuitionisticDerivation (Γ ∪ Δ ∪ Θ) χ
  | falseElim {Γ : Set (Formula Atom)} {φ : Formula Atom} :
      IntuitionisticDerivation Γ .falsum → IntuitionisticDerivation Γ φ

namespace IntuitionisticDerivation

/-- Embed an intuitionistic derivation into the shared classical tree. -/
theorem toDerivation : {Γ : Set (Formula Atom)} → {φ : Formula Atom} →
    IntuitionisticDerivation Γ φ → FormalOLP.ProofTheory.Derivation Γ φ
  | _, _, .assumption h => .assumption h
  | _, _, .impIntro d => .impIntro (toDerivation d)
  | _, _, .impElim dImp dArg => .impElim (toDerivation dImp) (toDerivation dArg)
  | _, _, .andIntro dLeft dRight => .andIntro (toDerivation dLeft) (toDerivation dRight)
  | _, _, .andElimLeft d => .andElimLeft (toDerivation d)
  | _, _, .andElimRight d => .andElimRight (toDerivation d)
  | _, _, .orIntroLeft d => .orIntroLeft (toDerivation d)
  | _, _, .orIntroRight d => .orIntroRight (toDerivation d)
  | _, _, .orElim dOr dLeft dRight =>
      .orElim (toDerivation dOr) (toDerivation dLeft) (toDerivation dRight)
  | _, _, .falseElim d => .falseElim (toDerivation d)

end IntuitionisticDerivation

/-- A proof in the OLP intuitionistic natural-deduction calculus. -/
abbrev Proof (Γ : Set (Formula Atom)) (φ : Formula Atom) : Prop :=
  Nonempty (IntuitionisticDerivation Γ φ)

/-- A model forces every formula in a context at a world. -/
def ForcesContext (M : Model Atom) (Γ : Set (Formula Atom)) (x : M.World) : Prop :=
  ∀ ⦃φ⦄, φ ∈ Γ → Forces M x φ

theorem forcesContext_insert_iff {M : Model Atom} {Γ : Set (Formula Atom)}
    {φ : Formula Atom} {x : M.World} :
    ForcesContext M (insert φ Γ) x ↔
      Forces M x φ ∧ ForcesContext M Γ x := by
  constructor
  · intro h
    exact ⟨h (Set.mem_insert φ Γ),
      fun ψ hψ => h (Set.mem_insert_of_mem φ hψ)⟩
  · rintro ⟨hφ, hΓ⟩ ψ hψ
    have hψ' : ψ = φ ∨ ψ ∈ Γ := by simpa using hψ
    rcases hψ' with rfl | hψ
    · exact hφ
    · exact hΓ hψ

theorem forcesContext_union_iff {M : Model Atom}
    {Γ Δ : Set (Formula Atom)} {x : M.World} :
    ForcesContext M (Γ ∪ Δ) x ↔
      ForcesContext M Γ x ∧ ForcesContext M Δ x := by
  constructor
  · intro h
    exact ⟨fun ψ hψ => h (Set.mem_union_left Δ hψ),
      fun ψ hψ => h (Set.mem_union_right Γ hψ)⟩
  · rintro ⟨hΓ, hΔ⟩ ψ hψ
    rcases hψ with hψ | hψ
    · exact hΓ hψ
    · exact hΔ hψ

theorem forcesContext_mono {M : Model Atom} {Γ Δ : Set (Formula Atom)}
    {x : M.World} (hΓΔ : Γ ⊆ Δ) (hΔ : ForcesContext M Δ x) :
    ForcesContext M Γ x := by
  intro φ hφ
  exact hΔ (hΓΔ hφ)

theorem forcesContext_hereditary {M : Model Atom} {Γ : Set (Formula Atom)}
    {x y : M.World} (hxy : M.Rel x y) :
    ForcesContext M Γ x → ForcesContext M Γ y := by
  intro hΓ φ hφ
  exact forces_hereditary hxy (hΓ hφ)

theorem derivation_sound {Γ : Set (Formula Atom)} {φ : Formula Atom}
    (d : IntuitionisticDerivation Γ φ) :
    ∀ (M : Model Atom) (x : M.World),
      ForcesContext M Γ x → Forces M x φ := by
  induction d with
  | assumption hmem =>
      intro M x hΓ
      exact hΓ hmem
  | impIntro d ih =>
      intro M x hΓ y hxy hφ
      have hΓy : ForcesContext M _ y := forcesContext_hereditary hxy hΓ
      exact ih M y (forcesContext_insert_iff.mpr ⟨hφ, hΓy⟩)
  | impElim dImp dArg ihImp ihArg =>
      intro M x hΓ
      have hImpAtX : Forces M x (.imp _ _) :=
        ihImp M x (forcesContext_mono
          (fun ψ hψ => Set.mem_union_left _ hψ) hΓ)
      have hImp : Forces M x _ → Forces M x _ := hImpAtX (M.rel_refl x)
      have hArg : Forces M x _ :=
        ihArg M x (forcesContext_mono
          (fun ψ hψ => Set.mem_union_right _ hψ) hΓ)
      exact hImp hArg
  | andIntro dLeft dRight ihLeft ihRight =>
      intro M x hΓ
      have hLeft : Forces M x _ :=
        ihLeft M x (forcesContext_mono
          (fun ψ hψ => Set.mem_union_left _ hψ) hΓ)
      have hRight : Forces M x _ :=
        ihRight M x (forcesContext_mono
          (fun ψ hψ => Set.mem_union_right _ hψ) hΓ)
      exact ⟨hLeft, hRight⟩
  | andElimLeft d ih =>
      intro M x hΓ
      exact (ih M x hΓ).1
  | andElimRight d ih =>
      intro M x hΓ
      exact (ih M x hΓ).2
  | orIntroLeft d ih =>
      intro M x hΓ
      exact Or.inl (ih M x hΓ)
  | orIntroRight d ih =>
      intro M x hΓ
      exact Or.inr (ih M x hΓ)
  | orElim dOr dLeft dRight ihOr ihLeft ihRight =>
      intro M x hΓ
      have hOr : Forces M x _ :=
        ihOr M x (forcesContext_mono
          (fun ψ hψ => Set.mem_union_left _ (Set.mem_union_left _ hψ)) hΓ)
      cases hOr with
      | inl hφ =>
          exact ihLeft M x (forcesContext_insert_iff.mpr ⟨hφ,
            forcesContext_mono
              (fun ψ hψ => Set.mem_union_left _ (Set.mem_union_right _ hψ)) hΓ⟩)
      | inr hψ =>
          exact ihRight M x (forcesContext_insert_iff.mpr ⟨hψ,
            forcesContext_mono
              (fun χ hχ => Set.mem_union_right _ hχ) hΓ⟩)
  | falseElim d ih =>
      intro M x hΓ
      exact False.elim (ih M x hΓ)

theorem proof_sound {Γ : Set (Formula Atom)} {φ : Formula Atom}
    (p : Proof Γ φ) (M : Model Atom) (x : M.World)
    (hΓ : ForcesContext M Γ x) : Forces M x φ :=
  match p with
  | ⟨d⟩ => derivation_sound d M x hΓ

end FormalOLP.IntuitionisticLogic

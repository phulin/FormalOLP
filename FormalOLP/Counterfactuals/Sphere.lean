import Mathlib.Data.Set.Basic

/-!
# Selection semantics for counterfactuals

This is an explicitly selected closest-world variant of the sphere clause in
`OpenLogic/content/counterfactuals/minimal-change-semantics/sphere-models.tex`.
For each world and antecedent proposition, `Closest` selects the worlds in
the chosen innermost antecedent-admitting sphere.  The source sphere model
allows an infinite descending system with no innermost sphere; this API adds
the Stalnaker-style limit condition that every nonempty antecedent has a
nonempty selection.  It also records the selection-subset condition and
strong centering.  The latter yields centered conditional modus ponens.
The module proves only the closest-world principles listed here; it makes no
material-implication or counterfactual-transitivity identification.
-/

namespace FormalOLP.Counterfactuals

universe u

inductive Formula (Atom : Type u) : Type u where
  | atom : Atom → Formula Atom
  | falsum : Formula Atom
  | and : Formula Atom → Formula Atom → Formula Atom
  | or : Formula Atom → Formula Atom → Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  | counterfactual : Formula Atom → Formula Atom → Formula Atom

namespace Formula

variable {Atom : Type u}

def neg (φ : Formula Atom) : Formula Atom := .imp φ .falsum

def verum : Formula Atom := .imp .falsum .falsum

end Formula

/-- A closest-world model with success and strong centering. -/
structure Model (Atom : Type u) where
  World : Type u
  world_nonempty : Nonempty World
  Valuation : World → Atom → Prop
  Closest : World → Set World → Set World
  closest_subset : ∀ w A, Closest w A ⊆ A
  closest_success : ∀ w A, A.Nonempty → (Closest w A).Nonempty
  centered : ∀ w A, w ∈ A → Closest w A = {w}

def Satisfies (M : Model Atom) : M.World → Formula Atom → Prop
  | w, .atom a => M.Valuation w a
  | _, .falsum => False
  | w, .and φ ψ => Satisfies M w φ ∧ Satisfies M w ψ
  | w, .or φ ψ => Satisfies M w φ ∨ Satisfies M w ψ
  | w, .imp φ ψ => Satisfies M w φ → Satisfies M w ψ
  | w, .counterfactual φ ψ =>
      ∀ v ∈ M.Closest w {u | Satisfies M u φ}, Satisfies M v ψ

namespace Satisfies

variable {Atom : Type u} {M : Model Atom} {w : M.World}

@[simp] theorem atom (a : Atom) : Satisfies M w (.atom a) ↔ M.Valuation w a := Iff.rfl

@[simp] theorem falsum : ¬Satisfies M w (.falsum : Formula Atom) := by
  simp [Satisfies]

@[simp] theorem and (φ ψ : Formula Atom) :
    Satisfies M w (.and φ ψ) ↔ Satisfies M w φ ∧ Satisfies M w ψ := Iff.rfl

@[simp] theorem or (φ ψ : Formula Atom) :
    Satisfies M w (.or φ ψ) ↔ Satisfies M w φ ∨ Satisfies M w ψ := Iff.rfl

@[simp] theorem imp (φ ψ : Formula Atom) :
    Satisfies M w (.imp φ ψ) ↔ (Satisfies M w φ → Satisfies M w ψ) := Iff.rfl

theorem neg (φ : Formula Atom) :
    Satisfies M w (Formula.neg φ) ↔ ¬Satisfies M w φ := Iff.rfl

end Satisfies

theorem conditional_identity (M : Model Atom) (w : M.World) (φ : Formula Atom) :
    Satisfies M w (.counterfactual φ φ) := by
  intro v hv
  exact M.closest_subset w {u | Satisfies M u φ} hv

theorem conditional_vacuous (M : Model Atom) (w : M.World)
    (φ ψ : Formula Atom) (hφ : ∀ v, ¬Satisfies M v φ) :
    Satisfies M w (.counterfactual φ ψ) := by
  intro v hv
  exact (hφ v (M.closest_subset w {u | Satisfies M u φ} hv)).elim

theorem conditional_consequent_conjunction (M : Model Atom) (w : M.World)
    (φ ψ χ : Formula Atom)
    (hψ : Satisfies M w (.counterfactual φ ψ))
    (hχ : Satisfies M w (.counterfactual φ χ)) :
    Satisfies M w (.counterfactual φ (.and ψ χ)) := by
  intro v hv
  exact ⟨hψ v hv, hχ v hv⟩

theorem conditional_modus_ponens_of_centering (M : Model Atom) (w : M.World)
    (φ ψ : Formula Atom) (hφ : Satisfies M w φ)
    (hcond : Satisfies M w (.counterfactual φ ψ)) :
    Satisfies M w ψ := by
  have hmem : w ∈ {u | Satisfies M u φ} := hφ
  have hcenter : M.Closest w {u | Satisfies M u φ} = {w} := M.centered w _ hmem
  have hw : w ∈ M.Closest w {u | Satisfies M u φ} := by
    rw [hcenter]
    change w = w
    rfl
  exact hcond w hw

theorem antecedent_extensionality (M : Model Atom) (w : M.World)
    (φ φ' ψ : Formula Atom)
    (hEq : ∀ v, Satisfies M v φ ↔ Satisfies M v φ') :
    (Satisfies M w (.counterfactual φ ψ) ↔
      Satisfies M w (.counterfactual φ' ψ)) := by
  have hsets : {v | Satisfies M v φ} = {v | Satisfies M v φ'} := by
    ext v
    exact hEq v
  change (∀ v ∈ M.Closest w {u | Satisfies M u φ}, Satisfies M v ψ) ↔
    (∀ v ∈ M.Closest w {u | Satisfies M u φ'}, Satisfies M v ψ)
  rw [show M.Closest w {v | Satisfies M v φ} =
      M.Closest w {v | Satisfies M v φ'} by rw [hsets]]

theorem closest_success (M : Model Atom) (w : M.World) (A : Set M.World)
    (hA : A.Nonempty) : (M.Closest w A).Nonempty :=
  M.closest_success w A hA

/-- OLP's success/limit condition for a satisfiable antecedent. -/
theorem closest_success_for_possible_antecedent (M : Model Atom) (w : M.World)
    (φ : Formula Atom) (hφ : ∃ v, Satisfies M v φ) :
    (M.Closest w {v | Satisfies M v φ}).Nonempty :=
  M.closest_success w _ hφ

end FormalOLP.Counterfactuals

import Mathlib.Data.Set.Basic

/-!
# De Bruijn lambda terms

This is the first native lambda-calculus chain for the OLP chapters
`OpenLogic/content/lambda-calculus/syntax/de-bruijn.tex`,
`.../syntax/substitution.tex`, and `.../syntax/beta.tex`.  The indexed
term type records the number of surrounding binders, so scope and capture
avoidance are enforced by the type of each operation.  The module proves
renaming and substitution identities/composition, contextual beta steps,
multi-step reduction, and scope preservation.  Named syntax, automatic
alpha-equivalence translation, Church--Rosser, and normalization remain
separate interfaces.
-/

namespace FormalOLP.LambdaCalculus

/-! ## Scoped de Bruijn terms and renaming -/

inductive Term : Nat → Type where
  | var {depth : Nat} : Fin depth → Term depth
  | app {depth : Nat} : Term depth → Term depth → Term depth
  | lam {depth : Nat} : Term (depth + 1) → Term depth

namespace Term

abbrev Renaming (source target : Nat) := Fin source → Fin target

def liftRenaming {source target : Nat} (ρ : Renaming source target) :
    Renaming (source + 1) (target + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

def rename {source target : Nat} (ρ : Renaming source target) :
    Term source → Term target
  | .var i => .var (ρ i)
  | .app t u => .app (rename ρ t) (rename ρ u)
  | .lam body => .lam (rename (liftRenaming ρ) body)

theorem liftRenaming_identity {depth : Nat} :
    liftRenaming (id : Renaming depth depth) = id := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

theorem rename_identity {depth : Nat} (t : Term depth) :
    rename (id : Renaming depth depth) t = t := by
  induction t with
  | var i => rfl
  | app t u iht ihu => simp only [rename, iht, ihu]
  | lam body ih =>
      simp only [rename, liftRenaming_identity, ih]

theorem liftRenaming_composition {a b c : Nat}
    (ρ : Renaming a b) (σ : Renaming b c) :
    liftRenaming (σ ∘ ρ) = liftRenaming σ ∘ liftRenaming ρ := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

theorem rename_composition {a : Nat} (t : Term a) :
    ∀ {b c : Nat} (ρ : Renaming a b) (σ : Renaming b c),
      rename σ (rename ρ t) = rename (σ ∘ ρ) t := by
  induction t with
  | var i =>
      intro b c ρ σ
      rfl
  | app t u iht ihu =>
      intro b c ρ σ
      simp only [rename, iht, ihu]
  | lam body ih =>
      intro b c ρ σ
      simp only [rename]
      rw [ih (liftRenaming ρ) (liftRenaming σ)]
      rw [← liftRenaming_composition]

/-! ## Capture-avoiding substitution -/

abbrev Substitution (source target : Nat) := Fin source → Term target

def liftSubstitution {source target : Nat}
    (σ : Substitution source target) : Substitution (source + 1) (target + 1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

def subst {source target : Nat} (σ : Substitution source target) :
    Term source → Term target
  | .var i => σ i
  | .app t u => .app (subst σ t) (subst σ u)
  | .lam body => .lam (subst (liftSubstitution σ) body)

theorem liftSubstitution_identity {depth : Nat} :
    liftSubstitution (fun i : Fin depth => .var i) =
      (fun i : Fin (depth + 1) => .var i) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

theorem subst_identity {depth : Nat} (t : Term depth) :
    subst (fun i : Fin depth => .var i) t = t := by
  induction t with
  | var i => rfl
  | app t u iht ihu => simp only [subst, iht, ihu]
  | lam body ih =>
      simp only [subst]
      rw [liftSubstitution_identity, ih]

theorem subst_rename {a : Nat} (t : Term a) :
    ∀ {b c : Nat} (ρ : Renaming a b) (σ : Substitution b c),
      subst σ (rename ρ t) = subst (fun i => σ (ρ i)) t := by
  induction t with
  | var i =>
      intro b c ρ σ
      rfl
  | app t u iht ihu =>
      intro b c ρ σ
      simp only [rename, subst]
      rw [iht, ihu]
  | lam body ih =>
      intro b c ρ σ
      simp only [rename, subst]
      rw [ih (liftRenaming ρ) (liftSubstitution σ)]
      have hmap :
          (fun i => liftSubstitution σ (liftRenaming ρ i)) =
            liftSubstitution (fun i => σ (ρ i)) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      rw [hmap]

theorem rename_subst {b : Nat} (t : Term b) :
    ∀ {a c : Nat} (ρ : Renaming a c) (σ : Substitution b a),
    rename ρ (subst σ t) =
      subst (fun i => rename ρ (σ i)) t := by
  induction t with
  | var i =>
      intro b c ρ σ
      rfl
  | app t u iht ihu =>
      intro b c ρ σ
      simp only [rename, subst]
      rw [iht, ihu]
  | lam body ih =>
      intro b c ρ σ
      simp only [rename, subst]
      rw [ih (liftRenaming ρ) (liftSubstitution σ)]
      have hmap :
          (fun i => rename (liftRenaming ρ) (liftSubstitution σ i)) =
            liftSubstitution (fun i => rename ρ (σ i)) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          have hcomp : liftRenaming ρ ∘ Fin.succ = Fin.succ ∘ ρ := by
            funext k
            rfl
          change rename (liftRenaming ρ) (rename Fin.succ (σ j)) =
            rename Fin.succ (rename ρ (σ j))
          rw [rename_composition (σ j) Fin.succ (liftRenaming ρ), hcomp]
          rw [rename_composition (σ j) ρ Fin.succ]
      rw [hmap]

theorem subst_rename_succ {source target : Nat}
    (σ : Substitution source target) (t : Term source) :
    subst (liftSubstitution σ) (rename Fin.succ t) =
      rename Fin.succ (subst σ t) := by
  rw [subst_rename t Fin.succ (liftSubstitution σ)]
  symm
  exact rename_subst t Fin.succ σ

theorem liftSubstitution_composition {a b c : Nat}
    (σ : Substitution a b) (τ : Substitution b c) :
    liftSubstitution (fun i => subst τ (σ i)) =
      (fun i => subst (liftSubstitution τ) (liftSubstitution σ i)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact (subst_rename_succ τ (σ j)).symm

theorem subst_composition {a : Nat} (t : Term a) :
    ∀ {b c : Nat} (σ : Substitution a b) (τ : Substitution b c),
      subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := by
  induction t with
  | var i =>
      intro b c σ τ
      rfl
  | app t u iht ihu =>
      intro b c σ τ
      simp only [subst]
      rw [iht, ihu]
  | lam body ih =>
      intro b c σ τ
      simp only [subst]
      rw [ih (liftSubstitution σ) (liftSubstitution τ)]
      rw [← liftSubstitution_composition]

/-! ## Raw erasure, beta reduction, and scope preservation -/

inductive RawTerm : Type where
  | var : Nat → RawTerm
  | app : RawTerm → RawTerm → RawTerm
  | lam : RawTerm → RawTerm

def erase {depth : Nat} : Term depth → RawTerm
  | .var i => .var i.val
  | .app t u => .app (erase t) (erase u)
  | .lam body => .lam (erase body)

def WellScoped : Nat → RawTerm → Prop
  | depth, .var i => i < depth
  | depth, .app t u => WellScoped depth t ∧ WellScoped depth u
  | depth, .lam body => WellScoped (depth + 1) body

def Closed (t : RawTerm) : Prop := WellScoped 0 t

theorem erase_wellScoped {depth : Nat} (t : Term depth) :
    WellScoped depth (erase t) := by
  induction t with
  | var i => exact i.isLt
  | app t u iht ihu => exact ⟨iht, ihu⟩
  | lam body ih => exact ih

theorem rename_wellScoped {source target : Nat}
    (ρ : Renaming source target) (t : Term source) :
    WellScoped target (erase (rename ρ t)) :=
  erase_wellScoped _

theorem subst_wellScoped_of {source : Nat} (t : Term source) :
    ∀ {target : Nat} (σ : Substitution source target),
      (∀ i, WellScoped target (erase (σ i))) →
        WellScoped target (erase (subst σ t)) := by
  induction t with
  | var i =>
      intro target σ hσ
      exact hσ i
  | app t u iht ihu =>
      intro target σ hσ
      exact ⟨iht σ hσ, ihu σ hσ⟩
  | lam body ih =>
      intro target σ hσ
      apply ih (liftSubstitution σ)
      intro i
      refine Fin.cases ?_ ?_ i
      · exact erase_wellScoped (.var 0)
      · intro j
        exact rename_wellScoped Fin.succ (σ j)

def betaSubstitution {depth : Nat} (argument : Term depth) :
    Substitution (depth + 1) depth :=
  Fin.cases argument
    (fun i => .var i)

theorem betaSubstitution_wellScoped {depth : Nat} (argument : Term depth) :
    ∀ i, WellScoped depth (erase (betaSubstitution argument i)) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact erase_wellScoped argument
  · intro j
    exact erase_wellScoped (.var j)

theorem betaRedex_wellScoped {depth : Nat}
    (body : Term (depth + 1)) (argument : Term depth) :
    WellScoped depth
      (erase (subst (betaSubstitution argument) body)) := by
  exact subst_wellScoped_of body (betaSubstitution argument)
    (betaSubstitution_wellScoped argument)

inductive BetaStep : {depth : Nat} → Term depth → Term depth → Prop where
  | redex {depth : Nat} (body : Term (depth + 1)) (argument : Term depth) :
      BetaStep (.app (.lam body) argument) (subst (betaSubstitution argument) body)
  | appLeft {depth : Nat} {t t' u : Term depth} :
      BetaStep t t' → BetaStep (.app t u) (.app t' u)
  | appRight {depth : Nat} {t u u' : Term depth} :
      BetaStep u u' → BetaStep (.app t u) (.app t u')
  | lam {depth : Nat} {t t' : Term (depth + 1)} :
      BetaStep t t' → BetaStep (.lam t) (.lam t')

inductive BetaStar : {depth : Nat} → Term depth → Term depth → Prop where
  | refl {depth : Nat} (t : Term depth) : BetaStar t t
  | tail {depth : Nat} {t u v : Term depth} :
      BetaStep t u → BetaStar u v → BetaStar t v

theorem BetaStar.trans {depth : Nat} {t u v : Term depth} :
    BetaStar t u → BetaStar u v → BetaStar t v
  | .refl _, huv => huv
  | .tail htu huv, huv' => .tail htu (BetaStar.trans huv huv')

theorem betaStep_wellScoped {depth : Nat} {t u : Term depth}
    (hstep : BetaStep t u) (ht : WellScoped depth (erase t)) :
    WellScoped depth (erase u) := by
  induction hstep with
  | redex body argument => exact betaRedex_wellScoped body argument
  | appLeft h ih =>
      exact ⟨ih ht.1, ht.2⟩
  | appRight h ih =>
      exact ⟨ht.1, ih ht.2⟩
  | lam h ih => exact ih ht

theorem betaStar_wellScoped {depth : Nat} {t u : Term depth}
    (hred : BetaStar t u) (ht : WellScoped depth (erase t)) :
    WellScoped depth (erase u) := by
  induction hred with
  | refl => exact ht
  | tail hstep _ ih => exact ih (betaStep_wellScoped hstep ht)

theorem betaStep_closed {t u : Term 0} (hstep : BetaStep t u) :
    Closed (erase u) := by
  exact betaStep_wellScoped hstep (erase_wellScoped t)

end Term

end FormalOLP.LambdaCalculus

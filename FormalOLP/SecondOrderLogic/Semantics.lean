import Mathlib.Data.Set.Basic

/-!
# A typed relational fragment of second-order semantics

This module implements the relation-variable part of the OLP second-order
language from `OpenLogic/content/second-order-logic/syntax-and-semantics/`.
Each relation variable carries an arity, relation environments are therefore
typed by `Fin (arity R)`, and quantification ranges over all relations of the
declared arity (full semantics).  Object variables are named natural numbers
and relation variables are named elements of an arbitrary type.  The
truth-agreement theorem tracks free relation variables while holding the
object assignment fixed; the freshness theorem is the corresponding
quantifier-introduction principle.
-/

namespace FormalOLP.SecondOrderLogic

universe u v

/-- A pure first-order domain for the relational second-order fragment. -/
structure Structure where
  Domain : Type u
  domain_nonempty : Nonempty Domain

/-- Formulas with typed relation variables and named object variables. -/
inductive Formula (RelVar : Type v) (arity : RelVar → Nat) : Type max u v where
  | relAtom (R : RelVar) (args : Fin (arity R) → Nat) :
      Formula RelVar arity
  | falsum : Formula RelVar arity
  | and : Formula RelVar arity → Formula RelVar arity → Formula RelVar arity
  | or : Formula RelVar arity → Formula RelVar arity → Formula RelVar arity
  | imp : Formula RelVar arity → Formula RelVar arity → Formula RelVar arity
  | allObj : Nat → Formula RelVar arity → Formula RelVar arity
  | existsObj : Nat → Formula RelVar arity → Formula RelVar arity
  | allRel : (R : RelVar) → Formula RelVar arity → Formula RelVar arity
  | existsRel : (R : RelVar) → Formula RelVar arity → Formula RelVar arity

namespace Formula

variable {RelVar : Type v} {arity : RelVar → Nat}

def neg (φ : Formula RelVar arity) : Formula RelVar arity := .imp φ .falsum

def verum : Formula RelVar arity := .imp .falsum .falsum

end Formula

abbrev RelEnv (S : Structure) (RelVar : Type v) (arity : RelVar → Nat) :=
  ∀ R : RelVar, (Fin (arity R) → S.Domain) → Prop

structure Assignment (S : Structure) (RelVar : Type v) (arity : RelVar → Nat) where
  obj : Nat → S.Domain
  rel : RelEnv S RelVar arity

namespace Assignment

def updateObj {S : Structure} {RelVar : Type v} {arity : RelVar → Nat}
    (s : Assignment S RelVar arity) (x : Nat) (d : S.Domain) :
    Assignment S RelVar arity :=
  { obj := Function.update s.obj x d
    rel := s.rel }

def updateRel {S : Structure} {RelVar : Type v} {arity : RelVar → Nat}
    [DecidableEq RelVar] (s : Assignment S RelVar arity) (R : RelVar)
    (P : (Fin (arity R) → S.Domain) → Prop) : Assignment S RelVar arity :=
  { obj := s.obj
    rel := Function.update s.rel R P }

end Assignment

def Satisfies {RelVar : Type v} {arity : RelVar → Nat} {S : Structure}
    [DecidableEq RelVar] (s : Assignment S RelVar arity) :
    Formula RelVar arity → Prop
  | .relAtom R args => s.rel R (fun i => s.obj (args i))
  | .falsum => False
  | .and φ ψ => Satisfies s φ ∧ Satisfies s ψ
  | .or φ ψ => Satisfies s φ ∨ Satisfies s ψ
  | .imp φ ψ => Satisfies s φ → Satisfies s ψ
  | .allObj x φ => ∀ d, Satisfies (Assignment.updateObj s x d) φ
  | .existsObj x φ => ∃ d, Satisfies (Assignment.updateObj s x d) φ
  | .allRel R φ => ∀ P, Satisfies (Assignment.updateRel s R P) φ
  | .existsRel R φ => ∃ P, Satisfies (Assignment.updateRel s R P) φ

def FreeRel {RelVar : Type v} {arity : RelVar → Nat} (R : RelVar) :
    Formula RelVar arity → Prop
  | .relAtom Q _ => R = Q
  | .falsum => False
  | .and φ ψ => FreeRel R φ ∨ FreeRel R ψ
  | .or φ ψ => FreeRel R φ ∨ FreeRel R ψ
  | .imp φ ψ => FreeRel R φ ∨ FreeRel R ψ
  | .allObj _ φ => FreeRel R φ
  | .existsObj _ φ => FreeRel R φ
  | .allRel Q φ => R ≠ Q ∧ FreeRel R φ
  | .existsRel Q φ => R ≠ Q ∧ FreeRel R φ

theorem satisfies_rel_agreement {RelVar : Type v} {arity : RelVar → Nat}
    [DecidableEq RelVar] {S : Structure} (obj : Nat → S.Domain)
    (ρ σ : RelEnv S RelVar arity) {φ : Formula RelVar arity}
    (hRel : ∀ R, FreeRel R φ → ∀ args, ρ R args ↔ σ R args) :
    Satisfies (Assignment.mk obj ρ) φ ↔ Satisfies (Assignment.mk obj σ) φ := by
  induction φ generalizing obj ρ σ with
  | relAtom R args =>
      exact hRel R (by simp [FreeRel]) (fun i => obj (args i))
  | falsum => rfl
  | and φ ψ ihφ ihψ =>
      have hφ := ihφ obj ρ σ (fun R hR => hRel R (Or.inl hR))
      have hψ := ihψ obj ρ σ (fun R hR => hRel R (Or.inr hR))
      exact and_congr hφ hψ
  | or φ ψ ihφ ihψ =>
      have hφ := ihφ obj ρ σ (fun R hR => hRel R (Or.inl hR))
      have hψ := ihψ obj ρ σ (fun R hR => hRel R (Or.inr hR))
      exact or_congr hφ hψ
  | imp φ ψ ihφ ihψ =>
      have hφ := ihφ obj ρ σ (fun R hR => hRel R (Or.inl hR))
      have hψ := ihψ obj ρ σ (fun R hR => hRel R (Or.inr hR))
      exact imp_congr hφ hψ
  | allObj x φ ih =>
      constructor
      · intro h d
        exact (ih (Function.update obj x d) ρ σ (fun R hR => hRel R hR)).mp (h d)
      · intro h d
        exact (ih (Function.update obj x d) ρ σ (fun R hR => hRel R hR)).mpr (h d)
  | existsObj x φ ih =>
      constructor
      · rintro ⟨d, h⟩
        exact ⟨d, (ih (Function.update obj x d) ρ σ (fun R hR => hRel R hR)).mp h⟩
      · rintro ⟨d, h⟩
        exact ⟨d, (ih (Function.update obj x d) ρ σ (fun R hR => hRel R hR)).mpr h⟩
  | allRel R φ ih =>
      constructor
      · intro h P
        have hRel' : ∀ Q, FreeRel Q φ → ∀ args,
            (Function.update ρ R P) Q args ↔ (Function.update σ R P) Q args := by
          intro Q hQ args
          by_cases hQR : Q = R
          · subst Q
            simp [Function.update]
          · simpa [Function.update, hQR] using hRel Q ⟨hQR, hQ⟩ args
        exact (ih obj (Function.update ρ R P) (Function.update σ R P) hRel').mp (h P)
      · intro h P
        have hRel' : ∀ Q, FreeRel Q φ → ∀ args,
            (Function.update ρ R P) Q args ↔ (Function.update σ R P) Q args := by
          intro Q hQ args
          by_cases hQR : Q = R
          · subst Q
            simp [Function.update]
          · simpa [Function.update, hQR] using hRel Q ⟨hQR, hQ⟩ args
        exact (ih obj (Function.update ρ R P) (Function.update σ R P) hRel').mpr (h P)
  | existsRel R φ ih =>
      constructor
      · rintro ⟨P, h⟩
        have hRel' : ∀ Q, FreeRel Q φ → ∀ args,
            (Function.update ρ R P) Q args ↔ (Function.update σ R P) Q args := by
          intro Q hQ args
          by_cases hQR : Q = R
          · subst Q
            simp [Function.update]
          · simpa [Function.update, hQR] using hRel Q ⟨hQR, hQ⟩ args
        exact ⟨P, (ih obj (Function.update ρ R P) (Function.update σ R P) hRel').mp h⟩
      · rintro ⟨P, h⟩
        have hRel' : ∀ Q, FreeRel Q φ → ∀ args,
            (Function.update ρ R P) Q args ↔ (Function.update σ R P) Q args := by
          intro Q hQ args
          by_cases hQR : Q = R
          · subst Q
            simp [Function.update]
          · simpa [Function.update, hQR] using hRel Q ⟨hQR, hQ⟩ args
        exact ⟨P, (ih obj (Function.update ρ R P) (Function.update σ R P) hRel').mpr h⟩

theorem allRel_elim {RelVar : Type v} {arity : RelVar → Nat}
    [DecidableEq RelVar] {S : Structure} (s : Assignment S RelVar arity)
    (R : RelVar) (φ : Formula RelVar arity) (h : Satisfies s (.allRel R φ))
    (P : (Fin (arity R) → S.Domain) → Prop) :
    Satisfies (Assignment.updateRel s R P) φ := h P

theorem allRel_intro {RelVar : Type v} {arity : RelVar → Nat}
    [DecidableEq RelVar] {S : Structure} (s : Assignment S RelVar arity)
    (R : RelVar) (φ : Formula RelVar arity)
    (h : ∀ P : (Fin (arity R) → S.Domain) → Prop,
      Satisfies (Assignment.updateRel s R P) φ) :
    Satisfies s (.allRel R φ) := h

theorem allRel_intro_of_not_free {RelVar : Type v} {arity : RelVar → Nat}
    [DecidableEq RelVar] {S : Structure} (s : Assignment S RelVar arity)
    (R : RelVar) (φ : Formula RelVar arity) (hR : ¬FreeRel R φ)
    (h : Satisfies s φ) : Satisfies s (.allRel R φ) := by
  intro P
  exact (satisfies_rel_agreement s.obj s.rel (Function.update s.rel R P)
    (fun Q hQ args => by
      by_cases hQR : Q = R
      · subst Q
        exact (hR hQ).elim
      · simp [Function.update, hQR])).mp h

end FormalOLP.SecondOrderLogic

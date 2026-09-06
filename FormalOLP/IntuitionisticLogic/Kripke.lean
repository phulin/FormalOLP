import FormalOLP.PropositionalLogic.Syntax

/-!
# Intuitionistic Kripke models

The OLP relational semantics uses nonempty partially ordered worlds and a
monotone valuation.  Forcing implication quantifies over all future worlds.
This module defines that model and proves persistence of forcing by induction
on formulas.  The target material is `OpenLogic/content/intuitionistic-
logic/semantics/relational-models.tex`, definition `defn:true-at-w` and
proposition `prop:true-monotonic`.

The structures correspond to Pool's `LO.IntProp.Kripke.Frame`,
`LO.IntProp.Kripke.Valuation`, `LO.IntProp.Kripke.Model`, and
`LO.IntProp.Formula.Kripke.Satisfies` in
`LeanPool/Incompleteness/Foundation/IntProp/Kripke/Basic.lean` at Pool
revision `c8ddda0a64f21cb019720cdda48c94354d4091e7`.  The declarations and
proofs here are native and do not import LeanPool.
-/

namespace FormalOLP.IntuitionisticLogic

open FormalOLP.PropositionalLogic

universe u v

/-- A nonempty partially ordered set of intuitionistic worlds. -/
structure Frame where
  World : Type u
  world_nonempty : Nonempty World
  Rel : World → World → Prop
  rel_refl : ∀ x, Rel x x
  rel_antisymm : ∀ {x y}, Rel x y → Rel y x → x = y
  rel_trans : ∀ {x y z}, Rel x y → Rel y z → Rel x z

/-- A valuation whose atomic truth persists along the frame relation. -/
structure Valuation (F : Frame) (Atom : Type v) where
  Val : F.World → Atom → Prop
  hereditary : ∀ {x y : F.World}, F.Rel x y → ∀ {a}, Val x a → Val y a

/-- A frame equipped with a persistent atom valuation. -/
structure Model (Atom : Type v) extends Frame where
  Valuation : Valuation toFrame Atom

namespace Model

/-- Build a model from a frame and one of its persistent valuations. -/
def fromFrame (F : Frame) (V : FormalOLP.IntuitionisticLogic.Valuation F Atom) : Model Atom :=
  { toFrame := F
    Valuation := V }

end Model

/-- Forcing of a propositional formula at a world. -/
def Forces (M : Model Atom) : M.World → Formula Atom → Prop
  | x, .atom a => M.Valuation.Val x a
  | _, .falsum => False
  | x, .and φ ψ => Forces M x φ ∧ Forces M x ψ
  | x, .or φ ψ => Forces M x φ ∨ Forces M x ψ
  | x, .imp φ ψ => ∀ {y}, M.Rel x y → (Forces M y φ → Forces M y ψ)

namespace Forces

variable {Atom : Type v} {M : Model Atom} {x y : M.World}

@[simp] theorem atom (a : Atom) : Forces M x (.atom a) ↔ M.Valuation.Val x a := Iff.rfl

@[simp] theorem falsum : ¬Forces M x (.falsum : Formula Atom) := by
  simp [Forces]

@[simp] theorem and (φ ψ : Formula Atom) :
    Forces M x (.and φ ψ) ↔ Forces M x φ ∧ Forces M x ψ := Iff.rfl

@[simp] theorem or (φ ψ : Formula Atom) :
    Forces M x (.or φ ψ) ↔ Forces M x φ ∨ Forces M x ψ := Iff.rfl

@[simp] theorem imp (φ ψ : Formula Atom) :
    Forces M x (.imp φ ψ) ↔
      ∀ {y}, M.Rel x y → (Forces M y φ → Forces M y ψ) := Iff.rfl

/-- Negation has the expected Kripke forcing clause. -/
theorem neg (φ : Formula Atom) :
    Forces M x (Formula.neg φ) ↔
      ∀ {y}, M.Rel x y → ¬Forces M y φ := by
  rfl

end Forces

/-- Every forced formula remains forced at every later world. -/
theorem forces_hereditary {φ : Formula Atom} (hxy : M.Rel x y) :
    Forces M x φ → Forces M y φ := by
  induction φ generalizing x y with
  | atom a =>
      intro h
      exact M.Valuation.hereditary hxy h
  | falsum =>
      intro h
      exact h
  | and φ ψ ihφ ihψ =>
      intro h
      exact ⟨ihφ hxy h.1, ihψ hxy h.2⟩
  | or φ ψ ihφ ihψ =>
      intro h
      cases h with
      | inl hφ => exact Or.inl (ihφ hxy hφ)
      | inr hψ => exact Or.inr (ihψ hxy hψ)
  | imp φ ψ ihφ ihψ =>
      intro h y hy
      exact h (M.rel_trans hxy hy)

namespace Model

/-- Truth at every world of a model. -/
def Valid (M : Model Atom) (φ : Formula Atom) : Prop :=
  ∀ x, Forces M x φ

end Model

namespace Frame

/-- Validity on a frame quantifies over all persistent valuations and worlds. -/
def Valid {Atom : Type v} (F : Frame) (φ : Formula Atom) : Prop :=
  ∀ V : FormalOLP.IntuitionisticLogic.Valuation F Atom,
    Model.Valid (Model.fromFrame F V) φ

end Frame

end FormalOLP.IntuitionisticLogic

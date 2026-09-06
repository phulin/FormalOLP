import Mathlib.Data.Set.Basic

/-!
# Relational epistemic logic

This module follows the OLP multi-agent epistemic language and relational
models in `OpenLogic/content/applied-modal-logic/epistemic-logic/`.  Each
agent has its own accessibility relation.  The semantic chain proves closure,
factivity, positive introspection, negative introspection, and the first
common-knowledge reachability lemmas.  The declarations are native and do
not import the Lean Pool modal development.
-/

namespace FormalOLP.AppliedModalLogic.Epistemic

universe u v

/-- Formulas with one knowledge operator for each agent. -/
inductive Formula (Agent : Type u) (Atom : Type v) : Type max u v where
  | atom : Atom → Formula Agent Atom
  | falsum : Formula Agent Atom
  | and : Formula Agent Atom → Formula Agent Atom → Formula Agent Atom
  | or : Formula Agent Atom → Formula Agent Atom → Formula Agent Atom
  | imp : Formula Agent Atom → Formula Agent Atom → Formula Agent Atom
  | knowledge : Agent → Formula Agent Atom → Formula Agent Atom

namespace Formula

variable {Agent : Type u} {Atom : Type v}

def neg (φ : Formula Agent Atom) : Formula Agent Atom := .imp φ .falsum

def verum : Formula Agent Atom := .imp .falsum .falsum

@[simp] theorem neg_eq (φ : Formula Agent Atom) : neg φ = .imp φ .falsum := rfl

@[simp] theorem verum_eq : (verum : Formula Agent Atom) = .imp .falsum .falsum := rfl

end Formula

/-- A nonempty multi-agent epistemic frame. -/
structure Frame (Agent : Type u) where
  World : Type v
  world_nonempty : Nonempty World
  Rel : Agent → World → World → Prop

/-- A frame and a valuation of atomic propositions. -/
structure Model (Agent : Type u) (Atom : Type w) extends Frame Agent where
  Valuation : World → Atom → Prop

namespace Model

universe w

def fromFrame (F : Frame Agent) (valuation : F.World → Atom → Prop) : Model Agent Atom :=
  { toFrame := F
    Valuation := valuation }

end Model

/-- Truth of an epistemic formula at a world. -/
def Satisfies (M : Model Agent Atom) : M.World → Formula Agent Atom → Prop
  | x, .atom a => M.Valuation x a
  | _, .falsum => False
  | x, .and φ ψ => Satisfies M x φ ∧ Satisfies M x ψ
  | x, .or φ ψ => Satisfies M x φ ∨ Satisfies M x ψ
  | x, .imp φ ψ => Satisfies M x φ → Satisfies M x ψ
  | x, .knowledge a φ => ∀ y, M.Rel a x y → Satisfies M y φ

namespace Satisfies

variable {Agent : Type u} {Atom : Type v} {M : Model Agent Atom} {x : M.World}

@[simp] theorem atom (a : Atom) : Satisfies M x (.atom a) ↔ M.Valuation x a := Iff.rfl

@[simp] theorem falsum : ¬Satisfies M x (.falsum : Formula Agent Atom) := by
  simp [Satisfies]

@[simp] theorem and (φ ψ : Formula Agent Atom) :
    Satisfies M x (.and φ ψ) ↔ Satisfies M x φ ∧ Satisfies M x ψ := Iff.rfl

@[simp] theorem or (φ ψ : Formula Agent Atom) :
    Satisfies M x (.or φ ψ) ↔ Satisfies M x φ ∨ Satisfies M x ψ := Iff.rfl

@[simp] theorem imp (φ ψ : Formula Agent Atom) :
    Satisfies M x (.imp φ ψ) ↔ (Satisfies M x φ → Satisfies M x ψ) := Iff.rfl

@[simp] theorem knowledge (a : Agent) (φ : Formula Agent Atom) :
    Satisfies M x (.knowledge a φ) ↔ ∀ y, M.Rel a x y → Satisfies M y φ := Iff.rfl

theorem neg (φ : Formula Agent Atom) :
    Satisfies M x (Formula.neg φ) ↔ ¬Satisfies M x φ := Iff.rfl

end Satisfies

namespace Frame

variable {Agent : Type u} {Atom : Type v}

def Valid (F : Frame Agent) (φ : Formula Agent Atom) : Prop :=
  ∀ valuation : F.World → Atom → Prop, ∀ x,
    Satisfies (Model.fromFrame F valuation) x φ

def Reflexive (F : Frame Agent) (a : Agent) : Prop := ∀ x, F.Rel a x x

def Transitive (F : Frame Agent) (a : Agent) : Prop :=
  ∀ ⦃x y z⦄, F.Rel a x y → F.Rel a y z → F.Rel a x z

def Euclidean (F : Frame Agent) (a : Agent) : Prop :=
  ∀ ⦃x y z⦄, F.Rel a x y → F.Rel a x z → F.Rel a y z

end Frame

def axiomK (a : Agent) (φ ψ : Formula Agent Atom) : Formula Agent Atom :=
  .imp (.knowledge a (.imp φ ψ)) (.imp (.knowledge a φ) (.knowledge a ψ))

theorem satisfies_axiomK (M : Model Agent Atom) (x : M.World)
    (a : Agent) (φ ψ : Formula Agent Atom) : Satisfies M x (axiomK a φ ψ) := by
  intro hK hφ y hxy
  exact hK y hxy (hφ y hxy)

theorem satisfies_factivity (M : Model Agent Atom) (a : Agent)
    (hR : M.toFrame.Reflexive a) (x : M.World)
    (φ : Formula Agent Atom) :
    Satisfies M x (.imp (.knowledge a φ) φ) := by
  intro hK
  exact hK x (hR x)

theorem satisfies_positive_introspection (M : Model Agent Atom) (a : Agent)
    (hR : M.toFrame.Transitive a) (x : M.World)
    (φ : Formula Agent Atom) :
    Satisfies M x (.imp (.knowledge a φ) (.knowledge a (.knowledge a φ))) := by
  intro hK y hxy z hyz
  exact hK z (hR hxy hyz)

theorem satisfies_negative_introspection (M : Model Agent Atom) (a : Agent)
    (hR : M.toFrame.Euclidean a) (x : M.World)
    (φ : Formula Agent Atom) :
    Satisfies M x (.imp (Formula.neg (.knowledge a φ))
      (.knowledge a (Formula.neg (.knowledge a φ)))) := by
  intro hnot y hxy
  change ¬Satisfies M y (.knowledge a φ)
  intro hy
  apply hnot
  intro z hxz
  exact hy z (hR hxy hxz)

/-- The one-step relation generated by a group of agents. -/
inductive Reach (F : Frame Agent) (G : Set Agent) : F.World → F.World → Prop where
  | refl (x : F.World) : Reach F G x x
  | tail {x y z : F.World} :
      (∃ a, a ∈ G ∧ F.Rel a x y) → Reach F G y z → Reach F G x z

theorem Reach.trans {F : Frame Agent} {G : Set Agent} {x y z : F.World}
    (hxy : Reach F G x y) (hyz : Reach F G y z) : Reach F G x z := by
  induction hxy with
  | refl => exact hyz
  | tail hstep _ ih => exact Reach.tail hstep (ih hyz)

/-- Common knowledge is truth at every world reachable through the group. -/
def CommonKnowledge (M : Model Agent Atom) (G : Set Agent)
    (φ : Formula Agent Atom) (x : M.World) : Prop :=
  ∀ y, Reach M.toFrame G x y → Satisfies M y φ

theorem commonKnowledge_at_world {M : Model Agent Atom} {G : Set Agent}
    {φ : Formula Agent Atom} {x : M.World}
    (h : CommonKnowledge M G φ x) : Satisfies M x φ :=
  h x (Reach.refl x)

theorem commonKnowledge_to_knowledge {M : Model Agent Atom} {G : Set Agent}
    {φ : Formula Agent Atom} {x : M.World} {a : Agent} (ha : a ∈ G)
    (h : CommonKnowledge M G φ x) :
    Satisfies M x (.knowledge a φ) := by
  intro y hxy
  exact h y (Reach.tail ⟨a, ha, hxy⟩ (Reach.refl y))

/- The semantic common-knowledge operator is the greatest fixed point of
the one-step group-knowledge condition.  Stating this at the semantic level
keeps the finite-path presentation explicit while exposing the usual OLP
fixed-point law. -/
theorem commonKnowledge_iff_fixedPoint {M : Model Agent Atom} {G : Set Agent}
    {φ : Formula Agent Atom} {x : M.World} :
    CommonKnowledge M G φ x ↔
      Satisfies M x φ ∧
        ∀ a, a ∈ G → ∀ y, M.Rel a x y → CommonKnowledge M G φ y := by
  constructor
  · intro h
    refine ⟨commonKnowledge_at_world h, ?_⟩
    intro a ha y hxy z hyz
    exact h z (Reach.trans
      (Reach.tail ⟨a, ha, hxy⟩ (Reach.refl y)) hyz)
  · rintro ⟨hx, hstep⟩ y hreach
    induction hreach with
    | refl => exact hx
    | tail hxy hyz _ih =>
        rcases hxy with ⟨a, ha, hxy⟩
        exact hstep a ha _ hxy _ hyz

end FormalOLP.AppliedModalLogic.Epistemic

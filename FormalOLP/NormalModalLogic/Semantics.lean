import FormalOLP.NormalModalLogic.Syntax

/-!
# Relational semantics for normal modal logic

The OLP relational-model chapters interpret `□φ` at a world as truth of `φ`
at every accessible world.  Frames and models below make nonempty worlds
explicit, as in that presentation.

The structures and recursive truth definition correspond to
`LO.Modal.Kripke.Frame`, `LO.Modal.Kripke.Model`, and
`LO.Modal.Formula.Kripke.Satisfies` in
`LeanPool/Incompleteness/Foundation/Modal/Kripke/Basic.lean` at Pool revision
`c8ddda0a64f21cb019720cdda48c94354d4091e7`.  `Frame.Valid` has the same
all-valuations/all-worlds scope as Pool's `ValidOnFrame`.  These are native
re-declarations; the proofs in this topic do not call Pool declarations.
-/

namespace FormalOLP.NormalModalLogic

universe u v

/-- A nonempty Kripke frame. -/
structure Frame where
  World : Type u
  Rel : World → World → Prop
  world_nonempty : Nonempty World

/-- A frame together with an atom valuation. -/
structure Model (Atom : Type v) extends Frame where
  Valuation : World → Atom → Prop

namespace Model

/-- Turn a frame and a valuation into a model. -/
def fromFrame (F : Frame) (valuation : F.World → Atom → Prop) : Model Atom :=
  { toFrame := F
    Valuation := valuation }

end Model

/-- Truth of a formula at a world of a model. -/
def Satisfies (M : Model Atom) : M.World → Formula Atom → Prop
  | x, .atom a => M.Valuation x a
  | _, .falsum => False
  | x, .imp φ ψ => Satisfies M x φ → Satisfies M x ψ
  | x, .box φ => ∀ y, M.Rel x y → Satisfies M y φ

namespace Satisfies

variable {Atom : Type v} {M : Model Atom} {x : M.World}

@[simp] theorem atom (a : Atom) : Satisfies M x (.atom a) ↔ M.Valuation x a := Iff.rfl

@[simp] theorem falsum : ¬Satisfies M x (.falsum : Formula Atom) := by
  simp [Satisfies]

@[simp] theorem imp (φ ψ : Formula Atom) :
    Satisfies M x (.imp φ ψ) ↔ (Satisfies M x φ → Satisfies M x ψ) := Iff.rfl

@[simp] theorem box (φ : Formula Atom) :
    Satisfies M x (.box φ) ↔ ∀ y, M.Rel x y → Satisfies M y φ := Iff.rfl

theorem necessitation {φ : Formula Atom} (h : ∀ y : M.World, Satisfies M y φ) :
    Satisfies M x (.box φ) := by
  intro y _
  exact h y

end Satisfies

namespace Model

/-- Truth at every world of a model. -/
def Valid (M : Model Atom) (φ : Formula Atom) : Prop :=
  ∀ x, Satisfies M x φ

theorem valid_box {φ : Formula Atom} (h : Valid M φ) : Valid M (.box φ) := by
  intro x
  exact Satisfies.necessitation h

end Model

namespace Frame

/-- Validity on a frame quantifies over all valuations and all worlds. -/
def Valid {Atom : Type v} (F : Frame) (φ : Formula Atom) : Prop :=
  ∀ valuation : F.World → Atom → Prop,
    ∀ x, Satisfies (Model.fromFrame F valuation) x φ

def Reflexive (F : Frame) : Prop := ∀ x, F.Rel x x

/-- Every two-step path in the frame can be shortened to one step. -/
def Transitive (F : Frame) : Prop :=
  ∀ ⦃x y z⦄, F.Rel x y → F.Rel y z → F.Rel x z

/-- Every world has at least one accessible successor. -/
def Serial (F : Frame) : Prop := ∀ x, ∃ y, F.Rel x y

/-- A symmetric accessibility relation can be traversed in either direction. -/
def Symmetric (F : Frame) : Prop :=
  ∀ ⦃x y⦄, F.Rel x y → F.Rel y x

/-- A Euclidean relation preserves a common successor from either branch. -/
def Euclidean (F : Frame) : Prop :=
  ∀ ⦃x y z⦄, F.Rel x y → F.Rel x z → F.Rel y z

theorem valid_box {φ : Formula Atom} (h : Valid F φ) : Valid F (.box φ) := by
  intro valuation x
  exact Satisfies.necessitation (fun y => h valuation y)

end Frame

end FormalOLP.NormalModalLogic

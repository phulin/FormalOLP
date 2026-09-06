import FormalOLP.NormalModalLogic.Semantics

/-!
# Soundness and frame correspondence for K and T

These are the first theorem chain in the OLP normal-modal-logic topic:
necessitation is valid on every frame, the distribution axiom K is valid on
every frame, and the reflexivity axiom T is valid exactly on reflexive frames.
The proofs use the native syntax and semantics from the preceding modules.

The formula definitions correspond to Pool's `LO.Axioms.K`, `LO.Axioms.T`,
`LO.Axioms.D`, and `LO.Axioms.Four` in
`LeanPool/Incompleteness/Foundation/Modal/Axioms.lean`.  The K and
necessitation arguments are new native proofs of the same mathematical facts
as Pool's `LO.Modal.Formula.Kripke.ValidOnModel.axiomK`,
`LO.Modal.Formula.Kripke.ValidOnFrame.axiomK`,
`LO.Modal.Formula.Kripke.ValidOnModel.nec`, and
`LO.Modal.Formula.Kripke.ValidOnFrame.nec` in `Kripke/Basic.lean`.
The T and 4 correspondence arguments are new direct proofs of the facts
named `LO.Modal.Kripke.reflexive_of_validate_AxiomT` and
`LO.Modal.Kripke.transitive_of_validate_AxiomFour` in
`Kripke/Hilbert/Geach.lean`; D has no matching generic Pool correspondence
lemma in the pinned snapshot, so both D directions here are new native proofs.
-/

namespace FormalOLP.NormalModalLogic

/-- The distribution axiom of the basic normal modal logic K. -/
def axiomK (φ ψ : Formula Atom) : Formula Atom :=
  .imp (.box (.imp φ ψ)) (.imp (.box φ) (.box ψ))

/-- The reflexivity axiom T. -/
def axiomT (φ : Formula Atom) : Formula Atom := .imp (.box φ) φ

theorem satisfies_axiomK (M : Model Atom) (x : M.World)
    (φ ψ : Formula Atom) : Satisfies M x (axiomK φ ψ) := by
  change (Satisfies M x (.box (.imp φ ψ)) →
    Satisfies M x (.box φ) → Satisfies M x (.box ψ))
  intro hK hφ y hxy
  exact (hK y hxy) (hφ y hxy)

theorem frame_valid_axiomK (F : Frame) :
    F.Valid (axiomK (.atom 0) (.atom 1) : Formula Nat) := by
  intro valuation x
  exact satisfies_axiomK (Model.fromFrame F valuation) x (.atom 0) (.atom 1)

theorem frame_valid_axiomT_of_reflexive {F : Frame} (hR : F.Reflexive) :
    F.Valid (axiomT (.atom 0) : Formula Nat) := by
  intro valuation x
  change Satisfies (Model.fromFrame F valuation) x
    (.box (.atom 0)) → Satisfies (Model.fromFrame F valuation) x (.atom 0)
  intro hbox
  exact hbox x (hR x)

theorem reflexive_of_frame_valid_axiomT {F : Frame}
    (hT : F.Valid (axiomT (.atom 0) : Formula Nat)) : F.Reflexive := by
  intro x
  by_cases hxx : F.Rel x x
  · exact hxx
  · let valuation : F.World → Nat → Prop := fun y a => y ≠ x ∧ a = 0
    let M : Model Nat := Model.fromFrame F valuation
    have hT_x : Satisfies M x (axiomT (.atom 0)) := hT valuation x
    change Satisfies M x (.box (.atom 0)) → Satisfies M x (.atom 0) at hT_x
    have hbox : Satisfies M x (.box (.atom 0)) := by
      intro y hxy
      change valuation y 0
      exact ⟨fun hyx => hxx (hyx ▸ hxy), rfl⟩
    have h_atom : Satisfies M x (.atom 0) := hT_x hbox
    change valuation x 0 at h_atom
    exact False.elim (h_atom.1 rfl)

theorem frame_valid_axiomT_iff_reflexive {F : Frame} :
    F.Valid (axiomT (.atom 0) : Formula Nat) ↔ F.Reflexive := by
  constructor
  · exact reflexive_of_frame_valid_axiomT
  · exact frame_valid_axiomT_of_reflexive

/-- The transitivity axiom 4. -/
def axiomFour (φ : Formula Atom) : Formula Atom := .imp (.box φ) (.box (.box φ))

/-- The seriality axiom D. -/
def axiomD (φ : Formula Atom) : Formula Atom := .imp (.box φ) (Formula.diamond φ)

theorem frame_valid_axiomFour_of_transitive {F : Frame} (hR : F.Transitive) :
    F.Valid (axiomFour (.atom 0) : Formula Nat) := by
  intro valuation x
  change Satisfies (Model.fromFrame F valuation) x (.box (.atom 0)) →
    Satisfies (Model.fromFrame F valuation) x (.box (.box (.atom 0)))
  intro hbox y hxy z hyz
  exact hbox z (hR hxy hyz)

theorem transitive_of_frame_valid_axiomFour {F : Frame}
    (h4 : F.Valid (axiomFour (.atom 0) : Formula Nat)) : F.Transitive := by
  intro x y z hxy hyz
  by_cases hxz : F.Rel x z
  · exact hxz
  · let valuation : F.World → Nat → Prop := fun w a => w ≠ z ∧ a = 0
    let M : Model Nat := Model.fromFrame F valuation
    have h4_x : Satisfies M x (axiomFour (.atom 0)) := h4 valuation x
    change Satisfies M x (.box (.atom 0)) →
      Satisfies M x (.box (.box (.atom 0))) at h4_x
    have hbox : Satisfies M x (.box (.atom 0)) := by
      intro w hxw
      change valuation w 0
      exact ⟨fun hwz => hxz (hwz ▸ hxw), rfl⟩
    have hdouble : Satisfies M x (.box (.box (.atom 0))) := h4_x hbox
    have hbox_at_y : ¬Satisfies M y (.box (.atom 0)) := by
      intro hbox_y
      have hfalse : Satisfies M z (.atom 0) := hbox_y z hyz
      change valuation z 0 at hfalse
      exact hfalse.1 rfl
    exact False.elim (hbox_at_y (hdouble y hxy))

theorem frame_valid_axiomFour_iff_transitive {F : Frame} :
    F.Valid (axiomFour (.atom 0) : Formula Nat) ↔ F.Transitive := by
  constructor
  · exact transitive_of_frame_valid_axiomFour
  · exact frame_valid_axiomFour_of_transitive

theorem frame_valid_axiomD_of_serial {F : Frame} (hR : F.Serial) :
    F.Valid (axiomD (.atom 0) : Formula Nat) := by
  intro valuation x
  change Satisfies (Model.fromFrame F valuation) x (.box (.atom 0)) →
    Satisfies (Model.fromFrame F valuation) x (Formula.diamond (.atom 0))
  intro hbox hbox_neg
  obtain ⟨y, hxy⟩ := hR x
  exact (hbox_neg y hxy) (hbox y hxy)

theorem serial_of_frame_valid_axiomD {F : Frame}
    (hD : F.Valid (axiomD (.atom 0) : Formula Nat)) : F.Serial := by
  intro x
  by_cases hserial : ∃ y, F.Rel x y
  · exact hserial
  · let valuation : F.World → Nat → Prop := fun _ _ => False
    let M : Model Nat := Model.fromFrame F valuation
    have hD_x : Satisfies M x (axiomD (.atom 0)) := hD valuation x
    change Satisfies M x (.box (.atom 0)) →
      Satisfies M x (Formula.diamond (.atom 0)) at hD_x
    have hbox : Satisfies M x (.box (.atom 0)) := by
      intro y hxy
      exact (hserial ⟨y, hxy⟩).elim
    have hdiamond : Satisfies M x (Formula.diamond (.atom 0)) := hD_x hbox
    change Satisfies M x (.box (Formula.neg (.atom 0))) → False at hdiamond
    have hbox_neg : Satisfies M x (.box (Formula.neg (.atom 0))) := by
      intro y hxy
      exact (hserial ⟨y, hxy⟩).elim
    exact False.elim (hdiamond hbox_neg)

theorem frame_valid_axiomD_iff_serial {F : Frame} :
    F.Valid (axiomD (.atom 0) : Formula Nat) ↔ F.Serial := by
  constructor
  · exact serial_of_frame_valid_axiomD
  · exact frame_valid_axiomD_of_serial

end FormalOLP.NormalModalLogic

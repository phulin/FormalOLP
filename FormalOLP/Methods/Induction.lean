import Mathlib.Data.Nat.Basic
import Mathlib.Order.WellFounded

/-!
# Induction principles

This file records the reusable induction principles used throughout the
formalization.  The statements follow the presentations in
`OpenLogic/content/methods/induction/induction-on-N.tex`,
`strong-induction.tex`, and `relations.tex`: ordinary induction, strong
induction, induction over a well-founded relation, and induction by a natural
valued measure.
-/

namespace FormalOLP.Methods

theorem weak_induction {P : Nat → Prop} (base : P 0)
    (step : ∀ n, P n → P (n + 1)) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih =>
      simpa [Nat.succ_eq_add_one] using step n ih

theorem strong_induction {P : Nat → Prop}
    (step : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  intro n
  exact Nat.strong_induction_on n step

theorem wellFounded_induction {α : Type} {r : α → α → Prop}
    (wellFounded : WellFounded r) {P : α → Prop}
    (step : ∀ x, (∀ y, r y x → P y) → P x) : ∀ x, P x := by
  intro x
  exact wellFounded.induction x step

theorem measure_induction {α : Type} (measure : α → Nat) {P : α → Prop}
    (step : ∀ x, (∀ y, measure y < measure x → P y) → P x) : ∀ x, P x := by
  intro x
  let wellFounded : WellFounded (Function.onFun (· < ·) measure) :=
    Nat.lt_wfRel.wf.onFun
  exact wellFounded.induction x step

theorem weak_induction_succ {P : Nat → Prop} (base : P 0)
    (step : ∀ n, P n → P (n + 1)) (n : Nat) : P (n + 1) := by
  exact weak_induction base step (n + 1)

end FormalOLP.Methods

import Lean.Util.CollectAxioms
import FormalOLP
import TauCeti.Algebra.Algebra.Hom
import LeanPool.Computability
import LeanPool.FoZfc
import LeanPool.FormalizationOfBoundedArithmetic
import LeanPool.Incompleteness
import LeanPool.PartialCombinatoryAlgebras
import LeanPool.ZFLean
import LeanPool.Lean4GlCoalgebras
import LeanPool.LeanModelChecking
import LeanPool.Lentil

/-!
# Lean Pool axiom audit

The audit walks every declaration whose name begins with `LeanPool`, including
non-entry declarations in the imported closure.  It rejects any dependency
outside the project's explicitly allowed foundational axioms.
-/

open Lean Elab Command

elab "#audit_leanpool_axioms" : command => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for h : idx in [0:env.header.moduleData.size] do
    let module := env.header.modules[idx]!
    if module.module.toString.startsWith "LeanPool" then
      for constant in env.header.moduleData[idx].constants do
        names := names.push constant.name
  let allowed : Array Name := #[``Classical.choice, ``propext, ``Quot.sound]
  let mut audited : Nat := 0
  let mut violations : Array (Name × Name) := #[]
  for name in names do
    let axioms ← liftCoreM <| Lean.collectAxioms name
    audited := audited + 1
    for ax in axioms do
      if !allowed.contains ax then
        violations := violations.push (name, ax)
  logInfo m!"audited {audited} LeanPool declarations"
  if !violations.isEmpty then
    for (name, ax) in violations do
      logError m!"{name} depends on disallowed axiom {ax}"
    throwError "LeanPool axiom audit failed"
  logInfo m!"LeanPool axiom audit passed"

#audit_leanpool_axioms

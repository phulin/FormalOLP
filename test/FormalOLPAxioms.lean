import Lean.Util.CollectAxioms
import FormalOLP

/-!
# FormalOLP axiom audit

The command audits every declaration whose defining module is under the native
`FormalOLP` module tree.  It uses the environment's module ownership data and
`Lean.collectAxioms`, so the audit does not depend on a declaration-name list
or on imported dependency declarations.  Only the standard foundational
axioms accepted by this project are allowed.
-/

open Lean Elab Command

elab "#audit_formalolp_axioms" : command => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for h : idx in [0:env.header.moduleData.size] do
    let module := env.header.modules[idx]!
    if module.module.toString.startsWith "FormalOLP" then
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
  logInfo m!"audited {audited} FormalOLP declarations"
  if !violations.isEmpty then
    for (name, ax) in violations do
      logError m!"{name} depends on disallowed axiom {ax}"
    throwError "FormalOLP axiom audit failed"
  logInfo m!"FormalOLP axiom audit passed"

#audit_formalolp_axioms

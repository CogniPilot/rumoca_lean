import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Build-time axiom audits. Failure is a Lean error, so Lake can cache the
checked module together with its complete import dependency trace. This is
checking infrastructure; it supplies no semantic theorem or proof axiom. -/
namespace ProofAudit
open Lean Elab Command

/-- Keep the same foundation whitelist as the actual-artifact gate. -/
def audit (name : Name) : CommandElabM Unit := do
  let axioms ← collectAxioms name
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in {name}: {dependency}"
  logInfo m!"{name} depends on axioms: {axioms.toList}"

/-- Audit the complete kernel-checked dependency closure of this declaration. -/
elab "#audit " "axioms " name:ident : command => do
  audit (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo name)

end ProofAudit

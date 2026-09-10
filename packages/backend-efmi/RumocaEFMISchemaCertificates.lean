import RumocaEFMIResources
import RumocaEFMI.ZIPCertificateCheck
import ProofAudit.Audit

/-! Kernel-checked encoding and CRC facts for every pinned schema resource.
Lake caches this proof library through the embedded resource dependency. The
larger thread stack is a library build option, not a change of proof authority.
Model-specific archive checks import these facts without recomputing CRCs. -/
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

open Lean Elab Command Rumoca.EFMI

elab "certify_efmi_schemas" : command => do
  let mut payloads : Array (TSyntax `term) := #[]
  for (resource, i) in Resources.schemas.zipIdx do
    let name := `Rumoca.EFMI.SchemaCertificates |>.str s!"resource_{i}"
    StoredZIP.CertificateCheck.certifyCRC name resource.text
    let payload := mkIdent (name.str "payload")
    payloads := payloads.push (← `(term| $payload:ident))
  let texts := mkIdent `Rumoca.EFMI.SchemaCertificates.texts
  elabCommand (← `(command| def $texts:ident : List StoredZIP.Certificate.Text := [$payloads,*]))

certify_efmi_schemas

namespace Rumoca.EFMI.SchemaCertificates

/-- The cached payloads cover exactly the embedded resource texts, in order.
The native certificate builder cannot substitute a different resource list. -/
theorem sources : texts.map (·.source) = Resources.schemas.map (·.text) := by rfl

#audit axioms texts
#audit axioms sources

end Rumoca.EFMI.SchemaCertificates

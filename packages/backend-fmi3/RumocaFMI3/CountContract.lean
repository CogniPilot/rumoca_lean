import RumocaFMI3.CountQueries

/-! Required contracts for the two existing ME count functions, on the same
definition table that is printed into the adapter. Error paths here cover
disabled logging; enabled callback execution is a separate obligation. -/
noncomputable section
namespace Rumoca.FMI3.CountQueries
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory

structure FunctionContract (m : Solve.FMI3Model source) (sigs : List Signature)
    (events : Bool) (text : String) : Prop where
  member : signature events ∈ sigs
  printed : text = (Runtime.function m (signature events)).render
  tokenization : Printer.FunctionTokenization RuntimePrinter.typedefs text
    (Runtime.function m (signature events))
  successful : ∀ heap p buffer kind mode old,
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .getCounts kind mode →
    heap buffer = some ⟨.size, true, old⟩ →
    ∀ behavior, (CCalls.Typed.machine (LiteralPreparation.program m sigs)).Behaves
      (.calling (signature events).name (arguments (some p) (some buffer)) heap .done) behavior ↔
      behavior = .terminates ⟨.integer 0, written events heap buffer⟩
  null : ∀ heap buffer behavior,
    (CCalls.Typed.machine (LiteralPreparation.program m sigs)).Behaves
      (.calling (signature events).name (arguments none buffer) heap .done) behavior ↔
      behavior = .terminates ⟨.integer 3, heap⟩
  rejected : ∀ heap p message buffer kind mode logger,
    static.addresses "Call is not allowed in the current FMI state" = some message →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    (¬ Reference.Allowed .getCounts kind mode) →
    ∀ behavior, (CCalls.Typed.machine (LiteralPreparation.program m sigs)).Behaves
      (.calling (signature events).name (arguments (some p) buffer) heap .done) behavior ↔
      behavior = .terminates ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩
  missing : ∀ heap p message kind mode logger,
    static.addresses "Missing output pointer" = some message →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    Reference.Allowed .getCounts kind mode →
    ∀ behavior, (CCalls.Typed.machine (LiteralPreparation.program m sigs)).Behaves
      (.calling (signature events).name (arguments (some p) none) heap .done) behavior ↔
      behavior = .terminates ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

theorem rendered_contract (m : Solve.FMI3Model source) (sigs : List Signature) (events : Bool)
    (unique : ((LiteralPreparation.functions m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature events ∈ sigs) :
    FunctionContract m sigs events (Runtime.function m (signature events)).render := by
  have defined := LiteralPreparation.function_bound m sigs unique _ member
  have helper := LiteralPreparation.helpers_bound m sigs Runtime.helpers[0] (by simp [Runtime.helpers])
  refine ⟨member, rfl, function_tokenization m events, ?_, ?_, ?_, ?_⟩
  · intro heap p buffer kind mode old hk hm allowed storage behavior
    exact call_behaviors m events _ heap p buffer kind mode old defined hk hm allowed storage behavior
  · intro heap buffer behavior
    exact null_behaviors m events _ heap buffer defined behavior
  · intro heap p message buffer kind mode logger literal hk hm hl hg rejected behavior
    exact rejected_behaviors m events _ heap p message buffer kind mode logger
      defined helper literal hk hm hl hg rejected behavior
  · intro heap p message kind mode logger literal hk hm hl hg allowed behavior
    exact missing_behaviors m events _ heap p message kind mode logger
      defined helper literal hk hm hl hg allowed behavior

end Rumoca.FMI3.CountQueries

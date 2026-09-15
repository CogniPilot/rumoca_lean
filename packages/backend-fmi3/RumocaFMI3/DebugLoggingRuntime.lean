import RumocaFMI3.DebugLoggingEnvironment

/-! Complete public logging behavior in the shared runtime. The error-helper
contracts are conclusions of its actual definition and callback bindings,
never additional execution assumptions in the public contract. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory CBody StaticFactory CStringMemory
open scoped Classical

def Responses (heap : Heap) (p : Address) (pointer : Option Address) (count : UInt64)
    (enabled : Bool) (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (failures : Bool → Transition.Events.Observation E CBody.Result → Prop)
    (behavior : Transition.Events.Observation E CBody.Result) : Prop :=
  if count.toNat = 0 ∨ pointer.isSome = true then
    if ∀ i < count.toNat, Accepted (selected i) (bytes i) (content "logStatus") then
      behavior = .terminates [] ⟨.integer 0, written heap p enabled⟩
    else failures true behavior
  else failures false behavior

def RequestContract [CInterface] (program : CCalls.Events.Program E) (heap : Heap)
    (p : Address) (kind : Kind) (mode : Mode)
    (failures : Bool → Transition.Events.Observation E CBody.Result → Prop) : Prop :=
  ∀ (pointer : Option Address) (count : UInt64) (enabled : Bool) (old : Option Value)
    (selected : Nat → Option Address) (bytes : Nat → List UInt8),
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    (pointer.isSome = true → Entries heap pointer count.toNat selected bytes) →
    heap (p.member "logging") = some ⟨.boolean, true, old⟩ →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) enabled count pointer) heap .done) behavior ↔
      Responses heap p pointer count enabled selected bytes failures behavior

def SuppressedContract [CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (kind : Kind) (mode : Mode) (logger : Option Address) (logging : Bool),
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    (logger = none ∨ logging = false) →
    RequestContract program heap p kind mode (fun _ behavior =>
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩)

def LoggedContract [CInterface] (program : CCalls.Events.Program E) (heap : Heap)
    (category : Address) (messages : Bool → Address) : Prop :=
  ∀ (p logger : Address) (environment : Option Address) (kind : Kind) (mode : Mode)
    (name : String) (foreign : CCalls.Events.External E),
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    RequestContract program heap p kind mode (fun unknown behavior =>
      (∃ events value final,
        foreign.execute (Logging.arguments environment category (messages unknown))
          (LifecycleBodies.writeMode heap p .terminated) events value final ∧
        behavior = .terminates events ⟨.integer 3, final⟩) ∨
      ((∀ events value final,
        ¬ foreign.execute (Logging.arguments environment category (messages unknown))
          (LifecycleBodies.writeMode heap p .terminated) events value final) ∧ behavior = .wrong []))

theorem runtime_suppressed_correct (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (category : Address) (messages : Bool → Address),
      program.internal.definitions signature.name = some (.tree function) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
      literals "logStatus" = some category →
      (∀ unknown, literals (failureMessage unknown) = some (messages unknown)) →
      Contents heap category (content "logStatus") → SuppressedContract program heap := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap category messages defined helper compare literal bound contents
    p kind mode logger logging hm hl hg suppressed pointer count enabled old selected bytes hk modeValue caller storage behavior
  have failed := fun unknown => suppressed_failure_contract
    ((ErrorContext.static objects literals).withRounding header) program heap p (messages unknown)
    (failureMessage unknown) _ logger logging helper (bound unknown) hm hl hg suppressed
  exact call_behaviors (runtime_types header objects literals) program
    (runtime_library header objects literals program compare) heap p category pointer count enabled old
    kind mode defined hk modeValue selected bytes (content "logStatus") literal contents caller storage
    _ _ (failed false) (failed true) behavior

theorem runtime_logged_correct (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (category : Address) (messages : Bool → Address),
      program.internal.definitions signature.name = some (.tree function) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
      literals "logStatus" = some category →
      (∀ unknown, literals (failureMessage unknown) = some (messages unknown)) →
      Contents heap category (content "logStatus") → LoggedContract program heap category messages := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap category messages defined helper compare literal bound contents
    p logger environment kind mode name foreign address external prototype hm hl hg he
    pointer count enabled old selected bytes hk modeValue caller storage behavior
  have failed := fun unknown => logged_failure_contract
    ((ErrorContext.static objects literals).withRounding header) program heap p (messages unknown)
    category logger (failureMessage unknown) environment _ name foreign helper (bound unknown)
    address external prototype literal hm hl hg he
  exact call_behaviors (runtime_types header objects literals) program
    (runtime_library header objects literals program compare) heap p category pointer count enabled old
    kind mode defined hk modeValue selected bytes (content "logStatus") literal contents caller storage
    _ _ (failed false) (failed true) behavior

theorem runtime_null_correct (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions signature.name = some (.tree function) →
      ∀ heap enabled count pointer behavior,
        (CCalls.Events.machine program).Behaves
          (.calling signature.name (arguments none enabled count pointer) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program defined heap enabled count pointer behavior
  exact public_null_behaviors (runtime_types header objects literals) program heap enabled count pointer
    defined rfl rfl behavior

end Rumoca.FMI3.DebugLogging
end

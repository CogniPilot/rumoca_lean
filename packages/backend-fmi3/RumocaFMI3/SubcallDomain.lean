import RumocaFMI3.ReservationOriginRuntime
import RumocaC.CallContextHistory

namespace Rumoca.FMI3.ReservationOrigin
open CTree CMemory CCalls CCalls.Events CCallSites RuntimeLinkage
variable [interface : CInterface] {E : Type}

/-- An admitted non-reservation helper remains in its closed call domain
while a factory is suspended below it. The caller's suffix may contain a
reservation; it is outside this interval and is retained unchanged. -/
theorem subcall_domain (model : Solve.FMI3Model source) (sigs : List Signature)
    (program : Events.Program E) (actual : program.internal = LiteralPreparation.program model sigs)
    (onlyNamed : ∀ name, allowed name = false → NamedOnly program name)
    (permitted : allowed helper = true)
    (entry : before.threads tracked = some (.calling helper args savedHeap outer))
    (path : Transition.Reaches (fun a b => ∃ chosen events,
      Concurrent.Step program a chosen events b ∧ Concurrent.BeforeReturn tracked outer a chosen) before after) :
    ∀ name values heap stack, after.threads tracked = some (.calling name values heap stack) →
      allowed name = true ∧ ∃ innerStack : Typed.Continuation, stack = innerStack.append outer := by
  have start : Context.ThreadReady (Ready Permitted (fun name _ => allowed name = true)) outer tracked before :=
    ⟨.calling helper args savedHeap .done, entry, permitted, True.intro⟩
  have finish := Context.interval_history program (Ready Permitted (fun name _ => allowed name = true))
    (fun _ ready heap => (ready_withHeap _ heap).mpr ready)
    (fun _ _ _ ready _ step => event_ready model sigs program actual onlyNamed ready step) start path
  intro name values heap stack calling
  obtain ⟨innerStack, same, ready⟩ := Context.call_origin finish calling
  exact ⟨ready.1, innerStack, same⟩

/-- Prepared linkage supplies the exact function table and excludes indirect
aliases for reservation. No per-step helper-state annotation is an input. -/
theorem logged_subcall_domain (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ helper args savedHeap outer (before after : Concurrent.State) tracked,
      allowed helper = true → before.threads tracked = some (.calling helper args savedHeap outer) →
      Transition.Reaches (fun a b => ∃ chosen events,
        Concurrent.Step program a chosen events b ∧ Concurrent.BeforeReturn tracked outer a chosen) before after →
      ∀ name values heap stack, after.threads tracked = some (.calling name values heap stack) →
        allowed name = true ∧ ∃ innerStack : Typed.Continuation, stack = innerStack.append outer := by
  intro program helper args savedHeap outer before after tracked permitted entry path
  exact subcall_domain model sigs program rfl
    (fun _ outside => logged_named_only model sigs covered tag boolean size integer double observed range logger effect outside)
    permitted entry path

end Rumoca.FMI3.ReservationOrigin

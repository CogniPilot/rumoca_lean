import RumocaFMI3.FactoryRejectionControl
import RumocaFMI3.StaticFactoryEnvironment
import RumocaC.AtomicScanEntryInvariant

namespace Rumoca.FMI3.FactoryControl
open CTree CMemory CBody CCalls CCallSites

def validationCode (model : Solve.FMI3Model source) (kind : Kind) : List Stmt :=
  FactoryPrefix.validation model :: FactoryPrefix.identityGuard :: StaticFactory.code model.solve kind

def identityCaller (model : Solve.FMI3Model source) (kind : Kind) (args : FactoryArguments.Raw)
    (types : CLoops.Types) : Typed.Continuation :=
  .caller (.declare "fmi3Boolean" "validIdentity")
    (FactoryPrefix.identityGuard :: StaticFactory.code model.solve kind)
    (FactoryArguments.parameters kind args) types "fmi3Instance" .done

def scanCaller (model : Solve.FMI3Model source) (kind : Kind) (args : FactoryArguments.Raw)
    (types : CLoops.Types) : Typed.Continuation :=
  .caller (.declare "size_t" "slot")
    (StaticFactory.guard :: StaticFactory.initializeInstance model.solve kind)
    (FactoryValidation.locals kind args true) types "fmi3Instance" .done

/-- The complete public factory's control phases retain its original
parameters. Scan readiness is established only through the real validation
guard and reservation call. Rejected and post-scan paths are closed to any
further reservation, including arbitrary callback outcomes. -/
inductive Control (model : Solve.FMI3Model source) (kind : Kind) (args : FactoryArguments.Raw)
    (objects : StaticFactory.Objects) : Typed.State → Prop where
  | entry (heap : Heap) : Control model kind args objects
      (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap .done)
  | csGuard (cs : kind = .cs) (types : CLoops.Types) (heap : Heap) : Control model kind args objects
      (.body (.running (FactoryPrefix.entry .cs (validationCode model kind))
        (FactoryArguments.parameters .cs args) types heap) "fmi3Instance" .done)
  | validation (types : CLoops.Types) (heap : Heap) : Control model kind args objects
      (.body (.running (validationCode model kind) (FactoryArguments.parameters kind args) types heap)
        "fmi3Instance" .done)
  | identity (types : CLoops.Types)
      (ready : Context.Suspended FactoryRejection.Closed (identityCaller model kind args types) state) :
      Control model kind args objects state
  | identityGuard (types : CLoops.Types) (valid : Bool) (heap : Heap) : Control model kind args objects
      (.body (.running (FactoryPrefix.identityGuard :: StaticFactory.code model.solve kind)
        (FactoryValidation.locals kind args valid) types heap) "fmi3Instance" .done)
  | capabilityRejected (types : CLoops.Types)
      (ready : FactoryRejection.Control "Events and intermediate updates are unsupported"
        (validationCode model kind) (FactoryArguments.parameters .cs args) types state) :
      Control model kind args objects state
  | identityRejected (types : CLoops.Types)
      (ready : FactoryRejection.Control "Invalid name or instantiation token"
        (StaticFactory.code model.solve kind) (FactoryValidation.locals kind args false) types state) :
      Control model kind args objects state
  | reserve (types : CLoops.Types) (heap : Heap) : Control model kind args objects
      (.body (.running (StaticFactory.code model.solve kind)
        (FactoryValidation.locals kind args true) types heap) "fmi3Instance" .done)
  | scan (types : CLoops.Types)
      (ready : CAtomicScan.ConcurrentInvariant.FullReady objects.flags objects.capacity
        (scanCaller model kind args types) state) : Control model kind args objects state
  | closed (ready : FactoryRejection.Closed state) : Control model kind args objects state

theorem Control.withHeap (ready : Control model kind args objects state) (heap : Heap) :
    Control model kind args objects (Concurrent.withHeap state heap) := by
  cases ready with
  | entry => exact .entry heap
  | csGuard cs types => exact .csGuard cs types heap
  | validation types => exact .validation types heap
  | identity types ready => exact .identity types (Context.suspended_heap ready heap
      (fun state ready heap => (ready_withHeap state heap).mpr ready))
  | identityGuard types valid => exact .identityGuard types valid heap
  | capabilityRejected types ready => exact .capabilityRejected types (ready.withHeap heap)
  | identityRejected types ready => exact .identityRejected types (ready.withHeap heap)
  | reserve types => exact .reserve types heap
  | scan types ready => exact .scan types (ready.withHeap heap)
  | closed ready => exact .closed ((ready_withHeap _ _).mpr ready)

/-- At an actual exchange the exact prepared scan and original factory frame
are recovered from the public-entry invariant, not supplied as helper history. -/
theorem Control.atomic_origin
    (ready : Control model kind args objects (.calling name values heap stack))
    (atomic : name = "atomic_exchange") :
    ∃ types, CAtomicScan.ConcurrentInvariant.FullReady objects.flags objects.capacity
      (scanCaller model kind args types) (.calling name values heap stack) ∧
      ∃ k : Nat, k < objects.capacity ∧
        values = [.pointer (some (objects.flags.index k)), CAtomicBoolean.value true] := by
  cases ready with
  | entry heap => cases kind <;> simp [FactoryArguments.signature, Identity.factoryName] at atomic
  | identity types ready =>
    obtain ⟨_, _, ready⟩ := Context.suspended_call ready
    have forbidden : ReservationOrigin.allowed "atomic_exchange" = false := by decide +kernel
    have allowed := ready.1
    rw [atomic, forbidden] at allowed
    contradiction
  | capabilityRejected types ready | identityRejected types ready =>
    have allowed := ready.call_allowed
    have forbidden : ReservationOrigin.allowed "atomic_exchange" = false := by decide +kernel
    rw [atomic, forbidden] at allowed
    contradiction
  | scan types ready => exact ⟨types, ready, ready.atomic_origin atomic⟩
  | closed ready =>
    have forbidden : ReservationOrigin.allowed "atomic_exchange" = false := by decide +kernel
    have allowed := ready.1
    rw [atomic, forbidden] at allowed
    contradiction

end Rumoca.FMI3.FactoryControl

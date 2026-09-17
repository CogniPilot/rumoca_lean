import RumocaFMI3.FactoryControl
import RumocaFMI3.FactoryAfterScan
import RumocaFMI3.FactoryIdentityResume
import RumocaFMI3.StaticRuntimeLinkage

namespace Rumoca.FMI3.FactoryControl
open CTree CMemory CBody CCalls CCallSites
variable {E : Type}

theorem control_step (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) :
    letI : CInterface := header.interface (StaticFactory.executionInterface objects literals)
    ∀ (model : Solve.FMI3Model source) (kind : Kind) (args : FactoryArguments.Raw) (sigs : List Signature)
      (program : Events.Program E),
      program.internal = LiteralPreparation.program model sigs →
      (∀ name, ReservationOrigin.allowed name = false → NamedOnly program name) →
      program.internal.definitions (FactoryArguments.signature kind).name =
        some (.tree (StaticFactory.function model kind)) →
      ∀ (expected whitespace : Address), literals (token model) = some expected →
      literals " \t\n\r\u000c\u000b" = some whitespace →
      ∀ tag : CAtomicBoolean.Calls.Event → E,
      program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
      ∀ before events after, Control model kind args objects before →
      Events.Step program before events after → Control model kind args objects after := by
  letI : CInterface := header.interface (StaticFactory.executionInterface objects literals)
  intro model kind args sigs program actual onlyNamed defined expected whitespace expectedBound whitespaceBound tag exchange
    before events after ready step
  have closedStep : ∀ before events after, FactoryRejection.Closed before →
      Events.Step program before events after → FactoryRejection.Closed after :=
    fun _ _ _ ready step => ReservationOrigin.event_ready model sigs program actual onlyNamed ready step
  cases ready with
  | entry heap =>
    obtain ⟨types, entered, _, _⟩ := FactoryArguments.call_entry program
      (FactoryPrefix.body model kind (StaticFactory.code model.solve kind)) kind args heap .done
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ defined
    obtain ⟨_, rfl⟩ := Events.internal_unique program entered _ _ step
    cases kind with
    | me => exact .validation types heap
    | cs => exact .csGuard rfl types heap
  | csGuard cs types heap =>
    subst kind
    obtain ⟨_, rfl⟩ := Events.internal_unique program
      (FactoryEntry.coSimulation_guard program (validationCode model .cs) args types heap .done) _ _ step
    cases unsupported : FactoryEntry.unsupported args <;> simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    · exact .validation types heap
    · exact .capabilityRejected types (.dispatch heap)
  | validation types heap =>
    have scope := FactoryArguments.scope kind args
    have entered := Identity.factory_enters program model (token model)
      (FactoryPrefix.identityGuard :: StaticFactory.code model.solve kind)
      (FactoryArguments.parameters kind args) types heap "fmi3Instance" .done
      args.name args.token expected whitespace scope.result scope.helper rfl scope.name scope.token
      expectedBound whitespaceBound
    obtain ⟨_, rfl⟩ := Events.internal_unique program entered _ _ step
    exact .identity types ⟨.calling Identity.function.signature.name
      (Identity.Arguments.values ⟨args.name, args.token, some expected, some whitespace⟩) heap .done,
      rfl, ⟨by change ReservationOrigin.allowed Identity.function.signature.name = true; decide +kernel, True.intro⟩, by simp [Context.Live]⟩
  | identity types ready =>
    by_cases exited : Concurrent.Exit (identityCaller model kind args types) before
    · obtain ⟨value, heap, rfl⟩ := exited
      obtain ⟨valid, _, _, rfl⟩ := FactoryValidation.actual_resume program kind args
        (StaticFactory.code model.solve kind) types heap .done value rfl step
      exact .identityGuard (CLoops.bindType types "validIdentity" .boolean) valid heap
    · exact .identity types (Context.suspended_step program closedStep ready exited step)
  | identityGuard types valid heap =>
    obtain ⟨_, rfl⟩ := FactoryValidation.actual_guard program kind args
      (StaticFactory.code model.solve kind) types heap .done valid step
    cases valid with
    | false => exact .identityRejected types (.dispatch heap)
    | true => exact .reserve types heap
  | capabilityRejected types ready =>
    have scope := FactoryArguments.scope .cs args
    exact .capabilityRejected types (FactoryRejection.control_step model sigs program actual onlyNamed
      args.logger args.logging
      (by simp [resolve, scope.logger]) (by simp [resolve, scope.logging])
      (by simp [resolve, scope.null, constants]; rfl) ready step)
  | identityRejected types ready =>
    have scope := FactoryArguments.scope kind args
    exact .identityRejected types (FactoryRejection.control_step model sigs program actual onlyNamed
      args.logger args.logging
      (by simp [FactoryValidation.locals, CBody.bind, resolve, scope.logger])
      (by simp [FactoryValidation.locals, CBody.bind, resolve, scope.logging])
      (by simp [FactoryValidation.locals, CBody.bind, resolve, scope.null, constants]; rfl) ready step)
  | reserve types heap =>
    obtain ⟨_, rfl⟩ := Events.internal_unique program
      (StaticFactory.header_reserve_entry header objects literals program model.solve kind args types heap .done) _ _ step
    exact .scan types (.entry heap)
  | scan types ready =>
    by_cases exited : Concurrent.Exit (scanCaller model kind args types) before
    · obtain ⟨value, heap, rfl⟩ := exited
      exact .closed (closedStep _ _ _
        (ReservationOrigin.factory_return_closed model.solve kind value heap
          (FactoryValidation.locals kind args true) types) step)
    · exact .scan types (CAtomicScan.ConcurrentInvariant.full_step_ready program tag rfl rfl rfl rfl rfl exchange
        (actual ▸ StaticRuntime.reservation_bound model sigs) objects.bounded ready exited step)
  | closed ready => exact .closed (closedStep _ _ _ ready step)

end Rumoca.FMI3.FactoryControl

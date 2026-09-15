import RumocaFMI3.FactoryValidation
import RumocaFMI3.FactoryScanEntry
import RumocaC.BooleanConversion

namespace Rumoca.FMI3.FactoryValidation
open CTree CMemory CBody CCalls
variable [interface : CInterface] {E : Type}

/-- An actual identity-helper return resumes the saved factory parameters.
The emitted destination's Boolean cast determines the guard value; there is
no assumed successful validation or manufactured post-call locals. -/
theorem actual_resume (program : Events.Program E) (kind : Kind) (args : FactoryArguments.Raw)
    (creation : List Stmt) (types : CLoops.Types) (heap : Heap) (stack : Typed.Continuation)
    (value : Value) (booleanType : interface.types "fmi3Boolean" = some .boolean)
    (step : Events.Step program
      (.returning value heap
        (.caller (.declare "fmi3Boolean" "validIdentity") (FactoryPrefix.identityGuard :: creation)
          (FactoryArguments.parameters kind args) types "fmi3Instance" stack)) events after) :
    ∃ valid : Bool, value.truth = some valid ∧ events = [] ∧
      after = .body (.running (FactoryPrefix.identityGuard :: creation)
        (locals kind args valid) (CLoops.bindType types "validIdentity" .boolean) heap) "fmi3Instance" stack := by
  cases step with
  | internal moved =>
    have fresh := (FactoryArguments.scope kind args).result
    change Typed.resume value heap
      (.caller (.declare "fmi3Boolean" "validIdentity") (FactoryPrefix.identityGuard :: creation)
        (FactoryArguments.parameters kind args) types "fmi3Instance" stack) = some after at moved
    cases cast : convert .boolean value with
    | none => simp [Typed.resume, fresh, booleanType, cast] at moved
    | some result =>
      obtain ⟨valid, truth, rfl⟩ := boolean_conversion cast
      refine ⟨valid, truth, rfl, ?_⟩
      simpa [Typed.resume, fresh, booleanType, cast, locals, boolean] using moved.symm

/-- The actual next guard step selects the validation result's continuation.
Rejection and creation stay distinct; no completed helper semantics are required
for this control and original-parameter fact. -/
theorem actual_guard (program : Events.Program E) (kind : Kind) (args : FactoryArguments.Raw)
    (creation : List Stmt) (types : CLoops.Types) (heap : Heap) (stack : Typed.Continuation)
    (valid : Bool)
    (step : Events.Step program
      (.body (.running (FactoryPrefix.identityGuard :: creation) (locals kind args valid) types heap)
        "fmi3Instance" stack) events after) :
    events = [] ∧ after = .body (.running (remaining creation valid) (locals kind args valid) types heap)
      "fmi3Instance" stack := by
  exact Events.internal_unique program
    (FactoryRejection.identity_guard program creation (locals kind args valid) types heap stack valid
      (by simp [locals, CBody.bind, CBody.resolve])) _ _ step

end Rumoca.FMI3.FactoryValidation

namespace Rumoca.FMI3.FactoryValidation
open CTree CMemory CBody CCalls
variable [interface : CInterface] {E : Type}

/-- The actual saved destination also has an enabled step for every
represented Boolean outcome, preserving its original factory parameters. -/
theorem resume_next (program : Events.Program E) (kind : Kind) (args : FactoryArguments.Raw)
    (creation : List Stmt) (types : CLoops.Types) (heap : Heap) (stack : Typed.Continuation)
    (value : Value) (valid : Bool)
    (booleanType : interface.types "fmi3Boolean" = some .boolean) (truth : value.truth = some valid) :
    Events.internalNext program
      (.returning value heap
        (.caller (.declare "fmi3Boolean" "validIdentity") (FactoryPrefix.identityGuard :: creation)
          (FactoryArguments.parameters kind args) types "fmi3Instance" stack)) =
      some (.body (.running (FactoryPrefix.identityGuard :: creation) (locals kind args valid)
        (CLoops.bindType types "validIdentity" .boolean) heap) "fmi3Instance" stack) := by
  have fresh := (FactoryArguments.scope kind args).result
  simp [Events.internalNext, Typed.nextWith, Typed.resume, fresh, booleanType, convert, truth, locals, boolean]

omit interface in
/-- The source-prepared globals and original parameter frame determine the
reservation call after an actual true identity result. The validation guard
and helper entry are genuine C transitions; no successful slot claim is assumed. -/
theorem header_reservation_after_identity (header : CFenv.Header) (objects : StaticFactory.Objects)
    (literals : CLiteralAddresses) :
    letI : CInterface := header.interface (StaticFactory.executionInterface objects literals)
    ∀ (program : Events.Program E) (model : Solve.Model source) (kind : Kind) (args : FactoryArguments.Raw)
      (types : CLoops.Types) (heap : Heap) (stack : Typed.Continuation) (value : Value),
      value.truth = some true →
      Transition.Reaches (fun s t => Events.internalNext program s = some t)
        (.returning value heap
          (.caller (.declare "fmi3Boolean" "validIdentity")
            (FactoryPrefix.identityGuard :: StaticFactory.code model kind)
            (FactoryArguments.parameters kind args) types "fmi3Instance" stack))
        (.calling CAtomicScan.function.signature.name [.pointer (some objects.flags), .integer objects.capacity] heap
          (.caller (.declare "size_t" "slot") (StaticFactory.guard :: StaticFactory.initializeInstance model kind)
            (locals kind args true) (CLoops.bindType types "validIdentity" .boolean) "fmi3Instance" stack)) := by
  letI : CInterface := header.interface (StaticFactory.executionInterface objects literals)
  intro program model kind args types heap stack value truth
  refine .next (resume_next program kind args (StaticFactory.code model kind) types heap stack value true rfl truth) ?_
  have guarded := FactoryRejection.identity_guard program (StaticFactory.code model kind) (locals kind args true)
    (CLoops.bindType types "validIdentity" .boolean) heap stack true (by simp [locals, CBody.bind, CBody.resolve])
  simp only [↓reduceIte, List.nil_append] at guarded
  exact .next guarded (.next (StaticFactory.header_reserve_entry header objects literals program model kind args
    (CLoops.bindType types "validIdentity" .boolean) heap stack) (.refl _))

end Rumoca.FMI3.FactoryValidation

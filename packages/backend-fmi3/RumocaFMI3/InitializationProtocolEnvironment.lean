import RumocaFMI3.InitializationProtocolHistory
import RumocaFMI3.InitializationProtocolLogging
import RumocaFMI3.InitializationProtocolEventIndicators
import RumocaFMI3.InitializationProtocolEvaluation
import RumocaFMI3.CSRunEnvironment
import RumocaFMI3.MEEnvironment

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CLiteral CMemory StaticFactory CCalls.Events

/-- Creation and every later protocol segment use these contracts for one
prepared table and literal pool. The CS environment includes common lifecycle
calls, shared by both interfaces. No stage supplies a new program identity. -/
structure PreparedContract (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames)) : Prop where
  getter : Float64Environment.PreparedContract model sigs pool
  setter : Float64SetEnvironment.PreparedContract model sigs pool
  counts : ∀ events, CountEnvironment.PreparedContract model sigs events pool
  nominals : NominalEnvironment.PreparedContract model sigs pool
  logging : DebugLogging.PreparedContract model sigs pool
  eventIndicators : EventIndicatorEnvironment.PreparedContract model sigs pool
  cs : CSRunEnvironment.PreparedContract model sigs pool
  me : MEEnvironment.PreparedContract model sigs pool

/-- Every operation contract is derived from the same actual prepared table
and pool. Original caller storage, not a later heap, supplies every request. -/
theorem execution_contract (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames))
    (getter : Float64Environment.PreparedContract model sigs pool)
    (setter : Float64SetEnvironment.PreparedContract model sigs pool)
    (counts : ∀ events, CountEnvironment.PreparedContract model sigs events pool)
    (nominals : NominalEnvironment.PreparedContract model sigs pool)
    (logging : DebugLogging.PreparedContract model sigs pool)
    (eventIndicators : EventIndicatorEnvironment.PreparedContract model sigs pool)
    (evaluation : DiscreteEvaluation.PreparedContract model sigs pool)
    (lifecycle : LifecycleEnvironment.PreparedContract model sigs)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
    program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
    ∀ (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
      (original : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind) (readers : ReadBank),
      Resources objects retained original p buffers readers →
      ExecutionContract model program objects retained owners original (pool.install baseHeap firstBlock signed) p buffers kind readers := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual compare retained owners original p buffers kind readers resources
  obtain ⟨reset, enterDefined, exitDefined, _, _⟩ := lifecycle.execution header objects (pool.addresses firstBlock) program actual
  have initialization := InitializationEnvironment.quiet_correct header objects (pool.addresses firstBlock) model program enterDefined exitDefined
  have get := getter.quiet header Invocation objects firstBlock program actual
  have set := setter.quiet header Invocation objects firstBlock program actual
  refine ⟨resources, ?_⟩
  intro heap state action invariant prepared allowed
  obtain ⟨_, prepared⟩ := prepared
  cases action with
  | access request =>
    have outputs : Float64Buffers.Stored heap buffers :=
      ⟨CStorage.PreservesOn.array invariant.caller _ _ _ resources.outputs.references resources.references,
        CStorage.PreservesOn.array invariant.caller _ _ _ resources.outputs.values resources.values⟩
    exact access_call program get set invariant.stored invariant.ownership outputs resources.separate request prepared allowed
  | reject request =>
    obtain ⟨inputs, guarded, separate⟩ := prepared
    exact rejection_call request header objects model sigs pool getter setter baseHeap firstBlock signed
      program actual heap p buffers kind state owners retained invariant.readonly invariant.stored
      (invariant.caller.request request inputs guarded) separate allowed resources.inPool invariant.ownership invariant.logging
  | counts request =>
    obtain ⟨inputs, guarded, separate⟩ := prepared
    have later := CountAccess.Request.OutputStorage.preserved request inputs invariant.caller guarded
    cases request with
    | get events buffer =>
      obtain ⟨old, storage⟩ := later
      exact count_get_call model program events
        ((counts events).quiet header Invocation objects firstBlock program actual)
        invariant.stored invariant.ownership buffer old storage
        (fun inside => separate buffer inside rfl) allowed
    | reject events missing buffer =>
      exact count_rejection_call events missing buffer header objects model sigs pool (counts events)
        baseHeap firstBlock signed program actual heap p buffers kind state owners retained
        invariant.readonly invariant.stored allowed resources.inPool invariant.ownership invariant.logging
  | nominals request =>
    obtain ⟨inputs, guarded, separate⟩ := prepared
    have later := NominalAccess.Request.OutputStorage.preserved request inputs invariant.caller guarded
    cases request with
    | get buffer =>
      obtain ⟨old, storage⟩ := later
      exact nominal_get_call model program
        (nominals.quiet header Invocation objects firstBlock program actual)
        invariant.stored invariant.ownership buffer old storage
        (fun inside => separate buffer inside rfl) allowed
    | reject access buffer count =>
      exact nominal_rejection_call access buffer count header objects model sigs pool nominals
        baseHeap firstBlock signed program actual heap p buffers kind state owners retained
        invariant.readonly invariant.stored allowed resources.inPool invariant.ownership invariant.logging
  | eventIndicators request =>
    cases request with
    | get buffer =>
      exact event_indicators_get_call model program
        (eventIndicators.quiet header Invocation objects firstBlock program actual)
        invariant.stored invariant.ownership buffer allowed
    | reject access buffer count =>
      exact event_indicators_rejection_call access buffer count header objects model sigs pool eventIndicators
        baseHeap firstBlock signed program actual heap p buffers kind state owners retained
        invariant.readonly invariant.stored allowed resources.inPool invariant.ownership invariant.logging
  | evaluation request =>
    cases request with
    | evaluate =>
      exact evaluation_call model program
        (evaluation.quiet header Invocation objects firstBlock program actual)
        invariant.stored invariant.ownership allowed
    | reject =>
      exact evaluation_rejection_call header objects model sigs pool evaluation
        baseHeap firstBlock signed program actual heap p buffers kind state owners retained
        invariant.readonly invariant.stored allowed resources.inPool invariant.ownership invariant.logging
  | logging request =>
    have inputs : request.Inputs heap := (resources.readerInputs.framed invariant.readerFrame) request prepared
    exact logging_call request header objects model sigs pool logging baseHeap firstBlock signed
      program actual compare heap p buffers kind state owners retained invariant.readonly invariant.stored
      inputs resources.inPool invariant.ownership invariant.logging
  | enter args => exact enter_call model program initialization invariant.stored invariant.ownership args allowed
  | exit => exact exit_call model program initialization invariant.stored invariant.ownership allowed
  | reset => exact reset_call model program reset invariant.stored invariant.ownership

end Rumoca.FMI3.InitializationProtocol
end

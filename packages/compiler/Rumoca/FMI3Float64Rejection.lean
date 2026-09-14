import Rumoca.FMI3InitializationAccess
import RumocaFMI3.Float64RejectionExecution
import RumocaFMI3.LifecycleEnvironment

noncomputable section
namespace Rumoca.FMI3.InitializationAccess
open CMemory

variable {source : AST.Model} {model : Solve.FMI3Model source}

theorem Recovery.completed_source [CInterface] {program : CCalls.Events.Program E}
    (certified : Recovery model program heap p buffers kind args before during beforeEntry atExit)
    (executed : Recovered program heap p buffers args before during events status observation after) :
    events = [] ∧ status = .integer 0 ∧
    observation = expectedObservation model ⟨Binary64.positiveZero⟩ Binary64.positiveZero args before during ∧
    InitializationCalls.SourceInitialized source after p args.start
      (trajectory ⟨Binary64.positiveZero⟩ args before during) ∧
    (∀ candidate, InitializationCalls.SourceInitialized source after p args.start candidate →
      candidate = trajectory ⟨Binary64.positiveZero⟩ args before during) := by
  obtain ⟨events, status, observation, same⟩ := certified.determines executed
  subst after
  obtain ⟨_, initialized, unique⟩ := certified.initialized.completed_source certified.initialized.executes
  exact ⟨events, status, observation, initialized, unique⟩

def RecoverySourceContract [CInterface] (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind) (args : Initialization.Arguments)
    (before during : List Float64Access.Request) : Prop :=
  ∃ beforeEntry atExit,
    Recovery model program heap p buffers kind args before during beforeEntry atExit ∧
    Recovered program heap p buffers args before during [] (.integer 0)
      (expectedObservation model ⟨Binary64.positiveZero⟩ Binary64.positiveZero args before during)
      (InitializationBodies.exitHeap atExit p kind) ∧
    ∀ events status observation after, Recovered program heap p buffers args before during events status observation after →
      events = [] ∧ status = .integer 0 ∧
      observation = expectedObservation model ⟨Binary64.positiveZero⟩ Binary64.positiveZero args before during ∧
      InitializationCalls.SourceInitialized source after p args.start
        (trajectory ⟨Binary64.positiveZero⟩ args before during) ∧
      (∀ candidate, InitializationCalls.SourceInitialized source after p args.start candidate →
        candidate = trajectory ⟨Binary64.positiveZero⟩ args before during)

end Rumoca.FMI3.InitializationAccess

namespace Rumoca.FMI3.Float64Rejection
open CTree CMemory CLiteral CCalls.Events StaticFactory

theorem Returned.source_recovery [CInterface] {buffers : Float64Buffers.Layout} (program : Program E)
    (reset : StaticReset.ExecutionContract program) (initialization : InitializationCalls.QuietExecutionContract program)
    (get : ∀ heap, Float64Calls.QuietExecutionContract model program heap)
    (set : ∀ heap, Float64Set.QuietExecutionContract program heap)
    (returned : Returned objects retained owners request heap p kind state time after)
    (stored : Float64Buffers.Stored heap buffers) (separate : buffers.Separate p)
    (references : ∀ i < buffers.capacity.toNat, Protected objects retained (buffers.references.index i))
    (values : ∀ i < buffers.capacity.toNat, Protected objects retained (buffers.values.index i))
    (args : Initialization.Arguments) (admissible : args.Admissible)
    (before during : List Float64Access.Request)
    (beforeFits : ∀ access ∈ before, access.Fits buffers)
    (beforeAllowed : ∀ access ∈ before, access.StartQuery)
    (duringFits : ∀ access ∈ during, access.Fits buffers)
    (duringAllowed : ∀ access ∈ during, access.Allowed kind .initialization) :
    InitializationAccess.RecoverySourceContract model program after p buffers kind args before during := by
  obtain ⟨beforeEntry, atExit, certified⟩ := returned.recover program reset initialization get set stored separate
    references values args admissible before during beforeFits beforeAllowed duringFits duringAllowed
  exact ⟨beforeEntry, atExit, certified, certified.executes, fun _ _ _ _ => certified.completed_source⟩

/-- One actual source/artifact/table supplies rejected Float64 calls and their
source-correct reset/reinitialization continuation. Request.RuntimeContract
derives Returned from every completed rejected call; no later storage, expected
status, callback return or initialized heap is supplied by the importer. -/
theorem runtime_source (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧
    Float64SetMetadata.Contract a.parsed.ast metadata ∧
    (∀ state d, Source.Equation a.parsed.ast d ↔
      d a.parsed.ast.state = Binary64.value (ModelExchange.derivative a.solve state)) ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      Float64Calls.FunctionContract a.solve.prepareFMI3 sigs
        (Runtime.function a.solve.prepareFMI3 (Float64Calls.signature false)).render Runtime.helpers[1].render ∧
      Float64Set.FunctionContract a.solve.prepareFMI3 sigs
        (Runtime.function a.solve.prepareFMI3 (Float64Calls.signature true)).render ∧
      (∀ request header objects baseHeap firstBlock signed,
        Request.RuntimeContract request header objects a.solve.prepareFMI3 sigs pool baseHeap firstBlock signed) ∧
      (∀ (header : CFenv.Header) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (E : Type) (program : Program E), program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
        ∀ (retained : Address → Prop) (owners : SlotOwners.State objects.capacity) (request : Request)
          (heap after : Heap) (p : Address) (kind : Kind) (state : ModelExchange.State) (time : Binary64.Value)
          (buffers : Float64Buffers.Layout),
        Returned objects retained owners request heap p kind state time after →
        Float64Buffers.Stored heap buffers → buffers.Separate p →
        (∀ i < buffers.capacity.toNat, Protected objects retained (buffers.references.index i)) →
        (∀ i < buffers.capacity.toNat, Protected objects retained (buffers.values.index i)) →
        ∀ (args : Initialization.Arguments) (before during : List Float64Access.Request),
        args.Admissible → (∀ access ∈ before, access.Fits buffers) → (∀ access ∈ before, access.StartQuery) →
        (∀ access ∈ during, access.Fits buffers) → (∀ access ∈ during, access.Allowed kind .initialization) →
        InitializationAccess.RecoverySourceContract a.solve.prepareFMI3 program after p buffers kind args before during) := by
  obtain ⟨sigs, unique, resetMember, printed, _, functions, _, _, _, ready, _, _, _, _, _, _, getter, setter,
    initialization, _, _, runtime, termination, _⟩ := build.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have getPrepared := Float64Environment.prepared_correct a.solve.prepareFMI3 sigs unique getter.member getter.numerical.fresh made
  have setPrepared := Float64SetEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique setter.member made
  have lifecycle : LifecycleEnvironment.PreparedContract a.solve.prepareFMI3 sigs :=
    ⟨LiteralPreparation.function_bound _ sigs unique _ resetMember,
      by rw [← InitializationCalls.function_eq a.solve.prepareFMI3]; exact LiteralPreparation.function_bound _ sigs unique _ initialization.enterMember,
      LiteralPreparation.function_bound _ sigs unique _ initialization.exitMember,
      LiteralPreparation.function_bound _ sigs unique _ termination.member, runtime.release_defined⟩
  refine ⟨compiled, build.numerical, Float64Metadata.artifact_variables _ _ build.metadata,
    Float64SetMetadata.artifact_state _ _ build.metadata, derivative_value_source a.solve,
    sigs, pool, made, printed, functions, getter, setter, ?_, ?_⟩
  · intro request header objects baseHeap firstBlock signed
    exact request.execution header objects a.solve.prepareFMI3 sigs pool getPrepared setPrepared baseHeap firstBlock signed
  · intro header objects firstBlock
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    intro E program actual retained owners request heap after p kind state time buffers returned stored separate references values
      args before during admissible beforeFits beforeAllowed duringFits duringAllowed
    obtain ⟨reset, enterDefined, exitDefined, _, _⟩ := lifecycle.execution header objects (pool.addresses firstBlock) program actual
    have initialization := InitializationEnvironment.quiet_correct header objects (pool.addresses firstBlock)
      a.solve.prepareFMI3 program enterDefined exitDefined
    exact returned.source_recovery program reset initialization
      (getPrepared.quiet header E objects firstBlock program actual) (setPrepared.quiet header E objects firstBlock program actual)
      stored separate references values args admissible before during beforeFits beforeAllowed duringFits duringAllowed

end Rumoca.FMI3.Float64Rejection
end

import RumocaFMI3.InitializationAccess
import Rumoca.FMI3Float64Environment
import Rumoca.FMI3InitializationSemantics

noncomputable section
namespace Rumoca.FMI3.InitializationAccess
open CTree CMemory Float64Buffers Float64Access StaticFactory

variable {source : AST.Model} {model : Solve.FMI3Model source}

def trajectory (state : ModelExchange.State) (args : Initialization.Arguments) (before during : List Request) : ℝ → ℝ :=
  Initialization.trajectory (Binary64.value args.start) (Binary64.value (finalState during (finalState before state)).x)

/-- Every completed actual initialization script selects the unique source
IVP from the state after its intervening host writes. -/
theorem Certificate.completed_source [CInterface] {program : CCalls.Events.Program E}
    (certified : Certificate model program p buffers args kind state time heap before during beforeEntry atExit)
    (executed : Executed program p buffers args heap before during observation after) :
    observation = expectedObservation model state time args before during ∧
    InitializationCalls.SourceInitialized source after p args.start (trajectory state args before during) ∧
    (∀ candidate, InitializationCalls.SourceInitialized source after p args.start candidate →
      candidate = trajectory state args before during) := by
  obtain ⟨observed, rfl⟩ := certified.determines executed
  exact ⟨observed, InitializationCalls.model_source_initialized source _ p args.start _
    model.solve.dae.flat.resolved certified.instanceStored.represented,
    fun _ initialized => InitializationCalls.source_initialized_unique initialized certified.instanceStored.represented⟩

def SourceContract [CInterface] (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (p : Address) (buffers : Layout) (args : Initialization.Arguments) (kind : Kind)
    (state : ModelExchange.State) (time : Binary64.Value) (heap : Heap) (before during : List Request) : Prop :=
  ∃ beforeEntry atExit,
    Certificate model program p buffers args kind state time heap before during beforeEntry atExit ∧
    Executed program p buffers args heap before during (expectedObservation model state time args before during)
      (InitializationBodies.exitHeap atExit p kind) ∧
    ∀ observation after, Executed program p buffers args heap before during observation after →
      observation = expectedObservation model state time args before during ∧
      InitializationCalls.SourceInitialized source after p args.start (trajectory state args before during) ∧
      (∀ candidate, InitializationCalls.SourceInitialized source after p args.start candidate →
        candidate = trajectory state args before during)

theorem source_contract [CInterface] (program : CCalls.Events.Program E)
    (initialization : InitializationCalls.QuietExecutionContract program)
    (get : ∀ heap, Float64Calls.QuietExecutionContract model program heap)
    (set : ∀ heap, Float64Set.QuietExecutionContract program heap)
    (stored : Instance heap p kind .instantiated state time)
    (entryStored : InitializationCalls.EntryStorage heap p)
    (buffersStored : Stored heap buffers) (separate : buffers.Separate p)
    (args : Initialization.Arguments) (admissible : args.Admissible)
    (before during : List Request)
    (beforeFits : ∀ request ∈ before, request.Fits buffers)
    (beforeAllowed : ∀ request ∈ before, request.StartQuery)
    (duringFits : ∀ request ∈ during, request.Fits buffers)
    (duringAllowed : ∀ request ∈ during, request.Allowed kind .initialization) :
    SourceContract model program p buffers args kind state time heap before during := by
  obtain ⟨beforeEntry, atExit, certified⟩ := initialization_history program initialization get set stored
    entryStored buffersStored separate args admissible before during beforeFits beforeAllowed duringFits duringAllowed
  exact ⟨beforeEntry, atExit, certified, certified.executes, fun _ _ => certified.completed_source⟩

/-- Actual source compilation, numerical C, XML state/reference metadata and
the emitted adapter's one function table supply the whole accepted script.
The caller supplies original typed storage and a pure request history; future
heaps and successful target executions are constructed by the theorem. -/
theorem runtime_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧
    Float64SetMetadata.Contract a.parsed.ast metadata ∧
    (∀ state d, Source.Equation a.parsed.ast d ↔
      d a.parsed.ast.state = Binary64.value (ModelExchange.derivative a.solve state)) ∧
    ∃ sigs, ∃ pool : CLiteral.Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap CLiteral.functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      ∀ (E : Type) (header : CFenv.Header) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
          ∀ (heap : Heap) (p : Address) (kind : Kind) (state : ModelExchange.State)
            (time : Binary64.Value) (buffers : Layout) (args : Initialization.Arguments)
            (before during : List Request),
            Instance heap p kind .instantiated state time → InitializationCalls.EntryStorage heap p →
            Stored heap buffers → buffers.Separate p → args.Admissible →
            (∀ request ∈ before, request.Fits buffers) → (∀ request ∈ before, request.StartQuery) →
            (∀ request ∈ during, request.Fits buffers) → (∀ request ∈ during, request.Allowed kind .initialization) →
            SourceContract a.solve.prepareFMI3 program p buffers args kind state time heap before during := by
  obtain ⟨sigs, unique, _, printed, _, grammar, _, _, _, ready, _, _, _, _, _, _, getter, setter, initialization, _⟩ :=
    contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have getPrepared := Float64Environment.prepared_correct a.solve.prepareFMI3 sigs unique getter.member getter.numerical.fresh made
  have setPrepared := Float64SetEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique setter.member made
  refine ⟨compiled, contract.numerical, Float64Metadata.artifact_variables _ _ contract.metadata,
    Float64SetMetadata.artifact_state _ _ contract.metadata, derivative_value_source a.solve,
    sigs, pool, made, printed, grammar, ?_⟩
  intro E header objects firstBlock
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program actual heap p kind state time buffers args before during stored entryStored buffersStored separate
    admissible beforeFits beforeAllowed duringFits duringAllowed
  have enterDefined : program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) := by
    rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
    exact LiteralPreparation.function_bound _ sigs unique _ initialization.enterMember
  have exitDefined : program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function a.solve.prepareFMI3 InitializationExit.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound _ sigs unique _ initialization.exitMember
  exact source_contract program
    (InitializationEnvironment.quiet_correct header objects literals a.solve.prepareFMI3 program enterDefined exitDefined)
    (getPrepared.quiet header E objects firstBlock program actual)
    (setPrepared.quiet header E objects firstBlock program actual)
    stored entryStored buffersStored separate args admissible before during beforeFits beforeAllowed duringFits duringAllowed

end Rumoca.FMI3.InitializationAccess
end

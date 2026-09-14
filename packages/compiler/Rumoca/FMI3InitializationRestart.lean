import Rumoca.FMI3InitializationProtocol
import RumocaFMI3.InitializationProtocolRestart

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory StaticFactory CCalls.Events CLiteral CTree

variable {source : AST.Model} {model : Solve.FMI3Model source}

/-- Reset returns from a simulation or failed state to the existing
initialization protocol. It retains the original caller-memory origin. -/
structure RestartSourceContract [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals heap : Heap) (p : Address) (buffers : Float64Buffers.Layout)
    (kind : Kind) (final : State) (actions : List Action) : Prop where
  resetCall : ∀ behavior, (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, Reset.finalHeap heap p⟩
  initialized : SourceContract model program objects retained owners original literals (Reset.finalHeap heap p)
    p buffers kind State.reset final actions
  readonly : CReadOnly.Preserves heap (Reset.finalHeap heap p)
  retains : Retains p heap (Reset.finalHeap heap p)

theorem RestartSourceContract.progress [CInterface] {program : Program Invocation}
    (certified : RestartSourceContract model program objects retained owners original literals heap p buffers kind final actions) :
    (∃ observed after checkpoints, Completed program p buffers heap (.reset :: actions) observed after checkpoints) ∨
    Stopped program p buffers heap (.reset :: actions) := by
  have called : Action.reset.Behaves program heap p buffers (.terminates [] ⟨.integer 0, Reset.finalHeap heap p⟩) :=
    ⟨heap, rfl, (certified.resetCall _).mpr rfl⟩
  rcases certified.initialized.progress with ⟨observed, after, checkpoints, completed⟩ | stopped
  · exact Or.inl ⟨_, after, _, .cons called completed⟩
  · exact Or.inr (.later called stopped)

/-- Every raw reset-and-initialization execution determines the reset result,
all later observations and the source IVP at each actual exit checkpoint. -/
theorem RestartSourceContract.completed [CInterface] {program : Program Invocation}
    (certified : RestartSourceContract model program objects retained owners original literals heap p buffers kind final actions)
    (executed : Completed program p buffers heap (.reset :: actions) observed after checkpoints) :
    (∃ values, observed = Float64Access.Observation.ok (fun _ => none) :: values ∧
      Observed model State.reset actions values) ∧
    List.Forall₂ (SourceCheckpoint source p) (exitStates State.reset actions) checkpoints ∧
    Invariant program objects retained owners original literals after p kind final ∧
    CReadOnly.Preserves heap after ∧ Retains p heap after ∧
    (∀ q, Float64Rejection.Protected objects retained q → Untouched p buffers actions q → after q = heap q) := by
  cases executed with
  | cons called following =>
    obtain ⟨ready, prepared, performed⟩ := called
    have same : heap = ready := Option.some.inj prepared
    subst ready
    have outcome := (certified.resetCall _).mp performed
    cases outcome
    obtain ⟨observations, exits, invariant, readonly, retains, frame⟩ := certified.initialized.completed _ _ _ following
    refine ⟨⟨_, rfl, observations⟩, exits, invariant, certified.readonly.trans readonly,
      (fun name outside => (retains name outside).trans (certified.retains name outside)), ?_⟩
    intro q guarded untouched
    exact (frame q guarded untouched).trans (StaticReset.record_frame heap p q untouched.1)

theorem restart_source [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {kind : Kind} {mode : Mode}
    (model : Solve.FMI3Model source) (reset : StaticReset.ExecutionContract program)
    (storage : Reset.Storage heap p)
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code))
    (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (caller : CallerStorage objects retained original heap)
    (literalFrame : CReadOnly.Preserves literals heap) (logging : LogPolicy program objects retained heap p)
    (compileProtocol : ∀ next, Invariant program objects retained owners original literals next p kind State.reset →
      SourceContract model program objects retained owners original literals next p buffers kind State.reset final actions) :
    RestartSourceContract model program objects retained owners original literals heap p buffers kind final actions := by
  obtain ⟨called, invariant, readonly, retains⟩ := reset_invariant model reset storage kindValue modeValue
    represented caller literalFrame logging
  exact ⟨called, compileProtocol _ invariant, readonly, retains⟩

/-- The printed source/artifact environment supplies reset and the reusable
protocol for any later heap justified by the simulation invariants. -/
theorem runtime_restart_source (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧ Float64SetMetadata.Contract a.parsed.ast metadata ∧
    (∀ state d, Source.Equation a.parsed.ast d ↔
      d a.parsed.ast.state = Binary64.value (ModelExchange.derivative a.solve state)) ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      ∀ (header : CFenv.Header) (objects : Objects) (baseHeap : Heap) (firstBlock : Nat) (signed : Bool),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : Program Invocation), program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
        ∀ (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
          (original heap : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind) (mode : Mode)
          (final : State) (actions : List Action),
          Resources objects retained original p buffers → Reset.Storage heap p →
          load heap (p.member "kind") = some (.integer kind.code) →
          load heap (p.member "mode") = some (.integer mode.code) →
          SlotOwners.Represents objects.flagsBlock heap owners → CallerStorage objects retained original heap →
          CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap → LogPolicy program objects retained heap p →
          ReferenceTrace kind State.reset actions final →
          (∀ action ∈ actions, action.Prepared objects retained original p buffers) →
          RestartSourceContract a.solve.prepareFMI3 program objects retained owners original
            (pool.install baseHeap firstBlock signed) heap p buffers kind final actions := by
  obtain ⟨compiled, numerical, metadataVariables, writable, equation, sigs, pool, made, printed, functions, lifecycle, certify⟩ :=
    runtime_source compiled build
  refine ⟨compiled, numerical, metadataVariables, writable, equation, sigs, pool, made, printed, functions, ?_⟩
  intro header objects baseHeap firstBlock signed
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual retained owners original heap p buffers kind mode final actions resources storage
    kindValue modeValue represented caller literalFrame logging reference prepared
  obtain ⟨reset, _, _, _, _⟩ := lifecycle.execution header objects (pool.addresses firstBlock) program actual
  exact restart_source a.solve.prepareFMI3 reset storage kindValue modeValue represented caller literalFrame logging
    (fun next invariant => certify header objects baseHeap firstBlock signed program actual retained owners original next p buffers
      kind State.reset final actions resources invariant reference prepared)

end Rumoca.FMI3.InitializationProtocol
end

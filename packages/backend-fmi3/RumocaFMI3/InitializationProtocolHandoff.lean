import RumocaFMI3.InitializationProtocolHistory
import RumocaFMI3.MENumericalInitialization
import RumocaFMI3.CSRunState

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory StaticFactory
variable {readers : ReadBank}

def MEOutputsGuarded (objects : Objects) (retained : Address → Prop)
    (addresses : String → Address) (buffer : Address) : Prop :=
  (∀ name ∈ DiscreteCalls.names, Float64Rejection.Protected objects retained (addresses name)) ∧
    Float64Rejection.Protected objects retained buffer

def CSOutputsGuarded (objects : Objects) (retained : Address → Prop) (buffers : StepEntry.Buffers) : Prop :=
  Float64Rejection.Protected objects retained buffers.event ∧
    Float64Rejection.Protected objects retained buffers.terminate ∧
    Float64Rejection.Protected objects retained buffers.early ∧
    Float64Rejection.Protected objects retained buffers.last

theorem CallerStorage.me_outputs (kept : CallerStorage objects retained original heap)
    (outputs : MENumericalHistory.CallerStorage original p addresses buffer)
    (guarded : MEOutputsGuarded objects retained addresses buffer) :
    MENumericalHistory.CallerStorage heap p addresses buffer := by
  have controls : MEHistory.Buffers heap addresses := by
    intro layout member
    obtain ⟨old, cell⟩ := outputs.controls layout member
    exact CStorage.PreservesOn.cell kept (guarded.1 layout.1 (List.mem_map.mpr ⟨layout, member, rfl⟩)) cell
  obtain ⟨old, cell⟩ := outputs.bufferCell
  exact ⟨controls, outputs.outside, CStorage.PreservesOn.cell kept guarded.2 cell,
    outputs.bufferOutside, outputs.bufferSeparate⟩

theorem CallerStorage.cs_outputs (kept : CallerStorage objects retained original heap)
    (outputs : StepArguments.Storage original p buffers)
    (guarded : CSOutputsGuarded objects retained buffers) : StepArguments.Storage heap p buffers := by
  have cell (q : Address) (type : CType) (inside : Float64Rejection.Protected objects retained q)
      (stored : ∃ old, original q = some ⟨type, true, old⟩) : ∃ old, heap q = some ⟨type, true, old⟩ := by
    obtain ⟨old, found⟩ := stored
    exact CStorage.PreservesOn.cell kept inside found
  exact ⟨cell _ _ guarded.1 outputs.event, cell _ _ guarded.2.1 outputs.terminate,
    cell _ _ guarded.2.2.1 outputs.early, cell _ _ guarded.2.2.2 outputs.last,
    outputs.outsideEvent, outputs.outsideTerminate, outputs.outsideEarly, outputs.outsideLast⟩

def meReference (state : State) (args : Initialization.Arguments) : MENumericalHistory.ReferenceState :=
  MENumericalHistory.ReferenceState.initial args state.value.x

def csReference (state : State) (args : Initialization.Arguments) : CSRun.Reference :=
  ⟨state.value.x, args.start, ⟨args.start, 0⟩, args.stopTime, .step⟩

theorem Stored.me_ready (stored : Stored heap p .me state) (phase : state.phase = .initialized args)
    (outputs : MENumericalHistory.CallerStorage heap p addresses buffer) :
    MENumericalHistory.Stored heap p (Time.Clock.initial args.start) (meReference state args) addresses buffer := by
  have configured : args.Admissible ∧ state.time = args.start ∧ Setup heap p args := by
    simpa only [phase, Phase.Configured] using stored.configured
  obtain ⟨admissible, _, setup⟩ := configured
  refine ⟨⟨stored.instanceStored.kind, ?_, setup.clock, Time.initial_represents args.start args.stopTime,
    stored.instanceStored.represented, ?_, ?_, outputs.controls, outputs.outside⟩,
    stored.instanceStored.state, outputs.bufferCell, outputs.bufferOutside, outputs.bufferSeparate⟩
  · simpa only [phase, Phase.mode, me_initialization] using stored.instanceStored.mode
  · change load heap (p.member "stopDefined") = some (CBody.boolean args.stopTime.isSome)
    simpa only [Initialization.stopTime_defined args admissible] using setup.stopDefined
  · intro limit selected
    simpa only [Value.finite, Initialization.stopTime_bits args admissible limit selected] using setup.stop

theorem Stored.cs_ready (model : Solve.Model source) (stored : Stored heap p .cs state)
    (phase : state.phase = .initialized args) (outputs : StepArguments.Storage heap p buffers) :
    CSRun.Stored model heap p buffers (csReference state args) := by
  have configured : args.Admissible ∧ state.time = args.start ∧ Setup heap p args := by
    simpa only [phase, Phase.Configured] using stored.configured
  obtain ⟨admissible, _, setup⟩ := configured
  refine ⟨stored.instanceStored.kind, ?_, setup.clock.time, stored.instanceStored.state,
    ?_, ?_, stored.reset, outputs⟩
  · simpa only [phase, Phase.mode, cs_initialization] using stored.instanceStored.mode_loaded
  · change load heap (p.member "stopDefined") = some (CBody.boolean args.stopTime.isSome)
    simpa only [Initialization.stopTime_defined args admissible] using setup.stopDefined
  · intro limit selected
    simpa only [Value.finite, Initialization.stopTime_bits args admissible limit selected] using setup.stop

theorem Invariant.me_ready [CInterface] {program : CCalls.Events.Program CCalls.Events.Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity}
    (invariant : Invariant program objects retained owners original literals heap p .me state readers)
    (phase : state.phase = .initialized args)
    (outputs : MENumericalHistory.CallerStorage original p addresses buffer)
    (guarded : MEOutputsGuarded objects retained addresses buffer) :
    MENumericalHistory.Stored heap p (Time.Clock.initial args.start) (meReference state args) addresses buffer :=
  invariant.stored.me_ready phase (invariant.caller.me_outputs outputs guarded)

theorem Invariant.cs_ready [CInterface] {program : CCalls.Events.Program CCalls.Events.Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} (model : Solve.Model source)
    (invariant : Invariant program objects retained owners original literals heap p .cs state readers)
    (phase : state.phase = .initialized args) (outputs : StepArguments.Storage original p buffers)
    (guarded : CSOutputsGuarded objects retained buffers) :
    CSRun.Stored model heap p buffers (csReference state args) :=
  invariant.stored.cs_ready model phase (invariant.caller.cs_outputs outputs guarded)

end Rumoca.FMI3.InitializationProtocol
end

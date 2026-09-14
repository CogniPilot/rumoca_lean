import RumocaFMI3.InitializationProtocolStorage

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory CBody StaticFactory CCalls.Events

def Retains (p : Address) (before after : Heap) : Prop :=
  ∀ name, name ∉ InitializationAccess.writtenFields → after (p.member name) = before (p.member name)

def Action.Outside (action : Action) (q : Address) : Prop :=
  match action with
  | .reject request => request.Outside q
  | _ => True

structure Result (objects : Objects) (retained : Address → Prop)
    (owners : SlotOwners.State objects.capacity) (p : Address) (buffers : Float64Buffers.Layout)
    (heap after : Heap) (kind : Kind) (state : State) (action : Action) : Prop where
  stored : Stored after p kind (action.next state)
  ownership : SlotOwners.Represents objects.flagsBlock after owners
  caller : CallerStorage objects retained heap after
  readonly : CReadOnly.Preserves heap after
  retains : Retains p heap after
  frame : ∀ q, Float64Rejection.Protected objects retained q → ¬ p.InRecord q →
    Float64Access.Outside buffers q → action.Outside q → after q = heap q

/-- Both returning branches and the modeled blocked logger outcome have an
actual execution. No expected status or future heap is an input premise. -/
structure CallContract [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (p : Address) (buffers : Float64Buffers.Layout) (heap : Heap) (kind : Kind) (state : State) (action : Action) : Prop where
  progress : (∃ events status after, action.Behaves program heap p buffers (.terminates events ⟨status, after⟩)) ∨
    action.Behaves program heap p buffers (.wrong [])
  returned : ∀ events status after, action.Behaves program heap p buffers (.terminates events ⟨status, after⟩) →
    action.Observed model state ⟨events, status, action.readback after buffers⟩ ∧
    Result objects retained owners p buffers heap after kind state action

variable {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem CallContract.quiet [CInterface] {program : Program Invocation}
    (prepared : action.hostRun heap buffers = some ready)
    (called : ∀ behavior, (machine program).Behaves
      (.calling (action.call p buffers).1 (action.call p buffers).2 ready .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, after⟩)
    (observed : action.Observed model state ⟨[], .integer 0, action.readback after buffers⟩)
    (result : Result objects retained owners p buffers heap after kind state action) :
    CallContract model program objects retained owners p buffers heap kind state action := by
  refine ⟨Or.inl ⟨[], .integer 0, after, ready, prepared, (called _).mpr rfl⟩, ?_⟩
  intro events status next executed
  obtain ⟨actualReady, actualPreparation, executed⟩ := executed
  have same := Option.some.inj (prepared.symm.trans actualPreparation)
  subst actualReady
  have returned := (called _).mp executed
  cases returned
  exact ⟨observed, result⟩

theorem Result.ordinary
    (stored : Stored after p kind (action.next state))
    (ownersStored : SlotOwners.Represents objects.flagsBlock heap owners)
    (storage : CStorage.Preserves heap after) (atomic : CAtomicBoolean.Preserves heap after)
    (readonly : CReadOnly.Preserves heap after) (retains : Retains p heap after)
    (frame : ∀ q, ¬ p.InRecord q → Float64Access.Outside buffers q → after q = heap q) :
    Result objects retained owners p buffers heap after kind state action :=
  ⟨stored, SlotOwners.ordinary_preserves ownersStored atomic, CallerStorage.ordinary storage,
    readonly, retains, fun q _ notRecord outside _ => frame q notRecord outside⟩

theorem access_call [CInterface] (program : Program Invocation)
    (get : ∀ heap, Float64Calls.QuietExecutionContract model program heap)
    (set : ∀ heap, Float64Set.QuietExecutionContract program heap)
    (stored : Stored heap p kind state) (ownersStored : SlotOwners.Represents objects.flagsBlock heap owners)
    (outputs : Float64Buffers.Stored heap buffers) (separate : buffers.Separate p)
    (request : Float64Access.Request) (fits : request.Fits buffers)
    (allowed : (Action.access request).Allowed kind state) :
    CallContract model program objects retained owners p buffers heap kind state (.access request) := by
  have permitted : request.Allowed kind (state.phase.mode kind) := by
    cases phase : state.phase with
    | instantiated => exact InitializationAccess.start_allowed request kind (by simpa [Action.Allowed, phase] using allowed)
    | initializing args => simpa [Action.Allowed, phase, Phase.mode] using allowed
    | initialized args | failed => simp [Action.Allowed, phase] at allowed
  obtain ⟨prepared, called, instanceAfter, _, observed, storage, readonly, frame⟩ :=
    Float64Access.step program get set request stored.instanceStored outputs fits separate permitted
  have fields (name : String) := frame (p.member name) (Ne.symm (HistoryBodies.state_ne_field p name))
    (Float64Access.instance_outside separate rfl)
  exact CallContract.quiet prepared called
    (by simp only [Action.Observed, Action.readback, request.readback_correct observed, Float64Access.Observation.ok])
    (Result.ordinary (stored.access request instanceAfter storage fields) ownersStored storage
      (request.after_atomic model stored.instanceStored outputs fits separate) readonly (fun name _ => fields name)
      (fun q notRecord outside => frame q
        (fun same => notRecord (same ▸ (p.member_in_record "model").member "x")) outside))

theorem enter_call [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (initialization : InitializationCalls.QuietExecutionContract program)
    (stored : Stored heap p kind state) (ownersStored : SlotOwners.Represents objects.flagsBlock heap owners)
    (args : Initialization.Arguments) (allowed : (Action.enter args).Allowed kind state) :
    CallContract model program objects retained owners p buffers heap kind state (.enter args) := by
  obtain ⟨phase, admissible⟩ := allowed
  have called := initialization.enter heap p args kind admissible (stored.entry phase) stored.instanceStored.kind
  have memory := InitializationStorage.entered heap p args kind admissible (stored.entry phase) stored.instanceStored.kind
  have frame (q : Address) (different : ∀ name ∈ InitializationAccess.writtenFields, q ≠ p.member name) :=
    InitializationEntry.frame heap p q args (different "time" (by simp [InitializationAccess.writtenFields]))
      (different "timeMin" (by simp [InitializationAccess.writtenFields]))
      (different "eventTime" (by simp [InitializationAccess.writtenFields]))
      (different "lastCompleted" (by simp [InitializationAccess.writtenFields]))
      (different "stop" (by simp [InitializationAccess.writtenFields]))
      (different "stopDefined" (by simp [InitializationAccess.writtenFields]))
      (different "mode" (by simp [InitializationAccess.writtenFields]))
  exact CallContract.quiet rfl called rfl
    (Result.ordinary (stored.entered args phase admissible) ownersStored memory.1 memory.2
      (termination_preserves ((called _).mpr rfl))
      (fun name outside => frame _ (fun other member same => outside ((Address.member_inj _ _ _).mp same ▸ member)))
      (fun q notRecord _ => frame q (fun name _ same => notRecord (same ▸ p.member_in_record name))))

theorem exit_call [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (initialization : InitializationCalls.QuietExecutionContract program)
    (stored : Stored heap p kind state) (ownersStored : SlotOwners.Represents objects.flagsBlock heap owners)
    (allowed : Action.exit.Allowed kind state) :
    CallContract model program objects retained owners p buffers heap kind state .exit := by
  obtain ⟨args, phase⟩ := allowed
  have mode : heap (p.member "mode") = some ⟨.int32, true, some (.integer 1)⟩ := by
    simpa only [phase, Phase.mode, Mode.code] using stored.instanceStored.mode
  have called := initialization.exit heap p kind stored.instanceStored.kind mode
  have memory := InitializationStorage.exited heap p kind mode
  exact CallContract.quiet rfl called rfl
    (Result.ordinary (stored.exited phase) ownersStored memory.1 memory.2
      (termination_preserves ((called _).mpr rfl))
      (fun name outside => InitializationBodies.exit_frame heap p (p.member name) kind (by
        intro same
        apply outside
        have equal := (Address.member_inj _ _ _).mp same
        simp [InitializationAccess.writtenFields, equal]))
      (fun q notRecord _ => InitializationBodies.exit_frame heap p q kind
        (fun same => notRecord (same ▸ p.member_in_record "mode"))))

theorem reset_call [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (reset : StaticReset.ExecutionContract program)
    (stored : Stored heap p kind state) (ownersStored : SlotOwners.Represents objects.flagsBlock heap owners) :
    CallContract model program objects retained owners p buffers heap kind state .reset := by
  have called := reset.successful heap p kind _ stored.reset stored.instanceStored.kind stored.instanceStored.mode_loaded
  have memory := Reset.preserves model heap p kind _ stored.reset stored.instanceStored.kind stored.instanceStored.mode_loaded
  exact CallContract.quiet rfl called rfl
    (Result.ordinary (stored.reset_done model) ownersStored memory.1 memory.2
      (termination_preserves ((called _).mpr rfl))
      (Reset.retained_field heap p) (fun q notRecord _ => StaticReset.record_frame heap p q notRecord))

end Rumoca.FMI3.InitializationProtocol
end

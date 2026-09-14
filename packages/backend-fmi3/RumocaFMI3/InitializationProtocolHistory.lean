import RumocaFMI3.InitializationProtocolCounts
import RumocaFMI3.InitializationProtocolNominals
import RumocaFMI3.LifecycleEnvironment

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory CBody StaticFactory CCalls.Events CLiteral

structure Resources (objects : Objects) (retained : Address → Prop) (original : Heap)
    (p : Address) (buffers : Float64Buffers.Layout) : Prop where
  outputs : Float64Buffers.Stored original buffers
  separate : buffers.Separate p
  inPool : p.block = objects.instances.block
  references : ∀ i < buffers.capacity.toNat, Float64Rejection.Protected objects retained (buffers.references.index i)
  values : ∀ i < buffers.capacity.toNat, Float64Rejection.Protected objects retained (buffers.values.index i)

def Action.Prepared (action : Action) (objects : Objects) (retained : Address → Prop)
    (original : Heap) (p : Address) (buffers : Float64Buffers.Layout) : Prop :=
  match action with
  | .access request => request.Fits buffers
  | .reject request => request.TransferStorage original ∧ RequestGuarded request objects retained ∧
      ∀ q, p.InRecord q → request.Outside q
  | .counts request => request.OutputStorage original ∧
      request.Guarded (Float64Rejection.Protected objects retained) ∧
      ∀ q, p.InRecord q → request.Outside q
  | .nominals request => request.OutputStorage original ∧
      request.Guarded (Float64Rejection.Protected objects retained) ∧
      ∀ q, p.InRecord q → request.Outside q
  | _ => True

structure Invariant [CInterface] (program : Program Invocation) (objects : Objects) (retained : Address → Prop)
    (owners : SlotOwners.State objects.capacity) (original literals heap : Heap)
    (p : Address) (kind : Kind) (state : State) : Prop where
  stored : Stored heap p kind state
  ownership : SlotOwners.Represents objects.flagsBlock heap owners
  caller : CallerStorage objects retained original heap
  readonly : CReadOnly.Preserves literals heap
  logging : LogPolicy program objects retained heap p

variable {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem Invariant.initial [CInterface] {program : Program Invocation}
    (stored : Stored heap p kind state) (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (readonly : CReadOnly.Preserves literals heap) (logging : LogPolicy program objects retained heap p) :
    Invariant program objects retained owners heap literals heap p kind state :=
  ⟨stored, ownership, .refl objects retained heap, readonly, logging⟩

theorem Invariant.advance [CInterface] {program : Program Invocation}
    (before : Invariant program objects retained owners original literals heap p kind state)
    (result : Result objects retained owners p buffers heap after kind state action) :
    Invariant program objects retained owners original literals after p kind (action.next state) :=
  ⟨result.stored, result.ownership, before.caller.trans result.caller,
    before.readonly.trans result.readonly, before.logging.framed result.retains⟩

structure ExecutionContract [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind) : Prop where
  call : ∀ heap state action,
    Invariant program objects retained owners original literals heap p kind state →
    action.Prepared objects retained original p buffers → action.Allowed kind state →
    CallContract model program objects retained owners p buffers heap kind state action

/-- Every operation contract is derived from the same actual prepared table
and pool. Original caller storage, not a later heap, supplies every request. -/
theorem execution_contract (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames))
    (getter : Float64Environment.PreparedContract model sigs pool)
    (setter : Float64SetEnvironment.PreparedContract model sigs pool)
    (counts : ∀ events, CountEnvironment.PreparedContract model sigs events pool)
    (nominals : NominalEnvironment.PreparedContract model sigs pool)
    (lifecycle : LifecycleEnvironment.PreparedContract model sigs)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
    ∀ (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
      (original : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind),
      Resources objects retained original p buffers →
      ExecutionContract model program objects retained owners original (pool.install baseHeap firstBlock signed) p buffers kind := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual retained owners original p buffers kind resources
  obtain ⟨reset, enterDefined, exitDefined, _, _⟩ := lifecycle.execution header objects (pool.addresses firstBlock) program actual
  have initialization := InitializationEnvironment.quiet_correct header objects (pool.addresses firstBlock) model program enterDefined exitDefined
  have get := getter.quiet header Invocation objects firstBlock program actual
  have set := setter.quiet header Invocation objects firstBlock program actual
  constructor
  intro heap state action invariant prepared allowed
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
  | enter args => exact enter_call model program initialization invariant.stored invariant.ownership args allowed
  | exit => exact exit_call model program initialization invariant.stored invariant.ownership allowed
  | reset => exact reset_call model program reset invariant.stored invariant.ownership

inductive Observed (model : Solve.FMI3Model source) : State → List Action →
    List (Float64Access.Observation Invocation) → Prop where
  | nil : Observed model state [] []
  | cons : action.Observed model state observed → Observed model (action.next state) rest values →
      Observed model state (action :: rest) (observed :: values)

/-- The per-exit reference state and stored heap remain paired through the
entire history. Failed initialization attempts contribute no exit checkpoint. -/
inductive Checkpoints (p : Address) (kind : Kind) : State → List Action → List Heap → Prop where
  | nil : Checkpoints p kind state [] []
  | cons {middle : Heap} {action : Action} {state : State} {rest : List Action} {checkpoints : List Heap} :
      Stored middle p kind (action.next state) →
      Checkpoints p kind (action.next state) rest checkpoints →
      Checkpoints p kind state (action :: rest) (action.checkpoints middle ++ checkpoints)

def exitStates : State → List Action → List State
  | _, [] => []
  | state, action :: rest =>
      (match action with | .exit => [action.next state] | _ => []) ++ exitStates (action.next state) rest

theorem Checkpoints.stored (checkpoints : Checkpoints p kind state actions heaps) :
    List.Forall₂ (fun state heap => Stored heap p kind state) (exitStates state actions) heaps := by
  induction checkpoints with
  | nil => exact .nil
  | @cons middle action state rest checkpoints stored _ ih =>
    cases action <;> simp only [Action.checkpoints, exitStates, List.nil_append, List.singleton_append]
    all_goals first | exact ih | exact .cons stored ih

def Untouched (p : Address) (buffers : Float64Buffers.Layout) (actions : List Action) (q : Address) : Prop :=
  ¬ p.InRecord q ∧ Float64Access.Outside buffers q ∧ ∀ action ∈ actions, action.Outside q

/-- Any finite admissible raw execution has the reference observations and
post-state. All later storage and logger premises are derived inductively. -/
theorem Completed.correct [CInterface] {program : Program Invocation}
    (contract : ExecutionContract model program objects retained owners original literals p buffers kind)
    (reference : ReferenceTrace kind state actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original p buffers)
    (invariant : Invariant program objects retained owners original literals heap p kind state)
    (executed : Completed program p buffers heap actions observed after checkpoints) :
    Observed model state actions observed ∧ Checkpoints p kind state actions checkpoints ∧
    Invariant program objects retained owners original literals after p kind final ∧
    CReadOnly.Preserves heap after ∧ Retains p heap after ∧
    (∀ q, Float64Rejection.Protected objects retained q → Untouched p buffers actions q → after q = heap q) := by
  induction executed generalizing state final with
  | nil =>
    cases reference
    exact ⟨.nil, .nil, invariant, .refl _, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | @cons middle rest observed after checkpoints heap action events status called _ ih =>
    cases reference with
    | cons allowed following =>
      have certified := contract.call heap state action invariant (prepared action (by simp)) allowed
      obtain ⟨observation, result⟩ := certified.returned events status middle called
      obtain ⟨observations, checkpoints, finalInvariant, readonly, retains, frame⟩ :=
        ih following (fun a member => prepared a (List.mem_cons_of_mem _ member)) (invariant.advance result)
      refine ⟨.cons observation observations, .cons result.stored checkpoints, finalInvariant,
        result.readonly.trans readonly, fun name outside => (retains name outside).trans (result.retains name outside), ?_⟩
      intro q guarded untouched
      exact (frame q guarded ⟨untouched.1, untouched.2.1,
        fun a member => untouched.2.2 a (List.mem_cons_of_mem _ member)⟩).trans
        (result.frame q guarded untouched.1 untouched.2.1 (untouched.2.2 action (by simp)))

/-- A stopped history retains its completed prefix and the real blocked C
call. It is not represented as a successful initialization. -/
inductive Stopped [CInterface] (program : Program Invocation) (p : Address) (buffers : Float64Buffers.Layout) :
    Heap → List Action → Prop where
  | here : action.Behaves program heap p buffers (.wrong []) → Stopped program p buffers heap (action :: rest)
  | later : action.Behaves program heap p buffers (.terminates events ⟨status, middle⟩) →
      Stopped program p buffers middle rest → Stopped program p buffers heap (action :: rest)

theorem progress [CInterface] {program : Program Invocation}
    (contract : ExecutionContract model program objects retained owners original literals p buffers kind)
    (reference : ReferenceTrace kind state actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original p buffers)
    (invariant : Invariant program objects retained owners original literals heap p kind state) :
    (∃ observed after checkpoints, Completed program p buffers heap actions observed after checkpoints) ∨
    Stopped program p buffers heap actions := by
  induction reference generalizing heap with
  | nil => exact Or.inl ⟨[], heap, [], .nil⟩
  | @cons rest final state action allowed _ ih =>
    have certified := contract.call heap state action invariant (prepared action (by simp)) allowed
    rcases certified.progress with ⟨events, status, middle, called⟩ | blocked
    · have next := invariant.advance (certified.returned events status middle called).2
      rcases ih (fun a member => prepared a (List.mem_cons_of_mem _ member)) next with
        ⟨observed, after, checkpoints, completed⟩ | stopped
      · exact Or.inl ⟨_, after, _, .cons called completed⟩
      · exact Or.inr (.later called stopped)
    · exact Or.inr (.here blocked)

end Rumoca.FMI3.InitializationProtocol
end

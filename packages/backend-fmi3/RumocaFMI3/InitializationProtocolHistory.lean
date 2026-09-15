import RumocaFMI3.InitializationProtocolCounts
import RumocaFMI3.InitializationProtocolNominals
import RumocaFMI3.InitializationProtocolInputs
import RumocaFMI3.LifecycleEnvironment

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory CBody StaticFactory CCalls.Events CLiteral

structure Resources (objects : Objects) (retained : Address → Prop) (original : Heap)
    (p : Address) (buffers : Float64Buffers.Layout) (readers : ReadBank) : Prop where
  outputs : Float64Buffers.Stored original buffers
  separate : buffers.Separate p
  inPool : p.block = objects.instances.block
  references : ∀ i < buffers.capacity.toNat, Float64Rejection.Protected objects retained (buffers.references.index i)
  values : ∀ i < buffers.capacity.toNat, Float64Rejection.Protected objects retained (buffers.values.index i)
  readerInputs : readers.Stored original
  readerGuarded : readers.Guarded objects retained p buffers

def Action.Prepared (action : Action) (objects : Objects) (retained : Address → Prop)
    (original : Heap) (p : Address) (buffers : Float64Buffers.Layout) (readers : ReadBank) : Prop :=
  action.ReadSafe readers ∧
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
  | .logging request => request ∈ readers
  | _ => True

structure Invariant [CInterface] (program : Program Invocation) (objects : Objects) (retained : Address → Prop)
    (owners : SlotOwners.State objects.capacity) (original literals heap : Heap)
    (p : Address) (kind : Kind) (state : State) (readers : ReadBank) : Prop where
  stored : Stored heap p kind state
  ownership : SlotOwners.Represents objects.flagsBlock heap owners
  caller : CallerStorage objects retained original heap
  readonly : CReadOnly.Preserves literals heap
  logging : LogPolicy program objects retained heap p
  readerFrame : readers.Frame original heap

variable {objects : Objects} {owners : SlotOwners.State objects.capacity}
variable {readers : ReadBank}

theorem Invariant.initial [CInterface] {program : Program Invocation}
    (stored : Stored heap p kind state) (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (readonly : CReadOnly.Preserves literals heap) (logging : LogPolicy program objects retained heap p) :
    Invariant program objects retained owners heap literals heap p kind state readers :=
  ⟨stored, ownership, .refl objects retained heap, readonly, logging, .refl _ _⟩

theorem Invariant.advance [CInterface] {program : Program Invocation}
    (before : Invariant program objects retained owners original literals heap p kind state readers)
    (resources : Resources objects retained original p buffers readers)
    (safe : action.ReadSafe readers)
    (result : Result objects retained owners p buffers heap after kind state action) :
    Invariant program objects retained owners original literals after p kind (action.next state) readers :=
  ⟨result.stored, result.ownership, before.caller.trans result.caller,
    before.readonly.trans result.readonly, before.logging.updated result.retains,
    before.readerFrame.trans (result.inputs_framed resources.readerGuarded safe)⟩

structure ExecutionContract [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals : Heap) (p : Address) (buffers : Float64Buffers.Layout) (kind : Kind)
    (readers : ReadBank) : Prop where
  resources : Resources objects retained original p buffers readers
  call : ∀ heap state action,
    Invariant program objects retained owners original literals heap p kind state readers →
    action.Prepared objects retained original p buffers readers → action.Allowed kind state →
    CallContract model program objects retained owners p buffers heap kind state action

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
    (contract : ExecutionContract model program objects retained owners original literals p buffers kind readers)
    (reference : ReferenceTrace kind state actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original p buffers readers)
    (invariant : Invariant program objects retained owners original literals heap p kind state readers)
    (executed : Completed program p buffers heap actions observed after checkpoints) :
    Observed model state actions observed ∧ Checkpoints p kind state actions checkpoints ∧
    Invariant program objects retained owners original literals after p kind final readers ∧
    CReadOnly.Preserves heap after ∧ Retention (loggingUpdate actions) p heap after ∧
    (∀ q, Float64Rejection.Protected objects retained q → Untouched p buffers actions q → after q = heap q) := by
  induction executed generalizing state final with
  | nil =>
    cases reference
    exact ⟨.nil, .nil, invariant, .refl _, Retention.refl _ _, fun _ _ _ => rfl⟩
  | @cons middle rest observed after checkpoints heap action events status called _ ih =>
    cases reference with
    | cons allowed following =>
      have certified := contract.call heap state action invariant (prepared action (by simp)) allowed
      obtain ⟨observation, result⟩ := certified.returned events status middle called
      obtain ⟨observations, checkpoints, finalInvariant, readonly, retains, frame⟩ :=
        ih following (fun a member => prepared a (List.mem_cons_of_mem _ member)) (invariant.advance contract.resources (prepared action (by simp)).1 result)
      refine ⟨.cons observation observations, .cons result.stored checkpoints, finalInvariant,
        result.readonly.trans readonly, result.retains.trans retains, ?_⟩
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
    (contract : ExecutionContract model program objects retained owners original literals p buffers kind readers)
    (reference : ReferenceTrace kind state actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original p buffers readers)
    (invariant : Invariant program objects retained owners original literals heap p kind state readers) :
    (∃ observed after checkpoints, Completed program p buffers heap actions observed after checkpoints) ∨
    Stopped program p buffers heap actions := by
  induction reference generalizing heap with
  | nil => exact Or.inl ⟨[], heap, [], .nil⟩
  | @cons rest final state action allowed _ ih =>
    have certified := contract.call heap state action invariant (prepared action (by simp)) allowed
    rcases certified.progress with ⟨events, status, middle, called⟩ | blocked
    · have next := invariant.advance contract.resources (prepared action (by simp)).1 (certified.returned events status middle called).2
      rcases ih (fun a member => prepared a (List.mem_cons_of_mem _ member)) next with
        ⟨observed, after, checkpoints, completed⟩ | stopped
      · exact Or.inl ⟨_, after, _, .cons called completed⟩
      · exact Or.inr (.later called stopped)
    · exact Or.inr (.here blocked)

end Rumoca.FMI3.InitializationProtocol
end

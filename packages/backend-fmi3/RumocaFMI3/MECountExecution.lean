import RumocaFMI3.MECountMemory
import RumocaFMI3.MEMixedConfiguration
import RumocaFMI3.CountRequests

/-! Complete count calls in the existing ME runtime. The caller count
cell is separate from the simulation's protected memory. The original-cell
handoff into these contracts belongs to the mixed-history induction. -/
noncomputable section
namespace Rumoca.FMI3.MECountCalls
open CTree CMemory CBody StaticFactory CCalls.Events CLiteral

def Separate (request : CountAccess.Request) (objects : Objects)
    (addresses : String → Address) (buffer : Address) : Prop :=
  match request with
  | .get _ output => ¬ MEFailure.Protected objects addresses buffer output
  | .reject _ _ _ => True

def next (request : CountAccess.Request) (reference : MENumericalHistory.ReferenceState) :
    MENumericalHistory.ReferenceState :=
  if request.failed then reference.failed else reference

structure Memory [CInterface] (objects : Objects) (owners : SlotOwners.State objects.capacity)
    (config : MEMixedRun.Configuration) (heap after : Heap) (p : Address)
    (addresses : String → Address) (buffer : Address) (clock : Time.Clock)
    (reference : MENumericalHistory.ReferenceState) (request : CountAccess.Request) : Prop where
  stored : MENumericalHistory.Stored after p clock (next request reference) addresses buffer
  reset : Reset.Storage after p
  configuration : config.Stored after p
  ownership : SlotOwners.Represents objects.flagsBlock after owners
  readonly : CReadOnly.Preserves heap after
  frame : ∀ q, MEFailure.Protected objects addresses buffer q → q ≠ p.member "mode" → after q = heap q
  storage : ∀ region, config.StoragePolicy region → CStorage.PreservesOn region heap after
  callerFrame : ∀ region, config.FramePolicy region →
    ∀ q, region q → q ≠ p.member "mode" → request.Outside q → after q = heap q

theorem configuration_frame [CInterface] {config : MEMixedRun.Configuration}
    (configured : config.Stored heap p)
    (inPool : p.block = objects.instances.block)
    (frame : ∀ q, MEFailure.Protected objects addresses buffer q → q ≠ p.member "mode" → after q = heap q) :
    config.Stored after p := by
  apply configured.framed
  intro name member
  apply frame (p.member name) (Or.inl inPool)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp

theorem Memory.success [CInterface] (events : Bool) (output : Address)
    {owners : SlotOwners.State objects.capacity} {config : MEMixedRun.Configuration}
    (stored : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (reset : Reset.Storage heap p) (configured : config.Stored heap p)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (inPool : p.block = objects.instances.block) (old : Option Value)
    (storage : heap output = some ⟨.size, true, old⟩)
    (outside : ¬ MEFailure.Protected objects addresses buffer output) :
    Memory objects owners config heap (CountQueries.written events heap output) p addresses buffer clock reference
      (.get events output) := by
  obtain ⟨storedAfter, resetAfter, ownersAfter, preserved, readonly, frame⟩ :=
    written_memory events heap p output objects addresses buffer clock reference owners old storage stored reset ownership inPool outside
  exact ⟨storedAfter, resetAfter, configuration_frame configured inPool (fun q guarded _ => frame q guarded),
    ownersAfter, readonly, (fun q guarded _ => frame q guarded), (fun region _ => preserved.on region),
    fun _ _ q _ _ outside => CountQueries.frame events heap output q outside⟩

theorem Memory.failure [CInterface] (events missing : Bool) (output : Option Address)
    {owners : SlotOwners.State objects.capacity} {config : MEMixedRun.Configuration}
    (stored : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (reset : Reset.Storage heap p) (configured : config.Stored heap p)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (inPool : p.block = objects.instances.block)
    (callbackFrame : MEFailure.ProtectedFrame objects addresses buffer (LifecycleBodies.writeMode heap p .terminated) after)
    (callbackReadonly : CReadOnly.Preserves (LifecycleBodies.writeMode heap p .terminated) after)
    (callbackStorage : ∀ region, config.StoragePolicy region →
      CStorage.PreservesOn region (LifecycleBodies.writeMode heap p .terminated) after)
    (callbackCells : ∀ region, config.FramePolicy region →
      ∀ q, region q → after q = LifecycleBodies.writeMode heap p .terminated q) :
    Memory objects owners config heap after p addresses buffer clock reference (.reject events missing output) := by
  have numerical := callbackFrame.numerical inPool
  have changed := LifecycleBodies.write_storage heap p _ .terminated stored.control.mode
  have frame (q : Address) (guarded : MEFailure.Protected objects addresses buffer q) (different : q ≠ p.member "mode") :=
    (callbackFrame q guarded).trans (LifecycleBodies.write_frame heap p q .terminated different)
  exact ⟨stored.failed.framed numerical, numerical.reset_storage (stored.failed_reset reset),
    configuration_frame configured inPool frame,
    callbackFrame.owners (SlotOwners.ordinary_preserves ownership changed.2.2),
    changed.2.1.trans callbackReadonly, frame,
    (fun region policy => (changed.1.on region).trans (callbackStorage region policy)),
    fun region policy q inside different _ => (callbackCells region policy q inside).trans
      (LifecycleBodies.write_frame heap p q .terminated different)⟩

def CorrectObservation (model : Solve.FMI3Model source) (request : CountAccess.Request)
    (events : List Invocation) (status : Value) (after : Heap) : Prop :=
  status = .integer (if request.failed then 3 else 0) ∧
  (request.failed = false → events = []) ∧
  request.readback after 0 = request.expected model 0

/-- This summarizes the same C machine, including every modeled return and
blocked branch. Returns is an independently specified predicate; it does not
restrict the raw call or assume an expected output. -/
structure Contract [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (objects : Objects) (owners : SlotOwners.State objects.capacity) (config : MEMixedRun.Configuration)
    (heap : Heap) (p : Address) (addresses : String → Address) (buffer : Address)
    (clock : Time.Clock) (reference : MENumericalHistory.ReferenceState) (request : CountAccess.Request)
    (returns : List Invocation → Value → Heap → Prop) (blocked : Prop) : Prop where
  behaviors : ∀ behavior, (machine program).Behaves
    (.calling (request.call p).1 (request.call p).2 heap .done) behavior ↔
    (∃ events status after, returns events status after ∧ behavior = .terminates events ⟨status, after⟩) ∨
    (blocked ∧ behavior = .wrong [])
  available : (∃ events status after, returns events status after) ∨ blocked
  returned : ∀ events status after, returns events status after →
    CorrectObservation model request events status after ∧
    Memory objects owners config heap after p addresses buffer clock reference request
  failure : blocked → request.failed = true

theorem Contract.quiet [CInterface] {program : Program Invocation} {config : MEMixedRun.Configuration}
    {owners : SlotOwners.State objects.capacity}
    (called : ∀ behavior, (machine program).Behaves
      (.calling (request.call p).1 (request.call p).2 heap .done) behavior ↔
      behavior = .terminates [] ⟨status, after⟩)
    (observation : CorrectObservation model request [] status after)
    (memory : Memory objects owners config heap after p addresses buffer clock reference request) :
    Contract model program objects owners config heap p addresses buffer clock reference request
      (fun events value result => events = [] ∧ value = status ∧ result = after) False := by
  refine ⟨?_, Or.inl ⟨[], status, after, rfl, rfl, rfl⟩, ?_, False.elim⟩
  · intro behavior
    exact (called behavior).trans (by simp)
  · rintro events value result ⟨rfl, rfl, rfl⟩
    exact ⟨observation, memory⟩

/-- Actual pool/table contracts supply this complete call specification from
the current invariant. The mixed-history proof will derive the caller storage
from its original heap using the existing universal StoragePolicy. -/
theorem execution (header : CFenv.Header) (objects : Objects) (model : Solve.FMI3Model source)
    (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames))
    (prepared : ∀ events, CountEnvironment.PreparedContract model sigs events pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation) (config : MEMixedRun.Configuration),
      program.internal = LiteralPreparation.program model sigs →
    ∀ heap p clock reference addresses buffer (request : CountAccess.Request) (owners : SlotOwners.State objects.capacity),
      config.Valid program objects addresses buffer → config.Stored heap p →
      p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
      CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
      MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
      request.OutputStorage heap → Separate request objects addresses buffer → request.Allowed .me reference.control.mode →
      ∃ returns blocked, Contract model program objects owners config heap p addresses buffer clock reference request returns blocked := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program config actual heap p clock reference addresses buffer request owners valid configured inPool ownership
    literals stored reset outputs separate allowed
  cases request with
  | get events output =>
    obtain ⟨old, cell⟩ := outputs
    have quiet := (prepared events).quiet header Invocation objects firstBlock program actual heap
    have called := quiet.successful p output .me reference.control.mode old stored.control.kind stored.mode_loaded allowed cell
    have observed := quiet.returned model p output .me reference.control.mode old stored.control.kind stored.mode_loaded
      allowed cell [] _ ((called _).mpr rfl)
    refine ⟨_, False, Contract.quiet called ?_ (Memory.success events output stored reset configured ownership inPool old cell separate)⟩
    exact ⟨rfl, fun _ => rfl, by simpa only [CountAccess.Request.readback, CountAccess.Request.expected, ↓reduceIte] using observed.2.2.1⟩
  | reject events missing output =>
    obtain ⟨category, messages, _, _, _, _, quiet, logged⟩ :=
      (prepared events).failures header baseHeap firstBlock signed objects heap literals
    cases config with
    | quiet logger logging =>
      have called := quiet Invocation program actual missing p output .me reference.control.mode logger logging
        stored.control.kind stored.control.mode configured.1 configured.2 allowed valid
      refine ⟨_, False, Contract.quiet called ?_ ?_⟩
      · exact ⟨rfl, by simp [CountAccess.Request.failed], rfl⟩
      · exact Memory.failure events missing output stored reset configured ownership inPool
          (fun _ _ => rfl) (.refl _) (fun region _ => .refl region _) (fun _ _ _ _ => rfl)
    | logged logger environment name effect =>
      obtain ⟨address, external, policy⟩ := valid
      have called := (logged program actual missing p logger environment output .me reference.control.mode name effect
        address external stored.control.kind stored.control.mode configured.1 configured.2.1 configured.2.2 allowed).1
      let args := Logging.arguments environment category (messages missing)
      let returns := fun (observed : List Invocation) (status : Value) (after : Heap) =>
        observed = [⟨name, args⟩] ∧ status = .integer 3 ∧
        ∃ value, effect.execute args (LifecycleBodies.writeMode heap p .terminated) value after
      let blocked := ∀ value after, ¬ effect.execute args (LifecycleBodies.writeMode heap p .terminated) value after
      refine ⟨returns, blocked, ?_, ?_, ?_, fun _ => rfl⟩
      · intro behavior
        refine (called behavior).trans ⟨?_, ?_⟩
        · rintro (⟨value, after, returned, same⟩ | ⟨stopped, same⟩)
          · exact Or.inl ⟨[⟨name, args⟩], .integer 3, after, ⟨rfl, rfl, value, returned⟩, same⟩
          · exact Or.inr ⟨stopped, same⟩
        · rintro (⟨observed, status, after, ⟨rfl, rfl, value, returned⟩, same⟩ | ⟨stopped, same⟩)
          · exact Or.inl ⟨value, after, returned, same⟩
          · exact Or.inr ⟨stopped, same⟩
      · classical
        by_cases available : ∃ value after, effect.execute args (LifecycleBodies.writeMode heap p .terminated) value after
        · obtain ⟨value, after, returned⟩ := available
          exact Or.inl ⟨[⟨name, args⟩], .integer 3, after, rfl, rfl, value, returned⟩
        · exact Or.inr (fun value after returned => available ⟨value, after, returned⟩)
      · rintro observed status after ⟨rfl, rfl, value, returned⟩
        exact ⟨⟨rfl, by simp [CountAccess.Request.failed], rfl⟩,
          Memory.failure events missing output stored reset configured ownership inPool
            (policy _ _ _ _ returned) (effect.readonly _ _ _ _ returned)
            (fun region preserve => preserve _ _ _ _ returned)
            (fun _ preserve q inside => preserve _ _ _ _ returned q inside)⟩

end Rumoca.FMI3.MECountCalls
end

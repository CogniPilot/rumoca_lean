import RumocaFMI3.CSRunExecution
import RumocaFMI3.TerminationEnvironment

noncomputable section
namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory CCalls

/-- The mixed reference needs the logical non-null handle, not a particular
slot address. Creation may therefore select any available instance. -/
theorem query_rehandle (reference : Reference) (header : CFenv.Header) (p q : Address)
    (request : CSHistory.Request) (outputs : StepEntry.Outputs) (observed : Int) (outcome : StepCases.Outcome) :
    StepCases.Condition (reference.query header p request outputs observed) outcome ↔
      StepCases.Condition (reference.query header q request outputs observed) outcome := by
  cases outcome <;> simp [StepCases.Condition, StepCases.Ready, Reference.query, StepCases.nextTime, StepCases.Duration]

theorem Change.rehandle (changed : Change header p buffers before action after status) (q : Address) :
    Change header q buffers before action after status := by
  cases changed with
  | accepted mode accepted => exact .accepted mode accepted
  | rejected reason selection selected => exact .rejected reason selection ((query_rehandle _ _ p q _ _ _ _).mp selected)
  | restart admitted => exact .restart admitted

theorem ReferenceTrace.rehandle (trace : ReferenceTrace header p buffers before actions after statuses) (q : Address) :
    ReferenceTrace header q buffers before actions after statuses := by
  induction trace with
  | nil => exact .nil
  | cons changed _ ih => exact .cons (changed.rehandle q) ih

def CanFinish (mode : Mode) : Prop := mode = .step ∨ mode = .terminated

theorem Change.can_finish (changed : Change header p buffers before action after status)
    (ready : CanFinish before.mode) : CanFinish after.mode := by
  cases changed with
  | accepted mode _ => exact Or.inl mode
  | rejected reason _ _ =>
    by_cases discard : reason = .discard
    · simpa only [Reference.reject, StepRejections.nextMode, if_pos discard] using ready
    · exact Or.inr (by simp [Reference.reject, StepRejections.nextMode, discard])
  | restart _ => exact Or.inl rfl

theorem ReferenceTrace.can_finish (trace : ReferenceTrace header p buffers before actions after statuses)
    (ready : CanFinish before.mode) : CanFinish after.mode := by
  induction trace with
  | nil => exact ready
  | cons changed _ ih => exact ih (changed.can_finish ready)

/-- The original writable-cell premise plus the successful typed load fixes
its exact payload; termination needs this cell, not just its loaded value. -/
theorem Stored.mode_cell {buffers : StepEntry.Buffers} (stored : Stored model heap p buffers reference) :
    heap (p.member "mode") = some ⟨.int32, true, some (.integer reference.mode.code)⟩ := by
  obtain ⟨old, found⟩ := stored.reset.mode
  have loaded := stored.mode
  cases old with
  | none => simp [load, found] at loaded
  | some value =>
    have same : value = .integer reference.mode.code := by
      simp only [load, found] at loaded
      change ((convert .int32 value).bind fun checked =>
        if checked = value then some value else none) = some (.integer reference.mode.code) at loaded
      obtain ⟨checked, _, returned⟩ := Option.bind_eq_some_iff.mp loaded
      split at returned
      · exact Option.some.inj returned
      · contradiction
    simpa only [same] using found

def beforeRelease (heap : Heap) (p : Address) (mode : Mode) : Heap :=
  if mode = .step then LifecycleBodies.writeMode heap p .terminated else heap

def releasedHeap (heap : Heap) (objects : Objects) (slot : Fin objects.capacity) (mode : Mode) : Heap :=
  replace (beforeRelease heap (objects.instances.index slot.val) mode)
    (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)

/-- An active Step Mode is terminated before release. An error has already
terminated the instance, so that branch performs only the actual release call.
The returned handle is not granted validity for any subsequent host call. -/
structure Released [CInterface] (objects : Objects) (program : Events.Program E)
    (tag : CAtomicBoolean.Calls.Event → E) (heap : Heap) (slot : Fin objects.capacity)
    (owners : SlotOwners.State objects.capacity) (owner : Nat) (mode : Mode) : Prop where
  modeAllowed : CanFinish mode
  terminated : mode = .step → ∀ behavior, (Events.machine program).Behaves
    (.calling Termination.signature.name [.pointer (some (objects.instances.index slot.val))] heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, beforeRelease heap (objects.instances.index slot.val) mode⟩
  discharged : SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none)
  ownersAfter : SlotOwners.Represents objects.flagsBlock (releasedHeap heap objects slot mode) (SlotOwners.update owners slot none)
  freed : ∀ behavior, (Events.machine program).Behaves
    (.calling StaticRelease.function.signature.name [.pointer (some (objects.instances.index slot.val))]
      (beforeRelease heap (objects.instances.index slot.val) mode) .done) behavior ↔
    behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)]
      ⟨.void, releasedHeap heap objects slot mode⟩
  frame : ∀ query, query ≠ (objects.instances.index slot.val).member "mode" →
    query ≠ AtomicSlots.address objects.flagsBlock slot → releasedHeap heap objects slot mode query = heap query

theorem finish_correct {E : Type} [interface : CInterface] (objects : Objects) (program : Events.Program E)
    (tag : CAtomicBoolean.Calls.Event → E) (finish : Termination.ReleaseContract objects program tag)
    (release : StaticRelease.Bindings program tag)
    (flags : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨objects.flagsBlock, [], 0⟩)))
    (model : Solve.Model source) (heap : Heap) (slot : Fin objects.capacity) (buffers : StepEntry.Buffers)
    (reference : Reference) (owners : SlotOwners.State objects.capacity) (owner : Nat)
    (stored : Stored model heap (objects.instances.index slot.val) buffers reference)
    (ready : CanFinish reference.mode) (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (owned : owners slot = some owner)
    (metadata : load heap ((objects.instances.index slot.val).member "slot") = some (.integer slot.val)) :
    Released objects program tag heap slot owners owner reference.mode := by
  rcases ready with active | stopped
  · obtain ⟨terminated, discharged, representedAfter, framed, freed⟩ := finish heap slot owners owner .cs .step
      stored.kind (by simpa only [active, Mode.code] using stored.mode_cell) (by simp [FMI3.Reference.Allowed])
      represented owned metadata
    refine ⟨Or.inl active, ?_, discharged, ?_, ?_, ?_⟩
    · intro _ behavior
      simpa only [beforeRelease, active, ↓reduceIte] using terminated behavior
    · simpa only [releasedHeap, beforeRelease, active, ↓reduceIte] using representedAfter
    · intro behavior
      simpa only [releasedHeap, beforeRelease, active, ↓reduceIte] using freed behavior
    · intro query notMode notFlag
      simpa only [releasedHeap, beforeRelease, active, ↓reduceIte] using framed query notMode notFlag
  · obtain ⟨discharged, representedAfter, _, framed, freed⟩ := StaticRelease.release_owned program tag heap
      objects.instances objects.flagsBlock owners slot owner release flags represented owned metadata
    refine ⟨Or.inr stopped, ?_, discharged, ?_, ?_, ?_⟩
    · intro active
      simp [stopped] at active
    · simpa only [releasedHeap, beforeRelease, stopped, reduceCtorEq, ↓reduceIte] using representedAfter
    · intro behavior
      simpa only [releasedHeap, beforeRelease, stopped, reduceCtorEq, ↓reduceIte] using freed behavior
    · intro query _ notFlag
      simpa only [releasedHeap, beforeRelease, stopped, reduceCtorEq, ↓reduceIte] using framed query notFlag

end Rumoca.FMI3.CSRun
end

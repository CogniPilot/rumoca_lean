import RumocaFMI3.CSHistory
import RumocaFMI3.TerminationRelease
import RumocaC.AtomicFrame

noncomputable section
namespace Rumoca.FMI3.CSHistory
open CTree CMemory StaticFactory CCalls

/-- Typed state and caller buffers cannot alias an existing atomic lease
cell, even when ordinary caller storage shares the flags' object block. -/
theorem Stored.atomic_outside {buffers : StepEntry.Buffers}
    (stored : Stored model seed heap p buffers reference stop)
    (query : Address) (busy : Bool) (atomic : heap query = some (CAtomicBoolean.cell busy)) :
    Outside p buffers query := by
  have different (address : Address) (old : Cell) (found : heap address = some old)
      (nonatomic : old.type ≠ .atomicBoolean) : query ≠ address := by
    intro same
    rw [same] at atomic
    exact nonatomic (congrArg Cell.type (Option.some.inj (found.symm.trans atomic)))
  obtain ⟨oldEvent, event⟩ := stored.buffers.event
  obtain ⟨oldTerminate, terminate⟩ := stored.buffers.terminate
  obtain ⟨oldEarly, early⟩ := stored.buffers.early
  obtain ⟨oldLast, last⟩ := stored.buffers.last
  exact ⟨different _ _ stored.state (by intro h; cases h), different _ _ stored.clock (by intro h; cases h),
    different _ _ event (by intro h; cases h), different _ _ terminate (by intro h; cases h),
    different _ _ early (by intro h; cases h), different _ _ last (by intro h; cases h)⟩

/-- All pre-existing atomic reservations survive the admitted numerical
history. This follows from initial typed storage and the proved write frame,
without a new host ownership premise for any subsequent call. -/
theorem trace_atomic_frame (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (seed : Binary64.Value) (p : Address) (buffers : StepEntry.Buffers) (stop : Option Binary64.Value)
    (contracts : ∀ (reference : ReferenceState) (request : Request), StepCalls.AcceptedContract
      (request.query header p buffers reference stop) objects literals model signatures) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Events.Program E)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
      program.internal = LiteralPreparation.program model signatures →
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      ∀ (heap : Heap) (before final : ReferenceState) (requests : List Request),
      Stored model.solve seed heap p buffers before stop → ReferenceTrace stop before requests final →
      ∃ after, Calls program p buffers heap before requests after final ∧
        Stored model.solve seed after p buffers final stop ∧ CAtomicBoolean.Preserves heap after ∧
        ∀ query, Outside p buffers query → after query = heap query := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program range actual rounding floorBound heap before final requests stored admitted
  obtain ⟨after, calls, finalStored, framed⟩ := trace_frame header objects literals model signatures seed p buffers stop
    contracts program range actual rounding floorBound heap before final requests stored admitted
  refine ⟨after, calls, finalStored, ?_, framed⟩
  intro query busy atomic
  exact (framed query (stored.atomic_outside query busy atomic)).trans atomic

/-- A proved CS history supplies the state, mode, metadata and lease for
termination/release. The conclusion does not grant future-call validity to a
released handle. Host ownership and the atomic external profile stay explicit. -/
theorem release_history [CInterface] (objects : Objects) (program : Events.Program E)
    (tag : CAtomicBoolean.Calls.Event → E) (finish : Termination.ReleaseContract objects program tag)
    (model : Solve.Model source) (seed : Binary64.Value) (before after : Heap)
    (slot : Fin objects.capacity) (buffers : StepEntry.Buffers) (reference final : ReferenceState)
    (stop : Option Binary64.Value) (requests : List Request)
    (owners : SlotOwners.State objects.capacity) (owner : Nat)
    (initial : Stored model seed before (objects.instances.index slot.val) buffers reference stop)
    (mode : before ((objects.instances.index slot.val).member "mode") =
      some ⟨.int32, true, some (.integer 4)⟩)
    (calls : Calls program (objects.instances.index slot.val) buffers before reference requests after final)
    (stored : Stored model seed after (objects.instances.index slot.val) buffers final stop)
    (atomic : CAtomicBoolean.Preserves before after)
    (frame : ∀ query, Outside (objects.instances.index slot.val) buffers query → after query = before query)
    (represented : SlotOwners.Represents objects.flagsBlock before owners)
    (owned : owners slot = some owner)
    (metadata : load before ((objects.instances.index slot.val).member "slot") = some (.integer slot.val)) :
    let p := objects.instances.index slot.val
    let terminated := LifecycleBodies.writeMode after p .terminated
    let released := replace terminated (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)
    Calls program p buffers before reference requests after final ∧
    (∀ behavior, (Events.machine program).Behaves
      (.calling Termination.signature.name [.pointer (some p)] after .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, terminated⟩) ∧
    SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
    SlotOwners.Represents objects.flagsBlock released (SlotOwners.update owners slot none) ∧
    (∀ behavior, (Events.machine program).Behaves
      (.calling StaticRelease.function.signature.name [.pointer (some p)] terminated .done) behavior ↔
      behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, released⟩) ∧
    (∀ query, Outside p buffers query → query ≠ p.member "mode" →
      query ≠ AtomicSlots.address objects.flagsBlock slot → released query = before query) := by
  let p := objects.instances.index slot.val
  have modeAfter : after (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ :=
    (frame _ (field_outside initial.buffers "mode" (by decide))).trans mode
  have metadataAfter : load after (p.member "slot") = some (.integer slot.val) := by
    simpa only [p, load, frame _ (field_outside initial.buffers "slot" (by decide))] using metadata
  obtain ⟨terminated, discharged, ownersAfter, releaseFrame, freed⟩ := finish after slot owners owner .cs .step
    stored.kind modeAfter (by simp [Reference.Allowed])
    (SlotOwners.ordinary_preserves represented atomic) owned metadataAfter
  refine ⟨calls, terminated, discharged, ownersAfter, freed, ?_⟩
  intro query outside outsideMode outsideFlag
  exact (releaseFrame query outsideMode outsideFlag).trans (frame query outside)

end Rumoca.FMI3.CSHistory
end

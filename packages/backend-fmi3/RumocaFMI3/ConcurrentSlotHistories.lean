import RumocaFMI3.ConcurrentSlotCalls

/-! Annotated shared-memory histories project to actual C steps and an independent ownership history. The annotations remain an explicit boundary. -/
noncomputable section
namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CAtomicBoolean
variable {capacity : Nat}

def claimOwners (owners : SlotOwners.State capacity) (slot : Fin capacity) (lease : Nat) :
    SlotOwners.State capacity :=
  if (SlotOwners.occupied owners) slot then owners else SlotOwners.update owners slot (some lease)

theorem Claim.target (claim : Claim owners slot lease ((SlotOwners.occupied owners) slot) ownersAfter) :
    ownersAfter = claimOwners owners slot lease := by
  cases busy : (SlotOwners.occupied owners) slot with
  | false =>
    have reserved : SlotOwners.reserve owners slot lease = some ownersAfter := by simpa [Claim, busy] using claim
    simpa [claimOwners, busy] using (SlotOwners.reserve_iff.mp reserved).2
  | true =>
    have same : ownersAfter = owners := (by simpa [Claim, busy] using claim : owners slot ≠ none ∧ ownersAfter = owners).2
    simpa [claimOwners, busy] using same

inductive Action (capacity : Nat) where
  | claim (slot : Fin capacity) (lease : Nat) (busy : Bool)
  | release (slot : Fin capacity) (lease : Nat)
  deriving DecidableEq

/-- Independent lease transitions; silent C operations project to no action. -/
inductive OwnerStep : SlotOwners.State capacity → List (Action capacity) → SlotOwners.State capacity → Prop where
  | claim (claimed : Claim before slot lease busy after) :
      OwnerStep before [.claim slot lease busy] after
  | release (released : SlotOwners.release before slot lease = some after) :
      OwnerStep before [.release slot lease] after

theorem owner_step_keeps (step : OwnerStep before actions after)
    (owned : before slot = some lease) (noRelease : Action.release slot lease ∉ actions) :
    after slot = some lease := by
  cases step with
  | @claim selected newLease busy after claimed =>
    cases busy with
    | true => rw [(claim_busy claimed).1]; exact owned
    | false =>
      by_cases same : slot = selected
      · subst selected
        have vacant := (claim_success claimed).1
        rw [owned] at vacant
        contradiction
      · rw [SlotOwners.reserve_frame claimed same]
        exact owned
  | @release selected releasing after released =>
    by_cases same : slot = selected
    · subst selected
      have identity := Option.some.inj (owned.symm.trans (SlotOwners.release_iff.mp released).1)
      subst releasing
      exact False.elim (noRelease (by simp))
    · rw [SlotOwners.release_frame released same]
      exact owned

theorem owner_history_keeps
    (path : Transition.Events.Reaches OwnerStep before actions after)
    (owned : before slot = some lease) (noRelease : Action.release slot lease ∉ actions) :
    after slot = some lease := by
  induction path with
  | refl => exact owned
  | next first rest ih =>
    exact ih (owner_step_keeps first owned (fun member => noRelease (List.mem_append_left _ member)))
      (fun member => noRelease (List.mem_append_right _ member))

/-- A later successful reservation of an owned slot entails an intervening
release of its previous lease. This covers arbitrary finite interleavings. -/
theorem reclaim_requires_release
    (path : Transition.Events.Reaches OwnerStep before actions after)
    (owned : before slot = some lease) (claimed : Claim after slot nextLease false ownersAfter) :
    Action.release slot lease ∈ actions := by
  by_contra absent
  have stillOwned := owner_history_keeps path owned absent
  have vacant := (claim_success claimed).1
  rw [stillOwned] at vacant
  contradiction

structure Configuration (capacity : Nat) where
  runtime : Concurrent.State
  owners : SlotOwners.State capacity

structure Tick (E : Type) (capacity : Nat) where
  thread : Nat
  effects : List E
  action : Option (Action capacity)

def runtimeTrace (ticks : List (Tick E capacity)) : List (Nat × List E) :=
  ticks.map fun tick => (tick.thread, tick.effects)

def ownerTrace (ticks : List (Tick E capacity)) : List (Action capacity) :=
  ticks.flatMap fun tick => tick.action.toList

variable [interface : CInterface] {E : Type}

/-- Ghost annotations classify actual scheduler steps. An ordinary step needs
its atomic-cell frame; reservation and release use actual call entry and raw
argument conversion. Release additionally requires the current lease.
Classifying every generated factory path remains a separate proof obligation. -/
inductive ScheduledStep (program : Events.Program E) (block : Nat) :
    Configuration capacity → List (Tick E capacity) → Configuration capacity → Prop where
  | ordinary (actual : Concurrent.Step program before thread effects after)
      (frame : Preserves before.heap after.heap) :
      ScheduledStep program block ⟨before, owners⟩ [⟨thread, effects, none⟩] ⟨after, owners⟩
  | claim (selected : before.threads thread = some saved)
      (atCall : Concurrent.withHeap saved before.heap = .calling "atomic_exchange" args before.heap stack)
      (converted : Events.convertedArguments Calls.exchangeSignature.parameters args =
        some [.pointer (some (AtomicSlots.address block slot)), value true])
      (actual : Concurrent.Step program before thread effects after) :
      ScheduledStep program block ⟨before, owners⟩
        [⟨thread, effects, some (.claim slot lease ((SlotOwners.occupied owners) slot))⟩]
        ⟨after, claimOwners owners slot lease⟩
  | release (selected : before.threads thread = some saved)
      (atCall : Concurrent.withHeap saved before.heap = .calling "atomic_store" args before.heap stack)
      (converted : Events.convertedArguments Calls.writeSignature.parameters args =
        some [.pointer (some (AtomicSlots.address block slot)), value false])
      (owned : owners slot = some lease)
      (actual : Concurrent.Step program before thread effects after) :
      ScheduledStep program block ⟨before, owners⟩ [⟨thread, effects, some (.release slot lease)⟩]
        ⟨after, SlotOwners.update owners slot none⟩

def runtimeStep (program : Events.Program E) (before : Concurrent.State)
    (labels : List (Nat × List E)) (after : Concurrent.State) : Prop :=
  ∃ thread effects, labels = [(thread, effects)] ∧ Concurrent.Step program before thread effects after

theorem ScheduledStep.erases (step : ScheduledStep program block before ticks after) :
    runtimeStep program before.runtime (runtimeTrace ticks) after.runtime := by
  cases step with
  | ordinary actual frame => exact ⟨_, _, rfl, actual⟩
  | claim selected atCall converted actual => exact ⟨_, _, rfl, actual⟩
  | release selected atCall converted owned actual => exact ⟨_, _, rfl, actual⟩

theorem ScheduledStep.refines (program : Events.Program E) (tag : Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (exchangeBound : program.externals "atomic_exchange" = some (Calls.exchangeExternal tag boolean))
    (writeBound : program.externals "atomic_store" = some (Calls.writeExternal tag))
    (step : ScheduledStep program block before ticks after)
    (represented : SlotOwners.Represents block before.runtime.heap before.owners) :
    SlotOwners.Represents block after.runtime.heap after.owners ∧
      Transition.Events.Reaches OwnerStep before.owners (ownerTrace ticks) after.owners := by
  cases step with
  | ordinary actual frame =>
    exact ⟨SlotOwners.ordinary_preserves represented frame, .refl _⟩
  | claim selected atCall converted actual =>
    rename_i lease
    obtain ⟨target, next, claimed, memory, _, _, unique⟩ :=
      reserve_scheduled program tag boolean exchangeBound selected atCall converted represented lease
    have same := (unique _ _).mp actual
    cases same.2
    have fixed := claimed.target
    rw [fixed] at memory claimed
    exact ⟨memory, by simpa using Transition.Events.Reaches.next (OwnerStep.claim claimed) (.refl _)⟩
  | release selected atCall converted owned actual =>
    obtain ⟨target, next, released, memory, _, _, unique⟩ :=
      release_scheduled program tag writeBound selected atCall converted represented owned
    have same := (unique _ _).mp actual
    cases same.2
    have fixed := (SlotOwners.release_iff.mp released).2
    rw [fixed] at memory released
    exact ⟨memory, by simpa using Transition.Events.Reaches.next (OwnerStep.release released) (.refl _)⟩

/-- Every finite annotated shared-memory history projects to both the actual
scheduler history and the independent lease history. No terminating complete
factory call is assumed. The annotation/classification boundary remains explicit. -/
theorem history_refines (program : Events.Program E) (tag : Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (exchangeBound : program.externals "atomic_exchange" = some (Calls.exchangeExternal tag boolean))
    (writeBound : program.externals "atomic_store" = some (Calls.writeExternal tag))
    (path : Transition.Events.Reaches (ScheduledStep program block) before ticks after)
    (represented : SlotOwners.Represents block before.runtime.heap before.owners) :
    SlotOwners.Represents block after.runtime.heap after.owners ∧
      Transition.Events.Reaches OwnerStep before.owners (ownerTrace ticks) after.owners ∧
      Transition.Events.Reaches (runtimeStep program) before.runtime (runtimeTrace ticks) after.runtime := by
  induction path with
  | refl => exact ⟨represented, .refl _, .refl _⟩
  | next first rest ih =>
    obtain ⟨memory, ownership⟩ := ScheduledStep.refines program tag boolean exchangeBound writeBound first represented
    obtain ⟨lastMemory, restOwners, restRuntime⟩ := ih memory
    exact ⟨lastMemory,
      by simpa [ownerTrace, List.flatMap_append] using ownership.trans restOwners,
      by simpa [runtimeTrace, List.map_append] using
        Transition.Events.Reaches.next first.erases restRuntime⟩

theorem scheduled_reclaim_requires_release (program : Events.Program E) (tag : Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (exchangeBound : program.externals "atomic_exchange" = some (Calls.exchangeExternal tag boolean))
    (writeBound : program.externals "atomic_store" = some (Calls.writeExternal tag))
    (path : Transition.Events.Reaches (ScheduledStep program block) before ticks after)
    (represented : SlotOwners.Represents block before.runtime.heap before.owners)
    (owned : before.owners slot = some lease)
    (claimed : Claim after.owners slot nextLease false ownersAfter) :
    Action.release slot lease ∈ ownerTrace ticks :=
  reclaim_requires_release (history_refines program tag boolean exchangeBound writeBound path represented).2.1 owned claimed

end Rumoca.FMI3.ConcurrentSlots

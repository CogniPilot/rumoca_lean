import RumocaFMI3.StaticRelease
import RumocaC.AtomicArguments
import RumocaC.AtomicLoadedFrame
import RumocaC.CallIntervals

/-! Actual public-release control and its own metadata frame through every selected step. -/
noncomputable section
namespace Rumoca.FMI3.StaticRelease.ConcurrentInvariant
open CTree CMemory CCalls
open CCalls.Concurrent (Exit BeforeReturn)

/-- Slot metadata required by a nonnull release. A null handle needs no heap
cell, so the same statement covers its unconditional no-op behavior. -/
def Metadata (p : Option Address) (slot : Nat) (heap : Heap) : Prop :=
  ∀ address, p = some address → load heap (address.member "slot") = some (.integer slot)

def MetadataFrame (p : Option Address) (before after : Heap) : Prop :=
  ∀ address, p = some address → after (address.member "slot") = before (address.member "slot")

theorem MetadataFrame.refl (p : Option Address) (heap : Heap) : MetadataFrame p heap heap :=
  fun _ _ => rfl

theorem Metadata.preserved (metadata : Metadata p slot before) (frame : MetadataFrame p before after) :
    Metadata p slot after := by
  intro address selected
  simpa only [load, frame address selected] using metadata address selected

/-- Actual control states of the generated public release, retaining its
original handle and the slot index read for the pending atomic call. -/
inductive Ready : Option Address → Address → Nat → Typed.Continuation → Typed.State → Prop where
  | entry (heap : Heap) : Ready p flags slot stack
      (.calling function.signature.name [.pointer p] heap stack)
  | parameters (heap : Heap) : Ready p flags slot stack
      (.body (.running function.body (StaticRelease.parameters p) parameterTypes heap) "void" stack)
  | guarded (heap : Heap) : Ready p flags slot stack
      (.body (.running [guard, .ret none] (locals p) types heap) "void" stack)
  | clear (address : Address) (heap : Heap) : Ready (some address) flags slot stack
      (.body (.running [StaticRelease.clear, .ret none] (locals (some address)) types heap) "void" stack)
  | atomic (address : Address) (heap : Heap) : Ready (some address) flags slot stack
      (.calling "atomic_store" [.pointer (some (flags.index slot)), CAtomicBoolean.value false] heap
        (.caller .discard [.ret none] (locals (some address)) types "void" stack))
  | resumed (address : Address) (heap : Heap) : Ready (some address) flags slot stack
      (.returning .void heap (.caller .discard [.ret none] (locals (some address)) types "void" stack))
  | returning (heap : Heap) : Ready p flags slot stack
      (.body (.running [.ret none] (locals p) types heap) "void" stack)
  | returned (heap : Heap) : Ready p flags slot stack
      (.body (.returned ⟨.void, heap⟩) "void" stack)
  | done (heap : Heap) : Ready p flags slot stack (.returning .void heap stack)

theorem Ready.withHeap (ready : Ready p flags slot stack state) (heap : Heap) :
    Ready p flags slot stack (Concurrent.withHeap state heap) := by
  cases ready with
  | entry => exact .entry heap
  | parameters => exact .parameters heap
  | guarded => exact .guarded heap
  | clear address => exact .clear address heap
  | atomic address => exact .atomic address heap
  | resumed address => exact .resumed address heap
  | returning => exact .returning heap
  | returned => exact .returned heap
  | done => exact .done heap

theorem Ready.atomic_origin (ready : Ready p flags slot stack (.calling name args heap later))
    (atomic : name = "atomic_store") :
    p.isSome = true ∧ args = [.pointer (some (flags.index slot)), CAtomicBoolean.value false] := by
  cases ready with
  | entry => simp [function] at atomic
  | atomic address => exact ⟨rfl, rfl⟩

theorem Ready.exit_value (ready : Ready p flags slot stack (.returning value heap stack)) :
    value = .void := by
  cases ready with
  | done => rfl

variable [interface : CInterface] {E : Type}

private theorem known_step (program : Events.Program E)
    (known : Events.internalNext program before = some target)
    (ready : Ready p flags slot stack target)
    (sameHeap : CReadOnly.typedHeap target = CReadOnly.typedHeap before)
    (step : Events.Step program before events after) :
    Ready p flags slot stack after ∧ MetadataFrame p (CReadOnly.typedHeap before) (CReadOnly.typedHeap after) := by
  obtain ⟨_, rfl⟩ := Events.internal_unique program known _ _ step
  exact ⟨ready, fun _ _ => congrFun sameHeap _⟩

/-- The complete public release preserves its control and metadata through
each selected step. Atomic stores cannot alias the successfully loaded ordinary
metadata cell. This does not assume that the slot is currently owned. -/
theorem step_ready (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (bindings : StaticRelease.Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some flags)))
    (ready : Ready p flags slot stack before)
    (metadata : Metadata p slot (CReadOnly.typedHeap before))
    (active : ¬ Exit stack before) (step : Events.Step program before events after) :
    Ready p flags slot stack after ∧ MetadataFrame p (CReadOnly.typedHeap before) (CReadOnly.typedHeap after) := by
  cases ready with
  | entry heap =>
    have bound : CCalls.parameters function.signature.parameters [.pointer p] = some (StaticRelease.parameters p) := by
      simp [function, CCalls.parameters, CCalls.parameterType, CBody.cast, bindings.handle, convert, StaticRelease.parameters]
    have typed : CLoops.Calls.parameterTypes function.signature.parameters = some parameterTypes := by
      simp [function, CLoops.Calls.parameterTypes, CCalls.parameterType, bindings.handle, parameterTypes]
    exact known_step program (Events.tree_entry program _ _ heap stack function _ _ bindings.defined bound typed)
      (.parameters heap) rfl step
  | parameters heap =>
    exact known_step program (Events.body_step program
      (CLoops.declare_local (StaticRelease.parameters p) parameterTypes heap "Instance *" "m" _ [guard, .ret none]
        .pointer (.pointer p) (.pointer p) bindings.pointer (by simp [StaticRelease.parameters, CBody.bind])
        (by simp [CLoops.eval, CBody.eval, CBody.expressionCast, CBody.cast, CBody.resolve,
          StaticRelease.parameters, CBody.bind, bindings.pointer, convert]) rfl)
      "void" stack) (.guarded heap) rfl step
  | guarded heap =>
    cases p with
    | none =>
      exact known_step program (Events.body_step program (guard_step none heap bindings.voidPointer) "void" stack)
        (.returning heap) rfl step
    | some address =>
      exact known_step program (Events.body_step program (guard_step (some address) heap bindings.voidPointer) "void" stack)
        (.clear address heap) rfl step
  | clear address heap =>
    exact known_step program (clear_entry program heap address flags slot stack bindings.boolean bindings.named flagsBound
      (metadata address rfl)) (.atomic address heap) rfl step
  | atomic address heap =>
    cases step with
    | internal next =>
      rw [Events.external_entry_exclusive program bindings.atomicBound] at next
      contradiction
    | external found converted executed =>
      cases Option.some.inj (found.symm.trans bindings.atomicBound)
      obtain ⟨target, pointer, written, _, rfl⟩ :=
        CAtomicBoolean.Calls.write_from_arguments tag bindings.boolean bindings.atomicPointer converted executed
      have same : flags.index slot = target := by simpa using pointer
      subst target
      refine ⟨.resumed address _, ?_⟩
      intro other selected
      cases Option.some.inj selected
      exact CAtomicBoolean.write_preserves_loaded written (metadata address rfl)
  | resumed address heap =>
    exact known_step program rfl (.returning heap) rfl step
  | returning heap =>
    exact known_step program (Events.body_step program rfl "void" stack) (.returned heap) rfl step
  | returned heap =>
    exact known_step program rfl (.done heap) rfl step
  | done heap => exact False.elim (active ⟨_, _, rfl⟩)

end Rumoca.FMI3.StaticRelease.ConcurrentInvariant

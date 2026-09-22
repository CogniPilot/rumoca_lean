import RumocaFMI3.StaticReleaseCode
import RumocaFMI3.SlotOwners
import RumocaC.NullComparison
import RumocaC.LoopProofs
import RumocaC.CallSignature

/-! Complete public calls of the static release function in authored C.
Valid nonnull handles need a live lease and the slot metadata established by
creation; null handles need neither. Native layout/ABI, generation of that
metadata, public histories and actual-artifact binding remain separate. -/
noncomputable section
namespace Rumoca.FMI3.StaticRelease
open CTree CMemory CBody
variable [interface : CInterface]

def parameters (p : Option Address) : Locals := CBody.bind (fun _ => none) "instance" (.pointer p)
def parameterTypes : CLoops.Types := CLoops.bindType (fun _ => none) "instance" .pointer
def locals (p : Option Address) : Locals := CBody.bind (parameters p) "m" (.pointer p)
def types : CLoops.Types := CLoops.bindType parameterTypes "m" .pointer

theorem call_entry (program : CCalls.Events.Program E) (p : Option Address) (heap : Heap)
    (stack : CCalls.Typed.Continuation)
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (handle : interface.types "fmi3Instance" = some .pointer)
    (pointer : interface.types "Instance *" = some .pointer) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling function.signature.name [.pointer p] heap stack)
      (.body (.running [guard, .ret none] (locals p) types heap) "void" stack) := by
  have bound : CCalls.parameters function.signature.parameters [.pointer p] = some (parameters p) := by
    simp [function, CCalls.parameters, CCalls.parameterType, CBody.cast, handle, convert, parameters]
  have typed : CLoops.Calls.parameterTypes function.signature.parameters = some parameterTypes := by
    simp [function, CLoops.Calls.parameterTypes, CCalls.parameterType, handle, parameterTypes]
  refine .next (CCalls.Events.tree_entry program _ _ heap stack function _ _ defined bound typed) ?_
  refine .next (CCalls.Events.body_step program
    (CLoops.declare_local (parameters p) parameterTypes heap "Instance *" "m" _ [guard, .ret none]
      .pointer (.pointer p) (.pointer p) pointer (by simp [parameters, CBody.bind])
      (by simp [CLoops.eval, CLoops.evalWith, legacyExpressions, eval, evalWith,
        expressionCast, CBody.cast, resolve, parameters, CBody.bind, pointer, convert]) rfl)
    "void" stack) ?_
  exact .refl _

theorem guard_step (p : Option Address) (heap : Heap)
    (voidPointer : interface.types "void *" = some .pointer) :
    CLoops.next (.running [guard, .ret none] (locals p) types heap) =
      some (.running ((if p.isSome then [clear] else []) ++ [.ret none]) (locals p) types heap) := by
  cases p <;> simp [guard, clear, CLoops.next, CLoops.nextWith, CLoops.noDeclarations,
    CLoops.evalWith, legacyExpressions, eval, evalWith, resolve, locals, CBody.bind,
    CNull.literal_eval voidPointer, comparison, boolean, Value.truth]

theorem return_path (program : CCalls.Events.Program E) (env : Locals) (localTypes : CLoops.Types)
    (heap : Heap) (stack : CCalls.Typed.Continuation) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running [.ret none] env localTypes heap) "void" stack)
      (.returning .void heap stack) :=
  .next (CCalls.Events.body_step program rfl "void" stack) (.next (by rfl) (.refl _))

theorem clear_entry (program : CCalls.Events.Program E) (heap : Heap) (p flags : Address)
    (slot : Nat) (stack : CCalls.Typed.Continuation)
    (boolean : interface.types "_Bool" = some .boolean)
    (named : interface.constants "atomic_store" = none)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some flags)))
    (metadata : load heap (p.member "slot") = some (.integer slot)) :
    CCalls.Events.internalNext program
      (.body (.running [clear, .ret none] (locals (some p)) types heap) "void" stack) =
      some (.calling "atomic_store" [.pointer (some (flags.index slot)), CAtomicBoolean.value false]
        heap (.caller .discard [.ret none] (locals (some p)) types "void" stack)) := by
  have nonnegative : ¬ (slot : Int) < 0 := by omega
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith,
    CCalls.Typed.nextWithExpressions, CLoops.nextWith, CLoops.evalWith, clear,
    CCalls.Events.enterCallWith, CCalls.Indirect.operand, CCalls.Events.resolveWith,
    CCalls.Indirect.resolveWith, CCalls.argumentsWith, legacyExpressions,
    eval, evalWith, lvalueWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt,
    CDeclaredMembers.fieldAt, resolve, constants, locals, parameters, CBody.bind,
    expressionCast, CBody.cast, zeroLiteral, boolean, convert, Value.truth, Value.address,
    flagsBound, named, metadata, nonnegative, CAtomicBoolean.value]

/-- Null release neither reads instance metadata nor performs any atomic or
foreign call, even when the heap contains no instance storage at all. -/
theorem null_behaviors (program : CCalls.Events.Program E) (heap : Heap)
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (handle : interface.types "fmi3Instance" = some .pointer)
    (pointer : interface.types "Instance *" = some .pointer)
    (voidPointer : interface.types "void *" = some .pointer) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling function.signature.name [.pointer none] heap .done) behavior ↔
      behavior = .terminates [] ⟨.void, heap⟩ := by
  have guarded := guard_step none heap voidPointer
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.nil_append] at guarded
  exact (CCalls.Events.internal_prefix program
    ((call_entry program none heap .done defined handle pointer).trans
      (.next (CCalls.Events.body_step program guarded "void" .done)
        (return_path program (locals none) types heap .done)))
    (CCalls.Events.return_forced program .void heap)).behaviors behavior

/-- For an occupied slot identified by valid metadata, the whole call performs
exactly one atomic store, preserves all other cells, and returns void. -/
theorem occupied_behaviors (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (heap : Heap) (p flags : Address) (slot : Nat)
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (handle : interface.types "fmi3Instance" = some .pointer)
    (pointer : interface.types "Instance *" = some .pointer)
    (voidPointer : interface.types "void *" = some .pointer)
    (boolean : interface.types "_Bool" = some .boolean)
    (atomicPointer : interface.types "volatile atomic_bool *" = some .pointer)
    (named : interface.constants "atomic_store" = none)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some flags)))
    (atomicBound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag))
    (metadata : load heap (p.member "slot") = some (.integer slot))
    (occupied : heap (flags.index slot) = some (CAtomicBoolean.cell true)) :
    let after := replace heap (flags.index slot) (CAtomicBoolean.cell false)
    CStorage.Preserves heap after ∧
      (∀ query, query ≠ flags.index slot → after query = heap query) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling function.signature.name [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates [tag (.write (flags.index slot) false)] ⟨.void, after⟩ := by
  let after := replace heap (flags.index slot) (CAtomicBoolean.cell false)
  have written : CAtomicBoolean.write heap (flags.index slot) false = some after :=
    CAtomicBoolean.write_as_exchange.mpr ⟨true, CAtomicBoolean.exchange_iff.mpr ⟨occupied, rfl⟩⟩
  refine ⟨CAtomicBoolean.write_storage written, fun query different => replace_other _ _ _ _ different, ?_⟩
  intro behavior
  have guarded := guard_step (some p) heap voidPointer
  simp only [Option.isSome_some, ↓reduceIte, List.singleton_append] at guarded
  have entered := (call_entry program (some p) heap .done defined handle pointer).trans
    (.next (CCalls.Events.body_step program guarded "void" .done)
      (.next (clear_entry program heap p flags slot .done boolean named flagsBound metadata) (.refl _)))
  have resumed : CCalls.Events.internalNext program
      (.returning .void after (.caller .discard [.ret none] (locals (some p)) types "void" .done)) =
      some (.body (.running [.ret none] (locals (some p)) types after) "void" .done) := rfl
  have returned := CCalls.Events.internal_prefix program (.next resumed
    (return_path program (locals (some p)) types after .done))
    (CCalls.Events.return_forced program .void after)
  have called := CCalls.Events.external_prefix program atomicBound
    (CAtomicBoolean.Calls.arguments_converted boolean atomicPointer (flags.index slot) false)
    (CAtomicBoolean.Calls.write_executes tag written)
    (fun _ _ _ executed => CAtomicBoolean.Calls.write_unique tag written executed) returned
  simpa only [List.append_nil] using (CCalls.Events.internal_prefix program entered called).behaviors behavior

structure Bindings (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E) : Prop where
  defined : program.internal.definitions function.signature.name = some (.tree function)
  handle : interface.types "fmi3Instance" = some .pointer
  pointer : interface.types "Instance *" = some .pointer
  voidPointer : interface.types "void *" = some .pointer
  boolean : interface.types "_Bool" = some .boolean
  atomicPointer : interface.types "volatile atomic_bool *" = some .pointer
  named : interface.constants "atomic_store" = none
  atomicBound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag)

/-- The complete public call discharges the current logical lease, using the
actual atomic store. A stale or foreign handle is not admitted as a live lease.
The returned C handle has no native lease tag; public-history validity must
establish the ownership premise before invoking this theorem. -/
theorem release_owned (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (heap : Heap) (base : Address) (block : Nat) (owners : SlotOwners.State capacity)
    (slot : Fin capacity) (owner : Nat) (bindings : Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨block, [], 0⟩)))
    (represented : SlotOwners.Represents block heap owners) (owned : owners slot = some owner)
    (metadata : load heap ((base.index slot.val).member "slot") = some (.integer slot.val)) :
    let after := replace heap (AtomicSlots.address block slot) (CAtomicBoolean.cell false)
    SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
      SlotOwners.Represents block after (SlotOwners.update owners slot none) ∧
      CStorage.Preserves heap after ∧
      (∀ query, query ≠ AtomicSlots.address block slot → after query = heap query) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling function.signature.name [.pointer (some (base.index slot.val))] heap .done) behavior ↔
      behavior = .terminates [tag (.write (AtomicSlots.address block slot) false)] ⟨.void, after⟩ := by
  have occupied : heap (AtomicSlots.address block slot) = some (CAtomicBoolean.cell true) := by
    simpa [SlotOwners.occupied, owned] using represented slot
  have written : CAtomicBoolean.write heap (AtomicSlots.address block slot) false =
      some (replace heap (AtomicSlots.address block slot) (CAtomicBoolean.cell false)) :=
    CAtomicBoolean.write_as_exchange.mpr ⟨true, CAtomicBoolean.exchange_iff.mpr ⟨occupied, rfl⟩⟩
  have released := SlotOwners.write_releases represented owned written
  refine ⟨released.1, released.2, ?_⟩
  simpa [AtomicSlots.address, Address.index] using occupied_behaviors program tag heap (base.index slot.val)
    ⟨block, [], 0⟩ slot.val bindings.defined bindings.handle bindings.pointer bindings.voidPointer
    bindings.boolean bindings.atomicPointer bindings.named flagsBound bindings.atomicBound metadata
    (by simpa [AtomicSlots.address, Address.index] using occupied)

end Rumoca.FMI3.StaticRelease

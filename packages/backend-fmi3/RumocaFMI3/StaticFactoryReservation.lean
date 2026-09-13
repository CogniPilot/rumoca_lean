import RumocaFMI3.StaticFactoryInitialization
import RumocaC.AtomicScanCalls
import RumocaC.NamedDeclarations

/-! Execute the actual reservation helper, its typed initializer continuation,
the capacity guard and full instance initialization in one call machine.
The Outcome premise is the independent scan relation, never an assumed C run;
Ready storage gives its existence. Public/global entry and the exhausted
logging path remain separate composition obligations. -/
noncomputable section
namespace Rumoca.FMI3.StaticFactory
open CTree CMemory CBody
variable [interface : CInterface]

structure Scope (env : Locals) (base flags : Address) (capacity : Nat)
    (environment logger : Option Address) (logging : Bool) : Prop where
  instances : resolve env "rumoca_instances" = some (.pointer (some base))
  flagsBound : resolve env "rumoca_instance_flags" = some (.pointer (some flags))
  count : resolve env "rumoca_instance_capacity" = some (.integer capacity)
  instanceFresh : env "m" = none
  slotFresh : env "slot" = none
  helperFresh : env CAtomicScan.function.signature.name = none
  environmentBound : resolve env "instanceEnvironment" = some (.pointer environment)
  loggerBound : resolve env "logMessage" = some (.pointer logger)
  loggingBound : resolve env "loggingOn" = some (boolean logging)

def reservedLocals (env : Locals) (slot : Nat) : Locals := CBody.bind env "slot" (.integer slot)
def reservedTypes (types : CLoops.Types) : CLoops.Types := CLoops.bindType types "slot" .size

theorem reserve_entry (program : CCalls.Events.Program E) (model : Solve.Model source)
    (kind : Kind) (env : Locals) (types : CLoops.Types) (heap : Heap)
    (base flags : Address) (capacity : Nat) (environment logger : Option Address)
    (logging : Bool) (stack : CCalls.Typed.Continuation)
    (scope : Scope env base flags capacity environment logger logging)
    (named : interface.constants CAtomicScan.function.signature.name = none) :
    CCalls.Events.internalNext program
      (.body (.running (code model kind) env types heap) "fmi3Instance" stack) =
      some (.calling CAtomicScan.function.signature.name [.pointer (some flags), .integer capacity] heap
        (.caller (.declare "size_t" "slot") (guard :: initializeInstance model kind) env types "fmi3Instance" stack)) := by
  exact CCalls.Events.named_declare_entry program env types heap "size_t" "slot"
    CAtomicScan.function.signature.name _ _ _ "fmi3Instance" stack scope.slotFresh scope.helperFresh named
    (by decide +kernel) (by simp [CCalls.arguments, eval, scope.flagsBound, scope.count])

theorem reserve_resume (program : CCalls.Events.Program E) (model : Solve.Model source)
    (kind : Kind) (env : Locals) (types : CLoops.Types) (heap : Heap) (slot : Nat)
    (stack : CCalls.Typed.Continuation) (fresh : env "slot" = none)
    (size : interface.types "size_t" = some .size) (bounded : slot < 2^64) :
    CCalls.Events.internalNext program
      (.returning (.integer slot) heap
        (.caller (.declare "size_t" "slot") (guard :: initializeInstance model kind) env types "fmi3Instance" stack)) =
      some (.body (.running (guard :: initializeInstance model kind) (reservedLocals env slot)
        (reservedTypes types) heap) "fmi3Instance" stack) :=
  CCalls.Events.declare_result program env types heap "size_t" "slot" _ "fmi3Instance" stack
    (.integer slot) (.integer slot) .size fresh size (CLoops.convert_size_nat slot bounded)

theorem successful (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (before after : Heap) (base flags : Address) (capacity : Nat)
    (environment logger : Option Address) (logging : Bool)
    (scope : Scope env base flags capacity environment logger logging)
    (storage : ∀ slot : Fin capacity, InstanceSlot.Storage before (base.index slot.val))
    (boolean : interface.types "_Bool" = some .boolean)
    (atomicPointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (constantSize : interface.types "const size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (namedHelper : interface.constants CAtomicScan.function.signature.name = none)
    (namedAtomic : interface.constants "atomic_exchange" = none)
    (atomicBound : program.externals "atomic_exchange" =
      some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (defined : program.internal.definitions CAtomicScan.function.signature.name =
      some (.tree CAtomicScan.function))
    (bounded : capacity < 2^64)
    (outcome : CAtomicScan.Outcome flags capacity 0 before trace slot after)
    (inside : slot < capacity) :
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.body (.running (code model kind) env types before) "fmi3Instance" .done) behavior ↔
      behavior = .terminates (trace.map tag) ⟨.pointer (some (base.index slot)),
        InstanceSlot.finalHeap after (base.index slot) slot kind environment logger logging⟩ := by
  have ready := (storage ⟨slot, inside⟩).preserved (CAtomicScan.outcome_storage outcome).1
  have initialized := guarded_initialization program model kind (reservedLocals env slot)
    (reservedTypes types) after base capacity ⟨slot, inside⟩ environment logger logging .done ready
    (by omega)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.instances)
    (by simp [reservedLocals, resolve, CBody.bind])
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.count)
    (by simpa [reservedLocals, CBody.bind] using scope.instanceFresh)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.environmentBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggerBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggingBound)
    pointer double handle
  have returned := CCalls.Events.internal_prefix program
    (.next (reserve_resume program model kind env types after slot .done scope.slotFresh size
      (by omega)) initialized)
    (CCalls.Events.return_forced program (.pointer (some (base.index slot)))
      (InstanceSlot.finalHeap after (base.index slot) slot kind environment logger logging))
  have called := CAtomicScan.call_prefix program tag boolean atomicPointer size constantSize namedAtomic
    atomicBound defined bounded outcome _ returned
  have complete := CCalls.Events.internal_prefix program
    (.next (reserve_entry program model kind env types before base flags capacity environment logger logging
      .done scope namedHelper) (.refl _)) called
  simpa only [List.append_nil] using complete.behaviors

end Rumoca.FMI3.StaticFactory

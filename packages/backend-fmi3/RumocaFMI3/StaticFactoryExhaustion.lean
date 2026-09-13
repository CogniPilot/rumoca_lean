import RumocaFMI3.StaticFactoryReservation
import RumocaFMI3.FactoryRejection

/-! Exhaustion of the actual static creation suffix. A bounded reservation
scan precedes the shared rejection code, with every logger outcome retained.
This is sequential C execution; public entry, concurrent histories, native
static declarations and actual-artifact binding remain separate obligations. -/
noncomputable section
namespace Rumoca.FMI3.StaticFactory
open CTree CMemory CBody
variable [interface : CInterface]

structure ReservationBindings (program : CCalls.Events.Program E)
    (tag : CAtomicBoolean.Calls.Event → E) : Prop where
  boolean : interface.types "_Bool" = some .boolean
  atomicPointer : interface.types "volatile atomic_bool *" = some .pointer
  size : interface.types "size_t" = some .size
  constantSize : interface.types "const size_t" = some .size
  namedHelper : interface.constants CAtomicScan.function.signature.name = none
  namedAtomic : interface.constants "atomic_exchange" = none
  atomicBound : program.externals "atomic_exchange" =
    some (CAtomicBoolean.Calls.exchangeExternal tag boolean)
  defined : program.internal.definitions CAtomicScan.function.signature.name =
    some (.tree CAtomicScan.function)

theorem exhaustion_path (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (before after : Heap) (base flags : Address) (capacity : Nat)
    (environment logger : Option Address) (logging : Bool)
    (scope : Scope env base flags capacity environment logger logging)
    (bindings : ReservationBindings program tag) (bounded : capacity < 2^64)
    (outcome : CAtomicScan.Outcome flags capacity 0 before trace capacity after)
    (stack : CCalls.Typed.Continuation) :
    Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (code model kind) env types before) "fmi3Instance" stack)
      (trace.map tag)
      (.body (.running (FactoryRejection.code "Instance capacity exhausted" ++ initializeInstance model kind)
        (reservedLocals env capacity) (reservedTypes types) before) "fmi3Instance" stack) := by
  have unchanged := (CAtomicScan.outcome_exhausted outcome rfl).1
  subst after
  apply (CCalls.Events.internal_path program
    (.next (reserve_entry program model kind env types before base flags capacity environment logger logging
      stack scope bindings.namedHelper) (.refl _))).trans
  refine (List.append_nil (trace.map tag)) ▸
    (CAtomicScan.call_path program tag bindings.boolean bindings.atomicPointer bindings.size
      bindings.constantSize bindings.namedAtomic bindings.atomicBound bindings.defined bounded outcome _).trans ?_
  apply CCalls.Events.internal_path program
  refine .next (reserve_resume program model kind env types before capacity stack scope.slotFresh
    bindings.size bounded) ?_
  have guarded := guard_step (reservedLocals env capacity) (reservedTypes types) before capacity capacity
    (initializeInstance model kind)
    (by simp [reservedLocals, resolve, CBody.bind])
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.count)
  simp only [↓reduceIte] at guarded
  exact .next (CCalls.Events.body_step program guarded "fmi3Instance" stack) (.refl _)

/-- With logging disabled or absent, exhaustion returns null, preserves the
complete heap, and performs only the scan's bounded sequence of atomic events. -/
theorem exhausted_silent (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (before after : Heap) (base flags : Address) (capacity : Nat)
    (environment logger : Option Address) (logging : Bool)
    (scope : Scope env base flags capacity environment logger logging)
    (bindings : ReservationBindings program tag) (bounded : capacity < 2^64)
    (outcome : CAtomicScan.Outcome flags capacity 0 before trace capacity after)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (nullBound : resolve env "NULL" = some (.pointer none))
    (quiet : (logger.isSome && logging) = false) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (code model kind) env types before) "fmi3Instance" .done) behavior ↔
      behavior = .terminates (trace.map tag) ⟨.pointer none, before⟩ := by
  have path := exhaustion_path program tag model kind env types before after base flags capacity
    environment logger logging scope bindings bounded outcome .done
  have dispatched := FactoryRejection.dispatch program "Instance capacity exhausted"
    (reservedLocals env capacity) (reservedTypes types) before (initializeInstance model kind) .done logger logging
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggerBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggingBound)
  rw [quiet] at dispatched
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at dispatched
  have finished := CCalls.Events.internal_prefix program (.next dispatched
    (FactoryRejection.return_null program (reservedLocals env capacity) (reservedTypes types) before
      (initializeInstance model kind) .done
      (by simpa [reservedLocals, resolve, CBody.bind] using nullBound) handle))
    (CCalls.Events.return_forced program (.pointer none) before)
  simpa only [List.append_nil] using (path.forced finished).behaviors behavior

/-- Enabled logging retains all callback events and writable-memory effects.
A missing represented callback outcome is wrong execution after the scan,
never successful creation or an omitted behavior. -/
theorem exhausted_logged (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (before after : Heap) (base flags : Address) (capacity : Nat)
    (environment : Option Address) (logger category message : Address)
    (name : String) (foreign : CCalls.Events.External E)
    (scope : Scope env base flags capacity environment (some logger) true)
    (bindings : ReservationBindings program tag) (bounded : capacity < 2^64)
    (outcome : CAtomicScan.Outcome flags capacity 0 before trace capacity after)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (loggerBound : env "logMessage" = some (.pointer (some logger)))
    (nullBound : resolve env "NULL" = some (.pointer none))
    (errorBound : resolve env "fmi3Error" = some (.integer 3))
    (categoryBound : interface.literals "logStatus" = some category)
    (messageBound : interface.literals "Instance capacity exhausted" = some message)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name)
    (converted : CCalls.Events.convertedArguments (Logging.signature name).parameters
      (Logging.arguments environment category message) = some (Logging.arguments environment category message))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (code model kind) env types before) "fmi3Instance" .done) behavior ↔
      (∃ events value heap, foreign.execute (Logging.arguments environment category message)
        before events value heap ∧ behavior = .terminates (trace.map tag ++ events) ⟨.pointer none, heap⟩) ∨
      ((∀ events value heap, ¬ foreign.execute (Logging.arguments environment category message)
        before events value heap) ∧ behavior = .wrong (trace.map tag)) := by
  have path := exhaustion_path program tag model kind env types before after base flags capacity
    environment (some logger) true scope bindings bounded outcome .done
  have suffix := FactoryRejection.all_behaviors program "Instance capacity exhausted"
    (reservedLocals env capacity) (reservedTypes types) before (initializeInstance model kind)
    logger category message environment name foreign
    (by simpa [reservedLocals, CBody.bind] using loggerBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggingBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.environmentBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using errorBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using nullBound)
    categoryBound messageBound address external prototype handle converted
  let returns := fun events result => ∃ value heap,
    foreign.execute (Logging.arguments environment category message) before events value heap ∧
      result = CBody.Result.mk (.pointer none) heap
  let errors := fun events : List E =>
    (∀ es value heap, ¬ foreign.execute (Logging.arguments environment category message) before es value heap) ∧
      events = []
  have complete := path.finite_behaviors returns errors (by
    intro observation
    rw [suffix observation]
    cases observation <;> simp [returns, errors]) behavior
  rw [complete]
  cases behavior <;> simp [returns, errors, and_assoc, and_comm, exists_and_left, eq_comm]

end Rumoca.FMI3.StaticFactory

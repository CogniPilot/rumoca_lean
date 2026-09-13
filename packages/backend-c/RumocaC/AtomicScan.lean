import RumocaC.AtomicScanCode
import RumocaC.AtomicCalls
import RumocaC.LoopEvents

/-! Execution of the fixed-storage reservation C helper. This uses the shared
typed call scheduler and the specified C11 sequentially consistent exchange.
Native storage/bounds and concurrent caller ownership remain separate. -/
noncomputable section
namespace Rumoca.CAtomicScan
open CTree CMemory

def locals (flags : Address) (count k : Nat) (busy : Bool) : CBody.Locals :=
  CBody.bind (CBody.bind (CBody.bind (CBody.bind (CBody.bind (fun _ => none)
    "count" (.integer count)) "flags" (.pointer (some flags))) "k" (.integer k))
    "one" (.integer 1)) "busy" (CAtomicBoolean.value busy)

def types : CLoops.Types :=
  CLoops.bindType (CLoops.bindType (CLoops.bindType (CLoops.bindType (CLoops.bindType
    (fun _ => none) "count" .size) "flags" .pointer) "k" .size) "one" .size) "busy" .boolean

variable [interface : CInterface]
set_option maxRecDepth 10000

theorem attempt_enter (program : CCalls.Events.Program E) (flags : Address) (count k : Nat)
    (busy : Bool) (heap : Heap) (rest : List Stmt) (resultType : String)
    (stack : CCalls.Typed.Continuation)
    (boolean : interface.types "_Bool" = some .boolean)
    (named : interface.constants "atomic_exchange" = none) :
    CCalls.Events.internalNext program
      (.body (.running (attempt :: rest) (locals flags count k busy) types heap) resultType stack) =
    some (.calling "atomic_exchange" [.pointer (some (flags.index k)), CAtomicBoolean.value true]
      heap (.caller (.assign (.id "busy")) rest (locals flags count k busy) types resultType stack)) := by
  have nonnegative : ¬ (k : Int) < 0 := by omega
  simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CLoops.next, CLoops.eval,
    attempt, CBody.eval, CBody.lvalue, CBody.resolve, CBody.expressionCast, CBody.cast,
    CBody.zeroLiteral, CBody.constants, CCalls.Events.enterCall, CCalls.Events.resolve,
    CCalls.Indirect.operand, CCalls.Indirect.resolve, CCalls.arguments,
    locals, CBody.bind, types, CLoops.bindType, Value.address, CAtomicBoolean.value,
    boolean, named, convert, Value.truth, nonnegative]

theorem attempt_resume (program : CCalls.Events.Program E) (flags : Address) (count k : Nat)
    (previous observed : Bool) (heap : Heap) (rest : List Stmt) (resultType : String)
    (stack : CCalls.Typed.Continuation) :
    CCalls.Events.internalNext program
      (.returning (CAtomicBoolean.value observed) heap
        (.caller (.assign (.id "busy")) rest (locals flags count k previous) types resultType stack)) =
    some (.body (.running rest (locals flags count k observed) types heap) resultType stack) := by
  have shadow : CBody.bind (locals flags count k previous) "busy" (CAtomicBoolean.value observed) =
      locals flags count k observed := by
    funext name
    simp [locals, CBody.bind]
    split <;> rfl
  cases observed <;>
    simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CCalls.Typed.resume,
      types, CLoops.bindType, locals, CBody.bind, convert, Value.truth, CAtomicBoolean.value] at shadow ⊢
  all_goals exact shadow

theorem attempt_prefix (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (operation : CAtomicBoolean.exchange before (flags.index k) true = some (observed, after))
    (rest : Transition.Events.Forced (CCalls.Events.machine program)
      (.body (.running tail (locals flags count k observed) types after) resultType stack) trace result) :
    Transition.Events.Forced (CCalls.Events.machine program)
      (.body (.running (attempt :: tail) (locals flags count k previous) types before) resultType stack)
      (tag (.exchange (flags.index k) observed true) :: trace) result := by
  apply CCalls.Events.internal_prefix program
    (.next (attempt_enter program flags count k previous before tail resultType stack boolean named) (.refl _))
  apply CCalls.Events.external_prefix program bound
    (CAtomicBoolean.Calls.arguments_converted boolean pointer (flags.index k) true)
    (CAtomicBoolean.Calls.exchange_executes tag boolean operation)
    (fun _ _ _ executed => CAtomicBoolean.Calls.exchange_unique tag boolean operation executed)
  exact CCalls.Events.internal_prefix program
    (.next (attempt_resume program flags count k previous observed after tail resultType stack) (.refl _)) rest

theorem scan_enter (flags : Address) (count k : Nat) (busy : Bool) (heap : Heap) (rest : List Stmt)
    (less : k < count) :
    CLoops.next (.running (scan :: rest) (locals flags count k busy) types heap) =
      some (.running (attempt :: selected :: advance :: scan :: rest) (locals flags count k busy) types heap) := by
  have below : (k : Int) < count := by exact_mod_cast less
  simp [scan, attempt, selected, advance, CLoops.next, CLoops.noDeclarations,
    CLoops.eval, CBody.eval, CBody.resolve, CBody.comparison, CBody.boolean,
    locals, CBody.bind, Value.truth, below]

theorem scan_stop (flags : Address) (count : Nat) (busy : Bool) (heap : Heap) (rest : List Stmt) :
    CLoops.next (.running (scan :: rest) (locals flags count count busy) types heap) =
      some (.running rest (locals flags count count busy) types heap) := by
  simp [scan, attempt, selected, advance, CLoops.next, CLoops.noDeclarations,
    CLoops.eval, CBody.eval, CBody.resolve, CBody.comparison, CBody.boolean,
    locals, CBody.bind, Value.truth]

theorem selected_step (flags : Address) (count k : Nat) (busy : Bool) (heap : Heap) (rest : List Stmt) :
    CLoops.next (.running (selected :: rest) (locals flags count k busy) types heap) =
      some (.running ((if busy then [] else [.ret (some (.id "k"))]) ++ rest)
        (locals flags count k busy) types heap) := by
  cases busy <;>
    simp [selected, CLoops.next, CLoops.noDeclarations, CLoops.eval, CBody.eval,
      CBody.resolve, CBody.boolean, locals, CBody.bind, CAtomicBoolean.value, Value.truth]

theorem advance_step (flags : Address) (count k : Nat) (busy : Bool) (heap : Heap) (rest : List Stmt)
    (bound : k + 1 < 2 ^ 64) :
    CLoops.next (.running (advance :: rest) (locals flags count k busy) types heap) =
      some (.running rest (locals flags count (k + 1) busy) types heap) := by
  have evaluated := CLoops.eval_sizeAdd (locals flags count k busy) types heap "k" "one" k 1
    (by simp [locals, CBody.bind]) (by simp [locals, CBody.bind])
    (by simp [types, CLoops.bindType]) (by simp [types, CLoops.bindType]) bound
  have shadow : CBody.bind (locals flags count k busy) "k" (.integer (k + 1)) =
      locals flags count (k + 1) busy := by
    funext name
    by_cases hk : name = "k"
    · subst name; simp [locals, CBody.bind]
    · simp [locals, CBody.bind, hk]
  have step := CLoops.assign_local (locals flags count k busy) types heap "k"
    (.bin .add (.id "k") (.id "one")) rest (.integer k) (.integer (k + 1)) (.integer (k + 1)) .size
    (by simp [locals, CBody.bind]) (by simp [types, CLoops.bindType]) evaluated
    (CLoops.convert_size_nat (k + 1) bound)
  simpa only [advance, shadow] using step

private theorem named_cast (spelling : String) (type : CType) (value result : Value)
    (typed : interface.types spelling = some type) (converted : convert type value = some result) :
    CBody.cast spelling value = some result := by
  simp only [CBody.cast, typed, bind, Option.bind_some, converted]

private theorem value_return_cast (spelling : String) (value result : Value)
    (nonvoid : spelling ≠ "void") (converted : CBody.cast spelling value = some result) :
    CCalls.returnCast spelling value = some result := by
  simp only [CCalls.returnCast, if_neg nonvoid, converted]

theorem size_cast (n : Nat) (size : interface.types "size_t" = some .size) (bound : n < 2 ^ 64) :
    CCalls.returnCast "size_t" (.integer n) = some (.integer n) :=
  value_return_cast "size_t" (.integer n) (.integer n) (by decide +kernel)
    (named_cast "size_t" .size (.integer n) (.integer n) size (CLoops.convert_size_nat n bound))

theorem size_returned (program : CCalls.Events.Program E) (heap : Heap) (n : Nat)
    (stack : CCalls.Typed.Continuation)
    (size : interface.types "size_t" = some .size)
    (bound : n < 2 ^ 64) :
    CCalls.Events.internalNext program
      (.body (.returned ⟨.integer n, heap⟩) "size_t" stack) =
      some (.returning (.integer n) heap stack) := by
  simp only [CCalls.Events.internalNext, CCalls.Typed.nextWith, size_cast n size bound,
    bind, Option.bind_some, pure]

theorem return_body (env : CBody.Locals) (heap : Heap) (name : String) (n : Nat) (rest : List Stmt)
    (found : env name = some (.integer n)) :
    CLoops.next (.running (.ret (some (.id name)) :: rest) env types heap) =
      some (.returned ⟨.integer n, heap⟩) := by
  simp [CLoops.next, CLoops.eval, CBody.eval, CBody.resolve, found]

theorem return_prefix (program : CCalls.Events.Program E) (env : CBody.Locals) (heap : Heap)
    (name : String) (n : Nat) (rest : List Stmt) (stack : CCalls.Typed.Continuation)
    (size : interface.types "size_t" = some .size)
    (found : env name = some (.integer n)) (bound : n < 2 ^ 64)
    (continued : Transition.Events.Forced (CCalls.Events.machine program)
      (.returning (.integer n) heap stack) trace result) :
    Transition.Events.Forced (CCalls.Events.machine program)
      (.body (.running (.ret (some (.id name)) :: rest) env types heap) "size_t" stack)
      trace result := by
  exact CCalls.Events.internal_prefix program
    (.next (CCalls.Events.body_step program (return_body env heap name n rest found) "size_t" stack)
      (.next (size_returned program heap n stack size bound) (.refl _))) continued

end Rumoca.CAtomicScan

import RumocaFMI3.IdentityState
import RumocaC.NamedCallSites

/-! Actual statement and call-site transitions of factory identity validation.
All intermediate locals and caller continuations are retained explicitly. -/
noncomputable section
namespace Rumoca.FMI3.Identity
open CTree CMemory

theorem length_update (args : Arguments) (length prefixLength newLength : Nat) (difference : Int) :
    CBody.bind (locals args length prefixLength difference) "length" (.integer newLength) =
      locals args newLength prefixLength difference := by
  funext key
  by_cases hd : key = "difference" <;> by_cases hp : key = "prefix" <;> by_cases hl : key = "length" <;>
    simp [locals, CBody.bind, hd, hp, hl]

theorem prefix_update (args : Arguments) (length prefixLength newPrefix : Nat) (difference : Int) :
    CBody.bind (locals args length prefixLength difference) "prefix" (.integer newPrefix) =
      locals args length newPrefix difference := by
  funext key
  by_cases hd : key = "difference" <;> by_cases hp : key = "prefix" <;>
    simp [locals, CBody.bind, hd, hp]

theorem difference_update (args : Arguments) (length prefixLength : Nat) (old result : Int) :
    CBody.bind (locals args length prefixLength old) "difference" (.integer result) =
      locals args length prefixLength result := by
  funext key
  by_cases hd : key = "difference" <;> simp [locals, CBody.bind, hd]

variable [interface : CInterface]

theorem measure_enter (program : CCalls.Events.Program E) (args : Arguments) (length prefixLength : Nat)
    (difference : Int) (heap : Heap) (rest : List Stmt) (stack : CCalls.Typed.Continuation)
    (named : interface.constants "strlen" = none) :
    CCalls.Events.internalNext program
      (.body (.running (measure :: rest) (locals args length prefixLength difference) types heap) "fmi3Boolean" stack) =
    some (.calling "strlen" [.pointer args.name] heap
      (.caller (.assign (.id "length")) rest (locals args length prefixLength difference) types "fmi3Boolean" stack)) := by
  apply CCalls.Events.named_assign_entry program _ _ _ _ _ _ _ _ _ _ (.integer length) .size
  · simp [locals, CBody.bind]
  · simp [types, CLoops.bindType]
  · simp [locals, parameterLocals, CBody.bind]
  · exact named
  · decide
  · simp [CCalls.arguments, CBody.eval, CBody.resolve, locals, parameterLocals, CBody.bind]

theorem prefix_enter (program : CCalls.Events.Program E) (args : Arguments) (length prefixLength : Nat)
    (difference : Int) (heap : Heap) (rest : List Stmt) (stack : CCalls.Typed.Continuation)
    (named : interface.constants "strspn" = none) :
    CCalls.Events.internalNext program
      (.body (.running (measurePrefix :: rest) (locals args length prefixLength difference) types heap) "fmi3Boolean" stack) =
    some (.calling "strspn" [.pointer args.name, .pointer args.whitespace] heap
      (.caller (.assign (.id "prefix")) rest (locals args length prefixLength difference) types "fmi3Boolean" stack)) := by
  apply CCalls.Events.named_assign_entry program _ _ _ _ _ _ _ _ _ _ (.integer prefixLength) .size
  · simp [locals, CBody.bind]
  · simp [types, CLoops.bindType]
  · simp [locals, parameterLocals, CBody.bind]
  · exact named
  · decide
  · simp [CCalls.arguments, CBody.eval, CBody.resolve, locals, parameterLocals, CBody.bind]

theorem compare_enter (program : CCalls.Events.Program E) (args : Arguments) (length prefixLength : Nat)
    (difference : Int) (heap : Heap) (rest : List Stmt) (stack : CCalls.Typed.Continuation)
    (named : interface.constants "strcmp" = none) :
    CCalls.Events.internalNext program
      (.body (.running (compareToken :: rest) (locals args length prefixLength difference) types heap) "fmi3Boolean" stack) =
    some (.calling "strcmp" [.pointer args.token, .pointer args.expected] heap
      (.caller (.assign (.id "difference")) rest (locals args length prefixLength difference) types "fmi3Boolean" stack)) := by
  apply CCalls.Events.named_assign_entry program _ _ _ _ _ _ _ _ _ _ (.integer difference) .int32
  · simp [locals, CBody.bind]
  · simp [types, CLoops.bindType]
  · simp [locals, parameterLocals, CBody.bind]
  · exact named
  · decide
  · simp [CCalls.arguments, CBody.eval, CBody.resolve, locals, parameterLocals, CBody.bind]

theorem length_resume (program : CCalls.Events.Program E) (args : Arguments)
    (old prefixLength newLength : Nat) (difference : Int) (heap : Heap) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (bound : newLength < 2^64) :
    CCalls.Events.internalNext program (.returning (.integer newLength) heap
      (.caller (.assign (.id "length")) rest (locals args old prefixLength difference) types "fmi3Boolean" stack)) =
    some (.body (.running rest (locals args newLength prefixLength difference) types heap) "fmi3Boolean" stack) := by
  simpa only [length_update] using CCalls.Events.assign_result program (locals args old prefixLength difference)
    types heap "length" rest "fmi3Boolean" stack (.integer old) (.integer newLength) (.integer newLength) .size
    (by simp [locals, CBody.bind]) (by simp [types, CLoops.bindType]) (CLoops.convert_size_nat newLength bound)

theorem prefix_resume (program : CCalls.Events.Program E) (args : Arguments)
    (length old newPrefix : Nat) (difference : Int) (heap : Heap) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (bound : newPrefix < 2^64) :
    CCalls.Events.internalNext program (.returning (.integer newPrefix) heap
      (.caller (.assign (.id "prefix")) rest (locals args length old difference) types "fmi3Boolean" stack)) =
    some (.body (.running rest (locals args length newPrefix difference) types heap) "fmi3Boolean" stack) := by
  simpa only [prefix_update] using CCalls.Events.assign_result program (locals args length old difference)
    types heap "prefix" rest "fmi3Boolean" stack (.integer old) (.integer newPrefix) (.integer newPrefix) .size
    (by simp [locals, CBody.bind]) (by simp [types, CLoops.bindType]) (CLoops.convert_size_nat newPrefix bound)

theorem compare_resume (program : CCalls.Events.Program E) (args : Arguments)
    (length prefixLength : Nat) (old result : Int) (heap : Heap) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (bound : -(2^31) ≤ result ∧ result < 2^31) :
    CCalls.Events.internalNext program (.returning (.integer result) heap
      (.caller (.assign (.id "difference")) rest (locals args length prefixLength old) types "fmi3Boolean" stack)) =
    some (.body (.running rest (locals args length prefixLength result) types heap) "fmi3Boolean" stack) := by
  simpa only [difference_update] using CCalls.Events.assign_result program (locals args length prefixLength old)
    types heap "difference" rest "fmi3Boolean" stack (.integer old) (.integer result) (.integer result) .int32
    (by simp [locals, CBody.bind]) (by simp [types, CLoops.bindType]) (by simp only [convert, if_pos bound])

theorem blank_step (args : Arguments) (length prefixLength : Nat) (difference : Int)
    (heap : Heap) (rest : List Stmt) :
    CLoops.next (.running (blank :: rest) (locals args length prefixLength difference) types heap) =
      some (.running ((if prefixLength = length then [falseReturn] else []) ++ rest)
        (locals args length prefixLength difference) types heap) := by
  by_cases same : prefixLength = length <;>
    simp [blank, falseReturn, CLoops.next, CLoops.noDeclarations, CLoops.eval, CBody.eval,
      CBody.resolve, CBody.comparison, CBody.boolean, Value.truth, locals, CBody.bind, same]

theorem boolean_return_cast (boolean : interface.types "fmi3Boolean" = some .boolean) (flag : Bool) :
    CCalls.returnCast "fmi3Boolean" (CBody.boolean flag) = some (CBody.boolean flag) := by
  cases flag <;> simp [CCalls.returnCast, CBody.cast, boolean, convert, CBody.boolean, Value.truth]

theorem false_return (program : CCalls.Events.Program E) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (rest : List Stmt) (stack : CCalls.Typed.Continuation)
    (boolean : interface.types "fmi3Boolean" = some .boolean) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (falseReturn :: rest) env types heap) "fmi3Boolean" stack)
      (.returning (CBody.boolean false) heap stack) := by
  apply CCalls.Events.expression_return program env types heap _ rest "fmi3Boolean" stack
    (CBody.boolean false) (CBody.boolean false)
  · simp [CLoops.eval, CBody.eval, CBody.expressionCast, CBody.zeroLiteral,
      CBody.cast, boolean, convert, Value.truth, CBody.boolean]
  · exact boolean_return_cast boolean false

theorem comparison_return (program : CCalls.Events.Program E) (args : Arguments)
    (length prefixLength : Nat) (difference : Int) (heap : Heap) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (boolean : interface.types "fmi3Boolean" = some .boolean) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (comparisonReturn :: rest) (locals args length prefixLength difference) types heap) "fmi3Boolean" stack)
      (.returning (CBody.boolean (decide (difference = 0))) heap stack) := by
  apply CCalls.Events.expression_return program (locals args length prefixLength difference) types heap _ rest
    "fmi3Boolean" stack (CBody.boolean (decide (difference = 0))) (CBody.boolean (decide (difference = 0)))
  · by_cases zero : difference = 0 <;>
      simp [CLoops.eval, CBody.eval, CBody.resolve, locals, CBody.bind,
        CBody.comparison, CBody.expressionCast, CBody.zeroLiteral, CBody.cast, boolean, convert,
        Value.truth, CBody.boolean, zero]
  · exact boolean_return_cast boolean _

end Rumoca.FMI3.Identity

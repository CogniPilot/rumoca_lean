import RumocaC.AtomicScanProofs
import RumocaC.CallSignature

/-! Complete calls of the fixed-storage reservation helper, from fresh typed
parameters through local initialization and the loop to the returned index.
Admitted entry storage guarantees termination; no successful C execution is
assumed. This remains a sequential component of the concurrency contract. -/
noncomputable section
namespace Rumoca.CAtomicScan
open CTree CMemory

def parameterLocals (flags : Address) (count : Nat) : CBody.Locals :=
  CBody.bind (CBody.bind (fun _ => none) "count" (.integer count)) "flags" (.pointer (some flags))

def parameterTypes : CLoops.Types :=
  CLoops.bindType (CLoops.bindType (fun _ => none) "count" .size) "flags" .pointer

variable [interface : CInterface]
set_option maxRecDepth 10000

theorem parameters_bound (flags : Address) (count : Nat)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size) (bounded : count < 2 ^ 64) :
    CCalls.parameters function.signature.parameters [.pointer (some flags), .integer count] =
      some (parameterLocals flags count) := by
  have arguments : CCalls.Signature.Arguments function.signature.parameters
      [.pointer (some flags), .integer count] [.pointer (some flags), .integer count] :=
    .cons pointer rfl (.cons size (CLoops.convert_size_nat count bounded) .nil)
  have binding := CCalls.Signature.parameters_bound arguments (by decide +kernel)
  simpa only [function, CCalls.Signature.locals_cons, CCalls.Signature.locals, List.map_nil,
    List.zip_nil_left, List.lookup_nil, parameterLocals] using binding

theorem parameter_types
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size) :
    CLoops.Calls.parameterTypes function.signature.parameters = some parameterTypes := by
  simp [CLoops.Calls.parameterTypes, function, CCalls.parameterType,
    pointer, size, parameterTypes, CLoops.bindType]

theorem initialization (flags : Address) (count : Nat) (heap : Heap)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (constantSize : interface.types "const size_t" = some .size) :
    CLoops.run 3 (.running function.body (parameterLocals flags count) parameterTypes heap) =
      some (.running [scan, .ret (some (.id "count"))] (locals flags count 0 false) types heap) := by
  let env0 := parameterLocals flags count
  let env1 := CBody.bind env0 "k" (.integer 0)
  let env2 := CBody.bind env1 "one" (.integer 1)
  let types1 := CLoops.bindType parameterTypes "k" .size
  let types2 := CLoops.bindType types1 "one" .size
  let tail : List Stmt := [scan, .ret (some (.id "count"))]
  let busyDecl := Stmt.declare "_Bool" "busy" (.cast "_Bool" (.nat 0))
  have first := CLoops.declare_local env0 parameterTypes heap "size_t" "k" (.nat 0)
    (.declare "const size_t" "one" (.nat 1) :: busyDecl :: tail) .size (.integer 0) (.integer 0)
    size (by simp [env0, parameterLocals, CBody.bind]) rfl
    (CLoops.convert_size_nat 0 (by decide +kernel))
  have second := CLoops.declare_local env1 types1 heap "const size_t" "one" (.nat 1)
    (busyDecl :: tail) .size (.integer 1) (.integer 1) constantSize
    (by simp [env1, env0, parameterLocals, CBody.bind]) rfl
    (CLoops.convert_size_nat 1 (by decide +kernel))
  have third := CLoops.declare_local env2 types2 heap "_Bool" "busy" (.cast "_Bool" (.nat 0))
    tail .boolean (.integer 0) (.integer 0) boolean
    (by simp [env2, env1, env0, parameterLocals, CBody.bind])
    (by simp [CLoops.eval, CBody.eval, CBody.expressionCast, CBody.cast, CBody.zeroLiteral,
      boolean, convert, Value.truth]) rfl
  change CLoops.run 3 (.running
    (.declare "size_t" "k" (.nat 0) :: .declare "const size_t" "one" (.nat 1) :: busyDecl :: tail)
    env0 parameterTypes heap) = _
  dsimp only [env1, types1] at second
  dsimp only [env2, types2, env1, types1, busyDecl] at third
  simp only [CLoops.run, first, second, third, bind, Option.bind_some, busyDecl]
  rfl

theorem call_prefix (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (constantSize : interface.types "const size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (bounded : count < 2 ^ 64)
    (outcome : Outcome flags count 0 before trace result after) (stack : CCalls.Typed.Continuation)
    (continued : Transition.Events.Forced (CCalls.Events.machine program)
      (.returning (.integer result) after stack) continuationTrace final) :
    Transition.Events.Forced (CCalls.Events.machine program)
      (.calling function.signature.name [.pointer (some flags), .integer count] before stack)
      (trace.map tag ++ continuationTrace) final := by
  apply CCalls.Events.internal_prefix program
    (.next (CCalls.Events.tree_entry program _ _ before stack function _ _ defined
      (parameters_bound flags count pointer size bounded) (parameter_types pointer size)) (.refl _))
  apply CCalls.Events.internal_prefix program
    (CCalls.Events.body_reaches program (CLoops.run_reaches (initialization flags count before boolean size constantSize))
      "size_t" stack)
  exact scan_prefix program tag boolean pointer size named bound bounded outcome false stack continued

/-- Total behavior classification for every admitted flag array and extent.
The result includes the checked bound on work, not an assumed terminating run. -/
theorem call_correct (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (constantSize : interface.types "const size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (bounded : count < 2 ^ 64) (ready : Ready flags count before) :
    ∃ trace result after, Outcome flags count 0 before trace result after ∧
      result ≤ count ∧ trace.length ≤ count ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling function.signature.name [.pointer (some flags), .integer count] before .done) behavior ↔
        behavior = .terminates (trace.map tag) ⟨.integer result, after⟩ := by
  obtain ⟨trace, result, after, outcome⟩ := outcome_exists ready (Nat.zero_le count)
  have forced := call_prefix program tag boolean pointer size constantSize named bound defined bounded outcome .done
    (CCalls.Events.return_forced program (.integer result) after)
  have limits := outcome_bounds outcome
  exact ⟨trace, result, after, outcome, limits.2.1, by simpa using limits.2.2,
    by simpa only [List.append_nil] using forced.behaviors⟩

end Rumoca.CAtomicScan

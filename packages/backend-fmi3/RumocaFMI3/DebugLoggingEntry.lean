import RumocaFMI3.DebugLoggingBody
import RumocaFMI3.LifecycleGuard
import RumocaC.BodyEvents
import RumocaC.CallSignature

/-! Public FMI logging arguments and the shared instance/lifecycle guard.
The function tree is model-independent; artifact acceptance must establish that
the actual generated definition is this tree in its prepared runtime table. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory CBody CLoops
set_option maxRecDepth 10000

def signature : Signature := ⟨"fmi3Status", "fmi3SetDebugLogging",
  [⟨"fmi3Instance", "instance", false⟩, ⟨"fmi3Boolean", "loggingOn", false⟩,
   ⟨"size_t", "nCategories", false⟩, ⟨"const fmi3String", "categories", true⟩]⟩

def function : Function := ⟨signature, Runtime.require .logging ++ code, false⟩

theorem function_eq (model : Solve.FMI3Model source) :
    Runtime.function model signature = function := rfl

def arguments (handle : Option Address) (enabled : Bool) (count : UInt64)
    (categories : Option Address) : List Value :=
  [.pointer handle, boolean enabled, .integer count.toNat, .pointer categories]

def parameters (handle : Option Address) (enabled : Bool) (count : UInt64)
    (categories : Option Address) : Locals :=
  CBody.bind (CBody.bind (CBody.bind (CBody.bind (fun _ => none)
    "categories" (.pointer categories)) "nCategories" (.integer count.toNat))
    "loggingOn" (boolean enabled)) "instance" (.pointer handle)

def locals (p : Address) (enabled : Bool) (count : UInt64) (categories : Option Address) : Locals :=
  CBody.bind (parameters (some p) enabled count categories) "m" (.pointer (some p))

theorem public_scope (p : Address) (enabled : Bool) (count : UInt64) (categories : Option Address) :
    Scope (locals p enabled count categories) p categories count.toNat enabled := by
  constructor <;> simp [locals, parameters, CBody.bind]

theorem function_closed : function.body.all CBodyEmbedding.closedBlocks = true := by
  simp [function, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
    Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret,
    code, missing, failure, validation, loop, iteration, rejectNull, comparison,
    rejectDifference, finish, writeLogging, counterStep, CBodyEmbedding.closedBlocks, noDeclarations]

variable [interface : CInterface]

structure EntryTypes : Prop where
  handle : interface.types "fmi3Instance" = some .pointer
  boolean : interface.types "fmi3Boolean" = some .boolean
  size : interface.types "size_t" = some .size
  strings : interface.types "const fmi3String *" = some .pointer
  instancePointer : interface.types "Instance *" = some .pointer
  nullPointer : interface.types "void *" = some .pointer

theorem parameters_bound (types : EntryTypes) (handle : Option Address) (enabled : Bool)
    (count : UInt64) (categories : Option Address) :
    CCalls.parameters signature.parameters (arguments handle enabled count categories) =
      some (parameters handle enabled count categories) := by
  have converted : CCalls.Signature.Arguments signature.parameters
      (arguments handle enabled count categories) (arguments handle enabled count categories) :=
    .cons types.handle rfl (.cons types.boolean (by cases enabled <;> decide)
      (.cons types.size (convert_size_nat count.toNat count.toNat_lt_size)
        (.cons types.strings rfl .nil)))
  have bound := CCalls.Signature.parameters_bound converted (by decide)
  simpa only [signature, arguments, CCalls.Signature.locals_cons, CCalls.Signature.locals,
    List.map_nil, List.zip_nil_left, List.lookup_nil, parameters] using bound

set_option maxHeartbeats 1000000 in
/-- Logging is allowed in every represented common ME/CS lifecycle mode. -/
theorem logging_guard_run (types : EntryTypes) (env : Locals) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode) (rest : List Stmt)
    (handle : env "instance" = some (.pointer (some p))) (fresh : env "m" = none)
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code)) :
    CBody.run 3 (.running (Runtime.require .logging ++ rest) env heap) =
      some (.running rest (CBody.bind env "m" (.pointer (some p))) heap) := by
  cases kind <;> cases mode <;>
    simp [CBody.run, CBody.next, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
      Runtime.reject, Runtime.branch, Runtime.ret, Runtime.negate, Runtime.v,
      Runtime.allowedExpression, Runtime.either, Runtime.both, Runtime.eqv,
      Runtime.field, Runtime.any, Runtime.mode, Runtime.n, permittedModes,
      Mode.code, Kind.code, CBody.bind, CBody.eval, resolve, constants,
      Expr.nullPointer, expressionCast, zeroLiteral, CBody.cast, types.instancePointer,
      types.nullPointer, convert, handle, fresh, kindValue, modeValue, CBody.comparison,
      boolean, Value.truth, Value.address]

theorem entry_run (types : EntryTypes) (heap : Heap) (p : Address) (enabled : Bool)
    (count : UInt64) (categories : Option Address) (kind : Kind) (mode : Mode)
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code)) :
    CBody.run 3 (.running function.body (parameters (some p) enabled count categories) heap) =
      some (.running code (locals p enabled count categories) heap) :=
  logging_guard_run types (parameters (some p) enabled count categories) heap p kind mode code
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) kindValue modeValue

theorem null_run (types : EntryTypes) (heap : Heap) (enabled : Bool) (count : UInt64)
    (categories : Option Address) (error : interface.constants "fmi3Error" = some (.integer 3)) :
    CBody.run 3 (.running function.body (parameters none enabled count categories) heap) =
      some (.returned ⟨.integer 3, heap⟩) := by
  simp [function, CBody.run, CBody.next, Runtime.require, Runtime.instancePrefix,
    Runtime.branch, Runtime.ret, Runtime.v, parameters, CBody.bind, CBody.eval, resolve, constants,
    Expr.nullPointer, expressionCast, zeroLiteral, CBody.cast, types.instancePointer,
    types.nullPointer, convert, CBody.comparison, boolean, Value.truth, error]

theorem public_prefix (types : EntryTypes) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (enabled : Bool) (count : UInt64) (categories : Option Address)
    (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions signature.name = some (.tree function))
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code)) :
    ∃ localsTypes, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling signature.name (arguments (some p) enabled count categories) heap .done)
      (.body (.running code (locals p enabled count categories) localsTypes heap) "fmi3Status" .done) :=
  CCalls.Events.body_prefix_reaches program function (arguments (some p) enabled count categories)
    (parameters (some p) enabled count categories) (locals p enabled count categories) heap heap
    code .done 3 defined (parameters_bound types (some p) enabled count categories) function_closed
    (entry_run types heap p enabled count categories kind mode kindValue modeValue)

theorem public_null_behaviors (types : EntryTypes) (program : CCalls.Events.Program E)
    (heap : Heap) (enabled : Bool) (count : UInt64) (categories : Option Address)
    (defined : program.internal.definitions signature.name = some (.tree function))
    (error : interface.constants "fmi3Error" = some (.integer 3))
    (status : CCalls.returnCast "fmi3Status" (.integer 3) = some (.integer 3)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments none enabled count categories) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩ :=
  CCalls.Events.body_call_behaviors program function (arguments none enabled count categories)
    (parameters none enabled count categories) heap ⟨.integer 3, heap⟩ (.integer 3) 3 defined
    (parameters_bound types none enabled count categories) function_closed
    (null_run types heap enabled count categories error) status behavior

end Rumoca.FMI3.DebugLogging
end

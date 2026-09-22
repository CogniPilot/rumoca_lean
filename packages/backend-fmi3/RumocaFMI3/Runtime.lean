import RumocaCore.FMI3.Lifecycle
import RumocaFMI3.Metadata
import RumocaC.Interface
import RumocaC.Body
import RumocaC.InitializationCode
import RumocaFMI3.IdentityCode
import RumocaFMI3.StaticFactoryCode
import RumocaFMI3.StaticReleaseCode
import RumocaFMI3.StaticStorageCode
import RumocaFMI3.DebugLoggingCode

/-! FMI ABI construction. Numerical evaluation is delegated to the existing
verified Solve/C kernel. The lifecycle table supplies guards. C memory,
callbacks and the emitted adapter still need a full execution bridge; they
must not be included in the scalar compiler's existing correctness claim. -/
namespace Rumoca.FMI3.Runtime
open CTree

def v := Expr.id
def n := Expr.nat
def call (name : String) (args : List Expr := []) := Expr.call (v name) args
def field (name : String) := Expr.field (v "m") name true
/-- Pointer to the first element of an array-typed record member: `&(m->name[0])`.
For an array member `double name[N]` this is the pointer-to-element type
(`double *`) the tensor copy loops and the tensor kernel prototype require; the
scalar member idiom `&(m->name)` (`.address (field name)`) is exact only for a
scalar member such as the rank-0 time base. The denoted address is the member's
first element cell, so region reads and writes are unchanged. -/
def region (name : String) := Expr.address (Expr.index (field name) (n 0))

open CMemory in
/-- `region name` evaluates to a pointer to the member's first element cell,
heap-independently, whenever `m` resolves to the instance pointer. The denoted
address is the same `m.member name` the scalar `&(m->name)` idiom denotes, so
region reads and writes are unchanged. -/
theorem eval_region [Rumoca.CInterface] (env : CBody.Locals) (heap : Heap)
    (name : String) (m : Address)
    (mResolves : CBody.resolve env "m" = some (.pointer (some m))) :
    CBody.eval env heap (region name) = some (.pointer (some (m.member name))) := by
  simp [region, field, v, n, CBody.eval, CBody.lvalue, mResolves, Value.address]
def x := Expr.field (field "model") "x"
def eqv := Expr.bin BinOp.eq
def nev := Expr.bin BinOp.ne
def lt := Expr.bin BinOp.lt
def gt := Expr.bin BinOp.gt
def le := Expr.bin BinOp.le
def ge := Expr.bin BinOp.ge
def both := Expr.bin BinOp.and
def either := Expr.bin BinOp.or
def negate := Expr.not
def ret (e : Expr) := Stmt.ret (some e)
def ok := ret (v "fmi3OK")
def put (name : String) (e : Expr) := Stmt.assign (field name) e
def out (name : String) (e : Expr) := Stmt.assign (.deref (v name)) e
def branch (c : Expr) (yes : List Stmt) (no : List Stmt := []) := Stmt.branch c yes no
def fail (message : String) := ret (call "fail" [v "m", .str message])
def reject (c : Expr) (message : String) := branch c [fail message]
def log (status : String) (message : Expr) :=
  branch (both (nev (field "logger") Expr.nullPointer) (field "logging"))
  [.eval (.call (field "logger") [field "environment", v status, .str "logStatus", message])]
def finite (e : Expr) := call "isfinite" [e]
def mode (m : Mode) := n m.code
def setMode (m : Mode) := put "mode" (mode m)

def any (es : List Expr) : Expr := es.foldr either (n 0)
def all (es : List Expr) : Expr := es.foldr both (n 1)

def allowedExpression (cmd : Command) : Expr :=
  either
    (both (eqv (field "kind") (n 0))
      (any ((permittedModes cmd .me).map fun m => eqv (field "mode") (mode m))))
    (both (eqv (field "kind") (n 1))
      (any ((permittedModes cmd .cs).map fun m => eqv (field "mode") (mode m))))

def instancePrefix : List Stmt := [
  .declare "Instance *" "m" (.cast "Instance *" (v "instance")),
  branch (.bin .eq (v "m") Expr.nullPointer) [ret (v "fmi3Error")]]

@[simp] def modeGuard (c : Command) : Stmt :=
  reject (negate (allowedExpression c)) "Call is not allowed in the current FMI state"

def require (c : Command) : List Stmt := instancePrefix ++ [modeGuard c]

def countLoop (count : Expr) (body : List Stmt) : List Stmt := [
  .declare "size_t" "k" (n 0),
  .whileLoop (lt (v "k") count) (body ++ [.assign (v "k") (.bin .add (v "k") (n 1))])]

def pointerCheck (names : List String) : Stmt :=
  reject (any (names.map fun p => negate (v p))) "Missing output pointer"

def makeInstance (m : Solve.FMI3Model source) (kind : Kind) : List Stmt :=
  FactoryPrefix.validation m :: FactoryPrefix.identityGuard :: StaticFactory.code m.solve kind

def scalarAccessCheck (array count : String) : List Stmt := [
  reject (either (nev (v count) (n 1)) (negate (v array))) "Expected one continuous state"]

def getFloat64 : List Stmt := require .get ++ [
  reject (any [nev (v "nValueReferences") (v "nValues"),
    both (v "nValueReferences") (negate (v "valueReferences")),
    both (v "nValues") (negate (v "values"))]) "Invalid Float64 array lengths or pointers"] ++
  countLoop (v "nValueReferences") [
    reject (gt (.index (v "valueReferences") (v "k")) (n 2)) "Unknown value reference"] ++
  [Stmt.assign (v "k") (n 0), .whileLoop (lt (v "k") (v "nValueReferences")) [
    branch (eqv (.index (v "valueReferences") (v "k")) (n 0))
      [.assign (.index (v "values") (v "k")) (field "time")]
      [branch (eqv (.index (v "valueReferences") (v "k")) (n 1))
        [.assign (.index (v "values") (v "k")) x]
        [.assign (.index (v "values") (v "k")) (call "model_rhs" [.address (field "model")])]],
    .assign (v "k") (.bin .add (v "k") (n 1))], ok]

/-- Value validation and writes after the setter's instance/lifecycle guards. -/
def setFloat64Values : List Stmt := [
  reject (any [nev (v "nValueReferences") (v "nValues"),
    both (v "nValueReferences") (negate (v "valueReferences")),
    both (v "nValues") (negate (v "values"))]) "Invalid Float64 array lengths or pointers"] ++
  countLoop (v "nValueReferences") [
    reject (either (nev (.index (v "valueReferences") (v "k")) (n 1))
      (negate (finite (.index (v "values") (v "k"))))) "Only a finite continuous state value may be set"] ++
  [Stmt.assign (v "k") (n 0), .whileLoop (lt (v "k") (v "nValueReferences")) [
    .assign x (.index (v "values") (v "k")), .assign (v "k") (.bin .add (v "k") (n 1))], ok]

/-- The instance binding has function scope. Empty calls use the general setter
endpoint guard and return before validating pointers or writing model values. -/
def setFloat64 : List Stmt := instancePrefix ++ [
  branch (both (eqv (v "nValueReferences") (n 0)) (eqv (v "nValues") (n 0)))
    [modeGuard .setVariables, ok], modeGuard .setStart] ++ setFloat64Values

def stepDiscard : List Stmt :=
  [log "fmi3Discard" (.str "Step cannot be completed on the unit internal time grid"),
   ret (v "fmi3Discard")]

def stepRounding : List Stmt := [
  .declare "int" "rounding" (call "fegetround"),
  reject (nev (v "rounding") (v "FE_TONEAREST")) "Round-to-nearest arithmetic is required"]

def stepClock : List Stmt := [
  .declare "double" "next" (.bin .add (field "time") (v "communicationStepSize")),
  reject (both (field "stopDefined") (gt (v "next") (field "stop"))) "Step exceeds stopTime",
  branch (any [negate (finite (v "next")), le (v "next") (field "time")]) stepDiscard]

def stepGrid : List Stmt := [
  .declare "double" "floored" (call "floor" [v "communicationStepSize"]),
  branch (any [nev (v "floored") (v "communicationStepSize"),
    gt (v "communicationStepSize") (n 1000000)]) stepDiscard]

def stepSolve : List Stmt := [
  .eval (call "model_advance" [.address (field "model"), .cast "uint64_t" (v "communicationStepSize")]),
  put "time" (v "next"), out "lastSuccessfulTime" (v "next"), ok]

/-- Ordinary library calls have explicit function-scope destinations. Keep
the stop check before the discard checks, and floor after finite progress. -/
def doStep : List Stmt := require .doStep ++ [
  pointerCheck ["eventHandlingNeeded", "terminateSimulation", "earlyReturn", "lastSuccessfulTime"],
  out "eventHandlingNeeded" (n 0), out "terminateSimulation" (n 0), out "earlyReturn" (n 0),
  out "lastSuccessfulTime" (field "time"),
  reject (any [negate (finite (v "currentCommunicationPoint")),
    negate (finite (v "communicationStepSize")),
    nev (v "currentCommunicationPoint") (field "time"), le (v "communicationStepSize") (n 0)])
    "Invalid communication point or step size"] ++
  stepRounding ++ stepClock ++ stepGrid ++ stepSolve

def invalidTime : Expr := any [negate (finite (v "time")), lt (v "time") (field "timeMin"),
  both (field "stopDefined") (gt (v "time") (field "stop"))]

def raiseField (name : String) (candidate : Expr) : Stmt :=
  branch (lt (field name) candidate) [put name candidate]

def initialTime : List Stmt :=
  [put "time" (v "startTime"), put "timeMin" (v "startTime"),
   put "eventTime" (v "startTime"), put "lastCompleted" (v "startTime")]

def eventTime : List Stmt :=
  [put "eventTime" (field "time"), raiseField "timeMin" (field "time")]

def completedTime : List Stmt :=
  [put "timeMin" (field "eventTime"), raiseField "timeMin" (field "lastCompleted"),
   put "lastCompleted" (field "time")]

def body (m : Solve.FMI3Model source) (sig : Signature) : List Stmt :=
  match sig.name with
  | "fmi3GetVersion" => [ret (.str "3.0")]
  | "fmi3InstantiateModelExchange" => makeInstance m .me
  | "fmi3InstantiateCoSimulation" =>
    FactoryPrefix.capabilityGuard :: makeInstance m .cs
  | "fmi3InstantiateScheduledExecution" => [
    branch (both (v "logMessage") (v "loggingOn")) [.eval (.call (v "logMessage")
      [v "instanceEnvironment", v "fmi3Error", .str "logStatus", .str "Scheduled Execution is unsupported"])], ret (v "NULL")]
  | "fmi3FreeInstance" => StaticRelease.function.body
  | "fmi3SetDebugLogging" => require .logging ++ DebugLogging.code
  | "fmi3EnterInitializationMode" => require .enterInitialization ++ [
    reject (any [negate (finite (v "startTime")),
      both (v "stopTimeDefined") (either (negate (finite (v "stopTime"))) (lt (v "stopTime") (v "startTime")))])
      "Invalid initialization time interval"] ++ initialTime ++ [
    put "stop" (v "stopTime"), put "stopDefined" (v "stopTimeDefined"),
    setMode .initialization, ok]
  | "fmi3ExitInitializationMode" => require .exitInitialization ++ [
    branch (eqv (field "kind") (n 0)) [setMode .event] [setMode .step], ok]
  | "fmi3EnterEventMode" => require .enterEvent ++ eventTime ++ [setMode .event, ok]
  | "fmi3EnterContinuousTimeMode" => require .enterContinuous ++ [setMode .continuous, ok]
  | "fmi3EvaluateDiscreteStates" => require .evaluateDiscrete ++ [ok]
  | "fmi3UpdateDiscreteStates" => require .updateDiscrete ++ [
    pointerCheck ["discreteStatesNeedUpdate", "terminateSimulation", "nominalsOfContinuousStatesChanged",
      "valuesOfContinuousStatesChanged", "nextEventTimeDefined", "nextEventTime"],
    out "discreteStatesNeedUpdate" (n 0), out "terminateSimulation" (n 0),
    out "nominalsOfContinuousStatesChanged" (n 0), out "valuesOfContinuousStatesChanged" (n 0),
    out "nextEventTimeDefined" (n 0), out "nextEventTime" (n 0), ok]
  | "fmi3Terminate" => require .terminate ++ [setMode .terminated, ok]
  | "fmi3Reset" => require .reset ++ [
    (CInitialization.emit m.solve x).statement,
    put "time" (n 0), put "timeMin" (n 0), put "eventTime" (n 0), put "lastCompleted" (n 0),
    put "stop" (n 0), put "stopDefined" (n 0), setMode .instantiated, ok]
  | "fmi3GetFloat64" => getFloat64
  | "fmi3SetFloat64" => setFloat64
  | "fmi3SetTime" => require .setTime ++ [
    reject invalidTime "Time is outside the permitted interval",
    put "time" (v "time"), ok]
  | "fmi3SetContinuousStates" => require .setStates ++ scalarAccessCheck "continuousStates" "nContinuousStates" ++ [
    reject (negate (finite (.index (v "continuousStates") (n 0)))) "State must be finite",
    .assign x (.index (v "continuousStates") (n 0)), ok]
  | "fmi3GetContinuousStates" => require .getStates ++ scalarAccessCheck "continuousStates" "nContinuousStates" ++
    [.assign (.index (v "continuousStates") (n 0)) x, ok]
  | "fmi3GetContinuousStateDerivatives" => require .getDerivatives ++ scalarAccessCheck "derivatives" "nContinuousStates" ++
    [.assign (.index (v "derivatives") (n 0)) (call "model_rhs" [.address (field "model")]), ok]
  | "fmi3GetNominalsOfContinuousStates" => require .getNominals ++ scalarAccessCheck "nominals" "nContinuousStates" ++
    [.assign (.index (v "nominals") (n 0)) (n 1), ok]
  | "fmi3GetNumberOfContinuousStates" => require .getCounts ++ [pointerCheck ["nContinuousStates"], out "nContinuousStates" (n 1), ok]
  | "fmi3GetNumberOfEventIndicators" => require .getCounts ++ [pointerCheck ["nEventIndicators"], out "nEventIndicators" (n 0), ok]
  | "fmi3GetEventIndicators" => require .getDerivatives ++ [reject (nev (v "nEventIndicators") (n 0)) "There are no event indicators", ok]
  | "fmi3CompletedIntegratorStep" => require .completedStep ++ [
    pointerCheck ["enterEventMode", "terminateSimulation"], out "enterEventMode" (n 0), out "terminateSimulation" (n 0)] ++
    completedTime ++ [ok]
  | "fmi3DoStep" => doStep
  | _ =>
    if (sig.name.startsWith "fmi3Get" || sig.name.startsWith "fmi3Set") &&
        (sig.parameters.any (·.name == "nValueReferences")) &&
        (sig.parameters.any (·.name == "nValues")) &&
        (sig.name.endsWith "Float32" || sig.name.endsWith "Int8" || sig.name.endsWith "UInt8" ||
         sig.name.endsWith "Int16" || sig.name.endsWith "UInt16" || sig.name.endsWith "Int32" ||
         sig.name.endsWith "UInt32" || sig.name.endsWith "Int64" || sig.name.endsWith "UInt64" ||
         sig.name.endsWith "Boolean" || sig.name.endsWith "String" || sig.name.endsWith "Binary") then
      require (if sig.name.startsWith "fmi3Set" then .setVariables else .get) ++
      [branch (both (eqv (v "nValueReferences") (n 0)) (eqv (v "nValues") (n 0))) [ok],
       fail "No variables of this type exist"]
    else instancePrefix ++ [fail "FMI capability is not supported"]

def helpers : List CTree.Function := [
  ⟨⟨"fmi3Status", "fail", [⟨"Instance *", "m", false⟩, ⟨"const char *", "message", false⟩]⟩,
    [setMode .terminated, log "fmi3Error" (v "message"), ret (v "fmi3Error")], true⟩,
  ⟨⟨"double", "model_rhs", [⟨"const Model *", "model", false⟩]⟩, [ret (call "rumoca_rhs")], true⟩,
  ⟨⟨"void", "model_advance", [⟨"Model *", "model", false⟩, ⟨"uint64_t", "count", false⟩]⟩,
    [.assign (.field (v "model") "x" true) (call "rumoca_sample" [.field (v "model") "x" true, v "count"])], true⟩,
  Identity.function,
  CAtomicScan.function]

def declarationPrefix : String :=
  "/* FMI 3 ABI adapter generated in Lean. See documentation/index.html for the proof boundary. */\n" ++
  "#include <fmi3Functions.h>\n#include <math.h>\n#include <string.h>\n#include <stdint.h>\n#include <fenv.h>\n#include <stdatomic.h>\n\n" ++
  "_Static_assert(ATOMIC_BOOL_LOCK_FREE == 2, \"Always-lock-free atomic Boolean storage is required\");\n\n"

def declarations : String :=
  declarationPrefix ++ StaticStorage.render StaticStorage.deploymentCapacity ++ "\n"

def function (m : Solve.FMI3Model source) (sig : Signature) : CTree.Function :=
  ⟨sig, body m sig, false⟩

def render (m : Solve.FMI3Model source) (signatures : List Signature) : String :=
  functionPrefix m.name ++ "#include \"model.c\"\n" ++ declarations ++
    String.join (helpers.map CTree.Function.render) ++
    String.join (signatures.map fun sig => (function m sig).render)

end Rumoca.FMI3.Runtime

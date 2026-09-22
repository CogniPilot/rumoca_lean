import RumocaFMI3.BodyEmbedding
import RumocaFMI3.LiteralPreparation
import RumocaFMI3.ErrorCalls
import RumocaFMI3.RuntimePrinter

/-! Complete typed calls for the two scalar ME count queries. Successful and
null-instance calls are independent of logging; rejected lifecycle and missing
output paths use the ordinary failure helper with logging disabled. Literal
bindings, instance storage, header meanings and native ABI remain explicit. -/
noncomputable section
namespace Rumoca.FMI3.CountQueries
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

def outputName (events : Bool) : String :=
  if events then "nEventIndicators" else "nContinuousStates"

def count (events : Bool) : Nat := if events then 0 else 1

def signature (events : Bool) : Signature :=
  ⟨"fmi3Status", if events then "fmi3GetNumberOfEventIndicators" else "fmi3GetNumberOfContinuousStates",
    [⟨"fmi3Instance", "instance", false⟩, ⟨"size_t *", outputName events, false⟩]⟩

def rest (events : Bool) : List Stmt :=
  [Runtime.pointerCheck [outputName events],
    Runtime.out (outputName events) (Runtime.n (count events)), Runtime.ok]

omit static in
theorem body_eq (m : Solve.FMI3Model source) (events : Bool) :
    Runtime.body m (signature events) = Runtime.require .getCounts ++ rest events := by
  cases events <;> simp [Runtime.body, signature, rest, count, outputName]

def arguments (p buffer : Option Address) : List Value := [.pointer p, .pointer buffer]

def parameters (events : Bool) (p buffer : Option Address) : Locals :=
  CBody.bind (CBody.bind (fun _ => none) (outputName events) (.pointer buffer)) "instance" (.pointer p)

def written (events : Bool) (heap : Heap) (buffer : Address) : Heap :=
  replace heap buffer ⟨.size, true, some (.integer (count events))⟩

theorem parameters_bound (events : Bool) (p buffer : Option Address) :
    CCalls.parameters (signature events).parameters (arguments p buffer) =
      some (parameters events p buffer) := by
  cases events <;> rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem body_run (m : Solve.FMI3Model source) (events : Bool)
    (heap : Heap) (p buffer : Address) (kind : Kind) (mode : Mode) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getCounts kind mode)
    (storage : heap buffer = some ⟨.size, true, old⟩) :
    run 6 (.running (Runtime.body m (signature events)) (parameters events (some p) (some buffer)) heap) =
      some (.returned ⟨.integer 0, written events heap buffer⟩) := by
  let tail := rest events
  have accepted := LifecycleGuard.accept (parameters events (some p) (some buffer)) heap p .getCounts kind mode tail
    (by simp [parameters, CBody.bind])
    (by cases events <;> simp [parameters, CBody.bind, outputName]) hk hm allowed
  have body : Runtime.body m (signature events) = Runtime.require .getCounts ++ tail := by
    exact body_eq m events
  rw [body, show 6 = 3 + 3 from rfl, run_add, accepted]
  cases events <;>
    simp [tail, rest, Runtime.pointerCheck, Runtime.reject, Runtime.branch, Runtime.ret, Runtime.ok,
      Runtime.out, Runtime.any, Runtime.either, Runtime.negate, Runtime.v, Runtime.n,
      run, CBody.next, CBody.nextWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.lvalue, CBody.lvalueWith, parameters, CBody.bind, outputName, count, resolve, constants,
      CBody.cast, convert, boolean, Value.truth, Value.address, store, storage, written]

theorem call_reaches (m : Solve.FMI3Model source) (events : Bool) (program : CCalls.Program)
    (heap : Heap) (p buffer : Address) (kind : Kind) (mode : Mode) (old : Option Value)
    (stack : CCalls.Typed.Continuation)
    (defined : program.definitions (signature events).name =
      some (.tree (Runtime.function m (signature events))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getCounts kind mode)
    (storage : heap buffer = some ⟨.size, true, old⟩) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling (signature events).name (arguments (some p) (some buffer)) heap stack)
      (.returning (.integer 0) (written events heap buffer) stack) :=
  CBodyEmbedding.typed_call_reaches program (Runtime.function m (signature events))
    (arguments (some p) (some buffer)) (parameters events (some p) (some buffer)) heap _ (.integer 0) stack 6
    defined (parameters_bound events (some p) (some buffer)) (BodyEmbedding.body_closed m _)
    (body_run m events heap p buffer kind mode old hk hm allowed storage)
    (by simp [Runtime.function, signature, CCalls.returnCast, CBody.cast, convert])

theorem call_behaviors (m : Solve.FMI3Model source) (events : Bool) (program : CCalls.Program)
    (heap : Heap) (p buffer : Address) (kind : Kind) (mode : Mode) (old : Option Value)
    (defined : program.definitions (signature events).name =
      some (.tree (Runtime.function m (signature events))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getCounts kind mode)
    (storage : heap buffer = some ⟨.size, true, old⟩) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.calling (signature events).name (arguments (some p) (some buffer)) heap .done) behavior ↔
      behavior = .terminates ⟨.integer 0, written events heap buffer⟩ :=
  (CCalls.Typed.machine program).behavior_iff
    ((call_reaches m events program heap p buffer kind mode old .done defined hk hm allowed storage).trans
      (.next rfl (.refl _))) rfl

omit static in
theorem frame (events : Bool) (heap : Heap) (buffer q : Address) (different : q ≠ buffer) :
    written events heap buffer q = heap q := replace_other _ _ _ _ different

omit static in
theorem stored_count (events : Bool) (heap : Heap) (buffer : Address) :
    load (written events heap buffer) buffer = some (.integer (count events)) := by
  cases events <;> simp [written, load, convert, count]

theorem null_run (m : Solve.FMI3Model source) (events : Bool) (heap : Heap) (buffer : Option Address) :
    run 3 (.running (Runtime.body m (signature events)) (parameters events none buffer) heap) =
      some (.returned ⟨.integer 3, heap⟩) := by
  cases events <;>
    simp [Runtime.body, signature, Runtime.require, Runtime.instancePrefix, Runtime.branch,
      Runtime.ret, Runtime.negate, Runtime.v, parameters, outputName,
      run, CBody.next, CBody.nextWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.bind, resolve, constants, CBody.cast, convert, Value.truth, boolean]

theorem null_reaches (m : Solve.FMI3Model source) (events : Bool) (program : CCalls.Program)
    (heap : Heap) (buffer : Option Address) (stack : CCalls.Typed.Continuation)
    (defined : program.definitions (signature events).name =
      some (.tree (Runtime.function m (signature events)))) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling (signature events).name (arguments none buffer) heap stack)
      (.returning (.integer 3) heap stack) :=
  CBodyEmbedding.typed_call_reaches program (Runtime.function m (signature events))
    (arguments none buffer) (parameters events none buffer) heap _ (.integer 3) stack 3
    defined (parameters_bound events none buffer) (BodyEmbedding.body_closed m _)
    (null_run m events heap buffer)
    (by simp [Runtime.function, signature, CCalls.returnCast, CBody.cast, convert])

theorem null_behaviors (m : Solve.FMI3Model source) (events : Bool) (program : CCalls.Program)
    (heap : Heap) (buffer : Option Address)
    (defined : program.definitions (signature events).name =
      some (.tree (Runtime.function m (signature events)))) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.calling (signature events).name (arguments none buffer) heap .done) behavior ↔
      behavior = .terminates ⟨.integer 3, heap⟩ :=
  (CCalls.Typed.machine program).behavior_iff
    ((null_reaches m events program heap buffer .done defined).trans (.next rfl (.refl _))) rfl

omit static in
theorem continuous_count_matches_solve (m : Solve.FMI3Model source) :
    count false = m.problem.stateShape.volume := rfl

theorem rejected_reaches (m : Solve.FMI3Model source) (events : Bool) (program : CCalls.Program)
    (heap : Heap) (p message : Address) (buffer : Option Address) (kind : Kind) (mode : Mode)
    (logger : Option Address) (stack : CCalls.Typed.Continuation)
    (defined : program.definitions (signature events).name =
      some (.tree (Runtime.function m (signature events))))
    (helper : program.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "Call is not allowed in the current FMI state" = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (rejected : ¬ Reference.Allowed .getCounts kind mode) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling (signature events).name (arguments (some p) buffer) heap stack)
      (.returning (.integer 3) (LifecycleBodies.writeMode heap p .terminated) stack) := by
  let env := parameters events (some p) buffer
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have prefixed := LifecycleGuard.reject_prefix env heap p .getCounts kind mode (rest events)
    (by simp [env, parameters, CBody.bind])
    (by cases events <;> simp [env, parameters, CBody.bind, outputName]) hk modeLoaded rejected
  rw [← body_eq m events] at prefixed
  exact ErrorCalls.failure_after_prefix m (signature events) rfl program
    (arguments (some p) buffer) env (CBody.bind env "m" (.pointer (some p))) heap heap 3 p message
    "Call is not allowed in the current FMI state" (rest events) _ logger stack defined
    (parameters_bound events (some p) buffer) prefixed helper
    (by cases events <;> simp [env, parameters, CBody.bind, outputName])
    (by simp [CBody.bind, resolve]) literal hm hl hg

theorem rejected_behaviors (m : Solve.FMI3Model source) (events : Bool) (program : CCalls.Program)
    (heap : Heap) (p message : Address) (buffer : Option Address) (kind : Kind) (mode : Mode)
    (logger : Option Address)
    (defined : program.definitions (signature events).name =
      some (.tree (Runtime.function m (signature events))))
    (helper : program.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "Call is not allowed in the current FMI state" = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (rejected : ¬ Reference.Allowed .getCounts kind mode) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.calling (signature events).name (arguments (some p) buffer) heap .done) behavior ↔
      behavior = .terminates ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ :=
  (CCalls.Typed.machine program).behavior_iff
    ((rejected_reaches m events program heap p message buffer kind mode logger .done
      defined helper literal hk hm hl hg rejected).trans (.next rfl (.refl _))) rfl

theorem missing_run (m : Solve.FMI3Model source) (events : Bool) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getCounts kind mode) :
    run 4 (.running (Runtime.body m (signature events)) (parameters events (some p) none) heap) =
      some (.running [Runtime.fail "Missing output pointer",
        Runtime.out (outputName events) (Runtime.n (count events)), Runtime.ok]
        (CBody.bind (parameters events (some p) none) "m" (.pointer (some p))) heap) := by
  have accepted := LifecycleGuard.accept (parameters events (some p) none) heap p
    .getCounts kind mode (rest events) (by simp [parameters, CBody.bind])
    (by cases events <;> simp [parameters, CBody.bind, outputName]) hk hm allowed
  rw [body_eq, show 4 = 3 + 1 from rfl, run_add, accepted]
  cases events <;>
    simp [rest, Runtime.pointerCheck, Runtime.reject, Runtime.branch, Runtime.any,
      Runtime.either, Runtime.negate, Runtime.v, Runtime.n, parameters, outputName,
      run, CBody.next, CBody.nextWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.bind, resolve, constants, Value.truth, boolean]

theorem missing_reaches (m : Solve.FMI3Model source) (events : Bool) (program : CCalls.Program)
    (heap : Heap) (p message : Address) (kind : Kind) (mode : Mode) (logger : Option Address)
    (stack : CCalls.Typed.Continuation)
    (defined : program.definitions (signature events).name =
      some (.tree (Runtime.function m (signature events))))
    (helper : program.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "Missing output pointer" = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (allowed : Reference.Allowed .getCounts kind mode) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling (signature events).name (arguments (some p) none) heap stack)
      (.returning (.integer 3) (LifecycleBodies.writeMode heap p .terminated) stack) := by
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  exact ErrorCalls.failure_after_prefix m (signature events) rfl program
    (arguments (some p) none) (parameters events (some p) none)
    (CBody.bind (parameters events (some p) none) "m" (.pointer (some p))) heap heap 4 p message
    "Missing output pointer" [Runtime.out (outputName events) (Runtime.n (count events)), Runtime.ok]
    _ logger stack defined (parameters_bound events (some p) none)
    (missing_run m events heap p kind mode hk modeLoaded allowed) helper
    (by cases events <;> simp [parameters, CBody.bind, outputName])
    (by simp [CBody.bind, resolve]) literal hm hl hg

theorem missing_behaviors (m : Solve.FMI3Model source) (events : Bool) (program : CCalls.Program)
    (heap : Heap) (p message : Address) (kind : Kind) (mode : Mode) (logger : Option Address)
    (defined : program.definitions (signature events).name =
      some (.tree (Runtime.function m (signature events))))
    (helper : program.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "Missing output pointer" = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (allowed : Reference.Allowed .getCounts kind mode) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.calling (signature events).name (arguments (some p) none) heap .done) behavior ↔
      behavior = .terminates ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ :=
  (CCalls.Typed.machine program).behavior_iff
    ((missing_reaches m events program heap p message kind mode logger .done
      defined helper literal hk hm hl hg allowed).trans (.next rfl (.refl _))) rfl

omit static in
theorem function_tokenization (m : Solve.FMI3Model source) (events : Bool) :
    CTree.Printer.FunctionTokenization RuntimePrinter.typedefs
      (Runtime.function m (signature events)).render (Runtime.function m (signature events)) := by
  apply RuntimePrinter.function_tokenization
  have statusType : CTree.Syntax.TypeSpelling RuntimePrinter.typedefs "fmi3Status" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  have handleType : CTree.Syntax.TypeSpelling RuntimePrinter.typedefs "fmi3Instance" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  have sizeType : CTree.Syntax.TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  cases events <;> refine ⟨statusType, by decide +kernel, ?_⟩
  all_goals
    intro param member
    simp [signature] at member
    rcases member with rfl | rfl
    · exact ⟨handleType, by decide +kernel⟩
    · exact ⟨CTree.Syntax.TypeSpelling.pointer sizeType, by decide +kernel⟩


end Rumoca.FMI3.CountQueries

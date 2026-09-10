import RumocaC.LoopCalls

/-! Typed call execution for the authored C fragment. Actual tree bodies use
the tensor loop statement machine; ordinary calls also carry return values,
destinations and declared local types. The definition table may additionally
select the existing numerical statement machine. No function name denotes an
assumed tensor result. Pure argument expressions, direct calls and explicit
header bindings are required. Allocation, native ABI/linking and C-to-machine
compilation are outside this model. -/
noncomputable section
namespace Rumoca.CCalls.Typed
open CTree CMemory CLoops
variable [interface : CInterface]

inductive Continuation where
  | done
  | caller (destination : Destination) (rest : List Stmt) (locals : CBody.Locals)
      (types : Types) (resultType : String) (outer : Continuation)

inductive State where
  | body (state : CLoops.State) (resultType : String) (stack : Continuation)
  | calling (name : String) (args : List Value) (heap : Heap) (stack : Continuation)
  | kernel (state : CStatements.State) (heap : Heap) (stack : Continuation)
  | returning (value : Value) (heap : Heap) (stack : Continuation)
  | halted (result : CBody.Result)

def enterCall (s : CLoops.State) (resultType : String) (stack : Continuation) : Option State :=
  match s with
  | .running [] _ _ heap =>
      if resultType = "void" then some (.returning .void heap stack) else none
  | .running (stmt :: rest) env types heap => do
      let (destination, name, args) ← CCalls.callOperand stmt
      if (env name).isSome || name = "isfinite" then none else do
        let values ← CCalls.arguments env heap args
        return .calling name values heap (.caller destination rest env types resultType stack)
  | .returned _ => none

def resume (value : Value) (heap : Heap) : Continuation → Option State
  | .done => some (.halted ⟨value, heap⟩)
  | .caller destination rest env types resultType outer =>
    match destination with
    | .assign (.id name) => do
        let _ ← env name
        let type ← types name
        let converted ← convert type value
        return .body (.running rest (CBody.bind env name converted) types heap) resultType outer
    | .assign target => do
        let address ← CBody.lvalue env heap target
        let heap' ← store heap address value
        return .body (.running rest env types heap') resultType outer
    | .declare type name => do
        if (env name).isSome then none else do
          let declared ← interface.types type
          let converted ← convert declared value
          return .body (.running rest (CBody.bind env name converted) (bindType types name declared) heap)
            resultType outer
    | .discard => some (.body (.running rest env types heap) resultType outer)
    | .ret => do return .returning (← returnCast resultType value) heap outer

def next (p : Program) : State → Option State
  | .halted _ => none
  | .body (.returned r) resultType stack => do
      return .returning (← returnCast resultType r.value) r.heap stack
  | .body s resultType stack =>
      match CLoops.next s with
      | some t => some (.body t resultType stack)
      | none => enterCall s resultType stack
  | .calling name args heap stack => do
      match ← p.definitions name with
      | .tree fn =>
          let env ← parameters fn.signature.parameters args
          let types ← CLoops.Calls.parameterTypes fn.signature.parameters
          return .body (.running fn.body env types heap) fn.signature.result stack
      | .kernel fn => return .kernel (← kernelEntry fn args) heap stack
  | .kernel (.returned x) heap stack => some (.returning (.finite x) heap stack)
  | .kernel s heap stack => do return .kernel (← CStatements.next p.kernel s) heap stack
  | .returning value heap stack => resume value heap stack

def machine (p : Program) : Transition.Machine State CBody.Result where
  step s t := next p s = some t
  final | .halted result => some result | _ => none
  deterministic ha hb := Option.some.inj (ha.symm.trans hb)
  final_stuck := by intro s result hs t; cases s <;> simp_all [next]

end Rumoca.CCalls.Typed

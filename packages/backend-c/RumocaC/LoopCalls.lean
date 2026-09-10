import RumocaC.Loops

/-! Ordinary void calls around the typed loop machine. The definition table
selects a C function tree; arguments are evaluated and converted, the callee
gets a fresh parameter scope, and its actual statements execute before the
caller resumes. No function name stands for an assumed tensor operation.
Only discarded void calls are admitted here. General return values, indirect
calls, allocation and the native ABI remain outside this fragment. -/
noncomputable section
namespace Rumoca.CLoops.Calls
open CTree CMemory
variable [interface : CInterface]

abbrev Definitions := String → Option CTree.Function

theorem cast_of_type (name : String) (type : CType) (value converted : Value)
    (typed : interface.types name = some type) (cast : convert type value = some converted) :
    CBody.cast name value = some converted := by
  simp only [CBody.cast, typed, bind, Option.bind_some, cast]

theorem bind_parameter (p : Parameter) (ps : List Parameter) (value converted : Value)
    (vs : List Value) (env : CBody.Locals) (ordinary : p.array = false)
    (tailBound : CCalls.parameters ps vs = some env) (fresh : env p.name = none)
    (cast : CBody.cast p.type value = some converted) :
    CCalls.parameters (p :: ps) (value :: vs) = some (CBody.bind env p.name converted) := by
  simp only [CCalls.parameters, CCalls.parameterType, ordinary, Bool.false_eq_true, ↓reduceIte, tailBound,
    bind, Option.bind_some, fresh, Option.isSome_none, cast, pure]

def parameterTypes : List Parameter → Option Types
  | [] => some (fun _ => none)
  | p :: ps => do
      let rest ← parameterTypes ps
      if (rest p.name).isSome then none else do
        let type ← interface.types (CCalls.parameterType p)
        return bindType rest p.name type

inductive Continuation where
  | done
  | caller (rest : List Stmt) (locals : CBody.Locals) (types : Types) (outer : Continuation)

inductive State where
  | body (state : CLoops.State) (stack : Continuation)
  | calling (name : String) (args : List Value) (heap : Heap) (stack : Continuation)
  | returning (heap : Heap) (stack : Continuation)
  | halted (heap : Heap)

def enterCall (s : CLoops.State) (stack : Continuation) : Option State :=
  match s with
  | .running (.eval (.call (.id name) args) :: rest) env types heap => do
      if (env name).isSome || name = "isfinite" then none else do
        let values ← CCalls.arguments env heap args
        return .calling name values heap (.caller rest env types stack)
  | _ => none

def next (definitions : Definitions) : State → Option State
  | .halted _ => none
  | .body (.returned result) stack =>
      if result.value = .void then some (.returning result.heap stack) else none
  | .body state stack =>
      match CLoops.next state with
      | some following => some (.body following stack)
      | none => enterCall state stack
  | .calling name args heap stack => do
      let fn ← definitions name
      if fn.signature.result ≠ "void" then none else do
        let locals ← CCalls.parameters fn.signature.parameters args
        let types ← parameterTypes fn.signature.parameters
        return .body (.running fn.body locals types heap) stack
  | .returning heap .done => some (.halted heap)
  | .returning heap (.caller rest locals types outer) =>
      some (.body (.running rest locals types heap) outer)

def machine (definitions : Definitions) : Transition.Machine State Heap where
  step s t := next definitions s = some t
  final | .halted heap => some heap | _ => none
  deterministic ha hb := Option.some.inj (ha.symm.trans hb)
  final_stuck := by intro s heap hs t; cases s <;> simp_all [next]

theorem body_step (definitions : Definitions) (h : CLoops.next s = some t) (stack) :
    next definitions (.body s stack) = some (.body t stack) := by
  cases s with
  | returned => simp [CLoops.next] at h
  | running => simp [next, h]

theorem body_reaches (definitions : Definitions)
    (h : Transition.Reaches CLoops.machine.step s t) (stack) :
    Transition.Reaches (machine definitions).step (.body s stack) (.body t stack) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact .next (body_step definitions hs stack) ih

/-- Enter and execute a selected function, reaching an ordinary return with
the same continuation. Parameter conversion and body execution are explicit. -/
theorem call_reaches (definitions : Definitions) (name : String) (args : List Value)
    (heap finalHeap : Heap) (fn : CTree.Function) (locals : CBody.Locals) (types : Types)
    (stack : Continuation) (found : definitions name = some fn)
    (returnsVoid : fn.signature.result = "void")
    (bound : CCalls.parameters fn.signature.parameters args = some locals)
    (typed : parameterTypes fn.signature.parameters = some types)
    (executed : Transition.Reaches CLoops.machine.step
      (.running fn.body locals types heap) (.returned ⟨.void, finalHeap⟩)) :
    Transition.Reaches (machine definitions).step (.calling name args heap stack)
      (.returning finalHeap stack) := by
  refine .next (t := .body (.running fn.body locals types heap) stack)
    (by simp [machine, next, found, returnsVoid, bound, typed]) ?_
  exact (body_reaches definitions executed stack).trans (.next (by simp [machine, next]) (.refl _))

theorem call_behaviors (definitions : Definitions) (name : String) (args : List Value)
    (heap finalHeap : Heap) (fn : CTree.Function) (locals : CBody.Locals) (types : Types)
    (found : definitions name = some fn) (returnsVoid : fn.signature.result = "void")
    (bound : CCalls.parameters fn.signature.parameters args = some locals)
    (typed : parameterTypes fn.signature.parameters = some types)
    (executed : Transition.Reaches CLoops.machine.step
      (.running fn.body locals types heap) (.returned ⟨.void, finalHeap⟩)) (behavior) :
    (machine definitions).Behaves (.calling name args heap .done) behavior ↔
      behavior = .terminates finalHeap := by
  have ran := call_reaches definitions name args heap finalHeap fn locals types .done
    found returnsVoid bound typed executed
  exact (machine definitions).behavior_iff (ran.trans (.next rfl (.refl _))) rfl

/-- A helper call resumes the exact saved locals and types, carrying only its
heap effects into the remaining caller statements. -/
theorem resume_caller (definitions : Definitions) (heap : Heap) (rest : List Stmt)
    (locals : CBody.Locals) (types : Types) (outer : Continuation) :
    next definitions (.returning heap (.caller rest locals types outer)) =
      some (.body (.running rest locals types heap) outer) := rfl

end Rumoca.CLoops.Calls

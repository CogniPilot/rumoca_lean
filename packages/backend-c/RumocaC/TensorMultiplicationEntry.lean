import RumocaC.TensorMultiplicationTotal
import RumocaC.TensorProgramCalls
import RumocaC.ContextCallResult

/-! Total finite-input execution of a prepared single-product Solve entry.
The proof is parameterized by the indexed register references, storage plan,
parameter list and actual emitted function. Overflow is an encoded result,
not a finite execution premise. No source names or solver policy are resolved.
This is the reusable call/lowering bridge needed before a caller can scan the
result of the square RHS and implement its own failure protocol. -/
noncomputable section
namespace Rumoca.CTensor.MultiplicationTotal
open CTree CMemory CMemory.TensorView Solve.Tensor Lowering
variable [interface : CInterface]

theorem invoke_reaches (definitions : CLoops.Calls.Definitions)
    (a b : Values shape) (heap : Heap) (left right output : Address)
    (argsLeft argsRight argsOutput argsCount : Expr) (env : CBody.Locals) (types : CLoops.Types)
    (rest : List Stmt) (stack : CLoops.Calls.Continuation)
    (found : definitions (function .mul).signature.name = some (function .mul))
    (header : HeaderTypes interface) (unshadowed : env (function .mul).signature.name = none)
    (hl : CBody.eval env heap argsLeft = some (.pointer (some left)))
    (hr : CBody.eval env heap argsRight = some (.pointer (some right)))
    (ho : CBody.eval env heap argsOutput = some (.pointer (some output)))
    (hc : CBody.eval env heap argsCount = some (.integer shape.volume))
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (write_output : Writable heap output shape.volume)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running (invoke .mul argsLeft argsRight argsOutput argsCount :: rest) env types heap) stack)
      (.body (.running rest env types (EncodedTensor.written heap output (result a b) shape.volume)) stack) := by
  refine .next (CTensor.invoke_step definitions .mul argsLeft argsRight argsOutput argsCount
    left right output shape.volume env types heap rest stack unshadowed hl hr ho hc) ?_
  exact (helper_call_reaches definitions a b heap left right output _ found header read_left read_right
    write_output separate_left separate_right bounded).trans (.next rfl (.refl _))

/-- Both operands and the destination retain their tensor shape in the plan.
Parameter validity and the ordinary lowering match justify the entire wrapper;
the numerical helper runs, rather than being replaced by a result assumption. -/
theorem entry_reaches (left right : Ref Γ shape) (destination : Buffer shape) (layout : Layout Γ)
    (f : Syntax.Function) (valid : f.valid = true)
    (matched : Syntax.Matches f (.binary .mul left right (.ret .here)) (destination, ()) layout)
    (definitions : CLoops.Calls.Definitions) (header : HeaderTypes interface)
    (helper : definitions (function .mul).signature.name = some (function .mul))
    (found : definitions f.name = some f.tree) (args : Arguments.Values)
    (arguments : Arguments.Valid f.parameters args) (locations : Locations)
    (values : Env Binary64.Value Γ) (heap : Heap)
    (bound : LayoutBound (Arguments.locals f.parameters args) locations layout)
    (represented : Represents locations layout heap values)
    (ready : Ready (Arguments.locals f.parameters args) locations
      (.binary .mul left right (.ret .here)) (destination, ()) layout heap)
    (stack : CLoops.Calls.Continuation) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling f.name (Arguments.values f.parameters args) heap stack)
      (.returning (EncodedTensor.written heap (locations destination)
        (result (values left) (values right)) shape.volume) stack) := by
  have nodup := valid_nodup f valid
  have parameters := Arguments.bind_parameters f.parameters args header nodup arguments
  have types := Arguments.bind_types f.parameters header nodup
  have entered : (CLoops.Calls.machine definitions).step
      (.calling f.name (Arguments.values f.parameters args) heap stack)
      (.body (.running f.tree.body (Arguments.locals f.parameters args) (Arguments.types f.parameters) heap) stack) := by
    simp only [CLoops.Calls.machine, CLoops.Calls.machineWith, CLoops.Calls.nextWith, found,
      Syntax.Function.tree, ne_eq, not_true_eq_false, ↓reduceIte, parameters, types,
      bind, Option.bind_some, pure]
  rcases ready with ⟨writable, bounded, outputBound, fresh, _⟩
  have unshadowed : Arguments.locals f.parameters args (function .mul).signature.name = none :=
    Arguments.locals_absent _ _ _ (helper_absent f valid _ (by decide))
  have ran := invoke_reaches definitions (values left) (values right) heap
    (locations (layout left)) (locations (layout right)) (locations destination)
    (layout left).pointer (layout right).pointer destination.pointer destination.count
    (Arguments.locals f.parameters args) (Arguments.types f.parameters) [.ret none] stack
    helper header unshadowed (bound left heap).1 (bound right heap).1
    (outputBound heap).1 (outputBound heap).2 (represented left) (represented right)
    writable (fresh left) (fresh right) bounded
  change f.tree.body = (emit (.binary .mul left right (.ret .here)) (destination, ()) layout).code ++
    [.ret none] at matched
  simp only [emit, List.nil_append, List.cons_append] at matched
  rw [matched] at entered
  exact .next entered (ran.trans (.next rfl (.next rfl (.refl _))))

theorem entry_correct (left right : Ref Γ shape) (destination : Buffer shape) (layout : Layout Γ)
    (f : Syntax.Function) (valid : f.valid = true)
    (matched : Syntax.Matches f (.binary .mul left right (.ret .here)) (destination, ()) layout)
    (definitions : CLoops.Calls.Definitions) (header : HeaderTypes interface)
    (helper : definitions (function .mul).signature.name = some (function .mul))
    (found : definitions f.name = some f.tree) (args : Arguments.Values)
    (arguments : Arguments.Valid f.parameters args) (locations : Locations)
    (values : Env Binary64.Value Γ) (heap : Heap)
    (bound : LayoutBound (Arguments.locals f.parameters args) locations layout)
    (represented : Represents locations layout heap values)
    (ready : Ready (Arguments.locals f.parameters args) locations
      (.binary .mul left right (.ret .here)) (destination, ()) layout heap) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling f.name (Arguments.values f.parameters args) heap .done) behavior ↔
    behavior = .terminates (EncodedTensor.written heap (locations destination)
      (result (values left) (values right)) shape.volume) := by
  have ran := entry_reaches left right destination layout f valid matched definitions header helper
    found args arguments locations values heap bound represented ready .done
  exact (CLoops.Calls.machine definitions).behavior_iff (ran.trans (.next rfl (.refl _))) rfl

/-- The same computation in the canonical C scheduler, with arbitrary declared
objects and saved callers. Header, function-table and storage premises remain
explicit. The exact final heap is shared with the encoded-output theorem. -/
theorem entry_context (left right : Ref Γ shape) (destination : Buffer shape) (layout : Layout Γ)
    (f : Syntax.Function) (valid : f.valid = true)
    (matched : Syntax.Matches f (.binary .mul left right (.ret .here)) (destination, ()) layout)
    (definitions : CLoops.Calls.Definitions) (header : HeaderTypes interface)
    (helper : definitions (function .mul).signature.name = some (function .mul))
    (found : definitions f.name = some f.tree) (args : Arguments.Values)
    (arguments : Arguments.Valid f.parameters args) (locations : Locations)
    (values : Env Binary64.Value Γ) (heap : Heap)
    (bound : LayoutBound (Arguments.locals f.parameters args) locations layout)
    (represented : Represents locations layout heap values)
    (ready : Ready (Arguments.locals f.parameters args) locations
      (.binary .mul left right (.ret .here)) (destination, ()) layout heap)
    (declarations : CDeclaredMembers.Declarations) (objects : CDeclaredMembers.Objects)
    (p : CCalls.Program) (linked : CCalls.Typed.Extends definitions p)
    (free : CContextMachine.FieldFree.DefinitionsFree definitions) :
    CContextMachine.CallResult (CContextMachine.declared declarations objects) p f.name
      (Arguments.values f.parameters args) heap
      (EncodedTensor.written heap (locations destination) (result (values left) (values right)) shape.volume) := by
  apply CContextMachine.loop_call_result_context declarations objects p definitions linked free
  exact (entry_correct left right destination layout f valid matched definitions header helper
    found args arguments locations values heap bound represented ready _).2 rfl

end Rumoca.CTensor.MultiplicationTotal

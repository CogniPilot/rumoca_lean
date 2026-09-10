import RumocaFMI3.BodyEmbedding
import RumocaFMI3.StateProofs

/-! Complete ME continuous-state calls for the emitted function trees. Array
parameter adjustment, fresh locals, typed body execution and return conversion
are derived, rather than assumed at body entry. The signatures match the pinned
FMI headers; the definition-table binding, valid storage and lifecycle state
remain explicit. Header parsing, printed adapter bytes and native ABI/linkage
are separate obligations. -/
noncomputable section
namespace Rumoca.FMI3.StateCalls
private local instance targetInterface : CInterface := cInterface
open CTree CMemory

/-- The two declarations in fmi3FunctionTypes.h use unsized array parameters.
The setter retains its pointee's const qualifier in the adjusted spelling. -/
def signature (write : Bool) : Signature :=
  ⟨"fmi3Status", if write then "fmi3SetContinuousStates" else "fmi3GetContinuousStates",
    [⟨"fmi3Instance", "instance", false⟩,
     ⟨if write then "const fmi3Float64" else "fmi3Float64", "continuousStates", true⟩,
     ⟨"size_t", "nContinuousStates", false⟩]⟩

def arguments (p buffer : Address) : List Value :=
  [.pointer (some p), .pointer (some buffer), .integer 1]

theorem parameters_bound (write : Bool) (p buffer : Address) :
    CCalls.parameters (signature write).parameters (arguments p buffer) =
      some (StateProofs.parameters p buffer) := by
  cases write <;> rfl

/-- Enter the actual runtime constructor, retaining an arbitrary saved caller.
The body-run premise is discharged separately by the existing state semantics. -/
theorem call_reaches (m : Solve.FMI3Model source) (write : Bool) (program : CCalls.Program)
    (p buffer : Address) (heap : Heap) (result : CBody.Result) (n : Nat)
    (stack : CCalls.Typed.Continuation)
    (defined : program.definitions (signature write).name =
      some (.tree (Runtime.function m (signature write))))
    (executed : CBody.run n (.running (Runtime.body m (signature write))
      (StateProofs.parameters p buffer) heap) = some (.returned result))
    (cast : CCalls.returnCast "fmi3Status" result.value = some result.value) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling (signature write).name (arguments p buffer) heap stack)
      (.returning result.value result.heap stack) :=
  CBodyEmbedding.typed_call_reaches program (Runtime.function m (signature write))
    (arguments p buffer) (StateProofs.parameters p buffer) heap result result.value stack n
    defined (parameters_bound write p buffer) (BodyEmbedding.body_closed m _) executed cast

theorem get_reaches (m : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (p buffer : Address) (mode : Mode) (state : ModelExchange.State)
    (old : Option Value) (stack : CCalls.Typed.Continuation)
    (defined : program.definitions "fmi3GetContinuousStates" =
      some (.tree (Runtime.function m (signature false))))
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getStates .me mode)
    (hx : StateProofs.Represents heap p state)
    (ho : heap buffer = some ⟨.float64, true, old⟩) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling "fmi3GetContinuousStates" (arguments p buffer) heap stack)
      (.returning (.integer 0)
        (StateProofs.written heap buffer (Binary64.toBits (ModelExchange.getContinuousState state)).val)
        stack) :=
  call_reaches m false program p buffer heap _ 6 stack defined
    (StateProofs.get_run m _ rfl heap p buffer mode state.x old hk hm allowed hx ho)
    (by simp [CCalls.returnCast, CBody.cast, convert])

/-- Every getter call returns the Solve ME state exactly, including its
binary64 representation. Its only heap change is the caller's output cell. -/
theorem get_behaviors (m : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (p buffer : Address) (mode : Mode) (state : ModelExchange.State)
    (old : Option Value)
    (defined : program.definitions "fmi3GetContinuousStates" =
      some (.tree (Runtime.function m (signature false))))
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getStates .me mode)
    (hx : StateProofs.Represents heap p state)
    (ho : heap buffer = some ⟨.float64, true, old⟩) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.calling "fmi3GetContinuousStates" (arguments p buffer) heap .done) behavior ↔
      behavior = .terminates ⟨.integer 0,
        StateProofs.written heap buffer (Binary64.toBits (ModelExchange.getContinuousState state)).val⟩ :=
  (CCalls.Typed.machine program).behavior_iff
    ((get_reaches m program heap p buffer mode state old .done defined hk hm allowed hx ho).trans
      (.next rfl (.refl _))) rfl

theorem set_reaches (m : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (p buffer : Address) (state : ModelExchange.State) (x : Binary64.Value)
    (stack : CCalls.Typed.Continuation)
    (defined : program.definitions "fmi3SetContinuousStates" =
      some (.tree (Runtime.function m (signature true))))
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (hi : load heap buffer = some (.finite x))
    (hs : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite state.x)⟩) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling "fmi3SetContinuousStates" (arguments p buffer) heap stack)
      (.returning (.integer 0)
        (StateProofs.written heap (StateProofs.stateAddress p)
          (Binary64.toBits (ModelExchange.setContinuousState state x).x).val) stack) :=
  call_reaches m true program p buffer heap _ 7 stack defined
    (StateProofs.set_run m _ rfl heap p buffer x _ hk hm hi hs)
    (by simp [CCalls.returnCast, CBody.cast, convert])

/-- Every setter call implements the Solve ME update, preserving the input
bits and every heap cell outside the model's continuous state. -/
theorem set_behaviors (m : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (p buffer : Address) (state : ModelExchange.State) (x : Binary64.Value)
    (defined : program.definitions "fmi3SetContinuousStates" =
      some (.tree (Runtime.function m (signature true))))
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (hi : load heap buffer = some (.finite x))
    (hs : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite state.x)⟩) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.calling "fmi3SetContinuousStates" (arguments p buffer) heap .done) behavior ↔
      behavior = .terminates ⟨.integer 0, StateProofs.written heap (StateProofs.stateAddress p)
        (Binary64.toBits (ModelExchange.setContinuousState state x).x).val⟩ :=
  (CCalls.Typed.machine program).behavior_iff
    ((set_reaches m program heap p buffer state x .done defined hk hm hi hs).trans
      (.next rfl (.refl _))) rfl

end Rumoca.FMI3.StateCalls

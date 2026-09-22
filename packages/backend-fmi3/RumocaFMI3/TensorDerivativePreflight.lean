import RumocaC.TensorProductPreflightInline
import RumocaC.TensorProductPreflightContract
import RumocaFMI3.DiscardCode
import RumocaFMI3.TensorInstanceStorage
import RumocaFMI3.CInterface
import RumocaC.CallEvents

/-! State-preserving numerical admission for the prepared square derivative.
The shared product loop runs inline, so the public caller needs no additional
helper lookup. The FMI policy branches to Discard before any instance/output
write. Logging effects are proved separately, not treated as heap-preserving. -/
noncomputable section
namespace Rumoca.FMI3.TensorDerivativePreflight
open CTree CMemory CBody CLoops CMemory.TensorView
open CTensor TensorInstance
set_option maxRecDepth 10000

def message := "Non-finite continuous state derivative"

def code : List Stmt := ProductPreflight.Inline.code "int"
  (Runtime.region inputName) (Runtime.region inputName) (Runtime.v "nContinuousStates")

def reject : Stmt := .branch (.bin .eq (.id "valid") (.nat 0)) (Discard.body message) []

def body : List Stmt := code ++ [reject]

def finalEnv (env : Locals) (p : Address) (input : Values shape) : Locals :=
  ProductPreflight.Inline.finalEnv env (some (p.member inputName)) (some (p.member inputName)) input input

def finalTypes := ProductPreflight.Inline.finalTypes

variable [static : StaticLiterals]
private local instance : CInterface := cInterface static.addresses

theorem code_reaches (env : Locals) (prior : Types) (heap : Heap) (p : Address)
    (input : Values shape) (rest : List Stmt)
    (instanceValue : env "m" = some (.pointer (some p)))
    (count : env "nContinuousStates" = some (.integer shape.volume))
    (fresh : ProductPreflight.Inline.Fresh env) (readable : Reads heap (p.member inputName) input)
    (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches CLoops.machine.step
      (.running (code ++ rest) env prior heap)
      (.running rest (finalEnv env p input) (finalTypes prior) heap) := by
  have readBits : FiniteScan.Readable heap (some (p.member inputName))
      (EncodedTensor.finiteBits input) := by
    intro i
    refine ⟨p.member inputName, rfl, ?_⟩
    simpa only [Fin.getElem_fin, EncodedTensor.finiteBits_get] using readable i
  apply ProductPreflight.Inline.code_reaches "int"
    (Runtime.region inputName) (Runtime.region inputName) (Runtime.v "nContinuousStates")
    input input heap (some (p.member inputName)) (some (p.member inputName)) env prior rest fresh
    ?_ ?_ ?_ readBits readBits bounded rfl rfl rfl rfl
  all_goals
    simp [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith,
      Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.resolve, CBody.bind,
      CBody.lvalueWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt,
      CDeclaredMembers.fieldAt, Value.address, instanceValue, count]

omit static in
theorem classified (env : Locals) (p : Address) (input : Values shape) :
    finalEnv env p input "valid" =
      some (boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input))) :=
  ProductPreflight.Inline.final_flag _ _ _ _ _

theorem pass (env : Locals) (prior : Types) (heap : Heap) (p : Address)
    (input : Values shape) (rest : List Stmt)
    (instanceValue : env "m" = some (.pointer (some p)))
    (count : env "nContinuousStates" = some (.integer shape.volume))
    (fresh : ProductPreflight.Inline.Fresh env) (readable : Reads heap (p.member inputName) input)
    (bounded : shape.volume < 2 ^ 64)
    (finite : Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = true) :
    Transition.Reaches CLoops.machine.step
      (.running (body ++ rest) env prior heap)
      (.running rest (finalEnv env p input) (finalTypes prior) heap) := by
  have ran := code_reaches env prior heap p input (reject :: rest) instanceValue count fresh readable bounded
  refine ran.trans (.next ?_ (.refl _))
  change CLoops.next _ = some _
  simp [reject, CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
    CLoops.noDeclarations, Discard.body, Runtime.log, Runtime.branch, Runtime.ret,
    CBody.eval, CBody.evalWith, CBody.resolve, CBody.comparison, classified, finite, boolean, Value.truth]

theorem failure (env : Locals) (prior : Types) (heap : Heap) (p : Address)
    (input : Values shape) (rest : List Stmt)
    (instanceValue : env "m" = some (.pointer (some p)))
    (count : env "nContinuousStates" = some (.integer shape.volume))
    (fresh : ProductPreflight.Inline.Fresh env) (readable : Reads heap (p.member inputName) input)
    (bounded : shape.volume < 2 ^ 64)
    (nonfinite : Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = false) :
    Transition.Reaches CLoops.machine.step
      (.running (body ++ rest) env prior heap)
      (.running (Discard.body message ++ rest) (finalEnv env p input) (finalTypes prior) heap) := by
  have ran := code_reaches env prior heap p input (reject :: rest) instanceValue count fresh readable bounded
  refine ran.trans (.next ?_ (.refl _))
  change CLoops.next _ = some _
  simp [reject, CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
    CLoops.noDeclarations, Discard.body, Runtime.log, Runtime.branch, Runtime.ret,
    CBody.eval, CBody.evalWith, CBody.resolve, CBody.comparison, classified, nonfinite, boolean, Value.truth]

end Rumoca.FMI3.TensorDerivativePreflight

import RumocaEFMI.CInterface
import RumocaEFMI.Metadata
import RumocaEFMI.ProductionProofs
import GALECParser.Syntax

open _root_.Parser

noncomputable section
namespace Rumoca.EFMI.Metadata
private local instance targetInterface : CInterface := cInterface
open CMemory

def Variable.value (var : Variable) (state : GALEC.UnitProfile.State α) :
    Tensor.Value α var.shape :=
  match var with
  | .state => state.x
  | .clock => state.samplePeriod

def Variable.scalarValue (var : Variable) (state : GALEC.UnitProfile.State α) : α :=
  (var.value state)[0]'(by change 0 < 1; decide)

/-- Logical variable names describe the actual emitted GALEC declarations. -/
theorem algorithm_variables :
    Variable.state.name = GALEC.Syntax.unit.state ∧
    Variable.clock.name = GALEC.Syntax.unit.clock := ⟨rfl, rfl⟩

theorem fields_declared (var : Variable) :
    ⟨var.name, var.scalar⟩ ∈ CHeader.stateFields := by
  cases var <;> simp [Variable.name, Variable.scalar, CHeader.stateFields]

theorem types_declared (var : Variable) :
    CHeader.scalarNamed var.scalar.alias CHeader.declarations = some var.scalar :=
  CHeader.real_alias

theorem references_unique :
    (([CHeader.Scalar.real64, .status32].flatMap fun scalar =>
        [targetTypeId scalar, scalarTypeId scalar]) ++ [modelTypeId] ++
      variables.flatMap (fun var => [var.id, var.componentId]) ++
      methods.flatMap (fun method =>
        [algorithmMethodId method, functionId method, parameterId method, returnId method])).Nodup := by
  decide +kernel

/-- Mappings name an actual exported C function and its declared instance
formal, with a status type backed by a real typedef. -/
def FunctionsCorrect (module : Production.Module) : Prop := ∀ method,
  let description := functionDescription module method
  (module.method method).static = false ∧
  (module.method method).signature.name = "UnitIntegrator_" ++ algorithmMethodName method ∧
  (module.method method).signature.result = CHeader.Scalar.status32.alias ∧
  (module.method method).signature.parameters = [⟨"Model *", description.parameterName, false⟩] ∧
  description.returnTypeId = scalarTypeId .status32 ∧
  description.parameterTypeId = modelTypeId ∧ description.pointer = true

theorem functions_correct (model : Solve.Algorithm.Model source) (module : Production.Module)
    (lowered : Production.lower model = .ok module) : FunctionsCorrect module := by
  have eq := (Production.lower_is_unit model).symm.trans lowered
  cases Except.ok.inj eq
  intro method
  cases method <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reading through the manifest's actual parameter/component reference
observes precisely the corresponding logical tensor, for either variable. -/
theorem read_correct (module : Production.Module) (method : GALEC.Method) (var : Variable)
    (heap : Heap) (p : Address) (state : GALEC.UnitProfile.State Binary64.Value)
    (represents : Production.Represents heap p state) :
    CBody.eval (Production.parameters p) heap (referenceExpression module method var) =
      some (.finite (var.scalarValue state)) := by
  have lx : load heap (p.member "x") = some (.finite state.x[0]) := by
    simp [load, represents.1, convert, Value.finite]
  have lp : load heap (p.member "samplePeriod") = some (.finite state.samplePeriod[0]) := by
    simp [load, represents.2, convert, Value.finite]
  cases var <;> simp [referenceExpression, functionDescription, dataReference,
    Variable.name, Variable.value, Variable.scalarValue, CBody.eval,
    CBody.resolve, CBody.bind, Production.parameters, Value.address, lx, lp] <;> rfl

/-- After every method, every mapped variable observes its exact Solve value.
The theorem quantifies over all finite states and both mapped tensors. -/
theorem execution_preserves (model : Solve.Algorithm.Model source) (module : Production.Module)
    (lowered : Production.lower model = .ok module)
    (method : GALEC.Method) (var : Variable) (heap : Heap) (p : Address)
    (state : GALEC.UnitProfile.State Binary64.Value) (represents : Production.Represents heap p state)
    (result : CBody.Result)
    (executed : CArithmetic.machine.Behaves
      (.running (module.method method).body (Production.parameters p) heap) (.terminates result)) :
    result.value = .integer 0 ∧
    CBody.eval (Production.parameters p) result.heap (referenceExpression module method var) =
        some (.finite (var.scalarValue
          (GALEC.UnitProfile.solveExecute model.block Binary64.positiveZero Binary64.one
            GALEC.roundedAdd method state))) := by
  have eq := (Production.method_correct model module lowered method heap p state represents).1 _ |>.mp executed
  injection eq with resultEq
  cases resultEq
  exact ⟨rfl, read_correct module method var _ p _
    (Production.result_represents model method heap p state represents)⟩

/-- Target half of the logical-data mapping contract. Actual XML binding and
foreign-manifest origin/checksum correlation must be added by the archive layer. -/
structure Contract (model : Solve.Algorithm.Model source) (module : Production.Module) : Prop where
  functions : FunctionsCorrect module
  fields : ∀ var : Variable, ⟨var.name, var.scalar⟩ ∈ CHeader.stateFields
  types : ∀ var : Variable, CHeader.scalarNamed var.scalar.alias CHeader.declarations = some var.scalar
  executions : ∀ method var heap p (state : GALEC.UnitProfile.State Binary64.Value),
    Production.Represents heap p state → ∀ result : CBody.Result,
    CArithmetic.machine.Behaves
      (.running (module.method method).body (Production.parameters p) heap) (.terminates result) →
    result.value = .integer 0 ∧
    CBody.eval (Production.parameters p) result.heap (referenceExpression module method var) =
      some (.finite (var.scalarValue
        (GALEC.UnitProfile.solveExecute model.block Binary64.positiveZero Binary64.one
          GALEC.roundedAdd method state)))

theorem correct (model : Solve.Algorithm.Model source) (module : Production.Module)
    (lowered : Production.lower model = .ok module) : Contract model module :=
  ⟨functions_correct model module lowered, fields_declared, types_declared,
    execution_preserves model module lowered⟩

end Rumoca.EFMI.Metadata

import RumocaEFMI.ManifestProofs

/-! eFMI Beta 1 §§3.1.4, 3.2.5 §1.6 and 5.1.5: the Algorithm Code error
anchor identifies a per-instance, 32-bit Production C observation. The unit
profile has no exposed errors; both the method result and mapped field are
zero. This contract checks the decoded reference, not just XML construction. -/
noncomputable section
namespace Rumoca.EFMI.Manifest
private local instance targetInterface : CInterface := cInterface
open Metadata XML CMemory

/-- Select by the foreign anchor and the actual function's formal identifier.
Requiring a singleton rules out missing and competing status mappings. -/
def statusReferences (root : Element) (anchor formal : String) : List DataReference :=
  ((dataNodes root).filterMap decodeData).filter fun reference =>
    reference.foreignVariableId == anchor && reference.formalParameterId == formal

def MappedStatus (module : Production.Module) (algorithmRoot productionRoot : Element)
    (method : GALEC.Method) (p : Address) (result : CBody.Result) : Prop :=
  ∃ anchor anchorId fn f mapping model component,
    only (select algorithmRoot ["ErrorSignalStatus"]) = some anchor ∧
    anchor.attributes.lookup "id" = some anchorId ∧
    fn ∈ functionNodes productionRoot ∧ decodeFunction fn = some f ∧
    f.name = (module.method method).signature.name ∧
    f.returnTypeId = scalarTypeId .status32 ∧
    statusReferences productionRoot anchorId f.parameterId = [mapping] ∧
    mapping.foreignVariableId = anchorId ∧ mapping.formalParameterId = f.parameterId ∧
    model ∈ select productionRoot ["CodeContainer", "CodeFiles", "CodeFile", "Typedefs", "Typedef"] ∧
    model.attributes.lookup "id" = some f.parameterTypeId ∧
    component ∈ select model ["Components", "Component"] ∧
    component.attributes.lookup "name" = some mapping.componentIdentifier ∧
    component.attributes.lookup "typeDefRefId" = some (scalarTypeId .status32) ∧
    CBody.eval (Production.parameters p) result.heap (mappedExpression f mapping) = some result.value ∧
    result.value = .integer 0

theorem decode_statusMapping (method : GALEC.Method) :
    decodeData (statusMapping method) = some (statusReference method) := by
  cases method <;> rfl

theorem status_unique (modelName : String) (identity : Identity) (algorithmXML : String)
    (module : Production.Module) (method : GALEC.Method) :
    statusReferences (production modelName identity algorithmXML module) errorSignalId
      (functionDescription module method).parameterId = [statusReference method] := by
  cases method <;> rfl

theorem mapped_status_of_result (module : Production.Module) (modelName : String) (identity : Identity)
    (algorithmSource algorithmXML : String) (method : GALEC.Method) (p : Address) (result : CBody.Result)
    (status : load result.heap (p.member CHeader.statusName) = some result.value)
    (success : result.value = .integer 0) :
    MappedStatus module (algorithm modelName identity algorithmSource)
      (production modelName identity algorithmXML module) method p result := by
  refine ⟨node "ErrorSignalStatus" [("id", errorSignalId)], errorSignalId,
    function module method, functionDescription module method, statusReference method,
    modelType, statusComponent, rfl, rfl, function_present _ _ _ _ _,
    decode_function _ _, rfl, rfl, status_unique _ _ _ _ _, rfl, rfl, ?_, rfl, ?_, rfl, rfl, ?_, success⟩
  · simp [select, production, node, codeFile, scalarType, modelType]
  · simp [select, modelType, node, statusComponent]
  · simpa [mappedExpression, functionDescription, statusReference, CBody.eval, CBody.resolve,
      CBody.bind, Production.parameters, Value.address] using status

theorem mapped_status (model : Solve.Algorithm.Model source) (module : Production.Module)
    (lowered : Production.lower model = .ok module) (modelName : String) (identity : Identity)
    (algorithmSource algorithmXML : String) (method : GALEC.Method) (heap : Heap) (p : Address)
    (state : GALEC.UnitProfile.State Binary64.Value) (represents : Production.Represents heap p state)
    (result : CBody.Result)
    (executed : CArithmetic.machine.Behaves
      (.running (module.method method).body (Production.parameters p) heap) (.terminates result)) :
    MappedStatus module (algorithm modelName identity algorithmSource)
      (production modelName identity algorithmXML module) method p result := by
  have eq := (Production.method_correct model module lowered method heap p state represents).1 _ |>.mp executed
  injection eq with resultEq
  cases resultEq
  exact mapped_status_of_result _ _ _ _ _ _ _ _ (Production.result_status heap p state method) rfl

/-- Startup's XML status observation also holds for uninitialized storage. -/
theorem mapped_startup_status (model : Solve.Algorithm.Model source) (module : Production.Module)
    (lowered : Production.lower model = .ok module) (modelName : String) (identity : Identity)
    (algorithmSource algorithmXML : String) (heap : Heap) (p : Address) (oldX oldPeriod : Option Value)
    (hx : heap (p.member "x") = some ⟨.float64, true, oldX⟩)
    (hp : heap (p.member "samplePeriod") = some ⟨.float64, true, oldPeriod⟩)
    (hs : Production.StatusStorage heap p) (result : CBody.Result)
    (executed : CArithmetic.machine.Behaves
      (.running module.startup.body (Production.parameters p) heap) (.terminates result)) :
    MappedStatus module (algorithm modelName identity algorithmSource)
      (production modelName identity algorithmXML module) .startup p result := by
  have unit := (Production.lower_is_unit model).symm.trans lowered
  cases Except.ok.inj unit
  have eq := (CArithmetic.behaviors_of_run (Production.startup_run heap p oldX oldPeriod hx hp hs) _).mp executed
  injection eq with resultEq
  cases resultEq
  apply mapped_status_of_result _ _ _ _ _ _ _ _ ?_ rfl
  simp [Production.initialized, Production.written, Production.clearStatus, replace,
    load, convert, CHeader.statusName]

end Rumoca.EFMI.Manifest

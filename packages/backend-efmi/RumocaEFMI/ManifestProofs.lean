import RumocaEFMI.CInterface
import RumocaEFMI.ManifestView
import RumocaEFMI.IdentityProofs
import RumocaEFMI.MetadataProofs
import XML.Proofs

noncomputable section
namespace Rumoca.EFMI.Manifest
private local instance targetInterface : CInterface := cInterface
open Metadata XML CMemory

theorem decode_dataMapping (method : GALEC.Method) (var : Variable) :
    decodeData (dataMapping method var) = some (dataReference method var) := by
  cases method <;> cases var <;> rfl

theorem decode_function (module : Production.Module) (method : GALEC.Method) :
    decodeFunction (function module method) = some (functionDescription module method) := by
  cases method <;> rfl

theorem data_nodes (modelName : String) (identity : Identity) (algorithmXML : String) (module : Production.Module) :
    dataNodes (production modelName identity algorithmXML module) =
      methods.flatMap (fun method => variables.map (dataMapping method)) := rfl

theorem function_nodes (modelName : String) (identity : Identity) (algorithmXML : String) (module : Production.Module) :
    functionNodes (production modelName identity algorithmXML module) = methods.map (function module) := rfl

theorem data_present (modelName : String) (identity : Identity) (algorithmXML : String) (module : Production.Module)
    (method : GALEC.Method) (var : Variable) :
    dataMapping method var ∈ dataNodes (production modelName identity algorithmXML module) := by
  rw [data_nodes]
  cases method <;> cases var <;> simp [methods, Metadata.variables]

theorem function_present (modelName : String) (identity : Identity) (algorithmXML : String) (module : Production.Module)
    (method : GALEC.Method) :
    function module method ∈ functionNodes (production modelName identity algorithmXML module) := by
  rw [function_nodes]
  cases method <;> simp [methods]

theorem algorithm_variables (modelName : String) (identity : Identity) (source : String) :
    select (algorithm modelName identity source) ["Variables", "RealVariable"] =
      variables.map algorithmVariable := rfl

theorem variable_declared (modelName : String) (identity : Identity) (source : String) (var : Variable) :
    algorithmVariable var ∈ select (algorithm modelName identity source) ["Variables", "RealVariable"] ∧
    (algorithmVariable var).attributes.lookup "id" = some var.id ∧
    (algorithmVariable var).attributes.lookup "name" = some var.name ∧
    var.shape = Tensor.scalar := by
  rw [algorithm_variables]
  cases var <;> exact ⟨by simp [Metadata.variables], rfl, rfl, rfl⟩

def MappedResult (model : Solve.Algorithm.Model source) (module : Production.Module) (root : Element)
    (method : GALEC.Method) (var : Variable) (p : Address)
    (state : GALEC.UnitProfile.State Binary64.Value) (result : CBody.Result) : Prop :=
    ∃ data ∈ dataNodes root,
      ∃ func ∈ functionNodes root,
        ∃ d f, decodeData data = some d ∧ decodeFunction func = some f ∧
          d.foreignVariableId = var.id ∧ d.formalParameterId = f.parameterId ∧
          f.name = (module.method method).signature.name ∧
          result.value = .integer 0 ∧
          CBody.eval (Production.parameters p) result.heap (mappedExpression f d) =
            some (.finite (var.scalarValue (GALEC.UnitProfile.solveExecute model.block
              Binary64.positiveZero Binary64.one GALEC.roundedAdd method state)))

/-- A decoded formal/component reference from the production manifest has the
same execution meaning as the logical variable declared in Algorithm Code. -/
theorem mapped_execution (model : Solve.Algorithm.Model source) (module : Production.Module)
    (lowered : Production.lower model = .ok module) (modelName : String)
    (identity : Identity) (algorithmXML : String)
    (method : GALEC.Method) (var : Variable) (heap : Heap) (p : Address)
    (state : GALEC.UnitProfile.State Binary64.Value) (represents : Production.Represents heap p state)
    (result : CBody.Result)
    (executed : CArithmetic.machine.Behaves
      (.running (module.method method).body (Production.parameters p) heap) (.terminates result)) :
    MappedResult model module (production modelName identity algorithmXML module) method var p state result := by
  refine ⟨dataMapping method var, data_present modelName identity algorithmXML module method var,
    function module method, function_present modelName identity algorithmXML module method,
    dataReference method var, functionDescription module method, decode_dataMapping method var,
    decode_function module method, rfl, rfl, rfl, ?_⟩
  exact Metadata.execution_preserves model module lowered method var heap p state represents result executed

theorem file_checksum (id name : String) (bytes : ByteArray) :
    (file id name bytes).attributes.lookup "checksum" = some (SHA1.hash bytes) := rfl

theorem origin_reference (modelName : String) (identity : Identity) (algorithmXML : String) (module : Production.Module) :
    ∃ origin, select (production modelName identity algorithmXML module)
        ["ManifestReferences", "ManifestReference"] = [origin] ∧
      origin.attributes.lookup "id" = some originId ∧
      origin.attributes.lookup "origin" = some "true" ∧
      origin.attributes.lookup "manifestRefId" = some identity.algorithm ∧
      origin.attributes.lookup "checksum" = some (SHA1.hash algorithmXML.toUTF8) :=
  ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem representation_reference (name kind id xml : String) :
    (representation name kind id xml).attributes.lookup "manifestRefId" = some id ∧
    (representation name kind id xml).attributes.lookup "checksum" = some (SHA1.hash xml.toUTF8) :=
  ⟨rfl, rfl⟩

/-- The graph hashes the same serialized documents that the caller receives,
not separately reconstructed or reformatted XML. -/
theorem prepare_graph (modelName : String) (identity : Identity) (algorithmSource : String) (module : Production.Module) :
    let documents := prepare modelName identity algorithmSource module
    documents.algorithm = algorithm modelName identity algorithmSource ∧
    documents.production = production modelName identity (document documents.algorithm) module ∧
    documents.content = content modelName identity (document documents.algorithm) (document documents.production) :=
  ⟨rfl, rfl, rfl⟩

/-- The manifest name is source metadata supplied by the compiler, distinct
from canonical identifiers in the generated GALEC and C interfaces. -/
def Documents.Named (documents : Documents) (modelName : String) : Prop :=
  documents.algorithm.attributes.lookup "name" = some modelName ∧
    documents.production.attributes.lookup "name" = some modelName ∧
    documents.content.attributes.lookup "name" = some modelName

theorem prepare_named (modelName : String) (identity : Identity) (algorithmSource : String)
    (module : Production.Module) :
    (prepare modelName identity algorithmSource module).Named modelName := ⟨rfl, rfl, rfl⟩

/-- Interpret the actual root attributes, including their lexical and calendar
requirements, separately from XML well-formedness and document construction. -/
def RootIdentity (root : Element) (id generated : String) : Prop :=
  root.attributes.lookup "id" = some id ∧ Identity.UUID id ∧
    root.attributes.lookup "generationDateAndTime" = some generated ∧ Identity.UTC generated

def Documents.Identified (documents : Documents) (identity : Identity) : Prop :=
  RootIdentity documents.algorithm identity.algorithm identity.generated ∧
    RootIdentity documents.production identity.production identity.generated ∧
    RootIdentity documents.content identity.container identity.generated ∧ identity.Distinct

theorem prepare_identified (modelName : String) (identity : Identity) (algorithmSource : String)
    (module : Production.Module) (h : identity.Valid) :
    (prepare modelName identity algorithmSource module).Identified identity :=
  ⟨⟨rfl, h.2.1, rfl, h.2.2.2.1⟩, ⟨rfl, h.2.2.1, rfl, h.2.2.2.1⟩,
    ⟨rfl, h.1, rfl, h.2.2.2.1⟩, h.2.2.2.2⟩

theorem documents_valid (documents : Documents) (h : documents.valid = true) :
    Document documents.algorithm (document documents.algorithm) ∧
    Document documents.production (document documents.production) ∧
    Document documents.content (document documents.content) := by
  simp only [Documents.valid, Bool.and_eq_true] at h
  exact ⟨document_correct _ h.1.1, document_correct _ h.1.2, document_correct _ h.2⟩

theorem checked_correct (modelName : String) (identity : Identity) (algorithmSource : String) (module : Production.Module)
    (result : { documents : Documents // documents.valid = true })
    (h : checked modelName identity algorithmSource module = .ok result) :
    identity.Valid ∧ result.val = prepare modelName identity algorithmSource module ∧
    result.val.Identified identity ∧ result.val.Named modelName ∧
    Document result.val.algorithm (document result.val.algorithm) ∧
    Document result.val.production (document result.val.production) ∧
    Document result.val.content (document result.val.content) := by
  unfold checked at h
  split at h
  · rename_i accepted
    have identityValid := (Identity.valid_iff identity).mp accepted
    dsimp only at h
    split at h
    · cases Except.ok.inj h
      exact ⟨identityValid, rfl, prepare_identified _ _ _ _ identityValid, prepare_named _ _ _ _,
        documents_valid _ (by assumption)⟩
    · contradiction
  · contradiction

end Rumoca.EFMI.Manifest

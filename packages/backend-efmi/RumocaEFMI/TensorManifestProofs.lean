import RumocaEFMI.TensorManifest
import RumocaEFMI.ManifestView
import XML.Proofs

/-! Well-formedness and correlation proofs for the tensor square manifests.

Well-formedness is the independent XML output grammar: a valid tree serializes to
a string the grammar relates back to that tree. The checksum and cross-reference
correlations are read from the actual attributes: the code-file checksums are the
SHA-1 of the emitted bytes, the origin reference and container representations
hash the serialized dependency, each array variable declares its dimensions, and
each logical data reference names the Algorithm Code variable and the C formal it
maps. These hold universally in the model name and packaging identity. -/
namespace Rumoca.EFMI.TensorManifest
open XML
open Rumoca.EFMI.Manifest (select node Identity algorithmFileId productionFileId originId)

/-! ### Well-formedness

The three documents lie in the restricted XML output grammar; the serialized
bytes each document hashes are the same bytes the grammar relates to the tree. -/

theorem documents_valid (documents : Documents) (h : documents.valid = true) :
    Document documents.algorithm (document documents.algorithm) ∧
    Document documents.production (document documents.production) ∧
    Document documents.content (document documents.content) := by
  simp only [Documents.valid, Bool.and_eq_true] at h
  exact ⟨document_correct _ h.1.1, document_correct _ h.1.2, document_correct _ h.2⟩

/-! ### Array variable declarations

Each logical variable is declared in the Algorithm Code `Variables` list with its
identifier, name, causality and dimensions. -/

theorem algorithm_variables (modelName : String) (identity : Identity) (source : String) :
    select (algorithm modelName identity source) ["Variables", "RealVariable"] =
      logicalVars.map algorithmVariable := rfl

/-- Every logical variable is declared with its identifier, name, causality and
its fixed dimensions, universal in the model name and identity. -/
theorem variable_declared (modelName : String) (identity : Identity) (source : String)
    (v : Var) (mem : v ∈ logicalVars) :
    algorithmVariable v ∈ select (algorithm modelName identity source) ["Variables", "RealVariable"] ∧
    (algorithmVariable v).attributes.lookup "id" = some v.algId ∧
    (algorithmVariable v).attributes.lookup "name" = some v.name ∧
    (algorithmVariable v).attributes.lookup "blockCausality" = some v.causality ∧
    (algorithmVariable v).children = dimensionNodes v.dims := by
  rw [algorithm_variables]
  exact ⟨List.mem_map_of_mem mem, rfl, rfl, rfl, rfl⟩

/-- The Jacobian variable declares both fixed extents as consecutive dimensions. -/
theorem jacobian_dimensions :
    (algorithmVariable jacobianVar).children = dimensionNodes [2, 2] ∧
    dimensionNodes [2, 2] = [node "Dimensions" []
      [node "Dimension" [("number", "1"), ("size", "2")],
       node "Dimension" [("number", "2"), ("size", "2")]]] :=
  ⟨rfl, rfl⟩

/-! ### Checksum correlation

The code files carry the SHA-1 of their emitted bytes; the origin reference and
the container representations hash the serialized dependency. -/

theorem algorithm_file_checksum (id name : String) (bytes : ByteArray) :
    (Manifest.file id name bytes).attributes.lookup "checksum" = some (SHA1.hash bytes) := rfl

theorem representation_reference (name kind id xml : String) :
    (representation name kind id xml).attributes.lookup "manifestRefId" = some id ∧
    (representation name kind id xml).attributes.lookup "checksum" = some (SHA1.hash xml.toUTF8) :=
  ⟨rfl, rfl⟩

/-! ### Logical data cross-references

Each data reference names the Algorithm Code variable and the C formal parameter
it maps; each function reference names the block method and the C function. -/

/-- A data reference names the foreign Algorithm Code variable and the C formal
parameter and component it maps, for every method and mapped variable. -/
theorem dataMapping_refs (m : Method) (v : Var) :
    ∃ foreign formal, (dataMapping m v).children = [foreign, formal] ∧
      foreign.attributes.lookup "manifestReferenceRefId" = some Manifest.originId ∧
      foreign.attributes.lookup "foreignRefId" = some v.algId ∧
      formal.attributes.lookup "formalParameterRefId" = some m.cp ∧
      formal.attributes.lookup "componentIdentifier" = some v.name :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

/-- The status reference maps the Algorithm Code error anchor to the C error word
of the same method's formal parameter. -/
theorem statusMapping_refs (m : Method) :
    ∃ foreign formal, (statusMapping m).children = [foreign, formal] ∧
      foreign.attributes.lookup "foreignRefId" = some errorSignalId ∧
      formal.attributes.lookup "formalParameterRefId" = some m.cp ∧
      formal.attributes.lookup "componentIdentifier" = some TensorProduction.statusName :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- A function reference names the block method and the global C function. -/
theorem functionMapping_refs (m : Method) :
    ∃ foreign global, (functionMapping m).children = [foreign, global] ∧
      foreign.attributes.lookup "foreignRefId" = some m.af ∧
      global.attributes.lookup "functionRefId" = some m.cf :=
  ⟨_, _, rfl, rfl, rfl⟩



/-! ### Code checksum graph

These universally quantified facts tie both code File nodes and all manifest dependencies to the supplied bytes.
They do not assign execution semantics or standards conformance to arbitrary C. -/

theorem prepare_graph (name : String) (id : Identity) (algorithmSource productionSource : String) :
    let documents := prepare name id algorithmSource productionSource
    documents.algorithm = algorithm name id algorithmSource ∧
    documents.production = production name id (document documents.algorithm) productionSource ∧
    documents.content = content name id (document documents.algorithm) (document documents.production) :=
  ⟨rfl, rfl, rfl⟩

theorem prepare_named (name : String) (id : Identity) (algorithmSource productionSource : String) :
    let documents := prepare name id algorithmSource productionSource
    documents.algorithm.attributes.lookup "name" = some name ∧
    documents.production.attributes.lookup "name" = some name ∧
    documents.content.attributes.lookup "name" = some name := ⟨rfl, rfl, rfl⟩

theorem origin_reference (name : String) (id : Identity) (algorithmXML productionSource : String) :
    ∃ origin, select (production name id algorithmXML productionSource)
        ["ManifestReferences", "ManifestReference"] = [origin] ∧
      origin.attributes.lookup "id" = some originId ∧
      origin.attributes.lookup "origin" = some "true" ∧
      origin.attributes.lookup "manifestRefId" = some id.algorithm ∧
      origin.attributes.lookup "checksum" = some (SHA1.hash algorithmXML.toUTF8) :=
  ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- Read both code hashes from the actual selected File nodes, with their IDs
and names; no positional XML rewriting or producer checksum is accepted. -/
theorem prepare_file_checksums (name : String) (id : Identity) (algorithmSource productionSource : String) :
    let documents := prepare name id algorithmSource productionSource
    ∃ manifest algorithmFile productionFile,
      select documents.algorithm ["Files", "File"] = [manifest, algorithmFile] ∧
      select documents.production ["Files", "File"] = [manifest, productionFile] ∧
      algorithmFile.attributes.lookup "id" = some algorithmFileId ∧
      algorithmFile.attributes.lookup "name" = some "model.alg" ∧
      algorithmFile.attributes.lookup "checksum" = some (SHA1.hash algorithmSource.toUTF8) ∧
      productionFile.attributes.lookup "id" = some productionFileId ∧
      productionFile.attributes.lookup "name" = some "production.c" ∧
      productionFile.attributes.lookup "checksum" = some (SHA1.hash productionSource.toUTF8) :=
  ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem prepare_checksums (name : String) (id : Identity) (algorithmSource productionSource : String) :
    let documents := prepare name id algorithmSource productionSource
    (∃ origin, select documents.production ["ManifestReferences", "ManifestReference"] = [origin] ∧
      origin.attributes.lookup "checksum" = some (SHA1.hash (document documents.algorithm).toUTF8)) ∧
    (representation "AlgorithmCode" "AlgorithmCode" id.algorithm
        (document documents.algorithm)).attributes.lookup "checksum" =
      some (SHA1.hash (document documents.algorithm).toUTF8) ∧
    (representation "ProductionCode" "ProductionCode" id.production
        (document documents.production)).attributes.lookup "checksum" =
      some (SHA1.hash (document documents.production).toUTF8) := ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩

/-- The hashed representations are exactly the container's selected nodes. -/
theorem prepare_container_checksums (name : String) (id : Identity) (algorithmSource productionSource : String) :
    let documents := prepare name id algorithmSource productionSource
    ∃ a p, select documents.content ["ModelRepresentation"] = [a, p] ∧
      a.attributes.lookup "name" = some "AlgorithmCode" ∧
      a.attributes.lookup "manifestRefId" = some id.algorithm ∧
      a.attributes.lookup "checksum" = some (SHA1.hash (document documents.algorithm).toUTF8) ∧
      p.attributes.lookup "name" = some "ProductionCode" ∧
      p.attributes.lookup "manifestRefId" = some id.production ∧
      p.attributes.lookup "checksum" = some (SHA1.hash (document documents.production).toUTF8) :=
  ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem data_nodes (name : String) (id : Identity) (algorithmXML productionSource : String) :
    select (production name id algorithmXML productionSource)
      ["CodeContainer", "LogicalData", "DataReferences", "DataReference"] =
      (methods.flatMap fun m => mappedVariables.map (dataMapping m)) ++ methods.map statusMapping := rfl

theorem function_nodes (name : String) (id : Identity) (algorithmXML productionSource : String) :
    select (production name id algorithmXML productionSource)
      ["CodeContainer", "LogicalData", "FunctionReferences", "FunctionReference"] =
      methods.map functionMapping := rfl

theorem function_declarations (name : String) (id : Identity) (algorithmXML productionSource : String) :
    Manifest.functionNodes (production name id algorithmXML productionSource) = methods.map function := rfl


/-- Each mapped variable of each method is present in the production logical data,
correlating the Algorithm Code declaration and the C formal. -/
theorem data_present (modelName : String) (identity : Identity) (algorithmXML productionSource : String)
    (m : Method) (v : Var) (hm : m ∈ methods) (hv : v ∈ mappedVariables) :
    dataMapping m v ∈ select (production modelName identity algorithmXML productionSource)
      ["CodeContainer", "LogicalData", "DataReferences", "DataReference"] := by
  rw [data_nodes]
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨m, hm, List.mem_map_of_mem hv⟩)

/-- Each method's function is present in the production logical data, correlating
the block method identifier and the C function identifier. -/
theorem function_present (modelName : String) (identity : Identity) (algorithmXML productionSource : String)
    (m : Method) (hm : m ∈ methods) :
    functionMapping m ∈ select (production modelName identity algorithmXML productionSource)
      ["CodeContainer", "LogicalData", "FunctionReferences", "FunctionReference"] := by
  rw [function_nodes]
  exact List.mem_map_of_mem hm

end Rumoca.EFMI.TensorManifest

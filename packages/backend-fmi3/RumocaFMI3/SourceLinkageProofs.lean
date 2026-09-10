import RumocaFMI3.BuildDescriptionProofs
import RumocaFMI3.Runtime

namespace Rumoca.FMI3

/-- The actual source prefix names a valid C token and includes the private
kernel in this translation unit. The rest of the FMI adapter is outside this
fragment contract. Official-header preprocessing and native linking remain
explicit boundaries. -/
def SourcePrefixContract (modelName adapter : String) : Prop :=
  CIdentifier.valid [] (modelIdentifier modelName ++ "_") = true ∧
  ∃ rest : String, adapter = "#define FMI3_FUNCTION_PREFIX " ++ modelIdentifier modelName ++
    "_\n" ++ "#include \"model.c\"\n" ++ rest

/-- Character-prefix evidence yields the same complete string decomposition.
This lets actual-file certificates quote long input as small character blocks
without reducing a UTF-8 builder over the whole adapter. -/
theorem sourcePrefix_of_chars (modelName : String) (chars : List Char)
    (valid : CIdentifier.valid [] (modelIdentifier modelName ++ "_") = true)
    (head : ("#define FMI3_FUNCTION_PREFIX " ++ modelIdentifier modelName ++
      "_\n" ++ "#include \"model.c\"\n").toList <+: chars) :
    SourcePrefixContract modelName (String.ofList chars) := by
  obtain ⟨rest, eq⟩ := head
  refine ⟨valid, ⟨String.ofList rest, ?_⟩⟩
  rw [← eq, String.ofList_append, String.ofList_toList]

theorem sourcePrefix_correct (m : Solve.FMI3Model source) (signatures : List CTree.Signature)
    (parts : NameParts m.name) : SourcePrefixContract m.name (Runtime.render m signatures) := by
  refine ⟨functionPrefix_word parts,
    ⟨Runtime.declarations ++ String.join (Runtime.helpers.map CTree.Function.render) ++
      String.join (signatures.map fun sig => (CTree.Function.mk sig (Runtime.body m sig) false).render), ?_⟩⟩
  simp only [Runtime.render, functionPrefix, String.append_assoc]

/-- Read the public identity of each advertised interface independently of
model-description generation. Missing or repeated interfaces fail decoding. -/
def decodeModelIdentifiers (root : XML.Element) : Option (String × String × String) := do
  guard (root.name == "fmiModelDescription")
  guard (root.attributes.lookup "fmiVersion" == some "3.0")
  let modelName ← root.attributes.lookup "modelName"
  let me ← Build.only? (root.children.filter (·.name == "ModelExchange"))
  let cs ← Build.only? (root.children.filter (·.name == "CoSimulation"))
  let meId ← me.attributes.lookup "modelIdentifier"
  let csId ← cs.attributes.lookup "modelIdentifier"
  return (modelName, meId, csId)

def ModelIdentifiersContract (modelName xml : String) : Prop :=
  ∃ root, XML.Document root xml ∧
    decodeModelIdentifiers root = some (modelName, modelIdentifier modelName, modelIdentifier modelName)

theorem modelIdentifiers_decode (m : Solve.FMI3Model source) :
    decodeModelIdentifiers (modelDescription m) = some (m.name, modelIdentifier m.name, modelIdentifier m.name) := by
  simp [decodeModelIdentifiers, modelDescription, guard, Build.only?, List.filter, List.lookup]

end Rumoca.FMI3

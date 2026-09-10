import RumocaEFMI.Manifest

/-! Read the manifest trees independently of their constructors. Selection
uses tag paths; references and signatures are decoded from actual attributes.
This is not a parser for XML characters: XMLProofs supplies their separate
binding to a tree. -/
namespace Rumoca.EFMI.Manifest
open Metadata XML

def select (root : Element) : List String → List Element
  | [] => [root]
  | name :: rest => root.children.flatMap fun child =>
      if child.name == name then select child rest else []

def only (elements : List Element) : Option Element := match elements with
  | [element] => some element
  | _ => none

def decodeData (element : Element) : Option DataReference := do
  if element.name != "DataReference" then none else do
    let foreign ← only (select element ["ForeignVariableReference"])
    let formal ← only (select element ["FormalParameter"])
    if (← foreign.attributes.lookup "manifestReferenceRefId") != originId then none else do
      return ⟨← foreign.attributes.lookup "foreignRefId",
        ← formal.attributes.lookup "formalParameterRefId",
        ← formal.attributes.lookup "componentIdentifier"⟩

def decodeFunction (element : Element) : Option FunctionDescription := do
  if element.name != "Function" then none else do
    let result ← only (select element ["ReturnParameter"])
    let formal ← only (select element ["FormalParameters", "FormalParameter"])
    if (← formal.attributes.lookup "number") != "0" then none else do
      let pointer ← formal.attributes.lookup "pointer"
      if pointer != "true" && pointer != "false" then none else do
        return ⟨← element.attributes.lookup "id", ← element.attributes.lookup "name",
          ← result.attributes.lookup "id", ← result.attributes.lookup "typeDefRefId",
          ← formal.attributes.lookup "id", ← formal.attributes.lookup "name",
          ← formal.attributes.lookup "typeDefRefId", pointer == "true"⟩

def mappedExpression (f : FunctionDescription) (d : DataReference) : CTree.Expr :=
  .field (.id f.parameterName) d.componentIdentifier true

def dataNodes (root : Element) : List Element :=
  select root ["CodeContainer", "LogicalData", "DataReferences", "DataReference"]

def functionNodes (root : Element) : List Element :=
  select root ["CodeContainer", "CodeFiles", "CodeFile", "Functions", "Function"]

end Rumoca.EFMI.Manifest

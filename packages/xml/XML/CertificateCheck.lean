import XML.Certificate
import Lean.Elab.Command

/-! Quote a candidate tree and produce a theorem binding its complete rendered
document to the supplied string. Native computation proposes data only. Each
element and child-list composition is checked by Lean's kernel. -/
namespace XML.CertificateCheck
open Lean Elab Command

private def chars (value : List Char) : CommandElabM (TSyntax `term) := do
  let entries ← value.toArray.mapM fun c => do
    let n := Syntax.mkNumLit (toString c.toNat)
    `(term| Char.ofNat $n)
  `(term| ([$entries,*] : List Char))

private partial def element (name : Lean.Name) (e : Element) (depth : Nat) : CommandElabM Unit := do
  let children := e.children.toArray
  let child := fun i => name.str s!"child_{depth}_{i}"
  let many := fun i => mkIdent (name.str s!"children_{i}")
  let body := fun i => mkIdent (name.str s!"body_{i}")
  let manyEq := fun i => mkIdent (name.str s!"children_eq_{i}")
  let d := Syntax.mkNumLit (toString depth)
  let nextDepth := Syntax.mkNumLit (toString (depth + 1))
  for (entry, i) in e.children.zipIdx do
    element (child i) entry (depth + 1)
  let endChildren := many children.size
  let endBody := body children.size
  let endEq := manyEq children.size
  elabCommand (← `(command| def $endChildren:ident : List Element := []))
  elabCommand (← `(command| def $endBody:ident : List Char := []))
  elabCommand (← `(command| theorem $endEq:ident :
    (($endChildren).flatMap fun c => (c.render $nextDepth).toList) = $endBody := rfl))
  for j in [:children.size] do
    let i := children.size - 1 - j
    let head := mkIdent (child i)
    let headChars := mkIdent ((child i).str "chars")
    let headEq := mkIdent ((child i).str "rendered")
    let rest := many (i + 1)
    let restBody := body (i + 1)
    let restEq := manyEq (i + 1)
    let cs := many i
    let text := body i
    let eq := manyEq i
    elabCommand (← `(command| def $cs:ident : List Element := $head :: $rest))
    elabCommand (← `(command| def $text:ident : List Char := $headChars ++ $restBody))
    elabCommand (← `(command| theorem $eq:ident :
      (($cs).flatMap fun c => (c.render $nextDepth).toList) = $text :=
        Certificate.children_cons $head $rest $nextDepth $headChars $restBody $headEq:ident $restEq:ident))
  let node := mkIdent name
  let nodeName := Syntax.mkStrLit e.name
  let value := Syntax.mkStrLit e.text
  let attrs ← e.attributes.toArray.mapM fun (key, value) => do
    let key := Syntax.mkStrLit key
    let value := Syntax.mkStrLit value
    `(term| ($key, $value))
  let cs := many 0
  let content := body 0
  let contentEq := manyEq 0
  elabCommand (← `(command| def $node:ident : Element := ⟨$nodeName, [$attrs,*], $cs, $value⟩))
  let leading := mkIdent (name.str "leading")
  let trailing := mkIdent (name.str "trailing")
  let leadingEq := mkIdent (name.str "leading_eq")
  let trailingEq := mkIdent (name.str "trailing_eq")
  let leadingValue ← chars (Certificate.leading e depth)
  let trailingValue ← chars (Certificate.trailing e depth)
  elabCommand (← `(command| def $leading:ident : List Char := $leadingValue))
  elabCommand (← `(command| def $trailing:ident : List Char := $trailingValue))
  elabCommand (← `(command| theorem $leadingEq:ident : Certificate.leading $node $d = $leading := by decide +kernel))
  elabCommand (← `(command| theorem $trailingEq:ident : Certificate.trailing $node $d = $trailing := by decide +kernel))
  let output := mkIdent (name.str "chars")
  let rendered := mkIdent (name.str "rendered")
  elabCommand (← `(command| def $output:ident : List Char := $leading ++ $content ++ $trailing))
  elabCommand (← `(command| theorem $rendered:ident : (($node).render $d).toList = $output :=
    Certificate.node $node $d $leading $content $trailing $leadingEq:ident $contentEq:ident $trailingEq:ident))
  if (← get).messages.hasErrors then
    throwError "XML element certificate failed: {name}"

/-- Define `treeName` and prove `XML.document treeName = source` as `proofName`.
Both names must be fresh. The caller audits the final theorem's dependencies. -/
def certify (treeName proofName : Lean.Name) (tree : Element) (source : String) : CommandElabM Unit := do
  element treeName tree 0
  let root := mkIdent treeName
  let body := mkIdent (treeName.str "chars")
  let rendered := mkIdent (treeName.str "rendered")
  let header := mkIdent (proofName.str "header")
  let headerEq := mkIdent (proofName.str "header_eq")
  let output := mkIdent (proofName.str "chars")
  let outputEq := mkIdent (proofName.str "chars_eq")
  let flat := mkIdent (proofName.str "flat_chars")
  let flatEq := mkIdent (proofName.str "flat_eq")
  let sourceEq := mkIdent (proofName.str "source_eq")
  let statement := mkIdent proofName
  let actual := Syntax.mkStrLit source
  let headerValue ← chars Certificate.header
  elabCommand (← `(command| def $header:ident : List Char := $headerValue))
  elabCommand (← `(command| theorem $headerEq:ident : Certificate.header = $header := by decide +kernel))
  elabCommand (← `(command| def $output:ident : List Char := $header ++ $body))
  elabCommand (← `(command| theorem $outputEq:ident : (XML.document $root).toList = $output :=
    (Certificate.document $root $body $rendered:ident).trans (congrArg (· ++ $body) $headerEq:ident)))
  -- A flat literal lets Lean's string-literal checker avoid evaluating the
  -- renderer's nested concatenations inside String.ofList. The connection
  -- to the composed output is itself checked by the kernel.
  let flatValue ← chars source.toList
  elabCommand (← `(command| def $flat:ident : List Char := $flatValue))
  elabCommand (← `(command| theorem $flatEq:ident : $output = $flat := by decide +kernel))
  -- Elaboration uses the character representation; the kernel still checks
  -- the exact original string literal against the composed character list.
  elabCommand (← `(command| section))
  try
    elabCommand (← `(command| attribute [local irreducible] String.ofList XML.document))
    elabCommand (← `(command| theorem $sourceEq:ident : $actual = String.ofList $flat := by rfl))
    elabCommand (← `(command| theorem $statement:ident : XML.document $root = $actual :=
      String.toList_injective (($outputEq:ident |>.trans $flatEq:ident).trans
        ((congrArg String.toList $sourceEq:ident).trans String.toList_ofList).symm)))
  finally
    elabCommand (← `(command| end))
  if (← get).messages.hasErrors then
    throwError "XML document certificate failed"

private partial def validity (name : Lean.Name) (e : Element) (depth : Nat) : CommandElabM Unit := do
  let child := fun i => name.str s!"child_{depth}_{i}"
  let many := fun i => mkIdent (name.str s!"children_{i}")
  let manyValid := fun i => mkIdent (name.str s!"children_valid_{i}")
  for (entry, i) in e.children.zipIdx do
    validity (child i) entry (depth + 1)
  let empty := many e.children.length
  let emptyValid := manyValid e.children.length
  elabCommand (← `(command| theorem $emptyValid:ident :
    (($empty).map Element.valid).all id = true := rfl))
  for j in [:e.children.length] do
    let i := e.children.length - 1 - j
    let head := mkIdent (child i)
    let headValid := mkIdent ((child i).str "valid_eq")
    let rest := many (i + 1)
    let restValid := manyValid (i + 1)
    let cs := many i
    let valid := manyValid i
    elabCommand (← `(command| theorem $valid:ident :
      (($cs).map Element.valid).all id = true :=
        Certificate.children_valid_cons $head $rest $headValid:ident $restValid:ident))
  let node := mkIdent name
  let headValid := mkIdent (name.str "valid_head")
  let childrenValid := manyValid 0
  let valid := mkIdent (name.str "valid_eq")
  elabCommand (← `(command| theorem $headValid:ident :
    decide (XML.Name ($node).name ∧ AttributesValid ($node).attributes ∧ Text ($node).text ∧
      (($node).text = "" ∨ ($node).children = [])) = true := by decide +kernel))
  elabCommand (← `(command| theorem $valid:ident : ($node).valid = true :=
    Certificate.node_valid $node $headValid:ident $childrenValid:ident))
  if (← get).messages.hasErrors then
    throwError "XML validity certificate failed: {name}"

/-- After `certify` defines the candidate tree, also prove `treeName.valid_eq`:
the tree passes the restricted XML output validator. This is a separate
obligation from faithful serialization. The caller audits the final theorem. -/
def certifyValidity (treeName : Lean.Name) (tree : Element) : CommandElabM Unit :=
  validity treeName tree 0

end XML.CertificateCheck

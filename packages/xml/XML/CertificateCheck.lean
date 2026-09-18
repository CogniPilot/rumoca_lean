import XML.Certificate
import Lean.Elab.Command

/-! Quote a candidate tree and produce a theorem binding its complete rendered
document to the supplied string. Native computation proposes data only. Every
element's opening and closing pieces are checked by Lean's kernel against
bounded literals, and their concatenation is bound to the actual bytes through a
block-structured cursor, so no single kernel step reduces the whole document. -/
namespace XML.CertificateCheck
open Lean Elab Command

private def chars (value : List Char) : CommandElabM (TSyntax `term) := do
  let entries ← value.toArray.mapM fun c => do
    let n := Syntax.mkNumLit (toString c.toNat)
    `(term| Char.ofNat $n)
  `(term| ([$entries,*] : List Char))

/-- Characters per input block. The whole-document literal is stored as blocks
sharing tails, so each cursor equality reduces only one bounded segment. -/
def blockSize : Nat := 256

/-- Store `input` as a block-structured character literal under `prefixName`:
`<prefixName>.part_0` is the whole list and each `part_i` is one block prepended
to the next part, so `List.drop k part_j` exposes an arbitrary suffix cheaply. -/
private def quoteBlocks (prefixName : Lean.Name) (input : String) : CommandElabM Unit := do
  let cs := input.toList.toArray
  let count := (cs.size + blockSize - 1) / blockSize
  let part := fun i => mkIdent (prefixName.str s!"part_{i}")
  elabCommand (← `(command| def $(part count):ident : List Char := []))
  for j in [:count] do
    let i := count - 1 - j
    let values ← (cs.toSubarray (i * blockSize) (min ((i + 1) * blockSize) cs.size)).toArray.mapM
      fun c => `(term| Char.ofNat $(Syntax.mkNumLit (toString c.toNat)))
    elabCommand (← `(command| def $(part i):ident : List Char := [$values,*] ++ $(part (i + 1))))

private def remaining (prefixName : Lean.Name) (offset : Nat) : CommandElabM (TSyntax `term) := do
  let block := mkIdent (prefixName.str s!"part_{offset / blockSize}")
  `(term| List.drop $(Syntax.mkNumLit (toString (offset % blockSize))) $block)

/-- Prove `left = right` by kernel reflexivity, admitting only the three approved
foundational axioms that the referenced XML definitions carry in their types. -/
private def checkEq (name : Ident) (left right : TSyntax `term) : CommandElabM Unit := do
  liftTermElabM do
    let type ← Term.elabType (← `(term| $left = $right))
    let rhs ← Term.elabTerm (← `(term| ($right : List Char))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let proof ← Meta.mkEqRefl (← instantiateMVars rhs)
    addDecl (.thmDecl { name := name.getId, levelParams := [], type, value := proof })
  for dependency in ← collectAxioms name.getId do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "invalid character equality certificate: {dependency}"

/-- Prove `[c0,…,cn].flatten = List.drop 0 <prefixName>.part_0` by composing
per-segment cursor equalities. Segment lengths only choose input cursors; the
kernel checks every split against the actual block-structured input. -/
private def concatenate (name : Lean.Name) (prefixName : Lean.Name)
    (pieces : Array Ident) (lengths : Array Nat) : CommandElabM Ident := do
  let mut splits : Array Ident := #[]
  let mut offsets : Array Nat := #[0]
  let mut offset := 0
  for i in [:pieces.size] do
    let start ← remaining prefixName offset
    offset := offset + lengths[i]!
    let rest ← remaining prefixName offset
    let split := mkIdent (name.str s!"split_{i}")
    checkEq split start (← `(term| $(pieces[i]!) ++ $rest))
    splits := splits.push split
    offsets := offsets.push offset
  let last ← remaining prefixName offset
  let empty := mkIdent (name.str "empty")
  checkEq empty last (← `(term| ([] : List Char)))
  let mut tail := mkIdent (name.str "pieces_end")
  let mut joined := mkIdent (name.str "joined_end")
  elabCommand (← `(command| def $tail:ident : List (List Char) := []))
  elabCommand (← `(command| theorem $joined:ident : ($tail).flatten = $last := Eq.symm $empty))
  for j in [:pieces.size] do
    let i := pieces.size - 1 - j
    let start ← remaining prefixName offsets[i]!
    let next := mkIdent (name.str s!"pieces_{i}")
    let nextEq := mkIdent (name.str s!"joined_{i}")
    elabCommand (← `(command| def $next:ident : List (List Char) := $(pieces[i]!) :: $tail))
    elabCommand (← `(command| theorem $nextEq:ident : ($next).flatten = $start := by
      change $(pieces[i]!) ++ ($tail).flatten = $start
      exact (congrArg (fun r : List Char => $(pieces[i]!) ++ r) $joined).trans (Eq.symm $(splits[i]!))))
    tail := next
    joined := nextEq
  if (← get).messages.hasErrors then throwError "XML fragment concatenation failed"
  return joined

/-- Emit the element and child definitions, prove each element's opening/closing
pieces equal to bounded literals, and compose the fragment-list equality. Returns
the element's piece term, its `pieces` equality, the flat chunk literals in
pre-order, and their character lengths. The child node and child-list definitions
are named so `certifyValidity` can also reference them. -/
private partial def element (name : Lean.Name) (e : Element) (depth : Nat) :
    CommandElabM (TSyntax `term × Ident × Array Ident × Array Nat) := do
  let child := fun i => name.str s!"child_{depth}_{i}"
  let many := fun i => mkIdent (name.str s!"children_{i}")
  let d := Syntax.mkNumLit (toString depth)
  let nextDepth := Syntax.mkNumLit (toString (depth + 1))
  let mut childTerms : Array (TSyntax `term) := #[]
  let mut childEqs : Array Ident := #[]
  let mut flatChunks : Array Ident := #[]
  let mut flatLengths : Array Nat := #[]
  for (entry, i) in e.children.zipIdx do
    let (cterm, ceq, cflat, clen) ← element (child i) entry (depth + 1)
    childTerms := childTerms.push cterm
    childEqs := childEqs.push ceq
    flatChunks := flatChunks ++ cflat
    flatLengths := flatLengths ++ clen
  -- Child-list definitions: children_n = [], children_i = child_i :: children_{i+1}.
  let endChildren := many e.children.length
  elabCommand (← `(command| def $endChildren:ident : List Element := []))
  for j in [:e.children.length] do
    let i := e.children.length - 1 - j
    let head := mkIdent (child i)
    let rest := many (i + 1)
    let cs := many i
    elabCommand (← `(command| def $cs:ident : List Element := $head :: $rest))
  let node := mkIdent name
  let nodeName := Syntax.mkStrLit e.name
  let value := Syntax.mkStrLit e.text
  let attrs ← e.attributes.toArray.mapM fun (key, value) => do
    `(term| ($(Syntax.mkStrLit key), $(Syntax.mkStrLit value)))
  elabCommand (← `(command| def $node:ident : Element := ⟨$nodeName, [$attrs,*], $(many 0), $value⟩))
  -- Opening and closing pieces as bounded literals, checked by reflexivity.
  let leadLit := mkIdent (name.str "leading")
  let trailLit := mkIdent (name.str "trailing")
  let leadVal := Certificate.leading e depth
  let trailVal := Certificate.trailing e depth
  elabCommand (← `(command| def $leadLit:ident : List Char := $(← chars leadVal)))
  elabCommand (← `(command| def $trailLit:ident : List Char := $(← chars trailVal)))
  let leadEq := mkIdent (name.str "leading_eq")
  let trailEq := mkIdent (name.str "trailing_eq")
  checkEq leadEq (← `(term| Certificate.leading $node $d)) (← `(term| $leadLit))
  checkEq trailEq (← `(term| Certificate.trailing $node $d)) (← `(term| $trailLit))
  -- Child fragment-list equality via an explicit pieces_children_cons fold.
  let childPieces ← if childTerms.isEmpty then `(term| ([] : List (List Char)))
    else do
      let mut acc := childTerms[childTerms.size - 1]!
      for k in [1:childTerms.size] do
        acc ← `(term| $(childTerms[childTerms.size - 1 - k]!) ++ $acc)
      pure acc
  let pcc := mkIdent ``XML.Certificate.pieces_children_cons
  let mut chainProof ← `(term| (rfl : (($(many e.children.length)).map fun c => Certificate.pieces c $nextDepth).flatten = []))
  for j in [:e.children.length] do
    let i := e.children.length - 1 - j
    let restTerm ← if i + 1 == e.children.length then `(term| ([] : List (List Char)))
      else do
        let mut acc := childTerms[e.children.length - 1]!
        for k in [1:e.children.length - (i + 1)] do
          acc ← `(term| $(childTerms[e.children.length - 1 - k]!) ++ $acc)
        pure acc
    chainProof ← `(term| $pcc $(mkIdent (child i)) $(many (i + 1)) $nextDepth
      $(childTerms[i]!) $restTerm $(childEqs[i]!) $chainProof)
  let childrenEq := mkIdent (name.str "children_pieces_eq")
  elabCommand (← `(command| theorem $childrenEq:ident :
    (($(many 0)).map fun c => Certificate.pieces c $nextDepth).flatten = $childPieces := $chainProof))
  let piecesEq := mkIdent (name.str "pieces_eq")
  let chunksTerm ← `(term| $leadLit :: ($childPieces ++ [$trailLit]))
  elabCommand (← `(command| theorem $piecesEq:ident : Certificate.pieces $node $d = $chunksTerm :=
    Certificate.pieces_node $node $d $leadLit $trailLit $childPieces $leadEq $trailEq $childrenEq))
  if (← get).messages.hasErrors then throwError "XML element certificate failed: {name}"
  return (chunksTerm, piecesEq, #[leadLit] ++ flatChunks ++ #[trailLit],
    #[leadVal.length] ++ flatLengths ++ #[trailVal.length])

/-- Define `treeName` and prove `XML.document treeName = source` as `proofName`.
Both names must be fresh. The caller audits the final theorem's dependencies. -/
def certify (treeName proofName : Lean.Name) (tree : Element) (source : String) : CommandElabM Unit := do
  let (rootTerm, rootEq, flatChunks, flatLengths) ← element treeName tree 0
  let root := mkIdent treeName
  let headerLit := mkIdent (proofName.str "header")
  elabCommand (← `(command| def $headerLit:ident : List Char := $(← chars Certificate.header)))
  let headerEq := mkIdent (proofName.str "header_eq")
  checkEq headerEq (← `(term| Certificate.header)) (← `(term| $headerLit))
  -- documentPieces treeName as a nested piece term, then normalized to a flat
  -- chunk list. The normalization reduces only the list spine of identifiers.
  let nestedEq := mkIdent (proofName.str "pieces_nested")
  let nestedTerm ← `(term| $headerLit :: $rootTerm)
  elabCommand (← `(command| theorem $nestedEq:ident :
    Certificate.documentPieces $root = $nestedTerm :=
      Certificate.documentPieces_eq $root $headerLit $rootTerm $headerEq $rootEq))
  let allChunks := #[headerLit] ++ flatChunks
  let allLengths := #[Certificate.header.length] ++ flatLengths
  let flatList ← `(term| [$allChunks,*])
  let piecesEq := mkIdent (proofName.str "pieces_eq")
  elabCommand (← `(command| theorem $piecesEq:ident :
    Certificate.documentPieces $root = $flatList := ($nestedEq).trans (by rfl)))
  -- Store the whole document bytes as blocks and join the chunks by cursors.
  let partsPrefix := proofName.str "chars"
  quoteBlocks partsPrefix source
  let joined ← concatenate (proofName.str "concat") partsPrefix allChunks allLengths
  let bytes ← remaining partsPrefix 0
  let joinedEq := mkIdent (proofName.str "joined")
  elabCommand (← `(command| theorem $joinedEq:ident : ($flatList).flatten = $bytes := $joined))
  let actual := Syntax.mkStrLit source
  let statement := mkIdent proofName
  elabCommand (← `(command| theorem $statement:ident : XML.document $root = $actual :=
    (Certificate.document_ofList $root $flatList $bytes $piecesEq $joinedEq).trans (by rfl)))
  if (← get).messages.hasErrors then throwError "XML document certificate failed"

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

import RumocaC.FunctionPrinter
import Lean

/-! Candidate proof construction for raw C signature spellings. The caller
supplies the typedef context and the actual signature data. This tool proposes
applications of the shared printer theorems, never an assumed type meaning or
parser result. The kernel must check the resulting SignaturePrintable judgment;
unsupported spellings fail certification. No file I/O is performed here. -/
namespace Rumoca.CTree.Printer.Certificate
open Lean Elab Command

-- Quotation proposes constructor trees only. The generated equality below is
-- checked by the kernel; neither this metaprogram nor native rendering is trusted.
deriving instance ToExpr for CTree.BinOp
deriving instance ToExpr for CTree.Expr
deriving instance ToExpr for CTree.Stmt
deriving instance ToExpr for CTree.Parameter
deriving instance ToExpr for CTree.Signature
deriving instance ToExpr for CTree.Function

def characterBlockSize : Nat := 256

def quoteCharacters (name : Name) (input : String) : CommandElabM Ident := do
  let chars := input.toList.toArray
  let count := (chars.size + characterBlockSize - 1) / characterBlockSize
  let part := fun i => mkIdent (name.str s!"part_{i}")
  let last := part count
  elabCommand (← `(command| def $last:ident : List Char := []))
  for j in [:count] do
    let i := count - 1 - j
    let values ← (chars.toSubarray (i * characterBlockSize)
      (min ((i + 1) * characterBlockSize) chars.size)).toArray.mapM fun c => do
      let n := Syntax.mkNumLit (toString c.toNat)
      `(term| Char.ofNat $n)
    let current := part i
    let rest := part (i + 1)
    elabCommand (← `(command| def $current:ident : List Char := [$values,*] ++ $rest))
  return part 0

-- A cursor refers to the independently quoted input, sharing its unconsumed
-- tail. Each kernel equality then reduces only the current segment, rather
-- than comparing the complete translation unit with recursive DecidableEq.
def remainingCharacters (actual : Ident) (offset : Nat) : CommandElabM (TSyntax `term) := do
  let block := mkIdent (actual.getId.getPrefix.str s!"part_{offset / characterBlockSize}")
  let skip := Syntax.mkNumLit (toString (offset % characterBlockSize))
  `(term| List.drop $skip $block)

def checkCharacterEquality (name : Ident) (left right : TSyntax `term) :
    CommandElabM Unit := do
  liftTermElabM do
    let type ← Term.elabType (← `(term| $left = $right))
    let rhs ← Term.elabTerm (← `(term| ($right : List Char))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let proof ← Meta.mkEqRefl (← instantiateMVars rhs)
    addDecl (.thmDecl { name := name.getId, levelParams := [], type, value := proof })
  let collected ← collectAxioms name.getId
  unless collected.isEmpty do
    throwError "invalid character equality certificate: {collected.toList}"

/-- Prove exact concatenation, including EOF, by composing checked segments.
Lengths only propose input cursors: the kernel checks every split against the
actual input. No length calculation or candidate renderer is trusted. -/
def certifyConcatenation (name : Name) (actual : Ident)
    (pieces : Array Ident) (lengths : Array Nat) : CommandElabM Ident := do
  unless pieces.size == lengths.size do throwError "missing adapter segment length"
  let mut splits : Array Ident := #[]
  let mut offsets : Array Nat := #[0]
  let mut offset := 0
  for i in [:pieces.size] do
    let piece := pieces[i]!
    let start ← remainingCharacters actual offset
    offset := offset + lengths[i]!
    let rest ← remainingCharacters actual offset
    let split := mkIdent (name.str s!"split_{i}")
    checkCharacterEquality split start (← `(term| $piece ++ $rest))
    splits := splits.push split
    offsets := offsets.push offset
  let last ← remainingCharacters actual offset
  let empty := mkIdent (name.str "empty")
  checkCharacterEquality empty last (← `(term| ([] : List Char)))
  let mut tail := mkIdent (name.str "pieces_end")
  let mut joined := mkIdent (name.str "joined_end")
  elabCommand (← `(command| def $tail:ident : List (List Char) := []))
  elabCommand (← `(command| theorem $joined:ident : ($tail).flatten = $last := Eq.symm $empty))
  for j in [:pieces.size] do
    let i := pieces.size - 1 - j
    let piece := pieces[i]!
    let split := splits[i]!
    let start ← remainingCharacters actual offsets[i]!
    let next := mkIdent (name.str s!"pieces_{i}")
    let nextEq := mkIdent (name.str s!"joined_{i}")
    elabCommand (← `(command| def $next:ident : List (List Char) := $piece :: $tail))
    elabCommand (← `(command| theorem $nextEq:ident : ($next).flatten = $start := by
      change $piece ++ ($tail).flatten = $start
      exact (congrArg (fun rest : List Char => $piece ++ rest) $joined).trans (Eq.symm $split)))
    tail := next
    joined := nextEq
  let collected ← collectAxioms joined.getId
  unless collected.isEmpty do
    throwError "invalid adapter concatenation certificate: {collected.toList}"
  return joined

private def typeProof (typedefs : TSyntax `term) : Nat → String → CommandElabM (TSyntax `term)
  | 0, _ => throwError "type spelling exceeds certificate budget"
  | fuel + 1, text => do
      if text.startsWith "const " then
        let tail := (text.drop 6).toString
        let proof ← typeProof typedefs fuel tail
        return ← `(term| CTree.Syntax.TypeSpelling.const $proof)
      if text.endsWith " *" then
        let tail := (text.dropEnd 2).toString
        let proof ← typeProof typedefs fuel tail
        return ← `(term| CTree.Syntax.TypeSpelling.pointer $proof)
      let name := Lean.Syntax.mkStrLit text
      if text ∈ ["void", "char", "int", "double"] then
        return ← `(term| (CTree.Syntax.TypeSpelling.named
          (.primitive (by decide +kernel)) : CTree.Syntax.TypeSpelling $typedefs $name))
      return ← `(term| (CTree.Syntax.TypeSpelling.named
        (.typedefName (by decide +kernel) (by decide +kernel)) : CTree.Syntax.TypeSpelling $typedefs $name))

def signatureProof (typedefs : TSyntax `term) (sig : CTree.Signature) :
    CommandElabM (TSyntax `term) := do
  let result ← typeProof typedefs (sig.result.length + 1) sig.result
  let mut parameters ← `(term| ((by intro param absent; cases absent) :
    ∀ param ∈ ([] : List CTree.Parameter), CTree.Printer.ParameterPrintable $typedefs param))
  for param in sig.parameters.reverse do
    let type ← typeProof typedefs (param.type.length + 1) param.type
    parameters ← `(term| List.forall_mem_cons.mpr ⟨⟨$type, by decide +kernel⟩, $parameters⟩)
  `(term| ⟨$result, by decide +kernel, $parameters⟩)

def signaturesProof (typedefs : TSyntax `term) (signatures : List CTree.Signature) :
    CommandElabM (TSyntax `term) := do
  let mut all ← `(term| ((by intro sig absent; cases absent) :
    ∀ sig ∈ ([] : List CTree.Signature), CTree.Printer.SignaturePrintable $typedefs sig))
  for sig in signatures.reverse do
    let proof ← signatureProof typedefs sig
    all ← `(term| List.forall_mem_cons.mpr ⟨$proof, $all⟩)
  return all

end Rumoca.CTree.Printer.Certificate

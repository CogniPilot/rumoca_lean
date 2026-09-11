import Rumoca.FMI3AdapterProofs
import Lean

/-! Kernel certificates for complete adapter bytes. Candidate signatures and
rendered chunks have no proof authority: each chunk is checked against its
function tree, and their concatenation against the independently read file.
The header collector is not claimed to implement the C header grammar. -/
namespace Rumoca.FMI3AdapterCertificate
open Lean Elab Command

-- Quotation proposes constructor trees only. The generated equality below is
-- checked by the kernel; neither this metaprogram nor native rendering is trusted.
deriving instance ToExpr for CTree.BinOp
deriving instance ToExpr for CTree.Expr
deriving instance ToExpr for CTree.Stmt
deriving instance ToExpr for CTree.Parameter
deriving instance ToExpr for CTree.Signature
deriving instance ToExpr for CTree.Function

private def characterBlockSize : Nat := 256

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
private def remainingCharacters (actual : Ident) (offset : Nat) : CommandElabM (TSyntax `term) := do
  let block := mkIdent (actual.getId.getPrefix.str s!"part_{offset / characterBlockSize}")
  let skip := Syntax.mkNumLit (toString (offset % characterBlockSize))
  `(term| List.drop $skip $block)

private def checkCharacterEquality (name : Ident) (left right : TSyntax `term) :
    CommandElabM Unit := do
  liftTermElabM do
    let type ← Term.elabType (← `(term| $left = $right))
    let rhs ← Term.elabTerm (← `(term| ($right : List Char))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let proof ← Meta.mkEqRefl (← instantiateMVars rhs)
    addDecl (.thmDecl { name := name.getId, levelParams := [], type, value := proof })
  let axioms ← collectAxioms name.getId
  unless axioms.isEmpty do
    throwError "invalid character equality certificate: {axioms.toList}"

/-- Prove exact concatenation, including EOF, by composing checked segments.
Lengths only propose input cursors: the kernel checks every split against the
actual input. No length calculation or candidate renderer is trusted. -/
private def certifyConcatenation (name : Name) (actual : Ident)
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
  let axioms ← collectAxioms joined.getId
  unless axioms.isEmpty do
    throwError "invalid adapter concatenation certificate: {axioms.toList}"
  return joined

private def quoteSignature (sig : CTree.Signature) : CommandElabM (TSyntax `term) := do
  let result := Syntax.mkStrLit sig.result
  let name := Syntax.mkStrLit sig.name
  let params ← sig.parameters.toArray.mapM fun p => do
    let type := Syntax.mkStrLit p.type
    let name := Syntax.mkStrLit p.name
    let array ← if p.array then `(term| true) else `(term| false)
    `(term| (⟨$type, $name, $array⟩ : CTree.Parameter))
  `(term| (⟨$result, $name, [$params,*]⟩ : CTree.Signature))

def certify (sourceFile source adapter : String) (sigs : List CTree.Signature)
    (actualChars : Ident) : CommandElabM Ident := do
  let .ok candidate := compile (.single sourceFile source) | throwError "source compilation failed"
  let prepared := candidate.solve.prepareFMI3
  if FMI3.Runtime.render prepared sigs != adapter then
    throwError "actual FMI adapter differs from the complete prepared function list"
  let base := `Rumoca.CheckedFMI3Files.adapter
  let src := Syntax.mkStrLit source
  let file := Syntax.mkStrLit sourceFile
  let input ← `(term| Parser.Source.InputRef.single $file $src)
  let model := mkIdent (base.str "model")
  let parsed := mkIdent (base.str "parsed")
  let artifact := mkIdent (base.str "artifact")
  let compiled := mkIdent (base.str "compiled")
  let name := Syntax.mkStrLit candidate.parsed.ast.name
  let state := Syntax.mkStrLit candidate.parsed.ast.state
  let derivative := Syntax.mkStrLit candidate.parsed.ast.derivativeName
  let ending := Syntax.mkStrLit candidate.parsed.ast.endName
  elabCommand (← `(command| def $model:ident : AST.Model := ⟨$name, $state, $derivative, $ending⟩))
  elabCommand (← `(command| def $parsed:ident : Parsed $src :=
    ⟨($model).tokens, $model, by rfl, parseTokens_complete $model⟩))
  elabCommand (← `(command| def $artifact:ident : Artifact $input :=
    Artifact.ofParsed $input $parsed ⟨by decide +kernel, by decide +kernel⟩))
  elabCommand (← `(command| theorem $compiled:ident : compile $input = .ok $artifact :=
    compile_eq_parsed $input $parsed _))
  let sigTerms ← sigs.toArray.mapM quoteSignature
  let signatures := mkIdent (base.str "signatures")
  elabCommand (← `(command| def $signatures:ident : List CTree.Signature := [$sigTerms,*]))
  let m ← `(term| ($artifact).solve.prepareFMI3)
  let preamble ← `(term| FMI3.functionPrefix ($m).name ++ "#include \"model.c\"\n" ++ FMI3.Runtime.declarations)
  let preambleText := FMI3.functionPrefix prepared.name ++ "#include \"model.c\"\n" ++ FMI3.Runtime.declarations
  let preambleChars ← quoteCharacters (base.str "preamble") preambleText
  let preambleEq := mkIdent (base.str "preamble_bytes")
  elabCommand (← `(command| theorem $preambleEq:ident : ($preamble).toList = $preambleChars := by
    decide +kernel))
  let mut fnTerms : Array (TSyntax `term) := #[]
  for i in [:FMI3.Runtime.helpers.length] do
    let index := Syntax.mkNumLit (toString i)
    fnTerms := fnTerms.push (← `(term| FMI3.Runtime.helpers[$index]'(by decide +kernel)))
  for sig in sigTerms do
    fnTerms := fnTerms.push (← `(term| FMI3.Runtime.function $m $sig))
  let functions := (FMI3.LiteralPreparation.functions prepared sigs).toArray
  let mut chunks : Array Ident := #[]
  let mut equations : Array Ident := #[]
  for i in [:functions.size] do
    let fn := fnTerms[i]!
    let some function := functions[i]? | throwError "missing prepared adapter function"
    let tree := mkIdent (base.str s!"function_{i}_tree")
    let quoted ← liftTermElabM <| PrettyPrinter.delab (toExpr function)
    elabCommand (← `(command| def $tree:ident : CTree.Function := $quoted))
    let treeEq := mkIdent (base.str s!"function_{i}_tree_eq")
    -- Ask Lean's kernel to check reflexivity directly. The elaborator's `rfl`
    -- reduction stops at string-pattern routing in some Runtime.body branches.
    -- addDecl checks a theorem body; it does not create an axiom or trust the
    -- native tree value. This uses the same kernel path as `decide +kernel`.
    liftTermElabM do
      let type ← Term.elabType (← `(term| $fn = $tree))
      Term.synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars type
      let proof ← Meta.mkEqRefl (mkConst tree.getId)
      addDecl (.thmDecl { name := treeEq.getId, levelParams := [], type, value := proof })
    let treeAxioms ← collectAxioms treeEq.getId
    for dependency in treeAxioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "invalid tree certificate for {function.signature.name}: {dependency}"
    let chars ← quoteCharacters (base.str s!"function_{i}") function.render
    let checked := mkIdent (base.str s!"function_{i}_bytes")
    -- Distribute characters over joins before kernel reduction. Evaluating a
    -- whole rendered String here creates much larger intermediate terms.
    elabCommand (← `(command|
      set_option linter.unusedSimpArgs false in
      theorem $checked:ident : ($fn).render.toList = $chars := by
        rw [$treeEq:ident]
        simp only [$tree:ident,
          CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
          CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render,
          List.map_cons, List.map_nil, CString.join_toList, String.toList_append,
          String.toList_ofList, List.flatMap_cons, List.flatMap_nil] <;>
          decide +kernel))
    let axioms ← collectAxioms checked.getId
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "invalid printer certificate for {function.signature.name}: {dependency}"
    chunks := chunks.push chars
    equations := equations.push checked
  let chunkList ← `(term| [$chunks,*])
  let matched := mkIdent (base.str "functions_matched")
  let mut pairProof ← `(term| List.Forall₂.nil)
  for i in [:equations.size] do
    let equation := equations[equations.size - 1 - i]!
    pairProof ← `(term| List.Forall₂.cons $equation $pairProof)
  elabCommand (← `(command| theorem $matched:ident :
    List.Forall₂ (fun fn chars => fn.render.toList = chars)
      (FMI3.LiteralPreparation.functions $m $signatures) $chunkList := $pairProof))
  let completeBytes := mkIdent (base.str "complete_bytes")
  let concatenated ← certifyConcatenation (base.str "assembly") actualChars
    (#[preambleChars] ++ chunks)
    (#[preambleText.toList.length] ++ functions.map (fun fn => fn.render.toList.length))
  elabCommand (← `(command| theorem $completeBytes:ident :
    $preambleChars ++ ($chunkList).flatten = $actualChars := $concatenated))
  let rendered := mkIdent (base.str "rendered")
  elabCommand (← `(command| theorem $rendered:ident :
    FMI3.Runtime.render $m $signatures = String.ofList $actualChars :=
      FMI3.adapter_chars $m $signatures $preambleChars $chunkList $actualChars
        $preambleEq $matched $completeBytes))
  let theoremId := mkIdent (base.str "contract")
  elabCommand (← `(command| theorem $theoremId:ident (a : Artifact $input)
    (accepted : compile $input = .ok a) : FMI3.AdapterContract a (String.ofList $actualChars) := by
      have same : a = $artifact := Except.ok.inj (accepted.symm.trans $compiled)
      subst a
      apply FMI3.adapter_correct $artifact $signatures
      · decide +kernel
      · change FMI3.Reset.signature ∈ [$sigTerms,*]
        simp [FMI3.Reset.signature]
      · exact $rendered))
  return theoremId

end Rumoca.FMI3AdapterCertificate

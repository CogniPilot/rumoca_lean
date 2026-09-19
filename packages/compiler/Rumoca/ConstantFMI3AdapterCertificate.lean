import Rumoca.FMI3AdapterCertificate
import Rumoca.ConstantProduction
import Rumoca.ConstantAdapterChars
import RumocaFMI3.ConstantAdapterContract
import RumocaFMI3.PublicAPICertificate

/-! Kernel certificate for the complete constant-rate adapter bytes, the constant
analog of `Rumoca.TensorFMI3AdapterCertificate.certify`, generalized over the
constant function list. Candidate signatures and rendered chunks have no proof
authority: each chunk is checked against its constant function tree, their
concatenation against the independently read file, and the render-to-contract
step is discharged by `ConstantAdapter.render_contract`. -/
namespace Rumoca.ConstantFMI3AdapterCertificate
open Lean Elab Command
open Rumoca.FMI3AdapterCertificate (quoteCharacters quoteSignature certifyConcatenation)
open Rumoca.FMI3

/-- Emit the constant adapter contract for the actual bytes: build the scalar
witness artifact, kernel-check every emitted constant function against its tree,
join the character chunks and bind them to the independently read file, then
discharge `ConstantAdapter.render_contract`. Returns the identifier of a proof of
`∀ [static], ConstantAdapter.Contract witnessModel Rumoca.constantRatesModel (String.ofList actualChars)`
together with the reconstructed scalar witness artifact identifier. -/
def certify (adapter : String) (sigs : List CTree.Signature) (actualChars : Ident) :
    CommandElabM (Ident × Ident) := do
  -- The synthetic scalar witness source carries the constant model name.
  let witnessName := "ConstantRates"
  let scalarSource := "model " ++ witnessName ++ " Real x; equation der(x) = 1; end " ++ witnessName ++ ";"
  let witnessFile := "rumoca-constant-witness:/scalar.mo"
  let .ok witness := compile (.single witnessFile scalarSource)
    | throwError "scalar witness compilation failed"
  let witnessModelVal := witness.solve.prepareFMI3
  let m := Rumoca.constantRatesModel
  if ConstantFunctions.render witnessModelVal m sigs != adapter then
    throwError "actual constant FMI adapter differs from the complete prepared function list"
  let base := `Rumoca.CheckedConstantFMI3Files.adapter
  let src := Syntax.mkStrLit scalarSource
  let file := Syntax.mkStrLit witnessFile
  let input ← `(term| Parser.Source.InputRef.single $file $src)
  let model := mkIdent (base.str "model")
  let parsed := mkIdent (base.str "parsed")
  let artifact := mkIdent (base.str "artifact")
  let compiled := mkIdent (base.str "compiled")
  let name := Syntax.mkStrLit witness.parsed.ast.name
  let state := Syntax.mkStrLit witness.parsed.ast.state
  let derivative := Syntax.mkStrLit witness.parsed.ast.derivativeName
  let ending := Syntax.mkStrLit witness.parsed.ast.endName
  elabCommand (← `(command| def $model:ident : AST.Model := ⟨$name, $state, $derivative, $ending⟩))
  elabCommand (← `(command| def $parsed:ident : Parsed $src :=
    ⟨($model).tokens, $model, by rfl, parseTokens_complete $model⟩))
  elabCommand (← `(command| def $artifact:ident : Artifact $input :=
    Artifact.ofParsed $input $parsed ⟨by decide +kernel, by decide +kernel⟩))
  elabCommand (← `(command| theorem $compiled:ident : compile $input = .ok $artifact :=
    compile_eq_parsed $input $parsed _))
  let witnessModel ← `(term| ($artifact).solve.prepareFMI3)
  -- The pinned constant model whose render the actual bytes must equal.
  let mTerm ← `(term| Rumoca.constantRatesModel)
  -- Quoted signature list, shared with the coverage/membership premises.
  let sigTerms ← sigs.toArray.mapM quoteSignature
  let signatures := mkIdent (base.str "signatures")
  elabCommand (← `(command| def $signatures:ident : List CTree.Signature := [$sigTerms,*]))
  -- Native constant function list; each function is checked against its tree.
  let functions := (ConstantFunctions.functions witnessModelVal m sigs).toArray
  let mut fnTerms : Array (TSyntax `term) := #[]
  for i in [:ConstantFunctions.helpers.length] do
    let index := Syntax.mkNumLit (toString i)
    fnTerms := fnTerms.push (← `(term| FMI3.ConstantFunctions.helpers[$index]'(by decide +kernel)))
  for sig in sigTerms do
    fnTerms := fnTerms.push (← `(term| FMI3.ConstantFunctions.constantFunction $witnessModel $mTerm $sig))
  let mut chunks : Array Ident := #[]
  let mut equations : Array Ident := #[]
  for i in [:functions.size] do
    let fn := fnTerms[i]!
    let some function := functions[i]? | throwError "missing prepared constant adapter function"
    let tree := mkIdent (base.str s!"function_{i}_tree")
    let quoted ← liftTermElabM <| PrettyPrinter.delab (toExpr function)
    elabCommand (← `(command| def $tree:ident : CTree.Function := $quoted))
    let treeEq := mkIdent (base.str s!"function_{i}_tree_eq")
    liftTermElabM do
      let type ← Term.elabType (← `(term| $fn = $tree))
      Term.synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars type
      let proof ← Meta.mkEqRefl (mkConst tree.getId)
      addDecl (.thmDecl { name := treeEq.getId, levelParams := [], type, value := proof })
    let treeAxioms ← collectAxioms treeEq.getId
    for dependency in treeAxioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "invalid constant tree certificate for {function.signature.name}: {dependency}"
    let chars ← quoteCharacters (base.str s!"function_{i}") function.render
    let checked := mkIdent (base.str s!"function_{i}_bytes")
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
    let collected ← collectAxioms checked.getId
    for dependency in collected do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "invalid constant printer certificate for {function.signature.name}: {dependency}"
    chunks := chunks.push chars
    equations := equations.push checked
  -- Every emitted function's bytes are the joined chunk list, in order.
  let chunkList ← `(term| [$chunks,*])
  let matched := mkIdent (base.str "functions_matched")
  let mut pairProof ← `(term| List.Forall₂.nil)
  for i in [:equations.size] do
    let equation := equations[equations.size - 1 - i]!
    pairProof ← `(term| List.Forall₂.cons $equation $pairProof)
  elabCommand (← `(command| theorem $matched:ident :
    List.Forall₂ (fun fn chars => fn.render.toList = chars)
      (FMI3.ConstantFunctions.functions $witnessModel $mTerm $signatures) $chunkList := $pairProof))
  -- The fixed declaration preamble bytes.
  let preambleText := functionPrefix m.name ++ "#include \"model.c\"\n" ++
    ConstantFunctions.declarations m.shape (ConstantFunctions.rates m)
  let preambleChars ← quoteCharacters (base.str "preamble") preambleText
  let preambleEq := mkIdent (base.str "preamble_bytes")
  elabCommand (← `(command| theorem $preambleEq:ident :
    (FMI3.functionPrefix ($mTerm).name ++ "#include \"model.c\"\n" ++
      FMI3.ConstantFunctions.declarations ($mTerm).shape
        (FMI3.ConstantFunctions.rates $mTerm)).toList = $preambleChars := by decide +kernel))
  -- The complete file is the preamble followed by the joined function chunks.
  let concatenated ← certifyConcatenation (base.str "assembly") actualChars
    (#[preambleChars] ++ chunks)
    (#[preambleText.toList.length] ++ functions.map (fun fn => fn.render.toList.length))
  let completeBytes := mkIdent (base.str "complete_bytes")
  elabCommand (← `(command| theorem $completeBytes:ident :
    $preambleChars ++ ($chunkList).flatten = $actualChars := $concatenated))
  -- The render equals the independently read file.
  let rendered := mkIdent (base.str "rendered")
  elabCommand (← `(command| theorem $rendered:ident :
    FMI3.ConstantFunctions.render $witnessModel $mTerm $signatures = String.ofList $actualChars :=
      FMI3.ConstantFunctions.constant_adapter_chars $witnessModel $mTerm $signatures
        $preambleChars $chunkList $actualChars $preambleEq $matched $completeBytes))
  -- Discharge the render contract premises over the pinned signature list.
  let contract := mkIdent (base.str "contract")
  elabCommand (← `(command|
    theorem $contract:ident : ∀ [FMI3.StaticLiterals],
        FMI3.ConstantAdapter.Contract $witnessModel $mTerm (String.ofList $actualChars) := by
      intro static
      rw [← $rendered:ident]
      refine FMI3.ConstantAdapter.render_contract $witnessModel $mTerm $signatures ?_ ?_ ?_ ?_
      · rw [FMI3.ConstantFunctions.functions_names]; decide +kernel
      · change FMI3.PublicAPI.Covered [$sigTerms,*]
        fmi_public_coverage
      · intro ty write
        cases ty <;> cases write <;> change FMI3.AbsentVariables.signature _ _ ∈ [$sigTerms,*]
        all_goals simp [FMI3.AbsentVariables.signature, FMI3.AbsentVariables.VariableType.name,
          FMI3.AbsentVariables.VariableType.hasSizes]
      · change ∀ sig ∈ FMI3.CapabilityRejection.signatures, sig ∈ [$sigTerms,*]
        simp [FMI3.CapabilityRejection.signatures]))
  return (contract, artifact)

end Rumoca.ConstantFMI3AdapterCertificate

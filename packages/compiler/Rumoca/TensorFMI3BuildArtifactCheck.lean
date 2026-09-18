import Rumoca.TensorProduction
import Rumoca.TensorFMI3AdapterCertificate
import Rumoca.CertificateOptions
import RumocaFMI3.Header
import RumocaFMI3.BuildDescriptionProofs
import RumocaFMI3.TensorMetadata
import XML.CertificateCheck

/-! Fixed actual-file adapter for the development tensor source-build profile.
The adapter independently reads all five staged files, compiles the source with
`compileTensor`, and checks a fixed proposition. Preliminary comparisons only
reject; candidate data is never proof authority. -/

register_option rumoca.tensorFmi3.root : String :=
  { defValue := "", descr := "Prepared tensor FMI 3 directory containing sources and source snapshot" }

namespace Rumoca.TensorFMI3BuildArtifactCheck
open Lean Elab Command
open Rumoca.FMI3AdapterCertificate (quoteCharacters certifyConcatenation)
open Rumoca Rumoca.FMI3 Rumoca.CTensor

/-- Kernel-check one `model.c` fragment against its rendered bytes by reflexivity.
Unlike the pure-character equalities of the concatenation splits, a rendered
fragment's type references the certified kernel definitions, which carry the
three approved foundational axioms; the proof term itself is still `Eq.refl`. -/
def checkPieceEquality (name : Ident) (left right : TSyntax `term) : CommandElabM Unit := do
  liftTermElabM do
    let type ← Term.elabType (← `(term| $left = $right))
    let rhs ← Term.elabTerm (← `(term| ($right : List Char))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let proof ← Meta.mkEqRefl (← instantiateMVars rhs)
    addDecl (.thmDecl { name := name.getId, levelParams := [], type, value := proof })
  let collected ← collectAxioms name.getId
  for dependency in collected do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "invalid tensor kernel fragment certificate: {dependency}"

elab "verify_tensor_fmi3_build_files" : command => do
  let directory := rumoca.tensorFmi3.root.get (← getOptions)
  if directory.isEmpty then throwError "missing rumoca.tensorFmi3.root"
  let root : System.FilePath := directory
  let sourcePath := root / "extra/org.cognipilot.rumoca/Source.mo"
  let sourceName := CertificateOptions.sourceName (← getOptions) sourcePath.toString
  let source ← IO.FS.readFile sourcePath
  let modelC ← IO.FS.readFile (root / "sources/model.c")
  let adapter ← IO.FS.readFile (root / "sources/fmi3.c")
  let description ← IO.FS.readFile (root / "sources/buildDescription.xml")
  let metadata ← IO.FS.readFile (root / "modelDescription.xml")
  let grammar ← IO.FS.readFile "packages/modelica-parser/grammar/Modelica.ebnf"
  if grammar != Generated.source then
    throwError "actual EBNF source differs from the certified grammar"
  let input : Parser.Source.InputRef := .single sourceName source
  let .ok candidate := compileTensor input | throwError "tensor source compilation failed"
  let modelName := candidate.name
  let buildTree := FMI3.Build.description modelName
  let metadataTree := FMI3.TensorMetadata.modelDescription candidate.tensorModel
  -- Preliminary rejections against the prepared documents and certified kernel.
  if description != XML.document buildTree then
    throwError "actual tensor FMI build description differs from the required source-build profile"
  if metadata != XML.document metadataTree then
    throwError "actual tensor FMI model description differs from the prepared model"
  if modelC != TensorKernel.modelC then
    throwError "actual tensor model.c differs from the certified tensor kernel text"
  let expectedPrefix := FMI3.functionPrefix modelName ++ "#include \"model.c\"\n"
  if !adapter.startsWith expectedPrefix then
    throwError "actual tensor FMI source prefix or private-kernel inclusion differs from its model identifier"
  -- The pinned header signature list.
  let header ← IO.FS.readFile "packages/backend-fmi3/vendor/fmi3/fmi3FunctionTypes.h"
  let .ok signatures := FMI3.Header.signatures header | throwError "invalid FMI signature header"
  -- Build description XML certificate.
  let buildTreeId := mkIdent `Rumoca.CheckedTensorFMI3Files.build_tree
  let buildBytesId := mkIdent `Rumoca.CheckedTensorFMI3Files.build_bytes
  XML.CertificateCheck.certify buildTreeId.getId buildBytesId.getId buildTree description
  let nameLit := Syntax.mkStrLit modelName
  let buildTreeEq := mkIdent `Rumoca.CheckedTensorFMI3Files.build_tree_eq
  elabCommand (← `(command|
    theorem $buildTreeEq:ident : FMI3.Build.description $nameLit = $buildTreeId := by rfl))
  -- Model description XML certificate and validity.
  let mdTreeId := mkIdent `Rumoca.CheckedTensorFMI3Files.metadata_tree
  let mdBytesId := mkIdent `Rumoca.CheckedTensorFMI3Files.metadata_bytes
  XML.CertificateCheck.certify mdTreeId.getId mdBytesId.getId metadataTree metadata
  XML.CertificateCheck.certifyValidity mdTreeId.getId metadataTree
  let mdValid := mkIdent (mdTreeId.getId.str "valid_eq")
  let preparedMd := mkIdent `Rumoca.CheckedTensorFMI3Files.prepared_metadata
  elabCommand (← `(command|
    theorem $preparedMd:ident : FMI3.TensorMetadata.modelDescription Rumoca.squareModel = $mdTreeId := by rfl))
  -- Adapter byte + contract certificate.
  let adapterChars ← quoteCharacters `Rumoca.CheckedTensorFMI3Files.adapter_chars adapter
  let (adapterContract, adapterArtifact) ←
    TensorFMI3AdapterCertificate.certify adapter signatures adapterChars
  -- model.c byte certificate. The first fragment is a fixed string literal; the
  -- eight render fragments are each a reachable `CTree.Function`'s render, checked
  -- against its independently delaborated tree exactly as the adapter functions.
  let base := `Rumoca.CheckedTensorFMI3Files
  let renderFuncTerms : Array (TSyntax `term) := #[
    ← `(term| Rumoca.CTensor.Fill.function),
    ← `(term| (Rumoca.CTensor.function Rumoca.Tensor.BinaryOp.add)),
    ← `(term| (Rumoca.CTensor.function Rumoca.Tensor.BinaryOp.mul)),
    ← `(term| Rumoca.CTensor.Diagonal.function),
    ← `(term| (Rumoca.CTensor.ProgramFixture.IVPEntry.plan Rumoca.ArrayProfile.stateShape).initial.function.tree),
    ← `(term| (Rumoca.CTensor.ProgramFixture.IVPEntry.plan Rumoca.ArrayProfile.stateShape).derivative.function.tree),
    ← `(term| Rumoca.CTensor.ProgramFixture.DiagonalEntry.profile.tree),
    ← `(term| Rumoca.CTensor.SquareDiagonal.function)]
  let renderFuncVals : Array CTree.Function := #[
    Fill.function, function .add, function .mul, Diagonal.function,
    (ProgramFixture.IVPEntry.plan ArrayProfile.stateShape).initial.function.tree,
    (ProgramFixture.IVPEntry.plan ArrayProfile.stateShape).derivative.function.tree,
    ProgramFixture.DiagonalEntry.profile.tree,
    SquareDiagonal.function]
  let modelChars ← quoteCharacters (base.str "model_chars") modelC
  let mut pieceCharIdents : Array Ident := #[]
  let mut pieceEqs : Array Ident := #[]
  let mut pieceLengths : Array Nat := #[]
  -- Fragment 0: the fixed `#include <stddef.h>` header line.
  let literalPiece := "#include <stddef.h>\n"
  let chars0 ← quoteCharacters (base.str "piece_0") literalPiece
  let eq0 := mkIdent (base.str "piece_0_eq")
  checkPieceEquality eq0 (← `(term| ("#include <stddef.h>\n").toList)) (← `(term| $chars0))
  pieceCharIdents := pieceCharIdents.push chars0
  pieceEqs := pieceEqs.push eq0
  pieceLengths := pieceLengths.push literalPiece.toList.length
  -- Fragments 1..8: the certified render fragments.
  for j in [:renderFuncTerms.size] do
    let i := j + 1
    let funcTerm := renderFuncTerms[j]!
    let some funcVal := renderFuncVals[j]? | throwError "missing tensor kernel fragment function"
    let chars ← quoteCharacters (base.str s!"piece_{i}") funcVal.render
    let tree := mkIdent (base.str s!"piece_{i}_tree")
    let quoted ← liftTermElabM <| PrettyPrinter.delab (toExpr funcVal)
    elabCommand (← `(command| def $tree:ident : CTree.Function := $quoted))
    let treeEq := mkIdent (base.str s!"piece_{i}_tree_eq")
    liftTermElabM do
      let type ← Term.elabType (← `(term| $funcTerm = $tree))
      Term.synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars type
      let proof ← Meta.mkEqRefl (mkConst tree.getId)
      addDecl (.thmDecl { name := treeEq.getId, levelParams := [], type, value := proof })
    let treeAxioms ← collectAxioms treeEq.getId
    for dependency in treeAxioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "invalid tensor kernel fragment tree certificate: {dependency}"
    let eqName := mkIdent (base.str s!"piece_{i}_eq")
    elabCommand (← `(command|
      set_option linter.unusedSimpArgs false in
      theorem $eqName:ident : ($funcTerm).render.toList = $chars := by
        rw [$treeEq:ident]
        simp only [$tree:ident,
          CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
          CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render,
          List.map_cons, List.map_nil, CString.join_toList, String.toList_append,
          String.toList_ofList, List.flatMap_cons, List.flatMap_nil] <;>
          decide +kernel))
    let collected ← collectAxioms eqName.getId
    for dependency in collected do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "invalid tensor kernel fragment certificate: {dependency}"
    pieceCharIdents := pieceCharIdents.push chars
    pieceEqs := pieceEqs.push eqName
    pieceLengths := pieceLengths.push funcVal.render.toList.length
  let chunkList ← `(term| [$pieceCharIdents,*])
  let matched := mkIdent `Rumoca.CheckedTensorFMI3Files.model_matched
  let mut pairProof ← `(term| List.Forall₂.nil)
  for i in [:pieceEqs.size] do
    let equation := pieceEqs[pieceEqs.size - 1 - i]!
    pairProof ← `(term| List.Forall₂.cons $equation $pairProof)
  elabCommand (← `(command| theorem $matched:ident :
    List.Forall₂ (fun s chars => s.toList = chars) Rumoca.TensorKernel.pieces $chunkList := $pairProof))
  let modelConcat ← certifyConcatenation `Rumoca.CheckedTensorFMI3Files.model_assembly modelChars
    pieceCharIdents pieceLengths
  let modelBytes := mkIdent `Rumoca.CheckedTensorFMI3Files.model_complete_bytes
  elabCommand (← `(command| theorem $modelBytes:ident :
    ($chunkList).flatten = $modelChars := $modelConcat))
  let modelEq := mkIdent `Rumoca.CheckedTensorFMI3Files.model_c_eq
  elabCommand (← `(command| theorem $modelEq:ident :
    Rumoca.TensorKernel.modelC = String.ofList $modelChars :=
      Rumoca.TensorKernel.chars $chunkList $modelChars $matched $modelBytes))
  -- Assemble the composed source-to-build contract.
  let src := Syntax.mkStrLit source
  let sourceFile := Syntax.mkStrLit sourceName
  let inputTerm ← `(term| Parser.Source.InputRef.single $sourceFile $src)
  let ebnf := Syntax.mkStrLit grammar
  let buildLit := Syntax.mkStrLit description
  let mdLit := Syntax.mkStrLit metadata
  let theoremName := `Rumoca.CheckedTensorFMI3Files.source_to_build
  let theoremId := mkIdent theoremName
  elabCommand (← `(command|
    theorem $theoremId:ident : Generated.source = $ebnf ∧
        ∃ a : Rumoca.TensorArtifact $inputTerm, Rumoca.compileTensor $inputTerm = .ok a ∧
          Rumoca.TensorSourceBuildContract a (String.ofList $modelChars) $buildLit
            (String.ofList $adapterChars) $mdLit := by
      refine ⟨by rfl, ?_⟩
      let parsed : Rumoca.ArrayProfile.Parsed $src :=
        ⟨Rumoca.squareAst.tokens, Rumoca.squareAst, by rfl,
          Rumoca.ParserActions.parseTokens_complete Rumoca.ArrayProfile.actions Rumoca.squareAst⟩
      let a : Rumoca.TensorArtifact $inputTerm :=
        Rumoca.TensorArtifact.ofParsed $inputTerm parsed Rumoca.squareAst_resolved
      have hc : Rumoca.compileTensor $inputTerm = .ok a :=
        Rumoca.compileTensor_eq_parsed $inputTerm parsed Rumoca.squareAst_resolved
      refine ⟨a, hc, ?_⟩
      have hast : a.prepared.parsed.parsed.ast = Rumoca.squareAst := rfl
      have hmodel : a.tensorModel = Rumoca.squareModel := Rumoca.TensorArtifact.tensorModel_square a hast
      have hname : a.name = "TensorSquare" := Rumoca.TensorArtifact.name_square a hast
      refine Rumoca.tensorSourceBuild_correct a (String.ofList $modelChars) $buildLit
        (String.ofList $adapterChars) $mdLit ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact ($modelEq:ident).symm
      · exact Rumoca.CTensor.ProgramFixture.IVPEntry.artifact_correct _ _ rfl rfl
      · rw [hname, ← (congrArg XML.document $buildTreeEq:ident).trans $buildBytesId:ident]
        exact FMI3.Build.artifact_correct "TensorSquare"
          ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
      · rw [hmodel, hname]
        exact ⟨($adapterArtifact).parsed.ast, ($adapterArtifact).solve.prepareFMI3, rfl, $adapterContract⟩
      · rw [hmodel, hname]
        exact FMI3.TensorMetadata.modelIdentifiers_decode Rumoca.squareModel
      · rw [hmodel]
        exact FMI3.TensorMetadata.token_attribute Rumoca.squareModel
      · rw [hmodel, $preparedMd:ident, ← $mdBytesId:ident]
        exact XML.document_correct $mdTreeId $mdValid:ident))
  let axioms ← collectAxioms theoremName
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in tensor FMI source-build contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {axioms.toList}"

end Rumoca.TensorFMI3BuildArtifactCheck

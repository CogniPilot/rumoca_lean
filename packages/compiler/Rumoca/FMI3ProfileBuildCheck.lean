import RumocaC.PrinterCertificate
import Rumoca.FMI3AdapterCertificate
import Rumoca.CertificateOptions
import RumocaFMI3.Header
import RumocaFMI3.BuildDescriptionProofs
import RumocaFMI3.TensorMetadata
import XML.CertificateCheck

/-! Shared actual-file build-artifact driver for the source-build FMI 3 profiles
that carry a private numerical `model.c` kernel (the tensor and constant-rate
profiles). The driver independently reads all five staged files, checks the
build description, model description, private kernel text and adapter prefix
against the compiler output, certifies the `model.c` byte assembly and the
adapter bytes, and composes the fixed `source_to_build` contract. Preliminary
comparisons only reject; candidate data is never proof authority. Each profile
supplies its compilation, its metadata and kernel identity, its `model.c`
render fragments and its final contract proof through `ProfileBuildInputs`. -/

namespace Rumoca.FMI3ProfileBuildCheck
open Lean Elab Command
open Rumoca.CTree.Printer.Certificate (quoteCharacters certifyConcatenation)
open Rumoca Rumoca.FMI3

/-- Kernel-check one `model.c` fragment against its rendered bytes by reflexivity.
Unlike the pure-character equalities of the concatenation splits, a rendered
fragment's type references the certified kernel definitions, which carry the
three approved foundational axioms; the proof term itself is still `Eq.refl`. The
`label` names the profile in the rejection diagnostic. -/
def checkPieceEquality (label : String) (name : Ident) (left right : TSyntax `term) :
    CommandElabM Unit := do
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
      throwError "invalid {label} kernel fragment certificate: {dependency}"

/-- The shared certificate identifiers the profile-specific `source_to_build`
proof consumes. The driver creates them; each profile's `emitFinal` splices them
into its fixed contract statement and proof. -/
structure FinalContext where
  inputTerm : TSyntax `term
  src : TSyntax `term
  sourceFile : TSyntax `term
  ebnf : TSyntax `term
  buildLit : TSyntax `term
  mdLit : TSyntax `term
  modelChars : Ident
  adapterChars : Ident
  modelEq : Ident
  buildTreeEq : Ident
  buildBytesId : Ident
  preparedMd : Ident
  mdTreeId : Ident
  mdBytesId : Ident
  mdValid : Ident
  adapterContract : Ident
  adapterArtifact : Ident

/-- Per-profile inputs to the shared driver. The base scalar FMI 3 profile is not
driven here: it certifies its compiled scalar source directly through
`ArtifactCheck.check` and `Rumoca.CheckedFiles.source_to_c` and carries no private
`model.c` render assembly. -/
structure ProfileBuildInputs where
  /-- Profile label used in the rejection diagnostics, e.g. `"tensor"`. -/
  label : String
  /-- Prepared directory holding the staged sources and source snapshot. -/
  root : System.FilePath
  /-- Checked-namespace base, e.g. `` `Rumoca.CheckedTensorFMI3Files ``. -/
  base : Name
  /-- Compile the independently read source, returning the model name, the
  prepared model-description tree, and the certified private kernel `model.c`
  bytes, or throwing the profile's compilation-failure diagnostic. -/
  compileProfile : Parser.Source.InputRef → CommandElabM (String × XML.Element × String)
  /-- Left-hand side of the prepared-metadata reflexivity theorem. -/
  preparedMdLhs : TSyntax `term
  /-- Adapter-bytes certificate; returns the contract and reconstructed witness
  artifact identifiers. -/
  adapterCertify : String → List CTree.Signature → Ident → CommandElabM (Ident × Ident)
  /-- Fixed `model.c` fragment 0 bytes and its `.toList` reference term. -/
  literalPiece : String
  literalPieceTerm : TSyntax `term
  /-- The remaining `model.c` render fragments: reference terms and the certified
  function values they delaborate to. -/
  renderFuncTerms : Array (TSyntax `term)
  renderFuncVals : Array CTree.Function
  /-- The profile kernel's `pieces`, `modelC` and `chars` terms. -/
  kernelPiecesTerm : TSyntax `term
  kernelModelCTerm : TSyntax `term
  kernelCharsTerm : TSyntax `term
  /-- Emit the fixed `source_to_build` contract for this profile. -/
  emitFinal : Ident → FinalContext → CommandElabM Unit

/-- Run the shared actual-file build-artifact check for one profile. -/
def run (p : ProfileBuildInputs) : CommandElabM Unit := do
  let root : System.FilePath := p.root
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
  let (modelName, metadataTree, kernelModelC) ← p.compileProfile input
  let buildTree := FMI3.Build.description modelName
  -- Preliminary rejections against the prepared documents and certified kernel.
  if description != XML.document buildTree then
    throwError "actual {p.label} FMI build description differs from the required source-build profile"
  if metadata != XML.document metadataTree then
    throwError "actual {p.label} FMI model description differs from the prepared model"
  if modelC != kernelModelC then
    throwError "actual {p.label} model.c differs from the certified {p.label} kernel text"
  let expectedPrefix := FMI3.functionPrefix modelName ++ "#include \"model.c\"\n"
  if !adapter.startsWith expectedPrefix then
    throwError "actual {p.label} FMI source prefix or private-kernel inclusion differs from its model identifier"
  -- The pinned header signature list.
  let header ← IO.FS.readFile "packages/backend-fmi3/vendor/fmi3/fmi3FunctionTypes.h"
  let .ok signatures := FMI3.Header.signatures header | throwError "invalid FMI signature header"
  -- Build description XML certificate.
  let buildTreeId := mkIdent (p.base.str "build_tree")
  let buildBytesId := mkIdent (p.base.str "build_bytes")
  XML.CertificateCheck.certify buildTreeId.getId buildBytesId.getId buildTree description
  let nameLit := Syntax.mkStrLit modelName
  let buildTreeEq := mkIdent (p.base.str "build_tree_eq")
  elabCommand (← `(command|
    theorem $buildTreeEq:ident : FMI3.Build.description $nameLit = $buildTreeId := by rfl))
  -- Model description XML certificate and validity.
  let mdTreeId := mkIdent (p.base.str "metadata_tree")
  let mdBytesId := mkIdent (p.base.str "metadata_bytes")
  XML.CertificateCheck.certify mdTreeId.getId mdBytesId.getId metadataTree metadata
  XML.CertificateCheck.certifyValidity mdTreeId.getId metadataTree
  let mdValid := mkIdent (mdTreeId.getId.str "valid_eq")
  let preparedMd := mkIdent (p.base.str "prepared_metadata")
  elabCommand (← `(command|
    theorem $preparedMd:ident : $(p.preparedMdLhs) = $mdTreeId := by rfl))
  -- Adapter byte + contract certificate.
  let adapterChars ← quoteCharacters (p.base.str "adapter_chars") adapter
  let (adapterContract, adapterArtifact) ← p.adapterCertify adapter signatures adapterChars
  -- model.c byte certificate. Fragment 0 is a fixed string literal; the render
  -- fragments are each a reachable `CTree.Function`'s render, checked against its
  -- independently delaborated tree exactly as the adapter functions.
  let base := p.base
  let renderFuncTerms := p.renderFuncTerms
  let renderFuncVals := p.renderFuncVals
  let modelChars ← quoteCharacters (base.str "model_chars") modelC
  let mut pieceCharIdents : Array Ident := #[]
  let mut pieceEqs : Array Ident := #[]
  let mut pieceLengths : Array Nat := #[]
  -- Fragment 0: the fixed literal preamble.
  let literalPiece := p.literalPiece
  let chars0 ← quoteCharacters (base.str "piece_0") literalPiece
  let eq0 := mkIdent (base.str "piece_0_eq")
  checkPieceEquality p.label eq0 p.literalPieceTerm (← `(term| $chars0))
  pieceCharIdents := pieceCharIdents.push chars0
  pieceEqs := pieceEqs.push eq0
  pieceLengths := pieceLengths.push literalPiece.toList.length
  -- Fragments 1..n: the certified render fragments.
  for j in [:renderFuncTerms.size] do
    let i := j + 1
    let funcTerm := renderFuncTerms[j]!
    let some funcVal := renderFuncVals[j]? | throwError "missing {p.label} kernel fragment function"
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
        throwError "invalid {p.label} kernel fragment tree certificate: {dependency}"
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
        throwError "invalid {p.label} kernel fragment certificate: {dependency}"
    pieceCharIdents := pieceCharIdents.push chars
    pieceEqs := pieceEqs.push eqName
    pieceLengths := pieceLengths.push funcVal.render.toList.length
  let chunkList ← `(term| [$pieceCharIdents,*])
  let matched := mkIdent (base.str "model_matched")
  let mut pairProof ← `(term| List.Forall₂.nil)
  for i in [:pieceEqs.size] do
    let equation := pieceEqs[pieceEqs.size - 1 - i]!
    pairProof ← `(term| List.Forall₂.cons $equation $pairProof)
  elabCommand (← `(command| theorem $matched:ident :
    List.Forall₂ (fun s chars => s.toList = chars) $(p.kernelPiecesTerm) $chunkList := $pairProof))
  let modelConcat ← certifyConcatenation (base.str "model_assembly") modelChars
    pieceCharIdents pieceLengths
  let modelBytes := mkIdent (base.str "model_complete_bytes")
  elabCommand (← `(command| theorem $modelBytes:ident :
    ($chunkList).flatten = $modelChars := $modelConcat))
  let modelEq := mkIdent (base.str "model_c_eq")
  elabCommand (← `(command| theorem $modelEq:ident :
    $(p.kernelModelCTerm) = String.ofList $modelChars :=
      $(p.kernelCharsTerm) $chunkList $modelChars $matched $modelBytes))
  -- Assemble the composed source-to-build contract.
  let src := Syntax.mkStrLit source
  let sourceFile := Syntax.mkStrLit sourceName
  let inputTerm ← `(term| Parser.Source.InputRef.single $sourceFile $src)
  let ebnf := Syntax.mkStrLit grammar
  let buildLit := Syntax.mkStrLit description
  let mdLit := Syntax.mkStrLit metadata
  let theoremName := base.str "source_to_build"
  let theoremId := mkIdent theoremName
  p.emitFinal theoremId {
    inputTerm, modelChars, adapterChars, modelEq, buildTreeEq, buildBytesId,
    preparedMd, mdTreeId, mdBytesId, mdValid, adapterContract, adapterArtifact,
    src := ⟨src⟩, sourceFile := ⟨sourceFile⟩, ebnf := ⟨ebnf⟩,
    buildLit := ⟨buildLit⟩, mdLit := ⟨mdLit⟩ }
  let axioms ← collectAxioms theoremName
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in {p.label} FMI source-build contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {axioms.toList}"

end Rumoca.FMI3ProfileBuildCheck

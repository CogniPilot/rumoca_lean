import Rumoca.EFMITensorArtifactCheck
import Rumoca.FMI3AdapterCertificate
import RumocaEFMI.TensorProductionText
import RumocaEFMI.Directory

/-! Fixed adapter extending the actual tensor Algorithm Code theorem with the
independently read complete tensor Production C member. The certified-kernel
translation unit is bound to the read file one certified fragment at a time,
exactly as the FMI 3 tensor build checker binds `model.c`: each kernel-entry
render, the interface header and each method-function render is checked against
its independently delaborated tree, and the concatenation against the read bytes.
It never evaluates producer proof commands. -/
namespace Rumoca.EFMITensorProductionArtifactCheck
open Lean Elab Command
open Rumoca.FMI3AdapterCertificate (quoteCharacters certifyConcatenation checkCharacterEquality)
open Rumoca Rumoca.EFMI Rumoca.EFMI.TensorProduction Rumoca.CTensor

/-- Certify one certified-kernel or method fragment: define its delaborated tree,
prove the render function's tree by reflexivity, and reduce its rendered bytes to
the quoted characters. Mirrors the FMI 3 tensor build checker's fragment check. -/
private def certifyFunctionPiece (base : Name) (i : Nat) (funcTerm : TSyntax `term)
    (funcVal : CTree.Function) : CommandElabM Ident := do
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
      throwError "invalid tensor Production fragment tree certificate: {dependency}"
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
      throwError "invalid tensor Production fragment certificate: {dependency}"
  return chars

/-- Bind the actual Production C bytes to `TensorProduction.render`, returning the
quoted character list and the byte-identity theorem `render = String.ofList <chars>`. -/
def certifyRender (c : String) : CommandElabM (Ident × Ident) := do
  let base := `Rumoca.CheckedTensorEFMIFiles
  let modelChars ← quoteCharacters (base.str "production_chars") c
  -- The literal header line and the interface header are plain strings; the ten
  -- remaining fragments are each a concrete `CTree.Function`'s render.
  let literalPiece := "#include <stddef.h>\n#include <stdint.h>\n"
  let chars0 ← quoteCharacters (base.str "piece_0") literalPiece
  let eq0 := mkIdent (base.str "piece_0_eq")
  checkCharacterEquality eq0 (← `(term| ("#include <stddef.h>\n#include <stdint.h>\n").toList)) (← `(term| $chars0))
  let headerChars ← quoteCharacters (base.str "piece_8") TensorProduction.header
  let eq8 := mkIdent (base.str "piece_8_eq")
  checkCharacterEquality eq8 (← `(term| Rumoca.EFMI.TensorProduction.header.toList)) (← `(term| $headerChars))
  let funcTerms : Array (TSyntax `term) := #[
    ← `(term| Rumoca.CTensor.Fill.function),
    ← `(term| (Rumoca.CTensor.function Rumoca.Tensor.BinaryOp.add)),
    ← `(term| (Rumoca.CTensor.function Rumoca.Tensor.BinaryOp.mul)),
    ← `(term| Rumoca.CTensor.Diagonal.function),
    ← `(term| (Rumoca.CTensor.ProgramFixture.IVPEntry.plan Rumoca.ArrayProfile.stateShape).initial.function.tree),
    ← `(term| (Rumoca.CTensor.ProgramFixture.IVPEntry.plan Rumoca.ArrayProfile.stateShape).derivative.function.tree),
    ← `(term| Rumoca.CTensor.SquareDiagonal.function),
    ← `(term| Rumoca.EFMI.TensorProduction.startupFunction),
    ← `(term| Rumoca.EFMI.TensorProduction.recalibrateFunction),
    ← `(term| Rumoca.EFMI.TensorProduction.doStepFunction)]
  let funcVals : Array CTree.Function := #[
    Fill.function, function .add, function .mul, Diagonal.function,
    (ProgramFixture.IVPEntry.plan ArrayProfile.stateShape).initial.function.tree,
    (ProgramFixture.IVPEntry.plan ArrayProfile.stateShape).derivative.function.tree,
    SquareDiagonal.function,
    TensorProduction.startupFunction, TensorProduction.recalibrateFunction,
    TensorProduction.doStepFunction]
  -- Fragment order in `renderPieces`: kernelPieces[0..7], header, then the three
  -- method renders. Fragments 1..7 are kernel entries, 9..11 the method functions.
  let mut kernelChars : Array Ident := #[]
  let mut methodChars : Array Ident := #[]
  for j in [:funcTerms.size] do
    let idx := if j < 7 then j + 1 else j + 2
    let chars ← certifyFunctionPiece base idx funcTerms[j]! funcVals[j]!
    if j < 7 then kernelChars := kernelChars.push chars
    else methodChars := methodChars.push chars
  -- Assemble the chunk list in `renderPieces` order and the piece equalities.
  let pieceChars : Array Ident := #[chars0] ++ kernelChars ++ #[headerChars] ++ methodChars
  let pieceEqs : Array Ident := #[eq0]
    ++ (Array.range 7).map (fun j => mkIdent (base.str s!"piece_{j + 1}_eq"))
    ++ #[eq8]
    ++ (Array.range 3).map (fun j => mkIdent (base.str s!"piece_{j + 9}_eq"))
  let pieceLengths : Array Nat := #[literalPiece.toList.length]
    ++ (funcVals.toSubarray 0 7).toArray.map (fun f => f.render.toList.length)
    ++ #[TensorProduction.header.toList.length]
    ++ (funcVals.toSubarray 7 10).toArray.map (fun f => f.render.toList.length)
  let chunkList ← `(term| [$pieceChars,*])
  let matched := mkIdent (base.str "production_matched")
  let mut pairProof ← `(term| List.Forall₂.nil)
  for i in [:pieceEqs.size] do
    let equation := pieceEqs[pieceEqs.size - 1 - i]!
    pairProof ← `(term| List.Forall₂.cons $equation $pairProof)
  elabCommand (← `(command| theorem $matched:ident :
    List.Forall₂ (fun s cs => s.toList = cs) Rumoca.EFMI.TensorProduction.renderPieces $chunkList :=
      $pairProof))
  let concat ← certifyConcatenation (base.str "production_assembly") modelChars pieceChars pieceLengths
  let bytesEq := mkIdent (base.str "production_complete_bytes")
  elabCommand (← `(command| theorem $bytesEq:ident :
    ($chunkList).flatten = $modelChars := $concat))
  let renderEq := mkIdent (base.str "production_render_eq")
  elabCommand (← `(command| theorem $renderEq:ident :
    Rumoca.EFMI.TensorProduction.render = String.ofList $modelChars :=
      Rumoca.EFMI.TensorProduction.render_chars $chunkList $modelChars $matched $bytesEq))
  return (modelChars, renderEq)

def check (input : EFMICheckOptions.Code) (c : String) : CommandElabM Unit := do
  let ⟨_, _, algorithm, grammar, algGrammar⟩ := input
  let .ok _candidate := compileTensor input.input | throwError "tensor source compilation failed"
  if c != EFMI.TensorProduction.render then
    throwError "actual tensor Production C differs from the certified translation unit"
  if algorithm != EFMI.tensorUnitSource then
    throwError "actual tensor Algorithm Code differs from the pinned tensor square profile"
  EFMITensorArtifactCheck.check input
  let (modelChars, renderEq) ← certifyRender c
  let inputTerm ← input.inputTerm
  let alg := Syntax.mkStrLit algorithm
  let ebnf := Syntax.mkStrLit grammar
  let algEbnf := Syntax.mkStrLit algGrammar
  let algorithmRoot := mkIdent `Rumoca.CheckedTensorEFMIFiles.source_to_algorithm
  let theoremName := `Rumoca.CheckedTensorEFMIFiles.source_to_production
  let theoremId := mkIdent theoremName
  elabCommand (← `(command|
    theorem $theoremId:ident :
        Generated.source = $ebnf ∧ GALEC.Generated.source = $algEbnf ∧
        ∃ a : TensorArtifact $inputTerm, compileTensor $inputTerm = .ok a ∧
          TensorProductionContract a $alg (String.ofList $modelChars) := by
      obtain ⟨g₁, g₂, a, compiled, algorithm⟩ := $algorithmRoot:ident
      exact ⟨g₁, g₂, a, compiled, tensor_production_correct a algorithm $renderEq:ident⟩))
  let axioms ← collectAxioms theoremName
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in tensor Production C contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {axioms.toList}"

elab "verify_tensor_efmi_production_files" : command => do
  let root : System.FilePath := ← EFMICheckOptions.required rumoca.efmi.root
  let algorithm ← IO.FS.readFile (root / EFMI.Directory.algorithmDirectory / EFMI.Directory.algorithmName)
  let c ← IO.FS.readFile (root / EFMI.Directory.productionDirectory / EFMI.Directory.productionName)
  check (← EFMICheckOptions.readCode algorithm) c

end Rumoca.EFMITensorProductionArtifactCheck

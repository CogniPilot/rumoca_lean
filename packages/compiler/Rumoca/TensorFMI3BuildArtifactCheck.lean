import Rumoca.TensorProduction
import Rumoca.TensorFMI3AdapterCertificate
import Rumoca.FMI3ProfileBuildCheck

/-! Fixed actual-file adapter for the development tensor source-build profile.
The adapter independently reads all five staged files, compiles the source with
`compileTensor`, and checks a fixed proposition through the shared
`Rumoca.FMI3ProfileBuildCheck` driver. Preliminary comparisons only reject;
candidate data is never proof authority. -/

register_option rumoca.tensorFmi3.root : String :=
  { defValue := "", descr := "Prepared tensor FMI 3 directory containing sources and source snapshot" }

namespace Rumoca.TensorFMI3BuildArtifactCheck
open Lean Elab Command
open Rumoca.FMI3ProfileBuildCheck (ProfileBuildInputs FinalContext)
open Rumoca Rumoca.FMI3 Rumoca.CTensor

elab "verify_tensor_fmi3_build_files" : command => do
  let directory := rumoca.tensorFmi3.root.get (← getOptions)
  if directory.isEmpty then throwError "missing rumoca.tensorFmi3.root"
  Rumoca.FMI3ProfileBuildCheck.run {
    label := "tensor"
    root := directory
    base := `Rumoca.CheckedTensorFMI3Files
    compileProfile := fun input => do
      let .ok candidate := compileTensor input | throwError "tensor source compilation failed"
      return (candidate.name, FMI3.TensorMetadata.modelDescription candidate.tensorModel,
        TensorKernel.modelC)
    preparedMdLhs := ← `(term| FMI3.TensorMetadata.modelDescription Rumoca.squareModel)
    adapterCertify := TensorFMI3AdapterCertificate.certify
    literalPiece := "#include <stddef.h>\n"
    literalPieceTerm := ← `(term| ("#include <stddef.h>\n").toList)
    renderFuncTerms := #[
      ← `(term| Rumoca.CTensor.Fill.function),
      ← `(term| (Rumoca.CTensor.function Rumoca.Tensor.BinaryOp.add)),
      ← `(term| (Rumoca.CTensor.function Rumoca.Tensor.BinaryOp.mul)),
      ← `(term| Rumoca.CTensor.Diagonal.function),
      ← `(term| (Rumoca.CTensor.ProgramFixture.IVPEntry.plan Rumoca.ArrayProfile.stateShape).initial.function.tree),
      ← `(term| (Rumoca.CTensor.ProgramFixture.IVPEntry.plan Rumoca.ArrayProfile.stateShape).derivative.function.tree),
      ← `(term| Rumoca.CTensor.ProgramFixture.DiagonalEntry.profile.tree),
      ← `(term| Rumoca.CTensor.SquareDiagonal.function)]
    renderFuncVals := #[
      Fill.function, function .add, function .mul, Diagonal.function,
      (ProgramFixture.IVPEntry.plan ArrayProfile.stateShape).initial.function.tree,
      (ProgramFixture.IVPEntry.plan ArrayProfile.stateShape).derivative.function.tree,
      ProgramFixture.DiagonalEntry.profile.tree,
      SquareDiagonal.function]
    kernelPiecesTerm := ← `(term| Rumoca.TensorKernel.pieces)
    kernelModelCTerm := ← `(term| Rumoca.TensorKernel.modelC)
    kernelCharsTerm := ← `(term| Rumoca.TensorKernel.chars)
    emitFinal := fun theoremId ctx => do
      elabCommand (← `(command|
        theorem $theoremId:ident : Generated.source = $(ctx.ebnf) ∧
            ∃ a : Rumoca.TensorArtifact $(ctx.inputTerm), Rumoca.compileTensor $(ctx.inputTerm) = .ok a ∧
              Rumoca.TensorSourceBuildContract a (String.ofList $(ctx.modelChars)) $(ctx.buildLit)
                (String.ofList $(ctx.adapterChars)) $(ctx.mdLit) := by
          refine ⟨by rfl, ?_⟩
          let parsed : Rumoca.ArrayProfile.Parsed $(ctx.src) :=
            ⟨Rumoca.squareAst.tokens, Rumoca.squareAst, by rfl,
              Rumoca.ParserActions.parseTokens_complete Rumoca.ArrayProfile.actions Rumoca.squareAst⟩
          let a : Rumoca.TensorArtifact $(ctx.inputTerm) :=
            Rumoca.TensorArtifact.ofParsed $(ctx.inputTerm) parsed Rumoca.squareAst_resolved
          have hc : Rumoca.compileTensor $(ctx.inputTerm) = .ok a :=
            Rumoca.compileTensor_eq_parsed $(ctx.inputTerm) parsed Rumoca.squareAst_resolved
          refine ⟨a, hc, ?_⟩
          have hast : a.prepared.parsed.parsed.ast = Rumoca.squareAst := rfl
          have hmodel : a.tensorModel = Rumoca.squareModel := Rumoca.TensorArtifact.tensorModel_square a hast
          have hname : a.name = "TensorSquare" := Rumoca.TensorArtifact.name_square a hast
          refine Rumoca.tensorSourceBuild_correct a (String.ofList $(ctx.modelChars)) $(ctx.buildLit)
            (String.ofList $(ctx.adapterChars)) $(ctx.mdLit) ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact ($(ctx.modelEq):ident).symm
          · exact Rumoca.CTensor.ProgramFixture.IVPEntry.artifact_correct _ _ rfl rfl
          · rw [hname, ← (congrArg XML.document $(ctx.buildTreeEq):ident).trans $(ctx.buildBytesId):ident]
            exact FMI3.Build.artifact_correct "TensorSquare"
              ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
          · rw [hmodel, hname]
            exact ⟨($(ctx.adapterArtifact)).parsed.ast, ($(ctx.adapterArtifact)).solve.prepareFMI3, rfl, $(ctx.adapterContract)⟩
          · rw [hmodel, hname]
            exact FMI3.TensorMetadata.modelIdentifiers_decode Rumoca.squareModel
          · rw [hmodel]
            exact FMI3.TensorMetadata.token_attribute Rumoca.squareModel
          · rw [hmodel, $(ctx.preparedMd):ident, ← $(ctx.mdBytesId):ident]
            exact XML.document_correct $(ctx.mdTreeId) $(ctx.mdValid):ident)) }

end Rumoca.TensorFMI3BuildArtifactCheck

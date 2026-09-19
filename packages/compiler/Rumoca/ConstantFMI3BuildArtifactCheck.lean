import Rumoca.ConstantProduction
import Rumoca.ConstantFMI3AdapterCertificate
import Rumoca.FMI3ProfileBuildCheck

/-! Fixed actual-file adapter for the development constant-rate source-build
profile. The adapter independently reads all five staged files, compiles the
source with `compileConstant`, and checks a fixed proposition through the shared
`Rumoca.FMI3ProfileBuildCheck` driver. Preliminary comparisons only reject;
candidate data is never proof authority. -/

register_option rumoca.constantFmi3.root : String :=
  { defValue := "", descr := "Prepared constant FMI 3 directory containing sources and source snapshot" }

namespace Rumoca.ConstantFMI3BuildArtifactCheck
open Lean Elab Command
open Rumoca.FMI3ProfileBuildCheck (ProfileBuildInputs FinalContext)
open Rumoca Rumoca.FMI3

elab "verify_constant_fmi3_build_files" : command => do
  let directory := rumoca.constantFmi3.root.get (← getOptions)
  if directory.isEmpty then throwError "missing rumoca.constantFmi3.root"
  Rumoca.FMI3ProfileBuildCheck.run {
    label := "constant"
    root := directory
    base := `Rumoca.CheckedConstantFMI3Files
    compileProfile := fun input => do
      let .ok candidate := compileConstant input | throwError "constant source compilation failed"
      return (candidate.name, FMI3.TensorMetadata.constantModelDescription
        candidate.constantModel.shape candidate.constantModel.name, ConstantKernel.modelC)
    preparedMdLhs := ← `(term| FMI3.TensorMetadata.constantModelDescription
      Rumoca.constantRatesModel.shape Rumoca.constantRatesModel.name)
    adapterCertify := ConstantFMI3AdapterCertificate.certify
    literalPiece := Rumoca.CConstant.preamble
    literalPieceTerm := ← `(term| (Rumoca.CConstant.preamble).toList)
    renderFuncTerms := #[
      ← `(term| (Rumoca.CConstant.rhsFunction Rumoca.ConstantKernel.rates)),
      ← `(term| (Rumoca.CConstant.stepFunction Rumoca.ConstantKernel.rates)),
      ← `(term| (Rumoca.CConstant.sampleFunction Rumoca.ConstantKernel.rates))]
    renderFuncVals := #[
      Rumoca.CConstant.rhsFunction Rumoca.ConstantKernel.rates,
      Rumoca.CConstant.stepFunction Rumoca.ConstantKernel.rates,
      Rumoca.CConstant.sampleFunction Rumoca.ConstantKernel.rates]
    kernelPiecesTerm := ← `(term| Rumoca.ConstantKernel.pieces)
    kernelModelCTerm := ← `(term| Rumoca.ConstantKernel.modelC)
    kernelCharsTerm := ← `(term| Rumoca.ConstantKernel.chars)
    emitFinal := fun theoremId ctx => do
      elabCommand (← `(command|
        theorem $theoremId:ident : Generated.source = $(ctx.ebnf) ∧
            ∃ a : Rumoca.ConstantArtifact $(ctx.inputTerm), Rumoca.compileConstant $(ctx.inputTerm) = .ok a ∧
              Rumoca.ConstantSourceBuildContract a (String.ofList $(ctx.modelChars)) $(ctx.buildLit)
                (String.ofList $(ctx.adapterChars)) $(ctx.mdLit) := by
          refine ⟨by rfl, ?_⟩
          let parsed : Rumoca.ConstantProfile.Parsed $(ctx.src) :=
            ⟨Rumoca.constantRatesAst.tokens, Rumoca.constantRatesAst, by rfl,
              Rumoca.ParserActions.parseTokens_complete Rumoca.ConstantProfile.actions Rumoca.constantRatesAst⟩
          let a : Rumoca.ConstantArtifact $(ctx.inputTerm) :=
            Rumoca.ConstantArtifact.ofParsed $(ctx.inputTerm) parsed Rumoca.constantRatesAst_resolved
          have hc : Rumoca.compileConstant $(ctx.inputTerm) = .ok a :=
            Rumoca.compileConstant_eq_parsed $(ctx.inputTerm) parsed Rumoca.constantRatesAst_resolved
          refine ⟨a, hc, ?_⟩
          have hname : a.name = "ConstantRates" := rfl
          have hmodel : a.constantModel = Rumoca.constantRatesModel := rfl
          refine Rumoca.constantSourceBuild_correct a (String.ofList $(ctx.modelChars)) $(ctx.buildLit)
            (String.ofList $(ctx.adapterChars)) $(ctx.mdLit) ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact ($(ctx.modelEq):ident).symm
          · exact Rumoca.CConstant.contract_correct Rumoca.ConstantKernel.rates Rumoca.ConstantKernel.modelC
              Rumoca.ConstantKernel.modelC_programText.symm
          · rw [hname, ← (congrArg XML.document $(ctx.buildTreeEq):ident).trans $(ctx.buildBytesId):ident]
            exact FMI3.Build.artifact_correct "ConstantRates"
              ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
          · rw [hmodel, hname]
            exact ⟨($(ctx.adapterArtifact)).parsed.ast, ($(ctx.adapterArtifact)).solve.prepareFMI3, rfl, $(ctx.adapterContract)⟩
          · rw [hmodel, hname]
            exact FMI3.TensorMetadata.constant_modelIdentifiers_decode
              Rumoca.constantRatesModel.shape Rumoca.constantRatesModel.name
          · rw [hmodel]
            exact FMI3.TensorMetadata.constantToken_attribute
              Rumoca.constantRatesModel.shape Rumoca.constantRatesModel.name
          · show XML.Document (FMI3.TensorMetadata.constantModelDescription
              Rumoca.constantRatesModel.shape Rumoca.constantRatesModel.name) $(ctx.mdLit)
            rw [$(ctx.preparedMd):ident, ← $(ctx.mdBytesId):ident]
            exact XML.document_correct $(ctx.mdTreeId) $(ctx.mdValid):ident)) }

end Rumoca.ConstantFMI3BuildArtifactCheck

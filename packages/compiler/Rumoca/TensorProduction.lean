import Rumoca.TensorArtifact
import RumocaFMI3.TensorFunctions
import RumocaFMI3.TensorCallPolicy
import RumocaFMI3.TensorAdapterContract
import RumocaFMI3.TensorMetadata
import RumocaFMI3.BuildDescriptionProofs
import RumocaC.TensorCode
import RumocaC.TensorFillCode
import RumocaC.TensorDiagonalCode
import RumocaC.TensorSquareDiagonal
import RumocaC.TensorSquareIVPEntry
import RumocaC.TensorSquareClosedCalls
import RumocaFMI3.TensorNumericalEvents
import RumocaFMI3.PreparedTensorLinkedContract
import RumocaFMI3.TensorAcceptedRuntime

/-! Tensor artifact and its composed source-to-build contract. This
mirrors the scalar `Artifact`/`FMI3.SourceBuildContract` shape for the pointwise
tensor profile: it parses the array profile, prepares the executable pointwise
kernel, and carries the certified tensor kernel C text, the rendered tensor
adapter, the tensor model description and the shared build description.

The CLI delegates the admitted array/tensor profile to this compiler path.
Publication still requires the relevant fixed actual-artifact certificate;
successful parsing alone does not authorize a new source case. Tensor rank and
extents stay symbolic in the shape parameter; the pointwise problem is the one
owner of the executable kernel. -/
namespace Rumoca

open _root_.Parser
open Rumoca.Solve Rumoca.FMI3

/-! ### The certified tensor kernel C text

The private numerical kernel `model.c` is the concatenation of the certified
tensor helper renders, the pointwise IVP sources (initial, derivative and the
square-Jacobian coefficient program) and the scratch-free square-Jacobian
diagonal materializer, with `<stddef.h>` prepended so `size_t` is in scope at
the adapter's `#include "model.c"`. Every fragment is the same emission the
tensor C artifact checks certify. -/
namespace TensorKernel
open Rumoca.CTensor

/-- The certified private-kernel fragments in emission order. -/
def pieces : List String :=
  ["#include <stddef.h>\n",
   Fill.function.render,
   (function .add).render,
   (function .mul).render,
   Diagonal.function.render,
   ProgramFixture.IVPEntry.sources.initial,
   ProgramFixture.IVPEntry.sources.derivative,
   ProgramFixture.IVPEntry.sources.diagonal.getD "",
   ProgramFixture.IVPEntry.jacobianDiagSource]

/-- The certified private-kernel `model.c` text. -/
def modelC : String := String.join pieces

/-- The existing rendered fragments are exactly the numerical execution table,
in the same order; no helper is inserted by a linkage certificate. -/
theorem pieces_functions :
    pieces = "#include <stddef.h>\n" :: functions.map CTree.Function.render := rfl

theorem square_ivp : Rumoca.squareModel.ivp =
    CTensor.ProgramFixture.IVPEntry.kernel ArrayProfile.stateShape :=
  ArrayProfile.Solved.lower_eq_squareIVP
    (ArrayProfile.DAE.lower (ArrayProfile.Flat.lower squareAst squareAst_resolved)) rfl rfl rfl

/-- Source compilation supplies the very Solve index consumed by the C plan. -/
theorem compiled_ivp (a : TensorArtifact input)
    (parsed : a.prepared.parsed.parsed.ast = squareAst) :
    a.tensorModel.ivp = CTensor.ProgramFixture.IVPEntry.kernel ArrayProfile.stateShape := by
  rw [a.tensorModel_square parsed]
  exact square_ivp

/-- Bind independently read numerical bytes to that same function table. -/
theorem actual_functions (actual : String) (checked : actual = modelC) :
    actual = String.join ("#include <stddef.h>\n" :: functions.map CTree.Function.render) := by
  rw [checked, modelC, pieces_functions]

private theorem piece_chunks (ps : List String) (chunks : List (List Char))
    (matched : List.Forall₂ (fun s chars => s.toList = chars) ps chunks) :
    ps.flatMap (fun s => s.toList) = chunks.flatten := by
  induction matched with
  | nil => rfl
  | cons head tail ih => simp only [List.flatMap_cons, List.flatten_cons, head, ih]

/-- The checker certifies each fragment separately, joins the character chunks
and binds them to the independently read `model.c` file. -/
theorem chars (chunks : List (List Char)) (actual : List Char)
    (matched : List.Forall₂ (fun s chars => s.toList = chars) pieces chunks)
    (bytes : chunks.flatten = actual) : modelC = String.ofList actual := by
  apply String.toList_injective
  rw [modelC, CString.join_toList, piece_chunks _ _ matched, bytes, String.toList_ofList]

end TensorKernel

noncomputable section
open CTree CMemory

structure TensorNumericalLinkage (a : TensorArtifact input) (numerical adapter : String) : Prop where
  /-- The compiler-owned Solve value is the exact index of the emitted plan. -/
  ivp : a.tensorModel.ivp = CTensor.ProgramFixture.IVPEntry.kernel ArrayProfile.stateShape
  /-- The actual numerical bytes use precisely the execution table's trees. -/
  bytes : numerical = String.join ("#include <stddef.h>\n" :: TensorKernel.functions.map Function.render)
  /-- Storage and finite-execution premises remain, but library/lookup premises do not. -/
  calls : ∀ shape, TensorKernel.ClosedIVPCalls shape
  /-- One signature witness owns the rendered adapter, prepared literal pool,
  numerical extension, prepared rejection calls and concrete accepted execution. -/
  adapterTable : ∃ (source : AST.Model) (model : Solve.FMI3Model source), source.name = a.name ∧
    ∀ [FMI3.StaticLiterals], ∃ sigs : List Signature,
      ((FMI3.TensorFunctions.functions model a.tensorModel sigs).map (fun fn => fn.signature.name)).Nodup ∧
      FMI3.TensorFunctions.render model a.tensorModel sigs = adapter ∧
      FMI3.StepEntry.signature ∈ sigs ∧
      (FMI3.TensorFunctions.prepare model a.tensorModel sigs).isSome = true ∧
      CCalls.Typed.Extends TensorKernel.definitions (FMI3.TensorFunctions.squareLinkedProgram model a.tensorModel sigs) ∧
      FMI3.PreparedStep.TensorContractFor model a.tensorModel sigs
        (FMI3.TensorFunctions.squareLinkedProgram model a.tensorModel sigs) ∧
      TensorKernel.RuntimeTransfer (FMI3.TensorFunctions.squareLinkedProgram model a.tensorModel sigs) ∧
      FMI3.TensorAcceptedRuntime.Contract model a.tensorModel sigs

theorem tensorNumericalLinkage_correct (a : TensorArtifact input) (numerical adapter : String)
    (index : a.tensorModel.ivp = CTensor.ProgramFixture.IVPEntry.kernel ArrayProfile.stateShape)
    (bytes : numerical = TensorKernel.modelC)
    (adapterContract : ∃ (source : AST.Model) (model : Solve.FMI3Model source), source.name = a.name ∧
      ∀ [FMI3.StaticLiterals], FMI3.TensorAdapter.Contract model a.tensorModel adapter) :
    TensorNumericalLinkage a numerical adapter := by
  refine ⟨index, TensorKernel.actual_functions numerical bytes, TensorKernel.ivp_closed, ?_⟩
  obtain ⟨source, model, named, contracts⟩ := adapterContract
  refine ⟨source, model, named, ?_⟩
  intro static
  obtain ⟨sigs, unique, rendered, step, poolReady, _prepared, _defined, _helper, _fragment, covered, _rest⟩ := contracts
  have linked := FMI3.TensorFunctions.linked_numerical_covered model a.tensorModel sigs unique covered
  exact ⟨sigs, unique, rendered, step, poolReady, linked,
    FMI3.PreparedStep.tensor_linked_contract model a.tensorModel sigs step unique covered,
    TensorKernel.runtime_transfer _ linked,
    FMI3.TensorAcceptedRuntime.contract model a.tensorModel sigs step unique covered⟩

/-- The existing actual-source checker already proves this AST identity. The
new field additionally requires it to discharge the missing numerical index. -/
theorem tensorNumericalLinkage_of_source (a : TensorArtifact input) (numerical adapter : String)
    (parsed : a.prepared.parsed.parsed.ast = squareAst)
    (bytes : numerical = TensorKernel.modelC)
    (adapterContract : ∃ (source : AST.Model) (model : Solve.FMI3Model source), source.name = a.name ∧
      ∀ [FMI3.StaticLiterals], FMI3.TensorAdapter.Contract model a.tensorModel adapter) :
    TensorNumericalLinkage a numerical adapter :=
  tensorNumericalLinkage_correct a numerical adapter (TensorKernel.compiled_ivp a parsed) bytes adapterContract

end

/-- The composed tensor source-to-build contract, mirroring
`FMI3.SourceBuildContract` for the pointwise tensor profile. It bundles the
certified tensor kernel C text and its pointwise IVP artifact contract, the
build-description contract, the rendered tensor adapter contract (over a scalar
witness that shares the model name and any static literal table), the model
identifier and instantiation-token agreements, and the tensor model description
XML document. -/
structure TensorSourceBuildContract (a : TensorArtifact input)
    (modelC buildDescription adapter metadata : String) : Prop where
  /-- Actual numerical bytes, compiled IVP, and the rendered adapter share one
  tree-backed execution table, including prepared rejection calls. -/
  numerical : TensorNumericalLinkage a modelC adapter
  /-- The actual private kernel is exactly the certified tensor kernel text. -/
  kernel : modelC = TensorKernel.modelC
  /-- The pointwise IVP sources (initial, derivative, Jacobian coefficients) and
  the scratch-free square-Jacobian diagonal entry carry their certified Solve
  emission and storage behavior. -/
  kernelContract : CTensor.ProgramFixture.IVPEntry.ArtifactContract
    CTensor.ProgramFixture.IVPEntry.sources CTensor.ProgramFixture.IVPEntry.jacobianDiagSource
  /-- The source-build recipe agrees with the required profile for the model. -/
  build : FMI3.Build.ArtifactContract a.name buildDescription
  /-- The complete rendered tensor call graph obeys the checked no-heap policy (no
  callee is an allocation entry point; every callee is a defined function, a declared
  kernel entry or a named external) and its direct-call relation among defined
  functions is acyclic. This is a proved consequence of the mandatory tensor adapter
  contract, carried as an explicit conjunct on the actual bytes. -/
  no_heap_acyclic : ∃ (src : AST.Model) (w : Solve.FMI3Model src) (sigs : List CTree.Signature),
    FMI3.TensorFunctions.render w a.tensorModel sigs = adapter ∧
    CCallPolicy.NoHeap (FMI3.TensorFunctions.functions w a.tensorModel sigs)
        FMI3.TensorCallPolicy.bTensor = true ∧
    CCallPolicy.Acyclic (FMI3.TensorFunctions.functions w a.tensorModel sigs)
  /-- The rendered adapter satisfies the tensor adapter contract for a scalar
  witness sharing the model name, relative to any static literal table. -/
  adapter : ∃ (src : AST.Model) (w : Solve.FMI3Model src), src.name = a.name ∧
    ∀ [FMI3.StaticLiterals], FMI3.TensorAdapter.Contract w a.tensorModel adapter
  /-- The tensor model description decodes to the model identifiers. -/
  model_identifiers : FMI3.decodeModelIdentifiers (FMI3.TensorMetadata.modelDescription a.tensorModel)
    = some (a.name, FMI3.modelIdentifier a.name, FMI3.modelIdentifier a.name)
  /-- The declared instantiation token is exactly the one the factory validates. -/
  token : (FMI3.TensorMetadata.modelDescription a.tensorModel).attributes.lookup "instantiationToken"
    = some (FMI3.TensorMetadata.token a.tensorModel)
  /-- The actual model description bytes are the prepared tensor document. -/
  metadata : XML.Document (FMI3.TensorMetadata.modelDescription a.tensorModel) metadata

/-- Bundle independently checked obligations into the composed contract,
mirroring `FMI3.sourceBuild_correct`. -/
theorem tensorSourceBuild_correct (a : TensorArtifact input)
    (modelC buildDescription adapter metadata : String)
    (index : a.tensorModel.ivp = CTensor.ProgramFixture.IVPEntry.kernel ArrayProfile.stateShape)
    (kernel : modelC = TensorKernel.modelC)
    (kernelContract : CTensor.ProgramFixture.IVPEntry.ArtifactContract
      CTensor.ProgramFixture.IVPEntry.sources CTensor.ProgramFixture.IVPEntry.jacobianDiagSource)
    (build : FMI3.Build.ArtifactContract a.name buildDescription)
    (adapter' : ∃ (src : AST.Model) (w : Solve.FMI3Model src), src.name = a.name ∧
      ∀ [FMI3.StaticLiterals], FMI3.TensorAdapter.Contract w a.tensorModel adapter)
    (identifiers : FMI3.decodeModelIdentifiers (FMI3.TensorMetadata.modelDescription a.tensorModel)
      = some (a.name, FMI3.modelIdentifier a.name, FMI3.modelIdentifier a.name))
    (token : (FMI3.TensorMetadata.modelDescription a.tensorModel).attributes.lookup "instantiationToken"
      = some (FMI3.TensorMetadata.token a.tensorModel))
    (metadataDocument : XML.Document (FMI3.TensorMetadata.modelDescription a.tensorModel) metadata) :
    TensorSourceBuildContract a modelC buildDescription adapter metadata :=
  ⟨tensorNumericalLinkage_correct a modelC adapter index kernel adapter',
    kernel, kernelContract, build,
    (by
      obtain ⟨src, w, _, contractFn⟩ := adapter'
      letI : FMI3.StaticLiterals := ⟨fun _ => none⟩
      obtain ⟨sigs, _, renderEq, _step, _poolReady, _prepared, _defined, _helper, _fragment, covered, _⟩ := contractFn
      exact ⟨src, w, sigs, renderEq,
        FMI3.TensorCallPolicy.tensor_no_heap w a.tensorModel sigs,
        FMI3.TensorCallPolicy.tensor_acyclic w a.tensorModel sigs covered⟩),
    adapter', identifiers, token, metadataDocument⟩

end Rumoca

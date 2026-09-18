import Rumoca.Compiler
import Rumoca.ArrayCompiler
import RumocaCore.Solve.TensorFMI3
import RumocaFMI3.TensorFunctions
import RumocaFMI3.TensorAdapterContract
import RumocaFMI3.TensorMetadata
import RumocaFMI3.BuildDescriptionProofs
import RumocaC.TensorCode
import RumocaC.TensorFillCode
import RumocaC.TensorDiagonalCode
import RumocaC.TensorSquareDiagonal
import TensorCChecks.IVPEntry

/-! Development tensor artifact and its composed source-to-build contract. This
mirrors the scalar `Artifact`/`FMI3.SourceBuildContract` shape for the pointwise
tensor profile: it parses the array profile, prepares the executable pointwise
kernel, and carries the certified tensor kernel C text, the rendered tensor
adapter, the tensor model description and the shared build description.

This path is deliberately kept out of the CLI's production admission: the
default compiler still rejects the array profile. Tensor rank and extents stay
symbolic in the shape parameter; the pointwise problem is the one owner of the
executable kernel. -/
namespace Rumoca

open _root_.Parser
open Rumoca.Solve Rumoca.FMI3

/-- A development tensor artifact: the located array parse together with its
prepared pointwise kernel. Source provenance and the lowering chain cannot be
absent or supplied by reparsing. -/
structure TensorArtifact (input : Source.InputRef) where
  prepared : ArrayCompiler.Prepared input.source

namespace TensorArtifact

/-- The parsed model name that owns every emitted identifier. -/
def name (a : TensorArtifact input) : String :=
  a.prepared.parsed.parsed.ast.header.name

/-- The prepared FMI 3 deployment data for the pointwise tensor problem: the
model name paired with the owned executable kernel. -/
def tensorModel (a : TensorArtifact input) : Solve.TensorFMI3Model ArrayProfile.stateShape :=
  ⟨a.name, a.prepared.kernel⟩

theorem tensorModel_name (a : TensorArtifact input) : a.tensorModel.name = a.name := rfl

/-- The synthetic scalar witness source that supplies the model-independent
adapter bodies. It is a valid scalar unit model carrying the same model name,
compiled through the same checked scalar parse/lower/prepare path as production;
its numerical kernel is dead for the tensor bodies, which call the prepared
tensor kernel entry directly. -/
def scalarSource (a : TensorArtifact input) : String :=
  "model " ++ a.name ++ " Real x; equation der(x) = 1; end " ++ a.name ++ ";"

def scalarInput (a : TensorArtifact input) : Source.InputRef :=
  .single "rumoca-tensor-witness:/scalar.mo" a.scalarSource

end TensorArtifact

/-- Parse the array profile and prepare its pointwise kernel. This entry is not
called by the CLI's default admission path. -/
def compileTensor (input : Source.InputRef) :
    Except (Source.Diagnostic input.source) (TensorArtifact input) := do
  let prepared ← ArrayCompiler.prepare input.source
  return ⟨prepared⟩

theorem compileTensor_eq (input : Source.InputRef) (prepared : ArrayCompiler.Prepared input.source)
    (parsed : ArrayCompiler.prepare input.source = .ok prepared) :
    compileTensor input = .ok ⟨prepared⟩ := by
  simp only [compileTensor, parsed, bind, Except.bind]
  rfl

/-! ### The development `TensorSquare` instance

The array profile admits a single development source case, `TensorSquare`. Its
parsed AST, prepared kernel and tensor model are pinned here so that the fixed
checker can bind the actual `compileTensor` result to the concrete tensor model
the render and metadata theorems reason about, using lexer/parser determinism
rather than reconstructing the located parse. -/

/-- The parsed array AST for the development `TensorSquare` source. -/
def squareAst : ArrayProfile.Model :=
  ⟨⟨"TensorSquare", "u", "x", "start", "fixed"⟩,
   .jacobian "J" "x" ⟨"u", "u"⟩ "J" ⟨"jacobian", ⟨"u", "u"⟩, "u"⟩, "TensorSquare"⟩

theorem squareAst_resolved : squareAst.Resolved := by decide

/-- The pinned tensor model for the development `TensorSquare` source. -/
def squareModel : Solve.TensorFMI3Model ArrayProfile.stateShape :=
  ⟨"TensorSquare", ArrayProfile.Solved.lower (ArrayProfile.DAE.lower (ArrayProfile.Flat.lower squareAst squareAst_resolved))⟩

namespace TensorArtifact

/-- The parsed AST of any tensor artifact is determined by the lexed token
stream: given the lexer result for the source, the parsed AST is the unique
model those tokens decode to. -/
theorem ast_determined (a : TensorArtifact input) (m : ArrayProfile.Model)
    (lexeq : Rumoca.lex input.source = .ok m.tokens) :
    a.prepared.parsed.parsed.ast = m := by
  have htok : a.prepared.parsed.parsed.tokens = m.tokens :=
    Except.ok.inj (a.prepared.parsed.parsed.lexical.symm.trans lexeq)
  have hsyn := a.prepared.parsed.parsed.syntactic
  rw [htok] at hsyn
  exact Option.some.inj (hsyn.symm.trans (ParserActions.parseTokens_complete ArrayProfile.actions m))

/- With the parsed AST pinned to `squareAst`, the tensor model is the pinned
`squareModel`, independent of the erased resolution proof. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem tensorModel_square (a : TensorArtifact input)
    (hast : a.prepared.parsed.parsed.ast = squareAst) : a.tensorModel = squareModel := by
  unfold TensorArtifact.tensorModel TensorArtifact.name
  obtain ⟨⟨parsed, res, kernel, hlow⟩⟩ := a
  simp only at hast ⊢
  generalize hg : parsed.parsed.ast = g at res hlow hast
  subst hast
  have hres : res = squareAst_resolved := rfl
  rw [hres] at hlow
  rw [hlow]
  show (⟨squareAst.header.name, _⟩ : Solve.TensorFMI3Model _) = squareModel
  rw [show squareAst.header.name = "TensorSquare" from rfl]
  rfl

set_option maxRecDepth 100000 in
theorem name_square (a : TensorArtifact input)
    (hast : a.prepared.parsed.parsed.ast = squareAst) : a.name = "TensorSquare" := by
  unfold TensorArtifact.name; rw [hast]; rfl

end TensorArtifact

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

/-- The composed tensor source-to-build contract, mirroring
`FMI3.SourceBuildContract` for the pointwise tensor profile. It bundles the
certified tensor kernel C text and its pointwise IVP artifact contract, the
build-description contract, the rendered tensor adapter contract (over a scalar
witness that shares the model name and any static literal table), the model
identifier and instantiation-token agreements, and the tensor model description
XML document. -/
structure TensorSourceBuildContract (a : TensorArtifact input)
    (modelC buildDescription adapter metadata : String) : Prop where
  /-- The actual private kernel is exactly the certified tensor kernel text. -/
  kernel : modelC = TensorKernel.modelC
  /-- The pointwise IVP sources (initial, derivative, Jacobian coefficients) and
  the scratch-free square-Jacobian diagonal entry carry their certified Solve
  emission and storage behavior. -/
  kernelContract : CTensor.ProgramFixture.IVPEntry.ArtifactContract
    CTensor.ProgramFixture.IVPEntry.sources CTensor.ProgramFixture.IVPEntry.jacobianDiagSource
  /-- The source-build recipe agrees with the required profile for the model. -/
  build : FMI3.Build.ArtifactContract a.name buildDescription
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
  ⟨kernel, kernelContract, build, adapter', identifiers, token, metadataDocument⟩

end Rumoca

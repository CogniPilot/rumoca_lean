import Rumoca.Compiler
import Rumoca.ConstantCompiler
import RumocaCore.Solve.ConstantFMI3
import RumocaFMI3.ConstantFunctions
import RumocaFMI3.ConstantCallPolicy
import RumocaFMI3.ConstantAdapterContract
import RumocaFMI3.TensorMetadata
import RumocaFMI3.BuildDescriptionProofs
import RumocaC.ConstantKernelProgram

/-! Development constant-rate (G01) artifact and its composed source-to-build
contract. This mirrors the scalar `Artifact`/`FMI3.SourceBuildContract` and the
tensor `TensorArtifact`/`TensorSourceBuildContract` shapes for the constant-rate
profile: it parses the constant profile, prepares the executable constant-rate
IVP, and carries the certified constant kernel C text (the three rendered
`ConstantKernelProgram` entries with their preamble), the rendered constant
adapter, the constant model description and the shared build description.

The constant profile carries no input tensor and no dense output: its state is a
homogeneous vector of scalar states whose derivatives are signed decimal
constants. The state count stays symbolic in the model's shape parameter. This
path is deliberately kept out of the tensor and unit production admission: the
default compiler and the tensor path still reject the constant profile. -/
namespace Rumoca

open _root_.Parser
open Rumoca.Solve Rumoca.FMI3 Rumoca.ConstantProfile

/-- A development constant-rate artifact: the located constant parse together
with its prepared constant-rate IVP. Source provenance and the lowering chain
cannot be absent or supplied by reparsing. -/
structure ConstantArtifact (input : Source.InputRef) where
  prepared : ConstantCompiler.Prepared input.source

namespace ConstantArtifact

/-- The parsed model name that owns every emitted identifier. -/
def name (a : ConstantArtifact input) : String :=
  a.prepared.parsed.parsed.ast.name

/-- The prepared FMI 3 deployment data for the constant-rate problem: the model
name paired with the owned constant-rate IVP over the declared state count. -/
def constantModel (a : ConstantArtifact input) :
    Solve.ConstantFMI3Model a.prepared.parsed.parsed.ast.states.length :=
  ⟨a.name, a.prepared.ivp⟩

theorem constantModel_name (a : ConstantArtifact input) : a.constantModel.name = a.name := rfl

/-- The synthetic scalar witness source that supplies the model-independent
adapter bodies. It is a valid scalar unit model carrying the same model name,
compiled through the same checked scalar parse/lower/prepare path as production;
its numerical kernel is dead for the constant bodies, which call the prepared
constant kernel entries directly. -/
def scalarSource (a : ConstantArtifact input) : String :=
  "model " ++ a.name ++ " Real x; equation der(x) = 1; end " ++ a.name ++ ";"

def scalarInput (a : ConstantArtifact input) : Source.InputRef :=
  .single "rumoca-constant-witness:/scalar.mo" a.scalarSource

end ConstantArtifact

/-- Parse the constant profile and prepare its constant-rate IVP. This entry is
not called by the CLI's default or tensor admission path. -/
def compileConstant (input : Source.InputRef) :
    Except (Source.Diagnostic input.source) (ConstantArtifact input) := do
  let prepared ← ConstantCompiler.prepare input.source
  return ⟨prepared⟩

theorem compileConstant_eq (input : Source.InputRef)
    (prepared : ConstantCompiler.Prepared input.source)
    (parsed : ConstantCompiler.prepare input.source = .ok prepared) :
    compileConstant input = .ok ⟨prepared⟩ := by
  simp only [compileConstant, parsed, bind, Except.bind]
  rfl

/-- Total construction of a constant artifact from an already certified constant
parse and its resolution, mirroring the tensor profile's
`TensorArtifact.ofParsed`. The generic `ParserActions.Parsed.located` from
`ActionsLocatedTotal` applies to the constant actions, so the located parse for
a pinned AST is produced without kernel-evaluating the LR parser on the source
text. -/
def ConstantArtifact.ofParsed (input : Source.InputRef)
    (parsed : ConstantProfile.Parsed input.source) (resolved : parsed.ast.Resolved) :
    ConstantArtifact input :=
  ⟨ConstantCompiler.prepareParsed parsed.located resolved⟩

/-- The constant driver implements the same successful parse and resolution for a
pinned AST. As in the tensor profile's `compileTensor_eq_parsed`, there is no
additional location-success assumption and the LR parser is not kernel-evaluated. -/
theorem compileConstant_eq_parsed (input : Source.InputRef)
    (parsed : ConstantProfile.Parsed input.source) (resolved : parsed.ast.Resolved) :
    compileConstant input = .ok (ConstantArtifact.ofParsed input parsed resolved) := by
  simp only [compileConstant, ConstantArtifact.ofParsed, bind, Except.bind,
    ConstantCompiler.prepare_eq_parsed parsed resolved]
  rfl

/-- Every resolvable constant-profile source in the existing lexical/AST
specification compiles, with its parsed AST pinned to the given model. This is
the constant analogue of the tensor profile's `compileTensor_complete`. -/
theorem compileConstant_complete (input : Source.InputRef) (m : ConstantProfile.Model)
    (syntaxValid : Lexes input.source.toList (ConstantProfile.actions.tokens m))
    (resolved : m.Resolved) :
    ∃ a, compileConstant input = .ok a ∧ a.prepared.parsed.parsed.ast = m :=
  let parsed : ConstantProfile.Parsed input.source :=
    ⟨ConstantProfile.actions.tokens m, m, (lex_correct input.source _).mpr syntaxValid,
      ParserActions.parseTokens_complete ConstantProfile.actions m⟩
  ⟨ConstantArtifact.ofParsed input parsed resolved,
    compileConstant_eq_parsed input parsed resolved, rfl⟩

/-! ### The development `ConstantRates` instance

The constant profile admits a single development source case, `ConstantRates`.
Its parsed AST and prepared constant model are pinned here so that the fixed
checker can bind the actual `compileConstant` result to the concrete constant
model the render and metadata theorems reason about, using lexer/parser
determinism rather than reconstructing the located parse. -/

/-- The parsed constant AST for the development `ConstantRates` source: two
states with the signed decimal rates `der(x) = 2.5` and `der(y) = -1`. -/
def constantRatesAst : ConstantProfile.Model :=
  ⟨"ConstantRates", "x", "y", [], ⟨"x", "2.5"⟩, [⟨"y", "-1"⟩], "ConstantRates"⟩

theorem constantRatesAst_resolved : constantRatesAst.Resolved := by decide

/-- The pinned constant model for the development `ConstantRates` source. -/
def constantRatesModel : Solve.ConstantFMI3Model 2 :=
  ⟨"ConstantRates", constantRatesAst.lower⟩

namespace ConstantArtifact

/-- With the parsed AST pinned to `constantRatesAst`, the model name is the
pinned `ConstantRates`. The prepared model is definitionally `constantRatesModel`
for a pinned parse, so the checker binds it by reflexivity. -/
theorem name_rates (a : ConstantArtifact input)
    (hast : a.prepared.parsed.parsed.ast = constantRatesAst) : a.name = "ConstantRates" := by
  unfold ConstantArtifact.name; rw [hast]; rfl

end ConstantArtifact

/-! ### The certified constant kernel C text

The private numerical kernel `model.c` is the constant-rate translation unit:
the IEEE 754 binary64 preamble followed by the three rendered kernel entries
(`rumoca_constant_rhs`, `rumoca_constant_step`, `rumoca_constant_sample`) over
the source rates. Every fragment is the same emission the constant kernel
contract certifies. -/
namespace ConstantKernel
open Rumoca.CConstant

/-- The declaration-order source rate literals for the development `ConstantRates`
fixture: `2.5 = 25 * 10^-1` and `-1 = -1 * 10^0`. -/
def rates : List Decimal := [⟨1, 25, -1⟩, ⟨-1, 1, 0⟩]

/-- The certified private-kernel fragments in emission order: the binary64
preamble and the three rendered kernel entries. -/
def pieces : List String :=
  [preamble, (rhsFunction rates).render, (stepFunction rates).render, (sampleFunction rates).render]

/-- The certified private-kernel `model.c` text. -/
def modelC : String := String.join pieces

/-- The certified `model.c` text is exactly the constant kernel's rendered
program over the source rates, the emission the constant kernel contract binds. -/
theorem modelC_programText : modelC = programText rates := by
  apply String.toList_injective
  rw [modelC, CString.join_toList]
  simp only [pieces, programText, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    String.toList_append, List.append_assoc]

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

end ConstantKernel

/-- The composed constant source-to-build contract, mirroring
`FMI3.SourceBuildContract` and `TensorSourceBuildContract` for the constant-rate
profile. It bundles the certified constant kernel C text and its constant kernel
contract, the build-description contract, the rendered constant adapter contract
(over a scalar witness that shares the model name and any static literal table),
the model identifier and instantiation-token agreements, and the constant model
description XML document. -/
structure ConstantSourceBuildContract (a : ConstantArtifact input)
    (modelC buildDescription adapter metadata : String) : Prop where
  /-- The actual private kernel is exactly the certified constant kernel text. -/
  kernel : modelC = ConstantKernel.modelC
  /-- The three constant kernel entries carry their certified target-execution and
  exact-rounding contract: the rounded-rate write, the finite whole-vector Euler
  step, and its counted iteration. -/
  kernelContract : Rumoca.CConstant.Contract ConstantKernel.rates ConstantKernel.modelC
  /-- The source-build recipe agrees with the required profile for the model. -/
  build : FMI3.Build.ArtifactContract a.name buildDescription
  /-- The complete rendered constant call graph obeys the checked no-heap policy (no
  callee is an allocation entry point; every callee is a defined function, a declared
  kernel entry or a named external) and its direct-call relation among defined
  functions is acyclic. This is a proved consequence of the mandatory constant adapter
  contract, carried as an explicit conjunct on the actual bytes. -/
  no_heap_acyclic : ∃ (src : AST.Model) (w : Solve.FMI3Model src) (sigs : List CTree.Signature),
    FMI3.ConstantFunctions.render w a.constantModel sigs = adapter ∧
    CCallPolicy.NoHeap (FMI3.ConstantFunctions.functions w a.constantModel sigs)
        FMI3.ConstantCallPolicy.bConstant = true ∧
    CCallPolicy.Acyclic (FMI3.ConstantFunctions.functions w a.constantModel sigs)
  /-- The rendered adapter satisfies the constant adapter contract for a scalar
  witness sharing the model name, relative to any static literal table. -/
  adapter : ∃ (src : AST.Model) (w : Solve.FMI3Model src), src.name = a.name ∧
    ∀ [FMI3.StaticLiterals], FMI3.ConstantAdapter.Contract w a.constantModel adapter
  /-- The constant model description decodes to the model identifiers. -/
  model_identifiers : FMI3.decodeModelIdentifiers
      (FMI3.TensorMetadata.constantModelDescription a.constantModel.shape a.constantModel.name)
    = some (a.name, FMI3.modelIdentifier a.name, FMI3.modelIdentifier a.name)
  /-- The declared instantiation token is exactly the one the factory validates. -/
  token : (FMI3.TensorMetadata.constantModelDescription a.constantModel.shape
      a.constantModel.name).attributes.lookup "instantiationToken"
    = some (FMI3.TensorMetadata.constantToken a.constantModel.name)
  /-- The actual model description bytes are the prepared constant document. -/
  metadata : XML.Document
    (FMI3.TensorMetadata.constantModelDescription a.constantModel.shape a.constantModel.name) metadata

/-- Bundle independently checked obligations into the composed contract,
mirroring `FMI3.sourceBuild_correct` and `tensorSourceBuild_correct`. -/
theorem constantSourceBuild_correct (a : ConstantArtifact input)
    (modelC buildDescription adapter metadata : String)
    (kernel : modelC = ConstantKernel.modelC)
    (kernelContract : Rumoca.CConstant.Contract ConstantKernel.rates ConstantKernel.modelC)
    (build : FMI3.Build.ArtifactContract a.name buildDescription)
    (adapter' : ∃ (src : AST.Model) (w : Solve.FMI3Model src), src.name = a.name ∧
      ∀ [FMI3.StaticLiterals], FMI3.ConstantAdapter.Contract w a.constantModel adapter)
    (identifiers : FMI3.decodeModelIdentifiers
        (FMI3.TensorMetadata.constantModelDescription a.constantModel.shape a.constantModel.name)
      = some (a.name, FMI3.modelIdentifier a.name, FMI3.modelIdentifier a.name))
    (token : (FMI3.TensorMetadata.constantModelDescription a.constantModel.shape
        a.constantModel.name).attributes.lookup "instantiationToken"
      = some (FMI3.TensorMetadata.constantToken a.constantModel.name))
    (metadataDocument : XML.Document
      (FMI3.TensorMetadata.constantModelDescription a.constantModel.shape a.constantModel.name) metadata) :
    ConstantSourceBuildContract a modelC buildDescription adapter metadata :=
  ⟨kernel, kernelContract, build,
    (by
      obtain ⟨src, w, _, contractFn⟩ := adapter'
      letI : FMI3.StaticLiterals := ⟨fun _ => none⟩
      obtain ⟨sigs, _, renderEq, covered, _⟩ := contractFn
      exact ⟨src, w, sigs, renderEq,
        FMI3.ConstantCallPolicy.constant_no_heap w a.constantModel sigs,
        FMI3.ConstantCallPolicy.constant_acyclic w a.constantModel sigs covered⟩),
    adapter', identifiers, token, metadataDocument⟩

end Rumoca

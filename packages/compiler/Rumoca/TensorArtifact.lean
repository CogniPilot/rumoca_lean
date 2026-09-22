import Rumoca.Compiler
import Rumoca.ArrayCompiler
import RumocaCore.Solve.TensorFMI3

/-! Source-owned tensor artifact and preparation facts, independent of backend
FMI adapter contracts. Declaration names and contents are preserved. -/
namespace Rumoca
open _root_.Parser
open Rumoca.Solve

/-- A tensor artifact: the located array parse together with its
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

/-- Parse the array profile and prepare its pointwise kernel. The CLI calls this
after the unit profile rejects; publication additionally requires its fixed
actual-artifact certificate. -/
def compileTensor (input : Source.InputRef) :
    Except (Source.Diagnostic input.source) (TensorArtifact input) := do
  let prepared ← ArrayCompiler.prepare input.source
  return ⟨prepared⟩

theorem compileTensor_eq (input : Source.InputRef) (prepared : ArrayCompiler.Prepared input.source)
    (parsed : ArrayCompiler.prepare input.source = .ok prepared) :
    compileTensor input = .ok ⟨prepared⟩ := by
  simp only [compileTensor, parsed, bind, Except.bind]
  rfl

/-- Total construction of a tensor artifact from an already certified array parse
and its resolution, mirroring the unit profile's `Artifact.ofParsed`. -/
def TensorArtifact.ofParsed (input : Source.InputRef) (parsed : ArrayProfile.Parsed input.source)
    (resolved : parsed.ast.Resolved) : TensorArtifact input :=
  ⟨ArrayCompiler.prepareParsed parsed.located resolved⟩

/-- The array driver implements the same successful parse and resolution for a
pinned AST. As in the unit profile's `compile_eq_parsed`, there is no additional
location-success assumption and the LR parser is not kernel-evaluated. -/
theorem compileTensor_eq_parsed (input : Source.InputRef) (parsed : ArrayProfile.Parsed input.source)
    (resolved : parsed.ast.Resolved) :
    compileTensor input = .ok (TensorArtifact.ofParsed input parsed resolved) := by
  simp only [compileTensor, TensorArtifact.ofParsed, bind, Except.bind,
    ArrayCompiler.prepare_eq_parsed parsed resolved]
  rfl

/-- Every resolvable array-profile source in the existing lexical/AST
specification compiles, with its parsed AST pinned to the given model. This is
the array analogue of the unit profile's `compile_complete`. -/
theorem compileTensor_complete (input : Source.InputRef) (m : ArrayProfile.Model)
    (syntaxValid : Lexes input.source.toList (ArrayProfile.actions.tokens m))
    (resolved : m.Resolved) :
    ∃ a, compileTensor input = .ok a ∧ a.prepared.parsed.parsed.ast = m :=
  let parsed : ArrayProfile.Parsed input.source :=
    ⟨ArrayProfile.actions.tokens m, m, (lex_correct input.source _).mpr syntaxValid,
      ParserActions.parseTokens_complete ArrayProfile.actions m⟩
  ⟨TensorArtifact.ofParsed input parsed resolved,
    compileTensor_eq_parsed input parsed resolved, rfl⟩

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

end Rumoca

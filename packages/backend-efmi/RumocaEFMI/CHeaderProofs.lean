import RumocaEFMI.ProductionCode
import Parser.Scanner
import RumocaEFMI.CInterface
import RumocaC.Body

open _root_.Parser

/-! The declared types of the current C interface, including its status return.
This is the fixed tiny header grammar, not a general C declaration parser.
It is independent of the header renderer: changing any alias, field or type
requires re-establishing the concrete-token and declared-type theorems.
The meanings of C's `double`, `int32_t`, object layout and preprocessing retain
the platform boundary documented for the target semantics. -/
namespace Rumoca.EFMI.CHeader
open CMemory


def returnValue (name : String) (value : Value) : Option Value := do
  let scalar ← scalarNamed name declarations
  convert scalar.memoryType value

/-- The shared C interpreter uses the aliases from these declaration nodes. -/
theorem interface_alias (scalar : Scalar) :
    cInterface.types scalar.alias = some scalar.memoryType := by
  cases scalar <;> rfl

/-- Header return conversion and shared C execution agree for every value. -/
theorem interface_return (scalar : Scalar) (value : Value) :
    CBody.cast (interface := cInterface) scalar.alias value =
      returnValue scalar.alias value := by
  cases scalar <;> rfl

/-- Independent token grammar: two aliases and a structure with three fields.
All declaration and field identifiers in this profile are legal and distinct
C identifiers; no producer-provided spelling supplies these tokens. -/
def tokens : List Token :=
  ["typedef", "double", "EfmiReal", ";", "typedef", "int32_t", "EfmiStatus", ";",
   "typedef", "struct", "{", "EfmiReal", "x", ";", "EfmiReal", "samplePeriod", ";",
   "EfmiStatus", "errorSignalStatus", ";",
   "}", "Model", ";"].map Token.literal

def scanner : Scanner.Config where
  wordStart := identStart
  wordRest := identRest
  numberRest := identRest
  classify := Token.literal
  single := fun c => ['{', '}', ';'].contains c
  pair := fun _ => none

def Declares (chars : List Char) : Prop := Scanner.Lexes scanner chars tokens

def text : String :=
  "typedef double EfmiReal;\ntypedef int32_t EfmiStatus;\n" ++
  "typedef struct {\n  EfmiReal x;\n  EfmiReal samplePeriod;\n  EfmiStatus errorSignalStatus;\n} Model;\n\n"

set_option maxRecDepth 10000 in
theorem render_text : render = text := rfl

private theorem toOption_some {result : Except ε α}
    (h : result.toOption = some value) : result = .ok value := by
  cases result <;> simp_all [Except.toOption]

set_option maxRecDepth 10000 in
theorem header_declares : Declares render.toList := by
  apply Scanner.scan_sound (fuel := render.toList.length + 1) (total := render.toList.length)
  apply toOption_some
  rw [render_text]
  decide +kernel

theorem real_alias : scalarNamed "EfmiReal" declarations = some .real64 := rfl
theorem status_alias : scalarNamed "EfmiStatus" declarations = some .status32 := rfl
theorem model_fields : fieldsNamed "Model" declarations =
    some [⟨"x", .real64⟩, ⟨"samplePeriod", .real64⟩, ⟨"errorSignalStatus", .status32⟩] := rfl

theorem success_return : returnValue "EfmiStatus" (.integer 0) = some (.integer 0) := rfl

/-- Binding the complete C source to its declared interface. The following
function bodies are certified separately by `ProductionContract`. -/
structure Contract (source : String) : Prop where
  prefix_bytes : ∃ body, source.toList = C.preamble.toList ++ render.toList ++ body
  header_syntax : Declares render.toList
  real_type : scalarNamed "EfmiReal" declarations = some .real64
  status_type : scalarNamed "EfmiStatus" declarations = some .status32
  interface_types : ∀ (scalar : Scalar), cInterface.types scalar.alias = some scalar.memoryType
  interface_returns : ∀ (scalar : Scalar) (value : Value),
    CBody.cast (interface := cInterface) scalar.alias value = returnValue scalar.alias value
  storage : fieldsNamed "Model" declarations =
    some [⟨"x", .real64⟩, ⟨"samplePeriod", .real64⟩, ⟨"errorSignalStatus", .status32⟩]

theorem render_contract (module : Production.Module) : Contract module.render := by
  refine ⟨⟨(module.startup.render ++ module.recalibrate.render ++ module.doStep.render).toList, ?_⟩,
    header_declares, real_alias, status_alias, interface_alias, interface_return, model_fields⟩
  simp only [Production.Module.render, Production.preamble, String.toList_append, List.append_assoc]

end Rumoca.EFMI.CHeader

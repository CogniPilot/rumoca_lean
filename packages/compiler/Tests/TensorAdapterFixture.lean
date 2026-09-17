import Rumoca.ArrayCompiler
import RumocaCore.Solve.FMI3
import RumocaFMI3.TensorAdapterPrinter
import RumocaFMI3.TensorStorageCode
import Tests.TensorMetadataFixture
import ProofAudit.Audit

/-! Package-level check that the development `TensorSquare` profile renders to a
concrete tensor FMI 3 adapter whose declaration preamble carries the tensor
instance record layout and whose function section tokenizes maximally under the
shared C scanner as the tensor function list. The tensor renderer needs a scalar
model witness for the model-independent bodies and numerical kernel (`scalarModel`,
built through the same checked parse/lower/prepare path as the unit profile) and
the tensor kernel witness (the `TensorSquare` fixture). The native regression
executable ties the actual `ArrayCompiler.prepare` kernel to this fixture and
retains the rendered adapter bytes under `build/tensor-fmi/`.

This fixture is a test artifact only and is not part of production emission. -/
namespace Rumoca.Tests.TensorAdapterFixture
open Rumoca Rumoca.Solve Rumoca.Tensor Rumoca.FMI3
open CTree CTree.Printer

/-! ### Scalar model witness for the model-independent adapter bodies -/

def scalarSource : AST.Model := ⟨"TensorSquare", "x", "x", "TensorSquare"⟩

def scalarInput : Parser.Source.InputRef :=
  .single "rumoca-check:/fmi3/TensorSquare.mo"
    "model TensorSquare Real x; equation der(x) = 1; end TensorSquare;"

def scalarParsed : Parsed scalarInput.source :=
  ⟨scalarSource.tokens, scalarSource, by rfl, parseTokens_complete scalarSource⟩

def scalarModel : Solve.FMI3Model scalarSource :=
  (Solve.lower (DAE.lower
    (Flat.lower (Provenance.Context.ofLocated scalarInput scalarParsed.located) ⟨rfl, rfl⟩))).prepareFMI3

/-! ### The rendered adapter over a representative dispatched signature list -/

/-- A representative slice of the pinned header signatures whose names dispatch
to the shape-dependent tensor bodies. Each is one of the tensor bodies' own
printable signatures, so the render contains those tensor bodies verbatim. -/
def signatures : List Signature :=
  [TensorReset.signature, TensorNominals.signature, TensorSetTime.signature,
   TensorDoStep.signature, TensorLifecycleModes.signature .terminate,
   TensorCountQueries.signature false, TensorCountQueries.signature true]

theorem signatures_printable :
    ∀ sig ∈ signatures, SignaturePrintable RuntimePrinter.typedefs sig := by
  intro sig member
  simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact TensorReset.signature_printable
  · exact TensorNominals.signature_printable
  · exact TensorSetTime.signature_printable
  · exact TensorDoStep.signature_printable
  · exact TensorLifecycleModes.signature_printable .terminate
  · exact TensorCountQueries.signature_printable false
  · exact TensorCountQueries.signature_printable true

/-- The tensor model kernel witness: the development `TensorSquare` fixture. -/
def tensorModel : TensorFMI3Model ⟨[2]⟩ := Tests.TensorMetadataFixture.fixtureModel

/-- The concrete rendered tensor adapter bytes for the `TensorSquare` profile. -/
def adapterBytes : String := TensorFunctions.render scalarModel tensorModel signatures

/-! ### The applied grammar / tokenization checks -/

/-- The function section following the fixed tensor declaration preamble
tokenizes maximally as the tensor function list, the tensor analog of the scalar
adapter's function-section grammar check. -/
theorem fixture_function_section :
    TensorAdapterPrinter.FunctionsContract scalarModel tensorModel signatures adapterBytes :=
  TensorAdapterPrinter.rendered_contract scalarModel tensorModel signatures signatures_printable

/-- The declaration preamble is the tensor storage block: the shared header
inclusion followed by the tensor instance record layout, which tokenizes under
the shared C scanner. -/
theorem fixture_preamble_tokenizes :
    ∃ tokens, ∀ rest, CTokens.Prefix
      ((TensorStorage.storageRender ⟨[2]⟩ true).toList ++ rest) tokens rest :=
  TensorStorage.storage_printed ⟨[2]⟩ true

/-- The declared record member names are exactly the ones `TensorInstance`
addresses. -/
theorem fixture_preamble_layout :
    (TensorStorage.regionMembers ⟨[2]⟩ true).map TensorStorage.Member.baseName
      = TensorInstance.fieldNames :=
  TensorStorage.layout_names ⟨[2]⟩

/-- The adapter's function prefix names the same model identifier the tensor
model description decodes to. -/
theorem fixture_identifier :
    decodeModelIdentifiers (TensorMetadata.modelDescription tensorModel)
      = some (tensorModel.name, modelIdentifier tensorModel.name, modelIdentifier tensorModel.name) :=
  TensorMetadata.modelIdentifiers_decode tensorModel

end Rumoca.Tests.TensorAdapterFixture

#audit axioms Rumoca.Tests.TensorAdapterFixture.fixture_function_section
#audit axioms Rumoca.Tests.TensorAdapterFixture.fixture_preamble_tokenizes
#audit axioms Rumoca.Tests.TensorAdapterFixture.fixture_preamble_layout
#audit axioms Rumoca.Tests.TensorAdapterFixture.fixture_identifier

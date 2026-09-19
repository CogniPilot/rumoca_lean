import RumocaCore.Solve.ConstantFMI3
import RumocaFMI3.ConstantAdapterPrinter
import RumocaFMI3.ConstantFunctions
import RumocaFMI3.TensorStorageCode
import RumocaFMI3.TensorMetadata
import Tests.TensorAdapterFixture
import ProofAudit.Audit

/-! Package-level check that the development `ConstantRates` profile renders to a
concrete constant-rate FMI 3 adapter whose declaration preamble carries the
no-input, no-output constant instance record layout and whose function section
tokenizes maximally under the shared C scanner as the constant function list. The
constant renderer needs a scalar model witness for the model-independent bodies
(reused from the tensor fixture's checked parse/lower/prepare path) and the
constant kernel witness (the `ConstantRates` fixture rates). The native regression
executable ties the actual `ConstantCompiler.prepare` kernel to this fixture and
retains the rendered adapter bytes under `build/constant-fmi/`.

This fixture is a test artifact only and is not part of production emission. -/
namespace Rumoca.Tests.ConstantAdapterFixture
open Rumoca Rumoca.Solve Rumoca.Tensor Rumoca.FMI3
open CTree CTree.Printer

/-! ### The constant-rate model kernel witness -/

/-- The prepared constant-rate IVP for the development `ConstantRates` fixture: two
states with the signed decimal rates `der(x) = 2.5` and `der(y) = -1`. -/
def fixtureIVP : ConstantProfile.ConstantIVP 2 :=
  ⟨![⟨1, 25, -1⟩, ⟨-1, 1, 0⟩]⟩

def constantModel : Solve.ConstantFMI3Model 2 := ⟨"ConstantRates", fixtureIVP⟩

/-- The scalar model witness for the model-independent adapter bodies, reused from
the tensor fixture's checked parse/lower/prepare path. -/
def scalarModel : Solve.FMI3Model Tests.TensorAdapterFixture.scalarSource :=
  Tests.TensorAdapterFixture.scalarModel

/-! ### The rendered adapter over a representative dispatched signature list -/

/-- A representative slice of the pinned header signatures whose names dispatch to
the constant-specific bodies (`fmi3DoStep`, `fmi3GetContinuousStateDerivatives`,
`fmi3GetFloat64`, `fmi3SetFloat64`) and the reused tensor bodies. -/
def signatures : List Signature :=
  [TensorReset.signature, TensorSetTime.signature, TensorDoStep.signature,
   DerivativeCalls.signature, Float64Calls.signature false, Float64Calls.signature true]

theorem signatures_printable :
    ∀ sig ∈ signatures, SignaturePrintable RuntimePrinter.typedefs sig := by
  intro sig member
  simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact TensorReset.signature_printable
  · exact TensorSetTime.signature_printable
  · exact TensorDoStep.signature_printable
  · exact TensorContinuousStates.derivSignature_printable
  · exact TensorFloat64.signature_printable false
  · exact TensorFloat64.signature_printable true

/-- The concrete rendered constant adapter bytes for the `ConstantRates` profile. -/
def adapterBytes : String := ConstantFunctions.render scalarModel constantModel signatures

/-! ### The applied grammar / tokenization checks -/

/-- The function section following the fixed constant declaration preamble tokenizes
maximally as the constant function list, the constant analog of the scalar adapter's
function-section grammar check. -/
theorem fixture_function_section :
    ConstantAdapterPrinter.FunctionsContract scalarModel constantModel signatures adapterBytes :=
  ConstantAdapterPrinter.rendered_contract scalarModel constantModel signatures signatures_printable

/-- The declaration preamble is the constant storage block: the shared header
inclusion followed by the no-input, no-output constant instance record layout,
which tokenizes under the shared C scanner. -/
theorem fixture_preamble_tokenizes :
    ∃ tokens, ∀ rest, CTokens.Prefix
      ((TensorStorage.storageRenderG ⟨[2]⟩ false false).toList ++ rest) tokens rest :=
  TensorStorage.storageG_printed ⟨[2]⟩ false false

/-- The declared record member names are exactly the time base, state and derivative
`TensorInstance` addresses in the constant profile. -/
theorem fixture_preamble_layout :
    (TensorStorage.regionMembersG ⟨[2]⟩ false false).map TensorStorage.Member.baseName
      = [TensorInstance.timeName, TensorInstance.stateName, TensorInstance.derivativeName] :=
  TensorStorage.layout_names_constant ⟨[2]⟩

/-- The adapter's function prefix names the same model identifier the constant model
description decodes to. -/
theorem fixture_identifier :
    decodeModelIdentifiers (TensorMetadata.constantModelDescription constantModel.shape constantModel.name)
      = some (constantModel.name, modelIdentifier constantModel.name, modelIdentifier constantModel.name) :=
  TensorMetadata.constant_modelIdentifiers_decode constantModel.shape constantModel.name

end Rumoca.Tests.ConstantAdapterFixture

#audit axioms Rumoca.Tests.ConstantAdapterFixture.fixture_function_section
#audit axioms Rumoca.Tests.ConstantAdapterFixture.fixture_preamble_tokenizes
#audit axioms Rumoca.Tests.ConstantAdapterFixture.fixture_preamble_layout
#audit axioms Rumoca.Tests.ConstantAdapterFixture.fixture_identifier

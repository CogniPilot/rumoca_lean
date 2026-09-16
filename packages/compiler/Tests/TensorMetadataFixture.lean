import Rumoca.ArrayCompiler
import RumocaFMI3.TensorMetadata
import ProofAudit.Audit

/-! Package-level check that the development `TensorSquare` profile renders to
concrete, well-formed tensor FMI 3 model-description bytes. The tensor model
description depends only on the model name, the tensor shape and whether the
prepared problem carries a diagonal (Jacobian) output, so this literal stands in
for the parsed `Rumoca.ArrayCompiler.prepare` kernel; the native regression
executable ties the actual prepared kernel to this fixture. This fixture is a
test artifact only and is not part of production emission. -/
namespace Rumoca.Tests.TensorMetadataFixture
open Rumoca Rumoca.Solve Rumoca.Tensor

/-- A literal pointwise problem for the development `TensorSquare` shape, with a
prepared diagonal (Jacobian) observation. -/
def fixtureIVP : PointwiseIVP ⟨[2]⟩ where
  initialProgram := Solve.Tensor.fill ⟨[2]⟩ .zero
  derivative := ArrayProfile.squareProgram ⟨[2]⟩
  diagonal := some (ArrayProfile.squareJacobianProgram ⟨[2]⟩)

def fixtureModel : TensorFMI3Model ⟨[2]⟩ := ⟨"TensorSquare", fixtureIVP⟩

theorem fixture_hasOutput : fixtureModel.hasOutput = true := rfl

/-- The development fixture renders to concrete, well-formed XML bytes. -/
theorem fixture_document :
    XML.Document (FMI3.TensorMetadata.modelDescription fixtureModel)
      (XML.document (FMI3.TensorMetadata.modelDescription fixtureModel)) :=
  FMI3.TensorMetadata.document fixtureModel (by decide)

end Rumoca.Tests.TensorMetadataFixture

#audit axioms Rumoca.Tests.TensorMetadataFixture.fixture_document
#audit axioms Rumoca.Tests.TensorMetadataFixture.fixture_hasOutput

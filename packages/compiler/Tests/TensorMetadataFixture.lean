import Rumoca.ArrayCompiler
import RumocaCore.Array.Interface
import RumocaFMI3.TensorMetadata
import ProofAudit.Audit

/-! Package-level check that the development `TensorSquare` profile renders to
concrete, well-formed tensor FMI 3 model-description bytes. The tensor model
description depends only on the model name and the declared interface of the
source, so this literal AST and kernel stand in for the parsed
`Rumoca.ArrayCompiler.prepare` result; the native regression executable ties the
actual prepared model to this fixture. This fixture is a
test artifact only and is not part of production emission. -/
namespace Rumoca.Tests.TensorMetadataFixture
open Rumoca Rumoca.Solve Rumoca.Tensor

/-- A literal pointwise problem for the development `TensorSquare` shape, with a
prepared diagonal (Jacobian) observation. -/
def fixtureIVP : PointwiseIVP ⟨[2]⟩ where
  initialProgram := Solve.Tensor.fill ⟨[2]⟩ .zero
  derivative := ArrayProfile.squareProgram ⟨[2]⟩
  diagonal := some (ArrayProfile.squareJacobianProgram ⟨[2]⟩)

/-- The literal `TensorSquare` source AST whose declarations the fixture exports. -/
def fixtureAst : ArrayProfile.Model :=
  ⟨⟨"TensorSquare", "u", "x", "start", "fixed"⟩,
   .jacobian "J" "x" ⟨"u", "u"⟩ "J" ⟨"jacobian", ⟨"u", "u"⟩, "u"⟩, "TensorSquare"⟩

def fixtureModel : TensorFMI3Model ⟨[2]⟩ := ⟨"TensorSquare", fixtureIVP, fixtureAst.interface⟩

theorem fixture_hasOutput : fixtureModel.hasOutput = true := rfl

/-- The development fixture renders to concrete, well-formed XML bytes. -/
theorem fixture_document :
    XML.Document (FMI3.TensorMetadata.modelDescription fixtureModel)
      (XML.document (FMI3.TensorMetadata.modelDescription fixtureModel)) :=
  FMI3.DeclaredMetadata.document _ _ _ (by decide) (by decide) (by decide)

end Rumoca.Tests.TensorMetadataFixture

#audit axioms Rumoca.Tests.TensorMetadataFixture.fixture_document
#audit axioms Rumoca.Tests.TensorMetadataFixture.fixture_hasOutput

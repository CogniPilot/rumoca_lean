import RumocaFMI3.Metadata
import RumocaFMI3.SourceLinkageProofs
import RumocaCore.Solve.TensorFMI3
import RumocaCore.Solve.ConstantFMI3

/-! The tensor and constant-rate model descriptions: the declared-interface
document (`DeclaredMetadata.modelDescription`) of each prepared model, under
the profile's instantiation token. Array variables keep their declared
`Dimension` extents; the variables, value references and model structure are
those of the shared builder, so every theorem of `DeclaredMetadata` applies. -/
namespace Rumoca.FMI3.TensorMetadata
open XML Rumoca.Solve

/-- The tensor model's instantiation token (FMI 3.0.2 §2.4.1 `instantiationToken`),
the tensor namespace paired with the model name. The tensor factory validates this
literal, and it is the `instantiationToken` attribute of the model description. -/
def token (m : TensorFMI3Model shape) : String := "lean-rumoca-tensor-v1:" ++ m.name

/-- The tensor model description of a prepared `TensorFMI3Model`. -/
def modelDescription (m : TensorFMI3Model shape) : Element :=
  DeclaredMetadata.modelDescription m.name (token m) m.interface

/-- The model description's declared `instantiationToken` attribute is exactly the
tensor token the tensor factory validates (FMI 3.0.2 §2.4.1). -/
theorem token_attribute (m : TensorFMI3Model shape) :
    (modelDescription m).attributes.lookup "instantiationToken" = some (token m) := rfl

theorem modelIdentifiers_decode (m : TensorFMI3Model shape) :
    decodeModelIdentifiers (modelDescription m)
      = some (m.name, modelIdentifier m.name, modelIdentifier m.name) :=
  DeclaredMetadata.modelIdentifiers_decode _ _ _

/-- The constant-rate model's instantiation token. -/
def constantToken (name : String) : String := "lean-rumoca-constant-v1:" ++ name

/-- The constant-rate model description of a prepared `ConstantFMI3Model`: one
scalar variable per source state, each followed by its derivative. -/
def constantModelDescription (m : ConstantFMI3Model n) : Element :=
  DeclaredMetadata.modelDescription m.name (constantToken m.name) m.interface

theorem constantToken_attribute (m : ConstantFMI3Model n) :
    (constantModelDescription m).attributes.lookup "instantiationToken"
      = some (constantToken m.name) := rfl

theorem constant_modelIdentifiers_decode (m : ConstantFMI3Model n) :
    decodeModelIdentifiers (constantModelDescription m)
      = some (m.name, modelIdentifier m.name, modelIdentifier m.name) :=
  DeclaredMetadata.modelIdentifiers_decode _ _ _

end Rumoca.FMI3.TensorMetadata

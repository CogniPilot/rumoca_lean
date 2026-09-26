import RumocaCore.Solve.FMI3
import RumocaFMI3.BuildDescription
import RumocaFMI3.DeclaredMetadata

namespace Rumoca.FMI3
open XML

def token (m : Solve.FMI3Model source) : String :=
  "lean-rumoca-unit-v1:" ++ m.name ++ ":" ++ m.stateName

/-- The unit model description: the declared-interface document of the unit
source's one scalar state. -/
def modelDescription (m : Solve.FMI3Model source) : Element :=
  DeclaredMetadata.modelDescription m.name (token m) m.interface

private theorem modelDescription_rendered (m : Solve.FMI3Model source) : modelDescription m =
  ⟨"fmiModelDescription", [("fmiVersion", "3.0"), ("modelName", m.name),
    ("instantiationToken", token m), ("generationTool", "lean_rumoca")], [
    ⟨"ModelExchange", [("modelIdentifier", modelIdentifier m.name)], [], ""⟩,
    ⟨"CoSimulation", [("modelIdentifier", modelIdentifier m.name),
      ("canHandleVariableCommunicationStepSize", "true"), ("fixedInternalStepSize", "1")], [], ""⟩,
    ⟨"LogCategories", [], [⟨"Category", [("name", "logStatus")], [], ""⟩], ""⟩,
    ⟨"DefaultExperiment", [("startTime", "0"), ("stopTime", "3"), ("stepSize", "1")], [], ""⟩,
    ⟨"ModelVariables", [], [
      ⟨"Float64", [("name", Solve.timeName), ("valueReference", "0"),
        ("causality", "independent"), ("variability", "continuous")], [], ""⟩,
      ⟨"Float64", [("name", m.stateName), ("valueReference", toString 1),
        ("causality", "local"), ("variability", "continuous"), ("initial", "exact"),
        ("start", DeclaredMetadata.startValue Tensor.scalar m.solve.initial.initial)], [], ""⟩,
      ⟨"Float64", [("name", m.derivativeName), ("valueReference", toString 2),
        ("causality", "local"), ("variability", "continuous"),
        ("initial", "calculated"), ("derivative", toString 1)], [], ""⟩], ""⟩,
    ⟨"ModelStructure", [], [
      ⟨"ContinuousStateDerivative", [("valueReference", toString 2), ("dependencies", "")], [], ""⟩,
      ⟨"InitialUnknown", [("valueReference", toString 2), ("dependencies", "")], [], ""⟩], ""⟩], ""⟩ := by
  rfl

/-- The unit document the declared-interface builder produces: the time base,
the state at reference `1` with its completed start value and its derivative at
reference `2`, which is the continuous-state derivative and the only initial
unknown. -/
theorem modelDescription_eq (m : Solve.FMI3Model source) : modelDescription m =
  ⟨"fmiModelDescription", [("fmiVersion", "3.0"), ("modelName", m.name),
    ("instantiationToken", token m), ("generationTool", "lean_rumoca")], [
    ⟨"ModelExchange", [("modelIdentifier", modelIdentifier m.name)], [], ""⟩,
    ⟨"CoSimulation", [("modelIdentifier", modelIdentifier m.name),
      ("canHandleVariableCommunicationStepSize", "true"), ("fixedInternalStepSize", "1")], [], ""⟩,
    ⟨"LogCategories", [], [⟨"Category", [("name", "logStatus")], [], ""⟩], ""⟩,
    ⟨"DefaultExperiment", [("startTime", "0"), ("stopTime", "3"), ("stepSize", "1")], [], ""⟩,
    ⟨"ModelVariables", [], [
      ⟨"Float64", [("name", Solve.timeName), ("valueReference", "0"),
        ("causality", "independent"), ("variability", "continuous")], [], ""⟩,
      ⟨"Float64", [("name", m.stateName), ("valueReference", "1"),
        ("causality", "local"), ("variability", "continuous"), ("initial", "exact"),
        ("start", DeclaredMetadata.startValue Tensor.scalar m.solve.initial.initial)], [], ""⟩,
      ⟨"Float64", [("name", m.derivativeName), ("valueReference", "2"),
        ("causality", "local"), ("variability", "continuous"),
        ("initial", "calculated"), ("derivative", "1")], [], ""⟩], ""⟩,
    ⟨"ModelStructure", [], [
      ⟨"ContinuousStateDerivative", [("valueReference", "2"), ("dependencies", "")], [], ""⟩,
      ⟨"InitialUnknown", [("valueReference", "2"), ("dependencies", "")], [], ""⟩], ""⟩], ""⟩ := by
  have one : toString (1 : Nat) = "1" := by decide +kernel
  have two : toString (2 : Nat) = "2" := by decide +kernel
  rw [modelDescription_rendered, one, two]

theorem metadata_name (m : Solve.FMI3Model source) :
    (modelDescription m).attributes.lookup "modelName" = some source.name := by
  rfl

end Rumoca.FMI3

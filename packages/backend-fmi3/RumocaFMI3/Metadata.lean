import RumocaCore.Solve.FMI3
import XML.Basic

namespace Rumoca.FMI3
open XML

def modelIdentifier : String := "RumocaModel"
def token (m : Solve.FMI3Model source) : String :=
  "lean-rumoca-unit-v1:" ++ m.name ++ ":" ++ m.stateName

def modelDescription (m : Solve.FMI3Model source) : Element :=
  ⟨"fmiModelDescription", [("fmiVersion", "3.0"), ("modelName", m.name),
    ("instantiationToken", token m), ("generationTool", "lean_rumoca")], [
    ⟨"ModelExchange", [("modelIdentifier", modelIdentifier)], [], ""⟩,
    ⟨"CoSimulation", [("modelIdentifier", modelIdentifier),
      ("canHandleVariableCommunicationStepSize", "true"), ("fixedInternalStepSize", "1")], [], ""⟩,
    ⟨"LogCategories", [], [⟨"Category", [("name", "logStatus")], [], ""⟩], ""⟩,
    ⟨"DefaultExperiment", [("startTime", "0"), ("stopTime", "3"), ("stepSize", "1")], [], ""⟩,
    ⟨"ModelVariables", [], [
      ⟨"Float64", [("name", m.timeName), ("valueReference", "0"),
        ("causality", "independent"), ("variability", "continuous")], [], ""⟩,
      ⟨"Float64", [("name", m.stateName), ("valueReference", "1"),
        ("causality", "local"), ("variability", "continuous"),
        ("initial", "exact"), ("start", "0")], [], ""⟩,
      ⟨"Float64", [("name", m.derivativeName), ("valueReference", "2"),
        ("causality", "local"), ("variability", "continuous"),
        ("initial", "calculated"), ("derivative", "1")], [], ""⟩], ""⟩,
    ⟨"ModelStructure", [], [
      ⟨"ContinuousStateDerivative", [("valueReference", "2"), ("dependencies", "")], [], ""⟩,
      ⟨"InitialUnknown", [("valueReference", "2"), ("dependencies", "")], [], ""⟩], ""⟩], ""⟩

def buildDescription : Element :=
  ⟨"fmiBuildDescription", [("fmiVersion", "3.0")], [
    ⟨"BuildConfiguration", [("modelIdentifier", modelIdentifier)], [
      ⟨"SourceFileSet", [("language", "C11")], [
        ⟨"SourceFile", [("name", "model.c")], [], ""⟩,
        ⟨"SourceFile", [("name", "fmi3.c")], [], ""⟩], ""⟩], ""⟩], ""⟩

theorem metadata_name (m : Solve.FMI3Model source) :
    (modelDescription m).attributes.lookup "modelName" = some source.name := by
  rfl

end Rumoca.FMI3

import RumocaFMI3.CapabilityRejectionContract
import RumocaFMI3.ScheduledCreationContract
import RumocaC.PrinterCertificate
import Lean

/-! Fixed unsupported-call catalog for the pinned public prototypes. Every
entry is checked against actual header membership by the artifact checker.
Routing and execution are universal in the compiled Solve model. The catalog
does not declare every raw request legal under the FMI state machine. -/
namespace Rumoca.FMI3.CapabilityRejection
open CTree

def signatures : List CTree.Signature :=
  [(⟨"fmi3Status", "fmi3GetClock",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "valueReferences", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValueReferences", false⟩ : CTree.Parameter),
          (⟨"fmi3Clock", "values", true⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3SetClock",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "valueReferences", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValueReferences", false⟩ : CTree.Parameter),
          (⟨"const fmi3Clock", "values", true⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3GetNumberOfVariableDependencies",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"fmi3ValueReference", "valueReference", false⟩ : CTree.Parameter),
          (⟨"size_t *", "nDependencies", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3GetVariableDependencies",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"fmi3ValueReference", "dependent", false⟩ : CTree.Parameter),
          (⟨"size_t", "elementIndicesOfDependent", true⟩ : CTree.Parameter),
          (⟨"fmi3ValueReference", "independents", true⟩ : CTree.Parameter),
          (⟨"size_t", "elementIndicesOfIndependents", true⟩ : CTree.Parameter),
          (⟨"fmi3DependencyKind", "dependencyKinds", true⟩ : CTree.Parameter),
          (⟨"size_t", "nDependencies", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3GetFMUState",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"fmi3FMUState *", "FMUState", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3SetFMUState",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"fmi3FMUState", "FMUState", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3FreeFMUState",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"fmi3FMUState *", "FMUState", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3SerializedFMUStateSize",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"fmi3FMUState", "FMUState", false⟩ : CTree.Parameter),
          (⟨"size_t *", "size", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3SerializeFMUState",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"fmi3FMUState", "FMUState", false⟩ : CTree.Parameter),
          (⟨"fmi3Byte", "serializedState", true⟩ : CTree.Parameter),
          (⟨"size_t", "size", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3DeserializeFMUState",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3Byte", "serializedState", true⟩ : CTree.Parameter),
          (⟨"size_t", "size", false⟩ : CTree.Parameter),
          (⟨"fmi3FMUState *", "FMUState", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3GetDirectionalDerivative",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "unknowns", true⟩ : CTree.Parameter),
          (⟨"size_t", "nUnknowns", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "knowns", true⟩ : CTree.Parameter),
          (⟨"size_t", "nKnowns", false⟩ : CTree.Parameter),
          (⟨"const fmi3Float64", "seed", true⟩ : CTree.Parameter),
          (⟨"size_t", "nSeed", false⟩ : CTree.Parameter),
          (⟨"fmi3Float64", "sensitivity", true⟩ : CTree.Parameter),
          (⟨"size_t", "nSensitivity", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3GetAdjointDerivative",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "unknowns", true⟩ : CTree.Parameter),
          (⟨"size_t", "nUnknowns", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "knowns", true⟩ : CTree.Parameter),
          (⟨"size_t", "nKnowns", false⟩ : CTree.Parameter),
          (⟨"const fmi3Float64", "seed", true⟩ : CTree.Parameter),
          (⟨"size_t", "nSeed", false⟩ : CTree.Parameter),
          (⟨"fmi3Float64", "sensitivity", true⟩ : CTree.Parameter),
          (⟨"size_t", "nSensitivity", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3EnterConfigurationMode",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3ExitConfigurationMode",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3GetIntervalDecimal",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "valueReferences", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValueReferences", false⟩ : CTree.Parameter),
          (⟨"fmi3Float64", "intervals", true⟩ : CTree.Parameter),
          (⟨"fmi3IntervalQualifier", "qualifiers", true⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3GetIntervalFraction",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "valueReferences", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValueReferences", false⟩ : CTree.Parameter),
          (⟨"fmi3UInt64", "counters", true⟩ : CTree.Parameter),
          (⟨"fmi3UInt64", "resolutions", true⟩ : CTree.Parameter),
          (⟨"fmi3IntervalQualifier", "qualifiers", true⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3GetShiftDecimal",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "valueReferences", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValueReferences", false⟩ : CTree.Parameter),
          (⟨"fmi3Float64", "shifts", true⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3GetShiftFraction",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "valueReferences", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValueReferences", false⟩ : CTree.Parameter),
          (⟨"fmi3UInt64", "counters", true⟩ : CTree.Parameter),
          (⟨"fmi3UInt64", "resolutions", true⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3SetIntervalDecimal",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "valueReferences", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValueReferences", false⟩ : CTree.Parameter),
          (⟨"const fmi3Float64", "intervals", true⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3SetIntervalFraction",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "valueReferences", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValueReferences", false⟩ : CTree.Parameter),
          (⟨"const fmi3UInt64", "counters", true⟩ : CTree.Parameter),
          (⟨"const fmi3UInt64", "resolutions", true⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3SetShiftDecimal",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "valueReferences", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValueReferences", false⟩ : CTree.Parameter),
          (⟨"const fmi3Float64", "shifts", true⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3SetShiftFraction",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "valueReferences", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValueReferences", false⟩ : CTree.Parameter),
          (⟨"const fmi3UInt64", "counters", true⟩ : CTree.Parameter),
          (⟨"const fmi3UInt64", "resolutions", true⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3EnterStepMode",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3GetOutputDerivatives",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"const fmi3ValueReference", "valueReferences", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValueReferences", false⟩ : CTree.Parameter),
          (⟨"const fmi3Int32", "orders", true⟩ : CTree.Parameter),
          (⟨"fmi3Float64", "values", true⟩ : CTree.Parameter),
          (⟨"size_t", "nValues", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature),
    (⟨"fmi3Status", "fmi3ActivateModelPartition",
        [(⟨"fmi3Instance", "instance", false⟩ : CTree.Parameter),
          (⟨"fmi3ValueReference", "clockReference", false⟩ : CTree.Parameter),
          (⟨"fmi3Float64", "activationTime", false⟩ : CTree.Parameter)]⟩ :
      CTree.Signature)]

set_option maxHeartbeats 4000000 in
theorem routing {source : AST.Model} (model : Solve.FMI3Model source) :
    ∀ sig ∈ signatures, Runtime.body model sig = code := by
  simp only [signatures, List.forall_mem_cons]
  repeat' constructor
  all_goals simp [Runtime.body, code, message]
  all_goals
    intro _ impossible
    exfalso
    revert impossible
    decide +kernel

theorem profiles : ∀ sig ∈ signatures, Profile sig sig.parameters.tail := by
  simp only [signatures, List.forall_mem_cons, List.not_mem_nil, false_implies]
  repeat' apply And.intro
  all_goals first
    | exact fun _ => True.intro
    | (refine ⟨rfl, rfl, by decide +kernel, ?_⟩
       intro name member
       simp only [List.mem_cons, List.not_mem_nil, or_false] at member
       rcases member with rfl | rfl | rfl <;> simp_all)

open Lean Elab Command in
run_cmd do
  let proof ← CTree.Printer.Certificate.signaturesProof (← `(term| RuntimePrinter.typedefs)) signatures
  let theoremName := mkIdent `_root_.Rumoca.FMI3.CapabilityRejection.signatures_printable
  elabCommand (← `(command| theorem $theoremName:ident :
    ∀ sig ∈ signatures, CTree.Printer.SignaturePrintable RuntimePrinter.typedefs sig := $proof))

noncomputable section
def FamilyContract (model : Solve.FMI3Model source) (sigs : List Signature) : Prop :=
  ∀ sig ∈ signatures, FunctionContract model sigs sig sig.parameters.tail (Runtime.function model sig).render

theorem family_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (members : ∀ sig ∈ signatures, sig ∈ sigs) : FamilyContract model sigs := by
  intro sig member
  exact rendered_contract model sigs (profiles sig member) (routing model sig member)
    (signatures_printable sig member) unique (members sig member)

structure AllContract (model : Solve.FMI3Model source) (sigs : List Signature) : Prop where
  family : FamilyContract model sigs
  scheduled : ScheduledCreation.FunctionContract model sigs
    (Runtime.function model ScheduledCreation.signature).render

theorem all_correct (model : Solve.FMI3Model source) (sigs : List Signature)
    (unique : ((LiteralPreparation.functions model sigs).map (fun fn => fn.signature.name)).Nodup)
    (members : ∀ sig ∈ signatures, sig ∈ sigs)
    (scheduled : ScheduledCreation.signature ∈ sigs) : AllContract model sigs :=
  ⟨family_correct model sigs unique members, ScheduledCreation.rendered_contract model sigs unique scheduled⟩

end
end Rumoca.FMI3.CapabilityRejection


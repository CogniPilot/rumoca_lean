import RumocaFMI3.TensorFamilyContracts
import RumocaFMI3.PublicAPICertificate
import RumocaFMI3.TensorVersion
import RumocaFMI3.TensorDebugLogging
import RumocaFMI3.TensorScheduledCreation
import RumocaFMI3.TensorDiscreteEvaluation
import RumocaFMI3.TensorDiscreteUpdate
import RumocaFMI3.TensorCompletedStep
import RumocaFMI3.TensorEventIndicators
import RumocaFMI3.TensorReset
import RumocaFMI3.TensorNominals
import RumocaFMI3.TensorCountQueries
import RumocaFMI3.TensorSetTime
import RumocaFMI3.TensorLifecycleModes
import RumocaFMI3.TensorDoStep
import RumocaFMI3.TensorFloat64Access
import RumocaFMI3.TensorContinuousStates
import RumocaFMI3.TensorStaticFactory
import RumocaFMI3.TensorFree
import RumocaFMI3.TensorStorageCode
import RumocaFMI3.TensorMetadata

/-! First tensor adapter contract skeleton. It binds the rendered text of the
tensor adapter function list to the model-free public-API coverage, the two
unsupported/absent-type family contracts over that list, and every proved
tensor behavioral function contract, in header order.

The contract is stated relative to one static literal table `[static]`, which
supplies the ambient C interface the accessor, factory and release contracts use;
the seven runtime-interface behavioral functions supply their own
floating-environment header, objects and literal addresses. This is not a
weakening of any conjunct: each behavioral contract is included exactly as its
proved product states it, with its own premises.

Two `fmi3DoStep` behaviors remain open inside `TensorDoStep.contract` itself (the
`fmi3Discard` off-grid composition and the header-aware floating-environment
interface); this skeleton includes that contract as proved and inherits exactly
those open items. This is a package-checked product only: no production artifact is
emitted, no CLI or grammar case is added, and no existing contract changes. -/
noncomputable section
namespace Rumoca.FMI3.TensorAdapter
open CTree CMemory CBody StaticFactory CLiteral.Interface
open TensorFunctions (functions render outputShape)

variable {source : AST.Model} {shape : Rumoca.Tensor.Shape}
variable [static : StaticLiterals]
private local instance adapterInterface : CInterface := cInterface static.addresses

/-- The tensor adapter contract for a rendered text: the located header list, its
distinct names, the model-free coverage, the two family contracts over the list,
and every proved tensor behavioral function contract with its explicit premises. -/
def Contract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (text : String) : Prop :=
  ∃ sigs : List Signature,
    ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup ∧
    render model m sigs = text ∧
    PublicAPI.Covered sigs ∧
    TensorAbsentVariables.FamilyContract model m sigs ∧
    TensorCapabilityRejection.FamilyContract model m sigs ∧
    -- Model-independent behavioral functions carried by the tensor record.
    TensorVersion.Contract model (Runtime.function model Version.signature).render ∧
    TensorEventIndicators.Contract model (Runtime.function model EventIndicatorCalls.signature).render ∧
    (∀ (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses),
      letI : CInterface := RuntimeEnvironment.interface header objects literals
      TensorDebugLogging.Contract literals model (Runtime.function model DebugLogging.signature).render) ∧
    (∀ (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses),
      letI : CInterface := RuntimeEnvironment.interface header objects literals
      TensorScheduledCreation.Contract literals model (Runtime.function model ScheduledCreation.signature).render) ∧
    (∀ (objects : Objects) (literals : CLiteralAddresses),
      letI : CInterface := executionInterface objects literals
      TensorDiscreteEvaluation.Contract model (Runtime.function model DiscreteEvaluation.signature).render) ∧
    (∀ (objects : Objects) (literals : CLiteralAddresses),
      letI : CInterface := executionInterface objects literals
      TensorDiscreteUpdate.Contract model (Runtime.function model DiscreteCalls.signature).render) ∧
    (∀ (objects : Objects) (literals : CLiteralAddresses),
      letI : CInterface := executionInterface objects literals
      TensorCompletedStep.Contract model (Runtime.function model CompletedCalls.signature).render) ∧
    -- Genuinely tensor bodies over the symbolic state volume.
    TensorReset.Contract shape (TensorReset.function shape).render ∧
    TensorNominals.Contract shape (TensorNominals.function shape).render ∧
    (∀ events, TensorCountQueries.Contract shape events (TensorCountQueries.function shape events).render) ∧
    TensorSetTime.Contract (TensorSetTime.function).render ∧
    (∀ ph, TensorLifecycleModes.Contract ph (TensorLifecycleModes.function ph).render) ∧
    TensorDoStep.Contract shape (TensorDoStep.function shape).render ∧
    -- Float64 and continuous-state accessors over the ambient static literal table.
    TensorFloat64.GetContract shape (outputShape m) (TensorFloat64.getFunction shape (outputShape m)).render ∧
    TensorFloat64.SetContract shape (TensorFloat64.setFunction shape).render ∧
    TensorContinuousStates.GetContract shape (TensorContinuousStates.getFunction shape).render ∧
    TensorContinuousStates.SetContract shape (TensorContinuousStates.setFunction shape).render ∧
    TensorContinuousStates.DerivContract shape (TensorContinuousStates.derivFunction shape).render ∧
    -- Factory and release over the static tensor instance pool.
    (∀ (E : Type) (prog : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
      TensorFactory.FunctionContract prog tag model shape) ∧
    (∀ (E : Type) (prog : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
      StaticRelease.Bindings prog tag → TensorFree.Contract prog tag) ∧
    -- Declaration preamble: the tensor storage block (`TensorStorage.declarations`)
    -- is the adapter's declaration preamble, the shared header inclusion followed
    -- by the tensor instance record layout the tensor bodies address. Its record
    -- member names and region extents agree with `TensorInstance.field`.
    (∃ before after : String,
      text = before ++ TensorStorage.declarations shape m.hasOutput ++ after) ∧
    (TensorStorage.declarations shape m.hasOutput).toList =
      Runtime.declarationPrefix.toList ++ (TensorStorage.storageRender shape m.hasOutput ++ "\n").toList ∧
    (TensorStorage.regionMembers shape true).map TensorStorage.Member.baseName = TensorInstance.fieldNames ∧
    TensorStorage.Member.region TensorInstance.stateName shape.volume ∈ TensorStorage.regionMembers shape m.hasOutput ∧
    (TensorStorage.Member.region TensorInstance.outputName ((Rumoca.Tensor.matrixShape shape.volume shape.volume).volume)
        ∈ TensorStorage.regionMembers shape true ∧
      (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume = shape.volume * shape.volume) ∧
    -- Identifier agreement: the adapter's function-prefix names the same model
    -- identifier the tensor model description decodes to
    -- (`TensorMetadata.modelIdentifiers_decode`).
    (∃ rest : String, text = "#define FMI3_FUNCTION_PREFIX " ++ modelIdentifier m.name ++ "_\n" ++ rest) ∧
    decodeModelIdentifiers (TensorMetadata.modelDescription m)
      = some (m.name, modelIdentifier m.name, modelIdentifier m.name)

/-- The tensor adapter contract holds for the rendered text of the function list,
given the located and distinct header signatures and the model-free coverage. -/
theorem render_contract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (covered : PublicAPI.Covered sigs)
    (absentMembers : ∀ ty write, AbsentVariables.signature ty write ∈ sigs)
    (capMembers : ∀ sig ∈ CapabilityRejection.signatures, sig ∈ sigs) :
    Contract model m (render model m sigs) :=
  ⟨sigs, unique, rfl, covered,
    TensorAbsentVariables.family_correct model m sigs unique absentMembers,
    TensorCapabilityRejection.family_correct model m sigs unique capMembers,
    TensorVersion.contract model,
    TensorEventIndicators.contract model,
    fun header objects literals => TensorDebugLogging.contract header objects literals model,
    fun header objects literals => TensorScheduledCreation.contract header objects literals model,
    fun objects literals => TensorDiscreteEvaluation.contract objects literals model,
    fun objects literals => TensorDiscreteUpdate.contract objects literals model,
    fun objects literals => TensorCompletedStep.contract objects literals model,
    TensorReset.contract shape,
    TensorNominals.contract shape,
    (fun events => TensorCountQueries.contract shape events),
    TensorSetTime.contract,
    (fun ph => TensorLifecycleModes.contract ph),
    TensorDoStep.contract shape,
    TensorFloat64.get_contract shape (outputShape m),
    TensorFloat64.set_contract shape,
    TensorContinuousStates.get_contract shape,
    TensorContinuousStates.set_contract shape,
    TensorContinuousStates.deriv_contract shape,
    (fun _E prog tag => TensorFactory.contract prog tag model shape),
    (fun _E prog tag bindings => TensorFree.contract prog tag bindings),
    ⟨functionPrefix m.name ++ "#include \"model.c\"\n",
      String.join (Runtime.helpers.map Function.render) ++
        String.join (sigs.map fun sig => (TensorFunctions.tensorFunction model m sig).render),
      by rw [render]; simp only [String.append_assoc]⟩,
    TensorStorage.declarations_header shape m.hasOutput,
    TensorStorage.layout_names shape,
    (TensorStorage.layout_state_extent shape m.hasOutput).1,
    TensorStorage.layout_output_extent shape,
    ⟨"#include \"model.c\"\n" ++ TensorStorage.declarations shape m.hasOutput ++
        String.join (Runtime.helpers.map Function.render) ++
        String.join (sigs.map fun sig => (TensorFunctions.tensorFunction model m sig).render),
      by rw [render, functionPrefix]; simp only [String.append_assoc]⟩,
    TensorMetadata.modelIdentifiers_decode m⟩

end Rumoca.FMI3.TensorAdapter
end

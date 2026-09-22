import RumocaFMI3.ConstantFamilyContracts
import RumocaFMI3.PreparedStepContract
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
import RumocaFMI3.ConstantDoStep
import RumocaFMI3.ConstantFloat64Access
import RumocaFMI3.ConstantDerivative
import RumocaFMI3.TensorContinuousStates
import RumocaFMI3.TensorStaticFactory
import RumocaFMI3.TensorFree
import RumocaFMI3.TensorStorageCode
import RumocaFMI3.TensorMetadata

/-! The constant-rate (`G01`) FMI 3 adapter contract skeleton, the constant analog
of `TensorAdapter.Contract`. It binds the rendered text of the constant adapter
function list to the model-free public-API coverage, the two unsupported/absent-type
family contracts over that list, and every proved constant (and reused tensor)
behavioral function contract, in header order.

The contract is stated relative to one static literal table `[static]`, which
supplies the ambient C interface the accessor, factory and release contracts use;
the seven runtime-interface behavioral functions supply their own
floating-environment header, objects and literal addresses. This is not a weakening
of any conjunct: each behavioral contract is included exactly as its proved product
states it, with its own premises.

The reused tensor behavioral contracts (reset, nominals, count queries, set-time,
lifecycle, continuous-state copies, factory and free) are universal in the state
shape and address only the time/state/derivative record members common to both the
tensor and constant records, so each instantiates at the constant state shape with
no re-proof; only the four constant-specific bodies (the Float64 accessors, the
constant derivative getter, the constant `fmi3DoStep`) carry constant-specific
contracts. This is a package-checked product only: no production artifact is
emitted, no CLI or grammar case is added, and no existing contract changes. -/
noncomputable section
namespace Rumoca.FMI3.ConstantAdapter
open CTree CMemory CBody StaticFactory CLiteral.Interface
open ConstantFunctions (functions render rates)

variable {source : AST.Model} {n : Nat}
variable [static : StaticLiterals]
private local instance adapterInterface : CInterface := cInterface static.addresses

/-- The constant adapter contract for a rendered text: the located header list, its
distinct names, the model-free coverage, the two family contracts over the list, and
every proved constant (and reused tensor) behavioral function contract with its
explicit premises. -/
def Contract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (text : String) : Prop :=
  ∃ sigs : List Signature,
    ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup ∧
    render model m sigs = text ∧
    StepEntry.signature ∈ sigs ∧
    (ConstantFunctions.prepare model m sigs).isSome = true ∧
    PreparedStep.ConstantContract model m sigs ∧
    (ConstantFunctions.program model m sigs).definitions "fmi3DoStep" =
      some (.tree ConstantDoStep.function) ∧
    (ConstantFunctions.program model m sigs).definitions "fail" =
      some (.tree Runtime.helpers[0]) ∧
    (∃ before after : String,
      text = before ++ ConstantDoStep.function.render ++ after) ∧
    PublicAPI.Covered sigs ∧
    ConstantAbsentVariables.FamilyContract model m sigs ∧
    ConstantCapabilityRejection.FamilyContract model m sigs ∧
    -- Model-independent behavioral functions carried by the constant record.
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
    -- Reused tensor bodies over the symbolic constant state volume.
    TensorReset.Contract m.shape (TensorReset.function m.shape).render ∧
    TensorNominals.Contract m.shape (TensorNominals.function m.shape).render ∧
    (∀ events, TensorCountQueries.Contract m.shape events (TensorCountQueries.function m.shape events).render) ∧
    TensorSetTime.Contract (TensorSetTime.function).render ∧
    (∀ ph, TensorLifecycleModes.Contract ph (TensorLifecycleModes.function ph).render) ∧
    -- The constant-specific `fmi3DoStep` over the constant instance record.
    (∀ (header : CFenv.Header), ConstantDoStep.Contract header (ConstantDoStep.function).render) ∧
    -- Constant Float64 accessors and reused continuous-state copies over the ambient
    -- static literal table.
    ConstantFloat64.GetContract m.shape (ConstantFloat64.getFunction m.shape).render ∧
    ConstantFloat64.SetContract m.shape (ConstantFloat64.setFunction m.shape).render ∧
    TensorContinuousStates.GetContract m.shape (TensorContinuousStates.getFunction m.shape).render ∧
    TensorContinuousStates.SetContract m.shape (TensorContinuousStates.setFunction m.shape).render ∧
    ConstantDerivative.DerivContract m.shape (ConstantDerivative.derivFunction m.shape).render ∧
    -- Factory and release over the static constant instance pool.
    (∀ (E : Type) (prog : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
      TensorFactory.FunctionContract prog tag model (TensorMetadata.constantToken m.name) m.shape) ∧
    (∀ (E : Type) (prog : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
      StaticRelease.Bindings prog tag → TensorFree.Contract prog tag) ∧
    -- Declaration preamble: the constant storage block (no input, no output) is the
    -- adapter's declaration preamble, the shared header inclusion followed by the
    -- constant-rate instance record layout the constant bodies address. Its record
    -- member names and region extents agree with `TensorInstance.field`.
    (∃ before after : String,
      text = before ++ ConstantFunctions.declarations m.shape (rates m) ++ after) ∧
    (ConstantFunctions.declarations m.shape (rates m)).toList =
      Runtime.declarationPrefix.toList ++
        (TensorStorage.storageRenderG m.shape false false ++
          ConstantFunctions.kernelPrototypes (rates m) ++ "\n").toList ∧
    (TensorStorage.regionMembersG m.shape false false).map TensorStorage.Member.baseName =
      [TensorInstance.timeName, TensorInstance.stateName, TensorInstance.derivativeName] ∧
    TensorStorage.Member.region TensorInstance.stateName m.shape.volume
        ∈ TensorStorage.regionMembersG m.shape false false ∧
    TensorStorage.Member.region TensorInstance.derivativeName m.shape.volume
        ∈ TensorStorage.regionMembersG m.shape false false ∧
    -- Identifier agreement: the adapter's function-prefix names the same model
    -- identifier the constant model description decodes to
    -- (`TensorMetadata.constant_modelIdentifiers_decode`).
    (∃ rest : String, text = "#define FMI3_FUNCTION_PREFIX " ++ modelIdentifier m.name ++ "_\n" ++ rest) ∧
    decodeModelIdentifiers (TensorMetadata.constantModelDescription m.shape m.name)
      = some (m.name, modelIdentifier m.name, modelIdentifier m.name) ∧
    -- Instantiation-token agreement: the constant factory validates exactly the
    -- token the constant model description declares as its `instantiationToken`
    -- attribute (`TensorMetadata.constantToken_attribute`, FMI 3.0.2 §2.4.1).
    (TensorMetadata.constantModelDescription m.shape m.name).attributes.lookup "instantiationToken"
      = some (TensorMetadata.constantToken m.name) ∧
    -- Call resolution: every function name the constant bodies call resolves. The
    -- three constant kernel entries are forward-declared in the preamble and resolve
    -- to their bound trees; their declared prototypes agree in arity and parameter
    -- roles with the arguments the constant derivative getter and step pass. The
    -- shared helpers the bodies call resolve to their defined trees.
    (∃ before after : String,
      text = before ++ ConstantFunctions.kernelPrototypes (rates m) ++ after) ∧
    ((∀ sig ∈ sigs, sig.name ≠ "rumoca_constant_rhs") →
      (ConstantFunctions.program model m sigs).definitions "rumoca_constant_rhs"
        = some (.tree (Rumoca.CConstant.rhsFunction (rates m)))) ∧
    ((∀ sig ∈ sigs, sig.name ≠ "rumoca_constant_step") →
      (ConstantFunctions.program model m sigs).definitions "rumoca_constant_step"
        = some (.tree (Rumoca.CConstant.stepFunction (rates m)))) ∧
    (Rumoca.CConstant.rhsFunction (rates m)).signature.parameters.length =
        ConstantDerivative.entryArgs.length ∧
    (Rumoca.CConstant.rhsFunction (rates m)).signature.parameters.map CTree.Parameter.name = ["der"] ∧
    (Rumoca.CConstant.stepFunction (rates m)).signature.parameters.length = 1 ∧
    (Rumoca.CConstant.stepFunction (rates m)).signature.parameters.map CTree.Parameter.name = ["x"] ∧
    (ConstantFunctions.program model m sigs).definitions ConstantFunctions.helpers[0].signature.name
        = some (.tree ConstantFunctions.helpers[0]) ∧
    (ConstantFunctions.program model m sigs).definitions Identity.function.signature.name
        = some (.tree Identity.function) ∧
    (ConstantFunctions.program model m sigs).definitions CAtomicScan.function.signature.name
        = some (.tree CAtomicScan.function)

/-- The constant adapter contract holds for the rendered text of the function list,
given the located and distinct header signatures and the model-free coverage. -/
theorem render_contract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (step : StepEntry.signature ∈ sigs)
    (covered : PublicAPI.Covered sigs)
    (absentMembers : ∀ ty write, AbsentVariables.signature ty write ∈ sigs)
    (capMembers : ∀ sig ∈ CapabilityRejection.signatures, sig ∈ sigs)
    (poolReady : (ConstantFunctions.prepare model m sigs).isSome = true) :
    Contract model m (render model m sigs) :=
  ⟨sigs, unique, rfl, step, poolReady, PreparedStep.constant_contract model m sigs step unique,
    ConstantFunctions.doStep_bound model m sigs unique step,
    ConstantFunctions.helpers_bound model m sigs Runtime.helpers[0]
      (by simp [ConstantFunctions.helpers, TensorFunctions.helpers]),
    ConstantFunctions.doStep_fragment model m sigs step, covered,
    ConstantAbsentVariables.family_correct model m sigs unique absentMembers,
    ConstantCapabilityRejection.family_correct model m sigs unique capMembers,
    TensorVersion.contract model,
    TensorEventIndicators.contract model,
    fun header objects literals => TensorDebugLogging.contract header objects literals model,
    fun header objects literals => TensorScheduledCreation.contract header objects literals model,
    fun objects literals => TensorDiscreteEvaluation.contract objects literals model,
    fun objects literals => TensorDiscreteUpdate.contract objects literals model,
    fun objects literals => TensorCompletedStep.contract objects literals model,
    TensorReset.contract m.shape,
    TensorNominals.contract m.shape,
    (fun events => TensorCountQueries.contract m.shape events),
    TensorSetTime.contract,
    (fun ph => TensorLifecycleModes.contract ph),
    (fun header => ConstantDoStep.contract header),
    ConstantFloat64.get_contract m.shape,
    ConstantFloat64.set_contract m.shape,
    TensorContinuousStates.get_contract m.shape,
    TensorContinuousStates.set_contract m.shape,
    ConstantDerivative.deriv_contract m.shape,
    (fun _E prog tag => TensorFactory.contract prog tag model (TensorMetadata.constantToken m.name) m.shape),
    (fun _E prog tag bindings => TensorFree.contract prog tag bindings),
    ⟨functionPrefix m.name ++ "#include \"model.c\"\n",
      String.join (ConstantFunctions.helpers.map Function.render) ++
        String.join (sigs.map fun sig => (ConstantFunctions.constantFunction model m sig).render),
      by rw [render]; simp only [String.append_assoc]⟩,
    (by simp [ConstantFunctions.declarations, String.toList_append]),
    TensorStorage.layout_names_constant m.shape,
    (TensorStorage.layout_state_extent_constant m.shape).1,
    (TensorStorage.layout_state_extent_constant m.shape).2,
    ⟨"#include \"model.c\"\n" ++ ConstantFunctions.declarations m.shape (rates m) ++
        String.join (ConstantFunctions.helpers.map Function.render) ++
        String.join (sigs.map fun sig => (ConstantFunctions.constantFunction model m sig).render),
      by rw [render, functionPrefix]; simp only [String.append_assoc]⟩,
    TensorMetadata.constant_modelIdentifiers_decode m.shape m.name,
    TensorMetadata.constantToken_attribute m.shape m.name,
    -- Call-resolution witnesses.
    ⟨functionPrefix m.name ++ "#include \"model.c\"\n" ++ Runtime.declarationPrefix ++
        TensorStorage.storageRenderG m.shape false false,
      "\n" ++ String.join (ConstantFunctions.helpers.map Function.render) ++
        String.join (sigs.map fun sig => (ConstantFunctions.constantFunction model m sig).render),
      by rw [render, ConstantFunctions.declarations]; simp only [String.append_assoc]⟩,
    (fun fresh => ConstantFunctions.kernel_entry_rhs model m sigs fresh),
    (fun fresh => ConstantFunctions.kernel_entry_step model m sigs fresh),
    (ConstantFunctions.rhs_prototype_matches_args (rates m)).1,
    (ConstantFunctions.rhs_prototype_matches_args (rates m)).2,
    (ConstantFunctions.step_prototype_matches_args (rates m)).1,
    (ConstantFunctions.step_prototype_matches_args (rates m)).2,
    ConstantFunctions.helpers_bound model m sigs ConstantFunctions.helpers[0]
      (by simp [ConstantFunctions.helpers, TensorFunctions.helpers]),
    ConstantFunctions.helpers_bound model m sigs Identity.function
      (by simp [ConstantFunctions.helpers, TensorFunctions.helpers]),
    ConstantFunctions.helpers_bound model m sigs CAtomicScan.function
      (by simp [ConstantFunctions.helpers, TensorFunctions.helpers])⟩

end Rumoca.FMI3.ConstantAdapter
end

import RumocaFMI3.IdentityFactoryEntry
import RumocaFMI3.CallTypes

/-! Fresh public ME/CS factory entry with every parameter from the pinned
prototype. Unused pointers are opaque and may be null. Size values have the
selected target's 64-bit range. Header/native ABI correspondence is separate. -/
noncomputable section
namespace Rumoca.FMI3.FactoryArguments
open CTree CMemory CBody

structure Raw where
  name : Option Address
  token : Option Address
  resource : Option Address
  visible : Bool
  logging : Bool
  environment : Option Address
  logger : Option Address
  events : Bool
  earlyReturn : Bool
  intermediateVariables : Option Address
  intermediateCount : Fin (2^64)
  intermediateUpdate : Option Address

def signature (kind : Kind) : Signature :=
  ⟨"fmi3Instance", Identity.factoryName kind,
    [⟨"fmi3String", "instanceName", false⟩,
     ⟨"fmi3String", "instantiationToken", false⟩,
     ⟨"fmi3String", "resourcePath", false⟩,
     ⟨"fmi3Boolean", "visible", false⟩,
     ⟨"fmi3Boolean", "loggingOn", false⟩] ++
    (match kind with | .me => [] | .cs => [
      ⟨"fmi3Boolean", "eventModeUsed", false⟩,
      ⟨"fmi3Boolean", "earlyReturnAllowed", false⟩,
      ⟨"const fmi3ValueReference", "requiredIntermediateVariables", true⟩,
      ⟨"size_t", "nRequiredIntermediateVariables", false⟩]) ++
    [⟨"fmi3InstanceEnvironment", "instanceEnvironment", false⟩,
     ⟨"fmi3LogMessageCallback", "logMessage", false⟩] ++
    (match kind with | .me => [] | .cs => [⟨"fmi3IntermediateUpdateCallback", "intermediateUpdate", false⟩])⟩

def arguments (kind : Kind) (args : Raw) : List Value :=
  [.pointer args.name, .pointer args.token, .pointer args.resource,
   boolean args.visible, boolean args.logging] ++
  (match kind with | .me => [] | .cs => [boolean args.events, boolean args.earlyReturn,
    .pointer args.intermediateVariables, .integer args.intermediateCount.val]) ++
  [.pointer args.environment, .pointer args.logger] ++
  (match kind with | .me => [] | .cs => [.pointer args.intermediateUpdate])

def parameters (kind : Kind) (args : Raw) : Locals :=
  CCalls.Signature.locals (signature kind).parameters (arguments kind args)

/-- Facts needed by validation and logging are derived from the parameter
list, including freshness of private names and unshadowed header constants. -/
structure Scope (args : Raw) (env : Locals) : Prop where
  name : env "instanceName" = some (.pointer args.name)
  token : env "instantiationToken" = some (.pointer args.token)
  logger : env "logMessage" = some (.pointer args.logger)
  logging : env "loggingOn" = some (boolean args.logging)
  environment : env "instanceEnvironment" = some (.pointer args.environment)
  helper : env Identity.function.signature.name = none
  result : env "validIdentity" = none
  null : env "NULL" = none
  error : env "fmi3Error" = none

theorem scope (kind : Kind) (args : Raw) : Scope args (parameters kind args) := by
  cases kind <;> constructor <;>
    simp [parameters, CCalls.Signature.locals, signature, arguments, Identity.function,
      Identity.factoryName, List.lookup]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem ready (kind : Kind) : CCalls.Signature.Ready (signature kind) := by
  change @CCalls.Signature.Ready cInterface (signature kind)
  cases kind <;> decide +kernel

omit static in
private theorem converted_boolean (flag : Bool) :
    convert .boolean (boolean flag) = some (boolean flag) := by cases flag <;> rfl

theorem arguments_converted (kind : Kind) (args : Raw) :
    CCalls.Signature.Arguments (signature kind).parameters (arguments kind args) (arguments kind args) := by
  have count : convert .size (.integer args.intermediateCount.val) =
      some (.integer args.intermediateCount.val) := by
    simp [convert]
  cases kind <;> simp only [signature, arguments, List.cons_append, List.nil_append]
  all_goals
    repeat' first
      | exact CCalls.Signature.Arguments.nil
      | refine CCalls.Signature.Arguments.cons (type := .pointer) (by rfl) (by rfl) ?_
      | refine CCalls.Signature.Arguments.cons (type := .boolean) (by rfl) (converted_boolean _) ?_
      | refine CCalls.Signature.Arguments.cons (type := .size) (by rfl) count ?_

theorem parameters_bound (kind : Kind) (args : Raw) :
    CCalls.parameters (signature kind).parameters (arguments kind args) = some (parameters kind args) :=
  CCalls.Signature.parameters_bound (arguments_converted kind args) (ready kind).1

/-- The actual call creates the entire local/type environment. No successful
execution or caller-supplied parameter environment is assumed. -/
theorem call_entry (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (kind : Kind) (args : Raw) (heap : Heap) (stack : CCalls.Typed.Continuation)
    (defined : program.internal.definitions (signature kind).name =
      some (.tree (Runtime.function model (signature kind)))) :
    ∃ types,
      CCalls.Events.internalNext program
        (.calling (signature kind).name (arguments kind args) heap stack) =
        some (.body (.running (Runtime.body model (signature kind)) (parameters kind args) types heap)
          "fmi3Instance" stack) ∧
      CCalls.Parameters.Coherent (parameters kind args) types ∧ Scope args (parameters kind args) := by
  obtain ⟨types, boundTypes, coherent⟩ := CCalls.Parameters.parameters_typed _ _ _ (parameters_bound kind args)
  exact ⟨types, CCalls.Events.tree_entry program _ _ heap stack
    (Runtime.function model (signature kind)) _ types defined (parameters_bound kind args) boundTypes,
    coherent, scope kind args⟩

end
end Rumoca.FMI3.FactoryArguments

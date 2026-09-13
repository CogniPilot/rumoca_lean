import RumocaFMI3.IdentityFactoryEntry
import RumocaC.CallSignature

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
variable [interface : CInterface]

/-- Exactly the header meanings needed to bind both public factory signatures.
Other types and global object symbols may be supplied by the same interface. -/
structure Types : Prop where
  string : interface.types "fmi3String" = some .pointer
  boolean : interface.types "fmi3Boolean" = some .boolean
  references : interface.types "const fmi3ValueReference *" = some .pointer
  size : interface.types "size_t" = some .size
  environment : interface.types "fmi3InstanceEnvironment" = some .pointer
  logger : interface.types "fmi3LogMessageCallback" = some .pointer
  update : interface.types "fmi3IntermediateUpdateCallback" = some .pointer
  handle : interface.types "fmi3Instance" = some .pointer

omit interface in
theorem base_types (literals : CLiteralAddresses) : @Types (cInterface literals) := by
  letI : CInterface := cInterface literals
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ready (kind : Kind) (bindings : Types) : CCalls.Signature.Ready (signature kind) := by
  cases kind <;> simp [CCalls.Signature.Ready, signature, CCalls.parameterType,
    bindings.string, bindings.boolean, bindings.references, bindings.size,
    bindings.environment, bindings.logger, bindings.update, bindings.handle]

omit interface in
private theorem converted_boolean (flag : Bool) :
    convert .boolean (boolean flag) = some (boolean flag) := by cases flag <;> rfl

theorem arguments_converted (kind : Kind) (args : Raw) (bindings : Types) :
    CCalls.Signature.Arguments (signature kind).parameters (arguments kind args) (arguments kind args) := by
  have count : convert .size (.integer args.intermediateCount.val) =
      some (.integer args.intermediateCount.val) := by
    simp [convert]
  cases kind <;> simp only [signature, arguments, List.cons_append, List.nil_append]
  all_goals
    repeat' first
      | exact CCalls.Signature.Arguments.nil
      | refine CCalls.Signature.Arguments.cons (type := .pointer)
          (by first | exact bindings.string | exact bindings.references | exact bindings.environment |
              exact bindings.logger | exact bindings.update) (by rfl) ?_
      | refine CCalls.Signature.Arguments.cons (type := .boolean) bindings.boolean (converted_boolean _) ?_
      | refine CCalls.Signature.Arguments.cons (type := .size) bindings.size count ?_

theorem parameters_bound (kind : Kind) (args : Raw) (bindings : Types) :
    CCalls.parameters (signature kind).parameters (arguments kind args) = some (parameters kind args) :=
  CCalls.Signature.parameters_bound (arguments_converted kind args bindings) (ready kind bindings).1

/-- The actual call creates the entire local/type environment. No successful
execution or caller-supplied parameter environment is assumed. -/
theorem call_entry (program : CCalls.Events.Program E) (body : List Stmt)
    (kind : Kind) (args : Raw) (heap : Heap) (stack : CCalls.Typed.Continuation)
    (bindings : Types)
    (defined : program.internal.definitions (signature kind).name =
      some (.tree ⟨signature kind, body, false⟩)) :
    ∃ types,
      CCalls.Events.internalNext program
        (.calling (signature kind).name (arguments kind args) heap stack) =
        some (.body (.running body (parameters kind args) types heap)
          "fmi3Instance" stack) ∧
      CCalls.Parameters.Coherent (parameters kind args) types ∧ Scope args (parameters kind args) := by
  obtain ⟨types, boundTypes, coherent⟩ := CCalls.Parameters.parameters_typed _ _ _ (parameters_bound kind args bindings)
  exact ⟨types, CCalls.Events.tree_entry program _ _ heap stack
    ⟨signature kind, body, false⟩ _ types defined (parameters_bound kind args bindings) boundTypes,
    coherent, scope kind args⟩

end
end Rumoca.FMI3.FactoryArguments

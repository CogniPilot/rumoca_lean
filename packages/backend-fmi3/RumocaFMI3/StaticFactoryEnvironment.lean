import RumocaFMI3.StaticFactoryReservation
import RumocaFMI3.FactoryValidation

/-! Explicit global object symbols and the C11 types used by fixed storage.
Object addresses are separate from literal addresses. These bindings model
array decay and the generation-time capacity; native declarations/layout and
the complete public-call correspondence must certify them separately. -/
namespace Rumoca.FMI3.StaticFactory
open CMemory

structure Objects where
  instancesBlock : Nat
  flagsBlock : Nat
  separate : instancesBlock ≠ flagsBlock
  capacity : Nat
  multiple : 2 ≤ capacity
  bounded : capacity < 2^64

def Objects.instances (objects : Objects) : Address := ⟨objects.instancesBlock, [], 0⟩
def Objects.flags (objects : Objects) : Address := ⟨objects.flagsBlock, [], 0⟩

def objectConstants (objects : Objects) : String → Option Value
  | "rumoca_instances" => some (.pointer (some objects.instances))
  | "rumoca_instance_flags" => some (.pointer (some objects.flags))
  | "rumoca_instance_capacity" => some (.integer objects.capacity)
  | name => cConstants name

def objectTypes : String → Option CType
  | "_Bool" => some .boolean
  | "const size_t" => some .size
  | "volatile atomic_bool *" => some .pointer
  | name => cTypes name

abbrev executionInterface (objects : Objects) (literals : CLiteralAddresses) : CInterface :=
  { constants := objectConstants objects, types := objectTypes, literals }

theorem factory_types (objects : Objects) (literals : CLiteralAddresses) :
    @FactoryArguments.Types (executionInterface objects literals) := by
  letI : CInterface := executionInterface objects literals
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Existing constants retain their values outside the three object symbols.
This is a lookup fact, not yet a transfer theorem for entire C executions. -/
theorem constants_unchanged (objects : Objects) (name : String)
    (outside : name ∉ ["rumoca_instances", "rumoca_instance_flags", "rumoca_instance_capacity"]) :
    objectConstants objects name = cConstants name := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  simp [objectConstants, outside.1, outside.2.1, outside.2.2]

theorem types_unchanged (name : String)
    (outside : name ∉ ["_Bool", "const size_t", "volatile atomic_bool *"]) :
    objectTypes name = cTypes name := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  simp [objectTypes, outside.1, outside.2.1, outside.2.2]

/-- Fresh public parameter values and the validated identity flag establish all
factory-suffix locals. The three globals come from the explicit object context,
not from a caller-supplied factory-local environment or a literal-table alias. -/
theorem factory_scope (objects : Objects) (literals : CLiteralAddresses)
    (kind : Kind) (args : FactoryArguments.Raw) :
    @Scope (executionInterface objects literals) (FactoryValidation.locals kind args true)
      objects.instances objects.flags objects.capacity args.environment args.logger args.logging := by
  letI : CInterface := executionInterface objects literals
  cases kind <;> constructor <;>
    simp [FactoryValidation.locals,
      FactoryArguments.parameters, FactoryArguments.signature, FactoryArguments.arguments,
      CCalls.Signature.locals, List.lookup, CBody.resolve, CBody.constants, CBody.bind,
      CAtomicScan.function, Identity.factoryName]
  all_goals rfl

end Rumoca.FMI3.StaticFactory

import RumocaFMI3.StaticFactoryEnvironment
import RumocaC.Fenv

/-! Derive reservation arguments from prepared globals and fresh factory locals. -/
namespace Rumoca.FMI3.StaticFactory
open CTree CMemory CCalls

/-- The prepared header does not change the factory's object/name bindings.
The original globals are derived from fresh factory locals, not supplied as a
caller-written Scope witness. -/
theorem header_factory_scope (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (kind : Kind) (args : FactoryArguments.Raw) :
    letI : CInterface := header.interface (executionInterface objects literals)
    Scope (FactoryValidation.locals kind args true) objects.instances objects.flags objects.capacity
      args.environment args.logger args.logging := by
  letI : CInterface := header.interface (executionInterface objects literals)
  cases kind <;> constructor <;>
    simp [FactoryValidation.locals, FactoryArguments.parameters, FactoryArguments.signature,
      FactoryArguments.arguments, CCalls.Signature.locals, List.lookup, CBody.resolve,
      CBody.constants, CBody.bind, CAtomicScan.function, Identity.factoryName]
  all_goals rfl

/-- The actual factory suffix issues the helper call with its concrete global
array and capacity, under the same prepared fenv/object interface as the source
artifact theorem. No successful reservation is a premise. -/
theorem header_reserve_entry (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) :
    letI : CInterface := header.interface (executionInterface objects literals)
    ∀ (program : Events.Program E) (model : Solve.Model source) (kind : Kind)
      (args : FactoryArguments.Raw) (types : CLoops.Types) (heap : Heap) (stack : Typed.Continuation),
    Events.internalNext program
      (.body (.running (code model kind) (FactoryValidation.locals kind args true) types heap) "fmi3Instance" stack) =
      some (.calling CAtomicScan.function.signature.name [.pointer (some objects.flags), .integer objects.capacity] heap
        (.caller (.declare "size_t" "slot") (guard :: initializeInstance model kind)
          (FactoryValidation.locals kind args true) types "fmi3Instance" stack)) := by
  letI : CInterface := header.interface (executionInterface objects literals)
  intro program model kind args types heap stack
  exact reserve_entry program model kind (FactoryValidation.locals kind args true) types heap
    objects.instances objects.flags objects.capacity args.environment args.logger args.logging stack
    (header_factory_scope header objects literals kind args) rfl

end Rumoca.FMI3.StaticFactory

import RumocaFMI3.IdentityCorrectness
import RumocaFMI3.IdentityNull
import RumocaFMI3.IdentityPrinter
import RumocaFMI3.IdentityLinkage

/-! The actual identity helper's complete observations and printed fragment.
Native headers, ABI, string-buffer validity and libc correspondence remain
explicit. This is a helper contract; allocation and the enclosing creation
functions still require their complete execution proofs. -/
noncomputable section
namespace Rumoca.FMI3.Identity
open CTree CMemory CStringMemory

structure ExecutionContract [interface : CInterface] (program : CCalls.Events.Program E) : Prop where
  valid : Bindings program → ∀
    (name token expected whitespace : Address)
    (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8) (heap : Heap),
    Contents heap name nameBytes → Contents heap token tokenBytes →
    Contents heap expected expectedBytes → Contents heap whitespace whitespaceBytes →
    nameBytes.length < 2^64 →
    ∀ (stack : CCalls.Typed.Continuation) (behavior : Transition.Events.Observation E CBody.Result),
      (CCalls.Events.machine program).Behaves
        (.calling function.signature.name
          (Arguments.values ⟨some name, some token, some expected, some whitespace⟩) heap stack) behavior ↔
      (CCalls.Events.machine program).Behaves
        (.returning (CBody.boolean (accepted nameBytes whitespaceBytes tokenBytes expectedBytes)) heap stack) behavior
  null : interface.types "const char *" = some .pointer →
    interface.types "size_t" = some .size → interface.types "int" = some .int32 →
    interface.types "fmi3Boolean" = some .boolean → interface.types "void *" = some .pointer →
    ∀ (args : Arguments) (heap : Heap) (stack : CCalls.Typed.Continuation),
      nullArguments args = true →
      ∀ behavior : Transition.Events.Observation E CBody.Result,
        (CCalls.Events.machine program).Behaves (.calling function.signature.name args.values heap stack) behavior ↔
          (CCalls.Events.machine program).Behaves (.returning (CBody.boolean false) heap stack) behavior

theorem execution_correct [interface : CInterface] (model : Solve.FMI3Model source)
    (sigs : List Signature) (program : CCalls.Events.Program E)
    (same : program.internal = LiteralPreparation.program model sigs) : ExecutionContract program := by
  have defined : program.internal.definitions function.signature.name = some (.tree function) := by
    rw [same]
    exact helper_defined model sigs
  constructor
  · intro bindings name token expected whitespace nameBytes tokenBytes expectedBytes whitespaceBytes heap
      nameStored tokenStored expectedStored whitespaceStored fits stack behavior
    exact call_equivalence program bindings defined name token expected whitespace
      nameBytes tokenBytes expectedBytes whitespaceBytes heap nameStored tokenStored expectedStored
      whitespaceStored fits stack behavior
  · intro pointer size integer boolean voidPointer args heap stack missing behavior
    exact null_call_equivalence program args pointer size integer boolean voidPointer defined heap stack missing behavior

/-- The supplied text occurs in the actual adapter and has the same function
tree used by execution. Existence of a consistent library environment is part
of the contract, alongside preservation in every environment with its bindings. -/
structure FunctionContract (model : Solve.FMI3Model source) (sigs : List Signature) (text : String) : Prop where
  member : function ∈ Runtime.helpers
  printed : text = function.render
  tokenization : CTree.Printer.FunctionTokenization Printer.typedefs text function
  located : ∃ before after, Runtime.render model sigs = before ++ text ++ after
  libraryFresh : LibraryNamesFresh sigs
  bindings : ∀ (literals : CLiteralAddresses) (E : Type),
    ∃ program : @CCalls.Events.Program (cInterface literals) E,
      @CCalls.Events.Program.internal (cInterface literals) E program =
        LiteralPreparation.program model sigs ∧ Bindings (interface := cInterface literals) program
  execution : ∀ (literals : CLiteralAddresses) (E : Type)
    (program : @CCalls.Events.Program (cInterface literals) E),
    @CCalls.Events.Program.internal (cInterface literals) E program =
      LiteralPreparation.program model sigs → ExecutionContract (interface := cInterface literals) program

theorem rendered_contract (model : Solve.FMI3Model source) (sigs : List Signature)
    (fresh : LibraryNamesFresh sigs) : FunctionContract model sigs function.render := by
  have member : function ∈ Runtime.helpers := by simp [Runtime.helpers]
  refine ⟨member, rfl, Printer.function_tokenization,
    LiteralPreparation.rendered_helper model sigs function member,
    fresh, bindings_exist model sigs fresh, ?_⟩
  intro literals E program same
  exact execution_correct (interface := cInterface literals) model sigs program same

end Rumoca.FMI3.Identity

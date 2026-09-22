import RumocaFMI3.IdentityPreparation
import RumocaC.NamedDeclarations

/-! The actual factory's validation initializer. Its call and typed result
resume at the next emitted statement with unchanged heap. The remaining
rejection/logging/allocation/initialization statements are not assumed to run. -/
noncomputable section
namespace Rumoca.FMI3.Identity
open CTree CMemory CStringMemory
variable [interface : CInterface]

theorem factory_arguments (model : Solve.FMI3Model source) (tok : String := token model) (env : CBody.Locals) (heap : Heap)
    (name suppliedToken : Option Address) (expected whitespace : Address)
    (nameBound : env "instanceName" = some (.pointer name))
    (tokenBound : env "instantiationToken" = some (.pointer suppliedToken))
    (expectedBound : interface.literals tok = some expected)
    (whitespaceBound : interface.literals " \t\n\r\u000c\u000b" = some whitespace) :
    CCalls.arguments env heap
      [Runtime.v "instanceName", Runtime.v "instantiationToken", .str tok, .str " \t\n\r\u000c\u000b"] =
      some (Arguments.values ⟨name, suppliedToken, some expected, some whitespace⟩) := by
  simp [CCalls.arguments, CCalls.argumentsWith, CBody.legacyExpressions,
    Runtime.v, CBody.eval, CBody.evalWith, CBody.resolve, nameBound, tokenBound,
    expectedBound, whitespaceBound, Arguments.values]

theorem factory_enters (program : CCalls.Events.Program E) (model : Solve.FMI3Model source) (tok : String := token model) (rest : List Stmt)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap) (resultType : String)
    (stack : CCalls.Typed.Continuation) (name suppliedToken : Option Address) (expected whitespace : Address)
    (fresh : env "validIdentity" = none) (unshadowed : env function.signature.name = none)
    (named : interface.constants function.signature.name = none)
    (nameBound : env "instanceName" = some (.pointer name))
    (tokenBound : env "instantiationToken" = some (.pointer suppliedToken))
    (expectedBound : interface.literals tok = some expected)
    (whitespaceBound : interface.literals " \t\n\r\u000c\u000b" = some whitespace) :
    CCalls.Events.internalNext program
      (.body (.running (FactoryPrefix.validation model tok :: rest) env types heap) resultType stack) =
      some (.calling function.signature.name
        (Arguments.values ⟨name, suppliedToken, some expected, some whitespace⟩) heap
        (.caller (.declare "fmi3Boolean" "validIdentity") rest
          env types resultType stack)) := by
  exact CCalls.Events.named_declare_entry program env types heap "fmi3Boolean" "validIdentity"
    function.signature.name _ _ rest resultType stack fresh unshadowed named
    (by decide) (factory_arguments model tok env heap name suppliedToken expected whitespace
      nameBound tokenBound expectedBound whitespaceBound)

theorem factory_resumes (program : CCalls.Events.Program E) (rest : List Stmt)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap) (resultType : String)
    (stack : CCalls.Typed.Continuation) (flag : Bool) (fresh : env "validIdentity" = none)
    (boolean : interface.types "fmi3Boolean" = some .boolean) :
    CCalls.Events.internalNext program
      (.returning (CBody.boolean flag) heap
        (.caller (.declare "fmi3Boolean" "validIdentity") rest env types resultType stack)) =
      some (.body (.running rest
        (CBody.bind env "validIdentity" (CBody.boolean flag)) (CLoops.bindType types "validIdentity" .boolean) heap)
        resultType stack) :=
  CCalls.Events.declare_result program env types heap "fmi3Boolean" "validIdentity"
    rest resultType stack _ _ .boolean fresh boolean (by cases flag <;> rfl)

theorem factory_validates (program : CCalls.Events.Program E) (bindings : Bindings program)
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (model : Solve.FMI3Model source) (tok : String := token model) (rest : List Stmt) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (resultType : String) (stack : CCalls.Typed.Continuation)
    (name suppliedToken expected whitespace : Address)
    (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8)
    (fresh : env "validIdentity" = none) (unshadowed : env function.signature.name = none)
    (named : interface.constants function.signature.name = none)
    (nameBound : env "instanceName" = some (.pointer (some name)))
    (tokenBound : env "instantiationToken" = some (.pointer (some suppliedToken)))
    (expectedBound : interface.literals tok = some expected)
    (whitespaceBound : interface.literals " \t\n\r\u000c\u000b" = some whitespace)
    (nameStored : Contents heap name nameBytes) (tokenStored : Contents heap suppliedToken tokenBytes)
    (expectedStored : Contents heap expected expectedBytes) (whitespaceStored : Contents heap whitespace whitespaceBytes)
    (fits : nameBytes.length < 2^64) (behavior : Transition.Events.Observation E CBody.Result) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (FactoryPrefix.validation model tok :: rest) env types heap) resultType stack) behavior ↔
    (CCalls.Events.machine program).Behaves
      (.body (.running rest
        (CBody.bind env "validIdentity" (CBody.boolean (accepted nameBytes whitespaceBytes tokenBytes expectedBytes)))
        (CLoops.bindType types "validIdentity" .boolean) heap) resultType stack) behavior := by
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (factory_enters program model tok rest env types heap resultType stack (some name) (some suppliedToken)
      expected whitespace fresh unshadowed named nameBound tokenBound expectedBound whitespaceBound) (.refl _)) behavior).trans
  rw [call_equivalence program bindings defined name suppliedToken expected whitespace
    nameBytes tokenBytes expectedBytes whitespaceBytes heap nameStored tokenStored expectedStored whitespaceStored fits]
  exact CCalls.Events.internal_prefix_behaviors program
    (.next (factory_resumes program rest env types heap resultType stack _ fresh bindings.boolean) (.refl _)) behavior

/-- Missing caller identity pointers produce false before any string read.
Only type/definition bindings are needed; no string-library premise is used. -/
theorem factory_null (program : CCalls.Events.Program E)
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (pointer : interface.types "const char *" = some .pointer)
    (size : interface.types "size_t" = some .size) (integer : interface.types "int" = some .int32)
    (boolean : interface.types "fmi3Boolean" = some .boolean) (voidPointer : interface.types "void *" = some .pointer)
    (model : Solve.FMI3Model source) (tok : String := token model) (rest : List Stmt) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (resultType : String) (stack : CCalls.Typed.Continuation)
    (name suppliedToken : Option Address) (expected whitespace : Address)
    (fresh : env "validIdentity" = none) (unshadowed : env function.signature.name = none)
    (named : interface.constants function.signature.name = none)
    (nameBound : env "instanceName" = some (.pointer name))
    (tokenBound : env "instantiationToken" = some (.pointer suppliedToken))
    (expectedBound : interface.literals tok = some expected)
    (whitespaceBound : interface.literals " \t\n\r\u000c\u000b" = some whitespace)
    (missing : (name.isNone || suppliedToken.isNone) = true)
    (behavior : Transition.Events.Observation E CBody.Result) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (FactoryPrefix.validation model tok :: rest) env types heap) resultType stack) behavior ↔
    (CCalls.Events.machine program).Behaves
      (.body (.running rest
        (CBody.bind env "validIdentity" (CBody.boolean false))
        (CLoops.bindType types "validIdentity" .boolean) heap) resultType stack) behavior := by
  have absent : nullArguments ⟨name, suppliedToken, some expected, some whitespace⟩ = true := by
    simpa only [nullArguments, Option.isNone_some, Bool.or_false] using missing
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (factory_enters program model tok rest env types heap resultType stack name suppliedToken
      expected whitespace fresh unshadowed named nameBound tokenBound expectedBound whitespaceBound) (.refl _)) behavior).trans
  rw [null_call_equivalence program _ pointer size integer boolean voidPointer defined heap _ absent]
  exact CCalls.Events.internal_prefix_behaviors program
    (.next (factory_resumes program rest env types heap resultType stack false fresh boolean) (.refl _)) behavior

end Rumoca.FMI3.Identity

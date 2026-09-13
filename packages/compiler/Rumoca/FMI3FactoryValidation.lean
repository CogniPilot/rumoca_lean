import Rumoca.FMI3IdentitySource
import RumocaFMI3.IdentityFactoryEntry

/-! Source-derived metadata and literal storage for the actual factory's
validation prefix. Complete allocation, rejection logging and instance
initialization are later obligations; no successful remaining call is assumed. -/
noncomputable section
namespace Rumoca.FMI3.Identity
open CTree CMemory CLiteral CStringMemory

theorem prepared_factory_validation (artifact : Artifact input) (sigs : List Signature)
    (sig : Signature) (member : sig ∈ sigs) (kind : Kind) (named : sig.name = factoryName kind)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions artifact.solve.prepareFMI3 sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare artifact.solve.prepareFMI3 sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) :
    ∃ expected whitespace : Address,
      pool.addresses firstBlock (token artifact.solve.prepareFMI3) = some expected ∧
      pool.addresses firstBlock " \t\n\r\u000c\u000b" = some whitespace ∧
      ∀ (E : Type) (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E),
        @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
          LiteralPreparation.program artifact.solve.prepareFMI3 sigs →
        Bindings (interface := cInterface (pool.addresses firstBlock)) program →
        ∀ (env : CBody.Locals) (types : CLoops.Types)
          (name suppliedToken : Address) (nameBytes tokenBytes : List UInt8),
          env "validIdentity" = none → env function.signature.name = none →
          env "instanceName" = some (.pointer (some name)) →
          env "instantiationToken" = some (.pointer (some suppliedToken)) →
          Contents (pool.install before firstBlock signed) name nameBytes →
          Contents (pool.install before firstBlock signed) suppliedToken tokenBytes →
          nameBytes.length < 2^64 →
          ∀ (resultType : String) (stack : CCalls.Typed.Continuation)
            (behavior : Transition.Events.Observation E CBody.Result),
            (@CCalls.Events.machine E (cInterface (pool.addresses firstBlock)) program).Behaves
              (.body (.running (Runtime.makeInstance artifact.solve.prepareFMI3 kind) env types
                (pool.install before firstBlock signed)) resultType stack) behavior ↔
            (@CCalls.Events.machine E (cInterface (pool.addresses firstBlock)) program).Behaves
              (.body (.running (Runtime.makeInstance artifact.solve.prepareFMI3 kind).tail
                (CBody.bind env "validIdentity" (CBody.boolean
                  (accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes
                    (token artifact.solve.prepareFMI3).toUTF8.data.toList)))
                (CLoops.bindType types "validIdentity" .boolean)
                (pool.install before firstBlock signed)) resultType stack) behavior := by
  letI : CInterface := cInterface (pool.addresses firstBlock)
  obtain ⟨expected, whitespace, expectedBound, whitespaceBound, expectedStored, whitespaceStored⟩ :=
    constants_ready artifact.solve.prepareFMI3 sigs sig member kind named made before firstBlock signed
  rw [compiled_token_content artifact] at expectedStored
  refine ⟨expected, whitespace, expectedBound, whitespaceBound, ?_⟩
  intro E program same bindings env types name suppliedToken nameBytes tokenBytes
    fresh unshadowed nameBound tokenBound nameStored tokenStored fits resultType stack behavior
  have defined : (@CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program).definitions
      function.signature.name = some (.tree function) := by
    rw [same]
    exact helper_defined artifact.solve.prepareFMI3 sigs
  exact factory_validates program bindings defined artifact.solve.prepareFMI3
    (Runtime.makeInstance artifact.solve.prepareFMI3 kind).tail env types
    (pool.install before firstBlock signed) resultType stack name suppliedToken expected whitespace
    nameBytes tokenBytes (token artifact.solve.prepareFMI3).toUTF8.data.toList (content " \t\n\r\u000c\u000b")
    fresh unshadowed rfl nameBound tokenBound expectedBound whitespaceBound
    nameStored tokenStored expectedStored whitespaceStored fits behavior

end Rumoca.FMI3.Identity

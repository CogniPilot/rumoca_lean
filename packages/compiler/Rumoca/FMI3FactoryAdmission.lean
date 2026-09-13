import Rumoca.FMI3IdentitySource
import Rumoca.FMI3AdapterProofs
import RumocaFMI3.FactoryValidation

/-! Source-to-public-factory admission. Actual parsed identifiers establish
the expected token's complete bytes; the actual literal pool constructs its
storage. Public argument binding and the emitted definition table are derived,
so no factory-local environment or successful execution is assumed. -/
noncomputable section
namespace Rumoca.FMI3.FactoryValidation
open CTree CMemory CLiteral CStringMemory FactoryArguments

theorem prepared_public_admission (artifact : Artifact input) (sigs : List Signature) (kind : Kind)
    (unique : ((LiteralPreparation.functions artifact.solve.prepareFMI3 sigs).map
      (fun fn => fn.signature.name)).Nodup)
    (member : signature kind ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions artifact.solve.prepareFMI3 sigs).flatMap functionNames)}
    (made : LiteralPreparation.prepare artifact.solve.prepareFMI3 sigs = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) :
    ∀ (E : Type) (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E),
      @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
        LiteralPreparation.program artifact.solve.prepareFMI3 sigs →
      Identity.Bindings (interface := cInterface (pool.addresses firstBlock)) program →
      ∀ (args : Raw) (name suppliedToken : Address) (nameBytes tokenBytes : List UInt8),
        (kind = .me ∨ FactoryEntry.unsupported args = false) →
        args.name = some name → args.token = some suppliedToken →
        Contents (pool.install before firstBlock signed) name nameBytes →
        Contents (pool.install before firstBlock signed) suppliedToken tokenBytes →
        nameBytes.length < 2^64 →
        ∀ stack : CCalls.Typed.Continuation, ∃ types, ∀ behavior,
          (@CCalls.Events.machine E (cInterface (pool.addresses firstBlock)) program).Behaves
            (.calling (signature kind).name (arguments kind args)
              (pool.install before firstBlock signed) stack) behavior ↔
          (@CCalls.Events.machine E (cInterface (pool.addresses firstBlock)) program).Behaves
            (.body (.running
              (remaining artifact.solve.prepareFMI3 kind (Identity.accepted nameBytes
                (content " \t\n\r\u000c\u000b") tokenBytes (token artifact.solve.prepareFMI3).toUTF8.data.toList))
              (locals kind args (Identity.accepted nameBytes
                (content " \t\n\r\u000c\u000b") tokenBytes (token artifact.solve.prepareFMI3).toUTF8.data.toList))
              types (pool.install before firstBlock signed)) "fmi3Instance" stack) behavior := by
  letI : StaticLiterals := ⟨pool.addresses firstBlock⟩
  letI : CInterface := cInterface (pool.addresses firstBlock)
  obtain ⟨expected, whitespace, expectedBound, whitespaceBound, expectedStored, whitespaceStored⟩ :=
    Identity.constants_ready artifact.solve.prepareFMI3 sigs (signature kind) member kind rfl
      made before firstBlock signed
  rw [compiled_token_content artifact] at expectedStored
  intro E program same bindings args name suppliedToken nameBytes tokenBytes supported nameBound tokenBound
    nameStored tokenStored fits stack
  have defined : program.internal.definitions (signature kind).name =
      some (.tree (Runtime.function artifact.solve.prepareFMI3 (signature kind))) := by
    rw [same]
    exact LiteralPreparation.function_bound artifact.solve.prepareFMI3 sigs unique (signature kind) member
  have helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function) := by
    rw [same]
    exact Identity.helper_defined artifact.solve.prepareFMI3 sigs
  exact admission_equivalence program bindings artifact.solve.prepareFMI3 kind args
    (pool.install before firstBlock signed) stack name suppliedToken expected whitespace
    nameBytes tokenBytes (token artifact.solve.prepareFMI3).toUTF8.data.toList (content " \t\n\r\u000c\u000b")
    defined helper supported nameBound tokenBound expectedBound whitespaceBound
    nameStored tokenStored expectedStored whitespaceStored fits

/-- The mandatory certificate for the independently read adapter yields the
public admission consequence using the original parsed source's full token
bytes. Its pool exists by the earlier artifact preparation obligation. -/
theorem actual_adapter_admission (artifact : Artifact input) (adapter : String)
    (contract : AdapterContract artifact adapter) :
    ∃ sigs pool,
      LiteralPreparation.prepare artifact.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render artifact.solve.prepareFMI3 sigs = adapter ∧
      ∀ (before : Heap) (firstBlock : Nat) (signed : Bool)
        (E : Type) (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E),
        @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
          LiteralPreparation.program artifact.solve.prepareFMI3 sigs →
        Identity.Bindings (interface := cInterface (pool.addresses firstBlock)) program →
        ∀ (kind : Kind) (args : Raw) (name suppliedToken : Address) (nameBytes tokenBytes : List UInt8),
          (kind = .me ∨ FactoryEntry.unsupported args = false) →
          args.name = some name → args.token = some suppliedToken →
          Contents (pool.install before firstBlock signed) name nameBytes →
          Contents (pool.install before firstBlock signed) suppliedToken tokenBytes →
          nameBytes.length < 2^64 →
          ∀ stack : CCalls.Typed.Continuation, ∃ types, ∀ behavior,
            (@CCalls.Events.machine E (cInterface (pool.addresses firstBlock)) program).Behaves
              (.calling (signature kind).name (arguments kind args)
                (pool.install before firstBlock signed) stack) behavior ↔
            (@CCalls.Events.machine E (cInterface (pool.addresses firstBlock)) program).Behaves
              (.body (.running
                (remaining artifact.solve.prepareFMI3 kind (Identity.accepted nameBytes
                  (content " \t\n\r\u000c\u000b") tokenBytes (token artifact.solve.prepareFMI3).toUTF8.data.toList))
                (locals kind args (Identity.accepted nameBytes
                  (content " \t\n\r\u000c\u000b") tokenBytes (token artifact.solve.prepareFMI3).toUTF8.data.toList))
                types (pool.install before firstBlock signed)) "fmi3Instance" stack) behavior := by
  obtain ⟨sigs, pool, made, printed, _, prepared⟩ := adapter_factory_admission contract
  refine ⟨sigs, pool, made, printed, ?_⟩
  intro before firstBlock signed E program same bindings kind args name suppliedToken nameBytes tokenBytes
    supported nameBound tokenBound nameStored tokenStored fits stack
  letI : StaticLiterals := ⟨pool.addresses firstBlock⟩
  letI : CInterface := cInterface (pool.addresses firstBlock)
  obtain ⟨_, _, execution⟩ := prepared before firstBlock signed
  have result := (execution E program same).valid bindings kind args name suppliedToken nameBytes tokenBytes
    supported nameBound tokenBound nameStored tokenStored fits stack
  simpa only [FactoryLiterals.text, compiled_token_content artifact] using result

end Rumoca.FMI3.FactoryValidation

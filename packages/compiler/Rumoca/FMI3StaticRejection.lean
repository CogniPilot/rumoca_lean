import Rumoca.FMI3StaticCreation
import RumocaFMI3.StaticFactoryRejection

/-! Source-derived reasons for rejecting a public factory call, composed with
the actual adapter and diagnostic pool. These conditions do not assume a C
execution, reservation result, initialized instance store or successful logger. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral CStringMemory StaticFactory

/-- Independent input conditions, indexed by the diagnostic selected by the
public interface. Capability rejection takes priority over identity access;
missing pointers need no readable caller buffer. -/
inductive FactoryInputRejected (artifact : Artifact input) (kind : Kind)
    (args : FactoryArguments.Raw) (heap : Heap) : FactoryLiterals.Field → Prop where
  | unsupported (cs : kind = .cs) (requested : FactoryEntry.unsupported args = true) :
      FactoryInputRejected artifact kind args heap .capability
  | missing (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
      (absent : (args.name.isNone || args.token.isNone) = true) :
      FactoryInputRejected artifact kind args heap .identity
  | invalid (name supplied : Address) (nameBytes tokenBytes : List UInt8)
      (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
      (nameBound : args.name = some name) (tokenBound : args.token = some supplied)
      (nameStored : Contents heap name nameBytes) (tokenStored : Contents heap supplied tokenBytes)
      (fits : nameBytes.length < 2^64)
      (accepted : Identity.accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes
        (token artifact.solve.prepareFMI3).toUTF8.data.toList = false) :
      FactoryInputRejected artifact kind args heap .identity

/-- The source predicate supplies the generic public rejection theorem's
premises using the actual definition table and prepared literal addresses. -/
theorem prepared_static_rejection (artifact : Artifact input) (signatures : List Signature)
    (member : FactoryArguments.signature .cs ∈ signatures)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions artifact.solve.prepareFMI3 signatures).flatMap functionNames)}
    (made : LiteralPreparation.prepare artifact.solve.prepareFMI3 signatures = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (E : Type) (storage : Objects) :
    letI : CInterface := executionInterface storage (pool.addresses firstBlock)
    ∀ (program : CCalls.Events.Program E),
    program.internal = LiteralPreparation.program artifact.solve.prepareFMI3 signatures →
    Identity.Bindings program →
    ∀ (kind : Kind) (args : FactoryArguments.Raw) (field : FactoryLiterals.Field),
    FactoryInputRejected artifact kind args heap field →
    Rejected program artifact.solve.prepareFMI3 kind args heap
      (FactoryLiterals.text artifact.solve.prepareFMI3 field) := by
  letI : CInterface := executionInterface storage (pool.addresses firstBlock)
  intro program actual identity kind args field rejected
  have helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function) := by
    rw [actual]
    exact StaticRuntime.identity_bound _ signatures
  cases rejected with
  | unsupported cs requested => exact .unsupported cs requested
  | missing supported absent =>
      obtain ⟨addresses, stored⟩ := FactoryLiterals.prepared artifact.solve.prepareFMI3 signatures
        member made before firstBlock signed
      exact .missing supported absent (addresses .expected) (addresses .whitespace)
        (stored .expected).1 (stored .whitespace).1 helper
  | invalid name supplied nameBytes tokenBytes supported nameBound tokenBound nameStored tokenStored fits accepted =>
      obtain ⟨request⟩ := prepared_static_identity artifact signatures member made before firstBlock signed heap frame
        kind args name supplied nameBytes tokenBytes supported nameBound tokenBound nameStored tokenStored fits accepted
      exact .identity request identity helper

/-- Every independently rejected call returns null with unchanged memory when
logging is disabled or unavailable. No ready instance storage is required. -/
theorem adapter_quiet_static_rejection (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (instances flags : Nat) (separate : instances ≠ flags)
        (before : Heap) (firstBlock : Nat) (signed : Bool),
        let storage := StaticRuntime.objects instances flags separate
        let literals := pool.addresses firstBlock
        letI : CInterface := executionInterface storage literals
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        Identity.Bindings program →
        ∀ (kind : Kind) (args : FactoryArguments.Raw) (heap : Heap) (field : FactoryLiterals.Field),
        CReadOnly.Preserves (pool.install before firstBlock signed) heap →
        FactoryInputRejected a kind args heap field →
        (args.logger.isSome && args.logging) = false →
        ∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap .done) behavior ↔
          behavior = .terminates [] ⟨.pointer none, heap⟩ := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady, _, _, _, _, _, _, _, _, _, _, factories, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E instances flags separate before firstBlock signed
  let storage := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface storage literals
  dsimp only
  intro program actual identity kind args heap field frame rejected quiet behavior
  have rejected' := prepared_static_rejection a signatures (factories.member .cs) made before firstBlock signed
    heap frame E storage program actual identity kind args field rejected
  exact public_rejected_silent storage literals program _ kind args heap _ rejected'
    (by rw [actual]; exact StaticRuntime.factory_bound _ signatures unique kind (factories.member kind)) quiet behavior

/-- Enabled rejection logging uses the exact cause-specific emitted bytes and
retains all represented callback results, effects and events. A foreign
relation without an outcome remains observable as failure. -/
theorem adapter_logged_static_rejection (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (instances flags : Nat) (separate : instances ≠ flags)
        (before : Heap) (firstBlock : Nat) (signed : Bool),
        let storage := StaticRuntime.objects instances flags separate
        let literals := pool.addresses firstBlock
        letI : CInterface := executionInterface storage literals
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        Identity.Bindings program →
        ∀ (kind : Kind) (args : FactoryArguments.Raw) (heap : Heap) (field : FactoryLiterals.Field),
        CReadOnly.Preserves (pool.install before firstBlock signed) heap →
        FactoryInputRejected a kind args heap field →
        ∀ (logger : Address) (callback : String) (foreign : CCalls.Events.External E),
        args.logger = some logger → args.logging = true →
        program.addresses logger = some callback → program.externals callback = some foreign →
        foreign.signature = Logging.signature callback →
        ∃ category message,
          literals "logStatus" = some category ∧
          literals (FactoryLiterals.text a.solve.prepareFMI3 field) = some message ∧
          Contents heap category (content "logStatus") ∧
          Contents heap message (content (FactoryLiterals.text a.solve.prepareFMI3 field)) ∧
          ∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap .done) behavior ↔
            (∃ events value after, foreign.execute (Logging.arguments args.environment category message)
              heap events value after ∧ behavior = .terminates events ⟨.pointer none, after⟩) ∨
            ((∀ events value after, ¬ foreign.execute (Logging.arguments args.environment category message)
              heap events value after) ∧ behavior = .wrong []) := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady, _, _, _, _, _, _, _, _, _, _, factories, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E instances flags separate before firstBlock signed
  let storage := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface storage literals
  dsimp only
  intro program actual identity kind args heap field frame rejected
    logger callback foreign loggerBound logging address external prototype
  have rejected' := prepared_static_rejection a signatures (factories.member .cs) made before firstBlock signed
    heap frame E storage program actual identity kind args field rejected
  obtain ⟨addresses, stored⟩ := FactoryLiterals.prepared a.solve.prepareFMI3 signatures
    (factories.member .cs) made before firstBlock signed
  have kept := FactoryLiterals.preserved a.solve.prepareFMI3 addresses
    (pool.install before firstBlock signed) heap signed (fun field => (stored field).2.1) frame
  refine ⟨addresses .category, addresses field, (stored .category).1, (stored field).1,
    (kept .category).2, (kept field).2, ?_⟩
  exact public_rejected_logged storage literals program _ kind args heap _ rejected'
    (by rw [actual]; exact StaticRuntime.factory_bound _ signatures unique kind (factories.member kind))
    logger (addresses .category) (addresses field) callback foreign loggerBound logging
    (stored .category).1 (stored field).1 address external prototype

end Rumoca.FMI3

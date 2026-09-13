import Rumoca.FMI3StaticCreation
import RumocaFMI3.StaticFactoryLiterals

/-! Actual-adapter creation with enabled exhaustion logging. Diagnostic
addresses and bytes are derived from the emitted literal pool. The foreign
logger retains every represented outcome; no successful callback is assumed. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral CStringMemory StaticFactory

/-- Creation from any ready static store, with the source identity and exact
exhaustion diagnostic supplied by the actual artifact. Success initializes a
slot without logging. Exhaustion preserves all represented logger outcomes,
including the stuck case when the foreign relation has no outcome. -/
theorem adapter_logged_static_creation (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (instances flags : Nat) (separate : instances ≠ flags)
        (before : Heap) (firstBlock : Nat) (signed : Bool),
        let storage := StaticRuntime.objects instances flags separate
        let literals := pool.addresses firstBlock
        letI : CInterface := executionInterface storage literals
        ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        Identity.Bindings program →
        program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
        ∀ (kind : Kind) (args : FactoryArguments.Raw) (heap : Heap),
        CReadOnly.Preserves (pool.install before firstBlock signed) heap →
        CreationStorage heap storage.instances storage.flags storage.capacity →
        ∀ (name supplied : Address) (nameBytes tokenBytes : List UInt8),
        (kind = .me ∨ FactoryEntry.unsupported args = false) →
        args.name = some name → args.token = some supplied →
        Contents heap name nameBytes → Contents heap supplied tokenBytes →
        nameBytes.length < 2^64 →
        Identity.accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes
          (token a.solve.prepareFMI3).toUTF8.data.toList = true →
        ∀ (logger : Address) (callback : String) (foreign : CCalls.Events.External E),
        args.logger = some logger → args.logging = true →
        program.addresses logger = some callback → program.externals callback = some foreign →
        foreign.signature = Logging.signature callback →
        ∃ category message,
          literals "logStatus" = some category ∧
          literals "Instance capacity exhausted" = some message ∧
          Contents heap category (content "logStatus") ∧
          Contents heap message (content "Instance capacity exhausted") ∧
          ∃ trace slot after,
            CAtomicScan.Outcome storage.flags storage.capacity 0 heap trace slot after ∧
            slot ≤ storage.capacity ∧ trace.length ≤ storage.capacity ∧
            ∀ behavior, (CCalls.Events.machine program).Behaves
              (.calling (FactoryArguments.signature kind).name
                (FactoryArguments.arguments kind args) heap .done) behavior ↔
              if slot < storage.capacity then
                behavior = .terminates (trace.map tag)
                  ⟨.pointer (some (storage.instances.index slot)),
                    InstanceSlot.finalHeap after (storage.instances.index slot) slot kind
                      args.environment (some logger) true⟩
              else
                (∃ events value finalHeap,
                  foreign.execute (Logging.arguments args.environment category message)
                    heap events value finalHeap ∧
                  behavior = .terminates (trace.map tag ++ events) ⟨.pointer none, finalHeap⟩) ∨
                ((∀ events value finalHeap,
                  ¬ foreign.execute (Logging.arguments args.environment category message)
                    heap events value finalHeap) ∧ behavior = .wrong (trace.map tag)) := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady, _, _, _, _, _, _, _, _, _, _, factories, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E instances flags separate before firstBlock signed
  let storage := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface storage literals
  dsimp only
  intro program tag actual identity exchange kind args heap frame ready name supplied nameBytes tokenBytes
    supported nameBound tokenBound nameStored tokenStored fits accepted
    logger callback foreign loggerBound logging address external prototype
  obtain ⟨request⟩ := prepared_static_identity a signatures (factories.member .cs) made before firstBlock signed heap frame
    kind args name supplied nameBytes tokenBytes supported nameBound tokenBound nameStored tokenStored fits accepted
  obtain ⟨addresses, stored⟩ := FactoryLiterals.prepared a.solve.prepareFMI3 signatures
    (factories.member .cs) made before firstBlock signed
  have kept := FactoryLiterals.preserved a.solve.prepareFMI3 addresses
    (pool.install before firstBlock signed) heap signed (fun field => (stored field).2.1) frame
  obtain ⟨message, messageBound, _, messageStored⟩ := capacity_message_prepared a.solve.prepareFMI3 signatures
    (factories.member .cs) made before firstBlock signed heap frame
  refine ⟨addresses .category, message, (stored .category).1, messageBound,
    (kept .category).2, messageStored, ?_⟩
  have bindings : ReservationBindings program tag :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, exchange, by rw [actual]; exact StaticRuntime.reservation_bound _ signatures⟩
  exact public_create_logged storage literals program tag identity _ kind args heap request
    (by rw [actual]; exact StaticRuntime.factory_bound _ signatures unique kind (factories.member kind))
    (by rw [actual]; exact StaticRuntime.identity_bound _ signatures) ready bindings
    logger (addresses .category) message callback foreign loggerBound logging (stored .category).1
    messageBound address external prototype

end Rumoca.FMI3

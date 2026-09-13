import Rumoca.FMI3AdapterProofs
import Rumoca.FMI3IdentitySource

/-! Source-derived identity buffers and complete quiet static creation on
ready storage. The actual adapter supplies the function table and literal
pool; host histories still establish buffer validity and current ownership. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral CStringMemory StaticFactory

/-- The source token and whitespace bytes come from the artifact's actual
literal pool and survive its readonly frame. Only current caller buffers and
their independent acceptance predicate are supplied by the host. -/
theorem prepared_static_identity (artifact : Artifact input) (signatures : List Signature)
    (member : FactoryArguments.signature .cs ∈ signatures)
    {pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions artifact.solve.prepareFMI3 signatures).flatMap functionNames)}
    (made : LiteralPreparation.prepare artifact.solve.prepareFMI3 signatures = some pool)
    (before : Heap) (firstBlock : Nat) (signed : Bool) (heap : Heap)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (kind : Kind) (args : FactoryArguments.Raw) (name supplied : Address)
    (nameBytes tokenBytes : List UInt8)
    (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
    (nameBound : args.name = some name) (tokenBound : args.token = some supplied)
    (nameStored : Contents heap name nameBytes) (tokenStored : Contents heap supplied tokenBytes)
    (fits : nameBytes.length < 2^64)
    {valid : Bool}
    (accepted : Identity.accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes
      (token artifact.solve.prepareFMI3).toUTF8.data.toList = valid) :
    Nonempty (IdentityRequest (pool.addresses firstBlock) artifact.solve.prepareFMI3 kind args heap valid) := by
  obtain ⟨addresses, stored⟩ := FactoryLiterals.prepared artifact.solve.prepareFMI3 signatures
    member made before firstBlock signed
  have kept := FactoryLiterals.preserved artifact.solve.prepareFMI3 addresses
    (pool.install before firstBlock signed) heap signed (fun field => (stored field).2.1) frame
  refine ⟨⟨name, supplied, addresses .expected, addresses .whitespace, nameBytes, tokenBytes,
    (token artifact.solve.prepareFMI3).toUTF8.data.toList, content " \t\n\r\u000c\u000b",
    supported, nameBound, tokenBound, (stored .expected).1, (stored .whitespace).1,
    nameStored, tokenStored, ?_, (kept .whitespace).2, fits, accepted⟩⟩
  simpa only [FactoryLiterals.text, compiled_token_content artifact] using (kept .expected).2

/-- A certificate for the actual adapter implies quiet creation on arbitrary
ready storage, including capacity exhaustion and reused objects. The source's
token bytes, actual definitions, and reservation bindings are derived. The
heap frame and storage readiness still need the enclosing host-history proof. -/
theorem adapter_quiet_static_creation (contract : AdapterContract a adapter) :
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
        (args.logger.isSome && args.logging) = false →
        ∃ trace slot after, CAtomicScan.Outcome storage.flags storage.capacity 0 heap trace slot after ∧
          slot ≤ storage.capacity ∧ trace.length ≤ storage.capacity ∧
          ∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap .done) behavior ↔
            if slot < storage.capacity then
              behavior = .terminates (trace.map tag)
                ⟨.pointer (some (storage.instances.index slot)),
                  InstanceSlot.finalHeap after (storage.instances.index slot) slot kind
                    args.environment args.logger args.logging⟩
            else behavior = .terminates (trace.map tag) ⟨.pointer none, heap⟩ := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady, _, _, _, _, _, _, _, _, _, _, factories, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E instances flags separate before firstBlock signed
  let storage := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface storage literals
  dsimp only
  intro program tag actual identity exchange kind args heap frame ready name supplied nameBytes tokenBytes
    supported nameBound tokenBound nameStored tokenStored fits accepted quiet
  obtain ⟨request⟩ := prepared_static_identity a signatures (factories.member .cs) made before firstBlock signed heap frame
    kind args name supplied nameBytes tokenBytes supported nameBound tokenBound nameStored tokenStored fits accepted
  have bindings : ReservationBindings program tag :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, exchange, by rw [actual]; exact StaticRuntime.reservation_bound _ signatures⟩
  exact public_create_silent storage literals program tag identity _ kind args heap request
    (by rw [actual]; exact StaticRuntime.factory_bound _ signatures unique kind (factories.member kind))
    (by rw [actual]; exact StaticRuntime.identity_bound _ signatures) ready bindings quiet

end Rumoca.FMI3

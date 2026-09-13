import Rumoca.FMI3AdapterProofs
import RumocaFMI3.TerminationRelease

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory StaticFactory

/-- Both public definitions and termination behavior come from the same
actual source/adapter certificate. Only the returning atomic-store semantics
and the host's input lease remain external premises of this sequence. -/
theorem adapter_termination_release (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := executionInterface objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        Termination.ReleaseContract objects program tag := by
  obtain ⟨signatures, _, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, _, _, _, runtime, termination, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E objects firstBlock
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface objects literals
  intro program tag actual write
  have bindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact runtime.release_defined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  exact Termination.terminate_release objects literals program tag
    ((termination.prepared pool made).quiet E objects firstBlock program actual) bindings

end Rumoca.FMI3

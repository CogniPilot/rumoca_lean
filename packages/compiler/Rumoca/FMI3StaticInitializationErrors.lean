import Rumoca.FMI3StaticInitialization
import RumocaFMI3.StaticInitializationErrors

noncomputable section
namespace Rumoca.FMI3

/-- The actual source/adapter certificate derives successful, null, rejected
and logged initialization contracts in the same static object environment.
Later lifecycle operations and callback/private-storage frames remain separate. -/
theorem adapter_static_initialization_complete (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      StaticInitialization.PreparedContract a.solve.prepareFMI3 signatures pool := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady, _, _, _, _, _, _, _, _, initialization, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  exact ⟨signatures, pool, made, printed,
    StaticInitialization.prepared_correct a.solve.prepareFMI3 signatures unique initialization made⟩

end Rumoca.FMI3

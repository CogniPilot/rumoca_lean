import Rumoca.FMI3MEEnvironment
import Rumoca.FMI3DerivativeProofs
import RumocaFMI3.MENumericalHistory

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral StaticFactory

/-- Every derivative query in a returned script describes the original
source Real equation. This does not identify importer trial states with an
integrated trajectory of the source IVP. -/
def MENumericalHistory.DerivativeObservations (source : AST.Model)
    (actions : List MENumericalHistory.Action)
    (observed : List (MENumericalHistory.Observation E)) : Prop :=
  List.Forall₂ (fun action result => action = .derivative →
    ∃ value, result.value = some (.finite value) ∧
      ∀ d : String → ℝ, Source.Equation source d ↔ d source.state = Binary64.value value)
    actions observed

theorem MENumericalHistory.observations_source (model : Solve.Model source)
    (reference : MENumericalHistory.ReferenceState) (actions : List MENumericalHistory.Action) :
    MENumericalHistory.DerivativeObservations (E := E) source actions
      ((MENumericalHistory.observations model.prepareFMI3 reference actions).map
        MENumericalHistory.Observation.ok) := by
  induction actions generalizing reference with
  | nil => exact .nil
  | cons action rest ih =>
    refine .cons ?_ (ih (action.next reference))
    intro derivative
    subst action
    exact ⟨ModelExchange.derivative model reference.state, rfl,
      derivative_value_source model reference.state⟩

/-- The actual compiled source and required C/metadata certificates supply
every call in a mixed ME history. Initial typed caller/instance storage and
the importer protocol are explicit; later writes, states and observations
are derived. Creation, reset, rejected histories and release need the later
lifetime composition, and native compilation/ABI remain external boundaries. -/
theorem runtime_me_numerical_history (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    DerivativeMetadata.Contract a.parsed.ast metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
          ∀ (heap : Heap) (p : Address) (clock : Time.Clock)
            (reference final : MENumericalHistory.ReferenceState)
            (addresses : String → Address) (buffer : Address) (actions : List MENumericalHistory.Action),
            MENumericalHistory.Stored heap p clock reference addresses buffer →
            MENumericalHistory.ReferenceTrace reference actions final →
            ∃ after finalClock,
              MENumericalHistory.Calls program p addresses buffer heap actions
                (MENumericalHistory.observations a.solve.prepareFMI3 reference actions) after ∧
              MENumericalHistory.Stored after p finalClock final addresses buffer ∧
              CReadOnly.Preserves heap after ∧
              (∀ q, MENumericalHistory.Outside p addresses buffer q → after q = heap q) ∧
              MENumericalHistory.Executed program p addresses buffer heap actions
                ((MENumericalHistory.observations a.solve.prepareFMI3 reference actions).map
                  MENumericalHistory.Observation.ok) after ∧
              (∀ observed actualAfter,
                MENumericalHistory.Executed program p addresses buffer heap actions observed actualAfter →
                observed = (MENumericalHistory.observations a.solve.prepareFMI3 reference actions).map
                  MENumericalHistory.Observation.ok ∧ actualAfter = after ∧
                MENumericalHistory.DerivativeObservations a.parsed.ast actions observed) := by
  obtain ⟨sigs, pool, made, printed, functions, prepared⟩ := adapter_me_environment contract.adapter
  refine ⟨compiled, contract.numerical, DerivativeMetadata.artifact_derivatives _ _ contract.metadata,
    sigs, pool, made, printed, functions, prepared, ?_⟩
  intro header E objects firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual heap p clock reference final addresses buffer actions stored admitted
  obtain ⟨after, finalClock, called, finalStored, readonly, frame⟩ := MENumericalHistory.trace program
    (prepared.quiet header E objects firstBlock program actual) stored admitted
  refine ⟨after, finalClock, called, finalStored, readonly, frame, called.executes, ?_⟩
  intro observed actualAfter executed
  obtain ⟨values, finalHeap⟩ := called.determines executed
  refine ⟨values, finalHeap, ?_⟩
  rw [values]
  exact MENumericalHistory.observations_source a.solve reference actions

end Rumoca.FMI3
end

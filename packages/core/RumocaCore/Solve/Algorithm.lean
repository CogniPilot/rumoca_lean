import RumocaCore.Solve.AlgorithmOrigins

namespace Rumoca.Solve.Algorithm
open Rumoca.Tensor

/-- Prepared executable root with provenance. Backends read `block`; they do
not repeat GALEC refinement or inspect DAE equations to select a solver. -/
structure Model (source : AST.Model) where
  origin : GALEC.Model source
  block : Block scalar
  lowered : block = lower origin.block
  origins : Block.Origins origin.origins.table block
  origins_lowered : (lowered ▸ origins) = lowerOrigins origin.originTrace

def prepare (model : GALEC.Model source) : Model source :=
  ⟨model, lower model.block, rfl, lowerOrigins model.originTrace, rfl⟩

theorem Model.block_is_unit (model : Model source) : model.block = lower GALEC.unitBlock := by
  rw [model.lowered, model.origin.profile]

end Rumoca.Solve.Algorithm

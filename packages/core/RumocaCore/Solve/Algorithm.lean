import RumocaCore.GALEC.OriginLowering
import RumocaCore.IR

namespace Rumoca.Solve.Algorithm
open Rumoca.Tensor

/-- Required source/rule/parent correspondence for every occurrence of the
prepared block. Its compact field references expand to the block trace. -/
structure Origins (dae : DAE.Model source) where
  table : Provenance.Table dae.flat.context
  extension : dae.origins.table.Extension table
  references : GALEC.UnitOrigins.References table
  correct : references.Correct dae

/-- Prepared executable root with provenance. It binds the Algorithm Code to
its original DAE and to the explicit unit-step/zero-start profile; it does not
license arbitrary DAEs. Backends read `block`; they do not select a solver or
inspect DAE equations. -/
structure Model (source : AST.Model) where
  dae : DAE.Model source
  origins : Origins dae
  block : Block scalar
  profile : block = unitBlock

def prepare (dae : DAE.Model source) : Model source :=
  ⟨dae, ⟨GALEC.OriginLowering.table dae, GALEC.OriginLowering.extension dae,
    GALEC.OriginLowering.references dae, GALEC.OriginLowering.references_correct dae⟩,
    unitBlock, rfl⟩

/-- The origins of the actual prepared block. -/
def Model.trace (model : Model source) : Block.Origins model.origins.table model.block :=
  model.profile.symm ▸ model.origins.references.trace

end Rumoca.Solve.Algorithm

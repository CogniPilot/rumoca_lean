import RumocaCore.GALEC.Syntax
import RumocaCore.GALEC.OriginLowering
import RumocaCore.IR

namespace Rumoca.GALEC
open Rumoca.Tensor

/-- Required source/rule/parent correspondence for every occurrence of the
admitted block. Its compact field references expand to a syntax-indexed trace. -/
structure Origins (dae : DAE.Model source) where
  table : Provenance.Table dae.flat.context
  extension : dae.origins.table.Extension table
  references : UnitOrigins.References table
  correct : references.Correct dae

/-- This admission token binds the Algorithm Code to its original DAE and to
the explicit unit-step/zero-start profile. It does not license arbitrary DAEs. -/
structure Model (source : AST.Model) where
  dae : DAE.Model source
  block : Block scalar
  profile : block = unitBlock
  origins : Origins dae

def Model.originTrace (model : Model source) : Block.Origins model.origins.table model.block :=
  model.profile.symm ▸ model.origins.references.trace

def lower (dae : DAE.Model source) : Model source :=
  ⟨dae, unitBlock, rfl,
    ⟨OriginLowering.table dae, OriginLowering.extension dae,
      OriginLowering.references dae, OriginLowering.references_correct dae⟩⟩

end Rumoca.GALEC

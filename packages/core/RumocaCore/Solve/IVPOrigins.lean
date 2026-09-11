import RumocaCore.Solve.IVP
import RumocaCore.Solve.Tensor.Origins

/-! Complete occurrence origins for an executable IVP. Empty input tensors
still require the generated origin that explains the absent input channel. -/
namespace Rumoca.Solve
open _root_.Parser.Provenance (Table Ref)

structure IVP.Origins (table : Table Site Rule) (problem : IVP) where
  model : Ref table
  state : Ref table
  input : Ref table
  output : Ref table
  initialProgram : Tensor.Program.Origins table problem.initialProgram
  derivative : Tensor.Program.Origins table problem.derivative
  observation : Tensor.Program.Origins table problem.output

def IVP.Origins.extend (extension : before.Extension after)
    (origins : IVP.Origins before problem) : IVP.Origins after problem where
  model := extension.ref origins.model
  state := extension.ref origins.state
  input := extension.ref origins.input
  output := extension.ref origins.output
  initialProgram := origins.initialProgram.extend extension
  derivative := origins.derivative.extend extension
  observation := origins.observation.extend extension

end Rumoca.Solve

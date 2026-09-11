import RumocaCore.IR.Solve
import RumocaCore.Solve.IVPOrigins

/-! Required provenance for the existing prepared unit IVP. An empty input
channel and the state observation are generated deployment choices; neither
is a source declaration carrying a Modelica input/output qualifier. -/
namespace Rumoca.Solve
open _root_.Parser.Provenance (Ref Node)

/-- Pure executable data for the admitted unit equation. -/
def unitIVP : IVP where
  stateShape := Rumoca.Tensor.scalar
  inputShape := ⟨[0]⟩
  outputShape := Rumoca.Tensor.scalar
  initialProgram := Tensor.fill _ .zero
  derivative := Tensor.fill _ .one
  output := .ret .here

namespace FMI3Origins

inductive Field where
  | model | input | observation | policy | time | derivativeName
  | initialFill | initialReturn | initialRead
  | derivativeFill | derivativeReturn | derivativeRead
  | outputReturn | outputRead
  deriving Repr, DecidableEq

def Field.index : Field → Fin 14
  | .model => 0
  | .input => 1
  | .observation => 2
  | .policy => 3
  | .time => 4
  | .derivativeName => 5
  | .initialFill => 6
  | .initialReturn => 7
  | .initialRead => 8
  | .derivativeFill => 9
  | .derivativeReturn => 10
  | .derivativeRead => 11
  | .outputReturn => 12
  | .outputRead => 13

structure References (table : Provenance.Table context) where
  origin : Field → Ref table
  sourceOrigin : Rumoca.Origins.Field → Ref table

def References.trace (refs : References table) : IVP.Origins table unitIVP where
  model := refs.origin .model
  state := refs.sourceOrigin .declaration
  input := refs.origin .input
  output := refs.origin .observation
  initialProgram := .fill (refs.origin .initialFill)
    (.ret (refs.origin .initialReturn) (refs.origin .initialRead))
  derivative := .fill (refs.origin .derivativeFill)
    (.ret (refs.origin .derivativeReturn) (refs.origin .derivativeRead))
  observation := .ret (refs.origin .outputReturn) (refs.origin .outputRead)

/-- Independent semantic-role requirements. Source references are the original
parser entries, while generated records explain each new operation. -/
def References.expected (solve : Model source)
    {table : Provenance.Table solve.dae.flat.context} (refs : References table) : Field →
    Node (_root_.Parser.Provenance.SourceRef solve.dae.flat.context.input.inputs) Provenance.Rule
  | .model => .derived .prepareIVP solve.origins.derivative.root.index.val
      #[(solve.sourceOrigin .model).index.val]
  | .input => .generated .emptyInputChannel (refs.origin .model).index.val #[]
  | .observation => .generated .stateObservation (solve.sourceOrigin .stateName).index.val
      #[(solve.sourceOrigin .declaration).index.val]
  | .policy => .generated .unitEulerPolicy (refs.origin .model).index.val
      #[solve.origins.derivative.root.index.val]
  | .time => .generated .independentTime (refs.origin .model).index.val #[]
  | .derivativeName => .generated .derivativeName (solve.sourceOrigin .stateName).index.val
      #[solve.origins.derivative.root.index.val]
  | .initialFill => .derived .tensorInitial solve.origins.completion.index.val #[]
  | .initialReturn => .generated .tensorReturn (refs.origin .initialFill).index.val #[]
  | .initialRead => .generated .tensorRead (refs.origin .initialFill).index.val #[]
  | .derivativeFill => .derived .tensorDerivative solve.origins.derivative.root.index.val #[]
  | .derivativeReturn => .generated .tensorReturn (refs.origin .derivativeFill).index.val #[]
  | .derivativeRead => .generated .tensorRead (refs.origin .derivativeFill).index.val #[]
  | .outputReturn => .generated .tensorReturn (refs.origin .observation).index.val #[]
  | .outputRead => .generated .tensorRead (solve.sourceOrigin .stateName).index.val
      #[(refs.origin .observation).index.val]

def References.Correct (solve : Model source)
    {table : Provenance.Table solve.dae.flat.context} (refs : References table) : Prop :=
  (∀ field, (refs.sourceOrigin field).index.val = (solve.sourceOrigin field).index.val) ∧
  ∀ field, table.get (refs.origin field) = refs.expected solve field

structure Data (solve : Model source) where
  table : Provenance.Table solve.dae.flat.context
  extension : solve.origins.table.Extension table
  references : References table
  correct : references.Correct solve

end FMI3Origins
end Rumoca.Solve

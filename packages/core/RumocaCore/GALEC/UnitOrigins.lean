import RumocaCore.GALEC.Origins
import RumocaCore.IR.DAE

/-! Independent provenance requirements for the admitted unit Algorithm Code.
The period is a generated sampling policy, never attributed to the source RHS
literal merely because both happen to be one. -/
namespace Rumoca.GALEC.UnitOrigins
open _root_.Parser.Provenance (Ref Node)

inductive Field where
  | model | periodDeclaration | periodValue | fallback | initial
  | startup | startupAssignment | startupTarget | recalibrate
  | doStep | stepRead | increment | addition | stepAssignment | stepTarget
  | periodAssignment | periodTarget
  deriving Repr, DecidableEq

def Field.index : Field → Fin 17
  | .model => 0
  | .periodDeclaration => 1
  | .periodValue => 2
  | .fallback => 3
  | .initial => 4
  | .startup => 5
  | .startupAssignment => 6
  | .startupTarget => 7
  | .recalibrate => 8
  | .doStep => 9
  | .stepRead => 10
  | .increment => 11
  | .addition => 12
  | .stepAssignment => 13
  | .stepTarget => 14
  | .periodAssignment => 15
  | .periodTarget => 16

/-- All generated occurrences are required. A function over the closed field
type is total; there is no missing-index or default-origin case. -/
structure References (table : Provenance.Table context) where
  origin : Field → Ref table
  stateDeclaration : Ref table

def References.trace (refs : References table) : Block.Origins table unitBlock where
  model := refs.origin .model
  stateDeclaration := refs.stateDeclaration
  startup := .assign (refs.origin .startup) (refs.origin .startupAssignment) (refs.origin .startupTarget)
    (.zero (refs.origin .initial))
  recalibrate := .empty (refs.origin .recalibrate)
  doStep := .assign (refs.origin .doStep) (refs.origin .stepAssignment) (refs.origin .stepTarget)
    (.add (refs.origin .addition) (.state (refs.origin .stepRead)) (.one (refs.origin .increment)))
  periodDeclaration := refs.origin .periodDeclaration
  periodAssignment := refs.origin .periodAssignment
  periodTarget := refs.origin .periodTarget
  periodValue := .one (refs.origin .periodValue)

/-- The specified parent relationship uses semantic roles, not the builder's
array positions. Reads and writes identify the original declared state; the
step increment additionally records the selected sampling period. -/
def References.expected (dae : DAE.Model source)
    {table : Provenance.Table dae.flat.context} (refs : References table) : Field →
    Node (_root_.Parser.Provenance.SourceRef dae.flat.context.input.inputs) Provenance.Rule
  | .model => .derived .algorithmAdmission dae.origins.expression.root.index.val
      #[dae.flat.origins.model.index.val]
  | .periodDeclaration => .generated .unitSamplingPeriod (refs.origin .model).index.val #[]
  | .periodValue => .generated .samplingPeriodValue (refs.origin .periodDeclaration).index.val #[]
  | .fallback => .generated .realStartFallback dae.initializationOrigin.index.val #[]
  | .initial => .generated .selectUnfixedStart (refs.origin .fallback).index.val #[]
  | .startup => .generated .algorithmStartup (refs.origin .model).index.val
      #[(refs.origin .initial).index.val, (refs.origin .periodDeclaration).index.val]
  | .startupAssignment => .generated .algorithmStateInitialization (refs.origin .initial).index.val
      #[dae.flat.origins.state.index.val]
  | .startupTarget => .generated .algorithmStateWrite (refs.origin .startupAssignment).index.val
      #[dae.flat.origins.state.index.val]
  | .recalibrate => .generated .algorithmRecalibrate (refs.origin .model).index.val
      #[dae.flat.origins.declaration.index.val]
  | .doStep => .generated .algorithmDoStep (refs.origin .model).index.val
      #[dae.origins.expression.root.index.val, (refs.origin .periodValue).index.val]
  | .stepRead => .generated .algorithmStateRead (refs.origin .doStep).index.val
      #[dae.flat.origins.state.index.val]
  | .increment => .derived .unitAlgorithmIncrement dae.origins.expression.root.index.val
      #[(refs.origin .periodValue).index.val]
  | .addition => .derived .unitAlgorithmStep dae.origins.expression.root.index.val
      #[(refs.origin .stepRead).index.val, (refs.origin .increment).index.val]
  | .stepAssignment => .generated .algorithmStateUpdate (refs.origin .addition).index.val
      #[dae.flat.origins.state.index.val]
  | .stepTarget => .generated .algorithmStateWrite (refs.origin .stepAssignment).index.val
      #[dae.flat.origins.state.index.val]
  | .periodAssignment => .generated .algorithmPeriodInitialization (refs.origin .startup).index.val
      #[(refs.origin .periodValue).index.val]
  | .periodTarget => .generated .algorithmPeriodWrite (refs.origin .periodAssignment).index.val
      #[(refs.origin .periodDeclaration).index.val]

def References.Correct (dae : DAE.Model source)
    {table : Provenance.Table dae.flat.context} (refs : References table) : Prop :=
  refs.stateDeclaration.index.val = dae.flat.origins.declaration.index.val ∧
  ∀ field, table.get (refs.origin field) = refs.expected dae field

end Rumoca.GALEC.UnitOrigins

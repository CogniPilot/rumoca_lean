import RumocaCore.Solve.AlgorithmSyntax
import Parser.ProvenanceExtension

/-! Exact operation and operand origins of prepared register programs. -/
namespace Rumoca.Solve.Algorithm
open Rumoca.Tensor
open Rumoca.Solve.Tensor (Ref)
open _root_.Parser.Provenance (Table)

variable {Site Rule : Type} {table : Table Site Rule}
abbrev Origin (table : Table Site Rule) := _root_.Parser.Provenance.Ref table

/-- Operation and operand occurrences remain distinct even when two operands
read the same register. Register types still retain complete tensor shapes. -/
inductive Program.Origins (table : Table Site Rule) : Program Γ shape → Type where
  | ret (command value : Origin table) : Origins table (.ret reference)
  | fill (operation : Origin table) (next : Origins table program) :
      Origins table (.fill literal program)
  | add (operation left right : Origin table) (next : Origins table program) :
      Origins table (.add lhs rhs program)

/-- Independent provenance observations record the exact operation and operand
origins. Tensor extents never enter this operation-level observation. -/
inductive OriginEvent (table : Table Site Rule) where
  | fill (operation : Origin table)
  | add (operation left right : Origin table)
  | ret (command value : Origin table)

def Program.Origins.events : Program.Origins table program → List (OriginEvent table)
  | .ret command value => [.ret command value]
  | .fill operation next => .fill operation :: next.events
  | .add operation left right next => .add operation left right :: next.events

/-- Root and destination occurrences stay explicit alongside the program
traces. In particular, an assignment's target is not inferred from a value's
origin or discarded when the value becomes a return instruction. -/
structure Block.Origins (table : Table Site Rule) (block : Block shape) where
  model : Origin table
  stateDeclaration : Origin table
  startupMethod : Origin table
  startupTarget : Origin table
  startup : Program.Origins table block.startup
  recalibrateMethod : Origin table
  recalibrateTarget : Origin table
  recalibrate : Program.Origins table block.recalibrate
  doStepMethod : Origin table
  doStepTarget : Origin table
  doStep : Program.Origins table block.doStep
  periodDeclaration : Origin table
  periodTarget : Origin table
  period : Program.Origins table block.startupPeriod

end Rumoca.Solve.Algorithm

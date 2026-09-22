import Parser.DecimalNat
import RumocaCore.GALEC.Elaboration.Static.Dimensions

/-! Mathematical nonnegative static Integer expressions: unsigned decimal
literals, dimension queries and parentheses. Neither runtime values nor
backend inference participate. Target Integer representability, general signed
arithmetic and loop-iterator-dependent expressions remain separate obligations. -/
namespace Rumoca.GALEC.Elaboration.Static.Naturals
open _root_.Parser
open Rumoca.Tensor Elaboration

def read (lookupShape : List String → Option Shape) : AST.Expr → Option Nat
  | .literal (.literal spelling) => DecimalNat.parse spelling
  | .size reference axis => (read lookupShape axis).bind (Dimensions.read lookupShape reference)
  | .parens body => read lookupShape body
  | _ => none

/-- Independent mathematical source interpretation of this static subset. -/
inductive Evaluates (HasShape : List String → Shape → Prop) : AST.Expr → Nat → Prop where
  | literal : DecimalNat.Denotes spelling value →
      Evaluates HasShape (.literal (.literal spelling)) value
  | size : Evaluates HasShape axis position → Dimensions.Denotes HasShape reference position extent →
      Evaluates HasShape (.size reference axis) extent
  | parens : Evaluates HasShape body value → Evaluates HasShape (.parens body) value

theorem read_sound (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (source : AST.Expr) (value : Nat) (found : read lookupShape source = some value) :
    Evaluates HasShape source value := by
  unfold read at found
  split at found
  · exact .literal ((DecimalNat.parse_iff _ _).mp found)
  · rename_i reference axis
    obtain ⟨position, axisFound, dimension⟩ := Option.bind_eq_some_iff.mp found
    exact .size (read_sound lookupShape HasShape correct axis position axisFound)
      ((Dimensions.read_iff lookupShape HasShape correct reference position value).mp dimension)
  · rename_i body
    exact .parens (read_sound lookupShape HasShape correct body value found)
  · contradiction
termination_by sizeOf source

theorem read_complete (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (evaluated : Evaluates HasShape source value) : read lookupShape source = some value := by
  induction evaluated with
  | literal spelling => exact (DecimalNat.parse_iff _ _).mpr spelling
  | size axis dimension ih =>
    simp only [read, ih, Option.bind_some]
    exact (Dimensions.read_iff lookupShape HasShape correct _ _ _).mpr dimension
  | parens inner ih => exact ih

theorem read_iff (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (source : AST.Expr) (value : Nat) :
    read lookupShape source = some value ↔ Evaluates HasShape source value :=
  ⟨read_sound lookupShape HasShape correct source value, read_complete lookupShape HasShape correct⟩

theorem evaluates_unique (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (first : Evaluates HasShape source a) (second : Evaluates HasShape source b) : a = b :=
  Option.some.inj ((read_complete lookupShape HasShape correct first).symm.trans
    (read_complete lookupShape HasShape correct second))

/-- Every canonical unsigned numeral retains its mathematical value; this
does not assert that the production grammar admits every such numeral. -/
theorem render_literal (lookupShape : List String → Option Shape) (value : Nat) :
    read lookupShape (.literal (.literal (toString value))) = some value :=
  DecimalNat.parse_render value

def bindingRead (table : BindingTable inputs outputs) : AST.Expr → Option Nat :=
  read (Dimensions.bindingShape table)

theorem binding_read_iff (table : BindingTable inputs outputs) (source : AST.Expr) (value : Nat) :
    bindingRead table source = some value ↔ Evaluates (Dimensions.HasBindingShape table) source value :=
  read_iff _ _ (Dimensions.bindingShape_iff table) source value

end Rumoca.GALEC.Elaboration.Static.Naturals

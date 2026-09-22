import RumocaCore.GALEC.Elaboration.Static.Naturals

/-! Explicit representability checks at every supported static expression
node, not merely at the root. The ceiling is a caller-supplied nonnegative
Integer profile; no bit width or machine arithmetic is assumed. -/
namespace Rumoca.GALEC.Elaboration.Static.Bounded
open _root_.Parser
open Rumoca.Tensor Elaboration

def fit (ceiling value : Nat) : Option Nat :=
  if value ≤ ceiling then some value else none

theorem fit_iff (ceiling candidate value : Nat) :
    fit ceiling candidate = some value ↔ candidate = value ∧ value ≤ ceiling := by
  unfold fit
  split <;> simp_all <;> omega

def read (lookupShape : List String → Option Shape) (ceiling : Nat) : AST.Expr → Option Nat
  | .literal (.literal spelling) => (DecimalNat.parse spelling).bind (fit ceiling)
  | .size reference axis => (read lookupShape ceiling axis).bind fun position =>
      (Dimensions.read lookupShape reference position).bind (fit ceiling)
  | .parens body => read lookupShape ceiling body
  | _ => none

inductive Evaluates (HasShape : List String → Shape → Prop) (ceiling : Nat) : AST.Expr → Nat → Prop where
  | literal : DecimalNat.Denotes spelling value → value ≤ ceiling →
      Evaluates HasShape ceiling (.literal (.literal spelling)) value
  | size : Evaluates HasShape ceiling axis position →
      Dimensions.Denotes HasShape reference position extent → extent ≤ ceiling →
      Evaluates HasShape ceiling (.size reference axis) extent
  | parens : Evaluates HasShape ceiling body value → Evaluates HasShape ceiling (.parens body) value

theorem read_sound (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) (source : AST.Expr) (value : Nat)
    (found : read lookupShape ceiling source = some value) : Evaluates HasShape ceiling source value := by
  unfold read at found
  split at found
  · obtain ⟨candidate, spelled, fitted⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨rfl, bounded⟩ := (fit_iff ceiling candidate value).mp fitted
    exact .literal ((DecimalNat.parse_iff _ _).mp spelled) bounded
  · rename_i reference axis
    simp only [Option.bind_eq_some_iff] at found
    obtain ⟨position, axisFound, extent, dimension, fitted⟩ := found
    obtain ⟨rfl, bounded⟩ := (fit_iff ceiling extent value).mp fitted
    exact .size (read_sound lookupShape HasShape correct ceiling axis position axisFound)
      ((Dimensions.read_iff lookupShape HasShape correct _ _ _).mp dimension) bounded
  · rename_i body
    exact .parens (read_sound lookupShape HasShape correct ceiling body value found)
  · contradiction
termination_by sizeOf source

theorem read_complete (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (evaluated : Evaluates HasShape ceiling source value) :
    read lookupShape ceiling source = some value := by
  induction evaluated with
  | literal spelling bounded =>
    simp only [read, (DecimalNat.parse_iff _ _).mpr spelling, Option.bind_some]
    exact (fit_iff _ _ _).mpr ⟨rfl, bounded⟩
  | size axis dimension bounded ih =>
    simp only [read, ih, Option.bind_some, (Dimensions.read_iff _ _ correct _ _ _).mpr dimension]
    exact (fit_iff _ _ _).mpr ⟨rfl, bounded⟩
  | parens inner ih => exact ih

theorem read_iff (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) (source : AST.Expr) (value : Nat) :
    read lookupShape ceiling source = some value ↔ Evaluates HasShape ceiling source value :=
  ⟨read_sound lookupShape HasShape correct ceiling source value,
    read_complete lookupShape HasShape correct⟩

theorem forget (evaluated : Evaluates HasShape ceiling source value) :
    Naturals.Evaluates HasShape source value := by
  induction evaluated with
  | literal spelling _ => exact .literal spelling
  | size _ dimension _ ih => exact .size ih dimension
  | parens _ ih => exact .parens ih

theorem value_bound (evaluated : Evaluates HasShape ceiling source value) : value ≤ ceiling := by
  induction evaluated with
  | literal _ bounded => exact bounded
  | size _ _ bounded _ => exact bounded
  | parens _ ih => exact ih

/-- Mathematical source Integer range only; counter instructions and a concrete
target representation still require their own profile/execution contracts. -/
theorem integer_bounds (evaluated : Evaluates HasShape ceiling source value) :
    (0 : Int) ≤ Int.ofNat value ∧ Int.ofNat value ≤ Int.ofNat ceiling := by
  have bounded := value_bound evaluated
  change 0 ≤ (value : Int) ∧ (value : Int) ≤ (ceiling : Int)
  omega

def bindingRead (table : BindingTable inputs outputs) (ceiling : Nat) : AST.Expr → Option Nat :=
  read (Dimensions.bindingShape table) ceiling

theorem binding_read_iff (table : BindingTable inputs outputs) (ceiling : Nat)
    (source : AST.Expr) (value : Nat) :
    bindingRead table ceiling source = some value ↔
      Evaluates (Dimensions.HasBindingShape table) ceiling source value :=
  read_iff _ _ (Dimensions.bindingShape_iff table) ceiling source value

end Rumoca.GALEC.Elaboration.Static.Bounded

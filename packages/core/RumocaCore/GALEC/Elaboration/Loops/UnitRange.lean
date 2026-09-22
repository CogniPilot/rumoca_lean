import RumocaCore.GALEC.Elaboration.Static.Bounded
import RumocaCore.GALEC.IntegerIteration
import RumocaCore.GALEC.Elaboration.Declarations.ShapeLookup

/-! The explicit ascending unit-range branch of source elaboration. Start,
step and stop are evaluated through the reusable static semantics, not matched
as token patterns. Omitted-step defaults and arbitrary strides remain separate
branches. The positive range is an authored repair profile, not full GALEC
loop completeness or a machine-counter contract. -/
namespace Rumoca.GALEC.Elaboration.Loops.UnitRange
open Rumoca.Tensor Elaboration.Static

def read (lookupShape : List String → Option Shape) (ceiling : Nat)
    (start : AST.Expr) (step : Option AST.Expr) (stop : AST.Expr) : Option Nat :=
  match step with
  | none => none
  | some stride => (Bounded.read lookupShape ceiling start).bind fun first =>
      (Bounded.read lookupShape ceiling stride).bind fun increment =>
        (Bounded.read lookupShape ceiling stop).bind fun last =>
          if first = 1 ∧ increment = 1 ∧ 0 < last then some last else none

inductive Denotes (HasShape : List String → Shape → Prop) (ceiling : Nat) :
    AST.Expr → Option AST.Expr → AST.Expr → Nat → Prop where
  | unit (first : Bounded.Evaluates HasShape ceiling start 1)
      (increment : Bounded.Evaluates HasShape ceiling stride 1)
      (last : Bounded.Evaluates HasShape ceiling stop count) (positive : 0 < count) :
      Denotes HasShape ceiling start (some stride) stop count

theorem read_iff (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) (start : AST.Expr) (step : Option AST.Expr) (stop : AST.Expr) (count : Nat) :
    read lookupShape ceiling start step stop = some count ↔
      Denotes HasShape ceiling start step stop count := by
  constructor
  · intro found
    cases step with
    | none => cases found
    | some stride =>
      obtain ⟨first, firstRead, remaining⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨increment, incrementRead, remaining⟩ := Option.bind_eq_some_iff.mp remaining
      obtain ⟨last, lastRead, accepted⟩ := Option.bind_eq_some_iff.mp remaining
      split at accepted
      · rename_i conditions
        obtain ⟨rfl, rfl, positive⟩ := conditions
        cases Option.some.inj accepted
        exact .unit ((Bounded.read_iff _ _ correct _ _ _).mp firstRead)
          ((Bounded.read_iff _ _ correct _ _ _).mp incrementRead)
          ((Bounded.read_iff _ _ correct _ _ _).mp lastRead) positive
      · contradiction
  · intro denoted
    cases denoted with
    | unit first increment last positive =>
      simp only [read, (Bounded.read_iff _ _ correct _ _ _).mpr first,
        (Bounded.read_iff _ _ correct _ _ _).mpr increment,
        (Bounded.read_iff _ _ correct _ _ _).mpr last, Option.bind_some]
      simp [positive]

theorem count_bounds (denoted : Denotes HasShape ceiling start step stop count) :
    0 < count ∧ count ≤ ceiling := by
  cases denoted with
  | unit _ _ last positive => exact ⟨positive, Bounded.value_bound last⟩

theorem count_unique (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (first : Denotes HasShape ceiling start step stop a)
    (second : Denotes HasShape ceiling start step stop b) : a = b :=
  Option.some.inj (((read_iff _ _ correct _ _ _ _ _).mpr first).symm.trans
    ((read_iff _ _ correct _ _ _ _ _).mpr second))

/-- Source execution uses mathematical Integer iterator values and retains
the actual intermediate states of an arbitrary partial/nondeterministic body.
It does not invoke the range reader or bounded Fin execution. -/
def Executes (HasShape : List String → Shape → Prop) (ceiling : Nat)
    (start : AST.Expr) (stride : Option AST.Expr) (stop : AST.Expr)
    (body : Int → State → State → Prop) (before after : State) : Prop :=
  ∃ count, Denotes HasShape ceiling start stride stop count ∧
    Rumoca.GALEC.IntegerIteration.Executes body count before after

theorem executes_iff (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (denoted : Denotes HasShape ceiling start stride stop count)
    (body : Int → State → State → Prop) (before after : State) :
    Executes HasShape ceiling start stride stop body before after ↔
      Iteration.Executes (fun i : Fin count => body (Int.ofNat i.val + 1)) count before after := by
  constructor
  · rintro ⟨actual, sourceRange, executed⟩
    have same := count_unique lookupShape HasShape correct sourceRange denoted
    subst actual
    exact (Rumoca.GALEC.IntegerIteration.executes_iff body count before after).mp executed
  · intro executed
    exact ⟨count, denoted, (Rumoca.GALEC.IntegerIteration.executes_iff body count before after).mpr executed⟩

theorem active_bounds (denoted : Denotes HasShape ceiling start stride stop count) (i : Fin count) :
    1 ≤ Int.ofNat i.val + 1 ∧ Int.ofNat i.val + 1 ≤ Int.ofNat count ∧
      Int.ofNat i.val + 1 ≤ Int.ofNat ceiling := by
  apply Rumoca.GALEC.IntegerIteration.one_based_representable count (Int.ofNat ceiling) _ i
  have bounded := (count_bounds denoted).2
  change (count : Int) ≤ (ceiling : Int)
  omega

theorem declarations_read_iff
    (declared : Elaboration.Declarations.Real.DeclaresAll ceiling sources declarations)
    (start : AST.Expr) (stride : Option AST.Expr) (stop : AST.Expr) (count : Nat) :
    read (Elaboration.Declarations.ShapeLookup.read declarations) ceiling start stride stop = some count ↔
      Denotes (Elaboration.Declarations.ShapeLookup.HasShape ceiling sources) ceiling start stride stop count :=
  read_iff _ _ (Elaboration.Declarations.ShapeLookup.read_iff declared) ceiling start stride stop count

end Rumoca.GALEC.Elaboration.Loops.UnitRange

import RumocaCore.GALEC.Elaboration.Assignments
import RumocaCore.GALEC.Elaboration.Loops.Header

/-! Independent execution of actual nested AST bodies. Integer iteration,
source assignment/address semantics and intermediate stores specify behavior;
neither the compiler nor target Statement.Executes defines this relation. -/
namespace Rumoca.GALEC.Elaboration.Bodies.Source
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor

def atInteger (body : Fin count → State → State → Prop)
    (integer : Int) (before after : State) : Prop :=
  ∃ index : Fin count, Int.ofNat index.val + 1 = integer ∧ body index before after

theorem atInteger_one_based (body : Fin count → State → State → Prop)
    (index : Fin count) (before after : State) :
    atInteger body (Int.ofNat index.val + 1) before after ↔ body index before after := by
  constructor
  · rintro ⟨other, same, executed⟩
    have equal : other = index := by
      apply Fin.ext
      change (other.val : Int) + 1 = (index.val : Int) + 1 at same
      omega
    cases equal
    exact executed
  · intro executed
    exact ⟨index, rfl, executed⟩

theorem integer_iterations_iff (body : Fin count → State → State → Prop) (before after : State) :
    IntegerIteration.Executes (atInteger body) count before after ↔
      Iteration.Executes body count before after :=
  (IntegerIteration.executes_iff (atInteger body) count before after).trans
    (Iteration.executes_congr _ _ (atInteger_one_based body) count before after)

mutual
def statement (table : BindingTable inputs outputs) (HasShape : List String → Shape → Prop)
    (ceiling : Nat) (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) {bounds : List Nat} (names : IteratorNames bounds) (env : IteratorEnv bounds)
    (source : AST.Statement) (before after : Env α outputs) : Prop :=
  match source with
  | .assign target value =>
      AssignmentLowering.Executes table names step zero one @input @env (.assign target value) @before @after
  | .forLoop binder start stride stop body =>
      ∃ name count, Loops.Header.Denotes names HasShape ceiling binder start stride stop name count ∧
        IntegerIteration.Executes (σ := Env α outputs)
          (atInteger (fun index current next =>
            statements table HasShape ceiling step zero one @input
              (.cons (bound := count) name names) (IteratorEnv.push index @env) body @current @next))
          count @before @after
termination_by sizeOf source

def statements (table : BindingTable inputs outputs) (HasShape : List String → Shape → Prop)
    (ceiling : Nat) (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) {bounds : List Nat} (names : IteratorNames bounds) (env : IteratorEnv bounds)
    (sources : List AST.Statement) (before after : Env α outputs) : Prop :=
  match sources with
  | [] => @after = @before
  | source :: rest => ∃ middle : Env α outputs,
      statement table HasShape ceiling step zero one @input names @env source @before @middle ∧
      statements table HasShape ceiling step zero one @input names @env rest @middle @after
termination_by sizeOf sources
end

/-- Representation change for the same actual source body, not a comparison
to target execution. Header uniqueness retains exactly the selected binder
and count; the body relation remains partial and state dependent. -/
theorem loop_finite_iff (table : BindingTable inputs outputs)
    (lookupShape : List String → Option Shape) (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) {bounds : List Nat} (names : IteratorNames bounds) (env : IteratorEnv bounds)
    (header : Loops.Header.Denotes names HasShape ceiling binder start stride stop name count)
    (body : List AST.Statement) (before after : Env α outputs) :
    statement table HasShape ceiling step zero one @input names @env
        (.forLoop binder start stride stop body) @before @after ↔
      Iteration.Executes (σ := Env α outputs)
        (fun index current next => statements table HasShape ceiling step zero one @input
          (.cons (bound := count) name names) (IteratorEnv.push index @env) body @current @next)
        count @before @after := by
  rw [statement]
  constructor
  · rintro ⟨actualName, actualCount, actualHeader, executed⟩
    have same := Option.some.inj
      (((Loops.Header.read_iff _ _ _ correct _ _ _ _ _ _ _).mpr actualHeader).symm.trans
        ((Loops.Header.read_iff _ _ _ correct _ _ _ _ _ _ _).mpr header))
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact (integer_iterations_iff _ @before @after).mp executed
  · intro executed
    exact ⟨name, count, header, (integer_iterations_iff _ @before @after).mpr executed⟩

end Rumoca.GALEC.Elaboration.Bodies.Source

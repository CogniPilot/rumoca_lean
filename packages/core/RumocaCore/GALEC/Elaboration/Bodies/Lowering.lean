import RumocaCore.GALEC.Elaboration.StatementLists
import RumocaCore.GALEC.Elaboration.Loops.Header

/-! Structural lowering of actual nested source bodies. Recursion traverses
the original AST and statement lists, never loop iterations or tensor cells.
Only existing indexed core statements are produced; no callbacks enter IR. -/
namespace Rumoca.GALEC.Elaboration.Bodies
open Elaboration Rumoca.Tensor

mutual
def statement (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (source : AST.Statement) : Option (Statement inputs outputs bounds) :=
  match source with
  | .assign target value => AssignmentLowering.lower table names (.assign target value)
  | .forLoop binder start stride stop body =>
      (Loops.Header.read names lookupShape ceiling binder start stride stop).bind fun (name, count) =>
        (statements table lookupShape ceiling (.cons (bound := count) name names) body).map
          (Statement.bounded count)
termination_by sizeOf source

def statements (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List AST.Statement) : Option (Statement inputs outputs bounds) :=
  match sources with
  | [] => some .skip
  | source :: rest => (statement table lookupShape ceiling names source).bind fun first =>
      (statements table lookupShape ceiling names rest).map (Statement.seq first)
termination_by sizeOf sources
end

mutual
inductive StatementElaborates (table : BindingTable inputs outputs)
    (HasShape : List String → Shape → Prop) (ceiling : Nat) :
    {bounds : List Nat} → IteratorNames bounds → AST.Statement → Statement inputs outputs bounds → Prop where
  | assign : AssignmentLowering.Elaborates table names source stmt →
      StatementElaborates table HasShape ceiling names source stmt
  | loop : Loops.Header.Denotes names HasShape ceiling binder start stride stop name count →
      BodyElaborates table HasShape ceiling (.cons (bound := count) name names) body loweredBody →
      StatementElaborates table HasShape ceiling names (.forLoop binder start stride stop body)
        (.bounded count loweredBody)

inductive BodyElaborates (table : BindingTable inputs outputs)
    (HasShape : List String → Shape → Prop) (ceiling : Nat) :
    {bounds : List Nat} → IteratorNames bounds → List AST.Statement → Statement inputs outputs bounds → Prop where
  | nil : BodyElaborates table HasShape ceiling names [] .skip
  | cons : StatementElaborates table HasShape ceiling names source first →
      BodyElaborates table HasShape ceiling names rest remaining →
      BodyElaborates table HasShape ceiling names (source :: rest) (.seq first remaining)
end

mutual
theorem statement_sound (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (source : AST.Statement) (stmt : Statement inputs outputs bounds)
    (found : statement table lookupShape ceiling names source = some stmt) :
    StatementElaborates table HasShape ceiling names source stmt := by
  cases source with
  | assign target value =>
    rw [statement] at found
    exact .assign ((AssignmentLowering.lower_iff _ _ _ _).mp found)
  | forLoop binder start stride stop body =>
    rw [statement] at found
    obtain ⟨⟨name, count⟩, header, lowered⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨loweredBody, bodyFound, same⟩ := Option.map_eq_some_iff.mp lowered
    cases same
    exact .loop ((Loops.Header.read_iff _ _ _ correct _ _ _ _ _ _ _).mp header)
      (statements_sound table lookupShape HasShape correct ceiling _ body loweredBody bodyFound)
termination_by sizeOf source

theorem statements_sound (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds)
    (found : statements table lookupShape ceiling names sources = some stmt) :
    BodyElaborates table HasShape ceiling names sources stmt := by
  cases sources with
  | nil =>
    rw [statements] at found
    cases Option.some.inj found
    exact .nil
  | cons source rest =>
    rw [statements] at found
    obtain ⟨first, firstFound, lowered⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨remaining, restFound, same⟩ := Option.map_eq_some_iff.mp lowered
    cases same
    exact .cons (statement_sound table lookupShape HasShape correct ceiling names source first firstFound)
      (statements_sound table lookupShape HasShape correct ceiling names rest remaining restFound)
termination_by sizeOf sources
end

mutual
theorem statement_complete (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (source : AST.Statement) (stmt : Statement inputs outputs bounds)
    (typed : StatementElaborates table HasShape ceiling names source stmt) :
    statement table lookupShape ceiling names source = some stmt := by
  cases typed with
  | assign assignment =>
    cases assignment with
    | assign target value =>
      rw [statement]
      exact (AssignmentLowering.lower_iff _ _ _ _).mpr (.assign target value)
  | loop header body =>
    simp only [statement, (Loops.Header.read_iff _ _ _ correct _ _ _ _ _ _ _).mpr header,
      Option.bind_some, statements_complete table lookupShape HasShape correct ceiling _ _ _ body,
      Option.map_some]
termination_by sizeOf source

theorem statements_complete (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds)
    (typed : BodyElaborates table HasShape ceiling names sources stmt) :
    statements table lookupShape ceiling names sources = some stmt := by
  cases typed with
  | nil => rw [statements]
  | cons first rest =>
    simp only [statements, statement_complete table lookupShape HasShape correct ceiling _ _ _ first,
      Option.bind_some, statements_complete table lookupShape HasShape correct ceiling _ _ _ rest,
      Option.map_some]
termination_by sizeOf sources
end

theorem statement_iff (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (source : AST.Statement) (stmt : Statement inputs outputs bounds) :
    statement table lookupShape ceiling names source = some stmt ↔
      StatementElaborates table HasShape ceiling names source stmt :=
  ⟨statement_sound table lookupShape HasShape correct ceiling names source stmt,
    statement_complete table lookupShape HasShape correct ceiling names source stmt⟩

theorem statements_iff (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds) :
    statements table lookupShape ceiling names sources = some stmt ↔
      BodyElaborates table HasShape ceiling names sources stmt :=
  ⟨statements_sound table lookupShape HasShape correct ceiling names sources stmt,
    statements_complete table lookupShape HasShape correct ceiling names sources stmt⟩

end Rumoca.GALEC.Elaboration.Bodies

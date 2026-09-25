import RumocaCore.GALEC.Elaboration.StatementLists
import RumocaCore.GALEC.Elaboration.Loops.Header
import RumocaCore.GALEC.Elaboration.Conditions

/-! Structural lowering of actual nested source bodies. Recursion traverses
the original AST and statement lists, never loop iterations or tensor cells.
An `if` statement lowers to nested branches in source order, its `else` body
(or nothing) last; an error-signal statement lowers to the set it names. Only
existing indexed core statements are produced; no callbacks enter IR. -/
namespace Rumoca.GALEC.Elaboration.Bodies
open Elaboration Rumoca.Tensor

mutual
def statement (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (source : AST.Statement) : Option (Statement inputs outputs bounds) :=
  match source with
  | .assign target value => AssignmentLowering.lower table names (.assign target value)
  | .ifThen [] _ => none
  | .ifThen (first :: rest) otherwise =>
      branches table lookupShape ceiling names (first :: rest) otherwise
  | .forLoop binder start stride stop body =>
      (Loops.Header.read names lookupShape ceiling binder start stride stop).bind fun (name, count) =>
        (statements table lookupShape ceiling (.cons (bound := count) name names) body).map
          (Statement.bounded count)
  | .signal [] => none
  | .signal (first :: rest) => (SignalNames.read (first :: rest)).map Statement.signal
termination_by sizeOf source

def branches (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List (AST.Condition × List AST.Statement)) (otherwise : Option (List AST.Statement)) :
    Option (Statement inputs outputs bounds) :=
  match sources with
  | [] =>
      match otherwise with
      | none => some .skip
      | some body => statements table lookupShape ceiling names body
  | (test, body) :: rest =>
      (ConditionLowering.lower table names test).bind fun condition =>
        (statements table lookupShape ceiling names body).bind fun yes =>
          (branches table lookupShape ceiling names rest otherwise).map (Statement.branch condition yes)
termination_by sizeOf sources + sizeOf otherwise

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
  | branch : BranchesElaborates table HasShape ceiling names (first :: rest) otherwise stmt →
      StatementElaborates table HasShape ceiling names (.ifThen (first :: rest) otherwise) stmt
  | loop : Loops.Header.Denotes names HasShape ceiling binder start stride stop name count →
      BodyElaborates table HasShape ceiling (.cons (bound := count) name names) body loweredBody →
      StatementElaborates table HasShape ceiling names (.forLoop binder start stride stop body)
        (.bounded count loweredBody)
  | signal : SignalNames.Denotes (first :: rest) raised →
      StatementElaborates table HasShape ceiling names (.signal (first :: rest)) (.signal raised)

inductive BranchesElaborates (table : BindingTable inputs outputs)
    (HasShape : List String → Shape → Prop) (ceiling : Nat) :
    {bounds : List Nat} → IteratorNames bounds → List (AST.Condition × List AST.Statement) →
      Option (List AST.Statement) → Statement inputs outputs bounds → Prop where
  | none : BranchesElaborates table HasShape ceiling names [] none .skip
  | otherwise : BodyElaborates table HasShape ceiling names body stmt →
      BranchesElaborates table HasShape ceiling names [] (some body) stmt
  | cons : ConditionLowering.Elaborates table names test condition →
      BodyElaborates table HasShape ceiling names body yes →
      BranchesElaborates table HasShape ceiling names rest otherwise no →
      BranchesElaborates table HasShape ceiling names ((test, body) :: rest) otherwise
        (.branch condition yes no)

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
  match source with
  | .assign target value =>
    rw [statement] at found
    exact .assign ((AssignmentLowering.lower_iff _ _ _ _).mp found)
  | .ifThen [] otherwise =>
    rw [statement] at found
    cases found
  | .ifThen (first :: rest) otherwise =>
    rw [statement] at found
    exact .branch (branches_sound table lookupShape HasShape correct ceiling names _ otherwise stmt found)
  | .forLoop binder start stride stop body =>
    rw [statement] at found
    obtain ⟨⟨name, count⟩, header, lowered⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨loweredBody, bodyFound, same⟩ := Option.map_eq_some_iff.mp lowered
    cases same
    exact .loop ((Loops.Header.read_iff _ _ _ correct _ _ _ _ _ _ _).mp header)
      (statements_sound table lookupShape HasShape correct ceiling _ body loweredBody bodyFound)
  | .signal [] =>
    rw [statement] at found
    cases found
  | .signal (first :: rest) =>
    rw [statement] at found
    obtain ⟨raised, read, same⟩ := Option.map_eq_some_iff.mp found
    cases same
    exact .signal ((SignalNames.read_iff _ _).mp read)
termination_by sizeOf source

theorem branches_sound (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List (AST.Condition × List AST.Statement)) (otherwise : Option (List AST.Statement))
    (stmt : Statement inputs outputs bounds)
    (found : branches table lookupShape ceiling names sources otherwise = some stmt) :
    BranchesElaborates table HasShape ceiling names sources otherwise stmt := by
  match sources, otherwise with
  | [], none =>
    rw [branches] at found
    cases Option.some.inj found
    exact .none
  | [], some body =>
    rw [branches] at found
    exact .otherwise (statements_sound table lookupShape HasShape correct ceiling names body stmt found)
  | (test, body) :: rest, otherwise =>
    rw [branches] at found
    obtain ⟨condition, tested, remaining⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨yes, bodyFound, remaining⟩ := Option.bind_eq_some_iff.mp remaining
    obtain ⟨no, restFound, same⟩ := Option.map_eq_some_iff.mp remaining
    cases same
    exact .cons ((ConditionLowering.lower_iff _ _ _ _).mp tested)
      (statements_sound table lookupShape HasShape correct ceiling names body yes bodyFound)
      (branches_sound table lookupShape HasShape correct ceiling names rest otherwise no restFound)
termination_by sizeOf sources + sizeOf otherwise

theorem statements_sound (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds)
    (found : statements table lookupShape ceiling names sources = some stmt) :
    BodyElaborates table HasShape ceiling names sources stmt := by
  match sources with
  | [] =>
    rw [statements] at found
    cases Option.some.inj found
    exact .nil
  | source :: rest =>
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
  match source, typed with
  | _, .assign assignment =>
    cases assignment with
    | assign target value =>
      rw [statement]
      exact (AssignmentLowering.lower_iff _ _ _ _).mpr (.assign target value)
  | .ifThen (first :: rest) otherwise, .branch chosen =>
    rw [statement]
    exact branches_complete table lookupShape HasShape correct ceiling names _ otherwise stmt chosen
  | .forLoop binder start stride stop body, .loop header typedBody =>
    simp only [statement, (Loops.Header.read_iff _ _ _ correct _ _ _ _ _ _ _).mpr header,
      Option.bind_some, statements_complete table lookupShape HasShape correct ceiling _ body _ typedBody,
      Option.map_some]
  | .signal (first :: rest), .signal denoted =>
    simp only [statement, (SignalNames.read_iff _ _).mpr denoted, Option.map_some]
termination_by sizeOf source

theorem branches_complete (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List (AST.Condition × List AST.Statement)) (otherwise : Option (List AST.Statement))
    (stmt : Statement inputs outputs bounds)
    (typed : BranchesElaborates table HasShape ceiling names sources otherwise stmt) :
    branches table lookupShape ceiling names sources otherwise = some stmt := by
  match sources, otherwise, typed with
  | [], none, .none => rw [branches]
  | [], some body, .otherwise typedBody =>
    rw [branches]
    exact statements_complete table lookupShape HasShape correct ceiling names body stmt typedBody
  | (test, body) :: rest, otherwise, .cons tested typedBody typedRest =>
    simp only [branches, (ConditionLowering.lower_iff _ _ _ _).mpr tested, Option.bind_some,
      statements_complete table lookupShape HasShape correct ceiling names body _ typedBody,
      branches_complete table lookupShape HasShape correct ceiling names rest otherwise _ typedRest,
      Option.map_some]
termination_by sizeOf sources + sizeOf otherwise

theorem statements_complete (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds)
    (typed : BodyElaborates table HasShape ceiling names sources stmt) :
    statements table lookupShape ceiling names sources = some stmt := by
  match sources, typed with
  | [], .nil => rw [statements]
  | source :: rest, .cons first typedRest =>
    simp only [statements, statement_complete table lookupShape HasShape correct ceiling _ _ _ first,
      Option.bind_some, statements_complete table lookupShape HasShape correct ceiling _ _ _ typedRest,
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

/-- An error-signal statement naming anything but predefined signals is rejected. -/
theorem signal_rejected (table : BindingTable inputs outputs)
    (lookupShape : List String → Option Shape) (ceiling : Nat) {bounds : List Nat}
    (names : IteratorNames bounds) (raised : List AST.Name) (member : name ∈ raised)
    (unknown : SignalNames.readName name = none) :
    statement (outputs := outputs) table lookupShape ceiling names (.signal raised) = none := by
  cases raised with
  | nil => rw [statement]
  | cons first rest =>
    rw [statement, SignalNames.read_rejected member unknown]
    rfl

/-- A branch whose condition is not admitted rejects the whole `if` statement. -/
theorem condition_rejected (table : BindingTable inputs outputs)
    (lookupShape : List String → Option Shape) (ceiling : Nat) {bounds : List Nat}
    (names : IteratorNames bounds) (test : AST.Condition) (body : List AST.Statement)
    (rest : List (AST.Condition × List AST.Statement)) (otherwise : Option (List AST.Statement))
    (rejected : ConditionLowering.lower table names test = none) :
    statement (outputs := outputs) table lookupShape ceiling names
      (.ifThen ((test, body) :: rest) otherwise) = none := by
  rw [statement, branches, rejected]
  rfl

/-- A nonempty branch list always elaborates to a branch. -/
theorem branches_branch
    (typed : BranchesElaborates table HasShape ceiling names (first :: rest) otherwise stmt) :
    ∃ condition yes no, stmt = Statement.branch condition yes no := by
  cases typed with
  | cons _ _ _ => exact ⟨_, _, _, rfl⟩

end Rumoca.GALEC.Elaboration.Bodies

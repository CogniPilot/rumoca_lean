import RumocaCore.IR.DAE

namespace Rumoca.Solve
open _root_.Parser.Provenance (Ref Node TracesTo)

/-- Pure straight-line register semantics; occurrences carry the indexed trace
below. A return can only read an existing register. -/
inductive Program : Nat → Type where
  | ret (register : Fin n) : Program n
  | one (next : Program (n + 1)) : Program n
  deriving Repr

def evalWith (one : α) (program : Program n) (registers : Fin n → α) : α :=
  match program with
  | .ret register => registers register
  | .one next => evalWith one next
      (fun i => if h : i.val < n then registers ⟨i.val, h⟩ else one)

def eval (program : Program n) (registers : Fin n → Nat) : Nat := evalWith 1 program registers
def unitDerivative : Program 0 := .one (.ret 0)

inductive Program.Origins (table : Provenance.Table context) : Program n → Type where
  | ret (origin : Ref table) : Origins table (.ret register)
  | one (origin : Ref table) (next : Origins table program) : Origins table (.one program)

def Program.Origins.root : Program.Origins table program → Ref table
  | .ret origin => origin
  | .one origin _ => origin

/-- Returns retain the origin of the actual register they read. The relation
follows the pure register program, including the extension of its environment. -/
def Program.Origins.Correct (dae : DAE.Model source) {table : Provenance.Table dae.flat.context} :
    {n : Nat} → {program : Program n} → Program.Origins table program →
      (Fin n → Ref table) → Prop
  | _, .ret register, .ret origin, registers =>
      table.get origin = .generated .returnDerivative (registers register).index.val #[]
  | n, .one _, .one origin next, registers =>
      table.get origin = .derived .solveUnitDerivative dae.origins.expression.root.index.val #[] ∧
      next.Correct dae (fun i => if h : i.val < n then registers ⟨i.val, h⟩ else origin)

structure Origins (dae : DAE.Model source) (program : Program 0) where
  table : Provenance.Table dae.flat.context
  extension : dae.origins.table.Extension table
  derivative : Program.Origins table program
  initial : Ref table
  completion : Ref table
  derivative_correct : derivative.Correct dae Fin.elim0
  initial_correct : table.get initial =
    .generated .realStartFallback dae.initializationOrigin.index.val #[]
  completion_correct : table.get completion = .generated .selectUnfixedStart initial.index.val #[]

namespace OriginLowering

private def batch (dae : DAE.Model source) :
    Array (Node (_root_.Parser.Provenance.SourceRef dae.flat.context.input.inputs) Provenance.Rule) :=
  let size := dae.origins.table.nodes.size
  #[.derived .solveUnitDerivative dae.origins.expression.root.index.val #[],
    .generated .returnDerivative size #[],
    .generated .realStartFallback dae.initializationOrigin.index.val #[],
    .generated .selectUnfixedStart (size + 2) #[]]

private theorem batch_prior (dae : DAE.Model source) (index : Nat)
    (bound : index < (batch dae).size) (parent : Nat)
    (member : parent ∈ (batch dae)[index].parents) :
    parent < dae.origins.table.nodes.size + index := by
  cases index with
  | zero =>
      simp [batch, Node.parents] at member
      subst parent
      exact dae.origins.expression.root.index.isLt
  | succ index =>
    cases index with
    | zero => simp [batch, Node.parents] at member; omega
    | succ index =>
      cases index with
      | zero =>
          simp [batch, Node.parents] at member
          have := dae.initializationOrigin.index.isLt
          omega
      | succ index =>
        cases index with
        | zero => simp [batch, Node.parents] at member; omega
        | succ index => simp [batch] at bound; omega

def table (dae : DAE.Model source) : Provenance.Table dae.flat.context :=
  dae.origins.table.append (batch dae) (batch_prior dae)

theorem extension (dae : DAE.Model source) : dae.origins.table.Extension (table dae) :=
  dae.origins.table.append_extension (batch dae) (batch_prior dae)

private def atIndex (dae : DAE.Model source) (index : Fin 4) : Ref (table dae) :=
  dae.origins.table.appendedRef (batch dae) (batch_prior dae)
    ⟨index.val, by simp [batch]⟩

def lower (dae : DAE.Model source) : Origins dae unitDerivative where
  table := table dae
  extension := extension dae
  derivative := .one (atIndex dae 0) (.ret (atIndex dae 1))
  initial := atIndex dae 2
  completion := atIndex dae 3
  derivative_correct := by
    have first := dae.origins.table.appended_lookup (batch dae) (batch_prior dae)
      ⟨0, by simp [batch]⟩
    have second := dae.origins.table.appended_lookup (batch dae) (batch_prior dae)
      ⟨1, by simp [batch]⟩
    constructor
    · simpa only [table, atIndex, batch] using first
    · simpa [Program.Origins.Correct, table, atIndex, batch,
        _root_.Parser.Provenance.Table.appendedRef] using second
  initial_correct := by
    have checked := dae.origins.table.appended_lookup (batch dae) (batch_prior dae)
      ⟨2, by simp [batch]⟩
    simpa only [table, atIndex, batch] using checked
  completion_correct := by
    have checked := dae.origins.table.appended_lookup (batch dae) (batch_prior dae)
      ⟨3, by simp [batch]⟩
    simpa [table, atIndex, batch, _root_.Parser.Provenance.Table.appendedRef] using checked

end OriginLowering

structure Model (source : AST.Model) where
  dae : DAE.Model source
  derivative : Program 0
  derivative_source : derivative = unitDerivative
  origins : Origins dae derivative
  initial : Initialization.Plan Nat
  initial_checked : Initialization.prepare dae.initialization 0 = .ok initial

def lower (dae : DAE.Model source) : Model source :=
  let plan := Initialization.checked dae.initialization 0 dae.initialization_succeeds
  ⟨dae, unitDerivative, rfl, OriginLowering.lower dae, plan.val, plan.property⟩

def Model.noticeOrigin (model : Model source) : Initialization.Notice → Ref model.origins.table
  | .fallbackUsed => model.origins.initial
  | .unfixedStartSelected => model.origins.completion

theorem Model.initial_default (model : Model source) :
    model.initial = ⟨0, [.fallbackUsed, .unfixedStartSelected]⟩ := by
  have checked := model.initial_checked
  rw [model.dae.initialization_default] at checked
  exact (Except.ok.inj checked).symm

def Model.rhs (model : Model source) : Nat := eval model.derivative Fin.elim0

theorem Model.rhs_eq_one (model : Model source) : model.rhs = 1 := by
  simp [Model.rhs, model.derivative_source, unitDerivative, eval, evalWith]

end Rumoca.Solve

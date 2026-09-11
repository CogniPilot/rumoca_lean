import RumocaEFMI.StartupOrigins
import RumocaCore.GALEC.OriginProofs

/-! Independent requirements inspect each actual C occurrence. In particular,
period initialization and state initialization use distinct Solve operands;
the instance status word belongs to the adapter's Startup method. -/
namespace Rumoca.EFMI.Production.StartupOrigins
open Rumoca.CTree
open _root_.Parser.Provenance (Ref)
variable {table : _root_.Parser.Provenance.Table Site Provenance.Rule}

/-- The actual Solve trace retains the source-stage roles through both prior
lowerings. This proof does not change the executable emitter's input. -/
theorem inputs_lowered (model : Solve.Algorithm.Model source) :
    inputs model =
      ⟨model.origin.origins.references.origin .startup,
        model.origin.origins.references.origin .initial,
        model.origin.origins.references.origin .startupAssignment,
        model.origin.origins.references.origin .startupTarget,
        model.origin.origins.references.origin .initial,
        model.origin.origins.references.origin .periodValue,
        model.origin.origins.references.origin .periodAssignment,
        model.origin.origins.references.origin .periodTarget,
        model.origin.origins.references.origin .periodValue⟩ := by
  rcases model with ⟨⟨dae, galec, profile, gaOrigins⟩, block, lowered, origins, correct⟩
  cases profile
  cases lowered
  cases correct
  rfl

theorem Inputs.original_traces (input : Inputs table) (ref : Ref table)
    (trace : _root_.Parser.Provenance.TracesTo table ref site) :
    _root_.Parser.Provenance.TracesTo input.outputTable (input.original ref) site :=
  (trace.mapRule Rule.upstream).extend input.extension

theorem state_literal_source (model : Solve.Algorithm.Model source) :
    _root_.Parser.Provenance.TracesTo (inputs model).outputTable
      ((inputs model).original (inputs model).stateLiteral)
      (model.origin.dae.flat.context.site .declaration) := by
  apply Inputs.original_traces
  rw [inputs_lowered]
  exact model.origin.initial_ancestry

theorem period_literal_source (model : Solve.Algorithm.Model source) :
    _root_.Parser.Provenance.TracesTo (inputs model).outputTable
      ((inputs model).original (inputs model).periodLiteral)
      (model.origin.dae.flat.context.site .model) := by
  apply Inputs.original_traces
  rw [inputs_lowered]
  exact model.origin.period_ancestry

def Inputs.Generated (input : Inputs table) (role : Role)
    (refs : List (Ref input.outputTable)) : Prop :=
  ∀ ref ∈ refs, input.outputTable.get ref = input.expected role

def Inputs.FieldCorrect (input : Inputs table) (storage : Role)
    (origins : Expr.Origins input.outputTable (stateField name)) : Prop :=
  match origins with
  | .field operation member (.id parameter) =>
      input.Generated storage [operation, member] ∧ input.Generated .parameter [parameter]

def Inputs.DeclarationCorrect (input : Inputs table) (register conversion : Role)
    (sourceLiteral : Ref table)
    (origins : Stmt.Origins input.outputTable (.declare "double" name (.cast "double" (.nat value)))) : Prop :=
  match origins with
  | .declare operation typeName declaration (.cast castOperation castType (.nat literal)) =>
      input.Generated register [operation, declaration] ∧
      input.Generated conversion [typeName, castOperation, castType] ∧
      literal.index.val = sourceLiteral.index.val

def Inputs.AssignmentCorrect (input : Inputs table) (assignment storage : Role)
    (sourceValue : Ref table)
    (origins : Stmt.Origins input.outputTable (.assign (stateField fieldName) (.id valueName))) : Prop :=
  match origins with
  | .assign operation target (.id value) =>
      input.Generated assignment [operation] ∧ input.FieldCorrect storage target ∧
      value.index.val = sourceValue.index.val

def Inputs.ClearCorrect (input : Inputs table)
    (origins : Stmt.Origins input.outputTable (.assign (stateField CHeader.statusName) (.nat 0))) : Prop :=
  match origins with
  | .assign operation target (.nat zero) =>
      input.Generated .statusClear [operation, zero] ∧ input.FieldCorrect .statusStorage target

def Inputs.ReturnCorrect (input : Inputs table)
    (origins : Stmt.Origins input.outputTable (.ret (some (stateField CHeader.statusName)))) : Prop :=
  match origins with
  | .retValue operation value =>
      input.Generated .statusReturn [operation] ∧ input.FieldCorrect .statusStorage value

def Inputs.TraceCorrect (input : Inputs table)
    (origins : Function.Origins input.outputTable unitModule.startup) : Prop :=
  match origins.signature.parameters, origins.body with
  | .cons parameter .nil,
    .cons clear (.cons stateDeclaration (.cons stateAssignment (.cons periodDeclaration
      (.cons periodAssignment (.cons returned .nil))))) =>
      input.Generated .function [origins.definition, origins.signature.declaration,
        origins.signature.resultType, origins.signature.name] ∧
      input.Generated .parameter [parameter.declaration, parameter.typeName, parameter.name] ∧
      input.ClearCorrect clear ∧
      input.DeclarationCorrect .stateRegister .stateConversion input.stateLiteral stateDeclaration ∧
      input.AssignmentCorrect .stateStore .stateStorage input.stateValue stateAssignment ∧
      input.DeclarationCorrect .periodRegister .periodConversion input.periodLiteral periodDeclaration ∧
      input.AssignmentCorrect .periodStore .periodStorage input.periodValue periodAssignment ∧
      input.ReturnCorrect returned

set_option backward.isDefEq.respectTransparency false in
theorem Inputs.trace_correct (input : Inputs table) : input.TraceCorrect input.trace := by
  dsimp only [TraceCorrect, trace, unitModule, function, stateField, CHeader.statusName,
    List.append, ClearCorrect, FieldCorrect, DeclarationCorrect, AssignmentCorrect, ReturnCorrect, field]
  simp [Generated, role_correct, original,
    _root_.Parser.Provenance.Table.Extension.ref, _root_.Parser.Provenance.Table.mapRef]

/-- Exactly the attached generation roles and literal/result uses are allowed.
This predicate concerns references; it is not an AST-occurrence bijection. -/
def Inputs.Allowed (input : Inputs table) (ref : Ref input.outputTable) : Prop :=
  (∃ role, ref = input.role role) ∨
    ref = input.original input.stateLiteral ∨ ref = input.original input.stateValue ∨
    ref = input.original input.periodLiteral ∨ ref = input.original input.periodValue

theorem Inputs.role_allowed (input : Inputs table) (role : Role) : input.Allowed (input.role role) :=
  .inl ⟨role, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem Inputs.trace_every (input : Inputs table) : input.trace.Every input.Allowed := by
  simp only [trace, unitModule, function, stateField, CHeader.statusName, List.append,
    Function.Origins.Every, Signature.Origins.Every,
    Parameter.Origins.EveryList, Parameter.Origins.Every, Stmt.Origins.EveryList,
    Stmt.Origins.Every, field, Expr.Origins.Every]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact input.role_allowed _
    | simp [Allowed]

end Rumoca.EFMI.Production.StartupOrigins

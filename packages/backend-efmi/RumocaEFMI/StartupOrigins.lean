import RumocaEFMI.ProductionCode
import RumocaC.AlgorithmRules
import RumocaC.FunctionOrigins
import Parser.ProvenanceExtension

/-! Origins of the actual unit Startup function. Input references are taken
from prepared Solve operations and operands. No DAE inspection or new solver
selection occurs here. The adapter appends one bounded batch of rule nodes. -/
namespace Rumoca.EFMI.Production.StartupOrigins
open _root_.Parser.Provenance (Ref Node)
open Rumoca.CTree

inductive Rule where
  | upstream (rule : Provenance.Rule)
  | instruction (rule : CAlgorithm.Rule)
  | function
  | instanceParameter
  | statusStorage
  | statusClear
  | statusReturn
  deriving Repr, DecidableEq

inductive Role where
  | function | parameter | statusStorage | statusClear | statusReturn
  | stateRegister | stateConversion | stateStore | stateStorage
  | periodRegister | periodConversion | periodStore | periodStorage
  deriving Repr, DecidableEq

def Role.index : Role → Fin 13
  | .function => 0 | .parameter => 1 | .statusStorage => 2
  | .statusClear => 3 | .statusReturn => 4
  | .stateRegister => 5 | .stateConversion => 6 | .stateStore => 7 | .stateStorage => 8
  | .periodRegister => 9 | .periodConversion => 10 | .periodStore => 11 | .periodStorage => 12

def roles : Array Role := #[.function, .parameter, .statusStorage, .statusClear,
  .statusReturn, .stateRegister, .stateConversion, .stateStore, .stateStorage,
  .periodRegister, .periodConversion, .periodStore, .periodStorage]

theorem roles_index (role : Role) : roles[role.index.val]'(by cases role <;> decide) = role := by
  cases role <;> rfl

structure Inputs (table : _root_.Parser.Provenance.Table Site Provenance.Rule) where
  method : Ref table
  stateLiteral : Ref table
  stateAssignment : Ref table
  stateTarget : Ref table
  stateValue : Ref table
  periodLiteral : Ref table
  periodAssignment : Ref table
  periodTarget : Ref table
  periodValue : Ref table

/-- The equality changes only the index of the already prepared trace. -/
def inputs (model : Solve.Algorithm.Model source) : Inputs model.origin.origins.table :=
  let trace := model.block_is_unit ▸ model.origins
  match trace.startup, trace.period with
  | .fill initial (.ret assignment value), .fill period (.ret periodAssignment periodValue) =>
      ⟨trace.startupMethod, initial, assignment, trace.startupTarget, value,
        period, periodAssignment, trace.periodTarget, periodValue⟩

variable {table : _root_.Parser.Provenance.Table Site Provenance.Rule}

/-- Requirements use the actual Solve role references, not batch offsets. -/
def Inputs.expected (input : Inputs table) : Role → Node Site Rule
  | .function => .generated .function input.method.index.val #[]
  | .parameter => .generated .instanceParameter input.method.index.val #[]
  | .statusStorage => .generated .statusStorage input.method.index.val #[]
  | .statusClear => .generated .statusClear input.method.index.val #[]
  | .statusReturn => .generated .statusReturn input.method.index.val #[]
  | .stateRegister => .generated (.instruction .registerDeclaration) input.stateLiteral.index.val #[]
  | .stateConversion => .generated (.instruction .literalConversion) input.stateLiteral.index.val #[]
  | .stateStore => .generated (.instruction .assignment) input.stateAssignment.index.val
      #[input.stateTarget.index.val, input.stateValue.index.val]
  | .stateStorage => .generated (.instruction .storageAccess) input.stateTarget.index.val #[]
  | .periodRegister => .generated (.instruction .registerDeclaration) input.periodLiteral.index.val #[]
  | .periodConversion => .generated (.instruction .literalConversion) input.periodLiteral.index.val #[]
  | .periodStore => .generated (.instruction .assignment) input.periodAssignment.index.val
      #[input.periodTarget.index.val, input.periodValue.index.val]
  | .periodStorage => .generated (.instruction .storageAccess) input.periodTarget.index.val #[]

theorem Inputs.expected_prior (input : Inputs table) (role : Role) (parent : Nat)
    (member : parent ∈ (input.expected role).parents) : parent < table.nodes.size := by
  have h0 := input.method.index.isLt
  have h1 := input.stateLiteral.index.isLt
  have h2 := input.stateAssignment.index.isLt
  have h3 := input.stateTarget.index.isLt
  have h4 := input.stateValue.index.isLt
  have h5 := input.periodLiteral.index.isLt
  have h6 := input.periodAssignment.index.isLt
  have h7 := input.periodTarget.index.isLt
  have h8 := input.periodValue.index.isLt
  cases role <;> simp [expected, Node.parents] at member <;> omega

def Inputs.batch (input : Inputs table) : Array (Node Site Rule) := roles.map input.expected

theorem Inputs.batch_prior (input : Inputs table) (index : Nat)
    (bound : index < input.batch.size) (parent : Nat)
    (member : parent ∈ input.batch[index].parents) :
    parent < (table.mapRule Rule.upstream).nodes.size + index := by
  simp only [batch, Array.getElem_map] at member
  have h := input.expected_prior (roles[index]'(by simpa only [batch, Array.size_map] using bound)) parent member
  simpa only [_root_.Parser.Provenance.Table.mapRule, Array.size_map] using
    Nat.lt_add_right index h

def Inputs.outputTable (input : Inputs table) : _root_.Parser.Provenance.Table Site Rule :=
  (table.mapRule Rule.upstream).append input.batch input.batch_prior

def Inputs.extension (input : Inputs table) :
    (table.mapRule Rule.upstream).Extension input.outputTable :=
  (table.mapRule Rule.upstream).append_extension input.batch input.batch_prior

def Inputs.original (input : Inputs table) (ref : Ref table) : Ref input.outputTable :=
  input.extension.ref (table.mapRef Rule.upstream ref)

def Inputs.role (input : Inputs table) (role : Role) : Ref input.outputTable :=
  (table.mapRule Rule.upstream).appendedRef input.batch input.batch_prior
    ⟨role.index.val, by simpa only [batch, Array.size_map] using role.index.isLt⟩

theorem Inputs.role_correct (input : Inputs table) (role : Role) :
    input.outputTable.get (input.role role) = input.expected role := by
  have found := (table.mapRule Rule.upstream).appended_lookup input.batch input.batch_prior
    ⟨role.index.val, by simpa only [batch, Array.size_map] using role.index.isLt⟩
  apply found.trans
  change input.batch[role.index.val]'(by simpa only [batch, Array.size_map] using role.index.isLt) = _
  simp only [batch, Array.getElem_map, roles_index]

theorem Inputs.original_correct (input : Inputs table) (ref : Ref table) :
    input.outputTable.get (input.original ref) = (table.get ref).mapRule Rule.upstream :=
  (input.extension.lookup _).trans (table.get_mapRef _ ref)

def Inputs.field (input : Inputs table) (storage : Role) (name : String) :
    Expr.Origins input.outputTable (stateField name) :=
  .field (input.role storage) (input.role storage) (.id (input.role .parameter))

def Inputs.trace (input : Inputs table) : Function.Origins input.outputTable unitModule.startup where
  definition := input.role .function
  signature := ⟨input.role .function, input.role .function, input.role .function,
    .cons ⟨input.role .parameter, input.role .parameter, input.role .parameter⟩ .nil⟩
  body := .cons (.assign (input.role .statusClear) (input.field .statusStorage CHeader.statusName)
      (.nat (input.role .statusClear)))
    (.cons (.declare (input.role .stateRegister) (input.role .stateConversion)
      (input.role .stateRegister) (.cast (input.role .stateConversion)
        (input.role .stateConversion) (.nat (input.original input.stateLiteral))))
    (.cons (.assign (input.role .stateStore) (input.field .stateStorage "x")
      (.id (input.original input.stateValue)))
    (.cons (.declare (input.role .periodRegister) (input.role .periodConversion)
      (input.role .periodRegister) (.cast (input.role .periodConversion)
        (input.role .periodConversion) (.nat (input.original input.periodLiteral))))
    (.cons (.assign (input.role .periodStore) (input.field .periodStorage "samplePeriod")
      (.id (input.original input.periodValue)))
    (.cons (.retValue (input.role .statusReturn) (input.field .statusStorage CHeader.statusName)) .nil)))))

end Rumoca.EFMI.Production.StartupOrigins

import RumocaCore.GALEC.Elaboration.Capabilities.Generic
import RumocaCore.GALEC.Elaboration.Methods.Headers
import RumocaCore.GALEC.Elaboration.Layout.Execution
import RumocaCore.GALEC.Elaboration.Signals.Soundness

/-! Generic named-method preparation from original AST and declarations.
The role policy is a frontend preparation parameter, never a target callback.
No parser, method ordinal, body recognizer, or backend inference is used. The
selected method's signal interface must equal its §1.5 out-reachable set
(eFMI §3.2.5 §1.3); the body is lowered only after that check. -/
namespace Rumoca.GALEC.Elaboration.Methods.Preparation
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor
open Capabilities.Generic

abbrev Result := Σ fields : List Layout.Field,
  Statement (Layout.inputShapes fields) (Layout.outputShapes fields) []

def fromBlock (name : _root_.Parser.Token) (role : Declarations.Real.Descriptor → Layout.Role)
    (ceiling : Nat) (block : AST.Block) : Option Result :=
  (Methods.Headers.select name block.methods).bind fun method =>
    (Reach.exposed method).bind fun _ =>
    (Declarations.Real.readAll ceiling block.declarations).bind fun declarations =>
      (Layout.body (fields role declarations) ceiling method.body).map fun statement =>
        ⟨fields role declarations, statement⟩

inductive Prepares (name : _root_.Parser.Token) (role : Declarations.Real.Descriptor → Layout.Role)
    (ceiling : Nat) (block : AST.Block) : Result → Prop where
  | body (selected : Methods.Headers.Selects name block.methods method)
      (exposes : Reach.Exposes method exposed)
      (declared : Declarations.Real.DeclaresAll ceiling block.declarations declarations)
      (typed : Bodies.BodyElaborates (Layout.bindings (fields role declarations))
        (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling .nil method.body statement) :
      Prepares name role ceiling block ⟨fields role declarations, statement⟩

/-- A selected method whose signal interface is not its exposed set (§1.3),
or whose checks violate §1.4, is rejected before its body is lowered. -/
theorem unexposed_rejected (selected : Methods.Headers.select name block.methods = some method)
    (unexposed : Reach.exposed method = none) :
    fromBlock name role ceiling block = none := by
  simp [fromBlock, selected, unexposed]

theorem declared_fields (role : Declarations.Real.Descriptor → Layout.Role)
    (declared : Declarations.Real.DeclaresAll ceiling sources declarations) :
    Declarations.Real.DeclaresAll ceiling sources
      ((fields role declarations).map Layout.Field.declaration) := by
  simpa only [fields_declarations] using declared

theorem fromBlock_iff (name : _root_.Parser.Token) (role : Declarations.Real.Descriptor → Layout.Role)
    (ceiling : Nat) (block : AST.Block) (result : Result) :
    fromBlock name role ceiling block = some result ↔ Prepares name role ceiling block result := by
  constructor
  · intro compiled
    obtain ⟨method, selected, remaining⟩ := Option.bind_eq_some_iff.mp compiled
    obtain ⟨exposed, checked, remaining⟩ := Option.bind_eq_some_iff.mp remaining
    obtain ⟨declarations, read, remaining⟩ := Option.bind_eq_some_iff.mp remaining
    obtain ⟨statement, lowered, same⟩ := Option.map_eq_some_iff.mp remaining
    cases same
    have declared := (Declarations.Real.readAll_iff _ _ _).mp read
    exact .body ((Methods.Headers.select_iff _ _ _).mp selected) ((Reach.exposed_iff _ _).mp checked)
      declared ((Layout.body_iff _ (declared_fields role declared) _ _).mp lowered)
  · intro prepared
    cases prepared with
    | body selected exposes declared typed =>
      simp only [fromBlock, (Methods.Headers.select_iff _ _ _).mpr selected, Option.bind_some,
        (Reach.exposed_iff _ _).mpr exposes,
        (Declarations.Real.readAll_iff _ _ _).mpr declared,
        (Layout.body_iff _ (declared_fields role declared) _ _).mpr typed, Option.map_some]

theorem prepared_declarations (prepared : Prepares name role ceiling block result) :
    Declarations.Real.DeclaresAll ceiling block.declarations
      (result.1.map Layout.Field.declaration) := by
  cases prepared with
  | body _ _ declared _ => exact declared_fields role declared

theorem prepared_method (prepared : Prepares name role ceiling block result) :
    ∃ method, Methods.Headers.Selects name block.methods method ∧
      Bodies.BodyElaborates (Layout.bindings result.1)
        (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling .nil method.body result.2 := by
  cases prepared with
  | body selected _ _ typed => exact ⟨_, selected, typed⟩

/-- One original selected method is fixed before all runtime values, stores
and arithmetic interpretations. No caller-supplied shape oracle remains. -/
theorem prepared_execution (prepared : Prepares name role ceiling block result) :
    ∃ method, Methods.Headers.Selects name block.methods method ∧
      ∀ {α : Type} (step : BinaryOp → α → α → α → Prop) (zero one : α)
        (input : Env α (Layout.inputShapes result.1)) (env : IteratorEnv [])
        (before after : Env α (Layout.outputShapes result.1)),
        Bodies.Source.statements (Layout.bindings result.1)
          (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling step zero one
          @input .nil @env method.body @before @after ↔
          result.2.Executes step zero one @input @env @before @after := by
  cases prepared with
  | body selected _ declared typed =>
    refine ⟨_, selected, ?_⟩
    intro α step zero one input env before after
    exact Bodies.statements_correct _ _ _
      (Layout.bindingShape_iff_source _ (declared_fields role declared)) ceiling .nil _ _ typed
      step zero one @input @env @before @after

/-- The selected method exposes exactly the out-reachable set of its body. -/
theorem prepared_exposes (prepared : Prepares name role ceiling block result) :
    ∃ method exposed, Methods.Headers.Selects name block.methods method ∧
      Reach.Exposes method exposed := by
  cases prepared with
  | body selected exposes _ _ => exact ⟨_, _, selected, exposes⟩

/-- Execution with error signals of the one selected original method is
execution of its prepared statement, for every arithmetic and finiteness
interpretation. -/
theorem prepared_runs (prepared : Prepares name role ceiling block result) :
    ∃ method, Methods.Headers.Selects name block.methods method ∧
      ∀ {α : Type} (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
        (input : Env α (Layout.inputShapes result.1)) (env : IteratorEnv [])
        (before after : Signaled α (Layout.outputShapes result.1)),
        Bodies.Source.runs (Layout.bindings result.1)
          (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling step finite zero one
          @input .nil @env method.body before after ↔
          result.2.Runs step finite zero one @input @env before after := by
  cases prepared with
  | body selected _ declared typed =>
    refine ⟨_, selected, ?_⟩
    intro α step finite zero one input env before after
    exact Bodies.statements_runs _ _ _
      (Layout.bindingShape_iff_source _ (declared_fields role declared)) ceiling .nil _ _ typed
      step finite zero one @input @env before after

/-- The admission claim: every execution of the prepared method that starts
with no signal set ends within the method's exposed set (§1.3, §1.5). -/
theorem prepared_signals (prepared : Prepares name role ceiling block result) :
    ∃ method exposed, Methods.Headers.Selects name block.methods method ∧
      Reach.Exposes method exposed ∧
      ∀ {α : Type} (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
        (input : Env α (Layout.inputShapes result.1)) (env : IteratorEnv [])
        (before : Env α (Layout.outputShapes result.1))
        (after : Signaled α (Layout.outputShapes result.1)),
        result.2.Runs step finite zero one @input @env ⟨@before, SignalSet.empty⟩ after →
        SignalSet.Subset after.2 exposed := by
  cases prepared with
  | body selected exposes _ typed =>
    exact ⟨_, _, selected, exposes, fun step finite zero one input env before after ran =>
      Reach.exposes_sound typed exposes step finite zero one @input @env @before after ran⟩

theorem prepared_policy {Allowed : Declarations.Real.Descriptor → Prop}
    (correct : ∀ declaration, role declaration = .writable ↔ Allowed declaration)
    (prepared : Prepares name role ceiling block result) :
    ∃ method declarations, Methods.Headers.Selects name block.methods method ∧
      Declarations.Real.DeclaresAll ceiling block.declarations declarations ∧
      BodyWrites Allowed declarations method.body := by
  cases prepared with
  | body selected _ declared typed => exact ⟨_, _, selected, declared, body_writes correct typed⟩

end Rumoca.GALEC.Elaboration.Methods.Preparation

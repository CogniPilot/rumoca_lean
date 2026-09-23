import RumocaCore.GALEC.Elaboration.Capabilities.Generic
import RumocaCore.GALEC.Elaboration.Methods.Headers
import RumocaCore.GALEC.Elaboration.Layout.Execution

/-! Generic named-method preparation from original AST and declarations.
The role policy is a frontend preparation parameter, never a target callback.
No parser, method ordinal, body recognizer, or backend inference is used. -/
namespace Rumoca.GALEC.Elaboration.Methods.Preparation
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor
open Capabilities.Generic

abbrev Result := Σ fields : List Layout.Field,
  Statement (Layout.inputShapes fields) (Layout.outputShapes fields) []

def fromBlock (name : _root_.Parser.Token) (role : Declarations.Real.Descriptor → Layout.Role)
    (ceiling : Nat) (block : AST.Block) : Option Result :=
  (Methods.Headers.select name block.methods).bind fun method =>
    (Declarations.Real.readAll ceiling block.declarations).bind fun declarations =>
      (Layout.body (fields role declarations) ceiling method.body).map fun statement =>
        ⟨fields role declarations, statement⟩

inductive Prepares (name : _root_.Parser.Token) (role : Declarations.Real.Descriptor → Layout.Role)
    (ceiling : Nat) (block : AST.Block) : Result → Prop where
  | body (selected : Methods.Headers.Selects name block.methods method)
      (declared : Declarations.Real.DeclaresAll ceiling block.declarations declarations)
      (typed : Bodies.BodyElaborates (Layout.bindings (fields role declarations))
        (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling .nil method.body statement) :
      Prepares name role ceiling block ⟨fields role declarations, statement⟩

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
    obtain ⟨declarations, read, remaining⟩ := Option.bind_eq_some_iff.mp remaining
    obtain ⟨statement, lowered, same⟩ := Option.map_eq_some_iff.mp remaining
    cases same
    have declared := (Declarations.Real.readAll_iff _ _ _).mp read
    exact .body ((Methods.Headers.select_iff _ _ _).mp selected) declared
      ((Layout.body_iff _ (declared_fields role declared) _ _).mp lowered)
  · intro prepared
    cases prepared with
    | body selected declared typed =>
      simp only [fromBlock, (Methods.Headers.select_iff _ _ _).mpr selected, Option.bind_some,
        (Declarations.Real.readAll_iff _ _ _).mpr declared,
        (Layout.body_iff _ (declared_fields role declared) _ _).mpr typed, Option.map_some]

theorem prepared_declarations (prepared : Prepares name role ceiling block result) :
    Declarations.Real.DeclaresAll ceiling block.declarations
      (result.1.map Layout.Field.declaration) := by
  cases prepared with
  | body _ declared _ => exact declared_fields role declared

theorem prepared_method (prepared : Prepares name role ceiling block result) :
    ∃ method, Methods.Headers.Selects name block.methods method ∧
      Bodies.BodyElaborates (Layout.bindings result.1)
        (Declarations.ShapeLookup.HasShape ceiling block.declarations) ceiling .nil method.body result.2 := by
  cases prepared with
  | body selected _ typed => exact ⟨_, selected, typed⟩

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
  | body selected declared typed =>
    refine ⟨_, selected, ?_⟩
    intro α step zero one input env before after
    exact Bodies.statements_correct _ _ _
      (Layout.bindingShape_iff_source _ (declared_fields role declared)) ceiling .nil _ _ typed
      step zero one @input @env @before @after

theorem prepared_policy {Allowed : Declarations.Real.Descriptor → Prop}
    (correct : ∀ declaration, role declaration = .writable ↔ Allowed declaration)
    (prepared : Prepares name role ceiling block result) :
    ∃ method declarations, Methods.Headers.Selects name block.methods method ∧
      Declarations.Real.DeclaresAll ceiling block.declarations declarations ∧
      BodyWrites Allowed declarations method.body := by
  cases prepared with
  | body selected declared typed => exact ⟨_, _, selected, declared, body_writes correct typed⟩

end Rumoca.GALEC.Elaboration.Methods.Preparation

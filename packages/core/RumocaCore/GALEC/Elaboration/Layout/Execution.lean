import RumocaCore.GALEC.Elaboration.Layout.Shapes
import RumocaCore.GALEC.Elaboration.Bodies.Correctness

/-! Compose actual declaration-derived storage with actual recursive source
bodies. Method role legality remains a separate obligation; the supplied roles
are never guessed from declaration directions. No backend is involved. -/
namespace Rumoca.GALEC.Elaboration.Layout
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor

/-- Lower a closed method body using the one table constructed from its fields.
Static size queries and assignment/read resolution share that exact table. -/
def body (fields : List Field) (ceiling : Nat) (sources : List AST.Statement) :
    Option (Statement (inputShapes fields) (outputShapes fields) []) :=
  Bodies.statements (bindings fields) (Static.Dimensions.bindingShape (bindings fields))
    ceiling .nil sources

theorem body_iff (fields : List Field)
    (declared : Declarations.Real.DeclaresAll ceiling declarations (fields.map Field.declaration))
    (sources : List AST.Statement) (stmt : Statement (inputShapes fields) (outputShapes fields) []) :
    body fields ceiling sources = some stmt ↔
      Bodies.BodyElaborates (bindings fields)
        (Declarations.ShapeLookup.HasShape ceiling declarations) ceiling .nil sources stmt :=
  Bodies.statements_iff _ _ _ (bindingShape_iff_source fields declared)
    ceiling .nil sources stmt

/-- No unconstrained shape-provider premise remains. The source declaration
judgment supplies it for the same non-enumerating typed storage construction. -/
theorem source_to_body (fields : List Field)
    (declared : Declarations.Real.DeclaresAll ceiling declarations (fields.map Field.declaration))
    (sources : List AST.Statement) (stmt : Statement (inputShapes fields) (outputShapes fields) [])
    (lowered : body fields ceiling sources = some stmt)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (inputShapes fields)) (env : IteratorEnv [])
    (before after : Env α (outputShapes fields)) :
    Bodies.Source.statements (bindings fields)
        (Declarations.ShapeLookup.HasShape ceiling declarations) ceiling step zero one
        @input .nil @env sources @before @after ↔
      stmt.Executes step zero one @input @env @before @after :=
  Bodies.source_to_body _ _ _ (bindingShape_iff_source fields declared)
    ceiling .nil sources stmt lowered step zero one @input @env @before @after

end Rumoca.GALEC.Elaboration.Layout

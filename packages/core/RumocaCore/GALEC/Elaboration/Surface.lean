import RumocaCore.GALEC.Elaboration.Bodies.Correctness
import RumocaCore.GALEC.VectorBodies
import RumocaCore.GALEC.MatrixBodies

/-! Surface constructors and reusable typing witnesses for the existing
prepared rank-one square/AD repair. These are not parser recognizers or source
semantics; the generic AST lowerer and independent judgments stay authoritative.
No source admission or actual-text claim follows from these AST builders. -/
namespace Rumoca.GALEC.Elaboration.Surface
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor Coefficients VectorBodies

def stateReference (name : String) (indices : List AST.Expr) : AST.Reference :=
  ⟨⟨.literal "self", []⟩, [⟨.ident name, indices⟩]⟩

def iterator (name : String) : AST.Expr :=
  .reference (AST.Reference.unindexed (.ident name) [])

def natural (value : Nat) : AST.Expr := .literal (.literal (toString value))

def dimension (name : String) (axis : Nat) : AST.Expr :=
  .size (stateReference name []) (natural axis)

def unitLoop (binder : String) (stop : AST.Expr) (body : List AST.Statement) : AST.Statement :=
  .forLoop (.ident binder) (natural 1) (some (natural 1)) stop body

theorem state_spelling (name : String) (indices : List AST.Expr) :
    Path.Surface (stateReference name indices) [name] indices := .self (.leaf _ _)

theorem natural_evaluates (bounded : value ≤ ceiling) :
    Static.Bounded.Evaluates HasShape ceiling (natural value) value :=
  .literal (_root_.Parser.DecimalNat.render_denotes value) bounded

theorem dimension_header (names : IteratorNames bounds)
    (fresh : Loops.Binder.Fresh names binder)
    (shapeKnown : HasShape [name] shape)
    (selected : shape.dimensions[position]? = some extent)
    (positive : 0 < extent) (within : extent ≤ ceiling)
    (axisBound : position + 1 ≤ ceiling) :
    Loops.Header.Denotes names HasShape ceiling (.ident binder)
      (natural 1) (some (natural 1)) (dimension name (position + 1)) binder extent := by
  have oneBound : 1 ≤ ceiling := by omega
  exact .header (.ident fresh) (.unit (natural_evaluates oneBound) (natural_evaluates oneBound)
    (.size (natural_evaluates axisBound) (.dimension (state_spelling name []) shapeKnown selected) within)
    positive)

theorem index_typed (names : IteratorNames bounds)
    (resolved : IteratorNames.Resolves names name ⟨extent, ref⟩) :
    IteratorIndices.Elaborates names extent (iterator name) (.iterator ref) :=
  .iterator (.reference name) resolved

theorem reference_typed (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (resolved : BindingTable.Resolves table [name] ⟨shape, access⟩)
    (indices : SubscriptLowering.Elaborates (IteratorIndices.Elaborates names)
      shape.dimensions expressions terms) :
    ReadLowering.Elaborates table names (stateReference name expressions) ⟨shape, access, terms⟩ :=
  .indexed (state_spelling name expressions) resolved indices

theorem vector_indices (name : String) (names : IteratorNames bounds) :
    SubscriptLowering.Elaborates
      (IteratorIndices.Elaborates (.cons (bound := extent) name names))
      [extent] [iterator name] vectorSubscripts :=
  .cons (index_typed _ .here) .nil

theorem diagonal_indices (name : String) (names : IteratorNames bounds) :
    SubscriptLowering.Elaborates
      (IteratorIndices.Elaborates (.cons (bound := extent) name names))
      [extent, extent] [iterator name, iterator name] diagonalSubscripts :=
  .cons (index_typed _ .here) (.cons (index_typed _ .here) .nil)

theorem matrix_indices (row col : String) (different : row ≠ col) (names : IteratorNames bounds) :
    SubscriptLowering.Elaborates
      (IteratorIndices.Elaborates (.cons (bound := cols) col (.cons (bound := rows) row names)))
      [rows, cols] [iterator row, iterator col] MatrixBodies.matrixSubscripts :=
  .cons (index_typed _ (.there different .here)) (.cons (index_typed _ .here) .nil)

end Rumoca.GALEC.Elaboration.Surface

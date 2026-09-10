import RumocaCore.Solve.Algorithm
import RumocaC.Tree

/-! Thin emission from prepared tensor Solve instructions. Unsupported storage
ranks are rejected without enumerating coordinates. Names and the final store
location are supplied by the target wrapper; no solving or DAE lowering occurs. -/
namespace Rumoca.CAlgorithm
open Rumoca.Tensor Rumoca.Solve.Tensor Rumoca.CTree

abbrev Names (Γ : List Shape) := {shape : Shape} → Ref Γ shape → Expr

def pushName (name : String) (env : Names Γ) : Names (shape :: Γ)
  | _, .here => .id name
  | _, .there ref => env ref


def literal : Solve.Tensor.Literal → Expr
  | .zero => .cast "double" (.nat 0)
  | .one => .cast "double" (.nat 1)

def emitProgram (program : Solve.Algorithm.Program Γ result) (env : Names Γ)
    (target : Expr) (nextId : Nat) : Except String (Nat × List Stmt) :=
  match program with
  | .ret ref => .ok (nextId, [.assign target (env ref)])
  | @Solve.Algorithm.Program.fill shape _ _ value next => do
      if shape ≠ scalar then throw "Production C storage currently requires rank-zero tensors"
      let name := s!"v{nextId}"
      let (lastId, rest) ← emitProgram next (pushName name env) target (nextId + 1)
      return (lastId, .declare "double" name (literal value) :: rest)
  | @Solve.Algorithm.Program.add _ shape _ a b next => do
      if shape ≠ scalar then throw "Production C storage currently requires rank-zero tensors"
      let name := s!"v{nextId}"
      let (lastId, rest) ← emitProgram next (pushName name env) target (nextId + 1)
      return (lastId, .declare "double" name (.bin .add (env a) (env b)) :: rest)


end Rumoca.CAlgorithm

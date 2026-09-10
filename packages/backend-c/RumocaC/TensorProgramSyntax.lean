import RumocaC.TensorProgramCode
import RumocaC.Identifier
import RumocaC.TensorSyntax

/-! Independent C grammar for prepared straight-line tensor-call functions.
Operands are named buffer/count parameters and the two Solve fill literals.
Scope/type checks belong to this target profile, not source resolution. -/
namespace Rumoca.CTensor.Lowering.Syntax
open CTree Solve.Tensor

def identifier := CIdentifier.valid ["size_t"]

inductive ParamKind where
  | input | output | count
  deriving Repr, BEq, DecidableEq

def ParamKind.type : ParamKind → String
  | .input => "const double *"
  | .output => "double *"
  | .count => "size_t"

def ParamKind.tokens : ParamKind → List String
  | .input => ["const", "double", "*"]
  | .output => ["double", "*"]
  | .count => ["size_t"]

structure Parameter where
  kind : ParamKind
  name : String
  deriving Repr, BEq, DecidableEq

def Parameter.tree (p : Parameter) : CTree.Parameter := ⟨p.kind.type, p.name, false⟩
def Parameter.tokens (p : Parameter) : List String := p.kind.tokens ++ [p.name]

def hasType (params : List Parameter) (name : String) (kind : ParamKind) : Bool :=
  params.any (fun p => p.name == name && p.kind == kind)

def readable (params : List Parameter) (name : String) : Bool :=
  hasType params name .input || hasType params name .output

def binaryName : Tensor.BinaryOp → String
  | .add => "rumoca_tensor_add"
  | .mul => "rumoca_tensor_mul"

inductive Statement where
  | fill (value : Literal) (output count : String)
  | binary (op : Tensor.BinaryOp) (left right output count : String)
  | diagonal (coefficients output count cells : String)
  deriving Repr

def Statement.names : Statement → List String
  | .fill _ output count => [output, count]
  | .binary _ left right output count => [left, right, output, count]
  | .diagonal coefficients output count cells => [coefficients, output, count, cells]

def Statement.scoped (params : List Parameter) : Statement → Bool
  | .fill _ output count => hasType params output .output && hasType params count .count
  | .binary _ left right output count => readable params left && readable params right &&
      hasType params output .output && hasType params count .count
  | .diagonal coefficients output count cells => readable params coefficients &&
      hasType params output .output && hasType params count .count && hasType params cells .count

def Statement.valid (params : List Parameter) (s : Statement) : Bool :=
  s.names.all identifier && s.scoped params

def Statement.tokens : Statement → List String
  | .fill value output count =>
      ["rumoca_tensor_fill", "(", "(", "(", "double", ")",
        match value with | .zero => "0" | .one => "1",
        ")", ",", output, ",", count, ")", ";"]
  | .binary op left right output count =>
      [binaryName op, "(", left, ",", right, ",", output, ",", count, ")", ";"]
  | .diagonal coefficients output count cells =>
      ["rumoca_tensor_diagonal", "(", coefficients, ",", output, ",", count, ",", cells, ")", ";"]

def Statement.tree : Statement → Stmt
  | .fill value output count =>
      .eval (.call (.id "rumoca_tensor_fill")
        [.cast "double" (.nat (match value with | .zero => 0 | .one => 1)), .id output, .id count])
  | .binary op left right output count =>
      .eval (.call (.id (binaryName op)) [.id left, .id right, .id output, .id count])
  | .diagonal coefficients output count cells =>
      .eval (.call (.id "rumoca_tensor_diagonal") [.id coefficients, .id output, .id count, .id cells])

structure Function where
  name : String
  parameters : List Parameter
  statements : List Statement
  deriving Repr

def Function.valid (f : Function) : Bool :=
  identifier f.name && f.parameters.all (fun p => identifier p.name) &&
    decide (f.parameters.map Parameter.name).Nodup &&
    !["rumoca_tensor_add", "rumoca_tensor_mul", "rumoca_tensor_fill"].contains f.name &&
    f.parameters.all (fun p => !["rumoca_tensor_add", "rumoca_tensor_mul", "rumoca_tensor_fill"].contains p.name) &&
    f.statements.all (Statement.valid f.parameters)

def Function.tree (f : Function) : CTree.Function :=
  ⟨⟨"void", f.name, f.parameters.map Parameter.tree⟩, f.statements.map Statement.tree ++ [.ret none], false⟩

def parameterTokens (params : List Parameter) : List String :=
  if params.isEmpty then ["void"] else List.intercalate [","] (params.map Parameter.tokens)

def Function.tokens (f : Function) : List String :=
  ["void", f.name, "("] ++ parameterTokens f.parameters ++ [")", "{"] ++
    f.statements.flatMap Statement.tokens ++ ["return", ";", "}"]

def Denotes (source : String) (f : Function) : Prop :=
  f.valid = true ∧ _root_.Parser.Scanner.Lexes CTensor.Syntax.config source.toList
    (f.tokens.map _root_.Parser.Token.literal)

/-- Bind the independently specified function body to the actual emission.
The semantic contract separately identifies the emitted result buffer. -/
def Matches (f : Function) (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) : Prop :=
  f.tree.body = (emit p plan layout).code ++ [.ret none]

end Rumoca.CTensor.Lowering.Syntax

import GALECParser.AST
import GALECParser.Syntax

/-! Checked-profile adapters, not parser actions. These inspect the AST directly
and never call the old token decoders. They retain every unresolved name; the
existing Resolved predicates belong to the subsequent checked phase. -/
namespace Rumoca.GALEC.ProfileProjection
open _root_.Parser

def selfRef (name : String) : AST.Reference :=
  AST.Reference.unindexed (.literal "self") [.ident name]

def startup (state clock : String) : AST.Method :=
  ⟨.public, .literal "Startup",
    [.assign (selfRef state) (.literal (.literal "0.0")),
     .assign (selfRef clock) (.literal (.literal "1.0"))], .literal "Startup"⟩

def recalibrate : AST.Method :=
  ⟨.public, .literal "Recalibrate", [], .literal "Recalibrate"⟩

def scalarStep (target read : String) : AST.Method :=
  ⟨.public, .literal "DoStep",
    [.assign (selfRef target) (.parens
      (.binary (.literal "+") (.reference (selfRef read)) (.literal (.literal "1.0"))))],
    .literal "DoStep"⟩

def product (left right : String) : AST.Expr :=
  .binary (.literal ".*") (.reference (selfRef left)) (.reference (selfRef right))

def tensorStep (target left right jacTarget callee jacLeft jacRight wrt : String) : AST.Method :=
  ⟨.public, .literal "DoStep",
    [.assign (selfRef target) (product left right),
     .assign (selfRef jacTarget) (.call (.ident callee)
       [product jacLeft jacRight, .reference (selfRef wrt)])], .literal "DoStep"⟩

def ofScalar (b : Syntax.Block) : AST.Block :=
  ⟨.ident b.name,
    [⟨.public, .output, .variable, .literal "Real", [], .ident b.state⟩,
     ⟨.protected, .local, .constant, .literal "Real", [], .ident b.clock⟩],
    [startup b.initialState b.initialClock, recalibrate, scalarStep b.stepTarget b.stepRead],
    .ident b.endName⟩

def ofTensor (b : Syntax.TensorBlock) : AST.Block :=
  ⟨.ident b.name,
    [⟨.public, .input, .variable, .literal "Real", [.literal "2"], .ident b.input⟩,
     ⟨.public, .output, .variable, .literal "Real", [.literal "2"], .ident b.state⟩,
     ⟨.public, .output, .variable, .literal "Real", [.literal "2", .literal "2"], .ident b.jacobian⟩,
     ⟨.protected, .local, .constant, .literal "Real", [], .ident b.clock⟩],
    [startup b.initialState b.initialClock, recalibrate,
      tensorStep b.stepState b.derivLeft b.derivRight b.jacTarget b.jacFn b.jacLeft b.jacRight b.jacArg],
    .ident b.endName⟩

/-! Compositional profile checks. Each noinline boundary keeps host code generation
from fusing malformed-input alternatives into one enormous matcher. All checks
operate directly on AST fields, with no token reconstruction or reparsing. -/
namespace Factors

@[noinline] def identifier : Token → Option String
  | .ident name => some name
  | _ => none

@[noinline] def one : List α → Option α
  | [x] => some x
  | _ => none

@[noinline] def two : List α → Option (α × α)
  | [x, y] => some (x, y)
  | _ => none

@[noinline] def three : List α → Option (α × α × α)
  | [x, y, z] => some (x, y, z)
  | _ => none

@[noinline] def four : List α → Option (α × α × α × α)
  | [w, x, y, z] => some (w, x, y, z)
  | _ => none

@[noinline] def empty : List α → Option Unit
  | [] => some ()
  | _ => none

@[noinline] def selfName (ref : AST.Reference) : Option String := do
  if ref.base.name = .literal "self" then
    let _ ← empty ref.base.indices
    let field ← one ref.fields
    let _ ← empty field.indices
    identifier field.name
  else none

@[noinline] def reference : AST.Expr → Option String
  | .reference ref => selfName ref
  | _ => none

@[noinline] def literal (spelling : String) : AST.Expr → Option Unit
  | .literal token => if token = .literal spelling then some () else none
  | _ => none

@[noinline] def parens : AST.Expr → Option AST.Expr
  | .parens body => some body
  | _ => none

@[noinline] def binary (operator : String) : AST.Expr → Option (AST.Expr × AST.Expr)
  | .binary token left right =>
      if token = .literal operator then some (left, right) else none
  | _ => none

@[noinline] def call : AST.Expr → Option (Token × List AST.Expr)
  | .call callee args => some (callee, args)
  | _ => none

@[noinline] def plusOne (expr : AST.Expr) : Option String := do
  let body ← parens expr
  let (left, right) ← binary "+" body
  let _ ← literal "1.0" right
  reference left

@[noinline] def product (expr : AST.Expr) : Option (String × String) := do
  let (left, right) ← binary ".*" expr
  return (← reference left, ← reference right)

@[noinline] def derivativeCall (expr : AST.Expr) : Option (String × String × String × String) := do
  let (callee, args) ← call expr
  let name ← identifier callee
  let (arg, wrt) ← two args
  let (left, right) ← product arg
  let wrtName ← reference wrt
  return (name, left, right, wrtName)

@[noinline] def literalAssignment (spelling : String) : AST.Statement → Option String
  | .assign target value => do
      let name ← selfName target
      let _ ← literal spelling value
      return name
  | _ => none

@[noinline] def scalarAssignment : AST.Statement → Option (String × String)
  | .assign target value => do return (← selfName target, ← plusOne value)
  | _ => none

@[noinline] def productAssignment : AST.Statement → Option (String × String × String)
  | .assign target value => do
      let name ← selfName target
      let (left, right) ← product value
      return (name, left, right)
  | _ => none

@[noinline] def callAssignment : AST.Statement → Option (String × String × String × String × String)
  | .assign target value => do
      let name ← selfName target
      let (callee, left, right, wrt) ← derivativeCall value
      return (name, callee, left, right, wrt)
  | _ => none

@[noinline] def methodBody (name : String) (method : AST.Method) : Option (List AST.Statement) :=
  if method.visibility = .public ∧ method.name = .literal name ∧ method.endName = .literal name
    then some method.body else none

@[noinline] def startup (method : AST.Method) : Option (String × String) := do
  let body ← methodBody "Startup" method
  let (state, clock) ← two body
  return (← literalAssignment "0.0" state, ← literalAssignment "1.0" clock)

@[noinline] def recalibrate (method : AST.Method) : Option Unit := do
  empty (← methodBody "Recalibrate" method)

@[noinline] def scalarStep (method : AST.Method) : Option (String × String) := do
  scalarAssignment (← one (← methodBody "DoStep" method))

@[noinline] def tensorStep (method : AST.Method) :
    Option (String × String × String × String × String × String × String × String) := do
  let (rhs, jac) ← two (← methodBody "DoStep" method)
  let (target, left, right) ← productAssignment rhs
  let (jacTarget, callee, jacLeft, jacRight, wrt) ← callAssignment jac
  return (target, left, right, jacTarget, callee, jacLeft, jacRight, wrt)

@[noinline] def declaration (visibility : AST.Visibility) (direction : AST.Direction)
    (variability : AST.Variability) (extents : List Token) (decl : AST.Declaration) : Option String :=
  if decl.visibility = visibility ∧ decl.direction = direction ∧ decl.variability = variability ∧
      decl.typeName = .literal "Real" ∧ decl.extents = extents
    then identifier decl.name else none

@[noinline] def scalarDeclarations (decls : List AST.Declaration) : Option (String × String) := do
  let (state, clock) ← two decls
  return (← declaration .public .output .variable [] state,
    ← declaration .protected .local .constant [] clock)

@[noinline] def tensorDeclarations (decls : List AST.Declaration) :
    Option (String × String × String × String) := do
  let (input, state, jac, clock) ← four decls
  return (← declaration .public .input .variable [.literal "2"] input,
    ← declaration .public .output .variable [.literal "2"] state,
    ← declaration .public .output .variable [.literal "2", .literal "2"] jac,
    ← declaration .protected .local .constant [] clock)

@[noinline] def toScalar (ast : AST.Block) : Option Syntax.Block := do
  let name ← identifier ast.name
  let endName ← identifier ast.endName
  let (state, clock) ← scalarDeclarations ast.declarations
  let (init, reset, step) ← three ast.methods
  let (initialState, initialClock) ← startup init
  let _ ← recalibrate reset
  let (stepTarget, stepRead) ← scalarStep step
  return ⟨name, state, clock, initialState, initialClock, stepTarget, stepRead, endName⟩

@[noinline] def toTensor (ast : AST.Block) : Option Syntax.TensorBlock := do
  let name ← identifier ast.name
  let endName ← identifier ast.endName
  let (input, state, jacobian, clock) ← tensorDeclarations ast.declarations
  let (init, reset, step) ← three ast.methods
  let (initialState, initialClock) ← startup init
  let _ ← recalibrate reset
  let (stepState, derivLeft, derivRight, jacTarget, jacFn, jacLeft, jacRight, jacArg) ← tensorStep step
  return ⟨name, input, state, jacobian, clock, initialState, initialClock, stepState,
    derivLeft, derivRight, jacTarget, jacFn, jacLeft, jacRight, jacArg, endName⟩

/-! Exact helper contracts on arbitrary ASTs, stated against the embeddings. -/
theorem identifier_iff (token : Token) (name : String) :
    identifier token = some name ↔ token = .ident name := by
  cases token <;> simp [identifier]

theorem one_iff (xs : List α) (x : α) : one xs = some x ↔ xs = [x] := by
  unfold one
  split <;> simp_all

theorem two_iff (xs : List α) (x y : α) : two xs = some (x, y) ↔ xs = [x, y] := by
  unfold two
  split <;> simp_all

theorem three_iff (xs : List α) (x y z : α) :
    three xs = some (x, y, z) ↔ xs = [x, y, z] := by
  unfold three
  split <;> simp_all

theorem four_iff (xs : List α) (w x y z : α) :
    four xs = some (w, x, y, z) ↔ xs = [w, x, y, z] := by
  unfold four
  split <;> simp_all

theorem empty_iff (xs : List α) (u : Unit) : empty xs = some u ↔ xs = [] := by
  cases u
  cases xs <;> simp [empty]

theorem selfName_iff (ref : AST.Reference) (name : String) :
    selfName ref = some name ↔ ref = ProfileProjection.selfRef name := by
  rcases ref with ⟨⟨base, indices⟩, fields⟩
  simp [selfName, Option.bind_eq_some_iff, one_iff, empty_iff, identifier_iff,
    ProfileProjection.selfRef, AST.Reference.unindexed]
  constructor
  · rintro ⟨baseName, baseIndices, field, fieldsEq, fieldIndices, fieldName⟩
    cases field
    simp_all
  · rintro ⟨⟨baseName, baseIndices⟩, fieldsEq⟩
    exact ⟨baseName, baseIndices, _, fieldsEq, rfl, rfl⟩

theorem reference_iff (expr : AST.Expr) (name : String) :
    reference expr = some name ↔ expr = .reference (ProfileProjection.selfRef name) := by
  cases expr <;> simp [reference, selfName_iff]

theorem literal_iff (spelling : String) (expr : AST.Expr) (u : Unit) :
    literal spelling expr = some u ↔ expr = .literal (.literal spelling) := by
  cases u
  cases expr <;> simp [literal]

theorem parens_iff (expr body : AST.Expr) : parens expr = some body ↔ expr = .parens body := by
  cases expr <;> simp [parens]

theorem binary_iff (operator : String) (expr left right : AST.Expr) :
    binary operator expr = some (left, right) ↔ expr = .binary (.literal operator) left right := by
  cases expr <;> simp [binary]

theorem call_iff (expr : AST.Expr) (callee : Token) (args : List AST.Expr) :
    call expr = some (callee, args) ↔ expr = .call callee args := by
  cases expr <;> simp [call]

theorem plusOne_iff (expr : AST.Expr) (name : String) :
    plusOne expr = some name ↔ expr = .parens
      (.binary (.literal "+") (.reference (ProfileProjection.selfRef name))
        (.literal (.literal "1.0"))) := by
  simp [plusOne, Option.bind_eq_some_iff, Prod.exists,
    parens_iff, binary_iff, literal_iff, reference_iff]
  constructor
  · rintro ⟨body, he, left, right, hb, hr, hl⟩
    rw [he, hb, hr, hl]
  · rintro rfl
    exact ⟨_, rfl, _, _, rfl, rfl, rfl⟩

theorem product_iff (expr : AST.Expr) (left right : String) :
    product expr = some (left, right) ↔ expr = ProfileProjection.product left right := by
  simp [product, Option.bind_eq_some_iff, Prod.exists,
    binary_iff, reference_iff, ProfileProjection.product]

theorem derivativeCall_iff (expr : AST.Expr) (callee left right wrt : String) :
    derivativeCall expr = some (callee, left, right, wrt) ↔ expr =
      .call (.ident callee) [ProfileProjection.product left right,
        .reference (ProfileProjection.selfRef wrt)] := by
  simp [derivativeCall, Option.bind_eq_some_iff, Prod.exists,
    call_iff, identifier_iff, two_iff, product_iff, reference_iff, and_assoc, and_left_comm, and_comm]

theorem literalAssignment_iff (spelling : String) (stmt : AST.Statement) (name : String) :
    literalAssignment spelling stmt = some name ↔ stmt =
      .assign (ProfileProjection.selfRef name) (.literal (.literal spelling)) := by
  cases stmt <;> simp [literalAssignment, Option.bind_eq_some_iff, selfName_iff, literal_iff]

theorem scalarAssignment_iff (stmt : AST.Statement) (target read : String) :
    scalarAssignment stmt = some (target, read) ↔ stmt =
      .assign (ProfileProjection.selfRef target) (.parens
        (.binary (.literal "+") (.reference (ProfileProjection.selfRef read))
          (.literal (.literal "1.0")))) := by
  cases stmt <;> simp [scalarAssignment, Option.bind_eq_some_iff, selfName_iff, plusOne_iff]

theorem productAssignment_iff (stmt : AST.Statement) (target left right : String) :
    productAssignment stmt = some (target, left, right) ↔ stmt =
      .assign (ProfileProjection.selfRef target) (ProfileProjection.product left right) := by
  cases stmt <;> simp [productAssignment, Option.bind_eq_some_iff, Prod.exists, selfName_iff, product_iff,
    and_assoc, and_comm]

theorem callAssignment_iff (stmt : AST.Statement) (target callee left right wrt : String) :
    callAssignment stmt = some (target, callee, left, right, wrt) ↔ stmt =
      .assign (ProfileProjection.selfRef target)
        (.call (.ident callee) [ProfileProjection.product left right,
          .reference (ProfileProjection.selfRef wrt)]) := by
  cases stmt <;> simp [callAssignment, Option.bind_eq_some_iff, Prod.exists, selfName_iff, derivativeCall_iff,
    and_assoc, and_left_comm, and_comm]

theorem methodBody_iff (name : String) (method : AST.Method) (body : List AST.Statement) :
    methodBody name method = some body ↔ method = ⟨.public, .literal name, body, .literal name⟩ := by
  cases method
  simp [methodBody, and_left_comm, and_comm]

theorem startup_iff (method : AST.Method) (state clock : String) :
    startup method = some (state, clock) ↔ method = ProfileProjection.startup state clock := by
  simp [startup, Option.bind_eq_some_iff, Prod.exists, methodBody_iff,
    two_iff, literalAssignment_iff, ProfileProjection.startup]

theorem recalibrate_iff (method : AST.Method) (u : Unit) :
    recalibrate method = some u ↔ method = ProfileProjection.recalibrate := by
  simp [recalibrate, Option.bind_eq_some_iff, methodBody_iff, empty_iff, ProfileProjection.recalibrate]

theorem scalarStep_iff (method : AST.Method) (target read : String) :
    scalarStep method = some (target, read) ↔ method = ProfileProjection.scalarStep target read := by
  simp [scalarStep, Option.bind_eq_some_iff, methodBody_iff, one_iff,
    scalarAssignment_iff, ProfileProjection.scalarStep]

theorem tensorStep_iff (method : AST.Method) (target left right jacTarget callee jacLeft jacRight wrt : String) :
    tensorStep method = some (target, left, right, jacTarget, callee, jacLeft, jacRight, wrt) ↔
      method = ProfileProjection.tensorStep target left right jacTarget callee jacLeft jacRight wrt := by
  simp [tensorStep, Option.bind_eq_some_iff, Prod.exists, methodBody_iff, two_iff,
    productAssignment_iff, callAssignment_iff, ProfileProjection.tensorStep,
    and_assoc, and_left_comm, and_comm]

theorem declaration_iff (visibility : AST.Visibility) (direction : AST.Direction)
    (variability : AST.Variability) (extents : List Token) (decl : AST.Declaration) (name : String) :
    declaration visibility direction variability extents decl = some name ↔
      decl = ⟨visibility, direction, variability, .literal "Real", extents, .ident name⟩ := by
  cases decl
  simp [declaration, identifier_iff, and_assoc]

theorem scalarDeclarations_iff (decls : List AST.Declaration) (state clock : String) :
    scalarDeclarations decls = some (state, clock) ↔ decls =
      [⟨.public, .output, .variable, .literal "Real", [], .ident state⟩,
       ⟨.protected, .local, .constant, .literal "Real", [], .ident clock⟩] := by
  simp [scalarDeclarations, Option.bind_eq_some_iff, Prod.exists, two_iff, declaration_iff]

theorem tensorDeclarations_iff (decls : List AST.Declaration) (input state jac clock : String) :
    tensorDeclarations decls = some (input, state, jac, clock) ↔ decls =
      [⟨.public, .input, .variable, .literal "Real", [.literal "2"], .ident input⟩,
       ⟨.public, .output, .variable, .literal "Real", [.literal "2"], .ident state⟩,
       ⟨.public, .output, .variable, .literal "Real", [.literal "2", .literal "2"], .ident jac⟩,
       ⟨.protected, .local, .constant, .literal "Real", [], .ident clock⟩] := by
  simp [tensorDeclarations, Option.bind_eq_some_iff, Prod.exists, four_iff, declaration_iff,
    and_assoc, and_left_comm, and_comm]
  constructor
  · rintro ⟨a, b, c, d, h, hd, ha, hb, hc⟩
    simpa only [hd, ha, hb, hc] using h
  · intro h
    exact ⟨_, _, _, _, h, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Exact image on every AST, including malformed inputs. There is no
accepted-tree, well-formedness or source-resolution premise. -/
theorem scalar_projection_iff (ast : AST.Block) (b : Syntax.Block) :
    toScalar ast = some b ↔ ast = ProfileProjection.ofScalar b := by
  cases ast
  cases b
  simp [toScalar, Option.bind_eq_some_iff, Prod.exists, identifier_iff,
    scalarDeclarations_iff, three_iff, startup_iff, recalibrate_iff, scalarStep_iff,
    ProfileProjection.ofScalar, and_assoc, and_left_comm, and_comm]
  intro _ _
  constructor
  · rintro ⟨hd, init, step, hm, hs, hi⟩
    exact ⟨by simpa only [hs, hi] using hm, hd⟩
  · rintro ⟨hm, hd⟩
    exact ⟨hd, _, _, hm, rfl, rfl⟩

theorem tensor_projection_iff (ast : AST.Block) (b : Syntax.TensorBlock) :
    toTensor ast = some b ↔ ast = ProfileProjection.ofTensor b := by
  cases ast
  cases b
  simp [toTensor, Option.bind_eq_some_iff, Prod.exists, identifier_iff,
    tensorDeclarations_iff, three_iff, startup_iff, recalibrate_iff, tensorStep_iff,
    ProfileProjection.ofTensor, and_assoc, and_left_comm, and_comm]

theorem scalar_retraction (b : Syntax.Block) : toScalar (ProfileProjection.ofScalar b) = some b :=
  (scalar_projection_iff _ b).mpr rfl

theorem tensor_retraction (b : Syntax.TensorBlock) : toTensor (ProfileProjection.ofTensor b) = some b :=
  (tensor_projection_iff _ b).mpr rfl

theorem scalar_projection_exact (h : toScalar ast = some b) : ast = ProfileProjection.ofScalar b :=
  (scalar_projection_iff ast b).mp h

theorem tensor_projection_exact (h : toTensor ast = some b) : ast = ProfileProjection.ofTensor b :=
  (tensor_projection_iff ast b).mp h


end Factors

@[noinline] def toScalar (ast : AST.Block) : Option Syntax.Block := Factors.toScalar ast

@[noinline] def toTensor (ast : AST.Block) : Option Syntax.TensorBlock := Factors.toTensor ast

theorem scalar_retraction (b : Syntax.Block) : toScalar (ofScalar b) = some b :=
  Factors.scalar_retraction b

theorem tensor_retraction (b : Syntax.TensorBlock) : toTensor (ofTensor b) = some b :=
  Factors.tensor_retraction b

theorem scalar_projection_exact (h : toScalar ast = some b) : ast = ofScalar b :=
  Factors.scalar_projection_exact h

theorem tensor_projection_exact (h : toTensor ast = some b) : ast = ofTensor b :=
  Factors.tensor_projection_exact h

theorem scalar_projection_iff : toScalar ast = some b ↔ ast = ofScalar b :=
  Factors.scalar_projection_iff ast b

theorem tensor_projection_iff : toTensor ast = some b ↔ ast = ofTensor b :=
  Factors.tensor_projection_iff ast b

end Rumoca.GALEC.ProfileProjection

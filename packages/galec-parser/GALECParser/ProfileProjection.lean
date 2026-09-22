import GALECParser.AST
import GALECParser.Syntax

/-! Checked-profile adapters, not parser actions. These inspect the AST directly
and never call the old token decoders. They retain every unresolved name; the
existing Resolved predicates belong to the subsequent checked phase. -/
namespace Rumoca.GALEC.ProfileProjection
open _root_.Parser

def selfRef (name : String) : AST.Reference := ⟨.literal "self", [.ident name]⟩

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

def toScalar : AST.Block → Option Syntax.Block
  | ⟨.ident name,
      [⟨.public, .output, .variable, .literal "Real", [], .ident state⟩,
       ⟨.protected, .local, .constant, .literal "Real", [], .ident clock⟩],
      [⟨.public, .literal "Startup",
        [.assign ⟨.literal "self", [.ident initialState]⟩ (.literal (.literal "0.0")),
         .assign ⟨.literal "self", [.ident initialClock]⟩ (.literal (.literal "1.0"))], .literal "Startup"⟩,
       ⟨.public, .literal "Recalibrate", [], .literal "Recalibrate"⟩,
       ⟨.public, .literal "DoStep",
        [.assign ⟨.literal "self", [.ident stepTarget]⟩ (.parens
          (.binary (.literal "+") (.reference ⟨.literal "self", [.ident stepRead]⟩)
            (.literal (.literal "1.0"))))], .literal "DoStep"⟩], .ident endName⟩ =>
      some ⟨name, state, clock, initialState, initialClock, stepTarget, stepRead, endName⟩
  | _ => none

def toTensor : AST.Block → Option Syntax.TensorBlock
  | ⟨.ident name,
      [⟨.public, .input, .variable, .literal "Real", [.literal "2"], .ident input⟩,
       ⟨.public, .output, .variable, .literal "Real", [.literal "2"], .ident state⟩,
       ⟨.public, .output, .variable, .literal "Real", [.literal "2", .literal "2"], .ident jacobian⟩,
       ⟨.protected, .local, .constant, .literal "Real", [], .ident clock⟩],
      [⟨.public, .literal "Startup",
        [.assign ⟨.literal "self", [.ident initialState]⟩ (.literal (.literal "0.0")),
         .assign ⟨.literal "self", [.ident initialClock]⟩ (.literal (.literal "1.0"))], .literal "Startup"⟩,
       ⟨.public, .literal "Recalibrate", [], .literal "Recalibrate"⟩,
       ⟨.public, .literal "DoStep",
        [.assign ⟨.literal "self", [.ident stepState]⟩
          (.binary (.literal ".*") (.reference ⟨.literal "self", [.ident derivLeft]⟩)
            (.reference ⟨.literal "self", [.ident derivRight]⟩)),
         .assign ⟨.literal "self", [.ident jacTarget]⟩
          (.call (.ident jacFn)
            [.binary (.literal ".*") (.reference ⟨.literal "self", [.ident jacLeft]⟩)
              (.reference ⟨.literal "self", [.ident jacRight]⟩),
             .reference ⟨.literal "self", [.ident jacArg]⟩])], .literal "DoStep"⟩], .ident endName⟩ =>
      some ⟨name, input, state, jacobian, clock, initialState, initialClock, stepState,
        derivLeft, derivRight, jacTarget, jacFn, jacLeft, jacRight, jacArg, endName⟩
  | _ => none

theorem scalar_retraction (b : Syntax.Block) : toScalar (ofScalar b) = some b := by
  cases b; rfl

theorem tensor_retraction (b : Syntax.TensorBlock) : toTensor (ofTensor b) = some b := by
  cases b; rfl

theorem scalar_projection_exact (h : toScalar ast = some b) : ast = ofScalar b := by
  unfold toScalar at h
  split at h
  · cases Option.some.inj h; rfl
  · contradiction

theorem tensor_projection_exact (h : toTensor ast = some b) : ast = ofTensor b := by
  unfold toTensor at h
  split at h
  · cases Option.some.inj h; rfl
  · contradiction

theorem scalar_projection_iff : toScalar ast = some b ↔ ast = ofScalar b :=
  ⟨scalar_projection_exact, fun h => h ▸ scalar_retraction b⟩

theorem tensor_projection_iff : toTensor ast = some b ↔ ast = ofTensor b :=
  ⟨tensor_projection_exact, fun h => h ▸ tensor_retraction b⟩

end Rumoca.GALEC.ProfileProjection


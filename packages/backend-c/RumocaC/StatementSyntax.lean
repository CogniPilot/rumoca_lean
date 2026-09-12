import RumocaC.ExpressionSyntax

/-! Independent token productions for the CTree block items. Declarations
occupy block-item positions, and every emitted control-flow body is compound.
The productions select N1570 §§6.5.16, 6.7, 6.7.9 and 6.8.2–6.8.6. Their
expression categories retain C's unary assignment target and assignment-valued
initializer restrictions. Modifiable lvalues, scope and type correctness are
separate execution obligations; these syntax judgments do not assert them. -/
namespace Rumoca.CTree.Syntax
open CTokens

mutual
inductive BlockItem (typedefs : List String) : List Token → Stmt → Prop where
  | declare : TypeDenotation typedefs type typeTokens → CIdentifier.valid typedefs name = true →
      Expression typedefs .assignment valueTokens value →
      BlockItem typedefs
        (typeTokens ++ [.word name, .punctuator "="] ++ valueTokens ++ [.punctuator ";"])
        (.declare type name value)
  | assign : Expression typedefs .unary targetTokens target →
      Expression typedefs .assignment valueTokens value →
      BlockItem typedefs (targetTokens ++ [.punctuator "="] ++ valueTokens ++ [.punctuator ";"])
        (.assign target value)
  | eval : Expression typedefs .expression tokens value →
      BlockItem typedefs (tokens ++ [.punctuator ";"]) (.eval value)
  | returnVoid : BlockItem typedefs [.word "return", .punctuator ";"] (.ret none)
  | returnValue : Expression typedefs .expression tokens value →
      BlockItem typedefs (.word "return" :: tokens ++ [.punctuator ";"]) (.ret (some value))
  | ifThen : Expression typedefs .expression conditionTokens condition →
      BlockItems typedefs yesTokens yes →
      BlockItem typedefs ([.word "if", .punctuator "("] ++ conditionTokens ++
        [.punctuator ")", .punctuator "{"] ++ yesTokens ++ [.punctuator "}"])
        (.branch condition yes [])
  | ifElse : Expression typedefs .expression conditionTokens condition →
      BlockItems typedefs yesTokens yes → BlockItems typedefs noTokens no →
      BlockItem typedefs ([.word "if", .punctuator "("] ++ conditionTokens ++
        [.punctuator ")", .punctuator "{"] ++ yesTokens ++
        [.punctuator "}", .word "else", .punctuator "{"] ++ noTokens ++ [.punctuator "}"])
        (.branch condition yes no)
  | whileLoop : Expression typedefs .expression conditionTokens condition →
      BlockItems typedefs bodyTokens body →
      BlockItem typedefs ([.word "while", .punctuator "("] ++ conditionTokens ++
        [.punctuator ")", .punctuator "{"] ++ bodyTokens ++ [.punctuator "}"])
        (.whileLoop condition body)

inductive BlockItems (typedefs : List String) : List Token → List Stmt → Prop where
  | nil : BlockItems typedefs [] []
  | cons : BlockItem typedefs first stmt → BlockItems typedefs rest stmts →
      BlockItems typedefs (first ++ rest) (stmt :: stmts)
end

end Rumoca.CTree.Syntax

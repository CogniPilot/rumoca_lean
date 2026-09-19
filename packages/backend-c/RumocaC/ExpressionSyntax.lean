import RumocaC.TypeSyntax
import RumocaC.TreeBoundary

/-! Independent expression-token grammar for CTree's existing operators.
The precedence classes and widening chain follow N1570 §6.5. Classes whose
operators are not emitted still appear in the chain. Field/call/subscript bases
must be postfix expressions; unary operands must be cast expressions. This
avoids assigning a CTree interpretation to a different C parse.
Syntax alone does not establish type validity, evaluation order or execution. -/
namespace Rumoca.CTree.Syntax
open CTokens

inductive Category where
  | primary | postfix | unary | cast | multiplicative | additive | shift
  | relational | equality | bitAnd | bitXor | bitOr | logicalAnd | logicalOr
  | conditional | assignment | expression
  deriving DecidableEq, Repr

def Category.rank : Category → Nat
  | .primary => 0 | .postfix => 1 | .unary => 2 | .cast => 3
  | .multiplicative => 4 | .additive => 5 | .shift => 6 | .relational => 7
  | .equality => 8 | .bitAnd => 9 | .bitXor => 10 | .bitOr => 11
  | .logicalAnd => 12 | .logicalOr => 13 | .conditional => 14
  | .assignment => 15 | .expression => 16

/-- C binary productions specify left/right precedence and exact spelling
independently of `BinOp.render`. The left category is also the result category. -/
inductive BinarySyntax : BinOp → Category → Category → String → Prop where
  | mul : BinarySyntax .mul .multiplicative .cast "*"
  | add : BinarySyntax .add .additive .multiplicative "+"
  | sub : BinarySyntax .sub .additive .multiplicative "-"
  | lt : BinarySyntax .lt .relational .shift "<"
  | le : BinarySyntax .le .relational .shift "<="
  | gt : BinarySyntax .gt .relational .shift ">"
  | ge : BinarySyntax .ge .relational .shift ">="
  | eq : BinarySyntax .eq .equality .relational "=="
  | ne : BinarySyntax .ne .equality .relational "!="
  | and : BinarySyntax .and .logicalAnd .bitOr "&&"
  | or : BinarySyntax .or .logicalOr .logicalAnd "||"

mutual
inductive Expression (typedefs : List String) : Category → List CTokens.Token → Expr → Prop where
  | identifier : CIdentifier.valid typedefs name = true →
      Expression typedefs .primary [.word name] (.id name)
  | natural : CDecimal.Denotes spelling.toList n →
      Expression typedefs .primary [.number spelling] (.nat n)
  | decimalMagnitude : Expression typedefs .primary
      [.number (Expr.decimalMagnitude mantissa exponent)] (.decimal false mantissa exponent)
  | decimalNegative : Expression typedefs .primary
      [.punctuator "(", .punctuator "-", .number (Expr.decimalMagnitude mantissa exponent),
        .punctuator ")"] (.decimal true mantissa exponent)
  | string : Expression typedefs .primary [.string (value.toUTF8.data.toList ++ [0])] (.str value)
  | widen : lower.rank ≤ upper.rank → Expression typedefs lower tokens expr →
      Expression typedefs upper tokens expr
  | parenthesized : Expression typedefs .expression tokens expr →
      Expression typedefs .primary (.punctuator "(" :: tokens ++ [.punctuator ")"]) expr
  | binary : BinarySyntax op leftCategory rightCategory spelling →
      Expression typedefs leftCategory left a → Expression typedefs rightCategory right b →
      Expression typedefs leftCategory (left ++ [.punctuator spelling] ++ right) (.bin op a b)
  | not : Expression typedefs .cast tokens expr →
      Expression typedefs .unary (.punctuator "!" :: tokens) (.not expr)
  | dereference : Expression typedefs .cast tokens expr →
      Expression typedefs .unary (.punctuator "*" :: tokens) (.deref expr)
  | address : Expression typedefs .cast tokens expr →
      Expression typedefs .unary (.punctuator "&" :: tokens) (.address expr)
  | field : Expression typedefs .postfix tokens expr → CIdentifier.valid [] name = true →
      Expression typedefs .postfix (tokens ++ [.punctuator ".", .word name]) (.field expr name false)
  | pointerField : Expression typedefs .postfix tokens expr → CIdentifier.valid [] name = true →
      Expression typedefs .postfix (tokens ++ [.punctuator "->", .word name]) (.field expr name true)
  | index : Expression typedefs .postfix base expr → Expression typedefs .expression index i →
      Expression typedefs .postfix (base ++ [.punctuator "["] ++ index ++ [.punctuator "]"])
        (.index expr i)
  | callEmpty : Expression typedefs .postfix base fn →
      Expression typedefs .postfix (base ++ [.punctuator "(", .punctuator ")"]) (.call fn [])
  | call : Expression typedefs .postfix base fn → Arguments typedefs args values →
      Expression typedefs .postfix (base ++ [.punctuator "("] ++ args ++ [.punctuator ")"])
        (.call fn values)
  | cast : TypeDenotation typedefs type typeTokens → Expression typedefs .cast tokens expr →
      Expression typedefs .cast (.punctuator "(" :: typeTokens ++ [.punctuator ")"] ++ tokens)
        (.cast type expr)
  | sizeof : TypeDenotation typedefs type typeTokens →
      Expression typedefs .unary ([.word "sizeof", .punctuator "("] ++ typeTokens ++ [.punctuator ")"])
        (.sizeof type)

/-- The nonempty, comma-separated assignment expressions of a C call. -/
inductive Arguments (typedefs : List String) : List CTokens.Token → List Expr → Prop where
  | one : Expression typedefs .assignment tokens expr → Arguments typedefs tokens [expr]
  | cons : Expression typedefs .assignment first expr → Arguments typedefs rest values →
      Arguments typedefs (first ++ [.punctuator ","] ++ rest) (expr :: values)
end

private theorem rank_le_expression (category : Category) : category.rank ≤ Category.expression.rank := by
  cases category <;> decide +kernel

theorem binary_render_syntax (op : BinOp) :
    ∃ left right, BinarySyntax op left right op.render ∧
      Category.cast.rank ≤ left.rank ∧ Category.cast.rank ≤ right.rank := by
  cases op with
  | mul => exact ⟨_, _, .mul, by decide +kernel, by decide +kernel⟩
  | add => exact ⟨_, _, .add, by decide +kernel, by decide +kernel⟩
  | sub => exact ⟨_, _, .sub, by decide +kernel, by decide +kernel⟩
  | lt => exact ⟨_, _, .lt, by decide +kernel, by decide +kernel⟩
  | le => exact ⟨_, _, .le, by decide +kernel, by decide +kernel⟩
  | gt => exact ⟨_, _, .gt, by decide +kernel, by decide +kernel⟩
  | ge => exact ⟨_, _, .ge, by decide +kernel, by decide +kernel⟩
  | eq => exact ⟨_, _, .eq, by decide +kernel, by decide +kernel⟩
  | ne => exact ⟨_, _, .ne, by decide +kernel, by decide +kernel⟩
  | and => exact ⟨_, _, .and, by decide +kernel, by decide +kernel⟩
  | or => exact ⟨_, _, .or, by decide +kernel, by decide +kernel⟩

/-- Every binary operator emitted by CTree has the intended parse when its
operands are cast expressions and the result is parenthesized. -/
theorem Expression.binary_grouped (op : BinOp)
    (left : Expression typedefs .cast leftTokens a) (right : Expression typedefs .cast rightTokens b) :
    Expression typedefs .primary
      (.punctuator "(" :: (leftTokens ++ [.punctuator op.render] ++ rightTokens) ++ [.punctuator ")"])
      (.bin op a b) := by
  obtain ⟨leftCategory, rightCategory, spelling, leftBound, rightBound⟩ := binary_render_syntax op
  exact .parenthesized (.widen (rank_le_expression leftCategory)
    (.binary spelling (.widen leftBound left) (.widen rightBound right)))

/-- The phrase grammar itself establishes the spelling conditions used by
the shared leading-character proof; the printer need not assume them twice. -/
theorem Expression.identifier_inputs (tree : Expression typedefs category tokens expr) :
    IdentifierInputs typedefs expr := by
  induction tree using Expression.rec (motive_2 := fun _ values _ =>
      ∀ expr ∈ values, IdentifierInputs typedefs expr) <;>
    simp_all [IdentifierInputs]
  rename_i firstTokens firstExpr restTokens restExprs firstTree restTree firstGood restGood expr member
  rcases member with rfl | member
  · exact firstGood
  · exact restGood expr member

end Rumoca.CTree.Syntax

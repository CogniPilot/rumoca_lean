import RumocaC.StatementSyntax

/-! Selected C parameter, prototype and function-definition productions,
N1570 §§6.7.6 and 6.9.1. Array parameters use the emitted unsized form; an
empty CTree parameter list emits the explicit `(void)` prototype. Storage,
type compatibility, name scope and ABI validity remain separate obligations. -/
namespace Rumoca.CTree.Syntax
open CTokens

inductive ParameterPhrase (typedefs : List String) : List Token → Parameter → Prop where
  | scalar : TypeDenotation typedefs type tokens → CIdentifier.valid typedefs name = true →
      ParameterPhrase typedefs (tokens ++ [.word name]) ⟨type, name, false⟩
  | array : TypeDenotation typedefs type tokens → CIdentifier.valid typedefs name = true →
      ParameterPhrase typedefs (tokens ++ [.word name, .punctuator "[", .punctuator "]"])
        ⟨type, name, true⟩

inductive ParametersPhrase (typedefs : List String) : List Token → List Parameter → Prop where
  | one : ParameterPhrase typedefs tokens param → ParametersPhrase typedefs tokens [param]
  | cons : ParameterPhrase typedefs first param → ParametersPhrase typedefs rest params →
      ParametersPhrase typedefs (first ++ [.punctuator ","] ++ rest) (param :: params)

inductive SignaturePhrase (typedefs : List String) : List Token → Signature → Prop where
  | empty : TypeDenotation typedefs result resultTokens → CIdentifier.valid typedefs name = true →
      SignaturePhrase typedefs
        (resultTokens ++ [.word name, .punctuator "(", .word "void", .punctuator ")"])
        ⟨result, name, []⟩
  | params : TypeDenotation typedefs result resultTokens → CIdentifier.valid typedefs name = true →
      ParametersPhrase typedefs paramTokens params →
      SignaturePhrase typedefs (resultTokens ++ [.word name, .punctuator "("] ++
        paramTokens ++ [.punctuator ")"]) ⟨result, name, params⟩

inductive FunctionPhrase (typedefs : List String) : List Token → Function → Prop where
  | external : SignaturePhrase typedefs signatureTokens signature →
      BlockItems typedefs bodyTokens body →
      FunctionPhrase typedefs (signatureTokens ++ [.punctuator "{"] ++ bodyTokens ++ [.punctuator "}"])
        ⟨signature, body, false⟩
  | internal : SignaturePhrase typedefs signatureTokens signature →
      BlockItems typedefs bodyTokens body →
      FunctionPhrase typedefs (.word "static" :: signatureTokens ++
        [.punctuator "{"] ++ bodyTokens ++ [.punctuator "}"]) ⟨signature, body, true⟩

end Rumoca.CTree.Syntax

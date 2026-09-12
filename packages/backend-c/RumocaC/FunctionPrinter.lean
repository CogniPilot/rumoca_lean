import RumocaC.StatementPrinter
import RumocaC.FunctionSyntax

/-! Generic parameter and whole-function printer proofs. These bind the actual
renderer characters to an independent C token grammar, for arbitrary parameters
and nested statements. They do not discharge typing, scope, header expansion
or function execution. -/
namespace Rumoca.CTree.Printer
open Syntax
open CTokens (separator_prefix)

def ParameterPrintable (typedefs : List String) (param : Parameter) : Prop :=
  TypeSpelling typedefs param.type ∧ CIdentifier.valid typedefs param.name = true

def ParameterRenders (typedefs : List String) (param : Parameter) : Prop :=
  ∃ tokens, ParameterPhrase typedefs tokens param ∧ ∀ marker ∈ [',', ')'], ∀ rest,
    CTokens.Prefix (param.render.toList ++ marker :: rest) tokens (marker :: rest)

theorem parameter_renders (valid : ParameterPrintable typedefs param) : ParameterRenders typedefs param := by
  obtain ⟨⟨typeTokens, type⟩, validName⟩ := valid
  rcases param with ⟨typeName, name, array⟩
  cases array with
  | false =>
      refine ⟨_, .scalar type validName, ?_⟩
      intro marker delimiter rest
      have boundary : CLexical.identifierCharacter marker = false ∧ marker ≠ '"' ∧ marker ≠ '\'' := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at delimiter
        rcases delimiter with rfl | rfl <;> decide +kernel
      have word := CTokens.word_prefix (CIdentifier.word_parts typedefs name validName)
        boundary.1 boundary.2.1 boundary.2.2 rest
      have typeChars := type.lexical ' ' (by simp) (name.toList ++ marker :: rest)
      simpa only [Parameter.render, Bool.false_eq_true, ↓reduceIte, String.toList_append,
        List.append_assoc, List.cons_append, List.nil_append, String.toList_empty, List.append_nil] using
        typeChars.append (.space (by decide +kernel) word)
  | true =>
      refine ⟨_, .array type validName, ?_⟩
      intro marker delimiter rest
      have close := separator_prefix (spelling := "]") (by simp) (marker :: rest)
      have openBracket := separator_prefix (spelling := "[") (by simp) (']' :: marker :: rest)
      have word := CTokens.word_prefix (CIdentifier.word_parts typedefs name validName)
        (marker := '[') (by decide +kernel) (by decide +kernel) (by decide +kernel) (']' :: marker :: rest)
      have typeChars := type.lexical ' ' (by simp) (name.toList ++ '[' :: ']' :: marker :: rest)
      simpa only [Parameter.render, ↓reduceIte, String.toList_append,
        List.append_assoc, List.cons_append, List.nil_append] using
        typeChars.append (.space (by decide +kernel) (word.append (openBracket.append close)))

def ParametersRender (typedefs : List String) (params : List Parameter) : Prop :=
  ∃ tokens, ((params = [] ∧ tokens = []) ∨ ParametersPhrase typedefs tokens params) ∧ ∀ rest,
    CTokens.Prefix ((String.intercalate ", " (params.map Parameter.render)).toList ++ ')' :: rest)
      tokens (')' :: rest)

theorem parameters_render (all : ∀ param ∈ params, ParameterRenders typedefs param) :
    ParametersRender typedefs params := by
  induction params with
  | nil => exact ⟨[], Or.inl ⟨rfl, rfl⟩, fun _ => .done⟩
  | cons first remaining ih =>
      obtain ⟨firstTokens, firstGrammar, firstLex⟩ := all first (by simp)
      cases remaining with
      | nil =>
          refine ⟨firstTokens, Or.inr (.one firstGrammar), ?_⟩
          intro rest
          simpa only [List.map_cons, List.map_nil, CText.intercalate_one] using
            firstLex ')' (by simp) rest
      | cons second remaining =>
          obtain ⟨restTokens, restGrammar, restLex⟩ := ih (fun p member => all p (by simp [member]))
          have nonempty : ParametersPhrase typedefs restTokens (second :: remaining) := by
            rcases restGrammar with impossible | grammar
            · cases impossible.1
            · exact grammar
          refine ⟨firstTokens ++ [.punctuator ","] ++ restTokens,
            Or.inr (.cons firstGrammar nonempty), ?_⟩
          intro rest
          have afterComma : CTokens.Prefix
              (' ' :: ((String.intercalate ", " ((second :: remaining).map Parameter.render)).toList ++ ')' :: rest))
              restTokens (')' :: rest) := .space (by decide +kernel) (restLex rest)
          have comma := separator_prefix (spelling := ",") (by simp)
            (' ' :: ((String.intercalate ", " ((second :: remaining).map Parameter.render)).toList ++ ')' :: rest))
          have initial := firstLex ',' (by simp)
            (' ' :: ((String.intercalate ", " ((second :: remaining).map Parameter.render)).toList ++ ')' :: rest))
          simpa only [List.map_cons, CText.intercalate_cons, String.toList_append,
            List.append_assoc, List.cons_append, List.nil_append] using initial.append (comma.append afterComma)

def SignaturePrintable (typedefs : List String) (signature : Signature) : Prop :=
  TypeSpelling typedefs signature.result ∧ CIdentifier.valid typedefs signature.name = true ∧
    ∀ param ∈ signature.parameters, ParameterPrintable typedefs param

def SignatureRenders (typedefs : List String) (signature : Signature) : Prop :=
  ∃ tokens, SignaturePhrase typedefs tokens signature ∧ ∀ rest,
    CTokens.Prefix (signature.render.toList ++ rest) tokens rest

theorem signature_renders (valid : SignaturePrintable typedefs signature) :
    SignatureRenders typedefs signature := by
  obtain ⟨⟨typeTokens, type⟩, validName, params⟩ := valid
  rcases signature with ⟨result, name, parameters⟩
  have opening : ∀ rest, CTokens.Prefix ((result ++ " " ++ name ++ "(").toList ++ rest)
      (typeTokens ++ [.word name, .punctuator "("]) rest := by
    intro rest
    have paren := separator_prefix (spelling := "(") (by simp) rest
    have word := CTokens.word_prefix (CIdentifier.word_parts typedefs name validName)
      (marker := '(') (by decide +kernel) (by decide +kernel) (by decide +kernel) rest
    have typeChars := type.lexical ' ' (by simp) (name.toList ++ '(' :: rest)
    simpa only [String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
      typeChars.append (.space (by decide +kernel) (word.append paren))
  cases parameters with
  | nil =>
      refine ⟨_, .empty type validName, ?_⟩
      intro rest
      have word := CTokens.word_prefix (name := "void")
        (show CIdentifierToken.WordParts "void" from ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩)
        (marker := ')') (by decide +kernel) (by decide +kernel) (by decide +kernel) rest
      have close := separator_prefix (spelling := ")") (by simp) rest
      simpa only [Signature.render, List.isEmpty_nil, ↓reduceIte, String.toList_append,
        List.append_assoc, List.cons_append, List.nil_append] using
        (opening ("void".toList ++ ')' :: rest)).append (word.append close)
  | cons first remaining =>
      obtain ⟨paramTokens, phrase, lexed⟩ := parameters_render
        (fun param member => parameter_renders (params param member))
      have nonempty : ParametersPhrase typedefs paramTokens (first :: remaining) := by
        rcases phrase with impossible | grammar
        · cases impossible.1
        · exact grammar
      refine ⟨_, .params type validName nonempty, ?_⟩
      intro rest
      have close := separator_prefix (spelling := ")") (by simp) rest
      simpa only [Signature.render, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
        (opening ((String.intercalate ", " ((first :: remaining).map Parameter.render)).toList ++ ')' :: rest)).append
          ((lexed rest).append close)

def FunctionPrintable (typedefs : List String) (function : Function) : Prop :=
  SignaturePrintable typedefs function.signature ∧ ∀ stmt ∈ function.body, ItemPrintable typedefs stmt

def FunctionRenders (typedefs : List String) (function : Function) : Prop :=
  ∃ tokens, FunctionPhrase typedefs tokens function ∧ ∀ rest,
    CTokens.Prefix (function.render.toList ++ rest) tokens rest

/-- The whole text has the supplied construction tree's independent token
derivation. This also accepts independently read text in artifact contracts. -/
def FunctionDenotes (typedefs : List String) (text : String) (function : Function) : Prop :=
  ∃ tokens, FunctionPhrase typedefs tokens function ∧ CTokens.Lexes text.toList tokens

/-- Every admissible complete CTree function prints its intended token grammar.
This theorem is reusable by both backends and preserves the existing printer. -/
theorem function_renders (valid : FunctionPrintable typedefs function) :
    FunctionRenders typedefs function := by
  obtain ⟨signatureValid, bodyValid⟩ := valid
  obtain ⟨signatureTokens, signatureGrammar, signatureLex⟩ := signature_renders signatureValid
  obtain ⟨bodyTokens, bodyGrammar, bodyLex⟩ := items_render
    (fun stmt member => statement_renders (bodyValid stmt member))
  have core : ∀ rest, CTokens.Prefix ((function.signature.render ++ " {\n" ++
      String.join (function.body.map fun s => s.render 1) ++ "}\n\n").toList ++ rest)
      (signatureTokens ++ [.punctuator "{"] ++ bodyTokens ++ [.punctuator "}"]) rest := by
    intro rest
    have close := separator_prefix (spelling := "}") (by simp) ('\n' :: '\n' :: rest)
    have final : CTokens.Prefix ('\n' :: '\n' :: rest) [] rest :=
      .space (by decide +kernel) (.space (by decide +kernel) .done)
    have bodyChars := bodyLex 1 ('}' :: '\n' :: '\n' :: rest)
    have openBrace := separator_prefix (spelling := "{") (by simp)
      ('\n' :: ((String.join (function.body.map fun s => s.render 1)).toList ++ '}' :: '\n' :: '\n' :: rest))
    have signatureChars := signatureLex
      (' ' :: '{' :: '\n' :: ((String.join (function.body.map fun s => s.render 1)).toList ++ '}' :: '\n' :: '\n' :: rest))
    simpa only [String.toList_append, List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using
      signatureChars.append (.space (by decide +kernel)
        (openBrace.append (.space (by decide +kernel) (bodyChars.append (close.append final)))))
  rcases function with ⟨signature, body, static⟩
  cases static with
  | false =>
      refine ⟨_, .external signatureGrammar bodyGrammar, ?_⟩
      intro rest
      simpa only [Function.render, Bool.false_eq_true, ↓reduceIte, String.empty_append] using core rest
  | true =>
      refine ⟨_, .internal signatureGrammar bodyGrammar, ?_⟩
      intro rest
      have word := CTokens.word_prefix (name := "static")
        (show CIdentifierToken.WordParts "static" from ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩)
        (marker := ' ') (by decide +kernel) (by decide +kernel) (by decide +kernel)
        ((signature.render ++ " {\n" ++ String.join (body.map fun s => s.render 1) ++ "}\n\n").toList ++ rest)
      simpa only [Function.render, ↓reduceIte, String.toList_append,
        List.append_assoc, List.cons_append, List.nil_append] using
        word.append (.space (by decide +kernel) (core rest))

theorem function_denotes (valid : FunctionPrintable typedefs function) :
    FunctionDenotes typedefs function.render function := by
  obtain ⟨tokens, grammar, lexed⟩ := function_renders valid
  exact ⟨tokens, grammar, by simpa only [List.append_nil] using lexed []⟩

end Rumoca.CTree.Printer

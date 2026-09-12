import RumocaC.Tokens

/-! Independent type-name syntax for the existing structured C printer.
N1570 §§6.7.2,6.7.3,6.7.6 and 6.7.7 provide the selected primitive/typedef,
qualifier and pointer productions. Surrounding typedef declarations are explicit
inputs. This module proves text/token syntax, not C type compatibility, object
layout, scope validity or ABI meanings. It adds no C reader or compiler pass. -/
namespace Rumoca.CTree.Syntax
open CTokens

inductive TypeSpecifier (typedefs : List String) : String → Prop where
  | primitive : name ∈ ["void", "char", "int", "double"] → TypeSpecifier typedefs name
  | typedefName : name ∈ typedefs → CIdentifier.valid [] name = true → TypeSpecifier typedefs name

/-- Selected specifier/qualifier and abstract-pointer productions. -/
inductive TypeTokens (typedefs : List String) : List CTokens.Token → Prop where
  | named : TypeSpecifier typedefs name → TypeTokens typedefs [.word name]
  | const : TypeTokens typedefs tokens → TypeTokens typedefs (.word "const" :: tokens)
  | pointer : TypeTokens typedefs tokens →
      TypeTokens typedefs (tokens ++ [.punctuator "*"])

/-- A type spelling with its independent phrase grammar and lexical contract
at both delimiters used by the current renderer: a space before a declarator,
or a closing parenthesis in a cast/sizeof. Every continuation is quantified. -/
structure TypeDenotation (typedefs : List String) (text : String)
    (tokens : List CTokens.Token) : Prop where
  phrase : TypeTokens typedefs tokens
  lexical : ∀ marker ∈ [' ', ')'], ∀ rest,
    CTokens.Prefix (text.toList ++ marker :: rest) tokens (marker :: rest)

def TypeSpelling (typedefs : List String) (text : String) : Prop :=
  ∃ tokens, TypeDenotation typedefs text tokens

theorem TypeSpecifier.word_parts (specifier : TypeSpecifier typedefs name) :
    CIdentifierToken.WordParts name := by
  cases specifier with
  | primitive member =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        exact ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
  | typedefName member valid => exact CIdentifier.word_parts [] name valid

private theorem type_delimiter (member : marker ∈ [' ', ')']) :
    CLexical.identifierCharacter marker = false ∧ marker ≠ '"' ∧ marker ≠ '\'' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

theorem TypeSpelling.named (specifier : TypeSpecifier typedefs name) : TypeSpelling typedefs name := by
  refine ⟨[.word name], .named specifier, ?_⟩
  intro marker member rest
  have boundary := type_delimiter member
  exact CTokens.word_prefix specifier.word_parts boundary.1 boundary.2.1 boundary.2.2 rest

theorem TypeSpelling.const (type : TypeSpelling typedefs text) :
    TypeSpelling typedefs ("const " ++ text) := by
  obtain ⟨tokens, phrase, lexed⟩ := type
  refine ⟨.word "const" :: tokens, .const phrase, ?_⟩
  intro marker member rest
  have first := CTokens.word_prefix (name := "const")
    (show CIdentifierToken.WordParts "const" from ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩)
    (marker := ' ') (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (text.toList ++ marker :: rest)
  have after : CTokens.Prefix (' ' :: (text.toList ++ marker :: rest)) tokens (marker :: rest) :=
    .space (by decide +kernel) (lexed marker member rest)
  simpa only [String.toList_append, List.cons_append, List.nil_append] using first.append after

private theorem pointer_prefix (member : marker ∈ [' ', ')']) (rest : List Char) :
    CTokens.Prefix ('*' :: marker :: rest) [.punctuator "*"] (marker :: rest) := by
  apply CTokens.punctuator_prefix
  · apply CPunctuator.consumes_boundary (spelling := "*") (by decide +kernel)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  · simp [CTokens.PunctuationSafe]

theorem TypeSpelling.pointer (type : TypeSpelling typedefs text) :
    TypeSpelling typedefs (text ++ " *") := by
  obtain ⟨tokens, phrase, lexed⟩ := type
  refine ⟨tokens ++ [.punctuator "*"], .pointer phrase, ?_⟩
  intro marker member rest
  have first := lexed ' ' (by simp) ('*' :: marker :: rest)
  have after : CTokens.Prefix (' ' :: '*' :: marker :: rest) [.punctuator "*"] (marker :: rest) :=
    .space (by decide +kernel) (pointer_prefix member rest)
  simpa only [String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    first.append after

end Rumoca.CTree.Syntax

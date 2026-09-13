import RumocaC.ObjectDeclarationCode
import RumocaC.TypeSyntax
import RumocaC.TreeBoundary
import RumocaC.TextLemmas

/-! Independent C11 declaration phrases and character-to-token proofs for
structured permanent-storage declarations. This is syntax and exact bound/
initializer spelling; typedef meaning, constant ranges, object layout and
static initialization semantics remain distinct obligations. No C parser is
introduced. The same continuation-aware token judgments serve C functions. -/
namespace Rumoca.CObject
open CTree.Syntax CTokens

inductive FieldPhrase (typedefs : List String) : List Token → Field → Prop where
  | scalar : TypeDenotation typedefs type tokens → CIdentifier.valid typedefs name = true →
      FieldPhrase typedefs (tokens ++ [.word name, .punctuator ";"]) ⟨type, name⟩

inductive FieldsPhrase (typedefs : List String) : List Token → List Field → Prop where
  | nil : FieldsPhrase typedefs [] []
  | cons : FieldPhrase typedefs head field → FieldsPhrase typedefs tail fields →
      FieldsPhrase typedefs (head ++ tail) (field :: fields)

inductive RecordPhrase (typedefs : List String) : List Token → Record → Prop where
  | typedefRecord : fields ≠ [] → (fields.map Field.name).Nodup →
      FieldsPhrase typedefs tokens fields → CIdentifier.valid typedefs name = true →
      RecordPhrase typedefs ([.word "typedef", .word "struct", .punctuator "{"] ++ tokens ++
        [.punctuator "}", .word name, .punctuator ";"]) ⟨name, fields⟩

inductive ArrayPhrase (typedefs : List String) : List Token → StaticArray → Prop where
  | fixed : TypeDenotation typedefs type tokens → CIdentifier.valid typedefs name = true →
      0 < count → CDecimal.Denotes bound.toList count →
      ArrayPhrase typedefs (.word "static" :: tokens ++
        [.word name, .punctuator "[", .number bound, .punctuator "]", .punctuator ";"])
        ⟨type, name, count⟩

inductive ConstantPhrase (typedefs : List String) : List Token → Constant → Prop where
  | natural : TypeDenotation typedefs type tokens → CIdentifier.valid typedefs name = true →
      CDecimal.Denotes spelling.toList value →
      ConstantPhrase typedefs ([.word "static", .word "const"] ++ tokens ++
        [.word name, .punctuator "=", .number spelling, .punctuator ";"]) ⟨type, name, value⟩

def FieldPrintable (typedefs : List String) (field : Field) : Prop :=
  TypeSpelling typedefs field.type ∧ CIdentifier.valid typedefs field.name = true

def RecordPrintable (typedefs : List String) (record : Record) : Prop :=
  record.fields ≠ [] ∧ (record.fields.map Field.name).Nodup ∧
    CIdentifier.valid typedefs record.name = true ∧ ∀ field ∈ record.fields, FieldPrintable typedefs field

def ArrayPrintable (typedefs : List String) (array : StaticArray) : Prop :=
  TypeSpelling typedefs array.type ∧ CIdentifier.valid typedefs array.name = true ∧ 0 < array.count

def ConstantPrintable (typedefs : List String) (constant : Constant) : Prop :=
  TypeSpelling typedefs constant.type ∧ CIdentifier.valid typedefs constant.name = true

def Renders (phrase : List Token → α → Prop) (render : α → String) (object : α) : Prop :=
  ∃ tokens, phrase tokens object ∧ ∀ rest, CTokens.Prefix ((render object).toList ++ rest) tokens rest

private theorem static_prefix (rest : List Char) :
    CTokens.Prefix ("static ".toList ++ rest) [.word "static"] rest := by
  have word := CTokens.word_prefix (name := "static")
    (show CIdentifierToken.WordParts "static" from ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩)
    (marker := ' ') (by decide +kernel) (by decide +kernel) (by decide +kernel) rest
  exact word.append (.space (by decide +kernel) .done)

private theorem keyword_prefix (name : String) (member : name ∈ ["typedef", "struct", "const"])
    (rest : List Char) : CTokens.Prefix ((name ++ " ").toList ++ rest) [.word name] rest := by
  have parts : CIdentifierToken.WordParts name := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
  have word := CTokens.word_prefix parts (marker := ' ')
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rest
  simpa only [String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    word.append (.space (by decide +kernel) .done)

theorem field_renders (valid : FieldPrintable typedefs field) : Renders (FieldPhrase typedefs) Field.render field := by
  obtain ⟨⟨tokens, type⟩, name⟩ := valid
  refine ⟨tokens ++ [.word field.name, .punctuator ";"], .scalar type name, ?_⟩
  intro rest
  have endToken := CTokens.separator_prefix (spelling := ";") (by simp) rest
  have word := CTokens.word_prefix (CIdentifier.word_parts typedefs field.name name)
    (marker := ';') (by decide +kernel) (by decide +kernel) (by decide +kernel) rest
  have typed := type.lexical ' ' (by simp) (field.name.toList ++ ';' :: rest)
  simpa only [Field.render, String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    typed.append (.space (by decide +kernel) (word.append endToken))

theorem fields_render (valid : ∀ field ∈ fields, FieldPrintable typedefs field) :
    ∃ tokens, FieldsPhrase typedefs tokens fields ∧ ∀ rest,
      CTokens.Prefix ((String.join (fields.map fun field => "  " ++ field.render ++ "\n")).toList ++ rest) tokens rest := by
  induction fields with
  | nil => exact ⟨[], .nil, fun _ => .done⟩
  | cons field fields ih =>
      obtain ⟨first, phrase, lex⟩ := field_renders (valid field (by simp))
      obtain ⟨tail, remaining, suffix⟩ := ih (fun field member => valid field (by simp [member]))
      refine ⟨first ++ tail, .cons phrase remaining, ?_⟩
      intro rest
      have after := CTokens.Prefix.space (c := '\n') (by decide +kernel) (suffix rest)
      have composed := CTokens.Prefix.space (c := ' ') (by decide +kernel)
        (CTokens.Prefix.space (c := ' ') (by decide +kernel) ((lex _).append after))
      simpa only [List.map_cons, CString.join_toList, List.flatMap_cons, String.toList_append, List.append_assoc,
        List.cons_append, List.nil_append] using composed

theorem record_renders (valid : RecordPrintable typedefs record) : Renders (RecordPhrase typedefs) Record.render record := by
  obtain ⟨nonempty, unique, name, fields⟩ := valid
  obtain ⟨tokens, phrase, lex⟩ := fields_render fields
  refine ⟨[.word "typedef", .word "struct", .punctuator "{"] ++ tokens ++
    [.punctuator "}", .word record.name, .punctuator ";"], .typedefRecord nonempty unique phrase name, ?_⟩
  intro rest
  have semicolon := (CTokens.separator_prefix (spelling := ";") (by simp) ('\n' :: rest)).append
    (.space (by decide +kernel) .done)
  have word := CTokens.word_prefix (CIdentifier.word_parts typedefs record.name name)
    (marker := ';') (by decide +kernel) (by decide +kernel) (by decide +kernel) ('\n' :: rest)
  have close := CTokens.separator_prefix (spelling := "}") (by simp) (' ' :: (record.name.toList ++ ';' :: '\n' :: rest))
  have tail := close.append (.space (by decide +kernel) (word.append semicolon))
  have body := CTokens.Prefix.space (c := '\n') (by decide +kernel) ((lex _).append tail)
  have opening := CTokens.separator_prefix (spelling := "{") (by simp)
    ('\n' :: ((String.join (record.fields.map fun field => "  " ++ field.render ++ "\n")).toList ++
      '}' :: ' ' :: (record.name.toList ++ ';' :: '\n' :: rest)))
  simpa only [Record.render, String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    (keyword_prefix "typedef" (by simp) _).append
      ((keyword_prefix "struct" (by simp) _).append (opening.append body))

theorem array_renders (valid : ArrayPrintable typedefs array) : Renders (ArrayPhrase typedefs) StaticArray.render array := by
  obtain ⟨⟨tokens, type⟩, name, positive⟩ := valid
  refine ⟨.word "static" :: tokens ++
    [.word array.name, .punctuator "[", .number (toString array.count), .punctuator "]", .punctuator ";"],
    .fixed type name positive (CDecimal.render_denotes array.count), ?_⟩
  intro rest
  have line := CTokens.Prefix.space (c := '\n') (by decide +kernel) (CTokens.Prefix.done (rest := rest))
  have semicolon := CTokens.separator_prefix (spelling := ";") (by simp) ('\n' :: rest)
  have close := CTokens.separator_prefix (spelling := "]") (by simp) (';' :: '\n' :: rest)
  have count := CTokens.natural_prefix array.count (marker := ']') (by decide +kernel) (';' :: '\n' :: rest)
  have openBracket := CTokens.separator_prefix (spelling := "[") (by simp)
    ((toString array.count).toList ++ ']' :: ';' :: '\n' :: rest)
  have word := CTokens.word_prefix (CIdentifier.word_parts typedefs array.name name)
    (marker := '[') (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ((toString array.count).toList ++ ']' :: ';' :: '\n' :: rest)
  have typed := type.lexical ' ' (by simp)
    (array.name.toList ++ '[' :: ((toString array.count).toList ++ ']' :: ';' :: '\n' :: rest))
  have body := typed.append (.space (by decide +kernel)
    (word.append (openBracket.append (count.append (close.append (semicolon.append line))))))
  simpa only [StaticArray.render, String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    (static_prefix _).append body

theorem constant_renders (valid : ConstantPrintable typedefs constant) :
    Renders (ConstantPhrase typedefs) Constant.render constant := by
  obtain ⟨⟨tokens, type⟩, name⟩ := valid
  refine ⟨[.word "static", .word "const"] ++ tokens ++
    [.word constant.name, .punctuator "=", .number (toString constant.value), .punctuator ";"],
    .natural type name (CDecimal.render_denotes constant.value), ?_⟩
  intro rest
  have semicolon := (CTokens.separator_prefix (spelling := ";") (by simp) ('\n' :: rest)).append
    (.space (by decide +kernel) .done)
  have value := CTokens.natural_prefix constant.value (marker := ';') (by decide +kernel) ('\n' :: rest)
  have eq : CTokens.Prefix ('=' :: ' ' :: ((toString constant.value).toList ++ ';' :: '\n' :: rest))
      [.punctuator "="] (' ' :: ((toString constant.value).toList ++ ';' :: '\n' :: rest)) :=
    CTokens.punctuator_prefix (CPunctuator.consumes_space (spelling := "=") (by decide +kernel) _)
      (by simp [CTokens.PunctuationSafe])
  have assignment := CTokens.Prefix.space (c := ' ') (by decide +kernel)
    (eq.append (.space (by decide +kernel) (value.append semicolon)))
  have word := CTokens.word_prefix (CIdentifier.word_parts typedefs constant.name name)
    (marker := ' ') (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ('=' :: ' ' :: ((toString constant.value).toList ++ ';' :: '\n' :: rest))
  have typed := type.lexical ' ' (by simp)
    (constant.name.toList ++ ' ' :: '=' :: ' ' :: ((toString constant.value).toList ++ ';' :: '\n' :: rest))
  have body := typed.append (.space (by decide +kernel) (word.append assignment))
  simpa only [Constant.render, String.toList_append, List.append_assoc, List.cons_append, List.nil_append] using
    (static_prefix _).append ((keyword_prefix "const" (by simp) _).append body)

end Rumoca.CObject

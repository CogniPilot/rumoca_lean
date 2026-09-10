import XML.Basic

/-! A deliberately restricted XML 1.0 output grammar. It supports unqualified
ASCII names, printable ASCII attribute/text values, the five predefined
entities, and element-only or text-only content. No DTD, namespace resolution,
numeric references or attribute normalization is assumed. This is an output
contract, not a general XML parser or XSD validator. -/
namespace XML

def NameStart (c : Char) : Prop :=
  ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ c = '_'
def NameRest (c : Char) : Prop :=
  NameStart c ∨ ('0' ≤ c ∧ c ≤ '9') ∨ c = '-' ∨ c = '.'
def Name (s : String) : Prop := match s.toList with
  | [] => False
  | c :: cs => NameStart c ∧ ∀ d ∈ cs, NameRest d
def TextChar (c : Char) : Prop := 32 ≤ c.toNat ∧ c.toNat ≤ 126
def Text (s : String) : Prop := ∀ c ∈ s.toList, TextChar c

instance (c : Char) : Decidable (NameStart c) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))
instance (c : Char) : Decidable (NameRest c) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
instance (s : String) : Decidable (Name s) := by
  unfold Name; split <;> infer_instance
instance (c : Char) : Decidable (TextChar c) := inferInstanceAs (Decidable (_ ∧ _))
instance (s : String) : Decidable (Text s) := inferInstanceAs (Decidable (∀ c ∈ _, _))

def AttributesValid (attributes : List (String × String)) : Prop :=
  (attributes.map Prod.fst).Nodup ∧ ∀ a ∈ attributes, Name a.1 ∧ Text a.2
instance (attributes : List (String × String)) : Decidable (AttributesValid attributes) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Element.valid (e : Element) : Bool := match e with
  | ⟨name, attrs, children, text⟩ =>
    decide (Name name ∧ AttributesValid attrs ∧ Text text ∧
      (text = "" ∨ children = [])) && (children.map (fun c => c.valid)).all id

/-- The meaning of each literal or predefined entity, independently of escape. -/
inductive EscapedChar : Char → List Char → Prop where
  | literal (c) : TextChar c → c ≠ '&' → c ≠ '<' → c ≠ '>' → c ≠ '"' → c ≠ '\'' →
      EscapedChar c [c]
  | amp : EscapedChar '&' ['&', 'a', 'm', 'p', ';']
  | lt : EscapedChar '<' ['&', 'l', 't', ';']
  | gt : EscapedChar '>' ['&', 'g', 't', ';']
  | quot : EscapedChar '"' ['&', 'q', 'u', 'o', 't', ';']
  | apos : EscapedChar '\'' ['&', 'a', 'p', 'o', 's', ';']

inductive Escaped : List Char → List Char → Prop where
  | nil : Escaped [] []
  | cons : EscapedChar c encoded → Escaped rest suffix →
      Escaped (c :: rest) (encoded ++ suffix)

inductive Attributes : List (String × String) → List Char → Prop where
  | nil : Attributes [] []
  | cons : Name name → name ∉ rest.map Prod.fst → Escaped value.toList encoded →
      Attributes rest suffix → Attributes ((name, value) :: rest)
        ([' '] ++ name.toList ++ ['=', '"'] ++ encoded ++ ['"'] ++ suffix)

mutual
  inductive Parses : Element → List Char → Prop where
    | empty (depth : Nat) : Name name → Attributes attrs encoded →
        Parses ⟨name, attrs, [], ""⟩
          (List.replicate (depth * 2) ' ' ++ ['<'] ++ name.toList ++ encoded ++ ['/', '>', '\n'])
    | text (depth : Nat) : Name name → Attributes attrs encoded → Escaped value.toList body →
        Parses ⟨name, attrs, [], value⟩
          (List.replicate (depth * 2) ' ' ++ ['<'] ++ name.toList ++ encoded ++ ['>'] ++
            body ++ ['<', '/'] ++ name.toList ++ ['>', '\n'])
    | branch (depth : Nat) : Name name → Attributes attrs encoded → ParsesMany children body →
        Parses ⟨name, attrs, children, ""⟩
          (List.replicate (depth * 2) ' ' ++ ['<'] ++ name.toList ++ encoded ++ ['>', '\n'] ++
            body ++ List.replicate (depth * 2) ' ' ++ ['<', '/'] ++ name.toList ++ ['>', '\n'])
  inductive ParsesMany : List Element → List Char → Prop where
    | nil : ParsesMany [] []
    | cons : Parses e chars → ParsesMany es rest → ParsesMany (e :: es) (chars ++ rest)
end

def Document (root : Element) (source : String) : Prop := ∃ body,
  source.toList = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n".toList ++ body ∧ Parses root body

end XML

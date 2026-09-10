import XML.Proofs

/-! Compositional character certificates for the existing XML renderer.
Only each element's own opening/text/closing pieces are evaluated; child
documents are connected by their checked equalities. -/
namespace XML.Certificate

def escaped (value : String) : List Char :=
  value.toList.flatMap (fun c => (escapeChar c).toList)

def attributes (attrs : List (String × String)) : List Char := attrs.flatMap fun (k, v) =>
  [' '] ++ k.toList ++ ['=', '"'] ++ escaped v ++ ['"']

def leading (e : Element) (depth : Nat) : List Char :=
  let head := List.replicate (depth * 2) ' ' ++ ['<'] ++ e.name.toList ++ attributes e.attributes
  if e.children.isEmpty then
    if e.text.isEmpty then head ++ ['/', '>', '\n']
    else head ++ ['>'] ++ escaped e.text ++ ['<', '/'] ++ e.name.toList ++ ['>', '\n']
  else head ++ ['>', '\n'] ++ escaped e.text

def trailing (e : Element) (depth : Nat) : List Char :=
  if e.children.isEmpty then []
  else List.replicate (depth * 2) ' ' ++ ['<', '/'] ++ e.name.toList ++ ['>', '\n']

theorem escape_toList (value : String) : (escape value).toList = escaped value := by
  simp only [escape, escaped, join_toList, List.flatMap_map]

theorem attributes_toList (attrs : List (String × String)) :
    (String.join (attrs.map fun (k, v) => " " ++ k ++ "=\"" ++ escape v ++ "\"")).toList = attributes attrs := by
  simp only [attributes, join_toList, List.flatMap_map, String.toList_append, escape_toList]
  rfl

theorem render_parts (e : Element) (depth : Nat) :
    (e.render depth).toList = leading e depth ++
      (e.children.flatMap fun c => (c.render (depth + 1)).toList) ++ trailing e depth := by
  cases e with
  | mk name attrs children value =>
    cases children with
    | nil =>
      simp only [Element.render, leading, trailing, List.isEmpty_nil, ↓reduceIte,
        List.flatMap_nil, List.append_nil]
      split <;> simp only [String.toList_append, String.toList_ofList, attributes_toList,
        escape_toList, List.append_assoc] <;> rfl
    | cons c cs =>
      simp only [Element.render, leading, trailing, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        String.toList_append, String.toList_ofList, join_toList, List.flatMap_map,
        escape_toList, attributes, List.append_assoc]
      rfl

theorem children_cons (child : Element) (children : List Element) (depth : Nat)
    (head rest : List Char)
    (h : (child.render depth).toList = head)
    (t : (children.flatMap fun c => (c.render depth).toList) = rest) :
    ((child :: children).flatMap fun c => (c.render depth).toList) = head ++ rest := by
  simp only [List.flatMap_cons, h, t]

theorem node (e : Element) (depth : Nat) (head body tail : List Char)
    (h : leading e depth = head)
    (b : (e.children.flatMap fun c => (c.render (depth + 1)).toList) = body)
    (t : trailing e depth = tail) :
    (e.render depth).toList = head ++ body ++ tail := by
  rw [render_parts, h, b, t]

def header : List Char := "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n".toList

theorem document (e : Element) (body : List Char) (h : (e.render 0).toList = body) :
    (XML.document e).toList = header ++ body := by
  simp only [XML.document, String.toList_append, header, h]

theorem children_valid_cons (child : Element) (children : List Element)
    (h : child.valid = true) (t : (children.map Element.valid).all id = true) :
    ((child :: children).map Element.valid).all id = true := by
  simp only [List.map_cons, List.all_cons, id_eq, h, t, Bool.and_self]

theorem node_valid (e : Element)
    (h : decide (Name e.name ∧ AttributesValid e.attributes ∧ Text e.text ∧
      (e.text = "" ∨ e.children = [])) = true)
    (b : (e.children.map Element.valid).all id = true) : e.valid = true := by
  cases e
  rw [Element.valid, h, b]
  rfl

end XML.Certificate

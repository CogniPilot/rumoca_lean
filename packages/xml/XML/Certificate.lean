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

/-! Fragment decomposition. Each element's rendered document is the flattening of
a pre-order list of small character pieces: its own opening piece, then each
child's fragment list, then its own closing piece. This lets an actual-byte
certificate bind every fragment to a bounded literal and join the fragments
against a block-structured input by cursor equalities, rather than reducing the
whole document in one kernel step. -/

/-- The pre-order list of an element's own and its descendants' character
pieces. Flattening it yields the element's rendered characters. -/
def pieces (e : Element) (depth : Nat) : List (List Char) :=
  match e with
  | ⟨name, attrs, children, text⟩ =>
    leading ⟨name, attrs, children, text⟩ depth ::
      ((children.map fun c => pieces c (depth + 1)).flatten ++ [trailing ⟨name, attrs, children, text⟩ depth])

theorem render_pieces (e : Element) (depth : Nat) :
    (e.render depth).toList = (pieces e depth).flatten := by
  refine Element.rec
    (motive_1 := fun e => ∀ depth, (e.render depth).toList = (pieces e depth).flatten)
    (motive_2 := fun es => ∀ depth,
      (es.flatMap fun c => (c.render depth).toList) = ((es.map fun c => pieces c depth).flatten).flatten)
    ?_ ?_ ?_ e depth
  · intro name attrs children value ih depth
    rw [render_parts, ih (depth + 1)]
    simp only [pieces, List.flatten_cons, List.flatten_append, List.flatten_nil, List.append_nil,
      List.append_assoc]
  · intro depth; rfl
  · intro c cs ihc ihcs depth
    simp only [List.flatMap_cons, List.map_cons, List.flatten_cons, List.flatten_append,
      ihc depth, ihcs depth]

/-- Prepend the document header piece to the root element's piece list. -/
def documentPieces (e : Element) : List (List Char) := header :: pieces e 0

theorem document_pieces (e : Element) :
    (XML.document e).toList = (documentPieces e).flatten := by
  rw [documentPieces, List.flatten_cons]
  exact document e _ (render_pieces e 0)

theorem pieces_children_cons (c : Element) (children : List Element) (depth : Nat)
    (head rest : List (List Char))
    (h : pieces c depth = head) (t : (children.map fun c => pieces c depth).flatten = rest) :
    ((c :: children).map fun c => pieces c depth).flatten = head ++ rest := by
  simp only [List.map_cons, List.flatten_cons, h, t]

theorem pieces_node (e : Element) (depth : Nat)
    (lead trail : List Char) (childPieces : List (List Char))
    (hl : leading e depth = lead) (ht : trailing e depth = trail)
    (hc : (e.children.map fun c => pieces c (depth + 1)).flatten = childPieces) :
    pieces e depth = lead :: (childPieces ++ [trail]) := by
  obtain ⟨name, attrs, children, text⟩ := e
  simp only [pieces, hl, ht, hc]

theorem documentPieces_eq (e : Element) (headerPiece : List Char) (rest : List (List Char))
    (hh : header = headerPiece) (hp : pieces e 0 = rest) :
    documentPieces e = headerPiece :: rest := by
  rw [documentPieces, hh, hp]

/-- Bind an element's document string to a byte list from a proof that the
element's piece list equals a chunk list and that the chunks flatten to the
bytes. Neither side reduces the whole document; the chunk equalities and their
join are supplied separately. -/
theorem document_ofList (e : Element) (chunks : List (List Char)) (bytes : List Char)
    (hpieces : documentPieces e = chunks) (joined : chunks.flatten = bytes) :
    XML.document e = String.ofList bytes := by
  apply String.toList_injective
  rw [document_pieces, hpieces, joined, String.toList_ofList]

end XML.Certificate

import Std

namespace XML

def escapeChar (c : Char) : String :=
  match c with
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;"
    | '"' => "&quot;" | '\'' => "&apos;" | c => String.singleton c

def escape (s : String) : String := String.join (s.toList.map escapeChar)

structure Element where
  name : String
  attributes : List (String × String) := []
  children : List Element := []
  text : String := ""
  deriving Repr

def Element.render (e : Element) (depth : Nat := 0) : String := match e with
  | ⟨name, attributes, children, text⟩ =>
  let indent := String.ofList (List.replicate (depth * 2) ' ')
  let attrs := String.join (attributes.map fun (k, v) => " " ++ k ++ "=\"" ++ escape v ++ "\"")
  if children.isEmpty then
    if text.isEmpty then indent ++ "<" ++ name ++ attrs ++ "/>\n"
    else indent ++ "<" ++ name ++ attrs ++ ">" ++ escape text ++ "</" ++ name ++ ">\n"
  else indent ++ "<" ++ name ++ attrs ++ ">\n" ++
    escape text ++
    String.join (children.map fun c => c.render (depth + 1)) ++
    indent ++ "</" ++ name ++ ">\n"

def document (root : Element) : String := "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ root.render

end XML

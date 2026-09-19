import Std

/-! Shared emission of kernel-checked source-text representations. This only
prepares proof terms; accepting them still requires ordinary Lean checking. -/
namespace Parser.EBNF.Emission

/-- Split a source text into newline-aligned character blocks near a target
size. Every block after the first begins with a newline, which is always a
top-level lexical separator (it closes a line comment and never extends an
identifier). Both the character-view certificate and the lexer certificate use
this shared split so a block boundary is a clean token boundary, letting each
block be certified on its own and composed. -/
def sourceBlocks (source : String) (target : Nat := 256) : Array (List Char) := Id.run do
  let chars := source.toList
  let mut blocks : Array (List Char) := #[]
  let mut current : List Char := []
  let mut len : Nat := 0
  for c in chars do
    if c == '\n' && len ≥ target then
      blocks := blocks.push current.reverse
      current := [c]
      len := 1
    else
      current := c :: current
      len := len + 1
  if !current.isEmpty then
    blocks := blocks.push current.reverse
  return blocks

/-- Keep an exact source literal and certify its character view. The literal is
emitted as the concatenation of readable per-block string literals, and every
equality is composed from per-block facts so no single kernel term ranges over
the whole text. -/
def sourceCertificate (source : String) : String := Id.run do
  let blocks := sourceBlocks source
  let count := blocks.size
  let total := source.toList.length
  let charNames := (List.range count).map fun i => s!"sourceChars{i}"
  let charJoin := if count == 0 then "[]" else String.intercalate " ++ " charNames
  let mut text := ""
  -- The source stays one exact literal: downstream artifact certificates compare
  -- an embedded grammar literal against it by `rfl`, which needs a single-literal
  -- normal form rather than a concatenation.
  text := text ++ s!"def source : String := {repr source}\n\n"
  -- Newline-aligned character blocks, reused by the lexer certificate. Each block
  -- after the first begins with a newline, a top-level token boundary.
  for (block, i) in blocks.zipIdx do
    text := text ++ s!"def sourceChars{i} : List Char := {repr block}\n\n"
  text := text ++ s!"def sourceChars : List Char := {charJoin}\n\n"
  -- Relate the literal to its characters through `String.ofList`; the reverse
  -- `String.toList` of a literal is far more expensive to reduce in the kernel.
  text := text ++ "-- Guide elaboration only: all equalities are still kernel-checked.\n" ++
    "attribute [local irreducible] String.ofList\n\n"
  text := text ++ "theorem source_ofList : source = String.ofList sourceChars := by rfl\n\n"
  text := text ++ "theorem source_toList : source.toList = sourceChars := by\n" ++
    "  rw [source_ofList, String.toList_ofList]\n\n"
  -- Per-block lengths, summed compositionally rather than measured in one term.
  for (block, i) in blocks.zipIdx do
    text := text ++
      s!"theorem sourceChars{i}_length : sourceChars{i}.length = {block.length} := by decide\n\n"
  text := text ++ "set_option linter.unusedSimpArgs false in\n" ++
    s!"theorem source_length : source.toList.length = {total} := by\n"
  if count == 0 then
    text := text ++ "  rfl\n\n"
  else
    text := text ++ "  rw [source_toList]\n  unfold sourceChars\n" ++
      "  simp only [List.length_append, " ++
      String.intercalate ", " ((List.range count).map fun i => s!"sourceChars{i}_length") ++ "]\n\n"
  return text


end Parser.EBNF.Emission

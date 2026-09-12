import Std

/-! Shared emission of kernel-checked source-text representations. This only
prepares proof terms; accepting them still requires ordinary Lean checking. -/
namespace Parser.EBNF.Emission

/-- Keep an exact source literal and certify its character view. Chunking
keeps generated terms shallow. Prevent tactics in this generated namespace
from unfolding UTF-8 encoding unnecessarily; kernel reduction is unaffected. -/
def sourceCertificate (source : String) : String := Id.run do
  let chars := source.toList.toArray
  let chunks := (List.range ((chars.size + 63) / 64)).map fun i =>
    (chars.extract (64 * i) (64 * (i + 1))).toList
  let mut text := s!"def source : String := {repr source}\n\n"
  for (chunk, i) in chunks.zipIdx do
    text := text ++ s!"def sourceChars{i} : List Char := {repr chunk}\n\n"
  let indices := List.range chunks.length
  let charParts := String.intercalate " ++ " (indices.map fun i => s!"sourceChars{i}")
  text := text ++ s!"def sourceChars : List Char := {if chunks.isEmpty then "[]" else charParts}\n\n" ++
    "-- Guide elaboration only: all equalities are still kernel-checked.\n" ++
    "attribute [local irreducible] String.ofList\n\n" ++
    "theorem source_ofList : source = String.ofList sourceChars := by rfl\n\n" ++
    "theorem source_toList : source.toList = sourceChars := by\n" ++
    "  rw [source_ofList, String.toList_ofList]\n\n" ++
    s!"theorem source_length : source.toList.length = {chars.size} :=\n" ++
    "  (congrArg List.length source_toList).trans (by decide +kernel)\n\n"
  return text


end Parser.EBNF.Emission

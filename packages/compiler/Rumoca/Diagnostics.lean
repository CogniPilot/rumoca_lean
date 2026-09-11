import ModelicaParser.LocatedParser
import Lean.Data.Json.FromToJson.Basic
import Lean.Data.Position

open _root_.Parser

/-! Terminal presentation is separate from the structured source diagnostic.
LSP clients consume Parser.Source.Diagnostic directly, with UTF-16 conversion at their
protocol boundary. This renderer never supplies positions to the parser. -/
namespace Rumoca.Diagnostics
open Lean

private def spanJson (span : Parser.Source.Span source) : Json :=
  Json.mkObj [("startByte", Lean.toJson span.start.offset.byteIdx),
    ("endByte", Lean.toJson span.stop.offset.byteIdx)]

/-- Plain structured data for CLI automation. Offsets are half-open UTF-8
bytes in the caller's named source snapshot, not display columns. -/
def toJson (e : Parser.Source.Diagnostic source) : Json := Json.mkObj [
  ("phase", Lean.toJson e.phase),
  ("span", spanJson e.span),
  ("message", Lean.toJson e.message),
  ("related", Lean.toJson (e.related.map fun note => Json.mkObj [
    ("span", spanJson note.span), ("message", Lean.toJson note.message)]))]

/-- Expand tabs and escape non-ASCII/control characters so caret placement is
independent of terminal width tables. The tiny source grammar is ASCII;
unsupported Unicode remains visible without executing terminal controls. -/
private def displayChar (c : Char) : String :=
  if c == '\t' then "    "
  else if ' ' ≤ c && c ≤ '~' then String.singleton c
  else "\\u{" ++ String.ofList (Nat.toDigits 16 c.val.toNat) ++ "}"

private def display (s : String) : String := String.join (s.toList.map displayChar)

private def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

private def lineText (lines : Array String) (line : Nat) : String :=
  let text := lines[line]?.getD ""
  if text.endsWith "\r" then (text.dropEnd 1).toString else text

/-- One line of context on either side, plus a precise range underline. A
multi-line span is marked through the first line and names its final endpoint. -/
private def renderAt (name : String) (span : Parser.Source.Span source)
    (heading : String) : String := Id.run do
  let fileMap := FileMap.ofString source
  let start := fileMap.toPosition span.start.offset
  let stop := fileMap.toPosition span.stop.offset
  let lines := (source.splitOn "\n").toArray
  let line := start.line - 1
  let text := lineText lines line
  let before := display (String.ofList (text.toList.take start.column))
  let stopColumn := if stop.line == start.line then stop.column else text.length
  let marked := display (String.ofList ((text.toList.drop start.column).take (stopColumn - start.column)))
  let width := (toString (min (line + 2) lines.size)).length
  let gutter := spaces width
  let mut out := s!"{heading}\n --> {display name}:{start.line}:{start.column + 1}\n{gutter} |\n"
  for n in [line - 1 : min (line + 2) lines.size] do
    let number := toString (n + 1)
    out := out ++ s!"{spaces (width - number.length)}{number} | {display (lineText lines n)}\n"
    if n == line then
      let carets := String.ofList (List.replicate (max 1 marked.length) '^')
      out := out ++ s!"{gutter} | {spaces before.length}{carets}\n"
  if stop.line != start.line then
    out := out ++ s!"{gutter} = range continues to {stop.line}:{stop.column + 1}\n"
  return out.trimAsciiEnd.toString

/-- Primary and related ranges are rendered from the same checked snapshot. -/
def render (name : String) (e : Parser.Source.Diagnostic source) : String :=
  String.intercalate "\n" (renderAt name e.span s!"error[{e.phase}]: {e.message}" ::
    e.related.map fun note => renderAt name note.span s!"note: {note.message}")

end Rumoca.Diagnostics

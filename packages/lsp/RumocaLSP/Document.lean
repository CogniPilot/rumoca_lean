import ModelicaParser.LocatedParser
import Lean.Data.Lsp.Utf16
import Lean.Data.Lsp.Diagnostics

open _root_.Parser

/-! Immutable document snapshots, inspired by Lean's file-worker boundary.
Analysis is pure and file-local, ready to be scheduled by independent workers.
The first server processes requests serially and advertises full text sync. -/
namespace RumocaLSP
open Lean Rumoca

structure Document where
  uri : String
  version : Int
  source : String
  fileMap : FileMap
  source_matches : fileMap.source = source
  result : Except (Parser.Source.Diagnostic source) (LocatedParsed source)

def Document.create (uri : String) (version : Int) (source : String) : Document :=
  ⟨uri, version, source, ⟨source, (FileMap.ofString source).positions⟩,
    rfl, Rumoca.parseLocated source⟩

/-- An older or duplicated change must not replace a newer snapshot. -/
def Document.update (old : Document) (version : Int) (source : String) : Document :=
  if version > old.version then .create old.uri version source else old

theorem Document.update_stale (old : Document) (version : Int) (source : String)
    (h : version ≤ old.version) : old.update version source = old := by
  simp [update, Int.not_lt.mpr h]

theorem Document.update_version (old : Document) (version : Int) (source : String) :
    old.version ≤ (old.update version source).version := by
  unfold update
  split <;> simp_all [create] <;> omega

def Document.range (d : Document) (span : Parser.Source.Span d.source) : Lsp.Range :=
  d.fileMap.utf8RangeToLspRange ⟨span.start.offset, span.stop.offset⟩

def Document.diagnostic (d : Document) : Option (Parser.Source.Diagnostic d.source) :=
  match d.result with
  | .error e => some e
  | .ok p => match p.resolve with
    | .error e => some e
    | .ok _ => none

def Document.diagnostics (d : Document) (includeRelated : Bool := false) : Array Lsp.Diagnostic :=
  match d.diagnostic with
  | none => #[]
  | some e => #[{
      range := d.range e.span
      severity? := some .error
      source? := some "rumoca"
      message := e.message
      code? := some (.string e.phase)
      relatedInformation? := if !includeRelated || e.related.isEmpty then none else
        some (e.related.toArray.map fun note => {
          location := { uri := d.uri, range := d.range note.span }
          message := note.message }) }]

/-- Clients that do not advertise related-information support receive only
the primary diagnostic. The source diagnostic itself retains every note. -/
theorem Document.diagnostics_without_related (d : Document) :
    ∀ e ∈ d.diagnostics false, e.relatedInformation? = none := by
  unfold diagnostics
  split <;> simp

/-- No diagnostic means both the actual located parser and resolver succeeded. -/
theorem Document.quiet (d : Document) (h : d.diagnostic = none) :
    ∃ p, d.result = .ok p ∧ AST.Resolved p.parsed.ast := by
  unfold diagnostic at h
  cases hp : d.result with
  | error e => simp [hp] at h
  | ok p =>
    refine ⟨p, rfl, ?_⟩
    cases hr : p.resolve with
    | error e => simp [hp, hr] at h
    | ok resolved => exact resolved.down

private def contains (range : Parser.Source.Span source) (byte : Nat) : Bool :=
  range.start.offset.byteIdx ≤ byte && byte < range.stop.offset.byteIdx

/-- Only the four identifier occurrences in the admitted Modelica AST are
navigable. Mismatched names are diagnosed and never linked to a declaration. -/
def Document.identifier (d : Document) (position : Lsp.Position) : Option (Nat × Nat × String) := do
  let .ok p := d.result | none
  let some lineStart := d.fileMap.positions[position.line]? | none
  let lineStop := (d.fileMap.positions[position.line + 1]?).getD d.source.rawEndPos
  if position.character > lineStop.byteIdx - lineStart.byteIdx then none else do
  let byte := (d.fileMap.lspPosToUtf8Pos position).byteIdx
  if d.fileMap.utf8PosToLspPos ⟨byte⟩ != position then none else do
  if contains (p.tokenSpan 1) byte then some (1, 1, s!"model {p.parsed.ast.name}")
  else if contains (p.tokenSpan 3) byte then some (3, 3, s!"Real {p.parsed.ast.state}\nState; der({p.parsed.ast.state}) = 1")
  else if contains (p.tokenSpan 8) byte && p.parsed.ast.derivativeName == p.parsed.ast.state then
    some (8, 3, s!"Real {p.parsed.ast.state}\nState; der({p.parsed.ast.state}) = 1")
  else if contains (p.tokenSpan 14) byte && p.parsed.ast.endName == p.parsed.ast.name then
    some (14, 1, s!"model {p.parsed.ast.name}")
  else none

def Document.definition (d : Document) (position : Lsp.Position) : Json :=
  match d.result, d.identifier position with
  | .ok p, some (_, target, _) => toJson ({ uri := d.uri, range := d.range (p.tokenSpan target) } : Lsp.Location)
  | _, _ => .null

def Document.hover (d : Document) (position : Lsp.Position) : Json :=
  match d.result, d.identifier position with
  | .ok p, some (index, _, label) => Json.mkObj [
      ("contents", Json.mkObj [("kind", "plaintext"), ("value", toJson label)]),
      ("range", toJson (d.range (p.tokenSpan index)))]
  | _, _ => .null

end RumocaLSP

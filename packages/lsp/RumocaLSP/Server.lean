import RumocaLSP.Document
import RumocaLSP.Sync
import Lean.Data.Lsp.Communication
import Lean.Data.Lsp.TextSync
import Lean.Data.Lsp.InitShutdown

/-! A small stdio LSP. Lean supplies protocol framing and JSON types. This
package never imports compiler backends or runs a proof build on an edit. -/
namespace RumocaLSP
open Lean hiding Message
open Lean.JsonRpc

structure State where
  initialized : Bool := false
  shutdown : Bool := false
  relatedInformation : Bool := false
  documents : Std.HashMap String Document := {}

private def publish (d : Document) (relatedInformation : Bool) : Message :=
  (⟨"textDocument/publishDiagnostics", {
    uri := d.uri, version? := some d.version, diagnostics := d.diagnostics relatedInformation
  }⟩ : Notification Lsp.PublishDiagnosticsParams)

private def warning (message : String) : Message :=
  (⟨"window/logMessage", Json.mkObj [("type", toJson (2 : Nat)), ("message", toJson message)]⟩
    : Notification Json)

private def decode [FromJson α] (params : Option Json.Structured) : Except String α :=
  fromJson? (toJson params)

/-- Lean's initialize record omits this optional LSP capability. Read it from
the same request; missing or unrecognized values do not opt the client in. -/
private def supportsRelatedInformation (params : Option Json.Structured) : Bool :=
  let requested : Except String Bool := do
    let capabilities ← (toJson params).getObjVal? "capabilities"
    let document ← capabilities.getObjVal? "textDocument"
    let diagnostics ← document.getObjVal? "publishDiagnostics"
    diagnostics.getObjValAs? Bool "relatedInformation"
  requested.toOption.getD false

private def capabilities : Json := Json.mkObj [
  ("capabilities", Json.mkObj [
    ("positionEncoding", "utf-16"),
    ("textDocumentSync", Json.mkObj [("openClose", toJson true), ("change", toJson (1 : Nat))]),
    ("hoverProvider", toJson true), ("definitionProvider", toJson true)]),
  ("serverInfo", Json.mkObj [("name", "rumoca-lsp"), ("version", "0.1.0")])]

/-- A single pure dispatch step. Notifications never receive responses;
unsupported requests do. Only explicitly advertised features are handled. -/
def handle (s : State) (message : Message) : State × Array Message × Option UInt32 := Id.run do
  match message with
  | .request id method params =>
    if s.shutdown then
      return (s, #[.responseError id .invalidRequest "server has shut down" none], none)
    if method == "initialize" then
      if s.initialized then
        return (s, #[.responseError id .invalidRequest "already initialized" none], none)
      match decode (α := Lsp.InitializeParams) params with
      | .error e => return (s, #[.responseError id .invalidParams e none], none)
      | .ok _ =>
        let ready := { s with
          initialized := true
          relatedInformation := supportsRelatedInformation params }
        return (ready, #[.response id capabilities], none)
    if !s.initialized then
      return (s, #[.responseError id .serverNotInitialized "initialize first" none], none)
    if method == "shutdown" then
      return ({ s with shutdown := true }, #[.response id .null], none)
    if method == "textDocument/hover" || method == "textDocument/definition" then
      match decode (α := Lsp.TextDocumentPositionParams) params with
      | .error e => return (s, #[.responseError id .invalidParams e none], none)
      | .ok p =>
        let some d := s.documents[p.textDocument.uri]?
          | return (s, #[.response id .null], none)
        let result := if method == "textDocument/hover" then d.hover p.position else d.definition p.position
        return (s, #[.response id result], none)
    return (s, #[.responseError id .methodNotFound s!"unsupported method: {method}" none], none)
  | .notification method params =>
    if method == "exit" then return (s, #[], some (if s.shutdown then 0 else 1))
    if !s.initialized || s.shutdown then return (s, #[], none)
    if method == "textDocument/didOpen" then
      match decode (α := Sync.Open) params with
      | .error e => return (s, #[warning e], none)
      | .ok p =>
        let item := p.textDocument
        if s.documents.contains item.uri then
          return (s, #[warning "document is already open"], none)
        let d := Document.create item.uri item.version item.text
        return ({ s with documents := s.documents.insert item.uri d },
          #[publish d s.relatedInformation], none)
    if method == "textDocument/didChange" then
      match decode (α := Sync.Change) params with
      | .error e => return (s, #[warning e], none)
      | .ok p =>
        let some old := s.documents[p.textDocument.uri]?
          | return (s, #[warning "change for an unopened document"], none)
        let version := p.textDocument.version
        if version ≤ old.version then return (s, #[], none)
        let mut source := old.source
        for change in p.contentChanges do source := change.text
        if p.contentChanges.isEmpty then return (s, #[], none)
        let d := old.update version source
        return ({ s with documents := s.documents.insert d.uri d },
          #[publish d s.relatedInformation], none)
    if method == "textDocument/didClose" then
      match decode (α := Lsp.DidCloseTextDocumentParams) params with
      | .error e => return (s, #[warning e], none)
      | .ok p =>
        let clear : Notification Lsp.PublishDiagnosticsParams :=
          ⟨"textDocument/publishDiagnostics", { uri := p.textDocument.uri, diagnostics := #[] }⟩
        return ({ s with documents := s.documents.erase p.textDocument.uri }, #[clear], none)
    return (s, #[], none)
  | _ => return (s, #[], none)

/-- Transport and the operating system are tested infrastructure, not part of
compiler semantic preservation. Standard output contains protocol frames only. -/
def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let mut state : State := {}
  try
    repeat
      let message ← input.readLspMessage
      let (next, responses, exitCode) := handle state message
      state := next
      for response in responses do output.writeLspMessage response
      if let some code := exitCode then return code
    return 1
  catch e =>
    IO.eprintln s!"rumoca-lsp: {e}"
    return 1

end RumocaLSP

# Rumoca language server

A small Lean LSP for the existing Modelica unit-derivative grammar. It uses
the parser package's checked spans and name resolution, and reuses Lean's
JSON-RPC transport, LSP types, file maps and UTF-16 conversions.
The protocol reference is the
[LSP 3.17 specification](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/).

From `nix develop` at the repository root:

```sh
lake build rumoca-lsp       # native stdio server
lake build check-lsp        # package proofs and axiom audit
lake run frontend-test     # actual LSP session and parallel frontend checks
```

Configure an editor to launch the absolute path to
`packages/lsp/.lake/build/bin/rumoca-lsp`. Launch the binary directly: build
messages on stdout would corrupt the protocol. The Nix Neovim configuration
starts it for `.mo` files in this repository once the executable has been built.
Restart Neovim in the updated `nix develop` environment to load that configuration.

Supported: full-document open/change/close synchronization, diagnostics with
UTF-16 ranges, hover and go-to-definition for model/state identifiers,
initialization and shutdown. Document versions are signed integers; stale
changes cannot replace newer snapshots. There is no grammar expansion or
backend invocation on edits. The server is serial; parallel batch parsing is
available through `rumoca parse --jobs N FILES...` and `ModelicaParser.Parallel`.

The pure snapshot update and diagnostic properties have Lean proofs.
Protocol I/O and Lean's file-map/UTF-16 implementation are tested infrastructure.
This is not a proof of the complete LSP protocol or an incremental/workspace
language server. See [scope and remaining provenance work](../../dev/provenance.md).

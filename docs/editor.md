# Lean in Neovim

Enter a fresh development shell and open a Lean source file:

```sh
nix develop
nvim packages/compiler/Rumoca/Lowering.lean
```

The default shell provides Neovim, `lean.nvim`, its dependencies and the
Tokyo Night theme from the existing pinned nixpkgs input. Lean/Lake remain
4.29.1, selected through Nix's Elan and `lean-toolchain`. The editor includes Lean
syntax highlighting, LSP semantic highlighting, diagnostics, completion, Unicode
abbreviations and an interactive goal infoview. Nix supplies the editor plugins;
Elan downloads the pinned Lean release on first use if it is not installed.

The Nix wrapper uses [nix/init.lua](../nix/init.lua) and does not edit your
personal Neovim configuration. `EDITOR` and `VISUAL` select this wrapper inside
the shell. An already running Neovim or an older development shell keeps its
old configuration: close it and enter `nix develop` again. The separate
`nix develop .#verification` shell deliberately remains a minimal CI environment.

| Key / command | Action |
| --- | --- |
| `Space i` | Toggle the Lean goal infoview |
| `Space Tab` | Jump to the infoview |
| `K` | Lean hover/type information |
| `gd` / `gr` | Definition / references |
| `Space ca` | Code actions |
| `Space e` | Diagnostic details |
| `Ctrl-Space`, then `Ctrl-n` / `Ctrl-p`, `Ctrl-y` | Request, select and accept completion |
| `\forall`, `\to` followed by space | Enter `∀`, `→` using Lean abbreviations |
| `Space r` | Restart Lean for the current file |
| `:checkhealth lean` | Lean plugin health information |

The language server uses the enclosing Git/Lake workspace, including when
editing sources in any of the four packages, so it sees the root dependency cache and
package build outputs. Build changed dependencies with `lake build`, then
restart the Lean file if its imports are out of date.

If highlighting is missing, verify `:set filetype? syntax?` reports `lean` for
both, `:echo g:colors_name` reports `tokyonight-night`, and
`:lua print(vim.inspect(vim.lsp.get_clients({bufnr=0})))` includes `leanls`.
Immediate syntax coloring works before the LSP finishes; semantic coloring
requires a working server and elaborated imports.

The reproducible integration check opens a real package file, checks colored
syntax groups, initializes Lean's LSP and requests nonempty semantic tokens:

```sh
nix develop --command nvim --headless '+luafile nix/check-editor.lua'
```

Configuration follows the [lean.nvim documentation](https://github.com/Julian/lean.nvim)
and the packaged plugin's Lake server integration. Proof checking still happens
in Lean; editor presentation does not change the compiler's verification gate.

## Modelica language server

Build `lake build rumoca-lsp` in `nix develop`. The repository's Neovim
configuration starts the resulting stdio executable for `.mo` files after
re-entering the updated shell and restarting the editor. The server provides
source-range diagnostics, hover and go-to-definition for the tiny supported
Modelica grammar. It shares the parser with the compiler and does not run
backend builds on edits. `gd` uses definition lookup and `<leader>e` displays
the diagnostic. See [the LSP package](../packages/lsp/README.md) for protocol
scope and [frontend provenance](../dev/provenance.md) for proof boundaries.

Command-line errors show file/line/column, source context and an underline.
`rumoca parse --json FILES...` returns structured diagnostics with a `span`
containing `startByte` and `endByte`; these are UTF-8 bytes. The LSP receives
structured diagnostics with UTF-16 ranges, never formatted terminal text.

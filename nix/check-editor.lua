-- Run inside `nix develop`: nvim --headless '+luafile nix/check-editor.lua'
-- This exercises a real Lean buffer and server, not just plugin installation.
local function check()
  vim.cmd.edit('packages/compiler/Rumoca/Compiler.lean')
  local buffer = vim.api.nvim_get_current_buf()
  assert(vim.bo[buffer].filetype == 'lean', 'Lean filetype was not detected')
  assert(vim.bo[buffer].syntax == 'lean', 'Lean syntax was not enabled')
  assert(vim.fn.synIDattr(vim.fn.synID(1, 1, 1), 'name') == 'leanCommand', 'Lean import keyword has no syntax group')
  assert(vim.api.nvim_get_hl(0, { name = 'leanCommand', link = false }).fg, 'Lean keyword has no color')
  assert(vim.fn.exists(':LeanInfoviewToggle') == 2, 'Lean infoview commands are missing')
  local client
  assert(vim.wait(45000, function()
    client = vim.lsp.get_clients({ bufnr = buffer, name = 'leanls' })[1]
    return client and client.initialized
  end, 100), 'Lean LSP did not attach and initialize')
  assert(client.config.root_dir == vim.uv.cwd(), 'LSP did not select the enclosing Lake workspace')
  assert(client:supports_method('textDocument/hover'), 'Lean hover is unavailable')
  assert(client:supports_method('textDocument/completion'), 'Lean completion is unavailable')
  assert(client:supports_method('textDocument/semanticTokens/full'), 'Lean semantic highlighting is unavailable')
  -- This buffer imports both frontend and backend packages. Ask Lean for
  -- semantic tokens to confirm imports elaborate through the shared workspace.
  local response = client:request_sync('textDocument/semanticTokens/full', {
    textDocument = { uri = vim.uri_from_bufnr(buffer) },
  }, 45000, buffer)
  assert(response and not response.err and response.result, 'Lean semantic-token request failed: ' .. vim.inspect(response))
  assert(response.result.data and #response.result.data > 0, 'Lean returned no semantic highlighting tokens')
  print('Editor passed: Lean syntax colors, workspace LSP, semantic tokens, infoview, completion=' .. tostring(client:supports_method('textDocument/completion')))
  client:stop(true)
end
local ok, err = pcall(check)
if not ok then
  io.stderr:write(tostring(err) .. '\n')
  vim.cmd('cquit 1')
end
vim.cmd('qa!')

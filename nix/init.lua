-- Project editor, packaged by Nix. No plugin downloads at startup.
vim.g.mapleader = ' '
vim.g.maplocalleader = ' '
vim.opt.termguicolors = true
vim.opt.number = true
vim.opt.signcolumn = 'yes'
vim.opt.updatetime = 250
vim.opt.expandtab = true
vim.opt.shiftwidth = 2
vim.opt.softtabstop = 2
vim.opt.ignorecase = true
vim.opt.smartcase = true
vim.opt.completeopt = { 'menu', 'menuone', 'noselect' }
vim.cmd('filetype plugin indent on')
vim.cmd('syntax enable')
require('tokyonight').setup({ style = 'night' })
vim.cmd.colorscheme('tokyonight')

-- Use the enclosing Lake workspace when editing package sources.
-- Standalone Lean projects still use their own lakefile/toolchain root.
vim.lsp.config('leanls', {
  root_dir = function(bufnr, on_dir)
    local name = vim.api.nvim_buf_get_name(bufnr)
    local repo = vim.fs.root(name, '.git')
    if repo and (vim.uv.fs_stat(repo .. '/lakefile.toml') or vim.uv.fs_stat(repo .. '/lakefile.lean')) then
      on_dir(repo)
    else
      on_dir(vim.fs.root(name, { 'lakefile.toml', 'lakefile.lean', 'lean-toolchain' }))
    end
  end,
})
require('lean').setup({ mappings = true })

-- The Modelica server is a local Lake product, built independently of Nix.
-- Start its binary directly: build output must never enter the LSP stream.
vim.filetype.add({ extension = { mo = 'modelica' } })
vim.lsp.config('rumoca', {
  filetypes = { 'modelica' },
  root_dir = function(bufnr, on_dir)
    local repo = vim.fs.root(vim.api.nvim_buf_get_name(bufnr), '.git')
    if repo and vim.fn.executable(repo .. '/packages/lsp/.lake/build/bin/rumoca-lsp') == 1 then
      on_dir(repo)
    end
  end,
  cmd = function(dispatchers, config)
    return vim.lsp.rpc.start({ config.root_dir .. '/packages/lsp/.lake/build/bin/rumoca-lsp' },
      dispatchers, { cwd = config.root_dir })
  end,
})
vim.lsp.enable('rumoca')

vim.diagnostic.config({ severity_sort = true, underline = true, virtual_text = false })
vim.api.nvim_create_autocmd('LspAttach', {
  callback = function(args)
    local client = vim.lsp.get_client_by_id(args.data.client_id)
    if not client or (client.name ~= 'leanls' and client.name ~= 'rumoca') then return end
    local opts = { buffer = args.buf }
    vim.keymap.set('n', 'gd', vim.lsp.buf.definition, opts)
    vim.keymap.set('n', 'gr', vim.lsp.buf.references, opts)
    vim.keymap.set('n', '<leader>ca', vim.lsp.buf.code_action, opts)
    vim.keymap.set('n', '<leader>e', vim.diagnostic.open_float, opts)
    if client:supports_method('textDocument/completion') then
      vim.lsp.completion.enable(true, client.id, args.buf, { autotrigger = true })
      vim.keymap.set('i', '<C-Space>', vim.lsp.completion.get, opts)
    end
  end,
})

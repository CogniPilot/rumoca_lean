{ pkgs }:
pkgs.wrapNeovimUnstable pkgs.neovim-unwrapped {
  plugins = with pkgs.vimPlugins; [ lean-nvim tokyonight-nvim ];
  luaRcContent = builtins.readFile ./init.lua;
  # Use the shell's pinned Lean/Lake even when launched through $EDITOR.
  wrapperArgs = [ "--prefix" "PATH" ":" (pkgs.lib.makeBinPath [ pkgs.lean4 pkgs.ripgrep ]) ];
}

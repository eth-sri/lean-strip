#!/bin/sh
# Install the lean-strip command.
#
#   curl -LsSf https://raw.githubusercontent.com/eth-sri/lean-strip/main/install.sh | sh
#
# Installs uv if it is missing, then installs lean-strip as an isolated uv tool
# with its own Python. Set LEAN_STRIP_SOURCE to install from another location
# (a git URL, a local checkout of this repository, or a wheel).
set -eu

LEAN_STRIP_SOURCE="${LEAN_STRIP_SOURCE:-git+https://github.com/eth-sri/lean-strip}"

say() { printf 'lean-strip installer: %s\n' "$*"; }

if ! command -v uv >/dev/null 2>&1; then
    say "uv not found; installing it (https://docs.astral.sh/uv/)"
    if command -v curl >/dev/null 2>&1; then
        curl -LsSf https://astral.sh/uv/install.sh | sh
    else
        wget -qO- https://astral.sh/uv/install.sh | sh
    fi
    # The uv installer puts uv in ~/.local/bin (or $XDG_BIN_HOME / $CARGO_HOME/bin).
    PATH="${XDG_BIN_HOME:-$HOME/.local/bin}:${CARGO_HOME:-$HOME/.cargo}/bin:$PATH"
    export PATH
fi

say "installing from $LEAN_STRIP_SOURCE"
uv tool install --force --python 3.12 "$LEAN_STRIP_SOURCE"

if ! command -v lean-strip >/dev/null 2>&1; then
    say "lean-strip is installed in $(uv tool dir --bin), which is not on PATH yet"
    say "run 'uv tool update-shell' (or open a new shell) to fix that"
fi

if ! command -v lake >/dev/null 2>&1; then
    say "note: lean-strip drives Lake, which was not found on PATH. Install Lean with elan:"
    say "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
fi

say "done. Run 'lean-strip' inside a repository containing comparator.json ('lean-strip --help')."

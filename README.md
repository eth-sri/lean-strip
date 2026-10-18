# lean-strip

`lean-strip` removes the Lean code that a repository's main results do not need. It is the preprocessing step of the LeanLean benchmark, packaged as one command, and it works on any repository in the [Palomar registry](https://palomar-registry.org).

It works on a Palomar-registry style repository: a Lake project with a comparator config (usually `comparator.json`) and the solution and challenge modules it names.

## Install

```sh
curl -LsSf https://raw.githubusercontent.com/eth-sri/lean-strip/main/install.sh | sh
```

The installer installs [uv](https://docs.astral.sh/uv/) if needed, then installs `lean-strip` as an isolated uv tool with its own Python. You also need Lean (`elan`/`lake`) on your `PATH`. It runs on Linux and macOS.

With uv already installed, either of these works:

```sh
uv tool install git+https://github.com/eth-sri/lean-strip           # permanent `lean-strip` command
uvx --from git+https://github.com/eth-sri/lean-strip lean-strip     # one-off run
uv tool upgrade lean-strip                                          # update
```

## Use

```sh
cd my-palomar-repo      # contains comparator.json, Solution.lean, Challenge.lean
lean-strip              # or: lean-strip --dry-run
```

Steps:

1. **Build.** Reuses a fresh `.lake` build, or runs `lake exe cache get` and `lake build +Solution`.
2. **Isolate.** Copies the project to `.lean-strip/work` and drops Lean files outside the solution/challenge import closure.
3. **Strip.** Builds a dependency graph from `.olean`, `.ilean` and source, removes the modules and declarations the protected theorems do not need, and rebuilds the stripped tree.
4. **Check the challenge.** Elaborates the challenge against the stripped tree.
5. **Check the lakefile.** If the lakefile names a module the strip deleted, makes the smallest edit that fixes it, with a warning.
6. **Run comparator.** Runs Palomar's comparator on the stripped tree with the repository's config. If it rejects the tree, nothing is applied.
7. **Apply.** Rewrites the repository's `.lean` files, deletes the unneeded ones and writes the lakefile edit, if any.

By default `lean-strip` changes only `.lean` files, plus the lakefile when it must, and keeps the originals in `.lean-strip/original/`. It prints how much it removed, and writes the full record to `.lean-strip/report.json` and `.lean-strip/log.txt`.

The comparator config is found automatically when the repository has exactly one (`comparator*.json`, or any JSON file naming a `solution_module` and a `challenge_module`); with several, `lean-strip` asks.

### Flags

- `--comparator PATH`: the comparator config to use.
- `--retain-lean-only`: also delete every file the Lean build does not need, such as READMEs, docs, scripts and CI; the challenge, the comparator config, the Lake files and files the Lean code reads stay. This is the layout of the LeanLean dataset.
- `--dry-run`: strip in `.lean-strip/work` only and leave the repository untouched.
- `--force`: run over uncommitted `.lean` or lakefile changes (any changes with `--retain-lean-only`).
- `--skip-comparator`: do not run comparator.
- `--clean-certify`: also rebuild the stripped tree from an empty `.lake/build`.
- `--container [podman|docker]`: run inside a container; the repository is mounted, not copied.
- `--memory SIZE`, `--cpus N`: with `--container`, limit memory (no swap) and CPUs.
- `--image IMAGE`: with `--container`, the image to run in (default: built on first use).
- `--jobs N`: Lean threads and parallel files (default 8, or `--cpus`).
- `--timeout SECONDS`: per-command timeout (default 21600).
- `--keep-work`: keep `.lean-strip/work` after a successful run.
- `--quiet`: print only the final summary.

`lean-strip` builds and runs the repository's code, so run untrusted repositories with `--container`. Where comparator's `bwrap` sandbox cannot start (Ubuntu's AppArmor default), comparator runs without it.

### What is kept

Everything the protected theorems depend on, by Lean's compiled terms, its `.ilean` references and the source text, plus what is used without being named:

- every declaration with an attribute, and every target of an `attribute` command;
- declarations an `attribute` command generates, such as the `_assoc` lemma of `attribute [reassoc] foo`;
- instances, macros, syntax, notation, elaborators, simprocs, unification hints and other `meta` declarations;
- names used in `run_cmd`, `run_elab` and `run_meta`;
- targets of `open … hiding` and `open … renaming`, and namespaces a surviving `open` needs;
- the project's own copies of declarations that a dependency also declares.

Files that declare the same full name as another file, and files whose `grind +suggestions` calls cannot be pinned to explicit lemmas, are kept whole. Path dependencies (vendored packages) are never changed.

### How files are edited

Lean re-elaborates every file the strip changes and reports each command's extent and what its names resolve to, so a dropped declaration goes with its whole command, and an `open`, `variable` or `attribute` goes only when it names something deleted.

### When the stripped tree does not build

`lean-strip` raises the heartbeat limit of a declaration that times out, silences the `privateModule` linter, or restores a file where `grind` fails; any other error fails the run, with the errors in `.lean-strip/diagnostics/`. A run that needed a repair reports `repaired`.

## License

MIT; see [LICENSE](LICENSE).

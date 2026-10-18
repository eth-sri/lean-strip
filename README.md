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
2. **Clean.** Copies the project to `.lean-strip/work` and drops Lean files outside the solution/challenge import closure.
3. **Strip.**
   - normalizes `grind +suggestions` calls;
   - builds a dependency graph from `.olean`, `.ilean` and source;
   - prunes modules and declarations, editing each changed file from Lean's own view of it (see [How files are edited](#how-files-are-edited));
   - restores the original `grind` calls;
   - rebuilds the stripped tree (from a clean `.lake/build` too with `--clean-certify`).
4. **Check the challenge.** Elaborates the challenge against the stripped tree.
5. **Check the lakefile.** If the lakefile names a module the strip deleted (say the umbrella `Foo.lean` of `lean_lib Foo`, or the root of a `lean_exe`), it plans the smallest edit that fixes it: the library builds its surviving submodules (`Foo.+`) instead, and an executable whose root is gone is removed. It then runs a plain `lake build` on the stripped tree with that lakefile.
6. **Run comparator.** Judges the stripped tree with the comparator config, the way Palomar does: every named theorem must still prove the challenge's statement, use only the permitted axioms and pass the kernel checks. If comparator rejects the stripped tree, nothing is applied. Lean v4.35.0-rc2 and later ship the judge as `lake comparator`. For older toolchains `lean-strip` uses Palomar's earlier judge: the standalone [comparator](https://github.com/leanprover/comparator) at the commit Palomar pinned, [`lean4export`](https://github.com/leanprover/lean4export) at the release of the project's Lean version (for a patch release without one, such as v4.33.1, the line's `.0` release rebuilt with the project's toolchain, as Palomar did), and the nanoda kernel when the config enables it. These are built once into `$XDG_CACHE_HOME/lean-strip/comparator-tools` (nanoda needs Rust; if `cargo` is missing, a minimal Rust toolchain is installed there too). `--skip-comparator` skips this step.
7. **Apply.** Rewrites the repository's `.lean` files, deletes the unneeded ones and writes the lakefile edit, if any.

By default `lean-strip` changes only `.lean` files, plus the lakefile when it must. It prints a warning naming each lakefile change, and another if plain `lake build` still fails afterwards. It never touches the challenge file, READMEs, the comparator config or anything else. It refuses to run over uncommitted `.lean` changes unless you pass `--force`, and it keeps the originals in `.lean-strip/original/`.

`--retain-lean-only` keeps only what the Lean build needs. This is the layout of the LeanLean dataset. It also deletes every other file, such as READMEs, licenses, docs, scripts and CI config. It keeps the surviving Lean sources, the challenge, the comparator config, the lakefile, `lean-toolchain`, `lake-manifest.json`, `.gitignore` and any file the Lean code reads. Git-ignored files stay. With this flag it refuses to run over any uncommitted change unless you pass `--force`. Deleted files are moved to `.lean-strip/original/`.

The comparator config is found automatically when the repository has exactly one: a `comparator*.json`, or any JSON file naming a `solution_module` and a `challenge_module`. With several, `lean-strip` asks, or takes `--comparator path/to/config.json`.

### Bounding memory and CPUs

```sh
lean-strip --container --memory 64g --cpus 8 --retain-lean-only
```

`--container` runs the same command inside a container, using podman if it is installed and docker otherwise. The container only bounds resources, through `--memory` (no swap beyond it) and `--cpus` (also the default `--jobs`). The repository is mounted at its own path and the run uses your user ID, so the result lands in the repository exactly as without `--container`. On Linux the container reuses your elan toolchains. The Mathlib cache is shared through `$XDG_CACHE_HOME` (default `~/.cache`). The small runtime image (Python, git, curl, a C compiler, elan) is built on first use; pass `--image` to use your own.

At the end it prints how many files, lines, Lean tokens and words it removed, split into isolation and stripping. It also lists the dropped declarations by kind and file. The full record is in `.lean-strip/report.json` and `.lean-strip/log.txt`.

### How files are edited

What to keep is decided from Lean's data; the edits are made in the source text. Before editing, `lean-strip` has Lean re-elaborate every file the strip changes, against the already built imports and with the options Lake compiled it with. Lean reports each command's exact extent and kind, the namespace, `open`s and `variable`s in scope, and the declarations its names denote, an overloaded name included, as Lean resolved it. From that:

- a dropped declaration goes with its whole command: attributes, doc comment, `set_option … in` or `open … in` prefixes, and a `mutual … end` block once all its members go; `namespace`, `section` and `end` stay;
- an `attribute`, `export` or `open Foo (…)` target goes when the declaration it names was dropped;
- an `open` loses a namespace when no declaration of any namespace Lean resolved it to survives (and none is imported or holds `export` aliases), also before `in`;
- a `variable` binder goes when its type uses a dropped declaration (or a binder that went), and the `include`/`omit` that name it go with it;
- `#check`, `#print`, `#reduce` and `#synth` go; `#eval`, `#guard` and project or `#`-style check commands go when they name a dropped declaration;
- a module that keeps no declaration becomes its header, exactly as written.

Proofs of theorems are not replayed (`debug.byAsSorry`), since nothing after a theorem depends on its proof, and nothing goes through the kernel; files run in parallel, `--jobs` at a time. On a repository with a few hundred changed files this takes a few minutes, about as long as the final build. A file Lean cannot analyse here (an import or elaboration error, or a timeout, by default 30 minutes, `LEAN_STRIP_LEAN_SYNTAX_TIMEOUT`) is edited by the older textual rules instead. `LEAN_STRIP_NO_LEAN_SYNTAX=1` uses the textual rules for every file. `report.json` records the analysis under `engine_report.lean_syntax` and the files edited each way under `engine_report.strip`.

### When the strip is not certain

The strip decides what to keep from Lean's compiled terms, `.ilean` references and the source text, and then rebuilds the stripped tree to certify it. If that build fails, `lean-strip` repairs only the errors a correct strip can cause, and rebuilds after each round:

1. A declaration that runs out of heartbeats gets twice the limit, as `set_option maxHeartbeats … in` (or `synthInstance.maxHeartbeats` for type-class search) on that declaration only, up to 8× Lean's default. It elaborates more slowly once other declarations are gone.
2. A file stripped down to private declarations gets `set_option linter.privateModule false`.
3. A file where `grind` fails is restored unstripped. `grind +suggestions` picks lemmas from the environment, so a smaller environment can change what it finds.

Any other error means the strip missed a dependency, and the run fails at `final_warm_build`. Nothing is restored or kept to hide it. A run that needed a repair has status `repaired` instead of `stripped`; the summary lists each repair, and `report.json` records them under `build_fallback`. When the run fails, `.lean-strip/diagnostics/` holds the errors no repair applies to (`build-fallback.json`), the strip plan (`strip-plan.json`) and the failing build's full output (`failed-final-build.log`). Set `LEAN_STRIP_NO_BUILD_FALLBACK=1` to stop at the first failing build without any repair.

Other situations it handles on its own:

- **Vendored dependencies.** Packages the lakefile requires by a path inside the repository (`path = "vendor/Foo"`) are dependencies. They are never isolated, stripped, measured or deleted. Protected names they provide need no special treatment.
- **Thread failures.** Lean reserves 1 GiB of address space for every thread's stack and keeps a thread alive for each command of the file it compiles. Under an address-space limit (`ulimit -v`), a file with a hundred-odd commands therefore fails with "failed to create thread" while using little memory. When that happens, `lean-strip` retries the build with smaller stacks (256, 64, then 16 MiB, through `lean --tstack`) and finally with fewer threads. The smaller stacks are applied by a small wrapper toolchain under `$XDG_CACHE_HOME/lean-strip/lean-stacks/` that it puts first on `PATH`.
- **No sandbox for comparator.** `lake comparator` builds the solution in a `bwrap` sandbox, which needs unprivileged user namespaces (Ubuntu's AppArmor blocks them by default, and so do containers). Where the sandbox cannot start, `lean-strip` runs comparator with `--inadvisably-no-sandbox`; the standalone comparator always runs with its own `landrun` passthrough. `lean-strip` has already built the same code without a sandbox, so a sandbox would protect against nothing here. The summary says when the judge ran without one.
- **Several comparator configs or `Solution.lean` files.** Modules are resolved through Lake's source search path, exactly as Lean resolves them, never by matching file names.

## License

MIT; see [LICENSE](LICENSE).

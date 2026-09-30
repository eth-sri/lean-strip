# lean-strip

`lean-strip` removes the Lean code that a repository's main results do not need. It is the preprocessing step of the LeanLean benchmark, packaged as one command.

It works on a Palomar-registry style repository: a Lake project with `comparator.json` and the solution and challenge modules that file names.

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
3. **Strip.** Runs the exact benchmark preprocessing:
   - normalizes `grind +suggestions` calls;
   - builds a dependency graph from `.olean`, `.ilean` and source;
   - prunes modules and declarations;
   - restores the original `grind` calls;
   - rebuilds the stripped tree (from a clean `.lake/build` too with `--clean-certify`).
4. **Check the challenge.** Elaborates `Challenge.lean` against the stripped tree.
5. **Keep lakefile roots.** If the strip deleted a library root the lakefile names (say the umbrella `Foo.lean` of `lean_lib Foo`), it is kept as a stub that imports the surviving `Foo.*` modules, so plain `lake build` still works.
6. **Apply.** Rewrites the repository's `.lean` files and deletes the unneeded ones.

`lean-strip` changes only `.lean` files. It never touches the challenge file, the lakefile, READMEs, `comparator.json` or anything else. It refuses to run over uncommitted `.lean` changes unless you pass `--force`, and it keeps the originals in `.lean-strip/original/`.

`--retain-lean-only` goes further: it also deletes every file the Lean build does not need, such as READMEs, licenses, docs, scripts and CI config. It keeps the surviving Lean sources, the challenge, `comparator.json`, the lakefile, `lean-toolchain`, `lake-manifest.json`, `.gitignore` and any file the Lean code reads. Git-ignored files stay. With this flag it refuses to run over any uncommitted change unless you pass `--force`. Deleted files are moved to `.lean-strip/original/`.

### Reproducing the LeanLean benchmark

`--leanlean-benchmark` writes the repository exactly as the published LeanLean benchmark does. The Lean sources are the same either way. The mode changes three things around them:

- the lakefile's library roots are synchronized with the comparator's solution and challenge modules, instead of keeping import-only stubs for deleted roots;
- the non-Lean files are the ones the benchmark's asset rule keeps: root build metadata and files the retained Lean code refers to;
- the challenge file and the comparator config are removed from the tree (the benchmark ships them separately).

Two options reproduce per-repository details of the publication: `--lake-root-repair` also synchronizes the roots with every locally imported module, and `--asset-rule before-cleanup` uses the asset rule's earlier revision, which also counts paths mentioned in comments. `--leanlean-benchmark` replaces `--retain-lean-only`.

At the end it prints how many files, lines, Lean tokens and words it removed, split into isolation and stripping. It also lists the dropped declarations by kind and file. The full record is in `.lean-strip/report.json` and `.lean-strip/log.txt`.

## License

MIT; see [LICENSE](LICENSE).

"""Project module discovery and anonymous ``example`` command ranges."""

from __future__ import annotations

import re
import shlex
from typing import Any

from lean_strip._pipeline.preprocessing.olean import DeclRange


_DISCOVER_MODULES_CMD = (
    r"sources=$(find /testbed -path '*/.lake' -prune -o -type f -name '*.lean' -print); "
    r"find /testbed/.lake/build/lib -name '*.olean' "
    r"| while IFS= read -r file; do "
    r"rel=${file#/testbed/.lake/build/lib/}; rel=${rel#lean/}; "
    r"rel=${rel%.olean}; "
    "if test -f \"/testbed/${rel}.lean\" "
    "|| printf '%s\\n' \"$sources\" | grep -Fq \"/${rel}.lean\"; then "
    "printf './%s\\n' \"$rel\"; fi; "
    r"done | sort"
)


_LEAN_MODULE_COMPONENT_RE = re.compile(
    r"^[A-Za-z_À-￿][\wÀ-￿']*$"
)


def _module_name_from_olean_relpath(relative_path: str) -> str:
    """Render an olean/source relative path as an exact Lean module name."""

    components = relative_path.split("/")
    return ".".join(
        component
        if _LEAN_MODULE_COMPONENT_RE.fullmatch(component)
        else f"«{component}»"
        for component in components
    )


def discover_modules(env: Any) -> list[str]:
    """Return modules that have both a built ``.olean`` and a project source."""
    result = env.execute(_DISCOVER_MODULES_CMD)
    modules = [
        _module_name_from_olean_relpath(row.strip().removeprefix("./"))
        if row.strip().startswith("./")
        else row.strip()
        for row in result.get("output", "").strip().splitlines()
        if row.strip()
    ]
    return modules


_DUMP_ANONYMOUS_EXAMPLES_LEAN = r"""
import Lean
open Lean Elab Frontend

partial def containsExample (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Command.example || stx.getArgs.any containsExample

unsafe def main (paths : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let opts : Options :=
    Options.empty.insert `maxHeartbeats (DataValue.ofNat 0)
  for path in paths do
    enableInitializersExecution
    let input ← IO.FS.readFile path
    let inputCtx := Parser.mkInputContext input path
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (env, messages) ← processHeader header opts messages inputCtx
    if messages.hasErrors then
      IO.eprintln s!"header/import error while parsing {path}"
      for message in messages.toList do
        if message.severity == MessageSeverity.error then
          IO.eprintln (← message.toString)
      return 1
    let commandState := Command.mkState env messages opts
    let state ← IO.processCommands inputCtx parserState commandState
    if state.commandState.messages.hasErrors then
      IO.eprintln s!"elaboration error while parsing {path}"
      for message in state.commandState.messages.toList do
        if message.severity == MessageSeverity.error then
          IO.eprintln (← message.toString)
      return 1
    for command in state.commands do
      if containsExample command then
        let start := inputCtx.fileMap.toPosition (command.getPos?.getD 0)
        let stop := inputCtx.fileMap.toPosition (command.getTailPos?.getD 0)
        IO.println s!"EXAMPLE\t{path}\t{start.line}\t{start.column}\t{stop.line}\t{stop.column}"
  return 0
""".strip()


_DUMP_ANONYMOUS_EXAMPLES_PATH = "/tmp/_dump_anonymous_examples.lean"


def collect_anonymous_example_ranges(
    env: Any, paths: list[str]
) -> dict[str, list[DeclRange]]:
    """Return exact outer-command ranges for anonymous ``example`` commands.

    Callers pass source-level candidate files. The Lean frontend supplies the
    complete command range, including doc-comment and command-modifier
    wrappers; no textual boundary heuristic is involved.

    Each source is elaborated in a fresh Lean process. Large repositories can
    have many heavyweight example-bearing modules, and retaining every loaded
    environment in one process produces unbounded peak memory even though the
    files are independent. Per-file processes preserve the exact frontend
    result while releasing imported environments between sources.
    """

    requested = sorted(set(paths))
    if not requested:
        return {}
    env.execute(
        f"cat > {_DUMP_ANONYMOUS_EXAMPLES_PATH} << 'LEANEXAMPLES_EOF'\n"
        f"{_DUMP_ANONYMOUS_EXAMPLES_LEAN}\nLEANEXAMPLES_EOF"
    )
    ranges: dict[str, list[DeclRange]] = {}
    record_index = 0
    for requested_path in requested:
        result = env.execute(
            "cd /testbed && lake env lean --run "
            f"{_DUMP_ANONYMOUS_EXAMPLES_PATH} "
            f"{shlex.quote(requested_path)}",
            timeout=3600,
        )
        returncode = result.get("returncode", 1)
        output = result.get("output", "")
        if returncode != 0:
            detail = output[-4000:].strip() or "<no process output>"
            raise RuntimeError(
                "Lean anonymous-example range extraction failed for "
                f"{requested_path} (exit {returncode}): {detail}"
            )

        for line in output.splitlines():
            parts = line.split("\t")
            if not parts or parts[0] != "EXAMPLE" or len(parts) != 6:
                continue
            _, path, sl, sc, el, ec = parts
            if path != requested_path:
                raise RuntimeError(
                    "anonymous-example extractor returned unexpected path "
                    f"{path!r} while processing {requested_path!r}"
                )
            try:
                row: DeclRange = {
                    "name": f"__anonymous_example__.{record_index}",
                    "module": "",
                    "start_line": int(sl),
                    "start_col": int(sc),
                    "end_line": int(el),
                    "end_col": int(ec),
                    "kind": "example",
                    "meta": False,
                    "keep": False,
                }
            except ValueError as error:
                raise RuntimeError(
                    f"invalid anonymous-example range record: {line!r}"
                ) from error
            ranges.setdefault(path, []).append(row)
            record_index += 1
    return ranges

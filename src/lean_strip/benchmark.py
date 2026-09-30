"""The published LeanLean benchmark's repository layout (``--leanlean-benchmark``).

The benchmark was preprocessed by this engine's strip, so the Lean sources a
run produces are the benchmark's. The published repositories also followed the
benchmark's own layout, which this module reproduces byte for byte:

* the lakefile's library roots are synchronized with the Comparator's solution
  and challenge modules (and, for repositories that needed it at publication,
  with every locally imported module), instead of keeping import-only stubs
  for deleted roots;
* the non-Lean files are the ones the benchmark's asset resolver kept: root
  build metadata and files that retained Lean code references. Two published
  repositories predate the resolver's comment-aware revision and use the
  earlier one, which also counts paths mentioned in comments;
* the challenge and the Comparator configuration are not part of the tree
  (the benchmark keeps them in each repository's Comparator bundle).

The synchronization and resolver functions are copied verbatim from the
benchmark's ``palomar_normalize.py``: ``synchronize_lake_roots`` as of its
source preparation, ``referenced_local_assets`` as of the comment-aware
cleanup and ``referenced_local_assets_before_cleanup`` as of the preparation.
"""

from __future__ import annotations

import json
import re
import tomllib
from pathlib import Path, PurePosixPath
from typing import Iterable

from lean_strip._pipeline import palomar_normalize as current_normalize

# The documentation the benchmark's source image removed before isolation.
_DOCUMENTS = re.compile(
    r"(?i)^(.*\.md|readme(\..*)?|licen[cs]e(\..*)?|notice(\..*)?|copying(\..*)?)$"
)


ROOT_BUILD_METADATA = {
    ".gitignore",
    "lake-manifest.json",
    "lakefile.lean",
    "lakefile.toml",
    "lean-toolchain",
}


ROOT_DOCUMENT_PREFIXES = ("readme", "license", "copying", "notice")


def _inside(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
    except ValueError:
        return False
    return True


def _keep_non_source(path: Path, root: Path) -> bool:
    """Keep only the small, explicit root-level repository scaffold."""

    try:
        relative = path.relative_to(root)
    except ValueError:
        return False
    if len(relative.parts) != 1:
        return False
    if path.name in ROOT_BUILD_METADATA:
        return True
    if path.suffix == ".lean":
        return False
    lower = path.name.lower()
    return lower.startswith(ROOT_DOCUMENT_PREFIXES)


def _without_lean_comments(content: str) -> str:
    """Mask nested Lean comments without changing strings or token boundaries.

    This script is also installed standalone in isolation containers, so its
    small lexer deliberately has no imports from the host Python package.
    """
    raw_prefix = re.compile(r'r(#+)"')
    character_literal = re.compile(r"'(?:\\.|[^'\\\n])'")
    result = list(content)
    index = 0
    while index < len(content):
        if content.startswith("--", index):
            end = content.find("\n", index)
            end = len(content) if end < 0 else end
            result[index:end] = " " * (end - index)
            index = end
        elif content.startswith("/-", index):
            depth = 1
            end = index + 2
            while end < len(content) and depth:
                if content.startswith("/-", end):
                    depth += 1
                    end += 2
                elif content.startswith("-/", end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
            result[index:end] = ["\n" if char == "\n" else " " for char in content[index:end]]
            index = end
        else:
            raw = raw_prefix.match(content, index) if content[index] == "r" else None
            character = character_literal.match(content, index) if content[index] == "'" else None
            if raw:
                terminator = '"' + raw.group(1)
                end = content.find(terminator, raw.end())
                index = len(content) if end < 0 else end + len(terminator)
            elif character:
                index = character.end()
            elif content[index] == '"':
                index += 1
                while index < len(content):
                    if content[index] == "\\":
                        index += 2
                    elif content[index] == '"':
                        index += 1
                        break
                    else:
                        index += 1
            else:
                index += 1
    return "".join(result)


def referenced_local_assets(
    sources: Iterable[Path], root: Path
) -> set[Path]:
    """Retain concrete repo-local files named in executable Lean source text."""

    root = root.resolve(strict=True)
    assets: set[Path] = set()
    quoted = re.compile(r'"((?:\\.|[^"\\])*)"')
    bare_path = re.compile(
        r"(?<![A-Za-z0-9_./-])"
        r"([A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)+)(?![A-Za-z0-9_./-])"
    )
    joined_path = re.compile(
        r"\"[^\"]*\"(?:[ \t]*/[ \t]*\"[^\"]*\")+"
    )
    for source in sources:
        try:
            content = _without_lean_comments(source.read_text())
        except (OSError, UnicodeDecodeError):
            continue
        for encoded in quoted.findall(content):
            try:
                value = json.loads(f'"{encoded}"')
            except (ValueError, TypeError):
                continue
            if (
                not isinstance(value, str)
                or not value
                or "\x00" in value
                or "\n" in value
            ):
                continue
            for base in (source.parent, root):
                candidate = Path(value)
                if candidate.is_absolute():
                    candidate = root / value.lstrip("/")
                else:
                    candidate = base / candidate
                try:
                    resolved = candidate.resolve(strict=True)
                except (OSError, RuntimeError):
                    continue
                relative = resolved.relative_to(root) if _inside(resolved, root) else None
                if (
                    resolved.is_file()
                    and resolved.suffix != ".lean"
                    and relative is not None
                    and ".lake" not in relative.parts
                    and ".git" not in relative.parts
                ):
                    assets.add(resolved)
        for value in bare_path.findall(content):
            for base in (source.parent, root):
                candidate = Path(value)
                if candidate.is_absolute():
                    candidate = root / value.lstrip("/")
                else:
                    candidate = base / candidate
                try:
                    resolved = candidate.resolve(strict=True)
                except (OSError, RuntimeError):
                    continue
                relative = (
                    resolved.relative_to(root)
                    if _inside(resolved, root)
                    else None
                )
                if (
                    resolved.is_file()
                    and resolved.suffix != ".lean"
                    and relative is not None
                    and ".lake" not in relative.parts
                    and ".git" not in relative.parts
                ):
                    assets.add(resolved)
        for expression in joined_path.findall(content):
            try:
                components = [
                    json.loads(f"\"{encoded}\"")
                    for encoded in quoted.findall(expression)
                ]
            except (ValueError, TypeError):
                continue
            if (
                len(components) < 2
                or any(not isinstance(part, str) for part in components)
                or any("\x00" in part or "\n" in part for part in components)
            ):
                continue
            value = str(Path(components[0]).joinpath(*components[1:]))
            for base in (source.parent, root):
                candidate = Path(value)
                if candidate.is_absolute():
                    candidate = root / value.lstrip("/")
                else:
                    candidate = base / candidate
                try:
                    resolved = candidate.resolve(strict=True)
                except (OSError, RuntimeError):
                    continue
                relative = (
                    resolved.relative_to(root)
                    if _inside(resolved, root)
                    else None
                )
                if (
                    resolved.is_file()
                    and resolved.suffix != ".lean"
                    and relative is not None
                    and ".lake" not in relative.parts
                    and ".git" not in relative.parts
                ):
                    assets.add(resolved)
    return assets


def referenced_local_assets_before_cleanup(
    sources: Iterable[Path], root: Path
) -> set[Path]:
    """Retain concrete repo-local files named in kept Lean source text."""

    root = root.resolve(strict=True)
    assets: set[Path] = set()
    quoted = re.compile(r'"((?:\\.|[^"\\])*)"')
    bare_path = re.compile(
        r"(?<![A-Za-z0-9_./-])"
        r"([A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)+)(?![A-Za-z0-9_./-])"
    )
    joined_path = re.compile(
        r"\"[^\"]*\"(?:[ \t]*/[ \t]*\"[^\"]*\")+"
    )
    for source in sources:
        try:
            content = source.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        for encoded in quoted.findall(content):
            try:
                value = json.loads(f'"{encoded}"')
            except (ValueError, TypeError):
                continue
            if (
                not isinstance(value, str)
                or not value
                or "\x00" in value
                or "\n" in value
            ):
                continue
            for base in (source.parent, root):
                candidate = Path(value)
                if candidate.is_absolute():
                    candidate = root / value.lstrip("/")
                else:
                    candidate = base / candidate
                try:
                    resolved = candidate.resolve(strict=True)
                except (OSError, RuntimeError):
                    continue
                relative = resolved.relative_to(root) if _inside(resolved, root) else None
                if (
                    resolved.is_file()
                    and resolved.suffix != ".lean"
                    and relative is not None
                    and ".lake" not in relative.parts
                    and ".git" not in relative.parts
                ):
                    assets.add(resolved)
        for value in bare_path.findall(content):
            for base in (source.parent, root):
                candidate = Path(value)
                if candidate.is_absolute():
                    candidate = root / value.lstrip("/")
                else:
                    candidate = base / candidate
                try:
                    resolved = candidate.resolve(strict=True)
                except (OSError, RuntimeError):
                    continue
                relative = (
                    resolved.relative_to(root)
                    if _inside(resolved, root)
                    else None
                )
                if (
                    resolved.is_file()
                    and resolved.suffix != ".lean"
                    and relative is not None
                    and ".lake" not in relative.parts
                    and ".git" not in relative.parts
                ):
                    assets.add(resolved)
        for expression in joined_path.findall(content):
            try:
                components = [
                    json.loads(f"\"{encoded}\"")
                    for encoded in quoted.findall(expression)
                ]
            except (ValueError, TypeError):
                continue
            if (
                len(components) < 2
                or any(not isinstance(part, str) for part in components)
                or any("\x00" in part or "\n" in part for part in components)
            ):
                continue
            value = str(Path(components[0]).joinpath(*components[1:]))
            for base in (source.parent, root):
                candidate = Path(value)
                if candidate.is_absolute():
                    candidate = root / value.lstrip("/")
                else:
                    candidate = base / candidate
                try:
                    resolved = candidate.resolve(strict=True)
                except (OSError, RuntimeError):
                    continue
                relative = (
                    resolved.relative_to(root)
                    if _inside(resolved, root)
                    else None
                )
                if (
                    resolved.is_file()
                    and resolved.suffix != ".lean"
                    and relative is not None
                    and ".lake" not in relative.parts
                    and ".git" not in relative.parts
                ):
                    assets.add(resolved)
    return assets


_SAFE_MODULE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)


_LEAN_LIBRARY = re.compile(
    r"(?m)^lean_lib[ \t]+(?P<name>«[^»\n]+»|[A-Za-z_][A-Za-z0-9_']*)"
    r"(?P<tail>[^\n]*)$"
)


def _validated_module_roots(module_roots: tuple[str, ...]) -> tuple[str, ...]:
    roots = tuple(dict.fromkeys(module_roots))
    invalid = [module for module in roots if not _SAFE_MODULE.fullmatch(module)]
    if invalid:
        raise ValueError(f"unsafe registered Lake root modules: {invalid}")
    return roots


def _string_list(value: object) -> bool:
    return isinstance(value, list) and all(
        isinstance(item, str) for item in value
    )


def _module_matches_toml_glob(pattern: str, module: str) -> bool:
    if pattern.endswith(".+"):
        return module.startswith(pattern[:-1])
    if pattern.endswith(".*"):
        prefix = pattern[:-2]
        return module == prefix or module.startswith(prefix + ".")
    return module == pattern


def _toml_library_contains(library: dict[str, object], module: str) -> bool:
    roots = library.get("roots")
    globs = library.get("globs")
    if roots is not None and not _string_list(roots):
        raise ValueError("[[lean_lib]].roots must be a string array")
    if globs is not None and not _string_list(globs):
        raise ValueError("[[lean_lib]].globs must be a string array")
    if roots is not None and module in roots:
        return True
    if globs is not None and any(
        _module_matches_toml_glob(pattern, module) for pattern in globs
    ):
        return True
    name = library.get("name")
    return (
        roots is None
        and globs is None
        and isinstance(name, str)
        and (module == name or module.startswith(name + "."))
    )


def _lake_report(
    *,
    status: str,
    path: str | None,
    roots: tuple[str, ...],
    libraries: list[dict[str, object]],
) -> dict[str, object]:
    return {
        "status": status,
        "path": path,
        "roots_after": list(roots),
        "roots_removed": sorted(
            {
                module
                for report in libraries
                for module in report["roots_removed"]
            }
        ),
        "libraries": libraries,
    }


def synchronize_lakefile_toml_roots(
    root: Path, roots: tuple[str, ...]
) -> dict[str, object]:
    """Restrict the relevant TOML Lean libraries to registered modules.

    Import resolution remains Lean's responsibility: dependencies of these
    roots are built transitively. In particular, a registered Challenge root
    may be absent from the isolated source tree because the official verifier
    injects it later.
    """

    path = root / "lakefile.toml"
    if not path.is_file():
        return {"status": "not_applicable", "path": None}

    original = path.read_text()
    payload = tomllib.loads(original)
    libraries = payload.get("lean_lib")
    if not isinstance(libraries, list) or not libraries:
        raise ValueError("lakefile.toml has no [[lean_lib]] table")
    assignments: dict[int, list[str]] = {}
    for module in roots:
        exact = [
            index
            for index, library in enumerate(libraries)
            if isinstance(library, dict) and library.get("name") == module
        ]
        containing = [
            index
            for index, library in enumerate(libraries)
            if isinstance(library, dict)
            and _toml_library_contains(library, module)
        ]
        candidates = exact or containing
        if not candidates and len(libraries) == 1:
            candidates = [0]
        if len(candidates) != 1:
            raise ValueError(
                "could not resolve exactly one [[lean_lib]] for registered "
                f"module {module!r}"
            )
        assignments.setdefault(candidates[0], []).append(module)

    table_starts = list(re.finditer(r"(?m)^\[\[[^\]]+\]\][^\n]*$", original))
    lean_tables = [
        (match.start(), index)
        for index, match in enumerate(table_starts)
        if match.group(0).strip().startswith("[[lean_lib]]")
    ]
    if len(lean_tables) != len(libraries):
        raise ValueError("could not map parsed [[lean_lib]] tables to source text")
    replacements: list[tuple[int, int, str]] = []
    library_reports: list[dict[str, object]] = []
    for target_index, assigned_roots in sorted(assignments.items()):
        target_library = libraries[target_index]
        before_roots = target_library.get("roots")
        before_globs = target_library.get("globs")
        if before_roots is not None and not _string_list(before_roots):
            raise ValueError("resolved [[lean_lib]].roots must be a string array")
        if before_globs is not None and not _string_list(before_globs):
            raise ValueError("resolved [[lean_lib]].globs must be a string array")
        before = list(before_roots or [])
        globs = list(before_globs or [])
        library_reports.append(
            {
                "library": str(target_library.get("name") or ""),
                "roots_before": before,
                "globs_before": globs,
                "roots_after": list(assigned_roots),
                "roots_removed": sorted(set(before) - set(assigned_roots)),
                "globs_removed": globs,
            }
        )
        if before == assigned_roots and before_globs is None:
            continue
        table_start, all_table_index = lean_tables[target_index]
        table_end = (
            table_starts[all_table_index + 1].start()
            if all_table_index + 1 < len(table_starts)
            else len(original)
        )
        section = original[table_start:table_end]
        rendered_roots = "roots = [\n" + "".join(
            f"  {json.dumps(module)},\n" for module in assigned_roots
        ) + "]"
        assignment = re.search(
            r"(?ms)^[ \t]*roots[ \t]*=[ \t]*\[.*?\]", section
        )
        if assignment is None:
            name_line = re.search(r"(?m)^[ \t]*name[ \t]*=.*$", section)
            if name_line is None:
                raise ValueError("resolved [[lean_lib]] has no name assignment")
            insert_at = name_line.end()
            section = (
                section[:insert_at]
                + "\n"
                + rendered_roots
                + section[insert_at:]
            )
        else:
            section = (
                section[: assignment.start()]
                + rendered_roots
                + section[assignment.end() :]
            )
        globs_assignment = re.search(
            r"(?ms)^[ \t]*globs[ \t]*=[ \t]*\[.*?\][ \t]*(?:#.*)?\n?",
            section,
        )
        if globs_assignment is not None:
            section = (
                section[: globs_assignment.start()]
                + section[globs_assignment.end() :]
            )
        replacements.append((table_start, table_end, section))
    rewritten = original
    for table_start, table_end, section in reversed(replacements):
        rewritten = rewritten[:table_start] + section + rewritten[table_end:]
    parsed = tomllib.loads(rewritten)
    for target_index, assigned_roots in assignments.items():
        rewritten_library = parsed["lean_lib"][target_index]
        if (
            rewritten_library.get("roots") != assigned_roots
            or "globs" in rewritten_library
        ):
            raise ValueError("rewritten [[lean_lib]] roots failed validation")
    if rewritten != original:
        path.write_text(rewritten)
    return _lake_report(
        status="rewritten" if replacements else "unchanged",
        path="lakefile.toml",
        roots=roots,
        libraries=library_reports,
    )


def _lean_name(text: str) -> str:
    return text[1:-1] if text.startswith("«") and text.endswith("»") else text


def _lean_array_modules(expression: str) -> list[str]:
    return re.findall(
        r"`([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)",
        expression,
    )


def _lean_libraries(source: str) -> list[dict[str, object]]:
    matches = list(_LEAN_LIBRARY.finditer(source))
    libraries: list[dict[str, object]] = []
    for match in matches:
        following = source[match.end() :]
        next_command = re.search(r"(?m)^\S", following)
        end = (
            match.end() + next_command.start()
            if next_command is not None
            else len(source)
        )
        section = source[match.start() : end]
        roots_match = re.search(
            r"(?ms)^[ \t]+roots[ \t]*:=[ \t]*(#\[.*?\])", section
        )
        globs_match = re.search(
            r"(?ms)^[ \t]+globs[ \t]*:=[ \t]*(#\[.*?\])", section
        )
        libraries.append(
            {
                "name": _lean_name(match.group("name")),
                "start": match.start(),
                "end": end,
                "declaration_end": match.end(),
                "has_where": bool(
                    re.search(
                        r"(?:^|[ \t])where[ \t]*(?:--.*)?$",
                        match.group("tail"),
                    )
                ),
                "roots": (
                    _lean_array_modules(roots_match.group(1))
                    if roots_match is not None
                    else None
                ),
                "roots_span": (
                    (roots_match.start(), roots_match.end())
                    if roots_match is not None
                    else None
                ),
                "globs": (
                    _lean_array_modules(globs_match.group(1))
                    if globs_match is not None
                    else None
                ),
                "globs_span": (
                    (globs_match.start(), globs_match.end())
                    if globs_match is not None
                    else None
                ),
                "section": section,
            }
        )
    return libraries


def _lean_library_candidates(
    libraries: list[dict[str, object]], module: str
) -> list[int]:
    exact = [
        index
        for index, library in enumerate(libraries)
        if library["name"] == module
    ]
    containing = [
        index
        for index, library in enumerate(libraries)
        if module in (library["roots"] or [])
        or module in (library["globs"] or [])
    ]
    candidates = exact or containing
    if not candidates and len(libraries) == 1:
        candidates = [0]
    return candidates


def _render_lean_roots(roots: list[str]) -> str:
    return "  roots := #[" + ", ".join(f"`{module}" for module in roots) + "]"


def _rewrite_lean_library(
    library: dict[str, object], assigned_roots: list[str]
) -> str:
    section = str(library["section"])
    replacements: list[tuple[int, int, str]] = []
    roots_span = library["roots_span"]
    if roots_span is not None:
        replacements.append((*roots_span, _render_lean_roots(assigned_roots)))
    globs_span = library["globs_span"]
    if globs_span is not None:
        start, end = globs_span
        if end < len(section) and section[end] == "\n":
            end += 1
        replacements.append((start, end, ""))
    for start, end, replacement in sorted(replacements, reverse=True):
        section = section[:start] + replacement + section[end:]
    if roots_span is None:
        declaration_end = int(library["declaration_end"]) - int(library["start"])
        if not library["has_where"]:
            section = section[:declaration_end] + " where" + section[declaration_end:]
            declaration_end += len(" where")
        section = (
            section[:declaration_end]
            + "\n"
            + _render_lean_roots(assigned_roots)
            + section[declaration_end:]
        )
    return section


def synchronize_lakefile_lean_roots(
    root: Path, roots: tuple[str, ...]
) -> dict[str, object]:
    """Restrict resolved Lake DSL libraries to the registered modules."""

    path = root / "lakefile.lean"
    if not path.is_file():
        return {"status": "not_applicable", "path": None}
    original = path.read_text()
    libraries = _lean_libraries(original)
    if not libraries:
        raise ValueError("lakefile.lean has no static lean_lib declaration")
    assignments: dict[int, list[str]] = {}
    for module in roots:
        candidates = _lean_library_candidates(libraries, module)
        if len(candidates) != 1:
            raise ValueError(
                "could not resolve exactly one lean_lib for registered "
                f"module {module!r}"
            )
        assignments.setdefault(candidates[0], []).append(module)

    replacements: list[tuple[int, int, str]] = []
    reports: list[dict[str, object]] = []
    for index, assigned_roots in sorted(assignments.items()):
        library = libraries[index]
        before_roots = library["roots"]
        before_globs = library["globs"]
        implicit_exact_root = (
            before_roots is None
            and before_globs is None
            and assigned_roots == [library["name"]]
        )
        reports.append(
            {
                "library": library["name"],
                "roots_before": (
                    list(before_roots)
                    if before_roots is not None
                    else [library["name"]]
                ),
                "globs_before": list(before_globs or []),
                "roots_after": list(assigned_roots),
                "roots_removed": sorted(
                    set((before_roots or []) + (before_globs or []))
                    - set(assigned_roots)
                ),
            }
        )
        if implicit_exact_root or (
            before_roots == assigned_roots and before_globs is None
        ):
            continue
        replacements.append(
            (
                int(library["start"]),
                int(library["end"]),
                _rewrite_lean_library(library, assigned_roots),
            )
        )

    rewritten = original
    for start, end, replacement in reversed(replacements):
        rewritten = rewritten[:start] + replacement + rewritten[end:]
    rewritten_libraries = _lean_libraries(rewritten)
    for module in roots:
        candidates = _lean_library_candidates(rewritten_libraries, module)
        if len(candidates) != 1:
            raise ValueError("rewritten lakefile.lean failed root validation")
        library = rewritten_libraries[candidates[0]]
        configured_roots = library["roots"]
        if configured_roots is None:
            configured_roots = [library["name"]]
        if module not in configured_roots or library["globs"] is not None:
            raise ValueError("rewritten lakefile.lean failed root validation")
    if rewritten != original:
        path.write_text(rewritten)
    return _lake_report(
        status="rewritten" if replacements else "unchanged",
        path="lakefile.lean",
        roots=roots,
        libraries=reports,
    )


def synchronize_lake_roots(
    root: Path, module_roots: tuple[str, ...]
) -> dict[str, object]:
    if not module_roots:
        return {"status": "not_requested", "path": None}
    roots = _validated_module_roots(module_roots)
    toml = root / "lakefile.toml"
    lean = root / "lakefile.lean"
    if toml.is_file() and lean.is_file():
        raise ValueError("project has both lakefile.toml and lakefile.lean")
    if toml.is_file():
        return synchronize_lakefile_toml_roots(root, roots)
    if lean.is_file():
        return synchronize_lakefile_lean_roots(root, roots)
    raise ValueError("project has no Lake manifest")


def is_document(relative: str) -> bool:
    """Documentation the benchmark removed before isolating a repository."""

    name = PurePosixPath(relative).name
    return not name.endswith(".lean") and bool(_DOCUMENTS.match(name))


def benchmark_non_lean_files(root: Path, closure: Iterable[str], candidates: Iterable[str], *,
                             before_cleanup: bool = False) -> set[str]:
    """The non-Lean ``candidates`` (repository-relative, documents excluded) the benchmark kept."""

    root = root.resolve()
    candidates = {path for path in candidates
                  if (path == "lakefile.lean" or not path.endswith(".lean")) and not is_document(path)}
    sources = {(root / path).resolve() for path in closure if (root / path).is_file()}
    resolver = referenced_local_assets_before_cleanup if before_cleanup else referenced_local_assets
    assets = {path.relative_to(root).as_posix() for path in resolver(sources, root)}
    kept = {path for path in candidates if _keep_non_source(root / path, root)}
    return (assets & candidates) | kept


def benchmark_lake_roots(tree: Path, solution_module: str, challenge_module: str,
                         *, repair: bool = False,
                         sources: Iterable[Path] | None = None) -> dict[str, object]:
    """Rewrite the lakefile's library roots as the benchmark's preparation did.

    ``repair`` re-synchronizes the roots with every locally imported module of
    ``sources`` (default: every Lean file under ``tree``), the publication repair
    of repositories that otherwise do not build from clean.
    """

    isolation = synchronize_lake_roots(tree, (solution_module, challenge_module))
    record: dict[str, object] = {"isolation": isolation, "repaired": repair}
    if repair:
        lean_files = list(sources) if sources is not None else list(tree.rglob("*.lean"))
        modules = current_normalize.local_import_modules(lean_files, tree)
        record["repair"] = current_normalize.synchronize_lake_roots(
            tree, tuple(dict.fromkeys((solution_module, challenge_module, *modules)))
        )
    return record

"""Reduce a built Lean project to the local source closure of its entry file.

Lean's --src-deps output contains the directly imported source paths. We apply
it recursively so module resolution remains Lean's responsibility while the
resulting closure is transitive. Files supplied by the Lean installation or
Lake packages remain build dependencies but are not copied into the local
source repository.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
import tomllib
from collections import deque
from pathlib import Path
from typing import Iterable


ROOT_BUILD_METADATA = {
    ".gitignore",
    "lake-manifest.json",
    "lakefile.lean",
    "lakefile.toml",
    "lean-toolchain",
}
ROOT_DOCUMENT_PREFIXES = ("readme", "license", "copying", "notice")
_SAFE_MODULE = re.compile(
    r"(?:[A-Za-z_][A-Za-z0-9_']*|«[^»\n]+»)"
    r"(?:\.(?:[A-Za-z_][A-Za-z0-9_']*|«[^»\n]+»))*"
)
_LEAN_LIBRARY = re.compile(
    r"(?m)^lean_lib[ \t]+(?P<name>«[^»\n]+»|[A-Za-z_][A-Za-z0-9_']*)"
    r"(?P<tail>[^\n]*)$"
)
_MODULE_COMPONENT = r"(?:[A-Za-z_][A-Za-z0-9_']*|«[^»\n]+»)"
_IMPORT_COMMAND = re.compile(
    rf"(?m)^[ \t]*(?:(?:public|meta)[ \t]+)?import"
    rf"(?:[ \t]+all)?[ \t]+(?P<module>{_MODULE_COMPONENT}(?:\.{_MODULE_COMPONENT})*)"
)


def _inside(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
    except ValueError:
        return False
    return True


def _local_source(path: str, root: Path) -> Path | None:
    candidate = Path(path.strip())
    if not candidate.is_absolute():
        candidate = root / candidate
    try:
        resolved = candidate.resolve(strict=True)
    except (OSError, RuntimeError):
        return None
    if (
        resolved.suffix != ".lean"
        or not _inside(resolved, root)
        or ".lake" in resolved.relative_to(root).parts
    ):
        return None
    return resolved


def lake_environment(root: Path) -> dict[str, str]:
    """Return the environment ``lake env`` would give a command in ``root``.

    Starting Lake costs about a second (it loads the workspace and every
    package manifest), while ``lean --src-deps`` itself takes milliseconds.
    Capture the environment once and reuse it for every file.
    """
    result = subprocess.run(
        [
            "lake", "env", sys.executable, "-c",
            "import json, os; print(json.dumps(dict(os.environ)))",
        ],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    return json.loads(result.stdout.strip().splitlines()[-1])


def direct_local_dependencies(
    source: Path, root: Path, env: dict[str, str] | None = None
) -> tuple[Path, ...]:
    command = (
        ["lake", "env", "lean", "--src-deps", str(source)]
        if env is None
        else [env.get("LEAN", "lean"), "--src-deps", str(source)]
    )
    result = subprocess.run(
        command,
        cwd=root,
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )
    dependencies = {
        dependency
        for line in result.stdout.splitlines()
        if (dependency := _local_source(line, root)) is not None
    }
    return tuple(sorted(dependencies))


def transitive_local_sources(entries: Iterable[Path], root: Path) -> set[Path]:
    root = root.resolve(strict=True)
    queue: deque[Path] = deque()
    closure: set[Path] = set()
    for entry in entries:
        source = entry if entry.is_absolute() else root / entry
        source = source.resolve(strict=True)
        if source.suffix != ".lean" or not _inside(source, root):
            raise ValueError(f"entry source is outside the Lean project: {entry}")
        queue.append(source)
    env = lake_environment(root)
    while queue:
        source = queue.popleft()
        if source in closure:
            continue
        closure.add(source)
        for dependency in direct_local_dependencies(source, root, env):
            if dependency not in closure:
                queue.append(dependency)
    return closure


def _module_to_relative_path(module: str) -> Path:
    """Convert an exact Lean module name to its source-path suffix."""

    components: list[str] = []
    component: list[str] = []
    quoted = False
    for char in module:
        if char == "«" and not quoted:
            quoted = True
        elif char == "»" and quoted:
            quoted = False
        elif char == "." and not quoted:
            components.append("".join(component))
            component = []
        else:
            component.append(char)
    if quoted:
        raise ValueError(f"unterminated quoted module component: {module!r}")
    components.append("".join(component))
    return Path(*components).with_suffix(".lean")


def local_import_modules(sources: Iterable[Path], root: Path) -> tuple[str, ...]:
    """Return exact imported module names whose sources are retained locally."""

    root = root.resolve(strict=True)
    retained = {source.resolve(strict=True) for source in sources}
    retained_relatives = tuple(
        source.relative_to(root).as_posix() for source in retained
    )
    modules: set[str] = set()
    for source in retained:
        masked = _without_lean_comments(source.read_text())
        for match in _IMPORT_COMMAND.finditer(masked):
            module = match.group("module")
            suffix = _module_to_relative_path(module).as_posix()
            if any(
                relative == suffix or relative.endswith("/" + suffix)
                for relative in retained_relatives
            ):
                modules.add(module)
    return tuple(sorted(modules))


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


ASSET_RESOLVER = "concrete_paths_in_retained_lean_code_no_comments_v2"


def _without_lean_comments(content: str) -> str:
    """Mask nested Lean comments without changing strings or token boundaries.

    Unlike ``metrics.tokens.remove_lean_comments`` this also skips raw strings
    and character literals, so a ``--`` or ``/-`` inside them is not a comment.
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


def _local_assets(value: str, directory: Path, root: Path) -> set[Path]:
    """Resolve a path literal against its source directory and the root."""

    found: set[Path] = set()
    for base in (directory, root):
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
            found.add(resolved)
    return found


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
            assets.update(_local_assets(value, source.parent, root))
        for value in bare_path.findall(content):
            assets.update(_local_assets(value, source.parent, root))
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
            assets.update(_local_assets(value, source.parent, root))
    return assets


def _validated_module_roots(module_roots: tuple[str, ...]) -> tuple[str, ...]:
    roots = tuple(dict.fromkeys(module_roots))
    invalid = [module for module in roots if not _SAFE_MODULE.fullmatch(module)]
    if invalid:
        raise ValueError(f"unsafe registered Lake root modules: {invalid}")
    return roots


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
    if roots is not None and any(
        module == root or module.startswith(root + ".") for root in roots
    ):
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


def synchronize_lakefile_toml_roots(
    root: Path, roots: tuple[str, ...]
) -> dict[str, object]:
    """Restrict the relevant TOML Lean libraries to registered modules.

    Import resolution remains Lean's responsibility: dependencies of these
    roots are built transitively, so a registered root need not have a source
    file in the tree (for example a challenge module that is added back after
    stripping).
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
        named = [
            index
            for index, library in enumerate(libraries)
            if isinstance(library, dict)
            and isinstance(library.get("name"), str)
            and (
                module == library["name"]
                or module.startswith(str(library["name"]) + ".")
            )
        ]
        candidates = exact or containing or named
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
        implicit_coverage = (
            before_roots is None
            and before_globs is None
            and all(
                _toml_library_contains(target_library, module)
                for module in assigned_roots
            )
        )
        if implicit_coverage or (
            before == assigned_roots and before_globs is None
        ):
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
        for module in assigned_roots:
            if not _toml_library_contains(rewritten_library, module):
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
        rf"`({_MODULE_COMPONENT}(?:\.{_MODULE_COMPONENT})*)",
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
        if any(
            module == root or module.startswith(str(root) + ".")
            for root in (library["roots"] or [])
        )
        or any(
            _module_matches_toml_glob(str(glob), module)
            for glob in (library["globs"] or [])
        )
    ]
    named = [
        index
        for index, library in enumerate(libraries)
        if module == library["name"]
        or module.startswith(str(library["name"]) + ".")
    ]
    candidates = exact or containing or named
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
            and all(
                module == library["name"]
                or module.startswith(str(library["name"]) + ".")
                for module in assigned_roots
            )
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
        # Lake treats a root as covering its submodules, which is why an
        # implicit `lean_lib Foo` root is left alone for `Foo.*` modules above.
        covered = any(
            module == root or module.startswith(str(root) + ".")
            for root in configured_roots
        )
        if not covered or library["globs"] is not None:
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


def _tree_digest(root: Path) -> str:
    digest = hashlib.sha256()
    for path in sorted(
        candidate for candidate in root.rglob("*") if candidate.is_file()
    ):
        relative = path.relative_to(root)
        if relative.parts[0] in {".git", ".lake"}:
            continue
        encoded = relative.as_posix().encode()
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
        digest.update(path.stat().st_mode.to_bytes(8, "big"))
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
    return digest.hexdigest()


def normalize(
    root: Path,
    entries: tuple[Path, ...],
    *,
    drop_entries: tuple[Path, ...] = (),
    root_modules: tuple[str, ...] = (),
) -> dict[str, object]:
    root = root.resolve(strict=True)
    resolved_entries = tuple(
        (entry if entry.is_absolute() else root / entry).resolve(strict=True)
        for entry in entries
    )
    resolved_drops = {
        (entry if entry.is_absolute() else root / entry).resolve(strict=True)
        for entry in drop_entries
    }
    if not resolved_drops.issubset(resolved_entries):
        raise ValueError("dropped entries must also be dependency-closure entries")
    closure = transitive_local_sources(resolved_entries, root)
    closure.difference_update(resolved_drops)
    assets = referenced_local_assets(closure, root)
    before = [
        path
        for path in root.rglob("*")
        if path.is_file()
        and path.relative_to(root).parts[0] not in {".git", ".lake"}
    ]
    removed: list[str] = []
    for path in before:
        if path in closure or path in assets or _keep_non_source(path, root):
            continue
        relative = path.relative_to(root).as_posix()
        path.unlink()
        removed.append(relative)
    local_modules = local_import_modules(closure, root)
    lake_roots = (
        tuple(dict.fromkeys((*root_modules, *local_modules)))
        if root_modules
        else ()
    )
    lake_metadata = synchronize_lake_roots(root, lake_roots)
    for directory, directories, _ in os.walk(root, topdown=False):
        current = Path(directory)
        if current == root or any(
            part in {".git", ".lake"} for part in current.relative_to(root).parts
        ):
            continue
        directories[:] = [
            name for name in directories if name not in {".git", ".lake"}
        ]
        try:
            current.rmdir()
        except OSError:
            pass
    after = [
        path
        for path in root.rglob("*")
        if path.is_file()
        and path.relative_to(root).parts[0] not in {".git", ".lake"}
    ]
    retained_sources = sorted(
        path.relative_to(root).as_posix() for path in closure
    )
    return {
        "kind": "palomar_import_closure",
        "schema_version": 1,
        "resolver": "recursive_lake_env_lean_src_deps",
        "entry_sources": sorted(
            entry.relative_to(root).as_posix() for entry in resolved_entries
        ),
        "dropped_entry_sources": sorted(
            entry.relative_to(root).as_posix() for entry in resolved_drops
        ),
        "retained_local_sources": retained_sources,
        "retained_local_source_count": len(retained_sources),
        "retained_local_import_modules": list(local_modules),
        "retained_local_assets": sorted(
            path.relative_to(root).as_posix() for path in assets
        ),
        "retained_local_asset_count": len(assets),
        "asset_resolver": ASSET_RESOLVER,
        "files_before": len(before),
        "files_after": len(after),
        "files_removed": len(removed),
        "removed_paths": sorted(removed),
        "lake_metadata": lake_metadata,
        "normalized_tree_sha256": _tree_digest(root),
    }


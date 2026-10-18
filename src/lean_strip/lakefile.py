"""Keeping the lakefile valid after the strip deleted modules it names.

Lake builds a library from its globs, which default to its roots. Deleting a
root module (`Foo.lean` of `lean_lib Foo`) or every module under a
`Foo.+`/`Foo.*` glob makes plain `lake build` fail, and so does deleting the
root of a `lean_exe`. The rewrite is the smallest edit that fixes this:

* a library glob whose module was deleted becomes `Foo.+` (the surviving
  submodules), or is dropped when nothing under it survives. The library's
  roots are left alone, so its surviving modules still belong to it and
  `lake build +Foo.Bar` keeps working;
* an executable whose root was deleted is removed, together with its entry in
  the default targets.

Only static `lean_lib`/`lean_exe` declarations are edited. A reference that
cannot be resolved safely is reported instead of guessed at.
"""

from __future__ import annotations

import json
import posixpath
import re
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

_COMPONENT = r"(?:«[^»]+»|[^\s.,\[\]`#():=]+)"
_NAME = rf"{_COMPONENT}(?:\.{_COMPONENT})*"
_DECLARATION = re.compile(
    rf"(?m)^(?P<attrs>(?:[ \t]*@\[[^\]\n]*\][ \t]*\n?)*)[ \t]*(?P<kind>lean_lib|lean_exe)[ \t]+(?P<name>{_NAME})(?P<tail>[^\n]*)$"
)
_LEAN_GLOB = re.compile(
    rf"^(?:(?:Lake\.)?(?:Glob)?\.(?P<kind>one|submodules|andSubmodules)[ \t]+)?`(?P<name>{_NAME})$"
)


@dataclass
class LakefileEdit:
    """The rewrite of one lakefile; ``text`` is None when nothing changes."""

    path: str
    text: str | None = None
    changes: list[str] = field(default_factory=list)
    unresolved: list[str] = field(default_factory=list)

    def as_report(self) -> dict[str, object]:
        return {
            "path": self.path,
            "rewritten": self.text is not None,
            "changes": self.changes,
            "unresolved": self.unresolved,
        }


def _plain(name: str) -> str:
    return ".".join(part.strip("«»") for part in name.split("."))


def _module_file(src_dir: str, module: str) -> str:
    return posixpath.normpath(posixpath.join(src_dir, *module.split("."))) + ".lean"


def _module_dir(src_dir: str, module: str) -> str:
    return posixpath.normpath(posixpath.join(src_dir, *module.split(".")))


class _Survivors:
    def __init__(self, files: set[str]) -> None:
        self.files = files
        self.dirs = {posixpath.dirname(path) for path in files}
        for directory in list(self.dirs):
            while directory:
                directory = posixpath.dirname(directory)
                self.dirs.add(directory)

    def has_module(self, src_dir: str, module: str) -> bool:
        return _module_file(src_dir, module) in self.files

    def has_submodules(self, src_dir: str, module: str) -> bool:
        return _module_dir(src_dir, module) in self.dirs


def _fix_globs(
    globs: list[tuple[str, str]], src_dir: str, survivors: _Survivors,
    existed: set[str],
) -> tuple[list[tuple[str, str]], list[str]]:
    """New (kind, module) globs and a note per change; kinds are one/submodules/andSubmodules."""

    fixed: list[tuple[str, str]] = []
    notes: list[str] = []
    before = _Survivors(existed)
    for kind, module in globs:
        own = survivors.has_module(src_dir, module)
        below = survivors.has_submodules(src_dir, module)
        never_there = not before.has_module(src_dir, module) and not before.has_submodules(src_dir, module)
        if never_there:
            # Nothing of it existed where we look (a root Lake resolves through a
            # srcDir we cannot read, say): not ours to judge, so leave it.
            fixed.append((kind, module))
        elif kind == "one" and not own:
            if below:
                fixed.append(("submodules", module))
                notes.append(f"{module} was deleted; building its surviving submodules ({module}.+) instead")
            else:
                notes.append(f"{module} was deleted and nothing under it survives; dropped from the build")
        elif kind == "andSubmodules" and not own:
            if below:
                fixed.append(("submodules", module))
                notes.append(f"{module} was deleted; {module}.* narrowed to {module}.+")
            else:
                notes.append(f"{module} and its submodules were deleted; {module}.* dropped")
        elif kind == "submodules" and not below:
            notes.append(f"nothing under {module} survives; {module}.+ dropped")
        else:
            fixed.append((kind, module))
    return fixed, notes


# -- lakefile.toml -------------------------------------------------------------

_TOML_SUFFIX = {".+": "submodules", ".*": "andSubmodules"}


def _toml_glob(text: str) -> tuple[str, str]:
    for suffix, kind in _TOML_SUFFIX.items():
        if text.endswith(suffix):
            return kind, text[: -len(suffix)]
    return "one", text


def _render_toml_glob(kind: str, module: str) -> str:
    return module + {"one": "", "submodules": ".+", "andSubmodules": ".*"}[kind]


def _toml_string_list(value: object) -> bool:
    return isinstance(value, list) and all(isinstance(item, str) for item in value)


def _toml_tables(text: str) -> list[tuple[str, int, int]]:
    """(header, start, end) of every table in ``text``, in order."""

    headers = list(re.finditer(r"(?m)^[ \t]*\[\[?[^\]\n]+\]\]?[^\n]*$", text))
    return [
        (match.group(0).strip(), match.start(),
         headers[index + 1].start() if index + 1 < len(headers) else len(text))
        for index, match in enumerate(headers)
    ]


def _toml_assignment(section: str, key: str) -> re.Match[str] | None:
    return re.search(rf"(?ms)^[ \t]*{key}[ \t]*=[ \t]*(\[.*?\]|\"[^\"\n]*\")[ \t]*(?:#[^\n]*)?\n?", section)


def _plan_toml(text: str, survivors: _Survivors, existed: set[str]) -> LakefileEdit:
    edit = LakefileEdit("lakefile.toml")
    try:
        config = tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:
        edit.unresolved.append(f"lakefile.toml does not parse: {error}")
        return edit
    package_dir = str(config.get("srcDir", "."))
    tables = _toml_tables(text)
    by_kind: dict[str, list[tuple[int, int]]] = {}
    for header, start, end in tables:
        kind = header.removeprefix("[[").split("]]")[0].strip()
        by_kind.setdefault(kind, []).append((start, end))
    replacements: list[tuple[int, int, str]] = []
    removed_targets: list[str] = []

    libraries = config.get("lean_lib") or []
    lib_spans = by_kind.get("lean_lib", [])
    if libraries and len(libraries) != len(lib_spans):
        edit.unresolved.append("lean_lib tables are not written as [[lean_lib]]; left as they are")
        libraries = []
    for library, (start, end) in zip(libraries, lib_spans):
        name = str(library.get("name", ""))
        src_dir = posixpath.join(package_dir, str(library.get("srcDir", ".")))
        roots, globs = library.get("roots"), library.get("globs")
        if (roots is not None and not _toml_string_list(roots)) or (
            globs is not None and not _toml_string_list(globs)
        ):
            edit.unresolved.append(f"lean_lib {name}: roots/globs are not plain string lists")
            continue
        current = (
            [_toml_glob(item) for item in globs] if globs is not None
            else [("one", root) for root in (roots or [name])]
        )
        fixed, notes = _fix_globs(current, src_dir, survivors, existed)
        if not notes:
            continue
        edit.changes.extend(f"lean_lib {name}: {note}" for note in notes)
        section = text[start:end]
        rendered = "globs = [" + ", ".join(
            json.dumps(_render_toml_glob(kind, module)) for kind, module in fixed
        ) + "]\n"
        existing = _toml_assignment(section, "globs")
        if existing is not None:
            section = section[: existing.start()] + rendered + section[existing.end():]
        else:
            anchor = _toml_assignment(section, "roots") or _toml_assignment(section, "name")
            if anchor is None:
                edit.unresolved.append(f"lean_lib {name}: no name/roots line to place globs after")
                continue
            line = section[anchor.start():anchor.end()]
            section = section[: anchor.end()] + ("" if line.endswith("\n") else "\n") + rendered + section[anchor.end():]
        replacements.append((start, end, section))

    executables = config.get("lean_exe") or []
    exe_spans = by_kind.get("lean_exe", [])
    if executables and len(executables) != len(exe_spans):
        edit.unresolved.append("lean_exe tables are not written as [[lean_exe]]; left as they are")
        executables = []
    for executable, (start, end) in zip(executables, exe_spans):
        name = str(executable.get("name", ""))
        root = str(executable.get("root", name))
        src_dir = posixpath.join(package_dir, str(executable.get("srcDir", ".")))
        path = _module_file(src_dir, root)
        if path in existed and path not in survivors.files:
            edit.changes.append(f"lean_exe {name}: its root {root} was deleted; executable removed")
            replacements.append((start, end, ""))
            removed_targets.append(name)

    rewritten = text
    for start, end, section in sorted(replacements, reverse=True):
        rewritten = rewritten[:start] + section + rewritten[end:]
    targets = config.get("defaultTargets")
    if _toml_string_list(targets):
        kept, notes = _fix_default_targets(
            targets, removed_targets, libraries, executables, package_dir, survivors, existed,
        )
        if kept != targets:
            assignment = _toml_assignment(rewritten, "defaultTargets")
            if assignment is None:
                edit.unresolved.append("defaultTargets names deleted targets but could not be rewritten")
            else:
                rewritten = (rewritten[: assignment.start()]
                             + "defaultTargets = " + json.dumps(kept) + "\n"
                             + rewritten[assignment.end():])
                edit.changes.extend(notes)
    if rewritten != text:
        try:
            tomllib.loads(rewritten)
        except tomllib.TOMLDecodeError as error:
            edit.unresolved.append(f"the rewritten lakefile.toml does not parse ({error}); left as it was")
            edit.changes.clear()
            return edit
        edit.text = rewritten
    return edit


def _library_builds(library: dict, package_dir: str, survivors: _Survivors) -> bool:
    """Whether every module a TOML library builds exists after the strip.

    A library whose root never existed (`lean_lib VCG` without `VCG.lean`,
    PALOMAR-2026-10-01-000009) is not a valid default target.
    """

    src_dir = posixpath.join(package_dir, str(library.get("srcDir", ".")))
    globs = library.get("globs")
    current = ([_toml_glob(item) for item in globs] if _toml_string_list(globs)
               else [("one", root) for root in (library.get("roots") or [str(library.get("name", ""))])])
    return all(
        survivors.has_module(src_dir, module) if kind == "one"
        else survivors.has_submodules(src_dir, module)
        for kind, module in current
    )


def _fix_default_targets(
    targets: list[str], removed_executables: list[str], libraries: list[dict],
    executables: list[dict], package_dir: str, survivors: _Survivors, existed: set[str],
) -> tuple[list[str], list[str]]:
    """``defaultTargets`` without removed executables or deleted modules, and notes.

    A default target may name a module (`defaultTargets = ["Foo.Main"]`). When
    the strip deleted it, the library it belongs to is built instead, so plain
    `lake build` keeps building the surviving code.
    """

    declared = {str(item.get("name", "")) for item in [*libraries, *executables]}
    source_dirs = {package_dir} | {
        posixpath.join(package_dir, str(library.get("srcDir", "."))) for library in libraries
    }
    kept: list[str] = []
    notes: list[str] = []
    for target in targets:
        if target in removed_executables:
            notes.append(f"defaultTargets: removed executable {target}")
            continue
        paths = {_module_file(src_dir, target) for src_dir in source_dirs}
        if target in declared or not paths & existed or paths & survivors.files:
            kept.append(target)
            continue
        owner = next((
            str(library.get("name")) for library in libraries
            if any(target.startswith(root + ".")
                   for root in (library.get("roots") or [str(library.get("name", ""))]))
            and _library_builds(library, package_dir, survivors)
        ), None)
        if owner is None:
            notes.append(f"defaultTargets: module {target} was deleted; removed")
        else:
            notes.append(f"defaultTargets: module {target} was deleted; building library {owner} instead")
            kept.append(owner)
    return list(dict.fromkeys(kept)), notes


# -- lakefile.lean -------------------------------------------------------------


def _lean_declarations(text: str) -> list[dict[str, object]]:
    matches = list(_DECLARATION.finditer(text))
    declarations = []
    for match in matches:
        following = re.search(r"(?m)^\S", text[match.end():])
        end = match.end() + following.start() if following else len(text)
        declarations.append({
            "kind": match.group("kind"),
            "name": _plain(match.group("name")),
            "start": match.start(),
            "body_start": match.start("kind"),
            "indent": text[text.rfind("\n", 0, match.start("kind")) + 1 : match.start("kind")],
            "end": end,
            "attrs": match.group("attrs"),
            "tail": match.group("tail"),
            "section": text[match.start("kind"):end],
        })
    return declarations


def field_indent(section: str, declaration_indent: str) -> str:
    """The column for a new field of a Lake DSL declaration: an existing field's
    indentation, or two columns deeper than the declaration itself. Lean needs
    all fields of a `where` block in one column."""

    field = re.search(r"(?m)^([ \t]+)[A-Za-z_][A-Za-z0-9_]*[ \t]*:=", section)
    return field.group(1) if field is not None else declaration_indent + "  "


def _lean_field(section: str, key: str) -> re.Match[str] | None:
    return re.search(rf"(?ms)^[ \t]+{key}[ \t]*:=[ \t]*(?P<value>#\[.*?\]|`{_NAME}|\"[^\"\n]*\")[ \t]*(?:--[^\n]*)?\n?", section)


def _lean_array(value: str) -> list[str] | None:
    inner = value.strip()
    if not (inner.startswith("#[") and inner.endswith("]")):
        return None
    inner = inner[2:-1].strip()
    return [item.strip() for item in inner.split(",")] if inner else []


def package_src_dir(text: str) -> str:
    """The `srcDir` of a `lakefile.lean`'s package; its libraries' paths start there."""

    package = re.search(r"(?ms)^package\b.*?(?=^\S|\Z)", text)
    found = package and re.search(r'srcDir[ \t]*:=[ \t]*"([^"]*)"', package.group(0))
    return found.group(1) if found else "."


def _render_lean_glob(kind: str, module: str) -> str:
    name = ".".join(f"«{part}»" if not re.fullmatch(r"[A-Za-z_][\w']*", part) else part
                    for part in module.split("."))
    return f"`{name}" if kind == "one" else f".{kind} `{name}"


def _plan_lean(text: str, survivors: _Survivors, existed: set[str]) -> LakefileEdit:
    edit = LakefileEdit("lakefile.lean")
    package_dir = package_src_dir(text)
    replacements: list[tuple[int, int, str]] = []
    removed_targets: list[str] = []
    for declaration in _lean_declarations(text):
        name = str(declaration["name"])
        section = str(declaration["section"])
        src = re.search(r'srcDir[ \t]*:=[ \t]*"([^"]*)"[ \t]*(?:--.*)?$', section, re.MULTILINE)
        if src is None and re.search(r"(?m)^[ \t]+srcDir[ \t]*:=", section):
            # A computed source directory: its modules cannot be located here.
            continue
        src_dir = posixpath.join(package_dir, src.group(1) if src else ".")
        if declaration["kind"] == "lean_exe":
            root_field = _lean_field(section, "root")
            root = (_plain(root_field.group("value")[1:])
                    if root_field and root_field.group("value").startswith("`") else name)
            path = _module_file(src_dir, root)
            if path in existed and path not in survivors.files:
                edit.changes.append(f"lean_exe {name}: its root {root} was deleted; executable removed")
                replacements.append((int(declaration["start"]), int(declaration["end"]), ""))
                removed_targets.append(name)
            continue
        roots_field, globs_field = _lean_field(section, "roots"), _lean_field(section, "globs")
        dynamic = [key for key, found in (("roots", roots_field), ("globs", globs_field))
                   if found is None and re.search(rf"(?m)^[ \t]+{key}[ \t]*:=", section)]
        if dynamic:
            if _mentions_deleted(section, src_dir, survivors, existed) or _name_deleted(name, src_dir, survivors, existed):
                edit.unresolved.append(f"lean_lib {name}: {'/'.join(dynamic)} computed, not a literal; check it by hand")
            continue
        if globs_field is not None:
            items = _lean_array(globs_field.group("value"))
        elif roots_field is not None:
            items = _lean_array(roots_field.group("value"))
        else:
            items = [f"`{name}"]
        parsed = [_LEAN_GLOB.match(item) for item in items] if items is not None else None
        if parsed is None or not all(parsed):
            if (roots_field or globs_field) and _mentions_deleted(section, src_dir, survivors, existed):
                edit.unresolved.append(f"lean_lib {name}: roots/globs are not a plain #[...] list")
            continue
        current = [
            (match.group("kind") or "one", _plain(match.group("name")))
            for match in parsed if match
        ]
        if globs_field is None:
            current = [("one", module) for _kind, module in current]
        fixed, notes = _fix_globs(current, src_dir, survivors, existed)
        if not notes:
            continue
        edit.changes.extend(f"lean_lib {name}: {note}" for note in notes)
        indent = field_indent(section, str(declaration["indent"]))
        rendered = indent + "globs := #[" + ", ".join(_render_lean_glob(*glob) for glob in fixed) + "]\n"
        if globs_field is not None:
            section = section[: globs_field.start()] + rendered + section[globs_field.end():]
        else:
            header_end = section.index("\n") + 1 if "\n" in section else len(section)
            header = section[:header_end].rstrip("\n")
            tail = str(declaration["tail"])
            if re.fullmatch(r"[ \t]*(?:--.*)?", tail):
                header = header[: len(header) - len(tail)].rstrip() + " where" + tail
            elif not re.fullmatch(r"[ \t]+(?:where|\{)[ \t]*(?:--.*)?", tail):
                edit.unresolved.append(f"lean_lib {name}: declaration header not understood")
                edit.changes = [c for c in edit.changes if not c.startswith(f"lean_lib {name}:")]
                continue
            section = header + "\n" + rendered + section[header_end:]
        replacements.append((int(declaration["body_start"]), int(declaration["end"]), section))

    rewritten = text
    for start, end, section in sorted(replacements, reverse=True):
        rewritten = rewritten[:start] + section + rewritten[end:]
    if removed_targets:
        dangling = [target for target in removed_targets
                    if re.search(rf"`{re.escape(target)}\b", rewritten)]
        if dangling:
            edit.unresolved.append("the lakefile still refers to removed executable(s): " + ", ".join(dangling))
    if rewritten != text:
        edit.text = rewritten
    return edit


def _name_deleted(name: str, src_dir: str, survivors: _Survivors, existed: set[str]) -> bool:
    path = _module_file(src_dir, name)
    return path in existed and path not in survivors.files


def _mentions_deleted(section: str, src_dir: str, survivors: _Survivors, existed: set[str]) -> bool:
    for match in re.finditer(rf"`({_NAME})", section):
        path = _module_file(src_dir, _plain(match.group(1)))
        if path in existed and path not in survivors.files:
            return True
    return False


def lakefile_path(directory: Path) -> Path | None:
    """The lakefile Lake reads in ``directory``: `lakefile.lean` wins over `lakefile.toml`."""

    for name in ("lakefile.lean", "lakefile.toml"):
        if (directory / name).is_file():
            return directory / name
    return None


def _path_requires(directory: Path) -> list[str]:
    """``require … path`` targets of the package in ``directory``, as written."""

    lakefile = lakefile_path(directory)
    if lakefile is None:
        return []
    if lakefile.name == "lakefile.lean":
        return re.findall(r'(?m)^\s*require\s+\S+\s+from\s+"([^"]+)"', lakefile.read_text())
    try:
        requires = tomllib.loads(lakefile.read_text()).get("require") or []
    except tomllib.TOMLDecodeError:
        return []
    return [str(item["path"]) for item in requires
            if isinstance(item, dict) and isinstance(item.get("path"), str)]


def path_dependency_dirs(repo: Path) -> list[Path]:
    """Every package the project requires by path, transitively, resolved.

    A vendored package may itself require another by path (`vendor/A` needing
    `../B`); the manifest lists all of them as well.
    """

    repo = repo.resolve()
    found: list[Path] = []
    queue = [repo]
    manifest = repo / "lake-manifest.json"
    try:
        packages = json.loads(manifest.read_text()).get("packages", []) if manifest.is_file() else []
    except (OSError, ValueError):
        packages = []
    for package in packages:
        if isinstance(package, dict) and package.get("type") == "path" and package.get("dir"):
            target = (repo / str(package["dir"])).resolve()
            if target.is_dir() and target != repo and target not in found:
                found.append(target)
                queue.append(target)
    while queue:
        directory = queue.pop()
        for path in _path_requires(directory):
            target = (directory / path).resolve()
            if target.is_dir() and target != repo and target not in found:
                found.append(target)
                queue.append(target)
    return found


def path_dependencies(repo: Path) -> tuple[str, ...]:
    """Path dependencies inside ``repo``, relative to it, outermost directories only.

    They are dependencies vendored into the repository, not project sources.
    """

    repo = repo.resolve()
    inside = sorted(
        target.relative_to(repo).as_posix() for target in path_dependency_dirs(repo)
        if target.is_relative_to(repo)
    )
    outermost: list[str] = []
    for relative in inside:
        if not any(relative.startswith(parent + "/") for parent in outermost):
            outermost.append(relative)
    return tuple(outermost)


def plan(repo: Path, existed: set[str], surviving: set[str]) -> LakefileEdit | None:
    """The lakefile rewrite for a tree where only ``surviving`` of ``existed`` remain.

    Both sets hold repository-relative ``.lean`` paths; ``surviving`` includes
    every Lean file that stays, the challenge too.
    """

    survivors = _Survivors(surviving)
    lakefile = lakefile_path(repo)
    if lakefile is None:
        return None
    if lakefile.name == "lakefile.lean":
        return _plan_lean(lakefile.read_text(), survivors, existed)
    return _plan_toml(lakefile.read_text(), survivors, existed)

"""Comparator's verdict on the stripped tree, with the settings Palomar used.

Lean v4.35.0-rc2 and later ship `lake comparator`, the judge Palomar runs: every
theorem the config names must prove the challenge's statement, with no axiom
outside the permitted ones, and be accepted by Lean's kernel (and any external
kernels the config asks for, which ship in the toolchain's `bin`).

Older toolchains get Palomar's earlier judge: the standalone comparator at the
commit Palomar pinned, `lean4export` at the release tag of the project's own
Lean version, and the nanoda kernel at Palomar's commit when the config enables
it. They are built once, into `$XDG_CACHE_HOME/lean-strip/comparator-tools`.

Both judges sandbox the builds they run (`bwrap`, or `landrun` for the
standalone comparator). Where the sandbox cannot start (Ubuntu's AppArmor
default, a container), and always for the standalone comparator, the check runs
without it: lean-strip has already built the same code unsandboxed, so the
sandbox would protect against nothing here. The comparison itself is the same.
"""

from __future__ import annotations

import fcntl
import json
import os
import re
import shutil
import subprocess
import time
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from pathlib import Path
from typing import Any

from . import stacks
from .workspace import LocalWorkspace

_BWRAP_FAILURE = re.compile(r"^bwrap: |`bwrap`", re.MULTILINE)

# What Palomar's verification pipeline pinned before toolchains shipped
# `lake comparator` (PalomarRegistry/PalomarSubmission, .github/workflows/submission.yml).
COMPARATOR = ("https://github.com/leanprover/comparator.git", "575674928e239f5bc452aab72d1dd7b0f1326494")
NANODA = ("https://github.com/robsimmons/nanoda_lib.git", "68d5ca9db226849b41a6fff59d796ff19d0a8840")
LEAN4EXPORT = "https://github.com/leanprover/lean4export.git"
_TOOLCHAIN_TAG = re.compile(r"^leanprover/lean4:(v\d+\.\d+\.\d+(?:-rc\d+)?)$")


class ToolError(RuntimeError):
    """A judge's tool could not be obtained or built."""


def run_comparator(
    ws: LocalWorkspace, config: Path, timeout: int, progress: Callable[[str], None],
) -> dict[str, Any]:
    """The judge's verdict on the workspace: accepted, rejected, error or unavailable."""

    started = time.perf_counter()
    usage = ws.execute(["lake", "comparator", "--help"], timeout=120)
    try:
        if "Judge a solution" in usage["output"]:
            verdict = _builtin(ws, config, timeout, progress)
        else:
            verdict = _standalone(ws, config, timeout, progress)
    except ToolError as error:
        verdict = {"status": "unavailable", "reason": str(error)}
    verdict["seconds"] = round(time.perf_counter() - started, 1)
    return verdict


def _toolchain_bin(ws: LocalWorkspace) -> Path | None:
    prefix = ws.execute(["lean", "--print-prefix"], timeout=120)["output"].strip().splitlines()
    return Path(prefix[-1]) / "bin" if prefix else None


@contextmanager
def _environment(ws: LocalWorkspace, extra: dict[str, str]) -> Iterator[None]:
    """``extra`` in the workspace environment; the toolchain's `bin` last on PATH.

    External kernels (`nanoda_bin`, ...) ship next to `lean`, and elan does not
    proxy them. Last, so a stack shim's `lean` still wins.
    """

    saved = dict(ws.environment)
    toolchain_bin = _toolchain_bin(ws)
    if toolchain_bin is not None:
        ws.environment["PATH"] = os.pathsep.join([saved.get("PATH", ""), str(toolchain_bin)])
    ws.environment.update(extra)
    try:
        yield
    finally:
        ws.environment.clear()
        ws.environment.update(saved)


def _builtin(ws: LocalWorkspace, config: Path, timeout: int, progress: Callable[[str], None]) -> dict[str, Any]:
    command = ["lake", "comparator", "--config", str(config)]
    with _environment(ws, {}):
        result = ws.execute_stream(command, timeout=timeout, on_output=progress)
        sandbox = True
        if result["returncode"] != 0 and _BWRAP_FAILURE.search(result["output"]):
            progress("the bwrap sandbox cannot start here; judging without it")
            sandbox = False
            result = ws.execute_stream(command + ["--inadvisably-no-sandbox"],
                                       timeout=timeout, on_output=progress)
    return _verdict("lake comparator", result, sandbox, {0: "accepted", 1: "rejected"})


def _standalone(ws: LocalWorkspace, config: Path, timeout: int, progress: Callable[[str], None]) -> dict[str, Any]:
    toolchain = (ws.root / "lean-toolchain").read_text().strip() if (ws.root / "lean-toolchain").is_file() else ""
    match = _TOOLCHAIN_TAG.match(toolchain)
    if match is None:
        raise ToolError(f"no lean4export release matches the toolchain {toolchain or '(none)'}")
    tools = Path(ws.environment.get("XDG_CACHE_HOME") or Path.home() / ".cache") / "lean-strip" / "comparator-tools"
    build_env = stacks.without_stack(ws.environment)
    comparator = _comparator(tools, build_env, progress)
    lean4export = _lean4export(tools, match.group(1), toolchain, build_env, progress)
    settings = json.loads((ws.root / config).read_text())
    extra = {
        "LEAN_STRIP_COMPARATOR": str(comparator / ".lake" / "build" / "bin" / "comparator"),
        "COMPARATOR_LEAN4EXPORT": str(lean4export),
        # Comparator's own passthrough for systems without landrun.
        "COMPARATOR_LANDRUN": str(comparator / "scripts" / "fake-landrun.sh"),
    }
    if settings.get("enable_nanoda") or settings.get("external_kernels"):
        extra["COMPARATOR_NANODA"] = str(_nanoda(tools, build_env, progress))
    # Absolute paths travel in the environment: the workspace maps `/tmp/...` arguments.
    command = ["lake", "env", "sh", "-c", f'exec "$LEAN_STRIP_COMPARATOR" "{config}"']
    with _environment(ws, extra):
        result = ws.execute_stream(command, timeout=timeout, on_output=progress)
    return _verdict(f"comparator {COMPARATOR[1][:8]}", result, False, {0: "accepted"},
                    failure="rejected")


def _verdict(judge: str, result: dict[str, Any], sandbox: bool, statuses: dict[int, str],
             failure: str = "error") -> dict[str, Any]:
    return {
        "status": statuses.get(result["returncode"], failure),
        "judge": judge,
        "sandbox": sandbox,
        "returncode": result["returncode"],
        "output_tail": "\n".join(result["output"].strip().splitlines()[-25:]),
    }


@contextmanager
def _locked(directory: Path) -> Iterator[None]:
    """One builder per tool directory, across concurrent lean-strip runs."""

    directory.parent.mkdir(parents=True, exist_ok=True)
    with open(directory.with_name(directory.name + ".lock"), "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        yield


def _run(argv: list[str], cwd: Path, env: dict[str, str], what: str) -> None:
    result = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True, check=False)
    if result.returncode != 0:
        tail = "\n".join((result.stdout + result.stderr).strip().splitlines()[-5:])
        raise ToolError(f"{what} failed: {tail}")


def _checkout(url: str, revision: str, directory: Path, env: dict[str, str], tag: bool = False) -> None:
    if directory.is_dir():
        return
    staging = directory.with_name(directory.name + ".partial")
    shutil.rmtree(staging, ignore_errors=True)
    if tag:
        _run(["git", "clone", "-q", "--depth", "1", "--branch", revision, url, str(staging)],
             directory.parent, env, f"cloning {url} at {revision}")
    else:
        _run(["git", "clone", "-q", "--filter=blob:none", url, str(staging)], directory.parent, env, f"cloning {url}")
        _run(["git", "checkout", "-q", revision], staging, env, f"checking out {revision}")
    staging.rename(directory)


def _comparator(tools: Path, env: dict[str, str], progress: Callable[[str], None]) -> Path:
    directory = tools / f"comparator-{COMPARATOR[1][:12]}"
    binary = directory / ".lake" / "build" / "bin" / "comparator"
    with _locked(directory):
        if not binary.is_file():
            progress(f"building comparator {COMPARATOR[1][:8]} (once)")
            _checkout(*COMPARATOR, directory, env)
            _run(["lake", "build", "comparator"], directory, env, "building comparator")
    return directory


def _release_tag(tag: str, env: dict[str, str]) -> str:
    """The lean4export release to build for Lean ``tag``, as Palomar chose it.

    The exact release, or for a stable patch release without one (v4.33.1),
    the release line's patch-zero tag (v4.33.0), rebuilt with the project's
    own toolchain. PALOMAR-2026-09-14-000011 was checked that way.
    """

    listed = subprocess.run(["git", "ls-remote", "--tags", LEAN4EXPORT, f"refs/tags/{tag}"],
                            env=env, capture_output=True, text=True, check=False)
    if listed.returncode != 0:
        raise ToolError(f"could not list lean4export releases: {listed.stderr.strip()[-200:]}")
    if listed.stdout.strip():
        return tag
    match = re.fullmatch(r"v(\d+)\.(\d+)\.(\d+)", tag)
    if match is None or match.group(3) == "0":
        raise ToolError(f"lean4export has no release {tag}")
    return f"v{match.group(1)}.{match.group(2)}.0"


def _lean4export(tools: Path, tag: str, toolchain: str, env: dict[str, str],
                 progress: Callable[[str], None]) -> Path:
    directory = tools / f"lean4export-{tag}"
    binary = directory / ".lake" / "build" / "bin" / "lean4export"
    with _locked(directory):
        if not binary.is_file():
            release = _release_tag(tag, env)
            progress(f"building lean4export {release} for {tag} (once per Lean version)")
            _checkout(LEAN4EXPORT, release, directory, env, tag=True)
            pinned = (directory / "lean-toolchain").read_text().strip()
            if pinned != f"leanprover/lean4:{release}":
                raise ToolError(f"lean4export {release} targets {pinned}")
            _run(["lake", "build", "lean4export"], directory, {**env, "ELAN_TOOLCHAIN": toolchain},
                 f"building lean4export {release} with {toolchain}")
    return binary


def _nanoda(tools: Path, env: dict[str, str], progress: Callable[[str], None]) -> Path:
    directory = tools / f"nanoda-{NANODA[1][:12]}"
    binary = directory / "target" / "release" / "nanoda_bin"
    with _locked(directory):
        if not binary.is_file():
            progress(f"building the nanoda kernel {NANODA[1][:8]} (once)")
            cargo = _cargo(tools, env, progress)
            _checkout(*NANODA, directory, env)
            _run([str(cargo), "build", "--release", "--locked"], directory,
                 {**env, **_rust_env(tools)}, "building nanoda")
    return binary


def _rust_env(tools: Path) -> dict[str, str]:
    return {"RUSTUP_HOME": str(tools / "rustup"), "CARGO_HOME": str(tools / "cargo")}


def _cargo(tools: Path, env: dict[str, str], progress: Callable[[str], None]) -> Path:
    """`cargo` from PATH, or a minimal Rust toolchain installed into the cache."""

    if (found := shutil.which("cargo", path=env.get("PATH"))):
        return Path(found)
    cargo = tools / "cargo" / "bin" / "cargo"
    if not cargo.is_file():
        progress("installing a minimal Rust toolchain for nanoda (once)")
        installer = tools / "rustup-init.sh"
        _run(["curl", "-sSf", "-o", str(installer), "https://sh.rustup.rs"], tools, env, "downloading rustup")
        _run(["sh", str(installer), "-y", "--no-modify-path", "--profile", "minimal"], tools,
             {**env, **_rust_env(tools)}, "installing Rust")
    return cargo

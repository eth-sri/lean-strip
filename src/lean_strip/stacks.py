"""Smaller Lean thread stacks, for builds under a finite address space.

Lean reserves a 1 GiB stack for every thread, and while it elaborates a file it
keeps one thread alive per command. Under `ulimit -v` those reservations alone
exhaust the address space although almost none of it is used: with a 128 GiB
limit, a file of about 115 commands after `import Mathlib.Data.Real.Basic`
fails with "failed to create thread" at 2 GiB of memory (PALOMAR-2026-08-27-000017
is a list of 220 `#check`s). Parallel elaboration adds a thread per worker.

`lean --tstack` sets the stack size, but Lake cannot pass it to the `lean`
processes it starts, and under elan it ignores `LEAN` and `LEAN_SYSROOT`. So a
shim toolchain goes first on PATH: the real toolchain's files, except a
`bin/lean` that adds `--tstack` and a copy of `bin/lake`, which looks for Lean
next to itself. Shims are cached per toolchain and stack size.
"""

from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

# The steps tried after a thread failure, largest first; Lean's own is 1 GiB.
STACK_STEPS_KIB = (256 * 1024, 64 * 1024, 16 * 1024)
# Records the current step in a build environment.
STACK_VARIABLE = "LEAN_STRIP_STACK_KIB"


def current_stack_kib(env: dict[str, str]) -> int | None:
    value = env.get(STACK_VARIABLE)
    return int(value) if value else None


def _cache(env: dict[str, str]) -> Path:
    return Path(env.get("XDG_CACHE_HOME") or Path.home() / ".cache") / "lean-strip" / "lean-stacks"


def without_stack(env: dict[str, str]) -> dict[str, str]:
    """``env`` without a shim: for building tools that pin a Lean of their own."""

    path = [entry for entry in env.get("PATH", "").split(os.pathsep)
            if entry and not entry.startswith(str(_cache(env)) + os.sep)]
    return {key: value for key, value in env.items() if key != STACK_VARIABLE} | {"PATH": os.pathsep.join(path)}


def use_stack(env: dict[str, str], project: Path, stack_kib: int) -> None:
    """Make every `lake` and `lean` started with ``env`` in ``project`` use ``stack_kib``."""

    cache = _cache(env)
    # Without an earlier shim, so that `lean` is the real one.
    plain = without_stack(env)
    path = plain["PATH"].split(os.pathsep) if plain["PATH"] else []
    sysroot = Path(subprocess.run(
        ["lean", "--print-prefix"], cwd=project, env=plain,
        capture_output=True, text=True, check=True,
    ).stdout.strip())
    bin_dir = _shim(sysroot, cache, stack_kib) / "bin"
    env["PATH"] = os.pathsep.join([str(bin_dir), *path])
    # Set by elan's proxies; either would point Lake back at the real toolchain.
    env.pop("LEAN_SYSROOT", None)
    env.pop("LEAN", None)
    env[STACK_VARIABLE] = str(stack_kib)


def _shim(sysroot: Path, cache: Path, stack_kib: int) -> Path:
    digest = hashlib.sha256(str(sysroot).encode()).hexdigest()[:12]
    target = cache / f"{sysroot.name}-{digest}-{stack_kib // 1024}m"
    if (target / "bin" / "lean").is_file():
        return target
    cache.mkdir(parents=True, exist_ok=True)
    # Concurrent runs build their own copy and the first rename wins.
    staging = Path(tempfile.mkdtemp(prefix=".shim-", dir=cache))
    (staging / "bin").mkdir()
    for entry in sysroot.iterdir():
        if entry.name != "bin":
            (staging / entry.name).symlink_to(entry)
    for entry in (sysroot / "bin").iterdir():
        if entry.name == "lake":
            shutil.copy2(entry, staging / "bin" / "lake")
        elif entry.name != "lean":
            (staging / "bin" / entry.name).symlink_to(entry)
    lean = staging / "bin" / "lean"
    lean.write_text(f'#!/bin/sh\nexec "{sysroot / "bin" / "lean"}" --tstack={stack_kib} "$@"\n')
    lean.chmod(0o755)
    try:
        staging.rename(target)
    except OSError:  # another run created it first
        shutil.rmtree(staging, ignore_errors=True)
    return target

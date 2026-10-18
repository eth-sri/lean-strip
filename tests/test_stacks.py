import os
import subprocess

from lean_strip import stacks


def _toolchain(root):
    """A fake toolchain whose `lean` prints its prefix or its arguments."""

    sysroot = root / "toolchain"
    (sysroot / "bin").mkdir(parents=True)
    (sysroot / "lib").mkdir()
    lean = sysroot / "bin" / "lean"
    lean.write_text(f'#!/bin/sh\n[ "$1" = --print-prefix ] && echo {sysroot} && exit\necho "$@"\n')
    lean.chmod(0o755)
    (sysroot / "bin" / "lake").write_text("lake binary")
    return sysroot


def test_shim_passes_the_stack_to_every_lean(tmp_path):
    # PALOMAR-2026-08-27-000017: Lake cannot pass `--tstack` itself.
    sysroot = _toolchain(tmp_path)
    env = {"PATH": f"{sysroot / 'bin'}{os.pathsep}/usr/bin:/bin", "XDG_CACHE_HOME": str(tmp_path / "cache"),
           "LEAN_SYSROOT": str(sysroot)}
    stacks.use_stack(env, tmp_path, 64 * 1024)
    shim = env["PATH"].split(os.pathsep)[0]
    assert "LEAN_SYSROOT" not in env and stacks.current_stack_kib(env) == 64 * 1024
    run = subprocess.run(["lean", "Foo.lean"], env=env, capture_output=True, text=True, check=True)
    assert run.stdout.strip() == "--tstack=65536 Foo.lean"
    # Lake finds Lean next to itself, so it must be a copy, not a link.
    assert not os.path.islink(os.path.join(shim, "lake"))
    assert os.path.islink(os.path.join(os.path.dirname(shim), "lib"))

    stacks.use_stack(env, tmp_path, 16 * 1024)
    path = env["PATH"].split(os.pathsep)
    assert path[0].endswith("-16m/bin") and shim not in path
    run = subprocess.run(["lean", "Foo.lean"], env=env, capture_output=True, text=True, check=True)
    assert run.stdout.strip() == "--tstack=16384 Foo.lean"

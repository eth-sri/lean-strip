from pathlib import Path

from lean_strip import verify


class Workspace:
    def __init__(self, help_text, results, root=Path("/nonexistent")):
        self.environment = {"PATH": "/usr/bin"}
        self.root = root
        self.help_text, self.results, self.calls = help_text, list(results), []

    def execute(self, argv, timeout=None):
        if argv[:2] == ["lake", "comparator"]:
            return {"returncode": 0, "output": self.help_text}
        return {"returncode": 0, "output": "/elan/toolchains/v4.35.0-rc3\n"}

    def execute_stream(self, argv, timeout=None, on_output=None):
        self.calls.append((argv, dict(self.environment)))
        return self.results.pop(0)


def test_falls_back_without_the_sandbox_where_bwrap_cannot_start():
    ws = Workspace("Judge a solution against a challenge", [
        {"returncode": 1, "output": "bwrap: setting up uid map: Permission denied\nerror: Child exited with 1"},
        {"returncode": 0, "output": "Lean default kernel accepts the solution\nYour solution is okay!"},
    ])
    verdict = verify.run_comparator(ws, Path("c.json"), 60, lambda _line: None)
    assert verdict["status"] == "accepted" and verdict["sandbox"] is False
    assert ws.calls[1][0][-1] == "--inadvisably-no-sandbox"
    # External kernels are found in the toolchain's bin; PATH is restored afterwards.
    assert ws.calls[0][1]["PATH"] == "/usr/bin:/elan/toolchains/v4.35.0-rc3/bin"
    assert ws.environment == {"PATH": "/usr/bin"}


def test_a_rejection_is_reported_as_such():
    ws = Workspace("Judge a solution against a challenge", [
        {"returncode": 1, "output": "error: theorem `t` does not match the challenge"},
    ])
    verdict = verify.run_comparator(ws, Path("c.json"), 60, lambda _line: None)
    assert verdict["status"] == "rejected" and verdict["sandbox"] is True and len(ws.calls) == 1


def test_older_toolchains_get_palomars_standalone_comparator(tmp_path, monkeypatch):
    # Toolchains before v4.35.0-rc2 have no `lake comparator`.
    (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.30.0-rc1\n")
    (tmp_path / "c.json").write_text('{"enable_nanoda": true}')
    built = []
    monkeypatch.setattr(verify, "_comparator", lambda tools, env, progress: tools / "comparator")
    monkeypatch.setattr(verify, "_lean4export", lambda tools, tag, toolchain, env, progress:
                        built.append((tag, toolchain)) or tools / "lean4export")
    monkeypatch.setattr(verify, "_nanoda", lambda tools, env, progress: tools / "nanoda_bin")
    ws = Workspace("USAGE:\n  lake [OPTIONS] <COMMAND>", [{"returncode": 0, "output": "Your solution is okay!"}],
                   root=tmp_path)
    ws.environment["XDG_CACHE_HOME"] = "/cache"
    verdict = verify.run_comparator(ws, Path("c.json"), 60, lambda _line: None)
    assert verdict["status"] == "accepted" and verdict["judge"] == "comparator 57567492"
    assert built == [("v4.30.0-rc1", "leanprover/lean4:v4.30.0-rc1")]
    argv, env = ws.calls[0]
    # No absolute path in the arguments: the workspace rewrites `/tmp/...`.
    assert argv == ["lake", "env", "sh", "-c", 'exec "$LEAN_STRIP_COMPARATOR" "c.json"']
    tools = "/cache/lean-strip/comparator-tools"
    assert env["LEAN_STRIP_COMPARATOR"] == f"{tools}/comparator/.lake/build/bin/comparator"
    assert env["COMPARATOR_LANDRUN"] == f"{tools}/comparator/scripts/fake-landrun.sh"
    assert env["COMPARATOR_NANODA"] == f"{tools}/nanoda_bin"


def test_a_toolchain_without_a_lean4export_release_is_reported(tmp_path):
    (tmp_path / "lean-toolchain").write_text("leanprover/lean4:nightly-2026-01-01\n")
    ws = Workspace("USAGE:", [], root=tmp_path)
    verdict = verify.run_comparator(ws, Path("c.json"), 60, lambda _line: None)
    assert verdict["status"] == "unavailable" and "lean4export" in verdict["reason"]


def test_patch_releases_fall_back_to_the_release_lines_lean4export(monkeypatch):
    # PALOMAR-2026-09-14-000011 (v4.33.1) was checked with lean4export v4.33.0.
    tags = {"refs/tags/v4.30.0-rc1", "refs/tags/v4.33.0"}

    def ls_remote(argv, **_kwargs):
        listed = f"abc\t{argv[-1]}\n" if argv[-1] in tags else ""
        return verify.subprocess.CompletedProcess(argv, 0, listed, "")

    monkeypatch.setattr(verify.subprocess, "run", ls_remote)
    assert verify._release_tag("v4.30.0-rc1", {}) == "v4.30.0-rc1"
    assert verify._release_tag("v4.33.1", {}) == "v4.33.0"
    for missing in ("v4.36.0-rc1", "v4.36.0"):
        try:
            verify._release_tag(missing, {})
        except verify.ToolError:
            continue
        raise AssertionError(missing)

from types import SimpleNamespace

from lean_strip import engine


class FakeWorkspace:
    """Files in memory; `lake build` fails while any file differs from `good`."""

    def __init__(self, files, good, report_only=None):
        self.files, self.good = dict(files), good
        self.report_only = report_only  # errors are only reported in these files

    def host_path(self, path):
        return SimpleNamespace(is_file=lambda: path in self.files)

    def snapshot(self, paths):
        return {path: self.files[path] for path in paths}

    def write_text(self, path, content):
        self.files[path] = content

    def apply_source_tree(self, current, desired):
        self.files = dict(desired)


def _patch(monkeypatch, ws):
    def build(_ws, _target, _timeout, _progress):
        bad = sorted(p for p, text in ws.files.items() if text != ws.good.get(p))
        if not bad:
            return True, "Build completed successfully"
        shown = [p for p in bad if ws.report_only is None or p in ws.report_only]
        return False, "\n".join(f"error: {p.removeprefix('/testbed/')}:1:1: boom" for p in shown)
    monkeypatch.setattr(engine, "_lake_build", build)
    monkeypatch.setattr(engine, "_list_project_lean_files", lambda ws: sorted(ws.files))


STAGE = SimpleNamespace(progress=lambda _line: None)


def test_other_errors_fail_without_restoring_anything(monkeypatch):
    # A missed dependency must surface as a failure, not be papered over by
    # restoring files or keeping more declarations.
    raw = {"/testbed/A.lean": "a full", "/testbed/B.lean": "b full"}
    ws = FakeWorkspace({"/testbed/A.lean": "a stripped", "/testbed/B.lean": "b stripped"},
                       good={"/testbed/A.lean": "a full", "/testbed/B.lean": "b stripped"})
    _patch(monkeypatch, ws)
    output = "error: A.lean:3:4: Unknown identifier `helper`"
    result = engine._recover_build(ws, "+S", 60, raw, output, STAGE)
    assert not result["ok"] and result["rounds"] == 0
    assert result["unrepaired_errors"] == [output]
    assert ws.files == {"/testbed/A.lean": "a stripped", "/testbed/B.lean": "b stripped"}


def test_a_build_failure_without_a_lean_error_fails(monkeypatch):
    raw = {"/testbed/A.lean": "a full"}
    ws = FakeWorkspace({"/testbed/A.lean": "a stripped"}, good=raw, report_only=set())
    _patch(monkeypatch, ws)
    result = engine._recover_build(ws, "+S", 60, raw, "error: build failed", STAGE)
    assert not result["ok"] and ws.files == {"/testbed/A.lean": "a stripped"}
    assert result["unrepaired_errors"][0].startswith("the build failed without a Lean error")


def test_grind_failures_restore_only_their_file(monkeypatch):
    # `grind +suggestions` searches the environment, which the strip shrank.
    raw = {"/testbed/A.lean": "a full", "/testbed/B.lean": "b full"}
    ws = FakeWorkspace({"/testbed/A.lean": "a stripped", "/testbed/B.lean": "b stripped"},
                       good={"/testbed/A.lean": "a full", "/testbed/B.lean": "b stripped"})
    _patch(monkeypatch, ws)
    output = "error: A.lean:3:4: `grind` failed\ncase grind\n  h : False"
    result = engine._recover_build(ws, "+S", 60, raw, output, STAGE)
    assert result["ok"] and result["grind_restored_files"] == ["/testbed/A.lean"]
    assert ws.files["/testbed/B.lean"] == "b stripped"
    assert engine._fallback_summary(result) == "restored 1 file(s) unstripped where grind failed (1 round)"


def test_a_grind_failure_next_to_another_error_fails(monkeypatch):
    raw = {"/testbed/A.lean": "a full", "/testbed/B.lean": "b full"}
    ws = FakeWorkspace({"/testbed/A.lean": "a stripped", "/testbed/B.lean": "b stripped"}, good=raw)
    _patch(monkeypatch, ws)
    output = ("error: A.lean:3:4: `grind` failed\n"
              "error: B.lean:7:2: Unknown constant `gone`")
    result = engine._recover_build(ws, "+S", 60, raw, output, STAGE)
    assert not result["ok"] and result["grind_restored_files"] == []
    assert result["unrepaired_errors"] == ["error: B.lean:7:2: Unknown constant `gone`"]


def test_report_forgets_drops_in_restored_files():
    report = {"dropped_decls": ["A.x", "B.y"]}
    fallback = {"grind_restored_files": ["/testbed/A.lean"]}
    engine._forget_restored_drops(report, fallback, {"A.x": "A", "B.y": "B"},
                                  {"A": "/testbed/A.lean", "B": "/testbed/B.lean"})
    assert report["dropped_decls"] == ["B.y"]


def test_error_blocks_keep_the_explanation():
    output = "\n".join([
        "✖ [3/4] Building M",
        "error: M.lean:289:8: failed to synthesize",
        "  Module.Finite K L",
        "",
        "Additional diagnostic information may be available.",
        "✔ [4/4] Built N",
        "error: build failed",
    ])
    assert engine._error_blocks(output) == [
        "error: M.lean:289:8: failed to synthesize\n  Module.Finite K L"
    ]


def _thread_failure_workspace(monkeypatch, succeeds):
    """A workspace whose builds fail with a thread failure until ``succeeds``."""

    calls = []
    monkeypatch.setattr(engine.stacks, "use_stack", lambda env, _project, kib: env.update(
        {engine.stacks.STACK_VARIABLE: str(kib)}))

    class Workspace:
        root = None
        environment = {"LEAN_NUM_THREADS": "8"}

        def execute_stream(self, argv, timeout, on_output):
            env = self.environment
            state = (int(env["LEAN_NUM_THREADS"]), engine.stacks.current_stack_kib(env))
            calls.append(state)
            if succeeds(*state):
                return {"returncode": 0, "output": "Build completed successfully"}
            return {"returncode": 1, "output": "libc++abi: ... failed to create thread\nerror: build failed"}

    return Workspace(), calls


def test_thread_failures_retry_with_smaller_stacks(monkeypatch):
    # PALOMAR-2026-08-27-000017: Lean keeps a thread with a 1 GiB stack per
    # command, so 220 `#check`s exhaust a 128 GiB address space at any LEAN_NUM_THREADS.
    ws, calls = _thread_failure_workspace(
        monkeypatch, lambda _threads, kib: kib is not None and kib <= 64 * 1024)
    ok, _ = engine._lake_build(ws, "+Solution", 60, lambda _line: None)
    assert ok and calls == [(8, None), (8, 256 * 1024), (8, 64 * 1024)]


def test_thread_failures_finally_halve_the_threads(monkeypatch):
    ws, calls = _thread_failure_workspace(monkeypatch, lambda threads, _kib: threads == 1)
    ok, _ = engine._lake_build(ws, "+Solution", 60, lambda _line: None)
    stack = 16 * 1024
    assert ok and calls == [(8, None), (8, 256 * 1024), (8, 64 * 1024), (8, stack),
                            (4, stack), (2, stack), (1, stack)]


def test_grind_edits_failing_the_aggregate_build_are_reverted(monkeypatch):
    # PALOMAR-2026-09-14-000008: an explicit lemma was redundant in the full tree.
    raw = {"/testbed/A.lean": "by grind +suggestions", "/testbed/B.lean": "by grind +suggestions"}
    normalized = {"/testbed/A.lean": "by grind [Equiv.trans_apply]", "/testbed/B.lean": "by grind [ok]"}
    ws = FakeWorkspace(normalized, good={"/testbed/A.lean": raw["/testbed/A.lean"],
                                         "/testbed/B.lean": "by grind [ok]"})
    _patch(monkeypatch, ws)
    normalization = {"files": [{"path": "/testbed/A.lean", "calls": [{"status": "normalized_replay_passed"}]}]}
    ok, _ = engine._revert_failing_grind_files(
        ws, "+S", 60, raw, normalized, normalization, "error: A.lean:91:9: this parameter is redundant", STAGE)
    assert ok and normalized["/testbed/A.lean"] == raw["/testbed/A.lean"]
    assert normalized["/testbed/B.lean"] == "by grind [ok]"
    assert normalization["retained_failed_files"] == ["/testbed/A.lean"]
    assert normalization["files"][0]["calls"][0]["persisted_after_file_decision"] is False


def test_private_module_lint_is_silenced_not_restored(monkeypatch):
    # PALOMAR-2026-09-18-000005: stripping left only private declarations;
    # under warningAsError the linter failed the build.
    raw = {"/testbed/P.lean": "module\n\npublic import A\n\npublic def x := 1\nprivate def y := 2\n"}
    stripped = "module\n\npublic import A\n\nprivate def y := 2\n"
    ws = FakeWorkspace({"/testbed/P.lean": stripped}, good={})
    ws.good["/testbed/P.lean"] = engine._silence_private_module_linter(stripped)
    _patch(monkeypatch, ws)
    output = "error: P.lean:1:0: The current module only contains private declarations."
    result = engine._recover_build(ws, "+S", 60, raw, output, STAGE)
    assert result["ok"] and result["grind_restored_files"] == []
    assert result["private_module_lint_silenced"] == ["/testbed/P.lean"]
    assert ws.files["/testbed/P.lean"] == (
        "module\n\npublic import A\n\nset_option linter.privateModule false\n\nprivate def y := 2\n")


def test_files_left_with_only_private_declarations_silence_the_linter():
    # PALOMAR-2026-09-17-000001: the strip dropped the only public theorem.
    originals = {"/testbed/A.lean": "module\n\nprivate theorem h : True := trivial\ntheorem t : True := h\n",
                 "/testbed/B.lean": "theorem u : True := trivial\ntheorem v : True := trivial\n"}
    desired = {"/testbed/A.lean": "module\n\nprivate theorem h : True := trivial\n",
               "/testbed/B.lean": "theorem u : True := trivial\n"}
    rows = [{"name": "_private.A.0.h", "module": "A", "keep": True},
            {"name": "t", "module": "A", "keep": False},
            {"name": "u", "module": "B", "keep": True},
            {"name": "v", "module": "B", "keep": False}]
    out, silenced = engine._silence_private_only_modules(
        desired, originals, rows, {"A": "/testbed/A.lean", "B": "/testbed/B.lean"})
    assert silenced == ["/testbed/A.lean"]
    assert out["/testbed/A.lean"].startswith("module\n\nset_option linter.privateModule false\n")
    assert out["/testbed/B.lean"] == desired["/testbed/B.lean"]


def test_heartbeats_go_on_the_whole_declaration_command():
    text = "\n".join([
        "theorem a : True := trivial",
        "",
        "omit [CharZero F] in",
        "/-- doc",
        "  more -/",
        "@[simp]",
        "theorem det₂_eq_inv : True := by",
        "  trivial",
    ])
    anchor = "theorem det₂_eq_inv : True := by\n  trivial"
    raised = engine._with_heartbeats(text, anchor, "maxHeartbeats", 400000)
    assert raised.split("\n")[2:4] == ["set_option maxHeartbeats 400000 in", "omit [CharZero F] in"]
    # A second doubling replaces the setting instead of stacking another.
    again = engine._with_heartbeats(raised, anchor, "maxHeartbeats", 800000)
    assert again.count("set_option") == 1 and "set_option maxHeartbeats 800000 in" in again


def test_heartbeat_timeouts_get_twice_the_limit_not_a_restore(monkeypatch):
    # PALOMAR-2026-10-05-000007: the stripped tree made one proof need 2x the
    # default heartbeats; restoring files instead cascaded over eight files.
    stripped = "theorem keep : True := trivial\n\n/-- doc -/\ntheorem slow : True := by\n  trivial\n"
    good = stripped.replace("/-- doc -/", "set_option maxHeartbeats 400000 in\n/-- doc -/")
    raw = {"/testbed/A.lean": "theorem dropped : True := trivial\n" + stripped}
    ws = FakeWorkspace({"/testbed/A.lean": stripped}, good={"/testbed/A.lean": good})
    _patch(monkeypatch, ws)
    output = ("error: A.lean:4:0: (deterministic) timeout at `whnf`, "
              "maximum number of heartbeats (200000) has been reached")
    result = engine._recover_build(ws, "+S", 60, raw, output, STAGE)
    assert result["ok"] and result["rounds"] == 1 and result["grind_restored_files"] == []
    assert result["heartbeats"] == [{"path": "/testbed/A.lean", "declaration": "theorem slow : True := by trivial",
                                     "option": "maxHeartbeats", "value": 400000}]
    assert engine._fallback_summary(result) == "raised heartbeats on 1 declaration(s) (1 round)"


def test_type_class_timeouts_raise_the_synthesis_limit():
    # PALOMAR-2026-09-28-000002.
    current = {"/testbed/A.lean": "theorem t :\n    True := by\n  exact inst\n"}
    block = ("error: A.lean:3:2: failed to synthesize\n  Foo\n(deterministic) timeout at `typeclass`, "
             "maximum number of heartbeats (20000) has been reached")
    assert engine._heartbeat_timeout(block, current) == (
        "/testbed/A.lean", "theorem t :\n    True := by", "synthInstance.maxHeartbeats", 40000)
    # Past 8x Lean's default, it is not a matter of speed any more.
    assert engine._heartbeat_timeout(block.replace("(20000)", "(160000)"), current) is None


def test_timeouts_reported_at_a_docstring_belong_to_the_declaration_below():
    # PALOMAR-2026-10-05-000007: Lean put the error on the docstring line of
    # `det₂_eq_inv`; the previous theorem got the heartbeats instead.
    current = {"/testbed/A.lean": "\n".join([
        "theorem pairingW₂_rho : True := by",
        "  trivial",
        "",
        "/-- doc -/",
        "theorem det₂_eq_inv : True := by",
        "  trivial",
    ])}
    block = ("error: A.lean:4:0: (deterministic) timeout at `whnf`, "
             "maximum number of heartbeats (200000) has been reached")
    path, anchor, option, value = engine._heartbeat_timeout(block, current)
    assert anchor.startswith("theorem det₂_eq_inv")


def test_a_bare_theorem_keyword_is_anchored_by_its_name():
    # PALOMAR-2026-09-28-000002 writes `theorem` alone on a line.
    text = "theorem\n    first : True := trivial\n\ntheorem\n    second : True := trivial\n"
    raised = engine._with_heartbeats(text, "theorem\n    second : True := trivial",
                                     "synthInstance.maxHeartbeats", 40000)
    assert raised.split("\n")[3] == "set_option synthInstance.maxHeartbeats 40000 in"


def test_build_outputs_of_deleted_modules_are_removed(tmp_path, monkeypatch):
    # PALOMAR-2026-09-25-000018: the stale `Main.olean` let the stripped tree
    # build although `Main.lean` was gone; `vendor/leancert/Main.lean` is a
    # dependency's file and does not count.
    root = tmp_path / "work"
    lib = root / ".lake" / "build" / "lib" / "lean"
    (lib / "Sub").mkdir(parents=True)
    for name in ("Main.olean", "Main.ilean", "Main.trace", "Kept.olean", "Sub/Gone.olean", "Sub/Gone.olean.private"):
        (lib / name).write_text("")
    (root / "Kept.lean").write_text("")
    (root / "vendor" / "leancert").mkdir(parents=True)
    (root / "vendor" / "leancert" / "Main.lean").write_text("")
    ws = SimpleNamespace(root=root, project_skip=("vendor/leancert",),
                         host_path=lambda path: root / path.removeprefix("/testbed").lstrip("/"))
    monkeypatch.setattr(engine, "project_source_dirs", lambda _ws: ["/testbed/vendor/leancert", "/testbed"])
    assert engine._remove_stale_build_outputs(ws) == ["Main", "Sub.Gone"]
    assert sorted(p.name for p in lib.rglob("*") if p.is_file()) == ["Kept.olean"]

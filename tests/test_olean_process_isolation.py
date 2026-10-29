"""Root batches release Lean imports and share a single extraction budget."""

import json
import os
import signal
import sys
import time

import pytest

from lean_strip._pipeline.preprocessing import dependency_graph, olean
from lean_strip.workspace import LocalWorkspace


@pytest.fixture
def workspace(tmp_path):
    project = tmp_path / "project"
    project.mkdir()
    binaries = tmp_path / "bin"
    binaries.mkdir()
    lake = binaries / "lake"
    lake.write_text(f"#!{sys.executable}\n" + r'''
import os, subprocess, sys, time
from pathlib import Path
assert sys.argv[1] == 'env'
child = subprocess.Popen(sys.argv[2:])
if os.environ.get('FAIL_LAUNCHER'):
    calls = Path(os.environ['CALLS'])
    while not (calls.exists() and calls.stat().st_size):
        time.sleep(0.01)
    sys.exit(137)
sys.exit(child.wait())
''')
    lake.chmod(0o755)
    lean = binaries / "lean"
    lean.write_text(f"#!{sys.executable}\n" + r'''
import json, os, sys, time
from pathlib import Path
args = sys.argv
modules = Path(args[args.index('--modules-file') + 1]).read_text().splitlines()
roots = Path(args[args.index('--roots-file') + 1]).read_text().splitlines()
assert modules == ['A', 'B', 'C'] and roots
with open(os.environ['CALLS'], 'a') as stream:
    stream.write(json.dumps([roots, os.getpid()]) + '\n')
for root in roots:
    if root == os.environ.get('ISOLATE_ROOT') and len(roots) > 1:
        print(f'ISOLATE\t{root}', flush=True)
        continue
    if root == os.environ.get('SLOW_ROOT'):
        time.sleep(30)
    for name, line in [('shared', 1), ('only' + root, 2)]:
        print(f'DECL\t{name}\t{root}\t{line}\t0\t{line}\t40\ttheorem\tnormal', flush=True)
    target = 'C' if root == 'A' else root
    print(f'DEP\t{root}\tshared\t{target}\tonly{target}', flush=True)
print('EXTNS\tExternal.Common', flush=True)
if os.environ.get('FAIL_ROOT') in roots:
    print(f'root {os.environ["FAIL_ROOT"]} failed', file=sys.stderr, flush=True)
    sys.exit(int(os.environ.get('FAIL_CODE', '17')))
''')
    lean.chmod(0o755)
    ws = LocalWorkspace(project, tmp_path / "scratch", default_timeout=10, lean_threads=2)
    ws.environment.update(PATH=f"{binaries}:{os.environ['PATH']}", CALLS=str(tmp_path / "calls"))
    return ws


def calls(workspace):
    path = workspace.tmp.parent / "calls"
    return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []


@pytest.fixture
def one_root_per_process(monkeypatch):
    monkeypatch.setattr(olean, "_ROOTS_PER_PROCESS", 1)


EXPECTED_DEPENDENCIES = {
    ("A", "shared"): {("C", "onlyC")},
    ("B", "shared"): {("B", "onlyB")},
    ("C", "shared"): {("C", "onlyC")},
}


def test_roots_share_a_process_with_the_full_project_list(workspace):
    declarations, dependencies, namespaces = olean.read_olean_declarations(workspace, ["A", "B", "C"])
    assert [roots for roots, _pid in calls(workspace)] == [["A", "B", "C"]]
    assert len(declarations) == 6
    assert dependencies == EXPECTED_DEPENDENCIES
    assert namespaces == {"External.Common"}


def test_batches_are_bounded(workspace, monkeypatch):
    monkeypatch.setattr(olean, "_ROOTS_PER_PROCESS", 2)
    declarations, dependencies, _namespaces = olean.read_olean_declarations(workspace, ["A", "B", "C"])
    rows = calls(workspace)
    assert [roots for roots, _pid in rows] == [["A", "B"], ["C"]]
    assert len({pid for _roots, pid in rows}) == 2
    assert len(declarations) == 6
    assert dependencies == EXPECTED_DEPENDENCIES


def test_an_isolated_root_runs_again_alone(workspace):
    workspace.environment["ISOLATE_ROOT"] = "B"
    declarations, dependencies, _namespaces = olean.read_olean_declarations(workspace, ["A", "B", "C"])
    assert [roots for roots, _pid in calls(workspace)] == [["A", "B", "C"], ["B"]]
    assert sorted((row["module"], row["name"]) for row in declarations) == sorted(
        (module, name) for module in ("A", "B", "C") for name in ("shared", "only" + module)
    )
    assert dependencies == EXPECTED_DEPENDENCIES


def test_each_root_gets_a_fresh_process_and_the_full_project_list(workspace, one_root_per_process):
    declarations, dependencies, namespaces = olean.read_olean_declarations(workspace, ["A", "B", "C"])
    rows = calls(workspace)
    assert [roots for roots, _pid in rows] == [["A"], ["B"], ["C"]]
    assert len({pid for _roots, pid in rows}) == 3
    assert len(declarations) == 6
    assert {(row["module"], row["name"]) for row in declarations} == {
        (module, name) for module in ("A", "B", "C") for name in ("shared", "only" + module)
    }
    assert dependencies == {
        ("A", "shared"): {("C", "onlyC")},
        ("B", "shared"): {("B", "onlyB")},
        ("C", "shared"): {("C", "onlyC")},
    }
    assert namespaces == {"External.Common"}


@pytest.mark.parametrize("root,code,partial,expected", [
    ("A", 17, 2, [["A", "B", "C"], ["A"]]),
    ("B", 17, 4, [["A", "B", "C"], ["A"], ["B", "C"], ["B"]]),
    ("B", 137, 4, [["A", "B", "C"], ["A"], ["B", "C"], ["B"]]),
])
def test_failure_aborts_without_a_partial_graph(workspace, monkeypatch, root, code, partial, expected):
    workspace.environment.update(FAIL_ROOT=root, FAIL_CODE=str(code))

    def incomplete_evidence(*args, **kwargs):
        pytest.fail("a failed extraction must not reach graph construction")

    monkeypatch.setattr(dependency_graph, "combine_dependency_evidence", incomplete_evidence)
    with pytest.raises(olean.DeclGraphExtractionError) as error:
        dependency_graph.collect_dependency_graph(
            workspace, {}, modules=["A", "B", "C"], allow_missing_sources=True, allow_empty=True,
        )
    assert error.value.details["returncode"] == code
    assert error.value.details["partial_declarations"] == partial
    assert error.value.details["root_module"] == root
    assert error.value.details["failure_kind"] == ("killed" if code == 137 else "process_error")
    assert f"root {root} failed" in error.value.details["diagnostics"]
    assert [roots for roots, _pid in calls(workspace)] == expected


def test_timeout_terminates_the_active_batch_without_splitting_it(workspace):
    workspace.environment["SLOW_ROOT"] = "B"
    started = time.monotonic()
    with pytest.raises(olean.DeclGraphExtractionError) as error:
        olean.read_olean_declarations(workspace, ["A", "B", "C"], timeout=2)
    assert time.monotonic() - started < 5
    assert error.value.details["failure_kind"] == "timeout"
    assert error.value.details["partial_declarations"] == 2
    assert [roots for roots, _pid in calls(workspace)] == [["A", "B", "C"]]


def test_timeout_terminates_the_active_root_and_never_starts_the_next(workspace, one_root_per_process):
    workspace.environment["SLOW_ROOT"] = "B"
    started = time.monotonic()
    with pytest.raises(olean.DeclGraphExtractionError) as error:
        olean.read_olean_declarations(workspace, ["A", "B", "C"], timeout=2)
    assert time.monotonic() - started < 5
    assert error.value.details["failure_kind"] == "timeout"
    assert error.value.details["partial_declarations"] == 2
    assert error.value.details["root_module"] == "B"
    rows = calls(workspace)
    assert [roots for roots, _pid in rows] == [["A"], ["B"]]
    # Both launcher and worker inherit stdout. Returning within the deadline
    # proves the worker was killed too; otherwise reader.join() waits 30s.


class Clock:
    now = 100.0

    def monotonic(self):
        return self.now


class TimedEnvironment:
    def __init__(self, clock, durations, *, setup=2, setup_result=None):
        self.clock, self.durations, self.setup = clock, iter(durations), setup
        self.setup_result = setup_result or {"returncode": 0}
        self.timeouts = []
        self.roots = []
        self.files = {}

    def execute(self, command, *, timeout):
        self.setup_timeout = timeout
        self.clock.now += self.setup
        return self.setup_result

    def write_file_bytes(self, path, payload):
        self.files[path] = payload

    def execute_stream(self, command, *, timeout, on_output, capture_output):
        assert not capture_output
        batch = self.files[olean._DUMP_KEEP_ROOT_PATH].decode().splitlines()
        self.roots.extend(batch)
        self.timeouts.append(timeout)
        for root in batch:
            on_output(f"DECL\tshared\t{root}\t1\t0\t1\t40\ttheorem\tnormal")
        self.clock.now += next(self.durations)
        return {"returncode": 0}


def test_setup_and_all_roots_share_one_deadline(monkeypatch, one_root_per_process):
    clock = Clock()
    monkeypatch.setattr(olean.time, "monotonic", clock.monotonic)
    env = TimedEnvironment(clock, [3, 2, 1])
    declarations, _dependencies, _namespaces = olean.read_olean_declarations(env, ["A", "B", "C"], timeout=12)
    assert env.setup_timeout == 12
    assert env.timeouts == [10, 7, 5]
    assert len(declarations) == 3


@pytest.mark.parametrize("modules,durations,setup,roots,partial", [
    (["A", "B", "C"], [3, 0, 0], 2, ["A"], 1),
    (["A"], [6], 0, ["A"], 1),  # even a late success must not return a graph
    (["A"], [], 5, [], 0),
])
def test_exhausted_deadline_rejects_partial_and_late_successes(
    monkeypatch, one_root_per_process, modules, durations, setup, roots, partial,
):
    clock = Clock()
    monkeypatch.setattr(olean.time, "monotonic", clock.monotonic)
    env = TimedEnvironment(clock, durations, setup=setup)
    with pytest.raises(olean.DeclGraphExtractionError) as error:
        olean.read_olean_declarations(env, modules, timeout=5)
    assert error.value.details["failure_kind"] == "timeout"
    assert error.value.details["partial_declarations"] == partial
    assert env.roots == roots


def test_installation_failure_starts_no_roots(monkeypatch):
    clock = Clock()
    monkeypatch.setattr(olean.time, "monotonic", clock.monotonic)
    env = TimedEnvironment(clock, [], setup_result={"returncode": 1, "output": "cannot install script"})
    with pytest.raises(olean.DeclGraphExtractionError, match="cannot install script"):
        olean.read_olean_declarations(env, ["A"])
    assert env.roots == []


def test_a_late_batch_success_is_rejected_with_its_declarations(monkeypatch):
    clock = Clock()
    monkeypatch.setattr(olean.time, "monotonic", clock.monotonic)
    env = TimedEnvironment(clock, [6], setup=0)
    with pytest.raises(olean.DeclGraphExtractionError) as error:
        olean.read_olean_declarations(env, ["A", "B"], timeout=5)
    assert error.value.details["failure_kind"] == "timeout"
    assert error.value.details["partial_declarations"] == 2
    assert env.roots == ["A", "B"]


def test_repeated_and_quoted_modules_preserve_physical_identity(monkeypatch):
    clock = Clock()
    monkeypatch.setattr(olean.time, "monotonic", clock.monotonic)
    env = TimedEnvironment(clock, [0], setup=0)
    modules = ["A", "A", "Geometry.«Adic spaces»"]
    declarations, _dependencies, _namespaces = olean.read_olean_declarations(env, modules)
    assert env.files[olean._DUMP_KEEP_MODULES_PATH].decode().splitlines() == ["A", "Geometry.«Adic spaces»"]
    assert env.roots == ["A", "Geometry.«Adic spaces»"]
    assert [(row["module"], row["name"]) for row in declarations] == [
        ("A", "shared"), ("Geometry.«Adic spaces»", "shared"),
    ]


def test_interruption_also_terminates_the_process_group(workspace, monkeypatch):
    from lean_strip import workspace as workspace_module

    original_popen = workspace_module.subprocess.Popen
    started = []

    def interrupted_process(*args, **kwargs):
        process = original_popen(*args, **kwargs)
        original_wait = process.wait

        def interrupt_once(*args, **kwargs):
            process.wait = original_wait
            raise KeyboardInterrupt

        process.wait = interrupt_once
        started.append(process)
        return process

    monkeypatch.setattr(workspace_module.subprocess, "Popen", interrupted_process)
    with pytest.raises(KeyboardInterrupt):
        workspace.execute_stream(["sh", "-c", "sleep 30"])
    assert started[0].returncode == -signal.SIGKILL


def test_launcher_failure_terminates_its_live_worker_immediately(workspace, one_root_per_process):
    workspace.environment.update(FAIL_LAUNCHER="1", SLOW_ROOT="A")
    started = time.monotonic()
    with pytest.raises(olean.DeclGraphExtractionError) as error:
        olean.read_olean_declarations(workspace, ["A", "B", "C"], timeout=2)
    assert time.monotonic() - started < 5
    assert error.value.details["returncode"] == 137
    assert error.value.details["failure_kind"] == "killed"
    assert error.value.details["root_module"] == "A"
    assert error.value.details["partial_declarations"] == 0
    assert [roots for roots, _pid in calls(workspace)] == [["A"]]

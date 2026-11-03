"""Roots run in parallel processes, and the script runs compiled when it can.

A fake Lake and Lean stand in for the toolchain. Whatever the number of
workers, the records and their order are those of one process at a time.
"""

import json
import os
import sys
import time

import pytest

from lean_strip._pipeline.preprocessing import olean
from lean_strip.workspace import LocalWorkspace

MODULES = [f"M{index}" for index in range(12)]

# One fake `lean`: `--run` and the compiled program both dump; `-c` and
# `--print-libdir` stand in for the compiler.
FAKE_LEAN = r'''
import json, os, sys, time
from pathlib import Path
args = sys.argv[1:]
if args[:1] == ['--print-libdir']:
    print(os.environ['FAKE_LIBDIR'])
    sys.exit(0)
if args[:1] == ['-c']:
    if os.environ.get('FAIL_COMPILE'):
        sys.exit(1)
    Path(args[1]).write_text('compiled ' + args[2])
    sys.exit(0)
native = Path(sys.argv[0]).name == '_dump_keep.bin'
modules = Path(args[args.index('--modules-file') + 1]).read_text().splitlines()
roots = Path(args[args.index('--roots-file') + 1]).read_text().splitlines()
known = set()
if '--known-namespaces-file' in args:
    known = set(Path(args[args.index('--known-namespaces-file') + 1]).read_text().splitlines())
with open(os.environ['CALLS'], 'a') as stream:
    stream.write(json.dumps({'roots': roots, 'native': native, 'known': len(known)}) + '\n')
isolate = os.environ.get('ISOLATE_ROOTS', '').split(',')
time.sleep(float(os.environ.get('DELAY', '0')) * (len(modules) - modules.index(roots[0])) / len(modules))
for root in roots:
    if root in isolate and len(roots) > 1:
        print(f'ISOLATE\t{root}', flush=True)
        continue
    for name, line in [('shared', 1), ('only' + root, 2)]:
        print(f'DECL\t{name}\t{root}\t{line}\t0\t{line}\t40\ttheorem\tnormal', flush=True)
    print(f'DEP\t{root}\tshared\t{root}\tonly{root}', flush=True)
    print(f'DEP\t{root}\tshared\t{modules[0]}\tshared', flush=True)
for namespace in ['External.Common', 'External.' + roots[0]]:
    if namespace not in known:
        print(f'EXTNS\t{namespace}', flush=True)
if os.environ.get('FAIL_ROOT') in roots:
    print(f'root {os.environ["FAIL_ROOT"]} failed', file=sys.stderr, flush=True)
    sys.exit(17)
if os.environ.get('FAIL_BATCHED') in roots and len(roots) > 1:
    sys.exit(18)
if roots == [os.environ.get('CRASH_ROOT')]:
    sys.exit(19)
if os.environ.get('SLOW_ROOT') in roots:
    time.sleep(60)
'''

FAKE_LEANC = r'''
import sys
from pathlib import Path
args = sys.argv[1:]
output = Path(args[args.index('-o') + 1])
output.write_text(Path(__file__).with_name('lean').read_text())
output.chmod(0o755)
'''

FAKE_LAKE = r'''
import os, sys
assert sys.argv[1] == 'env'
os.execvp(sys.argv[2], sys.argv[2:])
'''


@pytest.fixture
def workspace(tmp_path):
    project = tmp_path / "project"
    project.mkdir()
    binaries = tmp_path / "bin"
    binaries.mkdir()
    for name, body in (("lean", FAKE_LEAN), ("leanc", FAKE_LEANC), ("lake", FAKE_LAKE)):
        path = binaries / name
        path.write_text(f"#!{sys.executable}\n" + body)
        path.chmod(0o755)
    ws = LocalWorkspace(project, tmp_path / "scratch", default_timeout=30, lean_threads=2)
    ws.environment.update(PATH=f"{binaries}:{os.environ['PATH']}", CALLS=str(tmp_path / "calls"),
                          FAKE_LIBDIR=str(tmp_path / "lib"))
    return ws


def calls(workspace):
    path = workspace.tmp.parent / "calls"
    return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []


def extract(workspace, monkeypatch, workers, **environment):
    monkeypatch.setattr(olean, "_ROOTS_PER_PROCESS", 4)
    workspace.environment.update(environment)
    (workspace.tmp.parent / "calls").unlink(missing_ok=True)
    return olean.read_olean_declarations(workspace, MODULES, workers=workers)


@pytest.mark.parametrize("environment", [
    {},
    {"ISOLATE_ROOTS": "M1,M2,M6,M11"},
    # Later roots finish first, so completion order differs from queue order.
    {"ISOLATE_ROOTS": "M0,M5,M9", "DELAY": "0.3"},
])
def test_parallel_workers_return_the_sequential_records_in_order(workspace, monkeypatch, environment):
    expected = extract(workspace, monkeypatch, 1, **environment)
    processes = sorted(row["roots"] for row in calls(workspace))
    for workers in (2, 5):
        assert extract(workspace, monkeypatch, workers, **environment) == expected
        assert sorted(row["roots"] for row in calls(workspace)) == processes
    decls, deps, namespaces = expected
    assert len(decls) == 2 * len(MODULES)
    assert set(deps) == {(module, "shared") for module in MODULES}
    assert namespaces == {"External.Common", *(f"External.{module}" for module in MODULES[::4]),
                          *(f"External.{root}" for root in environment.get("ISOLATE_ROOTS", "").split(",") if root)}


def test_the_script_runs_compiled_with_lakes_environment(workspace, monkeypatch):
    native = extract(workspace, monkeypatch, 3)
    rows = calls(workspace)
    assert rows and all(row["native"] for row in rows)
    assert (workspace.tmp / "_dump_keep.bin").is_file()
    assert "FAKE_LIBDIR" in (workspace.tmp / "_dump_keep.env").read_text()
    assert extract(workspace, monkeypatch, 3, FAIL_COMPILE="1") == native
    assert not any(row["native"] for row in calls(workspace))


def test_later_processes_leave_out_namespaces_already_reported(workspace, monkeypatch):
    _decls, _deps, namespaces = extract(workspace, monkeypatch, 1)
    rows = calls(workspace)
    assert rows[0]["known"] == 0
    assert all(row["known"] for row in rows[1:])
    assert "External.Common" in namespaces


def test_a_failing_root_stops_the_other_workers(workspace, monkeypatch):
    monkeypatch.setattr(olean, "_ROOTS_PER_PROCESS", 1)
    workspace.environment.update(FAIL_ROOT="M3", DELAY="20")
    started = time.monotonic()
    with pytest.raises(olean.DeclGraphExtractionError) as error:
        olean.read_olean_declarations(workspace, MODULES[:4], workers=4)
    assert error.value.details["root_module"] == "M3"
    assert "root M3 failed" in error.value.details["diagnostics"]
    # M3 fails after 5 s; the other roots would sleep for 10 to 20 s.
    assert time.monotonic() - started < 15


# The checkpoint: an interrupted extraction saved what had finished, and a
# rerun on the same inputs runs only the rest, with the records of one run.

def exactly(result):
    """The records with the order of everything that has one."""
    decls, deps, namespaces = result
    return decls, list(deps.items()), namespaces


def resumable(workspace, monkeypatch, checkpoint, log, *, workers=1, inputs="built", modules=MODULES,
              timeout=3600, **environment):
    monkeypatch.setattr(olean, "_ROOTS_PER_PROCESS", 4)
    for name in ("SLOW_ROOT", "CRASH_ROOT", "FAIL_BATCHED"):
        workspace.environment.pop(name, None)
    workspace.environment.update(environment)
    (workspace.tmp.parent / "calls").unlink(missing_ok=True)
    return exactly(olean.read_olean_declarations(
        workspace, modules, workers=workers, timeout=timeout,
        checkpoint=checkpoint, checkpoint_inputs=inputs, log=log.append))


def processes(workspace):
    return sorted(row["roots"] for row in calls(workspace))


@pytest.mark.parametrize("workers", [1, 3])
def test_a_run_past_its_deadline_resumes_after_its_finished_batches(workspace, monkeypatch, tmp_path, workers):
    isolate = {"ISOLATE_ROOTS": "M1,M6,M9"}
    expected = exactly(extract(workspace, monkeypatch, 1, **isolate))
    checkpoint, log = tmp_path / "state" / "graph-checkpoint.jsonl", []
    with pytest.raises(olean.DeclGraphExtractionError) as error:
        resumable(workspace, monkeypatch, checkpoint, log, workers=workers, timeout=3, SLOW_ROOT="M8", **isolate)
    assert error.value.details["timed_out"]
    assert any("finished batches saved" in line for line in log)
    log.clear()
    assert resumable(workspace, monkeypatch, checkpoint, log, workers=workers, **isolate) == expected
    assert processes(workspace) == [["M8", "M9", "M10", "M11"], ["M9"]]
    assert any("resuming after 4 finished batches" in line for line in log)


def test_a_crashed_run_resumes_with_the_records_of_one_run(workspace, monkeypatch, tmp_path):
    isolate = {"ISOLATE_ROOTS": "M1,M6,M9"}
    expected = exactly(extract(workspace, monkeypatch, 1, **isolate))
    checkpoint, log = tmp_path / "graph-checkpoint.jsonl", []
    with pytest.raises(olean.DeclGraphExtractionError) as error:
        resumable(workspace, monkeypatch, checkpoint, log, CRASH_ROOT="M6", **isolate)
    assert error.value.details["root_module"] == "M6"
    assert resumable(workspace, monkeypatch, checkpoint, log, **isolate) == expected
    assert processes(workspace) == [["M6"], ["M8", "M9", "M10", "M11"], ["M9"]]


def test_a_batch_that_failed_is_not_run_again_whole(workspace, monkeypatch, tmp_path):
    # M5 fails in any batch, so its batch was split; the halves' records,
    # not those of the whole batch, are the ones a single run returns.
    environment = {"ISOLATE_ROOTS": "M4,M9", "FAIL_BATCHED": "M5"}
    expected = exactly(extract(workspace, monkeypatch, 1, **environment))
    checkpoint, log = tmp_path / "graph-checkpoint.jsonl", []
    with pytest.raises(olean.DeclGraphExtractionError):
        resumable(workspace, monkeypatch, checkpoint, log, timeout=3, SLOW_ROOT="M8", **environment)
    # Even where the batch would now succeed whole.
    del environment["FAIL_BATCHED"]
    assert resumable(workspace, monkeypatch, checkpoint, log, **environment) == expected
    assert processes(workspace) == [["M8", "M9", "M10", "M11"], ["M9"]]


def test_a_finished_checkpoint_runs_no_lean_at_all(workspace, monkeypatch, tmp_path):
    checkpoint, log = tmp_path / "graph-checkpoint.jsonl", []
    expected = resumable(workspace, monkeypatch, checkpoint, log, workers=2, ISOLATE_ROOTS="M3")
    assert expected == exactly(extract(workspace, monkeypatch, 1, ISOLATE_ROOTS="M3"))
    (workspace.tmp / "_dump_keep.bin").unlink()
    assert resumable(workspace, monkeypatch, checkpoint, log, workers=2, ISOLATE_ROOTS="M3") == expected
    assert calls(workspace) == []
    assert not (workspace.tmp / "_dump_keep.bin").exists()


@pytest.mark.parametrize(("change", "reason"), [
    ({"inputs": "rebuilt"}, "inputs"),
    ({"modules": MODULES[:-1]}, "module list"),
    ({"script": "-- another version"}, "graph script"),
    ({"batch": 3}, "batch size"),
    ({"garbage": "not a checkpoint\n"}, "not a checkpoint of this lean-strip"),
])
def test_a_checkpoint_of_anything_else_is_ignored_and_replaced(workspace, monkeypatch, tmp_path, change, reason):
    checkpoint, log = tmp_path / "graph-checkpoint.jsonl", []
    resumable(workspace, monkeypatch, checkpoint, log)
    if "garbage" in change:
        checkpoint.write_text(change["garbage"])
    options = {key: change[key] for key in ("inputs", "modules") if key in change}
    if "script" in change:
        monkeypatch.setattr(olean, "_DUMP_KEEP_LEAN", olean._DUMP_KEEP_LEAN + "\n" + change["script"])
    original = olean._ROOTS_PER_PROCESS

    def fresh():
        monkeypatch.setattr(olean, "_ROOTS_PER_PROCESS", change.get("batch", 4))
        (workspace.tmp.parent / "calls").unlink(missing_ok=True)
        result = exactly(olean.read_olean_declarations(
            workspace, options.get("modules", MODULES), checkpoint=checkpoint,
            checkpoint_inputs=options.get("inputs", "built"), log=log.append))
        monkeypatch.setattr(olean, "_ROOTS_PER_PROCESS", original)
        return result

    log.clear()
    first = fresh()
    assert any("ignored" in line and reason in line and str(checkpoint) in line for line in log)
    ran = processes(workspace)
    assert ran and sum(len(roots) for roots in ran) == len(options.get("modules", MODULES))
    # The ignored checkpoint was replaced by this run's.
    log.clear()
    assert fresh() == first
    assert calls(workspace) == [] and not any("ignored" in line for line in log)


def test_a_record_cut_short_is_dropped_and_its_batch_run_again(workspace, monkeypatch, tmp_path):
    checkpoint, log = tmp_path / "graph-checkpoint.jsonl", []
    expected = resumable(workspace, monkeypatch, checkpoint, log, ISOLATE_ROOTS="M9")
    lines = checkpoint.read_bytes().splitlines(keepends=True)
    assert len(lines) == 1 + 4  # the header, three batches and M9 alone
    checkpoint.write_bytes(b"".join(lines[:-1]) + lines[-1][:len(lines[-1]) // 2])
    assert resumable(workspace, monkeypatch, checkpoint, log, ISOLATE_ROOTS="M9") == expected
    assert processes(workspace) == [["M9"]]
    assert any("dropped an incomplete record" in line for line in log)
    assert checkpoint.read_bytes() == b"".join(lines)


def test_an_unwritable_checkpoint_only_costs_the_resume(workspace, monkeypatch, tmp_path):
    (tmp_path / "file").write_text("")
    log = []
    assert (resumable(workspace, monkeypatch, tmp_path / "file" / "graph-checkpoint.jsonl", log)
            == exactly(extract(workspace, monkeypatch, 1)))
    assert any("not used" in line for line in log)


def test_the_checkpoint_inputs_follow_sources_pins_and_vendored_dependencies(tmp_path):
    from lean_strip import engine

    project = tmp_path / "project"
    (project / "vendor" / "Dep").mkdir(parents=True)
    (project / "lean-toolchain").write_text("leanprover/lean4:v4.20.0\n")
    (project / "vendor" / "Dep" / "Dep.lean").write_text("def dep : Nat := 1\n")
    ws = LocalWorkspace(project, tmp_path / "scratch", default_timeout=30, lean_threads=1,
                        project_skip=("vendor/Dep",))
    sources = {"/testbed/A.lean": "def a : Nat := 1\n"}
    digest = engine._graph_inputs(ws, sources)
    assert engine._graph_inputs(ws, dict(sources)) == digest
    assert engine._graph_inputs(ws, {"/testbed/A.lean": "def a : Nat := 2\n"}) != digest
    (project / "lean-toolchain").write_text("leanprover/lean4:v4.21.0\n")
    assert engine._graph_inputs(ws, sources) != digest
    changed = engine._graph_inputs(ws, sources)
    (project / "vendor" / "Dep" / "Dep.lean").write_text("def dep : Nat := 2\n")
    assert engine._graph_inputs(ws, sources) != changed

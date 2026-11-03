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

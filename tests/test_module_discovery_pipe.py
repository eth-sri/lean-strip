"""Discovery must drain its pipes and accept only module-path records."""

import os
import subprocess
import sys

import pytest

from lean_strip._pipeline.preprocessing.examples import discover_modules


@pytest.fixture
def discovery_environment(tmp_path):
    executable = tmp_path / "find"
    executable.write_text(f"#!{sys.executable}\n" + r'''
import os, sys
root = os.environ['TESTBED']
if '-type' in sys.argv:
    print(root + '/vendor/Needle.lean')
    for i in range(3000):
        print(root + '/vendor/' + str(i) + 'x' * 80 + '.lean')
else:
    if os.environ.get('FAIL_BUILD_FIND'):
        sys.exit(13)
    print(root + '/.lake/build/lib/lean/Needle.olean')
''')
    executable.chmod(0o755)

    class Environment:
        environment = {**os.environ, "PATH": f"{tmp_path}:{os.environ['PATH']}",
                       "TESTBED": str(tmp_path / "project")}

        def execute(self, command):
            result = subprocess.run(
                ["bash", "-c", command.replace("/testbed", self.environment["TESTBED"])],
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=10,
                env=self.environment,
            )
            return {"returncode": result.returncode, "output": result.stdout}

    return Environment()


def test_large_source_list_does_not_emit_broken_pipe(discovery_environment):
    # The first source matches, followed by more than a pipe buffer of paths.
    # No root-level source exists, so this always exercises the fallback pipe.
    assert discover_modules(discovery_environment) == ["Needle"]


def test_discovery_propagates_upstream_find_failure(discovery_environment):
    discovery_environment.environment["FAIL_BUILD_FIND"] = "1"
    with pytest.raises(RuntimeError, match="discovery failed"):
        discover_modules(discovery_environment)


@pytest.mark.parametrize("result", [
    {"returncode": 1, "output": "find failed"},
    {"returncode": 0, "output": "./Good\nbash: broken pipe\n"},
    {"returncode": 0, "output": "Plain.Name\n"},
    {"returncode": 0, "output": "./\n"},
    {"returncode": 0, "output": "./A//B\n"},
    {"returncode": 0, "output": "./../Other\n"},
    {"returncode": 0, "output": "./A\tBad\n"},
    {"returncode": 0, "timed_out": True, "output": "./Good\n"},
])
def test_discovery_rejects_failed_or_contaminated_output(result):
    class Environment:
        def execute(self, command):
            return result

    with pytest.raises(RuntimeError, match="discovery"):
        discover_modules(Environment())


def test_discovery_preserves_quoted_module_components():
    class Environment:
        def execute(self, command):
            return {"returncode": 0, "output": "./Algebra/Adic spaces\n./A.with.dot\n./Algebra/Adic spaces\n"}

    assert discover_modules(Environment()) == ["Algebra.«Adic spaces»", "«A.with.dot»"]

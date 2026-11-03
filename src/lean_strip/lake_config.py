"""Read evaluated root-library configuration using the project's own Lake."""

from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path


QUERY = r'''import Lake
import Lake.Load.Workspace
open Lean Lake

unsafe def main (args : List String) : IO UInt32 := do
  let [sysroot] := args | throw <| IO.userError "Expected the active Lean sysroot"
  let lean ← Lake.LeanInstall.get sysroot
  let lake := Lake.LakeInstall.ofLean lean
  let elan? ← Lake.findElanInstall?
  let env ← (Lake.Env.compute lake lean elan?).toIO IO.userError
  let some ws ← (Lake.loadWorkspaceRoot {lakeEnv := env, wsDir := ← IO.currentDir}).toBaseIO
    | throw <| IO.userError "Could not load the root Lake configuration"
  let libraries := ws.root.leanLibs.map fun lib => Json.mkObj [
    ("name", toJson lib.name.toString),
    ("roots", toJson (lib.roots.map Name.toString)),
    ("globs", toJson (lib.config.globs.map toString))]
  IO.println (toJson libraries).compress
  return 0
'''


def evaluated_libraries(root: Path) -> list[dict]:
    """Load the root config only, without updating or resolving dependencies."""
    with tempfile.TemporaryDirectory(prefix="lean-strip-lake-config-") as directory:
        query = Path(directory) / "Libraries.lean"
        query.write_text(QUERY)
        prefix = subprocess.run(
            ["lean", "--print-prefix"], cwd=root,
            capture_output=True, text=True, check=True, timeout=30,
        ).stdout.strip()
        toolchain = Path(prefix)
        subprocess.run(
            [str(toolchain / "bin/lean"), "-c", "Libraries.c", query.name], cwd=directory,
            capture_output=True, text=True, check=True, timeout=120,
        )
        binary = Path(directory) / "libraries"
        subprocess.run(
            [str(toolchain / "bin/leanc"), "-o", str(binary), "Libraries.c", "-lLake", "-rdynamic"], cwd=directory,
            capture_output=True, text=True, check=True, timeout=120,
        )
        result = subprocess.run(
            [str(binary), prefix], cwd=root,
            capture_output=True, text=True, check=True, timeout=120,
        )
    return json.loads(result.stdout.strip().splitlines()[-1])

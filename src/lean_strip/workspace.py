"""The scratch checkout the pipeline runs against.

The pipeline addresses the project as ``/testbed`` and its helper files as
``/tmp/...``, the paths the LeanLean benchmark uses. ``LocalWorkspace`` keeps
those logical paths, so every planner sees the same path keys as the
benchmark, and maps them to the real scratch directories only when it runs a
process or touches a file.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import threading
import time
from pathlib import Path
from typing import Any, Callable, Iterable, Iterator

from lean_strip._pipeline.preprocessing.ilean import module_to_ilean_relpath

CONTAINER_ROOT = "/testbed"
CONTAINER_TMP = "/tmp/"


def _alternation(mapping: dict[str, str]) -> re.Pattern[str]:
    keys = sorted(mapping, key=len, reverse=True)
    return re.compile("|".join(re.escape(key) for key in keys))


class LocalWorkspace:
    """Runs the pipeline's commands and file I/O in one local Lake project."""

    def __init__(
        self,
        root: Path,
        scratch: Path,
        *,
        default_timeout: int,
        lean_threads: int,
        command_log: Callable[[str], None] | None = None,
    ) -> None:
        self.root = root.resolve()
        self.tmp = scratch.resolve()
        self.tmp.mkdir(parents=True, exist_ok=True)
        self.default_timeout = default_timeout
        self._host_map = {CONTAINER_ROOT: str(self.root), CONTAINER_TMP: f"{self.tmp}/"}
        self._container_map = {value: key for key, value in self._host_map.items()}
        self._host_pattern = _alternation(self._host_map)
        self._container_pattern = _alternation(self._container_map)
        self._log = command_log or (lambda _line: None)
        self._env = {
            **os.environ,
            # The benchmark runs under the POSIX locale; `sort` and
            # `find | sort` orderings must match it byte for byte.
            "LC_ALL": "C",
            "LEAN_NUM_THREADS": str(lean_threads),
        }

    # -- path translation ---------------------------------------------------

    def host_path(self, path: str) -> Path:
        if path == CONTAINER_ROOT or path.startswith(CONTAINER_ROOT + "/"):
            return Path(str(self.root) + path[len(CONTAINER_ROOT):])
        if path.startswith(CONTAINER_TMP):
            return self.tmp / path[len(CONTAINER_TMP):]
        raise ValueError(f"path outside the workspace: {path}")

    def _to_host(self, text: str) -> str:
        # One pass: the host paths may themselves live under /tmp/.
        return self._host_pattern.sub(lambda m: self._host_map[m.group(0)], text)

    def _to_container(self, text: str) -> str:
        return self._container_pattern.sub(lambda m: self._container_map[m.group(0)], text)

    def _timeout(self, timeout: Any) -> float:
        if timeout is True or timeout is False or timeout is None:
            return self.default_timeout
        return float(timeout)

    # -- the Environment surface the engine uses ------------------------------

    def execute(self, command: str | list[str], cwd: str = "", timeout: Any = True) -> dict[str, Any]:
        result = self.execute_stream(command, cwd=cwd, timeout=timeout)
        return {"output": result["output"], "returncode": result["returncode"]}

    def execute_stream(
        self,
        command: str | list[str],
        cwd: str = "",
        timeout: Any = True,
        on_output: Callable[[str], None] | None = None,
        capture_output: bool = True,
    ) -> dict[str, Any]:
        """Run a bash command string, or an argv directly; stdout and stderr are merged."""

        if isinstance(command, str):
            argv = ["bash", "-c", self._to_host(command)]
            shown = argv[2]
        else:
            argv = [self._to_host(arg) for arg in command]
            shown = " ".join(argv)
        self._log(f"$ {shown if len(shown) < 2000 else shown[:2000] + ' ...'}")
        started = time.perf_counter()
        process = subprocess.Popen(
            argv,
            cwd=self.host_path(cwd) if cwd else self.root,
            env=self._env,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            bufsize=1,
        )
        lines: list[str] = []

        def reader() -> None:
            assert process.stdout is not None
            for raw in process.stdout:
                line = self._to_container(raw)
                if capture_output:
                    lines.append(line)
                if on_output is not None:
                    on_output(line)

        thread = threading.Thread(target=reader, daemon=True)
        thread.start()
        timed_out = False
        try:
            process.wait(timeout=self._timeout(timeout))
        except subprocess.TimeoutExpired:
            timed_out = True
            process.kill()
            process.wait()
        thread.join()
        output = "".join(lines)
        self._log(
            f"  -> rc={process.returncode} in {time.perf_counter() - started:.1f}s"
            + (" (timed out)" if timed_out else "")
        )
        return {"output": output, "returncode": process.returncode, "timed_out": timed_out}

    def run_argv(self, argv: list[str], *, timeout: float | None = None) -> subprocess.CompletedProcess:
        """Run an argv (container paths allowed) in the project directory."""

        host_argv = [self._to_host(arg) for arg in argv]
        self._log("$ " + " ".join(host_argv))
        started = time.perf_counter()
        try:
            result = subprocess.run(
                host_argv,
                cwd=self.root,
                env=self._env,
                text=True,
                capture_output=True,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired as error:
            result = subprocess.CompletedProcess(
                host_argv, 124,
                stdout=(error.stdout or b"").decode() if isinstance(error.stdout, bytes) else (error.stdout or ""),
                stderr=(error.stderr or b"").decode() if isinstance(error.stderr, bytes) else (error.stderr or ""),
            )
        result.stdout = self._to_container(result.stdout)
        result.stderr = self._to_container(result.stderr)
        self._log(f"  -> rc={result.returncode} in {time.perf_counter() - started:.1f}s")
        return result

    def write_file_bytes(self, path: str, content: bytes) -> None:
        target = self.host_path(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)

    def write_text(self, path: str, content: str) -> None:
        # Match `cat > path` from a Python text pipe: exact UTF-8 bytes.
        self.write_file_bytes(path, content.encode("utf-8"))

    def snapshot(self, paths: Iterable[str]) -> dict[str, str]:
        return {
            path: self.host_path(path).read_bytes().decode("utf-8", "replace")
            for path in paths
        }

    def remove(self, paths: Iterable[str]) -> None:
        for path in paths:
            self.host_path(path).unlink()

    def apply_source_tree(self, current: dict[str, str], desired: dict[str, str]) -> None:
        for path, source in desired.items():
            if current.get(path) != source:
                self.write_text(path, source)
        self.remove(sorted(set(current) - set(desired)))

    def iter_ilean_documents(
        self, modules: Iterable[str] | None = None
    ) -> Iterator[tuple[str, dict[str, Any]]]:
        """Yield the same members as the container's ``find | sort | tar``."""

        lib = self.root / ".lake" / "build" / "lib"
        requested = sorted(set(modules or []))
        if requested and len(requested) < 512:
            if any(not module or "/" in module for module in requested):
                raise ValueError(f"invalid Lean module name in {requested!r}")
            wanted = {
                f".lake/build/lib/lean/{module_to_ilean_relpath(module)}"
                for module in requested
            }
            candidates = [
                relative
                for relative in wanted
                if (self.root / relative).is_file()
            ]
        else:
            candidates = [
                path.relative_to(self.root).as_posix()
                for path in lib.rglob("*.ilean")
                if path.is_file()
            ] if lib.is_dir() else []
        for relative in sorted(candidates, key=lambda item: item.encode()):
            try:
                document = json.loads((self.root / relative).read_bytes())
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValueError(f"{relative}: invalid .ilean JSON") from error
            if not isinstance(document, dict):
                raise ValueError(f"{relative}: .ilean root is not an object")
            yield relative, document

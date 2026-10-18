"""Running lean-strip inside a container, so its memory and CPUs can be bounded.

The container is only a resource boundary. The repository is bind-mounted at
its own path and the command runs as the calling user, so everything it writes
(the stripped sources, `.lake`, `.lean-strip/`) lands directly in the
repository, owned by that user, exactly as a run without --container would
leave it. Lean toolchains and the Mathlib cache come from the host's elan home
and cache directory where possible, so nothing is downloaded twice.

The image is small: Python, git, curl and elan. It is built on first use and
tagged by the hash of its recipe.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import platform
import shutil
import subprocess
import sys
from pathlib import Path

from . import lakefile

PACKAGE_DIR = Path(__file__).resolve().parent
CONTAINER_PACKAGE_ROOT = "/opt/lean-strip"

# The public ECR mirror of the official image: no Docker Hub login or rate limit.
BASE_IMAGE = "public.ecr.aws/docker/library/python:3.12-slim-bookworm"
RECIPE = f"""\
FROM {BASE_IMAGE}
RUN apt-get update \\
 && apt-get install -y --no-install-recommends git curl ca-certificates gcc libc6-dev \\
 && rm -rf /var/lib/apt/lists/*
RUN curl -sSfL "https://github.com/leanprover/elan/releases/latest/download/elan-$(uname -m)-unknown-linux-gnu.tar.gz" \\
      | tar -xz -C /tmp \\
 && ELAN_HOME=/opt/elan /tmp/elan-init -y --no-modify-path --default-toolchain none \\
 && rm /tmp/elan-init \\
 && chmod -R a+rX /opt/elan
ENV PATH=/opt/elan/bin:$PATH
"""

# Options that configure the container rather than the run inside it.
CONTAINER_DESTS = {"container", "memory", "cpus", "image"}


def add_arguments(parser: argparse.ArgumentParser) -> None:
    group = parser.add_argument_group("container")
    group.add_argument(
        "--container", nargs="?", const="auto", choices=("auto", "podman", "docker"),
        help="run inside a container (podman if installed, else docker); the repository is mounted, not copied",
    )
    group.add_argument("--memory", help="with --container: memory limit, e.g. 64g (no swap beyond it)")
    group.add_argument("--cpus", type=float, help="with --container: CPU limit; also the default --jobs")
    group.add_argument("--image", help="with --container: image to run in (default: built on first use)")


def _engine(choice: str) -> str:
    candidates = ("podman", "docker") if choice == "auto" else (choice,)
    for name in candidates:
        if shutil.which(name):
            return name
    raise SystemExit(f"lean-strip: --container needs {' or '.join(candidates)} on PATH")


def _ensure_image(engine: str) -> str:
    tag = "localhost/lean-strip-runtime:" + hashlib.sha256(RECIPE.encode()).hexdigest()[:12]
    present = subprocess.run([engine, "image", "exists", tag] if engine == "podman"
                             else [engine, "image", "inspect", tag],
                             capture_output=True, check=False)
    if present.returncode != 0:
        print(f"lean-strip: building the container image {tag} (once)", file=sys.stderr)
        subprocess.run([engine, "build", "-t", tag, "-"], input=RECIPE.encode(), check=True)
    return tag


def _git_dirs(repo: Path) -> list[Path]:
    """The git work tree and common dir around ``repo``, so git works inside."""

    found = []
    for flag in ("--show-toplevel", "--git-common-dir"):
        out = subprocess.run(["git", "rev-parse", "--path-format=absolute", flag],
                             cwd=repo, capture_output=True, text=True, check=False)
        if out.returncode == 0 and out.stdout.strip():
            found.append(Path(out.stdout.strip()))
    return found


def _inner_argv(parser: argparse.ArgumentParser, args: argparse.Namespace) -> list[str]:
    """The command line for the run inside, rebuilt from the parsed options."""

    argv: list[str] = []
    for action in parser._actions:
        dest = action.dest
        if dest in CONTAINER_DESTS or dest == "help" or not action.option_strings:
            continue
        value = getattr(args, dest, None)
        if value is None or value == action.default:
            continue
        flag = action.option_strings[-1]
        if isinstance(action, argparse._StoreTrueAction):
            argv.append(flag)
        else:
            argv += [flag, str(Path(value).resolve()) if isinstance(value, Path) else str(value)]
    if args.cpus and "--jobs" not in argv:
        argv += ["--jobs", str(max(1, int(args.cpus)))]
    return argv + [str(args.repo.resolve())]


def run(parser: argparse.ArgumentParser, args: argparse.Namespace) -> int:
    engine = _engine(args.container)
    repo = args.repo.resolve()
    image = args.image or _ensure_image(engine)

    mounts: dict[Path, str] = {repo: "rw"}
    for directory in _git_dirs(repo):
        mounts.setdefault(directory, "rw")
    # Lake builds path dependencies in place and follows a linked package directory.
    for directory in lakefile.path_dependency_dirs(repo):
        if not directory.is_relative_to(repo):
            mounts.setdefault(directory, "rw")
    packages = repo / ".lake" / "packages"
    if packages.is_symlink():
        mounts.setdefault(packages.resolve(), "rw")
    if args.comparator is not None and not args.comparator.resolve().is_relative_to(repo):
        mounts[args.comparator.resolve()] = "ro"
    mounts[PACKAGE_DIR] = "ro"

    env = {
        "HOME": "/tmp",
        "PYTHONPATH": CONTAINER_PACKAGE_ROOT,
        "PYTHONDONTWRITEBYTECODE": "1",
        "LEAN_STRIP_VERSION": _host_version(),
        # The repository is mounted from the host; its owner is the caller.
        "GIT_CONFIG_COUNT": "1",
        "GIT_CONFIG_KEY_0": "safe.directory",
        "GIT_CONFIG_VALUE_0": "*",
    }
    elan_home = Path(os.environ.get("ELAN_HOME") or Path.home() / ".elan")
    if platform.system() == "Linux" and (elan_home / "toolchains").is_dir():
        # Host toolchains are Linux binaries too: reuse them.
        mounts[elan_home] = "rw"
    else:
        elan_home = _cache_home() / "lean-strip" / "elan"
        elan_home.mkdir(parents=True, exist_ok=True)
        mounts[elan_home] = "rw"
    env["ELAN_HOME"] = str(elan_home)
    cache = _cache_home()
    cache.mkdir(parents=True, exist_ok=True)
    mounts[cache] = "rw"
    env["XDG_CACHE_HOME"] = str(cache)

    # Lake runs many Lean processes with several threads each; the engines'
    # default cap (2048 tasks) makes large builds fail to create threads.
    command = [engine, "run", "--rm", "--init", "--pids-limit=-1", "--workdir", str(repo)]
    if sys.stdin.isatty() and sys.stderr.isatty():
        command.append("-it")
    if engine == "podman":
        command.append("--userns=keep-id")
    else:
        command += ["--user", f"{os.getuid()}:{os.getgid()}"]
    if args.memory:
        command += ["--memory", args.memory, "--memory-swap", args.memory]
    if args.cpus:
        command += ["--cpus", str(args.cpus)]
    for host, mode in mounts.items():
        target = f"{CONTAINER_PACKAGE_ROOT}/lean_strip" if host == PACKAGE_DIR else str(host)
        command += ["--volume", f"{host}:{target}:{mode}"]
    for key, value in env.items():
        command += ["--env", f"{key}={value}"]
    command += [image, "python3", "-m", "lean_strip", *_inner_argv(parser, args)]
    try:
        return subprocess.run(command, check=False).returncode
    except KeyboardInterrupt:
        return 130


def _cache_home() -> Path:
    return Path(os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache")


def _host_version() -> str:
    from importlib.metadata import PackageNotFoundError, version

    try:
        return version("lean-strip")
    except PackageNotFoundError:
        return "unknown"

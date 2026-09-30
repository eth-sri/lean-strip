"""Finding the comparator config to strip against, and asking when it's unclear."""

from __future__ import annotations

import json
import os
import shutil
import sys
from pathlib import Path
from typing import Any

try:
    import termios
    import tty
except ImportError:  # Windows: fall back to a numbered prompt
    termios = tty = None


class ConfigError(ValueError):
    """A comparator config that cannot be used."""


def load_comparator(path: Path) -> dict[str, Any]:
    """Read a comparator config; ``protected`` is the sorted set of names to keep."""

    try:
        config = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ConfigError(f"{path.name}: not a readable JSON file ({error})") from error
    if not isinstance(config, dict):
        raise ConfigError(f"{path.name}: not a JSON object")
    for key in ("challenge_module", "solution_module"):
        if not isinstance(config.get(key), str) or not config[key]:
            raise ConfigError(f"{path.name}: missing {key}")
    names = set(config.get("theorem_names", [])) | set(config.get("definition_names", []))
    if not names:
        raise ConfigError(f"{path.name}: names no theorem_names/definition_names to protect")
    config["protected"] = sorted(names)
    return config


def find_comparators(repo: Path, skip: tuple[str, ...]) -> list[Path]:
    """Every ``comparator*.json`` in ``repo``, outside build, VCS and ``skip`` directories."""

    found: list[Path] = []
    for current, directories, files in os.walk(repo):
        directories[:] = sorted(d for d in directories if d not in {".git", ".lake", *skip})
        found.extend(
            Path(current) / name
            for name in files
            if name.lower().startswith("comparator") and name.lower().endswith(".json")
        )
    return sorted(found)


def describe(repo: Path, path: Path, config: dict[str, Any]) -> str:
    return (
        f"{path.relative_to(repo).as_posix()}  "
        f"(solution {config['solution_module']}, challenge {config['challenge_module']}, "
        f"{len(config['protected'])} protected)"
    )


def select(title: str, labels: list[str]) -> int:
    """Let the user pick one of ``labels`` on the terminal; return its index.

    Arrow keys (or j/k) move, Enter picks, a digit picks that entry directly.
    Raises KeyboardInterrupt on Ctrl-C, Esc or q.
    """

    out = sys.stderr
    width = max(shutil.get_terminal_size().columns - 4, 20)
    labels = [label if len(label) <= width else label[: width - 1] + "…" for label in labels]
    if termios is None or tty is None:
        out.write(title + "\n")
        for number, label in enumerate(labels, 1):
            out.write(f"  {number}. {label}\n")
        while True:
            answer = input(f"Choose 1-{len(labels)}: ").strip()
            if answer.isdigit() and 1 <= int(answer) <= len(labels):
                return int(answer) - 1

    def draw(index: int, redraw: bool) -> None:
        if redraw:
            out.write(f"\x1b[{len(labels)}A")
        for position, label in enumerate(labels):
            marker = "\x1b[1m❯" if position == index else " "
            out.write(f"\r\x1b[2K {marker} {label}\x1b[0m\n")
        out.flush()

    fd = sys.stdin.fileno()
    saved = termios.tcgetattr(fd)
    index = 0
    out.write(title + "  (↑/↓ and Enter)\n")
    draw(index, redraw=False)
    try:
        tty.setcbreak(fd)
        while True:
            key = os.read(fd, 3)
            if key in (b"\x1b[A", b"k"):
                index = (index - 1) % len(labels)
            elif key in (b"\x1b[B", b"j"):
                index = (index + 1) % len(labels)
            elif key in (b"\n", b"\r"):
                return index
            elif key.isdigit() and 1 <= int(key) <= len(labels):
                index = int(key) - 1
                draw(index, redraw=True)
                return index
            elif key in (b"\x1b", b"q", b"\x03"):
                raise KeyboardInterrupt
            draw(index, redraw=True)
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, saved)


def ask_for_comparator(
    repo: Path, candidates: list[tuple[Path, dict[str, Any]]], skipped: list[str]
) -> tuple[Path, dict[str, Any]]:
    """Ask which config to use: one of ``candidates``, or a path typed in."""

    for problem in skipped:
        sys.stderr.write(f"  skipped {problem}\n")
    title = (
        f"Found {len(candidates)} comparator configs. Which one should lean-strip use?"
        if candidates
        else "Found no usable comparator*.json. Where is the comparator config?"
    )
    labels = [describe(repo, path, config) for path, config in candidates] + ["Other…"]
    choice = select(title, labels)
    if choice < len(candidates):
        return candidates[choice]
    while True:
        answer = input("Path to the comparator config: ").strip()
        if not answer:
            continue
        path = Path(answer).expanduser()
        if not path.is_absolute():
            path = repo / path if (repo / path).is_file() else Path.cwd() / path
        try:
            return path.resolve(), load_comparator(path)
        except ConfigError as error:
            sys.stderr.write(f"  {error}\n")

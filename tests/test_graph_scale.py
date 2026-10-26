"""The graph's lookup structures answer exactly what the direct scans did.

They replace per-module copies and per-usage scans that did not fit in memory
or time on the largest registry projects (PALOMAR-2026-10-21-000025,
PALOMAR-2026-10-22-000009); each test compares one with its direct form on
random inputs.
"""

import random

from lean_strip._pipeline.preprocessing import ilean, strip


def _random_spans(rng, count, lines=40):
    spans = []
    for _ in range(count):
        start = (rng.randint(1, lines), rng.randint(0, 6))
        end = (rng.randint(start[0], min(lines, start[0] + rng.choice((0, 1, 3, 10, 40)))),
               rng.randint(0, 6))
        if end < start:
            end = (start[0], start[1] + rng.randint(0, 3))
        spans.append((start, end))
    return spans


def test_enclosing_declarations_match_the_pairwise_comparison():
    rng = random.Random(1)
    for trial in range(300):
        spans = _random_spans(rng, rng.randint(1, 30))
        if trial % 10 == 0:  # a malformed range takes the pairwise path
            spans.append(((9, 3), (8, 0)))
        decls = [{"name": f"d{rng.randint(0, 20)}", "start_line": s[0], "start_col": s[1],
                  "end_line": e[0], "end_col": e[1]} for s, e in spans]
        expected = [
            {outer["name"] for outer in decls
             if outer["name"] != child["name"]
             and (outer["start_line"], outer["start_col"]) <= (child["start_line"], child["start_col"])
             and (child["end_line"], child["end_col"]) <= (outer["end_line"], outer["end_col"])
             and ((outer["start_line"], outer["start_col"]), (outer["end_line"], outer["end_col"]))
             != ((child["start_line"], child["start_col"]), (child["end_line"], child["end_col"]))}
            for child in decls
        ]
        assert [set(found) for found in strip._enclosing_declarations(decls)] == expected


def test_visible_names_match_a_per_module_index():
    rng = random.Random(2)
    components = ["A", "B", "foo", "bar", "comm", "x"]
    for _ in range(100):
        modules = [f"M{index}" for index in range(5)]
        names_by_module = {module: set() for module in modules}
        for _ in range(40):
            module = rng.choice(modules)
            name = ".".join(rng.choice(components) for _ in range(rng.randint(1, 4)))
            if rng.random() < 0.2:
                name = f"_private.{rng.choice(modules)}.0.{name}"
            names_by_module[module].add(name)
        index = strip._ProjectNames(names_by_module)
        for module in modules:
            closure = set(rng.sample(modules, rng.randint(0, len(modules)))) | {module}
            view = index.visible_from(module, closure)
            # The per-module index augment_deps_with_source used to build.
            visible = set()
            for other in closure:
                for name in names_by_module[other]:
                    owner, _display = strip._private_owner_and_display(name)
                    if owner is None or owner == module:
                        visible.add(name)
            by_display, by_last, by_suffix = {}, {}, {}
            for name in visible:
                _owner, display = strip._private_owner_and_display(name)
                by_display.setdefault(display, set()).add(name)
                by_last.setdefault(display.rsplit(".", 1)[-1], set()).add(name)
                for position, char in enumerate(display):
                    if char == "." and position + 1 < len(display):
                        by_suffix.setdefault(display[position + 1:], set()).add(name)
            keys = {".".join(rng.choice(components) for _ in range(rng.randint(1, 3))) for _ in range(30)}
            keys |= set(by_display) | set(by_suffix) | set(by_last)
            for key in keys:
                assert view.by_display.get(key, set()) == by_display.get(key, set())
                assert view.by_last.get(key) == by_last.get(key)
                assert view.by_suffix.get(key, set()) == by_suffix.get(key, set())
            for name in index.modules_of:
                assert (name in view) == (name in visible)


def test_module_ranges_match_the_containment_scan():
    rng = random.Random(3)
    for _ in range(300):
        decls = [{"name": f"d{position}", "start_line": s[0], "start_col": s[1],
                  "end_line": e[0], "end_col": e[1]}
                 for position, (s, e) in enumerate(_random_spans(rng, rng.randint(0, 25)))]
        if decls and rng.random() < 0.3:
            decls[0]["end_col"] = None  # never contains anything
        ranges = ilean._ModuleRanges(decls)
        for _ in range(20):
            (sl, sc), (el, ec) = _random_spans(rng, 1)[0]
            usage = [sl, sc, el, ec] + (["owner"] if rng.random() < 0.5 else [])
            if rng.random() < 0.05:
                usage = [sl, "x", el, ec]
            expected = [decl["name"] for decl in decls if ilean._contains(decl, usage)]
            assert sorted(decl["name"] for decl in ranges.containing(usage)) == sorted(expected)


def test_resolution_by_last_component_matches_the_module_scan():
    rng = random.Random(4)
    components = ["A", "B", "foo", "_proof_1", "match_1"]
    for _ in range(200):
        names_by_module = {
            module: {".".join(rng.choice(components) for _ in range(rng.randint(1, 4))) for _ in range(8)}
            for module in ("M", "N")
        }
        names = {(module, name) for module, values in names_by_module.items() for name in values}
        names_by_last = {}
        for module, module_names in names_by_module.items():
            for name in module_names:
                names_by_last.setdefault(module, {}).setdefault(name.rsplit(".", 1)[-1], set()).add(name)
        for _ in range(10):
            raw = ".".join(rng.choice(components) for _ in range(rng.randint(1, 3)))
            module = rng.choice(("M", "N", "O"))
            if (module, raw) in names:
                expected = {(module, raw)}
            elif (module, f"{module}.{raw}") in names:
                expected = {(module, f"{module}.{raw}")}
            else:
                last = raw.rsplit(".", 1)[-1]
                expected = {(module, name) for name in names_by_module.get(module, set())
                            if name == raw or name.endswith("." + raw) or name.rsplit(".", 1)[-1] == last}
            assert ilean._resolve_in_module(raw, module, names, names_by_last) == expected


def test_namespace_members_from_the_prefix_index_match_the_scan():
    rng = random.Random(5)
    components = ["A", "B", "Foo", "«x.y»", "c"]
    for _ in range(200):
        names = {".".join(rng.choice(components) for _ in range(rng.randint(1, 4))) for _ in range(30)}
        index = strip._dotted_prefix_index(names)
        for _ in range(10):
            namespace = ".".join(rng.choice(components) for _ in range(rng.randint(1, 2)))
            lexical = ".".join(rng.choice(components) for _ in range(rng.randint(0, 2)))
            assert (strip._resolve_project_namespace_members(namespace, names, lexical, index)
                    == strip._resolve_project_namespace_members(namespace, names, lexical))

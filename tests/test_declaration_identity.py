"""Same Lean names in independent modules must remain physical graph nodes."""

import json

from lean_strip import engine
from lean_strip._pipeline.preprocessing import dependency_graph, graph_artifact, ilean, olean, strip
from lean_strip._pipeline.preprocessing.identity import decl_id, identity_rows


def declarations():
    return [
        dict(name=name, module=module, kind="theorem", meta=False,
             start_line=line, start_col=0, end_line=line, end_col=50)
        for module in ("A", "B")
        for name, line in ((f"only{module}", 1), ("shared", 2))
    ]


def sources():
    return {f"/testbed/{module}.lean": (
        f"axiom only{module} : True\ntheorem shared : True := only{module}\n"
    ) for module in ("A", "B")}


def documents():
    return [(f"{module}.ilean", {
        "module": module, "version": 5,
        "references": {json.dumps({"c": {"m": module, "n": f"only{module}"}}): {
            "usages": [[2, 30, 2, 35, "shared"]],
        }},
    }) for module in ("A", "B")]


def artifact(decls=None, **kwargs):
    options = dict(repository="duplicates", source_image="", source_image_id="",
                   declarations=declarations() if decls is None else decls,
                   kernel_edges=set(), ilean_edges=set(), source_text_edges=set(),
                   reports={}, originals={}, module_paths={})
    options.update(kwargs)
    return graph_artifact.build_graph_artifact(**options)


def edge_identities(graph):
    return {(decl_id(graph["nodes"][s]), decl_id(graph["nodes"][t]), mask)
            for s, t, mask in graph["edges"]}


def test_olean_wire_format_preserves_both_endpoints():
    class Reader:
        def execute(self, command, **kwargs):
            return {"returncode": 0}

        def write_file_bytes(self, path, payload):
            if path == olean._DUMP_KEEP_ROOT_PATH:
                self.roots = payload.decode().splitlines()

        def execute_stream(self, command, *, on_output, **kwargs):
            for module in self.roots:
                on_output(f"DECL\tshared\t{module}\t2\t0\t2\t50\ttheorem\tnormal\n")
                on_output(f"DEP\t{module}\tshared\t{module}\tonly{module}\n")
            return {"returncode": 0}

    decls, deps, _namespaces = olean.read_olean_declarations(Reader(), ["A", "B"])
    assert {decl_id(row) for row in decls} == {("A", "shared"), ("B", "shared")}
    assert deps == {("A", "shared"): {("A", "onlyA")},
                    ("B", "shared"): {("B", "onlyB")}}


def test_identity_survives_all_evidence_layers_reachability_and_serialization(tmp_path):
    class Reader:
        def iter_ilean_documents(self, modules):
            return iter(documents())

    decls = declarations()
    kernel = {(module, "shared"): {(module, f"only{module}")} for module in ("A", "B")}
    paths = {module: f"/testbed/{module}.lean" for module in ("A", "B")}
    deps, evidence, layers = dependency_graph.combine_dependency_evidence(
        Reader(), decls, kernel, sources(), paths,
    )
    expected = {((module, "shared"), (module, f"only{module}")) for module in ("A", "B")}
    assert all(edges == expected for edges in layers.values())
    assert evidence["total_edges"] == 2
    assert deps == kernel
    kept = strip.compute_keep_set(decls, deps, {("A", "shared")})
    assert kept == {("A", "shared"), ("A", "onlyA")}
    assert {decl_id(row) for row in strip.attach_keep(decls, kept) if row["keep"]} == kept
    report = {
        # Exact records take precedence over legacy summaries of the same names.
        "kept_declarations": ["shared", "onlyA", "onlyB"],
        "protected_declarations": ["shared"],
        "kept_declaration_identities": identity_rows(kept),
        "dropped_declaration_identities": identity_rows({("B", "shared"), ("B", "onlyB")}),
        "protected_declaration_identities": identity_rows({("A", "shared")}),
    }
    graph = artifact(kernel_edges=layers["kernel"], ilean_edges=layers["ilean"],
                     source_text_edges=layers["source_text"], reports={"production": report})
    assert edge_identities(graph) == {(s, t, 7) for s, t in expected}
    assert graph["policies"]["production"]["kept"] == [0, 1]
    assert graph["policies"]["production"]["removed"] == [2, 3]
    assert graph["policies"]["production"]["protected"] == [1]
    assert graph["ambiguous_edges"] == []
    assert artifact(list(reversed(decls)), kernel_edges=layers["kernel"], ilean_edges=layers["ilean"],
                    source_text_edges=layers["source_text"], reports={"production": report}) == graph
    path = tmp_path / "graph.json"
    graph_artifact.write_graph_artifact(path, graph)
    restored = json.loads(path.read_text())
    assert restored == graph
    assert restored["sha256"] == graph_artifact.graph_sha256(restored)


def test_ilean_does_not_redirect_an_external_homonym_to_a_project_provider():
    document = documents()[0][1]
    document["references"] = {
        json.dumps({"c": {"m": "External", "n": "shared"}}): {
            "usages": [[1, 20, 1, 25, "onlyA"]],
        }
    }
    deps, _report = ilean.union_ilean_documents([("A.ilean", document)], declarations(), {})
    assert deps == {}


def test_ilean_positional_owners_keep_their_module():
    docs = documents()
    for _path, document in docs:
        document["version"] = 3
        for reference in document["references"].values():
            reference["usages"][0].pop()
    deps, _report = ilean.union_ilean_documents(docs, declarations(), {})
    assert deps == {("A", "shared"): {("A", "onlyA")},
                    ("B", "shared"): {("B", "onlyB")}}


def test_module_pruning_uses_the_physical_root_and_dependency_owners():
    originals = {**sources(), "/testbed/Entry.lean": "import A\nimport B\n"}
    paths = {module: f"/testbed/{module}.lean" for module in ("A", "B", "Entry")}
    deps = {(module, "shared"): {(module, f"only{module}")} for module in ("A", "B")}
    planned, report = strip.plan_protected_module_prune(
        originals, declarations(), deps, {("A", "shared")}, "Entry", known_module_paths=paths,
    )
    assert report["live_declaration_identities"] == identity_rows({("A", "shared"), ("A", "onlyA")})
    assert report["deleted_modules"] == ["B"]
    assert "/testbed/B.lean" not in planned


def test_legacy_ambiguous_edges_are_explicit_and_never_assigned_to_one_provider():
    graph = artifact(kernel_edges={("shared", "onlyA"), ("onlyA", "shared")},
                     reports={"production": {"kept_declarations": ["shared", "onlyA", "onlyB"]}})
    assert graph["policies"]["production"]["removed"] == []  # supplied reproducer
    assert graph["edges"] == []
    assert graph["ambiguous_edges"] == [
        {"source_candidates": [0], "target_candidates": [1, 3], "kind_mask": 2},
        {"source_candidates": [1, 3], "target_candidates": [0], "kind_mask": 2},
    ]


def test_qualified_report_records_and_module_fallback_do_not_merge_status():
    graph = artifact(reports={"production": {
        "module_pruning": {"kept_modules": ["A"]},
        "dropped_decls": [{"module": "A", "name": "onlyA"}],
        "protected_declarations": [{"module": "A", "name": "shared"}],
    }})
    state = graph["policies"]["production"]
    assert state["kept"] == [1]
    assert state["removed"] == [0, 2, 3]
    assert state["protected"] == [1]


def test_source_ambiguity_retains_and_flags_every_possible_target():
    decls = declarations() + [dict(name="use", module="C", start_line=3, end_line=3)]
    originals = {**sources(), "/testbed/C.lean": "import A\nimport B\ntheorem use : True := shared\n"}
    paths = {module: f"/testbed/{module}.lean" for module in ("A", "B", "C")}
    ambiguities = []
    deps = strip.augment_deps_with_source(decls, {}, originals, paths, ambiguities=ambiguities)
    assert deps[("C", "use")] == {("A", "shared"), ("B", "shared")}
    assert ambiguities == [{"source": {"module": "C", "name": "use"}, "name": "shared",
                            "candidates": identity_rows({("A", "shared"), ("B", "shared")})}]
    graph = artifact(decls, source_text_edges=dependency_graph.dependency_edges(deps),
                     ambiguous_targets={"source_text": ambiguities})
    assert graph["ambiguous_edges"] == [
        {"source_candidates": [4], "target_candidates": [1, 3], "kind_mask": 1}
    ]


def test_grind_recovery_preserves_duplicate_owner_identity_and_flags_targets():
    report = {"grind_normalization": {"files": [
        {"path": f"/testbed/{module}.lean", "calls": [
            {"tactic_offset": sources()[f"/testbed/{module}.lean"].index("theorem"),
             "normalization": {"retained_parameters": [f"only{module}", "shared"]}}
        ]} for module in ("A", "B")
    ]}}
    graph = artifact(reports={"production": report}, originals=sources(),
                     module_paths={module: f"/testbed/{module}.lean" for module in ("A", "B")})
    state = graph["policies"]["production"]
    assert state["grind_edges"] == [[1, 0], [3, 2]]
    assert len(state["grind_recovery"]["ambiguous_targets"]) == 2


def test_restoring_one_file_updates_only_its_provider_status():
    ids = {decl_id(row) for row in declarations()}
    report = {"dropped_declaration_identities": identity_rows(ids), "kept_declaration_identities": []}
    engine._forget_restored_drops(
        report, {"grind_restored_files": ["/testbed/A.lean"]},
        {identity: identity[0] for identity in ids},
        {module: f"/testbed/{module}.lean" for module in ("A", "B")},
    )
    assert report["kept_declaration_identities"] == identity_rows({("A", "onlyA"), ("A", "shared")})
    assert report["dropped_declaration_identities"] == identity_rows({("B", "onlyB"), ("B", "shared")})


def test_attributes_root_only_the_annotated_provider():
    originals = sources()
    originals["/testbed/A.lean"] = originals["/testbed/A.lean"].replace("theorem shared", "@[simp] theorem shared")
    roots = strip.collect_implicit_dependency_roots(
        declarations(), originals, {module: f"/testbed/{module}.lean" for module in ("A", "B")},
    )
    assert roots["attributed"] == {("A", "shared")}


def test_ilean_ambiguous_targets_keep_module_and_report_candidates():
    decls = [dict(name=name, module=module, start_line=line, start_col=0,
                  end_line=line, end_col=50)
             for module, name, line in (("A", "N1.shared", 1), ("A", "N2.shared", 2),
                                        ("A", "use", 3), ("B", "shared", 1))]
    doc = {"module": "A", "version": 5, "references": {
        json.dumps({"c": {"m": "A", "n": "shared"}}): {"usages": [[3, 20, 3, 25, "use"]]}
    }}
    deps, report = ilean.union_ilean_documents([("A.ilean", doc)], decls, {})
    assert deps == {("A", "use"): {("A", "N1.shared"), ("A", "N2.shared")}}
    assert report["ambiguous_target_usages"] == 1
    assert report["ambiguous_targets"] == [{
        "source": {"module": "A", "name": "use"}, "name": "shared",
        "candidates": identity_rows({("A", "N1.shared"), ("A", "N2.shared")}),
    }]

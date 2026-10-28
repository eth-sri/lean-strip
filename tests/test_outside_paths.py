import json

from lean_strip.cli import _absolutize_outside_paths


def test_paths_leaving_the_project_point_at_their_real_targets(tmp_path):
    # PALOMAR-2026-10-27-000028: a project in `challenges/main-results`
    # requires the repository root by path and shares its packages. From
    # `.lean-strip/work` the relative paths pointed elsewhere.
    root = tmp_path / "repo"
    project = root / "challenges" / "main-results"
    work = project / ".lean-strip" / "work"
    (root / "vendor" / "inner").mkdir(parents=True)
    work.mkdir(parents=True)
    lakefile = '\n'.join([
        'name = "main_results"',
        'packagesDir = "../../.lake/packages"',
        '[[require]]',
        'name = "perron_variational"',
        'path = "../.."',
        '[[require]]',
        'name = "local"',
        'path = "lib"',
    ]) + '\n'
    (project / "lakefile.toml").write_text(lakefile)
    (work / "lakefile.toml").write_text(lakefile)
    manifest = {"version": "1.3.0", "packagesDir": "../../.lake/packages",
                "packages": [{"type": "path", "name": "perron_variational", "dir": "../.."},
                             {"type": "path", "name": "local", "dir": "lib"}]}
    (work / "lake-manifest.json").write_text(json.dumps(manifest))

    changed = _absolutize_outside_paths(project, work)

    text = (work / "lakefile.toml").read_text()
    assert f'path = "{root.resolve()}"' in text
    assert f'packagesDir = "{(root / ".lake" / "packages").resolve()}"' in text
    assert 'path = "lib"' in text  # inside the project: unchanged
    written = json.loads((work / "lake-manifest.json").read_text())
    assert written["packagesDir"] == str((root / ".lake" / "packages").resolve())
    assert written["packages"][0]["dir"] == str(root.resolve())
    assert written["packages"][1]["dir"] == "lib"
    assert (project / "lakefile.toml").read_text() == lakefile  # the repository is untouched
    assert len(changed) == 4

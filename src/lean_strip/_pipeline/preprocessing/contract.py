"""Versioned, declarative description of the preprocessing policy.

engine.py embeds the version, algorithm and :func:`report_contract` in every
report.json, so each report records exactly which policy produced it. The
identifier strings are part of that report format and are kept stable.
"""

from __future__ import annotations

from typing import Any

from lean_strip._pipeline.preprocessing.grind_discovery import DISCOVERY_FLAGS


PREPROCESSING_VERSION = "preprocessing_v25"
PREPROCESSING_ALGORITHM = (
    "verify_raw_query_replay_typed_graph_generated_aux_owner_edges_"
    "exact_environment_roots_strip_"
    "exact_kernel_edges_root_scoped_attributes_prune_selective_opens_with_"
    "source_order_safe_imported_namespace_provenance_"
    "drop_observational_commands_and_anonymous_examples_restore_grind_warm_build_"
    "persist_comparator_exact_discard_empty"
)
PIPELINE_SCHEMA = "leancompression_preprocessing_contract_v25"

FINAL_GRIND_SOURCE_ORIGINAL = "restore_original_after_dependency_discovery"
FAILED_GRIND_FILE_POLICY = "retain_exact_raw_file"


SAFETY_ROOTS = (
    "exact_database_protected_declarations",
    "project_local_attributed_declarations",
    "project_local_syntax_elaborator_and_instance_declarations",
    "exact_environment_command_targets",
    "exact_failed_grind_files",
)


def report_contract() -> dict[str, Any]:
    """Return a JSON-ready copy of the contract embedded in every report."""

    return {
        "schema": PIPELINE_SCHEMA,
        "preprocessing_version": PREPROCESSING_VERSION,
        "algorithm": PREPROCESSING_ALGORITHM,
        "discovery_flags": list(DISCOVERY_FLAGS),
        "safety_roots": list(SAFETY_ROOTS),
        "tactic_trace": False,
        "rebuild_recovery": False,
        "integrity_failure_policy": "fail_repository",
        "dependency_discovery_grind_source": (
            "replay_verified_nonempty_persistent_rules"
        ),
        "final_grind_source_policy": FINAL_GRIND_SOURCE_ORIGINAL,
        "failed_grind_file_policy": FAILED_GRIND_FILE_POLICY,
        "semantic_acceptance_oracle": "official_palomar_comparator",
        "internal_signature_fingerprinting": False,
        "dependency_graph_artifact": "preprocessing_dependency_graph_v2",
        "zero_project_declaration_policy": "discard_from_dataset",
        "module_then_declaration_liveness": True,
        "dead_source_command_policy": (
            "prune_exact_deleted_targets_typed_binders_and_anonymous_examples"
        ),
    }

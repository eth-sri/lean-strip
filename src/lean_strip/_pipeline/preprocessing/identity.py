"""Physical declaration identities, independent of Lean's environment name map."""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Iterable, Mapping
from typing import Any, TypeAlias

DeclId: TypeAlias = tuple[str, str]  # (defining module, full Lean name)
Dependencies: TypeAlias = dict[DeclId, set[DeclId]]
Edge: TypeAlias = tuple[DeclId, DeclId]


def decl_id(declaration: Mapping[str, Any]) -> DeclId:
    return str(declaration["module"]), str(declaration["name"])


def identity_row(identity: DeclId) -> dict[str, str]:
    return {"module": identity[0], "name": identity[1]}


def identity_rows(identities: Iterable[DeclId]) -> list[dict[str, str]]:
    return [identity_row(identity) for identity in sorted(set(identities))]


class DeclarationIndex:
    def __init__(self, declarations: Iterable[Mapping[str, Any]]):
        self.identities = {decl_id(row) for row in declarations}
        self.by_name: dict[str, set[DeclId]] = defaultdict(set)
        for identity in self.identities:
            self.by_name[identity[1]].add(identity)

    def resolve(self, reference: Any) -> set[DeclId]:
        """Qualified references match exactly; legacy names select all copies.

        Callers resolving edges must record multiple candidates as ambiguous.
        In particular, a qualified reference never falls back to another module.
        """
        if isinstance(reference, Mapping):
            if "module" in reference and "name" in reference:
                reference = decl_id(reference)
            else:
                reference = reference.get("name")
        if isinstance(reference, (tuple, list)) and len(reference) == 2:
            identity = tuple(reference)
            return {identity} if identity in self.identities else set()
        if isinstance(reference, str):
            return set(self.by_name.get(reference, ()))
        return set()

    def select(self, references: Iterable[Any]) -> set[DeclId]:
        return {identity for value in references for identity in self.resolve(value)}

    def dependencies(self, dependencies: Mapping[Any, Iterable[Any]]) -> Dependencies:
        result: Dependencies = {}
        for source, targets in dependencies.items():
            resolved = self.select(targets)
            for owner in self.resolve(source):
                result.setdefault(owner, set()).update(resolved)
        return result

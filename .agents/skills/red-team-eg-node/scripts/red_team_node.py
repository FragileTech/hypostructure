"""Build and track one-node red-team audits for the EG proof.

The graph-derived dossier is deliberately a locator, not a mathematical proof
state.  It exposes route alternatives, source records, loops, and formalization
locators so an auditor can reconstruct the exact cumulative contract from the
authoritative sources.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from collections.abc import Iterable
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

PROOF_ID = "erdos-gyarfas"
SCHEMA_VERSION = 1
MANUSCRIPT_REL = Path("to_formalize/erdos_64_proof.tex")
CHECKED_GRAPH_REL = Path("web/frontend/public/data/erdos-gyarfas.json")
LEAN_AUDIT_REL = Path("web/data/eg_node_audit.json")
DEFAULT_CAMPAIGN_REL = Path("audits/erdos-64-red-team")

VERDICTS = (
    "VALID LOCAL COUNTEREXAMPLE",
    "ISOLATED-STATEMENT COUNTEREXAMPLE ONLY",
    "PROSE AMBIGUITY",
    "NONEXHAUSTIVE BRANCH",
    "WRONG ROUTING DESTINATION",
    "MISSING REPRESENTATIVE",
    "MISSING RANGE OR DIVISIBILITY CHECK",
    "NO ISSUE FOUND",
)

REQUIRED_HEADINGS = (
    "## 1. Executive verdict",
    "## 2. Exact node contract",
    "## 3. Sentence audit",
    "## 4. Counterexample attempts",
    "## 5. Strongest valid counterexample",
    "## 6. Local repair",
    "## 7. Regression audit",
    "## 8. Residual uncertainty",
)

CONTRACT_HEADINGS = (
    "### Incoming residual",
    "### Accumulated facts",
    "### Current predicate and exact claim",
    "### Outgoing contracts",
)

CANDIDATE_HEADINGS = (
    "### Smallest-parameter test",
    "### Parity or 2-adic test",
    "### Boundary or range test",
    "### Graph-realizability test",
    "### Branch-routing test",
)

CANDIDATE_FIELDS = (
    "**Explicit data:**",
    "**Hypotheses satisfied:**",
    "**Accumulated facts violated:**",
    "**Applicability:**",
)

REPAIR_HEADINGS = (
    "### Corrected statement",
    "### Complete local proof",
    "### Counterexample disposition",
    "### Graph patch",
    "### Downstream impact",
)

SENTENCE_HEADER = (
    "| Sentence | Exact assertion | Facts used | Hidden obligation | "
    "Adversarial test | Status |"
)

ROUTE_FAMILIES = {
    "type-a": re.compile(r"\btype\s*a\b", re.IGNORECASE),
    "type-b": re.compile(r"\btype\s*b\b", re.IGNORECASE),
    "route-8": re.compile(r"\broute[- ]?8\b", re.IGNORECASE),
    "cold": re.compile(r"\bcold\b", re.IGNORECASE),
    "periodic-response": re.compile(r"periodic\s+response", re.IGNORECASE),
    "target-defect": re.compile(r"target[- ]defect", re.IGNORECASE),
    "support-dependence": re.compile(r"support[- ]depend", re.IGNORECASE),
    "sparse-exit": re.compile(r"sparse\s+(?:surplus\s+)?exit", re.IGNORECASE),
}


class AuditError(RuntimeError):
    """An actionable validation or repository error."""


def _utc_now() -> str:
    return datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _hash_json(value: Any) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


def _hash_file(path: Path) -> str:
    if not path.exists():
        return "absent"
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _node_key(node_id: str) -> tuple[int, str]:
    return (int(node_id), node_id) if node_id.isdigit() else (10**9, node_id)


def _edge_key(edge: dict[str, Any]) -> tuple[tuple[int, str], tuple[int, str], str]:
    return (_node_key(edge["source"]), _node_key(edge["target"]), edge.get("id", ""))


def discover_repo_root(candidate: Path | None = None) -> Path:
    starts = []
    if candidate is not None:
        starts.append(candidate.resolve())
    starts.extend([Path.cwd().resolve(), Path(__file__).resolve()])
    seen: set[Path] = set()
    for start in starts:
        current = start if start.is_dir() else start.parent
        for path in (current, *current.parents):
            if path in seen:
                continue
            seen.add(path)
            if (path / MANUSCRIPT_REL).is_file() and (path / "web/tools/proof_graph.py").is_file():
                return path
    raise AuditError("could not locate the repository root containing the EG manuscript and graph tools")


def _git_value(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=root, text=True, capture_output=True, check=False
    )
    return result.stdout.strip() if result.returncode == 0 else "unknown"


def load_live_document(root: Path) -> dict[str, Any]:
    tools_dir = root / "web/tools"
    tools_text = str(tools_dir)
    if tools_text not in sys.path:
        sys.path.insert(0, tools_text)
    try:
        from lean_review import build_review  # type: ignore
        from papers.erdos64 import SPEC  # type: ignore
        from proof_graph import build_document  # type: ignore
    except ImportError as exc:  # pragma: no cover - environment-specific message
        raise AuditError(f"could not import the repository graph tools: {exc}") from exc

    document = build_document(SPEC, root)
    review = build_review(root)
    if review:
        document["review"] = review
    return document


class GraphContext:
    """Live graph and source records used to prepare node dossiers."""

    def __init__(self, root: Path):
        self.root = discover_repo_root(root)
        self.document = load_live_document(self.root)
        self.nodes = {str(node["id"]): node for node in self.document.get("nodes", [])}
        self.edges = list(self.document.get("edges", []))
        self.items = {str(item["key"]): item for item in self.document.get("items", [])}
        self.invariants = {
            str(invariant["id"]): invariant
            for invariant in self.document.get("invariants", [])
        }
        self.groups = {str(group["id"]): group for group in self.document.get("groups", [])}
        self._contract_sha_cache: dict[str, str] = {}
        self.incoming: dict[str, list[dict[str, Any]]] = defaultdict(list)
        self.outgoing: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for edge in self.edges:
            self.incoming[str(edge["target"])].append(edge)
            self.outgoing[str(edge["source"])].append(edge)
        for value in self.incoming.values():
            value.sort(key=_edge_key)
        for value in self.outgoing.values():
            value.sort(key=_edge_key)

        self._validate_graph()
        self.sccs, self.scc_of = self._strongly_connected_components()
        self.dominators = self._dominators()
        self.lean_audit = self._load_optional_json(self.root / LEAN_AUDIT_REL)

        graph_basis = {
            "nodes": self.document.get("nodes", []),
            "edges": self.edges,
            "items": self.document.get("items", []),
            "invariants": self.document.get("invariants", []),
            "constants": self.document.get("constants", []),
            "groups": self.document.get("groups", []),
        }
        checked_document = self._load_optional_json(self.root / CHECKED_GRAPH_REL)
        checked_graph_basis = {
            key: checked_document.get(key, [])
            for key in ("nodes", "edges", "items", "invariants", "constants", "groups")
        }
        live_graph_sha = _hash_json(graph_basis)
        checked_semantic_sha = (
            _hash_json(checked_graph_basis) if checked_document else "absent"
        )
        self.source_fingerprints = {
            "manuscript_sha256": _hash_file(self.root / MANUSCRIPT_REL),
            "graph_sha256": live_graph_sha,
            "checked_graph_sha256": _hash_file(self.root / CHECKED_GRAPH_REL),
            "checked_graph_semantic_sha256": checked_semantic_sha,
            "graph_drift": checked_semantic_sha not in {"absent", live_graph_sha},
            "lean_audit_sha256": _hash_file(self.root / LEAN_AUDIT_REL),
            "git_commit": _git_value(self.root, "rev-parse", "HEAD"),
            "git_dirty": bool(_git_value(self.root, "status", "--short")),
        }

    @staticmethod
    def _load_optional_json(path: Path) -> dict[str, Any]:
        if not path.exists():
            return {}
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise AuditError(f"could not read {path}: {exc}") from exc
        if not isinstance(value, dict):
            raise AuditError(f"expected a JSON object in {path}")
        return value

    def _validate_graph(self) -> None:
        if not self.nodes:
            raise AuditError("the live proof graph contains no nodes")
        if any(not node_id.isdigit() for node_id in self.nodes):
            raise AuditError("the EG graph contains a nonnumeric node identifier")
        numbers = sorted(int(node_id) for node_id in self.nodes)
        if numbers != list(range(numbers[0], numbers[-1] + 1)):
            raise AuditError("the live EG node numbers are not contiguous")
        if numbers[0] != 1:
            raise AuditError("the live EG graph does not start at node [1]")
        roots = [node_id for node_id in self.nodes if not self.incoming[node_id]]
        if roots != ["1"]:
            raise AuditError(f"expected the unique graph root [1], found {roots}")
        for edge in self.edges:
            if edge["source"] not in self.nodes or edge["target"] not in self.nodes:
                raise AuditError(f"unresolved edge: {edge}")
        for node_id, node in self.nodes.items():
            if node.get("shape") == "terminal" and self.outgoing[node_id]:
                raise AuditError(f"terminal node [{node_id}] has a live outgoing edge")

    def _strongly_connected_components(self) -> tuple[list[list[str]], dict[str, int]]:
        index = 0
        indices: dict[str, int] = {}
        low: dict[str, int] = {}
        stack: list[str] = []
        on_stack: set[str] = set()
        components: list[list[str]] = []

        def visit(node_id: str) -> None:
            nonlocal index
            indices[node_id] = index
            low[node_id] = index
            index += 1
            stack.append(node_id)
            on_stack.add(node_id)
            for edge in self.outgoing[node_id]:
                target = str(edge["target"])
                if target not in indices:
                    visit(target)
                    low[node_id] = min(low[node_id], low[target])
                elif target in on_stack:
                    low[node_id] = min(low[node_id], indices[target])
            if low[node_id] != indices[node_id]:
                return
            component: list[str] = []
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.append(member)
                if member == node_id:
                    break
            component.sort(key=_node_key)
            components.append(component)

        for node_id in sorted(self.nodes, key=_node_key):
            if node_id not in indices:
                visit(node_id)
        components.sort(key=lambda members: _node_key(members[0]))
        scc_of = {
            member: component_id
            for component_id, members in enumerate(components)
            for member in members
        }
        return components, scc_of

    def _reachable_from_root(self) -> set[str]:
        seen = {"1"}
        stack = ["1"]
        while stack:
            source = stack.pop()
            for edge in self.outgoing[source]:
                target = str(edge["target"])
                if target not in seen:
                    seen.add(target)
                    stack.append(target)
        return seen

    def _dominators(self) -> dict[str, set[str]]:
        reachable = self._reachable_from_root()
        if reachable != set(self.nodes):
            missing = sorted(set(self.nodes) - reachable, key=_node_key)
            raise AuditError(f"nodes are unreachable from [1]: {missing}")
        dominators = {
            node_id: ({"1"} if node_id == "1" else set(reachable))
            for node_id in reachable
        }
        changed = True
        while changed:
            changed = False
            for node_id in sorted(reachable - {"1"}, key=_node_key):
                predecessors = [str(edge["source"]) for edge in self.incoming[node_id]]
                common = set(reachable)
                for predecessor in predecessors:
                    common &= dominators[predecessor]
                candidate = {node_id} | common
                if candidate != dominators[node_id]:
                    dominators[node_id] = candidate
                    changed = True
        return dominators

    def reverse_reachable(self, node_id: str) -> set[str]:
        seen = {node_id}
        stack = [node_id]
        while stack:
            target = stack.pop()
            for edge in self.incoming[target]:
                source = str(edge["source"])
                if source not in seen:
                    seen.add(source)
                    stack.append(source)
        return seen

    def forward_reachable(self, node_id: str) -> set[str]:
        seen = {node_id}
        stack = [node_id]
        while stack:
            source = stack.pop()
            for edge in self.outgoing[source]:
                target = str(edge["target"])
                if target not in seen:
                    seen.add(target)
                    stack.append(target)
        return seen

    def _expand_items(self, initial: Iterable[str]) -> set[str]:
        seen: set[str] = set()
        stack = [key for key in initial if key in self.items]
        while stack:
            key = stack.pop()
            if key in seen:
                continue
            seen.add(key)
            for required in self.items[key].get("requiresItems", []):
                if required in self.items and required not in seen:
                    stack.append(required)
        return seen

    @staticmethod
    def _node_record(node: dict[str, Any]) -> dict[str, Any]:
        fields = (
            "id",
            "number",
            "shape",
            "label",
            "group",
            "chapter",
            "overview",
            "formalContent",
            "failureRoute",
            "itemRefs",
            "invariantRefs",
            "constantRefs",
            "topics",
            "aliases",
            "blocks",
            "dossier",
        )
        return {field: node[field] for field in fields if field in node}

    @staticmethod
    def _edge_record(edge: dict[str, Any]) -> dict[str, Any]:
        return {
            field: edge.get(field)
            for field in ("id", "source", "target", "branch", "kind")
        }

    def _loop_record(self, node_id: str) -> dict[str, Any] | None:
        component_id = self.scc_of[node_id]
        members = self.sccs[component_id]
        has_self_loop = any(
            edge["source"] == node_id and edge["target"] == node_id for edge in self.edges
        )
        if len(members) == 1 and not has_self_loop:
            return None
        member_set = set(members)
        internal = [
            self._edge_record(edge)
            for edge in self.edges
            if edge["source"] in member_set and edge["target"] in member_set
        ]
        ingress = [
            self._edge_record(edge)
            for edge in self.edges
            if edge["source"] not in member_set and edge["target"] in member_set
        ]
        egress = [
            self._edge_record(edge)
            for edge in self.edges
            if edge["source"] in member_set and edge["target"] not in member_set
        ]
        return {
            "members": members,
            "internal_edges": sorted(internal, key=_edge_key),
            "ingress_edges": sorted(ingress, key=_edge_key),
            "egress_edges": sorted(egress, key=_edge_key),
            "requires_explicit_iteration_state": True,
            "requires_decreasing_measure": True,
        }

    def _route_alternatives(self, node_id: str) -> list[dict[str, Any]]:
        common = self.dominators[node_id] - {node_id}
        alternatives = []
        for edge in self.incoming[node_id]:
            source = str(edge["source"])
            source_cone = self.reverse_reachable(source) - {node_id}
            alternatives.append(
                {
                    "edge": self._edge_record(edge),
                    "same_scc": self.scc_of[source] == self.scc_of[node_id],
                    "candidate_predecessor_nodes": sorted(source_cone, key=_node_key),
                    "route_specific_candidates": sorted(source_cone - common, key=_node_key),
                    "warning": (
                        "These are graph candidates. Confirm retained facts and branch tags in "
                        "the manuscript/ledger; do not union sibling routes."
                    ),
                }
            )
        return alternatives

    def _unwired_routing_candidates(self, node_id: str) -> list[dict[str, Any]]:
        """Surface prose route families absent from the directed ancestry.

        This is intentionally heuristic. It never creates an edge; it gives the
        auditor a finite list of graph/prose discrepancies to verify in TeX.
        """

        target = self.nodes[node_id]
        target_text = " ".join(
            str(target.get(field, "")) for field in ("label", "overview", "topics")
        )
        families = {
            name for name, pattern in ROUTE_FAMILIES.items() if pattern.search(target_text)
        }
        if not families:
            return []
        ancestors = self.reverse_reachable(node_id)
        descendants = self.forward_reachable(node_id)
        candidates = []
        for source_id, source in self.nodes.items():
            if source_id in ancestors or source_id in descendants:
                continue
            source_text = " ".join(
                str(source.get(field, ""))
                for field in ("label", "overview", "formalContent", "failureRoute")
            )
            matched = sorted(
                name
                for name in families
                if ROUTE_FAMILIES[name].search(source_text)
            )
            route_like = source.get("shape") == "terminal" or re.search(
                r"\b(route|handoff|continue|send|enter)\w*\b", source_text, re.IGNORECASE
            )
            if not matched or not route_like:
                continue
            candidates.append(
                {
                    "source": self._node_record(source),
                    "matched_route_families": matched,
                    "warning": (
                        "No directed path from this node to the audited node was extracted. "
                        "Inspect the manuscript: this may be a terminal summary, an intentional "
                        "closure, or a missing/wrong routing edge."
                    ),
                }
            )
        candidates.sort(key=lambda record: _node_key(record["source"]["id"]))
        return candidates

    def _contract_basis(self, node_id: str) -> dict[str, Any]:
        ancestors = self.reverse_reachable(node_id) - {node_id}
        destinations = {str(edge["target"]) for edge in self.outgoing[node_id]}
        relevant_nodes = ancestors | {node_id} | destinations

        unwired_candidates = self._unwired_routing_candidates(node_id)
        initial_items: set[str] = set()
        invariant_keys: set[str] = set()
        for relevant_id in relevant_nodes:
            node = self.nodes[relevant_id]
            initial_items.update(node.get("itemRefs", []))
            invariant_keys.update(node.get("invariantRefs", []))
            for block in node.get("blocks", []):
                initial_items.update(block.get("itemRefs", []))
        for candidate in unwired_candidates:
            initial_items.update(candidate["source"].get("itemRefs", []))
        item_keys = self._expand_items(initial_items)

        relevant_edges = [
            self._edge_record(edge)
            for edge in self.edges
            if edge["source"] in relevant_nodes and edge["target"] in relevant_nodes
        ]
        basis = {
            "proof": PROOF_ID,
            "node": node_id,
            "node_records": [
                self._node_record(self.nodes[key])
                for key in sorted(relevant_nodes, key=_node_key)
            ],
            "edges": sorted(relevant_edges, key=_edge_key),
            "common_dominators": sorted(self.dominators[node_id] - {node_id}, key=_node_key),
            "route_alternatives": self._route_alternatives(node_id),
            "unwired_routing_candidates": unwired_candidates,
            "loop": self._loop_record(node_id),
            "items": [self.items[key] for key in sorted(item_keys)],
            "invariants": [
                self.invariants[key] for key in sorted(invariant_keys) if key in self.invariants
            ],
            "target_lean_audit": self.lean_audit.get("nodes", {}).get(node_id),
            "target_lean_review": self.document.get("review", {}).get("nodes", {}).get(node_id),
        }
        return basis

    def contract_sha256(self, node_id: str) -> str:
        if node_id not in self.nodes:
            raise AuditError(f"node [{node_id}] does not exist in the live graph")
        if node_id not in self._contract_sha_cache:
            self._contract_sha_cache[node_id] = _hash_json(self._contract_basis(node_id))
        return self._contract_sha_cache[node_id]

    def dossier(self, node_number: int | str) -> dict[str, Any]:
        node_id = str(int(node_number))
        if node_id not in self.nodes:
            raise AuditError(f"node [{node_id}] does not exist in the live graph")
        node = self.nodes[node_id]
        ancestors = self.reverse_reachable(node_id) - {node_id}
        common = self.dominators[node_id] - {node_id}
        local_keys = self._expand_items(node.get("itemRefs", []))
        outgoing_destinations = []
        for edge in self.outgoing[node_id]:
            destination = self.nodes[str(edge["target"])]
            outgoing_destinations.append(
                {
                    "edge": self._edge_record(edge),
                    "destination": self._node_record(destination),
                }
            )

        reverse_item_dependencies: dict[str, list[str]] = {}
        occurrence_lines: dict[str, list[int]] = {}
        manuscript_lines = (self.root / MANUSCRIPT_REL).read_text(encoding="utf-8").splitlines()
        for key in node.get("itemRefs", []):
            plain_key = key.split("/", 1)[-1]
            reverse_item_dependencies[key] = sorted(
                item_key
                for item_key, item in self.items.items()
                if key in item.get("requiresItems", [])
            )
            occurrence_lines[key] = [
                line_number
                for line_number, line in enumerate(manuscript_lines, start=1)
                if plain_key in line
            ]

        basis = self._contract_basis(node_id)
        dossier = {
            "schema_version": SCHEMA_VERSION,
            "proof": PROOF_ID,
            "generated_at": _utc_now(),
            "automation_warning": (
                "Graph ancestry and attached sources are candidates only. Reconstruct the exact "
                "retained mathematical state from TeX and the literal Lean ledger; never union "
                "sibling routes mechanically. The fingerprint basis also includes outgoing "
                "destination material to detect routing-contract drift; it is not an accumulated "
                "fact ledger."
            ),
            "source_fingerprints": self.source_fingerprints,
            "contract_sha256": _hash_json(basis),
            "node": self._node_record(node),
            "panel": self.groups.get(str(node.get("group"))),
            "immediate_incoming": [self._edge_record(edge) for edge in self.incoming[node_id]],
            "immediate_outgoing": [self._edge_record(edge) for edge in self.outgoing[node_id]],
            "common_dominator_nodes": [
                self._node_record(self.nodes[key]) for key in sorted(common, key=_node_key)
            ],
            "all_ancestor_node_ids": sorted(ancestors, key=_node_key),
            "route_alternatives": self._route_alternatives(node_id),
            "unwired_routing_candidates": self._unwired_routing_candidates(node_id),
            "loop_context": self._loop_record(node_id),
            "local_sources": [
                self.items[key] for key in sorted(local_keys) if key in self.items
            ],
            "node_invariants": [
                self.invariants[key]
                for key in node.get("invariantRefs", [])
                if key in self.invariants
            ],
            "outgoing_destinations": outgoing_destinations,
            "lean_audit_locator": self.lean_audit.get("nodes", {}).get(node_id),
            "lean_review_summary": self.document.get("review", {}).get("nodes", {}).get(node_id),
            "regression_candidates": {
                "reverse_item_dependencies": reverse_item_dependencies,
                "manuscript_occurrence_lines": occurrence_lines,
            },
            "fingerprint_scope": (
                "Route-relevant ancestry candidates, the current node, outgoing destination "
                "contracts, cited items/invariants, loop structure, and formalization locators. "
                "This payload exists only to detect drift."
            ),
            "fingerprint_basis": basis,
        }
        return dossier


def render_dossier_markdown(dossier: dict[str, Any]) -> str:
    node = dossier["node"]
    lines = [
        f"# EG node [{node['id']}] dossier",
        "",
        f"- Shape: `{node.get('shape')}`",
        f"- Panel: `{node.get('group')}`",
        f"- Label: {node.get('label', '')}",
        f"- Contract SHA-256: `{dossier['contract_sha256']}`",
        "",
        f"> {dossier['automation_warning']}",
        "",
        "## Immediate incoming edges",
        "",
    ]
    incoming = dossier["immediate_incoming"]
    if incoming:
        for edge in incoming:
            lines.append(
                f"- [{edge['source']}] -> [{edge['target']}], "
                f"branch `{edge.get('branch')}`, kind `{edge.get('kind')}`"
            )
    else:
        lines.append("- None (root node).")

    lines.extend(["", "## Immediate outgoing edges", ""])
    outgoing = dossier["immediate_outgoing"]
    if outgoing:
        for edge in outgoing:
            lines.append(
                f"- [{edge['source']}] -> [{edge['target']}], "
                f"branch `{edge.get('branch')}`, kind `{edge.get('kind')}`"
            )
    else:
        lines.append("- None (terminal node).")

    lines.extend(["", "## Graph-theoretic common dominators", ""])
    dominators = dossier["common_dominator_nodes"]
    if dominators:
        for record in dominators:
            lines.append(f"- [{record['id']}] {record.get('label', '')}")
    else:
        lines.append("- None.")

    lines.extend(["", "## Route alternatives", ""])
    if dossier["route_alternatives"]:
        for alternative in dossier["route_alternatives"]:
            edge = alternative["edge"]
            route_nodes = ", ".join(alternative["route_specific_candidates"]) or "none"
            lines.append(
                f"- From [{edge['source']}] (`{edge.get('branch')}`); "
                f"same SCC: `{alternative['same_scc']}`; route-specific candidates: {route_nodes}."
            )
    else:
        lines.append("- None.")

    lines.extend(["", "## Loop context", ""])
    loop = dossier.get("loop_context")
    if loop:
        lines.append(f"- SCC members: {', '.join(loop['members'])}")
        for edge in loop["internal_edges"]:
            lines.append(
                f"- Internal [{edge['source']}] -> [{edge['target']}], branch `{edge.get('branch')}`"
            )
        lines.append("- The audit must identify the iteration state and decreasing measure.")
    else:
        lines.append("- This node is not in a nontrivial SCC.")

    lines.extend(["", "## Local manuscript sources", ""])
    if dossier["local_sources"]:
        for item in dossier["local_sources"]:
            lines.extend(
                [
                    f"### `{item['key']}` — {item.get('title', '')}",
                    "",
                    f"Source line: {item.get('sourceLine', 'unknown')}",
                    "",
                    "**Statement**",
                    "",
                    item.get("statementLatex", ""),
                    "",
                    "**Proof**",
                    "",
                    item.get("proofLatex", "") or "(No proof body extracted.)",
                    "",
                ]
            )
    else:
        lines.append("- No precise result is attached; locate the routing/table source manually.")

    lines.extend(["## Outgoing destination candidates", ""])
    for outgoing_record in dossier["outgoing_destinations"]:
        destination = outgoing_record["destination"]
        edge = outgoing_record["edge"]
        lines.append(
            f"- Branch `{edge.get('branch')}` -> [{destination['id']}] "
            f"{destination.get('label', '')}; source refs: "
            f"{', '.join(destination.get('itemRefs', [])) or 'none'}"
        )
    if not dossier["outgoing_destinations"]:
        lines.append("- None.")

    lines.extend(["", "## Unwired routing candidates", ""])
    candidates = dossier.get("unwired_routing_candidates", [])
    if candidates:
        for candidate in candidates:
            source = candidate["source"]
            families = ", ".join(candidate["matched_route_families"])
            lines.append(
                f"- [{source['id']}] {source.get('label', '')}; matched families: {families}."
            )
    else:
        lines.append("- None found by the route-family heuristic.")

    lines.extend(
        [
            "",
            "## Formalization locator",
            "",
            "```json",
            json.dumps(dossier.get("lean_audit_locator"), ensure_ascii=False, indent=2),
            "```",
            "",
            "## Source fingerprints",
            "",
            "```json",
            json.dumps(dossier["source_fingerprints"], ensure_ascii=False, indent=2),
            "```",
            "",
        ]
    )
    return "\n".join(lines)


METADATA_RE = re.compile(
    r"\A\s*<!--\s*red-team-audit\s*\n(?P<payload>\{.*?\})\s*\n-->\s*",
    re.DOTALL,
)


def parse_report_metadata(text: str) -> dict[str, Any]:
    match = METADATA_RE.search(text)
    if not match:
        raise AuditError("report must begin with the red-team-audit JSON comment")
    try:
        metadata = json.loads(match.group("payload"))
    except json.JSONDecodeError as exc:
        raise AuditError(f"invalid report metadata JSON: {exc}") from exc
    if not isinstance(metadata, dict):
        raise AuditError("report metadata must be a JSON object")
    return metadata


def _heading_body(text: str, heading: str, all_headings: Iterable[str]) -> str:
    start = text.find(heading)
    if start < 0:
        raise AuditError(f"missing required heading: {heading}")
    start += len(heading)
    ends = [text.find(other, start) for other in all_headings if text.find(other, start) >= 0]
    end = min(ends) if ends else len(text)
    return text[start:end].strip()


def _validate_candidate_section(text: str, heading: str) -> None:
    all_boundaries = (*CANDIDATE_HEADINGS, REQUIRED_HEADINGS[4])
    body = _heading_body(text, heading, all_boundaries)
    for index, field in enumerate(CANDIDATE_FIELDS):
        position = body.find(field)
        if position < 0:
            raise AuditError(f"{heading} is missing {field}")
        content_start = position + len(field)
        later_positions = [
            body.find(other, content_start)
            for other in CANDIDATE_FIELDS[index + 1 :]
            if body.find(other, content_start) >= 0
        ]
        content_end = min(later_positions) if later_positions else len(body)
        content = body[content_start:content_end].strip(" \n-\t")
        if not content:
            raise AuditError(f"{heading} has no content for {field}")


def validate_report(report: Path, context: GraphContext) -> dict[str, Any]:
    try:
        text = report.read_text(encoding="utf-8")
    except OSError as exc:
        raise AuditError(f"could not read report {report}: {exc}") from exc
    if any(token in text for token in ("COPY_FROM_DOSSIER", "ONE CLOSED-TAXONOMY VERDICT", "TODO")):
        raise AuditError("report still contains template placeholders")

    metadata = parse_report_metadata(text)
    required_metadata = {
        "schema_version",
        "proof",
        "node",
        "node_label",
        "panel",
        "contract_sha256",
        "manuscript_sha256",
        "graph_sha256",
        "lean_audit_sha256",
        "verdict",
        "audited_at",
    }
    missing = sorted(required_metadata - set(metadata))
    if missing:
        raise AuditError(f"report metadata is missing: {', '.join(missing)}")
    if metadata["schema_version"] != SCHEMA_VERSION:
        raise AuditError(f"unsupported report schema_version {metadata['schema_version']!r}")
    if metadata["proof"] != PROOF_ID:
        raise AuditError(f"report proof must be {PROOF_ID!r}")
    try:
        node_id = str(int(metadata["node"]))
    except (TypeError, ValueError) as exc:
        raise AuditError("report node must be one integer") from exc
    if node_id not in context.nodes:
        raise AuditError(f"report names nonexistent node [{node_id}]")
    if metadata["verdict"] not in VERDICTS:
        raise AuditError(f"invalid verdict {metadata['verdict']!r}")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", str(metadata["audited_at"])):
        raise AuditError("audited_at must use UTC YYYY-MM-DDTHH:MM:SSZ")

    current = context.dossier(node_id)
    expected_values = {
        "node_label": current["node"].get("label", ""),
        "panel": current["node"].get("group", ""),
        "contract_sha256": current["contract_sha256"],
        "manuscript_sha256": current["source_fingerprints"]["manuscript_sha256"],
        "graph_sha256": current["source_fingerprints"]["graph_sha256"],
        "lean_audit_sha256": current["source_fingerprints"]["lean_audit_sha256"],
    }
    for field, expected in expected_values.items():
        if metadata[field] != expected:
            raise AuditError(
                f"stale or incorrect {field}: report has {metadata[field]!r}, current value is {expected!r}"
            )

    title = f"# Red-team audit: node [{int(node_id)}]"
    if not re.search(rf"(?m)^{re.escape(title)}\s*$", text):
        raise AuditError(f"report title must be exactly {title!r}")
    for heading in (*REQUIRED_HEADINGS, *CONTRACT_HEADINGS, *CANDIDATE_HEADINGS, *REPAIR_HEADINGS):
        if not re.search(rf"(?m)^{re.escape(heading)}\s*$", text):
            raise AuditError(f"missing required heading: {heading}")

    positions = [text.find(heading) for heading in REQUIRED_HEADINGS]
    if positions != sorted(positions):
        raise AuditError("the eight required report sections are out of order")

    executive = _heading_body(text, REQUIRED_HEADINGS[0], REQUIRED_HEADINGS[1:])
    verdict_matches = re.findall(r"(?m)^Verdict:\s*\*\*([^*]+)\*\*\s*$", executive)
    if len(verdict_matches) != 1:
        raise AuditError("the executive section must contain exactly one bold Verdict line")
    if verdict_matches[0] != metadata["verdict"]:
        raise AuditError("metadata verdict and executive verdict do not match")
    executive_without_verdict = re.sub(
        r"(?m)^Verdict:\s*\*\*[^*]+\*\*\s*$", "", executive
    ).strip()
    if len(executive_without_verdict) < 40:
        raise AuditError("the executive verdict needs a substantive node-local paragraph")

    sentence_section = _heading_body(
        text, REQUIRED_HEADINGS[2], REQUIRED_HEADINGS[3:]
    )
    if SENTENCE_HEADER not in sentence_section:
        raise AuditError("sentence audit table header does not match the required contract")
    table_lines = [line for line in sentence_section.splitlines() if line.strip().startswith("|")]
    if len(table_lines) < 3:
        raise AuditError("sentence audit table must contain at least one operative sentence row")

    for heading in CANDIDATE_HEADINGS:
        _validate_candidate_section(text, heading)

    for heading in REQUIRED_HEADINGS:
        body = _heading_body(text, heading, REQUIRED_HEADINGS)
        if len(body) < 20:
            raise AuditError(f"section {heading!r} is empty or too short")

    return metadata


def _campaign_root(root: Path, value: Path | None) -> Path:
    if value is None:
        return root / DEFAULT_CAMPAIGN_REL
    return value if value.is_absolute() else root / value


def _report_rel(node_id: str) -> str:
    return f"reports/node-{int(node_id):03}.md"


def _new_ledger(context: GraphContext) -> dict[str, Any]:
    entries = {}
    for node_id in sorted(context.nodes, key=_node_key):
        node = context.nodes[node_id]
        entries[node_id] = {
            "label": node.get("label", ""),
            "panel": node.get("group", ""),
            "shape": node.get("shape", ""),
            "status": "pending",
            "verdict": None,
            "report": _report_rel(node_id),
            "audited_at": None,
            "recorded_contract_sha256": None,
            "current_contract_sha256": context.contract_sha256(node_id),
        }
    return {
        "schema_version": SCHEMA_VERSION,
        "proof": PROOF_ID,
        "node_count": len(entries),
        "updated_at": _utc_now(),
        "source_snapshot": context.source_fingerprints,
        "nodes": entries,
        "retired_nodes": {},
    }


def _write_json_atomic(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _load_ledger(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise AuditError(f"coverage ledger does not exist: {path}; run init first")
    try:
        ledger = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise AuditError(f"could not read coverage ledger {path}: {exc}") from exc
    if ledger.get("schema_version") != SCHEMA_VERSION or ledger.get("proof") != PROOF_ID:
        raise AuditError("coverage ledger has the wrong schema or proof id")
    if not isinstance(ledger.get("nodes"), dict):
        raise AuditError("coverage ledger has no node map")
    return ledger


def init_campaign(context: GraphContext, campaign_root: Path) -> Path:
    ledger_path = campaign_root / "coverage.json"
    if ledger_path.exists():
        raise AuditError(f"refusing to overwrite existing coverage ledger: {ledger_path}")
    (campaign_root / "reports").mkdir(parents=True, exist_ok=True)
    _write_json_atomic(ledger_path, _new_ledger(context))
    return ledger_path


def sync_campaign(context: GraphContext, campaign_root: Path) -> dict[str, Any]:
    ledger_path = campaign_root / "coverage.json"
    ledger = _load_ledger(ledger_path)
    old_nodes = ledger["nodes"]
    retired = ledger.setdefault("retired_nodes", {})
    for node_id in list(old_nodes):
        if node_id not in context.nodes:
            retired[node_id] = old_nodes.pop(node_id)
            retired[node_id]["status"] = "retired"

    for node_id in sorted(context.nodes, key=_node_key):
        node = context.nodes[node_id]
        current_sha = context.contract_sha256(node_id)
        entry = old_nodes.setdefault(
            node_id,
            {
                "status": "pending",
                "verdict": None,
                "report": _report_rel(node_id),
                "audited_at": None,
                "recorded_contract_sha256": None,
            },
        )
        entry.update(
            {
                "label": node.get("label", ""),
                "panel": node.get("group", ""),
                "shape": node.get("shape", ""),
                "current_contract_sha256": current_sha,
            }
        )
        recorded = entry.get("recorded_contract_sha256")
        recorded_sources = entry.get("source_fingerprints", {})
        source_drift = any(
            recorded_sources.get(key) not in {None, context.source_fingerprints[key]}
            for key in ("manuscript_sha256", "graph_sha256", "lean_audit_sha256")
        )
        report_path = campaign_root / entry.get("report", _report_rel(node_id))
        if recorded:
            if recorded != current_sha or source_drift:
                entry["status"] = "stale"
            elif not report_path.exists():
                entry["status"] = "missing-report"
            else:
                entry["status"] = "audited"
        else:
            entry["status"] = "pending"

    ledger.update(
        {
            "node_count": len(context.nodes),
            "updated_at": _utc_now(),
            "source_snapshot": context.source_fingerprints,
        }
    )
    _write_json_atomic(ledger_path, ledger)
    return ledger


def campaign_status(context: GraphContext, campaign_root: Path) -> dict[str, Any]:
    ledger = _load_ledger(campaign_root / "coverage.json")
    states: dict[str, list[str]] = defaultdict(list)
    verdicts: Counter[str] = Counter()
    for node_id in sorted(context.nodes, key=_node_key):
        entry = ledger["nodes"].get(node_id)
        if entry is None:
            state = "pending"
        else:
            current_sha = context.contract_sha256(node_id)
            recorded = entry.get("recorded_contract_sha256")
            recorded_sources = entry.get("source_fingerprints", {})
            source_drift = any(
                recorded_sources.get(key) not in {None, context.source_fingerprints[key]}
                for key in ("manuscript_sha256", "graph_sha256", "lean_audit_sha256")
            )
            report_path = campaign_root / entry.get("report", _report_rel(node_id))
            if not recorded:
                state = "pending"
            elif recorded != current_sha or source_drift:
                state = "stale"
            elif not report_path.exists():
                state = "missing-report"
            else:
                state = "audited"
                if entry.get("verdict"):
                    verdicts[str(entry["verdict"])] += 1
        states[state].append(node_id)
    return {
        "proof": PROOF_ID,
        "node_count": len(context.nodes),
        "counts": {key: len(value) for key, value in sorted(states.items())},
        "nodes": {key: value for key, value in sorted(states.items())},
        "verdicts": dict(sorted(verdicts.items())),
        "retired_count": len(ledger.get("retired_nodes", {})),
    }


def record_report(context: GraphContext, campaign_root: Path, report: Path) -> dict[str, Any]:
    metadata = validate_report(report, context)
    node_id = str(int(metadata["node"]))
    expected = (campaign_root / _report_rel(node_id)).resolve()
    if report.resolve() != expected:
        raise AuditError(f"report for node [{node_id}] must be stored at {expected}")

    ledger_path = campaign_root / "coverage.json"
    ledger = _load_ledger(ledger_path)
    if node_id not in ledger["nodes"]:
        raise AuditError(f"coverage ledger has no entry for node [{node_id}]; run sync")
    entry = ledger["nodes"][node_id]
    entry.update(
        {
            "label": context.nodes[node_id].get("label", ""),
            "panel": context.nodes[node_id].get("group", ""),
            "shape": context.nodes[node_id].get("shape", ""),
            "status": "audited",
            "verdict": metadata["verdict"],
            "report": _report_rel(node_id),
            "audited_at": metadata["audited_at"],
            "recorded_contract_sha256": metadata["contract_sha256"],
            "current_contract_sha256": metadata["contract_sha256"],
            "source_fingerprints": {
                key: metadata[key]
                for key in ("manuscript_sha256", "graph_sha256", "lean_audit_sha256")
            },
        }
    )
    ledger["updated_at"] = _utc_now()
    ledger["source_snapshot"] = context.source_fingerprints
    _write_json_atomic(ledger_path, ledger)
    return entry


def _write_output(path: Path | None, content: str) -> None:
    if path is None:
        print(content)
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    print(path)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    def add_repo(command: argparse.ArgumentParser) -> None:
        command.add_argument("--repo-root", type=Path, default=Path.cwd())

    dossier = subparsers.add_parser("dossier", help="build a fresh one-node source dossier")
    add_repo(dossier)
    dossier.add_argument("--node", type=int, required=True)
    dossier.add_argument("--format", choices=("json", "markdown"), default="json")
    dossier.add_argument("--output", type=Path)

    init = subparsers.add_parser("init", help="initialize the campaign ledger")
    add_repo(init)
    init.add_argument("--campaign-root", type=Path)

    sync = subparsers.add_parser("sync", help="reconcile campaign nodes and stale contracts")
    add_repo(sync)
    sync.add_argument("--campaign-root", type=Path)

    validate = subparsers.add_parser("validate", help="validate one report against live sources")
    add_repo(validate)
    validate.add_argument("--report", type=Path, required=True)

    record = subparsers.add_parser("record", help="validate and record one canonical report")
    add_repo(record)
    record.add_argument("--campaign-root", type=Path)
    record.add_argument("--report", type=Path, required=True)

    status = subparsers.add_parser("status", help="show campaign coverage and staleness")
    add_repo(status)
    status.add_argument("--campaign-root", type=Path)
    status.add_argument("--json", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        root = discover_repo_root(args.repo_root)
        context = GraphContext(root)
        if args.command == "dossier":
            dossier = context.dossier(args.node)
            content = (
                json.dumps(dossier, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
                if args.format == "json"
                else render_dossier_markdown(dossier)
            )
            _write_output(args.output, content)
        elif args.command == "init":
            path = init_campaign(context, _campaign_root(root, args.campaign_root))
            print(f"initialized {len(context.nodes)} pending nodes in {path}")
        elif args.command == "sync":
            campaign_root = _campaign_root(root, args.campaign_root)
            sync_campaign(context, campaign_root)
            print(json.dumps(campaign_status(context, campaign_root), indent=2))
        elif args.command == "validate":
            metadata = validate_report(args.report, context)
            print(
                f"valid report for node [{int(metadata['node'])}]: {metadata['verdict']}"
            )
        elif args.command == "record":
            entry = record_report(
                context, _campaign_root(root, args.campaign_root), args.report
            )
            print(
                f"recorded node [{int(args.report.stem.split('-')[-1])}]: "
                f"{entry['verdict']}"
            )
        elif args.command == "status":
            result = campaign_status(context, _campaign_root(root, args.campaign_root))
            if args.json:
                print(json.dumps(result, indent=2))
            else:
                counts = ", ".join(f"{key}={value}" for key, value in result["counts"].items())
                print(f"{result['proof']}: {result['node_count']} nodes; {counts}")
                for state, node_ids in result["nodes"].items():
                    print(f"{state}: {', '.join(node_ids) if node_ids else '-'}")
        return 0
    except AuditError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

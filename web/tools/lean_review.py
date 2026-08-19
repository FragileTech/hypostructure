"""Per-node Lean verification status for the Erdos-Gyarfas proof.

Two inputs, both produced by reading or running the code -- never by
reading prose:

*Which declarations are proved* comes from :mod:`lean_axiom_audit`, which
builds the package with tracer stubs standing in for the unfinished
frontier producers and runs ``#print axioms`` on every declaration.  A
declaration is clean when the tracer does not appear in its axiom list.

*Which nodes a declaration covers* comes from ``-- EG-NODE [n] label``
annotations carried in Assembly.lean directly above each declaration.
Those annotations record what the declaration's rows and produced fact
keys actually establish, cross-referenced against the manuscript's node
labels.  Prose doc comments are not parsed: they cite invariant numbers
and neighbouring residuals in the same ``[n]`` syntax, so they cannot
distinguish coverage from reference.

A node is *verified* when it is covered and every covering declaration is
clean; *partial* when covered but some covering declaration is tainted;
*absent* when no declaration covers it.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ASSEMBLY_REL = Path(
    "proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly.lean"
)
AUDIT_REL = Path("web/data/eg_axiom_audit.json")

NODE_COUNT = 180

#: ``-- EG-NODE [12] context-universality for target-complete identifications``
_ANNOTATION_RE = re.compile(r"^\s*--\s*EG-NODE\s*\[(\d{1,3})\]\s*(.*)$")

_DECL_RE = re.compile(
    r"^(?:noncomputable\s+)?(?:private\s+)?(?:def|theorem|lemma|abbrev)\s+"
    r"([A-Za-z0-9_']+)",
)


def load_audit(repo_root: Path) -> tuple[frozenset[str], frozenset[str]] | None:
    """The clean and tainted declaration sets from the kernel audit."""
    path = repo_root / AUDIT_REL
    if not path.exists():
        return None
    report = json.loads(path.read_text(encoding="utf-8"))
    return frozenset(report["clean"]), frozenset(report["tainted"])


def parse_annotations(path: Path) -> dict[str, dict[int, str]]:
    """``{decl: {node_id: manuscript label}}`` from ``EG-NODE`` annotations.

    An annotation block sits immediately above the declaration it
    describes, separated from it only by the doc comment (if any).
    """
    lines = path.read_text(encoding="utf-8").splitlines()

    result: dict[str, dict[int, str]] = {}
    pending: dict[int, str] = {}
    for line in lines:
        annotation = _ANNOTATION_RE.match(line)
        if annotation:
            node = int(annotation.group(1))
            if 1 <= node <= NODE_COUNT:
                pending[node] = annotation.group(2).strip()
            continue
        declaration = _DECL_RE.match(line)
        if declaration:
            if pending:
                result.setdefault(declaration.group(1), {}).update(pending)
            pending = {}
    return result


def build_review(repo_root: Path) -> dict | None:
    """The ``review`` side-car: one lean/kernel state per manuscript node."""
    assembly = repo_root / ASSEMBLY_REL
    audit = load_audit(repo_root)
    if not assembly.exists() or audit is None:
        return None
    clean, tainted = audit

    covers = parse_annotations(assembly)

    #: node -> declarations that establish it
    by_node: dict[int, set[str]] = {}
    for decl, nodes in covers.items():
        for node in nodes:
            by_node.setdefault(node, set()).add(decl)

    nodes: dict[str, dict[str, str]] = {}
    for node in range(1, NODE_COUNT + 1):
        citing = by_node.get(node, set())
        known = citing & (clean | tainted)
        if not known:
            state = "absent"
        elif known <= clean:
            state = "verified"
        else:
            state = "partial"
        nodes[str(node)] = {"lean": state, "kernel": state}

    return {"nodes": nodes}

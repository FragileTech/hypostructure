"""Per-node review status for the Erdos-Gyarfas proof.

Read from ``web/data/eg_node_audit.json``, the exhaustive 180-node audit.
Nothing here parses ``-- EG-NODE`` comments or infers coverage from prose:
those annotations are unreliable in both directions (declarations that
implement a node carry none, and one umbrella claims 44 nodes it merely
runs), so the audit resolves node -> producer through the manuscript's own
dependency table and the fact vocabulary instead.

Two independent questions are kept apart, because passing one never implies
the other:

*Does the node's own producer reach a referenced-but-undefined declaration?*
That is ``complete``, and it is judged per producer.  A large declaration
runs many branch arms; one unfinished sibling arm says nothing about whether
this node's row is finished.

*Does the producer publish the manuscript's statement?*  That is ``fidelity``
(Gate B).  Because ``FactSystem`` values are data-free, all mathematical
content lives in the ``Holds`` proposition, so a row stating something weaker
than its manuscript label still composes and still closes.  A kernel check
cannot see the difference.

A trivial proof is only a defect when the manuscript proves real content at
that node.  ``FAITHFUL-TRIVIAL`` marks the steps whose paper proof is itself
immediate -- those read as verified.  ``SURROGATE-TRIVIAL`` marks the ones
whose triviality is manufactured by a weakened statement.
"""

from __future__ import annotations

import json
from pathlib import Path

AUDIT_REL = Path("web/data/eg_node_audit.json")

NODE_COUNT = 180

#: Gate B verdicts that mean the producer publishes the manuscript's statement.
_FAITHFUL = {"FAITHFUL", "FAITHFUL-TRIVIAL", "STRONGER"}
#: Verdicts that mean it publishes something, but not the manuscript's claim.
_PARTIAL = {"WEAKER", "DIVERGENT", "SURROGATE-TRIVIAL", "PLUMBING", "VACUOUS"}


def load_audit(repo_root: Path) -> dict | None:
    path = repo_root / AUDIT_REL
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _state(ok: bool, partial: bool = False) -> str:
    return "verified" if ok else ("partial" if partial else "absent")


def build_review(repo_root: Path) -> dict | None:
    """The ``review`` side-car: one row of dimensions per manuscript node."""
    audit = load_audit(repo_root)
    if audit is None:
        return None
    entries = audit["nodes"]

    nodes: dict[str, dict[str, str]] = {}
    for number in range(1, NODE_COUNT + 1):
        entry = entries.get(str(number))
        if entry is None:
            continue
        fidelity = entry["fidelity"]
        complete = entry["complete"]
        local = entry["local"]
        api = entry["api"]

        row: dict[str, str] = {
            # A producer exists at all.
            "lean": _state(fidelity != "ABSENT"),
            # This node's own producer is finished.
            "kernel": _state(complete.startswith("YES"), partial=complete.startswith("YES ")),
            # The arm through this node was probed stub-free end to end.
            # This is a measurement, not a property: an arm can pass through a
            # declaration that is tainted by its *other* arms, so declaration
            # cleanliness cannot decide it -- only a composed probe can. Nodes
            # marked partial have a finished producer on an unprobed arm; that
            # is unmeasured, not failing.
            # A node that establishes no proposition cannot claim membership
            # of the arm that runs past it: [11] and [51] sit on probed arms
            # and contribute nothing to them, so the arm is closed despite
            # them rather than through them.
            "wired": _state(
                entry["on_probed_closed_arm"] and fidelity != "ABSENT",
                partial=complete.startswith("YES"),
            ),
            # The proposition is about the literal active residual.
            "local": _state(
                local.startswith("YES"),
                partial=local.startswith(("PARTIAL", "MIXED", "⚠")),
            ),
            # Only the canonical ExactLedger path is used.
            "fidelity": _state(fidelity in _FAITHFUL, partial=fidelity in _PARTIAL),
            "note": f"{fidelity} — {entry['fidelity_note']}",
        }
        if not api.startswith(("OK", "N/A")):
            row["note"] += f" | API: {api}"
        nodes[str(number)] = row

    return {"nodes": nodes}

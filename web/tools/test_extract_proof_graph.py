"""Structural assertions on every extracted proof.

Run with ``python -m pytest web/tools`` or ``python web/tools/test_extract_proof_graph.py``.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import pytest  # noqa: E402

from papers import SPECS  # noqa: E402
from papers import navier_stokes  # noqa: E402
from proof_graph import build_document  # noqa: E402
from extract_page_map import build_page_map  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]

DOCUMENTS = {slug: build_document(spec, REPO_ROOT) for slug, spec in SPECS.items()}

from lean_review import build_review  # noqa: E402

_review = build_review(REPO_ROOT)
if _review:
    DOCUMENTS["erdos-gyarfas"]["review"] = _review

ERDOS = DOCUMENTS["erdos-gyarfas"]
NAVIER_STOKES = DOCUMENTS["navier-stokes"]

every = pytest.mark.parametrize("document", DOCUMENTS.values(), ids=list(DOCUMENTS))

# One page map per manuscript, keyed by the chapter id its records carry.
PAGE_MAPS = {
    chapter.id: build_page_map(chapter, REPO_ROOT)
    for spec in SPECS.values()
    for chapter in spec.chapters
}


# --------------------------------------------------------------- every proof --


@every
def test_nodes_are_unique_and_belong_to_a_panel(document) -> None:
    ids = [node["id"] for node in document["nodes"]]
    assert len(ids) == len(set(ids))
    panels = {group["id"] for group in document["groups"]}
    for node in document["nodes"]:
        assert node["group"] in panels, node["id"]
        assert node["shape"] in {"assertion", "decision", "terminal"}
        # Only a terminal can be left open, and the flag is only written when set.
        if "open" in node:
            assert node["open"] is True and node["shape"] == "terminal", node["id"]


@every
def test_node_numbers_run_without_gaps_in_each_chapter(document) -> None:
    by_chapter: dict[str, list[int]] = {}
    for node in document["nodes"]:
        by_chapter.setdefault(node.get("chapter", ""), []).append(int(node["number"]))
    for chapter, numbers in by_chapter.items():
        numbers.sort()
        assert numbers == list(range(numbers[0], numbers[-1] + 1)), chapter


@every
def test_every_edge_resolves(document) -> None:
    ids = {node["id"] for node in document["nodes"]}
    seen: set[str] = set()
    for edge in document["edges"]:
        assert edge["source"] in ids, edge
        assert edge["target"] in ids, edge
        assert edge["source"] != edge["target"], edge
        assert edge["kind"] in {"flow", "continuation"}
        assert edge["id"] not in seen, edge["id"]
        seen.add(edge["id"])


@every
def test_the_whole_argument_is_one_graph(document) -> None:
    neighbours: dict[str, set[str]] = {}
    for edge in document["edges"]:
        neighbours.setdefault(edge["source"], set()).add(edge["target"])
        neighbours.setdefault(edge["target"], set()).add(edge["source"])

    root = document["nodes"][0]["id"]
    seen = {root}
    queue = [root]
    while queue:
        for adjacent in neighbours.get(queue.pop(), set()):
            if adjacent not in seen:
                seen.add(adjacent)
                queue.append(adjacent)

    assert seen == {node["id"] for node in document["nodes"]}


@every
def test_every_node_explains_itself(document) -> None:
    for node in document["nodes"]:
        assert node["label"].strip(), node["id"]
        assert node["overview"].strip(), node["id"]


@every
def test_a_node_only_claims_the_results_that_are_its_own(document) -> None:
    """A node cites a handful of results, not everything its block uses."""
    counts = [len(node["itemRefs"]) for node in document["nodes"]]
    assert max(counts) <= 30
    assert sum(counts) / len(counts) < 6


@every
def test_every_reference_resolves(document) -> None:
    keys = {item["key"] for item in document["items"]}
    for node in document["nodes"]:
        for reference in node["itemRefs"]:
            assert reference in keys, reference
        for block in node["blocks"]:
            for reference in block["itemRefs"]:
                assert reference in keys, reference
        if "dossier" in node:
            for reference in node["dossier"]["closingItems"]:
                assert reference in keys, reference
    for item in document["items"]:
        for reference in item.get("requiresItems", []):
            assert reference in keys, reference


@every
def test_results_carry_statements(document) -> None:
    for item in document["items"]:
        assert item["statementLatex"].strip(), item["key"]
        assert item["kind"] in {
            "theorem",
            "proposition",
            "lemma",
            "corollary",
            "definition",
            "remark",
        }
    with_proof = [item for item in document["items"] if item.get("proofLatex")]
    assert len(with_proof) > len(document["items"]) // 4


@every
def test_constraints_are_distinguishable(document) -> None:
    """Each manuscript numbers its own constraints from one, so ids must differ."""
    ids = [invariant["id"] for invariant in document["invariants"]]
    assert len(ids) == len(set(ids))
    known = set(ids)
    for node in document["nodes"]:
        for reference in node["invariantRefs"]:
            assert reference in known, reference


@every
def test_no_table_heading_is_read_as_data(document) -> None:
    """Some papers set their headings in plain text, so they look like rows."""
    headings = {
        "fact",
        "invariant",
        "node",
        "state or exit",
        "state or test",
        "constant",
        "symbol",
        "result",
        "part",
    }
    for invariant in document["invariants"]:
        assert invariant["name"].strip().lower() not in headings, invariant
        assert invariant["constraint"].strip(), invariant["id"]
    for constant in document["constants"]:
        assert constant["symbol"].strip().lower() not in headings, constant


@every
def test_a_step_is_not_described_twice_over(document) -> None:
    """The name chip and the summary must not repeat one another."""
    for node in document["nodes"]:
        assert node["topics"] != [node["overview"]], node["id"]


@every
def test_the_papers_own_tables_are_published(document) -> None:
    tables = document["tables"]
    assert tables
    assert len({table["id"] for table in tables}) == len(tables)

    for table in tables:
        assert table["title"].strip(), table["id"]
        assert table["headers"], table["id"]
        assert table["rows"], table["id"]
        width = len(table["headers"])
        assert width >= 2, table["id"]
        for row in table["rows"]:
            assert len(row) == width, (table["id"], row)
        # A heading read as data would put a column name in the first cell.
        assert table["rows"][0][:2] != table["headers"][:2], table["id"]


@every
def test_every_step_a_table_names_exists(document) -> None:
    """Bracketed integers are the papers' node numbers, and the site links them."""
    prefixes = {chapter["id"]: chapter["prefix"] for chapter in document.get("chapters", [])}
    ids = {node["id"] for node in document["nodes"]}
    seen = 0

    for table in document["tables"]:
        prefix = prefixes.get(table.get("chapter"), "")
        for row in table["rows"]:
            for cell in row:
                for match in re.finditer(r"\[(\d+)\]", cell):
                    seen += 1
                    assert f"{prefix}{match.group(1)}" in ids, (table["id"], match.group(0))

    assert seen > 100


@every
def test_panels_are_named_and_described(document) -> None:
    for group in document["groups"]:
        assert group["title"].strip(), group["id"]
        assert group["caption"].strip(), group["id"]


@every
def test_every_panel_says_what_its_part_of_the_proof_does(document) -> None:
    for group in document["groups"]:
        summary = group["summary"].strip()
        assert summary, group["id"]
        # A summary that merely restates the title says nothing.
        assert summary != group["title"].strip(), group["id"]
        assert not summary.startswith(group["title"].strip()), group["id"]
        assert len(summary.split()) >= 8, group["id"]


@every
def test_nothing_shown_opens_on_the_drawing_legend(document) -> None:
    """`Proof-dependency diagram, Part I. Rectangles are…` describes the picture."""
    for group in document["groups"]:
        for field in ("summary", "caption"):
            text = group[field].lstrip()
            assert not text.startswith("Proof-dependency diagram"), (group["id"], field)
            assert not text.startswith("Proof flow"), (group["id"], field)
            assert not text.startswith("Rectangles"), (group["id"], field)


# ------------------------------------------------------- the Erdos-Gyarfas --


def test_erdos_publishes_its_sixteen_chapter_one_tables() -> None:
    titles = [table["title"] for table in ERDOS["tables"]]
    assert len(titles) == 16
    assert titles[0] == "Detailed dependency table"
    ledger = [table for table in ERDOS["tables"] if table["group"] == "The constraint ledger"]
    assert len(ledger) == 8
    per_result = [
        table
        for table in ERDOS["tables"]
        if table["group"] == "Per-lemma invariant requirements"
    ]
    assert len(per_result) == 7


def test_navier_stokes_publishes_four_tables_per_paper() -> None:
    counts: dict[str, int] = {}
    for table in NAVIER_STOKES["tables"]:
        counts[table["chapter"]] = counts.get(table["chapter"], 0) + 1
    assert counts == {"setup": 4, "type-i": 4, "type-ii": 4}
    audit = next(
        table
        for table in NAVIER_STOKES["tables"]
        if table["chapter"] == "type-i" and table["title"] == "Node-by-node audit table"
    )
    assert len(audit["rows"]) == 159
    assert audit["headers"][0] == "Node"


def test_erdos_review_sidecar_covers_all_nodes() -> None:
    review = ERDOS["review"]
    assert len(review["nodes"]) == 180
    valid = {"verified", "partial", "absent"}
    for nid, entry in review["nodes"].items():
        assert entry["lean"] in valid, f"node {nid}: lean={entry['lean']}"
        assert entry["kernel"] in valid, f"node {nid}: kernel={entry['kernel']}"


def test_review_states_come_from_the_node_audit() -> None:
    """Every dimension is read from the 180-node audit, never inferred."""
    from lean_review import load_audit

    audit = load_audit(REPO_ROOT)["nodes"]
    states = ERDOS["review"]["nodes"]

    for node in range(1, 181):
        entry = audit[str(node)]
        row = states[str(node)]
        # A producer exists iff the audit found one.
        assert row["lean"] == ("absent" if entry["fidelity"] == "ABSENT" else "verified"), node
        # Completeness is judged per producer, never per enclosing declaration.
        assert row["kernel"] == (
            "verified" if entry["complete"].startswith("YES") else "absent"
        ), node
        # The fidelity verdict carries into the note, so a reader sees why.
        assert row["note"].startswith(entry["fidelity"]), node


def test_a_node_that_states_nothing_claims_no_arm() -> None:
    """An arm running past an empty node is closed despite it, not through it."""
    from lean_review import load_audit

    audit = load_audit(REPO_ROOT)["nodes"]
    states = ERDOS["review"]["nodes"]
    for node, entry in audit.items():
        if entry["fidelity"] == "ABSENT":
            assert states[node]["wired"] != "verified", node


def test_every_absent_node_says_what_blocks_it() -> None:
    """ABSENT is a verdict about the tree, so it must name what stands in the way.

    It distinguishes a step whose only route runs through a referenced-but-undefined
    declaration from a paper-side remark that nothing downstream consumes -- [87] is
    the latter and must not read as a hole in the argument.
    """
    from lean_review import load_audit

    audit = load_audit(REPO_ROOT)["nodes"]
    states = ERDOS["review"]["nodes"]
    for node, entry in audit.items():
        if entry["fidelity"] == "ABSENT":
            assert entry.get("blocked_by"), node
            assert "Blocked by:" in states[node]["note"], node
    assert audit["87"]["blocked_by"].startswith("nothing")


def test_faithful_triviality_is_not_reported_as_a_defect() -> None:
    """A trivial proof is faithful when the paper's own step is immediate.

    These nodes were each checked against the manuscript's proof of the step:
    the paper proves nothing more, so the Lean triviality is inherited rather
    than manufactured and must read as verified.
    """
    from lean_review import load_audit

    audit = load_audit(REPO_ROOT)["nodes"]
    states = ERDOS["review"]["nodes"]
    for node in (12, 18, 23, 31, 36, 37, 52, 88, 104, 114, 126, 138, 154, 155):
        assert audit[str(node)]["fidelity"] == "FAITHFUL-TRIVIAL", node
        assert states[str(node)]["fidelity"] == "verified", node


def test_surrogate_triviality_is_reported_as_a_defect() -> None:
    """Triviality manufactured by a weakened statement is not verified."""
    from lean_review import load_audit

    audit = load_audit(REPO_ROOT)["nodes"]
    states = ERDOS["review"]["nodes"]
    for node in (76, 85, 103, 113, 129, 134):
        assert audit[str(node)]["fidelity"] == "SURROGATE-TRIVIAL", node
        assert states[str(node)]["fidelity"] == "partial", node


def test_axiom_audit_is_a_kernel_result_not_a_transcript() -> None:
    """The report must name the tracer and account for every declaration."""
    report = json.loads((REPO_ROOT / "web/data/eg_axiom_audit.json").read_text())
    assert report["tracer"] == "frontierGap"
    assert not report["unreported"], report["unreported"]
    assert len(report["clean"]) + len(report["tainted"]) == report["declarations"]
    # The public theorem still depends on the unfinished producers.
    assert "erdos_64" in report["tainted"]
    # Every frontier stub is an identifier Assembly.lean references but nothing defines.
    assert report["frontier_stubs"]
    assert not set(report["frontier_stubs"]) & set(report["clean"])


def test_node_coverage_is_not_derived_from_comments() -> None:
    """`-- EG-NODE` comments are not a trustworthy node<->declaration mapping.

    They are unreliable in both directions: declarations that implement a node
    carry none, and one umbrella claims 44 nodes it merely runs. The audit
    resolves node -> producer through the manuscript's own dependency table and
    the fact vocabulary instead, so nothing in the review pipeline may parse
    them.
    """
    source = (REPO_ROOT / "web/tools/lean_review.py").read_text(encoding="utf-8")
    assert "EG-NODE" not in source.replace("``-- EG-NODE``", "").replace(
        "-- EG-NODE", "", 1
    ) or "parse_annotations" not in source
    assert "parse_annotations" not in source


def test_every_node_records_a_producer_or_says_it_has_none() -> None:
    """No node is left without an answer, and 'absent' is stated, not implied."""
    from lean_review import load_audit

    audit = load_audit(REPO_ROOT)["nodes"]
    assert len(audit) == 180
    for node in range(1, 181):
        entry = audit[str(node)]
        assert entry["fidelity"], node
        assert entry["complete"], node
        if entry["fidelity"] == "ABSENT":
            # ABSENT means no proposition is established. A branch cursor may
            # still exist -- node [51] carries the high-entropy arm but states
            # no lemma -- so the absence is recorded in the note, not inferred
            # from the producer field being empty.
            assert entry["fidelity_note"], node


def test_erdos_has_all_180_steps_across_twelve_panels() -> None:
    assert len(ERDOS["nodes"]) == 180
    assert len(ERDOS["groups"]) == 12
    assert "chapters" not in ERDOS
    shapes = [node["shape"] for node in ERDOS["nodes"]]
    assert shapes.count("assertion") == 102
    assert shapes.count("decision") == 45
    assert shapes.count("terminal") == 33
    # The paper's red-ellipse style is declared but no node is drawn with it.
    assert not [node["id"] for node in ERDOS["nodes"] if node.get("open")]


def test_erdos_dense_packing_residual_is_part_xii() -> None:
    """The realization test [158] sits in Part I; its no-edge opens Part XII."""
    by_id = {node["id"]: node for node in ERDOS["nodes"]}
    assert by_id["158"]["group"] == "fig:proof-diagram-part-i"
    assert by_id["158"]["shape"] == "decision"
    for number in range(159, 173):
        assert by_id[str(number)]["group"] == "fig:proof-diagram-part-xii", number
    for number in ("160", "163", "170"):
        assert by_id[number]["shape"] == "decision", number
    for number in ("164", "168", "171", "172"):
        assert by_id[number]["shape"] == "terminal", number

    arrows = {(edge["source"], edge["target"]): edge for edge in ERDOS["edges"]}
    assert arrows[("21", "158")]["kind"] == "flow"
    assert arrows[("158", "22")]["branch"] == "yes"
    assert arrows[("158", "159")]["kind"] == "continuation"
    assert arrows[("158", "159")]["branch"].startswith("no")
    assert arrows[("159", "160")]["kind"] == "flow"
    assert arrows[("160", "161")]["branch"] == "yes"
    assert arrows[("160", "162")]["branch"] == "no"
    assert ("162", "163") in arrows and ("162", "164") in arrows
    assert arrows[("161", "25")]["kind"] == "continuation"
    # The neutral configuration [163]: replacement route and two-strand route.
    assert arrows[("163", "165")]["branch"] == "no"
    assert arrows[("163", "167")]["branch"] == "yes"
    assert arrows[("165", "166")]["kind"] == "flow"
    assert arrows[("166", "169")]["kind"] == "flow"
    assert arrows[("169", "170")]["kind"] == "flow"
    assert arrows[("170", "171")]["branch"] == "yes"
    assert arrows[("170", "172")]["branch"] == "no"
    assert arrows[("167", "168")]["branch"] == "survives"
    # Part XII redraws the power-of-two cycle [155] of Part XI; it is one node.
    assert arrows[("167", "155")]["branch"] == "closed"
    assert by_id["155"]["group"] == "fig:proof-diagram-part-xi"
    assert sum(1 for node in ERDOS["nodes"] if node["id"] == "155") == 1

    # Each new step carries the result the dependency table attributes to it.
    assert by_id["158"]["itemRefs"] == ["def:window-realization-test"]
    assert by_id["160"]["itemRefs"] == ["lem:dense-deficiency-routing"]
    assert by_id["162"]["itemRefs"] == ["lem:dense-cold-pass"]
    assert by_id["163"]["itemRefs"] == ["def:neutral-equal-length-germ"]
    assert by_id["164"]["itemRefs"] == ["def:all-cold-comparison"]
    assert by_id["165"]["itemRefs"] == ["lem:refined-minimality-swap"]
    assert by_id["167"]["itemRefs"] == ["lem:two-strand-check"]
    assert by_id["168"]["itemRefs"] == ["lem:symmetric-pair-endpoint"]
    assert "def:blocked-class" in by_id["169"]["itemRefs"]
    assert "def:barrier-overlap-system" in by_id["170"]["itemRefs"]
    items = {item["key"]: item for item in ERDOS["items"]}
    assert items["lem:dense-cold-pass"]["proofLatex"]
    assert items["rem:dense-residual-status"]["kind"] == "remark"
    for key in (
        "lem:scale-additivity",
        "lem:blocked-graphs-compress",
        "lem:system-increment-arithmetic",
        "lem:barrier-failure-overlap",
        "lem:window-system-realizability",
        "lem:serial-system-sumset",
        "lem:remainder-glue-injection",
        "lem:neutral-germ-symmetry",
    ):
        assert items[key]["kind"] == "lemma" and items[key]["proofLatex"], key
    assert items["def:serial-window-system"]["kind"] == "definition"


def test_erdos_exact_collision_test_sits_in_part_v() -> None:
    """[173]--[177] expand the no-edge of the exact collision test in place."""
    by_id = {node["id"]: node for node in ERDOS["nodes"]}
    for number in range(173, 178):
        assert by_id[str(number)]["group"] == "fig:proof-diagram-part-v", number
    assert by_id["173"]["shape"] == by_id["175"]["shape"] == "decision"
    assert by_id["176"]["shape"] == "terminal"

    arrows = {(edge["source"], edge["target"]): edge for edge in ERDOS["edges"]}
    assert arrows[("57", "173")]["kind"] == "flow"
    assert arrows[("173", "58")]["branch"] == "yes"
    assert arrows[("173", "174")]["branch"] == "no"
    assert arrows[("174", "175")]["kind"] == "flow"
    assert arrows[("175", "176")]["branch"] == "no"
    assert arrows[("175", "177")]["branch"] == "yes"
    assert arrows[("177", "65")]["kind"] == "continuation"
    assert ("57", "58") not in arrows

    assert by_id["173"]["itemRefs"] == ["lem:exact-collision-test"]
    assert by_id["175"]["itemRefs"] == ["lem:absorbed-germ-fan-data"]


def test_erdos_pair_code_residual_sits_in_part_x() -> None:
    """The entropy counts of [131] and [137] are branch tests; failure opens [178]."""
    by_id = {node["id"]: node for node in ERDOS["nodes"]}
    for number in ("178", "179", "180"):
        assert by_id[number]["group"] == "fig:proof-diagram-part-x", number
    assert by_id["180"]["shape"] == "terminal"

    arrows = {(edge["source"], edge["target"]): edge for edge in ERDOS["edges"]}
    assert arrows[("131", "178")]["kind"] == "flow"
    assert arrows[("131", "178")]["branch"] == "count fails"
    assert arrows[("137", "178")]["kind"] == "continuation"
    assert arrows[("137", "178")]["branch"].endswith("continue at [178]")
    assert arrows[("178", "179")]["kind"] == "flow"
    assert arrows[("179", "180")]["kind"] == "flow"

    assert by_id["178"]["itemRefs"] == ["def:pair-overlap-system"]
    assert by_id["179"]["itemRefs"] == ["lem:pair-system-realizability"]
    assert by_id["180"]["itemRefs"] == ["lem:pair-system-increment-arithmetic"]
    items = {item["key"]: item for item in ERDOS["items"]}
    for key in ("lem:pair-failure-overlap", "lem:pair-count-or-arithmetic"):
        assert items[key]["kind"] == "lemma" and items[key]["proofLatex"], key


def test_erdos_ledger_and_constants() -> None:
    assert [row["number"] for row in ERDOS["invariants"]] == list(range(1, 39))
    assert len(ERDOS["constants"]) == 10
    assert "$c_\\Omega$" in {constant["symbol"] for constant in ERDOS["constants"]}
    for name in ("\\Mers", "\\defp", "\\No"):
        assert name in ERDOS["macros"]


def test_erdos_external_theorem_reads_correctly() -> None:
    external = next(item for item in ERDOS["items"] if item["key"] == "thm:p13free")
    assert "power of two" in external["statementLatex"]
    node = next(node for node in ERDOS["nodes"] if node["id"] == "15")
    assert node["itemRefs"] == ["cor:p13-exists"]
    assert any("thm:p13free" in block["itemRefs"] for block in node["blocks"])


def test_erdos_remainder_core_node_has_its_own_lemma() -> None:
    key = "lem:remainder-empty-internal-3-core"
    lemma = next(item for item in ERDOS["items"] if item["key"] == key)
    assert "Every component of \\(R\\)" in lemma["statementLatex"]
    assert "empty internal \\(3\\)-core" in lemma["statementLatex"]
    node = next(node for node in ERDOS["nodes"] if node["id"] == "27")
    assert key in node["itemRefs"]


_REQUIRED_INVARIANTS = re.compile(r"\binv(?:ariants?)?\.?\s+([\d,\s\u2013-]+)", re.I)


def required_invariants(requires: str) -> set[int]:
    """The ledger numbers a Requires cell names, e.g. ``inv 4, 8, 25`` or ``20--24``."""
    numbers: set[int] = set()
    for match in _REQUIRED_INVARIANTS.finditer(requires or ""):
        for part in match.group(1).split(","):
            part = part.strip()
            span = re.fullmatch(r"(\d+)\s*[\u2013-]+\s*(\d+)", part)
            if span:
                numbers.update(range(int(span.group(1)), int(span.group(2)) + 1))
            elif part.isdigit():
                numbers.add(int(part))
    return numbers


def test_erdos_requires_only_constraints_tracked_upstream() -> None:
    """The paper's own rule for its requirement rows, checked along the diagram.

    Every ``inv N`` a result's Requires cell names must be a ledger row, and must
    be tracked at the step the result is attached to or at some step upstream of
    it — never only on a sibling branch. A referee reading a step then sees each
    declared input already on the table.
    """
    invariants = {row["number"]: row for row in ERDOS["invariants"]}
    tracked_at: dict[str, set[int]] = {node["id"]: set() for node in ERDOS["nodes"]}
    for row in ERDOS["invariants"]:
        for node_id in row["nodes"]:
            tracked_at[node_id].add(row["number"])

    incoming: dict[str, list[str]] = {}
    for edge in ERDOS["edges"]:
        incoming.setdefault(edge["target"], []).append(edge["source"])

    def available(node_id: str) -> set[int]:
        seen = {node_id}
        queue = [node_id]
        while queue:
            for source in incoming.get(queue.pop(), []):
                if source not in seen:
                    seen.add(source)
                    queue.append(source)
        return set().union(*(tracked_at[step] for step in seen))

    items = {item["key"]: item for item in ERDOS["items"]}
    dangling: list[str] = []
    early: list[str] = []
    for node in ERDOS["nodes"]:
        on_hand = available(node["id"])
        for key in node["itemRefs"]:
            for number in required_invariants(items[key].get("requires", "")):
                if number not in invariants:
                    dangling.append(f"{key} cites inv {number}")
                elif number not in on_hand:
                    early.append(f"[{node['id']}] {key} requires inv {number}, tracked at {invariants[number]['nodes']}")
    assert sorted(set(dangling)) == []
    assert early == []


# --------------------------------------------------------- the Navier-Stokes --


def test_navier_stokes_spans_three_chapters() -> None:
    chapters = {chapter["id"]: chapter for chapter in NAVIER_STOKES["chapters"]}
    assert list(chapters) == ["setup", "type-i", "type-ii"]
    assert len(NAVIER_STOKES["nodes"]) == 333

    sizes = {chapter: 0 for chapter in chapters}
    for node in NAVIER_STOKES["nodes"]:
        sizes[node["chapter"]] += 1
    assert sizes == {"setup": 39, "type-i": 159, "type-ii": 135}


def test_navier_stokes_ids_carry_their_chapter() -> None:
    by_id = {node["id"]: node for node in NAVIER_STOKES["nodes"]}
    assert by_id["S12"]["number"] == "12"
    assert by_id["I12"]["number"] == "12"
    assert by_id["II12"]["number"] == "12"
    assert by_id["S12"]["chapter"] == "setup"


def test_navier_stokes_summaries_come_from_the_manuscripts() -> None:
    """All 23 panels are described by their paper's own diagram map."""
    authored = {
        summary
        for chapter in navier_stokes.SPEC.chapters
        for summary in chapter.part_summaries.values()
    }
    assert not authored, "the Navier-Stokes summaries are tabulated, not authored"
    assert len(NAVIER_STOKES["groups"]) == 23
    for group in NAVIER_STOKES["groups"]:
        assert group["summary"].strip()


# ---------------------------------------------------------------- page maps --


def _raw_key(key: str) -> str:
    """The label as written in the paper: multi-chapter proofs prefix it."""
    return key.split("/", 1)[1] if "/" in key else key


@every
def test_every_stated_result_has_a_page_in_its_pdf(document) -> None:
    for collection in ("items", "equations"):
        for record in document[collection]:
            page_map = PAGE_MAPS[record["chapter"]]
            entry = page_map["labels"].get(_raw_key(record["key"]))
            assert entry, record["key"]
            # The graph records the ``\\begin`` line; the label follows it, at
            # the end of the display in the case of a long equation.
            assert 0 <= entry["line"] - record["sourceLine"] <= 20, record["key"]
            assert entry["page"] and 1 <= entry["page"] <= page_map["pages"], record["key"]


@pytest.mark.parametrize("page_map", PAGE_MAPS.values(), ids=list(PAGE_MAPS))
def test_page_maps_are_complete_and_consistent(page_map) -> None:
    assert page_map["pdf"].endswith(".pdf") and page_map["pages"] > 0
    labels = page_map["labels"]
    assert labels
    # Every label of the source landed on a page of this build, and vice versa.
    assert all(entry["line"] and entry["page"] for entry in labels.values())
    # Numbered results are placed in reading order: a later line is never on
    # an earlier page, up to the slack a page break inside a statement allows.
    theorems = sorted(
        (entry["line"], entry["page"])
        for entry in labels.values()
        if (entry["anchor"] or "").startswith("theorem.")
    )
    for (_, before), (_, after) in zip(theorems, theorems[1:]):
        assert after >= before - 1


def test_the_page_maps_name_the_pdfs_the_site_serves() -> None:
    served = {path.name for path in (REPO_ROOT / "web" / "frontend" / "public" / "papers").glob("*.pdf")}
    assert {page_map["pdf"] for page_map in PAGE_MAPS.values()} <= served


def test_navier_stokes_papers_are_joined() -> None:
    pairs = {(edge["source"], edge["target"]) for edge in NAVIER_STOKES["edges"]}
    for source, target, _note in navier_stokes.CROSSINGS:
        assert (source, target) in pairs, (source, target)


def test_navier_stokes_keeps_each_papers_labels_apart() -> None:
    """The three manuscripts reuse bare label names, so keys are namespaced."""
    keys = {item["key"] for item in NAVIER_STOKES["items"]}
    assert all("/" in key for key in keys)
    prefixes = {key.split("/", 1)[0] for key in keys}
    # Every manuscript contributes results, and each keeps its own namespace.
    assert prefixes == {"setup", "type-i", "type-ii"}
    assert "type-ii/thm:canonical-local-caccioppoli" in keys
    assert "setup/p1:thm:final-assembly" in keys


def test_navier_stokes_entry_and_terminal_read_correctly() -> None:
    by_id = {node["id"]: node for node in NAVIER_STOKES["nodes"]}
    assert "finite-energy suitable solution" in by_id["S1"]["label"]
    assert by_id["S2"]["shape"] == "decision"
    assert by_id["S3"]["shape"] == "terminal"
    # A dashed re-drawing of a terminal is the same node, not a second one.
    assert sum(1 for node in NAVIER_STOKES["nodes"] if node["id"] == "II110") == 1


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))

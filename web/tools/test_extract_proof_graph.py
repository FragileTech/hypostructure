"""Structural assertions on every extracted proof.

Run with ``python -m pytest web/tools`` or ``python web/tools/test_extract_proof_graph.py``.
"""

from __future__ import annotations

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


def test_erdos_has_all_157_steps_across_eleven_panels() -> None:
    assert len(ERDOS["nodes"]) == 157
    assert len(ERDOS["groups"]) == 11
    assert "chapters" not in ERDOS
    shapes = [node["shape"] for node in ERDOS["nodes"]]
    assert shapes.count("assertion") == 92
    assert shapes.count("decision") == 38
    assert shapes.count("terminal") == 27


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

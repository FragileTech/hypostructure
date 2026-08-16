"""Structural assertions on every extracted proof.

Run with ``python -m pytest web/tools`` or ``python web/tools/test_extract_proof_graph.py``.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import pytest  # noqa: E402

from papers import SPECS  # noqa: E402
from papers import navier_stokes  # noqa: E402
from proof_graph import build_document  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]

DOCUMENTS = {slug: build_document(spec, REPO_ROOT) for slug, spec in SPECS.items()}
ERDOS = DOCUMENTS["erdos-gyarfas"]
NAVIER_STOKES = DOCUMENTS["navier-stokes"]

every = pytest.mark.parametrize("document", DOCUMENTS.values(), ids=list(DOCUMENTS))


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

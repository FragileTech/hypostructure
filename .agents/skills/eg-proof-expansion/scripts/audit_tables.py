#!/usr/bin/env python3
"""Validate the synchronized EG paper-fact and diagram-node audit tables."""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


AUDIT_REL = Path("Assembly_node_audit.md")
TEX_REL = Path("to_formalize/original_erdos_64_proof.tex")
FACT_HEADING = "## Paper-fact implementation table"
NODE_HEADING = "## Node-by-node table"
FACT_HEADER = (
    "Label", "Page", "Node", "Tactic", "Lean", "Partial match",
    "Kernel checks", "Local", "Reads ledger", "Writes ledger", "Wired",
    "Legal", "No hardcoded facts",
)
NODE_HEADER = (
    "Node", "Original diagram label", "Assembly implementation",
    "Lean tactic/combinator", "Applicable CT(s) / shared nodes",
    "Implemented / reachable?", "Correctly wired?", "Residual-local proof?",
    "Correct ledger registration?", "Custom illegal carrier?",
    "Difference from prescribed proof", "Independently kernel checked?",
    "Manuscript `\\label` object(s)",
)
FACT_ENVIRONMENTS = ("definition", "lemma", "proposition", "corollary", "theorem")
STATUS_PREFIXES = ("✅", "⚠", "❌", "N/A", "—")


class AuditError(Exception):
    pass


@dataclass(frozen=True)
class Table:
    header: tuple[str, ...]
    rows: tuple[tuple[str, ...], ...]


def split_markdown_row(line: str) -> tuple[str, ...]:
    text = line.strip()
    if not text.startswith("|") or not text.endswith("|"):
        raise AuditError(f"malformed Markdown table row: {line}")
    cells: list[str] = []
    current: list[str] = []
    escaped = False
    for char in text[1:-1]:
        if char == "|" and not escaped:
            cells.append("".join(current).strip())
            current = []
        else:
            current.append(char)
        if char == "\\" and not escaped:
            escaped = True
        else:
            escaped = False
    cells.append("".join(current).strip())
    return tuple(cells)


def section(text: str, heading: str, next_heading: str | None) -> str:
    if text.count(heading) != 1:
        raise AuditError(f"expected exactly one {heading!r} heading")
    body = text.split(heading, 1)[1]
    if next_heading is not None:
        if next_heading not in body:
            raise AuditError(f"missing heading {next_heading!r} after {heading!r}")
        body = body.split(next_heading, 1)[0]
    return body


def parse_table(body: str, expected: tuple[str, ...]) -> Table:
    lines = [line for line in body.splitlines() if line.lstrip().startswith("|")]
    for index, line in enumerate(lines):
        cells = split_markdown_row(line)
        if cells == expected:
            if index + 1 >= len(lines):
                raise AuditError(f"missing separator after table header {expected[0]!r}")
            separator = split_markdown_row(lines[index + 1])
            if len(separator) != len(expected) or not all(
                re.fullmatch(r":?-{3,}:?", cell) for cell in separator
            ):
                raise AuditError(f"invalid separator for table {expected[0]!r}")
            rows: list[tuple[str, ...]] = []
            for row_line in lines[index + 2 :]:
                row = split_markdown_row(row_line)
                if len(row) != len(expected):
                    raise AuditError(
                        f"{expected[0]} row has {len(row)} columns, expected "
                        f"{len(expected)}: {row_line}"
                    )
                rows.append(row)
            return Table(expected, tuple(rows))
    raise AuditError(f"missing table with header {expected!r}")


def manuscript_fact_labels(tex: str) -> list[str]:
    env = "|".join(FACT_ENVIRONMENTS)
    pattern = re.compile(
        rf"\\begin\{{(?:{env})\}}(?P<body>.*?)\\end\{{(?:{env})\}}",
        re.DOTALL,
    )
    label_pattern = re.compile(r"\\label(?:\[[^\]]+\])?\{([^}]+)\}")
    labels: list[str] = []
    for match in pattern.finditer(tex):
        found = label_pattern.findall(match.group("body"))
        if len(found) != 1:
            raise AuditError(
                "each labeled fact environment must contain exactly one label; "
                f"found {found!r}"
            )
        labels.append(found[0])
    return labels


def manuscript_all_labels(tex: str) -> set[str]:
    return set(re.findall(r"\\label(?:\[[^\]]+\])?\{([^}]+)\}", tex))


def node_numbers(cell: str) -> set[int]:
    result: set[int] = set()
    normalized = cell.replace("–", "-")
    for first, last in re.findall(r"\[(\d+)\](?:-\[(\d+)\])?", normalized):
        start = int(first)
        stop = int(last) if last else start
        if stop < start:
            raise AuditError(f"descending node range in {cell!r}")
        result.update(range(start, stop + 1))
    if not result:
        raise AuditError(f"fact row has no diagram node in {cell!r}")
    invalid = sorted(number for number in result if not 1 <= number <= 157)
    if invalid:
        raise AuditError(f"out-of-range diagram nodes {invalid} in {cell!r}")
    return result


def listed_labels(cell: str) -> set[str]:
    if cell.strip() == "—":
        return set()
    return set(re.findall(r"`([^`]+)`", cell))


def check_status_cells(facts: Table, nodes: Table) -> None:
    for row in facts.rows:
        for index in range(6, 13):
            if not row[index].startswith(STATUS_PREFIXES):
                raise AuditError(
                    f"fact {row[0]!r} has unclassified status in {facts.header[index]!r}: "
                    f"{row[index]!r}"
                )
    for row in nodes.rows:
        for index in (6, 7, 8, 11):
            value = row[index]
            if not value.startswith(STATUS_PREFIXES):
                raise AuditError(
                    f"node {row[0]} has unclassified status in {nodes.header[index]!r}: "
                    f"{value!r}"
                )


def validate(repo_root: Path) -> None:
    audit_path = repo_root / AUDIT_REL
    tex_path = repo_root / TEX_REL
    missing = [str(path) for path in (audit_path, tex_path) if not path.is_file()]
    if missing:
        raise AuditError("missing required file(s): " + ", ".join(missing))

    audit = audit_path.read_text(encoding="utf-8")
    tex = tex_path.read_text(encoding="utf-8")
    facts = parse_table(section(audit, FACT_HEADING, NODE_HEADING), FACT_HEADER)
    nodes = parse_table(section(audit, NODE_HEADING, None), NODE_HEADER)

    expected_labels = manuscript_fact_labels(tex)
    actual_labels = [row[0] for row in facts.rows]
    if actual_labels != expected_labels:
        missing_labels = [label for label in expected_labels if label not in actual_labels]
        extra_labels = [label for label in actual_labels if label not in expected_labels]
        raise AuditError(
            "paper-fact labels differ from manuscript order; "
            f"missing={missing_labels}, extra={extra_labels}"
        )
    if len(actual_labels) != len(set(actual_labels)):
        raise AuditError("paper-fact table contains duplicate labels")

    node_rows: dict[int, tuple[str, ...]] = {}
    for row in nodes.rows:
        match = re.fullmatch(r"\[(\d+)\]", row[0])
        if match is None:
            raise AuditError(f"invalid node identifier {row[0]!r}")
        number = int(match.group(1))
        if number in node_rows:
            raise AuditError(f"duplicate node row [{number}]")
        node_rows[number] = row
    max_node = max(int(number) for number in re.findall(r"\\textbf\{\[(\d+)\]\}", tex))
    expected_nodes = set(range(1, max_node + 1))
    if set(node_rows) != expected_nodes:
        raise AuditError(
            f"node table must contain exactly [1]-[{max_node}]; "
            f"missing={sorted(expected_nodes - set(node_rows))}, "
            f"extra={sorted(set(node_rows) - expected_nodes)}"
        )

    fact_nodes = {row[0]: node_numbers(row[2]) for row in facts.rows}
    all_tex_labels = manuscript_all_labels(tex)
    for number, row in node_rows.items():
        for label in listed_labels(row[12]):
            if label not in all_tex_labels:
                raise AuditError(f"node [{number}] names unknown manuscript label {label!r}")
            if label in fact_nodes and number not in fact_nodes[label]:
                raise AuditError(
                    f"node [{number}] lists {label!r}, but its fact row maps to "
                    f"{sorted(fact_nodes[label])}"
                )
    for label, numbers in fact_nodes.items():
        for number in numbers:
            if label not in listed_labels(node_rows[number][12]):
                raise AuditError(
                    f"fact {label!r} maps to node [{number}], but that node row "
                    "does not list the label"
                )

    check_status_cells(facts, nodes)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("check",))
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    try:
        validate(args.repo_root.resolve())
    except AuditError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1) from error
    print("Assembly audit tables are structurally synchronized.")


if __name__ == "__main__":
    main()

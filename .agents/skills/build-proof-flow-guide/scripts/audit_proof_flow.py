#!/usr/bin/env python3
"""Check structural invariants of a LaTeX proof-flow guide."""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import sys


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tex", type=Path)
    parser.add_argument("--first", type=int)
    parser.add_argument("--last", type=int)
    parser.add_argument("--box-style", default="box")
    parser.add_argument("--decision-style", default="dec")
    parser.add_argument("--terminal-style", default="term")
    parser.add_argument("--route-style", default="route")
    parser.add_argument(
        "--diagram-marker", default=r"\subsection{Proof-dependency diagram}"
    )
    parser.add_argument(
        "--table-marker", default=r"\subsection{Node-by-node audit table}"
    )
    return parser.parse_args()


def option_tokens(options: str) -> set[str]:
    return {part.strip().split("=", 1)[0] for part in options.split(",")}


def main() -> int:
    args = parse_args()
    text = args.tex.read_text(encoding="utf-8")
    start = text.find(args.diagram_marker)
    end = text.find(args.table_marker, start + 1)
    if start < 0 or end < 0:
        print("ERROR: could not locate the diagram and audit-table markers")
        return 2

    diagram = text[start:end]
    table = text[end:]
    styles = {
        args.box_style: "box",
        args.decision_style: "decision",
        args.terminal_style: "terminal",
        args.route_style: "route",
    }
    node_pattern = re.compile(
        r"\\node\[(?P<options>[^\]]*)\]\s*"
        r"\((?P<name>[^)]+)\)\s*(?P<body>.*?);",
        re.DOTALL,
    )
    label_pattern = re.compile(r"\\textbf\{\[(\d+)\]\}")

    solid: dict[int, str] = {}
    solid_counts: Counter[int] = Counter()
    proxies: list[int] = []
    errors: list[str] = []

    for match in node_pattern.finditer(diagram):
        tokens = option_tokens(match.group("options"))
        kinds = [styles[token] for token in tokens if token in styles]
        if not kinds:
            continue
        kind = kinds[0]
        labels = label_pattern.findall(match.group("body"))
        name_match = re.fullmatch(r"n(\d+)", match.group("name"))
        if kind == "route":
            if labels:
                proxies.extend(int(label) for label in labels)
            continue
        if not name_match:
            continue
        node_id = int(name_match.group(1))
        solid_counts[node_id] += 1
        solid[node_id] = kind
        if labels != [str(node_id)]:
            errors.append(
                f"solid node n{node_id} has displayed labels {labels or 'none'}"
            )

    if not solid:
        errors.append("no numbered solid nodes were found")
        first = last = 0
    else:
        first = args.first if args.first is not None else min(solid)
        last = args.last if args.last is not None else max(solid)
        expected = set(range(first, last + 1))
        missing = sorted(expected - set(solid))
        extra = sorted(set(solid) - expected)
        if missing:
            errors.append(f"missing solid nodes: {missing}")
        if extra:
            errors.append(f"solid nodes outside requested range: {extra}")
        duplicates = sorted(node for node, count in solid_counts.items() if count != 1)
        if duplicates:
            errors.append(f"duplicate solid nodes: {duplicates}")

    draw_pattern = re.compile(
        r"\\draw(?:\[[^\]]*\])?\s*\(n(\d+)(?:\.[^)]+)?\)"
    )
    outputs = Counter(int(node) for node in draw_pattern.findall(diagram))
    for node_id, kind in sorted(solid.items()):
        count = outputs[node_id]
        if kind == "box" and count != 1:
            errors.append(f"rectangle [{node_id}] has {count} drawn outputs, expected 1")
        elif kind == "decision" and count < 2:
            errors.append(f"decision [{node_id}] has {count} drawn outputs, expected >=2")
        elif kind == "terminal" and count != 0:
            errors.append(f"terminal [{node_id}] has {count} drawn outputs, expected 0")

    for target in sorted(set(proxies)):
        if solid.get(target) != "terminal":
            errors.append(f"dashed closure proxy [{target}] does not name a solid terminal")

    continuation_pattern = re.compile(r"(?:continue at|\bto)\s*\[(\d+)\]")
    for target in sorted({int(value) for value in continuation_pattern.findall(diagram)}):
        if target not in solid:
            errors.append(f"continuation targets missing solid node [{target}]")

    table_counts = Counter(
        int(value) for value in re.findall(r"^\[(\d+)\]\s*&", table, re.MULTILINE)
    )
    if solid:
        for node_id in range(first, last + 1):
            count = table_counts[node_id]
            if count != 1:
                errors.append(f"audit table has {count} rows for node [{node_id}]")

    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1

    terminal_count = sum(kind == "terminal" for kind in solid.values())
    print(
        f"PASS: nodes [{first}]--[{last}], {len(solid)} solid nodes, "
        f"{terminal_count} solid terminals, {len(proxies)} dashed closure proxies"
    )
    print("PASS: shape outputs, continuation targets, proxies, and audit-table rows")
    return 0


if __name__ == "__main__":
    sys.exit(main())

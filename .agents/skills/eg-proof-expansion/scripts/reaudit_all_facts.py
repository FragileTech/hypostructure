#!/usr/bin/env python3
"""Conservatively rebuild every EG fact-audit row from live Lean evidence.

This intentionally never promotes a declaration-name match to manuscript
compliance.  Exact mathematical matching remains an explicit proposition-level
obligation until a human audit records it.
"""

from __future__ import annotations

import re
from pathlib import Path

from audit_tables import (
    AUDIT_REL,
    FACT_HEADER,
    FACT_HEADING,
    NODE_HEADER,
    NODE_HEADING,
    parse_table,
    section,
    split_markdown_row,
)


ROOT = Path(__file__).resolve().parents[4]
DECL = re.compile(
    r"^(?:@\[[^\]]+\]\s*)*(?:private\s+)?(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|structure|class|inductive)\s+([A-Za-z_][A-Za-z0-9_']*)",
    re.MULTILINE,
)
CALLBACK = re.compile(
    r"\b(?:decode|encode|routeOf|proofOf|witnessOf|decisionOf|certificateOf|factOf|resultOf)\s*:"
)
ROW_MARKERS = ("FactManifest", "DecisionManifest", "AtomicCT", "Decision.run", "factOnly")


def lean_sources() -> list[Path]:
    roots = (ROOT / "hypostructure", ROOT / "proofs" / "hypostructure_erdos_64_eg")
    return sorted(
        path for root in roots for path in root.rglob("*.lean")
        if ".lake" not in path.parts
    )


def declaration_index() -> tuple[dict[str, list[tuple[Path, int, str]]], dict[str, list[str]], str]:
    index: dict[str, list[tuple[Path, int, str]]] = {}
    labels: dict[str, list[str]] = {}
    all_text: list[str] = []
    for path in lean_sources():
        text = path.read_text(encoding="utf-8")
        all_text.append(text)
        matches = list(DECL.finditer(text))
        for pos, match in enumerate(matches):
            end = matches[pos + 1].start() if pos + 1 < len(matches) else len(text)
            line = text.count("\n", 0, match.start()) + 1
            index.setdefault(match.group(1), []).append((path, line, text[match.start():end]))
        for label_match in re.finditer(r"(?:def|lem|prop|cor|thm):[a-z0-9-]+", text):
            following = next(
                (match for match in matches
                 if label_match.end() <= match.start() <= label_match.end() + 1200),
                None,
            )
            if following is not None:
                labels.setdefault(label_match.group(), []).append(following.group(1))
    return index, labels, "\n".join(all_text)


def identifiers(cell: str) -> list[str]:
    result: list[str] = []
    for quoted in re.findall(r"`([^`]+)`", cell):
        token = quoted.split(".")[-1]
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", token):
            result.append(token)
    return result


def escape(cell: str) -> str:
    return re.sub(r"(?<!\\)\|", r"\\|", cell)


def markdown(row: list[str]) -> str:
    return "| " + " | ".join(escape(cell) for cell in row) + " |"


def audit_fact(row: tuple[str, ...], index: dict[str, list[tuple[Path, int, str]]], label_index: dict[str, list[str]], all_lean: str) -> list[str]:
    label, page, nodes, _, lean_cell, *_ = row
    normalized = "".join(part for part in label.split(":", 1)[-1].split("-")).lower()
    fuzzy = [name for name in index if name.lower() == normalized]
    names = list(dict.fromkeys(identifiers(lean_cell) + label_index.get(label, []) + fuzzy))
    if label == "thm:main":
        names = ["erdos_64"]
    found = [(name, hit) for name in names for hit in index.get(name, [])]
    if not found:
        return [
            label, page, nodes, "—", "— (no live declaration located)",
            "❌ no live Lean declaration proving this manuscript fact was located",
            "❌ not kernel checked", "❌ no residual-local implementation",
            "❌ no keyed reads", "❌ no ledger publication", "❌ not wired",
            "❌ no compliant implementation", "❌ no implementation to audit",
        ]

    locations: list[str] = []
    blocks: list[str] = []
    for name, (path, line, block) in found:
        rel = path.relative_to(ROOT)
        item = f"`{name}` ({rel}:{line})"
        if item not in locations:
            locations.append(item)
            blocks.append(block)
    body = "\n".join(blocks)
    is_row = any(marker in body for marker in ROW_MARKERS)
    has_current = "FactInputs.current" in body or "inputs.current" in body
    has_get = "FactInputs.get" in body or "inputs.get" in body or "ExactLedger.get" in body
    has_manifest = "FactManifest" in body or "DecisionManifest" in body or "rowManifest" in body
    has_produces = "Produces" in body or "Decision.run" in body or ".cons" in body
    has_run = "AtomicCT.run" in body or "Decision.run" in body or "factOnly" in body
    illegal = bool(CALLBACK.search(body))
    wired_names = [name for name, _ in found if all_lean.count(name) > len(index.get(name, []))]

    if is_row:
        tactic = "`Decision.run`" if "Decision.run" in body else "`AtomicCT.run` / `factOnly` candidate"
        local = "⚠ reads the current residual; exact manuscript locality not proposition-audited" if has_current else "❌ no current-residual read located in the candidate row"
        reads = "⚠ keyed `FactInputs.get`/`ExactLedger.get` reads located; required-key match not proposition-audited" if has_get else "❌ no keyed predecessor read located"
        writes = "⚠ manifest production located; exact labeled proposition/key match not proposition-audited" if has_manifest and has_produces and has_run else "❌ complete manifest publication path not located"
        wired = "⚠ candidate is referenced outside its declaration; exact predecessor/branch wiring not re-established" if wired_names else "❌ no live external call site located"
    else:
        tactic = "standalone/static declaration candidate"
        local = "N/A — declaration is not an active-residual executor"
        reads = "N/A — declaration has no ledger executor"
        writes = "❌ exact manuscript fact is not published by this declaration"
        wired = "⚠ declaration is referenced, but no exact ledger publication was established" if wired_names else "❌ no Assembly/row publication established"

    legal = "❌ forbidden callback/side-input parameter located in the candidate declaration block" if illegal else "⚠ no forbidden callback token located; full closed-API audit not yet established"
    kernel = "⚠ declaration located; current full Assembly build fails before unconditional closure"
    if label == "def:exact-response-profile":
        kernel = "❌ current build fails in its schema at `SpineVocabulary.lean:2128`: a `Finset` is supplied where `Set.InjOn` expects a `Set`"
    elif label == "thm:main":
        kernel = "❌ `lake build HypostructureErdos64EG.Assembly` fails upstream at `SpineVocabulary.lean:2128`; unconditional closure is not kernel checked"
    return [
        label, page, nodes, tactic, "<br>".join(locations),
        "⚠ related live declaration(s) located, but the exact manuscript proposition, hypotheses, alternatives, and proof strategy have not yet been freshly matched",
        kernel,
        local, reads, writes, wired, legal,
        "⚠ no supplied literal was detected by this structural pass; proposition-level derivation remains unaudited",
    ]


def node_labels(facts: list[list[str]]) -> dict[int, list[str]]:
    result = {number: [] for number in range(1, 158)}
    for row in facts:
        normalized = row[2].replace("–", "-")
        for first, last in re.findall(r"\[(\d+)\](?:-\[(\d+)\])?", normalized):
            start, stop = int(first), int(last or first)
            for number in range(start, stop + 1):
                result[number].append(row[0])
    return result


def main() -> None:
    path = ROOT / AUDIT_REL
    text = path.read_text(encoding="utf-8")
    facts = parse_table(section(text, FACT_HEADING, NODE_HEADING), FACT_HEADER)
    nodes = parse_table(section(text, NODE_HEADING, None), NODE_HEADER)
    index, label_index, all_lean = declaration_index()
    audited = [audit_fact(row, index, label_index, all_lean) for row in facts.rows]
    labels = node_labels(audited)

    fact_start = text.index("| " + " | ".join(FACT_HEADER) + " |")
    node_heading = text.index(NODE_HEADING)
    fact_prefix = text[:fact_start]
    fact_table = [markdown(list(FACT_HEADER)), markdown(["---"] * len(FACT_HEADER))]
    fact_table.extend(markdown(row) for row in audited)

    node_section = text[node_heading:]
    node_header_at = node_section.index("| " + " | ".join(NODE_HEADER) + " |")
    node_prefix = node_section[:node_header_at]
    node_table = [markdown(list(NODE_HEADER)), markdown(["---"] * len(NODE_HEADER))]
    for old in nodes.rows:
        number = int(old[0][1:-1])
        row = list(old)
        row[12] = ", ".join(f"`{label}`" for label in labels[number]) or "—"
        node_table.append(markdown(row))

    path.write_text(
        fact_prefix + "\n".join(fact_table) + "\n\n" + node_prefix + "\n".join(node_table) + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()

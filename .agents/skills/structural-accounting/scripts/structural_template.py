#!/usr/bin/env python3
"""Emit the blank structural-accounting template for one residual.

Usage:
  structural_template.py <ResidualName> [--repo PATH] [--out PATH]

It writes a Markdown file containing:
  * Table 1 skeleton: every property of the structural register
    (tools/methodology_gate/policy/structural-register.json), grouped as on
    the methodology page, with empty status/fact/technique columns;
  * Table 2 skeleton: every fact key of the named residual `abbrev`
    (generic residuals in Assembly/Residuals.lean, root subtypes and arm
    blocks in Assembly/Residuals/*.lean), in ledger order, with empty
    columns.  A conjunct naming another residual `abbrev` (a subtype's
    generic residual, or a conjunctive block) is expanded in place; a
    disjunctive arm block (a product path) is listed, not expanded;
  * the technique register, for reference.

The script only extracts; it never marks anything. Marking is the agent's job.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REGISTER = Path("tools/methodology_gate/policy/structural-register.json")
RESIDUALS = Path(
    "proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Residuals.lean"
)
RESIDUALS_DIR = RESIDUALS.with_suffix("")
VOCAB = Path("hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean")

KEY_RE = re.compile(r"erdosReceiverLoadProfile\s+spineData\s+\.(\w+)\s+selected\.object")


ABBREV_RE = re.compile(r"^abbrev (\w+)\b.*$", re.M)
STOP_RE = re.compile(r"^(abbrev|def|noncomputable def|theorem|/--)\b", re.M)
REF_RE = re.compile(r"\b([A-Z]\w*)\s+selected\b(?!\.)")


def residual_bodies(texts: list[str]) -> dict[str, str]:
    bodies: dict[str, str] = {}
    for text in texts:
        for start in ABBREV_RE.finditer(text):
            rest = text[start.end():]
            stop = STOP_RE.search(rest)
            bodies.setdefault(start.group(1), rest[: stop.start()] if stop else rest)
    return bodies


def residual_keys(bodies: dict[str, str], name: str,
                  keys: list[str], blocks: list[str]) -> None:
    body = bodies[name]
    events = [(m.start(), "key", m.group(1)) for m in KEY_RE.finditer(body)]
    events += [(m.start(), "ref", m.group(1)) for m in REF_RE.finditer(body)
               if m.group(1) in bodies and m.group(1) != name]
    for _, kind, value in sorted(events):
        if kind == "key":
            if value not in keys:
                keys.append(value)
        elif "∨" in bodies[value]:
            if value not in blocks:
                blocks.append(value)
        else:
            residual_keys(bodies, value, keys, blocks)


def key_indices(vocab: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for key, idx in re.findall(r"\|\s*\.(\w+)\s*=>\s*(\d+)\s*$", vocab, re.M):
        out.setdefault(key, idx)
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("residual")
    parser.add_argument("--repo", default=".")
    parser.add_argument("--out")
    args = parser.parse_args()
    repo = Path(args.repo)

    register = json.loads((repo / REGISTER).read_text())
    sources = [repo / RESIDUALS] + sorted((repo / RESIDUALS_DIR).glob("*.lean"))
    bodies = residual_bodies([f.read_text() for f in sources])
    if args.residual not in bodies:
        sys.exit(f"residual `{args.residual}` not found in {RESIDUALS} "
                 f"or {RESIDUALS_DIR}/*.lean")
    keys: list[str] = []
    blocks: list[str] = []
    residual_keys(bodies, args.residual, keys, blocks)
    idx = key_indices((repo / VOCAB).read_text()) if (repo / VOCAB).exists() else {}

    lines: list[str] = [f"# Structural accounting: `{args.residual}`", ""]
    lines += [
        f"Facts on the residual: {len(keys)}. "
        f"Structural coordinates: {sum(len(g['properties']) for g in register['groups'])}.",
        "",
    ]
    if blocks:
        lines += [
            "Disjunctive arm blocks (product path; not expanded, add the keys "
            "of the arm the path took): " + ", ".join(f"`{b}`" for b in blocks) + ".",
            "",
        ]
    lines += [
        "Status legend: `x` accounted · `~` partially accounted · "
        "`gap` present at G but unaccounted · `n/a` absent at G (reason required) · "
        "`nonG` accounted only through an object outside G (does not count).",
        "",
        "## Table 1 — Structural coordinates (same for every residual)",
        "",
    ]
    for group in register["groups"]:
        lines += [
            f"### {group['title']} (`{group['id']}`)",
            "",
            "| Code | Property | Observable | Status | Accounting facts | "
            "Certificate obtained | Techniques used | Missing accounting |",
            "|---|---|---|---|---|---|---|---|",
        ]
        for p in group["properties"]:
            obs = p["observable"].replace("|", "\\|")
            lines.append(f"| {p['id']} | {p['name']} | {obs} |  |  |  |  |  |")
        lines.append("")

    lines += [
        "## Table 2 — Facts of the residual → structural coordinates",
        "",
        "| # | Key | idx | Statement at G (one line) | About G only? | "
        "Coordinates accounted | Certificate type | Consumed by |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for n, key in enumerate(keys, 1):
        lines.append(f"| {n} | `{key}` | {idx.get(key, '?')} |  |  |  |  |  |")
    lines += ["", "## Technique register (reference)", "",
              "| Code | Technique | Standard move |", "|---|---|---|"]
    for t in register["techniques"]:
        lines.append(f"| {t['id']} | {t['name']} | {t['move']} |")
    lines.append("")

    text = "\n".join(lines)
    if args.out:
        Path(args.out).write_text(text)
        print(f"wrote {args.out}: {len(keys)} facts"
              + (f", {len(blocks)} unexpanded arm blocks" if blocks else ""))
    else:
        print(text)


if __name__ == "__main__":
    main()

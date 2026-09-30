#!/usr/bin/env python3
"""Emit the blank structural-accounting template for one residual.

Usage:
  structural_template.py <ResidualName> [--repo PATH] [--out PATH]

It writes a Markdown file containing:
  * Table 1 skeleton: every property of the structural register
    (tools/methodology_gate/policy/structural-register.json), grouped as on
    the methodology page, with empty status/fact/technique columns;
  * Table 2 skeleton: every fact key of the named residual `abbrev`
    in Assembly/Residuals.lean, in ledger order, with empty columns;
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
VOCAB = Path("hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean")

KEY_RE = re.compile(r"erdosReceiverLoadProfile\s+spineData\s+\.(\w+)\s+selected\.object")


def residual_keys(text: str, name: str) -> list[str]:
    start = re.search(rf"^abbrev {re.escape(name)}\b.*$", text, re.M)
    if not start:
        sys.exit(f"residual `{name}` not found in {RESIDUALS}")
    rest = text[start.end():]
    stop = re.search(r"^(abbrev|def|noncomputable def|theorem|/--)\b", rest, re.M)
    body = rest[: stop.start()] if stop else rest
    keys: list[str] = []
    for key in KEY_RE.findall(body):
        if key not in keys:
            keys.append(key)
    return keys


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
    keys = residual_keys((repo / RESIDUALS).read_text(), args.residual)
    idx = key_indices((repo / VOCAB).read_text()) if (repo / VOCAB).exists() else {}

    lines: list[str] = [f"# Structural accounting: `{args.residual}`", ""]
    lines += [
        f"Facts on the residual: {len(keys)}. "
        f"Structural coordinates: {sum(len(g['properties']) for g in register['groups'])}.",
        "",
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
        print(f"wrote {args.out}: {len(keys)} facts")
    else:
        print(text)


if __name__ == "__main__":
    main()

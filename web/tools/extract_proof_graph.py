#!/usr/bin/env python3
"""Turn the manuscripts in this repository into the JSON the explorer reads.

Each paper draws its argument as numbered TikZ panels and tabulates which
lemmas and definitions stand behind each node. :mod:`proof_graph` knows those
conventions; :mod:`papers` describes each paper. This script runs them.

Usage::

    python web/tools/extract_proof_graph.py                    # every proof
    python web/tools/extract_proof_graph.py --proof navier-stokes
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from papers import SPECS  # noqa: E402
from proof_graph import build_document  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT = REPO_ROOT / "web" / "frontend" / "public" / "data"


def write(slug: str, out_dir: Path) -> dict:
    document = build_document(SPECS[slug], REPO_ROOT)
    out_dir.mkdir(parents=True, exist_ok=True)
    path = out_dir / f"{slug}.json"
    path.write_text(json.dumps(document, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")

    chapters = len(document.get("chapters", [])) or 1
    print(
        f"{path}: {len(document['nodes'])} nodes, {len(document['edges'])} edges, "
        f"{len(document['groups'])} panels in {chapters} chapter(s), "
        f"{len(document['items'])} results, {len(document['invariants'])} constraints, "
        f"{len(document['constants'])} constants"
    )
    return document


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof", choices=[*SPECS, "all"], default="all")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()

    slugs = list(SPECS) if args.proof == "all" else [args.proof]
    for slug in slugs:
        write(slug, args.out)


if __name__ == "__main__":
    main()

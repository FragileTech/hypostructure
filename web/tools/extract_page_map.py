#!/usr/bin/env python3
"""Map every ``\\label`` of a manuscript to its line in the ``.tex`` and its page in the PDF.

The explorer's proof graphs (`extract_proof_graph.py`) record where a result is
stated as a line of the LaTeX source. Readers open the PDF, so they also need
the page. LaTeX already knows it: the ``.aux`` file written next to each PDF
holds one ``\\newlabel{L}{{number}{page}{title}{anchor}{}}`` line per label,
with the page the label landed on in that very build. This script joins the two.

One JSON is written per PDF, named after it::

    web/frontend/public/data/pages/original_erdos_64_proof.json
    {
      "pdf": "original_erdos_64_proof.pdf",
      "tex": "to_formalize/original_erdos_64_proof.tex",
      "chapter": "erdos-gyarfas",
      "pages": 240,
      "labels": {
        "def:net-charge": {"line": 8675, "page": 136, "number": "13.4",
                           "anchor": "theorem.13.4"},
        ...
      }
    }

Labels are the raw ``\\label`` names; the proof-graph JSON prefixes them with
the chapter id in multi-chapter proofs, and the app strips that prefix.
A label present in the source but missing from the ``.aux`` (unused, or from
an environment that does not write one) keeps its line and gets ``"page": null``.

Usage::

    python web/tools/extract_page_map.py                    # every proof
    python web/tools/extract_page_map.py --proof navier-stokes
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

from latex_source import line_of, strip_comments  # noqa: E402
from papers import SPECS  # noqa: E402
from proof_graph import ChapterSpec  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT = REPO_ROOT / "web" / "frontend" / "public" / "data" / "pages"

#: ``\\label{name}`` and cleveref's ``\\label[type]{name}``.
_LABEL = re.compile(r"\\label\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}")
#: ``\newlabel{name}{{number}{page}{title}{anchor}{extra}}``; hyperref writes
#: five fields, plain LaTeX two. ``@cref`` companions are cleveref's and skipped.
_NEWLABEL = re.compile(
    r"^\\newlabel\{(?P<name>[^}@]+)\}\{\{(?P<number>.*?)\}\{(?P<page>\d+)\}"
    r"(?:\{(?P<title>.*?)\}\{(?P<anchor>[^}]*)\}\{[^}]*\})?\}\s*$",
    re.M,
)


def source_labels(tex: str) -> dict[str, int]:
    """Every ``\\label`` in the source, with the 1-based line it sits on.

    Comments are stripped first so a commented-out label is not reported. If a
    label is written twice (LaTeX warns, and keeps the last), the first line wins,
    which is where a reader would look.
    """
    text = strip_comments(tex)
    lines: dict[str, int] = {}
    for match in _LABEL.finditer(text):
        lines.setdefault(match.group(1).strip(), line_of(text, match.start()))
    return lines


def aux_labels(aux: str) -> dict[str, dict[str, Any]]:
    """The ``\\newlabel`` records of an ``.aux`` file, keyed by label name."""
    records: dict[str, dict[str, Any]] = {}
    for match in _NEWLABEL.finditer(aux):
        records[match.group("name")] = {
            "page": int(match.group("page")),
            "number": match.group("number"),
            "anchor": match.group("anchor") or None,
        }
    return records


def build_page_map(chapter: ChapterSpec, root: Path) -> dict[str, Any]:
    tex_path = root / chapter.source
    aux_path = tex_path.with_suffix(".aux")
    pdf_path = tex_path.with_suffix(".pdf")
    if not aux_path.exists():
        raise FileNotFoundError(f"{aux_path}: no .aux next to the manuscript; build the PDF first")

    lines = source_labels(tex_path.read_text(encoding="utf-8"))
    placed = aux_labels(aux_path.read_text(encoding="utf-8", errors="replace"))

    labels: dict[str, dict[str, Any]] = {}
    for name, line in sorted(lines.items(), key=lambda pair: pair[1]):
        record = placed.get(name)
        labels[name] = {
            "line": line,
            "page": record["page"] if record else None,
            "number": record["number"] if record else None,
            "anchor": record["anchor"] if record else None,
        }
    # A label the .aux knows but the source no longer has: the .aux is stale.
    for name in placed.keys() - lines.keys():
        labels[name] = {"line": None, **placed[name]}

    pages = max((record["page"] for record in placed.values()), default=0)
    return {
        "pdf": pdf_path.name,
        "tex": chapter.source,
        "chapter": chapter.id,
        "pages": pages,
        "labels": labels,
    }


def write(slug: str, out_dir: Path) -> list[Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []
    for chapter in SPECS[slug].chapters:
        page_map = build_page_map(chapter, REPO_ROOT)
        path = out_dir / f"{Path(page_map['pdf']).stem}.json"
        path.write_text(json.dumps(page_map, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
        labels = page_map["labels"]
        unplaced = sum(1 for record in labels.values() if record["page"] is None)
        stale = sum(1 for record in labels.values() if record["line"] is None)
        print(
            f"{path}: {len(labels)} labels over {page_map['pages']} pages"
            f"{f', {unplaced} without a page' if unplaced else ''}"
            f"{f', {stale} only in the .aux' if stale else ''}"
        )
        written.append(path)
    return written


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--proof", choices=[*SPECS, "all"], default="all")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()

    slugs = list(SPECS) if args.proof == "all" else [args.proof]
    for slug in slugs:
        write(slug, args.out)


if __name__ == "__main__":
    main()

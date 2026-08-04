#!/usr/bin/env python3
"""Generate and validate the EG skill's compiled Hypostructure API catalog."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


BEGIN = "<!-- BEGIN GENERATED API -->"
END = "<!-- END GENERATED API -->"
SKILL_REL = Path(".agents/skills/eg-proof-expansion")
CATALOG_REL = SKILL_REL / "references/allowed-api.md"


def fail(message: str) -> "NoReturn":
    print(f"error: {message}", file=sys.stderr)
    raise SystemExit(1)


def validate_root(root: Path) -> Path:
    root = root.resolve()
    required = (
        root / "hypostructure/Hypostructure/Canonical/WebExport.lean",
        root / CATALOG_REL,
        root / "proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/StrategyDag.lean",
        root / "EG_STRATEGYDAG_AUDIT.md",
        root / "to_formalize/original_erdos_64_proof.tex",
    )
    missing = [str(path) for path in required if not path.is_file()]
    if missing:
        fail("repository root is missing: " + ", ".join(missing))
    return root


def compiled_catalog(root: Path) -> list[dict[str, object]]:
    package = root / "hypostructure"
    with tempfile.TemporaryDirectory(prefix="eg-proof-api-") as temp_dir:
        raw = Path(temp_dir) / "declarations.json"
        env = os.environ.copy()
        env["HYPOSTRUCTURE_WEB_DECLARATIONS_EXPORT"] = str(raw)
        command = ["lake", "env", "lean", "Hypostructure/Canonical/WebExport.lean"]
        result = subprocess.run(
            command,
            cwd=package,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        if result.returncode != 0:
            fail("compiled API export failed:\n" + result.stdout)
        if not raw.is_file():
            fail("compiled API export produced no declaration catalog")
        payload = json.loads(raw.read_text(encoding="utf-8"))

    declarations = []
    for declaration in payload.get("declarations", []):
        module = str(declaration.get("module", ""))
        if module.startswith("Hypostructure.Core"):
            category = "Core"
        elif any(
            module == f"Hypostructure.CT{number}"
            or module.startswith(f"Hypostructure.CT{number}.")
            for number in range(1, 18)
        ):
            category = "CT"
        elif module.startswith("Hypostructure.Graph.Strategy"):
            category = "Graph Strategy candidate"
        else:
            continue
        declarations.append(
            {
                "name": str(declaration["name"]),
                "kind": str(declaration["kind"]),
                "type": str(declaration["type"]),
                "module": module,
                "source_file": str(declaration["source_file"]),
                "category": category,
            }
        )
    declarations.sort(key=lambda item: str(item["name"]))
    if not declarations:
        fail("compiled API filter selected no declarations")
    return declarations


def markdown_catalog(declarations: list[dict[str, object]]) -> str:
    counts: dict[str, int] = {}
    for declaration in declarations:
        category = str(declaration["category"])
        counts[category] = counts.get(category, 0) + 1

    lines = [
        f"Compiled declarations: **{len(declarations)}**.",
        "",
        "Category counts: "
        + ", ".join(f"**{name}** {counts[name]}" for name in sorted(counts))
        + ".",
        "",
        "The `type` fields below come from the compiled Lean environment.  Docstrings",
        "and comments are deliberately excluded.",
        "",
    ]
    current_module = None
    for declaration in declarations:
        module = str(declaration["module"])
        if module != current_module:
            current_module = module
            lines.extend([f"### `{module}`", ""])
        declaration_type = str(declaration["type"]).replace("```", "` ` `")
        lines.extend(
            [
                f"#### `{declaration['name']}`",
                "",
                f"- Category: {declaration['category']}",
                f"- Kind: `{declaration['kind']}`",
                f"- Source: `{declaration['source_file']}`",
                "- Compiled type:",
                "",
                "```lean",
                declaration_type,
                "```",
                "",
            ]
        )
    return "\n".join(lines).rstrip() + "\n"


def replace_generated(document: str, generated: str) -> str:
    if document.count(BEGIN) != 1 or document.count(END) != 1:
        fail("allowed-api.md must contain exactly one generated API marker pair")
    prefix, remainder = document.split(BEGIN, 1)
    _, suffix = remainder.split(END, 1)
    return prefix + BEGIN + "\n" + generated + END + suffix


def expected_document(root: Path) -> tuple[Path, str]:
    path = root / CATALOG_REL
    current = path.read_text(encoding="utf-8")
    generated = markdown_catalog(compiled_catalog(root))
    return path, replace_generated(current, generated)


def refresh(root: Path) -> None:
    path, expected = expected_document(root)
    path.write_text(expected, encoding="utf-8")
    print(f"refreshed {path.relative_to(root)}")


def check(root: Path) -> None:
    path, expected = expected_document(root)
    current = path.read_text(encoding="utf-8")
    if current != expected:
        fail(
            f"{path.relative_to(root)} is stale; run "
            "api_catalog.py refresh --repo-root ."
        )
    print(f"catalog is current: {path.relative_to(root)}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("check", "refresh"))
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    root = validate_root(args.repo_root)
    if args.command == "refresh":
        refresh(root)
    else:
        check(root)


if __name__ == "__main__":
    main()

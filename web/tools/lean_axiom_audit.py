#!/usr/bin/env python3
"""Kernel-level axiom audit of the Erdos-Gyarfas Lean assembly.

Runs the real thing: inserts tracer stubs for the undefined frontier
producers, builds the package, then runs ``#print axioms`` on every
Assembly declaration.  A declaration is *clean* when the tracer axiom
``frontierGap`` does not appear in its axiom list; otherwise it is
*tainted* by an unfinished producer.

The stubs are ``def``s (not ``axiom``s) so that ``frontierGap``
propagates through them -- an ``axiom`` stub is terminal for
``#print axioms`` and would report every caller as clean.

Writes JSON to stdout (or --out) and restores the tree on exit.

Usage::

    python web/tools/lean_axiom_audit.py --out web/data/eg_axiom_audit.json
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
PROOF_DIR = REPO_ROOT / "proofs" / "hypostructure_erdos_64_eg"
PKG = PROOF_DIR / "HypostructureErdos64EG"
ASSEMBLY = PKG / "Assembly.lean"
STUBS = PKG / "FrontierStubs.lean"
AUDIT = PKG / "AxiomAudit.lean"

TRACER = "frontierGap"

_DECL_RE = re.compile(
    r"^(?:noncomputable\s+)?(?:private\s+)?(?:def|theorem|lemma|abbrev)\s+"
    r"([A-Za-z0-9_']+)",
)
_UNKNOWN_RE = re.compile(r"Unknown identifier `([A-Za-z0-9_']+)`")
_AXIOMS_RE = re.compile(r"^'([^']+)' depends on axioms:", re.MULTILINE)


def _lake(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", *args], cwd=PROOF_DIR, capture_output=True, text=True
    )


def declarations() -> list[str]:
    """Every top-level declaration name in Assembly.lean, in source order."""
    return [
        m.group(1)
        for line in ASSEMBLY.read_text(encoding="utf-8").splitlines()
        if (m := _DECL_RE.match(line))
    ]


def missing_producers() -> list[str]:
    """Identifiers Assembly.lean references but nothing defines."""
    build = _lake("build")
    return sorted(set(_UNKNOWN_RE.findall(build.stdout + build.stderr)))


def arity_of(name: str, text: str) -> int:
    """How many explicit arguments a producer is applied to at its call sites."""
    arity = 1
    for m in re.finditer(rf"\b{re.escape(name)}\b([^\n]*)", text):
        tail = m.group(1)
        # Count bare identifier arguments before any parenthesised tactic block.
        words = re.findall(r"\s+([A-Za-z_][A-Za-z0-9_']*)", tail.split("(")[0])
        arity = max(arity, len(words))
    return arity


def write_stubs(names: list[str]) -> None:
    """Tracer stubs. ``def`` (never ``axiom``) so the tracer propagates."""
    text = ASSEMBLY.read_text(encoding="utf-8")
    lines = [
        "import HypostructureErdos64EG.Problem",
        "",
        "namespace HypostructureErdos64EG",
        "",
        f"axiom {TRACER} : False",
        "",
    ]
    for name in names:
        n = arity_of(name, text)
        greek = ["α", "β", "γ", "δ", "ε"][: n + 1]
        binders = " ".join(greek)
        arrow = " → ".join(greek)
        holes = " ".join("_" for _ in range(n))
        lines.append(f"noncomputable def {name} : ∀ {{{binders} : Sort _}}, {arrow} :=")
        lines.append(f"  fun {holes} => {TRACER}.elim")
    lines += ["", "end HypostructureErdos64EG", ""]
    STUBS.write_text("\n".join(lines), encoding="utf-8")


def write_audit(names: list[str]) -> None:
    body = ["import HypostructureErdos64EG", "", "namespace HypostructureErdos64EG", ""]
    body += [f"#print axioms {n}" for n in names]
    body += ["", "end HypostructureErdos64EG", ""]
    AUDIT.write_text("\n".join(body), encoding="utf-8")


def split_axiom_report(text: str) -> tuple[list[str], list[str]]:
    """Split ``#print axioms`` output into clean and tracer-tainted names."""
    clean: list[str] = []
    tainted: list[str] = []
    blocks = re.split(r"(?=^')", text, flags=re.MULTILINE)
    for block in blocks:
        m = _AXIOMS_RE.match(block.strip())
        if not m:
            continue
        short = m.group(1).rsplit(".", 1)[-1]
        (tainted if TRACER in block else clean).append(short)
    return sorted(set(clean)), sorted(set(tainted))


def restore(import_added: bool) -> None:
    STUBS.unlink(missing_ok=True)
    AUDIT.unlink(missing_ok=True)
    if import_added:
        lines = ASSEMBLY.read_text(encoding="utf-8").splitlines(keepends=True)
        if lines and lines[0].startswith("import HypostructureErdos64EG.FrontierStubs"):
            ASSEMBLY.write_text("".join(lines[1:]), encoding="utf-8")


def run() -> dict:
    names = declarations()
    stubs = missing_producers()
    import_added = False
    try:
        if stubs:
            write_stubs(stubs)
            head = ASSEMBLY.read_text(encoding="utf-8")
            ASSEMBLY.write_text(
                "import HypostructureErdos64EG.FrontierStubs\n" + head, encoding="utf-8"
            )
            import_added = True

        build = _lake("build")
        if build.returncode != 0:
            errors = [
                l for l in (build.stdout + build.stderr).splitlines()
                if l.startswith("error:")
            ]
            raise SystemExit(
                "lake build failed with stubs in place:\n" + "\n".join(errors[:20])
            )

        write_audit(names)
        proc = subprocess.run(
            ["lake", "env", "lean", str(AUDIT.relative_to(PROOF_DIR))],
            cwd=PROOF_DIR, capture_output=True, text=True,
        )
        clean, tainted = split_axiom_report(proc.stdout + proc.stderr)
    finally:
        restore(import_added)

    missing = sorted(set(names) - set(clean) - set(tainted))
    return {
        "tracer": TRACER,
        "declarations": len(names),
        "frontier_stubs": stubs,
        "clean": clean,
        "tainted": tainted,
        "unreported": missing,
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path)
    args = ap.parse_args()
    report = run()
    text = json.dumps(report, indent=1) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
        print(
            f"{args.out}: {len(report['clean'])} clean, {len(report['tainted'])} tainted, "
            f"{len(report['frontier_stubs'])} frontier stubs",
            file=sys.stderr,
        )
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()

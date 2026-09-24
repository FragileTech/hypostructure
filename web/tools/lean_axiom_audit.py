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
    r"^(?:@\[[^\n]*?\]\s*)?(?:(?:noncomputable|private|protected)\s+)*(?:def|theorem|lemma|abbrev)\s+"
    r"([A-Za-z0-9_'.]+)",
)
_UNKNOWN_RE = re.compile(r"Unknown identifier `([A-Za-z0-9_']+)`")
_AXIOMS_RE = re.compile(r"^'([^']+)' depends on axioms:", re.MULTILINE)


def _lake(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", *args], cwd=PROOF_DIR, capture_output=True, text=True
    )


def assembly_sources() -> list[Path]:
    """Include the compatibility module and every split assembly module."""
    return [ASSEMBLY, *sorted((PKG / "Assembly").rglob("*.lean"))]


def source_declarations() -> list[tuple[Path, str]]:
    return [
        (path, m.group(1))
        for path in assembly_sources()
        for line in path.read_text(encoding="utf-8").splitlines()
        if (m := _DECL_RE.match(line))
    ]


def declarations() -> list[str]:
    """Source names, including explicitly qualified internal declarations."""
    return [name for _, name in source_declarations()]


def compiled_declarations() -> list[str]:
    """Resolve private names through Lean's index rather than inventing manglings."""
    result = []
    for path, name in source_declarations():
        index = (PROOF_DIR / ".lake/build/lib/lean" / path.relative_to(PROOF_DIR)).with_suffix(".ilean")
        decls = json.loads(index.read_text(encoding="utf-8"))["decls"]
        qualified = "HypostructureErdos64EG." + name
        matches = [n for n in decls if n == qualified or n.endswith("." + qualified)]
        if len(matches) != 1:
            raise RuntimeError(f"Cannot resolve {name} in {index}: {matches}")
        result.append(matches[0])
    return result


def assembly_text() -> str:
    return "\n".join(path.read_text(encoding="utf-8") for path in assembly_sources())


def missing_producers() -> list[str]:
    """Identifiers the assembly modules reference but nothing defines."""
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
    text = assembly_text()
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
    # Private names contain numeric Name components, which cannot be written
    # directly as source identifiers in a `#print axioms` command.
    body = ["import HypostructureErdos64EG", "import Lean", "", "open Lean in", "run_cmd do",
            "  let env ← getEnv", "  let names : List String := " + json.dumps(names),
            "  for text in names do",
            '    let name := (text.splitOn ".").foldl (fun n part =>',
            "      match part.toNat? with",
            "      | some i => Name.num n i",
            "      | none => Name.str n part) Name.anonymous",
            '    unless env.contains name do throwError "missing audit declaration {name}"',
            "    let axioms ← collectAxioms name",
            '    let listed := String.intercalate ", " (axioms.toList.map Name.toString)',
            '    IO.println s!"\'{text}\' depends on axioms: [{listed}]"', ""]
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
        short = m.group(1).rsplit("HypostructureErdos64EG.", 1)[-1]
        (tainted if TRACER in block else clean).append(short)
    return sorted(set(clean)), sorted(set(tainted))


def restore(originals: dict[Path, bytes | None]) -> None:
    for path, original in originals.items():
        if original is None:
            path.unlink(missing_ok=True)
        else:
            path.write_bytes(original)


def insert_stub_imports(names: list[str], originals: dict[Path, bytes | None]) -> None:
    """Stubs must be visible where missing names are used, not just at the root."""
    if not names:
        return
    pattern = re.compile(r"\b(?:" + "|".join(re.escape(n) for n in names) + r")\b")
    for path in assembly_sources():
        text = path.read_text(encoding="utf-8")
        if pattern.search(text) and "import HypostructureErdos64EG.FrontierStubs\n" not in text:
            originals.setdefault(path, path.read_bytes())
            path.write_text("import HypostructureErdos64EG.FrontierStubs\n" + text,
                            encoding="utf-8")


def run() -> dict:
    names = declarations()
    stubs: list[str] = []
    originals = {p: p.read_bytes() if p.exists() else None for p in (STUBS, AUDIT)}
    try:
        # An upstream failure can hide missing names in a downstream module.
        # Discover successive frontiers until the full dependency graph builds.
        while True:
            build = _lake("build")
            if build.returncode == 0:
                break
            output = build.stdout + build.stderr
            new_stubs = sorted(set(_UNKNOWN_RE.findall(output)) - set(stubs))
            if not new_stubs:
                errors = [line for line in output.splitlines() if line.startswith("error:")]
                raise RuntimeError("lake build failed with stubs in place:\n" +
                                   "\n".join(errors[:20]))
            stubs = sorted(set(stubs) | set(new_stubs))
            write_stubs(stubs)
            insert_stub_imports(stubs, originals)

        write_audit(compiled_declarations())
        proc = subprocess.run(
            ["lake", "env", "lean", str(AUDIT.relative_to(PROOF_DIR))],
            cwd=PROOF_DIR, capture_output=True, text=True,
        )
        if proc.returncode != 0:
            raise RuntimeError("Axiom inspection failed:\n" + proc.stdout + proc.stderr)
        clean, tainted = split_axiom_report(proc.stdout + proc.stderr)
    finally:
        restore(originals)

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

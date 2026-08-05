#!/usr/bin/env python3
"""Guard the canonical-ledger boundary.

The framework carries exactly one data carrier, `Core.Residual.ExactLedger`,
and `FactSystem.value_subsingleton` makes a fact value unable to hold data.
Two things that law cannot see are checked here instead:

  1. a declaration grafted into the canonical ledger's own namespace, which
     reads as canonical API while carrying whatever it likes;
  2. a structure named `...Ledger` that impersonates the canonical one without
     ever claiming to be a `FactSystem`.

Quarantined modules (see `quarantine.txt`) are the legacy carriers, kept on
disk as the porting reference for the rewrite.  They are outside the build
closure; this gate keeps them there.

Exit 0 = clean.  Scope is Core and Graph; PDE is not checked.
"""

from __future__ import annotations

import pathlib
import re
import sys

REPO = pathlib.Path(__file__).resolve().parents[2]
LIB = REPO / "hypostructure" / "Hypostructure"
ROOT_MODULE = REPO / "hypostructure" / "Hypostructure.lean"
QUARANTINE = REPO / "hypostructure" / "quarantine.txt"

# The one file allowed to declare the canonical ledger's API.
CANONICAL = LIB / "Core" / "Residual" / "ExactLedger.lean"

# The modules that constitute the single official API surface.  Only these may
# name a ledger at all; everywhere else, a ledger-named declaration is a second
# API no matter which form it takes.
CANONICAL_API = {
    CANONICAL,
    LIB / "Core" / "Strategy" / "FactManifest.lean",
    LIB / "Core" / "Strategy" / "ExactExecution.lean",
    LIB / "Core" / "Strategy" / "ProblemResidual.lean",
    LIB / "Core" / "Strategy" / "MinimalCounterexampleScope.lean",
    LIB / "Core" / "Strategy" / "FactOnlyStrategy.lean",
}

# Modules whose new-API port is complete; everything reachable from the root
# outside PDE is checked.
CHECKED_PREFIXES = ("Hypostructure.Core.", "Hypostructure.Graph.",
                    "Hypostructure.Fixtures.")

GRAFT = re.compile(r"_root_\.Hypostructure\.Core\.Residual\.ExactLedger\.")

# Any identifier ending in `Ledger` other than the canonical one.  The
# exemption is matched against the whole dotted path, so a namespaced shadow
# such as `SupportComplementNormalization.ExactLedger` is still a violation.
NONCANONICAL_LEDGER = re.compile(
    r"(?<![\w.])"
    r"(?!(?:Hypostructure\.)?(?:Core\.Residual\.)?ExactLedger\b)"
    r"(?:[A-Za-z_][A-Za-z0-9_']*\.)*"
    r"[A-Za-z0-9_']*Ledger\b"
)

# Every declaration form, not just the carriers.  An accessor named
# `...Ledger` is a second ledger API even when the record it reads lives
# elsewhere, so `def`/`abbrev` are checked exactly like `structure`.
#
# Capture every declared name and let `NONCANONICAL_LEDGER` judge it; matching
# the suffix here instead would miss a bare `structure Ledger`.
DECLARES_LEDGER = re.compile(
    r"(?m)^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(structure|inductive|abbrev|def)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)

CARRIER_FORMS = {"structure", "inductive"}


def module_name(path: pathlib.Path) -> str:
    rel = path.relative_to(LIB).with_suffix("")
    return "Hypostructure." + ".".join(rel.parts)


def build_closure() -> set[str]:
    """Modules Lake actually compiles: the root's transitive imports."""
    by_name = {module_name(p): p for p in LIB.rglob("*.lean")}
    imports = re.compile(r"(?m)^\s*import\s+(\S+)")

    def deps(path: pathlib.Path) -> list[str]:
        return imports.findall(path.read_text(errors="ignore"))

    seen: set[str] = set()
    stack = [m for m in deps(ROOT_MODULE) if m in by_name]
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        stack.extend(m for m in deps(by_name[current]) if m in by_name)
    return seen


def main() -> int:
    quarantined = {
        line.strip()
        for line in QUARANTINE.read_text().splitlines()
        if line.strip() and not line.startswith("#")
    }
    live = build_closure()
    by_name = {module_name(p): p for p in LIB.rglob("*.lean")}
    failures: list[str] = []

    leaked = sorted(live & quarantined)
    for module in leaked:
        failures.append(f"quarantined module is back in the build: {module}")

    for module in sorted(live):
        if not module.startswith(CHECKED_PREFIXES):
            continue
        path = by_name[module]
        text = path.read_text(errors="ignore")

        if path != CANONICAL:
            for number, line in enumerate(text.splitlines(), 1):
                if GRAFT.search(line):
                    failures.append(
                        f"{path.relative_to(REPO)}:{number}: declaration grafted "
                        f"into the canonical ledger namespace"
                    )

        if path in CANONICAL_API:
            continue

        for match in DECLARES_LEDGER.finditer(text):
            form, name = match.group(1), match.group(2)
            if not NONCANONICAL_LEDGER.search(name):
                continue
            number = text[: match.start()].count("\n") + 1
            kind = (
                "parallel data carrier"
                if form in CARRIER_FORMS
                else "second ledger API"
            )
            failures.append(
                f"{path.relative_to(REPO)}:{number}: {kind} `{name}` -- the only "
                f"ledger is Core.Residual.ExactLedger and the only accessors are "
                f"the ones it exposes"
            )

    if failures:
        print("canonical-ledger gate: FAIL")
        for failure in failures:
            print(f"  {failure}")
        return 1

    print(
        f"canonical-ledger gate: PASS "
        f"({len(live)} live module(s), {len(quarantined)} quarantined)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

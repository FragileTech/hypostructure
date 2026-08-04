#!/usr/bin/env python3
"""Reject partial outcomes in production Hypostructure execution code.

The check is intentionally narrower than a repository-wide search.  Lean's
`Option` is entirely legitimate in mathematical definitions; only files at
the official execution/compiler boundary are inspected, and only constructs
that encode an unimplemented execution outcome are rejected.

Run without arguments to scan the live production tree.  `--self-test` checks
the positive and negative regression corpus under
`Hypostructure/Fixtures/TotalExecutionGate`.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT / "Hypostructure"
FIXTURE_ROOT = SOURCE_ROOT / "Fixtures" / "TotalExecutionGate"

# These names are framework execution boundaries.  Restricting the scan here
# prevents ordinary mathematical `Option` use in feature files from becoming
# a false positive.
EXECUTION_BASENAMES = {
    "Compiler.lean",
    "DependentExecutor.lean",
    "Execution.lean",
    "ExecutionJson.lean",
    "Executor.lean",
    "Report.lean",
}


@dataclass(frozen=True)
class Rule:
    name: str
    message: str
    pattern: re.Pattern[str]


RULES = (
    Rule(
        "optional-decision",
        "production dispatch must be total; Option (Decision ...) is forbidden",
        re.compile(r"\bOption\s*\(\s*Decision\b", re.MULTILINE),
    ),
    Rule(
        "failed-result",
        "production execution must not expose or construct Result.failed",
        re.compile(
            r"(?:\bResult\s*\.\s*failed\b|"
            r"\|\s*failed\s*\(\s*failure\s*:\s*Failure\s*\)|"
            r"\.\s*failed\b)",
            re.MULTILINE,
        ),
    ),
    Rule(
        "failure-terminal",
        "unsupported/incompatibleJoin/fuelExhausted are compile errors, not outcomes",
        re.compile(
            r"(?:"
            r"\|\s*(?:unsupported|incompatibleJoin|fuelExhausted)\b|"
            r"\.\s*(?:unsupported|incompatibleJoin|fuelExhausted)\b"
            r")",
            re.MULTILINE,
        ),
    ),
    Rule(
        "wildcard-none",
        "a wildcard production dispatcher may not silently return none",
        re.compile(
            r"\|\s*_\s*,\s*_\s*=>\s*(?:exact\s+)?none\b",
            re.MULTILINE,
        ),
    ),
)


def strip_lean_noncode(source: str) -> str:
    """Replace comments and strings with spaces while preserving line breaks."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(source):
        if block_depth:
            if source.startswith("/-", i):
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif source.startswith("-/", i):
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif in_string:
            if source[i] == "\\" and i + 1 < len(source):
                out.extend((" ", " "))
                i += 2
            elif source[i] == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            block_depth = 1
            out.extend((" ", " "))
            i += 2
        elif source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                out.append(" ")
                i += 1
        elif source[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


def findings(path: Path) -> list[tuple[Rule, int, str]]:
    raw = path.read_text(encoding="utf-8")
    code = strip_lean_noncode(raw)
    result: list[tuple[Rule, int, str]] = []
    for rule in RULES:
        for match in rule.pattern.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            excerpt = raw.splitlines()[line - 1].strip()
            result.append((rule, line, excerpt))
    return sorted(result, key=lambda item: (item[1], item[0].name))


def production_files() -> list[Path]:
    files: list[Path] = []
    for domain in ("Core", "Graph", "PDE"):
        domain_root = SOURCE_ROOT / domain
        if not domain_root.exists():
            continue
        for path in domain_root.rglob("*.lean"):
            if "Official" in path.parts and path.name in EXECUTION_BASENAMES:
                files.append(path)
    return sorted(files)


def report(paths: list[Path]) -> int:
    count = 0
    for path in paths:
        for rule, line, excerpt in findings(path):
            count += 1
            relative = path.relative_to(ROOT)
            print(f"{relative}:{line}: {rule.name}: {rule.message}")
            print(f"  {excerpt}")
    if count:
        print(f"total-execution gate: FAIL ({count} forbidden occurrence(s))")
        return 1
    print(f"total-execution gate: PASS ({len(paths)} production file(s) checked)")
    return 0


def self_test() -> int:
    positive = sorted((FIXTURE_ROOT / "positive").glob("*.lean.txt"))
    negative = sorted((FIXTURE_ROOT / "negative").glob("*.lean.txt"))
    expected_negative_rule = {
        "OptionalDecision.lean.txt": "optional-decision",
        "FailedResult.lean.txt": "failed-result",
        "FailureTerminals.lean.txt": "failure-terminal",
        "WildcardDispatcherNone.lean.txt": "wildcard-none",
    }
    failures: list[str] = []
    if not positive or not negative:
        failures.append("fixture corpus must contain positive and negative cases")
    for path in positive:
        found = findings(path)
        if found:
            failures.append(f"positive fixture rejected: {path.name}: {found}")
    for path in negative:
        found_rules = {rule.name for rule, _, _ in findings(path)}
        expected = expected_negative_rule.get(path.name)
        if expected is None:
            failures.append(f"negative fixture has no expected rule: {path.name}")
        elif expected not in found_rules:
            failures.append(
                f"negative fixture {path.name} did not trigger {expected}; "
                f"triggered {sorted(found_rules)}"
            )
    missing = set(expected_negative_rule) - {path.name for path in negative}
    for name in sorted(missing):
        failures.append(f"expected negative fixture is missing: {name}")
    if failures:
        for failure in failures:
            print(f"self-test: {failure}")
        return 1
    print(
        "total-execution gate self-test: PASS "
        f"({len(positive)} positive, {len(negative)} negative)"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run the fixture corpus instead of scanning production",
    )
    args = parser.parse_args()
    return self_test() if args.self_test else report(production_files())


if __name__ == "__main__":
    sys.exit(main())

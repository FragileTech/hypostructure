#!/usr/bin/env python3
"""Static consistency checks for the consolidated Type II manuscript."""

from __future__ import annotations

import re
import sys
from pathlib import Path


TEX = Path(__file__).with_name("type_II_regularity.tex")


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def main() -> int:
    text = TEX.read_text(encoding="utf-8")
    errors: list[str] = []

    # R13 fixes one sign and time convention.  Remove insignificant whitespace
    # and TeX spacing commands before checking so formatting cannot evade it.
    compact = re.sub(r"\\[,;!]", "", text)
    compact = re.sub(r"\s+", "", compact)
    forbidden = {
        r"a(\tau):=-\Lambda'(\tau)": "wrong logarithmic scale coefficient",
        r"b(\tau):=-X'(\tau)": "wrong normalized center coefficient",
        r"d\tau=\Lambda^2dt": "reversed repaired-time law",
        r"\nabla_YV=\Lambda\nabla_xu": "wrong velocity-gradient scaling",
    }
    for pattern, description in forbidden.items():
        if pattern in compact:
            errors.append(f"forbidden formula ({description}): {pattern}")

    label_matches = list(re.finditer(r"\\label\{([^{}]+)\}", text))
    labels: dict[str, list[int]] = {}
    for match in label_matches:
        labels.setdefault(match.group(1), []).append(line_number(text, match.start()))
    for label, lines in sorted(labels.items()):
        if len(lines) != 1:
            errors.append(f"duplicate label {label!r} on lines {lines}")

    reference_pattern = re.compile(
        r"\\(?:[cC]ref|ref|eqref)\{([^{}]+)\}"
    )
    for match in reference_pattern.finditer(text):
        for label in (part.strip() for part in match.group(1).split(",")):
            if label and label not in labels:
                errors.append(
                    f"unresolved reference {label!r} on "
                    f"line {line_number(text, match.start())}"
                )

    obsolete_labels = {
        "paper1:prop:pressure-reconstruction",
        "paper1:eq:represented-ns",
        "paper2:lem:change-id",
        "paper2:thm:ren-NS",
        "paper4:eq:renorm-ns",
        "paper4:thm:caccioppoli",
        "paper6a:lem:repaired-gauge-equation",
        "paper6a:thm:ac-local-caccioppoli",
    }
    for label in sorted(obsolete_labels):
        if label in labels or label in text:
            errors.append(f"superseded proof interface remains: {label}")

    required_labels = {
        "def:canonical-chart-notation",
        "rem:r13-whole-space-norm-scope",
        "paper6a:lem:canonical-final-change-identities",
        "paper6a:thm:canonical-repaired-gauge-equation",
        "paper6a:eq:canonical-repaired-gauge-equation",
        "paper2:thm:pressure-decomp",
        "paper6a:thm:canonical-local-caccioppoli",
        "paper6a:eq:canonical-local-caccioppoli",
        "paper6:def:remaining-named-exits",
    }
    for label in sorted(required_labels):
        if label not in labels:
            errors.append(f"missing canonical R13 interface: {label}")

    edge_pattern = re.compile(
        r"^%\s*R13-LEDGER-EDGE\s+"
        r"(?P<state>[a-z0-9-]+)\s+"
        r"(?P<source_rank>\d+)\s+"
        r"(?P<target_rank>\d+)\s+"
        r"(?P<source_label>[A-Za-z0-9:.-]+)\s*$",
        re.MULTILINE,
    )
    edges = list(edge_pattern.finditer(text))
    expected_states = {
        "bounded-window",
        "autonomous-modulation",
        "noncanonical-cost",
        "active-core-loss",
    }
    states = {edge.group("state") for edge in edges}
    if states != expected_states or len(edges) != len(expected_states):
        errors.append(
            "canonical final ledger must contain exactly the four audited "
            f"states; found {sorted(states)}"
        )
    for edge in edges:
        state = edge.group("state")
        source_rank = int(edge.group("source_rank"))
        target_rank = int(edge.group("target_rank"))
        source_label = edge.group("source_label")
        if source_rank <= target_rank:
            errors.append(
                f"ledger edge {state!r} does not decrease rank: "
                f"{source_rank} -> {target_rank}"
            )
        if source_label not in labels:
            errors.append(
                f"ledger edge {state!r} has missing closure source "
                f"{source_label!r}"
            )
        following_row = text[edge.end() : edge.end() + 1200]
        if source_label not in following_row:
            errors.append(
                f"ledger edge {state!r} is not followed by its declared "
                f"closure source {source_label!r}"
            )

    # A pressure convergence/stability statement must state what happens to
    # the harmonic component, not merely to the Calderon--Zygmund source part.
    statement_pattern = re.compile(
        r"\\begin\{(?P<env>theorem|lemma|proposition|corollary)\}"
        r"(?P<body>.*?)"
        r"\\end\{(?P=env)\}",
        re.DOTALL,
    )
    for match in statement_pattern.finditer(text):
        body = match.group("body")
        body_without_refs = re.sub(
            r"\\(?:[cC]ref|ref|eqref)\{[^{}]+\}", "", body
        )
        title_match = re.match(r"\[([^\]]+)\]", body)
        title = title_match.group(1) if title_match else ""
        title_signal = (
            re.search(r"pressure", title, re.IGNORECASE)
            and re.search(r"converg|stabil", title, re.IGNORECASE)
        )
        pressure_convergence_signal = re.search(
            r"pressure.{0,80}converg"
            r"|converg.{0,80}pressure"
            r"|convergence\s+of\s+"
            r"(?:the\s+)?pressure",
            body_without_refs,
            re.IGNORECASE | re.DOTALL,
        )
        pressure_arrow_signal = re.search(
            r"(?:\\widetilde\s*)?P(?:_\{[^{}]+\}|_[A-Za-z0-9*]+)?"
            r"\s*(?:\\to|\\longrightarrow|\\rightharpoonup)",
            body_without_refs,
        )
        if (
            (title_signal or pressure_convergence_signal or pressure_arrow_signal)
            and not re.search(r"harmonic", body, re.IGNORECASE)
        ):
            errors.append(
                "pressure convergence/stability statement omits its harmonic "
                f"component near line {line_number(text, match.start())}"
            )

    # This scope declaration is the audited rule for every whole-space-looking
    # norm: it distinguishes explicit inputs/scaling identities/zero extensions
    # from the buffered local or local-tail estimates used in the proof.
    scope_start = text.find(r"\label{rem:r13-whole-space-norm-scope}")
    if scope_start >= 0:
        scope = text[scope_start : scope_start + 900].lower()
        for phrase in (
            "explicit",
            "scaling identity",
            "extended by zero",
            "local/tail",
            "no whole-space",
        ):
            if phrase not in scope:
                errors.append(
                    "whole-space norm scope declaration is missing the "
                    f"qualification {phrase!r}"
                )

    whole_space_norms = 0
    whole_space_norm_pattern = re.compile(
        r"L\^(?:\{[^{}\n]+\}|\\[A-Za-z]+|[0-9]+)"
        r"(?:_\{?[^{}\s()]+\}?)?\s*"
        r"\(\s*\\mathbb\s*(?:\{R\}|R)\^3\s*\)"
    )
    for match in whole_space_norm_pattern.finditer(text):
        whole_space_norms += 1
        window = text[
            max(0, match.start() - 1400) : min(len(text), match.end() + 700)
        ].lower()
        qualified = re.search(
            r"\bassume\b|\bsuppose\b|\blet\b|"
            r"\bdefinition\b|\bconvention\b|\bprofile\b|\bisometr|\binvariant|"
            r"calder|riesz|compactly supported|extended by zero|"
            r"local/tail|\btail\b|not require|does not require|"
            r"no whole-space|explicit input|explicit.{0,80}hypothesis",
            window,
        )
        if not qualified:
            errors.append(
                "whole-space-looking norm lacks an explicit-input, scaling, "
                "zero-extension, or local/tail qualification near "
                f"line {line_number(text, match.start())}"
            )

    if errors:
        print(f"{TEX}: R13 static audit failed", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1

    print(
        f"{TEX}: R13 static audit passed "
        f"({len(labels)} unique labels, "
        f"{len(list(reference_pattern.finditer(text)))} reference commands, "
        f"{len(edges)} rank-decreasing final-ledger edges, "
        f"{whole_space_norms} qualified whole-space-looking norms)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

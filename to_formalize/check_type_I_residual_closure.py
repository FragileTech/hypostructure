#!/usr/bin/env python3
"""Structural consistency checks for the Type I residual manuscript.

This script checks source-level interfaces, labels, and dependency order.  It
does not certify any analytic hypothesis and is not part of the proof.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
TEX = ROOT / "type_I_residual_closure.tex"
AUDIT = ROOT / "improvements_to_paper" / (
    "type_I_residual_closure_airtight_repair_blueprint.md"
)
ARCH = ROOT / "overall_proof_architecture.tex"


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def collect_labels(text: str, errors: list[str]) -> dict[str, int]:
    occurrences: dict[str, list[int]] = {}
    for match in re.finditer(r"\\label\{([^{}]+)\}", text):
        occurrences.setdefault(match.group(1), []).append(
            line_number(text, match.start())
        )
    for label, lines in sorted(occurrences.items()):
        if len(lines) != 1:
            errors.append(f"duplicate label {label!r} on lines {lines}")
    return {label: lines[0] for label, lines in occurrences.items()}


def require_order(
    labels: dict[str, int], chain: tuple[str, ...], errors: list[str]
) -> None:
    missing = [label for label in chain if label not in labels]
    if missing:
        errors.append(f"cannot check dependency order; missing {missing}")
        return
    lines = [labels[label] for label in chain]
    if lines != sorted(lines) or len(set(lines)) != len(lines):
        errors.append(
            "dependency declarations are out of order: "
            + " -> ".join(
                f"{label} (line {line})"
                for label, line in zip(chain, lines, strict=True)
            )
        )


def labelled_environment(text: str, label: str, radius: int = 8000) -> str:
    marker = rf"\label{{{label}}}"
    offset = text.find(marker)
    if offset < 0:
        return ""
    return text[max(0, offset - radius) : min(len(text), offset + radius)]


def main() -> int:
    manuscript = TEX.read_text(encoding="utf-8")
    audit = AUDIT.read_text(encoding="utf-8")
    architecture = ARCH.read_text(encoding="utf-8")
    errors: list[str] = []

    labels = collect_labels(manuscript, errors)

    reference_pattern = re.compile(r"\\(?:[cC]ref|ref|eqref)\{([^{}]+)\}")
    reference_count = 0
    for match in reference_pattern.finditer(manuscript):
        reference_count += 1
        for label in (part.strip() for part in match.group(1).split(",")):
            if label and label not in labels:
                errors.append(
                    f"unresolved local reference {label!r} on line "
                    f"{line_number(manuscript, match.start())}"
                )

    required_labels = {
        "tab:typeI-dependency-order",
        "tab:terminal-dependency-table",
        "tab:critical-tail-local-dependency-directory",
        "tab:atomic-endpoint-input-production",
        "tab:terminal-indecomposable-production",
        "tab:final-selected-owner-directory",
        "def:refined-decomposition",
        "thm:R1-exclusion",
        "prop:R2-reduction-to-terminal",
        "cor:R2-closure",
        "prop:R3-stationary-hull-reduction",
        "prop:R3S-R3-terminal-reduction",
        "cor:R3-closure",
        "thm:ancestor-realization-inheritance",
        "thm:descendant-heredity",
        "lem:critical-tail-defect-coordinate-closure",
        "lem:log-window-support-transfer",
        "lem:renormalized-log-window-heredity",
        "cor:coherent-critical-tail-branch-closure",
        "cor:young-branch-exclusion",
        "cor:log-diffuse-branch-exclusion",
        "cor:critical-tail-exclusion-complete",
        "thm:terminal-stratification",
        "thm:generic-terminal-exhaustion",
        "lem:atomic-sequence-L3",
        "thm:mildness-inheritance-main",
        "thm:AB-main",
        "lem:no-atomic-active",
        "thm:R4-final-closure",
        "sec:final-assembly",
        "thm:refined-residual-closure",
        "prop:setup-residual-handoff-complete",
        "thm:typeI-residual-closure",
        "cor:setup-residual-hypothesis-proof",
        "cor:two-paper-local-typeI-exclusion",
    }
    for label in sorted(required_labels):
        if label not in labels:
            errors.append(f"missing required Type I interface {label!r}")

    require_order(
        labels,
        ("prop:R2-reduction-to-terminal", "cor:R2-closure"),
        errors,
    )
    require_order(
        labels,
        (
            "prop:R3-stationary-hull-reduction",
            "prop:R3S-R3-terminal-reduction",
            "cor:R3-closure",
        ),
        errors,
    )
    require_order(
        labels,
        (
            "lem:atomic-sequence-L3",
            "thm:mildness-inheritance-main",
            "thm:AB-main",
            "lem:no-atomic-active",
        ),
        errors,
    )
    require_order(
        labels,
        (
            "thm:R4-final-closure",
            "thm:typeI-residual-closure",
            "cor:setup-residual-hypothesis-proof",
            "cor:two-paper-local-typeI-exclusion",
        ),
        errors,
    )

    protected_tables = {
        "tab:terminal-dependency-table": (
            "thm:terminal-stratification",
            "prop:R2-reduction-to-terminal",
            "prop:R3S-R3-terminal-reduction",
        ),
        "tab:critical-tail-local-dependency-directory": (
            "cor:coherent-critical-tail-branch-closure",
            "cor:young-branch-exclusion",
            "cor:log-diffuse-branch-exclusion",
        ),
        "tab:atomic-endpoint-input-production": (
            "lem:atomic-sequence-L3",
            "thm:mildness-inheritance-main",
            "thm:AB-main",
            "lem:no-atomic-active",
        ),
        "tab:final-selected-owner-directory": (
            "prop:R2-reduction-to-terminal",
            "prop:R3-stationary-hull-reduction",
            "cor:coherent-critical-tail-branch-closure",
            "cor:young-branch-exclusion",
            "cor:log-diffuse-branch-exclusion",
            "thm:R4-final-closure",
            "thm:typeI-residual-closure",
        ),
    }
    for table, tokens in protected_tables.items():
        window = labelled_environment(manuscript, table)
        if not window:
            continue
        for token in tokens:
            if token not in window:
                errors.append(f"{table!r} omits protected entry {token!r}")

    final_directory = labelled_environment(
        manuscript, "tab:final-selected-owner-directory", radius=11000
    )
    for class_macro in (
        r"\Cax",
        r"\Crot",
        r"\Cstat",
        r"\Caff",
        r"\Clogdiff",
        r"\Cyoung",
        r"\Chomcrit",
        r"\Clogper",
        r"\Capcrit",
        r"\Cgen",
    ):
        if class_macro not in final_directory:
            errors.append(
                "final selected-owner directory omits refined class "
                f"{class_macro}"
            )

    implication_markers = (
        r"V\in\calR^\#(\calS;I,J)\quad\Longrightarrow\quad\bot",
        r"V\in\calR_{\rm setup}(\calS)\quad\Longrightarrow\quad\bot",
    )
    for marker in implication_markers:
        if marker not in manuscript:
            errors.append(
                "final assembly does not expose the required pointwise "
                f"implication {marker!r}"
            )

    forbidden_manuscript_phrases = {
        "Assume, for contradiction, that a retained admissible residual "
        "profile exists.": "existential opening of the refined closure",
        "Let \\(V\\) be an arbitrary hypothetical incoming profile in": (
            "membership written as a profile-existence premise"
        ),
        "The positive local velocity concentration inherited by every "
        "normalized Seregin limit": "uniform descendant inheritance claim",
        "Every normalized Seregin limit produced by this extraction": (
            "overbroad normalized-limit ownership claim"
        ),
    }
    for phrase, description in forbidden_manuscript_phrases.items():
        if phrase in manuscript:
            errors.append(f"forbidden prose ({description}): {phrase!r}")

    architecture_required = (
        "prop:R2-reduction-to-terminal",
        "cor:R2-closure",
        "prop:R3-stationary-hull-reduction",
        "prop:R3S-R3-terminal-reduction",
        "cor:R3-closure",
        "cor:coherent-critical-tail-branch-closure",
        "cor:young-branch-exclusion",
        "cor:log-diffuse-branch-exclusion",
        "lem:atomic-sequence-L3",
        "thm:mildness-inheritance-main",
        "thm:AB-main",
        "lem:no-atomic-active",
        "thm:typeI-residual-closure",
        "cor:setup-residual-hypothesis-proof",
        "cor:two-paper-local-typeI-exclusion",
    )
    for label in architecture_required:
        if rf"\path|{label}|" not in architecture:
            errors.append(f"Type I architecture omits {label!r}")

    stale_architecture = (
        "every residual descendant preserves ancestry and retained mass",
    )
    for phrase in stale_architecture:
        if phrase in architecture:
            errors.append(f"stale architecture ownership claim: {phrase!r}")

    audit_required = (
        r"V\in\calR_{\rm setup}(\calS)\Rightarrow\bot",
        "antecedent, not an existence premise",
        "no residual element is postulated",
    )
    for phrase in audit_required:
        if phrase not in audit:
            errors.append(
                "audit does not state the pointwise contrapositive safeguard: "
                f"{phrase!r}"
            )

    if errors:
        print(f"{TEX}: Type I structural audit failed", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1

    print(
        f"{TEX}: Type I structural audit passed "
        f"({len(labels)} unique labels, {reference_count} reference commands, "
        f"{len(required_labels)} required interfaces, "
        f"{len(architecture_required)} synchronized architecture labels)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

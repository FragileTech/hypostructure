#!/usr/bin/env python3
"""Generate and validate the EG skill's compiled Hypostructure API catalog."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


BEGIN = "<!-- BEGIN GENERATED API -->"
END = "<!-- END GENERATED API -->"
SKILL_REL = Path(".agents/skills/eg-proof-expansion")
CATALOG_REL = SKILL_REL / "references/allowed-api.md"

CANONICAL_MODULES = {
    "Hypostructure.Core.Residual.ExactLedger": "Canonical ledger",
    "Hypostructure.Core.Strategy.FactManifest": "Canonical manifest",
    "Hypostructure.Core.Strategy.ExactExecution": "Canonical execution",
    "Hypostructure.Core.Strategy.ProblemResidual": "Canonical residual domain",
    "Hypostructure.Core.Strategy.MinimalCounterexampleScope":
        "Canonical scope initialization",
    "Hypostructure.Core.Strategy.FactOnlyStrategy":
        "Canonical fact-only steps and branch decisions",
    "Hypostructure.Graph.Strategy.SpineVocabulary":
        "Minimum-degree cycle spine vocabulary",
    "Hypostructure.Graph.Strategy.SpineRows":
        "Minimum-degree cycle spine rows",
}

SEALED_TOPOLOGY_PREFIXES = (
    "Hypostructure.Core.Strategy.Dag.Blueprint",
    "Hypostructure.Core.Strategy.Dag.AfterMinimalCounterexampleSelection",
    "Hypostructure.Core.Strategy.Dag.AfterTargetAlgebraReduction",
    "Hypostructure.Core.Strategy.Dag.AfterMinimalSubobjectExclusion",
    "Hypostructure.Core.Strategy.Dag.AfterCriticalModificationStructure",
)

# Any identifier ending in `Ledger` other than the canonical
# `Core.Residual.ExactLedger`.  The exemption is matched against the *whole*
# dotted path, so a namespaced shadow such as
# `SupportComplementNormalization.ExactLedger` is still a parallel carrier and
# is still rejected; only the bare name and its canonical qualifications are
# allowed through.
NONCANONICAL_LEDGER = re.compile(
    r"(?<![\w.])"
    r"(?!(?:Hypostructure\.)?(?:Core\.Residual\.)?ExactLedger\b)"
    r"(?:[A-Za-z_][A-Za-z0-9_']*\.)*"
    r"[A-Za-z0-9_']*Ledger\b"
)

FORBIDDEN_TYPE_PATTERNS = (
    re.compile(r"(?:^|\.)Core\.Residual\.Ledger(?:\.|\b)"),
    re.compile(r"(?:^|\.)Core\.Residual\.Query(?:\.|\b)"),
    re.compile(r"\bHasResidual\b"),
    re.compile(r"\bCapabilityStore\b"),
    re.compile(r"\bCapabilityFlow\b"),
    NONCANONICAL_LEDGER,
)

FORBIDDEN_PROOF_SOURCE = {
    "legacy residual ledger": re.compile(r"\bCore\.Residual\.Ledger\b"),
    "legacy residual query": re.compile(r"\bCore\.Residual\.Query\b"),
    "legacy residual instance": re.compile(r"\bHasResidual\b"),
    "parallel capability store": re.compile(r"\bCapabilityStore\b"),
    "parallel capability flow": re.compile(r"\bCapabilityFlow\b"),
    "noncanonical ledger type": NONCANONICAL_LEDGER,
    "direct ledger append": re.compile(r"\bExactLedger\.append\b"),
    "direct one-fact publication": re.compile(r"\bExactLedger\.publishFact\b"),
    "history reset": re.compile(r"\bExactLedger\.root\b"),
    "direct history transport": re.compile(r"\bExactLedger\.refine\b"),
    "direct scope initialization": re.compile(r"\bExactLedger\.initializeScope\b"),
    "framework authority type": re.compile(r"\bFrameworkToken\b"),
    "framework authority syntax": re.compile(r"\bexactLedgerInternal%"),
    "direct history-index access": re.compile(
        r"\bExactLedger\.materialize\b"
    ),
    "direct CT construction": re.compile(r"\bAtomicCT\.create\b"),
    "direct Strategy construction": re.compile(r"\bAtomicStrategy\.create\b"),
    "manual input extraction": re.compile(r"\bFactInputs\.ofLedger\b"),
    "opened framework construction namespace": re.compile(
        r"(?m)^\s*open(?:\s+scoped)?[^\n]*(?:ExactLedger|AtomicCT|FactInputs)\b"
    ),
    "raw manifest routing": re.compile(r"\bFactManifest\.(?:missing|ready)\b"),
    "raw route ordering": re.compile(r"\bRoutedTask\.(?:authoredOrder|preferred)\b"),
    "parallel product wrapper": re.compile(r"\b(?:Prod|Sigma|PSigma)\b"),
    "unfinished proof": re.compile(r"\b(?:sorry|admit)\b"),
}

FORBIDDEN_DAG_DECLARATION = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:structure|class|inductive|def|abbrev|opaque|theorem|lemma|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
)

ALLOWED_DAG_DECLARATIONS = {"strategyDag"}

# The closed presentation surface of `Problem.lean`.  Each entry is either the
# problem/target registration itself or a registered datum that genuinely
# cannot be derived from the incoming residual: a presentation parameter, a
# threshold the argument chooses, or the record of them the framework's entry
# spine reads.  No theorem, strategy, executor, or ledger operation may be
# added here -- those belong to the framework.
ALLOWED_PROBLEM_DECLARATIONS = {
    "erdosReceiverLoadProfile",
    "Baseline",
    "BranchState",
    "problem",
    "OfficialStatement",
    "Target",
    "target",
    # Registered constants of the presentation.
    "surplusScaleCoefficient",
    "surplusScaleThreshold",
    "nodeThirtyTwoRankAllowance",
    # The registered data record the entry spine reads.
    "spineData",
}

PROOF_BOUNDARY_FILES = (
    "proofs/hypostructure_erdos_64_eg/"
    "HypostructureErdos64EG/Problem.lean",
    "proofs/hypostructure_erdos_64_eg/"
    "HypostructureErdos64EG/StrategyDag.lean",
)

PROOF_TREE = Path("proofs/hypostructure_erdos_64_eg")

FORBIDDEN_PROOF_TREE = {
    label: pattern
    for label, pattern in FORBIDDEN_PROOF_SOURCE.items()
    if label != "unfinished proof"
}

REQUIRED_CANONICAL_DECLARATIONS = {
    "Hypostructure.Core.Residual.ExactLedger",
    "Hypostructure.Core.Residual.ExactLedger.audit",
    "Hypostructure.Core.Residual.ExactLedger.audit_commits_nonempty",
    "Hypostructure.Core.Residual.ExactLedger.audit_complete",
    "Hypostructure.Core.Residual.ExactLedger.audit_facts_unique",
    "Hypostructure.Core.Residual.ExactLedger.currentOf",
    "Hypostructure.Core.Residual.ExactLedger.get",
    "Hypostructure.Core.Residual.ExactLedger.getPresent",
    "Hypostructure.Core.Residual.AuditSnapshot",
    "Hypostructure.Core.Residual.CommitRecord",
    "Hypostructure.Core.Residual.FactSystem",
    "Hypostructure.Core.Residual.FactKey",
    "Hypostructure.Core.Residual.FactKeys",
    "Hypostructure.Core.Residual.FactKeys.Has",
    "Hypostructure.Core.Strategy.FactManifest",
    "Hypostructure.Core.Strategy.FactInputs",
    "Hypostructure.Core.Strategy.FactInputs.get",
    "Hypostructure.Core.Strategy.AtomicCT",
    "Hypostructure.Core.Strategy.AtomicCT.outputResidual",
    "Hypostructure.Core.Strategy.AtomicCT.run",
    "Hypostructure.Core.Strategy.AtomicStrategy",
    "Hypostructure.Core.Strategy.RoutedTask.selectFor",
    "Hypostructure.Core.Strategy.RoutedTask.dispatchFor",
}

FRAMEWORK_ONLY_DECLARATIONS = {
    "Hypostructure.Core.Residual.FrameworkToken",
    "Hypostructure.Core.Residual.ExactLedger.root",
    "Hypostructure.Core.Residual.ExactLedger.append",
    "Hypostructure.Core.Residual.ExactLedger.refine",
    "Hypostructure.Core.Residual.ExactLedger.initializeScope",
    "Hypostructure.Core.Residual.ExactLedger.publishFact",
    "Hypostructure.Core.Strategy.FactInputs.ofLedger",
    "Hypostructure.Core.Strategy.AtomicCT.create",
}

INTERNAL_PROJECTION_DECLARATIONS = {
    "Hypostructure.Core.Residual.FactKeys.Member.ofMem",
    "Hypostructure.Core.Residual.FactKeys.Values.get",
    "Hypostructure.Core.Residual.FactKeys.Values.getAt",
    "Hypostructure.Core.Strategy.FactKeys.Available.values",
    "Hypostructure.Core.Strategy.FactManifest.missing",
    "Hypostructure.Core.Strategy.FactManifest.missingKeys",
    "Hypostructure.Core.Strategy.FactManifest.ready",
    "Hypostructure.Core.Strategy.RoutedTask.authoredOrder",
    "Hypostructure.Core.Strategy.RoutedTask.preferred",
}

FRAMEWORK_ONLY_TYPE_REFERENCES = tuple(
    name.removeprefix("Hypostructure.")
    for name in FRAMEWORK_ONLY_DECLARATIONS
)

GENERATED_SUFFIXES = (
    ".rec",
    ".recOn",
    ".casesOn",
    ".below",
    ".brecOn",
    ".noConfusion",
    ".noConfusionType",
    ".ctorIdx",
)

GENERATED_NAME_PARTS = (
    ".brecOn.",
    ".ctorElim",
    ".elim",
    ".inj",
    ".injEq",
    ".match_",
    ".sizeOf_spec",
    ".eq_",
)


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
        name = str(declaration["name"])
        if module in CANONICAL_MODULES:
            category = CANONICAL_MODULES[module]
        elif module == "Hypostructure.Core.Strategy.Dag" and name.startswith(
            SEALED_TOPOLOGY_PREFIXES
        ):
            category = "Sealed topology"
        else:
            continue

        kind = str(declaration["kind"])
        if name in FRAMEWORK_ONLY_DECLARATIONS or name in INTERNAL_PROJECTION_DECLARATIONS:
            continue
        if "._" in name or name.endswith(GENERATED_SUFFIXES):
            continue
        if any(part in name for part in GENERATED_NAME_PARTS):
            continue
        if (
            category == "Sealed topology"
            and kind == "constructor"
            and name != "Hypostructure.Core.Strategy.Dag.Blueprint.root"
        ):
            continue

        declaration_type = str(declaration["type"])
        if name not in REQUIRED_CANONICAL_DECLARATIONS and any(
            forbidden in declaration_type
            for forbidden in FRAMEWORK_ONLY_TYPE_REFERENCES
        ):
            continue
        if any(
            pattern.search(declaration_type)
            for pattern in FORBIDDEN_TYPE_PATTERNS
        ):
            continue
        if "Ledger" in name and "ExactLedger" not in name:
            continue
        declarations.append(
            {
                "name": name,
                "kind": kind,
                "type": declaration_type,
                "module": module,
                "source_file": str(declaration["source_file"]),
                "category": category,
            }
        )
    declarations.sort(key=lambda item: str(item["name"]))
    if not declarations:
        fail("compiled API filter selected no declarations")
    names = {str(item["name"]) for item in declarations}
    missing = sorted(REQUIRED_CANONICAL_DECLARATIONS - names)
    if missing:
        fail("canonical API export is missing: " + ", ".join(missing))
    return declarations


def check_proof_boundary(root: Path) -> None:
    violations: list[str] = []
    for path in sorted((root / PROOF_TREE).rglob("*.lean")):
        relative_to_tree = path.relative_to(root / PROOF_TREE)
        if any(part.startswith(".") for part in relative_to_tree.parts):
            continue
        source = path.read_text(encoding="utf-8")
        for label, pattern in FORBIDDEN_PROOF_TREE.items():
            for match in pattern.finditer(source):
                line = source.count("\n", 0, match.start()) + 1
                violations.append(f"{path.relative_to(root)}:{line}: {label}")

    for relative in PROOF_BOUNDARY_FILES:
        path = root / relative
        source = path.read_text(encoding="utf-8")
        unfinished = FORBIDDEN_PROOF_SOURCE["unfinished proof"]
        for match in unfinished.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            violations.append(
                f"{path.relative_to(root)}:{line}: unfinished proof"
            )

        if path.name == "StrategyDag.lean":
            for match in FORBIDDEN_DAG_DECLARATION.finditer(source):
                if match.group("name") in ALLOWED_DAG_DECLARATIONS:
                    continue
                line = source.count("\n", 0, match.start()) + 1
                violations.append(
                    f"{path.relative_to(root)}:{line}: "
                    "application-local helper declaration"
                )
        elif path.name == "Problem.lean":
            for match in FORBIDDEN_DAG_DECLARATION.finditer(source):
                if match.group("name") in ALLOWED_PROBLEM_DECLARATIONS:
                    continue
                line = source.count("\n", 0, match.start()) + 1
                violations.append(
                    f"{path.relative_to(root)}:{line}: "
                    "non-presentation problem declaration"
                )
    if violations:
        fail("noncanonical EG proof plumbing:\n" + "\n".join(violations))


def check_canonical_sources(root: Path) -> None:
    paths = (
        root / "hypostructure/Hypostructure/Core/Residual/ExactLedger.lean",
        root / "hypostructure/Hypostructure/Core/Strategy/FactManifest.lean",
        root / "hypostructure/Hypostructure/Core/Strategy/ExactExecution.lean",
    )
    forbidden = (
        "Core.Residual.Ledger",
        "Core.Residual.Query",
        "HasResidual",
        "CapabilityStore",
        "CapabilityFlow",
    )
    violations = []
    for path in paths:
        source = path.read_text(encoding="utf-8")
        for token in forbidden:
            if token in source:
                violations.append(f"{path.relative_to(root)}: contains {token}")
    if violations:
        fail("canonical API depends on legacy transport:\n" + "\n".join(violations))

    obsolete_paths = (
        root / "hypostructure/Hypostructure/Core/Residual/ExactLedger.lean",
        root / "hypostructure/Hypostructure/Core/Strategy/FactManifest.lean",
        root / "hypostructure/Hypostructure/Core/Strategy/ExactExecution.lean",
        root / "hypostructure/Hypostructure/Core/Strategy/Dag.lean",
    )
    obsolete = (
        "CapabilityStore",
        "CapabilityFlow",
        "ManifestFlow",
        "ExactLedger.rebase",
        "allFacts",
    )
    violations = []
    for path in obsolete_paths:
        # A canonical source deleted by the rewrite cannot reintroduce obsolete
        # transport; only the modules that still exist are scanned.
        if not path.exists():
            continue
        source = path.read_text(encoding="utf-8")
        for token in obsolete:
            if token in source:
                violations.append(f"{path.relative_to(root)}: contains {token}")
    if violations:
        fail("obsolete proof transport was reintroduced:\n" + "\n".join(violations))

    deleted_modules = (
        root
        / "hypostructure/Hypostructure/Core/Strategy/Official/CapabilityFlow.lean",
        root / "hypostructure/Hypostructure/Fixtures/OfficialCapabilityFlow.lean",
    )
    present = [str(path.relative_to(root)) for path in deleted_modules if path.exists()]
    if present:
        fail("deleted parallel-ledger modules were restored: " + ", ".join(present))


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
    check_canonical_sources(root)
    check_proof_boundary(root)
    path, expected = expected_document(root)
    path.write_text(expected, encoding="utf-8")
    print(f"refreshed {path.relative_to(root)}")


def check(root: Path) -> None:
    check_canonical_sources(root)
    check_proof_boundary(root)
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

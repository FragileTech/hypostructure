"""Deterministic tests for the EG red-team skill tooling."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_modular_hit import audit_spec
from red_team_node import (
    VERDICTS,
    GraphContext,
    campaign_status,
    discover_repo_root,
    init_campaign,
    record_report,
    sync_campaign,
    validate_report,
)


def fixture_report(context: GraphContext, node_id: str = "1") -> str:
    dossier = context.dossier(node_id)
    node = dossier["node"]
    sources = dossier["source_fingerprints"]
    metadata = {
        "schema_version": 1,
        "proof": "erdos-gyarfas",
        "node": int(node_id),
        "node_label": node["label"],
        "panel": node["group"],
        "contract_sha256": dossier["contract_sha256"],
        "manuscript_sha256": sources["manuscript_sha256"],
        "graph_sha256": sources["graph_sha256"],
        "lean_audit_sha256": sources["lean_audit_sha256"],
        "verdict": "NO ISSUE FOUND",
        "audited_at": "2026-08-24T12:00:00Z",
    }
    attempts = []
    for heading in (
        "Smallest-parameter test",
        "Parity or 2-adic test",
        "Boundary or range test",
        "Graph-realizability test",
        "Branch-routing test",
    ):
        attempts.append(
            f"""### {heading}

- **Explicit data:** A concrete fixture with the smallest admissible values.
- **Hypotheses satisfied:** The explicit local hypotheses used in this fixture.
- **Accumulated facts violated:** None; this fixture is a validator test only.
- **Applicability:** NON-APPLICABLE TO THE NODE because this is not a mathematical campaign report.
"""
        )
    return f"""<!-- red-team-audit
{json.dumps(metadata, ensure_ascii=False, indent=2)}
-->
# Red-team audit: node [{int(node_id)}]

## 1. Executive verdict

Verdict: **NO ISSUE FOUND**

The structural fixture exercises the report contract and deliberately makes no theorem-wide claim.

## 2. Exact node contract

### Incoming residual

The exact incoming residual would be reconstructed from the manuscript sources.

### Accumulated facts

All path facts would be listed with their source labels and route tags.

### Current predicate and exact claim

The exact implication would preserve its quantifiers and current branch predicate.

### Outgoing contracts

Every outgoing destination would be checked against its complete entry contract.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | Fixture assertion | Fixture facts | Complete report shape | Structural validation | SUPPORTED |

## 4. Counterexample attempts

{''.join(attempts)}
## 5. Strongest valid counterexample

No candidate reaches the actual residual because this is a tooling fixture, not a mathematical audit.

## 6. Local repair

### Corrected statement

No proof-source change required; the tooling fixture states no manuscript claim.

### Complete local proof

Not applicable to the structural validator fixture, whose assertions are checked directly.

### Counterexample disposition

All fixture candidates are non-mathematical and therefore do not reach the residual.

### Graph patch

No graph patch is proposed or applied by this structural validator fixture.

### Downstream impact

No downstream theorem, table, caption, analogue, or Lean contract is affected.

## 7. Regression audit

No manuscript label is corrected, so the regression search has an empty target set.

## 8. Residual uncertainty

This fixture validates report structure only and makes no claim about mathematical correctness.
"""


class GraphTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.root = discover_repo_root(Path.cwd())
        cls.context = GraphContext(cls.root)

    def test_live_graph_shape(self) -> None:
        self.assertEqual(len(self.context.nodes), 180)
        self.assertEqual(len(self.context.incoming["1"]), 0)
        self.assertEqual(len(self.context.outgoing["180"]), 0)
        self.assertEqual(self.context.nodes["180"]["shape"], "terminal")
        self.assertIn("graph_drift", self.context.source_fingerprints)

    def test_merge_routes_are_tagged_separately(self) -> None:
        dossier = self.context.dossier("65")
        self.assertEqual(
            {route["edge"]["source"] for route in dossier["route_alternatives"]},
            {"64", "66", "177"},
        )
        self.assertIn(
            "144",
            {candidate["source"]["id"] for candidate in dossier["unwired_routing_candidates"]},
        )

    def test_type_a_loop_is_exposed(self) -> None:
        dossier = self.context.dossier("102")
        self.assertEqual(
            dossier["loop_context"]["members"],
            ["89", "93", "94", "95", "97", "99", "101", "102"],
        )
        self.assertTrue(dossier["loop_context"]["requires_decreasing_measure"])

    def test_report_validation_and_campaign_record(self) -> None:
        with tempfile.TemporaryDirectory(prefix="eg-red-team-test-") as temp:
            campaign = Path(temp)
            init_campaign(self.context, campaign)
            report = campaign / "reports/node-001.md"
            report.write_text(fixture_report(self.context), encoding="utf-8")
            metadata = validate_report(report, self.context)
            self.assertIn(metadata["verdict"], VERDICTS)
            record_report(self.context, campaign, report)
            status = campaign_status(self.context, campaign)
            self.assertEqual(status["counts"], {"audited": 1, "pending": 179})
            self.assertEqual(status["verdicts"], {"NO ISSUE FOUND": 1})

    def test_stale_contract_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory(prefix="eg-red-team-test-") as temp:
            report = Path(temp) / "node-001.md"
            text = fixture_report(self.context).replace(
                self.context.contract_sha256("1"), "0" * 64, 1
            )
            report.write_text(text, encoding="utf-8")
            with self.assertRaisesRegex(Exception, "stale or incorrect contract_sha256"):
                validate_report(report, self.context)

    def test_campaign_marks_recorded_contract_drift_stale(self) -> None:
        with tempfile.TemporaryDirectory(prefix="eg-red-team-test-") as temp:
            campaign = Path(temp)
            ledger_path = init_campaign(self.context, campaign)
            ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
            ledger["nodes"]["1"]["recorded_contract_sha256"] = "0" * 64
            ledger_path.write_text(json.dumps(ledger), encoding="utf-8")
            synced = sync_campaign(self.context, campaign)
            self.assertEqual(synced["nodes"]["1"]["status"], "stale")
            self.assertEqual(campaign_status(self.context, campaign)["counts"]["stale"], 1)

    def test_campaign_marks_global_source_drift_stale(self) -> None:
        with tempfile.TemporaryDirectory(prefix="eg-red-team-test-") as temp:
            campaign = Path(temp)
            ledger_path = init_campaign(self.context, campaign)
            report = campaign / "reports/node-001.md"
            report.write_text(fixture_report(self.context), encoding="utf-8")
            record_report(self.context, campaign, report)
            ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
            ledger["nodes"]["1"]["source_fingerprints"]["manuscript_sha256"] = "0" * 64
            ledger_path.write_text(json.dumps(ledger), encoding="utf-8")
            self.assertEqual(campaign_status(self.context, campaign)["counts"]["stale"], 1)

    def test_second_executive_verdict_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory(prefix="eg-red-team-test-") as temp:
            report = Path(temp) / "node-001.md"
            text = fixture_report(self.context).replace(
                "The structural fixture exercises",
                "Verdict: **PROSE AMBIGUITY**\n\nThe structural fixture exercises",
                1,
            )
            report.write_text(text, encoding="utf-8")
            with self.assertRaisesRegex(Exception, "exactly one bold Verdict line"):
                validate_report(report, self.context)


class ModularTests(unittest.TestCase):
    def test_two_adic_compatibility_and_range_are_separate(self) -> None:
        result = audit_spec(
            {
                "g": 12,
                "L": 0,
                "k_min": 0,
                "k_max": 6,
                "C_sys": 1,
                "residues": [
                    {"r": 1, "T_r": 20},
                    {"r": 4, "T_r": 20},
                    {"r": -8, "T_r": 1},
                ],
            }
        )
        incompatible, valid, out_of_range = result["residue_audits"]
        self.assertFalse(incompatible["two_adic_compatible"])
        self.assertTrue(incompatible["raw_odd_part_hit_exponents"])
        self.assertFalse(incompatible["odd_part_hit_exponents"])
        self.assertTrue(valid["valid_direct_hits"])
        self.assertTrue(out_of_range["exact_full_modulus_lifts"])
        self.assertFalse(out_of_range["valid_direct_hits"])


if __name__ == "__main__":
    unittest.main()

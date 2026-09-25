"""Residual-first task contracts; these fixtures do not certify mathematics."""
import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from tools.methodology_gate import taskflow as t


class TaskflowTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.proof = self.root / "proof.md"
        self.proof.write_text("Accepted fixture evidence about the same retained object.\n")
        self.state = t.fresh(dict(id="B", revision="r1", source_revision="commit-1",
            endpoint="B implies False", incoming="producer P, arm A", objects=["the actual G"],
            minimality="vertex count on G", imports=[], accounts=[], open_outcomes=["root"]))
        for kind in t.POLICY["phase_zero"]["tasks"]:
            name = "phase0-" + kind
            self.task(name, 0, kind, move_id="")
            self.accept(name)

    def ref(self):
        return dict(path="proof.md", sha256=hashlib.sha256(self.proof.read_bytes()).hexdigest(),
                    locator="line 1")

    def task(self, name, phase, kind, deps=(), **changes):
        contract = dict(id=name, mode="DISCOVER", phase=str(phase), branch_revision="r1",
            move_id="m", kind=kind, goal=f"Prove {name} on the retained G",
            objects=["the actual G"], reads=["branch:r1", "proof.md"],
            interaction="degree bound with overlap", parent_payoff="local restriction",
            depends_on=list(deps), allowed_write="proof.md", acceptance="two cited reviews",
            on_failure="name first missing inference")
        contract.update(changes)
        t.add_task(self.state, contract)
        return contract

    def result(self, status="SUBMITTED_RESULT"):
        return dict(status=status, output="The stated local inference on G",
                    evidence=[self.ref()], implementation_status="none",
                    first_missing_inference="" if status == "SUBMITTED_RESULT" else "unproved transport",
                    immediate_subobligations=[] if status == "SUBMITTED_RESULT" else ["prove transport"],
                    metadata=dict(structural_use=None, interaction=None, changed_objects=[],
                                  changed_accounts=[], side_observations=[]))

    def accept(self, name):
        t.submit(self.state, name, self.result(), self.root)
        for reviewer in ("A", "B"):
            t.review(self.state, name, dict(reviewer=reviewer, decision="accept",
                reason="Checked the fixture inference on the stated object", evidence=[self.ref()]), self.root)

    def move_inputs(self):
        self.task("payoff", 5, "prove_conditional_inference")
        self.task("coverage", 6, "check_coverage", ["payoff"])
        self.task("arm", 7, "record_advancement", ["coverage"])
        for name in ("payoff", "coverage", "arm"):
            self.accept(name)

    def test_dispatch_and_acceptance_require_current_benchmark(self):
        for stamp in (None, "0" * 64):
            state = copy.deepcopy(self.state)
            if stamp is None:
                state.pop("benchmark_policy_sha256")
            else:
                state["benchmark_policy_sha256"] = stamp
            with self.assertRaisesRegex(t.TaskError, "current benchmark policy"):
                t.next_task(state, self.root)
            with self.assertRaisesRegex(t.TaskError, "current benchmark policy"):
                t.submit(state, next(iter(state["tasks"])), self.result(), self.root)

    def test_policy_content_change_invalidates_dispatch(self):
        from unittest.mock import patch
        with patch.object(t, "benchmark_fingerprint", return_value="1" * 64):
            with self.assertRaisesRegex(t.TaskError, "current benchmark policy"):
                t.next_task(self.state, self.root)

    def test_phase_zero_requires_exact_snapshot_and_task_is_narrow(self):
        with self.assertRaises(t.TaskError):
            t.fresh({"id": "B"})
        self.task("pin", 0, "pin_source_revision", move_id="")
        with self.assertRaises(t.TaskError):
            self.task("bad", 2, "prove_conditional_inference")
        self.assertEqual(t.next_task(self.state)["task"]["id"], "pin")

    def test_future_phase_waits_for_reviewed_phase_zero(self):
        branch = copy.deepcopy(self.state["branch"])
        state = t.fresh(branch)
        contract = self.task("future", 2, "register_interaction")
        t.add_task(state, contract)
        self.assertIsNone(t.next_task(state)["task"])
        self.assertIn("Phase 0 tasks required", t.next_task(state)["diagnostic"])

    def test_correct_but_irrelevant_lemma_is_only_atomic_work(self):
        self.task("lemma", 6, "prove_property")
        self.accept("lemma")
        self.assertEqual(t.summary(self.state)["atomic_tasks"]["accepted"], 7)
        self.assertEqual(t.summary(self.state)["productive_moves"], 0)
        self.assertEqual(self.state["branch_status"], "open")

    def test_joint_contradiction_schedules_integration_before_exploration(self):
        self.task("bound", 6, "prove_property")
        self.task("overlap", 6, "prove_property")
        self.task("explore", 3, "select_tension")
        self.task("integrate", 7, "review_integration", ["bound", "overlap"])
        self.accept("bound")
        self.accept("overlap")
        self.assertEqual(t.next_task(self.state)["task"]["id"], "integrate")
        with self.assertRaises(t.TaskError):
            t.submit(self.state, "explore", self.result(), self.root)
        self.accept("integrate")
        self.assertEqual(t.next_task(self.state)["task"]["id"], "explore")

    def test_integration_chain_uses_transitive_dependencies(self):
        self.task("new-fact", 6, "prove_property")
        self.task("link", 7, "relate_new_and_retained", ["new-fact"])
        self.task("review-link", 7, "review_integration", ["link"])
        self.task("explore", 3, "select_tension")
        self.accept("new-fact")
        self.assertEqual(t.next_task(self.state)["task"]["id"], "link")
        self.accept("link")
        self.assertEqual(t.next_task(self.state)["task"]["id"], "review-link")
        self.accept("review-link")
        self.assertEqual(t.next_task(self.state)["task"]["id"], "explore")

    def test_old_bound_can_support_new_interaction_without_new_ledger(self):
        self.task("used", 1, "record_prior_use")
        self.task("new-link", 2, "register_interaction", ["used"])
        self.accept("used")
        self.assertEqual(t.next_task(self.state)["task"]["id"], "new-link")
        result = self.result()
        result["metadata"]["interaction"] = dict(object="G", ingredients=["degree bound", "overlap"],
            relation="both constrain the same marked family", known="each holds separately",
            unresolved="which overlaps remain", domains="marked family in G",
            previous_use="degree bound used only for total count")
        t.submit(self.state, "new-link", result, self.root)
        for reviewer in ("A", "B"):
            t.review(self.state, "new-link", dict(reviewer=reviewer, decision="accept",
                reason="Checked the same-object relation", evidence=[self.ref()]), self.root)
        self.assertEqual(len(self.state["interactions"]), 1)

    def test_finite_table_survivor_and_closed_sibling_leave_parent_open(self):
        self.move_inputs()
        self.task("payoff2", 5, "prove_conditional_inference")
        self.task("arm2", 7, "record_advancement", ["coverage"])
        self.accept("payoff2")
        self.accept("arm2")
        self.task("continuation", 7, "name_next_obligation", ["arm"])
        move = dict(id="m", branch_revision="r1", source_outcome="root",
            selected_conflict="degree and overlap on G", textbook_statement="local counting inequality",
            prerequisites=[], construction_tasks=["coverage"],
            conditional_payoff_tasks=["payoff", "payoff2"], coverage_task="coverage", outcomes=[
                dict(id="small-closed", payoff_task="payoff", task="arm", status="closed", advancement="closure",
                     survivor="", continuation=""),
                dict(id="table-survivor", payoff_task="payoff2", task="arm2", status="open_survivor",
                     advancement="constraint_restriction", survivor="full B plus exact table row 2",
                     continuation="continuation")])
        t.certify_move(self.state, move, self.root)
        self.assertEqual(self.state["branch"]["open_outcomes"], ["table-survivor"])
        with self.assertRaises(t.TaskError):
            t.close_branch(self.state, dict(task="arm", endpoint="B implies False",
                                            composition_tasks=[], direct_closure_tasks={}), self.root)

    def test_already_evidenced_contradiction_uses_fast_path(self):
        self.task("direct", 7, "test_constraint", move_id="")
        self.task("verify", 8, "check_composition", ["direct"], move_id="")
        self.accept("direct")
        self.accept("verify")
        t.close_branch(self.state, dict(task="verify", endpoint="B implies False",
            composition_tasks=[], direct_closure_tasks={"root": "direct"}), self.root)
        self.assertEqual(self.state["branch_status"], "closed")

    def test_missing_prerequisite_never_becomes_assumption(self):
        self.task("candidate", 4, "match_prerequisite")
        t.submit(self.state, "candidate", self.result("NEEDS_DECOMPOSITION"), self.root)
        with self.assertRaises(t.TaskError):
            t.review(self.state, "candidate", dict(reviewer="A", decision="accept",
                reason="No actual premise", evidence=[self.ref()]), self.root)
        self.assertNotEqual(self.state["tasks"]["candidate"]["status"], "accepted")

    def test_representation_change_requires_scheduled_transport_check(self):
        self.task("change", 6, "define_object")
        result = self.result(); result["metadata"]["changed_objects"] = ["represented G as H"]
        result["metadata"]["changed_accounts"] = ["capacity ledger on H"]
        t.submit(self.state, "change", result, self.root)
        for reviewer in ("A", "B"):
            t.review(self.state, "change", dict(reviewer=reviewer, decision="accept",
                reason="Checked actual representation", evidence=[self.ref()]), self.root)
        self.assertIn("Transport check required", t.next_task(self.state)["diagnostic"])
        self.task("transport", 1, "check_transport", ["change"])
        self.assertEqual(t.next_task(self.state)["task"]["id"], "transport")
        self.accept("transport")
        self.assertIn("Account reconciliation required", t.next_task(self.state)["diagnostic"])
        self.task("reconcile", 7, "reconcile_account", ["change", "transport"])
        self.assertEqual(t.next_task(self.state)["task"]["id"], "reconcile")
        self.accept("reconcile")
        self.assertIn("Integration task required", t.next_task(self.state)["diagnostic"])

    def test_bound_on_local_family_is_progress_but_not_branch_closure(self):
        self.move_inputs()
        self.task("next-local", 7, "name_next_obligation", ["arm"])
        t.certify_move(self.state, dict(id="m", branch_revision="r1", source_outcome="root",
            selected_conflict="degree and overlap on G", textbook_statement="local counting inequality",
            prerequisites=[], construction_tasks=["coverage"],
            conditional_payoff_tasks=["payoff"], coverage_task="coverage", outcomes=[dict(
                id="bounded-family", payoff_task="payoff", task="arm", status="open_survivor",
                advancement="quantitative_restriction", survivor="B and marked family size <= 7",
                continuation="next-local")]), self.root)
        self.assertEqual(t.summary(self.state)["productive_moves"], 1)
        self.assertEqual(t.summary(self.state)["branch_status"], "open")

    def test_stale_payoff_revokes_move_and_restores_source_outcome(self):
        self.move_inputs()
        t.certify_move(self.state, dict(id="m", branch_revision="r1", source_outcome="root",
            selected_conflict="degree and overlap on G", textbook_statement="local counting inequality",
            prerequisites=[], construction_tasks=["coverage"],
            conditional_payoff_tasks=["payoff"], coverage_task="coverage", outcomes=[dict(
                id="closed-arm", payoff_task="payoff", task="arm", status="closed",
                advancement="closure", survivor="", continuation="")]), self.root)
        self.assertEqual(self.state["branch"]["open_outcomes"], [])
        self.proof.write_text("Revised proof artifact.\n")
        t.retry(self.state, "payoff", self.root)
        self.assertEqual(self.state["moves"], {})
        self.assertEqual(self.state["branch"]["open_outcomes"], ["root"])

    def test_stale_evidence_blocks_use(self):
        self.task("fact", 2, "register_interaction")
        self.task("consumer", 3, "select_tension", ["fact"])
        self.accept("fact")
        self.accept("consumer")
        self.proof.write_text("Changed source.\n")
        self.assertIn("Repair stale evidence", t.next_task(self.state, self.root)["diagnostic"])
        t.retry(self.state, "fact", self.root)
        self.assertEqual(self.state["tasks"]["consumer"]["status"], "pending")
        self.assertEqual(len(self.state["tasks"]["fact"]["history"]), 1)

    def test_reviewed_construction_preserves_pinned_source_evidence(self):
        self.task("old-source", 2, "register_interaction")
        self.accept("old-source")
        old_ref = self.ref()
        archive = self.root / "tools" / "methodology_gate" / "evidence_snapshots"
        archive.mkdir(parents=True)
        (archive / old_ref["sha256"]).write_bytes(self.proof.read_bytes())
        self.proof.write_text("Kernel-checked construction on the same object.\n")
        self.assertIn("old-source", t.stale_tasks(self.state, self.root))
        self.task("construction", 6, "prove_property", deps=["old-source"])
        result = self.result()
        result["implementation_status"] = "kernel_checked"
        t.submit(self.state, "construction", result, self.root)
        for reviewer in ("C", "D"):
            t.review(self.state, "construction", dict(reviewer=reviewer,
                decision="accept", reason="Checked the current source and construction",
                evidence=[self.ref()]), self.root)
        self.assertEqual(t.stale_tasks(self.state, self.root), [])
        self.proof.write_text("Unreviewed edit after construction.\n")
        self.assertIn("old-source", t.stale_tasks(self.state, self.root))

    def test_reviewed_phase_seven_proof_preserves_pinned_source_evidence(self):
        self.task("old-source", 2, "register_interaction")
        self.accept("old-source")
        old_ref = self.ref()
        archive = self.root / "tools" / "methodology_gate" / "evidence_snapshots"
        archive.mkdir(parents=True)
        (archive / old_ref["sha256"]).write_bytes(self.proof.read_bytes())
        self.proof.write_text("Kernel-checked integrated consequence.\n")
        self.task("integration", 7, "prove_integrated_consequence", deps=["old-source"])
        result = self.result()
        result["implementation_status"] = "kernel_checked"
        t.submit(self.state, "integration", result, self.root)
        for reviewer in ("C", "D"):
            t.review(self.state, "integration", dict(reviewer=reviewer,
                decision="accept", reason="Checked the current integrated proof",
                evidence=[self.ref()]), self.root)
        self.assertEqual(t.stale_tasks(self.state, self.root), [])

    def test_archived_bytes_alone_do_not_clear_stale_evidence(self):
        old_ref = self.ref()
        archive = self.root / "tools" / "methodology_gate" / "evidence_snapshots"
        archive.mkdir(parents=True)
        (archive / old_ref["sha256"]).write_bytes(self.proof.read_bytes())
        self.proof.write_text("Unreviewed edit.\n")
        self.assertIn("phase0-pin_source_revision", t.stale_tasks(self.state, self.root))

    def test_rejected_task_can_be_retried_without_erasing_attempt(self):
        self.task("fact", 2, "register_interaction")
        t.submit(self.state, "fact", self.result(), self.root)
        t.review(self.state, "fact", dict(reviewer="A", decision="reject",
            reason="The claimed link is not proved", evidence=[self.ref()]), self.root)
        self.assertIn("Repair rejected", t.next_task(self.state)["diagnostic"])
        t.retry(self.state, "fact", self.root)
        self.assertEqual(self.state["tasks"]["fact"]["status"], "pending")
        self.assertEqual(len(self.state["tasks"]["fact"]["history"]), 1)

    def test_rejected_attempt_can_be_superseded_only_by_accepted_repair(self):
        self.task("old", 3, "select_tension")
        t.submit(self.state, "old", self.result(), self.root)
        t.review(self.state, "old", dict(reviewer="A", decision="reject",
            reason="This repeated an earlier use", evidence=[self.ref()]), self.root)
        self.task("repair", 1, "record_prior_use")
        with self.assertRaises(t.TaskError):
            t.supersede(self.state, "old", dict(repair_task="repair", reason="Not yet reviewed"))
        self.accept("repair")
        t.supersede(self.state, "old", dict(repair_task="repair", reason="Prior use recorded"))
        self.assertEqual(self.state["tasks"]["old"]["status"], "superseded")
        self.assertEqual(self.state["tasks"]["old"]["reviews"][0]["decision"], "reject")
        self.assertEqual(t.summary(self.state)["productive_moves"], 0)

    def test_two_distinct_reviews_are_required(self):
        self.task("fact", 2, "register_interaction")
        t.submit(self.state, "fact", self.result(), self.root)
        verdict = dict(reviewer="A", decision="accept", reason="Actual proof inspected", evidence=[self.ref()])
        t.review(self.state, "fact", verdict, self.root)
        self.assertEqual(self.state["tasks"]["fact"]["status"], "submitted")
        with self.assertRaises(t.TaskError):
            t.review(self.state, "fact", verdict, self.root)
        other = copy.deepcopy(verdict); other["reviewer"] = "B"
        t.review(self.state, "fact", other, self.root)
        self.assertEqual(self.state["tasks"]["fact"]["status"], "accepted")

    def test_cli_templates_initialize_and_dispatch_one_task(self):
        repository = Path(__file__).resolve().parents[3]
        templates = repository / "tools/methodology_gate/examples"
        record = self.root / "run.json"
        def call(command, source=None):
            args = [sys.executable, "-m", "tools.methodology_gate.taskflow", command,
                    "--record", str(record)]
            if source is not None:
                args += ["--input", str(source)]
            return json.loads(subprocess.run(args, cwd=repository, check=True,
                                             capture_output=True, text=True).stdout)
        call("init", templates / "branch-template.json")
        call("add", templates / "task-template.json")
        chosen = call("next")
        self.assertEqual(chosen["task"]["id"], "T0-pin-source")
        self.assertEqual(chosen["branch"]["endpoint"],
                         "replace-with-exact-unchanged-proposition")

    def test_cli_refuses_manual_submissions_outside_fresh_context_runner(self):
        repository = Path(__file__).resolve().parents[3]
        for command in ("submit", "review"):
            result = subprocess.run([sys.executable, "-m", "tools.methodology_gate.taskflow",
                command, "--record", str(self.root / "run.json")], cwd=repository,
                capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Use run-task for fresh isolated contexts", result.stderr)


if __name__ == "__main__":
    unittest.main()

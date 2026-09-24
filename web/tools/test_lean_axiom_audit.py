"""Regression checks for audit coverage and restoration after module splitting."""
from pathlib import Path
import json
import tempfile
import subprocess
import unittest
from unittest.mock import patch

import lean_axiom_audit as audit


class AssemblyAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.proof = Path(self.temp.name)
        self.pkg = self.proof / "HypostructureErdos64EG"
        self.pkg.mkdir()
        self.assembly = self.pkg / "Assembly.lean"
        self.assembly.write_text("import HypostructureErdos64EG.Assembly.Branch\n")
        self.branch = self.pkg / "Assembly/Branch.lean"
        self.branch.parent.mkdir()
        self.branch.write_text(
            "private noncomputable def hidden := missingProducer h\n"
            "noncomputable def Assembly.Internal.shared := hidden\n"
            "@[reducible] noncomputable def publicEntry := Assembly.Internal.shared\n"
        )
        for key, value in {"PROOF_DIR": self.proof, "PKG": self.pkg,
                           "ASSEMBLY": self.assembly, "STUBS": self.pkg / "FrontierStubs.lean",
                           "AUDIT": self.pkg / "AxiomAudit.lean"}.items():
            patcher = patch.object(audit, key, value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def test_recursive_coverage_and_private_name_resolution(self):
        self.assertEqual(audit.declarations(),
                         ["hidden", "Assembly.Internal.shared", "publicEntry"])
        index = self.proof / ".lake/build/lib/lean/HypostructureErdos64EG/Assembly/Branch.ilean"
        index.parent.mkdir(parents=True)
        names = ["_private.HypostructureErdos64EG.Assembly.Branch.0.HypostructureErdos64EG.hidden",
                 "HypostructureErdos64EG.Assembly.Internal.shared",
                 "HypostructureErdos64EG.publicEntry"]
        index.write_text(json.dumps({"decls": dict.fromkeys(names, [])}))
        self.assertEqual(audit.compiled_declarations(), names)

    def test_import_is_inserted_in_consumer_and_restored_exactly(self):
        before = self.branch.read_bytes()
        originals = {}
        audit.insert_stub_imports(["missingProducer"], originals)
        self.assertTrue(self.branch.read_text().startswith("import HypostructureErdos64EG.FrontierStubs\n"))
        self.assertNotIn(self.assembly, originals)
        audit.restore(originals)
        self.assertEqual(self.branch.read_bytes(), before)

    def test_restore_preserves_preexisting_temporary_files(self):
        existing = self.pkg / "AxiomAudit.lean"
        absent = self.pkg / "FrontierStubs.lean"
        existing.write_bytes(b"original\r\n")
        originals = {existing: existing.read_bytes(), absent: None}
        existing.write_text("replacement")
        absent.write_text("temporary")
        audit.restore(originals)
        self.assertEqual(existing.read_bytes(), b"original\r\n")
        self.assertFalse(absent.exists())

    def test_discovers_downstream_frontiers_and_restores_on_failure(self):
        before = self.branch.read_bytes()
        steps = [
            subprocess.CompletedProcess([], 1, "error: Unknown identifier `missingProducer`", ""),
            subprocess.CompletedProcess([], 1, "error: Unknown identifier `downstreamProducer`", ""),
            subprocess.CompletedProcess([], 1, "error: unrelated type mismatch", ""),
        ]
        with patch.object(audit, "_lake", side_effect=steps), \
                patch.object(audit, "write_stubs", wraps=audit.write_stubs) as writer:
            with self.assertRaisesRegex(RuntimeError, "unrelated type mismatch"):
                audit.run()
            self.assertEqual(writer.call_args_list[-1].args[0],
                             ["downstreamProducer", "missingProducer"])
        self.assertEqual(self.branch.read_bytes(), before)
        self.assertFalse(audit.STUBS.exists())
        self.assertFalse(audit.AUDIT.exists())

    def test_repeated_stub_import_insertion_is_idempotent(self):
        originals = {}
        audit.insert_stub_imports(["missingProducer"], originals)
        audit.insert_stub_imports(["missingProducer"], originals)
        self.assertEqual(self.branch.read_text().count("import HypostructureErdos64EG.FrontierStubs"), 1)
        audit.restore(originals)

    def test_report_preserves_internal_names_and_private_coverage(self):
        text = "\n".join([
            "'_private.HypostructureErdos64EG.Assembly.Branch.0.HypostructureErdos64EG.hidden' depends on axioms: [propext]",
            "'HypostructureErdos64EG.Assembly.Internal.shared' depends on axioms: [frontierGap]",
        ])
        self.assertEqual(audit.split_axiom_report(text),
                         (["hidden"], ["Assembly.Internal.shared"]))


if __name__ == "__main__":
    unittest.main()

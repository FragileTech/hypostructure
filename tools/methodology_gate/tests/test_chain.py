"""Dependency inventories are structural certificates, not proof evidence."""
import copy
import tempfile
import unittest
from pathlib import Path

from tools.methodology_gate.chain import validate_chain


class ChainTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'Proof.lean').write_text('-- fixture; not a Lean proof\n')
        self.fact = {'statement': 'Exact original mathematical statement',
                     'owner': 'node143', 'path': 'Proof.lean',
                     'declaration': 'Proof.fact', 'dependencies': [],
                     'status': 'pending'}
        self.manifest = {'target': 'goal', 'facts': {
            'goal': {**copy.deepcopy(self.fact), 'owner': 'node144',
                     'dependencies': ['input']},
            'input': copy.deepcopy(self.fact)}}

    def checked(self, fact_id):
        self.manifest['facts'][fact_id].update(
            status='kernel_checked', kernel_targets=['Proof'],
            statement_evidence=['statement-ref'],
            publication_evidence=['ledger-ref'])

    def errors(self, complete=False):
        return validate_chain(self.manifest, self.root, complete=complete)

    def test_setup_accepts_explicit_unimplemented_prerequisites(self):
        self.manifest['facts']['input']['path'] = 'Future/Owner.lean'
        self.assertEqual(self.errors(), [])
        self.assertTrue(self.errors(complete=True))

    def test_multiline_formulas_and_structured_owner_are_valid(self):
        self.manifest['facts']['input']['statement'] = '∀ x,\n\tP x →\n  Q x'
        self.manifest['facts']['input']['owner'] = {'node': ['[143]'], 'label': ['lem:input'],
                                                  'atomic_rows': ['inputRow']}
        self.assertEqual(self.errors(), [])
        del self.manifest['facts']['input']['owner']['atomic_rows']
        self.assertEqual(self.errors(), [])
        self.manifest['facts']['input']['statement'] += '\x00'
        self.assertTrue(self.errors())

    def test_controller_and_worker_share_the_identical_schema(self):
        from tools.methodology_gate.policy.chain_schema import validate_chain as worker_validator
        self.assertIs(validate_chain, worker_validator)

    def test_completed_inventory_needs_every_prerequisite(self):
        self.checked('goal')
        self.assertTrue(self.errors(complete=True))
        self.checked('input')
        self.assertEqual(self.errors(complete=True), [])

    def test_checked_status_does_not_replace_publication_evidence(self):
        self.checked('goal')
        del self.manifest['facts']['goal']['publication_evidence']
        self.assertTrue(any('publication_evidence' in e for e in self.errors()))

    def test_source_file_must_exist_when_claiming_checked(self):
        self.checked('input')
        self.manifest['facts']['input']['path'] = 'Future/Owner.lean'
        self.assertTrue(any('missing' in e for e in self.errors()))

    def test_reject_cycles_and_missing_dependencies(self):
        self.manifest['facts']['input']['dependencies'] = ['goal']
        self.assertTrue(any('cycle' in e for e in self.errors()))
        self.manifest['facts']['input']['dependencies'] = ['absent']
        self.assertTrue(any('missing dependency' in e for e in self.errors()))

    def test_reject_disconnected_inventory(self):
        self.manifest['facts']['irrelevant'] = copy.deepcopy(self.fact)
        self.assertTrue(any('outside' in e for e in self.errors()))

    def test_unnecessary_disposition_retains_original_inventory(self):
        self.checked('goal')
        self.manifest['facts']['input']['status'] = 'unnecessary'
        self.assertTrue(self.errors(complete=True))
        self.manifest['facts']['input']['unnecessary_evidence'] = ['nonuse-proof']
        self.assertEqual(self.errors(complete=True), [])
        self.manifest['facts']['goal'].update(
            status='unnecessary', unnecessary_evidence=['nonuse-proof'])
        self.assertTrue(any('target cannot' in e for e in self.errors()))

    def test_reject_source_escape_and_shell_targets(self):
        self.checked('input')
        for path in ('../Proof.lean', '/Proof.lean', 'a/../Proof.lean',
                     './Proof.lean', 'a\\Proof.lean', 'Proof.lean\n'):
            with self.subTest(path=path):
                self.manifest['facts']['input']['path'] = path
                self.assertTrue(self.errors())
        self.manifest['facts']['input']['path'] = 'Proof.lean'
        for module in ('--help', 'Proof;touch pwned', 'Proof$(id)', 'Proof/file', ''):
            with self.subTest(module=module):
                self.manifest['facts']['input']['kernel_targets'] = [module]
                self.assertTrue(self.errors())

    def test_reject_symlink_even_inside_snapshot(self):
        (self.root / 'Alias.lean').symlink_to(self.root / 'Proof.lean')
        self.manifest['facts']['input']['path'] = 'Alias.lean'
        self.assertTrue(any('symlink' in e for e in self.errors()))

    def test_wrong_json_types_fail_without_exceptions(self):
        for bad in (None, [], {'target': [], 'facts': {'f': None}},
                    {'target': 'f', 'facts': {'f': {'dependencies': [{}]}}}):
            with self.subTest(manifest=bad):
                self.assertTrue(validate_chain(bad, self.root))

    def test_unicode_lean_names_and_shared_ancestors(self):
        self.manifest['facts']['input']['declaration'] = "Proof.σ_bound'"
        self.manifest['facts']['goal']['dependencies'].append('other')
        self.manifest['facts']['other'] = {**copy.deepcopy(self.fact),
                                         'dependencies': ['input']}
        self.assertEqual(self.errors(), [])

    def test_explicit_target_cannot_be_omitted(self):
        del self.manifest['target']
        self.assertTrue(self.errors())


if __name__ == '__main__':
    unittest.main()

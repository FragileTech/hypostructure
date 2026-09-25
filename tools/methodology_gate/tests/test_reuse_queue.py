import copy
import unittest
from pathlib import Path
from tools.methodology_gate.chain import implementation_work, validate_chain


class ReuseQueueTests(unittest.TestCase):
    def setUp(self):
        self.chain = {'target': 'entry', 'facts': {}}
        for key, deps in [('input', []), ('routing', ['input']), ('handoff', ['routing']), ('entry', ['handoff'])]:
            self.chain['facts'][key] = dict(statement='True', owner='node144',
                path='Proof.lean', declaration='Proof.'+key, dependencies=deps, status='pending')

    def test_legacy_pending_is_not_a_proof_queue(self):
        work = implementation_work(self.chain)
        self.assertEqual(work['repair'], [])
        self.assertEqual([x['fact'] for x in work['reconcile']], ['input', 'routing', 'handoff', 'entry'])
        self.assertTrue(all(f['status'] == 'pending' for f in self.chain['facts'].values()))

    def test_only_actual_repair_is_scheduled_adapters_follow(self):
        facts = self.chain['facts']
        facts['input']['status'] = 'kernel_checked'
        facts['routing'].update(work_kind='proof_repair', work_reason='source reading mismatch', work_evidence=['e'])
        for key, dep in [('handoff', 'routing'), ('entry', 'handoff')]:
            facts[key].update(work_kind='adapter', adapter_of=[dep], work_reason='projection/injection', work_evidence=['e'])
        work = implementation_work(self.chain)
        self.assertEqual([x['fact'] for x in work['repair']], ['routing'])
        self.assertEqual([x['fact'] for x in work['adapters']], ['handoff', 'entry'])
        self.assertEqual([x['fact'] for x in work['reuse']], ['input'])

    def test_adapter_does_not_certify_completion(self):
        self.chain['facts']['entry'].update(work_kind='adapter', adapter_of=['handoff'], work_reason='injection', work_evidence=['e'])
        self.assertEqual(validate_chain(self.chain, Path('/tmp')), [])
        self.assertTrue(validate_chain(self.chain, Path('/tmp'), complete=True))

    def test_repair_needs_evidence_and_adapter_needs_actual_dependency(self):
        fact = self.chain['facts']['entry']
        fact['work_kind'] = 'proof_repair'
        self.assertTrue(validate_chain(self.chain, Path('/tmp')))
        fact.update(work_kind='adapter', adapter_of=['invented'], work_reason='injection', work_evidence=['e'])
        self.assertTrue(validate_chain(self.chain, Path('/tmp')))

    def test_checked_is_preserved_and_unnecessary_is_skipped(self):
        self.chain['facts']['input']['status'] = 'unnecessary'
        self.chain['facts']['routing']['status'] = 'kernel_checked'
        original = copy.deepcopy(self.chain)
        work = implementation_work(self.chain)
        self.assertEqual(self.chain, original)
        self.assertEqual([x['fact'] for x in work['reuse']], ['routing'])
        self.assertNotIn('input', [x['fact'] for q in work.values() for x in q])

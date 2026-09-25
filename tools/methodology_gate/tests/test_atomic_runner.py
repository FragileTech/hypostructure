"""Fresh task contexts and scope enforcement; model processes are mocked."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools.methodology_gate import atomic_runner as a, taskflow as t


class AtomicRunnerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / 'repo'
        self.root.mkdir()
        (self.root / 'premises.md').write_text('The complete retained hypotheses about G.')
        (self.root / 'unrelated-secret.md').write_text('Must not reach workers.')
        self.state = t.fresh(dict(id='B', revision='r', source_revision='commit', endpoint='B implies False',
            incoming='the selected arm', objects=['the same G'], minimality='vertex count', imports=[],
            accounts=[], open_outcomes=['residual']))
        self.contract = dict(id='one', mode='DISCOVER', phase='0', branch_revision='r', move_id='',
            kind='pin_source_revision', goal='Pin the source for this one retained graph.', objects=['G'],
            reads=['branch:r', 'premises.md'], interaction='', parent_payoff='', depends_on=[],
            allowed_write='proof.md', acceptance='Source citation verified', on_failure='Name missing source')
        t.add_task(self.state, self.contract)
        self.calls = []
        self.decision = 'accept'
        self.escape = False
        self.reuse = False

    def launch(self, role, view, output, packet, log, auth, timeout):
        self.calls.append((role, copy.deepcopy(packet), set(a.runner.files(view))))
        output.mkdir()
        ref = dict(path='proof.md', sha256=hashlib.sha256(b'One exact proof.').hexdigest(), locator='line 1')
        if role == 'atomic_executor':
            target = output / 'artifact/proof.md'
            target.parent.mkdir()
            target.write_text('One exact proof.')
            result = dict(status='SUBMITTED_RESULT', output='One inference proved', evidence=[ref],
                implementation_status='none', first_missing_inference='', immediate_subobligations=[],
                metadata=dict(structural_use=None, interaction=None, changed_objects=[],
                              changed_accounts=[], side_observations=[]))
            a.runner.write(output / 'result.json', result)
            if self.escape:
                (output / 'artifact/another-proof.md').write_text('unauthorized')
        else:
            self.assertNotIn('reviews', packet)
            self.assertFalse(any('reviewer-0' in name for name in a.runner.files(view)))
            a.runner.write(output / 'review.json', dict(reviewer='untrusted-model-id',
                decision=self.decision, reason='Inspected the exact inference', evidence=[ref]))
        return ('reused' if self.reuse else f'fresh-{len(self.calls)}'), {'summary': 'done'}

    def run_one(self):
        with patch.object(a.runner, 'sandbox_probe'), patch.object(a.runner, 'launch', self.launch):
            return a.run_one(self.state, self.root, self.root.parent / 'attempts',
                             self.root.parent / 'auth', 10)

    def test_three_fresh_contexts_scoped_inputs_and_controller_integration(self):
        result = self.run_one()
        self.assertEqual(result['status'], 'accepted')
        self.assertEqual([call[0] for call in self.calls],
                         ['atomic_executor', 'atomic_reviewer', 'atomic_reviewer'])
        for _, packet, files in self.calls:
            self.assertEqual(packet['task']['goal'], self.contract['goal'])
            self.assertEqual(packet['branch'], self.state['branch'])
            self.assertNotIn('sources/unrelated-secret.md', files)
            self.assertNotIn('tasks', packet)
        self.assertEqual((self.root / 'proof.md').read_text(), 'One exact proof.')
        task = self.state['tasks']['one']
        self.assertEqual(task['status'], 'accepted')
        self.assertEqual(task['context_receipt']['sessions'], ['fresh-1', 'fresh-2', 'fresh-3'])
        self.assertEqual([r['reviewer'] for r in task['reviews']], ['fresh-2', 'fresh-3'])

    def test_rejected_result_never_changes_working_proof_and_retry_is_fresh(self):
        before = copy.deepcopy(self.state)
        self.decision = 'reject'
        self.assertEqual(self.run_one()['status'], 'rejected')
        self.assertEqual(self.state['branch'], before['branch'])
        self.assertEqual(self.state['tasks']['one']['status'], 'pending')
        self.assertIsNone(self.state['tasks']['one']['submission'])
        self.assertEqual(len(self.state['tasks']['one']['isolated_attempts']), 1)
        self.assertFalse((self.root / 'proof.md').exists())
        self.decision = 'accept'
        self.run_one()
        self.assertEqual(self.calls[3][1]['repair_reasons'],
                         ['Inspected the exact inference', 'Inspected the exact inference'])
        self.assertEqual(self.state['tasks']['one']['context_receipt']['sessions'],
                         ['fresh-4', 'fresh-5', 'fresh-6'])

    def test_extra_output_and_context_reuse_are_rejected(self):
        self.escape = True
        with self.assertRaisesRegex(t.TaskError, 'single artifact scope'):
            self.run_one()
        self.escape = False
        self.reuse = True
        with self.assertRaisesRegex(t.TaskError, 'context was reused'):
            self.run_one()
        self.assertFalse((self.root / 'proof.md').exists())

    def test_isolation_failure_never_falls_back_to_operator(self):
        with patch.object(a.runner, 'sandbox_probe', side_effect=RuntimeError('isolation unavailable')):
            with self.assertRaisesRegex(RuntimeError, 'isolation unavailable'):
                a.run_one(self.state, self.root, self.root.parent / 'attempts', Path('auth'), 10)
        self.assertFalse((self.root.parent / 'attempts').exists())

    def test_directory_and_symlink_inputs_rejected(self):
        self.state['tasks']['one']['contract']['reads'].append('.')
        with self.assertRaises(t.TaskError):
            a.assignment(self.state, self.root)
        self.state['tasks']['one']['contract']['reads'].pop()
        (self.root / 'link').symlink_to(self.root / 'premises.md')
        self.state['tasks']['one']['contract']['reads'].append('link')
        with self.assertRaisesRegex(t.TaskError, 'Symlinks'):
            a.assignment(self.state, self.root)

    def test_construction_requires_admission_before_launch(self):
        task = self.state['tasks']['one']['contract']
        task.update(phase='6', kind='prove_property', move_id='M')
        with patch.object(t, 'next_task', return_value=dict(task=task, diagnostic=None)):
            with self.assertRaisesRegex(t.TaskError, 'Phase 5 admission'):
                a.assignment(self.state, self.root)

    def test_declared_accepted_evidence_does_not_import_worker_side_observations(self):
        self.run_one()
        contract = dict(self.contract, id='two', reads=['branch:r', 'one'], depends_on=['one'],
                        allowed_write='second.md')
        t.add_task(self.state, contract)
        self.state['tasks']['one']['submission']['metadata']['side_observations'] = ['Explore elsewhere']
        packet = a.assignment(self.state, self.root)
        self.assertNotIn('metadata', packet['accepted_inputs']['one'])
        self.assertNotIn('Explore elsewhere', json.dumps(packet))

    def test_missing_inference_is_not_accepted_as_task_completion(self):
        original = self.launch
        def blocked(*args):
            response = original(*args)
            if args[0] == 'atomic_executor':
                path = args[2] / 'result.json'
                result = json.loads(path.read_text())
                result.update(status='NEEDS_DECOMPOSITION', first_missing_inference='transport',
                              immediate_subobligations=['Prove the same-object transport'])
                a.runner.write(path, result)
            return response
        with patch.object(a.runner, 'sandbox_probe'), patch.object(a.runner, 'launch', blocked):
            with self.assertRaisesRegex(t.TaskError, 'cannot be accepted'):
                a.run_one(self.state, self.root, self.root.parent / 'attempts', Path('auth'), 10)
        self.assertFalse((self.root / 'proof.md').exists())


if __name__ == '__main__':
    unittest.main()

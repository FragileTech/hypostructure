"""Controller integration with mocked model processes, real immutable records and gates."""
import copy
import shutil
import tempfile
import threading
import unittest
from pathlib import Path
from unittest.mock import patch
from tools.methodology_gate import core, runner, egress
from tools.methodology_gate.policy import workflow as w
from tools.methodology_gate.tests.structural_fixtures import state, advance


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.base=Path(self.tmp.name);self.repo=self.base/'repo';self.repo.mkdir()
        project=Path(__file__).resolve().parents[3]
        for path in core.record.SOURCES:
            target=self.repo/path;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(project/path,target)
        (self.repo/'Fixture.lean').write_text('theorem Fixture.lower_bound : True := by trivial\n')
        self.source=self.repo/'record';self.source.mkdir()
        initial=state(self.source);runner.write(self.source/'state.json',initial)
        (self.source/'execution.md').write_text('Initial retained history.\n')
        self.contract=self.base/'contract.json'
        self.scoped_path=next(iter(core.record.SOURCES))
        stage_scopes={str(stage):list(core.record.SOURCES) for stage in w.STAGE_ORDER}
        stage_scopes['3b']=['Fixture.lean']
        stage_scopes['1']=[self.scoped_path]
        runner.write(self.contract,dict(name='Fixture branch',input_paths=list(core.record.SOURCES)+['Fixture.lean'],
            stage_input_paths=stage_scopes,allowed_changes=['New.lean','Fixture.lean'],
            checks=[dict(name='Fixture check',argv=['/usr/bin/true'])]))
        self.run=self.base/'controller';runner.initialize(self.run,self.repo,self.source,self.contract)
        self.auth=self.base/'unused-auth';self.calls=[];self.source_views=[];self.executor_mutation=None;self.review_mutation=None;self.sessions={}

    def state(self): return runner.read(runner.committed(self.run)/'record/state.json')

    def launch(self,role,view,output,assignment,log,auth,timeout):
        self.calls.append((role,assignment.copy()));output.mkdir()
        self.source_views.append((role,assignment['stage'],set(runner.files(view/'sources'))))
        if role=='executor':
            source=view/('saved-submission' if assignment.get('artifact_format_repair') else '')/'record'
            shutil.copytree(source,output/'record');b=runner.read(output/'record/state.json')
            a=b if assignment.get('artifact_format_repair') else advance(b,assignment['stage'],assignment['node'])
            if assignment['stage']=='3b':
                (output/'changes').mkdir(exist_ok=True)
                (output/'changes/Fixture.lean').write_text('theorem Fixture.lower_bound : True := by trivial\n')
            (output/'record'/('stage-'+assignment['attempt']+'.md')).write_text('Fixture reasoning or authorized construction.\n')
            if self.executor_mutation:self.executor_mutation(a,output,assignment)
            runner.write(output/'record/state.json',a);response={'summary':'Fixture submission'}
        else:
            s=runner.read(view/'record/state.json')
            ref={k:s['evidence']['e'][k] for k in ('path','sha256','locator')};ref['path']='record/'+ref['path']
            reviewed=[s['events'][-1]['artifact']['structure_fact_id']] if assignment['stage']=='3b' else []
            response=dict(binding=assignment['binding'],decision='accept',first_failure='',repair='',repair_stage=assignment['stage'],accepted_stage_revocation=None,reviewed_facts=reviewed,invalid_inherited_facts=[],revalidated_facts=[],unnecessary_facts=[],gates={g:dict(verdict='pass',reason='Mock review of exact fixture evidence',evidence=[copy.deepcopy(ref)]) for g in assignment['gates']})
            if self.review_mutation:self.review_mutation(response,view,assignment)
        key=assignment.get('role',role)
        return self.sessions.get(key,key+'-session-'+assignment['attempt']),response

    def tick(self):
        if core.next_stage(self.state(),'root')=='3b':
            def checked(proposal,contract,attempt,timeout):
                (proposal/'controller-checks').mkdir(exist_ok=True)
                runner.write(proposal/'controller-checks.json',[{'exit_code':0}])
            with patch.object(runner,'launch',side_effect=self.launch),patch.object(runner,'run_checks',side_effect=checked):
                return runner.tick(self.run,self.auth,10)
        with patch.object(runner,'launch',side_effect=self.launch):return runner.tick(self.run,self.auth,10)

    def advance_to(self,stage):
        while core.next_stage(self.state(),'root')!=stage:
            self.assertEqual(self.tick(),'accepted')

    def reject_review(self,r,view,a,gate='full_residual',stage=1):
        if a['role']=='reviewer-2':
            r.update(decision='reject',first_failure='Concrete substantive defect',repair='Correct earliest defective decision',repair_stage=stage)
            r['gates'][gate]['verdict']='fail'
            if w.before(stage,a['stage']):
                r['accepted_stage_revocation']=dict(stage=stage,defect='Concrete defect in the accepted stage result',
                    evidence=copy.deepcopy(r['gates'][gate]['evidence']))

    def test_two_independent_reviews_really_overlap(self):
        barrier=threading.Barrier(2);views=[]
        def concurrent(role,view,output,a,log,auth,timeout):
            if role=='reviewer':views.append((a['binding'],runner.files(view)));barrier.wait(timeout=3)
            return self.launch(role,view,output,a,log,auth,timeout)
        with patch.object(runner,'launch',side_effect=concurrent):self.assertEqual(runner.tick(self.run,self.auth,10),'accepted')
        self.assertEqual(views[0],views[1]);self.assertEqual(core.next_stage(self.state(),'root'),2)

    def test_stage_scoped_sources_hide_unneeded_files_and_restore_full_snapshot(self):
        self.assertEqual(self.tick(),'accepted')
        expected={self.scoped_path}
        stage_one=[paths for _,stage,paths in self.source_views if stage==1]
        self.assertEqual(stage_one,[expected,expected,expected])
        committed_sources=runner.files(runner.committed(self.run)/'sources')
        self.assertEqual(set(committed_sources),set(core.record.SOURCES) | {'Fixture.lean'})
        self.assertEqual(self.tick(),'accepted')
        stage_two=[paths for _,stage,paths in self.source_views if stage==2]
        self.assertEqual(stage_two,[set(core.record.SOURCES)]*3)

    def test_fresh_init_refuses_to_repeat_an_accepted_stage(self):
        self.assertEqual(self.tick(),'accepted')
        duplicate=self.base/'duplicate'
        with self.assertRaisesRegex(core.Rejected,'Accepted stage already exists'):
            runner.initialize(duplicate,self.repo,self.source,self.contract)
        self.assertFalse(duplicate.exists())

    def test_continuation_requires_current_benchmark_policy(self):
        self.assertEqual(self.tick(), 'accepted')
        changed_policy = self.base / 'changed-policy'
        shutil.copytree(runner.POLICY, changed_policy)
        (changed_policy / 'executor-prompt.md').write_text('Different instructions')
        with patch.object(runner, 'POLICY', changed_policy):
            with self.assertRaisesRegex(core.Rejected, 'current benchmark policy'):
                runner.continue_run(self.base / 'continuation', self.run, self.repo, self.contract)
        self.assertFalse((self.base / 'continuation').exists())

    def test_later_source_repair_carries_accepted_stage_without_rerunning_it(self):
        self.assertEqual(self.tick(),'accepted')
        reviewed=copy.deepcopy(self.state()['events'][0])
        extra='NarrowResidualDefinition.lean'
        (self.repo/extra).write_text('def residualWitness : True := trivial\n')
        amended=runner.read(self.contract)
        amended['input_paths'].append(extra)
        amended['stage_input_paths']['2'].append(extra)
        amended_contract=self.base/'amended-contract.json'
        runner.write(amended_contract,amended)
        continued=self.base/'continuation'
        runner.continue_run(continued,self.run,self.repo,amended_contract)
        preserved=runner.read(runner.committed(continued)/'record/state.json')
        self.assertEqual(preserved['events'][0],reviewed)
        self.assertEqual(core.next_stage(preserved,'root'),2)
        self.assertEqual(set(runner.active_artifacts(preserved,'root')),{1})
        self.run=continued;self.calls=[];self.source_views=[]
        self.assertEqual(self.tick(),'accepted')
        self.assertEqual([a['stage'] for role,a in self.calls if role=='executor'],[2])
        self.assertTrue(all(extra in paths for _,stage,paths in self.source_views if stage==2))

    def test_self_review_and_shared_review_session_cannot_commit(self):
        self.sessions={'reviewer-1':'same','executor':'same'}
        self.assertEqual(self.tick(),'retry_required');self.assertEqual(self.state()['events'],[])

    def test_shared_review_session_cannot_commit(self):
        self.sessions={'reviewer-1':'same','reviewer-2':'same'}
        self.assertEqual(self.tick(),'retry_required');self.assertEqual(self.state()['events'],[])

    def test_malformed_stage_five_event_cannot_crash_recovery(self):
        self.advance_to(5)
        self.executor_mutation=lambda s,o,a:s.update(events=[])
        self.assertEqual(self.tick(),'repair_queued')
        self.assertIn('failed',self.state()['events'][-1]['result'])

    def test_missing_stage_five_events_cannot_crash_recovery(self):
        self.advance_to(5)
        self.executor_mutation=lambda s,o,a:s.pop('events')
        self.assertEqual(self.tick(),'repair_queued')

    def test_invalid_stage_five_json_cannot_crash_recovery(self):
        self.advance_to(5)
        def invalid(role,view,output,a,log,auth,timeout):
            result=self.launch(role,view,output,a,log,auth,timeout)
            if role=='executor':(output/'record/state.json').write_text('{malformed')
            return result
        with patch.object(runner,'launch',side_effect=invalid):
            self.assertEqual(runner.tick(self.run,self.auth,10),'repair_queued')

    def test_final_verification_repair_preserves_discharged_mathematics(self):
        self.advance_to(8);original=copy.deepcopy(self.state()['nodes'])
        self.review_mutation=lambda r,v,a:self.reject_review(r,v,a,'target_node_closure',8)
        def checks(proposal,contract,attempt,timeout):
            (proposal/'controller-checks').mkdir(exist_ok=True)
            runner.write(proposal/'controller-checks.json',[{'exit_code':0}])
        with patch.object(runner,'run_checks',side_effect=checks):
            self.assertEqual(self.tick(),'repair_queued')
        self.assertEqual(self.state()['nodes'],original)
        self.assertEqual(core.next_stage(self.state(),'root'),8)
        self.review_mutation=None
        with patch.object(runner,'run_checks',side_effect=checks):
            self.assertEqual(self.tick(),'accepted')
        self.assertEqual(self.state()['status'],'complete')

    def failed_verification(self,s,out,a):
        s['status']='active'
        s['events'][-1].update(result='failed',failure=dict(field='verification evidence',
            reason='Exact final artifact not yet supplied',retained_prefix='Established closure',evidence=['e']))

    def test_accepted_failed_verification_can_repair_only_audit(self):
        self.advance_to(8);self.executor_mutation=self.failed_verification
        self.assertEqual(self.tick(),'accepted')
        self.assertEqual(core.next_stage(self.state(),'root'),8)
        self.assertEqual(self.state()['nodes'][0]['status'],'closed')

    def test_accepted_failed_verification_reopens_when_math_needs_repair(self):
        self.advance_to(8);self.executor_mutation=self.failed_verification
        self.review_mutation=lambda r,v,a:r.update(repair_stage=6,accepted_stage_revocation=dict(
            stage=6,defect='Accepted construction has a mathematical defect',
            evidence=copy.deepcopy(r['gates']['full_residual']['evidence'])))
        self.assertEqual(self.tick(),'accepted')
        self.assertEqual(core.next_stage(self.state(),'root'),6)
        self.assertEqual(self.state()['nodes'][0]['status'],'open')

    def test_rejection_preserves_failed_artifact_and_exact_residual(self):
        self.review_mutation=self.reject_review;original=self.state();self.assertEqual(self.tick(),'repair_queued')
        s=self.state();self.assertEqual(s['nodes'],original['nodes']);self.assertEqual(core.next_stage(s,'root'),1)
        self.assertTrue(list((runner.committed(self.run)/'record/gate-rejections').glob('*/submission/record/stage-*.md')))
        self.assertEqual(core.record.validate(s,runner.committed(self.run)/'record'),[])

    def test_review_repair_preserves_earlier_reasoning(self):
        self.advance_to(5);self.review_mutation=lambda r,v,a:self.reject_review(r,v,a,'conditional_payoff_proved',3)
        self.assertEqual(self.tick(),'repair_queued');self.assertEqual(core.next_stage(self.state(),'root'),5)
        self.assertEqual(set(runner.active_artifacts(self.state(),'root')),{1,2,3,'3b',4})

    def test_both_reviews_can_revoke_a_specific_accepted_stage(self):
        self.advance_to(5)
        def revoke(r,view,a):
            r.update(decision='reject',first_failure='Stage 3 conflict missed a bound case',
                     repair='Repair the Stage 3 classification',repair_stage=3,
                     accepted_stage_revocation=dict(stage=3,defect='Stage 3 conflict missed a bound case',
                         evidence=copy.deepcopy(r['gates']['full_residual']['evidence'])))
            r['gates']['conditional_payoff_proved']['verdict']='fail'
        self.review_mutation=revoke
        self.assertEqual(self.tick(),'repair_queued')
        self.assertEqual(core.next_stage(self.state(),'root'),3)
        self.assertEqual(set(runner.active_artifacts(self.state(),'root')),{1,2})

    def test_early_source_changes_rejected_even_on_failure(self):
        def early(s,out,a):
            (out/'changes').mkdir();(out/'changes/New.lean').write_text('theorem bad : True := by trivial\n')
        self.executor_mutation=early;self.assertEqual(self.tick(),'repair_queued')
        self.assertEqual([role for role,_ in self.calls],['executor'])
        self.assertIn('limited to the Stage 3b structure',self.state()['events'][-1]['reason'])

    def test_dispatch_never_runs_unreviewed_construction(self):
        # Corrupt a valid committed fixture to request construction without an authorization.
        self.advance_to(6);snapshot=runner.committed(self.run)
        with tempfile.TemporaryDirectory() as d:
            proposal=Path(d)/'p';shutil.copytree(snapshot,proposal);s=runner.read(proposal/'record/state.json')
            s['events'][-1]['artifact']['residual_binding']='stale';runner.write(proposal/'record/state.json',s)
            runner.commit(self.run,proposal,{'kind':'fixture corrupted authorization'})
        self.calls=[];self.assertEqual(self.tick(),'repair_queued');self.assertEqual(self.calls,[])
        self.assertEqual(core.next_stage(self.state(),'root'),6)

    def test_authorized_source_construction_and_final_checks(self):
        self.advance_to(6)
        def construct(s,out,a):
            (out/'changes').mkdir();(out/'changes/New.lean').write_text('theorem Fixture.done : True := by trivial\n')
        self.executor_mutation=construct;self.assertEqual(self.tick(),'accepted');self.executor_mutation=None
        self.assertTrue((runner.committed(self.run)/'changes/New.lean').is_file());self.assertEqual(self.tick(),'accepted')
        def checks(proposal,contract,attempt,timeout):
            (proposal/'controller-checks').mkdir(exist_ok=True);runner.write(proposal/'controller-checks.json',[{'exit_code':0}])
        with patch.object(runner,'run_checks',side_effect=checks) as check:
            self.assertEqual(self.tick(),'accepted');self.assertEqual(check.call_count,1)
        self.assertEqual(self.state()['status'],'complete');self.assertEqual(self.tick(),'complete')

    def test_final_check_failure_cannot_complete(self):
        self.advance_to(8)
        with patch.object(runner,'run_checks',side_effect=core.Rejected('actual kernel failure')):
            self.assertEqual(self.tick(),'repair_queued')
        self.assertNotEqual(self.state()['status'],'complete')

    def test_stage_eight_cannot_change_sources(self):
        self.advance_to(8)
        def mutate(s,out,a):
            (out/'changes').mkdir();(out/'changes/New.lean').write_text('unexpected change')
        self.executor_mutation=mutate;self.assertEqual(self.tick(),'repair_queued')

    def test_failed_construction_requires_new_authorization(self):
        self.advance_to(6)
        def failed(s,out,a):
            s['events'][-1].update(result='failed',failure=dict(field='response',reason='Actual authorized attempt failed',retained_prefix='All incoming facts',evidence=['e'],attempt='Exact authorized comparison'))
        self.executor_mutation=failed
        self.review_mutation=lambda r,v,a:r.update(repair_stage=5,accepted_stage_revocation=dict(
            stage=5,defect='The accepted authorization does not cover this failed output',
            evidence=copy.deepcopy(r['gates']['full_residual']['evidence'])))
        self.assertEqual(self.tick(),'accepted');s=self.state();self.assertEqual(core.next_stage(s,'root'),5)
        self.assertIsNone(runner.authorization(s,'root'));self.assertTrue(s['events'][-1]['attempted_technique'])
        self.executor_mutation=None;self.review_mutation=None;self.assertEqual(self.tick(),'repair_queued')

    def test_reviewer_cannot_accept_failed_construction_for_immediate_retry(self):
        self.advance_to(6)
        def failed(s,out,a):s['events'][-1].update(result='failed',failure=dict(field='response',reason='failed',retained_prefix='R',evidence=['e'],attempt='authorized work'))
        self.executor_mutation=failed;self.assertEqual(self.tick(),'retry_required')
        self.assertEqual(core.next_stage(self.state(),'root'),6)

    def test_unknown_new_facts_cannot_be_approved(self):
        self.review_mutation=lambda r,v,a:r.update(reviewed_facts=['invented'])
        self.assertEqual(self.tick(),'retry_required');self.assertEqual(self.state()['events'],[])

    def test_one_reviewer_cannot_restore_quarantine(self):
        def reject(r,v,a):
            self.reject_review(r,v,a)
            if a['role']=='reviewer-2':r['invalid_inherited_facts']=['f']
        self.review_mutation=reject;self.assertEqual(self.tick(),'repair_queued')
        self.review_mutation=lambda r,v,a:r.update(revalidated_facts=['f'] if a['role']=='reviewer-1' else [])
        self.assertEqual(self.tick(),'accepted');self.assertIn('f',self.state()['quarantined_facts'])

    def test_interrupted_reviewer_reuses_completed_executor_and_other_review(self):
        def interrupt(role,view,output,a,log,auth,timeout):
            if a.get('role')=='reviewer-2':raise runner.WorkerUnavailable('interrupted')
            return self.launch(role,view,output,a,log,auth,timeout)
        with patch.object(runner,'launch',side_effect=interrupt):self.assertEqual(runner.tick(self.run,self.auth,10),'retry_required')
        self.assertEqual(self.tick(),'accepted')
        self.assertEqual([r for r,_ in self.calls].count('executor'),1)
        self.assertEqual(sum(a.get('role')=='reviewer-1' for _,a in self.calls),1)

    def test_malformed_review_retries_without_mathematical_failure(self):
        self.review_mutation=lambda r,v,a:r.pop('repair_stage')
        self.assertEqual(self.tick(),'retry_required');self.assertEqual(self.state()['events'],[])
        self.review_mutation=None;self.assertEqual(self.tick(),'accepted')
        self.assertEqual([r for r,_ in self.calls].count('executor'),1)

    def test_checkpoint_tamper_blocks_reuse(self):
        self.review_mutation=lambda r,v,a:r.pop('repair_stage');self.assertEqual(self.tick(),'retry_required')
        cache=next((self.run/'attempts').glob('*/executor-checkpoint.json'));saved=runner.read(cache)
        (cache.parent/saved['output']/'record/proof.md').write_text('tampered')
        with self.assertRaises(runner.CheckpointInvalid):self.tick()
        self.assertEqual(self.state()['events'],[])

    def test_source_contract_engine_and_receipt_tamper_stop_before_launch(self):
        runner.write(self.run/'contract.json',{'tampered':True})
        with self.assertRaises(core.Rejected):self.tick()
        self.assertEqual(self.calls,[])

    def test_engine_manifest_drift_blocks_dispatch(self):
        with patch.object(runner,'engine_manifest',return_value={}):
            with self.assertRaises(core.Rejected):self.tick()
        self.assertEqual(self.calls,[])

    def test_committed_evidence_tamper_blocks_dispatch(self):
        (runner.committed(self.run)/'record/proof.md').write_text('tampered')
        with self.assertRaises(core.Rejected):self.tick()
        self.assertEqual(self.calls,[])

    def test_worker_cannot_change_claim_or_stop(self):
        self.executor_mutation=lambda s,o,a:s.update(claim='an easier goal')
        self.assertEqual(self.tick(),'repair_queued');self.assertEqual(self.state()['claim'],'Close the exact fixture residual')

    def test_new_source_is_validated_against_effective_overlay(self):
        self.advance_to(6)
        def new_source(s,out,a):
            (out/'changes').mkdir();(out/'changes/New.lean').write_text('theorem Fixture.done : True := by trivial\n')
            s['implementation_chain']=dict(target='target',facts={'target':dict(statement='True',owner='fixture',path='New.lean',declaration='Fixture.done',dependencies=[],status='kernel_checked',kernel_targets=['New'],statement_evidence=['e'],publication_evidence=['e'])})
        self.executor_mutation=new_source;self.assertEqual(self.tick(),'accepted')
        self.assertIn('implementation_chain',self.state())


class BrokerDestinationTests(unittest.TestCase):
    def test_api_connect_allowed(self):
        for host in sorted(egress.ALLOWED):
            self.assertEqual(egress.destination(f'CONNECT {host}:443 HTTP/1.1'), host)

    def test_other_destinations_protocols_and_ports_denied(self):
        for line in ('CONNECT localhost:443 HTTP/1.1', 'CONNECT 127.0.0.1:443 HTTP/1.1',
                     'CONNECT [::1]:443 HTTP/1.1', 'CONNECT api.openai.com:80 HTTP/1.1',
                     'GET api.openai.com:443 HTTP/1.1', 'CONNECT api.openai.com.evil.test:443 HTTP/1.1',
                     'CONNECT api.openai.com@127.0.0.1:443 HTTP/1.1', 'invalid',
                     'CONNECT api.openai.com:443 HTTP/2'):
            with self.subTest(line=line), self.assertRaises(ValueError):
                egress.destination(line)



if __name__ == '__main__':
    unittest.main()

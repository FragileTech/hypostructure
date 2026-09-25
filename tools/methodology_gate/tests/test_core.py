"""Immutable proof state, review binding and significant-child transitions."""
import copy
import tempfile
import unittest
from pathlib import Path
from tools.methodology_gate import core
from tools.methodology_gate.tests.structural_fixtures import state, prefix, advance


class GateTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.path=Path(self.tmp.name);self.before=state(self.path)

    def check(self,b,a,stage,node='root'):
        core.validate_transition(b,a,self.path,node,stage)

    def reject(self,b,a,stage=1,node='root'):
        with self.assertRaises(core.Rejected): self.check(b,a,stage,node)

    def test_complete_nine_stage_fixture(self):
        b=self.before
        for stage in core.STAGE_ORDER:
            a=advance(b,stage);self.check(b,a,stage);b=a
        self.assertIsNone(core.next_node(b))
        self.assertEqual(core.record.validate(b,self.path,complete=True),[])

    def test_residual_aspect_needs_no_invented_owner_fact(self):
        b=advance(self.before,1)
        a=advance(b,2)
        a['events'][-1]['artifact']['aspects'][0]['facts']=[]
        self.check(b,a,2)

    def test_workflow_records_are_unversioned(self):
        for key in ('version','workflow_version'):
            a=advance(self.before,1);a[key]=1;self.reject(self.before,a)

    def test_locked_contract_and_local_residual(self):
        for key in ('claim','scope','root','methodology_sources'):
            a=advance(self.before,1);a[key]='changed';self.reject(self.before,a)
        for key in ('goal','residual','parent','id'):
            a=advance(self.before,1);a['nodes'][0][key]='changed';self.reject(self.before,a)

    def test_facts_cannot_be_weakened_deleted_or_assumed(self):
        for change in ('weaken','delete','assume'):
            a=advance(self.before,1)
            if change=='weaken':a['facts']['f']['statement']='projection'
            elif change=='delete':a['facts']={}
            else:a['facts']['new']=dict(statement='Needed capacity',kind='standing',evidence=['e'])
            self.reject(self.before,a)

    def test_evidence_and_history_are_immutable(self):
        a=advance(self.before,1);a['evidence']['e']['proves']='other';self.reject(self.before,a)
        b=prefix(self.path,2);a=advance(b,3);a['events'][0]['reason']='rewritten';self.reject(b,a,3)
        a=advance(self.before,1);(self.path/'proof.md').write_text('tampered');self.reject(self.before,a)

    def test_exactly_one_ordered_event_required(self):
        a=advance(self.before,1);a['events'][-1]['stage']=2;self.reject(self.before,a)
        a=advance(advance(self.before,1),2);self.reject(self.before,a)

    def test_worker_cannot_stop_or_restore_unavailable_input(self):
        for field,value in [('status','complete'),('quarantined_facts',['f']),('unnecessary_facts',['f'])]:
            a=advance(self.before,1);a[field]=value;self.reject(self.before,a)

    def test_failed_stage_cannot_close(self):
        a=advance(self.before,1);a['events'][-1].update(result='failed',failure=dict(field='evidence',reason='missing',retained_prefix='R',evidence=['e']))
        a['nodes'][0].update(status='closed',certificate=['e']);a['queue']=[];self.reject(self.before,a)

    def test_reduction_requires_significance_and_all_edge_proofs(self):
        b=prefix(self.path,5,'significant_reduction');a=advance(b,6);self.check(b,a,6)
        for key in ('refinement','coverage','consumption','continuation'):
            broken=copy.deepcopy(a);broken['nodes'][0].pop(key);self.reject(b,broken,6)
        a['nodes'][-1]['reduction'].pop('significance');self.reject(b,a,6)

    def test_children_run_only_after_construction_and_before_outcomes(self):
        b=prefix(self.path,6,'significant_reduction');self.assertEqual(core.next_node(b),'root-child')
        self.reject(b,advance(b,7),7)
        for stage in core.STAGE_ORDER:
            a=advance(b,stage,'root-child');self.check(b,a,stage,'root-child');b=a
        self.assertEqual(core.next_node(b),'root')
        a=advance(b,7);self.check(b,a,7)

    def test_parent_retains_full_child_facts_and_no_sibling_leak(self):
        b=prefix(self.path,6,'significant_reduction');a=advance(b,1,'root-child')
        a['nodes'][1]['facts']=[];self.reject(b,a,1,'root-child')
        a=advance(b,1,'root-child');a['nodes'][0]['goal']='altered';self.reject(b,a,1,'root-child')

    def test_existing_sibling_premises_cannot_be_attached_by_id(self):
        b=prefix(self.path,5,'significant_reduction')
        left=b['events'][-1]['artifact']['outcomes'][0];left['case']='left'
        right=copy.deepcopy(left);right['case']='right'
        b['events'][-1]['artifact']['outcomes'].append(right)
        a=advance(b,6)
        a['events'][-1]['artifact']['outcomes'][1]['child']='right-child'
        sibling=copy.deepcopy(a['nodes'][1]);sibling['id']='right-child'
        a['nodes'].append(sibling);a['nodes'][0]['children'].append('right-child')
        a['queue'].append('right-child')
        a['facts']['left-case']=dict(statement='The left-only case holds',kind='case',evidence=['e'])
        a['nodes'][1]['facts'].append('left-case')
        self.check(b,a,6);b=a
        for stage in core.STAGE_ORDER:
            a=advance(b,stage,'root-child')
            if stage==6:
                a['facts']['left-derived']=dict(statement='A consequence on the left case',kind='derived',evidence=['e'])
                a['nodes'][1]['facts'].append('left-derived')
            self.check(b,a,stage,'root-child');b=a
        self.assertEqual(core.next_node(b),'right-child')
        for stage in core.STAGE_ORDER[:core.STAGE_ORDER.index(6)+1]:
            for fact_id in ('left-case','left-derived'):
                with self.subTest(stage=stage,fact=fact_id):
                    a=advance(b,stage,'right-child',kind='significant_reduction')
                    a['nodes'][2]['facts'].append(fact_id)
                    self.reject(b,a,stage,'right-child')
                if stage==6:
                    with self.subTest(stage=stage,fact=fact_id,new_child=True):
                        a=advance(b,stage,'right-child',kind='significant_reduction')
                        a['nodes'][-1]['facts'].append(fact_id)
                        self.reject(b,a,stage,'right-child')
            a=advance(b,stage,'right-child',kind='significant_reduction')
            if stage==5:
                a['events'][-1]['artifact']['outcomes'][0]['remaining_residual']='Full fixture R with disjoint supports and distinct labels'
            self.check(b,a,stage,'right-child');b=a

    def test_outcomes_cannot_leave_open_leaf(self):
        b=prefix(self.path,6);a=advance(b,7);a['nodes'][0].update(status='open');a['queue']=['root'];self.reject(b,a,7)

    def test_unresolved_quarantine_blocks_completion_not_accounting(self):
        b=copy.deepcopy(self.before);b['quarantined_facts']=['f'];a=advance(b,1);self.check(b,a,1)
        b=prefix(self.path,6);b['quarantined_facts']=['f'];a=advance(b,7);self.reject(b,a,7)
        b['unnecessary_facts']=['f'];a=advance(b,7);self.check(b,a,7)

    def test_verification_cannot_rewrite_math_or_implementation(self):
        b=prefix(self.path,7);a=advance(b,8);a['implementation_chain']={'target':'other'};self.reject(b,a,8)
        a=advance(b,8);a['nodes'][0]['certificate']=['e','e'];self.reject(b,a,8)

    def review(self,stage=1):
        ref={k:self.before['evidence']['e'][k] for k in ('path','sha256','locator')}
        return dict(binding='bound',decision='accept',gates={g:dict(verdict='pass',reason='Independently checked fixture',evidence=[copy.deepcopy(ref)]) for g in core.COMMON_GATES+core.STAGE_GATES[stage]},first_failure='',repair='',repair_stage=stage,accepted_stage_revocation=None,reviewed_facts=[])

    def test_review_requires_every_gate_and_current_binding(self):
        r=self.review();core.validate_review(r,'bound',1,self.path)
        for change in ('binding','missing','fail','empty','hash'):
            r=self.review();gate=r['gates']['full_residual']
            if change=='binding':r['binding']='stale'
            elif change=='missing':r['gates'].pop('full_residual')
            elif change=='fail':gate['verdict']='fail'
            elif change=='empty':gate['reason']=''
            else:gate['evidence'][0]['sha256']='wrong'
            with self.assertRaises(core.Rejected):core.validate_review(r,'bound',1,self.path)

    def test_failed_reasoning_stage_cannot_be_accepted_as_an_outcome(self):
        submitted=advance(self.before,1)
        submitted['events'][-1].update(result='failed',failure=dict(field='residual_components',
            reason='No productive aspect found',retained_prefix='Exact residual R',evidence=['e']))
        record=self.path/'record';record.mkdir(exist_ok=True)
        import json
        (record/'state.json').write_text(json.dumps(submitted))
        with self.assertRaises(core.Rejected):
            core.validate_review(self.review(1),'bound',1,self.path)
        review=self.review(1);review.update(decision='reject',first_failure='Residual component classification is incomplete',
            repair='Reconstruct the bound residual cases',repair_stage=1)
        review['gates']['residual_centric_analysis']['verdict']='fail'
        core.validate_review(review,'bound',1,self.path)

    def test_rejected_construction_must_invalidate_authorization(self):
        r=self.review(6);r.update(decision='reject',first_failure='failed output',repair='Repair authorization')
        r['gates']['actual_proof_advancement']['verdict']='fail'
        with self.assertRaises(core.Rejected):core.validate_review(r,'bound',6,self.path)
        r['repair_stage']=5
        r['accepted_stage_revocation']=dict(stage=5,defect='The accepted authorization is defective',
            evidence=copy.deepcopy(r['gates']['full_residual']['evidence']))
        core.validate_review(r,'bound',6,self.path)

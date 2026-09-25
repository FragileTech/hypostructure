"""Structural gate regressions: advancement, stage separation and noncosmetic repair."""
import copy
import tempfile
import unittest
from pathlib import Path
from tools.methodology_gate.policy import workflow as w
from tools.methodology_gate.tests.structural_fixtures import prefix, advance, outcome


class StructuralWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.path=Path(self.tmp.name)

    def pair(self,stage,kind='closure'):
        before=prefix(self.path,stage-1,kind); return before,advance(before,stage,kind=kind)

    def errors(self,before,after,stage):
        return w.validate_artifact(before,after,'root',stage)

    def test_all_stages_have_valid_separate_contracts(self):
        for stage in range(1,9):
            with self.subTest(stage=stage):
                b,a=self.pair(stage); self.assertEqual(self.errors(b,a,stage),[])

    def test_all_three_closure_mechanisms_allowed(self):
        for mechanism in w.MECHANISMS:
            b,a=self.pair(5); a['events'][-1]['artifact']['outcomes']=[outcome(mechanism=mechanism)]
            self.assertEqual(self.errors(b,a,5),[])

    def test_padding_unchanged_x1_burden_rejected(self):
        b,a=self.pair(5,'significant_reduction'); arm=a['events'][-1]['artifact']['outcomes'][0]
        arm.update(before='X1 response and representative obligations',after='X1 response and representative obligations',
                   excluded_structure='padding',significance='support is shorter')
        self.assertTrue(self.errors(b,a,5))

    def test_lemma_diagnostic_routing_and_cosmetic_outputs_rejected(self):
        for kind in ('required_lemma','diagnostic','routing','strict_reduction','paid_field','smaller_encoding'):
            with self.subTest(kind=kind):
                b,a=self.pair(5); a['events'][-1]['artifact']['outcomes'][0]['kind']=kind
                self.assertTrue(self.errors(b,a,5))

    def test_reduction_requires_excluded_structure_significance_and_full_survivor(self):
        for key in ('excluded_structure','significance','remaining_residual','continuation','measure','strictness_evidence'):
            b,a=self.pair(5,'significant_reduction'); del a['events'][-1]['artifact']['outcomes'][0][key]
            self.assertTrue(self.errors(b,a,5),key)

    def test_unproductive_complementary_arm_cannot_hide_behind_closure(self):
        b,a=self.pair(5); arm=outcome(); arm.update(case='failure',kind='required_lemma')
        a['events'][-1]['artifact']['outcomes'].append(arm)
        self.assertTrue(self.errors(b,a,5))

    def test_no_property_coverage_or_partial_inventory_is_rejected(self):
        b,a=self.pair(2); a['events'][-1]['artifact']['coordinates'].pop()
        self.assertTrue(self.errors(b,a,2))

    def test_inventory_must_classify_every_residual_bound_component(self):
        b,a=self.pair(2)
        a['events'][-1]['artifact']['component_classifications'][0]['component_id']='invented-component'
        self.assertTrue(self.errors(b,a,2))

    def test_conflict_must_cover_each_aspect_on_every_residual_case(self):
        b,a=self.pair(3)
        a['events'][-1]['artifact']['residual_case_assessments'].clear()
        self.assertTrue(self.errors(b,a,3))

    def test_unknown_or_quarantined_property_cannot_support_selection(self):
        for mode in ('unknown','sibling','quarantined'):
            b,a=self.pair(2)
            if mode=='unknown': a['events'][-1]['artifact']['coordinates'][0]['status']='unresolved'
            elif mode=='sibling': a['events'][-1]['artifact']['aspects'][0]['facts']=['sibling']
            else: b['quarantined_facts']=['f']
            self.assertTrue(self.errors(b,a,2),mode)

    def test_no_techniques_in_inventory_or_structural_ranking(self):
        for stage in (2,3):
            b,a=self.pair(stage); a['events'][-1]['artifact']['selected_move']='try deletion'
            self.assertTrue(self.errors(b,a,stage))

    def test_failed_early_stage_cannot_bypass_boundary(self):
        for stage in range(1,6):
            b,a=self.pair(stage); e=a['events'][-1]
            e.update(result='failed',failure=dict(field='X1',reason='attempt failed',retained_prefix='full R',evidence=['e'],attempt='try padding deletion'))
            self.assertTrue(self.errors(b,a,stage))

    def test_no_new_lemma_can_be_published_before_authorization(self):
        for stage in range(1,6):
            b,a=self.pair(stage); a['facts']['padding']=dict(statement='Padding lemma',kind='derived',evidence=['e'])
            a['nodes'][0]['facts'].append('padding'); self.assertTrue(self.errors(b,a,stage))

    def test_cannot_omit_stronger_unused_aspect(self):
        b,a=self.pair(3)
        alt=copy.deepcopy(b['events'][1]['artifact']['aspects'][0]);alt.update(id='stronger',statement='A stronger unused restriction')
        b['events'][1]['artifact']['aspects'].append(alt)
        a['events'][-1]['inputs']=w.bindings(b,'root',3)
        self.assertTrue(self.errors(b,a,3))

    def test_unsupported_alternative_does_not_block_a_target_relevant_selection(self):
        b,a=self.pair(3)
        alt=copy.deepcopy(b['events'][1]['artifact']['aspects'][0]);alt.update(id='weak',statement='No known relevant conflict')
        b['events'][1]['artifact']['aspects'].append(alt)
        e=a['events'][-1];e['inputs']=w.bindings(b,'root',3);art=e['artifact']
        c=copy.deepcopy(art['comparisons'][0]);c.update(aspect_id='weak',structural_status='unsupported',opposing_accounts=[])
        art['comparisons'].append(c);art['ranking'].append('weak');art['strongest_alternative']='weak'
        weak_case=copy.deepcopy(art['residual_case_assessments'][0]);weak_case.update(aspect_id='weak',case_groups=copy.deepcopy(weak_case['case_groups']))
        weak_case['case_groups'][0]['structural_status']='unsupported'
        art['residual_case_assessments'].append(weak_case)
        self.assertEqual(self.errors(b,a,3),[])
        art['ranking'].reverse();art['selected_aspect']='weak';art['strongest_alternative']='lower'
        self.assertTrue(self.errors(b,a,3))

    def test_stage3_cannot_select_without_a_target_residual_handle(self):
        b,a=self.pair(3)
        art=a['events'][-1]['artifact']
        art['comparisons'][0]['structural_status']='unsupported'
        art['residual_case_assessments'][0]['case_groups'][0]['structural_status']='unsupported'
        self.assertTrue(self.errors(b,a,3))

    def test_catalogue_requires_every_attached_family(self):
        b,a=self.pair(4);a['events'][-1]['artifact']['techniques'].pop();self.assertTrue(self.errors(b,a,4))

    def test_selected_technique_cannot_assume_missing_prerequisite(self):
        b,a=self.pair(5);next(e for e in b['events'] if e['stage']==4)['artifact']['techniques'][0]['status']='missing_prerequisite'
        a['events'][-1]['inputs']=w.bindings(b,'root',5);self.assertTrue(self.errors(b,a,5))

    def test_authorization_must_cover_all_incoming_residual_cases(self):
        b,a=self.pair(5)
        a['events'][-1]['artifact']['outcomes'][0]['residual_case_ids']=[]
        self.assertTrue(self.errors(b,a,5))

    def test_bindings_prevent_posthoc_aspect_output_and_consumer_substitution(self):
        for key in ('aspect_id','operation','object','output','candidate_id','residual_binding'):
            b,a=self.pair(5);a['events'][-1]['artifact'][key]='substituted';self.assertTrue(self.errors(b,a,5),key)
        b,a=self.pair(6);a['events'][-1]['artifact']['authorization_binding']='stale';self.assertTrue(self.errors(b,a,6))

    def test_missing_or_stale_authorization_blocks_dispatch(self):
        b,_=self.pair(6);self.assertEqual(w.dispatch_errors(b,'root',6),[])
        b['facts']['f']['statement']='Changed';self.assertTrue(w.dispatch_errors(b,'root',6))
        b['events'].pop();self.assertTrue(w.dispatch_errors(b,'root',6))

    def test_execution_cannot_return_only_a_lemma_or_omit_outcomes(self):
        for mutation in ('lemma','omission'):
            b,a=self.pair(6)
            if mutation=='lemma':a['events'][-1]['artifact']['outcomes'][0]['kind']='required_lemma'
            else:a['events'][-1]['artifact']['outcomes']=[]
            self.assertTrue(self.errors(b,a,6))

    def test_significant_reduction_constructs_exact_child(self):
        b,a=self.pair(6,'significant_reduction');self.assertEqual(self.errors(b,a,6),[])
        a['nodes'][-1]['residual']='Unchanged R';self.assertTrue(self.errors(b,a,6))

    def test_repair_invalidates_only_dependent_decisions(self):
        b=prefix(self.path,5)
        b['events'].append(dict(node='root',stage=6,result='failed',restart_stage=4,evidence=['e']))
        self.assertEqual(set(w.active_artifacts(b,'root')),{1,2,3,'3b'})
        self.assertIsNone(w.authorization(b,'root'))

    def test_failed_technique_not_property_is_exhausted(self):
        b=prefix(self.path,5);plan=b['events'][-1]['artifact']
        b['events'].append(dict(node='root',stage=6,result='failed',restart_stage=5,evidence=['e'],attempted_technique=w.technique_signature(plan)))
        a=advance(b,5);self.assertTrue(self.errors(b,a,5))
        # An actually different catalogued operation on the same property may be reviewed.
        next(e for e in b['events'] if e['stage']==4)['artifact']['techniques'][0]['operation']='A substantively different operation'
        a=advance(b,5);a['events'][-1]['artifact']['operation']='A substantively different operation'
        self.assertEqual(self.errors(b,a,5),[])

    def test_failed_same_technique_needs_actual_new_evidence(self):
        b=prefix(self.path,5);plan=b['events'][-1]['artifact']
        b['events'].append(dict(node='root',stage=6,result='failed',restart_stage=5,evidence=['e'],attempted_technique=w.technique_signature(plan)))
        a=advance(b,5);art=a['events'][-1]['artifact'];art['retry']=dict(kind='corrected_construction',change='Specific repaired witness',evidence=['e'])
        self.assertTrue(self.errors(b,a,5))
        a['evidence']['new']=copy.deepcopy(a['evidence']['e']);art['retry']['evidence']=['new']
        self.assertEqual(self.errors(b,a,5),[])

    def test_renaming_only_aspect_id_does_not_enable_failed_technique(self):
        b=prefix(self.path,5)
        attempted=w.technique_signature(b['events'][-1]['artifact'])
        b['events'].append(dict(node='root',stage=6,result='failed',restart_stage=5,
                               evidence=['e'],attempted_technique=attempted))
        a=advance(b,5);art=a['events'][-1]['artifact']
        art['aspect_id']='lower-renamed'
        self.assertTrue(self.errors(b,a,5),
                        'Changing only the aspect label cannot authorize the same failed argument')
        self.assertNotIn('retry',art)

    def test_repair_reuses_unchanged_verified_child(self):
        b=prefix(self.path,6,'significant_reduction')
        b['events'].append(dict(node='root',stage=7,result='failed',restart_stage=5,evidence=['e']))
        b=advance(b,5,kind='significant_reduction');a=advance(b,6)
        self.assertEqual(len(a['nodes']),2);self.assertEqual(self.errors(b,a,6),[])

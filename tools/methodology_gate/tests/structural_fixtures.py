"""Deterministic structural fixtures; mock review is never mathematical certification."""
import copy
import hashlib
from tools.methodology_gate import core
from tools.methodology_gate.policy import workflow as w


def state(directory):
    proof = directory / 'proof.md'
    proof.write_text('Fixture: a retained positive integer n has a previously used upper bound n <= 2.\n'
                     'The retained source also forces n >= 3, not yet used against this bound.\n'
                     'Conditional output: n >= 3. Together these imply 3 <= 2, a contradiction.\n')
    return dict(claim='Close the exact fixture residual',
        scope='Fixture only', status='active', methodology_sources=copy.deepcopy(core.record.SOURCES), root='root',
        facts={'f':dict(statement='The complete fixture residual holds',kind='standing',evidence=['e'])},
        evidence={'e':dict(path='proof.md',sha256=hashlib.sha256(proof.read_bytes()).hexdigest(),locator='entire fixture',proves='Retained fixture and conditional argument')},
        nodes=[dict(id='root',parent=None,goal='Close the exact fixture residual',residual='Full fixture R',facts=['f'],status='open',children=[])],
        queue=['root'],events=[],semantic_review=[])


def outcome(kind='closure', mechanism='constraint'):
    if kind == 'closure':
        return dict(case='all',condition='Every retained object',consumer='Original residual contradiction',
                    residual_case_ids=['case-all'],kind=kind,mechanism=mechanism,
                    contradiction='The retained requirements are incompatible',evidence=['e'])
    return dict(case='all',condition='Every surviving object',consumer='Residual structural continuation',kind=kind,
        residual_case_ids=['case-all'],
        object='original object',before='all retained configurations',after='only configurations without overlap',
        excluded_structure='the entire overlapping-support family',significance='eliminates the sole independent overlap obstruction',
        remaining_residual='Full fixture R with disjoint supports',continuation='Apply the exact disjoint-support consumer',
        measure='number of independent overlap freedoms',reduction_kind='structural_exclusion',
        strictness_evidence=['e'],evidence=['e'])


def artifact(before, stage, node='root', kind='closure'):
    a=w.active_artifacts(before,node)
    if stage == 1:
        return dict(prior_uses=[dict(id='upper',property_ids=['A01'],
                    structure='The retained integer n has an upper bound n <= 2',
                    move='Apply the upstream order bound',
                    effect_on_residual='Restricts the fixed n to n <= 2',evidence=['e'])],
                    coverage_evidence=['e'])
    if stage == 2:
        return dict(residual_components=[dict(id='order',kind='conjunction',
                    exact_statement='The retained integer n satisfies n <= 2 and n >= 3',
                    binders_and_domains='n is the fixed integer of the fixture',
                    current_object_link='The residual concerns the same fixed n',evidence=['e'])],
            coordinates=[dict(property_id=p,status='present' if p=='A01' else 'not_applicable',reason='Fixture order coordinate' if p=='A01' else 'Integer fixture has no such graph structure',evidence=['e']) for p in w.PROPERTIES],
            aspects=[dict(id='lower',property_ids=['A01'],statement='n >= 3',observable='retained integer order',object='n',prior_use='The Stage 1 upper-bound move',unused_difference='The lower bound remains unused against it',facts=['f'],status='unaccounted',evidence=['e'])],
            interactions=[],interaction_coverage_evidence=['e'],
            component_classifications=[dict(component_id='order',classification='Compare the two retained bounds on the same fixed n',
                relation_to_fixed_objects='Both constraints apply to the fixed integer n',exhaustiveness='The exact conjunction has one case: the fixed n must satisfy both bounds',
                remaining_obligation='Derive the direct order contradiction',evidence=['e'],cases=[dict(id='case-all',condition='n <= 2 and n >= 3',
                    established_consequence='The two bounds are incompatible',status='forced',evidence=['e'])])])
    if stage == 3:
        return dict(comparisons=[dict(aspect_id='lower',opposing_accounts=['upper'],structural_conflict='Lower bound exceeds upper bound',
                consequence='3 <= n <= 2',affected_residual_clause='The conjunction of bounds on the same n',
                structural_status='target_relevant',evidence=['e'])],
            residual_case_assessments=[dict(aspect_id='lower',case_groups=[dict(case_ids=['case-all'],
                structural_conflict='Lower bound exceeds upper bound',consequence='3 <= n <= 2',
                affected_residual_clause='The conjunction of bounds on the same n',
                structural_status='target_relevant',evidence=['e'])])],
            ranking=['lower'],selected_aspect='lower',strongest_alternative=None,selection_reason='Direct same-witness incompatibility',
            structural_opportunity=dict(bound_witness='The fixed integer n in case-all',prior_account_ids=['upper'],
                shared_structure='Both restrictions concern the same n',retained_restrictions='n <= 2 and n >= 3',
                deduction='The restrictions force 3 <= 2',affected_residual_clause='The conjunction of bounds on n',
            stage4_opportunity='Compare the exact lower and upper bounds',weakest_case_id='case-all',
            weakest_case_analysis='This sole case contains both incompatible bounds',evidence=['e']),evidence=['e'])
    if stage == '3b':
        fact_id='sf' if node=='root' else node+'-sf'
        return dict(residual_binding=w.residual_binding(before,node),selected_aspect='lower',
            incoming_residual_key='fixture.residual',lean_inputs=['fixture.residual'],
            ledger_row='Fixture.lower_bound',
            structure_fact_id=fact_id,structure_key='fixture.lower',lean_declaration='Fixture.lower_bound',
            bound_witness=a[3]['artifact']['structural_opportunity']['bound_witness'],
            source_path='Fixture.lean',weakest_case_id='case-all',
            claim_projections=[dict(claim='The lower bound holds for this n',
                declaration='Fixture.lower_bound',residual_clause='n >= 3',
                bound_witness=a[3]['artifact']['structural_opportunity']['bound_witness'],
                evidence=['e'])],evidence=['e'])
    if stage == 4:
        fact_id='sf' if node=='root' else node+'-sf'
        return dict(aspect_id='lower',structure_fact_id=fact_id,structure_binding=w.digest(a['3b']),
            techniques=[dict(id='inequality',technique_id='T01',status='candidate',reason='Direct bound comparison',evidence=['e'],theorem='Order transitivity: a <= n <= b implies a <= b',operation='Compare exact bounds',object='n',output='n >= 3',dependency_step='Use the independent lower bound',history_comparison='Lower bound not previously consumed',residual_case_ids=['case-all'],structure_fact_id=fact_id,prerequisites=[dict(statement='3 <= n and n <= 2',witness_binding='The same fixed n in the structure and f',derivation='Combine the checked structure with the retained upper bound',evidence=['e'])],payoff_composition=dict(selected_output='n >= 3',prior_restrictions='n <= 2',retained_estimates='Exact upper bound 2',derivation='3 <= n <= 2 contradicts arithmetic',resulting_conflict_or_bound='3 <= 2',before='n satisfies both bounds',after='no such n',weakest_case='case-all',direct_consumer='Original residual contradiction',evidence=['e'])),
            dict(id='extremal',technique_id='T02',status='excluded',reason='Direct contradiction is stronger and needs no replacement',evidence=['e'])],coverage_evidence=['e'],selected_candidate_id='inequality',selection_reason='Direct closure on the same n',strongest_alternative='extremal',selection_evidence=['e'])
    if stage == 5:
        return dict(residual_binding=w.residual_binding(before,node),aspect_id='lower',candidate_id='inequality',technique_id='T01',operation='Compare exact bounds',object='n',output='n >= 3',consumer='Original residual contradiction',dependency_test='Without the unused lower bound the upper bound alone gives no contradiction',dependency_evidence=['e'],comparison='Direct closure dominates extremal replacement',comparison_evidence=['e'],weakest_outcome='The single exhaustive case closes',coverage_evidence=['e'],payoff_evidence=['e'],history_evidence=['e'],outcomes=[outcome(kind)])
    if stage == 6:
        plan=w.authorization(before,node)
        arms=[]
        for x in plan['artifact']['outcomes']:
            arm=dict(case=x['case'],kind=x['kind'],evidence=['e'],application_evidence=['e'])
            if x['kind']=='significant_reduction':
                arm['child']=node+'-child'
            arms.append(arm)
        return dict(authorization_binding=plan['binding'],output_evidence=['e'],application_evidence=['e'],preservation_evidence=['e'],outcomes=arms)
    if stage == 7:
        return dict(construction_binding=w.digest(a[6]),discharges={x['case']:['e'] for x in a[6]['artifact']['outcomes']},account_updates=['e'],evidence=['e'])
    return dict(outcome_binding=w.digest(a[7]),statement_evidence=['e'],implementation_evidence=['e'],wiring_evidence=['e'],artifact_evidence=['e'])


def advance(before, stage, node='root', kind='closure'):
    after=copy.deepcopy(before)
    event=dict(node=node,stage=stage,result='done',evidence=['e'],inputs=w.bindings(before,node,stage),
               artifact=artifact(before,stage,node,kind),reason='Execute the exact next stage or reviewed repair')
    after['events'].append(event)
    current=next(n for n in after['nodes'] if n['id']==node)
    if stage=='3b':
        fact_id='sf' if node=='root' else node+'-sf'
        after['facts'][fact_id]=dict(statement='The selected lower bound holds for the same fixed n',kind='derived',evidence=['e'])
        current['facts'].append(fact_id)
    if stage==6:
        for arm in w.authorization(before,node)['artifact']['outcomes']:
            if arm['kind']=='significant_reduction':
                child=node+'-child'
                current.update(status='expanded',children=[child],refinement=['e'],coverage=['e'],consumption=['e'],continuation=['e'])
                if not any(n['id']==child for n in after['nodes']):
                    after['nodes'].append(dict(id=child,parent=node,goal=current['goal'],residual=arm['remaining_residual'],facts=list(current['facts']),status='open',children=[],
                        reduction=dict(from_=node)))
                    new=after['nodes'][-1]
                    new['reduction']={'from':node,'kind':arm['reduction_kind'],'strictness':'All overlapping configurations excluded',
                        'excluded_structure':arm['excluded_structure'],'significance':arm['significance'],'evidence':['e']}
                after['queue']=[n['id'] for n in after['nodes'] if n['status']=='open']
    if stage==7:
        if not current['children']:
            current.update(status='closed',certificate=['e'])
        after['queue']=[n['id'] for n in after['nodes'] if n['status']=='open']
    if stage==8:
        after['semantic_review']=['e']
        if node==after['root']:
            after['status']='complete'
    return after


def prefix(directory, count, kind='closure'):
    current=state(directory)
    for stage in w.STAGE_ORDER:
        if isinstance(stage,int) and stage>count:
            break
        current=advance(current,stage,kind=kind)
    return current

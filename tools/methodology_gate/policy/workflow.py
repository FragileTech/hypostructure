"""Unversioned structural reasoning contracts with mandatory residual-focused review."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).parent
SPEC = json.loads((ROOT / 'workflow.json').read_text())
REGISTER = json.loads((ROOT / 'structural-register.json').read_text())
STAGES = {s['number']: s for s in SPEC['stages']}
STAGE_ORDER = tuple(s['number'] for s in SPEC['stages'])
COMMON_GATES = tuple(SPEC['common_gates'])
STAGE_GATES = {n: tuple(s['gates']) for n, s in STAGES.items()}
PROPERTIES = {p['id']: p for g in REGISTER['groups'] for p in g['properties']}
TECHNIQUES = {t['id']: t for t in REGISTER['techniques']}
MECHANISMS = ('constraint', 'compression', 'quantity')


def ordinal(stage):
    return STAGE_ORDER.index(stage)


def successor(stage):
    position = ordinal(stage) + 1
    return STAGE_ORDER[position] if position < len(STAGE_ORDER) else 9


def predecessors(stage):
    return STAGE_ORDER[:ordinal(stage)]


def before(left, right):
    return ordinal(left) < ordinal(right)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def repair_stage(event):
    return event.get('restart_stage', STAGES[event['stage']]['repair_stage'])


def active_artifacts(state, node):
    active = {}
    for event in state['events']:
        if event['node'] != node:
            continue
        start = event['stage'] if event['result'] == 'done' else repair_stage(event)
        active = {n: e for n, e in active.items() if before(n, start)}
        if event['result'] == 'done':
            active[event['stage']] = event
    return active


def bindings(state, node, stage):
    return {str(n): digest(e) for n, e in active_artifacts(state, node).items() if before(n, stage)}


def residual_binding(state, node):
    owner = next(n for n in state['nodes'] if n['id'] == node)
    return digest({'claim': state['claim'], 'node': node, 'residual': owner['residual'],
                   'goal': owner['goal'], 'facts': {f: state['facts'][f] for f in owner['facts']},
                   'quarantine': sorted(set(owner['facts']) & set(state.get('quarantined_facts', [])))})


def authorization(state, node):
    event = active_artifacts(state, node).get(5)
    if not event:
        return None
    return {'binding': digest(event), 'artifact': event['artifact']}


def dispatch_errors(state, node, stage):
    active = active_artifacts(state, node)
    if set(active) != set(predecessors(stage)):
        return ['Every preceding reasoning stage must have an active independently reviewed artifact.']
    if stage == 4:
        certificate = active['3b']['artifact']
        owner = next(n for n in state['nodes'] if n['id'] == node)
        if certificate.get('structure_fact_id') not in owner['facts']:
            return ['Stage 4 requires the reviewed Stage 3b fact on this node.']
    if stage == 6:
        plan = authorization(state, node)
        if not plan or plan['artifact'].get('residual_binding') != residual_binding(state, node):
            return ['Construction authorization is missing or stale for the exact retained residual.']
    return []


def attempt_history(state, node):
    nodes = {n['id']: n for n in state['nodes']}
    lineage = {node}
    parent = nodes[node]['parent']
    while parent is not None:
        lineage.add(parent)
        parent = nodes[parent]['parent']
    return [e['attempted_technique'] for e in state['events']
            if e['node'] in lineage and e.get('attempted_technique')]


def technique_signature(plan):
    # Inventory labels may change during repair; they do not make an attempt new.
    return {k: plan[k] for k in ('technique_id', 'operation', 'object', 'output')}


def validate_artifact(before, after, node, stage):
    """Validate submitted evidence indexes without claiming mathematical truth."""
    errors = []
    event = after['events'][-1]
    artifact = event.get('artifact')
    evidence = after['evidence']
    active = active_artifacts(before, node)
    def need(ok, message):
        if not ok:
            errors.append(message)
        return bool(ok)
    def text(value):
        return isinstance(value, str) and bool(value.strip())
    def refs(value):
        return isinstance(value, list) and bool(value) and all(isinstance(x, str) and x in evidence for x in value)
    def strings(value):
        return isinstance(value, list) and all(text(x) for x in value)
    def fields(value, names, label):
        return need(isinstance(value, dict) and all(text(value.get(k)) for k in names), label)
    def normalized(value):
        return ' '.join(str(value).casefold().split())
    def rows(value, label, nonempty=True):
        if not need(isinstance(value, list) and (bool(value) or not nonempty) and
                    all(isinstance(x, dict) for x in value), label):
            return []
        return value
    def payoff(arm):
        if not fields(arm, ('case', 'condition', 'consumer'), 'Every outcome needs its condition and exact consumer'):
            return
        need(arm.get('kind') in ('closure', 'significant_reduction'),
             'Only closure or significant residual reduction is a productive outcome; an auxiliary lemma is insufficient')
        need(refs(arm.get('evidence')), 'Every outcome needs a conditional payoff proof')
        if arm.get('kind') == 'closure':
            need(arm.get('mechanism') in MECHANISMS and text(arm.get('contradiction')),
                 'Closure must specify constraint, compression or quantity and the exact contradiction')
        if arm.get('kind') == 'significant_reduction':
            required = ('object', 'before', 'after', 'excluded_structure', 'significance',
                        'remaining_residual', 'continuation', 'measure')
            if fields(arm, required, 'Reduction must describe excluded structure, significance, before/after, measure and full continuation'):
                need(normalized(arm['before']) != normalized(arm['after']),
                     'An unchanged burden cannot authorize construction')
                need(normalized(arm['remaining_residual']) != normalized(arm['before']),
                     'The surviving residual cannot be the unchanged incoming burden')
            need(arm.get('reduction_kind') in ('structural_exclusion', 'quantitative_restriction', 'well_founded_descent'),
                 'Bookkeeping, arbitrary partitions and smaller auxiliary objects are not significant reductions')
            need(refs(arm.get('strictness_evidence')), 'Significant reduction needs a proved strict conditional restriction')

    need(not dispatch_errors(before, node, stage), '; '.join(dispatch_errors(before, node, stage)))
    allowed = {'node', 'stage', 'result', 'evidence', 'artifact', 'inputs', 'reason', 'failure'}
    need(set(event) <= allowed, 'Unexpected event fields; use the exact stage contract')
    need(event.get('inputs') == bindings(before, node, stage), 'Stage inputs must bind every exact accepted predecessor artifact')
    if not need(isinstance(artifact, dict), 'Each stage requires its own artifact object'):
        return errors
    if event['result'] == 'failed':
        failure = event.get('failure', {})
        fields(failure, ('field', 'reason', 'retained_prefix'), 'Failure must identify the exact field, reason and retained prefix')
        need(refs(failure.get('evidence')), 'Failure needs actual reasoning or authorized construction evidence')
        if stage == 6:
            plan = authorization(before, node)
            need(artifact.get('authorization_binding') == (plan or {}).get('binding'),
                 'Even a failed construction must bind an already approved authorization')
            fields(failure, ('attempt',), 'Construction failure requires the actual authorized attempt')
        else:
            need('attempt' not in failure, 'A failed reasoning stage cannot authorize a construction attempt')
    # Apply stage boundaries also to failures; incomplete fields never grant a waiver.
    permitted = {
        1: {'prior_uses', 'coverage_evidence'},
        2: {'residual_components', 'coordinates', 'aspects', 'interactions', 'interaction_coverage_evidence', 'component_classifications'},
        3: {'comparisons', 'residual_case_assessments', 'ranking', 'selected_aspect', 'strongest_alternative', 'selection_reason', 'structural_opportunity', 'evidence'},
        '3b': {'residual_binding', 'selected_aspect', 'incoming_residual_key',
               'lean_inputs', 'ledger_row', 'structure_fact_id', 'structure_key',
               'lean_declaration', 'bound_witness', 'source_path',
               'claim_projections', 'weakest_case_id', 'evidence'},
        4: {'aspect_id', 'structure_fact_id', 'structure_binding', 'techniques', 'coverage_evidence',
            'selected_candidate_id', 'selection_reason', 'strongest_alternative', 'selection_evidence'},
        5: {'residual_binding', 'aspect_id', 'candidate_id', 'technique_id', 'operation', 'object', 'output',
            'consumer', 'dependency_test', 'dependency_evidence', 'comparison', 'comparison_evidence',
            'weakest_outcome', 'coverage_evidence', 'payoff_evidence', 'outcomes', 'retry', 'history_evidence'},
        6: {'authorization_binding', 'output_evidence', 'application_evidence', 'preservation_evidence', 'outcomes'},
        7: {'construction_binding', 'discharges', 'account_updates', 'evidence'},
        8: {'outcome_binding', 'statement_evidence', 'implementation_evidence', 'wiring_evidence', 'artifact_evidence'},
    }
    need(set(artifact) <= permitted[stage], 'Artifact contains work outside the assigned stage boundary')
    if stage in (1, 2, 3, '3b', 4, 5):
        old_nodes = {n['id']: n for n in before['nodes']}
        need(set(old_nodes) == {n['id'] for n in after['nodes']}, 'Reasoning stages cannot construct proof-tree children')
        for n in after['nodes']:
            old = old_nodes.get(n['id'], {})
            need(n.get('status') == old.get('status') and n.get('children') == old.get('children'),
                 'Reasoning stages cannot claim closure or expand the proof tree')
    if stage not in ('3b', 6):
        need(after['facts'] == before['facts'], 'This stage cannot publish new construction facts')
    if event['result'] == 'failed':
        return errors  # An honestly incomplete artifact is not an authorization.

    owner = next(n for n in before['nodes'] if n['id'] == node)
    usable = set(owner['facts']) - set(before.get('quarantined_facts', []))
    if stage == 1:
        prior_uses = rows(artifact.get('prior_uses'), 'Provide the compact prior-use ledger; use an empty list only when no move preceded this node', nonempty=False)
        ids = set()
        for use in prior_uses:
            fields(use, ('id', 'structure', 'move', 'effect_on_residual'),
                   'Each prior-use row needs the structure, move that used it and resulting residual effect')
            need(use.get('id') not in ids, 'Duplicate prior-use row id')
            ids.add(use.get('id'))
            need(strings(use.get('property_ids')) and bool(use['property_ids']) and
                 set(use['property_ids']) <= set(PROPERTIES), 'Each row must name registered structural properties')
            need(refs(use.get('evidence')), 'Each prior-use row needs a locator in the supplied branch excerpt')
        need(refs(artifact.get('coverage_evidence')),
             'Cite the supplied short excerpt used to enumerate the prior moves')
    elif stage == 2:
        components = rows(artifact.get('residual_components'),
                          'Decompose the exact incoming residual into its actual clauses, binders, witnesses and branches')
        component_ids = set()
        for component in components:
            fields(component, ('id', 'kind', 'exact_statement', 'binders_and_domains',
                               'current_object_link'),
                   'Each residual component needs its exact statement, binders and link to the fixed current object')
            need(component.get('id') not in component_ids, 'Duplicate residual component id')
            component_ids.add(component.get('id'))
            need(refs(component.get('evidence')), 'Each residual component needs evidence from the scoped residual source')
        coordinates = rows(artifact.get('coordinates'), 'Inventory every structural coordinate')
        ids = [r.get('property_id') for r in coordinates]
        need(len(ids) == len(set(ids)) and set(ids) == set(PROPERTIES), 'Every register coordinate must be explicitly covered exactly once')
        present = set()
        for row in coordinates:
            need(row.get('status') in ('present', 'absent', 'unresolved', 'not_applicable') and text(row.get('reason')) and refs(row.get('evidence')),
                 'Each coordinate needs an evidenced presence status; unknown properties are not premises')
            if row.get('status') == 'present':
                present.add(row.get('property_id'))
        aspects = rows(artifact.get('aspects'), 'Record the actual structural aspects', nonempty=False)
        aspect_ids, signatures = set(), set()
        covered = {p for use in active[1]['artifact']['prior_uses'] for p in use['property_ids']}
        for aspect in aspects:
            fields(aspect, ('id', 'statement', 'observable', 'object', 'prior_use', 'unused_difference'),
                   'Each aspect needs its exact object, observable and difference from prior accounting')
            need(aspect.get('id') not in aspect_ids, 'Duplicate aspect id')
            aspect_ids.add(aspect.get('id'))
            props = aspect.get('property_ids', [])
            need(strings(props) and bool(props) and set(props) <= present, 'An eligible aspect must be grounded in present registered structure')
            covered.update(props)
            facts = aspect.get('facts')
            need(strings(facts) and set(facts) <= usable,
                 'Aspect fact IDs must belong to usable owner-local history; an aspect grounded directly in the residual may list no extra facts')
            need(aspect.get('status') in ('accounted', 'partly_accounted', 'unaccounted'), 'Separate property use from technique failure')
            need(refs(aspect.get('evidence')), 'Aspects need evidence from the scoped residual sources')
            signature = tuple(normalized(aspect.get(k)) for k in ('statement', 'observable', 'object'))
            need(signature not in signatures, 'Renaming an aspect does not create unused structure')
            signatures.add(signature)
        need(present <= covered, 'Every present coordinate needs an accounted or inventoried aspect')
        for interaction in rows(artifact.get('interactions'), 'List inspected structural interactions', nonempty=False):
            need(strings(interaction.get('aspect_ids')) and set(interaction['aspect_ids']) <= aspect_ids and
                 text(interaction.get('restriction')) and refs(interaction.get('evidence')), 'Interactions need actual aspects and evidenced restrictions')
        need(refs(artifact.get('interaction_coverage_evidence')), 'Review interactions, including higher-order restrictions, independently')
        prior_components = components
        expected_components = {component.get('id') for component in prior_components}
        classifications = rows(artifact.get('component_classifications'),
                               'Classify every bound component of the retained residual')
        classified = [entry.get('component_id') for entry in classifications]
        need(len(classified) == len(set(classified)) and set(classified) == expected_components,
             'Classify every Stage 1 residual component exactly once')
        all_case_ids = set()
        for classification in classifications:
            fields(classification, ('component_id', 'classification', 'relation_to_fixed_objects',
                                    'exhaustiveness', 'remaining_obligation'),
                   'Each residual component needs a witness classification, object relation, exhaustive coverage and surviving obligation')
            cases = rows(classification.get('cases'), 'Every residual component needs explicit witness cases')
            local_ids = []
            for case in cases:
                fields(case, ('id', 'condition', 'established_consequence', 'status'),
                       'Each witness case needs its condition, proved consequence and status')
                need(case.get('status') in ('forced', 'excluded', 'open', 'unresolved'),
                     'Witness case status must distinguish forced, excluded, open and unresolved cases')
                need(refs(case.get('evidence')), 'Each witness case needs source evidence')
                local_ids.append(case.get('id'))
            need(bool(local_ids) and len(local_ids) == len(set(local_ids)),
                 'Witness cases must have stable, unique identifiers')
            need(not (set(local_ids) & all_case_ids), 'Residual case identifiers must be globally unique')
            all_case_ids.update(local_ids)
            need(refs(classification.get('evidence')), 'Residual case classification needs evidence')
        need(bool(all_case_ids), 'The full residual must have at least one explicitly classified case')
    elif stage == 3:
        eligible = {a['id']: a for a in active[2]['artifact']['aspects'] if a['status'] != 'accounted'}
        comparisons = rows(artifact.get('comparisons'), 'Compare the unused aspects before selecting one')
        ids = [c.get('aspect_id') for c in comparisons]
        need(len(ids) == len(set(ids)) and set(ids) == set(eligible), 'Compare every eligible unused aspect, not only the favorite')
        accounts = {a['id'] for a in active[1]['artifact']['prior_uses']}
        for comparison in comparisons:
            need('expected_outcome' not in comparison,
                 'Stage 3 records target-structure relevance; closure or significant-reduction claims belong to Stage 4')
            fields(comparison, ('structural_conflict', 'consequence', 'affected_residual_clause'),
                   'State the actual structural conflict, its consequence on the bound witness, and the target-residual clause it constrains')
            need(strings(comparison.get('opposing_accounts')) and
                 set(comparison['opposing_accounts']) <= accounts, 'Compare unused structure with exact already exploited restrictions')
            need(comparison.get('structural_status') in ('target_relevant', 'unsupported') and refs(comparison.get('evidence')),
                 'Classify whether this is a proved target-residual structural handle; do not claim its Stage 4 payoff here')
        classifications = active[2]['artifact']['component_classifications']
        residual_cases = {case['id'] for classification in classifications for case in classification['cases']}
        assessments = rows(artifact.get('residual_case_assessments'),
                           'Group residual cases by the exact inference each aspect supports')
        aspect_rows = [row.get('aspect_id') for row in assessments]
        need(len(aspect_rows) == len(set(aspect_rows)) and set(aspect_rows) == set(eligible),
             'Give one compact grouped case assessment for every eligible aspect')
        for assessment in assessments:
            need(assessment.get('aspect_id') in eligible,
                 'Case-group assessment names an ineligible aspect')
            groups = rows(assessment.get('case_groups'),
                          'Partition each aspect assessment into uniform inference groups')
            covered_cases = set()
            for group in groups:
                need('expected_outcome' not in group,
                     'Stage 3 case groups classify structural relevance; do not require a Stage 4 payoff here')
                fields(group, ('structural_conflict', 'consequence', 'affected_residual_clause',
                               'structural_status'),
                       'Each uniform case group needs its bound-witness inference and target-residual clause')
                case_ids = group.get('case_ids')
                need(strings(case_ids) and bool(case_ids) and set(case_ids) <= residual_cases,
                     'Each inference group must cite exact Stage 2 case IDs')
                need(not (set(case_ids) & covered_cases),
                     'Case groups for one aspect must be disjoint')
                covered_cases.update(case_ids or [])
                need(group.get('structural_status') in ('target_relevant', 'unsupported') and
                     refs(group.get('evidence')), 'Every uniform case group needs evidence for its structural relation to the target residual')
            need(covered_cases == residual_cases,
                 'Uniform case groups must cover every classified residual case exactly once')
        ranking = artifact.get('ranking', [])
        need(strings(ranking) and len(ranking) == len(set(ranking)) and set(ranking) == set(eligible), 'Rank all eligible aspects with an evidenced comparison')
        need(bool(ranking) and artifact.get('selected_aspect') == ranking[0], 'Select the strongest ranked structural conflict')
        selected = next((c for c in comparisons if c.get('aspect_id') == artifact.get('selected_aspect')), {})
        need(selected.get('structural_status') == 'target_relevant' and bool(selected.get('opposing_accounts')),
             'The selected aspect must have an evidenced target-residual structural handle overlapping prior accounts')
        selected_row = next((row for row in assessments
                             if row.get('aspect_id') == artifact.get('selected_aspect')), {})
        selected_groups = selected_row.get('case_groups', [])
        need(any(group.get('structural_status') == 'target_relevant' for group in selected_groups),
             'The selected structure must constrain an actual target-defect case, not only an auxiliary or marginal configuration')
        need(artifact.get('strongest_alternative') == (ranking[1] if len(ranking) > 1 else None), 'Explicitly challenge the strongest competing aspect')
        need(text(artifact.get('selection_reason')) and refs(artifact.get('evidence')), 'Selection needs independent structural justification')
        opportunity = artifact.get('structural_opportunity')
        need(not isinstance(opportunity, dict) or not
             ({'direct_consumer', 'payoff_composition', 'before', 'after',
               'target_burden', 'prospective_reduction'} & set(opportunity)),
             'Stage 3 cannot be judged by Stage 4 payoff or consumer fields')
        if fields(opportunity, ('bound_witness', 'shared_structure', 'retained_restrictions',
                                'deduction', 'affected_residual_clause', 'stage4_opportunity',
                                'weakest_case_id', 'weakest_case_analysis'),
                  'Selected structure needs a same-witness structural-opportunity certificate for the target residual'):
            need(strings(opportunity.get('prior_account_ids')) and
                 bool(opportunity['prior_account_ids']) and
                 set(opportunity['prior_account_ids']) <= accounts and
                 set(opportunity['prior_account_ids']) <= set(selected.get('opposing_accounts', [])),
                 'The structural-opportunity certificate must identify the already-accounted structures it directly overlaps')
            need(opportunity.get('weakest_case_id') in residual_cases,
                 'The certificate must identify its weakest classified residual case')
            need(any(opportunity.get('weakest_case_id') in group.get('case_ids', [])
                     for group in selected_groups),
                 'The weakest case must be assessed under the selected structural handle')
            need(refs(opportunity.get('evidence')),
                 'The structural-opportunity inference needs evidence on the same residual witnesses')
    elif stage == '3b':
        need(artifact.get('residual_binding') == residual_binding(before, node),
             'Stage 3b must bind the exact incoming residual and retained facts')
        need(artifact.get('selected_aspect') == active[3]['artifact']['selected_aspect'],
             'Stage 3b must realize the accepted Stage 3 selection')
        selected_witness = active[3]['artifact']['structural_opportunity']['bound_witness']
        need(artifact.get('bound_witness') == selected_witness,
             'Stage 3b must use the exact bound witness named by accepted Stage 3')
        fields(artifact, ('incoming_residual_key', 'ledger_row', 'structure_fact_id',
                          'structure_key', 'lean_declaration', 'source_path',
                          'weakest_case_id'),
               'Stage 3b needs the incoming residual key, owner-local ledger row, and checked output')
        lean_inputs = artifact.get('lean_inputs')
        need(isinstance(lean_inputs, list) and bool(lean_inputs) and
             all(isinstance(key, str) and key.strip() for key in lean_inputs) and
             len(lean_inputs) == len(set(lean_inputs)) and
             artifact.get('incoming_residual_key') in lean_inputs,
             'Stage 3b Lean inputs must include the exact incoming residual key')
        need(artifact.get('structure_key') != artifact.get('incoming_residual_key') and
             str(artifact.get('source_path', '')).endswith('.lean'),
             'Stage 3b must publish a new key from a Lean source')
        need(artifact.get('weakest_case_id') ==
             active[3]['artifact']['structural_opportunity']['weakest_case_id'],
             'Stage 3b must cover the accepted weakest residual case')
        projections = rows(artifact.get('claim_projections'),
                           'Map each selected structural claim to its Lean projection')
        for projection in projections:
            fields(projection, ('claim', 'declaration', 'residual_clause',
                                'bound_witness'),
                   'Each structural claim needs a same-witness Lean projection and affected residual clause')
            need(projection.get('bound_witness') == selected_witness,
                 'Every Stage 3b projection must concern the exact Stage 3 bound witness')
            need(refs(projection.get('evidence')), 'A structural projection needs evidence')
        fact_id = artifact.get('structure_fact_id')
        owner_after = next(n for n in after['nodes'] if n['id'] == node)
        need(set(after['facts']) - set(before['facts']) == {fact_id} and
             fact_id in set(owner_after['facts']) - set(owner['facts']) and
             after['facts'].get(fact_id, {}).get('kind') == 'derived',
             'Stage 3b must publish exactly one derived fact on this node')
        need(refs(artifact.get('evidence')), 'The Lean fact and exact ledger publication need evidence')
    elif stage == 4:
        structure = active['3b']['artifact']
        need(artifact.get('structure_fact_id') == structure['structure_fact_id'] and
             artifact.get('structure_binding') == digest(active['3b']),
             'Stage 4 must consume the exact reviewed Stage 3b fact')
        selected = active[3]['artifact']['selected_aspect']
        need(artifact.get('aspect_id') == selected, 'Catalogue only for the reviewed selected aspect')
        aspect = next(a for a in active[2]['artifact']['aspects'] if a['id'] == selected)
        expected = {t for p in aspect['property_ids'] for t in PROPERTIES[p]['techniques']}
        techniques = rows(artifact.get('techniques'), 'Catalogue all relevant textbook moves')
        need(expected <= {t.get('technique_id') for t in techniques}, 'Catalogue omits a registered technique family for the selected property')
        ids = set()
        for technique in techniques:
            need(text(technique.get('id')) and technique['id'] not in ids, 'Each distinct technique variant needs a unique id')
            ids.add(technique.get('id'))
            need(technique.get('technique_id') in TECHNIQUES, 'Use a registered textbook technique family')
            need(technique.get('status') in ('candidate', 'excluded', 'missing_prerequisite') and
                 text(technique.get('reason')) and refs(technique.get('evidence')), 'Every technique needs an evidenced applicability decision')
            if technique.get('status') == 'candidate':
                need(technique.get('structure_fact_id') == structure['structure_fact_id'],
                     'Candidate must use the Stage 3b fact on the incoming residual')
                fields(technique, ('theorem', 'operation', 'object', 'output', 'dependency_step', 'history_comparison'),
                       'Candidate needs an exact theorem, operation, object, output, indispensable use and history comparison')
                residual_cases = {case['id'] for classification in active[2]['artifact']['component_classifications']
                                  for case in classification['cases']}
                covered_cases = technique.get('residual_case_ids')
                need(strings(covered_cases) and bool(covered_cases) and set(covered_cases) <= residual_cases,
                     'Each candidate must name the exact classified residual cases it applies to')
                productive_cases = {case_id
                                    for row in active[3]['artifact']['residual_case_assessments']
                                    if row['aspect_id'] == selected
                                    for group in row['case_groups']
                                    if group.get('structural_status') == 'target_relevant'
                                    for case_id in group['case_ids']}
                need(bool(covered_cases) and set(covered_cases) <= productive_cases,
                     'A candidate must operate only on cases with the reviewed Stage 3 target-residual structural handle')
                for premise in rows(technique.get('prerequisites'), 'Candidate prerequisites must be stated and proved', nonempty=False):
                    need(text(premise.get('statement')) and text(premise.get('witness_binding')) and
                         text(premise.get('derivation')) and refs(premise.get('evidence')),
                         'Every prerequisite needs a derivation on the same Stage 3b residual witness')
        need(refs(artifact.get('coverage_evidence')), 'Explain catalogue completeness and other relevant textbook alternatives')
        candidates = {t['id']: t for t in techniques if t.get('status') == 'candidate'}
        chosen = candidates.get(artifact.get('selected_candidate_id'))
        need(chosen is not None, 'Stage 4 must select an applicable move before Stage 5')
        need(fields(artifact, ('selection_reason', 'strongest_alternative'),
                    'Compare the selected move with its strongest alternative') and
             refs(artifact.get('selection_evidence')),
             'The best-move comparison needs exact evidence')
        if chosen is not None:
            composition = chosen.get('payoff_composition')
            if fields(composition, ('selected_output', 'prior_restrictions',
                                     'retained_estimates', 'derivation', 'resulting_conflict_or_bound',
                                     'before', 'after', 'weakest_case', 'direct_consumer'),
                      'The selected move must make its use of the Stage 3 structural handle and resulting payoff explicit before authorization'):
                need(normalized(composition['selected_output']) == normalized(chosen.get('output')),
                     'The payoff composition must consume the selected move’s exact catalogued output')
                need(refs(composition.get('evidence')),
                     'The selected move needs a proved conditional payoff composition')
                need(normalized(composition['before']) != normalized(composition['after']),
                     'The selected move cannot leave the target-bearing burden unchanged')
    elif stage == 5:
        need(artifact.get('residual_binding') == residual_binding(before, node), 'Authorization must bind the full exact residual')
        need(artifact.get('aspect_id') == active[3]['artifact']['selected_aspect'], 'Cannot substitute another structural aspect after review')
        candidate = next((t for t in active[4]['artifact']['techniques'] if t['id'] == artifact.get('candidate_id')), None)
        need(candidate is not None and candidate.get('status') == 'candidate', 'Only an admitted catalogue candidate can be authorized')
        need(artifact.get('candidate_id') == active[4]['artifact'].get('selected_candidate_id'),
             'Stage 5 must authorize or challenge the move selected and justified at Stage 4')
        if candidate:
            for key in ('technique_id', 'operation', 'object', 'output'):
                need(artifact.get(key) == candidate.get(key), 'Authorization changed the catalogued ' + key)
        fields(artifact, ('consumer', 'dependency_test', 'comparison', 'weakest_outcome'),
               'Authorization needs exact consumer, indispensable use, candidate comparison and weakest-outcome assessment')
        for key in ('dependency_evidence', 'comparison_evidence', 'coverage_evidence', 'payoff_evidence', 'history_evidence'):
            need(refs(artifact.get(key)), 'Authorization needs proved ' + key)
        arms = rows(artifact.get('outcomes'), 'Specify every productive outcome before construction')
        cases = [a.get('case') for a in arms]
        need(len(cases) == len(set(cases)), 'Outcome cases must be distinct')
        for arm in arms:
            payoff(arm)
            residual_cases = {case['id'] for classification in active[2]['artifact']['component_classifications']
                              for case in classification['cases']}
            covered = arm.get('residual_case_ids')
            need(strings(covered) and bool(covered) and set(covered) <= residual_cases,
                 'Each authorized outcome must identify its exact incoming residual cases')
        if arms:
            need(set().union(*(set(arm.get('residual_case_ids', [])) for arm in arms)) == residual_cases,
                 'Authorized outcomes must cover every classified incoming residual case')
        if all(k in artifact for k in ('aspect_id', 'technique_id', 'operation', 'object', 'output')):
            signature = technique_signature(artifact)
            for prior in attempt_history(before, node):
                if all(normalized(prior.get(k)) == normalized(v) for k, v in signature.items()):
                    retry = artifact.get('retry', {})
                    need(retry.get('kind') in ('new_proved_premise', 'corrected_construction') and
                         text(retry.get('change')) and refs(retry.get('evidence')) and
                         any(e not in before['evidence'] for e in retry.get('evidence', [])),
                         'Repeating a failed technique needs a substantive evidenced change; its property remains available')
    elif stage == 6:
        plan = authorization(before, node)
        need(artifact.get('authorization_binding') == plan['binding'], 'Execution must bind the exact approved authorization')
        for key in ('output_evidence', 'application_evidence', 'preservation_evidence'):
            need(refs(artifact.get(key)), 'Execution needs actual ' + key)
        arms = rows(artifact.get('outcomes'), 'Execution must realize every authorized outcome')
        planned = {a['case']: a for a in plan['artifact']['outcomes']}
        need(len(arms) == len(planned) and {a.get('case') for a in arms} == set(planned), 'Every approved outcome must actually be discharged or reduced')
        children = {n['id']: n for n in after['nodes'] if n['parent'] == node}
        linked = set()
        for arm in arms:
            target = planned.get(arm.get('case'), {})
            need(arm.get('kind') == target.get('kind'), 'An auxiliary lemma cannot replace the approved proof advancement')
            need(refs(arm.get('evidence')) and refs(arm.get('application_evidence')), 'Each result needs actual gain and consumer-application evidence')
            if target.get('kind') == 'significant_reduction':
                child = children.get(arm.get('child'))
                need(child is not None and child['residual'] == target['remaining_residual'], 'Reduction must create the exact authorized surviving residual')
                if child:
                    linked.add(child['id'])
                    need(child.get('reduction', {}).get('excluded_structure') == target['excluded_structure'] and
                         child.get('reduction', {}).get('significance') == target['significance'],
                         'Actual reduction must realize the authorized substantial structural exclusion')
        need(linked == set(children), 'Every retained or new child must remain covered by the authorized outcomes')
    elif stage == 7:
        need(artifact.get('construction_binding') == digest(active[6]), 'Consume the exact verified construction')
        discharges = artifact.get('discharges', {})
        cases = {a['case'] for a in active[6]['artifact']['outcomes']}
        need(isinstance(discharges, dict) and set(discharges) == cases and all(refs(v) for v in discharges.values()),
             'Every actual outcome needs its full discharge proof')
        need(refs(artifact.get('account_updates')) and refs(artifact.get('evidence')), 'Update the structural accounts with proved exclusions, gains and exact multiplicities')
    elif stage == 8:
        need(artifact.get('outcome_binding') == digest(active[7]), 'Verification must bind the fully discharged outcomes')
        for key in ('statement_evidence', 'implementation_evidence', 'wiring_evidence', 'artifact_evidence'):
            need(refs(artifact.get(key)), 'Final verification needs ' + key)
    return errors

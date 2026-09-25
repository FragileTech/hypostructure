"""Pure transition checks. Only the supervisor calls these to commit state."""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import sys

POLICY = Path(__file__).parent / 'policy'
spec = importlib.util.spec_from_file_location('execution_record', POLICY / 'scripts/check_execution.py')
record = importlib.util.module_from_spec(spec)
sys.dont_write_bytecode = True
spec.loader.exec_module(record)

from .policy.workflow import (COMMON_GATES, STAGE_GATES,
                              STAGE_ORDER, before, ordinal, successor,
                              repair_stage, validate_artifact)

class Rejected(ValueError):
    pass


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def require(condition, message):
    if not condition:
        raise Rejected(message)


def last_event(state, node):
    return next((e for e in reversed(state['events']) if e['node'] == node), None)


def next_stage(state, node):
    event = last_event(state, node)
    if event is None:
        return 1
    if event['result'] == 'failed':
        return repair_stage(event)
    return successor(event['stage'])


def next_node(state):
    """Parents execute construction before children; outcome gate waits for children."""
    nodes = {n['id']: n for n in state['nodes']}
    def visit(name):
        stage = next_stage(state, name)
        if stage != 9 and ordinal(stage) <= ordinal(6):
            return name
        for child in nodes[name]['children']:
            pending = visit(child)
            if pending:
                return pending
        return name if stage != 9 else None
    return visit(state['root'])


def validate_transition(before, after, directory, node, stage):
    """Reject altered contracts, retroactive history, skipped work, and hidden children."""
    require(next_node(before) == node and next_stage(before, node) == stage,
            'Assignment is not the next prescribed obligation')
    require(not record.validate(after, directory), 'Execution record structural validation failed: ' +
            '; '.join(record.validate(after, directory)))
    for key in ('claim', 'scope', 'root', 'methodology_sources'):
        require(before[key] == after[key], f'Locked contract changed: {key}')
    require(after['events'][:-1] == before['events'] and
            len(after['events']) == len(before['events']) + 1, 'Exactly one append-only stage event required')
    event = after['events'][-1]
    require(event['node'] == node and event['stage'] == stage, 'Wrong stage or node')
    require('restart_stage' not in event, 'Only the controller may select an inherited-state restart')
    require(after.get('quarantined_facts', []) == before.get('quarantined_facts', []),
            'Only independent review may change fact quarantine')
    require(after.get('unnecessary_facts', []) == before.get('unnecessary_facts', []),
            'Only independent review may certify that an unavailable fact is unnecessary')
    if stage == 8:
        require(before.get('implementation_chain') == after.get('implementation_chain'),
                'Stage 8 cannot change the kernel-checked dependency chain')
        require(after['nodes'] == before['nodes'] and after['facts'] == before['facts'],
                'Verification cannot introduce a construction or change discharged mathematics')
    for name, fact in before['facts'].items():
        require(after['facts'].get(name) == fact, f'Retained fact changed/dropped: {name}')
    for name in set(after['facts']) - set(before['facts']):
        require(after['facts'][name]['kind'] in ('derived', 'case'), 'New standing assumption forbidden')
    for name, evidence in before['evidence'].items():
        require(after['evidence'].get(name) == evidence, f'Historical evidence changed: {name}')
    old = {n['id']: n for n in before['nodes']}
    new = {n['id']: n for n in after['nodes']}
    require(set(old) <= set(new), 'Obligation deleted')
    for name, previous in old.items():
        current = new[name]
        if name != node:
            ancestors = []
            parent = previous['parent']
            while parent is not None:
                ancestors.append(parent)
                parent = old[parent]['parent']
            if node in ancestors:
                inherited_additions = set(new[node]['facts']) - set(old[node]['facts'])
                expected = set(previous['facts']) | inherited_additions
                require(set(current['facts']) == expected and
                        {k: v for k, v in current.items() if k != 'facts'} ==
                        {k: v for k, v in previous.items() if k != 'facts'},
                        f'Only proved ancestor facts may propagate to {name}')
            else:
                require(current == previous, f'Other obligation modified: {name}')
        else:
            for field in ('id', 'parent', 'goal', 'residual'):
                require(current[field] == previous[field], f'Local contract changed: {field}')
            require(set(previous['facts']) <= set(current['facts']), 'Inherited residual projected away')
            local_additions = set(current['facts']) - set(previous['facts'])
            require(not local_additions or stage in ('3b', 6) and event['result'] == 'done' and all(
                    f not in before['facts'] and after['facts'][f]['kind'] == 'derived'
                    for f in local_additions),
                    'Only a proved Stage 3b structure or Stage 6 construction may extend this node')
            require(set(previous['children']) <= set(current['children']), 'Child obligation discarded')
            history = previous.get('move_history', [])
            require(current.get('move_history', [])[:len(history)] == history,
                    'Previously accounted or exhausted moves cannot be erased or rewritten')
    violations = validate_artifact(before, after, node, stage)
    require(not violations, '; '.join(violations))
    additions = set(new) - set(old)
    for fact_id in set(after['facts']) - set(before['facts']):
        if after['facts'][fact_id]['kind'] == 'case':
            require(stage == 6 and event['result'] == 'done' and
                    any(fact_id in new[c]['facts'] for c in additions) and
                    all(fact_id not in new[c]['facts'] for c in old),
                    'A new case assumption belongs only to a new exhaustively refined child')
    if additions:
        require(stage == 6 and event['result'] == 'done', 'Unverified child transition')
        for child in additions:
            require(new[child]['parent'] == node and new[child]['status'] == 'open', 'Invalid new child')
            require(set(new[child]['facts']) <= set(new[node]['facts']) | (set(after['facts']) - set(before['facts'])),
                    'A new child cannot borrow existing premises outside its parent residual')
            require(last_event(after, child) is None, 'Child work cannot be pre-certified')
            inherited_history = new[node].get('move_history', [])
            require(new[child].get('move_history', [])[:len(inherited_history)] == inherited_history,
                    'New residual must retain the upstream exhausted-move history')
            reduction = new[child].get('reduction', {})
            require(isinstance(reduction, dict) and reduction.get('from') == node,
                    'New residual needs a reduction from its exact incoming parent')
            require(reduction.get('kind') in ('structural_exclusion', 'quantitative_restriction', 'well_founded_descent'),
                    'Tree expansion or renaming is not a meaningful residual reduction')
            require(isinstance(reduction.get('strictness'), str) and bool(reduction['strictness'].strip()),
                    'Reduction must state what strictly improves')
            proof = reduction.get('evidence', [])
            require(isinstance(proof, list) and bool(proof) and
                    all(isinstance(e, str) and e in after['evidence'] for e in proof),
                    'Strict residual reduction requires proof evidence')
            if reduction['kind'] == 'well_founded_descent':
                require(new[node].get('uses_descent') is True,
                        'Descent must trigger transport and base-case checks')
    if new[node]['status'] == 'closed' and old[node]['status'] != 'closed':
        require(stage == 7 and event['result'] == 'done', 'Closure before outcome discharge')
    if event['result'] == 'failed' and stage != 8:
        require(new[node]['status'] != 'closed', 'Failed obligation must reopen, not retain a closure claim')
    if stage in (7, 8) and event['result'] == 'done':
        require(node != after['root'] or not (set(before.get('quarantined_facts', [])) - set(before.get('unnecessary_facts', []))),
                'Unresolved prerequisites block outcome discharge and completion, not setup or inventory')
        def discharged(name):
            item = new[name]
            return next_stage(after, name) == 9 and item['status'] != 'open' and all(
                discharged(c) for c in item['children'])
        require(all(discharged(c) for c in new[node]['children']), 'Unconsumed descendant or base case')
        require(new[node]['status'] != 'open', 'Outcome gate left its obligation open')
    if stage == 8 and event['result'] == 'done' and node == after['root']:
        require(after['status'] == 'complete', 'Root stage 8 requires complete, reconciled record')
        require(not record.validate(after, directory, complete=True), 'Incomplete final certificate')
    else:
        require(after['status'] == 'active', 'Worker cannot stop, pause, or complete the workflow')


def validate_review(review, binding, stage, directory):
    required = {'binding', 'decision', 'gates', 'first_failure', 'repair', 'repair_stage', 'reviewed_facts'}
    optional_lists = {'invalid_inherited_facts', 'revalidated_facts', 'unnecessary_facts'}
    optional = optional_lists | {'accepted_stage_revocation'}
    require(required <= set(review) <= required | optional,
            'Unexpected review fields')
    require(review['binding'] == binding, 'Stale or replayed review')
    require(review['decision'] in ('accept', 'reject'), 'Invalid verdict')
    expected = set(COMMON_GATES + STAGE_GATES[stage])
    require(set(review['gates']) == expected, 'Review gates missing or added')
    for name, check in review['gates'].items():
        require(set(check) == {'verdict', 'reason', 'evidence'}, f'Invalid gate: {name}')
        require(check['verdict'] in ('pass', 'fail'), f'Invalid verdict: {name}')
        require(isinstance(check['reason'], str) and bool(check['reason'].strip()), f'No reasoning: {name}')
        require(isinstance(check['evidence'], list) and bool(check['evidence']), f'No source inspection: {name}')
        for ref in check['evidence']:
            require(set(ref) == {'path', 'sha256', 'locator'}, 'Invalid evidence reference')
            p = (directory / ref['path']).resolve()
            require(p.is_relative_to(directory.resolve()) and p.is_file(), 'Review evidence outside snapshot')
            require(hashlib.sha256(p.read_bytes()).hexdigest() == ref['sha256'], 'Stale review evidence')
            require(isinstance(ref['locator'], str) and bool(ref['locator'].strip()), 'Missing evidence locator')
    require(review['repair_stage'] in STAGE_ORDER and
            not before(stage, review['repair_stage']),
            'Review must identify the earliest defective decision within the executed prefix')
    revocation = review.get('accepted_stage_revocation')
    if before(review['repair_stage'], stage):
        require(isinstance(revocation, dict) and
                set(revocation) == {'stage', 'defect', 'evidence'} and
                revocation['stage'] == review['repair_stage'] and
                isinstance(revocation['defect'], str) and bool(revocation['defect'].strip()) and
                isinstance(revocation['evidence'], list) and bool(revocation['evidence']),
                'Reopening an accepted stage requires an explicit stage-specific defect and evidence')
        for ref in revocation['evidence']:
            require(isinstance(ref, dict) and set(ref) == {'path', 'sha256', 'locator'},
                    'Invalid accepted-stage revocation evidence')
            p = (directory / ref['path']).resolve()
            require(p.is_relative_to(directory.resolve()) and p.is_file() and
                    hashlib.sha256(p.read_bytes()).hexdigest() == ref['sha256'] and
                    isinstance(ref['locator'], str) and bool(ref['locator'].strip()),
                    'Stale or missing accepted-stage revocation evidence')
    else:
        require(revocation is None, 'Current-stage repair must not revoke an accepted stage')
    if stage == 6 and (review['decision'] == 'reject' or
                      (directory / 'record/state.json').is_file() and
                      json.loads((directory / 'record/state.json').read_text())['events'][-1]['result'] == 'failed'):
        require(review['repair_stage'] <= 5, 'A failed construction must invalidate authorization before another attempt')
    if review['decision'] == 'accept':
        require(all(g['verdict'] == 'pass' for g in review['gates'].values()), 'Acceptance has failed gates')
        require(review['first_failure'] == '' and review['repair'] == '', 'Acceptance has unresolved failure')
        state_path = directory / 'record/state.json'
        if stage in (1, 2, 3, '3b', 4, 5) and state_path.is_file():
            submitted = json.loads(state_path.read_text())['events'][-1]
            require(submitted.get('result') != 'failed',
                    'A failed reasoning-stage submission is an execution defect, never an accepted workflow outcome; reject and repair it')
    else:
        require(any(g['verdict'] == 'fail' for g in review['gates'].values()), 'Rejection must identify a failed gate')
        require(bool(review['first_failure'].strip()) and bool(review['repair'].strip()), 'Rejection lacks repair obligation')
    require(isinstance(review['reviewed_facts'], list), 'Missing independently checked new fact IDs')
    for field in optional_lists:
        require(isinstance(review.get(field, []), list) and
                all(isinstance(x, str) for x in review.get(field, [])), 'Invalid fact review list')
    if review.get('invalid_inherited_facts'):
        require(review['decision'] == 'reject' and review['gates']['full_residual']['verdict'] == 'fail',
                'Invalid inherited fact must reject the residual gate')
    if review.get('unnecessary_facts'):
        require(stage in (1, 2, 3, '3b', 6) and review['decision'] == 'accept',
                'Unnecessary-input certification requires an accepted dependency proof before closure')
    if review.get('revalidated_facts'):
        require(stage in (1, 2, 3, '3b', 6) and review['decision'] == 'accept',
                'Revalidation requires independently accepted prerequisite proof before outcome discharge')

#!/usr/bin/env python3
"""Validate methodology record structure and evidence freshness, never mathematics."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

SKILL = Path(__file__).resolve().parents[1]
SOURCES = json.loads((SKILL / 'references/sources.json').read_text())
WORKFLOW = json.loads((SKILL / 'workflow.json').read_text())
STAGES = {s['number']: s for s in WORKFLOW['stages']}
STAGE_ORDER = tuple(s['number'] for s in WORKFLOW['stages'])


def next_stage(stage):
    index = STAGE_ORDER.index(stage) + 1
    return STAGE_ORDER[index] if index < len(STAGE_ORDER) else 9


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def present(value):
    return isinstance(value, str) and bool(value.strip())


def validate(state, directory, repo=None, complete=False):
    errors = []
    def need(condition, message):
        if not condition:
            errors.append(message)
    need('version' not in state and 'workflow_version' not in state,
         'Workflow records are unversioned; remove version fields')
    need(present(state.get('claim')), 'Exact requested claim is missing')
    need(present(state.get('scope')), 'Authorized scope is missing')
    need(state.get('status') in ('active', 'interrupted', 'complete'), 'Invalid task status')
    final = complete or state.get('status') == 'complete'
    evidence = state.get('evidence', {})
    need(isinstance(evidence, dict), 'Evidence must be a dictionary')
    if not isinstance(evidence, dict):
        evidence = {}
    for name, item in evidence.items():
        if not isinstance(item, dict):
            errors.append(f'{name}: evidence entry is not an object')
            continue
        for field in ('path', 'sha256', 'locator', 'proves'):
            need(present(item.get(field)), f'{name}: missing evidence {field}')
        if present(item.get('path')):
            p = Path(item['path'])
            if not p.is_absolute():
                p = directory / p
            need(p.is_file(), f'{name}: evidence file missing: {p}')
            if p.is_file():
                need(sha(p) == item.get('sha256'), f'{name}: evidence changed; re-review it')
    def refs(ids, where, required=True):
        need(isinstance(ids, list), f'{where}: evidence references must be a list')
        if not isinstance(ids, list):
            return
        if required:
            need(bool(ids), f'{where}: no evidence references')
        for name in ids:
            need(isinstance(name, str) and name in evidence, f'{where}: unknown evidence {name}')
    if repo:
        for path, digest in SOURCES.items():
            p = repo / path
            need(p.is_file(), f'Methodology source missing: {p}')
            if p.is_file():
                need(sha(p) == digest, f'Methodology source drift: {path}; reconcile skill before work')
    need(state.get('methodology_sources') == SOURCES, 'Source manifest differs from skill snapshot')
    facts = state.get('facts', {})
    need(isinstance(facts, dict), 'Facts must be a dictionary')
    if not isinstance(facts, dict):
        facts = {}
    for name, fact in facts.items():
        need(isinstance(fact, dict), f'{name}: invalid fact')
        if isinstance(fact, dict):
            need(present(fact.get('statement')), f'{name}: fact statement missing')
            need(fact.get('kind') in ('standing', 'derived', 'case'), f'{name}: invalid fact kind')
            refs(fact.get('evidence'), f'fact {name}')
    nodes = state.get('nodes', [])
    need(isinstance(nodes, list) and bool(nodes), 'Proof tree is missing')
    if not isinstance(nodes, list):
        nodes = []
    by_id = {}
    for node in nodes:
        if not isinstance(node, dict) or not present(node.get('id')):
            errors.append('Invalid node or missing node ID')
            continue
        need(node['id'] not in by_id, f'Duplicate node ID {node["id"]}')
        by_id[node['id']] = node
    root = state.get('root')
    need(root in by_id, 'Root does not exist')
    if root in by_id:
        need(by_id[root].get('parent') is None, 'Root has a parent')
        need(bool(by_id[root].get('facts')), 'Root has no retained facts')
    for name, node in by_id.items():
        need(present(node.get('residual')), f'{name}: exact residual missing')
        need(present(node.get('goal')), f'{name}: exact local goal missing')
        status = node.get('status')
        need(status in ('open', 'closed', 'expanded'), f'{name}: invalid node status')
        nf = node.get('facts', [])
        need(isinstance(nf, list) and all(isinstance(x, str) for x in nf), f'{name}: invalid fact list')
        if not isinstance(nf, list) or not all(isinstance(x, str) for x in nf):
            nf = []
        need(len(nf) == len(set(nf)), f'{name}: duplicate facts')
        need(set(nf) <= set(facts), f'{name}: unregistered facts')
        if name != root:
            parent = by_id.get(node.get('parent'))
            need(parent is not None, f'{name}: parent missing')
            if parent:
                need(name in parent.get('children', []), f'{name}: absent from parent children')
                need(set(parent.get('facts', [])) <= set(nf), f'{name}: inherited facts dropped')
        children = node.get('children', [])
        need(isinstance(children, list), f'{name}: children must be a list')
        if not isinstance(children, list):
            children = []
        need(all(isinstance(x, str) for x in children), f'{name}: invalid child ID')
        children = [x for x in children if isinstance(x, str)]
        need(len(children) == len(set(children)), f'{name}: duplicate children')
        if status in ('open', 'closed'):
            need(not children, f'{name}: open/closed terminal has successors')
        if status == 'closed':
            refs(node.get('certificate'), f'{name}: terminal certificate')
        if status == 'expanded':
            need(bool(children), f'{name}: expanded node has no children')
            for field in ('refinement', 'coverage', 'consumption', 'continuation'):
                refs(node.get(field), f'{name}: {field}')
            if node.get('uses_descent'):
                refs(node.get('descent'), f'{name}: strict descent and transport')
                refs(node.get('base_cases'), f'{name}: base cases')
        for child in children:
            need(child in by_id, f'{name}: unrecorded child {child}')
            if child in by_id:
                need(by_id[child].get('parent') == name, f'{child}: wrong parent')
    visited, visiting = set(), set()
    def walk(name):
        if name in visiting:
            errors.append('Cycle in verified proof tree')
            return
        if name in visited or name not in by_id:
            return
        visiting.add(name)
        for child in by_id[name].get('children', []):
            if isinstance(child, str):
                walk(child)
        visiting.remove(name)
        visited.add(name)
    if isinstance(root, str):
        walk(root)
    need(visited == set(by_id), 'Unreachable/orphan proof nodes')
    open_ids = {name for name, node in by_id.items() if node.get('status') == 'open'}
    queue = state.get('queue', [])
    need(isinstance(queue, list) and all(isinstance(x, str) for x in queue), 'Invalid queue')
    if isinstance(queue, list) and all(isinstance(x, str) for x in queue):
        need(len(queue) == len(set(queue)) and set(queue) == open_ids, 'Queue does not equal open leaves')
    previous_by_node = {}
    events = state.get('events', [])
    need(isinstance(events, list), 'Events must be a list')
    if not isinstance(events, list):
        events = []
    for index, event in enumerate(events):
        if not isinstance(event, dict):
            errors.append(f'Event {index}: invalid event')
            continue
        stage = event.get('stage')
        need(stage in STAGE_ORDER, f'Event {index}: invalid stage')
        need(event.get('result') in ('done', 'failed'), f'Event {index}: invalid result')
        need(event.get('node') in by_id, f'Event {index}: unknown node')
        refs(event.get('evidence'), f'Event {index}')
        previous = previous_by_node.get(event.get('node'))
        if previous is None:
            need(stage == 1, 'First event must establish the branch')
        else:
            normal = (previous.get('result') == 'done' and
                      previous.get('stage') in STAGE_ORDER and
                      stage == next_stage(previous['stage']))
            repair = previous.get('result') == 'failed' and stage == previous.get('restart_stage', STAGES.get(previous.get('stage'), {}).get('repair_stage')) and present(event.get('reason'))
            need(normal or repair,
                 f'Event {index}: skipped stage or unexplained restart')
        previous_by_node[event.get('node')] = event
    if final:
        need(state.get('status') == 'complete', 'Record is not marked complete')
        need(not open_ids, 'Completion claim has open leaves')
        need(bool(events) and events[-1].get('stage') == 8 and events[-1].get('result') == 'done', 'Final stage not completed')
        for name in by_id:
            last = previous_by_node.get(name, {})
            need(last.get('stage') == 8 and last.get('result') == 'done', f'{name}: execution stages incomplete')
        refs(state.get('semantic_review'), 'Semantic review of actual evidence')
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for command in ('init', 'check'):
        p = sub.add_parser(command)
        p.add_argument('directory', type=Path)
        p.add_argument('--repo', type=Path)
        if command == 'check':
            p.add_argument('--complete', action='store_true')
    p = sub.add_parser('evidence')
    p.add_argument('path', type=Path)
    p.add_argument('--locator', required=True)
    p.add_argument('--proves', required=True)
    args = parser.parse_args()
    if args.command == 'evidence':
        print(json.dumps({'path':str(args.path.resolve()), 'sha256':sha(args.path), 'locator':args.locator, 'proves':args.proves}, indent=2))
        return 0
    directory = args.directory.resolve()
    if args.command == 'init':
        directory.mkdir(parents=True, exist_ok=True)
        if (directory/'state.json').exists() or (directory/'execution.md').exists():
            parser.error('Refusing to overwrite an execution record; resume it instead')
        state = {'claim':'', 'scope':'', 'status':'active', 'methodology_sources':SOURCES,
                 'root':'root', 'facts':{}, 'evidence':{}, 'nodes':[{'id':'root', 'parent':None,
                 'goal':'', 'residual':'', 'facts':[], 'status':'open', 'children':[]}],
                 'queue':['root'], 'events':[], 'semantic_review':[]}
        (directory/'state.json').write_text(json.dumps(state,indent=2)+'\n')
        titles = [stage['title'] for stage in WORKFLOW['stages']]
        body = '# Methodology execution record\n\nStatus: unfinished. This is not a proof certificate.\n'
        for i, title in enumerate(titles,1):
            body += f'\n## {i}. {title}\n\nInput and exact objects:\nWork performed:\nProof/evidence locations:\nFirst failed obligation, if any:\nOutput and remaining queue:\n'
        body += '\n## Retained failures and repair decisions\n'
        (directory/'execution.md').write_text(body)
        print('Created unfinished record. Fill exact state before execution; nothing is pre-certified.')
        return 0
    try:
        state = json.loads((directory/'state.json').read_text())
        errors = validate(state, directory, args.repo, args.complete)
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as exc:
        print(f'INVALID RECORD: {exc}', file=sys.stderr)
        return 1
    if errors:
        print('\n'.join('FAIL: '+e for e in errors))
        return 1
    print('STRUCTURE ONLY: record consistent; mathematical truth and semantic compliance require review.')
    return 0

if __name__ == '__main__':
    sys.exit(main())

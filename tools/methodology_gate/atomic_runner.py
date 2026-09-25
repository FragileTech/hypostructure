"""Run one mathematical obligation in a fresh isolated process, then review it.

No conversation or task queue is mounted for the worker. The existing Linux
supervisor supplies a private home, ephemeral CLI invocation and scoped root.
"""
from __future__ import annotations

import copy
import hashlib
import json
import re
from pathlib import Path
import shutil
import uuid

from . import runner, taskflow as t


def scoped_path(root: Path, name: str) -> Path:
    relative = Path(name)
    t.require(not relative.is_absolute() and relative.parts and '..' not in relative.parts,
              'Task inputs and output must be repository-relative files')
    path = root / relative
    t.require(path.resolve().is_relative_to(root.resolve()) and
              not any(parent.is_symlink() for parent in (path, *path.parents)),
              'Symlinks and outside paths are not task inputs')
    return path


def assignment(state: dict, root: Path) -> dict:
    selected = t.next_task(state, root)
    t.require(selected['task'] is not None, selected['diagnostic'] or 'No ready task')
    task = selected['task']
    # Review of admission certifies the complete outcome list before construction.
    if str(task['phase']) == '6':
        t.require(any(item['status'] == 'accepted' and
                      item['contract']['kind'] == 'review_admission' and
                      str(item['contract']['phase']) == '5' and
                      item['contract']['move_id'] == task['move_id'] and
                      t.depends_on(state, task['id'], key)
                      for key, item in state['tasks'].items()),
                  'Construction requires a reviewed Phase 5 admission dependency for this move')
    inputs = set()
    accepted = {}
    for name in task['reads']:
        if name == f"branch:{state['branch']['revision']}":
            continue
        if name in state['tasks']:
            item = state['tasks'][name]
            t.require(item['status'] == 'accepted', 'Only accepted task evidence may be supplied')
            accepted[name] = {key: copy.deepcopy(item['submission'][key])
                              for key in ('output', 'evidence', 'implementation_status')}
            inputs.update(ref['path'] for ref in item['submission']['evidence'])
        else:
            inputs.add(name)
    # Carry direct accepted dependencies as premises. Their ancestry is checked
    # by the controller; importing every ancestor would recreate the old context.
    for name, item in state['tasks'].items():
        if name in task['depends_on'] and name not in accepted:
            t.require(item['status'] == 'accepted', 'Dependency is not accepted')
            accepted[name] = dict(output=item['submission']['output'], evidence=[],
                                  implementation_status=item['submission']['implementation_status'])
    output = scoped_path(root, task['allowed_write'])
    if output.exists():
        inputs.add(task['allowed_write'])
    historical = []
    for item in accepted.values():
        for ref in item['evidence']:
            if not t.evidence_valid(ref, root):
                t.require(t.archived_evidence_valid(ref, root), 'Accepted source bytes are unavailable')
                archived = 'tools/methodology_gate/evidence_snapshots/' + ref['sha256']
                historical.append(dict(original_path=ref['path'], sha256=ref['sha256'], mounted_path=archived))
                ref['path'] = archived
                inputs.add(archived)
    manifest = {}
    for name in sorted(inputs):
        path = scoped_path(root, name)
        t.require(path.is_file(), f'Declare individual input files, not a directory: {name}')
        manifest[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    return dict(task=copy.deepcopy(task), branch=copy.deepcopy(state['branch']),
                accepted_inputs=accepted, source_manifest=manifest,
                historical_sources=historical,
                result_contract={key: copy.deepcopy(t.POLICY[key]) for key in
                                 ('result_fields', 'metadata_fields', 'structural_use_fields',
                                  'interaction_fields', 'worker_results')},
                repair_reasons=state['tasks'][task['id']].get('last_isolated_failure', []) +
                               [review['reason'] for past in state['tasks'][task['id']]['history'][-1:]
                                for review in past['reviews'] if review['decision'] == 'reject'],
                context_policy=copy.deepcopy(t.POLICY['context_policy']),
                worker_instruction=t.POLICY['worker_instruction'])


def run_one(state: dict, root: Path, attempts: Path, auth: Path, timeout: int,
            runtime_paths: list[dict] | None = None, review_attempt: Path | None = None) -> dict:
    """Mutate state only after two fresh reviews; keep failed attempts on disk."""
    packet = assignment(state, root)
    runtimes = runtime_paths or []
    targets = set()
    for mount in runtimes:
        t.require(set(mount) == {'source', 'target'}, 'Invalid runtime mount')
        source, target = Path(mount['source']).resolve(), Path(mount['target'])
        t.require(source.is_dir() and not root.resolve().is_relative_to(source) and
                  not attempts.resolve().is_relative_to(source) and
                  not auth.resolve().is_relative_to(source), 'Runtime exposes controller state or login')
        t.require(target.parent == Path('/runtime') and '..' not in target.parts and
                  str(target) not in targets, 'Runtime mounts need distinct names under /runtime')
        targets.add(str(target))
    packet['runtime_targets'] = sorted(targets)
    runner.sandbox_probe()  # No fallback to execution in the operator's context.
    attempt = attempts / uuid.uuid4().hex
    attempt.mkdir(parents=True)
    view = attempt / 'input'
    view.mkdir()
    sources = view / 'sources'
    sources.mkdir()
    for name in packet['source_manifest']:
        target = sources / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(scoped_path(root, name), target)
    t.require(runner.files(sources) == packet['source_manifest'], 'Inputs changed during snapshot')
    (view / 'policy').mkdir()
    shutil.copyfile(runner.POLICY / 'network_worker.py', view / 'policy/network_worker.py')
    runner.write(view / 'contract.json', {'runtime_paths': runtimes})
    runner.write(view / 'assignment.json', packet)
    task = packet['task']
    name = task['allowed_write']
    executor_packet = copy.deepcopy(packet)
    executor_packet['worker_instruction'] += (
        '\nRead /input/assignment.json. Declared files are under /input/sources. '
        'Write only /output/artifact/' + name + ' and /output/result.json. '
        'The result JSON has these fields: ' + ', '.join(t.POLICY['result_fields']) + '. '
        'Metadata fields: ' + ', '.join(t.POLICY['metadata_fields']) + '. '
        'Use null for unused structural_use and interaction, and lists for changed_objects, '
        'changed_accounts and side_observations. Evidence entries have path, sha256, locator; '
        'paths are relative to the repository, without /input/sources or /output/artifact. '
        'implementation_status must be exactly "none" or "kernel_checked" (put all explanatory '
        'text in output). first_missing_inference must be a string, empty when absent. '
        'changed_objects lists representation or domain changes requiring transport; a new '
        'definition on unchanged objects does not itself belong in that list. '
        'Return SUBMITTED_RESULT, NEEDS_DECOMPOSITION, BLOCKED_WITH_REASON or COUNTEREXAMPLE_CANDIDATE. '
        'If the assignment requires several unresolved inferences, return NEEDS_DECOMPOSITION '
        'and immediate subobligations; do not solve those children. End the process after this result.')
    if review_attempt is None:
        executor, _ = runner.launch('atomic_executor', view, attempt / 'executor', executor_packet,
                                    attempt / 'executor.log', auth, timeout)
        runner.write(attempt / 'executor-checkpoint.json', {'session': executor})
    else:
        t.require(review_attempt.resolve().is_relative_to(attempts.resolve()),
                  'Only a prior isolated attempt may be sent for fresh review')
        saved = runner.read(review_attempt / 'input/assignment.json')
        t.require(all(saved.get(key) == packet.get(key) for key in
                      ('task', 'branch', 'source_manifest', 'accepted_inputs', 'context_policy')),
                  'Saved assignment or evidence changed; cannot reuse its result')
        runner.files(review_attempt / 'executor')
        checkpoint = review_attempt / 'executor-checkpoint.json'
        if checkpoint.exists():
            executor = runner.read(checkpoint)['session']
        else:
            # Older failed attempts retain the actual fresh CLI session header.
            header = (review_attempt / 'executor.log').read_text().split('\nuser\n', 1)[0]
            match = re.search(r'^session id: ([0-9a-f-]+)$', header, re.M)
            t.require(match is not None, 'No saved isolated worker identity')
            executor = match.group(1)
        shutil.copytree(review_attempt / 'executor', attempt / 'executor')
        runner.write(attempt / 'executor-checkpoint.json',
                     {'session': executor, 'reused_from': str(review_attempt)})
    output = attempt / 'executor'
    expected = {'schema.json', 'response.json', 'result.json', 'artifact/' + name}
    t.require(set(runner.files(output)) <= expected, 'Worker wrote outside its single artifact scope')
    result = runner.read(output / 'result.json')
    artifact = output / 'artifact' / name
    t.require(artifact.is_file(), 'Task must return its designated evidence artifact')
    # Bind the actual artifact mechanically; this is not mathematical acceptance.
    t.require(isinstance(result.get('evidence'), list), 'Result needs an evidence list')
    artifact_ref = dict(path=name, sha256=hashlib.sha256(artifact.read_bytes()).hexdigest(),
                        locator='designated task artifact')
    if not any(ref.get('path') == name for ref in result['evidence'] if isinstance(ref, dict)):
        result['evidence'].append(artifact_ref)
    if result.get('first_missing_inference') is None and result.get('status') == 'SUBMITTED_RESULT':
        result['first_missing_inference'] = ''
    implementation = result.get('implementation_status')
    if isinstance(implementation, str) and implementation.startswith('kernel_checked: '):
        result['output'] += '\nImplementation evidence: ' + implementation.split(': ', 1)[1]
        result['implementation_status'] = 'kernel_checked'
    review_view = attempt / 'review-input'
    shutil.copytree(view, review_view)
    proposed = review_view / 'sources' / name
    if proposed.exists():
        original = review_view / 'original' / name
        original.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(proposed, original)
    proposed.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(artifact, proposed)
    runner.write(review_view / 'submission.json', result)
    # Validate the result against the exact proposed tree, before paying for review.
    candidate = copy.deepcopy(state)
    t.submit(candidate, task['id'], result, review_view / 'sources', assignment_checked=True)
    reviews = []
    sessions = [executor]
    for index in range(2):
        review_packet = copy.deepcopy(packet)
        review_packet['worker_instruction'] = (
            'Fresh independent review of exactly one mathematical obligation. '
            'Read /input/assignment.json and /input/submission.json; evidence is in /input/sources. '
            'For an edited existing artifact, its input version is preserved under /input/original '
            'at the same relative path; accepted premises about that version remain tied to it. '
            'Check the stated goal against the complete retained hypotheses, same witnesses and '
            'declared scope. Accepted inputs are premises; do not repeat prior tasks. '
            'Reject task drift, missing inferences, unproved payoff or a construction without '
            'its full reviewed admission. Do not repair or extend the proof. '
            'Write only /output/review.json with reviewer, decision (accept or reject), reason, '
            'evidence (nonempty list of path, sha256, locator relative to sources). '
            'A decomposed or blocked result cannot be accepted as task completion. Stop after one verdict.')
        session, _ = runner.launch('atomic_reviewer', review_view, attempt / f'reviewer-{index}',
                                   review_packet, attempt / f'reviewer-{index}.log', auth, timeout)
        t.require(session not in sessions, 'Worker or reviewer context was reused')
        sessions.append(session)
        review_output = attempt / f'reviewer-{index}'
        t.require(set(runner.files(review_output)) <= {'schema.json', 'response.json', 'review.json'},
                  'Reviewer wrote outside its verdict scope')
        verdict = runner.read(review_output / 'review.json')
        verdict['reviewer'] = session  # Identity comes from the supervisor, not the model.
        # Validate each verdict independently so both can report a rejection.
        validation = copy.deepcopy(candidate)
        t.review(validation, task['id'], verdict, review_view / 'sources')
        reviews.append(verdict)
    receipt = dict(task_id=task['id'], sessions=sessions, input_hash=runner.digest(packet),
                   submission_hash=runner.digest(result), reviews=reviews)
    runner.write(attempt / 'receipt.json', receipt)
    if any(verdict['decision'] != 'accept' for verdict in reviews):
        item = state['tasks'][task['id']]
        item.setdefault('isolated_attempts', []).append(str(attempt / 'receipt.json'))
        item['last_isolated_failure'] = [verdict['reason'] for verdict in reviews
                                         if verdict['decision'] == 'reject']
        return dict(status='rejected', attempt=str(attempt), task_id=task['id'])
    for verdict in reviews:
        t.review(candidate, task['id'], verdict, review_view / 'sources')
    for path, digest in packet['source_manifest'].items():
        t.require(hashlib.sha256(scoped_path(root, path).read_bytes()).hexdigest() == digest,
                  'Source changed during isolated task; refusing integration')
    destination = scoped_path(root, name)
    t.require(name in packet['source_manifest'] or not destination.exists(),
              'Output appeared during isolated task; refusing overwrite')
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        old_bytes = destination.read_bytes()
        archive = root / 'tools/methodology_gate/evidence_snapshots' / hashlib.sha256(old_bytes).hexdigest()
        archive.parent.mkdir(parents=True, exist_ok=True)
        if not archive.exists():
            archive.write_bytes(old_bytes)
    temporary = destination.with_name(destination.name + '.atomic-' + attempt.name)
    shutil.copyfile(artifact, temporary)
    temporary.replace(destination)
    candidate['tasks'][task['id']]['context_receipt'] = receipt
    candidate['tasks'][task['id']].pop('last_isolated_failure', None)
    state.clear()
    state.update(candidate)
    return dict(status='accepted', attempt=str(attempt), task_id=task['id'])

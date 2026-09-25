"""Linux supervisor: fresh isolated executor, two fresh read-only reviewers, then commit.

No command accepts a user-supplied approval. Verdicts are read only from the
supervisor-launched review processes for the current immutable submission.
"""
from __future__ import annotations

import argparse
import contextlib
from concurrent.futures import ThreadPoolExecutor
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import uuid

from .core import (POLICY, COMMON_GATES, STAGE_GATES, Rejected, digest, last_event,
                   next_node, next_stage, record, require, validate_review,
                   validate_transition)
from .egress import broker
from .chain import validate_chain, implementation_work
from .policy.workflow import (STAGES, STAGE_ORDER, before, ordinal, bindings, active_artifacts,
                              authorization, residual_binding, dispatch_errors, repair_stage,
                              technique_signature, attempt_history)


class ArtifactFormatError(RuntimeError):
    pass


class CheckpointInvalid(RuntimeError):
    pass


class WorkerUnavailable(RuntimeError):
    pass


def engine_manifest():
    return {name: hashlib.sha256((Path(__file__).parent / name).read_bytes()).hexdigest()
            for name in ('core.py', 'runner.py', 'egress.py', 'chain.py')}


def read(path):
    return json.loads(Path(path).read_text())


def write(path, obj):
    path = Path(path)
    tmp = path.with_suffix(path.suffix + '.tmp')
    with tmp.open('w') as stream:
        stream.write(json.dumps(obj, indent=2) + '\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(tmp, path)
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def files(root):
    """No symlinks, devices or outside references can enter a trusted snapshot."""
    root = Path(root)
    result = {}
    for path in sorted(root.rglob('*')):
        if '__pycache__' in path.relative_to(root).parts:
            continue
        require(not path.is_symlink(), f'Symlink rejected: {path}')
        if path.is_dir():
            continue
        require(path.is_file(), f'Non-regular artifact: {path}')
        result[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def check_record_paths(state):
    for evidence in state['evidence'].values():
        p = Path(evidence['path'])
        require(not p.is_absolute() and '..' not in p.parts, 'Evidence must be snapshot-relative')


def visible_source_manifest(contract, stage):
    """Return the immutable source subset visible to one stage's workers."""
    manifest = contract['source_manifest']
    requested = contract.get('stage_input_paths', {}).get(str(stage))
    require(requested is not None, f'Stage {stage} has no explicit source scope')
    visible = {}
    for prefix in requested:
        prefix = prefix.rstrip('/')
        matches = {name: sha for name, sha in manifest.items()
                   if name == prefix or name.startswith(prefix + '/')}
        require(bool(matches), f'Stage {stage} source scope has no frozen files: {prefix}')
        visible.update(matches)
    require(bool(visible), f'Stage {stage} source scope is empty')
    return dict(sorted(visible.items()))


def restrict_source_tree(source_dir, manifest):
    """Remove out-of-scope source files from a worker's private read-only view."""
    source_dir = Path(source_dir)
    visible = set(manifest)
    for name in files(source_dir):
        if name not in visible:
            (source_dir / name).unlink()
    for directory in sorted((p for p in source_dir.rglob('*') if p.is_dir()),
                            key=lambda p: len(p.parts), reverse=True):
        if not any(directory.iterdir()):
            directory.rmdir()


def worker_contract(contract, stage, manifest):
    """Redact controller-only source inventory from the worker-visible contract."""
    result = dict(contract)
    result.pop('stage_input_paths', None)
    result['input_paths'] = sorted(manifest)
    result['source_manifest'] = manifest
    result['allowed_changes'] = [p for p in contract['allowed_changes'] if p in manifest]
    result['worker_stage'] = stage
    return result


def prepare_worker_view(source, destination, contract, assignment):
    stage = assignment['stage']
    scoped = str(stage) in contract.get('stage_input_paths', {})
    manifest = visible_source_manifest(contract, stage)
    shutil.copytree(source, destination)
    if scoped:
        restrict_source_tree(destination / 'sources', manifest)
        scoped_assignment = dict(assignment, visible_source_paths=sorted(manifest))
        write(destination / 'contract.json', worker_contract(contract, stage, manifest))
    else:
        scoped_assignment = dict(assignment)
        scoped_assignment.pop('visible_source_paths', None)
        write(destination / 'contract.json', contract)
    write(destination / 'assignment.json', scoped_assignment)
    return scoped_assignment


def freeze_preserved_files(before, after):
    old, new = files(before), files(after)
    for name, sha in old.items():
        if name == 'state.json':
            continue
        if name == 'execution.md':
            require((after / name).read_bytes().startswith((before / name).read_bytes()),
                    'Execution history was rewritten')
        else:
            require(new.get(name) == sha, f'Frozen evidence changed/deleted: {name}')


def sandbox_command(mounts, argv):
    """Construct a new root; do NOT ro-bind / (which would expose controller state)."""
    cmd = ['bwrap', '--unshare-all', '--die-with-parent', '--new-session',
           '--cap-drop', 'ALL', '--clearenv']
    for name in ('/usr', '/bin', '/sbin', '/lib', '/lib64'):
        p = Path(name)
        if p.is_symlink():
            cmd += ['--symlink', os.readlink(p), name]
        elif p.exists():
            cmd += ['--ro-bind', name, name]
    cmd += ['--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--tmpfs', '/home',
            '--dir', '/home/worker', '--dir', '/etc']
    for name in ('/etc/ssl', '/etc/resolv.conf', '/etc/hosts', '/etc/nsswitch.conf'):
        if Path(name).exists():
            cmd += ['--ro-bind', name, name]
    for source, target, writable in mounts:
        cmd += ['--bind' if writable else '--ro-bind', str(source), target]
    cmd += ['--setenv', 'HOME', '/home/worker', '--setenv', 'CODEX_HOME', '/home/worker/.codex',
            '--setenv', 'PATH', '/runtime/lean/bin:/usr/local/bin:/usr/bin:/bin', '--setenv', 'LANG', 'C.UTF-8',
            '--setenv', 'PYTHONDONTWRITEBYTECODE', '1', '--chdir', '/output', '--']
    return cmd + argv


def sandbox_probe():
    with tempfile.TemporaryDirectory(prefix='methodology-probe-') as tmp:
        p = Path(tmp)
        secret = p / 'controller-secret'
        secret.write_text('must not be visible')
        output = p / 'output'
        output.mkdir()
        command = sandbox_command([(output, '/output', True)], [
            '/usr/bin/python3', '-c',
            "from pathlib import Path; import os; "
            f"assert not Path({str(secret)!r}).exists(); "
            "assert not Path('/home/guillem').exists(); "
            "assert not Path('/proc/1/root/home/guillem').exists(); "
            "Path('/output/probe').write_text('isolated')"])
        result = subprocess.run(command, capture_output=True, text=True, timeout=20)
        require(result.returncode == 0 and (output / 'probe').read_text() == 'isolated',
                'OS isolation unavailable; refusing unsandboxed fallback: ' + result.stderr)


def review_schema(stage):
    evidence = {'type': 'object', 'additionalProperties': False,
                'properties': {k: {'type': 'string'} for k in ('path', 'sha256', 'locator')},
                'required': ['path', 'sha256', 'locator']}
    gate = {'type': 'object', 'additionalProperties': False, 'properties': {
        'verdict': {'type': 'string', 'enum': ['pass', 'fail']},
        'reason': {'type': 'string'}, 'evidence': {'type': 'array', 'items': evidence}},
        'required': ['verdict', 'reason', 'evidence']}
    keys = list(COMMON_GATES + STAGE_GATES[stage])
    properties = {'binding': {'type': 'string'}, 'decision': {'type': 'string', 'enum': ['accept', 'reject']},
                  'gates': {'type': 'object', 'additionalProperties': False,
                            'properties': {k: gate for k in keys}, 'required': keys},
                  'first_failure': {'type': 'string'}, 'repair': {'type': 'string'},
                  'repair_stage': {'enum': list(STAGE_ORDER[:ordinal(stage) + 1])},
                  'reviewed_facts': {'type': 'array', 'items': {'type': 'string'}},
                  'invalid_inherited_facts': {'type': 'array', 'items': {'type': 'string'}},
                  'revalidated_facts': {'type': 'array', 'items': {'type': 'string'}},
                  'unnecessary_facts': {'type': 'array', 'items': {'type': 'string'}}}
    properties['accepted_stage_revocation'] = {
        'type': ['object', 'null'], 'additionalProperties': False,
        'properties': {'stage': {'enum': list(STAGE_ORDER[:ordinal(stage)])},
                       'defect': {'type': 'string'},
                       'evidence': {'type': 'array', 'minItems': 1, 'items': evidence}},
        'required': ['stage', 'defect', 'evidence']}
    return {'type': 'object', 'additionalProperties': False, 'properties': properties,
            'required': list(properties)}


def launch(role, view, output, assignment, log, auth, timeout):
    """Only the controller selects role, invocation and output path; no worker callbacks."""
    session = uuid.uuid4().hex
    output.mkdir()
    atomic = role in {'atomic_executor', 'atomic_reviewer'}
    if role == 'executor':
        source = view / ('saved-submission' if assignment.get('artifact_format_repair') else '')
        shutil.copytree(source / 'record', output / 'record')
        if assignment.get('artifact_format_repair') and (source / 'changes').exists():
            shutil.copytree(source / 'changes', output / 'changes')
    schema = review_schema(assignment['stage']) if role != 'executor' and not atomic else {
        'type': 'object', 'additionalProperties': False,
        'properties': {'summary': {'type': 'string'}}, 'required': ['summary']}
    write(output / 'schema.json', schema)
    private_home = output.parent / ('home-' + session)
    private_home.mkdir()
    # No host config, plugins, MCP servers, hooks, sessions or credentials beyond
    # Codex's existing login. The auth copy is never part of a proof snapshot.
    shutil.copyfile(auth, private_home / 'auth.json')
    os.chmod(private_home / 'auth.json', 0o600)
    if atomic:
        prompt = assignment['worker_instruction']
    else:
        prompt = (POLICY / ('executor-prompt.md' if role == 'executor' else 'reviewer-prompt.md')).read_text()
    prompt += '\n\nCONTROLLER ASSIGNMENT\n' + json.dumps(assignment, indent=2)
    argv = ['/usr/local/bin/codex', 'exec', '--ignore-user-config', '--ignore-rules',
            '--ephemeral', '--skip-git-repo-check', '-c', 'approval_policy="never"',
            '--sandbox', 'danger-full-access', '--output-schema', '/output/schema.json',
            '--output-last-message', '/output/response.json', '-']
    # The inner CLI runs without a second sandbox because this entire process,
    # including every shell child, is already confined by bubblewrap's new root.
    try:
        with tempfile.TemporaryDirectory(prefix='mg-net-') as netdir, broker(Path(netdir) / 'api.sock') as proxy:
            mounts = [(view, '/input', False), (output, '/output', True),
                      (private_home, '/home/worker/.codex', True),
                      (proxy, '/run/api-proxy.sock', False)]
            mounts += [(m['source'], m['target'], False)
                       for m in read(view / 'contract.json').get('runtime_paths', [])]
            cmd = sandbox_command(mounts,
                                  ['/usr/bin/python3', '/input/policy/network_worker.py'] + argv)
            with log.open('wb') as stream:
                result = subprocess.run(cmd, input=prompt.encode(), stdout=stream, stderr=stream, timeout=timeout)
        if result.returncode != 0:
            raise WorkerUnavailable(f'{role} process failed; inspect {log.name}')
        files(output)  # Reject links before following response.json.
        require((output / 'response.json').stat().st_size < 4_000_000, 'Oversized response')
        return session, read(output / 'response.json')
    finally:
        shutil.rmtree(private_home)


@contextlib.contextmanager
def locked(run):
    with (run / 'lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        yield


def committed(run):
    head = read(run / 'HEAD.json')
    receipt = read(run / 'commits' / (head['snapshot'] + '.json'))
    require(digest(receipt) == head['receipt'], 'Commit receipt tampered with')
    snapshot = run / 'snapshots' / head['snapshot']
    require(digest(files(snapshot)) == head['digest'], 'Committed snapshot tampered with')
    return snapshot


def commit(run, source, event):
    previous = read(run / 'HEAD.json') if (run / 'HEAD.json').exists() else None
    name = f'{len(list((run / "snapshots").iterdir())):06d}-{uuid.uuid4().hex[:12]}'
    dest = run / 'snapshots' / name
    shutil.copytree(source, dest)
    receipt = {'snapshot': name, 'digest': digest(files(dest)), 'previous': previous,
               'event': event, 'time': time.time()}
    write(run / 'commits' / (name + '.json'), receipt)
    head = {'snapshot': name, 'digest': receipt['digest'], 'receipt': digest(receipt)}
    write(run / 'HEAD.json', head)


def claim_binding(state):
    return digest({k: state[k] for k in ('claim', 'scope', 'root', 'facts', 'nodes')})


def accepted_sibling(run, contract_file, binding):
    """Catch accidental fresh starts beside an already reviewed run of this claim."""
    for parent in {run.parent, contract_file.parent}:
        if not parent.is_dir():
            continue
        for sibling in parent.iterdir():
            if sibling == run or not (sibling / 'contract.json').is_file():
                continue
            previous = read(sibling / 'contract.json')
            if previous.get('claim_binding') != binding:
                continue
            snapshot = committed(sibling)
            state = read(snapshot / 'record/state.json')
            if any(active_artifacts(state, item['id']) for item in state['nodes']):
                return sibling
    return None


def initialize(run, repo, source_record, contract_file, continuation=None):
    require(not run.exists(), 'Refusing to overwrite a run')
    contract = read(contract_file)
    required = {'name', 'input_paths', 'allowed_changes', 'checks'}
    require(required <= set(contract) <= required | {'runtime_paths', 'repair_roots', 'lean_projects', 'stage_input_paths'}, 'Unexpected contract fields')
    stage_inputs = contract.get('stage_input_paths', {})
    require(isinstance(stage_inputs, dict) and
            set(stage_inputs) == {str(n) for n in STAGE_ORDER} and
            all(stage in {str(n) for n in STAGE_ORDER} and isinstance(paths, list) and
                bool(paths) and all(isinstance(path, str) and bool(path.strip()) for path in paths)
                for stage, paths in stage_inputs.items()), 'Every stage needs an explicit, nonempty source scope')
    for mount in contract.get('runtime_paths', []):
        require(set(mount) == {'source', 'target'}, 'Invalid runtime mount')
        target = Path(mount['target'])
        require(target.is_absolute() and target.parent == Path('/runtime') and
                '..' not in target.parts, 'Runtime mounts must be named children of /runtime')
        source = Path(mount['source']).resolve()
        require(source.exists() and not run.is_relative_to(source) and not source.is_relative_to(run),
                'Runtime mount exposes controller state')
    for p in contract['input_paths'] + contract['allowed_changes']:
        require(not Path(p).is_absolute() and '..' not in Path(p).parts, 'Unsafe contract path')
    for paths in stage_inputs.values():
        for p in paths:
            require(not Path(p).is_absolute() and '..' not in Path(p).parts,
                    'Unsafe stage-specific source path')
    require(isinstance(contract['checks'], list), 'Checks must be operator-defined command arrays')
    for check in contract['checks']:
        require(set(check) == {'name', 'argv'} and isinstance(check['name'], str) and
                isinstance(check['argv'], list) and bool(check['argv']) and
                all(isinstance(x, str) and bool(x) for x in check['argv']), 'Invalid verification command')
    require(not run.is_relative_to(repo), 'Controller state must live outside the repository')
    initial = read(source_record / 'state.json')
    if continuation is not None:
        initial['methodology_sources'] = record.SOURCES
    files(source_record)
    check_record_paths(initial)
    require(not record.validate(initial, source_record, repo), 'Initial record invalid')
    if continuation is None:
        prior = accepted_sibling(run, contract_file, claim_binding(initial))
        require(prior is None,
                f'Accepted stage already exists in {prior}; continue that reviewed prefix instead of repeating it')
    run.mkdir(parents=True, mode=0o700)
    (run / 'snapshots').mkdir()
    (run / 'commits').mkdir()
    (run / 'attempts').mkdir()
    snapshot = run / 'initial'
    snapshot.mkdir()
    shutil.copytree(source_record, snapshot / 'record')
    sources = snapshot / 'sources'
    if continuation is None:
        sources.mkdir()
    else:
        shutil.copytree(continuation / 'sources', sources)
    for relative in contract['input_paths']:
        origin = repo / relative
        target = sources / relative
        require(origin.resolve().is_relative_to(repo), 'Source escapes repository')
        if continuation is not None and target.exists():
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        if origin.is_dir():
            shutil.copytree(origin, target, symlinks=True)
        else:
            shutil.copyfile(origin, target)
    files(sources)
    shutil.copytree(POLICY, snapshot / 'policy', ignore=shutil.ignore_patterns('__pycache__'))
    state = initial
    require(len(state['nodes']) == 1 and state['nodes'][0]['status'] == 'open',
            'Import currently supports one open branch; do not flatten an expanded tree')
    if continuation is None:
        require(not state.get('events'), 'Initialize a fresh canonical run without imported closure-attempt history')
    else:
        node = next_node(state)
        require(node is not None and bool(active_artifacts(state, node)) and next_stage(state, node) != 1,
                'Continuation needs an accepted prior stage and an open later stage')
    state['status'] = 'active'
    if continuation is None:
        state['events'] = []
        state['semantic_review'] = []
    write(snapshot / 'record/state.json', state)
    contract['claim_binding'] = claim_binding(state)
    contract['source_manifest'] = files(sources)
    for stage in stage_inputs:
        visible_source_manifest(contract, '3b' if stage == '3b' else int(stage))
    contract['policy_manifest'] = files(snapshot / 'policy')
    contract['engine_manifest'] = engine_manifest()
    write(run / 'contract.json', contract)
    (run / 'contract.sha256').write_text(digest(contract))
    if continuation is None:
        commit(run, snapshot, {'kind': 'initialized', 'next': 'independently verify stage 1'})
    else:
        commit(run, snapshot, {'kind': 'continued', 'next_stage': next_stage(state, next_node(state)),
                               'accepted_prefix': bindings(state, next_node(state), next_stage(state, next_node(state)))})


def continue_run(run, old_run, repo, contract_file):
    """Extend a later-stage source scope while retaining accepted stage events."""
    require(run != old_run and run.parent == old_run.parent,
            'Continue beside the existing run; never overwrite its reviewed record')
    snapshot = committed(old_run)
    old_contract = read(old_run / 'contract.json')
    require(digest(old_contract) == (old_run / 'contract.sha256').read_text(), 'Old contract changed')
    require(files(snapshot / 'sources') == old_contract['source_manifest'], 'Old sources changed')
    require(files(snapshot / 'policy') == old_contract['policy_manifest'], 'Old policy snapshot changed')
    require(files(POLICY) == old_contract['policy_manifest'],
            'Run does not match the current benchmark policy')
    state = read(snapshot / 'record/state.json')
    node = next_node(state)
    require(node is not None, 'Cannot continue a completed node')
    accepted = active_artifacts(state, node)
    require(bool(accepted), 'No accepted stage to carry forward')
    new_contract = read(contract_file)
    for key in ('name', 'checks', 'runtime_paths', 'repair_roots', 'lean_projects'):
        require(new_contract.get(key) == old_contract.get(key),
                f'Continuation changed a fixed contract field: {key}')
    require(set(old_contract['allowed_changes']) <= set(new_contract['allowed_changes']),
            'Continuation cannot withdraw authorized source paths')
    require(set(old_contract['input_paths']) <= set(new_contract['input_paths']),
            'Continuation cannot remove frozen source paths')
    for stage in accepted:
        key = str(stage)
        require(new_contract['stage_input_paths'][key] == old_contract['stage_input_paths'][key],
                f'Accepted Stage {stage} source scope changed')
    old_workflow = read(snapshot / 'policy/workflow.json')
    new_workflow = read(POLICY / 'workflow.json')
    for stage in accepted:
        old_definition = next(s for s in old_workflow['stages'] if s['number'] == stage)
        new_definition = next(s for s in new_workflow['stages'] if s['number'] == stage)
        require(old_definition == new_definition,
                f'Accepted Stage {stage} contract changed')
    require((snapshot / 'policy/structural-register.json').read_bytes() ==
            (POLICY / 'structural-register.json').read_bytes(),
            'Structural register changed; accepted classifications need explicit review')
    initialize(run, repo, snapshot / 'record', contract_file, continuation=snapshot)


def check_contract(run, snapshot):
    contract = read(run / 'contract.json')
    require(digest(contract) == (run / 'contract.sha256').read_text(), 'Contract changed')
    require(files(snapshot / 'sources') == contract['source_manifest'], 'Source snapshot changed')
    for stage in contract.get('stage_input_paths', {}):
        visible_source_manifest(contract, '3b' if stage == '3b' else int(stage))
    require(files(snapshot / 'policy') == contract['policy_manifest'], 'Methodology changed')
    # The installed controller itself is trusted, but must not drift mid-run.
    require(files(POLICY) == contract['policy_manifest'], 'Installed policy drift; no silent update')
    require(engine_manifest() == contract['engine_manifest'], 'Controller drift; no silent update')
    return contract


def reopen_for_repair(state, node, restart):
    current = next(n for n in state['nodes'] if n['id'] == node)
    if current['status'] == 'closed' and ordinal(restart) <= ordinal(7):
        current['status'] = 'expanded' if current['children'] else 'open'
        current.pop('certificate', None)
        if not current['children'] and current['id'] not in state['queue']:
            state['queue'].append(current['id'])


def reviewed_restart_stage(reviews, assignment, state, accepted_failure=False):
    """A reviewed stage survives unless both reviewers revoke it explicitly."""
    current = assignment['stage']
    relevant = reviews if accepted_failure else [r for r in reviews if r['decision'] == 'reject']
    requested = min((r['repair_stage'] for r in relevant), key=ordinal, default=current)
    if before(requested, current) and requested in active_artifacts(state, assignment['node']):
        unanimous = len(reviews) == 2 and all(
            r['repair_stage'] == requested and
            isinstance(r.get('accepted_stage_revocation'), dict) and
            r['accepted_stage_revocation']['stage'] == requested and
            (accepted_failure or r['decision'] == 'reject') for r in reviews)
        return requested if unanimous else current
    return requested


def rejection(run, snapshot, assignment, reason, reviews, proposal=None):
    """Rejection is an active repair transition, not a terminal status."""
    with tempfile.TemporaryDirectory(prefix='methodology-repair-') as tmp:
        dest = Path(tmp) / 'snapshot'
        shutil.copytree(snapshot, dest)
        state = read(dest / 'record/state.json')
        relative = f'gate-rejections/{assignment["attempt"]}.json'
        path = dest / 'record' / relative
        path.parent.mkdir(exist_ok=True)
        write(path, {'assignment': assignment, 'first_failure': reason, 'reviews': reviews,
                     'next_action': 'Execute prescribed repair under the complete retained residual.'})
        if proposal:
            archive = dest / 'record' / 'gate-rejections' / assignment['attempt']
            archive.mkdir()
            baseline_files = files(snapshot)
            proposal_files = files(proposal)
            write(archive / 'base-manifest.json', baseline_files)
            write(archive / 'submission-manifest.json', proposal_files)
            # Keep the exact failed construction, without recursively duplicating
            # all old rejection archives. Unchanged files remain in /input.
            for name, sha in proposal_files.items():
                if baseline_files.get(name) != sha:
                    target = archive / 'submission' / name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(proposal / name, target)
        ref = 'gate-' + assignment['attempt']
        state['evidence'][ref] = {'path': relative, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                                 'locator': 'first_failure and reviews', 'proves': 'Exact rejected obligation and repair instruction'}
        # Facts independently established by BOTH reviewers survive even when
        # another part of the submission fails. Never promote unreviewed facts.
        if proposal and len(reviews) == 2:
            candidate = read(proposal / 'record/state.json')
            shared = set(reviews[0]['reviewed_facts']) & set(reviews[1]['reviewed_facts'])
            current = next(n for n in state['nodes'] if n['id'] == assignment['node'])
            for fact_id in sorted(shared - set(state['facts'])):
                fact = candidate['facts'][fact_id]
                candidate_node = next(n for n in candidate['nodes'] if n['id'] == assignment['node'])
                if fact['kind'] != 'derived' or fact_id not in candidate_node['facts']:
                    continue  # A verified child case is not a theorem on its parent.
                for eid in fact['evidence']:
                    entry = candidate['evidence'][eid]
                    target = dest / 'record' / entry['path']
                    target.parent.mkdir(parents=True, exist_ok=True)
                    if target.exists():
                        require(hashlib.sha256(target.read_bytes()).hexdigest() == entry['sha256'], 'Fact evidence collision')
                    else:
                        shutil.copyfile(proposal / 'record' / entry['path'], target)
                    state['evidence'][eid] = entry
                state['facts'][fact_id] = fact
                def retain(item):
                    if fact_id not in item['facts']:
                        item['facts'].append(fact_id)
                    for child in item['children']:
                        retain(next(n for n in state['nodes'] if n['id'] == child))
                retain(current)
        event = {'node': assignment['node'], 'stage': assignment['stage'], 'result': 'failed',
                 'evidence': [ref], 'reason': reason}
        # Failure reserves an attempt, never the structural property itself.
        selected = authorization(state, assignment['node'])
        if selected and assignment['stage'] == 6:
            event['attempted_technique'] = technique_signature(selected['artifact'])
        elif proposal and assignment['stage'] == 5:
            submitted = {}
            try:
                candidate_events = read(proposal / 'record/state.json').get('events', [])
                if isinstance(candidate_events, list) and candidate_events and isinstance(candidate_events[-1], dict):
                    submitted = candidate_events[-1].get('artifact', {})
            except (OSError, ValueError, TypeError, AttributeError):
                pass  # A malformed proposal still needs a durable repair record.
            if isinstance(submitted, dict) and all(isinstance(submitted.get(k), str) for k in
                    ('aspect_id', 'technique_id', 'operation', 'object', 'output')):
                event['attempted_technique'] = technique_signature(submitted)
        event['restart_stage'] = reviewed_restart_stage(reviews, assignment, state)
        invalid = set().union(*(set(r.get('invalid_inherited_facts', [])) for r in reviews))
        if invalid:
            require(invalid <= set(state['facts']), 'Cannot quarantine unknown facts')
            if state.get('unnecessary_facts'):
                state['unnecessary_facts'] = sorted(set(state['unnecessary_facts']) - invalid)
            state['quarantined_facts'] = sorted(set(state.get('quarantined_facts', [])) | invalid)
            # Quarantine is immediate, but it does not silently revoke an
            # independently accepted earlier stage. Reviewers can identify an
            # actual defect in that stage and unanimously reopen it.
        state['events'].append(event)
        state['status'] = 'active'
        reopen_for_repair(state, assignment['node'], event['restart_stage'])
        write(dest / 'record/state.json', state)
        require(not record.validate(state, dest / 'record'), 'Controller repair record invalid')
        commit(run, dest, {'kind': 'repair_queued', 'assignment': assignment, 'reason': reason})


def run_checks(proposal, contract, attempt, timeout):
    """Controller-owned checks, isolated just like agents; results cannot be self-reported."""
    results = []
    for index, check in enumerate(contract['checks']):
        output = attempt / f'check-{index}'
        output.mkdir()
        shutil.copytree(proposal / 'sources', output / 'workspace')
        if (proposal / 'changes').exists():
            for name in files(proposal / 'changes'):
                target = output / 'workspace' / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(proposal / 'changes' / name, target)
        log = attempt / f'check-{index}.log'
        mounts = [(proposal, '/input', False), (output, '/output', True)]
        mounts += [(m['source'], m['target'], False) for m in contract.get('runtime_paths', [])]
        cmd = sandbox_command(mounts, check['argv'])
        with log.open('wb') as stream:
            proc = subprocess.run(cmd, stdout=stream, stderr=stream, timeout=timeout)
        results.append({'name': check['name'], 'argv': check['argv'], 'exit_code': proc.returncode})
        destination = proposal / 'controller-checks'
        destination.mkdir(exist_ok=True)
        shutil.copyfile(log, destination / log.name)
    write(proposal / 'controller-checks.json', results)
    require(all(r['exit_code'] == 0 for r in results), 'Controller-run verification failed')


def checkpoint_launch(role, view, attempt, key, assignment, auth, timeout):
    """Cache only controller-observed results, bound to the exact read-only input.

    A killed worker gets a fresh process/output directory. A completed worker is
    reused; failed format validation invalidates only that review's cache.
    """
    cache = attempt / (key + '-checkpoint.json')
    binding = digest({'assignment': assignment, 'input': files(view)})
    if cache.exists():
        saved = read(cache)
        if saved['binding'] != binding:
            raise CheckpointInvalid('Checkpoint input changed')
        output = attempt / saved['output']
        if files(output) != saved['manifest']:
            raise CheckpointInvalid('Checkpoint output changed')
        return saved['session'], saved['response'], output
    output = attempt / (key + '-try-' + uuid.uuid4().hex)
    feedback_path = attempt / (key + '-feedback.json')
    task = dict(assignment)
    if feedback_path.exists():
        task['review_format_repair'] = read(feedback_path)
    repair_path = attempt / 'executor-format-repair.json'
    launch_view = view
    if role == 'executor' and repair_path.exists():
        repair = read(repair_path)
        previous = attempt / repair['checkpoint']['output']
        if files(previous) != repair['checkpoint']['manifest']:
            raise CheckpointInvalid('Saved format-repair submission changed')
        launch_view = attempt / ('format-input-' + uuid.uuid4().hex)
        shutil.copytree(view, launch_view)
        saved = launch_view / 'saved-submission'
        saved.mkdir()
        shutil.copytree(previous / 'record', saved / 'record')
        if (previous / 'changes').exists():
            shutil.copytree(previous / 'changes', saved / 'changes')
        task['artifact_format_repair'] = {
            'errors': repair['errors'], 'saved_submission': '/input/saved-submission',
            'instruction': 'Correct only the reported representation/schema problems in the supplied '
            'submission. Preserve its mathematics, evidence, source changes and single stage event. '
            'Do not rerun setup or restart proof work; keep exactly one event for this assignment.'}
    session, response = launch(role, launch_view, output, task,
                               output.with_suffix('.log'), auth, timeout)
    write(cache, {'binding': binding, 'output': output.name,
                  'manifest': files(output), 'session': session, 'response': response})
    return session, response, output


def invalidate_review(attempt, key, exc):
    cache = attempt / (key + '-checkpoint.json')
    previous = read(cache) if cache.exists() else None
    feedback = {'error': str(exc), 'previous_response': previous and previous['response'],
                'instruction': 'Repair this reviewer response against the SAME submission. '
                'Preserve substantive objections; correct only invalid metadata or unsupported '
                'review assertions. Do not ask the executor to redo this step.'}
    write(attempt / (key + '-feedback.json'), feedback)
    if cache.exists():
        cache.rename(attempt / (key + '-invalid-' + uuid.uuid4().hex + '.json'))


def tick(run, auth, timeout):
    snapshot = committed(run)
    contract = check_contract(run, snapshot)
    state = read(snapshot / 'record/state.json')
    node = next_node(state)
    if node is None:
        require(not record.validate(state, snapshot / 'record', complete=True), 'Missing final certificate')
        return 'complete'
    dispatch = dispatch_errors(state, node, next_stage(state, node))
    if dispatch:
        assignment = {'attempt': uuid.uuid4().hex, 'node': node, 'stage': next_stage(state, node),
                      'parent': digest(files(snapshot)), 'contract': digest(contract)}
        rejection(run, snapshot, assignment, '; '.join(dispatch), [])
        return 'repair_queued'
    pending = run / 'pending.json'
    parent = digest(files(snapshot))
    saved = read(pending) if pending.exists() else None
    if saved and saved['parent'] == parent and saved['contract'] == digest(contract):
        assignment = saved
        attempt = run / 'attempts' / assignment['attempt']
        view = attempt / 'input'
    else:
        attempt_id = uuid.uuid4().hex
        attempt = run / 'attempts' / attempt_id
        attempt.mkdir()
        assignment = {'attempt': attempt_id, 'node': node, 'stage': next_stage(state, node),
                      'parent': parent, 'contract': digest(contract),
                      'gates': list(COMMON_GATES + STAGE_GATES[next_stage(state, node)])}
        view = attempt / 'input'
        # Give workers the actual recipe section, not a generic demand for closure.
        stage = assignment['stage']
        assignment['stage_contract'] = STAGES[stage]
        assignment['accepted_inputs'] = bindings(state, node, stage)
        accepted = active_artifacts(state, node)
        assignment['accepted_artifacts'] = ({'3': accepted[3]['artifact']}
            if stage == '3b' else {str(n): e['artifact'] for n, e in accepted.items()})
        assignment['residual_binding'] = residual_binding(state, node)
        if stage == '3b':
            owner = next(item for item in state['nodes'] if item['id'] == node)
            assignment['stage3b_focus'] = {
                'incoming_residual': owner['residual'],
                'retained_fact_ids': owner['facts'],
                'selected_aspect': accepted[3]['artifact']['selected_aspect'],
                'selected_structure': accepted[3]['artifact']['structural_opportunity']}
        assignment['construction_authorization'] = authorization(state, node) if stage in (6, 7, 8) else None
        assignment['attempt_history'] = attempt_history(state, node)
        assignment['source_changes_permitted'] = stage in ('3b', 6)
        assignment['unavailable_premises'] = {
            key: state['facts'][key] for key in state.get('quarantined_facts', [])}
        work = implementation_work(state.get('implementation_chain', {}))
        assignment['upstream_implementation_queue'] = work['repair']
        assignment['adapter_followups'] = work['adapters']
        assignment['evidence_reconciliation_batch'] = work['reconcile']
        assignment['reused_checked_facts'] = work['reuse']
        assignment['implementation_policy'] = (
            'Retain the exact original target and required implementation chain. Reuse checked '
            'statements at their actual types; do not recursively re-prove settled input. Concrete '
            'missing hypotheses remain obligations, not premises. New mathematical prerequisite '
            'work requires structural reasoning and a proved application to the waiting consumer. '
            'Bookkeeping, adapters and prerequisite lemmas are not standalone proof advancement. '
            'Stage 3b may publish only the selected Lean-checked structure to the exact ledger; '
            'Stage 6 constructs the productive move; Stage 8 checks the chain.')
        assignment = prepare_worker_view(snapshot, view, contract, assignment)
        write(pending, assignment)
    safe_proposal = None
    try:
        executor_id, _, executor_output = checkpoint_launch(
            'executor', view, attempt, 'executor', assignment, auth, timeout)
        proposal = attempt / 'proposal'
        # Rebuild deterministically from the cached executor; reviewers are bound
        # to these bytes, never to a mutable working directory.
        shutil.rmtree(proposal, ignore_errors=True)
        shutil.copytree(view, proposal)
        if str(assignment['stage']) in contract.get('stage_input_paths', {}):
            shutil.rmtree(proposal / 'sources')
            shutil.copytree(snapshot / 'sources', proposal / 'sources')
            write(proposal / 'contract.json', contract)
        shutil.rmtree(proposal / 'record')
        shutil.copytree(executor_output / 'record', proposal / 'record', symlinks=True)
        files(proposal)
        safe_proposal = proposal
        candidate = read(proposal / 'record/state.json')
        check_record_paths(candidate)
        freeze_preserved_files(snapshot / 'record', proposal / 'record')
        validate_transition(state, candidate, proposal / 'record', node, assignment['stage'])
        # Source changes are delivered as full replacement files, never applied
        # to live sources by a worker. Reviewers inspect them beside the originals.
        if (executor_output / 'changes').exists():
            changed = files(executor_output / 'changes')
            require(not changed or assignment['stage'] in ('3b', 6),
                    'Source changes are limited to the Stage 3b structure and Stage 6 construction')
            authorized = set(contract['allowed_changes'])
            for fact in state.get('implementation_chain', {}).get('facts', {}).values():
                path = fact.get('path', '')
                if any(Path(path).is_relative_to(root) for root in contract.get('repair_roots', [])):
                    require(path in contract['source_manifest'], 'Owner absent from frozen sources')
                    authorized.add(path)
            require(set(changed) <= authorized, 'Edit outside reviewed upstream owners and authorized files')
            if assignment['stage'] == '3b':
                structure = candidate['events'][-1].get('artifact', {})
                require(candidate['events'][-1]['result'] != 'done' or
                        (bool(changed) and structure.get('source_path') in changed and
                         set(changed) <= set(visible_source_manifest(contract, '3b'))),
                        'Stage 3b must submit its exact scoped Lean ledger publication')
            shutil.copytree(executor_output / 'changes', proposal / 'changes', dirs_exist_ok=True)
        elif assignment['stage'] == '3b' and candidate['events'][-1]['result'] == 'done':
            raise Rejected('Stage 3b must submit a checked Lean ledger publication')
        if assignment['stage'] == 8:
            old_changes = files(snapshot / 'changes') if (snapshot / 'changes').exists() else {}
            new_changes = files(proposal / 'changes') if (proposal / 'changes').exists() else {}
            require(old_changes == new_changes, 'Stage 8 cannot change sources after verification')
        if (state.get('implementation_chain') or candidate.get('implementation_chain') or
                (contract.get('lean_projects') and candidate['events'][-1]['result'] == 'done')):
            chain = candidate.get('implementation_chain')
            require(not state.get('implementation_chain') or isinstance(chain, dict),
                    'Previously recorded implementation dependency chain removed')
            errors = validate_chain(chain, proposal / 'sources', complete=False, replacements=proposal / 'changes')
            if errors:
                raise ArtifactFormatError('Implementation chain format: ' + '; '.join(errors))
            if node == candidate['root'] and assignment['stage'] == 8 and candidate['events'][-1]['result'] == 'done':
                require(not validate_chain(chain, proposal / 'sources', complete=True, replacements=proposal / 'changes'),
                        'Required implementation chain remains unproved')
            if node != candidate['root'] and assignment['stage'] == 8 and candidate['events'][-1]['result'] == 'done':
                current_node = next(n for n in candidate['nodes'] if n['id'] == node)
                local_target = current_node.get('implementation_target')
                require(local_target in chain['facts'], 'Child verification needs its exact implementation target')
                relevant = set()
                def collect(key):
                    if key in relevant:
                        return
                    relevant.add(key)
                    for dependency in chain['facts'][key]['dependencies']:
                        collect(dependency)
                collect(local_target)
                local_chain = {'target': local_target, 'facts': {k: chain['facts'][k] for k in relevant}}
                require(not validate_chain(local_chain, proposal / 'sources', complete=True, replacements=proposal / 'changes'),
                        'Child implementation chain remains unresolved')
            for fact in chain['facts'].values():
                for key in ('statement_evidence', 'publication_evidence', 'unnecessary_evidence', 'work_evidence'):
                    require(all(e in candidate['evidence'] for e in fact.get(key, [])),
                            'Unknown implementation-chain proof evidence')
            old_chain = state.get('implementation_chain', {})
            require(not old_chain or old_chain['target'] == chain['target'], 'Implementation target changed')
            require(set(old_chain.get('facts', {})) <= set(chain['facts']), 'Required upstream obligation deleted')
            for key, old_fact in old_chain.get('facts', {}).items():
                for field in ('statement', 'owner', 'path', 'declaration'):
                    require(old_fact[field] == chain['facts'][key][field], 'Required upstream contract changed')
                if old_fact['status'] == 'kernel_checked' and chain['facts'][key]['status'] != 'kernel_checked':
                    reopened = chain['facts'][key]
                    require(reopened.get('work_kind') == 'proof_repair' and
                            bool(reopened.get('work_evidence')) and bool(reopened.get('work_reason')),
                            'Cannot reopen checked input without an evidenced concrete defect')
                require(set(old_fact['dependencies']) <= set(chain['facts'][key]['dependencies']),
                        'Required upstream dependency deleted')
        if assignment['stage'] in ('3b', 8) and candidate['events'][-1]['result'] == 'done':
            require(bool(contract['checks']), 'A Lean publication or final verification requires controller-run checks')
            check_cache = attempt / 'checks-complete'
            if not check_cache.exists():
                # Interrupted checks must rerun in fresh output folders.
                for old in attempt.glob('check-*'):
                    if old.is_dir():
                        shutil.rmtree(old)
                checked_contract = dict(contract, checks=contract['checks'] + ([{
                    'name': 'Complete prerequisite chain kernel verification',
                    'argv': ['/usr/bin/python3', '/input/policy/check_chain.py']}]
                    if assignment['stage'] == 8 and candidate.get('implementation_chain') else []))
                run_checks(proposal, checked_contract, attempt, timeout)
                staging = attempt / 'checks-staging'
                shutil.rmtree(staging, ignore_errors=True)
                staging.mkdir()
                shutil.copytree(proposal / 'controller-checks', staging / 'controller-checks')
                shutil.copyfile(proposal / 'controller-checks.json', staging / 'controller-checks.json')
                staging.rename(check_cache)
            else:
                shutil.rmtree(proposal / 'controller-checks', ignore_errors=True)
                shutil.copytree(check_cache / 'controller-checks', proposal / 'controller-checks')
                shutil.copyfile(check_cache / 'controller-checks.json', proposal / 'controller-checks.json')
        binding = digest({'assignment': assignment, 'submission': files(proposal)})
        reviews = []
        review_ids = set()
        retry_errors = []
        with ThreadPoolExecutor(max_workers=2) as pool:
            futures = {}
            review_view = attempt / 'review-input'
            shutil.rmtree(review_view, ignore_errors=True)
            prepare_worker_view(proposal, review_view, contract, assignment)
            for index in (1, 2):
                key = f'reviewer-{index}'
                task = dict(assignment, binding=binding, role=key)
                futures[index] = pool.submit(checkpoint_launch, 'reviewer', review_view,
                                             attempt, key, task, auth, timeout)
            # Validate both results even if one fails; preserve the other checkpoint.
            for index in (1, 2):
                review_assignment = dict(assignment, binding=binding, role=f'reviewer-{index}')
                key = f'reviewer-{index}'
                try:
                    review_id, verdict, _ = futures[index].result()
                    require(review_id != executor_id and review_id not in review_ids, 'Self-review or reused review session')
                    review_ids.add(review_id)
                    require(digest({'assignment': assignment, 'submission': files(proposal)}) == binding,
                            'Submission changed during review')
                    validate_review(verdict, binding, assignment['stage'], proposal)
                    require(set(verdict['reviewed_facts']) <= set(candidate['facts']) - set(state['facts']),
                            'Reviewer certified an unknown or old new-fact ID')
                    require(set(verdict.get('invalid_inherited_facts', [])) <= set(state['facts']), 'Unknown inherited fact')
                    require(set(verdict.get('revalidated_facts', [])) <= set(state.get('quarantined_facts', [])),
                            'Revalidation must address a quarantined fact')
                    require(set(verdict.get('unnecessary_facts', [])) <= set(state.get('quarantined_facts', [])),
                            'Unnecessary-input certification must address a quarantined fact')
                    if verdict['decision'] == 'accept':
                        require(set(verdict['reviewed_facts']) == set(candidate['facts']) - set(state['facts']),
                                'Acceptance must review every new fact or explicitly reject the unsupported fact')
                except (Rejected, KeyError, TypeError, AttributeError, json.JSONDecodeError) as exc:
                    invalidate_review(attempt, key, exc)
                    retry_errors.append({'reviewer': key, 'error': str(exc)})
                    continue
                except (WorkerUnavailable, OSError, ValueError, subprocess.TimeoutExpired) as exc:
                    retry_errors.append({'reviewer': key, 'error': str(exc)})
                    continue
                reviews.append(verdict)
        if retry_errors:
            write(attempt / 'retry.json', {'assignment': assignment, 'errors': retry_errors,
                  'status': 'review_retry_required', 'next': 'retry only affected reviewers'})
            return 'retry_required'
        new_facts = set(candidate['facts']) - set(state['facts'])
        quarantine = set(state.get('quarantined_facts', []))
        revalidated = set(reviews[0].get('revalidated_facts', [])) & set(reviews[1].get('revalidated_facts', []))
        if any(r['decision'] != 'accept' for r in reviews) or any(
                set(r['reviewed_facts']) != new_facts for r in reviews):
            reason = '\n'.join(r['first_failure'] + '\n' + r['repair'] for r in reviews if r['decision'] == 'reject')
            rejection(run, snapshot, assignment, reason or 'Facts not independently established on the retained residual', reviews, proposal)
            return 'repair_queued'
        unnecessary = (set(reviews[0].get('unnecessary_facts', [])) &
                       set(reviews[1].get('unnecessary_facts', [])))
        if unnecessary:
            candidate['unnecessary_facts'] = sorted(set(state.get('unnecessary_facts', [])) | unnecessary)
            # These remain quarantined: proving non-use does not prove the fact.
            write(proposal / 'record/state.json', candidate)
        if revalidated:
            candidate['quarantined_facts'] = sorted(quarantine - revalidated)
            write(proposal / 'record/state.json', candidate)
        if candidate['events'][-1]['result'] == 'failed':
            failed = candidate['events'][-1]
            failed['restart_stage'] = reviewed_restart_stage(
                reviews, assignment, state, accepted_failure=True)
            if assignment['stage'] == 6:
                failed['attempted_technique'] = technique_signature(authorization(state, node)['artifact'])
            reopen_for_repair(candidate, node, failed['restart_stage'])
            require(not record.validate(candidate, proposal / 'record'), 'Accepted failure repair record invalid')
            write(proposal / 'record/state.json', candidate)
        # Verdicts come from separate launched processes, not files supplied by
        # the executor. The exact reviewed bytes are the bytes committed.
        write(attempt / 'accepted-reviews.json', {'binding': binding, 'sessions': sorted(review_ids), 'reviews': reviews})
        commit(run, proposal, {'kind': 'accepted',
                               'accepted_deliverable': candidate['events'][-1]['result'],
                               'proof_progress': ('closure_or_significant_reduction' if assignment['stage'] == 6 and candidate['events'][-1]['result'] == 'done' else 'none'),
                               'cycle_complete': assignment['stage'] == 8 and candidate['events'][-1]['result'] == 'done',
                               'assignment': assignment, 'binding': binding,
                               'controller_revalidated': sorted(revalidated),
                               'controller_unnecessary': sorted(unnecessary),
                               'executor': executor_id, 'reviewers': sorted(review_ids), 'reviews': reviews})
        return 'accepted'
    except ArtifactFormatError as exc:
        cache = attempt / 'executor-checkpoint.json'
        saved = read(cache)
        correction_kind = 'format_correction'
        write(attempt / 'executor-format-repair.json', {'checkpoint': saved, 'errors': str(exc), 'kind': correction_kind})
        cache.rename(attempt / ('executor-format-invalid-' + uuid.uuid4().hex + '.json'))
        write(attempt / 'retry.json', {'assignment': assignment, 'status': correction_kind + '_required',
                                     'error': str(exc), 'next': 'correct saved submission only'})
        return 'retry_required'
    except Rejected as exc:
        rejection(run, snapshot, assignment, str(exc), [], safe_proposal)
        return 'repair_queued'
    except (KeyError, TypeError, AttributeError, json.JSONDecodeError) as exc:
        rejection(run, snapshot, assignment, 'Malformed worker artifact: ' + str(exc), [], safe_proposal)
        return 'repair_queued'
    except (WorkerUnavailable, OSError, ValueError, subprocess.TimeoutExpired) as exc:
        # Crashes and unavailable services preserve the last accepted state;
        # they do not assert a mathematical negative or manufacture an event.
        write(attempt / 'retry.json', {'assignment': assignment, 'error': str(exc),
                                      'status': 'retry_required', 'next': 'same pending step'})
        return 'retry_required'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('init')
    p.add_argument('--run', type=Path, required=True)
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--record', type=Path, required=True)
    p.add_argument('--contract', type=Path, required=True)
    p = sub.add_parser('continue')
    p.add_argument('--run', type=Path, required=True)
    p.add_argument('--from-run', type=Path, required=True)
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--contract', type=Path, required=True)
    sub.add_parser('probe')
    p = sub.add_parser('status')
    p.add_argument('--run', type=Path, required=True)
    p = sub.add_parser('run')
    p.add_argument('--run', type=Path, required=True)
    p.add_argument('--auth', type=Path, default=Path.home() / '.codex/auth.json')
    p.add_argument('--timeout', type=int, default=1800)
    p.add_argument('--rounds', type=int, default=None, help='Optional operator resource limit; never means complete')
    args = parser.parse_args()
    if args.command == 'probe':
        sandbox_probe()
        print('OS isolation verified; controller state is outside worker filesystem.')
        return
    run = args.run.resolve()
    if args.command == 'init':
        initialize(run, args.repo.resolve(), args.record.resolve(), args.contract.resolve())
        print('Initialized from a clean record. Stage 1 requires independent review.')
    elif args.command == 'continue':
        continue_run(run, args.from_run.resolve(), args.repo.resolve(), args.contract.resolve())
        state = read(committed(run) / 'record/state.json')
        print(f'Accepted stages preserved. Next stage: {next_stage(state, next_node(state))}.')
    elif args.command == 'status':
        snapshot = committed(run)
        check_contract(run, snapshot)
        state = read(snapshot / 'record/state.json')
        node = next_node(state)
        print(json.dumps({'status': state['status'], 'node': node,
                          'next_stage': next_stage(state, node) if node else None,
                          'open_leaves': state['queue'],
                          'last_accepted_attempt_result': state['events'][-1]['result'] if state['events'] else None,
                          'last_advancement': next((e['artifact']['outcomes'] for e in reversed(state['events']) if e['stage'] == 6 and e['result'] == 'done'), None),
                          'active_stages': [stage for stage in STAGE_ORDER
                                            if stage in active_artifacts(state, node)] if node else [],
                          'record': str(snapshot / 'record')}, indent=2))
    else:
        require(args.timeout > 0 and (args.rounds is None or args.rounds > 0), 'Invalid resource limit')
        sandbox_probe()
        with locked(run):
            rounds = 0
            while args.rounds is None or rounds < args.rounds:
                outcome = tick(run, args.auth.resolve(), args.timeout)
                print(outcome, flush=True)
                rounds += 1
                if outcome == 'complete':
                    break
                if outcome == 'retry_required':
                    time.sleep(5)
            else:
                print('Operator round limit reached; pending work preserved, not completed.')


if __name__ == '__main__':
    main()

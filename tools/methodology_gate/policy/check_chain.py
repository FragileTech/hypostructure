"""Controller-run kernel checks for every required fact in the reviewed chain.

Kernel success is separate from reviewers' statement/ledger fidelity checks.
No shell commands or check commands are supplied by the worker.
"""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

root = Path('/output/workspace')
state = json.loads(Path('/input/record/state.json').read_text())
contract = json.loads(Path('/input/contract.json').read_text())
chain = state['implementation_chain']
projects = contract.get('lean_projects', [])
assert projects, 'No operator-configured Lean projects: cannot certify prerequisite chain'
assignment_file = Path('/input/assignment.json')
if assignment_file.exists():
    assignment = json.loads(assignment_file.read_text())
    if assignment['node'] != state['root']:
        node = next(n for n in state['nodes'] if n['id'] == assignment['node'])
        target = node['implementation_target']
        selected = set()
        def visit(key):
            if key in selected:
                return
            selected.add(key)
            for dep in chain['facts'][key]['dependencies']:
                visit(dep)
        visit(target)
        chain = {'target': target, 'facts': {k: chain['facts'][k] for k in selected}}
required = [f for f in chain['facts'].values() if f['status'] != 'unnecessary']
assert required and all(f['status'] == 'kernel_checked' for f in required)
groups = {}
for fact in required:
    owners = [p for p in projects if Path(fact['path']).is_relative_to(p['root'])]
    assert len(owners) == 1, 'Required owner lacks an unambiguous configured Lean project'
    project = owners[0]
    groups.setdefault(project['root'], []).append(fact)
results = []
for spec in projects:
    if spec['root'] not in groups:
        continue
    project = root / spec['root']
    assert project.is_dir() and (project / 'lakefile.toml').is_file()
    lake = project / '.lake'
    lake.mkdir(exist_ok=True)
    packages = lake / 'packages'
    if not packages.exists():
        packages.mkdir()
        for package in Path('/runtime/packages').iterdir():
            (packages / package.name).symlink_to(package, target_is_directory=package.is_dir())
        if spec.get('framework_dependency'):
            (packages / 'hypostructure').symlink_to(root / spec['framework_dependency'], target_is_directory=True)
    if spec.get('cache') and not (lake / 'build').exists():
        subprocess.run(['cp', '-a', '--reflink=auto', spec['cache'], str(lake / 'build')], check=True)
    facts = groups[spec['root']]
    targets = sorted({t for f in facts for t in f['kernel_targets']})
    assert all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', t) for t in targets)
    subprocess.run(['/runtime/lean/bin/lake', 'build', *targets], cwd=project, check=True)
    probe = Path('/output') / ('chain-probe-' + str(len(results)) + '.lean')
    declarations = sorted({f['declaration'] for f in facts})
    probe.write_text('\n'.join(['import ' + t for t in targets] +
                              ['#check ' + d + '\n#print axioms ' + d for d in declarations]) + '\n')
    proc = subprocess.run(['/runtime/lean/bin/lake', 'env', 'lean', str(probe)], cwd=project,
                          capture_output=True, text=True)
    print(proc.stdout, flush=True)
    print(proc.stderr, flush=True)
    assert proc.returncode == 0, 'Required declaration failed kernel probe'
    assert 'sorryAx' not in proc.stdout + proc.stderr, 'Admitted proof in required chain'
    axiom_lists = re.findall(r'depends on axioms:\s*\[(.*?)\]', proc.stdout, re.S)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for axioms in axiom_lists:
        assert {x.strip() for x in axioms.split(',') if x.strip()} <= allowed, 'Unapproved axiom in required chain'
    results.append({'project': spec['root'], 'targets': targets, 'declarations': declarations,
                    'kernel_exit_code': proc.returncode, 'axiom_check': 'passed'})
assert sum(len(g) for g in groups.values()) == len(required)
Path('/output/chain-kernel-results.json').write_text(json.dumps(results, indent=2))
print('ALL REQUIRED CHAIN DECLARATIONS KERNEL-CHECKED; statement and ledger fidelity still require review.')

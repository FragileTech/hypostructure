"""Operator-locked integration checks, run in the controller's isolated workspace.

The controller separately checks every required implementation-chain declaration.
Both independent reviewers must certify closure of the entire visible history.
"""
from pathlib import Path
import os
import subprocess

workspace = Path('/output/workspace')
env = dict(os.environ, PATH='/runtime/lean/bin:/usr/bin:/bin')


def run(argv, cwd=workspace):
    subprocess.run(argv, cwd=cwd, env=env, check=True)


def cache(project, source):
    lake = project / '.lake'
    lake.mkdir(exist_ok=True)
    if not (lake / 'packages').exists():
        (lake / 'packages').symlink_to('/runtime/packages', target_is_directory=True)
    if not (lake / 'build').exists():
        run(['cp', '-a', '--reflink=auto', source, str(lake / 'build')])


framework = workspace / 'hypostructure'
eg = workspace / 'proofs/hypostructure_erdos_64_eg'
cache(framework, '/runtime/build-cache')
cache(eg, '/runtime/eg-build-cache')
run(['/runtime/lean/bin/lake', 'build',
     'Hypostructure.Graph.Strategy.SpineRows.Route8JointBalance'], framework)
run(['/runtime/lean/bin/lake', 'build',
     'HypostructureErdos64EG.Assembly.RouteEight.Residual',
     'HypostructureErdos64EG.Assembly.RouteEight.TypeBContinuation',
     'HypostructureErdos64EG.Assembly.TypeA.ExitFourDischargedRetest'], eg)
run(['/runtime/lean/bin/lake', 'build'], eg)
for script in ('api_catalog.py', 'audit_tables.py'):
    run(['/usr/bin/python3', str(workspace / '.agents/skills/eg-proof-expansion/scripts' / script),
         'check', '--repo-root', str(workspace)])
run(['/usr/bin/python3', '/input/policy/scripts/check_execution.py',
     'check', '/input/record', '--repo', str(workspace)])

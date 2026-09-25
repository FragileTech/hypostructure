"""Operator-locked verification for node 172a; run only in isolated scratch."""
from pathlib import Path
import os
import subprocess
w = Path('/output/workspace')
p = w / 'hypostructure'
env = dict(os.environ, PATH='/runtime/lean/bin:/usr/bin:/bin')
def run(argv, cwd=w):
    subprocess.run(argv, cwd=cwd, env=env, check=True)
def cache(project, source):
    lake = project / '.lake'
    lake.mkdir(exist_ok=True)
    (lake / 'packages').symlink_to('/runtime/packages', target_is_directory=True)
    run(['cp', '-a', '--reflink=auto', source, str(lake / 'build')])
cache(p, '/runtime/build-cache')
run(['/runtime/lean/bin/lake', 'build',
    'Hypostructure.Core.Residual.ExactLedger',
    'Hypostructure.Core.Strategy.FactManifest',
    'Hypostructure.Core.Strategy.ExactExecution',
    *['Hypostructure.Fixtures.' + x for x in (
        'ExactLedger', 'ExactExecution', 'AutomaticLedgerClosure',
        'BranchScopedExactLedger', 'DerivedFactPublication',
        'ExactExecutionDroppedFact', 'ExactExecutionMissingRequirement',
        'ExactLedgerDuplicateFact', 'ExactLedgerEmptinessClosure',
        'ExactLedgerMissingFact', 'ExactLedgerOpacity', 'LedgerAutorouting')]], p)
targets = ['Hypostructure.Graph.Strategy.SpineVocabulary',
           'Hypostructure.Graph.Strategy.BlockedCompressionRows']
if (p / 'Hypostructure/Graph/Strategy/BlockedOverlapRows.lean').exists():
    targets.append('Hypostructure.Graph.Strategy.BlockedOverlapRows')
run(['/runtime/lean/bin/lake', 'build', *targets], p)
eg = w / 'proofs/hypostructure_erdos_64_eg'
cache(eg, '/runtime/eg-build-cache')
run(['/runtime/lean/bin/lake', 'build', 'HypostructureErdos64EG.Assembly',
     'HypostructureErdos64EG.Official.StructuralProgram'], eg)
# Other open endpoints 182 and 186 preclude requiring whole-root closure here.
# Record the strict probe independently; reviewers must distinguish its failure.
probe = eg / 'HypostructureErdos64EG/Official/ClosureProbe.lean'
if probe.exists():
    result = subprocess.run(['/runtime/lean/bin/lake', 'env', 'lean', str(probe)], cwd=eg, env=env, capture_output=True, text=True)
    (w / 'node172a-closure-probe.log').write_text(result.stdout + result.stderr)
    print('Whole-root strict closure probe exit:', result.returncode, flush=True)
for script in ('api_catalog.py', 'audit_tables.py'):
    run(['/usr/bin/python3', str(w / '.agents/skills/eg-proof-expansion/scripts' / script), 'check', '--repo-root', str(w)])
run(['/usr/bin/python3', '/input/policy/scripts/check_execution.py', 'check', '/input/record', '--repo', str(w)])

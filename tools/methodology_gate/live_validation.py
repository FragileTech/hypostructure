#!/usr/bin/env python3
"""One real isolated Stage 1 gate on a public synthetic integer fixture.

This never imports a user proof or certifies a mathematical branch. Two freshly
launched reviewers must accept the actual executor artifact before it advances.
"""
import argparse
import json
from pathlib import Path
import shutil
import sys
import tempfile
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.methodology_gate import runner, core
from tools.methodology_gate.tests.structural_fixtures import state


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--result', type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    with tempfile.TemporaryDirectory(prefix='structural-workflow-fixture-') as tmp:
        tmp = Path(tmp)
        source = tmp / 'record'; source.mkdir()
        runner.write(source / 'state.json', state(source))
        (source / 'execution.md').write_text('Synthetic fixture. No previous nodes beyond the stated upper bound.\n')
        contract = tmp / 'contract.json'
        source_paths=list(core.record.SOURCES)
        scopes={str(stage):source_paths for stage in range(1,9)}
        scopes['1']=source_paths[:1]
        runner.write(contract, dict(name='Synthetic prior-use ledger behavior smoke',
            input_paths=source_paths, stage_input_paths=scopes, allowed_changes=[],
            checks=[dict(name='Synthetic fixture check', argv=['/usr/bin/true'])]))
        if not args.run.exists():
            runner.initialize(args.run, repo, source, contract)
    runner.sandbox_probe()
    with runner.locked(args.run):
        outcome = runner.tick(args.run, Path.home()/'.codex/auth.json', 900)
    snapshot = runner.committed(args.run)
    head = runner.read(args.run/'HEAD.json')
    receipt = runner.read(args.run/'commits'/(head['snapshot']+'.json'))
    current = runner.read(snapshot/'record/state.json')
    result = dict(scope='One isolated executor and two independent reviewers, synthetic Stage 1 only',
                  outcome=outcome, run=str(args.run), next_stage=core.next_stage(current,current['root']),
                  receipt=receipt['event'])
    args.result.parent.mkdir(parents=True,exist_ok=True)
    runner.write(args.result,result)
    print(json.dumps({k:v for k,v in result.items() if k!='receipt'},indent=2))
    if outcome != 'accepted': raise SystemExit(1)

if __name__ == '__main__': main()

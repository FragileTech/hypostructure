from pathlib import Path
import ast,copy,hashlib,importlib.util,json
before=json.loads(Path('/input/record/state.json').read_text())
record=Path('/output/record');after=json.loads((record/'state.json').read_text())
a=json.loads(Path('/input/assignment.json').read_text())
# Execute the unchanged validator function bodies without the top-level register
# load. Stage 3b never reads that register or revalidates earlier artifacts.
spec=json.loads(Path('/input/policy/workflow.json').read_text())
ctx={'json':json,'hashlib':hashlib,'STAGES':{s['number']:s for s in spec['stages']},'STAGE_ORDER':tuple(s['number'] for s in spec['stages']),'MECHANISMS':('constraint','compression','quantity')}
tree=ast.parse(Path('/input/policy/workflow.py').read_text())
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef))],type_ignores=[]),'/input/policy/workflow.py','exec'),ctx)
errs=ctx['validate_artifact'](before,after,a['node'],a['stage'])
assert not errs,errs
print('Stage 3b workflow artifact validation: PASS (structural register not loaded).')
ms=importlib.util.spec_from_file_location('record_check','/input/policy/scripts/check_execution.py')
m=importlib.util.module_from_spec(ms);ms.loader.exec_module(m)
errs=m.validate(after,record)
assert not errs,errs
print('Record structure and all evidence hashes: PASS.')
assert after['events'][:-1]==before['events'] and len(after['events'])==len(before['events'])+1
assert after['events'][-1]['inputs']==a['accepted_inputs']
assert after['status']==before['status']=='active'
for k,v in before['facts'].items(): assert after['facts'][k]==v
for k,v in before['evidence'].items(): assert after['evidence'][k]==v
assert set(after['facts'])-set(before['facts'])=={'f129_originalCyclePassage'}
for old,new in zip(before['nodes'],after['nodes']):
 for k in old:
  if k=='facts': assert new[k]==old[k]+['f129_originalCyclePassage']
  else: assert new[k]==old[k]
for k in before:
 if k not in ['events','facts','evidence','nodes']: assert after[k]==before[k]
assert (record/'execution.md').read_bytes().startswith(Path('/input/record/execution.md').read_bytes())
artifact=json.loads((record/'evidence/stage3b-artifact.json').read_text())
assert artifact==after['events'][-1]['artifact']
assert artifact['bound_witness']==a['stage3b_focus']['selected_structure']['bound_witness']
assert artifact['residual_binding']==ctx['residual_binding'](before,a['node'])==a['residual_binding']
print('Exact accepted prefix, residual, endpoint, queue and evidence preserved: PASS.')
print('Exactly one event and one new derived fact; exact accepted inputs and bound witness: PASS.')
root=Path('/output/changes');contract=json.loads(Path('/input/contract.json').read_text())
actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
assert actual<=set(contract['allowed_changes']) and len(actual)==6
logs=(record/'evidence/stage3b-kernel.log').read_text()
for p in root.rglob('*.lean'): assert hashlib.sha256(p.read_bytes()).hexdigest() in logs
assert logs.count('EXIT 0')==6 and 'ALL SIX CHANGED MODULES' in logs
assert 'EXIT 0' in (record/'evidence/stage3b-certificate.log').read_text()
assert 'sorryAx' not in (record/'evidence/stage3b-certificate.log').read_text()
print('Six authorized source snapshots match the successful locked compilation log: PASS.')
print('These are representation and kernel checks, not independent mathematical acceptance.')

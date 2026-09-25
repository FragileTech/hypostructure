"""Single dependency schema shared by controller and worker preflight."""
import sys
sys.dont_write_bytecode = True
from .policy.chain_schema import validate_chain


def implementation_work(chain):
    """Pending certification is not evidence that a theorem needs reproving.

    Classifications are reviewed evidence, never a shortcut to checked status.
    Unclassified legacy records get batched reconciliation, not proof tasks.
    """
    queues = {k: [] for k in ('repair', 'reconcile', 'adapters', 'reuse')}
    seen = set()
    def visit(key):
        if key in seen or key not in chain.get('facts', {}):
            return
        seen.add(key)
        fact = chain['facts'][key]
        for dep in fact['dependencies']:
            visit(dep)
        if fact['status'] == 'unnecessary':
            return
        item = {'fact': key, **fact}
        if fact['status'] == 'kernel_checked':
            queues['reuse'].append(item)
        elif fact.get('work_kind') == 'proof_repair':
            queues['repair'].append(item)
        elif fact.get('work_kind') == 'adapter':
            queues['adapters'].append(item)
        else:
            queues['reconcile'].append(item)
    visit(chain.get('target'))
    return queues

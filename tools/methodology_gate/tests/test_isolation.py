"""Real OS boundary checks; explicitly enabled on a host permitting namespaces."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from tools.methodology_gate.runner import sandbox_command, run_checks
from tools.methodology_gate.core import Rejected
from tools.methodology_gate.egress import broker


@unittest.skipUnless(os.environ.get('METHODOLOGY_ISOLATION_TESTS') == '1', 'Requires host namespace permission')
class IsolationTests(unittest.TestCase):
    def test_complete_chain_kernel_probe_rejects_sorry(self):
        import json
        toolchain = Path('/home/guillem/.elan/toolchains/leanprover--lean4---v4.31.0')
        if not toolchain.exists():
            self.skipTest('Configured Lean runtime absent')
        for body, accepted in [('by trivial', True), ('by sorry', False)]:
            with self.subTest(body=body), tempfile.TemporaryDirectory() as tmp:
                base = Path(tmp); proposal = base / 'proposal'; proposal.mkdir()
                (proposal / 'record').mkdir(); (proposal / 'policy').mkdir()
                source = proposal / 'sources/project'; source.mkdir(parents=True)
                (source / 'lakefile.toml').write_text('name = "probe"\n[[lean_lib]]\nname = "Fixture"\n')
                (source / 'Fixture.lean').write_text('theorem Fixture.done : True := ' + body + '\n')
                state = {'implementation_chain': {'target': 'f', 'facts': {'f': {
                    'status': 'kernel_checked', 'path': 'project/Fixture.lean',
                    'declaration': 'Fixture.done', 'kernel_targets': ['Fixture']}}}}
                (proposal / 'record/state.json').write_text(json.dumps(state))
                (proposal / 'contract.json').write_text(json.dumps({'lean_projects': [{'root': 'project'}]}))
                script = Path(__file__).resolve().parents[1] / 'policy/check_chain.py'
                (proposal / 'policy/check_chain.py').write_text(script.read_text())
                packages = base / 'packages'; packages.mkdir()
                contract = {'checks': [{'name': 'chain', 'argv': ['/usr/bin/python3', '/input/policy/check_chain.py']}],
                    'runtime_paths': [{'source': str(toolchain), 'target': '/runtime/lean'},
                                      {'source': str(packages), 'target': '/runtime/packages'}]}
                attempt = base / 'attempt'; attempt.mkdir()
                if accepted:
                    run_checks(proposal, contract, attempt, 60)
                else:
                    with self.assertRaises(Rejected):
                        run_checks(proposal, contract, attempt, 60)

    def test_verification_runs_against_submitted_changes(self):
        with tempfile.TemporaryDirectory(prefix='mg-check-') as tmp:
            base = Path(tmp); proposal = base / 'proposal'; proposal.mkdir()
            (proposal / 'sources').mkdir(); (proposal / 'changes').mkdir()
            (proposal / 'sources/value').write_text('original')
            (proposal / 'changes/value').write_text('submitted')
            attempt = base / 'attempt'; attempt.mkdir()
            contract = {'checks': [{'name': 'actual subprocess', 'argv': ['/usr/bin/python3', '-c',
                "from pathlib import Path; assert Path('/output/workspace/value').read_text()=='submitted'"]}]}
            run_checks(proposal, contract, attempt, 20)
            self.assertEqual((proposal / 'sources/value').read_text(), 'original')
            self.assertTrue((proposal / 'controller-checks.json').is_file())

    def test_verification_failure_is_not_accepted(self):
        with tempfile.TemporaryDirectory(prefix='mg-check-') as tmp:
            base = Path(tmp); proposal = base / 'proposal'; proposal.mkdir()
            (proposal / 'sources').mkdir()
            attempt = base / 'attempt'; attempt.mkdir()
            contract = {'checks': [{'name': 'actual failure', 'argv': ['/usr/bin/python3', '-c', 'raise SystemExit(3)']}]}
            with self.assertRaises(Rejected):
                run_checks(proposal, contract, attempt, 20)

    def test_worker_cannot_reach_controller_or_modify_review_input(self):
        with tempfile.TemporaryDirectory(prefix='mg-isolate-') as tmp:
            base = Path(tmp)
            protected = base / 'controller-state'
            protected.write_text('unmodified')
            source = base / 'input'
            source.mkdir()
            (source / 'policy').write_text('locked')
            output = base / 'output'
            output.mkdir()
            code = f'''
from pathlib import Path
import socket
assert not Path({str(protected)!r}).exists()
assert not Path('/proc/1/root' + {str(protected)!r}).exists()
assert not Path('/home/guillem/.codex/auth.json').exists()
try:
    Path('/input/policy').write_text('bypassed')
except OSError:
    pass
else:
    raise AssertionError('worker could rewrite reviewer input')
s=socket.socket(); s.settimeout(1)
try:
    s.connect(('1.1.1.1',443))
except OSError:
    pass
else:
    raise AssertionError('worker has direct external network')
Path('/output/result').write_text('passed')
'''
            cmd = sandbox_command([(source, '/input', False), (output, '/output', True)],
                                  ['/usr/bin/python3', '-c', code])
            subprocess.run(cmd, check=True, timeout=20)
            self.assertEqual((output / 'result').read_text(), 'passed')
            self.assertEqual(protected.read_text(), 'unmodified')
            self.assertEqual((source / 'policy').read_text(), 'locked')

    def test_broker_rejects_host_services_from_actual_worker(self):
        with tempfile.TemporaryDirectory(prefix='mg-proxy-') as tmp:
            base = Path(tmp)
            output = base / 'output'; output.mkdir()
            with broker(base / 'api.sock') as proxy:
                code = '''
import socket
for target in ['127.0.0.1:443', 'localhost:443', '192.168.1.1:443', 'chatgpt.com:80', 'example.com:443']:
    with socket.socket(socket.AF_UNIX) as s:
        s.connect('/run/api-proxy.sock')
        s.sendall(('CONNECT '+target+' HTTP/1.1\\r\\n\\r\\n').encode())
        assert s.recv(4096).startswith(b'HTTP/1.1 403'), target
'''
                cmd = sandbox_command([(output, '/output', True), (proxy, '/run/api-proxy.sock', False)],
                                      ['/usr/bin/python3', '-c', code])
                subprocess.run(cmd, check=True, timeout=20)


if __name__ == '__main__':
    unittest.main()

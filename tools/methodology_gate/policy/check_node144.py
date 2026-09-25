"""Locked verification commands for the Node 144 owner, run in isolated scratch."""
from pathlib import Path
import os
import subprocess

workspace = Path('/output/workspace')
project = workspace / 'hypostructure'
lake = project / '.lake'
lake.mkdir(exist_ok=True)
(lake / 'packages').symlink_to('/runtime/packages', target_is_directory=True)
# Copy-on-write when supported; never hardlink writable outputs into live caches.
subprocess.run(['cp', '-a', '--reflink=auto', '/runtime/build-cache', str(lake / 'build')], check=True)
subprocess.run(['/runtime/lean/bin/lake', 'build',
                'Hypostructure.Graph.Strategy.HomogeneousBottleneckRows'], cwd=project, check=True)
subprocess.run(['/usr/bin/python3', '/input/policy/scripts/check_execution.py', 'check',
                '/input/record', '--repo', str(workspace)], check=True)
subprocess.run(['/usr/bin/python3',
                str(workspace / '.agents/skills/eg-proof-expansion/scripts/audit_tables.py'),
                'check', '--repo-root', str(workspace)], check=True)

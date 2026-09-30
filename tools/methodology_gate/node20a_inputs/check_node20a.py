"""Locked check for the [20a] run: build only the direct consumer of the residual.

Runs inside the controller's bubblewrap check sandbox.  `/output/workspace` is the
frozen source snapshot with the submitted replacement files applied.  The warm
build caches come read-only from `/runtime` (the analysis worktree at the pinned
revision) and are copied into the private workspace, so Lake rebuilds exactly the
modules whose sources or dependencies changed.  The single target is
`HypostructureErdos64EG.Assembly.Final`, which imports the residual module and
contains the direct consumer `node20aReturn`; everything it does not import is
not built.  The whole check runs under the operator's `flock` on the lane lock.
"""
from pathlib import Path
import os
import subprocess
import sys

WORKSPACE = Path('/output/workspace')
LAKE = '/runtime/lean/bin/lake'


def prepare(project, build_cache, package_cache):
    lake = project / '.lake'
    lake.mkdir(exist_ok=True)
    (lake / 'packages').symlink_to(package_cache, target_is_directory=True)
    subprocess.run(['cp', '-a', '--reflink=auto', str(build_cache), str(lake / 'build')],
                   check=True)


def main():
    hypo = WORKSPACE / 'hypostructure'
    proof = WORKSPACE / 'proofs/hypostructure_erdos_64_eg'
    prepare(hypo, Path('/runtime/hypostructure-build'), Path('/runtime/hypostructure-packages'))
    prepare(proof, Path('/runtime/erdos-build'), Path('/runtime/erdos-packages'))
    env = dict(os.environ, LAKE_NO_CACHE='1')
    result = subprocess.run([LAKE, 'build', 'HypostructureErdos64EG.Assembly.Final'],
                            cwd=proof, env=env)
    # The copied caches are large; drop them so the attempt keeps only logs.
    for project in (hypo, proof):
        subprocess.run(['rm', '-rf', str(project / '.lake')], check=False)
    sys.exit(result.returncode)


if __name__ == '__main__':
    main()

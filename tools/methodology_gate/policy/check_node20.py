"""Build Node 20's changed owner and its direct assembly consumer in isolation."""
from pathlib import Path
import subprocess

WORKSPACE = Path('/output/workspace')


def prepare(project, build_cache, package_cache):
    lake = project / '.lake'
    lake.mkdir(exist_ok=True)
    packages = lake / 'packages'
    packages.symlink_to(package_cache, target_is_directory=True)
    subprocess.run(['cp', '-a', '--reflink=auto', str(build_cache), str(lake / 'build')], check=True)


hypo = WORKSPACE / 'hypostructure'
proof = WORKSPACE / 'proofs/hypostructure_erdos_64_eg'
prepare(hypo, Path('/runtime/hypostructure-build'), Path('/runtime/hypostructure-packages'))
prepare(proof, Path('/runtime/erdos-build'), Path('/runtime/erdos-packages'))
subprocess.run(['/runtime/lean/bin/lake', 'build', 'HypostructureErdos64EG.Assembly'],
               cwd=proof, check=True)

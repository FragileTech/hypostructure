from pathlib import Path
import hashlib, os, subprocess, sys, time
root=Path('/output/changes')
mods=[
 ('hypostructure','Hypostructure/Graph/Node20aStructure'),
 ('hypostructure','Hypostructure/Graph/Statements/Node20aStructure'),
 ('hypostructure','Hypostructure/Graph/Strategy/SpineVocabulary'),
 ('hypostructure','Hypostructure/Graph/Strategy/SpineRows/Node20aStructure'),
 ('proofs/hypostructure_erdos_64_eg','HypostructureErdos64EG/Assembly/Residuals'),
 ('proofs/hypostructure_erdos_64_eg','HypostructureErdos64EG/Assembly/Final'),
]
print('Stage 3b local locked kernel check; pinned accepted prerequisite caches.',flush=True)
print('The contract runner /input/sources/tools/methodology_gate/node20a_inputs/check_node20a.py is absent; its prescribed invocation returned exit 2. This check invokes the mounted Lean toolchain directly on the changed modules and direct consumer.',flush=True)
for pkg,mod in mods:
 src=root/pkg/(mod+'.lean'); out=Path('/output/build')/(mod+'.olean')
 if out.is_symlink(): out.unlink()
 out.parent.mkdir(parents=True,exist_ok=True)
 print('\nSOURCE',src.relative_to(root),'SHA256',hashlib.sha256(src.read_bytes()).hexdigest(),flush=True)
 cmd=['bash','/output/check_lean.sh','-o',str(out),str(src)]
 print('COMMAND',cmd,flush=True)
 t=time.monotonic(); p=subprocess.run(cmd)
 print('EXIT',p.returncode,'SECONDS',round(time.monotonic()-t,2),flush=True)
 if p.returncode: sys.exit(p.returncode)
print('\nALL SIX CHANGED MODULES AND THE DIRECT CONSUMER ELABORATED.',flush=True)

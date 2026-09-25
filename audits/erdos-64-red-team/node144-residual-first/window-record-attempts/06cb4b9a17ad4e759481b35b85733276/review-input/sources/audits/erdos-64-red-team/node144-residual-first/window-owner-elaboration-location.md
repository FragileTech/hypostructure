# Source-bound owner: first bounded elaboration diagnostic

Status: **SUBMITTED_RESULT**. Implementation status: **none**.

The requested diagnostic is complete. The first emitted Lean error is at saved-candidate **689:18**, inside `sameTokenBottleneckRoutingRow`, in the local lemma `armEdgeSet_first_incidence`, at the proof of `firstOrLater`:

```lean
                  simpa [armEdgeSet, List.zip_cons_cons,
                    Finset.image_insert] using incident
```

Lean reports `Tactic simp failed with a nested error`, specifically a deterministic timeout at `whnf` after **20,000 heartbeats**. This is the first reported obstruction in the reduced-budget run, not proof that the original 4,000,000-heartbeat candidate fails at this location. It does not identify a missing mathematical premise. No mathematical inference is asserted missing; there are no immediate mathematical subobligations for this completed diagnostic task.

The run exited **1** after **84.49437089500134 seconds**, before its 90-second wall limit. It was not killed by a wall-clock timeout. Two subsequent diagnostics at 692:16 and 610:60 also report heartbeat exhaustion; they are retained below without treating them as independent missing inferences. No further compilation was performed.

## Exact correspondence and goal context

Candidate path: `audits/erdos-64-red-team/node144-residual-first/window-record-attempts/eb2e67d5b2a44c81821a4470261c058d/executor/artifact/hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean`.

Candidate SHA256: `bea3d412d7cc0db2232180b50999d3d75eddcb477053e0ab4c6dc75a5833753b`.

The disposable file keeps candidate lines 1–17 and 592–4169, including precisely the changed owner and consumer. Lines 18–591 are blanked, except that line 18 sets the global heartbeat budget to 20,000. The candidate's sole source-local high limit, line 592, is replaced from `set_option maxHeartbeats 4000000 in` to `set_option maxHeartbeats 20000 in`. A namespace terminator is appended. No retained proof or declaration is otherwise edited or renamed. Thus Lean's line and column positions correspond directly to the saved candidate. The command also passes `-DmaxHeartbeats=20000`; the actual source-local replacement ensures that the original limit cannot override it.

The target written in the candidate at the failing step is:

```lean
s(start, other) = s(start, next) ∨
  s(start, other) ∈ armEdgeSet (next :: rest)
```

This target is transcribed from the source, not a separately emitted Lean goal dump. `armEdgeSet path` is `((path.zip path.tail).toFinset).image (fun pair => s(pair.1, pair.2))`. The step is in the `path = start :: next :: rest` case with `incident : s(start, other) ∈ armEdgeSet (start :: next :: rest)`, `nodup`, `startNotTail`, and `startNeNext` in the local context. The exact emitted diagnostic alone suffices to locate the obstruction; persistent tactic markers were unnecessary because the bounded run returned it.

Source excerpt (original numbering):

```text
667:           have armEdgeSet_first_incidence :
668:               ∀ (path : List object.Vertex) (start other : object.Vertex),
669:                 path.head? = some start → path.Nodup →
670:                   s(start, other) ∈ armEdgeSet path →
671:                     ∃ next rest, path = start :: next :: rest ∧ other = next := by
672:             intro path start other issued nodup incident
673:             cases path with
674:             | nil => simp at issued
675:             | cons head tail =>
676:               have headEq : head = start := by simpa using issued
677:               subst head
678:               cases tail with
679:               | nil => simp [armEdgeSet] at incident
680:               | cons next rest =>
681:                 have startNotTail : start ∉ next :: rest :=
682:                   (List.nodup_cons.mp nodup).1
683:                 have startNeNext : start ≠ next := by
684:                   intro equal
685:                   exact startNotTail (equal ▸ List.mem_cons_self)
686:                 have firstOrLater :
687:                     s(start, other) = s(start, next) ∨
688:                       s(start, other) ∈ armEdgeSet (next :: rest) := by
689:                   simpa [armEdgeSet, List.zip_cons_cons,
690:                     Finset.image_insert] using incident
691:                 rcases firstOrLater with first | later
692:                 · rcases (Sym2.mk_eq_mk_iff
693:                     (p := (start, other)) (q := (start, next))).mp first with
694:                     same | swapped
695:                   · exact ⟨next, rest, rfl, (Prod.mk.inj same).2⟩
696:                   · exact False.elim (startNeNext (Prod.mk.inj swapped).1)
697:                 · exact False.elim
698:                     (startNotTail (armEdgeSet_endpoint_mem (next :: rest)
699:                       (s(start, other)) later start
700:                         (Sym2.mem_mk_left start other)))
```

## Package and bounded invocation

The already-compiled current-vocabulary package is first on `LEAN_PATH`. Its manifest reports successful compilation and unchanged source SHA256 `46b2cfd88ca9bd71826111c46b392e9a60d86d14fee505fe64a4714546439052`. The imported vocabulary `.olean` SHA256 is `b5ef4f67ccc34ab1be9bfe6bd033cd402bbae59288d21aee99333e891ba80a8b`, matching the accepted integration record. Imports and the package were not rebuilt or separately rechecked. The compiler is the supplied `/runtime/lean/bin/lean` from the Lean 4.31.0 runtime. All 18 declared source hashes matched before the run and again before writing this result.

Disposable source SHA256: `70f31d7352617b92b7ad86440705760b42c4c91cd85c1eaa06339c44331ef18e`.

The exact Python 3 extraction and bounded invocation below reproduces the run in the supplied environment. Save it under `/tmp` and execute with `python3`. All temporary files are under `/tmp`; no `.olean` output was requested.

```python
from pathlib import Path
import hashlib,json,os,subprocess,time
root=Path('/input/sources'); assignment=json.loads(Path('/input/assignment.json').read_text())
checks={p:hashlib.sha256((root/p).read_bytes()).hexdigest()==h for p,h in assignment['source_manifest'].items()}
assert all(checks.values()),checks
candidate=next(root.glob('audits/**/eb2e67d5b2a44c81821a4470261c058d/executor/artifact/hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean'))
lines=candidate.read_text().splitlines()
# Keep the imports/namespace/variables and exactly the changed owner and consumer.
for i in range(17,591): lines[i]=''
lines[17]='set_option maxHeartbeats 20000'
assert lines[591]=='set_option maxHeartbeats 4000000 in'
lines[591]='set_option maxHeartbeats 20000 in'
source='\n'.join(lines[:4169])+ '\nend Hypostructure.Graph.Strategy.Spine\n'
p=Path('/tmp/window104-narrow.lean');p.write_text(source)
paths=['/runtime/current-vocabulary','/runtime/build-cache/lib/lean','/runtime/eg-build-cache/lib/lean']+sorted(str(x) for x in Path('/runtime/packages').glob('*/.lake/build/lib/lean'))
env=os.environ.copy();env['LEAN_PATH']=':'.join(paths)
meta={'candidate':str(candidate.relative_to(root)),'candidate_sha256':hashlib.sha256(candidate.read_bytes()).hexdigest(),'manifest_checks':checks,'lean_path':env['LEAN_PATH'],'command':['/runtime/lean/bin/lean','-DmaxHeartbeats=20000',str(p)],'narrow_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'compiled_vocabulary_sha256':hashlib.sha256(Path('/runtime/current-vocabulary/Hypostructure/Graph/Strategy/SpineVocabulary.olean').read_bytes()).hexdigest(),'wall_limit_seconds':90}
Path('/tmp/window104-progress').write_text('started\n'); start=time.monotonic()
with open('/tmp/window104-stdout','w') as out,open('/tmp/window104-stderr','w') as err:
 try:
  run=subprocess.run(meta['command'],env=env,stdout=out,stderr=err,timeout=90)
  meta['exit_code']=run.returncode
 except subprocess.TimeoutExpired:
  meta['timeout']=True
meta['elapsed_seconds']=time.monotonic()-start
Path('/tmp/window104-run.json').write_text(json.dumps(meta,indent=2))
Path('/tmp/window104-progress').write_text('finished\n')
print(json.dumps(meta,indent=2));print(Path('/tmp/window104-stdout').read_text());print(Path('/tmp/window104-stderr').read_text())

```

Exact run metadata:

```json
{
  "candidate": "audits/erdos-64-red-team/node144-residual-first/window-record-attempts/eb2e67d5b2a44c81821a4470261c058d/executor/artifact/hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean",
  "candidate_sha256": "bea3d412d7cc0db2232180b50999d3d75eddcb477053e0ab4c6dc75a5833753b",
  "manifest_checks": {
    "audits/erdos-64-red-team/node144-residual-first/phase0-evidence.md": true,
    "audits/erdos-64-red-team/node144-residual-first/window-kernel-label-identity-integration.md": true,
    "audits/erdos-64-red-team/node144-residual-first/window-kernel-pointwise-profile.md": true,
    "audits/erdos-64-red-team/node144-residual-first/window-phase6-source-bound-schema.md": true,
    "audits/erdos-64-red-team/node144-residual-first/window-phase7-schema-integration.md": true,
    "audits/erdos-64-red-team/node144-residual-first/window-record-attempts/eb2e67d5b2a44c81821a4470261c058d/executor/artifact/hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean": true,
    "audits/erdos-64-red-team/node144-residual-first/window-record-attempts/ebd3bd6b381746ee9967532895ac82c3/executor/artifact/audits/erdos-64-red-team/node144-residual-first/window-kernel-routing-label-identity.md": true,
    "audits/erdos-64-red-team/node144-residual-first/window-reduction-acceptance.json": true,
    "audits/erdos-64-red-team/node144-residual-first/window-routing-label-integration.md": true,
    "audits/erdos-64-red-team/node144-residual-first/window-routing-label-source.txt": true,
    "audits/erdos-64-red-team/node144-residual-first/window-routing-label-transport.md": true,
    "audits/erdos-64-red-team/node144-residual-first/window-source-bound-predicate-integration.md": true,
    "hypostructure/Hypostructure/Graph/DecoratedHandoffEnvelope.lean": true,
    "hypostructure/Hypostructure/Graph/ObjectCapacityLedger.lean": true,
    "hypostructure/Hypostructure/Graph/SameTokenRoutingGerms.lean": true,
    "hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean": true,
    "hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean": true,
    "tools/methodology_gate/evidence_snapshots/36ab8555e398179dd5c73fd4218acbe7dd6dde052dc2b41bb7a97ee71f06e635": true
  },
  "lean_path": "/runtime/current-vocabulary:/runtime/build-cache/lib/lean:/runtime/eg-build-cache/lib/lean:/runtime/packages/LeanSearchClient/.lake/build/lib/lean:/runtime/packages/Qq/.lake/build/lib/lean:/runtime/packages/aesop/.lake/build/lib/lean:/runtime/packages/batteries/.lake/build/lib/lean:/runtime/packages/importGraph/.lake/build/lib/lean:/runtime/packages/mathlib/.lake/build/lib/lean:/runtime/packages/plausible/.lake/build/lib/lean:/runtime/packages/proofwidgets/.lake/build/lib/lean",
  "command": [
    "/runtime/lean/bin/lean",
    "-DmaxHeartbeats=20000",
    "/tmp/window104-narrow.lean"
  ],
  "narrow_sha256": "70f31d7352617b92b7ad86440705760b42c4c91cd85c1eaa06339c44331ef18e",
  "compiled_vocabulary_sha256": "b5ef4f67ccc34ab1be9bfe6bd033cd402bbae59288d21aee99333e891ba80a8b",
  "wall_limit_seconds": 90,
  "exit_code": 1,
  "elapsed_seconds": 84.49437089500134
}
```

Complete stdout:

```text
/tmp/window104-narrow.lean:689:18: error: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (20000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
/tmp/window104-narrow.lean:692:16: error: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (20000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
/tmp/window104-narrow.lean:610:60: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (20000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

```

Complete stderr: empty.

## Scope and preservation

This is a failed narrow elaboration diagnostic, not a successful kernel check of the owner, consumer, or whole package. Inclusion of the consumer in the disposable source is not reported as a separate accepted check. The first obstruction occurs before the candidate's `actualLabel_eq` block (line 1247); the accepted label-identity result was not reproved in a separate task or replaced. No source fix, new mathematical construction, full-owner compilation, vocabulary compilation, import compilation, or root build was attempted.

The pinned window conjunction, selected graph, handoff witnesses, separate class-audit and token-ledger witnesses, domains, exclusions, both minimalities, and all quantitative accounts are unchanged. No equality between separate capacity witnesses is introduced. No bound on demand multiplicity is claimed, no negative arm is selected, and no move or branch is declared closed. The source-bound producer remains pending. The only side observation is that this first reduced-budget location is in a pre-existing arm-incidence helper, before the changed source-bound witness packaging; it was recorded without pursuing a repair.

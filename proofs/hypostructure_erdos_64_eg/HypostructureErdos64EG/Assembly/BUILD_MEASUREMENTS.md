# Assembly and SpineRows build measurements

Measured on the same development machine on 2026-09-22 with the repository's
existing Lean 4.31.0 toolchain and cached external dependencies. The working
tree contained substantial proof changes before this structural refactor.

## Baseline

The original full package build succeeded. Lake reported **1,068 seconds
(17.8 minutes)** for the original 9,261-line `Assembly.lean`, with profiling
enabled. Its cumulative profiler counters included 627 seconds in simplification,
309 seconds in tactic execution, and 51.5 seconds in instance inference.
These counters are diagnostic, not separate end-to-end build measurements.

The original 14,469-line `SpineRows.lean` took **703 seconds** to rebuild.
The initial package build also rebuilt preexisting changed framework files:
`ColdCorridorRows` alone took 2,418 seconds. That framework refresh is not an
Assembly edit benchmark and is excluded from the local-edit comparison.

Some baseline work overlapped independent refactor build experiments. Thus
these initial figures establish the observed bottleneck, but are not an isolated
hardware benchmark or a guarantee of a particular speedup.

## Individual row edits

Each measurement inserted a harmless local proof into the row body, built the
named module with warm dependencies, then restored the exact original source.

| Module below `Hypostructure.Graph.Strategy.SpineRows` | Edit and targeted rebuild |
|---|---:|
| `ReturnAvoidance` | 9.89 s |
| `Route8WindowBlockers` | 17.28 s |
| `Route8UnifiedTerminalNoGo` | 50.01 s |

All 153 row modules compile, exporting the same 156 public declarations.
All 156 types, universes, declaration kinds, and axiom sets match the original
compiled module; comparison ignores only the module component of generated
hygienic binder names. Source comparison also confirms unchanged row bodies,
attributes, options, and scoped `omit` directives.

The complete initial split-row compilation took 785.38 seconds, in batches of
eight. Splitting is primarily an incremental-development improvement; it does
not promise a cheaper first build.

## Assembly edit measurements

Representative edits insert an unused local `True` proof into the selected
proof body. Each targeted build is followed by a full build. Between samples,
the exact source and its previously verified build artifacts are restored; a
no-change build checks cache validity. Restoring identical proofs is not counted
as an edit measurement. All commands use warm dependency caches.
API/audit validation also ran during part of this session;
wall-clock figures describe that development workload, not isolated CPU time.

An unchanged full build took **6.123 seconds**, with **zero Lean modules rebuilt**.

| Edited Assembly module | Targeted check | Subsequent downstream build | Combined |
|---|---:|---:|---:|
| `TypeA.ExitFourChain` | 15.887 s | 325.728 s | 341.615 s |
| `TypeB.HighSurplusContinuation` | 19.854 s | 220.037 s | 239.891 s |
| `Cold.Germs` | 10.543 s | 10.098 s | 20.641 s |
| `NearCubic.Survivor.RealizedBelow.Wedge` | 19.885 s | 27.033 s | 46.918 s |

Each targeted check rebuilt exactly one module. Subsequent full builds rebuilt
50, 47, 2, and 7 importing modules respectively. Every rebuilt module was in
the edited module's dependency closure. Type A edits left Type B and cold
siblings cached; Type B edits left Type A and cold siblings cached. The cold
edit rebuilt only the two compatibility/package importers, while the survivor
edit left its sibling branch implementations cached.

Combined times were approximately 3.1×, 4.5×, 51.7×, and 22.8× faster than the
observed monolithic Assembly baseline, subject to the workload caveat above.
**Targeted checks take seconds; a widely used continuation still requires a
several-minute full downstream rebuild.**

After the final source/cache restoration, the unchanged full build took
**4.359 seconds**, with zero Lean recompilation. All temporary proof edits
were removed. Machine-readable measurements and rebuilt-module lists are in
[`BUILD_MEASUREMENTS.json`](BUILD_MEASUREMENTS.json).

## Compatibility and audit checks

- The full EG package builds successfully with 90 Assembly modules and 153
  SpineRows modules behind imports-only compatibility files.
- All 88 original public Assembly declarations match their original types,
  universes, declaration kinds, and axiom sets. Shared former private names and
  the module component of hygienic binder names are normalized for comparison.
- Expanding the extracted helper calls reconstructs the original survivor and
  strict-surplus proof tokens, ignoring whitespace and comments.
- All 230 original `EG-NODE` annotation lines are preserved.
- The axiom audit ran in a disposable package copy: 144 declarations inspected,
  no frontier stubs, no tracer-tainted declarations, and none unreported. This
  does not remove any existing mathematical assumption or open residual.
- Eight Python regression checks cover recursive audit discovery, private-name
  handling, restoration on failure, import cycles, and compatibility coverage.
- The live node tables retain their judgments; declaration links and the API
  catalog point to the new modules.

## Reproducing a local check

From `proofs/hypostructure_erdos_64_eg`:

```sh
lake build Hypostructure.Graph.Strategy.SpineRows.ReturnAvoidance
lake build HypostructureErdos64EG.Assembly.TypeA.ExitFourChain
lake build HypostructureErdos64EG.Assembly.NearCubic.Survivor.RealizedBelow.Wedge
lake build
```

Keep the build cache between edits. The named target checks its prerequisites;
the full build also checks importing dependents. Shared vocabulary or framework
changes can still cause much wider rebuilds. The existing open mathematical
residuals and axiom dependencies are retained.

# Working on the Erdős–Gyárfás assembly

`HypostructureErdos64EG.Assembly` remains the compatibility import for all public
assembly declarations. Individual proof modules live here and retain the
`HypostructureErdos64EG` namespace. The directory hierarchy does not change
public declaration names.

From `proofs/hypostructure_erdos_64_eg`, build the module being edited:

```sh
lake build HypostructureErdos64EG.Assembly.TypeA.ExitFourChain
lake build HypostructureErdos64EG.Assembly.Cold.Germs
lake build HypostructureErdos64EG.Assembly.NearCubic.Survivor.RealizedBelow.Wedge
```

Before finishing a change, build the whole package:

```sh
lake build
```

Keep `.lake` build artifacts between edits. A targeted build checks that module
and its prerequisites; the full build also checks downstream callers. Neither
command needs a clean build for ordinary proof changes.

## Dependency structure

- `Basic` contains the problem/input/target aliases.
- `Boundary` modules contain shared result types and import no branch proofs.
- `Entry`, `Surplus/Local`, `Cold/*`, `NearCubic/Local`, and `RouteEight/Local`
  contain independently reusable steps.
- `TypeA/*`, `TypeB/*`, and `Absorbed/*` contain individual continuations.
- `NetCharge/Continuation` combines the Type A/B and absorbed continuations.
- `NearCubic/Survivor` combines the survivor branches. Its subdirectories split
  rank, entropy, root-wedge, linear-mass, and bounded-mass decisions into
  independently compiled proofs with explicit complete ledger inputs.
- `Final` connects the entry decisions to strict-surplus and near-cubic results.

Import the module that defines a dependency. Never import `Assembly` or the
package root from within this directory: those imports create cycles or make
unrelated proof branches rebuild together. Do not add an import merely because
a module precedes another in manuscript order.

Helpers shared between files use `HypostructureErdos64EG.Assembly.Internal`.
Helpers used by only one file remain private. These helpers are implementation
details, not new assumptions or alternative ledger interfaces.

The axiom audit discovers this directory recursively and resolves private
names from Lean's compiled index. The API catalog checker also scans every
module here. Preserve node annotations when moving declarations; update live
source references without rewriting historical audit evidence.

## Measuring changes

Measure with framework dependencies already built. Record separately:

1. the build of the edited module;
2. the subsequent full package build;
3. the no-change full build.

For declaration profiling without changing package-wide options:

```sh
lake env lean -Dprofiler=true HypostructureErdos64EG/Assembly/TypeA/ExitFourChain.lean
```

A change to a common framework module can still invalidate many proofs.
Splitting modules reduces the work for local edits; it does not remove genuine
import dependencies. See `BUILD_MEASUREMENTS.md` for this refactor's results.

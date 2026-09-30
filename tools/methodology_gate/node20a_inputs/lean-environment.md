# Lean environment inside the worker sandbox (operator note; no mathematics)

The kernel toolchain and warm build caches of the pinned sources (g-repair-base at
7d3186b, which the frozen `/input/sources` match) are mounted read-only:

* `/runtime/lean`: the Lean 4.31.0 toolchain (`/runtime/lean/bin/lean`, `/runtime/lean/bin/lake`);
* `/runtime/hypostructure-build/lib/lean`: `.olean` files of every `Hypostructure.*` module;
* `/runtime/erdos-build/lib/lean`: `.olean` files of every `HypostructureErdos64EG.*` module;
* `/runtime/erdos-packages/<pkg>/.lake/build/lib/lean`: Mathlib and the other dependencies.

**Check a new file against the existing modules.** This takes seconds and has been
tested in this sandbox. Write the file under `/output`, then run:

```sh
LP=/runtime/erdos-build/lib/lean:/runtime/hypostructure-build/lib/lean
for p in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do
  LP=$LP:/runtime/erdos-packages/$p/.lake/build/lib/lean; done
LEAN_PATH=$LP /runtime/lean/bin/lean /output/Scratch.lean
```

A file that imports, for example, `Hypostructure.Graph.ReadingProfiles` and
`HypostructureErdos64EG.Assembly.Residuals` elaborates in about 3 seconds. Use this
for every new vocabulary-free library lemma and every statement or contract module
that only *imports* existing modules.

**What this does not check.** An edit to an existing module that other modules
import (for example `Strategy/SpineVocabulary.lean`, `Assembly/Final.lean` or
`Assembly/Residuals.lean`) is not checked this way. The controller's locked check
(`lake build HypostructureErdos64EG.Assembly.Final` on the submitted replacement
files) checks those after submission.

**Process facts.** Each worker has a time budget of 90 minutes. The stage
controller dispatches exactly one assignment per round. It has no mechanism that
launches child contexts for the sub-obligations of a stage assignment. A
NEEDS_DECOMPOSITION submission at Stage 3b is therefore re-queued as the same
Stage 3b assignment.

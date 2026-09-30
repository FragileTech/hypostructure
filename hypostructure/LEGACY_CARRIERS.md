# Illegal data carriers in Core and Graph

**Gate status.**  `scripts/check_quarantine.py` (wired into `make lint`)
fails with 13 violations:

- six quarantined modules are imported by live code:
  `Graph.TypeBFanClosedPorts` and `Graph.TypeBPostLedgerCore` (from
  `Graph.Statements.Parameters`), `Graph.TypeABCertificate` (from
  `Graph.TypeBGlobalLocalReflection` and `Graph.TypeBPostLedgerCore`), and,
  through them, `Graph.DecoratedFan`, `Graph.ReceiverExhaustion` and
  `Graph.TypeBMarkedFan`;
- `Core/Strategy/ExactExecution.lean:191` declares into the canonical
  `Core.Residual.ExactLedger` namespace;
- six ledger-named declarations: the carriers `CapacityTokenLedger`
  (`Graph/CapacityTokenLedger.lean`), `ObjectCapacityLedger` and
  `CertifiedObjectCapacityLedger` (`Graph/ObjectCapacityLedger.lean`) and
  `DisjointLedger` (`Graph/TypeBCanonicalB2.lean`), and the accessors
  `canonicalIncidenceLedger` (`Graph/SurplusBlockers.lean`) and
  `augmentedLedger` (`Graph/TypeBCanonicalB2.lean`).

There is one allowed API: `Core.Residual.ExactLedger` and the accessors it
exposes.

## Quarantine

The modules listed in `quarantine.txt` (78 entries, all on disk) are kept
out of the build closure, except the six listed above that live code imports.
They are the porting reference for the rows that have not
been rewritten on `ExactLedger`. The legacy `Core.Residual.Ledger` /
`Ledger.Extension` stage stack is not in the build.

**The framework names the problem only through `Spine.Data`.**  The curvature
algebra is order-generic.  The Hegde--Sandeep--Shashank axiom
(`p13Free_hasPowerOfTwoCycle`) lives in the proof's `WindowAlgebra.lean` and
reaches the framework as the `freeForcesTarget` field, and `windowOrder` is a
field whose value the proof supplies.  The field types of `Spine.Data` in
`Graph/Strategy/SpineVocabulary.lean` pin the manuscript's values
(`threshold_eq_three`, `labelCount : ... = 399`, `labelSizeDistribution`), and
the `.localAlgebra` fact statement repeats `399` and the size distribution.

## Counts

Live modules are the gate's own `build_closure()` (transitive imports of `Hypostructure.lean`),
the spine closure is the same walk from `SpineVocabulary` (itself included),
and the gate result is a run of `scripts/check_quarantine.py`.

| | |
|---|---|
| live modules in the build | 656 |
| quarantined (`quarantine.txt` entries) | 78 |
| `Graph.Strategy.SpineVocabulary` import closure | 356 modules |
| quarantined modules reachable from the spine | 6 |
| legacy `Core.Residual.Ledger` / `Ledger.Extension` in the build | none |
| gate violations | 13 |

The spine reaches no legacy `Core.Residual.Ledger` or `Ledger.Extension`, but
its import closure includes the six quarantined modules and the ledger-named
carriers listed above.

## Scope note

This gate is name-based -- it matches declarations named `...Ledger`.  A carrier
named `Summary`, `Profile`, `Store`, or `Registration` passes it untouched, so a
clean run is necessary and not sufficient.  The structural guarantee is
`FactSystem.value_subsingleton`, which makes a fact value unable to hold data at
all; and the side channel that the name gate does not see --
`Ledger.Extension`, a dependent pair that lets a stage carry anything -- is
outside the build: no live module mentions it.

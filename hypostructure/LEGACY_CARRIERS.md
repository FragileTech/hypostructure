# Illegal data carriers in Core and Graph

**Some are back in the build.**  `scripts/check_quarantine.py` (wired into
`make lint`) currently fails with 15 violations:

- eight quarantined modules are imported by live code again:
  `Graph.TypeBFanClosedPorts` and `Graph.TypeBPostLedgerCore` (from
  `Graph.Strategy.SpineVocabulary`), `Graph.TypeABCertificate` (from
  `Graph.TypeBGlobalLocalReflection`), `Graph.TypeBProfileSchedule` (from
  `Graph.TypeBCanonicalB2`), and, through them, `Graph.DecoratedFan`,
  `Graph.ReceiverExhaustion`, `Graph.TypeBHybridLedger` and
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

## How it was cleared

Two mechanisms, in this order.

**Deleted, carrier by carrier, as their rows ported.**  `RateLedger`,
`CriticalityLedger`, `SlackIncompatibilityLedger`, `deletionCriticalityOfLedger`,
`VisibleLoadLedger`, `inheritedOverflowLedger`, `classifiedCapacityLedger`,
`classifiedDensityLedger`, and the `Execution`/`Routing` stage chains.  The
mathematics survived every one -- in several cases it got shorter, because the
carrier had been the long way round to say something about two natural numbers.

**Quarantined, once the spine no longer needed them.**  The entry spine was
first severed from the legacy stage stack by splitting ten files along the seam
between their mathematics and their `Ledger.Extension` plumbing.  With the
spine's import closure clean, the whole legacy-ledger cone -- 226 live modules
at that point -- could leave the build without touching it.

The quarantined modules still on disk are the porting reference for the rows
that have not been rewritten yet.  See `quarantine.txt`: 73 of its 82 entries
are on disk; the other nine have since been deleted.

**Deleted outright, once their rows had exactly one implementation.**  Block A's
legacy layer is no longer quarantined beside the spine -- it is gone.  Twenty-two
`Core.Strategy` modules (the counterexample-reduction chain, obstruction
packing, the exact finite local algebra, the scale-threshold and barrier
dichotomies, the density budget, and the row-37/38 normalization and
boundary-demand pair) and seven `Graph.Strategy` modules were removed, together
with `Graph.External.HegdeSandeepShashank`, `Graph.WindowCurvatureTypeB` and
`Graph.Strategy.Official.Universal`.  The EG registration layer that drove them
(`Official/`, `AB/`, `Presentation.lean`) went with them.

**The framework names the problem only through `Spine.Data`.**  The curvature
algebra is order-generic.  The Hegde--Sandeep--Shashank axiom
(`p13Free_hasPowerOfTwoCycle`) lives in the proof's `WindowAlgebra.lean` and
reaches the framework as the `freeForcesTarget` field, and `windowOrder` is a
field whose value the proof supplies.  The field types of `Spine.Data` in
`Graph/Strategy/SpineVocabulary.lean` do still pin the manuscript's values
(`threshold_eq_three`, `labelCount : ... = 399`, `labelSizeDistribution`), and
the `.localAlgebra` fact statement repeats `399` and the size distribution.

## Where things stand

| | |
|---|---|
| live modules in the build | 410 |
| quarantined (`quarantine.txt` entries) | 82 |
| `Graph.Strategy.SpineVocabulary` import closure | 187 modules |
| quarantined modules reachable from the spine | 8 |
| legacy `Core.Residual.Ledger` / `Ledger.Extension` in the build | none |
| gate violations | 15 |

The spine reaches no legacy `Core.Residual.Ledger` or `Ledger.Extension`, but
its import closure includes the eight quarantined modules and the ledger-named
carriers listed above.

## Scope note

This gate is name-based -- it matches declarations named `...Ledger`.  A carrier
named `Summary`, `Profile`, `Store`, or `Registration` passes it untouched, so a
clean run is necessary and not sufficient.  The structural guarantee is
`FactSystem.value_subsingleton`, which makes a fact value unable to hold data at
all; and the legacy side channel that the name gate never saw --
`Ledger.Extension`, a dependent pair that let a stage carry anything -- is now
outside the build entirely: no live module mentions it.

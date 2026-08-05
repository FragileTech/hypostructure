# Illegal data carriers in Core and Graph

**None remain in the build.**  `scripts/check_quarantine.py` passes, and it is
wired into `make lint`, so a new one cannot land silently.

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

The quarantined modules are still on disk and are the porting reference for the
rows that have not been rewritten yet.  See `quarantine.txt`.

## Where things stand

| | |
|---|---|
| live modules in the build | 111 |
| quarantined | 315 |
| entry-spine import closure | 58 modules |
| legacy residual stack reachable from the spine | none |
| gate violations | 0 |

The spine reaches no `Ledger`, `Stage`, `Query`, `Focus`, or `Decision`.  Block
A runs on `ExactLedger` by construction, not by convention.

## Scope note

This gate is name-based -- it matches declarations named `...Ledger`.  A carrier
named `Summary`, `Profile`, `Store`, or `Registration` passes it untouched, so a
clean run is necessary and not sufficient.  The structural guarantee is
`FactSystem.value_subsingleton`, which makes a fact value unable to hold data at
all; and the legacy side channel that the name gate never saw --
`Ledger.Extension`, a dependent pair that let a stage carry anything -- is now
outside the build entirely.

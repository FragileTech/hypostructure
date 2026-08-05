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

**Deleted outright, once their rows had exactly one implementation.**  Block A's
legacy layer is no longer quarantined beside the spine -- it is gone.  Twenty-two
`Core.Strategy` modules (the counterexample-reduction chain, obstruction
packing, the exact finite local algebra, the scale-threshold and barrier
dichotomies, the density budget, and the row-37/38 normalization and
boundary-demand pair) and seven `Graph.Strategy` modules were removed, together
with `Graph.External.HegdeSandeepShashank`, `Graph.WindowCurvatureTypeB` and
`Graph.Strategy.Official.Universal`.  The EG registration layer that drove them
(`Official/`, `AB/`, `Presentation.lean`) went with them.

**The framework stopped naming the problem.**  The curvature algebra is
order-generic; the specializations at `windowOrder = 13` and the label count
`399`, and the Hegde--Sandeep--Shashank axiom, now live in the proof and reach
the framework only as fields of the problem's registered `Spine.Data`.

## Where things stand

| | |
|---|---|
| live modules in the build | 106 |
| quarantined | 302 |
| entry-spine import closure | 62 modules |
| legacy residual stack reachable from the spine | none |
| problem-specific declarations in Core or Graph | none |
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

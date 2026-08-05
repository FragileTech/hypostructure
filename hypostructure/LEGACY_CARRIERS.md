# Illegal data carriers still live in Core and Graph

Generated from `scripts/check_quarantine.py`, ordered by blast radius.

There is one allowed API: `Core.Residual.ExactLedger` and the accessors it
exposes. Each entry below is a declaration that violates it — either a record
that carries facts (`parallel data carrier`) or a set of accessors that forms a
second ledger API (`second ledger API`).

**Delete the carrier, keep the mathematics.** Every one of these files also
holds real proofs. The work per file is: remove the record and its accessors,
and route what the proofs need through the canonical ledger instead. Nothing
mathematical should be lost — only the vehicle it travels in.

`live deps` is the number of modules in the build closure that would need
touching, so the list is also the cheapest-first order to do the work.

## Status

Block A (nodes `[1]`–`[24]`) is ported. **No Block A row constructs, reads, or
writes any of the carriers below.** The spine runs on `ExactLedger` alone:
`Graph/Strategy/SpineRun.lean` composes all ten rows, and
`complete_audit_facts` pins the ledger's audit to exactly the ten facts it
commits. The `on Block A path` column below records only that a module is
*reachable through imports* from the spine — never that the spine uses it.

Deleted since the previous revision, as their rows ported:

| carrier | was | replaced by |
|---|---|---|
| `FiniteBarrierEnumerationSemantics.RateLedger` | row 9's rate carrier | `Key.barrierCap` / `barrierOverflow` |
| `CriticalModificationStructure.CriticalityLedger` | row 4's criticality carrier | `Key.tightEndpoint` |
| `CriticalModificationStructure.SlackIncompatibilityLedger` | row 4's slack carrier | `Key.slackIndependent` |
| `Graph.deletionCriticalityOfLedger` | row 4's graph accessor | `deletionCriticalityRow` |
| `ReceiverLoad.VisibleLoadLedger` | unused visible-load carrier | — (no consumer) |
| `ColdBranchAggregation.inheritedOverflowLedger` | overflow accessor | — (no consumer) |
| `FiniteStateNetChargeContinuation.classifiedCapacityLedger` | capacity accessor | — (no consumer) |
| `FiniteStateNetChargeContinuation.classifiedDensityLedger` | density accessor | — (no consumer) |

Quarantined in the same pass: `Core.Strategy.FiniteBottleneckClassification`,
`Core.Strategy.FiniteDensityBudget`, `Core.Strategy.CriticalModificationStructure`,
`Core.Strategy.CounterexampleReduction`, `Graph.InducedPathWindowLedger`,
`Graph.Strategy.Official.Features.SupportIncidenceLedger`.

The gate stands at **17** violations, from 30.

## What is left

| live deps | violations | on Block A path | module |
|---:|---:|:-:|---|
| 1 | 1 | no | `Core.ClosedLedger.Closure` (`ClosedClassLedger`) |
| 1 | 3 | yes | `Core.Finite.ColdCorridor` (`classifyIntoLedger` ×2, `classifyStateIntoLedger`) |
| 1 | 1 | no | `Core.NormalForm.ClassClosure` (`extendedLedger`) |
| 1 | 1 | yes | `Core.Strategy.ColdBranchAggregationSemantics` (`OverflowLedger`) |
| 1 | 1 | no | `Core.Strategy.CoupledHomogeneousFibrePressure` (`OverloadLedger`) |
| 1 | 1 | yes | `Core.Strategy.FiniteStateNetChargeContinuationSemantics` (`CapacityLedger`) |
| 1 | 2 | no | `Core.Strategy.Official.Features.DeletionFanAccounting` (`ThresholdLedger`, `deriveThresholdLedger`) |
| 1 | 1 | no | `Graph.TypeBOverlapObstruction` (`RefinedSupportLedger`) |
| 2 | 1 | yes | `Core.Strategy.FiniteDensityBudgetSemantics` (`CapLedger`) |
| 2 | 2 | no | `Graph.Strategy.Official.Features.DegreeSurplusLedger` (bare `Ledger` ×2) |
| 2 | 1 | no | `Graph.TypeBBridgeResidual` (`augmentedLedger`) |
| 6 | 1 | yes | **`Core.Residual.Ledger`** (bare `Ledger`) — the legacy residual ledger |
| 6 | 1 | yes | `Core.Strategy` (`CapacityLedger`) |

## The two that block the rest

`Core/Residual/Ledger.lean:28` and `Core/Strategy.lean:1595` are the spine of
the legacy framework. Six direct dependents each, but the transitive cone is
essentially the whole build: `Core.Strategy` alone is reachable from 71
modules, including — through `Graph.Strategy.MinimumDegreeBaseline` — the new
spine's own vocabulary. They cannot be cut; they dissolve as the remaining
blocks port onto `ExactLedger`.

`FiniteDensityBudgetSemantics.CapLedger` is a near miss. It is row 10's old
carrier and row 10 no longer touches it, but
`FiniteStateNetChargeContinuation`'s `DensityCap56`/`RateCap56` machinery —
row 41, block E — still reads its four queries. It goes when row 41 ports.

## Scope note

This gate is name-based — it matches declarations named `...Ledger`. A carrier
named `Summary`, `Profile`, `Store`, or `Registration` passes it untouched, so
a clean run here is necessary and not sufficient. The structural guarantee is
`FactSystem.value_subsingleton`, which makes a fact value unable to hold data
at all.

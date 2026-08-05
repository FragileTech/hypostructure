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

`live dependents` is the number of modules in the build closure that would need
touching, so the list is also the cheapest-first order to do the work.

| live deps | violations | module |
|---:|---:|---|
| 1 | 1 | `Core.Strategy.FiniteBottleneckClassification` (`SeparatorLedger`) |
| 1 | 1 | `Graph.InducedPathWindowLedger` (bare `Ledger`) |
| 1 | 1 | `Graph.Strategy.Official.Features.SupportIncidenceLedger` (bare `Ledger`) |
| 1 | 2 | `Core.Strategy.FiniteDensityBudget` (`overflowLedger`, `capLedger`) |
| 2 | 1 | `Core.NormalForm.ClassClosure` (`extendedLedger`) |
| 2 | 1 | `Graph.TypeBOverlapObstruction` (`RefinedSupportLedger`) |
| 5 | 1 | `Core.ClosedLedger.Closure` (`ClosedClassLedger`) |
| 5 | 1 | `Core.Strategy.CoupledHomogeneousFibrePressure` (`OverloadLedger`) |
| 5 | 2 | `Graph.Strategy.Official.Features.DegreeSurplusLedger` (bare `Ledger` ×2) |
| 9 | 1 | `Graph.TypeBBridgeResidual` (`augmentedLedger`) |
| 18 | 2 | `Core.Strategy.Official.Features.DeletionFanAccounting` (`ThresholdLedger`) |
| 23 | 1 | `Graph.ReceiverLoad` (`VisibleLoadLedger`) |
| 24 | 1 | `Graph.DeletionCriticality` (`deletionCriticalityOfLedger`) |
| 26 | 2 | `Core.Strategy.CriticalModificationStructure` (`CriticalityLedger`, `SlackIncompatibilityLedger`) |
| 43 | 1 | `Core.Strategy` (`CapacityLedger`) |
| 71 | 1 | `Core.Strategy.ColdBranchAggregation` (`inheritedOverflowLedger`) |
| 71 | 2 | `Core.Strategy.FiniteStateNetChargeContinuation` |
| 72 | 1 | `Core.Strategy.ColdBranchAggregationSemantics` (`OverflowLedger`) |
| 72 | 1 | `Core.Strategy.FiniteDensityBudgetSemantics` (`CapLedger`) |
| 72 | 1 | `Core.Strategy.FiniteStateNetChargeContinuationSemantics` (`CapacityLedger`) |
| 73 | 3 | `Core.Finite.ColdCorridor` (`classifyIntoLedger` ×2, `classifyStateIntoLedger`) |
| 77 | 1 | `Core.Strategy.FiniteBarrierEnumerationSemantics` (`RateLedger`) |
| **275** | 1 | **`Core.Residual.Ledger`** (bare `Ledger`) — the legacy residual ledger |

## The one that matters

`Core/Residual/Ledger.lean:28` is the spine of the legacy framework: 275 live
dependents, essentially all of CT1–CT17. It cannot be cut; it has to be
dissolved as rows port onto `ExactLedger`. Everything above it in the table is
comparatively local.

## Scope note

This gate is name-based — it matches declarations named `...Ledger`. A carrier
named `Summary`, `Profile`, `Store`, or `Registration` passes it untouched, so
a clean run here is necessary and not sufficient. The structural guarantee is
`FactSystem.value_subsingleton`, which makes a fact value unable to hold data
at all.

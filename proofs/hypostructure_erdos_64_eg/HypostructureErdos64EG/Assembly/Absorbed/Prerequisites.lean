import Hypostructure.Graph.Strategy.ColdCorridorRows
import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: Absorbed / Prerequisites

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Nodes `[174]`--`[177]`, `lem:absorbed-germ-fan-data`: the absorbed-germ
residual**, index-polymorphic over any residual carrying the hot/cold ledger of
the fixed packing and the actual `[153]` first-failure state and extraction.
Its cold windows' selected branch-excess corridors were charged as the
germ-extraction loss; the charge is restored here at `[175]`: a selected corridor with a
subcubic first-failure support is a genuine (F5) germ, routed exactly as
`[154]`--`[157]` and the `[163]` symmetry split (`[176]`); otherwise every
  selected corridor meets a heavy centre and the half-edges are decorated
  handoff fan data entering Type B at `[65]` (`[177]`).  The function then runs
  the paper's common `[67]`--`[85]` continuation and returns its literal
  ExactLedger boundary.  The genuine-germ arm closes and is eliminated into
  the same result type; no `[64]`-specific quantitative tail is imported.
Entered only from the exact collision failure (`[173]`). -/
-- EG-NODE [153] linear first-failure extraction? \(N_{\rm conf}\ge9C/D_{\rm cold}-o(n)\)
-- EG-NODE [154] bounded configuration case?
-- EG-NODE [155] G1: power-of-two cycle
-- EG-NODE [156] G2: target defect, exit (4), or handoff
-- EG-NODE [157] G3 or same-interface table: compression
-- EG-NODE [163] neutral equal-length terminal configuration: second strand graph-realized?
-- EG-NODE [165] canonical replacement \(E\ne Q\): swap \(Q\to E\) gives a same-size counterexample
-- EG-NODE [166] refined lexicographic minimality: \(Q=E\)
-- EG-NODE [167] symmetric strand pair: finite two-strand check on the closing lengths \(2\ell\), \(\ell+d\)
-- EG-NODE [169] trivial neutral-configuration residual: dense packing, every corridor terminal and neutral, \(Q=E\); every window is blocked at every dyadic scale
-- EG-NODE [175] selected corridor meets a high-degree vertex?
-- EG-NODE [176] graph-realized (F5) configuration: closed by [154]--[157], [165]--[168]
-- EG-NODE [177] decorated handoff fan data at the heavy centre \(z\): continue at Type B [65]
private noncomputable abbrev AbsorbedPrerequisiteKnown (known : FactKeys EGInput.{u}) :
    FactKeys EGInput.{u} :=
  coldGermCandidatesRow.manifest.Produces ++
    (coldGermExtractionRow.manifest.Produces ++
      (coldFirstFailureRoutingRow.manifest.Produces ++
        (coldHandoffTransferRow.manifest.Produces ++
          (coldFailureHandoffRow.manifest.Produces ++
            (coldFailureCompressionRow.manifest.Produces ++
              (coldFailureDefectRow.manifest.Produces ++
                (coldFailureCycleRow.manifest.Produces ++
                  (coldFirstFailureOccurrenceRow.manifest.Produces ++
                      (denseColdCorridorsTerminalRow.manifest.Produces ++
                          (coldCorridorStateRow.manifest.Produces ++
                          (coldDeclaredHandoffLedgerRow.manifest.Produces ++
                            (coldReturnCorridorRow.manifest.Produces ++ known))))))))))))

/-- The enclosing node-`[174]` assembly publishes the corridor and extraction
facts which node `[175]` receives.  These are the canonical registered owners
from node `[153]`; `[175]` never reconstructs them and only queries their
ExactLedger entries. -/
noncomputable def selectedAbsorbedGermPrerequisites
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .bridgeless) known]
    (returnFresh : K .coldReturnCorridors ∉ known)
    (declaredFresh : K .coldDeclaredHandoffLedger ∉ known)
    (stateFresh : K .coldCorridorState ∉ known)
    (terminalFresh : K .denseColdCorridorsTerminal ∉ known)
    (occurrenceFresh : K .coldFirstFailureOccurrence ∉ known)
    (routingFresh : K .coldFailureRouting ∉ known)
    (failureCycleFresh : K .coldFailureCycle ∉ known)
    (failureDefectFresh : K .coldFailureDefect ∉ known)
    (failureDefectRouteFresh : K .coldFailureDefectRoute ∉ known)
    (failureCompressionFresh : K .coldFailureCompression ∉ known)
    (failureHandoffFresh : K .coldFailureHandoff ∉ known)
    (handoffTransferFresh : K .coldHandoffTransfer ∉ known)
    (exchangeFresh : K .coldExchangeBound ∉ known)
    (extractionFresh : K .coldGermExtraction ∉ known)
    (candidatesFresh : K .coldGermCandidates ∉ known) :
    ExactLedger EGInput.{u} selected (AbsorbedPrerequisiteKnown known) := by
  let returned :=
    (coldReturnCorridorRow (data := spineData)).run history
      (by simp [K_eq_iff, returnFresh])
  let declared :=
    (coldDeclaredHandoffLedgerRow (data := spineData)).run returned
      (by simp [K_eq_iff, declaredFresh])
  let state :=
    (coldCorridorStateRow (data := spineData)).run declared
      (by simp [K_eq_iff, stateFresh])
  let terminal :=
    (denseColdCorridorsTerminalRow (data := spineData)).run state
      (by simp [K_eq_iff, terminalFresh])
  let occurrence :=
    (coldFirstFailureOccurrenceRow (data := spineData)).run terminal
      (by simp [K_eq_iff, occurrenceFresh])
  let failureCycle :=
    (coldFailureCycleRow (data := spineData)).run occurrence
      (by simp [K_eq_iff, failureCycleFresh])
  let failureDefect :=
    (coldFailureDefectRow (data := spineData)).run failureCycle
      (by simp [K_eq_iff, failureDefectFresh, failureDefectRouteFresh])
  let failureCompression :=
    (coldFailureCompressionRow (data := spineData)).run failureDefect
      (by simp [K_eq_iff, failureCompressionFresh])
  let failureHandoff :=
    (coldFailureHandoffRow (data := spineData)).run failureCompression
      (by simp [K_eq_iff, failureHandoffFresh])
  let handoffTransfer :=
    (coldHandoffTransferRow (data := spineData)).run failureHandoff
      (by simp [K_eq_iff, handoffTransferFresh])
  let routed :=
    (coldFirstFailureRoutingRow (data := spineData)).run handoffTransfer
      (by simp [K_eq_iff, stateFresh, occurrenceFresh, routingFresh, failureCycleFresh,
        failureDefectFresh, failureDefectRouteFresh, failureCompressionFresh,
        failureHandoffFresh, handoffTransferFresh])
  let extracted :=
    (coldGermExtractionRow (data := spineData)).run routed
      (by simp [K_eq_iff, exchangeFresh, extractionFresh])
  exact (coldGermCandidatesRow (data := spineData)).run extracted
    (by simp [K_eq_iff, candidatesFresh])

end HypostructureErdos64EG

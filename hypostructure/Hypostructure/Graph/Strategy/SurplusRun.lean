import Hypostructure.Graph.Strategy.SurplusRows
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows
import Hypostructure.Graph.Strategy.SpineAssembly
import Hypostructure.Graph.Strategy.ColdCorridorRun

/-!
# The sparse surplus branch, run

Nodes `[126]`--`[136]`, on the arm node `[19]` sends an object whose degree
surplus exceeds the registered scale threshold.  The rows of `SurplusRows` are
each quantified over the keys they consume and produce; this module installs
them at the spine's own vocabulary and runs them in the manuscript's order
against the one canonical `ExactLedger`, over the literal ledger the entry
spine leaves at `Spine.Result.surplusAbove`.

Every prerequisite is discharged by instance resolution against the incoming
index: node `[127]` does not elaborate before node `[10]`'s slack-independence
entry, and node `[128]` does not elaborate before the node-`[1]`--`[4]`
selection entry.  Nothing is carried between rows but the residual and the
ledger, and no row names a producer or an execution position.

Node `[125]` is the *survivor* of the five sparse surplus exits of
`def:named-surplus-exits`, together with `lem:replacement`'s proper-support
obstruction at the same selection.  Both halves are derived from the node
`[1]`--`[4]` selection entry, and both are what node `[132]`'s blocker arm
needs, so neither is left to be assumed by a later row.

Node `[132]` is `lem:sparse-pair-dependence-exit`'s own disjunction and is a
branch here: its exit arm is node `[133]`, where the exit collides with node
`[125]`'s entry and Core's `closeIncompatible` appends the canonical closure
key, and its blocker arm is the one the canonical blocker ledger `[134]` and
everything downstream of it runs on.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## The rows, at the spine's own keys

Every schema bridge below is the identity on `PLift`: the spine's value at a
sparse-surplus key *is* the manuscript statement, so nothing is re-encoded. -/

/-- Node `[126]`: the sparse slack identity. -/
@[reducible] noncomputable def sparseSlackSurplus :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  sparseSlackSurplusRow (K .sparseSlackSurplus) (fun _input value => ⟨value⟩)

/-- Node `[127]`: the excess selector, its count, and the port structure. -/
@[reducible] noncomputable def activeSurplusFamily :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  activeSurplusFamilyRow (K .slackIndependent) (K .activeSurplusFamily)
    (by simp) (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Node `[128]`: port activation.

The selection entry supplies both halves the suppression witness needs: the
object's own avoidance and its own minimality.  The minimality clause is read
at the registered progress, which is the canonical lexicographic one, so it is
exactly the raw hypothesis `TightVertexSuppression` asks for. -/
@[reducible] noncomputable def sparsePortActivation :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  sparsePortActivationRow (K .selection) (K .sparsePortActivation) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact smaller lexicographic baseline =>
      fact.down.2 smaller lexicographic baseline)
    (fun _input value => ⟨value⟩)

/-- Node `[129]`: the common cubic baseline and the room above it. -/
@[reducible] noncomputable def baselineSpineDemand :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  baselineSpineDemandRow (K .windowPackageSeparated) (K .baselineSpineDemand)
    (by simp) (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Nodes `[130]`--`[134]`: the pair schedule and the canonical blocker
ledger. -/
@[reducible] noncomputable def canonicalPairLedger :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  canonicalPairLedgerRow (K .activeSurplusFamily) (K .sparseSlackSurplus)
    (K .surplusAbove) (K .baselineSpineDemand) (K .canonicalBlockerRoute)
    (K .canonicalPairLedger)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input fact Coordinate family support =>
      (fact.down Coordinate family support).2)
    (fun _input value => ⟨value⟩)

/-- Node `[132]`: `lem:sparse-pair-dependence-exit`'s own disjunction.  The exit
arm is node `[133]` and the blocker arm opens the canonical blocker ledger
`[134]`. -/
@[reducible] noncomputable def blockedPairRouting
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (exitFresh : K (data := data) .sparsePairExit ∉ known)
    (blockerFresh : K (data := data) .canonicalBlockerRoute ∉ known) :
    Decision (K (data := data) .sparsePairExit)
      (K (data := data) .canonicalBlockerRoute) previous :=
  blockedPairRoutingDichotomy previous (K .sparsePairExit)
    (K .canonicalBlockerRoute) (fun value => ⟨value⟩) (fun value => ⟨value⟩)
    exitFresh blockerFresh

/-- **Node `[133]`: the sparse surplus exit closes.**

Node `[125]` commits that the selected object survives the sparse surplus exits
and node `[132]`'s exit arm commits that one occurs.  Neither fact mentions the
other, and neither node knows the other exists: the contradiction is read off
the two committed statements, so the closure is the framework's rather than a
row's. -/
noncomputable instance sparsePairExitClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .sparseSurplusSurvivor)
      (K (data := data) .sparsePairExit) where
  contradiction := fun _input survivor exit => exit.down survivor.down

/-- Node `[138]`'s registered square-root bound contradicts the high-surplus
entry that opened this branch. -/
noncomputable instance spineSurplusEstimateClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .surplusAbove)
      (K (data := data) .spineSurplusEstimate) where
  contradiction := fun _input above estimate =>
    have above' : data.surplusThreshold _input.object.vertexCount <
        _input.object.degreeSurplus data.threshold := above.down
    have estimate' : _input.object.degreeSurplus data.threshold ≤
        data.spineScale * Core.ceilSqrt _input.object.vertexCount := estimate.down
    (Nat.not_lt_of_ge estimate') (by
      rw [Data.surplusThreshold] at above'
      exact above')

/-- Nodes `[134]`--`[136]`: `lem:sparse-upper-envelope`, the primitive carrier
supply and the capacity-token ledger.

Four reads and all four spent: node `[130]`'s pair count is what the ledger's
charge is levied against, node `[8]`'s no-proper-core entry is the degeneracy the
envelope is proved from, node `[9]`'s tight-endpoint entry puts one end of an
edge exactly at the baseline, and the branch's own node-`[19]` entry makes the
surplus positive, which is what exhibits the edge. -/
@[reducible] noncomputable def capacityTokenLedger :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  capacityTokenLedgerRow (K .canonicalPairLedger) (K .baselineSpineDemand)
    (K .noProperBaseline) (K .tightEndpoint) (K .surplusAbove) (K .sparseUpperEnvelope)
    (K .capacityTokenLedger)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down.1)
    (fun _input fact baseline Coordinate Chord activation =>
      fact.down.2.2 baseline Coordinate Chord activation)
    (fun _input fact => fact.down)
    (fun _input fact => fact.down)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩) (fun _input value => ⟨value⟩)

/-- Nodes `[137]`--`[143]`: the coupled high-load test with its role split.

Three keys are read and all three are spent: node `[130]`'s pair count converts
the lower-bound package bound, node `[136]`'s capacity-token ledger witnesses the
high-load display, and node `[129]`'s package ordering supplies the deficit the
estimate is stated at. -/
@[reducible] noncomputable def coupledFibrePressure :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coupledFibrePressureRow (K .canonicalPairLedger) (K .capacityTokenLedger)
    (K .roleFibrePartition) (K .fibrePressure)
    (by simp) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact declared =>
      let certified := (fact.down.2.1 declared).some
      ⟨certified.ledger⟩)
    (fun _input value => ⟨value⟩) (fun _input value => ⟨value⟩)

/-- Node `[138]` commits the actual square-root surplus bound. -/
@[reducible] noncomputable def spineSurplusEstimate :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  spineSurplusEstimateRow (K .sparsePressureNearCubic)
    (K .capacityTokenLedger) (K .surplusAbove) (K .spineSurplusEstimate)
    (by simp) (by simp) (by simp)
    (fun _input fact => fact.down)
    (fun _input fact => fact.down.2.2)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[140]`: the window-incidence geometric audit, on node `[139]`'s yes
arm. -/
@[reducible] noncomputable def windowIncidenceAudit :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  classAuditRow .windowIncidence (K .windowIncidenceAudit)
    (K .quantitativeOverload) (by simp)
    (fun _input value => ⟨value⟩) (fun _input value => ⟨value⟩)

/-- Node `[142]`: the remainder-surplus geometric audit, on node `[141]`'s yes
arm. -/
@[reducible] noncomputable def remainderSurplusAudit :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  classAuditRow .remainderSurplus (K .remainderSurplusAudit)
    (K .quantitativeOverload) (by simp)
    (fun _input value => ⟨value⟩) (fun _input value => ⟨value⟩)

/-- Node `[143]`: the primitive-carrier geometric audit, on the fall-through arm.
Its three reads are node `[137]`'s overload and the two negative class arms, and
all three are spent deriving its own class verdict. -/
@[reducible] noncomputable def primitiveCarrierAudit :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  primitiveCarrierAuditRow (K .sparsePressureOverload) (K .windowClassAbsent)
    (K .remainderClassAbsent) (K .primitiveClassOverload)
    (K .primitiveCarrierAudit) (K .quantitativeOverload)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun _input fact => fact.down)
    (fun _input fact => fact.down)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩) (fun _input value => ⟨value⟩)
    (fun _input value => ⟨value⟩)

/-- Node `[144]`, the bottleneck arm's own fact: the manuscript's first
assertion, at the object's declared routed bottlenecks.  Both reads are spent —
the selection entry's avoidance and node `[11]`--`[14]`'s `cor:uncompressible`,
at the ledger's own predicate. -/
@[reducible] noncomputable def bottleneckRouting :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  bottleneckRoutingRow (K .selection) (K .uncompressible)
    (K .sparseSurplusSurvivor) (K .bottleneckRouting)
    (by simp) (by simp) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down.1) (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[144]`, the near-cubic close.  Both reads are spent: the caps arm's own
fact discharges `cor:homogeneous-same-token-caps-close`'s clauses, and node
`[126]`'s slack identity gives the edge-count half. -/
@[reducible] noncomputable def homogeneousBottleneck :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  homogeneousBottleneckRow (K .homogeneousCapsHold) (K .sparseSlackSurplus)
    (K .homogeneousBottleneck) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[144]` commits the exact square-root bound from its cap-close
pressure and the certified capacity ledger. -/
@[reducible] noncomputable def homogeneousSpineSurplusEstimate :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  homogeneousSpineSurplusEstimateRow (K .homogeneousBottleneck)
    (K .capacityTokenLedger) (K .surplusAbove) (K .spineSurplusEstimate)
    (by simp) (by simp) (by simp)
    (fun _input fact => fact.down)
    (fun _input fact => fact.down.2.2)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[125]`: the selected object survives the five sparse surplus exits.
Derived from the selection entry; every later node of the block reads it. -/
@[reducible] noncomputable def sparseSurplusSurvivor :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  sparseSurplusSurvivorRow (K .selection) (K .uncompressible)
    (K .sparseSurplusSurvivor) (by simp) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact smaller lexicographic baseline =>
      fact.down.2 smaller lexicographic baseline)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[125]`, continued: `def:active-surplus-demands` with
`lem:surviving-active-family`.  Every input is a fact the branch already
carries. -/
@[reducible] noncomputable def activeSurplusDemands :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  activeSurplusDemandsRow (K .sparseSurplusSurvivor) (K .activeSurplusFamily)
    (K .sparsePortActivation) (K .activeSurplusDemands)
    (by simp) (by simp) (by simp) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down.1)
    (fun _input fact pair member left right shoulders distinct =>
      fact.down pair member left right shoulders distinct)
    (fun _input value => ⟨value⟩)

/-! ## The block, run -/

/-- The key index a branch carries at node `[132]`: nodes `[126]`--`[130]`, with
neither arm of the blocked-pair routing taken yet. -/
abbrev pairRoutingKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .baselineSpineDemand :: K .activeSurplusDemands :: K .sparseSurplusSurvivor ::
    K .sparsePortActivation :: K .activeSurplusFamily ::
    K .sparseSlackSurplus :: known

/-- Node `[131]` after the mixed dependence route has established full rank. -/
abbrev pairLedgerKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .canonicalPairLedger :: K .canonicalBlockerRoute :: pairRoutingKeys known

/-- Node `[133]`'s index: node `[132]`'s exit arm and the canonical closure key
Core appends from it and node `[125]`'s survivor entry. -/
abbrev sparsePairExitKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .sparsePairExit :: pairRoutingKeys known

/-- The key index a branch carries after nodes `[126]`--`[137]`, before the
node-`[137]` branch.  It sits over node `[132]`'s *blocker* arm: the exit arm's
verdict is absent, so nothing here can read a dependence that was settled by an
exit. -/
abbrev sparseActivationKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .roleFibrePartition :: K .fibrePressure :: K .sparseUpperEnvelope ::
    K .capacityTokenLedger ::
    pairLedgerKeys known

/-- The near-cubic arm's index: the block's facts plus
`prop:single-graph-sparse-pressure-routing` (a).  The geometric audits are
absent, so nothing downstream of `[138]` can read an overload that did not
occur. -/
abbrev nearCubicKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .spineSurplusEstimate :: K .sparsePressureNearCubic ::
    sparseActivationKeys known

/-- The index common to the three overload arms: the block's facts and the
forced role-homogeneous pattern of `prop:single-graph-sparse-pressure-routing`
(b). -/
abbrev overloadKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .sparsePressureOverload :: sparseActivationKeys known

/-- Node `[140]`'s arm: node `[139]`'s window-incidence verdict, the audit it
opens, the forced pattern scale, and node `[144]` that reads them. -/
abbrev windowAuditKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .windowIncidenceAudit :: K .quantitativeOverload ::
    K .windowClassOverload :: overloadKeys known

/-- Node `[142]`'s arm: node `[139]`'s negative verdict, node `[141]`'s
remainder-surplus verdict, and the audit they open. -/
abbrev remainderAuditKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .remainderSurplusAudit :: K .quantitativeOverload ::
    K .remainderClassOverload :: K .windowClassAbsent :: overloadKeys known

/-- Node `[143]`'s arm: both negative verdicts, the primitive-carrier verdict
derived from them, and the audit they open. -/
abbrev primitiveAuditKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .primitiveClassOverload :: K .primitiveCarrierAudit ::
    K .quantitativeOverload :: K .remainderClassAbsent ::
    K .windowClassAbsent :: overloadKeys known

/-- Node `[144]`'s caps arm over a geometric audit: the near-cubic close. -/
abbrev capsClosedKeys
    (audited : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .spineSurplusEstimate :: K .homogeneousBottleneck ::
    K .homogeneousCapsHold :: audited

/-- Node `[144]`'s bottleneck arm: the pattern
`lem:same-token-bottleneck-routing` reads as a sparse surplus exit or as
decorated Type B fan data. -/
abbrev bottleneckKeys
    (audited : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .bottleneckRouting :: K .homogeneousBottleneckPattern :: audited

/-- Node `[144]`'s bottleneck arm, with `[70]`'s source-free cap committed: the
entry index of the local Type B fan ledger.

`thm:homogeneous-overload-geometric-closure` routes the decorated Type B handoff
fan data of a role-homogeneous same-token bottleneck *into the Type B fan
ledger*, and `prop:fan-closed-port-typeB-routing` says that ledger is entered at
node `[72]`.  This is that entry. -/
abbrev bottleneckFanKeys
    (audited : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateCap :: bottleneckKeys audited

/-- **The exit of the sparse activation block: `[125]`--`[144]`, closed.**

Eight constructors.  `sparsePairExit` is node `[133]`: node `[132]`'s exit arm,
closed against node `[125]`'s survivor entry by Core's own `closeIncompatible`,
so it carries the canonical closure key and nothing downstream of `[133]` runs.
`nearCubic` is
`prop:single-graph-sparse-pressure-routing` (a), the branch that never overloads
and routes straight to `[138]`.  The other six are node `[144]`'s two outcomes
over each of the three geometric audits `class(t)` dispatched to:
`prop:nonnear-cubic-sharp-overload-routing` (a) again -- the fixed homogeneous
caps hold and `cor:homogeneous-same-token-caps-close` closes the branch with
`σ(G) = O(√n)` and `m = (3/2)n + O(√n)` -- or its (b)/(c), the same-token
bottleneck `lem:same-token-bottleneck-routing` reads as a sparse surplus exit or
as decorated Type B handoff fan data.

No arm's key index contains another arm's verdict, so a window-incidence
bottleneck cannot be read as a remainder-surplus one, a capped branch cannot
read a bottleneck, and the near-cubic route cannot read an overload that did not
occur.  Nothing remains at `[144]`. -/
inductive SurplusResult
    (selected : Input BranchState Presentation presentation data)
    (known : FactKeys (Input BranchState Presentation presentation data)) where
  | sparsePairExit
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (sparsePairExitKeys known))
  | nearCubic
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (nearCubicKeys known))
  | windowCapsClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (capsClosedKeys (windowAuditKeys known)))
  | windowBottleneck
      (result : TypeBFanLedgerResult selected
        (bottleneckFanKeys (windowAuditKeys known)))
  | remainderCapsClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (capsClosedKeys (remainderAuditKeys known)))
  | remainderBottleneck
      (result : TypeBFanLedgerResult selected
        (bottleneckFanKeys (remainderAuditKeys known)))
  | primitiveCapsClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (capsClosedKeys (primitiveAuditKeys known)))
  | primitiveBottleneck
      (result : TypeBFanLedgerResult selected
        (bottleneckFanKeys (primitiveAuditKeys known)))

/-- **Nodes `[126]`--`[144]`, run.**

The eleven fact-only rows are composed by `AtomicCT.run`, which appends each
row's declared productions to the incoming index while retaining the literal
ancestry.  Every freshness side condition is decided on the vocabulary's own
finite `Key`. -/
noncomputable def runSparseActivation
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .slackIndependent) known]
    [FactKeys.Has (K (data := data) .uncompressible) known]
    [FactKeys.Has (K (data := data) .noProperBaseline) known]
    [FactKeys.Has (K (data := data) .tightEndpoint) known]
    [FactKeys.Has (K (data := data) .surplusAbove) known]
    [FactKeys.Has (K (data := data) .windowPackageSeparated) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (slackFresh : K (data := data) .sparseSlackSurplus ∉ known)
    (familyFresh : K (data := data) .activeSurplusFamily ∉ known)
    (activationFresh : K (data := data) .sparsePortActivation ∉ known)
    (survivorFresh : K (data := data) .sparseSurplusSurvivor ∉ known)
    (demandsFresh : K (data := data) .activeSurplusDemands ∉ known)
    (demandFresh : K (data := data) .baselineSpineDemand ∉ known)
    (pairFresh : K (data := data) .canonicalPairLedger ∉ known)
    (exitFresh : K (data := data) .sparsePairExit ∉ known)
    (blockerFresh : K (data := data) .canonicalBlockerRoute ∉ known)
    (closureFresh : closed (BranchState := BranchState)
      (presentation := presentation) (data := data) ∉ known)
    (envelopeFresh : K (data := data) .sparseUpperEnvelope ∉ known)
    (tokenFresh : K (data := data) .capacityTokenLedger ∉ known)
    (partitionFresh : K (data := data) .roleFibrePartition ∉ known)
    (pressureFresh : K (data := data) .fibrePressure ∉ known)
    (estimateFresh : K (data := data) .spineSurplusEstimate ∉ known)
    (nearCubicFresh : K (data := data) .sparsePressureNearCubic ∉ known)
    (overloadFresh : K (data := data) .sparsePressureOverload ∉ known)
    (windowOverloadFresh : K (data := data) .windowClassOverload ∉ known)
    (windowAbsentFresh : K (data := data) .windowClassAbsent ∉ known)
    (remainderOverloadFresh : K (data := data) .remainderClassOverload ∉ known)
    (remainderAbsentFresh : K (data := data) .remainderClassAbsent ∉ known)
    (windowAuditFresh : K (data := data) .windowIncidenceAudit ∉ known)
    (remainderAuditFresh : K (data := data) .remainderSurplusAudit ∉ known)
    (primitiveAuditFresh : K (data := data) .primitiveCarrierAudit ∉ known)
    (primitiveVerdictFresh : K (data := data) .primitiveClassOverload ∉ known)
    (scaleFresh : K (data := data) .quantitativeOverload ∉ known)
    (capsHoldFresh : K (data := data) .homogeneousCapsHold ∉ known)
    (patternFresh : K (data := data) .homogeneousBottleneckPattern ∉ known)
    (routingFresh : K (data := data) .bottleneckRouting ∉ known)
    (bottleneckFresh : K (data := data) .homogeneousBottleneck ∉ known)
    (capFresh : K (data := data) .fanCertificateCap ∉ known)
    (markedFresh : K (data := data) .fanCertificateMarked ∉ known)
    (certResidualFresh : K (data := data) .fanCertificateResidual ∉ known)
    (cycleFresh : K (data := data) .typeBDirectCycle ∉ known)
    (cycleFreeFresh : K (data := data) .typeBDirectCycleFree ∉ known)
    (b2ChoiceFresh : K (data := data) .typeBB2Choice ∉ known)
    (obstructionFresh : K (data := data) .typeBOverlapObstruction ∉ known)
    (hybridFresh : K (data := data) .typeBHybridEntry ∉ known)
    (disjointFresh : K (data := data) .typeBDisjointLedger ∉ known) :
    SurplusResult current known := by
  classical
  have afterSlack :=
    (sparseSlackSurplus (data := data)).run history (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [slackFresh])
  have afterFamily :=
    (activeSurplusFamily (data := data)).run afterSlack (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [familyFresh])
  have afterActivation :=
    (sparsePortActivation (data := data)).run afterFamily (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [activationFresh])
  have afterSurvivor :=
    (sparseSurplusSurvivor (data := data)).run afterActivation (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [survivorFresh])
  have afterDemands :=
    (activeSurplusDemands (data := data)).run afterSurvivor (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [demandsFresh])
  have afterDemand :=
    (baselineSpineDemand (data := data)).run afterDemands (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [demandFresh])
  -- Node `[132]`: `lem:sparse-pair-dependence-exit`.
  match blockedPairRouting afterDemand (by simp [exitFresh])
      (by simp [blockerFresh]) with
  | .left exitHistory =>
      -- Node `[133]`: the exit collides with node `[125]`'s survivor entry.
      exact .sparsePairExit
        (closeIncompatible exitHistory (K .sparseSurplusSurvivor)
          (K .sparsePairExit) (by simp [closureFresh]))
  | .right afterBlockers =>
  have afterPairs :=
    (canonicalPairLedger (data := data)).run afterBlockers (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [pairFresh])
  have afterTokens :=
    (capacityTokenLedger (data := data)).run afterPairs (by
      intro key isNew isOld
      simp only [List.mem_cons, List.not_mem_nil, or_false] at isNew
      rcases isNew with rfl | rfl <;> revert isOld <;>
        simp [envelopeFresh, tokenFresh])
  have afterPressure :=
    (coupledFibrePressure (data := data)).run afterTokens (by
      intro key isNew isOld
      simp only [List.mem_cons, List.not_mem_nil, or_false] at isNew
      rcases isNew with rfl | rfl <;> revert isOld <;>
        simp [partitionFresh, pressureFresh])
  -- Node `[137]`: `prop:single-graph-sparse-pressure-routing`.
  match sparsePressureDichotomy afterPressure (K .sparsePressureNearCubic)
      (K .sparsePressureOverload) (fun value => ⟨value⟩) (fun value => ⟨value⟩)
      (by simp [nearCubicFresh]) (by simp [overloadFresh]) with
  | .left nearCubicHistory =>
      have afterEstimate :=
        (spineSurplusEstimate (data := data)).run nearCubicHistory (by
          intro key isNew isOld
          simp only [List.mem_singleton] at isNew
          subst isNew
          revert isOld
          simp [estimateFresh])
      exact .nearCubic
        (closeIncompatible afterEstimate (K .surplusAbove)
          (K .spineSurplusEstimate) (by simp [closureFresh]))
  | .right overloadHistory =>
      -- Node `[139]`: is the overloading token a window incidence?
      match windowClassDichotomy overloadHistory (K .windowClassOverload)
          (K .windowClassAbsent) (fun value => ⟨value⟩) (fun value => ⟨value⟩)
          (by simp [windowOverloadFresh]) (by simp [windowAbsentFresh]) with
      | .left windowHistory =>
          have afterAudit :=
            (windowIncidenceAudit (data := data)).run windowHistory (by
              intro key isNew isOld
              simp only [List.mem_cons, List.not_mem_nil, or_false] at isNew
              rcases isNew with rfl | rfl <;> revert isOld <;>
                simp [windowAuditFresh, scaleFresh])
          -- Node `[144]`: do the fixed homogeneous caps hold?
          match homogeneousCapsDichotomy afterAudit (K .homogeneousCapsHold)
              (K .homogeneousBottleneckPattern) (fun value => ⟨value⟩)
              (fun value => ⟨value⟩) (by simp [capsHoldFresh])
              (by simp [patternFresh]) with
          | .left capsHistory =>
              have afterClose :=
                (homogeneousBottleneck (data := data)).run capsHistory (by
                  intro key isNew isOld
                  simp only [List.mem_singleton] at isNew
                  subst isNew
                  revert isOld
                  simp [bottleneckFresh])
              have afterEstimate :=
                (homogeneousSpineSurplusEstimate (data := data)).run afterClose (by
                  intro key isNew isOld
                  simp only [List.mem_singleton] at isNew
                  subst isNew
                  revert isOld
                  simp [estimateFresh])
              exact .windowCapsClosed
                (closeIncompatible afterEstimate (K .surplusAbove)
                  (K .spineSurplusEstimate) (by simp [closureFresh]))
          | .right patternHistory =>
              have afterRouting :=
                (bottleneckRouting (data := data)).run patternHistory (by
                  intro key isNew isOld
                  simp only [List.mem_singleton] at isNew
                  subst isNew
                  revert isOld
                  simp [routingFresh])
              -- `thm:homogeneous-overload-geometric-closure`: the decorated
              -- Type B handoff fan data is routed into the Type B fan ledger,
              -- which `prop:fan-closed-port-typeB-routing` enters at `[72]`.
              exact .windowBottleneck
                (runTypeBFanLedger
                  ((fanCertificateCap (data := data)).run afterRouting (by
                    intro key isNew isOld
                    simp only [List.mem_singleton] at isNew
                    subst isNew
                    revert isOld
                    simp [capFresh]))
                  (by simp [markedFresh]) (by simp [certResidualFresh])
                  (by simp [cycleFresh]) (by simp [cycleFreeFresh])
                  (by simp [b2ChoiceFresh]) (by simp [obstructionFresh])
                  (by simp [hybridFresh]) (by simp [disjointFresh])
                  (by simp [closureFresh]))
      | .right freeHistory =>
          -- Node `[141]`: is it a remainder-surplus token?
          match remainderClassDichotomy freeHistory (K .remainderClassOverload)
              (K .remainderClassAbsent) (fun value => ⟨value⟩)
              (fun value => ⟨value⟩) (by simp [remainderOverloadFresh])
              (by simp [remainderAbsentFresh]) with
          | .left remainderHistory =>
              have afterAudit :=
                (remainderSurplusAudit (data := data)).run remainderHistory (by
                  intro key isNew isOld
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at isNew
                  rcases isNew with rfl | rfl <;> revert isOld <;>
                    simp [remainderAuditFresh, scaleFresh])
              -- Node `[144]`: do the fixed homogeneous caps hold?
              match homogeneousCapsDichotomy afterAudit (K .homogeneousCapsHold)
                  (K .homogeneousBottleneckPattern) (fun value => ⟨value⟩)
                      (fun value => ⟨value⟩) (by simp [capsHoldFresh])
                  (by simp [patternFresh]) with
              | .left capsHistory =>
                  have afterClose :=
                    (homogeneousBottleneck (data := data)).run capsHistory (by
                      intro key isNew isOld
                      simp only [List.mem_singleton] at isNew
                      subst isNew
                      revert isOld
                      simp [bottleneckFresh])
                  have afterEstimate :=
                    (homogeneousSpineSurplusEstimate (data := data)).run afterClose (by
                      intro key isNew isOld
                      simp only [List.mem_singleton] at isNew
                      subst isNew
                      revert isOld
                      simp [estimateFresh])
                  exact .remainderCapsClosed
                    (closeIncompatible afterEstimate (K .surplusAbove)
                      (K .spineSurplusEstimate) (by simp [closureFresh]))
              | .right patternHistory =>
              have afterRouting :=
                (bottleneckRouting (data := data)).run patternHistory (by
                  intro key isNew isOld
                  simp only [List.mem_singleton] at isNew
                  subst isNew
                  revert isOld
                  simp [routingFresh])
              -- `thm:homogeneous-overload-geometric-closure`: the decorated
              -- Type B handoff fan data is routed into the Type B fan ledger,
              -- which `prop:fan-closed-port-typeB-routing` enters at `[72]`.
              exact .remainderBottleneck
                (runTypeBFanLedger
                  ((fanCertificateCap (data := data)).run afterRouting (by
                    intro key isNew isOld
                    simp only [List.mem_singleton] at isNew
                    subst isNew
                    revert isOld
                    simp [capFresh]))
                  (by simp [markedFresh]) (by simp [certResidualFresh])
                  (by simp [cycleFresh]) (by simp [cycleFreeFresh])
                  (by simp [b2ChoiceFresh]) (by simp [obstructionFresh])
                  (by simp [hybridFresh]) (by simp [disjointFresh])
                  (by simp [closureFresh]))
          | .right primitiveHistory =>
              have afterAudit :=
                (primitiveCarrierAudit (data := data)).run primitiveHistory (by
                  intro key isNew isOld
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at isNew
                  rcases isNew with rfl | rfl | rfl <;> revert isOld <;>
                    simp [primitiveVerdictFresh, primitiveAuditFresh, scaleFresh])
              -- Node `[144]`: do the fixed homogeneous caps hold?
              match homogeneousCapsDichotomy afterAudit (K .homogeneousCapsHold)
                  (K .homogeneousBottleneckPattern) (fun value => ⟨value⟩)
                      (fun value => ⟨value⟩) (by simp [capsHoldFresh])
                  (by simp [patternFresh]) with
              | .left capsHistory =>
                  have afterClose :=
                    (homogeneousBottleneck (data := data)).run capsHistory (by
                      intro key isNew isOld
                      simp only [List.mem_singleton] at isNew
                      subst isNew
                      revert isOld
                      simp [bottleneckFresh])
                  have afterEstimate :=
                    (homogeneousSpineSurplusEstimate (data := data)).run afterClose (by
                      intro key isNew isOld
                      simp only [List.mem_singleton] at isNew
                      subst isNew
                      revert isOld
                      simp [estimateFresh])
                  exact .primitiveCapsClosed
                    (closeIncompatible afterEstimate (K .surplusAbove)
                      (K .spineSurplusEstimate) (by simp [closureFresh]))
              | .right patternHistory =>
              have afterRouting :=
                (bottleneckRouting (data := data)).run patternHistory (by
                  intro key isNew isOld
                  simp only [List.mem_singleton] at isNew
                  subst isNew
                  revert isOld
                  simp [routingFresh])
              -- `thm:homogeneous-overload-geometric-closure`: the decorated
              -- Type B handoff fan data is routed into the Type B fan ledger,
              -- which `prop:fan-closed-port-typeB-routing` enters at `[72]`.
              exact .primitiveBottleneck
                (runTypeBFanLedger
                  ((fanCertificateCap (data := data)).run afterRouting (by
                    intro key isNew isOld
                    simp only [List.mem_singleton] at isNew
                    subst isNew
                    revert isOld
                    simp [capFresh]))
                  (by simp [markedFresh]) (by simp [certResidualFresh])
                  (by simp [cycleFresh]) (by simp [cycleFreeFresh])
                  (by simp [b2ChoiceFresh]) (by simp [obstructionFresh])
                  (by simp [hybridFresh]) (by simp [disjointFresh])
                  (by simp [closureFresh]))

/-- **The sparse surplus branch, entered from the entry spine's own exit.**

The predecessor is the literal ledger of `Spine.Result.surplusAbove`: node
`[19]`'s above arm, indexed by the nine facts that branch established.  Both
prerequisites -- the selection entry and node `[10]`'s slack independence -- are
in that index, so the block elaborates against it and nothing is re-selected or
re-proved. -/
abbrev surplusAbovePackageKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .windowPackageSeparated ::
    surplusAboveKeys (BranchState := BranchState)
      (presentation := presentation) (data := data)

abbrev surplusAbovePackageFailedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .windowPackageCollided ::
    surplusAboveKeys (BranchState := BranchState)
      (presentation := presentation) (data := data)

/-- The high-surplus failure of node `[21]`, after the diagram's cold
continuation `[145]`--`[157]` has consumed that exact residual. -/
abbrev surplusAboveColdKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  coldKeys (surplusAbovePackageFailedKeys (BranchState := BranchState)
    (presentation := presentation) (data := data))

/-- The at-or-below failure of node `[21]`, continued through the same cold
corridor on the residual accumulated before the package test. -/
abbrev atOrBelowColdKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  coldKeys (windowPackageCollidedKeys (BranchState := BranchState)
    (presentation := presentation) (data := data))

noncomputable def runSurplusBranch
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (surplusAbovePackageKeys (BranchState := BranchState)
        (presentation := presentation) (data := data))) :
    SurplusResult selected
      (surplusAbovePackageKeys (BranchState := BranchState)
        (presentation := presentation) (data := data)) :=
  runSparseActivation history
    (slackFresh := by simp)
    (familyFresh := by simp)
    (activationFresh := by simp)
    (survivorFresh := by simp)
    (demandsFresh := by simp)
    (demandFresh := by simp)
    (pairFresh := by simp)
    (exitFresh := by simp)
    (blockerFresh := by simp)
    (closureFresh := by simp)
    (envelopeFresh := by simp)
    (tokenFresh := by simp)
    (partitionFresh := by simp)
    (pressureFresh := by simp)
    (estimateFresh := by simp)
    (nearCubicFresh := by simp)
    (overloadFresh := by simp)
    (windowOverloadFresh := by simp)
    (windowAbsentFresh := by simp)
    (remainderOverloadFresh := by simp)
    (remainderAbsentFresh := by simp)
    (windowAuditFresh := by simp)
    (remainderAuditFresh := by simp)
    (primitiveAuditFresh := by simp)
    (primitiveVerdictFresh := by simp)
    (scaleFresh := by simp)
    (capsHoldFresh := by simp)
    (patternFresh := by simp)
    (routingFresh := by simp)
    (bottleneckFresh := by simp)
    (capFresh := by simp)
    (markedFresh := by simp)
    (certResidualFresh := by simp)
    (cycleFresh := by simp)
    (cycleFreeFresh := by simp)
    (b2ChoiceFresh := by simp)
    (obstructionFresh := by simp)
    (hybridFresh := by simp)
    (disjointFresh := by simp)
end Hypostructure.Graph.Strategy.Spine
